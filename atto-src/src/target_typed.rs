//! Typed signature IR for proposed namespace-scoped actor receiver declarations.
//! This is separate from executable check.rs. Forward-declared actors have no
//! linked implementation, state layout, proven effects or borrow semantics.

use crate::ast::{ActorInterface, ActorInterfaceMethod, Param, Program, Type};
use crate::diag::{Diagnostic, Pos};
use crate::target_syntax::{ReceiverHeader, TargetHeaders};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TargetType {
    Int,
    Bool,
    Float,
    Str,
    Void,
    /// Index in TypedActorModule.actors. Capability, not actor value.
    ActorRef(usize),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedParam {
    pub name: String,
    pub ty: TargetType,
    pub pos: Pos,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedActor {
    pub name: String,
    /// Concrete syntax definition linked to the forward declaration;
    /// this alone does NOT make the actor spawnable.
    pub has_definition: bool,
    pub defined: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedReceiver {
    pub actor: usize,
    pub method: String,
    pub arity: usize,
    pub params: Vec<TypedParam>,
    pub returns: TargetType,
    pub mutable: bool,
    pub public: bool,
    pub pos: Pos,
    /// Signatures only: method bodies are not lowered or executable.
    pub body_lowered: bool,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TypedActorModule {
    pub namespace: Option<String>,
    pub actors: Vec<TypedActor>,
    pub receivers: Vec<TypedReceiver>,
}

fn type_error(pos: Pos, why: impl Into<String>) -> Diagnostic {
    Diagnostic::new(pos, "E_TYPE", why)
}

impl TypedActorModule {
    pub fn actor_index(&self, actor: &str, pos: Pos) -> Result<usize, Diagnostic> {
        self.actors.iter().position(|a| a.name == actor)
            .ok_or_else(|| Diagnostic::new(pos, "E_UNBOUND",
                format!("undeclared actor type '{actor}'")))
    }

    /// Unambiguous in-module lookup, not actor runtime dispatch.
    pub fn resolve<'a>(&'a self, namespace: Option<&str>, actor: &str,
        method: &str, arity: usize, external: bool,
        pos: Pos) -> Result<&'a TypedReceiver, Diagnostic> {
        if namespace != self.namespace.as_deref() {
            return Err(Diagnostic::new(pos, "E_NAMESPACE",
                "receiver not in its defining namespace"));
        }
        let owner = self.actor_index(actor, pos)?;
        let method = self.receivers.iter().find(|m|
            m.actor == owner && m.method == method && m.arity == arity)
            .ok_or_else(|| Diagnostic::new(pos, "E_UNBOUND",
                format!("no receiver method {actor}.{method}/{arity}")))?;
        if external && !method.public {
            return Err(Diagnostic::new(pos, "E_VISIBILITY",
                format!("receiver method {actor}.{} is not public", method.method)));
        }
        Ok(method)
    }

    /// All source-level actors in this IR are forward declarations. Runtime
    /// linking must establish a real implementation before spawn can work.
    pub fn require_spawnable(&self, actor: &str, pos: Pos)
        -> Result<usize, Diagnostic> {
        let index = self.actor_index(actor, pos)?;
        if !self.actors[index].defined {
            return Err(Diagnostic::new(pos, "E_UNLINKED",
                format!("actor '{actor}' is forward-declared but not defined")));
        }
        Ok(index)
    }

    fn type_of(&self, name: &str, pos: Pos) -> Result<TargetType, Diagnostic> {
        Ok(match name {
            "int" => TargetType::Int,
            "bool" | "boolean" => TargetType::Bool,
            "float" | "f64" => TargetType::Float,
            "string" | "String" => TargetType::Str,
            "void" => TargetType::Void,
            _ if name.starts_with("ActorRef<") && name.ends_with('>') => {
                let actor = &name["ActorRef<".len()..name.len()-1];
                TargetType::ActorRef(self.actor_index(actor, pos)?)
            },
            _ if self.actors.iter().any(|a| a.name == name) =>
                return Err(type_error(pos,
                    "actor values cannot be passed by value; use ActorRef<Actor>")),
            _ => return Err(Diagnostic::new(pos, "E_UNKNOWN_TYPE",
                format!("unknown receiver signature type '{name}'"))),
        })
    }

    fn lower_one(&self, h: &ReceiverHeader) -> Result<TypedReceiver, Diagnostic> {
        let actor = self.actor_index(&h.owner, h.pos)?;
        let mut params = Vec::with_capacity(h.params.len());
        for p in &h.params {
            let ty = self.type_of(&p.type_name, p.pos)?;
            if ty == TargetType::Void {
                return Err(type_error(p.pos, "a method parameter cannot have type void"));
            }
            params.push(TypedParam { name: p.name.clone(), ty, pos: p.pos });
        }
        let returns = self.type_of(&h.return_type, h.pos)?;
        if h.arity != params.len() {
            return Err(type_error(h.pos, "internal receiver arity mismatch"));
        }
        Ok(TypedReceiver {
            actor, method: h.name.clone(), arity: params.len(), params, returns,
            mutable: h.mutable, public: h.public, pos: h.pos,
            body_lowered: false,
        })
    }
}

/// Resolve the entire declaration set before typing receiver parameters and
/// result annotations, so forward references within one file are permitted.
pub fn lower_target_signatures(headers: &TargetHeaders)
    -> Result<TypedActorModule, Diagnostic> {
    let mut module = TypedActorModule {
        namespace: headers.namespace.clone(),
        actors: headers.actors.iter().map(|name| TypedActor {
            name: name.clone(),
            has_definition: headers.definitions.iter().any(|a| a.name == *name),
            defined: false,
        }).collect(),
        receivers: Vec::with_capacity(headers.receivers.len()),
    };
    for definition in &headers.definitions {
        if !headers.actors.contains(&definition.name) {
            return Err(Diagnostic::new(definition.pos, "E_UNBOUND",
                format!("concrete actor '{}' has no matching declare actor", definition.name)));
        }
    }
    for header in &headers.receivers {
        module.receivers.push(module.lower_one(header)?);
    }
    Ok(module)
}


impl TargetType {
    /// ActorRef indices are into actor_interface.forwards, not runtime actors.
    pub fn as_ast_type(&self) -> Type {
        match *self {
            Self::Int => Type::Int,
            Self::Bool => Type::Bool,
            Self::Float => Type::Float,
            Self::Str => Type::Str,
            Self::Void => Type::Void,
            Self::ActorRef(index) => Type::ActorRef(index as u32),
        }
    }
}

/// Preserve real concrete ActorDecls and nominal receiver signatures inside
/// the production AST, for checking before any actor code generation.
pub fn build_actor_program(headers: &TargetHeaders, module: &TypedActorModule) -> Program {
    let interface = ActorInterface {
        namespace: module.namespace.clone(),
        forwards: module.actors.iter().map(|a| a.name.clone()).collect(),
        methods: module.receivers.iter().map(|m| ActorInterfaceMethod {
            owner: m.actor as u32,
            name: m.method.clone(),
            params: m.params.iter().map(|p| Param {
                name: p.name.clone(), ty: p.ty.as_ast_type(),
                mutable: false, pos: p.pos,
            }).collect(),
            ret: m.returns.as_ast_type(),
            mutable: m.mutable, public: m.public, pos: m.pos,
        }).collect(),
    };
    Program {
        actors: headers.definitions.clone(),
        actor_interface: Some(interface),
        ..Program::default()
    }
}
