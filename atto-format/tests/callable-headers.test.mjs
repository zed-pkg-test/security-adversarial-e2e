import test from 'node:test';
import assert from 'node:assert/strict';
import {normalize_callable_headers} from '../src/callable-headers.mjs';
const cases = [
  [
    "named legacy",
    "mtd (Calculator self) square(int x) -> int :: x*x end",
    "mtd (self: Calculator) square(int x) -> int :: x*x end"
  ],
  [
    "named already canonical",
    "mtd (self: Calculator) square(int x) -> int :: x*x end",
    "mtd (self: Calculator) square(int x) -> int :: x*x end"
  ],
  [
    "implicit underscore",
    "mtd (Calculator _) square(int x) -> int :: x*x end",
    "mtd (Calculator) square(int x) -> int :: x*x end"
  ],
  [
    "implicit already canonical",
    "mtd (Calculator) square(int x) -> int :: x*x end",
    "mtd (Calculator) square(int x) -> int :: x*x end"
  ],
  [
    "mutable explicit",
    "mtd ( mut self : Calculator ) square(int x) -> int :: x*x end",
    "mtd (mut self: Calculator) square(int x) -> int :: x*x end"
  ],
  [
    "static and 5 inline",
    "define class C as\n  fnc a(): int { return 5; }\n  method b(): int -> { return 5; }\n  c() -> int { return 5; }\n  fnc d() -> int\n    let int x = 3,\n    x + 2\n  end\n  method e() -> int :: let int x = 3, x + 2 end\n  static fnc s(): int { return 5; }\nend",
    "define class C as\n  a(): int { return 5; }\n  b(): int -> { return 5; }\n  c() -> int { return 5; }\n  d() -> int\n    let int x = 3,\n    x + 2\n  end\n  e() -> int :: let int x = 3, x + 2 end\n  static fnc s(): int { return 5; }\nend"
  ],
  [
    "generic inline methods, nested return types, and static fnc",
    "define class Box as\n  fnc identity<T>(T value): T { return value; }\n  method wrap<T, E=Error>(T value) -> Result<Option<T>, E> { return value; }\n  fnc tail<T>() -> T :: make<T>() end\n  static fnc keep<T>(T value): T { return value; }\n  fnc after(): int { return 5; }\nend",
    "define class Box as\n  identity<T>(T value): T { return value; }\n  wrap<T, E=Error>(T value) -> Result<Option<T>, E> { return value; }\n  tail<T>() -> T :: make<T>() end\n  static fnc keep<T>(T value): T { return value; }\n  after(): int { return 5; }\nend"
  ],
  [
    "bare generic method does not hide next prefixed method",
    "define class C as\n  identity<T>(T x) -> T { return x; }\n  fnc next(): int { return 1; }\nend",
    "define class C as\n  identity<T>(T x) -> T { return x; }\n  next(): int { return 1; }\nend"
  ],
  [
    "generic callable return types and qualified names",
    "define actor A as\n  fnc f<T>(T value) -> fnc(int)->T { return value; }\n  method g<T>() : my.ns.Box<Option<T>> { return 0; }\nend",
    "define actor A as\n  f<T>(T value) -> fnc(int)->T { return value; }\n  g<T>() : my.ns.Box<Option<T>> { return 0; }\nend"
  ],
  [
    "unclosed generic method not rewritten",
    "define class C as fnc broken<T(T value): T { return value; } end",
    "define class C as fnc broken<T(T value): T { return value; } end"
  ],
  [
    "comment between keyword and generic method name blocks rewrite",
    "define class C as fnc /*keep*/ id<T>(T x): T { return x; } end",
    "define class C as fnc /*keep*/ id<T>(T x): T { return x; } end"
  ],
  [
    "noncode must be untouched",
    "// mtd (Calculator self) foo() -> int :: 5 end\nfnc foo(): int { return 5; }\nval x = \"mtd (Calculator self) foo()\";\nmtd (Calculator /*keep*/ self) bar() -> int :: 5 end",
    "// mtd (Calculator self) foo() -> int :: 5 end\nfnc foo(): int { return 5; }\nval x = \"mtd (Calculator self) foo()\";\nmtd (Calculator /*keep*/ self) bar() -> int :: 5 end"
  ],
  [
    "invalid receiver untouched",
    "mtd (Calculator mut self) set() -> int :: 5 end",
    "mtd (Calculator mut self) set() -> int :: 5 end"
  ]
];
for (const [name,input,expected] of cases) {
  test(name, () => {
    const output = normalize_callable_headers(input);
    assert.equal(output, expected);
    assert.equal(normalize_callable_headers(output), output, 'format twice equals format once');
  });
}
