import test from 'node:test';
import assert from 'node:assert/strict';
import {
  normalize_ownership_operations as normalize,
  normalize_verified_ownership_operations as verified,
} from '../src/ownership-operations.mjs';

test('all eleven ownership spellings remain intact and idempotent', () => {
  const text = [
    'val a = borrow! x;',
    'val b = take! x;',
    'val c = share! x;',
    'val d = copy! x;',
    'val e = copy!! x;',
    'val f = borrow! mut x;',
    'lt! a;',
    'val g = freeze! take! x;',
    'val h = weak! shared;',
    'val i = pin! take! x;',
    'drop! x;',
  ].join('\n');
  assert.equal(normalize(text), text);
  assert.equal(normalize(normalize(text)), text);
});

test('long lifetime binder canonicalizes with identity-safe generic syntax', () => {
  for (const [input, expected] of [
    ['fnc f<lifetime! a, T>(Borrow<T, lt=a> x) {}',
     'fnc f<lt! a, T>(Borrow<T, lt=a> x) {}'],
    ['lifetime! a;\nlifetime! _my_lifetime2;',
     'lt! a;\nlt! _my_lifetime2;'],
    ['fnc f<lifetime!a>() {}', 'fnc f<lt!a>() {}'],
  ]) {
    assert.equal(normalize(input), expected);
    assert.equal(normalize(expected), expected);
  }
});

test('contiguous copy!! stays different from copy! followed by unary !', () => {
  for (const input of ['copy!! x', 'copy! !x', 'copy!(!x)', 'copy ! ! x']) {
    assert.equal(normalize(input), input);
  }
});

test('comments, strings, templates and nested comments are opaque', () => {
  const input = [
    '// lifetime! should remain literal',
    '/* lifetime! x /* nested lifetime! y */ lifetime! z */',
    'val s = "lifetime! a";',
    "val t = 'lifetime! b';",
    'val u = '+String.fromCharCode(96)+'lifetime! c'+String.fromCharCode(96)+';',
    'fnc f<lifetime! d>() {}',
  ].join('\n');
  const expected = input.replace('fnc f<lifetime! d>', 'fnc f<lt! d>');
  assert.equal(normalize(input), expected);
});

test('conservative gate refuses nonbinder or comment-separated spellings', () => {
  for (const input of [
    'obj.lifetime! a',
    'lifetime!! a',
    'val x = lifetime! /* keep */ a;',
    'prefix_lifetime! a',
  ]) assert.equal(normalize(input), input);
});

test('malformed comments and strings do not get normalized by guesswork', () => {
  assert.throws(() => normalize('/* lifetime! a'), /Unterminated nested block/);
  assert.throws(() => normalize('"lifetime! a'), /Unterminated quoted literal/);
  assert.throws(() => normalize(null), /Expected Atto source/);
});

test('verified wrapper requires real caller compiler output, not empty bytes', async () => {
  const source = 'fnc f<lifetime! a>() {}';
  await assert.rejects(() => verified(source, null), /real guest compiler/);
  await assert.rejects(() => verified(source, async () => new Uint8Array()),
    /valid WebAssembly/);
});

test('test fixture: deterministic compiler output permits matching normalization', async () => {
  // A stand-in callback tests the wrapper contract ONLY. It is not real guest
  // parity evidence; production must supply the Atto compiler.
  const wasm = Uint8Array.of(0, 97, 115, 109, 1, 0, 0, 0);
  assert.ok(WebAssembly.validate(wasm));
  const result = await verified('fnc f<lifetime! a>() {}', async () => wasm);
  assert.equal(result.changed, true);
  assert.equal(result.formatted, 'fnc f<lt! a>() {}');
  assert.equal(result.guest_binary_equal, true);
});

test('verified wrapper fails if source rewriting changes guest binary', async () => {
  let n = 0;
  await assert.rejects(
    () => verified('fnc f<lifetime! a>() {}', async () =>
      n++ === 0
        ? Uint8Array.of(0, 97, 115, 109, 1, 0, 0, 0)
        : Uint8Array.of(0, 97, 115, 109, 1, 0, 0, 0, 0, 1, 0)),
    /changed emitted guest semantics/,
  );
});

test('guest proof rejects malformed post-header sections and oversized binary results', async () => {
  const source = 'fnc f<lifetime! a>() {}';
  const validHeader = Uint8Array.of(0, 97, 115, 109, 1, 0, 0, 0);
  assert.ok(WebAssembly.validate(validHeader));
  assert.equal(WebAssembly.validate(Uint8Array.of(...validHeader, 42)), false);
  await assert.rejects(
    () => verified(source, async () => Uint8Array.of(...validHeader, 42)),
    /structurally valid WebAssembly/,
  );
  await assert.rejects(
    () => verified(source, async () => new Uint8Array(16 * 1024 * 1024 + 1)),
    /bounded, structurally valid WebAssembly/,
  );
});
