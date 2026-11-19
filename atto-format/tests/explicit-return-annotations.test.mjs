import test from 'node:test';
import assert from 'node:assert/strict';
import { normalize_callable_headers } from '../src/callable-headers.mjs';

test('explicit void and infer survive class method normalization', () => {
  const src = 'define class C as fnc get() -> infer { return 5; } method reset(): void { } end';
  const expected = 'define class C as get() -> infer { return 5; } reset(): void { } end';
  assert.equal(normalize_callable_headers(src), expected);
  assert.equal(normalize_callable_headers(expected), expected);
});

test('named methods without return types are never silently formatted as void', () => {
  for (const src of [
    'define class C as fnc f() { } end',
    'define class C as method f() { return 3; } end',
    'define actor A as fnc f() { } end',
    'mtd (C self) f() { return 1; }',
  ]) {
    assert.equal(normalize_callable_headers(src), src);
  }
});

test('explicit inferred out-of-line result keeps infer and source body', () => {
  const src='mtd (C self) get() -> infer :: 1 end';
  assert.equal(normalize_callable_headers(src), 'mtd (self: C) get() -> infer :: 1 end');
  assert.equal(normalize_callable_headers(normalize_callable_headers(src)), normalize_callable_headers(src));
});

test('formatter does not invent return types in top-level callables', () => {
  const invalid='fnc f() { }';
  const explicit='fnc f() -> void { }';
  assert.equal(normalize_callable_headers(invalid), invalid);
  assert.equal(normalize_callable_headers(explicit), explicit);
});
