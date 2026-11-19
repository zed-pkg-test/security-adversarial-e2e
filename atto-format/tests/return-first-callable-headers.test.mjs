import test from 'node:test';
import assert from 'node:assert/strict';
import { normalize_callable_headers } from '../src/callable-headers.mjs';

test('return-first inline methods with fnc normalize without changing result or body family', () => {
  const tests = [
    [
      'define class C as fnc int <- calculate(int x) { return x * 2; } end',
      'define class C as int <- calculate(int x) { return x * 2; } end'
    ],
    [
      'define class C as fnc void <- reset() begin end end',
      'define class C as void <- reset() begin end end'
    ],
    [
      'define actor A as method infer <- guess() begin return 42; end end',
      'define actor A as infer <- guess() begin return 42; end end'
    ],
    [
      'define class C as fnc int <- calculate(int x) return x * 2; end end',
      'define class C as int <- calculate(int x) return x * 2; end end'
    ],
    [
      'define class C as fnc calculate(int x): int -> { return x * 2; } end',
      'define class C as calculate(int x): int -> { return x * 2; } end'
    ],
  ];
  for (const [src, expected] of tests) {
    assert.equal(normalize_callable_headers(src), expected, src);
    assert.equal(normalize_callable_headers(expected), expected, 'idempotent ' + src);
  }
});

test('return-first receivers retain <- and canonicalize receiver spelling only', () => {
  const input = 'mtd (C self) int <- calculate(int x) begin return x * 2; end';
  const expected = 'mtd (self: C) int <- calculate(int x) begin return x * 2; end';
  assert.equal(normalize_callable_headers(input), expected);
  assert.equal(normalize_callable_headers(expected), expected);
});

test('non-method return-first declarations stay untouched', () => {
  for (const src of [
    'fnc int <- calculate(int x) begin return x * 2; end',
    'int <- calculate(int x) return x * 2; end',
    'void <- reset() begin end',
    'infer <- guess() begin return 42; end',
  ]) assert.equal(normalize_callable_headers(src), src);
});

test('split arrows, missing returns, and comments are not silently fixed', () => {
  for (const src of [
    'define class C as fnc int < - calculate(int x) { return x; } end',
    'define class C as fnc int <- calculate(int x) -> int { return x; } end',
    'define class C as fnc missing() { } end',
    'define class C as fnc /* preserve */ int <- method() begin end end',
  ]) assert.equal(normalize_callable_headers(src), src);
});
