import test from 'node:test';
import assert from 'node:assert/strict';
import { normalize_callable_headers } from '../src/callable-headers.mjs';

// This is a lexical formatter-safety regression, NOT an Atto compiler
// acceptance test. PR #84 proposes a struct-only equals initializer; ordinary
// callable named args remain colon-based. No token rewrite is authorized.
const unchanged = [
  'val p = Particle(x=10, y=20, velocity=1);',
  'val p = Particle{x: 10, y: 20, velocity: 1};',
  'val rows: Array<Particle, layout=soa> = [Particle(x=10, y=20, velocity=1)];',
  'val rows: Array<layout=soa, T=Particle> = [];',
  'val answer = combine(second: 2, first: 1);',
  'val invalid_call = combine(second=2, first=1);',
  'val invalid_mixed = Particle(x=10, y:20, velocity=1);',
  'val not_a_struct = object.update(x=10);',
  'val reassigned = (x = 10);',
];

for (const [i, source] of unchanged.entries()) {
  test(`preserves distinct equals/colon syntax ${i}`, () => {
    const out = normalize_callable_headers(source);
    assert.equal(out, source);
    assert.equal(normalize_callable_headers(out), out);
  });
}

test('only method header is normalized; nested field syntax stays byte-identical', () => {
  const input = [
    'define class Holder as',
    '  fnc build() -> int {',
    '    val p = Particle(x=10, y=20, velocity=1);',
    '    val q = Particle{x: 10, y: 20, velocity: 1};',
    '    return p.x + q.y;',
    '  }',
    'end',
  ].join('\n');
  const expected = input.replace('  fnc build()', '  build()');
  const output = normalize_callable_headers(input);
  assert.equal(output, expected);
  assert.equal(normalize_callable_headers(output), output);
});

test('comments and string literals never authorize a field syntax rewrite', () => {
  const source = [
    '// Particle(x=10,y=20) and combine(x: 10)',
    'val x = "Particle(x=10,y=20)";',
    '/* Particle{x:10,y:20} */',
    'val p = Particle(x=10, y=20);',
  ].join('\n');
  assert.equal(normalize_callable_headers(source), source);
});
