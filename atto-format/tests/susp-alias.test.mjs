import test from 'node:test';
import assert from 'node:assert/strict';
import {normalize_callable_headers} from '../src/callable-headers.mjs';

const cases = [
  ['top level', 'pub suspends fnc age(): int { return 42; }', 'pub susp fnc age(): int { return 42; }'],
  ['routine', 'pub suspends routine process() -> int { return 42; }', 'pub susp routine process() -> int { return 42; }'],
  ['method', 'define class Foo as\n  suspends mtd load(): int { return 42; }\nend',
    'define class Foo as\n  susp mtd load(): int { return 42; }\nend'],
  ['static', 'define class Foo as\n  static suspends fnc open(): int { return 42; }\nend',
    'define class Foo as\n  static susp fnc open(): int { return 42; }\nend'],
  ['lambda', 'const callback = suspends |v| -> { return v; };',
    'const callback = susp |v| -> { return v; };'],
  ['callable type', 'const callback: suspends fnc(int)->int = suspends |v| -> v;',
    'const callback: susp fnc(int)->int = susp |v| -> v;'],
  ['preserve comments', '// suspends fnc fake()\n/* suspends |x| -> x */\npub suspends fnc real(): int { return 42; }',
    '// suspends fnc fake()\n/* suspends |x| -> x */\npub susp fnc real(): int { return 42; }'],
  ['preserve strings', 'const message = "suspends fnc foo()";\nconst f = suspends |v| -> v;',
    'const message = "suspends fnc foo()";\nconst f = susp |v| -> v;'],
  ['do not rewrite identifier prefixes', 'pub fnc suspends_data(): int { return 42; }',
    'pub fnc suspends_data(): int { return 42; }'],
  ['do not rewrite unrelated words', 'let value = suspends + fnc_name;',
    'let value = suspends + fnc_name;'],
  ['suspending generator retains generator marker', 'pub suspends fnc *gen values(): Generator<int> { yield 42; }',
    'pub susp fnc *gen values(): Generator<int> { yield 42; }'],
  ['comment trivia between effect and fnc', 'pub suspends /* keep this */ fnc value(): int { return 42; }',
    'pub susp /* keep this */ fnc value(): int { return 42; }'],
  ['symbol marker does not become an effect', 'const stage = #ready; pub suspends fnc value(): int { return 42; }',
    'const stage = #ready; pub susp fnc value(): int { return 42; }'],
  ['invalid hash-lambda remains untouched', 'const cb = # |v| -> v;',
    'const cb = # |v| -> v;'],
  ['already canonical', 'pub susp fnc age(): int { return 42; }',
    'pub susp fnc age(): int { return 42; }']
];

for (const [name,input,expected] of cases) {
  test(name, () => {
    const formatted = normalize_callable_headers(input);
    assert.equal(formatted, expected);
    assert.equal(normalize_callable_headers(formatted), formatted, 'formatter must be idempotent');
  });
}

test('duplicate modifiers are never removed by the formatter', () => {
  assert.equal(normalize_callable_headers('pub suspends susp fnc f() {}'),
    'pub suspends susp fnc f() {}');
  assert.equal(normalize_callable_headers('pub susp suspends fnc f() {}'),
    'pub susp susp fnc f() {}');
});
