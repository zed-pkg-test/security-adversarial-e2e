import assert from 'node:assert/strict';
import { mkdtempSync, writeFileSync, readFileSync, existsSync, rmSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';

const compiler = resolve('atto-src/target/debug/attoc');
const temp = mkdtempSync(join(tmpdir(), 'atto-return-first-guest-'));
let executed = 0, rejected = 0;
const atto = {
  print_i64: () => {}, print_bool: () => {}, print_str: () => {},
  print_newline: () => {}, print_f64: () => {},
  actor_spawn: () => 0, actor_send: () => {},
};
function compile(source, label, expectedFailure) {
  const input = join(temp, label + '.atto'), output = join(temp, label + '.wasm');
  writeFileSync(input, source);
  const result = spawnSync(compiler, [input, '-o', output], {encoding:'utf8', timeout:15000});
  if (expectedFailure) {
    assert.equal(result.status, 1, label + ': expected fail: ' + result.stderr);
    assert.ok(result.stderr.includes(expectedFailure), label + ': expected ' + expectedFailure + '; got ' + result.stderr);
    assert.equal(existsSync(output), false, label + ': failed source must not emit guest');
    rejected++;
    return;
  }
  assert.equal(result.status, 0, label + ': compilation failed: ' + result.stderr);
  const bytes = readFileSync(output);
  assert.equal(WebAssembly.validate(bytes), true, label + ': invalid guest wasm');
  const guest = new WebAssembly.Module(bytes);
  const instance = new WebAssembly.Instance(guest, {atto});
  assert.equal(typeof instance.exports.main, 'function', label + ': no main export');
  executed++;
  return instance.exports.main();
}
const heads = [
  (t,n,p,b) => 'fnc '+n+'('+p+') -> '+t+' { '+b+' }',
  (t,n,p,b) => 'fnc '+n+'('+p+'): '+t+' { '+b+' }',
  (t,n,p,b) => 'fnc '+n+'('+p+'): '+t+' -> { '+b+' }',
  (t,n,p,b) => 'fnc '+t+' <- '+n+'('+p+') { '+b+' }',
  (t,n,p,b) => t+' <- '+n+'('+p+') { '+b+' }',
  (t,n,p,b) => t+' <- '+n+'('+p+') '+b+' end',
  (t,n,p,b) => t+' <- '+n+'('+p+') begin '+b+' end',
  (t,n,p,b) => 'fnc '+t+' <- '+n+'('+p+') begin '+b+' end',
];
const types = [
  {t:'int', n:'calculate', p:'int x', b:'return x * 2;', call:'calculate(21)', expected:42n},
  {t:'void', n:'reset', p:'', b:'', call:'reset()', expected:0n},
  {t:'infer', n:'calculate_other', p:'', b:'return 42;', call:'calculate_other()', expected:42n},
];
try {
  for (const x of types) for (let k=0;k<heads.length;k++) {
    const decl=heads[k](x.t,x.n,x.p,x.b);
    const main=x.t==='void'
      ? 'pub fnc main() -> int { '+x.call+'; return 0; }'
      : 'pub fnc main() -> int { return '+x.call+'; }';
    const got=compile(decl+'\n'+main, x.t+'-'+k);
    assert.equal(got, x.expected, x.t+' syntax variant '+k+' wrong guest result');
  }
  const negatives = [
    ['missing-annotation','fnc calculate(int x) { return x; }','E_RETURN_ANNOTATION'],
    ['double-annotation','fnc int <- calculate(int x) -> int { return x; }','E_RETURN_ANNOTATION'],
    ['split-left-arrow','int < - calculate(int x) { return x; }','E_TOPLEVEL'],
    ['missing-end','int <- calculate(int x) begin return x;','E_EOF'],
    ['missing-return','int <- calculate(int x) begin end','E_RETURN'],
    ['duplicate-signature','fnc calculate(int x) -> int { return x; }\nint <- calculate(int x) begin return x; end','E_DUPLICATE'],
  ];
  for (const [label, source, code] of negatives) {
    compile(source+'\npub fnc main() -> int { return 0; }', label, code);
  }
  console.log('PASS '+executed+' real compiled WebAssembly guests executed with correct BigInt results; '+rejected+' compiler rejections produced no artifacts');
} finally {
  rmSync(temp, {recursive:true,force:true});
}
