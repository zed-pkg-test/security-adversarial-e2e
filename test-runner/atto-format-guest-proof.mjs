import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, mkdtempSync, rmSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { normalize_callable_headers } from '../atto-format/src/callable-headers.mjs';
const source = [
  'define class Counter as',
  '  pub int value: 42;',
  '  pub fnc get_value() -> int { return self.value; }',
  'end',
  'pub fnc main() -> int {',
  '  val counter = new Counter();',
  '  return counter.get_value();',
  '}',
].join('\n');
const formatted = normalize_callable_headers(source);
assert.notEqual(formatted, source, 'fixture must actually change');
assert.equal(normalize_callable_headers(formatted),formatted);
const bin=resolve('atto-src/target/debug/attoc');
const dir=mkdtempSync(join(tmpdir(),'atto-formatter-guest-'));
const compiled=[];
try {
  for (const [idx, body] of [source,formatted].entries()) {
    const file=join(dir,'case'+idx+'.atto'),out=join(dir,'case'+idx+'.wasm');
    writeFileSync(file,body);
    const r=spawnSync(bin,[file,'-o',out],{encoding:'utf8',timeout:15000});
    assert.equal(r.status,0,'compile failed: '+r.stderr);
    const bytes=readFileSync(out);
    assert.ok(WebAssembly.validate(bytes));
    const inst=new WebAssembly.Instance(new WebAssembly.Module(bytes),{atto:{print_i64:()=>{},print_bool:()=>{},print_str:()=>{},print_newline:()=>{}}});
    assert.equal(inst.exports.main(),42n);
    compiled.push(bytes);
  }
  assert.equal(compiled[0].equals(compiled[1]),true,'formatter changed compiled guest binary');
  console.log('PASS verified formatter: real guest execution returns 42 and source/normalized Wasm bytes match');
} finally { rmSync(dir,{recursive:true,force:true}); }
