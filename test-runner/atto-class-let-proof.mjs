import assert from 'node:assert/strict';
import { mkdtempSync, writeFileSync, readFileSync, existsSync, rmSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
const dir=mkdtempSync(join(tmpdir(),'atto-class-let-'));
const compiler=resolve('atto-let-src/target/debug/attoc');
let ok=0,denied=0;
function check(name,source,expected,err){
  const inFile=join(dir,name+'.atto'),outFile=join(dir,name+'.wasm');
  writeFileSync(inFile,source);
  const process=spawnSync(compiler,[inFile,'-o',outFile],{encoding:'utf8',timeout:15000});
  if(err){
    assert.equal(process.status,1,name+': expected compile rejection '+process.stderr);
    assert.ok(process.stderr.includes(err),name+': '+process.stderr);
    assert.equal(existsSync(outFile),false,name+': compiler rejection emitted artifact');
    denied++;return;
  }
  assert.equal(process.status,0,name+': '+process.stderr);
  const bytes=readFileSync(outFile);
  assert.ok(WebAssembly.validate(bytes),name+': malformed guest');
  const guest=new WebAssembly.Instance(new WebAssembly.Module(bytes),{atto:{print_i64:()=>{},print_bool:()=>{},print_str:()=>{},print_newline:()=>{}}});
  assert.equal(guest.exports.main(),BigInt(expected),name+': wrong guest behavior');
  ok++;
}
try {
 const base=(binding)=>[
  'define class Counter as',
  '  pub '+binding+'int count = 1;',
  '  constructor() { self.count = 3; }',
  'end',
  'pub fnc main() -> int {',
  '  val counter = new Counter();',
  '  return counter.count;',
  '}',
 ].join('\n');
 check('implicit-let',base(''),3);
 check('explicit-let',base('let '),3);
 check('explicit-val-reject',base('val '),null,'E_IMMUTABLE');
 check('readonly-receiver-reject',[
  'define class C as',
  ' pub int count = 1;',
  ' change(): int { self.count = 2; return self.count; }',
  'end',
  'pub fnc main() -> int { return 0; }',
 ].join('\n'),null,'E_OWNERSHIP');
 console.log('PASS '+ok+' compiled class-field-let Wasm guests; '+denied+' compile-time rejections with no artifacts');
} finally{ rmSync(dir,{recursive:true,force:true}); }
