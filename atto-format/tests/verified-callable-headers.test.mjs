import test from 'node:test';
import assert from 'node:assert/strict';
import {readFile,writeFile,rm,mkdtemp} from 'node:fs/promises';
import {spawnSync,execFileSync} from 'node:child_process';
import {tmpdir} from 'node:os';
import {join,resolve} from 'node:path';
import {normalize_verified_callable_headers} from '../src/verified-callable-headers.mjs';
const sample='mtd (Calculator self) foo() -> int :: 5 end';
const guest=new Uint8Array([0,97,115,109,1,0,0,0]);
const differentValidGuest=new Uint8Array([...guest,0,1,0]); // valid empty-name custom section
assert.ok(WebAssembly.validate(guest));
assert.ok(WebAssembly.validate(differentValidGuest));
test('host verifier admits only binary-identical compilable rewrites',async()=>{
  const checked=await normalize_verified_callable_headers(sample,async()=>guest);
  assert.equal(checked.formatted,'mtd (self: Calculator) foo() -> int :: 5 end');
  assert.equal(checked.changed,true);
  assert.equal(checked.guest_sha256_same,true);
  await assert.rejects(()=>normalize_verified_callable_headers(sample,async text=>
    text===sample?guest:differentValidGuest),/guest binary changed/);
  await assert.rejects(()=>normalize_verified_callable_headers(sample,async()=>
    {throw new Error('E_UNSUPPORTED');}),/E_UNSUPPORTED/);
  await assert.rejects(()=>normalize_verified_callable_headers(sample,async()=>
    new Uint8Array([1,2,3])),/valid guest Wasm header/);
  await assert.rejects(()=>normalize_verified_callable_headers('x'.repeat(1024*1024+1),async()=>guest),/limit/);
  await assert.rejects(()=>normalize_verified_callable_headers(sample,async()=>new Uint8Array([...guest,77])),/invalid guest Wasm module/);
  await assert.rejects(()=>normalize_verified_callable_headers(sample,async()=>new Uint8Array(16*1024*1024+1)),/bounded guest Wasm binary/);
  await assert.rejects(()=>normalize_verified_callable_headers(sample,null),/required/);
});
const attoc=process.env.ATTOC?resolve(process.env.ATTOC):null;
async function compileGuest(source) {
  const dir=await mkdtemp(join(tmpdir(),'atto-format-integration-'));
  try{
    const inFile=join(dir,'sample.atto'),outFile=join(dir,'guest.wasm');
    await writeFile(inFile,source);
    execFileSync(attoc,[inFile,'-o',outFile],{timeout:15000});
    return await readFile(outFile);
  } finally {await rm(dir,{recursive:true,force:true});}
}
test('real merged Atto compiler agrees on class method guest bytes and format idempotence',
  {skip:!attoc},async()=>{
    for(const fixture of ['immutable-class-mtd.atto','inline-legacy-prefixes.atto']){
      const source=await readFile(new URL('fixtures/'+fixture,import.meta.url),'utf8');
      const result=await normalize_verified_callable_headers(source,compileGuest);
      assert.equal(result.ok,true);
      assert.equal(result.changed,true,fixture+' should canonicalize a legacy form');
      const twice=await normalize_verified_callable_headers(result.formatted,compileGuest);
      assert.equal(twice.changed,false,'idempotent formatter');
      assert.equal(twice.formatted,result.formatted);
      assert.equal(result.guest_sha256_same,true);
    }
});
test('CLI refuses invalid code, and --check/--write preserve the executable meaning',
  {skip:!attoc},async()=>{
    const dir=await mkdtemp(join(tmpdir(),'atto-format-cli-'));
    const tool=new URL('../tools/atto-format-callable.mjs',import.meta.url).pathname;
    const env={...process.env,ATTOC:attoc};
    try{
      const original=await readFile(new URL('fixtures/inline-legacy-prefixes.atto',import.meta.url),'utf8');
      const file=join(dir,'file.atto');
      await writeFile(file,original);
      const check=spawnSync(process.execPath,[tool,'--check',file],{encoding:'utf8',env});
      assert.equal(check.status,1,'--check reports noncanonical source');
      assert.equal(await readFile(file,'utf8'),original,'--check must not mutate source');
      const changed=spawnSync(process.execPath,[tool,'--write',file],{encoding:'utf8',env});
      assert.equal(changed.status,0,changed.stderr);
      const after=await readFile(file,'utf8');
      assert.notEqual(after,original);
      assert.equal((await compileGuest(original)).toString('hex'),(await compileGuest(after)).toString('hex'));
      const stable=spawnSync(process.execPath,[tool,'--check',file],{encoding:'utf8',env});
      assert.equal(stable.status,0,stable.stderr);
      await writeFile(file,'define class C as mtd (C self) x() -> int :: 5 end');
      const invalid=spawnSync(process.execPath,[tool,'--write',file],{encoding:'utf8',env});
      assert.notEqual(invalid.status,0,'invalid program must not be changed');
      assert.equal(await readFile(file,'utf8'),'define class C as mtd (C self) x() -> int :: 5 end');
    }finally{await rm(dir,{recursive:true,force:true});}
});
