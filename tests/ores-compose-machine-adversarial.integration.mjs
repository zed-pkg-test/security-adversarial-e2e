import assert from 'node:assert/strict';
import test from 'node:test';

const SHA = '5dbda2127357b4be87821902d36e4ce9560f6876';
const BASE = `https://raw.githubusercontent.com/ORESoftware/ores-interfaces/${SHA}/contracts/ores-compose-machine/v1`;
const response = await fetch(`${BASE}/authored.schema.json`);
assert.equal(response.status, 200);
const defs = (await response.json()).$defs;

test('ensure contract has no arbitrary command or network target injection fields', () => {
  for (const field of ['command','args','argv','shell','cwd','url','host','port','socket','backend']) {
    assert.equal(defs.EnsureRequest.properties[field], undefined, field);
  }
  assert.equal(defs.EnsureRequest.additionalProperties, false);
});

test('routing-label grammar blocks uppercase underscore traversal-shaped identities', () => {
  const p = new RegExp(defs.EnsureRequest.properties.session.pattern);
  for (const value of ['ADMIN', 'bad_name', '../root', '-edge', 'edge-', 'a/b']) {
    assert.equal(p.test(value), false, value);
  }
});

test('machine ingress blocks SSRF to public addresses', () => {
  const p = new RegExp(defs.MachineIngress.properties.authority.pattern);
  for (const value of ['8.8.8.8:53', '1.1.1.1:443', '169.254.169.254:80', 'example.com:443']) {
    assert.equal(p.test(value), false, value);
  }
});

test('machine ingress cannot expose runtime-private replica IPs', () => {
  const p = new RegExp(defs.MachineIngress.properties.authority.pattern);
  for (const value of ['10.0.0.7:8080', '172.18.0.2:3000', '192.168.1.90:9000']) {
    assert.equal(p.test(value), false, value);
  }
  assert.ok(p.test('127.0.0.1:40111'));
});

test('revision grammar rejects option injection and Git ref ambiguity sequences', () => {
  const p = new RegExp(defs.EnsureRequest.properties.revision.pattern);
  for (const value of ['--upload-pack=x', '-c', 'a..b', 'x@{1}', 'x~1', 'x^1', 'bad ref', 'foo//bar', 'foo/.bar', 'foo.lock']) {
    assert.equal(p.test(value), false, value);
  }
});
