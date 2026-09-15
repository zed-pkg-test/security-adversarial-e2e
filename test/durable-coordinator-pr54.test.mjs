import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import test from "node:test";
import { pathToFileURL } from "node:url";

const sourceRoot = process.env.SOURCE_ROOT;
if (!sourceRoot) throw new Error("SOURCE_ROOT is required");

const coordinatorRoot = path.join(sourceRoot, "modules/cloudflare/durable-coordinator");
const protocol = await import(pathToFileURL(path.join(coordinatorRoot, "protocol.mjs")));

test("accepts ecosystem-realistic package lock keys", () => {
  assert.equal(protocol.normalizeKey("@scope/package"), "@scope/package");
  assert.equal(protocol.normalizeKey("package:@scope/package"), "package:@scope/package");
  assert.equal(protocol.normalizeKey("formula:libfoo+ssl"), "formula:libfoo+ssl");
  assert.equal(protocol.normalizeKey("crate:serde_json"), "crate:serde_json");
});

test("rejects traversal, separators outside the contract, and oversized keys", () => {
  assert.throws(() => protocol.normalizeKey("../escape"), TypeError);
  assert.throws(() => protocol.normalizeKey("package:@scope/../escape"), TypeError);
  assert.throws(() => protocol.normalizeKey("pkg\\windows"), TypeError);
  assert.throws(() => protocol.normalizeKey("x".repeat(257)), TypeError);
});

test("lease TTL and expiry boundaries are deterministic", () => {
  assert.equal(protocol.normalizeTtlMs(1_000), 1_000);
  assert.equal(protocol.normalizeTtlMs(300_000), 300_000);
  assert.throws(() => protocol.normalizeTtlMs(999), RangeError);
  assert.throws(() => protocol.normalizeTtlMs(300_001), RangeError);
  assert.equal(protocol.leaseIsLive({ expires_at: 5001 }, 5000), true);
  assert.equal(protocol.leaseIsLive({ expires_at: 5000 }, 5000), false);
});

test("worker uses transactional monotonic fencing tokens", () => {
  const worker = fs.readFileSync(path.join(coordinatorRoot, "worker.mjs"), "utf8");
  assert.match(worker, /ctx\.storage\.transaction/);
  assert.match(worker, /Math\.max\(counter, current\?\.fencing_token \?\? 0\) \+ 1/);
  assert.match(worker, /current\.holder !== normalizedHolder/);
  assert.match(worker, /current\.fencing_token !== fencingToken/);
});

test("Wrangler binds ZedPackageCoordinator consistently", () => {
  const wrangler = fs.readFileSync(path.join(coordinatorRoot, "wrangler.jsonc"), "utf8");
  const bindings = (wrangler.match(/"name"\s*:\s*"COORDINATOR"/g) || []).length;
  const classes = (wrangler.match(/"class_name"\s*:\s*"ZedPackageCoordinator"/g) || []).length;
  assert.ok(bindings >= 4, `expected root + 3 environment bindings, got ${bindings}`);
  assert.equal(classes, bindings);
  assert.match(wrangler, /"storage"\s*:\s*"sqlite"/);
});
