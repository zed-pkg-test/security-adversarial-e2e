/** Admission gate for canonicalizing Atto method/receiver headers.
 * The caller must supply the *real* compiler, not a JS syntax simulation.
 * A normalized result is usable only when both sources compile to exactly
 * the same guest binary. Unsupported/invalid source fails closed.
 */
import { normalize_callable_headers } from './callable-headers.mjs';

export async function normalize_verified_callable_headers(source, compileGuest) {
  if (typeof source !== 'string' || typeof compileGuest !== 'function')
    throw new TypeError('Source and compiler callback are required');
  if (Buffer.byteLength(source, 'utf8') > 1024 * 1024)
    throw new RangeError('Atto source exceeds formatter admission size limit');
  const formatted = normalize_callable_headers(source);
  const read = async (text) => {
    const guest = await compileGuest(text);
    if (!(guest instanceof Uint8Array) || guest.byteLength < 8 ||
        guest.byteLength > 16 * 1024 * 1024 ||
        Buffer.from(guest.subarray(0, 8)).toString('hex') !== '0061736d01000000')
      throw new Error('Compiler did not return a bounded guest Wasm binary with valid header');
    if (!WebAssembly.validate(guest))
      throw new Error('Compiler returned an invalid guest Wasm module');
    return Buffer.from(guest);
  };
  const before = await read(source);
  const after = formatted === source ? before : await read(formatted);
  if (!before.equals(after))
    throw new Error('Unsafe callable formatting: guest binary changed');
  return { ok: true, changed: formatted !== source, formatted, guest_sha256_same: true };
}
