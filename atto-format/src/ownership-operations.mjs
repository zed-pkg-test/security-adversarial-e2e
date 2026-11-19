/**
 * Conservative ownership-operator formatter.
 *
 * We do NOT split or rewrite copy!!, copy! !value, borrow! mut, take!,
 * share!, freeze!, weak!, pin!, drop! or mut. They have different static
 * rights, and whitespace-based guesses could silently weaken a program.
 *
 * Only a contextually admitted lifetime! binder is canonicalized to lt!.
 * The lexical pass is not a parser or compiler proof; see verified wrapper.
 */
const isStart = c => /[A-Za-z_]/.test(c || '');
const isTail = c => /[A-Za-z0-9_]/.test(c || '');
const WS = c => /\s/.test(c || '');

export function normalize_ownership_operations(source) {
  if (typeof source !== 'string')
    throw new TypeError('Expected Atto source string');
  if (Buffer.byteLength(source, 'utf8') > 1024 * 1024)
    throw new RangeError('Atto source exceeds ownership normalizer limit');
  const edits = [];
  for (let i = 0; i < source.length;) {
    const start = i;
    const c = source[i];
    if (WS(c)) { ++i; continue; }
    if (source.startsWith('//', i)) {
      const end = source.indexOf('\n', i);
      i = end < 0 ? source.length : end;
      continue;
    }
    if (source.startsWith('/*', i)) {
      let depth = 1;
      i += 2;
      while (i < source.length && depth) {
        if (source.startsWith('/*', i)) { ++depth; i += 2; }
        else if (source.startsWith('*/', i)) { --depth; i += 2; }
        else ++i;
      }
      if (depth) throw new SyntaxError('Unterminated nested block comment');
      continue;
    }
    if (c === '"' || c === "'" || c === '\x60') {
      // Quote and template contents are intentionally opaque. Escapes must
      // not expose fake operators or lifetime declarations to the scanner.
      const quote = c;
      ++i;
      while (i < source.length && source[i] !== quote) {
        if (source[i] === '\\') ++i;
        ++i;
      }
      if (i >= source.length) throw new SyntaxError('Unterminated quoted literal');
      ++i;
      continue;
    }
    if (!isStart(c)) { ++i; continue; }
    ++i;
    while (isTail(source[i])) ++i;
    const word = source.slice(start, i);
    if (word !== 'lifetime' || source[i] !== '!' || source[i + 1] === '!') continue;
    let next = i + 1;
    while (WS(source[next])) ++next;
    // Do not normalize a comment-separated binder, operator, method member,
    // or unknown grammar. A real compiler must verify all other rewrites.
    if (!isStart(source[next])) continue;
    const before = source.slice(0, start);
    const lastNonspace = before.trimEnd().at(-1);
    const atNewline = /\n[ \t]*$/.test(before);
    if (!(start === 0 || atNewline || '<,({;'.includes(lastNonspace))) continue;
    edits.push({ start, end: i, replacement: 'lt' });
  }
  let result = source;
  for (const edit of edits.reverse()) {
    result = result.slice(0, edit.start) + edit.replacement + result.slice(edit.end);
  }
  return result;
}

/**
 * Production callers MUST pass the real compiler to validate both variants.
 * Equal Wasm guest bytes prove only equivalent admitted output for that
 * particular source/toolchain; host-only parser stubs are not guest evidence.
 */
export async function normalize_verified_ownership_operations(source, compileGuest) {
  if (typeof compileGuest !== 'function')
    throw new TypeError('A real guest compiler callback is required');
  const formatted = normalize_ownership_operations(source);
  const compile = async text => {
    const binary = await compileGuest(text);
    if (!(binary instanceof Uint8Array) || binary.byteLength < 8 ||
        binary.byteLength > 16 * 1024 * 1024 ||
        Buffer.from(binary.subarray(0, 8)).toString('hex') !== '0061736d01000000' ||
        !WebAssembly.validate(binary))
      throw new Error('Guest compiler did not return bounded, structurally valid WebAssembly');
    return Buffer.from(binary);
  };
  const original = await compile(source);
  const rewritten = formatted === source ? original : await compile(formatted);
  if (!original.equals(rewritten))
    throw new Error('Ownership formatting changed emitted guest semantics');
  return { formatted, changed: formatted !== source, guest_binary_equal: true };
}
