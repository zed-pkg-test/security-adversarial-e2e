/** Conservative lexical normalizer for a bounded subset of AttoLang declaration headers.
 * Not a full formatter; it refuses to transform unrecognized declaration grammar.
 * Accepted spelling contract: atto-spec language/callable-body-styles-v1.md.
 */
export function normalize_callable_headers(source) {
  const toks = [];
  const word = c => /[A-Za-z_]/.test(c || '');
  const tail = c => /[A-Za-z0-9_]/.test(c || '');
  for (let i = 0; i < source.length;) {
    let s = i, c = source[i];
    if (/\s/.test(c)) { ++i; continue; }
    if (source.startsWith('//', i)) { i = source.indexOf('\n', i); if (i === -1) break; continue; }
    if (source.startsWith('/*', i)) {
      let depth = 1; i += 2;
      while (i < source.length && depth) {
        if (source.startsWith('/*', i)) { ++depth; i += 2; }
        else if (source.startsWith('*/', i)) { --depth; i += 2; }
        else ++i;
      }
      if (depth) throw new Error('unterminated block comment');
      continue;
    }
    if (c === '"' || c === "'") {
      const quote = c; ++i;
      while (i < source.length && source[i] !== quote) {
        if (source[i] === '\\') ++i;
        ++i;
      }
      if (i >= source.length) throw new Error('unterminated string literal');
      ++i; continue;
    }
    if (word(c)) { ++i; while (tail(source[i])) ++i; }
    else if (['::', '->', '<-', '=>'].some(x => source.startsWith(x, i))) i += 2;
    else ++i;
    toks.push({ s: source.slice(s, i), start: s, end: i });
  }
  const is = (i, s) => toks[i]?.s === s;
  const ident = i => /^[A-Za-z_][A-Za-z0-9_]*$/.test(toks[i]?.s || '');
  const hasComment = (start, end) => /\/\/|\/\*/.test(source.slice(start, end));
  const edits = [];
  const add = (start, end, replacement) => {
    if (source.slice(start, end) !== replacement) edits.push({ start, end, replacement });
  };
  function skipPaired(i, open, close) {
    if (!is(i, open)) return -1;
    let n = 1;
    for (let j = i + 1; j < toks.length; ++j) {
      if (is(j, open)) ++n;
      if (is(j, close) && --n === 0) return j + 1;
    }
    return -1;
  }
  // Skip a syntactically balanced type reference, including qualified
  // nested generics. This is deliberately lexical: verified formatting still
  // requires the real compiler to accept both source and normalized source.
  function skipType(i) {
    if (!ident(i)) return -1;
    let j = i + 1;
    if (is(i, 'fnc') && is(j, '(')) {
      j = skipPaired(j, '(', ')');
      if (j < 0 || !is(j, '->')) return -1;
      j = skipType(j + 1);
      if (j < 0) return -1;
    } else {
      while (true) {
        if (is(j, '<')) {
          j = skipPaired(j, '<', '>');
          if (j < 0) return -1;
        }
        if ((is(j, '.') || is(j, '::')) && ident(j + 1)) {
          j += 2;
          continue;
        }
        break;
      }
    }
    while (is(j, '?') || (is(j, '[') && is(j + 1, ']'))) {
      j += is(j, '?') ? 1 : 2;
    }
    return j;
  }
  function scanMethod(name) {
    if (!ident(name)) return -1;
    let j = name + 1;
    // Return-first inline method: int <- name(...), with optional fnc.
    // This is a declaration delimiter, not a left-directed stream operator.
    const returnFirst = is(j, '<-');
    if (returnFirst) {
      if (!ident(j + 1)) return -1;
      j += 2;
    }
    // Generic parameters are part of the method header, before '('.
    // Never confuse an unclosed '<' with a callable body or class 'end'.
    if (is(j, '<')) {
      j = skipPaired(j, '<', '>');
      if (j < 0) return -1;
    }
    if (!is(j, '(')) return -1;
    j = skipPaired(j, '(', ')');
    if (j < 0) return -1;
    let arrowType = !returnFirst && is(j, '->');
    let colonType = !returnFirst && is(j, ':');
    // No omitted return is allowed. A return-first header already carried
    // a complete result, and cannot declare a second result after params.
    if (!returnFirst && !arrowType && !colonType) return -1;
    if (returnFirst && (is(j, '->') || is(j, ':'))) return -1;
    if (!returnFirst) {
      j = skipType(j + 1);
      if (j < 0) return -1;
    }
    if (colonType && is(j, '->')) ++j;
    if (is(j, '{')) return skipPaired(j, '{', '}');
    // Explicit statement/end allows empty bodies. All source body-family
    // spellings must be preserved verbatim by the lexical formatter.
    if (is(j, 'begin')) ++j;
    else if (!returnFirst && !arrowType) return -1;
    else if (!returnFirst && is(j, '::')) ++j;
    let nestedEnd = 0;
    for (; j < toks.length; ++j) {
      if (is(j, '{')) { j = skipPaired(j, '{', '}'); if (j < 0) return -1; --j; continue; }
      if (is(j, 'match') || is(j, 'switch') || is(j, 'select') || is(j, 'begin')) ++nestedEnd;
      else if (is(j, 'end')) { if (nestedEnd) --nestedEnd; else return j + 1; }
    }
    return -1;
  }
  for (let i = 0; i < toks.length; ++i) {
    if (!is(i, 'define') || !(is(i + 1, 'class') || is(i + 1, 'actor'))) continue;
    let as = i + 3;
    while (as < toks.length && as < i + 20 && !is(as, 'as')) ++as;
    if (!is(as, 'as')) continue;
    let j = as + 1;
    while (j < toks.length && !is(j, 'end')) {
      if (is(j, 'pub') || is(j, 'private')) { ++j; continue; }
      if (is(j, 'fnc') || is(j, 'method')) {
        const finish = scanMethod(j + 1);
        if (finish < 0) break;
        if (!hasComment(toks[j].start, toks[j + 1].start))
          add(toks[j].start, toks[j + 1].start, '');
        j = finish; continue;
      }
      if (is(j, 'static') && is(j + 1, 'fnc')) {
        const finish = scanMethod(j + 2);
        if (finish < 0) break;
        j = finish; continue;
      }
      if (ident(j) && (is(j + 1, '(') || is(j + 1, '<') || is(j + 1, '<-'))) {
        const finish = scanMethod(j);
        if (finish < 0) break;
        j = finish; continue;
      }
      while (j < toks.length && !is(j, ';') && !is(j, 'end')) ++j;
      if (is(j, ';')) ++j;
    }
    i = j;
  }
  for (let i = 0; i < toks.length; ++i) {
    if (!is(i, 'mtd') || !is(i + 1, '(')) continue;
    const close = skipPaired(i + 1, '(', ')') - 1;
    if (close <= i + 1 || !ident(close + 1) ||
        !(is(close + 2, '(') || is(close + 2, '<-'))) continue;
    // Never normalize out-of-line receiver names when their named callable
    // lacks an explicit return result (including void or infer).
    if (scanMethod(close + 1) < 0) continue;
    if (hasComment(toks[i + 1].start, toks[close].end)) continue;
    const r = toks.slice(i + 2, close).map(x => x.s);
    let canonical = null;
    if (r.length === 3 && r[0] === 'self' && r[1] === ':' && ident(i + 4))
      canonical = `(self: ${r[2]})`;
    else if (r.length === 4 && r[0] === 'mut' && r[1] === 'self' && r[2] === ':')
      canonical = `(mut self: ${r[3]})`;
    else if (r.length === 2 && (r[1] === 'self' || r[1] === '_'))
      canonical = r[1] === 'self' ? `(self: ${r[0]})` : `(${r[0]})`;
    else if (r.length === 1) canonical = `(${r[0]})`;
    if (canonical && /^[A-Za-z_][A-Za-z0-9_]*$/.test(r.at(-1)) &&
        (r.length === 1 || /^[A-Za-z_][A-Za-z0-9_]*$/.test(r[0]) || r[0] === 'mut')) {
      add(toks[i + 1].start, toks[close].end, canonical);
    }
  }
  // Canonical spelling of the callable effect: suspends -> susp.
  // Only rewrite in known modifier positions. The tokenizer has already
  // skipped strings and comments; all other identifiers remain untouched.
  for (let i = 0; i < toks.length; ++i) {
    if (!is(i, 'suspends')) continue;
    if (['fnc', 'routine', 'mtd', 'method', '|'].some(next => is(i + 1, next)))
      add(toks[i].start, toks[i].end, 'susp');
  }
  edits.sort((a, b) => b.start - a.start);
  let result = source;
  for (const { start, end, replacement } of edits) result = result.slice(0, start) + replacement + result.slice(end);
  return result;
}
