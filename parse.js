// parse.js — a dependency-free Markdown renderer.
//
// parse(markdown) returns the HTML that marked 18.1.3 renders with its default
// options (GFM on, breaks off). This is an independent implementation written
// from the CommonMark 0.31.2 and GFM 0.29 specifications plus marked's
// observable behaviour on probe inputs; no part of marked's source is used.
//
// Structure: a line-based block parser builds a block tree (handling
// blockquotes, lists, code, HTML blocks, tables and link reference
// definitions), then an inline parser renders each leaf's text with the
// delimiter-stack emphasis algorithm, link resolution and GFM autolinks.

const TAB = 9;
const LF = 10;
const SPACE = 32;

// ---------- character classification ----------

function isSpaceTab(code) {
  return code === SPACE || code === TAB;
}

// Whitespace allowed inside an HTML tag: space, tab, newline, vertical tab
// and form feed (tags may span lines).
function isTagSpace(code) {
  return code === SPACE || code === TAB || code === LF || code === 11 || code === 12;
}

function isAsciiPunct(code) {
  return (code >= 33 && code <= 47) || (code >= 58 && code <= 64) ||
    (code >= 91 && code <= 96) || (code >= 123 && code <= 126);
}

function isAsciiLetter(code) {
  return (code >= 65 && code <= 90) || (code >= 97 && code <= 122);
}

function isAsciiDigit(code) {
  return code >= 48 && code <= 57;
}

function isWordChar(code) {
  return isAsciiLetter(code) || isAsciiDigit(code) || code === 95;
}

const UNICODE_PUNCT = /[\p{P}\p{S}]/u;
const UNICODE_SPACE = /\s/u;

// The full character (one or two code units) starting at index i, or ''.
function charAt(str, i) {
  if (i < 0 || i >= str.length) return '';
  const c = str.charCodeAt(i);
  if (c >= 0xD800 && c <= 0xDBFF && i + 1 < str.length) {
    const d = str.charCodeAt(i + 1);
    if (d >= 0xDC00 && d <= 0xDFFF) return str.slice(i, i + 2);
  }
  return str[i];
}

// The full character ending at index i, or ''.
function charBefore(str, i) {
  if (i <= 0) return '';
  const c = str.charCodeAt(i - 1);
  if (c >= 0xDC00 && c <= 0xDFFF && i - 2 >= 0) {
    const d = str.charCodeAt(i - 2);
    if (d >= 0xD800 && d <= 0xDBFF) return str.slice(i - 2, i);
  }
  return str[i - 1];
}

function isPunctChar(ch) {
  if (ch === '') return false;
  const code = ch.charCodeAt(0);
  if (code < 128) return isAsciiPunct(code);
  return UNICODE_PUNCT.test(ch);
}

function isSpaceChar(ch) {
  // Start/end of text count as whitespace for flanking purposes.
  if (ch === '') return true;
  const code = ch.charCodeAt(0);
  if (code < 128) {
    return code === SPACE || code === TAB || code === LF || code === 13 ||
      code === 12 || code === 11;
  }
  return UNICODE_SPACE.test(ch);
}

// ---------- escaping and entities ----------

// Escape & < > " ' with no entity processing. Used for text nodes (whose
// entities were already resolved while scanning) and for code content.
const RE_ESCAPABLE = /[&<>"']/;

function escapeRaw(s) {
  if (!RE_ESCAPABLE.test(s)) return s;
  let out = '';
  let start = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    let rep = null;
    if (c === 38) rep = '&amp;';
    else if (c === 60) rep = '&lt;';
    else if (c === 62) rep = '&gt;';
    else if (c === 34) rep = '&quot;';
    else if (c === 39) rep = '&#39;';
    if (rep !== null) {
      out += s.slice(start, i) + rep;
      start = i + 1;
    }
  }
  return start === 0 ? s : out + s.slice(start);
}

function decodeNumericEntity(digits, hex) {
  let n = 0;
  if (hex) {
    for (let k = 0; k < digits.length; k++) {
      const c = digits.charCodeAt(k);
      n = n * 16 + (c <= 57 ? c - 48 : (c <= 70 ? c - 55 : c - 87));
    }
  } else {
    for (let k = 0; k < digits.length; k++) {
      n = n * 10 + (digits.charCodeAt(k) - 48);
    }
  }
  if (n === 0 || n > 0x10FFFF || (n >= 0xD800 && n <= 0xDFFF)) return '\uFFFD';
  return String.fromCodePoint(n);
}

// Scan an entity reference starting at s[i] === '&'. Returns
// {len, raw, decoded, numeric} or null. Numeric references allow 1-7 decimal
// or 1-6 hexadecimal digits; named references are &word; with word characters.
function scanEntity(s, i) {
  const n = s.length;
  let j = i + 1;
  if (j < n && s.charCodeAt(j) === 35) {
    j++;
    let hex = false;
    if (j < n && (s.charCodeAt(j) === 120 || s.charCodeAt(j) === 88)) {
      hex = true;
      j++;
    }
    const d0 = j;
    const maxLen = hex ? 6 : 7;
    while (j < n && j - d0 < maxLen) {
      const c = s.charCodeAt(j);
      const ok = hex
        ? (c >= 48 && c <= 57) || (c >= 65 && c <= 70) || (c >= 97 && c <= 102)
        : (c >= 48 && c <= 57);
      if (!ok) break;
      j++;
    }
    if (j > d0 && j < n && s.charCodeAt(j) === 59) {
      return {
        len: j + 1 - i,
        raw: s.slice(i, j + 1),
        decoded: decodeNumericEntity(s.slice(d0, j), hex),
        numeric: true,
      };
    }
    return null;
  }
  const w0 = j;
  while (j < n && isWordChar(s.charCodeAt(j))) j++;
  if (j > w0 && j < n && s.charCodeAt(j) === 59) {
    return { len: j + 1 - i, raw: s.slice(i, j + 1), decoded: '', numeric: false };
  }
  return null;
}

// Attribute escaping (href, title): every entity reference, named or numeric,
// passes through verbatim; every other & < > " ' is escaped.
function escapeAttr(s) {
  if (!RE_ESCAPABLE.test(s)) return s;
  let out = '';
  let start = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c === 38) {
      const e = scanEntity(s, i);
      if (e) {
        out += s.slice(start, i) + e.raw;
        i += e.len - 1;
        start = i + 1;
        continue;
      }
      out += s.slice(start, i) + '&amp;';
      start = i + 1;
    } else if (c === 60) {
      out += s.slice(start, i) + '&lt;';
      start = i + 1;
    } else if (c === 62) {
      out += s.slice(start, i) + '&gt;';
      start = i + 1;
    } else if (c === 34) {
      out += s.slice(start, i) + '&quot;';
      start = i + 1;
    } else if (c === 39) {
      out += s.slice(start, i) + '&#39;';
      start = i + 1;
    }
  }
  return start === 0 ? s : out + s.slice(start);
}

// Text escaping with entity processing (used for image alt text): named
// references pass through verbatim, numeric references decode (then escape),
// bare & < > " ' escape.
function escapeText(s) {
  if (!RE_ESCAPABLE.test(s)) return s;
  let out = '';
  let start = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c === 38) {
      const e = scanEntity(s, i);
      if (e) {
        const rep = e.numeric ? escapeRaw(e.decoded) : e.raw;
        out += s.slice(start, i) + rep;
        i += e.len - 1;
        start = i + 1;
        continue;
      }
      out += s.slice(start, i) + '&amp;';
      start = i + 1;
    } else if (c === 60) {
      out += s.slice(start, i) + '&lt;';
      start = i + 1;
    } else if (c === 62) {
      out += s.slice(start, i) + '&gt;';
      start = i + 1;
    } else if (c === 34) {
      out += s.slice(start, i) + '&quot;';
      start = i + 1;
    } else if (c === 39) {
      out += s.slice(start, i) + '&#39;';
      start = i + 1;
    }
  }
  return start === 0 ? s : out + s.slice(start);
}

// URL percent-encoding matching encodeURI, except '%' is always preserved
// verbatim (marked never double-encodes percent sequences). Lone surrogates
// are replaced.
function encodeUrl(s) {
  try {
    return encodeURI(s).replace(/%25/g, '%');
  } catch (_) {
    return encodeURI(s.replace(/[\uD800-\uDBFF](?![\uDC00-\uDFFF])|(?<![\uD800-\uDBFF])[\uDC00-\uDFFF]/g, '\uFFFD')).replace(/%25/g, '%');
  }
}

// ---------- line cursor ----------
// A cursor tracks a position inside one source line in virtual columns, so a
// tab advances to the next multiple of four. `tab` holds the virtual spaces
// left when a tab was only partly consumed.

function makeCursor(line) {
  return { s: line, i: 0, col: 0, tab: 0 };
}

function copyCursor(c) {
  return { s: c.s, i: c.i, col: c.col, tab: c.tab };
}

// Consume up to `max` columns of spaces/tabs. Returns columns consumed.
function skipIndent(c, max) {
  let n = 0;
  while (n < max) {
    if (c.tab > 0) {
      const take = Math.min(c.tab, max - n);
      c.tab -= take;
      c.col += take;
      n += take;
    } else if (c.i < c.s.length && c.s.charCodeAt(c.i) === SPACE) {
      c.i++;
      c.col++;
      n++;
    } else if (c.i < c.s.length && c.s.charCodeAt(c.i) === TAB) {
      const w = 4 - (c.col % 4);
      if (n + w > max) {
        c.tab = w - (max - n);
        c.i++;
        c.col += max - n;
        n = max;
      } else {
        c.i++;
        c.col += w;
        n += w;
      }
    } else {
      break;
    }
  }
  return n;
}

// The rest of the line from the cursor, with any partly-consumed tab rendered
// as the spaces that remain of it.
function restOfLine(c) {
  return (c.tab > 0 ? ' '.repeat(c.tab) : '') + c.s.slice(c.i);
}

// True when everything from the cursor to the end of the line is blank.
function isBlankRest(c) {
  for (let i = c.i; i < c.s.length; i++) {
    const ch = c.s.charCodeAt(i);
    if (ch !== SPACE && ch !== TAB) return false;
  }
  return true;
}

// The line content after skipping at most `n` columns of indentation, or null
// when the indentation exceeds `n`. Returns {text, indent}.
function indentAndContent(c, n) {
  const d = copyCursor(c);
  const used = skipIndent(d, n);
  if (d.tab > 0) return null;
  if (d.i < d.s.length) {
    const ch = d.s.charCodeAt(d.i);
    if (ch === SPACE || ch === TAB) return null;
  }
  return { text: d.s.slice(d.i), indent: used, cursor: d };
}

// ---------- HTML tags ----------

const BLOCK_TAGS = new Set(
  'address article aside base basefont blockquote body caption center col colgroup dd details dialog dir div dl dt fieldset figcaption figure footer form frame frameset h1 h2 h3 h4 h5 h6 head header hr html iframe legend li link main menu menuitem nav noframes ol optgroup option p param search section summary table tbody td tfoot th thead title tr track ul'.split(' ')
);

// Scan an HTML tag starting at s[start] === '<'. Returns the tag length, or 0
// when the text does not form a complete open or close tag. Covers open tags
// (name, attributes, optional /), close tags, comments, processing
// instructions, declarations and CDATA sections.
function scanHtmlTag(s, start) {
  const n = s.length;
  if (start + 1 >= n || s.charCodeAt(start) !== 60) return 0;
  // Comment (<!--> and <!---> are complete, abruptly closed comments).
  if (s.startsWith('<!--', start)) {
    if (start + 4 < n && s.charCodeAt(start + 4) === 62) return 5;
    if (start + 5 < n && s.charCodeAt(start + 4) === 45 && s.charCodeAt(start + 5) === 62) return 6;
    const e = s.indexOf('-->', start + 4);
    return e === -1 ? 0 : e + 3 - start;
  }
  // Processing instruction.
  if (s.startsWith('<?', start)) {
    const e = s.indexOf('?>', start + 2);
    return e === -1 ? 0 : e + 2 - start;
  }
  // Declaration: <! + uppercase letter, up to the next '>'.
  if (s.startsWith('<!', start) && start + 2 < n) {
    const c = s.charCodeAt(start + 2);
    if (c >= 65 && c <= 90) {
      const e = s.indexOf('>', start + 3);
      return e === -1 ? 0 : e + 1 - start;
    }
  }
  // CDATA section.
  if (s.startsWith('<![CDATA[', start)) {
    const e = s.indexOf(']]>', start + 9);
    return e === -1 ? 0 : e + 3 - start;
  }
  let i = start + 1;
  let closing = false;
  if (i < n && s.charCodeAt(i) === 47) {
    closing = true;
    i++;
  }
  // Tag name.
  if (i >= n || !isAsciiLetter(s.charCodeAt(i))) return 0;
  i++;
  while (i < n) {
    const c = s.charCodeAt(i);
    if (isAsciiLetter(c) || isAsciiDigit(c) || c === 45) i++;
    else break;
  }
  if (closing) {
    while (i < n && isTagSpace(s.charCodeAt(i))) i++;
    return i < n && s.charCodeAt(i) === 62 ? i + 1 - start : 0;
  }
  // Attributes.
  while (true) {
    let hadSpace = false;
    while (i < n && isTagSpace(s.charCodeAt(i))) {
      i++;
      hadSpace = true;
    }
    if (i >= n) return 0;
    const c = s.charCodeAt(i);
    if (c === 62) return i + 1 - start;
    if (c === 47) {
      if (i + 1 < n && s.charCodeAt(i + 1) === 62) return i + 2 - start;
      return 0;
    }
    if (!hadSpace) return 0;
    // Attribute name.
    const ac = s.charCodeAt(i);
    if (!(isAsciiLetter(ac) || ac === 95 || ac === 58)) return 0;
    i++;
    while (i < n) {
      const d = s.charCodeAt(i);
      if (isAsciiLetter(d) || isAsciiDigit(d) || d === 95 || d === 58 || d === 46 || d === 45) i++;
      else break;
    }
    // Optional spaces, then an optional =value. When there is no '=', the
    // spaces stay for the separator before the next attribute.
    let j = i;
    while (j < n && isTagSpace(s.charCodeAt(j))) j++;
    if (j < n && s.charCodeAt(j) === 61) {
      j++;
      while (j < n && isTagSpace(s.charCodeAt(j))) j++;
      if (j >= n) return 0;
      const q = s.charCodeAt(j);
      if (q === 34 || q === 39) {
        j++;
        while (j < n && s.charCodeAt(j) !== q) j++;
        if (j >= n) return 0;
        j++;
      } else {
        let vlen = 0;
        while (j < n) {
          const d = s.charCodeAt(j);
          if (d === SPACE || d === TAB || d === LF || d === 34 || d === 39 ||
              d === 61 || d === 60 || d === 62 || d === 96) break;
          j++;
          vlen++;
        }
        if (vlen === 0) return 0;
      }
      i = j;
    }
  }
}

// ---------- link destinations, titles, and reference definitions ----------

// Skip spaces, tabs and line endings.
function skipLinkSpace(s, i) {
  while (i < s.length) {
    const c = s.charCodeAt(i);
    if (c === SPACE || c === TAB || c === LF) i++;
    else break;
  }
  return i;
}

// Resolve backslash escapes in a raw slice: a backslash before ASCII
// punctuation yields the punctuation; otherwise the backslash stays.
function resolveEscapes(raw) {
  if (raw.indexOf('\\') === -1) return raw;
  let out = '';
  let start = 0;
  for (let i = 0; i < raw.length; i++) {
    if (raw.charCodeAt(i) === 92 && i + 1 < raw.length &&
        isAsciiPunct(raw.charCodeAt(i + 1))) {
      out += raw.slice(start, i) + raw[i + 1];
      start = i + 2;
      i++;
    }
  }
  return start === 0 ? raw : out + raw.slice(start);
}

// Parse a link destination starting at s[i]. Returns {dest, next} or null.
// Angle form forbids <, > and newlines; bare form forbids spaces and control
// characters and allows one level of balanced parentheses.
function parseDest(s, i) {
  const n = s.length;
  if (i < n && s.charCodeAt(i) === 60) {
    let j = i + 1;
    let raw = '';
    while (j < n) {
      const c = s.charCodeAt(j);
      if (c === 62) return { dest: resolveEscapes(raw), next: j + 1 };
      if (c === 60 || c === LF) return null;
      if (c === 92 && j + 1 < n && isAsciiPunct(s.charCodeAt(j + 1))) {
        raw += s[j + 1];
        j += 2;
      } else {
        raw += s[j];
        j++;
      }
    }
    return null;
  }
  let j = i;
  let depth = 0;
  let raw = '';
  while (j < n) {
    const c = s.charCodeAt(j);
    if (c === SPACE || c === TAB || c === LF) break;
    if (c === 40) {
      depth++;
      raw += '(';
      j++;
    } else if (c === 41) {
      if (depth === 0) break;
      depth--;
      raw += ')';
      j++;
    } else if (c === 92 && j + 1 < n && isAsciiPunct(s.charCodeAt(j + 1))) {
      raw += s[j + 1];
      j += 2;
    } else if ((c < 32 && c !== TAB && c !== LF) || c === 127) {
      return null;
    } else {
      raw += s[j];
      j++;
    }
  }
  return { dest: raw, next: j };
}

// Parse a link title starting at s[i] ('"', '\'' or '('). Returns
// {title, next} or null. Titles may span lines; parenthesised titles forbid
// unescaped '(' inside.
function parseTitle(s, i) {
  const n = s.length;
  const q = s.charCodeAt(i);
  if (q !== 34 && q !== 39 && q !== 40) return null;
  const close = q === 40 ? 41 : q;
  let j = i + 1;
  let raw = '';
  while (j < n) {
    const c = s.charCodeAt(j);
    if (c === close) return { title: resolveEscapes(raw), next: j + 1 };
    if (q === 40 && c === 40) return null;
    if (c === 92 && j + 1 < n && isAsciiPunct(s.charCodeAt(j + 1))) {
      raw += s[j + 1];
      j += 2;
    } else {
      raw += s[j];
      j++;
    }
  }
  return null;
}

// Parse the tail of an inline link: "( dest title )" starting at s[i] === '('.
// Returns {dest, title, next} or null.
function parseInlineTail(s, i) {
  let j = skipLinkSpace(s, i + 1);
  const d = parseDest(s, j);
  if (d === null) return null;
  const afterDest = d.next;
  j = skipLinkSpace(s, afterDest);
  let title = null;
  if (j < s.length) {
    const c = s.charCodeAt(j);
    if (c === 34 || c === 39 || c === 40) {
      // A title needs separating whitespace after the destination.
      if (j === afterDest) return null;
      const t = parseTitle(s, j);
      if (t === null) return null;
      title = t.title;
      j = skipLinkSpace(s, t.next);
    }
  }
  if (j < s.length && s.charCodeAt(j) === 41) {
    return { dest: d.dest, title, next: j + 1 };
  }
  return null;
}

// Scan a bracketed label starting at s[i] === '['. Returns {label, next} with
// the raw label text (escapes kept, whitespace kept) or null. Labels allow
// balanced brackets and escaped brackets, span lines, and hold at most 999
// characters.
function scanLabel(s, i) {
  const n = s.length;
  let j = i + 1;
  const start = j;
  while (j < n) {
    const c = s.charCodeAt(j);
    if (c === 92 && j + 1 < n) {
      j += 2;
      continue;
    }
    // An unescaped '[' inside a reference label invalidates it.
    if (c === 91) return null;
    // Reference labels end at the first unescaped ']' (no nesting, and no
    // length limit: marked accepts labels longer than 999 characters).
    if (c === 93) {
      return { label: s.slice(start, j), next: j + 1 };
    }
    j++;
  }
  return null;
}

// Normalise a reference label: collapse whitespace runs to one space, trim,
// lowercase. Matching uses the raw label text (entities are not decoded).
function normaliseLabel(raw) {
  let out = '';
  let pendingSpace = false;
  let started = false;
  for (let i = 0; i < raw.length; i++) {
    const c = raw.charCodeAt(i);
    if (c === SPACE || c === TAB || c === LF || c === 13 || c === 12 || c === 11) {
      if (started) pendingSpace = true;
    } else {
      if (pendingSpace) {
        out += ' ';
        pendingSpace = false;
      }
      out += raw[i];
      started = true;
    }
  }
  // The lower-upper-lower round trip folds characters like ẞ/ß to "ss".
  return out.toLowerCase().toUpperCase().toLowerCase();
}

// Skip spaces only (no tabs) starting at i.
function skipSpacesOnly(s, i) {
  while (i < s.length && s.charCodeAt(i) === SPACE) i++;
  return i;
}

// Try to parse one link reference definition starting at text[i] (the '[').
// Returns {label, dest, title, next} or null. `next` points just past the
// definition (at a line ending or end of text). Only spaces (not tabs) may
// separate the parts on one line; the destination and the title may each move
// to the following line. A title that fails on the following line leaves the
// definition standing with the destination only.
function parseRefDef(text, i) {
  const n = text.length;
  const lab = scanLabel(text, i);
  if (lab === null || lab.label.length === 0) return null;
  if (normaliseLabel(lab.label) === '') return null;
  let j = lab.next;
  if (j >= n || text.charCodeAt(j) !== 58) return null;
  j++;
  // Spaces, then optionally one line ending plus spaces, before the dest.
  j = skipSpacesOnly(text, j);
  if (j < n && text.charCodeAt(j) === LF) {
    j = skipSpacesOnly(text, j + 1);
  }
  if (j >= n) return null;
  // A tab where the destination should start rejects the definition.
  if (text.charCodeAt(j) === TAB) return null;
  const d = parseDest(text, j);
  if (d === null) return null;
  // A bare destination may not be empty.
  if (d.dest === '' && text.charCodeAt(j) !== 60) return null;
  const afterDest = d.next;
  j = skipSpacesOnly(text, afterDest);
  if (j >= n || text.charCodeAt(j) === LF) {
    // No title on this line: try one on the next line.
    if (j < n && text.charCodeAt(j) === LF) {
      let k = skipSpacesOnly(text, j + 1);
      if (k < n) {
        const c = text.charCodeAt(k);
        if (c === 34 || c === 39 || c === 40) {
          const t = parseTitle(text, k);
          if (t !== null) {
            const e = skipSpacesOnly(text, t.next);
            if (e >= n || text.charCodeAt(e) === LF) {
              return { label: lab.label, dest: d.dest, title: t.title, next: e };
            }
          }
        }
      }
    }
    return { label: lab.label, dest: d.dest, title: null, next: j };
  }
  // A title on the same line needs at least one separating space.
  if (j === afterDest) return null;
  const c = text.charCodeAt(j);
  if (c === 34 || c === 39 || c === 40) {
    const t = parseTitle(text, j);
    if (t === null) return null;
    const e = skipSpacesOnly(text, t.next);
    if (e >= n || text.charCodeAt(e) === LF) {
      return { label: lab.label, dest: d.dest, title: t.title, next: e };
    }
    return null;
  }
  return null;
}

// ---------- block-start matchers ----------

function matchATX(c) {
  const r = indentAndContent(c, 3);
  if (r === null) return null;
  const s = r.text;
  let i = 0;
  while (i < s.length && s.charCodeAt(i) === 35) i++;
  if (i === 0 || i > 6) return null;
  if (i < s.length) {
    const ch = s.charCodeAt(i);
    if (ch !== SPACE && ch !== TAB) return null;
  }
  let text = s.slice(i);
  let a = 0;
  while (a < text.length && isSpaceTab(text.charCodeAt(a))) a++;
  let b = text.length;
  while (b > a && isSpaceTab(text.charCodeAt(b - 1))) b--;
  text = text.slice(a, b);
  // Strip a closing sequence: a run of '#' preceded by whitespace.
  let e = text.length;
  while (e > 0 && text.charCodeAt(e - 1) === 35) e--;
  if (e < text.length && (e === 0 || isSpaceTab(text.charCodeAt(e - 1)))) {
    let f = e;
    while (f > 0 && isSpaceTab(text.charCodeAt(f - 1))) f--;
    text = text.slice(0, f);
  }
  return { level: i, text };
}

function matchFence(c) {
  const r = indentAndContent(c, 3);
  if (r === null) return null;
  const s = r.text;
  const ch = s.charCodeAt(0);
  if (ch !== 96 && ch !== 126) return null;
  let i = 0;
  while (i < s.length && s.charCodeAt(i) === ch) i++;
  if (i < 3) return null;
  const info = s.slice(i);
  if (ch === 96 && info.indexOf('`') !== -1) return null;
  // Strip count for backtick fences: the number of leading whitespace
  // characters on the fence line (marked's indentCodeCompensation).
  return { fenceChar: ch, fenceLen: i, info, indent: r.indent, strip: c.tab + (r.cursor.i - c.i) };
}

// Mirror of marked's indent compensation: remove up to n leading
// whitespace characters from a fenced-code content line.
function stripLeadWs(text, n) {
  const m = LEAD_WS.exec(text);
  if (m === null) return text;
  return text.slice(Math.min(m[0].length, n));
}

function isClosingFence(c, fenceChar, fenceLen) {
  const r = indentAndContent(c, 3);
  if (r === null) return false;
  const s = r.text;
  let i = 0;
  while (i < s.length && s.charCodeAt(i) === fenceChar) i++;
  if (i < fenceLen) return false;
  while (i < s.length && isSpaceTab(s.charCodeAt(i))) i++;
  return i === s.length;
}

function matchHR(c) {
  const r = indentAndContent(c, 3);
  if (r === null) return false;
  const s = r.text;
  let ch = -1;
  let count = 0;
  for (let i = 0; i < s.length; i++) {
    const code = s.charCodeAt(i);
    if (code === SPACE || code === TAB) continue;
    if (ch === -1) {
      if (code !== 42 && code !== 45 && code !== 95) return false;
      ch = code;
      count = 1;
    } else if (code === ch) {
      count++;
    } else {
      return false;
    }
  }
  return count >= 3;
}

function matchSetext(c) {
  const r = indentAndContent(c, 3);
  if (r === null) return 0;
  const s = r.text;
  const ch = s.charCodeAt(0);
  if (ch !== 61 && ch !== 45) return 0;
  let i = 1;
  while (i < s.length && s.charCodeAt(i) === ch) i++;
  while (i < s.length && isSpaceTab(s.charCodeAt(i))) i++;
  if (i !== s.length) return 0;
  return ch === 61 ? 1 : 2;
}

function matchQuoteStart(c) {
  const d = copyCursor(c);
  skipIndent(d, 3);
  if (d.tab === 0 && d.i < d.s.length && d.s.charCodeAt(d.i) === 62) {
    d.i++;
    d.col++;
    // The marker consumes at most one literal space; a following tab stays
    // content. Quote content is measured from virtual column 2, reset at
    // every quote level, so a leading tab always expands to two spaces.
    if (d.i < d.s.length && d.s.charCodeAt(d.i) === SPACE) {
      d.i++;
      d.col++;
    }
    d.col = 2;
    return d;
  }
  return null;
}

function matchListMarker(c, paraOpen, paraInItem) {
  const r = indentAndContent(c, 3);
  if (r === null) return null;
  const s = r.text;
  let i = 0;
  let ordered = false;
  let delim = null;
  let marker = null;
  let num = 0;
  const c0 = s.charCodeAt(0);
  if (c0 === 45 || c0 === 43 || c0 === 42) {
    marker = s[0];
    i = 1;
  } else if (isAsciiDigit(c0)) {
    let j = 0;
    while (j < s.length && isAsciiDigit(s.charCodeAt(j))) j++;
    if (j > 9) return null;
    if (j < s.length && (s.charCodeAt(j) === 46 || s.charCodeAt(j) === 41)) {
      num = parseInt(s.slice(0, j), 10);
      delim = s[j];
      ordered = true;
      i = j + 1;
    } else {
      return null;
    }
  } else {
    return null;
  }
  // Measure the whitespace after the marker in virtual columns.
  const d = copyCursor(c);
  skipIndent(d, 3);
  for (let k = 0; k < i; k++) {
    d.i++;
    d.col++;
  }
  const w0 = copyCursor(d);
  const ws = skipIndent(w0, 1000000);
  const atEnd = w0.i >= w0.s.length && w0.tab === 0;
  if (ws === 0 && !atEnd) return null;
  // An ordered list may only interrupt a paragraph when it starts at 1,
  // unless the paragraph sits directly in a list item (any number works).
  if (paraOpen && ordered && num !== 1 && !paraInItem) return null;
  const markerCols = d.col - c.col;
  if (atEnd) {
    return { ordered, delim, marker, num, contentIndent: markerCols + 1, contentCursor: w0 };
  }
  if (ws <= 4) {
    return { ordered, delim, marker, num, contentIndent: w0.col - c.col, contentCursor: w0 };
  }
  const cc = copyCursor(d);
  skipIndent(cc, 1);
  return { ordered, delim, marker, num, contentIndent: markerCols + 1, contentCursor: cc };
}

function matchHtmlBlock(c) {
  const r = indentAndContent(c, 3);
  if (r === null) return null;
  const s = r.text;
  if (s.length === 0 || s.charCodeAt(0) !== 60) return null;
  if (s.startsWith('<!--')) return { htype: 2, endTag: null };
  if (s.startsWith('<?')) return { htype: 3, endTag: null };
  if (s.startsWith('<![CDATA[')) return { htype: 5, endTag: null };
  if (s.startsWith('<!') && s.length > 2 && isAsciiLetter(s.charCodeAt(2))) {
    return { htype: 4, endTag: null };
  }
  const m1 = /^<(pre|script|style|textarea)(?=[ \t>]|$)/i.exec(s);
  if (m1) return { htype: 1, endTag: m1[1].toLowerCase() };
  const m6 = /^<\/?([A-Za-z][A-Za-z0-9-]*)/.exec(s);
  if (m6) {
    const name = m6[1].toLowerCase();
    const after = s[m6[0].length];
    if (BLOCK_TAGS.has(name) &&
        (after === undefined || after === ' ' || after === '\t' || after === '>' || after === '/')) {
      return { htype: 6, endTag: null };
    }
  }
  const tagLen = scanHtmlTag(s, 0);
  if (tagLen > 0) {
    let k = tagLen;
    while (k < s.length && isSpaceTab(s.charCodeAt(k))) k++;
    if (k === s.length) return { htype: 7, endTag: null };
  }
  return null;
}

// Whether a line of an HTML block of types 1-5 contains the block's end.
function htmlBlockEnds(htype, endTag, lineText) {
  if (htype === 1) {
    const low = lineText.toLowerCase();
    const needle = '</' + endTag;
    let idx = low.indexOf(needle);
    while (idx !== -1) {
      const after = low[idx + needle.length];
      if (after === undefined || after === ' ' || after === '\t' || after === '>') return true;
      idx = low.indexOf(needle, idx + 1);
    }
    return false;
  }
  if (htype === 2) return lineText.indexOf('-->') !== -1;
  if (htype === 3) return lineText.indexOf('?>') !== -1;
  if (htype === 4) return lineText.indexOf('>') !== -1;
  if (htype === 5) return lineText.indexOf(']]>') !== -1;
  return false;
}

// ---------- table helpers ----------

// Split a table row on unescaped pipes, converting \| to a literal pipe.
function splitTableRow(line) {
  const cells = [];
  let cur = '';
  for (let i = 0; i < line.length; i++) {
    const ch = line.charCodeAt(i);
    if (ch === 92 && i + 1 < line.length && line.charCodeAt(i + 1) === 124) {
      cur += '|';
      i++;
    } else if (ch === 124) {
      cells.push(cur);
      cur = '';
    } else {
      cur += line[i];
    }
  }
  cells.push(cur);
  return cells;
}

// Drop the empty first/last cells produced by leading/trailing pipes.
function trimCellEdges(cells, line) {
  const t = line.trim();
  let start = 0;
  let end = cells.length;
  if (t.length > 0 && t.charCodeAt(0) === 124 && end > 0 && cells[0].trim() === '') start = 1;
  if (t.length > 0 && t.charCodeAt(t.length - 1) === 124 && end > start && cells[end - 1].trim() === '') end--;
  return cells.slice(start, end);
}

// Parse a delimiter row into alignments, or null when it is not one.
function parseDelimiterRow(line) {
  const cells = trimCellEdges(splitTableRow(line), line);
  if (cells.length === 0) return null;
  const aligns = [];
  for (const cell of cells) {
    const t = cell.trim();
    if (!/^:?-+:?$/.test(t)) return null;
    const left = t.charCodeAt(0) === 58;
    const right = t.charCodeAt(t.length - 1) === 58;
    aligns.push(left && right ? 'center' : left ? 'left' : right ? 'right' : null);
  }
  return aligns;
}

function splitRowCells(line, ncols) {
  const cells = trimCellEdges(splitTableRow(line), line);
  const out = [];
  for (let k = 0; k < ncols; k++) {
    out.push(k < cells.length ? cells[k].trim() : '');
  }
  return out;
}

// ---------- block parser ----------

// The rest of the line with leading tabs expanded to spaces (to the next tab
// stop from the cursor's column). Used for content lines inside containers,
// where a leading tab is expanded rather than kept.
function expandLeadingTabs(c) {
  let out = '';
  let col = c.col;
  let i = c.i;
  if (c.tab > 0) {
    out = ' '.repeat(c.tab);
    col += c.tab;
  }
  const s = c.s;
  while (i < s.length) {
    const ch = s.charCodeAt(i);
    if (ch === SPACE) {
      out += ' ';
      col++;
      i++;
    } else if (ch === TAB) {
      const w = 4 - (col % 4);
      out += ' '.repeat(w);
      col += w;
      i++;
    } else {
      break;
    }
  }
  return out + s.slice(i);
}

// Skip up to three columns of spaces/tabs at text[i] (for definition starts).
function leadingSkip(text, i) {
  let col = 0;
  while (i < text.length && col < 3) {
    const ch = text.charCodeAt(i);
    if (ch === SPACE) {
      i++;
      col++;
    } else if (ch === TAB) {
      const w = 4 - (col % 4);
      if (col + w > 3) break;
      i++;
      col += w;
    } else {
      break;
    }
  }
  return i;
}

function parseBlocks(lines, endsWithNewline) {
  const defs = new Map();
  const doc = { t: 'doc', children: [], parent: null };
  const stack = [doc];
  const nLines = lines.length;
  let prevLazy = false;

  function tip() {
    return stack[stack.length - 1];
  }

  // Number of open containers (quotes, lists, items) on the stack.
  function containerDepth() {
    let d = 0;
    for (let k = 1; k < stack.length; k++) {
      const t = stack[k].t;
      if (t === 'quote' || t === 'list' || t === 'item') d++;
    }
    return d;
  }

  function extractContent(c) {
    return containerDepth() > 0 ? expandLeadingTabs(c) : restOfLine(c);
  }

  function addBlock(b) {
    const parent = tip();
    if (parent.t === 'item' && parent.blankPending) {
      if (parent.children.length > 0) parent.blankBetween = true;
      parent.blankPending = false;
    }
    // Content added inside a descendant consumes a pending blank for every
    // enclosing item: the blank separated blocks below, not blocks here.
    let anc = parent.parent;
    while (anc !== null) {
      if (anc.t === 'item') anc.blankPending = false;
      anc = anc.parent;
    }
    b.parent = parent;
    parent.children.push(b);
    return b;
  }

  function openBlock(b) {
    addBlock(b);
    stack.push(b);
    return b;
  }

  // Extract leading link reference definitions from paragraph text, recording
  // them in the global map (first definition per label wins). Returns the
  // remaining paragraph text.
  function extractDefs(text) {
    let textStart = 0;
    let pos = leadingSkip(text, 0);
    while (true) {
      if (pos >= text.length || text.charCodeAt(pos) !== 91) break;
      const def = parseRefDef(text, pos);
      if (def === null) break;
      const label = normaliseLabel(def.label);
      if (!defs.has(label)) defs.set(label, { dest: def.dest, title: def.title });
      let next = def.next;
      if (next < text.length && text.charCodeAt(next) === LF) next++;
      textStart = next;
      pos = leadingSkip(text, next);
    }
    return text.slice(textStart);
  }

  function finalizePara(b) {
    const remainder = extractDefs(b.lines.join('\n'));
    if (remainder.trim() === '') {
      const parent = b.parent;
      const at = parent.children.indexOf(b);
      if (at !== -1) parent.children.splice(at, 1);
      b.removed = true;
    } else {
      b.text = remainder;
      delete b.lines;
    }
  }

  function finalizeCode(b) {
    let ls = b.lines;
    if (!b.fenced) {
      let end = ls.length;
      while (end > 0 && /^[ \t]*$/.test(ls[end - 1])) end--;
      ls = ls.slice(0, end);
    } else if (ls.length > 0 && ls[ls.length - 1] === '') {
      // Fenced code drops exactly one trailing empty line.
      ls = ls.slice(0, -1);
    }
    b.content = ls.length === 0 ? '' : ls.join('\n') + '\n';
    delete b.lines;
    let lang = '';
    if (b.fenced && b.info) {
      const t = b.info.trim();
      if (t !== '') lang = resolveEscapes(t.split(/[ \t]+/)[0]);
    }
    b.lang = lang;
  }

  function finalizeHtml(b) {
    let text = b.lines.join('\n');
    const followedByBlank = b.endedByBlank || b.followedByBlank;
    if (!followedByBlank && (b.lastLineIndex < nLines - 1 || endsWithNewline)) {
      text += '\n';
    }
    b.text = text;
    delete b.lines;
  }

  function finalizeItem(b) {
    // Task list marker on the first paragraph: [x], [X] or [ ] followed by
    // whitespace and content on the same line.
    const first = b.children[0];
    if (first && first.t === 'para') {
      const text = first.text;
      if (text.length >= 4 && text.charCodeAt(0) === 91 && text.charCodeAt(2) === 93) {
        const m = text.charCodeAt(1);
        if (m === 120 || m === 88 || m === SPACE) {
          let k = 3;
          while (k < text.length && isSpaceTab(text.charCodeAt(k))) k++;
          if (k < text.length && text.charCodeAt(k) !== LF) {
            b.task = m === SPACE ? 'unchecked' : 'checked';
            first.text = text.slice(k);
          }
        }
      }
    }
  }

  function finalizeList(b) {
    b.tight = !b.loose;
    if (b.tight) {
      for (const it of b.children) {
        if (it.blankBetween) {
          b.tight = false;
          break;
        }
      }
    }
  }

  function finalize(b) {
    if (b.t === 'para') finalizePara(b);
    else if (b.t === 'code') finalizeCode(b);
    else if (b.t === 'html') finalizeHtml(b);
    else if (b.t === 'item') finalizeItem(b);
    else if (b.t === 'list') finalizeList(b);
  }

  // Whether the source line after index idx strips the HTML block's
  // trailing newline: the line leaves the block's containers, or its
  // content after the container markers is empty. A whitespace-only
  // line does NOT strip it (marked keeps the newline there).
  function peekBlankAfter(idx) {
    const ni = idx + 1;
    if (ni >= nLines) return false;
    const res = matchContainers(lines[ni], stack);
    if (res.failedAt !== -1) return true;
    return restOfLine(res.cursor).length === 0;
  }

  function closeTo(k) {
    while (stack.length > k) {
      const b = stack.pop();
      if (b.t === 'html' && !b.endedByBlank) {
        b.followedByBlank = peekBlankAfter(b.lastLineIndex);
      }
      finalize(b);
    }
  }

  function matchContainers(line, stk) {
    let cur = makeCursor(line);
    let failedAt = -1;
    for (let k = 1; k < stk.length; k++) {
      const b = stk[k];
      if (b.t === 'list') continue;
      if (b.t === 'quote') {
        const q = matchQuoteStart(cur);
        if (q === null) {
          failedAt = k;
          break;
        }
        cur = q;
        continue;
      }
      if (b.t === 'item') {
        if (isBlankRest(cur)) continue;
        // An empty item that saw a blank line is closed: indented lines
        // after the blank belong outside the list.
        if (b.children.length === 0 && b.sawBlank) {
          failedAt = k;
          break;
        }
        const d = copyCursor(cur);
        if (skipIndent(d, b.contentIndent) < b.contentIndent) {
          failedAt = k;
          break;
        }
        cur = d;
        continue;
      }
      break;
    }
    return { cursor: cur, failedAt };
  }

  // Whether a line (after the matched container prefix) is paragraph
  // continuation text rather than the start of an interrupting block.
  function isLazyText(cur) {
    if (matchATX(cur) !== null) return false;
    if (matchFence(cur) !== null) return false;
    if (matchHR(cur)) return false;
    const hb = matchHtmlBlock(cur);
    if (hb !== null && hb.htype <= 6) return false;
    // Any list marker disqualifies laziness: a marker for the enclosing list
    // starts a new item even when it could not interrupt a paragraph.
    if (matchListMarker(cur, false) !== null) return false;
    // A blockquote start disqualifies laziness: the quote opens in the
    // enclosing container instead of continuing the paragraph.
    const qc = indentAndContent(cur, 3);
    if (qc !== null && qc.text.charCodeAt(0) === 62) return false;
    return true;
  }

  // Lazy continuation content: strip up to four columns of leading whitespace
  // when the leading whitespace run spans at least four columns.
  function lazyContent(cur) {
    // When containers matched (cursor past column 0), leading tabs expand
    // from the cursor's column, as in normal content extraction. At
    // document level the raw line is kept (tabs preserved).
    if (cur.col > 0) {
      const expanded = expandLeadingTabs(copyCursor(cur));
      let lead = 0;
      while (lead < expanded.length && expanded.charCodeAt(lead) === SPACE) lead++;
      return lead >= 4 ? expanded.slice(4) : expanded;
    }
    const d = copyCursor(cur);
    const avail = skipIndent(d, 1000000);
    if (avail >= 4) {
      const e = copyCursor(cur);
      skipIndent(e, 4);
      return restOfLine(e);
    }
    return restOfLine(cur);
  }

  // Marked quirk: a lazy line shaped like a setext underline, inside a
  // blockquote, immediately after another lazy line, is indented to four
  // spaces (or kept verbatim when indented further / tab-led). Returns the
  // special content, or null when the ordinary lazy rule applies.
  function lazySetextContent(cur, failedAt, wasLazy) {
    if (!wasLazy) return null;
    const failed = stack[failedAt];
    if (!failed || failed.t !== 'quote') return null;
    const raw = restOfLine(cur);
    let p = 0;
    let hasTab = false;
    while (p < raw.length) {
      const cc = raw.charCodeAt(p);
      if (cc === 32) { p++; continue; }
      if (cc === 9) { hasTab = true; p++; continue; }
      break;
    }
    const ch = raw.charCodeAt(p);
    if (ch !== 61 && ch !== 45) return null;
    let k = p;
    while (k < raw.length && raw.charCodeAt(k) === ch) k++;
    if (ch === 45 && k - p > 2) return null;
    for (let m = k; m < raw.length; m++) {
      const cc = raw.charCodeAt(m);
      if (cc !== 32 && cc !== 9) return null;
    }
    if (!hasTab && p <= 4) return '    ' + raw.slice(p);
    return raw;
  }

  function listMatches(list, lm) {
    if (list.ordered !== lm.ordered) return false;
    if (lm.ordered) return list.delim === lm.delim;
    return list.marker === lm.marker;
  }

  function startOrContinueList(lm) {
    const t = tip();
    if (t.t === 'list' && listMatches(t, lm)) {
      const prev = t.children[t.children.length - 1];
      if (prev && prev.blankPending) {
        t.loose = true;
      }
      openBlock({ t: 'item', children: [], contentIndent: lm.contentIndent, blankPending: false, blankBetween: false, sawBlank: false });
      return;
    }
    if (t.t === 'list') closeTo(stack.length - 1);
    openBlock({ t: 'list', ordered: lm.ordered, delim: lm.delim, marker: lm.marker, start: lm.num, children: [], loose: false });
    openBlock({ t: 'item', children: [], contentIndent: lm.contentIndent, blankPending: false, blankBetween: false, sawBlank: false });
  }

  function handleBlank() {
    const t = tip();
    if (t.t === 'para' || t.t === 'table') {
      closeTo(stack.length - 1);
    } else if (t.t === 'html' && t.htype >= 6) {
      t.endedByBlank = true;
      closeTo(stack.length - 1);
    }
    for (let k = stack.length - 1; k >= 1; k--) {
      const st = stack[k].t;
      // A blank inside a blockquote is quote-internal: it does not loosen
      // an enclosing list. Otherwise it marks every enclosing item.
      if (st === 'quote') break;
      if (st === 'item') {
        stack[k].blankPending = true;
        stack[k].sawBlank = true;
      }
    }
  }

  function tryTableStart(cur, idx) {
    if (indentAndContent(cur, 3) === null) return null;
    if (idx + 1 >= nLines) return null;
    // A delimiter row needs dashes; without one on the next line there is
    // no table, so the container matching and cell parsing are skipped.
    if (lines[idx + 1].indexOf('-') === -1) return null;
    const peek = matchContainers(lines[idx + 1], stack);
    if (peek.failedAt !== -1) return null;
    const delimLine = restOfLine(peek.cursor);
    if (delimLine.indexOf('-') === -1) return null;
    const aligns = parseDelimiterRow(delimLine);
    if (aligns === null) return null;
    const headerLine = restOfLine(cur);
    const headerHasPipe = splitTableRow(headerLine).length > 1;
    const delimHasPipe = splitTableRow(delimLine).length > 1;
    const delimHasColon = aligns.some((a) => a !== null);
    if (!headerHasPipe && !delimHasPipe && aligns.length === 1 && !delimHasColon) return null;
    // The header and delimiter rows must have the same number of cells.
    if (trimCellEdges(splitTableRow(headerLine), headerLine).length !== aligns.length) return null;
    const header = splitRowCells(headerLine, aligns.length);
    return { t: 'table', aligns, header, rows: [], ncols: aligns.length, delimLine: idx + 1 };
  }

  function isTableRowLine(cur) {
    if (indentAndContent(cur, 3) === null) return false;
    if (matchATX(cur) !== null) return false;
    if (matchFence(cur) !== null) return false;
    if (matchHR(cur)) return false;
    if (matchQuoteStart(cur) !== null) return false;
    if (matchListMarker(cur, false) !== null) return false;
    if (matchHtmlBlock(cur) !== null) return false;
    return true;
  }

  function processLine(idx) {
    const line = lines[idx];
    const res = matchContainers(line, stack);
    let cur = res.cursor;
    const wasLazy = prevLazy;
    prevLazy = false;
    if (res.failedAt !== -1) {
      const t = tip();
      // Fence capture: a line that leaves its containers is still fence
      // content when the fence sits directly in a list item and already
      // holds a non-blank content line. A closing-fence-shaped line is
      // not captured: the containers close and it is re-processed.
      if (t.t === 'code' && t.fenced && t.parent !== null && t.parent.t === 'item' && t.sawContent) {
        const raw = makeCursor(line);
        // A line that opens a blockquote at the level the containers
        // reached is not fence content: the fence ends and the quote
        // opens in the enclosing item.
        const qc = indentAndContent(res.cursor, 3);
        const quoteStart = qc !== null && qc.text.charCodeAt(0) === 62;
        if (!quoteStart && !isClosingFence(raw, t.fenceChar, t.fenceLen)) {
          let text = extractContent(raw);
          if (t.fenceChar === 96) text = stripLeadWs(text, t.fenceStrip);
          t.lines.push(text);
          t.lastLineIndex = idx;
          return;
        }
      }
      if (t.t === 'para' && !isBlankRest(cur) && isLazyText(cur)) {
        const special = lazySetextContent(cur, res.failedAt, wasLazy);
        prevLazy = true;
        t.lines.push(special !== null ? special : lazyContent(cur));
        return;
      }
      closeTo(res.failedAt);
      cur = res.cursor;
    }

    let t = tip();

    // Fenced code: every line is content until the closing fence.
    if (t.t === 'code' && t.fenced) {
      if (isClosingFence(cur, t.fenceChar, t.fenceLen)) {
        closeTo(stack.length - 1);
        return;
      }
      let text = extractContent(cur);
      if (t.fenceChar === 96) text = stripLeadWs(text, t.fenceStrip);
      t.lines.push(text);
      if (!isBlankRest(cur)) t.sawContent = true;
      t.lastLineIndex = idx;
      return;
    }

    // HTML blocks of types 1-5 swallow blank lines as content.
    if (t.t === 'html' && t.htype <= 5) {
      const text = extractContent(cur);
      t.lines.push(text);
      t.lastLineIndex = idx;
      if (htmlBlockEnds(t.htype, t.endTag, text)) {
        closeTo(stack.length - 1);
      }
      return;
    }

    // Indented code: blank lines are content; other lines need 4 columns.
    if (t.t === 'code' && !t.fenced) {
      if (isBlankRest(cur)) {
        // A blank line contributes what remains after the 4-column strip.
        const d = copyCursor(cur);
        skipIndent(d, 4);
        t.lines.push(extractContent(d));
        t.lastLineIndex = idx;
        return;
      }
      const d = copyCursor(cur);
      if (skipIndent(d, 4) === 4) {
        t.lines.push(extractContent(d));
        t.lastLineIndex = idx;
        return;
      }
      closeTo(stack.length - 1);
      t = tip();
    }

    // Blank line: ends paragraphs, tables and type 6/7 HTML blocks.
    if (isBlankRest(cur)) {
      // Quirk: a whitespace-only final line with content left after the
      // container markers joins an open paragraph when inside a blockquote,
      // or at document level when the input has no trailing newline.
      if (idx === nLines - 1 && t.t === 'para' && restOfLine(cur).length > 0) {
        let deepest = null;
        for (let k = stack.length - 1; k >= 1; k--) {
          const st = stack[k].t;
          if (st === 'quote' || st === 'list' || st === 'item') { deepest = st; break; }
        }
        if (deepest === 'quote' || (deepest === null && !endsWithNewline)) {
          t.lines.push(extractContent(cur));
          return;
        }
      }
      // A blank line that still holds a tab is an empty table row, not
      // the end of the table (a spaces-only line does end it).
      if (t.t === 'table' && restOfLine(cur).indexOf('\t') !== -1) {
        t.rows.push(splitRowCells(extractContent(cur), t.ncols));
        return;
      }
      handleBlank();
      return;
    }

    // HTML blocks of types 6/7: every non-blank line is content.
    if (t.t === 'html') {
      const text = extractContent(cur);
      t.lines.push(text);
      t.lastLineIndex = idx;
      return;
    }

    // Table: row lines continue it, anything else ends it. The delimiter
    // line itself is consumed, never a row.
    if (t.t === 'table') {
      if (idx === t.delimLine) return;
      if (isTableRowLine(cur)) {
        t.rows.push(splitRowCells(extractContent(cur), t.ncols));
        return;
      }
      closeTo(stack.length - 1);
      t = tip();
    }

    // Close lists that this line does not continue with a new item.
    while (tip().t === 'list') {
      const lm = matchListMarker(cur, false);
      if (lm !== null && listMatches(tip(), lm)) break;
      closeTo(stack.length - 1);
    }

    // Start new containers (blockquotes, list items) as deep as the line goes.
    // A thematic break on the whole line wins over a list marker.
    while (true) {
      if (matchHR(cur)) break;
      const t2 = tip();
      const paraOpen = t2.t === 'para';
      const q = matchQuoteStart(cur);
      if (q !== null) {
        if (paraOpen) closeTo(stack.length - 1);
        openBlock({ t: 'quote', children: [] });
        cur = q;
        continue;
      }
      const lm = matchListMarker(cur, paraOpen, paraOpen && t2.parent !== null && t2.parent.t === 'item');
      if (lm !== null) {
        // An empty item cannot interrupt a paragraph: the line stays text
        // (or becomes a setext underline). Inside a list item, an empty
        // ORDERED item does interrupt; an empty bullet still does not.
        const paraInItem = paraOpen && t2.parent !== null && t2.parent.t === 'item';
        if (paraOpen && isBlankRest(lm.contentCursor) && (!paraInItem || !lm.ordered)) break;
        if (paraOpen) closeTo(stack.length - 1);
        startOrContinueList(lm);
        cur = lm.contentCursor;
        continue;
      }
      break;
    }

    // A line that only opened containers contributes no leaf content.
    if (isBlankRest(cur)) return;

    const t3 = tip();
    const paraOpen = t3.t === 'para';

    // Setext underline: definitions are extracted from the paragraph first;
    // a paragraph that turns out to be only definitions is no heading.
    if (paraOpen) {
      const level = matchSetext(cur);
      if (level !== 0) {
        const para = t3;
        const remainder = extractDefs(para.lines.join('\n'));
        stack.pop();
        const parent = para.parent;
        const at = parent.children.indexOf(para);
        if (remainder.trim() === '') {
          if (at !== -1) parent.children.splice(at, 1);
        } else {
          // Setext heading text is stripped of leading/trailing spaces/tabs.
          const headText = remainder.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
          const heading = { t: 'head', level, text: headText, parent };
          if (at !== -1) parent.children[at] = heading;
          return;
        }
        // Fall through: the underline line becomes ordinary content.
      }
    }

    // ATX heading.
    const atx = matchATX(cur);
    if (atx !== null) {
      if (tip().t === 'para') closeTo(stack.length - 1);
      addBlock({ t: 'head', level: atx.level, text: atx.text });
      return;
    }

    // Fenced code.
    const fen = matchFence(cur);
    if (fen !== null) {
      if (tip().t === 'para') closeTo(stack.length - 1);
      openBlock({ t: 'code', fenced: true, fenceChar: fen.fenceChar, fenceLen: fen.fenceLen, fenceStrip: fen.strip, info: fen.info, lines: [], lastLineIndex: idx, sawContent: false });
      return;
    }

    // HTML block (type 7 cannot interrupt a paragraph).
    const hb = matchHtmlBlock(cur);
    if (hb !== null && (tip().t !== 'para' || hb.htype <= 6)) {
      if (tip().t === 'para') closeTo(stack.length - 1);
      const text = extractContent(cur);
      const html = { t: 'html', htype: hb.htype, endTag: hb.endTag, lines: [text], lastLineIndex: idx, endedByBlank: false };
      openBlock(html);
      if (hb.htype <= 5 && htmlBlockEnds(hb.htype, hb.endTag, text)) {
        closeTo(stack.length - 1);
      }
      return;
    }

    // Thematic break.
    if (matchHR(cur)) {
      if (tip().t === 'para') closeTo(stack.length - 1);
      while (tip().t === 'list') closeTo(stack.length - 1);
      addBlock({ t: 'hr' });
      return;
    }

    // Table.
    const tbl = tryTableStart(cur, idx);
    if (tbl !== null) {
      if (tip().t === 'para') closeTo(stack.length - 1);
      openBlock(tbl);
      return;
    }

    // Indented code (cannot interrupt a paragraph).
    if (tip().t !== 'para') {
      const d = copyCursor(cur);
      if (skipIndent(d, 4) === 4) {
        openBlock({ t: 'code', fenced: false, info: '', lines: [extractContent(d)], lastLineIndex: idx });
        return;
      }
    }

    // Paragraph: append to the open one, or open a new one.
    if (tip().t === 'para') {
      tip().lines.push(extractContent(cur));
    } else {
      openBlock({ t: 'para', lines: [extractContent(cur)] });
    }
  }

  for (let idx = 0; idx < nLines; idx++) {
    processLine(idx);
  }
  closeTo(1);
  return { doc, defs };
}

// ---------- inline parser: autolinks ----------

// Match an email address starting at s[start] (local@domain, at least two
// domain labels). Returns {end} or null. The caller checks the lookahead.
function matchEmailAt(s, start, end) {
  let i = start;
  const l0 = i;
  while (i < end) {
    const ch = s.charCodeAt(i);
    if (isAsciiLetter(ch) || isAsciiDigit(ch) || ch === 46 || ch === 95 || ch === 43 || ch === 45) i++;
    else break;
  }
  if (i === l0) return null;
  if (i >= end || s.charCodeAt(i) !== 64) return null;
  i++;
  // First domain label: [A-Za-z0-9-_]+ (may end in '-' or '_').
  const lab0 = i;
  while (i < end) {
    const ch = s.charCodeAt(i);
    if (isAsciiLetter(ch) || isAsciiDigit(ch) || ch === 45 || ch === 95) i++;
    else break;
  }
  if (i === lab0) return null;
  // One or more dot-groups: '.' + [A-Za-z0-9-_]* + [A-Za-z0-9]. Each group
  // must end with an alphanumeric, so trailing '-'/'_' stay unconsumed.
  let groups = 0;
  while (i < end && s.charCodeAt(i) === 46) {
    let j = i + 1;
    let lastAlnum = -1;
    while (j < end) {
      const ch = s.charCodeAt(j);
      if (isAsciiLetter(ch) || isAsciiDigit(ch)) {
        lastAlnum = j;
        j++;
      } else if (ch === 45 || ch === 95) {
        j++;
      } else {
        break;
      }
    }
    if (lastAlnum === -1) break;
    i = lastAlnum + 1;
    groups++;
  }
  if (groups < 1) return null;
  return { end: i };
}

// Length of a scheme prefix (http://, https://, ftp://, case-insensitive)
// starting at text[i], or 0.
function matchScheme(text, i) {
  const c0 = text.charCodeAt(i) | 32;
  if (c0 === 104) {
    if ((text.charCodeAt(i + 1) | 32) === 116 &&
        (text.charCodeAt(i + 2) | 32) === 116 &&
        (text.charCodeAt(i + 3) | 32) === 112) {
      if (text.charCodeAt(i + 4) === 58 &&
          text.charCodeAt(i + 5) === 47 &&
          text.charCodeAt(i + 6) === 47) return 7;
      if ((text.charCodeAt(i + 4) | 32) === 115 &&
          text.charCodeAt(i + 5) === 58 &&
          text.charCodeAt(i + 6) === 47 &&
          text.charCodeAt(i + 7) === 47) return 8;
    }
  } else if (c0 === 102) {
    if ((text.charCodeAt(i + 1) | 32) === 116 &&
        (text.charCodeAt(i + 2) | 32) === 112 &&
        text.charCodeAt(i + 3) === 58 &&
        text.charCodeAt(i + 4) === 47 &&
        text.charCodeAt(i + 5) === 47) return 6;
  }
  return 0;
}

const BACKPEDAL_PUNCT = new Set([33, 63, 46, 44, 58, 59, 42, 95, 126, 34, 39, 41]);

// One backpedal pass: the longest valid URL prefix. Ordinary characters
// pass through; a '(' must open a group closed by ')' with no ')' inside;
// '&' is dropped when it starts a trailing named-entity tail; a run of
// punctuation is kept only when more content follows it.
function backpedalOnce(u) {
  let i = 0;
  const n = u.length;
  while (i < n) {
    const c = u.charCodeAt(i);
    if (c === 40) {
      let j = i + 1;
      while (j < n && u.charCodeAt(j) !== 41) j++;
      if (j < n) {
        i = j + 1;
        continue;
      }
      break;
    }
    if (c === 38) {
      if (isEntityTail(u, i)) break;
      i++;
      continue;
    }
    if (BACKPEDAL_PUNCT.has(c)) {
      let j = i;
      while (j < n && BACKPEDAL_PUNCT.has(u.charCodeAt(j))) j++;
      if (j < n) {
        i = j;
        continue;
      }
      break;
    }
    i++;
  }
  return u.slice(0, i);
}

// '&' at i starts a trailing named-entity tail: &[A-Za-z0-9]+; at the end.
function isEntityTail(u, i) {
  let j = i + 1;
  const n = u.length;
  const d0 = j;
  while (j < n) {
    const c = u.charCodeAt(j);
    if (isAsciiLetter(c) || isAsciiDigit(c)) j++;
    else break;
  }
  return j > d0 && j + 1 === n && u.charCodeAt(j) === 59;
}

// Trim a scanned bare URL by re-applying the backpedal until stable.
function trimAutolinkUrl(raw) {
  let u = raw;
  while (true) {
    const v = backpedalOnce(u);
    if (v === u) return u;
    u = v;
  }
}

// Whether a trimmed www. candidate matches marked's url pattern: after
// "www." there must be at least one label character [A-Za-z0-9-]; the
// rest of the run is an unrestricted tail (backslashes included).
function isValidWww(u) {
  if (!u.startsWith('www.') || u.length < 5) return false;
  const ch = u.charCodeAt(4);
  return (ch >= 48 && ch <= 57) || (ch >= 65 && ch <= 90) || (ch >= 97 && ch <= 122) || ch === 45;
}

function isWwwPreceding(code) {
  return code === SPACE || code === TAB || code === LF || code === 13 ||
    code === 12 || code === 11 || code === 40 || code === 42 ||
    code === 95 || code === 126;
}

// Scan a run of URL characters ([^\s<]+) starting at i. Returns the end index.
function scanUrlRun(text, i) {
  const n = text.length;
  let j = i;
  while (j < n) {
    const ch = text.charCodeAt(j);
    if (ch === 60 || ch === SPACE || ch === TAB || ch === LF || ch === 13 || ch === 12 || ch === 11) break;
    j++;
  }
  return j;
}

function makeAutoLink(linkText, dest, ext) {
  return { t: 'link', dest, title: null, rawText: linkText, image: false, auto: true, ext: !!ext };
}

// The character after an extended email must not be a word character or
// '-'. Exception: a following '_' run is skipped when it will close an
// earlier '_' opener, because the email then sits inside emphasis and
// marked parses it within the emphasis content, where the closer is gone.
function emailLookaheadOk(text, end, items) {
  const n = text.length;
  if (end >= n) return true;
  const c = text.charCodeAt(end);
  if (!isWordChar(c) && c !== 45) return true;
  if (c !== 95) return false;
  let j = end;
  while (j < n && text.charCodeAt(j) === 95) j++;
  if (j < n && (isWordChar(text.charCodeAt(j)) || text.charCodeAt(j) === 45)) return false;
  for (let k = items.length - 1; k >= 0; k--) {
    const it = items[k];
    if (it.t === 'delim' && it.ch === 95 && it.open) return true;
  }
  return false;
}

// Try the GFM extended autolinks at position i: mailto:, schemes, www., email.
// c is the char code at i; each branch is dispatched on it so positions that
// cannot start a given form skip its check entirely.
function tryExtendedAutolink(text, i, openers, items, c) {
  const n = text.length;
  if (c === 109 && text.startsWith('mailto:', i)) {
    const em = matchEmailAt(text, i + 7, n);
    if (em !== null &&
        (i === 0 || !isWordChar(text.charCodeAt(i - 1))) &&
        emailLookaheadOk(text, em.end, items)) {
      const url = text.slice(i, em.end);
      return { node: makeAutoLink(url, url, true), next: em.end };
    }
  }
  if (c === 120 && text.startsWith('xmpp:', i)) {
    const em = matchEmailAt(text, i + 5, n);
    if (em !== null &&
        (i === 0 || !isWordChar(text.charCodeAt(i - 1))) &&
        emailLookaheadOk(text, em.end, items)) {
      // Optional one-segment path: '/' + [A-Za-z0-9@.]+, minus trailing dots.
      let end = em.end;
      if (end < n && text.charCodeAt(end) === 47) {
        let j = end + 1;
        while (j < n) {
          const ch = text.charCodeAt(j);
          if (isAsciiLetter(ch) || isAsciiDigit(ch) || ch === 64 || ch === 46) j++;
          else break;
        }
        while (j > end + 1 && text.charCodeAt(j - 1) === 46) j--;
        if (j > end + 1) end = j;
      }
      const url = text.slice(i, end);
      return { node: makeAutoLink(url, url, true), next: end };
    }
  }
  if (c === 104 || c === 72 || c === 102 || c === 70) {
    const schemeLen = matchScheme(text, i);
    if (schemeLen > 0) {
      let j = scanUrlRun(text, i);
      j = capUrlRunAtBracket(text, i, j, openers);
      if (j - i > schemeLen) {
        const trimmed = trimAutolinkUrl(text.slice(i, j));
        if (trimmed.length > schemeLen) {
          return { node: makeAutoLink(trimmed, trimmed, true), next: i + trimmed.length };
        }
      }
    }
  }
  if (c === 119 && text.startsWith('www.', i)) {
    if (i === 0 || isWwwPreceding(text.charCodeAt(i - 1))) {
      let j = scanUrlRun(text, i);
      j = capUrlRunAtBracket(text, i, j, openers);
      const trimmed = trimAutolinkUrl(text.slice(i, j));
      if (isValidWww(trimmed)) {
        return { node: makeAutoLink(trimmed, 'http://' + trimmed, true), next: i + trimmed.length };
      }
    }
  }
  // Email: only at the start of a local-part run. A mid-run start can only
  // match when the run-start attempt already matched (and consumed the run)
  // or when the run starts with '_' (consumed by the delimiter branch, so
  // the check below still runs there).
  if (i === 0 || !isEmailRunChar(text.charCodeAt(i - 1))) {
    const em = matchEmailAt(text, i, n);
    if (em !== null && emailLookaheadOk(text, em.end, items)) {
      const url = text.slice(i, em.end);
      return { node: makeAutoLink(url, 'mailto:' + url, true), next: em.end };
    }
  }
  return null;
}

// Local-part characters other than '_': [A-Za-z0-9.+-].
function isEmailRunChar(ch) {
  return (ch >= 48 && ch <= 57) || (ch >= 65 && ch <= 90) || (ch >= 97 && ch <= 122) ||
    ch === 46 || ch === 43 || ch === 45;
}

// With a pending link label, a ']' inside a URL run is the label closer:
// stop the run there so the link can still form.
function capUrlRunAtBracket(text, i, j, openers) {
  for (let k = 0; k < openers.length; k++) {
    if (openers[k].active) {
      const br = text.indexOf(']', i);
      if (br !== -1 && br < j) return br;
      return j;
    }
  }
  return j;
}

// Try a <...> autolink (scheme or email) starting at text[i] === '<'.
function tryAutolink(text, i) {
  const gt = text.indexOf('>', i + 1);
  if (gt === -1) return null;
  const content = text.slice(i + 1, gt);
  if (content.length === 0) return null;
  for (let k = 0; k < content.length; k++) {
    const ch = content.charCodeAt(k);
    if (ch === 60 || ch <= 32 || ch === 127) return null;
  }
  const colon = content.indexOf(':');
  if (colon >= 2 && colon <= 32) {
    let ok = isAsciiLetter(content.charCodeAt(0));
    for (let k = 1; ok && k < colon; k++) {
      const ch = content.charCodeAt(k);
      ok = isAsciiLetter(ch) || isAsciiDigit(ch) || ch === 43 || ch === 45 || ch === 46;
    }
    if (ok && colon + 1 < content.length) {
      return { node: makeAutoLink(content, content), next: gt + 1 };
    }
  }
  const em = matchEmailAt(content, 0, content.length);
  if (em !== null && em.end === content.length) {
    return { node: makeAutoLink(content, 'mailto:' + content), next: gt + 1 };
  }
  return null;
}

// ---------- inline parser: emphasis ----------

// Resolve emphasis and strikethrough in an array of inline nodes, in place.
// Implements the delimiter-stack algorithm: `*` and `_` use the standard
// rules (including the rule of three), while `~` matches only equal-length
// runs of one or two and always consumes the whole run.
// ---------- emphasis masking ----------

// Masking pass that hides delimiter runs inside code spans, links,
// and HTML, the way the reference lexer does before it computes the
// last possible closer positions. All replacements preserve length,
// so positions in the masked text line up with the original.
const RE_MASK_CODE = /(`+)(?:[^`]|[^`][\s\S]*?[^`])\1(?!`)|`+|\\([\p{P}\p{S}])/gu;
const RE_MASK_SKIP = /\[(?:[^\[\]`]|(?<a>`+)[^`]+\k<a>(?!`))*?\]\((?:\\[\s\S]|[^\\()]|\((?:\\[\s\S]|[^\\()])*\))*\)|(?<!`)(?<b>`+)[^`]+\k<b>(?!`)|<(?! )[^<>]*?>/g;

function maskInlineText(s, needCode, needSkip) {
  let t = s;
  if (needCode) {
    t = t.replace(RE_MASK_CODE, (m, run, punct) => {
      if (punct !== undefined) return '+'.repeat(m.length);
      if (run !== undefined) return run + m.slice(run.length, -run.length).replace(/`/g, '+') + run;
      return m;
    });
  }
  if (needSkip) t = t.replace(RE_MASK_SKIP, (m) => '[' + 'a'.repeat(m.length - 2) + ']');
  return t;
}

// Last run start of each emphasis delimiter that is not preceded by
// whitespace (a run at the very start counts as preceded). Runs past
// these positions can never close emphasis.
function closerLimits(s) {
  const lim = { star: -1, und: -1 };
  const n = s.length;
  for (let i = 0; i < n; i++) {
    const c = s.charCodeAt(i);
    if (c !== 42 && c !== 95) continue;
    let j = i;
    while (j < n && s.charCodeAt(j) === c) j++;
    const prev = i === 0 ? '\n' : s[i - 1];
    if (prev !== ' ' && prev !== '\t' && prev !== '\n' && prev !== '\r' && prev !== '\f') {
      if (c === 42) lim.star = i;
      else lim.und = i;
    }
    i = j - 1;
  }
  return lim;
}

// ---------- emphasis ----------

const RE_EMPH_SPACE = /\s/u;
const LEAD_WS = /^\s+/;
const RE_EMPH_PUNCT = /[\p{P}\p{S}]/u;
const RE_EMPH_ALNUM = /[\p{L}\p{N}]/u;

// The single code point starting at pos, or '' past the slice end.
function emphCharAt(text, pos, sliceEnd) {
  if (pos >= sliceEnd) return '';
  return String.fromCodePoint(text.codePointAt(pos));
}

// The single code point ending at pos, or '' at the slice start.
function emphCharBefore(text, pos, sliceStart) {
  if (pos <= sliceStart) return '';
  let p = pos - 1;
  const lo = text.charCodeAt(p);
  if (lo >= 0xdc00 && lo <= 0xdfff && p - 1 >= sliceStart) {
    const hi = text.charCodeAt(p - 1);
    if (hi >= 0xd800 && hi <= 0xdbff) p--;
  }
  return text.slice(p, pos);
}

// Character class for flanking: 0 = none, 1 = whitespace,
// 2 = punctuation/symbol, 3 = anything else. For '*' searches a '~'
// counts as a word character (class 3); for '_' searches it counts
// as punctuation (class 2).
function emphClass(ch, tildeWord) {
  if (ch === '') return 0;
  if (tildeWord && ch === '~') return 3;
  if (RE_EMPH_SPACE.test(ch)) return 1;
  if (RE_EMPH_PUNCT.test(ch)) return 2;
  return 3;
}

// Classify a delimiter run as a closer candidate, mirroring the
// closer-match groups: 0 = neither, 1 = closer-only, 2 = opener-only,
// 3 = both open and close. A '_' run between two word characters is
// neither (there is no intraword group for '_').
function classifyCloser(text, run, sliceStart, sliceEnd) {
  const tildeWord = run.ch === 42;
  const pc = emphClass(emphCharBefore(text, run.pos, sliceStart), tildeWord);
  const nc = emphClass(emphCharAt(text, run.pos + run.len, sliceEnd), tildeWord);
  if (pc === 2 && (nc === 1 || nc === 0)) return 1;
  if (pc === 3 && nc !== 3) return 1;
  if ((pc === 2 || pc === 1) && nc === 3) return 2;
  if (pc === 1 && nc === 2) return 2;
  if (pc === 2 && nc === 2) return 3;
  if (run.ch === 42 && pc === 3 && nc === 3) return 3;
  return 0;
}

// At the start of a closer search, a pair of the OTHER delimiter's
// strong markers guards one inner run of this delimiter: that inner
// run is skipped. Returns the position of the closing guard, or the
// search start when the pattern does not match.
function skipGuardedRegion(text, start, sliceEnd, ch) {
  const guard = ch === 42 ? 95 : 42;
  let i = start;
  while (i < sliceEnd) {
    const c = text.charCodeAt(i);
    if (c === 42 || c === 95) break;
    i++;
  }
  if (i + 1 >= sliceEnd || text.charCodeAt(i) !== guard || text.charCodeAt(i + 1) !== guard) return start;
  let j = i + 2;
  while (j < sliceEnd) {
    const c = text.charCodeAt(j);
    if (c === 42 || c === 95) break;
    j++;
  }
  if (j >= sliceEnd || text.charCodeAt(j) !== ch) return start;
  let k = j + 1;
  while (k < sliceEnd) {
    const c = text.charCodeAt(k);
    if (c === 42 || c === 95) break;
    k++;
  }
  if (k + 1 >= sliceEnd || text.charCodeAt(k) !== guard || text.charCodeAt(k + 1) !== guard) return start;
  return k;
}

// Forward emphasis search from the delimiter run at index oi in work.
// Returns null, or {ci, bUsed, isEm}: the closer's index, how many of
// its delimiters the match consumes, and whether it is emphasis
// (rather than strong). Mirrors marked's forward search: opener-only
// runs raise the number of delimiters still needed, both-way runs are
// subject to the rule of three, and the first closer that brings the
// count to zero wins.
function tryEmStrong(work, oi, text, sliceStart, sliceEnd, masked, lim) {
  const opener = work[oi];
  const r = opener.ch;
  const pos = opener.pos;
  const k = opener.len;
  const mpos = pos - sliceStart;
  // The opener pattern runs on the original text; the run back-up,
  // flanking, and closer search run on the masked text.
  const after = emphCharAt(text, pos + k, sliceEnd);
  if (after === '' || RE_EMPH_SPACE.test(after)) return null;
  const d = after !== '~' && RE_EMPH_PUNCT.test(after);
  let l = mpos;
  while (l > 0 && masked.charCodeAt(l - 1) === r) l--;
  const p = l > 0 ? emphCharBefore(masked, l, 0) : '';
  const pc = emphClass(p);
  const h = pc === 1 || pc === 2;
  let n = pos > sliceStart ? emphCharBefore(text, pos, sliceStart) : '';
  const o = n === String.fromCharCode(r);
  if (l < mpos) n = p;
  const nc = emphClass(n);
  const u = l < mpos ? h : (n !== '*' && n !== '_' && (nc === 1 || nc === 2));
  if (r === 95 && !d && n !== '' && RE_EMPH_ALNUM.test(n)) return null;
  if (d && n !== '' && !u) return null;
  const y = mpos - l + k;
  const R = p !== '' && pc !== 1 && (d || (r === 42 && !h));
  let m = k;
  let f = 0;
  const v = r === 42 ? lim.star : lim.und;
  const skipEnd = skipGuardedRegion(masked, mpos + k, masked.length, r);
  for (let ci = oi + 1; ci < work.length; ci++) {
    const cand = work[ci];
    if (cand.t !== 'delim' || cand.ch !== r) continue;
    const cm = cand.pos - sliceStart;
    if (masked.charCodeAt(cm) !== r) continue;
    if (cm > v) break;
    if (cm < skipEnd) continue;
    const b = cand.len;
    const cls = classifyCloser(masked, { pos: cm, len: b, ch: r }, 0, masked.length);
    if (cls === 0) continue;
    if (cls === 2) {
      m += b;
      continue;
    }
    if (cls === 3 || R) {
      if (o && cls === 3) return null;
      if (y % 3 !== 0 && (y + b) % 3 === 0) {
        f += b;
        continue;
      }
    }
    m -= b;
    if (m > 0) continue;
    const bUsed = Math.min(b, b + m + f);
    return { ci, bUsed, isEm: Math.min(k, bUsed) % 2 === 1 };
  }
  return null;
}

// Resolve '*'/'_' emphasis in an item array by forward search. Runs
// left over after the search become literal text. Recurses into
// strikethrough nodes and into emphasis content.
function resolveStar(items, text, sliceStart, sliceEnd) {
  // Fast paths: with no * / _ delimiters and no del nodes there is nothing
  // to resolve, so the masking and limit scans are skipped entirely. With
  // del nodes but no * / _ delimiters, only the del recursion is needed.
  let hasStar = false;
  let hasDel = false;
  for (let k = 0; k < items.length; k++) {
    const it = items[k];
    if (it.t === 'del') hasDel = true;
    else if (it.t === 'delim' && (it.ch === 42 || it.ch === 95)) hasStar = true;
  }
  if (!hasStar && !hasDel) return items;
  if (!hasStar) {
    const work = items.slice();
    for (let k = 0; k < work.length; k++) {
      if (work[k].t === 'del') {
        work[k].children = resolveStar(work[k].children, text, work[k].cs, work[k].ce);
      }
    }
    return work;
  }
  const slice = text.slice(sliceStart, sliceEnd);
  const hasTick = slice.indexOf('`') !== -1;
  const needCode = hasTick || slice.indexOf('\\') !== -1;
  const needSkip = hasTick || slice.indexOf('[') !== -1 || slice.indexOf('<') !== -1;
  const masked = (needCode || needSkip) ? maskInlineText(slice, needCode, needSkip) : slice;
  const lim = closerLimits(masked);
  const work = items.slice();
  let i = 0;
  while (i < work.length) {
    const it = work[i];
    if (it.t === 'del') {
      it.children = resolveStar(it.children, text, it.cs, it.ce);
      i++;
      continue;
    }
    if (it.t !== 'delim' || (it.ch !== 42 && it.ch !== 95)) {
      i++;
      continue;
    }
    const res = tryEmStrong(work, i, text, sliceStart, sliceEnd, masked, lim);
    if (res === null) {
      if (it.len > 1) {
        // No match from the whole run: one delimiter becomes literal
        // text and the search retries from the next position in the
        // run, as the lexer does when it advances past one character.
        work[i] = { t: 'delim', ch: it.ch, len: it.len - 1, pos: it.pos + 1, open: false, close: false };
        work.splice(i, 0, { t: 'text', s: String.fromCharCode(it.ch) });
        i++;
      } else {
        i++;
      }
      continue;
    }
    const opener = work[i];
    const closer = work[res.ci];
    const u = res.isEm ? 1 : 2;
    const k = opener.len;
    const bUsed = res.bUsed;
    const content = [];
    if (k - u > 0) {
      content.push({ t: 'delim', ch: opener.ch, len: k - u, pos: opener.pos + u, open: false, close: false });
    }
    for (let j = i + 1; j < res.ci; j++) content.push(work[j]);
    if (bUsed - u > 0) {
      content.push({ t: 'delim', ch: closer.ch, len: bUsed - u, pos: closer.pos, open: false, close: false });
    }
    const children = resolveStar(content, text, opener.pos + u, closer.pos + (bUsed - u));
    const replacement = [{ t: res.isEm ? 'em' : 'strong', children }];
    if (closer.len - bUsed > 0) {
      replacement.push({ t: 'delim', ch: closer.ch, len: closer.len - bUsed, pos: closer.pos + bUsed, open: false, close: false });
    }
    work.splice(i, res.ci - i + 1, ...replacement);
    i++;
  }
  for (let k = 0; k < work.length; k++) {
    if (work[k].t === 'delim') {
      work[k] = { t: 'text', s: String.fromCharCode(work[k].ch).repeat(work[k].len) };
    }
  }
  return work;
}

// Resolve '~' strikethrough with the delimiter stack: runs of length
// 1-2 match only runs of equal length, with free lookback. Runs of
// length 3+ never reach this pass (the scanner leaves them as text).
function resolveDel(items) {
  const delims = [];
  for (const nd of items) {
    if (nd.t === 'delim' && nd.ch === 126) delims.push(nd);
  }
  let cur = 0;
  while (cur < delims.length) {
    const closer = delims[cur];
    if (!closer.close) {
      cur++;
      continue;
    }
    let openerIdx = -1;
    for (let k = cur - 1; k >= 0; k--) {
      const cand = delims[k];
      if (!items.includes(cand)) continue;
      if (cand.open && cand.len === closer.len) {
        openerIdx = k;
        break;
      }
    }
    if (openerIdx === -1) {
      cur++;
      continue;
    }
    const opener = delims[openerIdx];
    const oiPos = items.indexOf(opener);
    const ciPos = items.indexOf(closer);
    if (oiPos === -1 || ciPos === -1 || oiPos >= ciPos) {
      cur++;
      continue;
    }
    const children = items.slice(oiPos + 1, ciPos);
    const node = { t: 'del', children, cs: opener.pos + opener.len, ce: closer.pos };
    items.splice(oiPos, ciPos - oiPos + 1, node);
    delims.splice(cur, 1);
    delims.splice(openerIdx, 1);
    cur--;
  }
}

function processEmphasis(items, text, sliceStart, sliceEnd) {
  resolveDel(items);
  const resolved = resolveStar(items, text, sliceStart, sliceEnd);
  items.splice(0, items.length, ...resolved);
}

// Validate a link label the way the link pattern does: plain
// characters, escapes, nested bracket groups (at most two levels
// deep), and code spans whose content holds no backtick. A trailing
// run of two or more backticks is also allowed.
function isValidLinkLabel(s) {
  let i = 0;
  const end = s.length;
  while (i < end) {
    const c = s.charCodeAt(i);
    if (c === 92) {
      if (i + 1 >= end) return false;
      i += 2;
      continue;
    }
    if (c === 91) {
      const g = matchLabelGroup(s, i, end, 1);
      if (g === -1) return false;
      i = g;
      continue;
    }
    if (c === 96) {
      let j = i;
      while (j < end && s.charCodeAt(j) === 96) j++;
      if (j === end) return j - i >= 2;
      let k = j;
      let closed = -1;
      while (k < end) {
        if (s.charCodeAt(k) === 96) {
          let m = k;
          while (m < end && s.charCodeAt(m) === 96) m++;
          closed = m;
          break;
        }
        k++;
      }
      if (closed === -1) return false;
      i = closed;
      continue;
    }
    if (c === 93) return false;
    i++;
  }
  return true;
}

// Match a nested bracket group starting at i (s[i] === '[') at the
// given nesting depth (1 or 2). Returns the position after the
// closing ']', or -1.
function matchLabelGroup(s, i, end, depth) {
  let j = i + 1;
  while (j < end) {
    const c = s.charCodeAt(j);
    if (c === 93) return j + 1;
    if (c === 92) {
      if (j + 1 >= end) return -1;
      j += 2;
      continue;
    }
    if (c === 91) {
      if (depth >= 2) return -1;
      const g = matchLabelGroup(s, j, end, depth + 1);
      if (g === -1) return -1;
      j = g;
      continue;
    }
    j++;
  }
  return -1;
}

function isEscapedAt(text, i) {
  let k = i - 1;
  let count = 0;
  while (k >= 0 && text.charCodeAt(k) === 92) {
    count++;
    k--;
  }
  return count % 2 === 1;
}

// Would a link or image form at the ']' at text[j], judging only by
// the opener, the label pattern, the tail, and the definitions? Used
// to bound code-span searches, which cannot cross a link boundary.
// A link already formed inside the label blocks the outer one.
function linkFormsAt(text, j, openers, items, defs) {
  if (isEscapedAt(text, j)) return false;
  let opIdx = -1;
  for (let k = openers.length - 1; k >= 0; k--) {
    if (openers[k].active) {
      opIdx = k;
      break;
    }
  }
  if (opIdx === -1) return false;
  const opener = openers[opIdx];
  if (!opener.image) {
    for (let k = 0; k < opIdx; k++) {
      if (openers[k].active && openers[k].image) return false;
    }
  }
  const opPos = items.indexOf(opener);
  if (opPos !== -1) {
    for (let k = opPos + 1; k < items.length; k++) {
      const nd = items[k];
      if (nd.t === 'link' && !nd.auto && !nd.image) return false;
    }
  }
  const n = text.length;
  const after = j + 1;
  const rawLabel = text.slice(opener.srcPos, j);
  if (after < n && text.charCodeAt(after) === 40) {
    const tail = parseInlineTail(text, after);
    if (tail !== null && isValidLinkLabel(rawLabel)) return true;
    return defs.has(normaliseLabel(rawLabel));
  }
  if (after < n && text.charCodeAt(after) === 91) {
    const lab = scanLabel(text, after);
    if (lab !== null && lab.label !== '') {
      if (isValidLinkLabel(rawLabel)) return defs.has(normaliseLabel(lab.label));
      return defs.has(normaliseLabel(rawLabel));
    }
    return defs.has(normaliseLabel(rawLabel));
  }
  return defs.has(normaliseLabel(rawLabel));
}

// Find the closing backtick run of exactly runLen starting at or after
// start. The search stops at a ']' that would form a link, since a
// code span cannot cross a link boundary.
function findCodeClose(text, start, runLen, openers, items, defs) {
  const n = text.length;
  let i = start;
  while (i < n) {
    const c = text.charCodeAt(i);
    if (c === 96) {
      let j = i;
      while (j < n && text.charCodeAt(j) === 96) j++;
      if (j - i === runLen) return i;
      i = j;
    } else if (c === 93 && linkFormsAt(text, i, openers, items, defs)) {
      return -1;
    } else {
      i++;
    }
  }
  return -1;
}

// ---------- inline parser: scanner and link resolution ----------

// Try to resolve a link or image at the ']' at text[closePos]. One attempt
// per ']': the nearest active opener is tried, and a failed attempt
// deactivates it. A '[' shadowed by an earlier active '![' cannot form a
// link (the ']' belongs to the pending image label). On success the items
// array is restructured and the position after the link tail is returned.
// Expand a raw source string into text/entity nodes, resolving entities
// the way the inline scanner does (named pass through verbatim, numeric
// decode to the character).
function expandRawText(s) {
  const nodes = [];
  let start = 0;
  for (let i = 0; i < s.length; i++) {
    if (s.charCodeAt(i) === 38) {
      const e = scanEntity(s, i);
      if (e !== null) {
        if (i > start) nodes.push({ t: 'text', s: s.slice(start, i) });
        nodes.push(e.numeric ? { t: 'text', s: e.decoded } : { t: 'entity', s: e.raw });
        i += e.len - 1;
        start = i + 1;
      }
    }
  }
  if (start < s.length) nodes.push({ t: 'text', s: s.slice(start) });
  if (nodes.length === 0) nodes.push({ t: 'text', s: '' });
  return nodes;
}

function tryResolveLink(items, openers, text, closePos, defs, st) {
  let opIdx = -1;
  for (let k = openers.length - 1; k >= 0; k--) {
    if (openers[k].active) {
      opIdx = k;
      break;
    }
  }
  if (opIdx === -1) return null;
  const opener = openers[opIdx];
  if (!opener.image) {
    for (let k = 0; k < opIdx; k++) {
      if (openers[k].active && openers[k].image) {
        opener.active = false;
        return null;
      }
    }
  }
  const n = text.length;
  const after = closePos + 1;
  let dest = null;
  let title = null;
  let next = -1;
  let ok = false;
  const rawLabel = text.slice(opener.srcPos, closePos);
  if (after < n && text.charCodeAt(after) === 40) {
    const tail = parseInlineTail(text, after);
    if (tail !== null && isValidLinkLabel(rawLabel)) {
      dest = tail.dest;
      title = tail.title;
      next = tail.next;
      ok = true;
    } else {
      // A failed inline tail falls back to a shortcut reference.
      const def = defs.get(normaliseLabel(rawLabel));
      if (def !== undefined) {
        dest = def.dest;
        title = def.title;
        next = after;
        ok = true;
      }
    }
  } else if (after < n && text.charCodeAt(after) === 91) {
    const lab = scanLabel(text, after);
    if (lab !== null && lab.label !== '') {
      // Full reference: the first label follows the link-label pattern.
      // When the pattern matches but the definition is missing, the '['
      // is consumed as literal text and no shortcut is tried. When the
      // pattern itself fails, the shortcut form is tried instead.
      if (isValidLinkLabel(rawLabel)) {
        const def = defs.get(normaliseLabel(lab.label));
        if (def !== undefined) {
          dest = def.dest;
          title = def.title;
          next = lab.next;
          ok = true;
        }
      } else {
        const def = defs.get(normaliseLabel(rawLabel));
        if (def !== undefined) {
          dest = def.dest;
          title = def.title;
          next = after;
          ok = true;
        }
      }
    } else if (lab !== null) {
      // Collapsed reference.
      const def = defs.get(normaliseLabel(rawLabel));
      if (def !== undefined) {
        dest = def.dest;
        title = def.title;
        next = lab.next;
        ok = true;
      }
    } else {
      const def = defs.get(normaliseLabel(rawLabel));
      if (def !== undefined) {
        dest = def.dest;
        title = def.title;
        next = after;
        ok = true;
      }
    }
  } else {
    const def = defs.get(normaliseLabel(rawLabel));
    if (def !== undefined) {
      dest = def.dest;
      title = def.title;
      next = after;
      ok = true;
    }
  }
  if (!ok) {
    opener.active = false;
    return null;
  }
  const opPos = items.indexOf(opener);
  if (opPos === -1) {
    opener.active = false;
    return null;
  }
  let children;
  if (opener.image) {
    // Image labels parse independently: inner links form and feed the alt
    // text, and emphasis does not leak across the label boundary. The
    // label parses with in-link state set, then the state is restored.
    st.inLink = true;
    children = parseInline(text.slice(opener.srcPos, closePos), defs, st);
    st.inLink = opener.inLink;
  } else {
    children = items.slice(opPos + 1);
    // Autolinks do not form inside link text: expand any EXTENDED autolink
    // the scan produced back into plain text nodes. Angle-bracket
    // autolinks do nest inside link text, so they are left alone.
    const expanded = [];
    for (const ch of children) {
      if (ch.t === 'link' && ch.auto && ch.ext) expanded.push(...expandRawText(ch.rawText));
      else expanded.push(ch);
    }
    children = expanded;
    processEmphasis(children, text, opener.srcPos, closePos);
    st.inLink = opener.inLink;
  }
  const node = { t: 'link', dest, title, children, image: opener.image, auto: false };
  items.splice(opPos, items.length - opPos, node);
  opener.active = false;
  if (!opener.image) {
    for (let k = 0; k < opIdx; k++) openers[k].active = false;
  }
  return { next };
}

function parseInline(text, defs, st) {
  const items = [];
  const openers = [];
  const n = text.length;
  let i = 0;
  let textStart = 0;

  function flushText(upto) {
    if (upto > textStart) {
      items.push({ t: 'text', s: text.slice(textStart, upto) });
    }
  }

  while (i < n) {
    const c = text.charCodeAt(i);

    // Backslash escape, or backslash hard break before a newline.
    if (c === 92) {
      if (i + 1 < n) {
        const nc = text.charCodeAt(i + 1);
        if (nc === LF) {
          flushText(i);
          items.push({ t: 'br' });
          i += 2;
          while (i < n && isSpaceTab(text.charCodeAt(i))) i++;
          textStart = i;
          continue;
        }
        if (isAsciiPunct(nc)) {
          flushText(i);
          items.push({ t: 'text', s: text[i + 1] });
          i += 2;
          textStart = i;
          continue;
        }
      }
      i++;
      continue;
    }

    // Code span.
    if (c === 96) {
      let j = i;
      while (j < n && text.charCodeAt(j) === 96) j++;
      const runLen = j - i;
      const close = findCodeClose(text, j, runLen, openers, items, defs);
      if (close !== -1) {
        let content = text.slice(j, close).replace(/\n/g, ' ');
        if (content.length >= 2 &&
            content.charCodeAt(0) === SPACE &&
            content.charCodeAt(content.length - 1) === SPACE &&
            !/^[ ]+$/.test(content)) {
          content = content.slice(1, -1);
        }
        flushText(i);
        items.push({ t: 'code', s: content });
        i = close + runLen;
        textStart = i;
        continue;
      }
      i = j;
      continue;
    }

    // Autolink or inline HTML tag.
    if (c === 60) {
      const auto = tryAutolink(text, i);
      if (auto !== null) {
        flushText(i);
        items.push(auto.node);
        i = auto.next;
        textStart = i;
        continue;
      }
      const tagLen = scanHtmlTag(text, i);
      if (tagLen > 0) {
        flushText(i);
        const tagText = text.slice(i, i + tagLen);
        items.push({ t: 'html', s: tagText });
        // <a ...> opens the in-link state, </a> closes it (startATag needs
        // "<a " with a literal space; endATag needs "</a>" exactly).
        if (!st.inLink) {
          if (tagLen >= 3 && (tagText.charCodeAt(1) | 32) === 97 && tagText.charCodeAt(2) === 32) {
            st.inLink = true;
          }
        } else if (tagLen >= 4 && tagText.charCodeAt(1) === 47 &&
            (tagText.charCodeAt(2) | 32) === 97 && tagText.charCodeAt(3) === 62) {
          st.inLink = false;
        }
        i += tagLen;
        textStart = i;
        continue;
      }
      i++;
      continue;
    }

    // Link/image opener.
    if (c === 91) {
      flushText(i);
      const op = { t: 'opener', image: false, active: true, srcPos: i + 1, inLink: st.inLink };
      items.push(op);
      openers.push(op);
      i++;
      textStart = i;
      continue;
    }
    if (c === 33 && i + 1 < n && text.charCodeAt(i + 1) === 91) {
      flushText(i);
      const op = { t: 'opener', image: true, active: true, srcPos: i + 2, inLink: st.inLink };
      items.push(op);
      openers.push(op);
      i += 2;
      textStart = i;
      continue;
    }

    // Link/image closer.
    if (c === 93) {
      flushText(i);
      const resolved = tryResolveLink(items, openers, text, i, defs, st);
      if (resolved !== null) {
        i = resolved.next;
        textStart = i;
        continue;
      }
      // Failed: the text before ']' was already flushed, so restart the
      // pending run at the ']' itself to avoid emitting it twice.
      textStart = i;
      i++;
      continue;
    }

    // Emphasis / strikethrough delimiters.
    if (c === 42 || c === 95 || c === 126) {
      let j = i;
      while (j < n && text.charCodeAt(j) === c) j++;
      const runLen = j - i;
      if (c === 126 && runLen >= 3) {
        i = j;
        continue;
      }
      const before = charBefore(text, i);
      const after = charAt(text, j);
      const leftFlank = !isSpaceChar(after) &&
        (!isPunctChar(after) || isSpaceChar(before) || isPunctChar(before));
      const rightFlank = !isSpaceChar(before) &&
        (!isPunctChar(before) || isSpaceChar(after) || isPunctChar(after));
      let canOpen;
      let canClose;
      if (c === 95) {
        canOpen = leftFlank && (!rightFlank || isPunctChar(before));
        canClose = rightFlank && (!leftFlank || isPunctChar(after));
      } else {
        canOpen = leftFlank;
        canClose = rightFlank;
      }
      flushText(i);
      items.push({ t: 'delim', ch: c, len: runLen, pos: i, open: canOpen, close: canClose });
      i = j;
      textStart = i;
      continue;
    }

    // Entity reference.
    if (c === 38) {
      const e = scanEntity(text, i);
      if (e !== null) {
        flushText(i);
        if (e.numeric) {
          items.push({ t: 'text', s: e.decoded });
        } else {
          items.push({ t: 'entity', s: e.raw });
        }
        i += e.len;
        textStart = i;
        continue;
      }
      i++;
      continue;
    }

    // Newline: hard break when two or more spaces precede it.
    if (c === LF) {
      let k = i - 1;
      let spaces = 0;
      while (k >= textStart && text.charCodeAt(k) === SPACE) {
        spaces++;
        k--;
      }
      if (spaces >= 2) {
        flushText(i - spaces);
        items.push({ t: 'br' });
        i++;
        // A hard break swallows the next line's leading spaces/tabs.
        while (i < n && isSpaceTab(text.charCodeAt(i))) i++;
        textStart = i;
        continue;
      }
      i++;
      continue;
    }

    // Extended autolinks (suppressed while in-link state is set).
    if (!st.inLink && (isAsciiLetter(c) || isAsciiDigit(c) || c === 46 || c === 43 || c === 45)) {
      const ext = tryExtendedAutolink(text, i, openers, items, c);
      if (ext !== null) {
        flushText(i);
        items.push(ext.node);
        i = ext.next;
        textStart = i;
        continue;
      }
    }

    i++;
  }

  flushText(n);
  processEmphasis(items, text, 0, n);
  return items;
}

// ---------- rendering ----------

function plainText(nodes) {
  let out = '';
  for (const node of nodes) {
    switch (node.t) {
      case 'text':
      case 'entity':
      case 'code':
      case 'html':
        out += node.s;
        break;
      case 'delim':
        out += String.fromCharCode(node.ch).repeat(node.len);
        break;
      case 'opener':
        out += node.image ? '![' : '[';
        break;
      case 'em':
      case 'strong':
      case 'del':
        out += plainText(node.children);
        break;
      case 'link':
        if (node.auto) out += node.rawText;
        else out += plainText(node.children);
        break;
      default:
        break;
    }
  }
  return out;
}

function renderLink(node, defs) {
  const href = escapeAttr(encodeUrl(node.dest));
  const titleAttr = node.title !== null && node.title !== ''
    ? ' title="' + escapeAttr(node.title) + '"'
    : '';
  if (node.image) {
    const alt = escapeText(plainText(node.children));
    return '<img src="' + href + '" alt="' + alt + '"' + titleAttr + '>';
  }
  if (node.auto) {
    return '<a href="' + href + '">' + escapeText(node.rawText) + '</a>';
  }
  return '<a href="' + href + '"' + titleAttr + '>' + renderInline(node.children, defs) + '</a>';
}

function renderInline(nodes, defs) {
  let out = '';
  for (const node of nodes) {
    switch (node.t) {
      case 'text':
        out += escapeRaw(node.s);
        break;
      case 'entity':
      case 'html':
        out += node.s;
        break;
      case 'code':
        out += '<code>' + escapeRaw(node.s) + '</code>';
        break;
      case 'br':
        out += '<br>';
        break;
      case 'delim':
        out += escapeRaw(String.fromCharCode(node.ch).repeat(node.len));
        break;
      case 'opener':
        out += node.image ? '![' : '[';
        break;
      case 'em':
        out += '<em>' + renderInline(node.children, defs) + '</em>';
        break;
      case 'strong':
        out += '<strong>' + renderInline(node.children, defs) + '</strong>';
        break;
      case 'del':
        out += '<del>' + renderInline(node.children, defs) + '</del>';
        break;
      case 'link':
        out += renderLink(node, defs);
        break;
      default:
        break;
    }
  }
  return out;
}

function renderText(text, defs, st) {
  return renderInline(parseInline(text, defs, st), defs);
}

function taskCheckbox(task) {
  return task === 'checked'
    ? '<input checked="" disabled="" type="checkbox">'
    : '<input disabled="" type="checkbox">';
}

function renderItem(item, defs, tight, st) {
  let inner = '';
  const children = item.children;
  for (let k = 0; k < children.length; k++) {
    const child = children[k];
    const checkbox = k === 0 && child.t === 'para' && item.task
      ? taskCheckbox(item.task) + ' '
      : '';
    if (child.t === 'para' && tight) {
      inner += checkbox + renderText(child.text, defs, st);
    } else if (child.t === 'para') {
      inner += '<p>' + checkbox + renderText(child.text, defs, st) + '</p>\n';
    } else {
      inner += renderBlock(child, defs, st);
    }
  }
  return '<li>' + inner + '</li>\n';
}

function renderTable(table, defs, st) {
  let out = '<table>\n<thead>\n<tr>\n';
  for (let k = 0; k < table.ncols; k++) {
    const align = table.aligns[k];
    const attr = align !== null ? ' align="' + align + '"' : '';
    out += '<th' + attr + '>' + renderText(table.header[k], defs, st) + '</th>\n';
  }
  out += '</tr>\n</thead>\n';
  if (table.rows.length > 0) {
    out += '<tbody>';
    for (const row of table.rows) {
      out += '<tr>\n';
      for (let k = 0; k < table.ncols; k++) {
        const align = table.aligns[k];
        const attr = align !== null ? ' align="' + align + '"' : '';
        out += '<td' + attr + '>' + renderText(row[k], defs, st) + '</td>\n';
      }
      out += '</tr>\n';
    }
    out += '</tbody></table>\n';
  } else {
    out += '</table>\n';
  }
  return out;
}

function renderBlock(block, defs, st) {
  switch (block.t) {
    case 'doc': {
      let out = '';
      for (const child of block.children) out += renderBlock(child, defs, st);
      return out;
    }
    case 'quote': {
      let out = '<blockquote>\n';
      for (const child of block.children) out += renderBlock(child, defs, st);
      return out + '</blockquote>\n';
    }
    case 'list': {
      const tag = block.ordered ? 'ol' : 'ul';
      const start = block.ordered && block.start !== 1 ? ' start="' + block.start + '"' : '';
      let out = '<' + tag + start + '>\n';
      for (const child of block.children) out += renderItem(child, defs, block.tight, st);
      return out + '</' + tag + '>\n';
    }
    case 'head':
      return '<h' + block.level + '>' + renderText(block.text, defs, st) + '</h' + block.level + '>\n';
    case 'para':
      return '<p>' + renderText(block.text, defs, st) + '</p>\n';
    case 'code': {
      const cls = block.lang !== '' ? ' class="language-' + escapeAttr(block.lang) + '"' : '';
      return '<pre><code' + cls + '>' + escapeRaw(block.content) + '</code></pre>\n';
    }
    case 'html':
      return block.text;
    case 'hr':
      return '<hr>\n';
    case 'table':
      return renderTable(block, defs, st);
    default:
      return '';
  }
}

// ---------- entry point ----------

export function parse(markdown) {
  const norm = String(markdown).replace(/\r\n?/g, '\n');
  const endsWithNewline = norm.endsWith('\n');
  const lines = norm.split('\n');
  if (endsWithNewline) lines.pop();
  const { doc, defs } = parseBlocks(lines, endsWithNewline);
  // Shared inline-lexer state: an unclosed <a ...> tag suppresses extended
  // autolinks for the rest of the document.
  const st = { inLink: false };
  return renderBlock(doc, defs, st);
}
