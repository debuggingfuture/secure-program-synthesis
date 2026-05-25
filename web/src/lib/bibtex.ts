/**
 * Minimal BibTeX parser, tailored to the entry shapes used in
 * `paper/references.bib`. Supports `@TYPE{key, field = {value}, ...}`
 * with balanced braces and `field = "value"`. Does not handle BibTeX
 * `@string` macros, crossrefs, or LaTeX accent escapes — those are
 * absent from our 15-entry bibliography.
 */

export interface BibEntry {
  type: string;
  key: string;
  fields: Record<string, string>;
}

/** Strip LaTeX braces used purely for case-preservation: `{Foo}` → `Foo`. */
function stripBalancedBraces(s: string): string {
  // Repeatedly strip single-character `{X}` and outer-paired braces.
  let out = s;
  // Replace `{...}` groups that contain no further braces with their contents.
  // Run a few passes to handle nested groups.
  for (let i = 0; i < 4; i++) {
    out = out.replace(/\{([^{}]*)\}/g, "$1");
  }
  return out;
}

/** Normalise whitespace + escape LaTeX accents we actually encounter. */
function cleanValue(raw: string): string {
  const tex2unicode: Record<string, string> = {
    "\\\"u": "ü",
    "\\\"a": "ä",
    "\\\"o": "ö",
    "\\'e": "é",
    "\\`e": "è",
    "\\~n": "ñ",
  };
  let s = raw;
  for (const [tex, uni] of Object.entries(tex2unicode)) {
    // Both `{\"u}` and `\"u` forms.
    s = s.split(`{${tex}}`).join(uni).split(tex).join(uni);
  }
  // `\url{https://...}` → `https://...`. Run before brace stripping.
  s = s.replace(/\\url\{([^}]+)\}/g, "$1");
  // `\href{url}{text}` → `text (url)` — none in our bib, but cheap.
  s = s.replace(/\\href\{([^}]+)\}\{([^}]+)\}/g, "$2 ($1)");
  // Common LaTeX escapes that survive: `\&`, `\%`, `\$`, `\#`, `\_`,
  // and the accent-without-letter forms like `\'a` (handled), `\'`.
  s = s.replace(/\\([&%$#_])/g, "$1");
  // Accent commands like `\'e`, `\^a` we missed via the table.
  s = s.replace(/\\['`^~"=.][A-Za-z]/g, (m) => m[2] ?? "");
  // Strip any remaining backslash-command syntax we missed.
  s = s.replace(/\\[A-Za-z]+\s*/g, "");
  s = stripBalancedBraces(s);
  return s.replace(/\s+/g, " ").trim();
}

/** Read a brace-balanced or quote-delimited value starting at `i`. */
function readValue(src: string, i: number): { value: string; next: number } {
  // Skip leading whitespace.
  while (i < src.length && /\s/.test(src[i]!)) i++;
  const start = src[i];
  if (start === "{") {
    let depth = 1;
    let j = i + 1;
    while (j < src.length && depth > 0) {
      const c = src[j]!;
      if (c === "{") depth++;
      else if (c === "}") depth--;
      if (depth > 0) j++;
    }
    return { value: src.slice(i + 1, j), next: j + 1 };
  }
  if (start === '"') {
    let j = i + 1;
    while (j < src.length && src[j] !== '"') j++;
    return { value: src.slice(i + 1, j), next: j + 1 };
  }
  // Bare numeric / word value (e.g. year = 2024).
  let j = i;
  while (j < src.length && !/[,\s}]/.test(src[j]!)) j++;
  return { value: src.slice(i, j), next: j };
}

/** Parse the entries from a BibTeX file. */
export function parseBib(src: string): BibEntry[] {
  const entries: BibEntry[] = [];
  // Strip line comments (lines starting with `%`) — `references.bib`
  // uses them.
  const cleaned = src
    .split("\n")
    .map((line) => (line.trimStart().startsWith("%") ? "" : line))
    .join("\n");

  const entryStart = /@(\w+)\s*\{\s*([^,\s]+)\s*,/g;
  let m: RegExpExecArray | null;
  while ((m = entryStart.exec(cleaned)) !== null) {
    const type = m[1]!.toLowerCase();
    const key = m[2]!;
    const fields: Record<string, string> = {};
    let i = m.index + m[0].length;
    let depth = 1;
    while (i < cleaned.length && depth > 0) {
      // Skip whitespace + commas.
      while (i < cleaned.length && /[\s,]/.test(cleaned[i]!)) i++;
      if (cleaned[i] === "}") {
        depth--;
        i++;
        break;
      }
      // Read field name.
      const fnameMatch = /([A-Za-z]+)\s*=\s*/y;
      fnameMatch.lastIndex = i;
      const fm = fnameMatch.exec(cleaned);
      if (!fm) {
        // Malformed — bail to outer loop.
        i++;
        continue;
      }
      const fname = fm[1]!.toLowerCase();
      i = fnameMatch.lastIndex;
      const { value, next } = readValue(cleaned, i);
      fields[fname] = cleanValue(value);
      i = next;
    }
    entries.push({ type, key, fields });
    entryStart.lastIndex = i;
  }
  return entries;
}

/** Format a single entry as a "Authors (Year). Title. Venue." citation. */
export function formatCitation(entry: BibEntry): string {
  const f = entry.fields;
  const authors = (f.author ?? "").replace(/\s+and\s+/g, ", ");
  const year = f.year ?? "n.d.";
  const title = f.title ?? "(untitled)";
  const venue =
    f.journal ??
    f.booktitle ??
    f.howpublished ??
    f.publisher ??
    f.institution ??
    "";
  const doi = f.doi ? ` doi:${f.doi}` : "";
  const note = f.note ? ` ${f.note}.` : "";
  return [
    authors ? `${authors}.` : "",
    `(${year})`,
    `${title}.`,
    venue ? `${venue}.` : "",
    doi,
    note,
  ]
    .filter(Boolean)
    .join(" ")
    .replace(/\s+/g, " ")
    .trim();
}
