/**
 * Render the Postern paper (Pandoc-flavoured markdown + BibTeX) to
 * HTML at build time. Handles:
 *
 *   - YAML front-matter (extracts title/subtitle/author/abstract/keywords)
 *   - `[@key]` and `[@k1; @k2]` citations → numbered superscripts
 *   - `$...$` and `$$...$$` math via KaTeX server-side
 *   - mermaid code blocks → `<pre class="mermaid">` for client render
 *   - everything else via markdown-it
 */

import MarkdownIt from "markdown-it";
import anchor from "markdown-it-anchor";
import katex from "katex";
import { parseBib, formatCitation, type BibEntry } from "./bibtex.ts";

// Inline paper.md and references.bib at build time via Vite raw imports.
// These resolve against the repo on the source tree (not the bundle output).
import paperSrc from "../../../paper/paper.md?raw";
import bibSrc from "../../../paper/references.bib?raw";

export interface PaperFrontmatter {
  title: string;
  subtitle?: string;
  author?: string[];
  abstract?: string;
  keywords?: string[];
}

export interface RenderedPaper {
  frontmatter: PaperFrontmatter;
  html: string;
  references: Array<{ key: string; index: number; text: string }>;
}

function parseFrontmatter(src: string): {
  fm: PaperFrontmatter;
  body: string;
} {
  if (!src.startsWith("---\n")) {
    return { fm: { title: "Untitled" }, body: src };
  }
  const end = src.indexOf("\n---\n", 4);
  if (end === -1) return { fm: { title: "Untitled" }, body: src };
  const yaml = src.slice(4, end);
  const body = src.slice(end + 5);

  // Very small YAML parser sufficient for the paper's frontmatter:
  //   key: "value"
  //   key: |
  //     multiline
  //   key:
  //     - item
  //     - item
  //     - name: foo
  //   key: ["a","b"]
  const fm: Record<string, unknown> = {};
  const lines = yaml.split("\n");
  let i = 0;
  while (i < lines.length) {
    const line = lines[i]!;
    if (!line.trim() || line.trimStart().startsWith("#")) {
      i++;
      continue;
    }
    const m = /^([A-Za-z_][\w-]*)\s*:\s*(.*)$/.exec(line);
    if (!m) {
      i++;
      continue;
    }
    const key = m[1]!;
    const inline = m[2]!.trim();
    if (inline === "|") {
      // Block scalar — collect indented lines.
      const buf: string[] = [];
      i++;
      while (i < lines.length && (lines[i]!.startsWith("  ") || !lines[i]!.trim())) {
        buf.push(lines[i]!.replace(/^  /, ""));
        i++;
      }
      fm[key] = buf.join("\n").trim();
    } else if (inline === "") {
      // List or nested map.
      i++;
      const list: unknown[] = [];
      while (i < lines.length && lines[i]!.startsWith("  -")) {
        const itemLine = lines[i]!.slice(3).trim();
        if (itemLine.includes(":")) {
          // Object item — collect nested keys.
          const obj: Record<string, string> = {};
          const first = /^([A-Za-z_][\w-]*)\s*:\s*(.*)$/.exec(itemLine);
          if (first) obj[first[1]!] = stripYamlString(first[2]!);
          i++;
          while (i < lines.length && lines[i]!.startsWith("    ")) {
            const sub = /^\s+([A-Za-z_][\w-]*)\s*:\s*(.*)$/.exec(lines[i]!);
            if (sub) obj[sub[1]!] = stripYamlString(sub[2]!);
            i++;
          }
          list.push(obj);
        } else {
          list.push(stripYamlString(itemLine));
          i++;
        }
      }
      fm[key] = list;
    } else {
      fm[key] = stripYamlString(inline);
      i++;
    }
  }

  // Normalise author shape.
  let author: string[] | undefined;
  if (Array.isArray(fm.author)) {
    author = fm.author.map((a) =>
      typeof a === "string" ? a : ((a as { name?: string }).name ?? ""),
    );
  } else if (typeof fm.author === "string") {
    author = [fm.author];
  }

  return {
    fm: {
      title: typeof fm.title === "string" ? fm.title : "Untitled",
      subtitle: typeof fm.subtitle === "string" ? fm.subtitle : undefined,
      author,
      abstract: typeof fm.abstract === "string" ? fm.abstract : undefined,
      keywords: Array.isArray(fm.keywords)
        ? (fm.keywords as string[]).filter((k) => typeof k === "string")
        : undefined,
    },
    body,
  };
}

function stripYamlString(s: string): string {
  const trimmed = s.trim();
  if (
    (trimmed.startsWith('"') && trimmed.endsWith('"')) ||
    (trimmed.startsWith("'") && trimmed.endsWith("'"))
  ) {
    return trimmed.slice(1, -1);
  }
  return trimmed;
}

function renderMath(src: string, displayMode: boolean): string {
  try {
    return katex.renderToString(src, {
      displayMode,
      throwOnError: false,
      strict: "ignore",
    });
  } catch (e) {
    return '<span class="math-error" title="' + String(e) + '">' + src + "</span>";
  }
}

interface CitationState {
  /** key → 1-based index in the rendered references section */
  indices: Map<string, number>;
  /** in citation order */
  order: string[];
}

function resolveCitations(body: string, state: CitationState): string {
  // `[@key]`, `[@k1; @k2]`, and `[@k1; @k2; @k3]` patterns.
  return body.replace(/\[@([^\]]+)\]/g, (_match, inner: string) => {
    const keys = inner
      .split(";")
      .map((k) => k.trim().replace(/^@/, "").trim())
      .filter(Boolean);
    const refs = keys.map((key) => {
      let idx = state.indices.get(key);
      if (!idx) {
        idx = state.order.length + 1;
        state.indices.set(key, idx);
        state.order.push(key);
      }
      return '<sup class="cite"><a href="#ref-' + key + '">' + idx + "</a></sup>";
    });
    return refs.join("");
  });
}

function setupMarkdown(): MarkdownIt {
  const md = new MarkdownIt({
    html: true,
    linkify: true,
    // Disable typographer to avoid smartypants rewriting whitespace
    // around inline HTML we splice in for math.
    typographer: false,
    breaks: false,
  });

  md.use(anchor, {
    permalink: anchor.permalink.headerLink({ safariReaderFix: true }),
    level: [1, 2, 3, 4],
    slugify: (s: string) =>
      s
        .toLowerCase()
        .replace(/[^\w\s-]/g, "")
        .trim()
        .replace(/\s+/g, "-"),
  });

  // Mermaid fence → preserve for client-side rendering.
  const defaultFence = md.renderer.rules.fence!.bind(md.renderer.rules);
  md.renderer.rules.fence = (tokens, idx, options, env, self) => {
    const token = tokens[idx]!;
    const info = (token.info || "").trim();
    if (info === "mermaid") {
      return '<pre class="mermaid">' + escapeHtml(token.content) + "</pre>\n";
    }
    return defaultFence(tokens, idx, options, env, self);
  };

  return md;
}

function escapeHtml(s: string): string {
  return s
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;");
}

function escapeAttr(s: string): string {
  return escapeHtml(s).replace(/"/g, "&quot;");
}

/**
 * Pre-process math: replace `$$...$$` and `$...$` with rendered HTML
 * BEFORE markdown-it sees them. We emit raw HTML directly — earlier
 * we used text-token placeholders but markdown-it's typographer was
 * rewriting their whitespace delimiters to U+FFFD replacement chars.
 */
function renderMathSpans(body: string): string {
  let out = body;

  // Display math: `$$...$$` — emit a block-level <div> set off by
  // blank lines so markdown-it treats it as an HTML block.
  out = out.replace(
    /\$\$([\s\S]+?)\$\$/g,
    (_m, expr: string) =>
      '\n\n<div class="math-display">' +
      renderMath(expr.trim(), true) +
      "</div>\n\n",
  );

  // Inline math: `$...$`. Pandoc rule: opening `$` must NOT be
  // followed by whitespace, closing `$` must NOT be preceded by
  // whitespace, and closing `$` must NOT be followed by a digit
  // (avoid currency `$5`). Reject opening when preceded by `\` or `$`.
  out = out.replace(
    /(^|[^\w\\$])\$([^\s$][^$\n]*?[^\s$])\$(?!\d)/g,
    (_m, pre: string, expr: string) =>
      pre +
      '<span class="math-inline">' +
      renderMath(expr, false) +
      "</span>",
  );
  // Single-character inline math (e.g. `$x$`).
  out = out.replace(
    /(^|[^\w\\$])\$([^\s$])\$(?!\d)/g,
    (_m, pre: string, expr: string) =>
      pre +
      '<span class="math-inline">' +
      renderMath(expr, false) +
      "</span>",
  );

  return out;
}

/** Render the paper at `paper/paper.md`. */
export async function renderPaper(): Promise<RenderedPaper> {
  const raw: string = paperSrc;
  const entries = parseBib(bibSrc);
  const byKey = new Map<string, BibEntry>();
  for (const e of entries) byKey.set(e.key, e);

  const { fm, body } = parseFrontmatter(raw);
  const state: CitationState = { indices: new Map(), order: [] };

  // 1. resolve citations FIRST so the `<sup>` anchors survive any
  //    later text mutation.
  const cited = resolveCitations(body, state);

  // 1b. Rewrite pandoc-flavoured figure references for HTML output.
  //     Markdown source carries `![cap](figures/foo.pdf){#fig:x width=N%}`
  //     because tectonic embeds the PDF directly. For the web we
  //     (a) swap the .pdf path for the SVG mirror under /figures/,
  //     and (b) wrap the result in <figure>/<figcaption> so the caption
  //     renders (markdown-it ignores pandoc attr blocks otherwise).
  const figured = cited.replace(
    /!\[([^\]]+)\]\(figures\/([^)]+)\.pdf\)(\{[^}]*\})?/g,
    (_m, caption: string, base: string) =>
      '<figure class="paper-figure">' +
      `<img src="/figures/${base}.svg" alt="${escapeAttr(caption)}" />` +
      `<figcaption>${caption}</figcaption>` +
      "</figure>",
  );

  // 2. swap math expressions for inline KaTeX HTML.
  const mathed = renderMathSpans(figured);

  // 3. markdown → HTML.
  const md = setupMarkdown();
  const html = md.render(mathed);

  // 4. build references section in citation order.
  const references = state.order.map((key, i) => {
    const entry = byKey.get(key);
    return {
      key,
      index: i + 1,
      text: entry ? formatCitation(entry) : "(missing reference: " + key + ")",
    };
  });

  return { frontmatter: fm, html, references };
}
