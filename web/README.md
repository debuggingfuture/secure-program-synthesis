# postern-web

Astro site for the Postern research artifact:

- `/` — landing with claim, contributions, repo pointers.
- `/paper` — `paper/paper.md` rendered with KaTeX math, Mermaid
  diagrams, and BibTeX citations resolved against
  `paper/references.bib`.
- `/slides` — 6-slide reveal.js deck (title, problem, architecture,
  Lean theorems, Rust mirror, open problems).
- `/demo` — interactive form that calls the WASM-compiled
  `postern-core::rewrite` from the browser.

## Run

```sh
pnpm install
pnpm dev   # http://localhost:4321
```

`predev` and `prebuild` invoke `wasm-pack` against
`prototype/crates/postern-wasm` and drop the artifacts under
`src/wasm/` (gitignored). Build needs the `wasm32-unknown-unknown`
Rust target installed (`rustup target add wasm32-unknown-unknown`).

## Deploy

```sh
pnpm build
pnpm deploy:cf   # wrangler pages deploy dist --project-name postern-web
```

`wrangler.toml` ships the project name (`postern-web`, placeholder).
Custom domain attach via `wrangler pages project domain add ...`.

## Layout

```text
web/
├── astro.config.mjs        # tailnet allowedHosts + raw imports
├── wrangler.toml           # Cloudflare Pages config
├── src/
│   ├── layouts/Base.astro  # nav + footer
│   ├── lib/                # paper renderer, BibTeX parser, demo data
│   ├── pages/              # /, /paper, /slides, /demo
│   ├── styles/global.css
│   └── wasm/               # wasm-pack output (gitignored)
└── README.md
```

## Notes on the WASM surface

The browser demo invokes one function — `rewrite_plan(request)` from
`prototype/crates/postern-wasm`. It wraps `postern-core::rewrite` and
returns either `{ok: true, allowed, input_plan, output_plan}` or
`{ok: false, reason, allowed}`. The `postern-core` rewriter is the
Rust mirror of `verifier/lean/Postern.lean`; the WASM does NOT yet
call into `biscuit_auth::datalog::World` — that migration is task
#4 in the pivot plan and disclosed in the demo's "About this demo"
panel.
