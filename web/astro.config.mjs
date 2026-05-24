// @ts-check
import { defineConfig } from "astro/config";

// https://astro.build/config
export default defineConfig({
  // Default subdomain for Cloudflare Pages; user will set custom domain later.
  site: "https://postern-web.pages.dev",
  // Bind dev/preview to all interfaces so the Tailscale MagicDNS host
  // (`<device>.<tailnet>.ts.net`) reaches the dev server.
  server: {
    host: true,
  },
  vite: {
    server: {
      // Allow Tailnet MagicDNS hosts (`.ts.net` matches any subdomain).
      // Survives device rename and works across the tailnet.
      allowedHosts: [".ts.net"],
    },
    preview: {
      allowedHosts: [".ts.net"],
    },
    // wasm-pack's generated glue imports the .wasm via URL — Vite needs
    // to leave it as an asset, not try to parse it.
    assetsInclude: ["**/*.wasm"],
  },
});
