import react from "@astrojs/react"
import starlight from "@astrojs/starlight"
import tailwindcss from "@tailwindcss/vite";
import { defineConfig } from "astro/config"
import tsconfigPaths from "vite-tsconfig-paths"

// https://astro.build/config
export default defineConfig({
  base: "/ao",
  integrations: [
    starlight({
      customCss: ["./src/globals.css"],
      sidebar: [
        {
          items: [{ label: "Introduction", slug: "guides/introduction" }],
          label: "Guides",
        },
      ],
      social: {
        github: "https://github.com/ricora/ao",
      },
      title: "Ao Language",
    }),
    react(),
  ],
  site: "https://ricora.github.io",
  vite: {
    optimizeDeps: {
      exclude: ["@bytecodealliance/jco/component", "@rollup/browser"],
    },
    plugins: [tsconfigPaths(), tailwindcss()],
  },
})
