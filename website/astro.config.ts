import react from "@astrojs/react"
import starlight from "@astrojs/starlight"
import tailwind from "@astrojs/tailwind"
import { defineConfig } from "astro/config"
import tsconfigPaths from "vite-tsconfig-paths"

// https://astro.build/config
export default defineConfig({
  base: "/ao",
  integrations: [
    starlight({
      customCss: ["./src/tailwind.css"],
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
    tailwind({ applyBaseStyles: false }),
  ],
  site: "https://ricora.github.io",
  vite: {
    optimizeDeps: {
      exclude: ["@bytecodealliance/jco/component", "@rollup/browser"],
    },
    plugins: [tsconfigPaths()],
  },
})
