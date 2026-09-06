import { defineConfig } from "astro/config";

export default defineConfig({
  site: "https://sean-reid.github.io",
  base: "/square-achievement",
  compressHTML: false,
  // the two result pages of earlier versions, now one result
  redirects: {
    "/threshold": "/square-achievement/",
    "/threshold/proof": "/square-achievement/proof/",
    "/plus": "/square-achievement/",
    "/plus/proof": "/square-achievement/proof/",
  },
});
