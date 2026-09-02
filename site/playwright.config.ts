import { defineConfig, devices } from "@playwright/test";

// PORT lets a local run coexist with a dev server on the default port
const port = Number(process.env["PORT"] ?? 4321);

export default defineConfig({
  testDir: "e2e",
  webServer: {
    command: `npm run build && npm run preview -- --port ${port}`,
    port,
    reuseExistingServer: !process.env["CI"],
  },
  use: { baseURL: `http://localhost:${port}/square-achievement/` },
  projects: [
    { name: "desktop", use: { ...devices["Desktop Chrome"] } },
    { name: "mobile", use: { ...devices["Pixel 7"] } },
  ],
});
