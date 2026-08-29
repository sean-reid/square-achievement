import { defineConfig, devices } from "@playwright/test";

export default defineConfig({
  testDir: "e2e",
  webServer: {
    command: "npm run build && npm run preview",
    port: 4321,
    reuseExistingServer: !process.env["CI"],
  },
  use: { baseURL: "http://localhost:4321/square-achievement/" },
  projects: [
    { name: "desktop", use: { ...devices["Desktop Chrome"] } },
    { name: "mobile", use: { ...devices["iPhone 13"] } },
  ],
});
