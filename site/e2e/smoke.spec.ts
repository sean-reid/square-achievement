import { expect, test } from "@playwright/test";

test("the article and the game load", async ({ page }) => {
  await page.goto("./");
  await expect(page.locator("h1")).toContainText("Square Achievement Game");
  await expect(page.locator("sag-board .sag-grid")).toBeVisible();
  await expect(
    page.locator("sag-board .sag-cell", { hasText: "X" }),
  ).toHaveCount(1);
});

test("placing a stone draws the bot's reply", async ({ page }) => {
  await page.goto("./");
  await page.locator('sag-board .sag-cell[data-r="0"][data-c="0"]').click();
  await expect(
    page.locator("sag-board .sag-cell", { hasText: "O" }),
  ).toHaveCount(1);
  await expect(
    page.locator("sag-board .sag-cell", { hasText: "X" }),
  ).toHaveCount(2);
});
