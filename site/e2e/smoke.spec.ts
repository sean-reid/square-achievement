import { expect, test } from "@playwright/test";

test("the article and the game load", async ({ page }) => {
  await page.goto("./");
  await expect(page.locator("h1")).toContainText("Square Achievement Game");
  await expect(page.locator("sag-board .sag-svg")).toBeVisible();
  await expect(page.locator("sag-board .sag-x")).toHaveCount(1);
});

test("placing a stone draws the bot's reply", async ({ page }) => {
  await page.goto("./");
  await page.locator('sag-board rect[data-i="1"]').click();
  await expect(page.locator("sag-board .sag-o")).toHaveCount(1);
  await expect(page.locator("sag-board .sag-x")).toHaveCount(2);
});

test("undo removes the last exchange", async ({ page }) => {
  await page.goto("./");
  await page.locator('sag-board rect[data-i="1"]').click();
  await page.locator("sag-board .sag-undo").click();
  await expect(page.locator("sag-board .sag-x")).toHaveCount(1);
  await expect(page.locator("sag-board .sag-o")).toHaveCount(0);
});

test("threat highlighting paints threat cells", async ({ page }) => {
  await page.goto("./");
  await page.locator("sag-board .sag-th").click();
  await page.locator('sag-board rect[data-i="1"]').click();
  await page.locator('sag-board rect[data-i="3"]').click();
  await expect
    .poll(async () => page.locator("sag-board .sag-threat").count())
    .toBeGreaterThan(0);
});

test("games are shareable through the URL", async ({ page }) => {
  await page.goto("./");
  await page.locator('sag-board rect[data-i="1"]').click();
  const url = page.url();
  expect(url).toContain("?g=5:");
  await page.goto(url);
  await expect(page.locator("sag-board .sag-o")).toHaveCount(1);
  await expect(page.locator("sag-board .sag-x")).toHaveCount(2);
});
