import { expect, test } from "@playwright/test";

test("the hub leads with the game and lists the results", async ({ page }) => {
  await page.goto("./");
  await expect(page.locator("h1")).toContainText("Square Achievement Game");
  await expect(page.locator("sag-board .sag-svg")).toBeVisible();
  await expect(page.locator("article.result")).toHaveCount(1);
  await expect(page.locator("article.result h3")).toContainText(
    "winning threshold",
  );
});

test("the result overview states the theorem and its routes", async ({
  page,
}) => {
  await page.goto("./");
  await page.locator('article.result a[href$="threshold/"]').click();
  await expect(page.locator(".theorem")).toContainText("if and only if");
  await expect(page.locator("nav.routes a")).toHaveCount(3);
  await expect(page.locator("pre.lean")).toContainText("theorem outcome");
});

test("the proof guide has its figures and references", async ({ page }) => {
  await page.goto("./threshold/");
  await page.locator('nav.routes a[href$="threshold/proof/"]').click();
  await expect(page.locator("h1")).toContainText("How the proof works");
  await expect(page.locator("figure.diagram")).toHaveCount(3);
  await expect(page.locator("ol.refs li")).toHaveCount(9);
  await expect(page.locator("sag-board .sag-x")).toHaveCount(1);
});

test("placing a stone draws the bot's reply", async ({ page }) => {
  await page.goto("./");
  await page.locator('sag-board rect[data-i="1"]').click();
  await expect(page.locator("sag-board .sag-o")).toHaveCount(1);
  await expect(page.locator("sag-board .sag-x")).toHaveCount(2);
});

test("the board plays from the keyboard", async ({ page }) => {
  await page.goto("./");
  await page.locator("sag-board .sag-svg").focus();
  await page.keyboard.press("ArrowRight");
  await page.keyboard.press("Enter");
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
