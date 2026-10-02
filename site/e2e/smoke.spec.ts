import { expect, test } from "@playwright/test";

test("the hub states the theorem, plays the rule, and routes onward", async ({
  page,
}) => {
  await page.goto("./");
  await expect(page.locator("h1")).toContainText("Square Achievement Game");
  await expect(page.locator(".theorem")).toContainText("if and only if");
  await expect(page.locator("sag-board .sag-svg")).toBeVisible();
  await expect(page.locator("nav.routes a")).toHaveCount(3);
  await expect(page.locator("pre.lean")).toContainText("theorem outcome");
  await expect(page.locator("pre.lean")).toContainText("plus_wins_with");
});

test("the hub's theorem carries no ply bound", async ({ page }) => {
  await page.goto("./");
  await expect(page.locator(".theorem")).toContainText(
    "following the plus rule wins.",
  );
  await expect(page.locator(".theorem")).not.toContainText("ply");
});

test("the proof guide follows the paper's sections", async ({ page }) => {
  await page.goto("./");
  await page.locator('nav.routes a[href$="proof/"]').click();
  await expect(page.locator("h1")).toContainText("How the proof works");
  await expect(page.locator("h2")).toHaveText([
    "Introduction",
    "Definitions",
    "The plus rule",
    "Small boards and the 5 × 5 board",
    "Verification",
    "Boards of size at least 17",
    "Formalization",
    "Open questions",
    "References",
  ]);
  await expect(page.locator("h3")).toHaveText([
    "Pluses",
    "Far stones and the hidden corner",
    "Tempo moves and lines",
  ]);
  await expect(page.locator(".theorem")).not.toContainText("ply");
});

test("the proof guide has its figures and references", async ({ page }) => {
  await page.goto("./proof/");
  await expect(page.locator("figure.diagram")).toHaveCount(4);
  await expect(page.locator("figure.diagram svg rect[width='12']")).toHaveCount(
    1,
  );
  await expect(page.locator("ol.refs li")).toHaveCount(13);
  await expect(page.locator("sag-board .sag-x")).toHaveCount(1);
  await expect(page.locator("pre.lean")).toContainText("plus_wins_with");
});

test("the guide speaks of the first and second player", async ({ page }) => {
  await page.goto("./proof/");
  const text = await page.locator("main, body").first().innerText();
  expect(text).not.toMatch(/\b(we|our|us|opponent|latent|farm)\b/i);
  expect(text).toContain("hidden corner");
  expect(text).toContain("branch point");
  expect(text).toContain("anchor board");
});

test("pages carry an icon and Open Graph tags", async ({ page }) => {
  await page.goto("./proof/");
  await expect(page.locator('link[rel="icon"]')).toHaveAttribute(
    "href",
    "/square-achievement/favicon.svg",
  );
  await expect(page.locator('meta[property="og:type"]')).toHaveAttribute(
    "content",
    "website",
  );
  await expect(page.locator('meta[property="og:url"]')).toHaveAttribute(
    "content",
    "https://sean-reid.github.io/square-achievement/proof/",
  );
  const icon = await page.request.get("./favicon.svg");
  expect(icon.ok()).toBe(true);
  expect(icon.headers()["content-type"]).toContain("image/svg+xml");
});

test("the old result pages redirect", async ({ page }) => {
  await page.goto("./threshold/");
  await expect(page.locator("h1")).toContainText("Square Achievement Game");
  await page.goto("./plus/proof/");
  await expect(page.locator("h1")).toContainText("How the proof works");
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
  expect(url).toContain("?g=6:");
  await page.goto(url);
  await expect(page.locator("sag-board .sag-o")).toHaveCount(1);
  await expect(page.locator("sag-board .sag-x")).toHaveCount(2);
});

test("the bot explains its moves and shows its line", async ({ page }) => {
  await page.goto("./");
  await expect(page.locator("sag-board .sag-now-text")).toContainText(
    "the opening",
  );
  await page.locator('sag-board rect[data-i="0"]').click();
  await page.locator('sag-board rect[data-i="5"]').click();
  await expect(page.locator("sag-board .sag-now-text")).toContainText(
    "threatens",
  );
  await expect(page.locator("sag-board .sag-plan-note")).toContainText(
    "plus at",
  );
  await expect
    .poll(async () => page.locator("sag-board .sag-chip").count())
    .toBeGreaterThan(2);
});

test("the 5 by 5 board plays the table without a line panel", async ({
  page,
}) => {
  await page.goto("./");
  await page.locator("sag-board .sag-dec").click();
  await expect(page.locator("sag-board .sag-size")).toHaveText("5 × 5");
  await expect(page.locator("sag-board .sag-x")).toHaveCount(1);
  await expect(page.locator("sag-board .sag-plan")).toBeHidden();
  await expect(page.locator("sag-board .sag-note")).toContainText(
    "5 × 5 table",
  );
});
