/** The interactive board: an SVG figure in the paper's own idiom.
 *
 * The visitor plays white against the bot's black stones, under the
 * plus rule or the table strategy; the `strategy` attribute picks the
 * page's default. Hairline rules, drawn stones, threat washes, a
 * winning square that draws itself in, a move list with the bot's
 * stated reasons, the rule's committed line drawn on the board, undo,
 * a shareable link, and a self-playing demonstration. Motion is subtle
 * and respects prefers-reduced-motion.
 */

import { Position, threats, winningSquare } from "./rules";
import {
  botDecision,
  effectiveStrategy,
  loadTables,
  type Strategy,
} from "./bot";
import { fmt, lineOf, type Line } from "./plus";
import { decodeGame, encodeGame } from "./url";

const U = 10; // svg units per cell
const NS = "http://www.w3.org/2000/svg";

export class SagBoard extends HTMLElement {
  private pos = new Position(5);
  private over = false;
  private showThreats = false;
  private demoTimer: ReturnType<typeof setInterval> | null = null;
  private svg!: SVGSVGElement;
  private focusIdx = 0;
  private generation = 0;
  private thinking = false;
  private wanted: Strategy = "plus";

  connectedCallback(): void {
    const params = new URLSearchParams(location.search);
    const fromUrl = params.get("g");
    const decoded = fromUrl ? decodeGame(fromUrl) : null;
    const n = decoded?.n ?? Number(this.getAttribute("n") ?? "5");
    const attr = this.getAttribute("strategy");
    const fromParam = params.get("s");
    this.wanted =
      fromParam === "table" || fromParam === "plus"
        ? fromParam
        : attr === "table"
          ? "table"
          : "plus";
    this.buildShell(n);
    this.newGame(n, decoded?.history);
  }

  /** The strategy playing on the current board. */
  private strategy(): Strategy {
    return effectiveStrategy(this.pos.n, this.wanted);
  }

  disconnectedCallback(): void {
    this.stopDemo();
  }

  private buildShell(n: number): void {
    this.innerHTML = `
      <div class="sag-controls">
        <button class="sag-dec" aria-label="smaller board">−</button>
        <span class="sag-size">${n} × ${n}</span>
        <button class="sag-inc" aria-label="larger board">+</button>
        <button class="sag-new">new game</button>
      </div>
      <div class="sag-strategy" role="group" aria-label="strategy">
        <span class="sag-strategy-label">strategy</span>
        <button data-strategy="plus" aria-pressed="false">plus rule</button>
        <button data-strategy="table" aria-pressed="false">table</button>
        <span class="sag-strategy-hint"></span>
      </div>
      <div class="sag-stage"></div>
      <p class="sag-status" role="status"></p>
      <p class="sag-quiet">
        <button class="sag-undo">undo</button> ·
        <button class="sag-th" aria-pressed="false">threats</button> ·
        <button class="sag-share">share</button> ·
        <button class="sag-demo">demo</button>
      </p>
      <aside class="sag-explain" aria-label="what the bot is thinking">
        <p class="sag-now">
          <span class="sag-explain-label">last move</span>
          <span class="sag-now-text"></span>
        </p>
        <p class="sag-plan" hidden>
          <span class="sag-explain-label">line</span>
          <span class="sag-chips"></span>
          <span class="sag-plan-note"></span>
        </p>
        <details class="sag-log">
          <summary>move log</summary>
          <ol class="sag-moves" aria-label="moves and reasons"></ol>
        </details>
      </aside>`;
    for (const b of this.querySelectorAll<HTMLButtonElement>(
      ".sag-strategy button",
    )) {
      b.addEventListener("click", () => {
        if (b.disabled || b.dataset["strategy"] === this.wanted) return;
        this.stopDemo();
        this.wanted = b.dataset["strategy"] === "table" ? "table" : "plus";
        this.newGame(this.pos.n);
      });
    }
    this.querySelector<HTMLButtonElement>(".sag-new")!.addEventListener(
      "click",
      () => {
        this.stopDemo();
        this.newGame(this.pos.n);
      },
    );
    this.querySelector<HTMLButtonElement>(".sag-dec")!.addEventListener(
      "click",
      () => {
        this.stopDemo();
        this.newGame(Math.max(2, this.pos.n - 1));
      },
    );
    this.querySelector<HTMLButtonElement>(".sag-inc")!.addEventListener(
      "click",
      () => {
        this.stopDemo();
        this.newGame(Math.min(99, this.pos.n + 1));
      },
    );
    this.querySelector<HTMLButtonElement>(".sag-undo")!.addEventListener(
      "click",
      () => {
        this.stopDemo();
        this.undoPair();
      },
    );
    this.querySelector<HTMLButtonElement>(".sag-th")!.addEventListener(
      "click",
      (e) => {
        this.showThreats = !this.showThreats;
        (e.target as HTMLButtonElement).setAttribute(
          "aria-pressed",
          String(this.showThreats),
        );
        this.paintThreats();
      },
    );
    this.querySelector<HTMLButtonElement>(".sag-share")!.addEventListener(
      "click",
      () => {
        void navigator.clipboard?.writeText(location.href).then(() => {
          this.status("link copied");
        });
      },
    );
    this.querySelector<HTMLButtonElement>(".sag-demo")!.addEventListener(
      "click",
      () => {
        if (this.demoTimer) this.stopDemo();
        else this.startDemo();
      },
    );
  }

  private newGame(n: number, replay?: number[]): void {
    this.generation++;
    this.thinking = false;
    this.pos = new Position(n);
    this.over = false;
    this.querySelector(".sag-size")!.textContent = `${n} × ${n}`;
    this.paintStrategy();
    this.buildSvg();
    if (n < 5) this.status("boards below 5 x 5 are drawn with best play");
    if (replay && replay.length > 0) {
      for (const i of replay) {
        if (this.over) break;
        const [r, c] = this.pos.cell(i);
        this.commit([r, c]);
      }
    } else {
      void this.botTurn();
    }
    this.afterMoves();
  }

  private buildSvg(): void {
    const n = this.pos.n;
    const size = n * U;
    this.svg = document.createElementNS(NS, "svg");
    this.svg.setAttribute("viewBox", `-1 -1 ${size + 2} ${size + 2}`);
    this.svg.setAttribute("class", "sag-svg");
    this.svg.setAttribute("tabindex", "0");
    this.svg.setAttribute("role", "group");
    this.svg.setAttribute(
      "aria-label",
      `${n} by ${n} board: arrow keys move, Enter or Space plays`,
    );
    this.svg.addEventListener("keydown", (e) => this.onKey(e));
    this.focusIdx = Math.min(this.focusIdx, n * n - 1);
    const stage = this.querySelector<HTMLElement>(".sag-stage")!;
    stage.innerHTML = "";
    stage.appendChild(this.svg);
    // touch targets stay usable at any n: grow past the column and
    // let the stage scroll rather than shrink the cells
    const coarse = window.matchMedia("(pointer: coarse)").matches;
    const minCell = coarse ? 44 : 26;
    const avail = stage.clientWidth || 416;
    this.svg.style.width = avail / n < minCell ? `${n * minCell}px` : "";
    for (const name of [
      "threats",
      "grid",
      "stones",
      "marks",
      "win",
      "focus",
      "cells",
    ]) {
      const g = document.createElementNS(NS, "g");
      g.setAttribute("class", `sag-${name}`);
      this.svg.appendChild(g);
    }
    const grid = this.svg.querySelector(".sag-grid")!;
    for (let k = 0; k <= n; k++) {
      for (const [x1, y1, x2, y2] of [
        [0, k * U, size, k * U],
        [k * U, 0, k * U, size],
      ]) {
        const line = document.createElementNS(NS, "line");
        line.setAttribute("x1", String(x1));
        line.setAttribute("y1", String(y1));
        line.setAttribute("x2", String(x2));
        line.setAttribute("y2", String(y2));
        grid.appendChild(line);
      }
    }
    const cells = this.svg.querySelector(".sag-cells")!;
    for (let i = 0; i < n * n; i++) {
      const [r, c] = this.pos.cell(i);
      const rect = document.createElementNS(NS, "rect");
      rect.setAttribute("x", String(c * U));
      rect.setAttribute("y", String(r * U));
      rect.setAttribute("width", String(U));
      rect.setAttribute("height", String(U));
      rect.setAttribute("data-i", String(i));
      rect.setAttribute("class", "sag-cell");
      rect.addEventListener("click", () => {
        this.focusIdx = i;
        this.paintFocus();
        this.humanPlay(i);
      });
      cells.appendChild(rect);
    }
    this.paintFocus();
  }

  /** The keyboard cursor: one tab stop for the board, arrows inside. */
  private onKey(e: KeyboardEvent): void {
    const n = this.pos.n;
    const [r, c] = this.pos.cell(this.focusIdx);
    const moves: Record<string, [number, number]> = {
      ArrowUp: [r - 1, c],
      ArrowDown: [r + 1, c],
      ArrowLeft: [r, c - 1],
      ArrowRight: [r, c + 1],
    };
    const target = moves[e.key];
    if (target) {
      e.preventDefault();
      const [tr, tc] = target;
      if (tr >= 0 && tc >= 0 && tr < n && tc < n) {
        this.focusIdx = this.pos.idx([tr, tc]);
        this.paintFocus();
      }
      return;
    }
    if (e.key === "Enter" || e.key === " ") {
      e.preventDefault();
      this.humanPlay(this.focusIdx);
    }
  }

  private paintFocus(): void {
    const layer = this.svg.querySelector(".sag-focus")!;
    layer.innerHTML = "";
    const [r, c] = this.pos.cell(this.focusIdx);
    const rect = document.createElementNS(NS, "rect");
    rect.setAttribute("x", String(c * U + 0.4));
    rect.setAttribute("y", String(r * U + 0.4));
    rect.setAttribute("width", String(U - 0.8));
    rect.setAttribute("height", String(U - 0.8));
    layer.appendChild(rect);
    this.svg.setAttribute(
      "aria-description",
      `cursor at row ${r + 1}, column ${c + 1}`,
    );
  }

  private stoneNode(i: number, first: boolean): SVGElement {
    const [r, c] = this.pos.cell(i);
    const cx = c * U + U / 2;
    const cy = r * U + U / 2;
    const g = document.createElementNS(NS, "g");
    g.setAttribute("class", first ? "sag-stone sag-x" : "sag-stone sag-o");
    g.setAttribute("data-stone", String(i));
    const circle = document.createElementNS(NS, "circle");
    circle.setAttribute("cx", String(cx));
    circle.setAttribute("cy", String(cy));
    circle.setAttribute("r", String(U * 0.32));
    g.appendChild(circle);
    return g;
  }

  /** Place a stone for the side to move. */
  private commit(cell: [number, number]): void {
    const first = this.pos.p1ToMove();
    const i = this.pos.idx(cell);
    const stones = first ? this.pos.p1 : this.pos.p2;
    const win = winningSquare(this.pos, new Set([...stones, i]), cell);
    this.pos.play(cell);
    this.svg
      .querySelector(".sag-stones")!
      .appendChild(this.stoneNode(i, first));
    if (win) {
      this.over = true;
      this.dimOthers(win);
      this.status(
        first
          ? "the strategy completes a square and wins."
          : "you completed a square: you win!",
      );
    } else if (this.pos.full()) {
      this.over = true;
      this.status("the board is full: a draw");
    }
  }

  private dimOthers(square: number[]): void {
    for (const node of this.svg.querySelectorAll(".sag-stone")) {
      const i = Number((node as SVGElement).dataset["stone"]);
      if (!square.includes(i)) node.classList.add("sag-dim");
    }
  }

  private paintThreats(): void {
    const layer = this.svg.querySelector(".sag-threats")!;
    layer.innerHTML = "";
    if (!this.showThreats || this.over) return;
    for (const i of threats(this.pos, this.pos.p1)) {
      const [r, c] = this.pos.cell(i);
      const rect = document.createElementNS(NS, "rect");
      rect.setAttribute("x", String(c * U));
      rect.setAttribute("y", String(r * U));
      rect.setAttribute("width", String(U));
      rect.setAttribute("height", String(U));
      rect.setAttribute("class", "sag-threat");
      layer.appendChild(rect);
    }
  }

  /** The bot's move, after its table has loaded; a game started in
   * the meantime discards the pending turn. */
  private async botTurn(): Promise<void> {
    if (this.over || this.pos.full() || this.thinking) return;
    const gen = this.generation;
    this.thinking = true;
    try {
      await loadTables(this.pos.n, this.strategy());
    } finally {
      this.thinking = false;
    }
    if (gen !== this.generation || this.over) return;
    const d = botDecision(this.pos, this.strategy());
    if (d.move === null) {
      this.over = true;
      this.status(
        this.strategy() === "plus"
          ? "this position is outside the rule's play"
          : "this position is outside the table",
      );
      return;
    }
    this.commit(d.move);
    this.afterMoves();
  }

  private humanPlay(i: number): void {
    if (this.over || this.demoTimer || this.pos.p1ToMove()) return;
    if (this.pos.occupied(i)) return;
    const [r, c] = this.pos.cell(i);
    this.commit([r, c]);
    this.afterMoves();
    if (!this.over) void this.botTurn();
  }

  private undoPair(): void {
    if (this.pos.history.length < 2) return;
    this.popOne();
    if (this.pos.history.length % 2 === 0) this.popOne();
    this.over = false;
    for (const node of this.svg.querySelectorAll(".sag-dim")) {
      node.classList.remove("sag-dim");
    }
    this.afterMoves();
  }

  private popOne(): void {
    const i = this.pos.history[this.pos.history.length - 1]!;
    this.pos.undo();
    this.svg.querySelector(`[data-stone="${i}"]`)?.remove();
  }

  private startDemo(): void {
    this.newGame(this.pos.n);
    this.querySelector<HTMLButtonElement>(".sag-demo")!.textContent = "stop";
    this.demoTimer = setInterval(() => {
      if (this.over || this.pos.full()) {
        this.stopDemo();
        return;
      }
      if (this.pos.p1ToMove()) void this.botTurn();
      else {
        this.commit(this.demoReply());
        this.afterMoves();
      }
    }, 700);
  }

  private stopDemo(): void {
    if (this.demoTimer) clearInterval(this.demoTimer);
    this.demoTimer = null;
    const b = this.querySelector<HTMLButtonElement>(".sag-demo");
    if (b) b.textContent = "demo";
  }

  /** The demonstration's O: block when threatened, else stay close. */
  private demoReply(): [number, number] {
    const urgent = threats(this.pos, this.pos.p1);
    if (urgent.length > 0) {
      const [r, c] = this.pos.cell(urgent[0]!);
      return [r, c];
    }
    const last = this.pos.history[this.pos.history.length - 1]!;
    const [lr, lc] = this.pos.cell(last);
    let best: [number, number] = [0, 0];
    let bestDist = Infinity;
    for (let i = 0; i < this.pos.n * this.pos.n; i++) {
      if (this.pos.occupied(i)) continue;
      const [r, c] = this.pos.cell(i);
      const dist = Math.abs(r - lr) + Math.abs(c - lc);
      if (dist < bestDist) {
        bestDist = dist;
        best = [r, c];
      }
    }
    return best;
  }

  private afterMoves(): void {
    this.paintThreats();
    this.paintLine();
    this.renderMoves();
    if (!this.over && !this.demoTimer) {
      this.status(this.pos.p1ToMove() ? "" : "your move");
    }
    history.replaceState(
      null,
      "",
      `?g=${encodeGame(this.pos.n, this.pos.history)}&s=${this.wanted}`,
    );
  }

  /** The segmented control: the playing strategy pressed, both disabled
   * below 6 x 6 with a hint saying why. */
  private paintStrategy(): void {
    const playing = this.strategy();
    const small = this.pos.n < 6;
    for (const b of this.querySelectorAll<HTMLButtonElement>(
      ".sag-strategy button",
    )) {
      b.setAttribute("aria-pressed", String(b.dataset["strategy"] === playing));
      b.disabled = small;
    }
    this.querySelector<HTMLElement>(".sag-strategy-hint")!.textContent = small
      ? this.pos.n === 5
        ? "the rule applies from 6 × 6; the 5 × 5 table plays here"
        : "below 5 × 5 the game is drawn; a never-losing policy plays"
      : "";
  }

  /** The rule's committed line, if the rule is playing and has one. */
  private currentLine(): Line | null {
    if (this.strategy() !== "plus") return null;
    return lineOf(this.pos);
  }

  /** Mark the line's cells on the board: pending tempo moves and arms,
   * the plus's centre, and the latent corner the rule never surrenders;
   * and lay the line out as chips in the explainer. */
  private paintLine(): void {
    const layer = this.svg.querySelector(".sag-marks")!;
    layer.innerHTML = "";
    const plan = this.querySelector<HTMLElement>(".sag-plan")!;
    const line = this.currentLine();
    if (line === null || this.over) {
      plan.hidden = true;
      return;
    }
    const held = (cell: [number, number]) =>
      this.pos.p1.has(this.pos.idx(cell));
    const nextIdx = line.cells.findIndex((c) => !held(c));
    const mark = (cell: [number, number], kind: string) => {
      const [r, c] = cell;
      if (this.pos.occupied(this.pos.idx(cell)) && kind !== "hot") return;
      const rect = document.createElementNS(NS, "rect");
      rect.setAttribute("x", String(c * U + 2.5));
      rect.setAttribute("y", String(r * U + 2.5));
      rect.setAttribute("width", String(U - 5));
      rect.setAttribute("height", String(U - 5));
      rect.setAttribute("class", `sag-mark sag-mark-${kind}`);
      layer.appendChild(rect);
    };
    line.cells.forEach((cell, k) => {
      mark(cell, k === nextIdx ? "next" : k < line.tempo ? "tempo" : "arm");
    });
    mark(line.centre, "centre");
    const hot = this.hotCell();
    if (hot) mark(hot, "hot");

    plan.hidden = false;
    const chips = this.querySelector<HTMLElement>(".sag-chips")!;
    chips.innerHTML = "";
    line.cells.forEach((cell, k) => {
      const chip = document.createElement("span");
      const kind = k < line.tempo ? "tempo" : "arm";
      const state = held(cell) ? "held" : k === nextIdx ? "next" : "pending";
      chip.className = `sag-chip sag-chip-${kind} sag-chip-${state}`;
      chip.textContent = fmt(cell);
      chip.title = `${kind === "tempo" ? "tempo move" : "arm"}, ${state}`;
      chips.appendChild(chip);
    });
    const tempo = line.tempo;
    const parts = [
      tempo > 0
        ? `${tempo} tempo ${tempo === 1 ? "move" : "moves"}, then the`
        : "the",
      `side-${line.side} plus at ${fmt(line.centre)}`,
    ];
    if (hot)
      parts.push(`· latent corner ${fmt(hot)}, never offered as a block`);
    this.querySelector<HTMLElement>(".sag-plan-note")!.textContent =
      parts.join(" ");
  }

  private hotCell(): [number, number] | null {
    const d = botDecision(this.pos, "plus");
    return "hot" in d
      ? ((d as { hot: [number, number] | null }).hot ?? null)
      : null;
  }

  /** The move log with the bot's reasons, rebuilt from the history so
   * that undo and shared links show the same text as live play; the
   * latest bot move also heads the explainer. */
  private renderMoves(): void {
    const list = this.querySelector<HTMLOListElement>(".sag-moves")!;
    list.innerHTML = "";
    const replay = new Position(this.pos.n);
    const strategy = this.strategy();
    let latest = "";
    this.pos.history.forEach((i) => {
      const [r, c] = replay.cell(i);
      const item = document.createElement("li");
      const who = document.createElement("span");
      who.className = "sag-who";
      const text = document.createElement("span");
      if (replay.p1ToMove()) {
        let reason = "";
        try {
          const d = botDecision(replay, strategy);
          if (d.move && d.move[0] === r && d.move[1] === c)
            reason = d.reason ?? d.source;
        } catch {
          reason = "";
        }
        who.textContent = "bot";
        text.textContent = reason ? `${fmt([r, c])}: ${reason}` : fmt([r, c]);
        latest = `bot ${text.textContent}`;
        item.className = "sag-move-bot";
      } else {
        who.textContent = "you";
        text.textContent = fmt([r, c]);
        item.className = "sag-move-you";
      }
      item.append(who, text);
      list.appendChild(item);
      replay.play([r, c]);
    });
    if (list.lastElementChild)
      list.lastElementChild.classList.add("sag-move-last");
    this.querySelector<HTMLElement>(".sag-now-text")!.textContent = latest;
    this.querySelector<HTMLElement>(".sag-log summary")!.textContent =
      `move log (${this.pos.history.length})`;
  }

  private status(text: string): void {
    this.querySelector(".sag-status")!.textContent = text;
  }
}

customElements.define("sag-board", SagBoard);
