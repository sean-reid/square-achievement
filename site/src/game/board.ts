/** The interactive board: an SVG figure in the paper's own idiom.
 *
 * The visitor plays O against the table strategy's X. Hairline rules,
 * drawn stones, threat washes, a winning square that draws itself in,
 * a move list with the strategy's stated reasons, undo, a shareable
 * link, and a self-playing demonstration. Motion is subtle and
 * respects prefers-reduced-motion.
 */

import { Position, threats, winningSquare } from "./rules";
import { botDecision } from "./bot";
import { decodeGame, encodeGame } from "./url";

const U = 10; // svg units per cell
const NS = "http://www.w3.org/2000/svg";

export class SagBoard extends HTMLElement {
  private pos = new Position(5);
  private over = false;
  private showThreats = false;
  private demoTimer: ReturnType<typeof setInterval> | null = null;
  private svg!: SVGSVGElement;

  connectedCallback(): void {
    const fromUrl = new URLSearchParams(location.search).get("g");
    const decoded = fromUrl ? decodeGame(fromUrl) : null;
    const n = decoded?.n ?? Number(this.getAttribute("n") ?? "5");
    this.buildShell(n);
    this.newGame(n, decoded?.history);
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
      <div class="sag-stage"></div>
      <p class="sag-status" role="status"></p>
      <p class="sag-quiet">
        <button class="sag-undo">undo</button> ·
        <label class="sag-toggle"><input type="checkbox" class="sag-th"> threats</label> ·
        <button class="sag-share">share</button> ·
        <button class="sag-demo">demo</button>
      </p>`;
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
    this.querySelector<HTMLInputElement>(".sag-th")!.addEventListener(
      "change",
      (e) => {
        this.showThreats = (e.target as HTMLInputElement).checked;
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
    this.pos = new Position(n);
    this.over = false;
    this.querySelector(".sag-size")!.textContent = `${n} × ${n}`;
    this.buildSvg();
    if (n < 5) this.status("boards below 5 x 5 are drawn with best play");
    if (replay && replay.length > 0) {
      for (const i of replay) {
        if (this.over) break;
        const [r, c] = this.pos.cell(i);
        this.commit([r, c]);
      }
    } else {
      this.botTurn();
    }
    this.afterMoves();
  }

  private buildSvg(): void {
    const n = this.pos.n;
    const size = n * U;
    this.svg = document.createElementNS(NS, "svg");
    this.svg.setAttribute("viewBox", `-1 -1 ${size + 2} ${size + 2}`);
    this.svg.setAttribute("class", "sag-svg");
    const stage = this.querySelector(".sag-stage")!;
    stage.innerHTML = "";
    stage.appendChild(this.svg);
    for (const name of ["threats", "grid", "stones", "marks", "win", "cells"]) {
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
      rect.addEventListener("click", () => this.humanPlay(i));
      cells.appendChild(rect);
    }
  }

  private stoneNode(i: number, first: boolean): SVGElement {
    const [r, c] = this.pos.cell(i);
    const cx = c * U + U / 2;
    const cy = r * U + U / 2;
    const g = document.createElementNS(NS, "g");
    g.setAttribute("class", first ? "sag-stone sag-x" : "sag-stone sag-o");
    g.setAttribute("data-stone", String(i));
    if (first) {
      const d = U * 0.26;
      for (const s of [1, -1]) {
        const line = document.createElementNS(NS, "line");
        line.setAttribute("x1", String(cx - d));
        line.setAttribute("y1", String(cy - d * s));
        line.setAttribute("x2", String(cx + d));
        line.setAttribute("y2", String(cy + d * s));
        g.appendChild(line);
      }
    } else {
      const circle = document.createElementNS(NS, "circle");
      circle.setAttribute("cx", String(cx));
      circle.setAttribute("cy", String(cy));
      circle.setAttribute("r", String(U * 0.3));
      g.appendChild(circle);
    }
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
          ? "X completes a square: the strategy wins."
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

  private botTurn(): void {
    if (this.over || this.pos.full()) return;
    const d = botDecision(this.pos);
    if (d.move === null) {
      this.over = true;
      this.status("this position is outside the table's verified range");
      return;
    }
    this.commit(d.move);
  }

  private humanPlay(i: number): void {
    if (this.over || this.demoTimer || this.pos.p1ToMove()) return;
    if (this.pos.occupied(i)) return;
    const [r, c] = this.pos.cell(i);
    this.commit([r, c]);
    if (!this.over) this.botTurn();
    this.afterMoves();
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
      if (this.pos.p1ToMove()) this.botTurn();
      else this.commit(this.demoReply());
      this.afterMoves();
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
    if (!this.over && !this.demoTimer) {
      this.status(this.pos.p1ToMove() ? "" : "your move");
    }
    history.replaceState(
      null,
      "",
      `?g=${encodeGame(this.pos.n, this.pos.history)}`,
    );
  }

  private status(text: string): void {
    this.querySelector(".sag-status")!.textContent = text;
  }
}

customElements.define("sag-board", SagBoard);
