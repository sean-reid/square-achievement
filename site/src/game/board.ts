/** The interactive board, a dependency-free custom element.
 *
 * The visitor plays O against the bot's X. Skeleton scope: fixed-size
 * rendering suited to n up to ~15; the large-n viewport, threat
 * highlighting, history, and demo mode land with the verified table.
 */

import { Position, threats, winningSquare } from "./rules";
import { botMove, VERIFIED } from "./bot";

export class SagBoard extends HTMLElement {
  private pos = new Position(5);
  private status = "";
  private over = false;

  connectedCallback(): void {
    this.reset(Number(this.getAttribute("n") ?? "5"));
  }

  reset(n: number): void {
    this.pos = new Position(n);
    this.over = false;
    this.status = VERIFIED
      ? "You are O. The bot plays the machine-verified strategy."
      : "You are O. Preview bot; the verified strategy table lands soon.";
    if (n < 5) this.status += " Boards below 5x5 are drawn with best play.";
    this.botTurn();
    this.render();
  }

  private botTurn(): void {
    if (this.over || this.pos.full()) return;
    const move = botMove(this.pos);
    this.pos.play(move);
    const sq = winningSquare(this.pos, this.pos.p1, move);
    if (sq) {
      this.over = true;
      this.status = "The bot completed a square. P1 wins.";
    }
  }

  private humanPlay(r: number, c: number): void {
    if (this.over || !this.pos.onBoard([r, c])) return;
    if (this.pos.occupied(this.pos.idx([r, c]))) return;
    this.pos.play([r, c]);
    const sq = winningSquare(this.pos, this.pos.p2, [r, c]);
    if (sq) {
      this.over = true;
      this.status = "You completed a square. You win!";
    } else if (this.pos.full()) {
      this.over = true;
      this.status = "Board full: a draw.";
    } else {
      this.botTurn();
      if (!this.over && this.pos.full()) {
        this.over = true;
        this.status = "Board full: a draw.";
      }
    }
    this.render();
  }

  private render(): void {
    const n = this.pos.n;
    const cellPx = Math.min(44, Math.floor(352 / n));
    let cells = "";
    for (let r = 0; r < n; r++) {
      for (let c = 0; c < n; c++) {
        const i = r * n + c;
        const mark = this.pos.p1.has(i) ? "X" : this.pos.p2.has(i) ? "O" : "";
        cells += `<button class="sag-cell" data-r="${r}" data-c="${c}"
          style="width:${cellPx}px;height:${cellPx}px"
          ${mark || this.over ? "disabled" : ""}>${mark}</button>`;
      }
    }
    this.innerHTML = `
      <div class="sag-controls">
        <label>n = <input type="number" min="2" max="25" value="${n}" class="sag-n"></label>
        <button class="sag-reset">new game</button>
      </div>
      <div class="sag-grid" style="grid-template-columns:repeat(${n},${cellPx}px)">${cells}</div>
      <p class="sag-status" role="status">${this.status}</p>`;
    this.querySelectorAll<HTMLButtonElement>(
      ".sag-cell:not([disabled])",
    ).forEach((b) =>
      b.addEventListener("click", () =>
        this.humanPlay(Number(b.dataset["r"]), Number(b.dataset["c"])),
      ),
    );
    this.querySelector<HTMLButtonElement>(".sag-reset")?.addEventListener(
      "click",
      () => {
        const n2 = Number(
          this.querySelector<HTMLInputElement>(".sag-n")?.value ?? "5",
        );
        this.reset(Math.max(2, Math.min(25, n2)));
      },
    );
  }
}

customElements.define("sag-board", SagBoard);

export { threats };
