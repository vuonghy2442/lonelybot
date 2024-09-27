"use strict";

// ♤♡♢♧♠♥♦♣

const RANK_MAP = ["A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K"];
const SUIT_MAP = ["♡", "♢", "♧", "♤"];

export const N_SUITS = SUIT_MAP.length;
export const N_RANKS = RANK_MAP.length;

export const KING_RANK = N_RANKS - 1;
export const N_CARDS = N_SUITS * N_RANKS;

export function cardId(rank, suit) {
  return rank * N_SUITS + suit;
}

function createCardSVG(c) {
  const rank_str = RANK_MAP[c.rank];
  const suit_str = SUIT_MAP[c.suit];
  const color = c.suit < 2 ? "#e22" : "#001";

  return `<svg xmlns="http://www.w3.org/2000/svg" class="card_front" fill="${color}" viewBox="0 0 250 350">
    <g font-size="45">
      <text x="5%" y="50">${rank_str}</text>
      <text x="5%" y="95">${suit_str}</text>
    </g>
    <text x="50%" y="50%" dominant-baseline="middle" text-anchor="middle" font-size="150">${rank_str}</text>
    <g font-size="45" transform="rotate(180 125 175)">
      <text x="5%" y="50">${rank_str}</text>
      <text x="5%" y="95">${suit_str}</text>
    </g>
  </svg>`;
}

let front_element = null;

export class Card {
  #rank;
  #suit;
  #flipped;
  #draggable;
  #animating;
  #element;

  constructor(rank, suit) {
    if (typeof rank !== "number" || rank < 0 || rank > N_RANKS) throw new Error("Invalid rank");
    if (typeof suit !== "number" || suit < 0 || suit >= N_SUITS) throw new Error("Invalid suit");

    this.#rank = rank;
    this.#suit = suit;
    this.#flipped = false;
    this.#draggable = true;
    this.#animating = false;
    this.#element = null;
  }

  get id() {
    return cardId(this.#rank, this.#suit);
  }

  get rank() {
    return this.#rank;
  }

  get suit() {
    return this.#suit;
  }

  get animating() {
    return this.#animating;
  }

  get element() {
    return this.#element;
  }

  get container() {
    return this.#element.parentElement;
  }

  /**
   * @param {boolean} val
   */
  set draggable(val) {
    this.#draggable = val;
  }

  deleteDOM() {
    if (this.#element === null) return;
    this.#element.remove();
    this.#element = null;
  }

  moveToFront() {
    if (this.#element === null) return;
    this.container.appendChild(this.#element);
  }

  containerToFront() {
    if (this.#element === null) return;
    if (front_element !== null) front_element.style.zIndex = 0;
    this.container.style.zIndex = 1;
    front_element = this.container;
  }

  createDOM(container, posX, posY) {
    if (this.#element !== null) return;
    const cardElement = document.createElement("div");
    cardElement.className = "card";
    cardElement.innerHTML = `<div class="card_inner">
      <div class="card_back"></div>
      ${createCardSVG(this)}
    </div>`;
    const inner = cardElement.firstElementChild;
    if (this.#flipped) inner.classList.add("flipped");

    cardElement.style.left = `${posX}%`;
    cardElement.style.top = `${posY}%`;
    cardElement.dataset.cardId = this.id;

    cardElement.addEventListener("transitionrun", (_) => {
      this.#animating = true;
    });

    const doneAnimate = (_) => {
      cardElement.style.removeProperty("transition");
      this.#animating = false;
    };

    cardElement.addEventListener("transitioncancel", doneAnimate);
    cardElement.addEventListener("transitionend", doneAnimate);

    container.appendChild(cardElement);
    this.#element = cardElement;
  }

  turnUp(duration) {
    if (this.#flipped) {
      this.flipCard(duration);
    }
  }

  flipCard(duration) {
    this.#flipped = !this.#flipped;
    if (this.#element === null) return;
    const inner = this.#element.firstElementChild;
    inner.classList.toggle("flipped");
  }

  moveTo(container, posX, posY, duration) {
    if (this.#element === null) return;
    const sameContainer = container === null || container === this.container;
    let currentLeft = parseFloat(this.#element.style.left) || 0;
    let currentTop = parseFloat(this.#element.style.top) || 0;

    if (sameContainer && Math.abs(currentLeft - posX) < 1e-2 && Math.abs(currentTop - posY) < 1e-2) {
      return;
    }

    if (duration > 0) this.#element.style.transition = `top ${duration}ms ease-in, left ${duration}ms ease-in`;
    if (posX !== null) this.#element.style.left = `${posX}%`;
    if (posY !== null) this.#element.style.top = `${posY}%`;
    if (!sameContainer) {
      const parent = this.container;
      parent.removeChild(this.#element);
      container.appendChild(this.#element);
    }
  }

  isDraggable() {
    return this.#draggable && !this.#animating;
  }

  goBefore(card) {
    if (typeof card !== "object" || !(card instanceof Card)) throw new Error("Invalid card");
    return this.#rank === card.#rank + 1 && (((this.#suit ^ card.#suit) & 2) === 2 || this.#rank === N_RANKS);
  }
}
