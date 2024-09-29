"use strict";

// ♤♡♢♧♠♥♦♣

/** @type {string[]} */
const RANK_MAP = ["A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K"];

/** @type {string[]} */
const SUIT_MAP = ["♡", "♢", "♧", "♤"];

/** @type {number} */
export const N_SUITS = SUIT_MAP.length;

/** @type {number} */
export const N_RANKS = RANK_MAP.length;

/** @type {number} */
export const KING_RANK = N_RANKS - 1;

/** @type {number} */
export const N_CARDS = N_SUITS * N_RANKS;

/**
 * @param {number} rank
 * @param {number} suit
 * @returns {number}
 */
export function cardId(rank, suit) {
  return rank * N_SUITS + suit;
}

/**
 * @typedef {Object} CardObject
 * @property {number} rank
 * @property {number} suit
 */

/**
 * @param {Card} c
 * @returns {string}
 */
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

export function getOffsetRect(el) {
  const rect = el.getBoundingClientRect();

  // add window scroll position to get the offset position
  const left = rect.left + window.scrollX;
  const top = rect.top + window.scrollY;
  const right = rect.right + window.scrollX;
  const bottom = rect.bottom + window.scrollY;

  // width and height are the same
  const width = rect.width;
  const height = rect.height;

  return { left, top, right, bottom, width, height };
}

export class CardPlace {
  constructor(element, offset, dirX, placeId) {
    element.dataset.placeId = placeId;

    this.element = element;
    this.offset = offset / 100;
    this.dirX = dirX;
    this.placeId = placeId;
  }

  getPos(el) {
    const boundBox = getOffsetRect(this.element);
    const bound = getOffsetRect(el);
    const nChild = this.element.childElementCount;
    const offset = this.offset * nChild;

    const x = (boundBox.left - bound.left) / bound.width + (this.dirX ? offset : 0);
    const y = (boundBox.top - bound.top) / bound.height + (!this.dirX ? offset : 0);

    return [x, y];
  }

  getSelfPos() {
    return this.getPos(this.element);
  }

  get last() {
    return this.element.lastChild || this.element;
  }
}

export class Card {
  /** @type {number} */
  #rank;

  /** @type {number} */
  #suit;

  /** @type {boolean} */
  #flipped;

  /** @type {boolean} */
  #draggable;

  /** @type {boolean} */
  #animating;

  /** @type {HTMLElement | null} */
  #element;

  /**
   * @param {number} rank
   * @param {number} suit
   */
  constructor(rank, suit) {
    this.#rank = rank;
    this.#suit = suit;
    this.#flipped = false;
    this.#draggable = true;
    this.#animating = false;
    this.#element = null;
  }

  /** @returns {number} */
  get id() {
    return cardId(this.#rank, this.#suit);
  }

  /** @returns {number} */
  get rank() {
    return this.#rank;
  }

  /** @returns {number} */
  get suit() {
    return this.#suit;
  }

  /** @returns {boolean} */
  get animating() {
    return this.#animating;
  }

  /** @returns {HTMLElement | null} */
  get element() {
    return this.#element;
  }

  /** @returns {HTMLElement | null} */
  get container() {
    return this.#element ? this.#element.parentElement : null;
  }

  /**
   * @param {boolean} val
   */
  set draggable(val) {
    this.#draggable = val;
  }

  /** @returns {number | null} */
  get placeId() {
    if (this.#element === null) return null;
    return parseInt(this.container.dataset.placeId);
  }

  deleteDOM() {
    if (this.#element === null) return;
    this.#element.remove();
    this.#element = null;
  }

  moveToFront() {
    if (this.#element === null) return;
    this.container?.appendChild(this.#element);
  }

  /**
   * @param {CardPlace} place
   * @param {number} posX
   * @param {number} posY
   */
  createDOM(place, prepend) {
    if (this.#element !== null) return;
    const cardElement = document.createElement("div");
    cardElement.className = "card";
    cardElement.innerHTML = `<div class="card_inner">
      <div class="card_back"></div>
      ${createCardSVG(this)}
    </div>`;
    const inner = cardElement.firstElementChild;
    if (inner && this.#flipped) inner.classList.add("flipped");

    cardElement.dataset.cardId = this.id.toString();
    // cardElement.addEventListener("transitionrun", (_) => {
    //   this.#animating = true;
    // });
    // const doneAnimate = (_) => {
    //   cardElement.style.removeProperty("transition");
    //   this.#animating = false;
    // };
    // cardElement.addEventListener("transitioncancel", doneAnimate);
    // cardElement.addEventListener("transitionend", doneAnimate);

    if (prepend) {
      cardElement.style.left = "0%";
      cardElement.style.top = "0%";
      place.element.prepend(cardElement);
    } else {
      const [posX, posY] = place.getSelfPos();
      cardElement.style.left = `${posX * 100}%`;
      cardElement.style.top = `${posY * 100}%`;
      place.element.append(cardElement);
    }

    this.#element = cardElement;
  }

  /**
   * @param {number} duration
   */
  turnUp(duration) {
    if (this.#flipped) {
      this.flipCard(duration);
    }
  }

  /**
   * @param {number} duration
   */
  flipCard(duration) {
    this.#flipped = !this.#flipped;
    if (this.#element === null) return;
    const inner = this.#element.firstElementChild;
    if (inner) inner.classList.toggle("flipped");
  }

  /**
   * @param {CardPlace} container
   * @param {number | null} posX
   * @param {number | null} posY
   * @param {number} duration
   */
  moveTo(place, animation) {
    if (this.#element === null || place === null || place.element === this.container) return;

    const [posX, posY] = place.getSelfPos();
    // console.log("meo", posX, posY);

    // if (duration > 0) this.#element.style.transition = `top ${duration}ms ease-in, left ${duration}ms ease-in`;
    this.#element.style.left = `${posX * 100}%`;
    this.#element.style.top = `${posY * 100}%`;

    if (animation) {
      const [curX, curY] = place.getPos(this.#element);
      this.#element.style.transform = `translate(-${curX * 100}%,-${curY * 100}%)`;
    }

    place.element.appendChild(this.#element);

    if (animation) {
      requestAnimationFrame(() => {
        this.#element.style.transition = `transform ${animation}ms ease-in`;
        this.#element.style.transform = "";
      });
    }
  }

  /** @returns {boolean} */
  isDraggable() {
    return this.#draggable && !this.#animating;
  }

  /**
   * @param {Card} card
   * @returns {boolean}
   */
  goBefore(card) {
    return this.#rank === card.#rank + 1 && (((this.#suit ^ card.#suit) & 2) === 2 || this.#rank === N_RANKS);
  }
}
