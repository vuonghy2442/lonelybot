"use strict";
import { N_SUITS, Card, N_RANKS } from "./Card.js";

/** @type {number} */
export const N_PILES = 7;

/** @type {number} */
export const N_HIDDEN_CARDS = (N_PILES * (N_PILES + 1)) / 2;

export class Deck {
  /**
   * @param {Card[]} cards
   * @param {number} drawStep
   */
  constructor(cards, drawStep) {
    if (!Array.isArray(cards)) throw new Error("Cards must be an array");
    if (typeof drawStep !== "number" || drawStep <= 0) throw new Error("Draw step must be a positive number");

    this._stock = cards;
    this._waste = [];
    this._drawStep = drawStep;
  }

  /**
   * @param {number} n
   * @returns {Card[]}
   */
  peek(n) {
    const len = this._waste.length;
    const start = Math.max(len - n, 0);
    return this._waste.slice(start, len);
  }

  /**
   * @returns {Card}
   */
  pop() {
    return this._waste.pop();
  }

  deal() {
    if (this._stock.length === 0) {
      this._stock = this._waste;
      this._waste = [];
    } else {
      const removedCards = this._stock.splice(0, this._drawStep);
      this._waste.push(...removedCards);
    }
  }
}

/**
 * @typedef {Object} Pos
 * @property {number} Deck - The position of a card on the deck.
 * @property {number} Stack - The position of a card in a stack (e.g., tableau).
 * @property {number} Pile - The position of a card in a pile which is offset by N_SUITS.
 * @property {number} None - Indicates no specific position or an invalid/null position.
 */
export const Pos = {
  Deck: 0,
  Stack: 1,
  Pile: 1 + N_SUITS,
  None: -1,
};

export class Solitaire {
  /**
   * Creates an instance of Solitaire.
   * @param {Array<Card>} cards - The array of all cards in the deck including hidden ones.
   * @param {number} drawStep - The number of cards to deal from the top of the deck at each step.
   */
  constructor(cards, drawStep) {
    const hiddenCards = cards.slice(0, N_HIDDEN_CARDS);

    this.piles = Array.from({ length: N_PILES }, (_, i) => {
      return [hiddenCards[((i + 2) * (i + 1)) / 2 - 1]];
    });

    this.hiddenPiles = Array.from({ length: N_PILES }, (_, i) => {
      return hiddenCards.slice(((i + 1) * i) / 2, ((i + 2) * (i + 1)) / 2 - 1);
    });

    this.deck = new Deck(cards.slice(N_HIDDEN_CARDS), drawStep);
    this.stack = Array.from({ length: N_SUITS }, () => 0);

    this.onDealCallbacks = [];
    this.onPopDeckCallbacks = [];
    this.onPopStackCallbacks = [];
    this.onPushStackCallbacks = [];
    this.onRevealCallbacks = [];
  }

  /**
   * Determines which positions cards can move to based on game rules.
   * @param {Array<Card>} cards - The card(s) to check for movement possibilities.
   * @returns {Array<string>} Positions where the card(s) can be moved: 'Deck', 'Pile', or 'Stack'.
   */
  liftCard(cards) {
    const card = cards[0];
    const result = [];
    if (cards.length === 1 && this.stack[card.suit] === card.rank) {
      result.push(Pos.Stack + card.suit);
    }
    for (let i = 0; i < N_PILES; ++i) {
      const pile = this.piles[i];
      const lastCard = pile[pile.length - 1] || new Card(N_RANKS, 0);
      if (lastCard.goBefore(card)) {
        result.push(Pos.Pile + i);
      }
    }
    return result;
  }

  /**
   * Executes a move in the game based on source and destination positions.
   * @param {Card} card - The card to be moved.
   * @param {string} src - Source position ('Deck', 'Pile', or 'Stack').
   * @param {string} dst - Destination position ('Deck', 'Pile', or 'Stack').
   */
  makeMove(card, src, dst) {
    if (src === Pos.Deck && dst === Pos.Deck) {
      this.deck.deal();
      this.onDealCallbacks.forEach((callback) => callback());
      return;
    }
    if (src === Pos.Deck) {
      const dealtCard = this.deck.pop();
      this.onPopDeckCallbacks.forEach((callback) => callback(dealtCard));
    } else if (src <= N_SUITS) {
      this.stack[src - 1] -= 1;
      this.onPopStackCallbacks.forEach((callback) => callback(card));
    }
    if (dst <= N_SUITS) {
      this.stack[dst - 1] += 1;
      this.onPushStackCallbacks.forEach((callback) => callback(card));
    }
    let cards = [card];

    if (src >= Pos.Pile) {
      src -= Pos.Pile;
      const cardIndex = this.piles[src].findIndex((c) => c.id === card.id);
      cards = this.piles[src].splice(cardIndex);
      if (this.piles[src].length === 0 && this.hiddenPiles[src].length > 0) {
        const lastHiddenCard = this.hiddenPiles[src].pop();
        this.piles[src].push(lastHiddenCard);
        this.onRevealCallbacks.forEach((callback) => callback(src, lastHiddenCard));
      }
    }
    if (dst >= Pos.Pile) {
      dst -= Pos.Pile;
      this.piles[dst].push(...cards);
    }
  }
}
