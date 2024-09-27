"use strict";
import { N_SUITS, cardId, Card, N_RANKS } from "./Card.js";

export const N_PILES = 7;
export const N_HIDDEN_CARDS = (N_PILES * (N_PILES + 1)) / 2;

export class Deck {
  constructor(cards, drawStep) {
    if (!Array.isArray(cards)) throw new Error("Cards must be an array");
    if (typeof drawStep !== "number" || drawStep <= 0) throw new Error("Draw step must be a positive number");

    this._stock = cards;
    this._waste = [];
    this._drawStep = drawStep;
  }

  peek(n) {
    const len = this._waste.length;
    const start = Math.max(len - n, 0);
    return this._waste.slice(start, len);
  }

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

export const Pos = {
  Deck: 0,
  Stack: 1,
  Pile: 1 + N_SUITS,
  None: -1,
};

export class Solitaire {
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

    this.findOrigin = (card) => {
      if (this.deck.peek(1).some((c) => c.id === card.id)) {
        return Pos.Deck;
      }
      const stackIndex = this.stack.findIndex((rank, suit) => cardId(rank - 1, suit) === card.id);
      if (stackIndex !== -1) {
        return Pos.Stack + stackIndex;
      }
      const pileIndex = this.piles.findIndex((pile) => pile.some((c) => c.id === card.id));
      if (pileIndex !== -1) {
        return Pos.Pile + pileIndex;
      }
      return Pos.None;
    };

    this.liftCard = (cards) => {
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
    };

    this.makeMove = (card, src, dst) => {
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
    };
  }
}
