"use strict";

import { Card, N_CARDS, N_SUITS, N_RANKS, cardId } from "./Card.js";
import { Solitaire, N_PILES, Pos } from "./Solitaire.js";

window.onload = initGame;

const UP_SPACE = 15;
const DOWN_SPACE = 10;
const DEAL_SPACE = 25;

const ANIMATION_TIME = 100;
const OFFSET_TIME = 100;
const REVEAL_TIME = 300;

const getOffsetRect = (el) => {
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
};

function initCards() {
  // creating cards
  const cardArray = new Array(N_CARDS);

  for (let rank = 0; rank < N_RANKS; ++rank) {
    for (let suit = 0; suit < N_SUITS; ++suit) {
      const c = new Card(rank, suit);
      cardArray[c.id] = c;
    }
  }

  function shuffleArray(array) {
    for (let i = array.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      [array[i], array[j]] = [array[j], array[i]];
    }
  }

  const shuffledCards = [...cardArray];
  shuffleArray(shuffledCards);
  return [cardArray, new Solitaire(shuffledCards, 3)];
}

const [cardArray, game] = initCards();

function getCard(rank, suit) {
  return cardArray[cardId(rank, suit)];
}

const THRESHOLD = 0.4;
const THRESHOLD_2 = THRESHOLD * THRESHOLD;

const snap_audio = new Audio("sound/snap.mp3");

const tableauContainers = [...document.querySelectorAll(".tableau")];
const stackContainers = [...document.querySelectorAll(".stack")];
const dealContainer = document.querySelector("#deal");
const wasteContainer = document.querySelector("#waste");

class CardPlace {
  constructor(element, offset, dirX, placeId) {
    element.dataset.placeId = placeId;

    this.element = element;
    this.offset = offset / 100;
    this.dirX = dirX;
    this.boundBox = getOffsetRect(element);
    this.placeId = placeId;
  }

  getPos(el) {
    const bound = getOffsetRect(el);
    const last = getOffsetRect(this.element.lastChild || this.element);

    const x = (last.left - bound.left) / bound.width + (this.element.lastChild && this.dirX ? this.offset : 0);
    const y = (last.top - bound.top) / bound.height + (this.element.lastChild && !this.dirX ? this.offset : 0);

    return [x, y];
  }
}

const cardPlaces = [
  new CardPlace(wasteContainer, DEAL_SPACE, true, 0),
  ...stackContainers.map((s, idx) => new CardPlace(s, 0, false, Pos.Stack + idx)),
  ...tableauContainers.map((s, idx) => new CardPlace(s, UP_SPACE, false, Pos.Pile + idx)),
];

// Helper function to initialize piles
function initializePiles() {
  for (let i = 0; i < N_PILES; ++i) {
    const hidden = game.hiddenPiles[i];
    const cont = tableauContainers[i];
    for (let j = 0; j < hidden.length; ++j) {
      hidden[j].flipCard();
      hidden[j].draggable = false;
      hidden[j].createDOM(cont, 0, DOWN_SPACE * j);
    }
    const visible = game.piles[i];
    for (let j = 0; j < visible.length; ++j) {
      visible[j].draggable = j + 1 == visible.length;
      visible[j].createDOM(cont, 0, DOWN_SPACE * hidden.length + UP_SPACE * j);
    }
  }
}

let wasteCards = [];

function handleDealEvent() {
  for (const c of wasteCards) {
    c.deleteDOM();
  }

  wasteCards = game.deck.peek(3);

  for (const [pos, c] of wasteCards.entries()) {
    c.draggable = false;
    c.flipCard();

    c.createDOM(dealContainer, 0, 0);
    c.moveToFront();

    setTimeout(() => {
      c.flipCard(ANIMATION_TIME);
      c.moveTo(wasteContainer, pos * DEAL_SPACE, 0, ANIMATION_TIME);
      if (pos + 1 == wasteCards.length) {
        c.draggable = true;
      }
    }, OFFSET_TIME * pos);
  }
}

function handlePushStackEvent(card) {
  card.moveToFront();

  if (card.rank >= 2) {
    getCard(card.rank - 2, card.suit).deleteDOM();
  }

  if (card.rank > 0) {
    getCard(card.rank - 1, card.suit).draggable = false;
  }
}

function handlePopStackEvent(card) {
  if (card.rank >= 2) {
    const c = getCard(card.rank - 2, card.suit);
    c.turnUp();
    c.draggable = false;
    c.createDOM(stackContainers[card.suit], 0, 0);
    getCard(card.rank - 1, card.suit).moveToFront();
  }

  if (card.rank > 0) {
    getCard(card.rank - 1, card.suit).draggable = true;
  }
}

function handlePopDeckEvent() {
  wasteCards.pop();
  if (wasteCards.length <= 1) {
    // append new stuff
    wasteCards = game.deck.peek(wasteCards.length + 1);

    if (wasteCards.length > 0) {
      wasteCards[0].draggable = false;
      wasteCards[0].turnUp();
      wasteCards[0].createDOM(wasteContainer, 0, 0);
    }

    for (const c of wasteCards) {
      c.moveToFront();
    }
  }

  if (wasteCards.length > 0) {
    wasteCards[wasteCards.length - 1].draggable = true;
  }
}

let handlingMove = false;

function moveCard(event, card) {
  const origin_cont = card.container;
  const origin = parseInt(origin_cont.dataset.placeId);

  let moving_cards = [card];

  if (origin >= Pos.Pile) {
    const p = game.piles[origin - Pos.Pile];
    const id = p.findIndex((c) => c.id == card.id);
    moving_cards = p.slice(id);
  }

  if (moving_cards.some((c) => !c.isDraggable())) return;
  snap_audio.play();

  card.containerToFront();

  const dropPos = game.liftCard(moving_cards).map((p) => [cardPlaces[p], cardPlaces[p].getPos(origin_cont)]);

  const cont_bound = getOffsetRect(origin_cont);
  const card_bound = getOffsetRect(card.element);

  const offsetX = (event.pageX - card_bound.left) / cont_bound.width;
  const offsetY = (event.pageY - card_bound.top) / cont_bound.height;

  const initialX = (card_bound.left - cont_bound.left) / cont_bound.width;
  const initialY = (card_bound.top - cont_bound.top) / cont_bound.height;

  let snapped = null;

  function distance2(x, y, u, v) {
    const [dx, dy] = [x - u, y - v];
    return dx * dx + dy * dy;
  }

  function findNear(x, y) {
    for (const [place, pos] of dropPos) {
      if (distance2(x, y, ...pos) < THRESHOLD_2) {
        return [place, pos];
      }
    }
    return [null, null];
  }

  function handlePointerMove(event) {
    if (!event.isPrimary) return;

    const x = (event.pageX - cont_bound.left) / cont_bound.width - offsetX;
    const y = (event.pageY - cont_bound.top) / cont_bound.height - offsetY;

    const [place, pos] = findNear(x, y);

    if (place !== null) {
      snapped = place;
      const [u, v] = pos;

      moving_cards.forEach((c, idx) => c.moveTo(null, u * 100, v * 100 + idx * UP_SPACE, 100));
    } else if (snapped !== null) {
      snapped = null;
      moving_cards.forEach((c, idx) => c.moveTo(null, x * 100, y * 100 + idx * UP_SPACE, 100));
    } else {
      moving_cards.forEach((c, idx) => {
        if (!c.animating) c.moveTo(null, x * 100, y * 100 + idx * UP_SPACE, 0);
      });
    }
  }

  function handlePointerCancel() {
    snapped = null;
    handlePointerUp();
  }

  function handlePointerUp() {
    window.removeEventListener("pointermove", handlePointerMove);
    window.removeEventListener("pointerup", handlePointerUp);
    window.removeEventListener("pointercancel", handlePointerCancel);

    // Implement card snapping or other dragging behavior
    if (snapped === null) {
      moving_cards.forEach((c, idx) =>
        c.moveTo(null, initialX * 100, initialY * 100 + idx * UP_SPACE, ANIMATION_TIME + 10 * idx)
      );
    } else {
      moving_cards.forEach((c) => {
        const [x, y] = snapped.getPos(snapped.element);
        c.moveTo(snapped.element, 100 * x, 100 * y, 0);
      });
      game.makeMove(card, origin, snapped.placeId);
      snapped = null;
    }
    handlingMove = false;
  }

  handlingMove = true;

  window.addEventListener("pointermove", handlePointerMove);
  window.addEventListener("pointerup", handlePointerUp);
  window.addEventListener("pointercancel", handlePointerCancel);
}

function onPointerDown(event) {
  if (event.which !== 1 || !event.isPrimary || handlingMove) return;

  const cardDOM = event.target.closest(".card");

  if (cardDOM) {
    const card = cardArray[parseInt(cardDOM.dataset.cardId)];
    moveCard(event, card);
    // some how it fix the default stuff :))
    event.preventDefault();
    return;
  }

  if (event.target.closest("#deal")) {
    game.makeMove(null, 0, 0);
    event.preventDefault();
    return;
  }
}

function initGame() {
  // Initialize piles
  initializePiles();

  game.onDealCallbacks.push(handleDealEvent);
  game.onPushStackCallbacks.push(handlePushStackEvent);
  game.onPopStackCallbacks.push(handlePopStackEvent);
  game.onPopDeckCallbacks.push(handlePopDeckEvent);
  game.onRevealCallbacks.push((_, card) => {
    card.draggable = true;
    card.turnUp(REVEAL_TIME);
  });

  document.querySelector("#game_box").addEventListener("pointerdown", onPointerDown);
}
