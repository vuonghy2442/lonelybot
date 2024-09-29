"use strict";

import { Card, CardPlace, getOffsetRect, N_CARDS, N_SUITS, N_RANKS, cardId } from "./Card.js";
import { Solitaire, N_PILES, Pos } from "./Solitaire.js";

window.onload = initGame;

const UP_SPACE = 15;
const DEAL_SPACE = 25;

const ANIMATION_TIME = 100;
const OFFSET_TIME = 100;
const REVEAL_TIME = 300;

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

const THRESHOLD = 1;
const THRESHOLD_2 = THRESHOLD * THRESHOLD;

const snap_audio = new Audio("sound/snap.mp3");

const tableauContainers = [...document.querySelectorAll(".tableau")];
const stackContainers = [...document.querySelectorAll(".stack")];
const wasteContainer = document.querySelector("#waste");

const wastePlace = new CardPlace(wasteContainer, DEAL_SPACE, true, 0);
const stackPlaces = stackContainers.map((s, idx) => new CardPlace(s, 0, false, Pos.Stack + idx));
const tableauPlaces = tableauContainers.map((s, idx) => new CardPlace(s, UP_SPACE, false, Pos.Pile + idx));

const cardPlaces = [wastePlace, ...stackPlaces, ...tableauPlaces];

class MovingPlace {
  constructor() {
    this.element = document.querySelector("#moving");
  }

  setMoving(el) {
    const rect = getOffsetRect(el);
    this.element.style.left = rect.left + "px";
    this.element.style.top = rect.top + "px";
    this.element.style.width = rect.width + "px";
    this.element.style.height = rect.height + "px";
    this.element.style.transform = "";
  }

  takeCards(cards) {
    if (cards.length == 0) return;

    this.setMoving(cards[0].container);
    cards.forEach((c) => this.element.append(c.element));
    this.cards = cards;
  }
  moveTo(x, y) {
    this.element.style.transform = `translate(${x * 100}%,${y * 100}%)`;
  }

  putCards(place) {
    this.cards.forEach((c) => {
      c.moveTo(place);
    });
  }
}

const mover = new MovingPlace();

// Helper function to initialize piles
function initializePiles() {
  for (let i = 0; i < N_PILES; ++i) {
    const hidden = game.hiddenPiles[i];
    const cont = tableauPlaces[i];
    for (let j = 0; j < hidden.length; ++j) {
      hidden[j].flipCard();
      hidden[j].draggable = false;
      hidden[j].createDOM(cont);
    }
    const visible = game.piles[i];
    for (let j = 0; j < visible.length; ++j) {
      visible[j].draggable = j + 1 == visible.length;
      visible[j].createDOM(cont);
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
    c.createDOM(wastePlace);
    if (pos + 1 == wasteCards.length) {
      c.draggable = true;
    }
  }
}

function handlePushStackEvent(card) {
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
    c.createDOM(stackPlaces[card.suit], true);
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
      wasteCards[0].createDOM(wastePlace, true);
    }
  }

  if (wasteCards.length > 0) {
    wasteCards[wasteCards.length - 1].draggable = true;
  }
}

let handlingMove = false;

function getMoving(card) {
  if (!card.isDraggable()) return [];

  const origin = card.placeId;
  let moving_cards = [card];

  if (origin >= Pos.Pile) {
    const p = game.piles[origin - Pos.Pile];
    const id = p.findIndex((c) => c.id == card.id);
    moving_cards = p.slice(id);
  }

  if (moving_cards.some((c) => !c.isDraggable())) return [];
  return moving_cards;
}

function moveCard(event, card) {
  const originContainer = card.container;
  const origin = card.placeId;
  const originPlace = cardPlaces[origin];

  const movingCards = getMoving(card);
  if (movingCards.length == 0) return;

  snap_audio.play();

  mover.takeCards(movingCards);

  const dropPos = game.liftCard(movingCards).map((p) => [cardPlaces[p], cardPlaces[p].getPos(originContainer)]);

  dropPos.forEach((p) => {
    p[0].last.classList.add("hinted");
  });

  const cont_bound = getOffsetRect(originContainer);

  const offsetX = event.pageX;
  const offsetY = event.pageY;

  let snapped = null;
  const startTime = new Date();

  function distance2(x, y, u, v) {
    const [dx, dy] = [x - u, y - v];
    return dx * dx + dy * dy;
  }

  function findNear(x, y) {
    for (const [place, pos] of dropPos) {
      if (distance2(x, y, ...pos) < THRESHOLD_2) {
        return place;
      }
    }
    return null;
  }

  function handlePointerMove(event) {
    if (!event.isPrimary) return;

    const x = (event.pageX - offsetX) / cont_bound.width;
    const y = (event.pageY - offsetY) / cont_bound.height;

    const place = findNear(x, y);

    if (snapped !== place) {
      snapped?.last.classList.remove("highlighted");
      place?.last.classList.add("highlighted");
    }

    snapped = place;

    mover.moveTo(x, y);
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
    snapped?.last.classList.remove("highlighted");

    dropPos.forEach((p) => {
      p[0].last.classList.remove("hinted");
    });

    handlingMove = false;

    const duration = new Date() - startTime;

    if (dropPos.length == 0 || (snapped === null && duration > 200)) {
      snapped = originPlace;
    } else if (snapped === null) {
      snapped = dropPos[0][0];
    }

    mover.putCards(snapped);

    if (origin != snapped.placeId) game.makeMove(card, origin, snapped.placeId);
    snapped = null;
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
