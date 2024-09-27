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

const gameBox = document.querySelector("#game_box");

const getOffsetRect = (el) => {
  let rect = el.getBoundingClientRect();

  // add window scroll position to get the offset position
  let left = rect.left + window.scrollX;
  let top = rect.top + window.scrollY;
  let right = rect.right + window.scrollX;
  let bottom = rect.bottom + window.scrollY;

  // width and height are the same
  let width = rect.width;
  let height = rect.height;

  return { left, top, right, bottom, width, height };
};

let gameBoxBound = getOffsetRect(gameBox);

window.addEventListener("resize", (_) => {
  gameBoxBound = getOffsetRect(gameBox);
});

// creating cards
const cardArray = (() => {
  const cardArray = new Array(N_CARDS);

  for (let rank = 0; rank < N_RANKS; ++rank) {
    for (let suit = 0; suit < N_SUITS; ++suit) {
      let c = new Card(rank, suit);
      cardArray[c.id] = c;
    }
  }
  return cardArray;
})();

function shuffleArray(array) {
  for (let i = array.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [array[i], array[j]] = [array[j], array[i]];
  }
}

let shuffledCards = [...cardArray];
shuffleArray(shuffledCards);

const game = new Solitaire(shuffledCards, 3);

function getCard(rank, suit) {
  return cardArray[cardId(rank, suit)];
}

const THRESHOLD = 0.4;
const THRESHOLD_2 = THRESHOLD * THRESHOLD;

var snap_audio = new Audio("sound/snap.mp3");

let tableauContainers = [...document.querySelectorAll(".tableau")];
let stackContainers = [...document.querySelectorAll(".stack")];
let dealContainer = document.querySelector("#deal");
let wasteContainer = document.querySelector("#waste");

class CardPlace {
  constructor(element, offset, dirX, placeId) {
    element.dataset.placeId = placeId;

    this.element = element;
    this.offset = offset / 100;
    this.dirX = dirX;
    this.boundBox = getOffsetRect(element);
    this.placeId = placeId;

    this.getPos = (el) => {
      const bound = getOffsetRect(el);
      const last = getOffsetRect(element.lastChild || element);

      const x = (last.left - bound.left) / bound.width + (element.lastChild && dirX ? this.offset : 0);
      const y = (last.top - bound.top) / bound.height + (element.lastChild && !dirX ? this.offset : 0);

      return [x, y];
    };
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
    let hidden = game.hiddenPiles[i];
    const cont = tableauContainers[i];
    for (let j = 0; j < hidden.length; ++j) {
      hidden[j].flipCard();
      hidden[j].draggable = false;
      hidden[j].createDOM(cont, 0, DOWN_SPACE * j);
    }
    let visible = game.piles[i];
    for (let j = 0; j < visible.length; ++j) {
      visible[j].draggable = j + 1 == visible.length;
      visible[j].createDOM(cont, 0, DOWN_SPACE * hidden.length + UP_SPACE * j);
    }
  }
}

let wasteCards = [];

function handleDealEvent() {
  for (let c of wasteCards) {
    c.deleteDOM();
  }

  wasteCards = game.deck.peek(3);

  for (let [pos, c] of wasteCards.entries()) {
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
    let c = getCard(card.rank - 2, card.suit);
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

    for (let c of wasteCards) {
      c.moveToFront();
    }
  }

  if (wasteCards.length > 0) {
    wasteCards[wasteCards.length - 1].draggable = true;
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

  let handlingMove = false;

  function moveCard(event, card) {
    const origin_cont = card.container;
    const origin = parseInt(origin_cont.dataset.placeId);

    let moving_cards = [card];

    if (origin >= Pos.Pile) {
      let p = game.piles[origin - Pos.Pile];
      let id = p.findIndex((c) => c.id == card.id);
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
      for (let [place, pos] of dropPos) {
        if (distance2(x, y, ...pos) < THRESHOLD_2) {
          return [place, pos];
        }
      }
      return [null, null];
    }

    function handlePointerMove(event) {
      if (!event.isPrimary) return;

      let x = (event.pageX - cont_bound.left) / cont_bound.width - offsetX;
      let y = (event.pageY - cont_bound.top) / cont_bound.height - offsetY;

      let [place, pos] = findNear(x, y);

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

  gameBox.addEventListener("pointerdown", onPointerDown);
}
