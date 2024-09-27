"use strict";

window.onload = addListeners;

const RANK_MAP = ["A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K"];
const SUIT_MAP = ["♡", "♢", "♧", "♤"];
const N_SUITS = SUIT_MAP.length;
const N_RANKS = RANK_MAP.length;
const KING_RANK = N_RANKS - 1;
const N_CARDS = N_SUITS * N_RANKS;

const N_PILES = 7;
const N_HIDDEN_CARDS = (N_PILES * (N_PILES + 1)) / 2;
const N_FULL_DECK = N_CARDS - N_HIDDEN_CARDS;

const UP_SPACE = 15;
const DOWN_SPACE = 10;
const DEAL_SPACE = 25;

const ANIMATION_TIME = 100;
const OFFSET_TIME = 100;
const REVEAL_TIME = 300;

// ♤♡♢♧♠♥♦♣

function cardId(rank, suit) {
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

// const container = document.querySelector("#card_container");

let front_element = null;

class Card {
  constructor(rank, suit) {
    this.rank = rank;
    this.suit = suit;
    this.flipped = false;

    // private shouldn't change from the outside
    this.draggable = true;

    this.animating = false;
    this.element = null;

    this.id = () => {
      return cardId(rank, suit);
    };

    this.deleteDom = () => {
      if (this.element === null) return;
      this.element.remove();
      this.element = null;
    };

    this.moveToFront = () => {
      if (this.element === null) return;
      this.element.parentElement.appendChild(this.element);
    };

    this.moveParentToFront = () => {
      if (this.element === null) return;
      if (front_element !== null) front_element.style.zIndex = 0;

      this.element.parentElement.style.zIndex = 1;
      front_element = this.element.parentElement;
    };

    this.createDOM = (container, pos_x, pos_y) => {
      if (this.element !== null) return;
      const c = document.createElement("div");
      c.className = "card";
      c.draggable = false;
      c.innerHTML = `<div class="card_inner">
        <div class="card_back"></div>
        ${createCardSVG(this)}
      </div>`;

      const inner = c.firstElementChild;

      if (this.flipped) inner.classList.add("flipped");

      c.style.left = pos_x + "%";
      c.style.top = pos_y + "%";

      c.addEventListener("transitionrun", (_) => {
        this.animating = true;
      });

      const done_animate = (_) => {
        c.style.removeProperty("transition");
        this.animating = false;
      };

      c.addEventListener("transitioncancel", done_animate);
      c.addEventListener("transitionend", done_animate);

      // const done_flip_animate = (_) => {
      //   c.style.removeProperty("transition");
      //   this.animating = false;
      // };

      // inner.addEventListener("transitioncancel", done_flip_animate);
      // inner.addEventListener("transitionend", done_flip_animate);

      container.appendChild(c);
      c.dataset.cardId = this.id();

      this.element = c;
    };

    this.turnUp = (duration) => {
      if (this.flipped) {
        this.flipCard(duration);
      }
    };

    this.flipCard = (duration) => {
      this.flipped = !this.flipped;

      if (this.element === null) {
        return;
      }

      // Flip card logic
      let inner = this.element.firstElementChild;
      // if (duration > 0) {
      //   inner.style.transition = `transform ${duration}ms`;
      // }

      inner.classList.toggle("flipped");
    };

    this.moveTo = (container, pos_x, pos_y, duration) => {
      if (this.element === null) return;
      const same_cont = container === null || container === this.element.parentElement;
      {
        const currentLeft = parseFloat(this.element.style.left) || 0;
        const currentTop = parseFloat(this.element.style.top) || 0;

        // this to prevent transitionend not triggered
        if (same_cont && Math.abs(currentLeft - pos_x) < 1e-2 && Math.abs(currentTop - pos_y) < 1e-2) {
          return;
        }
      }

      if (duration > 0) this.element.style.transition = `top ${duration}ms ease-in, left ${duration}ms ease-in`;

      if (pos_x !== null) this.element.style.left = pos_x + "%";

      if (pos_y !== null) this.element.style.top = pos_y + "%";
      if (!same_cont) {
        this.element.parentElement.removeChild(this.element);
        container.appendChild(this.element);
      }
    };

    this.isDraggable = () => {
      return this.draggable && !this.animating;
    };

    this.goBefore = (card) => {
      return this.rank == card.rank + 1 && (((this.suit ^ card.suit) & 2) === 2 || this.rank === N_RANKS);
    };
  }
}

class Deck {
  constructor(cards, draw_step) {
    this.stock = cards;
    this.waste = [];
    this.draw_step = draw_step;

    this.peek = (n) => {
      const len = this.waste.length;
      const start = Math.max(len - n, 0);
      return this.waste.slice(start, len);
    };

    this.pop = () => {
      return this.waste.pop();
    };

    this.deal = () => {
      if (this.stock.length == 0) {
        this.stock = this.waste;
        this.waste = [];
      } else {
        let removed = this.stock.splice(0, this.draw_step);
        this.waste.push(...removed);
      }
    };
  }
}

const Pos = {
  Deck: 0,
  Stack: 1,
  Pile: 1 + N_SUITS,
  None: -1,
};

class Solitaire {
  constructor(cards, draw_step) {
    const hidden_cards = cards.slice(0, N_HIDDEN_CARDS);
    this.piles = Array.from(Array(N_PILES), (_, i) => {
      return [hidden_cards[((i + 2) * (i + 1)) / 2 - 1]];
    });

    this.hidden_piles = Array.from(Array(N_PILES), (_, i) => {
      return hidden_cards.slice(((i + 1) * i) / 2, ((i + 2) * (i + 1)) / 2 - 1);
    });

    this.deck = new Deck(cards.slice(N_HIDDEN_CARDS, N_CARDS), draw_step);
    this.stack = Array.from(Array(N_SUITS), () => 0);

    this.on_deal = [];
    this.on_pop_deck = [];
    this.on_pop_stack = [];
    this.on_push_stack = [];
    this.on_reveal = [];

    this.find_origin = (card) => {
      if (this.deck.peek(1).find((c) => c.id() == card.id())) {
        return Pos.Deck;
      }

      if (this.stack.find((rank, suit) => card.id() == cardId(rank - 1, suit))) {
        return Pos.Stack + card.suit;
      }

      const pos = this.piles.findIndex((pile) => pile.find((c) => c.id() == card.id()));
      if (pos >= 0) {
        return Pos.Pile + pos;
      }
      return Pos.None;
    };

    this.lift_card = (cards) => {
      const card = cards[0];
      const res = new Array();
      if (cards.length == 1 && this.stack[card.suit] == card.rank) {
        res.push(Pos.Stack + card.suit);
      }

      for (let i = 0; i < N_PILES; ++i) {
        const p = this.piles[i];
        const last = p[p.length - 1] || new Card(N_RANKS, 0);
        if (last.goBefore(card)) {
          res.push(Pos.Pile + i);
        }
      }

      return res;
    };

    this.make_move = (card, src, dst) => {
      // find the position
      if (src == Pos.Deck && dst == Pos.Deck) {
        this.deck.deal();
        for (const callback of this.on_deal) {
          callback();
        }
        return;
      }
      if (src == Pos.Deck) {
        this.deck.pop();
        for (const callback of this.on_pop_deck) {
          callback();
        }
      } else if (src <= N_SUITS) {
        this.stack[src - 1] -= 1;
        for (const callback of this.on_pop_stack) {
          callback(card);
        }
      }

      if (dst <= N_SUITS) {
        this.stack[dst - 1] += 1;
        for (const callback of this.on_push_stack) {
          callback(card);
        }
      }

      // from pile
      let cards = [card];
      if (src >= Pos.Pile) {
        src = src - Pos.Pile;
        const cardPos = this.piles[src].findIndex((c) => c.id() == card.id());
        cards = this.piles[src].splice(cardPos);

        if (this.piles[src].length == 0 && this.hidden_piles[src].length > 0) {
          const last = this.hidden_piles[src].pop();
          this.piles[src].push(last);
          for (const callback of this.on_reveal) {
            callback(src, last);
          }
        }
      }

      // to pile
      if (dst >= Pos.Pile) {
        dst = dst - Pos.Pile;
        this.piles[dst].push(...cards);
      }
    };
  }
}

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
      cardArray[c.id()] = c;
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

function addListeners() {
  initGame();
}

function getCard(rank, suit) {
  return cardArray[cardId(rank, suit)];
}

const THRES = 0.4;
const THRES_2 = THRES * THRES;

var snap_audio = new Audio("sound/snap.mp3");

let tableauConts = [...document.querySelectorAll(".tableau")];
let stackConts = [...document.querySelectorAll(".stack")];
let dealCont = document.querySelector("#deal");
let wasteCont = document.querySelector("#waste");

class CardPlace {
  constructor(element, offset, dirX, placeId) {
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
  new CardPlace(wasteCont, DEAL_SPACE, true, 0),
  ...stackConts.map((s, idx) => new CardPlace(s, 0, false, Pos.Stack + idx)),
  ...tableauConts.map((s, idx) => new CardPlace(s, UP_SPACE, false, Pos.Pile + idx)),
];

function initGame() {
  for (let i = 0; i < N_PILES; ++i) {
    let hidden = game.hidden_piles[i];
    const cont = tableauConts[i];
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

  game.on_deal.push(() => {
    for (let c of cards) {
      c.deleteDom();
    }

    cards = game.deck.peek(3);

    for (let [pos, c] of cards.entries()) {
      c.draggable = false;
      c.flipCard();

      c.createDOM(dealCont, 0, 0);
      c.moveToFront();

      setTimeout(() => {
        c.flipCard(ANIMATION_TIME);
        c.moveTo(wasteCont, pos * DEAL_SPACE, 0, ANIMATION_TIME);
        if (pos + 1 == cards.length) {
          c.draggable = true;
        }
      }, OFFSET_TIME * pos);
    }
  });

  game.on_push_stack.push((card) => {
    card.moveToFront();

    if (card.rank >= 2) {
      cardArray[cardId(card.rank - 2, card.suit)].deleteDom();
    }

    if (card.rank > 0) {
      cardArray[cardId(card.rank - 1, card.suit)].draggable = false;
    }
  });

  game.on_pop_stack.push((card) => {
    if (card.rank >= 2) {
      let c = cardArray[cardId(card.rank - 2, card.suit)];
      c.turnUp();
      c.draggable = false;
      c.createDOM(stackConts[card.suit], 0, 0);
      cardArray[cardId(card.rank - 1, card.suit)].moveToFront();
    }

    if (card.rank > 0) {
      cardArray[cardId(card.rank - 1, card.suit)].draggable = true;
    }
  });

  game.on_pop_deck.push(() => {
    cards.pop();
    if (cards.length <= 1) {
      // append new stuff
      cards = game.deck.peek(cards.length + 1);

      if (cards.length > 0) {
        cards[0].draggable = false;
        cards[0].turnUp();
        cards[0].createDOM(wasteCont, 0, 0);
      }

      for (let c of cards) {
        c.moveToFront();
      }
    }

    if (cards.length > 0) {
      cards[cards.length - 1].draggable = true;
    }
  });

  game.on_reveal.push((src, card) => {
    card.draggable = true;
    card.turnUp(REVEAL_TIME);
  });

  let handlingMove = false;

  function moveCard(event, card) {
    const origin = game.find_origin(card);
    const origin_cont = card.element.parentElement;

    let moving_cards = [card];

    if (origin >= Pos.Pile) {
      let p = game.piles[origin - Pos.Pile];
      let id = p.findIndex((c) => c.id() == card.id());
      moving_cards = p.slice(id);
    }

    if (moving_cards.some((c) => !c.isDraggable())) return;
    snap_audio.play();

    card.moveParentToFront();

    const dropPos = game.lift_card(moving_cards).map((p) => [cardPlaces[p], cardPlaces[p].getPos(origin_cont)]);

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
        if (distance2(x, y, ...pos) < THRES_2) {
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
        // const [dx, dy] = [x - u, y - v];
        // let dis2 = dx * dx + dy * dy;
        // let d = Math.max(Math.sqrt(dis2) / THRES - 0.5, 0);

        // const force = d > 0 ? Math.exp(-d / 0.5) : 1;
        // x -= dx * force;
        // y -= dy * force;

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
        game.make_move(card, origin, snapped.placeId);
        snapped = null;
      }
      handlingMove = false;
    }

    handlingMove = true;

    window.addEventListener("pointermove", handlePointerMove);
    window.addEventListener("pointerup", handlePointerUp);
    window.addEventListener("pointercancel", handlePointerCancel);
  }

  let cards = [];

  function deal() {
    game.make_move(null, 0, 0);
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
      deal();
      event.preventDefault();
      return;
    }
  }

  gameBox.addEventListener("pointerdown", onPointerDown);
}
