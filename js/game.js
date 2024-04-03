"use strict";

window.onload = addListeners;

const RANK_MAP = ['A', '2', '3', '4', '5', '6', '7', '8', '9', '10', 'J', 'Q', 'K'];
const SUIT_MAP = ['♡', '♢', '♧', '♤'];
const N_SUITS = SUIT_MAP.length;
const N_RANKS = RANK_MAP.length;
const KING_RANK = N_RANKS - 1;
const N_CARDS = N_SUITS * N_RANKS;

const N_PILES = 7;
const N_HIDDEN_CARDS = N_PILES * (N_PILES + 1) / 2;
const N_FULL_DECK = N_CARDS - N_HIDDEN_CARDS;

// ♤♡♢♧♠♥♦♣

function cardId(rank, suit) {
    return rank * N_SUITS + suit;
}


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
            this.animating = false;
            this.element.remove();
            this.element = null;
        };

        this.createDOM = (pos_x, pos_y) => {
            if (this.element !== null) return;
            const c = document.createElement('div');
            c.id = `card_${rank}_${suit}`;
            c.className = suit < 2 ? "card red_card" : "card black_card";
            c.draggable = false;
            c.innerHTML = `
            <div class="card_inner">
                <div class="card_back">
                    <svg width="100%" height="100%">
                        <image xlink:href="images/back.svg" width="100%" height="100%"/>
                    </svg>
                </div>
                <div class="card_front">
                    <div class="card_header">
                        <span>${RANK_MAP[rank]}</span> <br>
                        <span>${SUIT_MAP[suit]}</span>

                    </div>
                    <div class="card_body">
                        <span>${RANK_MAP[rank]}</span>

                    </div>
                    <div class="card_footer">
                        <span>${RANK_MAP[rank]}</span> <br>
                        <span>${SUIT_MAP[suit]}</span>
                    </div>
                </div>
            </div>
                `;

            if (this.flipped)
                c.firstElementChild.classList.add("flipped")

            c.style.left = pos_x + "%";
            c.style.top = pos_y + "%";
            gameBox.appendChild(c);
            c.dataset.cardId = this.id();

            this.element = c;
        };

        this.turnUp = (duration) => {
            if (this.flipped) {
                this.flipCard(duration);
            }
        }

        this.flipCard = (duration) => {
            this.flipped = !this.flipped;

            if (this.element === null) {
                return;
            }

            // Flip card logic
            let inner = this.element.firstElementChild;
            if (duration > 0) {
                inner.style.transition = `transform ${duration}ms`
                inner.addEventListener("transitionend", (e) => {
                    inner.style.removeProperty('transition');
                }, { once: true });
            }

            inner.classList.toggle("flipped");
        };

        this.moveTo = (pos_x, pos_y, duration, zIndex) => {
            if (this.element === null) return;

            {
                const currentLeft = parseFloat(this.element.style.left) || 0;
                const currentTop = parseFloat(this.element.style.top) || 0;

                // this to prevent transitionend not triggered
                if (Math.abs(currentLeft - pos_x) < 1e-2 && Math.abs(currentTop - pos_y) < 1e-2) {
                    this.element.style.zIndex = zIndex;
                    return;
                }
            }

            if (duration > 0) {
                this.animating = true;
                this.element.style.transition = `top ${duration}ms ease-in-out, left ${duration}ms ease-in-out`;

                this.element.addEventListener("transitionend", (e) => {
                    this.element.style.removeProperty('transition');
                    this.animating = false;
                    if (zIndex !== null) {
                        this.element.style.zIndex = zIndex;
                    }
                }, { once: true });
            } else {
                if (zIndex !== null) {
                    this.element.style.zIndex = zIndex;
                }
            }

            if (pos_x !== null)
                this.element.style.left = pos_x + "%";

            if (pos_y !== null)
                this.element.style.top = pos_y + "%";
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
            };
        };
    }
}

const Pos = {
    Deck: 0,
    Stack: 1,
    Pile: 1 + N_SUITS,
    None: -1,
}

class Solitaire {
    constructor(cards, draw_step) {
        const hidden_cards = cards.slice(0, N_HIDDEN_CARDS);
        this.piles = Array.from(Array(N_PILES), (_, i) => {
            return [hidden_cards[(i + 2) * (i + 1) / 2 - 1]];
        });

        this.hidden_piles = Array.from(Array(N_PILES), (_, i) => {
            return hidden_cards.slice((i + 1) * i / 2, (i + 2) * (i + 1) / 2 - 1);
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
            return Pos.None
        }

        this.lift_card = (card) => {
            // here
            const res = new Array();
            if (this.stack[card.suit] == card.rank) {
                res.push(Pos.Stack + card.suit);
            }

            for (let i = 0; i < N_PILES; ++i) {
                const p = this.piles[i]
                const last = p[p.length - 1] || new Card(N_RANKS, 0);
                if (last.goBefore(card)) {
                    res.push(Pos.Pile + i);
                }
            }

            return res;
        }

        this.make_move = (card, src, dst) => {
            // find the position
            if (src == Pos.Deck && dst == Pos.Deck) {
                this.deck.deal();
                for (const callback of this.on_deal) { callback(); }
                return;
            }
            if (src == Pos.Deck) {
                this.deck.pop();
                for (const callback of this.on_pop_deck) { callback(); }

            } else if (src <= N_SUITS) {
                this.stack[src - 1] -= 1
                for (const callback of this.on_pop_stack) { callback(card); }
            }

            if (dst <= N_SUITS) {
                this.stack[dst - 1] += 1
                for (const callback of this.on_push_stack) { callback(card); }
            }

            // from pile
            let cards = [card];
            if (src >= Pos.Pile) {
                src = src - Pos.Pile;
                const cardPos = this.piles[src].findIndex((c) => c.id() == card.id());
                cards = this.piles[src].splice(cardPos)

                if (this.piles[src].length == 0 && this.hidden_piles[src].length > 0) {
                    const last = this.hidden_piles[src].pop()
                    this.piles[src].push(last);
                    for (const callback of this.on_reveal) { callback(src, last); }
                }
            }

            // to pile
            if (dst >= Pos.Pile) {
                dst = dst - Pos.Pile;
                this.piles[dst].push(...cards);
            }
        }
    }
};

const gameBox = document.querySelector("#game_box");

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
// shuffledCards.reverse();
shuffleArray(shuffledCards);

const game = new Solitaire(shuffledCards, 3);

function addListeners() {
    initGame();
}


function getCard(rank, suit) {
    return cardArray[cardId(rank, suit)];
}

const THRES = 0.06;
const THRES_2 = THRES * THRES;

var snap_audio = new Audio('sound/snap.mp3');


function initGame() {
    let gameBoxBound = gameBox.getBoundingClientRect();

    function getDOMPos(el) {
        let bound = el.getBoundingClientRect();
        const x = (bound.left - gameBoxBound.left) / gameBoxBound.width;
        const y = (bound.top - gameBoxBound.top) / gameBoxBound.height;
        return [x, y];
    }

    const pilePos = function () {
        let pos_stack = new Array();
        let pos_tableau = new Array();
        // not correct but whatever =))
        pos_stack.push(getDOMPos(document.querySelector("#deal")));

        for (let s of document.querySelectorAll("#stack > div")) {
            pos_stack.push(getDOMPos(s));
        }

        for (let s of document.querySelectorAll("#tableau > div")) {
            pos_tableau.push(getDOMPos(s));
        }

        for (let i = 0; i < N_PILES; ++i) {
            let hidden = game.hidden_piles[i];
            const pos = pos_tableau[i];
            for (let j = 0; j < hidden.length; ++j) {
                hidden[j].flipCard();
                hidden[j].draggable = false;
                hidden[j].createDOM(pos[0] * 100, pos[1] * 100 + 2 * j);
            }
            let visible = game.piles[i];
            for (let j = 0; j < visible.length; ++j) {
                visible[j].draggable = j + 1 == visible.length;
                visible[j].createDOM(pos[0] * 100, pos[1] * 100 + 2 * hidden.length + j * 3);
            }
        }

        return () => [...pos_stack, ...pos_tableau.map((p, i) =>
            [p[0], p[1] + 0.02 * game.hidden_piles[i].length + 0.03 * game.piles[i].length]
        )];
    }();
    console.log(pilePos())

    window.addEventListener('resize', (_) => {
        gameBoxBound = gameBox.getBoundingClientRect();
    });

    game.on_deal.push(() => {
        for (let c of cards) {
            c.deleteDom();
        }

        cards = []

        for (let [pos, c] of game.deck.peek(3).entries()) {
            cards.push(c);
            c.draggable = false;

            c.flipCard();
            c.createDOM(2, 2.5);
            c.element.style.zIndex = pos;

            setTimeout(() => {
                c.flipCard(300);
                c.moveTo(15 + pos * 2, 2.5, 300);
                c.draggable = pos == 2;
            }, 200 * pos);
        }
    })

    game.on_push_stack.push((card) => {
        if (card.rank >= 2) {
            cardArray[cardId(card.rank - 2, card.suit)].deleteDom();
        }

        if (card.rank > 0) {
            cardArray[cardId(card.rank - 1, card.suit)].draggable = false;
        }
    })

    game.on_pop_stack.push((card) => {
        if (card.rank > 2) {
            let c = cardArray[cardId(card.rank - 2, card.suit)];
            c.turnUp();
            c.draggable = false;
            c.createDOM(initialX, initialY);
        }

        if (card.rank > 0) {
            cardArray[cardId(card.rank - 1, card.suit)].draggable = false;
        }
    })

    game.on_pop_deck.push(() => {
        cards.pop();
        if (cards.length <= 1) {
            // append new stuff
            cards = game.deck.peek(cards.length + 1)

            cards[0].draggable = false;
            cards[0].turnUp();
            cards[0].createDOM(15, 2.5);

            for (let [pos, c] of cards.entries()) {
                c.element.style.zIndex = pos;
            }
        }
        cards[cards.length - 1].draggable = true;
    })

    game.on_reveal.push((src, card) => {
        card.draggable = true;
        card.turnUp(200);
    })

    function moveCard(event, card) {
        if (!card.isDraggable()) return;
        snap_audio.play();
        const initialZIndex = card.element.style.zIndex;
        card.element.style.zIndex = 100;

        const origin = game.find_origin(card);

        const dropPos = game.lift_card(card);

        const [initialX, initialY] = getDOMPos(card.element);

        const offsetX = (event.clientX - gameBoxBound.left) / gameBoxBound.width - initialX;
        const offsetY = (event.clientY - gameBoxBound.top) / gameBoxBound.height - initialY;

        let changed = false;
        let snapped = -1;

        let curPilePos = pilePos();

        function distance2(x, y, u, v) {
            const [dx, dy] = [x - u, y - v];
            return dx * dx + dy * dy;
        }

        function findNear(x, y) {
            if (snapped >= 0) return snapped;
            for (let p of dropPos) {
                if (distance2(x, y, ...curPilePos[p]) < THRES_2) {
                    return p;
                }
            }
            return -1
        }

        function handleMouseMove(event) {
            if (!card.isDraggable()) return;

            let x = (event.clientX - gameBoxBound.left) / gameBoxBound.width - offsetX;
            let y = (event.clientY - gameBoxBound.top) / gameBoxBound.height - offsetY;

            let p = findNear(x, y);

            if (p >= 0) {
                let [u, v] = curPilePos[p];
                const [dx, dy] = [x - u, y - v];
                let dis2 = distance2(x, y, u, v);
                let d = Math.max(Math.sqrt(dis2) / THRES - 1, 0);

                if (d == 0 && snapped < 0) {
                    snapped = p;
                } else if (d > 0 && snapped >= 0) {
                    snapped = -1;
                }

                const force = d > 0 ? 0 : 1;
                x -= dx * force;
                y -= dy * force;
            }

            card.moveTo(x * 100, y * 100, 0);
            changed = true;
        }

        function handleMouseUp() {
            window.removeEventListener('mousemove', handleMouseMove);

            // Implement card snapping or other dragging behavior
            if (snapped < 0) {
                card.moveTo(initialX * 100, initialY * 100, 300, initialZIndex);
            } else {
                snap_audio.play();
                card.element.style.zIndex = card.rank;

                // if (origin == Pos.Deck) {

                // } else if (origin < Pos.Pile) {

                // } else {
                //     // Piles
                // }

                game.make_move(card, origin, snapped);
            }

        }

        window.addEventListener('mousemove', handleMouseMove);
        window.addEventListener('mouseup', handleMouseUp, { once: true });
    }

    let cards = [];

    function deal() {
        game.make_move(null, 0, 0);
    }

    gameBox.addEventListener('mousedown', (event) => {
        if (event.which !== 1)
            return;

        const cardDOM = event.target.closest('.card');

        if (cardDOM) {
            const card = cardArray[parseInt(cardDOM.dataset.cardId)];
            moveCard(event, card);
            // some how it fix the default stuff :))
            event.preventDefault();
            return;
        }

        if (event.target.closest('#deal')) {
            deal();
            event.preventDefault();
            return;
        }
    });
}