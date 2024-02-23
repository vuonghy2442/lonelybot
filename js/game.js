window.onload = addListeners;

const RANK_MAP = ['A', '1', '2', '3', '4', '5', '6', '7', '8', '9', '10', 'J', 'Q', 'K'];
const SUIT_MAP = ['♡', '♢', '♧', '♤'];
const N_SUITS = SUIT_MAP.length;
const N_RANKS = RANK_MAP.length;
// ♤♡♢♧♠♥♦♣

const game_box = document.querySelector("#game_box");

function addListeners() {
    document.querySelector("#deal").addEventListener('click', deal)
    draggable(game_box);
}

const cardMap = new Map();

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
            return this.rank * N_SUITS + this.suit;
        }

        cardMap.set(this.id(), this); // Add card to map

        this.createDOM = (pos_x, pos_y) => {
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
            game_box.appendChild(c);
            c.dataset.cardId = this.id();

            this.element = c;
        }

        this.flipCard = (duration) => {
            this.flipped = !this.flipped;

            if (this.element === null) {
                return;
            }

            // Flip card logic
            let inner = this.element.firstElementChild;
            if (duration > 0)
                inner.style.transition = `transform ${duration}ms`
            inner.classList.toggle("flipped");
            if (duration > 0)
                setTimeout(() => {
                    inner.style.removeProperty('transition');
                }, duration)
        };

        this.moveTo = (pos_x, pos_y, duration) => {
            if (this.element === null) return;

            if (duration > 0) {
                this.element.style.transition = `top ${duration}ms ease-in-out, left ${duration}ms ease-in-out`;
                this.animating = true;
            }

            if (pos_x !== null)
                this.element.style.left = pos_x + "%";

            if (pos_y !== null)
                this.element.style.top = pos_y + "%";

            if (duration > 0) {
                setTimeout(() => {
                    this.element.style.removeProperty('transition');
                    this.animating = false;
                }, duration);
            }
        }

        this.is_draggable = () => {
            return this.draggable && !this.animating;
        }
    }
}


function draggable(gameBox) {
    gameBox.addEventListener('mousedown', (event) => {
        const cardDOM = event.target.closest('.card');

        if (!cardDOM) return;
        const card = cardMap.get(parseInt(cardDOM.dataset.cardId));

        if (!card.is_draggable()) return;

        const gameBoxWidth = parseFloat(window.getComputedStyle(gameBox).width);
        const gameBoxHeight = parseFloat(window.getComputedStyle(gameBox).height);

        const initialX = parseFloat(window.getComputedStyle(cardDOM).left) / gameBoxWidth;
        const initialY = parseFloat(window.getComputedStyle(cardDOM).top) / gameBoxHeight;

        const offsetX = event.clientX / gameBoxWidth - initialX;
        const offsetY = event.clientY / gameBoxHeight - initialY;

        let changed = false;

        function handleMouseMove(event) {
            const clientX = event.clientX / gameBoxWidth;
            const clientY = event.clientY / gameBoxHeight;

            cardDOM.style.top = (clientY - offsetY) * 100 + '%';
            cardDOM.style.left = (clientX - offsetX) * 100 + '%';

            changed = true;
        }

        function handleMouseUp() {
            window.removeEventListener('mousemove', handleMouseMove);
            // Implement card snapping or other dragging behavior
            card.moveTo(initialX * 100, initialY * 100, 300);

            if (!changed) {
                // Handle the case where the card wasn't dragged
                card.flipCard(300);
            }
        }

        window.addEventListener('mousemove', handleMouseMove);
        window.addEventListener('mouseup', handleMouseUp, { once: true });
    });
}


function deal() {

    let deal_card = (rank, suit, pos) => {

        const c = new Card(rank, suit);
        c.flipCard();
        c.draggable = pos == 2;
        c.createDOM(2, 2.5);

        setTimeout(() => {
            c.flipCard(300);
            c.moveTo(15 + pos * 2, 2.5, 1000);
        }, 200 * pos);
    }

    deal_card(0, 0, 0);
    deal_card(0, 1, 1);
    deal_card(0, 2, 2);
}