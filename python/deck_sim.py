"""Exact Python port of deck.rs's state machine (the K+ representation),
verified against the engine's winning lines, then used to derive the
order-separable draw-3 constraints for rung 2.

Deck model (from deck.rs):
- self.deck: the remaining stock; draw(id) removes position id and sets
  draw_cur = id + 1; push undoes
- deal_once: draw_cur = 0 if cur >= len else min(cur + step, len)
- compute_mask(filter=False): the accessible set:
    loop 1: i = draw_cur - 1 if draw_cur > 0 else step - 1... exactly:
       i starts at draw_cur + (step if draw_cur == 0 else 0) - 1,
       visiting deck[i] for i += step while i < len - 1
    plus deck[len-1] always
    loop 2 (filter=False): i from step-1, += step, while i < end
       where end = (len if draw_cur % step else draw_cur) - 1
"""
import sys


class Deck:
    def __init__(self, cards, step):
        self.deck = list(cards)   # remaining, in deck.rs's order
        self.step = step
        self.draw_cur = 0

    def len(self):
        return len(self.deck)

    def draw(self, i):
        card = self.deck.pop(i)
        # draw(id) = set_offset(id+1); pop_next decrements -> final id
        self.draw_cur = i
        return card

    def push(self, card, i):
        self.deck.insert(i, card)
        self.draw_cur = i + 1

    def deal_once(self):
        cur = self.draw_cur
        self.draw_cur = 0 if cur >= len(self.deck) else min(cur + self.step, len(self.deck))

    def compute_mask(self):
        mask = set()
        n = len(self.deck)
        i = self.draw_cur + (self.step if self.draw_cur == 0 else 0) - 1
        while i < n - 1:
            if 0 <= i < n:
                mask.add(self.deck[i])
            i += self.step
        if n > 0:
            mask.add(self.deck[-1])
        # loop 2
        offset = self.draw_cur % self.step
        end = (n if offset != 0 else self.draw_cur) - 1
        i = self.step - 1
        while i < end:
            if 0 <= i < n:
                mask.add(self.deck[i])
            i += self.step
        return mask


def verify_line(seed, draw):
    """Replay the engine's winning line, checking every deck move is in
    compute_mask at its moment."""
    from graph import Card, Game, RANKS
    from sat_scheduler import run_cli, deal_from_seed
    from check_line import parse_line

    game = Game.from_str(deal_from_seed(seed))
    moves = parse_line(run_cli("solve", "default", str(seed), str(draw)))
    import json
    raw = json.loads(run_cli("print", "default", str(seed)).split("\n", 0)[0])if False else None
    from sat_scheduler import deal_from_seed as dfs
    raw = dfs(seed)
    orientations = {
        "printed-stock": [Card.from_str(c) for c in raw["stock"]],
        "reversed": list(game.deck),
    }
    for name, cards in orientations.items():
        deck = Deck(cards, draw)
        try:
            _verify_with(deck, moves)
            print(f"verify deck seed {seed} d{draw} [{name}]: ALL PASS")
            return
        except AssertionError as e:
            print(f"[{name}] failed: {e}")
    print("BOTH ORIENTATIONS FAILED")


def _verify_with(deck, moves):
    checks = 0
    for i, (name, c) in enumerate(moves):
        if name in ("DeckStack", "DeckPile"):
            assert c in deck.compute_mask(), (
                i, name, c, "not accessible",
                sorted(str(x) for x in deck.compute_mask()),
                "draw_cur", deck.draw_cur,
            )
            pos = deck.deck.index(c)
            deck.draw(pos)
            checks += 1


if __name__ == "__main__":
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    draw = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    verify_line(seed, draw)
