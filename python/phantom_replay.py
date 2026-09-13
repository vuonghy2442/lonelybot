"""Phantom-replay instrument (the CEGAR probe).

For a game the ladder leaves SAT, extract the SAT model's witness
schedule (the phantom), replay it against the exact game — the deck
state machine (deck_sim.Deck) plus the dynamic gates — and tag the
first illegal move. The tag names the axis the phantom exploits:

  PACE      a deck draw is not accessible in the draw-3 machine
  GATE-BM   a foundation departure fails the bm (movability) gate
  GATE-FS   a placement/reveal fails the free_slot gate
  GATE-PRE  a foundation prefix violation (model bug if it fires)
  STRUCT    a surface/visibility mismatch (model bug if it fires)

Known liberties of rung 1/2 this probe is designed to expose: the deck
as a free set (draw-3), and the missing bm gate on deck-origin
departures (PileStack of a DeckPile-placed card).

Self-validation: `checkline` mode replays the ORACLE's winning line
through both machines — it must pass end-to-end.

Usage:
  python phantom_replay.py <seed> <draw>             # rung-2 phantom, k models
  python phantom_replay.py <seed> <draw> --no-pace  # pre-pace phantom
  python phantom_replay.py checkline <seed> <draw>   # replay the oracle's line
"""
import sys
import time

from pysat.solvers import Cadical153

from graph import Game, RANKS, SUITS
from sat_scheduler import run_cli, deal_from_seed
from check_line import parse_line
from deck_sim import Deck
from unsat_gates import Rung1, bottom_mask_of, free_slot_of, from_iid, iid, KING, KING_MASK
from unsat_pace3 import Rung3


def cname(c: int) -> str:
    return RANKS[c // 4] + SUITS[from_iid(c).suit]


class Replay:
    """The exact game: set-tableau + unlock chains + foundations, plus
    the exact deck machine. check() is legality-before; apply() mutates."""

    def __init__(self, game: Game, draw: int):
        self.piles = [[iid(c) for c in list(h) + list(v)] for h, v in game.tableau]
        self.surface = [len(p) - 1 for p in self.piles]
        self.deck = Deck([iid(c) for c in game.deck], draw)  # engine order
        self.vis = 0
        for p in self.piles:
            if p:
                self.vis |= 1 << p[-1]
        self.first_layer_kings = {p[0] for p in self.piles if p and p[0] // 4 == KING}
        self.found = [0] * 4

    def surface_of(self, c):
        return next((j for j, s in enumerate(self.surface)
                     if s >= 0 and self.piles[j][s] == c), None)

    def check(self, name, c):
        """(tag, detail) or None if legal."""
        lk = 0
        for j, s in enumerate(self.surface):
            if s >= 0:
                lk |= 1 << self.piles[j][s]
        bm = bottom_mask_of(self.vis, lk)
        fp = bin(self.vis & (lk | KING_MASK)).count("1") < 7
        fs = free_slot_of(bm, fp)
        t = 1 << c
        card = from_iid(c)
        if name == "PileStack":
            if not (self.vis & t):
                return ("STRUCT", "not in visible set")
            if not (bm & t):
                return ("GATE-BM", f"bm gate (bm={bm:013x})")
            if self.found[card.suit] != card.rank:
                return ("GATE-PRE", f"foundation at {self.found[card.suit]}")
            return None
        if name == "DeckStack":
            if c not in self.deck.deck:
                return ("STRUCT", "not in deck")
            if c not in self.deck.compute_mask():
                return ("PACE", f"draw_cur={self.deck.draw_cur}, "
                                f"accessible={self.accessible()}")
            if self.found[card.suit] != card.rank:
                return ("GATE-PRE", f"foundation at {self.found[card.suit]}")
            return None
        if name == "DeckPile":
            if c not in self.deck.deck:
                return ("STRUCT", "not in deck")
            if c not in self.deck.compute_mask():
                return ("PACE", f"draw_cur={self.deck.draw_cur}, "
                                f"accessible={self.accessible()}")
            if not (fs & t):
                return ("GATE-FS", f"free_slot={fs:013x}, "
                                   f"fp={fp}, bm={bm:013x}")
            return None
        if name == "Reveal":
            pi = self.surface_of(c)
            if pi is None:
                return ("STRUCT", "not a locked surface")
            if c in self.first_layer_kings:
                return ("STRUCT", "first-layer king reveal")
            if not (fs & t):
                return ("GATE-FS", f"free_slot={fs:013x}, fp={fp}, bm={bm:013x}")
            return None
        if name == "StackPile":  # the worry-back: foundation top -> vis
            if self.found[card.suit] != card.rank + 1:
                return ("STRUCT", f"not the foundation top ({self.found[card.suit]})")
            if not (fs & t):
                return ("GATE-FS", f"free_slot={fs:013x}, fp={fp}, bm={bm:013x}")
            return None
        raise AssertionError(name)

    def accessible(self):
        return sorted(cname(c) for c in self.deck.compute_mask())

    def apply(self, name, c):
        card = from_iid(c)
        if name == "PileStack":
            self.vis &= ~(1 << c)
            self.found[card.suit] += 1
            pi = self.surface_of(c)
            if pi is not None:
                self.surface[pi] -= 1
                if self.surface[pi] >= 0:
                    self.vis |= 1 << self.piles[pi][self.surface[pi]]
        elif name == "DeckStack":
            self.deck.draw(self.deck.deck.index(c))
            self.found[card.suit] += 1
        elif name == "DeckPile":
            self.deck.draw(self.deck.deck.index(c))
            self.vis |= 1 << c
        elif name == "Reveal":
            pi = self.surface_of(c)
            self.surface[pi] -= 1
            if self.surface[pi] >= 0:
                self.vis |= 1 << self.piles[pi][self.surface[pi]]
        elif name == "StackPile":  # the worry-back
            self.found[card.suit] -= 1
            self.vis |= 1 << c
        else:
            raise AssertionError(name)


def replay_moves(game, draw, moves):
    """First failure (i, name, card, tag, detail) or None if fully legal."""
    rp = Replay(game, draw)
    for i, (name, c) in enumerate(moves):
        err = rp.check(name, c)
        if err is not None:
            return (i, name, c, *err)
        rp.apply(name, c)
    return None


def pace_only(game, draw, moves):
    """Deck-machine-only check of the draw subsequence. First violation
    (i, name, card, detail) or None."""
    d = Deck([iid(c) for c in game.deck], draw)
    seq = [(n, c) for n, c in moves if n in ("DeckPile", "DeckStack")]
    for i, (n, c) in enumerate(seq):
        if c not in d.compute_mask():
            return (i, n, c,
                    f"draw_cur={d.draw_cur}, accessible="
                    f"{sorted(cname(x) for x in d.compute_mask())}")
        d.draw(d.deck.index(c))
    return None


# ---- phantom extraction ----------------------------------------------------


def extract_moves(m, model):
    idx2 = {}
    for c, i in m.R.items():
        idx2[i] = ("R", c)
    for c, i in m.ARR.items():
        idx2[i] = ("A", c)
    for c, i in m.DEP.items():
        idx2[i] = ("D", c)

    n = m.n
    succ = {i: [] for i in range(1, n + 1)}
    indeg = {i: 0 for i in range(1, n + 1)}
    for a in range(1, n + 1):
        for b in range(a + 1, n + 1):
            lab = m.lit(("lt", a, b))
            x, y = (a, b) if lab in model else (b, a)
            succ[x].append(y)
            indeg[y] += 1
    ready = [i for i in range(1, n + 1) if indeg[i] == 0]
    topo = []
    while ready:
        i = ready.pop()
        topo.append(i)
        for j in succ[i]:
            indeg[j] -= 1
            if indeg[j] == 0:
                ready.append(j)
    assert len(topo) == n, "order cycle"

    moves = []
    for i in topo:
        kind, c = idx2[i]
        if kind == "R":
            if m.occR(c) in model:
                moves.append(("Reveal", c))
        elif kind == "A":
            if m.occA(c) in model:
                moves.append(("DeckPile", c))
        else:
            if c in m.deck and m.occA(c) not in model:
                moves.append(("DeckStack", c))
            else:
                moves.append(("PileStack", c))
    return moves


def phantom_models(m, k=3):
    """k diverse SAT models: block the occurrence + deck-order projection."""
    out = []
    with Cadical153(bootstrap_with=m.clauses) as s:
        for _ in range(k):
            if not s.solve():
                break
            model = set(s.get_model())
            out.append(model)
            proj = [m.occA(c) for c in m.deck] + [m.occR(c) for c in m.pile_cards()]
            deck_evs = [m.ARR[c] for c in m.deck] + [m.DEP[c] for c in m.deck]
            deps = [m.DEP[c] for c in sorted(m.DEP)]
            for evs in (deck_evs, deps):
                for a in range(len(evs)):
                    for b in range(a + 1, len(evs)):
                        x, y = sorted((evs[a], evs[b]))
                        proj.append(m.lit(("lt", x, y)))
            block = [-l for l in proj if l in model]
            assert block, "empty blocking projection"
            s.add_clause(block)
    return out


# ---- modes -------------------------------------------------------------------


def report(seed, draw, use_pace=True, k=3, rung3=False):
    game = Game.from_str(deal_from_seed(seed))
    m = Rung3(game, draw) if rung3 else Rung1(game, draw, use_pace=use_pace)
    t0 = time.perf_counter()
    models = phantom_models(m, k)
    t = time.perf_counter() - t0
    pace_lbl = "rung3" if rung3 else ("on" if use_pace else "OFF")
    print(f"seed {seed} d{draw} ({pace_lbl}): "
          f"{len(models)} phantom(s), {t:.2f}s")
    if not models:
        print("  UNSAT — no phantom; the model kills this game")
        return
    for j, model in enumerate(models):
        moves = extract_moves(m, model)
        fail = replay_moves(game, draw, moves)
        pace = pace_only(game, draw, moves)
        if fail is None:
            print(f"  phantom #{j + 1}: {len(moves)} moves — FULLY LEGAL "
                  f"(a real win?!)")
        else:
            i, name, c, tag, detail = fail
            print(f"  phantom #{j + 1}: {len(moves)} moves; first illegal at "
                  f"#{i}: {name} {cname(c)} — {tag} ({detail})")
        if pace is None:
            print(f"    pace-only: CLEAN ({sum(1 for n, _ in moves if n in ('DeckPile', 'DeckStack'))} draws)")
        else:
            i, name, c, detail = pace
            print(f"    pace-only: violation at draw #{i + 1}: {name} "
                  f"{cname(c)} ({detail})")


def checkline(seed, draw):
    game = Game.from_str(deal_from_seed(seed))
    moves = parse_line(run_cli("solve", "default", str(seed), str(draw)))
    moves = [(n, iid(c)) for n, c in moves]
    fail = replay_moves(game, draw, moves)
    pace = pace_only(game, draw, moves)
    if fail is None and pace is None:
        print(f"checkline seed {seed} d{draw}: {len(moves)} moves — "
              f"ALL LEGAL (both machines)")
    else:
        if fail is not None:
            i, name, c, tag, detail = fail
            print(f"checkline seed {seed} d{draw}: FAIL at #{i}: {name} "
                  f"{cname(c)} — {tag} ({detail})")
        if pace is not None:
            i, name, c, detail = pace
            print(f"  pace: FAIL at draw #{i + 1}: {name} {cname(c)} ({detail})")


def main():
    if sys.argv[1] == "checkline":
        checkline(int(sys.argv[2]), int(sys.argv[3]))
        return
    seed = int(sys.argv[1])
    draw = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    use_pace = "--no-pace" not in sys.argv
    report(seed, draw, use_pace, rung3="--rung3" in sys.argv)


if __name__ == "__main__":
    main()
