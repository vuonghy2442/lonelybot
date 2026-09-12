"""The unsat ladder, rung 0 — the corrected set-semantics model.

After the P.8 correction, the game is: per-pile unlock chains (fixed
top->bottom pop order), deck arrivals (free at draw-1), and foundation
departures (per-suit prefix order). A card's pop (its Reveal or its
surface-departure via PileStack) advances its pile's chain; the popped
card stays visible and may depart later.

Rung 0 is the sound RELAXATION: the dynamic legality gates (bm
movability, free_slot for deck placements, the reveal mask) are
dropped, and worry-backs are excluded (W=0). Therefore:

    solvable  => SAT   (the true winning line maps onto a schedule)
    UNSAT     => truly unsolvable (in the W=0 subgame at least — and
                 if the true game needs no worry-backs, fully unsolvable)

UNSAT of rung 0 is a sound rejection. SAT proves nothing (phantom
schedules possible). The ladder's next rungs add the gates one by one
to raise the kill rate; each rung stays a relaxation so its UNSAT
stays sound. The old solver is the oracle.
"""
import sys
import time

from pysat.formula import IDPool
from pysat.solvers import Cadical153

from graph import Card, Game, RANKS
from sat_scheduler import run_cli, deal_from_seed


class Rung0:
    def __init__(self, game: Game):
        self.game = game
        self.piles = [list(h) + list(v) for h, v in game.tableau]  # bottom -> top
        self.deck = set(game.deck)
        self.pool = IDPool()
        self.clauses = []

        # events:
        #   pop(X)  — X vacates its pile's surface (Reveal or surface-PileStack)
        #   arr(X)  — X leaves the deck to the visible set (DeckPile)
        #   dep(X)  — X departs to the foundation (PileStack/DeckStack)
        self.pop = {}   # card -> event idx
        self.arr = {}   # deck card -> event idx
        self.dep = {}   # all cards -> event idx
        ev = []

        def ev_new():
            i = len(ev)
            ev.append(i)
            return i

        for p in self.piles:
            for c in p:
                self.pop[c] = ev_new()
        for c in sorted(self.deck):
            self.arr[c] = ev_new()
        for c in set(self.pop) | self.deck:
            self.dep[c] = ev_new()
        self.ev = ev
        self.n = len(ev)

        self._order_vars()
        self._constraints()

    # ---- literals -------------------------------------------------------

    def lt_lit(self, a, b):
        """Literal TRUE iff event a happens before event b."""
        if a < b:
            return self.pool.id(("lt", a, b))
        return -self.pool.id(("lt", b, a))

    def occ_lit(self, c):
        return self.pool.id(("occ", c))

    def arr_lit(self, c):
        return self.pool.id(("arr", c))

    # ---- construction ----------------------------------------------------

    def _order_vars(self):
        n = self.n
        for a in range(n):
            for b in range(a + 1, n):
                lab = self.pool.id(("lt", a, b))
                for c in range(b + 1, n):
                    lbc = self.pool.id(("lt", b, c))
                    lac = self.pool.id(("lt", a, c))
                    self.clauses.append([-lab, -lbc, lac])
                    self.clauses.append([-lac, lab, lbc])

    def _constraints(self):
        # 1. pile chains: pops run top -> bottom in strict order
        for p in self.piles:
            for i in range(len(p) - 1):  # pop(top) < pop(next) < ... (top first)
                # events: p[i] is BELOW p[i+1]; the surface starts at the top
                pass
            # the chain: popping the surface reveals the card under it, so
            # the pops happen in the order top, top-1, ..., bottom
            for j in range(len(p) - 1, 0, -1):
                # pop of p[j] (nearer the top) precedes pop of p[j-1]
                self.clauses.append([self.lt_lit(self.pop[p[j]], self.pop[p[j - 1]])])

        # 2. visibility before departure:
        #    a pile card becomes visible when the card ABOVE it is popped
        for p in self.piles:
            for j in range(len(p) - 1):
                # dep(p[j]) > pop(p[j+1]): the card above must pop first
                self.clauses.append([self.lt_lit(self.pop[p[j + 1]], self.dep[p[j]])])
        #    a deck card departs after its arrival (if it arrived at all)
        for c in self.arr:
            self.clauses.append([-self.arr_lit(c), self.lt_lit(self.arr[c], self.dep[c])])
            self.clauses.append([self.occ_lit(c), self.arr_lit(c)])  # occ -> arrived
            self.clauses.append([-self.occ_lit(c), self.arr_lit(c),
                                 self.lt_lit(self.arr[c], self.dep[c])])

        # 3. a card's pop precedes-or-equals its departure:
        #    not(dep(X) < pop(X)) — the pop is the Reveal or the PileStack itself
        for c in self.pop:
            self.clauses.append([self.lt_lit(self.pop[c], self.dep[c])])

        # 4. foundation prefix: lower same-suit departs first
        for c in self.dep:
            if c.rank > 0:
                lo = Card(c.rank - 1, c.suit)
                self.clauses.append([self.lt_lit(self.dep[lo], self.dep[c])])

        # (all departs are mandatory events of the total order: the win
        #  condition is simply that every card's dep is scheduled, which
        #  the order encoding guarantees; the final state is all-foundations)

    # ---- solve -----------------------------------------------------------

    def solve(self):
        t0 = time.perf_counter()
        with Cadical153(bootstrap_with=self.clauses) as s:
            return s.solve(), time.perf_counter() - t0


def evaluate(seed: int, draw: int):
    game = Game.from_str(deal_from_seed(seed))
    t0 = time.perf_counter()
    m = Rung0(game)
    t_enc = time.perf_counter() - t0
    sat, t_sat = m.solve()
    oracle = run_cli("solve", "default", str(seed), str(draw))
    oracle_win = "Solvable" in oracle
    return {
        "oracle": "WIN" if oracle_win else "LOSE",
        "model": "SAT" if sat else "UNSAT",
        "n_ev": m.n,
        "n_cl": len(m.clauses),
        "t_enc": t_enc,
        "t_sat": t_sat,
    }


def main():
    if len(sys.argv) > 2 and sys.argv[1] == "corpus":
        lo, hi = int(sys.argv[2]), int(sys.argv[3])
        kill = agree = total_loss = 0
        for seed in range(lo, hi + 1):
            for draw in (1, 3):
                r = evaluate(seed, draw)
                if r["oracle"] == "LOSE":
                    total_loss += 1
                    if r["model"] == "UNSAT":
                        kill += 1
                    print(f"seed={seed} d{draw} oracle=LOSE model={r['model']} "
                          f"[{r['t_enc']:.2f}s+{r['t_sat']:.2f}s]")
                else:
                    if r["model"] == "UNSAT":
                        print(f"seed={seed} d{draw} *** UNSOUND: oracle WIN but model UNSAT ***")
                    else:
                        agree += 1
        print(f"\nrung-0: {kill}/{total_loss} losses killed "
              f"({100*kill/max(1,total_loss):.0f}%), "
              f"{agree} wins correctly SAT, 0 unsound (if none printed above)")
        return

    seed = int(sys.argv[1])
    draw = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    r = evaluate(seed, draw)
    print(r)


if __name__ == "__main__":
    main()
