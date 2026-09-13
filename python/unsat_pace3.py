"""The unsat ladder, rung 3 — the exact draw-3 deck machine.

deck_bf.py establishes (all reachable states N<=15, all permutations
N<=9, all 56 corpus d3 winning lines): a draw sequence is realizable
in deck.rs's K+ machine iff, for every consecutive pair x -> w,

    lane2(w) or max(w) or ( lane(w) = lane(x)-1 (mod 3)
                            and interval(x, w) )

with lane(v) = (O(v) - r(v)) % 3, r(v) = the number of cards drawn
before v from below O(v); max(w) = every card above O(w) drawn before
w; interval(x, w) = O(w) > O(x), or every card in [O(w), O(x)) except
w drawn before x (the burial constraint P(w) >= P(x) - 1, whose
between-count is always saturated).

This encoding makes those constraints exact over the event order:

  dlt(x,y)     the rung-1 drawLt aux, completed to a biconditional
  lane(w,k)    a mod-3 sequential counter over dlt(z,w), z below w
  first(w)     self-certifying: forces dlt(w,z) for all z
  max(w)       self-certifying: forces dlt(z,w) for all z above
  P(x,w)       self-certifying: forces x = w's immediate predecessor
               (dlt + no-between), the lane congruence, the interval
  per-card clause   first(w) v max(w) v lane2(w) v OR_x P(x,w)

Every aux certifies its own truth when asserted (its clauses are the
facts it names), so no converse clauses are needed and no phantom can
hide: a false first/max/P contradicts the pinned order literals.

Usage:
  python unsat_pace3.py <seed> <draw>
  python unsat_pace3.py corpus [lo hi]     # default 12 75
"""
import sys
import time

from pysat.solvers import Cadical153

from graph import Game
from sat_scheduler import run_cli, deal_from_seed
from unsat_gates import Rung1, iid


class Rung3(Rung1):
    def __init__(self, game: Game, draw_step: int = 3):
        super().__init__(game, draw_step, use_pace=False)
        self.deck_order = [iid(c) for c in game.deck]  # engine order
        self.pos = {c: i for i, c in enumerate(self.deck_order)}
        self._dlt_done = set()
        self._lane_cache = {}
        self._max_cache = {}
        self._pace3()

    # ---- pieces --------------------------------------------------------

    def _dlt(self, x, y):
        """x drawn before y — drawLt completed to a biconditional."""
        if (x, y) in self._dlt_done:
            return self.lit(("drawLt", x, y))
        a = self.drawLt(x, y)  # the aux + the forward case-split clauses
        ax, ay = self.occA(x), self.occA(y)
        rx, dx = self.ARR[x], self.DEP[x]
        ry, dy = self.ARR[y], self.DEP[y]
        # the case-split orders imply the aux (the converse rung-1 omits)
        self.emit([-ax, -ay, -self.lt_lit(rx, ry), a])
        self.emit([-ax, ay, -self.lt_lit(rx, dy), a])
        self.emit([ax, -ay, -self.lt_lit(dx, ry), a])
        self.emit([ax, ay, -self.lt_lit(dx, dy), a])
        self._dlt_done.add((x, y))
        return a

    def _lane_lits(self, w):
        """One-hot [lane0, lane1, lane2] of w at its draw time: the
        mod-3 count of below-cards drawn before w, subtracted from
        O(w). Final state aliased directly onto the lane literals."""
        if w in self._lane_cache:
            return self._lane_cache[w]
        prev = [self.TRUE_lit(), self.FALSE_lit(), self.FALSE_lit()]
        j = 0
        for z in self.deck_order:
            if self.pos[z] >= self.pos[w]:
                break
            I = self._dlt(z, w)
            cur = [self.lit(("laneS", w, j, k)) for k in range(3)]
            for k in range(3):
                kp = (k - 1) % 3
                # cur[k] <-> (I & prev[kp]) | (~I & prev[k])
                self.emit([-I, -prev[kp], cur[k]])
                self.emit([I, -prev[k], cur[k]])
                self.emit([-cur[k], I, prev[k]])
                self.emit([-cur[k], -I, prev[kp]])
            prev = cur
            j += 1
        lits = [prev[(self.pos[w] - l) % 3] for l in range(3)]
        self._lane_cache[w] = lits
        return lits

    def _max_lit(self, w):
        """w is the max remaining card at its draw."""
        if w in self._max_cache:
            return self._max_cache[w]
        a = self.lit(("maxd", w))
        for z in self.deck_order:
            if self.pos[z] > self.pos[w]:
                self.emit([-a, self._dlt(z, w)])
        self._max_cache[w] = a
        return a

    # ---- the exact pace --------------------------------------------------

    def _pace3(self):
        if self.draw_step < 2:
            return
        deck = self.deck_order
        pos = self.pos
        lanes = {c: self._lane_lits(c) for c in deck}

        for w in deck:
            lw = lanes[w]
            # first(w): every other card drawn after w
            first = self.lit(("firstd", w))
            for z in deck:
                if z != w:
                    self.emit([-first, self._dlt(w, z)])
            self.emit([-first, self._max_lit(w), lw[2]])
            # the disjunction: first | max | lane2 | some certified P
            clause = [first, self._max_lit(w), lw[2]]
            for x in deck:
                if x == w:
                    continue
                p = self.lit(("P", x, w))
                # p -> x immediately before w (adjacency)
                self.emit([-p, self._dlt(x, w)])
                for z in deck:
                    if z != x and z != w:
                        self.emit([-p, -self._dlt(x, z), -self._dlt(z, w)])
                # p -> lane(w) = lane(x) - 1 (mod 3)
                lx = lanes[x]
                for k in range(3):
                    self.emit([-p, -lx[k], lw[(k + 2) % 3]])
                # p -> the burial interval when O(w) < O(x)
                if pos[w] < pos[x]:
                    for z in deck[pos[w]:pos[x]]:
                        if z != w:
                            self.emit([-p, self._dlt(z, x)])
                clause.append(p)
            self.emit(clause)


# ---- evaluation -------------------------------------------------------------


def evaluate(seed: int, draw: int):
    game = Game.from_str(deal_from_seed(seed))
    t0 = time.perf_counter()
    m = Rung3(game, draw)
    t_enc = time.perf_counter() - t0
    sat, t_sat = m.solve()
    oracle = run_cli("solve", "default", str(seed), str(draw))
    return {
        "oracle": "WIN" if "Solvable" in oracle else "LOSE",
        "model": "SAT" if sat else "UNSAT",
        "n_ev": m.n,
        "n_cl": len(m.clauses),
        "t_enc": t_enc,
        "t_sat": t_sat,
    }


# ---- acceptance test ---------------------------------------------------------


def accept(seed: int, draw: int):
    """Pin the oracle's TRUE winning line — the fired-event order plus
    every occurrence choice — into the rung-3 CNF and expect SAT. This
    is the direct soundness test: the model must accept the real
    schedule itself, not merely possess some phantom model. Lines that
    use worry-backs (StackPile) are reported separately: the W=0 model
    maps them only via the C2 worry-back-elimination port."""
    from check_line import parse_line
    game = Game.from_str(deal_from_seed(seed))
    moves = parse_line(run_cli("solve", "default", str(seed), str(draw)))
    m = Rung3(game, draw)
    order = []
    pins = []
    revealed = set()
    for name, c in moves:
        c = iid(c)
        if name == "DeckPile":
            order.append(m.ARR[c])
            pins.append(m.occA(c))
        elif name == "Reveal":
            order.append(m.R[c])
            revealed.add(c)
            pins.append(m.occR(c))
        elif name == "DeckStack":
            order.append(m.DEP[c])
            pins.append(-m.occA(c))
        elif name == "PileStack":
            order.append(m.DEP[c])
            if c in m.deck:
                pins.append(m.occA(c))
            elif c not in revealed:
                pins.append(-m.occR(c))  # departed straight from the surface
        elif name == "StackPile":
            return "WORRY-BACK", None
    for a, b in zip(order, order[1:]):
        pins.append(m.lt_lit(a, b))
    with Cadical153(bootstrap_with=m.clauses) as s:
        return "OK", bool(s.solve(assumptions=pins))


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "18"
    if mode == "accept":
        ok = worry = fail = 0
        for seed in range(12, 76):
            for draw in (1, 3):
                out = run_cli("solve", "default", str(seed), str(draw))
                if "Solvable" not in out:
                    continue
                tag, sat = accept(seed, draw)
                if tag == "WORRY-BACK":
                    worry += 1
                elif sat:
                    ok += 1
                else:
                    fail += 1
                    print(f"seed {seed} d{draw}: ACCEPT FAIL — the true line "
                          f"is rejected by the model", flush=True)
        print(f"acceptance: {ok} true lines accepted, {fail} rejected, "
              f"{worry} worry-back lines (C2-dependent, untested)")
        return
    if mode == "corpus":
        args = [int(x) for x in sys.argv[2:4]]
        lo, hi = args if args else [12, 75]
        kill = agree = total_loss = 0
        for seed in range(lo, hi + 1):
            for draw in (1, 3):
                r = evaluate(seed, draw)
                if r["oracle"] == "LOSE":
                    total_loss += 1
                    if r["model"] == "UNSAT":
                        kill += 1
                    print(f"seed={seed} d{draw} LOSE model={r['model']} "
                          f"[{r['t_enc']:.2f}s+{r['t_sat']:.2f}s]", flush=True)
                elif r["model"] == "UNSAT":
                    print(f"seed={seed} d{draw} *** UNSOUND: WIN but UNSAT ***",
                          flush=True)
                else:
                    agree += 1
        print(f"\nrung-3: {kill}/{total_loss} losses killed, "
              f"{agree} wins SAT (sound if no UNSOUND above)")
        return
    seed = int(mode)
    draw = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    r = evaluate(seed, draw)
    print(r)


if __name__ == "__main__":
    main()
