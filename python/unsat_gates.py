"""The unsat ladder, rung 1 — rung 0's ordering skeleton + the dynamic
legality gates (bm / free_slot / reveal), W=0.

LAYOUT (the key discovery, from card.rs's suit_xor_color): the engine's
mask index is rank*4 + (suit ^ 2 if rank is odd) — suits are
color-interleaved by rank parity, so +4 in mask space = next rank
OPPOSITE color (increase_rank_swap_color). All mask arithmetic
(bottom_mask_of, free_slot = bm >> 4, ALT_MASK pairs) lives in this
internal space; logical suits (H=0,D=1,C=2,S=3) only appear at the
deal boundary and in output.

Gates, evaluated "just before" each event:
  PileStack(X)   type(X) in bm (bottom_mask_of(vis, locked))
  DeckPile(X)    type(X) in free_slot (bm >> 4; kings: free_pile)
  Reveal(X)      type(X) in free_slot, X a locked surface, not a
                 bottom-layer king
  DeckStack(X)   per-suit prefix only
W=0 (no worry-backs): sound for rejection — fewer options.

UNSAT is sound; SAT proves nothing. The old solver is the oracle.
"""
import sys
import time

from pysat.formula import IDPool
from pysat.solvers import Cadical153

from graph import Card, Game, RANKS
from sat_scheduler import run_cli, deal_from_seed
from check_line import parse_line

KING = len(RANKS) - 1
MASK52 = (1 << 52) - 1
ALT_MASK = 0x5555_5555_5555_5555
KING_MASK = 0xF << (4 * KING)


def iid(card: Card) -> int:
    """Internal (mask-space) index of a logical card."""
    return card.rank * 4 + (card.suit ^ (2 if card.rank & 1 else 0))


def from_iid(i: int) -> Card:
    r = i // 4
    return Card(r, (i % 4) ^ (2 if r & 1 else 0))


def cmask(card: Card) -> int:
    return 1 << iid(card)


def bottom_mask_of(vis, locked):
    """Direct port of state.rs bottom_mask_of (internal-space masks)."""
    free = vis & ~locked & MASK52
    xor_free = free ^ (free >> 1)
    xor_vis = vis ^ (vis >> 1)
    xor_all = xor_vis ^ ((xor_free << 4) & MASK52)
    or_free = free | (free >> 1)
    or_vis = vis | (vis >> 1)
    bottom = (xor_all | (~(or_free << 4) & MASK52)) & or_vis & ALT_MASK
    return (bottom * 0b11) & MASK52


def free_slot_of(bm, free_pile):
    return ((bm >> 4) & MASK52) | (KING_MASK if free_pile else 0)


# ---------------------------------------------------------------------------
# verification: replay the engine's winning line and check every gate
# ---------------------------------------------------------------------------


def verify_line(seed: int):
    game = Game.from_str(deal_from_seed(seed))
    moves = parse_line(run_cli("solve", "default", str(seed), "1"))
    piles = [list(h) + list(v) for h, v in game.tableau]
    surface = [len(p) - 1 for p in piles]
    deck = set(game.deck)
    found = [0] * 4
    vis = 0
    for p in piles:
        vis |= cmask(p[-1])
    first_layer = {p[0] for p in piles if p}
    checks = 0

    def locked_mask():
        m = 0
        for pi, s in enumerate(surface):
            if s >= 0:
                m |= cmask(piles[pi][s])
        return m

    for i, (name, c) in enumerate(moves):
        lk = locked_mask()
        bm = bottom_mask_of(vis, lk)
        fp = bin(vis & (lk | KING_MASK)).count("1") < 7
        fs = free_slot_of(bm, fp)
        t = cmask(c)
        if name == "PileStack":
            assert vis & t, (i, name, c, "not visible")
            assert bm & t, (i, name, c, "bm gate")
            assert found[c.suit] == c.rank, (i, name, c, "prefix")
            vis &= ~t
            found[c.suit] += 1
            pi = next((j for j, s in enumerate(surface) if s >= 0 and piles[j][s] == c), None)
            if pi is not None:
                surface[pi] -= 1
                if surface[pi] >= 0:
                    vis |= cmask(piles[pi][surface[pi]])
            checks += 1
        elif name == "DeckStack":
            assert c in deck and found[c.suit] == c.rank, (i, name, c)
            deck.remove(c)
            found[c.suit] += 1
            checks += 1
        elif name == "DeckPile":
            assert fs & t, (i, name, c, "free_slot gate")
            deck.remove(c)
            vis |= t
            checks += 1
        elif name == "Reveal":
            assert fs & t, (i, name, c, "free_slot gate")
            assert not (c in first_layer and c.rank == KING), (i, name, c)
            pi = next(j for j, s in enumerate(surface) if s >= 0 and piles[j][s] == c)
            surface[pi] -= 1
            if surface[pi] >= 0:
                vis |= cmask(piles[pi][surface[pi]])
            checks += 1
    assert all(h == 13 for h in found)
    print(f"verify seed {seed}: {len(moves)} moves, {checks} gate checks, ALL PASS")


# ---------------------------------------------------------------------------
# the rung-1 SAT model (cards keyed by internal index)
# ---------------------------------------------------------------------------


class Rung1:
    def __init__(self, game: Game, draw_step: int = 1):
        self.game = game
        self.draw_step = draw_step
        self.piles = [[iid(c) for c in list(h) + list(v)] for h, v in game.tableau]
        self.deck = {iid(c) for c in game.deck}
        self.pool = IDPool()
        self.clauses = []

        self.all_cards = set(c for p in self.piles for c in p) | self.deck
        self.above = {}
        for p in self.piles:
            for j, c in enumerate(p):
                self.above[c] = p[j + 1] if j + 1 < len(p) else None
        self.first_layer_kings = {p[0] for p in self.piles if p and p[0] // 4 == KING}

        self.R, self.ARR, self.DEP = {}, {}, {}
        self.ev = []
        for c in self.pile_cards():
            self.R[c] = self._new_ev()
            self.DEP[c] = self._new_ev()
        for c in sorted(self.deck):
            self.ARR[c] = self._new_ev()
            self.DEP[c] = self._new_ev()
        self.n = len(self.ev)

        self._order_vars()
        self._structure()
        self._deck_pace()
        self._gates()

    # ---- basics -----------------------------------------------------------

    def pile_cards(self):
        return [c for p in self.piles for c in p]

    def _new_ev(self):
        self.ev.append(len(self.ev))
        return len(self.ev)

    def lit(self, key):
        return self.pool.id(key)

    def lt_lit(self, a, b):
        if a == b:
            # no event is strictly before itself — the constant FALSE
            f = self.lit(("FALSE",))
            if not self._falsedone:
                self._falsedone.add(True)
                self.clauses.append([-f])
            return f
        if a < b:
            return self.lit(("lt", a, b))
        return -self.lit(("lt", b, a))

    def emit(self, clause):
        if clause:
            self.clauses.append([x for x in clause if x is not None])

    def occR(self, c):
        return self.lit(("occR", c))

    def occA(self, c):
        return self.lit(("occA", c))

    def drawLt(self, X, Y):
        """Aux: deck card X was drawn before deck card Y (draw = the
        arrival if placed, the departure if stacked directly). Only the
        case-split backward clauses are needed: setting the aux true
        forces the order literal for whichever case holds — that is the
        constraint. (The forward direction is omitted deliberately:
        sound for UNSAT, and the units/disjunctions supply the truth.)"""
        key = ("drawLt", X, Y)
        if key in self.pool.id2obj:
            return self.lit(key)
        a = self.lit(key)
        ax, ay = self.occA(X), self.occA(Y)
        rx, dx = self.ARR[X], self.DEP[X]
        ry, dy = self.ARR[Y], self.DEP[Y]
        # a & ax & ay  -> arr_X < arr_Y
        self.emit([-a, -ax, -ay, self.lt_lit(rx, ry)])
        # a & ax & ~ay -> arr_X < dep_Y
        self.emit([-a, -ax, ay, self.lt_lit(rx, dy)])
        # a & ~ax & ay -> dep_X < arr_Y
        self.emit([-a, ax, -ay, self.lt_lit(dx, ry)])
        # a & ~ax & ~ay -> dep_X < dep_Y
        self.emit([-a, ax, ay, self.lt_lit(dx, dy)])
        return a

    def _order_vars(self):
        for a in range(1, self.n + 1):
            for b in range(a + 1, self.n + 1):
                lab = self.lit(("lt", a, b))
                for c in range(b + 1, self.n + 1):
                    lbc = self.lit(("lt", b, c))
                    lac = self.lit(("lt", a, c))
                    self.clauses.append([-lab, -lbc, lac])
                    self.clauses.append([-lac, lab, lbc])

    # ---- aux state literals ----------------------------------------------

    def popA(self, X, e):
        """Aux: X's surface-departure completed strictly before e."""
        key = ("popA", X, e)
        if key in self.pool.id2obj:
            return self.lit(key)
        a = self.lit(key)
        r, d = self.R[X], self.DEP[X]
        o = self.occR(X)
        l1 = self.lt_lit(r, e)
        l2 = self.lt_lit(d, e)
        # a <-> (o & l1) | (~o & l2)
        self.emit([-o, -l1, a])
        self.emit([o, -l2, a])
        self.emit([-a, o, l2])
        self.emit([-a, -o, l1])
        return a

    def vis(self, Y, e):
        """Aux: Y is visible just before e (arrived/revealed AND not yet
        departed — the engine's vis bit clears on stack)."""
        key = ("vis", Y, e)
        if key in self.pool.id2obj:
            return self.lit(key)
        a = self.lit(key)
        d = self.DEP[Y]
        if Y not in self.above:  # deck card
            o = self.occA(Y)
            l = self.lt_lit(self.ARR[Y], e)
            dep = self.lt_lit(d, e)
            # a <-> o & l & ~dep
            self.emit([-o, -l, dep, a])
            self.emit([-a, o])
            self.emit([-a, l])
            self.emit([-a, -dep])
        else:
            ab = self.above[Y]
            dep = self.lt_lit(d, e)
            if ab is None:  # top card: visible from the start
                # a <-> ~dep
                self.emit([dep, a])
                self.emit([-a, -dep])
            else:
                p = self.popA(ab, e)
                # a <-> p & ~dep
                self.emit([-p, dep, a])
                self.emit([-a, p])
                self.emit([-a, -dep])
        return a

    def free(self, Y, e):
        """Aux: Y is visible and unlocked just before e."""
        if Y not in self.above:  # deck card: never locked
            return self.vis(Y, e)
        key = ("free", Y, e)
        if key in self.pool.id2obj:
            return self.lit(key)
        a = self.lit(key)
        p = self.popA(Y, e)
        v = self.vis(Y, e)
        # a <-> v & p
        self.emit([-v, -p, a])
        self.emit([-a, v])
        self.emit([-a, p])
        return a

    # ---- structure ---------------------------------------------------------

    def _structure(self):
        for X in self.pile_cards():
            r, d = self.R[X], self.DEP[X]
            o = self.occR(X)
            self.emit([-o, self.lt_lit(r, d)])
            ab = self.above[X]
            if ab is not None:
                # R fires on the surface: the card above already popped
                self.emit([-o, self.popA(ab, r)])
        for X in self.pile_cards():
            ab = self.above[X]
            if ab is not None:
                self.emit([self.popA(ab, self.DEP[X])])
        for X in self.deck:
            self.emit([-self.occA(X), self.lt_lit(self.ARR[X], self.DEP[X])])
        for X in self.all_cards:
            if X // 4 == 0:
                continue
            # same LOGICAL suit one rank down: the color-interleaved
            # layout makes it X-2 for internal suits {0,1}, X-6 for {2,3}
            lo = X - 2 if (X % 4) < 2 else X - 6
            if lo in self.DEP:
                self.emit([self.lt_lit(self.DEP[lo], self.DEP[X])])

    # ---- deck pace (draw-3+: the K+ cyclic accessibility) ---------------

    def _deck_pace(self):
        """The deck-draw order constraints (engine coordinates: deck[0] =
        bottom/deepest, deck[n-1] = top/first-accessible).

        Brute-force over the exact deck state machine (N=6/9/12, step 3)
        shows the pairwise-forced residue is ONLY the bottom block's
        chain: pos[step-1] < ... < pos[1] < pos[0]. graph.py's pivot
        clauses are NOT implied (a realizable order violates them —
        demonstrated live by seed 56 d3, a win they wrongly reject).
        The deeper rigidity is higher-order (pass counting); capturing
        it needs the exact state machine, not order literals."""
        if self.draw_step <= 1:
            return  # draw-1: free set, no constraints
        step = self.draw_step
        pos = [iid(c) for c in self.game.deck]  # engine order
        n = len(pos)
        for i in range(min(n, step) - 1):
            # the bottom block: drawn top-down, forced
            self.emit([self.drawLt(pos[i + 1], pos[i])])

    # ---- gates ---------------------------------------------------------------

    def bm_lit(self, rank, col, e):
        """Aux: type (rank, col) movable just before e (internal space)."""
        key = ("bm", rank, col, e)
        if key in self.pool.id2obj:
            return self.lit(key)
        out = self.lit(key)
        pool, emit = self.pool, self.emit

        def cardf(rk, s):
            return rk * 4 + 2 * col + s

        def AND(a, b):
            o = pool.id(("and", a, b, key))
            emit([-a, -b, o])
            emit([a, -o])
            emit([b, -o])
            return o

        def OR(a, b):
            o = pool.id(("or", a, b, key))
            emit([a, b, -o])
            emit([-a, o])
            emit([-b, o])
            return o

        def XOR(a, b):
            o = pool.id(("xor", a, b, key))
            emit([a, b, -o])
            emit([-a, -b, -o])
            emit([a, -b, o])
            emit([-a, b, o])
            return o

        v0 = self.vis(cardf(rank, 0), e)
        v1 = self.vis(cardf(rank, 1), e)
        if rank > 0:
            f0b = self.free(cardf(rank - 1, 0), e)
            f1b = self.free(cardf(rank - 1, 1), e)
            xor_fb = XOR(f0b, f1b)
            or_fb = OR(f0b, f1b)
            xor_all = XOR(XOR(v0, v1), xor_fb)
            inner = OR(xor_all, -or_fb)
            both = OR(v0, v1)
            res = AND(inner, both)
        else:
            res = OR(v0, v1)
        emit([res, -out])
        emit([-res, out])
        return out

    _truedone = set()
    _falsedone = set()

    def TRUE_lit(self):
        t = self.lit(("TRUE",))
        if not self._truedone:
            self._truedone.add(True)
            self.clauses.append([t])
        return t

    def free_pile_lit(self, e):
        """Aux: fewer than 7 extended tops (vis & (locked|KING)) before e."""
        key = ("fp", e)
        if key in self.pool.id2obj:
            return self.lit(key)
        out = self.lit(key)
        TRUE = self.TRUE_lit()
        # inputs: per card Y: vis(Y) & (locked(Y) | king(Y))
        #   pile card: vis & (~popA | king); deck card: vis & king
        inputs = []
        for Y in sorted(self.all_cards):
            v = self.vis(Y, e)
            is_king = Y // 4 == KING
            if Y in self.above:
                if is_king:
                    # inp <-> vis (kings count regardless of lock)
                    inputs.append(v)
                else:
                    p = self.popA(Y, e)
                    a = self.lit(("top", Y, e))
                    # a <-> v & ~p
                    self.emit([-v, p, a])
                    self.emit([-a, v])
                    self.emit([-a, -p])
                    inputs.append(a)
            else:
                if not is_king:
                    continue  # non-king deck card: never a top
                inputs.append(v)
        # out <-> at most 6 inputs true (sequential counter)
        # prev[j] = "at least j true so far" (None = FALSE)
        prev = [None] * 8
        prev[0] = TRUE
        for idx, x in enumerate(inputs):
            cur = list(prev)
            for j in range(1, 8):
                pj = prev[j - 1]
                cj = prev[j]
                if pj is None:
                    cur[j] = None  # x & FALSE = FALSE
                elif cj is None:
                    # cur[j] <-> x & pj
                    o = self.lit(("cnt", idx, j, e))
                    self.emit([x, pj, -o])
                    self.emit([o, -x])
                    self.emit([o, -pj])
                    cur[j] = o
                else:
                    # o <-> cj | (x & pj)
                    o = self.lit(("cnt", idx, j, e))
                    self.emit([cj, -o])
                    self.emit([x, pj, -o])
                    self.emit([o, -cj, -x])
                    self.emit([o, -cj, -pj])
                    cur[j] = o
            prev = cur
        ge7 = prev[7]
        if ge7 is None:
            self.emit([out])  # certainly free_pile
        else:
            self.emit([ge7, -out])
            self.emit([out, -ge7])
        return out

    def _gates(self):
        # pile-card departures: bm gate
        for X in self.pile_cards():
            rank, suit = X // 4, X % 4
            col = suit // 2  # internal color class
            self.emit([self.bm_lit(rank, col, self.DEP[X])])
        # deck placements: free_slot gate (only when the arrival occurs —
        # DeckStack-only cards never need it)
        for X in self.deck:
            rank, suit = X // 4, X % 4
            col = suit // 2
            e = self.ARR[X]
            o = self.occA(X)
            if rank == KING:
                self.emit([-o, self.free_pile_lit(e)])
            else:
                self.emit([-o, self.bm_lit(rank + 1, col, e)])
        # reveals: free_slot gate (+ the surface/first-layer parts)
        for X in self.pile_cards():
            o = self.occR(X)
            rank, suit = X // 4, X % 4
            col = suit // 2
            e = self.R[X]
            if X in self.first_layer_kings:
                self.emit([-o])
                continue
            if rank == KING:
                self.emit([-o, self.free_pile_lit(e)])
            else:
                self.emit([-o, self.bm_lit(rank + 1, col, e)])

    def solve(self):
        t0 = time.perf_counter()
        with Cadical153(bootstrap_with=self.clauses) as s:
            r = s.solve()
        return r, time.perf_counter() - t0


def evaluate(seed: int, draw: int):
    game = Game.from_str(deal_from_seed(seed))
    t0 = time.perf_counter()
    m = Rung1(game, draw)
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


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "18"
    if mode == "verify":
        verify_line(int(sys.argv[2]))
        return
    if mode == "corpus":
        lo, hi = int(sys.argv[2]), int(sys.argv[3])
        kill = agree = total_loss = 0
        for seed in range(lo, hi + 1):
            for draw in (1, 3):
                r = evaluate(seed, draw)
                if r["oracle"] == "LOSE":
                    total_loss += 1
                    if r["model"] == "UNSAT":
                        kill += 1
                    print(f"seed={seed} d{draw} LOSE model={r['model']} "
                          f"[{r['t_enc']:.2f}s+{r['t_sat']:.2f}s]")
                elif r["model"] == "UNSAT":
                    print(f"seed={seed} d{draw} *** UNSOUND: WIN but UNSAT ***")
                else:
                    agree += 1
        print(f"\nrung-1: {kill}/{total_loss} losses killed, "
              f"{agree} wins SAT (sound if no UNSOUND above)")
        return
    seed = int(mode)
    draw = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    print(evaluate(seed, draw))


if __name__ == "__main__":
    main()
