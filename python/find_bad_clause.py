"""Find the falsified clause: build the intended model from the engine's
realized winning line, propagate every aux by semantics, and report any
clause of the Rung-1 encoding it violates."""
import sys

from graph import Card, Game, RANKS
from sat_scheduler import deal_from_seed
from check_line import parse_line
from unsat_gates import Rung1, iid, KING, MASK52, KING_MASK
from sat_scheduler import run_cli


def realize_events(seed):
    """The engine's line as (order, occR, occA) + a state-replay that can
    answer queries about the moment of each event."""
    game = Game.from_str(deal_from_seed(seed))
    moves = parse_line(run_cli("solve", "default", str(seed), "1"))
    piles = [list(h) + list(v) for h, v in game.tableau]
    surface = [len(p) - 1 for p in piles]
    deck = set(game.deck)
    found = [0] * 4
    vis = set(p[-1] for p in piles)

    order = []   # list of (kind, internal_id)
    occR, occA = set(), set()
    for i, (name, c0) in enumerate(moves):
        c = c0
        ci = iid(c0)
        if name == "DeckStack":
            deck.remove(c)
            found[c.suit] += 1
            order.append(("dep", ci))
        elif name == "PileStack":
            vis.discard(c)
            found[c.suit] += 1
            pi = next((j for j, s in enumerate(surface) if s >= 0 and piles[j][s] == c), None)
            if pi is not None:
                surface[pi] -= 1
                if surface[pi] >= 0:
                    vis.add(piles[pi][surface[pi]])
            order.append(("dep", ci))
        elif name == "DeckPile":
            deck.remove(c)
            vis.add(c)
            occA.add(ci)
            order.append(("arr", ci))
        elif name == "Reveal":
            pi = next(j for j, s in enumerate(surface) if s >= 0 and piles[j][s] == c)
            surface[pi] -= 1
            if surface[pi] >= 0:
                vis.add(piles[pi][surface[pi]])
            occR.add(ci)
            order.append(("rev", ci))
    assert all(h == 13 for h in found)
    return game, order, occR, occA


def from_iid_str(i):
    from unsat_gates import from_iid
    c = from_iid(i)
    return f"{RANKS[c.rank]}{'HDCS'[c.suit]}"


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 18
    game, order, occR, occA = realize_events(seed)
    m = Rung1(game)

    # map model events to positions; unoccurred events go at the end
    pos = {}
    t = 0
    for kind, c in order:
        if kind == "dep":
            pos[m.DEP[c]] = t
        elif kind == "arr":
            pos[m.ARR[c]] = t
        else:
            pos[m.R[c]] = t
        t += 1
    for X in m.R:
        if X not in occR:
            pos[m.R[X]] = t
            t += 1
    for X in m.ARR:
        if X not in occA:
            pos[m.ARR[X]] = t
            t += 1
    for X in m.DEP:
        if m.DEP[X] not in pos:
            pos[m.DEP[X]] = t
            t += 1

    def occR_v(X):
        return X in occR

    def occA_v(X):
        return X in occA

    def lt_v(a, b):
        return pos[a] < pos[b]

    def val(lit_):
        # decode via the pool's reverse map
        key = m.pool.id2obj[abs(lit_)]
        v = evaluate(key)
        return v if lit_ > 0 else not v

    cache = {}

    def evaluate(key):
        if key in cache:
            return cache[key]
        cache[key] = False  # guard recursion
        tag = key[0]
        if tag == "lt":
            v = lt_v(key[1], key[2])
        elif tag == "occR":
            v = occR_v(key[1])
        elif tag == "occA":
            v = occA_v(key[1])
        elif tag == "TRUE":
            v = True
        elif tag == "FALSE":
            v = False
        elif tag == "popA":
            X, e = key[1], key[2]
            v = (occR_v(X) and lt_v(m.R[X], e)) or ((not occR_v(X)) and lt_v(m.DEP[X], e))
        elif tag == "vis":
            Y, e = key[1], key[2]
            ab = m.above.get(Y)
            d = m.DEP[Y]
            if Y not in m.above:
                v = occA_v(Y) and lt_v(m.ARR[Y], e) and not lt_v(d, e)
            elif ab is None:
                v = not lt_v(d, e)
            else:
                v = evaluate(("popA", ab, e)) and not lt_v(d, e)
        elif tag == "free":
            Y, e = key[1], key[2]
            if Y not in m.above:
                v = evaluate(("vis", Y, e))
            else:
                v = evaluate(("vis", Y, e)) and evaluate(("popA", Y, e))
        elif tag == "top":
            Y, e = key[1], key[2]
            is_king = Y // 4 == KING
            v = evaluate(("vis", Y, e)) and (
                is_king or not evaluate(("popA", Y, e))
            )
        elif tag == "bm":
            rank, col, e = key[1], key[2], key[3]

            def cardvis(rk, s):
                return evaluate(("vis", rk * 4 + 2 * col + s, e))

            def cardfree(rk, s):
                return evaluate(("free", rk * 4 + 2 * col + s, e))

            v0, v1 = cardvis(rank, 0), cardvis(rank, 1)
            if rank > 0:
                f0, f1 = cardfree(rank - 1, 0), cardfree(rank - 1, 1)
                inner = (v0 != v1) != (f0 != f1) or not (f0 or f1)
                v = inner and (v0 or v1)
            else:
                v = v0 or v1
        elif tag in ("and", "or", "xor"):
            a, b = key[1], key[2]
            va = val(a)
            vb = val(b)
            if tag == "and":
                v = va and vb
            elif tag == "or":
                v = va or vb
            else:
                v = va != vb
        elif tag == "cnt":
            idx, j, e = key[1], key[2], key[3]
            # recompute: at least j among the inputs up to idx — the input
            # list isn't stored; approximate via the counter's semantics:
            v = None  # unused: handled below
            v = False
        elif tag == "fp":
            v = None
        else:
            v = None
        if v is None:
            v = False
        cache[key] = v
        return v

    # fp/cnt need the input lists — evaluate them separately with the
    # intended state at each event: brute-force over the order's history
    def vis_set_at(e):
        """Cards visible strictly before event e (by the line's history)."""
        te = pos[e]
        piles = [[iid(c) for c in list(h) + list(v)] for h, v in game.tableau]
        surface = [len(p) - 1 for p in piles]
        vis = set(p[-1] for p in piles)
        for kind, c in order:
            if pos[{"dep": m.DEP, "arr": m.ARR, "rev": m.R}[kind][c]] >= te:
                break
            if kind == "arr":
                vis.add(c)
            elif kind == "rev":
                pi = next(j for j, s in enumerate(surface) if s >= 0 and piles[j][s] == c)
                surface[pi] -= 1
                if surface[pi] >= 0:
                    vis.add(piles[pi][surface[pi]])
            else:
                vis.discard(c)
                pi = next((j for j, s in enumerate(surface) if s >= 0 and piles[j][s] == c), None)
                if pi is not None:
                    surface[pi] -= 1
                    if surface[pi] >= 0:
                        vis.add(piles[pi][surface[pi]])
        return vis, surface

    # override fp evaluation with the true semantics
    def eval_fp(e):
        vis, surface = vis_set_at(e)
        tops = [c for c in vis if c.rank == KING or c in
                {piles[s][s2] for piles, s in [] for s2 in []}]
        # locked = current surfaces
        surfaces = set()
        piles2 = [list(h) + list(v) for h, v in game.tableau]
        # recompute surfaces from the replay
        surf_now = surface
        for pi, s in enumerate(surf_now):
            if s >= 0:
                surfaces.add(piles2[pi][s])
        n = sum(1 for c in vis if c.rank == KING or c in surfaces)
        return n < 7

    # check every clause
    # first: compare bm-lit evaluation vs the pure formula at each pile-card dep
    from unsat_gates import bottom_mask_of, cmask
    def pure_state_at(e):
        vis, surface = vis_set_at(e)
        vm = 0
        for c in vis:
            vm |= 1 << c
        lk = 0
        piles2 = [list(h) + list(v) for h, v in game.tableau]
        for pi, s in enumerate(surface):
            if s >= 0:
                lk |= 1 << iid(piles2[pi][s])
        return vm, lk
    for X in m.pile_cards():
        rank, suit = X // 4, X % 4
        col = suit // 2
        e = m.DEP[X]
        vm, lk = pure_state_at(e)
        pure_bit = (bottom_mask_of(vm, lk) >> X) & 1
        model_bit = evaluate(("bm", rank, col, e))
        if pure_bit != (1 if model_bit else 0):
            print(f"bm DIVERGE card {X} ({from_iid_str(X)}) at DEP: pure={pure_bit} model={model_bit}")
            if X // 4 == 5 and col == 0 or True:
                v0 = evaluate(("vis", rank * 4 + 2 * col + 0, e))
                v1 = evaluate(("vis", rank * 4 + 2 * col + 1, e))
                f0 = evaluate(("free", (rank - 1) * 4 + 2 * col + 0, e)) if rank else None
                f1 = evaluate(("free", (rank - 1) * 4 + 2 * col + 1, e)) if rank else None
                print(f"   model inputs: vis({rank*4+2*col})={v0} vis({rank*4+2*col+1})={v1} "
                      f"free({(rank-1)*4+2*col})={f0} free({(rank-1)*4+2*col+1})={f1}")
                vis_s, _ = vis_set_at(e)
                print(f"   pure vis set: {sorted(from_iid_str(c) for c in vis_s)}")
            break
    bad = 0
    for cl in m.clauses:
        if any(val(l) for l in cl):
            continue
        bad += 1
        if bad == 1:
            k = ("popA", 0, 37)
            print("inner probe: pos[37]=", pos.get(37), "pos[DEP0]=", pos.get(m.DEP[0]),
                  "occR(18)=", occR_v(18),
                  "eval popA(0,37)=", evaluate(k),
                  "lt(DEP0,37)=", lt_v(m.DEP[0], 37))
        if bad <= 10:
            print("VIOLATED:", [m.pool.id2obj.get(abs(l), l) if abs(l) in m.pool.id2obj else l for l in cl])
            k0 = m.pool.id2obj.get(abs(cl[0]))
            if k0 and k0[0] == "bm":
                rank, col, e = k0[1], k0[2], k0[3]
                v0 = evaluate(("vis", rank * 4 + 2 * col + 0, e))
                v1 = evaluate(("vis", rank * 4 + 2 * col + 1, e))
                f0 = evaluate(("free", (rank - 1) * 4 + 2 * col + 0, e)) if rank else None
                f1 = evaluate(("free", (rank - 1) * 4 + 2 * col + 1, e)) if rank else None
                print(f"   bm({rank},{col})@{e}: v0={v0} v1={v1} f0={f0} f1={f1}")
                vis_s, _ = vis_set_at(e)
                print(f"   vis-at-{e}: {sorted(from_iid_str(c) for c in vis_s)}")
    print(f"{bad} violated clauses out of {len(m.clauses)}"
          if bad else "ALL CLAUSES SATISFIED BY THE INTENDED MODEL")


if __name__ == "__main__":
    main()
