"""Falsify (R), correctly stated:

  sameOrbit s s'  and  RungLe s s'   =>   there is a *raiseS*-only licensed path
  from s to a state with rungs(s').

A `raiseS` letter is "slide-star, then one licensed raise" (the campaign's
`RaiseStepS`), i.e. slides are allowed but pulls and draws are not.  `Search_lib`
gives: `c_cargo_closure` (slide star), `c_can_raise_set` (vanilla licence), and
`c_component` (the orbit, witness moves only = `sameOrbitSetoid`).
"""
import sys, time, random
from collections import deque

sys.path.insert(0, 'Temp')
from Search_lib import (c_step, c_moves, c_cargo_closure, c_can_raise_set,
                        c_component, rungs_of, c_show, c_live)


def raiseS_succs(u, cap=4000):
    """States reachable from u by slide-star + one licensed raise."""
    out = []
    for z in c_cargo_closure(u, limit=cap):
        for c in c_can_raise_set(z):
            v = c_step(z, ('tabToFound', c))
            if v is not None:
                out.append(v)
    return out


def raiseS_rungs(cst, cap_nodes=4000, cap_cargo=4000):
    """Rung tuples reachable from cst by a raiseS-only licensed path."""
    seen = {cst}
    out = {rungs_of(cst)}
    q = deque([cst])
    while q:
        u = q.popleft()
        for v in raiseS_succs(u, cap=cap_cargo):
            if v in seen:
                continue
            seen.add(v)
            out.add(rungs_of(v))
            q.append(v)
            if len(seen) > cap_nodes:
                raise RuntimeError('raiseS cap')
    return out


def rung_le(a, b):
    return all(x <= y for x, y in zip(a, b))


def check(cst, comp_cap=800):
    try:
        order, _succ = c_component(cst, cap=comp_cap)
    except RuntimeError:
        return None
    try:
        reach = raiseS_rungs(cst)
    except RuntimeError:
        return None
    rs = rungs_of(cst)
    bad = []
    for s2 in order:
        r2 = rungs_of(s2)
        if rung_le(rs, r2) and r2 not in reach:
            bad.append((s2, r2))
    return bad, reach


# ---------------------------------------------------------------- generators

def legal_runs(rng, nruns=3, maxlen=3, rankmax=6):
    piles = []
    for _ in range(nruns):
        if rng.random() < 0.1:
            piles.append((rng.random() < 0.5, ()))
            continue
        r = rng.randrange(0, rankmax)
        run = [(r, rng.randrange(4))]
        for _ in range(rng.randrange(maxlen)):
            r2 = r + 1
            if r2 > rankmax:
                break
            suits = [s for s in range(4) if (s // 2) != (run[-1][1] // 2)]
            r = r2
            run.append((r, rng.choice(suits)))
        piles.append((rng.random() < 0.3, tuple(run)))
    return tuple(piles)


def random_state(rng, rankmax=7):
    rungs = tuple(rng.randrange(0, 2) for _ in range(4))
    run_piles = legal_runs(rng, nruns=rng.randrange(4, 8), maxlen=4, rankmax=rankmax)
    ps = run_piles + tuple((False, ()) for _ in range(7 - len(run_piles)))
    cards = [c for _h, run in ps for c in run]
    if len(set(cards)) != len(cards):
        return None
    if any(c[0] < rungs[c[1]] for c in cards):
        return None
    return (rungs, ps)


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    t0 = time.time()
    rng = random.Random(seed)
    found = checked = 0
    for _ in range(n):
        cst = random_state(rng)
        if cst is None:
            continue
        r = check(cst)
        if r is None:
            continue
        bad, reach = r
        checked += 1
        if bad:
            found += 1
            s2, r2 = bad[0]
            print('=' * 70)
            print("COUNTEREXAMPLE  rungs(s) =", rungs_of(cst), " rungs(s') =", r2)
            print('--- s:')
            print(c_show(cst))
            print("--- s':")
            print(c_show(s2))
            print('raiseS-reachable rungs from s:', sorted(reach))
            print('live at s (vanilla):', sorted(c_can_raise_set(cst)))
            print('#counterexamples in component:', len(bad))
            if found >= 5:
                break
        if time.time() - t0 > 900:
            print('time budget reached')
            break
    print('checked', checked, 'states;', found, 'with counterexamples;',
          '%.1fs' % (time.time() - t0))


main()
