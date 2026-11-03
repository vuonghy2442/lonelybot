"""Bigger sweep for the raiseS form of (R), via the sharpest failure mode:

  a component containing an S-saturated state `s` and a class-mate `s'` with
  `RungLe s s'` and `rungs s' != rungs s`.

That refutes (R) outright: from a saturated state no raiseS letter exists
(`RaiseStepS` needs `CanRaiseS`), so the only raiseS-only path is empty.

The suspected mechanism (twin pull): pull `d.twin` from the foundation, slide
`d`'s cover onto it, raise `d`, then slide the cover onto the opposite-colour
rank partner and re-raise `d.twin`.  Net: +1 in `d`'s suit, 0 in the twin's.
The generator below is tuned to make such states likely: low rungs, many piles,
long runs, a long reversible walk from the seed.
"""
import sys, random, time
sys.path.insert(0, 'Temp')
from Search_lib import (c_step, c_moves, c_component, rungs_of, c_show,
                        c_live, c_can_raise_set, c_saturated)


def rung_le(a, b):
    return all(x <= y for x, y in zip(a, b))


def legal_runs(rng, nruns, maxlen, rankmax):
    piles = []
    for _ in range(nruns):
        if rng.random() < 0.08:
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
        piles.append((rng.random() < 0.25, tuple(run)))
    return tuple(piles)


def seed_state(rng, rankmax=12):
    rungs = tuple(rng.randrange(0, 4) for _ in range(4))
    run_piles = legal_runs(rng, rng.randrange(5, 8), 6, rankmax)
    ps = run_piles + tuple((False, ()) for _ in range(7 - len(run_piles)))
    cards = [c for _h, run in ps for c in run]
    if len(set(cards)) != len(cards):
        return None
    if any(c[0] < rungs[c[1]] for c in cards):
        return None
    return (rungs, ps)


def walk_state(rng, depth=12):
    cst = seed_state(rng)
    if cst is None:
        return None
    for _ in range(rng.randrange(0, depth)):
        ms = c_moves(cst)
        if not ms:
            break
        v = c_step(cst, rng.choice(ms))
        if v is None:
            break
        cst = v
    return cst


def scan(cst, cap=500):
    order, _ = c_component(cst, cap=cap)
    sat = [u for u in order if c_saturated(u)]
    for u in sat:
        ru = rungs_of(u)
        for v in order:
            rv = rungs_of(v)
            if rung_le(ru, rv) and rv != ru:
                return order, sat, (u, ru, v, rv)
    return order, sat, None


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    budget = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    rng = random.Random(seed)
    t0 = time.time()
    checked = 0
    n_sat = 0
    hits = 0
    maxcomp = 0
    while checked < budget and time.time() - t0 < 900:
        cst = walk_state(rng)
        if cst is None:
            continue
        try:
            order, sat, hit = scan(cst)
        except RuntimeError:
            continue
        checked += 1
        maxcomp = max(maxcomp, len(order))
        n_sat += len(sat)
        if hit:
            hits += 1
            u, ru, v, rv = hit
            print('=' * 66)
            print('HIT: saturated rungs', ru, ' class-mate rungs', rv)
            print('--- saturated s:')
            print(c_show(u))
            print("--- class-mate s':")
            print(c_show(v))
            print('component', len(order), 'saturated in it:', len(sat))
            if hits >= 3:
                break
    print('checked', checked, 'components; max size', maxcomp,
          '; saturated seen', n_sat, '; hits', hits,
          '; %.1fs' % (time.time() - t0))


if __name__ == '__main__':
    main()
