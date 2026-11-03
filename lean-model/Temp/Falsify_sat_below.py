"""Decisive falsifier for (R) over raiseS letters.

If a component contains a state `s` that is **S-saturated** (no `CanRaiseS` at
all: `c_live` empty) and also a state `s'` with `RungLe s s'` and
`rungs s' != rungs s`, then (R) fails immediately: from a saturated state no
`RaiseStepS` letter exists, so the only raiseS-only path is the empty one, whose
rung tuple is `rungs s`.

This is much cheaper than the full raise-reachability check and it is exactly
the sharpest way (R) can break.
"""
import sys, random, time
sys.path.insert(0, 'Temp')
from Search_lib import (c_step, c_moves, c_component, rungs_of, c_show,
                        c_live, c_can_raise_set, c_saturated)
from Falsify_rungreach import random_state, rung_le


def walk_state(rng, steps=6):
    cst = random_state(rng)
    if cst is None:
        return None
    for _ in range(rng.randrange(0, steps)):
        ms = c_moves(cst)
        if not ms:
            break
        v = c_step(cst, rng.choice(ms))
        if v is None:
            break
        cst = v
    return cst


def scan_component(cst, cap=400):
    order, _ = c_component(cst, cap=cap)
    sat = [u for u in order if c_saturated(u)]
    out = []
    for u in sat:
        ru = rungs_of(u)
        for v in order:
            rv = rungs_of(v)
            if rung_le(ru, rv) and rv != ru:
                out.append((u, ru, v, rv))
                break
    return order, sat, out


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    budget = int(sys.argv[2]) if len(sys.argv) > 2 else 400
    rng = random.Random(seed)
    t0 = time.time()
    checked = 0
    hits = 0
    n_sat = 0
    while checked < budget and time.time() - t0 < 600:
        cst = walk_state(rng)
        if cst is None:
            continue
        try:
            order, sat, out = scan_component(cst)
        except RuntimeError:
            continue
        checked += 1
        n_sat += len(sat)
        if out:
            hits += 1
            u, ru, v, rv = out[0]
            print('=' * 66)
            print('SATURATED-BELOW-COUSIN: rungs(sat) =', ru, '  rungs(other) =', rv)
            print('--- saturated s:')
            print(c_show(u))
            print('--- class-mate s\' (strictly above in some suit):')
            print(c_show(v))
            print('component size', len(order), '; saturated states', len(sat))
            if hits >= 3:
                break
    print('components checked', checked, '; saturated states seen', n_sat,
          '; hits', hits, '; %.1fs' % (time.time() - t0))


if __name__ == '__main__':
    main()
