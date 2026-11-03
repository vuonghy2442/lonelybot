"""Look for (R)'s failure inside *forked* components.

(R) over raiseS letters fails if a saturated state `u` has an orbit mate `v`
with `RungLe u v` and `rungs v != rungs u` (from a saturated state no raiseS
letter exists, so only the empty raiseS path exists).

So: search components for (a) saturated states with differing rungs, and
(b) whether the component is forked (`forkState`: the S-live spectrum contains a
whole twin pair while one of them is not vanilla-raisable).
"""
import sys, random, time
from collections import deque
sys.path.insert(0, 'Temp')
from Search_lib import (c_step, c_moves, c_saturated, rungs_of, c_show,
                        c_live, c_can_raise_set)
from Falsify_sat_below2 import walk_state


def reach(src, cap=600):
    seen = {src}
    q = deque([src])
    while q:
        x = q.popleft()
        for m in c_moves(x):
            y = c_step(x, m)
            if y is not None and y not in seen:
                seen.add(y)
                q.append(y)
                if len(seen) > cap:
                    raise RuntimeError('cap')
    return seen


def twin_of(c):
    return (c[0], c[1] ^ 1)


def is_forked(states):
    for F in states:
        live = c_live(F)
        vanilla = c_can_raise_set(F)
        for x in live:
            if twin_of(x) in live and twin_of(x) not in vanilla:
                return (F, x, live)
    return None


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    budget = int(sys.argv[2]) if len(sys.argv) > 2 else 80
    rng = random.Random(seed)
    t0 = time.time()
    checked = forked = 0
    hits = 0
    while checked < budget and time.time() - t0 < 900:
        cst = walk_state(rng)
        if cst is None:
            continue
        try:
            R = reach(cst)
        except RuntimeError:
            continue
        checked += 1
        sat = [u for u in R if c_saturated(u)]
        rungs = sorted({rungs_of(u) for u in sat})
        fk = is_forked(list(R))
        if fk is None:
            continue
        forked += 1
        if len(rungs) > 1:
            hits += 1
            print('=' * 66)
            print('FORKED component with', len(rungs), 'distinct saturated rungs')
            print('rungs:', rungs)
            F, x, live = fk
            print('fork witness state:')
            print(c_show(F))
            print('x =', x, ' live =', sorted(live))
            if hits >= 3:
                break
    print('checked', checked, 'components;', forked, 'forked;',
          hits, 'forked with rung-different saturated states;',
          '%.1fs' % (time.time() - t0))


if __name__ == '__main__':
    main()
