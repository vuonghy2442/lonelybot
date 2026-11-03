"""Same sweep, but with `sameOrbitSetoid` as the *symmetric* closure.

`c_component` is a directed reachability over `c_moves`; the orbit is the pair
`v in reach(u) and u in reach(v)`.  (The earlier hit was one-way: a pull with no
reversible inverse reachable from the saturated side, so it is not an orbit
mate at all.)

Failure mode tested: an orbit mate pair (u saturated, v above it in rungs).
"""
import sys, random, time
from collections import deque
sys.path.insert(0, 'Temp')
from Search_lib import c_step, c_moves, c_saturated, rungs_of, c_show
from Falsify_sat_below2 import walk_state


def rung_le(a, b):
    return all(x <= y for x, y in zip(a, b))


def reach(src, cap=400):
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


def scan(cst):
    R = reach(cst)
    # only states mutually reachable with cst are orbit mates of cst; for the
    # pair test we need the mutual relation inside R
    reach_cache = {cst: R}
    sat = []
    for u in R:
        try:
            Ru = reach_cache.get(u) or reach(u)
        except RuntimeError:
            continue
        reach_cache[u] = Ru
        if c_saturated(u):
            sat.append(u)
    hits = []
    for u in sat:
        ru = rungs_of(u)
        Ru = reach_cache[u]
        for v in R:
            if v not in Ru:
                continue          # one-way: not an orbit mate
            rv = rungs_of(v)
            if rung_le(ru, rv) and rv != ru:
                hits.append((u, ru, v, rv))
                break
    return len(R), sat, hits


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    budget = int(sys.argv[2]) if len(sys.argv) > 2 else 120
    rng = random.Random(seed)
    t0 = time.time()
    checked = n_sat = hits = 0
    maxcomp = 0
    while checked < budget and time.time() - t0 < 900:
        cst = walk_state(rng)
        if cst is None:
            continue
        try:
            size, sat, hs = scan(cst)
        except RuntimeError:
            continue
        checked += 1
        maxcomp = max(maxcomp, size)
        n_sat += len(sat)
        if hs:
            hits += 1
            u, ru, v, rv = hs[0]
            print('=' * 66)
            print('ORBIT HIT: saturated rungs', ru, ' vs orbit mate rungs', rv)
            print(c_show(u))
            print('--- mate:')
            print(c_show(v))
            if hits >= 3:
                break
    print('checked', checked, 'components; max size', maxcomp,
          '; saturated seen', n_sat, '; orbit hits', hits,
          '; %.1fs' % (time.time() - t0))


if __name__ == '__main__':
    main()
