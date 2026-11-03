"""Re-find the saturated-below hit and dump everything needed to kernel-check it."""
import sys, random
from collections import deque
sys.path.insert(0, 'Temp')
from Search_lib import (c_step, c_moves, c_component, rungs_of, c_show,
                        c_live, c_can_raise_set, c_saturated, c_cargo_closure,
                        fmt)
from Falsify_sat_below2 import walk_state, scan


def path_between(order, succ, src, dst):
    """Shortest move path src -> dst inside the component (c_moves are witness)."""
    prev = {src: None}
    q = deque([src])
    while q:
        u = q.popleft()
        if u == dst:
            break
        for m in c_moves(u):
            v = c_step(u, m)
            if v is not None and v not in prev:
                prev[v] = (u, m)
                q.append(v)
    if dst not in prev:
        return None
    out = []
    cur = dst
    while prev[cur] is not None:
        u, m = prev[cur]
        out.append(m)
        cur = u
    return list(reversed(out))


def main():
    rng = random.Random(1)
    found = None
    for _ in range(3000):
        cst = walk_state(rng)
        if cst is None:
            continue
        try:
            order, sat, hit = scan(cst)
        except RuntimeError:
            continue
        if hit:
            found = (order, sat, hit)
            break
    if not found:
        print('no hit')
        return
    order, sat, (u, ru, v, rv) = found
    print('rungs(s)  =', ru)
    print("rungs(s') =", rv)
    print('rung_le:', all(a <= b for a, b in zip(ru, rv)), ' strict:',
          ru != rv)
    print('saturated(s):', c_saturated(u))
    print('cargo fibre of s size:', len(c_cargo_closure(u)))
    print('vanilla live at s:', sorted(c_can_raise_set(u)))
    print()
    print('--- s (compact):')
    print('rungs =', u[0])
    for i, (hb, run) in enumerate(u[1]):
        if hb or run:
            print(' p%d hidden=%s run=%s' % (i, hb, run))
    print()
    print("--- s' (compact):")
    print('rungs =', v[0])
    for i, (hb, run) in enumerate(v[1]):
        if hb or run:
            print(' p%d hidden=%s run=%s' % (i, hb, run))
    print()
    p = path_between(order, None, u, v)
    print('witness path s -> s\' (%d moves):' % (len(p) if p else -1))
    if p:
        cur = u
        for m in p:
            print('   ', fmt(m))
            cur = c_step(cur, m)
        print('   ends at s\':', cur == v)


if __name__ == '__main__':
    main()
