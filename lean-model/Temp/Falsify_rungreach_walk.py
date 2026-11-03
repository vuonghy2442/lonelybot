import sys, random, time
sys.path.insert(0, 'Temp')
from Search_lib import (c_step, c_moves, c_component, rungs_of, c_show,
                        c_can_raise_set, c_cargo_closure)
from Falsify_rungreach import check, random_state, raiseS_rungs, rung_le


def walk_state(rng):
    cst = random_state(rng)
    if cst is None:
        return None
    for _ in range(rng.randrange(0, 6)):
        ms = c_moves(cst)
        if not ms:
            break
        m = rng.choice(ms)
        v = c_step(cst, m)
        if v is None:
            break
        cst = v
    return cst


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 11
    budget = int(sys.argv[2]) if len(sys.argv) > 2 else 300
    rng = random.Random(seed)
    t0 = time.time()
    checked = 0
    found = 0
    sizes = []
    while checked < budget and time.time() - t0 < 600:
        cst = walk_state(rng)
        if cst is None:
            continue
        try:
            order, _ = c_component(cst, cap=600)
        except RuntimeError:
            continue
        sizes.append(len(order))
        try:
            r = check(cst)
        except RuntimeError:
            continue
        if r is None:
            continue
        bad, reach = r
        checked += 1
        if bad:
            found += 1
            s2, r2 = bad[0]
            print('=' * 60)
            print('COUNTEREXAMPLE  rungs(s) =', rungs_of(cst), ' rungs(s\') =', r2)
            print(c_show(cst))
            print('--- s\':')
            print(c_show(s2))
            print('raiseS-reachable rungs:', sorted(reach))
            print('vanilla live at s:', sorted(c_can_raise_set(cst)))
            if found >= 3:
                break
    print('checked', checked, 'states; component max/avg',
          max(sizes) if sizes else 0,
          '%.1f' % (sum(sizes) / max(1, len(sizes))),
          '; counterexamples:', found)


if __name__ == '__main__':
    main()
