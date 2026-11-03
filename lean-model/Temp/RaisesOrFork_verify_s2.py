"""RaisesOrFork_verify_s2.py -- independent checks for the s2 probe.

1. State-level raiseS reachability (literal BFS: for each state u, take its
   cargo/slide closure and fire every licensed raise) must equal the
   fibre-quotient reach set used by the probe, for sample components.

2. Fork witnesses of the two named families must satisfy the brief's
   definition with `c_live` computed directly from the cargo closure:
   c_live(F) == {x, twin(x)} and twin(x) not in c_can_raise_set(F).

3. The campaign failure pair must really have no dominating raiseS endpoint.
"""
import sys
from collections import deque

sys.path.insert(0, 'Temp')

from Search_lib import (c_step, c_cargo_closure, c_can_raise_set, c_live,
                        rungs_of, c_show)
from RaisesOrFork_probe_s2 import (analyse_component, rung_le, twin_of,
                                   SECOND, gen_random, gen_high)
from SatDiffer_sweep import s1

CAP = 6000


def raiseS_reach_states(src):
    """Literal raiseS BFS: slides are taken as the cargo closure at u, then one
    licensed raise.  Returns (rung-tuple set, number of states visited)."""
    seen = {src}
    q = deque([src])
    rs = set()
    while q:
        u = q.popleft()
        rs.add(rungs_of(u))
        for z in c_cargo_closure(u):
            for c in c_can_raise_set(z):
                v = c_step(z, ('tabToFound', c))
                if v is not None and v not in seen:
                    seen.add(v)
                    q.append(v)
    return frozenset(rs), len(seen)


def check_component(tag, st, max_states=4):
    inf = analyse_component(st, cap=CAP)
    order = inf['order']
    # choose: a saturated state, the largest-reach state, and a few others
    picks = []
    sat = [u for u in order if not inf['live'][inf['fid'][u]]]
    if sat:
        picks.append(sat[0])
    by_reach = sorted(order, key=lambda u: -len(inf['reach'][inf['fid'][u]]))
    picks.append(by_reach[0])
    for u in order:
        if len(picks) >= max_states:
            break
        if u not in picks:
            picks.append(u)

    ok = 0
    for u in picks:
        r_bf, nstates = raiseS_reach_states(u)
        r_fib = inf['reach'][inf['fid'][u]]
        if r_bf != r_fib:
            print(f'  MISMATCH [{tag}] rungs {rungs_of(u)}')
            print('    BFS :', sorted(r_bf))
            print('    fib :', sorted(r_fib))
            print('    state:', c_show(u))
            raise SystemExit(1)
        ok += 1
    # every fibre's live union must equal c_live (cargo closure) of its states
    nfib = 0
    for i, f in enumerate(inf['fibres']):
        if inf['live'][i] != c_live(f[0]):
            print(f'  LIVE MISMATCH [{tag}] fibre {i}',
                  sorted(inf['live'][i]), sorted(c_live(f[0])))
            raise SystemExit(1)
        nfib += 1
    # fork witnesses: direct c_live check on every one in this component
    nfk = 0
    for F, x in inf['forks']:
        L = c_live(F)
        if L != frozenset({x, twin_of(x)}):
            print(f'  FORK MISMATCH [{tag}] c_live != {{x,twin}}', sorted(L), x)
            raise SystemExit(1)
        if twin_of(x) in c_can_raise_set(F):
            print(f'  FORK MISMATCH [{tag}] twin is directly raisable', x)
            raise SystemExit(1)
        nfk += 1
    print(f'  [{tag}] {inf["n_states"]} states, {inf["n_fibres"]} fibres: '
          f'{ok} state-level reach checks OK, {nfib} fibre-live checks OK, '
          f'{nfk} fork witnesses OK')


def check_failure_pair(tag, st):
    inf = analyse_component(st, cap=CAP)
    if not inf['fails']:
        print(f'  [{tag}] no failure pair')
        return
    s, rs, t, rt = inf['fails'][0]
    r_bf, _ = raiseS_reach_states(s)
    bad = [v for v in r_bf if rung_le(rt, v)]
    print(f'  [{tag}] failure s={rs} t={rt}: state-level raiseS reach '
          f'{sorted(r_bf)}')
    print(f'    endpoints dominating t: {bad if bad else "NONE"}')
    assert not bad, 'probe reported a failure but BFS found a dominating endpoint'


def main():
    print('== 1/3. named families ==')
    check_component('campaign', s1)
    check_component('second', SECOND)

    print('== 2. random (rng 31337) components ==')
    seeds = gen_random(6, 31337)
    for i, cst in enumerate(seeds):
        check_component(f'rand31337-{i}', cst, max_states=2)

    print('== 3. high-rung (rng 555) components ==')
    seeds = gen_high(3, 555)
    for i, cst in enumerate(seeds):
        check_component(f'high555-{i}', cst, max_states=2)

    print('== 4. failure-pair cross-checks ==')
    check_failure_pair('campaign', s1)
    check_failure_pair('second', SECOND)
    seeds = gen_high(20, 555)
    done = 0
    for i, cst in enumerate(seeds):
        inf = analyse_component(cst, cap=CAP)
        if inf['fails']:
            check_failure_pair(f'high555-{i}', cst)
            done += 1
            if done >= 2:
                break

    print('ALL VERIFICATION CHECKS PASSED')


if __name__ == '__main__':
    main()
