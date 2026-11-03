"""RaisesOrFork_probe_s2.py -- empirical test of the one-sided raise-or-fork claim.

(This is a self-contained second copy: another concurrent session owns
Temp/RaisesOrFork_probe.py, so this probe uses its own filename.)

CLAIM (one-sided raise-or-fork).  For any two orbit mates s, t:

  either  some raiseS-only licensed play goes from s to a state v with
          rungs(v) >= rungs(t)  (componentwise; incomparable targets allowed),
  or      the whole orbit class of s is forked.

`raiseS` = slide-star (reversible tabToTab closure) followed by ONE licensed
rise (tabToFound); no foundToTab pulls, no draws.  In the compact model the
letter set is therefore `{tabToTab, tabToFound}`.

Because slides preserve rungs, raiseS reachability of rung tuples is computed
on the SLIDE FIBRES: node = cargo/slide fibre (rungs fixed), edge = a licensed
raise from some state of the fibre.  A raise strictly increases one rung, so
this quotient is acyclic and the per-fibre reachable-rung set is a finite
memoised DFS.  `c_live(F)` (used by forkState) is replaced by the union of the
direct raise sets over F's cargo/slide fibre, which is exactly what c_live
computes (cross-checked on samples against Search_lib.c_live).

Fork detection (exactly the wording of the brief):
  forkState(F)  iff  c_live(F) == {x, twin(x)}  and  x.twin not in
  c_can_raise_set(F).  `Fork s` iff a class mate has forkState.

Generator: the CORRECTED descending bottom-first generator of
Temp/RungLe_probe.py (every seed filtered through Search_lib.to_full, so only
WF states survive).  Campaign orbit: s1 of Temp/SatDiffer_sweep.py.  High-rung
seeds: RungLe_probe_hi.walk_hi.

Scratch.  READ-ONLY on Orig2/ and on existing Temp scripts.
"""
import sys
import time
from collections import defaultdict

sys.path.insert(0, 'Temp')

from Search_lib import (c_step, c_moves, c_component, c_fibers,
                        c_can_raise_set, c_live, c_show, rungs_of)
from RungLe_probe import walk_state, wf_ok
from SatDiffer_sweep import s1

# second independent instance family of Temp/SatDiffer_vacuity_Report.md (A/B)
SECOND = ((0, 1, 4, 3), (
    (False, ((5, 2), (4, 0))),                  # 6S 5H
    (True, ((5, 3), (4, 1), (3, 3), (2, 1))),   # # 6C 5D 4C 3D
    (False, ((5, 1), (4, 3), (3, 1))),          # 6D 5C 4D
    (True, ()),                                 # # hidden only
    (False, ((10, 3), (9, 0))),                 # JC TH
    (False, ()),
    (False, ()),
))


# ---------------------------------------------------------------- helpers

def rung_le(a, b):
    return all(x <= y for x, y in zip(a, b))


def maxima(tuples):
    """Pareto maxima of a set of rung tuples (only those can dominate)."""
    ts = sorted(set(tuples))
    out = []
    for a in ts:
        if not any(b != a and rung_le(a, b) for b in ts):
            out.append(a)
    return out


def twin_of(c):
    return (c[0], c[1] ^ 1)


def fibre_live(fibre):
    L = set()
    for u in fibre:
        L |= c_can_raise_set(u)
    return frozenset(L)


def fork_witnesses(fibre, L):
    """Exact forkState members of one slide fibre.

    forkState(F) needs c_live(F) == {x, twin(x)} and twin(x) not in the
    *direct* raise set at F.  Both choices of x are tested.
    """
    if len(L) != 2:
        return []
    a, b = sorted(L)
    if not (a[0] == b[0] and (a[1] ^ 1) == b[1]):
        return []
    out = []
    for u in fibre:
        direct = c_can_raise_set(u)
        if b not in direct:          # x = a, twin = b
            out.append((u, a))
        if a not in direct:          # x = b, twin = a
            out.append((u, b))
    return out


# ---------------------------------------------------------------- analysis

def analyse_component(seed, cap=6000, check_live_cross=False):
    """Full raiseS / fork analysis of one mutual orbit.

    Returns a dict; raises RuntimeError on the component cap.
    """
    order, succ = c_component(seed, cap=cap)
    fibres, fid = c_fibers(order, succ)

    live = [fibre_live(f) for f in fibres]

    forks = []
    for i, f in enumerate(fibres):
        forks.extend(fork_witnesses(f, live[i]))
    forked = bool(forks)

    if forks:
        # direct c_live check on one witness of every forked component
        F, _x = forks[0]
        assert live[fid[F]] == c_live(F), (
            'fork witness c_live mismatch', c_show(F),
            sorted(live[fid[F]]), sorted(c_live(F)))

    if check_live_cross:
        # the fibre union must equal c_live (cargo closure) on a sample
        for i in range(min(3, len(fibres))):
            u = fibres[i][0]
            assert live[i] == c_live(u), (
                'fibre live != c_live', c_show(u), sorted(live[i]),
                sorted(c_live(u)))

    # raise graph on fibres
    nf = len(fibres)
    fedge = [set() for _ in range(nf)]
    n_raise_letters = 0
    for u in order:
        for c in c_can_raise_set(u):
            v = c_step(u, ('tabToFound', c))
            if v is None:
                continue
            n_raise_letters += 1
            fedge[fid[u]].add(fid[v])

    memo = {}

    def reach_rungs(i):
        if i in memo:
            return memo[i]
        out = {rungs_of(fibres[i][0])}
        for j in fedge[i]:
            out |= reach_rungs(j)
        memo[i] = out
        return out

    reach = [frozenset(reach_rungs(i)) for i in range(nf)]
    reachmax = [maxima(reach[i]) for i in range(nf)]

    # Group target states by rung tuple: ok(s, t) depends only on fid[s] and
    # rungs(t), so every ordered pair is decided, once per (fibre, tuple) class.
    rung_states = defaultdict(list)
    for u in order:
        rung_states[rungs_of(u)].append(u)
    rt_list = list(rung_states)
    comp_maxima = maxima(rt_list)

    fails = []            # representative failing pairs
    fail_classes = []     # (fibre index, target rung tuple, pair count)
    fail_count = 0
    for i in range(nf):
        ms = reachmax[i]
        for rt in rt_list:
            if not any(rung_le(rt, m) for m in ms):
                c = len(fibres[i]) * len(rung_states[rt])
                fail_count += c
                fail_classes.append((i, rt, c))
                if len(fails) < 20:
                    s = fibres[i][0]
                    fails.append((s, rungs_of(s), rung_states[rt][0], rt))

    return {
        'order': order,
        'fibres': fibres,
        'fid': fid,
        'live': live,
        'forks': forks,
        'forked': forked,
        'reach': reach,
        'reachmax': reachmax,
        'fails': fails,
        'fail_classes': fail_classes,
        'fail_count': fail_count,
        'comp_maxima': comp_maxima,
        'n_pairs': len(order) * len(order),
        'n_states': len(order),
        'n_fibres': nf,
        'n_raise_letters': n_raise_letters,
        'n_pull': sum(1 for u in order for m, _v in succ[u]
                      if m[0] == 'foundToTab'),
        'max_reach': max(len(x) for x in reach) if reach else 0,
    }


# ---------------------------------------------------------------- reporting

def dump_pair(s, rs, t, rt, inf):
    print('  FAILURE PAIR')
    print('    rungs s =', rs, ' rungs t =', rt)
    print('    s:', c_show(s))
    print('    t:', c_show(t))
    print('    reachable raiseS rung tuples from s:',
          sorted(inf['reach'][inf['fid'][s]]))
    print('    raiseS rung maxima from s:',
          inf['reachmax'][inf['fid'][s]])


def run_family(name, seeds, cap, stats, time_limit, check_live_cross=False,
               quiet_every=1000):
    t0 = time.time()
    start = {k: stats[k] for k in ('comps', 'states', 'pairs',
                                   'forked_comps', 'fails', 'fails_bare',
                                   'multimax_comps')}
    for seed in seeds:
        if time.time() - t0 > time_limit:
            print(f'  [{name}] time limit hit after {stats["comps"]} comps')
            break
        try:
            inf = analyse_component(
                seed, cap=cap,
                check_live_cross=(check_live_cross and stats['comps'] < 20))
        except (RuntimeError, AssertionError) as e:
            stats['skipped'] += 1
            if isinstance(e, AssertionError):
                stats['sanity_bad'] += 1
                print('  SANITY FAILURE:', e)
            continue
        stats['comps'] += 1
        stats['states'] += inf['n_states']
        stats['pairs'] += inf['n_pairs']
        stats['sat_states'] += sum(1 for u in inf['order']
                                   if not inf['live'][inf['fid'][u]])
        stats['pull_bearing'] += inf['n_pull'] > 0
        stats['forked_comps'] += inf['forked']
        stats['forks'] += len(inf['forks'])
        stats['max_reach'] = max(stats['max_reach'], inf['max_reach'])
        stats['max_comp'] = max(stats['max_comp'], inf['n_states'])
        stats['max_fibres'] = max(stats['max_fibres'], inf['n_fibres'])
        if len(inf['comp_maxima']) >= 2:
            stats['multimax_comps'] += 1
            if inf['forked']:
                stats['multimax_forked'] += 1
            if inf['fail_count']:
                stats['multimax_fail_comps'] += 1
            stats['mm_records'].append({
                'family': name,
                'size': inf['n_states'],
                'fibres': inf['n_fibres'],
                'maxima': inf['comp_maxima'],
                'forked': inf['forked'],
                'fork_count': len(inf['forks']),
                'fail_count': inf['fail_count'],
                'fork_example': inf['forks'][0] if inf['forks'] else None,
                'fail_example': inf['fails'][0] if inf['fails'] else None,
            })
        if inf['forked'] and name not in ('campaign', 'second'):
            F, x = inf['forks'][0]
            if len(stats['fork_examples']) < 6:
                stats['fork_examples'].append(
                    (name, F, x, inf['live'][inf['fid'][F]], rungs_of(F)))
        if inf['fail_count']:
            stats['fail_comps'] += 1
            stats['fails'] += inf['fail_count']
            if inf['forked']:
                stats['fail_comps_forked'] += 1
                stats['fails_forked'] += inf['fail_count']
            else:
                stats['fail_comps_bare'] += 1
                stats['fails_bare'] += inf['fail_count']
                print(f'  *** BARE FAILURE (component NOT forked) in {name}')
                print('      component:', inf['n_states'], 'states,',
                      inf['n_fibres'], 'fibres,',
                      inf['fail_count'], 'failing ordered pairs,',
                      len(inf['fail_classes']), 'fail classes,',
                      'live sets:', [sorted(x) for x in inf['live']][:8])
                for f in inf['fails'][:2]:
                    dump_pair(*f, inf)
        if stats['comps'] % quiet_every == 0:
            print(f'  ... {name}: {stats["comps"]} comps, '
                  f'{stats["states"]} states, {stats["pairs"]} pairs, '
                  f'fails={stats["fails"]} '
                  f'(forked {stats["fails_forked"]}, '
                  f'bare {stats["fails_bare"]}), '
                  f'{time.time() - t0:.0f}s')
    stats['per_family'][name] = {k: stats[k] - start[k] for k in start}


def gen_random(n, rng_seed, walk_depth=12):
    import random
    rng = random.Random(rng_seed)
    out = []
    while len(out) < n:
        cst = walk_state(rng, depth=walk_depth)
        if cst is None:
            continue
        if not wf_ok(cst):
            continue
        out.append(cst)
    return out


def gen_high(n, rng_seed):
    import random
    from RungLe_probe_hi import walk_hi
    rng = random.Random(rng_seed)
    out = []
    while len(out) < n:
        cst = walk_hi(rng)
        if cst is None:
            continue
        if not wf_ok(cst):
            continue
        out.append(cst)
    return out


def new_stats():
    return defaultdict(int)


def main():
    budget = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    hi_budget = int(sys.argv[2]) if len(sys.argv) > 2 else 150
    cap = int(sys.argv[3]) if len(sys.argv) > 3 else 6000
    tlimit = int(sys.argv[4]) if len(sys.argv) > 4 else 1500

    print('=' * 76)
    print('one-sided raise-or-fork probe')
    print('=' * 76)

    stats = new_stats()
    stats['mm_records'] = []
    stats['fork_examples'] = []
    stats['per_family'] = {}

    # (a) campaign orbit of s1 / t1, plus the second SatDiffer family
    print('\n--- (a) campaign orbit (s1) + second family (A) ---')
    run_family('campaign', [s1], cap=cap, stats=stats, time_limit=600,
               check_live_cross=True, quiet_every=10)
    run_family('second', [SECOND], cap=cap, stats=stats, time_limit=600,
               check_live_cross=True, quiet_every=10)

    # (b) random components, corrected generator, independent RNG seeds
    print('\n--- (b) random WF components ---')
    for rng_seed, n in [(1, budget), (7, budget), (2026, budget // 2),
                        (31337, budget // 2), (424242, budget // 2)]:
        seeds = gen_random(n, rng_seed)
        print(f'  rng {rng_seed}: generated {len(seeds)} WF seeds')
        run_family(f'random-{rng_seed}', seeds, cap=cap, stats=stats,
                   time_limit=tlimit, check_live_cross=False)

    # (c) high-rung seeds
    print('\n--- (c) high-rung WF components ---')
    for rng_seed, n in [(4242, hi_budget), (987654, hi_budget),
                        (555, hi_budget // 2)]:
        seeds_hi = gen_high(n, rng_seed)
        print(f'  rng {rng_seed}: generated {len(seeds_hi)} high-rung WF seeds')
        run_family(f'high-{rng_seed}', seeds_hi, cap=cap, stats=stats,
                   time_limit=tlimit, check_live_cross=False)

    print('\n' + '=' * 76)
    print('TOTALS')
    print('=' * 76)
    print('  components checked        :', stats['comps'])
    print('  states                    :', stats['states'])
    print('  ordered pairs checked     :', stats['pairs'])
    print('  S-saturated states        :', stats['sat_states'])
    print('  pull-bearing components   :', stats['pull_bearing'])
    print('  forked components         :', stats['forked_comps'])
    print('  fork witness states       :', stats['forks'])
    print('  max component size        :', stats['max_comp'])
    print('  max fibres per component  :', stats['max_fibres'])
    print('  max raiseS rung set       :', stats['max_reach'])
    print('  components with >=2 Pareto-maximal rung tuples:',
          stats['multimax_comps'],
          f'(forked {stats["multimax_forked"]}, '
          f'with ok-failures {stats["multimax_fail_comps"]})')
    print('  components with ok-failure:', stats['fail_comps'])
    print('  FAILURES of ok            :', stats['fails'])
    print('    in forked components    :', stats['fails_forked'],
          f'({stats["fail_comps_forked"]} comps)')
    print('    in NON-forked components:', stats['fails_bare'],
          f'({stats["fail_comps_bare"]} comps)')
    print('  skipped components        :', stats['skipped'],
          '(sanity:', stats['sanity_bad'], ')')

    print('\n--- per family ---')
    print('  family              comps    states        pairs  forked  failures  bare')
    for name, d in stats['per_family'].items():
        print(f'  {name:<18} {d["comps"]:>6} {d["states"]:>9} '
              f'{d["pairs"]:>12} {d["forked_comps"]:>7} '
              f'{d["fails"]:>9} {d["fails_bare"]:>5}')

    print('\n--- every component with >=2 Pareto-maximal rung tuples ---')
    for r in stats['mm_records']:
        print(f"  [{r['family']}] {r['size']} states, {r['fibres']} fibres, "
              f"maxima={r['maxima']}")
        print(f"    forked={r['forked']} fork-states={r['fork_count']} "
              f"ok-failures={r['fail_count']}")
        if r['fork_example']:
            F, x = r['fork_example']
            print(f"    fork witness: x={x} twin={twin_of(x)} "
                  f"live={sorted([x, twin_of(x)])} at rungs {rungs_of(F)}")
            print(f"      {c_show(F)}")
        if r['fail_example']:
            s, rs, t, rt = r['fail_example']
            print(f"    failure example: s rungs {rs} vs t rungs {rt}")
            print(f"      s: {c_show(s)}")
            print(f"      t: {c_show(t)}")

    print('\n--- fork witnesses outside the two known families ---')
    for name, F, x, L, rs in stats['fork_examples']:
        print(f'  [{name}] rungs {rs} x={x} live={sorted(L)}')
        print('   ', c_show(F))

    print('\n  verdict:', ('CLAIM SURVIVES' if stats['fails_bare'] == 0
                         else 'CLAIM REFUTED'))


if __name__ == '__main__':
    main()
