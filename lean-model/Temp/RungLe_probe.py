"""RungLe_probe.py — the corrected componentwise (R) probe.

Statement tested, exactly:

  (R)  sameOrbit s s'  and  RungLe s s'  (componentwise: forall suit,
       rungAt s suit <= rungAt s' suit)
       ==> some raiseS-only *licensed* play from s ends at rungs = rungs s'.

`raiseS` letters (`RaiseStepS` + the `RaiseSSeqLicensed` licence in
Orig2/Fork/Class/ForkRaiseReorder.lean):
   one letter = cargo slides (reversible tabToTab) to expose c, then a raise
   of c that is licensed (CanRaiseS).  At WF, licensed = reversible, so the
   letter set is the compact model's `tabToTab` moves together with its
   `tabToFound` moves.  NO `foundToTab` (pulls), NO `draw`.

Consequences used:
  * slides preserve rungs, so `raiseS` reachability of rung tuples is the
    closure under {slides, licensed raises};
  * at an S-saturated state no raise is licensed anywhere in its slide fibre,
    so the only raiseS-reachable rung tuple is the state's own.

Generator corrected: face-up runs are descending bottom-first
(`can_sit_on(c,b) := c.rank + 1 == b.rank`).  Every seed is filtered through
`Search_lib.to_full`, which asserts the model's `WF`.
"""
import sys, random, time
sys.path.insert(0, 'Temp')
from collections import deque, defaultdict
from Search_lib import (c_step, c_moves, c_saturated, c_live, c_can_raise_set,
                        rungs_of, c_show, to_full, fmt)


# ---------------------------------------------------------------- WF filter
def wf_ok(cst):
    """`to_full` asserts WF; use it as the oracle and swallow failures."""
    try:
        to_full(cst)
        return True
    except Exception:
        return False


# ---------------------------------------------------------------- order
def rung_le(a, b):
    return all(x <= y for x, y in zip(a, b))


# ---------------------------------------------------------------- graph
def reach(src, cap=20000):
    seen = {src}
    q = deque([src])
    while q:
        u = q.popleft()
        for m in c_moves(u):
            v = c_step(u, m)
            if v is not None and v not in seen:
                seen.add(v)
                q.append(v)
                if len(seen) > cap:
                    raise RuntimeError('cap')
    return seen


def succ_all(u):
    out = []
    for m in c_moves(u):
        v = c_step(u, m)
        if v is not None:
            out.append(v)
    return out


def succ_raiseS(u):
    """Licensed raiseS letters: slides + licensed (= reversible) raises."""
    out = []
    for m in c_moves(u):
        if m[0] in ('tabToTab', 'tabToFound'):
            v = c_step(u, m)
            if v is not None:
                out.append(v)
    return out


def raiseS_rungs(src, succ):
    """Rung tuples reachable from `src` by raiseS-only plays (slides free)."""
    seen = {src}
    stack = [src]
    rs = set()
    while stack:
        u = stack.pop()
        rs.add(rungs_of(u))
        for v in succ[u]:
            if v not in seen:
                seen.add(v)
                stack.append(v)
    return frozenset(rs)


def is_symmetric(R, sample=None):
    states = list(R)
    if sample is not None and len(states) > sample:
        states = states[:sample]
    for u in states:
        ms = c_moves(u)
        for m in ms:
            v = c_step(u, m)
            if v is None:
                continue
            if not any(c_step(v, m2) == u for m2 in c_moves(v)):
                return False
    return True


# ---------------------------------------------------------------- generator
def run_ok(run):
    return all(run[i + 1][0] + 1 == run[i][0] and
               (run[i + 1][1] // 2) != (run[i][1] // 2)
               for i in range(len(run) - 1))


def legal_runs(rng, nruns, maxlen, rankmax):
    """Descending bottom-first runs: run[i+1] sits on run[i]."""
    piles = []
    for _ in range(nruns):
        if rng.random() < 0.08:
            piles.append((rng.random() < 0.5, ()))
            continue
        r = rng.randrange(1, rankmax)
        run = [(r, rng.randrange(4))]
        for _ in range(rng.randrange(maxlen)):
            r2 = r - 1
            if r2 < 0:
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
    if not all(run_ok(run) for _h, run in ps):
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


# ---------------------------------------------------------------- analysis
def analyse(seed, cap=20000, check_sym=False, full_test=True):
    R = reach(seed, cap=cap)
    if check_sym and not is_symmetric(R):
        raise AssertionError('asymmetric edge (non-WF state?)')

    allmoves = {u: c_moves(u) for u in R}
    n_pull = sum(1 for u in R for m in allmoves[u] if m[0] == 'foundToTab')

    sat = [u for u in R if c_saturated(u)]
    by_rungs = defaultdict(list)
    for u in R:
        by_rungs[rungs_of(u)].append(u)
    rungtups = list(by_rungs)
    has_strict = any(a != b and rung_le(a, b)
                     for a in rungtups for b in rungtups)

    # ---- (i) saturated source test: any comparable strictly-higher mate?
    sat_hits = []
    for u in sat:
        ru = rungs_of(u)
        for rv in rungtups:
            if rv == ru:
                continue
            if rung_le(ru, rv):
                sat_hits.append((u, ru, by_rungs[rv][0], rv))
                break

    # ---- (ii) full (R): every s (non-saturated in the strict form), every
    #          comparable mate rung tuple must be raiseS-reachable
    rung_hits = []
    n_checked = n_reachable = n_unreachable = 0
    sat_lemma_bad = 0
    max_reach = 0
    if full_test:
        succ = {u: [v for m in allmoves[u]
                    if m[0] in ('tabToTab', 'tabToFound')
                    for v in [c_step(u, m)] if v is not None]
                for u in R}
        # sanity lemma: a saturated state has no licensed raise anywhere in its
        # slide fibre, so its raiseS rung set is exactly {own rungs}
        for u in sat:
            rs_u = raiseS_rungs(u, succ)
            max_reach = max(max_reach, len(rs_u))
            if rs_u != frozenset({rungs_of(u)}):
                sat_lemma_bad += 1
        for s in R:
            if s in sat:
                continue                      # covered by (i)
            rs = rungs_of(s)
            reachset = raiseS_rungs(s, succ)
            max_reach = max(max_reach, len(reachset))
            for rv in rungtups:
                if rv == rs or not rung_le(rs, rv):
                    continue
                n_checked += 1
                if rv in reachset:
                    n_reachable += 1
                else:
                    n_unreachable += 1
                    if len(rung_hits) < 8:
                        rung_hits.append((s, rs, by_rungs[rv][0], rv, reachset))
    return {
        'size': len(R),
        'sat': sat,
        'n_pull': n_pull,
        'has_strict': has_strict,
        'sat_hits': sat_hits,
        'rung_hits': rung_hits,
        'n_checked': n_checked,
        'n_reachable': n_reachable,
        'n_unreachable': n_unreachable,
        'sat_lemma_bad': sat_lemma_bad,
        'max_reach': max_reach,
        'rungtups': sorted(rungtups),
    }


def play_between(R, a, b):
    """A shortest reversible play a -> b inside the orbit (BFS parents)."""
    par = {a: (None, None)}
    q = deque([a])
    while q:
        u = q.popleft()
        if u == b:
            break
        for m in c_moves(u):
            v = c_step(u, m)
            if v is not None and v not in par:
                par[v] = (u, m)
                q.append(v)
    if b not in par:
        return None
    out = []
    cur = b
    while cur != a:
        p, m = par[cur]
        out.append(m)
        cur = p
    return list(reversed(out))


def main():
    # the two known instance families (s1 from BoundaryForkFree; A the second
    # family found by the vacuity sweep)
    from SatDiffer_sweep import s1, dip_states
    campaign = s1
    second = ((0, 1, 4, 3), (
        (False, ((5, 2), (4, 0))),                 # 6S 5H
        (True, ((5, 3), (4, 1), (3, 3), (2, 1))),  # # 6C 5D 4C 3D
        (False, ((5, 1), (4, 3), (3, 1))),         # 6D 5C 4D
        (True, ()),                                # # hidden only
        (False, ((10, 3), (9, 0))),                # JC TH
        (False, ()),
        (False, ()),
    ))

    print("=" * 74)
    print("(a) campaign orbit (397 states)")
    print("=" * 74)
    inf = analyse(campaign, cap=20000, check_sym=True, full_test=True)
    print("  |orbit|", inf['size'], " saturated", len(inf['sat']),
          " rung tuples", len(inf['rungtups']),
          " pull letters", inf['n_pull'], " strict pair:", inf['has_strict'])
    print("  saturated strict-comparable hits:", len(inf['sat_hits']))
    for u, ru, v, rv in inf['sat_hits']:
        print("    HIT", ru, "<= ", rv)
        print("     u:", c_show(u))
        print("     v:", c_show(v))
    print("  full-(R) failures:", len(inf['rung_hits']),
          " (checked", inf['n_checked'], "source/target rung pairs;",
          inf['n_reachable'], "reachable,", inf['n_unreachable'], "unreachable)")
    print("  saturated raiseS-rung lemma violations:", inf['sat_lemma_bad'],
          " max raiseS rung set:", inf['max_reach'])

    print()
    print("=" * 74)
    print("(b) second family (44 states)")
    print("=" * 74)
    inf2 = analyse(second, cap=20000, check_sym=True, full_test=True)
    print("  |orbit|", inf2['size'], " saturated", len(inf2['sat']),
          " rung tuples", len(inf2['rungtups']),
          " pull letters", inf2['n_pull'], " strict pair:", inf2['has_strict'])
    print("  saturated strict-comparable hits:", len(inf2['sat_hits']))
    for u, ru, v, rv in inf2['sat_hits']:
        print("    HIT", ru, "<= ", rv)
        print("     u:", c_show(u))
        print("     v:", c_show(v))
    print("  full-(R) failures:", len(inf2['rung_hits']),
          " (checked", inf2['n_checked'], "source/target rung pairs;",
          inf2['n_reachable'], "reachable,", inf2['n_unreachable'], "unreachable)")
    print("  saturated raiseS-rung lemma violations:", inf2['sat_lemma_bad'],
          " max raiseS rung set:", inf2['max_reach'])

    # ---- random sweep
    budget = int(sys.argv[1]) if len(sys.argv) > 1 else 900
    seed0 = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    cap = int(sys.argv[3]) if len(sys.argv) > 3 else 4000
    rng = random.Random(seed0)

    print()
    print("=" * 74)
    print(f"(c) random WF-valid components (target {budget})")
    print("=" * 74)
    t0 = time.time()
    attempts = accepted_seeds = checked = 0
    n_states = n_sat = 0
    n_sat_hits = n_rung_hits = 0
    n_checked_pairs = n_reachable = n_unreachable = 0
    n_sat_lemma_bad = 0
    n_pull_comps = n_strict_comps = 0
    max_reach = 0
    maxcomp = 0
    printed = 0
    while checked < budget and time.time() - t0 < 1200:
        cst = walk_state(rng)
        attempts += 1
        if cst is None:
            continue
        if not wf_ok(cst):
            continue
        accepted_seeds += 1
        try:
            inf = analyse(cst, cap=cap, check_sym=(checked % 50 == 0),
                          full_test=True)
        except (RuntimeError, AssertionError):
            continue
        checked += 1
        n_states += inf['size']
        n_sat += len(inf['sat'])
        n_checked_pairs += inf['n_checked']
        n_reachable += inf['n_reachable']
        n_unreachable += inf['n_unreachable']
        n_sat_lemma_bad += inf['sat_lemma_bad']
        if inf['n_pull']:
            n_pull_comps += 1
        if inf['has_strict']:
            n_strict_comps += 1
        max_reach = max(max_reach, inf['max_reach'])
        maxcomp = max(maxcomp, inf['size'])
        if inf['sat_hits']:
            n_sat_hits += len(inf['sat_hits'])
            for u, ru, v, rv in inf['sat_hits'][:1]:
                print("SAT-HIT", ru, "<= " , rv)
                print("   u:", c_show(u))
                print("   v:", c_show(v))
        if inf['rung_hits']:
            n_rung_hits += len(inf['rung_hits'])
            if printed < 5:
                printed += 1
                s, rs, v, rv, reachset = inf['rung_hits'][0]
                print("RUNG-HIT source rungs", rs, " target", rv)
                print("   s:", c_show(s))
                print("   v:", c_show(v))
                print("   raiseS rungs from s:", sorted(reachset))
        if checked % 100 == 0:
            print(f"  ... {checked} components, {n_states} states, "
                  f"{n_sat} sat, sat_hits={n_sat_hits}, "
                  f"rung_hits={n_rung_hits}, %.0fs" % (time.time() - t0))

    print()
    print("COVERAGE (WF-valid random):")
    print("  seed attempts          :", attempts)
    print("  seeds surviving WF     :", accepted_seeds,
          f"({100.0*accepted_seeds/max(1,attempts):.1f}%)")
    print("  components analysed    :", checked)
    print("  pull-bearing components:", n_pull_comps)
    print("  components with a strict comparable pair:", n_strict_comps)
    print("  max component size     :", maxcomp)
    print("  total states           :", n_states)
    print("  saturated states       :", n_sat)
    print("  source/target rung pairs checked:", n_checked_pairs,
          " (reachable", n_reachable, ", unreachable", n_unreachable, ")")
    print("  saturated raiseS-rung lemma violations:", n_sat_lemma_bad)
    print("  max raiseS rung-set size:", max_reach)
    print("  saturated strict-comparable HITS :", n_sat_hits)
    print("  full-(R) rung-reach FAILURES     :", n_rung_hits)
    print("  %.1fs" % (time.time() - t0))


if __name__ == '__main__':
    main()
