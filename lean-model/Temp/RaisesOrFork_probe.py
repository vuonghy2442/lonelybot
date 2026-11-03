"""RaisesOrFork_probe.py -- independent falsification probe for

  raises_or_fork:
    sameOrbit s t  ==>  (exists raiseS-only *licensed* play s ->* v with
                         rungAt v >= rungAt t componentwise)
                        OR Fork s

and, alongside it, the strictly stronger claim (R) that the endpoint reaches
EXACTLY rungs t.

Everything is read off the compact witness model (Search_lib), which is the
vetted projection of the full game (Search_check_projection.py).  The
dictionary to the Lean card is:

  rungAt w s            = (w.found s).length            = rungs_of(w)[s]
  CanRaise st c         = c_step(st, ('tabToFound', c)) fires  = c_can_raise_set
  CanRaiseS st c        = CanRaise at SOME state of the cargo (tabToTab) fibre
  reversibleAtW letter  = exactly the c_moves letters of the compact model
  sameOrbitSetoid.r     = same component of the c_moves graph
  raiseS letter         = slide-star then one licensed raise
                        = an edge of the induced subgraph on
                          {tabToTab, tabToFound}   (slides are free)
  RungLe v w            = all(rungAt v s <= rungAt w s)
  Fork s                = some state F of the component has ForkWitness F x,
                          i.e. its CanRaiseS spectrum is EXACTLY {x, x.twin}
                          and x.twin is not CanRaise-live at F.

The target test is the real statement: for every ordered pair (s,t) in a
component with RungLe s t, either a raiseS-reachable endpoint dominates t,
or the component carries a forkState.

No file under Orig2/ or Temp/*.lean is touched.  Scratch only.
"""
import sys, time, random
sys.path.insert(0, 'Temp')
from collections import deque, defaultdict

from Search_lib import (c_moves, c_step, c_can_raise_set, c_show, rungs_of,
                        to_full)
from valley_probe import twin


# ------------------------------------------------------------------ helpers
def rung_le(a, b):
    return all(x <= y for x, y in zip(a, b))


def component(src, cap=20000):
    """Ordered component of the reversible (witness) graph."""
    seen = {src}
    q = deque([src])
    order = [src]
    succ = {}
    while q:
        u = q.popleft()
        ss = []
        for m in c_moves(u):
            v = c_step(u, m)
            if v is None:
                continue
            ss.append((m, v))
            if v not in seen:
                seen.add(v)
                order.append(v)
                q.append(v)
                if len(seen) > cap:
                    raise RuntimeError('cap')
        succ[u] = ss
    return order, succ


def fibres_and_spectra(order, succ):
    """tabToTab fibres, per-state CanRaise set, per-state CanRaiseS spectrum."""
    par = {u: u for u in order}

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            par[rb] = ra

    for u in order:
        for m, v in succ[u]:
            if m[0] == 'tabToTab':
                union(u, v)
    groups = defaultdict(list)
    for u in order:
        groups[find(u)].append(u)
    canR = {u: c_can_raise_set(u) for u in order}
    spec = {}
    for root, members in groups.items():
        S = set()
        for z in members:
            S |= canR[z]
        for z in members:
            spec[z] = frozenset(S)
    return spec, canR


def fork_witness(canR, spectrum):
    """Return x if ForkWitness F x holds (spectrum == {x, x.twin} and
    x.twin not vanilla-raisable), else None."""
    if len(spectrum) != 2:
        return None
    for x in spectrum:
        xt = (x[0], twin(x[1]))
        if xt in spectrum and xt not in canR:
            return x
    return None


def raiseS_rungs(src, succ):
    """Rung tuples reachable by slides + raises (licensed raises are the
    only tabToFound edges the model admits)."""
    seen = {src}
    stack = [src]
    out = set()
    while stack:
        u = stack.pop()
        out.add(rungs_of(u))
        for m, v in succ[u]:
            if m[0] in ('tabToTab', 'tabToFound') and v not in seen:
                seen.add(v)
                stack.append(v)
    return frozenset(out)


def analyse(order, succ, want_plays=False):
    spec, canR = fibres_and_spectra(order, succ)
    forks = {u: fork_witness(canR, spec[u]) for u in order}
    fork_states = {u: x for u, x in forks.items() if x is not None}
    rungset = sorted({rungs_of(u) for u in order})
    sat = [u for u in order if not spec[u]]

    info = {
        'n': len(order), 'rungset': rungset, 'sat': len(sat),
        'forks': len(fork_states), 'fork_states': fork_states,
        'failures': [], 'exact_failures': [], 'needed_fork': [],
        'sat_below': [], 'pairs': 0, 'exact_ok': 0, 'dom_ok': 0,
        'has_strict': any(a != b and rung_le(a, b)
                          for a in rungset for b in rungset),
    }
    # no saturated state strictly below an orbit mate
    for u in sat:
        ru = rungs_of(u)
        for rv in rungset:
            if rv != ru and rung_le(ru, rv):
                info['sat_below'].append((u, ru, rv))

    reach = {}
    for s in order:
        reach[s] = raiseS_rungs(s, succ)

    for s in order:
        rs = rungs_of(s)
        R = reach[s]
        for rv in rungset:
            if not rung_le(rs, rv):
                continue
            if rv == rs:
                # trivial: s itself (empty play), counted, never a failure
                info['pairs'] += 1
                info['exact_ok'] += 1
                info['dom_ok'] += 1
                continue
            info['pairs'] += 1
            if rv in R:
                info['exact_ok'] += 1
                info['dom_ok'] += 1
            elif any(rung_le(rv, w) for w in R):
                info['dom_ok'] += 1
            elif fork_states:
                info['needed_fork'].append((s, rs, rv))
            else:
                info['failures'].append((s, rs, rv, sorted(R)))
            if rv not in R and not fork_states:
                info['exact_failures'].append((s, rs, rv, sorted(R)))
    return info


def describe(cst):
    return c_show(cst), rungs_of(cst)


# ------------------------------------------------------------------ boards
# campaign s1: F<AH2H3H4H5H  AS2S3S4S  AC2C> with
# P{0:4D3C2D | 1:8D7S | 2:5D4C | 3:6H5C | 4:6C | 5:8S7D | 6:#}
S1 = ((5, 0, 4, 2), (
    (False, ((3, 1), (2, 3), (1, 1))),
    (False, ((7, 1), (6, 2))),
    (False, ((4, 1), (3, 3))),
    (False, ((5, 0), (4, 3))),
    (False, ((5, 3),)),
    (False, ((7, 2), (6, 1))),
    (True, ())))

# second family A from RungLe_probe.py / SatDiffer_dump2.py
SECOND = ((0, 1, 4, 3), (
    (False, ((5, 2), (4, 0))),
    (True, ((5, 3), (4, 1), (3, 3), (2, 1))),
    (False, ((5, 1), (4, 3), (3, 1))),
    (True, ()),
    (False, ((10, 3), (9, 0))),
    (False, ()),
    (False, ())))

# FJ_Report.md 3.0: the minimal missing-join / fork board
#   B : F<AH2H3H AD2D3D AS2S3S>  P{4:5S4D3C | 5:5C4H}
FJMIN = ((3, 3, 3, 0), (
    (False, ()),
    (False, ()),
    (False, ()),
    (False, ()),
    (False, ((4, 2), (3, 1), (2, 3))),
    (False, ((4, 3), (3, 0))),
    (False, ())))


def run_board(name, cst, cap=20000):
    try:
        to_full(cst)
    except Exception as e:
        print(f"  [{name}] WF FAILED: {e}")
        return None
    order, succ = component(cst, cap=cap)
    inf = analyse(order, succ)
    print(f"  [{name}] n={inf['n']} rungvecs={len(inf['rungset'])} "
          f"sat={inf['sat']} forks={inf['forks']} strict={inf['has_strict']}")
    print(f"      pairs={inf['pairs']} exact_ok={inf['exact_ok']} "
          f"dom_ok={inf['dom_ok']} needed_fork={len(inf['needed_fork'])} "
          f"FAILURES={len(inf['failures'])} sat_below={len(inf['sat_below'])}")
    for (s, rs, rv, R) in inf['failures'][:3]:
        print("      FAIL", rs, "->", rv)
        print("        s:", c_show(s))
        print("        reach:", R)
    return inf


# ------------------------------------------------------------------ random
def legal_runs_hi(rng, nruns, maxlen, rungs, rankmax=12):
    piles = []
    for _ in range(nruns):
        if rng.random() < 0.05:
            piles.append((rng.random() < 0.5, ()))
            continue
        s0 = rng.randrange(4)
        if rungs[s0] > rankmax:
            piles.append((False, ()))
            continue
        r = rng.randrange(rungs[s0], rankmax + 1)
        run = [(r, s0)]
        for _ in range(rng.randrange(maxlen)):
            r2 = r - 1
            if r2 < 0:
                break
            suits = [t for t in range(4)
                     if (t // 2) != (run[-1][1] // 2) and r2 >= rungs[t]]
            if not suits:
                break
            r = r2
            t = rng.choice(suits)
            run.append((r, t))
        piles.append((rng.random() < 0.2, tuple(run)))
    return tuple(piles)


def seed_hi(rng, runglo=2, rnghi=6, maxlen=8):
    rungs = tuple(rng.randrange(runglo, rnghi) for _ in range(4))
    run_piles = legal_runs_hi(rng, rng.randrange(5, 8), maxlen, rungs)
    ps = run_piles + tuple((False, ()) for _ in range(7 - len(run_piles)))
    cards = [c for _h, run in ps for c in run]
    if len(set(cards)) != len(cards):
        return None
    if any(c[0] < rungs[c[1]] for c in cards):
        return None
    return (rungs, ps)


def walk_hi(rng, depth=15, runglo=2, rnghi=6, maxlen=8):
    cst = seed_hi(rng, runglo, rnghi, maxlen)
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


def wf_ok(cst):
    try:
        to_full(cst)
        return True
    except Exception:
        return False


def random_sweep(budget, seed0, cap, secs, runglo=2, rnghi=6, maxlen=8):
    rng = random.Random(seed0)
    t0 = time.time()
    n = states = sat = forks = pairs = exact_ok = dom_ok = 0
    needed = fails = satbelow = 0
    pull_comps = strict_comps = 0
    maxn = 0
    while n < budget and time.time() - t0 < secs:
        cst = walk_hi(rng, runglo=runglo, rnghi=rnghi, maxlen=maxlen)
        if cst is None or not wf_ok(cst):
            continue
        try:
            order, succ = component(cst, cap=cap)
        except RuntimeError:
            continue
        if time.time() - t0 > secs:
            break
        inf = analyse(order, succ)
        n += 1
        states += inf['n']
        maxn = max(maxn, inf['n'])
        sat += inf['sat']
        forks += 1 if inf['forks'] else 0
        pairs += inf['pairs']
        exact_ok += inf['exact_ok']
        dom_ok += inf['dom_ok']
        needed += len(inf['needed_fork'])
        fails += len(inf['failures'])
        satbelow += len(inf['sat_below'])
        if inf['has_strict']:
            strict_comps += 1
        if any(m[0] == 'foundToTab' for u in order for m, _ in succ[u]):
            pull_comps += 1
        if inf['failures'] or inf['sat_below'] or inf['needed_fork']:
            print(f"  !! component seed {seed0} #{n}: fails={len(inf['failures'])} "
                  f"sat_below={len(inf['sat_below'])} "
                  f"needed_fork={len(inf['needed_fork'])}")
            for (s, rs, rv, R) in inf['failures'][:2]:
                print("     FAIL", rs, "->", rv)
                print("       s:", c_show(s))
                print("       reach:", R)
    return dict(components=n, states=states, sat=sat, sat_states=forks,
                pairs=pairs, exact_ok=exact_ok, dom_ok=dom_ok,
                needed_fork=needed, failures=fails, sat_below=satbelow,
                pull_comps=pull_comps, strict_comps=strict_comps, maxn=maxn,
                secs=time.time() - t0)


# ------------------------------------------------------------------ exhaustive
def exhaustive(K, maxtab, secs, tag):
    from Search_enum import enum_boards
    deadline = time.time() + secs
    visited = set()
    n = states = pairs = exact_ok = dom_ok = 0
    needed = fails = satbelow = forks = sat = 0
    maxn = 0
    t0 = time.time()
    try:
        for cst in enum_boards(K, maxtab, deadline):
            if time.time() > deadline:
                break
            if cst in visited:
                continue
            try:
                order, succ = component(cst, cap=10000)
            except RuntimeError:
                continue
            visited.update(order)
            inf = analyse(order, succ)
            n += 1
            states += inf['n']
            maxn = max(maxn, inf['n'])
            pairs += inf['pairs']
            exact_ok += inf['exact_ok']
            dom_ok += inf['dom_ok']
            needed += len(inf['needed_fork'])
            fails += len(inf['failures'])
            satbelow += len(inf['sat_below'])
            sat += inf['sat']
            forks += 1 if inf['forks'] else 0
            if inf['failures'] or inf['sat_below'] or inf['needed_fork']:
                print(f"  !! {tag} comp n={inf['n']} fails={len(inf['failures'])} "
                      f"sat_below={len(inf['sat_below'])} "
                      f"needed_fork={len(inf['needed_fork'])}")
                print("     board:", c_show(cst), rungs_of(cst))
                for (s, rs, rv, R) in inf['failures'][:2]:
                    print("     FAIL", rs, "->", rv, " s:", c_show(s))
                    print("       reach:", R)
    except TimeoutError:
        pass
    return dict(tag=tag, components=n, states=states, pairs=pairs,
                exact_ok=exact_ok, dom_ok=dom_ok, needed_fork=needed,
                failures=fails, sat_below=satbelow, forked_comps=forks,
                sat=sat, maxn=maxn, secs=time.time() - t0)


def main():
    print("=" * 78)
    print("(A) known boards")
    print("=" * 78)
    for name, cst, cap in [("campaign s1", S1, 20000),
                           ("second family", SECOND, 20000),
                           ("FJ minimal 12", FJMIN, 20000)]:
        run_board(name, cst, cap)

    secs = float(sys.argv[1]) if len(sys.argv) > 1 else 60.0

    print()
    print("=" * 78)
    print("(B) random high-rung components (rungs 2..5)")
    print("=" * 78)
    tot = defaultdict(int)
    for seed0 in (4242, 987654, 31337):
        r = random_sweep(400, seed0, 4000, secs / 3)
        print(f"  seed {seed0}: comps={r['components']} states={r['states']} "
              f"maxn={r['maxn']} sat={r['sat']} forked={r['sat_states']} "
              f"pull={r['pull_comps']} strict={r['strict_comps']}")
        print(f"      pairs={r['pairs']} exact={r['exact_ok']} "
              f"dom={r['dom_ok']} needed_fork={r['needed_fork']} "
              f"FAIL={r['failures']} sat_below={r['sat_below']}")
        for k in ('components', 'states', 'sat', 'pairs', 'exact_ok',
                  'dom_ok', 'needed_fork', 'failures', 'sat_below',
                  'pull_comps', 'strict_comps'):
            tot[k] += r[k]

    print()
    print("=" * 78)
    print("(C) exhaustive small boards")
    print("=" * 78)
    ex = []
    ex.append(exhaustive(3, 5, secs / 2, "K3/tab5"))
    ex.append(exhaustive(4, 5, secs / 2, "K4/tab5"))
    for r in ex:
        print(f"  {r['tag']}: comps={r['components']} states={r['states']} "
              f"maxn={r['maxn']} forked={r['forked_comps']} sat={r['sat']}")
        print(f"      pairs={r['pairs']} exact={r['exact_ok']} "
              f"dom={r['dom_ok']} needed_fork={r['needed_fork']} "
              f"FAIL={r['failures']} sat_below={r['sat_below']} "
              f"({r['secs']:.0f}s)")

    print()
    print("=" * 78)
    print("(D) totals")
    print("=" * 78)
    for k in sorted(tot):
        print(f"  random {k:14s} {tot[k]}")
    for r in ex:
        for k in ('components', 'states', 'pairs', 'exact_ok', 'dom_ok',
                  'needed_fork', 'failures', 'sat_below'):
            print(f"  {r['tag']:8s} {k:14s} {r[k]}")
    allfail = tot['failures'] + sum(r['failures'] for r in ex)
    allsb = tot['sat_below'] + sum(r['sat_below'] for r in ex)
    allneed = tot['needed_fork'] + sum(r['needed_fork'] for r in ex)
    print()
    print(f"VERDICT: failures={allfail}  sat_below={allsb}  "
          f"fork-rescued-pairs={allneed}")


if __name__ == '__main__':
    main()
