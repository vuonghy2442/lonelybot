"""RungLe_probe_hi.py — adversarial high-rung sweep for (R).

Same `analyse` as RungLe_probe, but seeds have rungs 2..5 (so `foundToTab`
pulls are immediately available) and deeper runs.  High pull pressure is where
a raiseS-only play would be most likely to fail to match a comparable orbit
mate.
"""
import sys, random, time
sys.path.insert(0, 'Temp')
from RungLe_probe import analyse, wf_ok, run_ok, rung_le


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


def seed_hi(rng):
    rungs = tuple(rng.randrange(2, 6) for _ in range(4))
    run_piles = legal_runs_hi(rng, rng.randrange(5, 8), 8, rungs)
    ps = run_piles + tuple((False, ()) for _ in range(7 - len(run_piles)))
    cards = [c for _h, run in ps for c in run]
    if len(set(cards)) != len(cards):
        return None
    if not all(run_ok(run) for _h, run in ps):
        return None
    if any(c[0] < rungs[c[1]] for c in cards):
        return None
    return (rungs, ps)


def walk_hi(rng, depth=15):
    cst = seed_hi(rng)
    if cst is None:
        return None
    for _ in range(rng.randrange(0, depth)):
        from Search_lib import c_moves, c_step
        ms = c_moves(cst)
        if not ms:
            break
        v = c_step(cst, rng.choice(ms))
        if v is None:
            break
        cst = v
    return cst


def main():
    budget = int(sys.argv[1]) if len(sys.argv) > 1 else 500
    seed0 = int(sys.argv[2]) if len(sys.argv) > 2 else 4242
    cap = int(sys.argv[3]) if len(sys.argv) > 3 else 4000
    rng = random.Random(seed0)
    t0 = time.time()
    attempts = accepted = checked = 0
    n_states = n_sat = n_checked = n_reach = n_hits = 0
    n_sat_hits = n_lemma = 0
    pull_comps = strict_comps = 0
    maxcomp = 0
    printed = 0
    while checked < budget and time.time() - t0 < 1200:
        cst = walk_hi(rng)
        attempts += 1
        if cst is None or not wf_ok(cst):
            continue
        accepted += 1
        try:
            inf = analyse(cst, cap=cap, check_sym=(checked % 50 == 0))
        except (RuntimeError, AssertionError):
            continue
        checked += 1
        n_states += inf['size']
        n_sat += len(inf['sat'])
        n_checked += inf['n_checked']
        n_reach += inf['n_reachable']
        n_hits += inf['n_unreachable']
        n_sat_hits += len(inf['sat_hits'])
        n_lemma += inf['sat_lemma_bad']
        if inf['n_pull']:
            pull_comps += 1
        if inf['has_strict']:
            strict_comps += 1
        maxcomp = max(maxcomp, inf['size'])
        if inf['sat_hits'] and printed < 3:
            printed += 1
            u, ru, v, rv = inf['sat_hits'][0]
            print("SAT-HIT", ru, "<=", rv)
            from Search_lib import c_show
            print("  u:", c_show(u))
            print("  v:", c_show(v))
        if inf['n_unreachable'] and printed < 3:
            printed += 1
            s, rs, v, rv, rset = inf['rung_hits'][0]
            from Search_lib import c_show
            print("RUNG-HIT", rs, "target", rv)
            print("  s:", c_show(s))
            print("  v:", c_show(v))
    print()
    print("COVERAGE (high-rung WF-valid):")
    print("  seed attempts          :", attempts)
    print("  seeds surviving WF     :", accepted,
          f"({100.0*accepted/max(1,attempts):.1f}%)")
    print("  components analysed    :", checked)
    print("  pull-bearing components:", pull_comps)
    print("  components with a strict comparable pair:", strict_comps)
    print("  max component size     :", maxcomp)
    print("  total states           :", n_states)
    print("  saturated states       :", n_sat)
    print("  pairs checked          :", n_checked,
          "(reachable", n_reach, ", unreachable", n_hits, ")")
    print("  saturated strict hits  :", n_sat_hits)
    print("  saturated-lemma bad    :", n_lemma)
    print("  %.1fs" % (time.time() - t0))


if __name__ == '__main__':
    main()
