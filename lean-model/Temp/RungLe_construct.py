"""Independent constructive check of RungLe_probe's reachability claim:
for sampled (s, target rung tuple) pairs it reconstructs an explicit
raiseS-only play and replays it with the *full* Valley `step`, printing the
letter sequence.  This both (i) confirms the closure is not permissive and
(ii) gives a human-readable witness."""
import sys, random
sys.path.insert(0, 'Temp')
from Search_lib import (c_step, c_moves, rungs_of, c_show, fmt, to_full)
from RungLe_probe import (reach, succ_raiseS, raiseS_rungs, rung_le, walk_state,
                          wf_ok)

H, D, S, C = 0, 1, 2, 3


def raiseS_path(src, succ, target_rungs):
    """BFS in the raiseS graph, returns (states, moves) or None."""
    from collections import deque
    par = {src: (None, None)}
    q = deque([src])
    while q:
        u = q.popleft()
        if rungs_of(u) == target_rungs:
            out_s, out_m = [], []
            cur = u
            while cur != src:
                p, m = par[cur]
                out_s.append(cur)
                out_m.append(m)
                cur = p
            return list(reversed(out_s)), list(reversed(out_m))
        for m in c_moves(u):
            if m[0] not in ('tabToTab', 'tabToFound'):
                continue
            v = c_step(u, m)
            if v is not None and v not in par:
                par[v] = (u, m)
                q.append(v)
    return None


def sample_component(seed_cst, n_pairs=6, rngseed=0):
    R = reach(seed_cst, cap=20000)
    succ = {u: succ_raiseS(u) for u in R}
    rungtups = sorted(set(rungs_of(u) for u in R))
    rng = random.Random(rngseed)
    done = 0
    for u in R:
        ru = rungs_of(u)
        cands = [rv for rv in rungtups if rv != ru and rung_le(ru, rv)]
        rng.shuffle(cands)
        for rv in cands[:2]:
            assert rv in raiseS_rungs(u, succ), "closure mismatch"
            got = raiseS_path(u, succ, rv)
            assert got is not None, "no path but closure says reachable"
            states, moves = got
            # verify every letter is raiseS and the endpoint rungs match
            cur = u
            for m in moves:
                assert m[0] in ('tabToTab', 'tabToFound')
                cur = c_step(cur, m)
                assert cur is not None
            assert rungs_of(cur) == rv, (rungs_of(cur), rv)
            if done < n_pairs:
                print(f"  witness {ru} -> {rv}: " +
                      " ; ".join(fmt(m) for m in moves))
                done += 1
        if done >= n_pairs:
            break
    return done


if __name__ == '__main__':
    from SatDiffer_sweep import s1
    print("campaign orbit, constructive raiseS paths:")
    sample_component(s1, n_pairs=6, rngseed=1)

    rng = random.Random(31337)
    n = 0
    while n < 3:
        cst = walk_state(rng)
        if cst is None or not wf_ok(cst):
            continue
        R = reach(cst, cap=5000)
        succ = {u: succ_raiseS(u) for u in R}
        rungtups = sorted(set(rungs_of(u) for u in R))
        # only components with at least one strict comparable pair
        ok = any(rv != rungs_of(u) and rung_le(rungs_of(u), rv)
                 for u in R for rv in rungtups)
        if not ok:
            continue
        n += 1
        print(f"\nrandom component #{n} |orbit|={len(R)}:")
        sample_component(cst, n_pairs=4, rngseed=n)
