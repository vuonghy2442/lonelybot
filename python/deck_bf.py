"""Deck-machine brute force: the validation harness for rung 3.

The machine (deck_sim.Deck, the port of deck.rs): remaining cards in a
fixed order + a cursor. compute_mask(filter=False) = the accessible set
aggregated over all deal_once-advances from the current cursor.

THE CHARACTERIZATION (to be validated): at state (rem, c), card w at
current position P(w) is accessible iff

    P(w) % 3 == 2          (the batch-top lane: always reachable by
                            dealing forward, and through the wrap)
    or w == max-remaining  (the last position is always accessible)
    or P(w) % 3 == (c-1) % 3 and P(w) >= c-1
                           (the leading lane: the current waste top and
                            its forward-dealing lane; the >= bound is
                            the burial constraint)

Because dealing only shrinks the mask (buried waste tops), the maximal
mask sits at the post-draw cursor, so a draw SEQUENCE is realizable iff
every consecutive pair satisfies the condition at the predecessor's
post-draw state — the engine's deal_onces never add options.

Sequence form (original positions O, draw order sigma): for each
consecutive pair x -> w,

    lane2(w) or max(w) or [ lane(w) = lane(x)-1 (mod 3) and interval(x,w) ]

with lane(v) = (O(v) - r(v)) % 3, r(v) = #drawn-before-v below O(v);
interval(x,w) = (O(w) > O(x)) or (every z in [O(w), O(x)), z != w,
drawn before x).  The interval identity: P(w) >= P(x)-1 reduces to
exactly this because between-position counts are saturated.

Modes:
  python deck_bf.py states [N ...]   — reachable-state BFS, predicate
                                       check, pairwise-forced residue
  python deck_bf.py seqs [N ...]     — all-permutation iff check
  python deck_bf.py wins              — the corpus' winning draw
                                       sequences must satisfy the
                                       pair conditions (the soundness
                                       falsifier for rung 3)
"""
import sys
import time

STEP = 3


# ---- the machine (direct tuple port of deck_sim.Deck) -----------------------


def mask_positions(rem, c, step=STEP):
    """Accessible positions of compute_mask(filter=False)."""
    out = set()
    n = len(rem)
    i = c + (step if c == 0 else 0) - 1
    while i < n - 1:
        if 0 <= i < n:
            out.add(i)
        i += step
    if n > 0:
        out.add(n - 1)
    off = c % step
    end = (n if off != 0 else c) - 1
    i = step - 1
    while i < end:
        if 0 <= i < n:
            out.add(i)
        i += step
    return out


def pred_positions(rem, c, step=STEP):
    """The characterized predicate, as a set of positions."""
    out = set()
    n = len(rem)
    for p in range(n):
        if p % step == step - 1 or p == n - 1:
            out.add(p)
        elif c > 0 and p >= c - 1 and p % step == (c - 1) % step:
            out.add(p)
    return out


def offset_once(c, n, step=STEP):
    return 0 if c >= n else min(c + step, n)


# ---- state BFS --------------------------------------------------------------


def bfs_states(n, step=STEP):
    """Reachable (rem, c) via draws and deal_once. Returns the state set
    and mismatch statistics for the predicate check."""
    start = (tuple(range(n)), 0)
    seen = {start}
    stack = [start]
    mismatches = []
    while stack:
        rem, c = s = stack.pop()
        mask = mask_positions(rem, c, step)
        pred = pred_positions(rem, c, step)
        if mask != pred:
            m = set(rem[i] for i in mask)
            p = set(rem[i] for i in pred)
            mismatches.append((s, sorted(m), sorted(p)))
        # draws
        for i in mask:
            card = rem[i]
            new_rem = rem[:i] + rem[i + 1:]
            s2 = (new_rem, i)
            if s2 not in seen:
                seen.add(s2)
                stack.append(s2)
        # deal_once
        c2 = offset_once(c, len(rem), step)
        s2 = (rem, c2)
        if s2 not in seen:
            seen.add(s2)
            stack.append(s2)
    return seen, mismatches


def pairwise_forced(n, states, step=STEP):
    """Pairs (a, b) such that b-before-a is impossible in any realizable
    order: no reachable state has b accessible while a remains."""
    poss = [0] * n  # poss[b] = bitmask of a that can follow b
    for rem, c in states:
        mask = mask_positions(rem, c, step)
        rem_bits = 0
        for v in rem:
            rem_bits |= 1 << v
        for i in mask:
            b = rem[i]
            poss[b] |= rem_bits
    forced = []
    for b in range(n):
        for a in range(n):
            if a != b and not (poss[b] >> a) & 1:
                forced.append((a, b))  # a must be drawn before b
    return forced


# ---- sequence-level -----------------------------------------------------------


def check_seq(perm, step=STEP):
    """The pair conditions on a full draw sequence (original indices)."""
    n = len(perm)
    pos = {v: t for t, v in enumerate(perm)}
    # lanes: r(v) = # earlier draws below O(v)
    lane = [0] * n
    r = [0] * n
    for t, v in enumerate(perm):
        r[v] = sum(1 for u in perm[:t] if u < v)
        lane[v] = (v - r[v]) % step
    # first draw
    if perm[0] % step != step - 1 and perm[0] != n - 1:
        return (0, "first draw not lane-2/max")
    for t in range(1, n):
        w = perm[t]
        x = perm[t - 1]
        # lane2(w) or max(w) or leading
        ok = False
        if (w - r[w]) % step == step - 1:
            ok = True
        elif all(pos[z] < t for z in range(w + 1, n)):
            ok = True  # max-remaining
        elif (w - r[w]) % step == (x - r[x] - 1) % step:
            if w > x:
                ok = True  # interval auto-satisfied
            else:
                ok = all(pos[z] < pos[x] for z in range(w, x) if z != w)
        if not ok:
            return (t, f"pair {x}->{w}")
    return None


def realizable(perm, step=STEP):
    rem = list(range(len(perm)))
    c = 0
    for v in perm:
        try:
            i = rem.index(v)
        except ValueError:
            return False
        if i not in mask_positions(tuple(rem), c, step):
            return False
        rem.pop(i)
        c = i
    return True


def seqs_check(n, step=STEP):
    from itertools import permutations
    bad = 0
    total = 0
    for perm in permutations(range(n)):
        total += 1
        a = check_seq(perm, step) is None
        b = realizable(perm, step)
        if a != b:
            bad += 1
            if bad <= 5:
                print(f"  MISMATCH {perm}: conditions={a} realizable={b}")
    print(f"  N={n}: {total} permutations, {bad} mismatches")


# ---- the corpus' winning sequences -------------------------------------------


def wins_check():
    from graph import Game
    from sat_scheduler import run_cli, deal_from_seed
    from check_line import parse_line
    from unsat_gates import iid
    checked = bad = 0
    for seed in range(12, 76):
        for draw in (1, 3):
            if draw == 1:
                continue  # the draw-1 deck is a free set; conditions are step-3
            out = run_cli("solve", "default", str(seed), str(draw))
            if "Solvable" not in out:
                continue
            moves = parse_line(out)
            game = Game.from_str(deal_from_seed(seed))
            deck = [iid(c) for c in game.deck]  # engine order
            pos_of = {c: i for i, c in enumerate(deck)}
            seq = [pos_of[iid(c)] for n, c in moves
                   if n in ("DeckStack", "DeckPile")]
            err = check_seq(seq)
            checked += 1
            if err is not None:
                bad += 1
                print(f"  seed {seed} d{draw}: VIOLATION {err}")
    print(f"wins: {checked} winning draw sequences checked, {bad} violations")


# ---- random full-scale sampling (N=24) ---------------------------------------


def cond_ok(x, x_r, w, drawn, n, step=STEP):
    """Is w a legal successor of x? (x_r = r(x) at x's draw; drawn = the
    cards drawn before w would be.) Mirrors check_seq's pair condition."""
    r_w = sum(1 for z in drawn if z < w)
    if (w - r_w) % step == step - 1:
        return True
    if all(z in drawn for z in range(w + 1, n)):
        return True  # max-remaining
    if (w - r_w) % step == (x - x_r - 1) % step:
        if w > x:
            return True
        return all((z in drawn) or z == w for z in range(w, x))
    return False


def sample_check(n=24, k=2000, step=STEP, seed=1234):
    """Both directions of the characterization at full scale:
    forward — random machine-legal playouts satisfy the conditions;
    converse — random condition-satisfying sequences are realizable."""
    import random
    rng = random.Random(seed)
    bad_fwd = 0
    for _ in range(k):
        rem = list(range(n))
        c = 0
        seq = []
        while rem:
            mask = mask_positions(tuple(rem), c, step)
            i = rng.choice(sorted(mask))
            seq.append(rem[i])
            rem.pop(i)
            c = i
        if check_seq(seq, step) is not None:
            bad_fwd += 1
            if bad_fwd <= 3:
                print(f"  FORWARD violation: {seq}")
    bad_back = 0
    made = 0
    attempts = 0
    while made < k and attempts < k * 50:
        attempts += 1
        drawn = set()
        prev = None
        prev_r = 0
        seq = []
        ok = True
        while len(seq) < n:
            cands = []
            for w in range(n):
                if w in drawn:
                    continue
                if prev is None:
                    if w % step == step - 1 or w == n - 1:
                        cands.append(w)
                elif cond_ok(prev, prev_r, w, drawn, n, step):
                    cands.append(w)
            if not cands:
                ok = False
                break
            w = rng.choice(cands)
            seq.append(w)
            drawn.add(w)
            prev_r = sum(1 for z in seq[:-1] if z < w)
            prev = w
        if not ok:
            continue
        made += 1
        if not realizable(seq, step):
            bad_back += 1
            if bad_back <= 3:
                print(f"  CONVERSE violation: {seq}")
    print(f"  N={n}: {k} random legal playouts -> {bad_fwd} condition "
          f"violations; {made} condition-generated sequences "
          f"({attempts} attempts) -> {bad_back} non-realizable")


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "states"
    if mode == "states":
        for n in [int(x) for x in sys.argv[2:]] or [6, 9, 12]:
            t0 = time.perf_counter()
            states, mism = bfs_states(n)
            t = time.perf_counter() - t0
            print(f"N={n}: {len(states)} reachable states in {t:.1f}s, "
                  f"{len(mism)} predicate mismatches")
            for s, m, p in mism[:5]:
                print(f"    state rem={s[0]} c={s[1]}: mask={m} pred={p}")
            forced = pairwise_forced(n, states)
            print(f"    pairwise-forced (a before b): {forced}")
    elif mode == "seqs":
        for n in [int(x) for x in sys.argv[2:]] or [6, 9]:
            t0 = time.perf_counter()
            seqs_check(n)
            print(f"    [{time.perf_counter() - t0:.1f}s]")
    elif mode == "sample":
        n = int(sys.argv[2]) if len(sys.argv) > 2 else 24
        k = int(sys.argv[3]) if len(sys.argv) > 3 else 2000
        sample_check(n, k)
    elif mode == "wins":
        wins_check()


if __name__ == "__main__":
    main()
