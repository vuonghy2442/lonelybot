"""RaisesOrFork_prepend_probe.py -- test the parent's PREPEND mechanism.

Mechanism under test (the pull branch of the induction):

  s --(pull c b)--> u,  and  rho is a licensed raiseS play u --> v.
  Claim:  the word  c :: rho  fires at u,
          i.e.  rho fires at s  (because  u --(raise c)--> s  exactly).

We test the *firing* statement, which is the whole content:

  for every pull edge s -c-> u  and every raiseS play rho from u
  that contains no raise of a card of c's suit,
      word_fires(u, [c] + rho).

`word_fires` = the state-set BFS: at each letter, close the current state set
under tabToTab (the cargo slides), fire the raise from every member of the
closure, and continue.  Empty set at any point = the word does not fire.

Also reported: whether the *endpoint rungs* of the prepended word dominate
both rungs s and rungs t (the rung bookkeeping of the mechanism).

Scratch; nothing under Orig2/ or Temp/*.lean touched.
"""
import sys, random
sys.path.insert(0, 'Temp')
from Search_lib import (c_moves, c_step, c_can_raise_set, c_cargo_closure,
                        c_show, rungs_of)
from RaisesOrFork_probe import S1, SECOND, FJMIN, component, rung_le
from valley_probe import twin


# ------------------------------------------------------------------ firing
def closure(S):
    out = set()
    for u in S:
        out |= c_cargo_closure(u)
    return out


def fire_word(S, word):
    """States reachable from the set S by the exact letter sequence `word`."""
    cur = set(S)
    for c in word:
        cl = closure(cur)
        nxt = set()
        for z in cl:
            if c in c_can_raise_set(z):
                w = c_step(z, ('tabToFound', c))
                if w is not None:
                    nxt.add(w)
        if not nxt:
            return None          # word does not fire
        cur = nxt
    return cur


def licensed_raises(u):
    """All cards c such that the letter raise c fires at u (CanRaiseS)."""
    out = []
    for z in c_cargo_closure(u):
        out.extend(c_can_raise_set(z))
    return sorted(set(out))


def rand_raiseS_play(u, rng, maxlen=4):
    """A random licensed raiseS play (word + endpoint states)."""
    word = []
    cur = {u}
    for _ in range(rng.randrange(0, maxlen + 1)):
        cl = closure(cur)
        cand = sorted({c for z in cl for c in c_can_raise_set(z)})
        if not cand:
            break
        c = rng.choice(cand)
        nxt = set()
        for z in cl:
            if c in c_can_raise_set(z):
                w = c_step(z, ('tabToFound', c))
                if w is not None:
                    nxt.add(w)
        if not nxt:
            break
        word.append(c)
        cur = nxt
    return word, cur


# ------------------------------------------------------------------ test
def test_component(order, succ, rng, plays_per_pull=3, maxlen=4):
    res = dict(pulls=0, plays=0, fail=0, tgt_checked=0, tgt_fail=0,
               examples=[])

    def rungs_le(rv, S):
        return any(rung_le(rv, rungs_of(z)) for z in S)

    for s in order:
        for m, u in succ[s]:
            if m[0] != 'foundToTab':
                continue
            c = m[1]
            res['pulls'] += 1
            # the raise of c at u must fire (it does: canRaise_after_pull)
            assert c in licensed_raises(u), (c_show(s), c)
            for _ in range(plays_per_pull):
                rho, V = rand_raiseS_play(u, rng, maxlen)
                # the deficit argument says rho has no letter of c's suit
                if any(d[1] == c[1] for d in rho):
                    continue
                ct = (c[0], twin(c[1]))
                if ct in rho:
                    # the plan's residual: the twin IS raised
                    res.setdefault('twin_plays', 0)
                    res['twin_plays'] += 1
                    W0 = fire_word({u}, rho + [c])
                    if W0 is None:
                        res.setdefault('twin_fail', 0)
                        res['twin_fail'] += 1
                    continue
                res['plays'] += 1
                # the parent's lemma: the word is `c :: rho` in Lean's
                # reverse-play convention, i.e. the PLAY is  rho  then  c.
                W = fire_word({u}, rho + [c])
                if W is None:
                    res['fail'] += 1
                    if len(res['examples']) < 5:
                        res['examples'].append(
                            ('PREPEND FAILS', c_show(s), c, rho,
                             [c_show(z) for z in list(V)[:1]]))
                    continue
                # rung bookkeeping: endpoint must dominate s and every t
                # that the original play dominated
                for w in W:
                    res['tgt_checked'] += 1
                    if not rung_le(rungs_of(u), rungs_of(w)):
                        res['tgt_fail'] += 1
                        if len(res['examples']) < 5:
                            res['examples'].append(
                                ('RUNG u FAILS', c, rho, rungs_of(u),
                                 rungs_of(w)))
                if not rungs_le(rungs_of(s), W):
                    res['tgt_fail'] += 1
                    if len(res['examples']) < 5:
                        res['examples'].append(
                            ('RUNG s FAILS', c, rho, rungs_of(s),
                             [rungs_of(z) for z in W]))
    return res


def main():
    secs = float(sys.argv[1]) if len(sys.argv) > 1 else 60.0
    rng = random.Random(20261103)
    import time
    t0 = time.time()
    boards = [('campaign', S1), ('second', SECOND), ('FJmin', FJMIN)]
    tot = dict(pulls=0, plays=0, fail=0, tgt_checked=0, tgt_fail=0)
    for name, cst in boards:
        order, succ = component(cst, cap=6000)
        r = test_component(order, succ, rng)
        print(f"  [{name}] pulls={r['pulls']} plays={r['plays']} "
              f"prepend_failures={r['fail']} rung_fail={r['tgt_fail']}")
        for e in r['examples'][:3]:
            print("     ", e)
        for k in tot:
            tot[k] += r[k]

    # random components
    from RaisesOrFork_probe import walk_hi, wf_ok
    n = 0
    while time.time() - t0 < secs and n < 250:
        cst = walk_hi(rng)
        if cst is None or not wf_ok(cst):
            continue
        try:
            order, succ = component(cst, cap=3000)
        except RuntimeError:
            continue
        if time.time() - t0 > secs:
            break
        n += 1
        r = test_component(order, succ, rng)
        for k in tot:
            tot[k] += r[k]
        if r['fail'] or r['tgt_fail']:
            print(f"  !! component #{n}: prepend_fail={r['fail']} "
                  f"rung_fail={r['tgt_fail']}")
            for e in r['examples'][:2]:
                print("     ", e)

    print()
    print("TOTALS", tot)
    print(f"  random components: {n}  ({time.time()-t0:.0f}s)")
    print("VERDICT:", "no prepend failure" if tot['fail'] == 0 else
          f"{tot['fail']} PREPEND FAILURES")


if __name__ == '__main__':
    main()
