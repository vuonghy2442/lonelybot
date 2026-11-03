"""RaisesOrFork_enum3.py -- complete enumeration at K=3, tab<=5.

The full board list is 4 183 859 canonical boards (counted by
`Search_enum.enum_boards(3,5)`), which is small enough to finish.  We dedup
components and run the gated target test on every component.

Usage: python RaisesOrFork_enum3.py [secs]
Prints progressively; the final line states whether the enumeration completed.
"""
import sys, time
sys.path.insert(0, 'Temp')
from Search_enum import enum_boards
from RaisesOrFork_probe import component, analyse

K, MAXTAB, TOTAL = 3, 5, 4183859
secs = float(sys.argv[1]) if len(sys.argv) > 1 else 2400.0

deadline = time.time() + secs
visited = set()
boards = comps = states = pairs = exact_ok = dom_ok = 0
needed = fails = satbelow = 0
t0 = time.time()
done = True
for cst in enum_boards(K, MAXTAB):
    boards += 1
    if boards % 200000 == 0:
        print(f"  [{time.time()-t0:.0f}s] boards={boards}/{TOTAL} comps={comps} "
              f"states={states} fails={fails} sat_below={satbelow}",
              flush=True)
    if time.time() > deadline:
        done = False
        break
    if cst in visited:
        continue
    try:
        order, succ = component(cst, cap=10000)
    except RuntimeError:
        continue
    visited.update(order)
    inf = analyse(order, succ)
    comps += 1
    states += inf['n']
    pairs += inf['pairs']
    exact_ok += inf['exact_ok']
    dom_ok += inf['dom_ok']
    needed += len(inf['needed_fork'])
    fails += len(inf['failures'])
    satbelow += len(inf['sat_below'])
    if inf['failures'] or inf['sat_below'] or inf['needed_fork']:
        from Search_lib import c_show, rungs_of
        print("!! HIT:", c_show(cst), rungs_of(cst))
        for (s, rs, rv, R) in inf['failures'][:2]:
            print("   FAIL", rs, "->", rv, c_show(s))
            print("   reach:", R)

print(f"FINAL boards={boards}/{TOTAL} complete={done and boards == TOTAL} "
      f"comps={comps} states={states} pairs={pairs} exact={exact_ok} "
      f"dom={dom_ok} needed_fork={needed} failures={fails} "
      f"sat_below={satbelow} time={time.time()-t0:.0f}s")
