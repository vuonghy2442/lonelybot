"""Port check: Lean Pace.maskPos vs deck_sim.Deck.compute_mask.

Generates a #eval grid (n = 0..9, cursor = 0..n+1 including the
saturated state, step = 1..4), runs it through `lake env lean`, and
diffs against the Python machine. The reference chain: deck_sim was
validated against the engine's winning lines; this checks the Lean
port against deck_sim.

Usage: python pace_port_check.py [--nmax N]
"""
import re
import subprocess
import sys
import tempfile
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from deck_sim import Deck

LEAN_MODEL = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                          "..", "lean-model")

LEAN_SRC = """import Klondike.Pace

def m (n cursor step : Nat) : List Nat :=
  Pace.maskPos ⟨List.range n, cursor⟩ (step + 1) (Nat.succ_pos step)

def grid : List String :=
  (List.range {nmax}).flatMap fun n =>
    (List.range (n + 2)).flatMap fun cursor =>
      (List.range 4).map fun step =>
        s!"{{n}} {{cursor}} {{step + 1}} {{m n cursor step}}"

#eval grid
"""


def main():
    nmax = 10
    if "--nmax" in sys.argv:
        nmax = int(sys.argv[sys.argv.index("--nmax") + 1])
    with tempfile.NamedTemporaryFile("w", suffix=".lean",
                                      delete=False, encoding="utf-8") as f:
        f.write(LEAN_SRC.format(nmax=nmax))
        path = f.name
    try:
        r = subprocess.run(["lake", "env", "lean", path],
                           cwd=LEAN_MODEL, capture_output=True,
                           text=True, encoding="utf-8", check=True)
        out = r.stdout
    finally:
        os.unlink(path)
    rows = re.findall(r'"(\d+) (\d+) (\d+) (\[[^\]]*\])"', out)
    assert rows, "no rows parsed from Lean output"
    bad = 0
    for n, cursor, step, lst in rows:
        n, cursor, step = int(n), int(cursor), int(step)
        lean = set(int(x) for x in re.findall(r"\d+", lst))
        d = Deck(list(range(n)), step)
        d.draw_cur = cursor
        py = d.compute_mask()
        if lean != py:
            bad += 1
            if bad <= 10:
                print(f"MISMATCH n={n} c={cursor} step={step}: "
                      f"lean={sorted(lean)} py={sorted(py)}")
    print(f"{len(rows)} states compared, {bad} mismatches")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
