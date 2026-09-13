"""Measurement: oracle (old solver) wall time on the 10 loss games of
the 128-game corpus (seeds 12-75). The killed/missed split is the
rung-2-era classification; post rung 3 all ten are ladder kills, so
this documents where the search cost actually sits (answer: nowhere
on this corpus — every loss resolves in <=1.4s).

Usage: python measure_oracle.py
"""
import time

from sat_scheduler import run_cli

KILLED = [(22, 1), (22, 3), (32, 1), (32, 3), (46, 3)]
MISSED = [(18, 3), (21, 3), (51, 3), (55, 3), (62, 3)]


def main():
    for label, games in (("killed", KILLED), ("missed", MISSED)):
        print(f"--- {label} ---", flush=True)
        for seed, draw in games:
            t0 = time.perf_counter()
            out = run_cli("solve", "default", str(seed), str(draw))
            t = time.perf_counter() - t0
            verdict = "Solvable" if "Solvable" in out else "Impossible"
            print(f"seed={seed} d{draw}: {verdict} in {t:.1f}s", flush=True)


if __name__ == "__main__":
    main()
