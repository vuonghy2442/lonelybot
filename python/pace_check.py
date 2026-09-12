"""Find which deck-pace clause the engine's own winning line violates —
the over-constraint that made seed 56 d3 unsound."""
from graph import Card, Game
from sat_scheduler import run_cli, deal_from_seed
from check_line import parse_line
from unsat_gates import iid


def draw_order(seed, draw):
    game = Game.from_str(deal_from_seed(seed))
    moves = parse_line(run_cli("solve", "default", str(seed), str(draw)))
    pos = [iid(c) for c in game.deck]  # engine order: 0 = bottom
    order = []
    for name, c in moves:
        if name in ("DeckStack", "DeckPile"):
            order.append(iid(c))
    return pos, order


def check(seed, draw):
    pos, order = draw_order(seed, draw)
    idx = {c: i for i, c in enumerate(order)}  # draw rank per card
    n = len(pos)
    step = draw
    bad = []
    # chain: pos[i+1] drawn before pos[i], i in 0..min(n,step)-2
    for i in range(min(n, step) - 1):
        if idx[pos[i + 1]] > idx[pos[i]]:
            bad.append(f"chain {i + 1}<{i}: rank {idx[pos[i+1]]} vs {idx[pos[i]]}")
    pivots = []
    for i in range(step, n - 1):
        if i % step == 0:
            pivots.append(i)
            continue
        ok = idx[pos[i + 1]] < idx[pos[i]] or any(idx[pos[p]] < idx[pos[i]] for p in pivots)
        if not ok:
            bad.append(f"clause i={i}: ({i+1}<{i})={idx[pos[i+1]]<idx[pos[i]]}, "
                       f"pivots {[ (p, idx[pos[p]] < idx[pos[i]]) for p in pivots ]}")
    print(f"seed {seed} d{draw}: {len(order)} draws, {len(bad)} violated clauses")
    for b in bad[:10]:
        print("  ", b)
    # also print the draw order as positions
    print("  draw order (positions):", [pos.index(c) for c in order])


if __name__ == "__main__":
    check(56, 3)
