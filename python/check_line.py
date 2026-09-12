"""Ground-truth audit: take the old engine's printed winning line,
replay it concretely (choosing destinations for Reveal/DeckPile), and
check the realized schedule against each constraint family of the
M=1/W=0 SAT model. The family the TRUE line violates is the buggy
encoding; if the line needs a second relocation of some card, the
model's M=1 is genuinely insufficient instead.

usage: python check_line.py 18
"""
import re
import sys

from graph import Card, Game, RANKS, SUITS
from sat_scheduler import run_cli, deal_from_seed, color, KING

MOVE_RE = re.compile(r"(DS|PS|DP|SP|R) (10|[AJKQ2-9])([♠♥♦♣])")
PREFIX = {"DS": "DeckStack", "PS": "PileStack", "DP": "DeckPile", "SP": "StackPile", "R": "Reveal"}
USUIT = {"♥": "H", "♦": "D", "♣": "C", "♠": "S"}


def parse_line(text):
    out = []
    for pfx, rank, us in MOVE_RE.findall(text):
        out.append((PREFIX[pfx], Card(RANKS.index(rank), "HDCS".index(USUIT[us]))))
    return out


def compatible(guest, host):
    return host.rank == guest.rank + 1 and color(host.suit) != color(guest.suit)


def realize(moves, game):
    """Replay under the engine's TRUE semantics: the tableau is a set
    (visible set + per-pile unlock chains), no physical piles.

    - Reveal(c): c is the current surface of a pile with hidden cards
      left; the card under it becomes visible (c stays visible too)
    - DeckPile(c): c leaves the deck, joins the visible set (no spot
      consumed; legality was free_slot, existential)
    - PileStack/DeckStack(c): c joins the foundation (prefix up)
    """
    piles = [list(h) + list(v) for h, v in game.tableau]  # bottom -> top
    # surface[p] = index of the current locked surface (the top of the
    # remaining pile range); everything below it in the range is hidden.
    # Reveal(c) pops c (the surface); the card under becomes visible.
    # PileStack(c) with c locked also reveals (make_stack -> make_reveal).
    surface = [len(p) - 1 for p in piles]
    vis = {c for _, v in game.tableau for c in v}
    deck = set(game.deck)
    found = [0] * 4
    events = []

    def surface_pile(c):
        return next(
            (j for j, s in enumerate(surface) if s >= 0 and piles[j][s] == c), None
        )

    for i, (name, c) in enumerate(moves):
        if name == "DeckStack":
            assert c in deck and found[c.suit] == c.rank, (i, name, c)
            deck.remove(c)
            vis.discard(c)
            found[c.suit] += 1
            events.append(("depart", c, None))
        elif name == "PileStack":
            assert c in vis and found[c.suit] == c.rank, (i, name, c)
            vis.remove(c)
            found[c.suit] += 1
            pi = surface_pile(c)
            if pi is not None:
                surface[pi] -= 1
                if surface[pi] >= 0:
                    vis.add(piles[pi][surface[pi]])
            events.append(("depart", c, None))
        elif name == "DeckPile":
            assert c in deck, (i, name, c)
            deck.remove(c)
            vis.add(c)
            events.append(("park", c, None))
        elif name == "Reveal":
            pi = surface_pile(c)
            assert pi is not None, (i, name, c, "not a locked surface")
            surface[pi] -= 1
            if surface[pi] >= 0:
                vis.add(piles[pi][surface[pi]])
            events.append(("move", c, None))
        else:
            raise AssertionError(name)
    assert all(h == 13 for h in found), found
    return events


def first_leave(card, events):
    """Index of the first event where `card` vacates its initial pile:
    its first arrival (move) or its departure."""
    for i, (kind, c, _) in enumerate(events):
        if c == card and kind in ("move", "depart"):
            return i
    return None


def main():
    seed = int(sys.argv[1])
    game = Game.from_str(deal_from_seed(seed))
    moves = parse_line(run_cli("solve", "default", str(seed), "1"))
    print(f"engine line: {len(moves)} moves")
    events = realize(moves, game)
    if events is None:
        print("FAILED to realize the line (no destination choices worked)")
        return
    print(f"realized: {len(events)} events")

    # per-card arrival counts (M)
    arrivals = {}
    for kind, c, _ in events:
        if kind in ("move", "park"):
            arrivals[c] = arrivals.get(c, 0) + 1
    m = max(arrivals.values(), default=0)
    twice = [c for c, n in arrivals.items() if n > 1]
    print(f"M (max relocations per card) = {m}; cards relocating twice: {twice}")
    if m > 1:
        print("-> the true line needs M=2: the M=1 model's UNSAT is honest, not a bug")
        return

    dep_idx = {}
    arr_idx = {}
    for i, (kind, c, _) in enumerate(events):
        if kind == "depart":
            dep_idx[c] = i
        else:
            arr_idx.setdefault(c, i)

    # initial piles and blocking (mirror of the encoder)
    piles0 = [list(h) + list(v) for h, v in game.tableau]
    above = {}
    for p in piles0:
        for j, c in enumerate(p):
            above[c] = p[j + 1 :]

    def leave_idx(c):
        return arr_idx[c] if c in arr_idx else dep_idx[c]

    fails = []

    # family: block — X's first leave after all initial-above leaves
    for c in above:
        if c not in dep_idx:
            continue  # deck cards never in above
        if c in arr_idx:  # X's first leave is its arrival
            for z in above[c]:
                if leave_idx(z) > arr_idx[c]:
                    fails.append(("block", f"{z} above {c} not left before arrival"))
        else:  # X departs from initial
            for z in above[c]:
                if leave_idx(z) > dep_idx[c]:
                    fails.append(("block", f"{z} above {c} not left before depart"))

    # family: hosttop / deckhost / root — arrival preconditions
    for i, (kind, c, host) in enumerate(events):
        if kind not in ("move", "park"):
            continue
        if isinstance(host, Card):
            if host in game.deck and host not in above:
                # deck host: must have parked earlier
                if not (host in arr_idx and arr_idx[host] < i):
                    fails.append(("deckhost", f"{c} on deck host {host} not parked"))
            else:
                if host in arr_idx:
                    if arr_idx[host] > i:
                        fails.append(("hosttop", f"host {host} moved after {c} arrived"))
                else:
                    for z in above.get(host, ()):
                        if leave_idx(z) > i:
                            fails.append(
                                ("hosttop", f"{z} above host {host} not left before {c}")
                            )
        else:
            p = host[1]
            for y in piles0[p]:
                if leave_idx(y) > i:
                    fails.append(("root", f"pile {p} not empty when {c} landed"))

    # family: guesthost — guest departs before host departs
    for kind, c, host in events:
        if kind in ("move", "park") and isinstance(host, Card):
            if dep_idx[c] > dep_idx[host]:
                fails.append(("guesthost", f"guest {c} departs after host {host}"))

    # family: prefix — lower same-suit departs first
    for c in dep_idx:
        if c.rank > 0:
            lo = Card(c.rank - 1, c.suit)
            if dep_idx[lo] > dep_idx[c]:
                fails.append(("prefix", f"{lo} departs after {c}"))

    # family: excl — guest intervals disjoint per host
    by_host = {}
    for kind, c, host in events:
        if kind in ("move", "park"):
            by_host.setdefault(host, []).append((arr_idx[c], dep_idx[c], c))
    for host, ivs in by_host.items():
        for a in range(len(ivs)):
            for b in range(a + 1, len(ivs)):
                (s1, e1, c1), (s2, e2, c2) = ivs[a], ivs[b]
                if s1 < e2 and s2 < e1:
                    fails.append(("excl", f"{c1} and {c2} overlap on host {host}"))

    if not fails:
        print("ALL FAMILIES SATISFIED — the model should be SAT; the UNSAT is a clause bug")
    for fam, msg in fails[:20]:
        print(f"  FAIL {fam}: {msg}")
    print(f"{len(fails)} total violations" if fails else "")


if __name__ == "__main__":
    main()
