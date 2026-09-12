"""Milestone-1 SAT scheduler: the M=1/W=0 rung of the K-ladder.

The macro (commitment) game as a temporal-matching SAT instance:

- every card departs to the foundation exactly once (W=0: no worry-backs)
- every card visits at most one host after leaving its initial position
  (M=1: one relocation per card; deck cards park at most once)
- hosts are compatible cards (rank+1, opposite color) or, for kings,
  empty pile roots; a host serves one guest at a time
- draw-1: the deck is a free set (no ordering constraints — the K+
  representation; graph.py encodes the same)

SAT model -> a schedule; the replay validator checks it against the
concrete rules (the independent win certificate). UNSAT -> dead in the
M=1/W=0 subgame — a conditional refutation rung of the K-ladder.

Soundness notes for the UNSAT direction: the model must allow every
play the real M=1/W=0 subgame allows. The known liberties it takes
(audit list): hosting is permissive about pile identity (type-level),
and the initial blocker relation is the only source of blocking (guests
handled via exclusion). Validate against the engine corpus before
trusting UNSAT as a kill.
"""
import json
import os
import subprocess
import sys
import time

from pysat.formula import IDPool
from pysat.solvers import Cadical153

from graph import Card, Game, RANKS, SUITS

KING = len(RANKS) - 1
N_RANK = len(RANKS)
REPO = subprocess.run(
    ["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True, check=True
).stdout.strip()

# the main tree may be mid-edit by the other session; run deal/verdict
# fetches against a detached worktree at HEAD instead
WORKTREE = os.path.join(os.environ.get("TEMP", "."), "kilo", "lb-deal")
EXE = os.path.join(WORKTREE, "target", "release", "lonecli.exe")


def run_cli(*args):
    if not os.path.exists(EXE):
        subprocess.run(
            ["git", "worktree", "add", "--detach", WORKTREE, "HEAD"],
            cwd=REPO, check=True, capture_output=True,
        )
        subprocess.run(
            ["cargo", "build", "--release", "-p", "lonecli"],
            cwd=WORKTREE, check=True, capture_output=True,
        )
    r = subprocess.run([EXE, *args], capture_output=True, check=True)
    return r.stdout.decode("utf-8", errors="replace")


def color(suit: int) -> int:
    return suit // 2


def compat_hosts(card: Card):
    """Cards that can host `card`: rank+1, opposite color. Kings: None (roots)."""
    if card.rank == KING:
        return None
    return [Card(card.rank + 1, card.suit ^ 2), Card(card.rank + 1, card.suit ^ 3)]


class Event:
    __slots__ = ("card", "kind", "idx")

    def __init__(self, card, kind, idx):
        self.card = card
        self.kind = kind  # 'move' | 'park' | 'depart'
        self.idx = idx

    def __repr__(self):
        return f"{self.kind.title()}({self.card})"


class Encoder:
    # constraint families, disableable for bisection debugging
    FAMILIES = ("same", "block", "hosttop", "deckhost", "guesthost",
                "prefix", "excl", "root")

    def __init__(self, game: Game, off=()):
        self.game = game
        self.off = set(off)
        self.pool = IDPool()
        self.clauses = []
        self.piles = [list(h) + list(v) for h, v in game.tableau]  # bottom -> top
        self.deck = set(game.deck)
        self.all_cards = set()
        for p in self.piles:
            self.all_cards.update(p)
        self.all_cards.update(self.deck)
        self.above = {}
        self.loc0 = {}
        for i, p in enumerate(self.piles):
            for j, c in enumerate(p):
                # piles are bottom -> top; the cards blocking c are the
                # ones stacked ON it: the later indices
                self.above[c] = p[j + 1 :]
                self.loc0[c] = i
        for c in self.deck:
            self.loc0[c] = None  # deck

        # events: (optional) arrive + (mandatory) depart per card
        self.events = []
        self.arrive = {}
        self.depart = {}
        for c in sorted(self.all_cards):
            a = Event(c, "park" if c in self.deck else "move", len(self.events))
            self.events.append(a)
            d = Event(c, "depart", len(self.events))
            self.events.append(d)
            self.arrive[c] = a
            self.depart[c] = d

        # host domains
        self.domains = {}  # card -> [host_key]; host_key = Card | ('root', i)
        for c in self.all_cards:
            hs = compat_hosts(c)
            if hs is None:
                self.domains[c] = [("root", i) for i in range(len(self.piles))]
            else:
                self.domains[c] = list(hs)

        self._order_vars()
        self._occurrence()
        self._semantics()

    # ---- literal helpers -------------------------------------------------

    def lit(self, key):
        return self.pool.id(key)

    def occ_lit(self, card):
        return self.lit(("occ", card))

    def h_lit(self, guest_card, host_key):
        return self.lit(("h", guest_card, host_key))

    def lt_lit(self, e1: Event, e2: Event) -> int:
        """Literal TRUE iff e1 happens before e2."""
        if e1.idx < e2.idx:
            return self.lit(("lt", e1.idx, e2.idx))
        return -self.lit(("lt", e2.idx, e1.idx))

    def emit(self, clause):
        if clause:
            self.clauses.append(clause)

    # ---- construction ----------------------------------------------------

    def _order_vars(self):
        n = len(self.events)
        # transitivity, both directions of the total order:
        #   lt(a,b) & lt(b,c) -> lt(a,c)
        #   lt(a,c) -> lt(a,b) | lt(b,c)   (the between clause)
        for ia in range(n):
            for ib in range(ia + 1, n):
                lab = self.lit(("lt", ia, ib))
                for ic in range(ib + 1, n):
                    lbc = self.lit(("lt", ib, ic))
                    lac = self.lit(("lt", ia, ic))
                    self.clauses.append([-lab, -lbc, lac])
                    self.clauses.append([-lac, lab, lbc])
        # (totality is inherent: each pair literal is assigned)

    def _occurrence(self):
        for c in self.all_cards:
            a = self.arrive[c]
            occ = self.occ_lit(c)
            dom = self.domains[c]
            # h -> occ
            for hk in dom:
                self.emit([-self.h_lit(c, hk), occ])
            # occ -> or of hosts
            self.emit([-occ] + [self.h_lit(c, hk) for hk in dom])
            # at most one host
            for i in range(len(dom)):
                for j in range(i + 1, len(dom)):
                    self.emit([-self.h_lit(c, dom[i]), -self.h_lit(c, dom[j])])

    def _z_leaves(self, z: Card, e: Event, head):
        """Z must vacate its initial pile before event e; head = extra
        negative guards. Z leaves via its move (if any) or its depart."""
        zm = self.arrive[z]
        zd = self.depart[z]
        oz = self.occ_lit(z)
        # if z moved: zm < e
        self.emit(head + [-oz, self.lt_lit(zm, e)])
        # if z never moved: zd < e
        self.emit(head + [oz, self.lt_lit(zd, e)])

    def _semantics(self):
        for c in self.all_cards:
            a = self.arrive[c]
            d = self.depart[c]
            occ = self.occ_lit(c)
            in_deck = c in self.deck

            # (a) arrival precedes departure
            if not in_deck:
                self.emit([-occ, self.lt_lit(a, d)])

            # (b) initial blocking: X's arrival, and X's depart-from-initial
            #     (the latter only when X never moved)
            if not in_deck and "block" not in self.off:
                for z in self.above.get(c, ()):
                    self._z_leaves(z, a, [-occ])
                    self._z_leaves(z, d, [occ])  # off when c moved away first

            # (c) host preconditions
            for hk in self.domains[c]:
                h = self.h_lit(c, hk)
                if isinstance(hk, Card):
                    if hk in self.deck:
                        # deck hosts must have parked before being sat on
                        if "deckhost" not in self.off:
                            self.emit([-h, self.occ_lit(hk)])
                            self.emit([-h, self.lt_lit(self.arrive[hk], a)])
                    else:
                        # if the host moved, it moved before gaining guests
                        if "hosttop" not in self.off:
                            self.emit(
                                [-h, -self.occ_lit(hk), self.lt_lit(self.arrive[hk], a)]
                            )
                            # if it never moved, its initial blockers left first
                            for z in self.above.get(hk, ()):
                                self._z_leaves(z, a, [-h, self.occ_lit(hk)])
                    # guest leaves before the host departs
                    if "guesthost" not in self.off:
                        self.emit([-h, self.lt_lit(d, self.depart[hk])])
                else:
                    # root: every initial card of that pile left
                    if "root" not in self.off:
                        p = hk[1]
                        for y in self.piles[p]:
                            self._z_leaves(y, a, [-h])

            # (f) departure prefix
            if c.rank > 0 and "prefix" not in self.off:
                lower = Card(c.rank - 1, c.suit)
                self.emit([self.lt_lit(self.depart[lower], d)])

        # (d') host mutual exclusion (arrive..depart intervals disjoint)
        if "excl" not in self.off:
            by_host = {}
            for c in self.all_cards:
                for hk in self.domains[c]:
                    by_host.setdefault(hk, []).append(c)
            for hk, guests in by_host.items():
                for i in range(len(guests)):
                    for j in range(i + 1, len(guests)):
                        x1, x2 = guests[i], guests[j]
                        e1, e2 = self.arrive[x1], self.arrive[x2]
                        self.emit(
                            [
                                -self.h_lit(x1, hk),
                                -self.h_lit(x2, hk),
                                self.lt_lit(self.depart[x2], e1),
                                self.lt_lit(self.depart[x1], e2),
                            ]
                        )


# ---- replay validator ----------------------------------------------------


class ReplayError(Exception):
    pass


def replay(game: Game, schedule):
    """schedule: ordered list of (kind, card, host_key). Returns True iff
    the schedule is a legal concrete play that completes the foundations."""
    piles = [list(p) for p in (list(h) + list(v) for h, v in game.tableau)]
    deck = set(game.deck)
    loc = dict(Encoder.__dict__ and {})  # placeholder, real loc below
    loc = {}
    for i, p in enumerate(piles):
        for c in p:
            loc[c] = i
    found = [0] * 4

    for kind, x, hk in schedule:
        if kind in ("move", "park"):
            if kind == "park":
                if x not in deck:
                    raise ReplayError(f"{x} not in deck")
                deck.remove(x)
            else:
                pi = loc.get(x)
                if pi is None or piles[pi][-1] != x:
                    raise ReplayError(f"{x} not top of its pile")
                piles[pi].pop()
                loc.pop(x, None)
            if isinstance(hk, Card):
                ph = loc.get(hk)
                if ph is None or piles[ph][-1] != hk:
                    raise ReplayError(f"host {hk} not top")
                if hk.rank != x.rank + 1 or color(hk.suit) == color(x.suit):
                    raise ReplayError(f"{x} incompatible with host {hk}")
                piles[ph].append(x)
                loc[x] = ph
            else:
                p = hk[1]
                if piles[p]:
                    raise ReplayError(f"root {p} not empty")
                piles[p].append(x)
                loc[x] = p
        else:  # depart
            if x in deck:
                deck.remove(x)
            else:
                pi = loc.get(x)
                if pi is None or piles[pi][-1] != x:
                    raise ReplayError(f"{x} not top when departing")
                piles[pi].pop()
                loc.pop(x, None)
            if found[x.suit] != x.rank:
                raise ReplayError(f"{x}: foundation at {found[x.suit]}, need {x.rank}")
            found[x.suit] += 1

    return all(h == N_RANK for h in found), found


# ---- solve ----------------------------------------------------------------


def solve(game: Game):
    t0 = time.perf_counter()
    enc = Encoder(game)
    t_enc = time.perf_counter() - t0
    t0 = time.perf_counter()
    with Cadical153(bootstrap_with=enc.clauses) as s:
        sat = s.solve()
        model = set(s.get_model()) if sat else None
    t_sat = time.perf_counter() - t0
    if not sat:
        return {
            "verdict": "UNSAT",
            "t_enc": t_enc,
            "t_sat": t_sat,
            "n_vars": len(enc.pool.id2obj),
            "n_clauses": len(enc.clauses),
        }

    # extract the order and the host choices
    t0 = time.perf_counter()
    n = len(enc.events)
    succ = {i: [] for i in range(n)}
    indeg = {i: 0 for i in range(n)}
    for ia in range(n):
        for ib in range(ia + 1, n):
            lab = enc.lit(("lt", ia, ib))
            (a, b) = (ia, ib) if lab in model else (ib, ia)
            succ[a].append(b)
            indeg[b] += 1
    topo = []
    ready = [i for i in range(n) if indeg[i] == 0]
    while ready:
        i = ready.pop()
        topo.append(i)
        for j in succ[i]:
            indeg[j] -= 1
            if indeg[j] == 0:
                ready.append(j)
    assert len(topo) == n, "cyclic order (transitivity violated?)"

    schedule = []
    for i in topo:
        e = enc.events[i]
        if e.kind == "depart":
            schedule.append(("depart", e.card, None))
            continue
        if enc.occ_lit(e.card) not in model:
            continue
        host = next(
            (hk for hk in enc.domains[e.card] if enc.h_lit(e.card, hk) in model),
            None,
        )
        assert host is not None
        schedule.append((e.kind, e.card, host))

    try:
        win, found = replay(game, schedule)
        rep = "WIN" if win else f"INCOMPLETE (foundations {found})"
    except ReplayError as ex:
        rep = f"INVALID: {ex}"
    return {
        "verdict": f"SAT/{rep}",
        "t_enc": t_enc,
        "t_sat": t_sat,
        "t_extract": time.perf_counter() - t0,
        "n_vars": len(enc.pool.id2obj),
        "n_clauses": len(enc.clauses),
        "schedule": schedule,
    }


# ---- deal sources ---------------------------------------------------------


def deal_from_seed(seed: int) -> dict:
    out = run_cli("print", "default", str(seed))
    i, j = out.index("{"), out.rindex("}") + 1
    return json.loads(out[i:j])


def engine_verdict(seed: int, draw: int) -> bool:
    out = run_cli("solve-macro", "default", str(seed), str(draw))
    return "Solvable" in out


def main():
    if sys.argv[1] == "corpus":
        lo, hi = int(sys.argv[2]), int(sys.argv[3])
        kills = sat_wins = eng_wins = 0
        for seed in range(lo, hi + 1):
            game = Game.from_str(deal_from_seed(seed))
            res = solve(game)
            ev = engine_verdict(seed, 1)
            eng_wins += ev
            v = res["verdict"]
            sat_ok = v.startswith("SAT/WIN")
            sat_wins += sat_ok
            kills += (not ev) and v == "UNSAT"
            flag = ""
            if ev and not sat_ok:
                flag = "  <-- model missed a win (expected: M=1/W=0 is restrictive)"
            if (not ev) and sat_ok:
                flag = "  <-- CONTRADICTION: schedule wins but engine says Impossible"
            print(
                f"seed {seed}: engine={'win' if ev else 'LOSE'} sat={v} "
                f"[{res['t_enc']:.2f}s enc, {res['t_sat']:.2f}s sat]{flag}"
            )
        print(
            f"\ncorpus: {hi - lo + 1} games, {eng_wins} engine wins; "
            f"SAT found {sat_wins} wins; UNSAT killed {kills}/{hi - lo + 1 - eng_wins} losses"
        )
        return

    seed = int(sys.argv[1])
    game = Game.from_str(deal_from_seed(seed))
    res = solve(game)
    print(
        f"{res['verdict']}  [{res['n_vars']} vars, {res['n_clauses']} clauses, "
        f"enc {res['t_enc']:.2f}s, sat {res['t_sat']:.2f}s]"
    )
    if "schedule" in res and len(sys.argv) > 2 and sys.argv[2] == "-v":
        for step in res["schedule"]:
            print(" ", step)


if __name__ == "__main__":
    main()
