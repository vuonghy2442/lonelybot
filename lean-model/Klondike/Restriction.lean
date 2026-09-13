import Klondike.Initial

/-!
# The pile-to-pile restriction (B2) — scaffold

The engine never plays a bare pile-to-pile move: every run relocation
is *implicit* — either a shuffle detour (`pileStack`/`stackPile`, the
accommodation channel) or fused into a run-carrying `Reveal`
(state.rs:312 — "revealing a card by moving the top card to another
pile").  B2 is the claim that this restriction loses nothing: a dealt
game is winnable in the full physical game iff it is winnable with the
engine's move set.

**Why the naive form died** (witnesses/EngineWitness.lean, archived in
FARM.md's REFUTED section): the model's `reveal` is *bare-trigger* —
it seats the boundary card only while a visible card still sits on it —
while the engine's `Reveal` is run-carrying.  At arbitrary WF states
the concrete move subset is strictly weaker (the p2 = [♥3, ♠5, ♥4]
deadlock).  The repaired statement must therefore be scoped to what
the engine actually solves: **states reachable from a dealt game**.

**Where the twin swap enters** (already proven, ready to cite): the
B4 endgame's worry-back has *two* candidate bases — the rank-`r+1`,
opposite-colour twins (`Card.only_blocker_is_twin`).  The choice
between them is a placement equivalence, licensed exactly like §5.5's
`twinPair_placement_equi`: `solvable_relabel`/`solvable_flipAll`
(Relabel.lean, proven, axiom-clean) applied as a local swap under the
both-heights-equal condition.  No *local* two-card swap theorem is
needed for this skeleton.

## Proof route (the B2 main induction)

`←` of the headline is `solvable_of_engine` (Move.lean, proven).  `→`
is well-founded induction on `cascadeMeasure` (Dominance.lean —
proven, with `cascade_escape_progress`): at each state, case-split on
the first move of a winning play; every engine move is verbatim; a
`pilePile c b` is replayed per the step lemma below, and the escapes
(strict measure drops) are what make the induction well-founded rather
than circular.

The step's cases (the EngineWitness shapes are the fence posts):
1. **returnable base** (`canReturnBase`): the `stackPile`/`pileStack`
   detour — proven kits: `stackPile_pileStack_cancel`,
   `pileStack_comm_*` squares, `solvable_of_stackPile`.
2. **locked boundary carry** (the EngineWitness shape): the run sits
   on the hidden boundary — the worry-back ban routes through B4's
   `solvable_of_pileStack` (sorried crux, Theorems.lean) plus the
   rank-mate twin argument above.
3. **the deadlock escape hatch**: if a full-deck probe ever replays
   the EngineWitness state from `State.initial wdeal 1`, this file's
   statements fall and the model needs the run-carrying-reveal repair
   (track R, design decision — recorded in FARM.md).

Refute-first gate: reachability probe — reconstruct the EngineWitness
state by an *engine* play from `State.initial wdeal 1`
(`witnesses/EngineWitness.lean` has both).  If unreachable, the
`initialReachable` hypothesis is doing its job; if reachable,
escalate before farming the sorries below.
-/

/-- Reachable from a dealt game: the domain the engine actually plays
on, and the domain under which the pile-to-pile restriction is
believed to hold. -/
def initialReachable (st : State) : Prop :=
  ∃ (d : Deal) (s : Nat) (play : List Move), d.WF ∧ 0 < s ∧
    (State.initial d s).run play = some st

/-- **B2, the engine's license**: on states reached from a deal, the
full physical game and the engine's restricted move set have the same
solvability.  The `→` direction is `solvable_of_engine` (proven);
`←` is the restriction.

TODO(proof) **[H]**: the well-founded `cascadeMeasure` induction whose
per-move replay is `engine_replay_of_pilePile` below (plus the B4 crux
for the boundary-carry case).  Witness fence: `EngineWitness`'s state
must not satisfy `initialReachable` — the refute-first probe above
decides whether this statement stands as written. -/
theorem solvableEngine_iff_solvable_of_reachable {st : State}
    (hreach : initialReachable st) (hwf : st.WF) :
    st.solvableFrom ↔ st.solvableEngine := sorry

/-- **The replay step**: from a dealt-reachable state, a winning play
headed by a pile-to-pile move can be replaced by an engine-only win —
every pile-to-pile is implicit.

TODO(proof) **[H]**: case-split per the header's ledger.  Case 1 is
assembled from proven pieces (`stackPile_pileStack_cancel` +
`pileStack_comm_*` + the roundtrips); case 2 reduces to the B4 crux
`solvable_of_pileStack` — note its `hnotlock` gate matches exactly the
boundary-carry shape here (a locked sitter IS the EngineWitness
trigger); case 3 is the probe's alarm.  The twin placement in case 2's
endgame cites `solvable_flipAll` under the both-heights-equal license —
the same pattern as `twinPair_placement_equi`. -/
theorem engine_replay_of_pilePile {st : State}
    (hreach : initialReachable st) (hwf : st.WF) {c : Card} {b : Base}
    (hlegal : st.legal (Move.pilePile c b) = true)
    (hsol : st.solvableFrom) : st.solvableEngine := sorry
