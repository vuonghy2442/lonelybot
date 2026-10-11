import Orig

/-!
# TWIN-CONTENTION CANDIDATE COUNTEREXAMPLE — verification probe

User-reported candidate (2026-10-11, decompression session relay): a
state with BOTH twins (c, c.twin) licensed, and a single contested
seat both contend for — "stacking either exercises fine, but
stacking A forecloses B; the state forks into 2."

Minimal craft (full-deck WF state `TC`): both black threes rung-ready
in their foundations (♠ = [A♠, 2♠], ♣ = [A♣, 2♣]), sitting BARE on
their own piles, and the ONE remaining red-four top 4♥ on pile 0 as
the single contested seat.  Everything else lives in the waste.

Cardinality verdict-row: at a WF state where a black-three twin pair
sits licensed-RAISABLE (each needing an under-seat of opposite-color
rank 4 by `CanRaise`'s seat clause), both red fours are consumed as
under-seats — so no red-four top can remain.  The literal candidate —
"both twins fully licensed raises AND a contended red-4 seat" — is
UNREALIZABLE at WF.  What IS realizable: rung-ready twins with a
single contested seat, and the two contenders are STACKINGS
(`tabToTab`), never canon's lifts.
-/

namespace TwinContentionProbe

set_option maxRecDepth 200000

private abbrev H (r : Rank) : Card := ⟨Suit.heart, r⟩
private abbrev S (r : Rank) : Card := ⟨Suit.spade, r⟩
private abbrev D (r : Rank) : Card := ⟨Suit.diamond, r⟩
private abbrev C (r : Rank) : Card := ⟨Suit.club, r⟩

private def restMinus (used : List Card) : List Card :=
  Card.universe.filter fun x => decide (¬ (x ∈ used))

private def tcFound : Suit → List Card
  | .spade => [S .ace, S .two]
  | .club => [C .ace, C .two]
  | _ => []

private def tcUsed : List Card :=
  [S .ace, S .two, C .ace, C .two, H .four, S .three, C .three, S .two]

private def tcPiles : Anchor → Pile
  | .p0 => ⟨[], [H .four]⟩        -- the single contested seat
  | .p1 => ⟨[], [S .three]⟩       -- twin one, bare
  | .p2 => ⟨[], [C .three]⟩       -- twin two, bare
  | _ => ⟨[], []⟩

def TC : State where
  found := tcFound
  piles := tcPiles
  stock := []
  waste := restMinus tcUsed
  drawStep := 1

private def decSt (s t : State) : Decidable (s = t) :=
  decidable_of_decidable_of_iff (p :=
    (s.found .spade = t.found .spade ∧ s.found .heart = t.found .heart ∧
     s.found .diamond = t.found .diamond ∧ s.found .club = t.found .club ∧
     s.piles .p0 = t.piles .p0 ∧ s.piles .p1 = t.piles .p1 ∧
     s.piles .p2 = t.piles .p2 ∧ s.piles .p3 = t.piles .p3 ∧
     s.piles .p4 = t.piles .p4 ∧ s.piles .p5 = t.piles .p5 ∧
     s.piles .p6 = t.piles .p6 ∧
     s.stock = t.stock ∧ s.waste = t.waste ∧ s.drawStep = t.drawStep))
    (by
      constructor
      · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
        apply State.ext
        · funext σ; cases σ <;> assumption
        · funext a; cases a <;> assumption
        · assumption
        · assumption
        · assumption
      · rintro rfl
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

local instance : DecidableEq State := fun s t => decSt s t

theorem TC_wf : TC.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s; cases s with
    | spade => exact ⟨2, rfl⟩
    | heart => exact ⟨0, rfl⟩
    | diamond => exact ⟨0, rfl⟩
    | club => exact ⟨2, rfl⟩
  · intro a; cases a <;> first | rfl | decide
  · intro c _; rcases c with ⟨s, r⟩; cases s <;> cases r <;> decide
  · decide

/-- Both twins are rung-ready. -/
theorem twins_rung_ready :
    TC.nextUp (S .three) = true ∧ TC.nextUp (C .three) = true := by decide

/-- The exclusivity verdict: with the single contested seat present
(the lone red-four top), the bare twins are NOT lift-licensed —
their seat clause fails. -/
theorem bare_twins_not_liftable :
    canRaiseB TC (S .three) = false ∧ canRaiseB TC (C .three) = false := by
  constructor <;> decide

/-- Both stacking moves claim the one seat — the fork is live. -/
theorem both_stackings_fire :
    (State.step TC (Move.tabToTab (S .three) (Sum.inr (H .four)))).isSome = true ∧
    (State.step TC (Move.tabToTab (C .three) (Sum.inr (H .four)))).isSome = true := by
  constructor <;> decide

/-- The two fork images. -/
def A1 : State := (State.step TC (Move.tabToTab (S .three) (Sum.inr (H .four)))).getD TC
def A2 : State := (State.step TC (Move.tabToTab (C .three) (Sum.inr (H .four)))).getD TC

/-- Stacking A forecloses B: the seat is consumed. -/
theorem stacking_A_forecloses_B :
    State.step A1 (Move.tabToTab (C .three) (Sum.inr (H .four))) = none := by decide

theorem stacking_B_forecloses_A :
    State.step A2 (Move.tabToTab (S .three) (Sum.inr (H .four))) = none := by decide

/-- The two fork images — the children are genuinely different
states; the fork is commit-live. -/
theorem fork_images_differ : ¬ (A1 = A2) := by decide

/-- Canon itself is FORK-FREE on the base state: the contention
never touches canonicalization — canon TC does nothing (all
licenses dead at the base: the twins sit bare, seat clause fails),
and the fork belongs to the commit side (the stacking moves the
successor program may choose between). -/
theorem canon_TC_fixed : canon TC = TC := by decide

/-- At each child, the CLAIMANT twin has become licensed (it now
sits on the contested seat with a surviving under-seat) — canon
MOVES at the children: the refuted prediction was "children are
fixed points". -/
theorem claimant_licensed_at_child :
    canRaiseB A1 (S .three) = true ∧ canRaiseB A2 (C .three) = true := by
  constructor <;> decide

/-- The leftover twin stays unlicensed at each child: bare on its
own pile, chop clause dead, not a king. -/
theorem leftover_bare_unlicensed :
    canRaiseB A1 (C .three) = false ∧ canRaiseB A2 (S .three) = false := by
  constructor <;> decide

/-- The saturation lifts exactly the claimant, so canon A1 ≠ A1
and canon A2 ≠ A2. -/
theorem canon_children_move :
    ¬ (canon A1 = A1) ∧ ¬ (canon A2 = A2) := by
  constructor <;> decide

/-- THE FORK SURVIVES INTO THE CANONICAL WORLD: the two canonical
finals are genuinely different states (which suit's foundation
book holds the twin-3 differs) — the retracted claim "forks
vanish at canon" does NOT cover contrended-seat stacking forks;
this fork is commit-side all the way through, and the canonical
forms inherit it. -/
theorem fork_survives_canonical_grade :
    ¬ (canon A1 = canon A2) := by decide

/-- THE ABSORB GRADE: the two canonical finals are related by the
COMPOSITE transform — the twin foundation-book relabel, the
p1↔p2 anchor rotation carrying a twin relabel of the rotated
leftover pile, and the settled seat left intact.  (The strict
whole-state twinMap fails: it would flip the settled seat 4♥ to
4♦ and disturb the rest-waste's exclusions.  The bare
{twin-pair} position-swap fails: it leaves a mixed suit book.
The composite is exact.) -/
private def ptw (p : Pile) : Pile :=
  ⟨p.hidden.map Card.twin, p.faceUp.map Card.twin⟩

theorem final_foundation_relabel_rotate_close :
    { (canon A1) with
        found := fun k => ((canon A1).found k.twin).map Card.twin
        piles := fun a =>
          match a with
          | .p1 => ptw ((canon A1).piles .p2)
          | .p2 => ptw ((canon A1).piles .p1)
          | x => (canon A1).piles x } = canon A2 := by
  decide

/-- THE PAIR-SWAP VERDICT (the strict whole-state reading): NO. -/
theorem not_global_twin_equal : ¬ (State.twinMap A1 = A2) := by decide

theorem not_global_twin_equal_final : ¬ (State.twinMap (canon A1) = canon A2) := by
  decide

/-- The empty canonical schedule at the base is the trivially
reversible run (the pick-raise grading: nothing fires at the
fork base; the firing happens commit-side). -/
theorem tc_schedule_trivially_reversible : StackRun TC [] TC := StackRun.nil TC

end TwinContentionProbe
