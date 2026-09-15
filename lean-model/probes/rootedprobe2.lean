import Klondike.Move

/-! # Rooted-bridge probe 2: the CleanAt shape vs. the blockade witnesses.

The iterated deep-hole premise's clearing condition (`State.CleanAt`,
TwinBridge.lean §4 — copied VERBATIM here because TwinBridge's olean is
stale mid-session), instantiated at the two witnesses that killed the
plain single-detach form: in both, the validated clearing prefix is
π₀ = [pileStack ♥10], and ♥10 is off each witness's protected zone
{t, t', z, z', c, r₁} — the card-level content of "the clearing move is
CleanAt".  The play-level validation (the clearing stack, then the
detach, then the same merge, winning on BOTH sides at both witnesses,
heights [13,13,13,13]) is detour.lean's playIter/playIterX and
detour2.lean's playIter2/playIter2X. -/

def CleanAt (m : Move) (t z z' c r₁ : Card) : Prop :=
  ∃ q : Card, m = Move.pileStack q ∧
    q ≠ t ∧ q ≠ t.flipSuit ∧ q ≠ z ∧ q ≠ z' ∧ q ≠ c ∧ q ≠ r₁

def c_ (s : Suit) (r : Rank) : Card := Card.mk s r

/-- Witness 1 (detour.lean): t = ♠Q, t' = ♣Q, z = ♥J, z' = ♦J, c = ♥Q,
r₁ = ♣J — the clearing move pileStack ♥10 (which frees the blocker-ridden
candidate top ♦Q) is CleanAt. -/
example : CleanAt (Move.pileStack (c_ .heart .ten)) (c_ .spade .queen)
    (c_ .heart .jack) (c_ .diamond .jack) (c_ .heart .queen) (c_ .club .jack) :=
  ⟨_, rfl, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Witness 2 (detour2.lean): t = ♥Q, t' = ♦Q, z = ♠J, z' = ♣J, c = ♦J,
r₁ = ♥K — the clearing move pileStack ♥10 (which frees the anchor p3 for
the king rider) is CleanAt. -/
example : CleanAt (Move.pileStack (c_ .heart .ten)) (c_ .heart .queen)
    (c_ .spade .jack) (c_ .club .jack) (c_ .diamond .jack) (c_ .heart .king) :=
  ⟨_, rfl, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The detour-lean mirror-replay condition rides the same zone: at both
witnesses the moved root of the DETOUR (r₁) is off the twin pair and both
cargos, and the twins sit off r₁'s run — the shapes the bridge's
`exchangeTwinCargo_step_pilePile` consumes (detour.lean's own #evals:
t, t' ∉ aboveOf r₁ at both). -/
example : (c_ .club .jack) ≠ (c_ .spade .queen) ∧ (c_ .club .jack) ≠ (c_ .club .queen) ∧
    (c_ .club .jack) ≠ (c_ .heart .jack) ∧ (c_ .club .jack) ≠ (c_ .diamond .jack) ∧
    (c_ .heart .king) ≠ (c_ .heart .queen) ∧ (c_ .heart .king) ≠ (c_ .diamond .queen) ∧
    (c_ .heart .king) ≠ (c_ .spade .jack) ∧ (c_ .heart .king) ≠ (c_ .club .jack) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
