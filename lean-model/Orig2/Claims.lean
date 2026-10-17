import Orig2.Vocab

/-!
# Orig2.Claims — THE CLAIMS LAYER

The statements ledger: each claim is a frozen statement with its
`sorry` as honest debt, a PRICE line in its docstring (the content
that discharges it), and a promotion rule — when the proof lands,
the claim moves to the theorems tier (a future `Orig2/Theorems.lean`
or per-mission cards), the stub deleted, never duplicated.  The
debt only shrinks.

HOUSE FENCES BINDING THIS LAYER (from the registry's design notes
and the frozen-tier CHALLENGES):

* THE UNCONDITIONAL `reversibleAtW ↔ reversibleAt` IS FENCED: never
  state it uncalled — the ← direction pushes a negation through a
  universal into an existential and drags `Classical.choice` into
  every consumer's battery profile.  The WF-gated form below is the
  honest one (the oracle's constructive dichotomy); at wild states
  the negative form WITHOUT a witness is intuitionistically
  consistent — the divergence corners are witnessed in the
  frozen-tier archive.

## §0. The banked intuitionistic halves (zero-sorry, proved now)

The two constructive directions the old home banked at
`Orig/Fate.lean:97,105` — ported verbatim, the Claims layer's first
green rows. -/

/-- A witness proves the negative form — intuitionistic, axiom-free.
PORTED VERBATIM from `Orig/Fate.lean:97`. -/
theorem reversibleAt_of_W {st : State} {m : Move} (h : reversibleAtW st m) :
    reversibleAt st m := by
  obtain ⟨s₁, play, hstep, hrun⟩ := h
  intro contra
  exact contra s₁ play hstep hrun

/-- A commitment refutes every witness — intuitionistic, axiom-free.
PORTED VERBATIM from `Orig/Fate.lean:105`. -/
theorem not_reversibleAtW_of_irreversibleAt {st : State} {m : Move}
    (h : irreversibleAt st m) : ¬ reversibleAtW st m := by
  rintro ⟨s₁, play, hstep, hrun⟩
  exact absurd hrun (h s₁ play hstep)

/-!
## §1. The claims proper  (prices attached, sorries tracked)

CLAIM 1 — the oracle's WF-gated specification, in the registry's
reversible-first polarity (the updated `irreversible_iff_of`):
at a WF state the Bool oracle decides the semantic negative form
exactly, constructor by constructor.

PRICE: the classification program — the draw row (`drawIrr`'s
stock/waste cycle-mod reading), the two waste rows' trivial
commits, and the three table-move rows (chop/hidden-flip/bare-king
shapes).  Frozen-tier templates: `Orig/Classify.lean`'s
`drawClass`/`tabToFoundClass`/`foundToTabClass`/`tabToTabClass`
and the waste rows. -/

/-- **CLAIM `reversible_iff_of`** — the WF-gated oracle spec. -/
theorem reversible_iff_of {st : State} (hwf : st.WF) (m : Move) :
    reversibleAt st m ↔ reversibleOf st m = true := by
  sorry

/-!
CLAIM 2 — the **oracle ↔ carrier bridge** (owner formulation,
2026-10-17; supersedes the earlier `reversibleAtW ↔ reversibleAt`
stub — that one is now DERIVED content: Claim 1 + this claim give
it as a corollary, so it moved out of the claims ledger and into
the future theorems tier): at a WF state the Bool oracle and the
witness carrier are the same fact.

PRICE: → is cheap given Claim 1 (witness → §0's `reversibleAt_of_W`
→ oracle true).  ← is the deep half: the classification rows'
witness-CONSTRUCTION sides — shape-false hands the explicit undo
play, constructor by constructor (the effective dichotomy the
Fate design note priced as the program's method).  At wild states
BOTH directions are refuted by the archived divergence corners —
the WF gate is part of the claim's truth, not decoration. -/

/-- **CLAIM `reversibleOf_iff_reversibleAtW`** — the oracle meets
the witness carrier exactly at WF worlds. -/
theorem reversibleOf_iff_reversibleAtW {st : State} (hwf : st.WF)
    (m : Move) :
    reversibleOf st m = true ↔ reversibleAtW st m := by
  sorry

/-! ## The audit battery

Proved heads expect `[propext]`-class; the two §0 rows are the
layer's foundation pair.  Claim stubs carry `sorryAx` by design —
the debt ledger this file exists to track. -/

#print axioms reversibleAt_of_W
#print axioms not_reversibleAtW_of_irreversibleAt
