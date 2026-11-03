import Orig2.Fork.Class.ForkRaiseReorderProof

set_option autoImplicit false

/-!
# Temp/RungMono — the rung is monotone along a licensed raiseS word

A `raiseS` step slides (cargo legs, rung-inert) and then raises exactly one
card, so it adds exactly one to that card's suit rung and fixes every other
suit.  Consequently a licensed `raiseS` word `ws` moves a suit's rung by
exactly the number of letters of that suit in `ws` — in particular the rung
can only *climb*, never fall.

Reused from the library (nothing is reproved):

* `OneColourClosure.cargoPath_rungAt` — cargo legs move no rung;
* `Orig2.Substrate.Position.rungAt_tabToFound` — a raise is `+1` on its suit;
* `OneColourClosure.RaiseSSeqLicensed.rungAt_eq` — the exact ledger of a
  licensed word (rung = start + count of the suit in the word);
* `List.countP_eq_length_filter` — `countP` is the filtered length.
-/

namespace RungMono

open OneColourClosure

/-! ## §1. One step -/

/-- **A single `raiseS` step.**  Sliding is rung-inert, so the raise is the
only event: the raised card's suit goes up by exactly one and every other
suit is untouched. -/
theorem rungAt_raiseStepS {z z' : State} {c : Card} (h : RaiseStepS z z' c) :
    rungAt z' c.suit = rungAt z c.suit + 1 ∧
      ∀ σ : Suit, σ ≠ c.suit → rungAt z' σ = rungAt z σ := by
  obtain ⟨z₀, hp, hstep⟩ := h
  refine ⟨?_, ?_⟩
  · rw [rungAt_tabToFound hstep c.suit, ite_eq_left rfl,
      ← cargoPath_rungAt hp c.suit]
  · intro σ hσ
    rw [rungAt_tabToFound hstep σ, ite_eq_right hσ]
    exact (cargoPath_rungAt hp σ).symm

/-! ## §2. The word, with no letter of the suit -/

/-- **A licensed word with no letter of `σ` leaves `σ`'s rung where it was.** -/
theorem rungAt_eq_of_no_letter {s z : State} {ws : List Card}
    (h : RaiseSSeqLicensed s ws z) {σ : Suit}
    (hno : ∀ d ∈ ws, d.suit ≠ σ) :
    rungAt z σ = rungAt s σ := by
  induction h with
  | nil => rfl
  | cons htail hS hp hstep ih =>
      rename_i zz zz0 zz' cc wws
      have hcc : cc.suit ≠ σ := hno cc (List.mem_cons_self ..)
      have htail_no : ∀ d ∈ wws, d.suit ≠ σ :=
        fun d hd => hno d (List.mem_cons_of_mem cc hd)
      have hrest : rungAt zz σ = rungAt s σ := ih htail_no
      have hcargo : rungAt zz0 σ = rungAt zz σ :=
        (cargoPath_rungAt hp σ).symm
      rw [rungAt_tabToFound hstep σ, ite_eq_right (Ne.symm hcc), hcargo, hrest]

/-- **The rung never falls along a licensed word whose letters avoid `σ`.** -/
theorem rungAt_le_of_raiseSSeqLicensed {s z : State} {ws : List Card}
    (h : RaiseSSeqLicensed s ws z) {σ : Suit}
    (hno : ∀ d ∈ ws, d.suit ≠ σ) :
    rungAt z σ ≤ rungAt s σ := by
  rw [rungAt_eq_of_no_letter h hno]
  exact Nat.le_refl _

/-! ## §3. The exact ledger -/

/-- **The exact ledger, in filtered-length form.**  After a licensed word
`ws`, a suit's rung is its starting value plus the number of letters of that
suit in `ws`. -/
theorem rungAt_add_count {s z : State} {ws : List Card}
    (h : RaiseSSeqLicensed s ws z) (σ : Suit) :
    rungAt z σ = rungAt s σ +
      (ws.filter (fun d => decide (d.suit = σ))).length := by
  rw [h.rungAt_eq σ, List.countP_eq_length_filter]

/-- **The rung never falls along a licensed word** — no side condition on the
word: every letter only adds to its own suit's rung. -/
theorem rungAt_le {s z : State} {ws : List Card}
    (h : RaiseSSeqLicensed s ws z) (σ : Suit) :
    rungAt s σ ≤ rungAt z σ := by
  rw [rungAt_add_count h σ]
  exact Nat.le_add_right _ _

end RungMono

#print axioms RungMono.rungAt_raiseStepS
#print axioms RungMono.rungAt_eq_of_no_letter
#print axioms RungMono.rungAt_le_of_raiseSSeqLicensed
#print axioms RungMono.rungAt_add_count
#print axioms RungMono.rungAt_le
