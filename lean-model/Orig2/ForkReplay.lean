import Orig2.ForkInrExpRefute

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Replay — the inert-interior replay lemma is FALSE as posed

READ-ONLY scratch card (`Temp/`).  No source edit, no commit.  No `sorry`,
no `Classical.choice`, no `native_decide`; axiom battery at the tail.

The campaign's most-repeated gap is the **play-level replay of a non-empty inert
interior**: a play

```text
pre ++ raise c :: γ ++ pull c b :: post        (γ ≠ [], ReadSafe c γ, SeatInert b γ)
```

should strictly shorten (bubble the pull left across `γ`, collapse
`raise c ; pull c b` to the single slide `slide c b`).

This card settles the *play-algebra* form of that claim:

* **(a) `gated_shortens`** — if the pull is `Pullable` at the raise's image,
  the play shortens (the `Ready`-gated replay, proved);
* **(b) `ungated_false`** — the un-gated replay is **FALSE**, by the 19-card
  kernel witness of `Orig2/ForkInrExpRefute.lean`: the play

  ```text
  raise J♠ ; slide J♣ onto Q♥ ; pull J♠ onto Q♦
  ```

  has a non-empty, read-safe, seat-inert interior and is *shortest*;
* **(c) `gate_not_forced`** — the gate is not a consequence of the two
  inertness hypotheses (same witness: `foundTop` holds, `canPlace` fails).

Hence no induction on `γ` can prove the un-gated form, and no play-level
hypothesis weaker than `Pullable` replaces it.  The remaining obligation is
**structural** (a fact about split bottoms), not play algebra.

The witness mechanism is new relative to `Orig2/ForkPermRefute.lean`: the
interior slide's **base is the pile that the raise emptied**, so the slide is
not even a legal letter at the raise's origin, and the intended 2-letter
replacement `slide w b' ; slide c b` does not exist there.
-/

namespace ReplayKit

open MountainKit
open CommuteStep

/-! ## §1. The replay lemma, as posed, and its two companions -/

/-- **`InertInteriorShortens` — THE REPLAY LEMMA, EXACTLY AS POSED.**  Every
play `pre ++ raise c :: γ ++ pull c b :: post` with `γ` non-empty, read-safe for
`c` and seat-inert on `b` strictly shortens.  (This is the un-gated
`MtnPr.SameCardRelocation` — `Orig2/ForkRelocate.lean:563` — with the
non-emptiness of `γ` made explicit.) -/
def InertInteriorShortens : Prop :=
  ∀ (u v : State) (ρ pre γ post : List Move) (c : Card) (b : Base) (A B : State),
    u.WF → ShufflePlayW u ρ v →
    ρ = pre ++ Move.tabToFound c :: γ ++ Move.foundToTab c b :: post →
    ShufflePlayW u pre A →
    State.step A (Move.tabToFound c) = some B →
    (∀ q ∈ γ, SlideFwd.ReadSafe c q) →
    (∀ q ∈ γ, MtnPr.SeatInert b q) →
    γ ≠ [] →
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length

/-- **`InertInteriorShortensGated` — THE SAME WITH THE READINESS GATE.** -/
def InertInteriorShortensGated : Prop :=
  ∀ (u v : State) (ρ pre γ post : List Move) (c : Card) (b : Base) (A B : State),
    u.WF → ShufflePlayW u ρ v →
    ρ = pre ++ Move.tabToFound c :: γ ++ Move.foundToTab c b :: post →
    ShufflePlayW u pre A →
    State.step A (Move.tabToFound c) = some B →
    (∀ q ∈ γ, SlideFwd.ReadSafe c q) →
    (∀ q ∈ γ, MtnPr.SeatInert b q) →
    γ ≠ [] →
    PullKit.Pullable B c b →
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length

/-- **`GateForced`** — the inertness hypotheses would already force the pull to
be legal at the raise's image (the gate of `PullKit.PullReadyAtImage`,
`Orig2/ForkPullSwaps.lean:768`, with the explicit non-emptiness). -/
def GateForced : Prop :=
  ∀ (u v : State) (ρ pre γ post : List Move) (c : Card) (b : Base) (A B : State),
    u.WF → ShufflePlayW u ρ v →
    ρ = pre ++ Move.tabToFound c :: γ ++ Move.foundToTab c b :: post →
    ShufflePlayW u pre A →
    State.step A (Move.tabToFound c) = some B →
    (∀ q ∈ γ, SlideFwd.ReadSafe c q) →
    (∀ q ∈ γ, MtnPr.SeatInert b q) →
    γ ≠ [] →
    PullKit.Pullable B c b

/-! ## §2. (a) The gated replay is a theorem -/

/-- **THE GATED REPLAY.**  Readiness at the raise's image is *sufficient*: the
pull bubbles left across the whole interior and `raise ; pull` collapses. -/
theorem gated_shortens : InertInteriorShortensGated := by
  intro u v ρ pre γ post c b A B huwf hplay hρ hpre hstep hread hseat _ hpull
  exact BaseEn.shortens_of_readyAtImage huwf hplay hρ hpre hstep hread hseat hpull.2

/-! ## §3. (b) The un-gated replay is false — the kernel witness -/

/-- **THE UN-GATED REPLAY IS FALSE.**  On the 19-card board of
`Orig2/ForkInrExpRefute.lean` the 3-letter play

```text
raise J♠ ; slide J♣ onto Q♥ ; pull J♠ onto Q♦
```

has a *non-empty* interior (`γ = [slide J♣ onto Q♥]`) that is `ReadSafe J♠` and
`SeatInert (inr Q♦)`, and no shorter play exists (`InrExpRefute.no_short`). -/
theorem ungated_false : ¬ InertInteriorShortens := by
  intro h
  have hshort := h InrExpRefute.u InrExpRefute.v
    [Move.tabToFound InrExpRefute.cJ,
      Move.tabToTab InrExpRefute.cZj (Sum.inr InrExpRefute.cQh),
      Move.foundToTab InrExpRefute.cJ (Sum.inr InrExpRefute.cQd)]
    [] [Move.tabToTab InrExpRefute.cZj (Sum.inr InrExpRefute.cQh)] []
    InrExpRefute.cJ (Sum.inr InrExpRefute.cQd) InrExpRefute.u InrExpRefute.s1
    InrExpRefute.u_wf InrExpRefute.play rfl (Walk.nil InrExpRefute.u)
    InrExpRefute.step_raise
    (by
      intro q hq
      rw [List.mem_singleton] at hq
      subst hq
      exact InrExpRefute.interior_readSafe)
    (by
      intro q hq
      rw [List.mem_singleton] at hq
      subst hq
      exact InrExpRefute.interior_seatInert)
    (by simp)
  obtain ⟨ρ', hplay', hlen⟩ := hshort
  have h3 := InrExpRefute.no_short ρ' hplay'
  simp only [List.length_cons, List.length_nil] at hlen
  omega

/-! ## §4. (c) The gate is not implied by the inertness hypotheses -/

/-- At the raise's image the pull `J♠ onto Q♦` is **not** legal: `Q♦` is still
covered by `J♣`.  (The frontier licence `foundTop` *does* hold — only
`canPlace` fails, so readiness is genuinely a seat fact.) -/
theorem s1_canPlace_J : InrExpRefute.s1.canPlace InrExpRefute.cJ
    (Sum.inr InrExpRefute.cQd) = false := by decide

/-- **THE GATE IS NOT FORCED.**  `ReadSafe + SeatInert` (with `γ ≠ []`) do not
imply `Pullable` at the raise's image. -/
theorem gate_not_forced : ¬ GateForced := by
  intro h
  have hpull := h InrExpRefute.u InrExpRefute.v
    [Move.tabToFound InrExpRefute.cJ,
      Move.tabToTab InrExpRefute.cZj (Sum.inr InrExpRefute.cQh),
      Move.foundToTab InrExpRefute.cJ (Sum.inr InrExpRefute.cQd)]
    [] [Move.tabToTab InrExpRefute.cZj (Sum.inr InrExpRefute.cQh)] []
    InrExpRefute.cJ (Sum.inr InrExpRefute.cQd) InrExpRefute.u InrExpRefute.s1
    InrExpRefute.u_wf InrExpRefute.play rfl (Walk.nil InrExpRefute.u)
    InrExpRefute.step_raise
    (by
      intro q hq
      rw [List.mem_singleton] at hq
      subst hq
      exact InrExpRefute.interior_readSafe)
    (by
      intro q hq
      rw [List.mem_singleton] at hq
      subst hq
      exact InrExpRefute.interior_seatInert)
    (by simp)
  exact absurd hpull.2 (by rw [s1_canPlace_J]; simp)

/-! ## §5. The trichotomy -/

/-- **THE LANE'S TRICHOTOMY.**  (a) the gated replay is a theorem; (b) the
un-gated replay is false; (c) the gate is not implied by the inertness
hypotheses.  Therefore the residual can only be closed *structurally*. -/
theorem replay_trichotomy :
    InertInteriorShortensGated ∧ ¬ InertInteriorShortens ∧ ¬ GateForced :=
  ⟨gated_shortens, ungated_false, gate_not_forced⟩

/-! ## §6. What this means for the two campaign lanes

* **`LandingResidual` / `UncoverResidual`** (`Orig2/ForkLandResReduction.lean`)
  do **not** fit `InertInteriorShortens`: there the cover and the uncover are
  slides of the *same* card `x`, and the state-level net-zero
  `LandRes.slideSt_slideSt_self` already identifies the pair with the single
  slide `slide x b''` — *no readiness gate is involved*.  The missing step
  there is the **replay of the interior between the two slides from the
  pre-cover state**, which is a different obligation (and is *not* refuted by
  the witness: the witness's interior is a slide of a different card `w`).

* **`TailHead.sameCard_turn_atLeastTwoSlides`**
  (`Orig2/ForkTailHead.lean:429`) lives in `InertInteriorShortens`'s regime: a
  same-card raise/pull with ≥ 2 slides in the free tail.  By (b)+(c) that case
  cannot be closed by a play-level replay lemma; the needed fact is structural
  (saturation / the split's `SplitHyp` data).  The `|slides| ≤ 1` stratum is
  unaffected.
-/

end ReplayKit

#print axioms ReplayKit.gated_shortens
#print axioms ReplayKit.ungated_false
#print axioms ReplayKit.s1_canPlace_J
#print axioms ReplayKit.gate_not_forced
#print axioms ReplayKit.replay_trichotomy
