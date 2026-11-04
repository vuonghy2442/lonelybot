import Orig2.Fork.Class.ForkRaiseReorderKit
import Orig2.Fork.Class.ForkRaiseReorderProof
import Orig2.Fork.Split.ForkDrainInduction
import Orig2.Fork.Commute.RungMono
import Orig2.Fork.Commute.RaisesOrFork
import Orig2.Fork.Commute.SatDiffer_config
import Orig2.Fork.Commute.FrozenSuit
import Orig2.Fork.Commute.Fork_producer

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Temp/SpectrumCollapse — draining the spectrum onto a twin pair

This card supplies the **spectrum containment** consumed by the sibling
producers `OneColourClosure.fork_of_collapsed_spectrum` /
`fork_of_spectrum` (`Orig2/Fork/Commute/RaisesOrFork.lean`, committed).  Those producers are
**not reproved here**.

Main theorem (the requested shape):

```lean
theorem spectrum_pair_by_draining {z : State} (hz : z.WF) {x : Card}
    (hx : CanRaiseS z x) (hxt : CanRaiseS z x.twin) :
    ∃ z', sameOrbitSetoid.r z z' ∧
      (∀ c, CanRaiseS z' c → c = x ∨ c = x.twin)
```

The drain raises every `S`-live card outside the pair, terminates on
`52 - Drain.rungSum` (`rungSum_raiseStepS`, `Drain.rungSum_le_52`), and keeps
both twins `S`-live.  Preservation per letter uses the brief's split:
`d.rank ≠ x.rank` → `canRaiseS_step_of_rank_ne`; `d.rank = x.rank`,
`d ∉ {x, x.twin}` → `SatDifferConfig.licence_lost_only_by_twin`.

## The unblocking caveat (the honest dichotomy)

The drain does **not** imply `¬ CanRaise z' x.twin`: draining a card that sits
on `x.twin` removes the cover and can expose the twin.  At a collapsed
spectrum with both twins `S`-live, `ForkWitness z' x` is *exactly* the block
`¬ CanRaise z' x.twin`; but the opposite orientation is a fork just as well:

* twin vanilla and `x` blocked ⇒ `ForkWitness z' x.twin` (because
  `x.twin.twin = x`);
* both twins vanilla ⇒ the both-vanilla square `twin_raise_square_both`
  applies (`Orig2/Fork/Commute/RaisesOrFork.lean`).

Hence the exhaustive endpoint statement is a **trichotomy**
(`spectrum_pair_trichotomy`), not the naive two-branch template.  The naive
template with the first arm restricted to `¬ CanRaise z' x.twin` misses the
flipped fork and is not provable; the corrected two-arm form is

```lean
theorem spectrum_pair_dichotomy {z : State} (hz : z.WF) {x : Card}
    (hx : CanRaiseS z x) (hxt : CanRaiseS z x.twin) :
    (∃ z', sameOrbitSetoid.r z z' ∧ (∀ c, CanRaiseS z' c → c = x ∨ c = x.twin) ∧
        (¬ CanRaise z' x.twin ∨ ¬ CanRaise z' x))
    ∨ (∃ z', sameOrbitSetoid.r z z' ∧ (∀ c, CanRaiseS z' c → c = x ∨ c = x.twin) ∧
        CanRaise z' x ∧ CanRaise z' x.twin)
```

and, packaging the first arm as a fork (`Fork z`),

```lean
theorem spectrum_pair_fork_or_both {z : State} (hz : z.WF) {x : Card}
    (hx : CanRaiseS z x) (hxt : CanRaiseS z x.twin) :
    Fork z ∨
      ∃ z', sameOrbitSetoid.r z z' ∧
        (∀ c, CanRaiseS z' c → c = x ∨ c = x.twin) ∧
        CanRaise z' x ∧ CanRaise z' x.twin
```

House rules: no `sorry`, no `Classical`, no `noncomputable`; `Orig2/` and the
existing `Temp/*.lean` cards are read-only.
-/

namespace SpectrumCollapse

open OneColourClosure

/-! ## §1. A drained letter outside the pair keeps the pair live -/

/-- **Raising an outside card preserves both twins' `S`-licence.**  The rank
split is exactly the brief's: a letter of a different rank is licence-inert
(`canRaiseS_step_of_rank_ne`), and a letter of the twins' rank other than the
twins is inert (`SatDifferConfig.licence_lost_only_by_twin`).  `hz : z.WF` is
required by both rows; `RaiseStepS` alone does not imply well-formedness. -/
theorem drain_pair_stays_live {z z' : State} {d x : Card} (hz : z.WF)
    (hstep : RaiseStepS z z' d)
    (hd : d ≠ x) (hdt : d ≠ x.twin)
    (hx : CanRaiseS z x) (hxt : CanRaiseS z x.twin) :
    CanRaiseS z' x ∧ CanRaiseS z' x.twin := by
  have hx' : CanRaiseS z' x := by
    by_cases hr : d.rank = x.rank
    · exact SatDifferConfig.licence_lost_only_by_twin hz hstep hr hd hdt hx
    · exact canRaiseS_step_of_rank_ne hz hstep hr hx
  have hxt' : CanRaiseS z' x.twin := by
    by_cases hr : d.rank = x.rank
    · have hr' : d.rank = x.twin.rank := by
        rw [Card.twin_rank]; exact hr
      exact SatDifferConfig.licence_lost_only_by_twin hz hstep hr' hdt
        (by simpa [card_twin_twin] using hd) hxt
    · have hr' : d.rank ≠ x.twin.rank := by
        rw [Card.twin_rank]; exact hr
      exact canRaiseS_step_of_rank_ne hz hstep hr' hxt
  exact ⟨hx', hxt'⟩

/-! ## §2. The rank-sum measure of a `RaiseStepS` letter -/

/-- **A `RaiseStepS` letter climbs the rank sum by exactly one.**  The cargo
prefix is rung-inert and the raise bumps exactly one suit; the sum is
`Drain.rungSum`. -/
theorem rungSum_raiseStepS {z z' : State} {d : Card} (h : RaiseStepS z z' d) :
    Drain.rungSum z' = Drain.rungSum z + 1 := by
  unfold Drain.rungSum
  obtain ⟨hclimb, hfix⟩ := RungMono.rungAt_raiseStepS h
  have hmap : (Suit.all.map (fun s => rungAt z' s)) =
      Suit.all.map (fun s => if s = d.suit then rungAt z s + 1 else rungAt z s) := by
    apply List.map_congr_left
    intro σ _
    by_cases hσ : σ = d.suit
    · rw [ite_eq_left hσ, hσ]
      exact hclimb
    · rw [ite_eq_right hσ]
      exact hfix σ hσ
  rw [hmap]
  exact Drain.sum_map_ite_bump Suit.all (fun s => rungAt z s) d.suit
    Drain.suit_all_nodup (Suit.mem_all d.suit)

/-! ## §3. The drain loop -/

/-- **The drain engine.**  From a `WF` state `z` with both twins `S`-live,
licensed raises of cards outside the pair terminate at a class-mate whose
`S`-live set is contained in `{x, x.twin}`, with both twins still live.

The search is the constructive census `Drain.drainLiveB`; the witness
extractor is `Drain.exists_of_all_false` (no `Classical.choice`). -/
theorem drain_aux (x : Card) (n : Nat) :
    ∀ z : State, z.WF → 52 - Drain.rungSum z ≤ n →
      CanRaiseS z x → CanRaiseS z x.twin →
      ∃ ws z', RaiseSSeqLicensed z ws z' ∧
        (∀ c, CanRaiseS z' c → c = x ∨ c = x.twin) ∧
        sameOrbitSetoid.r z z' ∧
        CanRaiseS z' x ∧ CanRaiseS z' x.twin := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro z hz hle hx hxt
      cases hb : Drain.drainLiveB z x with
      | true =>
          have hsub : ∀ c, CanRaiseS z c → c = x ∨ c = x.twin :=
            (Drain.drainLiveB_iff hz x).mp hb
          exact ⟨[], z, RaiseSSeqLicensed.nil z, hsub,
            sameOrbitSetoid.iseqv.refl z, hx, hxt⟩
      | false =>
          obtain ⟨c, -, hcf⟩ :=
            Drain.exists_of_all_false (p := fun c =>
              !(canRaiseSB z c) || decide (c = x) || decide (c = x.twin))
              (by simpa only [Drain.drainLiveB] using hb)
          rw [Bool.or_eq_false_iff, Bool.or_eq_false_iff] at hcf
          obtain ⟨⟨hnot, hdeq⟩, hteq⟩ := hcf
          have hprobe : canRaiseSB z c = true := by
            cases hp : canRaiseSB z c with
            | true => rfl
            | false => rw [hp] at hnot; simp at hnot
          have hcx : c ≠ x := of_decide_eq_false hdeq
          have hct : c ≠ x.twin := of_decide_eq_false hteq
          have hSc : CanRaiseS z c := (canRaiseSB_iff hz).mp hprobe
          obtain ⟨z', hstepS⟩ := raiseStepS_of_canRaiseS hSc
          have hz' : z'.WF := raiseStepS_wf hz hstepS
          have hpair := drain_pair_stays_live hz hstepS hcx hct hx hxt
          have hsum : Drain.rungSum z' = Drain.rungSum z + 1 :=
            rungSum_raiseStepS hstepS
          have hlt : 52 - Drain.rungSum z' < n := by
            have hbound : Drain.rungSum z' ≤ 52 := Drain.rungSum_le_52 hz'
            omega
          obtain ⟨ws, w, hpath, hsub, horb, hwx, hwxt⟩ :=
            ih (52 - Drain.rungSum z') hlt z' hz' (Nat.le_refl _)
              hpair.1 hpair.2
          obtain ⟨z₀, hp, hs⟩ := hstepS
          have hletter : RaiseSSeqLicensed z [c] z' :=
            RaiseSSeqLicensed.cons (RaiseSSeqLicensed.nil z) hSc hp hs
          have hfull : RaiseSSeqLicensed z (ws ++ [c]) w :=
            RaiseSSeqLicensed.append hletter hpath
          exact ⟨ws ++ [c], w, hfull, hsub,
            RevEqW_symm (RaiseSSeqLicensed.revEqW hfull hz), hwx, hwxt⟩

/-- **SPECTRUM CONTAINMENT BY DRAINING.**  Draining every `S`-live card outside
`{x, x.twin}` reaches a class-mate whose `S`-live set is contained in the pair.
This is the input `fork_of_collapsed_spectrum` / `fork_of_spectrum` consume. -/
theorem spectrum_pair_by_draining {z : State} (hz : z.WF) {x : Card}
    (hx : CanRaiseS z x) (hxt : CanRaiseS z x.twin) :
    ∃ z', sameOrbitSetoid.r z z' ∧
      (∀ c, CanRaiseS z' c → c = x ∨ c = x.twin) := by
  obtain ⟨ws, z', hpath, hsub, horb, -, -⟩ :=
    drain_aux x (52 - Drain.rungSum z) z hz (Nat.le_refl _) hx hxt
  exact ⟨z', horb, hsub⟩

/-- The strengthened form: the endpoint also keeps both twins `S`-live. -/
theorem spectrum_pair_by_draining_live {z : State} (hz : z.WF) {x : Card}
    (hx : CanRaiseS z x) (hxt : CanRaiseS z x.twin) :
    ∃ ws z', RaiseSSeqLicensed z ws z' ∧
      (∀ c, CanRaiseS z' c → c = x ∨ c = x.twin) ∧
      sameOrbitSetoid.r z z' ∧ CanRaiseS z' x ∧ CanRaiseS z' x.twin :=
  drain_aux x (52 - Drain.rungSum z) z hz (Nat.le_refl _) hx hxt

/-! ## §4. The endpoint trichotomy and the honest dichotomy -/

/-- At a collapsed spectrum with both twins `S`-live, the spectrum equality
for the pair `{x, x.twin}` is exactly the inclusion hypothesis. -/
theorem spectrum_iff_of_subset {z : State} {x : Card}
    (hx : CanRaiseS z x) (hxt : CanRaiseS z x.twin)
    (hsub : ∀ c, CanRaiseS z c → c = x ∨ c = x.twin) :
    ∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS z c := by
  intro c
  exact ⟨fun h => by rcases h with rfl | rfl; exact hx; exact hxt, hsub c⟩

/-- **The flipped witness.**  If the spectrum has collapsed onto the pair and
`x` is the blocked twin, then `x.twin` is a fork witness, because
`x.twin.twin = x`.  This is the case the naive two-branch template misses. -/
theorem forkWitness_twin_of_blocked_x {z : State} {x : Card}
    (hx : CanRaiseS z x) (hxt : CanRaiseS z x.twin)
    (hsub : ∀ c, CanRaiseS z c → c = x ∨ c = x.twin)
    (hblk : ¬ CanRaise z x) : ForkWitness z x.twin := by
  have hspec : ∀ c, (c = x.twin ∨ c = x.twin.twin) ↔ CanRaiseS z c := by
    intro c
    constructor
    · rintro (rfl | h)
      · exact hxt
      · rw [card_twin_twin] at h
        rw [h]
        exact hx
    · intro hc
      rcases hsub c hc with h | h
      · exact Or.inr (by rw [h, card_twin_twin])
      · exact Or.inl h
  exact forkWitness_of_spectrum hspec (by simpa [card_twin_twin] using hblk)

/-- **ENDPOINT TRICHOTOMY.**  At the drain endpoint exactly one of three things
holds: `x`'s twin is blocked (fork), `x` itself is blocked (the flipped fork),
or both twins are vanilla-raisable (the square case).  All three are read at
the same endpoint. -/
theorem spectrum_pair_trichotomy {z : State} (hz : z.WF) {x : Card}
    (hx : CanRaiseS z x) (hxt : CanRaiseS z x.twin) :
    ∃ z', sameOrbitSetoid.r z z' ∧
      (∀ c, CanRaiseS z' c → c = x ∨ c = x.twin) ∧
      (ForkWitness z' x ∨ ForkWitness z' x.twin ∨
        (CanRaise z' x ∧ CanRaise z' x.twin)) := by
  obtain ⟨ws, z', hpath, hsub, horb, hx', hxt'⟩ :=
    spectrum_pair_by_draining_live hz hx hxt
  refine ⟨z', horb, hsub, ?_⟩
  have hspec := spectrum_iff_of_subset hx' hxt' hsub
  cases hb : tabToFoundR z' x.twin with
  | false =>
      have hblk : ¬ CanRaise z' x.twin := by
        intro h
        have htrue : tabToFoundR z' x.twin = true :=
          (tabToFoundR_iff_canRaise z' x.twin).mpr h
        rw [hb] at htrue
        exact Bool.noConfusion htrue
      exact Or.inl (forkWitness_of_spectrum hspec hblk)
  | true =>
      have hvt : CanRaise z' x.twin :=
        (tabToFoundR_iff_canRaise z' x.twin).mp hb
      cases ha : tabToFoundR z' x with
      | false =>
          have hblk : ¬ CanRaise z' x := by
            intro h
            have htrue : tabToFoundR z' x = true :=
              (tabToFoundR_iff_canRaise z' x).mpr h
            rw [ha] at htrue
            exact Bool.noConfusion htrue
          exact Or.inr (Or.inl (forkWitness_twin_of_blocked_x hx' hxt' hsub hblk))
      | true =>
          have hvx : CanRaise z' x := (tabToFoundR_iff_canRaise z' x).mp ha
          exact Or.inr (Or.inr ⟨hvx, hvt⟩)

/-- **THE HONEST DICHOTOMY.**  At the drain endpoint either one of the twins is
blocked — which is a fork, in one orientation or the other — or both twins are
vanilla-raisable.  The first arm deliberately allows **either** block: the
naive template's `¬ CanRaise z' x.twin` alone is *not* exhaustive, since
draining can expose `x.twin` while leaving `x` covered. -/
theorem spectrum_pair_dichotomy {z : State} (hz : z.WF) {x : Card}
    (hx : CanRaiseS z x) (hxt : CanRaiseS z x.twin) :
    (∃ z', sameOrbitSetoid.r z z' ∧
      (∀ c, CanRaiseS z' c → c = x ∨ c = x.twin) ∧
      (¬ CanRaise z' x.twin ∨ ¬ CanRaise z' x))
    ∨ (∃ z', sameOrbitSetoid.r z z' ∧
      (∀ c, CanRaiseS z' c → c = x ∨ c = x.twin) ∧
      CanRaise z' x ∧ CanRaise z' x.twin) := by
  obtain ⟨z', horb, hsub, htri⟩ := spectrum_pair_trichotomy hz hx hxt
  rcases htri with hw | hw | hboth
  · exact Or.inl ⟨z', horb, hsub, Or.inl hw.2⟩
  · exact Or.inl ⟨z', horb, hsub, Or.inr (by simpa [card_twin_twin] using hw.2)⟩
  · exact Or.inr ⟨z', horb, hsub, hboth⟩

/-- **The twin-blocked arm, through the sibling producer.**  Build `Fork z'`
with `fork_of_collapsed_spectrum`, then lift along the class relation. -/
theorem spectrum_pair_fork_of_blocked {z z' : State} {x : Card}
    (horb : sameOrbitSetoid.r z z')
    (hx : CanRaiseS z' x) (hxt : CanRaiseS z' x.twin)
    (hsub : ∀ c, CanRaiseS z' c → c = x ∨ c = x.twin)
    (hblk : ¬ CanRaise z' x.twin) : Fork z := by
  have hfork' : Fork z' := fork_of_collapsed_spectrum hx hxt hsub hblk
  obtain ⟨F, y, hF, hwit⟩ := hfork'
  exact ⟨F, y, sameOrbitSetoid.iseqv.trans horb hF, hwit⟩

/-- **The flipped arm, through the sibling producer.**  With `x` blocked, the
pair is renamed to `{x.twin, x}` and `fork_of_collapsed_spectrum` applies with
witness `x.twin`. -/
theorem spectrum_pair_fork_of_flipped_blocked {z z' : State} {x : Card}
    (horb : sameOrbitSetoid.r z z')
    (hx : CanRaiseS z' x) (hxt : CanRaiseS z' x.twin)
    (hsub : ∀ c, CanRaiseS z' c → c = x ∨ c = x.twin)
    (hblk : ¬ CanRaise z' x) : Fork z := by
  have hsub' : ∀ c, CanRaiseS z' c → c = x.twin ∨ c = x.twin.twin := by
    intro c hc
    rcases hsub c hc with h | h
    · exact Or.inr (by rw [h, card_twin_twin])
    · exact Or.inl h
  have hfork' : Fork z' :=
    fork_of_collapsed_spectrum hxt (by simpa [card_twin_twin] using hx) hsub'
      (by simpa [card_twin_twin] using hblk)
  obtain ⟨F, y, hF, hwit⟩ := hfork'
  exact ⟨F, y, sameOrbitSetoid.iseqv.trans horb hF, hwit⟩

/-- **FORK OR BOTH VANILLA.**  Packaging the blocked arms as `Fork z` through
the sibling producer `fork_of_collapsed_spectrum`, this is the two-arm form
with no residue: either the class has a fork, or a class-mate has both twins
vanilla-raisable with the spectrum collapsed onto them. -/
theorem spectrum_pair_fork_or_both {z : State} (hz : z.WF) {x : Card}
    (hx : CanRaiseS z x) (hxt : CanRaiseS z x.twin) :
    Fork z ∨
      ∃ z', sameOrbitSetoid.r z z' ∧
        (∀ c, CanRaiseS z' c → c = x ∨ c = x.twin) ∧
        CanRaise z' x ∧ CanRaise z' x.twin := by
  obtain ⟨z', horb, hsub, htri⟩ := spectrum_pair_trichotomy hz hx hxt
  rcases htri with hw | hw | hboth
  · -- `ForkWitness z' x`: read the pair liveness off the witness itself
    have hx' : CanRaiseS z' x := (hw.1 x).1 (Or.inl rfl)
    have hxt' : CanRaiseS z' x.twin := (hw.1 x.twin).1 (Or.inr rfl)
    exact Or.inl (spectrum_pair_fork_of_blocked horb hx' hxt' hsub hw.2)
  · -- `ForkWitness z' x.twin`: the flipped arm
    have hxt' : CanRaiseS z' x.twin := (hw.1 x.twin).1 (Or.inl rfl)
    have hx' : CanRaiseS z' x :=
      (hw.1 x).1 (Or.inr (by rw [card_twin_twin]))
    exact Or.inl (spectrum_pair_fork_of_flipped_blocked horb hx' hxt' hsub
      (by simpa [card_twin_twin] using hw.2))
  · exact Or.inr ⟨z', horb, hsub, hboth⟩

/-- **THE BOTH-VANILLA ARM IS THE SQUARE.**  In the second arm of
`spectrum_pair_fork_or_both`, `twin_raise_square_both` fires at the endpoint:
raising the twins in either order is legal and the two two-letter plays share
their landing. -/
theorem spectrum_pair_both_square {z z' : State} {x : Card}
    (hz' : z'.WF) (hx : CanRaise z' x) (hxt : CanRaise z' x.twin) :
    ∃ zt zc z2 : State,
      State.step z' (Move.tabToFound x.twin) = some zt ∧
      State.step zt (Move.tabToFound x) = some z2 ∧
      State.step z' (Move.tabToFound x) = some zc ∧
      State.step zc (Move.tabToFound x.twin) = some z2 :=
  twin_raise_square_both hz' hx hxt

/-- The both-vanilla arm with the square attached, in one statement. -/
theorem spectrum_pair_fork_or_both_square {z : State} (hz : z.WF) {x : Card}
    (hx : CanRaiseS z x) (hxt : CanRaiseS z x.twin) :
    Fork z ∨
      ∃ z', sameOrbitSetoid.r z z' ∧
        (∀ c, CanRaiseS z' c → c = x ∨ c = x.twin) ∧
        CanRaise z' x ∧ CanRaise z' x.twin ∧
        ∃ zt zc z2 : State,
          State.step z' (Move.tabToFound x.twin) = some zt ∧
          State.step zt (Move.tabToFound x) = some z2 ∧
          State.step z' (Move.tabToFound x) = some zc ∧
          State.step zc (Move.tabToFound x.twin) = some z2 := by
  rcases spectrum_pair_fork_or_both hz hx hxt with hfork | ⟨z', horb, hsub, hvx, hvt⟩
  · exact Or.inl hfork
  · refine Or.inr ⟨z', horb, hsub, hvx, hvt, ?_⟩
    -- `sameOrbitSetoid.r z z'` is `RevEqW z' z`, whose second component is a
    -- witness shuffle from `z` to `z'`; well-formedness transports along it.
    obtain ⟨σ, hσ, τ, hτ⟩ := horb
    have hz' : z'.WF := walk_wf hz hτ
    exact twin_raise_square_both hz' hvx hvt

end SpectrumCollapse

#print axioms SpectrumCollapse.drain_pair_stays_live
#print axioms SpectrumCollapse.rungSum_raiseStepS
#print axioms SpectrumCollapse.drain_aux
#print axioms SpectrumCollapse.spectrum_pair_by_draining
#print axioms SpectrumCollapse.spectrum_pair_by_draining_live
#print axioms SpectrumCollapse.spectrum_iff_of_subset
#print axioms SpectrumCollapse.forkWitness_twin_of_blocked_x
#print axioms SpectrumCollapse.spectrum_pair_trichotomy
#print axioms SpectrumCollapse.spectrum_pair_dichotomy
#print axioms SpectrumCollapse.spectrum_pair_fork_of_blocked
#print axioms SpectrumCollapse.spectrum_pair_fork_of_flipped_blocked
#print axioms SpectrumCollapse.spectrum_pair_fork_or_both
#print axioms SpectrumCollapse.spectrum_pair_both_square
#print axioms SpectrumCollapse.spectrum_pair_fork_or_both_square
