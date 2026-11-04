import Orig2.Fork.Split.ForkDrainClose
import Orig2.Fork.Class.ForkRaiseReorderProof
import Orig2.Fork.Split.FirstPassage
import Orig2.Fork.Split.ForkSplit
import Orig2.Fork.Commute.Drain_transport_rows

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Temp/SatDiffer_config — the `SatDifferForkWF` configuration card

Attack on the campaign residue `SatDifferForkWF`
(`Orig2/Substrate/Vocab.lean:641`).  New file only; nothing under `Orig2/`
and no existing `Temp/` file is modified.

## What is proved here

* **§1 STEP 1 — `licence_lost_only_by_twin`.**  A `RaiseStepS` letter
  whose raised card `d` has the same rank as `c`, with `d ≠ c` and
  `d ≠ c.twin`, preserves `CanRaiseS · c`.  Proof: the licence splits as
  `nextUp ∧ freeCardS` (`canRaiseS_split`); `d`'s suit differs from
  `c.suit` (same rank + different card), so `nextUp` is fixed, and
  `freeCardS c` reads only `c`'s own pile and `pileOfTop c.twin` — both
  untouched by a same-rank raise (a same-rank card is never *above* `c`
  in a legal run, and `c.twin` is never the raised card).  The cargo
  prefix is absorbed with `canRaiseS_orbit_rung` (a `CargoPath` is an
  equal-rung orbit move).

* **§2 STEP 2 — `pulled_card_refounded`.**  In a witness play a
  `foundToTab c b` letter drops the `c.suit`-rung from
  `c.rank.toIdx + 1` to `c.rank.toIdx`.  If the play's end reads the
  suit's rung at least its value at the start, then `tabToFound c`
  occurs in the play.  Two crossings of the level `c.rank.toIdx`: if
  the start is already above it, the first later rise
  (`SatDifferCensus.firstRise_of_rung_lt`) is the raise of `c`; if the
  start is at most `c.rank.toIdx`, the pull's pre-state reads
  `c.rank.toIdx + 1`, so the first rise already occurs in the prefix.
  In both cases the crossing letter is a `tabToFound c'` with
  `c'.suit = c.suit` and `c'.rank.toIdx = c.rank.toIdx`, hence `c' = c`.

* **§3 THE CONFIGURATION.**  The drain half is already unconditional in
  `Orig2` (`DrainClose.fork_exists_of_asymmetry`): a `WF` state carrying
  a raisable card `x` whose twin is S-live and vanilla-blocked, with no
  live card below `x`'s rank, has a fork in its class.  So the whole
  residue is the *existence* of that configuration in the class.  We
  prove the assembly `satDifferForkWF_of_asymmetry` from that existence
  statement (stated inline, no new `Prop` wrapper), and we record the
  precise residual conjunct in the report.  The carry-on conjunct
  `Drain.DrainRaisable` is **not** part of the residual: `DrainClose`
  drains blocked live cards by the two-letter slide-then-raise, so the
  weaker `drain_phase_fork` provider is not needed.

House compliance: zero `sorry`, zero `Classical.choice`, zero
`noncomputable`, zero `native_decide`.
-/

namespace SatDifferConfig

open OneColourClosure

/-! ## §1. Step 1 — a same-rank raise never kills the licence

The leaf row: a card of the raised card's rank, other than the card
itself and its twin, cannot sit on the raised pile nor on the twin's
top, so neither `freeCardS` read moves. -/

/-- **A same-rank card other than the top is not in the top's pile.**
(`rank_lt_of_mem_of_lastOf` with the strict inequality collapsed to
equality by the same-rank hypothesis.) -/
theorem not_mem_pileOfTop_of_rank_eq {z : State} (hz : z.WF) {e d : Card} {a : Anchor}
    (hpa : z.pileOfTop e = some a) (hde : d ≠ e) (hr : d.rank = e.rank) :
    d ∉ (z.piles a).faceUp := by
  intro hmem
  have hlast : lastOf (z.piles a).faceUp = some e := (pileOfTop_top hpa).2
  have hlt := OneColourClosure.rank_lt_of_mem_of_lastOf (hz.2.1 a) hlast hmem hde
  rw [hr] at hlt
  exact absurd hlt (by omega)

/-- **`freeCardS` is preserved (forward) by a same-rank raise.**
`freeCardS` reads `c`'s holding pile and `pileOfTop c.twin`; the raised
pile is neither, and the twin's top cannot vanish.  (Equality can fail
in one direction only: a raise may *reveal* `c.twin` from the hidden
deck of the raised pile, which turns `none` into `some` — harmless for
the forward read used by the licence.) -/
theorem freeCardS_fwd_of_rank_eq {z z' : State} {e d : Card}
    (hz : z.WF) (hstep : State.step z (Move.tabToFound e) = some z')
    (hde : d ≠ e) (hdt : d.twin ≠ e) (hr : d.rank = e.rank) :
    freeCardS z d = true → freeCardS z' d = true := by
  obtain ⟨a0, hpa0, hpiles⟩ := OneColourClosure.piles_tabToFound hstep
  have hz' : z'.WF := step_wf hz hstep
  have hd0 : d ∉ (z.piles a0).faceUp := not_mem_pileOfTop_of_rank_eq hz hpa0 hde hr
  have hdt0 : d.twin ∉ (z.piles a0).faceUp := by
    refine not_mem_pileOfTop_of_rank_eq hz hpa0 hdt ?_
    show d.twin.rank = e.rank
    rw [Card.twin_rank]
    exact hr
  intro hf
  unfold freeCardS at hf ⊢
  cases hhold : z.pileHolding d with
  | none => rw [hhold] at hf; exact absurd hf (by simp)
  | some a =>
      simp only [hhold] at hf
      have hmem : d ∈ (z.piles a).faceUp := pileHolding_mem hhold
      have ha0 : a ≠ a0 := by
        intro h
        subst h
        exact hd0 hmem
      have hp_a : z'.piles a = z.piles a := by
        rw [hpiles a, ite_eq_right ha0]
      have hhold' : z'.pileHolding d = some a :=
        (pileHolding_eq_some_iff hz').2 (by rw [hp_a]; exact hmem)
      simp only [hhold']
      have hfrom : fromCard d (z'.piles a).faceUp = fromCard d (z.piles a).faceUp := by
        rw [hp_a]
      have hbelow : below d (z'.piles a).faceUp = below d (z.piles a).faceUp := by
        rw [hp_a]
      have hhidden : (z'.piles a).hidden = (z.piles a).hidden := by
        rw [hp_a]
      rw [hfrom, hbelow, hhidden]
      cases hfc : fromCard d (z.piles a).faceUp with
      | nil => rw [hfc] at hf; exact absurd hf (by simp)
      | cons c0 run =>
          simp only [hfc] at hf ⊢
          rw [Bool.and_eq_true] at hf ⊢
          obtain ⟨hA, hrot⟩ := hf
          refine ⟨hA, ?_⟩
          rw [Bool.or_eq_true] at hrot ⊢
          rcases hrot with hre | his
          · exact Or.inl hre
          · refine Or.inr ?_
            have hne : z.pileOfTop d.twin ≠ none := by
              intro hn
              rw [hn] at his
              exact absurd his (by simp)
            obtain ⟨q, hq⟩ := option_some_of_ne_none hne
            have htop : (z.piles q).top = some d.twin := (pileOfTop_eq_some_iff hz).mp hq
            have hq0 : q ≠ a0 := by
              intro h
              subst h
              exact hdt0 (Pile.mem_of_top htop)
            have htop' : (z'.piles q).top = some d.twin := by
              rw [hpiles q, ite_eq_right hq0]
              exact htop
            have hq' : z'.pileOfTop d.twin = some q :=
              (pileOfTop_eq_some_iff hz').mpr htop'
            show (z'.pileOfTop d.twin).isSome = true
            rw [hq']
            rfl

/-- **`CanRaiseS` is preserved (forward) by a same-rank raise.**  The
foundation gate `nextUp` is untouched because a distinct card of equal
rank has a different suit; the tableau readiness is the previous row. -/
theorem canRaiseS_tabToFound_fwd_of_rank_eq {z z' : State} {e d : Card}
    (hz : z.WF) (hstep : State.step z (Move.tabToFound e) = some z')
    (hde : d ≠ e) (hdt : d.twin ≠ e) (hr : d.rank = e.rank) :
    CanRaiseS z d → CanRaiseS z' d := by
  intro hS
  have hz' : z'.WF := step_wf hz hstep
  rw [canRaiseS_split hz] at hS
  rw [canRaiseS_split hz']
  obtain ⟨hnext, hfree⟩ := hS
  have hsuit : d.suit ≠ e.suit := by
    intro hse
    have hdeq : d = e := by
      cases d with
      | mk ds dr =>
          cases e with
          | mk es er => simp_all
    exact hde hdeq
  have hnext' : z'.nextUp d = true := by
    unfold State.nextUp State.foundHeight at hnext ⊢
    rw [OneColourClosure.found_tabToFound hstep d.suit, ite_eq_right hsuit]
    exact hnext
  exact ⟨hnext', freeCardS_fwd_of_rank_eq hz hstep hde hdt hr hfree⟩

/-- **STEP 1 — `licence_lost_only_by_twin`.**  A `RaiseStepS u u' d`
letter (`CargoPath` then a `tabToFound d`) with `d.rank = c.rank`,
`d ≠ c`, `d ≠ c.twin` preserves `CanRaiseS · c`.

The cargo prefix is an equal-rung orbit move, so the licence transfers
across it (`canRaiseS_orbit_rung`); the raise is the leaf row above. -/
theorem licence_lost_only_by_twin {u u' : State} {d c : Card}
    (hu : u.WF) (hstep : RaiseStepS u u' d)
    (hr : d.rank = c.rank) (hdc : d ≠ c) (hdt : d ≠ c.twin) :
    CanRaiseS u c → CanRaiseS u' c := by
  intro hS
  obtain ⟨z0, hpath, hfire⟩ := hstep
  have hz0 : z0.WF := cargoPath_wf hu hpath
  have horb : sameOrbitSetoid.r u z0 := OneColourClosure.sameOrbit_of_cargoPath hpath
  have hrung : ∀ σ, rungAt u σ = rungAt z0 σ := rungAt_cargoPath hpath
  have h1 : CanRaiseS u c ↔ CanRaiseS z0 c := canRaiseS_orbit_rung hu horb hrung
  exact canRaiseS_tabToFound_fwd_of_rank_eq hz0 hfire hdc.symm hdt.symm hr.symm (h1.mp hS)

/-- **The contrapositive: the licence can be lost only at `c` or `c.twin`.**
If a same-rank raise step destroys `c`'s S-licence, the raised card is
`c` or `c.twin` itself.  This is the exact "only by twin" reading used by
the configuration step: an intervening same-rank raise of any *other*
card is licence-inert. -/
theorem licence_lost_only_by_twin' {u u' : State} {d c : Card}
    (hu : u.WF) (hstep : RaiseStepS u u' d) (hr : d.rank = c.rank)
    (hS : CanRaiseS u c) (hlost : ¬ CanRaiseS u' c) :
    d = c ∨ d = c.twin := by
  by_cases hdc : d = c
  · exact Or.inl hdc
  · by_cases hdt : d = c.twin
    · exact Or.inr hdt
    · exact absurd (licence_lost_only_by_twin hu hstep hr hdc hdt hS) hlost

/-! ## §2. Step 2 — a pulled card is re-founded when the rung returns -/

/-- Split a list at a member occurrence. -/
theorem exists_split_at_mem {α : Type} :
    ∀ (l : List α) (x : α), x ∈ l → ∃ a b, l = a ++ x :: b
  | [], x, h => by simp at h
  | y :: t, x, h => by
      rcases List.mem_cons.mp h with hyx | h1
      · subst hyx
        exact ⟨[], t, rfl⟩
      · obtain ⟨a, b, hab⟩ := exists_split_at_mem t x h1
        exact ⟨y :: a, b, by rw [hab]; rfl⟩

/-- **A first-rise crossing letter is the named raise.**  The crossing
letter of `FirstRise u v ρ σ k` is a `tabToFound` of the unique
`σ`-card of rank index `k`. -/
theorem FirstRise.mem_raise {u v : State} {ρ : List Move} {σ : Suit} {k : Nat} {c : Card}
    (hcs : c.suit = σ) (hcr : c.rank.toIdx = k)
    (fr : SatDifferCensus.FirstRise u v ρ σ k) :
    Move.tabToFound c ∈ ρ := by
  obtain ⟨pre, m, rest, mid, post, c', hplay, -, -, -, -, -, -, hm, hcs', hcr', -⟩ := fr
  have hcc : c' = c := by
    have hsuit : c'.suit = c.suit := by rw [hcs', hcs]
    have hrank : c'.rank.toIdx = c.rank.toIdx := by rw [hcr', hcr]
    have hrank' : c'.rank = c.rank := Rank.toIdx_inj hrank
    cases c' with
    | mk s r =>
        cases c with
        | mk s' r' => simp_all
  have hm' : m = Move.tabToFound c := by
    rw [hm, hcc]
  rw [hplay, hm']
  exact List.mem_append_right _ (List.mem_cons_self ..)

/-- **STEP 2 — `pulled_card_refounded`.**  If a witness play contains
the pull `foundToTab c b` and the `c.suit`-rung at the end of the play
is at least its value at the start, then `tabToFound c` occurs somewhere
in the play.

Two cases, both crossings of the level `c.rank.toIdx`:

* if the start already reads `> c.rank.toIdx`, the pull drops the rung
  from `c.rank.toIdx + 1` to `c.rank.toIdx`, and the end reading
  `≥` the start forces a later first rise through `c.rank.toIdx` — the
  raise of `c`;
* otherwise the start reads `≤ c.rank.toIdx` while the pull's
  pre-state reads `c.rank.toIdx + 1`, so the first rise already happens
  in the prefix before the pull — again the raise of `c`. -/
theorem pulled_card_refounded {st W : State} {play : List Move} {c : Card} {b : Base}
    (hwf : st.WF) (hplay : ShufflePlayW st play W)
    (hmem : Move.foundToTab c b ∈ play)
    (hrung : rungAt st c.suit ≤ rungAt W c.suit) :
    Move.tabToFound c ∈ play := by
  obtain ⟨a, b', hsplit⟩ := exists_split_at_mem play (Move.foundToTab c b) hmem
  subst hsplit
  obtain ⟨F, hpreF, hpostW⟩ :=
    ValleyElim.ShufflePlayW_split hplay a (Move.foundToTab c b :: b') rfl
  cases hpostW with
  | cons hrev hstep hrest =>
      rename_i A
      have hF : F.WF := SatDifferCensus.ShufflePlayW.wf_end hpreF hwf
      obtain ⟨c0, htop0, hc0, -, -⟩ := step_foundToTab_inv hstep
      have htop : F.foundTop c.suit = some c := by
        have h := htop0
        rw [hc0] at h
        exact h
      have hrF : c.rank.toIdx + 1 = rungAt F c.suit :=
        SatDifferCensus.foundTop_rank_succ hF htop
      have hrA : rungAt A c.suit = c.rank.toIdx := by
        have h1 := rungAt_foundToTab hstep c.suit
        rw [ite_eq_left rfl] at h1
        omega
      by_cases hcase : rungAt st c.suit ≤ c.rank.toIdx
      · -- the rise happens in the prefix, before the pull
        have hgt : c.rank.toIdx < rungAt F c.suit := by omega
        have hfr := SatDifferCensus.firstRise_exists hpreF hcase hgt
        exact List.mem_append_left _
          (FirstRise.mem_raise (c := c) (σ := c.suit) (k := c.rank.toIdx) rfl rfl hfr)
      · -- the start is already above: the rise happens after the pull
        have hlt : rungAt A c.suit < rungAt W c.suit := by omega
        have hfr := SatDifferCensus.firstRise_of_rung_lt hrest hlt
        rw [hrA] at hfr
        have hmem' : Move.tabToFound c ∈ Move.foundToTab c b :: b' := by
          have := FirstRise.mem_raise (c := c) (σ := c.suit) (k := c.rank.toIdx) rfl rfl hfr
          exact List.mem_cons_of_mem _ this
        exact List.mem_append_right a hmem'

/-- **A low-rank raise cannot kill a higher card's vanilla licence.**  The
mirror of `Drain.canRaise_of_raise_high_fwd` for `c.rank < d.rank`: the
raised pile is not `d`'s pile (two tops of one pile would be one card),
and the foundation of `d`'s suit is untouched.  This is the row the rank
floor would need to be *removed* from the configuration: a live card
below the pair can be raised without disturbing the pair's raisable
member. -/
theorem canRaise_of_raise_low_fwd {st w : State} {c d : Card}
    (hwf : st.WF) (hstep : State.step st (Move.tabToFound c) = some w)
    (hcd : c ≠ d) (hrank : c.rank.toIdx < d.rank.toIdx)
    (h : CanRaise st d) : CanRaise w d := by
  obtain ⟨hnext_d, a1, hpa1, hclause⟩ := h
  obtain ⟨hnext_c, a0, hpa0, hs⟩ := step_tabToFound_inv hstep
  have hsuit : d.suit ≠ c.suit :=
    Drain.suit_ne_of_nextUp hnext_d hnext_c (Ne.symm hcd)
  have htop_d : (st.piles a1).top = some d := (pileOfTop_eq_some_iff hwf).mp hpa1
  have htop_c : (st.piles a0).top = some c := (pileOfTop_eq_some_iff hwf).mp hpa0
  have ha10 : a1 ≠ a0 := by
    intro hcon
    rw [hcon] at htop_d
    exact hcd (Option.some.inj (htop_d.symm.trans htop_c)).symm
  have hfound : w.found d.suit = st.found d.suit := by
    rw [hs]
    exact setFound_found_ne hsuit
  have hnext_w : w.nextUp d = true := by
    have h1 : d.rank.toIdx = (st.found d.suit).length := by
      simpa [State.nextUp, State.foundHeight] using of_decide_eq_true hnext_d
    unfold State.nextUp State.foundHeight
    rw [hfound]
    exact decide_eq_true h1
  have hpiles : w.piles a1 = st.piles a1 := by
    rw [hs]
    simp only []
    rw [ite_eq_right ha10]
  have hwfw : w.WF := step_wf hwf hstep
  have htop_w : (w.piles a1).top = some d := by
    rw [hpiles]
    exact htop_d
  have hpile_w : w.pileOfTop d = some a1 := (pileOfTop_eq_some_iff hwfw).mpr htop_w
  refine ⟨hnext_w, a1, hpile_w, ?_⟩
  rcases hclause with hchop | ⟨hhid, hking⟩
  · left
    rw [hpiles]
    exact hchop
  · right
    refine ⟨?_, hking⟩
    rw [hpiles]
    exact hhid

/-! ## §2b. The pull's landing is a live configuration

A `WF` pull re-founds the pulled card in the tableau with the suit's
rung exactly at its rank index, so it is `nextUp` and vanilla-raisable
at the landing.  This is the "pull creates the live card" half of the
plan's configuration step, with the `nextUp` premise discharged from
`WF`. -/

/-- **`nextUp` after a pull.**  The pulled card is next-up at the
landing: the rung has dropped from `c.rank.toIdx + 1` to
`c.rank.toIdx`. -/
theorem nextUp_after_pull {F A : State} {c : Card} {b : Base}
    (hF : F.WF) (hstep : State.step F (Move.foundToTab c b) = some A) :
    A.nextUp c = true := by
  obtain ⟨c0, htop0, hc0, -, -⟩ := step_foundToTab_inv hstep
  have htop : F.foundTop c.suit = some c := by
    have h := htop0
    rw [hc0] at h
    exact h
  have hrF : c.rank.toIdx + 1 = rungAt F c.suit :=
    SatDifferCensus.foundTop_rank_succ hF htop
  have hrA : rungAt A c.suit = c.rank.toIdx := by
    have h1 := rungAt_foundToTab hstep c.suit
    rw [ite_eq_left rfl] at h1
    omega
  unfold State.nextUp State.foundHeight
  apply decide_eq_true
  show c.rank.toIdx = (A.found c.suit).length
  exact hrA.symm

/-- **The pull's card is vanilla-raisable at the landing.** -/
theorem canRaise_after_pull {F A : State} {c : Card} {b : Base}
    (hF : F.WF) (hstep : State.step F (Move.foundToTab c b) = some A) :
    CanRaise A c :=
  SatDifferCensus.canRaise_post_of_pull hF hstep (nextUp_after_pull hF hstep)

/-- **The pull's card is S-live at the landing.** -/
theorem canRaiseS_after_pull {F A : State} {c : Card} {b : Base}
    (hF : F.WF) (hstep : State.step F (Move.foundToTab c b) = some A) :
    CanRaiseS A c :=
  CanRaiseS.now c (canRaise_after_pull hF hstep)

/-! ## §3. The configuration: the drain half is unconditional

`DrainClose.fork_exists_of_asymmetry` consumes exactly the twin
asymmetry plus the rank floor.  The residue is therefore the existence
of a class-mate carrying that data — the plan's "blocking state".  We
isolate the assembly with the existence hypothesis inline (no new
`Prop` wrapper). -/

/-- **THE CONFIGURATION ASSEMBLY.**  If every saturated differing-rung
class pair has a class-mate `w` carrying a raisable card `x` whose twin
is S-live but vanilla-blocked, with no live card below `x`'s rank, then
`SatDifferForkWF` holds.

The `WF` of `w` is transported from `u` along the class relation; the
drain half is `DrainClose.fork_exists_of_asymmetry` (unconditional — no
`DrainRaisable` and no `RaiseTransport` provider is needed). -/
theorem satDifferForkWF_of_asymmetry
    (h : ∀ u v : State, u.WF → SSaturated u → SSaturated v →
      sameOrbitSetoid.r u v →
      (∃ σ : Suit, rungAt u σ ≠ rungAt v σ) →
      ∃ (w : State) (x : Card), sameOrbitSetoid.r u w ∧
        CanRaise w x ∧ CanRaiseS w x.twin ∧ ¬ CanRaise w x.twin ∧
        (∀ c, CanRaiseS w c → x.rank.toIdx ≤ c.rank.toIdx)) :
    SatDifferForkWF := by
  intro u v huwf hsu hsv hcls hdiff
  obtain ⟨w, x, huw, hcan, hlive, hblock, hfloor⟩ := h u v huwf hsu hsv hcls hdiff
  have hwwf : w.WF := by
    obtain ⟨σ, hσ, τ, hτ⟩ := huw
    exact SatDifferCensus.ShufflePlayW.wf_end hτ huwf
  obtain ⟨F, hrel, hfork⟩ :=
    DrainClose.fork_exists_of_asymmetry hwwf hcan hlive hblock hfloor
  obtain ⟨y, hy⟩ := forkState_iff.mp hfork
  exact ⟨F, y, sameOrbitSetoid.iseqv.trans huw hrel, hy⟩

/-- **The same assembly through the weaker `Drain.DrainRaisable` route.**
This is the plan's literal four-conjunct configuration: `DrainInvariant`
(raisable `x`, S-live blocked twin, rank floor) plus the carry-on
`DrainRaisable`.  The previous theorem shows the carry-on is *not*
needed — `DrainClose` drains blocked live cards as well.  Both routes
are recorded so the report can point at the exact difference. -/
theorem satDifferForkWF_of_drainConfig
    (h : ∀ u v : State, u.WF → SSaturated u → SSaturated v →
      sameOrbitSetoid.r u v →
      (∃ σ : Suit, rungAt u σ ≠ rungAt v σ) →
      ∃ (w : State) (x : Card), sameOrbitSetoid.r u w ∧ w.WF ∧
        Drain.DrainInvariant w x ∧ Drain.DrainRaisable w x) :
    SatDifferForkWF := by
  intro u v huwf hsu hsv hcls hdiff
  obtain ⟨w, x, huw, hwwf, hinv, hra⟩ := h u v huwf hsu hsv hcls hdiff
  obtain ⟨F, hrel, hfork⟩ := OneColourClosure.drain_phase_fork hwwf hinv hra
  obtain ⟨y, hy⟩ := forkState_iff.mp hfork
  exact ⟨F, y, sameOrbitSetoid.iseqv.trans huw hrel, hy⟩

end SatDifferConfig

#print axioms SatDifferConfig.not_mem_pileOfTop_of_rank_eq
#print axioms SatDifferConfig.freeCardS_fwd_of_rank_eq
#print axioms SatDifferConfig.canRaiseS_tabToFound_fwd_of_rank_eq
#print axioms SatDifferConfig.licence_lost_only_by_twin
#print axioms SatDifferConfig.licence_lost_only_by_twin'
#print axioms SatDifferConfig.exists_split_at_mem
#print axioms SatDifferConfig.FirstRise.mem_raise
#print axioms SatDifferConfig.pulled_card_refounded
#print axioms SatDifferConfig.canRaise_of_raise_low_fwd
#print axioms SatDifferConfig.nextUp_after_pull
#print axioms SatDifferConfig.canRaise_after_pull
#print axioms SatDifferConfig.canRaiseS_after_pull
#print axioms SatDifferConfig.satDifferForkWF_of_asymmetry
#print axioms SatDifferConfig.satDifferForkWF_of_drainConfig
