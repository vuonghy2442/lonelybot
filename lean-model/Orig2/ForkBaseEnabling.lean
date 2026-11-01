import Orig2.ForkPullSwaps

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# BaseEn — the BASE-ENABLING case of `MtnPr.SameCardRelocation`

READ-ONLY scratch card (`Temp/`).  No source edits, no commit.  No `sorry`,
no `Classical.choice`, no `native_decide`.

The pull-bubble machine of `Orig2/ForkPullSwaps.lean` reduces
`MtnPr.SameCardRelocation` to *pull readiness at the raise's image*
(`PullKit.PullReadyAtImage`), which is kernel-false.  This card works the
genuine gap:

* **§1**  the *ready-at-image* half: if the pull is legal at the raise's
  image, the residual shortens (`shortens_of_readyAtImage`) — the
  `sameCardRelocation_ready` route with readiness *supplied*, not assumed
  globally.
* **§2**  the `inl` half of the base-enabling gap: if the raise **empties**
  its own pile `a` and the pull lands there as a king
  (`b = Sum.inl a`, `A.piles a = ⟨[], [c]⟩`, `c` a king), then the base *is*
  available at the raise's image (`raise_empties_inl_base`), so §1 closes it:
  `baseEnabling_inl_shortens`.
* **§3**  the decomposition: `SameCardRelocation` follows from §1 + the
  remaining `BaseEnabling` residual (`sameCardRelocation_of_baseEnabling`).
  This names exactly what is left: the pull legal at the *final* window state
  but **not** at the raise's image.
* **§4**  the `inr` analysis: `canSitOn c z = false` kills the base forever;
  enabling forces `z` to be *exposed* as a pile top, and once exposed the base
  survives every read-safe, seat-inert letter.  The residual is named
  `InrExposeResidual`.
* **§5**  the local net-one identity behind the gap witness
  (`raise_raise_pull_eq_raise_slide`), the local shortening
  (`raise_raise_pull_shortens_local`), and the adjacent interior-enabling
  full-play case (`baseEnabling_inl_interior_adjacent_shortens`), which
  generalises `PullKit.gap_instance_shortens`.
* **§6**  composition: `SameCardRelocation` ⇒ no same-card raise-before-pull
  in a minimal play (the same-card half of M1, gated); the cross-suit half is
  the kernel-refuted corner and is *not* claimed.
-/

namespace BaseEn

open MountainKit
open CommuteStep

/-- A `setPile` read at an arbitrary anchor, as an `if`. -/
theorem setPile_piles_apply (st : State) (a a' : Anchor) (p : Pile) :
    (st.setPile a p).piles a' = if a' = a then p else st.piles a' := rfl

/-- The `inl` write of `putCard`, read at an arbitrary anchor. -/
theorem putCard_inl_piles_apply (st : State) (c : Card) (a a' : Anchor) :
    (st.putCard c (Sum.inl a)).piles a' =
      if a' = a then (⟨[], [c]⟩ : Pile) else st.piles a' := by
  rw [putCard_piles_inl]

/-- The `inl` write of `putRun`, read at an arbitrary anchor. -/
theorem putRun_inl_piles_apply (st : State) (run : List Card) (a a' : Anchor) :
    (st.putRun run (Sum.inl a)).piles a' =
      if a' = a then (⟨[], run⟩ : Pile) else st.piles a' := by
  rw [putRun_eq_inl]
  rfl

/-! ## §1. The ready-at-image half -/

/-- A raise of `c` puts `c` on top of its own foundation. -/
theorem foundTop_raiseSt_self (A : State) (c : Card) (a : Anchor) :
    (raiseSt A c a).foundTop c.suit = some c := by
  unfold State.foundTop
  rw [raiseSt_found_apply, ite_eq_left rfl, lastOf_snoc]

/-- **THE READY-AT-IMAGE HALF.**  If the pull `pull c b` is legal at `B`, the
image of the raise in the residual play
`pre ++ raise c :: γ ++ pull c b :: post`, then the play strictly shortens.
(`γ` is read-safe for `c` and seat-inert on `b`.)  This is
`PullKit.sameCardRelocation_ready` with the readiness hypothesis discharged at
the actual image. -/
theorem shortens_of_readyAtImage
    {u v : State} {ρ pre γ post : List Move} {c : Card} {b : Base} {A B : State}
    (huwf : u.WF) (hplay : ShufflePlayW u ρ v)
    (hρ : ρ = pre ++ Move.tabToFound c :: γ ++ Move.foundToTab c b :: post)
    (hpre : ShufflePlayW u pre A)
    (hstep : State.step A (Move.tabToFound c) = some B)
    (hread : ∀ q ∈ γ, SlideFwd.ReadSafe c q)
    (hseat : ∀ q ∈ γ, MtnPr.SeatInert b q)
    (hcp : B.canPlace c b = true) :
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length := by
  refine PullKit.sameCardRelocation_ready u v ρ pre γ post c b
    huwf hplay hρ hread hseat ?_
  intro A' B' hpre' hstep'
  -- determinism: `pre` lands at `A` and at `A'`
  have hrunA : u.run pre = some A := Walk_run _ hpre
  have hrunA' : u.run pre = some A' := Walk_run _ hpre'
  have hAA : A' = A := Option.some.inj (hrunA'.symm.trans hrunA)
  subst A'
  have hBB : B' = B := Option.some.inj (hstep'.symm.trans hstep)
  subst B'
  obtain ⟨-, a, hpa, hs⟩ := step_tabToFound_inv hstep
  refine ⟨?_, hcp⟩
  rw [hs]
  exact foundTop_raiseSt_self A c a

/-! ## §2. The `inl` half: the raise empties its own pile -/

/-- `canPlace c (inl p)` is true as soon as `p` is empty and `c` is a king. -/
theorem canPlace_inl_of_empty_king {st : State} {c : Card} {p : Anchor}
    (hemp : (st.piles p).isEmpty = true) (hk : c.rank = Rank.king) :
    st.canPlace c (Sum.inl p) = true := by
  rw [canPlace_inl_unfold, hemp, decide_eq_true hk]
  rfl

/-- A bare pile `[c]` (nothing hidden) is emptied by the raise of `c`. -/
theorem raiseSt_piles_self_bare {A : State} {c : Card} {a : Anchor}
    (hface : (A.piles a).faceUp = [c]) (hhid : (A.piles a).hidden = []) :
    (raiseSt A c a).piles a = ⟨[], []⟩ := by
  rw [raiseSt_piles_apply, ite_eq_left rfl, hface]
  have hchop : chop ([c] : List Card) = [] := by simp [chop]
  rw [hchop]
  exact Pile.afterRunRemoved_bare hhid

/-- **THE RAISE-EMPTIES-`inl` ENABLEMENT.**  If pile `a` is the bare `[c]` with
nothing hidden and `c` is a king, then the pull `pull c (inl a)` is legal at
the raise's image. -/
theorem raise_empties_inl_base {A : State} {c : Card} {a : Anchor}
    (hface : (A.piles a).faceUp = [c]) (hhid : (A.piles a).hidden = [])
    (hking : c.rank = Rank.king) :
    (raiseSt A c a).canPlace c (Sum.inl a) = true := by
  refine canPlace_inl_of_empty_king ?_ hking
  rw [raiseSt_piles_self_bare hface hhid]
  rfl

/-- **THE `inl` HALF IS CLOSED.**  In the residual play
`pre ++ raise c :: γ ++ pull c b :: post` with `b = Sum.inl a`, if the raise of
`c` from `a` empties pile `a` (bare `[c]`, nothing hidden, `c` a king), then
the play strictly shortens.

This covers exactly the sub-case in which the enabling happens *at the raise
itself*: then the pull is ready at the image and §1 applies.  The
interior-enabled sub-cases are §5 (the enabling raise is the first interior
letter) and the residual `BaseEnabling` (§3). -/
theorem baseEnabling_inl_shortens
    {u v : State} {ρ pre γ post : List Move} {c : Card} {a : Anchor} {A B : State}
    (huwf : u.WF) (hplay : ShufflePlayW u ρ v)
    (hρ : ρ = pre ++ Move.tabToFound c :: γ ++ Move.foundToTab c (Sum.inl a) :: post)
    (hpre : ShufflePlayW u pre A)
    (hstep : State.step A (Move.tabToFound c) = some B)
    (hread : ∀ q ∈ γ, SlideFwd.ReadSafe c q)
    (hseat : ∀ q ∈ γ, MtnPr.SeatInert (Sum.inl a) q)
    (hface : (A.piles a).faceUp = [c]) (hhid : (A.piles a).hidden = [])
    (hking : c.rank = Rank.king) :
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length := by
  obtain ⟨hnext, a', hpo, hs⟩ := step_tabToFound_inv hstep
  -- the raise's source is `a`: `c` tops both piles otherwise
  have htopA : (A.piles a).top = some c := by
    rw [Pile.top, hface]
    simpa using lastOf_snoc (front := ([] : List Card)) (c := c)
  have hAwf : A.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  have hpoA : A.pileOfTop c = some a := (pileOfTop_eq_some_iff hAwf).mpr htopA
  have haa : a' = a := Option.some.inj (hpo.symm.trans hpoA)
  subst a'
  have hB : B = raiseSt A c a := by rw [hs]; rfl
  have hcp : B.canPlace c (Sum.inl a) = true := by
    rw [hB]
    exact raise_empties_inl_base hface hhid hking
  exact shortens_of_readyAtImage huwf hplay hρ hpre hstep hread hseat hcp

/-! ## §3. The decomposition: only `BaseEnabling` is left -/

/-- **THE BASE-ENABLING RESIDUAL.**  Every residual play whose pull is **not**
legal at the raise's image (the only case `PullKit.PullReadyAtImage` misses)
shortens.  This is the exact, named hole left by the pull-bubble route. -/
def BaseEnabling : Prop :=
  ∀ (u v : State) (ρ pre γ post : List Move) (c : Card) (b : Base) (A B : State),
    u.WF → ShufflePlayW u ρ v →
    ρ = pre ++ Move.tabToFound c :: γ ++ Move.foundToTab c b :: post →
    ShufflePlayW u pre A →
    State.step A (Move.tabToFound c) = some B →
    (∀ q ∈ γ, SlideFwd.ReadSafe c q) →
    (∀ q ∈ γ, MtnPr.SeatInert b q) →
    B.canPlace c b = false →
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length

/-- **`SameCardRelocation` FROM §1 + THE NAMED RESIDUAL.**  Given the residual
`BaseEnabling`, every same-card relocation shortens: split at the raise, and
either the pull is legal at the image (§1) or it is not (`BaseEnabling`). -/
theorem sameCardRelocation_of_baseEnabling
    (h : BaseEnabling) : MtnPr.SameCardRelocation := by
  intro u v ρ pre γ post c b huwf hplay hρ hread hseat
  have hρa : ρ = pre ++ (Move.tabToFound c :: γ ++ Move.foundToTab c b :: post) := by
    rw [hρ]; simp only [List.append_assoc]
  obtain ⟨A, hpre, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hplay pre
      (Move.tabToFound c :: γ ++ Move.foundToTab c b :: post) hρa
  obtain ⟨B, -, hstep, -⟩ := Bubble.walk_cons_inv hrest
  by_cases hcp : B.canPlace c b = true
  · exact shortens_of_readyAtImage huwf hplay hρ hpre hstep hread hseat hcp
  · have hno : B.canPlace c b = false := by
      cases hcc : B.canPlace c b with
      | false => rfl
      | true => exact absurd hcc hcp
    exact h u v ρ pre γ post c b A B huwf hplay hρ hpre hstep hread hseat hno

/-! ## §4. The `inr` half: monotonicity of the base card

The `inr z` base reads `pileOfTop z` (a *state* datum) and `canSitOn c z`
(a *card* datum).  `canSitOn` is state-independent, so the impossible half of
the `inr` case is settled outright; the possible half is exactly "some interior
letter makes `z` a pile top". -/

/-- The `inr` guard does not depend on *which* pile holds `z`; it is `canSitOn`
once `z` is a pile top, and `false` when it is buried. -/
theorem canPlace_inr_false_of_canSitOn_false {st : State} {c z : Card}
    (h : canSitOn c z = false) : st.canPlace c (Sum.inr z) = false := by
  rw [canPlace_inr_eq]
  cases st.pileOfTop z with
  | none => rfl
  | some k => exact h

/-- **THE `inr` BASE CANNOT BE ENABLED IF THE FIT IS DEAD.**  A dead
`canSitOn c z` makes `canPlace c (inr z)` false at every state: no interior
letter can ever enable such a base. -/
theorem inr_never_enabled_of_dead_fit {A C : State} {c z : Card}
    (h : canSitOn c z = false) :
    A.canPlace c (Sum.inr z) = false ∧ C.canPlace c (Sum.inr z) = false :=
  ⟨canPlace_inr_false_of_canSitOn_false h, canPlace_inr_false_of_canSitOn_false h⟩

/-- **ENABLING THE `inr` BASE FORCES AN EXPOSURE.**  If the `inr z` base is
unavailable at `A` and available at `C`, then the fit is live, `z` is buried
(`pileOfTop z = none`) at `A`, and `z` is a pile top at `C`.  So the enabling
event is exactly a letter that *exposes* `z`. -/
theorem inr_enable_needs_expose {A C : State} {c z : Card}
    (hA : A.canPlace c (Sum.inr z) = false)
    (hC : C.canPlace c (Sum.inr z) = true) :
    canSitOn c z = true ∧ A.pileOfTop z = none ∧ ∃ k, C.pileOfTop z = some k := by
  have hfit : canSitOn c z = true := by
    obtain ⟨k, -, hfit⟩ := canPlace_inr hC
    exact hfit
  have hAnone : A.pileOfTop z = none := by
    cases h : A.pileOfTop z with
    | none => rfl
    | some k =>
        rw [canPlace_inr_located h] at hA
        exact absurd hfit (by rw [hA]; simp)
  obtain ⟨k, hk, -⟩ := canPlace_inr hC
  exact ⟨hfit, hAnone, k, hk⟩

/-- **THE `inr` BASE STAYS ENABLED.**  Once available, a reversible, read-safe
(for `c`) and seat-inert (on `inr z`) letter keeps it available.  This is the
placement half of `PullKit.pullable_step`, isolated. -/
theorem canPlace_inr_stays {st s' : State} {c z : Card} {q : Move}
    (hst : st.WF) (hstep : State.step st q = some s')
    (hrev : reversibleAtW st q)
    (hread : SlideFwd.ReadSafe c q)
    (hseat : MtnPr.SeatInert (Sum.inr z) q)
    (hft : st.foundTop c.suit = some c)
    (h : st.canPlace c (Sum.inr z) = true) :
    s'.canPlace c (Sum.inr z) = true :=
  (PullKit.pullable_step hst hstep hrev hread hseat ⟨hft, h⟩).2

/-- **THE `inr` EXPOSURE RESIDUAL.**  Every residual play whose pull lands on a
base card `z` that is exposed (`pileOfTop z = none` → `some k`) during the
interior shortens.  The exposure letter is a `raise` or a `slide` (a pull can
never remove a card from a pile), and it must be moved before the raise or
traded for a slide; this is the exact remaining `inr` hole. -/
def InrExposeResidual : Prop :=
  ∀ (u v : State) (ρ pre γ₁ γ₂ post : List Move) (c z : Card) (A E : State),
    u.WF → ShufflePlayW u ρ v →
    ρ = pre ++ Move.tabToFound c :: γ₁ ++ Move.foundToTab c (Sum.inr z) :: post →
    ShufflePlayW u pre A →
    (∀ q ∈ γ₁, SlideFwd.ReadSafe c q) →
    (∀ q ∈ γ₁, MtnPr.SeatInert (Sum.inr z) q) →
    A.pileOfTop z = none →
    (∃ k, E.pileOfTop z = some k) →
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length

/-! ## §5. The local net-one identity behind the gap witness

At a `WF` state `S` where `c` tops pile `a` and a *different* card `d` sits
alone on pile `p ≠ a`, the three-letter segment
`raise c ; raise d ; pull c (inl p)` lands exactly where the two-letter
segment `raise d ; slide c (inl p)` lands.  This is the engine of
`PullKit.gap_instance_shortens`, stated without the concrete witness. -/

theorem raise_raise_pull_eq_raise_slide
    {S : State} {c d : Card} {a p : Anchor}
    (hS : S.WF)
    (hc : S.pileOfTop c = some a)
    (hpa : p ≠ a)
    (hdbare : S.piles p = ⟨[], [d]⟩)
    (hsu : d.suit ≠ c.suit) :
    CommuteStep.pullSt (raiseSt (raiseSt S c a) d p) c (Sum.inl p) =
      CommuteStep.slideSt (raiseSt S d p) c (Sum.inl p) a := by
  -- the `c`-run is a singleton; `below`/`chop` agree
  have hnd : (S.piles a).faceUp.Nodup := runOK_nodup (hS.runOK_of a)
  have hlast : lastOf (S.piles a).faceUp = some c := (pileOfTop_top hc).2
  have hfrom : fromCard c (S.piles a).faceUp = [c] :=
    NoSelfKit.fromCard_singleton_of_last hnd hlast
  have hbelow : below c (S.piles a).faceUp = chop (S.piles a).faceUp :=
    NoSelfKit.below_eq_chop_of_last hnd hlast
  -- pile reads
  have hXp : (raiseSt S c a).piles p = S.piles p := by
    rw [raiseSt_piles_apply, ite_eq_right hpa]
  have hEp : (raiseSt (raiseSt S c a) d p).piles p = ⟨[], []⟩ := by
    rw [raiseSt_piles_apply, ite_eq_left rfl, hXp, hdbare]
    exact Pile.afterRunRemoved_bare rfl
  have hEa : (raiseSt (raiseSt S c a) d p).piles a =
      Pile.afterRunRemoved (S.piles a) (chop (S.piles a).faceUp) := by
    rw [raiseSt_piles_apply, ite_eq_right (Ne.symm hpa), raiseSt_piles_apply, ite_eq_left rfl]
  have hYp : (raiseSt S d p).piles p = ⟨[], []⟩ := by
    rw [raiseSt_piles_apply, ite_eq_left rfl, hdbare]
    exact Pile.afterRunRemoved_bare rfl
  have hYa : (raiseSt S d p).piles a = S.piles a := by
    rw [raiseSt_piles_apply, ite_eq_right (Ne.symm hpa)]
  -- foundation reads
  have hEfc : (raiseSt (raiseSt S c a) d p).found c.suit = S.found c.suit ++ [c] := by
    rw [raiseSt_found_apply, ite_eq_right (Ne.symm hsu), raiseSt_found_apply, ite_eq_left rfl]
  have hEfd : (raiseSt (raiseSt S c a) d p).found d.suit = S.found d.suit ++ [d] := by
    rw [raiseSt_found_apply, ite_eq_left rfl, raiseSt_found_apply, ite_eq_right hsu]
  have hYfc : (raiseSt S d p).found c.suit = S.found c.suit := by
    rw [raiseSt_found_apply, ite_eq_right (Ne.symm hsu)]
  have hYfd : (raiseSt S d p).found d.suit = S.found d.suit ++ [d] := by
    rw [raiseSt_found_apply, ite_eq_left rfl]
  apply State.ext
  · funext s
    rw [CommuteStep.pullSt_found_apply]
    by_cases hsc : s = c.suit
    · rw [ite_eq_left hsc, hsc, hEfc, chop_snoc, CommuteStep.slideSt_found, hYfc]
    · rw [ite_eq_right hsc]
      by_cases hsd : s = d.suit
      · rw [hsd, hEfd, CommuteStep.slideSt_found, hYfd]
      · rw [raiseSt_found_apply, ite_eq_right hsd]
        rw [raiseSt_found_apply, ite_eq_right hsc]
        rw [CommuteStep.slideSt_found, raiseSt_found_apply, ite_eq_right hsd]
  · funext a'
    rw [CommuteStep.pullSt_piles, putCard_inl_piles_apply]
    rw [CommuteStep.slideSt, putRun_inl_piles_apply, setPile_piles_apply,
      hYa, hfrom]
    by_cases ha'p : a' = p
    · rw [ite_eq_left ha'p, ite_eq_left ha'p]
    · rw [ite_eq_right ha'p, ite_eq_right ha'p]
      by_cases ha'a : a' = a
      · rw [ite_eq_left ha'a]
        rw [hbelow, ha'a, hEa]
      · rw [ite_eq_right ha'a]
        have hL : (raiseSt (raiseSt S c a) d p).piles a' = S.piles a' := by
          rw [raiseSt_piles_apply, ite_eq_right ha'p, raiseSt_piles_apply, ite_eq_right ha'a]
        have hR : (raiseSt S d p).piles a' = S.piles a' := by
          rw [raiseSt_piles_apply, ite_eq_right ha'p]
        rw [hL, hR]
  · simp only [CommuteStep.pullSt_stock, raiseSt_stock, CommuteStep.slideSt_stock]
  · simp only [CommuteStep.pullSt_waste, raiseSt_waste, CommuteStep.slideSt_waste]
  · simp only [CommuteStep.pullSt_drawStep, raiseSt_drawStep, CommuteStep.slideSt_drawStep]

/-- The raise-shape guard is true at a located seat with the cell condition. -/
theorem tabToFoundR_true_of_seat {st : State} {c : Card} {a : Anchor}
    (hnext : st.nextUp c = true) (hpo : st.pileOfTop c = some a)
    (hcell : chop (st.piles a).faceUp ≠ [] ∨
      (chop (st.piles a).faceUp = [] ∧ (st.piles a).hidden = [] ∧ c.rank = Rank.king)) :
    tabToFoundR st c = true := by
  rcases hcell with h | ⟨hchop, hhid, hk⟩
  · cases hc : chop (st.piles a).faceUp with
    | nil => exact absurd hc h
    | cons x xs => simp only [tabToFoundR, hnext, hpo, hc]
  · simp only [tabToFoundR, hnext, hpo, hchop, hhid]
    rw [decide_eq_true hk]

/-- **THE LOCAL SHORTENING.**  At a `WF` state `S` where `c` tops pile `a`
with the raise data (`nextUp c`, and the chop-or-bare-king cell), and the bare
king `d` sits alone on pile `p ≠ a`, the three-letter word
`raise c ; raise d ; pull c (inl p)` is **not shortest**: the two-letter word
`raise d ; slide c (inl p)` is a witness play with the same endpoint.
This is the local engine of `PullKit.gap_instance_shortens`. -/
theorem raise_raise_pull_shortens_local
    {S : State} {c d : Card} {a p : Anchor}
    (hS : S.WF)
    (hc : S.pileOfTop c = some a)
    (hd : S.pileOfTop d = some p)
    (hpa : p ≠ a)
    (hdbare : S.piles p = ⟨[], [d]⟩)
    (hsu : d.suit ≠ c.suit)
    (hnextC : S.nextUp c = true)
    (hnextD : S.nextUp d = true)
    (hcellC : chop (S.piles a).faceUp ≠ [] ∨
      (chop (S.piles a).faceUp = [] ∧ (S.piles a).hidden = [] ∧ c.rank = Rank.king))
    (hking : c.rank = Rank.king) (hkingD : d.rank = Rank.king) :
    ∃ ρ' : List Move,
      ShufflePlayW S ρ'
        (CommuteStep.pullSt (raiseSt (raiseSt S c a) d p) c (Sum.inl p)) ∧
      ρ'.length < 3 := by
  -- `d`'s raise, at `S`
  have hstepD : State.step S (Move.tabToFound d) =
      some (raiseSt S d p) := by
    rw [step_tabToFound_splice hnextD hd]
    rfl
  -- the slide at the `d`-image
  have hcmem : c ∈ (S.piles a).faceUp := lastOf_mem (pileOfTop_top hc).2
  have hholdY : (raiseSt S d p).pileHolding c = some a :=
    CommuteStep.pileHolding_raiseSt_ne hS hd hcmem (Ne.symm hpa)
  have hYp : (raiseSt S d p).piles p = ⟨[], []⟩ :=
    raiseSt_piles_self_bare (by rw [hdbare]) (by rw [hdbare])
  have hYa : (raiseSt S d p).piles a = S.piles a := by
    rw [raiseSt_piles_apply, ite_eq_right (Ne.symm hpa)]
  have hcpY : (raiseSt S d p).canPlace c (Sum.inl p) = true :=
    canPlace_inl_of_empty_king (by rw [hYp]; rfl) hking
  have hnd : (S.piles a).faceUp.Nodup := runOK_nodup (hS.runOK_of a)
  have hlast : lastOf (S.piles a).faceUp = some c := (pileOfTop_top hc).2
  have hfrom : fromCard c (S.piles a).faceUp = [c] :=
    NoSelfKit.fromCard_singleton_of_last hnd hlast
  have hbelow : below c (S.piles a).faceUp = chop (S.piles a).faceUp :=
    NoSelfKit.below_eq_chop_of_last hnd hlast
  have hfromY : fromCard c ((raiseSt S d p).piles a).faceUp = [c] := by
    rw [hYa, hfrom]
  have hstepSL : State.step (raiseSt S d p) (Move.tabToTab c (Sum.inl p)) =
      some (CommuteStep.slideSt (raiseSt S d p) c (Sum.inl p) a) := by
    simp [step_tabToTab_eq, hholdY, hcpY, hfromY, CommuteStep.slideSt]
  -- reversibility of the two letters
  have hYwf : (raiseSt S d p).WF := step_wf hS hstepD
  have hrevD : reversibleAtW S (Move.tabToFound d) :=
    (tabToFoundR_iff_reversibleAtW hS d).mp
      (tabToFoundR_true_of_seat hnextD hd
        (by rw [hdbare]; exact Or.inr ⟨by simp [chop], rfl, hkingD⟩))
  have hcellY : below c ((raiseSt S d p).piles a).faceUp ≠ [] ∨
      (below c ((raiseSt S d p).piles a).faceUp = [] ∧
        ((raiseSt S d p).piles a).hidden = [] ∧ c.rank = Rank.king) := by
    rw [hYa, hbelow]
    rcases hcellC with hchop | ⟨hchop, hhid, hk⟩
    · exact Or.inl hchop
    · exact Or.inr ⟨hchop, hhid, hk⟩
  have hrevSL : reversibleAtW (raiseSt S d p) (Move.tabToTab c (Sum.inl p)) :=
    (tabToTabR_iff_reversibleAtW hYwf c (Sum.inl p)).mp
      (R12.tabToTabR_true_of hholdY hcpY hcellY)
  -- the endpoint identity
  have hZ : CommuteStep.pullSt (raiseSt (raiseSt S c a) d p) c (Sum.inl p) =
      CommuteStep.slideSt (raiseSt S d p) c (Sum.inl p) a :=
    raise_raise_pull_eq_raise_slide hS hc hpa hdbare hsu
  refine ⟨[Move.tabToFound d, Move.tabToTab c (Sum.inl p)], ?_, ?_⟩
  · rw [hZ]
    exact Walk.cons hrevD hstepD (Walk.cons hrevSL hstepSL (Walk.nil _))
  · simp

/-- **THE ADJACENT INTERIOR-ENABLING CASE.**  The residual play
`pre ++ raise c :: raise d :: γ₂ ++ pull c (inl p) :: post`, where the *second*
raise empties the `inl` base pile `p` and `c` is a king, shortens: bubble the
pull left past `γ₂` (it is legal from `d`'s image on), then replace
`raise c ; raise d ; pull c (inl p)` by `raise d ; slide c (inl p)` (§5's
local net-one identity).  This generalises `PullKit.gap_instance_shortens`
to an arbitrary read-safe, seat-inert tail `γ₂`. -/
theorem baseEnabling_inl_interior_adjacent_shortens
    {u v : State} {ρ pre γ₂ post : List Move} {c d : Card} {a p : Anchor} {A B E : State}
    (huwf : u.WF) (hplay : ShufflePlayW u ρ v)
    (hρ : ρ = pre ++ Move.tabToFound c :: Move.tabToFound d :: γ₂
              ++ Move.foundToTab c (Sum.inl p) :: post)
    (hpre : ShufflePlayW u pre A)
    (h1 : State.step A (Move.tabToFound c) = some B)
    (h2 : State.step B (Move.tabToFound d) = some E)
    (hread : ∀ q ∈ (Move.tabToFound d :: γ₂), SlideFwd.ReadSafe c q)
    (hseat : ∀ q ∈ (Move.tabToFound d :: γ₂), MtnPr.SeatInert (Sum.inl p) q)
    (hpoC : A.pileOfTop c = some a)
    (hpoD : A.pileOfTop d = some p)
    (hbare : A.piles p = ⟨[], [d]⟩)
    (hnextC : A.nextUp c = true)
    (hnextD : A.nextUp d = true)
    (hcellC : chop (A.piles a).faceUp ≠ [] ∨
      (chop (A.piles a).faceUp = [] ∧ (A.piles a).hidden = [] ∧ c.rank = Rank.king))
    (hking : c.rank = Rank.king) (hkingD : d.rank = Rank.king) :
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length := by
  have hsu : d.suit ≠ c.suit := hread (Move.tabToFound d) (List.mem_cons_self ..)
  have hAwf : A.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  -- `p ≠ a`: two distinct cards cannot top the same pile at `WF`
  have htopC : (A.piles a).top = some c := (pileOfTop_eq_some_iff hAwf).mp hpoC
  have hpa : p ≠ a := by
    intro h
    have htopD : (A.piles a).top = some d := by
      rw [← h]; exact (pileOfTop_eq_some_iff hAwf).mp hpoD
    have hcd : c = d := Option.some.inj (htopC.symm.trans htopD)
    exact hsu (congrArg Card.suit hcd.symm)
  -- the two raises, explicitly
  have hB : B = raiseSt A c a := by
    have := step_tabToFound_splice hnextC hpoC
    exact Option.some.inj (h1.symm.trans this)
  have hE : E = raiseSt B d p := by
    have hnextDB : B.nextUp d = true := by
      rw [hB, raiseSt_nextUp_ne (u := A) (c := c) (d := d) (a := a) (Ne.symm hsu)]
      exact hnextD
    have hpoDB : B.pileOfTop d = some p := by
      rw [hB]; exact raiseSt_pileOfTop_ne hAwf hpoD (Ne.symm hpa)
    have := step_tabToFound_splice hnextDB hpoDB
    exact Option.some.inj (h2.symm.trans this)
  -- the pull is legal right after the enabling raise
  have hftB : B.foundTop c.suit = some c := by
    rw [hB]; exact foundTop_raiseSt_self A c a
  have hftE : E.foundTop c.suit = some c := by
    rw [hE]
    unfold State.foundTop
    rw [raiseSt_found_apply, ite_eq_right (Ne.symm hsu)]
    unfold State.foundTop at hftB
    exact hftB
  have hBp : B.piles p = A.piles p := by
    rw [hB, raiseSt_piles_apply, ite_eq_right hpa]
  have hEp : E.piles p = ⟨[], []⟩ := by
    rw [hE, raiseSt_piles_apply, ite_eq_left rfl, hBp, hbare]
    exact Pile.afterRunRemoved_bare rfl
  have hpull : PullKit.Pullable E c (Sum.inl p) :=
    ⟨hftE, canPlace_inl_of_empty_king (by rw [hEp]; rfl) hking⟩
  have hEwf : E.WF := step_wf (step_wf hAwf h1) h2
  -- read the suffix `γ₂ ++ pull :: post` off the play
  have hρa : ρ = pre ++ (Move.tabToFound c :: Move.tabToFound d :: γ₂
              ++ Move.foundToTab c (Sum.inl p) :: post) := by
    rw [hρ]; simp only [List.append_assoc]
  obtain ⟨A₁, hpre₁, hrest₁⟩ :=
    ValleyElim.ShufflePlayW_split hplay pre _ hρa
  have hAA : A₁ = A := Option.some.inj ((Walk_run _ hpre₁).symm.trans (Walk_run _ hpre))
  subst A₁
  obtain ⟨B₁, -, h1', hrest₂⟩ := Bubble.walk_cons_inv hrest₁
  have hBB : B₁ = B := Option.some.inj (h1'.symm.trans h1)
  subst B₁
  obtain ⟨E₁, -, h2', hrest₃⟩ := Bubble.walk_cons_inv hrest₂
  have hEE : E₁ = E := Option.some.inj (h2'.symm.trans h2)
  subst E₁
  -- bubble the pull past `γ₂`
  have hsw : PullKit.PullSwaps E c (Sum.inl p) γ₂ :=
    PullKit.pullSwaps_of_read hEwf hrest₃ hpull
      (fun q hq => hread q (List.mem_cons_of_mem _ hq))
      (fun q hq => hseat q (List.mem_cons_of_mem _ hq))
  have hplay₂ : ShufflePlayW E (Move.foundToTab c (Sum.inl p) :: γ₂ ++ post) v :=
    PullKit.pull_bubble γ₂ hrest₃ hsw
  obtain ⟨F, -, hstepF, htail⟩ := Bubble.walk_cons_inv hplay₂
  obtain ⟨c', htop', hc'c, -, hsF⟩ := step_foundToTab_inv hstepF
  subst c'
  have hF : F = CommuteStep.pullSt E c (Sum.inl p) := by rw [hsF]; rfl
  -- the local replacement
  obtain ⟨ρloc, hloc, hlenloc⟩ :=
    raise_raise_pull_shortens_local hAwf hpoC hpoD hpa hbare hsu hnextC hnextD
      hcellC hking hkingD
  have hloc' : ShufflePlayW A ρloc F := by
    rw [hF, hE, hB]
    exact hloc
  refine ⟨pre ++ (ρloc ++ (γ₂ ++ post)), ?_, ?_⟩
  · exact ShufflePlayW_append hpre (ShufflePlayW_append hloc' htail)
  · rw [hρ]
    simp only [List.length_append, List.length_cons]
    omega

/-! ## §6. Composition: how far the chain reaches

`MtnPr.SameCardRelocation` is the same-card deletion residual; it kills a
same-card `raise c ; γ ; pull c b` **only along its own gates** (`γ` read-safe
for `c`, seat-inert on `b`).  This section records exactly that consequence
(the same-card half of M1, gated) and leaves the campaign-level composition
analysis to the report. -/

/-- **NO GATED SAME-CARD RELOCATION IN A SHORTEST PLAY.**  Direct minimality
consequence of `SameCardRelocation`. -/
theorem no_gated_sameCard_relocation_of_shortest
    (hrel : MtnPr.SameCardRelocation)
    {u v : State} {ρ : List Move}
    (huwf : u.WF) (hplay : ShufflePlayW u ρ v)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length)
    {pre γ post : List Move} {c : Card} {b : Base}
    (hρ : ρ = pre ++ Move.tabToFound c :: γ ++ Move.foundToTab c b :: post)
    (hread : ∀ q ∈ γ, SlideFwd.ReadSafe c q)
    (hseat : ∀ q ∈ γ, MtnPr.SeatInert b q) : False := by
  obtain ⟨ρ', hρ', hlen⟩ := hrel u v ρ pre γ post c b huwf hplay hρ hread hseat
  have := hmin ρ' hρ'
  omega

/-- **`SameCardRelocation` FROM READY-AT-IMAGE + `BaseEnabling`.**  The
composition of §1 and §3: the ready-at-image half is a theorem
(`shortens_of_readyAtImage`), so only `BaseEnabling` remains as input.  The two
sub-cases proved in §2 (`baseEnabling_inl_shortens`) and §5
(`baseEnabling_inl_interior_adjacent_shortens`) are instances of `BaseEnabling`. -/
theorem sameCardRelocation_of_baseEnabling_only
    (h : BaseEnabling) : MtnPr.SameCardRelocation :=
  sameCardRelocation_of_baseEnabling h

/-- **THE GAP WITNESS IS AN INSTANCE.**  The kernel witness of
`PullKit.gap_instance_shortens` satisfies §5's hypotheses, so the local
shortening reproduces that result (`gapState --raise HK ; raise SK ; pull HK
-> inl p1--> gapD` shortens to two letters). -/
theorem gap_recovered_shortens :
    ∃ ρ' : List Move, ShufflePlayW PullKit.gapState ρ' PullKit.gapD ∧
      ρ'.length < 3 := by
  have h := raise_raise_pull_shortens_local
    (S := PullKit.gapState) (c := PullKit.GAPK_C) (d := PullKit.GAPK_W)
    (a := Anchor.p0) (p := Anchor.p1)
    PullKit.gapState_wf
    PullKit.gapState_pileOfTop_C
    PullKit.gapState_pileOfTop_W
    (by decide)
    (by decide)
    (by decide)
    PullKit.gapState_nextUp_C
    PullKit.gapState_nextUp_W
    (Or.inr ⟨by decide, by decide, rfl⟩)
    rfl rfl
  exact h

end BaseEn

#print axioms BaseEn.setPile_piles_apply
#print axioms BaseEn.putCard_inl_piles_apply
#print axioms BaseEn.putRun_inl_piles_apply
#print axioms BaseEn.tabToFoundR_true_of_seat
#print axioms BaseEn.gap_recovered_shortens
#print axioms BaseEn.no_gated_sameCard_relocation_of_shortest
#print axioms BaseEn.sameCardRelocation_of_baseEnabling_only
#print axioms BaseEn.baseEnabling_inl_interior_adjacent_shortens
#print axioms BaseEn.raise_raise_pull_shortens_local
#print axioms BaseEn.raise_raise_pull_eq_raise_slide
#print axioms BaseEn.foundTop_raiseSt_self
#print axioms BaseEn.shortens_of_readyAtImage
#print axioms BaseEn.canPlace_inl_of_empty_king
#print axioms BaseEn.raiseSt_piles_self_bare
#print axioms BaseEn.raise_empties_inl_base
#print axioms BaseEn.baseEnabling_inl_shortens
#print axioms BaseEn.sameCardRelocation_of_baseEnabling
#print axioms BaseEn.canPlace_inr_false_of_canSitOn_false
#print axioms BaseEn.inr_never_enabled_of_dead_fit
#print axioms BaseEn.inr_enable_needs_expose
#print axioms BaseEn.canPlace_inr_stays
