import Orig2.ForkBaseEnabling

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Temp/InrExp - the `inr` exposure residual of the base-enabling gap

READ-ONLY scratch card (`Temp/`).  No source edits, no commit.  No `sorry`,
no `Classical.choice`, no `native_decide`; axiom battery at the tail.

`BaseEn.InrExposeResidual` (`Orig2/ForkBaseEnabling.lean:269`) is the last
base-enabling case of `MtnPr.SameCardRelocation`: the pull lands on an `inr z`
base that is **buried** at the raise's origin (`A.pileOfTop z = none`) and only
becomes a pile top somewhere inside the interior `γ₁`.

* §0  two-line helpers.
* §1  `pullSt_raiseSt_eq_slideSt`: `MtnPr.raise_pull_eq_slide`
  (`Orig2/ForkRelocate.lean:90`) in the explicit `pullSt`/`slideSt` normal form.
* §2  the **exposing raise** identity: `raise c ; raise x ; pull c (inr z)` =
  `raise x ; slide c (inr z)` (`raise_raise_pull_eq_raise_slide_inr`), via
  `raiseSt_commute` (`Orig2/ForkCriticalPair.lean:206`) + §1.
* §3  the **exposing slide** identity: `raise c ; slide w b'' ; pull c (inr z)`
  = `slide w b'' ; slide c (inr z)` (`raise_slide_pull_eq_slide_slide_inr`),
  via `CommuteStep.step_comm_slide_raise` (`Orig2/ForkCommuteSlide.lean:951`)
  + §1.
* §4  the full-play adjacent shortening built on the raising identity, the
  exact `inr` analogue of `BaseEn.baseEnabling_inl_interior_adjacent_shortens`
  (`Orig2/ForkBaseEnabling.lean:452`): bubble the pull across the read-safe,
  seat-inert tail (`PullKit.pull_bubble`), then replace the three letters.
* §5  the residual bookkeeping and the composition chain; the exact residual is
  `InrExpDeep` (§5) together with the play-level *lift* named `InrExpLift`.
-/

namespace InrExp

open MountainKit
open CommuteStep

/-! ## §0. Helpers -/

/-- Two distinct cards cannot top the same pile at a `WF` state. -/
theorem pileOfTop_ne_of_ne {st : State} (hwf : st.WF) {c d : Card} {a b : Anchor}
    (hc : st.pileOfTop c = some a) (hd : st.pileOfTop d = some b) (hcd : c ≠ d) :
    a ≠ b := by
  intro hab
  have htc : (st.piles a).top = some c := (pileOfTop_eq_some_iff hwf).mp hc
  have htd : (st.piles b).top = some d := (pileOfTop_eq_some_iff hwf).mp hd
  rw [hab] at htc
  exact hcd (Option.some.inj (htc.symm.trans htd))

/-- `z ≠ c` from a live fit `canSitOn c z`. -/
theorem ne_of_canSitOn {c z : Card} (h : canSitOn c z = true) : z ≠ c := by
  intro hzc
  rw [hzc, MtnPr.canSitOn_self_false] at h
  exact absurd h (by simp)

/-! ## §1. The net-one core in normal form -/

/-- **`raise c ; pull c b` IS THE SINGLE SLIDE `slide c b`**, in the explicit
`pullSt` / `slideSt` normal form.  (`MtnPr.raise_pull_eq_slide`, read through
the two spliced step rows.) -/
theorem pullSt_raiseSt_eq_slideSt {st : State} {c : Card} {b : Base} {a : Anchor}
    (hwf : st.WF) (hnext : st.nextUp c = true) (hpo : st.pileOfTop c = some a)
    (hcp : st.canPlace c b = true) (hbc : b ≠ Sum.inr c) :
    CommuteStep.pullSt (raiseSt st c a) c b = CommuteStep.slideSt st c b a := by
  have hcore := MtnPr.raise_pull_eq_slide hwf hnext hpo hcp
  have hcp' : (raiseSt st c a).canPlace c b = true := by
    rw [R12.canPlace_raiseSt hwf hpo hbc hcp]; exact hcp
  have hpull : State.step (raiseSt st c a) (Move.foundToTab c b) =
      some (CommuteStep.pullSt (raiseSt st c a) c b) := by
    rw [step_foundToTab_splice (BaseEn.foundTop_raiseSt_self st c a) hcp']; rfl
  have hhold : st.pileHolding c = some a := Drain.pileHolding_of_pileOfTop hwf hpo
  have hfrom : fromCard c (st.piles a).faceUp = [c] :=
    NoSelfKit.fromCard_singleton_of_last (runOK_nodup (hwf.runOK_of a))
      (pileOfTop_top hpo).2
  have hslide : State.step st (Move.tabToTab c b) = some (CommuteStep.slideSt st c b a) := by
    rw [step_tabToTab_eq, hhold]
    simp only [hcp, ite_true, hfrom, CommuteStep.slideSt]
  have hsome :
      some (CommuteStep.pullSt (raiseSt st c a) c b) = some (CommuteStep.slideSt st c b a) := by
    rw [← hpull, hcore, hslide]
  exact Option.some.inj hsome

/-! ## §2. The exposing raise: `raise c ; raise x ; pull c (inr z)`

At `S`, `c` tops pile `a`; a *different* pile `p` carries `x` on top with `z`
directly below (so `raise x` exposes `z`).  Then the three letters land exactly
where the two letters `raise x ; slide c (inr z)` land: the two raises commute
(`raiseSt_commute`), and at the `x`-image the raise-then-pull of `c` is the
single slide (§1). -/

theorem raise_raise_pull_eq_raise_slide_inr
    {S : State} {c x z : Card} {a p : Anchor}
    (hS : S.WF)
    (hape : p ≠ a)
    (hsu : x.suit ≠ c.suit)
    (hc : S.pileOfTop c = some a)
    (hnextC : S.nextUp c = true)
    (hnextX : S.nextUp x = true)
    (hpoX : S.pileOfTop x = some p)
    (hzE : (raiseSt S x p).pileOfTop z = some p)
    (hfit : canSitOn c z = true) :
    CommuteStep.pullSt (raiseSt (raiseSt S c a) x p) c (Sum.inr z) =
      CommuteStep.slideSt (raiseSt S x p) c (Sum.inr z) a := by
  have hzc : z ≠ c := ne_of_canSitOn hfit
  -- the `x`-raise is a legal step, hence its landing is `WF`
  have hstepX : State.step S (Move.tabToFound x) = some (raiseSt S x p) := by
    rw [step_tabToFound_splice hnextX hpoX]; rfl
  have hXwf : (raiseSt S x p).WF := step_wf hS hstepX
  -- the two raises commute
  have hcomm : raiseSt (raiseSt S c a) x p = raiseSt (raiseSt S x p) c a :=
    raiseSt_commute (u := S) (c := c) (d := x) (a := a) (b := p) (Ne.symm hape) (Ne.symm hsu)
  -- `c` is still a pile top at the `x`-image
  have hcX : (raiseSt S x p).pileOfTop c = some a :=
    raiseSt_pileOfTop_ne hS hc hape
  have hnextXC : (raiseSt S x p).nextUp c = true := by
    rw [raiseSt_nextUp_ne (u := S) (c := x) (d := c) (a := p) hsu]; exact hnextC
  have hcpX : (raiseSt S x p).canPlace c (Sum.inr z) = true := by
    rw [canPlace_inr_eq, hzE]; exact hfit
  rw [hcomm]
  exact pullSt_raiseSt_eq_slideSt hXwf hnextXC hcX hcpX (by simpa using hzc)

/-! ## §3. The exposing slide: `raise c ; slide w b'' ; pull c (inr z)`

The slide `w → b''` fires at the **raise's image** `B = raiseSt S c a` and
exposes `z`.  `step_comm_slide_raise` puts the same composite behind
`slide w b''` first (`S1`, landing on `S21`), so the raise-then-slide landing
`E` is `S21 = raiseSt S1 c a1`; then §1 turns `raise c ; pull c (inr z)` at
`S1` into the single slide `slide c (inr z)`. -/

theorem raise_slide_pull_eq_slide_slide_inr
    {S S1 B E S21 : State} {c w z : Card} {a a1 : Anchor} {b'' : Base}
    (hS : S.WF)
    (hrevW : reversibleAtW S (Move.tabToTab w b''))
    (hrevC : reversibleAtW S (Move.tabToFound c))
    (hslideS : State.step S (Move.tabToTab w b'') = some S1)
    (hraiseS : State.step S (Move.tabToFound c) = some B)
    (h12 : State.step S1 (Move.tabToFound c) = some S21)
    (h21 : State.step B (Move.tabToTab w b'') = some E)
    (hS1wf : S1.WF)
    (hnextC1 : S1.nextUp c = true)
    (hpoC1 : S1.pileOfTop c = some a1)
    (hfit1 : S1.canPlace c (Sum.inr z) = true)
    (hzc : z ≠ c) :
    CommuteStep.pullSt E c (Sum.inr z) = CommuteStep.slideSt S1 c (Sum.inr z) a1 := by
  have hES : E = S21 :=
    (CommuteStep.step_comm_slide_raise hS hrevW hrevC hslideS hraiseS h12 h21).symm
  obtain ⟨-, a', hpo, hs⟩ := step_tabToFound_inv h12
  have ha' : a' = a1 := Option.some.inj (hpo.symm.trans hpoC1)
  have hS21 : S21 = raiseSt S1 c a1 := by
    rw [ha'] at hs
    exact hs
  rw [hES, hS21]
  exact pullSt_raiseSt_eq_slideSt hS1wf hnextC1 hpoC1 hfit1 (by simpa using hzc)

/-! ## §4. The full play: an adjacent exposing raise shortens

The residual play `pre ++ raise c :: raise x :: γ₂ ++ pull c (inr z) :: post`
with `z` exposed by `raise x` shortens: bubble the pull left across `γ₂` (legal
from `x`'s image on), then replace `raise c ; raise x ; pull c (inr z)` by
`raise x ; slide c (inr z)` (§2).  This is the `inr` analogue of
`BaseEn.baseEnabling_inl_interior_adjacent_shortens`. -/

theorem inr_expose_raise_adjacent_shortens
    {u v : State} {ρ pre γ₂ post : List Move} {c x z : Card} {a p : Anchor}
    {A B E : State}
    (huwf : u.WF) (hplay : ShufflePlayW u ρ v)
    (hρ : ρ = pre ++ Move.tabToFound c :: Move.tabToFound x :: γ₂
              ++ Move.foundToTab c (Sum.inr z) :: post)
    (hpre : ShufflePlayW u pre A)
    (h1 : State.step A (Move.tabToFound c) = some B)
    (h2 : State.step B (Move.tabToFound x) = some E)
    (hread : ∀ q ∈ (Move.tabToFound x :: γ₂), SlideFwd.ReadSafe c q)
    (hseat : ∀ q ∈ (Move.tabToFound x :: γ₂), MtnPr.SeatInert (Sum.inr z) q)
    (hpoC : A.pileOfTop c = some a)
    (hnextC : A.nextUp c = true)
    (hpoX : A.pileOfTop x = some p)
    (hnextX : A.nextUp x = true)
    (hpa : p ≠ a)
    (hcellX : chop (A.piles p).faceUp ≠ [] ∨
      (chop (A.piles p).faceUp = [] ∧ (A.piles p).hidden = [] ∧ x.rank = Rank.king))
    (hcellC : chop (A.piles a).faceUp ≠ [] ∨
      (chop (A.piles a).faceUp = [] ∧ (A.piles a).hidden = [] ∧ c.rank = Rank.king))
    (hfit : canSitOn c z = true)
    (hzE : (raiseSt A x p).pileOfTop z = some p)
    (hftE : E.foundTop c.suit = some c)
    (hcpE : E.canPlace c (Sum.inr z) = true) :
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length := by
  have hsu : x.suit ≠ c.suit := hread (Move.tabToFound x) (List.mem_cons_self ..)
  have hAwf : A.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  -- the two raises, explicitly
  have hB : B = raiseSt A c a := by
    have := step_tabToFound_splice hnextC hpoC
    exact Option.some.inj (h1.symm.trans this)
  have hnextXB : B.nextUp x = true := by
    rw [hB, raiseSt_nextUp_ne (u := A) (c := c) (d := x) (a := a) (Ne.symm hsu)]
    exact hnextX
  have hpoXB : B.pileOfTop x = some p := by
    rw [hB]; exact raiseSt_pileOfTop_ne hAwf hpoX (Ne.symm hpa)
  have hE : E = raiseSt B x p := by
    have := step_tabToFound_splice hnextXB hpoXB
    exact Option.some.inj (h2.symm.trans this)
  -- the pull is legal at the `x`-image
  have hpull : PullKit.Pullable E c (Sum.inr z) := ⟨hftE, hcpE⟩
  have hEwf : E.WF := step_wf (step_wf hAwf h1) h2
  -- read the suffix off the play
  have hρa : ρ = pre ++ (Move.tabToFound c :: Move.tabToFound x :: γ₂
              ++ Move.foundToTab c (Sum.inr z) :: post) := by
    rw [hρ]; simp only [List.append_assoc]
  obtain ⟨A₁, hpre₁, hrest₁⟩ :=
    ValleyElim.ShufflePlayW_split hplay pre _ hρa
  have hAA : A₁ = A := Option.some.inj ((Walk_run _ hpre₁).symm.trans (Walk_run _ hpre))
  subst hAA
  obtain ⟨B₁, -, h1', hrest₂⟩ := Bubble.walk_cons_inv hrest₁
  have hBB : B₁ = B := Option.some.inj (h1'.symm.trans h1)
  subst hBB
  obtain ⟨E₁, -, h2', hrest₃⟩ := Bubble.walk_cons_inv hrest₂
  have hEE : E₁ = E := Option.some.inj (h2'.symm.trans h2)
  subst hEE
  -- bubble the pull past `γ₂`
  have hsw : PullKit.PullSwaps E₁ c (Sum.inr z) γ₂ :=
    PullKit.pullSwaps_of_read hEwf hrest₃ hpull
      (fun q hq => hread q (List.mem_cons_of_mem _ hq))
      (fun q hq => hseat q (List.mem_cons_of_mem _ hq))
  have hplay₂ : ShufflePlayW E₁ (Move.foundToTab c (Sum.inr z) :: γ₂ ++ post) v :=
    PullKit.pull_bubble γ₂ hrest₃ hsw
  obtain ⟨F, -, hstepF, htail⟩ := Bubble.walk_cons_inv hplay₂
  obtain ⟨c', htop', hc'c, hcF, hsF⟩ := step_foundToTab_inv hstepF
  rw [hc'c] at htop'
  have hF : F = CommuteStep.pullSt E₁ c (Sum.inr z) := by rw [hsF]; rfl
  -- the local replacement's endpoint
  have hS1wf : (raiseSt A₁ x p).WF := step_wf hAwf (by
    rw [step_tabToFound_splice hnextX hpoX]; rfl)
  have hident : CommuteStep.pullSt E₁ c (Sum.inr z) =
      CommuteStep.slideSt (raiseSt A₁ x p) c (Sum.inr z) a := by
    rw [hE, hB]
    exact raise_raise_pull_eq_raise_slide_inr hAwf hpa hsu hpoC hnextC hnextX hpoX hzE hfit
  -- the two-letter witness play from `A`
  have hrevX : reversibleAtW A₁ (Move.tabToFound x) :=
    (tabToFoundR_iff_reversibleAtW hAwf x).mp
      (BaseEn.tabToFoundR_true_of_seat hnextX hpoX hcellX)
  have hstepX : State.step A₁ (Move.tabToFound x) = some (raiseSt A₁ x p) := by
    rw [step_tabToFound_splice hnextX hpoX]; rfl
  have hcX : (raiseSt A₁ x p).pileOfTop c = some a :=
    raiseSt_pileOfTop_ne hAwf hpoC hpa
  have hholdS1 : (raiseSt A₁ x p).pileHolding c = some a :=
    Drain.pileHolding_of_pileOfTop hS1wf hcX
  have hcpS1 : (raiseSt A₁ x p).canPlace c (Sum.inr z) = true := by
    rw [canPlace_inr_eq, hzE]; exact hfit
  have hpaA : (raiseSt A₁ x p).piles a = A₁.piles a := by
    rw [raiseSt_piles_apply, ite_eq_right (Ne.symm hpa)]
  have hnd : (A₁.piles a).faceUp.Nodup := runOK_nodup (hAwf.runOK_of a)
  have hbelow : below c (A₁.piles a).faceUp = chop (A₁.piles a).faceUp :=
    NoSelfKit.below_eq_chop_of_last hnd (pileOfTop_top hpoC).2
  have hfromS1 : fromCard c ((raiseSt A₁ x p).piles a).faceUp = [c] := by
    rw [hpaA]
    exact NoSelfKit.fromCard_singleton_of_last hnd (pileOfTop_top hpoC).2
  have hcellS1 : below c ((raiseSt A₁ x p).piles a).faceUp ≠ [] ∨
      (below c ((raiseSt A₁ x p).piles a).faceUp = [] ∧
        ((raiseSt A₁ x p).piles a).hidden = [] ∧ c.rank = Rank.king) := by
    rw [hpaA, hbelow]
    exact hcellC
  have hrevSL : reversibleAtW (raiseSt A₁ x p) (Move.tabToTab c (Sum.inr z)) :=
    (tabToTabR_iff_reversibleAtW hS1wf c (Sum.inr z)).mp
      (R12.tabToTabR_true_of hholdS1 hcpS1 hcellS1)
  have hstepSL : State.step (raiseSt A₁ x p) (Move.tabToTab c (Sum.inr z)) =
      some (CommuteStep.slideSt (raiseSt A₁ x p) c (Sum.inr z) a) := by
    rw [step_tabToTab_eq, hholdS1]
    simp only [hcpS1, ite_true, hfromS1, CommuteStep.slideSt]
  have hloc : ShufflePlayW A₁
      [Move.tabToFound x, Move.tabToTab c (Sum.inr z)] F := by
    rw [hF, hident]
    exact Walk.cons hrevX hstepX (Walk.cons hrevSL hstepSL (Walk.nil _))
  refine ⟨pre ++ ([Move.tabToFound x, Move.tabToTab c (Sum.inr z)] ++ (γ₂ ++ post)), ?_, ?_⟩
  · exact ShufflePlayW_append hpre (ShufflePlayW_append hloc htail)
  · rw [hρ]
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
    omega

/-! ## §5. Residual bookkeeping and the composition chain

`InrExposeResidual` splits by the *position* of the exposure event:

* the raise itself exposes `z` (or `γ₁ = []`): the pull is ready at the image,
  `BaseEn.shortens_of_readyAtImage` closes it (`inrExpose_ready_shortens`);
* the **head** of `γ₁` exposes `z`: `InrExpHead` (named; the raising head is
  §4, the sliding head is §3's identity plus the same bubble, the pull-type
  head — a pull of `z` itself off the foundation onto an empty pile — is the
  third shape);
* the exposure is **deeper**: `InrExpDeep` (named).

Then the `inr` half of `BaseEn.BaseEnabling` follows, and with the `inl`
residual so does the (gated, same-card) `MtnPr.SameCardRelocation`. -/

/-- The **head residual**: the first interior letter exposes `z`. -/
def InrExpHead : Prop :=
  ∀ (u v : State) (ρ pre γ₁' post : List Move) (c z : Card) (A B Aq : State) (q : Move),
    u.WF → ShufflePlayW u ρ v →
    ρ = pre ++ Move.tabToFound c :: (q :: γ₁') ++ Move.foundToTab c (Sum.inr z) :: post →
    ShufflePlayW u pre A →
    State.step A (Move.tabToFound c) = some B →
    State.step B q = some Aq →
    (∀ r ∈ (q :: γ₁'), SlideFwd.ReadSafe c r) →
    (∀ r ∈ (q :: γ₁'), MtnPr.SeatInert (Sum.inr z) r) →
    B.pileOfTop z = none →
    (∃ k, Aq.pileOfTop z = some k) →
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length

/-- The **deep residual**: the head of `γ₁` does not expose `z`. -/
def InrExpDeep : Prop :=
  ∀ (u v : State) (ρ pre γ₁' post : List Move) (c z : Card) (A B Aq : State) (q : Move),
    u.WF → ShufflePlayW u ρ v →
    ρ = pre ++ Move.tabToFound c :: (q :: γ₁') ++ Move.foundToTab c (Sum.inr z) :: post →
    ShufflePlayW u pre A →
    State.step A (Move.tabToFound c) = some B →
    State.step B q = some Aq →
    (∀ r ∈ (q :: γ₁'), SlideFwd.ReadSafe c r) →
    (∀ r ∈ (q :: γ₁'), MtnPr.SeatInert (Sum.inr z) r) →
    B.pileOfTop z = none →
    Aq.pileOfTop z = none →
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length

/-- **THE READY-AT-IMAGE CASE OF THE `inr` RESIDUAL.**  If the pull is legal at
the raise's image (in particular when the raise itself exposes `z`, or when
`γ₁ = []`), §1 of `Orig2/ForkBaseEnabling.lean` closes the play. -/
theorem inrExpose_ready_shortens
    {u v : State} {ρ pre γ post : List Move} {c z : Card} {A B : State}
    (huwf : u.WF) (hplay : ShufflePlayW u ρ v)
    (hρ : ρ = pre ++ Move.tabToFound c :: γ ++ Move.foundToTab c (Sum.inr z) :: post)
    (hpre : ShufflePlayW u pre A)
    (h1 : State.step A (Move.tabToFound c) = some B)
    (hread : ∀ q ∈ γ, SlideFwd.ReadSafe c q)
    (hseat : ∀ q ∈ γ, MtnPr.SeatInert (Sum.inr z) q)
    (hcp : B.canPlace c (Sum.inr z) = true) :
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length :=
  BaseEn.shortens_of_readyAtImage huwf hplay hρ hpre h1 hread hseat hcp

/-- **`InrExposeResidual` FROM HEAD + DEEP.**  Split `ρ` at the raise, look at
the raise's image `B` and at the state `Aq` after the head letter:

* `B.pileOfTop z ≠ none` (or `γ₁ = []`) ⇒ the pull is ready at `B`: §1;
* the head exposes `z` ⇒ `InrExpHead`;
* otherwise ⇒ `InrExpDeep` on the same play.

The live fit `canSitOn c z = true` is read off the pull's own legality in the
play. -/
theorem inrExposeResidual_of_head_deep
    (hhead : InrExpHead) (hdeep : InrExpDeep) : BaseEn.InrExposeResidual := by
  intro u v ρ pre γ₁ γ₂ post c z A E huwf hplay hρ hpre hread hseat hAz hEz
  -- the live fit comes from the pull that fires in the play
  have hfit : canSitOn c z = true := by
    have hρp : ρ = (pre ++ (Move.tabToFound c :: γ₁))
        ++ (Move.foundToTab c (Sum.inr z) :: post) := by
      simpa using hρ
    obtain ⟨Ep, -, hrestP⟩ :=
      ValleyElim.ShufflePlayW_split hplay (pre ++ (Move.tabToFound c :: γ₁))
        (Move.foundToTab c (Sum.inr z) :: post) hρp
    obtain ⟨Ep', -, hstepP, -⟩ := Bubble.walk_cons_inv hrestP
    obtain ⟨c', hft', hc'c, hcp', -⟩ := step_foundToTab_inv hstepP
    rw [hc'c] at hft'
    obtain ⟨k, -, hfit⟩ := canPlace_inr hcp'
    exact hfit
  -- split at the raise
  have hρ1 : ρ = pre ++ (Move.tabToFound c :: γ₁
      ++ Move.foundToTab c (Sum.inr z) :: post) := by
    simpa using hρ
  obtain ⟨A₀, hpre₀, hrest₀⟩ :=
    ValleyElim.ShufflePlayW_split hplay pre
      (Move.tabToFound c :: γ₁ ++ Move.foundToTab c (Sum.inr z) :: post) hρ1
  have hAA : A₀ = A := Option.some.inj ((Walk_run _ hpre₀).symm.trans (Walk_run _ hpre))
  rw [hAA] at hpre₀ hrest₀
  clear hAA
  obtain ⟨B, -, hstepB, hrestB⟩ := Bubble.walk_cons_inv hrest₀
  -- the raise itself may already expose `z`
  have hready : B.pileOfTop z ≠ none → B.canPlace c (Sum.inr z) = true := by
    intro hne
    cases hB : B.pileOfTop z with
    | none => exact absurd hB hne
    | some k' => rw [canPlace_inr_located hB]; exact hfit
  by_cases hBz : B.pileOfTop z = none
  · cases γ₁ with
    | nil =>
        -- `γ₁ = []`: the pull fires at the raise's image
        obtain ⟨Bp, -, hstepP, -⟩ := Bubble.walk_cons_inv hrestB
        obtain ⟨-, -, -, hcpB, -⟩ := step_foundToTab_inv hstepP
        exact inrExpose_ready_shortens huwf hplay hρ hpre hstepB
          (by simp) (by simp) hcpB
    | cons q γ₁' =>
        obtain ⟨Aq, -, hstepq, -⟩ := Bubble.walk_cons_inv hrestB
        cases hAq : Aq.pileOfTop z with
        | none =>
            exact hdeep u v ρ pre γ₁' post c z A B Aq q huwf hplay
              hρ hpre hstepB hstepq hread hseat hBz hAq
        | some k =>
            exact hhead u v ρ pre γ₁' post c z A B Aq q huwf hplay
              hρ hpre hstepB hstepq hread hseat hBz ⟨k, hAq⟩
  · exact inrExpose_ready_shortens huwf hplay hρ hpre hstepB hread hseat
      (hready hBz)

/-! ### The `inr` half of `BaseEnabling` -/

/-- **THE `inr` INSTANCE OF `BaseEnabling` FROM `InrExposeResidual`.**  In the
`BaseEnabling` context the pull is *not* legal at the raise's image, so `z` is
buried there (`B.pileOfTop z = none`: otherwise `canPlace` would be the live
fit, which the final pull forces).  Hence `InrExposeResidual` applies with
`A := B`. -/
theorem baseEnabling_inr_of_inrExpose (h : BaseEn.InrExposeResidual) :
    ∀ (u v : State) (ρ pre γ post : List Move) (c z : Card) (A B : State),
      u.WF → ShufflePlayW u ρ v →
      ρ = pre ++ Move.tabToFound c :: γ ++ Move.foundToTab c (Sum.inr z) :: post →
      ShufflePlayW u pre A →
      State.step A (Move.tabToFound c) = some B →
      (∀ q ∈ γ, SlideFwd.ReadSafe c q) →
      (∀ q ∈ γ, MtnPr.SeatInert (Sum.inr z) q) →
      B.canPlace c (Sum.inr z) = false →
      ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length := by
  intro u v ρ pre γ post c z A B huwf hplay hρ hpre hstep hread hseat hno
  -- the pull's own legality in the play
  have hρa : ρ = (pre ++ (Move.tabToFound c :: γ))
      ++ (Move.foundToTab c (Sum.inr z) :: post) := by
    simpa using hρ
  obtain ⟨Ep, hpreEp, hrestP⟩ :=
    ValleyElim.ShufflePlayW_split hplay (pre ++ (Move.tabToFound c :: γ)) _ hρa
  obtain ⟨Ep', hrevP, hstepP, -⟩ := Bubble.walk_cons_inv hrestP
  obtain ⟨c', hft', hc'c, hcp', -⟩ := step_foundToTab_inv hstepP
  rw [hc'c] at hft'
  obtain ⟨k, hk, hfit⟩ := canPlace_inr hcp'
  -- `z` is buried at the raise's image
  have hBz : B.pileOfTop z = none := by
    cases hB : B.pileOfTop z with
    | none => rfl
    | some k' =>
        rw [canPlace_inr_located hB] at hno
        exact absurd hfit (by rw [hno]; simp)
  -- hence it is buried at the raise's origin too
  have hAwf : A.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  obtain ⟨-, a, hpoC, -⟩ := step_tabToFound_inv hstep
  have hAz : A.pileOfTop z = none := by
    cases hA : A.pileOfTop z with
    | none => rfl
    | some k'' =>
        have hzc : z ≠ c := ne_of_canSitOn hfit
        have hk''a : k'' ≠ a := pileOfTop_ne_of_ne hAwf hA hpoC hzc
        have hBeq : B = raiseSt A c a := by
          have hs := step_tabToFound_splice (step_tabToFound_inv hstep).1 hpoC
          exact Option.some.inj (hstep.symm.trans hs)
        have hcontra : B.pileOfTop z = some k'' := by
          rw [hBeq]
          exact raiseSt_pileOfTop_ne hAwf hA (Ne.symm hk''a)
        rw [hcontra] at hBz
        exact absurd hBz (by simp)
  exact h u v ρ pre γ [] post c z A Ep huwf hplay hρ hpre
    hread hseat hAz ⟨k, hk⟩

/-- **`BaseEnabling` FROM ITS `inl` RESIDUAL + `InrExposeResidual`.** -/
theorem baseEnabling_of_inl_and_inr
    (hinl : ∀ (u v : State) (ρ pre γ post : List Move) (c : Card) (a : Anchor)
        (A B : State),
      u.WF → ShufflePlayW u ρ v →
      ρ = pre ++ Move.tabToFound c :: γ ++ Move.foundToTab c (Sum.inl a) :: post →
      ShufflePlayW u pre A →
      State.step A (Move.tabToFound c) = some B →
      (∀ q ∈ γ, SlideFwd.ReadSafe c q) →
      (∀ q ∈ γ, MtnPr.SeatInert (Sum.inl a) q) →
      B.canPlace c (Sum.inl a) = false →
      ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length)
    (hinr : BaseEn.InrExposeResidual) : BaseEn.BaseEnabling := by
  intro u v ρ pre γ post c b A B huwf hplay hρ hpre hstep hread hseat hno
  cases b with
  | inl a =>
      exact hinl u v ρ pre γ post c a A B huwf hplay hρ hpre hstep hread hseat hno
  | inr z =>
      exact baseEnabling_inr_of_inrExpose hinr u v ρ pre γ post c z A B
        huwf hplay hρ hpre hstep hread hseat hno

/-- **THE CHAIN, GATED, SAME-CARD.**  `MtnPr.SameCardRelocation` from the `inl`
buffer residual + `InrExposeResidual`, through `BaseEnabling`
(`BaseEn.sameCardRelocation_of_baseEnabling`). -/
theorem sameCardRelocation_of_inl_and_inr
    (hinl : ∀ (u v : State) (ρ pre γ post : List Move) (c : Card) (a : Anchor)
        (A B : State),
      u.WF → ShufflePlayW u ρ v →
      ρ = pre ++ Move.tabToFound c :: γ ++ Move.foundToTab c (Sum.inl a) :: post →
      ShufflePlayW u pre A →
      State.step A (Move.tabToFound c) = some B →
      (∀ q ∈ γ, SlideFwd.ReadSafe c q) →
      (∀ q ∈ γ, MtnPr.SeatInert (Sum.inl a) q) →
      B.canPlace c (Sum.inl a) = false →
      ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length)
    (hinr : BaseEn.InrExposeResidual) : MtnPr.SameCardRelocation :=
  BaseEn.sameCardRelocation_of_baseEnabling (baseEnabling_of_inl_and_inr hinl hinr)

end InrExp

#print axioms InrExp.pileOfTop_ne_of_ne
#print axioms InrExp.ne_of_canSitOn
#print axioms InrExp.pullSt_raiseSt_eq_slideSt
#print axioms InrExp.raise_raise_pull_eq_raise_slide_inr
#print axioms InrExp.raise_slide_pull_eq_slide_slide_inr
#print axioms InrExp.inr_expose_raise_adjacent_shortens
#print axioms InrExp.inrExpose_ready_shortens
#print axioms InrExp.inrExposeResidual_of_head_deep
#print axioms InrExp.baseEnabling_inr_of_inrExpose
#print axioms InrExp.baseEnabling_of_inl_and_inr
#print axioms InrExp.sameCardRelocation_of_inl_and_inr
