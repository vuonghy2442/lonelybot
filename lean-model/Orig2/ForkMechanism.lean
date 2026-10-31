import Orig2.ForkSplitResidual

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false

/-!
# Orig2/ForkMechanism — the mechanism at the valley bottom

Read-only on the repository.  Zero `sorry`, zero `Classical.choice`, zero
`native_decide`; axiom audit at the tail.

## What this file proves

* `mover_seat_twin_of_slide_into_card` — **the twin-source law**: a
  reversible slide `tabToTab x (inr c)` has its mover `x` seated directly
  on `c.twin` before the slide.  Unconditional at `WF`; no minimality.
* `seat_eq_of_free_play_no_mover` — a free play that never slides `x`
  leaves `x`'s seat alone (`tfc_seat_point_edit` inducted).
* `mover_or_last_mover` — the last-mover decomposition of a free play.
* `coverEvent_of_block` / `block_of_coverEvent` / `coverEvent_iff_block` —
  **the mechanism is exactly `SplitBlock`**: at the pull landing the free
  tail carries the twin-source cover slide iff `c` is blocked at the
  bottom.  (Existence is the residual; the twin-source half is free.)
* `twinLivePair_landing_iff` — the live set is invariant under the free
  tail, so `SplitLivePair` is exactly a **landing** statement.
* `twinLivePair_of_landing` — with the pull's rung pin, the landing
  residual `LandingLivePair` ("no third-suit live card, and `c.twin`
  live") is exactly `TwinLivePair B c`.
* `mechanism_yields` — the two landing-level clauses imply, at the
  bottom, `d = c.twin`, the live set `{c, c.twin}`, `¬ CanRaise F c`,
  and the rank floor.
* `splitFloor_of_mechanismResidual` — the single residual
  `MechanismResidual` implies `SplitFloor` (and the corrected residual).
-/

namespace Mech

/-! ## §1. Seats and the twin-source law -/

/-- **THE TWIN-SOURCE SLIDE.**  At a `WF` state, a reversible slide
`tabToTab x (inr c)` (the mover `x` lands directly on the card `c`)
has its mover sitting directly on `c.twin` before the slide.

Why: `x` fits on `c` (`canPlace`), so `rank(x) + 1 = rank(c)` and
`color(x) ≠ color(c)`.  The card `y` directly beneath `x` fits `x`, hence
`rank(y) = rank(c)` and `color(y) = color(c)`; so `y ∈ {c, c.twin}`.
But `y = c` would put `x` above `c` while `c` still tops a pile (the
slide's own licence), impossible.  Hence `y = c.twin`. -/
theorem mover_seat_twin_of_slide_into_card {st z : State} {x c : Card}
    (hwf : st.WF)
    (hstep : State.step st (Move.tabToTab x (Sum.inr c)) = some z)
    (hrev : reversibleAtW st (Move.tabToTab x (Sum.inr c))) :
    seatOf st x = some (Sum.inr c.twin) := by
  have hcell : tabToTabR st x (Sum.inr c) = true :=
    (tabToTabR_iff_reversibleAtW hwf x (Sum.inr c)).mpr hrev
  obtain ⟨a, hhold, hcp, hbelow⟩ := tfc_tabToTabR_inv hcell
  have hloc : st.pileOfTop c ≠ none := by
    intro hk
    simp [State.canPlace, hk] at hcp
  obtain ⟨k, hk⟩ := option_some_of_ne_none hloc
  have hfitc : canSitOn x c = true := by
    rw [canPlace_inr_located hk] at hcp
    exact hcp
  have hbelow_ne : below x (st.piles a).faceUp ≠ [] := by
    rcases hbelow with hne | ⟨h0, -, hking⟩
    · exact hne
    · exfalso
      have h1 := ((canSitOn_eq x c).mp hfitc).1
      have h2 : x.rank.toIdx = 12 := by rw [hking]; rfl
      have h3 := Rank.toIdx_lt c.rank
      omega
  obtain ⟨y, hy⟩ := lastOf_exists hbelow_ne
  have hseat : seatOf st x = some (Sum.inr y) := tfc_seatOf_inr_intro hhold hy
  have hfity : canSitOn x y = true := (tfc_seat_parent hwf hhold hy).1
  have htopY : st.pileOfTop y = none := (tfc_seat_parent hwf hhold hy).2
  rcases tfc_fitting_parent (c := x) hfity hfitc with hyc | hyc
  · rw [hyc] at htopY hseat
    rw [hk] at htopY
    exact absurd htopY (by simp)
  · rw [hyc] at hseat
    exact hseat

/-- A reversible slide that does not move `q` leaves `q`'s seat alone
(the one-point edit row `tfc_seat_point_edit`). -/
theorem seat_of_nonmover_slide {st z : State} {y : Card} {base : Base}
    (hwf : st.WF) (hstep : State.step st (Move.tabToTab y base) = some z)
    (hrev : reversibleAtW st (Move.tabToTab y base)) {q : Card} (hq : q ≠ y) :
    seatOf z q = seatOf st q := by
  rw [tfc_seat_point_edit hwf hstep hrev q, ite_eq_right hq]

/-- `NoMover x ρ`: no letter of `ρ` slides the card `x`. -/
def NoMover (x : Card) (ρ : List Move) : Prop :=
  ∀ m ∈ ρ, ∀ b : Base, m ≠ Move.tabToTab x b

/-- **SEAT PERSISTENCE.**  A free play with no `x`-mover keeps `x`'s
seat. -/
theorem seat_eq_of_free_play_no_mover {B F : State} {post : List Move} {x : Card}
    (hplay : ShufflePlayW B post F)
    (hfree : ∀ m ∈ post, ValleyElim.FreeMove m)
    (hno : NoMover x post) :
    B.WF → seatOf F x = seatOf B x := by
  induction hplay with
  | nil st => intro _; rfl
  | @cons st s1 W m ρ hrev hstep hrest ih =>
      intro hwf
      have hfreeTail : ∀ y ∈ ρ, ValleyElim.FreeMove y :=
        fun y hy => hfree y (List.mem_cons_of_mem m hy)
      have hnoTail : NoMover x ρ :=
        fun y hy b => hno y (List.mem_cons_of_mem m hy) b
      have hwfS : s1.WF := step_wf hwf hstep
      have htail : seatOf W x = seatOf s1 x := ih hfreeTail hnoTail hwfS
      have hhead : seatOf s1 x = seatOf st x := by
        rcases hfree m (List.mem_cons_self ..) with hm | ⟨y, base, hm⟩
        · subst hm
          exact seatOf_congr_piles (stepDraw_piles hstep) x
        · subst hm
          have hxy : x ≠ y := by
            intro hxy
            exact hno (Move.tabToTab y base) (List.mem_cons_self ..) base
              (by rw [hxy])
          exact seat_of_nonmover_slide hwf hstep hrev hxy
      exact htail.trans hhead

/-- **THE LAST-MOVER DECOMPOSITION (scan form).**  A free witness play is
either `x`-mover-free, or it has a last `x`-mover: a decomposition whose
suffix contains no `x`-mover, with the seat of `x` frozen from the mover's
landing to the end. -/
theorem mover_or_last_mover {B F : State} {post : List Move} {x : Card}
    (hwf : B.WF)
    (hplay : ShufflePlayW B post F)
    (hfree : ∀ m ∈ post, ValleyElim.FreeMove m) :
    NoMover x post ∨
      ∃ (s1 s2 : List Move) (A Z : State) (b : Base),
        post = s1 ++ Move.tabToTab x b :: s2 ∧
        ShufflePlayW B s1 A ∧
        reversibleAtW A (Move.tabToTab x b) ∧
        State.step A (Move.tabToTab x b) = some Z ∧
        ShufflePlayW Z s2 F ∧
        NoMover x s2 ∧
        seatOf Z x = seatOf F x := by
  induction hplay with
  | nil st => exact Or.inl (fun m hm => absurd hm (by simp))
  | @cons st s1 W m ρ hrev hstep hrest ih =>
      have hfreeTail : ∀ y ∈ ρ, ValleyElim.FreeMove y :=
        fun y hy => hfree y (List.mem_cons_of_mem m hy)
      rcases ih (step_wf hwf hstep) hfreeTail with hno | ⟨s1', s2', A, Z, b, heq, hplay1, hrev1, hstep1, hplay2, hno2, hseat⟩
      · rcases hfree m (List.mem_cons_self ..) with hm | ⟨y, base, hm⟩
        · subst hm
          refine Or.inl (fun m' hm' b' => ?_)
          rcases List.mem_cons.mp hm' with rfl | hm''
          · exact fun hcon => by cases hcon
          · exact hno m' hm'' b'
        · subst hm
          by_cases hyx : y = x
          · subst hyx
            refine Or.inr ⟨[], ρ, st, s1, base, ?_, ?_, hrev, hstep, hrest, hno, ?_⟩
            · rw [List.nil_append]
            · exact Walk.nil st
            · exact (seat_eq_of_free_play_no_mover hrest hfreeTail hno
                (step_wf hwf hstep)).symm
          · refine Or.inl (fun m' hm' b' => ?_)
            rcases List.mem_cons.mp hm' with rfl | hm''
            · exact fun hcon => hyx (by cases hcon; rfl)
            · exact hno m' hm'' b'
      · refine Or.inr ⟨m :: s1', s2', A, Z, b, ?_, ?_, hrev1, hstep1, hplay2, hno2, hseat⟩
        · rw [List.cons_append, heq]
        · exact Walk.cons hrev hstep hplay1

/-! ## §2. The landing -/

/-- **THE LANDING RUNG PIN.**  After the pull of `c`, the rung of `c.suit`
is exactly `c`'s rank index. -/
theorem rungAt_landing_eq {A' B : State} {c : Card} {b : Base}
    (hA' : A'.WF) (hstep : State.step A' (Move.foundToTab c b) = some B) :
    rungAt B c.suit = c.rank.toIdx := by
  obtain ⟨c', htop, hc', -, -⟩ := step_foundToTab_inv hstep
  rw [hc'] at htop
  have hidx : c.rank.toIdx + 1 = rungAt A' c.suit :=
    SatDifferCensus.foundTop_rank_succ hA' htop
  have h := rungAt_foundToTab hstep c.suit
  rw [ite_eq_left rfl] at h
  omega

/-- **A VANILLA-RAISABLE CARD IS NOT COVERED.** -/
theorem not_covered_of_canRaise {st : State} {c : Card}
    (hwf : st.WF) (hcan : CanRaise st c) : ¬ CoveredAt st c :=
  fun hcov => not_canRaise_of_covered hwf hcov hcan

/-! ## §3. The cover-slide event -/

/-- **`CoverEvent B F post c`** — the free tail `post` (a witness play
`B → F`) contains a slide whose mover `x` lands directly on `c`, and
before the slide `x` sat directly on `c.twin`; afterwards `x` stays on
`c` down to `F`.  This is the probe's twin-source cover slide, in exact
form. -/
def CoverEvent (B F : State) (post : List Move) (c : Card) : Prop :=
  ∃ (x : Card) (s1 s2 : List Move) (A Z : State),
    post = s1 ++ Move.tabToTab x (Sum.inr c) :: s2 ∧
    ShufflePlayW B s1 A ∧
    seatOf A x = some (Sum.inr c.twin) ∧
    reversibleAtW A (Move.tabToTab x (Sum.inr c)) ∧
    State.step A (Move.tabToTab x (Sum.inr c)) = some Z ∧
    ShufflePlayW Z s2 F ∧
    seatOf F x = some (Sum.inr c)

/-- **THE MECHANISM EXISTS FROM THE BLOCK.**  If `c` is blocked at the
bottom `F` and S-live there, then the last mover of the cover card in
the free tail is a twin-source slide.  (No minimality used.) -/
theorem coverEvent_of_block {B F : State} {post : List Move} {c : Card}
    (hB : B.WF) (hplay : ShufflePlayW B post F)
    (hfree : ∀ m ∈ post, ValleyElim.FreeMove m)
    (hBcan : CanRaise B c) (hS : CanRaiseS F c) (hblock : ¬ CanRaise F c) :
    CoverEvent B F post c := by
  have hF : F.WF := SatDifferCensus.ShufflePlayW.wf_end hplay hB
  obtain ⟨x, hxF⟩ := covered_of_live_not_canRaise hF hS hblock
  have hchg : seatOf B x ≠ seatOf F x := by
    intro heq
    exact (not_covered_of_canRaise hB hBcan) ⟨x, heq.trans hxF⟩
  rcases mover_or_last_mover hB hplay hfree with hno | ⟨s1, s2, A, Z, base, heq, hplay1, hrev1, hstep1, hplay2, hno2, hseat⟩
  · exact absurd (seat_eq_of_free_play_no_mover hplay hfree hno hB).symm hchg
  · have hAwf : A.WF := SatDifferCensus.ShufflePlayW.wf_end hplay1 hB
    have hZ : seatOf Z x = some (Sum.inr c) := hseat.trans hxF
    have hZb : seatOf Z x = some base := by
      rw [tfc_seat_point_edit hAwf hstep1 hrev1 x, ite_eq_left rfl]
    have hbase : base = Sum.inr c := Option.some.inj (hZb.symm.trans hZ)
    subst hbase
    have hsrc : seatOf A x = some (Sum.inr c.twin) :=
      mover_seat_twin_of_slide_into_card hAwf hstep1 hrev1
    exact ⟨x, s1, s2, A, Z, heq, hplay1, hsrc, hrev1, hstep1, hplay2, hxF⟩

/-- **THE MECHANISM IMPLIES THE BLOCK.**  The cover slide covers `c`
at the bottom, so `c` is not vanilla-raisable there. -/
theorem block_of_coverEvent {B F : State} {post : List Move} {c : Card}
    (hF : F.WF) (h : CoverEvent B F post c) : ¬ CanRaise F c := by
  obtain ⟨x, s1, s2, A, Z, -, -, -, -, -, -, hstay⟩ := h
  exact not_canRaise_of_covered hF ⟨x, hstay⟩

/-- **THE EXACT EQUIVALENCE.**  At a pull landing `B` (where `c` is
vanilla-raisable), the free witness tail `B → F`, with `c` S-live at
`F`, contains the twin-source cover slide **iff** `c` is blocked at `F`.
The mechanism's *twin-source* half is unconditional; its *existence* is
exactly `SplitBlock`. -/
theorem coverEvent_iff_block {B F : State} {post : List Move} {c : Card}
    (hB : B.WF) (hplay : ShufflePlayW B post F)
    (hfree : ∀ m ∈ post, ValleyElim.FreeMove m)
    (hBcan : CanRaise B c) (hS : CanRaiseS F c) :
    CoverEvent B F post c ↔ ¬ CanRaise F c := by
  have hF : F.WF := SatDifferCensus.ShufflePlayW.wf_end hplay hB
  exact ⟨fun h => block_of_coverEvent hF h,
    fun hblock => coverEvent_of_block hB hplay hfree hBcan hS hblock⟩

/-! ## §4. The live set -/

/-- Free witness plays preserve the S-live set. -/
theorem canRaiseS_landing_iff {B F : State} {post : List Move}
    (hB : B.WF) (hplay : ShufflePlayW B post F)
    (hfree : ∀ m ∈ post, ValleyElim.FreeMove m) (e : Card) :
    CanRaiseS B e ↔ CanRaiseS F e :=
  Bridge.canRaiseS_of_free_play_iff hplay hfree hB e

/-- **LIVE-SET TRANSPORT.**  `TwinLivePair` is invariant under the free
tail. -/
theorem twinLivePair_landing_iff {B F : State} {post : List Move} {x : Card}
    (hB : B.WF) (hplay : ShufflePlayW B post F)
    (hfree : ∀ m ∈ post, ValleyElim.FreeMove m) :
    TwinLivePair B x ↔ TwinLivePair F x := by
  unfold TwinLivePair
  constructor
  · intro h e
    rw [← canRaiseS_landing_iff hB hplay hfree e]
    exact h e
  · intro h e
    rw [canRaiseS_landing_iff hB hplay hfree e]
    exact h e

/-- A live card at the landing whose suit is `c.suit` is `c`. -/
theorem live_eq_of_suit_left {B : State} {c e : Card}
    (hrung : rungAt B c.suit = c.rank.toIdx)
    (he : CanRaiseS B e) (hsuit : e.suit = c.suit) : e = c := by
  have h := canRaiseS_rung he
  rw [hsuit, hrung] at h
  have hrank : e.rank = c.rank := Rank.toIdx_inj h.symm
  cases e with
  | mk es er =>
    cases c with
    | mk cs cr =>
      simp only at hsuit hrank
      rw [hsuit, hrank]

/-- A live card at the landing whose suit is `c.twin.suit` is `c.twin`. -/
theorem live_eq_of_suit_twin {B : State} {c e : Card}
    (hrungT : rungAt B c.twin.suit = c.rank.toIdx)
    (he : CanRaiseS B e) (hsuit : e.suit = c.twin.suit) : e = c.twin := by
  have h := canRaiseS_rung he
  rw [hsuit, hrungT] at h
  have hrank : e.rank = c.twin.rank := Rank.toIdx_inj h.symm
  have hrank' : e.rank = c.rank := hrank
  cases e with
  | mk es er =>
    cases c with
    | mk cs cr =>
      simp only [Card.twin, Card.mk.injEq] at hsuit hrank' ⊢
      exact ⟨hsuit, hrank'⟩

/-- **`LandingLivePair B c`** — the landing's live set is confined to the
two suits of the cover card (`c` and `c.twin`), and `c.twin` is live.
This is the exact "no third live card" residual, read at the pull
landing instead of the bottom. -/
def LandingLivePair (B : State) (c : Card) : Prop :=
  CanRaiseS B c.twin ∧
    (∀ e, CanRaiseS B e → e.suit = c.suit ∨ e.suit = c.twin.suit)

/-- **THE PAIR-SUIT PIN.**  With both pair-suit rungs at `c`'s rank, the
landing live set being confined to the pair suits *is* `TwinLivePair`. -/
theorem twinLivePair_of_landing {B : State} {c : Card}
    (hBc : CanRaise B c)
    (hrungC : rungAt B c.suit = c.rank.toIdx)
    (h : LandingLivePair B c) : TwinLivePair B c := by
  have hrongT : rungAt B c.twin.suit = c.rank.toIdx := by
    rw [canRaiseS_rung h.1, Card.twin_rank]
  intro e
  constructor
  · intro he
    rcases h.2 e he with hs | hs
    · exact Or.inl (live_eq_of_suit_left hrungC he hs)
    · exact Or.inr (live_eq_of_suit_twin hrongT he hs)
  · intro hmem
    rcases hmem with h1 | h1
    · rw [h1]; exact CanRaiseS.now c hBc
    · rw [h1]; exact h.1

/-- `TwinLivePair` transfers across an equality of the pair's twin. -/
theorem twinLivePair_of_eq_twin {F : State} {c d : Card}
    (hl : TwinLivePair F c) (hd : d = c.twin) : TwinLivePair F d := by
  subst hd
  intro e
  rw [hl e, card_twin_twin]
  constructor
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl h

/-- The raise card at the bottom is the pull card's twin, given the live
pair at `c` and the block. -/
theorem raise_eq_twin_of_livePair_block {F : State} {c d : Card}
    (hl : TwinLivePair F c) (hblock : ¬ CanRaise F c) (hcanD : CanRaise F d) :
    d = c.twin := by
  have hSd : CanRaiseS F d := CanRaiseS.now d hcanD
  rcases (hl d).mp hSd with h | h
  · exact absurd (h ▸ hcanD) hblock
  · exact h

/-- **THE RANK FLOOR FROM THE LIVE PAIR.**  With `d = c.twin` and the
bottom's live set exactly `{d, d.twin}`, every live card has rank
`c.rank`. -/
theorem floor_of_livePair_twin {F : State} {c d : Card}
    (hl : TwinLivePair F d) (hd : d = c.twin) :
    ∀ e, CanRaiseS F e → c.rank.toIdx ≤ e.rank.toIdx := by
  have hdrank : d.rank.toIdx = c.rank.toIdx := by rw [hd, Card.twin_rank]
  intro e he
  rcases (hl e).mp he with h | h
  · rw [h]; omega
  · rw [h, Card.twin_rank]; omega

/-! ## §5. The residual and the assembly -/

/-- **`SplitMechanism`** — the mechanism at one split: the pull landing
`B` carries the landing live pair, and the free tail carries the
twin-source cover slide.  This is the TWO-clause residual, both clauses
read at `B`/`post` rather than at the bottom:
`LandingLivePair` (= `SplitLivePair`) and `CoverEvent` (= `SplitBlock`). -/
def SplitMechanism (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move) : Prop :=
  ∃ A' B : State,
    ShufflePlayW u pre A' ∧
    State.step A' (Move.foundToTab c b) = some B ∧
    ShufflePlayW B post F ∧
    LandingLivePair B c ∧
    CoverEvent B F post c

/-- **THE MECHANISM YIELDS BOTH CLAUSES.**  From `SplitHyp` and
`SplitMechanism`, the bottom has `d = c.twin`, the live set `{c, c.twin}`
(`TwinLivePair F d`, i.e. `SplitLivePair` at this split) and
`¬ CanRaise F c` (`SplitBlock`), plus the rank floor. -/
theorem mechanism_yields {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hm : SplitMechanism u v ρ F left right c d b pre post tail) :
    d = c.twin ∧ TwinLivePair F d ∧ ¬ CanRaise F c ∧
      (∀ e, CanRaiseS F e → c.rank.toIdx ≤ e.rank.toIdx) := by
  have hgreen := SplitKit.splitHyp_green h
  obtain ⟨hF, hSc, hcanD, -⟩ := hgreen
  obtain ⟨huwf, -, -, -, -, -, -, hleft, -, hshape, hfree, -⟩ := h
  obtain ⟨A', B, hpre, hstepP, hpost, hland, hcov⟩ := hm
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  have hB : B.WF := step_wf hA' hstepP
  have hcanB : CanRaise B c := ValleyStep.pull_card_canRaise hA' hstepP
  have hrungC : rungAt B c.suit = c.rank.toIdx := rungAt_landing_eq hA' hstepP
  have hliveB : TwinLivePair B c := twinLivePair_of_landing hcanB hrungC hland
  have hliveF : TwinLivePair F c := (twinLivePair_landing_iff hB hpost hfree).mp hliveB
  have hblock : ¬ CanRaise F c := block_of_coverEvent hF hcov
  have hd : d = c.twin := raise_eq_twin_of_livePair_block hliveF hblock hcanD
  have hliveFd : TwinLivePair F d := twinLivePair_of_eq_twin hliveF hd
  exact ⟨hd, hliveFd, hblock, floor_of_livePair_twin hliveFd hd⟩

/-- **`MechanismResidual`** — the single named residual: every split
carries `SplitMechanism`. -/
def MechanismResidual : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
      SplitMechanism u v ρ F left right c d b pre post tail

/-- `MechanismResidual` gives `SplitLivePair`. -/
theorem splitLivePair_of_mechanismResidual (h : MechanismResidual) :
    SplitKit.SplitLivePair := by
  intro u v ρ F left right c d b pre post tail hh
  exact (mechanism_yields hh (h u v ρ F left right c d b pre post tail hh)).2.1

/-- `MechanismResidual` gives `SplitBlock`. -/
theorem splitBlock_of_mechanismResidual (h : MechanismResidual) :
    SplitKit.SplitBlock := by
  intro u v ρ F left right c d b pre post tail hh
  exact (mechanism_yields hh (h u v ρ F left right c d b pre post tail hh)).2.2.1

/-- `MechanismResidual` gives `SplitFloor`. -/
theorem splitFloor_of_mechanismResidual (h : MechanismResidual) :
    SplitKit.SplitFloor := by
  intro u v ρ F left right c d b pre post tail hh
  exact (mechanism_yields hh (h u v ρ F left right c d b pre post tail hh)).2.2.2

/-- `MechanismResidual` gives the corrected residual. -/
theorem splitResidualData_of_mechanismResidual (h : MechanismResidual) :
    SplitKit.SplitResidualData :=
  SplitKit.splitResidualData_of_livePair_block
    (splitLivePair_of_mechanismResidual h) (splitBlock_of_mechanismResidual h)

/-! ## §6. The identity-pair rule (W3) and the shortest split

`Temp/FullCancel_Report.md` §5.1: the complete local cancellation rule deletes
an adjacent pair `m1 ; m2` whenever `step (step s m1) m2 = s`.  The row below
formalises it for witness plays.  Its consequence is the *minimality
discriminator*: a shortest split contains no adjacent identity pair anywhere
in its free tail. -/

/-- **IDENTITY-PAIR DELETION (W3).**  An adjacent pair whose composite is the
identity on states deletes from a witness play, strictly shortening it. -/
theorem identity_pair_shortens {u v : State} {α β : List Move} {m1 m2 : Move}
    (huwf : u.WF) (hplay : ShufflePlayW u (α ++ m1 :: m2 :: β) v)
    (hid : ∀ (A A' : State), ShufflePlayW u α A →
        State.step A m1 = some A' → State.step A' m2 = some A) :
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧
      ρ'.length < (α ++ m1 :: m2 :: β).length := by
  obtain ⟨A, hα, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hplay α (m1 :: m2 :: β) rfl
  cases hrest with
  | cons hrev1 hstep1 hrest1 =>
    rename_i A1
    cases hrest1 with
    | cons hrev2 hstep2 hβ =>
      rename_i A2
      have hback : State.step A1 m2 = some A := hid A A1 hα hstep1
      have hA2 : A2 = A := Option.some.inj (hstep2.symm.trans hback)
      subst hA2
      refine ⟨α ++ β, ShufflePlayW_append hα hβ, ?_⟩
      simp only [List.length_append, List.length_cons]
      omega

/-- **NO ADJACENT IDENTITY PAIR IN A SHORTEST SPLIT'S FREE TAIL.**  This is
the contrapositive of `identity_pair_shortens` on the split's minimality. -/
theorem split_no_free_tail_identity {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    {s1 s2 : List Move} {m1 m2 : Move}
    (hpost : post = s1 ++ m1 :: m2 :: s2)
    (hid : ∀ (A A' : State),
        ShufflePlayW u (pre ++ Move.foundToTab c b :: s1) A →
        State.step A m1 = some A' → State.step A' m2 = some A) :
    False := by
  obtain ⟨huwf, -, -, hplay, -, hmin, hρ, hleft, -, hshape, hfree, -⟩ := h
  have heq : ρ =
      (pre ++ Move.foundToTab c b :: s1) ++ m1 :: m2 :: (s2 ++ right) := by
    rw [hρ, hshape, hpost]
    simp only [List.append_assoc, List.cons_append]
  rw [heq] at hplay hmin
  obtain ⟨ρ', hρ', hlen⟩ := identity_pair_shortens huwf hplay hid
  exact absurd hlen (Nat.not_lt.mpr (hmin ρ' hρ'))

#print axioms Mech.mover_seat_twin_of_slide_into_card
#print axioms Mech.seat_of_nonmover_slide
#print axioms Mech.seat_eq_of_free_play_no_mover
#print axioms Mech.mover_or_last_mover
#print axioms Mech.rungAt_landing_eq
#print axioms Mech.not_covered_of_canRaise
#print axioms Mech.coverEvent_of_block
#print axioms Mech.block_of_coverEvent
#print axioms Mech.coverEvent_iff_block
#print axioms Mech.canRaiseS_landing_iff
#print axioms Mech.twinLivePair_landing_iff
#print axioms Mech.live_eq_of_suit_left
#print axioms Mech.live_eq_of_suit_twin
#print axioms Mech.twinLivePair_of_landing
#print axioms Mech.twinLivePair_of_eq_twin
#print axioms Mech.raise_eq_twin_of_livePair_block
#print axioms Mech.floor_of_livePair_twin
#print axioms Mech.mechanism_yields
#print axioms Mech.splitLivePair_of_mechanismResidual
#print axioms Mech.splitBlock_of_mechanismResidual
#print axioms Mech.splitFloor_of_mechanismResidual
#print axioms Mech.splitResidualData_of_mechanismResidual
#print axioms Mech.identity_pair_shortens
#print axioms Mech.split_no_free_tail_identity

/-- **THE FULL CHAIN FROM THE MECHANISM.**  The two local landing facts
(`LandingLivePair` + `CoverEvent`, bundled as `MechanismResidual`) plus the
choice-free shortest-play interface give `SatDifferForkWF`; the drain is
already discharged. -/
theorem satDifferForkWF_of_mechanismResidual_drainClosed
    (h : MechanismResidual) (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  SplitKit.satDifferForkWF_of_splitResidualData_drainClosed
    (splitResidualData_of_mechanismResidual h) hmin

#print axioms Mech.satDifferForkWF_of_mechanismResidual_drainClosed
end Mech
