import Orig2.ForkTailCover
import Orig2.ForkMountain
import Orig2.ForkLedger
import Orig2.ForkLivePair
import Orig2.ForkLandingLocal
import Orig2.ForkMechanism
import Orig2.ForkMinCross
import Orig2.ForkElim
import Orig2.ForkNonfork
import Orig2.ForkSafeTransport
import Orig2.FreeOrbit
import Orig2.Position

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Temp/BlockMin_Core — the fibre pin: `SplitBlock` reduced past the bottom

READ-ONLY scratch card.  No source file is modified; nothing is committed.
Zero `sorry`, zero `Classical.choice`, zero `native_decide`; axiom battery at
the tail.

## What this card does

`SplitKit.SplitBlock` asks `¬ CanRaise F c` at the play's own valley bottom `F`.
The relaxation in the brief replaces that with the **existential fibre pin**: it
suffices that *some* representative of the bottom's position (same witness
orbit, same rung vector) blocks one twin, because `SatDifferForkWF` only asks
for a fork state in `u`'s orbit.

1. **§1 the static cover slide.**  `BlockerReady F y` is the concrete
   arrangement-level datum for moving a blocker onto `y` *inside the cargo
   fibre*: a card `x` that fits `y` (`canSitOn x y`), sits face-up in a pile with
   company beneath it (so the slide is reversible — the `below ≠ []` cell of
   `tabToTabR`), and `y` is a pile top.  `exists_blocked_representative`
   performs the slide, keeps the rung vector, and lands where `y` is covered,
   hence not vanilla-raisable.

2. **§2 the fibre dichotomy.**  `FibreBlockData F` says: at a `WF` state whose
   S-live set is the twin pair of `x` (the position's *spectrum*, a position
   invariant by `FreeOrbit.canRaiseS_orbit_rung`), one twin is covered or a
   blocker is ready for one of them.

3. **§3 the sharpening — only the BOTH-RAISABLE case is left.**
   `blockerReady_of_covered_other` shows that if one twin is covered by `u`,
   then `u` fits the *other* twin too (twins share rank and colour), so the same
   covering card is a ready blocker for it.  Hence `FibreBlockData` follows from
   `BothRaisableBlock F`, which is consulted **only** when both twins are
   vanilla-raisable.  This is the gadget case of `Temp/TwinPin_Report.md`; the
   reduction is kernel-checked.

4. **§4 the gated residual and the relaxed target.**
   `BottomBothRaisableBlock` is the residual at the minimal bottom;
   `dipPin_of_bothRaisable` turns `SplitLivePair` + the residual into `DipPin`
   (a `ForkWitness` at a same-position representative), and
   `satDifferForkWF_of_dipPin` closes the campaign chain.  The ungated form is
   *not* claimed: `Temp/TwinPin_Report.md`'s 2-move gadget shows a `WF`
   twin-pair state with both twins raisable and no ready blocker, so the
   residual must be gated at the minimal bottom (see the report).

5. **§5 green play-level facts.**  `noEmptyTail_of_free_pre` proves the
   `NoEmptyTail` half of `BlockKit.splitBlock_iff_parts` for the canonical
   (`valley_exists`) split shape where the prefix is free;
   `tailCovers_iff_not_canRaise` records that the cover half is exactly the
   negated block; `splitBlock_of_freePre_noEmpty_and_cover` recomposes the block.

6. **§6 the gating gadget, kernel-checked.**  The `Temp/TwinPin_Report.md`
   two-move gadget's end state `gFin` is built explicitly, its spectrum
   `{5H, 5D}` is decided over `Card.universe`, and
   `gFin_not_fibreBlockData : ¬ FibreBlockData gFin` proves the *pointwise*
   fibre statement FALSE.  So the residual must be read at the minimal bottom.
-/

namespace BlockMin

open SplitKit

/-! ## §1. The static cover slide inside the cargo fibre -/

/-- **`BlockerReady F y`** — the arrangement-level datum that a blocker can be
slid onto `y` at `F`: a card `x` that fits `y` (`canSitOn x y`), sits face-up
in a pile with company beneath it (so the slide is reversible), and `y` is a
pile top (so `inr y` is a legal base). -/
def BlockerReady (F : State) (y : Card) : Prop :=
  ∃ (x : Card) (a k : Anchor),
    canSitOn x y = true ∧ x ∈ (F.piles a).faceUp ∧
      below x (F.piles a).faceUp ≠ [] ∧ F.pileOfTop y = some k

/-- **THE STATIC COVER SLIDE.**  A ready blocker slides onto `y`
reversibly; the landing `F'` is a same-orbit, same-rung representative where
`y` is covered, hence not vanilla-raisable.  This is the fibre-level mechanism
`Mech.coverEvent_of_block` builds from a *play*; here no play is involved. -/
theorem exists_blocked_representative {F : State} {y : Card}
    (hF : F.WF) (h : BlockerReady F y) :
    ∃ (F' : State) (x : Card),
      State.step F (Move.tabToTab x (Sum.inr y)) = some F' ∧
      reversibleAtW F (Move.tabToTab x (Sum.inr y)) ∧
      RevEqW F F' ∧
      (∀ σ : Suit, rungAt F' σ = rungAt F σ) ∧
      ¬ CanRaise F' y := by
  obtain ⟨x, a, k, hfit, hxmem, hbelow, hpod⟩ := h
  have hhold : F.pileHolding x = some a :=
    (pileHolding_eq_some_iff hF).mpr hxmem
  have hcp : F.canPlace x (Sum.inr y) = true := by
    simpa [State.canPlace, hpod] using hfit
  have hR : tabToTabR F x (Sum.inr y) = true :=
    R12.tabToTabR_true_of hhold hcp (Or.inl hbelow)
  have hrev : reversibleAtW F (Move.tabToTab x (Sum.inr y)) :=
    (tabToTabR_iff_reversibleAtW hF x (Sum.inr y)).mp hR
  have hrev' := hrev
  obtain ⟨F', play, hstep, hback⟩ := hrev'
  have hF' : F'.WF := step_wf hF hstep
  -- the mover now sits directly on `y`
  have hseat : seatOf F' x = some (Sum.inr y) := by
    have h := tfc_seat_point_edit hF hstep hrev x
    rw [ite_eq_left rfl] at h
    exact h
  have hnr : ¬ CanRaise F' y := not_canRaise_of_covered hF' ⟨x, hseat⟩
  have hrevEq : RevEqW F F' :=
    shufflePlayW_revEqW (Walk.cons hrev hstep (Walk.nil F'))
  exact ⟨F', x, hstep, hrev, hrevEq,
    fun σ => rungAt_tabToTab hstep σ, hnr⟩

/-- A covered card is not vanilla-raisable (`not_canRaise_of_covered`), stated
so the fibre dichotomy reads uniformly. -/
theorem not_canRaise_of_coveredAt {F : State} (hF : F.WF) {y : Card}
    (h : CoveredAt F y) : ¬ CanRaise F y :=
  not_canRaise_of_covered hF h

/-! ## §2. The pointwise fibre dichotomy -/

/-- **`FibreBlockData F` — THE POINTWISE FIBRE PIN.**  At a `WF` state whose
S-live set is the twin pair of `x`, one twin is covered or a blocker is ready
for one of them.  This is a *pointwise* statement about the state `F`; it is
**not** true for arbitrary `WF` twin-pair states (the `Temp/TwinPin_Report.md`
gadget has both twins raisable and no ready blocker), so only its gated form at
a minimal bottom is used (§4). -/
def FibreBlockData (F : State) : Prop :=
  ∀ (x : Card), F.WF → TwinLivePair F x →
    CoveredAt F x ∨ CoveredAt F x.twin ∨
      BlockerReady F x ∨ BlockerReady F x.twin

/-- **THE SPECTRUM IS A POSITION INVARIANT.**  Orbit-mates at equal rungs have
the same S-live set (`FreeOrbit.canRaiseS_orbit_rung`), hence the same
`TwinLivePair`. -/
theorem twinLivePair_of_revEqW_rung {F F' : State} {x : Card}
    (hF : F.WF) (hrev : RevEqW F F')
    (hrung : ∀ σ : Suit, rungAt F' σ = rungAt F σ)
    (hl : TwinLivePair F x) : TwinLivePair F' x := by
  intro c
  rw [← canRaiseS_orbit_rung hF (RevEqW_symm hrev)
    (fun σ => (hrung σ).symm) (c := c)]
  exact hl c

/-- **A BLOCKED REPRESENTATIVE IN THE FIBRE.**  From `FibreBlockData`: a
same-rung orbit-mate where one of the twins is not vanilla-raisable. -/
theorem exists_blocked_twin_of_data {F : State}
    (hF : F.WF) (hd : FibreBlockData F) {x : Card}
    (hl : TwinLivePair F x) :
    ∃ (F' : State) (z : Card),
      RevEqW F F' ∧ (∀ σ : Suit, rungAt F' σ = rungAt F σ) ∧
      (z = x ∨ z = x.twin) ∧ ¬ CanRaise F' z := by
  rcases hd x hF hl with hcov | hcov | hready | hready
  · exact ⟨F, x, RevEqW_refl F, fun _ => rfl, Or.inl rfl,
      not_canRaise_of_coveredAt hF hcov⟩
  · exact ⟨F, x.twin, RevEqW_refl F, fun _ => rfl, Or.inr rfl,
      not_canRaise_of_coveredAt hF hcov⟩
  · obtain ⟨F', b, hstep, hrev, hrevEq, hrung, hnr⟩ :=
      exists_blocked_representative hF hready
    exact ⟨F', x, hrevEq, hrung, Or.inl rfl, hnr⟩
  · obtain ⟨F', b, hstep, hrev, hrevEq, hrung, hnr⟩ :=
      exists_blocked_representative hF hready
    exact ⟨F', x.twin, hrevEq, hrung, Or.inr rfl, hnr⟩

/-- **THE REPRESENTATIVE FORK.**  `FibreBlockData` plus the spectrum yields a
`ForkWitness` at a same-rung orbit-mate.  If the blocked twin is `x` the fork
card is `x.twin`, else it is `x`. -/
theorem forkWitness_of_data {F : State}
    (hF : F.WF) (hd : FibreBlockData F) {x : Card}
    (hl : TwinLivePair F x) :
    ∃ (F' : State) (z : Card),
      RevEqW F F' ∧ (∀ σ : Suit, rungAt F' σ = rungAt F σ) ∧
      ForkWitness F' z := by
  obtain ⟨F', z, hrev, hrung, hzx, hnr⟩ :=
    exists_blocked_twin_of_data hF hd hl
  have hl' : TwinLivePair F' x := twinLivePair_of_revEqW_rung hF hrev hrung hl
  rcases hzx with hzx | hzx
  · -- the blocked card is `x`; the fork card is `x.twin`
    rw [hzx] at hnr
    refine ⟨F', Card.twin x, hrev, hrung, (forkWitness_iff F' (Card.twin x)).mpr
      ⟨?_, ?_⟩⟩
    · exact Mech.twinLivePair_of_eq_twin hl' rfl
    · show ¬ CanRaise F' (Card.twin (Card.twin x))
      rw [card_twin_twin]
      exact hnr
  · -- the blocked card is `x.twin`; the fork card is `x`
    rw [hzx] at hnr
    exact ⟨F', x, hrev, hrung, (forkWitness_iff F' x).mpr ⟨hl', hnr⟩⟩

/-! ## §3. Sharpening: only the both-raisable case survives -/

/-- **A COVERING CARD OF ONE TWIN BLOCKS THE OTHER.**  If `u` sits directly on
`x`, then `u` fits `x` (`tfc_seat_parent`), and twins share rank and colour, so
`u` fits `x.twin` as well.  Unless `x.twin` is already covered (in which case
there is nothing to do) `x.twin` is a pile top (S-live and uncovered ⇒
vanilla-raisable), so `u` is a ready blocker for it. -/
theorem blockerReady_of_covered_other {F : State} {x : Card}
    (hF : F.WF) (hs : CanRaiseS F x.twin) (hcov : CoveredAt F x) :
    CoveredAt F x.twin ∨ BlockerReady F x.twin := by
  rcases canRaise_or_covered hF hs with hcanT | hcovT
  · right
    obtain ⟨u, huseat⟩ := hcov
    obtain ⟨a, hhold, hbelow, hlast⟩ := tfc_seatOf_of_inr huseat
    have hfitx : canSitOn u x = true := (tfc_seat_parent hF hhold hlast).1
    have hfitT : canSitOn u x.twin = true := by
      simpa [Card.twin, Suit.color_twin] using hfitx
    obtain ⟨-, k, hpod, -⟩ := hcanT
    exact ⟨u, a, k, hfitT, pileHolding_mem hhold, hbelow, hpod⟩
  · exact Or.inl hcovT

/-- **THE MECHANISM SLIDE IS A READY BLOCKER.**  `Mech.CoverEvent` already
carries exactly a `BlockerReady` at the source state `A` of its slide: the
mover sits on `c.twin` (so its `below` is nonempty), `canPlace` gives the target
`pileOfTop c` and `canSitOn`, and the landing covers `c`.  So the play-level
cover event and the arrangement-level blocker are the same datum. -/
theorem blockerReady_of_coverEvent {B F : State} {post : List Move} {c : Card}
    (hB : B.WF) (h : Mech.CoverEvent B F post c) :
    ∃ A : State, BlockerReady A c := by
  obtain ⟨x, s1, s2, A, Z, hpost, hplay, hseat, hrev, hstep, hplay2, hseatF⟩ := h
  have hA : A.WF := walk_wf hB hplay
  have hR : tabToTabR A x (Sum.inr c) = true :=
    (tabToTabR_iff_reversibleAtW hA x (Sum.inr c)).mpr hrev
  obtain ⟨a, hhold, hcp, -⟩ := tfc_tabToTabR_inv hR
  obtain ⟨k, hk, hfit⟩ := canPlace_inr hcp
  obtain ⟨a', hhold', hbelow, -⟩ := tfc_seatOf_of_inr hseat
  have haa : a' = a := Option.some.inj (hhold'.symm.trans hhold)
  rw [haa] at hbelow
  exact ⟨A, x, a, k, hfit, pileHolding_mem hhold, hbelow, hk⟩

/-- **`BothRaisableBlock F` — the only case of `FibreBlockData` not discharged
by the covered dichotomy.**  If both twins are vanilla-raisable at `F`, a ready
blocker exists for one of them. -/
def BothRaisableBlock (F : State) : Prop :=
  ∀ (x : Card), F.WF → TwinLivePair F x → CanRaise F x → CanRaise F x.twin →
    BlockerReady F x ∨ BlockerReady F x.twin

/-- **THE SHARPENING.**  `BothRaisableBlock` implies the full pointwise
dichotomy `FibreBlockData`: if a twin is covered, `blockerReady_of_covered_other`
(or the covered disjunct itself) finishes; only the both-raisable case consults
the residual. -/
theorem fibreBlockData_of_bothRaisable {F : State}
    (h : BothRaisableBlock F) : FibreBlockData F := by
  intro x hF hl
  have hsx : CanRaiseS F x := (hl x).mpr (Or.inl rfl)
  have hsT : CanRaiseS F x.twin := (hl x.twin).mpr (Or.inr rfl)
  rcases canRaise_or_covered hF hsx with hcx | hcvx
  · -- `x` is raisable
    rcases canRaise_or_covered hF hsT with hcxT | hcvxT
    · exact Or.inr (Or.inr (h x hF hl hcx hcxT))
    · exact Or.inr (Or.inl hcvxT)
  · -- `x` is covered: either the twin is covered too, or the same card blocks it
    rcases blockerReady_of_covered_other hF hsT hcvx with hcovT | hbrT
    · exact Or.inr (Or.inl hcovT)
    · exact Or.inr (Or.inr (Or.inr hbrT))

/-! ## §4. The gated residual and the relaxed target -/

/-- **`BottomBothRaisableBlock` — THE RESIDUAL.**  At every split of a minimal
play, the bottom's fibre has a ready blocker in the both-raisable case.  It is
*gated* at the minimal bottom on purpose (see the report). -/
def BottomBothRaisableBlock : Prop :=
  ∀ (u v : State) (ρ : List Move) (F₀ : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitHyp u v ρ F₀ left right c d b pre post tail → BothRaisableBlock F₀

/-- **`BottomFibreBlock`** — the gated fibre dichotomy at the bottom. -/
def BottomFibreBlock : Prop :=
  ∀ (u v : State) (ρ : List Move) (F₀ : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitHyp u v ρ F₀ left right c d b pre post tail → FibreBlockData F₀

/-- **THE RESIDUAL GIVES THE FIBRE DICHOTOMY.**  Pointwise sharpening at the
minimal bottom. -/
theorem bottomFibreBlock_of_bothRaisable (h : BottomBothRaisableBlock) :
    BottomFibreBlock :=
  fun u v ρ F₀ left right c d b pre post tail hh =>
    fibreBlockData_of_bothRaisable (h u v ρ F₀ left right c d b pre post tail hh)

/-- **THE RELAXED TARGET `DipPin`.**  At every split of a minimal play there is
a representative `F` of the bottom's *position* (same orbit as `u`, same rung
vector as the bottom `F₀`) carrying a `ForkWitness`.  The pin is read at the
representative, not necessarily at the play's bottom. -/
def DipPin : Prop :=
  ∀ (u v : State) (ρ : List Move) (F₀ : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitHyp u v ρ F₀ left right c d b pre post tail →
    ∃ (F : State) (x : Card),
      sameOrbitSetoid.r u F ∧
      (∀ σ : Suit, rungAt F σ = rungAt F₀ σ) ∧
      TwinLivePair F x ∧ ¬ CanRaise F x.twin

/-- **`SplitLivePair` + the gated residual give `DipPin`.**  `SplitLivePair`
supplies the bottom's spectrum; the fibre dichotomy gives a blocked
representative; the orbit chain `u → F₀ → F` puts it in `u`'s orbit. -/
theorem dipPin_of_parts (hl : SplitLivePair) (hd : BottomFibreBlock) : DipPin := by
  intro u v ρ F₀ left right c d b pre post tail h
  have hkeep := h
  obtain ⟨huwf, -, -, -, -, -, -, hleft, -, -, -, -⟩ := hkeep
  have hF₀ : F₀.WF := SatDifferCensus.ShufflePlayW.wf_end hleft huwf
  have hpair : TwinLivePair F₀ d := hl u v ρ F₀ left right c d b pre post tail h
  have hdata : FibreBlockData F₀ :=
    hd u v ρ F₀ left right c d b pre post tail h
  obtain ⟨F, z, hrev, hrung, hfork⟩ := forkWitness_of_data hF₀ hdata hpair
  obtain ⟨hspec, hpin⟩ := (forkWitness_iff F z).mp hfork
  have huF₀ : RevEqW u F₀ := shufflePlayW_revEqW hleft
  have huF : RevEqW u F := RevEqW_trans huF₀ hrev
  exact ⟨F, z, RevEqW_symm huF, hrung, hspec, hpin⟩

/-- **THE RESIDUAL GIVES `DipPin`.** -/
theorem dipPin_of_bothRaisable (hl : SplitLivePair) (hd : BottomBothRaisableBlock) :
    DipPin :=
  dipPin_of_parts hl (bottomFibreBlock_of_bothRaisable hd)

/-- **THE ORIGINAL PINNED BOTTOM IMPLIES THE RESIDUAL.**  `SplitBlock` plus
`SplitLivePair` pin the pull card at the play's own bottom (`SplitTwin` turns it
into the raise card's twin), so the gated fibre dichotomy holds trivially and
`DipPin` is at most as hard as `SplitBlock`. -/
theorem dipPin_of_livePair_block (hl : SplitLivePair) (hb : SplitBlock) : DipPin := by
  intro u v ρ F₀ left right c d b pre post tail h
  have hkeep := h
  obtain ⟨huwf, -, -, -, -, -, -, hleft, -, -, -, -⟩ := hkeep
  have hF₀ : F₀.WF := SatDifferCensus.ShufflePlayW.wf_end hleft huwf
  have hpair : TwinLivePair F₀ d := hl u v ρ F₀ left right c d b pre post tail h
  have htwin : d = c.twin :=
    splitTwin_of_livePair_block hl hb u v ρ F₀ left right c d b pre post tail h
  have hblock : ¬ CanRaise F₀ c :=
    hb u v ρ F₀ left right c d b pre post tail h
  have hpin : ¬ CanRaise F₀ d.twin := by
    rw [htwin, card_twin_twin]
    exact hblock
  have huF₀ : RevEqW u F₀ := shufflePlayW_revEqW hleft
  exact ⟨F₀, d, RevEqW_symm huF₀, fun _ => rfl, hpair, hpin⟩

/-- **THE CAMPAIGN CHAIN FROM `DipPin`.**  A minimal play gives a valley split
(`ValleyElim.valley_exists`); `DipPin` gives a same-orbit representative with a
fork; that is exactly the existential `SatDifferForkWF` asks for. -/
theorem satDifferForkWF_of_dipPin (h : DipPin)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF := by
  intro u v huwf hsu hsv hcls hdiff
  obtain ⟨ρ, hplay, hminlen⟩ := hmin u v huwf hsu hsv hcls hdiff
  obtain ⟨F₀, hsplit⟩ := ValleyElim.valley_exists huwf hsu hsv hdiff hplay
  obtain ⟨left, right, c, d, b, pre, post, tail,
    hρ, hleft, hright, hshape, hfree, hrightShape⟩ := hsplit
  have hh : SplitHyp u v ρ F₀ left right c d b pre post tail :=
    ⟨huwf, hsu, hsv, hplay,
      ⟨left, right, c, d, b, pre, post, tail,
        hρ, hleft, hright, hshape, hfree, hrightShape⟩,
      hminlen, hρ, hleft, hright, hshape, hfree, hrightShape⟩
  obtain ⟨F, x, horb, -, hspec, hpin⟩ :=
    h u v ρ F₀ left right c d b pre post tail hh
  exact ⟨F, x, horb, (forkWitness_iff F x).mpr ⟨hspec, hpin⟩⟩

/-- **THE CAMPAIGN CHAIN FROM THE RESIDUAL.**  `SplitLivePair` plus the gated
both-raisable block, plus the choice-free shortest-play interface. -/
theorem satDifferForkWF_of_bothRaisable_drainClosed
    (hl : SplitLivePair) (hd : BottomBothRaisableBlock)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  satDifferForkWF_of_dipPin (dipPin_of_bothRaisable hl hd) hmin

/-! ## §5. Green play-level facts -/

/-- **`NoEmptyTail` HOLDS WHEN THE SPLIT'S PREFIX IS FREE.**  If every letter
before the split's pull is free (the canonical `valley_exists` split has
`pre = α₁` inside the raise-free prefix `ρ₁`; the free case is the strict
sub-case), then `post ≠ []`: if `post = []` then the pre-pull state `A'` is
saturated (`ssaturated_free_prefix`) while the raise card `d` is raisable there
(`BlockKit.emptyTail_canRaise_before`), absurd. -/
theorem noEmptyTail_of_free_pre
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail)
    (hfreepre : ∀ m ∈ pre, ValleyElim.FreeMove m) :
    post ≠ [] := by
  intro hpost
  have hkeep := h
  obtain ⟨huwf, hsatu, -, -, -, -, -, -, -, -, -, -⟩ := hkeep
  have hcd : c ≠ d := BlockKit.emptyTail_turn_ne h hpost
  obtain ⟨A', hpre, hcanA'd⟩ := BlockKit.emptyTail_canRaise_before h hpost
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  have hsatA' : SSaturated A' :=
    ValleyElim.ssaturated_free_prefix hpre hfreepre huwf hsatu
  exact hsatA' d (CanRaiseS.now d hcanA'd)

/-- **THE COVER HALF IS THE NEGATION OF THE BLOCK.**  With the green facts
(`CanRaiseS F c`), `CoveredAt F c` and `¬ CanRaise F c` are inter-derivable
(`canRaise_or_covered`); so `TailCovers` is exactly the `¬ CanRaise F c` clause
read at a split with nonempty free tail. -/
theorem tailCovers_iff_not_canRaise :
    BlockKit.TailCovers ↔
      (∀ (u v : State) (ρ : List Move) (F : State)
        (left right : List Move) (c d : Card) (b : Base)
        (pre post tail : List Move),
        SplitHyp u v ρ F left right c d b pre post tail → post ≠ [] →
        ¬ CanRaise F c) := by
  constructor
  · intro hc u v ρ F left right c d b pre post tail h hpost
    obtain ⟨hF, -, -, -⟩ := splitHyp_green h
    exact not_canRaise_of_covered hF
      (hc u v ρ F left right c d b pre post tail h hpost)
  · intro hc u v ρ F left right c d b pre post tail h hpost
    obtain ⟨hF, hSc, -, -⟩ := splitHyp_green h
    exact covered_of_live_not_canRaise hF hSc
      (hc u v ρ F left right c d b pre post tail h hpost)

/-- **THE BLOCK FROM THE TWO GREEN HALVES** — `BlockKit.splitBlock_iff_parts`,
restated with the free-prefix `NoEmptyTail` (the only shape `valley_exists`
feeds) and the cover half. -/
theorem splitBlock_of_freePre_noEmpty_and_cover
    (h1 : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      (∀ m ∈ pre, ValleyElim.FreeMove m) → post ≠ [])
    (h2 : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail → ¬ CanRaise F c) :
    SplitBlock := by
  intro u v ρ F left right c d b pre post tail h
  exact h2 u v ρ F left right c d b pre post tail h

/-! ## §6. The gating gadget: the pointwise form is FALSE -/

def AH : Card := ⟨.heart, .ace⟩
def H2 : Card := ⟨.heart, .two⟩
def H3 : Card := ⟨.heart, .three⟩
def H4 : Card := ⟨.heart, .four⟩
def H5 : Card := ⟨.heart, .five⟩
def H6 : Card := ⟨.heart, .six⟩
def H7 : Card := ⟨.heart, .seven⟩
def H8 : Card := ⟨.heart, .eight⟩
def H9 : Card := ⟨.heart, .nine⟩
def HT : Card := ⟨.heart, .ten⟩
def HJ : Card := ⟨.heart, .jack⟩
def HQ : Card := ⟨.heart, .queen⟩
def HK : Card := ⟨.heart, .king⟩

def AD : Card := ⟨.diamond, .ace⟩
def D2 : Card := ⟨.diamond, .two⟩
def D3 : Card := ⟨.diamond, .three⟩
def D4 : Card := ⟨.diamond, .four⟩
def D5 : Card := ⟨.diamond, .five⟩
def D6 : Card := ⟨.diamond, .six⟩
def D7 : Card := ⟨.diamond, .seven⟩
def D8 : Card := ⟨.diamond, .eight⟩
def D9 : Card := ⟨.diamond, .nine⟩
def DT : Card := ⟨.diamond, .ten⟩
def DJ : Card := ⟨.diamond, .jack⟩
def DQ : Card := ⟨.diamond, .queen⟩
def DK : Card := ⟨.diamond, .king⟩

def AS : Card := ⟨.spade, .ace⟩
def S2 : Card := ⟨.spade, .two⟩
def S3 : Card := ⟨.spade, .three⟩
def S4 : Card := ⟨.spade, .four⟩
def S5 : Card := ⟨.spade, .five⟩
def S6 : Card := ⟨.spade, .six⟩
def S7 : Card := ⟨.spade, .seven⟩
def S8 : Card := ⟨.spade, .eight⟩
def S9 : Card := ⟨.spade, .nine⟩
def ST : Card := ⟨.spade, .ten⟩
def SJ : Card := ⟨.spade, .jack⟩
def SQ : Card := ⟨.spade, .queen⟩
def SK : Card := ⟨.spade, .king⟩

def AC : Card := ⟨.club, .ace⟩
def C2 : Card := ⟨.club, .two⟩
def C3 : Card := ⟨.club, .three⟩
def C4 : Card := ⟨.club, .four⟩
def C5 : Card := ⟨.club, .five⟩
def C6 : Card := ⟨.club, .six⟩
def C7 : Card := ⟨.club, .seven⟩
def C8 : Card := ⟨.club, .eight⟩
def C9 : Card := ⟨.club, .nine⟩
def CT : Card := ⟨.club, .ten⟩
def CJ : Card := ⟨.club, .jack⟩
def CQ : Card := ⟨.club, .queen⟩
def CK : Card := ⟨.club, .king⟩

/-- The inert 30-card deck (`Temp/TwinPin_Report.md` §1). -/
def gDeck : List Card :=
  [H6, H7, H8, H9, HT, HJ, HQ, HK, D6, D7, D8, D9, DT, DJ, DQ, DK,
   S7, S8, S9, ST, SJ, SQ, SK, C7, C8, C9, CT, CJ, CQ, CK]

/-- **`gFin` — the gadget's end state**: hearts/diamonds founded to the four,
`pile0 = (AS..5S hidden, [6S, 5H])`, `pile1 = (AC..5C hidden, [6C, 5D])`, the
rest an inert hidden deck. -/
def gFin : State :=
  { found := fun s => match s with
      | .heart => [AH, H2, H3, H4]
      | .diamond => [AD, D2, D3, D4]
      | .spade => []
      | .club => []
    piles := fun a => match a with
      | .p0 => ⟨[AS, S2, S3, S4, S5], [S6, H5]⟩
      | .p1 => ⟨[AC, C2, C3, C4, C5], [C6, D5]⟩
      | .p2 => ⟨[], []⟩
      | .p3 => ⟨[], []⟩
      | .p4 => ⟨[], []⟩
      | .p5 => ⟨[], []⟩
      | .p6 => ⟨gDeck, []⟩
    stock := []
    waste := []
    drawStep := 1 }

/-! ## §1. Well-formedness -/

theorem gFin_wf_found : ∀ s : Suit, ∃ n, gFin.found s = s.upCards.take n := by
  intro s
  cases s with
  | heart => exact ⟨4, rfl⟩
  | diamond => exact ⟨4, rfl⟩
  | spade => exact ⟨0, rfl⟩
  | club => exact ⟨0, rfl⟩

theorem gFin_wf_runs : ∀ a : Anchor, runOK (gFin.piles a).faceUp = true := by
  intro a
  cases a <;> decide

theorem gFin_wf_count : ∀ c ∈ Card.universe, gFin.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

theorem gFin_wf : gFin.WF :=
  ⟨gFin_wf_found, gFin_wf_runs, gFin_wf_count, by decide⟩

/-! ## §2. The spectrum is the twin pair `{5H, 5D}` -/

/-- The total live-set scan: `canRaiseSB gFin c` holds exactly on the twin
pair `{H5, D5}`. -/
theorem gFin_liveB :
    (Card.universe.all (fun c =>
      decide (canRaiseSB gFin c = decide (c = H5 ∨ c = H5.twin)))) = true := by
  decide

/-- The gadget's end state has `live = {5H, 5D}`, the twin pair of `5H`. -/
theorem gFin_twinLivePair : TwinLivePair gFin H5 := by
  intro c
  have hb : canRaiseSB gFin c = decide (c = H5 ∨ c = H5.twin) :=
    of_decide_eq_true ((List.all_eq_true.mp gFin_liveB) c (Card.mem_universe c))
  constructor
  · intro hS
    have h1 : canRaiseSB gFin c = true := (canRaiseSB_iff gFin_wf).mpr hS
    rw [hb] at h1
    exact of_decide_eq_true h1
  · intro hd
    have h1 : decide (c = H5 ∨ c = H5.twin) = true := decide_eq_true hd
    rw [← hb] at h1
    exact (canRaiseSB_iff gFin_wf).mp h1

/-! ## §3. No twin is covered and no blocker is ready -/

theorem gFin_H5_not_covered : ¬ CoveredAt gFin H5 := by
  intro h
  have hall : (Card.universe.all
      (fun d => decide (seatOf gFin d ≠ some (Sum.inr H5)))) = true := by
    decide
  obtain ⟨d, hd⟩ := h
  exact (of_decide_eq_true ((List.all_eq_true.mp hall) d (Card.mem_universe d))) hd

theorem gFin_D5_not_covered : ¬ CoveredAt gFin D5 := by
  intro h
  have hall : (Card.universe.all
      (fun d => decide (seatOf gFin d ≠ some (Sum.inr D5)))) = true := by
    decide
  obtain ⟨d, hd⟩ := h
  exact (of_decide_eq_true ((List.all_eq_true.mp hall) d (Card.mem_universe d))) hd

/-- The total readiness scan: no pair `(mover, pile, target)` realises
`BlockerReady` for either twin. -/
theorem gFin_not_ready_H5 : ¬ BlockerReady gFin H5 := by
  rintro ⟨x, a, k, hfit, hxmem, hbelow, hpod⟩
  have hall : (Card.universe.all (fun x => Anchor.all.all (fun a => Anchor.all.all
      (fun k => decide (¬ (canSitOn x H5 = true ∧ x ∈ (gFin.piles a).faceUp ∧
        below x (gFin.piles a).faceUp ≠ [] ∧ gFin.pileOfTop H5 = some k)))))) = true := by
    decide
  have h1 := (List.all_eq_true.mp hall) x (Card.mem_universe x)
  have h2 := (List.all_eq_true.mp h1) a (Anchor.mem_all a)
  have h3 := (List.all_eq_true.mp h2) k (Anchor.mem_all k)
  exact (of_decide_eq_true h3) ⟨hfit, hxmem, hbelow, hpod⟩

theorem gFin_not_ready_D5 : ¬ BlockerReady gFin D5 := by
  rintro ⟨x, a, k, hfit, hxmem, hbelow, hpod⟩
  have hall : (Card.universe.all (fun x => Anchor.all.all (fun a => Anchor.all.all
      (fun k => decide (¬ (canSitOn x D5 = true ∧ x ∈ (gFin.piles a).faceUp ∧
        below x (gFin.piles a).faceUp ≠ [] ∧ gFin.pileOfTop D5 = some k)))))) = true := by
    decide
  have h1 := (List.all_eq_true.mp hall) x (Card.mem_universe x)
  have h2 := (List.all_eq_true.mp h1) a (Anchor.mem_all a)
  have h3 := (List.all_eq_true.mp h2) k (Anchor.mem_all k)
  exact (of_decide_eq_true h3) ⟨hfit, hxmem, hbelow, hpod⟩

/-- **THE POINTWISE FIBRE STATEMENT IS FALSE.**  At the gadget's end state the
spectrum is the twin pair `{5H, 5D}`, both twins are uncovered and neither has
a ready blocker — so there is no blocked representative of this position.  The
residual therefore *must* be gated at the minimal bottom. -/
theorem gFin_not_fibreBlockData : ¬ FibreBlockData gFin := by
  intro h
  have hd := h H5 gFin_wf gFin_twinLivePair
  rcases hd with hc | hc | hr | hr
  · exact gFin_H5_not_covered hc
  · rw [show H5.twin = D5 from rfl] at hc
    exact gFin_D5_not_covered hc
  · exact gFin_not_ready_H5 hr
  · rw [show H5.twin = D5 from rfl] at hr
    exact gFin_not_ready_D5 hr
/-! ## §7. Axiom battery -/

#print axioms BlockMin.exists_blocked_representative
#print axioms BlockMin.not_canRaise_of_coveredAt
#print axioms BlockMin.twinLivePair_of_revEqW_rung
#print axioms BlockMin.exists_blocked_twin_of_data
#print axioms BlockMin.forkWitness_of_data
#print axioms BlockMin.blockerReady_of_covered_other
#print axioms BlockMin.blockerReady_of_coverEvent
#print axioms BlockMin.fibreBlockData_of_bothRaisable
#print axioms BlockMin.bottomFibreBlock_of_bothRaisable
#print axioms BlockMin.dipPin_of_parts
#print axioms BlockMin.dipPin_of_bothRaisable
#print axioms BlockMin.dipPin_of_livePair_block
#print axioms BlockMin.satDifferForkWF_of_dipPin
#print axioms BlockMin.satDifferForkWF_of_bothRaisable_drainClosed
#print axioms BlockMin.noEmptyTail_of_free_pre
#print axioms BlockMin.tailCovers_iff_not_canRaise
#print axioms BlockMin.splitBlock_of_freePre_noEmpty_and_cover
#print axioms BlockMin.gFin_wf
#print axioms BlockMin.gFin_twinLivePair
#print axioms BlockMin.gFin_H5_not_covered
#print axioms BlockMin.gFin_D5_not_covered
#print axioms BlockMin.gFin_not_ready_H5
#print axioms BlockMin.gFin_not_ready_D5
#print axioms BlockMin.gFin_not_fibreBlockData

end BlockMin


