import Orig2
import Orig2.ForkDisj

/-!
# Orig2/ForkDisjBranches - what each clause's violation branch actually yields

Scratch card (read-only on `Orig2/`; nothing committed).  Zero `sorry`,
zero `Classical.choice`, zero `native_decide`; axiom battery at the tail.

## Questions answered here

For the three split clauses (`SplitBlock`, `SplitContainment`, `SplitTwinRungPin`)
we ask the brief's question: in the VIOLATION branch, does the bottom (or the
landing) carry the drain asymmetry of
`DrainClose.fork_exists_of_asymmetry`?  The answers are kernel-checked below.

* **Containment violation** (`∃ e`, third suit, S-live at the bottom): the
  bottom is NOT a fork, for any witness (`containment_violation_no_forkWitness`):
  the live set contains two cards (`c` and `e`) that no twin pair can contain.
  The drain can still fire at the bottom, but only with the pair `{c, c.twin}`,
  so it needs `CanRaise F c.twin`, the block `¬ CanRaise F c`, and the extra
  rank-floor datum that the third card does not sit below `c`'s rank
  (`containment_violation_drain_datum`).  Without that floor the violation does
  NOT produce the drain asymmetry at the bottom.

* **Pin violation** (`¬ F.nextUp c.twin`, under the block and the containment):
  the bottom's live set contains NO twin pair at all
  (`pin_violation_no_twin_pair`).  Hence the bottom is not a fork and no
  same-rung cargo-fibre representative is either
  (`pin_violation_no_witness_in_fibre`).  The answer to the brief's concrete
  question is NEGATIVE: the live set is not a different twin pair, it is
  twin-free.  A fork in this branch, if any, must live at a DIFFERENT rung
  vector (i.e. the global bridge residual), not in the bottom's fibre.

* **Block violation** (`CanRaise F c`, under the containment and the pin):
  the live set is contained in `{c, c.twin}`.  If `c.twin` is live and blocked,
  the drain asymmetry holds AT the bottom with `x = c`, with NO minimality
  (`block_violation_drain`).  If `c.twin` is live and raisable, the pair is the
  both-raisable corner, and the existing `BlockMin.BothRaisableBlock` datum
  produces a fork at a same-rung representative (`block_violation_fork_of_blocker`).
  If `c.twin` is dead, the bottom is not a fork either
  (`block_violation_twin_dead_no_fork`).
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Disj

open Disj

/-! ## §1. Containment violation -/

/-- **A CONTAINMENT VIOLATION MAKES THE BOTTOM A NON-FORK.**  If `c` is S-live
(the green fact of every split) and a third-suit card `e` is S-live, then no
card `y` has its twin pair as the whole live set: `c` and `e` cannot both lie in
`{y, y.twin}`.  Hence `ForkWitness F y` fails for every `y`.

Note: no block, no pin, no minimality. -/
theorem containment_violation_no_forkWitness
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hviol : ∃ e, CanRaiseS F e ∧ e.suit ≠ c.suit ∧ e.suit ≠ c.twin.suit) :
    ∀ y, ¬ ForkWitness F y := by
  obtain ⟨-, hSc, -, -⟩ := SplitKit.splitHyp_green h
  obtain ⟨e, he, h1, h2⟩ := hviol
  intro y hy
  have hl : TwinLivePair F y := (forkWitness_iff F y).mp hy |>.1
  have hcy : c = y ∨ c = y.twin := (hl c).mp hSc
  have hey : e = y ∨ e = y.twin := (hl e).mp he
  have hec : e = c ∨ e = c.twin := by
    rcases hcy with hcy | hcy
    · rcases hey with hey | hey
      · exact Or.inl (hey.trans hcy.symm)
      · exact Or.inr (by rw [hey, hcy])
    · rcases hey with hey | hey
      · exact Or.inr (by rw [hey, hcy, card_twin_twin])
      · exact Or.inl (hey.trans hcy.symm)
  rcases hec with hec | hec
  · exact h1 (congrArg Card.suit hec)
  · exact h2 (congrArg Card.suit hec)

/-- **THE LANDING FORM OF THE CONTAINMENT VIOLATION.**  A third-suit card that
is S-live at the pull landing `B` is S-live at the bottom `F` (the free tail is
an iff-transport), so the bottom is a non-fork by
`containment_violation_no_forkWitness`. -/
theorem landingThirdSuitViolation_no_forkWitness
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    {A' B : State} (hpre : ShufflePlayW u pre A')
    (hstep : State.step A' (Move.foundToTab c b) = some B)
    (e : Card) (heB : CanRaiseS B e)
    (h1 : e.suit ≠ c.suit) (h2 : e.suit ≠ c.twin.suit) :
    ∀ y, ¬ ForkWitness F y := by
  have hk := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hfree, -⟩ := hk
  obtain ⟨hpost, hB⟩ := Landing.post_play_of_landing h hpre hstep
  have heF : CanRaiseS F e :=
    (Mech.canRaiseS_landing_iff hB hpost hfree e).mp heB
  exact containment_violation_no_forkWitness h ⟨e, heF, h1, h2⟩

/-- The exact positive data of a containment violation: the third card `e` is
neither `c` nor `c.twin`, and its rank is the suit's rung. -/
theorem containment_violation_third_data
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (_h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (e : Card) (he : CanRaiseS F e)
    (h1 : e.suit ≠ c.suit) (h2 : e.suit ≠ c.twin.suit) :
    e ≠ c ∧ e ≠ c.twin ∧ e.rank.toIdx = rungAt F e.suit := by
  refine ⟨?_, ?_, (canRaiseS_rung he).symm⟩
  · intro hec
    exact h1 (congrArg Card.suit hec)
  · intro hec
    exact h2 (congrArg Card.suit hec)

/-- **THE DRAIN IN THE CONTAINMENT-VIOLATION BRANCH.**  The violation does not
by itself give the drain asymmetry, but the pair `{c, c.twin}` does the job
provided (i) `c` is blocked, (ii) `c.twin` is vanilla-raisable, and (iii) the
third card does not sit below `c`'s rank (the rank-floor datum).  Then the drain
of `DrainClose.fork_exists_of_asymmetry` fires at `F` with `x = c.twin`, and
the fork lands in `u`'s class.

Condition (iii) is exactly the extra datum the violation branch needs: the
third-suit card can have an arbitrarily low rung, and the drain's floor is not
free. -/
theorem containment_violation_drain_datum
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hblock : ¬ CanRaise F c)
    (_hviol : ∃ e, CanRaiseS F e ∧ e.suit ≠ c.suit ∧ e.suit ≠ c.twin.suit)
    (hcanT : CanRaise F c.twin)
    (hfloor : ∀ e, CanRaiseS F e → c.rank.toIdx ≤ e.rank.toIdx) :
    ForkInClass u := by
  have hk := h
  obtain ⟨hF, hSc, -, -⟩ := SplitKit.splitHyp_green hk
  obtain ⟨-, -, -, -, -, -, -, hleft, -, -, -, -⟩ := hk
  have hlive : CanRaiseS F (c.twin).twin := by
    rwa [card_twin_twin]
  have hblk : ¬ CanRaise F (c.twin).twin := by
    rwa [card_twin_twin]
  have hfloorT : ∀ e, CanRaiseS F e → (c.twin).rank.toIdx ≤ e.rank.toIdx := by
    intro e he
    have h' := hfloor e he
    have htr : (c.twin).rank = c.rank := Card.twin_rank c
    rw [htr]
    exact h'
  have hinv : Drain.DrainInvariant F c.twin :=
    ⟨hcanT, hlive, hblk, hfloorT⟩
  exact forkInClass_of_drainInvariant
    (RevEqW_symm (shufflePlayW_revEqW hleft)) hF hinv

/-! ## §2. Pin violation -/

/-- **A PIN VIOLATION MAKES THE LIVE SET TWIN-FREE.**  Assume the block, the
containment (live set confined to the two pair suits) and a failing pin
`¬ nextUp c.twin`.  Then no card has both itself and its twin S-live at the
bottom.

The rungs do the work: the pull card's suit is at `c.rank`, the twin suit is
strictly behind (`pin_fails_iff_strictly_behind`), and containment confines
every live card to one of those two suits.  A twin pair needs equal ranks on
the two twin suits, which is impossible. -/
theorem pin_violation_no_twin_pair
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hblock : ¬ CanRaise F c)
    (hcont : ∀ e, CanRaiseS F e → e.suit = c.suit ∨ e.suit = c.twin.suit)
    (hpin : ¬ F.nextUp c.twin = true) :
    ∀ x, ¬ (CanRaiseS F x ∧ CanRaiseS F x.twin) := by
  obtain ⟨hF, hSc, -, -⟩ := SplitKit.splitHyp_green h
  have hne : rungAt F c.twin.suit ≠ rungAt F c.suit := by
    intro heq
    apply hpin
    rw [TwinKit.nextUp_true_iff]
    rw [heq, canRaiseS_rung hSc, Card.twin_rank]
  have hlt : rungAt F c.twin.suit < c.rank.toIdx :=
    (PairRungKit.pin_fails_iff_strictly_behind hF hSc hblock).mpr hne
  intro x ⟨hxlive, hxtlive⟩
  have hxr : rungAt F x.suit = x.rank.toIdx := canRaiseS_rung hxlive
  have hxtr : rungAt F x.twin.suit = x.twin.rank.toIdx := canRaiseS_rung hxtlive
  have htr : x.twin.rank = x.rank := Card.twin_rank x
  rcases hcont x hxlive with hs | hs
  · -- `x` is in `c`'s suit; its twin is in `c.twin`'s suit at the same rank
    have hxs : rungAt F x.suit = rungAt F c.suit := by rw [hs]
    have hxrank : x.rank.toIdx = c.rank.toIdx := by
      rw [← hxr, hxs, canRaiseS_rung hSc]
    have hts : x.twin.suit = c.twin.suit := by
      simp [Card.twin, hs]
    have hcontr : x.twin.rank.toIdx = rungAt F c.twin.suit := by
      rw [← hxtr, hts]
    have hbad : x.twin.rank.toIdx < x.rank.toIdx := by
      omega
    rw [htr] at hbad
    exact Nat.lt_irrefl _ hbad
  · -- `x` is in `c.twin`'s suit (strictly behind); its twin is in `c`'s suit
    have hxs : rungAt F x.suit = rungAt F c.twin.suit := by rw [hs]
    have hxrank : x.rank.toIdx = rungAt F c.twin.suit := by
      rw [← hxr, hxs]
    have hts : x.twin.suit = c.suit := by
      simp [Card.twin, hs]
    have hcontr : x.twin.rank.toIdx = rungAt F c.suit := by
      rw [← hxtr, hts]
    have hlt2 : x.rank.toIdx < c.rank.toIdx := by
      omega
    have heq : x.twin.rank.toIdx = c.rank.toIdx := by
      rw [hcontr, canRaiseS_rung hSc]
    rw [htr] at heq
    omega

/-- **NO FORK AT A PIN-VIOLATING BOTTOM.** -/
theorem pin_violation_no_forkWitness
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hblock : ¬ CanRaise F c)
    (hcont : ∀ e, CanRaiseS F e → e.suit = c.suit ∨ e.suit = c.twin.suit)
    (hpin : ¬ F.nextUp c.twin = true) :
    ∀ y, ¬ ForkWitness F y := by
  have hpair := pin_violation_no_twin_pair h hblock hcont hpin
  intro y hy
  have hl : TwinLivePair F y := (forkWitness_iff F y).mp hy |>.1
  have hyLive : CanRaiseS F y := (hl y).mpr (Or.inl rfl)
  have hyT : CanRaiseS F y.twin := (hl y.twin).mpr (Or.inr rfl)
  exact hpair y ⟨hyLive, hyT⟩

/-- **NO FORK IN THE PIN-VIOLATING FIBRE.**  Since the live set has no twin
pair at `F`, and `CanRaiseS` is constant along a same-rung reversible orbit
(`FreeOrbit.canRaiseS_orbit_rung`), no same-rung orbit-mate of `F` is a fork
either.  So the fork core of the drain cannot fire anywhere in `F`'s
rung-preserving fibre. -/
theorem pin_violation_no_witness_in_fibre
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hblock : ¬ CanRaise F c)
    (hcont : ∀ e, CanRaiseS F e → e.suit = c.suit ∨ e.suit = c.twin.suit)
    (hpin : ¬ F.nextUp c.twin = true)
    {F' : State} (hrev : RevEqW F F')
    (hrung : ∀ s : Suit, rungAt F' s = rungAt F s) :
    ∀ y, ¬ ForkWitness F' y := by
  obtain ⟨hF, -, -, -⟩ := SplitKit.splitHyp_green h
  have hpair := pin_violation_no_twin_pair h hblock hcont hpin
  have hcls : sameOrbitSetoid.r F F' := RevEqW_symm hrev
  have hlift : ∀ c, CanRaiseS F' c → CanRaiseS F c := by
    intro c hc
    exact (canRaiseS_orbit_rung hF hcls
      (fun s => (hrung s).symm) (c := c)).mpr hc
  intro y hy
  have hl : TwinLivePair F' y := (forkWitness_iff F' y).mp hy |>.1
  have hyLive : CanRaiseS F' y := (hl y).mpr (Or.inl rfl)
  have hyT : CanRaiseS F' y.twin :=
    (hl y.twin).mpr (Or.inr rfl)
  exact hpair y ⟨hlift y hyLive, hlift y.twin hyT⟩

/-! ## §3. Block violation -/

/-- **CONTAINMENT + PIN PIN THE LIVE SET TO THE TWIN PAIR.**  Every S-live card
is `c` or `c.twin` (the pin puts the twin suit's rung at `c`'s rank). -/
theorem live_eq_pair_of_cont_pin
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hcont : ∀ e, CanRaiseS F e → e.suit = c.suit ∨ e.suit = c.twin.suit)
    (hpin : F.nextUp c.twin = true) :
    ∀ e, CanRaiseS F e → e = c ∨ e = c.twin := by
  obtain ⟨-, hSc, -, -⟩ := SplitKit.splitHyp_green h
  have hpinR : rungAt F c.twin.suit = c.rank.toIdx :=
    TwinKit.nextUp_true_iff.mp hpin
  intro e he
  rcases hcont e he with hs | hs
  · exact Or.inl (Mech.live_eq_of_suit_left (canRaiseS_rung hSc) he hs)
  · exact Or.inr (Mech.live_eq_of_suit_twin hpinR he hs)

/-- **THE BLOCK VIOLATION FEEDS THE DRAIN DIRECTLY.**  Assume the containment
and the pin (so the live set is `⊆ {c, c.twin}`), the violation `CanRaise F c`,
that `c.twin` is S-live, and that `c.twin` is blocked.  Then the drain
asymmetry holds AT the bottom with `x = c`:

* `CanRaise F c` - the violation;
* `CanRaiseS F c.twin` - the live twin;
* `¬ CanRaise F c.twin` - the hypothesis;
* the rank floor is free: every live card is `c` or `c.twin`, and both have
  `c`'s rank.

No minimality is used.  This is the positive half of the brief's idea: the
block violation's datum is exactly what the drain consumes. -/
theorem block_violation_drain
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hcont : ∀ e, CanRaiseS F e → e.suit = c.suit ∨ e.suit = c.twin.suit)
    (hpin : F.nextUp c.twin = true)
    (hcan : CanRaise F c)
    (hliveT : CanRaiseS F c.twin)
    (hblockT : ¬ CanRaise F c.twin) :
    ForkInClass u := by
  have hk := h
  obtain ⟨hF, hSc, -, -⟩ := SplitKit.splitHyp_green hk
  obtain ⟨-, -, -, -, -, -, -, hleft, -, -, -, -⟩ := hk
  have hpinR : rungAt F c.twin.suit = c.rank.toIdx :=
    TwinKit.nextUp_true_iff.mp hpin
  have hfloor : ∀ e, CanRaiseS F e → c.rank.toIdx ≤ e.rank.toIdx := by
    intro e he
    rcases hcont e he with hs | hs
    · have heq : e.rank.toIdx = c.rank.toIdx := by
        rw [← canRaiseS_rung he, hs, canRaiseS_rung hSc]
      omega
    · have heq : e.rank.toIdx = c.rank.toIdx := by
        rw [← canRaiseS_rung he, hs, hpinR]
      omega
  have hinv : Drain.DrainInvariant F c := ⟨hcan, hliveT, hblockT, hfloor⟩
  exact forkInClass_of_drainInvariant
    (RevEqW_symm (shufflePlayW_revEqW hleft)) hF hinv

/-- **THE BLOCK VIOLATION IN THE BOTH-RAISABLE CASE.**  With the containment
and the pin, if `c.twin` is S-live and vanilla-raisable, then the live set is
exactly `{c, c.twin}` and both twins are raisable.  The existing pointwise
fibre residual `BlockMin.BothRaisableBlock F` then gives a ready blocker, hence
a fork at a same-rung orbit-mate. -/
theorem block_violation_fork_of_blocker
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hcont : ∀ e, CanRaiseS F e → e.suit = c.suit ∨ e.suit = c.twin.suit)
    (hpin : F.nextUp c.twin = true)
    (hcan : CanRaise F c)
    (hliveT : CanRaiseS F c.twin)
    (hcanT : CanRaise F c.twin)
    (hblk : BlockMin.BothRaisableBlock F) :
    ForkInClass u := by
  have hk := h
  obtain ⟨hF, hSc, -, -⟩ := SplitKit.splitHyp_green hk
  obtain ⟨-, -, -, -, -, -, -, hleft, -, -, -, -⟩ := hk
  have hpinR : rungAt F c.twin.suit = c.rank.toIdx :=
    TwinKit.nextUp_true_iff.mp hpin
  have hl : TwinLivePair F c := by
    intro e
    constructor
    · intro he
      rcases hcont e he with hs | hs
      · exact Or.inl (Mech.live_eq_of_suit_left (canRaiseS_rung hSc) he hs)
      · exact Or.inr (Mech.live_eq_of_suit_twin hpinR he hs)
    · rintro (rfl | he)
      · exact hSc
      · rw [he]; exact hliveT
  have hbd : BlockMin.FibreBlockData F :=
    BlockMin.fibreBlockData_of_bothRaisable hblk
  obtain ⟨F', z, hrev, -, hfork⟩ := BlockMin.forkWitness_of_data hF hbd hl
  have hclsF : sameOrbitSetoid.r u F :=
    RevEqW_symm (shufflePlayW_revEqW hleft)
  exact ⟨F', z, sameOrbitSetoid.iseqv.trans hclsF (RevEqW_symm hrev), hfork⟩

/-- **THE BLOCK VIOLATION WITH A DEAD TWIN: SINGLETON LIVE SET.**  With the
containment and the pin, if `c.twin` is not S-live then every S-live card is
`c`. -/
theorem block_violation_twin_dead_live_singleton
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hcont : ∀ e, CanRaiseS F e → e.suit = c.suit ∨ e.suit = c.twin.suit)
    (hpin : F.nextUp c.twin = true)
    (hdead : ¬ CanRaiseS F c.twin) :
    ∀ e, CanRaiseS F e → e = c := by
  obtain ⟨-, hSc, -, -⟩ := SplitKit.splitHyp_green h
  have hpinR : rungAt F c.twin.suit = c.rank.toIdx :=
    TwinKit.nextUp_true_iff.mp hpin
  intro e he
  rcases hcont e he with hs | hs
  · exact Mech.live_eq_of_suit_left (canRaiseS_rung hSc) he hs
  · exfalso
    have hrank : e.rank.toIdx = (c.twin).rank.toIdx := by
      rw [Card.twin_rank, ← canRaiseS_rung he, hs, hpinR]
    have hee : e = c.twin := ThirdLive.eq_of_suit_eq_rank_toIdx_eq hs hrank
    rw [hee] at he
    exact hdead he

/-- **NO FORK AT A BLOCK-VIOLATING, TWIN-DEAD BOTTOM.**  Since the live set is
`{c}`, no twin pair is live, so no `ForkWitness` exists at the bottom. -/
theorem block_violation_twin_dead_no_fork
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hdead : ¬ CanRaiseS F c.twin) :
    ∀ y, ¬ ForkWitness F y := by
  obtain ⟨-, hSc, -, -⟩ := SplitKit.splitHyp_green h
  intro y hy
  have hl : TwinLivePair F y := (forkWitness_iff F y).mp hy |>.1
  have hcy : c = y ∨ c = y.twin := (hl c).mp hSc
  have hyLive : CanRaiseS F y := (hl y).mpr (Or.inl rfl)
  have hyT : CanRaiseS F y.twin :=
    (hl y.twin).mpr (Or.inr rfl)
  rcases hcy with hcy | hcy
  · rw [hcy] at hdead
    exact hdead hyT
  · have hyc : y = c.twin := by rw [hcy, card_twin_twin]
    rw [hyc] at hyLive
    exact hdead hyLive

end Disj

/-! ## Battery -/

#print axioms Disj.containment_violation_no_forkWitness
#print axioms Disj.landingThirdSuitViolation_no_forkWitness
#print axioms Disj.containment_violation_third_data
#print axioms Disj.containment_violation_drain_datum
#print axioms Disj.pin_violation_no_twin_pair
#print axioms Disj.pin_violation_no_forkWitness
#print axioms Disj.pin_violation_no_witness_in_fibre
#print axioms Disj.live_eq_pair_of_cont_pin
#print axioms Disj.block_violation_drain
#print axioms Disj.block_violation_fork_of_blocker
#print axioms Disj.block_violation_twin_dead_live_singleton
#print axioms Disj.block_violation_twin_dead_no_fork
