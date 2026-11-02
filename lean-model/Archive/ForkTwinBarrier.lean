import Orig2.ForkGap
import Orig2.Fork.ForkFrontier
import Orig2.Fork.ForkTwinLive
import Orig2.Fork.ForkLanding
import Orig2.Fork.ForkPin
import Orig2.Fork.ForkSplitResidual

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2 scratch — `Orig2/ForkTwinBarrier`

READ-ONLY on `Orig2/`; scratch card; no source edit, no commit.

## Question

`Gap.SChainMateResidual` (`Orig2/ForkGap.lean:425`) says: in a shortest cross-suit
corridor, every terminal S-raise of rank `≤ d.rank` in the tail is a raise of the
pulled card `d` itself.  `Gap`'s report isolates the *surviving* case
`raise d.twin`.  The campaign's **TWIN PIN** lane
(`Landing.LandingTwinLive`, `TwinKit.SplitTwinRungPin`,
`TwinKit.SplitPairRungEq`, `PairRungKit.SplitTwinRungGe`) is a ledger statement
about `d.twin`'s rung.  The question of this card: does the pin close the twin
case?

## Answer (kernel-checked below)

**No — the pin has the wrong sign, and the ledger route is exactly as strong as
the licence route (so it buys nothing).**

1. **A fired `raise d.twin` *forces* the pin** (`mate_raise_rungAt` §1):
   `State.step A (raise d.twin) = some Z → rungAt A d.twin.suit = d.rank.toIdx`.
   The campaign's pin rows assert precisely this equality.  So the pin is a
   *consequence of the offending branch*, never a refutation of it.
   `Landing.LandingTwinLive` is the same statement at the landing: its
   conclusion `CanRaiseS B c.twin` *is* the twin's S-liveness, which forces the
   pin (`canRaiseS_rung`), and is the datum the mate raise consumes
   (`campaign_pin_of_twinLive`, `landingTwinLive_gives_pin`).

2. **The exact twin residual is licence-shaped, not rung-shaped**
   (`sChainMateResidual_iff` §3):
   `Gap.SChainMateResidual ↔ NonTwinResidual ∧ MateRaiseBarrier`, where
   `MateRaiseBarrier` says the tail never *fires* `raise d.twin`.

3. **The ledger form of that barrier is not weaker** (`twinRungBarrier_iff` §4):
   `TwinRungBarrier` (a `rungAt … ≠ d.rank.toIdx` clause at every twin-raise
   point) is *equivalent* to `MateRaiseBarrier`, because the equality is forced
   by the very event the barrier forbids.  Hence no `rungAt` residual — in
   particular no pin-shaped row — can imply the twin clause.

4. **What the corridor does pin** (§2): the pull leaves the twin suit's rung
   untouched, and the free interior preserves rungs, so
   `rungAt L d.twin.suit = rungAt B₀ d.twin.suit`.  Together with §1 this says
   the twin pin *transports* along the corridor: it is the enabling datum, not
   the obstruction.

Gates (§5): neither `RungEq`/`RungDiffers` nor `SSaturated u` is consumed; every
statement here is one-sided in `v`, exactly as `Gap.SChainMateResidual`.
-/

namespace TwinLink

open CommuteStep

/-! ## §0. The twin suit is the other suit -/

/-- The twin of a card sits in a different suit. -/
theorem twin_suit_ne (c : Card) : c.twin.suit ≠ c.suit :=
  fun h => Suit.twin_ne c.suit h

/-! ## §1. A fired `raise d.twin` pins the twin's rung — the pin is the
*consequence* of the mate branch -/

/-- **THE MATE RAISE PINS THE TWIN'S RUNG.**  Any *fired* `raise d.twin` at `A`
forces `rungAt A d.twin.suit = d.rank.toIdx`, i.e. exactly the ledger content of
the campaign's twin pin (`TwinKit.nextUp_true_iff`,
`TwinKit.SplitTwinRungPin`). -/
theorem mate_raise_rungAt {A Z : State} {d : Card}
    (hstep : State.step A (Move.tabToFound d.twin) = some Z) :
    rungAt A (d.twin.suit) = d.rank.toIdx := by
  obtain ⟨hnext, -⟩ := step_tabToFound_inv hstep
  rw [TwinKit.nextUp_true_iff.mp hnext, Card.twin_rank]

/-- The same fact in `nextUp` form (the spelling `TwinKit.SplitTwinRungPin`
uses at the bottom). -/
theorem mate_raise_nextUp {A Z : State} {d : Card}
    (hstep : State.step A (Move.tabToFound d.twin) = some Z) :
    A.nextUp d.twin = true :=
  TwinKit.nextUp_true_iff.mpr (mate_raise_rungAt hstep)

/-- **THE MATE RAISE *COMPLETES* THE TWIN COLUMN.**  The raise writes `d.twin`
onto its foundation, so the twin suit's rung rises by exactly one: the mate
branch is a positive `+1` step of the very ledger coordinate the pin tracks. -/
theorem mate_raise_completes {A Z : State} {d : Card}
    (hstep : State.step A (Move.tabToFound d.twin) = some Z) :
    rungAt Z (d.twin.suit) = rungAt A (d.twin.suit) + 1 := by
  obtain ⟨-, a, -, hZ⟩ := step_tabToFound_inv hstep
  subst hZ
  show (((A.setFound d.twin.suit (A.found d.twin.suit ++ [d.twin]))).found
      d.twin.suit).length = _
  rw [setFound_found_self]
  unfold rungAt
  rw [List.length_append, List.length_singleton]

/-- **THE CAMPAIGN'S PIN IS THE TWIN'S S-LIVENESS (in ledger form).**  At any
state, `CanRaiseS B c.twin` — the conclusion of `Landing.LandingTwinLive`, and
the first conjunct of `Mech.LandingLivePair` — forces both
`B.nextUp c.twin = true` (the `SplitTwinRungPin` conclusion) and
`rungAt B c.twin.suit = c.rank.toIdx`.  So the pin row is *implied by* the
mate-enabling datum: it cannot be used against it. -/
theorem campaign_pin_of_twinLive {B : State} {c : Card} (h : CanRaiseS B c.twin) :
    B.nextUp c.twin = true ∧ rungAt B c.twin.suit = c.rank.toIdx := by
  have hr : rungAt B c.twin.suit = c.twin.rank.toIdx := canRaiseS_rung h
  exact ⟨TwinKit.nextUp_true_iff.mpr hr, by rw [hr, Card.twin_rank]⟩

/-- **`Landing.LandingTwinLive` READ AS A PIN.**  The campaign's landing row, at
any split, gives the twin pin at the pull's landing `B` — in the campaign's own
naming `c` is the *pulled* card, so this is `rungAt B c.twin.suit = c.rank.toIdx`:
the twin is live (next-up) exactly where the split's raise will look for it. -/
theorem landingTwinLive_gives_pin
    (ht : Landing.LandingTwinLive)
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    {A' B : State} (hpre : ShufflePlayW u pre A')
    (hstep : State.step A' (Move.foundToTab c b) = some B) :
    rungAt B c.twin.suit = c.rank.toIdx :=
  (campaign_pin_of_twinLive
    (ht u v ρ F left right c d b pre post tail hs A' B hpre hstep)).2

/-- The campaign's own rows are the `= d.rank.toIdx` equality at the *bottom*,
so they are the same coordinate this card measures at the corridor's points. -/
theorem splitTwinRungPin_gives_rung {F : State} {c : Card}
    (h : F.nextUp c.twin = true) : rungAt F c.twin.suit = c.rank.toIdx := by
  have hr : rungAt F c.twin.suit = c.twin.rank.toIdx := TwinKit.nextUp_true_iff.mp h
  rw [hr, Card.twin_rank]

/-! ## §2. What the corridor itself pins: the twin rung transports along the
pull and the free interior -/

/-- **THE PULL DOES NOT TOUCH THE TWIN SUIT'S RUNG.**  A pull of `d` writes only
`d.suit`'s foundation column, so `d.twin.suit`'s rung is preserved. -/
theorem rungAt_twin_of_pull {P L : State} {d : Card} {b : Base}
    (hstep : State.step P (Move.foundToTab d b) = some L) :
    rungAt L (d.twin.suit) = rungAt P (d.twin.suit) := by
  obtain ⟨c', htop0, hc', hcp, hL⟩ := step_foundToTab_inv hstep
  cases hc'
  have hL' : L = CommuteStep.pullSt P d b := hL
  unfold rungAt
  rw [hL', CommuteStep.pullSt_found_apply, ite_eq_right (twin_suit_ne d)]

/-- **THE FREE INTERIOR PRESERVES THE TWIN SUIT'S RUNG** (re-export of
`ValleyElim.rungAt_eq_of_free_play` at the twin suit). -/
theorem rungAt_twin_of_freeOnly {B P : State} {γ : List Move} {d : Card}
    (hplay : ShufflePlayW B γ P) (hfree : Canon.FreeOnly γ) :
    rungAt P (d.twin.suit) = rungAt B (d.twin.suit) :=
  ValleyElim.rungAt_eq_of_free_play hplay hfree d.twin.suit

/-- **THE TWIN PIN AT THE LANDING IS THE TWIN PIN AT THE RAISE'S IMAGE.**  The
corridor's pull and its free interior are both ledger-inert on `d.twin.suit`, so
the twin's rung at the pull landing `L` is the rung at the corridor's raise image
`B₀`.  Any twin-pin row proved at `B₀` (e.g. by the campaign's split kit) is
therefore a statement about `L` — and `L` is where the mate raise starts from. -/
theorem rungAt_twin_landing_eq_image {B₀ P₀ L : State} {γ : List Move}
    {d : Card} {b : Base}
    (hγ : ShufflePlayW B₀ γ P₀) (hfree : Canon.FreeOnly γ)
    (hpull : State.step P₀ (Move.foundToTab d b) = some L) :
    rungAt L (d.twin.suit) = rungAt B₀ (d.twin.suit) :=
  (rungAt_twin_of_pull hpull).trans (rungAt_twin_of_freeOnly hγ hfree)

/-! ## §3. The exact decomposition of `Gap.SChainMateResidual` -/

/-- **`NonTwinResidual`** — `Gap.SChainMateResidual` with the twin case removed:
every terminal S-raise of rank `≤ d.rank` in the tail that is not `raise d.twin`
is a raise of `d`. -/
def NonTwinResidual : Prop :=
  ∀ (u v : State) (ρ pre γ tail : List Move) (c d : Card) (b : Base)
    (A₀ B₀ P₀ L : State),
    u.WF → SSaturated v → ShufflePlayW u ρ v →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
    ρ = pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))) →
    Canon.FreeOnly γ → c.suit ≠ d.suit →
    ShufflePlayW u pre A₀ → State.step A₀ (Move.tabToFound c) = some B₀ →
    ShufflePlayW B₀ γ P₀ → State.step P₀ (Move.foundToTab d b) = some L →
    ∀ (z : Card) (s1 s2 : List Move) (A Z : State),
      z.rank.toIdx ≤ d.rank.toIdx → tail = s1 ++ Move.tabToFound z :: s2 →
      ShufflePlayW L s1 A → (CanRaiseS A z ∨ CanRaiseS A z.twin) →
      State.step A (Move.tabToFound z) = some Z → z ≠ d.twin → z = d

/-- **`MateRaiseBarrier`** — THE EXACT TWIN RESIDUAL: the corridor's tail never
fires `raise d.twin` at a point where the twin is S-live.  This is the whole twin
clause of `Gap.SChainMateResidual`, isolated. -/
def MateRaiseBarrier : Prop :=
  ∀ (u v : State) (ρ pre γ tail : List Move) (c d : Card) (b : Base)
    (A₀ B₀ P₀ L : State),
    u.WF → SSaturated v → ShufflePlayW u ρ v →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
    ρ = pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))) →
    Canon.FreeOnly γ → c.suit ≠ d.suit →
    ShufflePlayW u pre A₀ → State.step A₀ (Move.tabToFound c) = some B₀ →
    ShufflePlayW B₀ γ P₀ → State.step P₀ (Move.foundToTab d b) = some L →
    ∀ (s1 s2 : List Move) (A Z : State),
      tail = s1 ++ Move.tabToFound d.twin :: s2 →
      ShufflePlayW L s1 A →
      (CanRaiseS A d.twin ∨ CanRaiseS A d.twin.twin) →
      State.step A (Move.tabToFound d.twin) = some Z → False

/-- **THE EXACT DECOMPOSITION.**  `Gap.SChainMateResidual` is precisely
`NonTwinResidual ∧ MateRaiseBarrier`.  The first factor is the rank/other-suit
lane; the second is *the entire twin case*, and it is licence-shaped. -/
theorem sChainMateResidual_iff :
    Gap.SChainMateResidual ↔ NonTwinResidual ∧ MateRaiseBarrier := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro u v ρ pre γ tail c d b A₀ B₀ P₀ L hwf hv hplay hmin heq hfree hsu hpre hstepR
        hγ hpull z s1 s2 A Z hle htail hp hlive hstep hne
      exact h u v ρ pre γ tail c d b A₀ B₀ P₀ L hwf hv hplay hmin heq hfree hsu hpre
        hstepR hγ hpull z s1 s2 A Z hle htail hp hlive hstep
    · intro u v ρ pre γ tail c d b A₀ B₀ P₀ L hwf hv hplay hmin heq hfree hsu hpre hstepR
        hγ hpull s1 s2 A Z htail hp hlive hstep
      have hdt : d.twin = d :=
        h u v ρ pre γ tail c d b A₀ B₀ P₀ L hwf hv hplay hmin heq hfree hsu hpre
          hstepR hγ hpull d.twin s1 s2 A Z (by simp [Card.twin_rank]) htail hp hlive hstep
      exact Gap.card_twin_ne d hdt
  · rintro ⟨h1, h2⟩
    intro u v ρ pre γ tail c d b A₀ B₀ P₀ L hwf hv hplay hmin heq hfree hsu hpre hstepR
      hγ hpull z s1 s2 A Z hle htail hp hlive hstep
    by_cases hz : z = d.twin
    · subst hz
      exact (h2 u v ρ pre γ tail c d b A₀ B₀ P₀ L hwf hv hplay hmin heq hfree hsu hpre
        hstepR hγ hpull s1 s2 A Z htail hp hlive hstep).elim
    · exact h1 u v ρ pre γ tail c d b A₀ B₀ P₀ L hwf hv hplay hmin heq hfree hsu hpre
        hstepR hγ hpull z s1 s2 A Z hle htail hp hlive hstep hz

/-- One direction of the reduction, in the useful orientation: **the twin
barrier plus the non-twin lane give `Gap.SChainMateResidual`**. -/
theorem sChainMateResidual_of_mateBarrier
    (h1 : MateRaiseBarrier) (h2 : NonTwinResidual) : Gap.SChainMateResidual :=
  sChainMateResidual_iff.mpr ⟨h2, h1⟩

/-- **THE REDUCTION TO THE SEAT-MATE FACE.**  The twin residual, isolated, plus
the non-twin lane and the same-card lane give `Blocks.NoSeatMateCrossSuit`
through `Gap.noSeatMate_of_residuals`. -/
theorem noSeatMate_of_mateBarrier (h1 : MateRaiseBarrier) (h2 : NonTwinResidual)
    (h3 : Gap.RelocationResidual) : Blocks.NoSeatMateCrossSuit :=
  Gap.noSeatMate_of_residuals (sChainMateResidual_of_mateBarrier h1 h2) h3

/-! ## §4. The no-go: the ledger (`rungAt`) form of the twin barrier is *not*
weaker than the licence form, and the pin is the *negation* of the barrier -/

/-- **`TwinRungBarrier`** — THE LEDGER SPELLING OF THE TWIN RESIDUAL: at every
point where the tail fires `raise d.twin` and the twin is S-live, the twin
suit's rung differs from `d.rank.toIdx`.  This is the strongest residual of
"twin-pin shape" (a `rungAt` inequality) that the twin case admits. -/
def TwinRungBarrier : Prop :=
  ∀ (u v : State) (ρ pre γ tail : List Move) (c d : Card) (b : Base)
    (A₀ B₀ P₀ L : State),
    u.WF → SSaturated v → ShufflePlayW u ρ v →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
    ρ = pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))) →
    Canon.FreeOnly γ → c.suit ≠ d.suit →
    ShufflePlayW u pre A₀ → State.step A₀ (Move.tabToFound c) = some B₀ →
    ShufflePlayW B₀ γ P₀ → State.step P₀ (Move.foundToTab d b) = some L →
    ∀ (s1 s2 : List Move) (A Z : State),
      tail = s1 ++ Move.tabToFound d.twin :: s2 →
      ShufflePlayW L s1 A →
      (CanRaiseS A d.twin ∨ CanRaiseS A d.twin.twin) →
      State.step A (Move.tabToFound d.twin) = some Z →
      rungAt A (d.twin.suit) ≠ d.rank.toIdx

/-- **NO-GO: THE LEDGER RESIDUAL IS THE LICENCE RESIDUAL.**  `TwinRungBarrier`
and `MateRaiseBarrier` are *equivalent*: the rung equality the barrier denies is
forced by the fired raise it is supposed to forbid (§1).  Hence no `rungAt`
inequality can be strictly weaker, and in particular no twin-pin row (which
asserts the equality) can imply the barrier. -/
theorem twinRungBarrier_iff : TwinRungBarrier ↔ MateRaiseBarrier := by
  constructor
  · intro hb u v ρ pre γ tail c d b A₀ B₀ P₀ L hwf hv hplay hmin heq hfree hsu hpre
      hstepR hγ hpull s1 s2 A Z htail hp hlive hstep
    exact (hb u v ρ pre γ tail c d b A₀ B₀ P₀ L hwf hv hplay hmin heq hfree hsu hpre
      hstepR hγ hpull s1 s2 A Z htail hp hlive hstep) (mate_raise_rungAt hstep)
  · intro hm u v ρ pre γ tail c d b A₀ B₀ P₀ L hwf hv hplay hmin heq hfree hsu hpre
      hstepR hγ hpull s1 s2 A Z htail hp hlive hstep
    exact (hm u v ρ pre γ tail c d b A₀ B₀ P₀ L hwf hv hplay hmin heq hfree hsu hpre
      hstepR hγ hpull s1 s2 A Z htail hp hlive hstep).elim

/-- **THE PIN IS THE EXACT NEGATION OF THE ONLY LEDGER RESIDUAL.**  At any state
where a `raise d.twin` fires, the campaign's twin-pin equality holds; therefore
the ledger residual fails there.  Contrapositive reading: a hypothesis that
*pins* the twin's rung at the tail's raise points is a hypothesis that the twin
case *occurs*, so it cannot be used to exclude it. -/
theorem pin_forbids_ledgerBarrier_at_raise {A Z : State} {d : Card}
    (hstep : State.step A (Move.tabToFound d.twin) = some Z) :
    ¬ (rungAt A (d.twin.suit) ≠ d.rank.toIdx) :=
  fun hne => hne (mate_raise_rungAt hstep)

/-! ## §5. Gates: what the connection does *not* consume -/

/-- The twin residual never mentions the start state's saturation: `NonTwinResidual`
and `MateRaiseBarrier` are one-sided in `v` (`ssatU` is an unused hypothesis), as
is `Gap.SChainMateResidual`.  This row records it in the kernel. -/
theorem sChainMateResidual_ssatU_irrelevant (h : Gap.SChainMateResidual)
    (u v : State) (ρ pre γ tail : List Move) (c d : Card) (b : Base)
    (A₀ B₀ P₀ L : State) (ssatU : SSaturated u)
    (hwf : u.WF) (hv : SSaturated v) (hplay : ShufflePlayW u ρ v)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length)
    (heq : ρ = pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))))
    (hfree : Canon.FreeOnly γ) (hsu : c.suit ≠ d.suit)
    (hpre : ShufflePlayW u pre A₀) (hstepR : State.step A₀ (Move.tabToFound c) = some B₀)
    (hγ : ShufflePlayW B₀ γ P₀) (hpull : State.step P₀ (Move.foundToTab d b) = some L)
    (z : Card) (s1 s2 : List Move) (A Z : State)
    (hle : z.rank.toIdx ≤ d.rank.toIdx) (htail : tail = s1 ++ Move.tabToFound z :: s2)
    (hp : ShufflePlayW L s1 A) (hlive : CanRaiseS A z ∨ CanRaiseS A z.twin)
    (hstep : State.step A (Move.tabToFound z) = some Z) : z = d :=
  h u v ρ pre γ tail c d b A₀ B₀ P₀ L hwf hv hplay hmin heq hfree hsu hpre hstepR hγ
    hpull z s1 s2 A Z hle htail hp hlive hstep

/-- The twin clause is *rung-difference-blind*: it asks for a fact about a single
state `A` in the tail, so it is unaffected by `RungEq`/`RungDiffers` hypotheses on
the endpoints `u`, `v` (the campaign's `SatDifferForkWF` gate). -/
theorem mateBarrier_rungBlind (h : MateRaiseBarrier)
    (u v : State) (ρ pre γ tail : List Move) (c d : Card) (b : Base)
    (A₀ B₀ P₀ L : State)
    (_rungSame : ∀ σ, rungAt u σ = rungAt v σ)
    (hwf : u.WF) (hv : SSaturated v) (hplay : ShufflePlayW u ρ v)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length)
    (heq : ρ = pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))))
    (hfree : Canon.FreeOnly γ) (hsu : c.suit ≠ d.suit)
    (hpre : ShufflePlayW u pre A₀) (hstepR : State.step A₀ (Move.tabToFound c) = some B₀)
    (hγ : ShufflePlayW B₀ γ P₀) (hpull : State.step P₀ (Move.foundToTab d b) = some L)
    (s1 s2 : List Move) (A Z : State)
    (htail : tail = s1 ++ Move.tabToFound d.twin :: s2)
    (hp : ShufflePlayW L s1 A)
    (hlive : CanRaiseS A d.twin ∨ CanRaiseS A d.twin.twin)
    (hstep : State.step A (Move.tabToFound d.twin) = some Z) : False :=
  h u v ρ pre γ tail c d b A₀ B₀ P₀ L hwf hv hplay hmin heq hfree hsu hpre hstepR hγ
    hpull s1 s2 A Z htail hp hlive hstep

/-! ## §6. THE CONNECTION: `LandingTwinLive` at the corridor's pull landing plus
`Gap.SChainMateResidual` force the tail to raise `d` itself

This is the sharpest form of the link.  `Gap.SChainMateResidual` is a `∀` over the
tail's S-raises; `Gap.skill_chain` turns a *twin* S-live at the landing into such
a raise.  The residual then renames the terminal of that chain to `d`.  So the
campaign's landing liveness (`CanRaiseS L d.twin`) cannot coexist with the
residual and a `d`-raise-free tail — which is exactly the mate branch's shape. -/

/-- Deterministic splitting: a suffix of a witness shuffle starting at a known
intermediate state is a witness shuffle from that state. -/
theorem shufflePlayW_suffix {P S T : State} {l₁ l₂ : List Move}
    (h : ShufflePlayW P (l₁ ++ l₂) T) (h₁ : ShufflePlayW P l₁ S) :
    ShufflePlayW S l₂ T := by
  obtain ⟨M, hpreM, htailM⟩ := ValleyElim.ShufflePlayW_split h l₁ l₂ rfl
  have hM : M = S := by
    have r1 := Walk_run (fun st m => reversibleAtW st m) hpreM
    have r2 := Walk_run (fun st m => reversibleAtW st m) h₁
    exact Option.some.inj (r1.symm.trans r2)
  subst hM
  exact htailM

/-- **THE CORRIDOR'S TAIL AS A WITNESS SHUFFLE FROM THE PULL LANDING.**  Peels
`pre`, the raise `c`, the free interior `γ` and the pull `d b` off the corridor
play, matching each intermediate state against the corridor's own data by
step-determinism. -/
theorem corridor_tail_play {u v : State} {ρ pre γ tail : List Move} {c d : Card}
    {b : Base} {A₀ B₀ P₀ L : State}
    (hplay : ShufflePlayW u ρ v)
    (heq : ρ = pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))))
    (hpre : ShufflePlayW u pre A₀) (hstepR : State.step A₀ (Move.tabToFound c) = some B₀)
    (hγ : ShufflePlayW B₀ γ P₀) (hpull : State.step P₀ (Move.foundToTab d b) = some L) :
    ShufflePlayW L tail v := by
  have hplay' : ShufflePlayW u
      (pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail)))) v := by
    rw [← heq]; exact hplay
  -- `pre`
  obtain ⟨M, hpreM, hrestM⟩ := ValleyElim.ShufflePlayW_split hplay' pre _ rfl
  have hMA : M = A₀ := by
    have r1 := Walk_run (fun st m => reversibleAtW st m) hpreM
    have r2 := Walk_run (fun st m => reversibleAtW st m) hpre
    exact Option.some.inj (r1.symm.trans r2)
  subst hMA
  -- the raise
  obtain ⟨B', -, hstepB, hrestB⟩ := Bubble.walk_cons_inv hrestM
  have hBB : B' = B₀ := Option.some.inj (hstepB.symm.trans hstepR)
  subst hBB
  -- the free interior
  obtain ⟨P', hγP, hrestP⟩ :=
    ValleyElim.ShufflePlayW_split hrestB γ (Move.foundToTab d b :: tail) rfl
  have hPP : P' = P₀ := by
    have r1 := Walk_run (fun st m => reversibleAtW st m) hγP
    have r2 := Walk_run (fun st m => reversibleAtW st m) hγ
    exact Option.some.inj (r1.symm.trans r2)
  subst hPP
  -- the pull
  obtain ⟨L', -, hstepL, htailL⟩ := Bubble.walk_cons_inv hrestP
  have hLL : L' = L := Option.some.inj (hstepL.symm.trans hpull)
  subst hLL
  exact htailL

/-- **THE TWIN AT THE LANDING IS CARRIED BY `SChainMateResidual` INTO A RAISE OF
`d`.**  Given the corridor, a `d.twin` that is S-live at the pull landing drives
`Gap.skill_chain`; `Gap.SChainMateResidual` forces the chain's terminal card to
be `d`.  Hence the tail contains `raise d` *at a point where `d` is S-live or its
twin is*. -/
theorem twinLive_landing_forces_raise_d
    (hres : Gap.SChainMateResidual)
    {u v : State} {ρ pre γ tail : List Move} {c d : Card} {b : Base}
    {A₀ B₀ P₀ L : State}
    (hwf : u.WF) (hv : SSaturated v) (hplay : ShufflePlayW u ρ v)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length)
    (heq : ρ = pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))))
    (hfree : Canon.FreeOnly γ) (hsu : c.suit ≠ d.suit)
    (hpre : ShufflePlayW u pre A₀) (hstepR : State.step A₀ (Move.tabToFound c) = some B₀)
    (hγ : ShufflePlayW B₀ γ P₀) (hpull : State.step P₀ (Move.foundToTab d b) = some L)
    (htwin : CanRaiseS L d.twin) :
    ∃ (s1 s2 : List Move) (A Z : State),
      tail = s1 ++ Move.tabToFound d :: s2 ∧ ShufflePlayW L s1 A ∧
      (CanRaiseS A d ∨ CanRaiseS A d.twin) ∧
      State.step A (Move.tabToFound d) = some Z ∧ ShufflePlayW Z s2 v := by
  have hA₀ : A₀.WF := SatDifferCensus.ShufflePlayW.wf_end hpre hwf
  have hB₀ : B₀.WF := step_wf hA₀ hstepR
  have hP₀ : P₀.WF := SatDifferCensus.ShufflePlayW.wf_end hγ hB₀
  have hLwf : L.WF := step_wf hP₀ hpull
  have htailplay : ShufflePlayW L tail v :=
    corridor_tail_play hplay heq hpre hstepR hγ hpull
  obtain ⟨z, s1, s2, A, Z, hle, htailEq, hp, hlive, hstep, hpost⟩ :=
    Gap.skill_chain hLwf hv htwin htailplay
  have hle' : z.rank.toIdx ≤ d.rank.toIdx := by
    rw [Card.twin_rank] at hle
    exact hle
  have hz : z = d :=
    hres u v ρ pre γ tail c d b A₀ B₀ P₀ L hwf hv hplay hmin heq hfree hsu hpre hstepR
      hγ hpull z s1 s2 A Z hle' htailEq hp hlive hstep
  subst hz
  exact ⟨s1, s2, A, Z, htailEq, hp, hlive, hstep, hpost⟩

/-- **THE INCOMPATIBILITY — THE MAIN NEGATIVE RESULT.**  `Gap.SChainMateResidual`
together with the campaign's landing twin-liveness (`CanRaiseS L d.twin`, the
conclusion of `Landing.LandingTwinLive` read at the corridor's pull) is
*inconsistent with a tail that never re-raises `d`*.  But `Gap.king_mate_first_kill_buried`
(`Orig2/ForkGap.lean:388`) says the mate branch is exactly such a `d`-raise-free
tail.  So the twin pin is not a lever on the residual: it *supplies the
residual's counter-hypothesis*. -/
theorem not_sChainMate_of_twinLive_and_noRaiseD
    (hres : Gap.SChainMateResidual)
    {u v : State} {ρ pre γ tail : List Move} {c d : Card} {b : Base}
    {A₀ B₀ P₀ L : State}
    (hwf : u.WF) (hv : SSaturated v) (hplay : ShufflePlayW u ρ v)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length)
    (heq : ρ = pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))))
    (hfree : Canon.FreeOnly γ) (hsu : c.suit ≠ d.suit)
    (hpre : ShufflePlayW u pre A₀) (hstepR : State.step A₀ (Move.tabToFound c) = some B₀)
    (hγ : ShufflePlayW B₀ γ P₀) (hpull : State.step P₀ (Move.foundToTab d b) = some L)
    (htwin : CanRaiseS L d.twin)
    (hno : ∀ s1 s2 : List Move, tail ≠ s1 ++ Move.tabToFound d :: s2) : False := by
  obtain ⟨s1, s2, -, -, htailEq, -⟩ :=
    twinLive_landing_forces_raise_d hres hwf hv hplay hmin heq hfree hsu hpre hstepR hγ
      hpull htwin
  exact hno s1 s2 htailEq

/-- **THE CORRIDOR'S OWN `d.suit` DIP.**  The pull leaves `d.suit`'s rung one
lower than at its origin: `rungAt L d.suit = d.rank.toIdx` while
`rungAt P₀ d.suit = d.rank.toIdx + 1`.  This is why the campaign's rung-difference
gate (`SatDifferForkWF`'s differing-rung conjunct) is *automatically* satisfied by
the corridor's pull, and hence why the twin clause needs no rung-difference
hypothesis: the dip at `d.suit` is already there. -/
theorem rung_d_suit_at_pull {P L : State} {d : Card} {b : Base} (hP : P.WF)
    (hstep : State.step P (Move.foundToTab d b) = some L) :
    rungAt P d.suit = d.rank.toIdx + 1 ∧ rungAt L d.suit = d.rank.toIdx := by
  obtain ⟨c', htop, hc', -, -⟩ := step_foundToTab_inv hstep
  rw [hc'] at htop
  have h1 : d.rank.toIdx + 1 = rungAt P d.suit :=
    SatDifferCensus.foundTop_rank_succ hP htop
  have hcan : CanRaise L d := ValleyStep.pull_card_canRaise hP hstep
  exact ⟨h1.symm, TwinKit.nextUp_true_iff.mp hcan.1⟩

/-- **THE RESIDUAL FORCES THE LANDING TWIN TO BE *DEAD*.**  The sharpest derived
form of §6: under `Gap.SChainMateResidual`, a corridor whose tail never re-raises
`d` cannot have the pulled card's twin S-live at the pull landing.  So the
campaign's `LandingTwinLive` — read at the corridor's pull letter, where it is
exactly `CanRaiseS L d.twin` — is *excluded* by the residual in the mate
configuration, and therefore cannot be used to prove it. -/
theorem not_twinLive_of_residual_and_noRaiseD
    (hres : Gap.SChainMateResidual)
    {u v : State} {ρ pre γ tail : List Move} {c d : Card} {b : Base}
    {A₀ B₀ P₀ L : State}
    (hwf : u.WF) (hv : SSaturated v) (hplay : ShufflePlayW u ρ v)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length)
    (heq : ρ = pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))))
    (hfree : Canon.FreeOnly γ) (hsu : c.suit ≠ d.suit)
    (hpre : ShufflePlayW u pre A₀) (hstepR : State.step A₀ (Move.tabToFound c) = some B₀)
    (hγ : ShufflePlayW B₀ γ P₀) (hpull : State.step P₀ (Move.foundToTab d b) = some L)
    (hno : ∀ s1 s2 : List Move, tail ≠ s1 ++ Move.tabToFound d :: s2) :
    ¬ CanRaiseS L d.twin :=
  fun htwin =>
    not_sChainMate_of_twinLive_and_noRaiseD hres hwf hv hplay hmin heq hfree hsu hpre
      hstepR hγ hpull htwin hno

/-! ## §7. Why the pin lane is the *enabling* lane: in the campaign's own split the
raise letter IS the twin raise -/

/-- **THE CAMPAIGN'S SPLIT RAISE IS THE PULLED CARD'S TWIN.**  Re-export of
`SplitKit.splitTwin_of_livePair_block` (`Orig2/Fork/ForkSplitResidual.lean:360`):
from `SplitLivePair` (the live set at the bottom is the raise card's twin pair)
and `SplitBlock`, the raise card `d` of the split's right leg is exactly `c.twin`,
where `c` is the *pulled* card.  So in the campaign's decomposition the split's
raise is `raise c.twin` — the same "raise the twin of a pulled card" shape that
`Gap.SChainMateResidual`'s surviving case excludes.  `Landing.LandingTwinLive`
(`CanRaiseS B c.twin` at the pull's landing) is precisely the datum that makes it
fire. -/
theorem campaign_split_raise_eq_pulled_twin
    (hl : SplitKit.SplitLivePair) (hb : SplitKit.SplitBlock) :
    SplitKit.SplitTwin :=
  SplitKit.splitTwin_of_livePair_block hl hb

/-- The same row, in readable form at a single split. -/
theorem split_raise_eq_twin (hl : SplitKit.SplitLivePair) (hb : SplitKit.SplitBlock)
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail) : d = c.twin :=
  campaign_split_raise_eq_pulled_twin hl hb u v ρ F left right c d b pre post tail hs

/-- **THE PIN IS THE `+1` COLUMN, AT THE BOTTOM AND AT THE MATE RAISE.**  Combined
reading of §1 and §2: at the split's bottom the twin suit's rung is the twin's
rank index (`SplitTwinRungPin`), and at the mate raise it is the same number —
then the raise takes it to `+1`.  So the mate branch moves the *pinned* coordinate
strictly upward: no rung inequality can forbid it. -/
theorem pin_and_mate_raise_agree {F A Z : State} {c d : Card}
    (hpin : F.nextUp c.twin = true)
    (hstep : State.step A (Move.tabToFound d.twin) = some Z) (hdc : d = c.twin) :
    rungAt F c.twin.suit = rungAt A d.twin.suit ∧
      rungAt Z d.twin.suit = rungAt A d.twin.suit + 1 := by
  refine ⟨?_, mate_raise_completes hstep⟩
  have h1 := splitTwinRungPin_gives_rung hpin
  have h2 := mate_raise_rungAt hstep
  rw [h1, h2, hdc, Card.twin_rank]

/-! ## §8. Axiom battery

Expected: every row `[]`, `[propext]` or `[propext, Quot.sound]`; no `sorryAx`,
no `Classical.choice`, no `Lean.ofReduceBool`. -/

#print axioms TwinLink.twin_suit_ne
#print axioms TwinLink.mate_raise_rungAt
#print axioms TwinLink.mate_raise_nextUp
#print axioms TwinLink.mate_raise_completes
#print axioms TwinLink.campaign_pin_of_twinLive
#print axioms TwinLink.landingTwinLive_gives_pin
#print axioms TwinLink.splitTwinRungPin_gives_rung
#print axioms TwinLink.rungAt_twin_of_pull
#print axioms TwinLink.rungAt_twin_of_freeOnly
#print axioms TwinLink.rungAt_twin_landing_eq_image
#print axioms TwinLink.sChainMateResidual_iff
#print axioms TwinLink.sChainMateResidual_of_mateBarrier
#print axioms TwinLink.noSeatMate_of_mateBarrier
#print axioms TwinLink.twinRungBarrier_iff
#print axioms TwinLink.pin_forbids_ledgerBarrier_at_raise
#print axioms TwinLink.rung_d_suit_at_pull
#print axioms TwinLink.not_twinLive_of_residual_and_noRaiseD
#print axioms TwinLink.shufflePlayW_suffix
#print axioms TwinLink.corridor_tail_play
#print axioms TwinLink.twinLive_landing_forces_raise_d
#print axioms TwinLink.not_sChainMate_of_twinLive_and_noRaiseD
#print axioms TwinLink.campaign_split_raise_eq_pulled_twin
#print axioms TwinLink.split_raise_eq_twin
#print axioms TwinLink.pin_and_mate_raise_agree

#check @TwinLink.NonTwinResidual
#check @TwinLink.MateRaiseBarrier
#check @TwinLink.TwinRungBarrier
#check @TwinLink.sChainMateResidual_iff
#check @TwinLink.twinRungBarrier_iff
#check @TwinLink.twinLive_landing_forces_raise_d
#check @TwinLink.not_sChainMate_of_twinLive_and_noRaiseD

end TwinLink


