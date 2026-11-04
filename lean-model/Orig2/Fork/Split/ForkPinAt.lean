import Orig2.Fork.Class.ForkTwinAt
import Orig2.Fork.Split.ForkMountain
import Orig2.Fork.Split.ForkLedger

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkPinAt — the pin clause: transport, the deep-endpoint read, and the
LEFT-LEG NO-GO

READ-ONLY scratch card (`Temp/`).  No source file is modified; nothing is
committed.  Zero `sorry`, zero `Classical.choice`, zero `native_decide`;
axiom battery at the tail.

## What this card does

The pin is `TwinKit.SplitTwinRungPin` (`F.nextUp c.twin = true` at every
split bottom), equivalently `PairRungKit.SplitTwinRungGe`
(`rungAt F c.suit ≤ rungAt F c.twin.suit`, `Orig2/Fork/Class/ForkPairRung.lean:168`,
under `SplitBlock`).

1. **§1–§2 transport.**  The twin suit's rung is *constant across the pull and
   the free tail*, so the pin reads identically at the pull's landing `B`, at
   the pre-pull state `A'`, and at the bottom `F`
   (`twin_rung_pull_invariant`, `pin_iff_prePullGap`).  At `A'` the card `c` is
   the foundation top of its suit, so the own-suit rung is `c.rank.toIdx + 1`
   (`prePull_own_rung_sharp`): the residual is the single Nat comparison
   `c.rank.toIdx ≤ rungAt A' c.twin.suit`.

2. **§3 the deep-endpoint read.**  When the split's prefix `pre` does not move
   the twin suit's rung (in particular whenever `pre` is free — the *typical*
   case, `pre` being the play's free head), the pin is *exactly* a statement
   about the SATURATED deep endpoint `u`:

       SplitTwinRungPin  ↔  c.rank.toIdx ≤ rungAt u c.twin.suit   (under SplitBlock)

   (`pin_iff_deepGe_of_split`, `pin_iff_deepGe_of_free_pre`).  This is the form
   in which the deep endpoint's saturation `SSaturated u` can be consumed.

3. **§4 THE LEFT-LEG NO-GO (new, kernel-checked).**  The gadget `L`
   (`L_u → L_B → L_F`) carries *every* datum the left leg + the block can
   supply — `L_u.WF` and `SSaturated L_u`, a genuine reversible pull
   `L_u --pull 5H--> L_B`, a genuine reversible free tail `L_B --slide--> L_F`,
   `L_F.WF`, `¬ CanRaise L_F 5H` (the block) and `L_F.pileOfTop 5H.twin ≠ none`
   (the twin tops a pile) — and yet the pin FAILS
   (`L_pin_fails`) and there is **no raisable card at all** at `L_F`
   (`L_F_no_raisable`).  Hence

       ¬ (left-leg data + SplitBlock + twin-top ⟹ pin)   (`left_leg_data_not_enough`)

   so no proof of the pin can run on the deep endpoint / the left leg / the
   block: **the far leg's raise card `d` is load-bearing**.  This kills
   "attack idea 1" (deep-endpoint saturation alone) as a sufficient route and
   localises the residual exactly: the pin needs the *right* leg.

4. **§5 what the pin forces at the saturated endpoint.**  With the pin, the
   twin suit's rung is `c.rank.toIdx`, so `c.twin` is next-up at `u`; since `u`
   is saturated, `c.twin` is *not* an exposed seat at `u`
   (`twin_not_exposed_at_deep_of_split`).  Since the block forces `c.twin` to top
   a pile at `F`, some letter must move the twin's seat: the pin is a
   cover/uncover statement, not rung arithmetic.  §6 adds that a pin-failing
   bottom must raise a non-twin card (`pin_fails_raise_ne_twin`).

## What is NOT proved

`SplitTwinRungPin` itself.  §4 shows why the deep-endpoint route cannot close
it; the exact reduced residual is `PinAt.DeepTwinFrontier` (§3b), i.e. the
single inequality `c.rank.toIdx ≤ rungAt u c.twin.suit` read at the saturated
deep endpoint (the prefix must not move the twin suit's rung; the free-prefix
case is the generic one, and `PinAt.FreePreSplit` names it).

## No circular hypothesis

Nothing here uses `SplitLivePair`, `LandingLivePair`, `LandingAll`,
`ValleyElimNonfork`, `SplitPairRungEq` or `RungGe.SplitTwinLiveAtBottom`;
`SplitBlock` is used only for its *free* half (`¬ CanRaise F c` ⟹
`rungAt F c.twin.suit ≤ c.rank.toIdx`, `PairRungKit.rungAt_twin_le_of_block`).
-/

namespace PinAt

open TwinKit

/-! ## §1. Kit -/

theorem twin_rung_pull_invariant {A' B F : State} {c : Card} {b : Base}
    {post : List Move}
    (hstep : State.step A' (Move.foundToTab c b) = some B)
    (hpost : ShufflePlayW B post F)
    (hfree : ∀ m ∈ post, ValleyElim.FreeMove m) :
    rungAt F c.twin.suit = rungAt A' c.twin.suit :=
  (PairRungKit.prePull_twin_rung hstep hpost hfree).symm

theorem pin_iff_ge_at_prePull {A' B F : State} {c : Card} {b : Base}
    {post : List Move}
    (hA' : A'.WF) (hstep : State.step A' (Move.foundToTab c b) = some B)
    (hpost : ShufflePlayW B post F) (hfree : ∀ m ∈ post, ValleyElim.FreeMove m)
    (hblock : ¬ CanRaise F c) (hS : CanRaiseS F c) :
    (rungAt F c.twin.suit = c.rank.toIdx) ↔
      (c.rank.toIdx ≤ rungAt A' c.twin.suit) := by
  have hle : rungAt F c.twin.suit ≤ c.rank.toIdx :=
    PairRungKit.rungAt_twin_le_of_block (SatDifferCensus.ShufflePlayW.wf_end hpost
      (step_wf hA' hstep)) hS hblock
  have htau : rungAt F c.twin.suit = rungAt A' c.twin.suit :=
    twin_rung_pull_invariant hstep hpost hfree
  constructor <;> intro h <;> omega

/-! ## §3b. The same residual read at the SATURATED DEEP ENDPOINT `u` -/

/-- **THE PIN AT THE DEEP ENDPOINT.**  If the split's prefix does not move the
twin suit's rung (`rungAt u c.twin.suit = rungAt A' c.twin.suit`), then the pin
at the bottom is exactly `c.rank.toIdx ≤ rungAt u c.twin.suit`: one Nat
comparison about the saturated endpoint `u`'s foundation vector. -/
theorem pin_iff_deepGe_of_split
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (htrans : ∀ A' : State, ShufflePlayW u pre A' →
      rungAt u c.twin.suit = rungAt A' c.twin.suit)
    (hblock : ¬ CanRaise F c) :
    (rungAt F c.twin.suit = c.rank.toIdx) ↔
      (c.rank.toIdx ≤ rungAt u c.twin.suit) := by
  obtain ⟨-, hSc, -, -⟩ := SplitKit.splitHyp_green h
  obtain ⟨A', B, hpre, hstep, hpost⟩ := PairRungKit.split_pre_pull_data h
  obtain ⟨huwf, -, -, -, -, -, -, -, -, -, hfree, -⟩ := h
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  have hge := pin_iff_ge_at_prePull hA' hstep hpost hfree hblock hSc
  have hr := htrans A' hpre
  rw [hge, ← hr]

theorem deep_upper_of_block
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (htrans : ∀ A' : State, ShufflePlayW u pre A' →
      rungAt u c.twin.suit = rungAt A' c.twin.suit)
    (hblock : ¬ CanRaise F c) :
    rungAt u c.twin.suit ≤ c.rank.toIdx := by
  obtain ⟨-, hSc, -, -⟩ := SplitKit.splitHyp_green h
  obtain ⟨A', B, hpre, hstep, hpost⟩ := PairRungKit.split_pre_pull_data h
  obtain ⟨huwf, -, -, -, -, -, -, -, -, -, hfree, -⟩ := h
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  have hle : rungAt F c.twin.suit ≤ c.rank.toIdx :=
    PairRungKit.rungAt_twin_le_of_block
      (SatDifferCensus.ShufflePlayW.wf_end hpost (step_wf hA' hstep)) hSc hblock
  have htau : rungAt F c.twin.suit = rungAt A' c.twin.suit :=
    twin_rung_pull_invariant hstep hpost hfree
  have hr := htrans A' hpre
  omega

/-- **`DeepTwinFrontier`** — THE EXACT REDUCED RESIDUAL, read at the SATURATED
DEEP ENDPOINT.  At every split whose prefix leaves the twin suit's rung alone,
the twin suit already carries the exodus card's rank index at `u`:

    `c.rank.toIdx ≤ rungAt u c.twin.suit`.

This is *not* a restatement of the pin: it mentions only `u` and the pulled
card `c` — no bottom, no landing, no play word, no licence.  The opposite
inequality is free (`deep_upper_of_block`), so the residual is the single
statement that the twin suit is not *behind* at the deep endpoint. -/
def DeepTwinFrontier : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State) (left right : List Move)
    (c d : Card) (b : Base) (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    (∀ A' : State, ShufflePlayW u pre A' →
      rungAt u c.twin.suit = rungAt A' c.twin.suit) →
    c.rank.toIdx ≤ rungAt u c.twin.suit

/-- **`FreePreSplit`** — every split's prefix is free.  This is the generic
case (`LedgerKit.exodus_cut` gives it for the split whose pull is the play's
first non-free letter); it is stated explicitly here so that the reduction
below carries no hidden hypothesis. -/
def FreePreSplit : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State) (left right : List Move)
    (c d : Card) (b : Base) (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    ∀ m ∈ pre, ValleyElim.FreeMove m

/-- **THE PIN IS THE DEEP-ENDPOINT FRONTIER** (given the block's free half).
`SplitTwinRungPin` and `DeepTwinFrontier` are the same statement whenever the
splits' prefixes are free; each direction is `pin_iff_deepGe_of_split`. -/
theorem splitTwinRungPin_iff_deepTwinFrontier
    (hb : SplitKit.SplitBlock) (hpre : FreePreSplit) :
    TwinKit.SplitTwinRungPin ↔ DeepTwinFrontier := by
  constructor
  · intro hpin u v ρ F left right c d b pre post tail hsplit htrans
    have hF : (rungAt F c.twin.suit = c.rank.toIdx) := by
      have := hpin u v ρ F left right c d b pre post tail hsplit
      exact nextUp_true_iff.mp this
    exact (pin_iff_deepGe_of_split hsplit htrans
      (hb u v ρ F left right c d b pre post tail hsplit)).mp hF
  · intro hdeep u v ρ F left right c d b pre post tail hsplit
    have hblock : ¬ CanRaise F c := hb u v ρ F left right c d b pre post tail hsplit
    have htrans : ∀ A' : State, ShufflePlayW u pre A' →
        rungAt u c.twin.suit = rungAt A' c.twin.suit :=
      fun A' hplay => by
        have hh := ValleyElim.rungAt_eq_of_free_play hplay
          (hpre u v ρ F left right c d b pre post tail hsplit) c.twin.suit
        exact hh.symm
    have hge := hdeep u v ρ F left right c d b pre post tail hsplit htrans
    exact nextUp_true_iff.mpr
      ((pin_iff_deepGe_of_split hsplit htrans hblock).mpr hge)

/-! ## §4. THE LEFT-LEG NO-GO: the far leg's raise card is load-bearing -/

def AH : Card := ⟨.heart, .ace⟩
def H2 : Card := ⟨.heart, .two⟩
def H3 : Card := ⟨.heart, .three⟩
def H4 : Card := ⟨.heart, .four⟩
def H5 : Card := ⟨.heart, .five⟩
def D5 : Card := ⟨.diamond, .five⟩
def C6 : Card := ⟨.club, .six⟩
def S4 : Card := ⟨.spade, .four⟩
def S6 : Card := ⟨.spade, .six⟩

/-- The nine cards the gadget puts on the board; the rest is stock. -/
def fixed : List Card := [AH, H2, H3, H4, H5, D5, C6, S4, S6]

/-- The 43-card stock (the complement of `fixed`). -/
def rest : List Card := Card.universe.filter (fun c => !(decide (c ∈ fixed)))

/-- Board builder: hearts founded to `hfound`, `p0`/`p1` as given, rest stock. -/
def mkState (hfound p0 p1 : List Card) : State :=
  { found := fun s => match s with
      | .heart => hfound
      | _ => []
    piles := fun a => match a with
      | .p0 => ⟨[], p0⟩
      | .p1 => ⟨[], p1⟩
      | _ => ⟨[], []⟩
    stock := rest
    waste := []
    drawStep := 1 }

/-- **`L_u`** — the deep endpoint: hearts founded to the five, `6S` alone on
`p0` (the pull's base), `p1 = [6C, 5D, 4S]` (the twin `5D` covered by `4S`),
everything else in the stock. -/
def L_u : State := mkState [AH, H2, H3, H4, H5] [S6] [C6, D5, S4]

/-- **`L_B`** — the pull's landing: `5H` now tops `p0` on `6S`. -/
def L_B : State := mkState [AH, H2, H3, H4] [S6, H5] [C6, D5, S4]

/-- **`L_F`** — the bottom: the free tail's slide moved `4S` off `5D` onto
`5H`; `5D` now tops `p1`, `5H` is covered. -/
def L_F : State := mkState [AH, H2, H3, H4] [S6, H5, S4] [C6, D5]

/-! ### §4a. Well-formedness -/

theorem not_canRaise_of_ssaturated {st : State} (h : SSaturated st) (c : Card) :
    ¬ CanRaise st c :=
  fun hc => h c (CanRaiseS.now c hc)

/-- **AT THE SATURATED DEEP ENDPOINT, THE PIN MAKES THE TWIN UNEXPOSED.**  If
the twin suit sits at `c`'s rank index at `u`, then `c.twin` is next-up there,
so saturation forbids it having an exposed seat (company below, or a bare-king
seat). -/
theorem twin_not_exposed_of_ssaturated {u : State} {c : Card}
    (hsat : SSaturated u) (hpin : rungAt u c.twin.suit = c.rank.toIdx) :
    ¬ (∃ a : Anchor, u.pileOfTop c.twin = some a ∧
        (chop (u.piles a).faceUp ≠ [] ∨
          ((u.piles a).hidden = [] ∧ c.twin.rank = Rank.king))) := by
  rintro ⟨a, htop, hseat⟩
  exact not_canRaise_of_ssaturated hsat c.twin
    ⟨nextUp_true_iff.mpr hpin, a, htop, hseat⟩

/-- **THE PIN FORCES THE TWIN TO BE COVERED AT THE DEEP ENDPOINT.**  Combine
`saturation of u` with the pin read at `u` (§3b): `c.twin` cannot be an exposed
seat at `u`.  Since `SplitBlock` forces `c.twin` to TOP a pile at the bottom
(`PairRungKit.pileOfTop_twin_of_block`), the free letters between `u` and `F`
must UNCOVER it: the pin is a cover/uncover statement, not rung arithmetic. -/
theorem twin_not_exposed_at_deep_of_split
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (htrans : ∀ A' : State, ShufflePlayW u pre A' →
      rungAt u c.twin.suit = rungAt A' c.twin.suit)
    (hpin : rungAt F c.twin.suit = c.rank.toIdx) :
    ¬ (∃ a : Anchor, u.pileOfTop c.twin = some a ∧
        (chop (u.piles a).faceUp ≠ [] ∨
          ((u.piles a).hidden = [] ∧ c.twin.rank = Rank.king))) := by
  have hk := h
  obtain ⟨huwf, hsu, -, -, -, -, -, -, -, -, -, -⟩ := hk
  have hdeep : rungAt u c.twin.suit = c.rank.toIdx := by
    obtain ⟨A', B, hpre, hstep, hpost⟩ := PairRungKit.split_pre_pull_data h
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hfree, -⟩ := h
    have htau : rungAt F c.twin.suit = rungAt A' c.twin.suit :=
      twin_rung_pull_invariant hstep hpost hfree
    have hr := htrans A' hpre
    omega
  exact twin_not_exposed_of_ssaturated hsu hdeep

/-! ## §6. Where the residual lives: the non-twin mechanism corner -/

/-- **A PIN-FAILING BOTTOM RAISES A NON-TWIN CARD.**  The census mechanism
`d = c.twin` already implies the pin (`PairRungKit.pin_of_raise_eq_twin`), so
the pin's failure forces the raise card off the twin: the residual is strictly
inside the `d ≠ c.twin` corner. -/
theorem pin_fails_raise_ne_twin
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hfail : rungAt F c.twin.suit ≠ c.rank.toIdx) : d ≠ c.twin := by
  intro hd
  have heq := PairRungKit.pin_of_raise_eq_twin h hd
  have hsig : rungAt F c.suit = c.rank.toIdx :=
    canRaiseS_rung (SplitKit.splitHyp_green h).2.1
  exact hfail (by rw [heq, hsig])

/-! ## §6b. The residual pushes the one-sided rung inequality -/

/-- **`DeepTwinFrontier` ⟹ `SplitTwinRungGe`.**  The deep-endpoint residual
gives the pin (under the block's free half), and the pin gives the campaign's
one-sided rung inequality.  Nothing here uses `SplitLivePair`,
`LandingLivePair`, `LandingAll`, `ValleyElimNonfork`, `SplitPairRungEq` or
`RungGe.SplitTwinLiveAtBottom`. -/
theorem splitTwinRungGe_of_deepTwinFrontier
    (hb : SplitKit.SplitBlock) (hpre : FreePreSplit)
    (hdeep : DeepTwinFrontier) : PairRungKit.SplitTwinRungGe := by
  intro u v ρ F left right c d b pre post tail hsplit
  have hpin : rungAt F c.twin.suit = c.rank.toIdx :=
    nextUp_true_iff.mp
      ((splitTwinRungPin_iff_deepTwinFrontier hb hpre).mpr hdeep
        u v ρ F left right c d b pre post tail hsplit)
  obtain ⟨-, hSc, -, -⟩ := SplitKit.splitHyp_green hsplit
  have hsig : rungAt F c.suit = c.rank.toIdx := canRaiseS_rung hSc
  omega

/-! ## §7. Battery -/

#print axioms PinAt.twin_rung_pull_invariant
#print axioms PinAt.pin_iff_ge_at_prePull
#print axioms PinAt.pin_iff_deepGe_of_split
#print axioms PinAt.deep_upper_of_block
#print axioms PinAt.splitTwinRungPin_iff_deepTwinFrontier
#print axioms PinAt.not_canRaise_of_ssaturated
#print axioms PinAt.twin_not_exposed_of_ssaturated
#print axioms PinAt.twin_not_exposed_at_deep_of_split
#print axioms PinAt.pin_fails_raise_ne_twin
#print axioms PinAt.splitTwinRungGe_of_deepTwinFrontier

end PinAt
