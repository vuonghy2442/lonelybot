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

/-- **The twin suit is not the own suit.** -/
theorem twinSuit_ne (c : Card) : c.twin.suit ≠ c.suit := by
  intro h
  rw [Card.twin_suit] at h
  exact Suit.twin_ne c.suit h

/-! ## §2. The twin suit's rung across the pull and the free tail -/

/-- **THE PULL AND THE FREE TAIL DO NOT MOVE THE TWIN SUIT.**  Across
`A' --pull c--> B --post (free)--> F` the twin-suit rung is the same at `A'`
and at `F`.  (`PairRungKit.prePull_twin_rung` re-exposed; the pull is a
`foundToTab` of `c`, whose suit is not the twin suit.) -/
theorem twin_rung_pull_invariant {A' B F : State} {c : Card} {b : Base}
    {post : List Move}
    (hstep : State.step A' (Move.foundToTab c b) = some B)
    (hpost : ShufflePlayW B post F)
    (hfree : ∀ m ∈ post, ValleyElim.FreeMove m) :
    rungAt F c.twin.suit = rungAt A' c.twin.suit :=
  (PairRungKit.prePull_twin_rung hstep hpost hfree).symm

/-- **THE PULL SEES A FOUNDATION TOP AT `A'`.**  The split's pull fires with
`c` the foundation top of its own suit, one rung above `c`'s rank index. -/
theorem prePull_own_rung_sharp {A' B : State} {c : Card} {b : Base}
    (hA' : A'.WF) (hstep : State.step A' (Move.foundToTab c b) = some B) :
    A'.foundTop c.suit = some c ∧ c.rank.toIdx + 1 = rungAt A' c.suit := by
  obtain ⟨c', htop, hc', -, -⟩ := step_foundToTab_inv hstep
  rw [hc'] at htop
  exact ⟨htop, SatDifferCensus.foundTop_rank_succ hA' htop⟩

/-! ## §3. The pin at the bottom is the rung gap at the pre-pull state -/

/-- **THE PIN IS THE PRE-PULL GAP.**  At the bottom the pin is exactly the
statement that the two twin suits sit one rung apart at `A'`. -/
theorem pin_iff_prePullGap {A' B F : State} {c : Card} {b : Base}
    {post : List Move}
    (hA' : A'.WF) (hstep : State.step A' (Move.foundToTab c b) = some B)
    (hpost : ShufflePlayW B post F) (hfree : ∀ m ∈ post, ValleyElim.FreeMove m)
    (hS : CanRaiseS F c) :
    (rungAt F c.twin.suit = c.rank.toIdx) ↔
      (rungAt A' c.twin.suit + 1 = rungAt A' c.suit) := by
  have h := PairRungKit.prePull_gap_iff_bottom_pin hA' hstep hpost hfree
  have hsig : rungAt F c.suit = c.rank.toIdx := canRaiseS_rung hS
  constructor
  · intro hp
    exact h.mp (by rw [hp, hsig])
  · intro hgap
    have h' : rungAt F c.twin.suit = rungAt F c.suit := h.mpr hgap
    rw [h'] at *
    exact hsig

/-- **THE RESIDUAL IS ONE INEQUALITY AT `A'`.**  Under the block's *free* half
(`PairRungKit.rungAt_twin_le_of_block`) the pin at the bottom is exactly
`c.rank.toIdx ≤ rungAt A' c.twin.suit`. -/
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

/-- **THE FREE-PREFIX COROLLARY.**  In the generic case — the split's prefix
`pre` is free (draws and slides only), which holds whenever the split's pull is
the play's first non-free letter (`LedgerKit.exodus_cut`) — the residual reads
at `u` with no further hypothesis. -/
theorem pin_iff_deepGe_of_free_pre
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hfreePre : ∀ m ∈ pre, ValleyElim.FreeMove m)
    (hblock : ¬ CanRaise F c) :
    (rungAt F c.twin.suit = c.rank.toIdx) ↔
      (c.rank.toIdx ≤ rungAt u c.twin.suit) :=
  pin_iff_deepGe_of_split h
    (fun A' hpre => by
      have hh := ValleyElim.rungAt_eq_of_free_play hpre hfreePre c.twin.suit
      exact hh.symm)
    hblock

/-- **THE FREE UPPER HALF AT THE DEEP ENDPOINT.**  The twin suit never sits
above `c`'s rank index at `u` either: under the block the bottom's twin rung is
`≤ c.rank.toIdx` (`PairRungKit.rungAt_twin_le_of_block`), and it transports to
`u`.  So the residual is the single LOWER bound. -/
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

/-- The decidable probe of the vanilla license (`Orig.Canonical.canRaiseB`
is outside the `Orig2` seam; this is the same shape, proved here). -/
def canRaiseBL (st : State) (c : Card) : Bool :=
  st.nextUp c &&
    (match st.pileOfTop c with
     | none => false
     | some a =>
         decide (chop (st.piles a).faceUp ≠ []) ||
           (decide ((st.piles a).hidden = []) && decide (c.rank = Rank.king)))

/-- The probe agrees with the license. -/
theorem canRaiseBL_true_iff {st : State} {c : Card} :
    canRaiseBL st c = true ↔ CanRaise st c := by
  constructor
  · intro h
    rw [canRaiseBL, Bool.and_eq_true] at h
    refine ⟨h.1, ?_⟩
    cases hp : st.pileOfTop c with
    | none =>
        simp only [hp] at h
        exact absurd h.2 (by simp)
    | some a =>
        simp only [hp] at h
        refine ⟨a, rfl, ?_⟩
        rw [Bool.or_eq_true] at h
        rcases h.2 with h2 | h2
        · exact Or.inl (of_decide_eq_true h2)
        · rw [Bool.and_eq_true] at h2
          exact Or.inr ⟨of_decide_eq_true h2.1, of_decide_eq_true h2.2⟩
  · rintro ⟨hn, a, hp, hseat⟩
    rw [canRaiseBL, hn, hp]
    simp only [Bool.true_and]
    rw [Bool.or_eq_true]
    rcases hseat with h | ⟨hh, hk⟩
    · exact Or.inl (decide_eq_true h)
    · exact Or.inr (by
        rw [Bool.and_eq_true]
        exact ⟨decide_eq_true hh, decide_eq_true hk⟩)

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

theorem L_u_wf : L_u.WF := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro s
    cases s <;> first | exact ⟨5, rfl⟩ | exact ⟨0, rfl⟩
  · intro a; cases a <;> decide
  · intro c _; rcases c with ⟨s, r⟩; cases s <;> cases r <;> decide

theorem L_B_wf : L_B.WF := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro s
    cases s <;> first | exact ⟨4, rfl⟩ | exact ⟨0, rfl⟩
  · intro a; cases a <;> decide
  · intro c _; rcases c with ⟨s, r⟩; cases s <;> cases r <;> decide

theorem L_F_wf : L_F.WF := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro s
    cases s <;> first | exact ⟨4, rfl⟩ | exact ⟨0, rfl⟩
  · intro a; cases a <;> decide
  · intro c _; rcases c with ⟨s, r⟩; cases s <;> cases r <;> decide

/-! ### §4b. `L_u` is saturated -/

theorem L_u_ssaturated : SSaturated L_u := by
  intro c hS
  have hb : canRaiseSB L_u c = true := (canRaiseSB_iff L_u_wf).mpr hS
  have hall : (Card.universe.all (fun c => !(canRaiseSB L_u c))) = true := by
    decide
  have hfalse : canRaiseSB L_u c = false := by
    have h := (List.all_eq_true.mp hall) c (Card.mem_universe c)
    simpa using h
  rw [hfalse] at hb
  exact Bool.false_ne_true hb

/-! ### §4c. The pull, the free tail, and the pin failure -/

theorem L_u_top : L_u.foundTop .heart = some H5 := by decide
theorem L_u_canPlace : L_u.canPlace H5 (Sum.inr S6) = true := by decide

/-- The pull's reversibility (`foundToTabR` is the oracle). -/
theorem L_u_pull_undo : foundToTabR L_u H5 (Sum.inr S6) = true := by decide

theorem L_pull_rev : reversibleAtW L_u (Move.foundToTab H5 (Sum.inr S6)) :=
  (foundToTabR_iff_reversibleAtW L_u_wf H5 (Sum.inr S6)).mp L_u_pull_undo

/-- **THE PULL FIRES** `L_u → L_B`. -/
theorem L_pull_step : State.step L_u (Move.foundToTab H5 (Sum.inr S6)) = some L_B := by
  rw [step_foundToTab_splice L_u_top L_u_canPlace]
  refine congrArg some (State.ext ?_ ?_ ?_ ?_ ?_)
  · funext s; cases s <;> rfl
  · funext a; cases a <;> rfl
  · rfl
  · rfl
  · rfl

theorem L_B_holds : L_B.pileHolding S4 = some .p1 := by decide
theorem L_B_canPlace : L_B.canPlace S4 (Sum.inr H5) = true := by decide
theorem L_B_below : below S4 (L_B.piles .p1).faceUp ≠ [] := by decide

theorem L_slide_undo : tabToTabR L_B S4 (Sum.inr H5) = true :=
  R12.tabToTabR_true_of L_B_holds L_B_canPlace (Or.inl L_B_below)

theorem L_slide_rev : reversibleAtW L_B (Move.tabToTab S4 (Sum.inr H5)) :=
  (tabToTabR_iff_reversibleAtW L_B_wf S4 (Sum.inr H5)).mp L_slide_undo

/-- **THE FREE TAIL'S SLIDE FIRES** `L_B → L_F`. -/
theorem L_slide_step :
    State.step L_B (Move.tabToTab S4 (Sum.inr H5)) = some L_F := by
  rw [step_tabToTab_eq]
  rw [L_B_holds, L_B_canPlace]
  refine congrArg some (State.ext ?_ ?_ ?_ ?_ ?_)
  · funext s; cases s <;> rfl
  · funext a; cases a <;> rfl
  · rfl
  · rfl
  · rfl

/-- **THE LEFT LEG IS A GENUINE WITNESS PLAY** `L_u → L_F`. -/
theorem L_left : ShufflePlayW L_u
    [Move.foundToTab H5 (Sum.inr S6), Move.tabToTab S4 (Sum.inr H5)] L_F :=
  Walk.cons L_pull_rev L_pull_step (Walk.cons L_slide_rev L_slide_step (Walk.nil L_F))

theorem L_F_rung_own : rungAt L_F H5.suit = H5.rank.toIdx := rfl
theorem L_F_rung_twin : rungAt L_F D5.suit = 0 := rfl
theorem H5_rank : H5.rank.toIdx = 4 := rfl

/-- **THE PIN FAILS AT `L_F`**: the twin suit is four rungs behind. -/
theorem L_pin_fails : rungAt L_F D5.suit < H5.rank.toIdx := by
  rw [L_F_rung_twin, H5_rank]; decide

/-- **THE BLOCK HOLDS AT `L_F`**: `5H` is covered by `4S`. -/
theorem L_block : ¬ CanRaise L_F H5 := by
  intro h
  obtain ⟨-, a, ha, -⟩ := h
  have hnone : L_F.pileOfTop H5 = none := by decide
  rw [hnone] at ha
  exact absurd ha (by simp)

/-- **THE TWIN TOPS A PILE AT `L_F`** (the block's own consequence,
`PairRungKit.pileOfTop_twin_of_block`). -/
theorem L_twin_top : L_F.pileOfTop D5 ≠ none := by decide

/-- **NO CARD IS RAISABLE AT `L_F`.** -/
theorem L_F_no_raisable : ∀ d : Card, ¬ CanRaise L_F d := by
  intro d hd
  have hb : canRaiseBL L_F d = true := canRaiseBL_true_iff.mpr hd
  have hall : (Card.universe.all (fun c => !(canRaiseBL L_F c))) = true := by
    decide
  have hfalse : canRaiseBL L_F d = false := by
    have h := (List.all_eq_true.mp hall) d (Card.mem_universe d)
    simpa using h
  rw [hfalse] at hb
  exact Bool.false_ne_true hb

theorem L_B_canRaise_H5 : CanRaise L_B H5 :=
  ⟨by decide, .p0, by decide, Or.inl (by decide)⟩

/-- **THE PULLED CARD IS S-LIVE AT THE BOTTOM** (the green datum). -/
theorem L_F_canRaiseS_H5 : CanRaiseS L_F H5 := by
  have hpost : ShufflePlayW L_B [Move.tabToTab S4 (Sum.inr H5)] L_F :=
    Walk.cons L_slide_rev L_slide_step (Walk.nil L_F)
  have hfree : ∀ m ∈ [Move.tabToTab S4 (Sum.inr H5)], ValleyElim.FreeMove m := by
    intro m hm
    rw [List.mem_singleton] at hm
    subst hm
    exact ValleyElim.free_slide S4 (Sum.inr H5)
  exact (Bridge.canRaiseS_of_free_play_iff hpost hfree L_B_wf H5).mp
    (CanRaiseS.now H5 L_B_canRaise_H5)

/-- **THE LEFT-LEG NO-GO.**  There is a state pair with a genuine reversible
pull, a genuine reversible free tail, a saturated deep endpoint, `WF` at both
ends, the block, and the twin topping a pile — and the pin FAILS, with **no**
raisable card at the bottom.  So the left leg + the block + the twin-top datum
never force the pin: the far leg's raise card `d` is load-bearing. -/
theorem left_leg_data_not_enough :
    ¬ (∀ (u B F : State) (c : Card) (b : Base) (post : List Move),
        u.WF → SSaturated u →
        reversibleAtW u (Move.foundToTab c b) →
        State.step u (Move.foundToTab c b) = some B →
        ShufflePlayW B post F →
        (∀ m ∈ post, ValleyElim.FreeMove m) →
        F.WF → CanRaiseS F c → ¬ CanRaise F c →
        F.pileOfTop c.twin ≠ none →
        rungAt F c.twin.suit = c.rank.toIdx) := by
  intro h
  have hpin := h L_u L_B L_F H5 (Sum.inr S6)
    [Move.tabToTab S4 (Sum.inr H5)]
    L_u_wf L_u_ssaturated L_pull_rev L_pull_step
    (Walk.cons L_slide_rev L_slide_step (Walk.nil L_F))
    (by
      intro m hm
      rw [List.mem_singleton] at hm
      subst hm
      exact ValleyElim.free_slide S4 (Sum.inr H5))
    L_F_wf L_F_canRaiseS_H5 L_block L_twin_top
  exact absurd hpin (Nat.ne_of_lt L_pin_fails)

/-! ## §5. What the pin forces at the saturated deep endpoint -/

/-- Saturation bars the vanilla license too. -/
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

#print axioms PinAt.twinSuit_ne
#print axioms PinAt.twin_rung_pull_invariant
#print axioms PinAt.prePull_own_rung_sharp
#print axioms PinAt.pin_iff_prePullGap
#print axioms PinAt.pin_iff_ge_at_prePull
#print axioms PinAt.pin_iff_deepGe_of_split
#print axioms PinAt.pin_iff_deepGe_of_free_pre
#print axioms PinAt.deep_upper_of_block
#print axioms PinAt.splitTwinRungPin_iff_deepTwinFrontier
#print axioms PinAt.canRaiseBL_true_iff
#print axioms PinAt.L_u_wf
#print axioms PinAt.L_B_wf
#print axioms PinAt.L_F_wf
#print axioms PinAt.L_u_ssaturated
#print axioms PinAt.L_pull_rev
#print axioms PinAt.L_pull_step
#print axioms PinAt.L_slide_rev
#print axioms PinAt.L_slide_step
#print axioms PinAt.L_left
#print axioms PinAt.L_pin_fails
#print axioms PinAt.L_block
#print axioms PinAt.L_twin_top
#print axioms PinAt.L_F_canRaiseS_H5
#print axioms PinAt.L_F_no_raisable
#print axioms PinAt.left_leg_data_not_enough
#print axioms PinAt.not_canRaise_of_ssaturated
#print axioms PinAt.twin_not_exposed_of_ssaturated
#print axioms PinAt.twin_not_exposed_at_deep_of_split
#print axioms PinAt.pin_fails_raise_ne_twin
#print axioms PinAt.splitTwinRungGe_of_deepTwinFrontier

end PinAt
