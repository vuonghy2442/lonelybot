import Orig2.TwinPointTransfer
import Orig2.TwinSplicePlay
import Orig2.TwinRerouteMulti
import Orig2.TwinDrawTransfer
import Orig2.OrbitFactor

/-!
# Temp/TwinPointOrbit — the point transfer along pair-free/recipe paths

`Orig2.TwinRerouteMulti` iterates the rider-free transfer along a
`RecipePath`, whose `pairFree` blocks carry `TwinReady` at both
endpoints.  The stronger point transfer
`swappableIn_transfer_point_play` (`Orig2.TwinSplicePlay`) only needs
the twins seated on `.inr` parents at both endpoints, so the pair-free
blocks can admit riders.

This card re-grammars the multi-detour path at the point grade:

* `PointPath.pairFree` carries `WF` at the source, the two `.inr` seat
  witnesses at both endpoints, the witness play, and the `hno` list;
  the landing's `WF` is derived from `run_wf` rather than stored;
* `PointPath.recipe` keeps the exact 3-leg block of `RecipePath`
  verbatim (`TwinReady`, the recipe seats, the pile top, the raise
  witness, and the shuffled block), since
  `swappableIn_recipe_segment` is rider-free at both endpoints;
* `PointPath.trans` composes.

Zero `sorry`, zero `Classical.choice`.
-/

/-! ## §1. The point-grade path grammar -/

/-- A play factored into pair-free point segments and exact 3-leg
recipe detours.  Pair-free segments carry `.inr` seat witnesses at
both endpoints (the rider-free clauses are dropped); recipe segments
keep the `TwinReady` endpoints demanded by `swappableIn_recipe_segment`. -/
inductive PointPath (x : Card) : State → List Move → State → Prop
  | nil (s : State) : PointPath x s [] s
  | pairFree {s u : State} {seg : List Move}
      (hwf : s.WF)
      (hxs : ∃ z, seatOf s x = some (Sum.inr z))
      (hxts : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
      (hxu : ∃ z, seatOf u x = some (Sum.inr z))
      (hxtu : ∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin))
      (h : ShufflePlayW s seg u) (hno : ∀ m ∈ seg, NotFoundPair x m) :
      PointPath x s seg u
  | recipe {s u : State} {z : Card} {a : Anchor}
      (hwf : s.WF)
      (hready_s : TwinReady s x) (hready_u : TwinReady u x)
      (hc : seatOf s x = some (Sum.inr z))
      (hct : seatOf s x.twin = some (Sum.inr z.twin))
      (hpa : s.pileOfTop x.twin = some a)
      (hraise : reversibleAtW s (Move.tabToFound x.twin))
      (h : ShufflePlayW s
        [Move.tabToFound x.twin, Move.tabToTab x (Sum.inr z.twin),
          Move.foundToTab x.twin (Sum.inr z)] u) :
      PointPath x s
        [Move.tabToFound x.twin, Move.tabToTab x (Sum.inr z.twin),
          Move.foundToTab x.twin (Sum.inr z)] u
  | trans {s u v : State} {l₁ l₂ : List Move}
      (h₁ : PointPath x s l₁ u) (h₂ : PointPath x u l₂ v) :
      PointPath x s (l₁ ++ l₂) v

/-! ## §2. The point transfer along a path -/

/-- Segment-by-segment `SwappableIn` transfer.  Each pair-free block is
the point transfer `swappableIn_transfer_point_play` (landing `WF`
derived), each 3-leg block is `swappableIn_recipe_segment`, and `trans`
composes. -/
theorem swappableIn_transfer_pointPath_aux {x : Card} :
    ∀ {s s' : State} {play : List Move},
      PointPath x s play s' → SwappableIn s x → SwappableIn s' x := by
  intro s s' play hpath
  induction hpath with
  | nil s =>
      intro hswap
      exact hswap
  | pairFree hwf hxs hxts hxu hxtu h hno =>
      intro hswap
      have hwfu := run_wf hwf (Walk_run _ h)
      exact swappableIn_transfer_point_play hwf hwfu
        hxs hxts hxu hxtu h hno hswap
  | recipe hwf hready_s hready_u hc hct hpa hraise h =>
      intro hswap
      obtain ⟨-, -, hrx, hrt⟩ := hready_s
      obtain ⟨-, -, hrux, hrtu⟩ := hready_u
      have hwfu := run_wf hwf (Walk_run _ h)
      exact (swappableIn_recipe_segment hwf hwfu hc hct hpa hraise h
        hrx hrt hrux hrtu).mp hswap
  | trans h₁ h₂ ih₁ ih₂ =>
      intro hswap
      exact ih₂ (ih₁ hswap)

/-- **The point transfer along a `PointPath`.** -/
theorem swappableIn_transfer_pointPath
    {s s' : State} {x : Card} {play : List Move}
    (hpath : PointPath x s play s')
    (hswap : SwappableIn s x) :
    SwappableIn s' x :=
  swappableIn_transfer_pointPath_aux hpath hswap

/-! ## §3. With the draw phase -/

/-- **The point transfer with a draw phase first.**  A draws-only
rotation `SWRotW s s0` transports `SwappableIn` to `s0`, and the point
path then carries it to `s'`. -/
theorem swappableIn_transfer_pointPath_draws
    {s s0 s' : State} {x : Card} {play : List Move}
    (hdraw : SWRotW s s0) (hpath : PointPath x s0 play s')
    (hswap : SwappableIn s x) :
    SwappableIn s' x :=
  swappableIn_transfer_pointPath hpath
    ((swappableIn_draw_transfer hdraw).mp hswap)

/-! ## §4. Audit -/

#print axioms swappableIn_transfer_pointPath
#print axioms swappableIn_transfer_pointPath_draws
