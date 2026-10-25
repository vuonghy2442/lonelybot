import Orig2.TwinReroute
import Orig2.DetourKit

/-!
# Orig2.TwinRerouteMulti — iterating the base-case reroute

The base-case reroute (`Orig2.TwinReroute`) is one pair-free prefix, one
exact 3-leg recipe detour, and one pair-free suffix.  This card iterates
that block across a whole play: a `RecipePath` is a concatenation of
pair-free witness shuffles and 3-leg recipe detours.

The grammar is the requested one with two additions forced by the
consumers:

* every non-empty segment carries `WF` at its source (the transfer rows
  are `WF`-gated and `WF` is not recoverable from `TwinReady`);
* every segment carries `TwinReady` at both endpoints (the rider-free
  transfer and `swappableIn_recipe_segment` both need endpoint
  readiness; pair-free plays do not preserve rider-freeness, since a
  non-pair-foundation `tabToTab` may seat a rider on a twin).

Nothing else changes; `nil` is as requested, and the three recipe legs
are the only non-pair-free block.

House compliance: new file only, no `sorry`, no `Classical.choice`.
-/

/-! ## §1. The segment grammar -/

/-- A play factored into pair-free witness shuffles and exact 3-leg
recipe detours. -/
inductive RecipePath (x : Card) : State → List Move → State → Prop
  | nil (s : State) : RecipePath x s [] s
  | pairFree {s u : State} {seg : List Move}
      (hwf : s.WF)
      (hready_s : TwinReady s x) (hready_u : TwinReady u x)
      (h : ShufflePlayW s seg u) (hno : ∀ m ∈ seg, NotFoundPair x m) :
      RecipePath x s seg u
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
      RecipePath x s
        [Move.tabToFound x.twin, Move.tabToTab x (Sum.inr z.twin),
          Move.foundToTab x.twin (Sum.inr z)] u
  | trans {s u v : State} {l₁ l₂ : List Move}
      (h₁ : RecipePath x s l₁ u) (h₂ : RecipePath x u l₂ v) :
      RecipePath x s (l₁ ++ l₂) v

/-! ## §2. Readiness propagates along a path -/

/-- A `RecipePath` starting at a ready state ends at a ready state. -/
theorem recipePath_ready {x : Card} :
    ∀ {s s' : State} {play : List Move},
      RecipePath x s play s' → TwinReady s x → TwinReady s' x := by
  intro s s' play hpath
  induction hpath with
  | nil s =>
      intro hready
      exact hready
  | pairFree hwf hready_s hready_u h hno =>
      intro _
      exact hready_u
  | recipe hwf hready_s hready_u hc hct hpa hraise h =>
      intro _
      exact hready_u
  | trans h₁ h₂ ih₁ ih₂ =>
      intro hready
      exact ih₂ (ih₁ hready)

/-! ## §3. The multi-detour transfer -/

/-- Segment-by-segment `SwappableIn` transfer.  Each pair-free block is the
rider-free transfer, each 3-leg block is `swappableIn_recipe_segment`, and
`trans` composes. -/
theorem swappableIn_transfer_recipePath_aux {x : Card} :
    ∀ {s s' : State} {play : List Move},
      RecipePath x s play s' → SwappableIn s x → SwappableIn s' x := by
  intro s s' play hpath
  induction hpath with
  | nil s =>
      intro hswap
      exact hswap
  | pairFree hwf hready_s hready_u h hno =>
      intro hswap
      obtain ⟨hsx, hstx, hrx, hrt⟩ := hready_s
      obtain ⟨hux, hutx, hrux, hrtu⟩ := hready_u
      have hwfu := run_wf hwf (Walk_run _ h)
      exact swappableIn_transfer_of_seated_riderFree hwf hwfu
        hsx hstx hux hutx hrx hrt hrux hrtu h hno hswap
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

/-- **The multi-detour transfer.**  Along any `RecipePath` from a ready
state to a ready state, `SwappableIn` transfers. -/
theorem swappableIn_transfer_recipePath
    {s s' : State} {x : Card} {play : List Move}
    (hready : TwinReady s x) (hready' : TwinReady s' x)
    (hpath : RecipePath x s play s')
    (hswap : SwappableIn s x) :
    SwappableIn s' x := by
  have _ : TwinReady s' x := recipePath_ready hpath hready
  have _ : TwinReady s' x := hready'
  exact swappableIn_transfer_recipePath_aux hpath hswap

#print axioms recipePath_ready
#print axioms swappableIn_transfer_recipePath
