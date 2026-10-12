import Orig.PairName

/-!
# Orig.OrphanSeat — THE ORPHAN-SEAT RESIDUE (the shared static core)

The one named residue TWO axes ride: the cross-family static kill
(`Orig.CrossFamilyStatic`) and the upward door's backward route
(`Orig.PairConfine`'s door head).  A card FOUNDED at the start of a
witness journey and STANDING (not founded) at its end sits face-up
on some end-state pile, seated on a face-up BELOW-NEIGHBOR it fits
under (`canSitOn`; the fit hands the caller the below-card's rank
and color without any adjacency bookkeeping — the caller's census
reads rank and color alone).

Hoisted here from `Orig/CrossFamilyStatic.lean` §1 as the dedup the
cycle demanded: `CrossFamilyStatic` imports `Orig.PairConfine`, so
the upward axis could not consume the residue in its old home; this
leaf imports only the shared upstream closure (`Orig.PairName`'s),
placing the residue BELOW both consumers.  Statement
byte-frozen from the original landing.

THE COMPLETE ROUTE (each step priced against banked rows or
named-to-land sub-rows):

1. THE WF CARRY — `step_wf` chains `st.WF` to every prefix state (the
   `conf_wf_along`-pattern copy).
2. THE ZONE CENSUS — at every WF state each card sits in one of the
   five zones (the `conf_zone_residency`-pattern copy over
   `WF.cardCount_eq`).
3. THE WASTE BAR — `e` founded at `st` is in neither stock nor waste
   there (`mem_found_unique`), and the two-zone union NEVER GAINS
   along any play (the fresh private row, six move cases: draws
   permute the union internally via `draw_unfold` + the
   `conf_dealUpTo_mem`-pattern deal rows; the waste legs only shrink
   it; tab/found/cargo legs never write the zone), so `e` is in
   neither at the end.
4. THE HIDDEN BAR — `e` founded at `st` is in no hidden list
   (`mem_found_unique`); `shuffle_hiddenPinned`
   (`Orig/ForkStateUniqGate.lean`) pins every pile's hidden list
   along the journey, so `e` is in none at the end.
5. THE SEAT — with the found bar (the hypothesis `hout`) and bars 3-4,
   the zone census leaves `e` face-up on some end-state pile `a`.
6. THE BELOW-NEIGHBOR (the residue's own core, the below-riding
   induction; the premise `hnk` is load-bearing — a KING could
   otherwise land bare on an empty anchor with no below-neighbor at
   all): `e` leaves its foundation only by a `foundToTab e b` leg
   (`foundToTab_pops_currentTop` names the popped card), whose
   landing for a non-king rides `canPlace`'s inr branch — a face-up
   pile TOP `z` with `canSitOn e z`: the below-neighbor SEED.  Face-up
   lists change only at their tops (the raise chops the top card, the
   cargo moves a suffix run, the pull appends), so no card ever
   departs FROM UNDER another: the below-neighbor identity is stable
   between `e`'s own re-landings, and every re-landing of `e` (as a
   run head or riding a run) reseeds it onto a fresh fitting face-up
   top; reveals never ride (`shuffle_hiddenPinned`), so `e` never
   bottoms on a hidden card.  The end state's `runOK` then reads the
   adjacent pair (the per-file `runOK`-adjacency copy, the pattern of
   `Orig/RunOrTwin.lean`'s private row): `canSitOn e b = true` for the
   face-up card `b` directly below `e` — b face-up at the end.
-/

/-- **THE ORPHAN-SEAT RESIDUE** — a card FOUNDED at the start of a
witness journey and STANDING (not founded) at its end sits face-up on
some end-state pile, seated on a face-up BELOW-NEIGHBOR it fits under. -/
theorem cross_orphan_seat {st st' : State} (hwf : st.WF) {τ : List Move}
    (hτ : ShufflePlayW st τ st') {e : Card} (hnk : e.rank ≠ Rank.king)
    (hmem : e ∈ st.found e.suit) (hout : e ∉ st'.found e.suit) :
    ∃ (a : Anchor) (b : Card),
      e ∈ (st'.piles a).faceUp ∧
      b ∈ (st'.piles a).faceUp ∧
      canSitOn e b = true := by
  sorry

#print axioms cross_orphan_seat
