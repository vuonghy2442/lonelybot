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

/-! ## §0. THE SEAT LANGUAGE AND THE DESIGN PROBE

The residue's core language, landed as data before any induction:
`Below` is the PURELY POSITIONAL below-neighbor read (a face-up pile
list exhibiting a card directly below `e` — no fit, no rank, no
witness continuity carried), and `SeatZone` is the orphan's four-way
zone package (founded, the draw-cycle union, some hidden deck, or a
below-neighbor) — the disjunction the journey induction carries.
The fit (`canSitOn e b = true`) is NOT part of the invariant: it is
read once, at the end state, from the pile discipline's own `runOK`
adjacency.  The probe below restates both packages as Bool and
decides the per-letter carry over curated witness cells BEFORE any
induction is written — blessing the rideable letters and surfacing
exactly the four barred sites (the two reveal letters, which need
their banked never-reveal bars, and the two bare-landing letters,
which need the non-king premise `hnk`). -/

/-- The positional below-neighbor read: some face-up pile list
exhibits a card directly below `e`. -/
def Below (st : State) (e z : Card) : Prop :=
  ∃ (a : Anchor) (L R : List Card), (st.piles a).faceUp = L ++ z :: e :: R

/-- The orphan's four-way zone package: founded, in the draw-cycle
union, in some hidden deck, or seated on a below-neighbor.  The
internal carry's arm-space; the public core is the collapsed
two-disjunct `Below_stable`. -/
private def SeatZone (st : State) (e : Card) : Prop :=
  e ∈ st.found e.suit ∨ (e ∈ st.stock ∨ e ∈ st.waste) ∨
    (∃ k, e ∈ (st.piles k).hidden) ∨ ∃ z, Below st e z

/-! ### The Bool restatement

`hasBelowB` is the tail-membership read (an element with a
predecessor occurrence exists exactly when `e` sits in the list's
tail), and `seatZoneB` mirrors `SeatZone` into `Bool` so the probe
cells can be decided by the kernel. -/

/-- The Bool mirror of `Below`'s inner read: `e` occurs past the
first position, i.e. with some predecessor directly below it. -/
private def hasBelowB (l : List Card) (e : Card) : Bool :=
  decide (e ∈ l.tail)

/-- The tail-membership read has exactly the append shape: a card
past the first position has the entry before it as a below-neighbor. -/
private theorem hasBelowB_shape {e : Card} :
    ∀ (l : List Card), hasBelowB l e = true →
      ∃ (L : List Card) (z : Card) (R : List Card), l = L ++ z :: e :: R := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (by simp [hasBelowB])
  | cons c t ih =>
      intro h
      have hmem : e ∈ t := of_decide_eq_true h
      cases t with
      | nil => exact absurd hmem (by simp)
      | cons d t' =>
          rcases List.mem_cons.mp hmem with hde | htl
          · refine ⟨[], c, t', ?_⟩
            subst hde
            rfl
          · obtain ⟨L, z, R, hs⟩ := ih (by
              show decide (e ∈ (d :: t').tail) = true
              exact decide_eq_true htl)
            exact ⟨c :: L, z, R, by rw [hs, List.cons_append]⟩

/-- The append shape reads back as tail membership. -/
private theorem hasBelowB_of_shape {e z : Card} :
    ∀ (L R : List Card), hasBelowB (L ++ z :: e :: R) e = true := by
  intro L
  induction L with
  | nil =>
      intro R
      show decide (e ∈ ([] ++ z :: e :: R).tail) = true
      rw [List.nil_append, List.tail_cons]
      exact decide_eq_true (List.mem_cons_self ..)
  | cons w t ih =>
      intro R
      show decide (e ∈ ((w :: t) ++ z :: e :: R).tail) = true
      rw [List.cons_append, List.tail_cons]
      exact decide_eq_true
        (List.mem_append.mpr (Or.inr
          (List.mem_cons.mpr (Or.inr (List.mem_cons_self ..)))))

/-- The Bool mirror of `SeatZone`: each arm as a decide-grade read. -/
private def seatZoneB (st : State) (e : Card) : Bool :=
  decide (e ∈ st.found e.suit) ||
    ((decide (e ∈ st.stock) || decide (e ∈ st.waste)) ||
      ((Anchor.all.any fun k => decide (e ∈ (st.piles k).hidden)) ||
        (Anchor.all.any fun a => hasBelowB (st.piles a).faceUp e)))

/-- The mirror is faithful: the Bool fold reads exactly the zone
package. -/
private theorem seatZoneB_iff (st : State) (e : Card) :
    seatZoneB st e = true ↔ SeatZone st e := by
  constructor
  · intro h
    rw [seatZoneB, Bool.or_eq_true] at h
    rcases h with h1 | h1
    · exact Or.inl (of_decide_eq_true h1)
    · rw [Bool.or_eq_true] at h1
      rcases h1 with h2 | h2
      · rw [Bool.or_eq_true] at h2
        rcases h2 with h3 | h3
        · exact Or.inr (Or.inl (Or.inl (of_decide_eq_true h3)))
        · exact Or.inr (Or.inl (Or.inr (of_decide_eq_true h3)))
      · rw [Bool.or_eq_true] at h2
        rcases h2 with h3 | h3
        · rw [List.any_eq_true] at h3
          obtain ⟨k, -, hk⟩ := h3
          exact Or.inr (Or.inr (Or.inl ⟨k, of_decide_eq_true hk⟩))
        · rw [List.any_eq_true] at h3
          obtain ⟨a, -, ha⟩ := h3
          obtain ⟨L, z, R, hs⟩ := hasBelowB_shape _ ha
          exact Or.inr (Or.inr (Or.inr ⟨z, a, L, R, hs⟩))
  · intro h
    rcases h with h1 | h1
    · rw [seatZoneB, Bool.or_eq_true]
      exact Or.inl (decide_eq_true h1)
    · rcases h1 with h2 | h2
      · rcases h2 with h3 | h3
        · rw [seatZoneB, Bool.or_eq_true]
          refine Or.inr ?_
          rw [Bool.or_eq_true]
          refine Or.inl ?_
          rw [Bool.or_eq_true]
          exact Or.inl (decide_eq_true h3)
        · rw [seatZoneB, Bool.or_eq_true]
          refine Or.inr ?_
          rw [Bool.or_eq_true]
          refine Or.inl ?_
          rw [Bool.or_eq_true]
          exact Or.inr (decide_eq_true h3)
      · rcases h2 with h3 | h3
        · obtain ⟨k, hk⟩ := h3
          rw [seatZoneB, Bool.or_eq_true]
          refine Or.inr ?_
          rw [Bool.or_eq_true]
          refine Or.inr ?_
          rw [Bool.or_eq_true]
          refine Or.inl ?_
          rw [List.any_eq_true]
          exact ⟨k, Anchor.mem_all k, decide_eq_true hk⟩
        · obtain ⟨z, a, L, R, hs⟩ := h3
          rw [seatZoneB, Bool.or_eq_true]
          refine Or.inr ?_
          rw [Bool.or_eq_true]
          refine Or.inr ?_
          rw [Bool.or_eq_true]
          refine Or.inr ?_
          rw [List.any_eq_true]
          refine ⟨a, Anchor.mem_all a, ?_⟩
          rw [hs]
          exact hasBelowB_of_shape L R


/-! ### The witness cells -/

-- the probe's deck of concrete cards
private def pHe : Card := ⟨.heart, .five⟩
private def pS6 : Card := ⟨.spade, .six⟩
private def pH4 : Card := ⟨.heart, .four⟩
private def pC6 : Card := ⟨.club, .six⟩
private def pHA : Card := ⟨.heart, .ace⟩
private def pH2 : Card := ⟨.heart, .two⟩
private def pH3 : Card := ⟨.heart, .three⟩
private def pDa2 : Card := ⟨.diamond, .two⟩
private def pDaA : Card := ⟨.diamond, .ace⟩
private def pDk : Card := ⟨.diamond, .king⟩
private def pDn : Card := ⟨.diamond, .nine⟩
private def pSk : Card := ⟨.spade, .king⟩

/-- The cell-state builder: piles and foundations by override,
draw step 3. -/
private def probeSt (ps : Anchor → Pile) (fs : Suit → List Card)
    (stk wst : List Card) : State := ⟨fs, ps, stk, wst, 3⟩

/-- The one-letter cell check: whenever the letter fires, the zone
package carries. -/
private def probeCellOK (st : State) (m : Move) (e : Card) : Bool :=
  match st.step m with
  | none => true
  | some s' => (!seatZoneB st e) || seatZoneB s' e

/-- The rideable cells: the letters that carry the package without
any bar needed — the draw (both the seated and the draw-cycle-union
residents), the raise (the mid-pile chop congruence and the own
top's founding arm), the pull's card-directed reseed, the cargo
rider and the cargo head's re-pairing, and the two king-gate refusals
(the empty-seat letters at a non-king demonstrate the gate itself). -/
private def probeRideCells : List (State × Move × Card) :=
  [(probeSt (fun a => if a = Anchor.p0 then ⟨[], [pS6, pHe]⟩ else ⟨[], []⟩)
      (fun _ => []) [pDa2, pDaA] [],
    Move.draw, pHe),
   (probeSt (fun _ => ⟨[], []⟩) (fun _ => []) [] [pHe],
    Move.draw, pHe),
   (probeSt (fun a => if a = Anchor.p0 then ⟨[], [pS6, pHe, pH4]⟩ else ⟨[], []⟩)
      (fun s => if s = Suit.heart then [pHA, pH2, pH3] else []) [] [],
    Move.tabToFound pH4, pHe),
   (probeSt (fun a => if a = Anchor.p0 then ⟨[], [pS6, pHe]⟩ else ⟨[], []⟩)
      (fun s => if s = Suit.heart then [pHA, pH2, pH3, pH4] else []) [] [],
    Move.tabToFound pHe, pHe),
   (probeSt (fun a => if a = Anchor.p1 then ⟨[], [pC6]⟩ else ⟨[], []⟩)
      (fun s => if s = Suit.heart then [pHA, pHe] else []) [] [],
    Move.foundToTab pHe (Sum.inr pC6), pHe),
   (probeSt (fun _ => ⟨[], []⟩)
      (fun s => if s = Suit.heart then [pHA, pHe] else []) [] [],
    Move.foundToTab pHe (Sum.inl Anchor.p2), pHe),
   (probeSt (fun a =>
       if a = Anchor.p0 then ⟨[], [pS6, pHe, pH4]⟩
       else if a = Anchor.p1 then ⟨[], [pC6]⟩ else ⟨[], []⟩)
      (fun _ => []) [] [],
    Move.tabToTab pHe (Sum.inr pC6), pH4),
   (probeSt (fun a =>
       if a = Anchor.p0 then ⟨[], [pS6, pHe]⟩
       else if a = Anchor.p1 then ⟨[], [pC6]⟩ else ⟨[], []⟩)
      (fun _ => []) [] [],
    Move.tabToTab pHe (Sum.inr pC6), pHe),
   (probeSt (fun a =>
       if a = Anchor.p0 then ⟨[], [pS6, pHe]⟩ else ⟨[], []⟩)
      (fun _ => []) [] [],
    Move.tabToTab pHe (Sum.inl Anchor.p5), pHe)]

/-- **THE PROBE BLESSING** — every rideable cell carries the package
(firing cells preserve `SeatZone`; refusals pass vacuously), by
kernel `decide` over the real step machine. -/
private theorem probe_ride_blessed : probeRideCells.all
    (fun c => probeCellOK c.1 c.2.1 c.2.2) = true := by decide

/-- The four barred sites, as decided failures: the two reveal letters
(a raise and a cargo that empty a face-up run over a hidden deck bare
the revealed card — their witness-journey bars are
`journey_tabToFound_never_reveal` and `journey_tabToTab_never_reveal`),
and the two bare-landing letters (a pull and a cargo run-head onto an
empty seat land a KING bare — the non-king premise `hnk` is exactly
what bars them). -/
private def probeDeadCells : List (State × Move × Card) :=
  [(probeSt (fun a => if a = Anchor.p0 then ⟨[pDk], [pH4]⟩ else ⟨[], []⟩)
      (fun s => if s = Suit.heart then [pHA, pH2, pH3] else []) [] [],
    Move.tabToFound pH4, pDk),
   (probeSt (fun a =>
       if a = Anchor.p0 then ⟨[pDn], [pHe]⟩
       else if a = Anchor.p1 then ⟨[], [pC6]⟩ else ⟨[], []⟩)
      (fun _ => []) [] [],
    Move.tabToTab pHe (Sum.inr pC6), pDn),
   (probeSt (fun _ => ⟨[], []⟩)
      (fun s => if s = Suit.spade then [pSk] else []) [] [],
    Move.foundToTab pSk (Sum.inl Anchor.p3), pSk),
   (probeSt (fun a => if a = Anchor.p0 then ⟨[], [pS6, pSk]⟩ else ⟨[], []⟩)
      (fun _ => []) [] [],
    Move.tabToTab pSk (Sum.inl Anchor.p5), pSk)]

/-- **THE PROBE SURFACING** — each barred site is a decided
counterexample row to the UNBARRED carry: exactly the four legs that
need their banked reveal-bars or the king premise. -/
private theorem probe_dead_surfaced : probeDeadCells.all
    (fun c => !(probeCellOK c.1 c.2.1 c.2.2)) = true := by decide

/-! ## §1. The four bar sources (the original brief's steps 1-4)

The WF carry, the five-zone census, the draw-cycle union's two
directions (the forward carry for the induction's union arm, the
never-gain direction for the close's bar), and the hidden pin (the
banked whole-journey row read per-leg and at the endpoints). -/

/-- **STEP 1 — THE WF CARRY** (the `conf_wf_along`-pattern copy):
`step_wf` chains the start's WF to every prefix state, hence to the
journey's end. -/
private theorem seat_wf_along {st : State} : ∀ {w : State} {play : List Move},
    ShufflePlayW st play w → st.WF → w.WF := by
  intro w play h
  induction h with
  | nil u => intro hwf; exact hwf
  | @cons s₀ mv s₁ rest w₀ hrev hstep hrest ih =>
      intro hwf
      exact ih (step_wf hwf hstep)

/-- **STEP 2 — THE ZONE CENSUS** (the `conf_zone_residency`-pattern
copy over `WF.cardCount_eq`): at any WF state every card sits in one
of the five zones, read existentially. -/
private theorem seat_zone_residency (st : State) (hwf : st.WF) (d : Card) :
    (∃ s, d ∈ st.found s) ∨ (∃ k, d ∈ (st.piles k).hidden) ∨
    (∃ k, d ∈ (st.piles k).faceUp) ∨ d ∈ st.stock ∨ d ∈ st.waste := by
  have h1 : st.cardCount d = 1 := hwf.cardCount_eq (Card.mem_universe d)
  unfold State.cardCount at h1
  cases hL : ((st.zones.flatMap id).filter fun x => decide (x = d)) with
  | nil =>
      rw [hL] at h1
      simp at h1
  | cons x xs =>
      have hxmem : x ∈ (st.zones.flatMap id).filter
          (fun x => decide (x = d)) := by
        rw [hL]
        exact List.mem_cons_self ..
      obtain ⟨hxeq, hxz⟩ := List.mem_filter.mp hxmem
      have hxd : x = d := of_decide_eq_true hxz
      obtain ⟨z, hz, hdz⟩ := List.mem_flatMap.mp hxeq
      have hdzd : d ∈ z := by rw [← hxd]; exact hdz
      have hspl : st.zones = (Suit.all.map st.found) ++
          ((Anchor.all.map fun a =>
            (st.piles a).hidden ++ (st.piles a).faceUp) ++
            [st.stock, st.waste]) := rfl
      rw [hspl] at hz
      rcases List.mem_append.mp hz with hA | hB
      · obtain ⟨s, -, hzs⟩ := List.mem_map.mp hA
        exact Or.inl ⟨s, by rw [← hzs] at hdzd; exact hdzd⟩
      · rcases List.mem_append.mp hB with hC | hD
        · obtain ⟨k, -, hzk⟩ := List.mem_map.mp hC
          rw [← hzk] at hdzd
          rcases List.mem_append.mp hdzd with hH | hF
          · exact Or.inr (Or.inl ⟨k, hH⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨k, hF⟩))
        · rcases List.mem_cons.mp hD with hS | hW
          · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
            rw [← hS]
            exact hdzd
          · rw [List.mem_singleton] at hW
            refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
            rw [← hW]
            exact hdzd

/-- **STEP 3a — THE UNION CARRY** (the `conf_stockWaste_closed`-pattern
copy): along a witness journey the stock and waste are a closed
two-zone world for their residents — the induction's union arm rides
this forward direction. -/
private theorem seat_union_carry (d : Card) :
    ∀ {s : State} {play : List Move} {w : State},
      ShufflePlayW s play w →
      (d ∈ s.stock ∨ d ∈ s.waste) → (d ∈ w.stock ∨ d ∈ w.waste) := by
  intro s play w h
  induction h with
  | nil u => intro hcyc; exact hcyc
  | @cons s₀ m s₁ rest w₀ hrev hstep hrest ih =>
      intro hcyc
      have hmid : d ∈ s₁.stock ∨ d ∈ s₁.waste := by
        cases m with
        | draw =>
            have hd : s₀.stepDraw = some s₁ := hstep
            obtain ⟨r, hrEq, -, hyEq⟩ := draw_unfold hd
            rw [hyEq]
            rcases hcyc with hst | hwst
            · cases hss : s₀.stock with
              | nil => rw [hss] at hst; exact absurd hst (by simp)
              | cons x xs =>
                  have hrt : r = s₀ := by
                    rw [← hrEq]
                    exact recycle_keep s₀ (by rw [hss]; simp)
                  have hin : d ∈ r.stock := by rw [hrt]; exact hst
                  have hspl := FoundKit.dealUpTo_mem d r.drawStep r.stock hin
                  rcases hspl with hD | hR
                  · exact Or.inr
                      (List.mem_append.mpr (Or.inl (List.mem_reverse.mpr hD)))
                  · exact Or.inl hR
            · cases hss : s₀.stock with
              | nil =>
                  cases hws : s₀.waste with
                  | nil => rw [hws] at hwst; exact absurd hwst (by simp)
                  | cons v vs =>
                      have hrt : r = { s₀ with
                          stock := s₀.waste.reverse,
                          waste := ([] : List Card) } := by
                        rw [← hrEq]
                        exact recycle_nil s₀ hss (by rw [hws]; simp)
                      have hin : d ∈ r.stock := by
                        rw [hrt]
                        exact List.mem_reverse.mpr hwst
                      have hspl := FoundKit.dealUpTo_mem d r.drawStep r.stock hin
                      rcases hspl with hD | hR
                      · exact Or.inr
                          (List.mem_append.mpr
                            (Or.inl (List.mem_reverse.mpr hD)))
                      · exact Or.inl hR
              | cons x xs =>
                  have hrt : r = s₀ := by
                    rw [← hrEq]
                    exact recycle_keep s₀ (by rw [hss]; simp)
                  exact Or.inr
                    (List.mem_append.mpr (Or.inr (by rw [hrt]; exact hwst)))
        | wasteToFound walt =>
            exact absurd hrev (journey_never_wasteToFound hstep)
        | wasteToTab walt balt =>
            exact absurd hrev (journey_never_wasteToTab hstep)
        | tabToFound walt =>
            obtain ⟨-, k, -, hs⟩ := step_tabToFound_inv hstep
            rw [hs]
            exact hcyc
        | foundToTab walt balt =>
            obtain ⟨-, -, -, -, hs⟩ := step_foundToTab_inv hstep
            rw [hs]
            obtain ⟨-, hP1, hP2, -⟩ :=
              putCard_keep (st := s₀.setFound walt.suit
                (chop (s₀.found walt.suit))) (c := walt) (b := balt)
            rw [hP1, hP2]
            exact hcyc
        | tabToTab walt balt =>
            obtain ⟨Asrc, -, -, -, hs⟩ := step_tabToTab_inv hstep
            rw [hs]
            obtain ⟨-, hP1, hP2, -⟩ :=
              putRun_keep (st := s₀.setPile Asrc
                (Pile.afterRunRemoved (s₀.piles Asrc)
                  (below walt ((s₀.piles Asrc).faceUp))))
                (run := fromCard walt ((s₀.piles Asrc).faceUp)) (b := balt)
            rw [hP1, hP2]
            exact hcyc
      exact ih hmid

/-- The deal's shrink row (the `conf_deal_shrink`-pattern copy): each
deal lane's residents came from the source list. -/
private theorem seat_deal_shrink (d : Card) : ∀ (k : Nat) (l : List Card),
    (d ∈ (State.dealUpTo k l).1 → d ∈ l) ∧
      (d ∈ (State.dealUpTo k l).2 → d ∈ l) := by
  intro k
  induction k with
  | zero =>
      intro l
      refine ⟨?_, ?_⟩
      · intro hmem
        simp only [State.dealUpTo] at hmem
        exact absurd hmem (by simp)
      · intro hmem
        simp only [State.dealUpTo] at hmem
        exact hmem
  | succ k ih =>
      intro l
      cases l with
      | nil =>
          refine ⟨?_, ?_⟩
          all_goals
            intro hmem
            simp only [State.dealUpTo] at hmem
            exact absurd hmem (by simp)
      | cons x xs =>
          obtain ⟨ih1, ih2⟩ := ih xs
          refine ⟨?_, ?_⟩
          · intro hmem
            simp only [State.dealUpTo] at hmem
            rcases List.mem_cons.mp hmem with heq | hrest
            · rw [heq]
              exact List.mem_cons_self ..
            · exact List.mem_cons.2 (Or.inr (ih1 hrest))
          · intro hmem
            simp only [State.dealUpTo] at hmem
            exact List.mem_cons.2 (Or.inr (ih2 hmem))

/-- **STEP 3b — THE UNION NEVER GAINS** (the `conf_orphan_union`-pattern
copy): the two-zone union never gains along any play — the close's
draw-cycle bar rides this backward direction. -/
private theorem seat_union_nogain {st : State} : ∀ {u : State}
    {τ : List Move},
    ShufflePlayW st τ u →
    (∀ d : Card, d ∈ u.stock ∨ d ∈ u.waste → d ∈ st.stock ∨ d ∈ st.waste) := by
  intro u τ h
  induction h with
  | nil s =>
      intro d hcyc
      exact hcyc
  | @cons s₀ m s₁ rest w₀ hrev hstep hrest ih =>
      intro d h1
      have hmid : d ∈ s₁.stock ∨ d ∈ s₁.waste := ih d h1
      cases m with
      | draw =>
          have hd : s₀.stepDraw = some s₁ := hstep
          obtain ⟨r, hrEq, -, hyEq⟩ := draw_unfold hd
          rw [hyEq] at hmid
          rcases hmid with hst | hwst
          · have hmem : d ∈ r.stock :=
              (seat_deal_shrink d r.drawStep r.stock).2 hst
            cases hss : s₀.stock with
            | nil =>
                cases hws : s₀.waste with
                | nil =>
                    have hall : r = s₀ := by
                      rw [← hrEq]
                      exact recycle_allEmpty s₀ hss hws
                    rw [hall, hss] at hmem
                    exact absurd hmem (by simp)
                | cons v vs =>
                    have hrt : r = { s₀ with
                        stock := s₀.waste.reverse,
                        waste := ([] : List Card) } := by
                      rw [← hrEq]
                      exact recycle_nil s₀ hss (by rw [hws]; simp)
                    rw [hrt, hws] at hmem
                    exact Or.inr (List.mem_reverse.mp hmem)
            | cons x xs =>
                have hrt : r = s₀ := by
                  rw [← hrEq]
                  exact recycle_keep s₀ (by rw [hss]; simp)
                rw [hrt, hss] at hmem
                exact Or.inl hmem
          · cases hss : s₀.stock with
            | nil =>
                cases hws : s₀.waste with
                | nil =>
                    have hall : r = s₀ := by
                      rw [← hrEq]
                      exact recycle_allEmpty s₀ hss hws
                    rcases List.mem_append.mp hwst with hD | hR
                    · have hmem : d ∈ r.stock :=
                        (seat_deal_shrink d r.drawStep r.stock).1
                          (List.mem_reverse.mp hD)
                      rw [hall, hss] at hmem
                      exact absurd hmem (by simp)
                    · rw [hall, hws] at hR
                      exact absurd hR (by simp)
                | cons v vs =>
                    have hrt : r = { s₀ with
                        stock := s₀.waste.reverse,
                        waste := ([] : List Card) } := by
                      rw [← hrEq]
                      exact recycle_nil s₀ hss (by rw [hws]; simp)
                    rcases List.mem_append.mp hwst with hD | hR
                    · have hmem : d ∈ r.stock :=
                        (seat_deal_shrink d r.drawStep r.stock).1
                          (List.mem_reverse.mp hD)
                      rw [hrt, hws] at hmem
                      exact Or.inr (List.mem_reverse.mp hmem)
                    · rw [hrt] at hR
                      exact absurd hR (by simp)
            | cons x xs =>
                have hrt : r = s₀ := by
                  rw [← hrEq]
                  exact recycle_keep s₀ (by rw [hss]; simp)
                rcases List.mem_append.mp hwst with hD | hR
                · have hmem : d ∈ r.stock :=
                    (seat_deal_shrink d r.drawStep r.stock).1
                      (List.mem_reverse.mp hD)
                  rw [hrt, hss] at hmem
                  exact Or.inl hmem
                · rw [hrt] at hR
                  exact Or.inr hR
      | wasteToFound walt =>
          exact absurd hrev (journey_never_wasteToFound hstep)
      | wasteToTab walt balt =>
          exact absurd hrev (journey_never_wasteToTab hstep)
      | tabToFound walt =>
          obtain ⟨-, k, -, hs⟩ := step_tabToFound_inv hstep
          rw [hs] at hmid
          exact hmid
      | foundToTab walt balt =>
          obtain ⟨-, -, -, -, hs⟩ := step_foundToTab_inv hstep
          rw [hs] at hmid
          obtain ⟨-, hP1, hP2, -⟩ :=
            putCard_keep (st := s₀.setFound walt.suit
              (chop (s₀.found walt.suit))) (c := walt) (b := balt)
          rw [hP1, hP2] at hmid
          exact hmid
      | tabToTab walt balt =>
          obtain ⟨Asrc, -, -, -, hs⟩ := step_tabToTab_inv hstep
          rw [hs] at hmid
          obtain ⟨-, hP1, hP2, -⟩ :=
            putRun_keep (st := s₀.setPile Asrc
              (Pile.afterRunRemoved (s₀.piles Asrc)
                (below walt ((s₀.piles Asrc).faceUp))))
              (run := fromCard walt ((s₀.piles Asrc).faceUp)) (b := balt)
          rw [hP1, hP2] at hmid
          exact hmid

/-- **STEP 4 — THE HIDDEN PIN**, per-leg (the banked whole-journey
`shuffle_hiddenPinned` read at the single-leg journey): a witness leg
writes no pile's hidden list. -/
private theorem seat_hidden_pinned_leg {s s' : State} {m : Move}
    (hrev : reversibleAtW s m) (hstep : State.step s m = some s') :
    ∀ a, (s'.piles a).hidden = (s.piles a).hidden :=
  fun a => shuffle_hiddenPinned (.cons hrev hstep (.nil s')) a

/-! ## §5. The positional list kit

The suffix/chop congruence rows the four-way carry rides: `below`'s
prefix cut and a run's suffix cut both keep the directly-below pair
(the SAME witness — pure list congruence, no fit data), the run
membership trivia, and the slide-profile workbench with its landing
base located. -/

/-- A run member is in the list (the `fromCard` membership half). -/
private theorem seat_mem_fromCard {c x : Card} :
    ∀ (l : List Card), x ∈ fromCard c l → x ∈ l := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (by simp [fromCard])
  | cons y t ih =>
      intro h
      rw [fromCard] at h
      split at h
      · exact h
      · exact List.mem_cons.mpr (Or.inr (ih h))

/-- The append nodup split: an element of the first part is not in
the second. -/
private theorem seat_nodup_parts {A B : List Card} (hnd : (A ++ B).Nodup) :
    ∀ {x : Card}, x ∈ A → x ∉ B := by
  induction A with
  | nil => intro x h; exact absurd h (by simp)
  | cons w A₁ ih =>
      obtain ⟨hw, hnd₁⟩ := List.nodup_cons.mp hnd
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hxt
      · intro hcon
        exact hw (List.mem_append.mpr (Or.inr hcon))
      · exact ih hnd₁ hxt

/-- The face-up run splits at the from-card: the below-prefix and the
moving run (the `conf_below_fromCard`-pattern copy). -/
private theorem seat_below_fromCard (t : Card) : ∀ (l : List Card),
    l = below t l ++ fromCard t l := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
      by_cases hxt : x = t
      · rw [hxt, below_cons_self, fromCard_cons_self, List.nil_append]
      · rw [below_cons_ne xs hxt, fromCard_cons_ne xs hxt, List.cons_append]
        exact congrArg (x :: ·) ih

/-- The last of an append with a nonempty tail is the tail's last
(the `conf_lastOf_append`-pattern copy). -/
private theorem seat_lastOf_append_tail (l₁ : List Card) :
    ∀ (l₂ : List Card), l₂ ≠ [] → lastOf (l₁ ++ l₂) = lastOf l₂ := by
  induction l₁ with
  | nil => intro l₂ _; rfl
  | cons x xs ih =>
      intro l₂ hne
      cases l₂ with
      | nil => exact absurd rfl hne
      | cons y l' =>
          cases xs with
          | nil => exact rfl
          | cons v vs =>
              exact ih (y :: l') hne

/-- **THE PREFIX-CUT CONGRUENCE** — cutting the below-prefix at the
run's head keeps the directly-below pair intact: if `e` sits in the
`below` part of a nodup list that exhibits `z` directly below `e`,
then the `below` prefix itself exhibits the same `z` (no fit data;
the duplicate cases die on nodup alone). -/
private theorem seat_below_adj {c e : Card} :
    ∀ (L R : List Card) (z : Card),
      (L ++ z :: e :: R).Nodup → e ∈ below c (L ++ z :: e :: R) →
      ∃ (Lₚ Rₚ : List Card),
        below c (L ++ z :: e :: R) = Lₚ ++ z :: e :: Rₚ := by
  intro L
  induction L with
  | nil =>
      intro R z hnd hmem
      have hmem' : e ∈ below c (z :: e :: R) := hmem
      have hnd' : (z :: e :: R).Nodup := hnd
      by_cases hzc : z = c
      · rw [hzc, below_cons_self] at hmem'
        exact absurd hmem' (by simp)
      · rw [below_cons_ne (e :: R) hzc] at hmem'
        by_cases hec : e = c
        · exfalso
          rw [hec, below_cons_self] at hmem'
          rcases List.mem_cons.mp hmem' with h | h
          · exact hzc h.symm
          · exact absurd h (by simp)
        · refine ⟨[], below c R, ?_⟩
          show below c (z :: e :: R) = ([] ++ z :: e :: below c R : List Card)
          rw [below_cons_ne (e :: R) hzc, below_cons_ne R hec]
          rfl
  | cons w t ih =>
      intro R z hnd hmem
      have hmem' : e ∈ below c (w :: (t ++ z :: e :: R)) := hmem
      have hnd' : (w :: (t ++ z :: e :: R)).Nodup := hnd
      by_cases hwc : w = c
      · rw [hwc, below_cons_self] at hmem'
        exact absurd hmem' (by simp)
      · rw [below_cons_ne (t ++ z :: e :: R) hwc] at hmem'
        rcases List.mem_cons.mp hmem' with hew | htl
        · exfalso
          have hwin : w ∈ z :: e :: R := by
            rw [← hew]
            exact List.mem_cons.mpr (Or.inr (List.mem_cons_self ..))
          exact (List.nodup_cons.mp hnd').1
            (List.mem_append.mpr (Or.inr hwin))
        · obtain ⟨Lₚ, Rₚ, hs⟩ :=
            ih R z (List.nodup_cons.mp hnd').2 htl
          refine ⟨w :: Lₚ, Rₚ, ?_⟩
          show below c ((w :: t) ++ z :: e :: R)
            = ((w :: Lₚ) ++ z :: e :: Rₚ : List Card)
          rw [List.cons_append, below_cons_ne (t ++ z :: e :: R) hwc, hs]
          rfl

/-- **THE SUFFIX-CUT CONGRUENCE** — a run's internal below-neighbor
stays below its rider: if `e` rides the moving run (in the run's
tail) of a nodup list exhibiting `z` directly below `e`, then the run
itself exhibits the same `z`. -/
private theorem seat_pair_in_suffix {c z e : Card} :
    ∀ (A S L R : List Card),
      (A ++ c :: S).Nodup → A ++ c :: S = L ++ z :: e :: R →
      e ∈ S → e ∉ A → e ≠ c →
      ∃ (B₁ B₂ : List Card), c :: S = B₁ ++ z :: e :: B₂ := by
  intro A
  induction A with
  | nil =>
      intro S L R hnd hshape hS _ hec
      rw [List.nil_append] at hshape
      cases L with
      | nil =>
          injection hshape with hzc hS2
          refine ⟨[], R, ?_⟩
          show c :: S = ([] ++ z :: e :: R : List Card)
          rw [hS2, hzc]
          rfl
      | cons w L₁ =>
          rw [List.cons_append] at hshape
          injection hshape with hwc hS2
          refine ⟨w :: L₁, R, ?_⟩
          show c :: S = ((w :: L₁) ++ z :: e :: R : List Card)
          rw [hS2, hwc]
          rfl
  | cons v A₁ ih =>
      intro S L R hnd hshape hS hnotA hec
      have hshape' : v :: (A₁ ++ c :: S) = L ++ z :: e :: R := hshape
      have hnd' : (v :: (A₁ ++ c :: S)).Nodup := hnd
      have hnotA' : e ∉ v :: A₁ := hnotA
      cases L with
      | nil =>
          exfalso
          have hshape'' : v :: (A₁ ++ (c :: S)) = (z :: e :: R) := hshape'
          injection hshape'' with hzv heR
          have heR' : A₁ ++ (c :: S) = e :: R := heR
          cases A₁ with
          | nil =>
              have heR'' : (c :: S) = (e :: R) := heR'
              injection heR'' with h1 _
              exact hec h1.symm
          | cons v' A₂ =>
              have heR'' : v' :: (A₂ ++ c :: S) = e :: R := heR'
              injection heR'' with h1 _
              exact hnotA' (List.mem_cons.mpr (Or.inr
                (List.mem_cons.mpr (Or.inl h1.symm))))
      | cons w L₁ =>
          rw [List.cons_append] at hshape'
          injection hshape' with hvw hrest2
          have hrest2' : (A₁ ++ (c :: S)) = (L₁ ++ z :: e :: R) := hrest2
          obtain ⟨B₁, B₂, hs⟩ := ih S L₁ R
            (List.nodup_cons.mp hnd').2 hrest2' hS
            (fun hcon => hnotA' (List.mem_cons.mpr (Or.inr hcon))) hec
          exact ⟨B₁, B₂, hs⟩

/-- The top search respects pile equality (the
`conf_pileOfTop_congr`-pattern copy). -/
private theorem seat_pileOfTop_congr {s s' : State}
    (h : s'.piles = s.piles) (z : Card) :
    s'.pileOfTop z = s.pileOfTop z := by
  unfold State.pileOfTop State.topOf
  rw [h]

/-- The emptied-pile top read, no hidden deck (the
`conf_arr_nil_top_none`-pattern copy). -/
private theorem seat_arr_nil_top_none {p : Pile} (h : p.hidden = []) :
    (Pile.afterRunRemoved p ([] : List Card)).top = none := by
  rcases p with ⟨hs, fs⟩
  rw [show (⟨hs, fs⟩ : Pile).hidden = hs from rfl] at h
  subst h
  rfl

/-- The emptied-pile top read, revealed head (the
`conf_arr_nil_top_some`-pattern copy). -/
private theorem seat_arr_nil_top_some {p : Pile} {g : Card} {gs : List Card}
    (h : p.hidden = g :: gs) :
    (Pile.afterRunRemoved p ([] : List Card)).top = some g := by
  rcases p with ⟨hs, fs⟩
  rw [show (⟨hs, fs⟩ : Pile).hidden = hs from rfl] at h
  subst h
  rfl

/-- **THE SLIDE-PROFILE WORKBENCH** (the `conf_slide_shape`-pattern
copy, with the landing base located): a firing run move at a WF state
has the two-pile write profile — the departure pile keeps (or
reveals over) its below-prefix, the landing pile (located by its base,
never the departure pile) takes the run appended above its own
face-up run, and every other pile is untouched. -/
private theorem seat_slide_shape {s s' : State} {c : Card} {b : Base}
    (hwf : s.WF)
    (hstep : State.step s (Move.tabToTab c b) = some s') :
    ∃ (a k : Anchor) (run : List Card),
      s.pileHolding c = some a ∧
      run = fromCard c (s.piles a).faceUp ∧
      run ≠ [] ∧
      k ≠ a ∧
      ((b = Sum.inl k ∧ (s.piles k).isEmpty = true) ∨
        (∃ z, b = Sum.inr z ∧ s.pileOfTop z = some k)) ∧
      (s'.piles a = Pile.afterRunRemoved (s.piles a)
          (below c (s.piles a).faceUp)) ∧
      (∀ y, y ≠ a → y ≠ k → s'.piles y = s.piles y) ∧
      ((s'.piles k).hidden = (s.piles k).hidden ∧
          (s'.piles k).faceUp = (s.piles k).faceUp ++ run) := by
  obtain ⟨a₀, hh, hcp, hrne, hs⟩ := step_tabToTab_inv hstep
  have hcmem : c ∈ (s.piles a₀).faceUp := pileHolding_mem hh
  cases b with
  | inl e =>
      obtain ⟨hemp, -⟩ := canPlace_inl hcp
      obtain ⟨hhde, hhfe⟩ := (Pile.isEmpty_eq _).mp hemp
      have hne : e ≠ a₀ := canPlace_inl_target_pile_ne hcp hcmem
      rw [hs, putRun_eq_inl]
      refine ⟨a₀, e, fromCard c (s.piles a₀).faceUp, hh, rfl, hrne, hne,
        Or.inl ⟨rfl, hemp⟩, ?_, ?_, ?_⟩
      · rw [setPile_piles_ne (Ne.symm hne), setPile_piles_self]
      · intro y hy hye
        rw [setPile_piles_ne hye, setPile_piles_ne hy]
      · rw [setPile_piles_self, hhde, hhfe]
        exact ⟨rfl, rfl⟩
  | inr z =>
      obtain ⟨k₀, hk₀, -⟩ := canPlace_inr hcp
      have hne : k₀ ≠ a₀ := fun hcon =>
        canPlace_inr_target_pile_ne hwf hcp hcmem (hcon ▸ hk₀)
      have hzmem : z ∈ (s.piles k₀).faceUp :=
        Pile.mem_of_top (pileOfTop_top hk₀).2
      have hzNotA : z ∉ (s.piles a₀).faceUp :=
        (mem_faceUp_unique hwf hzmem a₀ (Ne.symm hne)).1
      have hzNotH : z ∉ (s.piles a₀).hidden :=
        (mem_faceUp_unique hwf hzmem a₀ (Ne.symm hne)).2.1
      -- the mid state rewrites only the departure pile
      have hmidk : (s.setPile a₀ (Pile.afterRunRemoved (s.piles a₀)
          (below c (s.piles a₀).faceUp))).piles k₀
          = s.piles k₀ := setPile_piles_ne hne
      -- the base-card search answers as before: its own pile is untouched
      have hmidx : (s.setPile a₀ (Pile.afterRunRemoved (s.piles a₀)
          (below c (s.piles a₀).faceUp))).pileOfTop z = some k₀ := by
        unfold State.pileOfTop
        refine firstWhere_find (Anchor.mem_all k₀) ?_ ?_
        · show decide ((s.setPile a₀ (Pile.afterRunRemoved (s.piles a₀)
              (below c (s.piles a₀).faceUp))).topOf k₀
            = some z) = true
          rw [setPile_topOf_ne hne]
          exact decide_eq_true (pileOfTop_top hk₀).2
        · intro y _hy hyne'
          show decide ((s.setPile a₀ (Pile.afterRunRemoved (s.piles a₀)
              (below c (s.piles a₀).faceUp))).topOf y
            = some z) = false
          by_cases hya : y = a₀
          · have hXz : (Pile.afterRunRemoved (s.piles a₀)
                (below c (s.piles a₀).faceUp)).top ≠ some z := by
              intro hcon
              by_cases hpre : (below c (s.piles a₀).faceUp) = []
              · rw [hpre] at hcon
                cases hhid : (s.piles a₀).hidden with
                | nil =>
                    rw [seat_arr_nil_top_none hhid] at hcon
                    exact absurd hcon (by simp)
                | cons g gs =>
                    rw [seat_arr_nil_top_some hhid] at hcon
                    have hgt : g = z := Option.some.inj hcon
                    exact hzNotH
                      (by rw [← hgt, hhid]; exact List.mem_cons_self ..)
              · rw [afterRunRemoved_ne hpre] at hcon
                have hL : lastOf (below c (s.piles a₀).faceUp) = some z :=
                  hcon
                exact hzNotA
                  (mem_below ((s.piles a₀).faceUp) (lastOf_mem hL))
            rw [hya]
            unfold State.topOf
            rw [setPile_piles_self]
            exact decide_false_of_not hXz
          · rw [setPile_topOf_ne hya]
            exact decide_false_of_not (fun hcon =>
              (mem_faceUp_unique hwf hzmem y hyne').1 (Pile.mem_of_top hcon))
      rw [hs, putRun_inr_eq hmidx]
      refine ⟨a₀, k₀, fromCard c (s.piles a₀).faceUp, hh, rfl, hrne, hne,
        Or.inr ⟨z, rfl, hk₀⟩, ?_, ?_, ?_⟩
      · rw [setPile_piles_ne (Ne.symm hne), setPile_piles_self]
      · intro y hy hyk
        rw [setPile_piles_ne hyk, setPile_piles_ne hy]
      · rw [setPile_piles_self, hmidk]
        exact ⟨rfl, rfl⟩

/-! ## §6. The per-leg carry rows

The four-way `SeatZone` package is carried across each of the six
move letters individually — the arms the core induction consumes.
The waste letters are barred outright (they never ride), the draw is
pure record congruence plus the union carry, and the three tab/found
letters ride the re-landing modes: the raise chops the top (append
above and suffix chop keep the SAME below-witness; the raised card
itself flips to the founded arm), the pull reseeds a pulled non-king
onto the landing host's old top (the king gate is `hnk`'s
load-bearing site), and the cargo keeps the below-prefix, carries the
run-internal rider, and re-pairs the run head onto the host's old
top. -/

/-- LAYER 1, draw — the record congruence letter. -/
private theorem seat_step_draw {s s' : State} {d : Card}
    (hstep : State.step s Move.draw = some s')
    (hrev : reversibleAtW s Move.draw)
    (hc : SeatZone s d) : SeatZone s' d := by
  have hd : s.stepDraw = some s' := hstep
  rcases hc with hF | hU | hH | hB
  · exact Or.inl (by rw [stepDraw_found hd]; exact hF)
  · exact Or.inr (Or.inl
      (seat_union_carry d (.cons hrev hstep (.nil s')) hU))
  · obtain ⟨k, hk⟩ := hH
    exact Or.inr (Or.inr (Or.inl
      ⟨k, by rw [seat_hidden_pinned_leg hrev hstep k]; exact hk⟩))
  · obtain ⟨z, W, L, R, hshape⟩ := hB
    refine Or.inr (Or.inr (Or.inr ⟨z, W, L, R, ?_⟩))
    rw [congrFun (stepDraw_piles hd) W]
    exact hshape

/-- LAYER 1, waste letters — they never ride a witness journey. -/
private theorem seat_step_wasteFound {s s' : State} {c d : Card}
    (hstep : State.step s (Move.wasteToFound c) = some s')
    (hrev : reversibleAtW s (Move.wasteToFound c)) : SeatZone s' d :=
  absurd hrev (journey_never_wasteToFound hstep)

private theorem seat_step_wasteTab {s s' : State} {c d : Card} {b : Base}
    (hstep : State.step s (Move.wasteToTab c b) = some s')
    (hrev : reversibleAtW s (Move.wasteToTab c b)) : SeatZone s' d :=
  absurd hrev (journey_never_wasteToTab hstep)

/-- The four-layer append reassociation the seat shapes ride. -/
private theorem seat_assoc4 (L : List Card) (z d : Card) (R T : List Card) :
    L ++ z :: d :: (R ++ T) = (L ++ z :: d :: R) ++ T := by
  rw [List.append_assoc, List.cons_append, List.cons_append]

/-- The last of a two-card head is the pair's second (the R=[]
corner of the tail reads). -/
private theorem seat_lastOf_pairTail (z d : Card) :
    ∀ (R : List Card), R ≠ [] → lastOf (z :: d :: R) = lastOf R := by
  intro R h
  cases R with
  | nil => exact absurd rfl h
  | cons r t => rfl

/-- LAYER 1, raise — the top-chop letter: founded cards stay founded
(the same suit row grows by the raised card), and a below-neighbor
seat at the departure pile survives the chop with the SAME witness
(the raised card itself flips to the founded arm). -/
private theorem seat_step_raise {s s' : State} {c d : Card}
    (hstep : State.step s (Move.tabToFound c) = some s')
    (hrev : reversibleAtW s (Move.tabToFound c))
    (hc : SeatZone s d) : SeatZone s' d := by
  obtain ⟨hn, a, hpo, hs⟩ := step_tabToFound_inv hstep
  obtain ⟨hselfF, hothersF, -⟩ := tabToFound_found_trio (a := a) hs
  have hpy : ∀ y, s'.piles y = if y = a then
      Pile.afterRunRemoved (s.piles a) (chop (s.piles a).faceUp)
      else s.piles y := fun y => by rw [hs]
  rcases hc with hF | hU | hH | hB
  · refine Or.inl ?_
    by_cases hdcs : d.suit = c.suit
    · rw [hdcs, hselfF]
      exact List.mem_append.mpr (Or.inl (by rw [← hdcs]; exact hF))
    · rw [hothersF d.suit hdcs]
      exact hF
  · exact Or.inr (Or.inl
      (seat_union_carry d (.cons hrev hstep (.nil s')) hU))
  · obtain ⟨k, hk⟩ := hH
    exact Or.inr (Or.inr (Or.inl
      ⟨k, by rw [seat_hidden_pinned_leg hrev hstep k]; exact hk⟩))
  · obtain ⟨z, W, L, R, hshape⟩ := hB
    obtain ⟨-, hlast⟩ := pileOfTop_top hpo
    by_cases hWa : W = a
    · rw [hWa] at hshape
      rw [hshape] at hlast
      by_cases hdc : d = c
      · exact Or.inl (by
          rw [hs, hdc]
          show c ∈ (s.setFound c.suit (s.found c.suit ++ [c])).found c.suit
          rw [setFound_found_self]
          exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
      · cases hR : R with
        | nil =>
            exfalso
            rw [hR] at hlast
            have hlastd : lastOf (L ++ z :: d :: ([] : List Card))
                = some d :=
              (seat_lastOf_append_tail L (z :: d :: ([] : List Card))
                (by simp)).trans rfl
            exact hdc (Option.some.inj (hlastd.symm.trans hlast))
        | cons r rs =>
            rw [hR] at hlast
            rw [seat_lastOf_append_tail L (z :: d :: (r :: rs))
              (by simp)] at hlast
            rw [seat_lastOf_pairTail z d (r :: rs) (by simp)] at hlast
            obtain ⟨R₁, hR₁⟩ := lastOf_eq_snoc hlast
            refine Or.inr (Or.inr (Or.inr ⟨z, a, L, R₁, ?_⟩))
            rw [hpy a, ite_eq_left rfl]
            have hmem : d ∈ chop (s.piles a).faceUp := by
              rw [hshape, hR, hR₁, seat_assoc4 L z d R₁ [c], chop_snoc]
              exact List.mem_append.mpr (Or.inr
                (List.mem_cons.mpr (Or.inr (List.mem_cons_self ..))))
            rw [afterRunRemoved_ne (by
              intro hcon
              rw [hcon] at hmem
              exact absurd hmem (by simp))]
            show chop (s.piles a).faceUp = L ++ z :: d :: R₁
            rw [hshape, hR, hR₁, seat_assoc4 L z d R₁ [c], chop_snoc]
    · refine Or.inr (Or.inr (Or.inr ⟨z, W, L, R, ?_⟩))
      rw [hpy W, ite_eq_right hWa]
      exact hshape

/-- LAYER 1, pull — the reseed letter: a pulled card in another suit's
foundation stays founded through the chop; THE pulled card (a non-king
by `hnk`) lands on the pull base's host pile, seated directly on the
host's old top; seated cards elsewhere or below the append keep their
witness. -/
private theorem seat_step_pull {s s' : State} {c d : Card} {b : Base}
    (hstep : State.step s (Move.foundToTab c b) = some s')
    (hrev : reversibleAtW s (Move.foundToTab c b))
    (hnk : d.rank ≠ Rank.king)
    (hc : SeatZone s d) : SeatZone s' d := by
  obtain ⟨c', htop, hc'c, hcp, hs⟩ := step_foundToTab_inv hstep
  rw [hc'c] at htop
  rcases hc with hF | hU | hH | hB
  · -- FOUNDED
    by_cases hdcs : d.suit = c.suit
    · by_cases hdc : d = c
      · -- d IS the pulled card: the seed
        cases b with
        | inl k =>
            exfalso
            obtain ⟨-, hking⟩ := canPlace_inl hcp
            rw [← hdc] at hking
            exact absurd hking hnk
        | inr z =>
            obtain ⟨k, hpok, -⟩ := canPlace_inr hcp
            have hmidp : (s.setFound c.suit (chop (s.found c.suit))).piles
                = s.piles :=
              setFound_piles s c.suit (chop (s.found c.suit))
            have hmidpo :
                (s.setFound c.suit (chop (s.found c.suit))).pileOfTop z
                  = some k :=
              (seat_pileOfTop_congr hmidp z).trans hpok
            obtain ⟨-, hlastk⟩ := pileOfTop_top hmidpo
            obtain ⟨Lk, hLk⟩ := lastOf_eq_snoc hlastk
            refine Or.inr (Or.inr (Or.inr ⟨z, k, Lk, [], ?_⟩))
            rw [hs, putCard_piles_inr _ _ _ _ hmidpo]
            simp only []
            show ((s.setFound c.suit (chop (s.found c.suit))).piles k).faceUp
              ++ [c] = Lk ++ z :: d :: []
            rw [hLk, hdc, List.append_assoc]
            rfl
      · -- d rides the chop of its suit's foundation row
        refine Or.inl ?_
        have hlast : lastOf (s.found c.suit) = some c := htop
        obtain ⟨front, hfront⟩ := lastOf_eq_snoc hlast
        rw [hs, putCard_found, hdcs, setFound_found_self, hfront, chop_snoc]
        rw [hdcs, hfront] at hF
        rcases List.mem_append.mp hF with hpre | hlastm
        · exact hpre
        · rw [List.mem_singleton] at hlastm
          exact absurd hlastm hdc
    · refine Or.inl ?_
      rw [hs, putCard_found]
      show d ∈ (s.setFound c.suit (chop (s.found c.suit))).found d.suit
      rw [setFound_found_ne hdcs]
      exact hF
  · exact Or.inr (Or.inl
      (seat_union_carry d (.cons hrev hstep (.nil s')) hU))
  · obtain ⟨k, hk⟩ := hH
    exact Or.inr (Or.inr (Or.inl
      ⟨k, by rw [seat_hidden_pinned_leg hrev hstep k]; exact hk⟩))
  · -- BELOW
    obtain ⟨z, W, L, R, hshape⟩ := hB
    have hmidp : (s.setFound c.suit (chop (s.found c.suit))).piles
        = s.piles :=
      setFound_piles s c.suit (chop (s.found c.suit))
    cases b with
    | inl k =>
        obtain ⟨hemp, -⟩ := canPlace_inl hcp
        by_cases hWk : W = k
        · exfalso
          obtain ⟨-, hhfe⟩ := (Pile.isEmpty_eq _).mp hemp
          have hdm : d ∈ (s.piles W).faceUp := by
            rw [hshape]
            exact List.mem_append.mpr (Or.inr
              (List.mem_cons.mpr (Or.inr (List.mem_cons_self ..))))
          rw [hWk, hhfe] at hdm
          exact absurd hdm (by simp)
        · refine Or.inr (Or.inr (Or.inr ⟨z, W, L, R, ?_⟩))
          rw [hs, putCard_eq_inl, setPile_piles]
          simp only []
          rw [ite_eq_right hWk, congrFun hmidp W]
          exact hshape
    | inr z₂ =>
        obtain ⟨k, hpok, -⟩ := canPlace_inr hcp
        have hmidpo :
            (s.setFound c.suit (chop (s.found c.suit))).pileOfTop z₂
              = some k :=
          (seat_pileOfTop_congr hmidp z₂).trans hpok
        by_cases hWk : W = k
        · refine Or.inr (Or.inr (Or.inr ⟨z, k, L, R ++ [c], ?_⟩))
          rw [hWk] at hshape
          rw [hs, putCard_piles_inr _ _ _ _ hmidpo]
          simp only []
          show ((s.setFound c.suit (chop (s.found c.suit))).piles k).faceUp
            ++ [c] = L ++ z :: d :: (R ++ [c])
          rw [congrFun hmidp k, hshape, ← seat_assoc4 L z d R [c]]
        · refine Or.inr (Or.inr (Or.inr ⟨z, W, L, R, ?_⟩))
          rw [hs, putCard_piles_inr _ _ _ _ hmidpo]
          simp only []
          rw [ite_eq_right hWk, congrFun hmidp W]
          exact hshape

/-- LAYER 1, cargo — the run letter: the departure pile keeps (or
reveals over) its below-prefix, the run lands appended at the host
pile.  A below-neighbor seat in the below-prefix keeps the same
witness through the prefix cut; a rider in the run keeps the SAME
run-internal witness; the run head re-pairs onto the host's old top
(a non-king head by `hnk`); a seat at the host pile is appended
above; every other pile is untouched. -/
private theorem seat_step_cargo {s s' : State} {c d : Card} {b : Base}
    (hwf : s.WF) (hstep : State.step s (Move.tabToTab c b) = some s')
    (hrev : reversibleAtW s (Move.tabToTab c b))
    (hnk : d.rank ≠ Rank.king)
    (hc : SeatZone s d) : SeatZone s' d := by
  obtain ⟨Asrc, hh, hcp, hfr, hs⟩ := step_tabToTab_inv hstep
  obtain ⟨_a, k, run, _hold, hrun, hrne, _hne, hdesc, hpa, hothers,
    hpair⟩ := seat_slide_shape hwf hstep
  have hsrc : Asrc = _a := pileHolding_inj hh _hold
  subst hsrc
  rcases hc with hF | hU | hH | hB
  · exact Or.inl (by rw [hs, putRun_found, setPile_found]; exact hF)
  · exact Or.inr (Or.inl
      (seat_union_carry d (.cons hrev hstep (.nil s')) hU))
  · obtain ⟨kk, hk⟩ := hH
    exact Or.inr (Or.inr (Or.inl
      ⟨kk, by rw [seat_hidden_pinned_leg hrev hstep kk]; exact hk⟩))
  · obtain ⟨z, W, L, R, hshape⟩ := hB
    have hnodup : ((s.piles Asrc).faceUp).Nodup :=
      runOK_nodup (hwf.2.1 Asrc)
    by_cases hWa : W = Asrc
    · -- the seat sits in the departure pile: below-cut or run-ride
      rw [hWa] at hshape
      have hsplit : (s.piles Asrc).faceUp =
          below c ((s.piles Asrc).faceUp) ++ run := by
        rw [hrun]
        exact seat_below_fromCard c ((s.piles Asrc).faceUp)
      have hdm : d ∈ (s.piles Asrc).faceUp := by
        rw [hshape]
        exact List.mem_append.mpr (Or.inr
          (List.mem_cons.mpr (Or.inr (List.mem_cons_self ..))))
      have hcmem : c ∈ (s.piles Asrc).faceUp := pileHolding_mem hh
      obtain ⟨t, hct⟩ : ∃ t, run = c :: t := by
        rw [hrun]
        exact fromCard_eq_head_of_mem hcmem
      rcases List.mem_append.mp (by rw [← hsplit]; exact hdm) with
        hdbelow | hdrun
      · -- BELOW-CUT: the same witness persists through the prefix cut
        obtain ⟨Lₚ, Rₚ, hs2⟩ :=
          seat_below_adj L R z (by rw [← hshape]; exact hnodup)
            (by rw [← hshape]; exact hdbelow)
        have hdbne : below c ((s.piles Asrc).faceUp) ≠ [] := by
          intro hcon
          rw [hcon] at hdbelow
          exact absurd hdbelow (by simp)
        refine Or.inr (Or.inr (Or.inr ⟨z, Asrc, Lₚ, Rₚ, ?_⟩))
        rw [hpa, afterRunRemoved_ne hdbne]
        show below c ((s.piles Asrc).faceUp) = Lₚ ++ z :: d :: Rₚ
        rw [hshape]
        exact hs2
      · -- RUN-RIDE: the head re-pairs, the rider keeps its witness
        by_cases hdc : d = c
        · rcases hdesc with ⟨hbl, -⟩ | ⟨z₂, -, hpok⟩
          · exfalso
            rw [hbl] at hcp
            obtain ⟨-, hking⟩ := canPlace_inl hcp
            rw [← hdc] at hking
            exact absurd hking hnk
          · obtain ⟨-, hlastk⟩ := pileOfTop_top hpok
            obtain ⟨Lk, hLk⟩ := lastOf_eq_snoc hlastk
            refine Or.inr (Or.inr (Or.inr ⟨z₂, k, Lk, t, ?_⟩))
            rw [hpair.2, hLk, hct, hdc, List.append_assoc]
            rfl
        · have hdt : d ∈ t := by
            rw [hct] at hdrun
            rcases List.mem_cons.mp hdrun with hd1 | hd2
            · exact absurd hd1 hdc
            · exact hd2
          by_cases hdb2 : d ∈ below c ((s.piles Asrc).faceUp)
          · exfalso
            have hnodupR :
                (below c ((s.piles Asrc).faceUp) ++ (c :: t)).Nodup := by
              rw [hsplit, hct] at hnodup
              exact hnodup
            exact (seat_nodup_parts hnodupR hdb2)
              (by rw [← hct]; exact hdrun)
          · have hcomp : below c ((s.piles Asrc).faceUp) ++ (c :: t)
                = L ++ z :: d :: R := by
              have h2 := hsplit.symm.trans hshape
              rw [hct] at h2
              exact h2
            have hnodupR :
                (below c ((s.piles Asrc).faceUp) ++ (c :: t)).Nodup := by
              rw [hsplit, hct] at hnodup
              exact hnodup
            obtain ⟨B₁, B₂, hss⟩ :=
              seat_pair_in_suffix
                (below c ((s.piles Asrc).faceUp)) t L R hnodupR hcomp
                hdt hdb2 (fun hcon => hdc hcon)
            refine Or.inr (Or.inr (Or.inr
              ⟨z, k, (s.piles k).faceUp ++ B₁, B₂, ?_⟩))
            rw [hpair.2, hct, hss, ← List.append_assoc]
    · -- other piles: the landing host's append, or untouched
      by_cases hWk : W = k
      · refine Or.inr (Or.inr (Or.inr ⟨z, k, L, R ++ run, ?_⟩))
        rw [hWk] at hshape
        rw [hpair.2, hshape, ← seat_assoc4 L z d R run]
      · refine Or.inr (Or.inr (Or.inr ⟨z, W, L, R, ?_⟩))
        rw [hothers W hWa hWk]
        exact hshape

/-! ## §6a. The LIFO exodus law (the farm-copied wheel)

`Orig/CrossFamily.lean` banks `cross_found_exodus` as its per-file
copy "ready for upstream consumption"; the shared leaf now owns the
law (the copy name here is `orphan_found_exodus`, the dependency
`foundToTab_pops_currentTop` rides along as the per-file copy from
`Orig/BracketDecomp.lean`).  A card founded at a witness journey's
start and absent at its end has a LITERAL own-pull leg inside the
shuffle: the residency survives every raise, waste-founding, draw
and slide, and only the card's own pop spends it. -/

/-- **THE LIFO PULL LAW** (the `foundToTab_pops_currentTop`-pattern
copy) — a pull pops the CURRENT TOP of its suit's foundation: the
step's own guard names the popped card as the foundation's current
top. -/
private theorem seat_pull_pops_top {st : State} {c : Card} {b : Base}
    {s' : State} (h : State.step st (Move.foundToTab c b) = some s') :
    st.foundTop c.suit = some c := by
  obtain ⟨c', htop, hc'c, -, -⟩ := step_foundToTab_inv h
  rw [hc'c] at htop
  exact htop

/-- **THE LIFO EXODUS LAW** (the `cross_found_exodus`-pattern copy) —
a card foundation-resident at a witness journey's start yet absent
at the end has passed a literal `foundToTab` leg of its own along the
shuffle. -/
theorem orphan_found_exodus : ∀ {u : State} {τ : List Move} {w : State},
    ShufflePlayW u τ w → ∀ (d : Card),
    d ∈ u.found d.suit → d ∉ w.found d.suit →
    ∃ b, Move.foundToTab d b ∈ τ := by
  intro u τ w h
  induction h with
  | nil => intro d hmem hno; exact absurd hmem hno
  | @cons s m s₁ rest w' hrev hstep hrest ih =>
      intro d hmem hno
      cases m with
      | draw =>
          have hsurv : d ∈ s₁.found d.suit := by
            rw [stepDraw_found (show s.stepDraw = some s₁ from hstep)]
            exact hmem
          obtain ⟨b', hl⟩ := ih d hsurv hno
          exact ⟨b', List.mem_cons.2 (Or.inr hl)⟩
      | wasteToFound c =>
          obtain ⟨-, x, xs, -, hs⟩ := step_wasteToFound_inv hstep
          have hsurv : d ∈ s₁.found d.suit := by
            rw [hs]
            show d ∈ (s.setFound c.suit (s.found c.suit ++ [c])).found d.suit
            by_cases hsc : d.suit = c.suit
            · rw [hsc, setFound_found_self]
              rw [hsc] at hmem
              exact List.mem_append.2 (Or.inl hmem)
            · rw [setFound_found_ne hsc]
              exact hmem
          obtain ⟨b', hl⟩ := ih d hsurv hno
          exact ⟨b', List.mem_cons.2 (Or.inr hl)⟩
      | wasteToTab c b =>
          obtain ⟨-, x, xs, -, hs⟩ := step_wasteToTab_inv hstep
          have hsurv : d ∈ s₁.found d.suit := by
            rw [hs]
            show d ∈ (s.putCard c b).found d.suit
            rw [putCard_found]
            exact hmem
          obtain ⟨b', hl⟩ := ih d hsurv hno
          exact ⟨b', List.mem_cons.2 (Or.inr hl)⟩
      | tabToFound c =>
          obtain ⟨-, a, -, hs⟩ := step_tabToFound_inv hstep
          have hsurv : d ∈ s₁.found d.suit := by
            rw [hs]
            show d ∈ (s.setFound c.suit (s.found c.suit ++ [c])).found d.suit
            by_cases hsc : d.suit = c.suit
            · rw [hsc, setFound_found_self]
              rw [hsc] at hmem
              exact List.mem_append.2 (Or.inl hmem)
            · rw [setFound_found_ne hsc]
              exact hmem
          obtain ⟨b', hl⟩ := ih d hsurv hno
          exact ⟨b', List.mem_cons.2 (Or.inr hl)⟩
      | foundToTab c b =>
          by_cases hdc : d = c
          · exact ⟨b, List.mem_cons.2 (Or.inl (by rw [hdc]))⟩
          · obtain ⟨-, -, -, -, hs⟩ := step_foundToTab_inv hstep
            have hsurv : d ∈ s₁.found d.suit := by
              by_cases hsc : d.suit = c.suit
              · have hchop : s.found c.suit = chop (s.found c.suit) ++ [c] :=
                  lastOf_chop (seat_pull_pops_top hstep)
                rw [hsc] at hmem
                rw [hchop] at hmem
                rw [hs, putCard_found, hsc, setFound_found_self]
                rcases List.mem_append.1 hmem with h | h
                · exact h
                · rcases List.mem_cons.1 h with he | hn
                  · exact absurd he hdc
                  · exact absurd hn (by simp)
              · rw [hs, putCard_found, setFound_found_ne hsc]
                exact hmem
            obtain ⟨b', hl⟩ := ih d hsurv hno
            exact ⟨b', List.mem_cons.2 (Or.inr hl)⟩
      | tabToTab c b =>
          obtain ⟨a, -, -, -, hs⟩ := step_tabToTab_inv hstep
          have hsurv : d ∈ s₁.found d.suit := by
            rw [hs, putRun_found, setPile_found]
            exact hmem
          obtain ⟨b', hl⟩ := ih d hsurv hno
          exact ⟨b', List.mem_cons.2 (Or.inr hl)⟩

/-! ### The journey splitter

Membership in the play is a place to cut: a witness shuffle运势ing a
member leg splits into prefix-journey, the leg (with its own
witness), and suffix-journey — all three witness shuffles. -/

/-- **THE JOURNEY SPLIT** — a witness shuffle containing the leg
splits at its first need: prefix, leg, suffix, each a witness
shuffle, the leg carrying its own reversibility witness. -/
private theorem seat_journey_split {c : Card} {b : Base} :
    ∀ {τ : List Move} {st u : State},
      Move.foundToTab c b ∈ τ → ShufflePlayW st τ u →
      ∃ (ρ₁ ρ₂ : List Move) (sM sL : State),
        τ = ρ₁ ++ Move.foundToTab c b :: ρ₂ ∧
        ShufflePlayW st ρ₁ sM ∧
        reversibleAtW sM (Move.foundToTab c b) ∧
        State.step sM (Move.foundToTab c b) = some sL ∧
        ShufflePlayW sL ρ₂ u := by
  intro τ st u hmem hτ
  revert hmem
  induction hτ with
  | nil st0 => intro hmem; exact absurd hmem (by simp)
  | @cons st0 mv s₁ rest w0 hrev hstep hrest ih =>
      intro hmem
      by_cases hmv : mv = Move.foundToTab c b
      · refine ⟨[], rest, st0, s₁, ?_, .nil st0, by rw [← hmv]; exact hrev,
          by rw [← hmv]; exact hstep, hrest⟩
        rw [hmv, List.nil_append]
      · have hmem' : Move.foundToTab c b ∈ rest := by
          rcases List.mem_cons.mp hmem with h | hm
          · exact absurd h.symm hmv
          · exact hm
        obtain ⟨σ₁, σ₂, sM, sL, hEq, hj₁, hrev', hlegstep, hj₂⟩ :=
          ih hmem'
        refine ⟨mv :: σ₁, σ₂, sM, sL, ?_, ?_, hrev', hlegstep, hj₂⟩
        · exact congrArg (mv :: ·) hEq
        · exact ShufflePlayW_append (.cons hrev hstep (.nil s₁)) hj₁

/-- **THE LANDING SEED** — the exodus leg's own landing: a non-king
pulled from its foundation leaves it only on the card-directed
branch, and the landing's own write IS the seat shape (the host's
old top directly below the pulled card). -/
private theorem seat_landing_seed {s s' : State} {e : Card} {b : Base}
    (hstep : State.step s (Move.foundToTab e b) = some s')
    (hnk : e.rank ≠ Rank.king) :
    ∃ (a : Anchor) (L R : List Card) (z : Card),
      (s'.piles a).faceUp = L ++ z :: e :: R := by
  obtain ⟨-, -, -, hcp, hs⟩ := step_foundToTab_inv hstep
  cases b with
  | inl k =>
      exfalso
      obtain ⟨-, hking⟩ := canPlace_inl hcp
      exact absurd hking hnk
  | inr z =>
      obtain ⟨k, hpok, -⟩ := canPlace_inr hcp
      have hmidp : (s.setFound e.suit (chop (s.found e.suit))).piles
          = s.piles :=
        setFound_piles s e.suit (chop (s.found e.suit))
      have hmidpo :
          (s.setFound e.suit (chop (s.found e.suit))).pileOfTop z
            = some k :=
        (seat_pileOfTop_congr hmidp z).trans hpok
      obtain ⟨-, hlastk⟩ := pileOfTop_top hmidpo
      obtain ⟨Lk, hLk⟩ := lastOf_eq_snoc hlastk
      exact ⟨k, Lk, [], z, by
        rw [hs, putCard_piles_inr _ _ _ _ hmidpo]
        simp only []
        show ((s.setFound e.suit (chop (s.found e.suit))).piles k).faceUp
          ++ [e] = Lk ++ z :: e :: ([] : List Card)
        rw [hLk, List.append_assoc]
        rfl⟩

/-! ## §7. The end-state fit read

The invariant is purely positional; the FIT enters exactly once, at
the end state, from the pile discipline's own `runOK` adjacency. -/

/-- A legal run's adjacent pair reads as a fit: the card directly
below fits under the card directly above it. -/
private theorem seat_runOK_adjacent : ∀ (X R : List Card) (c d : Card),
    runOK (X ++ c :: d :: R) = true → canSitOn d c = true := by
  intro X
  induction X with
  | nil =>
      intro R c d hok
      rw [List.nil_append, runOK, Bool.and_eq_true] at hok
      exact hok.1
  | cons w t ih =>
      intro R c d hok
      cases hT : (t ++ c :: d :: R) with
      | nil =>
          exfalso
          have hcmem : c ∈ t ++ (c :: d :: R) :=
            List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
          rw [hT] at hcmem
          exact absurd hcmem (by simp)
      | cons u us =>
          have hok' : runOK (w :: u :: us) = true := by
            rw [← hT]
            exact hok
          rw [runOK, Bool.and_eq_true] at hok'
          obtain ⟨-, hrest⟩ := hok'
          rw [← hT] at hrest
          exact ih R c d hrest

/-! ## §8. THE CORE (the journey induction) and the residue's close -/

/-- **THE FOUR-WAY CARRY** (internal) — the orphan's zone package is
carried along any witness journey, per move letter.  The collapsed
core `Below_stable` wraps this carry: the union and hidden arms
cannot be entered from a founded-or-seated start, so its end-read
kills them by the banked bars. -/
private theorem seat_zone_carry {st : State} {d : Card}
    (hnk : d.rank ≠ Rank.king) :
    ∀ {u : State} {τ : List Move},
    ShufflePlayW st τ u → st.WF → SeatZone st d → SeatZone u d := by
  intro u τ h
  induction h with
  | nil s =>
      intro _hwf hc
      exact hc
  | @cons s₀ mv s₁ rest w₀ hrev hstep hrest ih =>
      intro hwf hc
      have hwf₁ : s₁.WF := step_wf hwf hstep
      cases mv with
      | draw =>
          exact ih hwf₁ (seat_step_draw hstep hrev hc)
      | wasteToFound c =>
          exact ih hwf₁ (seat_step_wasteFound hstep hrev)
      | wasteToTab c b =>
          exact ih hwf₁ (seat_step_wasteTab hstep hrev)
      | tabToFound c =>
          exact ih hwf₁ (seat_step_raise hstep hrev hc)
      | foundToTab c b =>
          exact ih hwf₁ (seat_step_pull hstep hrev hnk hc)
      | tabToTab c b =>
          exact ih hwf₁ (seat_step_cargo hwf hstep hrev hnk hc)

/-! ### The collapsed transport — the public two-disjunct core -/

/-- **THE BELOW-NEIGHBOR STABILITY** — the orphan's collapsed
package is TWO disjuncts only: founded, or seated on a face-up
below-neighbor.  Over any witness journey the draw-cycle and hidden
arms cannot be entered from such a start (the waste movers and the
reveal legs never ride, so nothing moves a resident into the stock,
the waste, or a hidden deck), so the two dated arms of the four-way
carry die at the end by the never-gain union row and the hidden pin.
Both consumers read this row at endpoints: the residue (founded
start, the found arm dying at `hout`; equivalently the exodus-split
route below) and the confine-side seam (`hseed` IS a `Below`
shape). -/
theorem Below_stable {st u : State} (hwf : st.WF) {τ : List Move}
    (hτ : ShufflePlayW st τ u) {d : Card} (hnk : d.rank ≠ Rank.king)
    (hstart : d ∈ st.found d.suit ∨ ∃ z, Below st d z) :
    d ∈ u.found d.suit ∨ ∃ z, Below u d z := by
  have hSW : d ∉ st.stock ∧ d ∉ st.waste := by
    rcases hstart with hF | ⟨z, a, L, R, hs⟩
    · obtain ⟨-, hS, hW, -⟩ := mem_found_unique hwf hF
      exact ⟨hS, hW⟩
    · have hdm : d ∈ (st.piles a).faceUp := by
        rw [hs]
        exact List.mem_append.mpr (Or.inr
          (List.mem_cons.mpr (Or.inr (List.mem_cons_self ..))))
      obtain ⟨-, -, hS, hW, -⟩ := mem_faceUp_only hwf hdm
      exact ⟨hS, hW⟩
  have hHid : ∀ k, d ∉ (st.piles k).hidden := by
    intro k
    rcases hstart with hF | ⟨z, a, L, R, hs⟩
    · exact (mem_found_unique hwf hF).1 k |>.1
    · have hdm : d ∈ (st.piles a).faceUp := by
        rw [hs]
        exact List.mem_append.mpr (Or.inr
          (List.mem_cons.mpr (Or.inr (List.mem_cons_self ..))))
      by_cases hka : k = a
      · rw [hka]
        exact (mem_faceUp_only hwf hdm).2.1
      · exact ((mem_faceUp_only hwf hdm).1 k hka).1
  have hz4 : SeatZone st d := by
    rcases hstart with hF | hB
    · exact Or.inl hF
    · exact Or.inr (Or.inr (Or.inr hB))
  rcases seat_zone_carry hnk hτ hwf hz4 with hF | hU | hH | hB
  · exact Or.inl hF
  · exfalso
    rcases seat_union_nogain hτ d hU with hS | hW
    · exact hSW.1 hS
    · exact hSW.2 hW
  · exfalso
    obtain ⟨k, hk⟩ := hH
    rw [shuffle_hiddenPinned hτ k] at hk
    exact hHid k hk
  · exact Or.inr hB

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
  -- THE EXODUS SPLIT: the literal own-pull leg inside the shuffle
  obtain ⟨b, hleg⟩ := orphan_found_exodus (d := e) hτ hmem hout
  obtain ⟨ρ₁, ρ₂, sM, sL, -, hj₁, hrev, hlegstep, hj₂⟩ :=
    seat_journey_split hleg hτ
  -- THE LANDING SEED: the leg's own write is the seat shape
  obtain ⟨a₀, L₀, R₀, z₀, hsL⟩ := seat_landing_seed hlegstep hnk
  -- THE SUFFIX TRANSPORT: founded-at-end dies by hout; seated gives
  -- the end-state Below witness
  have hjLeg : ShufflePlayW sM [Move.foundToTab e b] sL :=
    .cons hrev hlegstep (.nil sL)
  have hjPre : ShufflePlayW st (ρ₁ ++ [Move.foundToTab e b]) sL :=
    ShufflePlayW_append hj₁ hjLeg
  have hwfsL : sL.WF := seat_wf_along hjPre hwf
  rcases Below_stable hwfsL hj₂ hnk (Or.inr ⟨z₀, a₀, L₀, R₀, hsL⟩) with
    hF | ⟨z, a, L, R, hshape⟩
  · exact absurd hF hout
  · refine ⟨a, z, ?_, ?_, ?_⟩
    · rw [hshape]
      exact List.mem_append.mpr (Or.inr
        (List.mem_cons.mpr (Or.inr (List.mem_cons_self ..))))
    · rw [hshape]
      exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
    · have hrok : runOK (L ++ z :: e :: R) = true := by
        rw [← hshape]
        exact (seat_wf_along hj₂ hwfsL).2.1 a
      exact seat_runOK_adjacent L R z e hrok

/-! ## The audit battery

`#print axioms` per fresh head — the probe by kernel decide, the
exodus wheel and the collapsed transport over the banked rows: zero
`sorry`, zero `Classical.choice`, zero `native_decide`. -/

#print axioms Below
#print axioms orphan_found_exodus
#print axioms Below_stable
#print axioms cross_orphan_seat
#print axioms probe_ride_blessed
#print axioms probe_dead_surfaced
