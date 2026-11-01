import Orig2.ForkCrossSuitPartition
import Orig2.Integrity
import Orig2.PairClassSeed

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Off_WindowSlide — the prepared seat is a TWIN SEAT EXCHANGE

READ-ONLY scratch card (`Temp/`).  No source edit, no commit.  Zero `sorry`,
zero `Classical.choice`, zero `nativeDecide`; axiom battery at the tail.

## The arithmetic

The partition card (`Orig2/ForkCrossSuitPartition.lean`) proves that a
`¬ Pullable B d b` corridor forces the free window `γ` to contain a slide
(`slide_of_seat_change`).  This card computes *which* slide.

Let the pull be `pull d (inr z)` and suppose the window exposes `z` by
sliding its cover `p` off it.  Then

```text
p was on z   ⇒ p.rank + 1 = z.rank,   colour p ≠ colour z
d lands on z ⇒ d.rank + 1 = z.rank,   colour d ≠ colour z
            ⇒ p.rank = d.rank,        colour p = colour d
```

A rank/colour class has exactly two cards (they are twins), and `WF` counts
every card once, so `p ≠ d`.  Hence **`p = d.twin`** (`slide_expose_card_twin`).
The slide's base `y` then satisfies `y = inr z.twin` — never an empty pile,
because that would demand `p` (hence `d`) be a king and `z.rank = 13`
(`slide_expose_base_not_inl`, `slide_expose_base_eq_twin`).

So the offending slide is exactly the **twin seat exchange**

```text
slide d.twin : z → z.twin
pull  d      : foundation → z
```

## What is closed and what is left

* Closed: the exposing slide's **empty-pile base is impossible**, so the
  slide is pinned to `z → z.twin` (`slide_expose_base_eq_twin`).  The
  `seat` variant `Seat.king_cover_is_queen` is the cover direction; this is
  the slide direction and here the king case *dies*.
* Closed: the exposing slide is **both** `SlideFwd.ReadSafe` for `d` and
  `MtnPr.SeatInert` on `b = inr z` (`slide_expose_readSafe`,
  `slide_expose_seatInert`).  So the offending letter at least cannot be
  charged to `NoReadUnsafe` or `NoSeatActing`; a single-slide window is
  entirely nice (`twin_exchange_window_nice`).  The prepared-seat face is
  therefore genuinely separate from the other two complement faces.
* Corridor form: `corridor_single_slide_twin` (§7) cuts the partition card's
  corridor at the raise and at the window and lands the identity on the face.
* Residual (`TwinExchangeWindow`, §5): the window's exposing slide is the
  twin exchange, and nothing in the *arithmetic* contradicts it — the seat is
  legal.  The remaining content is the saturation/minimality lock (the
  seat-mate lane, `Blocks.NoSeatMateCrossSuit`), plus the non-cover windows
  where `z` is not face-up directly under the mover (`RevealResidual`), plus
  the `inl` pull base (`inl_nonempty_of_not_pullable`, the king residual).
-/

namespace OffWindow

/-! ## §1. A rank/colour class is a twin pair -/

/-- Cards of one rank and one colour are a two-card class: a card is itself or
its twin.  (Local restatement of `Seat.eq_or_twin_of_rank_color`.) -/
theorem eq_or_twin_of_rank_color {x y : Card} (hr : x.rank = y.rank)
    (hc : x.suit.color = y.suit.color) : x = y ∨ x = y.twin := by
  rcases x with ⟨sx, rx⟩
  rcases y with ⟨sy, ry⟩
  simp only at hr hc
  subst hr
  by_cases h : sx = sy
  · exact Or.inl (by rw [h])
  · refine Or.inr ?_
    have hsym : sy = sx.twin := by
      cases sx <;> cases sy <;> simp_all [Suit.color, Suit.twin]
    show (⟨sx, rx⟩ : Card) = ⟨sy.twin, rx⟩
    rw [hsym, Suit.twin_twin]

/-- **THE IDENTITY, ARITHMETIC FORM.**  Two distinct cards that both fit on the
same `z` have the same rank and the same colour, hence are twins. -/
theorem twin_of_two_fits {p d z : Card}
    (hp : p.rank.toIdx + 1 = z.rank.toIdx) (hpc : p.suit.color ≠ z.suit.color)
    (hd : d.rank.toIdx + 1 = z.rank.toIdx) (hdc : d.suit.color ≠ z.suit.color)
    (hne : p ≠ d) : p = d.twin := by
  have hrank : p.rank = d.rank := Rank.toIdx_inj (by omega)
  have hcol : p.suit.color = d.suit.color := Blocks.color_eq_of_ne_ne hpc hdc
  rcases eq_or_twin_of_rank_color hrank hcol with h | h
  · exact absurd h hne
  · exact h

/-- **THE IDENTITY, BASE FORM.**  If the slide's mover `p` (a fit on `z`) also
fits on `w`, and `w ≠ z`, then the slide's base card is `z.twin`: the two-card
class of `z` supplies no third card. -/
theorem twin_base_of_fits {p d z w : Card}
    (hp : p.rank.toIdx + 1 = z.rank.toIdx) (hpc : p.suit.color ≠ z.suit.color)
    (hd : d.rank.toIdx + 1 = z.rank.toIdx) (hdc : d.suit.color ≠ z.suit.color)
    (hne : p ≠ d)
    (hpw : p.rank.toIdx + 1 = w.rank.toIdx) (hpcw : p.suit.color ≠ w.suit.color)
    (hwz : w ≠ z) : w = z.twin := by
  have hpt : p = d.twin := twin_of_two_fits hp hpc hd hdc hne
  have hpcol : p.suit.color = d.suit.color := Blocks.color_eq_of_ne_ne hpc hdc
  have hwr : w.rank = z.rank := by
    have : w.rank.toIdx = z.rank.toIdx := by
      have h23 : p.rank.toIdx = d.rank.toIdx := by rw [hpt]; rfl
      omega
    exact Rank.toIdx_inj this
  have hwc : w.suit.color = z.suit.color := by
    have hwd : w.suit.color ≠ d.suit.color := by
      rw [hpcol] at hpcw
      exact fun h => hpcw h.symm
    exact Blocks.color_eq_of_ne_ne hwd (fun h => hdc h.symm)
  rcases eq_or_twin_of_rank_color hwr hwc with h | h
  · exact absurd h hwz
  · exact h

/-! ## §2. The slide step's foundation transport -/

/-- A slide leaves the foundation exactly as it was. -/
theorem slide_found_eq {B C : State} {p : Card} {y : Base}
    (h : State.step B (Move.tabToTab p y) = some C) : C.found = B.found := by
  obtain ⟨a, -, -, -, rfl⟩ := CommuteStep.step_tabToTab_slideSt h
  exact CommuteStep.slideSt_found B p y a

/-- A slide's launch guard is `canPlace`. -/
theorem slide_canPlace {B C : State} {p : Card} {y : Base}
    (h : State.step B (Move.tabToTab p y) = some C) :
    B.canPlace p y = true := by
  obtain ⟨a, -, hcp, -, -⟩ := CommuteStep.step_tabToTab_slideSt h
  exact hcp

/-! ## §3. The exposing slide, at the kernel -/

/-- **THE TWIN IDENTITY AT THE KERNEL.**  At a `WF` state, if the face-up run
of pile `a` reads `front ++ z :: p :: rest` (so `p` sits directly on `z`), and
the pull `foundToTab d (inr z)` fires after sliding `p` away, then
`p = d.twin`.

The three inputs are exactly the task's:
* `runOK` gives `p`'s fit on `z`;
* the pull step gives `d`'s fit on `z` and the foundation top `d`;
* `WF` (`mem_found_unique`) gives `p ≠ d`.
-/
theorem slide_expose_card_twin
    {B C Pv : State} {a : Anchor} {front rest : List Card} {p z d : Card} {y : Base}
    (hBwf : B.WF)
    (hface : (B.piles a).faceUp = front ++ z :: p :: rest)
    (hslide : State.step B (Move.tabToTab p y) = some C)
    (hpull : State.step C (Move.foundToTab d (Sum.inr z)) = some Pv) :
    p = d.twin := by
  -- the pull's landing guard and foundation top
  obtain ⟨c', hft, hc', hcp, -⟩ := step_foundToTab_inv hpull
  rw [hc'] at hft
  obtain ⟨_k, -, hfitd⟩ := canPlace_inr hcp
  obtain ⟨hdz, hdcol⟩ := (canSitOn_eq d z).mp hfitd
  -- the foundation card is in the foundation, hence in no pile (WF)
  have hfoundC : d ∈ C.found d.suit := lastOf_mem hft
  rw [slide_found_eq hslide] at hfoundC
  have hnotface : d ∉ (B.piles a).faceUp := (mem_found_unique hBwf hfoundC).1 a |>.2
  have hp_mem : p ∈ (B.piles a).faceUp := by rw [hface]; simp
  have hne : p ≠ d := fun hpd => hnotface (hpd ▸ hp_mem)
  -- `p`'s fit on `z` from the run discipline
  have hrok : runOK (B.piles a).faceUp = true := hBwf.runOK_of a
  rw [hface] at hrok
  have hpz := SeedKit.runOK_adjacent_fit z p front rest hrok
  obtain ⟨hpzr, hpzc⟩ := (canSitOn_eq p z).mp hpz
  exact twin_of_two_fits hpzr hpzc hdz hdcol hne

/-- **THE BASE IDENTITY AT THE KERNEL.**  If in addition the slide lands on an
`inr w` base with `w ≠ z`, then `w = z.twin`. -/
theorem slide_expose_base_twin
    {B C Pv : State} {a : Anchor} {front rest : List Card} {p z d w : Card} {y : Base}
    (hBwf : B.WF)
    (hface : (B.piles a).faceUp = front ++ z :: p :: rest)
    (hslide : State.step B (Move.tabToTab p y) = some C)
    (hpull : State.step C (Move.foundToTab d (Sum.inr z)) = some Pv)
    (hy : y = Sum.inr w) (hwz : w ≠ z) :
    w = z.twin := by
  -- re-derive the shared fits
  obtain ⟨c', hft, hc', hcp, -⟩ := step_foundToTab_inv hpull
  rw [hc'] at hft
  obtain ⟨_k, -, hfitd⟩ := canPlace_inr hcp
  obtain ⟨hdz, hdcol⟩ := (canSitOn_eq d z).mp hfitd
  have hfoundC : d ∈ C.found d.suit := lastOf_mem hft
  rw [slide_found_eq hslide] at hfoundC
  have hnotface : d ∉ (B.piles a).faceUp := (mem_found_unique hBwf hfoundC).1 a |>.2
  have hp_mem : p ∈ (B.piles a).faceUp := by rw [hface]; simp
  have hne : p ≠ d := fun hpd => hnotface (hpd ▸ hp_mem)
  have hrok : runOK (B.piles a).faceUp = true := hBwf.runOK_of a
  rw [hface] at hrok
  have hpz := SeedKit.runOK_adjacent_fit z p front rest hrok
  obtain ⟨hpzr, hpzc⟩ := (canSitOn_eq p z).mp hpz
  -- the slide's launch fit on its base
  have hcpS := slide_canPlace hslide
  rw [hy] at hcpS
  obtain ⟨_k2, -, hpw⟩ := canPlace_inr hcpS
  obtain ⟨hpwr, hpwc⟩ := (canSitOn_eq p w).mp hpw
  exact twin_base_of_fits hpzr hpzc hdz hdcol hne hpwr hpwc hwz

/-- **THE EMPTY-PILE BASE DIES — the slide direction of the king case.**  If
the slide's base were `inl a`, the mover `p` would be a king; but `p = d.twin`
and `d.rank + 1 = z.rank` make `d` a king too, forcing `z.rank = 13`, which no
rank has.  So the exposing slide is never `z → empty pile`. -/
theorem slide_expose_base_not_inl
    {B C Pv : State} {a : Anchor} {front rest : List Card} {p z d : Card} {y : Base}
    (hBwf : B.WF)
    (hface : (B.piles a).faceUp = front ++ z :: p :: rest)
    (hslide : State.step B (Move.tabToTab p y) = some C)
    (hpull : State.step C (Move.foundToTab d (Sum.inr z)) = some Pv)
    (hinl : ∃ a', y = Sum.inl a') : False := by
  have hpt : p = d.twin :=
    slide_expose_card_twin hBwf hface hslide hpull
  obtain ⟨c', hft, hc', hcp, -⟩ := step_foundToTab_inv hpull
  rw [hc'] at hft
  obtain ⟨_k, -, hfitd⟩ := canPlace_inr hcp
  obtain ⟨hdz, -⟩ := (canSitOn_eq d z).mp hfitd
  have hcpS := slide_canPlace hslide
  obtain ⟨a', rfl⟩ := hinl
  obtain ⟨-, hpk⟩ := canPlace_inl hcpS
  have hdk : d.rank = Rank.king := by
    have : d.twin.rank = Rank.king := by rw [← hpt]; exact hpk
    simpa [Card.twin] using this
  have h13 : z.rank.toIdx = 13 := by
    rw [hdk] at hdz
    have : Rank.king.toIdx = 12 := rfl
    omega
  have hlt := Rank.toIdx_lt z.rank
  omega

/-- **THE EXPOSING SLIDE IS EXACTLY `z → z.twin`.**  Combining the base identity
with the death of the empty-pile base. -/
theorem slide_expose_base_eq_twin
    {B C Pv : State} {a : Anchor} {front rest : List Card} {p z d : Card} {y : Base}
    (hBwf : B.WF)
    (hface : (B.piles a).faceUp = front ++ z :: p :: rest)
    (hslide : State.step B (Move.tabToTab p y) = some C)
    (hpull : State.step C (Move.foundToTab d (Sum.inr z)) = some Pv) :
    y = Sum.inr z.twin := by
  cases y with
  | inl a' =>
      exact absurd ⟨a', rfl⟩
        (slide_expose_base_not_inl hBwf hface hslide hpull)
  | inr w =>
      -- the base card cannot be `z` itself: the slide would need `z` as a pile top
      have hwz : w ≠ z := by
        intro hwz
        subst w
        have hcp : B.canPlace p (Sum.inr z) = true := by
          simpa using slide_canPlace hslide
        obtain ⟨k, hk, -⟩ := canPlace_inr hcp
        have htopk : (B.piles k).top = some z := (pileOfTop_eq_some_iff hBwf).1 hk
        have hzmem : z ∈ (B.piles a).faceUp := by rw [hface]; simp
        have hka : k = a := by
          by_cases hka : k = a
          · exact hka
          · exfalso
            exact ((mem_faceUp_only hBwf hzmem).1 k hka).2 (Pile.mem_of_top htopk)
        have htopa : (B.piles a).top = some z := by rwa [hka] at htopk
        -- but `z` sits below `p`, so it is not the last card of the run
        have hnd : (front ++ z :: p :: rest).Nodup := by
          simpa [hface] using runOK_nodup (hBwf.runOK_of a)
        have hnd2 : (z :: p :: rest).Nodup := (List.nodup_append.mp hnd).2.1
        have hznot : z ∉ p :: rest := (List.nodup_cons.mp hnd2).1
        have hlast : lastOf (B.piles a).faceUp = some z := htopa
        rw [hface] at hlast
        have hstep : lastOf (front ++ z :: p :: rest) = lastOf (z :: p :: rest) :=
          CommuteStep.lastOf_append_of_ne_nil (by simp)
        rw [hstep] at hlast
        have : lastOf (p :: rest) = some z := hlast
        exact hznot (lastOf_mem this)
      exact congrArg Sum.inr
        (slide_expose_base_twin hBwf hface hslide hpull rfl hwz)

/-! ## §4. The exposing slide is neither read-unsafe nor seat-acting -/

/-- A card is not its own twin. -/
theorem card_twin_ne (c : Card) : c.twin ≠ c := by
  intro h
  have hs : c.suit.twin = c.suit := by
    simpa [Card.twin] using congrArg Card.suit h
  exact Suit.twin_ne c.suit hs

/-- A card that sits one rank below `z` is not `z` (and not `z.twin`). -/
theorem card_ne_of_fit {p z : Card} (h : p.rank.toIdx + 1 = z.rank.toIdx) : p ≠ z := by
  intro hEq
  rw [hEq] at h
  omega

/-- **THE `z.twin` IS NOT THE PULL'S CARD.**  Rank bookkeeping: `d` sits one
rank below `z`, while `z.twin` has `z`'s rank. -/
theorem twin_card_ne_of_fit {d z : Card} (h : d.rank.toIdx + 1 = z.rank.toIdx) :
    z.twin ≠ d := by
  intro hEq
  have hr : d.rank = z.rank := by rw [← hEq]; rfl
  have hi : d.rank.toIdx = z.rank.toIdx := congrArg Rank.toIdx hr
  omega

/-- **THE EXPOSING SLIDE IS READ-SAFE FOR THE PULL.**  It moves `d.twin` and
lands on `z.twin`, so it never touches `d` or its would-be base `z`. -/
theorem slide_expose_readSafe {p z d : Card}
    (hpt : p = d.twin) (hdz : d.rank.toIdx + 1 = z.rank.toIdx) :
    SlideFwd.ReadSafe d (Move.tabToTab p (Sum.inr z.twin)) := by
  refine SlideFwd.readSafe_slide_of_ne ?_ ?_
  · rw [hpt]; exact card_twin_ne d
  · intro hEq
    exact twin_card_ne_of_fit hdz (Sum.inr.inj hEq)

/-- **THE EXPOSING SLIDE IS SEAT-INERT ON `inr z`.**  It moves *away* from
`z` (onto `z.twin`), so it never writes `z`'s pile and never lifts `z`. -/
theorem slide_expose_seatInert {p z : Card}
    (hpz : p.rank.toIdx + 1 = z.rank.toIdx) :
    MtnPr.SeatInert (Sum.inr z) (Move.tabToTab p (Sum.inr z.twin)) := by
  refine ⟨?_, ?_⟩
  · intro hEq
    have hc : z.twin = z := Sum.inr.inj hEq
    have hs : z.suit.twin = z.suit := by
      simpa [Card.twin] using congrArg Card.suit hc
    exact Suit.twin_ne z.suit hs
  · exact card_ne_of_fit hpz

/-! ## §5. The corridor-level pin: the twin seat exchange -/

/-- The exact single-slide shape a prepared seat takes:
`z` sits directly below its cover `p` at the raise's image `B`, the window
slides the cover onto `z.twin`, and the pull then lands `d` on `z`. -/
structure TwinExchangeWindow (B C Pv : State) (a : Anchor) (front rest : List Card)
    (p z d : Card) : Prop where
  /-- The raise's image is well-formed. -/
  wf : B.WF
  /-- `z` is face-up, directly below its cover `p`. -/
  face : (B.piles a).faceUp = front ++ z :: p :: rest
  /-- The window's slide: `d.twin` off `z`, onto `z.twin`. -/
  slide : State.step B (Move.tabToTab p (Sum.inr z.twin)) = some C
  /-- The pull: `d` off the foundation, onto the exposed `z`. -/
  pull : State.step C (Move.foundToTab d (Sum.inr z)) = some Pv

/-- **THE PULL AND THE SLIDE ARE TWINS.**  In the twin-exchange window the
slide's mover is exactly the pull's card's twin. -/
theorem twin_exchange_card {B C Pv : State} {a : Anchor} {front rest : List Card}
    {p z d : Card} (h : TwinExchangeWindow B C Pv a front rest p z d) :
    p = d.twin :=
  slide_expose_card_twin h.wf h.face h.slide h.pull

/-- **THE TWIN SEAT EXCHANGE IS LEGAL.**  Both halves fire: `d.twin` may be
placed on `z.twin` and `d` on `z`. -/
theorem twin_exchange_legal {B C Pv : State} {a : Anchor} {front rest : List Card}
    {p z d : Card} (h : TwinExchangeWindow B C Pv a front rest p z d) :
    B.canPlace d.twin (Sum.inr z.twin) = true ∧
      C.canPlace d (Sum.inr z) = true := by
  have hpt := twin_exchange_card h
  constructor
  · have := slide_canPlace h.slide
    rwa [hpt] at this
  · obtain ⟨_c', -, -, hcp, -⟩ := step_foundToTab_inv h.pull
    exact hcp

/-- **THE EXPOSING SLIDE IS IN NEITHER COMPLEMENT FACE 2 OR 3.**  In the
twin-exchange window the offending slide is read-safe for the pull and
seat-inert on its base.  So this witness cannot be charged to
`NoReadUnsafe` or `NoSeatActing`. -/
theorem twin_exchange_window_clean {B C Pv : State} {a : Anchor} {front rest : List Card}
    {p z d : Card} (h : TwinExchangeWindow B C Pv a front rest p z d) :
    SlideFwd.ReadSafe d (Move.tabToTab p (Sum.inr z.twin)) ∧
      MtnPr.SeatInert (Sum.inr z) (Move.tabToTab p (Sum.inr z.twin)) := by
  have hpt := twin_exchange_card h
  obtain ⟨_c', -, -, hcp, -⟩ := step_foundToTab_inv h.pull
  obtain ⟨_k, -, hfitd⟩ := canPlace_inr hcp
  obtain ⟨hdz, -⟩ := (canSitOn_eq d z).mp hfitd
  -- the mover's fit on `z` (for the seat-inert rank datum)
  have hrok : runOK (B.piles a).faceUp = true := h.wf.runOK_of a
  rw [h.face] at hrok
  have hpz := SeedKit.runOK_adjacent_fit z p front rest hrok
  obtain ⟨hpzr, -⟩ := (canSitOn_eq p z).mp hpz
  exact ⟨slide_expose_readSafe hpt hdz, slide_expose_seatInert hpzr⟩

/-- **A SINGLE-SLIDE PREPARED SEAT IS A NICE WINDOW.**  The only free letter —
the exposing slide — satisfies both window predicates, so the corridor is in
neither `NoReadUnsafe` nor `NoSeatActing`. -/
theorem twin_exchange_window_nice {B C Pv : State} {a : Anchor} {front rest : List Card}
    {p z d : Card} (h : TwinExchangeWindow B C Pv a front rest p z d) :
    (∀ q ∈ [Move.tabToTab p (Sum.inr z.twin)], SlideFwd.ReadSafe d q) ∧
      (∀ q ∈ [Move.tabToTab p (Sum.inr z.twin)], MtnPr.SeatInert (Sum.inr z) q) := by
  obtain ⟨hrd, hst⟩ := twin_exchange_window_clean h
  exact ⟨fun q hq => by
      rw [List.mem_singleton] at hq; subst hq; exact hrd,
    fun q hq => by
      rw [List.mem_singleton] at hq; subst hq; exact hst⟩

/-- **THE PARTITION FACE'S OFFENDING SLIDE, NAMED.**  A `¬ Pullable` corridor
whose window is the single exposing slide is exactly the twin seat exchange:
`p = d.twin`, the slide lands on `z.twin`, the empty-pile base is impossible,
and the slide is read-safe and seat-inert. -/
theorem prepared_seat_single_slide_is_twin_exchange
    {B C Pv : State} {a : Anchor} {front rest : List Card} {p z d : Card}
    (hBwf : B.WF)
    (hface : (B.piles a).faceUp = front ++ z :: p :: rest)
    (hslide : State.step B (Move.tabToTab p (Sum.inr z.twin)) = some C)
    (hpull : State.step C (Move.foundToTab d (Sum.inr z)) = some Pv) :
    p = d.twin ∧
      SlideFwd.ReadSafe d (Move.tabToTab p (Sum.inr z.twin)) ∧
      MtnPr.SeatInert (Sum.inr z) (Move.tabToTab p (Sum.inr z.twin)) ∧
      B.canPlace d.twin (Sum.inr z.twin) = true := by
  let W : TwinExchangeWindow B C Pv a front rest p z d :=
    ⟨hBwf, hface, hslide, hpull⟩
  exact ⟨twin_exchange_card W, twin_exchange_window_clean W |>.1,
    twin_exchange_window_clean W |>.2, twin_exchange_legal W |>.1⟩

/-! ## §6. The exact residual

The arithmetic above is not enough to contradict `NoWindowPreparedSeat`: the
twin exchange is a **legal** two-move seat relay (both halves fire,
`twin_exchange_legal`).  Two things remain outside the identity:

* `TwinExchangeWindow` itself — the seat relay must be excluded by the
  saturation/minimality lock (the seat-mate lane, `Blocks.NoSeatMateCrossSuit`),
  not by rank/colour arithmetic.  This card proves the cover case *is* the twin
  exchange, so that remaining content is exactly it.
* `RevealResidual` — a slide that empties a pile's face-up run and reveals `z`
  from the hidden deck.  Then `z` was never below the mover, so no twin
  identity is available from the slide; the pull's rank/colour read still fixes
  `d`, but `p` is only the bottom of the emptied run.
-/

/-- The only other single-slide way to expose `z`: `z` was the hidden card
revealed when a pile's whole face-up run was slid away.  Concretely, the cover
run is the *entire* face-up stack (`below p faceUp = []`, so nothing sits below
the mover) and `z` is the head of the hidden deck.  No twin identity connects
`p` and `d` in this case.

**THE STATE PREDICATE IS INHABITED** (`Reveal.revealResidual_of_singleton`):
any singleton face-up run over a nonempty hidden deck qualifies, so do NOT try
to prove `¬ RevealResidual`.  The VOID is at the LETTER GRADE: a reveal slide
strictly drops `hiddenTotal`, no legal step raises it, so the slide is not
`reversibleAtW` and is never a `ShufflePlayW` letter.  See `Orig2/ForkReveal.lean`
(`reveal_not_witness_letter`, `corridor_reveal_window_impossible`,
`reveal_not_twin_window`).  The face is closed by the reversibility oracle, not
by an empty predicate. -/
def RevealResidual (B : State) (a : Anchor) (p z : Card) : Prop :=
  (B.piles a).faceUp ≠ [] ∧ below p (B.piles a).faceUp = [] ∧
    ∃ rest, (B.piles a).hidden = z :: rest

/-- **`z` IS NOT A PILE TOP AT THE RAISE'S IMAGE.**  In the `¬ Pullable` face
with the pull legal later and the foundation fixed, the failure is purely
`z`-coverage: if `z` topped a pile at `B`, the pull's fit (state-free) would
already make it `Pullable`.  So the window must *uncover* `z`. -/
theorem pileOfTop_none_of_not_pullable {B P : State} {d z : Card}
    (hnp : ¬ PullKit.Pullable B d (Sum.inr z))
    (hpull : PullKit.Pullable P d (Sum.inr z))
    (htop : ∀ σ : Suit, B.foundTop σ = P.foundTop σ) :
    B.pileOfTop z = none := by
  cases h : B.pileOfTop z with
  | none => rfl
  | some k =>
      exfalso
      obtain ⟨_kP, -, hfit⟩ := canPlace_inr hpull.2
      have hcp : B.canPlace d (Sum.inr z) = true := by
        rw [canPlace_inr_located h]
        exact hfit
      exact hnp ⟨by rw [htop]; exact hpull.1, hcp⟩

/-- **`z` IS NOT A PILE TOP AT THE RAISE'S IMAGE (CORRIDOR FORM).**  The free
window fixes every foundation top (`foundTop_free_window`), so the
`¬ Pullable` face with a later `inr z` pull forces `z` to be *covered* at `B`:
the window must uncover it. -/
theorem pileOfTop_none_of_window_not_pullable {B P : State} {γ : List Move} {d z : Card}
    (hγ : ShufflePlayW B γ P) (hfree : Canon.FreeOnly γ)
    (hnp : ¬ PullKit.Pullable B d (Sum.inr z))
    (hpull : PullKit.Pullable P d (Sum.inr z)) :
    B.pileOfTop z = none :=
  pileOfTop_none_of_not_pullable hnp hpull
    (fun σ => CrossSuitPart.foundTop_free_window σ hγ hfree)

/-- **THE `inl` PULL BASE IS THE KING RESIDUAL.**  If the pull lands on an
empty pile `a` later but not at `B` (foundation fixed), then `d` is a king and
`a` is **nonempty** at `B`: the window emptied the whole file, and the pull puts
a king into the vacated seat.  No rank/colour datum connects the slide's mover
to `d` here — this is the king (`Seat.king_cover_is_queen`) residual, separate
from the twin exchange. -/
theorem inl_nonempty_of_not_pullable {B P : State} {d : Card} {a : Anchor}
    (hnp : ¬ PullKit.Pullable B d (Sum.inl a))
    (hpull : PullKit.Pullable P d (Sum.inl a))
    (htop : ∀ σ : Suit, B.foundTop σ = P.foundTop σ) :
    (B.piles a).isEmpty = false := by
  cases h : (B.piles a).isEmpty with
  | false => rfl
  | true =>
      exfalso
      obtain ⟨-, hk⟩ := canPlace_inl hpull.2
      have hcp : B.canPlace d (Sum.inl a) = true := by
        rw [canPlace_inl_unfold, h]
        simp [hk]
      exact hnp ⟨by rw [htop]; exact hpull.1, hcp⟩

/-- The king residual's window form. -/
theorem inl_nonempty_of_window_not_pullable {B P : State} {γ : List Move} {d : Card}
    {a : Anchor} (hγ : ShufflePlayW B γ P) (hfree : Canon.FreeOnly γ)
    (hnp : ¬ PullKit.Pullable B d (Sum.inl a))
    (hpull : PullKit.Pullable P d (Sum.inl a)) :
    (B.piles a).isEmpty = false :=
  inl_nonempty_of_not_pullable hnp hpull
    (fun σ => CrossSuitPart.foundTop_free_window σ hγ hfree)

theorem pull_card_not_king {d z : Card} (h : d.rank.toIdx + 1 = z.rank.toIdx) :
    d.rank ≠ Rank.king := by
  intro hk
  have hi : d.rank.toIdx = 12 := by rw [hk]; rfl
  have hlt := Rank.toIdx_lt z.rank
  omega

/-- The twin branch is forced: in the cover case the two cards of the corridor
are twins, never a king pair. -/
theorem twin_branch_not_king {p d z : Card}
    (hpz : p.rank.toIdx + 1 = z.rank.toIdx) (hpc : p.suit.color ≠ z.suit.color)
    (hdz : d.rank.toIdx + 1 = z.rank.toIdx) (hdc : d.suit.color ≠ z.suit.color)
    (hne : p ≠ d) : p = d.twin ∧ d.rank ≠ Rank.king :=
  ⟨twin_of_two_fits hpz hpc hdz hdc hne, pull_card_not_king hdz⟩

/-! ## §7. The identity on the partition face

The partition's corridor `pre ; raise c ; γ ; pull d b ; tail` is cut at the
raise and at the window, and the single-slide window's move is fed to the
kernel identity.  This is the corridor-level form of `slide_expose_card_twin`.
-/

/-- Two witness plays on the same letter list end at the same state. -/
theorem walk_end_unique {P : State → Move → Prop} {u A A' : State} {pre : List Move}
    (h1 : Walk P u pre A) (h2 : Walk P u pre A') : A = A' :=
  Option.some.inj ((Walk_run P h1).symm.trans (Walk_run P h2))

/-- **THE PREPARED SEAT OF A SINGLE-SLIDE CORRIDOR IS THE TWIN EXCHANGE.**  Take
a witness play split as `pre ; raise c ; [slide p (inr z.twin)] ; pull d b ; tail`
(with `b = inr z`), where at the raise's image `z` is face-up directly below its
cover `p`.  Then the slide's mover is `d.twin`: the corridor's offending slide
is the twin seat exchange. -/
theorem corridor_single_slide_twin
    {u v : State} {ρ pre γ tail : List Move} {c d : Card} {b : Base} {A B : State}
    {p z : Card} {a : Anchor} {front rest : List Card}
    (huwf : u.WF)
    (hplay : ShufflePlayW u ρ v)
    (heq : ρ = pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))))
    (hpre : ShufflePlayW u pre A)
    (hstepR : State.step A (Move.tabToFound c) = some B)
    (hγ : γ = [Move.tabToTab p (Sum.inr z.twin)])
    (hface : (B.piles a).faceUp = front ++ z :: p :: rest)
    (hb : b = Sum.inr z) :
    p = d.twin := by
  have hAwf : A.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  have hBwf : B.WF := step_wf hAwf hstepR
  -- cut at the raise
  have hdecomp : ρ = (pre ++ [Move.tabToFound c]) ++
      (γ ++ (Move.foundToTab d b :: tail)) := by
    rw [heq]
    simp [List.append_assoc]
  obtain ⟨B', hleft, hright⟩ :=
    ValleyElim.ShufflePlayW_split hplay _ _ hdecomp
  obtain ⟨M, hupre, hraise⟩ := Bubble.walk_split pre hleft
  have hMA : M = A := walk_end_unique hupre hpre
  obtain ⟨s1, -, hstep1, hnil⟩ := Bubble.walk_cons_inv hraise
  cases hnil
  have hB'B : B' = B := by
    rw [hMA] at hstep1
    exact Option.some.inj (hstep1.symm.trans hstepR)
  rw [hB'B] at hright
  -- cut at the window
  obtain ⟨C, hγwalk, hrest⟩ := Bubble.walk_split γ hright
  rw [hγ] at hγwalk
  obtain ⟨s2, -, hstepS, hnil2⟩ := Bubble.walk_cons_inv hγwalk
  cases hnil2
  -- the pull fires after the window
  obtain ⟨C1, -, hstepP, -⟩ := Bubble.walk_cons_inv hrest
  rw [hb] at hstepP
  exact slide_expose_card_twin hBwf hface hstepS hstepP

end OffWindow

#print axioms OffWindow.eq_or_twin_of_rank_color
#print axioms OffWindow.twin_of_two_fits
#print axioms OffWindow.twin_base_of_fits
#print axioms OffWindow.slide_found_eq
#print axioms OffWindow.slide_expose_card_twin
#print axioms OffWindow.slide_expose_base_twin
#print axioms OffWindow.slide_expose_base_not_inl
#print axioms OffWindow.slide_expose_base_eq_twin
#print axioms OffWindow.card_twin_ne
#print axioms OffWindow.card_ne_of_fit
#print axioms OffWindow.twin_card_ne_of_fit
#print axioms OffWindow.slide_expose_readSafe
#print axioms OffWindow.slide_expose_seatInert
#print axioms OffWindow.twin_exchange_card
#print axioms OffWindow.twin_exchange_legal
#print axioms OffWindow.twin_exchange_window_clean
#print axioms OffWindow.twin_exchange_window_nice
#print axioms OffWindow.prepared_seat_single_slide_is_twin_exchange
#print axioms OffWindow.pull_card_not_king
#print axioms OffWindow.pileOfTop_none_of_not_pullable
#print axioms OffWindow.pileOfTop_none_of_window_not_pullable
#print axioms OffWindow.inl_nonempty_of_not_pullable
#print axioms OffWindow.inl_nonempty_of_window_not_pullable
#print axioms OffWindow.twin_branch_not_king
#print axioms OffWindow.walk_end_unique
#print axioms OffWindow.corridor_single_slide_twin
