import Orig2.ArmFiber
import Orig2.PairClassSeed

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Orig2.Cover — the cover card at a fork

THE COVER'S GEOMETRY, both the pin and the top/base rows, in one card.

At a fork `F` with `ForkWitness F x`, put `y = x.twin` and let `d` be
the cover of `y` (`seatOf F d = some (.inr y)`):

* `cover_pins_of_fork` — `d` sits directly on `y`, the tower above it is
  empty, `d` tops its pile and is NOT `nextUp`; it lives in the opposite
  colour family, one rank below the pair, and its suit rung is at least
  two below the fork rank (the `F4/F5` rank ledger).
* `cover_top_of_fork` — `d` tops its pile.
* `not_nextUp_cover_of_fork` — `d` is not `nextUp`.
* `cover_base_is_twin` — every fitting base of `d` is `x` or `y`.
* `cover_rank_ne_king` — `d` cannot use an empty-anchor base.
* `cover_raise_cascade_*` — the census ledger: raising the cover requires
  a net raise on its suit.

The rows are used by `Orig2/LockRung.lean` (the frozen cover rung and
the mutual-lock invariant) and by `Orig2/ForkClass.lean`.

House compliance: additive leaf (`Orig2.ArmFiber` +
`Orig2.PairClassSeed`); zero `sorry`, zero `Classical.choice`; battery
at the tail.
-/
namespace Card

/-- The twin involution fixes the rank. -/
theorem twin_rank (c : Card) : c.twin.rank = c.rank := rfl

/-- The twin involution writes the twin suit. -/
theorem twin_suit (c : Card) : c.twin.suit = c.suit.twin := rfl

end Card
/-- **THE PILED-RUNG READ** — a face-up card's suit rung sits weakly below its
own rank index (a taller rung would have founded it, against conservation).
Port of the frozen `conf_piled_rung` / `lock_piled_rung`. -/
theorem piled_rung {st : State} (hwf : st.WF) {z : Card} {a : Anchor}
    (hmem : z ∈ (st.piles a).faceUp) : rungAt st z.suit ≤ z.rank.toIdx := by
  rcases Nat.lt_or_ge z.rank.toIdx (rungAt st z.suit) with hlt | hge
  · exfalso
    exact (mem_faceUp_only hwf hmem).2.2.2.2 z.suit
      (FoundKit.mem_found_of_rung hwf hlt)
  · exact hge

/-! ## §2. The cover pin at the fork (port of `pair_cover_pins`) -/

/-- The double-snoc `lastOf` read. -/
theorem lastOf_snoc2 (bs : List Card) (u d : Card) :
    lastOf (bs ++ [u, d]) = some d := by
  have h : bs ++ [u, d] = (bs ++ [u]) ++ [d] := by
    rw [List.append_assoc]
    rfl
  rw [h]
  exact lastOf_snoc

/-- **THE COVER PIN AT THE FORK** — if `y = x.twin` is covered at the fork `F`
by the card `d` (`seatOf F d = some (inr y)`), then `d` sits DIRECTLY on `y`
in its pile, nothing sits above `d`, `d` TOPS that pile, `d` is NOT next-up,
and the cover suit's rung is at least two below the fork rank.

This is `Orig/PairConfine.lean:185 pair_cover_pins` re-derived at the Orig2
seam (`[propext, Quot.sound]` there; the tower bar is the load-bearing part:
any card above `d` would be a same-family card below the fork rank, hence
already founded, hence not face-up). -/
theorem cover_pins_of_fork {st : State} (hwf : st.WF) {x y d : Card}
    (hx : ForkWitness st x) (hxy : y = x.twin)
    (hdseat : seatOf st d = some (Sum.inr y)) :
    ∃ (a : Anchor) (bs : List Card),
      (st.piles a).faceUp = bs ++ [y, d] ∧
      st.pileOfTop d = some a ∧
      st.nextUp d = false ∧
      d.suit.color ≠ x.suit.color ∧
      d.rank.toIdx + 1 = x.rank.toIdx ∧
      rungAt st d.suit + 2 ≤ x.rank.toIdx := by
  -- (1) the S-live twin and its flat shape
  have hliveY : CanRaiseS st y := (hx.1 y).mp (Or.inr hxy)
  have hcov : CoveredAt st y := ⟨d, hdseat⟩
  have hny : ¬ CanRaise st y := not_canRaise_of_covered hwf hcov
  obtain ⟨hnextY, aY, bsY, runY, hshapeY, hseatY, hrunY⟩ :=
    canRaiseS_flat_necessity hwf hliveY
  -- (2) the run above `y` is nonempty (else `y` is vanilla-raisable)
  have hrunne : runY ≠ [] := by
    intro hnil
    rw [hnil] at hshapeY
    have htop : st.pileOfTop y = some aY := by
      refine (pileOfTop_eq_some_iff hwf).2 ?_
      show lastOf (st.piles aY).faceUp = some y
      rw [hshapeY]
      exact lastOf_snoc
    refine hny ⟨hnextY, aY, htop, ?_⟩
    rw [hshapeY, chop_snoc]
    exact hseatY
  -- (3) the cover's own seat read at the twin's pile
  obtain ⟨ad, hhold, hbne, hlast⟩ := tfc_seatOf_of_inr hdseat
  have hdmemPile : d ∈ (st.piles ad).faceUp := pileHolding_mem hhold
  have hdmemY : y ∈ (st.piles aY).faceUp := by
    rw [hshapeY]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  have had : ad = aY := by
    by_cases h : ad = aY
    · exact h
    · exfalso
      have hymemAd : y ∈ (st.piles ad).faceUp := mem_below _ (lastOf_mem hlast)
      exact (mem_faceUp_unique hwf hdmemY ad h).1 hymemAd
  subst ad
  -- the list is `bs ++ [y, d] ++ rest'` from the seat's below-last read
  obtain ⟨bs, hbs⟩ := lastOf_eq_snoc hlast
  obtain ⟨tl, hfc⟩ := fromCard_eq_head_of_mem hdmemPile
  have hface : (st.piles aY).faceUp = bs ++ y :: d :: tl := by
    have hsplit := tfc_below_fromCard d ((st.piles aY).faceUp)
    rw [hbs, hfc] at hsplit
    rw [← hsplit]
    simp [List.append_assoc]
  -- (4) THE TOWER BAR: nothing sits above `d`
  have hrest : tl = [] := by
    cases tl with
    | nil => rfl
    | cons w ws =>
        exfalso
        have hface2 : (st.piles aY).faceUp = bs ++ y :: d :: w :: ws := by
          rw [hface]
        have hrok : runOK (bs ++ y :: d :: w :: ws) = true := by
          rw [← hface2]
          exact hwf.2.1 aY
        have he : (bs ++ [y]) ++ d :: w :: ws = bs ++ y :: d :: w :: ws := by
          simp [List.append_assoc]
        have hrok' : runOK ((bs ++ [y]) ++ d :: w :: ws) = true := by
          rw [he]
          exact hrok
        have hfitD : canSitOn d y = true :=
          SeedKit.runOK_adjacent_fit y d bs (w :: ws) hrok
        have hfitW : canSitOn w d = true :=
          SeedKit.runOK_adjacent_fit d w (bs ++ [y]) ws hrok'
        obtain ⟨hd1, hdc⟩ := (canSitOn_eq d y).mp hfitD
        obtain ⟨hw1, hwc⟩ := (canSitOn_eq w d).mp hfitW
        have hwcol : w.suit.color = y.suit.color :=
          SeedKit.color_pair (a := d.suit.color) (Ne.symm hwc) hdc
        have hwcolx : w.suit.color = x.suit.color := by
          rw [hwcol, hxy]
          exact Suit.color_twin x.suit
        have hyx : y.rank.toIdx = x.rank.toIdx := by rw [hxy, Card.twin_rank]
        have hwlt : w.rank.toIdx < x.rank.toIdx := by omega
        have hmemTail : w ∈ y :: d :: w :: ws :=
          List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
            (Or.inr (List.mem_cons_self ..))))
        have hwmem : w ∈ (st.piles aY).faceUp := by
          rw [hface2]
          exact List.mem_append.mpr (Or.inr hmemTail)
        exact (mem_faceUp_only hwf hwmem).2.2.2.2 w.suit
          (pair_lowFamily_founded hwf hx hwcolx hwlt)
  subst hrest
  have hface' : (st.piles aY).faceUp = bs ++ [y, d] := by
    rw [hface]
  -- (5) `d` tops the twin's pile
  have hdtop : st.pileOfTop d = some aY := by
    refine (pileOfTop_eq_some_iff hwf).2 ?_
    show lastOf (st.piles aY).faceUp = some d
    rw [hface']
    exact lastOf_snoc2 bs y d
  -- (6) the fit arithmetic
  have hfitDY : canSitOn d y = true := by
    refine SeedKit.runOK_adjacent_fit y d bs [] ?_
    rw [← hface']
    exact hwf.2.1 aY
  obtain ⟨hdidx, hdcol⟩ := (canSitOn_eq d y).mp hfitDY
  have hyidx : y.rank.toIdx = x.rank.toIdx := by rw [hxy, Card.twin_rank]
  -- (7) `d` is not next-up (else it is vanilla-raisable against the pair-only iff)
  have hnextD : st.nextUp d = false := by
    cases hb : st.nextUp d with
    | false => rfl
    | true =>
        exfalso
        have hchop : chop (st.piles aY).faceUp ≠ [] := by
          rw [hface']
          rw [show bs ++ [y, d] = (bs ++ [y]) ++ [d] from by simp]
          rw [chop_snoc]
          cases bs with
          | nil => simp
          | cons b bs' => simp
        have hcan : CanRaise st d := ⟨hb, aY, hdtop, Or.inl hchop⟩
        have hliv : CanRaiseS st d := CanRaiseS.now d hcan
        rcases (hx.1 d).mpr hliv with hdx | hdt
        · rw [hdx] at hdidx
          omega
        · rw [hdt] at hdidx
          rw [Card.twin_rank] at hdidx
          omega
  -- (8) the rung deficit
  have hdmem' : d ∈ (st.piles aY).faceUp := by
    rw [hface']
    exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons_self ..))))
  have hpile : rungAt st d.suit ≤ d.rank.toIdx := piled_rung hwf hdmem'
  have hne : d.rank.toIdx ≠ rungAt st d.suit := by
    intro hcon
    have hup : st.nextUp d = true := by
      unfold State.nextUp
      exact decide_eq_true hcon
    rw [hup] at hnextD
    exact absurd hnextD (by simp)
  have hdcolx : d.suit.color ≠ x.suit.color := by
    intro hc
    apply hdcol
    rw [hc, hxy, Card.twin_suit]
    exact (Suit.color_twin x.suit).symm
  exact ⟨aY, bs, hface', hdtop, hnextD, hdcolx, by omega, by omega⟩

private theorem below_succ_of_fromCard {l : List Card} {c e : Card} {rest : List Card}
    (hnd : l.Nodup) (h : fromCard c l = c :: e :: rest) :
    below e l = below c l ++ [c] := by
  have hsplit : below c l ++ c :: e :: rest = l := by
    have h0 := tfc_below_fromCard c l
    rw [h] at h0
    exact h0
  have hnd' : (below c l ++ c :: e :: rest).Nodup := by
    rw [hsplit]; exact hnd
  have hnot : e ∉ below c l := by
    intro hmem
    exact (((List.nodup_append.1 hnd').2.2 e hmem) e
      (List.mem_cons_of_mem c (List.mem_cons_self ..))) rfl
  have htail : (c :: e :: rest).Nodup := (List.nodup_append.1 hnd').2.1
  have hcnot : c ∉ e :: rest := (List.nodup_cons.1 htail).1
  have hcne : c ≠ e := fun hce =>
    hcnot (by rw [hce]; exact List.mem_cons_self ..)
  have hstep : below e (c :: e :: rest) = [c] := by
    show (if c = e then [] else c :: below e (e :: rest)) = [c]
    rw [ite_eq_right hcne]
    show c :: (if e = e then [] else e :: below e rest) = [c]
    rw [ite_eq_left rfl]
  calc below e l = below e (below c l ++ c :: e :: rest) := by rw [hsplit]
    _ = below c l ++ below e (c :: e :: rest) := below_append_notmem hnot _
    _ = below c l ++ [c] := by rw [hstep]

/- SHA-SCAN STRIKE (2026-10-31, wave 7): the transitive two-colour row is
struck - the Kit home `color_eq_of_ne` (`Orig2/Kit.lean`) gives it in
one line (`color_eq_of_ne hab (Ne.symm hbc)`); the cite re-pointed. -/

/-- **COVER TOP OF FORK.**  At a `WF` live twin pair `F`, `y = x.twin`,
if `d` sits directly on `y` (`seatOf F d = some (inr y)`), then `d`
tops a pile.

Proof: `d` is one rank above `y` and opposite colour.  Both twin suits
have founded prefix `y.rank.toIdx` (`canRaiseS_flat_necessity` plus
`nextUp`), so any card `e` directly on `d` is two ranks below `y`,
hence founded, and has `y`'s colour, hence `x`'s or `y`'s suit —
contradicting `mem_found_unique`.  So nothing covers `d`, i.e. `d` is
the last face-up card of its pile. -/
theorem cover_top_of_fork {F : State} {x y d : Card} (hwf : F.WF)
    (hxy : y = x.twin) (hlive : TwinLivePair F x)
    (hd : seatOf F d = some (Sum.inr y)) :
    ∃ a, F.pileOfTop d = some a := by
  -- the cover's seat data
  obtain ⟨ad, hhold, hbne, hlast⟩ := tfc_seatOf_of_inr hd
  -- the parent fit, and y is not a pile top
  obtain ⟨hsit, -⟩ := tfc_seat_parent hwf hhold hlast
  obtain ⟨hrankD, hcolD⟩ := (canSitOn_eq d y).mp hsit
  have hrankxy : x.rank = y.rank := by rw [hxy]; rfl
  -- both twins are S-live and next-up, so both twin rungs sit at y's index
  have hxS : CanRaiseS F x := (hlive x).mpr (Or.inl rfl)
  have hyS : CanRaiseS F y := (hlive y).mpr (Or.inr hxy)
  have hnextX : F.nextUp x = true := (canRaiseS_flat_necessity hwf hxS).1
  have hnextY : F.nextUp y = true := (canRaiseS_flat_necessity hwf hyS).1
  have hfx : (F.found x.suit).length = y.rank.toIdx := by
    have h : x.rank.toIdx = (F.found x.suit).length := by
      simpa [State.nextUp, State.foundHeight] using of_decide_eq_true hnextX
    rw [← h, hrankxy]
  have hfy : (F.found y.suit).length = y.rank.toIdx := by
    have h : y.rank.toIdx = (F.found y.suit).length := by
      simpa [State.nextUp, State.foundHeight] using of_decide_eq_true hnextY
    exact h.symm
  -- no card is seated on d
  have noCover : ∀ e, seatOf F e ≠ some (Sum.inr d) := by
    intro e hes
    exfalso
    obtain ⟨ae, hholde, -, hlaste⟩ := tfc_seatOf_of_inr hes
    obtain ⟨hsitE, -⟩ := tfc_seat_parent hwf hholde hlaste
    obtain ⟨hrankE, hcolE⟩ := (canSitOn_eq e d).mp hsitE
    -- ranks: e is two below y
    have hstep : e.rank.toIdx + 2 = y.rank.toIdx := by
      rw [← hrankD, ← hrankE]
    have hlt : e.rank.toIdx < y.rank.toIdx := by
      rw [← hstep]
      exact Nat.lt_add_of_pos_right (by decide : 0 < 2)
    -- colours: e has y's colour
    have hcolY : e.suit.color = y.suit.color :=
      color_eq_of_ne hcolE (Ne.symm hcolD)
    have hsu : e.suit = y.suit ∨ e.suit = y.suit.twin :=
      tfc_suit_same_color_or_twin hcolY
    have hytwin : y.suit.twin = x.suit := by
      rw [hxy]; exact Suit.twin_twin x.suit
    have hsu' : e.suit = x.suit ∨ e.suit = y.suit := by
      rcases hsu with hs | hs
      · exact Or.inr hs
      · exact Or.inl (by rw [hs, hytwin])
    -- e is founded
    have hfoundE : e ∈ F.found e.suit := by
      apply FoundKit.mem_found_of_rung hwf
      rcases hsu' with hs | hs
      · rw [hs]; show e.rank.toIdx < (F.found x.suit).length; omega
      · rw [hs]; show e.rank.toIdx < (F.found y.suit).length; omega
    -- but it is also face-up in ae
    have hemem : e ∈ (F.piles ae).faceUp := pileHolding_mem hholde
    exact ((mem_found_unique hwf hfoundE).1 ae).2 hemem
  -- d is face-up; classify by the part above it
  have hdmem : d ∈ (F.piles ad).faceUp := pileHolding_mem hhold
  obtain ⟨tr, hfc⟩ := tfc_fromCard_cons_head (c := d) (F.piles ad).faceUp hdmem
  cases tr with
  | nil =>
      -- nothing above d: d is the last face-up card
      have hsingle : fromCard d (F.piles ad).faceUp = [d] := by simpa using hfc
      have hlastD : lastOf (F.piles ad).faceUp = some d := by
        have h0 := tfc_below_fromCard d (F.piles ad).faceUp
        rw [hsingle] at h0
        rw [← h0]
        exact lastOf_snoc
      exact ⟨ad, (pileOfTop_eq_some_iff hwf).2 hlastD⟩
  | cons e rest =>
      -- e is directly above d: it is seated on d, contradiction
      have hface : (F.piles ad).faceUp
          = below d (F.piles ad).faceUp ++ d :: e :: rest := by
        have h0 := tfc_below_fromCard d (F.piles ad).faceUp
        rw [hfc] at h0
        exact h0.symm
      have hnd : (F.piles ad).faceUp.Nodup := runOK_nodup (hwf.2.1 ad)
      have hbel : below e (F.piles ad).faceUp
          = below d (F.piles ad).faceUp ++ [d] :=
        below_succ_of_fromCard hnd hfc
      have hlastE : lastOf (below e (F.piles ad).faceUp) = some d := by
        rw [hbel]; exact lastOf_snoc
      have heMem : e ∈ (F.piles ad).faceUp := by
        rw [hface]
        exact List.mem_append.mpr
          (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons_self ..))))
      have hholdE : F.pileHolding e = some ad :=
        (pileHolding_eq_some_iff hwf).2 heMem
      exact absurd (tfc_seatOf_inr_intro hholdE hlastE) (noCover e)

/-- **THE COVER IS NOT NEXT-UP.**  At a live twin pair, a card seated on
the covered twin is not `nextUp` — else (it tops a pile by
`cover_top_of_fork`, and has a nonempty chop because it sits on `y`) it
would be vanilla raisable, hence S-live, contradicting `TwinLivePair`. -/
theorem not_nextUp_cover_of_fork {F : State} {x y d : Card} (hwf : F.WF)
    (hxy : y = x.twin) (hlive : TwinLivePair F x)
    (hd : seatOf F d = some (Sum.inr y)) :
    F.nextUp d = false := by
  obtain ⟨a, hpa⟩ := cover_top_of_fork hwf hxy hlive hd
  obtain ⟨ad, hhold, hbne, hlast⟩ := tfc_seatOf_of_inr hd
  obtain ⟨hrankD, -⟩ := (canSitOn_eq d y).mp
    (tfc_seat_parent hwf hhold hlast).1
  have hrankxy : x.rank = y.rank := by rw [hxy]; rfl
  -- the holding pile and the top pile agree
  have haa : a = ad := by
    by_cases hne : a = ad
    · exact hne
    · exfalso
      have hdmemA : d ∈ (F.piles a).faceUp :=
        lastOf_mem (pileOfTop_top hpa).2
      exact (mem_faceUp_unique hwf hdmemA ad (fun h => hne h.symm)).1
        (pileHolding_mem hhold)
  -- the chop under d is nonempty: y sits below d
  have hlastD : lastOf (F.piles a).faceUp = some d := (pileOfTop_top hpa).2
  have hchop : chop (F.piles a).faceUp ≠ [] := by
    intro hc
    have hsplit : (F.piles a).faceUp = chop (F.piles a).faceUp ++ [d] :=
      lastOf_chop hlastD
    rw [hc] at hsplit
    have hbel : below d (F.piles ad).faceUp = [] := by
      rw [← haa, hsplit, List.nil_append]
      rw [below_cons, ite_eq_left rfl]
    exact hbne hbel
  -- otherwise d would be S-live
  have hnotTrue : F.nextUp d ≠ true := by
    intro hnext
    have hcan : CanRaise F d := ⟨hnext, a, hpa, Or.inl hchop⟩
    have hcanS : CanRaiseS F d := CanRaiseS.now d hcan
    have hdx : d ≠ x := by
      intro h
      rw [h, hrankxy] at hrankD
      exact (Nat.succ_ne_self y.rank.toIdx) hrankD
    have hdy : d ≠ y := by
      intro h
      rw [h] at hrankD
      exact (Nat.succ_ne_self y.rank.toIdx) hrankD
    rcases (hlive d).mp hcanS with h | h
    · exact hdx h
    · exact hdy (h.trans hxy.symm)
  cases h : F.nextUp d with
  | false => rfl
  | true => exact absurd h hnotTrue

/-- **THE COVER'S ONLY BASES ARE THE TWINS.**  A card seated on `y`
can only be placed on `y` or on `y.twin = x`: the fitting parents of
`d` are `y` and its twin (`tfc_fitting_parent`).  In particular, once
`x` is founded the cover has nowhere to go. -/
theorem cover_base_is_twin {F : State} {x y d : Card} (hwf : F.WF)
    (hxy : y = x.twin) (hd : seatOf F d = some (Sum.inr y))
    {z : Card} (hz : canSitOn d z = true) :
    z = x ∨ z = y := by
  obtain ⟨ad, hhold, -, hlast⟩ := tfc_seatOf_of_inr hd
  have hfit : canSitOn d y = true := (tfc_seat_parent hwf hhold hlast).1
  have hpair := tfc_fitting_parent hz hfit
  rcases hpair with h | h
  · exact Or.inr h
  · refine Or.inl ?_
    rw [h, hxy]
    simp [Card.twin]

/-- **THE COVER IS NOT A KING** — its rank is one below the covered
twin's, so it cannot use an empty-anchor base. -/
theorem cover_rank_ne_king {F : State} {y d : Card} (hwf : F.WF)
    (hd : seatOf F d = some (Sum.inr y)) :
    d.rank ≠ Rank.king := by
  obtain ⟨ad, hhold, -, hlast⟩ := tfc_seatOf_of_inr hd
  obtain ⟨hrankD, -⟩ := (canSitOn_eq d y).mp
    (tfc_seat_parent hwf hhold hlast).1
  intro hk
  have h12 : d.rank.toIdx = 12 := by rw [hk]; rfl
  rw [h12] at hrankD
  have hy13 : y.rank.toIdx = 13 := hrankD.symm
  exact (Nat.lt_irrefl 13) (hy13 ▸ Rank.toIdx_lt y.rank)
/-! ## The battery -/

#print axioms piled_rung
#print axioms cover_pins_of_fork
#print axioms cover_top_of_fork
#print axioms not_nextUp_cover_of_fork
#print axioms cover_base_is_twin
#print axioms cover_rank_ne_king