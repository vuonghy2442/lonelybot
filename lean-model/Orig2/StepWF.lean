import Orig2.CargoKit

/-!
# Orig2.StepWF — THE WF CONSERVATION FENCE

THE CARD'S MISSION: a legal play never leaves the well-formed
world — every legal single step from a `WF` state lands in a
`WF` state (`step_wf`), and the play lift carries the fence along
a whole run (`run_wf`).  The frozen tier's phrasing: `WF` is the
program's working invariant, and this is the chapter that keeps
it closed under the rules.

LINEAGE: `Orig/Reach.lean` — the frozen chapter, read freely,
never imported (it rides `Orig.Combine`/`Orig.Integrity`/
`Orig.Irreversible`, all above the closed core seam; the
per-case fence lives at `Orig/Reach.lean:739-2103` with the
public capstone at `:2104`).  Every row below is a re-statement
at the seam definitions — verbatim shape copies with the frozen
line cited per row, riding the rebuild's public kit by NAME:

* the occurrence-count kit, the search rows, the run kit and the
  `tabToTab` case are `Orig2/CargoKit.lean`'s own `Reach` ports,
  cited `tfc_*`, never re-landed — including the hardest case
  itself: the `tabToTab` fence row is CARGOKIT's
  `tfc_tabToTab_wf` (`Orig2/CargoKit.lean:673`, its §D port of
  `Orig/Reach.lean:1676`), consumed here by name;
* the step inversions, the placement guards, the `firstWhere`
  soundness and the play-lift engine `run_rec` are
  `Orig2/Kit.lean` §1a/§1c/§1e — cited by name;
* `runOK_chop`, `setPile_piles_self`/`_ne`,
  `setFound_found_self`/`_ne`, `wasteIs_head_eq`,
  `putCard_eq_inl`, `putCard_inr_eq`, `draw_unfold`,
  `State.run_cons` are core-seam rows (`Orig/State.lean`,
  `Orig/Play.lean`) — the seam already carries them;
* the thin remainder — the take/snoc foundation-prefix kit, the
  draw-pool count, `cnt_reverse`/`cnt_singleton`, the `nextUp`
  pin — is re-landed as this card's private kit, each row with
  its frozen line cited.

SCOPE NOTE (deferred, not lost): the frozen chapter's deal half —
`initial_wf` and the reachable⇒WF capstones
`initialReachable_wf` (`Orig/Reach.lean:626/:2118`) — rides the
FROZEN `initialReachable` definition (`Orig/Reach.lean:39`), a
program-wide notion the vocabulary registry has not yet opened
(no owner intent line = no landing per the root charter); those
rows port to a future reachability card when the registry does.

Constructivity: the fence is decidability-free list arithmetic
over the count kit — expected audit `[propext]` or
`[propext, Quot.sound]`, never `Classical.choice` (inherited from
the kit rows the cases ride).  `run_wf` is this card's own row
(the frozen tier re-derived it per-file at `Orig/Dominance.lean:9177`
and the ForkFloor/ForkCensus lifts; here it is one instance of
Kit's `run_rec` engine).

House compliance: per-row provenance docstrings; private kit for
the thin remainder; frozen statements never force-premised; the
battery at the tail; commits staged green, `lake build Orig2`
between batches.
-/

/-! ## §0. The private kit  (thin re-lands, every row cited) -/

/-- The four suits enumerate without repetition.  PORTED verbatim
from `Orig/Reach.lean:806`. -/
private theorem Suit_all_nodup : (Suit.all : List Suit).Nodup := by decide

/-- The count of a singleton list is its indicator.  PORTED
verbatim from `Orig/Reach.lean:141`, restated at the kit's
`tfc_cnt`. -/
private theorem cnt_singleton (c x : Card) : tfc_cnt c [x] = if x = c then 1 else 0 := by
  show ((if x = c then 1 else 0) + tfc_cnt c []) = if x = c then 1 else 0
  rw [tfc_cnt_nil]
  omega

/-- Counting is insensitive to reversal.  PORTED verbatim from
`Orig/Reach.lean:159`, restated at the kit's `tfc_cnt`. -/
private theorem cnt_reverse (c : Card) (l : List Card) :
    tfc_cnt c l.reverse = tfc_cnt c l := by
  induction l with
  | nil => rfl
  | cons x t ih =>
      rw [List.reverse_cons, tfc_cnt_snoc, cnt_singleton, ih, tfc_cnt_def]
      omega

/-- Recycling moves no card between the counted zones.  PORTED
verbatim from `Orig/Reach.lean:573`, restated at the kit's
`tfc_cnt`. -/
private theorem recycle_pool_cnt (st : State) (c₀ : Card) :
    tfc_cnt c₀ (State.recycle st).stock + tfc_cnt c₀ (State.recycle st).waste
      = tfc_cnt c₀ st.stock + tfc_cnt c₀ st.waste := by
  by_cases hsne : st.stock = []
  · by_cases hwne : st.waste = []
    · rw [recycle_allEmpty st hsne hwne]
    · rw [recycle_nil st hsne hwne,
        show tfc_cnt c₀
            ({ st with stock := st.waste.reverse, waste := ([] : List Card) } : State).stock
          = tfc_cnt c₀ st.waste.reverse from rfl,
        show tfc_cnt c₀
            ({ st with stock := st.waste.reverse, waste := ([] : List Card) } : State).waste
          = tfc_cnt c₀ ([] : List Card) from rfl,
        cnt_reverse, hsne, tfc_cnt_nil]
      omega
  · rw [recycle_keep st hsne]

/-- The searches only read the piles, so a foundation update leaves
them unchanged.  PORTED verbatim from `Orig/Reach.lean:555`. -/
private theorem pileOfTop_setFound {st : State} {s : Suit} {l : List Card} {z : Card} :
    (st.setFound s l).pileOfTop z = st.pileOfTop z := rfl

/-- The `nextUp` guard pins the foundation length at the mover's
rank index.  PORTED verbatim from `Orig/Reach.lean:558`. -/
private theorem nextUp_true {st : State} {c : Card} (h : st.nextUp c = true) :
    c.rank.toIdx = (st.found c.suit).length := by
  have h' : c.rank.toIdx = st.foundHeight c.suit := of_decide_eq_true h
  exact h'

/-- The foundation top reads as the lastOf of its list.  PORTED
verbatim from `Orig/Reach.lean:563`. -/
private theorem foundTop_lastOf {st : State} {c : Card}
    (h : st.foundTop c.suit = some c) : lastOf (st.found c.suit) = some c := h

/-- `chop` is the take-the-front part of a list.  PORTED verbatim
from `Orig/Reach.lean:420`. -/
private theorem chop_eq_take : ∀ (l : List Card), chop l = l.take (l.length - 1)
  | [] => rfl
  | [x] => rfl
  | x :: y :: t => by
      have ih := chop_eq_take (y :: t)
      have hA : (y :: t).length = t.length + 1 := List.length_cons
      have hlen : (x :: y :: t).length - 1 = (y :: t).length - 1 + 1 := by
        rw [List.length_cons]
        omega
      rw [hlen]
      show x :: chop (y :: t) = x :: (y :: t).take ((y :: t).length - 1)
      rw [ih]

/-- Dealt pile cards reconstruct: `chop` is the take-the-front part
of a dealt hand.  PORTED verbatim from `Orig/Reach.lean:435`. -/
private theorem chop_take_succ (L : List Card) (m : Nat) (h : m + 1 ≤ L.length) :
    chop (L.take (m + 1)) = L.take m := by
  rw [chop_eq_take, List.length_take, Nat.min_eq_left h, List.take_take,
    Nat.min_eq_left (by omega : m + 1 - 1 ≤ m + 1)]
  rfl

/-- A taken prefix records its new last element.  PORTED verbatim
from `Orig/Reach.lean:441`. -/
private theorem take_succ_snoc_some : ∀ (l : List Card) (m : Nat) (x : Card),
    l[m]? = some x → l.take (m + 1) = l.take m ++ [x]
  | [], 0, x, h => by simp at h
  | [], m + 1, x, h => by simp at h
  | y :: t, 0, x, h => by
      have hxy : x = y := (Option.some.inj h).symm
      subst hxy
      rfl
  | y :: t, m + 1, x, h => by
      rw [List.getElem?_cons_succ] at h
      have ih := take_succ_snoc_some t m x h
      show y :: t.take (m + 1) = (y :: t.take m) ++ [x]
      rw [List.cons_append, ih]

/-- The thirteen-way position pin: each rank sits at its own index
of `Rank.all`.  PORTED verbatim from `Orig/Reach.lean:457`. -/
private theorem rank_all_pin (r : Rank) :
    (Rank.all : List Rank)[r.toIdx]? = some r := by
  cases r <;> rfl

/-- The build-order take-step: extending a foundation built to
`c`'s rank index takes exactly one more card — `c` itself.
PORTED verbatim from `Orig/Reach.lean:463`. -/
private theorem upCards_take_succ {c : Card} :
    c.suit.upCards.take (c.rank.toIdx + 1) = c.suit.upCards.take c.rank.toIdx ++ [c] := by
  have h1 : (Rank.all : List Rank)[c.rank.toIdx]? = some c.rank := rank_all_pin c.rank
  have h2 : (c.suit.upCards)[c.rank.toIdx]? = some c := by
    rw [show c.suit.upCards = Rank.all.map (Card.mk c.suit) from rfl, List.getElem?_map, h1]
    rfl
  exact take_succ_snoc_some _ _ _ h2

/-- `nextUp` pins the foundation prefix exactly at the next card's
index.  PORTED verbatim from `Orig/Reach.lean:670`. -/
private theorem found_prefix_eq {st : State} {c : Card}
    (hpre : ∀ σ, ∃ n, st.found σ = σ.upCards.take n)
    (hnext : st.nextUp c = true) :
    ∃ n, st.found c.suit = c.suit.upCards.take n ∧ n = c.rank.toIdx := by
  obtain ⟨n, hn⟩ := hpre c.suit
  have hlen : c.rank.toIdx = (st.found c.suit).length := nextUp_true hnext
  have htakelen : (c.suit.upCards.take n).length = min n 13 := by
    rw [List.length_take, Suit.upCards_length]
  have hfl : (st.found c.suit).length = (c.suit.upCards.take n).length := by
    rw [hn]
  rcases Nat.lt_or_ge n 13 with hlt | hge
  · have hmin : min n 13 = n := Nat.min_eq_left (Nat.le_of_lt hlt)
    refine ⟨n, hn, ?_⟩
    omega
  · exfalso
    have hmin : min n 13 = 13 := Nat.min_eq_right hge
    have hc : c.rank.toIdx < 13 := Rank.toIdx_lt c.rank
    omega

/-- The appendix clause when a foundation gains its next card.
PORTED verbatim from `Orig/Reach.lean:690`. -/
private theorem found_gain_clause {st st' : State} {c : Card}
    (hpre : ∀ σ, ∃ n, st.found σ = σ.upCards.take n)
    (hnext : st.nextUp c = true)
    (hself : st'.found c.suit = st.found c.suit ++ [c])
    (hne : ∀ σ ≠ c.suit, st'.found σ = st.found σ) :
    ∀ σ, ∃ n, st'.found σ = σ.upCards.take n := by
  intro σ
  rcases Decidable.em (σ = c.suit) with heq | hneσ
  · subst heq
    obtain ⟨n, hn, hnidx⟩ := found_prefix_eq hpre hnext
    refine ⟨n + 1, ?_⟩
    rw [hself, hn, hnidx, upCards_take_succ]
  · obtain ⟨n, hn⟩ := hpre σ
    exact ⟨n, by rw [hne σ hneσ, hn]⟩

/-- The prefix clause when a foundation loses its top card by the
`chop` of `foundTop`.  PORTED from `Orig/Reach.lean:707` (the
frozen `take_ge` is Kit's `take_ge_length` here; the tall-table
branch's take-shuffle re-sequenced deterministically at the
explicit row — same arithmetic, no unification-order games). -/
private theorem found_chop_prefix {st : State} {c : Card}
    (hpre : ∀ σ, ∃ n, st.found σ = σ.upCards.take n)
    (hlast : lastOf (st.found c.suit) = some c) :
    ∃ m, chop (st.found c.suit) = c.suit.upCards.take m := by
  obtain ⟨n, hn⟩ := hpre c.suit
  have hlmem : 1 ≤ (st.found c.suit).length :=
    List.length_pos_of_mem (lastOf_mem hlast)
  have hfl : (st.found c.suit).length = (c.suit.upCards.take n).length := by
    rw [hn]
  have htakelen : (c.suit.upCards.take n).length = min n 13 := by
    rw [List.length_take, Suit.upCards_length]
  rcases Nat.lt_or_ge n 13 with hlt | hge
  · have hmin : min n 13 = n := Nat.min_eq_left (Nat.le_of_lt hlt)
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
    refine ⟨m, ?_⟩
    rw [hn, hm]
    have hguard : m + 1 ≤ c.suit.upCards.length := by
      rw [Suit.upCards_length]; omega
    exact chop_take_succ c.suit.upCards m hguard
  · refine ⟨12, ?_⟩
    have htake13 : c.suit.upCards.take 13 = c.suit.upCards :=
      take_ge_length c.suit.upCards 13 (by rw [Suit.upCards_length]; omega)
    have htaken : c.suit.upCards.take n = c.suit.upCards.take 13 := by
      rw [take_ge_length c.suit.upCards n (by rw [Suit.upCards_length]; omega), htake13]
    rw [hn, htaken]
    exact chop_take_succ c.suit.upCards 12 (by rw [Suit.upCards_length]; omega)

/-! ## §1. The fence, move by move

Five of the six constructor cases, PORTED reading (verbatim bodies,
renamed to the kit's `tfc_*` rows); the sixth — `tabToTab` — is
CargoKit's public `tfc_tabToTab_wf` and is consumed by name in the
capstone below. -/

/-- The draw: only the stock and waste reshape (a recycle reverses
the waste into the stock; the deal takes and reverses), so all four
clauses survive.  PORTED verbatim from `Orig/Reach.lean:739`, at
the kit's `tfc_cnt`. -/
private theorem draw_wf {st st' : State} (hwf : st.WF) (hstep : st.stepDraw = some st') :
    st'.WF := by
  obtain ⟨hpre, hpile, hcard, hstep1or3⟩ := hwf
  obtain ⟨r, hrec, hrne, hrw⟩ := draw_unfold hstep
  rw [← hrec] at hrw
  have hkeepsR : (State.recycle st).found = st.found ∧
      (State.recycle st).piles = st.piles ∧
      (State.recycle st).drawStep = st.drawStep := by
    by_cases hs : st.stock = []
    · by_cases hw : st.waste = []
      · rw [recycle_allEmpty st hs hw]
        exact ⟨rfl, rfl, rfl⟩
      · rw [recycle_nil st hs hw]
        exact ⟨rfl, rfl, rfl⟩
    · rw [recycle_keep st hs]
      exact ⟨rfl, rfl, rfl⟩
  obtain ⟨hk1, hk2, hk3⟩ := hkeepsR
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro σ
    have h1 : st'.found σ = st.found σ := by
      rw [hrw]
      show (State.recycle st).found σ = st.found σ
      rw [hk1]
    rw [h1]
    exact hpre σ
  · intro a
    have h1 : st'.piles a = st.piles a := by
      rw [hrw]
      show (State.recycle st).piles a = st.piles a
      rw [hk2]
    rw [h1]
    exact hpile a
  · intro c₀ hc₀
    have hcc := hcard c₀ hc₀
    rw [tfc_cardCount_zones] at hcc
    rw [tfc_cardCount_zones]
    have hst : st'.stock = r.stock.drop r.drawStep := by
      rw [hrw, hrec, dealUpTo_eq_take_drop]
    have hwst : st'.waste = (r.stock.take r.drawStep).reverse ++ r.waste := by
      rw [hrw, hrec, dealUpTo_eq_take_drop]
    have hs : tfc_cnt c₀ st'.stock + tfc_cnt c₀ st'.waste
        = tfc_cnt c₀ st.stock + tfc_cnt c₀ st.waste := by
      rw [hst, hwst, tfc_cnt_app c₀, cnt_reverse]
      have hdealsplit : tfc_cnt c₀ (r.stock.take r.drawStep) + tfc_cnt c₀ (r.stock.drop r.drawStep)
          = tfc_cnt c₀ r.stock := by
        rw [← tfc_cnt_app c₀, List.take_append_drop]
      have hpool := recycle_pool_cnt st c₀
      rw [hrec] at hpool
      omega
    have hf : tfc_cntFlat c₀ (Suit.all.map st'.found) = tfc_cntFlat c₀ (Suit.all.map st.found) := by
      rw [show st'.found = (State.recycle st).found from by rw [hrw], hk1]
    have hp : tfc_cntFlat c₀ (Anchor.all.map fun a => (st'.piles a).hidden ++ (st'.piles a).faceUp)
        = tfc_cntFlat c₀ (Anchor.all.map fun a => (st.piles a).hidden ++ (st.piles a).faceUp) := by
      have hp0 : st'.piles = (State.recycle st).piles := by rw [hrw]
      rw [show (fun a => (st'.piles a).hidden ++ (st'.piles a).faceUp) =
          (fun a => ((State.recycle st).piles a).hidden ++ ((State.recycle st).piles a).faceUp)
          from by rw [show (fun a : Anchor => (st'.piles a).hidden ++ (st'.piles a).faceUp) =
            (fun a : Anchor => (st'.piles a).hidden ++ (st'.piles a).faceUp) from rfl,
          hp0],
        hk2]
    omega
  · have hsd : st'.drawStep = st.drawStep := by
      rw [hrw]
      show (State.recycle st).drawStep = st.drawStep
      rw [hk3]
    rw [hsd]; exact hstep1or3

/-- The `wasteToFound` move: the waste top joins its foundation.
PORTED verbatim from `Orig/Reach.lean:814`, at the kit's rows. -/
private theorem wasteToFound_wf {st st' : State} {c : Card}
    (hwf : st.WF) (h : State.step st (.wasteToFound c) = some st') : st'.WF := by
  obtain ⟨hpre, hpile, hcard, hsd⟩ := hwf
  obtain ⟨hguard, x, ws, hws0, hrw⟩ := step_wasteToFound_inv h
  rw [Bool.and_eq_true] at hguard
  obtain ⟨hwasteis, hnextup⟩ := hguard
  have hxc : x = c := State.wasteIs_head_eq hws0 hwasteis
  have hweq : st.waste = c :: ws := by rw [hws0, hxc]
  have hf : st'.found c.suit = st.found c.suit ++ [c] := by
    rw [hrw]
    show (st.setFound c.suit (st.found c.suit ++ [c])).found c.suit = _
    rw [setFound_found_self]
  have hfne : ∀ σ ≠ c.suit, st'.found σ = st.found σ := by
    intro σ hσ
    rw [hrw]
    show (st.setFound c.suit (st.found c.suit ++ [c])).found σ = _
    rw [setFound_found_ne hσ]
  have hpp : st'.piles = st.piles := by rw [hrw]; rfl
  have hwr : st'.waste = ws := by rw [hrw]
  have hstock : st'.stock = st.stock := by rw [hrw]; rfl
  have hsd' : 0 < st'.drawStep := by
    have hdeq : st'.drawStep = st.drawStep := by
      rw [hrw]
      show (st.setFound c.suit (st.found c.suit ++ [c])).drawStep = st.drawStep
      rfl
    rw [hdeq]; exact hsd
  refine ⟨?_, ?_, ?_, hsd'⟩
  · exact found_gain_clause hpre hnextup hf hfne
  · intro a
    rw [show st'.piles a = st.piles a from by rw [hpp]]
    exact hpile a
  · intro c₀ hc₀
    have hcc := hcard c₀ hc₀
    rw [tfc_cardCount_zones] at hcc
    rw [tfc_cardCount_zones]
    have hp : tfc_cntFlat c₀ (Anchor.all.map fun a => (st'.piles a).hidden ++ (st'.piles a).faceUp)
        = tfc_cntFlat c₀ (Anchor.all.map fun a => (st.piles a).hidden ++ (st.piles a).faceUp) := by
      rw [hpp]
    have hfdelta : tfc_cntFlat c₀ (Suit.all.map st'.found)
        = tfc_cntFlat c₀ (Suit.all.map st.found) + tfc_cnt c₀ [c] := by
      have h1 := tfc_cntFlat_map_delta c₀ st.found st'.found Suit.all
        (fun σ => if σ = c.suit then tfc_cnt c₀ [c] else 0)
        (by intro σ _
            by_cases hσc : σ = c.suit
            · rw [hσc, hf, tfc_cnt_snoc, ite_eq_left rfl]
            · rw [hfne σ hσc, ite_eq_right hσc]
              omega)
      have h2 : (Suit.all.map (fun σ => if σ = c.suit then tfc_cnt c₀ [c] else 0)).sum
          = tfc_cnt c₀ [c] := by
        have h3 := tfc_sum_map_single Suit.all (fun σ => if σ = c.suit then tfc_cnt c₀ [c] else 0)
          c.suit Suit_all_nodup (Suit.mem_all c.suit)
          (by intro j _ hjc; rw [ite_eq_right hjc])
        have h4 : (if c.suit = c.suit then tfc_cnt c₀ [c] else 0) = tfc_cnt c₀ [c] :=
          by rw [ite_eq_left rfl]
        rw [h3, h4]
      rw [← h1, h2]
    have hwaste : tfc_cnt c₀ st'.waste + tfc_cnt c₀ [c] = tfc_cnt c₀ st.waste := by
      rw [hwr, hweq, tfc_cnt_def c₀ c ws, cnt_singleton c₀ c]
      omega
    have hstockc : tfc_cnt c₀ st'.stock = tfc_cnt c₀ st.stock := by rw [hstock]
    omega

/-- The `wasteToTab` move: the waste top joins the tableau, either a
king opening an empty position or a card fitted under a pile top.
PORTED verbatim from `Orig/Reach.lean:884` (the frozen private
`pile_isEmpty` twin is Kit's public `Pile.isEmpty_eq` here, the
frozen private `runOK_append_fit` is CargoKit's
`tfc_runOK_append_fit`), at the kit's rows. -/
private theorem wasteToTab_wf {st st' : State} {c : Card} {b : Base}
    (hwf : st.WF) (h : State.step st (.wasteToTab c b) = some st') : st'.WF := by
  obtain ⟨hpre, hpile, hcard, hsd⟩ := hwf
  obtain ⟨hguard, x, ws, hws0, hrw⟩ := step_wasteToTab_inv h
  rw [Bool.and_eq_true] at hguard
  obtain ⟨hwasteis, hcanplace⟩ := hguard
  have hxc : x = c := State.wasteIs_head_eq hws0 hwasteis
  have hweq : st.waste = c :: ws := by rw [hws0, hxc]
  have hwr : st'.waste = ws := by rw [hrw]
  have hwaste : ∀ c₀, tfc_cnt c₀ st'.waste + tfc_cnt c₀ [c] = tfc_cnt c₀ st.waste := by
    intro c₀
    rw [hwr, hweq, tfc_cnt_def c₀ c ws, cnt_singleton c₀ c]
    omega
  cases b with
  | inl a₁ =>
      obtain ⟨hempty, _⟩ := canPlace_inl hcanplace
      obtain ⟨hid, hfu⟩ := (Pile.isEmpty_eq _).mp hempty
      have hstock : st'.stock = st.stock := by rw [hrw, putCard_eq_inl]; rfl
      have hfeq : st'.found = st.found := by rw [hrw, putCard_eq_inl]; rfl
      have hsd' : 0 < st'.drawStep := by
        have hdeq : st'.drawStep = st.drawStep := by
          rw [hrw, putCard_eq_inl]; rfl
        rw [hdeq]; exact hsd
      have hstockc : ∀ c₀, tfc_cnt c₀ st'.stock = tfc_cnt c₀ st.stock := fun c₀ => by rw [hstock]
      have hfcnt : ∀ c₀, tfc_cntFlat c₀ (Suit.all.map st'.found)
          = tfc_cntFlat c₀ (Suit.all.map st.found) := fun c₀ => by rw [hfeq]
      have hrp : st'.piles = (st.setPile a₁ ⟨[], [c]⟩).piles := by rw [hrw, putCard_eq_inl]
      refine ⟨?_, ?_, ?_, hsd'⟩
      · intro σ
        have h1 : st'.found σ = st.found σ := by rw [hfeq]
        rw [h1]
        exact hpre σ
      · intro a
        rcases Decidable.em (a = a₁) with ha | ha
        · rw [ha, show st'.piles a₁ = (st.setPile a₁ ⟨[], [c]⟩).piles a₁ from by rw [hrp],
            setPile_piles_self]
          show runOK ([c] : List Card) = true
          rfl
        · rw [show st'.piles a = (st.setPile a₁ ⟨[], [c]⟩).piles a from by rw [hrp],
            setPile_piles_ne ha]
          exact hpile a
      · intro c₀ hc₀
        have hcc := hcard c₀ hc₀
        rw [tfc_cardCount_zones] at hcc
        rw [tfc_cardCount_zones]
        have hpcnt : tfc_cntFlat c₀
              (Anchor.all.map fun j => (st'.piles j).hidden ++ (st'.piles j).faceUp)
            = tfc_cntFlat c₀ (Anchor.all.map fun j => (st.piles j).hidden ++ (st.piles j).faceUp)
              + tfc_cnt c₀ [c] := by
          have h1 := tfc_cntFlat_map_delta c₀
            (fun j => (st.piles j).hidden ++ (st.piles j).faceUp)
            (fun j => ((st.setPile a₁ ⟨[], [c]⟩).piles j).hidden
              ++ ((st.setPile a₁ ⟨[], [c]⟩).piles j).faceUp)
            Anchor.all
            (fun j => if j = a₁ then tfc_cnt c₀ [c] else 0)
            (by intro j _
                by_cases hj : j = a₁
                · have hGO : tfc_cnt c₀
                         (((st.setPile a₁ ⟨[], [c]⟩).piles a₁).hidden
                          ++ ((st.setPile a₁ ⟨[], [c]⟩).piles a₁).faceUp)
                       = tfc_cnt c₀ ([c] : List Card) := by
                    rw [setPile_piles_self]
                    show tfc_cnt c₀ (([] : List Card) ++ ([c] : List Card)) = tfc_cnt c₀ [c]
                    rw [tfc_cnt_app c₀, tfc_cnt_nil]
                    omega
                  have hFO : tfc_cnt c₀ ((st.piles a₁).hidden ++ (st.piles a₁).faceUp)
                      = 0 := by rw [hid, hfu, tfc_cnt_app c₀, tfc_cnt_nil]
                  rw [hj, hGO, ite_eq_left rfl, hFO]
                  omega
                · rw [ite_eq_right hj]
                  have hident : tfc_cnt c₀ ((st.piles j).hidden ++ (st.piles j).faceUp)
                      = tfc_cnt c₀ (((st.setPile a₁ ⟨[], [c]⟩).piles j).hidden
                        ++ ((st.setPile a₁ ⟨[], [c]⟩).piles j).faceUp) := by
                    rw [setPile_piles_ne hj]
                  rw [hident]
                  omega)
          have h2 : (Anchor.all.map (fun j => if j = a₁ then tfc_cnt c₀ [c] else 0)).sum
              = tfc_cnt c₀ [c] := by
            have h3 := tfc_sum_map_single Anchor.all
              (fun j => if j = a₁ then tfc_cnt c₀ [c] else 0) a₁
              Anchor.all_nodup (Anchor.mem_all a₁)
              (by intro j _ hjc; rw [ite_eq_right hjc])
            have h4 : (if a₁ = a₁ then tfc_cnt c₀ [c] else 0) = tfc_cnt c₀ [c] := by
              rw [ite_eq_left rfl]
            rw [h3, h4]
          have hfold : tfc_cntFlat c₀
              (Anchor.all.map fun j => (st'.piles j).hidden ++ (st'.piles j).faceUp)
              = tfc_cntFlat c₀
                  (Anchor.all.map fun j => ((st.setPile a₁ ⟨[], [c]⟩).piles j).hidden
                    ++ ((st.setPile a₁ ⟨[], [c]⟩).piles j).faceUp) := by
            rw [hrp]
          rw [hfold, ← h1, h2]
        rw [hpcnt, hfcnt c₀, hstockc c₀]
        have hwaste0 := hwaste c₀
        omega
  | inr z =>
      obtain ⟨k, hps, hfit⟩ := canPlace_inr hcanplace
      have htopk : lastOf (st.piles k).faceUp = some z := (tfc_pileOfTop_top hps).2
      have hstock : st'.stock = st.stock := by rw [hrw, putCard_inr_eq hps]; rfl
      have hfeq : st'.found = st.found := by rw [hrw, putCard_inr_eq hps]; rfl
      have hsd' : 0 < st'.drawStep := by
        have hdeq : st'.drawStep = st.drawStep := by
          rw [hrw, putCard_inr_eq hps]; rfl
        rw [hdeq]; exact hsd
      have hstockc : ∀ c₀, tfc_cnt c₀ st'.stock = tfc_cnt c₀ st.stock := fun c₀ => by rw [hstock]
      have hfcnt : ∀ c₀, tfc_cntFlat c₀ (Suit.all.map st'.found)
          = tfc_cntFlat c₀ (Suit.all.map st.found) := fun c₀ => by rw [hfeq]
      have hrp : st'.piles
          = (st.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles := by
        rw [hrw, putCard_inr_eq hps]
      refine ⟨?_, ?_, ?_, hsd'⟩
      · intro σ
        have h1 : st'.found σ = st.found σ := by rw [hfeq]
        rw [h1]
        exact hpre σ
      · intro a
        rcases Decidable.em (a = k) with ha | ha
        · rw [ha, show st'.piles k = (st.setPile k
                { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles k from by rw [hrp],
            setPile_piles_self]
          show runOK ((st.piles k).faceUp ++ ([c] : List Card)) = true
          exact tfc_runOK_append_fit (st.piles k).faceUp c z ([] : List Card)
            (hpile k) rfl htopk hfit
        · rw [show st'.piles a = (st.setPile k
                { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles a from by rw [hrp],
            setPile_piles_ne ha]
          exact hpile a
      · intro c₀ hc₀
        have hcc := hcard c₀ hc₀
        rw [tfc_cardCount_zones] at hcc
        rw [tfc_cardCount_zones]
        have hpcnt : tfc_cntFlat c₀
              (Anchor.all.map fun j => (st'.piles j).hidden ++ (st'.piles j).faceUp)
            = tfc_cntFlat c₀ (Anchor.all.map fun j => (st.piles j).hidden ++ (st.piles j).faceUp)
              + tfc_cnt c₀ [c] := by
          have h1 := tfc_cntFlat_map_delta c₀
            (fun j => (st.piles j).hidden ++ (st.piles j).faceUp)
            (fun j => ((st.setPile k
                { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles j).hidden
              ++ ((st.setPile k
                { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles j).faceUp)
            Anchor.all
            (fun j => if j = k then tfc_cnt c₀ [c] else 0)
            (by intro j _
                by_cases hj : j = k
                · have hG : tfc_cnt c₀
                        (((st.setPile k
                            { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles k).hidden
                          ++ ((st.setPile k
                            { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles k).faceUp)
                      = tfc_cnt c₀ ((st.piles k).hidden ++ ((st.piles k).faceUp ++ [c])) := by
                    rw [setPile_piles_self]
                  rw [hj, hG, ite_eq_left rfl, ← List.append_assoc, tfc_cnt_snoc]
                · rw [ite_eq_right hj]
                  have hident : tfc_cnt c₀ ((st.piles j).hidden ++ (st.piles j).faceUp)
                      = tfc_cnt c₀ (((st.setPile k
                          { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles j).hidden
                        ++ ((st.setPile k
                          { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles j).faceUp) := by
                    rw [setPile_piles_ne hj]
                  rw [hident]
                  omega)
          have h2 : (Anchor.all.map (fun j => if j = k then tfc_cnt c₀ [c] else 0)).sum
              = tfc_cnt c₀ [c] := by
            have h3 := tfc_sum_map_single Anchor.all
              (fun j => if j = k then tfc_cnt c₀ [c] else 0) k
              Anchor.all_nodup (Anchor.mem_all k)
              (by intro j _ hjc; rw [ite_eq_right hjc])
            have h4 : (if k = k then tfc_cnt c₀ [c] else 0) = tfc_cnt c₀ [c] := by
              rw [ite_eq_left rfl]
            rw [h3, h4]
          have hfold : tfc_cntFlat c₀
              (Anchor.all.map fun j => (st'.piles j).hidden ++ (st'.piles j).faceUp)
              = tfc_cntFlat c₀
                  (Anchor.all.map fun j => ((st.setPile k
                      { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles j).hidden
                    ++ ((st.setPile k
                      { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles j).faceUp) := by
            rw [hrp]
          rw [hfold, ← h1, h2]
        rw [hpcnt, hfcnt c₀, hstockc c₀]
        have hwaste0 := hwaste c₀
        omega

/-- The `tabToFound` move: the pile top joins its foundation; the
pile face-up run loses its last card, possibly revealing one hidden
card.  PORTED verbatim from `Orig/Reach.lean:1169`, at the kit's
rows (the frozen private `runOK_afterRunRemoved_nil` /
`afterRunRemoved_zone_cnt` / `pileOfTop_top` are CargoKit's
`tfc_*` ports here). -/
private theorem tabToFound_wf {st st' : State} {c : Card}
    (hwf : st.WF) (h : State.step st (.tabToFound c) = some st') : st'.WF := by
  obtain ⟨hpre, hpile, hcard, hsd⟩ := hwf
  obtain ⟨hnextup, a, hpstop, hrw⟩ := step_tabToFound_inv h
  have hf : st'.found c.suit = st.found c.suit ++ [c] := by
    rw [hrw]
    show (st.setFound c.suit (st.found c.suit ++ [c])).found c.suit = _
    rw [setFound_found_self]
  have hfne : ∀ σ ≠ c.suit, st'.found σ = st.found σ := by
    intro σ hσ
    rw [hrw]
    show (st.setFound c.suit (st.found c.suit ++ [c])).found σ = _
    rw [setFound_found_ne hσ]
  have hpj : ∀ j, st'.piles j =
      if j = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
      else st.piles j := by
    intro j
    rw [hrw]
  have hstockeq : st'.stock = st.stock := by
    rw [hrw]
    show (st.setFound c.suit (st.found c.suit ++ [c])).stock = st.stock
    rfl
  have hwasteq : st'.waste = st.waste := by
    rw [hrw]
    show (st.setFound c.suit (st.found c.suit ++ [c])).waste = st.waste
    rfl
  have hsd' : 0 < st'.drawStep := by
    have hdeq : st'.drawStep = st.drawStep := by
      rw [hrw]
      show (st.setFound c.suit (st.found c.suit ++ [c])).drawStep = st.drawStep
      rfl
    rw [hdeq]; exact hsd
  refine ⟨?_, ?_, ?_, hsd'⟩
  · exact found_gain_clause hpre hnextup hf hfne
  · intro j
    rcases Decidable.em (j = a) with hj | hj
    · rw [hj, hpj a, ite_eq_left rfl]
      cases hchop : chop (st.piles a).faceUp with
      | nil => exact tfc_runOK_afterRunRemoved_nil (st.piles a)
      | cons y t =>
          show runOK ((y :: t : List Card)) = true
          rw [← hchop]
          exact runOK_chop (hpile a)
    · rw [hpj j, ite_eq_right hj]
      exact hpile j
  · intro c₀ hc₀
    have hcc := hcard c₀ hc₀
    rw [tfc_cardCount_zones] at hcc
    rw [tfc_cardCount_zones]
    have hlastc : lastOf (st.piles a).faceUp = some c := (tfc_pileOfTop_top hpstop).2
    have hsnoc : (st.piles a).faceUp = chop (st.piles a).faceUp ++ [c] :=
      lastOf_chop hlastc
    have hpcnt : tfc_cntFlat c₀
          (Anchor.all.map fun j => (st'.piles j).hidden ++ (st'.piles j).faceUp)
        + tfc_cnt c₀ [c]
        = tfc_cntFlat c₀ (Anchor.all.map fun j => (st.piles j).hidden ++ (st.piles j).faceUp) := by
      have h1 := tfc_cntFlat_map_delta c₀
        (fun j => (st'.piles j).hidden ++ (st'.piles j).faceUp)
        (fun j => (st.piles j).hidden ++ (st.piles j).faceUp)
        Anchor.all
        (fun j => if j = a then tfc_cnt c₀ [c] else 0)
        (by intro j _
            by_cases hj : j = a
            · rw [hj, hpj a, ite_eq_left rfl, ite_eq_left rfl]
              exact tfc_afterRunRemoved_zone_cnt (st.piles a) [c] c₀
                (chop (st.piles a).faceUp) hsnoc
            · rw [hpj j, ite_eq_right hj, ite_eq_right hj]
              omega)
      have h2 : (Anchor.all.map (fun j => if j = a then tfc_cnt c₀ [c] else 0)).sum
          = tfc_cnt c₀ [c] := by
        have h3 := tfc_sum_map_single Anchor.all
          (fun j => if j = a then tfc_cnt c₀ [c] else 0) a
          Anchor.all_nodup (Anchor.mem_all a)
          (by intro j _ hjc; rw [ite_eq_right hjc])
        have h4 : (if a = a then tfc_cnt c₀ [c] else 0) = tfc_cnt c₀ [c] := by
          rw [ite_eq_left rfl]
        rw [h3, h4]
      rw [← h1, h2]
    have hfdelta : tfc_cntFlat c₀ (Suit.all.map st'.found)
        = tfc_cntFlat c₀ (Suit.all.map st.found) + tfc_cnt c₀ [c] := by
      have h1 := tfc_cntFlat_map_delta c₀ st.found st'.found Suit.all
        (fun σ => if σ = c.suit then tfc_cnt c₀ [c] else 0)
        (by intro σ _
            by_cases hσc : σ = c.suit
            · rw [hσc, hf, tfc_cnt_snoc, ite_eq_left rfl]
            · rw [hfne σ hσc, ite_eq_right hσc]
              omega)
      have h2 : (Suit.all.map (fun σ => if σ = c.suit then tfc_cnt c₀ [c] else 0)).sum
          = tfc_cnt c₀ [c] := by
        have h3 := tfc_sum_map_single Suit.all
          (fun σ => if σ = c.suit then tfc_cnt c₀ [c] else 0) c.suit
          Suit_all_nodup (Suit.mem_all c.suit)
          (by intro j _ hjc; rw [ite_eq_right hjc])
        have h4 : (if c.suit = c.suit then tfc_cnt c₀ [c] else 0) = tfc_cnt c₀ [c] := by
          rw [ite_eq_left rfl]
        rw [h3, h4]
      rw [← h1, h2]
    have hstockc : tfc_cnt c₀ st'.stock = tfc_cnt c₀ st.stock := by rw [hstockeq]
    have hwastec : tfc_cnt c₀ st'.waste = tfc_cnt c₀ st.waste := by rw [hwasteq]
    omega

/-- The `foundToTab` move: the foundation top returns to the
tableau — the foundation loses its top card by `chop`, and the
empty position or pile top takes it.  PORTED verbatim from
`Orig/Reach.lean:1273`, at the kit's rows (the frozen private
`runOK_append_fit` is CargoKit's `tfc_runOK_append_fit` here; the
seam's `putCard_eq_inl`/`putCard_inr_eq` build the update shapes). -/
private theorem foundToTab_wf {st st' : State} {c : Card} {b : Base}
    (hwf : st.WF) (h : State.step st (.foundToTab c b) = some st') : st'.WF := by
  obtain ⟨hpre, hpile, hcard, hsd⟩ := hwf
  obtain ⟨c₀', hft, hc'c, hcp, hrw⟩ := step_foundToTab_inv h
  have hc'' : st.foundTop c.suit = some c := hft.trans (congrArg some hc'c)
  have hlast : lastOf (st.found c.suit) = some c := foundTop_lastOf hc''
  have hsnocf : st.found c.suit = chop (st.found c.suit) ++ [c] :=
    lastOf_chop hlast
  have hR : ∀ c₀, tfc_cnt c₀ (st.found c.suit)
      = tfc_cnt c₀ (chop (st.found c.suit)) + tfc_cnt c₀ [c] := by
    intro c₀
    have h1 : tfc_cnt c₀ (chop (st.found c.suit) ++ [c])
        = tfc_cnt c₀ (chop (st.found c.suit)) + tfc_cnt c₀ [c] :=
      tfc_cnt_snoc c₀ c (chop (st.found c.suit))
    rw [← hsnocf] at h1
    exact h1
  cases b with
  | inl a₁ =>
      obtain ⟨hempty, _⟩ := canPlace_inl hcp
      have hfeq : st'.found
          = (st.setFound c.suit (chop (st.found c.suit))).found := by
        rw [hrw, putCard_eq_inl]
        rfl
      have hpil : st'.piles
          = (st.setFound c.suit (chop (st.found c.suit))
            |>.setPile a₁ ⟨[], [c]⟩).piles := by
        rw [hrw, putCard_eq_inl]
      have hstock : st'.stock = st.stock := by
        rw [hrw, putCard_eq_inl]
        show (st.setFound c.suit (chop (st.found c.suit))).stock = st.stock
        rfl
      have hwaste : st'.waste = st.waste := by
        rw [hrw, putCard_eq_inl]
        show (st.setFound c.suit (chop (st.found c.suit))).waste = st.waste
        rfl
      have hsd' : 0 < st'.drawStep := by
        have hdeq : st'.drawStep = st.drawStep := by
          rw [hrw, putCard_eq_inl]
          show (st.setFound c.suit (chop (st.found c.suit))).drawStep = st.drawStep
          rfl
        rw [hdeq]; exact hsd
      refine ⟨?_, ?_, ?_, hsd'⟩
      · intro σ
        rcases Decidable.em (σ = c.suit) with hσ | hσ
        · obtain ⟨m, hm⟩ := found_chop_prefix hpre hlast
          refine ⟨m, ?_⟩
          rw [hσ, hfeq, show (st.setFound c.suit (chop (st.found c.suit))).found c.suit
              = chop (st.found c.suit) from setFound_found_self, hm]
        · obtain ⟨n, hn⟩ := hpre σ
          refine ⟨n, ?_⟩
          rw [hfeq, setFound_found_ne hσ, hn]
      · intro j
        rcases Decidable.em (j = a₁) with hj | hj
        · rw [hj, show st'.piles a₁
              = (st.setFound c.suit (chop (st.found c.suit))
                  |>.setPile a₁ ⟨[], [c]⟩).piles a₁ from by rw [hpil],
            setPile_piles_self]
          show runOK ([c] : List Card) = true
          rfl
        · rw [show st'.piles j
              = (st.setFound c.suit (chop (st.found c.suit))
                  |>.setPile a₁ ⟨[], [c]⟩).piles j from by rw [hpil],
            setPile_piles_ne hj]
          exact hpile j
      · intro c₀ hc₀
        have hcc := hcard c₀ hc₀
        rw [tfc_cardCount_zones] at hcc
        rw [tfc_cardCount_zones]
        have hfdelta : tfc_cntFlat c₀ (Suit.all.map st'.found) + tfc_cnt c₀ [c]
            = tfc_cntFlat c₀ (Suit.all.map st.found) := by
          have h1 := tfc_cntFlat_map_delta c₀ st'.found st.found Suit.all
            (fun σ => if σ = c.suit then tfc_cnt c₀ [c] else 0)
            (by intro σ _
                by_cases hσ : σ = c.suit
                · rw [hσ, hfeq, setFound_found_self, ite_eq_left rfl, hR c₀]
                · rw [hfeq, setFound_found_ne hσ, ite_eq_right hσ]
                  omega)
          have h2 : (Suit.all.map (fun σ => if σ = c.suit then tfc_cnt c₀ [c] else 0)).sum
              = tfc_cnt c₀ [c] := by
            have h3 := tfc_sum_map_single Suit.all
              (fun σ => if σ = c.suit then tfc_cnt c₀ [c] else 0) c.suit
              Suit_all_nodup (Suit.mem_all c.suit)
              (by intro j _ hjc; rw [ite_eq_right hjc])
            have h4 : (if c.suit = c.suit then tfc_cnt c₀ [c] else 0) = tfc_cnt c₀ [c] := by
              rw [ite_eq_left rfl]
            rw [h3, h4]
          rw [← h1, h2]
        have hpcnt : tfc_cntFlat c₀
              (Anchor.all.map fun j => (st'.piles j).hidden ++ (st'.piles j).faceUp)
            = tfc_cntFlat c₀ (Anchor.all.map fun j => (st.piles j).hidden ++ (st.piles j).faceUp)
              + tfc_cnt c₀ [c] := by
          have h1 := tfc_cntFlat_map_delta c₀
            (fun j => (st.piles j).hidden ++ (st.piles j).faceUp)
            (fun j => ((st.setFound c.suit (chop (st.found c.suit))
                |>.setPile a₁ ⟨[], [c]⟩).piles j).hidden
              ++ ((st.setFound c.suit (chop (st.found c.suit))
                |>.setPile a₁ ⟨[], [c]⟩).piles j).faceUp)
            Anchor.all
            (fun j => if j = a₁ then tfc_cnt c₀ [c] else 0)
            (by intro j _
                by_cases hj : j = a₁
                · have hgo : tfc_cnt c₀
                        (((st.setFound c.suit (chop (st.found c.suit))
                          |>.setPile a₁ ⟨[], [c]⟩).piles a₁).hidden
                          ++ ((st.setFound c.suit (chop (st.found c.suit))
                          |>.setPile a₁ ⟨[], [c]⟩).piles a₁).faceUp)
                      = tfc_cnt c₀ ([c] : List Card) := by
                    rw [setPile_piles_self]
                    show tfc_cnt c₀ (([] : List Card) ++ ([c] : List Card)) = tfc_cnt c₀ [c]
                    rw [tfc_cnt_app c₀, tfc_cnt_nil]
                    omega
                  have hF0 : tfc_cnt c₀ ((st.piles a₁).hidden ++ (st.piles a₁).faceUp)
                      = 0 := by
                    obtain ⟨hid, hfu⟩ := (Pile.isEmpty_eq _).mp hempty
                    rw [hid, hfu, tfc_cnt_app c₀, tfc_cnt_nil]
                  rw [hj, hgo, ite_eq_left rfl, hF0]
                  omega
                · rw [ite_eq_right hj]
                  have hident : tfc_cnt c₀ ((st.piles j).hidden ++ (st.piles j).faceUp)
                      = tfc_cnt c₀ (((st.setFound c.suit (chop (st.found c.suit))
                          |>.setPile a₁ ⟨[], [c]⟩).piles j).hidden
                        ++ ((st.setFound c.suit (chop (st.found c.suit))
                          |>.setPile a₁ ⟨[], [c]⟩).piles j).faceUp) := by
                    rw [setPile_piles_ne hj]
                    rfl
                  rw [hident]
                  omega)
          have h2 : (Anchor.all.map (fun j => if j = a₁ then tfc_cnt c₀ [c] else 0)).sum
              = tfc_cnt c₀ [c] := by
            have h3 := tfc_sum_map_single Anchor.all
              (fun j => if j = a₁ then tfc_cnt c₀ [c] else 0) a₁
              Anchor.all_nodup (Anchor.mem_all a₁)
              (by intro j _ hjc; rw [ite_eq_right hjc])
            have h4 : (if a₁ = a₁ then tfc_cnt c₀ [c] else 0) = tfc_cnt c₀ [c] := by
              rw [ite_eq_left rfl]
            rw [h3, h4]
          have hfold : tfc_cntFlat c₀
              (Anchor.all.map fun j => (st'.piles j).hidden ++ (st'.piles j).faceUp)
              = tfc_cntFlat c₀
                  (Anchor.all.map fun j => ((st.setFound c.suit (chop (st.found c.suit))
                      |>.setPile a₁ ⟨[], [c]⟩).piles j).hidden
                    ++ ((st.setFound c.suit (chop (st.found c.suit))
                      |>.setPile a₁ ⟨[], [c]⟩).piles j).faceUp) := by
            rw [hpil]
          rw [hfold, ← h1, h2]
        have hstockc : tfc_cnt c₀ st'.stock = tfc_cnt c₀ st.stock := by rw [hstock]
        have hwastec : tfc_cnt c₀ st'.waste = tfc_cnt c₀ st.waste := by rw [hwaste]
        omega
  | inr z =>
      obtain ⟨k, hps, hfit⟩ := canPlace_inr hcp
      have htopk : lastOf (st.piles k).faceUp = some z := (tfc_pileOfTop_top hps).2
      have hpsA : (st.setFound c.suit (chop (st.found c.suit))).pileOfTop z
          = some k := by
        rw [pileOfTop_setFound]
        exact hps
      have hfeq : st'.found
          = (st.setFound c.suit (chop (st.found c.suit))).found := by
        rw [hrw]
        show (st.setFound c.suit (chop (st.found c.suit))
          |>.putCard c (Sum.inr z)).found = _
        rw [putCard_inr_eq hpsA]
        rfl
      have hpil : st'.piles
          = (st.setFound c.suit (chop (st.found c.suit))
            |>.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles := by
        rw [hrw]
        show (st.setFound c.suit (chop (st.found c.suit))
          |>.putCard c (Sum.inr z)).piles = _
        rw [putCard_inr_eq hpsA]
        rfl
      have hstock : st'.stock = st.stock := by
        rw [hrw]
        show (st.setFound c.suit (chop (st.found c.suit))
          |>.putCard c (Sum.inr z)).stock = st.stock
        rw [putCard_inr_eq hpsA]
        rfl
      have hwaste : st'.waste = st.waste := by
        rw [hrw]
        show (st.setFound c.suit (chop (st.found c.suit))
          |>.putCard c (Sum.inr z)).waste = st.waste
        rw [putCard_inr_eq hpsA]
        rfl
      have hsd' : 0 < st'.drawStep := by
        have hdeq : st'.drawStep = st.drawStep := by
          rw [hrw]
          show (st.setFound c.suit (chop (st.found c.suit))
            |>.putCard c (Sum.inr z)).drawStep = st.drawStep
          rw [putCard_inr_eq hpsA]
          rfl
        rw [hdeq]; exact hsd
      refine ⟨?_, ?_, ?_, hsd'⟩
      · intro σ
        rcases Decidable.em (σ = c.suit) with hσ | hσ
        · obtain ⟨m, hm⟩ := found_chop_prefix hpre hlast
          refine ⟨m, ?_⟩
          rw [hσ, hfeq, show (st.setFound c.suit (chop (st.found c.suit))).found c.suit
              = chop (st.found c.suit) from setFound_found_self, hm]
        · obtain ⟨n, hn⟩ := hpre σ
          refine ⟨n, ?_⟩
          rw [hfeq, setFound_found_ne hσ, hn]
      · intro j
        rcases Decidable.em (j = k) with hj | hj
        · rw [hj, show st'.piles k
              = (st.setFound c.suit (chop (st.found c.suit))
                  |>.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles k
              from by rw [hpil],
            setPile_piles_self]
          show runOK ((st.piles k).faceUp ++ ([c] : List Card)) = true
          exact tfc_runOK_append_fit (st.piles k).faceUp c z ([] : List Card)
            (hpile k) rfl htopk hfit
        · rw [show st'.piles j
              = (st.setFound c.suit (chop (st.found c.suit))
                  |>.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles j
              from by rw [hpil],
            setPile_piles_ne hj]
          exact hpile j
      · intro c₀ hc₀
        have hcc := hcard c₀ hc₀
        rw [tfc_cardCount_zones] at hcc
        rw [tfc_cardCount_zones]
        have hfdelta : tfc_cntFlat c₀ (Suit.all.map st'.found) + tfc_cnt c₀ [c]
            = tfc_cntFlat c₀ (Suit.all.map st.found) := by
          have h1 := tfc_cntFlat_map_delta c₀ st'.found st.found Suit.all
            (fun σ => if σ = c.suit then tfc_cnt c₀ [c] else 0)
            (by intro σ _
                by_cases hσ : σ = c.suit
                · rw [hσ, hfeq, setFound_found_self, ite_eq_left rfl, hR c₀]
                · rw [hfeq, setFound_found_ne hσ, ite_eq_right hσ]
                  omega)
          have h2 : (Suit.all.map (fun σ => if σ = c.suit then tfc_cnt c₀ [c] else 0)).sum
              = tfc_cnt c₀ [c] := by
            have h3 := tfc_sum_map_single Suit.all
              (fun σ => if σ = c.suit then tfc_cnt c₀ [c] else 0) c.suit
              Suit_all_nodup (Suit.mem_all c.suit)
              (by intro j _ hjc; rw [ite_eq_right hjc])
            have h4 : (if c.suit = c.suit then tfc_cnt c₀ [c] else 0) = tfc_cnt c₀ [c] := by
              rw [ite_eq_left rfl]
            rw [h3, h4]
          rw [← h1, h2]
        have hpcnt : tfc_cntFlat c₀
              (Anchor.all.map fun j => (st'.piles j).hidden ++ (st'.piles j).faceUp)
            = tfc_cntFlat c₀ (Anchor.all.map fun j => (st.piles j).hidden ++ (st.piles j).faceUp)
              + tfc_cnt c₀ [c] := by
          have h1 := tfc_cntFlat_map_delta c₀
            (fun j => (st.piles j).hidden ++ (st.piles j).faceUp)
            (fun j => ((st.setFound c.suit (chop (st.found c.suit))
                |>.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles j).hidden
              ++ ((st.setFound c.suit (chop (st.found c.suit))
                |>.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles j).faceUp)
            Anchor.all
            (fun j => if j = k then tfc_cnt c₀ [c] else 0)
            (by intro j _
                by_cases hj : j = k
                · have hgo : tfc_cnt c₀
                        (((st.setFound c.suit (chop (st.found c.suit))
                           |>.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles k).hidden
                          ++ ((st.setFound c.suit (chop (st.found c.suit))
                           |>.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles k).faceUp)
                      = tfc_cnt c₀ ((st.piles k).hidden ++ ((st.piles k).faceUp ++ [c])) := by
                    rw [setPile_piles_self]
                  rw [hj, hgo, ite_eq_left rfl, ← List.append_assoc, tfc_cnt_snoc]
                · rw [ite_eq_right hj]
                  have hident : tfc_cnt c₀ ((st.piles j).hidden ++ (st.piles j).faceUp)
                      = tfc_cnt c₀ (((st.setFound c.suit (chop (st.found c.suit))
                          |>.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles j).hidden
                        ++ ((st.setFound c.suit (chop (st.found c.suit))
                          |>.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles j).faceUp) := by
                    rw [setPile_piles_ne hj]
                    rfl
                  rw [hident]
                  omega)
          have h2 : (Anchor.all.map (fun j => if j = k then tfc_cnt c₀ [c] else 0)).sum
              = tfc_cnt c₀ [c] := by
            have h3 := tfc_sum_map_single Anchor.all
              (fun j => if j = k then tfc_cnt c₀ [c] else 0) k
              Anchor.all_nodup (Anchor.mem_all k)
              (by intro j _ hjc; rw [ite_eq_right hjc])
            have h4 : (if k = k then tfc_cnt c₀ [c] else 0) = tfc_cnt c₀ [c] := by
              rw [ite_eq_left rfl]
            rw [h3, h4]
          have hfold : tfc_cntFlat c₀
              (Anchor.all.map fun j => (st'.piles j).hidden ++ (st'.piles j).faceUp)
              = tfc_cntFlat c₀
                  (Anchor.all.map fun j => ((st.setFound c.suit (chop (st.found c.suit))
                      |>.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles j).hidden
                    ++ ((st.setFound c.suit (chop (st.found c.suit))
                      |>.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles j).faceUp) := by
            rw [hpil]
          rw [hfold, ← h1, h2]
        have hstockc : tfc_cnt c₀ st'.stock = tfc_cnt c₀ st.stock := by rw [hstock]
        have hwastec : tfc_cnt c₀ st'.waste = tfc_cnt c₀ st.waste := by rw [hwaste]
        omega

/-! ## §2. The capstones -/

/-- A legal step from a well-formed position lands well-formed: the
conservation invariant, the foundation prefix discipline, and the
draw-step clause all survive every constructor.  PORTED verbatim
from `Orig/Reach.lean:2104` (statement verbatim; the `tabToTab` arm
is CargoKit's `tfc_tabToTab_wf`, the other five arms this card's
private reading above). -/
theorem step_wf {st st' : State} {m : Move} (hwf : st.WF)
    (h : State.step st m = some st') : st'.WF := by
  cases m with
  | draw => exact draw_wf hwf h
  | wasteToFound c => exact wasteToFound_wf hwf h
  | wasteToTab c b => exact wasteToTab_wf hwf h
  | tabToFound c => exact tabToFound_wf hwf h
  | foundToTab c b => exact foundToTab_wf hwf h
  | tabToTab c b => exact tfc_tabToTab_wf hwf h

/-- **A legal play from a well-formed position lands well-formed** —
the step fence's play lift (this card's own row): one instance of
Kit's `run_rec` engine over `step_wf`, the single home the frozen
tier re-derived per-file (`Orig/Dominance.lean:9177` and the
ForkFloor/ForkCensus lifts, all superseded here). -/
theorem run_wf {st : State} (hwf : st.WF) : ∀ {play : List Move} {w : State},
    st.run play = some w → w.WF :=
  fun h => run_rec (fun x y => x.WF → y.WF)
    (fun hstep _ ih hwf₁ => ih (step_wf hwf₁ hstep))
    (fun _ hwf₁ => hwf₁) h hwf

/-! ## The audit battery

Per promoted head, this card.  Expected profile: `[propext]` or
`[propext, Quot.sound]` — never `sorryAx`, never `Classical.choice`. -/

#print axioms step_wf
#print axioms run_wf
