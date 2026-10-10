import Orig.Fate

/-!
# Orig — search integrity at `WF` states

`Orig/State.lean` licenses its two `firstWhere` searches and its
`canPlace` with a comment: "the fit rules make illegal same-pile
targets unreachable, so no side conditions are needed (a later
chapter proves this at `WF` states)".  This is that chapter.  At a
`WF` position every card occurs in exactly one place, so:

* the searches find the pile they promise, and only that pile —
  `pileHolding_eq_some_iff` / `pileOfTop_eq_some_iff` with their
  injectivity companions, on top of a public `pileHolding_mem`;
* `canPlace` never aims a card at its own pile or under its own
  run — `canPlace_inr_target_pile_ne` (the target pile is another
  pile), `canPlace_inr_target_off_run` (the target card does not
  lie in the mover's own run), and the empty-seat companion
  `canPlace_inl_target_pile_ne`.

The engine is occurrence bookkeeping (`mem_pile_unique`: a card in
one pile is in no other zone) plus a `runOK` descent kit
(`runOK_desc`, `runOK_nodup`) and a `firstWhere` completeness mini
lemma.  Convenience projections of `State.WF`
(`found_prefix`, `runOK_of`, `cardCount_eq`, `drawStep_pos`) and
`Pile.isEmpty_eq` ride along as the one-liners downstream cards
quote.

The census inversion is completed in all directions: the same-pile
half (`mem_faceUp_not_hidden` / `mem_hidden_not_faceUp` — a face-up
card is never its own pile's hidden card, and conversely), the
foundation/stock/waste sides (`mem_found_unique`,
`mem_stock_unique`, `mem_waste_unique`), and the compound one-liners
the exchange rows cite (`mem_faceUp_only` / `mem_hidden_only`: one
membership pins every other zone at once).  The pack is
dedup-marked against `Orig/TwinExchange.lean`'s private count kit
(its `ccn` mirrors and the `hZP`-style double-count idiom).

Constructivity: the searches carry decidable predicates and the
counts are finite list arithmetic — every theorem here audits
`[propext, Quot.sound]` or fewer; nothing drags `Classical.choice`.
-/

/-! ## The `WF` accessor strip -/

namespace State

/-- Foundations are prefixes of their build order. -/
theorem WF.found_prefix {st : State} (h : st.WF) (s : Suit) :
    ∃ n, st.found s = s.upCards.take n := h.1 s

/-- Every pile's face-up run is legal. -/
theorem WF.runOK_of {st : State} (h : st.WF) (a : Anchor) :
    runOK (st.piles a).faceUp = true := h.2.1 a

/-- Every real card occurs exactly once in the position. -/
theorem WF.cardCount_eq {st : State} (h : st.WF) {c : Card}
    (hc : c ∈ Card.universe) : st.cardCount c = 1 := h.2.2.1 c hc

/-- The draw step is 1 or 3. -/
theorem WF.drawStep_pos {st : State} (h : st.WF) :
    0 < st.drawStep := h.2.2.2

end State

namespace Pile

/-- A pile is empty iff both of its parts are. -/
theorem isEmpty_eq (p : Pile) :
    p.isEmpty = true ↔ p.hidden = [] ∧ p.faceUp = [] := by
  rcases p with ⟨h, f⟩
  cases h <;> cases f <;> simp [Pile.isEmpty]

end Pile

/-! ## Occurrence bookkeeping -/

/-- A pile's whole zone, hidden cards under face-up ones. -/
private def pileZone (st : State) (a : Anchor) : List Card :=
  (st.piles a).hidden ++ (st.piles a).faceUp

/-- The anchors before `a` in the deal order. -/
private def preAnchors : Anchor → List Anchor
  | .p0 => [] | .p1 => [.p0] | .p2 => [.p0, .p1] | .p3 => [.p0, .p1, .p2]
  | .p4 => [.p0, .p1, .p2, .p3] | .p5 => [.p0, .p1, .p2, .p3, .p4]
  | .p6 => [.p0, .p1, .p2, .p3, .p4, .p5]

/-- The anchors after `a` in the deal order. -/
private def sufAnchors : Anchor → List Anchor
  | .p0 => [.p1, .p2, .p3, .p4, .p5, .p6] | .p1 => [.p2, .p3, .p4, .p5, .p6]
  | .p2 => [.p3, .p4, .p5, .p6] | .p3 => [.p4, .p5, .p6]
  | .p4 => [.p5, .p6] | .p5 => [.p6] | .p6 => []

private theorem anchor_split (a : Anchor) :
    Anchor.all = preAnchors a ++ [a] ++ sufAnchors a := by
  cases a <;> rfl

private theorem anchor_ne_mem {a a' : Anchor} (hne : a' ≠ a) :
    a' ∈ preAnchors a ∨ a' ∈ sufAnchors a := by
  cases a <;> cases a' <;> simp_all [preAnchors, sufAnchors]

private theorem flatMapAppend {α β : Type} (f : α → List β) :
    ∀ (A B : List α), List.flatMap f (A ++ B) = List.flatMap f A ++ List.flatMap f B := by
  intro A
  induction A with
  | nil => intro B; rfl
  | cons x t ih =>
      intro B
      show f x ++ List.flatMap f (t ++ B) = (f x ++ List.flatMap f t) ++ List.flatMap f B
      rw [ih, List.append_assoc]

/-- Two card occurrences in separate flatMap blocks make the count
at least two. -/
private theorem count_ge_two_of_split {st : State} {c : Card} {A B : List (List Card)}
    (hsplit : st.zones = A ++ B) (hl : c ∈ A.flatMap id) (hr : c ∈ B.flatMap id) :
    2 ≤ st.cardCount c := by
  show 2 ≤ ((st.zones.flatMap id).filter fun x => decide (x = c)).length
  rw [hsplit, flatMapAppend, List.filter_append, List.length_append]
  have hL := count_filter_pos hl
  have hR := count_filter_pos hr
  omega

private theorem zone_mem_map {st : State} {zs : List Anchor} {a : Anchor}
    (h : a ∈ zs) : pileZone st a ∈ zs.map (pileZone st) :=
  List.mem_map.2 ⟨a, h, rfl⟩

private theorem found_mem_map {st : State} {ss : List Suit} {s : Suit}
    (h : s ∈ ss) : st.found s ∈ ss.map st.found :=
  List.mem_map.2 ⟨s, h, rfl⟩

private theorem zones_split_pre (st : State) (a : Anchor) :
    st.zones = (Suit.all.map st.found ++ (preAnchors a).map (pileZone st)) ++
      (pileZone st a :: ((sufAnchors a).map (pileZone st) ++ [st.stock, st.waste])) := by
  have h1 : Anchor.all = preAnchors a ++ [a] ++ sufAnchors a := anchor_split a
  have h2 : List.map (pileZone st) [a] = [pileZone st a] := rfl
  rw [show st.zones = Suit.all.map st.found ++
      (Anchor.all.map (pileZone st) ++ [st.stock, st.waste]) from rfl,
    h1, List.map_append, List.map_append, h2]
  simp only [List.append_assoc]
  rfl

private theorem zones_split_suf (st : State) (a : Anchor) :
    st.zones = ((Suit.all.map st.found ++ (preAnchors a).map (pileZone st)) ++
        [pileZone st a]) ++
      ((sufAnchors a).map (pileZone st) ++ [st.stock, st.waste]) := by
  have h1 : Anchor.all = preAnchors a ++ [a] ++ sufAnchors a := anchor_split a
  have h2 : List.map (pileZone st) [a] = [pileZone st a] := rfl
  rw [show st.zones = Suit.all.map st.found ++
      (Anchor.all.map (pileZone st) ++ [st.stock, st.waste]) from rfl,
    h1, List.map_append, List.map_append, h2]
  simp only [List.append_assoc]

private theorem wf_two_piles_ne {st : State} {c : Card} {a a' : Anchor} (hwf : st.WF)
    (hza : c ∈ pileZone st a) (hza' : c ∈ pileZone st a') (hne : a' ≠ a) : False := by
  have hcount : st.cardCount c = 1 := hwf.cardCount_eq (Card.mem_universe c)
  have h2 : 2 ≤ st.cardCount c := by
    rcases anchor_ne_mem hne with hpre | hsuf
    · refine count_ge_two_of_split (zones_split_pre st a) ?_ ?_
      · exact (List.mem_flatMap).2 ⟨pileZone st a',
          (List.mem_append).2 (Or.inr (zone_mem_map hpre)), hza'⟩
      · exact (List.mem_flatMap).2 ⟨pileZone st a, List.mem_cons.2 (Or.inl rfl), hza⟩
    · refine count_ge_two_of_split (zones_split_suf st a) ?_ ?_
      · exact (List.mem_flatMap).2 ⟨pileZone st a,
          (List.mem_append).2 (Or.inr (List.mem_cons.2 (Or.inl rfl))), hza⟩
      · exact (List.mem_flatMap).2 ⟨pileZone st a',
          (List.mem_append).2 (Or.inl (zone_mem_map hsuf)), hza'⟩
  omega

private theorem wf_pile_found_ne {st : State} {c : Card} {a : Anchor} {s : Suit}
    (hwf : st.WF) (hza : c ∈ pileZone st a) (hf : c ∈ st.found s) : False := by
  have hcount : st.cardCount c = 1 := hwf.cardCount_eq (Card.mem_universe c)
  have hsplit : st.zones = Suit.all.map st.found ++
      (Anchor.all.map (pileZone st) ++ [st.stock, st.waste]) := rfl
  have h2 : 2 ≤ st.cardCount c :=
    count_ge_two_of_split hsplit
      ((List.mem_flatMap).2 ⟨st.found s, found_mem_map (Suit.mem_all s), hf⟩)
      ((List.mem_flatMap).2 ⟨pileZone st a,
        (List.mem_append).2 (Or.inl (zone_mem_map (Anchor.mem_all a))), hza⟩)
  omega

private theorem wf_pile_stock_ne {st : State} {c : Card} {a : Anchor}
    (hwf : st.WF) (hza : c ∈ pileZone st a) (hs : c ∈ st.stock) : False := by
  have hcount : st.cardCount c = 1 := hwf.cardCount_eq (Card.mem_universe c)
  have hz0 : st.zones = Suit.all.map st.found ++
      (Anchor.all.map (pileZone st) ++ [st.stock, st.waste]) := rfl
  have hsplit : st.zones = (Suit.all.map st.found ++ Anchor.all.map (pileZone st)) ++
      [st.stock, st.waste] := hz0.trans (List.append_assoc _ _ _).symm
  have h2 : 2 ≤ st.cardCount c :=
    count_ge_two_of_split hsplit
      ((List.mem_flatMap).2 ⟨pileZone st a,
        (List.mem_append).2 (Or.inr (zone_mem_map (Anchor.mem_all a))), hza⟩)
      ((List.mem_flatMap).2 ⟨st.stock, List.mem_cons.2 (Or.inl rfl), hs⟩)
  omega

private theorem wf_pile_waste_ne {st : State} {c : Card} {a : Anchor}
    (hwf : st.WF) (hza : c ∈ pileZone st a) (hw : c ∈ st.waste) : False := by
  have hcount : st.cardCount c = 1 := hwf.cardCount_eq (Card.mem_universe c)
  have hz0 : st.zones = Suit.all.map st.found ++
      (Anchor.all.map (pileZone st) ++ [st.stock, st.waste]) := rfl
  have hsplit : st.zones = (Suit.all.map st.found ++
        (Anchor.all.map (pileZone st) ++ [st.stock])) ++ [st.waste] := by
    refine hz0.trans ?_
    simp only [List.append_assoc]
    rfl
  have h2 : 2 ≤ st.cardCount c :=
    count_ge_two_of_split hsplit
      ((List.mem_flatMap).2 ⟨pileZone st a,
        (List.mem_append).2 (Or.inr ((List.mem_append).2
          (Or.inl (zone_mem_map (Anchor.mem_all a))))), hza⟩)
      ((List.mem_flatMap).2 ⟨st.waste, List.mem_cons.2 (Or.inl rfl), hw⟩)
  omega

/-- The one general occurrence fact: a card in pile `a` — hidden or
face up, in either part — is nowhere else in a `WF` state.  No other
pile holds it, the stock and waste lack it, and it is on no
foundation.  This is what makes all the later searches unique. -/
theorem mem_pile_unique {st : State} {c : Card} {a : Anchor} (hwf : st.WF)
    (hmem : c ∈ (st.piles a).hidden ∨ c ∈ (st.piles a).faceUp) :
    (∀ a' ≠ a, c ∉ (st.piles a').hidden ∧ c ∉ (st.piles a').faceUp) ∧
      c ∉ st.stock ∧ c ∉ st.waste ∧ ∀ s, c ∉ st.found s := by
  have hz : c ∈ pileZone st a := by
    rcases hmem with h | h
    · exact (List.mem_append).2 (Or.inl h)
    · exact (List.mem_append).2 (Or.inr h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a' hne
    constructor
    · intro hcon
      exact wf_two_piles_ne hwf hz ((List.mem_append).2 (Or.inl hcon)) hne
    · intro hcon
      exact wf_two_piles_ne hwf hz ((List.mem_append).2 (Or.inr hcon)) hne
  · intro hcon
    exact wf_pile_stock_ne hwf hz hcon
  · intro hcon
    exact wf_pile_waste_ne hwf hz hcon
  · intro s hcon
    exact wf_pile_found_ne hwf hz hcon

/-- A face-up card is in no other pile — face up or hidden — and on
no stock, waste, or foundation card place. -/
theorem mem_faceUp_unique {st : State} {c : Card} {a : Anchor} (hwf : st.WF)
    (hmem : c ∈ (st.piles a).faceUp) :
    ∀ a' ≠ a, c ∉ (st.piles a').faceUp ∧ c ∉ (st.piles a').hidden ∧
      c ∉ st.stock ∧ c ∉ st.waste ∧ ∀ s, c ∉ st.found s := by
  intro a' hne
  obtain ⟨hh, hs, hw, hf⟩ := mem_pile_unique hwf (Or.inr hmem)
  exact ⟨(hh a' hne).2, (hh a' hne).1, hs, hw, hf⟩

/-- A hidden card is in no other pile — face up or hidden — and on
no stock, waste, or foundation card place. -/
theorem mem_hidden_unique {st : State} {c : Card} {a : Anchor} (hwf : st.WF)
    (hmem : c ∈ (st.piles a).hidden) :
    ∀ a' ≠ a, c ∉ (st.piles a').hidden ∧ c ∉ (st.piles a').faceUp ∧
      c ∉ st.stock ∧ c ∉ st.waste ∧ ∀ s, c ∉ st.found s := by
  intro a' hne
  obtain ⟨hh, hs, hw, hf⟩ := mem_pile_unique hwf (Or.inl hmem)
  exact ⟨(hh a' hne).1, (hh a' hne).2, hs, hw, hf⟩

/-! ## The same-pile and cross-side inversions

`mem_pile_unique` and its two projections exclude a card from every
*other* pile and from the stock, waste, and foundations — but not
from its own pile's other part, and the foundation/stock/waste sides
have no pack of their own.  This section completes the census
inversion so that one membership anywhere pins the card's location
everywhere; the exchange rows then cite the pack instead of
re-deriving double-count arguments (the `hZP`-style idiom in
`Orig/TwinExchange.lean`'s realization proofs, dedup-marked for the
tidy card against its private count kit).
-/

/-! ### The found-side splits -/

/-- The suits before `s` in enumeration order. -/
private def preSuits : Suit → List Suit
  | .spade => []
  | .heart => [.spade]
  | .diamond => [.spade, .heart]
  | .club => [.spade, .heart, .diamond]

/-- The suits after `s` in enumeration order. -/
private def sufSuits : Suit → List Suit
  | .spade => [.heart, .diamond, .club]
  | .heart => [.diamond, .club]
  | .diamond => [.club]
  | .club => []

private theorem suit_split (s : Suit) :
    Suit.all = preSuits s ++ [s] ++ sufSuits s := by
  cases s <;> rfl

private theorem suit_ne_mem {s s' : Suit} (hne : s' ≠ s) :
    s' ∈ preSuits s ∨ s' ∈ sufSuits s := by
  cases s <;> cases s' <;> simp_all [preSuits, sufSuits]

private theorem zones_split_found_pre (st : State) (s : Suit) :
    st.zones = (preSuits s).map st.found ++
      (st.found s :: ((sufSuits s).map st.found ++
        (Anchor.all.map (pileZone st) ++ [st.stock, st.waste]))) := by
  have h1 : Suit.all = preSuits s ++ [s] ++ sufSuits s := suit_split s
  have h2 : [s].map st.found = [st.found s] := rfl
  rw [show st.zones = Suit.all.map st.found ++
      (Anchor.all.map (pileZone st) ++ [st.stock, st.waste]) from rfl,
    h1, List.map_append, List.map_append, h2]
  simp only [List.append_assoc]
  rfl

private theorem zones_split_found_suf (st : State) (s : Suit) :
    st.zones = ((preSuits s).map st.found ++ [st.found s]) ++
      ((sufSuits s).map st.found ++
        (Anchor.all.map (pileZone st) ++ [st.stock, st.waste])) := by
  have h1 : Suit.all = preSuits s ++ [s] ++ sufSuits s := suit_split s
  have h2 : [s].map st.found = [st.found s] := rfl
  rw [show st.zones = Suit.all.map st.found ++
      (Anchor.all.map (pileZone st) ++ [st.stock, st.waste]) from rfl,
    h1, List.map_append, List.map_append, h2]
  simp only [List.append_assoc]

/-! ### The missing pair contradictions -/

private theorem wf_two_founds_ne {st : State} {c : Card} {s s' : Suit} (hwf : st.WF)
    (hf : c ∈ st.found s) (hf' : c ∈ st.found s') (hne : s' ≠ s) : False := by
  have hcount : st.cardCount c = 1 := hwf.cardCount_eq (Card.mem_universe c)
  have h2 : 2 ≤ st.cardCount c := by
    rcases suit_ne_mem hne with hpre | hsuf
    · refine count_ge_two_of_split (zones_split_found_pre st s) ?_ ?_
      · exact (List.mem_flatMap).2 ⟨st.found s', found_mem_map hpre, hf'⟩
      · exact (List.mem_flatMap).2 ⟨st.found s, List.mem_cons.2 (Or.inl rfl), hf⟩
    · refine count_ge_two_of_split (zones_split_found_suf st s) ?_ ?_
      · exact (List.mem_flatMap).2 ⟨st.found s,
          (List.mem_append).2 (Or.inr (List.mem_cons.2 (Or.inl rfl))), hf⟩
      · exact (List.mem_flatMap).2 ⟨st.found s',
          (List.mem_append).2 (Or.inl (found_mem_map hsuf)), hf'⟩
  omega

private theorem wf_found_stock_ne {st : State} {c : Card} {s : Suit} (hwf : st.WF)
    (hf : c ∈ st.found s) (hs : c ∈ st.stock) : False := by
  have hcount : st.cardCount c = 1 := hwf.cardCount_eq (Card.mem_universe c)
  have hsplit : st.zones = Suit.all.map st.found ++
      (Anchor.all.map (pileZone st) ++ [st.stock, st.waste]) := rfl
  have h2 : 2 ≤ st.cardCount c :=
    count_ge_two_of_split hsplit
      ((List.mem_flatMap).2 ⟨st.found s, found_mem_map (Suit.mem_all s), hf⟩)
      ((List.mem_flatMap).2 ⟨st.stock,
        (List.mem_append).2 (Or.inr (List.mem_cons.2 (Or.inl rfl))), hs⟩)
  omega

private theorem wf_found_waste_ne {st : State} {c : Card} {s : Suit} (hwf : st.WF)
    (hf : c ∈ st.found s) (hw : c ∈ st.waste) : False := by
  have hcount : st.cardCount c = 1 := hwf.cardCount_eq (Card.mem_universe c)
  have hz0 : st.zones = Suit.all.map st.found ++
      (Anchor.all.map (pileZone st) ++ [st.stock, st.waste]) := rfl
  have hsplit : st.zones = (Suit.all.map st.found ++
        (Anchor.all.map (pileZone st) ++ [st.stock])) ++ [st.waste] := by
    refine hz0.trans ?_
    simp only [List.append_assoc]
    rfl
  have h2 : 2 ≤ st.cardCount c :=
    count_ge_two_of_split hsplit
      ((List.mem_flatMap).2 ⟨st.found s, (List.mem_append).2
        (Or.inl (found_mem_map (Suit.mem_all s))), hf⟩)
      ((List.mem_flatMap).2 ⟨st.waste, List.mem_cons.2 (Or.inl rfl), hw⟩)
  omega

private theorem wf_stock_waste_ne {st : State} {c : Card} (hwf : st.WF)
    (hst : c ∈ st.stock) (hw : c ∈ st.waste) : False := by
  have hcount : st.cardCount c = 1 := hwf.cardCount_eq (Card.mem_universe c)
  have hz0 : st.zones = Suit.all.map st.found ++
      (Anchor.all.map (pileZone st) ++ [st.stock, st.waste]) := rfl
  have hsplit : st.zones = (Suit.all.map st.found ++
        (Anchor.all.map (pileZone st) ++ [st.stock])) ++ [st.waste] := by
    refine hz0.trans ?_
    simp only [List.append_assoc]
    rfl
  have h2 : 2 ≤ st.cardCount c :=
    count_ge_two_of_split hsplit
      ((List.mem_flatMap).2 ⟨st.stock, (List.mem_append).2
        (Or.inr ((List.mem_append).2 (Or.inr (List.mem_cons.2 (Or.inl rfl))))), hst⟩)
      ((List.mem_flatMap).2 ⟨st.waste, List.mem_cons.2 (Or.inl rfl), hw⟩)
  omega

/-! ### The intra-pile double count -/

private theorem flatMapSingleton {α β : Type} (f : α → List β) (x : α) :
    List.flatMap f [x] = f x := by
  simp [List.flatMap]

private theorem count_ge_two_pile_self {st : State} {c : Card} {a : Anchor}
    (hh : c ∈ (st.piles a).hidden) (hf : c ∈ (st.piles a).faceUp) :
    2 ≤ st.cardCount c := by
  have hsplit := zones_split_suf st a
  have hmid : 2 ≤ ((pileZone st a).filter fun x => decide (x = c)).length := by
    show 2 ≤ (List.filter (fun x => decide (x = c))
        ((st.piles a).hidden ++ (st.piles a).faceUp)).length
    rw [List.filter_append, List.length_append]
    have h1 := count_filter_pos hh
    have h2 := count_filter_pos hf
    omega
  have hflat : st.zones.flatMap id =
      ((Suit.all.map st.found ++ (preAnchors a).map (pileZone st)).flatMap id ++
        pileZone st a) ++
      ((sufAnchors a).map (pileZone st) ++ [st.stock, st.waste]).flatMap id := by
    rw [hsplit, flatMapAppend, flatMapAppend, flatMapSingleton]
    rfl
  show 2 ≤ ((st.zones.flatMap id).filter fun x => decide (x = c)).length
  rw [hflat, List.filter_append, List.filter_append,
    List.length_append, List.length_append]
  omega

/-! ### The completed inversion -/

/-- A face-up card never lies in its own pile's hidden cards — the
same-pile half of the census inversion (the cross-pile half is
`mem_faceUp_unique`). -/
theorem mem_faceUp_not_hidden {st : State} {c : Card} {a : Anchor} (hwf : st.WF)
    (h : c ∈ (st.piles a).faceUp) : c ∉ (st.piles a).hidden := by
  intro hcon
  have h1 : st.cardCount c = 1 := hwf.cardCount_eq (Card.mem_universe c)
  have h2 : 2 ≤ st.cardCount c := count_ge_two_pile_self hcon h
  omega

/-- A hidden card never lies in its own pile's face-up run. -/
theorem mem_hidden_not_faceUp {st : State} {c : Card} {a : Anchor} (hwf : st.WF)
    (h : c ∈ (st.piles a).hidden) : c ∉ (st.piles a).faceUp := by
  intro hcon
  have h1 : st.cardCount c = 1 := hwf.cardCount_eq (Card.mem_universe c)
  have h2 : 2 ≤ st.cardCount c := count_ge_two_pile_self h hcon
  omega

/-- One face-up membership pins the card's location everywhere: no
other pile (either part), not its own pile's hidden cards, not
stocked, not wasted, not on any foundation — the compound form the
exchange rows cite in place of a count re-derivation. -/
theorem mem_faceUp_only {st : State} {c : Card} {a : Anchor} (hwf : st.WF)
    (h : c ∈ (st.piles a).faceUp) :
    (∀ a' ≠ a, c ∉ (st.piles a').hidden ∧ c ∉ (st.piles a').faceUp) ∧
      c ∉ (st.piles a).hidden ∧ c ∉ st.stock ∧ c ∉ st.waste ∧
      ∀ s, c ∉ st.found s := by
  obtain ⟨hh, hs, hw, hf⟩ := mem_pile_unique hwf (Or.inr h)
  exact ⟨hh, mem_faceUp_not_hidden hwf h, hs, hw, hf⟩

/-- One hidden membership pins the card's location everywhere. -/
theorem mem_hidden_only {st : State} {c : Card} {a : Anchor} (hwf : st.WF)
    (h : c ∈ (st.piles a).hidden) :
    (∀ a' ≠ a, c ∉ (st.piles a').hidden ∧ c ∉ (st.piles a').faceUp) ∧
      c ∉ (st.piles a).faceUp ∧ c ∉ st.stock ∧ c ∉ st.waste ∧
      ∀ s, c ∉ st.found s := by
  obtain ⟨hh, hs, hw, hf⟩ := mem_pile_unique hwf (Or.inl h)
  exact ⟨hh, mem_hidden_not_faceUp hwf h, hs, hw, hf⟩

/-- A foundation card is nowhere else: in no pile (either part), not
stocked, not wasted, and on no other foundation. -/
theorem mem_found_unique {st : State} {c : Card} {s : Suit} (hwf : st.WF)
    (h : c ∈ st.found s) :
    (∀ a, c ∉ (st.piles a).hidden ∧ c ∉ (st.piles a).faceUp) ∧
      c ∉ st.stock ∧ c ∉ st.waste ∧ ∀ s' ≠ s, c ∉ st.found s' := by
  refine ⟨fun a => ⟨fun hcon => wf_pile_found_ne hwf ((List.mem_append).2 (Or.inl hcon)) h,
      fun hcon => wf_pile_found_ne hwf ((List.mem_append).2 (Or.inr hcon)) h⟩,
    fun hcon => wf_found_stock_ne hwf h hcon,
    fun hcon => wf_found_waste_ne hwf h hcon,
    fun s' hne hcon => wf_two_founds_ne hwf h hcon hne⟩

/-- A stock card is nowhere else. -/
theorem mem_stock_unique {st : State} {c : Card} (hwf : st.WF)
    (h : c ∈ st.stock) :
    (∀ a, c ∉ (st.piles a).hidden ∧ c ∉ (st.piles a).faceUp) ∧
      c ∉ st.waste ∧ ∀ s, c ∉ st.found s := by
  refine ⟨fun a => ⟨fun hcon => wf_pile_stock_ne hwf ((List.mem_append).2 (Or.inl hcon)) h,
      fun hcon => wf_pile_stock_ne hwf ((List.mem_append).2 (Or.inr hcon)) h⟩,
    fun hcon => wf_stock_waste_ne hwf h hcon,
    fun s hcon => wf_found_stock_ne hwf hcon h⟩

/-- A waste card is nowhere else. -/
theorem mem_waste_unique {st : State} {c : Card} (hwf : st.WF)
    (h : c ∈ st.waste) :
    (∀ a, c ∉ (st.piles a).hidden ∧ c ∉ (st.piles a).faceUp) ∧
      c ∉ st.stock ∧ ∀ s, c ∉ st.found s := by
  refine ⟨fun a => ⟨fun hcon => wf_pile_waste_ne hwf ((List.mem_append).2 (Or.inl hcon)) h,
      fun hcon => wf_pile_waste_ne hwf ((List.mem_append).2 (Or.inr hcon)) h⟩,
    fun hcon => wf_stock_waste_ne hwf hcon h,
    fun s hcon => wf_found_waste_ne hwf hcon h⟩

/-! ## `firstWhere` completeness -/

/-! ## The holding search -/

/-- Soundness of `pileHolding`: if the search answers, the card
really is face up in that pile. -/
theorem pileHolding_mem {st : State} {c : Card} {a : Anchor}
    (h : st.pileHolding c = some a) : c ∈ (st.piles a).faceUp :=
  of_decide_eq_true (firstWhere_sound (p := fun a' => decide (c ∈ (st.piles a').faceUp)) h)

/-- The holding search is exact at `WF` states: it answers `a`
precisely when `c` is face up in pile `a`. -/
theorem pileHolding_eq_some_iff {st : State} {c : Card} {a : Anchor} (hwf : st.WF) :
    st.pileHolding c = some a ↔ c ∈ (st.piles a).faceUp := by
  constructor
  · exact pileHolding_mem
  · intro hmem
    show firstWhere (fun a' => decide (c ∈ (st.piles a').faceUp)) Anchor.all = some a
    refine firstWhere_find (Anchor.mem_all a)
      (by simp only [decide_eq_true_eq]; exact hmem)
      (fun y hy hyne => ?_)
    exact decide_false_of_not ((mem_faceUp_unique hwf hmem y hyne).1)

/-- The holding search is deterministic: it names at most one pile. -/
theorem pileHolding_inj {st : State} {c : Card} {a a' : Anchor}
    (h : st.pileHolding c = some a) (h' : st.pileHolding c = some a') : a = a' := by
  rw [h] at h'
  injection h' with h''

namespace Pile

/-- A pile's top is its face-up list's last element. -/
theorem top_eq_lastOf_iff {p : Pile} {c : Card} :
    p.top = some c ↔ ∃ front, p.faceUp = front ++ [c] := by
  constructor
  · intro h
    exact lastOf_eq_snoc (show lastOf p.faceUp = some c from h)
  · rintro ⟨front, hfront⟩
    show lastOf p.faceUp = some c
    rw [hfront]
    exact lastOf_snoc

/-- The top card belongs to the face-up run. -/
theorem mem_of_top {p : Pile} {c : Card} (h : p.top = some c) : c ∈ p.faceUp :=
  lastOf_mem (show lastOf p.faceUp = some c from h)

end Pile

/-! ## The top search -/

/-- The top search is exact at `WF` states: it answers `a` precisely
when `z` is pile `a`'s top card. -/
theorem pileOfTop_eq_some_iff {st : State} {z : Card} {a : Anchor} (hwf : st.WF) :
    st.pileOfTop z = some a ↔ (st.piles a).top = some z := by
  constructor
  · intro h
    exact of_decide_eq_true
      (firstWhere_sound (p := fun a' => decide (st.topOf a' = some z)) h)
  · intro htop
    show firstWhere (fun a' => decide (st.topOf a' = some z)) Anchor.all = some a
    refine firstWhere_find (Anchor.mem_all a)
      (by simp only [decide_eq_true_eq]; exact htop)
      (fun y hy hyne => ?_)
    exact decide_false_of_not (fun hcon =>
      (mem_faceUp_unique hwf (Pile.mem_of_top htop) y hyne).1
        (Pile.mem_of_top (show (st.piles y).top = some z from hcon)))

/-- The top search is deterministic: it names at most one pile. -/
theorem pileOfTop_inj {st : State} {z : Card} {a a' : Anchor}
    (h : st.pileOfTop z = some a) (h' : st.pileOfTop z = some a') : a = a' := by
  rw [h] at h'
  injection h' with h''

/-! ## The `runOK` descent kit -/


/-- Every card under a legal run's head sits strictly below the
head in rank. -/
private theorem runOK_head_gt : ∀ {t : List Card} {x y : Card},
    runOK (x :: t) = true → y ∈ t → y.rank.toIdx < x.rank.toIdx := by
  intro t
  induction t with
  | nil => intro x y _ hmem; cases hmem
  | cons w t' ih =>
      intro x y hok hmem
      rw [runOK, Bool.and_eq_true] at hok
      obtain ⟨hsit, hrest⟩ := hok
      obtain ⟨heq, -⟩ := (canSitOn_eq w x).mp hsit
      have hwlt : w.rank.toIdx < x.rank.toIdx := by omega
      rcases List.mem_cons.1 hmem with rfl | hyt
      · exact hwlt
      · have := ih hrest hyt
        omega

/-- Strict rank descent, block form: in a legal face-up run, every
card of a later block sits strictly below every card of an earlier
block. -/
theorem runOK_desc : ∀ {P S : List Card} {x y : Card},
    runOK (P ++ S) = true → x ∈ P → y ∈ S → y.rank.toIdx < x.rank.toIdx := by
  intro P
  induction P with
  | nil => intro S x y _ hx; cases hx
  | cons p t ih =>
      intro S x y hok hx hy
      rcases List.mem_cons.1 hx with rfl | hxt
      · exact runOK_head_gt (show runOK (x :: (t ++ S)) = true from hok)
          ((List.mem_append).2 (Or.inr hy))
      · exact ih (runOK_cons_tail (show runOK (p :: (t ++ S)) = true from hok)) hxt hy

/-- A legal face-up run holds no card twice. -/
theorem runOK_nodup {l : List Card} (hok : runOK l = true) : l.Nodup := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons x t ih =>
      refine List.Pairwise.cons (fun y hy hyne => ?_) (ih (runOK_cons_tail hok))
      subst hyne
      have hgt := runOK_head_gt hok hy
      omega

/-- Everything in the run `fromCard c l` sits no higher than `c` in
rank: the descent of a legal run cuts off anything above `c` once
`c` itself appears. -/
private theorem runOK_fromCard_le : ∀ {l : List Card} {c x : Card},
    runOK l = true → x ∈ fromCard c l → x.rank.toIdx ≤ c.rank.toIdx := by
  intro l
  induction l with
  | nil => intro c x _ hmem; exact absurd hmem (by simp [fromCard])
  | cons y t ih =>
      intro c x hok hmem
      rw [fromCard] at hmem
      split at hmem
      · rename_i hyc
        rcases List.mem_cons.1 hmem with heq | hxt
        · subst heq; subst hyc; exact Nat.le_refl _
        · have hgt := runOK_head_gt hok hxt
          have hycr : y.rank.toIdx = c.rank.toIdx := by rw [hyc]
          omega
      · rename_i hyc
        exact ih (runOK_cons_tail hok) hmem

/-! ## `canPlace` self-safety -/

/-- A card that fits under `z` cannot itself sit below `z` in its
own run: a legal run descends from `c` while `z` is one rank above
`c`. -/
theorem canPlace_inr_target_off_run {st : State} {c z : Card} {a : Anchor}
    (hwf : st.WF) (hcp : st.canPlace c (Sum.inr z) = true)
    (_hmem : c ∈ (st.piles a).faceUp) :
    z ∉ fromCard c (st.piles a).faceUp := by
  intro hzin
  simp only [State.canPlace] at hcp
  split at hcp
  · rename_i k hk
    simp only [canSitOn_eq] at hcp
    obtain ⟨hrank, -⟩ := hcp
    have hdesc := runOK_fromCard_le (hwf.runOK_of a) hzin
    omega
  · exact Bool.noConfusion hcp

/-- The pile `z` tops is never the pile the mover `c` comes from:
`z` would be its top, yet everything after `c` in `c`'s own run
descends strictly. -/
theorem canPlace_inr_target_pile_ne {st : State} {c z : Card} {a : Anchor}
    (hwf : st.WF) (hcp : st.canPlace c (Sum.inr z) = true)
    (hmem : c ∈ (st.piles a).faceUp) :
    st.pileOfTop z ≠ some a := by
  intro hcon
  have htop : (st.piles a).top = some z :=
    of_decide_eq_true
      (firstWhere_sound (p := fun a' => decide (st.topOf a' = some z)) hcon)
  simp only [State.canPlace] at hcp
  split at hcp
  · rename_i k hk
    simp only [canSitOn_eq] at hcp
    obtain ⟨hrank, -⟩ := hcp
    obtain ⟨front, hfe⟩ := Pile.top_eq_lastOf_iff.mp htop
    rw [hfe] at hmem
    rcases (List.mem_append).1 hmem with hfront | hlast
    · have hrun : runOK (front ++ [z]) = true := by
        rw [← hfe]; exact hwf.runOK_of a
      have hdesc := runOK_desc hrun hfront (List.mem_cons.2 (Or.inl rfl))
      omega
    · rcases List.mem_cons.1 hlast with rfl | hnil
      · omega
      · cases hnil
  · exact Bool.noConfusion hcp

/-- The empty-seat branch never aims at the mover's own pile either:
`canPlace` demands the seat be empty while pile `a` holds `c` face
up.  (WF-free, like the branch's own condition.) -/
theorem canPlace_inl_target_pile_ne {st : State} {c : Card} {a b : Anchor}
    (hcp : st.canPlace c (Sum.inl b) = true) (hmem : c ∈ (st.piles a).faceUp) :
    b ≠ a := by
  intro hcon
  subst hcon
  simp only [State.canPlace, Bool.and_eq_true] at hcp
  obtain ⟨hempty, -⟩ := hcp
  obtain ⟨-, hfu⟩ := (Pile.isEmpty_eq _).mp hempty
  rw [hfu] at hmem
  exact absurd hmem (by simp)

/-! ## Card-fit arithmetic -/

/-- A fitting card is distinct from its host.  The rank half of the
fit ladder (the other ladder steps live in the exchange chapters'
kill families, dedup-marked against this home). -/
theorem ne_of_canSitOn {z y : Card} (h : canSitOn z y = true) : z ≠ y := by
  intro hcon
  subst hcon
  simp only [canSitOn_eq] at h
  omega

