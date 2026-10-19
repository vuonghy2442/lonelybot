import Orig2.Kit

/-!
# Orig2.Integrity — THE SEARCH-INTEGRITY CARD

THE CARD'S MISSION: at a `WF` position every real card occurs in
exactly one place, and this chapter licenses what the certified
core's `Orig/State.lean` searches promise — the holding search
(`pileHolding`) and the top search (`pileOfTop`) each find the pile
they name, and only that pile, while `canPlace` never aims a card
at its own pile or under its own run.  The engine is occurrence
bookkeeping (a card in one pile, stock, waste, or foundation is in
no other zone), the two census splits (anchors around a pile, suits
around a foundation), the completed census inversion (one
membership anywhere pins the card's location everywhere), the
`runOK` descent kit, and the `canPlace` self-safety family the undo
assemblies consume.

LINEAGE: `Orig/Integrity.lean` — the frozen chapter, read freely,
never imported: it rides above the closed core seam via
`Orig.Fate`, whose root-level `reversibleAtW` collides with the
registry carrier (the seam-veto record lives in the root charter
and in `Orig2/Classification.lean`'s header).  Every row below is
a re-statement at the seam definitions — a verbatim shape copy
with the frozen line cited per row.

THE SPLIT RECORD (2026-10-18, the owner's "split that into a new
file" decision): the classification card had landed part of this
pack 2026-10-17 as its per-file private kits — the `WF` accessor
strip (its §1a') and the count-integrity reading (its §1l) —
which stopped short of the frozen chapter's census inversion.  The
pack now has ONE home, this card, placed below the consumers on
the shared kit tier.  It adds everything the classification copies
lacked: the hidden uniqueness twin, the found-side splits, the
same-pile inversions (`mem_faceUp_not_hidden` /
`mem_hidden_not_faceUp`), the compound one-liners (`mem_faceUp_only`
/ `mem_hidden_only`), the foundation/stock/waste uniqueness pack,
the search exactness rows (`pileHolding_eq_some_iff` /
`pileOfTop_eq_some_iff`) with their determinism companions
(`pileHolding_inj` / `pileOfTop_inj`), `runOK_nodup`, the off-run
placement row `canPlace_inr_target_off_run`, and `ne_of_canSitOn`.
`Orig2/Classification.lean` imports this card and strikes its
private copies; its consuming rows resolve by name, byte-unchanged
(the strike-then-rewire recipe).

DEDUP: two rows of the frozen chapter already have their `Orig2`
home at `Orig2/Kit.lean` — `Pile.isEmpty_eq` (frozen :69, Kit §1c)
and `pileHolding_mem` (frozen :493, Kit §1f).  They are CITED
here, never re-landed; this card imports `Orig2.Kit` and nothing
above the shared kit tier (which carries the certified seam).

VISIBILITY (two deliberate lifts, both load-bearing for the
split): the frozen chapter held `wf_pile_found_ne` and
`runOK_head_gt` private.  Both are public here — the
classification card consumes them BY NAME (the found-pin letter
rows; the deck's `runOK_head_lt` alias), so the strike would not
elaborate with them hidden.  Each carries its lift note in place.

Constructivity: the searches carry decidable predicates and the
counts are finite list arithmetic — every row audits
`[propext, Quot.sound]` or fewer; nothing drags
`Classical.choice` (the frozen header's own audit discipline,
carried across).

House compliance: per-row provenance docstrings; private kit for
the chapter's internal contradictions; frozen statements never
force-premised; the battery at the tail; commits staged green,
`lake build Orig2` between batches.
-/

/-! ## The `WF` accessor strip

The four one-liner projections downstream cards quote.  PORTED
verbatim from `Orig/Integrity.lean:49-62`. -/

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

/- `Pile.isEmpty_eq` (frozen `Orig/Integrity.lean:69`) already
lives at `Orig2/Kit.lean` §1c — cited there, not re-landed here. -/

/-! ## Occurrence bookkeeping -/

/-- A pile's whole zone, hidden cards under face-up ones.  (The
frozen file's own note: the public home of the count-kit read,
cited by the frozen `Orig/Canonical.lean`'s private copy.)
PORTED verbatim from `Orig/Integrity.lean:81`. -/
def pileZone (st : State) (a : Anchor) : List Card :=
  (st.piles a).hidden ++ (st.piles a).faceUp

/-- The anchors before `a` in the deal order.  PORTED verbatim
from `Orig/Integrity.lean:85`. -/
def preAnchors : Anchor → List Anchor
  | .p0 => [] | .p1 => [.p0] | .p2 => [.p0, .p1] | .p3 => [.p0, .p1, .p2]
  | .p4 => [.p0, .p1, .p2, .p3] | .p5 => [.p0, .p1, .p2, .p3, .p4]
  | .p6 => [.p0, .p1, .p2, .p3, .p4, .p5]

/-- The anchors after `a` in the deal order.  PORTED verbatim
from `Orig/Integrity.lean:91`. -/
def sufAnchors : Anchor → List Anchor
  | .p0 => [.p1, .p2, .p3, .p4, .p5, .p6] | .p1 => [.p2, .p3, .p4, .p5, .p6]
  | .p2 => [.p3, .p4, .p5, .p6] | .p3 => [.p4, .p5, .p6]
  | .p4 => [.p5, .p6] | .p5 => [.p6] | .p6 => []

/-- The anchor enumeration splits around its own index.  PORTED
verbatim from `Orig/Integrity.lean:96`. -/
theorem anchor_split (a : Anchor) :
    Anchor.all = preAnchors a ++ [a] ++ sufAnchors a := by
  cases a <;> rfl

private theorem anchor_ne_mem {a a' : Anchor} (hne : a' ≠ a) :
    a' ∈ preAnchors a ∨ a' ∈ sufAnchors a := by
  cases a <;> cases a' <;> simp_all [preAnchors, sufAnchors]

/-- Flat map distributes over append.  PORTED verbatim from
`Orig/Integrity.lean:104` (distinct from Kit's §1b `flatMap_cons`,
which unrolls one head). -/
theorem flatMapAppend {α β : Type} (f : α → List β) :
    ∀ (A B : List α), List.flatMap f (A ++ B) = List.flatMap f A ++ List.flatMap f B := by
  intro A
  induction A with
  | nil => intro B; rfl
  | cons x t ih =>
      intro B
      show f x ++ List.flatMap f (t ++ B) = (f x ++ List.flatMap f t) ++ List.flatMap f B
      rw [ih, List.append_assoc]

/-- Two card occurrences in separate flatMap blocks make the count
at least two.  (The frozen file's own note: the public home since
its dedup-collapse wave; the private copies in the frozen
`Orig/Classify.lean` and `Orig/Canonical.lean` cite this row.)
PORTED verbatim from `Orig/Integrity.lean:118`. -/
theorem count_ge_two_of_split {st : State} {c : Card} {A B : List (List Card)}
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

/-- A pile card and a foundation card are two occurrences.  PORTED
verbatim from `Orig/Integrity.lean:173`; VISIBILITY LIFT — private
in the frozen home, public here because the classification card's
found-pin letter rows consume it by name (the strike-then-rewire
split demanded it). -/
theorem wf_pile_found_ne {st : State} {c : Card} {a : Anchor} {s : Suit}
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
foundation.  This is what makes all the later searches unique.
PORTED verbatim from `Orig/Integrity.lean:221`. -/
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
no stock, waste, or foundation card place.  PORTED verbatim from
`Orig/Integrity.lean:245`. -/
theorem mem_faceUp_unique {st : State} {c : Card} {a : Anchor} (hwf : st.WF)
    (hmem : c ∈ (st.piles a).faceUp) :
    ∀ a' ≠ a, c ∉ (st.piles a').faceUp ∧ c ∉ (st.piles a').hidden ∧
      c ∉ st.stock ∧ c ∉ st.waste ∧ ∀ s, c ∉ st.found s := by
  intro a' hne
  obtain ⟨hh, hs, hw, hf⟩ := mem_pile_unique hwf (Or.inr hmem)
  exact ⟨(hh a' hne).2, (hh a' hne).1, hs, hw, hf⟩

/-- A hidden card is in no other pile — face up or hidden — and on
no stock, waste, or foundation card place.  PORTED verbatim from
`Orig/Integrity.lean:255`; NEW to `Orig2` (the classification
card's private copies stopped at the face-up twin). -/
theorem mem_hidden_unique {st : State} {c : Card} {a : Anchor} (hwf : st.WF)
    (hmem : c ∈ (st.piles a).hidden) :
    ∀ a' ≠ a, c ∉ (st.piles a').hidden ∧ c ∉ (st.piles a').faceUp ∧
      c ∉ st.stock ∧ c ∉ st.waste ∧ ∀ s, c ∉ st.found s := by
  intro a' hne
  obtain ⟨hh, hs, hw, hf⟩ := mem_pile_unique hwf (Or.inl hmem)
  exact ⟨(hh a' hne).1, (hh a' hne).2, hs, hw, hf⟩

/-! ## The same-pile and cross-side inversions

`mem_pile_unique` and its two projections exclude a card from
every *other* pile and from the stock, waste, and foundations —
but not from its own pile's other part, and the
foundation/stock/waste sides have no pack of their own.  This
section completes the census inversion so that one membership
anywhere pins the card's location everywhere (NEW to `Orig2` in
full: the classification card's private copies carried none of
it). -/

/-! ### The found-side splits -/

/-- The suits before `s` in enumeration order.  PORTED verbatim
from `Orig/Integrity.lean:279`. -/
def preSuits : Suit → List Suit
  | .spade => []
  | .heart => [.spade]
  | .diamond => [.spade, .heart]
  | .club => [.spade, .heart, .diamond]

/-- The suits after `s` in enumeration order.  PORTED verbatim
from `Orig/Integrity.lean:285`. -/
def sufSuits : Suit → List Suit
  | .spade => [.heart, .diamond, .club]
  | .heart => [.diamond, .club]
  | .diamond => [.club]
  | .club => []

/-- The suit enumeration splits around its own index.  PORTED
verbatim from `Orig/Integrity.lean:292`. -/
theorem suit_split (s : Suit) :
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
`mem_faceUp_unique`).  PORTED verbatim from
`Orig/Integrity.lean:419`; NEW to `Orig2`. -/
theorem mem_faceUp_not_hidden {st : State} {c : Card} {a : Anchor} (hwf : st.WF)
    (h : c ∈ (st.piles a).faceUp) : c ∉ (st.piles a).hidden := by
  intro hcon
  have h1 : st.cardCount c = 1 := hwf.cardCount_eq (Card.mem_universe c)
  have h2 : 2 ≤ st.cardCount c := count_ge_two_pile_self hcon h
  omega

/-- A hidden card never lies in its own pile's face-up run.
PORTED verbatim from `Orig/Integrity.lean:427`; NEW to `Orig2`. -/
theorem mem_hidden_not_faceUp {st : State} {c : Card} {a : Anchor} (hwf : st.WF)
    (h : c ∈ (st.piles a).hidden) : c ∉ (st.piles a).faceUp := by
  intro hcon
  have h1 : st.cardCount c = 1 := hwf.cardCount_eq (Card.mem_universe c)
  have h2 : 2 ≤ st.cardCount c := count_ge_two_pile_self h hcon
  omega

/-- One face-up membership pins the card's location everywhere: no
other pile (either part), not its own pile's hidden cards, not
stocked, not wasted, not on any foundation — the compound form
downstream rows cite in place of a count re-derivation.  PORTED
verbatim from `Orig/Integrity.lean:438`; NEW to `Orig2`. -/
theorem mem_faceUp_only {st : State} {c : Card} {a : Anchor} (hwf : st.WF)
    (h : c ∈ (st.piles a).faceUp) :
    (∀ a' ≠ a, c ∉ (st.piles a').hidden ∧ c ∉ (st.piles a').faceUp) ∧
      c ∉ (st.piles a).hidden ∧ c ∉ st.stock ∧ c ∉ st.waste ∧
      ∀ s, c ∉ st.found s := by
  obtain ⟨hh, hs, hw, hf⟩ := mem_pile_unique hwf (Or.inr h)
  exact ⟨hh, mem_faceUp_not_hidden hwf h, hs, hw, hf⟩

/-- One hidden membership pins the card's location everywhere.
PORTED verbatim from `Orig/Integrity.lean:447`; NEW to `Orig2`. -/
theorem mem_hidden_only {st : State} {c : Card} {a : Anchor} (hwf : st.WF)
    (h : c ∈ (st.piles a).hidden) :
    (∀ a' ≠ a, c ∉ (st.piles a').hidden ∧ c ∉ (st.piles a').faceUp) ∧
      c ∉ (st.piles a).faceUp ∧ c ∉ st.stock ∧ c ∉ st.waste ∧
      ∀ s, c ∉ st.found s := by
  obtain ⟨hh, hs, hw, hf⟩ := mem_pile_unique hwf (Or.inl h)
  exact ⟨hh, mem_hidden_not_faceUp hwf h, hs, hw, hf⟩

/-- A foundation card is nowhere else: in no pile (either part),
not stocked, not wasted, and on no other foundation.  PORTED
verbatim from `Orig/Integrity.lean:457`; NEW to `Orig2`. -/
theorem mem_found_unique {st : State} {c : Card} {s : Suit} (hwf : st.WF)
    (h : c ∈ st.found s) :
    (∀ a, c ∉ (st.piles a).hidden ∧ c ∉ (st.piles a).faceUp) ∧
      c ∉ st.stock ∧ c ∉ st.waste ∧ ∀ s' ≠ s, c ∉ st.found s' := by
  refine ⟨fun a => ⟨fun hcon => wf_pile_found_ne hwf ((List.mem_append).2 (Or.inl hcon)) h,
      fun hcon => wf_pile_found_ne hwf ((List.mem_append).2 (Or.inr hcon)) h⟩,
    fun hcon => wf_found_stock_ne hwf h hcon,
    fun hcon => wf_found_waste_ne hwf h hcon,
    fun s' hne hcon => wf_two_founds_ne hwf h hcon hne⟩

/-- A stock card is nowhere else.  PORTED verbatim from
`Orig/Integrity.lean:468`; NEW to `Orig2`. -/
theorem mem_stock_unique {st : State} {c : Card} (hwf : st.WF)
    (h : c ∈ st.stock) :
    (∀ a, c ∉ (st.piles a).hidden ∧ c ∉ (st.piles a).faceUp) ∧
      c ∉ st.waste ∧ ∀ s, c ∉ st.found s := by
  refine ⟨fun a => ⟨fun hcon => wf_pile_stock_ne hwf ((List.mem_append).2 (Or.inl hcon)) h,
      fun hcon => wf_pile_stock_ne hwf ((List.mem_append).2 (Or.inr hcon)) h⟩,
    fun hcon => wf_stock_waste_ne hwf h hcon,
    fun s hcon => wf_found_stock_ne hwf hcon h⟩

/-- A waste card is nowhere else.  PORTED verbatim from
`Orig/Integrity.lean:478`; NEW to `Orig2`. -/
theorem mem_waste_unique {st : State} {c : Card} (hwf : st.WF)
    (h : c ∈ st.waste) :
    (∀ a, c ∉ (st.piles a).hidden ∧ c ∉ (st.piles a).faceUp) ∧
      c ∉ st.stock ∧ ∀ s, c ∉ st.found s := by
  refine ⟨fun a => ⟨fun hcon => wf_pile_waste_ne hwf ((List.mem_append).2 (Or.inl hcon)) h,
      fun hcon => wf_pile_waste_ne hwf ((List.mem_append).2 (Or.inr hcon)) h⟩,
    fun hcon => wf_stock_waste_ne hwf hcon h,
    fun s hcon => wf_found_waste_ne hwf hcon h⟩

/-! ## `firstWhere` completeness

`pileHolding_mem` (frozen `Orig/Integrity.lean:493`) already lives
at `Orig2/Kit.lean` §1f — cited there, not re-landed here; the
exactness rows below consume it by name. -/

/-! ### The holding search -/

/-- The holding search is exact at `WF` states: it answers `a`
precisely when `c` is face up in pile `a`.  PORTED verbatim from
`Orig/Integrity.lean:499`; NEW to `Orig2`. -/
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

/-- The holding search is deterministic: it names at most one
pile.  PORTED verbatim from `Orig/Integrity.lean:511`; NEW to
`Orig2`. -/
theorem pileHolding_inj {st : State} {c : Card} {a a' : Anchor}
    (h : st.pileHolding c = some a) (h' : st.pileHolding c = some a') : a = a' := by
  rw [h] at h'
  injection h' with h''

namespace Pile

/-- A pile's top is its face-up list's last element.  PORTED
verbatim from `Orig/Integrity.lean:519`. -/
theorem top_eq_lastOf_iff {p : Pile} {c : Card} :
    p.top = some c ↔ ∃ front, p.faceUp = front ++ [c] := by
  constructor
  · intro h
    exact lastOf_eq_snoc (show lastOf p.faceUp = some c from h)
  · rintro ⟨front, hfront⟩
    show lastOf p.faceUp = some c
    rw [hfront]
    exact lastOf_snoc

/-- The top card belongs to the face-up run.  PORTED verbatim from
`Orig/Integrity.lean:530`. -/
theorem mem_of_top {p : Pile} {c : Card} (h : p.top = some c) : c ∈ p.faceUp :=
  lastOf_mem (show lastOf p.faceUp = some c from h)

end Pile

/-! ### The top search -/

/-- The pile-top search's sound reading: a located pile's face-up
run is nonempty and really ends at the searched card.  HOSTED HERE
(2026-10-19, the hoist-below-both-consumers pattern): the frozen
home `Orig/Irreversible.lean:1272` rides above the closed seam;
the classification card's former private twin (its §1m landing)
is STRUCK for this public home (its call sites resolve by name over
its import), and CargoKit's public `tfc_pileOfTop_top` re-evidences
here as an alias, its name kept for the cold consumers' cites
(byte-stability).  The read rides the core's `firstWhere_sound`
alone — the search-integrity card is its natural public home. -/
theorem pileOfTop_top {st : State} {z : Card} {k : Anchor}
    (h : st.pileOfTop z = some k) :
    (st.piles k).faceUp ≠ [] ∧ lastOf (st.piles k).faceUp = some z := by
  have hd := firstWhere_sound (p := fun a => decide (st.topOf a = some z)) h
  have htop : lastOf (st.piles k).faceUp = some z := of_decide_eq_true hd
  constructor
  · intro hc
    rw [hc] at htop
    exact absurd htop (by simp [lastOf])
  · exact htop

/-- The top search is exact at `WF` states: it answers `a`
precisely when `z` is pile `a`'s top card.  PORTED verbatim from
`Orig/Integrity.lean:539`; NEW to `Orig2`. -/
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

/-- The top search is deterministic: it names at most one pile.
PORTED verbatim from `Orig/Integrity.lean:555`; NEW to `Orig2`. -/
theorem pileOfTop_inj {st : State} {z : Card} {a a' : Anchor}
    (h : st.pileOfTop z = some a) (h' : st.pileOfTop z = some a') : a = a' := by
  rw [h] at h'
  injection h' with h''

/-! ## The `runOK` descent kit -/

/-- Every card under a legal run's head sits strictly below the
head in rank.  PORTED verbatim from `Orig/Integrity.lean:565`;
VISIBILITY LIFT — private in the frozen home, public here because
the classification card's deck aliases it (`runOK_head_lt`) and
this card's own public `runOK_desc` / `runOK_nodup` ride it. -/
theorem runOK_head_gt : ∀ {t : List Card} {x y : Card},
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
block.  PORTED verbatim from `Orig/Integrity.lean:584`. -/
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

/-- A legal face-up run holds no card twice.  PORTED verbatim from
`Orig/Integrity.lean:597`; NEW to `Orig2`. -/
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
`c` itself appears.  PORTED verbatim from
`Orig/Integrity.lean:609`. -/
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
`c`.  PORTED verbatim from `Orig/Integrity.lean:632`; NEW to
`Orig2`. -/
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
descends strictly.  PORTED verbatim from
`Orig/Integrity.lean:649`. -/
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

/-- The located `inr`-landing's seat facts, derived from the three
public inputs the undo arms hold anyway: the located pile differs
from the card's own seat, and the card is not in it.  PORTED
verbatim from `Orig/Integrity.lean:678`. -/
theorem canPlace_inr_seat {st : State} {c z : Card} {k a : Anchor}
    (hwf : st.WF) (hh : st.pileHolding c = some a)
    (hcp : st.canPlace c (Sum.inr z) = true)
    (hk₀ : st.pileOfTop z = some k) :
    k ≠ a ∧ c ∉ (st.piles k).faceUp := by
  have hka : k ≠ a := fun hcon =>
    canPlace_inr_target_pile_ne hwf hcp (pileHolding_mem hh)
      (hk₀.trans (congrArg some hcon))
  exact ⟨hka, (mem_faceUp_unique hwf (pileHolding_mem hh) k hka).1⟩

/-- The empty-seat branch never aims at the mover's own pile
either: `canPlace` demands the seat be empty while pile `a` holds
`c` face up.  (WF-free, like the branch's own condition.)  PORTED
verbatim from `Orig/Integrity.lean:691`. -/
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
kill families).  PORTED verbatim from
`Orig/Integrity.lean:707`; NEW to `Orig2`. -/
theorem ne_of_canSitOn {z y : Card} (h : canSitOn z y = true) : z ≠ y := by
  intro hcon
  subst hcon
  simp only [canSitOn_eq] at h
  omega

/-! ## The audit battery

Per promoted head, this card.  Expected profile: `[]`,
`[propext]`, or `[propext, Quot.sound]` — never `sorryAx`, never
`Classical.choice` (the frozen header's own audit discipline). -/

#print axioms State.WF.found_prefix
#print axioms State.WF.runOK_of
#print axioms State.WF.cardCount_eq
#print axioms State.WF.drawStep_pos
#print axioms pileZone
#print axioms preAnchors
#print axioms sufAnchors
#print axioms anchor_split
#print axioms flatMapAppend
#print axioms count_ge_two_of_split
#print axioms wf_pile_found_ne
#print axioms mem_pile_unique
#print axioms mem_faceUp_unique
#print axioms mem_hidden_unique
#print axioms preSuits
#print axioms sufSuits
#print axioms suit_split
#print axioms mem_faceUp_not_hidden
#print axioms mem_hidden_not_faceUp
#print axioms mem_faceUp_only
#print axioms mem_hidden_only
#print axioms mem_found_unique
#print axioms mem_stock_unique
#print axioms mem_waste_unique
#print axioms pileHolding_eq_some_iff
#print axioms pileHolding_inj
#print axioms Pile.top_eq_lastOf_iff
#print axioms Pile.mem_of_top
#print axioms pileOfTop_top
#print axioms pileOfTop_eq_some_iff
#print axioms pileOfTop_inj
#print axioms runOK_head_gt
#print axioms runOK_desc
#print axioms runOK_nodup
#print axioms canPlace_inr_target_off_run
#print axioms canPlace_inr_target_pile_ne
#print axioms canPlace_inr_seat
#print axioms canPlace_inl_target_pile_ne
#print axioms ne_of_canSitOn
