import Orig2.Vocab
import Orig2.Kit

/-!
# Orig2.Classification — THE CLASSIFICATION CARD

THE CARD'S MISSION: at `WF` states the undoability oracle
`reversibleOf` decides the witness carrier `reversibleAtW` EXACTLY,
constructor by constructor, and thereby the program's ONE
reversibility question — does an explicit play return? — is answered
by a Bool.  The card's terminal head, the CLAIM
`reversibleOf_iff_reversibleAtW` (banked at `Orig2/Claims.lean`,
discharged here and promoted on completion), is the positive-side
companion of the retired commit-polarity classification; the
witness-only regime 2026-10-17 retired the semantic pair
(`irreversibleAt`/`reversibleAt`) from the new interface, and this
card speaks the carrier ONLY:

* every head of this card is stated at `reversibleOf ... = true ↔
  reversibleAtW ...` (or the carrier negation `¬ reversibleAtW ...`)
  — never at the retired pair;
* the WF gate is part of each letter's truth: at wild states the
  shape and the carrier diverge in both directions (the frozen
  tier's witness archive holds both corners — the diadem and the
  freezer); no premiseless row is stated anywhere;
* (→) shape-true HANDS the explicit undo play, constructor by
  constructor: the draw's re-deal back; the raise's giveback over
  the chop; the pull's re-raise onto the accepting base; the
  slide's whole-segment relocation; the bare-king vacates;
* (←) shape-false DENIES the witness, intuitionistically, no
  classical step anywhere: the waste rows' cycle-count drop; the
  hidden flip's reveal-arms-never-re-arm; the bare non-king lifts'
  no-redo seat; the draw's pristine/offset commits — each refutes a
  returning play directly.

LINEAGE (the frozen templates this card flips, per case, restated
at the new definitions; never imported): `Orig/Classify.lean`'s
commit-polarity card — `tabToFoundIrr` (:1775) + `tabToFoundClass`
(:1789), `foundToTabIrr` (:1974) + `foundToTabClass` (:1979),
`tabToTabIrr` (:2166) + `tabToTabClass` (:2180), `drawIrr` (:2778)
+ `drawClass` (:2783), the universal waste rows (:1072, :1080), the
bare non-king commitments (:967, :1004), the pass-base round trip
(:1206), the mirror-move undos (:1417, :1653), the lifted witness
heads (:1907, :2101, :2499, :2600), and the assembly
`irreversible_iff_of` (:2866) with its decider rider (:2891).  The
R-shapes (`Orig2/Vocab.lean` §1.6) are the cellwise flips of the
commit-polarity shapes; each row here cites its frozen home and the
flip.

THE SEAM VETO (2026-10-17, recorded at landing): the plan extended
the seam with the game-physics modules (`Orig.Integrity`,
`Orig.Irreversible`, `Orig.Mono`, `Orig.Phase`), but the carrier's
registry ownership structurally blocks it — every physics module
imports `Orig.Fate`, which declares a ROOT-LEVEL
`reversibleAtW` that collides with the registry's verbatim port
(lineage: `Orig/Fate.lean:92` vs `Orig2/Vocab.lean` §1.5; lean
refuses the double load — "already been declared").  So the seam
stays the certified core (`Basic`/`State`/`Play`, as re-tightened
at c82724f) and EVERY needed physics row is re-landed in this card
as per-file private kit — verbatim shape copies with sources
cited, or honest re-statements at the carrier grade — per the
house dedup discipline.  The frozen tier is read freely; nothing
above the core seam is imported.

DE-CHOICE NOTE (carried from the frozen card's own tranche): the
commit-tier's last `Classical.choice` carrier was the
`List.take`-bearing zero cell of the positional kit; this card
ports the explicit-cell de-choice verbatim, and the battery trails
expect `[propext]` / `[propext, Quot.sound]` on every proved head
— `sorryAx` only on unproved stubs (none at completion),
`Classical.choice` NEVER.

House compliance: per-row provenance docstrings; per-letter
sections; the letter-facing kit private to the card, the general
physics rows promoted to the shared `Orig2/Kit.lean` (owner
decree, 2026-10-17); the battery at the file's tail; frozen
statements never force-premised; commits staged green per letter,
`lake build Orig2` between batches.
-/


/-!
## §0–§1K. THE PHYSICS KIT (promoted)

The witness-grade bridge, the run engine, the constructive list
kit, the measures and their step tables, the placement rows, the
step inversions, the phase line, the ONE draw footprint with the
draw round trips, the pristine kit, and the lex kit now live at
`Orig2/Kit.lean` (owner promotion 2026-10-17: one shared copy for
the cards; per-row provenance cites moved with them).  This card
imports that kit and keeps only its letter-facing machinery from
§1A' below.
-/

/-! ### §1a'. The `WF` accessor strip

The four one-liner projections of `State.WF`, PORTED verbatim
from `Orig/Integrity.lean:49-62` (the frozen file rides above the
core seam via `Orig.Fate`, vetoed here).
-/
namespace State

/-- Foundations are prefixes of their build order. -/
private theorem WF.found_prefix {st : State} (h : st.WF) (s : Suit) :
    ∃ n, st.found s = s.upCards.take n := h.1 s

/-- Every pile's face-up run is legal. -/
private theorem WF.runOK_of {st : State} (h : st.WF) (a : Anchor) :
    runOK (st.piles a).faceUp = true := h.2.1 a

/-- Every real card occurs exactly once in the position. -/
private theorem WF.cardCount_eq {st : State} (h : st.WF) {c : Card}
    (hc : c ∈ Card.universe) : st.cardCount c = 1 := h.2.2.1 c hc

/-- The draw step is positive. -/
private theorem WF.drawStep_pos {st : State} (h : st.WF) :
    0 < st.drawStep := h.2.2.2

end State

/-! ### §1l. The count-integrity kit

`Orig.Integrity`'s occurrence bookkeeping and its placement-target
rows, ported reading (the frozen file rides above the core seam):
the pile-zone census splits, the two-occurrence contradiction,
the one-membership universal, the `runOK` descent kit, and the
`canPlace` self-safety family the undo assemblies consume.
-/

/-- A pile's whole zone, hidden cards under face-up ones.  PORTED
verbatim from `Orig/Integrity.lean:81`. -/
private def pileZone (st : State) (a : Anchor) : List Card :=
  (st.piles a).hidden ++ (st.piles a).faceUp

/-- The anchors before `a` in the deal order.  PORTED verbatim
from `Orig/Integrity.lean:85`. -/
private def preAnchors : Anchor → List Anchor
  | .p0 => [] | .p1 => [.p0] | .p2 => [.p0, .p1] | .p3 => [.p0, .p1, .p2]
  | .p4 => [.p0, .p1, .p2, .p3] | .p5 => [.p0, .p1, .p2, .p3, .p4]
  | .p6 => [.p0, .p1, .p2, .p3, .p4, .p5]

/-- The anchors after `a` in the deal order.  PORTED verbatim from
`Orig/Integrity.lean:91`. -/
private def sufAnchors : Anchor → List Anchor
  | .p0 => [.p1, .p2, .p3, .p4, .p5, .p6] | .p1 => [.p2, .p3, .p4, .p5, .p6]
  | .p2 => [.p3, .p4, .p5, .p6] | .p3 => [.p4, .p5, .p6]
  | .p4 => [.p5, .p6] | .p5 => [.p6] | .p6 => []

/-- The anchor enumeration splits around its own index.  PORTED
verbatim from `Orig/Integrity.lean:96`. -/
private theorem anchor_split (a : Anchor) :
    Anchor.all = preAnchors a ++ [a] ++ sufAnchors a := by
  cases a <;> rfl

/-- PORTED verbatim from `Orig/Integrity.lean:100`. -/
private theorem anchor_ne_mem {a a' : Anchor} (hne : a' ≠ a) :
    a' ∈ preAnchors a ∨ a' ∈ sufAnchors a := by
  cases a <;> cases a' <;> simp_all [preAnchors, sufAnchors]

/-- PORTED verbatim from `Orig/Integrity.lean:104`. -/
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
at least two.  PORTED verbatim from `Orig/Integrity.lean:118`. -/
private theorem count_ge_two_of_split {st : State} {c : Card} {A B : List (List Card)}
    (hsplit : st.zones = A ++ B) (hl : c ∈ A.flatMap id) (hr : c ∈ B.flatMap id) :
    2 ≤ st.cardCount c := by
  show 2 ≤ ((st.zones.flatMap id).filter fun x => decide (x = c)).length
  rw [hsplit, flatMapAppend, List.filter_append, List.length_append]
  have hL := count_filter_pos hl
  have hR := count_filter_pos hr
  omega

/-- PORTED verbatim from `Orig/Integrity.lean:127`. -/
private theorem zone_mem_map {st : State} {zs : List Anchor} {a : Anchor}
    (h : a ∈ zs) : pileZone st a ∈ zs.map (pileZone st) :=
  List.mem_map.2 ⟨a, h, rfl⟩

/-- PORTED verbatim from `Orig/Integrity.lean:131`. -/
private theorem found_mem_map {st : State} {ss : List Suit} {s : Suit}
    (h : s ∈ ss) : st.found s ∈ ss.map st.found :=
  List.mem_map.2 ⟨s, h, rfl⟩

/-- PORTED verbatim from `Orig/Integrity.lean:135`. -/
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

/-- PORTED verbatim from `Orig/Integrity.lean:146`. -/
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

/-- PORTED verbatim from `Orig/Integrity.lean:157`. -/
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

/-- PORTED verbatim from `Orig/Integrity.lean:173`. -/
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

/-- PORTED verbatim from `Orig/Integrity.lean:185`. -/
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

/-- PORTED verbatim from `Orig/Integrity.lean:199`. -/
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

/-- The one general occurrence fact: a card in pile `a` — hidden
or face up — is nowhere else in a `WF` state.  PORTED verbatim
from `Orig/Integrity.lean:221`. -/
private theorem mem_pile_unique {st : State} {c : Card} {a : Anchor} (hwf : st.WF)
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

/-- A face-up card is in no other pile — face up or hidden — and
on no stock, waste, or foundation card place.  PORTED verbatim
from `Orig/Integrity.lean:245`. -/
private theorem mem_faceUp_unique {st : State} {c : Card} {a : Anchor} (hwf : st.WF)
    (hmem : c ∈ (st.piles a).faceUp) :
    ∀ a' ≠ a, c ∉ (st.piles a').faceUp ∧ c ∉ (st.piles a').hidden ∧
      c ∉ st.stock ∧ c ∉ st.waste ∧ ∀ s, c ∉ st.found s := by
  intro a' hne
  obtain ⟨hh, hs, hw, hf⟩ := mem_pile_unique hwf (Or.inr hmem)
  exact ⟨(hh a' hne).2, (hh a' hne).1, hs, hw, hf⟩

/-- Every card under a legal run's head sits strictly below the
head in rank.  PORTED verbatim from `Orig/Integrity.lean:565`. -/
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

/-- Strict rank descent, block form.  PORTED verbatim from
`Orig/Integrity.lean:584`. -/
private theorem runOK_desc : ∀ {P S : List Card} {x y : Card},
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

/-- A pile's top is its face-up list's last element, as a snoc.
PORTED verbatim from `Orig/Integrity.lean:519`. -/
private theorem Pile.top_eq_lastOf_iff {p : Pile} {c : Card} :
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
private theorem Pile.mem_of_top {p : Pile} {c : Card} (h : p.top = some c) :
    c ∈ p.faceUp :=
  lastOf_mem (show lastOf p.faceUp = some c from h)

/-- The empty-seat branch never aims at the mover's own pile.  PORTED
verbatim from `Orig/Integrity.lean:691`. -/
private theorem canPlace_inl_target_pile_ne {st : State} {c : Card} {a b : Anchor}
    (hcp : st.canPlace c (Sum.inl b) = true) (hmem : c ∈ (st.piles a).faceUp) :
    b ≠ a := by
  intro hcon
  subst hcon
  simp only [State.canPlace, Bool.and_eq_true] at hcp
  obtain ⟨hempty, -⟩ := hcp
  obtain ⟨-, hfu⟩ := (Pile.isEmpty_eq _).mp hempty
  rw [hfu] at hmem
  exact absurd hmem (by simp)

/-- The pile `z` tops is never the pile the mover `c` comes from.
PORTED verbatim from `Orig/Integrity.lean:649`. -/
private theorem canPlace_inr_target_pile_ne {st : State} {c z : Card} {a : Anchor}
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

/-- The located `inr`-landing's seat facts.  PORTED verbatim from
`Orig/Integrity.lean:678`. -/
private theorem canPlace_inr_seat {st : State} {c z : Card} {k a : Anchor}
    (hwf : st.WF) (hh : st.pileHolding c = some a)
    (hcp : st.canPlace c (Sum.inr z) = true)
    (hk₀ : st.pileOfTop z = some k) :
    k ≠ a ∧ c ∉ (st.piles k).faceUp := by
  have hka : k ≠ a := fun hcon =>
    canPlace_inr_target_pile_ne hwf hcp (pileHolding_mem hh)
      (hk₀.trans (congrArg some hcon))
  exact ⟨hka, (mem_faceUp_unique hwf (pileHolding_mem hh) k hka).1⟩

/-! ### §1m. The constructive undos, tabToFound pair

`Orig.Irreversible`'s two raise-undo arms, ported in full (the
frozen file rides above the core seam): the under-seat giveback
over the chop, and the bare-king vacate onto the emptied seat.
-/

/-- The pile-top search's sound reading: a located pile's face-up
run is nonempty and really ends at the searched card.  PORTED
verbatim from `Orig/Irreversible.lean:1272`. -/
private theorem pileOfTop_top {st : State} {z : Card} {k : Anchor}
    (h : st.pileOfTop z = some k) :
    (st.piles k).faceUp ≠ [] ∧ lastOf (st.piles k).faceUp = some z := by
  have hd := firstWhere_sound (p := fun a => decide (st.topOf a = some z)) h
  have htop : lastOf (st.piles k).faceUp = some z := of_decide_eq_true hd
  constructor
  · intro hc
    rw [hc] at htop
    exact absurd htop (by simp [lastOf])
  · exact htop

/-- The pile-level no-reveal-empty round trip.  PORTED verbatim
from `Orig/Irreversible.lean:1469`. -/
private theorem afterRunRemoved_empty_eq : ∀ (p : Pile), p.hidden = [] →
    Pile.afterRunRemoved p ([] : List Card) = ⟨[], []⟩
  | ⟨[], pf⟩, _ => rfl
  | ⟨x :: xs, pf⟩, hhd => absurd hhd (by simp)

/-- A placement onto an empty seat, as one state update.  PORTED
verbatim from `Orig/Irreversible.lean:1299`. -/
private theorem putCard_inl_eq_setPile {st : State} {c : Card} {a : Anchor} :
    st.putCard c (Sum.inl a) =
      { st with piles := fun a' => if a' = a then ⟨[], [c]⟩ else st.piles a' } := by
  show (st.setPile a ⟨[], [c]⟩) = _
  rfl

/-- A placement onto a located card base, as one state update.
PORTED verbatim from `Orig/Irreversible.lean:1308`. -/
private theorem putCard_inr_eq_setPile {st : State} {c : Card} {z : Card} {k : Anchor}
    (hz : st.pileOfTop z = some k) :
    st.putCard c (Sum.inr z) =
      { st with piles := fun a' =>
          if a' = k then { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }
          else st.piles a' } := by
  simp only [State.putCard, hz]
  rfl

/-- **The under-seat `.tabToFound` undo, witness form (primary).**  A
successful no-reveal `.tabToFound` whose source pile keeps a
face-up card below the moved one is undone by `.foundToTab c
(Sum.inr z)` onto `z`'s pile.  PORTED verbatim from
`Orig/Irreversible.lean:1491`; the frozen statement concludes the
frozen twin of the carrier — this port's statement is the
registry's own constant (the same body, the § header's seam veto).
-/
private theorem tabToFound_undo_under {st : State} {c : Card} {a : Anchor} {z : Card}
    {s₁ : State}
    (hstep : State.step st (Move.tabToFound c) = some s₁)
    (hpa : st.pileOfTop c = some a)
    (hz : lastOf (chop (st.piles a).faceUp) = some z)
    (hsit : canSitOn c z = true)
    (hsearch : s₁.pileOfTop z = some a) :
    reversibleAtW st (Move.tabToFound c) := by
  obtain ⟨-, a₀, hpa₀, hs₁⟩ := step_tabToFound_inv hstep
  rw [hpa] at hpa₀
  injection hpa₀ with haa
  subst haa
  obtain ⟨-, hlastc⟩ := pileOfTop_top hpa
  have hfull : (st.piles a).faceUp = chop (st.piles a).faceUp ++ [c] := lastOf_chop hlastc
  obtain ⟨hs₁found, hs₁other, hft⟩ := tabToFound_found_trio hs₁

  have hcp : s₁.canPlace c (Sum.inr z) = true := by
    simp only [State.canPlace, hsearch]
    exact hsit
  refine ⟨s₁, [Move.foundToTab c (Sum.inr z)], hstep, ?_⟩
  have hstep2 : State.step s₁ (Move.foundToTab c (Sum.inr z)) = some st := by
    simp only [State.step, hft]
    rw [hcp]
    refine congrArg some (?_ :
      (s₁.setFound c.suit (chop (s₁.found c.suit))).putCard c (Sum.inr z) = st)
    have hz'' : (s₁.setFound c.suit (chop (s₁.found c.suit))).pileOfTop z = some a := hsearch
    rw [putCard_inr_eq_setPile hz'']
    refine State.ext (funext fun σ => ?_) (funext fun a'' => ?_) ?_ ?_ ?_
    · show (if σ = c.suit then chop (s₁.found c.suit) else s₁.found σ) = st.found σ
      by_cases hσ : σ = c.suit
      · rw [hσ, ite_eq_left rfl, hs₁found, chop_snoc]
      · rw [ite_eq_right hσ]
        exact hs₁other σ hσ
    · show (if a'' = a then
          { (s₁.setFound c.suit (chop (s₁.found c.suit))).piles a with
            faceUp := ((s₁.setFound c.suit (chop (s₁.found c.suit))).piles a).faceUp ++ [c] }
          else (s₁.setFound c.suit (chop (s₁.found c.suit))).piles a'') = st.piles a''
      have hQeq : (s₁.setFound c.suit (chop (s₁.found c.suit))).piles = s₁.piles := rfl
      rw [hQeq]
      by_cases ha'' : a'' = a
      · rw [ha'', ite_eq_left rfl]
        have hpla : s₁.piles a =
            Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp) := by
          rw [hs₁]
          show (if a = a then
              Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
              else st.piles a) = _
          rw [ite_eq_left rfl]
        rw [hpla]
        cases hc : chop (st.piles a).faceUp with
        | nil =>
            rw [hc] at hz
            exact absurd hz (by simp [lastOf])
        | cons y ys =>
            rw [hc] at hfull
            show (⟨(st.piles a).hidden, (y :: ys) ++ [c]⟩ : Pile) = st.piles a
            exact Pile.ext rfl hfull.symm
      · rw [ite_eq_right ha'']
        rw [hs₁]
        show (if a'' = a then
            Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
            else st.piles a'') = st.piles a''
        rw [ite_eq_right ha'']
    · show s₁.stock = st.stock
      rw [hs₁]
      rfl
    · show s₁.waste = st.waste
      rw [hs₁]
      rfl
    · show s₁.drawStep = st.drawStep
      rw [hs₁]
      rfl
  simp only [State.run, hstep2]

/-- **The bare `.tabToFound` undo, witness form (primary).**  A
successful no-reveal `.tabToFound` whose source pile empties
completely is undone by `.foundToTab c (Sum.inl a)` onto the
now-empty original seat.  PORTED verbatim from
`Orig/Irreversible.lean:1583`; carrier note as above. -/
private theorem tabToFound_undo_bare {st : State} {c : Card} {a : Anchor} {s₁ : State}
    (hstep : State.step st (Move.tabToFound c) = some s₁)
    (hpa : st.pileOfTop c = some a)
    (hchop : chop (st.piles a).faceUp = [])
    (hhidden : (st.piles a).hidden = [])
    (hking : c.rank = Rank.king) :
    reversibleAtW st (Move.tabToFound c) := by
  obtain ⟨-, a₀, hpa₀, hs₁⟩ := step_tabToFound_inv hstep
  rw [hpa] at hpa₀
  injection hpa₀ with haa
  subst haa
  obtain ⟨hs₁found, hs₁other, hft⟩ := tabToFound_found_trio hs₁

  have hface : (st.piles a).faceUp = [c] := by
    obtain ⟨-, hlastc⟩ := pileOfTop_top hpa
    have hc0 : (st.piles a).faceUp = chop (st.piles a).faceUp ++ [c] := lastOf_chop hlastc
    rw [hchop, List.nil_append] at hc0
    exact hc0
  have hpla : s₁.piles a = ⟨[], []⟩ := by
    rw [hs₁]
    show (if a = a then
        Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
        else st.piles a) = _
    rw [ite_eq_left rfl, hchop]
    exact afterRunRemoved_empty_eq _ hhidden
  have hcp : s₁.canPlace c (Sum.inl a) = true := by
    show ((s₁.piles a).isEmpty && decide (c.rank = Rank.king)) = true
    rw [hpla, decide_eq_true hking]
    rfl
  refine ⟨s₁, [Move.foundToTab c (Sum.inl a)], hstep, ?_⟩
  have hstep2 : State.step s₁ (Move.foundToTab c (Sum.inl a)) = some st := by
    simp only [State.step, hft]
    rw [hcp]
    refine congrArg some (?_ :
      (s₁.setFound c.suit (chop (s₁.found c.suit))).putCard c (Sum.inl a) = st)
    rw [putCard_inl_eq_setPile]
    refine State.ext (funext fun σ => ?_) (funext fun a'' => ?_) ?_ ?_ ?_
    · show (if σ = c.suit then chop (s₁.found c.suit) else s₁.found σ) = st.found σ
      by_cases hσ : σ = c.suit
      · rw [hσ, ite_eq_left rfl, hs₁found, chop_snoc]
      · rw [ite_eq_right hσ]
        exact hs₁other σ hσ
    · show (if a'' = a then (⟨[], [c]⟩ : Pile)
          else (s₁.setFound c.suit (chop (s₁.found c.suit))).piles a'') = st.piles a''
      by_cases ha'' : a'' = a
      · rw [ha'', ite_eq_left rfl]
        show (⟨[], [c]⟩ : Pile) = ⟨(st.piles a).hidden, (st.piles a).faceUp⟩
        rw [hhidden, hface]
      · rw [ite_eq_right ha'']
        show s₁.piles a'' = st.piles a''
        rw [hs₁]
        show (if a'' = a then
            Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
            else st.piles a'') = st.piles a''
        rw [ite_eq_right ha'']
    · show s₁.stock = st.stock
      rw [hs₁]
      rfl
    · show s₁.waste = st.waste
      rw [hs₁]
      rfl
    · show s₁.drawStep = st.drawStep
      rw [hs₁]
      rfl
  simp only [State.run, hstep2]

/-! ### §1n. The list & run mini kit

The frozen classification card's own private list and `runOK`
helpers (`Orig/Classify.lean`'s §small kit), ported reading.
-/

/-- Every nonempty list has a last element.  PORTED verbatim from
`Orig/Classify.lean:202`. -/
private theorem lastOf_cons_some : ∀ (l : List Card) (x : Card),
    ∃ z, lastOf (x :: l) = some z := by
  intro l
  induction l with
  | nil => intro x; exact ⟨x, rfl⟩
  | cons y t _ih => intro x; exact _ih y

/-- Every element of `chop` is an element of the list.  PORTED
verbatim from `Orig/Classify.lean:220`. -/
private theorem chop_mem {l : List Card} {x : Card} (h : x ∈ chop l) : x ∈ l := by
  induction l with
  | nil => cases h
  | cons y t ih =>
      cases t with
      | nil => cases h
      | cons w t' =>
          have h' : x ∈ y :: chop (w :: t') := h
          rcases List.mem_cons.1 h' with hxy | hrest
          · exact List.mem_cons.2 (Or.inl hxy)
          · exact List.mem_cons.2 (Or.inr (ih hrest))

/-- The run `fromCard c l`, when nonempty, starts at `c`.  PORTED
verbatim from `Orig/Classify.lean:263`. -/
private theorem fromCard_head {c : Card} : ∀ {l : List Card} {r : List Card},
    fromCard c l = r → r ≠ [] → ∃ t, r = c :: t := by
  intro l
  induction l with
  | nil =>
      intro r hr hne
      rw [fromCard] at hr
      exact absurd hr.symm hne
  | cons y t ih =>
      intro r hr hne
      rw [fromCard] at hr
      split at hr
      · rename_i hyc
        subst hr
        rw [hyc]
        exact ⟨t, rfl⟩
      · exact ih hr hne

/-- Every suffix of a legal run is legal — the left-degradation of
`runOK` under append.  PORTED verbatim from
`Orig/Classify.lean:378`. -/
private theorem runOK_append_left : ∀ (A B : List Card),
    runOK (A ++ B) = true → runOK B = true := by
  intro A
  induction A with
  | nil => intro B h; exact h
  | cons y t ih =>
      intro B h
      exact ih B (runOK_cons_tail h)

/-- Every prefix of a legal run is legal.  PORTED verbatim from
`Orig/Classify.lean:392`. -/
private theorem runOK_append_right : ∀ (A B : List Card),
    runOK (A ++ B) = true → runOK A = true := by
  intro A
  induction A with
  | nil => intro _ _; rfl
  | cons y t ih =>
      intro B h
      match t with
      | [] => rfl
      | w :: t' =>
          have h' : runOK (y :: w :: (t' ++ B)) = true := h
          rw [runOK, Bool.and_eq_true] at h' ⊢
          exact ⟨h'.1, ih B h'.2⟩

/-- In a legal run, every tail card sits strictly below the head in
rank.  PORTED verbatim from `Orig/Classify.lean:409`. -/
private theorem runOK_head_lt : ∀ {t : List Card} {x y : Card},
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

/-- The seam fit: in a legal face-up run, each card fits on its
immediate predecessor, anywhere in the list.  PORTED verbatim from
`Orig/Classify.lean:427`. -/
private theorem runOK_seam : ∀ (A B : List Card) {x c : Card},
    runOK (A ++ x :: c :: B) = true → canSitOn c x = true := by
  intro A
  induction A with
  | nil =>
      intro B x c h
      rw [List.nil_append, runOK, Bool.and_eq_true] at h
      exact h.1
  | cons y t ih =>
      intro B x c h
      exact ih B (runOK_cons_tail h)

/-- A list with a known last element keeps that element adjacent
to the snocced cards.  PORTED verbatim from
`Orig/Classify.lean:442`. -/
private theorem runOK_adjacent_snoc {P : List Card} {z c : Card}
    (hlast : lastOf P = some z) (hok : runOK (P ++ [c]) = true) :
    canSitOn c z = true := by
  have hc1 : P ++ [c] = (chop P ++ [z]) ++ [c] :=
    congrArg (· ++ [c]) (lastOf_chop hlast)
  have hc2 : (chop P ++ [z]) ++ [c] = chop P ++ [z, c] := by
    rw [List.append_assoc]
    rfl
  rw [hc1.trans hc2] at hok
  exact runOK_seam _ _ hok

/-- The removal-with-remainder writes the remainder as the face-up
run.  PORTED verbatim from `Orig/Classify.lean:778`. -/
private theorem afterRunRemoved_faceUp_ne {p : Pile} {pre : List Card} (h : pre ≠ []) :
    (Pile.afterRunRemoved p pre).faceUp = pre := by
  cases pre with
  | nil => exact absurd rfl h
  | cons w t => rfl

/-- With no hidden cards, removing the whole face-up run empties the
pile outright (no reveal fires).  PORTED verbatim from
`Orig/Classify.lean:786`. -/
private theorem afterRunRemoved_faceUp_empty_self {p : Pile} (hhd : p.hidden = []) :
    Pile.afterRunRemoved p [] = { p with faceUp := ([] : List Card) } := by
  rcases p with ⟨hlist, flist⟩
  cases hlist with
  | nil => rfl
  | cons h t => exact absurd hhd (by simp)

/-! ### §1o. The king-anchored pile invariant

The bare-king discipline (a pile with no hidden cards whose
face-up content, when present, is king-anchored) and its
preservation along every legal move — the no-redo-seat argument
behind the bare non-king commitments.  PORTED reading from
`Orig/Classify.lean:742-944`.
-/

/-- The face-up content is empty or anchored by a king at the
bottom.  PORTED verbatim from `Orig/Classify.lean:742`. -/
private def KingHead : List Card → Prop
  | [] => True
  | x :: _ => x.rank = Rank.king

/-- A pile with no hidden cards whose face-up content, when present,
is king-anchored.  PORTED verbatim from `Orig/Classify.lean:749`.
-/
private def BareKing (p : Pile) : Prop :=
  p.hidden = [] ∧ KingHead p.faceUp

/-- PORTED verbatim from `Orig/Classify.lean:752`. -/
private theorem kingHead_append {l r : List Card} (hl : l ≠ []) (h : KingHead l) :
    KingHead (l ++ r) := by
  obtain ⟨x, t, hc⟩ := list_cons_of_ne_nil hl
  subst hc
  exact h

/-- PORTED verbatim from `Orig/Classify.lean:758`. -/
private theorem kingHead_chop {l : List Card} (h : KingHead l) : KingHead (chop l) := by
  cases l with
  | nil => exact True.intro
  | cons x t =>
      cases t with
      | nil => exact True.intro
      | cons y t' => exact h

/-- PORTED verbatim from `Orig/Classify.lean:766`. -/
private theorem kingHead_below {c : Card} {l : List Card} (h : KingHead l) :
    KingHead (below c l) := by
  cases l with
  | nil => exact True.intro
  | cons x t =>
      rw [below]
      split
      · exact True.intro
      · exact h

/-- The one-card placement respects the invariant of an
already-bare pile.  PORTED verbatim from
`Orig/Classify.lean:795`. -/
private theorem bare_king_putCard {s : State} {c : Card} {b : Base} (a : Anchor)
    (hcp : s.canPlace c b = true)
    (hhd : (s.piles a).hidden = []) (hkh : KingHead (s.piles a).faceUp) :
    BareKing ((s.putCard c b).piles a) := by
  cases b with
  | inl k =>
      rw [putCard_piles_inl]
      show BareKing (if a = k then (⟨[], [c]⟩ : Pile) else s.piles a)
      by_cases hak : a = k
      · rw [ite_eq_left hak]
        obtain ⟨-, hking⟩ := canPlace_inl hcp
        exact ⟨rfl, hking⟩
      · rw [ite_eq_right hak]
        exact ⟨hhd, hkh⟩
  | inr z =>
      obtain ⟨j, hz, -⟩ := canPlace_inr hcp
      rw [putCard_piles_inr _ _ _ _ hz]
      show BareKing (if a = j then
          { s.piles j with faceUp := (s.piles j).faceUp ++ [c] } else s.piles a)
      by_cases hak : a = j
      · rw [ite_eq_left hak]
        obtain ⟨hf, -⟩ := pileOfTop_top hz
        have hkhj : KingHead (s.piles j).faceUp := by rw [← hak]; exact hkh
        have hhdj : (s.piles j).hidden = [] := by rw [← hak]; exact hhd
        exact ⟨hhdj, kingHead_append hf hkhj⟩
      · rw [ite_eq_right hak]
        exact ⟨hhd, hkh⟩

/-- Every legal single move preserves the bare-king discipline of
any one pile.  PORTED verbatim from `Orig/Classify.lean:828`. -/
private theorem bare_king_step : ∀ {s s' : State} {m : Move},
    State.step s m = some s' → ∀ (a : Anchor),
    BareKing (s.piles a) → BareKing (s'.piles a) := by
  intro s s' m hstep a ⟨hhd, hkh⟩
  match m with
  | .draw =>
      have hp := stepDraw_piles hstep
      rw [hp]
      exact ⟨hhd, hkh⟩
  | .wasteToFound c =>
      obtain ⟨-, x, xs, -, hs⟩ := step_wasteToFound_inv hstep
      rw [hs]
      exact ⟨hhd, hkh⟩
  | .wasteToTab c b =>
      obtain ⟨hg, x, xs, -, hs⟩ := step_wasteToTab_inv hstep
      rw [Bool.and_eq_true] at hg
      rw [hs]
      rw [show (({ s.putCard c b with waste := xs } : State).piles) a
          = (s.putCard c b).piles a from rfl]
      exact bare_king_putCard a hg.2 hhd hkh
  | .foundToTab c b =>
      obtain ⟨c', ht, hce, hcp, hs⟩ := step_foundToTab_inv hstep
      rw [hs]
      exact bare_king_putCard a hcp hhd hkh
  | .tabToFound c =>
      obtain ⟨-, a₀, hp, hs⟩ := step_tabToFound_inv hstep
      rw [hs]
      show BareKing
          ((fun a' =>
            if a' = a₀ then Pile.afterRunRemoved (s.piles a₀) (chop (s.piles a₀).faceUp)
            else s.piles a') a)
      show BareKing (if a = a₀ then
          Pile.afterRunRemoved (s.piles a₀) (chop (s.piles a₀).faceUp) else s.piles a)
      by_cases ha : a = a₀
      · rw [ite_eq_left ha]
        rw [ha] at hhd hkh
        rcases afterRunRemoved_hidden (s.piles a₀) (chop (s.piles a₀).faceUp) with
          ⟨hpre, hhidx⟩ | ⟨he, hhdd, hhidx⟩ | ⟨he, hhn, -⟩
        · show
            (Pile.afterRunRemoved (s.piles a₀) (chop (s.piles a₀).faceUp)).hidden = [] ∧
              KingHead (Pile.afterRunRemoved (s.piles a₀) (chop (s.piles a₀).faceUp)).faceUp
          refine ⟨?_, ?_⟩
          · rw [show (Pile.afterRunRemoved (s.piles a₀) (chop (s.piles a₀).faceUp)).hidden
                = (s.piles a₀).hidden from hhidx]
            exact hhd
          · rw [afterRunRemoved_faceUp_ne hpre]
            exact kingHead_chop hkh
        · rw [he, afterRunRemoved_faceUp_empty_self hhdd]
          exact ⟨hhdd, True.intro⟩
        · exact absurd hhd hhn
      · rw [ite_eq_right ha]
        exact ⟨hhd, hkh⟩
  | .tabToTab c b =>
      obtain ⟨a₀, hh, hcp, hne, hs⟩ := step_tabToTab_inv hstep
      rw [hs]
      have hmidfact : BareKing
          ((s.setPile a₀
              (Pile.afterRunRemoved (s.piles a₀) (below c (s.piles a₀).faceUp))).piles a) := by
        by_cases ha : a = a₀
        · rw [ha] at hhd hkh
          rw [ha]
          rw [setPile_afterRunRemoved_piles_self]
          rcases afterRunRemoved_hidden (s.piles a₀) (below c (s.piles a₀).faceUp) with
            ⟨hpre, hhidx⟩ | ⟨he, hhdd, hhidx⟩ | ⟨he, hhn, -⟩
          · show
              (Pile.afterRunRemoved (s.piles a₀) (below c (s.piles a₀).faceUp)).hidden = [] ∧
                KingHead (Pile.afterRunRemoved (s.piles a₀) (below c (s.piles a₀).faceUp)).faceUp
            refine ⟨?_, ?_⟩
            · rw [show (Pile.afterRunRemoved (s.piles a₀)
                    (below c (s.piles a₀).faceUp)).hidden = (s.piles a₀).hidden from hhidx]
              exact hhd
            · rw [afterRunRemoved_faceUp_ne hpre]
              exact kingHead_below hkh
          · rw [he, afterRunRemoved_faceUp_empty_self hhdd]
            exact ⟨hhdd, True.intro⟩
          · exact absurd hhd hhn
        · rw [setPile_afterRunRemoved_piles_ne _ _ _ _ ha]
          exact ⟨hhd, hkh⟩
      obtain ⟨ttr, hrt⟩ := fromCard_head rfl hne
      cases b with
      | inl k =>
          by_cases hak : a = k
          · rw [hak, putRun_piles_inl_self, hrt]
            obtain ⟨-, hking⟩ := canPlace_inl hcp
            exact ⟨rfl, hking⟩
          · rw [putRun_piles_inl_ne _ _ _ _ hak]
            exact hmidfact
      | inr z =>
          cases hz : (s.setPile a₀
              (Pile.afterRunRemoved (s.piles a₀) (below c (s.piles a₀).faceUp))).pileOfTop z with
          | none =>
              rw [putRun_inr_none hz]
              exact hmidfact
          | some j =>
              by_cases hak : a = j
              · rw [hak, putRun_piles_inr_self _ _ _ _ hz]
                obtain ⟨hfa, -⟩ := pileOfTop_top hz
                rw [hak] at hmidfact
                obtain ⟨hhdj, hkhj⟩ := hmidfact
                exact ⟨hhdj, kingHead_append hfa hkhj⟩
              · rw [putRun_piles_inr_ne _ _ _ _ hz hak]
                exact hmidfact

/-- The invariant rides along arbitrary plays.  PORTED from
`Orig/Classify.lean:932` (the run engine). -/
private theorem bare_king_run (play : List Move) (s w : State) (a : Anchor)
    (h : BareKing (s.piles a)) (hrun : s.run play = some w) : BareKing (w.piles a) :=
  run_rec (fun x y => BareKing (x.piles a) → BareKing (y.piles a))
    (fun hstep _ ih hb => ih (bare_king_step hstep a hb))
    (fun _ hb => hb) hrun h

/-! ### §1p. The search pins

The successor-side search re-pins: the classification's own grind
kit from `Orig/Classify.lean` (topPin at :667; the WF fact
`wf_no_other_top` at :731), ported reading.
-/

/-- The top search re-pins to the one changed pile.  PORTED
verbatim from `Orig/Classify.lean:667`. -/
private theorem topPin {st s₁ : State} {a : Anchor} {z : Card}
    (hothers : ∀ a', a' ≠ a → s₁.piles a' = st.piles a')
    (htop : (s₁.piles a).top = some z)
    (hnost : ∀ a', a' ≠ a → (st.piles a').top ≠ some z) :
    s₁.pileOfTop z = some a := by
  show firstWhere (fun a' => decide ((s₁.piles a').top = some z)) Anchor.all = some a
  refine firstWhere_find (Anchor.mem_all a) (decide_eq_true htop) ?_
  intro y hy hyne
  have he : (s₁.piles y).top = (st.piles y).top := by rw [hothers y hyne]
  rw [he]
  exact decide_false_of_not (hnost y hyne)

/-- The WF fact behind the pile-side `hnost` premises: a card
face-up in one pile tops no other pile.  PORTED verbatim from
`Orig/Classify.lean:731`. -/
private theorem wf_no_other_top {st : State} {c : Card} {a : Anchor}
    (hwf : st.WF) (hmem : c ∈ (st.piles a).faceUp) (a' : Anchor) (hne : a' ≠ a) :
    (st.piles a').top ≠ some c := by
  intro htop
  have := Pile.mem_of_top htop
  exact (mem_faceUp_unique hwf hmem a' hne).1 this

/-! ### §1q. The tabToFound step guards

PORTED verbatim reading from `Orig/Classify.lean:1747-1767`.
-/

/-- A refused `.tabToFound` next-up guard makes the move vacuous.
PORTED verbatim from `Orig/Classify.lean:1747`. -/
private theorem step_tabToFound_none_of_nextUp {st : State} {c : Card}
    (h : st.nextUp c = false) : State.step st (Move.tabToFound c) = none := by
  simp only [State.step, h]
  rfl

/-- A refused `.tabToFound` seat search makes the move vacuous.
PORTED verbatim from `Orig/Classify.lean:1752`. -/
private theorem step_tabToFound_none_of_pileOfTop {st : State} {c : Card}
    (hn : st.nextUp c = true) (h : st.pileOfTop c = none) :
    State.step st (Move.tabToFound c) = none := by
  simp only [State.step, hn, h]
  rfl

/-- A passing `.tabToFound` guard produces the recorded successor.
PORTED verbatim from `Orig/Classify.lean:1759`. -/
private theorem step_tabToFound_some {st : State} {c : Card} {a : Anchor}
    (hn : st.nextUp c = true) (ha : st.pileOfTop c = some a) :
    ∃ s₁, State.step st (Move.tabToFound c) = some s₁ := by
  refine ⟨{ st.setFound c.suit (st.found c.suit ++ [c]) with
    piles := fun a' =>
      if a' = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
      else st.piles a' }, ?_⟩
  simp only [State.step, hn, ha]
  rfl

/-! ### §1r. The found-position kit and the pull mirror

`orig/Classify.lean`'s positional kit (foundations end at their
rank index — the private `Rk` tabulation lifted from the frozen
`Orig/FoundKit.lean:371`, which itself rides above the seam via
`Combine`) plus the found-vs-pile occurrence survey, and
`Orig/Irreversible.lean`'s `foundToTab` mirror (the pile-level
round trip, the re-raise assembly, the undo), ported reading.
-/

/-- The list-length take fact.  PORTED from
`Orig/Classify.lean:495` (core re-provenance:
`List.length_take`). -/
private theorem take_length_min {α : Type} (l : List α) : ∀ (n : Nat),
    (l.take n).length = min n l.length := fun _ => List.length_take

/-- Taking no deeper than an earlier take reaches the same prefix.
PORTED from `Orig/Classify.lean:521` (core re-provenance:
`List.take_take`; the tranche's de-choice note stands). -/
private theorem take_take_le {α : Type} (l : List α) : ∀ (m n : Nat), m ≤ n →
    (l.take n).take m = l.take m := by
  intro m n h
  rw [List.take_take, Nat.min_eq_left h]

/-- Taking to a list's own length is the identity.  PORTED from
`Orig/Classify.lean:537`. -/
private theorem take_length_self {α : Type} (l : List α) : l.take l.length = l :=
  take_ge_length l l.length (Nat.le_refl _)

/-- Mapping commutes with dropping.  PORTED verbatim from
`Orig/Classify.lean:545`. -/
private theorem drop_map_min {α β : Type} (f : α → β) : ∀ (l : List α) (i : Nat),
    (l.map f).drop i = (l.drop i).map f := by
  intro l
  induction l with
  | nil =>
      intro i
      cases i <;> rfl
  | cons x t ih =>
      intro i
      match i with
      | 0 => rfl
      | i' + 1 => exact ih i'

/-- The rank of a zero-based index, tabulated.  PORTED verbatim
from `Orig/FoundKit.lean:371` (the frozen public home of the
retired per-file makers — the macro tier, not importable here;
lifted reading). -/
private def Rk : Nat → Rank
  | 0 => .ace | 1 => .two | 2 => .three | 3 => .four | 4 => .five | 5 => .six
  | 6 => .seven | 7 => .eight | 8 => .nine | 9 => .ten | 10 => .jack | 11 => .queen
  | 12 => .king | _ => .ace

/-- The tabulation inverts the rank index.  PORTED from
`Orig/FoundKit.lean:376`. -/
private theorem Rk_toIdx : ∀ (k : Nat), k < 13 → (Rk k).toIdx = k := by
  intro k hk
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _
  | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ => rfl
  | j + 13, hj => exact absurd hj (by omega)

/-- PORTED from `Orig/Classify.lean:558`. -/
private theorem rank_all_drop_cons : ∀ (k : Nat), k < 13 →
    Rank.all.drop k = Rk k :: Rank.all.drop (k + 1) := by
  intro k hk
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _
  | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ => rfl
  | j + 13, hj => exact absurd hj (by omega)

/-- The suits' up-card lists drop by cons, kernel-computed.  PORTED
verbatim from `Orig/Classify.lean:578`. -/
private theorem upCards_drop_cons (s : Suit) : ∀ (k : Nat), k < 13 →
    s.upCards.drop k = Card.mk s (Rk k) :: s.upCards.drop (k + 1) := by
  intro k hk
  have hd := rank_all_drop_cons k hk
  show (Rank.all.map (Card.mk s)).drop k
      = Card.mk s (Rk k) :: (Rank.all.map (Card.mk s)).drop (k + 1)
  have hrw2 : (Rank.all.map (Card.mk s)).drop (k + 1)
      = (Rank.all.drop (k + 1)).map (Card.mk s) :=
    drop_map_min (Card.mk s) Rank.all (k + 1)
  rw [drop_map_min, hrw2, hd]
  rfl

/-- The head of a nonempty list never hides in `lastOf`: the tail
is the last element's.  PORTED verbatim from
`orig/Classify.lean:195`. -/
private theorem lastOf_cons_of_ne {x : Card} {l : List Card} (h : l ≠ []) :
    lastOf (x :: l) = lastOf l := by
  obtain ⟨y, t, hc⟩ := list_cons_of_ne_nil h
  subst hc
  rfl

/-- A take of the up-card list, taken `n` deep from offset `k`,
ends at index `k + n - 1`.  PORTED verbatim from
`Orig/Classify.lean:592`. -/
private theorem upCards_last_of_take (s : Suit) : ∀ (n k : Nat), n + k ≤ 13 → 0 < n →
    lastOf ((s.upCards.drop k).take n) = some (Card.mk s (Rk (k + n - 1))) := by
  intro n
  induction n with
  | zero => intro k _ hn; omega
  | succ m ih =>
      intro k hle _hm
      have hk : k < 13 := by omega
      rw [upCards_drop_cons s k hk]
      match m with
      | 0 => rfl
      | m' + 1 =>
          have hih := ih (k + 1) (by omega) (by omega)
          have hne : (s.upCards.drop (k + 1)).take (m' + 1) ≠ [] := by
            intro hc
            have hlt := take_length_min ((s.upCards.drop (k + 1))) (m' + 1)
            rw [hc, List.length_nil] at hlt
            have hd := List.length_drop (l := s.upCards) (i := k + 1)
            have h13 : s.upCards.length = 13 := Suit.upCards_length s
            omega
          show lastOf (Card.mk s (Rk k) :: (s.upCards.drop (k + 1)).take (m' + 1)) =
            some (Card.mk s (Rk (k + (m' + 1 + 1) - 1)))
          rw [lastOf_cons_of_ne hne, hih]
          refine congrArg (fun q => some (Card.mk s (Rk q))) (by omega)

/-- The WF foundation arithmetic: a foundation's chop length is the
rank index of its top card.  PORTED verbatim from
`Orig/Classify.lean:621` (the frozen card's own public row). -/
private theorem wf_found_chop_toIdx {st : State} {s : Suit} {c : Card}
    (hwf : st.WF) (htop : st.foundTop s = some c) :
    (chop (st.found s)).length = c.rank.toIdx := by
  obtain ⟨n, hn⟩ := hwf.found_prefix s
  have hlast : lastOf (st.found s) = some c := htop
  have hne : st.found s ≠ [] := by
    intro hc
    rw [hc] at hlast
    exact absurd hlast (by simp [lastOf])
  have hpos : 0 < (st.found s).length := by
    obtain ⟨w0, xs, hcon⟩ := list_cons_of_ne_nil hne
    rw [hcon, List.length_cons]
    omega
  have hup : (Suit.upCards s).length = 13 := Suit.upCards_length s
  have h13 : (st.found s).length ≤ 13 := by
    rw [hn, take_length_min]
    omega
  have hN : st.found s = s.upCards.take ((st.found s).length) := by
    rw [hn]
    have htt := take_take_le (Suit.upCards s) ((s.upCards.take n).length) n
      (by rw [take_length_min]; omega)
    have hlself := take_length_self (s.upCards.take n)
    rw [htt] at hlself
    exact hlself.symm
  have hz := upCards_last_of_take s ((st.found s).length) 0 (by omega) (by omega)
  rw [List.drop_zero, Nat.zero_add] at hz
  rw [← hN] at hz
  have hEq : some c = some (Card.mk s (Rk ((st.found s).length - 1))) :=
    hlast.symm.trans hz
  injection hEq with hRk
  have hcl : (chop (st.found s)).length + 1 = (st.found s).length := by
    have hlc := congrArg List.length (lastOf_chop hlast)
    rw [List.length_append] at hlc
    have h1 : ([c] : List Card).length = 1 := rfl
    omega
  rw [hRk]
  show (chop (st.found s)).length = (Rk ((st.found s).length - 1)).toIdx
  rw [Rk_toIdx ((st.found s).length - 1) (by omega)]
  omega

/-- One pile's whole zone (the private reshaping).  PORTED
verbatim from `Orig/Classify.lean:459`. -/
private def pileZoneC (st : State) (a : Anchor) : List Card :=
  (st.piles a).hidden ++ (st.piles a).faceUp

/-- A WF state never holds a foundation card in a pile.  PORTED
verbatim from `Orig/Classify.lean:465`. -/
private theorem wf_found_not_in_pile {st : State} {c : Card} {a : Anchor} {σ : Suit}
    (hwf : st.WF) (hf : c ∈ st.found σ) (hp : c ∈ (st.piles a).hidden ∨ c ∈ (st.piles a).faceUp) :
    False := by
  have hcount : st.cardCount c = 1 := hwf.cardCount_eq (Card.mem_universe c)
  have hsplit : st.zones =
      (Suit.all.map st.found) ++
        ((Anchor.all.map (fun a' => pileZoneC st a')) ++ [st.stock, st.waste]) := rfl
  have hl : c ∈ (Suit.all.map st.found).flatMap id :=
    (List.mem_flatMap).2 ⟨st.found σ, List.mem_map.2 ⟨σ, Suit.mem_all σ, rfl⟩, hf⟩
  have hz : c ∈ pileZoneC st a := by
    rcases hp with h | h
    · exact (List.mem_append).2 (Or.inl h)
    · exact (List.mem_append).2 (Or.inr h)
  have hr : c ∈ ((Anchor.all.map (fun a' => pileZoneC st a')) ++ [st.stock, st.waste]).flatMap id :=
    (List.mem_flatMap).2 ⟨pileZoneC st a,
      (List.mem_append).2 (Or.inl (List.mem_map.2 ⟨a, Anchor.mem_all a, rfl⟩)), hz⟩
  have h2 : 2 ≤ st.cardCount c := count_ge_two_of_split hsplit hl hr
  omega

/-- A WF state's foundation top is no pile's top.  PORTED verbatim
from `Orig/Classify.lean:486`. -/
private theorem wf_found_not_pileTop {st : State} {c : Card} {a : Anchor} {σ : Suit}
    (hwf : st.WF) (hf : lastOf (st.found σ) = some c) : (st.piles a).top ≠ some c := by
  intro htop
  have hmem : c ∈ (st.piles a).faceUp := Pile.mem_of_top htop
  exact wf_found_not_in_pile hwf (lastOf_mem hf) (Or.inr hmem)

/-- The pile-level round trip of a card-on-card placement.  PORTED
verbatim from `Orig/Irreversible.lean:1287`. -/
private theorem putCard_inr_roundtrip (p : Pile) (c : Card) (hf : p.faceUp ≠ []) :
    Pile.afterRunRemoved { p with faceUp := p.faceUp ++ [c] } (chop (p.faceUp ++ [c])) = p := by
  rw [chop_snoc]
  cases hp : p.faceUp with
  | nil => exact absurd hp hf
  | cons x xs =>
      show ({ p with faceUp := x :: xs } : Pile) = p
      exact Pile.ext rfl hp.symm

/-- The state-level round trip behind the pull undo.  PORTED
verbatim from `Orig/Irreversible.lean:1323`; the frozen statement
concludes the frozen twin of the carrier — this port's statement
is the registry's own constant. -/
private theorem foundToTab_rtp {st : State} {c : Card} {b : Base} {s₁ : State} {k : Anchor}
    (hstep : State.step st (Move.foundToTab c b) = some s₁)
    (hidx : (chop (st.found c.suit)).length = c.rank.toIdx)
    (hfound : s₁.found c.suit = chop (st.found c.suit))
    (hotherfound : ∀ σ, σ ≠ c.suit → s₁.found σ = st.found σ)
    (hsearch : s₁.pileOfTop c = some k)
    (hkrest : Pile.afterRunRemoved (s₁.piles k) (chop (s₁.piles k).faceUp) = st.piles k)
    (hzkeep : ∀ a', a' ≠ k → s₁.piles a' = st.piles a')
    (hkeep : s₁.stock = st.stock ∧ s₁.waste = st.waste ∧ s₁.drawStep = st.drawStep) :
    reversibleAtW st (Move.foundToTab c b) := by
  obtain ⟨c', htop, hc'c, -, hs⟩ := step_foundToTab_inv hstep
  have hF : st.found c.suit = chop (st.found c.suit) ++ [c] := by
    have h2 : st.foundTop c.suit = some c := by rw [htop, hc'c]
    exact lastOf_chop h2
  have hnextup : s₁.nextUp c = true := by
    show decide (c.rank.toIdx = (s₁.found c.suit).length) = true
    rw [hfound, hidx]
    exact decide_eq_true rfl
  refine ⟨s₁, [Move.tabToFound c], hstep, ?_⟩
  have hstep2 : State.step s₁ (Move.tabToFound c) = some st := by
    show (if s₁.nextUp c = true then
        (match s₁.pileOfTop c with
        | none => none
        | some a =>
            (some { s₁.setFound c.suit (s₁.found c.suit ++ [c]) with
                     piles := fun a' =>
                       if a' = a then Pile.afterRunRemoved (s₁.piles a) (chop (s₁.piles a).faceUp)
                       else s₁.piles a' } : Option State))
        else none) = some st
    rw [hnextup, hsearch]
    refine congrArg some (?_ :
      { s₁.setFound c.suit (s₁.found c.suit ++ [c]) with
        piles := fun a' =>
          if a' = k then Pile.afterRunRemoved (s₁.piles k) (chop (s₁.piles k).faceUp)
          else s₁.piles a' } = st)
    refine State.ext (funext fun σ => ?_) (funext fun a' => ?_) ?_ ?_ ?_
    · show (if σ = c.suit then s₁.found c.suit ++ [c] else s₁.found σ) = st.found σ
      by_cases hσ : σ = c.suit
      · rw [hσ, ite_eq_left rfl, hfound, ← hF]
      · rw [ite_eq_right hσ]
        exact hotherfound σ hσ
    · show (if a' = k then Pile.afterRunRemoved (s₁.piles k) (chop (s₁.piles k).faceUp)
          else s₁.piles a') = st.piles a'
      by_cases ha' : a' = k
      · rw [ha', ite_eq_left rfl]
        exact hkrest
      · rw [ite_eq_right ha']
        exact hzkeep a' ha'
    · show (s₁.setFound c.suit (s₁.found c.suit ++ [c])).stock = st.stock
      rw [setFound_stock]
      exact hkeep.1
    · show (s₁.setFound c.suit (s₁.found c.suit ++ [c])).waste = st.waste
      rw [setFound_waste]
      exact hkeep.2.1
    · show (s₁.setFound c.suit (s₁.found c.suit ++ [c])).drawStep = st.drawStep
      rw [setFound_drawStep]
      exact hkeep.2.2
  simp only [State.run, hstep2]

/-- **The `.foundToTab` undo, witness form (primary).**  A
successful `Move.foundToTab c b` is undone by `Move.tabToFound c`
of the same card, returning to the origin in one move.  PORTED
verbatim from `Orig/Irreversible.lean:1400`; carrier note as
above. -/
private theorem foundToTab_undo {st : State} {c : Card} {b : Base} {s₁ : State} {k : Anchor}
    (h : State.step st (Move.foundToTab c b) = some s₁)
    (hnext : (chop (st.found c.suit)).length = c.rank.toIdx)
    (hsearch : s₁.pileOfTop c = some k)
    (hseat : b = Sum.inl k ∨ ∃ z, b = Sum.inr z ∧ st.pileOfTop z = some k) :
    reversibleAtW st (Move.foundToTab c b) := by
  obtain ⟨c', htop, hc'c, hcp, hs⟩ := step_foundToTab_inv h
  have hkeep : s₁.stock = st.stock ∧ s₁.waste = st.waste ∧ s₁.drawStep = st.drawStep := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hs, putCard_stock, setFound_stock]
    · rw [hs, putCard_waste, setFound_waste]
    · rw [hs, putCard_drawStep, setFound_drawStep]
  have hs₁found : s₁.found c.suit = chop (st.found c.suit) := by
    rw [hs, putCard_found]
    exact setFound_found_self
  have hs₁other : ∀ σ, σ ≠ c.suit → s₁.found σ = st.found σ := by
    intro σ hσ
    rw [hs, putCard_found]
    exact setFound_found_ne hσ
  rcases hseat with hb | ⟨z, hb, hz⟩
  · subst hb
    obtain ⟨hemp, -⟩ := canPlace_inl hcp
    obtain ⟨hhd, hfu⟩ := (Pile.isEmpty_eq _).mp hemp
    have hPk : s₁.piles k = ⟨[], [c]⟩ := by
      rw [hs]
      simp only [putCard_piles_inl]
      rw [ite_true]
    have hzkeep : ∀ a', a' ≠ k → s₁.piles a' = st.piles a' := by
      intro a' hne
      rw [hs]
      simp only [putCard_piles_inl]
      rw [ite_eq_right hne, setFound_piles]
    exact foundToTab_rtp h hnext hs₁found hs₁other hsearch
      (by
        rw [hPk]
        show (⟨[], []⟩ : Pile) = st.piles k
        exact Pile.ext hhd.symm hfu.symm)
      hzkeep hkeep
  · subst hb
    obtain ⟨hfne, -⟩ := pileOfTop_top hz
    have hz' : (st.setFound c.suit (chop (st.found c.suit))).pileOfTop z = some k := hz
    have hPk : s₁.piles k = { st.piles k with faceUp := (st.piles k).faceUp ++ [c] } := by
      rw [hs]
      simp only [putCard_piles_inr _ _ _ _ hz']
      rw [setFound_piles, ite_true]
    have hzkeep : ∀ a', a' ≠ k → s₁.piles a' = st.piles a' := by
      intro a' hne
      rw [hs]
      simp only [putCard_piles_inr _ _ _ _ hz']
      rw [ite_eq_right hne, setFound_piles]
    exact foundToTab_rtp h hnext hs₁found hs₁other hsearch
      (by
        rw [hPk]
        exact putCard_inr_roundtrip _ c hfne)
      hzkeep hkeep

/-! ### §1s. The foundToTab step guards

PORTED verbatim reading from `Orig/Classify.lean:1954-1967`.
-/

/-- A refused `.foundToTab` guard makes the move vacuous.  PORTED
verbatim from `Orig/Classify.lean:1954`. -/
private theorem step_foundToTab_none {st : State} {c' c : Card} {b : Base}
    (htop : st.foundTop c.suit = some c')
    (hcond : ((decide (c' = c) && st.canPlace c b) = true) → False) :
    State.step st (Move.foundToTab c b) = none := by
  simp only [State.step, htop]
  rw [ite_eq_right hcond]

/-- A passing `.foundToTab` guard produces the recorded successor.
PORTED verbatim from `Orig/Classify.lean:1962`. -/
private theorem step_foundToTab_legal {st : State} {c : Card} {b : Base}
    (htop : st.foundTop c.suit = some c) (hcp : st.canPlace c b = true) :
    ∃ s₁, State.step st (Move.foundToTab c b) = some s₁ := by
  refine ⟨((st.setFound c.suit (chop (st.found c.suit))).putCard c b), ?_⟩
  simp only [State.step, htop, hcp]
  rfl

/-! ### §1t. The mirror-move kit

The `.tabToTab` slide's own apparatus, ported reading: the
below/run split kit and the step guards (`orig/Classify.lean`
privates at :233-:360, :1264-:1278), the whole-segment
relocation round trips (`tabToTab_bare_rtp` at :1297 and
`tabToTab_under_rtp` at :1498 with their two undos at :1417 and
:1653), and the two-exception search pins (`topPin2` at :682,
`holdingPin2` at :713).
-/

/-- Every element of `below c` is an element.  PORTED verbatim from
`Orig/Classify.lean:233`. -/
private theorem below_mem {c : Card} : ∀ {l : List Card} {x : Card},
    x ∈ below c l → x ∈ l := by
  intro l
  induction l with
  | nil => intro x h; cases h
  | cons y t ih =>
      intro x h
      rw [below] at h
      split at h
      · cases h
      · rcases List.mem_cons.1 h with rfl | hm
        · exact List.mem_cons.2 (Or.inl rfl)
        · exact List.mem_cons.2 (Or.inr (ih hm))

/-- A card present in a list has a nonempty run from it.  PORTED
verbatim from `Orig/Classify.lean:360`. -/
private theorem fromCard_ne_of_mem {c : Card} : ∀ {l : List Card},
    c ∈ l → fromCard c l ≠ [] := by
  intro l
  induction l with
  | nil => intro hmem; cases hmem
  | cons y t ih =>
      intro hmem
      rw [fromCard]
      split
      · exact List.cons_ne_nil _ _
      · rename_i hy
        rcases List.mem_cons.1 hmem with heq | hta
        · exact absurd heq.symm hy
        · exact ih hta

/-- The below-part and the run from `c` reassemble the list.
PORTED verbatim from `Orig/Classify.lean:282`. -/
private theorem below_join {c : Card} : ∀ (l : List Card),
    below c l ++ fromCard c l = l := by
  intro l
  induction l with
  | nil => rfl
  | cons y t ih =>
      rw [below, fromCard]
      split
      · rfl
      · rw [List.cons_append, ih]

/-- `c` never lies strictly below itself.  PORTED verbatim from
`Orig/Classify.lean:294`. -/
private theorem below_not_mem_self {c : Card} : ∀ (l : List Card), c ∉ below c l := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons y t ih =>
      rw [below]
      split
      · intro h; cases h
      · rename_i hy
        intro h
        rcases List.mem_cons.1 h with hyc | hm
        · exact absurd hyc.symm hy
        · exact ih hm

/-- With `c` absent from a prefix, below and fromCard only look
past it.  PORTED verbatim from `Orig/Classify.lean:310`. -/
private theorem below_fromCard_excl {c : Card} : ∀ (X l : List Card), c ∉ X →
    below c (X ++ l) = X ++ below c l ∧ fromCard c (X ++ l) = fromCard c l := by
  intro X
  induction X with
  | nil => intro l _; exact ⟨rfl, rfl⟩
  | cons y t ih =>
      intro l hc
      have hy : y ≠ c := fun heq => hc (List.mem_cons.2 (Or.inl heq.symm))
      have hcT : c ∉ t := fun hm => hc (List.mem_cons.2 (Or.inr hm))
      constructor
      · show below c (y :: (t ++ l)) = y :: (t ++ below c l)
        rw [below, ite_eq_right hy]
        exact congrArg (y :: ·) (ih l hcT).1
      · show fromCard c (y :: (t ++ l)) = fromCard c l
        rw [fromCard, ite_eq_right hy]
        exact (ih l hcT).2

/-- The below-part of a run that starts at `c` is empty.  PORTED
verbatim from `Orig/Classify.lean:354`. -/
private theorem below_head_eq {c : Card} {t : List Card} :
    below c (c :: t) = [] := by
  rw [below, ite_eq_left rfl]

/-- The removal over the empty below-part with no hidden cards
empties the pile outright.  PORTED verbatim from
`Orig/Classify.lean:1255`. -/
private theorem afterRunRemoved_empty_eq' {p : Pile} {z : Card}
    (h : below z p.faceUp = []) (hh : p.hidden = []) :
    Pile.afterRunRemoved p (below z p.faceUp) = ⟨[], []⟩ := by
  rw [h, afterRunRemoved_empty_eq p hh]

/-- A self-located top search is impossible on an empty pile.
PORTED verbatim from `Orig/Classify.lean:947`. -/
private theorem pileOfTop_ne_of_empty {st : State} {a : Anchor}
    (hE : st.piles a = ⟨[], ([] : List Card)⟩) (z : Card) :
    st.pileOfTop z ≠ some a := by
  intro hloc
  obtain ⟨hfa, -⟩ := pileOfTop_top hloc
  rw [hE] at hfa
  exact absurd rfl hfa

/-- `setPile` read at its own pile.  PORTED verbatim from
`Orig/Classify.lean:956`. -/
private theorem setPile_piles_self_any {st : State} {a : Anchor} {p : Pile} :
    (st.setPile a p).piles a = p := by
  show (if a = a then p else st.piles a) = p
  rw [ite_eq_left rfl]

/-- The top pin with two exception piles.  PORTED verbatim from
`Orig/Classify.lean:682`. -/
private theorem topPin2 {st s₁ : State} {a k : Anchor} {z : Card}
    (htop : (s₁.piles a).top = some z)
    (hothers : ∀ a', a' ≠ a → a' ≠ k → s₁.piles a' = st.piles a')
    (hknot : (s₁.piles k).top ≠ some z)
    (hno : ∀ a', a' ≠ a → a' ≠ k → (st.piles a').top ≠ some z) :
    s₁.pileOfTop z = some a := by
  show firstWhere (fun a' => decide ((s₁.piles a').top = some z)) Anchor.all = some a
  refine firstWhere_find (Anchor.mem_all a) (decide_eq_true htop) ?_
  intro y hy hyne
  by_cases hyk : y = k
  · rw [hyk]
    exact decide_false_of_not hknot
  · have he : (s₁.piles y).top = (st.piles y).top := by rw [hothers y hyne hyk]
    rw [he]
    exact decide_false_of_not (hno y hyne hyk)

/-- The holding pin with two exception piles.  PORTED verbatim
from `Orig/Classify.lean:713`. -/
private theorem holdingPin2 {st s₁ : State} {k a : Anchor} {c : Card}
    (ha : c ∉ (s₁.piles a).faceUp)
    (hothers : ∀ a', a' ≠ k → a' ≠ a → s₁.piles a' = st.piles a')
    (hholds : c ∈ (s₁.piles k).faceUp)
    (hno : ∀ a', a' ≠ k → a' ≠ a → c ∉ (st.piles a').faceUp) :
    s₁.pileHolding c = some k := by
  show firstWhere (fun a' => decide (c ∈ (s₁.piles a').faceUp)) Anchor.all = some k
  refine firstWhere_find (Anchor.mem_all k) (decide_eq_true hholds) ?_
  intro y hy hyne
  by_cases hya : y = a
  · rw [hya]
    exact decide_false_of_not ha
  · have he : (s₁.piles y).faceUp = (st.piles y).faceUp := by rw [hothers y hyne hya]
    rw [he]
    exact decide_false_of_not (hno y hyne hya)

/-- A refused `.tabToTab` head search makes the move vacuous.
PORTED verbatim from `Orig/Classify.lean:1264`. -/
private theorem step_tabToTab_none_of_holding {st : State} {c : Card} {b : Base}
    (h : st.pileHolding c = none) : State.step st (Move.tabToTab c b) = none := by
  simp only [State.step, h]

/-- A refused placement guard makes the move vacuous.  PORTED
verbatim from `Orig/Classify.lean:1269`. -/
private theorem step_tabToTab_none_of_cp {st : State} {c : Card} {b : Base} {a : Anchor}
    (hh : st.pileHolding c = some a) (h : st.canPlace c b = false) :
    State.step st (Move.tabToTab c b) = none := by
  simp only [State.step, hh]
  rw [ite_eq_right (fun hcond => by rw [h] at hcond; exact Bool.noConfusion hcond)]

/-- A passing `.tabToTab` guard produces the recorded successor
(the run from the head card is nonempty because the head is
present).  PORTED verbatim from `Orig/Classify.lean:1278`. -/
private theorem step_tabToTab_some {st : State} {c : Card} {b : Base} {a : Anchor}
    (hh : st.pileHolding c = some a) (hcp : st.canPlace c b = true) :
    ∃ s₁, State.step st (Move.tabToTab c b) = some s₁ := by
  have hmem : c ∈ (st.piles a).faceUp := pileHolding_mem hh
  have hne : fromCard c (st.piles a).faceUp ≠ [] := fromCard_ne_of_mem hmem
  refine ⟨(st.setPile a
      (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
    (fromCard c (st.piles a).faceUp) b, ?_⟩
  simp only [State.step, hh, hcp]
  cases hList : fromCard c (st.piles a).faceUp with
  | nil => exact absurd hList hne
  | cons w r => rfl

/-- **The bare-king slide's whole-segment relocation round trip.**
PORTED verbatim from `Orig/Classify.lean:1297`
(`tabToTab_bare_rtp`); the frozen statement concludes `s₁.run
[Move.tabToTab c (Sum.inl a)] = some st`, restated here as such (the
witness assembly wraps it into the carrier). -/
private theorem tabToTab_bare_rtp {st : State} {c : Card} {b : Base} {a k : Anchor}
    {tr : List Card} {s₁ : State}
    (hs₁ : s₁ = (st.setPile a ⟨[], ([] : List Card)⟩).putRun
      (fromCard c (st.piles a).faceUp) b)
    (hrt : fromCard c (st.piles a).faceUp = c :: tr)
    (hface : (st.piles a).faceUp = c :: tr)
    (hhidden : (st.piles a).hidden = [])
    (hking : c.rank = Rank.king)
    (hhold : s₁.pileHolding c = some k)
    (hs₁A : s₁.piles a = ⟨[], ([] : List Card)⟩)
    (hs₁K : s₁.piles k = ⟨(st.piles k).hidden,
      (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp⟩)
    (hkeep : ∀ y, y ≠ a → y ≠ k → s₁.piles y = st.piles y)
    (hcN : c ∉ (st.piles k).faceUp)
    (hka : k ≠ a)
    (hKE : (st.piles k).faceUp = [] → (st.piles k).hidden = []) :
    s₁.run [Move.tabToTab c (Sum.inl a)] = some st := by
  -- successor accessor facts
  have hsF : ∀ σ, s₁.found σ = st.found σ := by
    intro σ
    rw [hs₁, putRun_found, setPile_found]
  have hsS : s₁.stock = st.stock := by rw [hs₁, putRun_stock, setPile_stock]
  have hsW : s₁.waste = st.waste := by rw [hs₁, putRun_waste, setPile_waste]
  have hsD : s₁.drawStep = st.drawStep := by
    rw [hs₁, putRun_drawStep, setPile_drawStep]
  -- the landing pile read, as the mirror needs it
  have hKfaceUp : (s₁.piles k).faceUp =
      (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp :=
    congrArg (fun p => p.faceUp) hs₁K
  have hKhidden : (s₁.piles k).hidden = (st.piles k).hidden :=
    congrArg (fun p => p.hidden) hs₁K
  have hexcl := below_fromCard_excl (c := c) ((st.piles k).faceUp)
    (fromCard c (st.piles a).faceUp) hcN
  have hbelowK : below c (s₁.piles k).faceUp = (st.piles k).faceUp := by
    have h1 : below c (s₁.piles k).faceUp
        = below c ((st.piles k).faceUp ++ fromCard c (st.piles a).faceUp) := by
      rw [hKfaceUp]
    rw [h1, hexcl.1, hrt, below_head_eq, List.append_nil]
  have hrunK : fromCard c (s₁.piles k).faceUp = c :: tr := by
    have h1 : fromCard c (s₁.piles k).faceUp
        = fromCard c ((st.piles k).faceUp ++ fromCard c (st.piles a).faceUp) := by
      rw [hKfaceUp]
    rw [h1, hexcl.2, hrt, fromCard_head_eq]
  have hcp1 : s₁.canPlace c (Sum.inl a) = true := by
    show ((s₁.piles a).isEmpty && decide (c.rank = Rank.king)) = true
    rw [hs₁A, decide_eq_true hking]
    rfl
  have hstep2 : State.step s₁ (Move.tabToTab c (Sum.inl a)) = some st := by
    simp only [State.step, hhold, hcp1, hrunK]
    refine congrArg some (?_ :
      (s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
          (below c (s₁.piles k).faceUp))).putRun (c :: tr) (Sum.inl a) = st)
    rw [show (s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
        (below c (s₁.piles k).faceUp))).putRun (c :: tr) (Sum.inl a)
        = (s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
            (below c (s₁.piles k).faceUp))).setPile a
            ⟨[], c :: tr⟩ from rfl]
    refine State.ext (funext fun σ => ?_) (funext fun y => ?_) ?_ ?_ ?_
    · rw [setPile_found, setPile_found, hsF σ]
    · by_cases hya : y = a
      · rw [hya]
        show (if a = a then ⟨[], c :: tr⟩
          else (if a = k then
              Pile.afterRunRemoved (s₁.piles k) (below c (s₁.piles k).faceUp)
            else s₁.piles a)) = st.piles a
        rw [ite_eq_left rfl]
        refine Pile.ext ?_ ?_
        · rw [hhidden]
        · rw [hface]
      · by_cases hyk : y = k
        · rw [hyk]
          show (if k = a then ⟨[], c :: tr⟩
            else (if k = k then
                Pile.afterRunRemoved (s₁.piles k) (below c (s₁.piles k).faceUp)
              else s₁.piles k)) = st.piles k
          rw [ite_eq_right hka, ite_eq_left rfl, hbelowK]
          cases hF2 : (st.piles k).faceUp with
          | nil =>
              rw [afterRunRemoved_empty_eq _ (hKhidden.trans (hKE hF2))]
              exact Pile.ext (hKE hF2).symm hF2.symm
          | cons w r₂ =>
              exact Pile.ext hKhidden hF2.symm
        · show (if y = a then ⟨[], c :: tr⟩
            else (if y = k then
                Pile.afterRunRemoved (s₁.piles k) (below c (s₁.piles k).faceUp)
              else s₁.piles y)) = st.piles y
          rw [ite_eq_right hya, ite_eq_right hyk]
          exact hkeep y hya hyk
    · exact hsS
    · exact hsW
    · exact hsD
  simp only [State.run, hstep2]

/-- **The bare `.tabToTab` undo, witness form (primary).**  A
successful `.tabToTab` that empties its source pile outright is
undone by the mirror move: run back onto the emptied seat.  PORTED
verbatim from `Orig/Classify.lean:1417`; the frozen statement
concludes the frozen twin of the carrier — this port's statement
is the registry's own constant. -/
private theorem tabToTab_undo_bare {st : State} {c : Card} {b : Base} {a k : Anchor}
    {s₁ : State}
    (hstep : State.step st (Move.tabToTab c b) = some s₁)
    (hh : st.pileHolding c = some a)
    (hpre : below c (st.piles a).faceUp = [])
    (hhidden : (st.piles a).hidden = [])
    (hking : c.rank = Rank.king)
    (hhold : s₁.pileHolding c = some k)
    (hseat : b = Sum.inl k ∨ ∃ z', b = Sum.inr z' ∧
      (st.setPile a ⟨[], ([] : List Card)⟩ : State).pileOfTop z' = some k)
    (hkeep : ∀ y, y ≠ a → y ≠ k → s₁.piles y = st.piles y)
    (hcN : c ∉ (st.piles k).faceUp) :
    reversibleAtW st (Move.tabToTab c b) := by
  obtain ⟨a₀, hh₀, hcp, hfr, hs₁⟩ := step_tabToTab_inv hstep
  rw [hh] at hh₀
  injection hh₀ with haa
  subst haa
  obtain ⟨tr, hrt⟩ := fromCard_head rfl hfr
  have hface : (st.piles a).faceUp = c :: tr := by
    have hj := below_join (c := c) ((st.piles a).faceUp)
    rw [hpre, List.nil_append] at hj
    rw [← hj, hrt]
  have hka : k ≠ a := fun hcon => hcN (by rw [hcon]; exact pileHolding_mem hh)
  -- the emptied source pile, as a literal
  have haremf : Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp) =
      ⟨[], ([] : List Card)⟩ := by
    rw [hpre]
    exact afterRunRemoved_empty_eq _ hhidden
  rw [haremf] at hs₁
  have hmidK : (st.setPile a ⟨[], ([] : List Card)⟩ : State).piles k = st.piles k :=
    setPile_piles_ne hka
  have hs₁A : s₁.piles a = ⟨[], ([] : List Card)⟩ := by
    rw [hs₁]
    rcases hseat with rfl | ⟨z', rfl, hmidPin⟩
    · rw [putRun_piles_inl_ne _ _ _ _ (Ne.symm hka),
        setPile_piles_self]
    · rw [putRun_piles_inr_ne _ _ _ _ hmidPin (Ne.symm hka),
        setPile_piles_self]
  have hs₁K : s₁.piles k = ⟨(st.piles k).hidden,
      (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp⟩ := by
    rcases hseat with rfl | ⟨z', rfl, hmidPin⟩
    · rw [hs₁, putRun_piles_inl_self]
      obtain ⟨hhE, hfE⟩ := (Pile.isEmpty_eq _).mp (canPlace_inl hcp).1
      refine Pile.ext ?_ ?_
      · rw [hhE]
      · rw [hfE, List.nil_append]
    · rw [hs₁, putRun_piles_inr_self _ _ _ _ hmidPin, hmidK]
  have hKE : (st.piles k).faceUp = [] → (st.piles k).hidden = [] := by
    rcases hseat with rfl | ⟨z', rfl, hmidPin⟩
    · intro _
      exact (Pile.isEmpty_eq _).mp (canPlace_inl hcp).1 |>.1
    · intro hcon
      have hne := (pileOfTop_top hmidPin).1
      rw [hmidK] at hne
      exact absurd hcon hne
  exact ⟨s₁, [Move.tabToTab c (Sum.inl a)], hstep,
    tabToTab_bare_rtp hs₁ hrt hface hhidden hking hhold hs₁A hs₁K hkeep hcN hka hKE⟩

/-- **The under-seat slide's whole-segment relocation round trip.**
PORTED verbatim from `Orig/Classify.lean:1498`
(`tabToTab_under_rtp`); statement note as the bare twin above. -/
private theorem tabToTab_under_rtp {st : State} {c : Card} {b : Base} {a k : Anchor}
    {z : Card} {tr : List Card} {s₁ : State}
    (hs₁ : s₁ = (st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
      (fromCard c (st.piles a).faceUp) b)
    (hrt : fromCard c (st.piles a).faceUp = c :: tr)
    (hz : lastOf (below c (st.piles a).faceUp) = some z)
    (hsit : canSitOn c z = true)
    (hhold : s₁.pileHolding c = some k)
    (hsA : s₁.piles a = ⟨(st.piles a).hidden, below c (st.piles a).faceUp⟩)
    (hs₁K : s₁.piles k = ⟨(st.piles k).hidden,
      (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp⟩)
    (hkeep : ∀ y, y ≠ a → y ≠ k → s₁.piles y = st.piles y)
    (hcN : c ∉ (st.piles k).faceUp)
    (hka : k ≠ a)
    (hzOnly : ∀ y, y ≠ a → (s₁.piles y).top ≠ some z)
    (hzK : (st.piles k).top ≠ some z)
    (hKE : (st.piles k).faceUp = [] → (st.piles k).hidden = []) :
    s₁.run [Move.tabToTab c (Sum.inr z)] = some st := by
  -- successor accessor facts
  have hsF : ∀ σ, s₁.found σ = st.found σ := by
    intro σ
    rw [hs₁, putRun_found, setPile_found]
  have hsS : s₁.stock = st.stock := by rw [hs₁, putRun_stock, setPile_stock]
  have hsW : s₁.waste = st.waste := by rw [hs₁, putRun_waste, setPile_waste]
  have hsD : s₁.drawStep = st.drawStep := by
    rw [hs₁, putRun_drawStep, setPile_drawStep]
  -- the landing pile read, as the mirror needs it
  have hKfaceUp : (s₁.piles k).faceUp =
      (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp :=
    congrArg (fun p => p.faceUp) hs₁K
  have hKhidden : (s₁.piles k).hidden = (st.piles k).hidden :=
    congrArg (fun p => p.hidden) hs₁K
  have hexcl := below_fromCard_excl (c := c) ((st.piles k).faceUp)
    (fromCard c (st.piles a).faceUp) hcN
  have hbelowK : below c (s₁.piles k).faceUp = (st.piles k).faceUp := by
    have h1 : below c (s₁.piles k).faceUp
        = below c ((st.piles k).faceUp ++ fromCard c (st.piles a).faceUp) := by
      rw [hKfaceUp]
    rw [h1, hexcl.1, hrt, below_head_eq, List.append_nil]
  have hrunK : fromCard c (s₁.piles k).faceUp = c :: tr := by
    have h1 : fromCard c (s₁.piles k).faceUp
        = fromCard c ((st.piles k).faceUp ++ fromCard c (st.piles a).faceUp) := by
      rw [hKfaceUp]
    rw [h1, hexcl.2, hrt, fromCard_head_eq]
  -- the base search pins, first at s₁, then after the mirror's own removal
  have haTop : (s₁.piles a).top = some z := by
    show lastOf ((s₁.piles a).faceUp) = some z
    rw [show (s₁.piles a).faceUp = below c (st.piles a).faceUp from
      congrArg (fun p => p.faceUp) hsA]
    exact hz
  have hsTop : s₁.pileOfTop z = some a := by
    show firstWhere (fun x => decide ((s₁.piles x).top = some z)) Anchor.all = some a
    exact firstWhere_find (Anchor.mem_all a) (decide_eq_true haTop)
      (fun y hy hyne => decide_false_of_not (hzOnly y hyne))
  have hmidA : (s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
      (below c (s₁.piles k).faceUp)) : State).piles a = s₁.piles a := by
    show (if a = k then Pile.afterRunRemoved (s₁.piles k)
        (below c (s₁.piles k).faceUp) else s₁.piles a) = _
    rw [ite_eq_right (Ne.symm hka)]
  have hmidTop : ((s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
      (below c (s₁.piles k).faceUp)) : State).piles a).top = some z := by
    rw [hmidA]
    exact haTop
  have hknotN : ((s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
      (below c (s₁.piles k).faceUp)) : State).piles k).top ≠ some z := by
    show (if k = k then Pile.afterRunRemoved (s₁.piles k)
        (below c (s₁.piles k).faceUp) else s₁.piles k).top ≠ some z
    rw [ite_eq_left rfl, hbelowK]
    cases hF2 : (st.piles k).faceUp with
    | nil =>
        rw [afterRunRemoved_empty_eq _ (hKhidden.trans (hKE hF2))]
        intro htop
        nomatch htop
    | cons w r₂ =>
        exact fun htop => hzK (show (st.piles k).top = some z from by
          show lastOf ((st.piles k).faceUp) = some z
          rw [hF2]
          exact htop)
  have hzN' : (s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
      (below c (s₁.piles k).faceUp)) : State).pileOfTop z = some a :=
    topPin2 hmidTop (fun y hya hyk => by
      show (if y = k then Pile.afterRunRemoved (s₁.piles k)
          (below c (s₁.piles k).faceUp) else s₁.piles y) = s₁.piles y
      rw [ite_eq_right hyk])
      hknotN (fun y hya _ => hzOnly y hya)
  have hcp1 : s₁.canPlace c (Sum.inr z) = true := by
    show (match s₁.pileOfTop z with
      | some _ => canSitOn c z | none => false) = true
    rw [hsTop]
    exact hsit
  have hstep2 : State.step s₁ (Move.tabToTab c (Sum.inr z)) = some st := by
    simp only [State.step, hhold, hcp1, hrunK]
    refine congrArg some (?_ :
      (s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
          (below c (s₁.piles k).faceUp))).putRun (c :: tr) (Sum.inr z) = st)
    refine State.ext (funext fun σ => ?_) (funext fun y => ?_) ?_ ?_ ?_
    · rw [putRun_found, setPile_found, hsF σ]
    · by_cases hya : y = a
      · rw [hya, putRun_piles_inr_self _ _ _ _ hzN', hmidA]
        refine Pile.ext ?_ ?_
        · exact congrArg (fun p => p.hidden) hsA
        · have hj := below_join (c := c) ((st.piles a).faceUp)
          rw [hrt] at hj
          rw [show (s₁.piles a).faceUp = below c (st.piles a).faceUp from
            congrArg (fun p => p.faceUp) hsA]
          exact hj
      · by_cases hyk : y = k
        · rw [hyk, putRun_piles_inr_ne _ _ _ _ hzN' hka,
            setPile_piles_self, hbelowK]
          cases hF2 : (st.piles k).faceUp with
          | nil =>
              rw [afterRunRemoved_empty_eq _ (hKhidden.trans (hKE hF2))]
              exact Pile.ext (hKE hF2).symm hF2.symm
          | cons w r₂ =>
              exact Pile.ext hKhidden hF2.symm
        · rw [putRun_piles_inr_ne _ _ _ _ hzN' hya,
            setPile_piles_ne hyk]
          exact hkeep y hya hyk
    · rw [putRun_stock, setPile_stock]
      exact hsS
    · rw [putRun_waste, setPile_waste]
      exact hsW
    · rw [putRun_drawStep, setPile_drawStep]
      exact hsD
  simp only [State.run, hstep2]

/-- **The under-seat `.tabToTab` undo, witness form (primary).**  A
successful no-reveal `.tabToTab` whose source pile keeps face-up
content below the moved run (`hz` pins that content's top card,
`z`) is undone by the mirror move: run back onto `z`.  PORTED
verbatim from `Orig/Classify.lean:1653`; carrier note as above. -/
private theorem tabToTab_undo_under {st : State} {c : Card} {b : Base} {a k : Anchor}
    {z : Card} {s₁ : State}
    (hstep : State.step st (Move.tabToTab c b) = some s₁)
    (hh : st.pileHolding c = some a)
    (hz : lastOf (below c (st.piles a).faceUp) = some z)
    (hsit : canSitOn c z = true)
    (hhold : s₁.pileHolding c = some k)
    (hseat : b = Sum.inl k ∨ ∃ z', b = Sum.inr z' ∧
      (st.setPile a (Pile.afterRunRemoved (st.piles a)
        (below c (st.piles a).faceUp)) : State).pileOfTop z' = some k)
    (hkeep : ∀ y, y ≠ a → y ≠ k → s₁.piles y = st.piles y)
    (hcN : c ∉ (st.piles k).faceUp)
    (hzOnly : ∀ y, y ≠ a → (s₁.piles y).top ≠ some z)
    (hzK : (st.piles k).top ≠ some z) :
    reversibleAtW st (Move.tabToTab c b) := by
  obtain ⟨a₀, hh₀, hcp, hfr, hs₁⟩ := step_tabToTab_inv hstep
  rw [hh] at hh₀
  injection hh₀ with haa
  subst haa
  obtain ⟨tr, hrt⟩ := fromCard_head rfl hfr
  have hka : k ≠ a := fun hcon => hcN (by rw [hcon]; exact pileHolding_mem hh)
  have hprene : below c (st.piles a).faceUp ≠ [] := by
    intro hcon
    rw [hcon] at hz
    exact absurd hz (by simp [lastOf])
  -- the source seat keeps its hidden cards and its below part (no
  -- reveal: the below part is nonempty)
  have hsA : s₁.piles a = ⟨(st.piles a).hidden, below c (st.piles a).faceUp⟩ := by
    rw [hs₁]
    rcases hseat with rfl | ⟨z', rfl, hmidPin⟩
    · rw [putRun_piles_inl_ne _ _ _ _ (Ne.symm hka),
        setPile_piles_self]
      cases hF : below c (st.piles a).faceUp with
      | nil => exact absurd hF hprene
      | cons w t₂ => rfl
    · rw [putRun_piles_inr_ne _ _ _ _ hmidPin (Ne.symm hka),
        setPile_piles_self]
      cases hF : below c (st.piles a).faceUp with
      | nil => exact absurd hF hprene
      | cons w t₂ => rfl
  have hs₁K : s₁.piles k = ⟨(st.piles k).hidden,
      (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp⟩ := by
    rw [hs₁]
    rcases hseat with rfl | ⟨z', rfl, hmidPin⟩
    · rw [putRun_piles_inl_self]
      obtain ⟨hhE, hfE⟩ := (Pile.isEmpty_eq _).mp (canPlace_inl hcp).1
      refine Pile.ext ?_ ?_
      · rw [hhE]
      · rw [hfE, List.nil_append]
    · rw [putRun_piles_inr_self _ _ _ _ hmidPin,
        setPile_piles_ne hka]
  have hKE : (st.piles k).faceUp = [] → (st.piles k).hidden = [] := by
    rcases hseat with rfl | ⟨z', rfl, hmidPin⟩
    · intro _
      exact (Pile.isEmpty_eq _).mp (canPlace_inl hcp).1 |>.1
    · intro hcon
      have hne := (pileOfTop_top hmidPin).1
      rw [setPile_piles_ne hka] at hne
      exact absurd hcon hne
  exact ⟨s₁, [Move.tabToTab c (Sum.inr z)], hstep,
    tabToTab_under_rtp hs₁ hrt hz hsit hhold hsA hs₁K hkeep hcN hka hzOnly hzK hKE⟩

/-!
## §2. THE WASTE PAIR  (universal rows — no gate)

FLIP of `Orig/Classify.lean:1072`/`:1080`
(`irreversibleAt_wasteToFound`/`irreversibleAt_wasteToTab`,
commit-polarity, no gate): the cycle count strictly drops and never
rises, so a returning play is refuted at every position, wild or
WF; here the refutation is taken directly against the carrier.
The oracle's `false` cells for these two letters are exactly this
universality.
-/

/-- **The waste-to-foundation letter**: the oracle reads `false`
and the witness is denied UNIVERSALLY — the cycle count strictly
drops on the move and never rises along any play. -/
theorem wasteToFound_not_reversibleAtW (st : State) (c : Card) :
    ¬ reversibleAtW st (Move.wasteToFound c) := by
  rintro ⟨s₁, play, hstep, hrun⟩
  have hdrop := cycleCount_step_wasteToFound hstep
  have hle := mono_run cycleCount (fun _ _ _ hst => cycleCount_step hst) hrun
  omega

/-- **The waste-to-tableau letter**: same measure, same denial —
the popped waste never re-arms. -/
theorem wasteToTab_not_reversibleAtW (st : State) (c : Card) (b : Base) :
    ¬ reversibleAtW st (Move.wasteToTab c b) := by
  rintro ⟨s₁, play, hstep, hrun⟩
  have hdrop := cycleCount_step_wasteToTab hstep
  have hle := mono_run cycleCount (fun _ _ _ hst => cycleCount_step hst) hrun
  omega

/-!
## §3. THE DRAW LETTER

The draw's undoability shape reads: no stock and the waste rests
(the pass base — one recycle re-deals the waste whole, the
re-deal's play handed by the §1k kit), or stock present, waste
nonempty and the cycle resting on a whole deal (the in-phase round
trip, the two-leg rotation).  The flipped template is `drawClass`
(`Orig/Classify.lean:2783`, whose `drawIrr` (:2778) cell is the
negation of `drawR`); the commit side is §1i's pristine row and
§1j's lex offset row (the two Phase originals re-stated at
carrier grade); the both-empty cell is the vacuous denial.
-/

/-- **The draw letter**: at `WF` the shape `drawR` reads
undoability exactly — the both-empty, pristine and offset draws
deny the witness; the pass-base and in-phase draws hand the
explicit re-deal back.  FLIP of `Orig/Classify.lean:2783`
(`drawClass`); the `drawR` cells are the negation of the frozen
`drawIrr` cells at `:2778`, per case. -/
theorem drawR_iff_reversibleAtW {st : State} (hwf : st.WF) :
    drawR st = true ↔ reversibleAtW st Move.draw := by
  have hd : 0 < st.drawStep := hwf.drawStep_pos
  cases hstock : st.stock with
  | nil =>
      have hred : drawR st = decide (st.waste ≠ []) := by
        rw [drawR, hstock]
      rw [hred]
      by_cases hw : st.waste = []
      · have hcell : decide (st.waste ≠ []) = false :=
          decide_false_of_not (fun h => h hw)
        rw [hcell]
        exact ⟨fun h => Bool.noConfusion h,
          fun w => absurd w (not_W_of_step_none (by
            show State.dealStock (State.recycle st) = none
            rw [recycle_allEmpty st hstock hw, dealStock_nil st hstock]))⟩
      · have hcell : decide (st.waste ≠ []) = true := decide_eq_true hw
        rw [hcell]
        exact ⟨fun _ => draw_passBase_reversibleW hstock hw hd, fun _ => rfl⟩
  | cons w' t =>
      have hne : st.stock ≠ [] := by
        intro hc
        rw [hstock] at hc
        exact absurd hc (by simp)
      have hred : drawR st =
          (decide (st.waste ≠ []) && decide (st.waste.length % st.drawStep = 0)) := by
        rw [drawR, hstock]
      rw [hred]
      by_cases hw : st.waste = []
      · have hcell : (decide (st.waste ≠ []) &&
            decide (st.waste.length % st.drawStep = 0)) = false := by
          rw [decide_false_of_not (fun h => h hw), Bool.false_and]
        rw [hcell]
        exact ⟨fun h => Bool.noConfusion h,
          fun w => absurd w (draw_notW_of_pristine hd hne hw)⟩
      · by_cases hres : st.waste.length % st.drawStep = 0
        · have hcell : (decide (st.waste ≠ []) &&
              decide (st.waste.length % st.drawStep = 0)) = true := by
            rw [decide_eq_true hw, decide_eq_true hres, Bool.true_and]
          rw [hcell]
          have hph : inPhase st = true := by
            rw [inPhase_eq_decide_of_cons hstock, decide_eq_true hres]
          exact ⟨fun _ => draw_inphase_reversibleW hd hne hw hph, fun _ => rfl⟩
        · have hcell : (decide (st.waste ≠ []) &&
              decide (st.waste.length % st.drawStep = 0)) = false := by
            rw [decide_eq_false hres]
            exact Bool.and_false _
          rw [hcell]
          exact ⟨fun h => Bool.noConfusion h,
            fun w => absurd w (draw_notW_of_offset hd hne hres)⟩

/-!
## §4. THE TABTOFOUND LETTER

The raise shape `tabToFoundR` reads undoability natively: licensed
and a chop beneath the card (the giveback seat — the under row),
or a bare KING seat (the emptied seat readmits its king); bare
non-king lifts and hidden flips are the commits.  FLIP of
`Orig/Classify.lean:1789` (`tabToFoundClass` over `tabToFoundIrr`
at :1775), restated at the carrier grade.
-/

/-- A bare `.tabToFound` of a non-king denies the witness: the
emptied seat never receives the card back — every write onto an
empty seat demands a king, every card-base write only extends
nonempty already-anchored contents, and the bare-king invariant
along any play keeps the pile empty or king-anchored, which the
original content, headed by the non-king mover, contradicts.
FLIP of `Orig/Classify.lean:967`
(`tabToFound_irreversible_of_bare_nonking`, commit grade there) —
re-stated at `¬ reversibleAtW` over the §1o invariant kit. -/
private theorem tabToFound_notW_of_bare_nonking {st : State} {c : Card}
    {a : Anchor} {s₁ : State}
    (hstep : State.step st (Move.tabToFound c) = some s₁)
    (hpa : st.pileOfTop c = some a)
    (hchop : chop (st.piles a).faceUp = [])
    (hhidden : (st.piles a).hidden = [])
    (hking : c.rank ≠ Rank.king) :
    ¬ reversibleAtW st (Move.tabToFound c) := by
  rintro ⟨s₁', play, hstep', hrun⟩
  rw [hstep] at hstep'
  injection hstep' with hEq
  subst hEq
  obtain ⟨-, a', hp', hs₁eq⟩ := step_tabToFound_inv hstep
  have hae : a' = a := by
    have hx : some a = some a' := hpa.symm.trans hp'
    injection hx with hxE
    exact hxE.symm
  have hbare : BareKing (s₁.piles a) := by
    rw [hs₁eq, hae]
    show BareKing (if a = a
        then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
        else st.piles a)
    rw [ite_eq_left rfl, hchop, afterRunRemoved_faceUp_empty_self hhidden]
    exact ⟨hhidden, True.intro⟩
  have hd := bare_king_run play s₁ st a hbare hrun
  obtain ⟨-, hkc⟩ := hd
  have hface : (st.piles a).faceUp = [c] := by
    obtain ⟨-, hlast⟩ := pileOfTop_top hpa
    rw [lastOf_chop hlast, hchop, List.nil_append]
  rw [hface] at hkc
  exact absurd hkc hking

/-- **The under-row `.tabToFound` witness at `WF`.**  The
classification's own grind, re-stated at the carrier grade: the
`runOK` seam fit of the giveback card, and the successor's
`pileOfTop` re-pin (the card-count uniqueness excluding every
other seat).  PORTED (extraction, not re-derivation) from
`Orig/Classify.lean:1907` (`tabToFound_reversibleAtW_under_wf`);
the witness is the §1m `tabToFound_undo_under`. -/
private theorem tabToFound_W_under_wf {st : State} {c : Card} {a : Anchor}
    (hwf : st.WF) (hn : st.nextUp c = true) (ha : st.pileOfTop c = some a)
    {z' : Card} {preT : List Card}
    (hchop : chop (st.piles a).faceUp = z' :: preT) :
    reversibleAtW st (Move.tabToFound c) := by
  obtain ⟨s₁, hs₁⟩ := step_tabToFound_some hn ha
  obtain ⟨zW, hzw0⟩ := lastOf_cons_some preT z'
  have hzw : lastOf (chop (st.piles a).faceUp) = some zW := by
    rw [hchop]
    exact hzw0
  have hsit : canSitOn c zW = true := by
    refine runOK_adjacent_snoc hzw0 ?_
    have hface : (st.piles a).faceUp = chop (st.piles a).faceUp ++ [c] :=
      lastOf_chop (pileOfTop_top ha).2
    have hrunk : runOK (st.piles a).faceUp = true := hwf.runOK_of a
    rw [hface, hchop] at hrunk
    exact hrunk
  have hsearch : s₁.pileOfTop zW = some a := by
    obtain ⟨-, a', hp', hs'⟩ := step_tabToFound_inv hs₁
    have hae : a' = a := by
      have hx : some a = some a' := ha.symm.trans hp'
      injection hx with hxE
      exact hxE.symm
    rw [hs', hae]
    have hothers : ∀ a₂, a₂ ≠ a →
        ((({ found := fun σ => if σ = c.suit then st.found c.suit ++ [c] else st.found σ, piles := fun a'' => if a'' = a then (Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp) : Pile) else st.piles a'', stock := st.stock, waste := st.waste, drawStep := st.drawStep } : State).piles) a₂) = st.piles a₂ := by
      intro a₂ hne₂
      show (if a₂ = a then
          ((Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp) : Pile))
          else st.piles a₂) = st.piles a₂
      rw [ite_eq_right hne₂]
    have htop2 : ((({ found := fun σ => if σ = c.suit then st.found c.suit ++ [c] else st.found σ, piles := fun a'' => if a'' = a then (Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp) : Pile) else st.piles a'', stock := st.stock, waste := st.waste, drawStep := st.drawStep } : State).piles a)).top = some zW := by
      show (if a = a then
          ((Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp) : Pile))
          else st.piles a).top = some zW
      rw [ite_eq_left rfl]
      show lastOf ((Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)).faceUp) = some zW
      rw [afterRunRemoved_faceUp_ne (by
          rw [hchop]; exact fun hh => absurd hh (by simp)), hchop]
      exact hzw0
    have hnost2 : ∀ a₂, a₂ ≠ a → (st.piles a₂).top ≠ some zW :=
      fun a₂ hne₂ => wf_no_other_top hwf (chop_mem (lastOf_mem hzw)) a₂ hne₂
    exact topPin hothers htop2 hnost2
  exact tabToFound_undo_under hs₁ ha hzw hsit hsearch

/-- **The raise letter**: at `WF` the shape `tabToFoundR` reads
undoability exactly — unlicensed seats and refused searches deny
the witness; the reveal flip's hidden total strictly drops; the
bare non-king lift denies the no-redo seat; the bare KING hands
the vacate play; the chop-beneath row hands the giveback over the
chop.  FLIP of `Orig/Classify.lean:1789` (`tabToFoundClass`; the
`tabToFoundR` cells negate the frozen `tabToFoundIrr` cells at
`:1775`, per case). -/
theorem tabToFoundR_iff_reversibleAtW {st : State} (hwf : st.WF) (c : Card) :
    tabToFoundR st c = true ↔ reversibleAtW st (Move.tabToFound c) := by
  by_cases hn : st.nextUp c = true
  · by_cases hloc : st.pileOfTop c = none
    · have hcell : tabToFoundR st c = false := by rw [tabToFoundR, hn, hloc]
      rw [hcell]
      exact ⟨fun h => Bool.noConfusion h,
        fun w => absurd w (not_W_of_step_none
          (step_tabToFound_none_of_pileOfTop hn hloc))⟩
    · obtain ⟨a, ha⟩ := option_some_of_ne_none hloc
      obtain ⟨s₁, hs₁⟩ := step_tabToFound_some hn ha
      cases hchop : chop (st.piles a).faceUp with
      | nil =>
          cases hhidden : (st.piles a).hidden with
          | nil =>
              by_cases hkng : c.rank = Rank.king
              · have hcell : tabToFoundR st c = true := by
                  simp only [tabToFoundR, hn, ha, hchop, hhidden]
                  rw [decide_eq_true hkng]
                rw [hcell]
                exact ⟨fun _ => tabToFound_undo_bare hs₁ ha hchop hhidden hkng,
                  fun _ => rfl⟩
              · have hcell : tabToFoundR st c = false := by
                  simp only [tabToFoundR, hn, ha, hchop, hhidden]
                  rw [decide_false_of_not hkng]
                rw [hcell]
                exact ⟨fun h => Bool.noConfusion h,
                  fun w => absurd w (tabToFound_notW_of_bare_nonking hs₁ ha hchop
                    hhidden hkng)⟩
          | cons hh1 t1 =>
              have hcell : tabToFoundR st c = false := by
                simp only [tabToFoundR, hn, ha, hchop, hhidden]
              rw [hcell]
              exact ⟨fun h => Bool.noConfusion h,
                fun w => absurd w (not_W_of_desc hiddenTotal
                  (fun s m s' hst => hiddenTotal_step hst) hs₁
                  (hiddenTotal_step_tabToFound_reveal hs₁ ha hchop
                    (by rw [hhidden]; intro hh; exact absurd hh (by simp))))⟩
      | cons z' preT =>
          have hcell : tabToFoundR st c = true := by
            simp only [tabToFoundR, hn, ha, hchop]
          rw [hcell]
          exact ⟨fun _ => tabToFound_W_under_wf hwf hn ha hchop, fun _ => rfl⟩
  · have hf : st.nextUp c = false := by
      cases hnf : st.nextUp c with
      | true => exact absurd hnf hn
      | false => rfl
    have hcell : tabToFoundR st c = false := by
      simp only [tabToFoundR, hf]
    rw [hcell]
    exact ⟨fun h => Bool.noConfusion h,
      fun w => absurd w (not_W_of_step_none (step_tabToFound_none_of_nextUp hf))⟩

/-!
## §5. THE FOUNDTOTAB LETTER

The pull shape `foundToTabR` reads undoability natively: the
foundation's current top is the pulled card and the base accepts
it (the re-raise onto the accepting base — the mirror of the
raise letter); every refused cell (empty foundation, foreign top,
refused seat) makes the move vacuous.  FLIP of
`Orig/Classify.lean:1979` (`foundToTabClass` over `foundToTabIrr`
at :1974), restated at the carrier grade.
-/

/-- **The legal-pull `.foundToTab` witness at `WF`.**  The
classification's own grind, re-stated at the carrier grade: the
chop arithmetic pins the `nextUp` premise via the foundation's
prefix property, and the successor's `pileOfTop` search re-pins
its written seat (the card-count uniqueness excluding every other
seat — `wf_found_not_pileTop`).  PORTED (extraction, not
re-derivation) from `Orig/Classify.lean:2101`
(`foundToTab_reversibleAtW_of_legal_wf`); the witness is the §1r
`foundToTab_undo`. -/
private theorem foundToTab_W_of_legal_wf {st : State} {c : Card} {b : Base}
    (hwf : st.WF) (htop : st.foundTop c.suit = some c) (hcp : st.canPlace c b = true) :
    reversibleAtW st (Move.foundToTab c b) := by
  obtain ⟨s₁, hs⟩ := step_foundToTab_legal htop hcp
  have hnext : (chop (st.found c.suit)).length = c.rank.toIdx :=
    wf_found_chop_toIdx hwf htop
  cases b with
  | inl k =>
      have hnost : ∀ a₂ : Anchor, a₂ ≠ k → (st.piles a₂).top ≠ some c :=
        fun a₂ _ => @wf_found_not_pileTop st c a₂ c.suit hwf htop
      have hsearch : s₁.pileOfTop c = some k := by
        obtain ⟨-, -, -, -, hs'⟩ := step_foundToTab_inv hs
        rw [hs']
        have hothers : ∀ a₂, a₂ ≠ k →
            ((st.setFound c.suit (chop (st.found c.suit))).putCard c (Sum.inl k)).piles a₂
              = st.piles a₂ := by
          intro a₂ hne₂
          rw [putCard_piles_inl]
          show (if a₂ = k then ((⟨[], [c]⟩ : Pile)) else st.piles a₂) = st.piles a₂
          rw [ite_eq_right hne₂]
        have htop2 : (((st.setFound c.suit (chop (st.found c.suit))).putCard c (Sum.inl k)).piles k).top
            = some c := by
          rw [putCard_piles_inl]
          show (if k = k then ((⟨[], [c]⟩ : Pile)) else st.piles k).top = some c
          rw [ite_eq_left rfl]
          rfl
        exact topPin hothers htop2 hnost
      exact foundToTab_undo hs hnext hsearch (Or.inl rfl)
  | inr z =>
      obtain ⟨k, hz, -⟩ := canPlace_inr hcp
      have hnost : ∀ a₂ : Anchor, a₂ ≠ k → (st.piles a₂).top ≠ some c :=
        fun a₂ _ => @wf_found_not_pileTop st c a₂ c.suit hwf htop
      have hsearch : s₁.pileOfTop c = some k := by
        obtain ⟨-, -, -, -, hs'⟩ := step_foundToTab_inv hs
        rw [hs']
        have hz2 : (st.setFound c.suit (chop (st.found c.suit))).pileOfTop z
            = some k := hz
        have hothers : ∀ a₂, a₂ ≠ k →
            ((st.setFound c.suit (chop (st.found c.suit))).putCard c (Sum.inr z)).piles a₂
              = st.piles a₂ := by
          intro a₂ hne₂
          rw [putCard_piles_inr _ _ _ _ hz2]
          show (if a₂ = k then
              ({ st.piles k with faceUp := (st.piles k).faceUp ++ [c] } : Pile)
              else st.piles a₂) = st.piles a₂
          rw [ite_eq_right hne₂]
        have htop2 : (((st.setFound c.suit (chop (st.found c.suit))).putCard c (Sum.inr z)).piles k).top
            = some c := by
          rw [putCard_piles_inr _ _ _ _ hz2]
          show (if k = k then
              ({ st.piles k with faceUp := (st.piles k).faceUp ++ [c] } : Pile)
              else st.piles k).top = some c
          rw [ite_eq_left rfl]
          show lastOf ((st.piles k).faceUp ++ [c]) = some c
          exact lastOf_snoc
        exact topPin hothers htop2 hnost
      exact foundToTab_undo hs hnext hsearch (Or.inr ⟨z, rfl, hz⟩)

/-- **The pull letter**: at `WF` the shape `foundToTabR` reads
undoability exactly — every refused cell (empty foundation, no
matching top, refused base) makes the move vacuous and denies the
witness; the legal cell hands the re-raise play back.  FLIP of
`Orig/Classify.lean:1979` (`foundToTabClass`; the `foundToTabR`
cells negate the frozen `foundToTabIrr` cells at `:1974`, per
case). -/
theorem foundToTabR_iff_reversibleAtW {st : State} (hwf : st.WF) (c : Card) (b : Base) :
    foundToTabR st c b = true ↔ reversibleAtW st (Move.foundToTab c b) := by
  cases htop : st.foundTop c.suit with
  | none =>
      have hcell : foundToTabR st c b = false := by
        simp only [foundToTabR, htop]
      rw [hcell]
      exact ⟨fun h => Bool.noConfusion h,
        fun w => absurd w (not_W_of_step_none (by simp only [State.step, htop]))⟩
  | some c' =>
      by_cases hcc : c' = c
      · rw [hcc] at htop
        cases hcp : st.canPlace c b with
        | false =>
            have hcell : foundToTabR st c b = false := by
              simp only [foundToTabR, htop, hcp]
              rfl
            rw [hcell]
            exact ⟨fun h => Bool.noConfusion h,
              fun w => absurd w (not_W_of_step_none (step_foundToTab_none htop (by
                intro hc
                rw [Bool.and_eq_true, decide_eq_true rfl] at hc
                exact Bool.noConfusion (hcp.symm.trans hc.2))))⟩
        | true =>
            have hcell : foundToTabR st c b = true := by
              simp only [foundToTabR, htop, hcp]
              rfl
            rw [hcell]
            exact ⟨fun _ => foundToTab_W_of_legal_wf hwf htop hcp, fun _ => rfl⟩
      · have hcell : foundToTabR st c b = false := by
          simp only [foundToTabR, htop]
          rw [ite_eq_right hcc]
        rw [hcell]
        exact ⟨fun h => Bool.noConfusion h,
          fun w => absurd w (not_W_of_step_none (step_foundToTab_none htop (by
            intro hc
            rw [Bool.and_eq_true] at hc
            exact Bool.noConfusion (hc.1.symm.trans (decide_eq_false hcc)))))⟩

/-!
## §6. THE TABTOTAB LETTER

The slide shape `tabToTabR` reads undoability natively: located
run head, accepting base, and either a bare KING seat (the
whole-segment vacate back onto the emptied seat) or face-up company
beneath the run (the whole-segment relocation back onto the seat
card).  FLIP of `Orig/Classify.lean:2180` (`tabToTabClass` over
`tabToTabIrr` at :2166), restated at the carrier grade.
-/

/-- A bare `.tabToTab` of a non-king run head denies the witness:
the emptied seat obeys the receive-only-kings discipline, and the
run can never come back to an empty seat under a non-king head.
FLIP of `Orig/Classify.lean:1004`
(`tabToTab_irreversible_of_bare_nonking`, commit grade there) —
re-stated at `¬ reversibleAtW` over the §1o invariant kit and the
§1t mirror kit. -/
private theorem tabToTab_notW_of_bare_nonking {st : State} {c : Card} {b : Base}
    {a : Anchor} {s₁ : State}
    (hstep : State.step st (Move.tabToTab c b) = some s₁)
    (hh : st.pileHolding c = some a)
    (hpre : below c (st.piles a).faceUp = [])
    (hhidden : (st.piles a).hidden = [])
    (hfr : fromCard c (st.piles a).faceUp ≠ [])
    (hking : c.rank ≠ Rank.king) :
    ¬ reversibleAtW st (Move.tabToTab c b) := by
  rintro ⟨s₁', play, hstep', hrun⟩
  rw [hstep] at hstep'
  injection hstep' with hEq
  subst hEq
  obtain ⟨a₀, hh₀, hcp, hfr₀, hs₁eq⟩ := step_tabToTab_inv hstep
  have hae : a₀ = a := by
    have hx : some a = some a₀ := hh.symm.trans hh₀
    injection hx with hxE
    exact hxE.symm
  rw [hae] at hfr₀
  have hbare : BareKing (s₁.piles a) := by
    rw [hs₁eq, hae, hpre]
    have hself : BareKing
        ((st.setPile a (Pile.afterRunRemoved (st.piles a) ([] : List Card))).piles a) := by
      rw [setPile_piles_self_any, afterRunRemoved_faceUp_empty_self hhidden]
      exact ⟨hhidden, True.intro⟩
    have hEmptyM1 : ((st.setPile a
        (Pile.afterRunRemoved (st.piles a) ([] : List Card))).piles) a
        = ⟨[], ([] : List Card)⟩ := by
      rw [setPile_piles_self_any, afterRunRemoved_faceUp_empty_self hhidden, hhidden]
    cases b with
    | inl k =>
        obtain ⟨his, -⟩ := canPlace_inl hcp
        have hka : k ≠ a := by
          intro hcon
          rw [hcon] at his
          obtain ⟨-, hfe⟩ := (Pile.isEmpty_eq (st.piles a)).mp his
          rw [hfe] at hfr₀
          exact absurd rfl hfr₀
        rw [putRun_piles_inl_ne _ _ _ _ (fun hcon => hka hcon.symm)]
        exact hself
    | inr z =>
        cases hz' : (st.setPile a
            (Pile.afterRunRemoved (st.piles a) ([] : List Card))).pileOfTop z with
        | none =>
            rw [putRun_inr_none hz']
            exact hself
        | some j =>
            by_cases hja : j = a
            · rw [hja] at hz'
              exact absurd hz' (pileOfTop_ne_of_empty hEmptyM1 z)
            · rw [putRun_piles_inr_ne _ _ _ _ hz' (fun hcon => hja hcon.symm)]
              exact hself
  have hd := bare_king_run play s₁ st a hbare hrun
  obtain ⟨-, hkc⟩ := hd
  have hface : (st.piles a).faceUp = fromCard c (st.piles a).faceUp := by
    have hj := below_join (c := c) ((st.piles a).faceUp)
    rw [hpre, List.nil_append] at hj
    exact hj.symm
  obtain ⟨ttr, hrt⟩ := fromCard_head rfl hfr
  rw [hface] at hkc
  rw [hrt] at hkc
  exact absurd hkc hking

/-- **The bare-KING slide witness at `WF`.**  PORTED (extraction,
not re-derivation) from `Orig/Classify.lean:2499`
(`tabToTab_reversibleAtW_bare_king_wf`); the witness is the §1t
`tabToTab_undo_bare`, the grounds (the landing-pile occurrence
pins through `canPlace_inl_target_pile_ne` /
`canPlace_inr_seat`, the successor holding re-pin, the mid-board
top pin) are the classification's own grind.  One lemma swap
against the frozen text: the emptied-seat removal row is stated
at the zero scrutinee (`afterRunRemoved_empty_eq`) — the frozen
below-form wrapper died at the `cases`/`rw` iota behavior
differences recorded in §1t. -/
private theorem tabToTab_W_bare_king_wf {st : State} {c : Card} {b : Base} {a : Anchor}
    (hwf : st.WF) (hh : st.pileHolding c = some a) (hcp : st.canPlace c b = true)
    (hbelow : below c (st.piles a).faceUp = []) (hhid : (st.piles a).hidden = [])
    (hkng : c.rank = Rank.king) :
    reversibleAtW st (Move.tabToTab c b) := by
  obtain ⟨s₁, hs⟩ := step_tabToTab_some hh hcp
  obtain ⟨a₂, hht, hct, hfr, hs₁⟩ := step_tabToTab_inv hs
  have haeq : a₂ = a := by
    have hx : some a = some a₂ := hh.symm.trans hht
    injection hx with hxE
    exact hxE.symm
  rw [haeq] at hs₁ hfr
  obtain ⟨tr, hrt⟩ := fromCard_head rfl hfr
  rw [hbelow, afterRunRemoved_empty_eq _ hhid] at hs₁
  cases b with
  | inl k =>
      have hka : k ≠ a := canPlace_inl_target_pile_ne hcp (pileHolding_mem hh)
      have hcN : c ∉ (st.piles k).faceUp :=
        (mem_faceUp_unique hwf (pileHolding_mem hh) k hka).1
      have hkeep : ∀ y, y ≠ a → y ≠ k → s₁.piles y = st.piles y := by
        intro y hya hyk
        rw [hs₁, putRun_piles_inl_ne _ _ _ _ hyk,
          setPile_piles_ne hya]
      have hca : c ∉ (s₁.piles a).faceUp := by
        rw [hs₁, putRun_piles_inl_ne _ _ _ _ (Ne.symm hka),
          setPile_piles_self]
        intro hcon
        cases hcon
      have hhk : c ∈ (s₁.piles k).faceUp := by
        rw [hs₁, putRun_piles_inl_self, hrt]
        exact List.mem_cons_self
      have hhold : s₁.pileHolding c = some k :=
        holdingPin2 hca (fun y hyk hya => hkeep y hya hyk) hhk
          (fun y hyk hya =>
            (mem_faceUp_unique hwf (pileHolding_mem hh) y hya).1)
      exact tabToTab_undo_bare hs hh hbelow hhid hkng hhold (Or.inl rfl)
        hkeep hcN
  | inr z' =>
      obtain ⟨k, hk₀, -⟩ := canPlace_inr hcp
      obtain ⟨hka, hcN⟩ := canPlace_inr_seat hwf hh hcp hk₀
      -- the mid pin: the source pile is topless at mid (it was
      -- emptied), so the card search pins pile k alone
      have hmidK : (st.setPile a ⟨[], ([] : List Card)⟩ : State).piles k
          = st.piles k := by
        show (if k = a then ⟨[], ([] : List Card)⟩ else st.piles k) = _
        rw [ite_eq_right hka]
      have hmidAtop : ((st.setPile a ⟨[], ([] : List Card)⟩ : State).piles a).top
          ≠ some z' := by
        show (if a = a then ⟨[], ([] : List Card)⟩ else st.piles a).top
          ≠ some z'
        rw [ite_eq_left rfl]
        intro hcon
        nomatch hcon
      have hseatMid :
          (st.setPile a ⟨[], ([] : List Card)⟩ : State).pileOfTop z'
            = some k :=
          topPin2 (by
              rw [hmidK]
              exact (pileOfTop_top hk₀).2)
            (fun y hyk hya => by
              show (if y = a then ⟨[], ([] : List Card)⟩
                  else st.piles y) = st.piles y
              rw [ite_eq_right hya])
            hmidAtop (fun y hyk _ =>
              wf_no_other_top hwf (lastOf_mem (pileOfTop_top hk₀).2) y hyk)
      have hkeep : ∀ y, y ≠ a → y ≠ k → s₁.piles y = st.piles y := by
        intro y hya hyk
        rw [hs₁, putRun_piles_inr_ne _ _ _ _ hseatMid hyk,
          setPile_piles_ne hya]
      have hca : c ∉ (s₁.piles a).faceUp := by
        rw [hs₁, putRun_piles_inr_ne _ _ _ _ hseatMid (Ne.symm hka),
          setPile_piles_self]
        intro hcon
        cases hcon
      have hhk : c ∈ (s₁.piles k).faceUp := by
        rw [hs₁, putRun_piles_inr_self _ _ _ _ hseatMid,
          hmidK, hrt]
        exact (List.mem_append).2 (Or.inr List.mem_cons_self)
      have hhold : s₁.pileHolding c = some k :=
        holdingPin2 hca (fun y hyk hya => hkeep y hya hyk) hhk
          (fun y hyk hya =>
            (mem_faceUp_unique hwf (pileHolding_mem hh) y hya).1)
      exact tabToTab_undo_bare hs hh hbelow hhid hkng hhold
        (Or.inr ⟨z', rfl, hseatMid⟩) hkeep hcN

/-- **The under-row slide witness at `WF`.**  PORTED (extraction,
not re-derivation) from `Orig/Classify.lean:2600`
(`tabToTab_reversibleAtW_under_wf`); the witness is the §1t
`tabToTab_undo_under`, the grounds (the seat-card pin, the `runOK`
seam fit, the landing-pile occurrence pins, the successor holding
re-pin, the rank-exclusion grind of `hzOnly`, the mid-board
`pileOfTop` pin through the `z ≠ z'` occurrence split) are the
classification's own grind. -/
private theorem tabToTab_W_under_wf {st : State} {c : Card} {b : Base} {a : Anchor}
    (hwf : st.WF) (hh : st.pileHolding c = some a) (hcp : st.canPlace c b = true)
    {z₀ : Card} {pre' : List Card}
    (hbelow : below c (st.piles a).faceUp = z₀ :: pre') :
    reversibleAtW st (Move.tabToTab c b) := by
  obtain ⟨s₁, hs⟩ := step_tabToTab_some hh hcp
  obtain ⟨a₂, hht, hct, hfr, hs₁⟩ := step_tabToTab_inv hs
  have haeq : a₂ = a := by
    have hx : some a = some a₂ := hh.symm.trans hht
    injection hx with hxE
    exact hxE.symm
  rw [haeq] at hs₁ hfr
  obtain ⟨tr, hrt⟩ := fromCard_head rfl hfr
  obtain ⟨z, hz⟩ := lastOf_cons_some pre' z₀
  have hzB : lastOf (below c (st.piles a).faceUp) = some z := by
    rw [hbelow]
    exact hz
  have hzin : z ∈ below c (st.piles a).faceUp := lastOf_mem hzB
  have hzmem : z ∈ (st.piles a).faceUp := below_mem hzin
  have h1 := below_join (c := c) ((st.piles a).faceUp)
  rw [hbelow, hrt] at h1
  -- h1 : (z₀ :: pre') ++ (c :: tr) = (st.piles a).faceUp
  have hrunOK0 : runOK ((st.piles a).faceUp) = true := hwf.runOK_of a
  have hrunlit : runOK ((z₀ :: pre') ++ (c :: tr)) = true := by
    rw [h1]
    exact hrunOK0
  have hrunTail : runOK (c :: tr) = true :=
    runOK_append_left (z₀ :: pre') (c :: tr) hrunlit
  have hfitpre : runOK (((z₀ :: pre') ++ [c]) ++ tr) = true := by
    rw [List.append_assoc]
    have hE : [c] ++ tr = c :: tr := by
      rw [List.cons_append, List.nil_append]
    rw [hE]
    exact hrunlit
  have hsit : canSitOn c z = true :=
    runOK_adjacent_snoc hz
      (runOK_append_right ((z₀ :: pre') ++ [c]) tr hfitpre)
  cases b with
  | inl k =>
      have hka : k ≠ a := canPlace_inl_target_pile_ne hcp (pileHolding_mem hh)
      have hcN : c ∉ (st.piles k).faceUp :=
        (mem_faceUp_unique hwf (pileHolding_mem hh) k hka).1
      have hzK : (st.piles k).top ≠ some z :=
        wf_no_other_top hwf hzmem k hka
      have hkeep : ∀ y, y ≠ a → y ≠ k → s₁.piles y = st.piles y := by
        intro y hya hyk
        rw [hs₁, putRun_piles_inl_ne _ _ _ _ hyk,
          setPile_piles_ne hya]
      have hca : c ∉ (s₁.piles a).faceUp := by
        rw [hs₁, putRun_piles_inl_ne _ _ _ _ (Ne.symm hka),
          setPile_piles_self, hbelow]
        show c ∉ (z₀ :: pre')
        rw [← hbelow]
        exact below_not_mem_self _
      have hhk : c ∈ (s₁.piles k).faceUp := by
        rw [hs₁, putRun_piles_inl_self, hrt]
        exact List.mem_cons_self
      have hhold : s₁.pileHolding c = some k :=
        holdingPin2 hca (fun y hyk hya => hkeep y hya hyk) hhk
          (fun y hyk hya =>
            (mem_faceUp_unique hwf (pileHolding_mem hh) y hya).1)
      have hzOnly : ∀ y, y ≠ a → (s₁.piles y).top ≠ some z := by
        intro y hya
        by_cases hyk : y = k
        · rw [hyk]
          intro htop
          have hmemK : z ∈ (s₁.piles k).faceUp := Pile.mem_of_top htop
          have hkFu : (s₁.piles k).faceUp
              = fromCard c (st.piles a).faceUp := by
            rw [hs₁, putRun_piles_inl_self]
          rw [hkFu, hrt] at hmemK
          rcases List.mem_cons.1 hmemK with heq | htr2
          · rw [heq] at hsit
            obtain ⟨hrank, -⟩ := (canSitOn_eq c c).mp hsit
            omega
          · have hrk := runOK_head_lt hrunTail htr2
            obtain ⟨hrank, -⟩ := (canSitOn_eq c z).mp hsit
            omega
        · intro htop
          rw [hkeep y hya hyk] at htop
          exact wf_no_other_top hwf hzmem y hya htop
      exact tabToTab_undo_under hs hh hzB hsit hhold (Or.inl rfl)
        hkeep hcN hzOnly hzK
  | inr z' =>
      obtain ⟨k, hk₀, -⟩ := canPlace_inr hcp
      obtain ⟨hka, hcN⟩ := canPlace_inr_seat hwf hh hcp hk₀
      have hzK : (st.piles k).top ≠ some z :=
        wf_no_other_top hwf hzmem k hka
      have hz'mem : z' ∈ (st.piles k).faceUp :=
        lastOf_mem (pileOfTop_top hk₀).2
      have hnostK : ∀ y : Anchor, y ≠ k → (st.piles y).top ≠ some z' :=
        fun y hy => wf_no_other_top hwf hz'mem y hy
      have hmidK : (st.setPile a (Pile.afterRunRemoved (st.piles a)
          (below c (st.piles a).faceUp)) : State).piles k = st.piles k := by
        show (if k = a then Pile.afterRunRemoved (st.piles a)
            (below c (st.piles a).faceUp) else st.piles k) = _
        rw [ite_eq_right hka]
      -- at mid, the source pile tops z (the below part survived),
      -- and z ≠ z' by the occurrence uniqueness
      have hmidAtop : ((st.setPile a (Pile.afterRunRemoved (st.piles a)
          (below c (st.piles a).faceUp)) : State).piles a).top
          ≠ some z' := by
        show (if a = a then Pile.afterRunRemoved (st.piles a)
            (below c (st.piles a).faceUp) else st.piles a).top ≠ some z'
        rw [ite_eq_left rfl, hbelow]
        show (⟨(st.piles a).hidden, z₀ :: pre'⟩ : Pile).top ≠ some z'
        intro hcon
        have hlt : lastOf (z₀ :: pre') = some z' := hcon
        rw [hz] at hlt
        injection hlt with hzz'
        have hzc : z' ∈ (st.piles a).faceUp := by
          rw [← hzz']
          exact hzmem
        exact absurd hz'mem ((mem_faceUp_unique hwf hzc k hka).1)
      have hseatMid : (st.setPile a (Pile.afterRunRemoved (st.piles a)
          (below c (st.piles a).faceUp)) : State).pileOfTop z' = some k :=
        topPin2 (by
            rw [hmidK]
            exact (pileOfTop_top hk₀).2)
          (fun y hyk hya => by
            show (if y = a then Pile.afterRunRemoved (st.piles a)
                (below c (st.piles a).faceUp) else st.piles y) = st.piles y
            rw [ite_eq_right hya])
          hmidAtop (fun y hyk _ => hnostK y hyk)
      have hkeep : ∀ y, y ≠ a → y ≠ k → s₁.piles y = st.piles y := by
        intro y hya hyk
        rw [hs₁, putRun_piles_inr_ne _ _ _ _ hseatMid hyk,
          setPile_piles_ne hya]
      have hca : c ∉ (s₁.piles a).faceUp := by
        rw [hs₁, putRun_piles_inr_ne _ _ _ _ hseatMid (Ne.symm hka),
          setPile_piles_self, hbelow]
        show c ∉ (z₀ :: pre')
        rw [← hbelow]
        exact below_not_mem_self _
      have hhk : c ∈ (s₁.piles k).faceUp := by
        rw [hs₁, putRun_piles_inr_self _ _ _ _ hseatMid,
          hmidK, hrt]
        exact (List.mem_append).2 (Or.inr List.mem_cons_self)
      have hhold : s₁.pileHolding c = some k :=
        holdingPin2 hca (fun y hyk hya => hkeep y hya hyk) hhk
          (fun y hyk hya =>
            (mem_faceUp_unique hwf (pileHolding_mem hh) y hya).1)
      have hzOnly : ∀ y, y ≠ a → (s₁.piles y).top ≠ some z := by
        intro y hya
        by_cases hyk : y = k
        · rw [hyk]
          intro htop
          have hmemK : z ∈ (s₁.piles k).faceUp := Pile.mem_of_top htop
          have hkFu : (s₁.piles k).faceUp
              = (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp := by
            rw [hs₁, putRun_piles_inr_self _ _ _ _ hseatMid,
              hmidK]
          rw [hkFu, hrt] at hmemK
          have hzrun2 : z ∈ (st.piles k).faceUp ++ (c :: tr) := hmemK
          rcases (List.mem_append).1 hzrun2 with hL | hR
          · exact absurd hL ((mem_faceUp_unique hwf hzmem k hka).1)
          · rcases List.mem_cons.1 hR with heq | htr2
            · rw [heq] at hsit
              obtain ⟨hrank, -⟩ := (canSitOn_eq c c).mp hsit
              omega
            · have hrk := runOK_head_lt hrunTail htr2
              obtain ⟨hrank, -⟩ := (canSitOn_eq c z).mp hsit
              omega
        · intro htop
          rw [hkeep y hya hyk] at htop
          exact wf_no_other_top hwf hzmem y hya htop
      exact tabToTab_undo_under hs hh hzB hsit hhold
        (Or.inr ⟨z', rfl, hseatMid⟩) hkeep hcN hzOnly hzK

/-- **The slide letter**: at `WF` the shape `tabToTabR` reads
undoability exactly — unlocated head and refused bases make the
move vacuous; the reveal flip's hidden total strictly drops; the
bare non-king run head denies the no-redo seat; the bare KING
hands the whole-segment vacate play; the company-beneath row
hands the whole-segment relocation.  FLIP of
`Orig/Classify.lean:2180` (`tabToTabClass`; the `tabToTabR`
cells negate the frozen `tabToTabIrr` cells at `:2166`, per
case). -/
theorem tabToTabR_iff_reversibleAtW {st : State} (hwf : st.WF) (c : Card) (b : Base) :
    tabToTabR st c b = true ↔ reversibleAtW st (Move.tabToTab c b) := by
  cases hh : st.pileHolding c with
  | none =>
      have hcell : tabToTabR st c b = false := by
        simp only [tabToTabR, hh]
      rw [hcell]
      exact ⟨fun h => Bool.noConfusion h,
        fun w => absurd w (not_W_of_step_none (step_tabToTab_none_of_holding hh))⟩
  | some a =>
      cases hcp : st.canPlace c b with
      | false =>
          have hcell : tabToTabR st c b = false := by
            simp only [tabToTabR, hh, hcp]
          rw [hcell]
          exact ⟨fun h => Bool.noConfusion h,
            fun w => absurd w (not_W_of_step_none (step_tabToTab_none_of_cp hh hcp))⟩
      | true =>
          obtain ⟨s₁, hs⟩ := step_tabToTab_some hh hcp
          cases hbelow : below c (st.piles a).faceUp with
          | nil =>
              cases hhid : (st.piles a).hidden with
              | nil =>
                  by_cases hkng : c.rank = Rank.king
                  · have hcell : tabToTabR st c b = true := by
                      simp only [tabToTabR, hh, hcp, hbelow, hhid]
                      rw [decide_eq_true hkng]
                    rw [hcell]
                    exact ⟨fun _ =>
                      tabToTab_W_bare_king_wf hwf hh hcp hbelow hhid hkng,
                      fun _ => rfl⟩
                  · have hcell : tabToTabR st c b = false := by
                      simp only [tabToTabR, hh, hcp, hbelow, hhid]
                      rw [decide_false_of_not hkng]
                    rw [hcell]
                    have hfr : fromCard c (st.piles a).faceUp ≠ [] :=
                      fromCard_ne_of_mem (pileHolding_mem hh)
                    exact ⟨fun h => Bool.noConfusion h,
                      fun w => absurd w (tabToTab_notW_of_bare_nonking hs hh hbelow
                        hhid hfr hkng)⟩
              | cons hh1 t1 =>
                  have hcell : tabToTabR st c b = false := by
                    simp only [tabToTabR, hh, hcp, hbelow, hhid]
                  rw [hcell]
                  exact ⟨fun h => Bool.noConfusion h,
                    fun w => absurd w (not_W_of_desc hiddenTotal
                      (fun s m s' hst => hiddenTotal_step hst) hs
                      (hiddenTotal_step_tabToTab_reveal hs hh hbelow
                        (by rw [hhid]; intro hh; exact absurd hh (by simp))))⟩
          | cons z₀ pre' =>
              have hcell : tabToTabR st c b = true := by
                simp only [tabToTabR, hh, hcp, hbelow]
              rw [hcell]
              exact ⟨fun _ => tabToTab_W_under_wf hwf hh hcp hbelow, fun _ => rfl⟩

/-!
## §7. THE ASSEMBLY — THE CLAIM, DISCHARGED AND PROMOTED

The five letters tile the oracle's constructor arms — the draw
reads `drawR`, the raises `tabToFoundR`, the pulls `foundToTabR`,
the slides `tabToTabR` — and the two universal waste rows deny the
waste arms outright, so the carrier decision is exactly the
oracle's bit at every arm.  The statement below is the frozen
bank of `Orig2/Claims.lean` §1, proved here per the promotion
rule (the stub deleted there, the Claims battery line moved into
this card's battery).  FLIP of `Orig/Classify.lean:2866`
(`irreversible_iff_of`, the commit-polarity assembly) — this is
its witness-grade companion; the retired commitment grade appears
in no statement of this card.
-/

/-- **CLAIM `reversibleOf_iff_reversibleAtW`** — the oracle meets
the witness carrier exactly at `WF` worlds: both halves at
witness grade, the five letters' cells handing or denying the
carrier per constructor, no classical step anywhere. -/
theorem reversibleOf_iff_reversibleAtW {st : State} (hwf : st.WF)
    (m : Move) :
    reversibleOf st m = true ↔ reversibleAtW st m := by
  cases m with
  | draw =>
      show (drawR st = true) ↔ reversibleAtW st Move.draw
      exact drawR_iff_reversibleAtW hwf
  | wasteToFound c =>
      show (false = true) ↔ reversibleAtW st (Move.wasteToFound c)
      exact ⟨fun h => Bool.noConfusion h,
        fun w => absurd w (wasteToFound_not_reversibleAtW st c)⟩
  | wasteToTab c b =>
      show (false = true) ↔ reversibleAtW st (Move.wasteToTab c b)
      exact ⟨fun h => Bool.noConfusion h,
        fun w => absurd w (wasteToTab_not_reversibleAtW st c b)⟩
  | tabToFound c =>
      show (tabToFoundR st c = true) ↔ reversibleAtW st (Move.tabToFound c)
      exact tabToFoundR_iff_reversibleAtW hwf c
  | foundToTab c b =>
      show (foundToTabR st c b = true) ↔ reversibleAtW st (Move.foundToTab c b)
      exact foundToTabR_iff_reversibleAtW hwf c b
  | tabToTab c b =>
      show (tabToTabR st c b = true) ↔ reversibleAtW st (Move.tabToTab c b)
      exact tabToTabR_iff_reversibleAtW hwf c b

/-! ## The audit battery

Per proved head, this card.  Expected profile per the card header:
`[propext]` or `[propext, Quot.sound]` — never `sorryAx`, never
`Classical.choice`.  The claim's battery line lives here since the
promotion (see §7). -/

#print axioms wasteToFound_not_reversibleAtW
#print axioms wasteToTab_not_reversibleAtW
#print axioms drawR_iff_reversibleAtW
#print axioms tabToFoundR_iff_reversibleAtW
#print axioms foundToTabR_iff_reversibleAtW
#print axioms tabToTabR_iff_reversibleAtW
#print axioms reversibleOf_iff_reversibleAtW
