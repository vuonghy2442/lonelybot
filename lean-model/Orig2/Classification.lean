import Orig2.Vocab

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
sections; per-file private kit only; the battery at the file's
tail; frozen statements never force-premised; commits staged green
per letter, `lake build Orig2` between batches.
-/

/-!
## §0. THE WITNESS-GRADE BRIDGE  (private kit)

The vacuous denial: a refused move admits no successor, so no
witness exists — flip of `Orig/Classify.lean:1739`
`irreversibleAt_of_illegal`).  The measure denial joins it at §1a,
beside the monotone bridge it rides.  The retired commitment grade
appears nowhere in this card — the frozen physics rows are
re-landed natively at `¬ reversibleAtW` (or hand the carrier),
each with its frozen cite.
-/

/-- A refused move admits no successor, so no witness exists —
the vacuous denial, re-stated at the carrier grade (flip of
`Orig/Classify.lean:1739` `irreversibleAt_of_illegal`). -/
private theorem not_W_of_step_none {st : State} {m : Move}
    (h : State.step st m = none) : ¬ reversibleAtW st m := by
  rintro ⟨s₁, play, hstep, -⟩
  rw [h] at hstep
  exact absurd hstep (by simp)

/-!
## §1. THE PHYSICS PORT KIT  (private; the seam annex)

Everything between the core seam and the letters, re-landed from
the frozen tier reading, never imported.  Sources cited per row.
Subsections: the monotone bridge (with the measure denial that
rides it), the measures and their flat-map kit, the placement
field-keepers and guard inversions, the draw pipeline, the step
inversions, the cycle-count table, the hidden-total table.
-/

/-! ### §1a. The monotone bridge -/

/-- A play whose every legal step descends in `Q` (`Q s' ≤ Q s`)
ends at a position no higher than its start.  PORTED verbatim from
`Orig/Mono.lean:40` (`mono_run`; the frozen file rides above the
core seam via `Orig.Fate`, vetoed here — see the header). -/
private theorem mono_run (Q : State → Nat)
    (h : ∀ s m s', State.step s m = some s' → Q s' ≤ Q s) :
    ∀ {s play w}, s.run play = some w → Q w ≤ Q s := by
  intro s play
  induction play generalizing s with
  | nil =>
      intro w hw
      have hw' : some s = some w := hw
      injection hw' with he
      subst he
      exact Nat.le_refl _
  | cons m rest ih =>
      intro w hw
      obtain ⟨s₁, hstep, hrun⟩ := State.run_cons hw
      have h1 : Q s₁ ≤ Q s := h s m s₁ hstep
      have h2 : Q w ≤ Q s₁ := ih hrun
      omega

/-- A strictly descending one-step measure denies the carrier: a
returning play would walk the measure back up from below its own
start while every step only descends — the witness-grade
re-statement of `Orig/Mono.lean:82` `irr_of_desc` (same walk, the
negated existential taken directly; the frozen original is stated
at the retired grade). -/
private theorem not_W_of_desc (Q : State → Nat)
    (h : ∀ s m s', State.step s m = some s' → Q s' ≤ Q s)
    {st : State} {m : Move} {s₁ : State}
    (hstep : State.step st m = some s₁) (hdrop : Q s₁ < Q st) :
    ¬ reversibleAtW st m := by
  rintro ⟨s₁', play, hstep', hrun⟩
  rw [hstep] at hstep'
  injection hstep' with heq
  subst heq
  have hle := mono_run Q h hrun
  omega

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

/-! ### §1b. The measures and the flat-map kit -/

/-- Cards in the draw cycle: the stock plus the waste.  A draw
conserves it exactly; a waste-consuming move pops it.  PORTED
verbatim from `Orig/Irreversible.lean:66`. -/
private def cycleCount (st : State) : Nat := st.stock.length + st.waste.length

/-- The face-down cards across the seven piles, as one flat sum.
PORTED verbatim from `Orig/Irreversible.lean:71`. -/
private def hiddenTotal (st : State) : Nat :=
  (Anchor.all.flatMap fun a => (st.piles a).hidden).length

/-- Flat map unrolls one head element.  PORTED from
`Orig/Irreversible.lean:81`. -/
private theorem flatMap_cons {α β : Type} (f : α → List β) (x : α) (t : List α) :
    List.flatMap f (x :: t) = f x ++ List.flatMap f t := rfl

/-- Pointwise pile-hidden equality gives hidden-total equality.
PORTED from `Orig/Irreversible.lean:85`. -/
private theorem hiddenTotal_congr {s s' : State}
    (h : ∀ a, (s'.piles a).hidden = (s.piles a).hidden) :
    hiddenTotal s' = hiddenTotal s := by
  unfold hiddenTotal
  rw [show (fun a => (s'.piles a).hidden) = (fun a => (s.piles a).hidden) from funext h]

/-- A flat map is length-monotone in the summed function.  PORTED
from `Orig/Irreversible.lean:99`. -/
private theorem flatMap_length_mono {α : Type} (F G : α → List Card) (as : List α)
    (h : ∀ y, (G y).length ≤ (F y).length) :
    (as.flatMap G).length ≤ (as.flatMap F).length := by
  induction as with
  | nil => exact Nat.le_refl _
  | cons y t ih =>
      rw [flatMap_cons, flatMap_cons, List.length_append, List.length_append]
      exact Nat.add_le_add (h y) ih

/-- The strict version: if some witness point drops by one and
nothing grows anywhere, the total drops by at least one.  PORTED
verbatim (constructive, axiom-free) from
`Orig/Irreversible.lean:116`. -/
private theorem flatMap_length_mono_lt {α : Type} (F G : α → List Card) (as : List α) (x : α)
    (hmem : x ∈ as) (hle : ∀ y, (G y).length ≤ (F y).length)
    (hlt : (G x).length + 1 ≤ (F x).length) :
    (as.flatMap G).length + 1 ≤ (as.flatMap F).length := by
  induction as with
  | nil => exact absurd hmem (by simp)
  | cons y t ih =>
      rw [flatMap_cons, flatMap_cons, List.length_append, List.length_append]
      rcases Nat.lt_or_ge ((G y).length) ((F y).length) with hlt' | hge
      · have htail := flatMap_length_mono F G t hle
        omega
      · have hy : (G y).length = (F y).length := Nat.le_antisymm (hle y) hge
        have hne : y = x → False := by
          intro heq
          subst heq
          omega
        have hxint : x ∈ t := (List.mem_cons.mp hmem).resolve_left (fun heq => hne heq.symm)
        have hp := ih hxint
        omega

/-- Pile-wise domination gives hidden-total domination.  PORTED
from `Orig/Irreversible.lean:137`. -/
private theorem hiddenTotal_mono {s s' : State}
    (h : ∀ a, (s'.piles a).hidden.length ≤ (s.piles a).hidden.length) :
    hiddenTotal s' ≤ hiddenTotal s :=
  flatMap_length_mono _ _ _ h

/-- The strict witness lemma: dropping one pile's hidden count by
one drops the total by at least one, nothing anywhere growing.
PORTED from `Orig/Irreversible.lean:752`. -/
private theorem hiddenTotal_mono_lt {s s' : State} {a : Anchor}
    (hle : ∀ a', (s'.piles a').hidden.length ≤ (s.piles a').hidden.length)
    (hlt : (s'.piles a).hidden.length + 1 ≤ (s.piles a).hidden.length) :
    hiddenTotal s' + 1 ≤ hiddenTotal s :=
  flatMap_length_mono_lt _ _ Anchor.all a (Anchor.mem_all a) hle hlt

/-- The hidden-cards trichotomy of the run removal.  PORTED
verbatim from `Orig/Irreversible.lean:157`. -/
private theorem afterRunRemoved_hidden (p : Pile) (pre : List Card) :
    (pre ≠ [] ∧ (Pile.afterRunRemoved p pre).hidden = p.hidden) ∨
    (pre = [] ∧ p.hidden = [] ∧ (Pile.afterRunRemoved p pre).hidden = p.hidden) ∨
    (pre = [] ∧ p.hidden ≠ [] ∧
      (Pile.afterRunRemoved p pre).hidden.length + 1 = p.hidden.length) := by
  cases pre with
  | cons x xs => exact Or.inl ⟨by simp, rfl⟩
  | nil =>
      rcases p with ⟨h, f⟩
      cases h with
      | nil => exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
      | cons g gs =>
          refine Or.inr (Or.inr ⟨rfl, by simp, ?_⟩)
          show (Pile.revealTop { hidden := g :: gs, faceUp := [] } : Pile).hidden.length + 1
            = (g :: gs).length
          simp only [Pile.revealTop, List.length_cons]

/-- The hidden-count never grows through a run removal.  PORTED
from `Orig/Irreversible.lean:175`. -/
private theorem afterRunRemoved_hidden_le (p : Pile) (pre : List Card) :
    (Pile.afterRunRemoved p pre).hidden.length ≤ p.hidden.length := by
  rcases afterRunRemoved_hidden p pre with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
  · rw [h]; exact Nat.le_refl _
  · rw [h]; exact Nat.le_refl _
  · omega

/-! ### §1c. The placement field-keepers and guard inversions -/

/-- `setPile` keeps the stock.  PORTED from
`Orig/Irreversible.lean:191`. -/
private theorem setPile_stock (st : State) (a : Anchor) (p : Pile) :
    (st.setPile a p).stock = st.stock := rfl

/-- `setPile` keeps the waste.  PORTED from
`Orig/Irreversible.lean:195`. -/
private theorem setPile_waste (st : State) (a : Anchor) (p : Pile) :
    (st.setPile a p).waste = st.waste := rfl

/-- `setPile` keeps the draw step.  PORTED from
`Orig/Irreversible.lean:199`. -/
private theorem setPile_drawStep (st : State) (a : Anchor) (p : Pile) :
    (st.setPile a p).drawStep = st.drawStep := rfl

/-- `setFound` keeps the stock.  PORTED from
`Orig/Irreversible.lean:208`. -/
private theorem setFound_stock (st : State) (s : Suit) (l : List Card) :
    (st.setFound s l).stock = st.stock := rfl

/-- `setFound` keeps the waste.  PORTED from
`Orig/Irreversible.lean:212`. -/
private theorem setFound_waste (st : State) (s : Suit) (l : List Card) :
    (st.setFound s l).waste = st.waste := rfl

/-- `setFound` keeps the tableau.  PORTED from
`Orig/Irreversible.lean:216`. -/
private theorem setFound_piles (st : State) (s : Suit) (l : List Card) :
    (st.setFound s l).piles = st.piles := rfl

/-- `setFound` keeps the draw step.  PORTED from
`Orig/Irreversible.lean:220`. -/
private theorem setFound_drawStep (st : State) (s : Suit) (l : List Card) :
    (st.setFound s l).drawStep = st.drawStep := rfl

/-- `putCard` keeps the stock.  PORTED from
`Orig/Irreversible.lean:224`. -/
private theorem putCard_stock (st : State) (c : Card) (b : Base) :
    (st.putCard c b).stock = st.stock := by
  cases b with
  | inl a => rfl
  | inr z => cases hz : st.pileOfTop z <;> simp [State.putCard, hz] <;> rfl

/-- `putCard` keeps the waste.  PORTED from
`Orig/Irreversible.lean:231`. -/
private theorem putCard_waste (st : State) (c : Card) (b : Base) :
    (st.putCard c b).waste = st.waste := by
  cases b with
  | inl a => rfl
  | inr z => cases hz : st.pileOfTop z <;> simp [State.putCard, hz] <;> rfl

/-- `putCard` keeps the foundations.  PORTED from
`Orig/Irreversible.lean:238`. -/
private theorem putCard_found (st : State) (c : Card) (b : Base) :
    (st.putCard c b).found = st.found := by
  cases b with
  | inl a => rfl
  | inr z => cases hz : st.pileOfTop z <;> simp [State.putCard, hz] <;> rfl

/-- `putCard` keeps the draw step.  PORTED from
`Orig/Irreversible.lean:245`. -/
private theorem putCard_drawStep (st : State) (c : Card) (b : Base) :
    (st.putCard c b).drawStep = st.drawStep := by
  cases b with
  | inl a => rfl
  | inr z => cases hz : st.pileOfTop z <;> simp [State.putCard, hz] <;> rfl

/-- `putRun` keeps the stock.  PORTED from
`Orig/Irreversible.lean:252`. -/
private theorem putRun_stock (st : State) (run : List Card) (b : Base) :
    (st.putRun run b).stock = st.stock := by
  cases b with
  | inl a => rfl
  | inr z => cases hz : st.pileOfTop z <;> simp [State.putRun, hz] <;> rfl

/-- `putRun` keeps the waste.  PORTED from
`Orig/Irreversible.lean:259`. -/
private theorem putRun_waste (st : State) (run : List Card) (b : Base) :
    (st.putRun run b).waste = st.waste := by
  cases b with
  | inl a => rfl
  | inr z => cases hz : st.pileOfTop z <;> simp [State.putRun, hz] <;> rfl

/-- `putRun` keeps the foundations.  PORTED from
`Orig/Irreversible.lean:266`. -/
private theorem putRun_found (st : State) (run : List Card) (b : Base) :
    (st.putRun run b).found = st.found := by
  cases b with
  | inl a => rfl
  | inr z => cases hz : st.pileOfTop z <;> simp [State.putRun, hz] <;> rfl

/-- `putRun` keeps the draw step.  PORTED from
`Orig/Irreversible.lean:273`. -/
private theorem putRun_drawStep (st : State) (run : List Card) (b : Base) :
    (st.putRun run b).drawStep = st.drawStep := by
  cases b with
  | inl a => rfl
  | inr z => cases hz : st.pileOfTop z <;> simp [State.putRun, hz] <;> rfl

/-- A single card onto an empty seat writes exactly that pile to
the singleton card.  PORTED from `Orig/Irreversible.lean:281`. -/
private theorem putCard_piles_inl (st : State) (c : Card) (a : Anchor) :
    (st.putCard c (Sum.inl a)).piles =
      (fun a' => if a' = a then ⟨[], [c]⟩ else st.piles a') := rfl

/-- A single card onto a card base appends to the located pile.
PORTED from `Orig/Irreversible.lean:286`. -/
private theorem putCard_piles_inr (st : State) (c : Card) (z : Card) (k : Anchor)
    (hz : st.pileOfTop z = some k) :
    (st.putCard c (Sum.inr z)).piles =
      (fun a' => if a' = k then { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }
        else st.piles a') := by
  simp only [State.putCard, hz]
  rfl

/-- Putting a run onto an empty seat writes exactly that pile.
PORTED from `Orig/Irreversible.lean:295`. -/
private theorem putRun_piles_inl (st : State) (run : List Card) (a : Anchor) :
    (st.putRun run (Sum.inl a)).piles =
      (fun a' => if a' = a then ⟨[], run⟩ else st.piles a') := rfl

/-- Putting a run onto a card base appends to the located pile.
PORTED from `Orig/Irreversible.lean:300`. -/
private theorem putRun_piles_inr (st : State) (run : List Card) (z : Card) (k : Anchor)
    (hz : st.pileOfTop z = some k) :
    (st.putRun run (Sum.inr z)).piles =
      (fun a' => if a' = k then { st.piles k with faceUp := (st.piles k).faceUp ++ run }
        else st.piles a') := by
  simp only [State.putRun, hz]
  rfl

/-- The pointwise self read of an inl landing.  PORTED from
`Orig/Irreversible.lean:312`. -/
private theorem putRun_piles_inl_self (st : State) (run : List Card) (a : Anchor) :
    (st.putRun run (Sum.inl a)).piles a = ⟨[], run⟩ := by
  rw [putRun_piles_inl]
  exact ite_eq_left rfl

/-- The pointwise other-pile read of an inl landing.  PORTED from
`Orig/Irreversible.lean:318`. -/
private theorem putRun_piles_inl_ne (st : State) (run : List Card) (a a' : Anchor)
    (hne : a' ≠ a) :
    (st.putRun run (Sum.inl a)).piles a' = st.piles a' := by
  rw [putRun_piles_inl]
  exact ite_eq_right hne

/-- The pointwise self read of an inr landing.  PORTED from
`Orig/Irreversible.lean:325`. -/
private theorem putRun_piles_inr_self (st : State) (run : List Card) (z : Card)
    (k : Anchor) (hz : st.pileOfTop z = some k) :
    (st.putRun run (Sum.inr z)).piles k
      = { st.piles k with faceUp := (st.piles k).faceUp ++ run } := by
  rw [putRun_piles_inr _ _ _ _ hz]
  exact ite_eq_left rfl

/-- The pointwise other-pile read of an inr landing.  PORTED from
`Orig/Irreversible.lean:333`. -/
private theorem putRun_piles_inr_ne (st : State) (run : List Card) (z : Card)
    (k : Anchor) (hz : st.pileOfTop z = some k) {a' : Anchor}
    (hne : a' ≠ k) :
    (st.putRun run (Sum.inr z)).piles a' = st.piles a' := by
  rw [putRun_piles_inr _ _ _ _ hz]
  exact ite_eq_right hne

/-- The empty-seat placement guard: empty target, king card.
PORTED from `Orig/Irreversible.lean:343`. -/
private theorem canPlace_inl {st : State} {c : Card} {a : Anchor}
    (h : st.canPlace c (Sum.inl a) = true) :
    (st.piles a).isEmpty = true ∧ c.rank = Rank.king := by
  simp only [State.canPlace, Bool.and_eq_true] at h
  exact ⟨h.1, of_decide_eq_true h.2⟩

/-- The card-on-card placement guard: the base card tops some pile
and the mover fits under it.  PORTED from
`Orig/Irreversible.lean:351`. -/
private theorem canPlace_inr {st : State} {c z : Card}
    (h : st.canPlace c (Sum.inr z) = true) :
    ∃ k, st.pileOfTop z = some k ∧ canSitOn c z = true := by
  simp only [State.canPlace] at h
  cases hz : st.pileOfTop z with
  | none => rw [hz] at h; exact absurd h (by simp)
  | some k => rw [hz] at h; exact ⟨k, rfl, h⟩

/-- A pile is empty iff both of its parts are.  PORTED from
`Orig/Integrity.lean:69`. -/
private theorem Pile.isEmpty_eq (p : Pile) :
    p.isEmpty = true ↔ p.hidden = [] ∧ p.faceUp = [] := by
  rcases p with ⟨h, f⟩
  cases h <;> cases f <;> simp [Pile.isEmpty]

/-- A pile holding `c` face up is not empty.  PORTED from
`Orig/Irreversible.lean:742`. -/
private theorem Pile.isEmpty_eq_false_of_mem {p : Pile} {c : Card}
    (h : c ∈ p.faceUp) : p.isEmpty = false := by
  rcases p with ⟨hd, f⟩
  cases f with
  | nil => cases h
  | cons x fs => cases hd <;> rfl

/-- A legal placement never disturbs hidden cards.  PORTED from
`Orig/Irreversible.lean:646`. -/
private theorem putCard_hidden_eq {st : State} {c : Card} {b : Base}
    (hcp : st.canPlace c b = true) (a' : Anchor) :
    ((st.putCard c b).piles a').hidden = (st.piles a').hidden := by
  cases b with
  | inl a =>
      obtain ⟨hemp, -⟩ := canPlace_inl hcp
      obtain ⟨hhd, -⟩ := (Pile.isEmpty_eq _).mp hemp
      simp only [putCard_piles_inl]
      by_cases hae : a' = a
      · subst hae
        rw [ite_eq_left rfl, hhd]
      · rw [ite_eq_right hae]
  | inr z =>
      obtain ⟨k, hz, -⟩ := canPlace_inr hcp
      simp only [putCard_piles_inr _ _ _ _ hz]
      by_cases hae : a' = k
      · subst hae
        rw [ite_eq_left rfl]
      · rw [ite_eq_right hae]

/-- The intermediate `setPile` of the run removal never enlarges a
pile's hidden cards.  PORTED from `Orig/Irreversible.lean:669`. -/
private theorem setPile_afterRunRemoved_hidden_le (st : State) (a : Anchor) (c : Card)
    (a' : Anchor) :
    ((st.setPile a
      (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles a').hidden.length
        ≤ (st.piles a').hidden.length := by
  by_cases hae : a' = a
  · subst hae
    simp only [State.setPile]
    rw [ite_true]
    exact afterRunRemoved_hidden_le _ _
  · simp only [State.setPile]
    rw [ite_eq_right hae]
    exact Nat.le_refl _

/-- The run-removal `setPile`, read at its own pile.  PORTED from
`Orig/Irreversible.lean:850`. -/
private theorem setPile_afterRunRemoved_piles_self (st : State) (a : Anchor) (c : Card) :
    (st.setPile a
      (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles a
      = Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp) := by
  simp only [State.setPile]
  rw [ite_true]

/-- The run-removal `setPile` leaves every other pile alone.
PORTED from `Orig/Irreversible.lean:858`. -/
private theorem setPile_afterRunRemoved_piles_ne (st : State) (a : Anchor) (c : Card)
    (a' : Anchor) (hne : a' ≠ a) :
    (st.setPile a
      (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles a'
      = st.piles a' := by
  simp only [State.setPile]
  rw [ite_eq_right hne]

/-! ### §1d. The draw pipeline -/

/-- `dealUpTo` splits without loss.  PORTED from
`Orig/Irreversible.lean:373`. -/
private theorem dealUpTo_length (k : Nat) : ∀ (l : List Card),
    (State.dealUpTo k l).1.length + (State.dealUpTo k l).2.length = l.length := by
  intro l
  induction k generalizing l with
  | zero => simp [State.dealUpTo]
  | succ n ih =>
      cases l with
      | nil => simp [State.dealUpTo]
      | cons x t =>
          show (x :: (State.dealUpTo n t).1).length + (State.dealUpTo n t).2.length
            = (x :: t).length
          have h1 : (x :: (State.dealUpTo n t).1).length = (State.dealUpTo n t).1.length + 1 := rfl
          have h2 : (x :: t).length = t.length + 1 := rfl
          rw [h1, h2]
          have h3 := ih t
          omega

/-- Recycling keeps the cycle count.  PORTED from
`Orig/Irreversible.lean:392`. -/
private theorem recycle_cycle (st : State) : cycleCount st.recycle = cycleCount st := by
  cases hs : st.stock with
  | nil =>
      cases hw : st.waste with
      | nil => rw [show st.recycle = st from by simp only [State.recycle, hs, hw]]
      | cons x t =>
          rw [show st.recycle = { st with stock := (x :: t).reverse, waste := [] } from by
              simp only [State.recycle, hs, hw]]
          simp only [cycleCount, List.length_reverse, hs, hw, List.length_cons, List.length_nil]
          omega
  | cons y s =>
      rw [show st.recycle = st from by simp only [State.recycle, hs]]

/-- Recycling keeps the piles.  PORTED from
`Orig/Irreversible.lean:406`. -/
private theorem recycle_piles (st : State) : st.recycle.piles = st.piles := by
  cases hs : st.stock <;> cases hw : st.waste <;>
    simp only [State.recycle, hs, hw]

/-- Recycling keeps the foundations.  PORTED from
`Orig/Irreversible.lean:411`. -/
private theorem recycle_found (st : State) : st.recycle.found = st.found := by
  cases hs : st.stock <;> cases hw : st.waste <;>
    simp only [State.recycle, hs, hw]

/-- A successful `dealStock` is the split literal.  PORTED from
`Orig/Irreversible.lean:417`. -/
private theorem dealStock_inv {rt : State} {s' : State}
    (h : State.dealStock rt = some s') :
    rt.stock ≠ [] ∧
      s' = { rt with
             stock := (State.dealUpTo rt.drawStep rt.stock).2,
             waste := (State.dealUpTo rt.drawStep rt.stock).1.reverse ++ rt.waste } := by
  cases hs : rt.stock with
  | nil =>
      rw [show State.dealStock rt = none from by simp only [State.dealStock, hs]] at h
      exact absurd h (by simp)
  | cons x t =>
      refine ⟨by simp, ?_⟩
      rw [show State.dealStock rt =
            some { rt with
                   stock := (State.dealUpTo rt.drawStep (x :: t)).2,
                   waste := (State.dealUpTo rt.drawStep (x :: t)).1.reverse ++ rt.waste } from by
              simp only [State.dealStock, hs]] at h
      injection h with hEq
      exact hEq.symm

/-- A successful draw keeps the piles.  PORTED from
`Orig/Irreversible.lean:438`. -/
private theorem stepDraw_piles {st s' : State} (h : st.stepDraw = some s') :
    s'.piles = st.piles := by
  have hd : State.dealStock st.recycle = some s' := h
  obtain ⟨-, hEq⟩ := dealStock_inv hd
  rw [hEq]
  rw [show st.recycle.piles = st.piles from recycle_piles st]

/-- A successful draw keeps the foundations.  PORTED from
`Orig/Irreversible.lean:445`. -/
private theorem stepDraw_found {st s' : State} (h : st.stepDraw = some s') :
    s'.found = st.found := by
  have hd : State.dealStock st.recycle = some s' := h
  obtain ⟨-, hEq⟩ := dealStock_inv hd
  rw [hEq]
  rw [show st.recycle.found = st.found from recycle_found st]

/-- A successful draw conserves the cycle count exactly.  PORTED
from `Orig/Irreversible.lean:454`. -/
private theorem stepDraw_cycle {st s' : State} (h : st.stepDraw = some s') :
    cycleCount s' = cycleCount st := by
  have hd : State.dealStock st.recycle = some s' := h
  obtain ⟨-, hEq⟩ := dealStock_inv hd
  have hsplit := dealUpTo_length (st.recycle).drawStep (st.recycle).stock
  have e1 : s'.stock =
      (State.dealUpTo (st.recycle).drawStep (st.recycle).stock).2 := by
    rw [hEq]
  have e2 : s'.waste =
      (State.dealUpTo (st.recycle).drawStep (st.recycle).stock).1.reverse
        ++ (st.recycle).waste := by
    rw [hEq]
  show s'.stock.length + s'.waste.length = st.stock.length + st.waste.length
  rw [e1, e2, List.length_append, List.length_reverse]
  have hrc : (st.recycle).stock.length + (st.recycle).waste.length
      = st.stock.length + st.waste.length := recycle_cycle st
  omega

/-! ### §1e. The step inversions -/

/-- A successful `.wasteToFound`: the guard held, the waste was
nonempty, and the successor is the written foundation with the
waste popped.  PORTED from `Orig/Irreversible.lean:476`. -/
private theorem step_wasteToFound_inv {st : State} {c : Card} {s' : State}
    (h : State.step st (Move.wasteToFound c) = some s') :
    (st.wasteIs c && st.nextUp c) = true ∧
    ∃ x xs, st.waste = x :: xs ∧
      s' = { st.setFound c.suit (st.found c.suit ++ [c]) with waste := xs } := by
  simp only [State.step] at h
  split at h
  · rename_i hg
    split at h
    · rename_i _ x xs hw
      injection h with hEq
      exact ⟨hg, x, xs, hw, hEq.symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A successful `.wasteToTab`.  PORTED from
`Orig/Irreversible.lean:493`. -/
private theorem step_wasteToTab_inv {st : State} {c : Card} {b : Base} {s' : State}
    (h : State.step st (Move.wasteToTab c b) = some s') :
    (st.wasteIs c && st.canPlace c b) = true ∧
    ∃ x xs, st.waste = x :: xs ∧
      s' = { st.putCard c b with waste := xs } := by
  simp only [State.step] at h
  split at h
  · rename_i hg
    split at h
    · rename_i _ x xs hw
      injection h with hEq
      exact ⟨hg, x, xs, hw, hEq.symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A successful `.tabToFound`.  PORTED from
`Orig/Irreversible.lean:511`. -/
private theorem step_tabToFound_inv {st : State} {c : Card} {s' : State}
    (h : State.step st (Move.tabToFound c) = some s') :
    st.nextUp c = true ∧
    ∃ a, st.pileOfTop c = some a ∧
      s' = { st.setFound c.suit (st.found c.suit ++ [c]) with
             piles := fun a' =>
               if a' = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
               else st.piles a' } := by
  simp only [State.step] at h
  split at h
  · rename_i hn
    split at h
    · exact absurd h (by simp)
    · rename_i _ a hp
      injection h with hEq
      exact ⟨hn, a, hp, hEq.symm⟩
  · exact absurd h (by simp)

/-- The tabToFound-landing's foundation trio.  PORTED from
`Orig/Irreversible.lean:534`. -/
private theorem tabToFound_found_trio {st s₁ : State} {c : Card} {a : Anchor}
    (hs₁ : s₁ = { st.setFound c.suit (st.found c.suit ++ [c]) with
                   piles := fun a' =>
                     if a' = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
                     else st.piles a' }) :
    s₁.found c.suit = st.found c.suit ++ [c] ∧
    (∀ σ, σ ≠ c.suit → s₁.found σ = st.found σ) ∧
    s₁.foundTop c.suit = some c := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hs₁]
    exact setFound_found_self
  · intro σ hσ
    rw [hs₁]
    exact setFound_found_ne hσ
  · show lastOf (s₁.found c.suit) = some c
    rw [hs₁, setFound_found_self]
    exact lastOf_snoc

/-- A successful `.foundToTab`.  PORTED from
`Orig/Irreversible.lean:555`. -/
private theorem step_foundToTab_inv {st : State} {c : Card} {b : Base} {s' : State}
    (h : State.step st (Move.foundToTab c b) = some s') :
    ∃ c', st.foundTop c.suit = some c' ∧ c' = c ∧ st.canPlace c b = true ∧
      s' = (st.setFound c.suit (chop (st.found c.suit))).putCard c b := by
  simp only [State.step] at h
  split at h
  · split at h
    · rename_i _ c' ht hg
      rw [Bool.and_eq_true] at hg
      injection h with hEq
      exact ⟨c', ht, of_decide_eq_true hg.1, hg.2, hEq.symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A successful `.tabToTab`.  PORTED from
`Orig/Irreversible.lean:572`. -/
private theorem step_tabToTab_inv {st : State} {c : Card} {b : Base} {s' : State}
    (h : State.step st (Move.tabToTab c b) = some s') :
    ∃ a, st.pileHolding c = some a ∧ st.canPlace c b = true ∧
      fromCard c (st.piles a).faceUp ≠ [] ∧
        s' = (st.setPile a
            (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
              (fromCard c (st.piles a).faceUp) b := by
  simp only [State.step] at h
  split at h
  · exact absurd h (by simp)
  · rename_i _ a hh
    split at h
    · rename_i hcp
      split at h
      · exact absurd h (by simp)
      · rename_i _ hne
        injection h with hEq
        exact ⟨a, hh, hcp, hne, hEq.symm⟩
    · exact absurd h (by simp)

/-! ### §1f. The cycle-count table -/

/-- Soundness of the `pileHolding` search: if the search answers
`a`, the card really is face up in that pile.  PORTED verbatim
from `Orig/Integrity.lean:493`. -/
private theorem pileHolding_mem {st : State} {c : Card} {a : Anchor}
    (h : st.pileHolding c = some a) : c ∈ (st.piles a).faceUp :=
  of_decide_eq_true (firstWhere_sound (p := fun a' => decide (c ∈ (st.piles a').faceUp)) h)

/-- Same stock and waste give the same cycle count.  PORTED from
`Orig/Irreversible.lean:685`. -/
private theorem cycleCount_eq_of_stock_waste {s s' : State}
    (hst : s'.stock = s.stock) (hwa : s'.waste = s.waste) :
    cycleCount s' = cycleCount s := by
  show s'.stock.length + s'.waste.length = s.stock.length + s.waste.length
  rw [hst, hwa]

/-- A successful `.wasteToFound` pops the waste, so the cycle
count strictly drops.  PORTED from `Orig/Irreversible.lean:692`. -/
private theorem cycleCount_step_wasteToFound {st : State} {c : Card} {s' : State}
    (h : State.step st (Move.wasteToFound c) = some s') :
    cycleCount s' + 1 ≤ cycleCount st := by
  obtain ⟨-, x, xs, hw, hs⟩ := step_wasteToFound_inv h
  rw [hs]
  show st.stock.length + xs.length + 1 ≤ st.stock.length + st.waste.length
  rw [hw]
  simp only [List.length_cons]
  omega

/-- A successful `.wasteToTab` pops the waste, so the cycle count
strictly drops.  PORTED from `Orig/Irreversible.lean:704`. -/
private theorem cycleCount_step_wasteToTab {st : State} {c : Card} {b : Base} {s' : State}
    (h : State.step st (Move.wasteToTab c b) = some s') :
    cycleCount s' + 1 ≤ cycleCount st := by
  obtain ⟨-, x, xs, hw, hs⟩ := step_wasteToTab_inv h
  rw [hs]
  show (st.putCard c b).stock.length + xs.length + 1 ≤ st.stock.length + st.waste.length
  rw [putCard_stock, hw]
  simp only [List.length_cons]
  omega

/-- Table 1: no legal single move ever raises the draw-cycle count.
PORTED from `Orig/Irreversible.lean:718`. -/
private theorem cycleCount_step {st : State} {m : Move} {s' : State}
    (h : State.step st m = some s') : cycleCount s' ≤ cycleCount st := by
  cases m with
  | draw => have := stepDraw_cycle h; omega
  | wasteToFound c => have := cycleCount_step_wasteToFound h; omega
  | wasteToTab c b => have := cycleCount_step_wasteToTab h; omega
  | tabToFound c =>
      obtain ⟨-, a, -, hs⟩ := step_tabToFound_inv h
      rw [hs]
      exact Nat.le_of_eq (cycleCount_eq_of_stock_waste rfl rfl)
  | foundToTab c b =>
      obtain ⟨-, -, -, -, hs⟩ := step_foundToTab_inv h
      rw [hs]
      exact Nat.le_of_eq (cycleCount_eq_of_stock_waste (putCard_stock _ _ _)
        (by rw [putCard_waste]; rfl))
  | tabToTab c b =>
      obtain ⟨a, -, -, -, hs⟩ := step_tabToTab_inv h
      rw [hs]
      exact Nat.le_of_eq (cycleCount_eq_of_stock_waste (putRun_stock _ _ _)
        (by rw [putRun_waste]; rfl))

/-! ### §1g. The hidden-total table -/

/-- The from-pile hidden facts of a successful `.tabToFound`, per
anchor.  PORTED from `Orig/Irreversible.lean:769`. -/
private theorem tabToFound_pile_le (st : State) (c : Card) (a : Anchor) (a' : Anchor) :
    (({ st.setFound c.suit (st.found c.suit ++ [c]) with
       piles := fun a'' =>
        if a'' = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
        else st.piles a'' } : State).piles a').hidden.length
      ≤ (st.piles a').hidden.length := by
  show (if a' = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
      else st.piles a').hidden.length ≤ (st.piles a').hidden.length
  by_cases hae : a' = a
  · subst hae
    rw [ite_eq_left rfl]
    exact afterRunRemoved_hidden_le _ _
  · rw [ite_eq_right hae]
    exact Nat.le_refl _

/-- A successful `.tabToTab` moves the whole run headed by `c`, so
the source pile's hidden cards after the successor are exactly the
run removal's.  PORTED from `Orig/Irreversible.lean:908`. -/
private theorem tabToTab_a_hidden (st : State) (a : Anchor) (c : Card) (b : Base)
    (hmem : c ∈ (st.piles a).faceUp) (hcp : st.canPlace c b = true) :
    (((st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
          (fromCard c (st.piles a).faceUp) b).piles a).hidden
      = (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp)).hidden := by
  cases b with
  | inl a₁ =>
      obtain ⟨hemp, -⟩ := canPlace_inl hcp
      have hfa : (st.piles a).isEmpty = false := Pile.isEmpty_eq_false_of_mem hmem
      have hne : a₁ ≠ a := by
        intro heq
        rw [heq] at hemp
        exact absurd hemp (by rw [hfa]; simp)
      simp only [putRun_piles_inl]
      rw [ite_eq_right (Ne.symm hne), setPile_afterRunRemoved_piles_self st a c]
  | inr z =>
      cases hz : (st.setPile a
          (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).pileOfTop z with
      | none =>
          have hR : (st.setPile a
              (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
                (fromCard c (st.piles a).faceUp) (Sum.inr z)
              = (st.setPile a
                (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))) := by
            simp only [State.putRun, hz]
          rw [hR, setPile_afterRunRemoved_piles_self st a c]
      | some k =>
          by_cases hka : k = a
          · simp only [putRun_piles_inr _ _ _ _ hz]
            rw [hka, ite_eq_left rfl]
            show ((st.setPile a
                (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles a).hidden
              = (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp)).hidden
            rw [setPile_afterRunRemoved_piles_self st a c]
          · simp only [putRun_piles_inr _ _ _ _ hz]
            rw [ite_eq_right (Ne.symm hka)]
            show ((st.setPile a
                (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles a).hidden
              = (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp)).hidden
            rw [setPile_afterRunRemoved_piles_self st a c]

/-- Per-anchor hidden domination for a `.tabToTab` successor.
PORTED from `Orig/Irreversible.lean:867`. -/
private theorem tabToTab_pile_le (st : State) (a : Anchor) (c : Card) (b : Base)
    (a' : Anchor) :
    (((st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
          (fromCard c (st.piles a).faceUp) b).piles a').hidden.length
      ≤ (st.piles a').hidden.length := by
  cases b with
  | inl a₁ =>
      simp only [putRun_piles_inl]
      by_cases hae : a' = a₁
      · rw [hae, ite_eq_left rfl]
        exact Nat.zero_le _
      · rw [ite_eq_right hae]
        exact setPile_afterRunRemoved_hidden_le st a c a'
  | inr z =>
      cases hz : (st.setPile a
          (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).pileOfTop z with
      | none =>
          have hR : (st.setPile a
              (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
                (fromCard c (st.piles a).faceUp) (Sum.inr z)
              = (st.setPile a
                (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))) := by
            simp only [State.putRun, hz]
          rw [hR]
          exact setPile_afterRunRemoved_hidden_le st a c a'
      | some k =>
          simp only [putRun_piles_inr _ _ _ _ hz]
          by_cases hae : a' = k
          · rw [hae, ite_eq_left rfl]
            show ((st.setPile a
                (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k).hidden.length
              ≤ (st.piles k).hidden.length
            exact setPile_afterRunRemoved_hidden_le st a c k
          · rw [ite_eq_right hae]
            exact setPile_afterRunRemoved_hidden_le st a c a'

/-- A successful `.tabToTab` that empties the from-pile's face-up
prefix over a nonempty hidden stack reveals one card: the hidden
total drops by at least one.  PORTED from
`Orig/Irreversible.lean:953`. -/
private theorem hiddenTotal_step_tabToTab_reveal {st : State} {c : Card} {b : Base}
    {a : Anchor} {s' : State} (h : State.step st (Move.tabToTab c b) = some s')
    (hh : st.pileHolding c = some a)
    (hrev : below c (st.piles a).faceUp = []) (hhne : (st.piles a).hidden ≠ []) :
    hiddenTotal s' + 1 ≤ hiddenTotal st := by
  obtain ⟨a₀, hh2, hcp, -, hs⟩ := step_tabToTab_inv h
  rw [hh2] at hh
  injection hh with haa
  rw [haa] at hs
  have hmem : c ∈ (st.piles a).faceUp := by
    have := pileHolding_mem hh2
    rw [haa] at this
    exact this
  rw [hs]
  refine hiddenTotal_mono_lt (a := a) ?_ ?_
  · intro a'
    exact tabToTab_pile_le st a c b a'
  · rw [tabToTab_a_hidden st a c b hmem hcp, hrev]
    rcases afterRunRemoved_hidden (st.piles a) [] with ⟨hne, -⟩ | ⟨-, hhd, -⟩ | ⟨-, -, hdrop⟩
    · exact absurd rfl hne
    · exact absurd hhne (by simp [hhd])
    · omega

/-- A successful `.tabToFound` that empties the from-pile's face-up
run over a nonempty hidden stack reveals one card: the hidden total
drops by at least one.  PORTED from
`Orig/Irreversible.lean:1219`. -/
private theorem hiddenTotal_step_tabToFound_reveal {st : State} {c : Card} {a : Anchor}
    {s' : State} (h : State.step st (Move.tabToFound c) = some s')
    (hpa : st.pileOfTop c = some a)
    (hrev : chop (st.piles a).faceUp = []) (hhne : (st.piles a).hidden ≠ []) :
    hiddenTotal s' + 1 ≤ hiddenTotal st := by
  obtain ⟨-, a₀, hp2, hs⟩ := step_tabToFound_inv h
  rw [hp2] at hpa
  injection hpa with haa
  rw [haa] at hs
  rw [hs]
  refine hiddenTotal_mono_lt (a := a) ?_ ?_
  · intro a'
    exact tabToFound_pile_le st c a a'
  · simp only [ite_true]
    rw [hrev]
    rcases afterRunRemoved_hidden (st.piles a) [] with ⟨hne, -⟩ | ⟨-, hhd, -⟩ | ⟨-, -, hdrop⟩
    · exact absurd rfl hne
    · exact absurd hhne (by simp [hhd])
    · omega

/-- Table 2: no legal single move ever turns a face-down card face
up.  PORTED from `Orig/Irreversible.lean:786`. -/
private theorem hiddenTotal_step {st : State} {m : Move} {s' : State}
    (h : State.step st m = some s') : hiddenTotal s' ≤ hiddenTotal st := by
  cases m with
  | draw =>
      have hp := stepDraw_piles h
      exact Nat.le_of_eq (hiddenTotal_congr (fun a => by rw [hp]))
  | wasteToFound c =>
      obtain ⟨-, x, xs, -, hs⟩ := step_wasteToFound_inv h
      rw [hs]
      exact Nat.le_of_eq (hiddenTotal_congr (fun _ => rfl))
  | wasteToTab c b =>
      obtain ⟨hg, x, xs, -, hs⟩ := step_wasteToTab_inv h
      have hcp : st.canPlace c b = true := by
        cases hcap : st.canPlace c b with
        | true => rfl
        | false => rw [hcap] at hg; simp at hg
      rw [hs]
      exact Nat.le_of_eq (hiddenTotal_congr (putCard_hidden_eq hcp))
  | tabToFound c =>
      obtain ⟨-, a, -, hs⟩ := step_tabToFound_inv h
      rw [hs]
      exact hiddenTotal_mono (fun a' => tabToFound_pile_le st c a a')
  | foundToTab c b =>
      obtain ⟨-, -, -, hcp, hs⟩ := step_foundToTab_inv h
      rw [hs]
      refine Nat.le_of_eq (hiddenTotal_congr (putCard_hidden_eq hcp))
  | tabToTab c b =>
      obtain ⟨a, hh, hcp, -, hs⟩ := step_tabToTab_inv h
      rw [hs]
      refine hiddenTotal_mono ?_
      intro a'
      cases b with
      | inl a₁ =>
          simp only [putRun_piles_inl]
          by_cases hae : a' = a₁
          · subst hae
            rw [ite_eq_left rfl]
            exact Nat.zero_le _
          · rw [ite_eq_right hae]
            exact setPile_afterRunRemoved_hidden_le st a c a'
      | inr z =>
          cases hz : (st.setPile a
              (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).pileOfTop z with
          | none =>
              have hR : (st.setPile a
                  (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
                    (fromCard c (st.piles a).faceUp) (Sum.inr z)
                  = (st.setPile a
                    (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))) := by
                simp only [State.putRun, hz]
              rw [hR]
              exact setPile_afterRunRemoved_hidden_le st a c a'
          | some k =>
              simp only [putRun_piles_inr _ _ _ _ hz]
              by_cases hae : a' = k
              · rw [hae, ite_eq_left rfl]
                show ((st.setPile a
                    (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k).hidden.length
                  ≤ (st.piles k).hidden.length
                exact setPile_afterRunRemoved_hidden_le st a c k
              · rw [ite_eq_right hae]
                exact setPile_afterRunRemoved_hidden_le st a c a'

/-! ### §1h. The deal-split kit and the phase line

`Orig.Phase`'s draw algebra, ported reading: the `dealUpTo`
length facts, the recycled-pipeline conservation rows, and the
phase predicate with its decisive rows (the trap: every recycled
draw lands phase-aligned, and alignment is preserved by every
draw).
-/

/-- Lengths of the `dealUpTo` split.  PORTED verbatim from
`Orig/Phase.lean:123`. -/
private theorem dealUpTo_lens (k : Nat) : ∀ (l : List Card),
    (State.dealUpTo k l).1.length = min k l.length ∧
    (State.dealUpTo k l).1.length + (State.dealUpTo k l).2.length = l.length := by
  induction k with
  | zero =>
      intro l
      refine ⟨?_, ?_⟩
      · exact (Nat.min_eq_left (Nat.zero_le l.length)).symm
      · exact Nat.zero_add l.length
  | succ k ih =>
      intro l
      cases l with
      | nil =>
          refine ⟨?_, ?_⟩
          · exact (Nat.min_eq_right (Nat.zero_le (k + 1))).symm
          · rfl
      | cons c cs =>
          obtain ⟨h1, h2⟩ := ih cs
          have hs1 : (State.dealUpTo (k + 1) (c :: cs)).1.length
              = (State.dealUpTo k cs).1.length + 1 := rfl
          have hs2 : (State.dealUpTo (k + 1) (c :: cs)).2.length
              = (State.dealUpTo k cs).2.length := rfl
          have hlen : (c :: cs).length = (cs).length + 1 := rfl
          rw [hs1, hs2, hlen]
          rcases Nat.lt_or_ge k cs.length with hlt | hge
          · rw [Nat.min_eq_left (Nat.le_of_lt hlt)] at h1
            refine ⟨?_, ?_⟩
            · rw [h1, Nat.min_eq_left (Nat.succ_le_succ (Nat.le_of_lt hlt))]
            · omega
          · rw [Nat.min_eq_right hge] at h1
            refine ⟨?_, ?_⟩
            · rw [h1, Nat.min_eq_right (Nat.succ_le_succ hge)]
            · omega

/-- A full deal: when the list has no more than `k` cards, every
card is dealt and nothing remains.  PORTED verbatim from
`Orig/Phase.lean:159`. -/
private theorem dealUpTo_all (k : Nat) : ∀ (l : List Card), l.length ≤ k →
    State.dealUpTo k l = (l, ([] : List Card)) := by
  induction k with
  | zero =>
      intro l hlen
      have hnil : l = [] := List.length_eq_zero_iff.mp (by omega)
      rw [hnil]
      rfl
  | succ k ih =>
      intro l hlen
      cases l with
      | nil => rfl
      | cons c cs =>
          have hcc : (c :: cs).length = cs.length + 1 := List.length_cons
          have hcs : cs.length ≤ k := by omega
          have hrs := ih cs hcs
          show State.dealUpTo (k+1) (c :: cs) = _
          rw [State.dealUpTo, hrs]

/-- A full deal: when the stock has no more cards than one deal, all
of the stock is dealt onto the waste and nothing remains.  PORTED
verbatim from `Orig/Phase.lean:195`. -/
private theorem dealStock_full {st : State} (hs : st.stock ≠ [])
    (hsize : st.stock.length ≤ st.drawStep) :
    State.dealStock st = some
      { st with stock := ([] : List Card), waste := st.stock.reverse ++ st.waste } := by
  rw [dealStock_eq_of_ne_nil st hs, dealUpTo_all st.drawStep st.stock hsize]

/-- A draw conserves the cycle count.  PORTED from
`Orig/Phase.lean:204`, the recycle row restated over §1d's
`recycle_cycle` (the frozen proof rides `Orig.Fate`, not in this
import graph). -/
private theorem draw_cycleCount {x y : State} (hsuc : x.stepDraw = some y) :
    cycleCount y = cycleCount x := by
  obtain ⟨r, hrec, hrne, hy⟩ := draw_unfold hsuc
  have hrc : r.stock.length + r.waste.length = x.stock.length + x.waste.length := by
    rw [← hrec]
    exact recycle_cycle x
  have hyW : y.waste = (State.dealUpTo r.drawStep r.stock).1.reverse ++ r.waste := by
    rw [hy]
  have hyS : y.stock = (State.dealUpTo r.drawStep r.stock).2 := by
    rw [hy]
  obtain ⟨_, h2⟩ := dealUpTo_lens r.drawStep r.stock
  have hcx : cycleCount x = x.stock.length + x.waste.length := rfl
  have hcy : cycleCount y = r.stock.length + r.waste.length := by
    show y.stock.length + y.waste.length = r.stock.length + r.waste.length
    rw [hyS, hyW, List.length_append, List.length_reverse]
    omega
  omega

/-- Recycling leaves the draw step alone.  PORTED verbatim from
`Orig/Phase.lean:247`. -/
private theorem recycle_drawStep (st : State) :
    (State.recycle st).drawStep = st.drawStep := by
  by_cases hst : st.stock = []
  · by_cases hw : st.waste = []
    · rw [recycle_allEmpty st hst hw]
    · rw [recycle_nil st hst hw]
  · rw [recycle_keep st hst]

/-- Every state along a draw has the same draw step as its parent.
PORTED verbatim from `Orig/Phase.lean:256`. -/
private theorem draw_drawStep {x y : State} (hsuc : x.stepDraw = some y) :
    y.drawStep = x.drawStep := by
  obtain ⟨r, hrec, hrne, hy⟩ := draw_unfold hsuc
  have hyD : y.drawStep = r.drawStep := by
    rw [hy]
  rw [hyD, ← hrec]
  exact recycle_drawStep x

/-- The toolchain's Boolean dichotomy.  PORTED from
`Orig/Phase.lean:55`. -/
private theorem bool_dich (b : Bool) : b = true ∨ b = false := by
  cases b <;> simp

/-- `true` exactly at the phase boundaries of the draw cycle: no
cards remain in the stock ("at the end"), or the waste holds a
whole number of deals so the next recycle would begin cleanly.
PORTED verbatim from `Orig/Phase.lean:63`. -/
private def inPhase (st : State) : Bool :=
  match st.stock with
  | [] => true
  | _ => decide (st.waste.length % st.drawStep = 0)

/-- With cards left in the stock, `inPhase` is literally the decide
on the waste residue.  PORTED verbatim from `Orig/Phase.lean:70`.
-/
private theorem inPhase_eq_decide_of_cons {st : State} {c : Card} {t : List Card}
    (hcon : st.stock = c :: t) :
    inPhase st = decide (st.waste.length % st.drawStep = 0) := by
  simp only [inPhase, hcon]

/-- `inPhase` depends only on the stock, the waste, and the draw
step.  PORTED verbatim from `Orig/Phase.lean:76`. -/
private theorem inPhase_congr {x y : State} (h1 : x.stock = y.stock)
    (h2 : x.waste = y.waste) (h3 : x.drawStep = y.drawStep) :
    inPhase x = inPhase y := by
  simp only [inPhase, h1, h2, h3]

/-- No stock cards means aligned: the cycle sits at its end.
PORTED verbatim from `Orig/Phase.lean:82`. -/
private theorem inPhase_eq_true_of_nil {st : State} (hnil : st.stock = []) :
    inPhase st = true := by
  simp only [inPhase, hnil]

/-- `inPhase = false` is exactly the offset condition.  PORTED
verbatim from `Orig/Phase.lean:88`. -/
private theorem inPhase_eq_false_iff {st : State} :
    inPhase st = false ↔ st.stock ≠ [] ∧ st.waste.length % st.drawStep ≠ 0 := by
  constructor
  · intro h
    by_cases hst : st.stock = []
    · rw [inPhase_eq_true_of_nil hst] at h
      exact absurd h (by simp)
    · obtain ⟨c, t, hcon⟩ := list_cons_of_ne_nil hst
      rw [inPhase_eq_decide_of_cons hcon] at h
      exact ⟨hst, of_decide_eq_false h⟩
  · rintro ⟨hst, hres⟩
    obtain ⟨c, t, hcon⟩ := list_cons_of_ne_nil hst
    rw [inPhase_eq_decide_of_cons hcon, decide_eq_false hres]

/-- **The first half of the trap.**  A draw fired at the end of the
stock (a recycle) lands phase-aligned.  PORTED verbatim from
`Orig/Phase.lean:268`. -/
private theorem draw_nil_inPhase {x y : State} (hst : x.stock = [])
    (hsuc : x.stepDraw = some y) : inPhase y = true := by
  obtain ⟨r, hrec, hrne, hy⟩ := draw_unfold hsuc
  by_cases hw : x.waste = []
  · exfalso
    have hrx : r = x := hrec.symm.trans (recycle_allEmpty x hst hw)
    rw [hrx] at hrne
    rw [hst] at hrne
    exact absurd rfl hrne
  · have hrfl : r = { x with stock := x.waste.reverse, waste := [] } :=
      hrec.symm.trans (recycle_nil x hst hw)
    rw [hrfl] at hy
    have hyS : y.stock = (State.dealUpTo x.drawStep x.waste.reverse).2 := by
      rw [hy]
    have hyW : y.waste =
        (State.dealUpTo x.drawStep x.waste.reverse).1.reverse ++ ([] : List Card) := by
      rw [hy]
    have hwr : (x.waste.reverse).length = x.waste.length := List.length_reverse
    obtain ⟨h1, h2⟩ := dealUpTo_lens x.drawStep x.waste.reverse
    rcases Nat.lt_or_ge x.drawStep x.waste.length with hlt | hge
    · rw [hwr, Nat.min_eq_left (Nat.le_of_lt hlt)] at h1
      have hyne : y.stock ≠ [] := by
        intro hc0
        have hc2 : (State.dealUpTo x.drawStep x.waste.reverse).2 = ([] : List Card) :=
          hyS.symm.trans hc0
        rw [hc2, List.length_nil] at h2
        omega
      obtain ⟨c', t', hys⟩ := list_cons_of_ne_nil hyne
      have hdec : inPhase y = decide (y.waste.length % y.drawStep = 0) := by
        simp only [inPhase, hys]
      have hywl : y.waste.length = x.drawStep := by
        rw [hyW, List.length_append, List.length_reverse, List.length_nil, h1]
        omega
      have hyD : y.drawStep = x.drawStep := by
        rw [hy]
      rw [hdec, hywl, hyD]
      exact decide_eq_true (Nat.mod_self x.drawStep)
    · rw [hwr, Nat.min_eq_right hge] at h1
      have hyv : y.stock = [] := by
        have hy0 : y.stock.length = 0 := by
          rw [hyS]
          omega
        exact List.length_eq_zero_iff.mp hy0
      exact inPhase_eq_true_of_nil hyv

/-- **The second half of the trap.**  Alignment is drawn into: a
draw from a phase-aligned position stays phase-aligned.  PORTED
verbatim from `Orig/Phase.lean:315`. -/
private theorem draw_keeps_inPhase {x y : State} (hsuc : x.stepDraw = some y)
    (hin : inPhase x = true) : inPhase y = true := by
  by_cases hst : x.stock = []
  · exact draw_nil_inPhase hst hsuc
  · obtain ⟨r, hrec, hrne, hy⟩ := draw_unfold hsuc
    have hxr : x = r := ((recycle_keep x hst).symm).trans hrec
    rw [← hxr] at hy
    obtain ⟨c, t, hcon⟩ := list_cons_of_ne_nil hst
    have hres : x.waste.length % x.drawStep = 0 := by
      rw [inPhase_eq_decide_of_cons hcon] at hin
      exact of_decide_eq_true hin
    have hyS : y.stock = (State.dealUpTo x.drawStep x.stock).2 := by
      rw [hy]
    have hyW : y.waste = (State.dealUpTo x.drawStep x.stock).1.reverse ++ x.waste := by
      rw [hy]
    have hyD : y.drawStep = x.drawStep := by
      rw [hy]
    obtain ⟨h1, h2⟩ := dealUpTo_lens x.drawStep x.stock
    have hsl : x.stock.length = 1 + t.length := by
      show (x.stock).length = 1 + t.length
      rw [hcon, List.length_cons]
      omega
    rcases Nat.lt_or_ge x.drawStep x.stock.length with hlt | hge
    · rw [Nat.min_eq_left (Nat.le_of_lt hlt)] at h1
      have hyne : y.stock ≠ [] := by
        intro hc0
        have hc2 : (State.dealUpTo x.drawStep x.stock).2 = ([] : List Card) :=
          hyS.symm.trans hc0
        rw [hc2, List.length_nil] at h2
        omega
      obtain ⟨c', t', hys⟩ := list_cons_of_ne_nil hyne
      have hdec : inPhase y = decide (y.waste.length % y.drawStep = 0) := by
        simp only [inPhase, hys]
      have hywl : y.waste.length = x.drawStep + x.waste.length := by
        rw [hyW, List.length_append, List.length_reverse, h1]
      rw [hdec, hywl, hyD, Nat.add_mod_left]
      try exact decide_eq_true hres
    · rw [Nat.min_eq_right hge] at h1
      have hyv : y.stock = [] := by
        have hy0 : y.stock.length = 0 := by
          rw [hyS]
          omega
        exact List.length_eq_zero_iff.mp hy0
      exact inPhase_eq_true_of_nil hyv

/-! ### §1i. The pristine-commit kit

The invariant-carrying half of `Orig.Phase`'s draw commit bank:
the waste-consuming move table, the never-emptying-waste invariant
along waste-free plays, and the committed successor of a pristine
draw.  Ends at the carrier grade: `draw_notW_of_pristine`.
-/

/-- The two moves that spend a waste card.  PORTED verbatim from
`Orig/Phase.lean:363`. -/
private def isWasteMove (m : Move) : Bool :=
  match m with
  | .wasteToFound _ => true
  | .wasteToTab _ _ => true
  | _ => false

/-- Placing a card on the tableau never touches the stock, the
waste, or the draw step.  PORTED (re-stated over the seam's public
`putCard_keep`, `Orig/Play.lean:523`) from `Orig/Phase.lean:371`.
-/
private theorem putCard_zone_keep (x : State) (c : Card) (b : Base) :
    (x.putCard c b).stock = x.stock ∧ (x.putCard c b).waste = x.waste ∧
    (x.putCard c b).drawStep = x.drawStep :=
  ⟨putCard_keep.2.1, putCard_keep.2.2.1, putCard_keep.2.2.2⟩

/-- Building the waste top onto its foundation spends exactly one
cycle-count unit.  PORTED verbatim from `Orig/Phase.lean:382`. -/
private theorem cycleCount_lt_wasteToFound {x y : State} {c : Card}
    (h : State.step x (.wasteToFound c) = some y) :
    cycleCount y < cycleCount x := by
  simp only [State.step] at h
  split at h
  · by_cases hw : x.waste = []
    · rw [hw] at h
      simp at h
    · obtain ⟨w', ws, hcon⟩ := list_cons_of_ne_nil hw
      rw [hcon] at h
      simp only [Option.some.injEq] at h
      subst h
      show x.stock.length + ws.length < x.stock.length + x.waste.length
      rw [hcon, List.length_cons]
      omega
  · simp at h

/-- Building the waste top onto the tableau spends exactly one
cycle-count unit.  PORTED verbatim from `Orig/Phase.lean:401`. -/
private theorem cycleCount_lt_wasteToTab {x y : State} {c : Card} {b : Base}
    (h : State.step x (.wasteToTab c b) = some y) :
    cycleCount y < cycleCount x := by
  simp only [State.step] at h
  split at h
  · by_cases hw : x.waste = []
    · rw [hw] at h
      simp at h
    · obtain ⟨w', ws, hcon⟩ := list_cons_of_ne_nil hw
      rw [hcon] at h
      simp only [Option.some.injEq] at h
      subst h
      have hpc := putCard_zone_keep x c b
      show (x.putCard c b).stock.length + ws.length < x.stock.length + x.waste.length
      rw [hpc.1, hcon, List.length_cons]
      omega
  · simp at h

/-- A pile top onto its foundation leaves the stock, the waste, and
the draw step verbatim.  PORTED verbatim from
`Orig/Phase.lean:421`. -/
private theorem tabToFound_fixed {x y : State} {c : Card}
    (h : State.step x (.tabToFound c) = some y) :
    y.stock = x.stock ∧ y.waste = x.waste ∧ y.drawStep = x.drawStep := by
  simp only [State.step] at h
  split at h
  · split at h
    · simp at h
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl⟩
  · simp at h

/-- A foundation top back onto the tableau leaves the stock, the
waste, and the draw step verbatim.  PORTED verbatim from
`Orig/Phase.lean:435`. -/
private theorem foundToTab_fixed {x y : State} {c : Card} {b : Base}
    (h : State.step x (.foundToTab c b) = some y) :
    y.stock = x.stock ∧ y.waste = x.waste ∧ y.drawStep = x.drawStep := by
  simp only [State.step] at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨(putCard_zone_keep _ c b).1, (putCard_zone_keep _ c b).2.1,
        (putCard_zone_keep _ c b).2.2⟩
    · simp at h
  · simp at h

/-- A run between piles leaves the stock, the waste, and the draw
step verbatim.  PORTED verbatim from `Orig/Phase.lean:450`
(the `putRun_keep` cite rides the seam,
`Orig/Play.lean:537`). -/
private theorem tabToTab_fixed {x y : State} {c : Card} {b : Base}
    (h : State.step x (.tabToTab c b) = some y) :
    y.stock = x.stock ∧ y.waste = x.waste ∧ y.drawStep = x.drawStep := by
  simp only [State.step] at h
  by_cases hph : x.pileHolding c = none
  · rw [hph] at h
    simp at h
  · obtain ⟨a, hph'⟩ := option_some_of_ne_none hph
    simp only [hph'] at h
    split at h
    · by_cases hfc : fromCard c (x.piles a).faceUp = []
      · rw [hfc] at h
        simp at h
      · obtain ⟨rhd, rtl, hfc'⟩ := list_cons_of_ne_nil hfc
        rw [hfc'] at h
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨putRun_keep.2.1, putRun_keep.2.2.1,
          putRun_keep.2.2.2⟩
    · simp at h

/-- **The per-move step table**: every legal move leaves the cycle
count weakly down.  PORTED verbatim from `Orig/Phase.lean:473`
(the draw row rides §1d's `stepDraw_cycle`). -/
private theorem step_cycleCount_le {x y : State} : ∀ m : Move,
    State.step x m = some y → cycleCount y ≤ cycleCount x := by
  intro m h
  cases m with
  | draw => exact Nat.le_of_eq (stepDraw_cycle h)
  | wasteToFound c =>
      have hlt := cycleCount_lt_wasteToFound h
      omega
  | wasteToTab c b =>
      have hlt := cycleCount_lt_wasteToTab h
      omega
  | tabToFound c =>
      obtain ⟨h1, h2, _⟩ := tabToFound_fixed h
      exact Nat.le_of_eq (by simp only [cycleCount, h1, h2])
  | foundToTab c b =>
      obtain ⟨h1, h2, _⟩ := foundToTab_fixed h
      exact Nat.le_of_eq (by simp only [cycleCount, h1, h2])
  | tabToTab c b =>
      obtain ⟨h1, h2, _⟩ := tabToTab_fixed h
      exact Nat.le_of_eq (by simp only [cycleCount, h1, h2])

/-- The play lift of the step table.  PORTED verbatim from
`Orig/Phase.lean:497`. -/
private theorem run_cycleCount_le : ∀ {play : List Move} {x w : State},
    x.run play = some w → cycleCount w ≤ cycleCount x := by
  intro play
  induction play with
  | nil =>
      intro x w hrun
      have hx : some x = some w := hrun
      injection hx with h
      rw [← h]
      exact Nat.le_refl _
  | cons m rest ih =>
      intro x w hrun
      obtain ⟨s₁, hm, hrs⟩ := State.run_cons hrun
      have h1 := ih hrs
      have h2 := step_cycleCount_le m hm
      omega

/-- A play that spends a waste card strictly drops the cycle count.
PORTED verbatim from `Orig/Phase.lean:515`. -/
private theorem run_cycleCount_lt : ∀ {play : List Move} {x w : State},
    x.run play = some w → (∃ m ∈ play, isWasteMove m = true) →
    cycleCount w < cycleCount x := by
  intro play
  induction play with
  | nil =>
      intro x w _ hmem
      obtain ⟨m, hm, _⟩ := hmem
      exact absurd hm (by simp)
  | cons m rest ih =>
      intro x w hrun hmem
      obtain ⟨s₁, hm, hrs⟩ := State.run_cons hrun
      by_cases hmv : isWasteMove m = true
      · have hlt : cycleCount s₁ < cycleCount x := by
          cases m with
          | draw => simp [isWasteMove] at hmv
          | wasteToFound c => exact cycleCount_lt_wasteToFound hm
          | wasteToTab c b => exact cycleCount_lt_wasteToTab hm
          | tabToFound c => simp [isWasteMove] at hmv
          | foundToTab c b => simp [isWasteMove] at hmv
          | tabToTab c b => simp [isWasteMove] at hmv
        have hle := run_cycleCount_le hrs
        omega
      · obtain ⟨m', hm', hmis⟩ := hmem
        rcases List.mem_cons.1 hm' with heq | hmem2
        · exact absurd (heq ▸ hmis) hmv
        · have hlt := ih hrs ⟨m', hmem2, hmis⟩
          have hle := step_cycleCount_le m hm
          omega

/-- A list appended to a nonempty list is nonempty.  PORTED
verbatim from `Orig/Phase.lean:548`. -/
private theorem append_ne_nil_right (A : List Card) {B : List Card}
    (h : B ≠ []) : A ++ B ≠ [] := by
  obtain ⟨b, bs, hb⟩ := list_cons_of_ne_nil h
  intro hc
  subst hb
  cases A <;> simp_all

/-- **The pristine-step invariant.**  In a `wasteTo*`-free play at a
positive draw step, a state with a nonempty waste is never followed
by one with an empty waste.  PORTED verbatim from
`Orig/Phase.lean:559`. -/
private theorem step_wasteNe_preserved {x y : State} (hd : 0 < x.drawStep)
    {m : Move} (hgood : isWasteMove m ≠ true) (hs : State.step x m = some y)
    (hw : x.waste ≠ []) : y.waste ≠ [] ∧ y.drawStep = x.drawStep := by
  cases m with
  | draw =>
      have hsuc : x.stepDraw = some y := hs
      refine ⟨?_, draw_drawStep hsuc⟩
      by_cases hst : x.stock = []
      · obtain ⟨r, hrec, hrne, hy⟩ := draw_unfold hsuc
        have hrfl : r = { x with stock := x.waste.reverse, waste := [] } :=
          hrec.symm.trans (recycle_nil x hst hw)
        rw [hrfl] at hy
        have hyW : y.waste =
            (State.dealUpTo x.drawStep x.waste.reverse).1.reverse ++ ([] : List Card) := by
          rw [hy]
        obtain ⟨h1, _⟩ := dealUpTo_lens x.drawStep x.waste.reverse
        have hwr : (x.waste.reverse).length = x.waste.length := List.length_reverse
        have hwlen : 1 ≤ x.waste.length := by
          obtain ⟨c0, t0, hwcon⟩ := list_cons_of_ne_nil hw
          rw [hwcon, List.length_cons]
          omega
        rcases Nat.lt_or_ge x.drawStep x.waste.length with hlt | hge
        · rw [hwr, Nat.min_eq_left (Nat.le_of_lt hlt)] at h1
          intro hc0
          rw [hyW] at hc0
          have hlen := congrArg List.length hc0
          rw [List.length_append, List.length_reverse, List.length_nil] at hlen
          omega
        · rw [hwr, Nat.min_eq_right hge] at h1
          intro hc0
          rw [hyW] at hc0
          have hlen := congrArg List.length hc0
          rw [List.length_append, List.length_reverse, List.length_nil] at hlen
          omega
      · obtain ⟨r, hrec, hrne, hy⟩ := draw_unfold hsuc
        have hxr : x = r := ((recycle_keep x hst).symm).trans hrec
        rw [← hxr] at hy
        have hyW : y.waste = (State.dealUpTo x.drawStep x.stock).1.reverse ++ x.waste := by
          rw [hy]
        rw [hyW]
        exact append_ne_nil_right _ hw
  | wasteToFound c => simp [isWasteMove] at hgood
  | wasteToTab c b => simp [isWasteMove] at hgood
  | tabToFound c =>
      obtain ⟨_, h2, h3⟩ := tabToFound_fixed hs
      refine ⟨?_, h3⟩
      rw [h2]
      exact hw
  | foundToTab c b =>
      obtain ⟨_, h2, h3⟩ := foundToTab_fixed hs
      refine ⟨?_, h3⟩
      rw [h2]
      exact hw
  | tabToTab c b =>
      obtain ⟨_, h2, h3⟩ := tabToTab_fixed hs
      refine ⟨?_, h3⟩
      rw [h2]
      exact hw

/-- The pristine run lift: a `wasteTo*`-free play from a
positive-draw state with nonempty waste ends with nonempty waste
(and the same draw step throughout).  PORTED verbatim from
`Orig/Phase.lean:621`. -/
private theorem run_wasteNe (st : State) : ∀ {play : List Move} {x w : State},
    0 < st.drawStep → (∀ m ∈ play, isWasteMove m ≠ true) →
    x.drawStep = st.drawStep → x.waste ≠ [] →
    x.run play = some w → w.waste ≠ [] ∧ w.drawStep = st.drawStep := by
  intro play
  induction play with
  | nil =>
      intro x w _hd _hgood hsd hw hrun
      have hx : some x = some w := hrun
      injection hx with h
      rw [← h]
      exact ⟨hw, hsd⟩
  | cons m rest ih =>
      intro x w hd hgood hsd hw hrun
      obtain ⟨s₁, hm, hrs⟩ := State.run_cons hrun
      have hmne : isWasteMove m ≠ true := hgood m (by simp)
      have hdx : 0 < x.drawStep := by
        rw [hsd]
        exact hd
      obtain ⟨hw', hsd'⟩ := step_wasteNe_preserved hdx hmne hm hw
      exact ih hd (fun m' hm' => hgood m' (by simp [hm'])) (hsd'.trans hsd) hw' hrs

/-- The committed successor of a pristine draw: the first deal
drops at least one card onto the (previously empty) waste.  PORTED
verbatim from `Orig/Phase.lean:645`. -/
private theorem draw_pristine_s1 {st s₁ : State} (hd : 0 < st.drawStep)
    (hs : st.stock ≠ []) (hw : st.waste = []) (hsuc : st.stepDraw = some s₁) :
    s₁.waste ≠ [] ∧ s₁.drawStep = st.drawStep := by
  obtain ⟨r, hrec, hrne, hy⟩ := draw_unfold hsuc
  have hxr : st = r := ((recycle_keep st hs).symm).trans hrec
  rw [← hxr] at hy
  have hyW : s₁.waste =
      (State.dealUpTo st.drawStep st.stock).1.reverse ++ st.waste := by
    rw [hy]
  refine ⟨?_, draw_drawStep hsuc⟩
  rw [hyW, hw]
  obtain ⟨h1, _⟩ := dealUpTo_lens st.drawStep st.stock
  obtain ⟨c, t, hcon⟩ := list_cons_of_ne_nil hs
  have hsl : st.stock.length = 1 + t.length := by
    show (st.stock).length = 1 + t.length
    rw [hcon, List.length_cons]
    omega
  rcases Nat.lt_or_ge st.drawStep st.stock.length with hlt | hge
  · rw [Nat.min_eq_left (Nat.le_of_lt hlt)] at h1
    intro hc0
    have hlen := congrArg List.length hc0
    rw [List.length_append, List.length_reverse, List.length_nil] at hlen
    omega
  · rw [Nat.min_eq_right hge] at h1
    intro hc0
    have hlen := congrArg List.length hc0
    rw [List.length_append, List.length_reverse, List.length_nil] at hlen
    omega

/-- **Draws at pristine positions deny the witness.**  A draw made
with stock cards present and an *empty* waste: the committed
successor receives dealt cards in its waste, no `wasteTo*`-free
play ever empties a nonempty waste, and a returning play cannot
contain `wasteTo*` moves (they would strictly drop the cycle count,
which the draw conserves).  RE-STATED at the carrier grade from
`Orig/Phase.lean:853` (`draw_irreversible_pristine`, commit
grade there); every internal row is the §1i port above. -/
private theorem draw_notW_of_pristine {st : State}
    (hd : 0 < st.drawStep) (hs : st.stock ≠ []) (hw : st.waste = []) :
    ¬ reversibleAtW st Move.draw := by
  rintro ⟨s₁, play, hstep, hrun⟩
  have hsuc : st.stepDraw = some s₁ := hstep
  have hnoWaste : ∀ m ∈ play, isWasteMove m ≠ true := by
    intro m hm hc
    have hlt := run_cycleCount_lt hrun ⟨m, hm, hc⟩
    have hcc := draw_cycleCount hsuc
    rw [hcc] at hlt
    omega
  obtain ⟨hw₁, hsd₁⟩ := draw_pristine_s1 hd hs hw hsuc
  exact (run_wasteNe st hd hnoWaste hsd₁ hw₁ hrun).1 hw

/-! ### §1j. The lex-descent kit

`Orig.Phase`'s measure packaging for the offset draw: the
descending lexicographic pair `(cycleCount, D)` with `D` the
draw-distance to the phase line.  Ends at the carrier grade:
`draw_notW_of_offset`.
-/

/-- The working order for the measure packaging: pairs of naturals
in the *descending* lexicographic order.  PORTED verbatim from
`Orig/Phase.lean:904`. -/
private def lexDesc (p p' : Nat × Nat) : Prop :=
  p'.1 ≤ p.1 ∧ (p'.1 = p.1 → p'.2 ≤ p.2)

/-- Strict descent in the descending lex order.  PORTED verbatim
from `Orig/Phase.lean:909`. -/
private def lexDescStrict (p p' : Nat × Nat) : Prop :=
  p'.1 < p.1 ∨ (p'.1 = p.1 ∧ p'.2 < p.2)

/-- Reflexivity of the descending lex order.  PORTED verbatim from
`Orig/Phase.lean:912`. -/
private theorem lexDesc_refl (p : Nat × Nat) : lexDesc p p :=
  ⟨Nat.le_refl p.1, fun _ => Nat.le_refl p.2⟩

/-- Transitivity of the descending lex order.  PORTED verbatim from
`Orig/Phase.lean:916`. -/
private theorem lexDesc_trans {p q r : Nat × Nat} (h1 : lexDesc p q) (h2 : lexDesc q r) :
    lexDesc p r := by
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  refine ⟨Nat.le_trans h2a h1a, fun hE => ?_⟩
  have hq : q.1 = p.1 := by omega
  have hr : r.1 = q.1 := by omega
  exact Nat.le_trans (h2b hr) (h1b hq)

/-- A strict descent cannot be retraced by a weak one.  PORTED
verbatim from `Orig/Phase.lean:928`. -/
private theorem lexDescStrict_contra {p q : Nat × Nat}
    (h1 : lexDescStrict p q) (h2 : lexDesc q p) : False := by
  obtain ⟨h2a, h2b⟩ := h2
  rcases h1 with hlt | ⟨heq, hlt⟩
  · omega
  · have hp2 := h2b heq.symm
    omega

/-- **The lex ascent.**  PORTED verbatim from `Orig/Phase.lean:939`
(`mono_run_lex`). -/
private theorem mono_run_lex (Q : State → Nat × Nat)
    (h : ∀ {s m s'}, State.step s m = some s' → lexDesc (Q s) (Q s')) :
    ∀ {s play w}, s.run play = some w → lexDesc (Q s) (Q w) := by
  intro s play
  revert s
  induction play with
  | nil =>
      intro s w hrun
      have hx : some s = some w := hrun
      injection hx with hq
      rw [← hq]
      exact lexDesc_refl _
  | cons m rest ih =>
      intro s w hrun
      obtain ⟨s₁, hm, hrs⟩ := State.run_cons hrun
      exact lexDesc_trans (h hm) (ih hrs)

/-- The draw-distance potential against the in-phase attractor: `0`
on phase-aligned positions, otherwise the number of whole deals
left before the stock drains (in ceiling form).  PORTED verbatim
from `Orig/Phase.lean:971`. -/
private def D (st : State) : Nat :=
  if (inPhase st) = true then 0 else (st.stock.length + st.drawStep - 1) / st.drawStep

/-- The measure pair: the cycle count first, the draw distance
second.  PORTED verbatim from `Orig/Phase.lean:976`. -/
private def QPair (st : State) : Nat × Nat := (cycleCount st, D st)

/-- One successful draw from a nonempty stock, as four bookkeeping
facts.  PORTED verbatim from `Orig/Phase.lean:981`. -/
private theorem draw_facts {x y : State} (hsuc : x.stepDraw = some y)
    (hne : x.stock ≠ []) :
    cycleCount y = cycleCount x ∧ y.drawStep = x.drawStep ∧
      y.stock.length + min x.drawStep x.stock.length = x.stock.length ∧
      y.waste.length = min x.drawStep x.stock.length + x.waste.length := by
  obtain ⟨r, hrec, hrne, hy⟩ := draw_unfold hsuc
  have hxr : x = r := ((recycle_keep x hne).symm).trans hrec
  rw [← hxr] at hy
  have hyS : y.stock = (State.dealUpTo x.drawStep x.stock).2 := by rw [hy]
  have hyW : y.waste = (State.dealUpTo x.drawStep x.stock).1.reverse ++ x.waste := by
    rw [hy]
  obtain ⟨h1, h2⟩ := dealUpTo_lens x.drawStep x.stock
  refine ⟨draw_cycleCount hsuc, draw_drawStep hsuc, ?_, ?_⟩
  · rw [hyS]
    omega
  · rw [hyW, List.length_append, List.length_reverse]
    omega

/-- `D` only reads the stock, the waste, and the draw step.  PORTED
verbatim from `Orig/Phase.lean:1000`. -/
private theorem D_congr {x y : State} (h1 : x.stock = y.stock)
    (h2 : x.waste = y.waste) (h3 : x.drawStep = y.drawStep) : D x = D y := by
  show (if (inPhase x) = true then 0 else
          (x.stock.length + x.drawStep - 1) / x.drawStep) =
       (if (inPhase y) = true then 0 else
          (y.stock.length + y.drawStep - 1) / y.drawStep)
  rw [inPhase_congr h1 h2 h3, h1, h3]

/-- `D` vanishes on phase-aligned positions.  PORTED verbatim from
`Orig/Phase.lean:1009`. -/
private theorem D_of_inPhase_true {x : State} (h : inPhase x = true) : D x = 0 := by
  show (if (inPhase x) = true then 0 else _) = 0
  rw [h]
  rfl

/-- `D` opens to its ceiling form on off-line positions.  PORTED
verbatim from `Orig/Phase.lean:1015`. -/
private theorem D_of_inPhase_false {x : State} (h : inPhase x = false) :
    D x = (x.stock.length + x.drawStep - 1) / x.drawStep := by
  show (if (inPhase x) = true then 0 else
          (x.stock.length + x.drawStep - 1) / x.drawStep) = _
  rw [h]
  rfl

/-- The measure pair is verbatim under a move that copies the stock,
the waste, and the draw step.  PORTED verbatim from
`Orig/Phase.lean:1024`. -/
private theorem lex_of_fixed {x y : State} (h1 : y.stock = x.stock)
    (h2 : y.waste = x.waste) (h3 : y.drawStep = x.drawStep) :
    lexDesc (QPair x) (QPair y) :=
  ⟨show y.stock.length + y.waste.length ≤ x.stock.length + x.waste.length by
      rw [h1, h2]
      omega,
    fun _ => Nat.le_of_eq (D_congr h1 h2 h3)⟩

/-- **The per-move lex table.**  Every legal move descends the
measure pair `(cycleCount, D)`.  PORTED verbatim from
`Orig/Phase.lean:1038`. -/
private theorem step_lexDesc : ∀ {x y : State} {m : Move},
    State.step x m = some y → lexDesc (QPair x) (QPair y) := by
  intro x y m hs
  cases m with
  | draw =>
      have hsuc : x.stepDraw = some y := hs
      refine ⟨Nat.le_of_eq (draw_cycleCount hsuc), fun _ => ?_⟩
      by_cases hstock : x.stock = []
      · have hDy : D y = 0 := D_of_inPhase_true (draw_nil_inPhase hstock hsuc)
        show D y ≤ D x
        omega
      · obtain ⟨_, hdeq, hslen, hwlen⟩ := draw_facts hsuc hstock
        by_cases hin : inPhase x = true
        · have hDy : D y = 0 := D_of_inPhase_true (draw_keeps_inPhase hsuc hin)
          show D y ≤ D x
          omega
        · rcases bool_dich (inPhase x) with hb | hb
          · exact absurd hb hin
          · obtain ⟨hnx, hres⟩ := inPhase_eq_false_iff.1 hb
            by_cases hdr : y.stock = []
            · have hDy : D y = 0 := D_of_inPhase_true (inPhase_eq_true_of_nil hdr)
              show D y ≤ D x
              omega
            · obtain ⟨c', t', hcon'⟩ := list_cons_of_ne_nil hdr
              have hp' : 1 ≤ y.stock.length := by
                rw [hcon', List.length_cons]
                omega
              have hk : min x.drawStep x.stock.length = x.drawStep := by omega
              have hresy : y.waste.length % x.drawStep = x.waste.length % x.drawStep := by
                rw [show y.waste.length =
                    min x.drawStep x.stock.length + x.waste.length from hwlen,
                  hk, Nat.add_mod_left]
              have hiny : inPhase y = false := by
                rw [inPhase_eq_decide_of_cons hcon']
                refine decide_eq_false (fun hc0 => ?_)
                rw [hdeq, hresy] at hc0
                exact hres hc0
              show D y ≤ D x
              rw [D_of_inPhase_false hiny, D_of_inPhase_false hb,
                show y.drawStep = x.drawStep from hdeq]
              exact Nat.div_le_div_right (show y.stock.length + x.drawStep - 1 ≤
                  x.stock.length + x.drawStep - 1 from by omega)
  | wasteToFound c =>
      have hlt := cycleCount_lt_wasteToFound hs
      refine ⟨?_, fun hE => absurd hE
        (show ¬(cycleCount y = cycleCount x) from by omega)⟩
      show cycleCount y ≤ cycleCount x
      omega
  | wasteToTab c b =>
      have hlt := cycleCount_lt_wasteToTab hs
      refine ⟨?_, fun hE => absurd hE
        (show ¬(cycleCount y = cycleCount x) from by omega)⟩
      show cycleCount y ≤ cycleCount x
      omega
  | tabToFound c =>
      obtain ⟨h1, h2, h3⟩ := tabToFound_fixed hs
      exact lex_of_fixed h1 h2 h3
  | foundToTab c b =>
      obtain ⟨h1, h2, h3⟩ := foundToTab_fixed hs
      exact lex_of_fixed h1 h2 h3
  | tabToTab c b =>
      obtain ⟨h1, h2, h3⟩ := tabToTab_fixed hs
      exact lex_of_fixed h1 h2 h3

/-- **Draws at offset positions deny the witness.**  At a position
with cards still in the stock whose waste sits strictly inside a
deal (and a positive draw step): the committed draw conserves the
cycle count and strictly drops the draw distance `D`, and no legal
play ascends the measure pair.  RE-STATED at the carrier grade
from `Orig/Phase.lean:1108` (`draw_irreversible_offset_lex`,
commit grade there); every internal row is the §1h/§1j port
above. -/
private theorem draw_notW_of_offset {st : State}
    (hd : 0 < st.drawStep) (hs : st.stock ≠ [])
    (hoff : st.waste.length % st.drawStep ≠ 0) :
    ¬ reversibleAtW st Move.draw := by
  rintro ⟨s₁, play, hstep, hrun⟩
  have hs₁ : st.stepDraw = some s₁ := hstep
  obtain ⟨_, hdeq, hslen, hwlen⟩ := draw_facts hs₁ hs
  obtain ⟨c, t, hcon⟩ := list_cons_of_ne_nil hs
  have hp : 1 ≤ st.stock.length := by
    rw [hcon, List.length_cons]
    omega
  have hinF : inPhase st = false := by
    rw [inPhase_eq_decide_of_cons hcon, decide_eq_false hoff]
  have hDst : D st = (st.stock.length - 1) / st.drawStep + 1 := by
    rw [D_of_inPhase_false hinF]
    have hshift : st.stock.length + st.drawStep - 1 =
        (st.stock.length - 1) + st.drawStep := by omega
    rw [hshift, Nat.add_div_right _ hd]
  have hstrict : lexDescStrict (QPair st) (QPair s₁) :=
    Or.inr ⟨show (QPair s₁).fst = (QPair st).fst from draw_cycleCount hs₁, ?_⟩
  show D s₁ < D st
  by_cases hdr : s₁.stock = []
  · have hD0 : D s₁ = 0 := D_of_inPhase_true (inPhase_eq_true_of_nil hdr)
    rw [hD0, hDst]
    have hq : 0 ≤ (st.stock.length - 1) / st.drawStep := Nat.zero_le _
    omega
  · obtain ⟨c', t', hcon'⟩ := list_cons_of_ne_nil hdr
    have hp' : 1 ≤ s₁.stock.length := by
      rw [hcon', List.length_cons]
      omega
    have hresy : s₁.waste.length % st.drawStep = st.waste.length % st.drawStep := by
      have hk : min st.drawStep st.stock.length = st.drawStep := by omega
      rw [show s₁.waste.length =
          min st.drawStep st.stock.length + st.waste.length from hwlen,
        hk, Nat.add_mod_left]
    have hiny : inPhase s₁ = false := by
      rw [inPhase_eq_decide_of_cons hcon']
      refine decide_eq_false (fun hc0 => ?_)
      rw [hdeq, hresy] at hc0
      exact hoff hc0
    have hDs₁ : D s₁ = (s₁.stock.length - 1) / st.drawStep + 1 := by
      rw [D_of_inPhase_false hiny,
        show s₁.drawStep = st.drawStep from hdeq]
      have hshift : s₁.stock.length + st.drawStep - 1 =
          (s₁.stock.length - 1) + st.drawStep := by omega
      rw [hshift, Nat.add_div_right _ hd]
    have hchain : st.stock.length - 1 = (s₁.stock.length - 1) + st.drawStep := by omega
    calc D s₁ = (s₁.stock.length - 1) / st.drawStep + 1 := hDs₁
      _ < ((s₁.stock.length - 1) + st.drawStep) / st.drawStep + 1 := by
          rw [Nat.add_div_right _ hd]
          omega
      _ = D st := by rw [hDst, hchain]
  exact lexDescStrict_contra hstrict (mono_run_lex QPair step_lexDesc hrun)

/-! ### §1k. The draw round trips

The constructive half of the draw letter: the pass-end full
redeal, the drain/redeal position banks, and the three round trips
the oracle's `true` cells hand (selfRecycle, pass base via the
pure-draw drain, and the in-phase two-leg rotation).
-/

/-- The additive take split.  PORTED verbatim from
`Orig/Phase.lean:1207`. -/
private theorem take_drop_add {α : Type} : ∀ (i j : Nat) (l : List α),
    l.take (i + j) = l.take i ++ (l.drop i).take j := by
  intro i
  induction i with
  | zero =>
      intro j l
      simp
  | succ i ih =>
      intro j l
      have hidx : i + 1 + j = i + j + 1 := by omega
      rw [hidx]
      cases l with
      | nil => simp only [List.take_nil, List.drop_nil, List.nil_append]
      | cons a t =>
          show a :: t.take (i + j) = a :: (t.take i ++ (t.drop i).take j)
          exact congrArg (a :: ·) (ih j t)

/-- The additive drop split.  PORTED verbatim from
`Orig/Phase.lean:1232`. -/
private theorem drop_drop_add {α : Type} : ∀ (i j : Nat) (l : List α),
    (l.drop i).drop j = l.drop (i + j) := by
  intro i
  induction i with
  | zero =>
      intro j l
      simp
  | succ i ih =>
      intro j l
      have hidx : i + 1 + j = i + j + 1 := by omega
      rw [hidx]
      cases l with
      | nil => simp only [List.drop_nil]
      | cons a t =>
          show (t.drop i).drop j = t.drop (i + j)
          exact ih j t

/-- Take and drop recombine to the whole list.  PORTED verbatim
from `Orig/Phase.lean:1251` (the same row as the private
`take_drop_join` below, which the frozen `Orig/Classify.lean:1091`
kit copy drove; both kept, sources distinct). -/
private theorem take_drop_append {α : Type} : ∀ (n : Nat) (l : List α),
    l.take n ++ l.drop n = l := by
  intro n
  induction n with
  | zero => intro l; simp
  | succ m ih =>
      intro l
      cases l with
      | nil => rfl
      | cons a t =>
          show a :: (t.take m ++ t.drop m) = a :: t
          exact congrArg (a :: ·) (ih t)

/-- Taking past (or exactly to) the end of a list takes the whole
list.  PORTED verbatim from `Orig/Phase.lean:1266`. -/
private theorem take_ge_length {α : Type} : ∀ (l : List α) (n : Nat),
    l.length ≤ n → l.take n = l := by
  intro l
  induction l with
  | nil =>
      intro n _
      exact List.take_nil
  | cons a t ih =>
      intro n
      intro h
      match n with
      | 0 =>
          exact absurd h (by
            have hx : (a :: t).length = t.length + 1 := rfl
            omega)
      | m + 1 =>
          have hm : t.length ≤ m := by
            have hx : (a :: t).length = t.length + 1 := rfl
            omega
          show a :: t.take m = a :: t
          exact congrArg (a :: ·) (ih m hm)

/-- Dropping past (or exactly to) the end of a list drops it to
nothing.  PORTED verbatim from `Orig/Phase.lean:1290`. -/
private theorem drop_ge_length {α : Type} : ∀ (l : List α) (n : Nat),
    l.length ≤ n → l.drop n = [] := by
  intro l
  induction l with
  | nil =>
      intro n _
      exact List.drop_nil
  | cons a t ih =>
      intro n
      intro h
      match n with
      | 0 =>
          exact absurd h (by
            have hx : (a :: t).length = t.length + 1 := rfl
            omega)
      | m + 1 =>
          have hm : t.length ≤ m := by
            have hx : (a :: t).length = t.length + 1 := rfl
            omega
          exact ih m hm

/-- The prefix clip on an appended list: dropping past a known
prefix returns the suffix.  PORTED verbatim from
`Orig/Phase.lean:1313`. -/
private theorem drop_append_prefix {α : Type} : ∀ (A B : List α),
    (A ++ B).drop A.length = B := by
  intro A
  induction A with
  | nil => intro B; rfl
  | cons a t ih =>
      intro B
      show (t ++ B).drop t.length = B
      exact ih B

/-- The prefix clip on an appended list, take side.  PORTED
verbatim from `Orig/Phase.lean:1325`. -/
private theorem take_append_prefix {α : Type} : ∀ (A B : List α),
    (A ++ B).take A.length = A := by
  intro A
  induction A with
  | nil => intro B; rfl
  | cons a t ih =>
      intro B
      show a :: (t ++ B).take t.length = a :: t
      exact congrArg (a :: ·) (ih B)

/-- One draw followed by the rest of the play.  PORTED verbatim
from `Orig/Phase.lean:1353`. -/
private theorem run_draw_cons {x y : State} {rest : List Move}
    (hstep : State.step x Move.draw = some y) :
    x.run (Move.draw :: rest) = y.run rest := by
  show (match State.step x Move.draw with
      | some st' => State.run st' rest
      | none => none) = State.run y rest
  rw [hstep]

/-- Append-glue for pure-draw plays.  PORTED verbatim from
`Orig/Phase.lean:1363`. -/
private theorem run_replicate_append :
    ∀ (q : Nat) (x z : State) (rest : List Move),
    x.run (List.replicate q Move.draw) = some z →
    x.run (List.replicate q Move.draw ++ rest) = z.run rest := by
  intro q
  induction q with
  | zero =>
      intro x z rest h
      have hx : (some x : Option State) = some z := h
      injection hx with hx2
      rw [← hx2]
      rfl
  | succ q ih =>
      intro x z rest h
      obtain ⟨y, hstep, hrest⟩ := State.run_cons h
      show x.run (Move.draw :: (List.replicate q Move.draw ++ rest)) = z.run rest
      rw [run_draw_cons hstep]
      exact ih y z rest hrest

/-- One plain draw (the stock is nonempty, so no recycle fires):
the head deal moves stock-to-waste, list-exact.  PORTED verbatim
from `Orig/Phase.lean:1174`. -/
private theorem plain_draw_shape {x : State} (hne : x.stock ≠ []) :
    x.stepDraw = some
      { x with stock := x.stock.drop x.drawStep, waste := (x.stock.take x.drawStep).reverse ++ x.waste } := by
  rw [State.stepDraw, show State.recycle x = x from recycle_keep x hne,
    dealStock_eq_of_ne_nil x hne, dealUpTo_eq_take_drop]

/-- One pass-end draw (the stock is empty and the waste nonempty,
so the recycle fires).  PORTED verbatim from
`Orig/Phase.lean:1184`. -/
private theorem base_draw_shape {x : State} (hstock : x.stock = ([] : List Card))
    (hw : x.waste ≠ []) :
    x.stepDraw = some
      { x with stock := x.waste.reverse.drop x.drawStep, waste := (x.waste.reverse.take x.drawStep).reverse ++ ([] : List Card) } := by
  have hrne : x.waste.reverse ≠ [] := by
    intro hc
    have hlen := congrArg List.length hc
    rw [List.length_reverse, List.length_nil] at hlen
    obtain ⟨c0, t0, hwcon0⟩ := list_cons_of_ne_nil hw
    have h1 : 1 ≤ x.waste.length := by
      rw [hwcon0, List.length_cons]
      omega
    omega
  rw [State.stepDraw, recycle_nil x hstock hw,
    dealStock_eq_of_ne_nil _ hrne, dealUpTo_eq_take_drop]

/-- **The short-stock full deal.**  PORTED verbatim from
`Orig/Phase.lean:1495`. -/
private theorem draw_full_shape (x : State) (hne : x.stock ≠ [])
    (hx : x.stock.length < x.drawStep) :
    State.step x Move.draw = some
      (State.mk x.found x.piles ([] : List Card) (x.stock.reverse ++ x.waste) x.drawStep) := by
  have ge := Nat.le_of_lt hx
  rw [show State.step x Move.draw = x.stepDraw from rfl, plain_draw_shape hne,
    drop_ge_length x.stock x.drawStep ge, take_ge_length x.stock x.drawStep ge]

/-- The pass-end full-redeal, as a computed step.  PORTED verbatim
from `Orig/Phase.lean:775`. -/
private theorem selfRecycle_draw {st : State} (hstock : st.stock = [])
    (hw : st.waste ≠ []) (hsize : st.waste.length ≤ st.drawStep) :
    State.step st Move.draw = some st := by
  show st.stepDraw = some st
  rw [State.stepDraw, recycle_nil st hstock hw]
  have hrne : st.waste.reverse ≠ [] := by
    intro hc
    have hlen := congrArg List.length hc
    rw [List.length_reverse, List.length_nil] at hlen
    obtain ⟨c0, t0, hwcon0⟩ := list_cons_of_ne_nil hw
    have h1 : 1 ≤ st.waste.length := by
      rw [hwcon0, List.length_cons]
      omega
    omega
  have hfull : State.dealStock { st with stock := st.waste.reverse, waste := [] } = some { st with stock := ([] : List Card), waste := (st.waste.reverse).reverse ++ ([] : List Card) } :=
    dealStock_full (st := { st with stock := st.waste.reverse, waste := [] })
      (by
        show st.waste.reverse ≠ []
        exact hrne)
      (by
        show (st.waste.reverse).length ≤ st.drawStep
        rw [List.length_reverse]
        exact hsize)
  rw [hfull, List.reverse_reverse, List.append_nil, ← hstock]

/-- **The drain positions.**  From a state whose stock is `l`, `q`
consecutive full-deal draws move exactly `q * drawStep` cards from
the stock's front to the waste's front, list-exact.  PORTED
verbatim from `Orig/Phase.lean:1386`. -/
private theorem drain_positions_one :
    ∀ (q : Nat) (x : State) (n : Nat) (l : List Card),
    0 < x.drawStep → n = q * x.drawStep → n ≤ l.length → x.stock = l →
    x.run (List.replicate q Move.draw) = some
      { x with stock := l.drop n, waste := (l.take n).reverse ++ x.waste } := by
  intro q
  induction q with
  | zero =>
      intro x n l _hd hn _hle hstock
      have hn0 : n = 0 := by
        rw [Nat.zero_mul] at hn
        exact hn
      subst hn0
      show (some x : Option State) = some
        { x with stock := l.drop 0, waste := (l.take 0).reverse ++ x.waste }
      rw [List.drop_zero, List.take_zero, List.reverse_nil, List.nil_append,
        ← hstock]
  | succ q ih =>
      intro x n l hd hn hle hstock
      have hnsm : n = q * x.drawStep + x.drawStep := by
        rw [Nat.succ_mul] at hn
        exact hn
      have hlne : l ≠ [] := by
        intro hc
        have hlen : l.length = 0 := by rw [hc]; simp
        omega
      have hsne : x.stock ≠ [] := by
        intro hc
        apply hlne
        rw [← hstock]
        exact hc
      have hstep : State.step x Move.draw = some
          { x with stock := x.stock.drop x.drawStep, waste := (x.stock.take x.drawStep).reverse ++ x.waste } :=
        plain_draw_shape hsne
      have hrep : List.replicate (q + 1) Move.draw
          = Move.draw :: List.replicate q Move.draw := rfl
      rw [hrep, run_draw_cons hstep, hstock]
      have hle' : q * x.drawStep ≤ (l.drop x.drawStep).length := by
        have h1 := List.length_drop (i := x.drawStep) (l := l)
        omega
      have hres := ih
        { x with stock := l.drop x.drawStep, waste := (l.take x.drawStep).reverse ++ x.waste }
        (q * x.drawStep) (l.drop x.drawStep) hd rfl hle' rfl
      rw [hres]
      have hSw : (show State from
          { x with stock := l.drop x.drawStep, waste := (l.take x.drawStep).reverse ++ x.waste }).waste
          = (l.take x.drawStep).reverse ++ x.waste := rfl
      rw [hSw]
      have hidx : x.drawStep + q * x.drawStep = n := by omega
      rw [drop_drop_add x.drawStep (q * x.drawStep) l, hidx]
      have hmerge : (List.take (q * x.drawStep) (List.drop x.drawStep l)).reverse
            ++ ((List.take x.drawStep l).reverse ++ x.waste)
          = (l.take (x.drawStep + q * x.drawStep)).reverse ++ x.waste := by
        rw [take_drop_add, List.reverse_append, List.append_assoc]
      rw [hmerge, hidx]

/-- **The redeal positions.**  From a pass base, `k + 1`
consecutive draws move exactly `(k + 1) * drawStep` cards of the
recycled pool back onto the waste, list-exact.  PORTED verbatim
from `Orig/Phase.lean:1451`. -/
private theorem base_positions_one :
    ∀ (k : Nat) (x : State),
    x.stock = ([] : List Card) → x.waste ≠ [] → 0 < x.drawStep →
    (k + 1) * x.drawStep ≤ x.waste.length →
    x.run (List.replicate (k + 1) Move.draw) = some
      { x with stock := x.waste.reverse.drop ((k + 1) * x.drawStep), waste := (x.waste.reverse.take ((k + 1) * x.drawStep)).reverse ++ ([] : List Card) } := by
  intro k x hstock hw hd hsize
  rw [Nat.succ_mul] at hsize
  have hstep : State.step x Move.draw = some
      { x with stock := x.waste.reverse.drop x.drawStep, waste := (x.waste.reverse.take x.drawStep).reverse ++ ([] : List Card) } :=
    base_draw_shape hstock hw
  rw [show List.replicate (k + 1) Move.draw
        = Move.draw :: List.replicate k Move.draw from rfl,
    run_draw_cons hstep]
  have hle' : k * x.drawStep ≤ (x.waste.reverse.drop x.drawStep).length := by
    have h1 := List.length_drop (i := x.drawStep) (l := x.waste.reverse)
    have h2 : x.waste.reverse.length = x.waste.length := List.length_reverse
    omega
  have hres := drain_positions_one k
    { x with stock := x.waste.reverse.drop x.drawStep, waste := (x.waste.reverse.take x.drawStep).reverse ++ ([] : List Card) }
    (k * x.drawStep) (x.waste.reverse.drop x.drawStep) hd rfl hle' rfl
  rw [hres]
  have hSw : (show State from
      { x with stock := x.waste.reverse.drop x.drawStep, waste := (x.waste.reverse.take x.drawStep).reverse ++ ([] : List Card) }).waste
      = (x.waste.reverse.take x.drawStep).reverse ++ ([] : List Card) := rfl
  rw [hSw]
  have hidx : x.drawStep + k * x.drawStep = (k + 1) * x.drawStep := by
    rw [Nat.succ_mul]; omega
  rw [drop_drop_add x.drawStep (k * x.drawStep) x.waste.reverse, hidx]
  have hmerge : (List.take (k * x.drawStep)
          (List.drop x.drawStep x.waste.reverse)).reverse
        ++ ((List.take x.drawStep x.waste.reverse).reverse ++ ([] : List Card))
      = ((List.take (x.drawStep + k * x.drawStep) x.waste.reverse).reverse
          ++ ([] : List Card)) := by
    rw [take_drop_add, List.reverse_append, List.append_assoc]
  rw [hmerge, hidx]

/-- The additive take-drop reassembly (the frozen card's own
private copy).  PORTED verbatim from
`Orig/Classify.lean:1091`. -/
private theorem take_drop_join : ∀ (n : Nat) (l : List Card),
    l.take n ++ l.drop n = l := take_drop_append

/-- The run-composition shape.  PORTED verbatim from
`Orig/Classify.lean:1124`. -/
private theorem run_cons_shape {s : State} {m : Move} {rest : List Move} {s' w : State}
    (hstep : State.step s m = some s') (hrun : s'.run rest = some w) :
    s.run (m :: rest) = some w := by
  simp only [State.run, hstep]
  exact hrun

/-- The pure-draw drain: from any stock-bearing position, some
pure-draw play drains the stock to the pass base, ending with the
whole recycle-reversed stock re-dealt onto the waste.  PORTED
verbatim from `Orig/Classify.lean:1133`. -/
private theorem drain_to_pass : ∀ (n : Nat) (l : List Card) (s : State), l.length ≤ n →
    0 < s.drawStep → s.stock = l →
    ∃ play, s.run play = some
      { s with stock := ([] : List Card), waste := l.reverse ++ s.waste } := by
  intro n
  induction n with
  | zero =>
      intro l s hlen hd hstock
      have hnil : l = [] := by
        cases l with
        | nil => rfl
        | cons w t =>
            have h1 : (w :: t).length = t.length + 1 := rfl
            omega
      subst hnil
      refine ⟨[], ?_⟩
      have hrfl : s.run [] = some s := rfl
      rw [hrfl]
      refine congrArg some (State.ext rfl rfl hstock ?_ rfl)
      rfl
  | succ n ih =>
      intro l s hlen hd hstock
      have hsplit : l = [] ∨ ∃ w t, l = w :: t := by
        cases l with
        | nil => exact Or.inl rfl
        | cons w t => exact Or.inr ⟨w, t, rfl⟩
      rcases hsplit with hnil | ⟨w, t, hcon⟩
      · subst hnil
        refine ⟨[], ?_⟩
        have hrfl : s.run [] = some s := rfl
        rw [hrfl]
        refine congrArg some (State.ext rfl rfl hstock ?_ rfl)
        rfl
      · subst hcon
        have hne : s.stock ≠ [] := by
          intro hc
          rw [hstock] at hc
          exact absurd hc (by simp)
        have hstep : State.step s Move.draw = some
            { s with stock := s.stock.drop s.drawStep, waste := (s.stock.take s.drawStep).reverse ++ s.waste } :=
          plain_draw_shape hne
        have hdrop : (s.stock.drop s.drawStep).length ≤ n := by
          rw [hstock]
          have hd2 := List.length_drop (l := w :: t) (i := s.drawStep)
          have hl : (w :: t).length = t.length + 1 := rfl
          omega
        have hstock₂ : { s with stock := s.stock.drop s.drawStep, waste := (s.stock.take s.drawStep).reverse ++ s.waste }.stock
            = s.stock.drop s.drawStep := rfl
        obtain ⟨play', hrun'⟩ := ih (s.stock.drop s.drawStep)
          { s with stock := s.stock.drop s.drawStep, waste := (s.stock.take s.drawStep).reverse ++ s.waste }
          hdrop hd hstock₂
        refine ⟨Move.draw :: play', ?_⟩
        refine run_cons_shape hstep ?_
        rw [hrun']
        have hEqd : (s.stock.drop s.drawStep).reverse
            ++ (s.stock.take s.drawStep).reverse = s.stock.reverse := by
          rw [show (s.stock.drop s.drawStep).reverse ++ (s.stock.take s.drawStep).reverse
                = ((s.stock.take s.drawStep) ++ s.stock.drop s.drawStep).reverse from
                by rw [List.reverse_append],
              take_drop_join]
        rw [show (s.stock.drop s.drawStep).reverse
              ++ ((s.stock.take s.drawStep).reverse ++ s.waste)
              = ((s.stock.drop s.drawStep).reverse ++ (s.stock.take s.drawStep).reverse) ++ s.waste from
              by rw [← List.append_assoc],
            hEqd]
        refine congrArg some (State.ext rfl rfl rfl ?_ rfl)
        rw [hstock]

/-- **The pass-base round trip** (the draw's undo play, witness
grade): drawing at the pass base is undone by a pure-draw play — a
small waste re-deals wholesale (the selfRecycle row above), a
larger one drains the recycled remainder back onto the waste in
its original arrangement.  PORTED verbatim from
`Orig/Classify.lean:1206`. -/
private theorem draw_passBase_reversibleW {st : State}
    (hstock : st.stock = ([] : List Card)) (hw : st.waste ≠ []) (hd : 0 < st.drawStep) :
    reversibleAtW st Move.draw := by
  by_cases hsize : st.waste.length ≤ st.drawStep
  · exact ⟨st, [], selfRecycle_draw hstock hw hsize, rfl⟩
  · have hstep : State.step st Move.draw = some
        { st with stock := st.waste.reverse.drop st.drawStep, waste := (st.waste.reverse.take st.drawStep).reverse ++ ([] : List Card) } :=
      base_draw_shape hstock hw
    have hdropLen : (st.waste.reverse.drop st.drawStep).length ≤ st.waste.length := by
      have hd2 := List.length_drop (l := st.waste.reverse) (i := st.drawStep)
      have hrev : st.waste.reverse.length = st.waste.length := by rw [List.length_reverse]
      omega
    have hstock₂ : { st with stock := st.waste.reverse.drop st.drawStep, waste := (st.waste.reverse.take st.drawStep).reverse ++ ([] : List Card) }.stock
        = st.waste.reverse.drop st.drawStep := rfl
    have hstepPos : 0 < { st with stock := st.waste.reverse.drop st.drawStep, waste := (st.waste.reverse.take st.drawStep).reverse ++ ([] : List Card) }.drawStep := hd
    obtain ⟨play, hrun⟩ := drain_to_pass st.waste.length
      (st.waste.reverse.drop st.drawStep)
      { st with stock := st.waste.reverse.drop st.drawStep, waste := (st.waste.reverse.take st.drawStep).reverse ++ ([] : List Card) }
      hdropLen hstepPos hstock₂
    refine ⟨_, play, hstep, ?_⟩
    rw [hrun]
    have hwE : (st.waste.reverse.drop st.drawStep).reverse
        ++ ((st.waste.reverse.take st.drawStep).reverse ++ ([] : List Card))
        = st.waste := by
      rw [List.append_nil,
        show (st.waste.reverse.drop st.drawStep).reverse
            ++ (st.waste.reverse.take st.drawStep).reverse
            = ((st.waste.reverse.take st.drawStep) ++ st.waste.reverse.drop st.drawStep).reverse from
            by rw [List.reverse_append],
        take_drop_join, List.reverse_reverse]
    refine congrArg some (State.ext rfl rfl hstock.symm hwE rfl)

/-- **The in-phase round trip, witness grade.**  At a
phase-aligned position with a positive draw step, cards left in
the stock, and a nonempty whole number of deals in the waste, the
draw is undone by an explicit pure-draw play: drain the committed
stock to the pass base, then redeal exactly the waste's whole
number of deals from the recycled pool.  PORTED verbatim from
`Orig/Phase.lean:1513` (`draw_reversible_inphaseW`; the frozen
statement concludes the frozen twin of the carrier — the same
body, this card's carrier constant). -/
private theorem draw_inphase_reversibleW {st : State} (hd : 0 < st.drawStep)
    (hs : st.stock ≠ []) (hw : st.waste ≠ []) (hph : inPhase st = true) :
    reversibleAtW st Move.draw := by
  obtain ⟨c, t, hcon⟩ := list_cons_of_ne_nil hs
  have hres0 : st.waste.length % st.drawStep = 0 := by
    rw [inPhase_eq_decide_of_cons hcon] at hph
    exact of_decide_eq_true hph
  have hjd : st.drawStep * (st.waste.length / st.drawStep) = st.waste.length := by
    have := Nat.div_add_mod st.waste.length st.drawStep
    omega
  have hstep : State.step st Move.draw = some
      (State.mk st.found st.piles (st.stock.drop st.drawStep)
        ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep) :=
    plain_draw_shape hs
  obtain ⟨w0, t0, hwcon⟩ := list_cons_of_ne_nil hw
  have hw1 : 1 ≤ st.waste.length := by rw [hwcon, List.length_cons]; omega
  have hp1 : 1 ≤ st.stock.length := by rw [hcon, List.length_cons]; omega
  have hNl : (st.stock.reverse ++ st.waste).length
      = st.stock.length + st.waste.length := by
    rw [List.length_append, List.length_reverse]
  have hpool : (st.stock.drop st.drawStep).reverse
      ++ ((st.stock.take st.drawStep).reverse ++ st.waste)
      = st.stock.reverse ++ st.waste := by
    rw [show st.stock.reverse
          = (st.stock.take st.drawStep ++ st.stock.drop st.drawStep).reverse from
          congrArg List.reverse (take_drop_append st.drawStep st.stock).symm,
      List.reverse_append, List.append_assoc]
  -- the waste's whole number of deals, in successor form for the redeal leg
  rcases hqj : st.waste.length / st.drawStep with _ | jk
  · exfalso
    rw [hqj, Nat.mul_zero] at hjd
    omega
  rw [hqj] at hjd
  have hjd2 : (jk + 1) * st.drawStep = st.waste.length := by
    rw [Nat.mul_comm]
    exact hjd
  -- the pass base's pool waste carries the whole cycle; it is not empty
  have hwB : (st.stock.reverse ++ st.waste) ≠ [] := by
    intro hc
    rw [hc] at hNl
    simp only [List.length_nil] at hNl
    omega
  have hsizeB : (jk + 1) * st.drawStep
      ≤ (st.stock.reverse ++ st.waste).length := by rw [hNl]; omega
  have hmfull :=
    Nat.div_add_mod (st.stock.drop st.drawStep).length st.drawStep
  have hmodlt : (st.stock.drop st.drawStep).length % st.drawStep < st.drawStep :=
    Nat.mod_lt _ hd
  by_cases hdr : (st.stock.drop st.drawStep).length % st.drawStep = 0
  · -- the drain reaches the base at whole deals only
    have hnA : (st.stock.drop st.drawStep).length
        = ((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep := by
      rw [Nat.mul_comm]
      omega
    have hDA := drain_positions_one
      ((st.stock.drop st.drawStep).length / st.drawStep)
      (State.mk st.found st.piles (st.stock.drop st.drawStep)
        ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep)
      (st.stock.drop st.drawStep).length
      (st.stock.drop st.drawStep)
      hd hnA (Nat.le_refl _) rfl
    have hdrop0 : (st.stock.drop st.drawStep).drop
        (st.stock.drop st.drawStep).length = [] :=
      drop_ge_length _ _ (Nat.le_refl _)
    have htake0 : (st.stock.drop st.drawStep).take
        (st.stock.drop st.drawStep).length = st.stock.drop st.drawStep :=
      take_ge_length _ _ (Nat.le_refl _)
    have hSw1 : (State.mk st.found st.piles (st.stock.drop st.drawStep)
        ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep).waste
        = (st.stock.take st.drawStep).reverse ++ st.waste := rfl
    refine ⟨State.mk st.found st.piles (st.stock.drop st.drawStep)
        ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep,
      List.replicate ((st.stock.drop st.drawStep).length / st.drawStep) Move.draw
        ++ List.replicate (jk + 1) Move.draw,
      hstep, ?_⟩
    rw [run_replicate_append _ _ _ (List.replicate (jk + 1) Move.draw) hDA,
      hdrop0, htake0, hSw1, hpool]
    -- the redeal leg from the pass base
    have hb := base_positions_one jk
      (State.mk st.found st.piles ([] : List Card) (st.stock.reverse ++ st.waste) st.drawStep)
      rfl hwB hd hsizeB
    rw [hb]
    -- the two final matches: the recycled pool splits back into st
    have hz1w : (State.mk st.found st.piles ([] : List Card)
        (st.stock.reverse ++ st.waste) st.drawStep).waste
        = st.stock.reverse ++ st.waste := rfl
    have hz1d : (State.mk st.found st.piles ([] : List Card)
        (st.stock.reverse ++ st.waste) st.drawStep).drawStep
        = st.drawStep := rfl
    rw [hz1w, hz1d]
    have hSpl : st.waste.reverse ++ st.stock
        = (st.stock.reverse ++ st.waste).reverse := by
      rw [List.reverse_append, List.reverse_reverse]
    rw [← hSpl, hjd2, ← List.length_reverse, drop_append_prefix, take_append_prefix,
      List.reverse_reverse, List.append_nil]
  · -- the stock's remainder forces one boundary deal before the base
    have hqB : ((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep
        + (st.stock.drop st.drawStep).length % st.drawStep
        = (st.stock.drop st.drawStep).length := by
      have h := hmfull
      rw [Nat.mul_comm] at h
      exact h
    -- the post-drain state, restated with flat fields
    have hDB := drain_positions_one
      ((st.stock.drop st.drawStep).length / st.drawStep)
      (State.mk st.found st.piles (st.stock.drop st.drawStep)
        ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep)
      (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep)
      (st.stock.drop st.drawStep)
      hd rfl (by omega) rfl
    have hDB2 : (State.mk st.found st.piles (st.stock.drop st.drawStep)
          ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep).run
        (List.replicate ((st.stock.drop st.drawStep).length / st.drawStep) Move.draw) = some
      (State.mk st.found st.piles
        ((st.stock.drop st.drawStep).drop
          (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep))
        ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
            (List.drop st.drawStep st.stock)).reverse
          ++ ((st.stock.take st.drawStep).reverse ++ st.waste))
        st.drawStep) := by
      have hXf : (State.mk st.found st.piles (st.stock.drop st.drawStep)
          ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep).found
          = st.found := rfl
      have hXp : (State.mk st.found st.piles (st.stock.drop st.drawStep)
          ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep).piles
          = st.piles := rfl
      have hXw : (State.mk st.found st.piles (st.stock.drop st.drawStep)
          ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep).waste
          = (st.stock.take st.drawStep).reverse ++ st.waste := rfl
      have hXd : (State.mk st.found st.piles (st.stock.drop st.drawStep)
          ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep).drawStep
          = st.drawStep := rfl
      rw [hDB, hXf, hXp, hXw, hXd]
    -- the boundary draw acts on the post-drain state as a short-stock full deal
    have hx₀ne : (st.stock.drop st.drawStep).drop
        (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep) ≠ [] := by
      intro hc
      have hld := List.length_drop
        (i := ((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep)
        (l := st.stock.drop st.drawStep)
      rw [hc] at hld
      simp only [List.length_nil] at hld
      omega
    have hx₀len : ((st.stock.drop st.drawStep).drop
        (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep)).length
        < st.drawStep := by
      have hld := List.length_drop
        (i := ((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep)
        (l := st.stock.drop st.drawStep)
      rw [hld]
      omega
    have hBstep : State.step
        (State.mk st.found st.piles
          ((st.stock.drop st.drawStep).drop
            (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep))
          ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
              (List.drop st.drawStep st.stock)).reverse
            ++ ((st.stock.take st.drawStep).reverse ++ st.waste))
          st.drawStep) Move.draw = some
        (State.mk (State.mk st.found st.piles
            ((st.stock.drop st.drawStep).drop
              (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep))
            ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
                (List.drop st.drawStep st.stock)).reverse
              ++ ((st.stock.take st.drawStep).reverse ++ st.waste))
            st.drawStep).found
          (State.mk st.found st.piles
            ((st.stock.drop st.drawStep).drop
              (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep))
            ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
                (List.drop st.drawStep st.stock)).reverse
              ++ ((st.stock.take st.drawStep).reverse ++ st.waste))
            st.drawStep).piles
          ([] : List Card)
          ((State.mk st.found st.piles
              ((st.stock.drop st.drawStep).drop
                (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep))
              ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
                  (List.drop st.drawStep st.stock)).reverse
                ++ ((st.stock.take st.drawStep).reverse ++ st.waste))
              st.drawStep).stock.reverse
            ++ (State.mk st.found st.piles
              ((st.stock.drop st.drawStep).drop
                (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep))
              ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
                  (List.drop st.drawStep st.stock)).reverse
                ++ ((st.stock.take st.drawStep).reverse ++ st.waste))
              st.drawStep).waste)
          (State.mk st.found st.piles
            ((st.stock.drop st.drawStep).drop
              (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep))
            ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
                (List.drop st.drawStep st.stock)).reverse
              ++ ((st.stock.take st.drawStep).reverse ++ st.waste))
            st.drawStep).drawStep) :=
      draw_full_shape
        (State.mk st.found st.piles
          ((st.stock.drop st.drawStep).drop
            (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep))
          ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
              (List.drop st.drawStep st.stock)).reverse
            ++ ((st.stock.take st.drawStep).reverse ++ st.waste))
          st.drawStep)
        hx₀ne hx₀len
    -- the y0 position from the boundary draw carries x₀'s flat fields by iota
    have hySt : (show State from
        State.mk st.found st.piles
          ((st.stock.drop st.drawStep).drop
            (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep))
          ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
              (List.drop st.drawStep st.stock)).reverse
            ++ ((st.stock.take st.drawStep).reverse ++ st.waste))
          st.drawStep).stock
        = (st.stock.drop st.drawStep).drop
            (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep) := rfl
    have hyWs : (show State from
        State.mk st.found st.piles
          ((st.stock.drop st.drawStep).drop
            (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep))
          ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
              (List.drop st.drawStep st.stock)).reverse
            ++ ((st.stock.take st.drawStep).reverse ++ st.waste))
          st.drawStep).waste
        = (List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
              (List.drop st.drawStep st.stock)).reverse
          ++ ((st.stock.take st.drawStep).reverse ++ st.waste) := rfl
    -- the boundary segments merge into the whole stock, reversed
    have hpool2 : (((st.stock.drop st.drawStep).drop
            (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep)).reverse
          ++ ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
              (List.drop st.drawStep st.stock)).reverse
            ++ ((st.stock.take st.drawStep).reverse ++ st.waste)))
        = st.stock.reverse ++ st.waste := by
      rw [show st.stock.reverse
            = (st.stock.take st.drawStep ++ st.stock.drop st.drawStep).reverse from
            congrArg List.reverse (take_drop_append st.drawStep st.stock).symm,
        List.reverse_append,
        show (st.stock.drop st.drawStep).reverse
            = ((st.stock.drop st.drawStep).take
                (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep)
              ++ (st.stock.drop st.drawStep).drop
                (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep)).reverse from
            congrArg List.reverse
              (take_drop_append
                (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep)
                (st.stock.drop st.drawStep)).symm,
        List.reverse_append]
      simp only [List.append_assoc]
    refine ⟨State.mk st.found st.piles (st.stock.drop st.drawStep)
        ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep,
      List.replicate
        ((st.stock.drop st.drawStep).length / st.drawStep) Move.draw
        ++ (Move.draw :: List.replicate (jk + 1) Move.draw),
      hstep, ?_⟩
    rw [run_replicate_append _ _ _
      (Move.draw :: List.replicate (jk + 1) Move.draw) hDB2,
      run_draw_cons hBstep]
    -- the boundary deal's position is the pass base with the merged pool
    rw [hySt, hyWs, hpool2]
    -- the redeal leg from the pass base
    have hb := base_positions_one jk
      (State.mk st.found st.piles ([] : List Card) (st.stock.reverse ++ st.waste) st.drawStep)
      rfl hwB hd hsizeB
    rw [hb]
    -- the two final matches: the recycled pool splits back into st
    have hz1w : (State.mk st.found st.piles ([] : List Card)
        (st.stock.reverse ++ st.waste) st.drawStep).waste
        = st.stock.reverse ++ st.waste := rfl
    have hz1d : (State.mk st.found st.piles ([] : List Card)
        (st.stock.reverse ++ st.waste) st.drawStep).drawStep
        = st.drawStep := rfl
    rw [hz1w, hz1d]
    have hSpl : st.waste.reverse ++ st.stock
        = (st.stock.reverse ++ st.waste).reverse := by
      rw [List.reverse_append, List.reverse_reverse]
    rw [← hSpl, hjd2, ← List.length_reverse, drop_append_prefix, take_append_prefix,
      List.reverse_reverse, List.append_nil]

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

/-- The invariant rides along arbitrary plays.  PORTED verbatim
from `Orig/Classify.lean:932`. -/
private theorem bare_king_run : ∀ (play : List Move) (s w : State) (a : Anchor),
    BareKing (s.piles a) → s.run play = some w → BareKing (w.piles a) := by
  intro play
  induction play with
  | nil =>
      intro s w a h hrun
      injection hrun with hu
      subst hu
      exact h
  | cons m rest ih =>
      intro s w a h hrun
      obtain ⟨s₁, hstep, hrest⟩ := State.run_cons hrun
      exact ih s₁ w a (bare_king_step hstep a h) hrest

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

/-- The list-length take fact.  PORTED verbatim from
`Orig/Classify.lean:495`. -/
private theorem take_length_min {α : Type} (l : List α) : ∀ (n : Nat),
    (l.take n).length = min n l.length := by
  induction l with
  | nil =>
      intro n
      simp only [List.take_nil, List.length_nil]
      omega
  | cons x t ih =>
      intro n
      match n with
      | 0 =>
          show (0 : Nat) = min 0 (x :: t).length
          omega
      | n' + 1 =>
          show (x :: t.take n').length = min (n' + 1) (t.length + 1)
          rw [List.length_cons, ih n']
          omega

/-- Taking no deeper than an earlier take reaches the same prefix.
PORTED verbatim (the tranche's de-choice row, explicit cells —
see the frozen card's own audit note) from
`Orig/Classify.lean:521`. -/
private theorem take_take_le {α : Type} (l : List α) : ∀ (m n : Nat), m ≤ n →
    (l.take n).take m = l.take m := by
  induction l with
  | nil => intro m n _; rw [List.take_nil]
  | cons x t ih =>
      intro m n
      match m with
      | 0 => intro _; rfl
      | m' + 1 =>
          match n with
          | 0 => intro hle; exact absurd hle (Nat.not_succ_le_zero m')
          | n' + 1 =>
              intro hle
              exact congrArg (x :: ·) (ih (m') (n') (Nat.le_of_succ_le_succ hle))

/-- Taking to a list's own length is the identity.  PORTED verbatim
from `Orig/Classify.lean:537`. -/
private theorem take_length_self {α : Type} (l : List α) : l.take l.length = l := by
  induction l with
  | nil => rfl
  | cons x t ih =>
      show x :: t.take t.length = x :: t
      exact congrArg (x :: ·) ih

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

/-- The tabulation inverts the rank index.  PORTED verbatim from
`Orig/FoundKit.lean:376`. -/
private theorem Rk_toIdx : ∀ (k : Nat), k < 13 → (Rk k).toIdx = k := by
  intro k hk
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | 9 => rfl
  | 10 => rfl
  | 11 => rfl
  | 12 => rfl
  | j + 13 => exact absurd hk (by omega)

/-- PORTED verbatim from `Orig/Classify.lean:558`. -/
private theorem rank_all_drop_cons : ∀ (k : Nat), k < 13 →
    Rank.all.drop k = Rk k :: Rank.all.drop (k + 1) := by
  intro k hk
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | 9 => rfl
  | 10 => rfl
  | 11 => rfl
  | 12 => rfl
  | w + 13 => exact absurd hk (by omega)

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

/-! ## The audit battery

Per proved head, this batch.  Expected profile per the card header:
`[propext]` or `[propext, Quot.sound]` — never `sorryAx`, never
`Classical.choice`. -/

#print axioms wasteToFound_not_reversibleAtW
#print axioms wasteToTab_not_reversibleAtW
#print axioms drawR_iff_reversibleAtW
#print axioms tabToFoundR_iff_reversibleAtW
#print axioms foundToTabR_iff_reversibleAtW
