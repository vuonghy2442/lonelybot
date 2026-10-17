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

/-! ## The audit battery

Per proved head, this batch.  Expected profile per the card header:
`[propext]` or `[propext, Quot.sound]` — never `sorryAx`, never
`Classical.choice`. -/

#print axioms wasteToFound_not_reversibleAtW
#print axioms wasteToTab_not_reversibleAtW
#print axioms drawR_iff_reversibleAtW
