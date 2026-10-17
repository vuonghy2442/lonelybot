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

/-! ## The audit battery

Per proved head, this batch.  Expected profile per the card header:
`[propext]` or `[propext, Quot.sound]` — never `sorryAx`, never
`Classical.choice`. -/

#print axioms wasteToFound_not_reversibleAtW
#print axioms wasteToTab_not_reversibleAtW
