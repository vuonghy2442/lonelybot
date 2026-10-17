import Orig2.Vocab

/-!
# Orig2.Kit — THE PHYSICS KIT (the reusable tier)

PROMOTION NOTE (2026-10-17, owner decree): the general physics rows
that the cards had been re-landing as per-file private copies are
promoted to this shared kit so that every `Orig2` card reads ONE
copy; the classification card's former §0 and §1a-§1k move here
with their per-row provenance docstrings intact.

THE IMPORT SURFACE: exactly `Orig2.Vocab` (hence the certified core
seam `Orig.Basic`/`Orig.State`/`Orig.Play`).  The fate-tier
collision that keeps the frozen physics modules (`Orig.Mono`,
`Orig.Irreversible`, `Orig.Phase`, `Orig.Integrity`)
unimportable applies unchanged — nothing above the core seam is
imported here — so every row below keeps its frozen cite.

CONTENTS: the witness-grade bridge (the vacuous denial and the
measure denial), the run engine (`run_rec` and its instances
`mono_run`), the constructive list kit, the
placement field-keepers and guard inversions, the step inversions,
the measure tables (`cycleCount`, `hiddenTotal`) with their strict
rows, the phase line, ONE draw footprint (the single home of the
`dealUpTo` arithmetic) with the four draw round trips, the pristine
invariant kit, and the lex descent kit.

House compliance: per-row provenance docstrings retained; zero
`sorry`; `Classical.choice` NEVER (core's `List.take_add` is
choice-bearing, which is exactly why the constructive row
`take_drop_add` is kept); the battery at the tail.
-/

/-!
## §0. THE WITNESS-GRADE BRIDGE

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
theorem not_W_of_step_none {st : State} {m : Move}
    (h : State.step st m = none) : ¬ reversibleAtW st m := by
  rintro ⟨s₁, play, hstep, -⟩
  rw [h] at hstep
  exact absurd hstep (by simp)

/-- **The one-mirror witness handoff** (this kit's own row): if a
single mirror move returns from the committed successor, the
carrier's witness exists.  The constructive arms of the cards'
round trips ride this one tool; the frozen cards inlined the same
`⟨s₁, [m'], hstep, simp only [State.run, hret]⟩` dance at every
arm. -/
theorem reversible_mirrorW {st s₁ : State} {m : Move} {m' : Move}
    (hstep : State.step st m = some s₁) (hret : State.step s₁ m' = some st) :
    reversibleAtW st m :=
  ⟨s₁, [m'], hstep, by simp only [State.run, hret]⟩

/-!
## §1. THE PHYSICS KIT  (the seam annex, promoted)

Everything between the core seam and the letters, re-landed from
the frozen tier reading, never imported.  Sources cited per row.
Subsections: the monotone bridge (with the measure denial that
rides it), the measures and their flat-map kit, the placement
field-keepers and guard inversions, the draw pipeline, the step
inversions, the cycle-count table, the hidden-total table.
-/

/-! ### §1a. The monotone bridge -/

/-- **The play-lift induction principle** (this card's own row): every
invariant that walks a play rides this one recursion; the specific
lifts (`mono_run`, `run_cycleCount_le`,
`bare_king_run`) are its instances.  The motive `P` is an explicit
argument — each instance names its own invariant. -/
theorem run_rec (P : State → State → Prop)
    (hstep : ∀ {x m y rest w}, State.step x m = some y → y.run rest = some w →
      P y w → P x w) (hnil : ∀ x, P x x) :
    ∀ {play : List Move} {x w}, x.run play = some w → P x w := by
  intro play
  induction play with
  | nil =>
      intro x w h
      injection h with hh
      rw [← hh]
      exact hnil x
  | cons m rest ih =>
      intro x w h
      obtain ⟨s₁, h1, h2⟩ := State.run_cons h
      exact hstep h1 h2 (ih h2)

/-- A play whose every legal step descends in `Q` (`Q s' ≤ Q s`)
ends at a position no higher than its start.  PORTED from
`Orig/Mono.lean:40` (`mono_run`; the frozen file rides above the
core seam via `Orig.Fate`, vetoed here — see the header). -/
theorem mono_run (Q : State → Nat)
    (h : ∀ s m s', State.step s m = some s' → Q s' ≤ Q s) :
    ∀ {s play w}, s.run play = some w → Q w ≤ Q s :=
  run_rec (fun x y => Q y ≤ Q x)
    (fun hstep _ ih => Nat.le_trans ih (h _ _ _ hstep))
    (fun x => Nat.le_refl (Q x))

/-- A strictly descending one-step measure denies the carrier: a
returning play would walk the measure back up from below its own
start while every step only descends — the witness-grade
re-statement of `Orig/Mono.lean:82` `irr_of_desc` (same walk, the
negated existential taken directly; the frozen original is stated
at the retired grade). -/
theorem not_W_of_desc (Q : State → Nat)
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
def cycleCount (st : State) : Nat := st.stock.length + st.waste.length

/-- The face-down cards across the seven piles, as one flat sum.
PORTED verbatim from `Orig/Irreversible.lean:71`. -/
def hiddenTotal (st : State) : Nat :=
  (Anchor.all.flatMap fun a => (st.piles a).hidden).length

/-- Flat map unrolls one head element.  PORTED from
`Orig/Irreversible.lean:81`. -/
theorem flatMap_cons {α β : Type} (f : α → List β) (x : α) (t : List α) :
    List.flatMap f (x :: t) = f x ++ List.flatMap f t := rfl

/-- Pointwise pile-hidden equality gives hidden-total equality.
PORTED from `Orig/Irreversible.lean:85`. -/
theorem hiddenTotal_congr {s s' : State}
    (h : ∀ a, (s'.piles a).hidden = (s.piles a).hidden) :
    hiddenTotal s' = hiddenTotal s := by
  unfold hiddenTotal
  rw [show (fun a => (s'.piles a).hidden) = (fun a => (s.piles a).hidden) from funext h]

/-- A flat map is length-monotone in the summed function.  PORTED
from `Orig/Irreversible.lean:99`. -/
theorem flatMap_length_mono {α : Type} (F G : α → List Card) (as : List α)
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
theorem flatMap_length_mono_lt {α : Type} (F G : α → List Card) (as : List α) (x : α)
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
theorem hiddenTotal_mono {s s' : State}
    (h : ∀ a, (s'.piles a).hidden.length ≤ (s.piles a).hidden.length) :
    hiddenTotal s' ≤ hiddenTotal s :=
  flatMap_length_mono _ _ _ h

/-- The strict witness lemma: dropping one pile's hidden count by
one drops the total by at least one, nothing anywhere growing.
PORTED from `Orig/Irreversible.lean:752`. -/
theorem hiddenTotal_mono_lt {s s' : State} {a : Anchor}
    (hle : ∀ a', (s'.piles a').hidden.length ≤ (s.piles a').hidden.length)
    (hlt : (s'.piles a).hidden.length + 1 ≤ (s.piles a).hidden.length) :
    hiddenTotal s' + 1 ≤ hiddenTotal s :=
  flatMap_length_mono_lt _ _ Anchor.all a (Anchor.mem_all a) hle hlt

/-- The hidden-cards trichotomy of the run removal.  PORTED
verbatim from `Orig/Irreversible.lean:157`. -/
theorem afterRunRemoved_hidden (p : Pile) (pre : List Card) :
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
theorem afterRunRemoved_hidden_le (p : Pile) (pre : List Card) :
    (Pile.afterRunRemoved p pre).hidden.length ≤ p.hidden.length := by
  rcases afterRunRemoved_hidden p pre with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
  · rw [h]; exact Nat.le_refl _
  · rw [h]; exact Nat.le_refl _
  · omega

/-! ### §1c. The placement field-keepers and guard inversions -/

/-- `setPile` keeps the stock.  PORTED from
`Orig/Irreversible.lean:191`. -/
theorem setPile_stock (st : State) (a : Anchor) (p : Pile) :
    (st.setPile a p).stock = st.stock := rfl

/-- `setPile` keeps the waste.  PORTED from
`Orig/Irreversible.lean:195`. -/
theorem setPile_waste (st : State) (a : Anchor) (p : Pile) :
    (st.setPile a p).waste = st.waste := rfl

/-- `setPile` keeps the draw step.  PORTED from
`Orig/Irreversible.lean:199`. -/
theorem setPile_drawStep (st : State) (a : Anchor) (p : Pile) :
    (st.setPile a p).drawStep = st.drawStep := rfl

/-- `setFound` keeps the stock.  PORTED from
`Orig/Irreversible.lean:208`. -/
theorem setFound_stock (st : State) (s : Suit) (l : List Card) :
    (st.setFound s l).stock = st.stock := rfl

/-- `setFound` keeps the waste.  PORTED from
`Orig/Irreversible.lean:212`. -/
theorem setFound_waste (st : State) (s : Suit) (l : List Card) :
    (st.setFound s l).waste = st.waste := rfl

/-- `setFound` keeps the tableau.  PORTED from
`Orig/Irreversible.lean:216`. -/
theorem setFound_piles (st : State) (s : Suit) (l : List Card) :
    (st.setFound s l).piles = st.piles := rfl

/-- `setFound` keeps the draw step.  PORTED from
`Orig/Irreversible.lean:220`. -/
theorem setFound_drawStep (st : State) (s : Suit) (l : List Card) :
    (st.setFound s l).drawStep = st.drawStep := rfl

/-- `putCard` keeps the stock.  PORTED from
`Orig/Irreversible.lean:224`. -/
theorem putCard_stock (st : State) (c : Card) (b : Base) :
    (st.putCard c b).stock = st.stock := by
  cases b with
  | inl a => rfl
  | inr z => cases hz : st.pileOfTop z <;> simp [State.putCard, hz] <;> rfl

/-- `putCard` keeps the waste.  PORTED from
`Orig/Irreversible.lean:231`. -/
theorem putCard_waste (st : State) (c : Card) (b : Base) :
    (st.putCard c b).waste = st.waste := by
  cases b with
  | inl a => rfl
  | inr z => cases hz : st.pileOfTop z <;> simp [State.putCard, hz] <;> rfl

/-- `putCard` keeps the foundations.  PORTED from
`Orig/Irreversible.lean:238`. -/
theorem putCard_found (st : State) (c : Card) (b : Base) :
    (st.putCard c b).found = st.found := by
  cases b with
  | inl a => rfl
  | inr z => cases hz : st.pileOfTop z <;> simp [State.putCard, hz] <;> rfl

/-- `putCard` keeps the draw step.  PORTED from
`Orig/Irreversible.lean:245`. -/
theorem putCard_drawStep (st : State) (c : Card) (b : Base) :
    (st.putCard c b).drawStep = st.drawStep := by
  cases b with
  | inl a => rfl
  | inr z => cases hz : st.pileOfTop z <;> simp [State.putCard, hz] <;> rfl

/-- `putRun` keeps the stock.  PORTED from
`Orig/Irreversible.lean:252`. -/
theorem putRun_stock (st : State) (run : List Card) (b : Base) :
    (st.putRun run b).stock = st.stock := by
  cases b with
  | inl a => rfl
  | inr z => cases hz : st.pileOfTop z <;> simp [State.putRun, hz] <;> rfl

/-- `putRun` keeps the waste.  PORTED from
`Orig/Irreversible.lean:259`. -/
theorem putRun_waste (st : State) (run : List Card) (b : Base) :
    (st.putRun run b).waste = st.waste := by
  cases b with
  | inl a => rfl
  | inr z => cases hz : st.pileOfTop z <;> simp [State.putRun, hz] <;> rfl

/-- `putRun` keeps the foundations.  PORTED from
`Orig/Irreversible.lean:266`. -/
theorem putRun_found (st : State) (run : List Card) (b : Base) :
    (st.putRun run b).found = st.found := by
  cases b with
  | inl a => rfl
  | inr z => cases hz : st.pileOfTop z <;> simp [State.putRun, hz] <;> rfl

/-- `putRun` keeps the draw step.  PORTED from
`Orig/Irreversible.lean:273`. -/
theorem putRun_drawStep (st : State) (run : List Card) (b : Base) :
    (st.putRun run b).drawStep = st.drawStep := by
  cases b with
  | inl a => rfl
  | inr z => cases hz : st.pileOfTop z <;> simp [State.putRun, hz] <;> rfl

/-- A single card onto an empty seat writes exactly that pile to
the singleton card.  PORTED from `Orig/Irreversible.lean:281`. -/
theorem putCard_piles_inl (st : State) (c : Card) (a : Anchor) :
    (st.putCard c (Sum.inl a)).piles =
      (fun a' => if a' = a then ⟨[], [c]⟩ else st.piles a') := rfl

/-- A single card onto a card base appends to the located pile.
PORTED from `Orig/Irreversible.lean:286`. -/
theorem putCard_piles_inr (st : State) (c : Card) (z : Card) (k : Anchor)
    (hz : st.pileOfTop z = some k) :
    (st.putCard c (Sum.inr z)).piles =
      (fun a' => if a' = k then { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }
        else st.piles a') := by
  simp only [State.putCard, hz]
  rfl

/-- Putting a run onto an empty seat writes exactly that pile.
PORTED from `Orig/Irreversible.lean:295`. -/
theorem putRun_piles_inl (st : State) (run : List Card) (a : Anchor) :
    (st.putRun run (Sum.inl a)).piles =
      (fun a' => if a' = a then ⟨[], run⟩ else st.piles a') := rfl

/-- Putting a run onto a card base appends to the located pile.
PORTED from `Orig/Irreversible.lean:300`. -/
theorem putRun_piles_inr (st : State) (run : List Card) (z : Card) (k : Anchor)
    (hz : st.pileOfTop z = some k) :
    (st.putRun run (Sum.inr z)).piles =
      (fun a' => if a' = k then { st.piles k with faceUp := (st.piles k).faceUp ++ run }
        else st.piles a') := by
  simp only [State.putRun, hz]
  rfl

/-- The pointwise self read of an inl landing.  PORTED from
`Orig/Irreversible.lean:312`. -/
theorem putRun_piles_inl_self (st : State) (run : List Card) (a : Anchor) :
    (st.putRun run (Sum.inl a)).piles a = ⟨[], run⟩ := by
  rw [putRun_piles_inl]
  exact ite_eq_left rfl

/-- The pointwise other-pile read of an inl landing.  PORTED from
`Orig/Irreversible.lean:318`. -/
theorem putRun_piles_inl_ne (st : State) (run : List Card) (a a' : Anchor)
    (hne : a' ≠ a) :
    (st.putRun run (Sum.inl a)).piles a' = st.piles a' := by
  rw [putRun_piles_inl]
  exact ite_eq_right hne

/-- The pointwise self read of an inr landing.  PORTED from
`Orig/Irreversible.lean:325`. -/
theorem putRun_piles_inr_self (st : State) (run : List Card) (z : Card)
    (k : Anchor) (hz : st.pileOfTop z = some k) :
    (st.putRun run (Sum.inr z)).piles k
      = { st.piles k with faceUp := (st.piles k).faceUp ++ run } := by
  rw [putRun_piles_inr _ _ _ _ hz]
  exact ite_eq_left rfl

/-- The pointwise other-pile read of an inr landing.  PORTED from
`Orig/Irreversible.lean:333`. -/
theorem putRun_piles_inr_ne (st : State) (run : List Card) (z : Card)
    (k : Anchor) (hz : st.pileOfTop z = some k) {a' : Anchor}
    (hne : a' ≠ k) :
    (st.putRun run (Sum.inr z)).piles a' = st.piles a' := by
  rw [putRun_piles_inr _ _ _ _ hz]
  exact ite_eq_right hne

/-- The empty-seat placement guard: empty target, king card.
PORTED from `Orig/Irreversible.lean:343`. -/
theorem canPlace_inl {st : State} {c : Card} {a : Anchor}
    (h : st.canPlace c (Sum.inl a) = true) :
    (st.piles a).isEmpty = true ∧ c.rank = Rank.king := by
  simp only [State.canPlace, Bool.and_eq_true] at h
  exact ⟨h.1, of_decide_eq_true h.2⟩

/-- The card-on-card placement guard: the base card tops some pile
and the mover fits under it.  PORTED from
`Orig/Irreversible.lean:351`. -/
theorem canPlace_inr {st : State} {c z : Card}
    (h : st.canPlace c (Sum.inr z) = true) :
    ∃ k, st.pileOfTop z = some k ∧ canSitOn c z = true := by
  simp only [State.canPlace] at h
  cases hz : st.pileOfTop z with
  | none => rw [hz] at h; exact absurd h (by simp)
  | some k => rw [hz] at h; exact ⟨k, rfl, h⟩

/-- A pile is empty iff both of its parts are.  PORTED from
`Orig/Integrity.lean:69`. -/
theorem Pile.isEmpty_eq (p : Pile) :
    p.isEmpty = true ↔ p.hidden = [] ∧ p.faceUp = [] := by
  rcases p with ⟨h, f⟩
  cases h <;> cases f <;> simp [Pile.isEmpty]

/-- A pile holding `c` face up is not empty.  PORTED from
`Orig/Irreversible.lean:742`. -/
theorem Pile.isEmpty_eq_false_of_mem {p : Pile} {c : Card}
    (h : c ∈ p.faceUp) : p.isEmpty = false := by
  rcases p with ⟨hd, f⟩
  cases f with
  | nil => cases h
  | cons x fs => cases hd <;> rfl

/-- A legal placement never disturbs hidden cards.  PORTED from
`Orig/Irreversible.lean:646`. -/
theorem putCard_hidden_eq {st : State} {c : Card} {b : Base}
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
theorem setPile_afterRunRemoved_hidden_le (st : State) (a : Anchor) (c : Card)
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
theorem setPile_afterRunRemoved_piles_self (st : State) (a : Anchor) (c : Card) :
    (st.setPile a
      (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles a
      = Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp) := by
  simp only [State.setPile]
  rw [ite_true]

/-- The run-removal `setPile` leaves every other pile alone.
PORTED from `Orig/Irreversible.lean:858`. -/
theorem setPile_afterRunRemoved_piles_ne (st : State) (a : Anchor) (c : Card)
    (a' : Anchor) (hne : a' ≠ a) :
    (st.setPile a
      (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles a'
      = st.piles a' := by
  simp only [State.setPile]
  rw [ite_eq_right hne]

/-! ### §1d. The draw pipeline: ONE draw footprint

The frozen tier carried four independent unfoldings of the same
`dealUpTo` arithmetic (Irreversible's `stepDraw` rows over
`dealStock_inv`, Phase's `cycleCount`/`drawStep` rows over
`draw_unfold`); this card folds them into ONE recycle-level
conservation row, `draw_footprint`, and every other draw fact is a
projection or a case split on it. -/

/-- Recycling keeps the cycle count.  PORTED from
`Orig/Irreversible.lean:392`. -/
theorem recycle_cycle (st : State) : cycleCount st.recycle = cycleCount st := by
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
theorem recycle_piles (st : State) : st.recycle.piles = st.piles := by
  cases hs : st.stock <;> cases hw : st.waste <;>
    simp only [State.recycle, hs, hw]

/-- Recycling keeps the foundations.  PORTED from
`Orig/Irreversible.lean:411`. -/
theorem recycle_found (st : State) : st.recycle.found = st.found := by
  cases hs : st.stock <;> cases hw : st.waste <;>
    simp only [State.recycle, hs, hw]

/-- Recycling leaves the draw step alone.  PORTED from
`Orig/Phase.lean:247`. -/
theorem recycle_drawStep (st : State) :
    (State.recycle st).drawStep = st.drawStep := by
  by_cases hst : st.stock = []
  · by_cases hw : st.waste = []
    · rw [recycle_allEmpty st hst hw]
    · rw [recycle_nil st hst hw]
  · rw [recycle_keep st hst]

/-- Lengths of the `dealUpTo` split.  PORTED from
`Orig/Phase.lean:123`. -/
theorem dealUpTo_lens (k : Nat) : ∀ (l : List Card),
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

/-- **The draw footprint** (this card's own row): one successful
draw, as six facts at the recycled base — the draw step, the
foundations, and the piles verbatim; the cycle count conserved; the
dealt/split lengths exact.  One home for the dealUpTo arithmetic of
the four frozen draw analyses.  FOLD-PORT of
`Orig/Irreversible.lean:438/:445/:454` and
`Orig/Phase.lean:204/:256`. -/
theorem draw_footprint {x y : State} (h : x.stepDraw = some y) :
    y.drawStep = x.drawStep ∧ y.found = x.found ∧ y.piles = x.piles ∧
    cycleCount y = cycleCount x ∧
    y.stock.length + min (State.recycle x).drawStep (State.recycle x).stock.length
      = (State.recycle x).stock.length ∧
    y.waste.length
      = min (State.recycle x).drawStep (State.recycle x).stock.length
        + (State.recycle x).waste.length := by
  obtain ⟨r, hrec, -, hy⟩ := draw_unfold h
  subst hrec
  subst hy
  obtain ⟨h1, h2⟩ := dealUpTo_lens (State.recycle x).drawStep (State.recycle x).stock
  have rc : (State.recycle x).stock.length + (State.recycle x).waste.length
      = x.stock.length + x.waste.length := recycle_cycle x
  refine ⟨recycle_drawStep x, recycle_found x, recycle_piles x, ?_, ?_, ?_⟩
  · show (State.dealUpTo (State.recycle x).drawStep (State.recycle x).stock).2.length
        + ((State.dealUpTo (State.recycle x).drawStep (State.recycle x).stock).1.reverse
            ++ (State.recycle x).waste).length
      = x.stock.length + x.waste.length
    rw [List.length_append, List.length_reverse]
    omega
  · show (State.dealUpTo (State.recycle x).drawStep (State.recycle x).stock).2.length
        + min (State.recycle x).drawStep (State.recycle x).stock.length
      = (State.recycle x).stock.length
    omega
  · show ((State.dealUpTo (State.recycle x).drawStep (State.recycle x).stock).1.reverse
        ++ (State.recycle x).waste).length
      = min (State.recycle x).drawStep (State.recycle x).stock.length
        + (State.recycle x).waste.length
    rw [List.length_append, List.length_reverse]
    omega

/-- A successful draw conserves the cycle count exactly.  PORTED
from `Orig/Irreversible.lean:454` — a footprint projection. -/
theorem draw_cycleCount {x y : State} (h : x.stepDraw = some y) :
    cycleCount y = cycleCount x := (draw_footprint h).2.2.2.1

/-- Every state along a draw has the same draw step as its parent.
PORTED from `Orig/Phase.lean:256` — a footprint projection. -/
theorem draw_drawStep {x y : State} (h : x.stepDraw = some y) :
    y.drawStep = x.drawStep := (draw_footprint h).1

/-- A successful draw keeps the foundations.  PORTED from
`Orig/Irreversible.lean:445` — a footprint projection. -/
theorem stepDraw_found {st s' : State} (h : st.stepDraw = some s') :
    s'.found = st.found := (draw_footprint h).2.1

/-- A successful draw keeps the piles.  PORTED from
`Orig/Irreversible.lean:438` — a footprint projection. -/
theorem stepDraw_piles {st s' : State} (h : st.stepDraw = some s') :
    s'.piles = st.piles := (draw_footprint h).2.2.1

/-! ### §1e. The step inversions -/

/-- A successful `.wasteToFound`: the guard held, the waste was
nonempty, and the successor is the written foundation with the
waste popped.  PORTED from `Orig/Irreversible.lean:476`. -/
theorem step_wasteToFound_inv {st : State} {c : Card} {s' : State}
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
theorem step_wasteToTab_inv {st : State} {c : Card} {b : Base} {s' : State}
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
theorem step_tabToFound_inv {st : State} {c : Card} {s' : State}
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
theorem tabToFound_found_trio {st s₁ : State} {c : Card} {a : Anchor}
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
theorem step_foundToTab_inv {st : State} {c : Card} {b : Base} {s' : State}
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
theorem step_tabToTab_inv {st : State} {c : Card} {b : Base} {s' : State}
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
theorem pileHolding_mem {st : State} {c : Card} {a : Anchor}
    (h : st.pileHolding c = some a) : c ∈ (st.piles a).faceUp :=
  of_decide_eq_true (firstWhere_sound (p := fun a' => decide (c ∈ (st.piles a').faceUp)) h)

/-- Same stock and waste give the same cycle count.  PORTED from
`Orig/Irreversible.lean:685`. -/
theorem cycleCount_eq_of_stock_waste {s s' : State}
    (hst : s'.stock = s.stock) (hwa : s'.waste = s.waste) :
    cycleCount s' = cycleCount s := by
  show s'.stock.length + s'.waste.length = s.stock.length + s.waste.length
  rw [hst, hwa]

/-- A successful `.wasteToFound` pops the waste, so the cycle
count strictly drops.  PORTED from `Orig/Irreversible.lean:692`. -/
theorem cycleCount_step_wasteToFound {st : State} {c : Card} {s' : State}
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
theorem cycleCount_step_wasteToTab {st : State} {c : Card} {b : Base} {s' : State}
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
theorem cycleCount_step {st : State} {m : Move} {s' : State}
    (h : State.step st m = some s') : cycleCount s' ≤ cycleCount st := by
  cases m with
  | draw => have := draw_cycleCount h; omega
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
theorem tabToFound_pile_le (st : State) (c : Card) (a : Anchor) (a' : Anchor) :
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
theorem tabToTab_a_hidden (st : State) (a : Anchor) (c : Card) (b : Base)
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
theorem tabToTab_pile_le (st : State) (a : Anchor) (c : Card) (b : Base)
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
theorem hiddenTotal_step_tabToTab_reveal {st : State} {c : Card} {b : Base}
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
theorem hiddenTotal_step_tabToFound_reveal {st : State} {c : Card} {a : Anchor}
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
theorem hiddenTotal_step {st : State} {m : Move} {s' : State}
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
      obtain ⟨a, -, -, -, hs⟩ := step_tabToTab_inv h
      rw [hs]
      exact hiddenTotal_mono (fun a' => tabToTab_pile_le st a c b a')

/-! ### §1h. The phase line

`Orig.Phase`'s phase predicate with its decisive rows (the trap:
every recycled draw lands phase-aligned, and alignment is preserved
by every draw).  The `dealUpTo` length facts now live at §1d's
footprint; the full-deal rows remain here. -/

/-- A full deal: when the list has no more than `k` cards, every
card is dealt and nothing remains.  PORTED verbatim from
`Orig/Phase.lean:159`. -/
theorem dealUpTo_all (k : Nat) : ∀ (l : List Card), l.length ≤ k →
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
theorem dealStock_full {st : State} (hs : st.stock ≠ [])
    (hsize : st.stock.length ≤ st.drawStep) :
    State.dealStock st = some
      { st with stock := ([] : List Card), waste := st.stock.reverse ++ st.waste } := by
  rw [dealStock_eq_of_ne_nil st hs, dealUpTo_all st.drawStep st.stock hsize]

/-- The toolchain's Boolean dichotomy.  PORTED from
`Orig/Phase.lean:55`. -/
theorem bool_dich (b : Bool) : b = true ∨ b = false := by
  cases b <;> simp

/-- `true` exactly at the phase boundaries of the draw cycle: no
cards remain in the stock ("at the end"), or the waste holds a
whole number of deals so the next recycle would begin cleanly.
PORTED verbatim from `Orig/Phase.lean:63`. -/
def inPhase (st : State) : Bool :=
  match st.stock with
  | [] => true
  | _ => decide (st.waste.length % st.drawStep = 0)

/-- With cards left in the stock, `inPhase` is literally the decide
on the waste residue.  PORTED verbatim from `Orig/Phase.lean:70`.
-/
theorem inPhase_eq_decide_of_cons {st : State} {c : Card} {t : List Card}
    (hcon : st.stock = c :: t) :
    inPhase st = decide (st.waste.length % st.drawStep = 0) := by
  simp only [inPhase, hcon]

/-- `inPhase` depends only on the stock, the waste, and the draw
step.  PORTED verbatim from `Orig/Phase.lean:76`. -/
theorem inPhase_congr {x y : State} (h1 : x.stock = y.stock)
    (h2 : x.waste = y.waste) (h3 : x.drawStep = y.drawStep) :
    inPhase x = inPhase y := by
  simp only [inPhase, h1, h2, h3]

/-- No stock cards means aligned: the cycle sits at its end.
PORTED verbatim from `Orig/Phase.lean:82`. -/
theorem inPhase_eq_true_of_nil {st : State} (hnil : st.stock = []) :
    inPhase st = true := by
  simp only [inPhase, hnil]

/-- `inPhase = false` is exactly the offset condition.  PORTED
verbatim from `Orig/Phase.lean:88`. -/
theorem inPhase_eq_false_iff {st : State} :
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
stock (a recycle) lands phase-aligned.  PORTED from
`Orig/Phase.lean:268` (the §1d footprint's split arithmetic). -/
theorem draw_nil_inPhase {x y : State} (hst : x.stock = [])
    (hsuc : x.stepDraw = some y) : inPhase y = true := by
  by_cases hw : x.waste = []
  · exfalso
    obtain ⟨_, hrec, hrne, -⟩ := draw_unfold hsuc
    rw [← hrec, recycle_allEmpty x hst hw, hst] at hrne
    exact absurd rfl hrne
  · obtain ⟨-, -, -, -, hS, hW⟩ := draw_footprint hsuc
    rw [recycle_nil x hst hw] at hS hW
    have hS2 : y.stock.length + min x.drawStep x.waste.reverse.length
        = x.waste.reverse.length := hS
    have hW2 : y.waste.length = min x.drawStep x.waste.reverse.length
        + ([] : List Card).length := hW
    rw [List.length_reverse] at hS2 hW2
    rw [List.length_nil] at hW2
    rcases Nat.lt_or_ge x.drawStep x.waste.length with hlt | hge
    · have hmin : min x.drawStep x.waste.length = x.drawStep :=
        Nat.min_eq_left (Nat.le_of_lt hlt)
      rw [hmin] at hS2 hW2
      have hyne : y.stock ≠ [] := by
        intro hc0
        rw [hc0] at hS2
        simp only [List.length_nil] at hS2
        omega
      obtain ⟨c', t', hys⟩ := list_cons_of_ne_nil hyne
      rw [inPhase_eq_decide_of_cons hys, hW2, draw_drawStep hsuc, Nat.add_zero,
        Nat.mod_self]
      rfl
    · have hmin : min x.drawStep x.waste.length = x.waste.length :=
        Nat.min_eq_right hge
      rw [hmin] at hS2
      have hy0 : y.stock = [] := List.length_eq_zero_iff.mp (by omega)
      exact inPhase_eq_true_of_nil hy0

/-- **The second half of the trap.**  Alignment is drawn into: a
draw from a phase-aligned position stays phase-aligned.  PORTED
from `Orig/Phase.lean:315` (the §1d footprint's split arithmetic). -/
theorem draw_keeps_inPhase {x y : State} (hsuc : x.stepDraw = some y)
    (hin : inPhase x = true) : inPhase y = true := by
  by_cases hst : x.stock = []
  · exact draw_nil_inPhase hst hsuc
  · obtain ⟨-, -, -, -, hS, hW⟩ := draw_footprint hsuc
    rw [recycle_keep x hst] at hS hW
    obtain ⟨c, t, hcon⟩ := list_cons_of_ne_nil hst
    have hres : x.waste.length % x.drawStep = 0 := by
      rw [inPhase_eq_decide_of_cons hcon] at hin
      exact of_decide_eq_true hin
    rcases Nat.lt_or_ge x.drawStep x.stock.length with hlt | hge
    · have hmin : min x.drawStep x.stock.length = x.drawStep :=
        Nat.min_eq_left (Nat.le_of_lt hlt)
      rw [hmin] at hS hW
      have hyne : y.stock ≠ [] := by
        intro hc0
        rw [hc0] at hS
        simp only [List.length_nil] at hS
        omega
      obtain ⟨c', t', hys⟩ := list_cons_of_ne_nil hyne
      rw [inPhase_eq_decide_of_cons hys, hW, draw_drawStep hsuc, Nat.add_mod_left]
      exact decide_eq_true hres
    · have hmin : min x.drawStep x.stock.length = x.stock.length :=
        Nat.min_eq_right hge
      rw [hmin] at hS
      have hy0 : y.stock = [] := List.length_eq_zero_iff.mp (by omega)
      exact inPhase_eq_true_of_nil hy0

/-! ### §1i. The pristine-commit kit

The invariant-carrying half of `Orig.Phase`'s draw commit bank: the
fixed-field rows, the never-emptying-waste invariant along
waste-free plays, and the committed successor of a pristine draw.
Ends at the carrier grade: `draw_notW_of_pristine`.  The waste
moves' strict cycle drops ride §1f's inversions-shaped rows
(`cycleCount_step_wasteTo*`) — the frozen Step re-derivations
(`Orig/Phase.lean:371/:382/:401`, putCard_zone_keep and the
`cycleCount_lt_*` pair) retire here; the per-move cycle table is
§1f's `cycleCount_step` alone.
-/

/-- The two moves that spend a waste card.  PORTED verbatim from
`Orig/Phase.lean:363`. -/
def isWasteMove (m : Move) : Bool :=
  match m with
  | .wasteToFound _ => true
  | .wasteToTab _ _ => true
  | _ => false

/-- A pile top onto its foundation leaves the stock, the waste, and
the draw step verbatim.  PORTED from `Orig/Phase.lean:421` (the
§1e inversions replace the frozen step unfolding). -/
theorem tabToFound_fixed {x y : State} {c : Card}
    (h : State.step x (.tabToFound c) = some y) :
    y.stock = x.stock ∧ y.waste = x.waste ∧ y.drawStep = x.drawStep := by
  obtain ⟨-, a, -, hs⟩ := step_tabToFound_inv h
  rw [hs]
  exact ⟨rfl, rfl, rfl⟩

/-- A foundation top back onto the tableau leaves the stock, the
waste, and the draw step verbatim.  PORTED from
`Orig/Phase.lean:435` (the §1e inversions; the seam's
`putCard_keep` carries the fields). -/
theorem foundToTab_fixed {x y : State} {c : Card} {b : Base}
    (h : State.step x (.foundToTab c b) = some y) :
    y.stock = x.stock ∧ y.waste = x.waste ∧ y.drawStep = x.drawStep := by
  obtain ⟨-, -, -, -, hs⟩ := step_foundToTab_inv h
  rw [hs]
  exact ⟨putCard_keep.2.1, putCard_keep.2.2.1, putCard_keep.2.2.2⟩

/-- A run between piles leaves the stock, the waste, and the draw
step verbatim.  PORTED from `Orig/Phase.lean:450` (the §1e
inversions; the seam's `putRun_keep` carries the fields,
`Orig/Play.lean:537`). -/
theorem tabToTab_fixed {x y : State} {c : Card} {b : Base}
    (h : State.step x (.tabToTab c b) = some y) :
    y.stock = x.stock ∧ y.waste = x.waste ∧ y.drawStep = x.drawStep := by
  obtain ⟨a, -, -, -, hs⟩ := step_tabToTab_inv h
  rw [hs]
  exact ⟨putRun_keep.2.1, putRun_keep.2.2.1, putRun_keep.2.2.2⟩

/-- The play lift of the step table.  PORTED from
`Orig/Phase.lean:497` (the §1a `mono_run` engine over §1f's
`cycleCount_step` — the frozen induction retires here). -/
theorem run_cycleCount_le : ∀ {play : List Move} {x w : State},
    x.run play = some w → cycleCount w ≤ cycleCount x :=
  mono_run cycleCount (fun _ _ _ hst => cycleCount_step hst)

/-- A play that spends a waste card strictly drops the cycle count.
PORTED from `Orig/Phase.lean:515` (the §1f strict rows carry the
waste arms). -/
theorem run_cycleCount_lt : ∀ {play : List Move} {x w : State},
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
          | wasteToFound c =>
              have := cycleCount_step_wasteToFound hm
              omega
          | wasteToTab c b =>
              have := cycleCount_step_wasteToTab hm
              omega
          | tabToFound c => simp [isWasteMove] at hmv
          | foundToTab c b => simp [isWasteMove] at hmv
          | tabToTab c b => simp [isWasteMove] at hmv
        have hle := run_cycleCount_le hrs
        omega
      · obtain ⟨m', hm', hmis⟩ := hmem
        rcases List.mem_cons.1 hm' with heq | hmem2
        · exact absurd (heq ▸ hmis) hmv
        · have hlt := ih hrs ⟨m', hmem2, hmis⟩
          have hle := cycleCount_step hm
          omega

/-- **The pristine-step invariant.**  In a `wasteTo*`-free play at a
positive draw step, a state with a nonempty waste is never followed
by one with an empty waste.  PORTED from `Orig/Phase.lean:559`
(the §1d footprint's waste-length component carries the draw arm —
the frozen append-nonempty row retires here). -/
theorem step_wasteNe_preserved {x y : State} (hd : 0 < x.drawStep)
    {m : Move} (hgood : isWasteMove m ≠ true) (hs : State.step x m = some y)
    (hw : x.waste ≠ []) : y.waste ≠ [] ∧ y.drawStep = x.drawStep := by
  have hw1 : 1 ≤ x.waste.length := by
    obtain ⟨w0, ws, hcon⟩ := list_cons_of_ne_nil hw
    rw [hcon, List.length_cons]
    omega
  cases m with
  | draw =>
      have hsuc : x.stepDraw = some y := hs
      obtain ⟨-, -, -, -, -, hW⟩ := draw_footprint hsuc
      refine ⟨?_, draw_drawStep hsuc⟩
      by_cases hst : x.stock = []
      · rw [recycle_nil x hst hw] at hW
        have hW2 : y.waste.length = min x.drawStep x.waste.reverse.length
            + ([] : List Card).length := hW
        rw [List.length_reverse, List.length_nil] at hW2
        intro hc0
        rw [hc0] at hW2
        simp only [List.length_nil] at hW2
        omega
      · rw [recycle_keep x hst] at hW
        intro hc0
        rw [hc0] at hW
        simp only [List.length_nil] at hW
        omega
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
theorem run_wasteNe (st : State) : ∀ {play : List Move} {x w : State},
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
from `Orig/Phase.lean:645` (the §1d footprint's waste-length
component). -/
theorem draw_pristine_s1 {st s₁ : State} (hd : 0 < st.drawStep)
    (hs : st.stock ≠ []) (hw : st.waste = []) (hsuc : st.stepDraw = some s₁) :
    s₁.waste ≠ [] ∧ s₁.drawStep = st.drawStep := by
  obtain ⟨-, -, -, -, -, hW⟩ := draw_footprint hsuc
  rw [recycle_keep st hs, hw, List.length_nil] at hW
  refine ⟨?_, draw_drawStep hsuc⟩
  have hs1 : 1 ≤ st.stock.length := by
    obtain ⟨c, t, hcon⟩ := list_cons_of_ne_nil hs
    rw [hcon, List.length_cons]
    omega
  intro hc0
  rw [hc0] at hW
  simp only [List.length_nil] at hW
  omega

/-- **Draws at pristine positions deny the witness.**  A draw made
with stock cards present and an *empty* waste: the committed
successor receives dealt cards in its waste, no `wasteTo*`-free
play ever empties a nonempty waste, and a returning play cannot
contain `wasteTo*` moves (they would strictly drop the cycle count,
which the draw conserves).  RE-STATED at the carrier grade from
`Orig/Phase.lean:853` (`draw_irreversible_pristine`, commit
grade there); every internal row is the §1i port above. -/
theorem draw_notW_of_pristine {st : State}
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

/-! ### §1j. The phase-offset denial, SCALARIZED

`Orig.Phase`'s offset argument carried the pair
`(cycleCount, D)` through a lexicographic order theory
(`lexDesc`, `lexDescStrict`, and the five rows of their engine).
The same argument reads as ONE scalar, `phaseMeasure`: the cycle
count quadratic in front, the draw distance in the units column.
A drop in the cycle count covers any rise in the distance, since
`D` never exceeds the cycle count and the quadratic gap
`(c - c') * (c + c' + 1)` dwarfs `D`'s whole range; an equal cycle
count compares the distance directly.  One measure, the standard
`mono_run` engine, the usual denial shape via `not_W_of_desc`.
The pair machinery retires with this card (its frozen cites:
`Orig/Phase.lean:904/:909/:912/:916/:928/:939/:976/:1024/:1038`).

The load-bearing facts, each in plain words: `D` is the
draw-distance potential against the phase line; draws never raise
it (the two trap rows plus the one-whole-deal shift); the
committed offset draw drops it by exactly one whole deal
(`Nat.add_div_right` is that statement).
-/

/-- The draw-distance potential against the in-phase attractor: `0`
on phase-aligned positions, otherwise the number of whole deals
left before the stock drains (in ceiling form).  PORTED verbatim
from `Orig/Phase.lean:971`. -/
def D (st : State) : Nat :=
  if (inPhase st) = true then 0 else (st.stock.length + st.drawStep - 1) / st.drawStep

/-- One successful draw from a nonempty stock, as four bookkeeping
facts.  PORTED from `Orig/Phase.lean:981` (a §1d footprint
projection through `recycle_keep`; the frozen proof re-derived the
dealUpTo arithmetic). -/
theorem draw_facts {x y : State} (hsuc : x.stepDraw = some y)
    (hne : x.stock ≠ []) :
    cycleCount y = cycleCount x ∧ y.drawStep = x.drawStep ∧
      y.stock.length + min x.drawStep x.stock.length = x.stock.length ∧
      y.waste.length = min x.drawStep x.stock.length + x.waste.length := by
  obtain ⟨hD, -, -, hC, hS, hW⟩ := draw_footprint hsuc
  rw [recycle_keep x hne] at hS hW
  exact ⟨hC, hD, hS, hW⟩

/-- `D` only reads the stock, the waste, and the draw step.  PORTED
verbatim from `Orig/Phase.lean:1000`. -/
theorem D_congr {x y : State} (h1 : x.stock = y.stock)
    (h2 : x.waste = y.waste) (h3 : x.drawStep = y.drawStep) : D x = D y := by
  show (if (inPhase x) = true then 0 else
          (x.stock.length + x.drawStep - 1) / x.drawStep) =
       (if (inPhase y) = true then 0 else
          (y.stock.length + y.drawStep - 1) / y.drawStep)
  rw [inPhase_congr h1 h2 h3, h1, h3]

/-- `D` vanishes on phase-aligned positions.  PORTED verbatim from
`Orig/Phase.lean:1009`. -/
theorem D_of_inPhase_true {x : State} (h : inPhase x = true) : D x = 0 := by
  show (if (inPhase x) = true then 0 else _) = 0
  rw [h]
  rfl

/-- `D` opens to its ceiling form on off-line positions.  PORTED
verbatim from `Orig/Phase.lean:1015`. -/
theorem D_of_inPhase_false {x : State} (h : inPhase x = false) :
    D x = (x.stock.length + x.drawStep - 1) / x.drawStep := by
  show (if (inPhase x) = true then 0 else
          (x.stock.length + x.drawStep - 1) / x.drawStep) = _
  rw [h]
  rfl

/-- **The scalar phase measure** — the lexicographic argument
`(cycleCount, D)` linearized into one number: the cycle count
quadratic carries the primary ordering, the draw-distance
potential reads in the units column.  PORTED as the scalar form
of `Orig/Phase.lean:976` (`QPair`) and `:1038` (`step_lexDesc`). -/
def phaseMeasure (st : State) : Nat :=
  cycleCount st * (cycleCount st + 1) + D st

/-- **The potential is bounded by the cycle count** — the fact
that makes the scalarization work: a cycle drop of even one
covers any conceivable rise in `D`.  The bound in words: an
off-line position holds cards, and `(n + d - 1) / d =
((n - 1) + d) / d = (n - 1) / d + 1 <= n` by
`Nat.add_div_right` and `Nat.div_le_self`. -/
theorem D_le_cycleCount (st : State) : D st ≤ cycleCount st := by
  rcases bool_dich (inPhase st) with hin | hin
  · rw [D_of_inPhase_true hin]
    exact Nat.zero_le _
  · by_cases hd : st.drawStep = 0
    · rw [D_of_inPhase_false hin, hd, Nat.div_zero]
      exact Nat.zero_le _
    · have hne : st.stock ≠ [] := by
        intro hc0
        exact absurd (inPhase_eq_true_of_nil hc0) (by rw [hin]; simp)
      obtain ⟨c0, t0, hcon'⟩ := list_cons_of_ne_nil hne
      have hp : 1 ≤ st.stock.length := by rw [hcon', List.length_cons]; omega
      rw [D_of_inPhase_false hin,
        show st.stock.length + st.drawStep - 1
            = (st.stock.length - 1) + st.drawStep from by omega,
        Nat.add_div_right _ (by omega : 0 < st.drawStep)]
      show (st.stock.length - 1) / st.drawStep + 1
          ≤ st.stock.length + st.waste.length
      have hq := Nat.div_le_self (st.stock.length - 1) st.drawStep
      omega

/-- **Draws never raise the phase potential.**  Three readings of
the trap plus the plain shift: a recycle draw lands aligned; an
aligned position stays aligned; and an off-line plain draw
advances the stock by exactly one whole deal, so
`(y + d - 1) / d = (n - 1) / d` against
`D x = (n - 1) / d + 1`.  PORTED as the `D`-half of
`Orig/Phase.lean:1038`'s draw arm. -/
theorem draw_D_le {x y : State} (hsuc : x.stepDraw = some y) : D y ≤ D x := by
  by_cases hstock : x.stock = []
  · have hDy : D y = 0 := D_of_inPhase_true (draw_nil_inPhase hstock hsuc)
    omega
  · obtain ⟨-, hdeq, hslen, hwlen⟩ := draw_facts hsuc hstock
    rcases bool_dich (inPhase x) with hinx | hinx
    · have hDy : D y = 0 := D_of_inPhase_true (draw_keeps_inPhase hsuc hinx)
      have hDx : D x = 0 := D_of_inPhase_true hinx
      omega
    · obtain ⟨-, hres⟩ := inPhase_eq_false_iff.1 hinx
      by_cases hd0 : x.drawStep = 0
      · -- a zero draw step flattens both potentials (division by zero)
        rcases bool_dich (inPhase y) with hiny | hiny
        · rw [D_of_inPhase_true hiny, D_of_inPhase_false hinx, hd0, Nat.div_zero]
          omega
        · have hy0 : y.drawStep = 0 := hdeq.trans hd0
          rw [D_of_inPhase_false hiny, hy0, Nat.div_zero,
            D_of_inPhase_false hinx, hd0, Nat.div_zero]
          omega
      · have hdp : 0 < x.drawStep := by omega
        obtain ⟨cx0, tx0, hconx⟩ := list_cons_of_ne_nil hstock
        have hpx : 1 ≤ x.stock.length := by rw [hconx, List.length_cons]; omega
        by_cases hdr : y.stock = []
        · have hDy : D y = 0 := D_of_inPhase_true (inPhase_eq_true_of_nil hdr)
          omega
        · obtain ⟨c', t', hcon'⟩ := list_cons_of_ne_nil hdr
          have hp' : 1 ≤ y.stock.length := by rw [hcon', List.length_cons]; omega
          have hiny : inPhase y = false := by
            rw [inPhase_eq_decide_of_cons hcon']
            refine decide_eq_false (fun hc0 => ?_)
            have hresy : y.waste.length % x.drawStep = x.waste.length % x.drawStep := by
              have hk : min x.drawStep x.stock.length = x.drawStep := by omega
              rw [show y.waste.length
                    = min x.drawStep x.stock.length + x.waste.length from hwlen,
                hk, Nat.add_mod_left]
            rw [show y.drawStep = x.drawStep from hdeq, hresy] at hc0
            exact hres hc0
          rw [D_of_inPhase_false hiny, D_of_inPhase_false hinx,
            show y.drawStep = x.drawStep from hdeq,
            show y.stock.length + x.drawStep - 1
                = x.stock.length - 1 from by omega,
            show x.stock.length + x.drawStep - 1
                = (x.stock.length - 1) + x.drawStep from by omega,
            Nat.add_div_right _ hdp]
          omega

/-- **The committed offset draw drops the potential by exactly
one whole deal.**  The cycle count rests, and the stock advanced
one whole deal means `(y - 1) / d < (y - 1 + d) / d` literally by
`Nat.add_div_right`.  PORTED as the `D`-half of
`Orig/Phase.lean:1108`'s strict descent. -/
theorem draw_D_lt {st s₁ : State} (hd : 0 < st.drawStep) (hs : st.stock ≠ [])
    (hsuc : st.stepDraw = some s₁) (hoff : st.waste.length % st.drawStep ≠ 0) :
    D s₁ < D st := by
  obtain ⟨-, hdeq, hslen, hwlen⟩ := draw_facts hsuc hs
  obtain ⟨c0, t0, hcon⟩ := list_cons_of_ne_nil hs
  have hp : 1 ≤ st.stock.length := by rw [hcon, List.length_cons]; omega
  have hinF : inPhase st = false := by
    rw [inPhase_eq_decide_of_cons hcon, decide_eq_false hoff]
  have hDst : D st = (st.stock.length - 1) / st.drawStep + 1 := by
    rw [D_of_inPhase_false hinF,
      show st.stock.length + st.drawStep - 1
          = (st.stock.length - 1) + st.drawStep from by omega,
      Nat.add_div_right _ hd]
  by_cases hdr : s₁.stock = []
  · have hD0 : D s₁ = 0 := D_of_inPhase_true (inPhase_eq_true_of_nil hdr)
    rw [hD0, hDst]
    exact Nat.succ_le_succ (Nat.zero_le _)
  · obtain ⟨c', t', hcon'⟩ := list_cons_of_ne_nil hdr
    have hp' : 1 ≤ s₁.stock.length := by rw [hcon', List.length_cons]; omega
    have hiny : inPhase s₁ = false := by
      rw [inPhase_eq_decide_of_cons hcon']
      refine decide_eq_false (fun hc0 => ?_)
      have hresy : s₁.waste.length % st.drawStep
          = st.waste.length % st.drawStep := by
        have hk : min st.drawStep st.stock.length = st.drawStep := by omega
        rw [show s₁.waste.length
              = min st.drawStep st.stock.length + st.waste.length from hwlen,
          hk, Nat.add_mod_left]
      rw [show s₁.drawStep = st.drawStep from hdeq, hresy] at hc0
      exact hoff hc0
    have hDs₁ : D s₁ = (s₁.stock.length - 1) / st.drawStep + 1 := by
      rw [D_of_inPhase_false hiny, show s₁.drawStep = st.drawStep from hdeq,
        show s₁.stock.length + st.drawStep - 1
            = (s₁.stock.length - 1) + st.drawStep from by omega,
        Nat.add_div_right _ hd]
    have hchain : st.stock.length - 1
        = (s₁.stock.length - 1) + st.drawStep := by omega
    rw [hDs₁, hDst]
    calc (s₁.stock.length - 1) / st.drawStep + 1
        < ((s₁.stock.length - 1) + st.drawStep) / st.drawStep + 1 := by
          rw [Nat.add_div_right _ hd]
          omega
      _ = (st.stock.length - 1) / st.drawStep + 1 := by rw [hchain]

/-- `phaseMeasure` respects field-coincidence moves: the board
moves that copy the stock, waste and draw step leave both
coordinates verbatim. -/
theorem phaseMeasure_congr {x y : State}
    (hc : cycleCount x = cycleCount y) (hdd : D x = D y) :
    phaseMeasure x = phaseMeasure y := by
  simp only [phaseMeasure, hc, hdd]

/-- **The quadratic's cover** — the fact that lets the scalar
carry the lexicographic argument: when the cycle count drops at
all, the quadratic gap
`(c - c') * (c + c' + 1) >= 2 * c' + 2`
swallows the phase potential's whole range (which
`D_le_cycleCount` caps at the smaller cycle count).  The identity
behind it: `(a + 1) * (a + 1) = a * (a + 1) + (a + 1)`, one
`Nat.succ_mul`. -/
theorem phaseMeasure_cover {x y : State} (h : cycleCount y + 1 ≤ cycleCount x) :
    cycleCount y * (cycleCount y + 1) + cycleCount y + 1
      ≤ cycleCount x * (cycleCount x + 1) := by
  have hx1 : (cycleCount y + 1) * (cycleCount y + 1)
      ≤ cycleCount x * (cycleCount x + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hx2 : (cycleCount y + 1) * (cycleCount y + 1)
      = cycleCount y * (cycleCount y + 1) + (cycleCount y + 1) := by
    simp [Nat.succ_mul]
  omega

/-- **The per-move phase-measure table.**  Every legal move
descends the scalar phase measure: the board moves by
`phaseMeasure_congr`, the waste moves through the quadratic's
cover plus the potential bound, the draw through the conserved
cycle count plus `draw_D_le`.  PORTED as the scalar form of
`Orig/Phase.lean:1038` (`step_lexDesc`). -/
theorem step_phaseMeasure_le : ∀ {x y : State} {m : Move},
    State.step x m = some y → phaseMeasure y ≤ phaseMeasure x := by
  intro x y m hs
  cases m with
  | draw =>
      have hced : cycleCount y = cycleCount x := draw_cycleCount hs
      have hdd := draw_D_le hs
      simp only [phaseMeasure, hced]
      omega
  | wasteToFound c =>
      have hlt := cycleCount_step_wasteToFound hs
      have hmy := D_le_cycleCount y
      have hcover := phaseMeasure_cover (by omega)
      simp only [phaseMeasure]
      omega
  | wasteToTab c b =>
      have hlt := cycleCount_step_wasteToTab hs
      have hmy := D_le_cycleCount y
      have hcover := phaseMeasure_cover (by omega)
      simp only [phaseMeasure]
      omega
  | tabToFound c =>
      obtain ⟨h1, h2, h3⟩ := tabToFound_fixed hs
      exact Nat.le_of_eq
        (phaseMeasure_congr (cycleCount_eq_of_stock_waste h1 h2) (D_congr h1 h2 h3))
  | foundToTab c b =>
      obtain ⟨h1, h2, h3⟩ := foundToTab_fixed hs
      exact Nat.le_of_eq
        (phaseMeasure_congr (cycleCount_eq_of_stock_waste h1 h2) (D_congr h1 h2 h3))
  | tabToTab c b =>
      obtain ⟨h1, h2, h3⟩ := tabToTab_fixed hs
      exact Nat.le_of_eq
        (phaseMeasure_congr (cycleCount_eq_of_stock_waste h1 h2) (D_congr h1 h2 h3))

/-- **Draws at offset positions deny the witness.**  At a position
with cards still in the stock whose waste sits strictly inside a
deal (and a positive draw step): the committed draw conserves the
cycle count and drops the phase potential by exactly one whole
deal, and no legal play ascends the scalar phase measure.
RE-STATED at the carrier grade from `Orig/Phase.lean:1108`
(`draw_irreversible_offset_lex`, commit grade there); the
argument now rides the standard denial tool. -/
theorem draw_notW_of_offset {st : State}
    (hd : 0 < st.drawStep) (hs : st.stock ≠ [])
    (hoff : st.waste.length % st.drawStep ≠ 0) :
    ¬ reversibleAtW st Move.draw := by
  intro hw
  obtain ⟨s₁, -, hsuc, -⟩ := id hw
  have hced : cycleCount s₁ = cycleCount st := draw_cycleCount hsuc
  have hdd := draw_D_lt hd hs hsuc hoff
  exact absurd hw (not_W_of_desc phaseMeasure
    (fun _ _ _ hst => step_phaseMeasure_le hst) hsuc
    (by simp only [phaseMeasure, hced]; omega))

/-! ### §1k. The draw round trips

The constructive half of the draw letter: the pass-end full
redeal, the drain/redeal position banks, and the three round trips
the oracle's `true` cells hand (selfRecycle, pass base via the
pure-draw drain, and the in-phase two-leg rotation).
-/

/-! The additive drop split and the take-drop recombination ride Lean
core (`List.drop_drop`, `List.take_append_drop`); the frozen
originals this kit ported verbatim are `Orig/Phase.lean:1232`,
`:1251`, `:1266`, `:1290`, `:1313`, `:1325`.  DE-CHOICE NOTE:
core's `List.take_add` depends on `Classical.choice`, so the
additive take split stays a private constructive row below (the
card's de-choice discipline). -/

/-- The additive take split, CONSTRUCTIVE (core's `List.take_add` is
choice-bearing).  PORTED verbatim from `Orig/Phase.lean:1207`. -/
theorem take_drop_add {α : Type} : ∀ (i j : Nat) (l : List α),
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

/-- Taking past (or exactly to) the end of a list takes the whole
list.  PORTED from `Orig/Phase.lean:1266` (core re-provenance). -/
theorem take_ge_length {α : Type} : ∀ (l : List α) (n : Nat),
    l.length ≤ n → l.take n = l := by
  intro l n h
  have hd : l.drop n = [] := List.drop_of_length_le h
  have h2 := List.take_append_drop n l
  rw [hd, List.append_nil] at h2
  exact h2

/-- Dropping past (or exactly to) the end of a list drops it to
nothing.  PORTED from `Orig/Phase.lean:1290` (core re-provenance:
`List.drop_of_length_le`). -/
theorem drop_ge_length {α : Type} : ∀ (l : List α) (n : Nat),
    l.length ≤ n → l.drop n = [] := fun _ _ h => List.drop_of_length_le h

/-- The prefix clip on an appended list: dropping past a known
prefix returns the suffix.  PORTED from `Orig/Phase.lean:1313`
(core re-provenance: `List.drop_drop`-style rowing). -/
theorem drop_append_prefix {α : Type} : ∀ (A B : List α),
    (A ++ B).drop A.length = B := by
  intro A B
  rw [List.drop_append, List.drop_length, Nat.sub_self, List.drop_zero,
    List.nil_append]

/-- The prefix clip on an appended list, take side.  PORTED from
`Orig/Phase.lean:1325` (core re-provenance). -/
theorem take_append_prefix {α : Type} : ∀ (A B : List α),
    (A ++ B).take A.length = A := by
  intro A B
  rw [List.take_append_of_le_length (Nat.le_refl _)]
  exact take_ge_length A A.length (Nat.le_refl _)

/-- One draw followed by the rest of the play.  PORTED verbatim
from `Orig/Phase.lean:1353`. -/
theorem run_draw_cons {x y : State} {rest : List Move}
    (hstep : State.step x Move.draw = some y) :
    x.run (Move.draw :: rest) = y.run rest := by
  show (match State.step x Move.draw with
      | some st' => State.run st' rest
      | none => none) = State.run y rest
  rw [hstep]

/-- Append-glue for pure-draw plays.  PORTED verbatim from
`Orig/Phase.lean:1363`. -/
theorem run_replicate_append :
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
theorem plain_draw_shape {x : State} (hne : x.stock ≠ []) :
    x.stepDraw = some
      { x with stock := x.stock.drop x.drawStep, waste := (x.stock.take x.drawStep).reverse ++ x.waste } := by
  rw [State.stepDraw, show State.recycle x = x from recycle_keep x hne,
    dealStock_eq_of_ne_nil x hne, dealUpTo_eq_take_drop]

/-- One pass-end draw (the stock is empty and the waste nonempty,
so the recycle fires).  PORTED verbatim from
`Orig/Phase.lean:1184`. -/
theorem base_draw_shape {x : State} (hstock : x.stock = ([] : List Card))
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
theorem draw_full_shape (x : State) (hne : x.stock ≠ [])
    (hx : x.stock.length < x.drawStep) :
    State.step x Move.draw = some
      (State.mk x.found x.piles ([] : List Card) (x.stock.reverse ++ x.waste) x.drawStep) := by
  have ge := Nat.le_of_lt hx
  rw [show State.step x Move.draw = x.stepDraw from rfl, plain_draw_shape hne,
    drop_ge_length x.stock x.drawStep ge, take_ge_length x.stock x.drawStep ge]

/-- The pass-end full-redeal, as a computed step.  PORTED verbatim
from `Orig/Phase.lean:775`. -/
theorem selfRecycle_draw {st : State} (hstock : st.stock = [])
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
theorem drain_positions_one :
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
      rw [List.drop_drop, hidx]
      have hmerge : (List.take (q * x.drawStep) (List.drop x.drawStep l)).reverse
            ++ ((List.take x.drawStep l).reverse ++ x.waste)
          = (l.take (x.drawStep + q * x.drawStep)).reverse ++ x.waste := by
        rw [take_drop_add, List.reverse_append, List.append_assoc]
      rw [hmerge, hidx]

/-- **The redeal positions.**  From a pass base, `k + 1`
consecutive draws move exactly `(k + 1) * drawStep` cards of the
recycled pool back onto the waste, list-exact.  PORTED verbatim
from `Orig/Phase.lean:1451`. -/
theorem base_positions_one :
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
  rw [List.drop_drop, hidx]
  have hmerge : (List.take (k * x.drawStep)
          (List.drop x.drawStep x.waste.reverse)).reverse
        ++ ((List.take x.drawStep x.waste.reverse).reverse ++ ([] : List Card))
      = ((List.take (x.drawStep + k * x.drawStep) x.waste.reverse).reverse
          ++ ([] : List Card)) := by
    rw [take_drop_add, List.reverse_append, List.append_assoc]
  rw [hmerge, hidx]

/-- The run-composition shape.  PORTED verbatim from
`Orig/Classify.lean:1124`. -/
theorem run_cons_shape {s : State} {m : Move} {rest : List Move} {s' w : State}
    (hstep : State.step s m = some s') (hrun : s'.run rest = some w) :
    s.run (m :: rest) = some w := by
  simp only [State.run, hstep]
  exact hrun

/-- The pure-draw drain: from any stock-bearing position, some
pure-draw play drains the stock to the pass base, ending with the
whole recycle-reversed stock re-dealt onto the waste.  PORTED
verbatim from `Orig/Classify.lean:1133`. -/
theorem drain_to_pass : ∀ (n : Nat) (l : List Card) (s : State), l.length ≤ n →
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
              List.take_append_drop]
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
theorem draw_passBase_reversibleW {st : State}
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
        List.take_append_drop, List.reverse_reverse]
    refine congrArg some (State.ext rfl rfl hstock.symm hwE rfl)

/-- **The pass-base redeal finish** — the two first-leg branches'
shared closing, extracted: once the rotation reaches the pass base
`State.mk st.found st.piles [] (st.stock.reverse ++ st.waste)
st.drawStep`, the redeal leg rides `base_positions_one` and the
recycled pool splits back into `st` exactly.  FOLD-PORT of the two
duplicated redeal legs of `Orig/Phase.lean:1513`'s two-branch
rotation. -/
theorem inphase_redeal_finish {st : State} {jk : Nat} (hd : 0 < st.drawStep)
    (hjd2 : (jk + 1) * st.drawStep = st.waste.length)
    (hwB : (st.stock.reverse ++ st.waste) ≠ [])
    (hsizeB : (jk + 1) * st.drawStep ≤ (st.stock.reverse ++ st.waste).length) :
    (State.mk st.found st.piles ([] : List Card) (st.stock.reverse ++ st.waste) st.drawStep).run
      (List.replicate (jk + 1) Move.draw) = some st := by
  have hb := base_positions_one jk
    (State.mk st.found st.piles ([] : List Card) (st.stock.reverse ++ st.waste) st.drawStep)
    rfl hwB hd hsizeB
  rw [hb]
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

/-- **The in-phase round trip, witness grade.**  At a
phase-aligned position with a positive draw step, cards left in
the stock, and a nonempty whole number of deals in the waste, the
draw is undone by an explicit pure-draw play: drain the committed
stock to the pass base, then redeal exactly the waste's whole
number of deals from the recycled pool.  PORTED verbatim from
`Orig/Phase.lean:1513` (`draw_reversible_inphaseW`; the frozen
statement concludes the frozen twin of the carrier — the same
body, this card's carrier constant). -/
theorem draw_inphase_reversibleW {st : State} (hd : 0 < st.drawStep)
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
          congrArg List.reverse (List.take_append_drop st.drawStep st.stock).symm,
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
    exact inphase_redeal_finish hd hjd2 hwB hsizeB
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
            congrArg List.reverse (List.take_append_drop st.drawStep st.stock).symm,
        List.reverse_append,
        show (st.stock.drop st.drawStep).reverse
            = ((st.stock.drop st.drawStep).take
                (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep)
              ++ (st.stock.drop st.drawStep).drop
                (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep)).reverse from
            congrArg List.reverse
              (List.take_append_drop
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
    exact inphase_redeal_finish hd hjd2 hwB hsizeB


/-! ## The audit battery

Per promoted head, this kit.  Expected profile: `[propext]` or
`[propext, Quot.sound]` — never `sorryAx`, never `Classical.choice`. -/

#print axioms run_rec
#print axioms mono_run
#print axioms step_phaseMeasure_le
#print axioms draw_D_le
#print axioms not_W_of_desc
#print axioms not_W_of_step_none
#print axioms reversible_mirrorW
#print axioms cycleCount_step
#print axioms hiddenTotal_step
#print axioms draw_footprint
#print axioms draw_nil_inPhase
#print axioms draw_keeps_inPhase
#print axioms selfRecycle_draw
#print axioms inphase_redeal_finish
#print axioms draw_passBase_reversibleW
#print axioms draw_notW_of_pristine
#print axioms draw_notW_of_offset
