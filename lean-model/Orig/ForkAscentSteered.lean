import Orig.ForkAscent
import Orig.ForkStateSB
import Orig.LowSlab
import Orig.FoundKit

/-!
# Orig.ForkAscentSteered — THE RANK-FIRST STEERED ASCENT (forks as
fixed points of the deterministic scheduler)

THE OWNER-DIRECTED REFORMALIZATION (2026-10-17, session 9, branch
macro-game): the seventh-succession census read the every-run
exhaustion head honestly — its frozen conclusion is undeliverable at
every hypothesis-satisfying world (`ascent_exhaust_shape_impossible`),
so the head is vacuity-or-false as frozen.  This leaf formalizes the
replacement the design conversation converged on, in three layers:

* **THE STEERED ALPHABET** (which letters):  the raise arm carries the
  owner's TWIN GATE — `raiseGate st c := CanRaise st c ∧
  (CanRaiseS st c.twin → CanRaise st c.twin)` — raising c is refused
  exactly when the twin still has a raise FUTURE (the {slide · raise}
  cascade, `CanRaiseS`) yet is not raisable NOW; this is precisely the
  covered-S-live twin of the forkState terminal, and the gate halts
  the trajectory on it.  Joint pairs (the twin fires now) and dead
  pairs (the twin has no raise future) remain consumable — the race
  they carry is not the delivered fork's shape.  The seat arm is the
  slide-side twin: reversible slides only, with a mobile pair member
  seatable only while the pair is JOINT NOW (cargo cards — founded,
  stocked, buried, or otherwise unpaired — slide freely; the raw
  alphabet's unconditional slide arm was the fa3 channel's route).
* **THE RANK-FIRST SCHEDULER** (which letter): the trajectory's head is
  rank-minimal among steered-legal letters (`SteeredFirst`): always
  serve the smallest rank.  The rank ties land exactly on twin pairs
  (twins share rank), where the steer already speaks; the universe
  tie-break is the priced refinement R3 below.  Under determinism the
  old head's every-run quantifier collapses, and the fa0 multi-pair
  and twin-contention branch pathologies become fixed-point properties.
* **THE FROZEN CANDIDATE** (the theorem): from a state below a
  reachable fork's frontier with the pair deployed face-up, every
  steered trajectory run to steered-stuck exhausts AT a `forkState`
  (the S-grade detection of `Orig.MacroInternal`: the pair-saturation
  iff at the {slide · raise} grade plus the vanilla refusal of the
  covered twin).  The manifested fork is then one licensed leg away
  through the banked β-companion machinery (`ExhaustShapeRec`,
  `ascent_cover_pullback`, `ascent_rec_base_of_iff` — all PROVED in
  `Orig/ForkAscent.lean`, users of this leaf's conclusion).

RESIDUES this statement owns (each priced; the hbelow premise is the
old head's verbatim — the formalization's error was never there):

* R1 LOYALTY AND PARKING: the reachable fork's witness path must be
  compatible with the steered trajectory, and the rank-first schedule
  must park the family frontiers at the pair's rank on its own order
  (the climb content restated; the order-forcing is the new leverage,
  the witness-path gap is the old content).  [H]
* R2 THE TERMINAL CENSUS: a forkState carries no steered letter at all
  — raises self-refuse there (the gate), pair-member seats self-refuse
  (the joint clause), and what remains is the third-card cargo census
  (the fa2-class evidence suggests it closes; the fa3 channel's seating
  legs are steered-illegal).  [H-mini, decide-gradable]
* R3 THE TIE-BREAK AND THE BOOL BRIDGE: the within-rank universe
  tie-break row, and the decidable face of `CanRaiseS` the stepper
  needs (consume ForkStateS's flat `canRaiseS_iff`; the fa-board probe
  re-verdicts ride it).  [M]

PROBE-FIRST PROTOCOL before freeze-consumption: re-verdict fa2 (a
forkState-shaped terminal standing as a legal steered-stuck world),
fa3 (the resurrection needs a steered-forbidden leg), fa0 (multi-pair
under the rank spine), fcS/fcH (the twin-contention splits die under
the scheduler) — each a decide row over the banked boards once R3's
bridge lands.

SUCCESSION NOTE (the owner's retirement plan): this leaf is the
designated successor of `Orig/ForkAscent.lean` — the migration cargo
(the vocabulary columns the ceiling consumes, the toolkit rows, the
β-companion, the fence boards) moves here bucket by bucket, the
ForklessCeiling import rewire rides the same pass, and only then does
the old leaf RETIRE by its own commit (the working tree's in-flight
arc is banked first; the old head's four sorries retire WITH the file,
their verdicts truespeaked into CHALLENGES — vacuity-or-false, the
ceiling squeeze, and the census records).

House compliance: additive leaf (`Orig.ForkAscent` only — everything
else transitive); no mathlib; zero `Classical.choice`; frozen
byte-stable candidate with a complete route; `#print axioms` battery
per fresh head; no other file touched this pass; no git commits from
this leaf. -/

/-! ## §0. The steered alphabet -/

/-- The letter's rank — the moved card's rank index.  Non-letter
moves carry the sentinel (they are never SteeredLetter-legal, so the
sentinel never orders the spine). -/
def letterRank (m : Move) : Nat :=
  match m with
  | .tabToFound c => c.rank.toIdx
  | .tabToTab c _ => c.rank.toIdx
  | _ => 99

/-- **THE RAISE GATE** (the owner's twin gate): c fires now, and
whenever the twin still has a raise future in the {slide · raise}
cascade, the twin is raisable NOW outright — so the gate refuses
exactly the covered-S-live twin, the forkState terminal's own shape. -/
def raiseGate (st : State) (c : Card) : Prop :=
  CanRaise st c ∧ (CanRaiseS st c.twin → CanRaise st c.twin)

/-- **THE SEAT GATE**: the slide fires, is reversible (the same
class of slides the twin's cascade futures ride), and a mobile pair
member seats only while the pair is JOINT NOW — cargo cards seat
freely. -/
def seatGate (st : State) (c : Card) (b : Base) : Prop :=
  State.step st (Move.tabToTab c b) ≠ none ∧
    reversibleAtW st (Move.tabToTab c b) ∧
    (MobileTwin st c → CanRaise st c ∧ CanRaise st c.twin)

/-- **THE STEERED LETTERS**: the two arms of the steered alphabet —
everything else is not a letter. -/
def SteeredLetter (st : State) (m : Move) : Prop :=
  match m with
  | .tabToFound c => raiseGate st c
  | .tabToTab c b => seatGate st c b
  | _ => False

/-! ## §1. The three instance rows (the gate's verdict table,
zero-sorry, each one line off the defs) -/

/-- THE REFUSAL INSTANCE: a hot card whose twin is S-live but
vanilla-blocked is never raise-gated — the terminal's own raise
halts the trajectory there. -/
theorem raiseGate_refuses_coveredS {st : State} {c : Card}
    (hs : CanRaiseS st c.twin) (hn : ¬ CanRaise st c.twin) :
    ¬ raiseGate st c := by
  rintro ⟨-, himp⟩
  exact hn (himp hs)

/-- THE JOINT INSTANCE: a pair whose members both fire now passes the
gate — the pair is not the delivered shape, and the race it carries
resolves on the schedule's own order. -/
theorem raiseGate_joint {st : State} {c : Card}
    (h1 : CanRaise st c) (h2 : CanRaise st c.twin) :
    raiseGate st c :=
  ⟨h1, fun _ => h2⟩

/-- THE DEAD INSTANCE: a hot card whose twin has no raise future at
all passes the gate — nothing to protect. -/
theorem raiseGate_dead {st : State} {c : Card}
    (h1 : CanRaise st c) (hn : ¬ CanRaiseS st c.twin) :
    raiseGate st c := by
  refine ⟨h1, fun hs => ?_⟩
  exact absurd hs hn

/-- THE SEAT REFUSAL INSTANCE: a mobile pair member that is not
joint-now is never seated. -/
theorem seatGate_refuses_nonjoint {st : State} {c : Card} {b : Base}
    (hmob : MobileTwin st c)
    (hn : ¬ (CanRaise st c ∧ CanRaise st c.twin)) :
    ¬ seatGate st c b := by
  rintro ⟨-, -, himp⟩
  exact hn (himp hmob)

/-! ## §2. The rank-first spine and the trajectory -/

/-- **THE RANK-FIRST SPINE**: a lawful head is rank-minimal among all
steered-legal letters — always serve the smallest rank first.  The
within-rank universe tie-break is the priced refinement R3. -/
def SteeredFirst (st : State) (m : Move) : Prop :=
  ∀ m', SteeredLetter st m' → letterRank m' ≥ letterRank m

/-- **THE STEERED TRAJECTORY**: a finite sequence of steered letters,
each head rank-minimal at its own state. -/
inductive SteeredRun : State → List Move → State → Prop
  | nil (st : State) : SteeredRun st [] st
  | cons {st s' W : State} {m : Move} {ρ : List Move}
      (hletter : SteeredLetter st m)
      (hfirst : SteeredFirst st m)
      (hstep : State.step st m = some s')
      (hrest : SteeredRun s' ρ W) :
      SteeredRun st (m :: ρ) W

/-- **THE STEERED-STUCK READ**: the trajectory's only end — no
steered letter fires at all. -/
def SteeredStuck (st : State) : Prop :=
  ∀ m, SteeredLetter st m → State.step st m = none

/-! ## §2b. The terminal's raise plug — R2's landed half

At a saturation-packaged world — the pair exactly S-live, the
twin vanilla-blocked, the very `forkState` shape the candidate
claims as its exhaustion — NO raise letter is steered-legal:

* the WITNESS is refused by the twin gate's own implication (its
  twin is S-live through the iff yet vanilla-blocked — the gate is
  precisely this refusal, `raiseGate_refuses_coveredS` generalized
  off the concrete board);
* the TWIN and every THIRD CARD are refused for want of a vanilla
  raise (the iff kills their S-liveness, and `CanRaiseS.now` is the
  inclusion).

This is the halt mechanism: the gate stops the trajectory AT the
forkState shape, as designed.  The seat-side census (whether any
third-card cargo seat still fires at the terminal) is R2's priced
remainder — the fa2-class decide content.

PROBE COROLLARY (the §14.5 expectation, corrected by the design
itself): the fa2-class worlds — delivered DOUBLE-HOT pair, both
members vanilla-live — are NOT steered-stuck terminals but the
trajectory's MID-STATES: the twin gate deliberately permits joint
raises, so the trajectory consumes the benign pair and climbs on.
The steered re-verdict of fa2 therefore reads "fa2 admits a legal
steered raise" (both deuce raises pass the joint gate, the rank tie
resolved by R3's tie-break), and the plug above applies at the
covered-twin aftermath — at the forkState shape itself, one cover
slide past the joint world. -/
theorem raisePlug_of_saturated {st : State} {x : Card}
    (hiff : ∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS st c)
    (hxt : ¬ CanRaise st x.twin) :
    ∀ c, ¬ raiseGate st c := by
  intro c hgate
  by_cases hc1 : c = x
  · subst hc1
    exact hxt (hgate.2 ((hiff _).1 (Or.inr rfl)))
  · by_cases hc2 : c = x.twin
    · subst hc2
      exact hxt hgate.1
    · have hpair : ¬ (c = x ∨ c = x.twin) := fun h => h.elim hc1 hc2
      exact hpair ((hiff c).2 (CanRaiseS.now c hgate.1))

/-- **THE PLUG AT THE DETECTION GRADE**: at any `forkState`, no raise
letter is steered-legal — the raise side of the steered-stuck
terminal, assembled from the detection's own two conjuncts. -/
theorem raisePlug_forkState {st : State} (hf : forkState st) :
    ∀ c, ¬ raiseGate st c := by
  obtain ⟨x, hiff, hxt⟩ := hf
  exact raisePlug_of_saturated hiff hxt

/-- **THE LETTER-GRADE PLUG**: at a `forkState`, no `tabToFound`
letter is steered — the plug restated at the alphabet's grain for
the terminal census's consumers. -/
theorem no_raiseLetter_of_forkState {st : State} (hf : forkState st)
    (c : Card) : ¬ SteeredLetter st (Move.tabToFound c) :=
  raisePlug_forkState hf c

/-! ## §2c. The steered run geometry — the spine's order-content and
the reveal kill

THE R1 LOYALTY MEMO'S ORDER-CONTENT HALF, landed: the two letter
arms' rung geometry (a raise steps exactly its own suit by one; a
slide freezes every rung), the monotone lift along the trajectory,
the spine's two service rows (rank-minimality as a lemma, and the
COVER-PREEMPTION BAR — a steered cover letter at rank −1 bars the
member raise at rank, the leverage that pays the dead no-eat
guard's debt at the parking zone), and the seat arm's REVEAL KILL
— the `fa3` channel's general bar: the seat gate's `reversibleAtW`
clause is fed by the banked journey-never-reveal monotone, so a
seating leg that would expose a hidden head is never a steered
letter at all.

The three cited copies of banked geometry rows follow the house
dedup discipline (each cites its `Orig.ForkAscent` original, there
`private` — the originals retire with that leaf and these copies
are the migration's cargo at steered statement grain).  The
loyalty ledger carries forward: the persistence hybrid over the
explicit `hnoeat` premise lands next off these rows; the frontier
parking equalities and the witness-path census remain R1's priced
loyalty content (the memo's P7/P8). -/

/-- The rung read and the foundation-height read are the same
function (the cited copy of `Orig.ForkAscent.ascent_rung_height`). -/
private theorem steered_rung_height (w : State) (σ : Suit) :
    rungAt w σ = w.foundHeight σ := rfl

/-- A cargo leg's landing never touches the foundations (the cited
copy of `Orig.ForkAscent.ascent_putRun_foundHeight`). -/
private theorem steered_putRun_foundHeight (w : State) (run : List Card)
    (b : Base) (σ : Suit) :
    (w.putRun run b).foundHeight σ = w.foundHeight σ := by
  cases b with
  | inl a => rfl
  | inr z =>
      show (match w.pileOfTop z with
             | some k => w.setPile k { w.piles k with faceUp := (w.piles k).faceUp ++ run }
             | none => w).foundHeight σ = w.foundHeight σ
      cases hpz : w.pileOfTop z with
      | some k => rfl
      | none => rfl

/-- **THE RUNG STEP, RAISE ARM** (P0): a fired founding raises its
own suit's rung by exactly one and leaves every other suit's in
place. -/
theorem steered_rung_raise {st s' : State} {c : Card}
    (hstep : State.step st (Move.tabToFound c) = some s') :
    rungAt s' c.suit = rungAt st c.suit + 1 ∧
      ∀ σ : Suit, σ ≠ c.suit → rungAt s' σ = rungAt st σ := by
  obtain ⟨hn, a₀, hpo₀, hspl⟩ := step_tabToFound_inv hstep
  have hself : s'.found c.suit = st.found c.suit ++ [c] := by
    rw [hspl]
    exact setFound_found_self
  have hne : ∀ σ : Suit, σ ≠ c.suit → s'.found σ = st.found σ := by
    intro σ hσ
    rw [hspl]
    exact setFound_found_ne hσ
  refine ⟨?_, ?_⟩
  · show (s'.found c.suit).length = (st.found c.suit).length + 1
    rw [hself, List.length_append]
    simp
  · intro σ hσ
    show (s'.found σ).length = (st.found σ).length
    rw [hne σ hσ]

/-- **THE RUNG FREEZE, SLIDE ARM** (P1): a fired slide leaves every
suit's rung exactly where it stood (the steered twin of
`Orig.ForkAscent.ascent_slide_rung`). -/
theorem steered_rung_slide {st s' : State} {c : Card} {b : Base}
    (hstep : State.step st (Move.tabToTab c b) = some s') (σ : Suit) :
    rungAt s' σ = rungAt st σ := by
  obtain ⟨a, -, -, -, hspl⟩ := step_tabToTab_inv hstep
  rw [hspl, steered_rung_height _ σ, steered_putRun_foundHeight,
    steered_rung_height st σ]
  rfl

/-- **THE RUNG MONOTONE LIFT** (P2): along any steered trajectory,
no suit's rung ever drops. -/
theorem steered_rung_mono {s : State} {ρ : List Move} {W : State}
    (hrun : SteeredRun s ρ W) (σ : Suit) :
    rungAt s σ ≤ rungAt W σ := by
  induction hrun with
  | nil st => exact Nat.le_refl _
  | @cons st s' W m ρ hletter hfirst hstep hrest ih =>
      have hle : rungAt st σ ≤ rungAt s' σ := by
        cases m with
        | tabToFound c =>
            have h := steered_rung_raise hstep
            by_cases hc : c.suit = σ
            · rw [hc] at h
              have h1 := h.1
              omega
            · exact Nat.le_of_eq (h.2 σ (fun hq => hc hq.symm)).symm
        | tabToTab c b => exact Nat.le_of_eq (steered_rung_slide hstep σ).symm
        | draw => exact absurd hletter (fun hl => hl)
        | wasteToFound c => exact absurd hletter (fun hl => hl)
        | wasteToTab c b => exact absurd hletter (fun hl => hl)
        | foundToTab c b => exact absurd hletter (fun hl => hl)
      omega

/-- **THE SERVICE MINIMALITY** (P3a): the spine's own definition, as
a lemma — a steered head ranks at or below every steered-legal
letter at that state. -/
theorem steered_service_minimal {st : State} {m : Move}
    (hf : SteeredFirst st m) {m' : Move}
    (hl : SteeredLetter st m') :
    letterRank m ≤ letterRank m' := by
  have h := hf m' hl
  omega

/-- **THE COVER-PREEMPTION BAR** (P3b): while a fitting cover's
seat letter stands steered-legal at the state, the member raise is
NOT servable — the cover ranks one below the pair and the spine
must serve it first (the row-form of the parking zone's halt
leverage). -/
theorem steered_preempt_cover {st : State} {x d : Card} {b : Base}
    (hdh : d.rank.toIdx + 1 = x.rank.toIdx)
    (hcov : SteeredLetter st (Move.tabToTab d b))
    (hf : SteeredFirst st (Move.tabToFound x)) : False := by
  have h := hf _ hcov
  have h1 : letterRank (Move.tabToTab d b) = d.rank.toIdx := rfl
  have h2 : letterRank (Move.tabToFound x) = x.rank.toIdx := rfl
  rw [h1, h2] at h
  omega

/-- **THE SEAT ARM'S REVEAL KILL** (W2, the `fa3` channel's general
bar): a seating leg that would expose a hidden head — the whole
run leaves the pile over a nonempty hidden deck — is never a
steered letter: the seat gate's `reversibleAtW` clause collides
with the banked journey-never-reveal monotone. -/
theorem steered_seat_refuses_reveal {st s' : State} {c : Card} {b : Base}
    {a : Anchor}
    (hstep : State.step st (Move.tabToTab c b) = some s')
    (hh : st.pileHolding c = some a)
    (hbel : below c (st.piles a).faceUp = [])
    (hhne : (st.piles a).hidden ≠ []) :
    ¬ SteeredLetter st (Move.tabToTab c b) := by
  intro hl
  exact journey_tabToTab_never_reveal hstep hh hbel hhne hl.2.1

/-! ## §3. The frozen candidate (statement byte-stable; route
complete; the successor family's head) -/

/-- **THE STEERED ASCENT FORKS** — the reformalized exhaustion row:
from a state below a reachable fork's frontier (the old head's
premise, verbatim: a fork is reachable, both pair suits sit at or
below the frontier at the start, and the pair is deployed face-up),
every steered trajectory run to steered-stuck exhausts AT a
`forkState` — the S-grade detection: the pair saturates the
{slide · raise} liveness, and the covered twin refuses vanilla.  The
manifested fork is then one licensed leg away through the banked
β-companion (never re-derived here).

ROUTE (the three named pieces; the premise is untouched, so the old
program's climb machinery is restated, not replaced):

1. R1 THE ORDERED CLIMB — the rank-first spine parks the family
   frontiers at the pair's rank by its own order: every smaller rank
   is served before the pair's turn arrives, so the parking content
   the old `ascent_climb_delivery` carried becomes order-forced; the
   remaining content is the witness-path loyalty — the reachable
   fork's exhibiting play must be compatible with the steered leg
   set at the parking zone.  [H, the route's real load]
2. R2 THE TERMINAL CENSUS — at the steered-stuck point the S-set is
   exactly the pair (the exhaustion analysis): the gates self-block
   the pair's own letters, and the third-card cargo census is the
   fa2-class decide content (the old saturation axes, repriced: the
   fa1 member-liveness half is steered-forced by construction, the
   fa3 resurrection channel's seating legs are steered-illegal).
   [H-mini, decide-gradable]
3. R3 THE ASSEMBLY — the two pieces compose into the `forkState`
   conjunctions directly (the iff's membership half from R2's census,
   the vanilla twin-refusal from the terminal's covered shape); the
   exhaustion-shape ceiling does not bite here — this terminal's
   cover is the licensed aftermath's first leg, not a standing
   conjunct of the stuck world.

REFUTED 2026-10-17 (§6 carries the certified fence): the loA
counterexample — hbelow holds via a five-leg RAW play manifesting
the fork, while the steered spine eats the pair at its own rank and
drains SteeredStuck to a certified non-forkState.  This row keeps
its sorry as the honest witness (the fa2/ascent_cover_cell
precedent); `steered_ascent_forks_refuted` beside it is the wall.
The successor statements are the consumption/starvation dichotomy —
see §6's header. -/
theorem steered_ascent_forks {s : State} (hwf : s.WF)
    (hbelow : ∃ (F : State) (x : Card) (π : List Move),
      s.run π = some F ∧ ForkWitness F x ∧
        rungAt s x.suit ≤ x.rank.toIdx ∧
        rungAt s x.twin.suit ≤ x.rank.toIdx ∧
        (∃ (a : Anchor), x ∈ (s.piles a).faceUp) ∧
        (∃ (b : Anchor), x.twin ∈ (s.piles b).faceUp))
    {ρ : List Move} {W : State}
    (hrun : SteeredRun s ρ W)
    (hstuck : SteeredStuck W) :
    forkState W := by
  sorry

/-! ## The audit battery

`#print axioms` per fresh head: the four gate instance rows, the
three plug rows, and the six §2c geometry/spine rows are zero-sorry
(the geometry pair ride cited copies of banked `Orig.ForkAscent`
rows); the frozen candidate carries exactly one `sorry` — the priced
R1/R2 content recorded in its route; zero `Classical.choice` (every
case split rides a decidable read or the letter match); the leaf is
additive and touches no other file this pass. -/

#print axioms raiseGate_refuses_coveredS
#print axioms raiseGate_joint
#print axioms raiseGate_dead
#print axioms seatGate_refuses_nonjoint
#print axioms raisePlug_of_saturated
#print axioms raisePlug_forkState
#print axioms no_raiseLetter_of_forkState
#print axioms steered_rung_raise
#print axioms steered_rung_slide
#print axioms steered_rung_mono
#print axioms steered_service_minimal
#print axioms steered_preempt_cover
#print axioms steered_seat_refuses_reveal
#print axioms steered_ascent_forks
/-! ## §4. THE R3 DECIDABLE BRIDGE — promoted (2026-10-17, the probe
battery greenlit)

Promoted verbatim from the certified scratch draft
(`Temp/fas_bridge_draft.lean`, exit 0, 8 heads) per its own protocol:
"the rows that promote into the successor leaf when the probe battery
greenlights them" — the fa2/fa3/fa0 re-verdicts landed green the same
pass.  The banked-Bool census: `canRaiseSB` + `canRaiseSB_true_iff`
(Orig/ForkStateSB) is the flat characterization consumed AS-IS (the
WF premise is the banked row's own, never stronger); the raise face
is COMPLETE (`steerRaiseB_true_iff`); the seat face is the partial
letter `fires ∧ joint-now`, its Prop remainder priced as R3w — the
`reversibleAtW` Bool — with the stuck-side row turning the remainder
into a certified irreversibility detector (`steeredPick_stuck`).
-/

/-! ## §0. The private kit -/

/-- The first hit is found in the list (the membership half the
banked `firstWhere_sound` leaves implicit). -/
private theorem firstWhere_found_mem {α : Type} (p : α → Bool) :
    ∀ {l : List α} {x : α}, firstWhere p l = some x → x ∈ l := by
  intro l
  induction l with
  | nil => intro x h; simp [firstWhere] at h
  | cons y t ih =>
      intro x h
      rw [firstWhere] at h
      split at h
      · injection h with hxy
        exact List.mem_cons.2 (Or.inl hxy.symm)
      · exact List.mem_cons.2 (Or.inr (ih h))

/-- The none side's completeness: no hit means everything is false
(the search-completeness twin of the banked `firstWhere_find`). -/
private theorem firstWhere_none_complete {α : Type} (p : α → Bool) :
    ∀ {l : List α}, firstWhere p l = none →
      ∀ x ∈ l, p x = false := by
  intro l
  induction l with
  | nil => intro _ x hx; cases hx
  | cons y t ih =>
      intro h x hx
      rw [firstWhere] at h
      split at h
      · exact absurd h (by simp)
      · rename_i hp
        rcases List.mem_cons.1 hx with rfl | hxt
        · exact hp
        · exact ih h x hxt

/-- The option dichotomy, on a VARIABLE (any tactic splitting on the
rank-scan term itself would whnf the whole 13-rank chain at symbolic
states — the timeout lesson of this draft; vars are safe). -/
private theorem option_cases {α : Type} (o : Option α) :
    (∃ v, o = some v) ∨ o = none := by
  cases o with
  | none => exact Or.inr rfl
  | some v => exact Or.inl ⟨v, rfl⟩

/-- A firing step is not `none`, read off the `isSome` face. -/
private theorem step_isSome_ne_none {st : State} {m : Move}
    (h : (State.step st m).isSome = true) : State.step st m ≠ none := by
  cases hstep : State.step st m with
  | none => rw [hstep] at h; exact absurd h (by simp)
  | some v => intro hcon; exact absurd hcon (by simp)

/-- The anchor-membership half of the mobility read, as a fold over
the (finite) anchor enumeration. -/
private def anchorExB (st : State) (c : Card) : Bool :=
  Anchor.all.any (fun a => decide (c ∈ (st.piles a).faceUp))

private theorem anchorExB_true_iff (st : State) (c : Card) :
    anchorExB st c = true ↔ ∃ (a : Anchor), c ∈ (st.piles a).faceUp := by
  constructor
  · intro h
    rw [anchorExB] at h
    obtain ⟨a, _, hdec⟩ := (List.any_eq_true).1 h
    exact ⟨a, of_decide_eq_true hdec⟩
  · rintro ⟨a, hmem⟩
    rw [anchorExB, List.any_eq_true]
    exact ⟨a, Anchor.mem_all a, decide_eq_true hmem⟩

/-- The per-file `MobileTwin` decider (the banked `mobileTwinB` of
`Orig/ForkAscent.lean:1293` is private to that file; this is the
house per-file copy of the same fold — four decidable conjuncts). -/
private def mobileTwinB (st : State) (c : Card) : Bool :=
  (anchorExB st c && decide (c.rank.toIdx ≥ st.foundHeight c.suit)) &&
  (anchorExB st c.twin &&
    decide (c.twin.rank.toIdx ≥ st.foundHeight c.twin.suit))

private theorem mobileTwinB_iff (st : State) (c : Card) :
    mobileTwinB st c = true ↔ MobileTwin st c := by
  constructor
  · intro h
    rw [mobileTwinB, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rw [Bool.and_eq_true] at h1
    rw [Bool.and_eq_true] at h2
    exact ⟨(anchorExB_true_iff st c).1 h1.1, of_decide_eq_true h1.2,
           (anchorExB_true_iff st c.twin).1 h2.1,
           of_decide_eq_true h2.2⟩
  · rintro ⟨hm, hr, hmt, hrt⟩
    rw [mobileTwinB, Bool.and_eq_true]
    refine ⟨?_, ?_⟩ <;> rw [Bool.and_eq_true]
    · exact ⟨(anchorExB_true_iff st c).2 hm, decide_eq_true hr⟩
    · exact ⟨(anchorExB_true_iff st c.twin).2 hmt, decide_eq_true hrt⟩

/-- The seat arm's joint clause, as a Bool (the MobileTwin → both
vanilla-licensable read; no `WF` needed — pure `canRaiseB` +
`mobileTwinB` bridges). -/
private def seatJointB (st : State) (c : Card) : Bool :=
  (!mobileTwinB st c) || (canRaiseB st c && canRaiseB st c.twin)

private theorem seatJointB_true_iff (st : State) (c : Card) :
    seatJointB st c = true ↔
      (MobileTwin st c → CanRaise st c ∧ CanRaise st c.twin) := by
  constructor
  · intro h
    rw [seatJointB, Bool.or_eq_true] at h
    rcases h with hnt | hboth
    · have hmt : mobileTwinB st c = false := by
        cases hmt : mobileTwinB st c with
        | true => rw [hmt] at hnt; exact absurd hnt (by simp)
        | false => rfl
      intro hmob
      exact absurd ((mobileTwinB_iff st c).2 hmob)
        (by rw [hmt]; simp)
    · rw [Bool.and_eq_true] at hboth
      intro _
      exact ⟨(canRaiseB_true_iff).1 hboth.1,
             (canRaiseB_true_iff).1 hboth.2⟩
  · intro himpj
    rw [seatJointB]
    cases hmt : mobileTwinB st c with
    | false => rfl
    | true =>
        obtain ⟨h1, h2⟩ := himpj ((mobileTwinB_iff st c).1 hmt)
        have hb1 : canRaiseB st c = true := (canRaiseB_true_iff).2 h1
        have hb2 : canRaiseB st c.twin = true :=
          (canRaiseB_true_iff).2 h2
        rw [hb1, hb2]; rfl

/-! ## §1. The S-face at the twin gate (`canRaiseSB` consumed) -/

/-- **THE RAISE FACE** — the twin gate as a `Bool`: the vanilla probe
`canRaiseB`, and the gate leg (the twin's S-probe read at its false
side, or the twin's vanilla probe at its true side). -/
def steerRaiseB (st : State) (c : Card) : Bool :=
  canRaiseB st c && ((!canRaiseSB st c.twin) || canRaiseB st c.twin)

/-- The raise face's bridge, at the S-probe's own `WF` grade: the
Bool is exactly `raiseGate` (`Orig/ForkAscentSteered.lean:100`). -/
theorem steerRaiseB_true_iff {st : State} (hwf : st.WF) {c : Card} :
    steerRaiseB st c = true ↔ raiseGate st c := by
  constructor
  · intro h
    rw [steerRaiseB, Bool.and_eq_true] at h
    obtain ⟨hB, hgate⟩ := h
    refine ⟨(canRaiseB_true_iff).1 hB, ?_⟩
    intro hS
    have hSB : canRaiseSB st c.twin = true :=
      (canRaiseSB_true_iff hwf).2 hS
    rw [hSB] at hgate; simp at hgate
    exact (canRaiseB_true_iff).1 hgate
  · rintro ⟨hcr, himp⟩
    have hB : canRaiseB st c = true := (canRaiseB_true_iff).2 hcr
    rw [steerRaiseB, hB, Bool.true_and]
    cases hSB : canRaiseSB st c.twin with
    | false => rfl
    | true =>
        have htr : CanRaise st c.twin :=
          himp ((canRaiseSB_true_iff hwf).1 hSB)
        have hb2 : canRaiseB st c.twin = true :=
          (canRaiseB_true_iff).2 htr
        rw [hb2]; rfl

/-! ## §2. The letter face -/

/-- **THE SEAT FACE** (partial, honestly so): the firing check plus
the joint clause.  The reversibility conjunct of `seatGate`
(`reversibleAtW`) is the ONE PROP REMAINDER — priced at §6, never
faked here. -/
def steerSeatB (st : State) (c : Card) (b : Base) : Bool :=
  (State.step st (Move.tabToTab c b)).isSome && seatJointB st c

/-- The seat face's bridge (NO `WF` — every component is an
unconditional `canRaiseB`/folds bridge): exactly `seatGate` minus the
reversibility conjunct. -/
theorem steerSeatB_true_iff (st : State) (c : Card) (b : Base) :
    steerSeatB st c b = true ↔
      State.step st (Move.tabToTab c b) ≠ none ∧
        (MobileTwin st c → CanRaise st c ∧ CanRaise st c.twin) := by
  rw [steerSeatB, Bool.and_eq_true]
  constructor
  · rintro ⟨hfire, hjoint⟩
    exact ⟨step_isSome_ne_none hfire,
           (seatJointB_true_iff st c).1 hjoint⟩
  · rintro ⟨hfire, hjoint⟩
    have his : (State.step st (Move.tabToTab c b)).isSome = true := by
      cases hstep : State.step st (Move.tabToTab c b) with
      | none => rw [hstep] at hfire; exact absurd rfl hfire
      | some v => rfl
    exact ⟨his, (seatJointB_true_iff st c).2 hjoint⟩

/-- **THE LETTER FACE** — the full `Bool` mirror of `SteeredLetter`'s
two arms (the sentinel moves are `false`, exactly the Prop side's
`False` arm). -/
def SteeredLetterB (st : State) (m : Move) : Bool :=
  match m with
  | .tabToFound c => steerRaiseB st c
  | .tabToTab c b => steerSeatB st c b
  | _ => false

/-- The raise arm is complete: the face IS the gate at the S-probe's
`WF` grade. -/
theorem SteeredLetterB_raise_true_iff {st : State} (hwf : st.WF)
    {c : Card} :
    SteeredLetterB st (Move.tabToFound c) = true ↔ raiseGate st c :=
  steerRaiseB_true_iff hwf

/-- The seat arm is the partial letter: exactly the fires-plus-joint
half of `seatGate`; the reversibility conjunct is §6's residue. -/
theorem SteeredLetterB_seat_partial_true_iff {st : State} {c : Card}
    {b : Base} :
    SteeredLetterB st (Move.tabToTab c b) = true ↔
      State.step st (Move.tabToTab c b) ≠ none ∧
        (MobileTwin st c → CanRaise st c ∧ CanRaise st c.twin) :=
  steerSeatB_true_iff st c b

/-! ## §3. The ordered enumeration (rank-major, raises before slides) -/

/-- Every base a slide can name: the anchors in order, then every
card (the `inr` cover seats) in universe order. -/
def baseUniverse : List Base :=
  Anchor.all.map Sum.inl ++ Card.universe.map Sum.inr

theorem baseUniverse_mem_inl (a : Anchor) : Sum.inl a ∈ baseUniverse := by
  rw [baseUniverse, List.mem_append]
  exact Or.inl (List.mem_map.2 ⟨a, Anchor.mem_all a, rfl⟩)

theorem baseUniverse_mem_inr (z : Card) : Sum.inr z ∈ baseUniverse := by
  rw [baseUniverse, List.mem_append]
  exact Or.inr (List.mem_map.2 ⟨z, Card.mem_universe z, rfl⟩)

/-- The cards of one rank, in universe order (a fresh match-based
filter; the private kit rows below are its membership calculus). -/
def cardsAtRank : Nat → List Card → List Card
  | _, [] => []
  | r, c :: t =>
      match decide (c.rank.toIdx = r) with
      | true => c :: cardsAtRank r t
      | false => cardsAtRank r t

private theorem cardsAtRank_mem {r : Nat} :
    ∀ {l : List Card} {c : Card}, c ∈ l → c.rank.toIdx = r →
      c ∈ cardsAtRank r l := by
  intro l
  induction l with
  | nil => intro c hc; cases hc
  | cons x t ih =>
      intro c hc hr
      have hct : c ∈ t ∨ c = x := by
        rcases List.mem_cons.1 hc with heq | hm
        · exact Or.inr heq
        · exact Or.inl hm
      rw [cardsAtRank]
      split
      · rename_i hxdec
        rcases hct with hmem | hcx
        · exact List.mem_cons.2 (Or.inr (ih hmem hr))
        · exact List.mem_cons.2 (Or.inl hcx)
      · rename_i hxdec
        rcases hct with hmem | hcx
        · exact ih hmem hr
        · have hxr : x.rank.toIdx = r := by rw [← hcx]; exact hr
          rw [decide_eq_true hxr] at hxdec
          exact absurd hxdec (by simp)

private theorem cardsAtRank_rank {r : Nat} :
    ∀ {l : List Card} {c : Card}, c ∈ cardsAtRank r l →
      c.rank.toIdx = r := by
  intro l
  induction l with
  | nil => intro c hc; cases hc
  | cons x t ih =>
      intro c hc
      rw [cardsAtRank] at hc
      split at hc
      · rename_i hxdec
        rcases List.mem_cons.1 hc with rfl | hm
        · exact of_decide_eq_true hxdec
        · exact ih hm
      · exact ih hc

/-- The seat column: for each card of the list, every base in
`baseUniverse` order. -/
def seatMovesAt : List Card → List Move
  | [] => []
  | c :: t =>
      baseUniverse.map (fun b => Move.tabToTab c b) ++ seatMovesAt t

private theorem seatMovesAt_mem {c : Card} {b : Base} :
    ∀ {l : List Card}, c ∈ l → b ∈ baseUniverse →
      Move.tabToTab c b ∈ seatMovesAt l := by
  intro l
  induction l with
  | nil => intro hc; cases hc
  | cons x t ih =>
      intro hc hb
      rw [seatMovesAt]
      rcases List.mem_cons.1 hc with hcx | hct
      · rw [hcx]
        exact List.mem_append.2 (Or.inl (List.mem_map.2 ⟨b, hb, rfl⟩))
      · exact List.mem_append.2 (Or.inr (ih hct hb))

private theorem seatMovesAt_shape {m : Move} :
    ∀ {l : List Card}, m ∈ seatMovesAt l →
      ∃ (c : Card) (b : Base), c ∈ l ∧ b ∈ baseUniverse ∧
        m = Move.tabToTab c b := by
  intro l
  induction l with
  | nil => intro hm; cases hm
  | cons x t ih =>
      intro hm
      rw [seatMovesAt] at hm
      rcases List.mem_append.1 hm with hmap | hrest
      · obtain ⟨b, hbm, rfl⟩ := List.mem_map.1 hmap
        exact ⟨x, b, List.mem_cons.2 (Or.inl rfl), hbm, rfl⟩
      · obtain ⟨c, b, hcm, hbm, rfl⟩ := ih hrest
        exact ⟨c, b, List.mem_cons.2 (Or.inr hcm), hbm, rfl⟩

/-- The rank's letters, raises before slides: the raise column, then
the seat column — universe order within each. -/
def steeredRankBlock (r : Nat) : List Move :=
  (cardsAtRank r Card.universe).map (Move.tabToFound) ++
    seatMovesAt (cardsAtRank r Card.universe)

theorem raiseBlock_mem {c : Card} {r : Nat} (hr : c.rank.toIdx = r) :
    Move.tabToFound c ∈ steeredRankBlock r := by
  have hc : c ∈ cardsAtRank r Card.universe :=
    cardsAtRank_mem (Card.mem_universe c) hr
  rw [steeredRankBlock]
  exact List.mem_append.2
    (Or.inl (List.mem_map.2 ⟨c, hc, rfl⟩))

theorem seatBlock_mem {c : Card} {b : Base} {r : Nat}
    (hr : c.rank.toIdx = r) (hb : b ∈ baseUniverse) :
    Move.tabToTab c b ∈ steeredRankBlock r := by
  have hc : c ∈ cardsAtRank r Card.universe :=
    cardsAtRank_mem (Card.mem_universe c) hr
  rw [steeredRankBlock]
  exact List.mem_append.2 (Or.inr (seatMovesAt_mem hc hb))

private theorem block_letters {r : Nat} {m : Move}
    (hm : m ∈ steeredRankBlock r) :
    (∃ (d : Card), m = Move.tabToFound d ∧ d.rank.toIdx = r) ∨
    (∃ (d : Card) (b : Base), m = Move.tabToTab d b ∧ d.rank.toIdx = r) := by
  rw [steeredRankBlock] at hm
  rcases List.mem_append.1 hm with hraise | hseat
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hraise
    exact Or.inl ⟨c, rfl, cardsAtRank_rank hc⟩
  · obtain ⟨c, b, hcm, hbm, rfl⟩ := seatMovesAt_shape hseat
    exact Or.inr ⟨c, b, rfl, cardsAtRank_rank hcm⟩

private theorem block_letterRank {r : Nat} {m : Move}
    (hm : m ∈ steeredRankBlock r) : letterRank m = r := by
  rcases block_letters hm with ⟨c, rfl, hr⟩ | ⟨c, b, rfl, hr⟩
  · show c.rank.toIdx = r; exact hr
  · show c.rank.toIdx = r; exact hr

/-! ## §4. The stepper (rank-major `firstWhere`, lowest rank first) -/

/-- One rank's pick: the first Bool-true letter of the block (raises
before slides by list order; universe order within — the Prop spine's
within-arm tie-break is R3's named refinement). -/
def rankPick (st : State) (r : Nat) : Option Move :=
  firstWhere (SteeredLetterB st) (steeredRankBlock r)

private theorem rankPick_none_all_false {st : State} {r : Nat}
    (h : rankPick st r = none) :
    ∀ (m : Move), m ∈ steeredRankBlock r →
      SteeredLetterB st m = false := by
  rw [rankPick] at h
  exact firstWhere_none_complete _ h

/-- The scan's tail: an inner carry prefers to a fresh rank. -/
def takeRank (st : State) (k : Nat) (o : Option (Nat × Move)) :
    Option (Nat × Move) :=
  match o with
  | some p => some p
  | none =>
      match rankPick st k with
      | some m => some (k, m)
      | none => none

private theorem takeRank_some_inner {st : State} {k : Nat}
    {p : Nat × Move} : takeRank st k (some p) = some p := rfl

private theorem takeRank_none_none {st : State} {k : Nat}
    (h : rankPick st k = none) : takeRank st k none = none := by
  rw [takeRank, h]

private theorem takeRank_none_rank {st : State} {k : Nat} {m : Move}
    (h : rankPick st k = some m) :
    takeRank st k none = some (k, m) := by
  rw [takeRank, h]

/-- The rank scan: ranks `0, 1, 2, …` ascending (rank-major —
`satStep`'s universe-order precedent, keyed by rank first); the first
rank whose block yields a letter wins. -/
def firstRankUpTo (st : State) : Nat → Option (Nat × Move)
  | 0 => none
  | k+1 => takeRank st k (firstRankUpTo st k)

private theorem firstRankUpTo_none_complete {st : State} :
    ∀ {k : Nat}, firstRankUpTo st k = none →
      ∀ (r : Nat), r < k → rankPick st r = none := by
  intro k
  induction k with
  | zero => intro h r hr; exact absurd hr (by omega)
  | succ k ih =>
      intro h r hr
      rw [firstRankUpTo] at h
      cases hinner : firstRankUpTo st k with
      | none =>
          rw [hinner] at h
          by_cases hrk : r = k
          · rw [hrk]
            rcases option_cases (rankPick st k) with ⟨m, hp⟩ | hp
            · rw [takeRank_none_rank hp] at h
              exact absurd h (by simp)
            · exact hp
          · exact ih hinner r (by omega)
      | some p =>
          rw [hinner] at h
          rw [takeRank_some_inner] at h
          exact absurd h (by simp)

private theorem firstRankUpTo_shape {st : State} :
    ∀ {k : Nat} {r : Nat} {m : Move},
      firstRankUpTo st k = some (r, m) →
      r < k ∧ SteeredLetterB st m = true ∧
      m ∈ steeredRankBlock r ∧
      ∀ (r' : Nat), r' < r → rankPick st r' = none := by
  intro k
  induction k with
  | zero => intro r m h; rw [firstRankUpTo] at h;
            exact absurd h (by simp)
  | succ k ih =>
      intro r m h
      rw [firstRankUpTo] at h
      cases hinner : firstRankUpTo st k with
      | none =>
          rw [hinner] at h
          cases hp : rankPick st k with
          | none =>
              rw [takeRank_none_none hp] at h
              exact absurd h (by simp)
          | some m₀ =>
              rw [takeRank_none_rank hp] at h
              rw [rankPick] at hp
              injection h with hpair
              obtain ⟨hkr, hmr⟩ := Prod.mk.inj hpair
              subst hkr; subst hmr
              refine ⟨by omega, firstWhere_sound
                  (p := SteeredLetterB st)
                  (l := steeredRankBlock k) hp,
                firstWhere_found_mem _ hp, ?_⟩
              intro r' hr'
              exact firstRankUpTo_none_complete hinner r' hr'
      | some p =>
          rw [hinner] at h
          rw [takeRank_some_inner] at h
          injection h with hpair
          subst hpair
          obtain ⟨h1, h2, h3, h4⟩ := ih hinner
          exact ⟨by omega, h2, h3, h4⟩

/-- The tail projection (arg-matched, so its equations are structural
and no proof ever needs the rank-scan term evaluated — the same shape
discipline as `takeRank` above). -/
private def takeMove (o : Option (Nat × Move)) : Option Move :=
  match o with
  | some p => some p.2
  | none => none

private theorem takeMove_some {p : Nat × Move} :
    takeMove (some p) = some p.2 := rfl

private theorem takeMove_none : takeMove none = none := rfl

/-- **THE DETERMINISTIC STEPPER** — the lowest rank that owns a
Bool-true letter, that letter being the block's own first (raises
before slides, universe order within). -/
def steeredPick (st : State) : Option Move :=
  takeMove (firstRankUpTo st 13)

private theorem steeredPick_some_of_eq {st : State} {r : Nat} {m : Move}
    (h : firstRankUpTo st 13 = some (r, m)) :
    steeredPick st = some m := by
  rw [steeredPick, h, takeMove_some]

private theorem steeredPick_none_of_eq {st : State}
    (h : firstRankUpTo st 13 = none) : steeredPick st = none := by
  rw [steeredPick, h, takeMove_none]

private theorem steeredPick_extract {st : State} {m : Move}
    (h : steeredPick st = some m) :
    ∃ (r : Nat) (m' : Move),
      firstRankUpTo st 13 = some (r, m') ∧ m' = m := by
  rcases option_cases (firstRankUpTo st 13) with ⟨p, hFR⟩ | hFR
  · obtain ⟨r₀, m₀⟩ := p
    rw [steeredPick_some_of_eq hFR] at h
    injection h with hm
    exact ⟨r₀, m₀, hFR, hm⟩
  · rw [steeredPick_none_of_eq hFR] at h
    exact absurd h (by simp)

/-! ## §5. The four consumption rows -/

/-- (a, raise soundness, complete) — a returned raise letter IS the
twin gate, at the S-probe's `WF` grade (the raise arm's face has no
remainder). -/
theorem steeredPick_sound_raise {st : State} (hwf : st.WF) {c : Card}
    (h : steeredPick st = some (Move.tabToFound c)) :
    raiseGate st c := by
  obtain ⟨r, m, hFR, hm⟩ := steeredPick_extract h
  subst hm
  obtain ⟨-, hB, -, -⟩ := firstRankUpTo_shape hFR
  exact (SteeredLetterB_raise_true_iff hwf).1 hB

/-- (a, seat soundness, partial) — a returned seat letter fires and
obeys the joint clause; the reversibility conjunct of `seatGate` is
§6's priced residue (never claimed here). -/
theorem steeredPick_sound_seat {st : State} {c : Card} {b : Base}
    (h : steeredPick st = some (Move.tabToTab c b)) :
    State.step st (Move.tabToTab c b) ≠ none ∧
      (MobileTwin st c → CanRaise st c ∧ CanRaise st c.twin) := by
  obtain ⟨r, m, hFR, hm⟩ := steeredPick_extract h
  subst hm
  obtain ⟨-, hB, -, -⟩ := firstRankUpTo_shape hFR
  exact (steerSeatB_true_iff st c b).1 hB

/-- (a, rank-minimality, the face-complete half) — no gated raise
lives below the returned letter's rank.  The seat-competitor half of
`SteeredFirst` rides §6's residue: it closes the moment the seat
face's reversibility conjunct does. -/
theorem steeredPick_rank_raise {st : State} (hwf : st.WF) {m : Move}
    (h : steeredPick st = some m) {c : Card} (hgate : raiseGate st c) :
    c.rank.toIdx ≥ letterRank m := by
  obtain ⟨r, m, hFR, hm⟩ := steeredPick_extract h
  subst hm
  obtain ⟨-, -, hmem, hskip⟩ := firstRankUpTo_shape hFR
  have hlr : letterRank m = r := block_letterRank hmem
  rw [hlr]
  by_cases hlt : c.rank.toIdx < r
  · exfalso
    have hBtrue : SteeredLetterB st (Move.tabToFound c) = true :=
      (steerRaiseB_true_iff hwf).2 hgate
    have hmem2 : Move.tabToFound c ∈ steeredRankBlock c.rank.toIdx :=
      raiseBlock_mem rfl
    have hnone : rankPick st c.rank.toIdx = none :=
      hskip c.rank.toIdx hlt
    have hfalse := rankPick_none_all_false hnone _ hmem2
    rw [hfalse] at hBtrue
    exact absurd hBtrue (by simp)
  · omega

/-- (b, stuck certifies irreversibility) — at a `SteeredStuck` world
the picker returns no raise at all (the gate would fire against the
stuckness, `raise_eq_some_of_canRaise`); and any seat letter it
returns is CERTIFIED NOT REVERSIBLE — its witnessing leg is exactly
what the stuckness forbids.  The residue read backwards: §6's Bool,
once it lands, upgrades the seat return into a contradiction too,
closing `steeredPick st = none` outright. -/
theorem steeredPick_stuck {st : State} (hwf : st.WF)
    (hstuck : SteeredStuck st) {m : Move}
    (h : steeredPick st = some m) :
    ∃ (c : Card) (b : Base), m = Move.tabToTab c b ∧
      ¬ reversibleAtW st m := by
  obtain ⟨r, m', hFR, hm⟩ := steeredPick_extract h
  subst hm
  obtain ⟨-, hB, hmem, -⟩ := firstRankUpTo_shape hFR
  rcases block_letters hmem with ⟨c, rfl, -⟩ | ⟨c, b, rfl, -⟩
  · exfalso
    have hgate : raiseGate st c :=
      (SteeredLetterB_raise_true_iff hwf).1 hB
    have hletter : SteeredLetter st (Move.tabToFound c) := hgate
    have hnone : State.step st (Move.tabToFound c) = none :=
      hstuck _ hletter
    obtain ⟨s', hs'⟩ := raise_eq_some_of_canRaise st hgate.1
    have hsome : State.step st (Move.tabToFound c) = some s' := hs'
    rw [hsome] at hnone
    exact absurd hnone (by simp)
  · refine ⟨c, b, rfl, ?_⟩
    obtain ⟨hfire, hjoint⟩ := (steerSeatB_true_iff st c b).1 hB
    intro hrev
    have hseat : SteeredLetter st (Move.tabToTab c b) :=
      ⟨hfire, hrev, hjoint⟩
    have hnone2 : State.step st (Move.tabToTab c b) = none :=
      hstuck _ hseat
    rw [hnone2] at hfire
    exact absurd rfl hfire

/-! ## §6. The residue ledger, the battery, the spot checks

**R3w (priced [M-mini], NOT drafted — the one Prop remainder).**
The seat arm's second conjunct, `reversibleAtW st (Move.tabToTab c b)`
(`Orig/Fate.lean:92`), is existential over an UNBOUNDED play, so it
has no cheap `Bool` as stated.  ROUTE for the closing row (`steerRevB`
+ its iff, closing the seat face to the full `seatGate`):

* (sufficiency, constructive) for a slide whose landing run is intact,
  the symmetric return leg is the witness — the shape check is two
  `pileOfTop`/`below` reads (the inr-base landing: the run still
  heads the landing pile, the departure pile's chop accepts the
  run back); the leg is phrased as a one-move `tabToTab` return, so
  the witness play has length ONE — decidable by enumeration over
  the six moves, no search over plays;
* (necessity) at WF ride `reversibleAtW_iff_reversible`
  (`Orig/Classify.lean:3211`, the banked coincidence) plus the
  phase-classification dichotomy (the effective split the
  classification rows land): the irreversible shapes are read off
  the measure tables (`Orig/Irreversible.lean`), each a finite check.
  The Bool is then the shape read; both iff directions close at the
  cost of that row and the seat arms of §5 upgrade: full
  `seatGate` soundness, the seat-competitor half of rank-minimality,
  and `steeredPick st = none` at every stuck WF world.

The probe yard implications: once the fence boards migrate (the
roster's bucket C) the fa0/fa3 re-verdicts ride `SteeredLetterB` +
`steeredPick` directly — decide rows over the banked boards. -/

#print axioms steerRaiseB_true_iff
#print axioms steerSeatB_true_iff
#print axioms SteeredLetterB_raise_true_iff
#print axioms SteeredLetterB_seat_partial_true_iff
#print axioms steeredPick_sound_raise
#print axioms steeredPick_sound_seat
#print axioms steeredPick_rank_raise
#print axioms steeredPick_stuck

#eval baseUniverse.length
#eval (steeredRankBlock 0).length
#eval (steeredRankBlock 12).length

/- APPEND-MARKER -/
/-! ## §5. THE PERSISTENCE WAVE — promoted (2026-10-17)

Promoted verbatim from the certified scratch (exit 0, golden grades)
per the bridge protocol; the promotion's one designed rewire applied:
the kit's sp_rung_height STRUCK, all uses consuming the leaf's own §2c
steered_rung_height copy.  The wave's four rows: steered_pair_persists
(P4 — the persistent pair over the explicit no-eat premise),
steered_persist_mobile (P4prime), steered_cell_armor (P5), and
steered_climb_of_parked (P6 — the delivery as PURE ASSEMBLY off the
persistent clauses plus the two parking equalities).  The cited-kit
copies carry the house dedup notes — the originals retire with
Orig.ForkAscent.lean and these are the migration's cargo;
ascent_selfland_refuted was verified public and consumed as-is.
-/

/-! ## §0. The per-file kit (cited copies) -/

/-- The anchored top-search resolves a card that tops one named pile
and no other (the cited copy of `Orig.ForkAscent.ascent_topSearch`,
there private — cargo at steered grain). -/
private theorem steered_topSearch (st : State) {zm : Card} {hb : Anchor}
    (htopb : (st.piles hb).top = some zm)
    (hbar : ∀ y ∈ Anchor.all, y ≠ hb → (st.piles y).top ≠ some zm) :
    st.pileOfTop zm = some hb := by
  show firstWhere (fun a₂ => decide (st.topOf a₂ = some zm)) Anchor.all = some hb
  refine firstWhere_find (Anchor.mem_all hb) ?_ ?_
  · show decide ((st.piles hb).top = some zm) = true
    rw [htopb]
    exact decide_eq_true rfl
  · intro y hy hyne
    show decide ((st.piles y).top = some zm) = false
    exact decide_false_of_not (hbar y hy hyne)

/-- The last of an appended nonempty suffix is the suffix's last (the
cited copy of `Orig.ForkAscent.ascent_lastOf_append`). -/
private theorem steered_lastOf_append : ∀ (l m : List Card), m ≠ [] →
    lastOf (l ++ m) = lastOf m := by
  intro l
  induction l with
  | nil => intro m _; rfl
  | cons u t ih =>
      intro m hm
      cases m with
      | nil => exact absurd rfl hm
      | cons w ws =>
          cases t with
          | nil => rfl
          | cons v s => exact ih (w :: ws) hm

/-- The emptied pile's flip at a revealing hidden deck (cited copy of
`Orig/ForkAscent.ascent_afterRunRemoved_reveal`). -/
private theorem steered_afterRunRemoved_reveal {p : Pile} {z : Card}
    {t : List Card} (h : p.hidden = z :: t) :
    Pile.afterRunRemoved p [] = ⟨t, [z]⟩ := by
  simp only [Pile.afterRunRemoved, Pile.revealTop, h]
  rfl

/-- The emptied pile's burn at an empty hidden deck (cited copy of
`Orig/ForkAscent.ascent_afterRunRemoved_burn`). -/
private theorem steered_afterRunRemoved_burn {p : Pile}
    (h : p.hidden = []) :
    Pile.afterRunRemoved p [] = ⟨[], []⟩ := by
  simp only [Pile.afterRunRemoved, Pile.revealTop, h]

/-- The positional partition: every list splits at the first
occurrence into the below prefix and the `fromCard` run (cited copy
of `Orig.ForkAscent.ascent_split_mem`). -/
private theorem steered_split_mem (d : Card) :
    ∀ (l : List Card), l = below d l ++ fromCard d l := by
  intro l
  induction l with
  | nil => rfl
  | cons x t ih =>
      by_cases hxd : x = d
      · rw [below_cons, ite_eq_left hxd, fromCard, ite_eq_left hxd,
          List.nil_append]
      · rw [below_cons, ite_eq_right hxd, fromCard, ite_eq_right hxd]
        exact congrArg (x :: ·) ih

/-- **THE FACE-UP PRESERVATION, RAISE ARM** (the cited copy of
`Orig.ForkAscent.ascent_faceUp_raise` :1053-1094): a licensed raise
removes exactly the raised top; every OTHER face-up card stays
face-up. -/
private theorem steered_faceUp_raise {st st' : State} {c z : Card}
    (hstep : State.step st (Move.tabToFound z) = some st')
    (hne : c ≠ z) (hmem : ∃ a, c ∈ (st.piles a).faceUp) :
    ∃ a', c ∈ (st'.piles a').faceUp := by
  obtain ⟨a, hm⟩ := hmem
  obtain ⟨-, k, hk, hsuc⟩ := step_tabToFound_inv hstep
  by_cases hak : a = k
  · rw [hak] at hm
    have htopz : lastOf (st.piles k).faceUp = some z := (pileOfTop_top hk).2
    have hchop : (st.piles k).faceUp
        = chop (st.piles k).faceUp ++ [z] := lastOf_chop htopz
    have hcchop : c ∈ chop (st.piles k).faceUp := by
      rw [hchop] at hm
      rcases List.mem_append.mp hm with h1 | h2
      · exact h1
      · rcases List.mem_cons.mp h2 with hc | hc
        · exact absurd hc hne
        · cases hc
    have hchne : chop (st.piles k).faceUp ≠ [] := by
      intro hc
      rw [hc] at hcchop
      cases hcchop
    have hpilek : st'.piles k
        = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp) := by
      rw [hsuc]
      show (if k = k then
          Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
          else st.piles k)
          = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
      rw [ite_eq_left rfl]
    refine ⟨k, ?_⟩
    rw [hpilek, afterRunRemoved_ne hchne]
    exact hcchop
  · refine ⟨a, ?_⟩
    have hpile : st'.piles a = st.piles a := by
      rw [hsuc]
      show (if a = k then
          Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
          else st.piles a) = st.piles a
      rw [ite_eq_right (fun h => hak h)]
    rw [hpile]
    exact hm

/-- **THE INDEX-EXACT CAP ARITHMETIC** (cited copy of
`Orig.ForkAscent.ascent_idxCap_of_ne` :1526-1540): a card of the SAME
suit whose index sits at-or-below a family member's, and which is not
that member, sits strictly below it. -/
private theorem steered_idxCap_of_ne {x z : Card}
    (hcap : z.rank.toIdx ≤ x.rank.toIdx)
    (hsuit : z.suit = x.suit) (hne : z ≠ x) :
    z.rank.toIdx + 1 ≤ x.rank.toIdx := by
  obtain ⟨zs, zr⟩ := z
  obtain ⟨xs, xr⟩ := x
  have hss : zs = xs := hsuit
  by_cases hr : zr.toIdx = xr.toIdx
  · refine absurd ?_ hne
    show (⟨zs, zr⟩ : Card) = ⟨xs, xr⟩
    rw [hss, Rank.toIdx_inj hr]
  · have hcap' : zr.toIdx ≤ xr.toIdx := hcap
    have hne' : zr.toIdx ≠ xr.toIdx := hr
    have hgoal : zr.toIdx + 1 ≤ xr.toIdx := by omega
    exact hgoal

/-- The steered run preserves WF (the mirror of
`Orig.ForkAscent.ascent_run_wf` :1151-1156 over the leaf's own
inductive; `step_wf` chains). -/
private theorem steered_run_wf {s : State} (hwf : s.WF) :
    ∀ {ρ : List Move} {W : State}, SteeredRun s ρ W → W.WF := by
  intro ρ W h
  induction h with
  | nil st => exact hwf
  | @cons st s' W m ρ hletter _hfirst hstep hrest ih =>
      exact ih (step_wf hwf hstep)

/-- **THE BURN BAR** (cited copy of `Orig.ForkAscent.ascent_slideBase_ne`
:1572-1596): at a `WF` state, a fired slide's `inr` landing base tops a
pile OTHER than the departed run's source. -/
private theorem steered_slideBase_ne {st : State} (hwf : st.WF) {d z : Card}
    {a k : Anchor}
    (hhold : st.pileHolding d = some a)
    (hpot : st.pileOfTop z = some k)
    (hcan : st.canPlace d (Sum.inr z) = true) : k ≠ a := by
  intro hcon
  rw [hcon] at hpot
  obtain ⟨-, -, hfit⟩ := canPlace_inr hcan
  have hznd : z ≠ d := fun hcon' => by
    obtain ⟨hr, -⟩ := (canSitOn_eq d z).mp hfit
    rw [← hcon'] at hr
    omega
  have hzrun : z ∈ fromCard d ((st.piles a).faceUp) := by
    have hlast0 : lastOf ((st.piles a).faceUp) = some z := (pileOfTop_top hpot).2
    have hdmem : d ∈ (st.piles a).faceUp := pileHolding_mem hhold
    obtain ⟨t, ht⟩ := fromCard_eq_head_of_mem hdmem
    have hrnne : fromCard d ((st.piles a).faceUp) ≠ [] := by
      rw [ht]
      simp
    rw [steered_split_mem d ((st.piles a).faceUp),
      steered_lastOf_append _ _ hrnne] at hlast0
    exact lastOf_mem hlast0
  have hfalse := ascent_selfland_refuted hwf hhold hzrun hznd
  rw [hcan] at hfalse
  simp at hfalse

/-- **THE MID-STATE LANDING PIN** (cited copy of
`Orig.ForkAscent.ascent_slideLanding` :1618-1668): after the departed
run's source pile is rewritten, the landing base still tops exactly
the pile it topped. -/
private theorem steered_slideLanding {st : State} (hwf : st.WF) {d z : Card}
    {a k : Anchor}
    (hka : k ≠ a)
    (hpot : st.pileOfTop z = some k) :
    (st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below d ((st.piles a).faceUp)))).pileOfTop z
      = some k := by
  refine steered_topSearch _ (by
    rw [setPile_piles_ne hka]
    exact (pileOfTop_eq_some_iff hwf).1 hpot) ?_
  intro y _hy hyne
  by_cases hya : y = a
  · rw [hya, setPile_piles_self]
    show Pile.top
        (Pile.afterRunRemoved (st.piles a) (below d ((st.piles a).faceUp))) ≠ some z
    cases hpre : below d ((st.piles a).faceUp) with
    | nil =>
        cases hhid : (st.piles a).hidden with
        | nil =>
            rw [steered_afterRunRemoved_burn hhid]
            exact fun hcon => absurd hcon (by simp [Pile.top, lastOf])
        | cons h t =>
            have hhmem : h ∈ (st.piles a).hidden := by
              rw [hhid]
              exact List.mem_cons_self ..
            have hzne : h ≠ z := fun hcon =>
              (mem_hidden_unique hwf hhmem k hka).2.1
                (by rw [hcon]; exact lastOf_mem (pileOfTop_top hpot).2)
            rw [steered_afterRunRemoved_reveal hhid]
            intro hcon
            have hlasth : (⟨t, [h]⟩ : Pile).top = some h := rfl
            rw [hlasth] at hcon
            exact hzne (Option.some.inj hcon)
    | cons w ws =>
        rw [afterRunRemoved_ne (by simp)]
        intro hcon
        have hbr : ({ (st.piles a) with faceUp := w :: ws } : Pile).top
            = lastOf (w :: ws) := rfl
        rw [hbr] at hcon
        have hzin : z ∈ (st.piles a).faceUp :=
          mem_below ((st.piles a).faceUp) (by
            rw [hpre]
            exact lastOf_mem hcon)
        exact (mem_faceUp_unique hwf (lastOf_mem (pileOfTop_top hpot).2) a
          (fun hq => hka hq.symm)).1 hzin
  · rw [setPile_piles_ne hya]
    intro hcon
    have hsome := (pileOfTop_eq_some_iff hwf).2 hcon
    rw [hpot] at hsome
    injection hsome with hq
    exact hyne hq.symm

/-- **THE FACE-UP PRESERVATION, SLIDE ARM** (cited copy of
`Orig.ForkAscent.ascent_slide_faceUp` :1675-1751): along a FIRED
slide at a `WF` state, every face-up card of the pre-state is face-up
at the successor. -/
private theorem steered_slide_faceUp {st s' : State} (hwf : st.WF) {d : Card}
    {b : Base}
    (hstep : State.step st (Move.tabToTab d b) = some s')
    {c : Card} {p : Anchor} (hmem : c ∈ (st.piles p).faceUp) :
    ∃ p', c ∈ (s'.piles p').faceUp := by
  obtain ⟨a, hhold, hcan, -, hsplq⟩ := step_tabToTab_inv hstep
  rw [hsplq]
  by_cases hpa : p = a
  · rw [hpa] at hmem
    have hcm : c ∈ below d ((st.piles a).faceUp) ++
        fromCard d ((st.piles a).faceUp) := by
      rw [← steered_split_mem d ((st.piles a).faceUp)]
      exact hmem
    by_cases hcmem : c ∈ below d ((st.piles a).faceUp)
    · have hprene : below d ((st.piles a).faceUp) ≠ [] := by
        intro hc
        rw [hc] at hcmem
        cases hcmem
      cases b with
      | inl n =>
          have hdmem : d ∈ (st.piles a).faceUp := pileHolding_mem hhold
          obtain ⟨hemp, -⟩ := canPlace_inl hcan
          obtain ⟨-, hfn⟩ := (Pile.isEmpty_eq _).mp hemp
          have hna : a ≠ n := by
            intro hcon
            rw [hcon] at hdmem
            rw [hfn] at hdmem
            cases hdmem
          exact ⟨a, by
            rw [putRun_eq_inl, setPile_piles_ne hna, setPile_piles_self,
              afterRunRemoved_ne hprene]
            exact hcmem⟩
      | inr z =>
          obtain ⟨k, hpotk, -⟩ := canPlace_inr hcan
          have hka : k ≠ a := steered_slideBase_ne hwf hhold hpotk hcan
          have hhak : a ≠ k := fun hq => hka hq.symm
          have hpotM := steered_slideLanding (d := d) hwf hka hpotk
          exact ⟨a, by
            rw [putRun_piles_inr_ne _ _ _ k hpotM hhak, setPile_piles_self,
              afterRunRemoved_ne hprene]
            exact hcmem⟩
    · have hcmemr : c ∈ fromCard d ((st.piles a).faceUp) := by
        rcases List.mem_append.mp hcm with h' | h'
        · exact absurd h' hcmem
        · exact h'
      cases b with
      | inl n =>
          exact ⟨n, by rw [putRun_eq_inl, setPile_piles_self]; exact hcmemr⟩
      | inr z =>
          obtain ⟨k, hpotk, -⟩ := canPlace_inr hcan
          have hka : k ≠ a := steered_slideBase_ne hwf hhold hpotk hcan
          have hpotM := steered_slideLanding (d := d) hwf hka hpotk
          exact ⟨k, by
            rw [putRun_inr_eq hpotM, setPile_piles_self]
            exact List.mem_append.mpr (Or.inr hcmemr)⟩
  · cases b with
    | inl n =>
        by_cases hpn : p = n
        · obtain ⟨hemp, -⟩ := canPlace_inl hcan
          obtain ⟨-, hfn⟩ := (Pile.isEmpty_eq _).mp hemp
          rw [hpn, hfn] at hmem
          cases hmem
        · exact ⟨p, by
            rw [putRun_eq_inl, setPile_piles_ne hpn, setPile_piles_ne hpa]
            exact hmem⟩
    | inr z =>
        obtain ⟨k, hpotk, -⟩ := canPlace_inr hcan
        have hka : k ≠ a := steered_slideBase_ne hwf hhold hpotk hcan
        have hpotM := steered_slideLanding (d := d) hwf hka hpotk
        by_cases hpk : p = k
        · rw [hpk] at hmem
          exact ⟨k, by
            rw [putRun_inr_eq hpotM, setPile_piles_self, setPile_piles_ne hka]
            exact List.mem_append.mpr (Or.inl hmem)⟩
        · exact ⟨p, by
            rw [putRun_piles_inr_ne _ _ _ k hpotM hpk, setPile_piles_ne hpa]
            exact hmem⟩

/-! ## §1. P4 — the persistent pair -/

/-- **THE PERSISTENT PAIR** (P4): a card and its twin both face-up at
the start and both at-or-above their family rungs there, remain
face-up and rung-capped at the start's margins at EVERY state a
steered trajectory reaches — under the explicit no-eat premise: no
founding of either member anywhere along the trajectory.  The mirror
of `Orig.ForkAscent.ascent_pair_persists` (:1763-1852), with the two
substitutions this wave owns: the induction rides `SteeredRun`, and
the old full-time-guard derivation of `hne1`/`hne2` is replaced by
the head instance of `hnoeat` (the tail fed to `ih` through
`List.mem_cons`).  The slide legs' rung freeze reads the leaf's own
`steered_rung_slide`. -/
theorem steered_pair_persists {s : State} (hwf : s.WF) {x : Card}
    (hfu₁ : ∃ a, x ∈ (s.piles a).faceUp)
    (hfu₂ : ∃ b, x.twin ∈ (s.piles b).faceUp)
    (hrg₁ : rungAt s x.suit ≤ x.rank.toIdx)
    (hrg₂ : rungAt s x.twin.suit ≤ x.twin.rank.toIdx)
    {ρ : List Move} {W : State}
    (hrun : SteeredRun s ρ W)
    (hnoeat : ∀ m ∈ ρ, ∀ c, m = Move.tabToFound c → c ≠ x ∧ c ≠ x.twin) :
    (∃ a, x ∈ (W.piles a).faceUp) ∧
      (∃ b, x.twin ∈ (W.piles b).faceUp) ∧
      rungAt W x.suit ≤ x.rank.toIdx ∧
      rungAt W x.twin.suit ≤ x.twin.rank.toIdx := by
  induction hrun with
  | nil st => exact ⟨hfu₁, hfu₂, hrg₁, hrg₂⟩
  | @cons st s' W m ρ hletter _hfirst hstep hrest ih =>
      cases m with
      | tabToFound c =>
          obtain ⟨hn, a₀, hpo₀, hspl⟩ := step_tabToFound_inv hstep
          have hnext : c.rank.toIdx = st.foundHeight c.suit :=
            of_decide_eq_true hn
          obtain ⟨hne1, hne2⟩ :=
            hnoeat (Move.tabToFound c) (List.mem_cons.2 (Or.inl rfl)) c rfl
          have H₁ : ∃ a, x ∈ (s'.piles a).faceUp :=
            steered_faceUp_raise hstep (fun hq => hne1 hq.symm) hfu₁
          have H₂ : ∃ a, x.twin ∈ (s'.piles a).faceUp :=
            steered_faceUp_raise hstep (fun hq => hne2 hq.symm) hfu₂
          have hFself : s'.found c.suit = st.found c.suit ++ [c] := by
            rw [hspl]
            exact setFound_found_self
          have hFne : ∀ σ : Suit, σ ≠ c.suit → s'.found σ = st.found σ := by
            intro σ hσ
            rw [hspl]
            exact setFound_found_ne hσ
          have H₃ : rungAt s' x.suit ≤ x.rank.toIdx := by
            by_cases hxs : c.suit = x.suit
            · have hcxlen : (st.found c.suit).length = c.rank.toIdx := by
                rw [hnext]
                rfl
              have hcxle : c.rank.toIdx ≤ x.rank.toIdx := by
                rw [hnext, hxs]
                exact hrg₁
              have hcxcap : c.rank.toIdx + 1 ≤ x.rank.toIdx :=
                steered_idxCap_of_ne hcxle hxs hne1
              show (s'.found x.suit).length ≤ x.rank.toIdx
              rw [show s'.found x.suit = st.found c.suit ++ [c] from by
                  rw [← hxs]
                  exact hFself, List.length_append, hcxlen]
              exact hcxcap
            · have hxs' : x.suit ≠ c.suit := fun hq => hxs hq.symm
              show (s'.found x.suit).length ≤ x.rank.toIdx
              rw [hFne x.suit hxs']
              exact hrg₁
          have H₄ : rungAt s' x.twin.suit ≤ x.twin.rank.toIdx := by
            by_cases hxs : c.suit = x.twin.suit
            · have hcxlen : (st.found c.suit).length = c.rank.toIdx := by
                rw [hnext]
                rfl
              have hcxle : c.rank.toIdx ≤ x.twin.rank.toIdx := by
                rw [hnext, hxs]
                exact hrg₂
              have hcxcap : c.rank.toIdx + 1 ≤ x.twin.rank.toIdx :=
                steered_idxCap_of_ne hcxle hxs hne2
              show (s'.found x.twin.suit).length ≤ x.twin.rank.toIdx
              rw [show s'.found x.twin.suit = st.found c.suit ++ [c] from by
                  rw [← hxs]
                  exact hFself, List.length_append, hcxlen]
              exact hcxcap
            · have hxs' : x.twin.suit ≠ c.suit := fun hq => hxs hq.symm
              show (s'.found x.twin.suit).length ≤ x.twin.rank.toIdx
              rw [hFne x.twin.suit hxs']
              exact hrg₂
          exact ih (step_wf hwf hstep) H₁ H₂ H₃ H₄
            (fun hm hmem hc heq =>
              hnoeat hm (List.mem_cons.2 (Or.inr hmem)) hc heq)
      | tabToTab c b =>
          obtain ⟨p₁, hmem₁⟩ := hfu₁
          obtain ⟨p₂, hmem₂⟩ := hfu₂
          have H₁ : ∃ a, x ∈ (s'.piles a).faceUp := by
            obtain ⟨q, hq⟩ := steered_slide_faceUp hwf hstep hmem₁
            exact ⟨q, hq⟩
          have H₂ : ∃ a, x.twin ∈ (s'.piles a).faceUp := by
            obtain ⟨q, hq⟩ := steered_slide_faceUp hwf hstep hmem₂
            exact ⟨q, hq⟩
          have H₃ : rungAt s' x.suit ≤ x.rank.toIdx := by
            rw [steered_rung_slide hstep x.suit]
            exact hrg₁
          have H₄ : rungAt s' x.twin.suit ≤ x.twin.rank.toIdx := by
            rw [steered_rung_slide hstep x.twin.suit]
            exact hrg₂
          exact ih (step_wf hwf hstep) H₁ H₂ H₃ H₄
            (fun hm hmem hc heq =>
              hnoeat hm (List.mem_cons.2 (Or.inr hmem)) hc heq)
      | draw => exact absurd hletter (fun hl => hl)
      | wasteToFound c => exact absurd hletter (fun hl => hl)
      | wasteToTab c b => exact absurd hletter (fun hl => hl)
      | foundToTab c b => exact absurd hletter (fun hl => hl)

/-! ## §2. P4' — the mobility re-pack -/

/-- The four persistent clauses re-packed as the mobility read (the
mirror of `Orig.ForkAscent.ascent_persist_mobile` :1856-1861, the
residue routes' `MobileTwin` glue). -/
theorem steered_persist_mobile {st : State} {x : Card}
    (h₁ : ∃ a, x ∈ (st.piles a).faceUp)
    (h₂ : ∃ b, x.twin ∈ (st.piles b).faceUp)
    (h₃ : rungAt st x.suit ≤ x.rank.toIdx)
    (h₄ : rungAt st x.twin.suit ≤ x.twin.rank.toIdx) :
    MobileTwin st x := ⟨h₁, h₃, h₂, h₄⟩

/-! ## §3. P5 — the cell armor -/

/-- **THE CELL-ARMOR ROW** (P5): a cover-cell pair that arrives INTACT
at the start — both cells face-up and at-or-above their suits' rungs
there — survives every steered trajectory that never founds either
cell whole: at the landing both cells are still face-up, `MobileTwin`,
at-or-above their rungs, and UNFOUNDED (the face-up residence excludes
every foundation row at `WF`).  The mirror of
`Orig.ForkAscent.ascent_cell_armor` (:1879-1898) over P4, with the
never-found premise carried through `hnoeat`. -/
theorem steered_cell_armor {s : State} (hwf : s.WF)
    {d : Card}
    (hcell₁ : ∃ a, d ∈ (s.piles a).faceUp)
    (hcell₂ : ∃ b, d.twin ∈ (s.piles b).faceUp)
    (hrung₁ : rungAt s d.suit ≤ d.rank.toIdx)
    (hrung₂ : rungAt s d.twin.suit ≤ d.rank.toIdx)
    {ρ : List Move} {W : State}
    (hrun : SteeredRun s ρ W)
    (hnoeat : ∀ m ∈ ρ, ∀ c, m = Move.tabToFound c → c ≠ d ∧ c ≠ d.twin) :
    MobileTwin W d ∧
      W.foundHeight d.suit ≤ d.rank.toIdx ∧
      (∃ c, d ∈ (W.piles c).faceUp) ∧
      d ∉ W.found d.suit := by
  obtain ⟨h1, h2, h3, h4⟩ := steered_pair_persists hwf hcell₁ hcell₂ hrung₁
    (by rw [Card.twin_rank]; exact hrung₂) hrun hnoeat
  rw [steered_rung_height] at h3
  rw [steered_rung_height] at h4
  have hwfW : W.WF := steered_run_wf hwf hrun
  refine ⟨⟨h1, h3, h2, h4⟩, h3, h1, ?_⟩
  obtain ⟨c, hc⟩ := h1
  exact (mem_faceUp_only hwfW hc).2.2.2.2 d.suit

/-! ## §4. P6 — the climb reduction to the parking -/

/-- **THE CLIMB REDUCTION TO THE PARKING** (P6): the climb-delivery
conclusion — a delivered `DoubleHot` mobile pair, capped at its
family's rungs at the landing — is PURE ASSEMBLY off the persistent
pair (P4) plus the two FRONTIER-PARKING EQUALITIES (both family rungs
of the witnessed pair sit EXACTLY at the pair's rank at the
exhaustion).  The named open of R1's parking content is EXACTLY those
two equalities: parking them in closes the delivery with no further
content.  The mirror of `Orig.ForkAscent.ascent_climb_of_parked`
(:1910-1937). -/
theorem steered_climb_of_parked {s : State} (hwf : s.WF)
    {x : Card}
    (hfu₁ : ∃ a, x ∈ (s.piles a).faceUp)
    (hfu₂ : ∃ b, x.twin ∈ (s.piles b).faceUp)
    (hrg₁ : rungAt s x.suit ≤ x.rank.toIdx)
    (hrg₂ : rungAt s x.twin.suit ≤ x.rank.toIdx)
    {ρ : List Move} {W : State}
    (hrun : SteeredRun s ρ W)
    (hnoeat : ∀ m ∈ ρ, ∀ c, m = Move.tabToFound c → c ≠ x ∧ c ≠ x.twin)
    (hpark₁ : rungAt W x.suit = x.rank.toIdx)
    (hpark₂ : rungAt W x.twin.suit = x.rank.toIdx) :
    ∃ (y : Card), DoubleHot W y ∧ MobileTwin W y ∧
      rungAt W y.suit ≤ y.rank.toIdx ∧
      rungAt W y.twin.suit ≤ y.rank.toIdx := by
  obtain ⟨h1, h2, h3, h4⟩ := steered_pair_persists hwf hfu₁ hfu₂ hrg₁
    (by rw [Card.twin_rank]; exact hrg₂) hrun hnoeat
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  refine ⟨x, ⟨a, b, ha, hb, ?_, ?_⟩,
    ⟨⟨a, ha⟩, ?_, ⟨b, hb⟩, ?_⟩, ?_, ?_⟩
  · exact hpark₁.symm.trans (steered_rung_height W x.suit)
  · exact (congrArg Rank.toIdx (Card.twin_rank x)).trans
      (hpark₂.symm.trans (steered_rung_height W x.twin.suit))
  · exact Nat.le_of_eq
      (hpark₁.symm.trans (steered_rung_height W x.suit)).symm
  · rw [steered_rung_height] at h4
    exact h4
  · exact Nat.le_of_eq hpark₁
  · exact Nat.le_of_eq hpark₂

/-! ## §5. The audit battery

`#print axioms` per public fresh head — the four rows of the wave.
The kit copies are private per-file rows mirroring private sources;
the golden target is `[propext, Quot.sound]` like their mirrors. -/

#print axioms steered_pair_persists
#print axioms steered_persist_mobile
#print axioms steered_cell_armor
#print axioms steered_climb_of_parked

/- APPEND-MARKER -/
/-! ## §6. THE FALSIFIER — `steered_ascent_forks` REFUTED (2026-10-17)

The frozen §3 candidate is FALSE, certified end-to-end: the loA
counterexample — a WF, hbelow-admitting start whose RAW five-leg
play manifests the fork (`ForkWitness loA_F loA_s3`, SB-decided)
while the STEERED spine from the same start — six rank-minimal
raise letters, every letter and every head certified — ends
SteeredStuck at loA_T, a certified non-forkState.  The candidate
keeps its sorry as the honest witness of a false statement (the
fa2/ascent_cover_cell precedent); the negation
`steered_ascent_forks_refuted` beside it carries the fence: NEVER
RETRY the stuck-implies-forkState conclusion over the joint
arrivals — the spine eats the pair at its own rank (the loyalty
search's loH1/loA pattern) unless a COLD cover starves it (the
repair probe's rank-starvation invariant), and the loF2-class
oscillator never reaches stuck at all.  The successor statements
are the DICHOTOMY: the starvation lemma (cold cover standing, the
proved preempt bar P3b riding coldness) and the consumption lemma
(coverless joint arrival eats, rungs park past the pair's rank).
Promoted verbatim from the certified scratch (exit 0, 28 heads).
-/
/-! ## §0. The board and the successor chain -/

private def faCrd (s : Suit) (r : Rank) : Card := ⟨s, r⟩
private def faTakeUp (s : Suit) (n : Nat) : List Card := s.upCards.take n

private def loA_h2 : Card := faCrd .heart .two
private def loA_h3 : Card := faCrd .heart .three
private def loA_h4 : Card := faCrd .heart .four
private def loA_d2 : Card := faCrd .diamond .two
private def loA_d3 : Card := faCrd .diamond .three
private def loA_d4 : Card := faCrd .diamond .four
private def loA_sA : Card := faCrd .spade .ace
private def loA_s2 : Card := faCrd .spade .two
private def loA_s3 : Card := faCrd .spade .three
private def loA_cA : Card := faCrd .club .ace
private def loA_c2 : Card := faCrd .club .two
private def loA_c3 : Card := faCrd .club .three

/-- **THE START** — the below-frontier climb board: black
foundations empty, the black ace/deuce climb material seated on red
stools, the joint black-threes pair waiting over the red fours. -/
private def loA : State where
  found := fun _ => []
  piles := fun a => match a with
    | .p0 => ⟨[], [loA_h4, loA_s3]⟩
    | .p1 => ⟨[], [loA_d4, loA_c3]⟩
    | .p2 => ⟨[], [loA_h2, loA_sA]⟩
    | .p3 => ⟨[], [loA_h3, loA_s2]⟩
    | .p4 => ⟨[], [loA_d2, loA_cA]⟩
    | .p5 => ⟨[], [loA_d3, loA_c2]⟩
    | _ => ⟨[], []⟩
  stock :=
    [faCrd .spade .four, faCrd .spade .five, faCrd .spade .six,
     faCrd .spade .seven, faCrd .spade .eight, faCrd .spade .nine,
     faCrd .spade .ten, faCrd .spade .jack, faCrd .spade .queen,
     faCrd .spade .king,
     faCrd .heart .ace, faCrd .heart .five, faCrd .heart .six,
     faCrd .heart .seven, faCrd .heart .eight, faCrd .heart .nine,
     faCrd .heart .ten, faCrd .heart .jack, faCrd .heart .queen,
     faCrd .heart .king,
     faCrd .diamond .ace, faCrd .diamond .five, faCrd .diamond .six,
     faCrd .diamond .seven, faCrd .diamond .eight, faCrd .diamond .nine,
     faCrd .diamond .ten, faCrd .diamond .jack, faCrd .diamond .queen,
     faCrd .diamond .king,
     faCrd .club .four, faCrd .club .five, faCrd .club .six,
     faCrd .club .seven, faCrd .club .eight, faCrd .club .nine,
     faCrd .club .ten, faCrd .club .jack, faCrd .club .queen,
     faCrd .club .king]
  waste := []
  drawStep := 1

theorem loA_wf : loA.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    cases s <;> exact ⟨0, rfl⟩
  · intro a
    cases a <;> decide
  · intro c _
    rcases c with ⟨s, r⟩
    cases s <;> cases r <;> decide
  · decide

/-- After leg 1 (raise the spade ace): the splice successor. -/
private def loA_1 : State :=
  { loA.setFound Suit.spade (loA.found Suit.spade ++ [loA_sA]) with
    piles := fun a' => if a' = Anchor.p2 then
        Pile.afterRunRemoved (loA.piles Anchor.p2)
          (chop (loA.piles Anchor.p2).faceUp)
      else loA.piles a' }

/-- After leg 2 (raise the club ace). -/
private def loA_2 : State :=
  { loA_1.setFound Suit.club (loA_1.found Suit.club ++ [loA_cA]) with
    piles := fun a' => if a' = Anchor.p4 then
        Pile.afterRunRemoved (loA_1.piles Anchor.p4)
          (chop (loA_1.piles Anchor.p4).faceUp)
      else loA_1.piles a' }

/-- After leg 3 (raise the spade deuce). -/
private def loA_3 : State :=
  { loA_2.setFound Suit.spade (loA_2.found Suit.spade ++ [loA_s2]) with
    piles := fun a' => if a' = Anchor.p3 then
        Pile.afterRunRemoved (loA_2.piles Anchor.p3)
          (chop (loA_2.piles Anchor.p3).faceUp)
      else loA_2.piles a' }

/-- After leg 4 (raise the club deuce): the parking zone. -/
private def loA_4 : State :=
  { loA_3.setFound Suit.club (loA_3.found Suit.club ++ [loA_c2]) with
    piles := fun a' => if a' = Anchor.p5 then
        Pile.afterRunRemoved (loA_3.piles Anchor.p5)
          (chop (loA_3.piles Anchor.p5).faceUp)
      else loA_3.piles a' }

/-- After leg 5 (raise the spade three): the pair half-eaten. -/
private def loA_5 : State :=
  { loA_4.setFound Suit.spade (loA_4.found Suit.spade ++ [loA_s3]) with
    piles := fun a' => if a' = Anchor.p0 then
        Pile.afterRunRemoved (loA_4.piles Anchor.p0)
          (chop (loA_4.piles Anchor.p0).faceUp)
      else loA_4.piles a' }

/-- **THE DRAIN TERMINAL** — after leg 6 (raise the club three):
the six bare red stools, black rungs at 3, red rungs at 0. -/
private def loA_T : State :=
  { loA_5.setFound Suit.club (loA_5.found Suit.club ++ [loA_c3]) with
    piles := fun a' => if a' = Anchor.p1 then
        Pile.afterRunRemoved (loA_5.piles Anchor.p1)
          (chop (loA_5.piles Anchor.p1).faceUp)
      else loA_5.piles a' }

/-- **THE FORK-MANIFESTING WORLD** — after the fifth raw play leg
(the seat of the bare stool h2 onto the club three's top, off the
parking zone loA_4): the covered-twin fork shape, one raw seat away
from the steered drain's parking zone. -/
private def loA_F : State :=
  (loA_4.setPile Anchor.p2
      (Pile.afterRunRemoved (loA_4.piles Anchor.p2)
        (below loA_h2 (loA_4.piles Anchor.p2).faceUp))).putRun
    [loA_h2] (Sum.inr loA_c3)

#eval forkStateSB loA_F
#eval (forkWitnessSB loA_F).isSome
#eval forkStateSB loA_T

/-! ## §1. The seven step legs (banked splice rows, `rfl`-closed) -/

theorem loA_leg1 : State.step loA (Move.tabToFound loA_sA) = some loA_1 := by
  rw [step_tabToFound_splice
      (by decide : loA.nextUp loA_sA = true)
      (by decide : loA.pileOfTop loA_sA = some Anchor.p2)]
  rfl

theorem loA_leg2 : State.step loA_1 (Move.tabToFound loA_cA) = some loA_2 := by
  rw [step_tabToFound_splice
      (by decide : loA_1.nextUp loA_cA = true)
      (by decide : loA_1.pileOfTop loA_cA = some Anchor.p4)]
  rfl

theorem loA_leg3 : State.step loA_2 (Move.tabToFound loA_s2) = some loA_3 := by
  rw [step_tabToFound_splice
      (by decide : loA_2.nextUp loA_s2 = true)
      (by decide : loA_2.pileOfTop loA_s2 = some Anchor.p3)]
  rfl

theorem loA_leg4 : State.step loA_3 (Move.tabToFound loA_c2) = some loA_4 := by
  rw [step_tabToFound_splice
      (by decide : loA_3.nextUp loA_c2 = true)
      (by decide : loA_3.pileOfTop loA_c2 = some Anchor.p5)]
  rfl

theorem loA_leg5 : State.step loA_4 (Move.tabToFound loA_s3) = some loA_5 := by
  rw [step_tabToFound_splice
      (by decide : loA_4.nextUp loA_s3 = true)
      (by decide : loA_4.pileOfTop loA_s3 = some Anchor.p0)]
  rfl

theorem loA_leg6 : State.step loA_5 (Move.tabToFound loA_c3) = some loA_T := by
  rw [step_tabToFound_splice
      (by decide : loA_5.nextUp loA_c3 = true)
      (by decide : loA_5.pileOfTop loA_c3 = some Anchor.p1)]
  rfl

/-- **THE MANIFESTING SEAT LEG** — the raw play's fifth move: the
bare stool h2 seats onto the club three's top (the cover slide the
steered alphabet never rank-serves; the RAW play owes no letter). -/
theorem loA_seatLeg :
    State.step loA_4 (Move.tabToTab loA_h2 (Sum.inr loA_c3)) = some loA_F := by
  rw [step_tabToTab_eq]
  rw [(by decide : loA_4.pileHolding loA_h2 = some Anchor.p2)]
  rw [(by decide : loA_4.canPlace loA_h2 (Sum.inr loA_c3) = true)]
  rfl

/-! ## §2. The six steered letters (joint and dead instances) -/

/-- Leg 1 — the spade ace raise at loA: the black aces are JOINT
(both vanilla-live at their stools). -/
theorem loA_leg1_letter : SteeredLetter loA (Move.tabToFound loA_sA) :=
  raiseGate_joint
    ⟨by decide, Anchor.p2, by decide, Or.inl (by decide)⟩
    ⟨by decide, Anchor.p4, by decide, Or.inl (by decide)⟩

/-- Leg 2 — the club ace raise at loA_1: the spade twin is FOUNDED,
so the S-grade rung pin kills its S-liveness — the DEAD instance. -/
theorem loA_leg2_letter : SteeredLetter loA_1 (Move.tabToFound loA_cA) :=
  raiseGate_dead
    ⟨by decide, Anchor.p4, by decide, Or.inl (by decide)⟩
    (fun hs => absurd (canRaiseS_rung hs) (by decide))

/-- Leg 3 — the spade deuce raise at loA_2: the black deuces are
JOINT. -/
theorem loA_leg3_letter : SteeredLetter loA_2 (Move.tabToFound loA_s2) :=
  raiseGate_joint
    ⟨by decide, Anchor.p3, by decide, Or.inl (by decide)⟩
    ⟨by decide, Anchor.p5, by decide, Or.inl (by decide)⟩

/-- Leg 4 — the club deuce raise at loA_3: the DEAD instance (the
founded spade twin's rung pin). -/
theorem loA_leg4_letter : SteeredLetter loA_3 (Move.tabToFound loA_c2) :=
  raiseGate_dead
    ⟨by decide, Anchor.p5, by decide, Or.inl (by decide)⟩
    (fun hs => absurd (canRaiseS_rung hs) (by decide))

/-- Leg 5 — the spade three raise at the parking zone loA_4: the
threes are JOINT — the pair arrives standing, and the spine eats
it. -/
theorem loA_leg5_letter : SteeredLetter loA_4 (Move.tabToFound loA_s3) :=
  raiseGate_joint
    ⟨by decide, Anchor.p0, by decide, Or.inl (by decide)⟩
    ⟨by decide, Anchor.p1, by decide, Or.inl (by decide)⟩

/-- Leg 6 — the club three raise at loA_5: the DEAD instance (the
founded spade twin). -/
theorem loA_leg6_letter : SteeredLetter loA_5 (Move.tabToFound loA_c3) :=
  raiseGate_dead
    ⟨by decide, Anchor.p1, by decide, Or.inl (by decide)⟩
    (fun hs => absurd (canRaiseS_rung hs) (by decide))

/-! ## §3. Rank-minimality: the competitor sweeps, decided -/

/-- The raise-side competitor kill: a strictly-smaller raise would
be a `CanRaise`, contradicting the decided vanilla sweep. -/
private theorem lowRaise_dead (st : State) (r : Nat)
    (hst : ∀ c, c.rank.toIdx < r → canRaiseB st c = false) :
    ∀ (c : Card), c.rank.toIdx < r → ¬ SteeredLetter st (Move.tabToFound c) := by
  intro c hlt hL
  have hf : canRaiseB st c = false := hst c hlt
  rw [(canRaiseB_true_iff).2 hL.1] at hf
  exact absurd hf (by simp)

/-- The rank-0 raise sweeps are vacuous (no card ranks below an
ace). -/
private theorem loA_lowraise : ∀ c, c.rank.toIdx < 0 → canRaiseB loA c = false := by
  intro c hlt
  exact absurd hlt (by omega)

private theorem loA_1_lowraise : ∀ c, c.rank.toIdx < 0 → canRaiseB loA_1 c = false := by
  intro c hlt
  exact absurd hlt (by omega)

/-- The rank-1 raise sweeps at loA_2 (after three legs) and loA_3:
the only cards below the deuce rank are the aces, all founded or
stocked — decided card by card. -/
private theorem loA_2_lowraise : ∀ c, c.rank.toIdx < 1 → canRaiseB loA_2 c = false := by
  intro c hlt
  rcases c with ⟨s, r'⟩
  cases s <;> cases r' <;> first
    | exact absurd hlt (by decide)
    | decide

private theorem loA_3_lowraise : ∀ c, c.rank.toIdx < 1 → canRaiseB loA_3 c = false := by
  intro c hlt
  rcases c with ⟨s, r'⟩
  cases s <;> cases r' <;> first
    | exact absurd hlt (by decide)
    | decide

/-- The rank-2 raise sweeps at the parking zone loA_4 and its
successor loA_5: below the threes stand the aces and deuces — the
black ones founded, the red ones cold stools. -/
private theorem loA_4_lowraise : ∀ c, c.rank.toIdx < 2 → canRaiseB loA_4 c = false := by
  intro c hlt
  rcases c with ⟨s, r'⟩
  cases s <;> cases r' <;> first
    | exact absurd hlt (by decide)
    | decide

private theorem loA_5_lowraise : ∀ c, c.rank.toIdx < 2 → canRaiseB loA_5 c = false := by
  intro c hlt
  rcases c with ⟨s, r'⟩
  cases s <;> cases r' <;> first
    | exact absurd hlt (by decide)
    | decide

/-- **THE SEAT-SIDE COMPETITOR KILL, STOOL INSTANCE** — the leaf's
own refusal row: an exposed stool pair is mobile (both mates
face-up) but never JOINT (both cold), so no stool seat is ever a
steered letter, whichever base it aims at.  The assignment's bar
(`tabToTab_irreversible_of_bare_nonking`) is the second kill
available here; the joint clause reaches first, WF-free. -/
private theorem stoolSeat_refused {st : State} (c : Card)
    (hmob : MobileTwin st c)
    (hn : ¬ (CanRaise st c ∧ CanRaise st c.twin)) :
    ∀ (b : Base), ¬ SteeredLetter st (Move.tabToTab c b) :=
  fun _ hL => seatGate_refuses_nonjoint hmob hn hL

/-- The off-board mover kill: a stocked or founded card has no
firing seat at any base — the raw tabToTab equation reads the
decided `pileHolding = none`. -/
private theorem offBoardSeat_refused (st : State) (c : Card)
    (hhold : st.pileHolding c = none) (b : Base) :
    ¬ SteeredLetter st (Move.tabToTab c b) := by
  intro hL
  have hnone : State.step st (Move.tabToTab c b) = none := by
    rw [step_tabToTab_eq, hhold]
  have hgate : seatGate st c b := hL
  rcases hgate with ⟨hfired, -, -⟩
  exact hfired hnone

/-- The stool-pair mobility facts (the parking zone and its
successor; h2/d2 both topping their bare stools, cold). -/
private theorem loA_4_mob_h2 : MobileTwin loA_4 loA_h2 :=
  ⟨⟨Anchor.p2, by decide⟩, by decide, ⟨Anchor.p4, by decide⟩, by decide⟩

private theorem loA_4_nonjoint_h2 : ¬ (CanRaise loA_4 loA_h2 ∧ CanRaise loA_4 loA_h2.twin) := by
  rintro ⟨hc, -⟩
  have hf : canRaiseB loA_4 loA_h2 = false := by decide
  rw [(canRaiseB_true_iff).2 hc] at hf
  exact absurd hf (by simp)

private theorem loA_4_mob_d2 : MobileTwin loA_4 loA_d2 :=
  ⟨⟨Anchor.p4, by decide⟩, by decide, ⟨Anchor.p2, by decide⟩, by decide⟩

private theorem loA_4_nonjoint_d2 : ¬ (CanRaise loA_4 loA_d2 ∧ CanRaise loA_4 loA_d2.twin) := by
  rintro ⟨hc, -⟩
  have hf : canRaiseB loA_4 loA_d2 = false := by decide
  rw [(canRaiseB_true_iff).2 hc] at hf
  exact absurd hf (by simp)

private theorem loA_5_mob_h2 : MobileTwin loA_5 loA_h2 :=
  ⟨⟨Anchor.p2, by decide⟩, by decide, ⟨Anchor.p4, by decide⟩, by decide⟩

private theorem loA_5_nonjoint_h2 : ¬ (CanRaise loA_5 loA_h2 ∧ CanRaise loA_5 loA_h2.twin) := by
  rintro ⟨hc, -⟩
  have hf : canRaiseB loA_5 loA_h2 = false := by decide
  rw [(canRaiseB_true_iff).2 hc] at hf
  exact absurd hf (by simp)

private theorem loA_5_mob_d2 : MobileTwin loA_5 loA_d2 :=
  ⟨⟨Anchor.p4, by decide⟩, by decide, ⟨Anchor.p2, by decide⟩, by decide⟩

private theorem loA_5_nonjoint_d2 : ¬ (CanRaise loA_5 loA_d2 ∧ CanRaise loA_5 loA_d2.twin) := by
  rintro ⟨hc, -⟩
  have hf : canRaiseB loA_5 loA_d2 = false := by decide
  rw [(canRaiseB_true_iff).2 hc] at hf
  exact absurd hf (by simp)

/-- The rank-0 seat sweeps are vacuous. -/
private theorem loA_lowseat : ∀ (c : Card), c.rank.toIdx < 0 →
    ∀ (b : Base), ¬ SteeredLetter loA (Move.tabToTab c b) := by
  intro c hlt _ _
  exact absurd hlt (by omega)

private theorem loA_1_lowseat : ∀ (c : Card), c.rank.toIdx < 0 →
    ∀ (b : Base), ¬ SteeredLetter loA_1 (Move.tabToTab c b) := by
  intro c hlt _ _
  exact absurd hlt (by omega)

/-- The rank-1 seat sweeps at loA_2/loA_3: every ace is off board
(founded or stocked) — no firing seat. -/
private theorem loA_2_lowseat : ∀ (c : Card), c.rank.toIdx < 1 →
    ∀ (b : Base), ¬ SteeredLetter loA_2 (Move.tabToTab c b) := by
  intro c hlt b hL
  refine offBoardSeat_refused loA_2 c ?_ b hL
  rcases c with ⟨s, r'⟩
  cases s <;> cases r' <;> first
    | exact absurd hlt (by decide)
    | decide

private theorem loA_3_lowseat : ∀ (c : Card), c.rank.toIdx < 1 →
    ∀ (b : Base), ¬ SteeredLetter loA_3 (Move.tabToTab c b) := by
  intro c hlt b hL
  refine offBoardSeat_refused loA_3 c ?_ b hL
  rcases c with ⟨s, r'⟩
  cases s <;> cases r' <;> first
    | exact absurd hlt (by decide)
    | decide

/-- **THE RANK-2 SEAT SWEEPS AT THE PARKING ZONE** — the critical
competitors: below the threes stand the aces, the deuces, and the
EXPOSED RED STOOLS h2/d2 (the only face-up low cards): the off-board
movers die at the fired-step-read, the stools at the joint clause
(mobile pairs, both members cold). -/
private theorem loA_4_lowseat : ∀ (c : Card), c.rank.toIdx < 2 →
    ∀ (b : Base), ¬ SteeredLetter loA_4 (Move.tabToTab c b) := by
  intro c hlt b hL
  by_cases hmem : loA_4.pileHolding c = none
  · exact offBoardSeat_refused loA_4 c hmem b hL
  · rcases c with ⟨s, r'⟩
    cases s <;> cases r' <;> first
      | exact absurd hlt (by decide)
      | exact absurd hmem (by decide)
      | exact stoolSeat_refused loA_h2 loA_4_mob_h2 loA_4_nonjoint_h2 b hL
      | exact stoolSeat_refused loA_d2 loA_4_mob_d2 loA_4_nonjoint_d2 b hL

private theorem loA_5_lowseat : ∀ (c : Card), c.rank.toIdx < 2 →
    ∀ (b : Base), ¬ SteeredLetter loA_5 (Move.tabToTab c b) := by
  intro c hlt b hL
  by_cases hmem : loA_5.pileHolding c = none
  · exact offBoardSeat_refused loA_5 c hmem b hL
  · rcases c with ⟨s, r'⟩
    cases s <;> cases r' <;> first
      | exact absurd hlt (by decide)
      | exact absurd hmem (by decide)
      | exact stoolSeat_refused loA_h2 loA_5_mob_h2 loA_5_nonjoint_h2 b hL
      | exact stoolSeat_refused loA_d2 loA_5_mob_d2 loA_5_nonjoint_d2 b hL

/-- The uniform rank-minimality assembler: the two competitor
classes die at the sweeps; the sentinel moves are never letters. -/
private theorem steeredFirst_of_sweeps (st : State) (m : Move) (r : Nat)
    (hm : letterRank m = r)
    (hraise : ∀ c, c.rank.toIdx < r → ¬ SteeredLetter st (Move.tabToFound c))
    (hseat : ∀ (c : Card), c.rank.toIdx < r →
      ∀ (b : Base), ¬ SteeredLetter st (Move.tabToTab c b)) :
    SteeredFirst st m := by
  intro m' hL
  cases m' with
  | draw => exact absurd hL (fun h => h)
  | wasteToFound c => exact absurd hL (fun h => h)
  | wasteToTab c b => exact absurd hL (fun h => h)
  | foundToTab c b => exact absurd hL (fun h => h)
  | tabToFound c =>
      by_cases hlt : c.rank.toIdx < r
      · exact absurd hL (hraise c hlt)
      · rw [hm]
        show c.rank.toIdx ≥ r
        omega
  | tabToTab c b =>
      by_cases hlt : c.rank.toIdx < r
      · exact absurd hL (hseat c hlt b)
      · rw [hm]
        show c.rank.toIdx ≥ r
        omega

theorem loA_leg1_first : SteeredFirst loA (Move.tabToFound loA_sA) :=
  steeredFirst_of_sweeps loA _ 0 rfl (lowRaise_dead loA 0 loA_lowraise) loA_lowseat

theorem loA_leg2_first : SteeredFirst loA_1 (Move.tabToFound loA_cA) :=
  steeredFirst_of_sweeps loA_1 _ 0 rfl (lowRaise_dead loA_1 0 loA_1_lowraise) loA_1_lowseat

theorem loA_leg3_first : SteeredFirst loA_2 (Move.tabToFound loA_s2) :=
  steeredFirst_of_sweeps loA_2 _ 1 rfl (lowRaise_dead loA_2 1 loA_2_lowraise) loA_2_lowseat

theorem loA_leg4_first : SteeredFirst loA_3 (Move.tabToFound loA_c2) :=
  steeredFirst_of_sweeps loA_3 _ 1 rfl (lowRaise_dead loA_3 1 loA_3_lowraise) loA_3_lowseat

theorem loA_leg5_first : SteeredFirst loA_4 (Move.tabToFound loA_s3) :=
  steeredFirst_of_sweeps loA_4 _ 2 rfl (lowRaise_dead loA_4 2 loA_4_lowraise) loA_4_lowseat

theorem loA_leg6_first : SteeredFirst loA_5 (Move.tabToFound loA_c3) :=
  steeredFirst_of_sweeps loA_5 _ 2 rfl (lowRaise_dead loA_5 2 loA_5_lowraise) loA_5_lowseat

/-- **THE CERTIFIED STEERED TRAJECTORY** — six raise legs, every
head a steered letter at its own rank-minimal moment, landing the
drain world loA_T. -/
theorem loA_run : SteeredRun loA
    [Move.tabToFound loA_sA, Move.tabToFound loA_cA,
     Move.tabToFound loA_s2, Move.tabToFound loA_c2,
     Move.tabToFound loA_s3, Move.tabToFound loA_c3] loA_T :=
  SteeredRun.cons loA_leg1_letter loA_leg1_first loA_leg1
    (SteeredRun.cons loA_leg2_letter loA_leg2_first loA_leg2
      (SteeredRun.cons loA_leg3_letter loA_leg3_first loA_leg3
        (SteeredRun.cons loA_leg4_letter loA_leg4_first loA_leg4
          (SteeredRun.cons loA_leg5_letter loA_leg5_first loA_leg5
            (SteeredRun.cons loA_leg6_letter loA_leg6_first loA_leg6
              (SteeredRun.nil loA_T))))))

/-! ## §4. The terminal is steered-stuck and NOT a forkState -/

/-- Nothing at the drain world is vanilla-licensable. -/
private theorem loA_T_noraise : ∀ c, canRaiseB loA_T c = false := by
  intro c
  rcases c with ⟨s, r'⟩
  cases s <;> cases r' <;> decide

/-- The drain world's stool-pair facts: all three red pairs are
mobile (both mates exposed) and cold (the nonjoint refutations). -/
private theorem loA_T_mob_h2 : MobileTwin loA_T loA_h2 :=
  ⟨⟨Anchor.p2, by decide⟩, by decide, ⟨Anchor.p4, by decide⟩, by decide⟩

private theorem loA_T_nonjoint_h2 : ¬ (CanRaise loA_T loA_h2 ∧ CanRaise loA_T loA_h2.twin) := by
  rintro ⟨hc, -⟩
  have hb : canRaiseB loA_T loA_h2 = true := (canRaiseB_true_iff).2 hc
  rw [loA_T_noraise loA_h2] at hb
  exact absurd hb (by simp)

private theorem loA_T_mob_d2 : MobileTwin loA_T loA_d2 :=
  ⟨⟨Anchor.p4, by decide⟩, by decide, ⟨Anchor.p2, by decide⟩, by decide⟩

private theorem loA_T_nonjoint_d2 : ¬ (CanRaise loA_T loA_d2 ∧ CanRaise loA_T loA_d2.twin) := by
  rintro ⟨hc, -⟩
  have hb : canRaiseB loA_T loA_d2 = true := (canRaiseB_true_iff).2 hc
  rw [loA_T_noraise loA_d2] at hb
  exact absurd hb (by simp)

private theorem loA_T_mob_h3 : MobileTwin loA_T loA_h3 :=
  ⟨⟨Anchor.p3, by decide⟩, by decide, ⟨Anchor.p5, by decide⟩, by decide⟩

private theorem loA_T_nonjoint_h3 : ¬ (CanRaise loA_T loA_h3 ∧ CanRaise loA_T loA_h3.twin) := by
  rintro ⟨hc, -⟩
  have hb : canRaiseB loA_T loA_h3 = true := (canRaiseB_true_iff).2 hc
  rw [loA_T_noraise loA_h3] at hb
  exact absurd hb (by simp)

private theorem loA_T_mob_d3 : MobileTwin loA_T loA_d3 :=
  ⟨⟨Anchor.p5, by decide⟩, by decide, ⟨Anchor.p3, by decide⟩, by decide⟩

private theorem loA_T_nonjoint_d3 : ¬ (CanRaise loA_T loA_d3 ∧ CanRaise loA_T loA_d3.twin) := by
  rintro ⟨hc, -⟩
  have hb : canRaiseB loA_T loA_d3 = true := (canRaiseB_true_iff).2 hc
  rw [loA_T_noraise loA_d3] at hb
  exact absurd hb (by simp)

private theorem loA_T_mob_h4 : MobileTwin loA_T loA_h4 :=
  ⟨⟨Anchor.p0, by decide⟩, by decide, ⟨Anchor.p1, by decide⟩, by decide⟩

private theorem loA_T_nonjoint_h4 : ¬ (CanRaise loA_T loA_h4 ∧ CanRaise loA_T loA_h4.twin) := by
  rintro ⟨hc, -⟩
  have hb : canRaiseB loA_T loA_h4 = true := (canRaiseB_true_iff).2 hc
  rw [loA_T_noraise loA_h4] at hb
  exact absurd hb (by simp)

private theorem loA_T_mob_d4 : MobileTwin loA_T loA_d4 :=
  ⟨⟨Anchor.p1, by decide⟩, by decide, ⟨Anchor.p0, by decide⟩, by decide⟩

private theorem loA_T_nonjoint_d4 : ¬ (CanRaise loA_T loA_d4 ∧ CanRaise loA_T loA_d4.twin) := by
  rintro ⟨hc, -⟩
  have hb : canRaiseB loA_T loA_d4 = true := (canRaiseB_true_iff).2 hc
  rw [loA_T_noraise loA_d4] at hb
  exact absurd hb (by simp)

/-- No seat letter fires at the drain world: every mover is either
off board or an exposed cold stool (mobile, refused at the joint
clause). -/
private theorem loA_T_noseat : ∀ (c : Card) (b : Base),
    ¬ SteeredLetter loA_T (Move.tabToTab c b) := by
  intro c b hL
  by_cases hmem : loA_T.pileHolding c = none
  · exact offBoardSeat_refused loA_T c hmem b hL
  · rcases c with ⟨s, r'⟩
    cases s <;> cases r' <;> first
      | exact absurd hmem (by decide)
      | exact stoolSeat_refused loA_h2 loA_T_mob_h2 loA_T_nonjoint_h2 b hL
      | exact stoolSeat_refused loA_d2 loA_T_mob_d2 loA_T_nonjoint_d2 b hL
      | exact stoolSeat_refused loA_h3 loA_T_mob_h3 loA_T_nonjoint_h3 b hL
      | exact stoolSeat_refused loA_d3 loA_T_mob_d3 loA_T_nonjoint_d3 b hL
      | exact stoolSeat_refused loA_h4 loA_T_mob_h4 loA_T_nonjoint_h4 b hL
      | exact stoolSeat_refused loA_d4 loA_T_mob_d4 loA_T_nonjoint_d4 b hL

/-- **THE TERMINAL IS STEERED-STUCK** — no raise letter (nothing is
licensable), no seat letter (stool refusals), nothing else a letter
at all. -/
theorem loA_stuck : SteeredStuck loA_T := by
  intro m hL
  cases m with
  | draw => exact absurd hL (fun h => h)
  | wasteToFound c => exact absurd hL (fun h => h)
  | wasteToTab c b => exact absurd hL (fun h => h)
  | foundToTab c b => exact absurd hL (fun h => h)
  | tabToFound c =>
      have hb : canRaiseB loA_T c = true := (canRaiseB_true_iff).2 hL.1
      rw [loA_T_noraise c] at hb
      exact absurd hb (by simp)
  | tabToTab c b => exact absurd hL (loA_T_noseat c b)

theorem loA_T_wf : loA_T.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    cases s with
    | spade => exact ⟨3, rfl⟩
    | heart => exact ⟨0, rfl⟩
    | diamond => exact ⟨0, rfl⟩
    | club => exact ⟨3, rfl⟩
  · intro a
    cases a <;> decide
  · intro c _
    rcases c with ⟨s, r⟩
    cases s <;> cases r <;> decide
  · decide

/-- **THE TERMINAL IS NOT A FORKSTATE** — the SB census decides
false at the drain world, and the banked bridge's forward direction
carries it: no forkState at loA_T. -/
theorem loA_T_noFork : ¬ forkState loA_T := by
  intro h
  have hsb := (forkStateSB_true_iff loA_T_wf).2 h
  rw [(by decide : forkStateSB loA_T = false)] at hsb
  exact absurd hsb (by simp)

/-! ## §5. The hbelow parcel at loA -/

theorem loA_F_wf : loA_F.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    cases s with
    | spade => exact ⟨2, rfl⟩
    | heart => exact ⟨0, rfl⟩
    | diamond => exact ⟨0, rfl⟩
    | club => exact ⟨2, rfl⟩
  · intro a
    cases a <;> decide
  · intro c _
    rcases c with ⟨s, r⟩
    cases s <;> cases r <;> decide
  · decide

/-- **THE RAW FORK-MANIFESTING PLAY** — four founding legs plus the
cover seat, run-composed through the banked `run_one`/`run_split`. -/
private theorem loA_run5 : loA.run
    [Move.tabToFound loA_sA, Move.tabToFound loA_cA,
     Move.tabToFound loA_s2, Move.tabToFound loA_c2,
     Move.tabToTab loA_h2 (Sum.inr loA_c3)] = some loA_F := by
  have r1 : loA.run [Move.tabToFound loA_sA] = some loA_1 := run_one loA_leg1
  have r2 : loA_1.run [Move.tabToFound loA_cA] = some loA_2 := run_one loA_leg2
  have r3 : loA_2.run [Move.tabToFound loA_s2] = some loA_3 := run_one loA_leg3
  have r4 : loA_3.run [Move.tabToFound loA_c2] = some loA_4 := run_one loA_leg4
  have r5 : loA_4.run [Move.tabToTab loA_h2 (Sum.inr loA_c3)] = some loA_F :=
    run_one loA_seatLeg
  have f45 : loA_3.run
      [Move.tabToFound loA_c2, Move.tabToTab loA_h2 (Sum.inr loA_c3)] = some loA_F :=
    run_split [Move.tabToFound loA_c2] loA_3 loA_4
      [Move.tabToTab loA_h2 (Sum.inr loA_c3)] loA_F r4 r5
  have f345 : loA_2.run
      [Move.tabToFound loA_s2, Move.tabToFound loA_c2,
       Move.tabToTab loA_h2 (Sum.inr loA_c3)] = some loA_F :=
    run_split [Move.tabToFound loA_s2] loA_2 loA_3
      [Move.tabToFound loA_c2, Move.tabToTab loA_h2 (Sum.inr loA_c3)] loA_F r3 f45
  have f2345 : loA_1.run
      [Move.tabToFound loA_cA, Move.tabToFound loA_s2, Move.tabToFound loA_c2,
       Move.tabToTab loA_h2 (Sum.inr loA_c3)] = some loA_F :=
    run_split [Move.tabToFound loA_cA] loA_1 loA_2
      [Move.tabToFound loA_s2, Move.tabToFound loA_c2,
       Move.tabToTab loA_h2 (Sum.inr loA_c3)] loA_F r2 f345
  exact run_split [Move.tabToFound loA_sA] loA loA_1
    [Move.tabToFound loA_cA, Move.tabToFound loA_s2, Move.tabToFound loA_c2,
     Move.tabToTab loA_h2 (Sum.inr loA_c3)] loA_F r1 f2345

/-- **THE FORK WITNESS AT loA_F** — the decided SB witness search
returns the spade three, and the banked sound row reads its parcel
(the saturation iff at the twin form plus the vanilla refusal of
the covered twin). -/
theorem loA_F_witness : ForkWitness loA_F loA_s3 := by
  obtain ⟨hiff, hpin⟩ :=
    forkWitnessSB_sound loA_F_wf
      (by decide : forkWitnessSB loA_F = some loA_s3)
  exact ⟨hiff, hpin⟩

/-- **THE hbelow PARCEL AT loA** — the raw fork-manifesting play
(four founding legs plus the cover seat), the fork witness, the
rungs strictly below the pair's rank, the pair deployed face-up. -/
theorem loA_hbelow :
    ∃ (F : State) (x : Card) (π : List Move),
      loA.run π = some F ∧ ForkWitness F x ∧
        rungAt loA x.suit ≤ x.rank.toIdx ∧
        rungAt loA x.twin.suit ≤ x.rank.toIdx ∧
        (∃ (a : Anchor), x ∈ (loA.piles a).faceUp) ∧
        (∃ (b : Anchor), x.twin ∈ (loA.piles b).faceUp) :=
  ⟨loA_F, loA_s3,
   [Move.tabToFound loA_sA, Move.tabToFound loA_cA,
    Move.tabToFound loA_s2, Move.tabToFound loA_c2,
    Move.tabToTab loA_h2 (Sum.inr loA_c3)],
   loA_run5, loA_F_witness,
   by decide, by decide,
   ⟨Anchor.p0, by decide⟩, ⟨Anchor.p1, by decide⟩⟩

/-! ## §6. THE FALSIFIER -/

/-- **`steered_ascent_forks` REFUTED** — the successor leaf's frozen
candidate, negated at its own signature (the frozen statement's
implicit binders rendered explicit; the body verbatim), refuted by
the complete loA counterexample: a WF, hbelow-admitting start whose
fully certified steered trajectory (six rank-minimal raise letters)
ends steered-stuck at a world that is certifiably not a forkState —
while the same start's raw five-leg play manifests the fork and
its `ForkWitness` on the nose.  The class of worlds the candidate
quantifies over is nonempty, and the candidate fails at its first
executable member: the spined climb parks nothing, eats the pair,
and drains; the fork the candidate promises every steered-stuck
world is manifested only by the raw play the candidate's own steer
never takes. -/
theorem steered_ascent_forks_refuted :
    ¬ (∀ (s : State), s.WF →
        (∃ (F : State) (x : Card) (π : List Move),
          s.run π = some F ∧ ForkWitness F x ∧
            rungAt s x.suit ≤ x.rank.toIdx ∧
            rungAt s x.twin.suit ≤ x.rank.toIdx ∧
            (∃ (a : Anchor), x ∈ (s.piles a).faceUp) ∧
            (∃ (b : Anchor), x.twin ∈ (s.piles b).faceUp)) →
        ∀ (ρ : List Move) (W : State),
          SteeredRun s ρ W → SteeredStuck W → forkState W) := by
  intro h
  refine absurd
    (h loA loA_wf loA_hbelow
      [Move.tabToFound loA_sA, Move.tabToFound loA_cA,
       Move.tabToFound loA_s2, Move.tabToFound loA_c2,
       Move.tabToFound loA_s3, Move.tabToFound loA_c3]
      loA_T loA_run loA_stuck)
    loA_T_noFork

/-! ## §7. The audit battery -/

#print axioms loA_wf
#print axioms loA_leg1
#print axioms loA_leg2
#print axioms loA_leg3
#print axioms loA_leg4
#print axioms loA_leg5
#print axioms loA_leg6
#print axioms loA_seatLeg
#print axioms loA_leg1_letter
#print axioms loA_leg2_letter
#print axioms loA_leg3_letter
#print axioms loA_leg4_letter
#print axioms loA_leg5_letter
#print axioms loA_leg6_letter
#print axioms loA_leg1_first
#print axioms loA_leg2_first
#print axioms loA_leg3_first
#print axioms loA_leg4_first
#print axioms loA_leg5_first
#print axioms loA_leg6_first
#print axioms loA_run
#print axioms loA_stuck
#print axioms loA_T_noFork
#print axioms loA_T_wf
#print axioms loA_F_wf
#print axioms loA_F_witness
#print axioms loA_hbelow
#print axioms steered_ascent_forks_refuted

/-! ## §7. THE CORRECTED PREMISE AND THE SUCCESSOR FAMILY (2026-10-17)

The premise cleanup the refutation demanded, plated into the slab
program's own vocabulary: the below-fork read is now the BANKED
twin-side def `familyBelowFrontier` (`Orig.LowSlab:239`, byte-frozen,
consumed verbatim — never redefined here), the x-side rung clause
kept in the package pending the absorption row below (it is
DERIVABLE at WF from the face-up clauses, so the clause is dead
weight the slab refinement already priced), and the guilty half of
the old premise — the RAW ∃-reachability — retired with the
refuted candidate: its successor carrier is the minimal `hreach`
of the consumption arm, and the reachability QUESTION belongs to
the starvation/consumption dichotomy, not to an unguarded ∃.

THE TWO SUCCESSOR ARMS (the dichotomy the probes certified):

* THE STARVATION ARM — PROVED HERE (`starved_pair_survives`):
  along any steered run threaded by a standing cover letter, no
  pair-member raise ever serves (the §2c preemption bar P3b,
  per-world), and the pair SURVIVES the run intact — the
  persistence row's own conclusion off the no-eat ledger.  The
  rp2/loF2 evidence shows the oscillators maintain the standing
  premise; its maintenance along free tails is the separately
  priced oscillator residue.
* THE CONSUMPTION ARM — FROZEN (`steered_stuck_elevates`, [H]):
  from a deployed slab start, every steered trajectory that ends
  steered-stuck ends with the slab ELEVATED — the twin founded, the
  covered side's rung past the witness rank.  The falsifier's
  terminal is the boarded shape (`loA_T_elevated`, decided); the
  general row consumes the LowSlab transport calculus (the
  elevation dichotomy rows) and the arrival-zone raise census. -/

/-- **THE BELOW-FORK PACKAGE** — the banked twin-side slab (verbatim)
plus the x-side rung clause and the pair's deployment. -/
def BelowForkDeployed (s : State) (x : Card) : Prop :=
  familyBelowFrontier s x ∧ rungAt s x.suit ≤ x.rank.toIdx ∧
    (∃ a, x ∈ (s.piles a).faceUp) ∧ (∃ b, x.twin ∈ (s.piles b).faceUp)

/-- **THE COVER'S OWN PLUG, SEAT SIDE** — at any world where a cover
seat letter stands steered-legal, the world is NOT steered-stuck:
the letter's own firing conjunct contradicts stuckness outright.
The rp2/loF2 oscillators' never-stuck behavior, at its mechanism's
grain; the oscillator's maintenance of the standing is the [H-mini]
priced in `steered_stuck_elevates`'s route step 1. -/
theorem not_stuck_of_coverStanding {W : State} {d : Card}
    (hstanding : ∃ b, SteeredLetter W (Move.tabToTab d b)) :
    ¬ SteeredStuck W := by
  obtain ⟨b, hl⟩ := hstanding
  intro hstuck
  exact hl.1 (hstuck _ hl)

/-- **THE ABSORPTION ROW** [PROVED, off FoundKit's banked census]:
at WF a face-up x already sits at or below its own rung — the
x-side clause of the package is derivable, the dead weight the
slab refinement priced.  The mechanism: below its own rung, the
founded prefix would NAME x (`mem_found_of_rung`), and zone
exclusivity (`mem_faceUp_only`) bars exactly that read. -/
theorem slab_of_faceUp {st : State} (hwf : st.WF) {x : Card}
    (hfu : ∃ a, x ∈ (st.piles a).faceUp) :
    rungAt st x.suit ≤ x.rank.toIdx := by
  obtain ⟨a, hmem⟩ := hfu
  rcases Nat.lt_or_ge x.rank.toIdx (st.foundHeight x.suit) with hlt | hle
  · exact absurd (FoundKit.mem_found_of_rung hwf hlt)
      ((mem_faceUp_only hwf hmem).2.2.2.2 x.suit)
  · exact hle

/-- The old inline package re-plates into the corrected premise,
one assembly. -/
theorem BelowForkDeployed_of_hbelow {s F : State} {X : Card} {π : List Move}
    (_hr : s.run π = some F) (_hw : ForkWitness F X)
    (hrg₁ : rungAt s X.suit ≤ X.rank.toIdx)
    (hrg₂ : rungAt s X.twin.suit ≤ X.rank.toIdx)
    (hfu₁ : ∃ a, X ∈ (s.piles a).faceUp)
    (hfu₂ : ∃ b, X.twin ∈ (s.piles b).faceUp) :
    BelowForkDeployed s X := ⟨hrg₂, hrg₁, hfu₁, hfu₂⟩

/-- The per-world starvation bar, P3b as a lemma: under a standing
cover letter the member raise is unservable. -/
theorem member_raise_unservable_under_cover {st : State} {x d : Card} {b : Base}
    (hdh : d.rank.toIdx + 1 = x.rank.toIdx)
    (hcov : SteeredLetter st (Move.tabToTab d b)) :
    ¬ SteeredFirst st (Move.tabToFound x) :=
  fun hf => steered_preempt_cover hdh hcov hf

/-- **THE STANDING COVER, RUN-THREADED**: at every world along the
run the cover's seat letter stands steered-legal (the tail threads
through the run's own steps). -/
def CoverStandsAlong : State → List Move → Card → Prop
  | _, [], _ => True
  | st, m :: ρ, d =>
      (∃ b, SteeredLetter st (Move.tabToTab d b)) ∧
        ∀ s', State.step st m = some s' → CoverStandsAlong s' ρ d

/-- **THE NO-EAT LEDGER UNDER A STANDING COVER**: threaded by the
cover's standing, no pair-member raise is ever served — the
preemption bar applied head by head, the twin case riding the
twin-rank bridge. -/
theorem no_member_raise_underCover {s W : State} {ρ : List Move}
    (hrun : SteeredRun s ρ W) {x d : Card}
    (hdh : d.rank.toIdx + 1 = x.rank.toIdx)
    (hstand : CoverStandsAlong s ρ d) :
    ∀ m ∈ ρ, ∀ c, m = Move.tabToFound c → c ≠ x ∧ c ≠ x.twin := by
  induction hrun with
  | nil st => intro m hm _ _; cases hm
  | @cons st s₁ W₁ m₁ ρ₁ hletter hfirst hstep hrest ih =>
      obtain ⟨b, hcov⟩ := hstand.1
      intro m₀ hm₀ c₀ hmEq
      rcases List.mem_cons.1 hm₀ with rfl | htail
      · rw [hmEq] at hfirst
        by_cases hcx : c₀ = x
        · subst hcx
          exact absurd hfirst (steered_preempt_cover hdh hcov)
        · by_cases hct : c₀ = x.twin
          · subst hct
            have hdhT : d.rank.toIdx + 1 = x.twin.rank.toIdx := by
              rw [Card.twin_rank, hdh]
            exact absurd hfirst (steered_preempt_cover hdhT hcov)
          · exact ⟨hcx, hct⟩
      · exact ih (hstand.2 s₁ hstep) m₀ htail c₀ hmEq

/-- **THE STARVED PAIR SURVIVES** — the starvation arm's survival
conclusion, PROVED: along a cover-threaded steered run the pair
members are never founded — the no-eat ledger feeds the banked
persistence row, whose face-up clauses close at the terminal through
the zone-exclusivity read. -/
theorem starved_pair_survives {s W : State} (hwf : s.WF) {ρ : List Move}
    (hrun : SteeredRun s ρ W) {x d : Card}
    (hdh : d.rank.toIdx + 1 = x.rank.toIdx)
    (hdep : BelowForkDeployed s x)
    (hstand : CoverStandsAlong s ρ d) :
    x ∉ W.found x.suit ∧ x.twin ∉ W.found x.twin.suit := by
  obtain ⟨hslab, hrg₁, hfu₁, hfu₂⟩ := hdep
  have hrg₂ : rungAt s x.twin.suit ≤ x.twin.rank.toIdx := by
    rw [Card.twin_rank]
    exact hslab
  have hnoeat := no_member_raise_underCover hrun hdh hstand
  obtain ⟨p1, p2, -, -⟩ :=
    steered_pair_persists hwf hfu₁ hfu₂ hrg₁ hrg₂ hrun hnoeat
  have hwfW : W.WF := steered_run_wf hwf hrun
  obtain ⟨a₁, ha₁⟩ := p1
  obtain ⟨a₂, ha₂⟩ := p2
  exact ⟨fun hc => (mem_faceUp_only hwfW ha₁).2.2.2.2 x.suit hc,
    fun hc => (mem_faceUp_only hwfW ha₂).2.2.2.2 x.twin.suit hc⟩

/-- **THE CONSUMPTION ARM, FROZEN** [H]: from a deployed slab start
with the minimal reachability carrier (the raw fork play, kept as
the arm's data — the refutation's lesson recorded: this clause
buys no conclusion of its own), every steered trajectory ending
steered-stuck ends with the slab ELEVATED — the twin founded, the
covered side's rung past the witness rank.

ROUTE ( priced; the boarded shape decided below ):
1. THE DICHOTOMY SPLIT — if a cold cargo cover thread runs along
   ρ, the starvation arm already proved the pair survives; the
   oscillator evidence (rp2/loF2) closes the stuck half there: the
   cover-threaded tail never reaches steered-stuckness, so the
   stuck world has no standing cover along its tail.  [H-mini:
   the never-stuck-under-cover row — the alternation's
   maintenance, the rp2 certification pattern at statement grade.]
2. THE COVERLESS EAT — with no cover thread and the slab persisting
   into the arrival zone (the LowSlab transport rows, the
   conditional-preservation shapes), the joint/dead raise census at
   the zone serves the member raises (the loH1/loAŽ pattern) and
   the twin's founding elevates the slab.  [H: the arrival census
   at general WF worlds; the joint-instance leads already proved.]
3. THE ELEVATION READ — the founded twin's rung past the rank:
   `step_tabToFound_inv`'s rank arithmetic plus `Card.twin_rank`,
   the falsifier's `loA_T_elevated` shape at every grade.  [M]
-/
theorem steered_stuck_elevates {s : State} (hwf : s.WF) {x : Card}
    (hdep : BelowForkDeployed s x)
    (hreach : ∃ F π, s.run π = some F ∧ ForkWitness F x)
    {ρ : List Move} {W : State}
    (hrun : SteeredRun s ρ W) (hstuck : SteeredStuck W) :
    ¬ familyBelowFrontier W x := by
  sorry

/-- **THE BOARDED ELEVATION** — the refutation's own terminal, read
in the slab vocabulary: the falsifier's drain world has the twin
founded and the club rung past the witness rank — the consumption
arm's conclusion at its first certified instance. -/
theorem loA_T_elevated : ¬ familyBelowFrontier loA_T loA_s3 := by
  unfold familyBelowFrontier
  decide

/-! ### The §7 audit battery

`#print axioms` per fresh head: the package re-plating, the
absorption row (PROVED off FoundKit's census), the per-world bar,
the cover's own plug, the no-eat ledger and the survival row are
zero-sorry, riding the banked preemption bar P3b, the §5
persistence row and FoundKit's found-census; the consumption arm
carries the section's one priced sorry (route in its docstring);
the boarded elevation is decided. -/

#print axioms slab_of_faceUp
#print axioms not_stuck_of_coverStanding
#print axioms BelowForkDeployed_of_hbelow
#print axioms member_raise_unservable_under_cover
#print axioms no_member_raise_underCover
#print axioms starved_pair_survives
#print axioms steered_stuck_elevates
#print axioms loA_T_elevated
