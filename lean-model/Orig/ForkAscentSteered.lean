import Orig.ForkAscent
import Orig.ForkStateSB
import Orig.LowSlab
import Orig.FoundKit
import Orig.ForkDescent
import Orig.SlabEquiv

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
see §6's header.

REFUTED 2026-10-17 (§9 carries the certified fence): the stranded
counterexample rps — BelowForkDeployed with the slab intact and a
nine-leg raw fork play, whose EMPTY steered run ends at the start
itself, certified stuck.  This row keeps its sorry as the honest
witness (the fa2 precedent); the restatement menu (arrival clauses
rho-nonempty / parked-rung / steered-threaded reachability) is
recorded in §9's header and §8's census — the owner freezes. -/
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
/-! ## §8. THE ARRIVAL CENSUS — the zone competitor rows (promoted 2026-10-17)

The [H] step-2 content of `steered_stuck_elevates`'s route, landed at
its PROVABLE stratum (exit 0, 18 heads): thirteen of the fifteen
zone hazards die at banked rows — the past-rung kill, the off-board
kills, the burn bar (Classify's universal row IS in the cone), the
reveal-seat kill (§2c's own), and the REVEAL-WINDOW RAISE KILL: a
licensed reveal-raise is a BARE KING (rank 12), so it never
preempts a zone at r ≤ 12 — H3's delay hazard, closed.  Two hazards
are honestly OBSTRUCTED and carried as the zone statement's
premises: the third-suit live raises below r (the delay content,
decided per board) and the under-armed reversible cargo transfers
(rp2's cover class — their exclusion IS the coverless premise).

THE FROZEN ZONE STATEMENTS: `zone_serves_member` (the member's
letter AND rank-minimality off the two sweeps) and `zone_run_leg`
(the one-leg run) — the falsifier's per-board assembly at general
grade.  The priced `zone_pick_of_sweeps` [M, promote-tier] is the
pick-equality disjunction (the §4 scan glue, same-file at
promotion; the tie-break absorbed by the disjunction).

THE RESTATEMENT RECORD (the refuter-proof form the routes cite):
the consumption arm consumes its zone data FROM THE RUN — the
ARRIVAL CLAUSE (some prefix of the run lands a zone world: parking
equalities off the run's own rung arithmetic, the joint read, the
coverless sweeps) — never assumed at the start; without it every
stranded stuck world refutes the arm (two lanes converged on this
verdict independently: this census and the refuter-check).
Promoted verbatim from the certified scratch.
-/
/-! ## §1. The member-raise letter (known, cited) -/

/-- **THE HOT-JOINT LETTER** — a pair member whose vanilla license
and whose twin's vanilla license both stand, is a steered raise
letter: the twin gate's joint instance, the falsifier's leg pattern
at general grade. -/
theorem zone_letter_hot {st : State} {x : Card}
    (h1 : CanRaise st x) (h2 : CanRaise st x.twin) :
    SteeredLetter st (Move.tabToFound x) :=
  raiseGate_joint h1 h2

/-- **THE JOINT LETTER AT THE BOOL FACE** — the picker's grade of
the same instance, WF-free: with both vanilla probes true the gate
leg reads `(!S-probe || true) = true` regardless of the S-probe. -/
theorem steerRaiseB_true_of_joint {st : State} {c : Card}
    (h1 : canRaiseB st c = true) (h2 : canRaiseB st c.twin = true) :
    SteeredLetterB st (Move.tabToFound c) = true := by
  show steerRaiseB st c = true
  rw [steerRaiseB, h1, h2]
  simp

/-- **THE DEAD-INSTANCE GATE HALF** — after the first eat, the mate
raise passes the twin gate through the DEAD instance wherever the
eaten member's suit-rung has left its own index (the rung pin:
`canRaiseS_rung` forces `rungAt = the card's index`, so a rung that
has moved past pins its `CanRaiseS` dead).  The successor-side
transport (the step's rung arithmetic and the twin's preserved
license) is the §2c/§5 same-file content the promotion completes. -/
theorem dead_gate_of_rungPast {st : State} {x : Card}
    (hcr : CanRaise st x.twin) (hrung : rungAt st x.suit ≠ x.rank.toIdx) :
    SteeredLetter st (Move.tabToFound x.twin) := by
  refine raiseGate_dead hcr ?_
  intro hs
  rw [Card.twin_twin x] at hs
  exact hrung (canRaiseS_rung hs)

/-! ## §2. The raise-competitor census (hazard class a) -/

/-- **R1: THE PAST-RUNG KILL** — a card whose suit's rung does not
sit exactly at its index is never a raise letter (`nextUp` is the
decided index-rung equality; the rung above or below kills the
license's first conjunct outright). -/
theorem raise_pastRung_refused {st : State} {c : Card}
    (hne : st.foundHeight c.suit ≠ c.rank.toIdx) :
    ¬ SteeredLetter st (Move.tabToFound c) := by
  rintro ⟨hnu, -⟩
  have heq : c.rank.toIdx = st.foundHeight c.suit :=
    of_decide_eq_true hnu.1
  exact hne heq.symm

/-- **R2: THE OFF-BOARD KILL** — a card no pile holds (founded,
stocked, or hidden-only) is never a raise letter: the license's
top-existential contradicts the holding search's none read. -/
theorem raise_offboard_refused {st : State} (hwf : st.WF) {c : Card}
    (hh : st.pileHolding c = none) :
    ¬ SteeredLetter st (Move.tabToFound c) := by
  intro hL
  rcases hL.1 with ⟨-, a, htop, -⟩
  have hmem : c ∈ (st.piles a).faceUp := lastOf_mem (pileOfTop_top htop).2
  rw [(pileHolding_eq_some_iff hwf).2 hmem] at hh
  exact absurd hh (by simp)

/-- **R3: THE REVEAL-RAISE IS A KING** — a licensed raise that
EMPTIES its pile's face-up view (the chop read is empty — the
below-content vanishes) is a bare KING over a hidden-free pile: the
license's own seat-disjunct forces it.  So a pile-emptying raise is
rank-12 — the reveal window's RAISE arm (which has no reversibility
clause, the loyalty memo's H3) can never sit strictly below ANY
zone rank r ≤ 12: reveals through raises never delay an arrival. -/
theorem raise_reveal_is_king {st : State} {c : Card} {a : Anchor}
    (hL : SteeredLetter st (Move.tabToFound c))
    (htop : st.pileOfTop c = some a)
    (hchop : chop (st.piles a).faceUp = []) :
    c.rank = Rank.king ∧ (st.piles a).hidden = [] := by
  rcases hL.1 with ⟨-, w, hw, hdj⟩
  have hwa : w = a := Option.some.inj (hw.symm.trans htop)
  rw [hwa] at hdj
  rcases hdj with hne | ⟨hhid, hking⟩
  · exact absurd hchop hne
  · exact ⟨hking, hhid⟩

/-- The index form of R3: a pile-emptying licensed raise ranks 12. -/
theorem raise_reveal_rank12 {st : State} {c : Card} {a : Anchor}
    (hL : SteeredLetter st (Move.tabToFound c))
    (htop : st.pileOfTop c = some a)
    (hchop : chop (st.piles a).faceUp = []) :
    c.rank.toIdx = 12 := by
  obtain ⟨hking, -⟩ := raise_reveal_is_king hL htop hchop
  rw [hking]
  rfl

/-- **R3's ZONE COROLLARY** — a pile-emptying licensed raise never
sits below a zone rank r ≤ 12. -/
theorem no_reveal_raise_below {st : State} {c : Card} {a : Anchor}
    {r : Nat}
    (hL : SteeredLetter st (Move.tabToFound c))
    (htop : st.pileOfTop c = some a)
    (hchop : chop (st.piles a).faceUp = [])
    (hzone : r ≤ 12) : ¬ (c.rank.toIdx < r) := by
  intro hlt
  have h12 : c.rank.toIdx = 12 := raise_reveal_rank12 hL htop hchop
  omega

/-- The Bool-sweep-to-letter bridge at general grade (the falsifier's
`lowRaise_dead` pattern, promoted to a standalone row). -/
theorem lowraise_refused_of_B {st : State} {r : Nat}
    (h : ∀ c, c.rank.toIdx < r → canRaiseB st c = false) :
    ∀ c, c.rank.toIdx < r → ¬ SteeredLetter st (Move.tabToFound c) := by
  intro c hlt hL
  have hf : canRaiseB st c = false := h c hlt
  rw [(canRaiseB_true_iff).2 hL.1] at hf
  exact absurd hf (by simp)

/-- **R4: THE COMPOSED COLD-OR-ABSENT SWEEP** — the minimal
generalization the third-suit census supports TODAY: at a world
where every card below the zone rank is either COLD-OR-PAST (its
suit's rung is not at its index) or ABSENT (no pile holds it), no
raise letter stands below the zone.  This is what the climb's
order-content MEANS at the arrived zone — the spine served
everything hot below r on its way in.  The REVEAL-TRANSPORT content
(a hidden card surfaced below r BEFORE the zone) is the climb-side
remainder the sweep's premise carries, priced [H] at the run tier. -/
theorem lowraise_cold_or_absent {st : State} (hwf : st.WF) {r : Nat}
    (h : ∀ c, c.rank.toIdx < r →
      st.nextUp c = false ∨ st.pileHolding c = none) :
    ∀ c, c.rank.toIdx < r → ¬ SteeredLetter st (Move.tabToFound c) := by
  have hB : ∀ c, c.rank.toIdx < r → canRaiseB st c = false := by
    intro c hlt
    rcases h c hlt with hnu | hhold
    · rw [canRaiseB, hnu]
      simp
    · have hpot : st.pileOfTop c = none := by
        cases hpt : st.pileOfTop c with
        | none => rfl
        | some k =>
            have hmem : c ∈ (st.piles k).faceUp :=
              lastOf_mem (pileOfTop_top hpt).2
            rw [(pileHolding_eq_some_iff hwf).2 hmem] at hhold
            exact absurd hhold (by simp)
      rw [canRaiseB, hpot]
      simp
  exact lowraise_refused_of_B hB

/-! ## §3. The seat-competitor census (hazard class b) -/

/-- **S1: THE OFF-BOARD MOVER KILL** — a card no pile holds has no
firing seat at any base: the raw step equation reads the held-proof
`none`. -/
theorem seat_offboard_refused {st : State} {c : Card}
    (hhold : st.pileHolding c = none) (b : Base) :
    ¬ SteeredLetter st (Move.tabToTab c b) := by
  intro hL
  have hnone : State.step st (Move.tabToTab c b) = none := by
    rw [step_tabToTab_eq, hhold]
  exact hL.1 hnone

/-- **S2: THE MOBILE-NONJOINT KILL** — a mobile pair that is not
JOINT NOW is never seated, at any base: the leaf's own §1 joint-clause
row, at general grade (the exposed cold stool pairs are exactly this
shape — the falsifier's stoolSeat class). -/
theorem seat_mobile_nonjoint_refused {st : State} {c : Card}
    (hmob : MobileTwin st c)
    (hn : ¬ (CanRaise st c ∧ CanRaise st c.twin)) (b : Base) :
    ¬ SteeredLetter st (Move.tabToTab c b) :=
  seatGate_refuses_nonjoint hmob hn

/-- **S3: THE REVEAL-SEAT KILL** — a seating leg whose departure
would leave the whole face-up over a nonempty hidden deck is never a
steered letter: the leaf's own §2c journey-never-reveal row.  The
reveal window's SEAT arm dies here; the RAISE arm is R3 above
(king-only). -/
theorem seat_reveal_refused {st s' : State} {c : Card} {b : Base}
    {a : Anchor}
    (hstep : State.step st (Move.tabToTab c b) = some s')
    (hh : st.pileHolding c = some a)
    (hbel : below c (st.piles a).faceUp = [])
    (hhne : (st.piles a).hidden ≠ []) :
    ¬ SteeredLetter st (Move.tabToTab c b) :=
  steered_seat_refuses_reveal hstep hh hbel hhne

/-- **S4: THE BURN-MODE BAR** — a bare non-king whose whole visible
run departs over a hidden-free pile is a COMMITMENT, not a letter:
the emptied seat obeys the receive-only-kings discipline, so the leg
is irreversible (`tabToTab_irreversible_of_bare_nonking`, which IS
in the import cone — Classify sits under MacroInternal — no
ForklessCeiling row needed) and the seat gate's reversibility
conjunct dies (Fate's commitment-refutes-every-witness row). -/
theorem seat_burn_refused {st : State} {c : Card} {b : Base}
    {a : Anchor} {s₁ : State}
    (hstep : State.step st (Move.tabToTab c b) = some s₁)
    (hh : st.pileHolding c = some a)
    (hpre : below c (st.piles a).faceUp = [])
    (hhidden : (st.piles a).hidden = [])
    (hfr : fromCard c (st.piles a).faceUp ≠ [])
    (hking : c.rank ≠ Rank.king) :
    ¬ SteeredLetter st (Move.tabToTab c b) := by
  intro hL
  exact not_reversibleAtW_of_irreversibleAt
    (tabToTab_irreversible_of_bare_nonking hstep hh hpre hhidden hfr hking)
    hL.2.1

/-- The grade-coincidence note: a genuine seat letter forces the
picker's Bool face true (fires and joint conjuncts re-read), so a
decided `steerSeatB = false` per board kills the whole Prop letter
too — the sweep premises of §4 are one decide per (card, base) pair. -/
theorem steerSeatB_true_of_seatLetter {st : State} {c : Card} {b : Base}
    (hL : SteeredLetter st (Move.tabToTab c b)) :
    steerSeatB st c b = true :=
  (steerSeatB_true_iff st c b).2 ⟨hL.1, hL.2.2⟩

/-! ## §4. The zone-statement freeze -/

/-- The sweep assembler, general grade (the leaf's private
`steeredFirst_of_sweeps` pattern at zone shape). -/
private theorem zoneFirst_of_sweeps (st : State) (m : Move) (r : Nat)
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

/-- **THE ZONE SERVES THE MEMBER** (the frozen per-zone row, PROVABLE
TODAY): at a zone world — the pair joint at the Bool probes, no
raise probe live below the pair's rank, no seat letter below it —
the member's raise is BOTH a steered letter AND rank-minimal: the
head any steered trajectory through this zone must serve.  The
premises are ZONE-WORLD reads, decidable-applied per board (the
sweeps are the coverless condition; the joint read is the parking's
own table).  THE [H] CONTENT the row prices is exactly the
premise-closing: the arrival (the run actually entering such a
zone) and the sweeps' transport from the climb. -/
theorem zone_serves_member {st : State} {x : Card}
    (hjoint : canRaiseB st x = true ∧ canRaiseB st x.twin = true)
    (hra : ∀ c, c.rank.toIdx < x.rank.toIdx → canRaiseB st c = false)
    (hsa : ∀ (c : Card), c.rank.toIdx < x.rank.toIdx →
      ∀ (b : Base), ¬ SteeredLetter st (Move.tabToTab c b)) :
    SteeredLetter st (Move.tabToFound x) ∧
      SteeredFirst st (Move.tabToFound x) := by
  have hletter : SteeredLetter st (Move.tabToFound x) :=
    raiseGate_joint ((canRaiseB_true_iff).1 hjoint.1)
      ((canRaiseB_true_iff).1 hjoint.2)
  exact ⟨hletter, zoneFirst_of_sweeps st _ x.rank.toIdx rfl
    (lowraise_refused_of_B hra) hsa⟩

/-- **THE ZONE'S RUN LEG** — the service assembled into the
trajectory's own shape: the member's letter, its rank-minimality,
and its firing step compose one lawful steered run leg.  This is the
consumption arm's per-zone eat, certified. -/
theorem zone_run_leg {st s' : State} {x : Card}
    (hL : SteeredLetter st (Move.tabToFound x))
    (hF : SteeredFirst st (Move.tabToFound x))
    (hstep : State.step st (Move.tabToFound x) = some s') :
    SteeredRun st [Move.tabToFound x] s' :=
  SteeredRun.cons hL hF hstep (SteeredRun.nil s')

/-- **THE PICK-EQUALITY DISJUNCTION** (PRICED [M] at the promote
tier — the row is PROVABLE the day this draft merges into the leaf,
where the §4 stepper kit is same-file):

At a zone world with the pair joint at the Bool probes, every
non-pair raise probe dead below AND at the pair's rank, and every
seat probe dead below AND at the rank off the pair, the §4
deterministic picker returns exactly one of the two member raises.

ROUTE (the scan glue, all pieces named):
1. THE JOINT BOOL LETTERS: `steerRaiseB_true_of_joint` (in-file)
   puts both members' raise probes true at `letterRank = r`.
2. THE BELOW-SCAN EMPTINESS: `hrlo`/`hslo` empty every rank block
   below r (`rankPick st j = none` for `j < r`; per block the raise
   column reads `canRaiseB` through `steerRaiseB`'s first conjunct,
   the seat column reads `steerSeatB` directly).
3. THE RANK-STOP: the scan chain promotes — `firstRankUpTo st 13
   = some (r, m₀)`: over the none-prefix (step 2, via the §4 kit's
   `firstRankUpTo_none_complete`/`takeRank_none_none`) and the
   r-yield (`takeRank_none_rank` over `rankPick st r ≠ none`),
   by induction on `13 − r` with `takeRank_some_inner` carrying.
4. THE PICK'S MEMBERSHIP: `SteeredLetterB st m₀ = true`
   (`firstWhere_sound`) and `m₀ ∈ steeredRankBlock r`; the §4
   kit's `block_letters` splits m₀ into a raise or a seat at rank
   r; raises precede seats in the block, and both members'_raise
   probes are true, so the first true element is a RAISE.
5. THE PAIR READ: `hrank` sweeps every non-pair raise probe at r,
   `hsrk` every non-pair seat probe — the returned raise is x's or
   the twin's.  WHICH member is the universe tie-break (R3's priced
   refinement); the DISJUNCTION is the honest form the evidence
   supports today.

The premise-set is necessary and honest: a genuine third-suit raise
at or below r (rank-r) and the under-armed reversible cargo
transfer (the rp2 cover class) are REAL letters — the sweeps are
per-board decide rows, never general kills. -/
theorem zone_pick_of_sweeps {st : State} {x : Card}
    (hjoint : canRaiseB st x = true ∧ canRaiseB st x.twin = true)
    (hrlo : ∀ c, c.rank.toIdx < x.rank.toIdx → canRaiseB st c = false)
    (hrank : ∀ c, c.rank.toIdx = x.rank.toIdx → c ≠ x → c ≠ x.twin →
      canRaiseB st c = false)
    (hslo : ∀ (c : Card), c.rank.toIdx < x.rank.toIdx →
      ∀ (b : Base), steerSeatB st c b = false)
    (hsrk : ∀ (c : Card), c.rank.toIdx = x.rank.toIdx → c ≠ x → c ≠ x.twin →
      ∀ (b : Base), steerSeatB st c b = false) :
    steeredPick st = some (Move.tabToFound x) ∨
      steeredPick st = some (Move.tabToFound x.twin) := by
  sorry

/-! ## §5. THE CENSUS MEMO AND THE STRANDED-WORLD NOTE

THE CENSUS TABLE (what the decomposition found):

RAISE SIDE (class a):
  R1 past-rung kill ................................. PROVABLE (nextUp)
  R2 off-board kill ............................... PROVABLE (holding iff)
  R3 the reveal-raise is a bare king (rank 12) ..... PROVABLE — the
      reveal window's RAISE arm (no reversibility clause, the
      loyalty memo's H3) is KING-ONLY through the license's own
      seat-disjunct: it never preempts any zone r ≤ 12.  The reveal
      hazard lives on the SEAT arm only — killed by S3.
  R4 cold-or-absent composed sweep ............... PROVABLE (the
      zone-side generalization the climb order-content supports)
  R5 the RAW third-suit live raise below r ....... OBSTRUCTED as a
      general kill — the delay hazard is real; carried as `hrlo`,
      decided per board.

SEAT SIDE (class b):
  S1 off-board mover kill .......................... PROVABLE
  S2 mobile-nonjoint kill (cold stool pairs) ....... PROVABLE (the
      leaf's §1 own joint-clause row; reaches the rp1 bar's class)
  S3 reveal-seat kill (journey-never-reveal) ....... PROVABLE (the
      leaf's §2c own row — the reveal window's seat arm)
  S4 burn-mode bar (bare non-king whole departure) . PROVABLE — the
      import question RESOLVES: the irreversibility row is in the
      cone (Classify under MacroInternal) + Fate's commitment row;
      no ForklessCeiling topped-counter row is needed.  The census
      memo's S1 OPEN class (the under-armed reversible transfers)
      remains exactly the COVERLESS premise:
  S5 under-armed reversible cargo transfers ....... OBSTRUCTED as a
      kill — the repair probe certified these letters REAL (rp2's
      cycle: the cover seats fire reversibly forever); they are the
      starvation arm's own mechanism, swept per board (`hslo`/
      `hsrk`), never "killed".

THE STRANDED-WORLD NOTE (the refuter-check companion): a pair can
SURVIVE to a steered-stuck terminal WITHOUT ever arriving at a zone
— stranded mid-board, un-parked, unfounded: at such a world
`familyBelowFrontier` can stand with the pair intact, and the
elevation conclusion would be FALSE there.  The zone rows above are
already refuter-proof AS STATED (their premises are zone-world
reads, not start-world reads), but the CONSUMPTION ARM's step 2 may
eat them only with the premises consumed FROM THE RUN.  The
restatement the evidence recommends for `steered_stuck_elevates`:

* (i) THE ARRIVAL CLAUSE: some prefix of ρ lands a ZONE world W₁ —
  the parking equalities (both family rungs AT the pair's rank; off
  the run's own rung arithmetic, `steered_rung_mono` and the climb
  legs), the joint read (the §5 persistence's face-up clauses plus
  the slab), and the coverless sweeps (per the §7 dichotomy: a
  standing cover thread forces the never-stuck read
  — `not_stuck_of_coverStanding` — so a STUCK terminal's tail is
  coverless).  [H: the arrival is the R1 order-content itself]
* (ii) THE SERVE-AND-TAIL: `zone_serves_member` + `zone_run_leg`
  certify the member's founding leg out of W₁; the dead instance
  (`dead_gate_of_rungPast` after the step's own rung arithmetic)
  serves the twin next; the §5 persistence carries the face-up
  census forward, and the elevation read (`loA_T_elevated`'s
  arithmetic at general grade) closes the conclusion.  [M]

Without (i) every stranded stuck world refutes the arm; with it,
the zone data rides the trajectory — which is what a steered-stuck
CONSUMPTION conclusion may consume. -/

/-! ## §6. The audit battery -/

#print axioms zone_letter_hot
#print axioms steerRaiseB_true_of_joint
#print axioms dead_gate_of_rungPast
#print axioms raise_pastRung_refused
#print axioms raise_offboard_refused
#print axioms raise_reveal_is_king
#print axioms raise_reveal_rank12
#print axioms no_reveal_raise_below
#print axioms lowraise_refused_of_B
#print axioms lowraise_cold_or_absent
#print axioms seat_offboard_refused
#print axioms seat_mobile_nonjoint_refused
#print axioms seat_reveal_refused
#print axioms seat_burn_refused
#print axioms steerSeatB_true_of_seatLetter
#print axioms zone_serves_member
#print axioms zone_run_leg
#print axioms zone_pick_of_sweeps

/- APPEND-MARKER -/
/-! ## §9. THE STRANDED FALSIFIER AND THE OSCILLATOR — promoted (2026-10-17)

Promoted verbatim from the certified scratch (exit 0, 32 heads).
Two verdicts:

THE CONSUMPTION ARM IS REFUTED AS FROZEN —
`steered_stuck_elevates_refuted`: the stranded world rps (WF,
BelowForkDeployed — the slab reads intact: twin rung strictly below
the pair's rank — pair face-up over the red sixes) whose EMPTY
steered run is a certified SteeredRun to a certified SteeredStuck
terminal (the start itself: every raise licensable-read dead, the
three mobile-cold pairs at the joint clause, the lone cold cover at
the journey-never-reveal bar), while a NINE-LEG RAW play — climbing
both family wells reveal-by-reveal and seating the cold cover —
manifests ForkWitness rps_F loB_s5.  The arm's conclusion dies at
W = s.  THE RESTATEMENT MENU (recorded; the owner freezes):
(a) rho-nonemptiness, (b) the parked-rung arrival clause folded
into the premises (the §8 census's shape: the zone data consumed
FROM THE RUN), or (c) the reachability carrier upgraded to a
steered-threaded form.  §7 keeps its sorry as the honest witness.

THE OSCILLATOR MAINTENANCE, FIRST INSTANTIATIONS —
`cover_stands_after_seat_board`/`rwA_stands_after_seat` (the mirror
letter standing after every fired cover seat: fires off the banked
step equation, reversible by the one-move return, joint vacuous by
cargo), consumed through the PROVED `not_stuck_of_coverStanding`
into `rwA_neverStuck`/`rwB_neverStuck` — the [H-mini] route-step-1
read at its first certified boards; `mirror_fit_of_cover` PROVED at
full generality (the two-top fit: the tableau cannot tell the pair's
tops apart — one banked rewrite); the general
`cover_stands_after_seat` priced with its three-step splice-chase
route (fires/return/cargo-persistence — the R3w sufficiency shape
at oscillator grain).
-/
/-! ## §0. The kit -/

private def loB_C (s : Suit) (r : Rank) : Card := ⟨s, r⟩
private def loB_T (s : Suit) (n : Nat) : List Card := s.upCards.take n

/-! ## §1. Deliverable 1 — the stranded world -/

private def loB_s5 : Card := loB_C .spade .five
private def loB_c5 : Card := loB_C .club .five
private def loB_h6 : Card := loB_C .heart .six
private def loB_d6 : Card := loB_C .diamond .six
private def loB_sA : Card := loB_C .spade .ace
private def loB_cA : Card := loB_C .club .ace
private def loB_h4 : Card := loB_C .heart .four
private def loB_s2 : Card := loB_C .spade .two
private def loB_s3 : Card := loB_C .spade .three
private def loB_s4 : Card := loB_C .spade .four
private def loB_c2 : Card := loB_C .club .two
private def loB_c3 : Card := loB_C .club .three
private def loB_c4 : Card := loB_C .club .four
private def loB_hA : Card := loB_C .heart .ace
private def loB_dA : Card := loB_C .diamond .ace
private def loB_dK : Card := loB_C .diamond .king

/-- **THE STRANDED WORLD** — the consumption arm's hazard, boarded:
the black fives pair seated over the red sixes (each member topping
its own pile, both family rungs strictly below the pair's rank), the
four ACE climb seeds bare over their hidden wells (never
licensable, always raw-foundable), the cold cover h4 bare over the
hidden king.  All other 36 cards stocked; foundations empty. -/
private def rps : State where
  found := fun _ => []
  piles := fun a => match a with
    | .p0 => ⟨[loB_hA], [loB_h6, loB_s5]⟩
    | .p1 => ⟨[loB_dA], [loB_d6, loB_c5]⟩
    | .p4 => ⟨[loB_s2, loB_s3, loB_s4], [loB_sA]⟩
    | .p5 => ⟨[loB_c2, loB_c3, loB_c4], [loB_cA]⟩
    | .p6 => ⟨[loB_dK], [loB_h4]⟩
    | _ => ⟨[], []⟩
  stock :=
    [loB_C .spade .six, loB_C .spade .seven, loB_C .spade .eight,
     loB_C .spade .nine, loB_C .spade .ten, loB_C .spade .jack,
     loB_C .spade .queen, loB_C .spade .king,
     loB_C .heart .two, loB_C .heart .three, loB_C .heart .five,
     loB_C .heart .seven, loB_C .heart .eight, loB_C .heart .nine,
     loB_C .heart .ten, loB_C .heart .jack, loB_C .heart .queen,
     loB_C .heart .king,
     loB_C .diamond .two, loB_C .diamond .three, loB_C .diamond .four,
     loB_C .diamond .five, loB_C .diamond .seven, loB_C .diamond .eight,
     loB_C .diamond .nine, loB_C .diamond .ten, loB_C .diamond .jack,
     loB_C .diamond .queen,
     loB_C .club .six, loB_C .club .seven, loB_C .club .eight,
     loB_C .club .nine, loB_C .club .ten, loB_C .club .jack,
     loB_C .club .queen, loB_C .club .king]
  waste := []
  drawStep := 1

theorem rps_wf : rps.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    cases s <;> exact ⟨0, rfl⟩
  · intro a
    cases a <;> decide
  · intro c _
    rcases c with ⟨s, r⟩
    cases s <;> cases r <;> decide
  · decide

/-- The stranded slab read: the twin-side rung sits strictly below
the pair's rank — `familyBelowFrontier` holds at the world itself. -/
theorem rps_slab : familyBelowFrontier rps loB_s5 := by
  unfold familyBelowFrontier
  decide

/-- **THE BELOW-FRONTIER PARCEL** at the stranded world: the twin
slab, the x-side rung below the rank, the pair deployed face-up. -/
theorem rps_bfd : BelowForkDeployed rps loB_s5 :=
  ⟨rps_slab, by decide, ⟨Anchor.p0, by decide⟩, ⟨Anchor.p1, by decide⟩⟩

/-! ### §1b. The stuck certification -/

/-- Nothing at the stranded world is vanilla-licensable — the bare
aces fail the seat clause (bare, non-king, over nonempty hidden),
everything else is cold, buried, or stocked. -/
private theorem rps_noraise : ∀ c, canRaiseB rps c = false := by
  intro c
  rcases c with ⟨s, r'⟩
  cases s <;> cases r' <;> decide

/-- The stool-seat kill (the falsifier's row, verbatim): a mobile
nonjoint mover seats nowhere, whichever base it aims at. -/
private theorem rps_stool_refused (c : Card)
    (hmob : MobileTwin rps c)
    (hn : ¬ (CanRaise rps c ∧ CanRaise rps c.twin)) :
    ∀ (b : Base), ¬ SteeredLetter rps (Move.tabToTab c b) :=
  fun _ hL => seatGate_refuses_nonjoint hmob hn hL

/-- The off-board mover kill (the falsifier's row, verbatim). -/
private theorem rps_offBoard_refused (c : Card)
    (hhold : rps.pileHolding c = none) (b : Base) :
    ¬ SteeredLetter rps (Move.tabToTab c b) := by
  intro hL
  have hnone : State.step rps (Move.tabToTab c b) = none := by
    rw [step_tabToTab_eq, hhold]
  have hgate : seatGate rps c b := hL
  rcases hgate with ⟨hfired, -, -⟩
  exact hfired hnone

/-- The THREE mobile-cold pairs of the stranded world (s5/c5 seated,
the bare aces, the buried sixes) — mobile, never joint. -/
private theorem rps_mob_s5 : MobileTwin rps loB_s5 :=
  ⟨⟨Anchor.p0, by decide⟩, by decide, ⟨Anchor.p1, by decide⟩, by decide⟩

private theorem rps_nonjoint_s5 : ¬ (CanRaise rps loB_s5 ∧ CanRaise rps loB_s5.twin) := by
  rintro ⟨hc, -⟩
  have hb : canRaiseB rps loB_s5 = true := (canRaiseB_true_iff).2 hc
  rw [rps_noraise loB_s5] at hb
  exact absurd hb (by simp)

private theorem rps_mob_c5 : MobileTwin rps loB_c5 :=
  ⟨⟨Anchor.p1, by decide⟩, by decide, ⟨Anchor.p0, by decide⟩, by decide⟩

private theorem rps_nonjoint_c5 : ¬ (CanRaise rps loB_c5 ∧ CanRaise rps loB_c5.twin) := by
  rintro ⟨hc, -⟩
  have hb : canRaiseB rps loB_c5 = true := (canRaiseB_true_iff).2 hc
  rw [rps_noraise loB_c5] at hb
  exact absurd hb (by simp)

private theorem rps_mob_sA : MobileTwin rps loB_sA :=
  ⟨⟨Anchor.p4, by decide⟩, by decide, ⟨Anchor.p5, by decide⟩, by decide⟩

private theorem rps_nonjoint_sA : ¬ (CanRaise rps loB_sA ∧ CanRaise rps loB_sA.twin) := by
  rintro ⟨hc, -⟩
  have hb : canRaiseB rps loB_sA = true := (canRaiseB_true_iff).2 hc
  rw [rps_noraise loB_sA] at hb
  exact absurd hb (by simp)

private theorem rps_mob_cA : MobileTwin rps loB_cA :=
  ⟨⟨Anchor.p5, by decide⟩, by decide, ⟨Anchor.p4, by decide⟩, by decide⟩

private theorem rps_nonjoint_cA : ¬ (CanRaise rps loB_cA ∧ CanRaise rps loB_cA.twin) := by
  rintro ⟨hc, -⟩
  have hb : canRaiseB rps loB_cA = true := (canRaiseB_true_iff).2 hc
  rw [rps_noraise loB_cA] at hb
  exact absurd hb (by simp)

private theorem rps_mob_h6 : MobileTwin rps loB_h6 :=
  ⟨⟨Anchor.p0, by decide⟩, by decide, ⟨Anchor.p1, by decide⟩, by decide⟩

private theorem rps_nonjoint_h6 : ¬ (CanRaise rps loB_h6 ∧ CanRaise rps loB_h6.twin) := by
  rintro ⟨hc, -⟩
  have hb : canRaiseB rps loB_h6 = true := (canRaiseB_true_iff).2 hc
  rw [rps_noraise loB_h6] at hb
  exact absurd hb (by simp)

private theorem rps_mob_d6 : MobileTwin rps loB_d6 :=
  ⟨⟨Anchor.p1, by decide⟩, by decide, ⟨Anchor.p0, by decide⟩, by decide⟩

private theorem rps_nonjoint_d6 : ¬ (CanRaise rps loB_d6 ∧ CanRaise rps loB_d6.twin) := by
  rintro ⟨hc, -⟩
  have hb : canRaiseB rps loB_d6 = true := (canRaiseB_true_iff).2 hc
  rw [rps_noraise loB_d6] at hb
  exact absurd hb (by simp)

/-- **THE BARE-OVER-HIDDEN COVER KILL** — the lone fired-seat class
of the stranded world: the cold cover h4 (fitting both members'
tops) has no base to refuse by, so the kill rides the banked
journey-never-reveal bar — every fired seat of the cover is a bare
peel over a nonempty hidden deck, never reversible, never a letter. -/
private theorem rps_h4_refused : ∀ (b : Base),
    ¬ SteeredLetter rps (Move.tabToTab loB_h4 b) := by
  intro b hL
  obtain ⟨s', hs'⟩ := option_some_of_ne_none hL.1
  exact absurd hL.2.1
    (journey_tabToTab_never_reveal hs'
      (by decide : rps.pileHolding loB_h4 = some Anchor.p6)
      (by decide : below loB_h4 (rps.piles Anchor.p6).faceUp = [])
      (by decide : (rps.piles Anchor.p6).hidden ≠ []))

/-- No seat letter stands at the stranded world: every mover is off
board, or one of the three mobile-cold pairs (joint clause), or the
cover itself (reveal-barred). -/
private theorem rps_noseat : ∀ (c : Card) (b : Base),
    ¬ SteeredLetter rps (Move.tabToTab c b) := by
  intro c b hL
  by_cases hmem : rps.pileHolding c = none
  · exact rps_offBoard_refused c hmem b hL
  · rcases c with ⟨s, r'⟩
    cases s <;> cases r' <;> first
      | exact absurd hmem (by decide)
      | exact rps_stool_refused loB_s5 rps_mob_s5 rps_nonjoint_s5 b hL
      | exact rps_stool_refused loB_c5 rps_mob_c5 rps_nonjoint_c5 b hL
      | exact rps_stool_refused loB_sA rps_mob_sA rps_nonjoint_sA b hL
      | exact rps_stool_refused loB_cA rps_mob_cA rps_nonjoint_cA b hL
      | exact rps_stool_refused loB_h6 rps_mob_h6 rps_nonjoint_h6 b hL
      | exact rps_stool_refused loB_d6 rps_mob_d6 rps_nonjoint_d6 b hL
      | exact rps_h4_refused b hL

/-- **THE STRANDED WORLD IS STEERED-STUCK, CERTIFIED** — no raise
letter (nothing licensable), no seat letter (the cell census), no
other arm a letter at all. -/
theorem rps_stuck : SteeredStuck rps := by
  intro m hL
  cases m with
  | draw => exact absurd hL (fun h => h)
  | wasteToFound c => exact absurd hL (fun h => h)
  | wasteToTab c b => exact absurd hL (fun h => h)
  | foundToTab c b => exact absurd hL (fun h => h)
  | tabToFound c =>
      have hf : canRaiseB rps c = false := rps_noraise c
      rw [(canRaiseB_true_iff).2 hL.1] at hf
      exact absurd hf (by simp)
  | tabToTab c b => exact absurd hL (rps_noseat c b)

/-! ### §1c. The raw fork-manifesting play — nine spelled legs -/

/-- After raw leg 1 (found the spade ace off its well; the revealed
spade deuce tops). -/
private def rps_1 : State :=
  { rps.setFound Suit.spade (rps.found Suit.spade ++ [loB_sA]) with
    piles := fun a' => if a' = Anchor.p4 then
        Pile.afterRunRemoved (rps.piles Anchor.p4)
          (chop (rps.piles Anchor.p4).faceUp)
      else rps.piles a' }

/-- After raw leg 2 (the revealed spade deuce found). -/
private def rps_2 : State :=
  { rps_1.setFound Suit.spade (rps_1.found Suit.spade ++ [loB_s2]) with
    piles := fun a' => if a' = Anchor.p4 then
        Pile.afterRunRemoved (rps_1.piles Anchor.p4)
          (chop (rps_1.piles Anchor.p4).faceUp)
      else rps_1.piles a' }

/-- After raw leg 3. -/
private def rps_3 : State :=
  { rps_2.setFound Suit.spade (rps_2.found Suit.spade ++ [loB_s3]) with
    piles := fun a' => if a' = Anchor.p4 then
        Pile.afterRunRemoved (rps_2.piles Anchor.p4)
          (chop (rps_2.piles Anchor.p4).faceUp)
      else rps_2.piles a' }

/-- After raw leg 4: the spade ring parked at the pair's rank; the
spade well burned empty. -/
private def rps_4 : State :=
  { rps_3.setFound Suit.spade (rps_3.found Suit.spade ++ [loB_s4]) with
    piles := fun a' => if a' = Anchor.p4 then
        Pile.afterRunRemoved (rps_3.piles Anchor.p4)
          (chop (rps_3.piles Anchor.p4).faceUp)
      else rps_3.piles a' }

/-- After raw leg 5 (the club ace off its mirror well). -/
private def rps_5 : State :=
  { rps_4.setFound Suit.club (rps_4.found Suit.club ++ [loB_cA]) with
    piles := fun a' => if a' = Anchor.p5 then
        Pile.afterRunRemoved (rps_4.piles Anchor.p5)
          (chop (rps_4.piles Anchor.p5).faceUp)
      else rps_4.piles a' }

/-- After raw leg 6. -/
private def rps_6 : State :=
  { rps_5.setFound Suit.club (rps_5.found Suit.club ++ [loB_c2]) with
    piles := fun a' => if a' = Anchor.p5 then
        Pile.afterRunRemoved (rps_5.piles Anchor.p5)
          (chop (rps_5.piles Anchor.p5).faceUp)
      else rps_5.piles a' }

/-- After raw leg 7. -/
private def rps_7 : State :=
  { rps_6.setFound Suit.club (rps_6.found Suit.club ++ [loB_c3]) with
    piles := fun a' => if a' = Anchor.p5 then
        Pile.afterRunRemoved (rps_6.piles Anchor.p5)
          (chop (rps_6.piles Anchor.p5).faceUp)
      else rps_6.piles a' }

/-- After raw leg 8: both family rings parked at the pair's rank;
both wells burned empty. -/
private def rps_8 : State :=
  { rps_7.setFound Suit.club (rps_7.found Suit.club ++ [loB_c4]) with
    piles := fun a' => if a' = Anchor.p5 then
        Pile.afterRunRemoved (rps_7.piles Anchor.p5)
          (chop (rps_7.piles Anchor.p5).faceUp)
      else rps_7.piles a' }

/-- **THE FORK-MANIFESTING LANDING** — after raw leg 9 (the cold
cover seated onto the club five's top): the covered-twin fork shape
at the pair's own rank. -/
private def rps_F : State :=
  (rps_8.setPile Anchor.p6
      (Pile.afterRunRemoved (rps_8.piles Anchor.p6)
        (below loB_h4 (rps_8.piles Anchor.p6).faceUp))).putRun
    [loB_h4] (Sum.inr loB_c5)

#eval forkStateSB rps_F
#eval forkStateSB rps

theorem rps_leg1 : State.step rps (Move.tabToFound loB_sA) = some rps_1 := by
  rw [step_tabToFound_splice
      (by decide : rps.nextUp loB_sA = true)
      (by decide : rps.pileOfTop loB_sA = some Anchor.p4)]
  rfl

theorem rps_leg2 : State.step rps_1 (Move.tabToFound loB_s2) = some rps_2 := by
  rw [step_tabToFound_splice
      (by decide : rps_1.nextUp loB_s2 = true)
      (by decide : rps_1.pileOfTop loB_s2 = some Anchor.p4)]
  rfl

theorem rps_leg3 : State.step rps_2 (Move.tabToFound loB_s3) = some rps_3 := by
  rw [step_tabToFound_splice
      (by decide : rps_2.nextUp loB_s3 = true)
      (by decide : rps_2.pileOfTop loB_s3 = some Anchor.p4)]
  rfl

theorem rps_leg4 : State.step rps_3 (Move.tabToFound loB_s4) = some rps_4 := by
  rw [step_tabToFound_splice
      (by decide : rps_3.nextUp loB_s4 = true)
      (by decide : rps_3.pileOfTop loB_s4 = some Anchor.p4)]
  rfl

theorem rps_leg5 : State.step rps_4 (Move.tabToFound loB_cA) = some rps_5 := by
  rw [step_tabToFound_splice
      (by decide : rps_4.nextUp loB_cA = true)
      (by decide : rps_4.pileOfTop loB_cA = some Anchor.p5)]
  rfl

theorem rps_leg6 : State.step rps_5 (Move.tabToFound loB_c2) = some rps_6 := by
  rw [step_tabToFound_splice
      (by decide : rps_5.nextUp loB_c2 = true)
      (by decide : rps_5.pileOfTop loB_c2 = some Anchor.p5)]
  rfl

theorem rps_leg7 : State.step rps_6 (Move.tabToFound loB_c3) = some rps_7 := by
  rw [step_tabToFound_splice
      (by decide : rps_6.nextUp loB_c3 = true)
      (by decide : rps_6.pileOfTop loB_c3 = some Anchor.p5)]
  rfl

theorem rps_leg8 : State.step rps_7 (Move.tabToFound loB_c4) = some rps_8 := by
  rw [step_tabToFound_splice
      (by decide : rps_7.nextUp loB_c4 = true)
      (by decide : rps_7.pileOfTop loB_c4 = some Anchor.p5)]
  rfl

/-- **THE COVER SEAT LEG** — the play's ninth move: the cold heart
four seats onto the club five's top, revealing the hidden king at
the cover's source. -/
theorem rps_leg9 :
    State.step rps_8 (Move.tabToTab loB_h4 (Sum.inr loB_c5)) = some rps_F := by
  rw [step_tabToTab_eq]
  rw [(by decide : rps_8.pileHolding loB_h4 = some Anchor.p6)]
  rw [(by decide : rps_8.canPlace loB_h4 (Sum.inr loB_c5) = true)]
  rfl

/-- **THE RAW PLAY RUNS** — nine spelled legs, run-composed through
the banked `run_one`/`run_split` rows. -/
private theorem rps_run9 : rps.run
    [Move.tabToFound loB_sA, Move.tabToFound loB_s2,
     Move.tabToFound loB_s3, Move.tabToFound loB_s4,
     Move.tabToFound loB_cA, Move.tabToFound loB_c2,
     Move.tabToFound loB_c3, Move.tabToFound loB_c4,
     Move.tabToTab loB_h4 (Sum.inr loB_c5)] = some rps_F := by
  have r1 : rps.run [Move.tabToFound loB_sA] = some rps_1 := run_one rps_leg1
  have r2 : rps_1.run [Move.tabToFound loB_s2] = some rps_2 := run_one rps_leg2
  have r3 : rps_2.run [Move.tabToFound loB_s3] = some rps_3 := run_one rps_leg3
  have r4 : rps_3.run [Move.tabToFound loB_s4] = some rps_4 := run_one rps_leg4
  have r5 : rps_4.run [Move.tabToFound loB_cA] = some rps_5 := run_one rps_leg5
  have r6 : rps_5.run [Move.tabToFound loB_c2] = some rps_6 := run_one rps_leg6
  have r7 : rps_6.run [Move.tabToFound loB_c3] = some rps_7 := run_one rps_leg7
  have r8 : rps_7.run [Move.tabToFound loB_c4] = some rps_8 := run_one rps_leg8
  have r9 : rps_8.run [Move.tabToTab loB_h4 (Sum.inr loB_c5)] = some rps_F :=
    run_one rps_leg9
  have f89 : rps_7.run
      [Move.tabToFound loB_c4, Move.tabToTab loB_h4 (Sum.inr loB_c5)] = some rps_F :=
    run_split [Move.tabToFound loB_c4] rps_7 rps_8
      [Move.tabToTab loB_h4 (Sum.inr loB_c5)] rps_F r8 r9
  have f789 : rps_6.run
      [Move.tabToFound loB_c3, Move.tabToFound loB_c4,
       Move.tabToTab loB_h4 (Sum.inr loB_c5)] = some rps_F :=
    run_split [Move.tabToFound loB_c3] rps_6 rps_7
      [Move.tabToFound loB_c4, Move.tabToTab loB_h4 (Sum.inr loB_c5)] rps_F r7 f89
  have f6789 : rps_5.run
      [Move.tabToFound loB_c2, Move.tabToFound loB_c3, Move.tabToFound loB_c4,
       Move.tabToTab loB_h4 (Sum.inr loB_c5)] = some rps_F :=
    run_split [Move.tabToFound loB_c2] rps_5 rps_6
      [Move.tabToFound loB_c3, Move.tabToFound loB_c4,
       Move.tabToTab loB_h4 (Sum.inr loB_c5)] rps_F r6 f789
  have f56789 : rps_4.run
      [Move.tabToFound loB_cA, Move.tabToFound loB_c2, Move.tabToFound loB_c3,
       Move.tabToFound loB_c4, Move.tabToTab loB_h4 (Sum.inr loB_c5)] = some rps_F :=
    run_split [Move.tabToFound loB_cA] rps_4 rps_5
      [Move.tabToFound loB_c2, Move.tabToFound loB_c3, Move.tabToFound loB_c4,
       Move.tabToTab loB_h4 (Sum.inr loB_c5)] rps_F r5 f6789
  have f456789 : rps_3.run
      [Move.tabToFound loB_s4, Move.tabToFound loB_cA, Move.tabToFound loB_c2,
       Move.tabToFound loB_c3, Move.tabToFound loB_c4,
       Move.tabToTab loB_h4 (Sum.inr loB_c5)] = some rps_F :=
    run_split [Move.tabToFound loB_s4] rps_3 rps_4
      [Move.tabToFound loB_cA, Move.tabToFound loB_c2, Move.tabToFound loB_c3,
       Move.tabToFound loB_c4, Move.tabToTab loB_h4 (Sum.inr loB_c5)] rps_F r4 f56789
  have f3456789 : rps_2.run
      [Move.tabToFound loB_s3, Move.tabToFound loB_s4, Move.tabToFound loB_cA,
       Move.tabToFound loB_c2, Move.tabToFound loB_c3, Move.tabToFound loB_c4,
       Move.tabToTab loB_h4 (Sum.inr loB_c5)] = some rps_F :=
    run_split [Move.tabToFound loB_s3] rps_2 rps_3
      [Move.tabToFound loB_s4, Move.tabToFound loB_cA, Move.tabToFound loB_c2,
       Move.tabToFound loB_c3, Move.tabToFound loB_c4,
       Move.tabToTab loB_h4 (Sum.inr loB_c5)] rps_F r3 f456789
  have f23456789 : rps_1.run
      [Move.tabToFound loB_s2, Move.tabToFound loB_s3, Move.tabToFound loB_s4,
       Move.tabToFound loB_cA, Move.tabToFound loB_c2, Move.tabToFound loB_c3,
       Move.tabToFound loB_c4, Move.tabToTab loB_h4 (Sum.inr loB_c5)] = some rps_F :=
    run_split [Move.tabToFound loB_s2] rps_1 rps_2
      [Move.tabToFound loB_s3, Move.tabToFound loB_s4, Move.tabToFound loB_cA,
       Move.tabToFound loB_c2, Move.tabToFound loB_c3, Move.tabToFound loB_c4,
       Move.tabToTab loB_h4 (Sum.inr loB_c5)] rps_F r2 f3456789
  exact run_split [Move.tabToFound loB_sA] rps rps_1
    [Move.tabToFound loB_s2, Move.tabToFound loB_s3, Move.tabToFound loB_s4,
     Move.tabToFound loB_cA, Move.tabToFound loB_c2, Move.tabToFound loB_c3,
     Move.tabToFound loB_c4, Move.tabToTab loB_h4 (Sum.inr loB_c5)] rps_F r1 f23456789

/-- The landing world is WF (nine banked `step_wf` links off the
world's own WF). -/
theorem rps_F_wf : rps_F.WF :=
  step_wf (step_wf (step_wf (step_wf (step_wf (step_wf (step_wf (step_wf
    (step_wf rps_wf rps_leg1) rps_leg2) rps_leg3) rps_leg4) rps_leg5)
    rps_leg6) rps_leg7) rps_leg8) rps_leg9

/-- **THE FORK WITNESS AT THE LANDING** — the decided SB witness
search returns the spade five; the banked sound row reads the parcel:
the pair saturates the {slide · raise} license exactly, the covered
twin refuses vanilla. -/
theorem rps_F_witness : ForkWitness rps_F loB_s5 := by
  obtain ⟨hiff, hpin⟩ :=
    forkWitnessSB_sound rps_F_wf
      (by decide : forkWitnessSB rps_F = some loB_s5)
  exact ⟨hiff, hpin⟩

/-- **THE RAW REACHABILITY PACKAGE** at the stranded world. -/
theorem rps_reach :
    ∃ (F : State) (π : List Move),
      rps.run π = some F ∧ ForkWitness F loB_s5 :=
  ⟨rps_F,
   [Move.tabToFound loB_sA, Move.tabToFound loB_s2,
    Move.tabToFound loB_s3, Move.tabToFound loB_s4,
    Move.tabToFound loB_cA, Move.tabToFound loB_c2,
    Move.tabToFound loB_c3, Move.tabToFound loB_c4,
    Move.tabToTab loB_h4 (Sum.inr loB_c5)],
   rps_run9, rps_F_witness⟩

/-! ### §1d. THE REFUTATION -/

/-- **`steered_stuck_elevates` REFUTED** — the consumption arm's
frozen statement, negated at its own signature (implicit binders
rendered explicit; the body verbatim), refuted by the stranded
counterexample: a WF, BelowForkDeployed start — with the raw
fork-reachability carrier satisfied by a nine-leg play that climbs
both family rings to the pair's rank and seats the cold cover —
whose EMPTY steered run is a certified SteeredRun to a certified
SteeredStuck world (the start itself), while the start's slab reads
INTACT (the twin-side rung strictly below the pair's rank).  The
conclusion (`¬ familyBelowFrontier W x`) fails at the terminal W = s.

THE COUNTEREXAMPLE'S LESSON (the restatement the arm must adopt):
the premises admit worlds whose stuck terminal is the START itself
— the trajectory never ARRIVES anywhere.  The consumption arm
needs an ARRIVAL premise: either (a) a nonemptiness condition on ρ
(a first leg exists, so the world's own letters actually fired),
or (b) the exhaustion zone's parked-rung clause folded into the
hypotheses (the terminal is in the arrival zone: the family rungs
read EXACTLY the pair's rank), or (c) the reachability carrier
upgraded from RAW to STEERED-threaded (the manifesting play shares
the steer's own discipline).  Each bars the empty run: (a)
directly, (b) because the stranded slab reads strict-below, (c)
because the stranded world's only steered run is the empty one. -/
theorem steered_stuck_elevates_refuted :
    ¬ (∀ (s : State) (x : Card), s.WF → BelowForkDeployed s x →
        (∃ (F : State) (π : List Move),
          s.run π = some F ∧ ForkWitness F x) →
        ∀ (ρ : List Move) (W : State),
          SteeredRun s ρ W → SteeredStuck W → ¬ familyBelowFrontier W x) := by
  intro h
  exact (h rps loB_s5 rps_wf rps_bfd rps_reach [] rps
    (SteeredRun.nil rps) rps_stuck) rps_slab

/-! ## §2. Deliverable 2 — the oscillator maintenance, per leg -/

private def rpC_C (s : Suit) (r : Rank) : Card := ⟨s, r⟩
private def rpC_T (s : Suit) (n : Nat) : List Card := s.upCards.take n

private def rp_h4 : Card := rpC_C .heart .four
private def rp_s3 : Card := rpC_C .spade .three
private def rp_d4 : Card := rpC_C .diamond .four
private def rp_c3 : Card := rpC_C .club .three
private def rp_d2 : Card := rpC_C .diamond .two
private def rp_cA : Card := rpC_C .club .ace
private def rp_d3 : Card := rpC_C .diamond .three
private def rp_c2 : Card := rpC_C .club .two

/-- **THE TWO-LEG PARKING ZONE** (the certified rp2_z, restated):
club ring parked at 2, the cover exposed bare, the black-threes pair
still joint over the red fours. -/
private def rz : State where
  found := fun s => match s with
    | .club => rpC_T s 2
    | _ => []
  piles := fun a => match a with
    | .p0 => ⟨[], [rp_h4, rp_s3]⟩
    | .p1 => ⟨[], [rp_d4, rp_c3]⟩
    | .p2 => ⟨[], [rp_d2]⟩
    | .p3 => ⟨[], [rp_d3]⟩
    | _ => ⟨[], []⟩
  stock :=
    [rpC_C .spade .ace, rpC_C .spade .two,
     rpC_C .spade .four, rpC_C .spade .five, rpC_C .spade .six,
     rpC_C .spade .seven, rpC_C .spade .eight, rpC_C .spade .nine,
     rpC_C .spade .ten, rpC_C .spade .jack, rpC_C .spade .queen,
     rpC_C .spade .king,
     rpC_C .heart .ace, rpC_C .heart .two, rpC_C .heart .three,
     rpC_C .heart .five, rpC_C .heart .six, rpC_C .heart .seven,
     rpC_C .heart .eight, rpC_C .heart .nine, rpC_C .heart .ten,
     rpC_C .heart .jack, rpC_C .heart .queen, rpC_C .heart .king,
     rpC_C .diamond .ace, rpC_C .diamond .five, rpC_C .diamond .six,
     rpC_C .diamond .seven, rpC_C .diamond .eight, rpC_C .diamond .nine,
     rpC_C .diamond .ten, rpC_C .diamond .jack, rpC_C .diamond .queen,
     rpC_C .diamond .king,
     rpC_C .club .four, rpC_C .club .five, rpC_C .club .six,
     rpC_C .club .seven, rpC_C .club .eight, rpC_C .club .nine,
     rpC_C .club .ten, rpC_C .club .jack, rpC_C .club .queen,
     rpC_C .club .king]
  waste := []
  drawStep := 1

theorem rz_wf : rz.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    cases s with
    | spade => exact ⟨0, rfl⟩
    | heart => exact ⟨0, rfl⟩
    | diamond => exact ⟨0, rfl⟩
    | club => exact ⟨2, rfl⟩
  · intro a
    cases a <;> decide
  · intro c _
    rcases c with ⟨s, r⟩
    cases s <;> cases r <;> decide
  · decide

/-- **THE WITNESS-SIDE CYCLE WORLD** — the cover seated on the spade
three, the club three exposed. -/
private def rwA : State where
  found := fun s => match s with
    | .club => rpC_T s 2
    | _ => []
  piles := fun a => match a with
    | .p0 => ⟨[], [rp_h4, rp_s3, rp_d2]⟩
    | .p1 => ⟨[], [rp_d4, rp_c3]⟩
    | .p3 => ⟨[], [rp_d3]⟩
    | _ => ⟨[], []⟩
  stock := rz.stock
  waste := []
  drawStep := 1

theorem rwA_wf : rwA.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    cases s with
    | spade => exact ⟨0, rfl⟩
    | heart => exact ⟨0, rfl⟩
    | diamond => exact ⟨0, rfl⟩
    | club => exact ⟨2, rfl⟩
  · intro a
    cases a <;> decide
  · intro c _
    rcases c with ⟨s, r⟩
    cases s <;> cases r <;> decide
  · decide

/-- **THE MIRROR CYCLE WORLD** — the cover seated on the club three,
the spade three exposed. -/
private def rwB : State where
  found := fun s => match s with
    | .club => rpC_T s 2
    | _ => []
  piles := fun a => match a with
    | .p0 => ⟨[], [rp_h4, rp_s3]⟩
    | .p1 => ⟨[], [rp_d4, rp_c3, rp_d2]⟩
    | .p3 => ⟨[], [rp_d3]⟩
    | _ => ⟨[], []⟩
  stock := rz.stock
  waste := []
  drawStep := 1

theorem rwB_wf : rwB.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    cases s with
    | spade => exact ⟨0, rfl⟩
    | heart => exact ⟨0, rfl⟩
    | diamond => exact ⟨0, rfl⟩
    | club => exact ⟨2, rfl⟩
  · intro a
    cases a <;> decide
  · intro c _
    rcases c with ⟨s, r⟩
    cases s <;> cases r <;> decide
  · decide

theorem rz_leg_in :
    State.step rz (Move.tabToTab rp_d2 (Sum.inr rp_s3)) = some rwA := by
  rw [step_tabToTab_eq]
  rw [(by decide : rz.pileHolding rp_d2 = some Anchor.p2)]
  rw [(by decide : rz.canPlace rp_d2 (Sum.inr rp_s3) = true)]
  refine congrArg some (State.ext ?_ ?_ ?_ ?_ ?_)
  · funext s
    cases s <;> rfl
  · funext a
    cases a <;> rfl
  · rfl
  · rfl
  · rfl

theorem rp2c_legA :
    State.step rwA (Move.tabToTab rp_d2 (Sum.inr rp_c3)) = some rwB := by
  rw [step_tabToTab_eq]
  rw [(by decide : rwA.pileHolding rp_d2 = some Anchor.p0)]
  rw [(by decide : rwA.canPlace rp_d2 (Sum.inr rp_c3) = true)]
  refine congrArg some (State.ext ?_ ?_ ?_ ?_ ?_)
  · funext s
    cases s <;> rfl
  · funext a
    cases a <;> rfl
  · rfl
  · rfl
  · rfl

theorem rp2c_legB :
    State.step rwB (Move.tabToTab rp_d2 (Sum.inr rp_s3)) = some rwA := by
  rw [step_tabToTab_eq]
  rw [(by decide : rwB.pileHolding rp_d2 = some Anchor.p1)]
  rw [(by decide : rwB.canPlace rp_d2 (Sum.inr rp_s3) = true)]
  refine congrArg some (State.ext ?_ ?_ ?_ ?_ ?_)
  · funext s
    cases s <;> rfl
  · funext a
    cases a <;> rfl
  · rfl
  · rfl
  · rfl

/-- The cover's twin (the heart two) is stocked at both cycle worlds
— the cover is CARGO, never a mobile pair member. -/
private theorem rwA_cover_cargo :
    ∀ (p : Anchor), rp_d2.twin ∉ (rwA.piles p).faceUp := by
  intro p
  cases p <;> decide

private theorem rwB_cover_cargo :
    ∀ (p : Anchor), rp_d2.twin ∉ (rwB.piles p).faceUp := by
  intro p
  cases p <;> decide

/-- **THE OSCILLATOR MAINTENANCE, BOARD GRADE** — after a fired
cover seat landing the cover on the WITNESS member's top (leg A:
rwA → rwB, the spade three covered), the MIRROR letter stands at the
successor: the very same cover, seated onto the twin member's top,
is a genuine SteeredLetter of the successor world — it fires (leg B
off the banked step equation), is reversible (its one-move return
is leg A, through the banked `run_one`), and the joint clause reads
vacuously (cargo cover, the mate stocked).  This is rp2's alternation
generalized: the rattle leg of each cycle world is the mirror of the
leg that produced it. -/
theorem cover_stands_after_seat_board :
    ∃ b', SteeredLetter rwB (Move.tabToTab rp_d2 b') := by
  refine ⟨Sum.inr rp_s3, ⟨?_, ⟨rwA, [Move.tabToTab rp_d2 (Sum.inr rp_c3)],
    rp2c_legB, run_one rp2c_legA⟩, ?_⟩⟩
  · rw [rp2c_legB]
    exact Option.some_ne_none _
  · intro hmob
    rcases hmob with ⟨-, -, ⟨p, hp⟩, -⟩
    exact absurd hp (rwB_cover_cargo p)

/-- **THE ENTRY-SIDE MAINTENANCE** — the same read one leg earlier:
after the entry cover seat (rz → rwA), the forward rattle letter
stands at the landing. -/
theorem rwA_stands_after_seat :
    ∃ b', SteeredLetter rwA (Move.tabToTab rp_d2 b') := by
  refine ⟨Sum.inr rp_c3, ⟨?_, ⟨rwB, [Move.tabToTab rp_d2 (Sum.inr rp_s3)],
    rp2c_legA, run_one rp2c_legB⟩, ?_⟩⟩
  · rw [rp2c_legA]
    exact Option.some_ne_none _
  · intro hmob
    rcases hmob with ⟨-, -, ⟨p, hp⟩, -⟩
    exact absurd hp (rwA_cover_cargo p)

/-- **THE CYCLE WORLDS ARE NEVER STEERED-STUCK** — the maintenance
rows consumed through the leaf's own PROVED
`not_stuck_of_coverStanding`: the standing mirror letter of each
successor world blocks stuckness outright.  This is the [H-mini]
oscillator row of the consumption arm's route step 1, at its first
certified instantiation — the never-stuck-under-cover read the route
prices. -/
theorem rwA_neverStuck : ¬ SteeredStuck rwA := by
  obtain ⟨b', hb'⟩ := rwA_stands_after_seat
  exact not_stuck_of_coverStanding ⟨b', hb'⟩

theorem rwB_neverStuck : ¬ SteeredStuck rwB := by
  obtain ⟨b', hb'⟩ := cover_stands_after_seat_board
  exact not_stuck_of_coverStanding ⟨b', hb'⟩

/-- **THE TWO-TOP FIT DIVIDEND at the cycle worlds** — both pair
members top their own piles at every cycle world (the rattle never
buries a member), and the pair survives the rattle unfounded: the
starved survivors at both worlds, decided — the maintenance row's
geometry feeding `starved_pair_survives`'s conclusions at the
oscillator's own instance. -/
theorem rwA_starved_intact :
    rp_s3 ∉ rwA.found rp_s3.suit ∧ rp_s3.twin ∉ rwA.found rp_s3.twin.suit := by
  constructor <;> decide

theorem rwB_starved_intact :
    rp_s3 ∉ rwB.found rp_s3.suit ∧ rp_s3.twin ∉ rwB.found rp_s3.twin.suit := by
  constructor <;> decide

/-- **THE MIRROR FIT, GENERAL GRADE, PROVED** — the tableau rules
cannot tell the pair's tops apart: any card fitting one member's top
fits the twin member's top too (the banked `canSitOn_twin_right`,
one rewrite).  This is the two-top fit geometry of the maintenance
row, in the banked rows' own vocabulary — the mirror target of the
cover's post-seat letter always exists geometrically. -/
theorem mirror_fit_of_cover {d x : Card}
    (h : canSitOn d x = true) : canSitOn d x.twin = true := by
  have ht : canSitOn d x.twin = canSitOn d {x with suit := x.suit.twin} := rfl
  rw [ht, canSitOn_twin_right]
  exact h

/-- **THE OSCILLATOR MAINTENANCE, GENERAL GRADE** [H-mini, priced —
this row carries the file's one named sorry] — after a fired cover
seat `tabToTab d (inr x)` off a WF world, landing the cover on x's
top: the MIRROR letter stands at the successor, targeting the twin
member's top.

ROUTE (the priced assembly, all pieces banked):
(1) FIRES — the successor's mirror-seat read: `step_tabToTab_inv`
    decomposes the leg's splice; the twin's pile-top survives the
    seat's source rewrite and the landing rewrite (the §5 kit's
    `steered_slideLanding` grain: `steered_topSearch` over
    `setPile_piles_ne`/`putRun_piles_inr_ne` at m ≠ k), and the
    mirror target's fit is `mirror_fit_of_cover` (PROVED above)
    over the leg's own `canPlace` fit — so the successor's mirror
    seat fires.
(2) REVERSIBILITY — the one-move return: the cover departs the
    twin's top back onto x's re-exposed top (the mirror seat's own
    splice), restoring the successor; the witness play has length
    ONE, the R3w sufficiency shape at oscillator grain — the splice
    rows plus `run_one` (the two cycle worlds above certify the
    shape at grade).
(3) THE JOINT CLAUSE — the cover's cargo-persistence: under
    `hcargo1` the mate is off the face-up zone at the predecessor;
    the seat's writes touch only the source pile (bare-and-burn: no
    reveal) and the landing pile (only the cover lands), so the
    mate stays off the face-up zone at the successor — the §5
    slide-faceUp kit read in both directions.
The board-grade half is fully proved above
(`cover_stands_after_seat_board`); this general row is the same
statement at arbitrary WF geometry, and the sorry prices ONLY the
assembly's three splice chases. -/
theorem cover_stands_after_seat {W1 W2 : State} {d x : Card} {k m : Anchor}
    (hwf1 : W1.WF)
    (hstep : State.step W1 (Move.tabToTab d (Sum.inr x)) = some W2)
    (hpotx : W1.pileOfTop x = some k)
    (hpott : W1.pileOfTop x.twin = some m)
    (hmk : m ≠ k)
    (hfit : W1.canPlace d (Sum.inr x) = true)
    (hbare : below d (W1.piles Anchor.p6).faceUp = [] ∨
      ∃ a, W1.pileHolding d = some a ∧
        below d (W1.piles a).faceUp = [] ∧ (W1.piles a).hidden = [])
    (hcargo1 : ∀ (p : Anchor), d.twin ∉ (W1.piles p).faceUp) :
    ∃ b', SteeredLetter W2 (Move.tabToTab d b') := by
  sorry

/-! ## §3. The audit battery -/

#print axioms rps_wf
#print axioms rps_slab
#print axioms rps_bfd
#print axioms rps_stuck
#print axioms rps_leg1
#print axioms rps_leg2
#print axioms rps_leg3
#print axioms rps_leg4
#print axioms rps_leg5
#print axioms rps_leg6
#print axioms rps_leg7
#print axioms rps_leg8
#print axioms rps_leg9
#print axioms rps_F_wf
#print axioms rps_F_witness
#print axioms rps_reach
#print axioms steered_stuck_elevates_refuted
#print axioms rz_wf
#print axioms rwA_wf
#print axioms rwB_wf
#print axioms rz_leg_in
#print axioms rp2c_legA
#print axioms rp2c_legB
#print axioms cover_stands_after_seat_board
#print axioms rwA_stands_after_seat
#print axioms rwA_neverStuck
#print axioms rwB_neverStuck
#print axioms mirror_fit_of_cover
#print axioms rwA_starved_intact
#print axioms rwB_starved_intact
#print axioms cover_stands_after_seat
/-! ## §10. THE TWIN-FORK FAMILY — the owner's direct formulation
(2026-10-17; promoted from two certified scratch lanes, exit 0 both)

THE OWNER'S STATE-LEVEL SHAPE, frozen byte-verbatim:
`TwinFork st x := CanRaise st x ∧ ¬ CanRaise st x.twin ∧
CanRaiseS st x.twin` — one club standing, the mate coverable —
plus `ZoneCleanBelow` (the sub-rank zone).  Two scratch lanes
probed it falsifier-first (23 + 12 heads):

* THE FENCES (the hunt): `twinfork_direct_refuted` — the LATERAL
  leak (iks: a second hot-topped-seated card at the pair's OWN
  rank breaks the direct conclusion while both premise clauses
  hold; strictly-below filters cannot see it by design);
  `twinfork_bare_refuted` — the hot-cover board (sl3); the
  chase's double block (the pin kills S-liveness at every higher
  shape; the pollution kills every higher zone clause).
* THE PROVED DIRECT FORM (the draft): `twinFork_forkState` — the
  assembly closes with the two honest census premises (rank-equal
  and super-rank third-censuses); the FAMILY-SUIT PIN KILLS came
  free (both family rungs pinned at the pair's rank; the cover
  itself lands at r-1 — forkPointC's cover clauses for free, per
  the owner's design).
* THE EXIST-FORM SCAFFOLD: the rank-12 ANCHOR PROVED
  (`twinFork_witness_max`), the conditional rank-step PROVED;
  the residue priced as `twinFork_upCensus` [H] with its complete
  three-way-split route.
* THE FREEZE MENU for the owner (recorded; nothing consumed by
  force): (i) the census'd direct form (proved, censuses are the
  content); (ii) the exist-form (anchor+step proved; up-census
  priced); (iii) THE CLASS-CENSUS PIVOT — TwinFork alone implies
  the class forks, via ForkCensus's arm-contingency grammar —
  the reading of "a fork witness for the macro state" that
  survives every hunt board (iks forks as a CLASS even though
  its state does not).
-/
/-! ## §0. The owner's shapes, mirrored verbatim -/

def TwinFork (st : State) (x : Card) : Prop :=
  CanRaise st x ∧ ¬ CanRaise st x.twin ∧ CanRaiseS st x.twin

def ZoneCleanBelow (st : State) (x : Card) : Prop :=
  ∀ c, c ≠ x → c ≠ x.twin → c.rank.toIdx < x.rank.toIdx → ¬ CanRaiseS st c

/-! ## §1. The kit -/

private def tq_C (s : Suit) (r : Rank) : Card := ⟨s, r⟩
private def tq_T (s : Suit) (n : Nat) : List Card := s.upCards.take n

private def tq_sA : Card := tq_C .spade .ace
private def tq_s2 : Card := tq_C .spade .two
private def tq_s3 : Card := tq_C .spade .three
private def tq_s4 : Card := tq_C .spade .four
private def tq_cA : Card := tq_C .club .ace
private def tq_c2 : Card := tq_C .club .two
private def tq_c3 : Card := tq_C .club .three
private def tq_h2 : Card := tq_C .heart .two
private def tq_h3 : Card := tq_C .heart .three
private def tq_h4 : Card := tq_C .heart .four
private def tq_dA : Card := tq_C .diamond .ace
private def tq_d2 : Card := tq_C .diamond .two
private def tq_d3 : Card := tq_C .diamond .three
private def tq_d4 : Card := tq_C .diamond .four

/-! ## §2. Hunt 1 — the lateral-rank interference board `iks` -/

/-- **THE LATERAL-RANK INTERFERENCE BOARD**: black rungs parked at 2
(the fork pair hot and covered, the loF2 furniture), the HEART ring
parked at 2 with a SECOND hot-topped-seated heart three on its own
pile (h3 over s4) — a card at the pair's OWN rank, S-live on its
own merits, a genuine census-breaking third. -/
private def iks : State where
  found := fun s => match s with
    | .spade => tq_T s 2
    | .club => tq_T s 2
    | .heart => tq_T s 2
    | _ => []
  piles := fun a => match a with
    | .p0 => ⟨[], [tq_h4, tq_s3]⟩
    | .p1 => ⟨[], [tq_d4, tq_c3, tq_d2]⟩
    | .p2 => ⟨[], [tq_s4, tq_h3]⟩
    | _ => ⟨[], []⟩
  stock :=
    [tq_C .spade .five, tq_C .spade .six, tq_C .spade .seven,
     tq_C .spade .eight, tq_C .spade .nine, tq_C .spade .ten,
     tq_C .spade .jack, tq_C .spade .queen, tq_C .spade .king,
     tq_C .club .four, tq_C .club .five, tq_C .club .six,
     tq_C .club .seven, tq_C .club .eight, tq_C .club .nine,
     tq_C .club .ten, tq_C .club .jack, tq_C .club .queen,
     tq_C .club .king,
     tq_C .heart .five, tq_C .heart .six, tq_C .heart .seven,
     tq_C .heart .eight, tq_C .heart .nine, tq_C .heart .ten,
     tq_C .heart .jack, tq_C .heart .queen, tq_C .heart .king,
     tq_C .diamond .ace, tq_C .diamond .three, tq_C .diamond .five,
     tq_C .diamond .six, tq_C .diamond .seven, tq_C .diamond .eight,
     tq_C .diamond .nine, tq_C .diamond .ten, tq_C .diamond .jack,
     tq_C .diamond .queen, tq_C .diamond .king]
  waste := []
  drawStep := 1

theorem iks_wf : iks.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    cases s with
    | spade => exact ⟨2, rfl⟩
    | heart => exact ⟨2, rfl⟩
    | diamond => exact ⟨0, rfl⟩
    | club => exact ⟨2, rfl⟩
  · intro a
    cases a <;> decide
  · intro c _
    rcases c with ⟨s, r⟩
    cases s <;> cases r <;> decide
  · decide

/-- The S-deadness helper: a decided `canRaiseSB = false` upgrades
to `¬ CanRaiseS` at WF, through the banked flat bridge. -/
private theorem Snot_of_SBfalse {st : State} (hwf : st.WF) (c : Card)
    (hb : canRaiseSB st c = false) : ¬ CanRaiseS st c := by
  intro hS
  rw [(canRaiseSB_true_iff hwf).mpr hS] at hb
  exact absurd hb (by simp)

/-- The S-liveness re-read: any `CanRaiseS` at WF forces the flat
Bool true — theZeugnis-fail side, for leaf-decided sweeps. -/
private theorem SRaise_SBtrue {st : State} (hwf : st.WF) {c : Card}
    (hS : CanRaiseS st c) : canRaiseSB st c = true :=
  (canRaiseSB_true_iff hwf).mpr hS

/-- **TWIN-FORK PREMISE 1/3** — the spade three is hot over its
stool: raisable now. -/
theorem iks_raise_s3 : CanRaise iks tq_s3 :=
  ⟨by decide, Anchor.p0, by decide, Or.inl (by decide)⟩

/-- **TWIN-FORK PREMISE 2/3** — the covered club three refuses
vanilla outright. -/
theorem iks_noRaise_c3 : ¬ CanRaise iks tq_c3 := by
  intro hc
  have hb : canRaiseB iks tq_c3 = true := (canRaiseB_true_iff).2 hc
  rw [(by decide : canRaiseB iks tq_c3 = false)] at hb
  exact absurd hb (by simp)

/-- **TWIN-FORK PREMISE 3/3** — the covered club three is S-live
(a decided SB read through the flat bridge). -/
theorem iks_SRaise_c3 : CanRaiseS iks tq_c3 :=
  (canRaiseSB_true_iff iks_wf).mp (by decide : canRaiseSB iks tq_c3 = true)

/-- **THE TWIN-FORK HOLDS** at the rank-2 pair. -/
theorem iks_twinfork : TwinFork iks tq_s3 :=
  ⟨iks_raise_s3, iks_noRaise_c3, iks_SRaise_c3⟩

/-- **THE SUB-RANK ZONE IS CLEAN** — every strictly-sub-2 card is
S-dead: the black aces/deuces founded, the heart aces/deuces
founded, the diamond ace hot-in-principle but stocked-unlocatable,
the cover deuce cold at its pinned rung.  Read card by card through
the flat-S bridge. -/
theorem iks_zone : ZoneCleanBelow iks tq_s3 := by
  intro c _ _ hlt hS
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> first
    | exact absurd hlt (by decide)
    | exact absurd (SRaise_SBtrue iks_wf hS) (by decide)

/-- **THE HOT MEMBER'S S-READ** — the fork's own spade three is
S-live (hot-topped-seated); used by the pollution row below. -/
theorem iks_SRaise_s3 : CanRaiseS iks tq_s3 :=
  (canRaiseSB_true_iff iks_wf).mp (by decide : canRaiseSB iks tq_s3 = true)

/-- **THE THIRD, S-LIVE** — the lateral heart three (the pair's OWN
rank, on an independent pile): the census-breaking mechanism,
boarded. -/
theorem iks_h3_SRaised : CanRaiseS iks tq_h3 :=
  (canRaiseSB_true_iff iks_wf).mp (by decide : canRaiseSB iks tq_h3 = true)

/-- **THE PIN ROW** — the third's own twin (the diamond three) is
S-dead: its family's rung is pinned 0 by the low fork's cover
deuce, so it can never read hot. -/
theorem iks_d3_Sdead : ¬ CanRaiseS iks tq_d3 :=
  Snot_of_SBfalse iks_wf tq_d3 (by decide)

/-- **THE DIRECT CONCLUSION DIES** — the SB census decides FALSE at
the world (the lateral heart-three third breaks the pair's
saturation iff; no other witness stands), so there is no forkState
here. -/
theorem iks_noFork : ¬ forkState iks := by
  intro h
  have hb := (forkStateSB_true_iff iks_wf).mpr h
  rw [(by decide : forkStateSB iks = false)] at hb
  exact absurd hb (by simp)

/-- **HUNT 1'S VERDICT, LANDED** — the direct form of the twin-fork
statement is REFUTED: TwinFork + ZoneCleanBelow both hold at iks's
rank-2 pair, and `forkState iks` is FALSE.  The leak is the LATERAL
rank (a second hot-topped-seated card at the pair's own rank) — the
strictly-below zone filter cannot see it by design, and the
flat-S's own exit clause lets it live.  (The super-rank image
additionally cannot be built at all: the fork's furniture and the
cover's pin leave no realizable higher-rank future — the exit
clause kills the immovable stool outright, Find B.)  The freeze must
broaden the census to ALL non-pair cards, not just the strict
below. -/
theorem twinfork_direct_refuted :
    ¬ (∀ (st : State) (x : Card), TwinFork st x → ZoneCleanBelow st x → forkState st) := by
  intro h
  exact iks_noFork (h iks tq_s3 iks_twinfork iks_zone)

/-! ## §3. Hunt 2 — the exist-form's chase, live case -/

/-- **THE CHASE'S OBSTRUCTION, ARM 1** — TwinFork at the third's
own pair FAILS: the hot side (the lateral heart three) is raisable
now, its twin refuses vanilla (stocked), but the twin's S-liveness
is KILLED by the low fork's cover pinning the diamond rung at 0.
The rank-induction cannot even FORM its next twin-fork witness. -/
theorem iks_noTwinFork_h3 : ¬ TwinFork iks tq_h3 := by
  rintro ⟨-, -, hS⟩
  exact iks_d3_Sdead hS

/-- **THE CHASE'S OBSTRUCTION, ARM 1'** — TwinFork at the rank-3
furniture pair (the hot-in-naught heart four over its diamond twin)
fails on its FIRST arm: the stool is not even raisable now (its
rank reads past its suit's parked ring, and its seat is blocked by
the fork member atop it). -/
theorem iks_noTwinFork_h4 : ¬ TwinFork iks tq_h4 := by
  rintro ⟨hc, -, -⟩
  have hb : canRaiseB iks tq_h4 = true := (canRaiseB_true_iff).2 hc
  rw [(by decide : canRaiseB iks tq_h4 = false)] at hb
  exact absurd hb (by simp)

/-- **THE CHASE'S OBSTRUCTION, ARM 2 (THE POLLUTION)** —
ZoneCleanBelow at the rank-3 furniture pair FAILS: the low fork's
own hot member is a strictly-sub-3 S-live card.  Every candidate
witness at-or-above the fork inherits the fork's members as
sub-rank pollution. -/
theorem iks_zone_h4_fails : ¬ ZoneCleanBelow iks tq_h4 := by
  intro h
  exact h tq_s3 (by decide) (by decide) (by decide) iks_SRaise_s3

/-! ## §4. Hunt 3 — the sub-rank leak craft, board `sl3` -/

/-- **THE SUB-RANK LEAK BOARD**: the classic fork shape, with the
cover deuce's OWN ring parked at 1 — the cover is hot AT its
covering post (seated on the club three, chop nonempty), a genuine
strictly-sub-rank S-live third. -/
private def sl3 : State where
  found := fun s => match s with
    | .spade => tq_T s 2
    | .club => tq_T s 2
    | .diamond => tq_T s 1
    | _ => []
  piles := fun a => match a with
    | .p0 => ⟨[], [tq_h4, tq_s3]⟩
    | .p1 => ⟨[], [tq_d4, tq_c3, tq_d2]⟩
    | _ => ⟨[], []⟩
  stock :=
    [tq_C .spade .four, tq_C .spade .five, tq_C .spade .six,
     tq_C .spade .seven, tq_C .spade .eight, tq_C .spade .nine,
     tq_C .spade .ten, tq_C .spade .jack, tq_C .spade .queen,
     tq_C .spade .king,
     tq_C .club .four, tq_C .club .five, tq_C .club .six,
     tq_C .club .seven, tq_C .club .eight, tq_C .club .nine,
     tq_C .club .ten, tq_C .club .jack, tq_C .club .queen,
     tq_C .club .king,
     tq_C .heart .ace, tq_C .heart .two, tq_C .heart .three,
     tq_C .heart .five, tq_C .heart .six, tq_C .heart .seven,
     tq_C .heart .eight, tq_C .heart .nine, tq_C .heart .ten,
     tq_C .heart .jack, tq_C .heart .queen, tq_C .heart .king,
     tq_C .diamond .three, tq_C .diamond .five, tq_C .diamond .six,
     tq_C .diamond .seven, tq_C .diamond .eight, tq_C .diamond .nine,
     tq_C .diamond .ten, tq_C .diamond .jack, tq_C .diamond .queen,
     tq_C .diamond .king]
  waste := []
  drawStep := 1

theorem sl3_wf : sl3.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    cases s with
    | spade => exact ⟨2, rfl⟩
    | heart => exact ⟨0, rfl⟩
    | diamond => exact ⟨1, rfl⟩
    | club => exact ⟨2, rfl⟩
  · intro a
    cases a <;> decide
  · intro c _
    rcases c with ⟨s, r⟩
    cases s <;> cases r <;> decide
  · decide

/-- **THE FORK STILL HOLDS** at the sub-rank-leak board: the spade
three hot, the club three covered-refusing and S-live. -/
theorem sl3_raise_s3 : CanRaise sl3 tq_s3 :=
  ⟨by decide, Anchor.p0, by decide, Or.inl (by decide)⟩

theorem sl3_noRaise_c3 : ¬ CanRaise sl3 tq_c3 := by
  intro hc
  have hb : canRaiseB sl3 tq_c3 = true := (canRaiseB_true_iff).2 hc
  rw [(by decide : canRaiseB sl3 tq_c3 = false)] at hb
  exact absurd hb (by simp)

theorem sl3_SRaise_c3 : CanRaiseS sl3 tq_c3 :=
  (canRaiseSB_true_iff sl3_wf).mp (by decide : canRaiseSB sl3 tq_c3 = true)

theorem sl3_twinfork : TwinFork sl3 tq_s3 :=
  ⟨sl3_raise_s3, sl3_noRaise_c3, sl3_SRaise_c3⟩

/-- **THE SUB-RANK THIRD, S-LIVE** — the hot cover deuce itself,
ranked strictly below the fork's rank. -/
theorem sl3_SRaise_d2 : CanRaiseS sl3 tq_d2 :=
  (canRaiseSB_true_iff sl3_wf).mp (by decide : canRaiseSB sl3 tq_d2 = true)

/-- **THE ZONE CLAUSE FAILS, USEFULLY** — exhibited at the hot
cover: the third is neither pair member, ranks strictly below 2,
and reads S-live.  This is `ZoneCleanBelow`'s load-bearing instance:
without it, this board would pass. -/
theorem sl3_zone_fails : ¬ ZoneCleanBelow sl3 tq_s3 := by
  intro h
  exact h tq_d2 (by decide) (by decide) (by decide) sl3_SRaise_d2

/-- **THE CENSUS IS GENUINELY BROKEN** — the SB read decides FALSE:
the hot cover is a sub-rank S-live third, so no witness saturates. -/
theorem sl3_noFork : ¬ forkState sl3 := by
  intro h
  have hb := (forkStateSB_true_iff sl3_wf).mpr h
  rw [(by decide : forkStateSB sl3 = false)] at hb
  exact absurd hb (by simp)

/-- **HUNT 3'S VERDICT, LANDED** — the BARE form of the twin-fork
statement (TwinFork alone implies forkState) is REFUTED at sl3;
`ZoneCleanBelow` is exactly the premise that would have excluded
this board, which boards its load-bearing-ness — but by Hunt 1 even
the clean-zoned form fails, so the freeze needs the full census. -/
theorem twinfork_bare_refuted :
    ¬ (∀ (st : State) (x : Card), TwinFork st x → forkState st) := by
  intro h
  exact sl3_noFork (h sl3 tq_s3 sl3_twinfork)

/-! ## §5. The hunt telemetry -/

-- the interference reads, raw (the ranked facts the ledger cites)
#eval canRaiseSB iks tq_s3
#eval canRaiseSB iks tq_c3
#eval canRaiseSB iks tq_h3
#eval canRaiseSB iks tq_d3
#eval canRaiseSB iks tq_h4
#eval forkStateSB iks
#eval canRaiseSB sl3 tq_d2
#eval forkStateSB sl3

/-! ## §6. The audit battery -/

#print axioms iks_wf
#print axioms iks_raise_s3
#print axioms iks_noRaise_c3
#print axioms iks_SRaise_c3
#print axioms iks_twinfork
#print axioms iks_zone
#print axioms iks_SRaise_s3
#print axioms iks_h3_SRaised
#print axioms iks_d3_Sdead
#print axioms iks_noFork
#print axioms twinfork_direct_refuted
#print axioms iks_noTwinFork_h3
#print axioms iks_noTwinFork_h4
#print axioms iks_zone_h4_fails
#print axioms sl3_wf
#print axioms sl3_raise_s3
#print axioms sl3_noRaise_c3
#print axioms sl3_SRaise_c3
#print axioms sl3_twinfork
#print axioms sl3_SRaise_d2
#print axioms sl3_zone_fails
#print axioms sl3_noFork
#print axioms twinfork_bare_refuted
/-- The probe bridge: the twin-fork's decidable face — both vanilla
probes plus the S-probe on the mate. -/
def TwinForkB (st : State) (x : Card) : Bool :=
  canRaiseB st x && (!canRaiseB st x.twin) && canRaiseSB st x.twin

theorem twinForkB_true_iff {st : State} (hwf : st.WF) {x : Card} :
    TwinForkB st x = true ↔ TwinFork st x := by
  constructor
  · intro h
    have hfull : ((canRaiseB st x && (!canRaiseB st x.twin)) &&
        canRaiseSB st x.twin) = true := h
    rw [Bool.and_eq_true] at hfull
    obtain ⟨hab, hSB⟩ := hfull
    rw [Bool.and_eq_true] at hab
    obtain ⟨hA, hnt⟩ := hab
    have hb2 : canRaiseB st x.twin = false := by
      cases hb : canRaiseB st x.twin with
      | true => rw [hb] at hnt; exact absurd hnt (by simp)
      | false => rfl
    refine ⟨(canRaiseB_true_iff).1 hA, ?_, (canRaiseSB_true_iff hwf).1 hSB⟩
    intro hcr
    rw [(canRaiseB_true_iff).2 hcr] at hb2
    exact absurd hb2 (by simp)
  · rintro ⟨h1, h2, hS⟩
    have hA : canRaiseB st x = true := (canRaiseB_true_iff).2 h1
    have hb2 : canRaiseB st x.twin = false := by
      cases hb : canRaiseB st x.twin with
      | true => exact absurd ((canRaiseB_true_iff).1 hb) h2
      | false => rfl
    have hSB : canRaiseSB st x.twin = true := (canRaiseSB_true_iff hwf).2 hS
    show ((canRaiseB st x && (!canRaiseB st x.twin)) &&
        canRaiseSB st x.twin) = true
    rw [hA, hb2, hSB]
    rfl

/-! ## §1. The boards (fresh class-rebuilds, probe-first) -/

private def tfCrd (s : Suit) (r : Rank) : Card := ⟨s, r⟩
private def tfTakeUp (s : Suit) (n : Nat) : List Card := s.upCards.take n

-- **tfA**: the fa2 class — the saturated deuce pair (both members
-- vanilla-live at rung 1, the threes stocked): the JOINT world.
private def tfA : State where
  found := fun s => tfTakeUp s 1
  piles := fun a => match a with
    | .p0 => ⟨[], [tfCrd .heart .three, tfCrd .spade .two]⟩
    | .p1 => ⟨[], [tfCrd .diamond .three, tfCrd .club .two]⟩
    | _ => ⟨[], []⟩
  stock :=
    [tfCrd .spade .three, tfCrd .spade .four, tfCrd .spade .five,
     tfCrd .spade .six, tfCrd .spade .seven, tfCrd .spade .eight,
     tfCrd .spade .nine, tfCrd .spade .ten, tfCrd .spade .jack,
     tfCrd .spade .queen, tfCrd .spade .king,
     tfCrd .heart .two, tfCrd .heart .four, tfCrd .heart .five,
     tfCrd .heart .six, tfCrd .heart .seven, tfCrd .heart .eight,
     tfCrd .heart .nine, tfCrd .heart .ten, tfCrd .heart .jack,
     tfCrd .heart .queen, tfCrd .heart .king,
     tfCrd .diamond .two, tfCrd .diamond .four, tfCrd .diamond .five,
     tfCrd .diamond .six, tfCrd .diamond .seven, tfCrd .diamond .eight,
     tfCrd .diamond .nine, tfCrd .diamond .ten, tfCrd .diamond .jack,
     tfCrd .diamond .queen, tfCrd .diamond .king,
     tfCrd .club .three, tfCrd .club .four, tfCrd .club .five,
     tfCrd .club .six, tfCrd .club .seven, tfCrd .club .eight,
     tfCrd .club .nine, tfCrd .club .ten, tfCrd .club .jack,
     tfCrd .club .queen, tfCrd .club .king]
  waste := []
  drawStep := 1

theorem tfA_wf : tfA.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    cases s <;> exact ⟨1, rfl⟩
  · intro a
    cases a <;> decide
  · intro c _
    rcases c with ⟨s, r⟩
    cases s <;> cases r <;> decide
  · decide

-- **tf0**: the fa0 class — BOTH deuce pairs double-hot (the
-- multi-pair joint frontier).
private def tf0 : State where
  found := fun s => tfTakeUp s 1
  piles := fun a => match a with
    | .p0 => ⟨[], [tfCrd .heart .three, tfCrd .spade .two]⟩
    | .p1 => ⟨[], [tfCrd .club .three, tfCrd .diamond .two]⟩
    | .p2 => ⟨[], [tfCrd .spade .three, tfCrd .heart .two]⟩
    | .p5 => ⟨[], [tfCrd .diamond .three, tfCrd .club .two]⟩
    | _ => ⟨[], []⟩
  stock :=
    [tfCrd .spade .four, tfCrd .spade .five, tfCrd .spade .six,
     tfCrd .spade .seven, tfCrd .spade .eight, tfCrd .spade .nine,
     tfCrd .spade .ten, tfCrd .spade .jack, tfCrd .spade .queen,
     tfCrd .spade .king,
     tfCrd .heart .four, tfCrd .heart .five, tfCrd .heart .six,
     tfCrd .heart .seven, tfCrd .heart .eight, tfCrd .heart .nine,
     tfCrd .heart .ten, tfCrd .heart .jack, tfCrd .heart .queen,
     tfCrd .heart .king,
     tfCrd .diamond .four, tfCrd .diamond .five, tfCrd .diamond .six,
     tfCrd .diamond .seven, tfCrd .diamond .eight, tfCrd .diamond .nine,
     tfCrd .diamond .ten, tfCrd .diamond .jack, tfCrd .diamond .queen,
     tfCrd .diamond .king,
     tfCrd .club .four, tfCrd .club .five, tfCrd .club .six,
     tfCrd .club .seven, tfCrd .club .eight, tfCrd .club .nine,
     tfCrd .club .ten, tfCrd .club .jack, tfCrd .club .queen,
     tfCrd .club .king]
  waste := []
  drawStep := 1

theorem tf0_wf : tf0.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    cases s <;> exact ⟨1, rfl⟩
  · intro a
    cases a <;> decide
  · intro c _
    rcases c with ⟨s, r⟩
    cases s <;> cases r <;> decide
  · decide

private def tf_sA : Card := tfCrd .spade .ace
private def tf_s2 : Card := tfCrd .spade .two
private def tf_s3 : Card := tfCrd .spade .three
private def tf_h2 : Card := tfCrd .heart .two
private def tf_h3 : Card := tfCrd .heart .three
private def tf_h4 : Card := tfCrd .heart .four
private def tf_d2 : Card := tfCrd .diamond .two
private def tf_d3 : Card := tfCrd .diamond .three
private def tf_d4 : Card := tfCrd .diamond .four
private def tf_cA : Card := tfCrd .club .ace
private def tf_c2 : Card := tfCrd .club .two
private def tf_c3 : Card := tfCrd .club .three

-- **tfR**: the loA class — the below-frontier start (black
-- foundations EMPTY, the climb material on stools, the threes pair
-- joint over the red fours): NOTHING hot.
private def tfR : State where
  found := fun _ => []
  piles := fun a => match a with
    | .p0 => ⟨[], [tf_h4, tf_s3]⟩
    | .p1 => ⟨[], [tf_d4, tf_c3]⟩
    | .p2 => ⟨[], [tf_h2, tf_sA]⟩
    | .p3 => ⟨[], [tf_h3, tf_s2]⟩
    | .p4 => ⟨[], [tf_d2, tf_cA]⟩
    | .p5 => ⟨[], [tf_d3, tf_c2]⟩
    | _ => ⟨[], []⟩
  stock :=
    [tfCrd .spade .four, tfCrd .spade .five, tfCrd .spade .six,
     tfCrd .spade .seven, tfCrd .spade .eight, tfCrd .spade .nine,
     tfCrd .spade .ten, tfCrd .spade .jack, tfCrd .spade .queen,
     tfCrd .spade .king,
     tfCrd .heart .ace, tfCrd .heart .five, tfCrd .heart .six,
     tfCrd .heart .seven, tfCrd .heart .eight, tfCrd .heart .nine,
     tfCrd .heart .ten, tfCrd .heart .jack, tfCrd .heart .queen,
     tfCrd .heart .king,
     tfCrd .diamond .ace, tfCrd .diamond .five, tfCrd .diamond .six,
     tfCrd .diamond .seven, tfCrd .diamond .eight, tfCrd .diamond .nine,
     tfCrd .diamond .ten, tfCrd .diamond .jack, tfCrd .diamond .queen,
     tfCrd .diamond .king,
     tfCrd .club .four, tfCrd .club .five, tfCrd .club .six,
     tfCrd .club .seven, tfCrd .club .eight, tfCrd .club .nine,
     tfCrd .club .ten, tfCrd .club .jack, tfCrd .club .queen,
     tfCrd .club .king]
  waste := []
  drawStep := 1

theorem tfR_wf : tfR.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    cases s <;> exact ⟨0, rfl⟩
  · intro a
    cases a <;> decide
  · intro c _
    rcases c with ⟨s, r⟩
    cases s <;> cases r <;> decide
  · decide

-- **tfF**: the loF2 class — the cover world (the spade three live,
-- the club three under the cold cargo cover D2, black rungs parked
-- at 2): THE board where all three twin-fork clauses hold.
private def tfF : State where
  found := fun s => match s with
    | .spade => tfTakeUp s 2
    | .club => tfTakeUp s 2
    | _ => []
  piles := fun a => match a with
    | .p0 => ⟨[], [tf_h4, tf_s3]⟩
    | .p1 => ⟨[], [tf_d4, tf_c3, tf_d2]⟩
    | _ => ⟨[], []⟩
  stock :=
    [tfCrd .spade .four, tfCrd .spade .five, tfCrd .spade .six,
     tfCrd .spade .seven, tfCrd .spade .eight, tfCrd .spade .nine,
     tfCrd .spade .ten, tfCrd .spade .jack, tfCrd .spade .queen,
     tfCrd .spade .king,
     tfCrd .heart .ace, tfCrd .heart .two, tfCrd .heart .three,
     tfCrd .heart .five, tfCrd .heart .six, tfCrd .heart .seven,
     tfCrd .heart .eight, tfCrd .heart .nine, tfCrd .heart .ten,
     tfCrd .heart .jack, tfCrd .heart .queen, tfCrd .heart .king,
     tfCrd .diamond .ace, tfCrd .diamond .three, tfCrd .diamond .five,
     tfCrd .diamond .six, tfCrd .diamond .seven, tfCrd .diamond .eight,
     tfCrd .diamond .nine, tfCrd .diamond .ten, tfCrd .diamond .jack,
     tfCrd .diamond .queen, tfCrd .diamond .king,
     tfCrd .club .four, tfCrd .club .five, tfCrd .club .six,
     tfCrd .club .seven, tfCrd .club .eight, tfCrd .club .nine,
     tfCrd .club .ten, tfCrd .club .jack, tfCrd .club .queen,
     tfCrd .club .king]
  waste := []
  drawStep := 1

theorem tfF_wf : tfF.WF := by
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

-- The probe reads, raw (the decidable faces):
#eval TwinForkB tfA tf_s2
#eval TwinForkB tf0 tf_s2
#eval TwinForkB tfR tf_s3
#eval TwinForkB tfF tf_s3
#eval forkStateSB tfF
#eval (forkWitnessSB tfF).isSome

/-! ## §2. The refutation probes (the joint and cold classes) -/

/-- **THE JOINT CLASS REFUTES CLAUSE 2** — at the fa2-class board the
twin-fork read on the spade deuce fails: its mate the club deuce is
vanilla-live too (the saturated pair), so the twin-refusal clause
dies. -/
theorem tfA_noTwinFork : ¬ TwinFork tfA tf_s2 := by
  intro h
  have hb : TwinForkB tfA tf_s2 = true := (twinForkB_true_iff tfA_wf).2 h
  rw [show TwinForkB tfA tf_s2 = false from by decide] at hb
  exact absurd hb (by simp)

/-- **THE MULTI-PAIR JOINT CLASS REFUTES CLAUSE 2** — same read at
the fa0-class board. -/
theorem tf0_noTwinFork : ¬ TwinFork tf0 tf_s2 := by
  intro h
  have hb : TwinForkB tf0 tf_s2 = true := (twinForkB_true_iff tf0_wf).2 h
  rw [show TwinForkB tf0 tf_s2 = false from by decide] at hb
  exact absurd hb (by simp)

/-- **THE BELOW-FRONTIER CLASS REFUTES CLAUSE 1** — at the loA-class
start the spade three has no vanilla license at all (its rung sits
at 0): nothing is hot. -/
theorem tfR_noTwinFork : ¬ TwinFork tfR tf_s3 := by
  intro h
  have hb : TwinForkB tfR tf_s3 = true := (twinForkB_true_iff tfR_wf).2 h
  rw [show TwinForkB tfR tf_s3 = false from by decide] at hb
  exact absurd hb (by simp)

/-! ## §3. The direct form (the assembly)

The census decomposition.  The FAMILY-SUIT thirds die FREE by the
twin-fork's own rung pins: the standing member's license pins its
suit's rung at the pair's rank; the mate's S-license pins the twin
suit's rung there too (`canRaiseS_rung`); any S-live card of a
family suit must then sit exactly at the pair's rank, and suit+rank
name the card — so it IS a pair member.  No premise.  The
THIRD-SUIT thirds are the two honest leaks: their suits' rungs are
unpinned, free to stand anywhere — the sub-rank half is swept by
the owner's `ZoneCleanBelow`, and the rank-equal and super-rank
halves come in as the two named census premises. -/

/-- The standing member's own license pins its family rung at the
pair's rank. -/
private theorem twinFork_pin1 {st : State} {x : Card}
    (h : TwinFork st x) : rungAt st x.suit = x.rank.toIdx :=
  (of_decide_eq_true h.1.1).symm

/-- The mate's S-license pins the twin suit's rung at the pair's
rank (the twin rank bridge). -/
private theorem twinFork_pin2 {st : State} {x : Card}
    (h : TwinFork st x) : rungAt st x.twin.suit = x.rank.toIdx := by
  have hr := canRaiseS_rung h.2.2
  rwa [Card.twin_rank] at hr

/-- **THE PIN KILL** — an S-live card of a family suit is a pair
member: the pins name its rank as the pair's, and suit+rank name
the card. -/
theorem family_suit_in_pair {st : State} {x c : Card}
    (h : TwinFork st x) (hS : CanRaiseS st c)
    (hs : c.suit = x.suit ∨ c.suit = x.twin.suit) :
    c = x ∨ c = x.twin := by
  obtain ⟨xs, xr⟩ := x
  obtain ⟨cs, cr⟩ := c
  have hr : rungAt st cs = cr.toIdx := canRaiseS_rung hS
  have hp1 : rungAt st xs = xr.toIdx := twinFork_pin1 h
  have hp2 : rungAt st (Suit.twin xs) = xr.toIdx := twinFork_pin2 h
  rcases hs with hs1 | hs2
  · have hcsx : cs = xs := hs1
    rw [hcsx, hp1] at hr
    refine Or.inl ?_
    show (⟨cs, cr⟩ : Card) = ⟨xs, xr⟩
    rw [hcsx, Rank.toIdx_inj hr.symm]
  · have hcst : cs = xs.twin := hs2
    rw [hcst, hp2] at hr
    refine Or.inr ?_
    show (⟨cs, cr⟩ : Card) = ⟨Suit.twin xs, xr⟩
    rw [hcst, Rank.toIdx_inj hr.symm]

set_option linter.unusedVariables false in
/-- **THE DIRECT FORM, PROVED** — with the two named census
premises (the third-suit rank-equal and super-rank leaks), the
twin-fork's own facts are `forkState`'s witness parcel: the pair
members are S-live (`now` on the standing license, the mate given),
the mate is vanilla-blocked (given), and every third card is swept —
family suits by the pins, the sub-rank zone by the owner's clean
premise, the rank-equal and super thirds by the named censuses.
`hwf` is dead weight at the Prop-grade assembly (the pins need no
WF; the probe consumers hold it per board anyway) — kept for the
frozen statement's shape, the linter silenced. -/
theorem twinFork_forkState {st : State} (hwf : st.WF) {x : Card}
    (h : TwinFork st x)
    (hc : ZoneCleanBelow st x)
    (heq : ∀ c, c ≠ x → c ≠ x.twin → c.rank.toIdx = x.rank.toIdx →
      ¬ CanRaiseS st c)
    (hsup : ∀ c, c.rank.toIdx > x.rank.toIdx → ¬ CanRaiseS st c) :
    forkState st := by
  refine ⟨x, ?_, h.2.1⟩
  intro c
  constructor
  · rintro (rfl | rfl)
    · exact CanRaiseS.now _ h.1
    · exact h.2.2
  · intro hS
    by_cases hs : c.suit = x.suit ∨ c.suit = x.twin.suit
    · exact family_suit_in_pair h hS hs
    · have hcx : c ≠ x := fun he => hs (Or.inl (by rw [he]))
      have hct : c ≠ x.twin := fun he => hs (Or.inr (by rw [he]))
      rcases Nat.lt_trichotomy c.rank.toIdx x.rank.toIdx with hlt | heq2 | hgt
      · exact absurd hS (hc c hcx hct hlt)
      · exact absurd hS (heq c hcx hct heq2)
      · exact absurd hS (hsup c hgt)

/-! ## §4. The anchor instance (the boarded proof) -/

/-- **THE COVER WORLD IS A TWIN-FORK** — all three clauses at tfF,
Prop-grade: the spade three stands licensed (next-up at the parked
spade rung, topping its stool pile with content below); the club
three is covered (no pile tops it — the `CanRaise` existential
dies); the club three is S-live (its reversible-cover cascade, read
off the decided S-probe through the banked flat bridge). -/
theorem tfF_TwinFork : TwinFork tfF tf_s3 := by
  refine ⟨⟨by decide, Anchor.p0, by decide, Or.inl (by decide)⟩, ?_, ?_⟩
  · intro hcr
    rcases hcr with ⟨-, a, htop, -⟩
    rw [show tfF.pileOfTop tf_s3.twin = none from by decide] at htop
    exact absurd htop (by simp)
  · exact ((canRaiseSB_true_iff tfF_wf).1) (by decide)

/-- The cover world's sub-rank zone is clean: every third card below
the threes' rank has no raise future (per-card: the decided S-probe
reads false — the sub-rank space at tfF is the cold cover itself,
stocked cards, and nothing with a next-up). -/
theorem tfF_zoneCleanBelow : ZoneCleanBelow tfF tf_s3 := by
  intro c hc1 hc2 hlt hS
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> first
    | exact absurd hlt (by decide)
    | exact absurd hc1 (by decide)
    | exact absurd hc2 (by decide)
    | exact absurd ((canRaiseSB_true_iff tfF_wf).2 hS) (by decide)

/-- The cover world's rank-equal census: no third card AT the
threes' rank is S-live (the other rank-2 cards are stocked). -/
theorem tfF_zoneCleanEq :
    ∀ c, c ≠ tf_s3 → c ≠ tf_c3 → c.rank.toIdx = tf_s3.rank.toIdx →
      ¬ CanRaiseS tfF c := by
  intro c hc1 hc2 heq2 hS
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> first
    | exact absurd heq2 (by decide)
    | exact absurd hc1 (by decide)
    | exact absurd hc2 (by decide)
    | exact absurd ((canRaiseSB_true_iff tfF_wf).2 hS) (by decide)

/-- The cover world's super-rank census: nothing above the threes'
rank is S-live (the red fours are cold stools, everything else
stocked). -/
theorem tfF_zoneCleanSup :
    ∀ c, c.rank.toIdx > tf_s3.rank.toIdx → ¬ CanRaiseS tfF c := by
  intro c hgt hS
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> first
    | exact absurd hgt (by decide)
    | exact absurd ((canRaiseSB_true_iff tfF_wf).2 hS) (by decide)

/-- **THE BOARDED ANCHOR** — the proved direct form concludes
`forkState` at the cover world: the owner's twin-fork read, certified
end to end at the loF2 class. -/
theorem tfF_fork : forkState tfF :=
  twinFork_forkState tfF_wf tfF_TwinFork tfF_zoneCleanBelow
    tfF_zoneCleanEq tfF_zoneCleanSup

/-- The SB witness search agrees: the computable reader returns the
spade three (the forkWitnessSB_sound bridge would read the same
parcel the boarded proof just assembled). -/
theorem tfF_witnessSB : forkWitnessSB tfF = some tf_s3 := by
  decide

/-! ## §5. The exist-form scaffold (the rank chase) -/

set_option linter.unusedVariables false in
/-- **THE CONDITIONAL RANK-STEP, PROVED** — the assembly half of the
chase: a super-rank S-live third whose twin is blocked and
S-saturated, itself standing licensed, IS a twin-fork at the
strictly higher rank.  All the substantive legs are the priced
UP-CENSUS's content (`twinFork_upCensus` below); the assembly is
free.  The untouchable premises (the chase's scope) ride the row,
the linter silenced per the priced-row protocol. -/
theorem twinFork_rankStep {st : State} (hwf : st.WF) {x : Card}
    (h : TwinFork st x) (hz : ZoneCleanBelow st x)
    {c : Card}
    (hS : CanRaiseS st c) (hgt : c.rank.toIdx > x.rank.toIdx)
    (hcr : CanRaise st c) (hnt : ¬ CanRaise st c.twin)
    (hSct : CanRaiseS st c.twin) :
    TwinFork st c ∧ c.rank.toIdx > x.rank.toIdx :=
  ⟨⟨hcr, hnt, hSct⟩, hgt⟩
set_option linter.unusedVariables false in
/-- **THE UP-CENSUS, PRICED** [H] — the leak-chase's one genuinely
missing derivation.

CAPTION (the careful check the formulation demanded): the chase from
"super-rank S-live third" to "a higher twin-fork" does NOT close
unconditionally.  By the flat characterization's exit clause
(`canRaiseS_iff`, Orig/ForkStateS.lean:539 — read jointly with
`canRaiseS_positionSeat` and `canRaiseS_runOrTwin`) the S-live
third `c` splits:
* TOPPING (`run = []`): `c` is itself vanilla-live-shaped; its twin
  either raises too (a JOINT super pair — no fork up there; this is
  the joint world the falsifier certified the spine EATING at its
  own rank, one rank up — forking evidence is exactly what it lacks)
  or is blocked while NOT S-live — the saturation leg of a higher
  twin-fork is missing, and nothing in the below-fork's facts
  supplies it.
* COVERED (`run ≠ []`): `c`'s pile-top read dies (the license's
  top-existential fails), so `c` is not itself the standing member of
  anything — the covered shape is the MATE side of a would-be fork,
  whose standing member `c.twin` carries no derivable license.
In every branch the chase needs MORE than the leak gives.  The
owner's COVER note survives intact: any cover `d` of a mate sits at
`d.rank.toIdx + 1 = x.rank.toIdx` by the fit arithmetic
(`forkPointC`'s clause, Orig/MacroInternal.lean:1233), i.e. at rank
− 1, INSIDE `ZoneCleanBelow`'s own sweep — the cover
non-stackability arrives free, exactly as designed.

ROUTE: (i) a fresh zone-row family at the up-census grade — "every
super S-live pair at a fork-qualified world is joint- or
fork-saturated up there" — the owner's "not stackable-away" clause
is `forkPointC`'s ¬satStackable at the covered side, and the
fit-arithmetic leg above pins the cover census; (ii) with (i) the
step is `twinFork_rankStep` (proved above) and the rank rises
strictly; (iii) the maximal anchor (`twinFork_witness_max` below)
terminates the chase at rank 12 — the up-side is vacuous there
(`Rank.toIdx_lt`), the direct form applies, and the witness is the
  world itself (`π = []`, `run []` reads `rfl`).  THE RESIDUE: (i)
  alone. -/
theorem twinFork_upCensus {st : State} (hwf : st.WF) {x : Card}
    (h : TwinFork st x) (hz : ZoneCleanBelow st x)
    {c : Card}
    (hS : CanRaiseS st c) (hgt : c.rank.toIdx > x.rank.toIdx)
    (hcr : CanRaise st c) (hnt : ¬ CanRaise st c.twin) :
    CanRaiseS st c.twin := by
  sorry

/-- **THE MAXIMAL-ANCHOR WITNESS** (the chase's base case, PROVED):
at the maximal rank 12, the super-census is vacuous (no card ranks
past a king), so the direct form's premises carry the whole world
and the twin-fork IS the forkState — the witness at the world
itself, empty play (`run []` reads `rfl`), the parcel read off
`forkState_iff`. -/
theorem twinFork_witness_max {st : State} (hwf : st.WF) {x : Card}
    (hrank : x.rank.toIdx = 12)
    (h : TwinFork st x) (hz : ZoneCleanBelow st x)
    (heq : ∀ c, c ≠ x → c ≠ x.twin → c.rank.toIdx = x.rank.toIdx →
      ¬ CanRaiseS st c) :
    ∃ (y : Card) (F : State) (π : List Move),
      st.run π = some F ∧ ForkWitness F y := by
  have hsup : ∀ c, c.rank.toIdx > x.rank.toIdx → ¬ CanRaiseS st c := by
    intro c hgt
    have hlt := Rank.toIdx_lt c.rank
    rw [hrank] at hgt
    exact absurd hgt (by omega)
  have hf := twinFork_forkState hwf h hz heq hsup
  obtain ⟨y, hwp⟩ := (forkState_iff).1 hf
  exact ⟨y, st, [], rfl, hwp⟩

/-! ## §6. THE CENSUS MEMO

PROBE TABLE (the class rebuilds; the leaf's §8/§9 boards are
file-private, unreachable from Temp — these are verbatim-class
clones):

BOARD | CLASS            | TWINFORK READ                  | CONCLUSION
------+------------------+--------------------------------+-----------------------------
tfA   | fa2 (joint deuce | FALSE — clause 2 dies: the mate | correctly no fork evidence
      | pair, rungs at 1)| is vanilla-live too (joint)    |
tf0   | fa0 (both pairs  | FALSE — clause 2 dies           | correctly no fork evidence
      | double-hot)      |                                |
tfR   | loA (nothing hot)| FALSE — clause 1 dies: the      | correctly no fork evidence
      |                  | spade three has no license      |
tfF   | loF2 (the cover  | TRUE — all three clauses,       | forkState tfF (the PROVED
      | world)           | Prop-certified                 | direct form applied) + the
      |                  |                                | SB readers agree (decided)

DIRECT FORM STATUS: PROVED, with the two named census premises
(`heq` rank-equal thirds, `hsup` super thirds) added to the frozen
shape.  What came free: the family-suit pins (the honest
via-cascade — `twinFork_pin1`/`pin2`/`family_suit_in_pair`), the
pair-membership half, and the witness orientation (`x` itself,
`h.2.1` its mate's vanilla refusal).  What is content: the
third-suit censuses — no banked row closes a third suit's free
rung climb at or above the pair's rank, and the probes at the
joint worlds certify the negative space is real.

EXIST-FORM STATUS: anchor PROVED (`twinFork_witness_max` — rank 12
terminates, `π = []`, the parcel via `forkState_iff`); conditional
rank-step PROVED (`twinFork_rankStep` — assembly only); residue
PRICED [H] (`twinFork_upCensus` — the up-census, with the complete
leak caption and route above). -/

/-! ## §7. The audit battery -/

#print axioms twinForkB_true_iff
#print axioms tfA_wf
#print axioms tf0_wf
#print axioms tfR_wf
#print axioms tfF_wf
#print axioms tfA_noTwinFork
#print axioms tf0_noTwinFork
#print axioms tfR_noTwinFork
#print axioms family_suit_in_pair
#print axioms twinFork_forkState
#print axioms tfF_TwinFork
#print axioms tfF_zoneCleanBelow
#print axioms tfF_zoneCleanEq
#print axioms tfF_zoneCleanSup
#print axioms tfF_fork
#print axioms twinFork_witness_max
#print axioms twinFork_upCensus

/-! ## §11. THE FRONTIER BRIDGE — the deployed-pair answer (2026-10-17)

The "where is the descent-stuck-below-frontier theorem" question,
closed honestly: the twin-side slab at a DEPLOYED pair is the
face-up twin's own unfoundedness — WF's foundation prefixes plus
zone exclusivity make it automatic, for every state whatsoever,
stuck or not, descending or not.  The pinned-foundation refuter
attempted against this bridge was a phantom (its board could only
exist by violating the twin's deployment: founding the twin card
itself), and the attempt is recorded here because its failure
TEACHES the absorption: the 2026-10-12 twin-side refinement —
"the covered twin's side alone carries the content; the x-lift
members are absorbed into the slab" — IS this row.  The descent
program owes the composite nothing on the slab axis; what it
might owe is the STAGING axis (restoring climb material), which
is the live hunt's target, not the phantom. -/

/-- **THE FRONTIER BRIDGE, DEPLOYED FORM**: at a WF state, a
deployed twin already sits below the frontier — the twin-side slab
is the twin's face-up unfoundedness, one instance of the
absorption row `slab_of_faceUp` plus the twin-rank bridge. -/
theorem frontier_of_deployed {st : State} (hwf : st.WF) {x : Card}
    (hfu : ∃ b, x.twin ∈ (st.piles b).faceUp) :
    familyBelowFrontier st x := by
  have h := slab_of_faceUp hwf hfu
  unfold familyBelowFrontier
  rw [(congrArg Rank.toIdx (Card.twin_rank x)).symm]
  exact h

#print axioms frontier_of_deployed

/-! ## §12. THE DESCENT CORPUS TRIPLE — the confirmed bridge
(`descent_corpus_stays_below`, banked 2026-10-17)

The naive form ("descent-stuck ⇒ below-frontier") was a
geometry-from-silence claim: vacuous at deployed pairs (the twin's
own face-up does the work), phantom-refutable off them.  The
confirmed formulation is the corpus/preservation triple, banked
here: the frontier at the start (`frontier_of_deployed` — the
deployment absorption), preservation under every licensed pull
(pulls never found: the giveback drops its own suit's rung by
exactly one, leaves every other suit in place), and the corpus
assembly — with `DescentStuck` as the composite's EXTERNAL stopping
condition, never a premise of the slab law (the stuck-marked
corollary carries it decoratively, mirroring the owner's
formulation verbatim; the clean law does not smuggle it). -/

/-- **A LICENSED PULL'S RUNG LAW** — a fired giveback drops its own
suit's rung by exactly one and leaves every other suit's in place:
the pull never founds. -/
theorem pull_rung {st s' : State} {c : Card} {b : Base}
    (hstep : State.step st (Move.foundToTab c b) = some s') :
    rungAt s' c.suit + 1 = rungAt st c.suit ∧
      ∀ σ : Suit, σ ≠ c.suit → rungAt s' σ = rungAt st σ := by
  obtain ⟨c', htop, hcc, -, hspl⟩ := step_foundToTab_inv hstep
  rw [hcc] at htop
  have hself : s'.found c.suit = chop (st.found c.suit) := by
    rw [hspl, putCard_found]
    exact setFound_found_self
  have hne : ∀ σ : Suit, σ ≠ c.suit → s'.found σ = st.found σ := by
    intro σ hσ
    rw [hspl, putCard_found]
    exact setFound_found_ne hσ
  refine ⟨?_, ?_⟩
  · show (s'.found c.suit).length + 1 = (st.found c.suit).length
    rw [hself]
    have hsnoc : st.found c.suit = chop (st.found c.suit) ++ [c] :=
      lastOf_chop htop
    have hlen := congrArg (fun l : List Card => l.length) hsnoc
    rw [List.length_append, List.length_singleton] at hlen
    exact hlen.symm
  · intro σ hσ
    show (s'.found σ).length = (st.found σ).length
    rw [hne σ hσ]

/-- **THE SLAB SURVIVES A PULL** — the twin-side slab is preserved
(and improved) under every licensed giveback: the pull can only
lower rungs. -/
theorem slab_survives_pull {st s' : State} {c : Card} {b : Base} {x : Card}
    (hstep : State.step st (Move.foundToTab c b) = some s')
    (hslab : familyBelowFrontier st x) :
    familyBelowFrontier s' x := by
  obtain ⟨hdrop, hkeep⟩ := pull_rung hstep
  unfold familyBelowFrontier at hslab ⊢
  by_cases hs : x.twin.suit = c.suit
  · rw [hs] at hslab ⊢
    omega
  · rw [hkeep x.twin.suit hs]
    exact hslab

/-- **THE PULL CORPUS** — a finite sequence of licensed pulls
(`DescentMove`, consumed verbatim from `Orig.ForkDescent`). -/
inductive PullCorpus : State → List Move → State → Prop
  | nil (st : State) : PullCorpus st [] st
  | cons {st s' W : State} {m : Move} {ρ : List Move}
      (hmove : DescentMove st m)
      (hstep : State.step st m = some s')
      (hrest : PullCorpus s' ρ W) :
      PullCorpus st (m :: ρ) W

/-- **THE CORPUS PRESERVES THE SLAB** — the inner invariant: any
pull corpus from a below-frontier world ends below-frontier. -/
theorem pull_corpus_slab {st W : State} {x : Card} {ρ : List Move}
    (hrun : PullCorpus st ρ W) (hslab : familyBelowFrontier st x) :
    familyBelowFrontier W x := by
  induction hrun with
  | nil st' => exact hslab
  | @cons st₀ s' W' m ρ hmove hstep hrest ih =>
      obtain ⟨c₀, b₀, hmEq, -⟩ := hmove
      rw [hmEq] at hstep
      exact ih (slab_survives_pull hstep hslab)

/-- **THE CONFIRMED BRIDGE** — the descent corpus from a deployed
pair ends below the frontier: the triple assembled (deployment
absorption at the start, pull-preservation along the corpus). -/
theorem descent_corpus_stays_below {u W : State} {x : Card} {ρ : List Move}
    (huwf : u.WF) (hdep : ∃ b, x.twin ∈ (u.piles b).faceUp)
    (hrun : PullCorpus u ρ W) :
    familyBelowFrontier W x :=
  pull_corpus_slab hrun (frontier_of_deployed huwf hdep)

/-- **THE STUCK-MARKED READING** — the owner's formulation verbatim:
the corpus ends stuck, and the end world sits below the frontier.
The stuckness is the composite's stopping condition — carried here
decoratively (the clean law above does not use it). -/
theorem descent_corpus_stuck_stays_below {u W : State} {x : Card}
    {ρ : List Move}
    (huwf : u.WF) (hdep : ∃ b, x.twin ∈ (u.piles b).faceUp)
    (hrun : PullCorpus u ρ W)
    (hw : DescentStuck W) :
    familyBelowFrontier W x :=
  descent_corpus_stays_below huwf hdep hrun

#print axioms pull_rung
#print axioms slab_survives_pull
#print axioms pull_corpus_slab
#print axioms descent_corpus_stays_below
#print axioms descent_corpus_stuck_stays_below

/-! ## §13. `below_fork` — THE VOCABULARY NOTE (2026-10-17)

The program-wide below-fork def lives at ITS accessible home —
`Orig/SlabEquiv.lean` §3, the equivalence's own leaf, imported
here — with its three faces banked beside it:

* `below_fork st x` — the below-fork state, clean: the covered
  twin still exists in the tableau (face-up or covered-hidden).
* `below_fork_of_faceUp` — the face-up instance.
* `below_fork_rungFace` — the derived arrangement read at WF.
* `below_fork_iff_rung` — THE CLASS IFF (twin_slab_tableau
  re-plated): along the witness journey the tableau face and the
  rung face are the same fact.

Every premise of the family below consumes `below_fork` as the
SUBSTANTIVE form (§7's `Deployed` clauses, §12's corpus premises
via `frontier_of_deployed`'s face-up leg, the main-goal stack
premise), with the rung fact demoted to its derived face everywhere
it is not the star.  Placement record: LowSlab imports SlabEquiv
directly, so the def flows to LowSlab, ForkDescent, ForkFloor,
ForklessCeiling and here — every fork-program consumer. -/
#print axioms twinFork_witness_max

/- APPEND-MARKER -/
