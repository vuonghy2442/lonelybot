import Orig.PairName

/-!
# Orig.ForkAscent — THE GREEDY SLIDE-STACK ASCENT (forks as exhaustion shapes)

The formalization of the owner's script-claim in the EXHAUSTION
semantics: *from a state below a reachable fork's fork point, greedily
stacking — never founding either member of an intact twin pair,
stacking all the other stuff until none is stackable — the exhaustion
state IS the fork shape: the stuckness is the saturation.*

Why exhaustion beats halt-triggering (v1's design, corrected by the
owner): a run that merely STOPS when twins are detected must still
argue the rest of the board is blocked.  A run that stacks EVERYTHING
ELSE UNTIL IT CANNOT has manufactured the fork's saturation as its own
termination analysis — the only cards left S-live at exhaustion are
guarded pair members, which is literally the `ForkWitness` iff.  No
defusing hypothesis survives.

The claim's anatomy (each piece a definition below):

* **§0 THE VOCABULARY** — the full-time no-eat guard (`MobileTwin`,
  `AscentMove`), the run relation, the exhaustion read (`AscentStuck`),
  and the DELIVERED SHAPE (`TwinSlideHalt`, no longer a trigger: it is
  what the exhaustion must produce — a double-hot intact pair with the
  cover seat fit).
* **§1 THE ORIENTATION ASSEMBLY** (named residue, [M]) — from the
  exhausted saturation (S-live iff the pair) and a fitting mobile
  cover, ONE cargo slide seats the cover on the twin and lands the
  full `ForkWitness` parcel.
* **§2 THE EXHAUSTION ROW** (named residue, [H]) — the main claim:
  from a below-frontier start whose reachable fork's pair members
  are already mobile, every ascent run that runs to leg-exhaustion
  delivers the shape: an intact double-hot pair, S-saturation
  (`CanRaiseS` iff the pair), a fitting mobile cover — hence a fork
  one slide away.

Owner-phrase-to-conjunct map (the `pullEscape` lesson: every
hypothesis load-bearing and documented):

* "don't stack either of them" — the NO-EAT GUARD is FULL-TIME, not a
  halt condition: `AscentMove`'s raise arm declines any member of any
  intact mobile twin pair, at every state along the way.
* "stack other stuff until none is possible" — the END is exhaustion,
  not detection: `AscentStuck` reads "no guarded stackable move is
  legal" (raises and arrangement slides alike); "possible" is graded
  in the §2 route as the SLIDE-AWARE possibility (`CanRaiseS`, the
  program's own {slide · raise} grade): a card raisable after slides
  counts as possible, and the leg-stuck ⇒ S-stuck bridge is the
  row's named hard content.
* "will surely reach a fork state" — confluence grade: EVERY
  exhausted run delivers the shape.
* "below the fork point" (`hbelow`) — the two suits of the reachable
  fork's family sit at-or-below its rank at the start, and BOTH PAIR
  MEMBERS ARE MOBILE AT THE START (face-up).  The mobility premise is
  load-bearing and closes the reveal-gap: a deck whose target pair is
  hidden at the start is fork-reachable only through reveal-commits,
  which the stacking process never performs — no slides or raises of
  the script surface hidden cards — so the claim does not cover it.
  (The fourth suit floats, unconditioned: forks pin only their two
  family suits.)

House compliance: additive leaf (`import Orig.PairName`); definitions
statement-facing; both residues carry complete routes; fresh heads
audited.  Decidability note: all §0 predicates are finite enumerations
over `Card.universe`/`Anchor.all` in the pattern of
`Orig/ForkStateSB.lean`'s `forkStateSB` decider.
-/

/-! ## §0. The vocabulary -/

/-- **THE DOUBLE-HOT READ** — a card and its twin are both face-up on
the tableau, each sitting exactly at its own suit's frontier (each is
that suit's next-up card).  Neither member can be founded at this
configuration: founding is index-exact. -/
def DoubleHot (st : State) (x : Card) : Prop :=
  ∃ (a b : Anchor),
    x ∈ (st.piles a).faceUp ∧
      x.twin ∈ (st.piles b).faceUp ∧
      x.rank.toIdx = st.foundHeight x.suit ∧
      x.twin.rank.toIdx = st.foundHeight x.twin.suit

/-- **THE INTACT-PAIR MOBILITY READ** — `c` pairs with a mobile twin:
`c` and `c.twin` are both face-up and both unfounded, so founding
either member would kill that pair's fork forever.  The guard below
declines any raise of any member of any intact mobile pair. -/
def MobileTwin (st : State) (c : Card) : Prop :=
  (∃ (a : Anchor), c ∈ (st.piles a).faceUp) ∧
    c.rank.toIdx ≥ st.foundHeight c.suit ∧
    (∃ (b : Anchor), c.twin ∈ (st.piles b).faceUp) ∧
    c.twin.rank.toIdx ≥ st.foundHeight c.twin.suit

/-- **THE ASCENT STEP** — the script's full-time stacking discipline
at `st`: either a RAISE of a hot, face-up card that is NOT a member of
any intact mobile twin pair (the no-eat guard, full-time), or a SLIDE
(the arrangement move: expose buried raisables, free seats, open
cover lanes).  The script never pulls (unstacking is the sibling
descent program). -/
def AscentMove (st : State) (m : Move) : Prop :=
  (∃ (c : Card),
      m = Move.tabToFound c ∧
        c.rank.toIdx = st.foundHeight c.suit ∧
        (∃ (a : Anchor), c ∈ (st.piles a).faceUp) ∧
        ∀ (y : Card), MobileTwin st y → c ≠ y ∧ c ≠ y.twin) ∨
  (∃ (c : Card) (b : Base), m = Move.tabToTab c b)

/-- **THE ASCENT RUN** — a finite sequence of ascent steps. -/
inductive AscentRun : State → List Move → State → Prop
  | nil (st : State) : AscentRun st [] st
  | cons {st : State} {m : Move} {s' W : State} {ρ : List Move}
      (hm : AscentMove st m) (hstep : State.step st m = some s')
      (hrest : AscentRun s' ρ W) :
      AscentRun st (m :: ρ) W

/-- **THE EXHAUSTION READ** — the owner's "until none is possible":
no ascent move is legal at `st` (raises and slides alike).  THIS IS
THE ONLY END: the process has no detection-based trigger; it runs
until stuck. -/
def AscentStuck (st : State) : Prop :=
  ∀ (m : Move), AscentMove st m → State.step st m = none

/-- **THE DELIVERED SHAPE** — what an exhaustion state must produce
(the shape the v1 design mistook for a trigger): a double-hot intact
pair together with a fitting, mobile, unfounded COVER — one cargo
slide `tabToTab d (inr x.twin)` away from the covered-twin
orientation. -/
def TwinSlideHalt (st : State) : Prop :=
  ∃ (x d : Card),
    DoubleHot st x ∧
      d.rank.toIdx + 1 = x.rank.toIdx ∧
      d.suit.color ≠ x.suit.color ∧
      d.rank.toIdx ≥ st.foundHeight d.suit ∧
      (∃ (c : Anchor), d ∈ (st.piles c).faceUp) ∧
      canSitOn d x.twin = true

/-! ## §1. The orientation assembly -/

/-- **THE ORIENTATION ASSEMBLY ROW** — from a state whose S-liveness
is exactly an intact pair (the saturation clause of `ForkWitness`,
already delivered) together with a fitting mobile cover, ONE cargo
slide seats the cover on the twin and lands the full fork parcel.

ROUTE ([M]; the assembly is near-direct once the invariances land):

1. THE SLIDE — `tabToTab d (inr x.twin)`: the halt's own fit read
   (`canSitOn d x.twin`) plus the twin's face-up top seat give
   legality (the pile/seat rows); `putRun`'s shape rows give the
   covered-twin pile.
2. THE ORIENTATION — at the slid state, the covered twin is no longer
   a pile top, so ¬CanRaise of the twin (top-ness rows) — the
   orientation pin of `ForkWitness`.
3. THE SATURATION TRANSFER — the fork iff needs `CanRaiseS` iff the
   pair AT THE SLID state: the slide is reversible (the reverse
   slide is its own one-move mirror), so the slid state rides the
   same class; `CanRaiseS` is the {slide · raise}-closed grade by
   construction, so the slide cannot shrink or grow the S-set
   (ForkStateS's design rows — `canRaiseS_runOrTwin` and kin);
   transfer the given iff across the slide and conclude. -/
theorem orientation_assembly_fork {W : State} (hwf : W.WF)
    {x d : Card}
    (hsat : ∀ (c : Card), (c = x ∨ c = x.twin) ↔ CanRaiseS W c)
    (hdhot : DoubleHot W x)
    (hcover : d.rank.toIdx + 1 = x.rank.toIdx ∧
      d.suit.color ≠ x.suit.color ∧
      d.rank.toIdx ≥ W.foundHeight d.suit ∧
      (∃ (c : Anchor), d ∈ (W.piles c).faceUp) ∧
      canSitOn d x.twin = true) :
    ∃ (F : State) (τ : List Move) (x' : Card),
      W.run τ = some F ∧ ForkWitness F x' := by
  sorry

/-! ## §2. The exhaustion row -/

/-- The delivered shape as an explicit pair-plus-cover read (the
`TwinSlideHalt` existential restructured for the exhaustion row's
conclusion binders). -/
def ExhaustShape (st : State) (x d : Card) : Prop :=
  DoubleHot st x ∧
    d.rank.toIdx + 1 = x.rank.toIdx ∧
    d.suit.color ≠ x.suit.color ∧
    d.rank.toIdx ≥ st.foundHeight d.suit ∧
    (∃ (c : Anchor), d ∈ (st.piles c).faceUp) ∧
    canSitOn d x.twin = true

/-- **THE EXHAUSTION-FORKS ROW** — the owner's claim, in the
exhaustion semantics and the confluence grade: from any WF state
below a reachable fork's frontier whose pair members are already
mobile at the start, EVERY ascent run that runs to leg-exhaustion
delivers the shape — an intact double-hot pair whose members are the
only S-live cards, together with a fitting mobile cover — hence a
fork one slide away (§1 assembles it).

ROUTE ([H]; each step priced against banked rows or named sub-rows):

1. THE CLIMB IS INDEX-EXACT AND THE GUARD TRAPS THE FAMILY — raising
   goes one index at a time per suit; crossing rank r on a family
   suit requires founding the r-indexed member; the guard declines
   that forever (the mate is face-up and unfounded along the whole
   run — the script's own moves keep it face-up: no step hides or
   founds pair mates — so `MobileTwin` persists).  Both family suits
   therefore freeze at-or-below r for the whole run, and since the
   members were mobile at the start, the rung walk (`witness_rung_census`-grade
   ledger) reads both frontiers parked exactly at r by exhaustion:
   parking below r is impossible with a frozen climb — whichever
   suit sits below r had its frontier card unreachable, against
   leg-exhaustion (the frontier card is hot and face-up: a stackable
   raise, legal unless guarded — and it is not guarded below r since
   the pair mate only turns guard-relevant at r).  The pair emerges
   double-hot.
2. THE SATURATION IS THE STUCKNESS — every non-pair card at the
   exhaustion state is S-dead: a card S-live at W would carry a
   {slide · raise} witness — a slide prefix then a raise; each slide
   of the prefix is an ascent slide (arrangement moves are script
   members), each aborting raise is a guarded-or-illegal raise whose
   leg-stuck evaluation contradicts `AscentStuck`'s slide-exhaustion
   — the LEG-STUCK ⇒ S-STUCK BRIDGE, the row's named hard content
   (the `cf0` no-left-lift juries and the census's seat-exhaustion
   contrapositive — `excursion_issues_noNewSeat` — price the slide
   prefixes).  Guarded-raise-rejections cut by the same bridge: an
   S-live pair member outside the delivered pair would be an intact
   mobile pair at the frontier, and the exhaustion's frontier
   bookkeeping (step 1) leaves exactly one such pair.
3. THE COVER — the delivered pair's fitting cover cells: the
   `r−1`-index cards of the opposite family; mobility read at the
   exhaustion state the same way (the census rows price which covers
   survived the climb's seating loans); the fit is `canSitOn`.
4. THE ASSEMBLY — §1 with the delivered saturation, shape and
   cover.

Falsification boards (the refuter-first targets): ladder-exhaustion
decks — greedy slide-wasting runs, buried-cover exhaustions,
multi-pair frontiers — assigned to the probe program alongside the
descent program's boards. -/
theorem ascent_exhaustion_forks {s : State} (hwf : s.WF)
    (hbelow : ∃ (F : State) (x : Card) (π : List Move),
      s.run π = some F ∧ ForkWitness F x ∧
        rungAt s x.suit ≤ x.rank.toIdx ∧
        rungAt s x.twin.suit ≤ x.rank.toIdx ∧
        (∃ (a : Anchor), x ∈ (s.piles a).faceUp) ∧
        (∃ (b : Anchor), x.twin ∈ (s.piles b).faceUp))
    {ρ : List Move} {W : State}
    (hrun : AscentRun s ρ W)
    (hstuck : AscentStuck W) :
    ∃ (x d : Card),
      ExhaustShape W x d ∧
      (∀ (c : Card), (c = x ∨ c = x.twin) ↔ CanRaiseS W c) :=
  sorry

/-! ## The audit battery

`#print axioms` per fresh head: the §0 vocabulary rows are
statement-facing definitions elaborated here; the §1 assembly row
and the §2 exhaustion row are the file's two named residues — each
carries exactly one `sorryAx` with its complete route in the
docstring; nothing else flows into them from this file. -/

#print axioms orientation_assembly_fork
#print axioms ascent_exhaustion_forks
