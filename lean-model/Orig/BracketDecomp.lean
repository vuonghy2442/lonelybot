import Orig.ForkWeaker

/-!
# Orig.BracketDecomp — THE BRACKET DECOMPOSITION of equal-tuple journeys

A reversible journey whose endpoints share their height tuple
(`∀ σ, rungAt st σ = rungAt w σ`) factors into CARGO LEGS interleaved
with CONJUGATE-SHAPED BRACKETS — `raise · slides · pull` of the same
card, or its reverse `pull · slides · raise` (a card that leaves the
foundation and comes back).  The content is the per-suit STACK
DISCIPLINE: the pull letter (`foundToTab`) pops the CURRENT TOP of
its suit's foundation (`step_foundToTab_inv`'s guard
`foundTop = some c`), and the raise letter appends — so along a
witness journey each suit's foundation behaves as a STACK: every
pull pops the most recently raised still-resident card of its suit,
and the matched (raise, pull) pairs are per-suit well-nested.

THE LETTERS, graded honestly (the task sketch said "slide" for the
interior legs; the honest letter is slightly wider and this file
proves everything it states):

* **phase** — a block of FLAT legs: reversible `tabToTab` slides
  (each `FlatStep.cargo` by its own `reversibleAtW` witness) and
  draw loops (`FlatStep.draw`: the phase rotations — banked as the
  fiber algebra's second flat letter).  Draws genuinely ride lawful
  witness journeys (the draw cycle loops back), so the interior of a
  bracket, stated at the journey grade, is a `FlatPath`, not a bare
  `CargoPath`; under a draw-free journey premise every block here
  degenerates to pure cargo (route: the `FlatStep.cargo` kind
  census over the block).
* **bracket** — `BracketW`: raise `c`, then a cargo interior, then
  pull `c` (THE TASK'S LETTER, kept verbatim), and `BracketWFlat`:
  the honest journey-grade letter with a flat interior.
* **bracketRev** — `BracketRW`: the reversed excursion (pull · flat ·
  raise of the same card).  It is needed for honesty: a witness
  journey may PULL a founded card down and re-raise the SAME card
  later (`rung_found_congr` forces the same-card cycle), which no
  raise-first-only letter can express.
* **BracketClosure** — the closure under phase-blocks, brackets,
  reverse brackets, and sequencing; the task's `cargo` letter is
  kept as its own constructor (a `CargoPath` block segment).

WHAT IS PROVED HERE (all banked-grade, zero sorry):

* §1 THE LIFO PULL LAW: a pull pops the current top — the card most
  recently raised on its suit and still resident — read directly
  off the step guard (`step_foundToTab_inv`, `Orig/Irreversible.lean:555`);
  the correlated raise row: a raise makes the raised card the top.
* §2 THE JOURNEY CENSUS: along a witness shuffle the waste letters
  never ride (`journey_never_wasteToFound`/`journey_never_wasteToTab`,
  consumed from `Orig/ForkStateUniqGate`), so per suit the rungs move
  only by the raise/pull letters, and at an equal-tuple pair of
  endpoints every suit's raise count equals its pull count.
* §3 THE FLAT FACTORS: a quiet journey (no raises, no pulls) is a
  `FlatPath`; a raise-free journey with one pull factors as
  `flat · pull · flat` (the pulled card forced by the current top),
  and dually for the raise.
* §4 THE ONE-BRACKET DECOMPOSITION: an equal-tuple witness journey
  with at most ONE raise leg is: all flat; or
  `flat · raise c · flat · pull c · flat` (same card, by the LIFO
  law); or `flat · pull x · flat · raise x · flat` (same card, by
  the `rung_found_prefix` stack-discipline).  Membership in the
  closure follows.
* §5 THE MAIN DECOMPOSITION `reversible_equaltuple_decompose`: the
  N-bracket assembly — stated over the full closure, left as the
  NAMED RESIDUE `decompose_residue_nesting` with its route (the
  per-suit Dyck serialization, nested-bracket recursion, and the
  crossing-deroute step that still prices bracket commutation).

House note: `Orig/SFlatTransfer.lean` (landed tonight:
`S_census_one_leg`, `forkState_mate_S`) is not consumed here — this
card runs on the fork-universe census battery already below
`ForkWeaker`; `Orig/SConjugate.lean` is in sibling flux and is
neither imported nor needed (its ideas — the same-card cycle — are
re-derived from `rung_found_prefix` directly).
-/

/-! ## §0. The private kit

Per-leg readers copied to this leaf per the house dedup discipline:
MacroInternal's rung-write rows are private there, so the four
write-shapes are re-derived here from the public step inversions
(`Orig/Irreversible.lean`) — slides/draws write no foundation, the
raise writes its suit up one, the pull writes its suit down one. -/

/-! ### The per-leg rung ledger -/

/-- A run relocation (`tabToTab`) writes no foundation: every rung
levels (the move relocates a face-up run; `putRun`/`setPile` never
touch `found`). -/
private theorem ledger_tabToTab {st st' : State} {c : Card} {b : Base}
    (hstep : State.step st (Move.tabToTab c b) = some st') :
    ∀ s, rungAt st' s = rungAt st s := by
  obtain ⟨a, -, -, -, hs⟩ := step_tabToTab_inv hstep
  intro s
  show (st'.found s).length = (st.found s).length
  have hf : st'.found = st.found := by
    rw [hs, show ((st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
          (fromCard c (st.piles a).faceUp) b).found
          = (st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).found from
      putRun_found _ _ _]
    rw [setPile_found]
  rw [hf]

/-- A draw writes no foundation (the deal touches stock/waste only). -/
private theorem ledger_draw {st st' : State}
    (hstep : st.step .draw = some st') :
    ∀ s, rungAt st' s = rungAt st s := by
  intro s
  show (st'.found s).length = (st.found s).length
  rw [stepDraw_found hstep]

/-- The pull's landing shape: the foundation's suit row is the
chopped pre-row (the `putCard` placement writes no foundation). -/
private theorem foundToTab_found_self {st s' : State} {c : Card} {b : Base}
    (hstep : State.step st (Move.foundToTab c b) = some s') :
    s'.found c.suit = chop (st.found c.suit) ∧
      ∀ σ, σ ≠ c.suit → s'.found σ = st.found σ := by
  obtain ⟨-, htop, -, -, hs⟩ := step_foundToTab_inv hstep
  refine ⟨?_, ?_⟩
  · rw [hs]
    show ((st.setFound c.suit (chop (st.found c.suit))).putCard c b).found c.suit
      = chop (st.found c.suit)
    rw [show ((st.setFound c.suit (chop (st.found c.suit))).putCard c b).found
        = (st.setFound c.suit (chop (st.found c.suit))).found from
        putCard_found _ _ _]
    exact setFound_found_self
  · intro σ hσ
    rw [hs]
    show ((st.setFound c.suit (chop (st.found c.suit))).putCard c b).found σ
      = st.found σ
    rw [show ((st.setFound c.suit (chop (st.found c.suit))).putCard c b).found
        = (st.setFound c.suit (chop (st.found c.suit))).found from
        putCard_found _ _ _]
    exact setFound_found_ne hσ

/-- A foundation giveback writes exactly one rung: its suit's row is
the chopped prefix, so the rung falls by exactly one (the guard's
`foundTop` read pins the popped row's last card, `lastOf_chop`),
every other rung levels. -/
private theorem ledger_foundToTab {st st' : State} {c : Card} {b : Base}
    (hstep : State.step st (Move.foundToTab c b) = some st') :
    rungAt st c.suit = rungAt st' c.suit + 1 ∧
      ∀ s, s ≠ c.suit → rungAt st' s = rungAt st s := by
  obtain ⟨hself, hothers⟩ := foundToTab_found_self hstep
  obtain ⟨c', htop, hc'c, -, -⟩ := step_foundToTab_inv hstep
  rw [hc'c] at htop
  have hlast : lastOf (st.found c.suit) = some c := htop
  have hsnoc : st.found c.suit = chop (st.found c.suit) ++ [c] :=
    lastOf_chop hlast
  have hlen : (st.found c.suit).length = (chop (st.found c.suit)).length + 1 := by
    have hl := congrArg (List.length) hsnoc
    rw [List.length_append] at hl
    have h1 : ([c] : List Card).length = 1 := rfl
    omega
  refine ⟨?_, ?_⟩
  · show (st.found c.suit).length = (st'.found c.suit).length + 1
    rw [hself]
    omega
  · intro s hs
    show (st'.found s).length = (st.found s).length
    rw [hothers s hs]

/-- The raise's landing shape: the named suit row is extended by the
raised card, every other row stays (consumes the banked
`tabToFound_found_trio`). -/
private theorem tabToFound_found_pair {st s' : State} {c : Card}
    (hstep : State.step st (Move.tabToFound c) = some s') :
    s'.found c.suit = st.found c.suit ++ [c] ∧
      ∀ σ, σ ≠ c.suit → s'.found σ = st.found σ := by
  obtain ⟨-, a, -, hs⟩ := step_tabToFound_inv hstep
  obtain ⟨hself, hothers, -⟩ := tabToFound_found_trio (a := a) hs
  exact ⟨hself, hothers⟩

/-- A foundation raise writes exactly one rung: its suit's row grows
by the raised card, so the rung rises by one; every other rung
levels. -/
private theorem ledger_tabToFound {st st' : State} {c : Card}
    (hstep : State.step st (Move.tabToFound c) = some st') :
    rungAt st' c.suit = rungAt st c.suit + 1 ∧
      ∀ s, s ≠ c.suit → rungAt st' s = rungAt st s := by
  obtain ⟨hself, hothers⟩ := tabToFound_found_pair hstep
  refine ⟨?_, ?_⟩
  · show (st'.found c.suit).length = (st.found c.suit).length + 1
    rw [hself, List.length_append]
    have h1 : ([c] : List Card).length = 1 := rfl
    omega
  · intro s hs
    show (st'.found s).length = (st.found s).length
    rw [hothers s hs]

/-! ### The flat legs write no foundation -/

/-- Every flat letter preserves every foundation row pointwise: cargo
relocations and draw loops never touch `found` (the two non-writer
letters of the ledger). -/
private theorem flatStep_found {st s' : State} (h : FlatStep st s') (σ : Suit) :
    s'.found σ = st.found σ := by
  cases h with
  | cargo c b hstep _hrev =>
      obtain ⟨a, -, -, -, hs⟩ := step_tabToTab_inv hstep
      rw [hs]
      show ((st.setPile a
          (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
            (fromCard c (st.piles a).faceUp) b).found σ = st.found σ
      rw [show ((st.setPile a
          (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
            (fromCard c (st.piles a).faceUp) b).found
          = (st.setPile a
          (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).found from
        putRun_found _ _ _]
      rw [setPile_found]
  | draw hstep _hrev =>
      have hd : st.stepDraw = some s' := hstep
      rw [stepDraw_found hd]

/-- A flat path preserves every foundation row pointwise (the leg
row, lifted through the path). -/
theorem flatPath_found {st w : State} (h : FlatPath st w) (σ : Suit) :
    w.found σ = st.found σ := by
  induction h with
  | refl u => rfl
  | cons hs _t ih => exact ih.trans (flatStep_found hs σ)

/-- A flat path preserves every rung (the pointwise row, read at
length). -/
theorem flatPath_rungs {st w : State} (h : FlatPath st w) (σ : Suit) :
    rungAt w σ = rungAt st σ := by
  show (w.found σ).length = (st.found σ).length
  rw [flatPath_found h σ]

/-- A flat path preserves the current top of every suit's foundation
(the pointwise row, read at `foundTop`). -/
theorem flatPath_foundTop {st w : State} (h : FlatPath st w) (σ : Suit) :
    w.foundTop σ = st.foundTop σ := by
  show lastOf (w.found σ) = lastOf (st.found σ)
  rw [flatPath_found h σ]

/-! ### The leg counters -/

/-- The number of `tabToFound` legs of suit `σ` in a play. -/
def raisesOf : List Move → Suit → Nat
  | [], _ => 0
  | Move.tabToFound c :: t, σ => (if c.suit = σ then 1 else 0) + raisesOf t σ
  | _ :: t, σ => raisesOf t σ

/-- The number of `foundToTab` legs of suit `σ` in a play. -/
def pullsOf : List Move → Suit → Nat
  | [], _ => 0
  | Move.foundToTab c _ :: t, σ => (if c.suit = σ then 1 else 0) + pullsOf t σ
  | _ :: t, σ => pullsOf t σ

/-- The total number of `tabToFound` legs in a play. -/
def raiseTotal : List Move → Nat
  | [] => 0
  | Move.tabToFound _ :: t => raiseTotal t + 1
  | _ :: t => raiseTotal t

/-- The total number of `foundToTab` legs in a play. -/
def pullTotal : List Move → Nat
  | [] => 0
  | Move.foundToTab _ _ :: t => pullTotal t + 1
  | _ :: t => pullTotal t

/-! The cons-rows of the counters: each a definitional read at its own
constructor, and the uniform pass-through rows for the other
constructors (each reduces by the catch-all arm). -/

private theorem raisesOf_cons_raise {c : Card} {t : List Move} (σ : Suit) :
    raisesOf (Move.tabToFound c :: t) σ =
      (if c.suit = σ then 1 else 0) + raisesOf t σ := rfl

private theorem raisesOf_cons_draw {t : List Move} (σ : Suit) :
    raisesOf (Move.draw :: t) σ = raisesOf t σ := rfl

private theorem raisesOf_cons_wasteToFound {c : Card} {t : List Move} (σ : Suit) :
    raisesOf (Move.wasteToFound c :: t) σ = raisesOf t σ := rfl

private theorem raisesOf_cons_wasteToTab {c : Card} {b : Base} {t : List Move}
    (σ : Suit) : raisesOf (Move.wasteToTab c b :: t) σ = raisesOf t σ := rfl

private theorem raisesOf_cons_pull {c : Card} {b : Base} {t : List Move}
    (σ : Suit) : raisesOf (Move.foundToTab c b :: t) σ = raisesOf t σ := rfl

private theorem raisesOf_cons_tabToTab {c : Card} {b : Base} {t : List Move}
    (σ : Suit) : raisesOf (Move.tabToTab c b :: t) σ = raisesOf t σ := rfl

private theorem raisesOf_nil (σ : Suit) : raisesOf [] σ = 0 := rfl

private theorem pullsOf_cons_pull {c : Card} {b : Base} {t : List Move} (σ : Suit) :
    pullsOf (Move.foundToTab c b :: t) σ =
      (if c.suit = σ then 1 else 0) + pullsOf t σ := rfl

private theorem pullsOf_cons_draw {t : List Move} (σ : Suit) :
    pullsOf (Move.draw :: t) σ = pullsOf t σ := rfl

private theorem pullsOf_cons_wasteToFound {c : Card} {t : List Move} (σ : Suit) :
    pullsOf (Move.wasteToFound c :: t) σ = pullsOf t σ := rfl

private theorem pullsOf_cons_wasteToTab {c : Card} {b : Base} {t : List Move}
    (σ : Suit) : pullsOf (Move.wasteToTab c b :: t) σ = pullsOf t σ := rfl

private theorem pullsOf_cons_raise {c : Card} {t : List Move} (σ : Suit) :
    pullsOf (Move.tabToFound c :: t) σ = pullsOf t σ := rfl

private theorem pullsOf_cons_tabToTab {c : Card} {b : Base} {t : List Move}
    (σ : Suit) : pullsOf (Move.tabToTab c b :: t) σ = pullsOf t σ := rfl

private theorem pullsOf_nil (σ : Suit) : pullsOf [] σ = 0 := rfl

private theorem raiseTotal_cons_raise {c : Card} {t : List Move} :
    raiseTotal (Move.tabToFound c :: t) = raiseTotal t + 1 := rfl

private theorem raiseTotal_cons_draw {t : List Move} :
    raiseTotal (Move.draw :: t) = raiseTotal t := rfl

private theorem raiseTotal_cons_wasteToFound {c : Card} {t : List Move} :
    raiseTotal (Move.wasteToFound c :: t) = raiseTotal t := rfl

private theorem raiseTotal_cons_wasteToTab {c : Card} {b : Base} {t : List Move} :
    raiseTotal (Move.wasteToTab c b :: t) = raiseTotal t := rfl

private theorem raiseTotal_cons_pull {c : Card} {b : Base} {t : List Move} :
    raiseTotal (Move.foundToTab c b :: t) = raiseTotal t := rfl

private theorem raiseTotal_cons_tabToTab {c : Card} {b : Base} {t : List Move} :
    raiseTotal (Move.tabToTab c b :: t) = raiseTotal t := rfl

private theorem raiseTotal_nil : raiseTotal [] = 0 := rfl

private theorem pullTotal_cons_pull {c : Card} {b : Base} {t : List Move} :
    pullTotal (Move.foundToTab c b :: t) = pullTotal t + 1 := rfl

private theorem pullTotal_cons_draw {t : List Move} :
    pullTotal (Move.draw :: t) = pullTotal t := rfl

private theorem pullTotal_cons_wasteToFound {c : Card} {t : List Move} :
    pullTotal (Move.wasteToFound c :: t) = pullTotal t := rfl

private theorem pullTotal_cons_wasteToTab {c : Card} {b : Base} {t : List Move} :
    pullTotal (Move.wasteToTab c b :: t) = pullTotal t := rfl

private theorem pullTotal_cons_raise {c : Card} {t : List Move} :
    pullTotal (Move.tabToFound c :: t) = pullTotal t := rfl

private theorem pullTotal_cons_tabToTab {c : Card} {b : Base} {t : List Move} :
    pullTotal (Move.tabToTab c b :: t) = pullTotal t := rfl

private theorem pullTotal_nil : pullTotal [] = 0 := rfl

/-- A raise leg contributes to its own suit's count only. -/
private theorem raisesOf_cons_ne {c : Card} {t : List Move} {σ : Suit}
    (h : c.suit ≠ σ) :
    raisesOf (Move.tabToFound c :: t) σ = raisesOf t σ := by
  rw [raisesOf_cons_raise, ite_eq_right h]
  omega

/-- A pull leg contributes to its own suit's count only. -/
private theorem pullsOf_cons_ne {c : Card} {b : Base} {t : List Move} {σ : Suit}
    (h : c.suit ≠ σ) :
    pullsOf (Move.foundToTab c b :: t) σ = pullsOf t σ := by
  rw [pullsOf_cons_pull, ite_eq_right h]
  omega

/-- A raise leg's own suit's count strictly grows. -/
private theorem raisesOf_cons_self {c : Card} {t : List Move} :
    raisesOf (Move.tabToFound c :: t) c.suit = raisesOf t c.suit + 1 := by
  rw [raisesOf_cons_raise, ite_eq_left rfl]
  omega

/-- A pull leg's own suit's count strictly grows. -/
private theorem pullsOf_cons_self {c : Card} {b : Base} {t : List Move} :
    pullsOf (Move.foundToTab c b :: t) c.suit = pullsOf t c.suit + 1 := by
  rw [pullsOf_cons_pull, ite_eq_left rfl]
  omega

/-- The per-suit raise count never exceeds the total. -/
theorem raisesOf_le_raiseTotal : ∀ (L : List Move) (σ : Suit),
    raisesOf L σ ≤ raiseTotal L := by
  intro L
  induction L with
  | nil => intro σ; exact Nat.le_of_eq (raisesOf_nil σ)
  | cons m t ih =>
      intro σ
      cases m with
      | draw => rw [raisesOf_cons_draw, raiseTotal_cons_draw]; exact ih σ
      | wasteToFound c => rw [raisesOf_cons_wasteToFound, raiseTotal_cons_wasteToFound]; exact ih σ
      | wasteToTab c b => rw [raisesOf_cons_wasteToTab, raiseTotal_cons_wasteToTab]; exact ih σ
      | tabToFound c =>
          have hih := ih σ
          rw [raisesOf_cons_raise, raiseTotal_cons_raise]
          by_cases hc : c.suit = σ
          · rw [ite_eq_left hc]; omega
          · rw [ite_eq_right hc]; omega
      | foundToTab c b => rw [raisesOf_cons_pull, raiseTotal_cons_pull]; exact ih σ
      | tabToTab c b => rw [raisesOf_cons_tabToTab, raiseTotal_cons_tabToTab]; exact ih σ

/-- Two suits' raise counts together never exceed the total (one leg
carries one suit). -/
theorem raisesOf_pair_le_raiseTotal {σ σ' : Suit} (hne : σ ≠ σ') :
    ∀ (L : List Move), raisesOf L σ + raisesOf L σ' ≤ raiseTotal L := by
  intro L
  induction L with
  | nil => simp [raisesOf_nil, raiseTotal_nil]
  | cons m t ih =>
      cases m with
      | draw =>
          rw [raisesOf_cons_draw, raisesOf_cons_draw, raiseTotal_cons_draw]
          exact ih
      | wasteToFound c =>
          rw [raisesOf_cons_wasteToFound, raisesOf_cons_wasteToFound,
            raiseTotal_cons_wasteToFound]
          exact ih
      | wasteToTab c b =>
          rw [raisesOf_cons_wasteToTab, raisesOf_cons_wasteToTab,
            raiseTotal_cons_wasteToTab]
          exact ih
      | tabToFound c =>
          rw [raisesOf_cons_raise σ, raisesOf_cons_raise σ', raiseTotal_cons_raise]
          have hih : raisesOf t σ ≤ raiseTotal t := raisesOf_le_raiseTotal t σ
          have hih2 : raisesOf t σ' ≤ raiseTotal t := raisesOf_le_raiseTotal t σ'
          by_cases h1 : c.suit = σ
          · have h2 : c.suit ≠ σ' := fun hcon => hne (h1.symm.trans hcon)
            rw [ite_eq_left h1, ite_eq_right h2]
            omega
          · by_cases h2 : c.suit = σ'
            · rw [ite_eq_right h1, ite_eq_left h2]
              omega
            · rw [ite_eq_right h1, ite_eq_right h2]
              omega
      | foundToTab c b =>
          rw [raisesOf_cons_pull, raisesOf_cons_pull, raiseTotal_cons_pull]
          exact ih
      | tabToTab c b =>
          rw [raisesOf_cons_tabToTab, raisesOf_cons_tabToTab, raiseTotal_cons_tabToTab]
          exact ih

/-! ## §1. THE LIFO PULL LAW

The headline read, one step-guard long: a pull (`foundToTab`) pops the
CURRENT TOP of its pile — the card most recently raised on its suit
and still resident.  Every later row of this card composes this law
with the flat legs' found-preservation. -/

/-- **THE LIFO PULL LAW** — a pull (`foundToTab`) pops the CURRENT TOP
of its pile: the step's own guard names the popped card as the
foundation's current top (`step_foundToTab_inv`,
`Orig/Irreversible.lean:555`), i.e. the card most recently raised on
its suit and still resident. -/
theorem foundToTab_pops_currentTop {st : State} {c : Card} {b : Base} {s' : State}
    (h : State.step st (Move.foundToTab c b) = some s') :
    st.foundTop c.suit = some c := by
  obtain ⟨c', htop, hc'c, -, -⟩ := step_foundToTab_inv h
  rw [hc'c] at htop
  exact htop

/-- **The correlated raise row** — a raise makes the raised card the
CURRENT TOP of its suit's foundation: the append writes it at the
stack's end (`lastOf_snoc` through the landing record). -/
theorem tabToFound_tops_currentSuit {st s' : State} {c : Card}
    (h : State.step st (Move.tabToFound c) = some s') :
    s'.foundTop c.suit = some c := by
  obtain ⟨hself, -⟩ := tabToFound_found_pair h
  show lastOf (s'.found c.suit) = some c
  rw [hself]
  exact lastOf_snoc

/-- The pull's landing keeps every OTHER suit's current top in place
(the chopped row is the other suit's untouched row). -/
theorem foundToTab_keepsOtherTops {st s' : State} {c : Card} {b : Base}
    (h : State.step st (Move.foundToTab c b) = some s') :
    ∀ σ, σ ≠ c.suit → s'.foundTop σ = st.foundTop σ := by
  obtain ⟨-, hothers⟩ := foundToTab_found_self h
  intro σ hσ
  show lastOf (s'.found σ) = lastOf (st.found σ)
  rw [hothers σ hσ]

/-- The raise's landing keeps every OTHER suit's current top in place
(the extended row is the other suit's untouched row). -/
theorem tabToFound_keepsOtherTops {st s' : State} {c : Card}
    (h : State.step st (Move.tabToFound c) = some s') :
    ∀ σ, σ ≠ c.suit → s'.foundTop σ = st.foundTop σ := by
  obtain ⟨-, hothers⟩ := tabToFound_found_pair h
  intro σ hσ
  show lastOf (s'.found σ) = lastOf (st.found σ)
  rw [hothers σ hσ]

/-! ## §2. THE JOURNEY CENSUS

Along a witness shuffle the waste letters never ride (the banked
irreversibility census `journey_never_wasteToFound` /
`journey_never_wasteToTab`, consumed from `Orig/ForkStateUniqGate`),
the slides and draws write no foundation, the raise lifts exactly its
own suit's rung, and the pull lowers exactly its own suit's rung — so
every suit's rung ledger closes additively along the journey. -/

/-- **THE JOURNEY CENSUS** (per suit, additive form): along a witness
shuffle, `rungAt end + pulls = rungAt start + raises` per suit. -/
theorem witness_rung_census {st : State} : ∀ {play : List Move} {w : State},
    ShufflePlayW st play w →
    ∀ σ, rungAt w σ + pullsOf play σ = rungAt st σ + raisesOf play σ := by
  intro play w h
  induction h with
  | nil u => intro σ; rfl
  | @cons u m s₁ rest w' hrev hstep hrest ih =>
      intro σ
      have hih := ih σ
      cases m with
      | draw =>
          have hl := ledger_draw hstep σ
          have h1 : raisesOf (Move.draw :: rest) σ = raisesOf rest σ := rfl
          have h2 : pullsOf (Move.draw :: rest) σ = pullsOf rest σ := rfl
          omega
      | wasteToFound c =>
          exact absurd hrev (journey_never_wasteToFound hstep)
      | wasteToTab c b =>
          exact absurd hrev (journey_never_wasteToTab hstep)
      | tabToFound c =>
          obtain ⟨hup, hothers⟩ := ledger_tabToFound hstep
          have h2 : pullsOf (Move.tabToFound c :: rest) σ = pullsOf rest σ := rfl
          by_cases hσ : σ = c.suit
          · subst hσ
            have h1 := raisesOf_cons_self (c := c) (t := rest)
            omega
          · have h1 : raisesOf (Move.tabToFound c :: rest) σ = raisesOf rest σ :=
              raisesOf_cons_ne (fun hcon => hσ hcon.symm)
            have h3 := hothers σ (fun hcon => hσ hcon)
            omega
      | foundToTab c b =>
          obtain ⟨hdown, hothers⟩ := ledger_foundToTab hstep
          have h1 : raisesOf (Move.foundToTab c b :: rest) σ = raisesOf rest σ := rfl
          by_cases hσ : σ = c.suit
          · subst hσ
            have h2 := pullsOf_cons_self (c := c) (b := b) (t := rest)
            omega
          · have h2 : pullsOf (Move.foundToTab c b :: rest) σ = pullsOf rest σ :=
              pullsOf_cons_ne (fun hcon => hσ hcon.symm)
            have h3 := hothers σ (fun hcon => hσ hcon)
            omega
      | tabToTab c b =>
          have hl := ledger_tabToTab hstep σ
          have h1 : raisesOf (Move.tabToTab c b :: rest) σ = raisesOf rest σ := rfl
          have h2 : pullsOf (Move.tabToTab c b :: rest) σ = pullsOf rest σ := rfl
          omega

/-- **At an equal-tuple pair of endpoints the census closes**: every
suit's raise count equals its pull count along the forward witness
play — the counting face of "every raise is matched". -/
theorem witness_tuple_census {st : State} {play : List Move} {w : State}
    (h : ShufflePlayW st play w)
    (htup : ∀ σ, rungAt st σ = rungAt w σ) (σ : Suit) :
    raisesOf play σ = pullsOf play σ := by
  have hc := witness_rung_census h σ
  have ht := htup σ
  omega

/-! ## §3. THE FLAT FACTORS

The interior splitters the bracket assembly consumes: a quiet journey
is a `FlatPath`; a raise-free journey carrying exactly one pull
factors as `flat · pull · flat` with the pulled card forced by the
LIFO guard; dually, a pull-free prefix journey carrying exactly one
raise factors as `flat · raise · flat` with the raised card forced by
the foundation-prefix discipline (`rung_found_prefix`). -/

/-- A QUIET journey is a `FlatPath`: with every raise count and every
pull count at zero, the waste census (`journey_never_wasteToFound` /
`journey_never_wasteToTab`) leaves only the two flat letters, each
realizing as `FlatStep.cargo` / `FlatStep.draw` with its own leg's
reversibility witness. -/
theorem quiet_flat {st : State} : ∀ {play : List Move} {w : State},
    ShufflePlayW st play w →
    (∀ σ, raisesOf play σ = 0) → (∀ σ, pullsOf play σ = 0) →
    FlatPath st w := by
  intro play w h
  induction h with
  | nil u =>
      intro _ _
      exact FlatPath.refl u
  | @cons u m s₁ rest w' hrev hstep hrest ih =>
      intro hq1 hq2
      cases m with
      | draw =>
          have hr' : ∀ σ, raisesOf rest σ = 0 := fun σ => by
            have h0 := hq1 σ; rwa [raisesOf_cons_draw] at h0
          have hp' : ∀ σ, pullsOf rest σ = 0 := fun σ => by
            have h0 := hq2 σ; rwa [pullsOf_cons_draw] at h0
          exact FlatPath.cons (FlatStep.draw hstep hrev) (ih hr' hp')
      | wasteToFound c => exact absurd hrev (journey_never_wasteToFound hstep)
      | wasteToTab c b => exact absurd hrev (journey_never_wasteToTab hstep)
      | tabToFound c =>
          exfalso
          have h0 := hq1 c.suit
          rw [raisesOf_cons_self] at h0
          omega
      | foundToTab c b =>
          exfalso
          have h0 := hq2 c.suit
          rw [pullsOf_cons_self] at h0
          omega
      | tabToTab c b =>
          have hr' : ∀ σ, raisesOf rest σ = 0 := fun σ => by
            have h0 := hq1 σ; rwa [raisesOf_cons_tabToTab] at h0
          have hp' : ∀ σ, pullsOf rest σ = 0 := fun σ => by
            have h0 := hq2 σ; rwa [pullsOf_cons_tabToTab] at h0
          exact FlatPath.cons (FlatStep.cargo c b hstep hrev) (ih hr' hp')

/-- The flat legs preserve the current top of every suit's foundation
(the pointwise row, read at `foundTop`). -/
private theorem flatStep_foundTop {st s' : State} (h : FlatStep st s') (σ : Suit) :
    s'.foundTop σ = st.foundTop σ := by
  show lastOf (s'.found σ) = lastOf (st.found σ)
  rw [flatStep_found h σ]

/-- Cancellation of a common front: equal snoc-tails end equal (the
`lastOf` read of `append`). -/
private theorem snoc_cancel {l1 : List Card} {a b : Card}
    (h : l1 ++ [a] = l1 ++ [b]) : a = b := by
  have h1 : lastOf (l1 ++ [a]) = some a := lastOf_snoc
  have h2 : lastOf (l1 ++ [b]) = some b := lastOf_snoc
  rw [h] at h1
  exact Option.some.inj (h1.symm.trans h2)

/-- **THE FLAT PULL FACTOR** — the bracket-interior splitter.  In a
raise-free witness journey whose ONLY pull is of suit `top.suit`
(exactly one leg, all other suits at zero), `top` being the CURRENT
TOP of that suit at the journey's start (the raised card whose
bracket this pull closes — `tabToFound_tops_currentSuit` supplies it
at the call site), the journey factors as `flat · pull-of-top · flat`
with the pulled card forced equal to `top`: the flats preserve every
foundation row, so the LIFO guard reads the unchanged top. -/
theorem pull_factor {top : Card} : ∀ {st : State} {play : List Move} {w : State},
    ShufflePlayW st play w →
    st.foundTop top.suit = some top →
    (∀ σ, raisesOf play σ = 0) →
    (pullsOf play top.suit = 1) →
    (∀ σ, σ ≠ top.suit → pullsOf play σ = 0) →
    ∃ (u v : State) (bs : Base),
      FlatPath st u ∧
      State.step u (Move.foundToTab top bs) = some v ∧
      FlatPath v w := by
  intro st play w h
  induction h with
  | nil u =>
      intro _ _ _ hp1
      exfalso
      have h0 : pullsOf ([] : List Move) top.suit = 0 := rfl
      omega
  | @cons u m s₁ rest w' hrev hstep hrest ih =>
      intro htop hq1 hp1 hp2
      cases m with
      | draw =>
          have htop' : s₁.foundTop top.suit = some top :=
            (flatStep_foundTop (FlatStep.draw hstep hrev) top.suit).trans htop
          obtain ⟨u2, v2, bs2, pre, hf, post⟩ :=
            ih htop'
              (fun σ => by have h0 := hq1 σ; rwa [raisesOf_cons_draw] at h0)
              (by have h0 := hp1; rwa [pullsOf_cons_draw] at h0)
              (fun σ hσ => by
                have h0 := hp2 σ hσ; rwa [pullsOf_cons_draw] at h0)
          exact ⟨u2, v2, bs2, FlatPath.cons (FlatStep.draw hstep hrev) pre, hf, post⟩
      | wasteToFound c => exact absurd hrev (journey_never_wasteToFound hstep)
      | wasteToTab c b => exact absurd hrev (journey_never_wasteToTab hstep)
      | tabToFound c =>
          exfalso
          have h0 := hq1 c.suit
          rw [raisesOf_cons_self] at h0
          omega
      | foundToTab d bs0 =>
          by_cases hds : d.suit = top.suit
          · -- THE pull: assemble here, the pulled card forced to `top`
            have hpp := pullsOf_cons_self (c := d) (b := bs0) (t := rest)
            rw [hds] at hpp
            have hp0 : pullsOf rest top.suit = 0 := by omega
            have hr' : ∀ σ, raisesOf rest σ = 0 := fun σ => by
              have h0 := hq1 σ; rwa [raisesOf_cons_pull] at h0
            have hp2' : ∀ σ, σ ≠ top.suit → pullsOf rest σ = 0 := fun σ hσ => by
              have hdne : d.suit ≠ σ :=
                fun hcon => hσ ((hds.symm.trans hcon).symm)
              have h0 := hp2 σ hσ; rwa [pullsOf_cons_ne hdne] at h0
            have hallpulls : ∀ σ, pullsOf rest σ = 0 := fun σ => by
              by_cases hσ : σ = top.suit
              · subst hσ; exact hp0
              · exact hp2' σ hσ
            have hpost := quiet_flat hrest hr' hallpulls
            have hdtop := foundToTab_pops_currentTop hstep
            rw [hds] at hdtop
            have hdt : d = top :=
              Option.some.inj (hdtop.symm.trans htop)
            rw [hdt] at hstep
            exact ⟨u, s₁, bs0, FlatPath.refl u, hstep, hpost⟩
          · exfalso
            have hpp := pullsOf_cons_self (c := d) (b := bs0) (t := rest)
            have h0 := hp2 d.suit hds
            omega
      | tabToTab c b =>
          have htop' : s₁.foundTop top.suit = some top :=
            (flatStep_foundTop (FlatStep.cargo c b hstep hrev) top.suit).trans htop
          obtain ⟨u2, v2, bs2, pre, hf, post⟩ :=
            ih htop'
              (fun σ => by have h0 := hq1 σ; rwa [raisesOf_cons_tabToTab] at h0)
              (by have h0 := hp1; rwa [pullsOf_cons_tabToTab] at h0)
              (fun σ hσ => by
                have h0 := hp2 σ hσ; rwa [pullsOf_cons_tabToTab] at h0)
          exact ⟨u2, v2, bs2, FlatPath.cons (FlatStep.cargo c b hstep hrev) pre,
            hf, post⟩

/-- **THE FLAT RAISE FACTOR** — the reversed-bracket splitter.  After a
pull of `x` at `cur` (step `hstep0`, landing `rest₀`), a pull-free
witness journey whose ONLY raise is of suit `x.suit` (exactly one leg,
other suits at zero) factors as `flat · raise-of-x · flat`, the raised
card forced equal to `x` by the foundation-prefix discipline: both
found rows read the same `take` of `upCards` (WF descends through the
leg), and the pulled row was the snoc `[x]` — equal fronts cancel,
equal snocs agree. -/
theorem raise_factor {x : Card} {cur rest₀ : State} {bs0 : Base}
    (hstep0 : State.step cur (Move.foundToTab x bs0) = some rest₀)
    (hwfcur : cur.WF) :
    ∀ {play : List Move} {w : State},
    ShufflePlayW rest₀ play w →
    rest₀.found x.suit = chop (cur.found x.suit) →
    rest₀.WF →
    (∀ σ, pullsOf play σ = 0) →
    (raisesOf play x.suit = 1) →
    (∀ σ, σ ≠ x.suit → raisesOf play σ = 0) →
    ∃ (u v : State),
      FlatPath rest₀ u ∧
      State.step u (Move.tabToFound x) = some v ∧
      FlatPath v w := by
  have hgtop : cur.foundTop x.suit = some x := foundToTab_pops_currentTop hstep0
  have hsnocL : cur.found x.suit = chop (cur.found x.suit) ++ [x] :=
    lastOf_chop hgtop
  clear hstep0
  intro play w h
  induction h with
  | nil u =>
      intro _ _ _ hr1 _
      exfalso
      have h0 : raisesOf ([] : List Move) x.suit = 0 := rfl
      omega
  | @cons u m s₁ rest w' hrev hstep hrest ih =>
      intro hfnd hwf hp1 hr1 hr2
      cases m with
      | draw =>
          have hfnd' : s₁.found x.suit = chop (cur.found x.suit) :=
            (flatStep_found (FlatStep.draw hstep hrev) x.suit).trans hfnd
          obtain ⟨u2, v2, pre, hf, post⟩ :=
            ih hfnd'
              (step_wf hwf hstep)
              (fun σ => by have h0 := hp1 σ; rwa [pullsOf_cons_draw] at h0)
              (by have h0 := hr1; rwa [raisesOf_cons_draw] at h0)
              (fun σ hσ => by
                have h0 := hr2 σ hσ; rwa [raisesOf_cons_draw] at h0)
          exact ⟨u2, v2, FlatPath.cons (FlatStep.draw hstep hrev) pre, hf, post⟩
      | wasteToFound c => exact absurd hrev (journey_never_wasteToFound hstep)
      | wasteToTab c b => exact absurd hrev (journey_never_wasteToTab hstep)
      | foundToTab c b =>
          exfalso
          have h0 := hp1 c.suit
          rw [pullsOf_cons_self] at h0
          omega
      | tabToFound c =>
          -- THE raise: suit first, then the same-card cancel, then the
          -- quiet tail as the closing flat block
          by_cases hcs : c.suit = x.suit
          · have hrestx : raisesOf rest x.suit = 0 := by
              have h0 := raisesOf_cons_raise (c := c) (t := rest) (σ := x.suit)
              rw [ite_eq_left hcs] at h0
              omega
            have hr' : ∀ σ, raisesOf rest σ = 0 := fun σ => by
              by_cases hσ : σ = x.suit
              · subst hσ; exact hrestx
              · have hcne : c.suit ≠ σ :=
                  fun hcon => hσ (hcs.symm.trans hcon).symm
                have h0 := hr2 σ hσ
                rwa [raisesOf_cons_ne hcne] at h0
            have hallpulls : ∀ σ, pullsOf rest σ = 0 := fun σ => by
              have h0 := hp1 σ; rwa [pullsOf_cons_raise] at h0
            have hpost := quiet_flat hrest hr' hallpulls
            -- the same-card cancellation: the raised row at the landing
            -- reads the same `take` of `upCards` that the pulled card's
            -- pre-row read (both WFs, equal lengths), and that pre-row
            -- was the snoc `chop L ++ [x]` — equal fronts cancel, so the
            -- appended cards agree: `c = x`
            have hwfs₁ : s₁.WF := step_wf hwf hstep
            obtain ⟨hselfc, -⟩ := tabToFound_found_pair hstep
            rw [hcs] at hselfc
            -- hselfc : s₁.found x.suit = u.found x.suit ++ [c]
            have hs1row : s₁.found x.suit = chop (cur.found x.suit) ++ [c] := by
              rw [hselfc, hfnd]
            have hA : (s₁.found x.suit).length = (u.found x.suit).length + 1 := by
              rw [hselfc, List.length_append]
              have h1 : ([c] : List Card).length = 1 := rfl
              omega
            have huflen : (u.found x.suit).length =
                (chop (cur.found x.suit)).length :=
              congrArg (List.length) hfnd
            have hC : (cur.found x.suit).length =
                (chop (cur.found x.suit)).length + 1 := by
              have hl := congrArg (List.length) hsnocL
              rw [List.length_append] at hl
              have h1 : ([x] : List Card).length = 1 := rfl
              omega
            have hrungs : rungAt s₁ x.suit = rungAt cur x.suit := by
              show (s₁.found x.suit).length = (cur.found x.suit).length
              omega
            have hsame : s₁.found x.suit = cur.found x.suit := by
              rw [rung_found_prefix s₁ hwfs₁ x.suit,
                rung_found_prefix cur hwfcur x.suit, hrungs]
            have hcx : c = x :=
              snoc_cancel
                (hs1row.symm.trans (hsame.trans hsnocL))
            rw [hcx] at hstep
            exact ⟨u, s₁, FlatPath.refl u, hstep, hpost⟩
          · exfalso
            have h0 := hr2 c.suit hcs
            have h1 := raisesOf_cons_self (c := c) (t := rest)
            omega
      | tabToTab c b =>
          have hfnd' : s₁.found x.suit = chop (cur.found x.suit) :=
            (flatStep_found (FlatStep.cargo c b hstep hrev) x.suit).trans hfnd
          obtain ⟨u2, v2, pre, hf, post⟩ :=
            ih hfnd'
              (step_wf hwf hstep)
              (fun σ => by have h0 := hp1 σ; rwa [pullsOf_cons_tabToTab] at h0)
              (by have h0 := hr1; rwa [raisesOf_cons_tabToTab] at h0)
              (fun σ hσ => by
                have h0 := hr2 σ hσ; rwa [raisesOf_cons_tabToTab] at h0)
          exact ⟨u2, v2, FlatPath.cons (FlatStep.cargo c b hstep hrev) pre,
            hf, post⟩

/-! ## §4. The bracket letters and the closure -/

/-- **THE BRACKET** — THE TASK'S LETTER, verbatim: raise `c`, then a
cargo interior (slides only), then pull `c` back down — the
conjugate-shaped round trip. -/
def BracketW (st w : State) (c : Card) : Prop :=
  ∃ s₁ s₂ bs,
    State.step st (Move.tabToFound c) = some s₁ ∧
    CargoPath s₁ s₂ ∧
    State.step s₂ (Move.foundToTab c bs) = some w

/-- **THE JOURNEY-GRADE BRACKET** — the honest interior letter: a
FLAT block (reversible slides and draw loops).  A reversible draw
genuinely rides lawful witness journeys (the draw cycle loops back),
so the interior of a bracket read off a witness journey is a
`FlatPath`, not a bare `CargoPath`; under a draw-free journey every
block degenerates to pure cargo (the `FlatStep.cargo` kind census)
and this letter reads exactly as `BracketW`. -/
def BracketWF (st w : State) (c : Card) : Prop :=
  ∃ s₁ s₂ bs,
    State.step st (Move.tabToFound c) = some s₁ ∧
    FlatPath s₁ s₂ ∧
    State.step s₂ (Move.foundToTab c bs) = some w

/-- **THE REVERSED BRACKET** — pull `x` down, a flat interior, then
raise the SAME card back up: the excursion of a founded card that
circulates through the tableau and returns to its slot.  The
prefix discipline (`rung_found_prefix`) forces the same-card cycle
— `raise_factor` proves it at the one-bracket grade. -/
def BracketRW (st w : State) (x : Card) : Prop :=
  ∃ s₁ s₂ bs,
    State.step st (Move.foundToTab x bs) = some s₁ ∧
    FlatPath s₁ s₂ ∧
    State.step s₂ (Move.tabToFound x) = some w

/-- **THE BRACKET CLOSURE** — zero or more segments, each a cargo
block (the task's `CargoPath` letter), a flat phase-block (slides
plus draw loops — the honest journey-grade generalization), a
bracket (the task's letter `BracketW`), a journey-grade bracket
(`BracketWF`), or a reversed bracket (`BracketRW`), ending at the
base.  Sequencing is tail-consed; nesting rides the recursion
through each bracket letter's interior. -/
inductive BracketClosure : State → State → Prop
  | base (st : State) : BracketClosure st st
  | cargo {st w' w : State} (h : CargoPath st w')
      (t : BracketClosure w' w) : BracketClosure st w
  | phase {st w' w : State} (h : FlatPath st w')
      (t : BracketClosure w' w) : BracketClosure st w
  | bracket {st w' w : State} (c : Card) (h : BracketW st w' c)
      (t : BracketClosure w' w) : BracketClosure st w
  | bracketFlat {st w' w : State} (c : Card) (h : BracketWF st w' c)
      (t : BracketClosure w' w) : BracketClosure st w
  | bracketRev {st w' w : State} (x : Card) (h : BracketRW st w' x)
      (t : BracketClosure w' w) : BracketClosure st w

/-- The pure-cargo bracket rides the closure at both grades (the
cargo interior is a flat interior). -/
theorem BracketW_cargo_to_closure {st w' w : State} {c : Card}
    (h : BracketW st w' c) (t : BracketClosure w' w) :
    BracketClosure st w :=
  BracketClosure.bracket c h t

/-- Every cargo block is a flat block. -/
theorem flatPath_of_cargoPath {st w : State} (h : CargoPath st w) :
    FlatPath st w := by
  induction h with
  | refl u => exact FlatPath.refl u
  | @cons u z u2 hs hkind _t ih =>
      obtain ⟨c, b, hstep, hrev, rfl⟩ := hkind
      exact FlatPath.cons (FlatStep.cargo c b hstep hrev) ih

/-- The task's cargo letter spans the closure directly. -/
theorem bracketClosure_of_cargoPath {st w' w : State}
    (h : CargoPath st w') (t : BracketClosure w' w) : BracketClosure st w :=
  BracketClosure.phase (flatPath_of_cargoPath h) t

/-- Every flat span is a closure (the phase letter walks the legs). -/
theorem bracketClosure_of_flatPath {st w : State} (h : FlatPath st w) :
    BracketClosure st w := by
  induction h with
  | refl u => exact BracketClosure.base u
  | @cons u z u2 hs _t ih =>
      exact BracketClosure.phase (FlatPath.cons hs (FlatPath.refl z)) ih

/-! ## §5. THE ONE-BRACKET DECOMPOSITION -/

/-- **THE ONE-BRACKET DECOMPOSITION** — the assembly's proved frontier:
an equal-tuple witness journey with at most ONE raise leg factors
exactly as the bracket grammar promises:

* all flat (`raiseTotal = 0`), or
* `[flat][raise c][flat][pull c][flat]` — the pulled card is forced to
  be the raised card (between the two only flats run, so the suit's
  top is unchanged and the LIFO guard names it), or
* `[flat][pull x][flat][raise x][flat]` — the raised card is forced to
  be the pulled card (the raise lands the row the pull chopped, whose
  `take` is pinned by WF descent; the appended card was `x` itself).
-/
theorem witness_one_bracket {st : State} : ∀ {play : List Move} {w : State},
    ShufflePlayW st play w →
    st.WF →
    (∀ σ, rungAt st σ = rungAt w σ) →
    raiseTotal play ≤ 1 →
    FlatPath st w ∨
    (∃ (c : Card) (bs : Base) (s₀ s₁ z₁ w₁ : State),
       FlatPath st s₀ ∧
       State.step s₀ (Move.tabToFound c) = some s₁ ∧
       FlatPath s₁ z₁ ∧
       State.step z₁ (Move.foundToTab c bs) = some w₁ ∧
       FlatPath w₁ w) ∨
    (∃ (x : Card) (bs : Base) (s₀ s₁ z₁ w₁ : State),
       FlatPath st s₀ ∧
       State.step s₀ (Move.foundToTab x bs) = some s₁ ∧
       FlatPath s₁ z₁ ∧
       State.step z₁ (Move.tabToFound x) = some w₁ ∧
       FlatPath w₁ w) := by
  intro play w h
  induction h with
  | nil u =>
      intro _ _ _
      exact Or.inl (FlatPath.refl u)
  | @cons u m s₁ rest w' hrev hstep hrest ih =>
      intro hwf htup hrt
      cases m with
      | draw =>
          rcases ih (step_wf hwf hstep)
            (fun σ => (ledger_draw hstep σ).trans (htup σ)) hrt with
            hflat | ⟨c, bs, s₀, _, z₁, w₁, pre, hraise, mid, hpull, post⟩ |
            ⟨x, bs, s₀, _, z₁, w₁, pre, hpull0, mid, hraise0, post⟩
          · exact Or.inl (FlatPath.cons (FlatStep.draw hstep hrev) hflat)
          · exact Or.inr (Or.inl
              ⟨c, bs, s₀, _, z₁, w₁,
                FlatPath.cons (FlatStep.draw hstep hrev) pre,
                hraise, mid, hpull, post⟩)
          · exact Or.inr (Or.inr
              ⟨x, bs, s₀, _, z₁, w₁,
                FlatPath.cons (FlatStep.draw hstep hrev) pre,
                hpull0, mid, hraise0, post⟩)
      | wasteToFound c => exact absurd hrev (journey_never_wasteToFound hstep)
      | wasteToTab c b => exact absurd hrev (journey_never_wasteToTab hstep)
      | tabToTab c b =>
          rcases ih (step_wf hwf hstep)
            (fun σ => (ledger_tabToTab hstep σ).trans (htup σ)) hrt with
            hflat | ⟨c2, bs, s₀, _, z₁, w₁, pre, hraise, mid, hpull, post⟩ |
            ⟨x, bs, s₀, _, z₁, w₁, pre, hpull0, mid, hraise0, post⟩
          · exact Or.inl (FlatPath.cons (FlatStep.cargo c b hstep hrev) hflat)
          · exact Or.inr (Or.inl
              ⟨c2, bs, s₀, _, z₁, w₁,
                FlatPath.cons (FlatStep.cargo c b hstep hrev) pre,
                hraise, mid, hpull, post⟩)
          · exact Or.inr (Or.inr
              ⟨x, bs, s₀, _, z₁, w₁,
                FlatPath.cons (FlatStep.cargo c b hstep hrev) pre,
                hpull0, mid, hraise0, post⟩)
      | tabToFound c =>
          -- THE FORWARD BRACKET: the raise fires here; the unique
          -- same-suit pull (the census) closes it, the LIFO guard
          -- forces the same card
          have hrt0 : raiseTotal rest = 0 := by
            have h0 := raiseTotal_cons_raise (c := c) (t := rest)
            omega
          have hqr : ∀ σ, raisesOf rest σ = 0 := fun σ => by
            have h0 := raisesOf_le_raiseTotal rest σ
            omega
          have htop : s₁.foundTop c.suit = some c :=
            tabToFound_tops_currentSuit hstep
          have hcl := witness_rung_census hrest
          obtain ⟨hup, hothers⟩ := ledger_tabToFound hstep
          have hpT : pullsOf rest c.suit = 1 := by
            have hc0 := hcl c.suit
            have hu := hup
            have ht := htup c.suit
            have hq := hqr c.suit
            omega
          have hpO : ∀ σ, σ ≠ c.suit → pullsOf rest σ = 0 := fun σ hσ => by
            have hc0 := hcl σ
            have ho := hothers σ hσ
            have ht := htup σ
            have hq := hqr σ
            omega
          obtain ⟨z₁, w₁, bs2, pre, hpull, post⟩ :=
            pull_factor (top := c) hrest htop hqr hpT hpO
          exact Or.inr (Or.inl
            ⟨c, bs2, u, _, z₁, w₁, FlatPath.refl u, hstep, pre, hpull, post⟩)
      | foundToTab x bs =>
          -- THE REVERSED BRACKET: a pull fires first; the census forces
          -- exactly one raise later — and the prefix discipline forces
          -- the raised card to be this pulled card
          obtain ⟨hdown, hothers⟩ := ledger_foundToTab hstep
          have hcl := witness_rung_census hrest
          have hrX : raisesOf rest x.suit = 1 := by
            have hc0 := hcl x.suit
            have hd := hdown
            have ht := htup x.suit
            have h1 := raisesOf_le_raiseTotal rest x.suit
            have h0 := raiseTotal_cons_pull (c := x) (b := bs) (t := rest)
            omega
          have hzero : ∀ σ, σ ≠ x.suit → raisesOf rest σ = 0 := fun σ hσ => by
            have hc0 := hcl σ
            have ho := hothers σ hσ
            have ht := htup σ
            have h0 := raiseTotal_cons_pull (c := x) (b := bs) (t := rest)
            have hpair := raisesOf_pair_le_raiseTotal (σ := x.suit) (σ' := σ)
              (fun hcon => hσ hcon.symm) rest
            omega
          have hpX : pullsOf rest x.suit = 0 := by
            have hc0 := hcl x.suit
            have hd := hdown
            have ht := htup x.suit
            omega
          have hpO : ∀ σ, σ ≠ x.suit → pullsOf rest σ = 0 := fun σ hσ => by
            have hc0 := hcl σ
            have ho := hothers σ hσ
            have ht := htup σ
            have hz := hzero σ hσ
            omega
          have hallpulls : ∀ σ, pullsOf rest σ = 0 := fun σ => by
            by_cases hσ : σ = x.suit
            · subst hσ; exact hpX
            · exact hpO σ hσ
          have hfnd0 : s₁.found x.suit = chop (u.found x.suit) :=
            (foundToTab_found_self hstep).1
          have hwfs₁ : s₁.WF := step_wf hwf hstep
          obtain ⟨z₁, w₁, pre, hraise, post⟩ :=
            raise_factor (x := x) (cur := u) (rest₀ := s₁) (bs0 := bs)
              hstep hwf hrest hfnd0 hwfs₁ hallpulls hrX hzero
          exact Or.inr (Or.inr
            ⟨x, bs, u, s₁, z₁, w₁, FlatPath.refl u, hstep, pre, hraise, post⟩)

/-- **THE ONE-BRACKET CLOSURE MEMBERSHIP** — the proved frontier, read
in the closure's own letters: an equal-tuple witness journey with at
most one raise (and `WF` start) spans the bracket closure. -/
theorem one_bracket_closure {st : State} {play : List Move} {w : State}
    (h : ShufflePlayW st play w)
    (hwf : st.WF)
    (htup : ∀ σ, rungAt st σ = rungAt w σ)
    (hrt : raiseTotal play ≤ 1) :
    BracketClosure st w := by
  rcases witness_one_bracket h hwf htup hrt with
    hflat | ⟨c, bs, s₀, s₁, z₁, w₁, pre, hup, mid, hdown, post⟩ |
    ⟨x, bs, s₀, s₁, z₁, w₁, pre, hdown, mid, hup, post⟩
  · exact bracketClosure_of_flatPath hflat
  · exact BracketClosure.phase pre
      (BracketClosure.bracketFlat c ⟨s₁, z₁, bs, hup, mid, hdown⟩
        (bracketClosure_of_flatPath post))
  · exact BracketClosure.phase pre
      (BracketClosure.bracketRev x ⟨s₁, z₁, bs, hdown, mid, hup⟩
        (bracketClosure_of_flatPath post))

/-- **THE ZERO-RAISE CASE, standalone** — an equal-tuple witness journey
with NO raise leg is pure flat cargo+phase: the census bars the
raises (hypothesis), the pulls follow by the tuple census (every
suit's pull count equals its zero raise count), the waste letters
never ride, and `quiet_flat` Spans the `FlatPath`. -/
theorem raise_free_closure {st : State} {play : List Move} {w : State}
    (h : ShufflePlayW st play w)
    (htup : ∀ σ, rungAt st σ = rungAt w σ)
    (hquiet : raiseTotal play = 0) :
    BracketClosure st w := by
  have hqr : ∀ σ, raisesOf play σ = 0 := fun σ => by
    have h0 := raisesOf_le_raiseTotal play σ
    omega
  have hpl : ∀ σ, pullsOf play σ = 0 := fun σ => by
    have hc := witness_tuple_census h htup σ
    exact hc.symm.trans (hqr σ)
  exact bracketClosure_of_flatPath (quiet_flat h hqr hpl)

/-! ## §6. THE MAIN DECOMPOSITION -/

/-- The setoid unpack: every class carries a FORWARD witness play
(`st → w`), read straight off the rev-closure's reversed-argument
orientation (`Orig/Combine.lean:158`) — the extraction the residue's
route (and any downstream G-row casing on the class's play) begins
with. -/
theorem sameOrbit_forward {st w : State} (h : sameOrbitSetoid.r st w) :
    ∃ play, ShufflePlayW st play w := by
  obtain ⟨-, -, τ, hτ⟩ : RevEqW w st := h
  exact ⟨τ, hτ⟩

/-- The QUIET-CLASS GRADED MAIN — the proved frontier, setoid-grade:
an equal-tuple class whose forward witness play carries at most one
raise spans the bracket closure.  (The fully-ungraded main below is
the residue; this head is what a downstream row whose witness play is
observed quiet consumes directly.) -/
theorem reversible_equaltuple_decompose_one_raise {st w : State}
    (_h : sameOrbitSetoid.r st w)
    (hwf : st.WF)
    (htup : ∀ σ, rungAt st σ = rungAt w σ)
    (hsome : ∃ play, ShufflePlayW st play w ∧ raiseTotal play ≤ 1) :
    BracketClosure st w := by
  obtain ⟨play, hplay, hrt⟩ := hsome
  exact one_bracket_closure hplay hwf htup hrt

/-- **THE N-NESTING RESIDUE** — the main head's one open leaf, NAMED.
The route (each step priced by this card's proved rows):

1. **Extract the forward play**: `sameOrbitSetoid.r st w` is
   `RevEqW w st` (`Orig/Combine.lean:158`), so it unpacks to a FORWARD
   witness play `τ` (`ShufflePlayW st τ w`) — the pairing that rides
   every row below.  The census closes per suit along τ:
   `witness_tuple_census`.
2. **The per-suit Dyck serialization, by strong induction on the
   play length.** The heads run exactly as in
   `witness_one_bracket`: flats phase-prepend; at a raise-head of
   card `c`, the matching pull is the FIRST same-suit pull after it
   that pops `c` — the per-suit stack discipline
   (`foundToTab_pops_currentTop` + the flat found-rows) forces the
   same-suit legs between to NEST above `c`'s slot; the interior
   between them is a shorter equal-tuple witness subjourney (recurse
   into it — the closure's bracket letters with nested interiors), as
   is the tail after the matched pull.  The pull-first pattern
   recurses through the reversed letter the same way, seeded by
   `raise_factor`'s same-card row.  WF DESCENDS through every leg
   (`step_wf`), so the same-card claims hold at every interior state.
   THE STEP THIS CARD DOES NOT PRICE: pairs from DIFFERENT suits may
   CROSS (the task's own warning — four independent stacks), and the
   closure grammar expresses a crossing pair only by re-deroute —
   commuting a bracket's closing pull past another bracket's opening
   raise — which needs the bracket-edge commutation lemmas (phase
   legs write no foundation and touch piles disjoint from the found
   writers; pull landing bases are equivariant under leading
   slides — the TwinExchange-era relocation facts).  Until those
   land, the residue is honestly open.
3. **The premise grade**: the residue as stated (bare) needs
   `st.WF` added — or derived — for the same-card serialization (the
   fiber/fork consumers premised on this card all carry `WF`
   already); the route above is written at the WF grade to stay
   constructible. -/
private theorem decompose_residue_nesting {st w : State}
    (h : sameOrbitSetoid.r st w)
    (htup : ∀ σ, rungAt st σ = rungAt w σ) : BracketClosure st w := by
  sorry

/-- **THE MAIN DECOMPOSITION** (the unedited ambition, graded
honestly): a reversible equal-tuple pair spans the bracket closure —
every raise is matched by a same-card pull (LIFO, per suit), every
pull-first excursion is a same-card re-raise, and the intervening
legs are flat cargo/phase blocks.  The N-nesting wiring lives in the
named residue `decompose_residue_nesting` above with its route; the
proved frontier at theorem grade is `raise_free_closure` (zero
raises) and `one_bracket_closure` (at most one raise). -/
theorem reversible_equaltuple_decompose {st w : State}
    (h : sameOrbitSetoid.r st w)
    (htup : ∀ σ, rungAt st σ = rungAt w σ) :
    BracketClosure st w :=
  decompose_residue_nesting h htup

/-! ## The audit battery

Expected: `[propext]` or `[propext, Quot.sound]` for every proved
row; the main head carries `sorryAx` through exactly its named
residue (`decompose_residue_nesting` above, with its route). -/

#print axioms foundToTab_pops_currentTop
#print axioms tabToFound_tops_currentSuit
#print axioms foundToTab_keepsOtherTops
#print axioms tabToFound_keepsOtherTops
#print axioms witness_rung_census
#print axioms witness_tuple_census
#print axioms quiet_flat
#print axioms pull_factor
#print axioms raise_factor
#print axioms BracketW_cargo_to_closure
#print axioms flatPath_of_cargoPath
#print axioms bracketClosure_of_cargoPath
#print axioms bracketClosure_of_flatPath
#print axioms witness_one_bracket
#print axioms one_bracket_closure
#print axioms raise_free_closure
#print axioms sameOrbit_forward
#print axioms reversible_equaltuple_decompose_one_raise
#print axioms reversible_equaltuple_decompose
