import Orig.LowSlab

/-!
# Orig.ForkDescent — THE MAXIMAL UNSTACKING (the descent script)

The owner's UNSTACKING program, the pull-down sibling of
`Orig/ForkAscent.lean`'s stacking script: from any state, the descent
POPS FOUNDATION TOPS back to the tableau by the licensed
`foundToTab` — to the fitting top one-up opposite-family base, or
to the king-anchor's empty seat — until NO pull is licensed; the end
states are the MAXIMALLY-UNSTACKED `W`, the program's rung-floor
witnesses.  The composite (Unstack-then-Ascent, §4's route note):
descent first lays the whole liftable foundation inventory down at
the class's minimal rungs, then the ascent sibling's stacking script
climbs from there; the two scripts together walk the program's macro
classes from floor to fork.

* **§0 THE SCRIPT** [E] — the step relation `DescentMove` (a
  licensed pull: `m = foundToTab c b` with the foundation-top and
  placement guards — the two `canPlace` branches ARE the license:
  the fitting top one-up opposite-family host, or the king-anchor's
  empty seat), the stuck read `DescentStuck` (the maximally-unstacked
  end states), the pull-play read `PullPlay`, and THE CANONICAL
  ORDER: the round-robin-by-rank schedule `descentSchedule` (the
  rank ladder `descentRankLadder` king-first, the two-family
  alternating suit cycle `descentSuitOrder` within each rank), the
  base schedule `descentBases` (fitting tops in anchor order, then
  the king-anchor seats), and the deterministic pick `descentPick`.
  The canonical order is not decoration — it buys the maximal run's
  CONSTRUCTIVITY: a `firstWhere` search over a fixed total schedule
  fires exactly when any pull is licensed, so the maximal runs of §1
  are built with ZERO `Classical.choice` (`descent_pick_pulls`,
  `descent_pick_fires`, `descent_pick_none_stuck`; the kit row
  `fd_firstWhere_hits`).
* **§1 TERMINATION** [E–M] — every pull strictly decreases the
  found-census (`descent_pull_drops`, over the banked
  `foundTotal_step_foundToTab`, `Orig/Irreversible.lean`); the
  Σ-rung face of the same measure (`rungSum_eq_foundTotal`; the
  per-suit rung deltas `fd_rung_delta`, the per-file copy of
  LowSlab's private rung arithmetic); the LENGTH LEDGER
  `descent_run_foundTotal_bound` (a pull play of length n costs n
  rungs — every maximal run is finite in the strongest packaged
  sense: its length is bounded by the start's census); and the
  canonical maximal run's EXISTENCE `descent_reaches_floor` — every
  state descends to a maximally-unstacked `W` in at most
  `foundTotal st` pulls (the fuel induction `fd_descent_fuel`), with
  the empty-foundation degenerate floor banked separately
  (`descent_floor_zero_stuck`).  No WF premise anywhere in §1: WF
  enters at §2, where the class lives.
* **§2 CLASS-PRESERVATION** [M] — **THE LOAD-BEARING ROW**
  `descent_stays_class`: a pull play from a WF start never leaves
  the start's macro class (`sameOrbitSetoid.r st w`).  Proof shape
  exactly as the banked mirror dictates: per-leg witnesses via
  `lowslab_pull_wf_undo` (`Orig/LowSlab.lean` — every `foundToTab`
  at a WF member carries a one-move `tabToFound` mirror, so every
  descent leg is `reversibleAtW`), assembled by
  `descent_pull_shuffleW` (a pull play at WF IS a witness shuffle
  `ShufflePlayW` — per-leg mirror, then induct), and the chain by
  the class-weld kit (the per-file copies `fd_shuffleW_of_round` /
  `fd_class_leg` / `fd_journey_class`, dedup-cited against
  `Orig/LowSlab.lean`'s private originals).  MIND THE CLASS WELD:
  `sameOrbitSetoid` is the rev-closure (`r st w` is `RevEqW w st`),
  so the setoid's own symmetry/transitivity welds the links, and
  `sameOrbit_forward` is the forward-unpack the §3 route rides.
* **§3 THE FLOOR CLAIM** [H — THE NAMED RESIDUE, REFUTED AT THE
  FROZEN STATEMENT] `descent_stall_certifies_floor`: if a maximal
  descent stalls with a suit at rung `h`, NO class member has that
  suit below `h` — the stall itself CERTIFIES the class's rung
  floor.  The route (priced in the row's docstring, anchored EXACTLY
  at the census's `excursion_issues_noNewSeat`): §2's chain welds
  the member journeys; `descent_lower_member_crosses_pull` (proved
  here) forces every witnessing journey `W ⇝ u` with a lower σ-rung
  to carry a σ-pull leg; the census prices WHICH hosts the
  arrangement can still issue, and the stalled state's own
  exhaustion (`descent_stuck_seatExhausted`, proved here: at `W` NO
  host top fits any current foundation top) is the seat-exhaustion
  contrapositive the journey's pulls have to defeat.  Support rows
  landed alongside: `descent_class_wf` (the class of a WF start is
  WF — the member-grade premise the census rows demand).
  SESSION-4 FATE (2026-10-13, the fourth succession): the row is
  REFUTED — the counterexample family (the buried-host
  expose-raise) is certified decide-grade in-file at §3R
  (`descent_stall_refuted`, zero-sorry); the residue keeps its
  sorry and its [H] grade with the refutation on record.
* **§4 THE COMPOSITE** (route note only) — `s` reachable ⇒ descent
  reaches the class-minimal rung-floor componentwise, therefore ≤
  every member; the Unstack-then-Ascent composition hands off to
  `Orig/ForkAscent.lean`'s rows — cited in PROSE ONLY (that leaf is
  under active repair; this file takes NO import of it).

House compliance: additive leaf (`import Orig.LowSlab` — brings the
WF pull-mirror `lowslab_pull_wf_undo`, `familyBelowFrontier`, the
witness vocabulary; everything else consumed is transitive: the
splice/inv rows and `State.run`/`run_one`/`run_split` via
`Orig/Play.lean` and `Orig/Macro.lean`, the measure tables and step
inverses via `Orig/Irreversible.lean`, `step_wf` via
`Orig/Reach.lean`, the rung ledger `witness_rung_census` via
`Orig/BracketDecomp.lean`, the census `excursion_issues_noNewSeat`
and `witness_leg_mint_confined` via `Orig/HostCensus.lean`); every
private kit row a dedup-cited per-file copy; BOLD names with
grades; `#print axioms` battery for every fresh head; zero
`Classical.choice` (all splits on `Bool` / `Option` / decidable
`by_cases` reads and constructor mismatches; `exfalso`/`absurd`
before `omega` at non-arithmetic goals); the single `sorry` is §3's
named residue with its complete route — NEVER-force, no premise
smuggled to save it. -/

/-! ## §0. The script — the step relation and the pick engine -/

/-- **THE UNSTACKING STEP RELATION** `DescentMove` — a licensed pull:
`m` is the giveback `foundToTab c b`, the target suit's foundation
really tops at `c` (the step's own `foundTop` guard), and the
placement `canPlace c b` holds — `canPlace`'s two branches ARE the
license named in the program: the fitting top one-up opposite-family
host (`.inr z` with `canSitOn`), or the king-anchor's empty seat
(`.inl a`).  `DescentMove_fires_iff` reads the relation back at the
step: guards and firing say the same. -/
def DescentMove (st : State) (m : Move) : Prop :=
  ∃ (c : Card) (b : Base),
    m = Move.foundToTab c b ∧
      st.foundTop c.suit = some c ∧ st.canPlace c b = true

/-- **THE MAXIMALLY-UNSTACKED READ** `DescentStuck` — the script's
end states: NO licensed pull remains (the dual of `DescentMove`,
read over the whole move type). -/
def DescentStuck (st : State) : Prop :=
  ∀ (m : Move), DescentMove st m → False

/-- **THE PULL-PLAY READ** `PullPlay` — every letter of a play is a
pull letter (the letter predicate §1's ledger and §2's mirror
descend along). -/
def PullPlay (play : List Move) : Prop :=
  ∀ (m : Move), m ∈ play → ∃ (c : Card) (b : Base), m = Move.foundToTab c b

/-- **THE FIRED-FORM EQUIVALENCE** [E] — the guard relation and the
step's own firing coincide at a giveback letter: forward by the
splice row (`step_foundToTab_splice`), backward by the step's own
inversion (`step_foundToTab_inv`). -/
theorem DescentMove_fires_iff {st : State} {c : Card} {b : Base} :
    DescentMove st (Move.foundToTab c b) ↔
      ∃ (s₁ : State), State.step st (Move.foundToTab c b) = some s₁ := by
  constructor
  · rintro ⟨c', b', heq, htop, hcp⟩
    injection heq with hc hb
    subst hc
    subst hb
    exact ⟨(st.setFound c.suit (chop (st.found c.suit))).putCard c b,
      step_foundToTab_splice htop hcp⟩
  · rintro ⟨s₁, hstep⟩
    obtain ⟨c', htop, hc'c, hcp, -⟩ := step_foundToTab_inv hstep
    exact ⟨c, b, rfl, by rw [htop, hc'c], hcp⟩

/-- **THE TWO-FAMILY SUIT CYCLE** — within one rank the candidates
cycle suits in the family-alternating order (black, red, black,
red): adjacent faces of the round-robin are opposite-family, the
ladder's own alternation. -/
def descentSuitOrder : List Suit :=
  [Suit.spade, Suit.heart, Suit.club, Suit.diamond]

/-- **THE RANK LADDER** — king first, ace last: the descent pops the
top of the ladder first, because the high rungs' own hosts are
themselves foundation tops wanting pulled — to lower σ you need the
opposite family's hosts exposed, which are themselves foundation
cards wanting pulled: the two-family ladder, pulled rank-by-rank in
alternation, from the top down. -/
def descentRankLadder : List Rank :=
  [Rank.king, Rank.queen, Rank.jack, Rank.ten, Rank.nine, Rank.eight,
    Rank.seven, Rank.six, Rank.five, Rank.four, Rank.three, Rank.two,
    Rank.ace]

/-- **THE ROUND-ROBIN SCHEDULE** — the candidate cards in the
canonical order: rank ladder-down, suits cycled per rank. -/
def descentSchedule : List Card :=
  descentRankLadder.flatMap fun (r : Rank) =>
    descentSuitOrder.map fun (s : Suit) => Card.mk s r

/-- The ladder membership row of the schedule kit. [E] -/
private theorem fd_mem_ladder (r : Rank) : r ∈ descentRankLadder := by
  cases r <;> simp [descentRankLadder]

/-- The cycle membership row of the schedule kit: within a rank, all
four suits sit in the schedule under their own name. [E] -/
private theorem fd_mem_cycle (s : Suit) (r : Rank) :
    Card.mk s r ∈ descentSuitOrder.map fun (s' : Suit) => Card.mk s' r := by
  cases s <;> simp [descentSuitOrder]

/-- **THE SCHEDULE COVERS THE DECK** [E] — every card is a candidate
in the canonical order (the completeness half of the pick). -/
theorem mem_descentSchedule (c : Card) : c ∈ descentSchedule := by
  rcases c with ⟨s, r⟩
  exact List.mem_flatMap.2 ⟨r, fd_mem_ladder r, fd_mem_cycle s r⟩

/-- **THE BASE SCHEDULE** — the canonical base scan of a position:
the fitting pile-top hosts (anchor order), then the king-anchor
empty seats (anchor order).  `canPlace`'s own two branches decide
which segment can fire for the pulled card; the schedule only
orders them, so the scan itself is card-free; the pick's predicate
does the per-card filtering. -/
def descentBases (st : State) : List Base :=
  Anchor.all.flatMap (fun (a : Anchor) =>
      match st.topOf a with
      | some z => [Sum.inr z]
      | none => []) ++
  Anchor.all.map Sum.inl

/-- **THE BASE SCHEDULE COVERS THE LICENSE** [E] — every base the
placement guard would accept is IN the scan: an empty-seat king
anchor by the second segment; a fitting top host `z` because the
top search that licensed it answers some anchor whose pile really
tops at `z` (`firstWhere_sound`, a definitional read — no WF, no
Integrity grade). -/
theorem mem_descentBases {st : State} {c : Card} {b : Base}
    (h : st.canPlace c b = true) : b ∈ descentBases st := by
  cases b with
  | inl a =>
      show Sum.inl a ∈ Anchor.all.flatMap (fun (a : Anchor) =>
          match st.topOf a with
          | some z => [Sum.inr z]
          | none => []) ++ Anchor.all.map Sum.inl
      rw [List.mem_append]
      exact Or.inr (List.mem_map.2 ⟨a, a.mem_all, rfl⟩)
  | inr z =>
      obtain ⟨k, hpo, -⟩ := canPlace_inr h
      have htopk : st.topOf k = some z :=
        of_decide_eq_true (firstWhere_sound
          (fun (a : Anchor) => decide (st.topOf a = some z)) hpo)
      show Sum.inr z ∈ Anchor.all.flatMap (fun (a : Anchor) =>
          match st.topOf a with
          | some z' => [Sum.inr z']
          | none => []) ++ Anchor.all.map Sum.inl
      rw [List.mem_append, List.mem_flatMap]
      refine Or.inl ⟨k, k.mem_all, ?_⟩
      show Sum.inr z ∈ (match st.topOf k with
        | some z' => [Sum.inr z']
        | none => [])
      rw [htopk]
      exact List.mem_cons_self ..

/-- **THE FIRSTWHERE HIT KIT** (private per-file copy of the search
discipline's completeness half) — an item satisfying the predicate
guarantees the search answers SOMETHING: the scan is `isSome`
whenever a witness is in the list.  The proof is the plain
induction; the `(some _).isSome` readings close by `rfl`. -/
private theorem fd_firstWhere_hits {α : Type} (p : α → Bool) :
    ∀ (l : List α) (x : α), x ∈ l → p x = true →
      (firstWhere p l).isSome = true := by
  intro l
  induction l with
  | nil => intro x hx; exact absurd hx (by simp)
  | cons y t ih =>
      intro x hx hp
      rw [show firstWhere p (y :: t) =
        (match p y with
          | true => some y
          | false => firstWhere p t) from rfl]
      cases hpy : p y with
      | true => rfl
      | false =>
          have hxt : x ∈ t := by
            rcases List.mem_cons.1 hx with heq | hxt
            · exfalso
              rw [heq] at hp
              exact absurd hp (by rw [hpy]; simp)
            · exact hxt
          exact ih x hxt hp

/-- **THE PAIRED SCAN** — the round-robin flattened over the base
schedule: `(card, base)` pairs in the canonical order. -/
def descentPairs (st : State) : List (Card × Base) :=
  descentSchedule.flatMap fun (c : Card) =>
    (descentBases st).map fun (b : Base) => (c, b)

/-- **THE PAIRED SCAN COVERS THE LICENSE** [E] — every licensed
pull appears as a pair in the scan (the completeness composition of
the two schedule rows). -/
theorem mem_descentPairs {st : State} {c : Card} {b : Base}
    (hcp : st.canPlace c b = true) : (c, b) ∈ descentPairs st := by
  show (c, b) ∈ descentSchedule.flatMap fun (c : Card) =>
    (descentBases st).map fun (b : Base) => (c, b)
  rw [List.mem_flatMap]
  exact ⟨c, mem_descentSchedule c,
    List.mem_map.2 ⟨b, mem_descentBases hcp, rfl⟩⟩

/-- **THE CANONICAL PICK** — the first licensed pull in the canonical
order: the descent script's ONE step, deterministic and total (the
hit kit fires it whenever any pull is licensed).  This determinism
is the constructivity budget of §1: the maximal run is built from
the pick alone, no choice anywhere. -/
def descentPick (st : State) : Option (Card × Base) :=
  firstWhere
    (fun (cb : Card × Base) =>
      decide (st.foundTop cb.1.suit = some cb.1) && st.canPlace cb.1 cb.2)
    (descentPairs st)

/-- **THE PICK IS SOUND** [E] — the picked pair carries its own
guards: the suit's foundation tops at the named card and the
placement accepts — so `foundToTab` on the pair is a `DescentMove`
(by `DescentMove_fires_iff`, a fired one). -/
theorem descent_pick_pulls {st : State} {c : Card} {b : Base}
    (h : descentPick st = some (c, b)) :
    st.foundTop c.suit = some c ∧ st.canPlace c b = true := by
  have hguard := firstWhere_sound
    (fun (cb : Card × Base) =>
      decide (st.foundTop cb.1.suit = some cb.1) && st.canPlace cb.1 cb.2) h
  rw [Bool.and_eq_true] at hguard
  exact ⟨of_decide_eq_true hguard.1, hguard.2⟩

/-- **THE PICK IS COMPLETE** [E] — whenever ANY pull is licensed (the
foundation tops at `c` and the placement accepts `b`), the canonical
scan fires: the pair is in the paired scan (`mem_descentPairs`),
its guard reads true, and the hit kit answers. -/
theorem descent_pick_fires {st : State} {c : Card} {b : Base}
    (htop : st.foundTop c.suit = some c) (hcp : st.canPlace c b = true) :
    (descentPick st).isSome = true := by
  have hmem : (c, b) ∈ descentPairs st := mem_descentPairs hcp
  have hp : (fun (cb : Card × Base) =>
      decide (st.foundTop cb.1.suit = some cb.1) && st.canPlace cb.1 cb.2)
        (c, b) = true := by
    show (decide (st.foundTop c.suit = some c) && st.canPlace c b) = true
    rw [decide_eq_true htop, hcp]
    rfl
  exact fd_firstWhere_hits
    (fun (cb : Card × Base) =>
      decide (st.foundTop cb.1.suit = some cb.1) && st.canPlace cb.1 cb.2)
    (descentPairs st) (c, b) hmem hp

/-- **THE PICK'S NONE IS THE STALL** [E] — a silent pick means the
maximally-unstacked read: no licensed pull exists (the completeness
row read contrapositively — a licensed pull would have fired the
scan). -/
theorem descent_pick_none_stuck {st : State} (h : descentPick st = none) :
    DescentStuck st := by
  intro _ hmove
  obtain ⟨c, b, -, htop, hcp⟩ := hmove
  have hmem : (c, b) ∈ descentPairs st := mem_descentPairs hcp
  have hp : (fun (cb : Card × Base) =>
      decide (st.foundTop cb.1.suit = some cb.1) && st.canPlace cb.1 cb.2)
        (c, b) = true := by
    show (decide (st.foundTop c.suit = some c) && st.canPlace c b) = true
    rw [decide_eq_true htop, hcp]
    rfl
  have hits : (descentPick st).isSome = true :=
    fd_firstWhere_hits
      (fun (cb : Card × Base) =>
        decide (st.foundTop cb.1.suit = some cb.1) && st.canPlace cb.1 cb.2)
      (descentPairs st) (c, b) hmem hp
  rw [h] at hits
  exact absurd hits (by simp)

/-! ## §1. Termination — the census measure and the maximal run -/

/-- **THE EMPTY-FLOOR ROW** [E] — a state with an empty foundation
census is trivially maximally-unstacked: a pull needs a foundation
TOP, a top is a member, and the census counts members.  This is the
fuel induction's base case, banked on its own name. -/
theorem descent_floor_zero_stuck {st : State} (h : foundTotal st = 0) :
    DescentStuck st := by
  intro _ hmove
  obtain ⟨c, -, -, htop, -⟩ := hmove
  have hc : c ∈ st.found c.suit :=
    lastOf_mem (show lastOf (st.found c.suit) = some c from htop)
  have hin : c ∈ Suit.all.flatMap st.found :=
    List.mem_flatMap.2 ⟨c.suit, c.suit.mem_all, hc⟩
  have hlen : 0 < foundTotal st := List.length_pos_of_mem hin
  omega

/-- **THE DESCENT MEASURE** — the Σ-rung read over the suit cycle:
the multiset face of the found-census (the two faces are ONE
number, the row below). -/
def rungSum (st : State) : Nat :=
  Suit.all.foldr (fun (s : Suit) acc => rungAt st s + acc) 0

/-- The flatMap-length/foldr-sum bridge of the measure kit: length
counts the concatenation, the foldr sums the same rows. [E] -/
private theorem fd_flatMap_length (F : Suit → List Card) :
    ∀ (l : List Suit),
      (l.flatMap F).length =
        l.foldr (fun (s : Suit) acc => (F s).length + acc) 0 := by
  intro l
  induction l with
  | nil => rfl
  | cons x t ih =>
      have h1 : ((x :: t).flatMap F) = F x ++ t.flatMap F := rfl
      have h2 : ((x :: t).foldr (fun (s : Suit) acc => (F s).length + acc) 0)
          = (F x).length +
            t.foldr (fun (s : Suit) acc => (F s).length + acc) 0 := rfl
      rw [h1, List.length_append, h2, ih]

/-- **THE MEASURE'S TWO FACES** [E] — the Σ-rung read IS the
found-census: the descent's measure is one number whether read
per-suit (the rungs, the componentwise ledger of §3) or as the
total foundation load (the census of the banked drop row). -/
theorem rungSum_eq_foundTotal (st : State) : rungSum st = foundTotal st :=
  (fd_flatMap_length st.found Suit.all).symm

/-- **THE PER-LEG RUNG DELTAS** (private per-file copy, dedup-cited
against `Orig/LowSlab.lean`'s own private
`lowslab_rung_delta_foundToTab`) — a pull lowers exactly its own
suit's rung by one (the popped row's snoc shape) and leaves every
other suit alone.  The componentwise arithmetic §1's narrative and
§3's route read; the total face is the banked census drop. -/
private theorem fd_rung_delta {s s' : State} {c : Card} {b : Base}
    (hstep : State.step s (Move.foundToTab c b) = some s') :
    rungAt s' c.suit + 1 = rungAt s c.suit ∧
      ∀ (σ : Suit), σ ≠ c.suit → rungAt s' σ = rungAt s σ := by
  obtain ⟨c', htop, hc'c, -, hs⟩ := step_foundToTab_inv hstep
  rw [hc'c] at htop
  have hf : s'.found c.suit = chop (s.found c.suit) := by
    rw [hs, putCard_found, setFound_found_self]
  have hsnoc : s.found c.suit = chop (s.found c.suit) ++ [c] :=
    lastOf_chop htop
  have hlen : (s.found c.suit).length
      = (chop (s.found c.suit)).length + 1 := by
    have h := congrArg List.length hsnoc
    rw [List.length_append] at h
    have h1 : ([c] : List Card).length = 1 := rfl
    omega
  refine ⟨?_, ?_⟩
  · show (s'.found c.suit).length + 1 = (s.found c.suit).length
    rw [hf]
    omega
  · intro σ hσ
    show (s'.found σ).length = (s.found σ).length
    have h1 : s'.found σ
        = (s.setFound c.suit (chop (s.found c.suit))).found σ := by
      rw [hs, putCard_found]
    rw [h1]
    exact congrArg List.length (setFound_found_ne hσ)

/-- **THE PULL DROPS THE MEASURE** [E] — every licensed pull strictly
decreases the found-census (the banked `foundTotal_step_foundToTab`
at the pulled letter; the step is licensed, so the letter is a
giveback).  Via `rungSum_eq_foundTotal` the same drop is the
componentwise multiset decrease Σ-rung ↦ Σ-rung - 1 (the pulled
suit alone, by `fd_rung_delta`). -/
theorem descent_pull_drops {st s₁ : State} {m : Move}
    (hmove : DescentMove st m) (hstep : State.step st m = some s₁) :
    foundTotal s₁ + 1 ≤ foundTotal st := by
  obtain ⟨c, b, rfl, -, -⟩ := hmove
  exact foundTotal_step_foundToTab hstep

/-- **THE LENGTH LEDGER** [E] — a pull play of length n lands n
rungs below its start: the per-leg drops telescope.  Every maximal
run is therefore finite in the strongest packaged sense — its
length is bounded by the start's census (the infinite-chain
statement's count-form; this row is what §1's existence row
spends). -/
theorem descent_run_foundTotal_bound :
    ∀ (st : State) (play : List Move) (w : State),
      st.run play = some w → PullPlay play →
        foundTotal w + play.length ≤ foundTotal st := by
  intro st play
  induction play generalizing st with
  | nil =>
      intro w hrun _
      have hs : some st = some w := hrun
      injection hs with hw
      rw [← hw]
      have h0 : ([] : List Move).length = 0 := rfl
      omega
  | cons m rest ih =>
      intro w hrun hpulls
      obtain ⟨s₁, hstep, hrest⟩ := State.run_cons hrun
      obtain ⟨c, b, hm⟩ := hpulls m (List.mem_cons_self ..)
      rw [hm] at hstep
      have hdrop : foundTotal s₁ + 1 ≤ foundTotal st :=
        foundTotal_step_foundToTab hstep
      have hrec := ih s₁ w hrest
        (fun (m' : Move) hm' => hpulls m' (List.mem_cons_of_mem _ hm'))
      show foundTotal w + (m :: rest).length ≤ foundTotal st
      rw [List.length_cons]
      omega

/-- **THE FUEL INDUCTION** (private) — the canonical maximal run,
built by the pick: each firing pick is spliced (its guards name the
successor outright, `step_foundToTab_splice`), drops the census by
one (the banked table), and recurses inside the fuel; a silent
pick stalls by the dichotomy row; the zero floor stalls by its own
row.  Zero `Classical.choice`: the canon is the deterministic
schedule's. -/
private theorem fd_descent_fuel : ∀ (fuel : Nat) (st : State),
    foundTotal st ≤ fuel →
      ∃ (play : List Move) (W : State),
        st.run play = some W ∧ PullPlay play ∧ DescentStuck W := by
  intro fuel
  induction fuel with
  | zero =>
      intro st hle
      exact ⟨[], st, rfl, (fun _ hm => absurd hm (by simp)),
        descent_floor_zero_stuck (Nat.le_zero.mp hle)⟩
  | succ f ih =>
      intro st hle
      cases hpick : descentPick st with
      | none =>
          exact ⟨[], st, rfl, (fun _ hm => absurd hm (by simp)),
            descent_pick_none_stuck hpick⟩
      | some cb =>
          obtain ⟨c, b⟩ := cb
          have hg := descent_pick_pulls hpick
          have hstep : State.step st (Move.foundToTab c b) =
              some ((st.setFound c.suit (chop (st.found c.suit))).putCard c b) :=
            step_foundToTab_splice hg.1 hg.2
          have hdrop : foundTotal
              ((st.setFound c.suit (chop (st.found c.suit))).putCard c b) + 1
              ≤ foundTotal st := foundTotal_step_foundToTab hstep
          have hle₁ : foundTotal
              ((st.setFound c.suit (chop (st.found c.suit))).putCard c b) ≤ f :=
            by omega
          obtain ⟨play, W, hrun', hpulls', hstuck'⟩ := ih _ hle₁
          refine ⟨Move.foundToTab c b :: play, W, ?_, ?_, hstuck'⟩
          · show (match State.step st (Move.foundToTab c b) with
              | some s' => s'.run play
              | none => none) = some W
            rw [hstep]
            exact hrun'
          · intro m hm
            rcases List.mem_cons.1 hm with rfl | hm'
            · exact ⟨c, b, rfl⟩
            · exact hpulls' m hm'

/-- **THE MAXIMAL PULL EXISTS** [M] — from ANY state (no WF premise:
the script's license, measure and stall are arrangement-agnostic),
the canonical descent reaches a maximally-unstacked `W` in a
finite play of pull letters — and the length ledger prices the
finiteness outright: the play is at most `foundTotal st` legs
long.  Together with `DescentStuck` this is §1's end-state row:
the maximal run terminates, and its end states are exactly the
maximally-unstacked reads. -/
theorem descent_reaches_floor (st : State) :
    ∃ (play : List Move) (W : State),
      st.run play = some W ∧ PullPlay play ∧ DescentStuck W ∧
        play.length ≤ foundTotal st := by
  obtain ⟨play, W, hrun, hpulls, hstuck⟩ :=
    fd_descent_fuel (foundTotal st) st (Nat.le_refl _)
  have hbound := descent_run_foundTotal_bound st play W hrun hpulls
  exact ⟨play, W, hrun, hpulls, ⟨hstuck, by omega⟩⟩

/-! ## §2. Class-preservation — the load-bearing row -/

/-- **THE ROUND-TRIP ENGINE** (private per-file copy, dedup-cited
against `Orig/LowSlab.lean`'s `lowslab_shuffleW_of_round`, itself the
house pattern: a play from `x` landing at `w`, spliced with ANY play
back from `w` to `x`, is a witness shuffle `x ⇝ w` — for every
interior leg, the loop remainder is an explicit returning play, so
each leg carries its own `reversibleAtW`). -/
private theorem fd_shuffleW_of_round : ∀ (σ : List Move) (x w : State),
    x.run σ = some w → ∀ (ρ : List Move), w.run ρ = some x →
      ShufflePlayW x σ w := by
  intro σ
  induction σ with
  | nil =>
      intro x w hσ ρ hρ
      have hxw : some x = some w := hσ
      injection hxw with hx
      rw [hx]
      exact .nil w
  | cons p rest ih =>
      intro x w hσ ρ hρ
      obtain ⟨y, hp, hrest⟩ := State.run_cons hσ
      refine .cons ⟨y, rest ++ ρ, hp, run_split rest y w ρ x hrest hρ⟩ hp ?_
      exact ih y w hrest (ρ ++ [p]) (run_split ρ w x [p] y hρ (run_one hp))

/-- **THE PER-LEG CLASS WELD** (private per-file copy, dedup-cited
against `Orig/LowSlab.lean`'s `lowslab_class_leg`).  MIND THE WELD:
the setoid is the rev-closure, so the leg's membership reads
`RevEqW s₁ st` — the mirror play is the forward shuffle and the
leg itself, undone, the returning one. -/
private theorem fd_class_leg {st s₁ : State} {m : Move}
    (hrev : reversibleAtW st m) (hstep : State.step st m = some s₁) :
    sameOrbitSetoid.r st s₁ := by
  obtain ⟨s₁', play, hstep', hrun⟩ := hrev
  have hs : s₁' = s₁ := Option.some.inj (hstep'.symm.trans hstep)
  rw [hs] at hrun
  show RevEqW s₁ st
  exact ⟨play, fd_shuffleW_of_round play s₁ st hrun [m] (run_one hstep),
    [m], .cons ⟨s₁, play, hstep, hrun⟩ hstep (.nil s₁)⟩

/-- **THE JOURNEY WALK** (private per-file copy, dedup-cited against
`Orig/LowSlab.lean`'s `lowslab_journey_class`) — every member a
witness journey reaches is a class-mate of the journey's origin:
each reversible leg welds (the setoid's own transitivity), and the
walk is the plain induction. -/
private theorem fd_journey_class {st z : State} {ρ : List Move}
    (hρ : ShufflePlayW st ρ z) : sameOrbitSetoid.r st z := by
  induction hρ with
  | nil s => exact sameOrbitSetoid.iseqv.1 s
  | @cons s m s₁ rest w hrev hstep hrest ih =>
      exact sameOrbitSetoid.iseqv.trans (fd_class_leg hrev hstep) ih

/-- **THE DESCENT IS A WITNESS SHUFFLE** [M] — a successful pull play
from a WF start IS a `ShufflePlayW`: per leg, the banked WF
pull-mirror `lowslab_pull_wf_undo` reads the one-move `tabToFound`
mirror off the leg's own step (the WF premise riding through the
play by `step_wf`), and the mirrors assemble by the plain
induction.  This is the per-leg row the mission prescribes — read
the banked statement first, replicate per leg, then induct. -/
theorem descent_pull_shuffleW :
    ∀ (st : State) (play : List Move) (w : State),
      st.WF → st.run play = some w → PullPlay play →
        ShufflePlayW st play w := by
  intro st play
  induction play generalizing st with
  | nil =>
      intro w _ hrun _
      have hs : some st = some w := hrun
      injection hs with hw
      rw [← hw]
      exact .nil st
  | cons m rest ih =>
      intro w hwf hrun hpulls
      obtain ⟨s₁, hstep, hrest⟩ := State.run_cons hrun
      obtain ⟨c, b, hm⟩ := hpulls m (List.mem_cons_self ..)
      subst hm
      have hwf₁ : s₁.WF := step_wf hwf hstep
      exact .cons (lowslab_pull_wf_undo hwf hstep) hstep
        (ih s₁ w hwf₁ hrest
          (fun (m' : Move) hm' => hpulls m' (List.mem_cons_of_mem _ hm')))

/-- **THE CLASS-PRESERVATION ROW** `descent_stays_class` [M — THE
LOAD-BEARING ROW] — the whole descent stays within the initial
state's macro class: a pull play from a WF start lands at a
class-mate.  The banked WF pull-mirror (`lowslab_pull_wf_undo`)
carries every leg's per-move `tabToFound` mirror, the shuffle row
above assembles the legs' `reversibleAtW` witnesses into one
witness journey, and the class weld walks it home — the chain lemma
the mission names, with the setoid's own symmetry/transitivity
minding the rev-closure's orientation. -/
theorem descent_stays_class {st : State} (hwf : st.WF)
    {play : List Move} {w : State}
    (hrun : st.run play = some w) (hpulls : PullPlay play) :
    sameOrbitSetoid.r st w :=
  fd_journey_class (descent_pull_shuffleW st play w hwf hrun hpulls)

/-! ## §3. The floor claim — the stall-certifies-floor residue -/

/-- **THE WF CHAIN** (private per-file copy of the run-WF walk,
dedup-cited against `Orig/ForkFloor.lean`'s private `p_run_wf`) — a
legal play preserves WF leg by leg (`step_wf`). -/
private theorem fd_run_wf : ∀ (st : State) (play : List Move) (w : State),
    st.WF → st.run play = some w → w.WF := by
  intro st play
  induction play generalizing st with
  | nil =>
      intro w hwf hrun
      have hs : some st = some w := hrun
      injection hs with hw
      rw [← hw]
      exact hwf
  | cons m rest ih =>
      intro w hwf hrun
      obtain ⟨s₁, hstep, hrest⟩ := State.run_cons hrun
      exact ih s₁ w (step_wf hwf hstep) hrest

/-- **THE CLASS OF A WF START IS WF** [E] — every member of a WF
state's macro class is itself WF: the membership unpacks to a
forward witness journey (`sameOrbit_forward`), which is in
particular a legal play, and WF rides it leg by leg.  This is the
member-grade premise the §3 census rows demand — the confinement
row `witness_leg_mint_confined` reads the WF discipline at each
leg's origin. -/
theorem descent_class_wf {st u : State} (hwf : st.WF)
    (hmem : sameOrbitSetoid.r st u) : u.WF := by
  obtain ⟨ρ, hρ⟩ := sameOrbit_forward hmem
  exact fd_run_wf st ρ u hwf (ShufflePlayW_run hρ)

/-- **THE PULL-COUNT EXTRACTION KIT** (private) — a positive pull
count names a pull leg: the counters are the plain cons-census of
the giveback constructor. -/
private theorem fd_pullsOf_pos {σ : Suit} : ∀ (L : List Move),
    0 < pullsOf L σ →
      ∃ (c : Card) (b : Base), Move.foundToTab c b ∈ L ∧ c.suit = σ := by
  intro L
  induction L with
  | nil => intro h; exact absurd h (by simp [pullsOf])
  | cons m t ih =>
      cases m with
      | draw =>
          intro h
          rw [show pullsOf (Move.draw :: t) σ = pullsOf t σ from rfl] at h
          obtain ⟨c, b, hm, hcs⟩ := ih h
          exact ⟨c, b, List.mem_cons_of_mem _ hm, hcs⟩
      | wasteToFound c =>
          intro h
          rw [show pullsOf (Move.wasteToFound c :: t) σ = pullsOf t σ
            from rfl] at h
          obtain ⟨c₁, b, hm, hcs⟩ := ih h
          exact ⟨c₁, b, List.mem_cons_of_mem _ hm, hcs⟩
      | wasteToTab c b =>
          intro h
          rw [show pullsOf (Move.wasteToTab c b :: t) σ = pullsOf t σ
            from rfl] at h
          obtain ⟨c₁, b₁, hm, hcs⟩ := ih h
          exact ⟨c₁, b₁, List.mem_cons_of_mem _ hm, hcs⟩
      | tabToFound c =>
          intro h
          rw [show pullsOf (Move.tabToFound c :: t) σ = pullsOf t σ
            from rfl] at h
          obtain ⟨c₁, b, hm, hcs⟩ := ih h
          exact ⟨c₁, b, List.mem_cons_of_mem _ hm, hcs⟩
      | foundToTab c b =>
          intro h
          rw [show pullsOf (Move.foundToTab c b :: t) σ
              = (if c.suit = σ then 1 else 0) + pullsOf t σ from rfl] at h
          by_cases hcs : c.suit = σ
          · rw [ite_eq_left hcs] at h
            exact ⟨c, b, List.mem_cons_self .., hcs⟩
          · rw [ite_eq_right hcs] at h
            obtain ⟨c₁, b₁, hm, hcs'⟩ := ih (by omega)
            exact ⟨c₁, b₁, List.mem_cons_of_mem _ hm, hcs'⟩
      | tabToTab c b =>
          intro h
          rw [show pullsOf (Move.tabToTab c b :: t) σ = pullsOf t σ
            from rfl] at h
          obtain ⟨c₁, b₁, hm, hcs⟩ := ih h
          exact ⟨c₁, b₁, List.mem_cons_of_mem _ hm, hcs⟩

/-- **THE LOWER-MEMBER CROSSING** [M — proved route-split] — if a
class member `u` reads the suit σ STRICTLY BELOW `W`, then every
witnessing journey `W ⇝ u` carries a σ-pull leg: the rung ledger
(`witness_rung_census`) nets the two readings to a positive pull
count, and the extraction kit names the leg.  This is the
mechanical half of §3's route — the census's own arithmetic, no
open content — banked so the residue carries only its honest
remainder: what the journey DOES with the σ-pulls it must fire. -/
theorem descent_lower_member_crosses_pull {W u : State} {σ : Suit}
    {ρ : List Move} (hρ : ShufflePlayW W ρ u)
    (hlow : rungAt u σ < rungAt W σ) :
    ∃ (c : Card) (b : Base), Move.foundToTab c b ∈ ρ ∧ c.suit = σ := by
  have hledger := witness_rung_census hρ σ
  have hpulls : 0 < pullsOf ρ σ := by omega
  exact fd_pullsOf_pos ρ hpulls

/-- **THE STALLED STATE LACKS THE HOSTS** [E–M] — the
seat-exhaustion datum at the stall: at a maximally-unstacked `W`,
NO pile top fits ANY current foundation top — a fitting host would
license the giveback outright (the top search answers some anchor,
the placement guard reads the fit, and `DescentMove_fires_iff`
fires it against the stuckness).  WF-free, arrangement-only: this
is the stalled-side half of §3's contrapositive, banked on its own
name.  (The census-grade packaging — `hostCensus W col i = 0` at
the one-up opposite-family cells of every current top — is the
seven-seat split of `hostCensus_eq_sum` + the `seatInd` value
rows, `Orig/HostCensus.lean` §0, priced in the residue's route.) -/
theorem descent_stuck_seatExhausted {W : State} {c z : Card} {a : Anchor}
    (hstuck : DescentStuck W) (htop : W.foundTop c.suit = some c)
    (hhost : W.topOf a = some z) (hfit : canSitOn c z = true) : False := by
  have hpy : (fun (k : Anchor) => decide (W.topOf k = some z)) a = true :=
    decide_eq_true hhost
  have hsome := fd_firstWhere_hits
    (fun (k : Anchor) => decide (W.topOf k = some z)) Anchor.all a a.mem_all hpy
  have hsome' : (W.pileOfTop z).isSome = true := hsome
  cases hp : W.pileOfTop z with
  | none =>
      rw [hp] at hsome'
      exact absurd hsome' (by simp)
  | some k =>
      have hcp : W.canPlace c (Sum.inr z) = true := by
        rw [canPlace_inr_located hp, hfit]
      exact hstuck (Move.foundToTab c (Sum.inr z))
        ⟨c, Sum.inr z, rfl, htop, hcp⟩

/-- **THE STALL-CERTIFIES-FLOOR RESIDUE** `descent_stall_certifies_floor`
[H — THE NAMED RESIDUE of this leaf] — the floor claim: if a
maximal descent stalls with the suit σ at rung `h = rungAt W σ`,
then NO class member has that suit below `h` — the stall itself
CERTIFIES the class's rung floor, componentwise.

ROUTE (complete; every mechanical step banked in the transitive
closure or landed in-file above; the single open weave named and
priced; anchored EXACTLY at the census row the mission names, read
as stated):

1. **THE CLASS DIPTYCH** — the mission's §2 chain plus its WF
   face: `descent_stays_class` welds the stall `W` into the
   start's class (`sameOrbitSetoid.r st W`), and
   `descent_class_wf` keeps every member WF — a hypothetical lower
   member `u` (`rungAt u σ < h`) is therefore a WF class-mate, and
   the weld read through the setoid's own symmetry/transitivity
   hands the inter-member journeys BOTH ways; `sameOrbit_forward`
   unpacks each to a forward witness shuffle: `τ : W ⇝ u`,
   `ρ : u ⇝ W`.  (These are witness journeys, so every leg is
   reversible and every leg origin is WF-inherited — the member
   grade `witness_leg_mint_confined` demands.)
2. **THE RUNG LEDGER** (banked, `Orig/BracketDecomp.lean`) —
   `witness_rung_census` reads the σ-rungs along `τ`: the deficit
   `d = h - rungAt u σ` is exactly the NET pull count
   (`pullsOf τ σ - raisesOf τ σ = d`).  LANDED HERE on the
   mechanical half: `descent_lower_member_crosses_pull` — a lower
   member forces `τ` to carry a σ-pull leg; the full serialization
   of the `d` pulls is the per-suit Dyck stack discipline of the
   `Orig/BracketDecomp.lean` program (the rung-walk's own nesting),
   cited not rebuilt.
3. **THE CENSUS ANCHOR** — `excursion_issues_noNewSeat`
   (`Orig/HostCensus.lean`), consumed EXACTLY as stated: the round
   trip `W ⇝ u ⇝ W` is a RETURNED excursion; its per-cell ledger
   reads `hostCensus u col i + journeyBurn W τ col i = hostCensus
   W col i + journeyMint W τ col i` at EVERY (color, index) cell,
   and the two halves' budgets CANCEL cell-for-cell over
   `τ ++ ρ` — the arrangement profile of the stalled state is the
   whole truth of the hosting capacity the excursion rides: a
   returned excursion ISSUES NO NEW SEAT that the stall's
   arrangement does not carry (with `roundtrip_census_repay` the
   repayment half; `seatLedger_pair` / `play_census_ledger` the
   telescoping).
4. **THE MINT CONFINEMENT** (banked) — `witness_leg_mint_confined`
   prices which cells each witnessing leg can mint (WF at the leg's
   origin, step 1's grade): a σ-pull mints ONLY the pulled card's
   own cell (σ's color at the pulled rank `j`), SPENDING the live
   host its own `canPlace` guard demanded — the one-up
   opposite-family cell `((σ's other family), j+1)` — burning it
   from the base seat; raises mint only their exposed below-cards'
   cells; slides their cargo below/landing cells.  So each of the
   `d` σ-pulls burns a host cell the mint side must repay in kind:
   the exact capacity arithmetic step 3 balances per cell.
5. **THE STALLED STATE'S LACK** (LANDED HERE) —
   `descent_stuck_seatExhausted`: at `W` NO host top fits ANY
   current foundation top — in particular, every cell that σ's
   remaining runs (the tops of rungs `≤ h`) would need for ANOTHER
   pull reads EMPTY at `W` (the census-grade packaging a
   seven-seat split away, through `hostCensus_eq_sum` and the
   `seatInd` value rows).
6. **THE OPEN WEAVE** [the residue's entire own content, priced] —
   net steps 3-5 over the deficit `d`: to read σ lower at `u` the
   journey must FIRE the `d` σ-pulls, and each of them demanded a
   LIVE one-up opposite-family host at its leg's origin — the
   journey must MANUFACTURE, host-by-host, the seats the stalled
   arrangement lacks, while the returned tour repays every minted
   cell in kind and the stall's own host cells stay empty at both
   tour ends.  The per-kind accounting — the interleave of the
   σ-pulls' host BURNS with the repaying mint legs (the
   exposure/cargo cells of step 4) under the Dyck serialization of
   step 2, at WF leg origins — is exactly the census's content, and
   the missing piece is the global budget: the mint-and-burn
   interleave cannot simultaneously repay the round trip (step 3)
   and leave every pull-able host cell empty at the tour's `W`-end
   (step 5) when `d > 0`.  NO counterexample family is on record
   for the descent-phrased claim (the neighboring hard content is
   `Orig/ForkFloor.lean`'s own seat-delay residue
   `founded_late_seat_exists`, a different half); the row is priced
   [H], NEVER forced — no premise is added to save it, the canonical
   order and the WF grade both stay exactly as the mission states
   them.

The residue's consumers: the §4 composite note below — the floor's
componentwise minimality is the ascent's handing premise; the
composite's head belongs to a future leaf over both scripts.

SESSION-4 VERDICT (2026-10-13, the fourth succession — REFUTED AT
THE FROZEN STATEMENT): the step-6 weave is FALSE, and the
counterexample family is ON RECORD at decide grade IN-FILE (§3.R
below, `descent_stall_refuted`): a WF, maximally-unstacked stall
(spade rung 3, sole pile top `3♣`, no licensed pull) carries a
BURIED host `4♥` — one-deep in the face-up run `4♥ / 3♣` — that no
pull can see; the two-leg witness journey (raise the next-up `3♣`
— reversible, its giveback mirror onto the exposed host; then the
σ-pull `3♠` onto the exposed `4♥` — reversible, its raise mirror)
lands at a WF class-mate reading spade at rung 2, strictly below the
stall's 3.  THE CANONICAL GAP, named: `descent_stuck_seatExhausted`
pins pile TOPS only, so "every pull-able host cell reads EMPTY at
the `W`-end" is false of a cell OCCUPIED by a buried face-up card,
and the expose-raise mints exactly the one host cell mid-tour that
the σ-pull burns in kind — the mint-and-burn interleave repays the
round trip (step 3 stays satisfied), the global budget (step 6) is
balanced, and the deficit `d > 0` is PAYABLE.  NO repair at a
byte-frozen statement exists in-file (per the never-force
discipline none is smuggled): the owner's options are
statement-level, on the `lowslab_top_census` repair precedent —
strengthen the stall read to buried-host exhaustion, or restrict
the conclusion to pull-only witnessing journeys.  The row keeps
its sorry — the row as stated is FALSE — and hosts at [H, REFUTED].
-/
theorem descent_stall_certifies_floor {st : State} (hwf : st.WF)
    {play : List Move} {W : State}
    (hrun : st.run play = some W)
    (hpulls : PullPlay play)
    (hstuck : DescentStuck W) :
    ∀ (σ : Suit) (u : State), sameOrbitSetoid.r st u →
      rungAt W σ ≤ rungAt u σ := by
  sorry

/-! ### §3.R. THE REFUTATION BOARD (the fourth succession's verdict)

The residue above is REFUTED at the byte-frozen statement, by an
in-file decide-grade counterexample board — the counterexample family
the route's step 6 priced as impossible, made concrete and
kernel-certified.  THE FAMILY (the "buried-host expose-raise"):

* the stalled board `fdR_st` is WF and maximally-unstacked: its only
  pile top is `3♣`, and no foundation top (`3♠`, `3♥`, `2♣`, `6♦`)
  is a king or fits it — the only cards `3♣` could host are the red
  deuces, and neither tops a foundation.  σ = spade sits at rung 3
  (`A♠ 2♠ 3♠`).
* the HOST `4♥` that pulling `3♠` demands is not absent — it is
  BURIED: the one face-up run `4♥ / 3♣` reads `3♣` sitting exactly on
  the host.  Seat exhaustion counts pile TOPS only (the datum
  `descent_stuck_seatExhausted` licenses exactly that), so the buried
  host is invisible to the stall read and free for the class journey.
* the two-leg WITNESS JOURNEY: raise `3♣` (`tabToFound`: `3♣` is
  next-up for clubs and tops its pile — a licensed move the descent
  script never makes) — reversible, its one-move mirror being the
  giveback onto the exposed `4♥`; then the σ-pull `3♠` onto the
  exposed `4♥` (`foundToTab`, licensed at the raised member) —
  reversible, its one-move mirror being the raise back.  The landing
  `fdR_u` reads spade at rung 2 — strictly BELOW the stalled floor —
  while remaining a class-mate (`ShufflePlayW` both ways).
* instantiated at `st := fdR_st`, `play := []`, `W := fdR_st` (the
  empty play satisfies `hrun`/`hpulls` trivially), the residue would
  demand `rungAt fdR_st .spade ≤ rungAt fdR_u .spade` — i.e. `3 ≤ 2`.

WHY THE PRICED ROUTE FAILS (the census weave's exact gap, on
record): the route's step 5 reads the tour's host cells as empty at
the `W`-end, but the face-up run `4♥ / 3♣` occupies its cell at
`fdR_st` all along — only as a non-top.  The manufacture the weave
priced as globally impossible is cheap and local: ONE reversible
raise leg mints exactly the one host seat mid-tour (precisely the
mint the route's own step 4 attributes to raises — "raises mint only
their exposed below-cards' cells"), the σ-pull burns it in kind, and
the returned round trip repays everything: no capacity is issued
beyond the arrangement profile, so step 3's `excursion_issues_noNewSeat`
is satisfied and the step-6 "cannot simultaneously" is simply not a
theorem.  No repair at a byte-frozen statement exists (and none is
smuggled, per the never-force discipline); the owner's recourse is
statement-level, on the `lowslab_top_census` repair precedent:
strengthen the stall read to exhaustion over BURIED face-up hosts as
well — a strictly stronger maximality notion than the descent
script's — or restrict the conclusion's quantifier to pull-only
witnessing journeys.  The residue keeps its sorry (the row as stated
is FALSE) and hosts at [H, REFUTED]; `descent_stall_refuted` below
is the certified witness, zero-sorry. -/

private def fdC (s : Suit) (r : Rank) : Card := ⟨s, r⟩

private def fdStep (st : State) (m : Move) : State :=
  match st.step m with
  | none => st
  | some s' => s'

/-- The thirty-six cards buried under the board's one face-up run —
every card not on a foundation and not face-up, in one hidden deck. -/
private def fdR_deck : List Card :=
  [fdC .spade .four, fdC .spade .five, fdC .spade .six, fdC .spade .seven,
   fdC .spade .eight, fdC .spade .nine, fdC .spade .ten, fdC .spade .jack,
   fdC .spade .queen, fdC .spade .king,
   fdC .heart .five, fdC .heart .six, fdC .heart .seven, fdC .heart .eight,
   fdC .heart .nine, fdC .heart .ten, fdC .heart .jack, fdC .heart .queen,
   fdC .heart .king,
   fdC .diamond .seven, fdC .diamond .eight, fdC .diamond .nine,
   fdC .diamond .ten, fdC .diamond .jack, fdC .diamond .queen,
   fdC .diamond .king,
   fdC .club .four, fdC .club .five, fdC .club .six, fdC .club .seven,
   fdC .club .eight, fdC .club .nine, fdC .club .ten, fdC .club .jack,
   fdC .club .queen, fdC .club .king]

/-- The stalled board: `A♠ 2♠ 3♠ / A♥ 2♥ 3♥ / A♣ 2♣ / A♦…6♦` on the
foundations; one face-up run `4♥ / 3♣` over the buried deck; both
zones empty, deal size 1. -/
private def fdR_hmap : Suit → Nat
  | .spade => 3 | .heart => 3 | .diamond => 6 | .club => 2

private def fdR_st : State where
  found := fun s => s.upCards.take (fdR_hmap s)
  piles := fun a => match a with
    | .p3 => ⟨fdR_deck, [fdC .heart .four, fdC .club .three]⟩
    | _ => ⟨[], []⟩
  stock := []
  waste := []
  drawStep := 1

/-- the raised intermediate: `3♣` founded, `4♥` exposed. -/
private def fdR_s1 : State :=
  fdStep fdR_st (Move.tabToFound (fdC .club .three))

/-- the lower class-mate: `3♠` pulled back onto the exposed `4♥`. -/
private def fdR_u : State :=
  fdStep fdR_s1
    (Move.foundToTab (fdC .spade .three) (Sum.inr (fdC .heart .four)))

/-- THE STALLED BOARD IS WF — foundations are prefixes by the map,
the lone face-up run is legal, the full deck is counted once, the
deal size is positive. -/
private theorem fdR_st_wf : fdR_st.WF := by
  refine ⟨fun s => ⟨fdR_hmap s, rfl⟩, ?_, ?_, ?_⟩
  · intro a
    cases a <;> rfl
  · intro c _
    rcases c with ⟨s, r⟩
    cases s <;> cases r <;> decide
  · decide

/-- The one pile of the board tops at exactly `3♣` (the search's
answer, pinned for the stall read). -/
private theorem fdR_top_pin {z : Card} {a : Anchor}
    (h : fdR_st.pileOfTop z = some a) : z = fdC .club .three := by
  have hz : fdR_st.topOf a = some z :=
    of_decide_eq_true (firstWhere_sound
      (fun k => decide (fdR_st.topOf k = some z)) h)
  cases a with
  | p3 =>
      have h2 : (some (fdC .club .three) : Option Card) = some z := hz
      injection h2 with h3
      exact h3.symm
  | p0 =>
      have h2 : ((none : Option Card) = some z) := hz
      injection h2
  | p1 =>
      have h2 : ((none : Option Card) = some z) := hz
      injection h2
  | p2 =>
      have h2 : ((none : Option Card) = some z) := hz
      injection h2
  | p4 =>
      have h2 : ((none : Option Card) = some z) := hz
      injection h2
  | p5 =>
      have h2 : ((none : Option Card) = some z) := hz
      injection h2
  | p6 =>
      have h2 : ((none : Option Card) = some z) := hz
      injection h2

/-- No current foundation top can be placed anywhere on the stalled
board: the empty anchors want kings, and the only pile top `3♣`
hosts nothing they fit. -/
private theorem fdR_canPlace_false {c : Card}
    (hfour : c = fdC .spade .three ∨ c = fdC .heart .three ∨
      c = fdC .club .two ∨ c = fdC .diamond .six)
    (b : Base) : fdR_st.canPlace c b = false := by
  cases b with
  | inl a =>
      rw [canPlace_inl_unfold]
      have hking : decide (c.rank = Rank.king) = false := by
        rcases hfour with rfl | rfl | rfl | rfl <;> rfl
      rw [hking]
      cases _hb : (fdR_st.piles a).isEmpty <;> rfl
  | inr z =>
      cases hsearch : fdR_st.pileOfTop z with
      | none =>
          rw [canPlace_inr_eq, hsearch]
      | some k =>
          rw [canPlace_inr_located hsearch, fdR_top_pin hsearch]
          rcases hfour with rfl | rfl | rfl | rfl <;> decide

/-- THE STALLED BOARD IS MAXIMALLY-UNSTACKED — no licensed pull
remains: every `DescentMove` names a foundation top, the four tops
admit no placement. -/
private theorem fdR_st_stuck : DescentStuck fdR_st := by
  intro _ hmove
  obtain ⟨c, b, -, htop, hcp⟩ := hmove
  have hfour : c = fdC .spade .three ∨ c = fdC .heart .three ∨
      c = fdC .club .two ∨ c = fdC .diamond .six := by
    cases hs : c.suit with
    | spade =>
        rw [hs] at htop
        have h2 : (some (fdC .spade .three) : Option Card) = some c := htop
        injection h2 with h3
        exact Or.inl h3.symm
    | heart =>
        rw [hs] at htop
        have h2 : (some (fdC .heart .three) : Option Card) = some c := htop
        injection h2 with h3
        exact Or.inr (Or.inl h3.symm)
    | club =>
        rw [hs] at htop
        have h2 : (some (fdC .club .two) : Option Card) = some c := htop
        injection h2 with h3
        exact Or.inr (Or.inr (Or.inl h3.symm))
    | diamond =>
        rw [hs] at htop
        have h2 : (some (fdC .diamond .six) : Option Card) = some c := htop
        injection h2 with h3
        exact Or.inr (Or.inr (Or.inr h3.symm))
  rw [fdR_canPlace_false hfour] at hcp
  exact absurd hcp (by decide)

/-- THE EXPOSE-RAISE FIRES at the stalled board (its one-move mirror:
the giveback onto the exposed `4♥`). -/
private theorem fdR_raise_at_st :
    State.step fdR_st (Move.tabToFound (fdC .club .three)) = some fdR_s1 := by
  rfl

/-- the raise's mirror at the raised intermediate lands back at the
stall, exactly. -/
private def fdR_st' : State :=
  fdStep fdR_s1 (Move.foundToTab (fdC .club .three) (Sum.inr (fdC .heart .four)))

private theorem fdR_st'_eq : fdR_st' = fdR_st := by
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
  · cases σ <;> rfl
  · cases a <;> rfl
  · rfl
  · rfl
  · rfl

private theorem fdR_giveback_at_s1 :
    State.step fdR_s1
      (Move.foundToTab (fdC .club .three) (Sum.inr (fdC .heart .four))) =
      some fdR_st := by
  rw [← fdR_st'_eq]
  rfl

/-- THE σ-PULL FIRES at the raised member, onto the exposed `4♥`
(its one-move mirror: the raise back). -/
private theorem fdR_pull_at_s1 :
    State.step fdR_s1
      (Move.foundToTab (fdC .spade .three) (Sum.inr (fdC .heart .four))) =
      some fdR_u := by
  rfl

/-- the pull's mirror at the lower class-mate lands back at the
raised intermediate, exactly. -/
private def fdR_s1' : State := fdStep fdR_u (Move.tabToFound (fdC .spade .three))

private theorem fdR_s1'_eq : fdR_s1' = fdR_s1 := by
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
  · cases σ <;> rfl
  · cases a <;> rfl
  · rfl
  · rfl
  · rfl

private theorem fdR_raise_at_u :
    State.step fdR_u (Move.tabToFound (fdC .spade .three)) = some fdR_s1 := by
  rw [← fdR_s1'_eq]
  rfl

/-- **THE LOWER CLASS-MATE** — the stalled board and the two-leg
landing are joined by witness shuffles BOTH ways: forward the
expose-raise then the σ-pull (each with its one-move mirror), backward
their exact mirrors mirrored.  This is the membership premise the
residue demands of its hypothetical lower member, witnessed. -/
private theorem fdR_class : sameOrbitSetoid.r fdR_st fdR_u :=
  ⟨[Move.tabToFound (fdC .spade .three),
     Move.foundToTab (fdC .club .three) (Sum.inr (fdC .heart .four))],
    ShufflePlayW.cons
      ⟨fdR_s1,
        [Move.foundToTab (fdC .spade .three) (Sum.inr (fdC .heart .four))],
        fdR_raise_at_u, run_one fdR_pull_at_s1⟩
      fdR_raise_at_u
      (ShufflePlayW.cons
        ⟨fdR_st, [Move.tabToFound (fdC .club .three)],
          fdR_giveback_at_s1, run_one fdR_raise_at_st⟩
        fdR_giveback_at_s1
        (ShufflePlayW.nil fdR_st)),
    [Move.tabToFound (fdC .club .three),
     Move.foundToTab (fdC .spade .three) (Sum.inr (fdC .heart .four))],
    ShufflePlayW.cons
      ⟨fdR_s1,
        [Move.foundToTab (fdC .club .three) (Sum.inr (fdC .heart .four))],
        fdR_raise_at_st, run_one fdR_giveback_at_s1⟩
      fdR_raise_at_st
      (ShufflePlayW.cons
        ⟨fdR_u, [Move.tabToFound (fdC .spade .three)],
          fdR_pull_at_s1, run_one fdR_raise_at_u⟩
        fdR_pull_at_s1
        (ShufflePlayW.nil fdR_u))⟩

/-- **THE RESIDUE IS REFUTED** — the stall-certifies-floor claim is
FALSE at its byte-frozen statement: the exhibited WF, maximally-unstacked
`fdR_st` (a legal empty descent of itself), joined to the exhibited
lower class-mate `fdR_u` (the buried-host expose-raise's two-leg
landing), reads spade at rung 3 against its class-mate's 2.  The row
`descent_stall_certifies_floor` above therefore cannot land — its
`sorry` is the honest witness of a FALSE statement, and the owner's
recourse is the statement-level repair priced in §3.R's header. -/
theorem descent_stall_refuted :
    ¬ ∀ (st : State), st.WF → ∀ (play : List Move) (W : State),
      st.run play = some W → PullPlay play → DescentStuck W →
      ∀ (σ : Suit) (u : State), sameOrbitSetoid.r st u →
        rungAt W σ ≤ rungAt u σ := by
  intro h
  have hle := h fdR_st fdR_st_wf [] fdR_st rfl
    (fun _ hm => absurd hm (by simp)) fdR_st_stuck Suit.spade fdR_u fdR_class
  have h3 : rungAt fdR_st Suit.spade = 3 := rfl
  have h2 : rungAt fdR_u Suit.spade = 2 := rfl
  omega

/-! ## §4. The composite (route note only — no import)

**THE UNSTACK-THEN-ASCENT COMPOSITION.**  For `s` reachable in the
program's own sense — `initialReachable s`, so `s.WF` by
`initialReachable_wf` (`Orig/Reach.lean`) — §1's
`descent_reaches_floor` delivers a maximally-unstacked `W` in a
pull play of at most `foundTotal s` legs; §2's
`descent_stays_class` keeps `W` in `s`'s macro class (and the
whole journey is `sameFate`-preserving through
`RevEqW_sameFate`, `Orig/Combine.lean`); §3's
`descent_stall_certifies_floor` — the named residue, once it
lands — then reads the end state as the CLASS-MINIMAL RUNG-FLOOR
COMPONENTWISE: `rungAt W σ ≤ rungAt u σ` at every class member
`u` and every suit σ.  The descent therefore reaches the class's
floor, and the floor is therefore ≤ every member — the mission's
"unstack reaches the class-minimal rung-floor componentwise,
therefore ≤ every member", the composite's descent half in the
two-row shape this leaf can bank.

**THE ASCENT HAND-OFF** (prose citations only — `Orig/ForkAscent.lean`
is under active repair; this file takes NO import of it): the
stacking sibling climbs from the unstacked shape — its
`AscentMove` (the full-time no-eat stacking discipline: raises of
cards that are no member of any intact mobile twin pair, plus
arrangement slides), its `AscentRun`/`AscentStuck` exhaustion
dialect, whose banked halves are `ascent_stuck_collapse` and
`ascent_stuck_unblocked`, its delivered shape `TwinSlideHalt` (a
double-hot intact pair one cargo slide from the covered-twin
orientation, assembled by `orientation_assembly_fork`), and its
exhaustion row `ascent_exhaustion_forks`: the exhaustion state IS
the fork shape.  The two scripts compose: the descent's `W` is
the ascent's below-frontier start (foundations at the class
floor, the whole liftable inventory face-up in the tableau), and
the composite's fixed point is the `ForkWitness` certificate —
the shared mouth of `Orig/LowSlab.lean`'s neighborhood program
(`fork_neighbor_lowbridge`'s premise shape).

The composite is deliberately NOT stated as a theorem in this
leaf: §3's residue must land first (the floor's componentwise
minimality is the ascent's handing premise), and the composition
head belongs to a fresh leaf over both scripts.  Everything the
descent half needs is banked in this file; nothing here depends
on the sibling's repair state. -/

/-! ## The audit battery

`#print axioms` per fresh head, the landed rows first, then the named
residue.  THE PROFILES AS LANDED: every §0–§3 row is zero-sorry at
the house's clean grade — `[propext]` or `[propext, Quot.sound]`
(the family of `lowslab_pull_wf_undo`'s own
`[propext, Quot.sound]` battery grade in `Orig/LowSlab.lean`) —
with NO `Classical.choice` inflow anywhere (the canonical order
bought that: all splits are `Bool`/`Option`/decidable reads).  The
found-census rows (`descent_pull_drops`,
`descent_run_foundTotal_bound`, `fd_descent_fuel`,
`descent_reaches_floor`), the §2 chain and the census-adjacent
§3 supports read `[propext, Quot.sound]`; the pick's soundness row
(`descent_pick_pulls`), the schedule kit and the fuel-free
inductions sit at `[propext]`-only.  The single `sorry` of the
leaf is §3's `descent_stall_certifies_floor`, profile EXACTLY
`[propext, sorryAx]` — its own named residue, NO other inflow —
and the `sorry`-warning count of the file is exactly one: any
change that grows either side regresses the battery.

THE §3.R REFUTATION BOARD (the fourth succession's additions): the
board rows are zero-sorry at decide/defeq grade — all computations
on closed boards (no `Classical.choice`; the `State.ext` dances ride
`funext`, so the rows reading states read `[propext, Quot.sound]`,
the pure-`Bool`/decide rows `[propext]` or
`[propext, Quot.sound]` per their consumption).  The fresh public
head `descent_stall_refuted` — the certified negation of the
residue's own statement — is ZERO-sorry: the residue keeps its
sorry (the row as stated is FALSE, §3.R's record), so the sorry
count stays exactly one and every other profile stands. -/

#print axioms fd_mem_ladder
#print axioms fd_mem_cycle
#print axioms mem_descentSchedule
#print axioms mem_descentBases
#print axioms fd_firstWhere_hits
#print axioms mem_descentPairs
#print axioms DescentMove_fires_iff
#print axioms descent_pick_pulls
#print axioms descent_pick_fires
#print axioms descent_pick_none_stuck
#print axioms descent_floor_zero_stuck
#print axioms fd_flatMap_length
#print axioms rungSum_eq_foundTotal
#print axioms fd_rung_delta
#print axioms descent_pull_drops
#print axioms descent_run_foundTotal_bound
#print axioms fd_descent_fuel
#print axioms descent_reaches_floor
#print axioms fd_shuffleW_of_round
#print axioms fd_class_leg
#print axioms fd_journey_class
#print axioms descent_pull_shuffleW
#print axioms descent_stays_class
#print axioms fd_run_wf
#print axioms descent_class_wf
#print axioms fd_pullsOf_pos
#print axioms descent_lower_member_crosses_pull
#print axioms descent_stuck_seatExhausted
#print axioms descent_stall_certifies_floor
#print axioms fdR_st_wf
#print axioms fdR_top_pin
#print axioms fdR_canPlace_false
#print axioms fdR_st_stuck
#print axioms fdR_raise_at_st
#print axioms fdR_st'_eq
#print axioms fdR_giveback_at_s1
#print axioms fdR_pull_at_s1
#print axioms fdR_s1'_eq
#print axioms fdR_raise_at_u
#print axioms fdR_class
#print axioms descent_stall_refuted
