import Orig2.Fork.Class.ForkOneColourClosure
import Orig2.Substrate.PairClassSeed

set_option autoImplicit false

/-!
# Orig2.Fork.Class.ForkRaiseReorder — the raiseS reordering card

Vocabulary, the **true** one-way obligations, and the recorded residuals.  The
three obligations this card used to state (`RaiseAbove`, `SpecShift`,
`RaiseSReorder`) were **false as written**; they have been replaced by their
forward forms and by the rank-front target, and every refutation is recorded
in the docstring of the statement it kills.

A `raiseS` step is *slide to expose, then raise*:

    RaiseStepS z z' c  :=  ∃ z₀, CargoPath z z₀ ∧ step z₀ (tabToFound c) = some z'

A `raiseS` sequence is a word of raised cards.  **Word/play convention:**
`RaiseSSeq`'s head is the **last** raise, so a *play* `P = [σ₁, …, σₙ]`
(σ₁ raised first) is the word `P.reverse`.

## Status ledger

```
unsorted front  ([c] ++ ws.erase c)              FALSE    2 kernel refutations
rank-front      ([c] ++ sortRank (ws.erase c))   PROVED   at the licensed grade
                                                          (`RaiseSSeqLicensed` / `CanRaiseS`),
                                                          unconditional: no rank, twin, or
                                                          reachability side conditions
`↔` forms of SpecShift / RaiseAbove              FALSE    forward forms proved, side conditions removed
```

The ledger's lists are written in *play* order; `rankFrontWord` below is the
corresponding word (`(sortByRank (ws.erase c)).reverse ++ [c]`, whose play is
`c :: sortByRank (ws.erase c)`).

The proof of rank-front is `raiseS_rankfront_L` + `tail_exists` in
`Temp/RankFront_tail.lean`; the card states the same proposition as `RankFront`
below.  The carrier matters: see H1.

## What is proved here (inline)

Definitions: `RaiseStepS`, `RaiseSSeq`, `RaiseSSeqLicensed`.  Proved inline:
`suit_eq_or_twin_of_color`, `cover_seats`, `cover_seats_cases`,
`nextUp_raise_ne`.  Everything else is a `def … : Prop` obligation, each
pointing at its checked proof in `Temp/`.

## H1 — the licence, now closed by naming the right carrier

`RaiseSSeq.cons` carries only `State.step`, never `CanRaise`.  A bridge
"`State.step z (tabToFound c) = some z'` implies `CanRaise z c`" is
**impossible**, not merely inconvenient: `Temp/RankFront_proof.lean` has
`t4a_fires` (the step fires) together with `t4a_not_canRaise` (the licence
fails) — the raise flips a hidden card, i.e. it is a commit.

So the play relation is `RaiseSSeqLicensed` below, whose letters carry
`CanRaiseS`.  It is **exactly** the reversible grade: every step of a licensed
play is a witness shuffle (`canRaiseS_iff_reversible`-side rows in
`Temp/RankFront_licensed.lean`), and `RaiseSSeqLicensed → RaiseSSeq` is strict.
Every theorem of this lane is stated for the licensed grade.

## H2 — replay across shifted prefixes, now closed

In ascending order a later step runs at a state whose raised-set differs from
that of the original word, so licences must be *transferred* rather than
replayed.  Three rows close it (`Temp/RankFront_licensed.lean`,
`Temp/RankFront_close.lean`, `Temp/RankFront_tail.lean`):

* **licences depend only on the raised multiset.**  A licensed raise is
  reversible (`CanRaise z c ↔ tabToFoundR z c = true`), hence every licensed
  play is a witness shuffle, so any two licensed endpoints from the same start
  are `RevEqW`-mates; rungs are the multiset and equal rungs give equal
  licences.  Concretely: `canRaiseS_of_raise_perm` — order and slide choices
  are invisible to licences;
* **rank transfer.**  A strictly higher-rank raise is licence-inert in *both*
  directions when licensed (`canRaiseS_inert_of_canRaiseStep`), and R1 moves
  licences forward across other ranks (`canRaiseS_persist_of_rank_ne`);
* **the tie block.**  The state-level equal-rank swap is false (the twins may
  each be licensed only via the other topping a pile), but the play-level swap
  goes through: un-raising the twin to the vanilla witness forces the second
  card to be exposed there, and then `twin_raise_square` commutes the two
  vanilla raises (`tie_swap`, `tieFree`).

The old plan's `canRaiseS_unraise_of_rank_lt` (higher-rank inertness for the
*weak* step) is **false** and kernel-refuted: `unraise_probe_refutes`,
`Temp/RankFront_licensed.lean`, where a commit raise reveals the twin of the
lower-rank card.  Inertness holds only with the licence attached.

## The one-colour closure references

`twin_raise_square` (`Orig2/Fork/Local/ForkCriticalPair.lean:241`) for the two
exposed twins, and `freeCardS_orbit_rung` (`Orig2/Fiber/FreeOrbit.lean:1376`)
for replaying a tail at an equal-rung class-mate.
-/

namespace OneColourClosure

/-! ## §1. The step relation -/

/-- One `raiseS` step: slide inside the slide-fibre to expose `c`, then raise it. -/
def RaiseStepS (z z' : State) (c : Card) : Prop :=
  ∃ z₀, CargoPath z z₀ ∧ State.step z₀ (Move.tabToFound c) = some z'

/-- A `raiseS` sequence, indexed by the word of raised cards.  The head of the
word is the **last** raise.  The step is `State.step` only, so this relation
**admits commit raises** (§2b) and is *not* the play relation — never state a
play theorem over it.  See H1 in the module docstring; use `RaiseSSeqLicensed`. -/
inductive RaiseSSeq : State → List Card → State → Prop
  | nil (s : State) : RaiseSSeq s [] s
  | cons {s z z₀ z' : State} {c : Card} {ws : List Card} :
      RaiseSSeq s ws z →
      CargoPath z z₀ →
      State.step z₀ (Move.tabToFound c) = some z' →
      RaiseSSeq s (c :: ws) z'

/-- The **licensed** `raiseS` sequence (H1's repair): every letter carries the
licence `CanRaiseS` at the state where its slide begins.

This is the honest carrier for any replay argument.  It is *not* derivable from
`RaiseSSeq`: `Temp/RankFront_proof.lean` `t4a_fires` + `t4a_not_canRaise` is a
firing step whose card is not `CanRaise`, so the forgetful map
`RaiseSSeqLicensed → RaiseSSeq` is strict. -/
inductive RaiseSSeqLicensed : State → List Card → State → Prop
  | nil (s : State) : RaiseSSeqLicensed s [] s
  | cons {s z z₀ z' : State} {c : Card} {ws : List Card} :
      RaiseSSeqLicensed s ws z →
      CanRaiseS z c →
      CargoPath z z₀ →
      State.step z₀ (Move.tabToFound c) = some z' →
      RaiseSSeqLicensed s (c :: ws) z'

/-! ## §2. Suit bookkeeping (proved) -/

/-- The `nextUp` half of `SpecShift`: a raise in one suit never disturbs the
next-up condition of a card of another suit. -/
theorem nextUp_raise_ne {z z' : State} {c d : Card}
    (h : State.step z (Move.tabToFound c) = some z') (hd : d.suit ≠ c.suit) :
    z'.nextUp d = z.nextUp d := by
  unfold State.nextUp
  have hh : z'.foundHeight d.suit = z.foundHeight d.suit := by
    show rungAt z' d.suit = rungAt z d.suit
    rw [rungAt_tabToFound h d.suit, if_neg hd]
  rw [hh]

/-! ## §2b. Commits are exactly the irreversibles

A raise letter can fire `State.step` without being a legal play letter.  The
campaign already names that failure: the move is **not reversible**
(`¬ reversibleAtW`).  No new predicate is introduced here; the `Bool` read
`tabToFoundR` is used only as the decidable shape of the standard notion
(`tabToFoundR_iff_reversibleAtW`,
`Orig2/Substrate/Classification.lean:1858`).

The exclusion is one line: a licensed raise is reversible, hence never a commit.  `RaiseSSeqLicensed` therefore contains no commits by construction;
`RaiseSSeq` does (H1) — that relation is not the play relation.

## Living in the reversible space

At a `WF` state, for a raise letter `licensed` and `reversibleAtW` are the same
predicate (`tabToFoundR_iff_canRaise` + `tabToFoundR_iff_reversibleAtW`), and a
cargo leg carries its own undoability by definition (`CargoLeg`).  So every
`RaiseSSeqLicensed` play is a play of reversible moves, and any two such plays
from the same start are `RevEqW`-mates (`shufflePlayW_revEqW`).  Nothing in this
lane is outside the reversible space.

Why the carrier is the **card word** and not `List Move`: `CargoLeg` is
`∃ c b, tabToTab c b fires ∧ reversible`, so a slide's *move* is existentially
hidden.  Flattening a `CargoPath` into a `Walk reversibleAtW` with an explicit
move list would need `Classical.choice`, which this development forbids.  The
card word is the constructive presentation of the same plays: it records the
raised cards and keeps the slides existential.  A `List Move` formulation is a
corollary for plays that arrive with their slide letters written down (all
letters `tabToFound`, each `reversibleAtW`), via `canRaise_of_reversibleAtW`. -/

/-- **`CanRaise` is literally the undoability shape `tabToFoundR`.**  Both are
`nextUp ∧ pileOfTop = some a ∧ (chop faceUp ≠ [] ∨ (hidden = [] ∧ c king))`,
only one is a `Prop` and the other a `Bool`; no `WF` needed. -/
theorem tabToFoundR_iff_canRaise (st : State) (c : Card) :
    tabToFoundR st c = true ↔ CanRaise st c := by
  unfold tabToFoundR CanRaise
  cases hn : st.nextUp c with
  | false => simp
  | true =>
    cases hp : st.pileOfTop c with
    | none => simp
    | some a =>
      cases hc : chop (st.piles a).faceUp with
      | nil =>
        cases hh : (st.piles a).hidden with
        | nil => simp [hc, hh]
        | cons x xs => simp [hc, hh]
      | cons x xs => simp [hc]

theorem canRaise_of_reversibleAtW {z : State} {c : Card} (hz : z.WF)
    (h : reversibleAtW z (Move.tabToFound c)) : CanRaise z c :=
  (tabToFoundR_iff_canRaise z c).mp ((tabToFoundR_iff_reversibleAtW hz c).mpr h)

/-- **`CanRaiseS`, written in the reversible space.**  The S-licence is the
cargo span of the reversible raise letter: a reversible slide path to a state
where the raise itself is reversible.  Same predicate as `CanRaiseS`
(`Orig2/Substrate/Vocab.lean:485`), phrased with `CargoPath` and
`reversibleAtW` only.

Note the state: the raise may be illegal at `z` itself (a slide may be needed
first), so the reversible-raise read belongs at the *end* of the cargo path, not
at `z`. -/
theorem canRaiseS_iff_cargoPath_reversibleAtW {z : State} {c : Card} (hz : z.WF) :
    CanRaiseS z c ↔ ∃ z₀, CargoPath z z₀ ∧ reversibleAtW z₀ (Move.tabToFound c) := by
  constructor
  · rintro ⟨z₀, hp, hc⟩
    exact ⟨z₀, hp, DrainClose.reversibleAtW_tabToFound_of_canRaise (cargoPath_wf hz hp) hc⟩
  · rintro ⟨z₀, hp, hrev⟩
    exact ⟨z₀, hp, canRaise_of_reversibleAtW (cargoPath_wf hz hp) hrev⟩

/-- **A non-reversible move is not a raise letter.**  This is the commit
exclusion in the repo's own terms: no new predicate, just `reversibleAtW` (the
standard notion) and `CanRaise` (the standard licence).  The "fires" half is not
needed: reversibility alone decides the licence. -/
theorem not_canRaise_of_not_reversibleAtW {z : State} {c : Card} (hz : z.WF)
    (hrev : ¬ reversibleAtW z (Move.tabToFound c)) : ¬ CanRaise z c :=
  fun hc => hrev (DrainClose.reversibleAtW_tabToFound_of_canRaise hz hc)

/-! ## §3. Covers (proved) -/

/-- **OBLIGATION 1 (cover seats) — PROVED.**
A card `x` that may sit on `c.twin` has, among all tableau cards, only two
possible seats: `c` and `c.twin` itself. -/
theorem cover_seats {x c y : Card}
    (hx : canSitOn x c.twin = true) (hy : canSitOn x y = true) :
    y = c ∨ y = c.twin := by
  rw [canSitOn_eq] at hx hy
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  rw [Card.twin_rank] at hx1
  rw [Card.twin_suit, Suit.color_twin] at hx2
  -- ranks agree
  have hrank : y.rank = c.rank := Rank.toIdx_inj (by omega)
  -- colours agree (two-valued)
  have hcol : y.suit.color = c.suit.color := by
    rcases hxy : y.suit.color with _ | _ <;>
      rcases hcx : c.suit.color with _ | _ <;>
      rcases hxx : x.suit.color with _ | _ <;> simp_all
  rcases SeedKit.suit_family hcol with hs | hs
  · left
    cases y; cases c; simp_all
  · right
    cases y; cases c; simp_all [Card.twin]

/-- **The seats of a card that sits on `t`**: only `t` and `t.twin`.
Proved here from `cover_seats`; the same row is `seat_possibilities` in
`Temp/RankFront_final.lean:86`. -/
theorem cover_seats_cases {x t y : Card} (hxt : canSitOn x t = true)
    (hy : canSitOn x y = true) : y = t ∨ y = t.twin := by
  have hc : canSitOn x t.twin.twin = true := by rw [card_twin_twin]; exact hxt
  have h := cover_seats (c := t.twin) (x := x) (y := y) hc hy
  rw [card_twin_twin] at h
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

/-! ## §4. Rank order

A pile is a strictly descending run, so a card *above* another in the same
pile has strictly lower rank.  This is the "ascending clears covers first"
primitive of the rank-front route. -/

/-! ## §5. Licence propagation

Raising a card never disturbs the licence of a card of **different rank**:
twins share their rank, so both side conditions of `SpecShiftFwd` are
automatic.  The rank split that the old `↔` needed (above/below, with different
pile hypotheses) collapses: one forward step lemma covers both regimes, and no
converse is claimed. -/

/-! ## §6. The cover lock

While `x` sits on `t` and `t.twin` is founded, `x` has no legal placement
anywhere in the cargo class, so `t` is never a pile top there — hence `t` can
never be raised.  The state-level half is closed; the play-level passage is
the named residual `CoverMustBeRaisedWord`. -/

/-- **The cover must be raised (play level) — PROVED.**  If `x` sits on `t` and
`t.twin` is founded at `s`, then every valid `raiseS` word that raises `t`
also raises `x`.

PROVED: `cover_must_be_raised` (`Temp/RankFront_licensed.lean`), by induction
over the play: seats survive raises (`seatOf_tabToFound_of_seated_ne`) and
cargo legs (`seatOf_cargoLeg_of_seated`), the invariant is
`seat_invariant_of_not_mem`, and the state-level close is
`twin_covered_persists`.  A licensed (`RaiseSSeqLicensed`) version is proved
alongside as `cover_must_be_raised_L`; use the licensed one for plays. -/
def CoverMustBeRaisedWord : Prop :=
  ∀ {s z : State} {ws : List Card} {x t : Card},
    RaiseSSeq s ws z → s.WF → seatOf s x = some (Sum.inr t) →
      t.twin ∈ s.found t.twin.suit → t ∈ ws → x ∈ ws

/-! ## §8. The rank-front target -/

/-- Insert `a` into an ascending-by-rank list (stable: on a tie `a` goes first). -/
def insertByRank (a : Card) : List Card → List Card
  | [] => [a]
  | b :: t => if a.rank.toIdx ≤ b.rank.toIdx then a :: b :: t else b :: insertByRank a t

/-- Ascending (stable) sort of a play by rank. -/
def sortByRank : List Card → List Card
  | [] => []
  | a :: t => insertByRank a (sortByRank t)

/-- **`rankFrontWord c ws`** — the word whose *play* is
`c :: sortByRank (ws.erase c)`: `c` raised first, then the rest of `ws` in
ascending rank order.  (`RaiseSSeq`'s head is the last raise, hence the
`reverse` and the trailing `[c]`.) -/
def rankFrontWord (c : Card) (ws : List Card) : List Card :=
  (sortByRank (ws.erase c)).reverse ++ [c]

/-- **THE RANK-FRONT TARGET — PROVED (licensed grade).**

If `c` is raisableS at `s` and a **licensed** `raiseS` word from `s` contains
`c`, then the word whose play raises `c` first and the rest in ascending rank
order is realisable from `s`.

PROVED: `rankFront_holds` in `Orig2/Fork/Class/ForkRaiseReorderProof.lean`, which
discharges this `def` verbatim; the proof lives in `ForkRaiseReorderKit` /
`ForkRaiseReorderProof` (`raiseS_rankfront_L`, `tail_exists`,
`canRaiseS_of_raise_perm`, `cover_must_be_raised`, `tie_swap`/`tieFree`).
Unconditional — no rank, twin, fork, reachability or distinctness
side condition.  Earlier fragments: `raiseS_rankfront_of_licensed`
(`Temp/RankFront_proof.lean:130`, the "all cards licensed at `s`, distinct
ranks" case) and the sorted-play theorem `raiseS_sorted_of_licensed`
(`Temp/RankFront_close.lean`).  The intermediate rows are `canRaiseS_of_raise_perm`
(licences depend only on the raised multiset), `canRaiseS_inert_of_canRaiseStep`
and `canRaiseS_persist_of_rank_ne` (rank transfer), `tie_swap` / `tieFree` (the
play-level tie block) and `cover_must_be_raised` (R3).

**Do not state it over `RaiseSSeq`**: that relation admits commit raises whose
licences are missing (H1), and the rank-front theorem is not known to survive
the weakening; no refutation is known either.  `RaiseSSeqLicensed` is the
carrier.

**Two false neighbours — do not re-attack them:**

* the **unsorted** front `c :: ws.erase c` is FALSE:
  `raiseSReorder_false` (`Temp/Reorder_proof.lean:318`).  Witness
  `probeState`: `p0 = ⟨[], [10♦, 9♠, 8♥]⟩`, foundations `♠ A..8`, `♥ A..7`,
  `♦ = ♣ = []`, the rest stock, and *no* cargo slide fires there.  The word
  `[9♠, 8♥]` (play `8♥` then `9♠`) is valid and `c = 8♥` is raisableS, but
  `[8♥, 9♠]` would have to raise `9♠` first — it is buried under `8♥`, so the
  reordered word is invalid.
* the **unsorted play-front** `ws.erase c ++ [c]` (i.e. `c` first, tail as-is)
  is FALSE: `raiseSReorderFront_false`
  (`Temp/Reorder_front_proof.lean:308`).  Witness `probeState`:
  `p0 = ⟨[], [K♥]⟩`, `p1 = ⟨[], [K♦, Q♠]⟩`, foundations `♠ A..J`, `♥ A..Q`,
  `♦ A..Q`, `♣ = []`.  The word `[K♥, Q♠, K♦]` (play `K♦`, `Q♠`, `K♥`) is
  valid and `c = K♥` is raisableS, but the front word `[Q♠, K♦, K♥]` (play
  `K♥`, `K♦`, `Q♠`) is invalid: raising `K♥` first founds the only remaining
  seat of `Q♠`, the cover of `K♥`'s twin `K♦` — this is exactly the
  `CoverMustBeRaisedWord` obstruction.

Sorting the tail removes both obstacles: in the first witness the sorted word
is the original valid word `[9♠, 8♥]`; in the second it is `[K♦, Q♠, K♥]`
(play `K♥`, `Q♠`, `K♦`), which is valid although it is not the original word. -/
def RankFront : Prop :=
  ∀ {s : State} {c : Card}, s.WF → CanRaiseS s c →
    ∀ {ws : List Card} {z : State}, RaiseSSeqLicensed s ws z → c ∈ ws →
      ∃ z', RaiseSSeqLicensed s (rankFrontWord c ws) z'

end OneColourClosure

#print axioms OneColourClosure.nextUp_raise_ne
#print axioms OneColourClosure.cover_seats
#print axioms OneColourClosure.cover_seats_cases
#print axioms OneColourClosure.tabToFoundR_iff_canRaise
#print axioms OneColourClosure.canRaise_of_reversibleAtW
#print axioms OneColourClosure.not_canRaise_of_not_reversibleAtW
#print axioms OneColourClosure.canRaiseS_iff_cargoPath_reversibleAtW
