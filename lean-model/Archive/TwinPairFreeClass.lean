import Orig2.TwinPreludeFunctor
import Orig2.TwinAbstractLadder

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2.TwinPairFreeClass — the pair-free orbit class of a card

The last row needed by `FirstRaiseNormalization` is the endpoint
classification of an arbitrary witness shuffle at a state where both
twins are `.inr`-seated.

`PairFreeOrbit x u v` is the forward pair-free reachability relation:
a witness shuffle `u → v` none of whose letters raises or pulls either
twin.  The object of the card is

```
pairFree_endpoint_classification :
  u.WF → x@z → x.twin@z.twin → ShufflePlayW u play v →
  v both seated →
  PairFreeOrbit x v u ∨ PairFreeOrbit x v (u.spliceTwinRuns x).
```

The file proves the following unconditional rows:

* the relation is reflexive and transitive;
* a pair-free play is a `PairFreeOrbit` row in its own direction;
* **the canonical self-swap block already satisfies the target**: the
  ladder `[raise x, slide x.twin onto z, pull x onto z.twin]` ends
  exactly at `u.spliceTwinRuns x`, so the second disjunct holds by the
  empty play.  This is the `SelfSwapSeg` recognition of
  `TwinAbstractLadder`;
* a `SelfSwapSeg` play satisfies the target for the same reason;
* every list of moves either is pair-free, or has a split at its
  **last** pair-foundation letter whose suffix is pair-free.

The exact remaining content is isolated in two `Prop`s
(`PairFreeReversal`, `PairFoundSuffixCancellation`).  The card proves
that their conjunction suffices for the requested theorem; the last
section records the precise gap.  No counterexample to the target
was found: the obstruction is not a wrong seat configuration (the
endpoint seats are pinned by `endpoint_config_identity_or_swap`) but
the reversal of a pair-free play across a state where one twin is off
the tableau.

Zero `sorry`, zero `Classical.choice`, no new axioms.
-/

open State

/-! ## §1. The pair-free orbit relation -/

/-- **`PairFreeOrbit x u v`** — `v` is reachable from `u` by a witness
shuffle that never raises or pulls either twin. -/
def PairFreeOrbit (x : Card) (u v : State) : Prop :=
  ∃ play : List Move, ShufflePlayW u play v ∧ ∀ m ∈ play, NotFoundPair x m

/-- The empty play is pair-free. -/
theorem pairFreeOrbit_refl (x : Card) (u : State) :
    PairFreeOrbit x u u :=
  ⟨[], Walk.nil u, by simp⟩

/-- Pair-free orbits compose by concatenating the plays. -/
theorem PairFreeOrbit.trans {x : Card} {u v w : State}
    (h₁ : PairFreeOrbit x u v) (h₂ : PairFreeOrbit x v w) :
    PairFreeOrbit x u w := by
  obtain ⟨p, hp, hnp⟩ := h₁
  obtain ⟨q, hq, hnq⟩ := h₂
  exact ⟨p ++ q, ShufflePlayW_append hp hq, by
    intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hnp m hm
    · exact hnq m hm⟩

/-- A concrete pair-free shuffle is a `PairFreeOrbit` row. -/
theorem pairFreeOrbit_of_play {x : Card} {u v : State} {play : List Move}
    (hplay : ShufflePlayW u play v)
    (hno : ∀ m ∈ play, NotFoundPair x m) :
    PairFreeOrbit x u v :=
  ⟨play, hplay, hno⟩

/-- A pair-free play in the orientation of the target's conclusion. -/
theorem pairFreeOrbit_of_play_rev {x : Card} {u v : State} {play : List Move}
    (hplay : ShufflePlayW v play u)
    (hno : ∀ m ∈ play, NotFoundPair x m) :
    PairFreeOrbit x v u :=
  pairFreeOrbit_of_play hplay hno

/-! ## §2. Splitting at the last pair-foundation letter -/

/-- **Last pair-foundation split.**  A play either avoids the four
pair-foundation letters entirely, or splits as

```
pre ++ m :: suf
```

where `m` is a pair-foundation letter and the whole suffix `suf` is
pair-free.  This is the mirror of
`Orig2.DetourKit.exists_pairFound_split` at the last occurrence. -/
theorem exists_pairFound_last_split (x : Card) (play : List Move) :
    (∀ m ∈ play, NotFoundPair x m) ∨
    ∃ pre m suf, play = pre ++ m :: suf ∧ IsPairFound x m ∧
      (∀ n ∈ suf, NotFoundPair x n) := by
  rcases exists_pairFound_split x play.reverse with hno | ⟨pre, m, suf, hsplit, hm, hpre⟩
  · left
    intro n hn
    exact (notFoundPair_iff_not_isPairFound x n).mpr
      (hno n (by simpa using hn))
  · right
    refine ⟨suf.reverse, m, pre.reverse, ?_, hm, ?_⟩
    · have hplay : play = (pre ++ m :: suf).reverse := by
        rw [← hsplit, List.reverse_reverse]
      rw [hplay, List.reverse_append, List.reverse_cons]
      simp only [List.append_assoc, List.singleton_append]
    · intro n hn
      have hnpre : n ∈ pre := by simpa using hn
      exact (notFoundPair_iff_not_isPairFound x n).mpr (hpre n hnpre)

/-! ## §3. The self-swap and ladder subcases -/

/-- **Any recognized self-swap segment satisfies the target.**  A
`SelfSwapSeg` records the endpoint equality `v = u.spliceTwinRuns x`,
so the second disjunct is the empty play at the splice. -/
theorem pairFree_endpoint_classification_of_selfSwap
    {u v : State} {x : Card} {play : List Move}
    (hseg : SelfSwapSeg x u v play) :
    PairFreeOrbit x v u ∨ PairFreeOrbit x v (u.spliceTwinRuns x) := by
  right
  obtain ⟨-, -, -, -, hveq⟩ := hseg
  rw [hveq]
  exact pairFreeOrbit_refl x (u.spliceTwinRuns x)

/-- The run-splice is insensitive to which member of the pair names it. -/
theorem spliceTwinRuns_twin (s : State) (x : Card) :
    s.spliceTwinRuns x.twin = s.spliceTwinRuns x := by
  simp only [State.spliceTwinRuns, card_twin_twin]
  cases hx : s.pileHolding x with
  | none =>
      cases ht : s.pileHolding x.twin with
      | none => simp
      | some b => simp
  | some a =>
      cases ht : s.pileHolding x.twin with
      | none => simp
      | some b =>
          by_cases hab : a = b
          · subst hab
            simp
          · simp only [hx, ht, hab, Ne.symm hab]
            apply State.ext
            · rfl
            · funext a'
              by_cases hb : a' = b
              · simp [hb, hab, Ne.symm hab]
              · by_cases ha : a' = a
                · simp [hb, ha, hab, Ne.symm hab]
                · simp [hb, ha]
            · rfl
            · rfl
            · rfl

/-- **The canonical three-leg self-swap ladder satisfies the target.**
`ladderPlay x z []` is

```
[raise x, slide x.twin onto z, pull x onto z.twin]
```

and `TwinAbstractLadder.selfSwapSeg_abstractLadder` identifies its
endpoint with `u.spliceTwinRuns x`. -/
theorem pairFree_endpoint_classification_of_ladder
    {u v : State} {x z : Card}
    (hwf : u.WF)
    (hx : seatOf u x = some (Sum.inr z))
    (hxt : seatOf u x.twin = some (Sum.inr z.twin))
    (hplay : ShufflePlayW u (ladderPlay x z []) v)
    (_hvx : ∃ w, seatOf v x = some (Sum.inr w))
    (_hvt : ∃ w', seatOf v x.twin = some (Sum.inr w')) :
    PairFreeOrbit x v u ∨ PairFreeOrbit x v (u.spliceTwinRuns x) := by
  have hwf' : v.WF := run_wf hwf (Walk_run _ hplay)
  exact pairFree_endpoint_classification_of_selfSwap
    (selfSwapSeg_abstractLadder (ys := []) hwf hwf' hx hxt trivial hplay)

/-- **The mirror three-leg ladder satisfies the target.**  Naming the
pair by `x.twin` swaps the two run-splice spellings, so the second
disjunct is again `u.spliceTwinRuns x`. -/
theorem pairFree_endpoint_classification_of_ladder_twin
    {u v : State} {x z : Card}
    (hwf : u.WF)
    (hx : seatOf u x = some (Sum.inr z))
    (hxt : seatOf u x.twin = some (Sum.inr z.twin))
    (hplay : ShufflePlayW u (ladderPlay x.twin z.twin []) v)
    (_hvx : ∃ w, seatOf v x = some (Sum.inr w))
    (_hvt : ∃ w', seatOf v x.twin = some (Sum.inr w')) :
    PairFreeOrbit x v u ∨ PairFreeOrbit x v (u.spliceTwinRuns x) := by
  have hwf' : v.WF := run_wf hwf (Walk_run _ hplay)
  have hxt' : seatOf u x.twin.twin = some (Sum.inr z.twin.twin) := by
    simpa [card_twin_twin] using hx
  have hseg : SelfSwapSeg x.twin u v (ladderPlay x.twin z.twin []) :=
    selfSwapSeg_abstractLadder (ys := []) hwf hwf' hxt hxt' trivial hplay
  have hveq : v = u.spliceTwinRuns x.twin := by
    obtain ⟨-, -, -, -, hveq⟩ := hseg
    exact hveq
  right
  rw [hveq, spliceTwinRuns_twin]
  exact pairFreeOrbit_refl x (u.spliceTwinRuns x)

/-- A pair-free witness shuffle out of a both-seated source keeps both
twins `.inr`-seated at its landing.  Private copy of the exact-recipe
card's iteration of `seat_inr_of_pairFree_step`. -/
private theorem pairFree_play_inr_seats {x : Card} (seg : List Move) :
    ∀ {s t : State}, s.WF → ShufflePlayW s seg t →
      (∀ m ∈ seg, NotFoundPair x m) →
      (∃ z, seatOf s x = some (Sum.inr z)) →
      (∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin)) →
      (∃ z, seatOf t x = some (Sum.inr z)) ∧
        (∃ z : Card, seatOf t x.twin = some (Sum.inr z.twin)) := by
  induction seg with
  | nil =>
      intro s t _ hplay _ hx hxt
      cases hplay
      exact ⟨hx, hxt⟩
  | cons m rest ih =>
      intro s t hwf hplay hno hx hxt
      cases hplay with
      | @cons _ s1 _ _ _ hrev hstep hrest =>
          have hm : NotFoundPair x m := hno m (by simp)
          obtain ⟨hx₁, hxt₁⟩ :=
            seat_inr_of_pairFree_step hwf hstep hrev hm hx hxt
          have hwf₁ : s1.WF := step_wf hwf hstep
          exact ih hwf₁ hrest
            (fun n hn => hno n (List.mem_cons_of_mem m hn)) hx₁ hxt₁

/-! ## §4. The two residuals -/

/-- **The pair-free reversal gap.**  Every pair-free witness shuffle
out of a both-seated `WF` state is itself pair-free-reversible.  This
is the exact missing direction for the pair-free arm of the target. -/
def PairFreeReversal (x : Card) : Prop :=
  ∀ {u v : State} {z : Card} {play : List Move},
    u.WF →
    seatOf u x = some (Sum.inr z) →
    seatOf u x.twin = some (Sum.inr z.twin) →
    ShufflePlayW u play v →
    (∀ m ∈ play, NotFoundPair x m) →
    PairFreeOrbit x v u

/-- **The last-letter cancellation gap.**  A play split at its last
pair-foundation letter, with a pair-free suffix, already satisfies the
endpoint classification.  The prefix is completely arbitrary. -/
def PairFoundSuffixCancellation (x : Card) : Prop :=
  ∀ {u v : State} {z : Card} {pre : List Move} {m : Move} {suf : List Move},
    u.WF →
    seatOf u x = some (Sum.inr z) →
    seatOf u x.twin = some (Sum.inr z.twin) →
    ShufflePlayW u (pre ++ m :: suf) v →
    IsPairFound x m →
    (∀ n ∈ suf, NotFoundPair x n) →
    (∃ w, seatOf v x = some (Sum.inr w)) →
    (∃ w', seatOf v x.twin = some (Sum.inr w')) →
    PairFreeOrbit x v u ∨ PairFreeOrbit x v (u.spliceTwinRuns x)

/-- The requested endpoint classification, packaged as one `Prop`. -/
def PairFreeEndpointClassification (x : Card) : Prop :=
  ∀ {u v : State} {z : Card} {play : List Move},
    u.WF →
    seatOf u x = some (Sum.inr z) →
    seatOf u x.twin = some (Sum.inr z.twin) →
    ShufflePlayW u play v →
    (∃ w, seatOf v x = some (Sum.inr w)) →
    (∃ w', seatOf v x.twin = some (Sum.inr w')) →
    PairFreeOrbit x v u ∨ PairFreeOrbit x v (u.spliceTwinRuns x)

/-- **The target follows from the two residuals.**  The last-letter
split either yields a pair-free play (first residual) or the last
pair-foundation letter (second residual). -/
theorem pairFreeEndpointClassification_of_residuals {x : Card}
    (hrev : PairFreeReversal x) (hsuf : PairFoundSuffixCancellation x) :
    PairFreeEndpointClassification x := by
  intro u v z play hwf hx hxt hplay hvx hvt
  rcases exists_pairFound_last_split x play with hno | ⟨pre, m, suf, hsplit, hm, hnoSuf⟩
  · exact Or.inl (hrev hwf hx hxt hplay hno)
  · subst hsplit
    exact hsuf hwf hx hxt hplay hm hnoSuf hvx hvt

/-- **The requested endpoint classification, conditional on the two
residuals.**  This is the exact statement shape of
`pairFree_endpoint_classification`; the two hypotheses are the precise
remaining Lean obligations isolated above. -/
theorem pairFree_endpoint_classification_of_residuals
    {x : Card} (hrev : PairFreeReversal x) (hsuf : PairFoundSuffixCancellation x)
    {u v : State} {z : Card} {play : List Move}
    (hwf : u.WF)
    (hx : seatOf u x = some (Sum.inr z))
    (hxt : seatOf u x.twin = some (Sum.inr z.twin))
    (hplay : ShufflePlayW u play v)
    (hvx : ∃ w, seatOf v x = some (Sum.inr w))
    (hvt : ∃ w', seatOf v x.twin = some (Sum.inr w')) :
    PairFreeOrbit x v u ∨ PairFreeOrbit x v (u.spliceTwinRuns x) :=
  pairFreeEndpointClassification_of_residuals hrev hsuf hwf hx hxt hplay hvx hvt

/-- A pair-free play out of a both-seated source keeps both twins
`.inr`-seated at its landing (the public form of the private iteration
used above). -/
theorem pairFree_play_seats_inr {x : Card} {s t : State} {play : List Move}
    (hwf : s.WF) (hplay : ShufflePlayW s play t)
    (hno : ∀ m ∈ play, NotFoundPair x m)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin)) :
    (∃ z, seatOf t x = some (Sum.inr z)) ∧
      (∃ z : Card, seatOf t x.twin = some (Sum.inr z.twin)) :=
  pairFree_play_inr_seats play hwf hplay hno hx hxt

/-! ## §5. Audit -/

#print axioms exists_pairFound_last_split
#print axioms pairFreeOrbit_refl
#print axioms PairFreeOrbit.trans
#print axioms pairFreeOrbit_of_play
#print axioms pairFreeOrbit_of_play_rev
#print axioms pairFree_endpoint_classification_of_selfSwap
#print axioms spliceTwinRuns_twin
#print axioms pairFree_endpoint_classification_of_ladder
#print axioms pairFree_endpoint_classification_of_ladder_twin
#print axioms pairFree_play_seats_inr
#print axioms pairFree_endpoint_classification_of_residuals
#print axioms pairFreeEndpointClassification_of_residuals

/-! ## §6. Report: the precise remaining gap

### Proven

* `PairFreeOrbit` is reflexive and transitive.
* A pair-free shuffle is a `PairFreeOrbit` row in its own direction.
* The canonical three-leg self-swap ladder (both orientations) ends at
  the run splice, hence satisfies the target.
* Any `SelfSwapSeg` recognized block satisfies the target.
* Every play has a split at its last pair-foundation letter with a
  pair-free suffix (`exists_pairFound_last_split`).
* The target’s exact conclusion follows from the two residuals below
  (`pairFree_endpoint_classification_of_residuals`).

### The two open Lean obligations

```
def PairFreeReversal (x : Card) : Prop :=
  ∀ {u v : State} {z : Card} {play : List Move},
    u.WF → seatOf u x = some (Sum.inr z) →
    seatOf u x.twin = some (Sum.inr z.twin) →
    ShufflePlayW u play v → (∀ m ∈ play, NotFoundPair x m) →
    PairFreeOrbit x v u

def PairFoundSuffixCancellation (x : Card) : Prop :=
  ∀ {u v : State} {z : Card} {pre : List Move} {m : Move} {suf : List Move},
    u.WF → seatOf u x = some (Sum.inr z) →
    seatOf u x.twin = some (Sum.inr z.twin) →
    ShufflePlayW u (pre ++ m :: suf) v → IsPairFound x m →
    (∀ n ∈ suf, NotFoundPair x n) →
    (∃ w, seatOf v x = some (Sum.inr w)) →
    (∃ w', seatOf v x.twin = some (Sum.inr w')) →
    PairFreeOrbit x v u ∨ PairFreeOrbit x v (u.spliceTwinRuns x)
```

`PairFreeReversal` is the missing direction of the pair-free segment.
For a single pair-free letter at a both-seated state every move shape
has the expected pair-free inverse (`tabToTab` slides back onto the
exposed seat, a raise/pull of a third card mirrors to a pull/raise of
the same card, a draw is the phase rotation), but the library’s
`reversibleAtW` carrier stores only an arbitrary witness play, not the
canonical pair-free one, so the row has not been assembled here.

`PairFoundSuffixCancellation` is the geometric last-letter row.  Its
last letter `m` is a pull (a raise would leave one twin off the
tableau, and the pair-free suffix preserves that), and the endpoint
seat pair is pinned by `endpoint_config_identity_or_swap`; the content
is to commute the prefix past the pair-foundation excursion.  The
canonical instance `pre = [raise x, slide x.twin onto z]`,
`m = pull x onto z.twin` is discharged unconditionally above as the
ladder subcase.  Arbitrary interleavings of the two twins’ raises,
pulls, and third-card slides are the remaining work.

No counterexample was found: the only possible endpoint parents are
`z` and `z.twin`, so the conclusion’s two target states are the only
candidates, and each is realized by an actual `SelfSwapSeg` or by the
identity excursion.  The difficulty is proof-theoretic (the direction
of the pair-free witness), not a mismatch of endpoint data.
-/
