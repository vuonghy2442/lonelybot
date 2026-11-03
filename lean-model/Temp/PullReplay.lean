import Temp.BlockHousing
import Temp.RaisesOrFork

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Temp/PullReplay — the pull case by hoist-and-cancel, and the block-end licence

The hoist-and-cancel route is supplied by `Temp/BlockHousing.lean`:

* `insert_at_block_end` inserts `raise c` at a rank-block boundary;
* `cancel_prefix_is_play_from_source` drops the leading `raise c` of a play
  from the pull landing `u` and returns the tail as a play from the pull
  source `s` (the canonical `pull ; raise = id` raise lands at `s`; the
  given first letter's slide is replaced by the canonical empty-slide raise
  and the tail is moved by `RaiseSSeqLicensed.tail_transport`).

Consequently the whole pull case is reduced to **one** input:

```
CanRaiseS (state at the end of `c`'s rank block) c
```

This card proves that input from `CanRaiseS u c` in the non-twin case
(`c.twin ∉ ws`), proves the composition, and records the twin residual.

## What is proved

* `canRaiseS_persist_of_word_no_twin` — the licence `c` survives a whole
  licensed word that avoids `c`'s suit and `c.twin`.  Rank-`≠ c.rank`
  letters are inert (R1), rank-`= c.rank` letters other than `c`, `c.twin`
  are inert (`SatDifferConfig.licence_lost_only_by_twin`), and `c` itself is
  excluded by the suit hypothesis.  This is the existing
  `canRaiseS_of_word_notMem`.
* `block_end_licensed` — the block-boundary form requested: the state at
  the end of the low (rank-`≤ c.rank`) block still licenses `c`.
* `pull_case_of_end_live` — the composition, conditional only on
  `CanRaiseS v c` at the end of the play.
* `pull_case_sorted` — the unconditional (non-twin) pull case: the endpoint
  licence is `block_end_licensed`.

## The twin residual

`block_end_licensed` is **false** without `c.twin ∉ ws`: if `c` is buried
and `c.twin` tops a pile (the only disjunct that keeps a buried `c` alive),
raising `c.twin` in the low block kills `c`; `c` stays buried when its
cover is not itself a letter of the word.  The exact shape is

```
c buried under a cover y (y.rank = c.rank - 1), y ∉ ws,
c.twin ∈ ws,  ws-seat: below c ≠ [], run ≠ [],
CanRaiseS u c  (via  pileOfTop c.twin ≠ none)
⟹ ¬ CanRaiseS (block end) c
```

`block_end_dead_dichotomy` then returns `CoveredAt (block end) c` (the cover
`y`) or the commit lock.  The cover is not in `ws`, so closing this branch
requires inserting `raise y` too (an *extra* letter at `y`'s own rank
boundary), or taking the fork branch.  That is the precise residual.
-/

namespace OneColourClosure

/-! ## 1. The cheap append half -/

/-- **Append a raise of a still-live card.**  The word `c :: ws` plays `ws`
and then raises `c` (the head of the word is the last raise). -/
theorem append_raise_of_live {u v : State} {ws : List Card} {c : Card}
    (h : RaiseSSeqLicensed u ws v) (hc : CanRaiseS v c) :
    ∃ v', RaiseSSeqLicensed u (c :: ws) v' :=
  exists_append_raise h hc

/-! ## 2. The licence survives a twin-free, suit-silent word -/

/-- **Licence persistence across a twin-free word.**  If the word avoids
`c`'s suit and `c.twin`, then `c`'s S-licence is preserved.  (This is the
whole-word form of `block_end_licensed`; no rank-block bookkeeping is
needed because every letter is inert.)

The only letter that can destroy `c`'s licence at equal rank is `c` or
`c.twin` (`licence_lost_only_by_twin`); rank-different letters are inert
(R1, `canRaiseS_step_of_rank_ne`).  `c` is excluded by the suit
hypothesis, `c.twin` by hypothesis. -/
theorem canRaiseS_persist_of_word_no_twin {u z : State} {ws : List Card}
    {c : Card} (h : RaiseSSeqLicensed u ws z) (hu : u.WF) (hc : CanRaiseS u c)
    (hnosuit : ∀ d ∈ ws, d.suit ≠ c.suit) (htwin : c.twin ∉ ws) :
    CanRaiseS z c := by
  have hself : c ∉ ws := fun hmem => hnosuit c hmem rfl
  exact canRaiseS_of_word_notMem h hu hc hself htwin

/-! ## 3. The block-end licence -/

/-- A list with no element satisfying a Boolean predicate has count `0`. -/
theorem countP_eq_zero_of_forall_not {l : List Card} {p : Card → Bool}
    (h : ∀ d ∈ l, p d = false) : l.countP p = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.countP_cons, h a (List.mem_cons_self ..)]
      have ht : t.countP p = 0 :=
        ih (fun d hd => h d (List.mem_cons_of_mem a hd))
      rw [ht]
      simp

/-- **The state at the end of `c`'s rank block still licenses `c`.**  The
low block raises only cards of rank at most `c.rank`, and the word is
twin-free and suit-silent; persistence is therefore stronger than needed
and the rank hypothesis is not consulted.

`hhigh` is the play's high half, carried so that the statement matches the
`insert_at_block_end` boundary; it is not needed for the licence. -/
theorem block_end_licensed {u bnd z : State} {c : Card} {low high : List Card}
    (hu : u.WF)
    (hlow : RaiseSSeqLicensed u (playWord low) bnd)
    (_hhigh : RaiseSSeqLicensed bnd (playWord high) z)
    (hc : CanRaiseS u c)
    (_hlowRank : ∀ d ∈ low, d.rank.toIdx ≤ c.rank.toIdx)
    (hlowNoSuit : ∀ d ∈ low, d.suit ≠ c.suit)
    (hlowNoTwin : c.twin ∉ low) :
    CanRaiseS bnd c := by
  have hwordNoSuit : ∀ d ∈ playWord low, d.suit ≠ c.suit := by
    intro d hd
    exact hlowNoSuit d (by simpa [playWord] using hd)
  have hwordNoTwin : c.twin ∉ playWord low := by
    intro hd
    exact hlowNoTwin (by simpa [playWord] using hd)
  exact canRaiseS_persist_of_word_no_twin hlow hu hc hwordNoSuit hwordNoTwin

/-! ## 4. The twin/cover dichotomy (the residual, precisely)

Without `c.twin ∉ ws` the licence can be lost: the only disjunct keeping a
buried `c` alive is `pileOfTop c.twin ≠ none`, and raising `c.twin` removes
it.  The next two rows localise the failure: `c` stays face-up (so the first
two clauses of `not_canRaiseS_cases` are impossible), `nextUp` is unchanged,
and the failure is a cover or the commit lock. -/

/-- **Face-up membership survives a suit-silent licensed word.**  Cargo legs
are equal-rung orbit moves (`faceUp_iff`) and a raise of a card other than
`c` never removes `c` from a face-up run. -/
theorem faceUp_mem_of_raiseSSeqLicensed {u z : State} {ws : List Card} {c : Card}
    (h : RaiseSSeqLicensed u ws z) (hu : u.WF)
    (hnosuit : ∀ d ∈ ws, d.suit ≠ c.suit)
    (hface : ∃ a, c ∈ (u.piles a).faceUp) :
    ∃ a, c ∈ (z.piles a).faceUp := by
  revert hu hnosuit hface
  induction h with
  | nil =>
      intro _ _ hface
      exact hface
  | cons htail hS hp hstep ih =>
      rename_i zz zz0 zz' cc wws
      intro hu hnosuit hface
      have hzwf : zz.WF := htail.wf hu
      have hno_tail : ∀ d ∈ wws, d.suit ≠ c.suit :=
        fun d hd => hnosuit d (List.mem_cons_of_mem cc hd)
      have hface_zz : ∃ a, c ∈ (zz.piles a).faceUp := ih hu hno_tail hface
      have hface_zz0 : ∃ a, c ∈ (zz0.piles a).faceUp :=
        (faceUp_iff hzwf (sameOrbit_of_cargoPath hp) (rungAt_cargoPath hp) c).mp
          hface_zz
      have hcc : cc ≠ c := by
        intro hEq
        have h1 : cc.suit ≠ c.suit := hnosuit cc (List.mem_cons_self ..)
        exact h1 (by rw [hEq])
      obtain ⟨a, ha⟩ := hface_zz0
      exact ⟨a, mem_piles_tabToFound_of_mem_of_ne hstep
        (fun hcon => hcc hcon.symm) ha⟩

/-- **The dead `c` at the block end: a cover, or the commit lock.**  This is
the "only `c.twin` can kill `c`" dichotomy in the form the cover descent
consumes: `c` is still face-up and still next-up, so the first two clauses
of `not_canRaiseS_cases` are impossible; the remaining failure is either a
card covering `c` (`CoveredAt`), or the bottom-of-run commit lock.

In the cover case the cover is a card of rank `c.rank - 1`; the residual is
that it need not be a letter of `ws`, so it cannot be raised at its own
block boundary without enlarging the word. -/
theorem block_end_dead_dichotomy {u bnd : State} {c : Card} {low : List Card}
    (hu : u.WF) (hlow : RaiseSSeqLicensed u (playWord low) bnd)
    (hc : CanRaiseS u c) (hnosuit : ∀ d ∈ low, d.suit ≠ c.suit)
    (hdead : ¬ CanRaiseS bnd c) :
    CoveredAt bnd c ∨
      ∃ a, bnd.pileHolding c = some a ∧ below c (bnd.piles a).faceUp = [] ∧
        ((bnd.piles a).hidden ≠ [] ∨ c.rank ≠ Rank.king) := by
  have hno_word : ∀ d ∈ playWord low, d.suit ≠ c.suit := by
    intro d hd
    exact hnosuit d (by simpa [playWord] using hd)
  have hbnd : bnd.WF := hlow.wf hu
  have hface_u : ∃ a, c ∈ (u.piles a).faceUp := by
    obtain ⟨-, a, bs, run, hshape, -, -⟩ := (canRaiseS_iff hu).mp hc
    exact ⟨a, by rw [hshape]; exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))⟩
  have hface_b : ∃ a, c ∈ (bnd.piles a).faceUp :=
    faceUp_mem_of_raiseSSeqLicensed hlow hu hno_word hface_u
  obtain ⟨a0, hmem0⟩ := hface_b
  have hhold : bnd.pileHolding c = some a0 :=
    (pileHolding_eq_some_iff hbnd).2 hmem0
  have hnext_u : u.nextUp c = true := ((canRaiseS_split hu).mp hc).1
  have hrung : rungAt bnd c.suit = rungAt u c.suit :=
    RungMono.rungAt_eq_of_no_letter hlow hno_word
  have hnext_b : bnd.nextUp c = true := by
    unfold State.nextUp State.foundHeight at hnext_u ⊢
    rw [show (bnd.found c.suit).length = (u.found c.suit).length from hrung]
    exact hnext_u
  rcases not_canRaiseS_cases hbnd hdead with h1 | h1 | h1 | h1
  · rw [hnext_b] at h1
    exact absurd h1 (by simp)
  · rw [hhold] at h1
    exact absurd h1 (by simp)
  · obtain ⟨a, bs, run, hpa, hface, hrun, _htwin⟩ := h1
    rw [hhold] at hpa
    obtain rfl := Option.some.inj hpa
    exact Or.inl (covered_at_of_buried hbnd hhold hface hrun)
  · exact Or.inr h1

/-- **Dichotomy form of the block-end licence.**  At the block end, `c` is
either still S-live, or covered, or commit-locked. -/
theorem block_end_licensed_or_dichotomy {u bnd : State} {c : Card}
    {low : List Card}
    (hu : u.WF) (hlow : RaiseSSeqLicensed u (playWord low) bnd)
    (hc : CanRaiseS u c) (hnosuit : ∀ d ∈ low, d.suit ≠ c.suit) :
    CanRaiseS bnd c ∨ CoveredAt bnd c ∨
      ∃ a, bnd.pileHolding c = some a ∧ below c (bnd.piles a).faceUp = [] ∧
        ((bnd.piles a).hidden ≠ [] ∨ c.rank ≠ Rank.king) := by
  have hbnd : bnd.WF := hlow.wf hu
  by_cases hb : canRaiseSB bnd c = true
  · exact Or.inl ((canRaiseSB_iff hbnd).mp hb)
  · have hdead : ¬ CanRaiseS bnd c := fun hc' => hb ((canRaiseSB_iff hbnd).mpr hc')
    rcases block_end_dead_dichotomy hu hlow hc hnosuit hdead with hc' | hl
    · exact Or.inr (Or.inl hc')
    · exact Or.inr (Or.inr hl)

/-! ## 5. The composition: append `c`, hoist, cancel -/

/-- **The pull case, conditional only on the endpoint licence.**  If `c` is
still S-live at the end `v` of the play from `u`, then:

1. append `raise c` (`exists_append_raise`), giving the word `c :: ws`;
2. hoist `c` to the first chronological raise (`raiseS_rankfront_L`), giving
   the word `(sortByRank ws).reverse ++ [c] = playWord (c :: sortByRank ws)`;
3. cancel the leading `raise c` against the pull with
   `cancel_prefix_is_play_from_source`, leaving a play from `s` with the
   word `playWord (sortByRank ws)`;
4. the rung ledger: `sortByRank ws` is a permutation of `ws`, and `s` is one
   rung above `u` exactly on `c`'s suit, which `ws` never raises.

The endpoint is `v + e_c` on `c`'s suit and `v` elsewhere. -/
theorem pull_case_of_end_live {s u v : State} {c : Card} {b : Base}
    {ws : List Card}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hρ : RaiseSSeqLicensed u ws v) (hno : ∀ d ∈ ws, d.suit ≠ c.suit)
    (hcz : CanRaiseS v c) :
    ∃ v', RaiseSSeqLicensed s (playWord (sortByRank ws)) v' ∧
      (∀ σ, σ ≠ c.suit → rungAt v' σ = rungAt v σ) ∧
      rungAt v' c.suit = rungAt u c.suit + 1 := by
  have hu : u.WF := step_wf hs hpull
  have hcanU : CanRaiseS u c := SatDifferConfig.canRaiseS_after_pull hs hpull
  have hcan : CanRaise u c := SatDifferConfig.canRaise_after_pull hs hpull
  -- 1. append `raise c`
  obtain ⟨v₁, happ⟩ := append_raise_of_live hρ hcz
  -- 2. hoist `c` to the first chronological raise
  have hmem : c ∈ c :: ws := List.mem_cons_self ..
  obtain ⟨z, hz⟩ := raiseS_rankfront_L hu hcanU happ hmem
  have hword : rankFrontWord c (c :: ws) = playWord (c :: sortByRank ws) := by
    simp [rankFrontWord, playWord, List.erase_cons_head]
  have hz' : RaiseSSeqLicensed u (playWord (c :: sortByRank ws)) z := by
    rwa [hword] at hz
  -- 3. cancel the leading `raise c`
  obtain ⟨v', hv'⟩ := cancel_prefix_is_play_from_source hs hpull hcan hz'
  refine ⟨v', hv', ?_, ?_⟩
  · -- every suit other than `c`'s: `s` and `u` agree and the words are permutations
    intro σ hσ
    rw [hv'.rungAt_eq σ, hρ.rungAt_eq σ]
    have hperm : (playWord (sortByRank ws)).Perm ws := by
      rw [playWord]
      exact (reverse_perm (sortByRank ws)).trans (sortByRank_perm ws)
    rw [hperm.countP_eq (fun d => decide (d.suit = σ))]
    rw [rungAt_foundToTab hpull σ, ite_eq_right hσ]
  · -- `c`'s suit: `ws` has no letter of it, so only the pull's deficit remains
    rw [hv'.rungAt_eq c.suit]
    have hperm : (playWord (sortByRank ws)).Perm ws := by
      rw [playWord]
      exact (reverse_perm (sortByRank ws)).trans (sortByRank_perm ws)
    rw [hperm.countP_eq (fun d => decide (d.suit = c.suit))]
    have hzero : ws.countP (fun d => decide (d.suit = c.suit)) = 0 := by
      apply countP_eq_zero_of_forall_not
      intro d hd
      exact decide_eq_false (hno d hd)
    rw [hzero, Nat.add_zero]
    have hstepUS : State.step u (Move.tabToFound c) = some s :=
      step_tabToFound_of_foundToTab hs hpull
    rw [rungAt_tabToFound hstepUS c.suit, ite_eq_left rfl]

/-! ## 6. The unconditional non-twin pull case -/

/-- **THE PULL CASE (non-twin).**  If the licensed play from the pull landing
raises no card of `c`'s suit and does not raise `c.twin`, then a play from the
pull source `s` with the rank-sorted word `playWord (sortByRank ws)` exists,
and its endpoint is `v + e_c` on `c`'s suit and `v` elsewhere.

The endpoint licence is `block_end_licensed` (whole-word persistence). -/
theorem pull_case_sorted {s u v : State} {c : Card} {b : Base}
    {ws : List Card}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hρ : RaiseSSeqLicensed u ws v) (hno : ∀ d ∈ ws, d.suit ≠ c.suit)
    (htwin : c.twin ∉ ws) :
    ∃ v', RaiseSSeqLicensed s (playWord (sortByRank ws)) v' ∧
      (∀ σ, σ ≠ c.suit → rungAt v' σ = rungAt v σ) ∧
      rungAt v' c.suit = rungAt u c.suit + 1 := by
  have hu : u.WF := step_wf hs hpull
  have hcanU : CanRaiseS u c := SatDifferConfig.canRaiseS_after_pull hs hpull
  have hcz : CanRaiseS v c :=
    canRaiseS_persist_of_word_no_twin hρ hu hcanU hno htwin
  exact pull_case_of_end_live hs hpull hρ hno hcz

/-- **Rung domination form.**  If `t`'s rungs are dominated by `v`'s, then the
play from `s` produced by `pull_case_sorted` dominates both `s` and `t`:
its endpoint is `v + e_c`, so it dominates `v` rungwise. -/
theorem pull_case_sorted_rungLe {s u v t : State} {c : Card} {b : Base}
    {ws : List Card}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hρ : RaiseSSeqLicensed u ws v) (hno : ∀ d ∈ ws, d.suit ≠ c.suit)
    (htwin : c.twin ∉ ws) (ht : RungLe t v) :
    ∃ v', RaiseSSeqLicensed s (playWord (sortByRank ws)) v' ∧
      RungLe s v' ∧ RungLe t v' := by
  obtain ⟨v', hplay, hrung_ne, hrung_c⟩ :=
    pull_case_sorted hs hpull hρ hno htwin
  have hv_c : rungAt v c.suit = rungAt u c.suit := by
    rw [hρ.rungAt_eq c.suit]
    have hzero : ws.countP (fun d => decide (d.suit = c.suit)) = 0 := by
      apply countP_eq_zero_of_forall_not
      intro d hd
      exact decide_eq_false (hno d hd)
    rw [hzero, Nat.add_zero]
  refine ⟨v', hplay, fun σ => RungMono.rungAt_le hplay σ, fun σ => ?_⟩
  by_cases hσ : σ = c.suit
  · rw [hσ, hrung_c, ← hv_c]
    exact Nat.le_trans (ht c.suit) (Nat.le_succ _)
  · rw [hrung_ne σ hσ]
    exact ht σ

end OneColourClosure

#print axioms OneColourClosure.append_raise_of_live
#print axioms OneColourClosure.canRaiseS_persist_of_word_no_twin
#print axioms OneColourClosure.countP_eq_zero_of_forall_not
#print axioms OneColourClosure.block_end_licensed
#print axioms OneColourClosure.faceUp_mem_of_raiseSSeqLicensed
#print axioms OneColourClosure.block_end_dead_dichotomy
#print axioms OneColourClosure.block_end_licensed_or_dichotomy
#print axioms OneColourClosure.pull_case_of_end_live
#print axioms OneColourClosure.pull_case_sorted
#print axioms OneColourClosure.pull_case_sorted_rungLe
