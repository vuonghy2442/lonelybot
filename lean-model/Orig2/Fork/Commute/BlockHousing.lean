import Orig2.Fork.Commute.PullRaiseId
import Orig2.Fork.Commute.RungMono
import Orig2.Fork.Commute.RaisesOrFork

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Temp/BlockHousing — inserting `raise c` at a rank-block boundary

`RaiseSSeqLicensed` words are **reverse chronological** (`ForkRaiseReorder.lean`:
the head of the word is the last raise), so a chronological list `P` is carried by
the word `playWord P = P.reverse`.

The target of this file is the block-boundary insertion

```
low ; c ; high
```

where `low`, `c`, `high` are chronologically ordered and every card of `low` is
rung-weakly-below `c` while every card of `high` is strictly above `c`.  The
card `c` is only assumed raisable at the *boundary state* (the endpoint of
`low`), not at the source.

## What is proved

* `suffix_transport` — HALF 1, in the literal word form asked for: a licensed
  play of a word of strictly higher-rank letters leaves `c` licensed at its
  endpoint, so `c` can be appended as the next (last) letter.  This is
  `RaiseSSeqLicensed.canRaiseS_persist_of_rank_ne` (R1) plus
  `exists_append_raise`.

* `suffix_insert` — the chronological half that the main proof consumes: if
  `H` is ascending, strictly above `c`, and playable from `u` while `c` is
  licensed at `u`, then `c ; H` is playable from `u`.  Route: replay `H` and
  append `c` at the end (`exists_append_raise`), then **sort** the resulting
  play (`sortable`) and move between the two ascending orders of the same
  multiset (`tieFree`).  Because `c` is strictly below every letter of `H`, the
  ascending order is exactly `c :: H`.

* `insert_at_block_end_split` — the main theorem with the boundary state `u`
  (and the two half-plays) supplied explicitly by the caller.

* `insert_at_block_end` — the same theorem taking only the full play
  `low ++ high`; the boundary state is recovered with `split_chron`, and the
  caller supplies the licence at every candidate boundary state.

* `cancel_prefix_is_play_from_source` — the composition lemma: if `pull c`
  takes `s` to `u` and `raise c` returns `u` to `s`, a play from `u` that starts
  chronologically with `raise c` has its tail playable from `s`.  The first
  letter's landing is not canonical (the `RaiseSSeqLicensed` step hides its
  cargo path), so the proof replaces it by the canonical empty-slide raise and
  transports the tail with `RaiseSSeqLicensed.tail_transport`.

House rules: constructive only, no `sorry`, no `Classical`, no
`noncomputable`, no new `Prop` predicate.
-/

namespace OneColourClosure

/-! ## §1. Half 1 — a strictly higher-rank word is licence-inert for `c` -/

/-- **Suffix transport (word form).**  If a licensed word `high` raises only
cards of strictly higher rank than `c`, then `c` is still `S`-licensed at the
endpoint, and the word `c :: high` (i.e. play `high`, then raise `c`) is
licensed. -/
theorem suffix_transport {u z : State} {c : Card} {high : List Card}
    (hu : u.WF)
    (hplay : RaiseSSeqLicensed u high z)
    (hc : CanRaiseS u c)
    (hr : ∀ d ∈ high, c.rank.toIdx < d.rank.toIdx) :
    ∃ z', RaiseSSeqLicensed u (c :: high) z' := by
  have hcz : CanRaiseS z c :=
    RaiseSSeqLicensed.canRaiseS_persist_of_rank_ne hplay hu
      (fun d hd => by
        have hlt : c.rank.toIdx < d.rank.toIdx := hr d hd
        intro hEq
        rw [hEq] at hlt
        exact Nat.lt_irrefl _ hlt) hc
  exact exists_append_raise hplay hcz

/-! ## §2. The chronological suffix insertion -/

/-- **Chronological suffix insertion.**  If `H` is an ascending chronological
list all of whose cards are strictly above `c`, and `H` is licensed from `u`
with `c` licensed at `u`, then `c ; H` is licensed from `u` (same source).

The proof does not transport the tail across the extra raise (which would need
a state transport); it reorders the *whole* play instead:

1. play `H`, then append `c` (legal by §1);
2. `sortable` sorts that play ascending;
3. `tieFree` replaces the sorted list by the ascending list `c :: H`.
-/
theorem suffix_insert {u z : State} {c : Card} {H : List Card}
    (hu : u.WF)
    (hH : H.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx))
    (hplay : RaiseSSeqLicensed u (playWord H) z)
    (hc : CanRaiseS u c)
    (hr : ∀ d ∈ H, c.rank.toIdx < d.rank.toIdx) :
    ∃ z', RaiseSSeqLicensed u (playWord (c :: H)) z' := by
  have hcz : CanRaiseS z c :=
    RaiseSSeqLicensed.canRaiseS_persist_of_rank_ne hplay hu
      (fun d hd => by
        have hd' : d ∈ H := by simpa [playWord] using hd
        have hlt : c.rank.toIdx < d.rank.toIdx := hr d hd'
        intro hEq
        rw [hEq] at hlt
        exact Nat.lt_irrefl _ hlt) hc
  obtain ⟨v, hv⟩ := exists_append_raise hplay hcz
  have hplay' : RaiseSSeqLicensed u (playWord (H ++ [c])) v := by
    rw [playWord_snoc]
    exact hv
  obtain ⟨z₁, hz₁⟩ := sortable hu hplay'
  have hB : (c :: H).Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) :=
    List.pairwise_cons.mpr ⟨fun d hd => Nat.le_of_lt (hr d hd), hH⟩
  have hperm : (sortByRank (H ++ [c])).Perm (c :: H) :=
    (sortByRank_perm (H ++ [c])).trans (List.perm_append_singleton c H)
  exact tieFree hu (sortByRank_asc (H ++ [c])) hB hperm hz₁

/-! ## §3. The block-boundary insertion -/

/-- **Insertion at the upper boundary of `c`'s rank block** (split form).  The
boundary state `u` and the two half-plays are supplied explicitly; `low` is
chronologically first, `high` follows.  Every card of `low` is weakly below `c`,
every card of `high` is strictly above `c`, and `c` is licensed at `u`. -/
theorem insert_at_block_end_split {s u z : State} {c : Card} {low high : List Card}
    (hs : s.WF)
    (hlowPlay : RaiseSSeqLicensed s (playWord low) u)
    (hplay : RaiseSSeqLicensed u (playWord high) z)
    (hlow : ∀ d ∈ low, d.rank.toIdx ≤ c.rank.toIdx)
    (hhigh : ∀ d ∈ high, c.rank.toIdx < d.rank.toIdx)
    (hhighAsc : high.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx))
    (hc : CanRaiseS u c) :
    ∃ z', RaiseSSeqLicensed s (playWord (low ++ [c] ++ high)) z' := by
  have huwf : u.WF := RaiseSSeqLicensed.wf hlowPlay hs
  obtain ⟨z₁, hz₁⟩ := suffix_insert huwf hhighAsc hplay hc hhigh
  refine ⟨z₁, ?_⟩
  have hfin : RaiseSSeqLicensed s (playWord (c :: high) ++ playWord low) z₁ :=
    RaiseSSeqLicensed.append hlowPlay hz₁
  have heq : playWord (c :: high) ++ playWord low =
      playWord (low ++ [c] ++ high) := by
    simp [playWord, List.append_assoc]
  rwa [heq] at hfin

/-- **Insertion at the upper boundary of `c`'s rank block**, from the full
play alone.  The boundary state is the endpoint of the `low` prefix
(`split_chron`); the caller supplies the licence at the genuine boundary, i.e.
at every state that is both the endpoint of `low` and the start of `high`. -/
theorem insert_at_block_end {s z : State} {c : Card} {low high : List Card}
    (hs : s.WF)
    (hplay : RaiseSSeqLicensed s (playWord (low ++ high)) z)
    (hlow : ∀ d ∈ low, d.rank.toIdx ≤ c.rank.toIdx)
    (hhigh : ∀ d ∈ high, c.rank.toIdx < d.rank.toIdx)
    (hhighAsc : high.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx))
    (hc : ∀ u, RaiseSSeqLicensed s (playWord low) u →
      RaiseSSeqLicensed u (playWord high) z → CanRaiseS u c) :
    ∃ z', RaiseSSeqLicensed s (playWord (low ++ [c] ++ high)) z' := by
  obtain ⟨u, hlowPlay, hhighPlay⟩ :=
    RaiseSSeqLicensed.split_chron (A := low) (R := high) hplay
  exact insert_at_block_end_split hs hlowPlay hhighPlay hlow hhigh hhighAsc
    (hc u hlowPlay hhighPlay)

/-- The tail of a rank-ascending list is rank-ascending. -/
theorem pairwise_append_right {l m : List Card}
    (h : (l ++ m).Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx)) :
    m.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) := by
  induction l with
  | nil => simpa using h
  | cons a l ih =>
      rw [List.cons_append] at h
      exact ih (List.pairwise_cons.mp h).2

/-- **Insertion at the upper boundary**, taking the rank-sortedness of the whole
chronological word `low ++ high` (the prose hypothesis) rather than the
ascendingness of `high` alone. -/
theorem insert_at_block_end_sorted {s z : State} {c : Card} {low high : List Card}
    (hs : s.WF)
    (hplay : RaiseSSeqLicensed s (playWord (low ++ high)) z)
    (hlow : ∀ d ∈ low, d.rank.toIdx ≤ c.rank.toIdx)
    (hhigh : ∀ d ∈ high, c.rank.toIdx < d.rank.toIdx)
    (hsorted : (low ++ high).Pairwise
      (fun a b => a.rank.toIdx ≤ b.rank.toIdx))
    (hc : ∀ u, RaiseSSeqLicensed s (playWord low) u →
      RaiseSSeqLicensed u (playWord high) z → CanRaiseS u c) :
    ∃ z', RaiseSSeqLicensed s (playWord (low ++ [c] ++ high)) z' :=
  insert_at_block_end hs hplay hlow hhigh (pairwise_append_right hsorted) hc

/-! ## §4. The composition lemma: the tail after `raise c` starts at `s` -/

/-- **Cancelled pull prefix.**  If `pull c` takes `s` to `u` and a licensed
play from `u` starts chronologically with `raise c`, then its tail (everything
after `raise c`) is a licensed play from `s`.

The first letter of the play is not canonical — its `CargoPath` may be
nonempty, so its landing `s'` need not be `s` syntactically.  The proof inserts
the *canonical* first letter (empty slide, then `step_tabToFound_of_foundToTab`,
which lands at `s`), and uses `tail_transport` to move the tail from `s'` to
`s`.  Both first-letter plays carry the same one-card word `playWord [c]`. -/
theorem cancel_prefix_is_play_from_source {s u : State} {c : Card} {b : Base}
    {ws : List Card} {v : State} (hs : s.WF)
    (hpull : State.step s (Move.foundToTab c b) = some u)
    (hcan : CanRaise u c)
    (hplay : RaiseSSeqLicensed u (playWord (c :: ws)) v) :
    ∃ v', RaiseSSeqLicensed s (playWord ws) v' := by
  have huwf : u.WF := step_wf hs hpull
  obtain ⟨s', hfirst, htail⟩ :=
    RaiseSSeqLicensed.split_chron (A := [c]) (R := ws) hplay
  -- the canonical raise of `c` at `u` lands at `s`
  have hstep : State.step u (Move.tabToFound c) = some s :=
    step_tabToFound_of_foundToTab hs hpull
  have hcanon : RaiseSSeqLicensed u (playWord [c]) s :=
    RaiseSSeqLicensed.cons (RaiseSSeqLicensed.nil u)
      (CanRaiseS.now c hcan) (Steps.refl u) hstep
  exact RaiseSSeqLicensed.tail_transport huwf hfirst hcanon
    (List.Perm.refl [c]) (by simpa [playWord] using htail)

end OneColourClosure

#print axioms OneColourClosure.suffix_transport
#print axioms OneColourClosure.suffix_insert
#print axioms OneColourClosure.insert_at_block_end_split
#print axioms OneColourClosure.insert_at_block_end
#print axioms OneColourClosure.pairwise_append_right
#print axioms OneColourClosure.insert_at_block_end_sorted
#print axioms OneColourClosure.cancel_prefix_is_play_from_source
