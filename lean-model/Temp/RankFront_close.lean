import Temp.RankFront_licensed

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# RankFront_close — the same-multiset licence theorem (S)

This file closes the residual `SortedPrefixLicence` of
`Temp/RankFront_licensed.lean` *at its licence-transfer heart*: the statement
**(S)**

```lean
theorem canRaiseS_of_raise_perm {s u v : State} {P Q : List Card} {d : Card}
    (hs : s.WF) (hP : RaiseSSeqL s P u) (hQ : RaiseSSeqL s Q v) (hperm : P.Perm Q) :
    CanRaiseS u d ↔ CanRaiseS v d
```

is **true and proved** below.  Two licensed plays from the same state that
raise the same *multiset* of cards end in states with the same licences.

## The route (why (S) is true)

The earlier analysis tried to identify *cargo* classes.  That is the wrong
quotient: two licensed plays may end in genuinely different cargo classes even
with the same word (a raise is not a cargo move).  The right quotient is the
**orbit**:

* a licensed raise is *reversible* — `CanRaise z c` is literally the shape
  `tabToFoundR z c = true`, and at `WF` that is `reversibleAtW z (tabToFound c)`
  (`tabToFoundR_iff_reversibleAtW`); a cargo leg is reversible by definition;
* hence **every** licensed play is a witness shuffle `ShufflePlayW`, so its
  endpoint is `RevEqW`-related to its start (`RaiseSSeqL.revEqW`), and `RevEqW`
  is an equivalence — any two licensed endpoints from the same start are
  orbit-mates, *whatever their words*;
* a raise of `c` moves exactly the rung of `c`'s suit by one
  (`rungAt_tabToFound`), a cargo leg moves no rung (`cargoPath_rungAt`), so
  same-multiset plays end at **equal rungs** (`rungAt_eq_of_perm`);
* and at equal rungs the S-licence is an orbit invariant —
  `canRaiseS_orbit_rung` (`Orig2/Fiber/FreeOrbit.lean:1431`).

That is the whole proof.  Notice the load-bearing rôle of *licence*: with the
weak `RaiseSSeq` step the raise need not be reversible (`t4a_fires` +
`t4a_not_canRaise`), the endpoints need not be orbit-mates, and (S) is expected
to fail; the theorem is a statement about the licensed grade.

House rules: constructive only, no `sorry`, no `Classical`, no `noncomputable`.
-/

namespace OneColourClosure

/-! ## §0. Chronological-play notation

`RaiseSSeqL`'s word is *reverse chronological* (its head is the last raise).
We write `playWord P` for the word whose chronological play is the list `P`. -/

/-- The word whose chronological play is `P`. -/
def playWord (P : List Card) : List Card := P.reverse

@[simp] theorem playWord_nil : playWord ([] : List Card) = [] := rfl

theorem playWord_append (P Q : List Card) :
    playWord (P ++ Q) = playWord Q ++ playWord P := by
  simp [playWord]

theorem playWord_snoc (P : List Card) (c : Card) :
    playWord (P ++ [c]) = c :: playWord P := by
  simp [playWord]

/-! ## §1. A licensed raise is reversible -/

/-- `CanRaise` is exactly the undoability shape `tabToFoundR`.  Both are
`nextUp ∧ pileOfTop = some a ∧ (chop faceUp ≠ [] ∨ (hidden = [] ∧ c is king))`,
only written differently. -/
theorem canRaise_tabToFoundR {st : State} {c : Card} (h : CanRaise st c) :
    tabToFoundR st c = true := by
  obtain ⟨hnext, a, htop, hdisj⟩ := h
  simp only [tabToFoundR, hnext, htop]
  rcases hdisj with hchop | ⟨hhid, hking⟩
  · cases hc : chop (st.piles a).faceUp with
    | nil => exact absurd hc hchop
    | cons x xs => rfl
  · cases hc : chop (st.piles a).faceUp with
    | nil =>
        rw [hhid]
        exact decide_eq_true hking
    | cons x xs => rfl

/-- **A licensed raise is a reversible move.** -/
theorem canRaise_reversibleAtW {st : State} {c : Card} (hwf : st.WF)
    (h : CanRaise st c) : reversibleAtW st (Move.tabToFound c) :=
  (tabToFoundR_iff_reversibleAtW hwf c).mp (canRaise_tabToFoundR h)

/-! ## §2. Cargo legs move no rung -/

/-- A cargo leg preserves every foundation rung. -/
theorem cargoLeg_rungAt {w v : State} (h : CargoLeg w v) (σ : Suit) :
    rungAt w σ = rungAt v σ := by
  obtain ⟨c, b, hstep, -⟩ := h
  exact (rungAt_tabToTab hstep σ).symm

/-- A cargo path preserves every foundation rung. -/
theorem cargoPath_rungAt {a b : State} (h : CargoPath a b) (σ : Suit) :
    rungAt a σ = rungAt b σ := by
  induction h with
  | refl w => rfl
  | cons hleg rest ih => exact (cargoLeg_rungAt hleg σ).trans ih

/-! ## §3. The rung ledger of a licensed word -/

/-- **The rung ledger.**  After a licensed word `ws`, a suit's rung is its
starting rung plus the number of raised cards of that suit.  Depends on the
word only through its multiset. -/
theorem RaiseSSeqL.rungAt_eq {s z : State} {ws : List Card} (h : RaiseSSeqL s ws z)
    (σ : Suit) :
    rungAt z σ = rungAt s σ + ws.countP (fun c => decide (c.suit = σ)) := by
  induction h with
  | nil => simp
  | cons htail hp hcr hstep ih =>
      rename_i zz zz0 zz' cc wws
      have hcargo : rungAt zz0 σ = rungAt zz σ := (cargoPath_rungAt hp σ).symm
      have hstep' : rungAt zz' σ =
          if σ = cc.suit then rungAt zz0 σ + 1 else rungAt zz0 σ :=
        rungAt_tabToFound hstep σ
      rw [hstep', hcargo, ih, List.countP_cons]
      by_cases hσ : cc.suit = σ
      · rw [ite_eq_left (decide_eq_true hσ), ite_eq_left hσ.symm]
        omega
      · rw [ite_eq_right (c := decide (cc.suit = σ) = true) ?_]
        · rw [ite_eq_right (fun h => hσ h.symm)]
          omega
        · rw [decide_eq_false hσ]
          simp

/-- Same multiset, same rungs. -/
theorem rungAt_eq_of_perm {s u v : State} {P Q : List Card}
    (hP : RaiseSSeqL s P u) (hQ : RaiseSSeqL s Q v) (hperm : P.Perm Q) (σ : Suit) :
    rungAt u σ = rungAt v σ := by
  rw [hP.rungAt_eq σ, hQ.rungAt_eq σ, hperm.countP_eq (fun c => decide (c.suit = σ))]

/-! ## §4. Every licensed play is an orbit walk -/

/-- Every licensed play is a witness shuffle, hence its endpoint is
`RevEqW`-related to its start. -/
theorem RaiseSSeqL.revEqW {s z : State} {ws : List Card} (h : RaiseSSeqL s ws z) :
    s.WF → RevEqW s z := by
  induction h with
  | nil => intro _; exact RevEqW_refl _
  | cons htail hp hcr hstep ih =>
      intro hwf
      rename_i zz zz0 zz' cc wws
      have hzwf : zz.WF := RaiseSSeqL.wf htail hwf
      have hprev : RevEqW s zz := ih hwf
      obtain ⟨play, hplay⟩ := cargoPath_shuffle hp
      have hzwf0 : zz0.WF := cargoPath_wf hzwf hp
      have hrev : reversibleAtW zz0 (Move.tabToFound cc) :=
        canRaise_reversibleAtW hzwf0 hcr
      have hone : ShufflePlayW zz (play ++ [Move.tabToFound cc]) zz' :=
        ShufflePlayW_append hplay (Walk.cons hrev hstep (Walk.nil zz'))
      exact RevEqW_trans hprev (shufflePlayW_revEqW hone)

/-- Any two licensed endpoints from the same start are orbit-mates. -/
theorem revEqW_of_raise_plays {s u v : State} {P Q : List Card}
    (hs : s.WF) (hP : RaiseSSeqL s P u) (hQ : RaiseSSeqL s Q v) :
    RevEqW u v := by
  have hu : RevEqW s u := hP.revEqW hs
  have hv : RevEqW s v := hQ.revEqW hs
  exact RevEqW_trans (RevEqW_symm hu) hv

/-! ## §5. (S) — same multiset, same licences -/

/-- **(S), the same-multiset licence theorem.**  Two licensed plays from the
same state that raise the same multiset of cards end in states with the same
licences. -/
theorem canRaiseS_of_raise_perm {s u v : State} {P Q : List Card} {d : Card}
    (hs : s.WF) (hP : RaiseSSeqL s P u) (hQ : RaiseSSeqL s Q v) (hperm : P.Perm Q) :
    CanRaiseS u d ↔ CanRaiseS v d := by
  have huwf : u.WF := hP.wf hs
  have horb : sameOrbitSetoid.r u v := revEqW_of_raise_plays hs hQ hP
  exact canRaiseS_orbit_rung huwf horb (rungAt_eq_of_perm hP hQ hperm)

/-- **(S), symmetric reading** (recorded so consumers need not swap `Perm`). -/
theorem canRaiseS_of_raise_perm' {s u v : State} {P Q : List Card} {d : Card}
    (hs : s.WF) (hP : RaiseSSeqL s P u) (hQ : RaiseSSeqL s Q v) (hperm : P.Perm Q) :
    CanRaiseS v d → CanRaiseS u d :=
  (canRaiseS_of_raise_perm hs hP hQ hperm).mpr

/-! ## §6. Splitting a licensed word at its *first* raise -/

/-- **Split at the first chronological raise.**  If the word is `ws ++ [c]`
(the last letter is played first), the play splits into the single raise of `c`
and the rest. -/
theorem RaiseSSeqL.split_head {s z : State} {c : Card} {ws : List Card}
    (h : RaiseSSeqL s (ws ++ [c]) z) :
    ∃ u, RaiseSSeqL s [c] u ∧ RaiseSSeqL u ws z := by
  induction ws generalizing s z with
  | nil => exact ⟨z, by simpa using h, RaiseSSeqL.nil z⟩
  | cons a ws ih =>
      rw [List.cons_append] at h
      obtain ⟨z₁, z₀, htail, hp, hcr, hstep⟩ := RaiseSSeqL.step_s h
      obtain ⟨u, hc, hrest⟩ := ih htail
      exact ⟨u, hc, RaiseSSeqL.cons hrest hp hcr hstep⟩

/-- A single licensed step, packaged. -/
theorem raiseSSeqL_single_of_canRaiseS {z : State} {c : Card} (h : CanRaiseS z c) :
    ∃ u, RaiseSSeqL z [c] u := raiseSSeqL_step_of_canRaiseS h

/-! ## §7. Tail transport — the reordering primitive

A play's tail can be replayed from the endpoint of *any* other play of the same
multiset prefix.  This is the step a sorted replay consumes. -/

/-- Two-element reversal preserves permutation. -/
theorem perm_two_reverse_aux (l : List Card) (a b : Card) :
    ((l ++ [a]) ++ [b]).Perm ((l ++ [b]) ++ [a]) := by
  have h : ([a, b] : List Card).Perm [b, a] := (List.Perm.swap a b []).symm
  have h2 : (l ++ [a, b]).Perm (l ++ [b, a]) := List.Perm.append_left l h
  simpa [List.append_assoc] using h2

/-- Reversal preserves permutation (`List.Perm.reverse` is not in this core). -/
theorem perm_reverse {A B : List Card} (h : A.Perm B) : A.reverse.Perm B.reverse := by
  induction h with
  | nil => exact List.Perm.nil
  | cons x _ ih =>
      rw [List.reverse_cons, List.reverse_cons]
      exact ih.append_right [x]
  | swap x y l =>
      rw [List.reverse_cons, List.reverse_cons, List.reverse_cons, List.reverse_cons]
      exact perm_two_reverse_aux l.reverse x y
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- **Split a licensed play at a chronological prefix.** -/
theorem RaiseSSeqL.split_chron {s z : State} {A R : List Card}
    (h : RaiseSSeqL s (playWord (A ++ R)) z) :
    ∃ u, RaiseSSeqL s (playWord A) u ∧ RaiseSSeqL u (playWord R) z := by
  induction A generalizing s with
  | nil => exact ⟨s, RaiseSSeqL.nil s, h⟩
  | cons a A ih =>
      have hword : playWord ((a :: A) ++ R) = playWord (A ++ R) ++ [a] := by
        simp [playWord]
      rw [hword] at h
      obtain ⟨u₀, hstep_a, hrest⟩ := RaiseSSeqL.split_head h
      obtain ⟨u, hA, hR⟩ := ih hrest
      refine ⟨u, ?_, hR⟩
      rw [show playWord (a :: A) = playWord A ++ [a] from by simp [playWord]]
      exact RaiseSSeqL.append hstep_a hA

/-- **Tail transport.**  If `A₁` and `A₂` are permutations and both are
realisable from `s`, then any licensed tail playable after `A₁` is playable
after `A₂`. -/
theorem RaiseSSeqL.tail_transport {s u₁ u₂ z : State} {A₁ A₂ T : List Card}
    (hs : s.WF) (h₁ : RaiseSSeqL s (playWord A₁) u₁)
    (h₂ : RaiseSSeqL s (playWord A₂) u₂) (hperm : A₁.Perm A₂)
    (hT : RaiseSSeqL u₁ (playWord T) z) :
    ∃ z', RaiseSSeqL u₂ (playWord T) z' := by
  induction T generalizing u₁ u₂ z A₁ A₂ with
  | nil => exact ⟨u₂, RaiseSSeqL.nil u₂⟩
  | cons t T ih =>
      -- the word `playWord (t :: T)` is `(playWord T) ++ [t]`: t is played first
      have hword : playWord (t :: T) = playWord T ++ [t] := by
        simp [playWord]
      rw [hword] at hT
      obtain ⟨u₀, hstep_t, hrest⟩ := RaiseSSeqL.split_head hT
      have ht : CanRaiseS u₁ t := canRaiseS_of_raiseSSeqL_head hstep_t
      have hpermw : (playWord A₁).Perm (playWord A₂) := perm_reverse hperm
      have ht₂ : CanRaiseS u₂ t :=
        (canRaiseS_of_raise_perm hs h₁ h₂ hpermw).mp ht
      obtain ⟨u₂', hstep_t₂⟩ := raiseSSeqL_step_of_canRaiseS ht₂
      -- extend both prefix plays by `t`
      have h₁' : RaiseSSeqL s (playWord (A₁ ++ [t])) u₀ := by
        rw [playWord_snoc]
        exact RaiseSSeqL.append h₁ hstep_t
      have h₂' : RaiseSSeqL s (playWord (A₂ ++ [t])) u₂' := by
        rw [playWord_snoc]
        exact RaiseSSeqL.append h₂ hstep_t₂
      obtain ⟨z', hz'⟩ := ih h₁' h₂' (hperm.append_right [t]) hrest
      exact ⟨z', by rw [hword]; exact RaiseSSeqL.append hstep_t₂ hz'⟩


/-- **Inversion swap** (the bubble-sort primitive).  A licensed play can swap
adjacent cards `x` then `y` when `y` has *strictly lower* rank: `y`'s licence at
the prefix endpoint is recovered from its licence after `x` by inertness
(`canRaiseS_unraise_word`), both are then licensed there, and the tail is
replayed from the swapped endpoint by (S) (`tail_transport`). -/
theorem swap_inversion {s z : State} {A T : List Card} {x y : Card}
    (hs : s.WF) (hr : y.rank.toIdx < x.rank.toIdx)
    (h : RaiseSSeqL s (playWord (A ++ [x, y] ++ T)) z) :
    ∃ z', RaiseSSeqL s (playWord (A ++ [y, x] ++ T)) z' := by
  -- `++` is left-associative: `A ++ [x, y] ++ T` is `(A ++ [x, y]) ++ T`
  obtain ⟨uy, hOld, hT⟩ := RaiseSSeqL.split_chron (A := A ++ [x, y]) (R := T) h
  obtain ⟨u, hA, hR⟩ := RaiseSSeqL.split_chron (A := A) (R := [x, y]) hOld
  obtain ⟨ux, hx_play, hy_play⟩ := RaiseSSeqL.split_chron (A := [x]) (R := [y]) hR
  have huwf : u.WF := hA.wf hs
  have hx : CanRaiseS u x := canRaiseS_of_raiseSSeqL_head hx_play
  have hy' : CanRaiseS ux y := canRaiseS_of_raiseSSeqL_head hy_play
  have hrne : x.rank ≠ y.rank := by intro hcon; rw [hcon] at hr; omega
  have hy : CanRaiseS u y := by
    refine canRaiseS_unraise_word hx_play huwf ?_ hy'
    intro b hb
    simp only [playWord, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.mem_singleton] at hb
    subst hb
    exact hr
  -- fire `y` then `x` at `u`
  obtain ⟨u₁, hy_play'⟩ := raiseSSeqL_step_of_canRaiseS hy
  have hstep_y : RaiseStepS u u₁ y := by
    obtain ⟨z, z0, hnil, hp, hcr, hst⟩ := RaiseSSeqL.step_s hy_play'
    cases hnil
    exact ⟨z0, hp, hst⟩
  have hx₂ : CanRaiseS u₁ x :=
    canRaiseS_step_of_rank_ne huwf hstep_y (Ne.symm hrne) hx
  obtain ⟨u₂, hx_play'⟩ := raiseSSeqL_step_of_canRaiseS hx₂
  -- the swapped prefix play from `s`
  have hNew : RaiseSSeqL s (playWord (A ++ [y, x])) u₂ := by
    rw [show playWord (A ++ [y, x]) = playWord [y, x] ++ playWord A from
      playWord_append A [y, x]]
    have hyx : RaiseSSeqL u (playWord [y, x]) u₂ := by
      have := RaiseSSeqL.append hy_play' hx_play'
      simpa [playWord] using this
    exact RaiseSSeqL.append hA hyx
  have hperm : (A ++ [x, y]).Perm (A ++ [y, x]) :=
    List.Perm.append_left A (List.Perm.swap y x [])
  obtain ⟨z', hz'⟩ := RaiseSSeqL.tail_transport hs hOld hNew hperm hT
  refine ⟨z', ?_⟩
  have hfin := RaiseSSeqL.append hNew hz'
  simpa [playWord, List.append_assoc] using hfin

/-! ## §8. The residual as stated by the parent is FALSE

`SortedPrefixLicence` (from `Temp/RankFront_licensed.lean` §5) has no
`x ∉ R` hypothesis.  If `x ∈ R` then the sorted prefix has *already raised*
`x`, so `nextUp x` is false at its endpoint and `CanRaiseS u x` cannot hold.
The refutation below is the smallest instance: `R = P = [K♦]` at `t6`
(three bare kings). -/

/-- `K♦` is a vanilla top at `t6`: next-up, bare-king seat. -/
theorem t6_canRaise_KD : CanRaise t6 cKD := by
  refine ⟨by decide, Anchor.p2, by decide, ?_⟩
  exact Or.inr ⟨by decide, by decide⟩

/-- One licensed step of `K♦` at `t6`. -/
theorem t6_raiseSSeqL_KD : RaiseSSeqL t6 [cKD] t6a :=
  RaiseSSeqL.cons (RaiseSSeqL.nil t6) (Steps.refl t6) t6_canRaise_KD t6_step_KD

/-- After founding `K♦` its suit's rung is 13, so `nextUp` fails. -/
theorem t6a_not_nextUp_KD : t6a.nextUp cKD = false := by decide

/-- Hence `K♦` is not licensed after it has been raised. -/
theorem t6a_not_canRaiseS_KD : ¬ CanRaiseS t6a cKD := by
  intro h
  have hwf : t6a.WF := step_wf t6_WF t6_step_KD
  have hnext : t6a.nextUp cKD = true := ((canRaiseS_split hwf (c := cKD)).mp h).1
  rw [t6a_not_nextUp_KD] at hnext
  exact absurd hnext (by simp)

/-- **The parent's `SortedPrefixLicence` is refuted** (kernel-checked): take
`R = P = [K♦]`, `x = K♦`.  Every hypothesis holds — `R` is ascending, `R ⊆ P`,
`x ∈ P` — yet the conclusion `CanRaiseS t6a K♦` is false.  The missing
hypothesis is `x ∉ R` (the sorted prefix must not already contain the card whose
licence is being transferred). -/
theorem sortedPrefixLicence_false : ¬ SortedPrefixLicence := by
  intro H
  have hsort : ([cKD] : List Card).Pairwise
      (fun a b => a.rank.toIdx ≤ b.rank.toIdx) := by simp
  have hlow : ∀ p ∈ ([cKD] : List Card), p.rank.toIdx < cKD.rank.toIdx →
      p ∈ ([cKD] : List Card) := fun p hp _ => hp
  have hmem : cKD ∈ ([cKD] : List Card) := by simp
  have h := H t6_WF hsort (fun r hr => hr) hlow
    t6_raiseSSeqL_KD t6_raiseSSeqL_KD hmem
  exact t6a_not_canRaiseS_KD h

/-- **The repaired residual** — `SortedPrefixLicence` with `x ∉ R` added.
This is the honest form of the sorted-prefix bridge left open by
`Temp/RankFront_licensed.lean`.  (S) `canRaiseS_of_raise_perm` discharges its
licence-transfer half; what remains is the sorted-order/tie passage, and in
particular the *tail-existence* step named in the report. -/
def SortedPrefixLicenceFixed : Prop :=
  ∀ {s z u : State} {R P : List Card} {x : Card},
    s.WF →
    R.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) →
    (∀ r ∈ R, r ∈ P) →
    (∀ p ∈ P, p.rank.toIdx < x.rank.toIdx → p ∈ R) →
    x ∉ R →
    RaiseSSeqL s R.reverse u →
    RaiseSSeqL s P.reverse z →
    x ∈ P →
    CanRaiseS u x

/-- **The residual, in tail-existence form.**  Raising a licensed card `c` first
leaves the sorted rest of the raised multiset playable.

This is the *exact* remaining obligation of the lane.  (S) does **not** give it:
(S) compares the endpoints of two plays of the *same* multiset, whereas this
compares the endpoint of the single-raise play `[c]` with the interior state of
a longer play, and asks for a play of the remaining multiset from that endpoint.
The obstruction is not licence transfer (that is (S)) but the *sorted-order /
tie* passage: moving `c` to the front of a play across cards of *equal rank* is
not an inversion swap (`swap_inversion` needs strict inequality), and the
state-level tie step is false (probe `RankFront_close_probe10.py`: two
same-rank cards can both be licensed with neither order playable).  Only the
existence of the full play of the multiset can rescue it. -/
def TailExists : Prop :=
  ∀ {s z : State} {ws : List Card} {c : Card},
    s.WF → CanRaiseS s c → RaiseSSeqL s ws z → c ∈ ws →
      ∃ s₁, RaiseSSeqL s [c] s₁ ∧
        ∃ z', RaiseSSeqL s₁ (playWord (sortRank (ws.erase c))) z'

/-- **The lane reduces to `TailExists`**: the rank-front theorem follows from the
single residual statement. -/
theorem raiseS_rankfront_L_of_tail (H : TailExists) :
    ∀ {s z : State} {c : Card} {ws : List Card},
      s.WF → CanRaiseS s c → RaiseSSeqL s ws z → c ∈ ws →
        ∃ z', RaiseSSeqL s (rankFront c ws) z' := by
  intro s z c ws hs hc h hmem
  obtain ⟨s₁, hstep, z', htail⟩ := H hs hc h hmem
  refine ⟨z', ?_⟩
  have hfin : RaiseSSeqL s (playWord (sortRank (ws.erase c)) ++ [c]) z' :=
    RaiseSSeqL.append hstep htail
  rwa [show playWord (sortRank (ws.erase c)) ++ [c] = rankFront c ws from by
    simp [rankFront, playWord]] at hfin

/-! ## §9. The ascending play exists (the "sorted" census row as a theorem)

`insRank` / `sortRank` are `Temp/RankFront_proof.lean`'s stable ascending sort.
The whole content is: an adjacent inversion swap (`swap_inversion`) can push a
card rightward past every strictly-lower card, so a sorted list can always be
rebuilt from `c :: L` by bubbling `c` into place.  No sortedness hypothesis and
no tie swap is needed: `insRank` decides by `c.rank ≤ b.rank`, and the only
swaps used are strict. -/

/-- **Push a card into ascending place.**  If `c :: L` is a licensed play then so
is `insRank c L`. -/
theorem insRank_push {c : Card} :
    ∀ {s z : State} {L : List Card}, s.WF →
      RaiseSSeqL s (playWord (c :: L)) z →
        ∃ z', RaiseSSeqL s (playWord (insRank c L)) z' := by
  intro s z L
  induction L generalizing s z with
  | nil =>
      intro _ h
      exact ⟨z, by simpa [insRank] using h⟩
  | cons b L ih =>
      intro hs h
      by_cases hcb : c.rank.toIdx ≤ b.rank.toIdx
      · have hins : insRank c (b :: L) = c :: b :: L := by
          simp [insRank, hcb]
        rw [hins]
        exact ⟨z, h⟩
      · have hins : insRank c (b :: L) = b :: insRank c L := by
          simp [insRank, hcb]
        rw [hins]
        have hr : b.rank.toIdx < c.rank.toIdx := by omega
        -- swap the adjacent pair `(c, b)` into `(b, c)`
        obtain ⟨zs, hswap⟩ := swap_inversion (s := s) (z := z) (A := []) (T := L)
          (x := c) (y := b) hs hr (by simpa [playWord] using h)
        -- split off the leading `b`
        obtain ⟨s_b, h_b, hcL⟩ := RaiseSSeqL.split_chron (A := [b]) (R := c :: L)
          (s := s) (z := zs) (by simpa [playWord] using hswap)
        obtain ⟨z₂, hz₂⟩ := ih (s := s_b) (z := zs) (RaiseSSeqL.wf h_b hs) hcL
        refine ⟨z₂, ?_⟩
        have hfin := RaiseSSeqL.append h_b hz₂
        simpa [playWord] using hfin

/-- **The sorted play exists whenever a licensed play exists.**  This is the
`sorted` row of the rank-front census as a theorem. -/
theorem sortable {P : List Card} :
    ∀ {s z : State}, s.WF → RaiseSSeqL s (playWord P) z →
      ∃ z', RaiseSSeqL s (playWord (sortRank P)) z' := by
  induction P with
  | nil =>
      intro s z _ h
      exact ⟨z, by simpa [sortRank] using h⟩
  | cons a P ih =>
      intro s z hs h
      obtain ⟨s_a, h_a, h'⟩ := RaiseSSeqL.split_chron (A := [a]) (R := P) h
      have hsa : s_a.WF := RaiseSSeqL.wf h_a hs
      obtain ⟨z₁, hz₁⟩ := ih hsa h'
      have hpre : RaiseSSeqL s (playWord (a :: sortRank P)) z₁ := by
        rw [show playWord (a :: sortRank P) = playWord (sortRank P) ++ [a] from by
          simp [playWord]]
        exact RaiseSSeqL.append h_a hz₁
      have := insRank_push (c := a) (L := sortRank P) hs hpre
      simpa [sortRank] using this

/-- The `sorted` census row, in word form: if a licensed word is realisable
then its chronologically rank-sorted word is realisable.  (The word is the
reverse of the sorted *play*, hence `sortRank ws.reverse`.) -/
theorem raiseS_sorted_of_licensed {s z : State} {ws : List Card}
    (hs : s.WF) (h : RaiseSSeqL s ws z) :
    ∃ z', RaiseSSeqL s ((sortRank ws.reverse).reverse) z' := by
  have h' : RaiseSSeqL s (playWord ws.reverse) z := by simpa [playWord] using h
  obtain ⟨z', hz'⟩ := sortable (P := ws.reverse) hs h'
  exact ⟨z', hz'⟩

end OneColourClosure

#print axioms OneColourClosure.canRaise_tabToFoundR
#print axioms OneColourClosure.canRaise_reversibleAtW
#print axioms OneColourClosure.cargoLeg_rungAt
#print axioms OneColourClosure.cargoPath_rungAt
#print axioms OneColourClosure.RaiseSSeqL.rungAt_eq
#print axioms OneColourClosure.rungAt_eq_of_perm
#print axioms OneColourClosure.RaiseSSeqL.revEqW
#print axioms OneColourClosure.revEqW_of_raise_plays
#print axioms OneColourClosure.canRaiseS_of_raise_perm
#print axioms OneColourClosure.canRaiseS_of_raise_perm'
#print axioms OneColourClosure.RaiseSSeqL.split_head
#print axioms OneColourClosure.RaiseSSeqL.tail_transport
#print axioms OneColourClosure.perm_two_reverse_aux
#print axioms OneColourClosure.perm_reverse
#print axioms OneColourClosure.RaiseSSeqL.split_chron
#print axioms OneColourClosure.swap_inversion
#print axioms OneColourClosure.raiseSSeqL_single_of_canRaiseS
#print axioms OneColourClosure.playWord_append
#print axioms OneColourClosure.playWord_snoc
#print axioms OneColourClosure.t6_canRaise_KD
#print axioms OneColourClosure.t6_raiseSSeqL_KD
#print axioms OneColourClosure.t6a_not_nextUp_KD
#print axioms OneColourClosure.t6a_not_canRaiseS_KD
#print axioms OneColourClosure.sortedPrefixLicence_false
#print axioms OneColourClosure.insRank_push
#print axioms OneColourClosure.sortable
#print axioms OneColourClosure.raiseS_sorted_of_licensed
#print axioms OneColourClosure.raiseS_rankfront_L_of_tail
