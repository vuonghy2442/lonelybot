import Orig2.Fork.Class.ForkRaiseReorderKit

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-!
# Orig2.Fork.Class.ForkRaiseReorderProof — the rank-front theorem

The proof half of the port: `RankFront` (the card's statement) is closed at the
licensed grade, unconditionally.

Route (all rows are already in `Orig2`):

* a licensed raise is reversible (`canRaise_reversibleAtW`), so every
  `RaiseSSeqLicensed` play is a witness shuffle and its endpoint is
  `RevEqW`-related to its start;
* a raise moves exactly one suit's rung by one, so same-multiset plays end at
  equal rungs, and at equal rungs the S-licence is an orbit invariant
  (`canRaiseS_orbit_rung`) — this is `canRaiseS_of_raise_perm` (row **(S)**);
* a strictly higher-rank licensed raise is licence-inert in both directions
  (`canRaiseS_inert_of_canRaiseStep`), which drives the adjacent inversion swap
  `swap_inversion` and the sorted-play theorem;
* the equal-rank tie block is `tie_swap` / `tieFree`; the play-level swap uses
  `twin_raise_square` on the two vanilla raises at the exposed witness;
* `tail_exists` assembles these, and `raiseS_rankfront_L` = `tail_exists` +
  the word/play bridge `rankFrontWord`.

House rules: constructive only, no `sorry`, no `Classical`, no `noncomputable`.
No new `Prop` predicate is introduced.
-/

namespace OneColourClosure

/-! ## §1. Chronological-play notation

`RaiseSSeqLicensed`'s word is *reverse chronological* (its head is the last
raise).  `playWord P` is the word whose chronological play is the list `P`. -/

/-- The word whose chronological play is `P`. -/
def playWord (P : List Card) : List Card := P.reverse

@[simp] theorem playWord_nil : playWord ([] : List Card) = [] := rfl

theorem playWord_append (P Q : List Card) :
    playWord (P ++ Q) = playWord Q ++ playWord P := by
  simp [playWord]

theorem playWord_snoc (P : List Card) (c : Card) :
    playWord (P ++ [c]) = c :: playWord P := by
  simp [playWord]

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
theorem RaiseSSeqLicensed.rungAt_eq {s z : State} {ws : List Card}
    (h : RaiseSSeqLicensed s ws z) (σ : Suit) :
    rungAt z σ = rungAt s σ + ws.countP (fun c => decide (c.suit = σ)) := by
  induction h with
  | nil => simp
  | cons htail hS hp hstep ih =>
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
    (hP : RaiseSSeqLicensed s P u) (hQ : RaiseSSeqLicensed s Q v) (hperm : P.Perm Q)
    (σ : Suit) :
    rungAt u σ = rungAt v σ := by
  rw [hP.rungAt_eq σ, hQ.rungAt_eq σ, hperm.countP_eq (fun c => decide (c.suit = σ))]

/-! ## §4. Every licensed play is an orbit walk -/

/-- Every licensed play is a witness shuffle, hence its endpoint is
`RevEqW`-related to its start. -/
theorem RaiseSSeqLicensed.revEqW {s z : State} {ws : List Card}
    (h : RaiseSSeqLicensed s ws z) : s.WF → RevEqW s z := by
  induction h with
  | nil => intro _; exact RevEqW_refl _
  | cons htail hS hp hstep ih =>
      intro hwf
      rename_i zz zz0 zz' cc wws
      have hzwf : zz.WF := RaiseSSeqLicensed.wf htail hwf
      have hprev : RevEqW s zz := ih hwf
      obtain ⟨play, hplay⟩ := cargoPath_shuffle hp
      have hzwf0 : zz0.WF := cargoPath_wf hzwf hp
      have hcr : CanRaise zz0 cc := canRaise_of_canRaiseS_of_step hzwf hS hp hstep
      have hrev : reversibleAtW zz0 (Move.tabToFound cc) :=
        DrainClose.reversibleAtW_tabToFound_of_canRaise hzwf0 hcr
      have hone : ShufflePlayW zz (play ++ [Move.tabToFound cc]) zz' :=
        ShufflePlayW_append hplay (Walk.cons hrev hstep (Walk.nil zz'))
      exact RevEqW_trans hprev (shufflePlayW_revEqW hone)

/-- Any two licensed endpoints from the same start are orbit-mates. -/
theorem revEqW_of_raise_plays {s u v : State} {P Q : List Card}
    (hs : s.WF) (hP : RaiseSSeqLicensed s P u) (hQ : RaiseSSeqLicensed s Q v) :
    RevEqW u v := by
  have hu : RevEqW s u := hP.revEqW hs
  have hv : RevEqW s v := hQ.revEqW hs
  exact RevEqW_trans (RevEqW_symm hu) hv

/-! ## §5. (S) — same multiset, same licences -/

/-- **(S), the same-multiset licence theorem.**  Two licensed plays from the
same state that raise the same multiset of cards end in states with the same
licences. -/
theorem canRaiseS_of_raise_perm {s u v : State} {P Q : List Card} {d : Card}
    (hs : s.WF) (hP : RaiseSSeqLicensed s P u) (hQ : RaiseSSeqLicensed s Q v)
    (hperm : P.Perm Q) :
    CanRaiseS u d ↔ CanRaiseS v d := by
  have huwf : u.WF := hP.wf hs
  have horb : sameOrbitSetoid.r u v := revEqW_of_raise_plays hs hQ hP
  exact canRaiseS_orbit_rung huwf horb (rungAt_eq_of_perm hP hQ hperm)

/-- **(S), symmetric reading** (recorded so consumers need not swap `Perm`). -/
theorem canRaiseS_of_raise_perm' {s u v : State} {P Q : List Card} {d : Card}
    (hs : s.WF) (hP : RaiseSSeqLicensed s P u) (hQ : RaiseSSeqLicensed s Q v)
    (hperm : P.Perm Q) :
    CanRaiseS v d → CanRaiseS u d :=
  (canRaiseS_of_raise_perm hs hP hQ hperm).mpr

/-! ## §6. Permutation kit for the reordering -/

/-- Two-element reversal preserves permutation. -/
theorem perm_two_reverse_aux (l : List Card) (a b : Card) :
    ((l ++ [a]) ++ [b]).Perm ((l ++ [b]) ++ [a]) := by
  have h : ([a, b] : List Card).Perm [b, a] := (List.Perm.swap a b []).symm
  have h2 : (l ++ [a, b]).Perm (l ++ [b, a]) := List.Perm.append_left l h
  simpa [List.append_assoc] using h2

/-- Reversal preserves permutation. -/
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

/-- Erasing the same card from two permutations gives permutations. -/
theorem perm_erase {l₁ l₂ : List Card} {x : Card} (h : l₁.Perm l₂) :
    (l₁.erase x).Perm (l₂.erase x) := by
  induction h with
  | nil => exact List.Perm.nil
  | cons a h ih =>
      by_cases hax : (a == x) = true
      · have hae : a = x := beq_iff_eq.mp hax
        subst hae
        rw [List.erase_cons_head, List.erase_cons_head]
        exact h
      · rw [List.erase_cons_tail hax, List.erase_cons_tail hax]
        exact ih.cons a
  | swap a b l =>
      by_cases hb : b = x
      · rw [hb]
        by_cases ha : a = x
        · have e1 : (x :: a :: l).erase x = a :: l := List.erase_cons_head x (a :: l)
          have e2 : (a :: x :: l).erase x = a :: l := by
            rw [ha]
            exact List.erase_cons_head x (x :: l)
          rw [e1, e2]
        · have hne : ¬((a == x) = true) := by simp [beq_iff_eq, ha]
          have e1 : (x :: a :: l).erase x = a :: l := List.erase_cons_head x (a :: l)
          have e2 : (a :: x :: l).erase x = a :: l := by
            rw [List.erase_cons_tail hne, List.erase_cons_head]
          rw [e1, e2]
      · have hneb : ¬((b == x) = true) := by simp [beq_iff_eq, hb]
        by_cases ha : a = x
        · rw [ha]
          have e1 : (b :: x :: l).erase x = b :: l := by
            rw [List.erase_cons_tail hneb, List.erase_cons_head]
          have e2 : (x :: b :: l).erase x = b :: l := List.erase_cons_head x (b :: l)
          rw [e1, e2]
        · have hnea : ¬((a == x) = true) := by simp [beq_iff_eq, ha]
          have e1 : (b :: a :: l).erase x = b :: a :: l.erase x := by
            rw [List.erase_cons_tail hneb, List.erase_cons_tail hnea]
          have e2 : (a :: b :: l).erase x = a :: b :: l.erase x := by
            rw [List.erase_cons_tail hnea, List.erase_cons_tail hneb]
          rw [e1, e2]
          exact List.Perm.swap a b (l.erase x)
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## §7. Splitting a licensed word -/

/-- **The last step, without `WF`.**  Extracts the tail play, the S-licence of
the head, the slide and the firing step. -/
theorem RaiseSSeqLicensed.step_s' {s z' : State} {c : Card} {ws : List Card}
    (h : RaiseSSeqLicensed s (c :: ws) z') :
    ∃ z z₀, RaiseSSeqLicensed s ws z ∧ CanRaiseS z c ∧ CargoPath z z₀ ∧
      State.step z₀ (Move.tabToFound c) = some z' := by
  cases h with
  | cons htail hS hp hs => exact ⟨_, _, htail, hS, hp, hs⟩

/-- **Split at the first chronological raise.**  If the word is `ws ++ [c]`
(the last letter is played first), the play splits into the single raise of `c`
and the rest. -/
theorem RaiseSSeqLicensed.split_head {s z : State} {c : Card} {ws : List Card}
    (h : RaiseSSeqLicensed s (ws ++ [c]) z) :
    ∃ u, RaiseSSeqLicensed s [c] u ∧ RaiseSSeqLicensed u ws z := by
  induction ws generalizing s z with
  | nil => exact ⟨z, by simpa using h, RaiseSSeqLicensed.nil z⟩
  | cons a ws ih =>
      rw [List.cons_append] at h
      obtain ⟨z₁, z₀, htail, hS, hp, hstep⟩ := RaiseSSeqLicensed.step_s' h
      obtain ⟨u, hc, hrest⟩ := ih htail
      exact ⟨u, hc, RaiseSSeqLicensed.cons hrest hS hp hstep⟩

/-- **Split a licensed play at a chronological prefix.** -/
theorem RaiseSSeqLicensed.split_chron {s z : State} {A R : List Card}
    (h : RaiseSSeqLicensed s (playWord (A ++ R)) z) :
    ∃ u, RaiseSSeqLicensed s (playWord A) u ∧ RaiseSSeqLicensed u (playWord R) z := by
  induction A generalizing s with
  | nil => exact ⟨s, RaiseSSeqLicensed.nil s, h⟩
  | cons a A ih =>
      have hword : playWord ((a :: A) ++ R) = playWord (A ++ R) ++ [a] := by
        simp [playWord]
      rw [hword] at h
      obtain ⟨u₀, hstep_a, hrest⟩ := RaiseSSeqLicensed.split_head h
      obtain ⟨u, hA, hR⟩ := ih hrest
      refine ⟨u, ?_, hR⟩
      rw [show playWord (a :: A) = playWord A ++ [a] from by simp [playWord]]
      exact RaiseSSeqLicensed.append hstep_a hA

/-- **Tail transport.**  If `A₁` and `A₂` are permutations and both are
realisable from `s`, then any licensed tail playable after `A₁` is playable
after `A₂`. -/
theorem RaiseSSeqLicensed.tail_transport {s u₁ u₂ z : State} {A₁ A₂ T : List Card}
    (hs : s.WF) (h₁ : RaiseSSeqLicensed s (playWord A₁) u₁)
    (h₂ : RaiseSSeqLicensed s (playWord A₂) u₂) (hperm : A₁.Perm A₂)
    (hT : RaiseSSeqLicensed u₁ (playWord T) z) :
    ∃ z', RaiseSSeqLicensed u₂ (playWord T) z' := by
  induction T generalizing u₁ u₂ z A₁ A₂ with
  | nil => exact ⟨u₂, RaiseSSeqLicensed.nil u₂⟩
  | cons t T ih =>
      have hword : playWord (t :: T) = playWord T ++ [t] := by
        simp [playWord]
      rw [hword] at hT
      obtain ⟨u₀, hstep_t, hrest⟩ := RaiseSSeqLicensed.split_head hT
      have ht : CanRaiseS u₁ t := canRaiseS_of_raiseSSeqLicensed_head hstep_t
      have hpermw : (playWord A₁).Perm (playWord A₂) := perm_reverse hperm
      have ht₂ : CanRaiseS u₂ t :=
        (canRaiseS_of_raise_perm hs h₁ h₂ hpermw).mp ht
      obtain ⟨u₂', hstep_t₂⟩ := raiseSSeqLicensed_step_of_canRaiseS ht₂
      have h₁' : RaiseSSeqLicensed s (playWord (A₁ ++ [t])) u₀ := by
        rw [playWord_snoc]
        exact RaiseSSeqLicensed.append h₁ hstep_t
      have h₂' : RaiseSSeqLicensed s (playWord (A₂ ++ [t])) u₂' := by
        rw [playWord_snoc]
        exact RaiseSSeqLicensed.append h₂ hstep_t₂
      obtain ⟨z', hz'⟩ := ih h₁' h₂' (hperm.append_right [t]) hrest
      exact ⟨z', by rw [hword]; exact RaiseSSeqLicensed.append hstep_t₂ hz'⟩

/-! ## §8. Inertness of a licensed strictly higher raise -/

/-- **Card arithmetic.**  If `e` is the top (last face-up card) of a legal run
and `d` is another face-up card of that run, then `e` is above `d`, so
`e.rank < d.rank`. -/
theorem rank_lt_of_mem_of_lastOf {l : List Card} (h : runOK l = true) {e d : Card}
    (hlast : lastOf l = some e) (hd : d ∈ l) (hde : d ≠ e) :
    e.rank.toIdx < d.rank.toIdx := by
  induction l with
  | nil => exact absurd hd List.not_mem_nil
  | cons x t ih =>
      cases t with
      | nil =>
          have hx : x = e := by simpa [lastOf] using hlast
          have hdx : d = x := by simpa using hd
          exact absurd (hdx.trans hx) hde
      | cons y t =>
          have hlast' : lastOf (y :: t) = some e := by simpa [lastOf] using hlast
          rcases List.mem_cons.mp hd with hdx | hdt
          · have he : e ∈ y :: t := lastOf_mem hlast'
            have hlt := above_rank_lt h (y :: t) [] x e rfl he
            rw [← hdx] at hlt
            exact hlt
          · have hrun : runOK (y :: t) = true := (tfc_runOK_two_true h).2
            exact ih hrun hlast' hdt

/-- A card strictly lower-ranked than a pile top cannot occur in that pile. -/
theorem not_mem_pileOfTop_of_rank_lt {z : State} (hz : z.WF) {e d : Card}
    {a : Anchor} (hpa : z.pileOfTop e = some a)
    (hr : d.rank.toIdx < e.rank.toIdx) :
    d ∉ (z.piles a).faceUp := by
  intro hmem
  have hlast : lastOf (z.piles a).faceUp = some e := (pileOfTop_top hpa).2
  have hde : d ≠ e := by intro h; rw [h] at hr; omega
  have hlt := rank_lt_of_mem_of_lastOf (hz.2.1 a) hlast hmem hde
  omega

/-- The twin of a strictly lower-ranked card is also absent from the pile of the
top. -/
theorem not_mem_pileOfTop_twin_of_rank_lt {z : State} (hz : z.WF) {e d : Card}
    {a : Anchor} (hpa : z.pileOfTop e = some a)
    (hr : d.rank.toIdx < e.rank.toIdx) :
    d.twin ∉ (z.piles a).faceUp := by
  have hrt : d.twin.rank.toIdx = d.rank.toIdx := rfl
  intro hmem
  have hlast : lastOf (z.piles a).faceUp = some e := (pileOfTop_top hpa).2
  have hde : d.twin ≠ e := by
    intro h
    have h1 : d.twin.rank.toIdx = e.rank.toIdx := by rw [h]
    omega
  have hlt := rank_lt_of_mem_of_lastOf (hz.2.1 a) hlast hmem hde
  omega

/-- The holding pile of a card is unchanged by a raise that does not touch its
pile. -/
theorem pileHolding_eq_of_agree {z z' : State} {a0 : Anchor} {x : Card}
    (hwz' : z'.WF)
    (hagree : ∀ a, a ≠ a0 → z'.piles a = z.piles a)
    (hx0 : x ∉ (z.piles a0).faceUp) (hx0' : x ∉ (z'.piles a0).faceUp) :
    z'.pileHolding x = z.pileHolding x := by
  cases hh : z.pileHolding x with
  | none =>
      have hno : ∀ a, x ∉ (z'.piles a).faceUp := by
        intro a
        by_cases ha : a = a0
        · subst ha; exact hx0'
        · rw [hagree a ha]; exact tfc_not_mem_faceUp_of_holdNone hh a
      rw [tfc_pileHolding_none hno]
  | some a =>
      have ha0 : a ≠ a0 := by
        intro h; subst h; exact hx0 (pileHolding_mem hh)
      have hmem : x ∈ (z'.piles a).faceUp := by
        rw [hagree a ha0]; exact pileHolding_mem hh
      rw [(pileHolding_eq_some_iff hwz').mpr hmem]

/-- The top-search for a card absent from the changed pile is unchanged. -/
theorem pileOfTop_eq_of_agree {z z' : State} {a0 : Anchor} {x : Card}
    (hagree : ∀ a, a ≠ a0 → z'.piles a = z.piles a)
    (hx0 : x ∉ (z.piles a0).faceUp) (hx0' : x ∉ (z'.piles a0).faceUp) :
    z'.pileOfTop x = z.pileOfTop x := by
  unfold State.pileOfTop
  apply firstWhere_congr
  intro a
  by_cases ha : a = a0
  · subst ha
    have h1 : ¬ ((z'.piles a).top = some x) := fun h => hx0' (Pile.mem_of_top h)
    have h2 : ¬ ((z.piles a).top = some x) := fun h => hx0 (Pile.mem_of_top h)
    simp [State.topOf, h1, h2]
  · have hp := hagree a ha
    show decide (z'.topOf a = some x) = decide (z.topOf a = some x)
    rw [State.topOf, State.topOf, hp]

/-- `nextUp` of a lower-ranked card is unchanged by a raise of a higher rank. -/
theorem nextUp_tabToFound_eq_of_low_rank {z z' : State} {e d : Card}
    (hstep : State.step z (Move.tabToFound e) = some z')
    (hr : d.rank.toIdx < e.rank.toIdx) :
    z'.nextUp d = z.nextUp d := by
  have hnext : z.nextUp e = true := (step_tabToFound_inv hstep).1
  have heq : e.rank.toIdx = z.foundHeight e.suit := by
    simpa [State.nextUp] using of_decide_eq_true hnext
  unfold State.nextUp
  by_cases hsu : d.suit = e.suit
  · have hlen0 : z.foundHeight d.suit = e.rank.toIdx := by rw [hsu]; exact heq.symm
    have hlen1 : z'.foundHeight d.suit = z.foundHeight d.suit + 1 := by
      unfold State.foundHeight
      rw [found_tabToFound hstep d.suit, ite_eq_left hsu, List.length_append,
        List.length_singleton]
    rw [hlen1, hlen0]
    have h1 : ¬ (d.rank.toIdx = e.rank.toIdx) := by omega
    have h2 : ¬ (d.rank.toIdx = e.rank.toIdx + 1) := by omega
    simp [h1, h2]
  · have hlen : z'.foundHeight d.suit = z.foundHeight d.suit := by
      unfold State.foundHeight
      rw [found_tabToFound hstep d.suit, ite_eq_right hsu]
    rw [hlen]

/-- **`freeCardS` inertness.**  A *licensed* raise of a strictly higher rank
leaves the tableau-readiness of `d` untouched: the raised card's pile neither
holds `d` nor `d.twin` (rank), and a licensed raise never reveals a hidden
card. -/
theorem freeCardS_tabToFound_eq_of_low_rank {z z' : State} {e d : Card}
    (hz : z.WF) (hstep : State.step z (Move.tabToFound e) = some z')
    (hcr : CanRaise z e) (hr : d.rank.toIdx < e.rank.toIdx) :
    freeCardS z' d = freeCardS z d := by
  obtain ⟨-, a1, hpa1, hseat⟩ := hcr
  obtain ⟨a0, hpa0, hpiles⟩ := piles_tabToFound hstep
  have ha10 : a1 = a0 := Option.some.inj (hpa1.symm.trans hpa0)
  rw [ha10] at hseat
  have hwz' : z'.WF := step_wf hz hstep
  have hd0 : d ∉ (z.piles a0).faceUp := not_mem_pileOfTop_of_rank_lt hz hpa0 hr
  have hdt0 : d.twin ∉ (z.piles a0).faceUp :=
    not_mem_pileOfTop_twin_of_rank_lt hz hpa0 hr
  have hd0' : d ∉ (z'.piles a0).faceUp := by
    have hp0 : z'.piles a0 =
        Pile.afterRunRemoved (z.piles a0) (chop (z.piles a0).faceUp) := by
      rw [hpiles a0, ite_eq_left rfl]
    rw [hp0]
    rcases hseat with hne | ⟨hhid, -⟩
    · rw [afterRunRemoved_faceUp_ne hne]
      intro h; exact hd0 (chop_mem h)
    · by_cases hch : chop (z.piles a0).faceUp = []
      · rw [hch, afterRunRemoved_faceUp_bare hhid]; simp
      · rw [afterRunRemoved_faceUp_ne hch]
        intro h; exact hd0 (chop_mem h)
  have hdt0' : d.twin ∉ (z'.piles a0).faceUp := by
    have hp0 : z'.piles a0 =
        Pile.afterRunRemoved (z.piles a0) (chop (z.piles a0).faceUp) := by
      rw [hpiles a0, ite_eq_left rfl]
    rw [hp0]
    rcases hseat with hne | ⟨hhid, -⟩
    · rw [afterRunRemoved_faceUp_ne hne]
      intro h; exact hdt0 (chop_mem h)
    · by_cases hch : chop (z.piles a0).faceUp = []
      · rw [hch, afterRunRemoved_faceUp_bare hhid]; simp
      · rw [afterRunRemoved_faceUp_ne hch]
        intro h; exact hdt0 (chop_mem h)
  have hagree : ∀ a, a ≠ a0 → z'.piles a = z.piles a := by
    intro a ha
    rw [hpiles a, ite_eq_right ha]
  have hph_d : z'.pileHolding d = z.pileHolding d :=
    pileHolding_eq_of_agree hwz' hagree hd0 hd0'
  have hpt : z'.pileOfTop d.twin = z.pileOfTop d.twin :=
    pileOfTop_eq_of_agree hagree hdt0 hdt0'
  unfold freeCardS
  rw [hph_d]
  cases hhh : z.pileHolding d with
  | none => rfl
  | some a =>
      have ha0 : a ≠ a0 := by
        intro h; subst h; exact hd0 (pileHolding_mem hhh)
      simp only [hagree a ha0, hpt]

/-- **`(P)`, corrected (licensed) form.**  A licensed raise of a strictly higher
rank is **licence-inert** for a lower-ranked card. -/
theorem canRaiseS_inert_tabToFound_of_low_rank {z z' : State} {e d : Card}
    (hz : z.WF) (hstep : State.step z (Move.tabToFound e) = some z')
    (hcr : CanRaise z e) (hr : d.rank.toIdx < e.rank.toIdx) :
    CanRaiseS z' d ↔ CanRaiseS z d := by
  have hwz' : z'.WF := step_wf hz hstep
  have hnext := nextUp_tabToFound_eq_of_low_rank hstep hr
  have hfree := freeCardS_tabToFound_eq_of_low_rank hz hstep hcr hr
  rw [canRaiseS_split hwz', canRaiseS_split hz, hnext, hfree]

/-- **`(P)` at the step level.**  A licensed step (a cargo slide followed by a
licensed raise) of a strictly higher rank preserves a lower-ranked card's
licence, both ways. -/
theorem canRaiseS_inert_of_canRaiseStep {z z₀ z' : State} {e d : Card}
    (hz : z.WF) (hpath : CargoPath z z₀) (hcr : CanRaise z₀ e)
    (hstep : State.step z₀ (Move.tabToFound e) = some z')
    (hr : d.rank.toIdx < e.rank.toIdx) :
    CanRaiseS z' d ↔ CanRaiseS z d := by
  have hz₀ : z₀.WF := cargoPath_wf hz hpath
  have h1 : CanRaiseS z' d ↔ CanRaiseS z₀ d :=
    canRaiseS_inert_tabToFound_of_low_rank hz₀ hstep hcr hr
  have hround : CanRaiseS z d ↔ CanRaiseS z₀ d := by
    constructor
    · intro h
      exact (canRaiseS_orbit_rung hz (sameOrbit_of_cargoPath hpath)
        (rungAt_cargoPath hpath)).mp h
    · intro h
      exact (canRaiseS_orbit_rung hz₀
        (sameOrbitSetoid.iseqv.symm (sameOrbit_of_cargoPath hpath))
        (fun σ => (rungAt_cargoPath hpath σ).symm)).mp h
  exact h1.trans hround.symm

/-- **The un-raise transfer along a licensed word.**  If every card of the word
`B` has strictly higher rank than `x`, then `x`'s licence is *transferred
backwards* across the whole word. -/
theorem canRaiseS_unraise_word {s z : State} {B : List Card} {x : Card}
    (h : RaiseSSeqLicensed s B z) (hwf : s.WF)
    (hr : ∀ b ∈ B, x.rank.toIdx < b.rank.toIdx) :
    CanRaiseS z x → CanRaiseS s x := by
  revert hwf hr
  induction h with
  | nil => intro _ _ hc; exact hc
  | cons htail hS hp hs ih =>
      rename_i zz zz0 zz' cc wws
      intro hwf hr hc
      have hr' : ∀ b ∈ wws, x.rank.toIdx < b.rank.toIdx :=
        fun b hb => hr b (List.mem_cons_of_mem _ hb)
      have hcc : x.rank.toIdx < cc.rank.toIdx := hr cc (List.mem_cons_self ..)
      have hzwf : zz.WF := RaiseSSeqLicensed.wf htail hwf
      have hcr : CanRaise zz0 cc := canRaise_of_canRaiseS_of_step hzwf hS hp hs
      have hz : CanRaiseS zz x :=
        (canRaiseS_inert_of_canRaiseStep hzwf hp hcr hs hcc).mp hc
      exact ih hwf hr' hz

/-! ## §9. The inversion swap and the rank sort -/

/-- **Inversion swap** (the bubble-sort primitive).  A licensed play can swap
adjacent cards `x` then `y` when `y` has *strictly lower* rank: `y`'s licence at
the prefix endpoint is recovered from its licence after `x` by inertness
(`canRaiseS_unraise_word`), both are then licensed there, and the tail is
replayed from the swapped endpoint by (S) (`tail_transport`). -/
theorem swap_inversion {s z : State} {A T : List Card} {x y : Card}
    (hs : s.WF) (hr : y.rank.toIdx < x.rank.toIdx)
    (h : RaiseSSeqLicensed s (playWord (A ++ [x, y] ++ T)) z) :
    ∃ z', RaiseSSeqLicensed s (playWord (A ++ [y, x] ++ T)) z' := by
  obtain ⟨uy, hOld, hT⟩ :=
    RaiseSSeqLicensed.split_chron (A := A ++ [x, y]) (R := T) h
  obtain ⟨u, hA, hR⟩ := RaiseSSeqLicensed.split_chron (A := A) (R := [x, y]) hOld
  obtain ⟨ux, hx_play, hy_play⟩ := RaiseSSeqLicensed.split_chron (A := [x]) (R := [y]) hR
  have huwf : u.WF := hA.wf hs
  have hx : CanRaiseS u x := canRaiseS_of_raiseSSeqLicensed_head hx_play
  have hy' : CanRaiseS ux y := canRaiseS_of_raiseSSeqLicensed_head hy_play
  have hrne : x.rank ≠ y.rank := by intro hcon; rw [hcon] at hr; omega
  have hy : CanRaiseS u y := by
    refine canRaiseS_unraise_word hx_play huwf ?_ hy'
    intro b hb
    simp only [playWord, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.mem_singleton] at hb
    subst hb
    exact hr
  obtain ⟨u₁, hy_play'⟩ := raiseSSeqLicensed_step_of_canRaiseS hy
  have hstep_y : RaiseStepS u u₁ y := by
    obtain ⟨z1, z0, hnil, -, hp, hst⟩ := RaiseSSeqLicensed.step_s' hy_play'
    cases hnil
    exact ⟨z0, hp, hst⟩
  have hx₂ : CanRaiseS u₁ x :=
    canRaiseS_step_of_rank_ne huwf hstep_y (Ne.symm hrne) hx
  obtain ⟨u₂, hx_play'⟩ := raiseSSeqLicensed_step_of_canRaiseS hx₂
  have hNew : RaiseSSeqLicensed s (playWord (A ++ [y, x])) u₂ := by
    rw [show playWord (A ++ [y, x]) = playWord [y, x] ++ playWord A from
      playWord_append A [y, x]]
    have hyx : RaiseSSeqLicensed u (playWord [y, x]) u₂ := by
      have := RaiseSSeqLicensed.append hy_play' hx_play'
      simpa [playWord] using this
    exact RaiseSSeqLicensed.append hA hyx
  have hperm : (A ++ [x, y]).Perm (A ++ [y, x]) :=
    List.Perm.append_left A (List.Perm.swap y x [])
  obtain ⟨z', hz'⟩ := RaiseSSeqLicensed.tail_transport hs hOld hNew hperm hT
  refine ⟨z', ?_⟩
  have hfin := RaiseSSeqLicensed.append hNew hz'
  simpa [playWord, List.append_assoc] using hfin

/-- In a list that is ascending by rank, the head is below every member. -/
theorem asc_head_le_all : ∀ {l : List Card} {a : Card},
    (a :: l).Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) →
    ∀ x ∈ a :: l, a.rank.toIdx ≤ x.rank.toIdx
  | [], a, h, x, hx => by
      rw [List.mem_singleton] at hx
      subst hx
      omega
  | b :: t, a, h, x, hx => by
      have hab : a.rank.toIdx ≤ b.rank.toIdx :=
        (List.pairwise_cons.mp h).1 b (List.mem_cons_self ..)
      have ht : (b :: t).Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) :=
        (List.pairwise_cons.mp h).2
      rcases List.mem_cons.mp hx with rfl | hx'
      · omega
      · have := asc_head_le_all ht x hx'
        omega

/-- In an ascending list, a member of a prefix is below the element that
follows the prefix. -/
theorem asc_le_of_mem_append : ∀ {X Y : List Card} {b : Card},
    (X ++ b :: Y).Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) →
    ∀ x ∈ X, x.rank.toIdx ≤ b.rank.toIdx
  | [], Y, b, h, x, hx => absurd hx List.not_mem_nil
  | x :: X', Y, b, h, y, hy => by
      have hxb : x.rank.toIdx ≤ b.rank.toIdx :=
        (List.pairwise_cons.mp h).1 b (by simp)
      have htail : (X' ++ b :: Y).Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) :=
        (List.pairwise_cons.mp h).2
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact hxb
      · exact asc_le_of_mem_append htail y hy'

/-- A prefix of an ascending list is ascending. -/
theorem asc_append_left {l m : List Card}
    (h : (l ++ m).Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx)) :
    l.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons x t ih =>
      rw [List.cons_append] at h
      obtain ⟨hx, ht⟩ := List.pairwise_cons.mp h
      refine List.pairwise_cons.mpr ⟨?_, ih ht⟩
      intro z hz
      exact hx z (List.mem_append_left m hz)

/-- Erasing a card from an ascending list leaves it ascending. -/
theorem asc_erase : ∀ {l : List Card} {x : Card},
    l.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) →
    (l.erase x).Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx)
  | [], x, _ => List.Pairwise.nil
  | a :: t, x, h => by
      by_cases ha : a = x
      · subst ha
        rw [List.erase_cons_head]
        exact (List.pairwise_cons.mp h).2
      · rw [List.erase_cons_tail (by simp [ha])]
        obtain ⟨hx, ht⟩ := List.pairwise_cons.mp h
        refine List.pairwise_cons.mpr ⟨?_, asc_erase ht⟩
        intro z hz
        exact hx z (List.mem_of_mem_erase hz)

/-- Removing an element from the middle of an ascending list keeps it ascending. -/
theorem asc_erase_append {X Y : List Card} {b : Card}
    (h : (X ++ b :: Y).Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx)) :
    (X ++ Y).Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) := by
  induction X with
  | nil => exact (List.pairwise_cons.mp h).2
  | cons x X' ih =>
      rw [List.cons_append] at h
      obtain ⟨hx, htail⟩ := List.pairwise_cons.mp h
      refine List.pairwise_cons.mpr ⟨?_, ih htail⟩
      intro z hz
      rcases List.mem_append.mp hz with h1 | h2
      · exact hx z (List.mem_append_left _ h1)
      · exact hx z (List.mem_append_right _ (List.mem_cons_of_mem _ h2))

/-- The `insertByRank` membership read. -/
theorem mem_insertByRank : ∀ (a : Card) (L : List Card) (z : Card),
    z ∈ insertByRank a L ↔ z = a ∨ z ∈ L
  | a, [], z => by simp [insertByRank]
  | a, b :: t, z => by
      have hins : insertByRank a (b :: t) =
          if a.rank.toIdx ≤ b.rank.toIdx then a :: b :: t else b :: insertByRank a t := rfl
      rw [hins]
      by_cases h : a.rank.toIdx ≤ b.rank.toIdx
      · rw [ite_eq_left h]
        simp
      · rw [ite_eq_right h]
        simp only [List.mem_cons, mem_insertByRank a t z]
        constructor
        · rintro (rfl | rfl | hz)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr hz)
        · rintro (rfl | rfl | hz)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr hz)

/-- `insertByRank` is a permutation of the cons. -/
theorem insertByRank_perm (a : Card) : ∀ (L : List Card), (insertByRank a L).Perm (a :: L)
  | [] => by simp [insertByRank]
  | b :: t => by
      have hins : insertByRank a (b :: t) =
          if a.rank.toIdx ≤ b.rank.toIdx then a :: b :: t else b :: insertByRank a t := rfl
      rw [hins]
      by_cases h : a.rank.toIdx ≤ b.rank.toIdx
      · rw [ite_eq_left h]
      · rw [ite_eq_right h]
        exact ((insertByRank_perm a t).cons b).trans (List.Perm.swap b a t).symm

/-- `insertByRank` preserves ascendingness. -/
theorem insertByRank_asc {a : Card} : ∀ {L : List Card},
    L.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) →
    (insertByRank a L).Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx)
  | [], _ => List.pairwise_cons.mpr ⟨by simp, List.Pairwise.nil⟩
  | b :: t, h => by
      obtain ⟨hb, ht⟩ := List.pairwise_cons.mp h
      have hins : insertByRank a (b :: t) =
          if a.rank.toIdx ≤ b.rank.toIdx then a :: b :: t else b :: insertByRank a t := rfl
      rw [hins]
      by_cases hab : a.rank.toIdx ≤ b.rank.toIdx
      · rw [ite_eq_left hab]
        refine List.pairwise_cons.mpr ⟨?_, h⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz'
        · exact hab
        · exact Nat.le_trans hab (hb z hz')
      · rw [ite_eq_right hab]
        have hba : b.rank.toIdx ≤ a.rank.toIdx := by omega
        refine List.pairwise_cons.mpr ⟨?_, insertByRank_asc ht⟩
        intro z hz
        rcases (mem_insertByRank a t z).mp hz with rfl | hz'
        · exact hba
        · exact hb z hz'

/-- `sortByRank` is a permutation. -/
theorem sortByRank_perm : ∀ (P : List Card), (sortByRank P).Perm P
  | [] => List.Perm.nil
  | a :: t => (insertByRank_perm a (sortByRank t)).trans ((sortByRank_perm t).cons a)

/-- `sortByRank` is ascending. -/
theorem sortByRank_asc : ∀ (P : List Card),
    (sortByRank P).Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx)
  | [] => List.Pairwise.nil
  | a :: t => insertByRank_asc (sortByRank_asc t)

/-- A list is a permutation of its reversal. -/
theorem reverse_perm : ∀ (l : List Card), l.reverse.Perm l
  | [] => List.Perm.nil
  | a :: t => by
      rw [List.reverse_cons]
      refine ((reverse_perm t).append_right [a]).trans ?_
      induction t with
      | nil => exact List.Perm.refl _
      | cons y t ih =>
          have h1 : (y :: t ++ [a]).Perm (y :: (t ++ [a])) := List.Perm.refl _
          exact h1.trans ((ih.cons y).trans (List.Perm.swap y a t).symm)

/-! ## §10. The sorted play exists -/

/-- **Push a card into ascending place.**  If `c :: L` is a licensed play then
so is `insertByRank c L`. -/
theorem insertByRank_push {c : Card} :
    ∀ {s z : State} {L : List Card}, s.WF →
      RaiseSSeqLicensed s (playWord (c :: L)) z →
        ∃ z', RaiseSSeqLicensed s (playWord (insertByRank c L)) z' := by
  intro s z L
  induction L generalizing s z with
  | nil =>
      intro _ h
      exact ⟨z, by simpa [insertByRank, playWord] using h⟩
  | cons b L ih =>
      intro hs h
      by_cases hcb : c.rank.toIdx ≤ b.rank.toIdx
      · have hins : insertByRank c (b :: L) = c :: b :: L := by
          simp [insertByRank, hcb]
        rw [hins]
        exact ⟨z, h⟩
      · have hins : insertByRank c (b :: L) = b :: insertByRank c L := by
          simp [insertByRank, hcb]
        rw [hins]
        have hr : b.rank.toIdx < c.rank.toIdx := by omega
        obtain ⟨zs, hswap⟩ := swap_inversion (s := s) (z := z) (A := []) (T := L)
          (x := c) (y := b) hs hr (by simpa [playWord] using h)
        obtain ⟨s_b, h_b, hcL⟩ := RaiseSSeqLicensed.split_chron (A := [b]) (R := c :: L)
          (s := s) (z := zs) (by simpa [playWord] using hswap)
        obtain ⟨z₂, hz₂⟩ := ih (s := s_b) (z := zs) (RaiseSSeqLicensed.wf h_b hs) hcL
        refine ⟨z₂, ?_⟩
        have hfin := RaiseSSeqLicensed.append h_b hz₂
        simpa [playWord] using hfin

/-- **The sorted play exists whenever a licensed play exists.** -/
theorem sortable {P : List Card} :
    ∀ {s z : State}, s.WF → RaiseSSeqLicensed s (playWord P) z →
      ∃ z', RaiseSSeqLicensed s (playWord (sortByRank P)) z' := by
  induction P with
  | nil =>
      intro s z _ h
      exact ⟨z, by simpa [sortByRank] using h⟩
  | cons a P ih =>
      intro s z hs h
      obtain ⟨s_a, h_a, h'⟩ := RaiseSSeqLicensed.split_chron (A := [a]) (R := P) h
      have hsa : s_a.WF := RaiseSSeqLicensed.wf h_a hs
      obtain ⟨z₁, hz₁⟩ := ih hsa h'
      have hpre : RaiseSSeqLicensed s (playWord (a :: sortByRank P)) z₁ := by
        rw [show playWord (a :: sortByRank P) = playWord (sortByRank P) ++ [a] from by
          simp [playWord]]
        exact RaiseSSeqLicensed.append h_a hz₁
      have := insertByRank_push (c := a) (L := sortByRank P) hs hpre
      simpa [sortByRank] using this

/-- The sorted census row, in word form. -/
theorem raiseS_sorted_of_licensed {s z : State} {ws : List Card}
    (hs : s.WF) (h : RaiseSSeqLicensed s ws z) :
    ∃ z', RaiseSSeqLicensed s ((sortByRank ws.reverse).reverse) z' := by
  have h' : RaiseSSeqLicensed s (playWord ws.reverse) z := by simpa [playWord] using h
  obtain ⟨z', hz'⟩ := sortable (P := ws.reverse) hs h'
  exact ⟨z', hz'⟩

/-! ## §11. The equal-rank tie block -/

/-- `below` of a snoc is the prefix, provided the card is absent from it. -/
theorem below_append_singleton_of_not_mem : ∀ {l : List Card} {c : Card},
    c ∉ l → below c (l ++ [c]) = l
  | [], _, _ => by simp [below]
  | x :: t, c, h => by
      have hx : x ≠ c := fun hcon => h (by rw [hcon]; exact List.mem_cons_self ..)
      have ht : c ∉ t := fun hmem => h (List.mem_cons_of_mem _ hmem)
      show (if x = c then [] else x :: below c (t ++ [c])) = x :: t
      rw [ite_eq_right hx, below_append_singleton_of_not_mem ht]

/-- If `c` is absent from a prefix, appending `c` makes it the `fromCard`. -/
theorem fromCard_append_singleton_of_not_mem : ∀ {l : List Card} {c : Card},
    c ∉ l → fromCard c (l ++ [c]) = [c]
  | [], _, _ => by simp [fromCard]
  | x :: t, c, h => by
      have hx : x ≠ c := fun hcon => h (by rw [hcon]; exact List.mem_cons_self ..)
      have ht : c ∉ t := fun hmem => h (List.mem_cons_of_mem _ hmem)
      show (if x = c then x :: (t ++ [c]) else fromCard c (t ++ [c])) = [c]
      rw [ite_eq_right hx, fromCard_append_singleton_of_not_mem ht]

/-- If `fromCard c l` is the singleton, then `l` is a prefix followed by `c`. -/
theorem fromCard_singleton_decomp : ∀ {l : List Card} {c : Card},
    fromCard c l = [c] → ∃ bs, l = bs ++ [c]
  | [], _, h => by simp [fromCard] at h
  | x :: t, c, h => by
      by_cases hx : x = c
      · refine ⟨[], ?_⟩
        have hc : c :: t = [c] := by simpa [fromCard, hx] using h
        rwa [hx]
      · have h' : fromCard c t = [c] := by
          rw [show fromCard c (x :: t) = fromCard c t from by simp [fromCard, hx]] at h
          exact h
        obtain ⟨bs, hbs⟩ := fromCard_singleton_decomp h'
        exact ⟨x :: bs, by rw [hbs]; rfl⟩

/-- `a = c.twin` gives a different suit. -/
theorem suit_ne_of_twin {a c : Card} (h : a = c.twin) : c.suit ≠ a.suit := by
  rw [h]
  exact (Suit.twin_ne c.suit).symm

/-- A card of the same rank as the pile top cannot occur in that pile. -/
theorem not_mem_pileOfTop_of_rank_eq {z : State} (hz : z.WF) {e d : Card}
    {a : Anchor} (hpa : z.pileOfTop e = some a) (hr : d.rank = e.rank) (hde : d ≠ e) :
    d ∉ (z.piles a).faceUp := by
  intro hmem
  have hlast : lastOf (z.piles a).faceUp = some e := (pileOfTop_top hpa).2
  have hlt := rank_lt_of_mem_of_lastOf (hz.2.1 a) hlast hmem hde
  rw [hr] at hlt
  omega

/-- The twin of a card of the pile top's rank cannot occur in that pile either. -/
theorem not_mem_pileOfTop_twin_of_rank_eq {z : State} (hz : z.WF) {e d : Card}
    {a : Anchor} (hpa : z.pileOfTop e = some a) (hr : d.rank = e.rank)
    (hdt : d.twin ≠ e) :
    d.twin ∉ (z.piles a).faceUp := by
  intro hmem
  have hlast : lastOf (z.piles a).faceUp = some e := (pileOfTop_top hpa).2
  have hlt := rank_lt_of_mem_of_lastOf (hz.2.1 a) hlast hmem hdt
  have hrank : d.twin.rank.toIdx = e.rank.toIdx := by
    rw [Card.twin_rank, hr]
  rw [hrank] at hlt
  omega

/-- The flat data of `freeCardS`. -/
theorem freeCardS_unpack {st : State} {c : Card} (hfree : freeCardS st c = true) :
    ∃ p run, st.pileHolding c = some p ∧
      fromCard c ((st.piles p).faceUp) = c :: run ∧
      (below c ((st.piles p).faceUp) ≠ [] ∨
        ((st.piles p).hidden = [] ∧ c.rank = Rank.king)) ∧
      (run = [] ∨ st.pileOfTop c.twin ≠ none) := by
  unfold freeCardS at hfree
  split at hfree
  · exact absurd hfree (by simp)
  · rename_i p hhold
    split at hfree
    · exact absurd hfree (by simp)
    · rename_i head run hF0
      obtain ⟨run', hF'⟩ := tfc_fromCard_cons_head (l := (st.piles p).faceUp)
        (pileHolding_mem hhold)
      rw [hF'] at hF0
      injection hF0 with hhead hrun
      subst hhead
      subst hrun
      rw [Bool.and_eq_true] at hfree
      obtain ⟨hseat, hthird⟩ := hfree
      refine ⟨p, run', hhold, hF', ?_, ?_⟩
      · rw [Bool.or_eq_true] at hseat
        rcases hseat with h | h
        · exact Or.inl (of_decide_eq_true h)
        · rw [Bool.and_eq_true] at h
          exact Or.inr ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩
      · rw [Bool.or_eq_true] at hthird
        rcases hthird with h | h
        · exact Or.inl (of_decide_eq_true h)
        · exact Or.inr (Option.isSome_iff_ne_none.mp h)

/-- Repacking the flat data into `freeCardS`. -/
theorem freeCardS_of_data {st : State} {c : Card} {p : Anchor} {run : List Card}
    (hhold : st.pileHolding c = some p)
    (hF : fromCard c ((st.piles p).faceUp) = c :: run)
    (hseat : below c ((st.piles p).faceUp) ≠ [] ∨
      ((st.piles p).hidden = [] ∧ c.rank = Rank.king))
    (hthird : run = [] ∨ st.pileOfTop c.twin ≠ none) :
    freeCardS st c = true := by
  simp only [freeCardS, hhold, hF]
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [Bool.or_eq_true]
    rcases hseat with h | ⟨h1, h2⟩
    · exact Or.inl (decide_eq_true h)
    · exact Or.inr (by rw [Bool.and_eq_true]; exact ⟨decide_eq_true h1, decide_eq_true h2⟩)
  · rw [Bool.or_eq_true]
    rcases hthird with h | h
    · exact Or.inl (decide_eq_true h)
    · exact Or.inr (Option.isSome_iff_ne_none.mpr h)

/-- **Same-rank, non-twin: the tableau-readiness is unchanged by a licensed
raise.** -/
theorem freeCardS_tabToFound_eq_of_rank_eq_notTwin {z z' : State} {a c : Card}
    (hz : z.WF) (hstep : State.step z (Move.tabToFound a) = some z')
    (hcr : CanRaise z a) (hr : a.rank = c.rank) (hac : a ≠ c) (hat : a ≠ c.twin) :
    freeCardS z' c = freeCardS z c := by
  obtain ⟨-, a1, hpa1, hseat⟩ := hcr
  obtain ⟨a0, hpa0, hpiles⟩ := piles_tabToFound hstep
  have ha10 : a1 = a0 := Option.some.inj (hpa1.symm.trans hpa0)
  rw [ha10] at hseat
  have hwz' : z'.WF := step_wf hz hstep
  have hc0 : c ∉ (z.piles a0).faceUp :=
    not_mem_pileOfTop_of_rank_eq hz hpa0 hr.symm (Ne.symm hac)
  have hct0 : c.twin ∉ (z.piles a0).faceUp :=
    not_mem_pileOfTop_twin_of_rank_eq hz hpa0 hr.symm (Ne.symm hat)
  have hc0' : c ∉ (z'.piles a0).faceUp := by
    have hp0 : z'.piles a0 =
        Pile.afterRunRemoved (z.piles a0) (chop (z.piles a0).faceUp) := by
      rw [hpiles a0, ite_eq_left rfl]
    rw [hp0]
    rcases hseat with hne | ⟨hhid, -⟩
    · rw [afterRunRemoved_faceUp_ne hne]
      intro h; exact hc0 (chop_mem h)
    · by_cases hch : chop (z.piles a0).faceUp = []
      · rw [hch, afterRunRemoved_faceUp_bare hhid]; simp
      · rw [afterRunRemoved_faceUp_ne hch]
        intro h; exact hc0 (chop_mem h)
  have hct0' : c.twin ∉ (z'.piles a0).faceUp := by
    have hp0 : z'.piles a0 =
        Pile.afterRunRemoved (z.piles a0) (chop (z.piles a0).faceUp) := by
      rw [hpiles a0, ite_eq_left rfl]
    rw [hp0]
    rcases hseat with hne | ⟨hhid, -⟩
    · rw [afterRunRemoved_faceUp_ne hne]
      intro h; exact hct0 (chop_mem h)
    · by_cases hch : chop (z.piles a0).faceUp = []
      · rw [hch, afterRunRemoved_faceUp_bare hhid]; simp
      · rw [afterRunRemoved_faceUp_ne hch]
        intro h; exact hct0 (chop_mem h)
  have hagree : ∀ a', a' ≠ a0 → z'.piles a' = z.piles a' := by
    intro a' ha'
    rw [hpiles a', ite_eq_right ha']
  have hph : z'.pileHolding c = z.pileHolding c :=
    pileHolding_eq_of_agree hwz' hagree hc0 hc0'
  have hpt : z'.pileOfTop c.twin = z.pileOfTop c.twin :=
    pileOfTop_eq_of_agree hagree hct0 hct0'
  unfold freeCardS
  rw [hph]
  cases hhh : z.pileHolding c with
  | none => rfl
  | some a' =>
      have ha0 : a' ≠ a0 := by
        intro h; subst h; exact hc0 (pileHolding_mem hhh)
      simp only [hagree a' ha0, hpt]

/-- **Same-rank, non-twin: the licence transfers both ways.** -/
theorem canRaiseS_tabToFound_iff_of_rank_eq_notTwin {z z' : State} {a c : Card}
    (hz : z.WF) (hstep : State.step z (Move.tabToFound a) = some z')
    (hcr : CanRaise z a) (hr : a.rank = c.rank) (hac : a ≠ c) (hat : a ≠ c.twin) :
    CanRaiseS z' c ↔ CanRaiseS z c := by
  have hwz' : z'.WF := step_wf hz hstep
  have hsu : c.suit ≠ a.suit := by
    intro h
    exact hac (card_eq_of_suit_rank (c := c) (c' := a) h.symm (by rw [hr]))
  have hnext : z'.nextUp c = z.nextUp c := nextUp_raise_ne hstep hsu
  have hfree := freeCardS_tabToFound_eq_of_rank_eq_notTwin hz hstep hcr hr hac hat
  rw [canRaiseS_split hwz', canRaiseS_split hz, hnext, hfree]

/-- **The exposed read**: if `freeCardS st c` holds and `c.twin` is not a pile
top, then `c` is exposed (nothing sits above it in its pile). -/
theorem fromCard_nil_of_freeCardS_of_twin_none {st : State} {c : Card} {p : Anchor}
    (hhold : st.pileHolding c = some p) (hfree : freeCardS st c = true)
    (htwin : st.pileOfTop c.twin = none) :
    fromCard c ((st.piles p).faceUp) = [c] := by
  obtain ⟨p', run, hhold', hF, hseat, hthird⟩ := freeCardS_unpack hfree
  have hp : p' = p := by rw [hhold] at hhold'; exact (Option.some.inj hhold').symm
  subst hp
  rcases hthird with h | h
  · rw [h] at hF
    exact hF
  · rw [htwin] at h
    exact absurd h (by simp)

/-- **A licensed raise of a twin, backwards.** -/
theorem freeCardS_tabToFound_bwd_of_twin {z z' : State} {a c : Card}
    (hz : z.WF) (hstep : State.step z (Move.tabToFound a) = some z')
    (hcr : CanRaise z a) (ht : a = c.twin) :
    freeCardS z' c = true → freeCardS z c = true := by
  intro hfree'
  obtain ⟨-, a1, hpa1, hseat⟩ := hcr
  obtain ⟨a0, hpa0, hpiles⟩ := piles_tabToFound hstep
  have ha10 : a1 = a0 := Option.some.inj (hpa1.symm.trans hpa0)
  rw [ha10] at hseat
  have hwz' : z'.WF := step_wf hz hstep
  have hc0 : c ∉ (z.piles a0).faceUp := by
    apply not_mem_pileOfTop_of_rank_eq hz hpa0
    · rw [ht, Card.twin_rank]
    · intro h; exact (card_twin_ne c).symm (h.trans ht)
  have hc0' : c ∉ (z'.piles a0).faceUp := by
    have hp0 : z'.piles a0 =
        Pile.afterRunRemoved (z.piles a0) (chop (z.piles a0).faceUp) := by
      rw [hpiles a0, ite_eq_left rfl]
    rw [hp0]
    rcases hseat with hne | ⟨hhid, -⟩
    · rw [afterRunRemoved_faceUp_ne hne]
      intro h; exact hc0 (chop_mem h)
    · by_cases hch : chop (z.piles a0).faceUp = []
      · rw [hch, afterRunRemoved_faceUp_bare hhid]; simp
      · rw [afterRunRemoved_faceUp_ne hch]
        intro h; exact hc0 (chop_mem h)
  have hagree : ∀ a', a' ≠ a0 → z'.piles a' = z.piles a' := by
    intro a' ha'
    rw [hpiles a', ite_eq_right ha']
  have hph : z'.pileHolding c = z.pileHolding c :=
    pileHolding_eq_of_agree hwz' hagree hc0 hc0'
  have hfound : a ∈ z'.found a.suit := by
    rw [found_tabToFound hstep a.suit, ite_eq_left rfl]
    exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
  have htwinnone : z'.pileOfTop c.twin = none := by
    rw [← ht]
    exact pileOfTop_eq_none_of_found hwz' hfound
  obtain ⟨p', run, hhold', hF', hseat', hthird'⟩ := freeCardS_unpack hfree'
  have hholdz : z.pileHolding c = some p' := by rw [← hph]; exact hhold'
  have hexp' : fromCard c ((z'.piles p').faceUp) = [c] :=
    fromCard_nil_of_freeCardS_of_twin_none hhold' hfree' htwinnone
  have hpne : p' ≠ a0 := by
    intro h; subst h; exact hc0 (pileHolding_mem hholdz)
  have hpile : z.piles p' = z'.piles p' := (hagree p' hpne).symm
  have hexp : fromCard c ((z.piles p').faceUp) = [c] := by rw [hpile]; exact hexp'
  have hseat_z : below c ((z.piles p').faceUp) ≠ [] ∨
      ((z.piles p').hidden = [] ∧ c.rank = Rank.king) := by
    rcases hseat' with h | h
    · exact Or.inl (by rwa [hpile])
    · exact Or.inr ⟨by rw [hpile]; exact h.1, h.2⟩
  exact freeCardS_of_data hholdz hexp hseat_z (Or.inl rfl)

/-- **Same-rank twin, backward: the licence transfers back across the twin's
raise.** -/
theorem canRaiseS_tabToFound_bwd_of_twin {z z' : State} {a c : Card}
    (hz : z.WF) (hstep : State.step z (Move.tabToFound a) = some z')
    (hcr : CanRaise z a) (ht : a = c.twin) :
    CanRaiseS z' c → CanRaiseS z c := by
  intro hc
  have hwz' : z'.WF := step_wf hz hstep
  have hnext : z'.nextUp c = z.nextUp c := nextUp_raise_ne hstep (suit_ne_of_twin ht)
  have hsplit := (canRaiseS_split hwz').mp hc
  rw [canRaiseS_split hz]
  exact ⟨by rw [← hnext]; exact hsplit.1,
    freeCardS_tabToFound_bwd_of_twin hz hstep hcr ht hsplit.2⟩

/-- **A licensed raise of a twin, forwards, when the tracked card is exposed.** -/
theorem freeCardS_tabToFound_fwd_of_twin {z z' : State} {a c : Card} {p : Anchor}
    (hz : z.WF) (hstep : State.step z (Move.tabToFound a) = some z')
    (hcr : CanRaise z a) (ht : a = c.twin)
    (hhold : z.pileHolding c = some p)
    (hexp : fromCard c ((z.piles p).faceUp) = [c]) :
    freeCardS z c = true → freeCardS z' c = true := by
  intro hfree
  obtain ⟨-, a1, hpa1, hseat⟩ := hcr
  obtain ⟨a0, hpa0, hpiles⟩ := piles_tabToFound hstep
  have ha10 : a1 = a0 := Option.some.inj (hpa1.symm.trans hpa0)
  rw [ha10] at hseat
  have hwz' : z'.WF := step_wf hz hstep
  have hc0 : c ∉ (z.piles a0).faceUp := by
    apply not_mem_pileOfTop_of_rank_eq hz hpa0
    · rw [ht, Card.twin_rank]
    · intro h; exact (card_twin_ne c).symm (h.trans ht)
  have hc0' : c ∉ (z'.piles a0).faceUp := by
    have hp0 : z'.piles a0 =
        Pile.afterRunRemoved (z.piles a0) (chop (z.piles a0).faceUp) := by
      rw [hpiles a0, ite_eq_left rfl]
    rw [hp0]
    rcases hseat with hne | ⟨hhid, -⟩
    · rw [afterRunRemoved_faceUp_ne hne]
      intro h; exact hc0 (chop_mem h)
    · by_cases hch : chop (z.piles a0).faceUp = []
      · rw [hch, afterRunRemoved_faceUp_bare hhid]; simp
      · rw [afterRunRemoved_faceUp_ne hch]
        intro h; exact hc0 (chop_mem h)
  have hagree : ∀ a', a' ≠ a0 → z'.piles a' = z.piles a' := by
    intro a' ha'
    rw [hpiles a', ite_eq_right ha']
  have hph : z'.pileHolding c = z.pileHolding c :=
    pileHolding_eq_of_agree hwz' hagree hc0 hc0'
  obtain ⟨p', run, hhold', hF, hseat', hthird⟩ := freeCardS_unpack hfree
  have hp : p' = p := by rw [hhold] at hhold'; exact (Option.some.inj hhold').symm
  rw [hp] at hhold' hF hseat'
  have hpne : p ≠ a0 := by
    intro h; subst h; exact hc0 (pileHolding_mem hhold)
  have hpile : z'.piles p = z.piles p := hagree p hpne
  have hhold'' : z'.pileHolding c = some p := by rw [hph]; exact hhold'
  have hF' : fromCard c ((z'.piles p).faceUp) = c :: run := by rw [hpile]; exact hF
  have hrun : run = [] := by
    rw [hexp] at hF
    injection hF with _ h
    exact h.symm
  have hseat'' : below c ((z'.piles p).faceUp) ≠ [] ∨
      ((z'.piles p).hidden = [] ∧ c.rank = Rank.king) := by
    rcases hseat' with h | h
    · exact Or.inl (by rwa [hpile])
    · exact Or.inr ⟨by rw [hpile]; exact h.1, h.2⟩
  exact freeCardS_of_data hhold'' hF' hseat'' (Or.inl hrun)

/-- **Same-rank, non-twin licensed step: the licence transfers both ways.** -/
theorem canRaiseS_rankEq_notTwin_step_iff {z z₀ z' : State} {a c : Card}
    (hz : z.WF) (hpath : CargoPath z z₀) (hcr : CanRaise z₀ a)
    (hstep : State.step z₀ (Move.tabToFound a) = some z')
    (hr : a.rank = c.rank) (hac : a ≠ c) (hat : a ≠ c.twin) :
    CanRaiseS z' c ↔ CanRaiseS z c := by
  have hz₀ : z₀.WF := cargoPath_wf hz hpath
  exact (canRaiseS_tabToFound_iff_of_rank_eq_notTwin hz₀ hstep hcr hr hac hat).trans
    (canRaiseS_cargoPath_bicond hz hpath)

/-- **Same-rank twin licensed step, backward: the licence transfers back.** -/
theorem canRaiseS_rankEq_twin_step_bwd {z z₀ z' : State} {a c : Card}
    (hz : z.WF) (hpath : CargoPath z z₀) (hcr : CanRaise z₀ a)
    (hstep : State.step z₀ (Move.tabToFound a) = some z')
    (ht : a = c.twin) :
    CanRaiseS z' c → CanRaiseS z c := by
  have hz₀ : z₀.WF := cargoPath_wf hz hpath
  intro hc
  have h1 : CanRaiseS z₀ c :=
    canRaiseS_tabToFound_bwd_of_twin hz₀ hstep hcr ht hc
  exact (canRaiseS_cargoPath_bicond hz hpath).mp h1

/-- **Exposed + S-licensed ⇒ vanilla-licensed.** -/
theorem canRaise_of_canRaiseS_of_exposed {st : State} {c : Card} {p : Anchor}
    (hwf : st.WF) (hhold : st.pileHolding c = some p)
    (hexp : fromCard c ((st.piles p).faceUp) = [c])
    (hc : CanRaiseS st c) : CanRaise st c := by
  have hsplit := (canRaiseS_split hwf).mp hc
  have hnext := hsplit.1
  obtain ⟨-, hfree⟩ := hsplit
  obtain ⟨p', run, hhold', hF', hseat', hthird⟩ := freeCardS_unpack hfree
  have hp : p' = p := by rw [hhold] at hhold'; exact (Option.some.inj hhold').symm
  rw [hp] at hF' hseat'
  have hrun : run = [] := by
    rw [hexp] at hF'
    injection hF' with _ h
    exact h.symm
  subst hrun
  obtain ⟨bs, hbs⟩ := fromCard_singleton_decomp hexp
  have hnotmem : c ∉ bs := by
    intro hmem
    have hnodup : ((st.piles p).faceUp).Nodup := runOK_nodup (hwf.2.1 p)
    rw [hbs] at hnodup
    exact (List.nodup_append.mp hnodup).2.2 c hmem c (List.mem_singleton_self c) rfl
  have hchop : chop ((st.piles p).faceUp) = bs := by
    rw [hbs]; exact chop_append_singleton (l := bs) (c := c)
  have hbelow : below c ((st.piles p).faceUp) = bs := by
    rw [hbs]; exact below_append_singleton_of_not_mem hnotmem
  have htop : (st.piles p).top = some c := by
    show lastOf ((st.piles p).faceUp) = some c
    rw [hbs]; exact lastOf_snoc
  refine ⟨hnext, p, ?_, ?_⟩
  · exact (pileOfTop_eq_some_iff hwf).mpr htop
  · rw [hbelow] at hseat'
    rw [hchop]
    exact hseat'

/-- The pile geometry around a licensed raise of `c.twin`. -/
theorem twinStep_piles {z z' : State} {a c : Card}
    (hz : z.WF) (hstep : State.step z (Move.tabToFound a) = some z')
    (hcr : CanRaise z a) (ht : a = c.twin) :
    ∃ a0, z.pileOfTop a = some a0 ∧
      c ∉ (z.piles a0).faceUp ∧ c ∉ (z'.piles a0).faceUp ∧
      (∀ a', a' ≠ a0 → z'.piles a' = z.piles a') ∧
      z'.pileHolding c = z.pileHolding c := by
  obtain ⟨-, a1, hpa1, hseat⟩ := hcr
  obtain ⟨a0, hpa0, hpiles⟩ := piles_tabToFound hstep
  have ha10 : a1 = a0 := Option.some.inj (hpa1.symm.trans hpa0)
  rw [ha10] at hseat
  have hwz' : z'.WF := step_wf hz hstep
  have hc0 : c ∉ (z.piles a0).faceUp := by
    apply not_mem_pileOfTop_of_rank_eq hz hpa0
    · rw [ht, Card.twin_rank]
    · intro h; exact (card_twin_ne c).symm (h.trans ht)
  have hc0' : c ∉ (z'.piles a0).faceUp := by
    have hp0 : z'.piles a0 =
        Pile.afterRunRemoved (z.piles a0) (chop (z.piles a0).faceUp) := by
      rw [hpiles a0, ite_eq_left rfl]
    rw [hp0]
    rcases hseat with hne | ⟨hhid, -⟩
    · rw [afterRunRemoved_faceUp_ne hne]
      intro h; exact hc0 (chop_mem h)
    · by_cases hch : chop (z.piles a0).faceUp = []
      · rw [hch, afterRunRemoved_faceUp_bare hhid]; simp
      · rw [afterRunRemoved_faceUp_ne hch]
        intro h; exact hc0 (chop_mem h)
  have hagree : ∀ a', a' ≠ a0 → z'.piles a' = z.piles a' := by
    intro a' ha'
    rw [hpiles a', ite_eq_right ha']
  exact ⟨a0, hpa0, hc0, hc0', hagree,
    pileHolding_eq_of_agree hwz' hagree hc0 hc0'⟩

/-- **Exposure transfers backwards across a twin raise.** -/
theorem exposed_bwd_of_twin_step {z z' : State} {a c : Card}
    (hz : z.WF) (hstep : State.step z (Move.tabToFound a) = some z')
    (hcr : CanRaise z a) (ht : a = c.twin) (hc : CanRaiseS z' c) :
    ∃ p, z.pileHolding c = some p ∧ fromCard c ((z.piles p).faceUp) = [c] := by
  have hwz' : z'.WF := step_wf hz hstep
  obtain ⟨-, hfree⟩ := (canRaiseS_split hwz').mp hc
  obtain ⟨p, run, hhold', hF, hseat', hthird⟩ := freeCardS_unpack hfree
  have hfound : a ∈ z'.found a.suit := by
    rw [found_tabToFound hstep a.suit, ite_eq_left rfl]
    exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
  have htwinnone : z'.pileOfTop c.twin = none := by
    rw [← ht]
    exact pileOfTop_eq_none_of_found hwz' hfound
  have hexp' : fromCard c ((z'.piles p).faceUp) = [c] :=
    fromCard_nil_of_freeCardS_of_twin_none hhold' hfree htwinnone
  obtain ⟨a0, -, hc0, -, hagree, hph⟩ := twinStep_piles hz hstep hcr ht
  have hhold : z.pileHolding c = some p := by rw [← hph]; exact hhold'
  have hpne : p ≠ a0 := by
    intro h; subst h; exact hc0 (pileHolding_mem hhold)
  exact ⟨p, hhold, by rw [← hagree p hpne]; exact hexp'⟩

/-- A vanilla licence of `a` survives a vanilla raise of a *different card of the
same rank*. -/
theorem canRaise_of_raise_sameRank {z z' : State} {a c : Card}
    (hz : z.WF) (hstep : State.step z (Move.tabToFound c) = some z')
    (hr : a.rank = c.rank) (hac : a ≠ c) (ha : CanRaise z a) :
    CanRaise z' a := by
  have hwz' : z'.WF := step_wf hz hstep
  obtain ⟨hnext, pa, hpa, hseat⟩ := ha
  obtain ⟨a0, hpa0, hpiles⟩ := piles_tabToFound hstep
  have hsu : a.suit ≠ c.suit := by
    intro h
    exact hac (card_eq_of_suit_rank (c := c) (c' := a) h (by rw [hr]))
  have hnext' : z'.nextUp a = true := by
    rw [nextUp_raise_ne hstep hsu]
    exact hnext
  have hae : a ∉ (z.piles a0).faceUp :=
    not_mem_pileOfTop_of_rank_eq hz hpa0 hr hac
  have hpane : pa ≠ a0 := by
    intro h
    subst h
    exact hae (Pile.mem_of_top
      (show (z.piles pa).top = some a from (pileOfTop_top hpa).2))
  have hpile : z'.piles pa = z.piles pa := by
    rw [hpiles pa, ite_eq_right hpane]
  refine ⟨hnext', pa, ?_, ?_⟩
  · have htop : (z'.piles pa).top = some a := by
      rw [hpile]
      exact (pileOfTop_top hpa).2
    exact (pileOfTop_eq_some_iff hwz').mpr htop
  · rw [hpile]
    exact hseat

/-! ## §12. The equal-rank tie swap -/

/-- **Tie swap.**  Two adjacent raises of the *same rank* in a licensed play can
be performed in the other order (with the rest of the play replayed).

The non-twin case is the flat licence transfer of §11.  In the twin case we
un-raise the twin to expose `c` at the vanilla witness `z₀` of the first step;
there both raises are vanilla, so `twin_raise_square` commutes them exactly. -/
theorem tie_swap {u z : State} {a c : Card} {T : List Card}
    (hu : u.WF) (h : RaiseSSeqLicensed u (playWord (a :: c :: T)) z)
    (hr : a.rank = c.rank) (hac : a ≠ c) :
    ∃ z', RaiseSSeqLicensed u (playWord (c :: a :: T)) z' := by
  obtain ⟨u_ac, h_old, hT⟩ := RaiseSSeqLicensed.split_chron (A := [a, c]) (R := T) h
  obtain ⟨u_a, h_a, h_c⟩ := RaiseSSeqLicensed.split_chron (A := [a]) (R := [c]) h_old
  have hc_ua : CanRaiseS u_a c := canRaiseS_of_raiseSSeqLicensed_head h_c
  have ha_u : CanRaiseS u a := canRaiseS_of_raiseSSeqLicensed_head h_a
  obtain ⟨w0, z₀, hnil, hpath, hcr, hstep⟩ := RaiseSSeqLicensed.step_s h_a hu
  cases hnil
  have hz₀ : z₀.WF := cargoPath_wf hu hpath
  have hperm : ([a, c] : List Card).Perm [c, a] := by
    simpa using (List.Perm.swap c a ([] : List Card))
  by_cases hat : a = c.twin
  · have hc_z₀ : CanRaiseS z₀ c :=
      canRaiseS_tabToFound_bwd_of_twin hz₀ hstep hcr hat hc_ua
    obtain ⟨p, hhold, hexp⟩ := exposed_bwd_of_twin_step hz₀ hstep hcr hat hc_ua
    have hcvan : CanRaise z₀ c :=
      canRaise_of_canRaiseS_of_exposed hz₀ hhold hexp hc_z₀
    obtain ⟨v, hstep_c⟩ := step_tabToFound_of_canRaise hcvan
    have hsu : c.suit ≠ a.suit := suit_ne_of_twin hat
    obtain ⟨w', hstep_v_a, -⟩ := twin_raise_square hz₀ hsu hstep_c hstep
    have ha_v : CanRaise v a := canRaise_of_raise_sameRank hz₀ hstep_c hr hac hcr
    have hNew : RaiseSSeqLicensed u (playWord [c, a]) w' := by
      have h1 : RaiseSSeqLicensed u (playWord [c]) v :=
        RaiseSSeqLicensed.cons (RaiseSSeqLicensed.nil u) ⟨z₀, hpath, hcvan⟩ hpath hstep_c
      have h2 : RaiseSSeqLicensed v (playWord [a]) w' :=
        RaiseSSeqLicensed.cons (RaiseSSeqLicensed.nil v) ⟨v, Steps.refl v, ha_v⟩
          (Steps.refl v) hstep_v_a
      simpa [playWord] using RaiseSSeqLicensed.append h1 h2
    obtain ⟨z', hz'⟩ := RaiseSSeqLicensed.tail_transport hu h_old hNew hperm hT
    exact ⟨z', by simpa [playWord] using RaiseSSeqLicensed.append hNew hz'⟩
  · have hc_u : CanRaiseS u c :=
      (canRaiseS_rankEq_notTwin_step_iff hu hpath hcr hstep hr hac hat).mp hc_ua
    obtain ⟨u_c, h_c'⟩ := raiseSSeqLicensed_step_of_canRaiseS hc_u
    obtain ⟨w1, z1, hnil2, hpath2, hcr2, hstep2⟩ := RaiseSSeqLicensed.step_s h_c' hu
    cases hnil2
    have hat2 : c ≠ a.twin := by
      intro hcon
      exact hat (by rw [hcon, card_twin_twin])
    have hc2 : CanRaiseS u_c a :=
      (canRaiseS_rankEq_notTwin_step_iff hu hpath2 hcr2 hstep2 hr.symm
        (Ne.symm hac) hat2).mpr ha_u
    obtain ⟨u_ca, h_a'⟩ := raiseSSeqLicensed_step_of_canRaiseS hc2
    have hNew : RaiseSSeqLicensed u (playWord [c, a]) u_ca := by
      simpa [playWord] using RaiseSSeqLicensed.append h_c' h_a'
    obtain ⟨z', hz'⟩ := RaiseSSeqLicensed.tail_transport hu h_old hNew hperm hT
    exact ⟨z', by simpa [playWord] using RaiseSSeqLicensed.append hNew hz'⟩

/-! ## §13. Passing a strictly lower-rank card -/

/-- **Ascending swap.**  A licensed play beginning `y, c` with `y` strictly
lower-ranked can be rearranged to begin `c, y`, provided `c` is licensed at the
start: `y`'s licence survives `c`'s raise by inertness. -/
theorem asc_swap {u z : State} {y c : Card} {T : List Card}
    (hu : u.WF) (h : RaiseSSeqLicensed u (playWord (y :: c :: T)) z)
    (hr : y.rank.toIdx < c.rank.toIdx) (hc : CanRaiseS u c) :
    ∃ z', RaiseSSeqLicensed u (playWord (c :: y :: T)) z' := by
  obtain ⟨u_yc, h_old, hT⟩ := RaiseSSeqLicensed.split_chron (A := [y, c]) (R := T) h
  obtain ⟨u_y, h_y, h_c⟩ := RaiseSSeqLicensed.split_chron (A := [y]) (R := [c]) h_old
  have hy_u : CanRaiseS u y := canRaiseS_of_raiseSSeqLicensed_head h_y
  obtain ⟨u_c, h_c'⟩ := raiseSSeqLicensed_step_of_canRaiseS hc
  obtain ⟨w1, z1, hnil2, hpath2, hcr2, hstep2⟩ := RaiseSSeqLicensed.step_s h_c' hu
  cases hnil2
  have hy_uc : CanRaiseS u_c y :=
    (canRaiseS_inert_of_canRaiseStep hu hpath2 hcr2 hstep2 hr).mpr hy_u
  obtain ⟨u_cy, h_y'⟩ := raiseSSeqLicensed_step_of_canRaiseS hy_uc
  have hNew : RaiseSSeqLicensed u (playWord [c, y]) u_cy := by
    simpa [playWord] using RaiseSSeqLicensed.append h_c' h_y'
  have hperm : ([y, c] : List Card).Perm [c, y] := by
    simpa using (List.Perm.swap c y ([] : List Card))
  obtain ⟨z', hz'⟩ := RaiseSSeqLicensed.tail_transport hu h_old hNew hperm hT
  exact ⟨z', by simpa [playWord] using RaiseSSeqLicensed.append hNew hz'⟩

/-! ## §14. Moving the front card through a prefix -/

/-- Move `c` to the front of a same-rank block `B` that precedes it. -/
theorem bubble_tie (B : List Card) :
    ∀ {u z : State} {c : Card} {T : List Card},
      u.WF → c ∉ B → (∀ b ∈ B, b.rank = c.rank) →
      RaiseSSeqLicensed u (playWord (B ++ c :: T)) z →
      ∃ z', RaiseSSeqLicensed u (playWord (c :: B ++ T)) z' := by
  induction B with
  | nil =>
      intro u z c T hu _ _ h
      exact ⟨z, by simpa using h⟩
  | cons b B ih =>
      intro u z c T hu hcB hB h
      have hcb : b ≠ c := by
        intro hcon; exact hcB (by rw [hcon]; exact List.mem_cons_self ..)
      have hcB' : c ∉ B := fun hmem => hcB (List.mem_cons_of_mem _ hmem)
      have hb : b.rank = c.rank := hB b (List.mem_cons_self ..)
      have hB' : ∀ b' ∈ B, b'.rank = c.rank :=
        fun b' hb' => hB b' (List.mem_cons_of_mem _ hb')
      obtain ⟨u_b, h_b, hrest⟩ :=
        RaiseSSeqLicensed.split_chron (A := [b]) (R := B ++ c :: T) (by simpa using h)
      obtain ⟨z₁, hz₁⟩ := ih (u := u_b) (z := z) (c := c) (T := T)
        (RaiseSSeqLicensed.wf h_b hu) hcB' hB' hrest
      have hplay : RaiseSSeqLicensed u (playWord (b :: c :: (B ++ T))) z₁ := by
        have h1 := RaiseSSeqLicensed.append h_b hz₁
        simpa [playWord, List.append_assoc] using h1
      obtain ⟨z', hz'⟩ := tie_swap hu hplay hb hcb
      exact ⟨z', by simpa [playWord, List.append_assoc] using hz'⟩

/-- **Bubble the front card.**  In an ascending play whose prefix `A` has ranks
at most `c.rank`, the card `c` can be raised first (and the rest replayed). -/
theorem bubble_front (A : List Card) :
    ∀ {u z : State} {c : Card} {T : List Card},
      u.WF → A.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) → c ∉ A →
      (∀ a ∈ A, a.rank.toIdx ≤ c.rank.toIdx) → CanRaiseS u c →
      RaiseSSeqLicensed u (playWord (A ++ c :: T)) z →
      ∃ z', RaiseSSeqLicensed u (playWord (c :: A ++ T)) z' := by
  induction A with
  | nil =>
      intro u z c T hu _ _ _ _ h
      exact ⟨z, by simpa using h⟩
  | cons a A ih =>
      intro u z c T hu hAsc hcA hA hc h
      have hal : a.rank.toIdx ≤ c.rank.toIdx := hA a (List.mem_cons_self ..)
      by_cases hlt : a.rank.toIdx < c.rank.toIdx
      · obtain ⟨u_a, h_a, hrest⟩ :=
          RaiseSSeqLicensed.split_chron (A := [a]) (R := A ++ c :: T) (by simpa using h)
        have hAsc' : A.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) :=
          (List.pairwise_cons.mp hAsc).2
        have hcA' : c ∉ A := fun hmem => hcA (List.mem_cons_of_mem _ hmem)
        have hA' : ∀ a' ∈ A, a'.rank.toIdx ≤ c.rank.toIdx :=
          fun a' ha' => hA a' (List.mem_cons_of_mem _ ha')
        obtain ⟨w0, z₀, hnil, hpath, hcr, hstep⟩ := RaiseSSeqLicensed.step_s h_a hu
        cases hnil
        have hc_a : CanRaiseS u_a c :=
          canRaiseS_step_of_rank_ne hu ⟨z₀, hpath, hstep⟩
            (fun hcon => by rw [hcon] at hlt; omega) hc
        obtain ⟨z₁, hz₁⟩ := ih (u := u_a) (z := z) (c := c) (T := T)
          (RaiseSSeqLicensed.wf h_a hu) hAsc' hcA' hA' hc_a hrest
        have hplay : RaiseSSeqLicensed u (playWord (a :: c :: (A ++ T))) z₁ := by
          have h1 := RaiseSSeqLicensed.append h_a hz₁
          simpa [playWord, List.append_assoc] using h1
        obtain ⟨z', hz'⟩ := asc_swap hu hplay hlt hc
        exact ⟨z', by simpa [playWord, List.append_assoc] using hz'⟩
      · have hae : a.rank = c.rank := Rank.toIdx_inj (by omega)
        have hAll : ∀ b ∈ a :: A, b.rank = c.rank := by
          intro b hb
          have h1 : a.rank.toIdx ≤ b.rank.toIdx := asc_head_le_all hAsc b hb
          have h2 : b.rank.toIdx ≤ c.rank.toIdx := hA b hb
          have h3 : a.rank.toIdx = c.rank.toIdx := by rw [hae]
          exact Rank.toIdx_inj (by omega)
        exact bubble_tie (a :: A) hu hcA hAll h

/-! ## §15. Any two ascending orders of a multiset are interchangeable -/

theorem tieFree_aux (n : Nat) : ∀ (A : List Card), A.length ≤ n →
    ∀ {u z : State} {B : List Card}, u.WF →
      A.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) →
      B.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) → A.Perm B →
      RaiseSSeqLicensed u (playWord A) z → ∃ z', RaiseSSeqLicensed u (playWord B) z' := by
  induction n with
  | zero =>
      intro A hlen u z B hu hA hB hperm hplay
      cases A with
      | nil =>
          cases B with
          | nil => exact ⟨z, by simpa using hplay⟩
          | cons b B' => exact absurd hperm (by simp)
      | cons a A' => simp at hlen
  | succ n ih =>
      intro A hlen u z B hu hA hB hperm hplay
      cases A with
      | nil =>
          cases B with
          | nil => exact ⟨z, by simpa using hplay⟩
          | cons b B' => exact absurd hperm (by simp)
      | cons a A' =>
          cases B with
          | nil => exact absurd hperm (by simp)
          | cons b B' =>
              have hbA : b ∈ a :: A' := hperm.mem_iff.mpr (List.mem_cons_self ..)
              obtain ⟨X, Y, hXY, hbX⟩ := exists_append_cons_of_mem hbA
              have hAscX : (X ++ b :: Y).Pairwise
                  (fun a b => a.rank.toIdx ≤ b.rank.toIdx) := by
                rw [← hXY]; exact hA
              have hb_le_a : b.rank.toIdx ≤ a.rank.toIdx :=
                asc_head_le_all hB a (hperm.mem_iff.mp (List.mem_cons_self ..))
              have hXr : ∀ x ∈ X, x.rank = b.rank := by
                intro x hx
                have h1 : x.rank.toIdx ≤ b.rank.toIdx := asc_le_of_mem_append hAscX x hx
                have h2 : a.rank.toIdx ≤ x.rank.toIdx :=
                  asc_head_le_all hA x (by rw [hXY]; exact List.mem_append_left _ hx)
                exact Rank.toIdx_inj (by omega)
              have hplayX : RaiseSSeqLicensed u (playWord (X ++ b :: Y)) z := by
                rw [← hXY]; exact hplay
              obtain ⟨z₁, hz₁⟩ := bubble_tie X hu hbX hXr hplayX
              obtain ⟨u_b, h_b, hrest⟩ :=
                RaiseSSeqLicensed.split_chron (A := [b]) (R := X ++ Y) (by simpa using hz₁)
              have hAscXY : (X ++ Y).Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) :=
                asc_erase_append hAscX
              have hpermXY : B'.Perm (X ++ Y) := by
                have hp' : (b :: B').Perm (X ++ b :: Y) := by rw [← hXY]; exact hperm.symm
                have h1 : ((b :: B').erase b).Perm ((X ++ b :: Y).erase b) :=
                  perm_erase (x := b) hp'
                rwa [List.erase_cons_head, erase_append_cons_of_not_mem hbX] at h1
              have hlenXY : (X ++ Y).length ≤ n := by
                have h1 : (X ++ b :: Y).length = (a :: A').length := by rw [← hXY]
                have hlen' : A'.length ≤ n := by
                  simp only [List.length_cons] at hlen
                  omega
                simp only [List.length_append, List.length_cons] at h1 ⊢
                omega
              obtain ⟨z₂, hz₂⟩ := ih (X ++ Y) hlenXY (u := u_b) (z := z₁) (B := B')
                (RaiseSSeqLicensed.wf h_b hu) hAscXY (List.pairwise_cons.mp hB).2
                hpermXY.symm hrest
              refine ⟨z₂, ?_⟩
              have hfin := RaiseSSeqLicensed.append h_b hz₂
              simpa [playWord] using hfin

/-- **Tie freedom.**  Any two ascending orders of the same multiset are
interchangeable as licensed plays. -/
theorem tieFree {u z : State} {A B : List Card}
    (hu : u.WF)
    (hA : A.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx))
    (hB : B.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx))
    (hperm : A.Perm B)
    (hplay : RaiseSSeqLicensed u (playWord A) z) :
    ∃ z', RaiseSSeqLicensed u (playWord B) z' :=
  tieFree_aux A.length A (Nat.le_refl _) hu hA hB hperm hplay

/-! ## §16. Tail existence and the rank-front theorem -/

/-- **`tail_exists`** — raising a licensed card `c` first leaves the sorted
rest of the raised multiset playable.  This is the last residual of the
rank-front lane, now a theorem. -/
theorem tail_exists {s z : State} {ws : List Card} {c : Card}
    (hs : s.WF) (hc : CanRaiseS s c) (hplay : RaiseSSeqLicensed s ws z)
    (hmem : c ∈ ws) :
    ∃ s₁, RaiseSSeqLicensed s [c] s₁ ∧
      ∃ z', RaiseSSeqLicensed s₁ (playWord (sortByRank (ws.erase c))) z' := by
  have hplay' : RaiseSSeqLicensed s (playWord ws.reverse) z := by simpa [playWord] using hplay
  obtain ⟨z₁, hz₁⟩ := sortable (P := ws.reverse) hs hplay'
  have hc_mem : c ∈ sortByRank ws.reverse :=
    (sortByRank_perm ws.reverse).mem_iff.mpr (by simpa using hmem)
  obtain ⟨A, B, hAB, hcA⟩ := exists_append_cons_of_mem hc_mem
  have hAsc : (sortByRank ws.reverse).Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) :=
    sortByRank_asc _
  have hAscA : A.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) := by
    rw [hAB] at hAsc; exact asc_append_left hAsc
  have hAle : ∀ a ∈ A, a.rank.toIdx ≤ c.rank.toIdx := by
    rw [hAB] at hAsc
    exact fun a ha => asc_le_of_mem_append hAsc a ha
  have hplayA : RaiseSSeqLicensed s (playWord (A ++ c :: B)) z₁ := by rw [← hAB]; exact hz₁
  obtain ⟨z₂, hz₂⟩ := bubble_front A hs hAscA hcA hAle hc hplayA
  obtain ⟨s₁, h_c, hrest⟩ :=
    RaiseSSeqLicensed.split_chron (A := [c]) (R := A ++ B)
      (by simpa [playWord, List.append_assoc] using hz₂)
  refine ⟨s₁, h_c, ?_⟩
  have hs₁ : s₁.WF := RaiseSSeqLicensed.wf h_c hs
  have hAscAB : (A ++ B).Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) := by
    have h1 : A ++ B = (sortByRank ws.reverse).erase c := by
      rw [hAB, erase_append_cons_of_not_mem hcA]
    rw [h1]
    exact asc_erase hAsc
  have hpermAB : (A ++ B).Perm (sortByRank (ws.erase c)) := by
    have h1 : A ++ B = (sortByRank ws.reverse).erase c := by
      rw [hAB, erase_append_cons_of_not_mem hcA]
    rw [h1]
    have e1 : ((sortByRank ws.reverse).erase c).Perm ((ws.reverse).erase c) :=
      perm_erase (sortByRank_perm ws.reverse)
    have e2 : ((ws.reverse).erase c).Perm (ws.erase c) := perm_erase (reverse_perm ws)
    have e3 : (ws.erase c).Perm ((ws.erase c).reverse) := (reverse_perm (ws.erase c)).symm
    have e4 : ((ws.erase c).reverse).Perm (sortByRank (ws.erase c)) :=
      (reverse_perm (ws.erase c)).trans (sortByRank_perm (ws.erase c)).symm
    exact e1.trans (e2.trans (e3.trans e4))
  obtain ⟨z₃, hz₃⟩ := tieFree hs₁ hAscAB (sortByRank_asc (ws.erase c)) hpermAB hrest
  exact ⟨z₃, hz₃⟩

/-- **The rank-front theorem** (licensed grade), from `tail_exists`. -/
theorem raiseS_rankfront_L {s z : State} {c : Card} {ws : List Card}
    (hs : s.WF) (hc : CanRaiseS s c) (hplay : RaiseSSeqLicensed s ws z)
    (hmem : c ∈ ws) :
    ∃ z', RaiseSSeqLicensed s (rankFrontWord c ws) z' := by
  obtain ⟨s₁, hstep, z', htail⟩ := tail_exists hs hc hplay hmem
  refine ⟨z', ?_⟩
  have hfin : RaiseSSeqLicensed s (playWord (sortByRank (ws.erase c)) ++ [c]) z' :=
    RaiseSSeqLicensed.append hstep htail
  rwa [show playWord (sortByRank (ws.erase c)) ++ [c] = rankFrontWord c ws from by
    simp [rankFrontWord, playWord]] at hfin

/-- **THE RANK-FRONT THEOREM** — the card's `RankFront`, verbatim. -/
theorem rankFront_holds : RankFront := by
  intro s c hs hc ws z hplay hmem
  exact raiseS_rankfront_L hs hc hplay hmem

end OneColourClosure

#print axioms OneColourClosure.tie_swap
#print axioms OneColourClosure.asc_swap
#print axioms OneColourClosure.bubble_tie
#print axioms OneColourClosure.bubble_front
#print axioms OneColourClosure.tieFree_aux
#print axioms OneColourClosure.tieFree
#print axioms OneColourClosure.tail_exists
#print axioms OneColourClosure.raiseS_rankfront_L
#print axioms OneColourClosure.rankFront_holds
#print axioms OneColourClosure.cover_must_be_raised
#print axioms OneColourClosure.canRaiseS_of_raise_perm

#print axioms OneColourClosure.sortable
#print axioms OneColourClosure.raiseS_sorted_of_licensed
#print axioms OneColourClosure.below_append_singleton_of_not_mem
#print axioms OneColourClosure.fromCard_singleton_decomp
#print axioms OneColourClosure.freeCardS_unpack
#print axioms OneColourClosure.freeCardS_of_data
#print axioms OneColourClosure.freeCardS_tabToFound_eq_of_rank_eq_notTwin
#print axioms OneColourClosure.canRaiseS_tabToFound_iff_of_rank_eq_notTwin
#print axioms OneColourClosure.fromCard_nil_of_freeCardS_of_twin_none
#print axioms OneColourClosure.freeCardS_tabToFound_bwd_of_twin
#print axioms OneColourClosure.canRaiseS_tabToFound_bwd_of_twin
#print axioms OneColourClosure.freeCardS_tabToFound_fwd_of_twin
#print axioms OneColourClosure.canRaiseS_rankEq_notTwin_step_iff
#print axioms OneColourClosure.canRaiseS_rankEq_twin_step_bwd
#print axioms OneColourClosure.canRaise_of_canRaiseS_of_exposed
#print axioms OneColourClosure.twinStep_piles
#print axioms OneColourClosure.exposed_bwd_of_twin_step
#print axioms OneColourClosure.canRaise_of_raise_sameRank
#print axioms OneColourClosure.not_mem_pileOfTop_of_rank_lt
#print axioms OneColourClosure.not_mem_pileOfTop_twin_of_rank_lt
#print axioms OneColourClosure.pileHolding_eq_of_agree
#print axioms OneColourClosure.pileOfTop_eq_of_agree
#print axioms OneColourClosure.nextUp_tabToFound_eq_of_low_rank
#print axioms OneColourClosure.freeCardS_tabToFound_eq_of_low_rank
#print axioms OneColourClosure.canRaiseS_inert_tabToFound_of_low_rank
#print axioms OneColourClosure.canRaiseS_inert_of_canRaiseStep
#print axioms OneColourClosure.canRaiseS_unraise_word
#print axioms OneColourClosure.swap_inversion
#print axioms OneColourClosure.asc_head_le_all
#print axioms OneColourClosure.asc_le_of_mem_append
#print axioms OneColourClosure.asc_append_left
#print axioms OneColourClosure.asc_erase
#print axioms OneColourClosure.asc_erase_append
#print axioms OneColourClosure.mem_insertByRank
#print axioms OneColourClosure.insertByRank_perm
#print axioms OneColourClosure.insertByRank_asc
#print axioms OneColourClosure.sortByRank_perm
#print axioms OneColourClosure.sortByRank_asc
#print axioms OneColourClosure.reverse_perm

/-! ## §17. The battery (rest of the deck) -/

#print axioms OneColourClosure.playWord_nil
#print axioms OneColourClosure.playWord_append
#print axioms OneColourClosure.playWord_snoc
#print axioms OneColourClosure.cargoLeg_rungAt
#print axioms OneColourClosure.RaiseSSeqLicensed.rungAt_eq
#print axioms OneColourClosure.rungAt_eq_of_perm
#print axioms OneColourClosure.RaiseSSeqLicensed.revEqW
#print axioms OneColourClosure.revEqW_of_raise_plays
#print axioms OneColourClosure.canRaiseS_of_raise_perm'
#print axioms OneColourClosure.perm_two_reverse_aux
#print axioms OneColourClosure.perm_reverse
#print axioms OneColourClosure.perm_erase
#print axioms OneColourClosure.RaiseSSeqLicensed.step_s'
#print axioms OneColourClosure.RaiseSSeqLicensed.split_head
#print axioms OneColourClosure.RaiseSSeqLicensed.split_chron
#print axioms OneColourClosure.RaiseSSeqLicensed.tail_transport
#print axioms OneColourClosure.rank_lt_of_mem_of_lastOf
#print axioms OneColourClosure.insertByRank_push
#print axioms OneColourClosure.fromCard_append_singleton_of_not_mem
#print axioms OneColourClosure.suit_ne_of_twin
#print axioms OneColourClosure.not_mem_pileOfTop_of_rank_eq
#print axioms OneColourClosure.not_mem_pileOfTop_twin_of_rank_eq

