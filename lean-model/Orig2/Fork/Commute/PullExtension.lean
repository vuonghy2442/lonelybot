import Orig2.Fork.Commute.RaisesOrForkMain
import Orig2.Fork.Commute.ForklessTop_Main
import Orig2.Fork.Commute.SpectrumCollapse

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-!
# Temp/PullExtension — the pull case with an existential target word

The fixed-word `hPull` of `Orig2/Fork/Commute/RaisesOrForkMain.lean` asks for a play from the
pull source with the word `playWord (sortByRank ws)`.  That target is **false**:
on the dead-twin board (`Temp/ForkDeadTwin.lean`) the card `c.twin` is buried at
the pull source, so the fixed word is not licensed, while the class is
fork-free.  The join nevertheless exists — with an *enlarged* word.

This card restates the pull case in the form the campaign actually consumes:

```
(∃ ws v, RaiseSSeqLicensed s ws v ∧ RungLe s v ∧ RungLe t v) ∨ Fork s
```

i.e. the word is existentially quantified.  The proof is factored through one
clean notion:

* `RaiseExtension u c v` — a licensed play from `u` whose word contains `c` and
  whose endpoint dominates `v`.

The reduction `pull_case_of_extension` hoists `c` to the front of that play
(`raiseS_rankfront_L`), cancels it against the pull
(`cancel_prefix_is_play_from_source`), and reads the rungs off the two ledgers.
It never replays the original word at the pull source, so the dead-twin board is
handled by the enlarged (`4♦`-carrying) word rather than by a replay.

The two cheap extension producers are proved:

* `raiseExtension_of_end_live` — append `c` when it is still live at `v`;
* `raiseExtension_of_noTwin` — the same when `c.twin` is absent from the word.

The single remaining shape is isolated as `TwinRescue`: `c.twin` occurs in the
word and `c` dies at the endpoint, so the extension must first revive `c` by
raising the cards covering it.  `pull_case_existential` turns `TwinRescue` into
the existential pull case, and `fullJoinAtLeastOrFork_of_twinRescue` feeds it to
the path induction of `RaisesOrForkMain`.

House rules: no `sorry`, no `Classical`, no `noncomputable`, no new axioms.
-/

namespace OneColourClosure

/-! ## §1. The extension notion -/

/-- **A raise extension of `v` adding the card `c`.**  A licensed play from `u`
whose raised word contains `c` and whose endpoint dominates `v` rungwise.  It
may raise extra cards (the "rescues"); only the domination of `v` and the
occurrence of `c` are used downstream. -/
def RaiseExtension (u : State) (c : Card) (v : State) : Prop :=
  ∃ ws w, RaiseSSeqLicensed u ws w ∧ c ∈ ws ∧ RungLe v w

/-- **Appending a live card is an extension.**  If `c` is still `S`-live at the
endpoint `v`, append it as the last raise; the endpoint only climbs. -/
theorem raiseExtension_of_end_live {u v : State} {c : Card} {ws : List Card}
    (hρ : RaiseSSeqLicensed u ws v) (hcv : CanRaiseS v c) :
    RaiseExtension u c v := by
  obtain ⟨z0, hp, hcan⟩ := hcv
  obtain ⟨w, hstep⟩ := step_tabToFound_of_canRaise hcan
  have hstepS : RaiseStepS v w c := ⟨z0, hp, hstep⟩
  have hρ' : RaiseSSeqLicensed u (c :: ws) w :=
    RaiseSSeqLicensed.cons hρ ⟨z0, hp, hcan⟩ hp hstep
  refine ⟨c :: ws, w, hρ', by simp, ?_⟩
  obtain ⟨hon, hoff⟩ := RungMono.rungAt_raiseStepS hstepS
  intro σ
  by_cases hσ : σ = c.suit
  · subst hσ
    rw [hon]
    exact Nat.le_succ _
  · rw [hoff σ hσ]
    exact Nat.le_refl _

/-- **A twin-free word extends by `c`.**  `c`'s licence only ever dies at a
raise of `c` or `c.twin`; if `c` is absent from the word and so is its twin,
`c` is still live at the endpoint and `raiseExtension_of_end_live` applies. -/
theorem raiseExtension_of_noTwin {u v : State} {c : Card} {ws : List Card}
    (hu : u.WF) (hρ : RaiseSSeqLicensed u ws v) (hc : CanRaiseS u c)
    (hself : c ∉ ws) (htwin : c.twin ∉ ws) :
    RaiseExtension u c v :=
  raiseExtension_of_end_live hρ (canRaiseS_of_word_notMem hρ hu hc hself htwin)

/-! ## §1b. The word-carrying raise climb

`ForklessTop.exists_saturated_above` gives a saturated class-mate but forgets
the raises that produced it.  The same `52 - rungSum` recursion, with the word
accumulated, gives the object the rescue needs: a licensed raise-only play to a
saturated state above the start. -/

/-- **THE WORD-CARRYING RAISE CLIMB.**  Every `WF` state has a licensed
raise-only play to a saturated class-mate whose rungs dominate the start. -/
theorem exists_raiseClimb_saturated (u : State) (hu : u.WF) :
    ∃ ws w, RaiseSSeqLicensed u ws w ∧ w.WF ∧ SSaturated w ∧ RungLe u w := by
  have key : ∀ N (u : State), u.WF → 52 - Drain.rungSum u = N →
      ∃ ws w, RaiseSSeqLicensed u ws w ∧ w.WF ∧ SSaturated w ∧ RungLe u w := by
    intro N
    induction N using Nat.strongRecOn with
    | ind N ih =>
      intro u hu hN
      by_cases hb : rankSatB 13 u = true
      · exact ⟨[], u, RaiseSSeqLicensed.nil u, hu,
          ForklessTop.ssaturated_of_rankSatB_true hu hb, fun _ => Nat.le_refl _⟩
      · have hfalse : rankSatB 13 u = false := by
          cases h : rankSatB 13 u with
          | false => rfl
          | true => exact absurd h hb
        obtain ⟨c, -, hcS⟩ := ForklessTop.exists_live_of_rankSatB_false hu hfalse
        obtain ⟨z, hpath, hcan⟩ := hcS
        obtain ⟨A, hstep⟩ := step_tabToFound_of_canRaise hcan
        have hsingle : RaiseSSeqLicensed u [c] A :=
          RaiseSSeqLicensed.cons (RaiseSSeqLicensed.nil u)
            ⟨z, hpath, hcan⟩ hpath hstep
        have hzWF : z.WF := cargoPath_wf hu hpath
        have hAwf : A.WF := step_wf hzWF hstep
        have hsumA : Drain.rungSum A = Drain.rungSum u + 1 := by
          have hz : Drain.rungSum z = Drain.rungSum u :=
            ForklessTop.rungSum_eq_of_rung_eq
              (fun σ => (rungAt_cargoPath hpath σ).symm)
          rw [DrainClose.rungSum_raise hstep, hz]
        have hN' : 52 - Drain.rungSum A < N := by
          have hleA52 := Drain.rungSum_le_52 hAwf
          have hr : Drain.rungSum u < 52 := by omega
          have hlt : 52 - (Drain.rungSum u + 1) < 52 - Drain.rungSum u :=
            Nat.sub_lt_sub_left hr (Nat.lt_succ_self (Drain.rungSum u))
          rw [hsumA, ← hN]
          exact hlt
        obtain ⟨wsA, w, hρA, hwwf, hwsat, hleA⟩ :=
          ih (52 - Drain.rungSum A) hN' A hAwf rfl
        refine ⟨wsA ++ [c], w, RaiseSSeqLicensed.append hsingle hρA, hwwf, hwsat, ?_⟩
        obtain ⟨hon, hoff⟩ :=
          RungMono.rungAt_raiseStepS (z := u) (z' := A) (c := c) ⟨z, hpath, hstep⟩
        intro σ
        have huA : rungAt u σ ≤ rungAt A σ := by
          by_cases hσ : σ = c.suit
          · subst hσ
            rw [hon]
            exact Nat.le_succ _
          · rw [hoff σ hσ]
            exact Nat.le_refl _
        exact Nat.le_trans huA (hleA σ)
  exact key (52 - Drain.rungSum u) u hu rfl

/-! ## §1c. Merging a lower-rank word with a strictly higher-rank word

This is the rank-based `HigherReplay`: if `L` is ascending and every card of `L`
is strictly below every card of the ascending word `H`, then a licensed play of
`L` and a licensed play of `H` from the same state can be concatenated as
`L ; H`.  The proof inserts the letters of `L` one at a time with
`BlockHousing.suffix_insert`, aligning the two single-letter `l` landings by
`replay_of_orbit_rung` (they are equal-rung orbit mates). -/

theorem merge_lower_higher :
    ∀ (L : List Card) {s u v : State} {H : List Card},
      L.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) →
      H.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) →
      (∀ l ∈ L, ∀ h ∈ H, l.rank.toIdx < h.rank.toIdx) →
      s.WF →
      RaiseSSeqLicensed s (playWord L) u →
      RaiseSSeqLicensed s (playWord H) v →
      ∃ w, RaiseSSeqLicensed s (playWord (L ++ H)) w := by
  intro L
  induction L with
  | nil =>
      intro s u v H _ _ _ hs _ hH
      exact ⟨v, by simpa using hH⟩
  | cons l L' ih =>
      intro s u v H hLasc hHasc hrank hs hL hH
      obtain ⟨s1, h_l, hL'⟩ :=
        RaiseSSeqLicensed.split_chron (A := [l]) (R := L') (s := s) (z := u)
          (by simpa [playWord, List.append_assoc] using hL)
      have h_l' : RaiseSSeqLicensed s [l] s1 := by simpa [playWord] using h_l
      have hl : CanRaiseS s l := canRaiseS_of_raiseSSeqLicensed_head h_l'
      have hs1 : s1.WF := RaiseSSeqLicensed.wf h_l hs
      have hr : ∀ d ∈ H, l.rank.toIdx < d.rank.toIdx :=
        fun d hd => hrank l (by simp) d hd
      obtain ⟨z, h_lH⟩ := suffix_insert hs hHasc hH hl hr
      obtain ⟨s1', h_l2, hH'⟩ :=
        RaiseSSeqLicensed.split_chron (A := [l]) (R := H) (s := s) (z := z)
          (by simpa [playWord, List.append_assoc] using h_lH)
      have h_l2' : RaiseSSeqLicensed s [l] s1' := by simpa [playWord] using h_l2
      have hs1' : s1'.WF := RaiseSSeqLicensed.wf h_l2 hs
      have horb_eq : RevEqW s1' s1 := revEqW_of_raise_plays hs h_l2' h_l'
      have horb' : sameOrbitSetoid.r s1' s1 := RevEqW_symm horb_eq
      have hrung : ∀ σ, rungAt s1 σ = rungAt s1' σ :=
        rungAt_eq_of_perm h_l' h_l2' (List.Perm.refl [l])
      have hrung' : ∀ σ, rungAt s1' σ = rungAt s1 σ := fun σ => (hrung σ).symm
      obtain ⟨u', hL'', -, -⟩ := replay_of_orbit_rung hs1' horb' hrung' hL'
      have hL'asc : L'.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) :=
        (List.pairwise_cons.mp hLasc).2
      have hrank' : ∀ l' ∈ L', ∀ h ∈ H, l'.rank.toIdx < h.rank.toIdx :=
        fun l' hl' h hh => hrank l' (List.mem_cons_of_mem l hl') h hh
      obtain ⟨w, hmerge⟩ :=
        ih (s := s1') (u := u') (v := z) hL'asc hHasc hrank' hs1' hL'' hH'
      refine ⟨w, ?_⟩
      have hfin : RaiseSSeqLicensed s (playWord (L' ++ H) ++ playWord [l]) w :=
        RaiseSSeqLicensed.append h_l2 hmerge
      simpa [playWord, List.append_assoc] using hfin

/-! ## §1c'. The twin-free merge (no rank separation)

`merge_lower_higher` needs every card of `L` to be strictly below every card of
`H`; the insertion of the head `l` relies on `suffix_insert`, whose `tieFree`
step requires the target `l :: H` to be ascending.  If instead `H` merely avoids
`l` and `l.twin`, then `l`'s licence survives `H`
(`canRaiseS_of_word_notMem`), so a play of `H` can be extended by `l` at the end;
bubbling `l` back to the front uses the adjacent swaps `asc_swap` /
`tie_swap` / `swap_inversion`, none of which needs `H` to be ascending. -/

/-- **Bubble a twin-free card to the front.**  If a licensed play chronologically
runs `B` and then `c`, and `c` (with its twin) is absent from `B` and is
`S`-live at the start, then `c` can be played first.  No rank hypothesis on `B`:
the three adjacent-swap lemmas cover all rank comparisons. -/
theorem bubble_front_notwin (B : List Card) :
    ∀ {u z : State} {c : Card} {T : List Card},
      u.WF → c ∉ B → c.twin ∉ B → CanRaiseS u c →
      RaiseSSeqLicensed u (playWord (B ++ c :: T)) z →
      ∃ z', RaiseSSeqLicensed u (playWord (c :: B ++ T)) z' := by
  induction B with
  | nil =>
      intro u z c T _ _ _ _ h
      exact ⟨z, by simpa using h⟩
  | cons a B ih =>
      intro u z c T hu hcB hctB hc h
      have hne : a ≠ c := by
        intro hcon
        exact hcB (by rw [hcon]; exact List.mem_cons_self ..)
      have hcta : a ≠ c.twin := by
        intro hcon
        exact hctB (by rw [hcon]; exact List.mem_cons_self ..)
      obtain ⟨u_a, h_a, hrest⟩ :=
        RaiseSSeqLicensed.split_chron (A := [a]) (R := B ++ c :: T)
          (by simpa [List.append_assoc] using h)
      have hu_a : u_a.WF := RaiseSSeqLicensed.wf h_a hu
      have hca_word : c ∉ playWord [a] := by
        have hca : c ≠ a := fun hcon => hne hcon.symm
        simpa [playWord] using hca
      have hcta_word : c.twin ∉ playWord [a] := by
        have hcta' : c.twin ≠ a := fun hcon => hcta hcon.symm
        simpa [playWord] using hcta'
      have hc_a : CanRaiseS u_a c :=
        canRaiseS_of_word_notMem h_a hu hc hca_word hcta_word
      have hcB' : c ∉ B := fun hmem => hcB (List.mem_cons_of_mem a hmem)
      have hctB' : c.twin ∉ B := fun hmem => hctB (List.mem_cons_of_mem a hmem)
      obtain ⟨z₁, hz₁⟩ :=
        ih (u := u_a) (z := z) (c := c) (T := T) hu_a hcB' hctB' hc_a hrest
      have hplay : RaiseSSeqLicensed u (playWord (a :: c :: (B ++ T))) z₁ := by
        have h1 := RaiseSSeqLicensed.append h_a hz₁
        simpa [playWord, List.append_assoc] using h1
      by_cases hlt : a.rank.toIdx < c.rank.toIdx
      · obtain ⟨z', hz'⟩ := asc_swap hu hplay hlt hc
        exact ⟨z', by simpa [List.append_assoc] using hz'⟩
      · by_cases hgt : c.rank.toIdx < a.rank.toIdx
        · obtain ⟨z', hz'⟩ :=
            swap_inversion (s := u) (z := z₁) (A := ([] : List Card))
              (T := B ++ T) (x := a) (y := c) hu hgt
              (by simpa [List.append_assoc] using hplay)
          exact ⟨z', by simpa [List.append_assoc] using hz'⟩
        · have heq : a.rank = c.rank := by
            apply Rank.toIdx_inj
            omega
          obtain ⟨z', hz'⟩ := tie_swap hu hplay heq hne
          exact ⟨z', by simpa [List.append_assoc] using hz'⟩

/-- **Twin-free suffix insertion.**  If `H` is ascending and avoids `c` and
`c.twin`, and `c` is `S`-live at the start, then `c ; H` is playable from the
same source.  (The `H`-ascending hypothesis is inherited from the old interface;
the bubbling proof does not actually use it.) -/
theorem suffix_insert_notwin {u z : State} {c : Card} {H : List Card}
    (hu : u.WF)
    (hH : H.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx))
    (hplay : RaiseSSeqLicensed u (playWord H) z)
    (hc : CanRaiseS u c)
    (hcH : c ∉ H) (hctH : c.twin ∉ H) :
    ∃ z', RaiseSSeqLicensed u (playWord (c :: H)) z' := by
  have hcH' : c ∉ playWord H := by simpa [playWord] using hcH
  have hctH' : c.twin ∉ playWord H := by simpa [playWord] using hctH
  have hcz : CanRaiseS z c := canRaiseS_of_word_notMem hplay hu hc hcH' hctH'
  obtain ⟨v, hv⟩ := exists_append_raise hplay hcz
  have hplay' : RaiseSSeqLicensed u (playWord (H ++ [c])) v := by
    rw [playWord_snoc]
    exact hv
  obtain ⟨z', hz'⟩ :=
    bubble_front_notwin H hu hcH hctH hc (by simpa using hplay')
  exact ⟨z', by simpa using hz'⟩

/-- **The twin-free merge.**  If `L` and `H` are ascending, card-disjoint from
each other and from each other's twins, and both are playable from `s`, then
`L ; H` is playable from `s`.  Unlike `merge_lower_higher` there is no rank
separation between `L` and `H`. -/
theorem merge_notwin :
    ∀ (L : List Card) {s u v : State} {H : List Card},
      L.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) →
      H.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) →
      (∀ l ∈ L, l ∉ H ∧ l.twin ∉ H) →
      (∀ h ∈ H, h ∉ L ∧ h.twin ∉ L) →
      s.WF →
      RaiseSSeqLicensed s (playWord L) u →
      RaiseSSeqLicensed s (playWord H) v →
      ∃ w, RaiseSSeqLicensed s (playWord (L ++ H)) w := by
  intro L
  induction L with
  | nil =>
      intro s u v H _ _ _ _ hs _ hH
      exact ⟨v, by simpa using hH⟩
  | cons l L' ih =>
      intro s u v H hLasc hHasc hdisjL hdisjH hs hL hH
      obtain ⟨s1, h_l, hL'⟩ :=
        RaiseSSeqLicensed.split_chron (A := [l]) (R := L') (s := s) (z := u)
          (by simpa [playWord, List.append_assoc] using hL)
      have h_l' : RaiseSSeqLicensed s [l] s1 := by simpa [playWord] using h_l
      have hl : CanRaiseS s l := canRaiseS_of_raiseSSeqLicensed_head h_l'
      have hs1 : s1.WF := RaiseSSeqLicensed.wf h_l hs
      obtain ⟨hcH, hctH⟩ := hdisjL l (by simp)
      obtain ⟨z, h_lH⟩ := suffix_insert_notwin hs hHasc hH hl hcH hctH
      obtain ⟨s1', h_l2, hH'⟩ :=
        RaiseSSeqLicensed.split_chron (A := [l]) (R := H) (s := s) (z := z)
          (by simpa [playWord, List.append_assoc] using h_lH)
      have h_l2' : RaiseSSeqLicensed s [l] s1' := by simpa [playWord] using h_l2
      have hs1' : s1'.WF := RaiseSSeqLicensed.wf h_l2 hs
      have horb_eq : RevEqW s1' s1 := revEqW_of_raise_plays hs h_l2' h_l'
      have horb' : sameOrbitSetoid.r s1' s1 := RevEqW_symm horb_eq
      have hrung : ∀ σ, rungAt s1 σ = rungAt s1' σ :=
        rungAt_eq_of_perm h_l' h_l2' (List.Perm.refl [l])
      have hrung' : ∀ σ, rungAt s1' σ = rungAt s1 σ := fun σ => (hrung σ).symm
      obtain ⟨u', hL'', -, -⟩ := replay_of_orbit_rung hs1' horb' hrung' hL'
      have hL'asc : L'.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) :=
        (List.pairwise_cons.mp hLasc).2
      have hdisjL' : ∀ l' ∈ L', l' ∉ H ∧ l'.twin ∉ H :=
        fun l' hl' => hdisjL l' (List.mem_cons_of_mem l hl')
      have hdisjH' : ∀ h ∈ H, h ∉ L' ∧ h.twin ∉ L' := by
        intro h hh
        obtain ⟨h1, h2⟩ := hdisjH h hh
        exact ⟨fun hm => h1 (List.mem_cons_of_mem l hm),
          fun hm => h2 (List.mem_cons_of_mem l hm)⟩
      obtain ⟨w, hmerge⟩ :=
        ih (s := s1') (u := u') (v := z) hL'asc hHasc hdisjL' hdisjH'
          hs1' hL'' hH'
      refine ⟨w, ?_⟩
      have hfin : RaiseSSeqLicensed s (playWord (L' ++ H) ++ playWord [l]) w :=
        RaiseSSeqLicensed.append h_l2 hmerge
      simpa [playWord, List.append_assoc] using hfin

/-! ## §1d. The post-twin rescue and the `TailReplay` replacement

Instead of replaying the tail after the square, run the low rescue **after** the
original `c.twin` letter.  The tail `post` is then licensed from the same state
as the rescue and every rescue/`c` rank is strictly below every `post` rank, so
`merge_lower_higher` appends it.  This is the last good-arm input. -/

/-- **THE POST-TWIN RESCUE (residual).**  After the original `c.twin` letter,
a rank-`< c.rank` play makes `c` vanilla.  The rescue is ascending, and its
letters (plus `c`) are strictly below every tail letter. -/
def PostTwinRescue : Prop :=
  ∀ {t v : State} {c : Card} {post : List Card},
    t.WF → RaiseSSeqLicensed t (playWord post) v →
      (∀ d ∈ post, c.rank.toIdx < d.rank.toIdx) →
      post.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) →
      ∃ res w, RaiseSSeqLicensed t (playWord res) w ∧
        (res ++ [c]).Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) ∧
        (∀ d ∈ res, d.rank.toIdx < c.rank.toIdx) ∧
        CanRaise w c

/-! ## §1f. Rank-tie normalization: move the twin letter to the end of its block

After sorting, `c.twin` may still be followed by other cards of the same rank.
`tie_swap` lets us bubble it to the right across that same-rank block, so the
tail `post` has rank strictly above `c.rank`. -/

theorem tie_move_right (B : List Card) :
    ∀ {s z : State} {c : Card},
      s.WF → c ∉ B → (∀ b ∈ B, b.rank = c.rank) →
      RaiseSSeqLicensed s (playWord (c :: B)) z →
      ∃ z', RaiseSSeqLicensed s (playWord (B ++ [c])) z' := by
  induction B with
  | nil =>
      intro s z c hs _ _ h
      exact ⟨z, by simpa [playWord] using h⟩
  | cons b B' ih =>
      intro s z c hs hcB hB h
      have hb : b.rank = c.rank := hB b (by simp)
      have hcb : c ≠ b := by
        intro hEq
        exact hcB (by rw [hEq]; exact List.mem_cons_self ..)
      have hcB' : c ∉ B' := fun hmem => hcB (List.mem_cons_of_mem b hmem)
      have hB' : ∀ b' ∈ B', b'.rank = c.rank :=
        fun b' hb' => hB b' (List.mem_cons_of_mem b hb')
      obtain ⟨z1, h1⟩ := tie_swap hs h hb.symm hcb
      obtain ⟨s1, hbplay, hsl⟩ :=
        RaiseSSeqLicensed.split_chron (A := [b]) (R := c :: B') (s := s) (z := z1)
          (by simpa [playWord, List.append_assoc] using h1)
      have hs1 : s1.WF := RaiseSSeqLicensed.wf hbplay hs
      obtain ⟨z2, h2⟩ := ih hs1 hcB' hB' hsl
      refine ⟨z2, ?_⟩
      have hfin : RaiseSSeqLicensed s (playWord (B' ++ [c]) ++ playWord [b]) z2 :=
        RaiseSSeqLicensed.append hbplay h2
      simpa [playWord, List.append_assoc] using hfin

/-- Prefix form: move `c` to the end of the same-rank block `B` that follows it. -/
theorem move_twin_last {s z : State} {c : Card} {A B : List Card}
    (hs : s.WF) (hcB : c ∉ B) (hB : ∀ b ∈ B, b.rank = c.rank)
    (h : RaiseSSeqLicensed s (playWord (A ++ c :: B)) z) :
    ∃ z', RaiseSSeqLicensed s (playWord (A ++ B ++ [c])) z' := by
  obtain ⟨sA, hA, hSuf⟩ :=
    RaiseSSeqLicensed.split_chron (A := A) (R := c :: B) h
  have hsA : sA.WF := RaiseSSeqLicensed.wf hA hs
  obtain ⟨z', hSuf'⟩ := tie_move_right B hsA hcB hB hSuf
  refine ⟨z', ?_⟩
  have hfin : RaiseSSeqLicensed s (playWord (B ++ [c]) ++ playWord A) z' :=
    RaiseSSeqLicensed.append hA hSuf'
  simpa [playWord, List.append_assoc] using hfin

/-- **Post-twin vanilla read.**  Once `c.twin` is founded, a covered `c` cannot
be `S`-live: the only non-vanilla way to be live is the twin-top disjunct, which
is unavailable.  Hence `CanRaiseS` at `t` is already `CanRaise`. -/
theorem canRaise_of_canRaiseS_of_twin_founded {z : State} {c : Card}
    (hz : z.WF) (hfound : c.twin ∈ z.found c.twin.suit)
    (hc : CanRaiseS z c) : CanRaise z c := by
  obtain ⟨-, hfree⟩ := (canRaiseS_split hz).mp hc
  obtain ⟨a, run, hhold, -, -, -⟩ := freeCardS_unpack hfree
  have htwin : z.pileOfTop c.twin = none :=
    pileOfTop_eq_none_of_found hz hfound
  have hexp : fromCard c ((z.piles a).faceUp) = [c] :=
    fromCard_nil_of_freeCardS_of_twin_none hhold hfree htwin
  exact canRaise_of_canRaiseS_of_exposed hz hhold hexp hc

/-- **THE LAST GOOD-ARM RESIDUAL.**  The revive drain from `t` ends with `c`
still `S`-live (and `c.twin` still founded).  The ascending form is carried so
it can feed `PostTwinRescue` directly. -/
def PostTwinLive : Prop :=
  ∀ {t v : State} {c : Card} {post : List Card},
    t.WF → RaiseSSeqLicensed t (playWord post) v →
      (∀ d ∈ post, c.rank.toIdx < d.rank.toIdx) →
      post.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) →
      ∃ res w, RaiseSSeqLicensed t (playWord res) w ∧
        (res ++ [c]).Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) ∧
        (∀ d ∈ res, d.rank.toIdx < c.rank.toIdx) ∧
        CanRaiseS w c ∧ c.twin ∈ w.found c.twin.suit ∧ w.WF

/-- **`PostTwinLive` ⇒ `PostTwinRescue`.**  The post-twin vanilla read upgrades
the endpoint licence. -/
theorem postTwinRescue_of_live (hl : PostTwinLive) : PostTwinRescue := by
  intro t v c post ht hpost hrank hcast
  obtain ⟨res, w, hres, hLasc, hresRank, hcS, hfound, hwf⟩ :=
    hl ht hpost hrank hcast
  exact ⟨res, w, hres, hLasc, hresRank,
    canRaise_of_canRaiseS_of_twin_founded hwf hfound hcS⟩

/-- **`TailReplay` REPLACED BY THE POST-TWIN RESCUE + MERGE.**  From
`PostTwinRescue`, the pair extension `res ++ [c]` is merged with the tail
`post` by `merge_lower_higher`; the endpoint dominates `v` because `post` is a
factor of the merged word. -/
theorem extension_of_postTwinRescue (hp : PostTwinRescue)
    {t v : State} {c : Card} {post : List Card}
    (ht : t.WF) (hpost : RaiseSSeqLicensed t (playWord post) v)
    (hpostRank : ∀ d ∈ post, c.rank.toIdx < d.rank.toIdx)
    (hpostAsc : post.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx)) :
    ∃ ws w, RaiseSSeqLicensed t ws w ∧ c ∈ ws ∧ RungLe v w := by
  obtain ⟨res, w, hres, hLasc, hresRank, hcanC⟩ :=
    hp ht hpost hpostRank hpostAsc
  obtain ⟨w', hresC⟩ := exists_append_raise hres (CanRaiseS.now c hcanC)
  have hLlic : RaiseSSeqLicensed t (playWord (res ++ [c])) w' := by
    simpa [playWord] using hresC
  have hsep : ∀ l ∈ res ++ [c], ∀ h ∈ post,
      l.rank.toIdx < h.rank.toIdx := by
    intro l hl h hh
    rcases List.mem_append.mp hl with hl | hl
    · exact Nat.lt_trans (hresRank l hl) (hpostRank h hh)
    · rw [List.mem_singleton] at hl
      subst hl
      exact hpostRank h hh
  obtain ⟨w2, hmerge⟩ :=
    merge_lower_higher (res ++ [c]) hLasc hpostAsc hsep ht hLlic hpost
  refine ⟨playWord ((res ++ [c]) ++ post), w2, hmerge, ?_, ?_⟩
  · simp [playWord]
  · intro σ
    rw [hpost.rungAt_eq σ, hmerge.rungAt_eq σ]
    have hcount : (playWord post).countP (fun d => decide (d.suit = σ)) ≤
        (playWord ((res ++ [c]) ++ post)).countP
          (fun d => decide (d.suit = σ)) := by
      rw [show playWord ((res ++ [c]) ++ post) =
          playWord post ++ playWord (res ++ [c]) from by
        simp [playWord, List.append_assoc]]
      rw [List.countP_append]
      exact Nat.le_add_right _ _
    exact Nat.add_le_add_left hcount _

/-! ## §1e. The post-twin revive drain and the vanilla read

`revive_drain` is the unconditional low-rank climb: raise any S-live card of
rank below `x.rank` until none remains.  Unlike `PullInsert.low_drain_aux` it
does **not** assume the tracked card is live; it is the engine that tries to
revive `c` after the twin letter.  The `t`-side simplification is that `c.twin`
is now founded, so `CanRaiseS` already forces `c` to be exposed, hence vanilla:
`canRaise_of_canRaiseS_of_twin_founded`. -/

theorem revive_drain_aux (x : Card) (n : Nat) :
    ∀ z : State, z.WF → 52 - Drain.rungSum z ≤ n →
      ∃ ws z', RaiseSSeqLicensed z ws z' ∧
        (∀ d ∈ ws, d.rank.toIdx < x.rank.toIdx) ∧
        (∀ d, CanRaiseS z' d → x.rank.toIdx ≤ d.rank.toIdx) ∧
        sameOrbitSetoid.r z z' := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro z hz hle
      cases hb : Card.universe.all (fun d =>
          (!canRaiseSB z d) || !decide (d.rank.toIdx < x.rank.toIdx)) with
      | true =>
          have hfloor : ∀ d, CanRaiseS z d → x.rank.toIdx ≤ d.rank.toIdx := by
            intro d hd
            have hprobe : canRaiseSB z d = true := (canRaiseSB_iff hz).mpr hd
            have hall := List.all_eq_true.mp hb d (Card.mem_universe d)
            rw [hprobe] at hall
            simp only [Bool.not_true, Bool.false_or] at hall
            have hdecF : decide (d.rank.toIdx < x.rank.toIdx) = false := by
              cases hd2 : decide (d.rank.toIdx < x.rank.toIdx) with
              | true => rw [hd2] at hall; simp at hall
              | false => rfl
            exact Nat.le_of_not_gt (of_decide_eq_false hdecF)
          exact ⟨[], z, RaiseSSeqLicensed.nil z, by simp, hfloor,
            sameOrbitSetoid.iseqv.refl z⟩
      | false =>
          obtain ⟨d, -, hcfalse⟩ := Drain.exists_of_all_false hb
          rw [Bool.or_eq_false_iff] at hcfalse
          obtain ⟨hnot, hdec⟩ := hcfalse
          have hprobe : canRaiseSB z d = true := by
            cases hp : canRaiseSB z d with
            | true => rfl
            | false => rw [hp] at hnot; simp at hnot
          have hlt : d.rank.toIdx < x.rank.toIdx := by
            cases hd2 : decide (d.rank.toIdx < x.rank.toIdx) with
            | true => exact of_decide_eq_true hd2
            | false => rw [hd2] at hdec; simp at hdec
          have hSc : CanRaiseS z d := (canRaiseSB_iff hz).mp hprobe
          obtain ⟨z', hstepS⟩ := raiseStepS_of_canRaiseS hSc
          have hsum : Drain.rungSum z' = Drain.rungSum z + 1 :=
            SpectrumCollapse.rungSum_raiseStepS hstepS
          have hz' : z'.WF := raiseStepS_wf hz hstepS
          have hlt' : 52 - Drain.rungSum z' < n := by
            have hbound : Drain.rungSum z' ≤ 52 := Drain.rungSum_le_52 hz'
            omega
          obtain ⟨ws, w, hpath, hranks, hfloor, horb⟩ :=
            ih (52 - Drain.rungSum z') hlt' z' hz' (Nat.le_refl _)
          obtain ⟨z0, hp, hs⟩ := hstepS
          have hletter : RaiseSSeqLicensed z [d] z' :=
            RaiseSSeqLicensed.cons (RaiseSSeqLicensed.nil z) hSc hp hs
          have hfull : RaiseSSeqLicensed z (ws ++ [d]) w :=
            RaiseSSeqLicensed.append hletter hpath
          refine ⟨ws ++ [d], w, hfull, ?_, hfloor,
            RevEqW_symm (RaiseSSeqLicensed.revEqW hfull hz)⟩
          intro e he
          rcases List.mem_append.mp he with he | he
          · exact hranks e he
          · rw [List.mem_singleton] at he
            rw [he]
            exact hlt

/-- The unconditional low-rank revive drain. -/
theorem revive_drain {z : State} {x : Card} (hz : z.WF) :
    ∃ ws z', RaiseSSeqLicensed z ws z' ∧
      (∀ d ∈ ws, d.rank.toIdx < x.rank.toIdx) ∧
      (∀ d, CanRaiseS z' d → x.rank.toIdx ≤ d.rank.toIdx) ∧
      sameOrbitSetoid.r z z' :=
  revive_drain_aux x (52 - Drain.rungSum z) z hz (Nat.le_refl _)

/-- **THE GOOD ARM FROM `PostTwinLive`.**  Revive drain ⇒ `PostTwinRescue` ⇒
merge with the tail. -/
theorem extension_of_postTwinLive (hl : PostTwinLive)
    {t v : State} {c : Card} {post : List Card}
    (ht : t.WF) (hpost : RaiseSSeqLicensed t (playWord post) v)
    (hpostRank : ∀ d ∈ post, c.rank.toIdx < d.rank.toIdx)
    (hpostAsc : post.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx)) :
    ∃ ws w, RaiseSSeqLicensed t ws w ∧ c ∈ ws ∧ RungLe v w :=
  extension_of_postTwinRescue (postTwinRescue_of_live hl) ht hpost hpostRank hpostAsc

/-! ## §2. Extension ⇒ a play from the pull source -/

/-- **The pull case, from an extension.**  Hoist `c` to the front of the
extension play (`raiseS_rankfront_L`), cancel the leading raise against the pull
(`cancel_prefix_is_play_from_source`), and read the rungs off the two ledgers.
The resulting play starts at the pull source `s` and dominates `v`. -/
theorem pull_case_of_extension {s u v : State} {c : Card} {b : Base}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hext : RaiseExtension u c v) :
    ∃ ws w, RaiseSSeqLicensed s ws w ∧ RungLe s w ∧ RungLe v w := by
  obtain ⟨ws', w, hρ', hc_mem, hvw⟩ := hext
  have hu : u.WF := step_wf hs hpull
  have hcanU : CanRaiseS u c := SatDifferConfig.canRaiseS_after_pull hs hpull
  have hcan : CanRaise u c := SatDifferConfig.canRaise_after_pull hs hpull
  -- hoist `c` to the front of the extension play
  obtain ⟨z, hz⟩ := raiseS_rankfront_L hu hcanU hρ' hc_mem
  have hword : rankFrontWord c ws' =
      playWord (c :: sortByRank (ws'.erase c)) := by
    simp [rankFrontWord, playWord]
  have hz' : RaiseSSeqLicensed u (playWord (c :: sortByRank (ws'.erase c))) z := by
    rwa [hword] at hz
  -- cancel the leading raise against the pull
  obtain ⟨w', hw'⟩ := cancel_prefix_is_play_from_source hs hpull hcan hz'
  refine ⟨playWord (sortByRank (ws'.erase c)), w', hw',
    rungLe_of_raiseSSeqLicensed hw', ?_⟩
  -- the rung ledger: the cancelled play ends where the extension play ends
  have hperm : (playWord (sortByRank (ws'.erase c))).Perm (ws'.erase c) := by
    rw [playWord]
    exact (reverse_perm (sortByRank (ws'.erase c))).trans
      (sortByRank_perm (ws'.erase c))
  have hstepUS : State.step u (Move.tabToFound c) = some s :=
    step_tabToFound_of_foundToTab hs hpull
  have heq : ∀ σ : Suit, rungAt w' σ = rungAt w σ := by
    intro σ
    rw [hw'.rungAt_eq σ, hρ'.rungAt_eq σ,
      hperm.countP_eq (fun d => decide (d.suit = σ)),
      rungAt_tabToFound hstepUS σ]
    have herase := countP_erase_add hc_mem (fun d => decide (d.suit = σ))
    by_cases hσ : σ = c.suit
    · subst hσ
      have hp1 : (if decide (c.suit = c.suit) = true then 1 else 0) = 1 := by
        simp
      rw [hp1] at herase
      rw [ite_eq_left rfl]
      omega
    · have hp0 : (if decide (c.suit = σ) = true then 1 else 0) = 0 := by
        have hne : c.suit ≠ σ := fun h => hσ h.symm
        rw [decide_eq_false hne]
        rfl
      rw [hp0] at herase
      rw [ite_eq_right hσ]
      omega
  intro σ
  rw [heq σ]
  exact hvw σ

/-- **Fork lifts backwards along a licensed play.**  A fork at the endpoint of a
raise-only play is already a fork at its start.  This is the bridge the
pre-twin fork arm needs. -/
theorem fork_of_raiseSSeqLicensed {u z : State} {ws : List Card}
    (h : RaiseSSeqLicensed u ws z) (hu : u.WF) (hf : Fork z) : Fork u :=
  fork_of_sameOrbit (h.revEqW hu) hf

/-! ## §2b. The pre-twin state and the spectrum dichotomy

The fork lives one step *before* the dead endpoint: at the state just before the
first chronological `c.twin` letter, both twins are still `S`-live.  Splitting
the word there and applying the drain dichotomy is the correct shape of the
rescue. -/

/-- Split a word at the first occurrence of `x` in chronological order. -/
theorem exists_split_first {ws : List Card} {x : Card} (h : x ∈ ws) :
    ∃ pre post, ws = playWord (pre ++ x :: post) ∧ x ∉ pre := by
  obtain ⟨pre, post, hsplit, hpre⟩ :=
    exists_append_cons_of_mem (l := ws.reverse) (c := x) (by simpa using h)
  refine ⟨pre, post, ?_, hpre⟩
  rw [show playWord (pre ++ x :: post) = (pre ++ x :: post).reverse from rfl,
    ← hsplit]
  simp

/-- **THE PRE-TWIN DECOMPOSITION.**  Split a licensed word at the first
chronological `c.twin`; at the split state `z` both `c` and `c.twin` are
`S`-live. -/
theorem pretwin_decomposition
    {u v : State} {c : Card} {ws : List Card}
    (hu : u.WF) (hc : CanRaiseS u c) (hρ : RaiseSSeqLicensed u ws v)
    (hself : c ∉ ws) (htwin : c.twin ∈ ws) :
    ∃ (pre post : List Card) (z : State),
      ws = playWord (pre ++ c.twin :: post) ∧ c.twin ∉ pre ∧
      RaiseSSeqLicensed u (playWord pre) z ∧
      RaiseSSeqLicensed z (playWord (c.twin :: post)) v ∧
      z.WF ∧ CanRaiseS z c ∧ CanRaiseS z c.twin := by
  obtain ⟨pre, post, hws, hpreNoTwin⟩ := exists_split_first htwin
  have hρ' : RaiseSSeqLicensed u (playWord (pre ++ c.twin :: post)) v := by
    rwa [hws] at hρ
  obtain ⟨z, hprePlay, hsufPlay⟩ :=
    RaiseSSeqLicensed.split_chron (A := pre) (R := c.twin :: post) hρ'
  have hz : z.WF := RaiseSSeqLicensed.wf hprePlay hu
  have hselfPre : c ∉ playWord pre := by
    intro hmem
    apply hself
    rw [hws, playWord_append]
    exact List.mem_append_right _ hmem
  have htwinPre : c.twin ∉ playWord pre := by
    intro hmem
    exact hpreNoTwin (by simpa [playWord] using hmem)
  have hcZ : CanRaiseS z c :=
    canRaiseS_of_word_notMem hprePlay hu hc hselfPre htwinPre
  have hsuf' : RaiseSSeqLicensed z (playWord ([c.twin] ++ post)) v := by
    simpa using hsufPlay
  obtain ⟨z1, hhead, -⟩ :=
    RaiseSSeqLicensed.split_chron (A := [c.twin]) (R := post) hsuf'
  have hctZ : CanRaiseS z c.twin :=
    canRaiseS_of_raiseSSeqLicensed_head (by simpa [playWord] using hhead)
  exact ⟨pre, post, z, hws, hpreNoTwin, hprePlay, hsufPlay, hz, hcZ, hctZ⟩

/-- **FORK OR BOTH-VANILLA DRAIN, WITH THE WORD.**  At the pre-twin state the
drain dichotomy yields either a fork, or a licensed raise play whose endpoint has
both twins vanilla and the spectrum collapsed onto them.  Unlike
`spectrum_pair_fork_or_both` this keeps the drain's word, which the rescue
needs. -/
theorem pretwin_fork_or_both_drain {z : State} {c : Card} (hz : z.WF)
    (hc : CanRaiseS z c) (hct : CanRaiseS z c.twin) :
    Fork z ∨
      ∃ wsD z', RaiseSSeqLicensed z wsD z' ∧
        (∀ d, CanRaiseS z' d → d = c ∨ d = c.twin) ∧
        CanRaise z' c ∧ CanRaise z' c.twin := by
  obtain ⟨wsD, z', hD, hsub, horb, hx', hxt'⟩ :=
    SpectrumCollapse.spectrum_pair_by_draining_live hz hc hct
  cases hb : tabToFoundR z' c.twin with
  | false =>
      have hblk : ¬ CanRaise z' c.twin := by
        intro h
        have htrue : tabToFoundR z' c.twin = true :=
          (tabToFoundR_iff_canRaise z' c.twin).mpr h
        rw [hb] at htrue
        exact Bool.noConfusion htrue
      exact Or.inl
        (SpectrumCollapse.spectrum_pair_fork_of_blocked horb hx' hxt' hsub hblk)
  | true =>
      have hvt : CanRaise z' c.twin := (tabToFoundR_iff_canRaise z' c.twin).mp hb
      cases ha : tabToFoundR z' c with
      | false =>
          have hblk : ¬ CanRaise z' c := by
            intro h
            have htrue : tabToFoundR z' c = true :=
              (tabToFoundR_iff_canRaise z' c).mpr h
            rw [ha] at htrue
            exact Bool.noConfusion htrue
          exact Or.inl
            (SpectrumCollapse.spectrum_pair_fork_of_flipped_blocked horb hx' hxt' hsub hblk)
      | true =>
          exact Or.inr ⟨wsD, z', hD, hsub,
            (tabToFoundR_iff_canRaise z' c).mp ha, hvt⟩

/-- **THE REFINED RESIDUAL.**  In the both-vanilla drain arm, build the
extension from the prefix + drain word.  This is now a statement about the
drained pair, not about the dead post-twin endpoint. -/
def PreTwinRescue : Prop :=
  ∀ {u v z z' : State} {c : Card} {ws pre post wsD : List Card},
    u.WF → CanRaiseS u c → RaiseSSeqLicensed u ws v →
      c ∉ ws → c.twin ∈ ws →
      ws = playWord (pre ++ c.twin :: post) →
      RaiseSSeqLicensed u (playWord pre) z →
      RaiseSSeqLicensed z wsD z' →
      (∀ d, CanRaiseS z' d → d = c ∨ d = c.twin) →
      CanRaise z' c → CanRaise z' c.twin →
      RaiseExtension u c v

/-- **THE `post = []` RESCUE, PROVED.**  When `c.twin` is the last raise of the
original word, the drained both-vanilla endpoint is enough: raise `c`, then
`c.twin` (the square), and the endpoint dominates the old endpoint because the
old endpoint raised `c.twin` and the drain only adds rungs.  This closes the
o0 board and shows the shape of the general rescue. -/
theorem preTwinRescue_post_nil
    {u v z z' : State} {c : Card} {ws pre post wsD : List Card}
    (hu : u.WF) (hprePlay : RaiseSSeqLicensed u (playWord pre) z)
    (hD : RaiseSSeqLicensed z wsD z')
    (hcanC : CanRaise z' c) (hcanCT : CanRaise z' c.twin)
    (hsuf : RaiseSSeqLicensed z (playWord (c.twin :: post)) v)
    (hpost : post = []) :
    RaiseExtension u c v := by
  subst hpost
  have hz : z.WF := RaiseSSeqLicensed.wf hprePlay hu
  have hz' : z'.WF := RaiseSSeqLicensed.wf hD hz
  have hsuf' : RaiseSSeqLicensed z [c.twin] v := by simpa [playWord] using hsuf
  obtain ⟨-, zc, z2, -, -, hC1, hCT2⟩ :=
    twin_raise_square_both hz' hcanC hcanCT
  have hstepC : RaiseSSeqLicensed z' [c] zc :=
    RaiseSSeqLicensed.cons (RaiseSSeqLicensed.nil z')
      (CanRaiseS.now c hcanC) (Steps.refl z') hC1
  have hcanCT_zc : CanRaise zc c.twin :=
    canRaise_of_raise_sameRank hz' hC1 rfl (card_twin_ne_self c) hcanCT
  have hstepCT : RaiseSSeqLicensed zc [c.twin] z2 :=
    RaiseSSeqLicensed.cons (RaiseSSeqLicensed.nil zc)
      (CanRaiseS.now c.twin hcanCT_zc) (Steps.refl zc) hCT2
  have hboth : RaiseSSeqLicensed z' ([c.twin] ++ [c]) z2 :=
    RaiseSSeqLicensed.append hstepC hstepCT
  have hresZ : RaiseSSeqLicensed z (([c.twin] ++ [c]) ++ wsD) z2 :=
    RaiseSSeqLicensed.append hD hboth
  refine ⟨(([c.twin] ++ [c]) ++ wsD) ++ playWord pre, z2,
    RaiseSSeqLicensed.append hprePlay hresZ, by simp, ?_⟩
  intro σ
  have hvR := hsuf'.rungAt_eq σ
  have hz2R := hresZ.rungAt_eq σ
  rw [hvR, hz2R]
  have hcount : [c.twin].countP (fun d => decide (d.suit = σ)) ≤
      (([c.twin] ++ [c]) ++ wsD).countP (fun d => decide (d.suit = σ)) := by
    rw [List.countP_append, List.countP_append]
    omega
  exact Nat.add_le_add_left hcount _

/-! ## §3. The twin-dead residual, precisely -/

/-- **THE TWIN-DEAD RESCUE.**  This is the only missing input of the pull case
in the existential form: when `c.twin` occurs in the word and `c` dies at the
endpoint, some licensed play from the pull landing must revive `c` (raising the
cards covering it), or the class must fork.

This is a *vertex* statement on the `u`-side.  It deliberately does not mention
the pull or the target `t`; the reduction below consumes it through
`pull_case_of_extension`. -/
def TwinRescue : Prop :=
  ∀ {u v : State} {c : Card} {ws : List Card},
    u.WF → CanRaiseS u c → RaiseSSeqLicensed u ws v →
      c ∉ ws → c.twin ∈ ws → ¬ CanRaiseS v c →
      RaiseExtension u c v ∨ Fork u

/-- **`PreTwinRescue` gives the twin rescue.**  Split at the first `c.twin`,
apply `pretwin_fork_or_both_drain`; the fork arm lifts back along the prefix,
the drain arm is `PreTwinRescue`. -/
theorem twinRescue_of_preTwinRescue (hp : PreTwinRescue) : TwinRescue := by
  intro u v c ws hu hcU hρ hmem htwin hdead
  -- sort the original word: the pre-twin split is invariant, and the endpoint
  -- rungs are unchanged, so this is free
  have hρrev : RaiseSSeqLicensed u (playWord ws.reverse) v := by
    simpa [playWord] using hρ
  obtain ⟨vₛ, hρₛ⟩ := sortable (P := ws.reverse) hu hρrev
  let wsₛ : List Card := playWord (sortByRank ws.reverse)
  have hρₛ' : RaiseSSeqLicensed u wsₛ vₛ := hρₛ
  have hperm : wsₛ.Perm ws := by
    change (sortByRank ws.reverse).reverse.Perm ws
    have h := perm_reverse (sortByRank_perm ws.reverse)
    rwa [List.reverse_reverse] at h
  have hmemₛ : c ∉ wsₛ := fun h => hmem (hperm.mem_iff.mp h)
  have htwinₛ : c.twin ∈ wsₛ := hperm.mem_iff.mpr htwin
  obtain ⟨pre, post, z, hws, _hpreNoTwin, hprePlay, _hsufPlay, hz, hcZ, hctZ⟩ :=
    pretwin_decomposition hu hcU hρₛ' hmemₛ htwinₛ
  rcases pretwin_fork_or_both_drain hz hcZ hctZ with hf | hD
  · exact Or.inr (fork_of_raiseSSeqLicensed hprePlay hu hf)
  · obtain ⟨wsD, z', hDplay, hsub, hcanC, hcanCT⟩ := hD
    have hextₛ : RaiseExtension u c vₛ :=
      hp hu hcU hρₛ' hmemₛ htwinₛ hws hprePlay hDplay hsub hcanC hcanCT
    obtain ⟨wsE, w, hE, hcE, hle⟩ := hextₛ
    have hrung : ∀ σ, rungAt v σ = rungAt vₛ σ :=
      rungAt_eq_of_perm hρ hρₛ' hperm.symm
    exact Or.inl ⟨wsE, w, hE, hcE, fun σ => by rw [hrung σ]; exact hle σ⟩

/-- **THE DEAD-ENDPOINT REVIVAL.**  This is the vertex form of the sketch,
stated in the exact dead-twin context: from the endpoint `v` of a licensed play
that avoided `c` and raised `c.twin`, a further raise-only play either revives
`c` (or raises it outright, putting it in the word), or the class forks.  In
words: *raise the cards covering `c` (all of rank below `c`); if `c` cannot be
revived, fork.* -/
def DeadRevive : Prop :=
  ∀ {u v : State} {c : Card} {ws : List Card},
    u.WF → CanRaiseS u c → RaiseSSeqLicensed u ws v →
      c ∉ ws → c.twin ∈ ws → ¬ CanRaiseS v c →
      (∃ wsR w, RaiseSSeqLicensed v wsR w ∧ (c ∈ wsR ∨ CanRaiseS w c)) ∨ Fork v

/-- **`DeadRevive` gives the twin rescue.**  Concatenate the original word with
the revival play from its endpoint; if the revival ends with `c` live, append
`c` as well.  The fork arm lifts back along the play's orbit. -/
theorem twinRescue_of_deadRevive (hd : DeadRevive) : TwinRescue := by
  intro u v c ws hu hcU hρ hmem htwin hdead
  rcases hd hu hcU hρ hmem htwin hdead with ⟨wsR, w, hres, hrev⟩ | hfv
  · rcases hrev with hmemR | hlivew
    · -- `c` was raised by the revival: append the revival word to the original
      refine Or.inl ⟨wsR ++ ws, w, RaiseSSeqLicensed.append hρ hres, ?_,
        RungMono.rungAt_le hres⟩
      exact List.mem_append_left ws hmemR
    · -- `c` is live at the revival endpoint: append it too
      obtain ⟨w', hres'⟩ := exists_append_raise hres hlivew
      refine Or.inl ⟨(c :: wsR) ++ ws, w', RaiseSSeqLicensed.append hρ hres',
        ?_, RungMono.rungAt_le hres'⟩
      exact List.mem_append_left ws (by simp)
  · -- the revival play is a raise-only orbit walk from `v`
    exact Or.inr (fork_of_sameOrbit (hρ.revEqW hu) hfv)

/-- **The existential pull case.**  Split on whether `c` is in the word
(extension with the word itself), live at the endpoint, or dead.  In the dead
case the twin is forced into the word (`twin_mem_of_dead`), and `TwinRescue`
supplies the extension or the fork. -/
theorem pull_case_existential
    (hres : TwinRescue)
    {s u t v : State} {c : Card} {b : Base} {ws : List Card}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hρ : RaiseSSeqLicensed u ws v) (ht : RungLe t v) :
    (∃ ws w, RaiseSSeqLicensed s ws w ∧ RungLe s w ∧ RungLe t w) ∨ Fork s := by
  have hu : u.WF := step_wf hs hpull
  have hv : v.WF := hρ.wf hu
  have hcU : CanRaiseS u c := SatDifferConfig.canRaiseS_after_pull hs hpull
  have hfork_s_of_u : Fork u → Fork s := by
    intro hf
    have hrev : reversibleAtW s (Move.foundToTab c b) :=
      reversible_mirrorW hpull (step_tabToFound_of_foundToTab hs hpull)
    have hsu : sameOrbitSetoid.r u s := sameOrbit_of_revStep hrev hpull
    exact fork_of_sameOrbit hsu hf
  by_cases hmem : c ∈ ws
  · -- `c` is already in the word: the word itself is an extension
    have hext : RaiseExtension u c v := ⟨ws, v, hρ, hmem, fun _ => Nat.le_refl _⟩
    obtain ⟨ws', w, hplay, hsw, hvw⟩ := pull_case_of_extension hs hpull hext
    exact Or.inl ⟨ws', w, hplay, hsw, fun σ => Nat.le_trans (ht σ) (hvw σ)⟩
  · by_cases hliveB : canRaiseSB v c = true
    · -- endpoint still live: append `c`
      have hlive : CanRaiseS v c := (canRaiseSB_iff hv).mp hliveB
      have hext : RaiseExtension u c v := raiseExtension_of_end_live hρ hlive
      obtain ⟨ws', w, hplay, hsw, hvw⟩ := pull_case_of_extension hs hpull hext
      exact Or.inl ⟨ws', w, hplay, hsw, fun σ => Nat.le_trans (ht σ) (hvw σ)⟩
    · have hlive : ¬ CanRaiseS v c :=
        fun h => hliveB ((canRaiseSB_iff hv).mpr h)
      by_cases htwin : c.twin ∈ ws
      · -- the only residual: twin raised, `c` dead
        rcases hres hu hcU hρ hmem htwin hlive with hext | hf
        · obtain ⟨ws', w, hplay, hsw, hvw⟩ := pull_case_of_extension hs hpull hext
          exact Or.inl ⟨ws', w, hplay, hsw, fun σ => Nat.le_trans (ht σ) (hvw σ)⟩
        · exact Or.inr (hfork_s_of_u hf)
      · -- twin-free: the licence persists
        have hext : RaiseExtension u c v :=
          raiseExtension_of_noTwin hu hρ hcU hmem htwin
        obtain ⟨ws', w, hplay, hsw, hvw⟩ := pull_case_of_extension hs hpull hext
        exact Or.inl ⟨ws', w, hplay, hsw, fun σ => Nat.le_trans (ht σ) (hvw σ)⟩

/-! ## §4. Assembly: the path induction with the existential pull case -/

/-- **RAISE-OR-FORK from an existential pull hypothesis.**  The path induction of
`Orig2/Fork/Commute/RaisesOrForkMain.lean` only ever consumes the pull case; the other four
reversible letters are already unconditional. -/
theorem raises_or_fork_of_pullExist
    (hPull : ∀ {s u t v : State} {c : Card} {b : Base} {ws : List Card},
      s.WF → State.step s (Move.foundToTab c b) = some u →
      RaiseSSeqLicensed u ws v → RungLe t v →
      (∃ ws' v', RaiseSSeqLicensed s ws' v' ∧ RungLe s v' ∧ RungLe t v')
      ∨ Fork s) :
    ∀ s t : State, s.WF → sameOrbitSetoid.r s t →
      (∃ ws v, RaiseSSeqLicensed s ws v ∧ RungLe s v ∧ RungLe t v) ∨ Fork s := by
  intro s t hs h
  obtain ⟨_, _, play, hplay⟩ := h
  exact raises_or_fork_play hPull hplay hs

/-- **RAISE-OR-FORK from `TwinRescue`.**  The only non-structural input is the
twin-dead rescue; every other branch of the pull case is decided. -/
theorem raises_or_fork_of_twinRescue (hres : TwinRescue) :
    ∀ s t : State, s.WF → sameOrbitSetoid.r s t →
      (∃ ws v, RaiseSSeqLicensed s ws v ∧ RungLe s v ∧ RungLe t v) ∨ Fork s :=
  raises_or_fork_of_pullExist
    (fun hs hpull hρ ht => pull_case_existential hres hs hpull hρ ht)

/-- **`FullJoinAtLeastOrFork` from `TwinRescue`.**  The join witness is the
endpoint of the existential raise play, exactly as in
`fullJoinAtLeastOrFork_of_raises_or_fork`. -/
theorem fullJoinAtLeastOrFork_of_twinRescue (hres : TwinRescue) :
    FullJoinAtLeastOrFork :=
  fullJoinAtLeastOrFork_of_raises_or_fork (raises_or_fork_of_twinRescue hres)

/-- **RAISE-OR-FORK from `DeadRevive`.** -/
theorem raises_or_fork_of_deadRevive (hd : DeadRevive) :
    ∀ s t : State, s.WF → sameOrbitSetoid.r s t →
      (∃ ws v, RaiseSSeqLicensed s ws v ∧ RungLe s v ∧ RungLe t v) ∨ Fork s :=
  raises_or_fork_of_twinRescue (twinRescue_of_deadRevive hd)

/-- **`FullJoinAtLeastOrFork` from `DeadRevive`.**  This is the restructured
end point: the fixed-word `hPull` is gone, the dead-twin board is handled by an
enlarged word, and the only remaining input is the vertex revival statement. -/
theorem fullJoinAtLeastOrFork_of_deadRevive (hd : DeadRevive) :
    FullJoinAtLeastOrFork :=
  fullJoinAtLeastOrFork_of_raises_or_fork (raises_or_fork_of_deadRevive hd)

/-- **RAISE-OR-FORK from the pre-twin residual.** -/
theorem raises_or_fork_of_preTwinRescue (hp : PreTwinRescue) :
    ∀ s t : State, s.WF → sameOrbitSetoid.r s t →
      (∃ ws v, RaiseSSeqLicensed s ws v ∧ RungLe s v ∧ RungLe t v) ∨ Fork s :=
  raises_or_fork_of_twinRescue (twinRescue_of_preTwinRescue hp)

/-- **`FullJoinAtLeastOrFork` from the pre-twin residual.**  This is the
sharpest end point: the fork is taken at the pre-twin state (where the twin pair
is still live), and the only remaining input is the rescue from the drained
both-vanilla arm. -/
theorem fullJoinAtLeastOrFork_of_preTwinRescue (hp : PreTwinRescue) :
    FullJoinAtLeastOrFork :=
  fullJoinAtLeastOrFork_of_raises_or_fork (raises_or_fork_of_preTwinRescue hp)

end OneColourClosure

#print axioms OneColourClosure.exists_raiseClimb_saturated
#print axioms OneColourClosure.raiseExtension_of_end_live
#print axioms OneColourClosure.raiseExtension_of_noTwin
#print axioms OneColourClosure.fork_of_raiseSSeqLicensed
#print axioms OneColourClosure.merge_lower_higher
#print axioms OneColourClosure.bubble_front_notwin
#print axioms OneColourClosure.suffix_insert_notwin
#print axioms OneColourClosure.merge_notwin
#print axioms OneColourClosure.revive_drain
#print axioms OneColourClosure.canRaise_of_canRaiseS_of_twin_founded
#print axioms OneColourClosure.postTwinRescue_of_live
#print axioms OneColourClosure.extension_of_postTwinRescue
#print axioms OneColourClosure.extension_of_postTwinLive
#print axioms OneColourClosure.pull_case_of_extension
#print axioms OneColourClosure.exists_split_first
#print axioms OneColourClosure.pretwin_decomposition
#print axioms OneColourClosure.pretwin_fork_or_both_drain
#print axioms OneColourClosure.preTwinRescue_post_nil
#print axioms OneColourClosure.pull_case_existential
#print axioms OneColourClosure.twinRescue_of_preTwinRescue
#print axioms OneColourClosure.twinRescue_of_deadRevive
#print axioms OneColourClosure.raises_or_fork_of_pullExist
#print axioms OneColourClosure.raises_or_fork_of_twinRescue
#print axioms OneColourClosure.fullJoinAtLeastOrFork_of_twinRescue
#print axioms OneColourClosure.raises_or_fork_of_deadRevive
#print axioms OneColourClosure.fullJoinAtLeastOrFork_of_deadRevive
#print axioms OneColourClosure.raises_or_fork_of_preTwinRescue
#print axioms OneColourClosure.fullJoinAtLeastOrFork_of_preTwinRescue
