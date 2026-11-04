import Orig2.Fork.Commute.RaisesOrForkMain

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
the existential pull case, and `raises_or_fork_of_twinRescue` feeds it to the
path induction of `RaisesOrForkMain`; `PullCommute` later discharges `TwinRescue`
by commutation.

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

/-! ## §1c'. The twin-free merge (no rank separation)

If `H` merely avoids `l` and `l.twin`, then `l`'s licence survives `H`
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
`L ; H` is playable from `s`.  There is no rank separation between `L` and
`H`. -/
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

end OneColourClosure

#print axioms OneColourClosure.raiseExtension_of_end_live
#print axioms OneColourClosure.raiseExtension_of_noTwin
#print axioms OneColourClosure.fork_of_raiseSSeqLicensed
#print axioms OneColourClosure.bubble_front_notwin
#print axioms OneColourClosure.suffix_insert_notwin
#print axioms OneColourClosure.merge_notwin
#print axioms OneColourClosure.pull_case_of_extension
#print axioms OneColourClosure.exists_split_first
#print axioms OneColourClosure.pretwin_decomposition
#print axioms OneColourClosure.pull_case_existential
#print axioms OneColourClosure.raises_or_fork_of_pullExist
#print axioms OneColourClosure.raises_or_fork_of_twinRescue
