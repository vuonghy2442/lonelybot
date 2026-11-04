import Orig2.Fork.Commute.PullExtension

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-!
# Temp/PullCommute — the pre-twin good arm by commutation

`Temp/PullExtension` isolates the good arm as `PostTwinLive`: after the original
`c.twin` letter, a low revive drain must keep `c` `S`-live (and its twin
founded).  This card replaces that route by a direct commutation argument.

At the pre-twin state `z`:

* the low rescue `rescue` (all ranks below `c.rank`) reaches `zs`, where both
  `c` and `c.twin` are vanilla-raisable;
* the original twin letter runs `z --c.twin--> t`, followed by the tail `post`;
* `post` is ascending and every tail rank is strictly above `c.rank`.

Build the chronological play `rescue ; c ; c.twin` from `z` (the pair fires at
`zs`, and `canRaise_of_raise_sameRank` keeps `c.twin` vanilla after raising
`c`), then `bubble_front` moves `c.twin` to the chronological front.  Splitting
the bubble at `c.twin` gives a landing `t_b` whose single-letter twin play from
`z` is an equal-rung orbit mate of the original landing `t`, so the tail replays
from `t_b` (`replay_of_orbit_rung`).  Finally `merge_lower_higher` appends the
tail, since the rescue and `c` are strictly below every tail letter.

House rules: no `sorry`, no `Classical`, no `noncomputable`, no new axioms.
-/

namespace OneColourClosure

/-- Local spelling of the twin irreflexivity row (the promoted tree no longer
carries the scratch copy). -/
theorem card_twin_ne_self (c : Card) : c.twin ≠ c := card_twin_ne c

/-- Membership in `sortByRank P` is membership in `P`. -/
theorem mem_sortByRank_iff {P : List Card} {d : Card} :
    d ∈ sortByRank P ↔ d ∈ P :=
  (sortByRank_perm P).mem_iff

/-- **THE PRE-TWIN GOOD ARM, BY COMMUTATION.**  From the low rescue at the
pre-twin state (both twins vanilla at its endpoint), the original twin letter
and the ascending high tail, build a licensed raise play from `z` that contains
`c` and dominates the tail endpoint. -/
theorem preTwin_goodArm
    {z t v : State} {c : Card} {rescue post : List Card} {zs : State}
    (hz : z.WF)
    (hrescue : RaiseSSeqLicensed z rescue zs)
    (hrescueRank : ∀ d ∈ rescue, d.rank.toIdx < c.rank.toIdx)
    (hcanC : CanRaise zs c) (hcanCT : CanRaise zs c.twin)
    (htwin : RaiseSSeqLicensed z [c.twin] t)
    (htail : RaiseSSeqLicensed t (playWord post) v)
    (hpostAsc : post.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx))
    (hpostGe : ∀ d ∈ post, c.rank.toIdx ≤ d.rank.toIdx)
    (hcPost : c ∉ post) (hctPost : c.twin ∉ post) :
    RaiseExtension z c v := by
  -- chronological, ascending low rescue
  let L : List Card := sortByRank rescue.reverse
  have hLasc : L.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) :=
    sortByRank_asc rescue.reverse
  have hLperm : L.Perm rescue :=
    (sortByRank_perm rescue.reverse).trans (reverse_perm rescue)
  have hLrank : ∀ d ∈ L, d.rank.toIdx < c.rank.toIdx :=
    fun d hd => hrescueRank d (hLperm.mem_iff.mp hd)
  have hrescueRev : RaiseSSeqLicensed z (playWord rescue.reverse) zs := by
    simpa [playWord] using hrescue
  obtain ⟨zs', hrescue'raw⟩ := sortable (P := rescue.reverse) hz hrescueRev
  have hrescue' : RaiseSSeqLicensed z (playWord L) zs' := by
    simpa [L] using hrescue'raw
  have hzs'wf : zs'.WF := RaiseSSeqLicensed.wf hrescue' hz
  -- the pair fires at the original low-rescue endpoint `zs`
  have hzswf : zs.WF := RaiseSSeqLicensed.wf hrescue hz
  obtain ⟨zc, hcstep⟩ := step_tabToFound_of_canRaise hcanC
  have hcplay : RaiseSSeqLicensed zs [c] zc :=
    RaiseSSeqLicensed.cons (RaiseSSeqLicensed.nil zs)
      (CanRaiseS.now c hcanC) (Steps.refl zs) hcstep
  have hcanCT_zc : CanRaise zc c.twin :=
    canRaise_of_raise_sameRank hzswf hcstep (Card.twin_rank c)
      (card_twin_ne c) hcanCT
  obtain ⟨z2, hctstep⟩ := step_tabToFound_of_canRaise hcanCT_zc
  have hctplay : RaiseSSeqLicensed zc [c.twin] z2 :=
    RaiseSSeqLicensed.cons (RaiseSSeqLicensed.nil zc)
      (CanRaiseS.now c.twin hcanCT_zc) (Steps.refl zc) hctstep
  have hpair : RaiseSSeqLicensed zs (playWord [c, c.twin]) z2 := by
    have h := RaiseSSeqLicensed.append hcplay hctplay
    simpa [playWord] using h
  -- transfer the pair play to the sorted rescue endpoint `zs'`
  have hpermRescue : (playWord L).Perm rescue := by
    rw [playWord]
    exact (perm_reverse hLperm).trans (reverse_perm rescue)
  have hrungRescue : ∀ σ, rungAt zs' σ = rungAt zs σ :=
    rungAt_eq_of_perm hrescue' hrescue hpermRescue
  have horbRescue : sameOrbitSetoid.r zs' zs :=
    revEqW_of_raise_plays hz hrescue hrescue'
  obtain ⟨z2', hpair', -, -⟩ :=
    replay_of_orbit_rung hzs'wf horbRescue hrungRescue hpair
  -- the full chronological play `rescue ; c ; c.twin`
  have hfull : RaiseSSeqLicensed z (playWord (L ++ [c, c.twin])) z2' := by
    have h := RaiseSSeqLicensed.append hrescue' hpair'
    simpa [playWord, List.append_assoc] using h
  -- bubble `c.twin` to the front of `L ++ [c]`
  have hAasc : (L ++ [c]).Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) := by
    rw [List.pairwise_append]
    exact ⟨hLasc, List.Pairwise.cons (fun b hb => absurd hb List.not_mem_nil)
        List.Pairwise.nil, by
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      exact Nat.le_of_lt (hLrank a ha)⟩
  have hctnotA : c.twin ∉ L ++ [c] := by
    intro hmem
    rcases List.mem_append.mp hmem with hL | hc
    · have hlt := hLrank c.twin hL
      rw [Card.twin_rank] at hlt
      exact Nat.lt_irrefl _ hlt
    · rw [List.mem_singleton] at hc
      exact card_twin_ne c hc
  have hArank : ∀ a ∈ L ++ [c], a.rank.toIdx ≤ c.twin.rank.toIdx := by
    intro a ha
    rw [Card.twin_rank]
    rcases List.mem_append.mp ha with hL | hc
    · exact Nat.le_of_lt (hLrank a hL)
    · rw [List.mem_singleton] at hc
      subst hc
      exact Nat.le_refl _
  have hctZ : CanRaiseS z c.twin :=
    canRaiseS_of_raiseSSeqLicensed_head htwin
  obtain ⟨wb, hbubble⟩ :=
    bubble_front (L ++ [c]) hz hAasc hctnotA hArank hctZ (by
      simpa [List.append_assoc] using hfull)
  -- split off the bubble landing `t_b`
  obtain ⟨t_b, htb, hlow⟩ :=
    RaiseSSeqLicensed.split_chron (A := [c.twin]) (R := L ++ [c]) (by
      simpa [List.append_assoc] using hbubble)
  -- `t_b` and the original landing `t` are equal-rung orbit mates
  have htwin' : RaiseSSeqLicensed z (playWord [c.twin]) t := by
    simpa [playWord] using htwin
  have htbwf : t_b.WF := RaiseSSeqLicensed.wf htb hz
  have horb_tb : sameOrbitSetoid.r t_b t :=
    revEqW_of_raise_plays hz htwin' htb
  have hrung_tb : ∀ σ, rungAt t_b σ = rungAt t σ :=
    rungAt_eq_of_perm htb htwin' (List.Perm.refl [c.twin])
  -- replay the tail from the bubble landing
  obtain ⟨v_b, hpost_b, hrung_v, -⟩ :=
    replay_of_orbit_rung htbwf horb_tb hrung_tb htail
  -- disjointness for the twin-free merge: rescue ranks are below `c.rank`, and
  -- every `post` rank is at or above it (from the sorted split)
  have hdisjL : ∀ l ∈ L ++ [c], l ∉ post ∧ l.twin ∉ post := by
    intro l hl
    rcases List.mem_append.mp hl with hL | hc'
    · have hlt : l.rank.toIdx < c.rank.toIdx := hLrank l hL
      have hltT : l.twin.rank.toIdx < c.rank.toIdx := by
        simpa [Card.twin_rank] using hlt
      refine ⟨?_, ?_⟩
      · intro hp
        have hge := hpostGe l hp
        omega
      · intro hp
        have hge := hpostGe l.twin hp
        omega
    · rw [List.mem_singleton] at hc'
      subst hc'
      exact ⟨hcPost, hctPost⟩
  have hdisjH : ∀ h ∈ post, h ∉ L ++ [c] ∧ h.twin ∉ L ++ [c] := by
    intro h hh
    have hge : c.rank.toIdx ≤ h.rank.toIdx := hpostGe h hh
    have hgeT : c.rank.toIdx ≤ h.twin.rank.toIdx := by
      simpa [Card.twin_rank] using hge
    refine ⟨?_, ?_⟩
    · intro hmem
      rcases List.mem_append.mp hmem with hL | hc'
      · have hlt := hLrank h hL
        omega
      · rw [List.mem_singleton] at hc'
        exact hcPost (hc' ▸ hh)
    · intro hmem
      rcases List.mem_append.mp hmem with hL | hc'
      · have hlt := hLrank h.twin hL
        omega
      · rw [List.mem_singleton] at hc'
        have hh_twin : h = c.twin := by
          calc h = h.twin.twin := (card_twin_twin h).symm
            _ = c.twin := by rw [hc']
        exact hctPost (hh_twin ▸ hh)
  -- append the tail with the twin-free merge
  obtain ⟨w2, hmerge⟩ :=
    merge_notwin (L ++ [c]) hAasc hpostAsc hdisjL hdisjH htbwf hlow hpost_b
  -- assemble from `z`: twin letter, then the low pair, then the tail
  have hfinal : RaiseSSeqLicensed z (playWord (c.twin :: ((L ++ [c]) ++ post))) w2 := by
    have h := RaiseSSeqLicensed.append htb hmerge
    simpa [playWord, List.append_assoc] using h
  refine ⟨playWord (c.twin :: ((L ++ [c]) ++ post)), w2, hfinal, ?_, ?_⟩
  · rw [playWord, List.mem_reverse]
    simp [List.append_assoc]
  · intro σ
    rw [hrung_v σ, hpost_b.rungAt_eq σ, hmerge.rungAt_eq σ]
    have hcount : (playWord post).countP (fun d => decide (d.suit = σ)) ≤
        (playWord ((L ++ [c]) ++ post)).countP
          (fun d => decide (d.suit = σ)) := by
      rw [show playWord ((L ++ [c]) ++ post) =
          playWord post ++ playWord (L ++ [c]) from by
        simp [playWord, List.append_assoc]]
      rw [List.countP_append]
      exact Nat.le_add_right _ _
    exact Nat.add_le_add_left hcount _

/-! ## §2. The low rescue and the saturated asymmetry

Copied (under new names) from `Temp/PullInsert`, which cannot be imported here
because of the `PullReplay` module conflict. -/

theorem commute_pairwise_append_right_tail : ∀ (A B : List Card) (m : Card),
    (A ++ m :: B).Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) →
    (m :: B).Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) := by
  intro A
  induction A with
  | nil => intro B m h; simpa using h
  | cons x t ih =>
      intro B m h
      rw [List.cons_append] at h
      exact ih B m ((List.pairwise_cons.mp h).2)

/-- Every letter of a licensed word has its suit's rung strictly past its rank
index at the endpoint. -/
theorem play_fired_rung_floor : ∀ {s z : State} {ws : List Card},
    RaiseSSeqLicensed s ws z → ∀ (hwf : s.WF) (d : Card), d ∈ ws →
    d.rank.toIdx < rungAt z d.suit := by
  intro s z ws h
  induction h with
  | nil => intro _ d hd; cases hd
  | @cons s1 z1 z0 card ws1 htail hS hp hstep ih =>
      intro hwf d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · have hnext1 : s1.nextUp d = true :=
          ((canRaiseS_split (RaiseSSeqLicensed.wf htail hwf)).mp hS).1
        have hnext0 : z1.nextUp d = true :=
          (nextUp_cargoPath hp d).trans hnext1
        have hrung0 : d.rank.toIdx = rungAt z1 d.suit := by
          simpa [State.nextUp, State.foundHeight, rungAt] using
            of_decide_eq_true hnext0
        obtain ⟨hclimb, -⟩ := RungMono.rungAt_raiseStepS ⟨z1, hp, hstep⟩
        have hcargo : rungAt s1 d.suit = rungAt z1 d.suit :=
          rungAt_cargoPath hp d.suit
        omega
      · have hfloor := ih hwf d hd
        obtain ⟨hclimb, hfix⟩ := RungMono.rungAt_raiseStepS ⟨z1, hp, hstep⟩
        by_cases hds : d.suit = card.suit
        · have hcargo : rungAt s1 d.suit = rungAt z1 d.suit :=
            rungAt_cargoPath hp d.suit
          rw [← hds] at hclimb
          omega
        · rw [hfix d.suit hds]
          exact hfloor

/-- A licensed word has no duplicates. -/
theorem play_licensed_nodup : ∀ {s z : State} {ws : List Card},
    RaiseSSeqLicensed s ws z → s.WF → ws.Nodup := by
  intro s z ws h
  induction h with
  | nil => intro _; exact List.nodup_nil
  | @cons s1 z1 z0 card ws1 htail hS hp hstep ih =>
      intro hwf
      refine List.pairwise_cons.mpr ⟨?_, ih hwf⟩
      intro b hb hcon
      rw [hcon] at hS
      have hfloor := play_fired_rung_floor htail hwf b hb
      obtain ⟨w, hpath, hcan⟩ := hS
      have hnext : w.nextUp b = true := hcan.1
      have hrungw : b.rank.toIdx = rungAt w b.suit := by
        simpa [State.nextUp, State.foundHeight, rungAt] using
          of_decide_eq_true hnext
      have hrungs1 : rungAt s1 b.suit = rungAt w b.suit :=
        rungAt_cargoPath hpath b.suit
      omega

/-- A list is duplicate-free if its reversal is. -/
theorem nodup_of_nodup_reverse : ∀ {l : List Card}, l.reverse.Nodup → l.Nodup := by
  intro l
  induction l with
  | nil => intro _; exact List.nodup_nil
  | cons a t ih =>
      intro h
      rw [List.reverse_cons] at h
      have ht : t.reverse.Nodup := (List.nodup_append.mp h).1
      have hdisj := (List.nodup_append.mp h).2.2
      refine List.nodup_cons.mpr ⟨?_, ih ht⟩
      intro ha
      exact (hdisj a (List.mem_reverse.mpr ha) a (List.mem_singleton_self a)) rfl

/-! ## §1b. Local spectrum rows

The two rows of the old `SpectrumCollapse` card that this file consumes, copied
here so that the spectrum file can be removed. -/

/-- **Raising an outside card preserves both twins' `S`-licence.**  The rank
split is the brief's: a letter of a different rank is licence-inert
(`canRaiseS_step_of_rank_ne`), and a letter of the twins' rank other than the
twins is inert (`SatDifferConfig.licence_lost_only_by_twin`). -/
theorem drain_pair_stays_live' {z z' : State} {d x : Card} (hz : z.WF)
    (hstep : RaiseStepS z z' d)
    (hd : d ≠ x) (hdt : d ≠ x.twin)
    (hx : CanRaiseS z x) (hxt : CanRaiseS z x.twin) :
    CanRaiseS z' x ∧ CanRaiseS z' x.twin := by
  have hx' : CanRaiseS z' x := by
    by_cases hr : d.rank = x.rank
    · exact SatDifferConfig.licence_lost_only_by_twin hz hstep hr hd hdt hx
    · exact canRaiseS_step_of_rank_ne hz hstep hr hx
  have hxt' : CanRaiseS z' x.twin := by
    by_cases hr : d.rank = x.rank
    · have hr' : d.rank = x.twin.rank := by
        rw [Card.twin_rank]; exact hr
      exact SatDifferConfig.licence_lost_only_by_twin hz hstep hr' hdt
        (by simpa [card_twin_twin] using hd) hxt
    · have hr' : d.rank ≠ x.twin.rank := by
        rw [Card.twin_rank]; exact hr
      exact canRaiseS_step_of_rank_ne hz hstep hr' hxt
  exact ⟨hx', hxt'⟩

/-- **A `RaiseStepS` letter climbs the rank sum by exactly one.**  The cargo
prefix is rung-inert and the raise bumps exactly one suit; the sum is
`Drain.rungSum`. -/
theorem rungSum_raiseStepS' {z z' : State} {d : Card} (h : RaiseStepS z z' d) :
    Drain.rungSum z' = Drain.rungSum z + 1 := by
  unfold Drain.rungSum
  obtain ⟨hclimb, hfix⟩ := RungMono.rungAt_raiseStepS h
  have hmap : (Suit.all.map (fun s => rungAt z' s)) =
      Suit.all.map (fun s => if s = d.suit then rungAt z s + 1 else rungAt z s) := by
    apply List.map_congr_left
    intro σ _
    by_cases hσ : σ = d.suit
    · rw [ite_eq_left hσ, hσ]
      exact hclimb
    · rw [ite_eq_right hσ]
      exact hfix σ hσ
  rw [hmap]
  exact Drain.sum_map_ite_bump Suit.all (fun s => rungAt z s) d.suit
    Drain.suit_all_nodup (Suit.mem_all d.suit)

/-- **The low drain.**  Raise any `S`-live card of rank strictly below `x`'s,
keeping both twins `S`-live, until none remains. -/
theorem lowDrainCommute_aux (x : Card) (n : Nat) :
    ∀ z : State, z.WF → 52 - Drain.rungSum z ≤ n →
      CanRaiseS z x → CanRaiseS z x.twin →
      ∃ ws z', RaiseSSeqLicensed z ws z' ∧
        (∀ d ∈ ws, d.rank.toIdx < x.rank.toIdx) ∧
        (∀ d, CanRaiseS z' d → x.rank.toIdx ≤ d.rank.toIdx) ∧
        sameOrbitSetoid.r z z' ∧
        CanRaiseS z' x ∧ CanRaiseS z' x.twin := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro z hz hle hx hxt
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
          have hnilrank : ∀ d ∈ ([] : List Card), d.rank.toIdx < x.rank.toIdx := by
            intro d hd; cases hd
          exact ⟨[], z, RaiseSSeqLicensed.nil z, hnilrank, hfloor,
            sameOrbitSetoid.iseqv.refl z, hx, hxt⟩
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
          have hdx : d ≠ x := by intro h; subst h; exact Nat.lt_irrefl _ hlt
          have hdxt : d ≠ x.twin := by
            intro h; subst h; rw [Card.twin_rank] at hlt
            exact Nat.lt_irrefl _ hlt
          obtain ⟨z', hstepS⟩ := raiseStepS_of_canRaiseS hSc
          have hpair :=
            drain_pair_stays_live' hz hstepS hdx hdxt hx hxt
          have hsum : Drain.rungSum z' = Drain.rungSum z + 1 :=
            rungSum_raiseStepS' hstepS
          have hz' : z'.WF := raiseStepS_wf hz hstepS
          have hlt' : 52 - Drain.rungSum z' < n := by
            have hbound : Drain.rungSum z' ≤ 52 := Drain.rungSum_le_52 hz'
            omega
          obtain ⟨ws, w, hpath, hranks, hfloor, horb, hwx, hwxt⟩ :=
            ih (52 - Drain.rungSum z') hlt' z' hz' (Nat.le_refl _)
              hpair.1 hpair.2
          obtain ⟨z₀, hp, hs⟩ := hstepS
          have hletter : RaiseSSeqLicensed z [d] z' :=
            RaiseSSeqLicensed.cons (RaiseSSeqLicensed.nil z) hSc hp hs
          have hfull : RaiseSSeqLicensed z (ws ++ [d]) w :=
            RaiseSSeqLicensed.append hletter hpath
          refine ⟨ws ++ [d], w, hfull, ?_, hfloor,
            RevEqW_symm (RaiseSSeqLicensed.revEqW hfull hz), hwx, hwxt⟩
          intro e he
          rcases List.mem_append.mp he with he | he
          · exact hranks e he
          · rw [List.mem_singleton] at he; rw [he]; exact hlt

/-- The low drain, non-recursively. -/
theorem lowDrainCommute {z : State} {x : Card} (hz : z.WF)
    (hx : CanRaiseS z x) (hxt : CanRaiseS z x.twin) :
    ∃ ws z', RaiseSSeqLicensed z ws z' ∧
      (∀ d ∈ ws, d.rank.toIdx < x.rank.toIdx) ∧
      (∀ d, CanRaiseS z' d → x.rank.toIdx ≤ d.rank.toIdx) ∧
      sameOrbitSetoid.r z z' ∧
      CanRaiseS z' x ∧ CanRaiseS z' x.twin :=
  lowDrainCommute_aux x (52 - Drain.rungSum z) z hz (Nat.le_refl _) hx hxt

/-- The saturated asymmetry closes the fork arm. -/
theorem fork_of_lowAsym {s zs : State} {c : Card}
    (horb : sameOrbitSetoid.r s zs) (hzs : zs.WF)
    (hcan : CanRaise zs c) (hlive : CanRaiseS zs c.twin)
    (hblock : ¬ CanRaise zs c.twin)
    (hfloor : ∀ d, CanRaiseS zs d → c.rank.toIdx ≤ d.rank.toIdx) :
    Fork s := by
  obtain ⟨F, hF, hfs⟩ :=
    DrainClose.fork_exists_of_asymmetry hzs hcan hlive hblock hfloor
  obtain ⟨w, hwit⟩ := forkState_iff.mp hfs
  exact ⟨F, w, sameOrbitSetoid.iseqv.trans horb hF, hwit⟩

/-- The flipped orientation (the twin is the vanilla one). -/
theorem fork_of_lowAsym' {s zs : State} {c : Card}
    (horb : sameOrbitSetoid.r s zs) (hzs : zs.WF)
    (hcan : CanRaise zs c.twin) (hlive : CanRaiseS zs c)
    (hblock : ¬ CanRaise zs c)
    (hfloor : ∀ d, CanRaiseS zs d → c.rank.toIdx ≤ d.rank.toIdx) :
    Fork s := by
  have hlive' : CanRaiseS zs (c.twin.twin) := by
    rw [card_twin_twin]; exact hlive
  have hblock' : ¬ CanRaise zs (c.twin.twin) := by
    rw [card_twin_twin]; exact hblock
  have hfloor' : ∀ d, CanRaiseS zs d → c.twin.rank.toIdx ≤ d.rank.toIdx := by
    intro d hd; rw [Card.twin_rank]; exact hfloor d hd
  exact fork_of_lowAsym (c := c.twin) horb hzs hcan hlive' hblock' hfloor'

/-! ## §3. The remaining input and the commuted `TwinRescue` -/

/-- **THE SATURATED DEADLOCK INPUT.**  At a rank floor, both twins `S`-live
cannot both be vanilla-blocked.  (Identical to `Temp/PullInsert`'s
`SatDeadlock`; it is the only non-fork branch left at the drained pair.) -/
def SatDeadlockCommute : Prop :=
  ∀ (zs : State) (c : Card),
    zs.WF → CanRaiseS zs c → CanRaiseS zs c.twin →
    (∀ d, CanRaiseS zs d → c.rank.toIdx ≤ d.rank.toIdx) →
    CanRaise zs c ∨ CanRaise zs c.twin

/-- **THE SATURATED DEADLOCK IS VACUOUS — PROVED.**  A covered card tops no
pile (`tfc_seat_parent`), while the flat characterization of the *other*
twin's license forces that other twin to top a pile: if the run above it were
empty it would be vanilla (`CanRaise`), and otherwise its `run-or-twin` clause
says its twin — the first card — tops a pile.  So both twins cannot be
covered; hence at least one is vanilla.  The rank floor is not needed. -/
theorem satDeadlockCommute : SatDeadlockCommute := by
  intro zs c hzs hcS hctS _hfloor
  by_cases hcT : tabToFoundR zs c = true
  · exact Or.inl ((tabToFoundR_iff_canRaise zs c).mp hcT)
  · have hnotC : ¬ CanRaise zs c :=
      fun h => hcT ((tabToFoundR_iff_canRaise zs c).mpr h)
    by_cases hctT : tabToFoundR zs c.twin = true
    · exact Or.inr ((tabToFoundR_iff_canRaise zs c.twin).mp hctT)
    · exfalso
      have hnotT : ¬ CanRaise zs c.twin :=
        fun h => hctT ((tabToFoundR_iff_canRaise zs c.twin).mpr h)
      -- both twins would be covered
      have hcovC : CoveredAt zs c :=
        (canRaise_or_covered hzs hcS).resolve_left hnotC
      -- a covered card tops no pile
      obtain ⟨d, hdseat⟩ := hcovC
      obtain ⟨ad, hhold, -, hlast⟩ := tfc_seatOf_of_inr hdseat
      have hnoneC : zs.pileOfTop c = none :=
        (tfc_seat_parent hzs hhold hlast).2
      -- the flat shape of the other twin
      obtain ⟨hnextT, aT, bsT, runT, hshapeT, hseatT, hdisjT⟩ :=
        canRaiseS_flat_necessity hzs hctS
      cases runT with
      | nil =>
          -- an empty run above `c.twin` makes it vanilla
          have hcanT : CanRaise zs c.twin := by
            refine ⟨hnextT, aT, ?_, ?_⟩
            · rw [pileOfTop_eq_some_iff hzs]
              show lastOf (zs.piles aT).faceUp = some c.twin
              rw [hshapeT]
              exact lastOf_snoc
            · rw [hshapeT]
              rcases hseatT with hbs | hk
              · exact Or.inl (by rw [chop_snoc]; exact hbs)
              · exact Or.inr hk
          exact hnotT hcanT
      | cons d rest =>
          -- otherwise the twin tops a pile, i.e. `c` tops a pile
          have htwinTop : zs.pileOfTop c.twin.twin ≠ none :=
            hdisjT.resolve_left (by simp)
          rw [card_twin_twin] at htwinTop
          exact htwinTop hnoneC

/-- **`TwinRescue` FROM THE COMMUTATION GOOD ARM + THE FORK ARM.**  Sort the
word, split at the first twin letter, split off the original twin landing `t`
and the tail `post`, run the low rescue at the pre-twin state, and case on the
vanilla reads at the drained pair:

* both vanilla ⇒ `preTwin_goodArm` (the commutation) gives the extension;
* one vanilla ⇒ the saturated asymmetry is a fork;
* both blocked ⇒ `SatDeadlockCommute`.

The sorted split makes the tail ranks weakly above `c.rank`, and the rescue ranks
strictly below it, so the only missing input is the deadlock.  The tail merge is
`merge_notwin` (card-disjointness only). -/
theorem twinRescue_proved : TwinRescue := by
  intro u v c ws hu hcU hρ hmem htw hdead
  -- sort the original word
  have hρrev : RaiseSSeqLicensed u (playWord ws.reverse) v := by
    simpa [playWord] using hρ
  obtain ⟨vS, hρS⟩ := sortable (P := ws.reverse) hu hρrev
  let wsS : List Card := playWord (sortByRank ws.reverse)
  have hρS' : RaiseSSeqLicensed u wsS vS := hρS
  have hperm : wsS.Perm ws := by
    change (sortByRank ws.reverse).reverse.Perm ws
    have h := perm_reverse (sortByRank_perm ws.reverse)
    rwa [List.reverse_reverse] at h
  have hmemS : c ∉ wsS := fun h => hmem (hperm.mem_iff.mp h)
  have htwinS : c.twin ∈ wsS := hperm.mem_iff.mpr htw
  -- split at the first chronological twin letter
  obtain ⟨pre, post, z, hws, -, hprePlay, hsufPlay, hz, hcZ, hctZ⟩ :=
    pretwin_decomposition hu hcU hρS' hmemS htwinS
  -- split off the original twin landing `t` and the tail
  obtain ⟨t, htwinW, htailW⟩ :=
    RaiseSSeqLicensed.split_chron (A := [c.twin]) (R := post)
      (by simpa [List.append_assoc] using hsufPlay)
  have htwin : RaiseSSeqLicensed z [c.twin] t := by
    simpa [playWord] using htwinW
  have htail : RaiseSSeqLicensed t (playWord post) vS := htailW
  -- the sorted order supplies ascendingness of the chronological word
  have hchron : sortByRank ws.reverse = pre ++ c.twin :: post := by
    have h := congrArg List.reverse hws
    simpa [wsS, playWord] using h
  have hAscAll : (pre ++ c.twin :: post).Pairwise
      (fun a b => a.rank.toIdx ≤ b.rank.toIdx) := by
    rw [← hchron]
    exact sortByRank_asc ws.reverse
  have hctAsc : (c.twin :: post).Pairwise
      (fun a b => a.rank.toIdx ≤ b.rank.toIdx) :=
    commute_pairwise_append_right_tail pre post c.twin hAscAll
  have hpostAsc : post.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) :=
    (List.pairwise_cons.mp hctAsc).2
  have hpostGe : ∀ d ∈ post, c.rank.toIdx ≤ d.rank.toIdx := by
    intro d hd
    have h := asc_head_le_all hctAsc d (List.mem_cons_of_mem c.twin hd)
    simpa [Card.twin_rank] using h
  -- the sorted word is duplicate-free, so `c.twin` occurs only at the split
  have hnodupS : wsS.Nodup := play_licensed_nodup hρS' hu
  have hnodupSort : (sortByRank ws.reverse).Nodup := by
    have hwsS : wsS = (sortByRank ws.reverse).reverse := by
      simp [wsS, playWord]
    rw [hwsS] at hnodupS
    exact nodup_of_nodup_reverse hnodupS
  have hnodupTwinPost : (pre ++ c.twin :: post).Nodup := by
    rw [← hchron]
    exact hnodupSort
  have hmid : (c.twin :: post).Nodup :=
    (List.nodup_append.mp hnodupTwinPost).2.1
  have hctPost : c.twin ∉ post := (List.nodup_cons.mp hmid).1
  have hcPost : c ∉ post := by
    intro hp
    apply hmemS
    rw [hws]
    exact List.mem_reverse.mpr
      (List.mem_append_right pre (List.mem_cons_of_mem c.twin hp))
  -- the low rescue at the pre-twin state
  obtain ⟨rescue, zs, hrescue, hrescueRank, hfloor, horbZ, hzsC, hzsT⟩ :=
    lowDrainCommute hz hcZ hctZ
  have hzswf : zs.WF := RaiseSSeqLicensed.wf hrescue hz
  -- case on the vanilla reads at the drained pair
  by_cases hc1 : tabToFoundR zs c = true
  · by_cases hc2 : tabToFoundR zs c.twin = true
    · -- both vanilla: the commutation gives the extension
      have hcanC : CanRaise zs c := (tabToFoundR_iff_canRaise zs c).mp hc1
      have hcanT : CanRaise zs c.twin :=
        (tabToFoundR_iff_canRaise zs c.twin).mp hc2
      obtain ⟨wsG, wG, hplayG, hcG, hleG⟩ :=
        preTwin_goodArm hz hrescue hrescueRank hcanC hcanT htwin htail
          hpostAsc hpostGe hcPost hctPost
      have hplayU : RaiseSSeqLicensed u (wsG ++ playWord pre) wG :=
        RaiseSSeqLicensed.append hprePlay hplayG
      have hrungv : ∀ σ, rungAt v σ = rungAt vS σ :=
        rungAt_eq_of_perm hρ hρS' hperm.symm
      refine Or.inl ⟨wsG ++ playWord pre, wG, hplayU,
        List.mem_append_left _ hcG, ?_⟩
      intro σ
      rw [hrungv σ]
      exact hleG σ
    · -- (T,F): `c` vanilla, the twin blocked — the fork arm
      have hcanC : CanRaise zs c := (tabToFoundR_iff_canRaise zs c).mp hc1
      have hnotT : ¬ CanRaise zs c.twin :=
        fun h => hc2 ((tabToFoundR_iff_canRaise zs c.twin).mpr h)
      exact Or.inr (fork_of_raiseSSeqLicensed hprePlay hu
        (fork_of_lowAsym horbZ hzswf hcanC hzsT hnotT hfloor))
  · -- `c` blocked: the flipped fork or the deadlock
    have hnotC : ¬ CanRaise zs c :=
      fun h => hc1 ((tabToFoundR_iff_canRaise zs c).mpr h)
    by_cases hc3 : tabToFoundR zs c.twin = true
    · -- (F,T): the twin vanilla — the flipped asymmetry
      have hcanT : CanRaise zs c.twin :=
        (tabToFoundR_iff_canRaise zs c.twin).mp hc3
      exact Or.inr (fork_of_raiseSSeqLicensed hprePlay hu
        (fork_of_lowAsym' horbZ hzswf hcanT hzsC hnotC hfloor))
    · -- (F,F): the deadlock is vacuous
      have hnotT : ¬ CanRaise zs c.twin :=
        fun h => hc3 ((tabToFoundR_iff_canRaise zs c.twin).mpr h)
      rcases satDeadlockCommute zs c hzswf hzsC hzsT hfloor with hc | hc
      · exact absurd hc hnotC
      · exact absurd hc hnotT

/-- **RAISE-OR-FORK from the commutation input.** -/
theorem raises_or_fork :
    ∀ s t : State, s.WF → sameOrbitSetoid.r s t →
      (∃ ws v, RaiseSSeqLicensed s ws v ∧ RungLe s v ∧ RungLe t v) ∨ Fork s :=
  raises_or_fork_of_twinRescue twinRescue_proved

/-- **`FullJoinAtLeastOrFork` from the commutation input.** -/
theorem fullJoinAtLeastOrFork_proved :
    FullJoinAtLeastOrFork :=
  fullJoinAtLeastOrFork_of_raises_or_fork raises_or_fork

/-- A saturated state admits no nonempty licensed raise word. -/
theorem raiseSSeqLicensed_eq_nil_of_ssaturated {u w : State} {ws : List Card}
    (hsat : SSaturated u) (h : RaiseSSeqLicensed u ws w) : ws = [] := by
  cases hnil : ws with
  | nil => rfl
  | cons c ws' =>
      have hrevne : ws.reverse ≠ [] := by simp [hnil]
      obtain ⟨d, rest, hrev⟩ := List.exists_cons_of_ne_nil hrevne
      have hws : ws = playWord ([d] ++ rest) := by
        have h1 : ws = (d :: rest).reverse := by
          rw [← hrev, List.reverse_reverse]
        rw [h1, playWord]
        simp
      have h' : RaiseSSeqLicensed u (playWord ([d] ++ rest)) w := by
        rwa [hws] at h
      obtain ⟨u1, hsingle, -⟩ :=
        RaiseSSeqLicensed.split_chron (A := [d]) (R := rest) h'
      have hd : CanRaiseS u d :=
        canRaiseS_of_raiseSSeqLicensed_head (by simpa [playWord] using hsingle)
      exact absurd hd (hsat d)

/-- A class-mate of a `WF` state is `WF` (local copy of the one row the final
chain used from `ForklessTop_Main`). -/
theorem wf_of_sameOrbit {u v : State} (hcls : sameOrbitSetoid.r u v)
    (hu : u.WF) : v.WF := by
  obtain ⟨σ, hσ, τ, hτ⟩ := hcls
  exact run_wf hu (Walk_run _ hτ)

/-- **`SatDifferForkWF` FROM `raises_or_fork`.**  At saturated endpoints the
only licensed raise word is empty, so the join from `u` forces `v ≤ u` and the
join from `v` forces `u ≤ v`; differing rungs make that impossible, leaving the
fork arm. -/
theorem satDifferForkWF_proved : SatDifferForkWF := by
  intro u v hu hsu hsv hcls hdiff
  have hv : v.WF := wf_of_sameOrbit hcls hu
  rcases raises_or_fork u v hu hcls with ⟨ws, w, hplay, huw, hvw⟩ | hfork
  · have hws : ws = [] := raiseSSeqLicensed_eq_nil_of_ssaturated hsu hplay
    subst hws
    have hwu : w = u := by cases hplay; rfl
    have hvu : RungLe v u := by simpa [hwu] using hvw
    rcases raises_or_fork v u hv (sameOrbitSetoid.iseqv.symm hcls) with
      ⟨ws2, w2, hplay2, hvw2, huw2⟩ | hfork2
    · have hws2 : ws2 = [] := raiseSSeqLicensed_eq_nil_of_ssaturated hsv hplay2
      subst hws2
      have hw2v : w2 = v := by cases hplay2; rfl
      have huv : RungLe u v := by simpa [hw2v] using huw2
      obtain ⟨σ, hσ⟩ := hdiff
      exact absurd (Nat.le_antisymm (huv σ) (hvu σ)) hσ
    · obtain ⟨F, x, hF, hx⟩ := hfork2
      exact ⟨F, x, sameOrbitSetoid.iseqv.trans hcls hF, hx⟩
  · exact hfork

end OneColourClosure

#print axioms OneColourClosure.mem_sortByRank_iff
#print axioms OneColourClosure.preTwin_goodArm
#print axioms OneColourClosure.commute_pairwise_append_right_tail
#print axioms OneColourClosure.play_fired_rung_floor
#print axioms OneColourClosure.play_licensed_nodup
#print axioms OneColourClosure.nodup_of_nodup_reverse
#print axioms OneColourClosure.lowDrainCommute_aux
#print axioms OneColourClosure.lowDrainCommute
#print axioms OneColourClosure.fork_of_lowAsym
#print axioms OneColourClosure.fork_of_lowAsym'
#print axioms OneColourClosure.satDeadlockCommute
#print axioms OneColourClosure.twinRescue_proved
#print axioms OneColourClosure.raises_or_fork
#print axioms OneColourClosure.fullJoinAtLeastOrFork_proved
#print axioms OneColourClosure.raiseSSeqLicensed_eq_nil_of_ssaturated
#print axioms OneColourClosure.satDifferForkWF_proved
