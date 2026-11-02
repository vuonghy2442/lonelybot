import Orig2.ForkSatChain
import Orig2.Fork.Local.ForkCommute
import Orig2.Fork.Local.ForkCommuteSlide

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkGap — the king branch and the pull-in-tail branches, at the S-grade

Scratch card.  READ-ONLY on `Orig2/`; no source edit, no commit.  Zero `sorry`,
zero `Classical.choice`, zero `nativeDecide`; no `decide` over `State`.

## What this card does

`Blocks.NoSeatMateCrossSuit` is reduced at the *S-grade* (`CanRaiseS`, the
saturation grade) rather than at the vanilla raise grade:

* §1 `pull_kill_shape`: a pull can destroy a card's **S-licence** only in three
  shapes — it pulls in the card's own suit, it lands on the card, or it lands
  on the card's *twin*.  Every other pull leaves the S-licence intact.  (The
  vanilla chain's `Chain.blocking_letter_shape` had a fourth, *slide* shape;
  covers never kill the S-licence — `Direct.canRaiseS_survives_slide`.)
* §2 `pull_kill_descends`: from a pull kill, the pulled card sits exactly one
  rank below the killed card and is S-live at the pull's image.  So a pull kill
  *descends the S-chain by one full rank*.
* §3 `mate_raise_kill_buried`: `raise d.twin` can destroy `d`'s S-licence only
  if `d` is **not a pile top** at that moment.
* §4 `first_Skill`: the first letter at which a card's S-licence dies, with the
  full five-shape classification and the extra data of §2/§3.
* §5 `skill_chain`: the S-chain.  From `CanRaiseS B d` into a saturated `v`, the
  play carries a `raise z` with `z.rank ≤ d.rank`.  Unlike `Chain.chain_exists`
  there is **no stall clause**: the S-chain always terminates in a raise.
* §6 `king_pullFree`: the king branch (`c`, `d` both kings, `d ≠ c.twin`) over a
  pull-free tail raises `d` or `d.twin`.

Then §7 names the exact surviving residual and closes
`Blocks.NoSeatMateCrossSuit` modulo it.
-/

namespace Gap

open CommuteStep

/-! ## §0. The twin of a card is not the card -/

theorem card_twin_ne (c : Card) : c.twin ≠ c := by
  intro h
  exact Suit.twin_ne c.suit (congrArg Card.suit h)

/-! ## §1. A pull kills the S-licence only in three shapes -/

/-- **A PULL'S S-KILL SHAPE.**  If `d` is S-live at `st` and S-dead at the
landing `st'` of the pull `foundToTab e b`, then the pull either pulls in `d`'s
own suit, or lands on `d`, or lands on `d.twin`.

Proof: read the flat characterization (`canRaiseS_flat_necessity`) at `st` and
transport it to `st'` (`canRaiseS_flat_sufficiency`).  `nextUp d` survives any
pull outside `d.suit`; `d`'s pile survives unless the pull lands on it; and the
twin-top clause survives unless the pull lands on `d.twin`. -/
theorem pull_kill_shape {st st' : State} {e d : Card} {b : Base}
    (hwf : st.WF) (hstep : State.step st (Move.foundToTab e b) = some st')
    (hlive : CanRaiseS st d) (hdead : ¬ CanRaiseS st' d) :
    e.suit = d.suit ∨ b = Sum.inr d ∨ b = Sum.inr d.twin := by
  obtain ⟨c', htop0, hc', hcp, hst'⟩ := step_foundToTab_inv hstep
  cases hc'
  have hst'' : st' = pullSt st e b := hst'
  by_cases hsu : e.suit = d.suit
  · exact Or.inl hsu
  · by_cases hbd : b = Sum.inr d
    · exact Or.inr (Or.inl hbd)
    · by_cases hbt : b = Sum.inr d.twin
      · exact Or.inr (Or.inr hbt)
      · exfalso
        have hst'wf : st'.WF := step_wf hwf hstep
        obtain ⟨hnext, a, bs, run, hface, hseat, hdistw⟩ :=
          canRaiseS_flat_necessity hwf hlive
        have hfound : e ∈ st.found e.suit := lastOf_mem htop0
        obtain ⟨k, hk⟩ := exists_tgt_of_canPlace hcp
        have hcz : ∀ {m : Anchor}, st.pileOfTop d.twin = some m → e ≠ d.twin := by
          intro m hz he
          have hmf : d.twin ∈ st.found d.twin.suit := by rw [← he]; exact hfound
          exact ((mem_found_unique hwf hmf).1 m).2 (lastOf_mem (pileOfTop_top hz).2)
        have hkm : ∀ {m : Anchor}, st.pileOfTop d.twin = some m → k ≠ m := by
          intro m hz hkm
          cases hb : b with
          | inl a0 =>
              have hcp' : st.canPlace e (Sum.inl a0) = true := by rw [hb] at hcp; exact hcp
              obtain ⟨hemp, -⟩ := canPlace_inl hcp'
              have ha0 : a0 = k := by rw [hb] at hk; simpa using hk
              have hne : (st.piles a0).faceUp ≠ [] := by
                have hp := (pileOfTop_top hz).1
                rwa [← hkm, ← ha0] at hp
              exact hne ((Pile.isEmpty_eq _).mp hemp).2
          | inr z =>
              have hz' : st.pileOfTop z = some k := by rw [hb] at hk; simpa using hk
              have ht1 : (st.piles k).top = some z := (pileOfTop_eq_some_iff hwf).mp hz'
              have ht2 : (st.piles k).top = some d.twin := by
                have h := (pileOfTop_eq_some_iff hwf).mp hz
                rw [← hkm] at h
                exact h
              exact hbt (by rw [hb, Option.some.inj (ht1.symm.trans ht2)])
        have hnext' : st'.nextUp d = true := by
          have hfh : (st'.found d.suit).length = (st.found d.suit).length := by
            rw [hst'', pullSt_found_apply, ite_eq_right (fun h => hsu h.symm)]
          unfold State.nextUp at hnext
          show decide (d.rank.toIdx = (st'.found d.suit).length) = true
          rw [hfh]
          exact hnext
        have hdistW : run = [] ∨ st.pileOfTop d.twin ≠ none := hdistw
        by_cases hka : k = a
        · -- the pull lands on `d`'s own pile
          rw [← hka] at hface hseat
          cases hb : b with
          | inl a0 =>
              have hcp' : st.canPlace e (Sum.inl a0) = true := by rw [hb] at hcp; exact hcp
              obtain ⟨hemp, -⟩ := canPlace_inl hcp'
              have ha0 : a0 = k := by rw [hb] at hk; simpa using hk
              have hdmem : d ∈ (st.piles k).faceUp := by
                rw [hface]; exact List.mem_append_right _ (List.mem_cons_self ..)
              rw [ha0] at hemp
              obtain ⟨-, hfu⟩ := (Pile.isEmpty_eq _).mp hemp
              rw [hfu] at hdmem
              exact List.not_mem_nil hdmem
          | inr z =>
              have hz : st.pileOfTop z = some k := by rw [hb] at hk; simpa using hk
              have hpile : (st'.piles k) =
                  { (st.piles k) with faceUp := (st.piles k).faceUp ++ [e] } := by
                rw [hst'', hb, pullSt_piles_inr_apply st e z k hz k, ite_eq_left rfl]
              have hface' : (st'.piles k).faceUp = bs ++ d :: (run ++ [e]) := by
                rw [hpile]
                show (st.piles k).faceUp ++ [e] = bs ++ d :: (run ++ [e])
                rw [hface]
                simp only [List.cons_append, List.append_assoc]
              have hhid' : (st'.piles k).hidden = (st.piles k).hidden := by
                rw [hpile]
              have hrun_ne : run ≠ [] := by
                intro hr
                have htopd : (st.piles k).top = some d := by
                  show lastOf (st.piles k).faceUp = some d
                  rw [hface, hr]
                  exact lastOf_snoc
                have hzd : z = d :=
                  Option.some.inj (((pileOfTop_eq_some_iff hwf).mp hz).symm.trans htopd)
                exact hbd (by rw [hb, hzd])
              have hdist' : run ++ [e] = [] ∨ st'.pileOfTop d.twin ≠ none := by
                right
                intro hnone
                cases hz2 : st.pileOfTop d.twin with
                | none => exact absurd hz2 (hdistW.resolve_left hrun_ne)
                | some m =>
                    have hm : st'.pileOfTop d.twin = some m := by
                      rw [hst'', pullSt_pileOfTop_ne hwf hk hfound hz2 (hkm hz2) (hcz hz2)]
                    rw [hm] at hnone
                    exact absurd hnone (by simp)
              exact hdead (canRaiseS_flat_sufficiency hst'wf
                ⟨hnext', k, bs, run ++ [e], hface', by rw [hhid']; exact hseat, hdist'⟩)
        · -- the pull writes another pile: the whole flat witness transfers
          exact hdead (canRaiseS_flat_sufficiency hst'wf
            ⟨hnext', a, bs, run,
              by rw [hst'', pullSt_piles_ne hk (fun h => hka h.symm)]; exact hface,
              by rw [hst'', pullSt_piles_ne hk (fun h => hka h.symm)]; exact hseat, by
                rcases hdistW with h | h
                · exact Or.inl h
                · right
                  intro hnone
                  cases hz : st.pileOfTop d.twin with
                  | none => exact absurd hz h
                  | some m =>
                      have hm : st'.pileOfTop d.twin = some m := by
                        rw [hst'', pullSt_pileOfTop_ne hwf hk hfound hz (hkm hz) (hcz hz)]
                      rw [hm] at hnone
                      exact absurd hnone (by simp)⟩)

/-! ## §2. The pull kill descends one rank -/

/-- **A PULL KILL DESCENDS.**  From the three shapes of §1 the pulled card `e`
sits exactly one rank below `d`, and it is S-live at the pull's image (a pull's
own card is always vanilla-live at its landing, `pull_card_canRaise`). -/
theorem pull_kill_descends {st st' : State} {e d : Card} {b : Base}
    (hwf : st.WF) (hstep : State.step st (Move.foundToTab e b) = some st')
    (hlive : CanRaiseS st d) (hdead : ¬ CanRaiseS st' d) :
    e.rank.toIdx + 1 = d.rank.toIdx ∧ CanRaiseS st' e := by
  have hnext : st.nextUp d = true := (canRaiseS_flat_necessity hwf hlive).1
  refine ⟨?_, CanRaiseS.now e (ValleyStep.pull_card_canRaise hwf hstep)⟩
  rcases pull_kill_shape hwf hstep hlive hdead with hsu | h | h
  · exact Chain.pull_below_rank hwf hstep hnext hsu
  · have hs : State.step st (Move.foundToTab e (Sum.inr d)) = some st' := by
      rw [← h]; exact hstep
    exact (Chain.pull_onto_rank hs).1
  · have hs : State.step st (Move.foundToTab e (Sum.inr d.twin)) = some st' := by
      rw [← h]; exact hstep
    have h1 := (Chain.pull_onto_rank hs).1
    rwa [Card.twin_rank] at h1

/-! ## §3. The twin raise kills only a buried card -/

/-- If `d` tops the very run `bs ++ d :: run`, then `run` is empty. -/
theorem lastOf_split_eq {bs run : List Card} {d : Card}
    (hok : runOK (bs ++ d :: run) = true)
    (h : lastOf (bs ++ d :: run) = some d) : run = [] := by
  cases run with
  | nil => rfl
  | cons y ys =>
      exfalso
      have h1 : lastOf (bs ++ d :: y :: ys) = lastOf (y :: ys) := by
        rw [show bs ++ d :: y :: ys = (bs ++ [d]) ++ (y :: ys) from by simp,
          lastOf_append_of_ne_nil (by simp)]
      rw [h1] at h
      have hmem : d ∈ (y :: ys) := lastOf_mem h
      have hok' : runOK ((bs ++ [d]) ++ (y :: ys)) = true := by
        rwa [show (bs ++ [d]) ++ (y :: ys) = bs ++ d :: y :: ys from by simp]
      have hlt := runOK_desc (P := bs ++ [d]) (S := y :: ys) (x := d)
        hok' (List.mem_append_right _ (List.mem_singleton_self d)) hmem
      omega

/-- **`raise d.twin` KILLS `d`'S S-LICENCE ONLY WHEN `d` IS NOT A PILE TOP.**
If `d` topped a pile, the flat witness for `d` has an empty run above it, and the
twin raise (which writes another pile, and another foundation column) leaves
every clause of that witness intact. -/
theorem mate_raise_kill_buried {A Z : State} {d : Card}
    (hAwf : A.WF) (hstep : State.step A (Move.tabToFound d.twin) = some Z)
    (hlive : CanRaiseS A d) (hdead : ¬ CanRaiseS Z d) :
    A.pileOfTop d = none := by
  cases htop : A.pileOfTop d with
  | none => rfl
  | some m =>
      exfalso
      obtain ⟨hnext, a, bs, run, hface, hseat, hdistw⟩ :=
        canRaiseS_flat_necessity hAwf hlive
      have hdmem : d ∈ (A.piles a).faceUp := by
        rw [hface]; exact List.mem_append_right _ (List.mem_cons_self ..)
      have htopm : (A.piles m).top = some d := (pileOfTop_eq_some_iff hAwf).mp htop
      have hdmemm : d ∈ (A.piles m).faceUp := Pile.mem_of_top htopm
      have ham : a = m := by
        by_cases h : a = m
        · exact h
        · exact absurd hdmemm ((mem_faceUp_unique hAwf hdmem m (fun hh => h hh.symm)).1)
      have hok : runOK (A.piles a).faceUp = true := hAwf.2.1 a
      have hok' : runOK (bs ++ d :: run) = true := by rw [← hface]; exact hok
      have hlast : lastOf (bs ++ d :: run) = some d := by
        rw [← hface]; rw [ham]; exact htopm
      have hrun : run = [] := lastOf_split_eq hok' hlast
      -- the twin raise's pile is another pile
      obtain ⟨-, a', hpa', hZeq⟩ := step_tabToFound_inv hstep
      have ha' : a' ≠ a := by
        intro h
        have hdtmem : d.twin ∈ (A.piles a).faceUp := by
          rw [← h]
          exact Pile.mem_of_top ((pileOfTop_eq_some_iff hAwf).mp hpa')
        exact card_twin_ne d (runOK_rank_distinct hok hdtmem hdmem (by rw [Card.twin_rank]))
      have hsuits : d.twin.suit ≠ d.suit := by
        intro h
        exact Suit.twin_ne d.suit h
      have hnextZ : Z.nextUp d = true := SafeTransport.nextUp_tabToFound_ne hstep hsuits hnext
      have hpileZ : Z.piles a = A.piles a :=
        SafeTransport.piles_tabToFound_ne hstep hpa' (fun h => ha' h.symm)
      have hZwf : Z.WF := step_wf hAwf hstep
      refine hdead (canRaiseS_flat_sufficiency hZwf ⟨hnextZ, a, bs, run, ?_, ?_, ?_⟩)
      · rw [hpileZ]; exact hface
      · rw [hpileZ]; exact hseat
      · rw [hrun]; exact Or.inl rfl

/-! ## §4. The first letter that kills the S-licence -/

/-- **THE FIRST S-KILL.**  A witness play from a state where `d` is S-live into
a state where it is S-dead has a *first* S-killing letter, split with both
witness plays retained, and classified by §1: it is `raise d`, `raise d.twin`,
or a pull of one of the three shapes. -/
theorem first_Skill {B v : State} {τ : List Move}
    (hplay : ShufflePlayW B τ v) :
    ∀ {d : Card}, B.WF → CanRaiseS B d → ¬ CanRaiseS v d →
      ∃ (s1 s2 : List Move) (A Z : State) (m : Move),
        τ = s1 ++ m :: s2 ∧ ShufflePlayW B s1 A ∧ A.WF ∧ CanRaiseS A d ∧
        reversibleAtW A m ∧ State.step A m = some Z ∧ ShufflePlayW Z s2 v ∧
        ¬ CanRaiseS Z d ∧
        (m = Move.tabToFound d ∨ m = Move.tabToFound d.twin ∨
          ∃ e b, m = Move.foundToTab e b ∧
            (e.suit = d.suit ∨ b = Sum.inr d ∨ b = Sum.inr d.twin)) := by
  induction hplay with
  | nil st =>
      intro d hwf hlive hdead
      exact absurd hlive hdead
  | @cons st s₁ W m ρ hrev hstep hrest ih =>
      intro d hwf hlive hdead
      have hs1wf : s₁.WF := step_wf hwf hstep
      haveI : Decidable (CanRaiseS s₁ d) :=
        decidable_of_iff (canRaiseSB s₁ d = true) (canRaiseSB_iff hs1wf)
      by_cases hkill : CanRaiseS s₁ d
      · obtain ⟨s1', s2, A, Z, m', heq, hp, hAwf, hlive', hrev', hstep', hp2, hdead', hshape⟩ :=
          ih hs1wf hkill hdead
        exact ⟨m :: s1', s2, A, Z, m', by rw [heq]; rfl, Walk.cons hrev hstep hp,
          hAwf, hlive', hrev', hstep', hp2, hdead', hshape⟩
      · refine ⟨[], ρ, st, s₁, m, rfl, Walk.nil st, hwf, hlive, hrev, hstep, hrest,
          hkill, ?_⟩
        cases m with
        | draw =>
            exact absurd (Direct.canRaiseS_survives_draw hwf hstep hlive) hkill
        | wasteToFound c =>
            exact absurd hrev (wasteToFound_not_reversibleAtW st c)
        | wasteToTab c b =>
            exact absurd hrev (wasteToTab_not_reversibleAtW st c b)
        | tabToTab x b =>
            exact absurd (Direct.canRaiseS_survives_slide hwf hstep hrev hlive) hkill
        | tabToFound c =>
            by_cases hc : c = d
            · exact Or.inl (by rw [hc])
            · by_cases hct : c = d.twin
              · exact Or.inr (Or.inl (by rw [hct]))
              · exact absurd (Direct.canRaiseS_survives_raise_of_ne hwf hstep hc hct hlive) hkill
        | foundToTab e b =>
            exact Or.inr (Or.inr ⟨e, b, rfl, pull_kill_shape hwf hstep hlive hkill⟩)

/-! ## §5. The S-chain terminates in a raise -/

/-- **THE S-CHAIN.**  From `CanRaiseS B d` into a `SSaturated` `v`, the play
carries a `raise z` with `z.rank ≤ d.rank`, where `z` is S-live just before the
raise and S-dead just after.  Because every non-raise first kill is a *pull*
that descends one full rank (§2), the recursion is well founded and — unlike
`Chain.chain_exists` — has **no stall clause** and no cover branch. -/
theorem skill_chain_aux (k : Nat) :
    ∀ (B v : State) (τ : List Move) (d : Card),
      d.rank.toIdx = k → B.WF → SSaturated v → CanRaiseS B d → ShufflePlayW B τ v →
      ∃ (z : Card) (s1 s2 : List Move) (A Z : State),
        z.rank.toIdx ≤ k ∧ τ = s1 ++ Move.tabToFound z :: s2 ∧
        ShufflePlayW B s1 A ∧ (CanRaiseS A z ∨ CanRaiseS A z.twin) ∧
        State.step A (Move.tabToFound z) = some Z ∧ ShufflePlayW Z s2 v := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
      intro B v τ d hk hB hv hlive hplay
      obtain ⟨s1, s2, A, Z, m, heq, hp, hAwf, hliveA, hrevA, hstepA, htail, hdeadZ,
        hshape⟩ := first_Skill hplay hB hlive (hv d)
      rcases hshape with hd | hdt | ⟨e, b, hm, hcase⟩
      · subst hd
        exact ⟨d, s1, s2, A, Z, by omega, heq, hp, Or.inl hliveA, hstepA, htail⟩
      · subst hdt
        exact ⟨d.twin, s1, s2, A, Z, by rw [Card.twin_rank]; omega, heq, hp,
          Or.inr (by rw [card_twin_twin]; exact hliveA), hstepA, htail⟩
      · subst hm
        obtain ⟨hrank, hliveZ⟩ := pull_kill_descends hAwf hstepA hliveA hdeadZ
        have hlt : e.rank.toIdx < k := by omega
        obtain ⟨z, s1', s2', A', Z', hle, heq', hp', hlive', hstep', htail'⟩ :=
          ih e.rank.toIdx hlt Z v s2 e rfl (step_wf hAwf hstepA) hv hliveZ htail
        refine ⟨z, s1 ++ Move.foundToTab e b :: s1', s2', A', Z', by omega, ?_, ?_,
          hlive', hstep', htail'⟩
        · rw [heq, heq']
          simp only [List.append_assoc, List.cons_append]
        · exact ShufflePlayW_append hp (Walk.cons hrevA hstepA hp')

/-- **THE S-CHAIN, UNROLLED.** -/
theorem skill_chain {B v : State} {τ : List Move} {d : Card}
    (hB : B.WF) (hv : SSaturated v) (hlive : CanRaiseS B d)
    (hplay : ShufflePlayW B τ v) :
    ∃ (z : Card) (s1 s2 : List Move) (A Z : State),
      z.rank.toIdx ≤ d.rank.toIdx ∧ τ = s1 ++ Move.tabToFound z :: s2 ∧
      ShufflePlayW B s1 A ∧ (CanRaiseS A z ∨ CanRaiseS A z.twin) ∧
      State.step A (Move.tabToFound z) = some Z ∧ ShufflePlayW Z s2 v :=
  skill_chain_aux d.rank.toIdx B v τ d rfl hB hv hlive hplay

/-! ## §6. The king branch over a pull-free tail -/

/-- **THE KING BRANCH RAISES `d` OR `d.twin`.**  In the king branch
(`c.rank = d.rank = king`, `d ≠ c.twin`) with a pull-free tail, the kill
dichotomy applies directly: `d` is S-live at the pull's landing and S-dead at
the saturated `v`, so the tail raises `d` or `d.twin`. -/
theorem king_pullFree {B v : State} {tail : List Move} {c d : Card}
    (hB : B.WF) (hv : SSaturated v) (hcan : CanRaise B d)
    (hplay : ShufflePlayW B tail v) (hpf : ∀ m ∈ tail, ¬ Bubble.IsPull m)
    (hdk : d.rank = Rank.king) (hck : c.rank = Rank.king) (hne : d ≠ c.twin) :
    (∃ s1 s2 : List Move, tail = s1 ++ Move.tabToFound d :: s2) ∨
      (∃ s1 s2 : List Move, tail = s1 ++ Move.tabToFound d.twin :: s2) := by
  rcases Direct.canRaiseS_end_or_bad_raise hplay hB hpf (CanRaiseS.now d hcan) with
    h | h | h
  · exact absurd h (hv d)
  · exact Or.inl h
  · exact Or.inr h

/-- **THE KING BRANCH'S MATE-RAISE CASE, EXACTLY.**  Over a pull-free tail that
never raises `d`, the first S-kill of `d` is `raise d.twin`, and at that moment
`d` is **not a pile top** (`mate_raise_kill_buried`).  At the corridor's pull
landing `d` *is* a bare pile top (`⟨[], [d]⟩`), so in a pull-free tail some
slide must have landed on `d` before the mate raise: the mate branch of the king
gap always carries a cover of `d` plus a raise of `d.twin`. -/
theorem king_mate_first_kill_buried
    {L v : State} {tail : List Move} {d : Card}
    (hL : L.WF) (hv : SSaturated v) (hcan : CanRaise L d)
    (hplay : ShufflePlayW L tail v) (hpf : ∀ m ∈ tail, ¬ Bubble.IsPull m)
    (hno : ∀ s1 s2 : List Move, tail ≠ s1 ++ Move.tabToFound d :: s2) :
    ∃ (s1 s2 : List Move) (A Z : State),
      tail = s1 ++ Move.tabToFound d.twin :: s2 ∧ ShufflePlayW L s1 A ∧ A.WF ∧
      CanRaiseS A d ∧ State.step A (Move.tabToFound d.twin) = some Z ∧
      ¬ CanRaiseS Z d ∧ A.pileOfTop d = none := by
  obtain ⟨s1, s2, A, Z, m, heq, hpre, hAwf, hlive, hrev, hstep, htail, hdead,
    hshape⟩ := first_Skill hplay hL (CanRaiseS.now d hcan) (hv d)
  rcases hshape with hd | hdt | ⟨e, b, hm, hcase⟩
  · have heq0 : tail = s1 ++ Move.tabToFound d :: s2 := by rw [heq, hd]
    exact absurd heq0 (hno s1 s2)
  · have hstep' : State.step A (Move.tabToFound d.twin) = some Z := by
      rw [← hdt]; exact hstep
    have heq' : tail = s1 ++ Move.tabToFound d.twin :: s2 := by rw [heq, hdt]
    exact ⟨s1, s2, A, Z, heq', hpre, hAwf, hlive, hstep', hdead,
      mate_raise_kill_buried hAwf hstep' hlive hdead⟩
  · exfalso
    refine hpf m ?_ ?_
    · rw [heq]; exact List.mem_append_right _ (List.mem_cons_self ..)
    · rw [hm]; exact ⟨e, b, rfl⟩

/-! ## §7. The exact residual, and the reduction -/

/-- **`SChainMateResidual`** — THE SURVIVING CARD RESIDUAL.  In a shortest
cross-suit corridor into a `SSaturated` endpoint, a raise of any S-live card `z`
of rank at most the pulled card `d`'s rank is a raise of `d` itself.  Stated at
the corridor (with the corridor's raise origin `A₀`, image `B₀`, free-interior
landing `P₀` and pull landing `L`), never over arbitrary plays — the
arbitrary-play form is refuted by `Sat.not_noChainRaiseCorr`'s two-raise board.

This is the card datum the S-chain leaves: `skill_chain` returns *some* terminal
raise, and this says that terminal is `d`.  The definition quantifies over every
such raise in the tail (a slightly stronger, sufficient form); it is one-sided —
`SSaturated u` is not used. -/
def SChainMateResidual : Prop :=
  ∀ (u v : State) (ρ pre γ tail : List Move) (c d : Card) (b : Base)
    (A₀ B₀ P₀ L : State),
    u.WF → SSaturated v → ShufflePlayW u ρ v →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
    ρ = pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))) →
    Canon.FreeOnly γ → c.suit ≠ d.suit →
    ShufflePlayW u pre A₀ → State.step A₀ (Move.tabToFound c) = some B₀ →
    ShufflePlayW B₀ γ P₀ → State.step P₀ (Move.foundToTab d b) = some L →
    ∀ (z : Card) (s1 s2 : List Move) (A Z : State),
      z.rank.toIdx ≤ d.rank.toIdx → tail = s1 ++ Move.tabToFound z :: s2 →
      ShufflePlayW L s1 A → (CanRaiseS A z ∨ CanRaiseS A z.twin) →
      State.step A (Move.tabToFound z) = some Z → z = d

/-- **`RelocationResidual`** — the same-card lane, with NO pull-freeness.  In a
shortest cross-suit corridor into a saturated endpoint the tail is never a
same-card relocation `(nonempty) ; raise d`.  This SUBSUMES
`Sat.TwinRelocationResidual` (which carries `d = c.twin` and a pull-free tail
besides). -/
def RelocationResidual : Prop :=
  ∀ (u v : State) (ρ pre γ tail s1 s2 : List Move) (c d : Card) (b : Base),
    u.WF → SSaturated v → ShufflePlayW u ρ v →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
    ρ = pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))) →
    Canon.FreeOnly γ → c.suit ≠ d.suit →
    tail = s1 ++ Move.tabToFound d :: s2 → s1 ≠ [] → False

/-- `RelocationResidual` implies the twin/pull-free residual of `Sat`. -/
theorem twinRelocationResidual_of_relocation (h : RelocationResidual) :
    Sat.TwinRelocationResidual := by
  intro u v ρ pre γ tail s1 s2 c d b huwf hv hplay hmin heq hfree hsu hd hpf heqtail hs1
  have heq' : ρ = pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))) := by
    rw [heq]
    simp only [List.append_assoc, List.cons_append]
  exact h u v ρ pre γ tail s1 s2 c d b huwf hv hplay hmin heq' hfree hsu heqtail hs1

/-- **THE REDUCTION.**  `SChainMateResidual` (the S-chain lands on `d`) plus
`RelocationResidual` (the same-card lane) give `Blocks.NoSeatMateCrossSuit`.
This replaces the two open gaps — the king branch and the pull tails — by one
card statement at the corridor. -/
theorem noSeatMate_of_residuals (h1 : SChainMateResidual) (h2 : RelocationResidual) :
    Blocks.NoSeatMateCrossSuit := by
  intro u v ρ pre γ tail c d b A B huwf hu hv hplay hminlen hmininv heq hfree hsu
    hpre hstepR hpullB hread hseat hsm
  -- the play in the corridor's parenthesization
  have hplay'' : ShufflePlayW u
      (pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail)))) v := by
    rw [← heq]; exact hplay
  have hlist : pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail)))
      = (pre ++ Move.tabToFound c :: γ) ++ Move.foundToTab d b :: tail := by
    simp only [List.append_assoc, List.cons_append]
  have hplay' : ShufflePlayW u
      ((pre ++ Move.tabToFound c :: γ) ++ Move.foundToTab d b :: tail) v :=
    hlist ▸ hplay''
  have heq' : ρ = (pre ++ Move.tabToFound c :: γ) ++ Move.foundToTab d b :: tail := by
    rw [heq]; exact hlist
  -- split at the corridor's pull
  obtain ⟨P₀, hpreP, hrestP⟩ :=
    ValleyElim.ShufflePlayW_split hplay' (pre ++ Move.tabToFound c :: γ)
      (Move.foundToTab d b :: tail) rfl
  obtain ⟨L, hrevP, hstepP, htail⟩ := Bubble.walk_cons_inv hrestP
  have hPwf : P₀.WF := SatDifferCensus.ShufflePlayW.wf_end hpreP huwf
  have hLwf : L.WF := step_wf hPwf hstepP
  have hliveL : CanRaiseS L d :=
    CanRaiseS.now d (ValleyStep.pull_card_canRaise hPwf hstepP)
  -- the free interior's play from the raise's image
  have hrevR : reversibleAtW A (Move.tabToFound c) :=
    Blocks.rev_raise_of_corridor hplay'' hpre
  have hpreB : ShufflePlayW u (pre ++ [Move.tabToFound c]) B :=
    ShufflePlayW_append hpre (Walk.cons hrevR hstepR (Walk.nil B))
  have hpreP' : ShufflePlayW u ((pre ++ [Move.tabToFound c]) ++ γ) P₀ := by
    have hlist2 : (pre ++ [Move.tabToFound c]) ++ γ
        = pre ++ Move.tabToFound c :: γ := by
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [hlist2]
    exact hpreP
  obtain ⟨B₂, hpreB₂, hγB₂⟩ :=
    ValleyElim.ShufflePlayW_split hpreP' (pre ++ [Move.tabToFound c]) γ rfl
  have hB₂ : B₂ = B := by
    have h1 := Walk_run (fun st m => reversibleAtW st m) hpreB₂
    have h2 := Walk_run (fun st m => reversibleAtW st m) hpreB
    exact Option.some.inj (h1.symm.trans h2)
  rw [hB₂] at hγB₂
  -- the S-chain from the pull's landing
  obtain ⟨z, s1, s2, A', Z, hrest⟩ := skill_chain hLwf hv hliveL htail
  obtain ⟨hle, heqtail, hp', hlive', hstep', htail'⟩ := hrest
  have hz : z = d :=
    h1 u v ρ pre γ tail c d b A B P₀ L huwf hv hplay hminlen heq hfree hsu hpre
      hstepR hγB₂ hstepP z s1 s2 A' Z hle heqtail hp' hlive' hstep'
  rw [hz] at heqtail
  by_cases hs1 : s1 = []
  · subst hs1
    exact Sat.corridor_tail_head_ne_raise huwf hplay hminlen heq' s2 (by simpa using heqtail)
  · exact h2 u v ρ pre γ tail s1 s2 c d b huwf hv hplay hminlen heq hfree hsu
      heqtail hs1

/-! ## §8. Axiom battery

Expected: every row `[]`, `[propext]` or `[propext, Quot.sound]`; no `sorryAx`,
no `Classical.choice`, no `Lean.ofReduceBool`. -/

#print axioms Gap.card_twin_ne
#print axioms Gap.pull_kill_shape
#print axioms Gap.pull_kill_descends
#print axioms Gap.lastOf_split_eq
#print axioms Gap.mate_raise_kill_buried
#print axioms Gap.first_Skill
#print axioms Gap.skill_chain_aux
#print axioms Gap.skill_chain
#print axioms Gap.king_pullFree
#print axioms Gap.king_mate_first_kill_buried
#print axioms Gap.twinRelocationResidual_of_relocation
#print axioms Gap.noSeatMate_of_residuals

#check @Gap.SChainMateResidual
#check @Gap.RelocationResidual
#check @Gap.pull_kill_shape
#check @Gap.pull_kill_descends
#check @Gap.skill_chain
#check @Gap.king_pullFree
#check @Gap.king_mate_first_kill_buried
#check @Gap.noSeatMate_of_residuals

end Gap

