import Orig2.Fork.Local.ForkCommuteSlide
import Orig2.Fork.Local.ForkCommute

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# MtnPr_Net — the raise/pull relocation core

READ-ONLY scratch card.  No `sorry`, no `Classical.choice`, no `native_decide`.

`raise c` lifts the top card `c` of pile `a` to the foundation; a later
`pull c b` takes it back down onto base `b`.  When the two are ADJACENT the
composite is a single `slide c b` — except in the two seats where the slide
is not a legal replacement (the raise's own emptied seat, and the seat of
the card the raise exposes); those two are identity pairs and delete.

* §1  `putRun [c] = putCard c`
* §2  undoing the raise's foundation snoc
* §3  **the net-one core** `raise_pull_eq_slide`
* §4  the pull's landing formula
* §5  **the two exceptional seats are identity pairs**
* §6  **`adjacent_raise_pull_shortens`** — the adjacent case of the residual,
      fully discharged
-/

namespace MtnPr

open MountainKit

/-! ## §1. `putRun [c]` is `putCard c` -/

theorem putRun_singleton_eq_putCard (st : State) (c : Card) (b : Base) :
    st.putRun [c] b = st.putCard c b := by
  cases b with
  | inl a => rfl
  | inr z =>
      show (match st.pileOfTop z with
        | some k => st.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }
        | none => st) = _
      rfl

/-- A card cannot be placed onto itself. -/
theorem canSitOn_self_false (c : Card) : canSitOn c c = false := by
  show (decide (c.rank.toIdx + 1 = c.rank.toIdx) && decide (c.suit.color ≠ c.suit.color)) = false
  rw [decide_false_of_not (Nat.succ_ne_self c.rank.toIdx), Bool.false_and]

/-- `canPlace c (inr c)` is false. -/
theorem canPlace_inr_self_false (st : State) (c : Card) :
    st.canPlace c (Sum.inr c) = false := by
  change (match st.pileOfTop c with
    | some _ => canSitOn c c
    | none => false) = false
  cases h : st.pileOfTop c with
  | none => rfl
  | some _ => exact canSitOn_self_false c

/-! ## §2. The raise's foundation write, undone -/

/-- Undoing the raise's foundation snoc leaves the pile-only update. -/
theorem raiseSt_setFound_self (st : State) (c : Card) (a : Anchor) :
    (raiseSt st c a).setFound c.suit (st.found c.suit) =
      st.setPile a (Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)) := by
  apply State.ext
  · funext s
    show (if s = c.suit then st.found c.suit else (raiseSt st c a).found s) =
      (st.setPile a (Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp))).found s
    rw [setPile_found]
    by_cases hs : s = c.suit
    · rw [ite_eq_left hs, hs]
    · rw [ite_eq_right hs, raiseSt_found_apply, ite_eq_right hs]
  · funext a'
    rw [setFound_piles]
    by_cases ha : a' = a
    · rw [ha, setPile_piles_self, raiseSt_piles_apply, ite_eq_left rfl]
    · rw [setPile_piles_ne ha, raiseSt_piles_apply, ite_eq_right ha]
  · rfl
  · rfl
  · rfl

/-! ## §3. The net-one core -/

/-- **THE NET-ONE CORE.**  At a `WF` state where `c` is a pile top and the
slide onto `b` is legal, a raise of `c` followed by the pull of `c` onto `b`
lands exactly where the single slide `slide c b` lands. -/
theorem raise_pull_eq_slide {st : State} {c : Card} {b : Base} {a : Anchor}
    (hwf : st.WF) (hnext : st.nextUp c = true) (hpo : st.pileOfTop c = some a)
    (hcp : st.canPlace c b = true) :
    State.step (raiseSt st c a) (Move.foundToTab c b) =
      State.step st (Move.tabToTab c b) := by
  have hraise : State.step st (Move.tabToFound c) = some (raiseSt st c a) := by
    rw [step_tabToFound_splice hnext hpo]
    rfl
  have hwfR : (raiseSt st c a).WF := step_wf hwf hraise
  have hbz : b ≠ Sum.inr c := by
    intro hb
    rw [hb, canPlace_inr_self_false] at hcp
    exact absurd hcp (by simp)
  have htopR : (raiseSt st c a).foundTop c.suit = some c := by
    unfold State.foundTop
    rw [raiseSt_found_apply, ite_eq_left rfl, lastOf_snoc]
  have hcpR : (raiseSt st c a).canPlace c b = true := by
    rw [R12.canPlace_raiseSt hwf hpo hbz hcp]
    exact hcp
  have hpull : State.step (raiseSt st c a) (Move.foundToTab c b) = some
      (((raiseSt st c a).setFound c.suit (chop (st.found c.suit ++ [c]))).putCard c b) := by
    rw [step_foundToTab_splice htopR hcpR, raiseSt_found_apply, ite_eq_left rfl]
  have hndR : (st.piles a).faceUp.Nodup := runOK_nodup (hwf.runOK_of a)
  have hlast : lastOf (st.piles a).faceUp = some c := (pileOfTop_top hpo).2
  have hfrom : fromCard c (st.piles a).faceUp = [c] :=
    NoSelfKit.fromCard_singleton_of_last hndR hlast
  have hbelow : below c (st.piles a).faceUp = chop (st.piles a).faceUp :=
    NoSelfKit.below_eq_chop_of_last hndR hlast
  have hhold : st.pileHolding c = some a := Drain.pileHolding_of_pileOfTop hwf hpo
  have hslide : State.step st (Move.tabToTab c b) = some
      ((st.setPile a (Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp))).putCard c b) := by
    rw [step_tabToTab_eq, hhold]
    simp only [hcp, hfrom, ite_true]
    rw [hbelow, putRun_singleton_eq_putCard]
  rw [hpull, hslide, chop_snoc, raiseSt_setFound_self]

/-! ## §4. The pull landing, read off the raise state -/

/-- Whatever the pull does after the raise, it does it as
`putCard c b` on the raise's pile-only update.  (Shared body of the net-one
core and of the two exceptional seats.) -/
theorem raise_pull_landing {st X : State} {c : Card} {b : Base} {a : Anchor}
    (hwf : st.WF) (hnext : st.nextUp c = true) (hpo : st.pileOfTop c = some a)
    (hpull : State.step (raiseSt st c a) (Move.foundToTab c b) = some X) :
    X = (st.setPile a (Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp))).putCard c b := by
  obtain ⟨c', htop', hc', hcpR, hs⟩ := step_foundToTab_inv hpull
  have htopR : (raiseSt st c a).foundTop c.suit = some c := by
    unfold State.foundTop
    rw [raiseSt_found_apply, ite_eq_left rfl, lastOf_snoc]
  have hcc : c' = c := Option.some.inj (htop'.symm.trans htopR)
  subst hcc
  rw [hs, raiseSt_found_apply, ite_eq_left rfl, chop_snoc, raiseSt_setFound_self]

/-- `setPile` with the pile already in place changes nothing. -/
theorem setPile_piles_self_state (st : State) (a : Anchor) :
    st.setPile a (st.piles a) = st := by
  apply State.ext
  · exact setPile_found st a (st.piles a)
  · funext a'
    show (if a' = a then st.piles a else st.piles a') = st.piles a'
    by_cases h : a' = a
    · rw [ite_eq_left h, h]
    · rw [ite_eq_right h]
  · rfl
  · rfl
  · rfl

/-- Two pile writes at the same seat: the last one wins. -/
theorem setPile_setPile_same (st : State) (a : Anchor) (p q : Pile) :
    (st.setPile a p).setPile a q = st.setPile a q := by
  apply State.ext
  · rw [setPile_found, setPile_found, setPile_found]
  · funext a'
    by_cases h : a' = a
    · rw [h, setPile_piles_self, setPile_piles_self]
    · simp only [setPile_piles_ne h]
  · rfl
  · rfl
  · rfl

/-- A pile whose run removal leaves the face-up run empty was the bare
`[c]`-seat, with nothing hidden: `chop` was already empty. -/
theorem afterRunRemoved_faceUp_nil {p : Pile} {pre : List Card}
    (h : (Pile.afterRunRemoved p pre).faceUp = []) : pre = [] ∧ p.hidden = [] := by
  rcases p with ⟨hd, fu⟩
  cases pre with
  | nil =>
      cases hd with
      | nil => exact ⟨rfl, rfl⟩
      | cons x xs =>
          exact absurd h (by simp [Pile.afterRunRemoved, Pile.revealTop])
  | cons y ys => exact absurd h (by simp [Pile.afterRunRemoved])

/-! ## §5. The two exceptional seats are identity pairs

When `slide c b` is NOT a legal replacement, the pull's base must be one of
two seats, and in both the raise/pull pair returns to the state it started
from.  Reversibility of the raise (the cell clause) is what removes the
third, genuinely non-identity seat: the seat of the card the raise would
flip. -/

/-- **THE EXCEPTIONAL SEATS ARE IDENTITY SEATS.**  If the slide onto `b` is
illegal at the raise's origin, then a legal pull of the raised card onto `b`
returns the whole state to where the raise started. -/
theorem raise_pull_return_of_not_canPlace {st X : State} {c : Card} {b : Base} {a : Anchor}
    (hwf : st.WF) (hnext : st.nextUp c = true) (hpo : st.pileOfTop c = some a)
    (hcell : chop (st.piles a).faceUp ≠ [] ∨
      ((st.piles a).hidden = [] ∧ c.rank = Rank.king))
    (hpull : State.step (raiseSt st c a) (Move.foundToTab c b) = some X)
    (hno : st.canPlace c b = false) : X = st := by
  have hland := raise_pull_landing hwf hnext hpo hpull
  obtain ⟨c', htop', hc', hcpR, hs⟩ := step_foundToTab_inv hpull
  have hlast : lastOf (st.piles a).faceUp = some c := (pileOfTop_top hpo).2
  have hface : (st.piles a).faceUp = chop (st.piles a).faceUp ++ [c] :=
    lastOf_chop hlast
  rw [hland]
  cases b with
  | inl j =>
      have hemp : ((raiseSt st c a).piles j).isEmpty = true := (canPlace_inl hcpR).1
      have hking : c.rank = Rank.king := (canPlace_inl hcpR).2
      have hja : j = a := by
        by_cases h : j = a
        · exact h
        · exfalso
          have hsame : (raiseSt st c a).piles j = st.piles j := by
            rw [raiseSt_piles_apply, ite_eq_right h]
          have htrue : st.canPlace c (Sum.inl j) = true := by
            rw [canPlace_inl_unfold, ← hsame, hemp, decide_eq_true hking]
            rfl
          rw [hno] at htrue
          exact absurd htrue (by simp)
      rw [hja]
      rw [hja] at hemp
      have hAeq : (raiseSt st c a).piles a =
          Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp) := by
        rw [raiseSt_piles_apply, ite_eq_left rfl]
      rw [hAeq] at hemp
      obtain ⟨hA1, hA2⟩ := (Pile.isEmpty_eq _).mp hemp
      obtain ⟨hchop, hhid⟩ := afterRunRemoved_faceUp_nil hA2
      have hfill : (st.piles a).faceUp = [c] := by
        cases hf : (st.piles a).faceUp with
        | nil => rw [hf] at hlast; exact absurd hlast (by simp [lastOf])
        | cons x xs =>
            cases xs with
            | nil =>
                rw [hf] at hlast
                exact congrArg (fun z => [z]) (Option.some.inj hlast)
            | cons y ys =>
                rw [hf] at hchop
                exact absurd hchop (by simp [chop])
      have hpile : st.piles a = ⟨[], [c]⟩ := by
        apply Pile.ext
        · exact hhid
        · exact hfill
      rw [putCard_eq_inl, setPile_setPile_same, ← hpile, setPile_piles_self_state]
  | inr z =>
      obtain ⟨k, hkz, hfit⟩ := canPlace_inr hcpR
      have hnone : st.pileOfTop z = none := by
        cases h : st.pileOfTop z with
        | none => rfl
        | some k' =>
            have hfalse : canSitOn c z = false := by
              simpa [canPlace_inr_eq, h] using hno
            rw [hfalse] at hfit
            exact absurd hfit (by simp)
      have hnone_all : ∀ j : Anchor, (st.piles j).top ≠ some z := by
        intro j hj
        have hsome : st.pileOfTop z = some j := (pileOfTop_eq_some_iff hwf).mpr hj
        rw [hnone] at hsome
        exact absurd hsome (by simp)
      have hka : k = a := by
        by_cases h : k = a
        · exact h
        · exfalso
          have htop : lastOf ((raiseSt st c a).piles k).faceUp = some z := (pileOfTop_top hkz).2
          rw [raiseSt_piles_apply, ite_eq_right h] at htop
          exact hnone_all k htop
      rw [hka] at hkz
      have hchop : chop (st.piles a).faceUp ≠ [] := by
        intro hc
        rcases hcell with h | ⟨hh, -⟩
        · exact h hc
        · have hA : (raiseSt st c a).piles a =
              Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp) := by
            rw [raiseSt_piles_apply, ite_eq_left rfl]
          have htop : ((raiseSt st c a).piles a).top = some z := (pileOfTop_top hkz).2
          rw [hA, hc, Pile.afterRunRemoved_bare hh] at htop
          exact absurd htop (by simp [Pile.top, lastOf])
      have hA : (raiseSt st c a).piles a =
          { st.piles a with faceUp := chop (st.piles a).faceUp } := by
        rw [raiseSt_piles_apply, ite_eq_left rfl, afterRunRemoved_ne hchop]
      have hzlast : lastOf (chop (st.piles a).faceUp) = some z := by
        have htop : ((raiseSt st c a).piles a).top = some z := (pileOfTop_top hkz).2
        rw [hA] at htop
        exact htop
      have hpiles : (st.setPile a
          (Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp))).piles
          = (raiseSt st c a).piles := by
        funext a'
        rw [raiseSt_piles_apply]
        by_cases h : a' = a
        · rw [h, setPile_piles_self, ite_eq_left rfl]
        · rw [setPile_piles_ne h, ite_eq_right h]
      have hY : (st.setPile a
          (Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp))).pileOfTop z = some a := by
        rw [CommuteStep.pileOfTop_congr_piles hpiles z]
        exact hkz
      have hQ : ({ Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp) with
            faceUp := (Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)).faceUp
              ++ [c] } : Pile) = st.piles a := by
        rw [afterRunRemoved_ne hchop]
        apply Pile.ext
        · rfl
        · change chop (st.piles a).faceUp ++ [c] = (st.piles a).faceUp
          exact hface.symm
      rw [putCard_inr_eq hY, setPile_piles_self, setPile_setPile_same, hQ,
        setPile_piles_self_state]

/-! ## §6. The adjacent residual, fully discharged -/

/-- **ADJACENT `raise c ; pull c b` SHORTENS.**  In any witness play, an
adjacent raise of `c` followed by a pull of `c` onto any base `b` deletes to a
strictly shorter witness play with the same endpoints:

* if `slide c b` is legal at the raise's origin, the pair is the single slide
  (`raise_pull_eq_slide`), and the slide is reversible because the raise was;
* otherwise the pair is an identity pair (`raise_pull_return_of_not_canPlace`)
  and deletes.

This is the `γ = []` instance of the long-distance relocation residual, and
it is *unconditional in `b`*: no "same seat" hypothesis. -/
theorem adjacent_raise_pull_shortens {u v : State} {ρ pre post : List Move}
    {c : Card} {b : Base}
    (huwf : u.WF) (hplay : ShufflePlayW u ρ v)
    (hρ : ρ = pre ++ Move.tabToFound c :: Move.foundToTab c b :: post) :
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length := by
  obtain ⟨A, hpre, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hplay pre
      (Move.tabToFound c :: Move.foundToTab c b :: post) hρ
  obtain ⟨T, hrev1, hstep1, hrest2⟩ := Bubble.walk_cons_inv hrest
  obtain ⟨B, hrev2, hstep2, hpost⟩ := Bubble.walk_cons_inv hrest2
  have hAwf : A.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  have hnext : A.nextUp c = true := (step_tabToFound_inv hstep1).1
  obtain ⟨-, a, hpo, hs1⟩ := step_tabToFound_inv hstep1
  have hT : T = raiseSt A c a := by rw [hs1]; rfl
  have hR : tabToFoundR A c = true := (tabToFoundR_iff_reversibleAtW hAwf c).mpr hrev1
  obtain ⟨a', hpo', hcell'⟩ := seat_of_tabToFoundR hR
  have haa : a' = a := Option.some.inj (hpo'.symm.trans hpo)
  rw [haa] at hcell'
  by_cases hcp : A.canPlace c b = true
  · -- the pair is one slide
    have hslideeq : State.step (raiseSt A c a) (Move.foundToTab c b) =
        State.step A (Move.tabToTab c b) :=
      raise_pull_eq_slide hAwf hnext hpo hcp
    have hstepS : State.step A (Move.tabToTab c b) = some B := by
      rw [← hslideeq, ← hT]
      exact hstep2
    have hhold : A.pileHolding c = some a := Drain.pileHolding_of_pileOfTop hAwf hpo
    have hndA : (A.piles a).faceUp.Nodup := runOK_nodup (hAwf.runOK_of a)
    have hlastA : lastOf (A.piles a).faceUp = some c := (pileOfTop_top hpo).2
    have hbelowA : below c (A.piles a).faceUp = chop (A.piles a).faceUp :=
      NoSelfKit.below_eq_chop_of_last hndA hlastA
    have hcellB : below c (A.piles a).faceUp ≠ [] ∨
        (below c (A.piles a).faceUp = [] ∧ (A.piles a).hidden = [] ∧ c.rank = Rank.king) := by
      rw [hbelowA]
      by_cases hc : chop (A.piles a).faceUp = []
      · refine Or.inr ⟨hc, ?_, ?_⟩
        · rcases hcell' with h | ⟨hh, -⟩
          · exact absurd hc h
          · exact hh
        · rcases hcell' with h | ⟨-, hk⟩
          · exact absurd hc h
          · exact hk
      · exact Or.inl hc
    have hrevS : reversibleAtW A (Move.tabToTab c b) :=
      (tabToTabR_iff_reversibleAtW hAwf c b).mp (R12.tabToTabR_true_of hhold hcp hcellB)
    refine ⟨pre ++ Move.tabToTab c b :: post, ?_, ?_⟩
    · exact ShufflePlayW_append hpre (Walk.cons hrevS hstepS hpost)
    · rw [hρ]
      simp only [List.length_append, List.length_cons]
      omega
  · -- the pair is the identity
    have hno : A.canPlace c b = false := by
      cases h : A.canPlace c b
      · rfl
      · exact absurd h hcp
    have hpullT : State.step (raiseSt A c a) (Move.foundToTab c b) = some B := by
      simpa [hT] using hstep2
    have hBA : B = A :=
      raise_pull_return_of_not_canPlace hAwf hnext hpo hcell' hpullT hno
    have hid : State.step T (Move.foundToTab c b) = some A := by
      simpa [hT, hBA] using hstep2
    exact LiveKit.identity_pair_delete hplay hρ hpre ⟨hstep1, hid⟩

/-! ## §7. The cross-suit counterpart cannot shorten locally

`raise c` and `pull d b` with `c.suit ≠ d.suit` move *different* foundations.
Their adjacent composite has a rung delta with TWO nonzero coordinates
(`+1` on `c.suit`, `-1` on `d.suit`), which no single letter can produce.
Hence the `raise c ; pull d b` play is length-minimal, and the residual as
written in `Orig2/Fork/Split/ForkMountainShape.lean:503` — which asks only `u.WF` — is
FALSE at such a state.  (The campaign's *use* gates it on `SSaturated u`, which
excludes the initial-raise instance, but the residual itself must be gated.) -/

/-- The rung gap of the pair: `+1` on the raise's suit, `-1` on the pull's. -/
theorem twoSuit_gap_rungs {S T B : State} {c d : Card} {b : Base}
    (h1 : State.step S (Move.tabToFound c) = some T)
    (h2 : State.step T (Move.foundToTab d b) = some B)
    (hsu : c.suit ≠ d.suit) :
    rungAt B c.suit = rungAt S c.suit + 1 ∧
      rungAt B d.suit = rungAt S d.suit - 1 := by
  have hdc : d.suit ≠ c.suit := fun h => hsu h.symm
  refine ⟨?_, ?_⟩
  · rw [rungAt_foundToTab h2 c.suit, ite_eq_right hsu,
      rungAt_tabToFound h1 c.suit, ite_eq_left rfl]
  · rw [rungAt_foundToTab h2 d.suit, ite_eq_left rfl,
      rungAt_tabToFound h1 d.suit, ite_eq_right hdc]

/-- **NO SINGLE LETTER.**  No one-letter move takes `S` to the endpoint of
`raise c ; pull d b` when the two suits differ. -/
theorem no_single_step_of_twoSuit_gap {S T B : State} {c d : Card} {b : Base}
    (h1 : State.step S (Move.tabToFound c) = some T)
    (h2 : State.step T (Move.foundToTab d b) = some B)
    (hsu : c.suit ≠ d.suit) :
    ∀ m : Move, State.step S m ≠ some B := by
  obtain ⟨hcB, hdB⟩ := twoSuit_gap_rungs h1 h2 hsu
  have hdc : d.suit ≠ c.suit := fun h => hsu h.symm
  -- the pulled card is on its foundation, so the pull's suit has rung at least one
  have hdpos : 1 ≤ rungAt S d.suit := by
    obtain ⟨d', htop', hd'eq, -, -⟩ := step_foundToTab_inv h2
    have hmem : d ∈ T.found d.suit := by
      have h := htop'
      unfold State.foundTop at h
      have h' : lastOf (T.found d.suit) = some d := by rw [h, ← hd'eq]
      exact lastOf_mem h'
    have hlenT : 1 ≤ rungAt T d.suit := List.length_pos_of_mem hmem
    have hlen : rungAt T d.suit = rungAt S d.suit := by
      have h := rungAt_tabToFound h1 d.suit
      rw [ite_eq_right hdc] at h
      exact h
    omega
  intro m hm
  cases m with
  | draw =>
      have h := rungAt_draw hm c.suit
      omega
  | tabToFound x =>
      have hx := rungAt_tabToFound hm c.suit
      have hx' := rungAt_tabToFound hm d.suit
      by_cases hxs : x.suit = c.suit
      · rw [ite_eq_left hxs.symm] at hx
        rw [ite_eq_right (by intro h; exact hdc (h.trans hxs))] at hx'
        omega
      · rw [ite_eq_right (by intro h; exact hxs h.symm)] at hx
        omega
  | foundToTab x b' =>
      have hx := rungAt_foundToTab hm c.suit
      have hx' := rungAt_foundToTab hm d.suit
      by_cases hxs : x.suit = d.suit
      · rw [ite_eq_left hxs.symm] at hx'
        rw [ite_eq_right (by intro h; exact hsu (h.trans hxs))] at hx
        omega
      · rw [ite_eq_right (by intro h; exact hxs h.symm)] at hx'
        by_cases hxc : c.suit = x.suit
        · rw [ite_eq_left hxc] at hx
          omega
        · rw [ite_eq_right hxc] at hx
          omega
  | tabToTab x b' =>
      have h := rungAt_tabToTab hm c.suit
      omega
  | wasteToFound x =>
      have hx := rungAt_wasteToFound hm c.suit
      have hx' := rungAt_wasteToFound hm d.suit
      by_cases hxs : x.suit = c.suit
      · rw [ite_eq_left hxs.symm] at hx
        rw [ite_eq_right (by intro h; exact hdc (h.trans hxs))] at hx'
        omega
      · rw [ite_eq_right (by intro h; exact hxs h.symm)] at hx
        omega
  | wasteToTab x b' =>
      have h := rungAt_wasteToTab hm c.suit
      omega

/-- **THE TWO-LETTER PLAY IS SHORTEST.** -/
theorem twoSuit_gap_is_shortest {S T B : State} {c d : Card} {b : Base}
    (h1 : State.step S (Move.tabToFound c) = some T)
    (h2 : State.step T (Move.foundToTab d b) = some B)
    (hsu : c.suit ≠ d.suit) :
    ∀ ρ' : List Move, ShufflePlayW S ρ' B → 2 ≤ ρ'.length := by
  obtain ⟨hcB, -⟩ := twoSuit_gap_rungs h1 h2 hsu
  have hne : B ≠ S := by
    intro hBS
    rw [hBS] at hcB
    omega
  have hno1 := no_single_step_of_twoSuit_gap h1 h2 hsu
  intro ρ' hplay
  cases ρ' with
  | nil =>
      have hr := Walk_run (fun st m => reversibleAtW st m) hplay
      exact absurd (Option.some.inj hr).symm hne
  | cons m rest =>
      cases rest with
      | nil => exact absurd (Elim.step_of_singleton hplay) (hno1 m)
      | cons m2 rest2 => simp

/-- **THE UNGATED RESIDUAL IS FALSE.**  If there is a `WF` state at which a
raise of `c` is legal and a later-founded `d` (different suit) is pullable,
then `RaiseBeforePullShortens` (as stated, `u.WF` only) is refuted by the
two-letter play `raise c ; pull d b`: it is a shortest play, yet carries a
raise before a pull. -/
theorem not_raiseBeforePullShortens_of_twoSuit_gap
    (h : MountainKit.RaiseBeforePullShortens)
    {S T B : State} {c d : Card} {b : Base}
    (hS : S.WF)
    (h1 : State.step S (Move.tabToFound c) = some T)
    (h2 : State.step T (Move.foundToTab d b) = some B)
    (hc : reversibleAtW S (Move.tabToFound c))
    (hd : reversibleAtW T (Move.foundToTab d b))
    (hsu : c.suit ≠ d.suit) : False := by
  have hplay : ShufflePlayW S [Move.tabToFound c, Move.foundToTab d b] B :=
    Walk.cons hc h1 (Walk.cons hd h2 (Walk.nil B))
  obtain ⟨ρ', hρ'play, hρ'len⟩ :=
    h S B [Move.tabToFound c, Move.foundToTab d b] [] [Move.foundToTab d b]
      c d b hS hplay rfl (by simp)
  have hshort := twoSuit_gap_is_shortest h1 h2 hsu ρ' hρ'play
  have hlt : ρ'.length < 2 := by
    simpa using hρ'len
  omega

/-! ## §8. The named residual: same-card, populated interior

The adjacent same-card case is §6.  What §6 does NOT cover is a nonzero
interior `γ` between the raise and the pull of the same card; the net-zero
technique then needs `γ` to be transparent to the pull's *seat*.  Read-safety
for `c` alone is insufficient (an interior letter landing on the pull's base
dirties the seat), so the residual carries a seat-inertness clause. -/

/-- `SeatInert b q` — the letter `q` does not write to the base `b`, and it
does not move the card that `b` addresses (writing on `b`'s pile or lifting
the top card of `b`'s pile changes the seat's read). -/
def SeatInert (b : Base) (q : Move) : Prop :=
  match q, b with
  | Move.foundToTab _ b', _ => b' ≠ b
  | Move.wasteToTab _ b', _ => b' ≠ b
  | Move.tabToTab w b', Sum.inr z => b' ≠ b ∧ w ≠ z
  | Move.tabToTab _ b', Sum.inl _ => b' ≠ b
  | Move.tabToFound w, Sum.inr z => w ≠ z
  | _, _ => True

/-- **THE NAMED RESIDUAL — WITHDRAWN, FALSE AS STATED.**

Kernel counterexample (`Orig2/ForkPermRefute.lean`, `Perm.sameCardRelocation_false`):
a **17-card** board and the **3-letter shortest** play

```text
raise 4♠ ; slide 4♣ onto 5♦ ; pull 4♠ onto 5♥
```

The interior letter is *both* `SlideFwd.ReadSafe 4♠` and `SeatInert (inr 5♥)`, the
play is shortest (`Perm.no_short : 3 ≤ ρ.length`, from the rung ledger — no
search), and no shorter play exists.  So the two hypotheses here are satisfiable
in a shortest play that does **not** shorten.

The only failing hypothesis is **`Pullable` at the raise's image** — exactly the
readiness clause that `PullKit.SameCardRelocationReady`
(`Orig2/Fork/Local/ForkPullSwaps.lean`) adds, and `PullKit.PullReadyAtImage` shows it is not
implied by the other two.  So the correct residual is the `Ready`-gated form; this
un-gated version is kept only so the refutation can name it.

NOTE the campaign's own use is at a `SplitHyp` bottom (saturated endpoints), which
the witness is not — but do not cite this definition as a dischargeable hypothesis
without the readiness clause. -/
def SameCardRelocation : Prop :=
  ∀ (u v : State) (ρ pre γ post : List Move) (c : Card) (b : Base),
    u.WF →
    ShufflePlayW u ρ v →
    ρ = pre ++ Move.tabToFound c :: γ ++ Move.foundToTab c b :: post →
    (∀ q ∈ γ, SlideFwd.ReadSafe c q) →
    (∀ q ∈ γ, SeatInert b q) →
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length

/-- **THE EMPTY-INTERIOR INSTANCE IS A THEOREM** — §6 is exactly the residual
with `γ = []` (and no read-safety needed there). -/
theorem sameCardRelocation_nil {u v : State} {ρ pre post : List Move}
    {c : Card} {b : Base}
    (huwf : u.WF) (hplay : ShufflePlayW u ρ v)
    (hρ : ρ = pre ++ Move.tabToFound c :: Move.foundToTab c b :: post) :
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length :=
  adjacent_raise_pull_shortens huwf hplay hρ

/-- **NO ADJACENT `raise ; pull` OF THE SAME CARD IN A SHORTEST PLAY.**  The
direct minimality corollary of §6. -/
theorem noAdjacentRaisePull_of_minimal {u v : State} {ρ : List Move}
    {c : Card} {b : Base}
    (huwf : u.WF) (hplay : ShufflePlayW u ρ v)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) :
    ¬ ∃ (pre tail : List Move),
      ρ = pre ++ Move.tabToFound c :: Move.foundToTab c b :: tail := by
  rintro ⟨pre, tail, heq⟩
  obtain ⟨ρ', hρ', hlen⟩ := adjacent_raise_pull_shortens huwf hplay heq
  have hle := hmin ρ' hρ'
  omega

end MtnPr

#print axioms MtnPr.raiseSt_setFound_self
#print axioms MtnPr.raise_pull_eq_slide
#print axioms MtnPr.raise_pull_landing
#print axioms MtnPr.raise_pull_return_of_not_canPlace
#print axioms MtnPr.adjacent_raise_pull_shortens
#print axioms MtnPr.twoSuit_gap_rungs
#print axioms MtnPr.no_single_step_of_twoSuit_gap
#print axioms MtnPr.twoSuit_gap_is_shortest
#print axioms MtnPr.not_raiseBeforePullShortens_of_twoSuit_gap
#print axioms MtnPr.sameCardRelocation_nil

#print axioms MtnPr.putRun_singleton_eq_putCard
#print axioms MtnPr.canSitOn_self_false
#print axioms MtnPr.canPlace_inr_self_false
#print axioms MtnPr.setPile_piles_self_state
#print axioms MtnPr.setPile_setPile_same
#print axioms MtnPr.afterRunRemoved_faceUp_nil
#print axioms MtnPr.noAdjacentRaisePull_of_minimal
