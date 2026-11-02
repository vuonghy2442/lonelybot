import Orig2.Fork.Local.ForkRelocate
import Orig2.Fork.Local.ForkSlideFwd

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# PullSw — the PULL-SIDE mirror of the raise-bubble machine

READ-ONLY scratch card (`Temp/`).  No source edits, no commit.  No `sorry`,
no `Classical.choice`, no `native_decide`.

`NonforkKit.raise_bubble` (`Orig2/Fork/Third/ForkNonfork.lean:101`) moves a pending
**raise** to the front of an arbitrary window, given the per-position
two-order certificate `RaiseSwaps`.  This card builds the mirror for a
pending **pull**: `PullSwaps` + `pull_bubble`, the per-letter certificate
`pullSwaps_of_read`, and the play-level relocation reduction on
`MtnPr.SameCardRelocation` (`Orig2/Fork/Local/ForkRelocate.lean:545`).

§1  the certificate and the bubble (letter-generic)
§2  pull frames (the pull's effect on the search / placement readers)
§3  the per-letter diamond (pull swaps with every safe letter)
§4  the certificate from `ReadSafe` + `SeatInert`
§5  the play-level reduction (`SameCardRelocation` under pull readiness)
§6  the readiness gap, named
-/

namespace PullKit

open MountainKit
open CommuteStep

/-! ## §1. The certificate and the bubble -/

/-- **`PullSwaps Q z bz γ`** — the pull `pull z bz` swaps left across EVERY
position of the window `γ` starting from `Q`.  At each decomposition
`γ = pre ++ q :: rest` and each state `mid` reached by `pre`, the two-letter
word `[pull z bz, q]` is a witness play, and it lands where the ORIGINAL order
`[q, pull z bz]` lands.  The base `bz` is part of the letter and therefore
part of the certificate. -/
def PullSwaps (Q : State) (z : Card) (bz : Base) (γ : List Move) : Prop :=
  ∀ (pre : List Move) (mid : State) (q : Move) (rest : List Move),
    pre ++ q :: rest = γ → ShufflePlayW Q pre mid →
    ∃ e, ShufflePlayW mid [Move.foundToTab z bz, q] e ∧
         mid.run [q, Move.foundToTab z bz] = some e

/-- `Pullable st z bz` — the pull's own guard: `z` is the top of its
foundation and the base accepts it.  This is exactly `foundToTabR`. -/
def Pullable (st : State) (z : Card) (bz : Base) : Prop :=
  st.foundTop z.suit = some z ∧ st.canPlace z bz = true

/-- The empty window needs no certificate. -/
theorem pullSwaps_nil (Q : State) (z : Card) (bz : Base) : PullSwaps Q z bz [] := by
  intro pre mid q rest hsplit _
  cases pre with
  | nil => exact absurd hsplit (by simp)
  | cons a as => exact absurd hsplit (by simp)

/-- **PULL BUBBLE (the mirror of `NonforkKit.raise_bubble`).**  Move
`pull z bz` to the front of an arbitrary window of a witness play.  Only the
local certificate `PullSwaps` is consumed.  The induction is
letter-generic: it is the proof of `NonforkKit.raise_bubble` with the raise
replaced by the pull. -/
theorem pull_bubble :
    ∀ (γ : List Move) {Q v : State} {z : Card} {bz : Base} {β : List Move},
      ShufflePlayW Q (γ ++ Move.foundToTab z bz :: β) v →
      PullSwaps Q z bz γ →
      ShufflePlayW Q (Move.foundToTab z bz :: γ ++ β) v := by
  intro γ
  induction γ with
  | nil =>
      intro Q v z bz β h _
      simpa using h
  | cons a as ih =>
      intro Q v z bz β h hsw
      obtain ⟨S1, hrev_a, hstep_a, hrest⟩ := Bubble.walk_cons_inv h
      obtain ⟨e, hswap, hrun⟩ := hsw [] Q a as rfl (Walk.nil Q)
      have hstep_r : State.step S1 (Move.foundToTab z bz) = some e := by
        obtain ⟨s1, hs1, hrest1⟩ := State.run_cons hrun
        have hs1' : s1 = S1 := Option.some.inj (hs1.symm.trans hstep_a)
        subst hs1'
        obtain ⟨s2, hs2, hrest2⟩ := State.run_cons hrest1
        have hs2' : s2 = e := by simpa [State.run] using hrest2
        subst hs2'
        exact hs2
      have hsw' : PullSwaps S1 z bz as := by
        intro pre mid q rest hsplit hpre
        exact hsw (a :: pre) mid q rest
          (by rw [List.cons_append, hsplit])
          (Walk.cons hrev_a hstep_a hpre)
      have hIH : ShufflePlayW S1 (Move.foundToTab z bz :: as ++ β) v :=
        ih hrest hsw'
      obtain ⟨s0, hrev_r, hstep_r1, hrest2⟩ := Bubble.walk_cons_inv hIH
      have hs0 : s0 = e := Option.some.inj (hstep_r1.symm.trans hstep_r)
      subst hs0
      obtain ⟨R, hrev_R, hstep_R, hrest3⟩ := Bubble.walk_cons_inv hswap
      obtain ⟨e2, hrev_a2, hstep_a2, hnil⟩ := Bubble.walk_cons_inv hrest3
      cases hnil
      exact Walk.cons hrev_R hstep_R (Walk.cons hrev_a2 hstep_a2 hrest2)

/-- **`pull_moves_left`** — the `Witness`-level spelling: a witness play
`Q --γ ++ [pull z bz]--> W` becomes `Q --pull z bz :: γ--> W`. -/
theorem pull_moves_left {Q W : State} {z : Card} {bz : Base} {γ : List Move}
    (hplay : ShufflePlayW Q (γ ++ [Move.foundToTab z bz]) W)
    (hsw : PullSwaps Q z bz γ) :
    ShufflePlayW Q (Move.foundToTab z bz :: γ) W := by
  simpa using pull_bubble γ hplay hsw

/-- One-letter extension of the certificate. -/
theorem pullSwaps_cons {Q R : State} {z : Card} {bz : Base} {q : Move} {γ : List Move}
    (hstep : State.step Q q = some R)
    (hhead : ∃ e, ShufflePlayW Q [Move.foundToTab z bz, q] e ∧
      Q.run [q, Move.foundToTab z bz] = some e)
    (hrest : PullSwaps R z bz γ) : PullSwaps Q z bz (q :: γ) := by
  intro pre mid q' rest hsplit hpre
  cases pre with
  | nil =>
      simp only [List.nil_append] at hsplit
      injection hsplit with hq htail
      subst hq
      subst htail
      have hmid : mid = Q := by
        have h := Walk_run _ hpre
        simp only [State.run] at h
        exact (Option.some.inj h).symm
      subst hmid
      exact hhead
  | cons a as =>
      have hcons : a :: (as ++ q' :: rest) = q :: γ := by
        simpa only [List.cons_append] using hsplit
      have haq : a = q := (List.cons.inj hcons).1
      have htail : as ++ q' :: rest = γ := (List.cons.inj hcons).2
      obtain ⟨s1, hrev_a, hstep_a, hpre'⟩ := Bubble.walk_cons_inv hpre
      rw [haq] at hstep_a
      have hs1 : s1 = R := Option.some.inj (hstep_a.symm.trans hstep)
      subst hs1
      exact hrest as mid q' rest htail hpre'

/-! ## §2. Pull frames

The pull's own state edit: it chops the top of `z`'s foundation and appends
`z` to (or seats it on) the base pile.  The readers below are what the
per-letter diamond needs. -/

/-- The pull leaves every other suit's foundation top alone. -/
theorem pullSt_foundTop_ne {st : State} {z : Card} {bz : Base} {s : Suit}
    (hsu : s ≠ z.suit) : (pullSt st z bz).foundTop s = st.foundTop s := by
  unfold State.foundTop
  rw [pullSt_found_apply, ite_eq_right hsu]

/-- The pull lands `z` on the top of its target pile. -/
theorem pullSt_piles_target_top {st : State} {z : Card} {bz : Base} {k : Anchor}
    (hk : tgt st bz = some k) :
    ((pullSt st z bz).piles k).top = some z := by
  cases bz with
  | inl a0 =>
      have hka : k = a0 := (Option.some.inj hk).symm
      subst hka
      rw [pullSt_piles_inl_apply]
      simp [Pile.top, lastOf]
  | inr w0 =>
      rw [pullSt_piles_inr_apply _ _ _ _ hk]
      simp only [ite_true, Pile.top, lastOf_snoc]

/-- The pull does not move the top search of any card other than the pulled
`z` and the base card. -/
theorem pullSt_pileOfTop_of_ne {st : State} {z w : Card} {bz : Base}
    (hwf : st.WF) (htop : st.foundTop z.suit = some z)
    (hcp : st.canPlace z bz = true)
    (hwz : w ≠ z)
    (hbase : ∀ w0, bz = Sum.inr w0 → w ≠ w0) :
    (pullSt st z bz).pileOfTop w = st.pileOfTop w := by
  obtain ⟨k, hk⟩ := exists_tgt_of_canPlace hcp
  have hPwf : (pullSt st z bz).WF := step_wf hwf (by
    rw [step_foundToTab_splice htop hcp]; rfl)
  have hne_k : st.pileOfTop w ≠ some k := by
    intro h
    have htopk : (st.piles k).top = some w := (pileOfTop_eq_some_iff hwf).mp h
    cases bz with
    | inl a0 =>
        have hka : k = a0 := (Option.some.inj hk).symm
        rw [hka] at htopk
        obtain ⟨hemp, -⟩ := canPlace_inl hcp
        obtain ⟨-, hfu⟩ := (Pile.isEmpty_eq _).mp hemp
        simp only [Pile.top] at htopk
        rw [hfu] at htopk
        exact absurd htopk (by simp [lastOf])
    | inr w0 =>
        have htopk0 : (st.piles k).top = some w0 := (pileOfTop_eq_some_iff hwf).mp hk
        exact hbase w0 rfl (Option.some.inj (htopk.symm.trans htopk0))
  have hfwd : ∀ a, st.pileOfTop w = some a → a ≠ k →
      (pullSt st z bz).pileOfTop w = some a := by
    intro a ha hak
    rw [pileOfTop_eq_some_iff hPwf]
    have htopa : (st.piles a).top = some w := (pileOfTop_eq_some_iff hwf).mp ha
    rw [show (pullSt st z bz).piles a = st.piles a from pullSt_piles_ne hk hak]
    exact htopa
  have hrev : ∀ a, (pullSt st z bz).pileOfTop w = some a → st.pileOfTop w = some a := by
    intro a ha
    rw [pileOfTop_eq_some_iff hPwf] at ha
    rw [pileOfTop_eq_some_iff hwf]
    by_cases hak : a = k
    · exfalso
      have htopk : ((pullSt st z bz).piles a).top = some w := ha
      rw [hak, pullSt_piles_target_top hk] at htopk
      exact hwz ((Option.some.inj htopk).symm)
    · rw [show (pullSt st z bz).piles a = st.piles a from pullSt_piles_ne hk hak] at ha
      exact ha
  cases hw : st.pileOfTop w with
  | none =>
      have hPnone : (pullSt st z bz).pileOfTop w = none := by
        cases hP : (pullSt st z bz).pileOfTop w with
        | none => rfl
        | some a => exact absurd (hrev a hP) (by rw [hw]; simp)
      exact hPnone
  | some a =>
      have hak : a ≠ k := fun h => hne_k (by rw [← h]; exact hw)
      exact hfwd a hw hak

/-- The pull does not move the holding search of any card other than the
pulled `z`. -/
theorem pullSt_pileHolding_of_ne {st : State} {z c : Card} {bz : Base}
    (hwf : st.WF) (htop : st.foundTop z.suit = some z)
    (hcp : st.canPlace z bz = true) (hcz : c ≠ z) :
    (pullSt st z bz).pileHolding c = st.pileHolding c := by
  obtain ⟨k, hk⟩ := exists_tgt_of_canPlace hcp
  have hPwf : (pullSt st z bz).WF := step_wf hwf (by
    rw [step_foundToTab_splice htop hcp]; rfl)
  have hmem_of : ∀ a, c ∈ (st.piles a).faceUp → c ∈ ((pullSt st z bz).piles a).faceUp := by
    intro a hmem
    by_cases hak : a = k
    · rw [hak] at hmem ⊢
      cases bz with
      | inl a0 =>
          have hka : k = a0 := (Option.some.inj hk).symm
          rw [hka] at hmem ⊢
          have hemp := (canPlace_inl hcp).1
          obtain ⟨-, hfu⟩ := (Pile.isEmpty_eq _).mp hemp
          rw [hfu] at hmem
          exact absurd hmem List.not_mem_nil
      | inr w0 =>
          have hz : st.pileOfTop w0 = some k := hk
          rw [pullSt_piles_inr_apply _ _ _ _ hz]
          simp only [ite_true]
          exact List.mem_append.mpr (Or.inl hmem)
    · rw [show (pullSt st z bz).piles a = st.piles a from pullSt_piles_ne hk hak]
      exact hmem
  have hmem_back : ∀ a, c ∈ ((pullSt st z bz).piles a).faceUp → c ∈ (st.piles a).faceUp := by
    intro a hmem
    by_cases hak : a = k
    · rw [hak] at hmem ⊢
      cases bz with
      | inl a0 =>
          exfalso
          have hka : k = a0 := (Option.some.inj hk).symm
          rw [hka] at hmem
          rw [pullSt_piles_inl_apply] at hmem
          simp only [ite_true] at hmem
          rcases List.mem_cons.mp hmem with h | h
          · exact absurd h hcz
          · exact absurd h List.not_mem_nil
      | inr w0 =>
          have hz : st.pileOfTop w0 = some k := hk
          rw [pullSt_piles_inr_apply _ _ _ _ hz] at hmem
          simp only [ite_true] at hmem
          rcases List.mem_append.mp hmem with h | h
          · exact h
          · rcases List.mem_cons.mp h with h' | h'
            · exact absurd h' hcz
            · exact absurd h' List.not_mem_nil
    · rw [show (pullSt st z bz).piles a = st.piles a from pullSt_piles_ne hk hak] at hmem
      exact hmem
  cases hc : st.pileHolding c with
  | none =>
      have hPnone : (pullSt st z bz).pileHolding c = none := by
        cases hP : (pullSt st z bz).pileHolding c with
        | none => rfl
        | some a =>
            exfalso
            have hmem := pileHolding_mem hP
            have hmem' := hmem_back a hmem
            have hsome : st.pileHolding c = some a :=
              (pileHolding_eq_some_iff hwf).mpr hmem'
            rw [hc] at hsome
            exact absurd hsome (by simp)
      exact hPnone
  | some a =>
      have hmem := pileHolding_mem hc
      have hmem' := hmem_of a hmem
      exact (pileHolding_eq_some_iff hPwf).mpr hmem'

/-- The pull transports a `true` placement guard forward, provided the target
base is neither the pull's own base nor the pulled card's new seat. -/
theorem canPlace_pullSt_of_true {st : State} {c z : Card} {b b' : Base}
    (hwf : st.WF) (hc : c ∈ st.found c.suit)
    (hcp : st.canPlace c b = true)
    (hz : st.canPlace z b' = true)
    (hb : b' ≠ b) (hbc : b' ≠ Sum.inr c) :
    (pullSt st c b).canPlace z b' = true := by
  obtain ⟨k, hk⟩ := exists_tgt_of_canPlace hcp
  cases b' with
  | inl a' =>
      rw [canPlace_inl_unfold] at hz ⊢
      rw [Bool.and_eq_true] at hz ⊢
      obtain ⟨hemp, hking⟩ := hz
      obtain ⟨-, hfa⟩ := (Pile.isEmpty_eq _).mp hemp
      have hak : a' ≠ k := by
        intro h
        cases b with
        | inl a0 =>
            have hka : k = a0 := (Option.some.inj hk).symm
            exact hb (congrArg Sum.inl (h.trans hka))
        | inr w0 =>
            have hmem : w0 ∈ (st.piles k).faceUp :=
              lastOf_mem (pileOfTop_top hk).2
            rw [← h] at hmem
            rw [hfa] at hmem
            exact absurd hmem List.not_mem_nil
      refine ⟨?_, hking⟩
      rw [pullSt_piles_ne hk hak]
      exact hemp
  | inr w =>
      obtain ⟨kw, hkw, hfit⟩ := canPlace_inr hz
      rw [canPlace_inr_eq]
      have hkm : k ≠ kw := by
        intro h
        cases b with
        | inl a0 =>
            have htop : (st.piles kw).top = some w := (pileOfTop_eq_some_iff hwf).mp hkw
            rw [← h] at htop
            have hka : k = a0 := (Option.some.inj hk).symm
            rw [hka] at htop
            obtain ⟨hemp, -⟩ := canPlace_inl hcp
            obtain ⟨-, hfu⟩ := (Pile.isEmpty_eq _).mp hemp
            simp only [Pile.top] at htop
            rw [hfu] at htop
            exact absurd htop (by simp [lastOf])
        | inr w0 =>
            have htop : (st.piles kw).top = some w := (pileOfTop_eq_some_iff hwf).mp hkw
            rw [← h] at htop
            have htop0 : (st.piles k).top = some w0 := (pileOfTop_eq_some_iff hwf).mp hk
            have hw0 : w = w0 := Option.some.inj (htop.symm.trans htop0)
            exact hb (by rw [hw0])
      have hcw : c ≠ w := by
        intro h; exact hbc (by rw [h])
      rw [pullSt_pileOfTop_ne hwf hk hc hkw hkm hcw]
      exact hfit

/-- A reversible slide transports the pull's placement guard forward: its
base card stays a pile top (it may ride to the slide's target) and every
other pile is untouched. -/
theorem canPlace_slideSt_of {st : State} {c z : Card} {b bz : Base} {a k : Anchor}
    (hwf : st.WF) (hhold : st.pileHolding c = some a)
    (hcp : st.canPlace c b = true) (hk : tgt st b = some k) (hak : k ≠ a)
    (hrunv : fromCard c (st.piles a).faceUp ≠ [])
    (hcell : below c (st.piles a).faceUp ≠ [] ∨
      (below c (st.piles a).faceUp = [] ∧ (st.piles a).hidden = []))
    (hz : st.canPlace z bz = true) (hbz : bz ≠ b) :
    (slideSt st c b a).canPlace z bz = true := by
  have hcmem : c ∈ (st.piles a).faceUp := pileHolding_mem hhold
  cases bz with
  | inl a0 =>
      rw [canPlace_inl_unfold] at hz ⊢
      rw [Bool.and_eq_true] at hz ⊢
      obtain ⟨hemp, hking⟩ := hz
      obtain ⟨-, hfa⟩ := (Pile.isEmpty_eq _).mp hemp
      have ha0a : a0 ≠ a := by
        intro h
        rw [← h] at hcmem
        rw [hfa] at hcmem
        exact absurd hcmem List.not_mem_nil
      have ha0k : a0 ≠ k := by
        intro h
        cases b with
        | inl a1 =>
            have hk1 : k = a1 := (Option.some.inj hk).symm
            exact hbz (congrArg Sum.inl (h.trans hk1))
        | inr w =>
            have hmem : w ∈ (st.piles k).faceUp := lastOf_mem (pileOfTop_top hk).2
            rw [← h] at hmem
            rw [hfa] at hmem
            exact absurd hmem List.not_mem_nil
      refine ⟨?_, hking⟩
      rw [slideSt_piles_other hwf hcp hk hak hcell ha0a ha0k]
      exact hemp
  | inr w =>
      obtain ⟨k0, hk0, hfit⟩ := canPlace_inr hz
      rw [canPlace_inr_eq]
      have htopw : (slideSt st c b a).pileOfTop w = some k0 ∨
          (slideSt st c b a).pileOfTop w = some k := by
        by_cases hk0a : k0 = a
        · right
          exact slideSt_pileOfTop_source hwf hcp hk hak hrunv hcell (by rw [← hk0a]; exact hk0)
        · left
          have hk0k : k0 ≠ k := by
            intro h
            have htopw0 : (st.piles k0).top = some w := (pileOfTop_eq_some_iff hwf).mp hk0
            rw [h] at htopw0
            cases b with
            | inl a1 =>
                have hka : k = a1 := (Option.some.inj hk).symm
                rw [hka] at htopw0
                obtain ⟨hemp, -⟩ := canPlace_inl hcp
                obtain ⟨-, hfu⟩ := (Pile.isEmpty_eq _).mp hemp
                simp only [Pile.top] at htopw0
                rw [hfu] at htopw0
                exact absurd htopw0 (by simp [lastOf])
            | inr w0 =>
                have htop0 : (st.piles k).top = some w0 := (pileOfTop_eq_some_iff hwf).mp hk
                have hw0 : w = w0 := Option.some.inj (htopw0.symm.trans htop0)
                exact hbz (by rw [hw0])
          exact slideSt_pileOfTop_third hwf hcp hk hak hrunv hcell hk0 hk0a hk0k
      rcases htopw with h | h
      · rw [h]; exact hfit
      · rw [h]; exact hfit

/-! ### `SeatInert` extraction helpers -/

theorem seatInert_foundToTab {c : Card} {b bz : Base}
    (h : MtnPr.SeatInert bz (Move.foundToTab c b)) : b ≠ bz := by
  cases bz with
  | inl a => simpa [MtnPr.SeatInert] using h
  | inr w => simpa [MtnPr.SeatInert] using h

theorem seatInert_tabToTab_base {c : Card} {b bz : Base}
    (h : MtnPr.SeatInert bz (Move.tabToTab c b)) : b ≠ bz := by
  cases bz with
  | inl a => simpa [MtnPr.SeatInert] using h
  | inr w => exact h.1

theorem seatInert_tabToFound {w : Card} {bz : Base}
    (h : MtnPr.SeatInert bz (Move.tabToFound w)) : ∀ w0, bz = Sum.inr w0 → w ≠ w0 := by
  intro w0 hb
  subst hb
  simpa [MtnPr.SeatInert] using h

/-! ## §3. The per-letter diamond

A pull and a read-safe, seat-inert letter commute: both orders are legal and
land together.  Reversibility of `q` at the pull's landing is *derived*, not
assumed: the undo path is `undo-pull` after `q`, `undo-q`, then the pull again
(`reversible_after_swap` below). -/

/-- A legal pull is reversible (its guard is exactly `foundToTabR`). -/
theorem reversible_pull_of {st : State} {z : Card} {bz : Base}
    (hst : st.WF) (hpull : Pullable st z bz) :
    reversibleAtW st (Move.foundToTab z bz) := by
  rw [← foundToTabR_iff_reversibleAtW hst z bz]
  unfold foundToTabR
  rw [hpull.1]
  simp only [ite_true]
  exact hpull.2

/-- **THE PULL GUARD SURVIVES A READ-SAFE, SEAT-INERT LETTER.** -/
theorem pullable_step {st s' : State} {z : Card} {bz : Base} {q : Move}
    (hst : st.WF) (hstep : State.step st q = some s')
    (hrev : reversibleAtW st q)
    (hread : SlideFwd.ReadSafe z q) (hseat : MtnPr.SeatInert bz q)
    (hpull : Pullable st z bz) : Pullable s' z bz := by
  obtain ⟨hft, hcp⟩ := hpull
  cases q with
  | draw =>
      exact ⟨by unfold State.foundTop; rw [stepDraw_found hstep]; exact hft,
        by rw [canPlace_congr_piles (stepDraw_piles hstep)]; exact hcp⟩
  | wasteToFound c => exact absurd hrev (wasteToFound_not_reversibleAtW st c)
  | wasteToTab c b => exact absurd hrev (wasteToTab_not_reversibleAtW st c b)
  | tabToFound w =>
      obtain ⟨hnext, aw, hpa, hs⟩ := step_tabToFound_inv hstep
      have hsR : s' = raiseSt st w aw := by rw [hs]; rfl
      subst hsR
      have hsu : z.suit ≠ w.suit := hread.symm
      have hbz : bz ≠ Sum.inr w := by
        intro h
        exact (seatInert_tabToFound hseat w h) rfl
      have hft' : (raiseSt st w aw).foundTop z.suit = st.foundTop z.suit :=
        R12.foundTop_raiseSt_ne (z := w) (c := z) (a := aw) hsu
      have hcp' : (raiseSt st w aw).canPlace z bz = st.canPlace z bz :=
        R12.canPlace_raiseSt hst hpa hbz hcp
      exact ⟨by rw [hft']; exact hft, by rw [hcp']; exact hcp⟩
  | foundToTab c b =>
      obtain ⟨c', hftc, hc'c, hcpb, hs⟩ := step_foundToTab_inv hstep
      rw [hc'c] at hftc
      have hsP : s' = pullSt st c b := by rw [hs]; rfl
      subst hsP
      have hc_found : c ∈ st.found c.suit := by
        unfold State.foundTop at hftc
        exact lastOf_mem hftc
      have hbc : bz ≠ Sum.inr c := by
        intro h
        rw [h] at hcp
        obtain ⟨kw, hkw, -⟩ := canPlace_inr hcp
        have hmem : c ∈ (st.piles kw).faceUp := lastOf_mem (pileOfTop_top hkw).2
        exact ((mem_found_unique hst hc_found).1 kw).2 hmem
      have hft' : (pullSt st c b).foundTop z.suit = st.foundTop z.suit :=
        pullSt_foundTop_ne (z := c) (bz := b) (s := z.suit) hread.1.symm
      have hcp' : (pullSt st c b).canPlace z bz = true :=
        canPlace_pullSt_of_true hst hc_found hcpb hcp (Ne.symm (seatInert_foundToTab hseat)) hbc
      exact ⟨by rw [hft']; exact hft, hcp'⟩
  | tabToTab c b =>
      obtain ⟨a, hhold, hcpb, -, hs⟩ := step_tabToTab_slideSt hstep
      obtain ⟨aD, kD, hholdD, -, hkD, hkDne, -, hrunvD, hcellD⟩ := slide_data hst hrev
      have haeq : aD = a := Option.some.inj (hholdD.symm.trans hhold)
      have hcell : below c (st.piles a).faceUp ≠ [] ∨
          (below c (st.piles a).faceUp = [] ∧ (st.piles a).hidden = []) := by
        rw [← haeq]; exact hcellD
      have hrunv : fromCard c (st.piles a).faceUp ≠ [] := by
        rw [← haeq]; exact hrunvD
      have hak : kD ≠ a := by rw [← haeq]; exact hkDne
      have hsS : s' = slideSt st c b a := by rw [hs]
      subst hsS
      refine ⟨?_, ?_⟩
      · unfold State.foundTop
        rw [slideSt_found]
        exact hft
      · exact canPlace_slideSt_of hst hhold hcpb hkD hak hrunv hcell hcp
          (Ne.symm (seatInert_tabToTab_base hseat))

/-- **REVERSIBILITY AFTER A SWAP.**  If `p` is reversible at `mid'`, `q` is
reversible at `mid`, and the two orders meet (`step P q = step mid' p`), then
`q` is reversible at `pull`'s landing `P` — via the explicit undo path. -/
theorem reversible_after_swap {mid mid' P s21 : State} {p q : Move}
    (hstepq : State.step mid q = some mid')
    (hstepP : State.step mid p = some P)
    (hrevq : reversibleAtW mid q)
    (hstep21 : State.step mid' p = some s21)
    (hrevP21 : reversibleAtW mid' p)
    (hstep12 : State.step P q = some s21) :
    reversibleAtW P q := by
  obtain ⟨s1, playP, hs1, hrunP⟩ := hrevP21
  have hs1e : s1 = s21 := Option.some.inj (hs1.symm.trans hstep21)
  obtain ⟨s2, playQ, hs2, hrunQ⟩ := hrevq
  have hs2e : s2 = mid' := Option.some.inj (hs2.symm.trans hstepq)
  refine ⟨s21, playP ++ (playQ ++ [p]), hstep12, ?_⟩
  have h1 : s21.run playP = some mid' := hs1e ▸ hrunP
  have h2 : mid'.run playQ = some mid := hs2e ▸ hrunQ
  have h3 : mid.run [p] = some P := by simp only [State.run, hstepP]
  exact run_append _ _ _ _ _ h1 (run_append _ _ _ _ _ h2 h3)


/-- A reversible letter has a step. -/
theorem step_of_reversibleAtW {st : State} {m : Move} (h : reversibleAtW st m) :
    ∃ s', State.step st m = some s' := by
  obtain ⟨s', -, hs', -⟩ := h
  exact ⟨s', hs'⟩

/-- **ASSEMBLY.**  Once the swapped-order step at the pull's landing is known
to land on `pullSt mid' z bz` (the square), the certificate follows, with the
reversibility of `q` at the landing derived by `reversible_after_swap`. -/
theorem pull_swap_finish {mid mid' : State} {z : Card} {bz : Base} {q : Move}
    (hmid : mid.WF) (hrev : reversibleAtW mid q) (hpull : Pullable mid z bz)
    (hstepq : State.step mid q = some mid') (hpull' : Pullable mid' z bz)
    (hstep12 : State.step (pullSt mid z bz) q = some (pullSt mid' z bz)) :
    ∃ e, ShufflePlayW mid [Move.foundToTab z bz, q] e ∧
         mid.run [q, Move.foundToTab z bz] = some e := by
  have hrevP : reversibleAtW mid (Move.foundToTab z bz) := reversible_pull_of hmid hpull
  have hstepP : State.step mid (Move.foundToTab z bz) = some (pullSt mid z bz) := by
    rw [step_foundToTab_splice hpull.1 hpull.2]; rfl
  have hstep21 : State.step mid' (Move.foundToTab z bz) = some (pullSt mid' z bz) := by
    rw [step_foundToTab_splice hpull'.1 hpull'.2]; rfl
  have hrevP21 : reversibleAtW mid' (Move.foundToTab z bz) :=
    reversible_pull_of (step_wf hmid hstepq) hpull'
  have hrevPq : reversibleAtW (pullSt mid z bz) q :=
    reversible_after_swap hstepq hstepP hrev hstep21 hrevP21 hstep12
  refine ⟨pullSt mid' z bz,
    Walk.cons hrevP hstepP (Walk.cons hrevPq hstep12 (Walk.nil _)), ?_⟩
  exact run_append _ _ _ _ _ (run_one hstepq) (run_one hstep21)

/-- **THE LOCAL PULL DIAMOND.**  At a `WF` state with a legal pull, every
reversible read-safe seat-inert letter swaps with the pull. -/
theorem pull_swap_of_read {mid : State} {z : Card} {bz : Base} {q : Move}
    (hmid : mid.WF) (hrev : reversibleAtW mid q)
    (hread : SlideFwd.ReadSafe z q) (hseat : MtnPr.SeatInert bz q)
    (hpull : Pullable mid z bz) :
    ∃ e, ShufflePlayW mid [Move.foundToTab z bz, q] e ∧
         mid.run [q, Move.foundToTab z bz] = some e := by
  have hrevP : reversibleAtW mid (Move.foundToTab z bz) := reversible_pull_of hmid hpull
  have hstepP : State.step mid (Move.foundToTab z bz) = some (pullSt mid z bz) := by
    rw [step_foundToTab_splice hpull.1 hpull.2]; rfl
  have hzf : z ∈ mid.found z.suit := by
    have h := hpull.1
    unfold State.foundTop at h
    exact lastOf_mem h
  cases q with
  | draw =>
      obtain ⟨mid', hstepq⟩ := step_of_reversibleAtW hrev
      have hpull' : Pullable mid' z bz := pullable_step hmid hstepq hrev hread hseat hpull
      have hPwf : (pullSt mid z bz).WF := step_wf hmid hstepP
      have hstep21 : State.step mid' (Move.foundToTab z bz) = some (pullSt mid' z bz) := by
        rw [step_foundToTab_splice hpull'.1 hpull'.2]; rfl
      have hRmid : drawR mid = true := (drawR_iff_reversibleAtW hmid).mpr hrev
      have hRP : drawR (pullSt mid z bz) = true := by
        rw [show drawR (pullSt mid z bz) = drawR mid from by
          unfold drawR
          rw [pullSt_stock, pullSt_waste, pullSt_drawStep]]
        exact hRmid
      obtain ⟨s12, play12, hs12, -⟩ := (drawR_iff_reversibleAtW hPwf).mp hRP
      have hsq : pullSt mid' z bz = s12 :=
        CommuteStep.step_comm_draw_pull hmid hrev hrevP hstepq hstepP hstep21 hs12
      refine pull_swap_finish hmid hrev hpull hstepq hpull' ?_
      rw [hsq]; exact hs12
  | wasteToFound c => exact absurd hrev (wasteToFound_not_reversibleAtW mid c)
  | wasteToTab c b => exact absurd hrev (wasteToTab_not_reversibleAtW mid c b)
  | tabToFound w =>
      obtain ⟨mid', hstepq⟩ := step_of_reversibleAtW hrev
      obtain ⟨hnext, aw, hpa, -⟩ := step_tabToFound_inv hstepq
      have hpull' : Pullable mid' z bz := pullable_step hmid hstepq hrev hread hseat hpull
      have hstep21 : State.step mid' (Move.foundToTab z bz) = some (pullSt mid' z bz) := by
        rw [step_foundToTab_splice hpull'.1 hpull'.2]; rfl
      have hbase : ∀ w0, bz = Sum.inr w0 → w ≠ w0 := seatInert_tabToFound hseat
      have hnextP : (pullSt mid z bz).nextUp w = true := by
        unfold State.nextUp State.foundHeight
        rw [pullSt_found_apply, ite_eq_right hread]
        exact hnext
      have hpoP : (pullSt mid z bz).pileOfTop w = some aw := by
        rw [pullSt_pileOfTop_of_ne hmid hpull.1 hpull.2
          (fun h => hread (by rw [h])) hbase]
        exact hpa
      have hs12 : State.step (pullSt mid z bz) (Move.tabToFound w) =
          some (raiseSt (pullSt mid z bz) w aw) :=
        step_tabToFound_splice hnextP hpoP
      have hsq : raiseSt (pullSt mid z bz) w aw = pullSt mid' z bz :=
        CommuteStep.step_comm_pull_raise hmid hrevP hrev hstepP hstepq hs12 hstep21
      refine pull_swap_finish hmid hrev hpull hstepq hpull' ?_
      rw [← hsq]; exact hs12
  | foundToTab c b =>
      obtain ⟨mid', hstepq⟩ := step_of_reversibleAtW hrev
      obtain ⟨c', hftc, hc'c, hcpb, -⟩ := step_foundToTab_inv hstepq
      rw [hc'c] at hftc
      have hpull' : Pullable mid' z bz := pullable_step hmid hstepq hrev hread hseat hpull
      have hstep21 : State.step mid' (Move.foundToTab z bz) = some (pullSt mid' z bz) := by
        rw [step_foundToTab_splice hpull'.1 hpull'.2]; rfl
      have hftcP : (pullSt mid z bz).foundTop c.suit = some c := by
        rw [pullSt_foundTop_ne (z := z) (bz := bz) (s := c.suit) hread.1]
        exact hftc
      have hcpbP : (pullSt mid z bz).canPlace c b = true :=
        canPlace_pullSt_of_true hmid hzf hpull.2 hcpb
          (seatInert_foundToTab hseat) hread.2
      have hs12 : State.step (pullSt mid z bz) (Move.foundToTab c b) =
          some (pullSt (pullSt mid z bz) c b) :=
        step_foundToTab_splice hftcP hcpbP
      have hsq : pullSt (pullSt mid z bz) c b = pullSt mid' z bz :=
        CommuteStep.step_comm_pull_pull hmid hrevP hrev hstepP hstepq hs12 hstep21
      refine pull_swap_finish hmid hrev hpull hstepq hpull' ?_
      rw [← hsq]; exact hs12
  | tabToTab c b =>
      obtain ⟨mid', hstepq⟩ := step_of_reversibleAtW hrev
      obtain ⟨a, hhold, hcpb, -, -⟩ := step_tabToTab_slideSt hstepq
      have hpull' : Pullable mid' z bz := pullable_step hmid hstepq hrev hread hseat hpull
      have hstep21 : State.step mid' (Move.foundToTab z bz) = some (pullSt mid' z bz) := by
        rw [step_foundToTab_splice hpull'.1 hpull'.2]; rfl
      have hholdP : (pullSt mid z bz).pileHolding c = some a := by
        rw [pullSt_pileHolding_of_ne hmid hpull.1 hpull.2 hread.1]
        exact hhold
      have hcpbP : (pullSt mid z bz).canPlace c b = true :=
        canPlace_pullSt_of_true hmid hzf hpull.2 hcpb
          (seatInert_tabToTab_base hseat) hread.2
      have hSTEP : ∃ S12, State.step (pullSt mid z bz) (Move.tabToTab c b) = some S12 := by
        rw [step_tabToTab_eq, hholdP]
        simp only [hcpbP, ite_true]
        obtain ⟨rest, hfc⟩ := fromCard_eq_head_of_mem (pileHolding_mem hholdP)
        rw [hfc]
        exact ⟨_, rfl⟩
      obtain ⟨S12, hS12⟩ := hSTEP
      have hsq : pullSt mid' z bz = S12 :=
        CommuteStep.step_comm_slide_pull hmid hrev hrevP hstepq hstepP hstep21 hS12
      refine pull_swap_finish hmid hrev hpull hstepq hpull' ?_
      rw [hsq]; exact hS12


/-! ## §4. The certificate from `ReadSafe` + `SeatInert` -/

/-- **`PullSwaps` FROM A READ-SAFE, SEAT-INERT WINDOW.**  Structurally
`R12.raiseSwaps_of_read` (`Orig2/Fork/Class/ForkReadBracket.lean:675`): each window letter
is read-safe and seat-inert, hence survives the pull's guard
(`pullable_step`) and supplies the two-letter diamond (`pull_swap_of_read`).

The hypothesis `hpull : Pullable Q z bz` is the pull's guard at the *start* of
the window.  For the relocation residual this is exactly the readiness issue
of §6: it is free when the pull is legal at the raise's image, but it is NOT
implied by `ReadSafe` + `SeatInert` in general. -/
theorem pullSwaps_of_read {Q v : State} {z : Card} {bz : Base} {γ β : List Move}
    (hQwf : Q.WF)
    (hplay : ShufflePlayW Q (γ ++ Move.foundToTab z bz :: β) v)
    (hpull : Pullable Q z bz)
    (hread : ∀ q ∈ γ, SlideFwd.ReadSafe z q)
    (hseat : ∀ q ∈ γ, MtnPr.SeatInert bz q) : PullSwaps Q z bz γ := by
  induction γ generalizing Q v β with
  | nil => exact pullSwaps_nil Q z bz
  | cons q γ' ih =>
      rw [List.cons_append] at hplay
      obtain ⟨R, hrevq, hstepq, hplayR⟩ := Bubble.walk_cons_inv hplay
      have hreadq : SlideFwd.ReadSafe z q := hread q (List.mem_cons_self ..)
      have hseatq : MtnPr.SeatInert bz q := hseat q (List.mem_cons_self ..)
      have hpullR : Pullable R z bz :=
        pullable_step hQwf hstepq hrevq hreadq hseatq hpull
      have hhead := pull_swap_of_read hQwf hrevq hreadq hseatq hpull
      have hrest : PullSwaps R z bz γ' :=
        ih (step_wf hQwf hstepq) hplayR hpullR
          (fun x hx => hread x (List.mem_cons_of_mem q hx))
          (fun x hx => hseat x (List.mem_cons_of_mem q hx))
      exact pullSwaps_cons hstepq hhead hrest

/-- The window lemma, read-safe spelling. -/
theorem pull_moves_left_read {Q v : State} {z : Card} {bz : Base} {γ β : List Move}
    (hQ : Q.WF) (hpull : Pullable Q z bz)
    (hplay : ShufflePlayW Q (γ ++ Move.foundToTab z bz :: β) v)
    (hread : ∀ q ∈ γ, SlideFwd.ReadSafe z q)
    (hseat : ∀ q ∈ γ, MtnPr.SeatInert bz q) :
    ShufflePlayW Q (Move.foundToTab z bz :: γ ++ β) v :=
  pull_bubble γ hplay (pullSwaps_of_read hQ hplay hpull hread hseat)

/-! ## §5. The play-level reduction

The `Ready`-gated `SameCardRelocation`: the extra hypothesis is that the pull
is legal right after the raise.  With that, the pull bubbles to adjacency and
`MtnPr.adjacent_raise_pull_shortens` finishes the job. -/

/-- The readiness hypothesis of the pull-bubble route, isolated. -/
def SameCardRelocationReady : Prop :=
  ∀ (u v : State) (ρ pre γ post : List Move) (c : Card) (b : Base),
    u.WF →
    ShufflePlayW u ρ v →
    ρ = pre ++ Move.tabToFound c :: γ ++ Move.foundToTab c b :: post →
    (∀ q ∈ γ, SlideFwd.ReadSafe c q) →
    (∀ q ∈ γ, MtnPr.SeatInert b q) →
    (∀ (A B : State), ShufflePlayW u pre A →
      State.step A (Move.tabToFound c) = some B → Pullable B c b) →
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length

/-- **THE PULL-BUBBLE CLOSURE.**  Under pull readiness at the raise's image,
`SameCardRelocation` holds: bubble the pull left to adjacency, then delete the
adjacent same-card pair.  No `γ = []` special case, no minimality. -/
theorem sameCardRelocation_ready : SameCardRelocationReady := by
  intro u v ρ pre γ post c b huwf hplay hρ hread hseat hready
  -- split the play at the raise
  have hρa : ρ = pre ++ (Move.tabToFound c :: γ ++ Move.foundToTab c b :: post) := by
    rw [hρ]; simp only [List.append_assoc]
  obtain ⟨A, hpre, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hplay pre
      (Move.tabToFound c :: γ ++ Move.foundToTab c b :: post) hρa
  obtain ⟨B, hrevR, hstepR, hplayB⟩ := Bubble.walk_cons_inv hrest
  have hAwf : A.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  have hBwf : B.WF := step_wf hAwf hstepR
  have hpullB : Pullable B c b := hready A B hpre hstepR
  -- the certificate, then the bubble
  have hsw : PullSwaps B c b γ := pullSwaps_of_read hBwf hplayB hpullB hread hseat
  have hbubble : ShufflePlayW B (Move.foundToTab c b :: γ ++ post) v :=
    pull_bubble γ hplayB hsw
  have hfull : ShufflePlayW u
      (pre ++ Move.tabToFound c :: Move.foundToTab c b :: (γ ++ post)) v :=
    ShufflePlayW_append hpre (Walk.cons hrevR hstepR hbubble)
  -- the adjacent same-card pair now shortens
  obtain ⟨ρ', hρ'play, hlen⟩ := MtnPr.adjacent_raise_pull_shortens huwf hfull rfl
  refine ⟨ρ', hρ'play, ?_⟩
  rw [hρ]
  simp only [List.length_append, List.length_cons] at hlen ⊢
  omega

theorem pullable_raiseSt_of_canPlace {A : State} {c : Card} {b : Base} {a : Anchor}
    (hA : A.WF) (hpo : A.pileOfTop c = some a)
    (hcp : A.canPlace c b = true) :
    Pullable (raiseSt A c a) c b := by
  have hbz : b ≠ Sum.inr c := by
    intro h
    rw [h, MtnPr.canPlace_inr_self_false] at hcp
    exact absurd hcp (by simp)
  have hft : (raiseSt A c a).foundTop c.suit = some c := by
    simp [State.foundTop, raiseSt_found_apply, lastOf_snoc]
  exact ⟨hft,
    by rw [R12.canPlace_raiseSt hA hpo hbz hcp]; exact hcp⟩


/-! ## §6. The readiness gap is genuine (a concrete witness)

One `WF` position, one witness play of the shape `raise c ; γ ; pull c b` whose
interior is `ReadSafe c` and `SeatInert b`, yet the pull is **not** legal at the
raise's image: a bare-king raise inside `γ` empties the `inl` base.  Hence
`PullReadyAtImage` is not implied by the residual's hypotheses, and the
pull-bubble route cannot reach `SameCardRelocation` for this configuration.

Notation: `c = HK` (heart king, raised from `p0`), `w = SK` (spade king, a bare
king on `p1`), base `b = Sum.inl p1`.  Keys are on foundations `take 12`, so
both kings are raisable; diamonds and clubs sit in the stock. -/

def GAPK_C : Card := ⟨Suit.heart, Rank.king⟩
def GAPK_W : Card := ⟨Suit.spade, Rank.king⟩

def gapState : State :=
  { found := fun s => match s with
      | .heart => Suit.heart.upCards.take 12
      | .spade => Suit.spade.upCards.take 12
      | .diamond => []
      | .club => []
    piles := fun a => match a with
      | .p0 => ⟨[], [GAPK_C]⟩
      | .p1 => ⟨[], [GAPK_W]⟩
      | _ => ⟨[], []⟩
    stock := Suit.diamond.upCards ++ Suit.club.upCards
    waste := []
    drawStep := 1 }

theorem gapState_wf : gapState.WF := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro s
    cases s with
    | heart => exact ⟨12, rfl⟩
    | spade => exact ⟨12, rfl⟩
    | diamond => exact ⟨0, rfl⟩
    | club => exact ⟨0, rfl⟩
  · intro a
    cases a <;> decide
  · intro c _
    rcases c with ⟨s, r⟩
    cases s <;> cases r <;> decide

def gapB : State := raiseSt gapState GAPK_C Anchor.p0
def gapC : State := raiseSt gapB GAPK_W Anchor.p1
def gapD : State := pullSt gapC GAPK_C (Sum.inl Anchor.p1)

theorem gapState_nextUp_C : gapState.nextUp GAPK_C = true := by decide
theorem gapState_pileOfTop_C : gapState.pileOfTop GAPK_C = some Anchor.p0 := by decide
theorem gapB_nextUp_W : gapB.nextUp GAPK_W = true := by decide
theorem gapB_pileOfTop_W : gapB.pileOfTop GAPK_W = some Anchor.p1 := by decide
theorem gapC_foundTop_C : gapC.foundTop GAPK_C.suit = some GAPK_C := by
  unfold State.foundTop
  have hf : gapC.found GAPK_C.suit = gapState.found GAPK_C.suit ++ [GAPK_C] := by
    simp only [gapC, gapB, raiseSt_found_apply]
    rw [ite_eq_right (by decide : ¬ GAPK_C.suit = GAPK_W.suit)]
    simp
  rw [hf, lastOf_snoc]
theorem gapC_canPlace_C : gapC.canPlace GAPK_C (Sum.inl Anchor.p1) = true := by
  rw [canPlace_inl_unfold]; decide

theorem step_raiseC : State.step gapState (Move.tabToFound GAPK_C) = some gapB := by
  rw [step_tabToFound_splice gapState_nextUp_C gapState_pileOfTop_C]; rfl
theorem step_raiseW : State.step gapB (Move.tabToFound GAPK_W) = some gapC := by
  rw [step_tabToFound_splice gapB_nextUp_W gapB_pileOfTop_W]; rfl
theorem step_pullC : State.step gapC (Move.foundToTab GAPK_C (Sum.inl Anchor.p1)) =
    some gapD := by
  rw [step_foundToTab_splice gapC_foundTop_C gapC_canPlace_C]; rfl

theorem gapB_wf : gapB.WF := step_wf gapState_wf step_raiseC
theorem gapC_wf : gapC.WF := step_wf gapB_wf step_raiseW

theorem rev_raiseC : reversibleAtW gapState (Move.tabToFound GAPK_C) :=
  (tabToFoundR_iff_reversibleAtW gapState_wf GAPK_C).mp (by decide)
theorem rev_raiseW : reversibleAtW gapB (Move.tabToFound GAPK_W) :=
  (tabToFoundR_iff_reversibleAtW gapB_wf GAPK_W).mp (by decide)
theorem rev_pullC : reversibleAtW gapC (Move.foundToTab GAPK_C (Sum.inl Anchor.p1)) :=
  (foundToTabR_iff_reversibleAtW gapC_wf GAPK_C _).mp (by decide)

theorem gap_play : ShufflePlayW gapState
    [Move.tabToFound GAPK_C, Move.tabToFound GAPK_W,
      Move.foundToTab GAPK_C (Sum.inl Anchor.p1)] gapD :=
  Walk.cons rev_raiseC step_raiseC
    (Walk.cons rev_raiseW step_raiseW
      (Walk.cons rev_pullC step_pullC (Walk.nil gapD)))

theorem gap_readSafe : SlideFwd.ReadSafe GAPK_C (Move.tabToFound GAPK_W) := by
  show GAPK_W.suit ≠ GAPK_C.suit
  decide

theorem gap_seatInert : MtnPr.SeatInert (Sum.inl Anchor.p1) (Move.tabToFound GAPK_W) :=
  trivial

/-- The pull is NOT ready at the raise's image: pile `p1` still holds `SK`. -/
theorem gapB_not_pullable_C :
    gapB.canPlace GAPK_C (Sum.inl Anchor.p1) = false := by
  rw [canPlace_inl_unfold]; decide

def gapB2 : State := raiseSt gapState GAPK_W Anchor.p1
def gapD2 : State := slideSt gapB2 GAPK_C (Sum.inl Anchor.p1) Anchor.p0

theorem gapD2_eq_gapD : gapD2 = gapD := by
  apply State.ext
  · funext s; cases s <;> decide
  · funext a; cases a <;> decide
  · decide
  · decide
  · decide

theorem gapState_pileOfTop_W : gapState.pileOfTop GAPK_W = some Anchor.p1 := by decide
theorem gapState_nextUp_W : gapState.nextUp GAPK_W = true := by decide
theorem gapB2_pileHolding_C : gapB2.pileHolding GAPK_C = some Anchor.p0 := by decide
theorem gapB2_canPlace_C : gapB2.canPlace GAPK_C (Sum.inl Anchor.p1) = true := by
  rw [canPlace_inl_unfold]; decide

theorem step_raiseW_g : State.step gapState (Move.tabToFound GAPK_W) = some gapB2 := by
  rw [step_tabToFound_splice gapState_nextUp_W gapState_pileOfTop_W]; rfl

theorem step_slide_g : State.step gapB2 (Move.tabToTab GAPK_C (Sum.inl Anchor.p1)) =
    some gapD2 := by
  rw [step_tabToTab_eq, gapB2_pileHolding_C]
  simp only [gapB2_canPlace_C, ite_true]
  unfold gapD2 slideSt
  rw [show (gapB2.piles Anchor.p0).faceUp = [GAPK_C] by decide]
  simp [fromCard_head_eq]
theorem rev_raiseW_g : reversibleAtW gapState (Move.tabToFound GAPK_W) :=
  (tabToFoundR_iff_reversibleAtW gapState_wf GAPK_W).mp (by decide)
theorem gapB2_wf : gapB2.WF := step_wf gapState_wf step_raiseW_g
theorem rev_slide_g : reversibleAtW gapB2 (Move.tabToTab GAPK_C (Sum.inl Anchor.p1)) :=
  (tabToTabR_iff_reversibleAtW gapB2_wf GAPK_C (Sum.inl Anchor.p1)).mp (by decide)

/-- **THE SHORT ALTERNATIVE**: two letters instead of three. -/
theorem gap_short : ShufflePlayW gapState
    [Move.tabToFound GAPK_W, Move.tabToTab GAPK_C (Sum.inl Anchor.p1)] gapD := by
  rw [← gapD2_eq_gapD]
  exact Walk.cons rev_raiseW_g step_raiseW_g
    (Walk.cons rev_slide_g step_slide_g (Walk.nil gapD2))


/-! ## §8. Length corollary for the gap instance -/

theorem gap_play_len : ([Move.tabToFound GAPK_C, Move.tabToFound GAPK_W,
    Move.foundToTab GAPK_C (Sum.inl Anchor.p1)] : List Move).length = 3 := rfl

theorem gap_short_len : ([Move.tabToFound GAPK_W,
    Move.tabToTab GAPK_C (Sum.inl Anchor.p1)] : List Move).length = 2 := rfl

/-- **THE GAP INSTANCE SHORTENS** (two letters beat three) — so the residual is
not refuted by §6; only the pull-bubble route is blocked. -/
theorem gap_instance_shortens :
    ∃ ρ' : List Move, ShufflePlayW gapState ρ' gapD ∧ ρ'.length < 3 :=
  ⟨_, gap_short, by rw [gap_short_len]; decide⟩

/-! ## §9. Axiom battery -/

#print axioms PullKit.pull_bubble
#print axioms PullKit.pull_moves_left
#print axioms PullKit.pullSwaps_cons
#print axioms PullKit.pullable_step
#print axioms PullKit.pull_swap_of_read
#print axioms PullKit.reversible_after_swap
#print axioms PullKit.canPlace_pullSt_of_true
#print axioms PullKit.canPlace_slideSt_of
#print axioms PullKit.pullSt_pileOfTop_of_ne
#print axioms PullKit.pullSt_pileHolding_of_ne
#print axioms PullKit.pullSwaps_of_read
#print axioms PullKit.pull_moves_left_read
#print axioms PullKit.sameCardRelocation_ready
#print axioms PullKit.pullable_raiseSt_of_canPlace
#print axioms PullKit.gapState_wf
#print axioms PullKit.gap_play
#print axioms PullKit.gap_short
#print axioms PullKit.gap_instance_shortens

end PullKit
