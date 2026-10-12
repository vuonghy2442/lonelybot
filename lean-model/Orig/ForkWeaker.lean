import Orig.PositionSeat
import Orig.ForkStateS

/-!
# Orig.ForkWeaker — THE STRONG-TO-WEAK BRIDGE

Every maneuver-stable `forkState` is a `weakForkState` (the retired
three-clause detection) with the SAME witness `x`: the rung pins travel
free through the S-iff's pair-live halves (`canRaiseS_rung`), and the
vanilla unique-raiser iff follows from the S-saturation — the witness's
own vanilla liveness is forced by the covered-twin geometry: if the
witness were covered, its twin would either raise now (against the
orientation pin `¬ CanRaise st x.twin`) or sit covered while topping
(against the run discipline's descent law, `runOK_desc`).
-/

/-! ## §0. The private kit -/

private theorem lastOf_cons_tail {w : Card} {L : List Card} (h : L ≠ []) :
    lastOf (w :: L) = lastOf L := by
  cases L with
  | nil => exact absurd rfl h
  | cons y t => rfl

private theorem lastOf_append_tail {t : List Card} (ht : t ≠ []) :
    ∀ (bs : List Card), lastOf (bs ++ t) = lastOf t := by
  intro bs
  induction bs with
  | nil => rfl
  | cons w ws ih =>
      have hne : ws ++ t ≠ [] := by
        intro hcon
        apply ht
        cases ws with
        | nil => rw [List.nil_append] at hcon; exact hcon
        | cons v vs => exact absurd hcon (by simp)
      rw [List.cons_append, lastOf_cons_tail hne, ih]

private theorem nextUp_of_rung {st : State} {c : Card}
    (hr : rungAt st c.suit = c.rank.toIdx) : st.nextUp c = true := by
  show decide (c.rank.toIdx = (st.found c.suit).length) = true
  exact decide_eq_true hr.symm

/-! ## §1. The witness's vanilla liveness -/

/-- **THE WITNESS'S VANILLA LIVENESS** — the covered-twin geometry: from
the two-conjunct parcel alone, the witness `x` raises at the vanilla
grade.  Either `x` tops its position (the license assembles), or it is
covered — and then the twin's S-life positions the twin: if the twin
tops, `CanRaise st x.twin` fires against the orientation pin; if `x`
tops somewhere else while covered in its own pile, the two positions
disagree with the run discipline's strict descent (`runOK_desc`). -/
theorem forkState_witness_canRaise {st : State} {x : Card} (hwf : st.WF)
    (hiff : ∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS st c)
    (hnt : ¬ CanRaise st x.twin) : CanRaise st x := by
  have hxS : CanRaiseS st x := (hiff x).mp (Or.inl rfl)
  have hnext : st.nextUp x = true := nextUp_of_rung (canRaiseS_rung hxS)
  obtain ⟨a, bs, run, hshape, hseat⟩ := canRaiseS_positionSeat hwf hxS
  have htopcase : run = [] ∨ ∃ d rest, run = d :: rest := by
    cases run with
    | nil => exact Or.inl rfl
    | cons d rest => exact Or.inr ⟨d, rest, rfl⟩
  rcases htopcase with rfl | ⟨d, rest, rfl⟩
  · have htop : (st.piles a).top = some x := by
      show lastOf (st.piles a).faceUp = some x
      rw [hshape]
      exact lastOf_snoc
    have hseat' : chop (st.piles a).faceUp ≠ [] ∨
        ((st.piles a).hidden = [] ∧ x.rank = Rank.king) := by
      rw [hshape]
      rcases hseat with hbs | hhk
      · exact Or.inl (by rw [chop_snoc]; exact hbs)
      · exact Or.inr hhk
    exact ⟨hnext, a, (pileOfTop_eq_some_iff hwf).2 htop, hseat'⟩
  · exfalso
    have hxtwinS : CanRaiseS st x.twin := (hiff x.twin).mp (Or.inr rfl)
    have hnextt : st.nextUp x.twin = true :=
      nextUp_of_rung (canRaiseS_rung hxtwinS)
    obtain ⟨a', bs', run', hshape', hseat'⟩ :=
      canRaiseS_positionSeat hwf hxtwinS
    have hdich : run' = [] ∨ st.pileOfTop x.twin.twin ≠ none :=
      canRaiseS_runOrTwin hwf hxtwinS a' bs' run' hshape'
    rw [Card.twin_twin] at hdich
    rcases hdich with rfl | hpxne
    · have htopt : (st.piles a').top = some x.twin := by
        show lastOf (st.piles a').faceUp = some x.twin
        rw [hshape']
        exact lastOf_snoc
      have hseatt : chop (st.piles a').faceUp ≠ [] ∨
          ((st.piles a').hidden = [] ∧ x.twin.rank = Rank.king) := by
        rw [hshape']
        rcases hseat' with hbs' | hhk'
        · exact Or.inl (by rw [chop_snoc]; exact hbs')
        · exact Or.inr hhk'
      exact hnt ⟨hnextt, a', (pileOfTop_eq_some_iff hwf).2 htopt, hseatt⟩
    · obtain ⟨c, hpx⟩ := option_some_of_ne_none hpxne
      have hxmema : x ∈ (st.piles a).faceUp := by
        rw [hshape]
        exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
      have hxmemc : x ∈ (st.piles c).faceUp :=
        Pile.mem_of_top (pileOfTop_top hpx).2
      have hca : c = a := by
        by_cases hcon : c = a
        · exact hcon
        · exact absurd hxmemc ((mem_faceUp_unique hwf hxmema c hcon).1)
      rw [hca] at hpx
      have hlast : lastOf (st.piles a).faceUp = some x := (pileOfTop_top hpx).2
      rw [hshape] at hlast
      rw [lastOf_append_tail (by simp)] at hlast
      rw [lastOf_cons_tail (by simp)] at hlast
      have hxrun : x ∈ d :: rest := lastOf_mem hlast
      have hok2 : runOK (bs ++ x :: d :: rest) = true := by
        rw [← hshape]
        exact hwf.runOK_of a
      have hdesc : x.rank.toIdx < x.rank.toIdx :=
        runOK_desc (P := bs ++ [x]) (S := d :: rest)
          (by rw [show (bs ++ [x]) ++ (d :: rest)
                  = bs ++ x :: d :: rest from by
                rw [List.append_assoc]; rfl]
              exact hok2)
          (by simp) hxrun
      omega

/-! ## §2. The public bridge rows -/

/-- **THE STRONG-TO-WEAK BRIDGE** — every maneuver-stable forkState is a
weakForkState (the old three-clause detection), with THE SAME witness x:
the rung pins travel free (the in-tree forkState_pins pattern — via
`canRaiseS_rung`), and the vanilla unique-raiser iff follows from the
S-saturation. -/
theorem forkState_to_weak {st : State} (hwf : st.WF) (h : forkState st) :
    weakForkState st := by
  obtain ⟨x, hiff, hnt⟩ :
    ∃ x : Card, (∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS st c) ∧
      ¬ CanRaise st x.twin := h
  have hrx : rungAt st x.suit = x.rank.toIdx :=
    canRaiseS_rung ((hiff x).mp (Or.inl rfl))
  have hrt : rungAt st x.twin.suit = x.rank.toIdx := by
    have hr := canRaiseS_rung ((hiff x.twin).mp (Or.inr rfl))
    rwa [Card.twin_rank] at hr
  refine ⟨x, hrx, hrt, ?_⟩
  intro c
  constructor
  · intro hc
    rcases (hiff c).mpr (CanRaiseS.now c hc) with hce | hct
    · exact hce
    · rw [hct] at hc
      exact absurd hc hnt
  · intro hcx
    rw [hcx]
    exact forkState_witness_canRaise hwf hiff hnt

/-- The witness's geometry: it tops with a license-read seat. -/
theorem forkState_witness_tops {st : State} (hwf : st.WF) (h : forkState st) :
    ∃ x a, st.pileOfTop x = some a ∧ CanRaise st x := by
  obtain ⟨x, hiff, hnt⟩ :
    ∃ x : Card, (∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS st c) ∧
      ¬ CanRaise st x.twin := h
  have hcan : CanRaise st x := forkState_witness_canRaise hwf hiff hnt
  obtain ⟨-, a, hpod, -⟩ := id hcan
  exact ⟨x, a, hpod, hcan⟩

/-! ## The audit battery -/

#print axioms forkState_witness_canRaise
#print axioms forkState_to_weak
#print axioms forkState_witness_tops
