import Temp.RankFront_census

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Rank-front — the proof kit (route (a): licensed steps)

`RaiseSSeq`'s head is the **last** raise, so a *play* `P = [σ₁, …, σₙ]`
(σ₁ raised first) is the word `P.reverse`; `Real s P = ∃ z, RaiseSSeq s P.reverse z`
(from `Temp/RankFront_census.lean`).

Hazard: `RaiseSSeq.cons`'s step is `State.step` only (`nextUp` + `pileOfTop`),
not `CanRaise`, so `specShift_sem_fwd` cannot be applied to a play's steps.  The
witness is `t4a_not_canRaise` / `t4a_fires` at the end: the step fires *and*
`CanRaise` fails (a commit raise flips the hidden `10♥`).  So the theorem is
stated for plays whose cards are licensed (`CanRaiseS`) at the start; that is
route (a), and it is not a proof defect — commit steps are genuinely unlicensed.
-/

namespace OneColourClosure

/-! ## §1. The rank-front word -/

/-- Insert `a` into an ascending-by-rank list (stable: on a tie `a` goes first). -/
def insRank (a : Card) : List Card → List Card
  | [] => [a]
  | b :: t => if a.rank.toIdx ≤ b.rank.toIdx then a :: b :: t else b :: insRank a t

/-- Ascending (stable) sort of a play by rank. -/
def sortRank : List Card → List Card
  | [] => []
  | a :: t => insRank a (sortRank t)

/-- **`rankFront c ws`** — the word whose *play* is `c :: sortRank (ws.erase c)`:
`c` first, then the rest of `ws` in ascending rank order. -/
def rankFront (c : Card) (ws : List Card) : List Card :=
  (sortRank (ws.erase c)).reverse ++ [c]

/-- The full statement (the target; **not** proved here). -/
def RankFrontClaim : Prop :=
  ∀ {s : State} {c : Card}, s.WF → CanRaiseS s c →
    ∀ {ws : List Card} {z : State}, RaiseSSeq s ws z → c ∈ ws →
      ∃ z', RaiseSSeq s (rankFront c ws) z'

/-! ## §2. Row 1 — propagation across a strictly-different rank -/

theorem twin_rank (c : Card) : c.twin.rank = c.rank := rfl

theorem twin_rank_toIdx (c : Card) : c.twin.rank.toIdx = c.rank.toIdx := rfl

/-- A `RaiseStepS` lands well-formed. -/
theorem raiseStepS_wf {z z' : State} {c : Card} (hz : z.WF) (h : RaiseStepS z z' c) :
    z'.WF := by
  obtain ⟨z₀, hp, hs⟩ := h
  exact step_wf (cargoPath_wf hz hp) hs

/-- **R1, one step.**  Raising a card of different rank preserves `c`'s licence;
both `specShift_sem_fwd` side conditions are automatic by rank. -/
theorem canRaiseS_step_of_rank_ne {z z' : State} {d c : Card}
    (hz : z.WF) (hstep : RaiseStepS z z' d) (hr : d.rank ≠ c.rank) :
    CanRaiseS z c → CanRaiseS z' c := by
  intro hc
  refine specShift_sem_fwd hz hstep ?_ ?_ hc
  · intro h; exact hr (by rw [h])
  · intro h; exact hr (by rw [h, twin_rank])

/-- **R1, a word.**  If every raised card has rank different from `c`'s, `c`'s
licence survives. -/
theorem canRaiseS_persist_of_rank_ne {s z : State} {ws : List Card} {c : Card}
    (h : RaiseSSeq s ws z) (hwf : s.WF)
    (hr : ∀ d ∈ ws, d.rank ≠ c.rank) (hc : CanRaiseS s c) :
    CanRaiseS z c := by
  revert hwf hr hc
  induction h with
  | nil => intro _ _ hc; exact hc
  | cons htail hp hs ih =>
      rename_i zz zz0 zz' cc wws
      intro hwf hr hc
      have hr' : ∀ d ∈ wws, d.rank ≠ c.rank :=
        fun d hd => hr d (List.mem_cons_of_mem _ hd)
      have hcc : cc.rank ≠ c.rank := hr cc (List.mem_cons_self ..)
      have hzwf : zz.WF := raiseSSeq_wf htail hwf
      have hz : CanRaiseS zz c := ih hwf hr' hc
      exact canRaiseS_step_of_rank_ne hzwf ⟨zz0, hp, hs⟩ hcc hz

/-! ## §3. Row 2 — a cover is strictly lower-ranked -/

theorem cover_rank_lt {x y : Card} (h : canSitOn x y = true) :
    x.rank.toIdx < y.rank.toIdx := by
  have := ((canSitOn_eq x y).mp h).1
  omega

theorem cover_rank_ne {x y : Card} (h : canSitOn x y = true) : x.rank ≠ y.rank := by
  intro hcon
  have := cover_rank_lt h
  rw [hcon] at this
  omega

/-! ## §4. The main positive theorem (licensed, pairwise distinct ranks) -/

/-- **Every order works** when all cards are licensed at `s` and the ranks are
pairwise distinct (row 1 makes each licence survive every other raise). -/
theorem real_of_licensed_distinct : ∀ {s : State} {P : List Card}, s.WF →
    (∀ x ∈ P, CanRaiseS s x) →
    P.Pairwise (fun a b => a.rank ≠ b.rank) →
    ∃ z', RaiseSSeq s P.reverse z'
  | _, [], _, _, _ => ⟨_, RaiseSSeq.nil _⟩
  | s, a :: t, hs, hcan, hdist => by
      have ha : CanRaiseS s a := hcan a (List.mem_cons_self ..)
      obtain ⟨s₁, hstep_a⟩ := raiseStepS_of_canRaiseS ha
      have hs₁wf : s₁.WF := raiseStepS_wf hs hstep_a
      obtain ⟨hrel, htail⟩ := List.pairwise_cons.mp hdist
      have hcan₁ : ∀ x ∈ t, CanRaiseS s₁ x := by
        intro x hx
        exact canRaiseS_step_of_rank_ne hs hstep_a
          (fun h => hrel x hx (by rw [h])) (hcan x (List.mem_cons_of_mem _ hx))
      obtain ⟨z, hz⟩ := real_of_licensed_distinct hs₁wf hcan₁ htail
      have h₁ : RaiseSSeq s [a] s₁ := by
        obtain ⟨z₀, hp, hst⟩ := hstep_a
        exact RaiseSSeq.cons (RaiseSSeq.nil s) hp hst
      refine ⟨z, ?_⟩
      rw [List.reverse_cons]
      exact raiseSSeq_append h₁ hz

/-- **The target statement in word form, under the two carried hypotheses**:
every card of the target play is licensed at `s`, and the ranks are pairwise
distinct. -/
theorem raiseS_rankfront_of_licensed {s : State} {c : Card} {ws : List Card} (hs : s.WF)
    (hcan : ∀ x ∈ c :: sortRank (ws.erase c), CanRaiseS s x)
    (hdist : (c :: sortRank (ws.erase c)).Pairwise (fun a b => a.rank ≠ b.rank)) :
    ∃ z', RaiseSSeq s (rankFront c ws) z' := by
  have hword : rankFront c ws = (c :: sortRank (ws.erase c)).reverse := by
    simp [rankFront, List.reverse_cons]
  rw [hword]
  exact real_of_licensed_distinct hs hcan hdist

/-! ## §5. The adjacent rank-swap (last two steps) -/

/-- **`swap_last_two`** — the rank-swap of the last two steps needs no replay:
fire the lower-ranked `a` at the prefix's landing, then `b`, whose licence
survives by row 1 (the ranks differ, so `b ≠ a` and `b ≠ a.twin`). -/
theorem swap_last_two {s u : State} {X : List Card} {b a : Card}
    (hX : RaiseSSeq s X.reverse u) (hu : u.WF)
    (hb : CanRaiseS u b) (ha : CanRaiseS u a)
    (hr : a.rank.toIdx < b.rank.toIdx) :
    ∃ z', RaiseSSeq s (X ++ [a, b]).reverse z' := by
  obtain ⟨u₂, z₀, hp_a, hs_a⟩ := raiseStepS_of_canRaiseS ha
  have hstep_a : RaiseStepS u u₂ a := ⟨z₀, hp_a, hs_a⟩
  have hu₂ : u₂.WF := raiseStepS_wf hu hstep_a
  have hb₂ : CanRaiseS u₂ b :=
    canRaiseS_step_of_rank_ne hu hstep_a (fun h => by rw [h] at hr; omega) hb
  obtain ⟨u₃, z₁, hp_b, hs_b⟩ := raiseStepS_of_canRaiseS hb₂
  refine ⟨u₃, ?_⟩
  rw [show (X ++ [a, b]).reverse = b :: a :: X.reverse from by simp]
  exact RaiseSSeq.cons (RaiseSSeq.cons hX hp_a hs_a) hp_b hs_b

/-! ## §6. The hazard, kernel-checked: a legal step that is not licensed -/

theorem t4a_pileOfTop_9S : t4a.pileOfTop e9S = some Anchor.p0 := by decide

/-- At `t4a`, `9♠` is the only face-up card over a nonempty hidden deck, so it is
**not** `CanRaise`-able — yet `t4a_step_9S` fires. -/
theorem t4a_not_canRaise : ¬ CanRaise t4a e9S := by
  rintro ⟨-, a, hpa, hdisj⟩
  rw [t4a_pileOfTop_9S] at hpa
  have ha : a = Anchor.p0 := Option.some.inj hpa.symm ▸ rfl
  subst ha
  rcases hdisj with hchop | ⟨hhidden, -⟩
  · exact absurd hchop (by decide)
  · exact absurd hhidden (by decide)

/-- The same state's step *does* fire (`RaiseSSeq` allows it). -/
theorem t4a_fires : State.step t4a (Move.tabToFound e9S) = some t4b := t4a_step_9S

end OneColourClosure

#print axioms OneColourClosure.twin_rank
#print axioms OneColourClosure.raiseStepS_wf
#print axioms OneColourClosure.canRaiseS_step_of_rank_ne
#print axioms OneColourClosure.canRaiseS_persist_of_rank_ne
#print axioms OneColourClosure.cover_rank_lt
#print axioms OneColourClosure.cover_rank_ne
#print axioms OneColourClosure.real_of_licensed_distinct
#print axioms OneColourClosure.raiseS_rankfront_of_licensed
#print axioms OneColourClosure.swap_last_two
#print axioms OneColourClosure.t4a_not_canRaise
