import Temp.SpecShift_sem

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-!
# The corrected target `raiseS_reorder_front` — still FALSE

The corrected statement (word convention fixed: the head of a `RaiseSSeq` word is
the *last* raise, so appending `c` at the tail makes `c` the **first** raise):

    s.WF → CanRaiseS s c → RaiseSSeq s ws z → c ∈ ws →
      ∃ z', RaiseSSeq s (ws.erase c ++ [c]) z'

is **false too**.  A card can be forced to be raised *last* even when it is
raisableS at the start, because raising it first founds the only remaining seat
of its twin's cover.

The counterexample (a well-formed state, `probeState` below):

    pile p0:  K♥        (a bare king — the card `c`, raisable now)
    pile p1:  K♦  Q♠    (c's twin `K♦`, covered by `Q♠`)
    found:    ♠↦A..J, ♥↦A..Q, ♦↦A..Q, ♣↦[]
    rest:     stock

The legal play (chronologically `K♦`, then `Q♠`, then `K♥`; word `[K♥, Q♠, K♦]`):

* slide `Q♠` from `K♦` onto `K♥` (a reversible cargo leg), then raise `K♦`;
* raise `Q♠`; then raise `K♥`.

The corrected target demands the word `[Q♠, K♦, K♥]` (chronologically `K♥`,
`K♦`, `Q♠`).  After `K♥` is founded, `Q♠` has **no seat at all** (`Q♠` can only
sit on a red king; `K♥` is founded, `K♦` is beneath it), so `Q♠` stays on `K♦`
in every cargo mate — hence `K♦` is never a pile top and the second raise can
never fire.  `probe_not_raiseSeq_front` below machine-checks this.

Consequently only ONE hypothesis can repair the statement: excluding the twin.
With `c.twin ∉ ws` every other card's license is `specShift_sem_fwd`-stable, and
the general statement reduces to a single block-replay obligation (§9,
`raiseS_reorder_front_of_block`).  The true unconditional fragments are in §8:
the two one-swap lemmas, twin-free persistence, twin-free deferral, and the
corrected-direction two-card reordering `raiseSSeq_front_two`.

House compliance: no `sorry`, no `Classical.choice`, no `noncomputable`; battery
at the tail.  Requires the compiled `Temp/SpecShift_sem` module
(`lake env lean -o .lake/build/lib/lean/Temp/SpecShift_sem.olean
Temp/SpecShift_sem.lean`).
-/

namespace OneColourClosure

/-! ## §1. The probe state -/

/-- `c` — a bare king, raisableS at the probe state, moved to the front. -/
def cKH : Card := ⟨Suit.heart, Rank.king⟩

/-- `c.twin` — covered by `cQS`. -/
def cKD : Card := ⟨Suit.diamond, Rank.king⟩

/-- The cover of `c.twin`; its only seats are `c.twin` and `c`. -/
def cQS : Card := ⟨Suit.spade, Rank.queen⟩

theorem cKD_twin : cKD.twin = cKH := by decide

/-- The probe state: `p0` holds the bare king `K♥`, `p1` holds `Q♠` on `K♦`. -/
def probeState : State where
  found := fun su =>
    match su with
    | .spade => (Suit.upCards .spade).take 11
    | .heart => (Suit.upCards .heart).take 12
    | .diamond => (Suit.upCards .diamond).take 12
    | .club => []
  piles := fun a =>
    match a with
    | .p0 => ⟨[], [cKH]⟩
    | .p1 => ⟨[], [cKD, cQS]⟩
    | _ => ⟨[], []⟩
  stock := (Suit.upCards .spade).drop 12 ++ Suit.upCards .club
  waste := []
  drawStep := 1

/-- The probe state is well formed. -/
theorem probeState_WF : probeState.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro su
    match su with
    | .spade => exact ⟨11, by decide⟩
    | .heart => exact ⟨12, by decide⟩
    | .diamond => exact ⟨12, by decide⟩
    | .club => exact ⟨0, by decide⟩
  · intro a
    match a with
    | .p0 => decide
    | .p1 => decide
    | .p2 => decide
    | .p3 => decide
    | .p4 => decide
    | .p5 => decide
    | .p6 => decide
  · intro c _
    rcases c with ⟨su, r⟩
    cases su <;> cases r <;> decide
  · decide

theorem probe_nextUp_KH : probeState.nextUp cKH = true := by decide

theorem probe_pileOfTop_KH : probeState.pileOfTop cKH = some Anchor.p0 := by decide

theorem probe_seat_QS : seatOf probeState cQS = some (Sum.inr cKD) := by decide

/-- `K♥` is raisableS at the probe state (a bare king, next-up). -/
theorem probe_canRaiseS_KH : CanRaiseS probeState cKH :=
  CanRaiseS.now cKH
    ⟨probe_nextUp_KH, ⟨Anchor.p0, probe_pileOfTop_KH,
      Or.inr ⟨by decide, by decide⟩⟩⟩

/-! ## §2. The slide `Q♠ : K♦ → K♥` -/

/-- The landing of sliding `Q♠` from `K♦` onto `K♥`. -/
def slideState : State :=
  (probeState.setPile Anchor.p1
      (Pile.afterRunRemoved (probeState.piles Anchor.p1)
        (below cQS (probeState.piles Anchor.p1).faceUp))).putRun
    (fromCard cQS (probeState.piles Anchor.p1).faceUp) (Sum.inr cKH)

theorem probe_step_slide :
    State.step probeState (Move.tabToTab cQS (Sum.inr cKH)) = some slideState := by
  rw [step_tabToTab_eq]
  have hhold : probeState.pileHolding cQS = some Anchor.p1 := by decide
  have hcp : probeState.canPlace cQS (Sum.inr cKH) = true := by decide
  rw [hhold]
  simp only [hcp, ite_true]
  rfl

theorem probe_slide_cargoLeg : CargoLeg probeState slideState := by
  refine ⟨cQS, Sum.inr cKH, probe_step_slide, ?_⟩
  exact (tabToTabR_iff_reversibleAtW probeState_WF cQS (Sum.inr cKH)).mp (by decide)

theorem probe_cargoPath_slide : CargoPath probeState slideState :=
  Steps.cons probe_slide_cargoLeg (Steps.refl slideState)

/-! ## §3. The rest of the play -/

theorem slide_nextUp_KD : slideState.nextUp cKD = true := by decide

theorem slide_pileOfTop_KD : slideState.pileOfTop cKD = some Anchor.p1 := by decide

/-- The landing of raising `K♦` at `slideState`. -/
def afterD : State :=
  { slideState.setFound cKD.suit (slideState.found cKD.suit ++ [cKD]) with
    piles := fun a' =>
      if a' = Anchor.p1 then
        Pile.afterRunRemoved (slideState.piles Anchor.p1)
          (chop (slideState.piles Anchor.p1).faceUp)
      else slideState.piles a' }

theorem slide_step_KD : State.step slideState (Move.tabToFound cKD) = some afterD :=
  step_tabToFound_splice slide_nextUp_KD slide_pileOfTop_KD

theorem afterD_nextUp_QS : afterD.nextUp cQS = true := by decide

theorem afterD_pileOfTop_QS : afterD.pileOfTop cQS = some Anchor.p0 := by decide

/-- The landing of raising `Q♠` at `afterD`. -/
def afterQ : State :=
  { afterD.setFound cQS.suit (afterD.found cQS.suit ++ [cQS]) with
    piles := fun a' =>
      if a' = Anchor.p0 then
        Pile.afterRunRemoved (afterD.piles Anchor.p0)
          (chop (afterD.piles Anchor.p0).faceUp)
      else afterD.piles a' }

theorem afterD_step_QS : State.step afterD (Move.tabToFound cQS) = some afterQ :=
  step_tabToFound_splice afterD_nextUp_QS afterD_pileOfTop_QS

theorem afterQ_nextUp_KH : afterQ.nextUp cKH = true := by decide

theorem afterQ_pileOfTop_KH : afterQ.pileOfTop cKH = some Anchor.p0 := by decide

/-- The landing of raising `K♥` at `afterQ`. -/
def afterK : State :=
  { afterQ.setFound cKH.suit (afterQ.found cKH.suit ++ [cKH]) with
    piles := fun a' =>
      if a' = Anchor.p0 then
        Pile.afterRunRemoved (afterQ.piles Anchor.p0)
          (chop (afterQ.piles Anchor.p0).faceUp)
      else afterQ.piles a' }

theorem afterQ_step_KH : State.step afterQ (Move.tabToFound cKH) = some afterK :=
  step_tabToFound_splice afterQ_nextUp_KH afterQ_pileOfTop_KH

/-- **The original play is legal**: chronologically `K♦`, `Q♠`, `K♥` — i.e. the
word `[K♥, Q♠, K♦]` (the word head is the last raise). -/
theorem probe_raiseSeq : RaiseSSeq probeState [cKH, cQS, cKD] afterK :=
  RaiseSSeq.cons
    (RaiseSSeq.cons
      (RaiseSSeq.cons (RaiseSSeq.nil probeState) probe_cargoPath_slide slide_step_KD)
      (Steps.refl afterD) afterD_step_QS)
    (Steps.refl afterQ) afterQ_step_KH

/-! ## §4. Foundations are cargo-invariant -/

theorem found_cargoLeg {a b : State} (h : CargoLeg a b) : b.found = a.found := by
  obtain ⟨c, bb, hstep, -⟩ := h
  obtain ⟨a₀, -, -, -, hv⟩ := step_tabToTab_inv hstep
  rw [hv, putRun_found, setPile_found]

theorem found_cargoPath {a b : State} (h : CargoPath a b) : b.found = a.found := by
  induction h with
  | refl => rfl
  | cons hleg _ ih => rw [ih, found_cargoLeg hleg]

/-- `Parented` is orbit-invariant (hence cargo-path invariant). -/
theorem parented_of_cargoPath {a b : State} (hwf : a.WF) (h : CargoPath a b)
    {x : Card} (hk : x.rank ≠ Rank.king) (hp : Parented a x) : Parented b x :=
  (parented_orbit_rung hwf (sameOrbit_of_cargoPath h) (fun σ => rungAt_cargoPath h σ)
    hk).mp hp

/-! ## §5. `K♦` can never be raised after `K♥` is founded -/

/-- **The cover's seat survives** — after `K♥` is raised (from any cargo mate of
the probe state), `Q♠` still sits on `K♦` in every further cargo mate; hence
`K♦` is never a pile top and can never be raised. -/
theorem no_step_KD_after_KH {u₀ u₁ : State}
    (hpath : CargoPath probeState u₀)
    (hstep : State.step u₀ (Move.tabToFound cKH) = some u₁) :
    ∀ u₂, CargoPath u₁ u₂ → State.step u₂ (Move.tabToFound cKD) = none := by
  intro u₂ hpath2
  by_cases hfire : State.step u₂ (Move.tabToFound cKD) = none
  · exact hfire
  · exfalso
    obtain ⟨v, hv⟩ : ∃ v, State.step u₂ (Move.tabToFound cKD) = some v := by
      cases h : State.step u₂ (Move.tabToFound cKD) with
      | none => exact absurd h hfire
      | some v => exact ⟨v, rfl⟩
    have hwu₀ : u₀.WF := cargoPath_wf probeState_WF hpath
    have hwu₁ : u₁.WF := step_wf hwu₀ hstep
    have hwu₂ : u₂.WF := cargoPath_wf hwu₁ hpath2
    -- `Q♠` stays seated all the way
    have hparS : Parented probeState cQS := ⟨cKD, probe_seat_QS⟩
    have hpar₀ : Parented u₀ cQS :=
      parented_of_cargoPath probeState_WF hpath (by decide) hparS
    have hpar₁ : Parented u₁ cQS :=
      parented_tabToFound_of_ne hwu₀ hstep (by decide) hpar₀
    have hpar₂ : Parented u₂ cQS := parented_of_cargoPath hwu₁ hpath2 (by decide) hpar₁
    -- and its seat is `K♦` (the only other possibility `K♥` is founded)
    obtain ⟨z, hz⟩ := hpar₂
    have hfit : canSitOn cQS z = true := by
      obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hz
      exact (tfc_seat_parent hwu₂ hhold hlast).1
    have hxz : z = cKD ∨ z = cKH := by
      have hx : canSitOn cQS cKD.twin = true := by rw [cKD_twin]; decide
      have hcs := cover_seats (c := cKD) (x := cQS) (y := z) hx hfit
      rwa [cKD_twin] at hcs
    have hKHfound : cKH ∈ u₂.found cKH.suit := by
      have h1 : cKH ∈ u₁.found cKH.suit := by
        rw [found_tabToFound hstep cKH.suit, ite_eq_left rfl]
        exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
      rw [found_cargoPath hpath2]
      exact h1
    have hz_ne : z ≠ cKH := by
      rintro rfl
      obtain ⟨a, -, -, hlast⟩ := tfc_seatOf_of_inr hz
      have hmem : cKH ∈ (u₂.piles a).faceUp := mem_below _ (lastOf_mem hlast)
      exact ((mem_found_unique hwu₂ hKHfound).1 a).2 hmem
    have hseat : seatOf u₂ cQS = some (Sum.inr cKD) := by
      rcases hxz with h | h
      · rw [h] at hz; exact hz
      · exact absurd h hz_ne
    have hnotop : u₂.pileOfTop cKD = none := no_top_of_seat hwu₂ hseat
    obtain ⟨-, a, hpa, -⟩ := step_tabToFound_inv hv
    rw [hnotop] at hpa
    exact absurd hpa (by simp)

/-! ## §6. The corrected target word is illegal -/

/-- **The front-reordered word `[Q♠, K♦, K♥]` is not legal** (chronologically
`K♥`, `K♦`, `Q♠`): the second raise `K♦` can never fire. -/
theorem probe_not_raiseSeq_front : ¬ ∃ z', RaiseSSeq probeState [cQS, cKD, cKH] z' := by
  rintro ⟨z', hz'⟩
  cases hz' with
  | cons h1 hp1 hs1 =>
      cases h1 with
      | cons h2 hp2 hs2 =>
          cases h2 with
          | cons h3 hp3 hs3 =>
              cases h3
              have hnone := no_step_KD_after_KH hp3 hs3 _ hp2
              rw [hs2] at hnone
              exact absurd hnone (by simp)

/-! ## §7. The corrected statement is false -/

/-- The corrected reordering target: `c` appended at the **tail** of the word,
i.e. `c` raised **first** (`RaiseSSeq`'s head is the last raise). -/
def RaiseSReorderFront : Prop :=
  ∀ {s : State} {c : Card}, s.WF → CanRaiseS s c →
    ∀ {ws : List Card} {z : State}, RaiseSSeq s ws z → c ∈ ws →
      ∃ z', RaiseSSeq s (ws.erase c ++ [c]) z'

/-- **THE CORRECTED STATEMENT IS FALSE.**

At `probeState`: `K♥` is raisableS, the legal word `[K♥, Q♠, K♦]` (chronologically
`K♦`, `Q♠`, `K♥`) contains `K♥`, but the front-reordered word `[Q♠, K♦, K♥]`
(chronologically `K♥`, `K♦`, `Q♠`) is illegal, because raising `K♥` first
founds the only remaining seat of `Q♠` (the cover of `K♥`'s twin `K♦`). -/
theorem raiseSReorderFront_false : ¬ RaiseSReorderFront := by
  intro hR
  have hmem : cKH ∈ [cKH, cQS, cKD] := by simp
  obtain ⟨z', hz'⟩ := hR probeState_WF probe_canRaiseS_KH probe_raiseSeq hmem
  have hw : [cKH, cQS, cKD].erase cKH ++ [cKH] = [cQS, cKD, cKH] := by decide
  rw [hw] at hz'
  exact probe_not_raiseSeq_front ⟨z', hz'⟩

/-! ## §8. The true fragments (all unconditional, no `SpecShift` hypothesis)

The forward shift `specShift_sem_fwd` is all that is needed for the *usable*
direction: a raise never destroys another card's license (except its twin's).
Hence the swaps, the twin-free persistence and the twin-free deferral are
unconditional. -/

/-- A `CanRaiseS` license fires a `RaiseStepS`. -/
theorem raiseStepS_of_canRaiseS {z : State} {c : Card} (h : CanRaiseS z c) :
    ∃ z', RaiseStepS z z' c := by
  obtain ⟨z₀, hp, hcr⟩ := h
  obtain ⟨z', hs⟩ := step_tabToFound_of_canRaise hcr
  exact ⟨z', z₀, hp, hs⟩

/-- Append one raise to a raiseS sequence. -/
theorem raiseSSeq_snoc {s z : State} {ws : List Card} {c : Card}
    (h : RaiseSSeq s ws z) (hz : ∃ z', RaiseStepS z z' c) :
    ∃ z', RaiseSSeq s (c :: ws) z' := by
  obtain ⟨z', z₀, hp, hs⟩ := hz
  exact ⟨z', RaiseSSeq.cons h hp hs⟩

/-- Sequence composition (`w₁` first, then `w₂`, gives the word `w₂ ++ w₁`). -/
theorem raiseSSeq_append {s u v : State} {w₁ w₂ : List Card}
    (h₁ : RaiseSSeq s w₁ u) (h₂ : RaiseSSeq u w₂ v) :
    RaiseSSeq s (w₂ ++ w₁) v := by
  induction h₂ generalizing s with
  | nil => exact h₁
  | cons _ hp hs ih =>
      rw [List.cons_append]
      exact RaiseSSeq.cons (ih h₁) hp hs

/-- A raiseS word transports well-formedness. -/
theorem raiseSSeq_wf {s z : State} {ws : List Card} (h : RaiseSSeq s ws z)
    (hwf : s.WF) : z.WF := by
  revert hwf
  induction h with
  | nil => exact id
  | cons _ hp hs ih => exact fun hwf => step_wf (cargoPath_wf (ih hwf) hp) hs

/-- **TWIN-FREE PERSISTENCE (unconditional)** — a raiseS word avoiding `c` and
`c.twin` never disturbs `c`'s licence.  Only `specShift_sem_fwd` is used. -/
theorem canRaiseS_persist_fwd {s z : State} {ws : List Card} {x : Card}
    (h : RaiseSSeq s ws z) (hwf : s.WF)
    (hx : x ∉ ws) (hxt : x.twin ∉ ws) (hcan : CanRaiseS s x) :
    CanRaiseS z x := by
  revert hwf hx hxt hcan
  induction h with
  | nil => intro _ _ _ hcan; exact hcan
  | cons htail hp hs ih =>
      rename_i zz zz0 zz' cc wws
      intro hwf hx hxt hcan
      have hx' : x ∉ wws := fun hmem => hx (List.mem_cons_of_mem _ hmem)
      have hxt' : x.twin ∉ wws := fun hmem => hxt (List.mem_cons_of_mem _ hmem)
      have hxd : x ≠ cc := fun hcon => hx (by rw [hcon]; exact List.mem_cons_self ..)
      have hxtd : x ≠ cc.twin := by
        intro hcon
        have hmem : x.twin ∈ cc :: wws := by
          rw [hcon]
          exact List.mem_cons.mpr (Or.inl (card_twin_twin cc))
        exact hxt hmem
      have hzwf : zz.WF := raiseSSeq_wf htail hwf
      have hz : CanRaiseS zz x := ih hwf hx' hxt' hcan
      exact (specShift_sem_fwd hzwf ⟨zz0, hp, hs⟩ hxd hxtd) hz

/-- **DEFER PAST A TWIN-FREE WORD (unconditional)**: a card absent from the word
(together with its twin) can always be raised last. -/
theorem raiseSSeq_defer {s z : State} {ws : List Card} {x : Card}
    (h : RaiseSSeq s ws z) (hwf : s.WF)
    (hx : x ∉ ws) (hxt : x.twin ∉ ws) (hcan : CanRaiseS s x) :
    ∃ z', RaiseSSeq s (x :: ws) z' :=
  raiseSSeq_snoc h (raiseStepS_of_canRaiseS (canRaiseS_persist_fwd h hwf hx hxt hcan))

/-- **ONE-SWAP, `c` FIRST (unconditional)**. -/
theorem swap_c_first {s : State} {c d : Card} (hs : s.WF)
    (hc : CanRaiseS s c) (hd : CanRaiseS s d)
    (hdc : d ≠ c) (hdt : d ≠ c.twin) :
    ∃ s₂, RaiseStepS s s₂ c ∧ ∃ s₃, RaiseStepS s₂ s₃ d := by
  obtain ⟨s₂, hs₂⟩ := raiseStepS_of_canRaiseS hc
  have hd₂ : CanRaiseS s₂ d := specShift_sem_fwd hs hs₂ hdc hdt hd
  obtain ⟨s₃, hs₃⟩ := raiseStepS_of_canRaiseS hd₂
  exact ⟨s₂, hs₂, s₃, hs₃⟩

/-- **ONE-SWAP, `d` FIRST (unconditional)** — the direction the front reordering
needs (a card passing a block). -/
theorem swap_d_first {s : State} {c d : Card} (hs : s.WF)
    (hc : CanRaiseS s c) (hd : CanRaiseS s d)
    (hcd : c ≠ d) (hct : c ≠ d.twin) :
    ∃ s₂, RaiseStepS s s₂ d ∧ ∃ s₃, RaiseStepS s₂ s₃ c := by
  obtain ⟨s₂, hs₂⟩ := raiseStepS_of_canRaiseS hd
  have hc₂ : CanRaiseS s₂ c := specShift_sem_fwd hs hs₂ hcd hct hc
  obtain ⟨s₃, hs₃⟩ := raiseStepS_of_canRaiseS hc₂
  exact ⟨s₂, hs₂, s₃, hs₃⟩

/-- **THE ONE-SWAP IN THE CORRECTED DIRECTION** — the corrected target for the
two-element word: moving `c` to the front past a non-twin `d` is legal.  (The
hypotheses `hc`/`hd` are the licences at the start; deriving `hd` from a bare
`RaiseSSeq s [c, d] z` is not possible, since a `RaiseSSeq` step only needs the
*weak* `nextUp ∧ pileOfTop` and not the `CanRaise` shape.) -/
theorem raiseSSeq_front_two {s : State} {c d : Card} (hs : s.WF)
    (hc : CanRaiseS s c) (hd : CanRaiseS s d)
    (hdc : d ≠ c) (hdt : d ≠ c.twin) :
    ∃ z', RaiseSSeq s [d, c] z' := by
  obtain ⟨s₂, hs₂, s₃, hs₃⟩ := swap_c_first hs hc hd hdc hdt
  obtain ⟨z₀, hp, hstep⟩ := hs₂
  obtain ⟨z₁, hp₁, hstep₁⟩ := hs₃
  exact ⟨s₃, RaiseSSeq.cons (RaiseSSeq.cons (RaiseSSeq.nil s) hp hstep) hp₁ hstep₁⟩

/-! ## §9. The exact residual for the general twin-free statement -/

/-- Splitting a word at its first occurrence of `c`. -/
theorem exists_append_cons_of_mem : ∀ {l : List Card} {c : Card}, c ∈ l →
    ∃ A B, l = A ++ c :: B ∧ c ∉ A := by
  intro l
  induction l with
  | nil => intro c hc; exact absurd hc List.not_mem_nil
  | cons x t ih =>
      intro c hc
      by_cases hx : x = c
      · subst hx
        exact ⟨[], t, rfl, List.not_mem_nil⟩
      · have hmem : c ∈ t := by
          rcases List.mem_cons.mp hc with h | h
          · exact absurd h.symm hx
          · exact h
        obtain ⟨A, B, hAB, hA⟩ := ih hmem
        refine ⟨x :: A, B, by rw [hAB, List.cons_append], ?_⟩
        intro hmem2
        rcases List.mem_cons.mp hmem2 with h | h
        · exact hx h.symm
        · exact hA h

/-- `erase` removes the split card. -/
theorem erase_append_cons_of_not_mem : ∀ {A B : List Card} {c : Card}, c ∉ A →
    (A ++ c :: B).erase c = A ++ B := by
  intro A
  induction A with
  | nil =>
      intro B c _
      exact List.erase_cons_head c B
  | cons x t ih =>
      intro B c hc
      have hx : x ≠ c := fun h => hc (by rw [h]; exact List.mem_cons_self ..)
      show (x :: (t ++ c :: B)).erase c = x :: (t ++ B)
      rw [List.erase_cons_tail (by simp [hx])]
      rw [ih (fun h => hc (List.mem_cons_of_mem _ h))]

/-- **REDUCTION**: the corrected statement, with the twin excluded, follows from
the single *block-replay* obligation — after `c` is raised, the block that
`c`'s raise used to be followed by (chronologically) can still be played.  This
is the exact residual: the probe state above shows that the twin must be
excluded, and the block replay is where the state-mismatch difficulty sits
(the block starts from a *different* state than in the original play). -/
theorem raiseS_reorder_front_of_block {s : State} {c : Card} {ws : List Card} {z : State}
    (hs : s.WF) (hc : CanRaiseS s c) (h : RaiseSSeq s ws z)
    (hmem : c ∈ ws) (ht : c.twin ∉ ws)
    (hblock : ∀ (A B : List Card) (u : State), ws = A ++ c :: B → c ∉ A →
      RaiseStepS s u c → ∃ v, RaiseSSeq u (A ++ B) v) :
    ∃ z', RaiseSSeq s (ws.erase c ++ [c]) z' := by
  obtain ⟨A, B, hAB, hA⟩ := exists_append_cons_of_mem (l := ws) hmem
  have herase : ws.erase c = A ++ B := by
    rw [hAB]
    exact erase_append_cons_of_not_mem hA
  obtain ⟨u, hstep⟩ := raiseStepS_of_canRaiseS hc
  obtain ⟨v, hv⟩ := hblock A B u hAB hA hstep
  obtain ⟨z₀, hp, hstep'⟩ := hstep
  have h₁ : RaiseSSeq s [c] u := RaiseSSeq.cons (RaiseSSeq.nil s) hp hstep'
  exact ⟨v, by rw [herase]; exact raiseSSeq_append h₁ hv⟩

end OneColourClosure

#print axioms OneColourClosure.probeState_WF
#print axioms OneColourClosure.probe_canRaiseS_KH
#print axioms OneColourClosure.probe_raiseSeq
#print axioms OneColourClosure.no_step_KD_after_KH
#print axioms OneColourClosure.probe_not_raiseSeq_front
#print axioms OneColourClosure.raiseSReorderFront_false
#print axioms OneColourClosure.raiseStepS_of_canRaiseS
#print axioms OneColourClosure.raiseSSeq_append
#print axioms OneColourClosure.raiseSSeq_wf
#print axioms OneColourClosure.canRaiseS_persist_fwd
#print axioms OneColourClosure.raiseSSeq_defer
#print axioms OneColourClosure.swap_c_first
#print axioms OneColourClosure.swap_d_first
#print axioms OneColourClosure.raiseSSeq_front_two
#print axioms OneColourClosure.erase_append_cons_of_not_mem
#print axioms OneColourClosure.raiseS_reorder_front_of_block

