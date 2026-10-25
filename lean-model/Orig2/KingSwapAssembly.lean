import Orig2.KingSwapStrict
import Orig2.KingTrace
import Orig2.KingOrbitFull

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Temp/KingSwapAssembly — the two king arms of the transfer

This additive card assembles the king arms around the strict anchor-swap
row of `Orig2.KingSwapStrict`:

* the anchor-permutation transfer of the strict twin letter;
* the orbit lift of `sameOrbitSetoid` and `SwappableIn`;
* the transfer of `SwappableIn` along a `KingShuffle`;
* the vacancy arm (`SameOrbitVacant s → SwappableIn s x`) and the
  no-vacancy arm (`¬ SameOrbitVacant s → ¬ SwappableIn s x`).

House compliance: new file only; zero `sorry`, zero `Classical.choice`.
-/

open State

/-! ## §1. The anchor-permutation transfer of the strict letter -/

/-- The strict twin-swap letter is natural under anchor relabeling.  The
`WF` gates are needed for the `seatOf` read: `seatOf_permute` locates the
moved anchors through the unique-occurrence invariant. -/
theorem twinPairSwapStrict_permute {s v : State} {x : Card} {σ : AnchorPerm}
    (hwfs : s.WF) (hwfv : v.WF) (h : twinPairSwapStrict s v x) :
    twinPairSwapStrict (s.permute σ) (v.permute σ) x := by
  obtain ⟨hseat, hseatt, hother, hbf, hff, hstock, hwaste, hcut⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [State.seatOf_permute (σ := σ) (st := v) hwfv x,
      State.seatOf_permute (σ := σ) (st := s) hwfs x.twin, hseat]
  · rw [State.seatOf_permute (σ := σ) (st := v) hwfv x.twin,
      State.seatOf_permute (σ := σ) (st := s) hwfs x, hseatt]
  · intro y hyx hyt
    rw [State.seatOf_permute (σ := σ) (st := v) hwfv y,
      State.seatOf_permute (σ := σ) (st := s) hwfs y, hother y hyx hyt]
  · constructor
    · intro a
      show (s.piles (σ.invFun a)).hidden = (v.piles (σ.invFun a)).hidden
      exact hbf.1 (σ.invFun a)
    · rw [State.permute_drawStep, State.permute_drawStep, hbf.2]
  · intro su
    rw [State.permute_found, State.permute_found, hff su]
  · rw [State.permute_stock, State.permute_stock, hstock]
  · rw [State.permute_waste, State.permute_waste, hwaste]
  · simp [cutOf, State.permute_stock, hstock]

#print axioms twinPairSwapStrict_permute

/-! ## §2. The orbit and `SwappableIn` lifts -/

/-- `sameOrbitSetoid` is anchor-equivariant.  The `WF` gate is necessary:
the witness shuffle transport (`ShufflePlayW_permute`) is WF-gated on both
directions, and the reverse direction's WF is recovered from `s.WF`. -/
theorem ksa_sameOrbit_permute {s v : State} {σ : AnchorPerm}
    (hwf : s.WF) (h : sameOrbitSetoid.r s v) :
    sameOrbitSetoid.r (s.permute σ) (v.permute σ) := by
  obtain ⟨ρ, hρ, τ, hτ⟩ := h
  have hvf : v.WF := run_wf hwf
    (Walk_run (P := fun st m => reversibleAtW st m) (st := s) (W := v) hτ)
  exact ⟨ρ.map (Move.permute σ), ShufflePlayW_permute hρ hvf,
    τ.map (Move.permute σ), ShufflePlayW_permute hτ hwf⟩

#print axioms ksa_sameOrbit_permute

/-- `SwappableIn` is invariant under anchor relabeling. -/
theorem swappableIn_permute {s : State} {x : Card} {σ : AnchorPerm}
    (hwf : s.WF) (h : SwappableIn s x) :
    SwappableIn (s.permute σ) x := by
  obtain ⟨v, hstrict, horb⟩ := h
  have hvf : v.WF := by
    obtain ⟨ρ, hρ, τ, hτ⟩ := horb
    exact run_wf hwf
      (Walk_run (P := fun st m => reversibleAtW st m) (st := s) (W := v) hτ)
  exact ⟨v.permute σ, twinPairSwapStrict_permute hwf hvf hstrict,
    ksa_sameOrbit_permute hwf horb⟩

#print axioms swappableIn_permute

/-- `SwappableIn` transports forward along a `KingShuffle`.  The shuffle is
an anchor relabeling (`KingShuffle.is_permute_vk`), so the relabeling lift
applies. -/
theorem swappableIn_of_kingShuffle {u v : State} {x : Card}
    (hwf : u.WF) (h : KingShuffle u v) (hswap : SwappableIn u x) :
    SwappableIn v x := by
  obtain ⟨π, hv, -, -⟩ := KingShuffle.is_permute_vk h hwf
  rw [hv]
  exact swappableIn_permute hwf hswap

#print axioms swappableIn_of_kingShuffle

/-! ## §3. The anchor-permutation form of the bare king swap -/

/-- Any anchor permutation that swaps the two bare king anchors, fixes every
other bottomed-king anchor, and fixes every non-VK anchor realizes the strict
twin swap.  This is the form produced by the king-assignment iteration, which
may additionally permute vacant anchors (those carry no cards, so the strict
letter is blind to them). -/
theorem twinPairSwapStrict_permute_of_anchorSwap
    {u : State} {x : Card} {a a' : Anchor} (σ : AnchorPerm)
    (hwf : u.WF) (hking : x.rank = Rank.king)
    (hx : seatOf u x = some (Sum.inl a))
    (hxt : seatOf u x.twin = some (Sum.inl a'))
    (hne : a ≠ a')
    (hbareA : (u.piles a).faceUp = [x] ∧ (u.piles a).hidden = [])
    (hbareB : (u.piles a').faceUp = [x.twin] ∧ (u.piles a').hidden = [])
    (hσa : σ.toFun a = a') (hσa' : σ.toFun a' = a)
    (hσKB : ∀ b, KingBottom u b → b ≠ a → b ≠ a' → σ.toFun b = b)
    (hσfix : ∀ j, ¬ VKSet u j → σ.toFun j = j) :
    twinPairSwapStrict u (u.permute σ) x := by
  have hkingt : x.twin.rank = Rank.king := by
    simpa [Card.twin] using hking
  have hKB_a : KingBottom u a := ⟨x, hx, hking, hbareA.2⟩
  have hKB_a' : KingBottom u a' := ⟨x.twin, hxt, hkingt, hbareB.2⟩
  have hσK : ∀ b, KingBottom u b → KingBottom u (σ.toFun b) := by
    intro b hb
    by_cases hba : b = a
    · rw [hba, hσa]; exact hKB_a'
    · by_cases hba' : b = a'
      · rw [hba', hσa']; exact hKB_a
      · rw [hσKB b hb hba hba']; exact hb
  have hσ_inj : Function.Injective σ.toFun := by
    intro p q hpq
    have h := congrArg σ.invFun hpq
    rwa [σ.left_inv p, σ.left_inv q] at h
  have hnotKB_of_vacant : ∀ j, VacantSpot u j → ¬ KingBottom u j := by
    intro j hvacj hkb
    obtain ⟨c, hse, -, -⟩ := hkb
    have hmem : c ∈ (u.piles j).faceUp :=
      pileHolding_mem (tfc_seatOf_of_inl hse).1
    have hface : (u.piles j).faceUp = [] := ((Pile.isEmpty_eq (u.piles j)).mp hvacj).2
    rw [hface] at hmem
    exact absurd hmem (by simp)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [State.seatOf_permute (σ := σ) (st := u) hwf x, hx]
    simp [Base.permute, hσa, hxt]
  · rw [State.seatOf_permute (σ := σ) (st := u) hwf x.twin, hxt]
    simp [Base.permute, hσa', hx]
  · intro y hyx hyt
    rw [State.seatOf_permute (σ := σ) (st := u) hwf y]
    cases hse : seatOf u y with
    | none => rfl
    | some b =>
        cases b with
        | inr z => simp [Base.permute]
        | inl c =>
            have hσc : σ.toFun c = c := by
              by_cases hkbB : kingBottomB u c = true
              · have hkb : KingBottom u c := kingBottomB_eq_true.mp hkbB
                have hca : c ≠ a := by
                  intro h
                  exact hyx (king_seat_injective hse (by rw [h]; exact hx))
                have hca' : c ≠ a' := by
                  intro h
                  exact hyt (king_seat_injective hse (by rw [h]; exact hxt))
                exact hσKB c hkb hca hca'
              · have hnotKB : ¬ KingBottom u c :=
                  fun h => hkbB (kingBottomB_eq_true.mpr h)
                have hnotvac : ¬ VacantSpot u c := by
                  intro hemp
                  have hmem : y ∈ (u.piles c).faceUp :=
                    pileHolding_mem (tfc_seatOf_of_inl hse).1
                  have hface : (u.piles c).faceUp = [] :=
                    ((Pile.isEmpty_eq (u.piles c)).mp hemp).2
                  rw [hface] at hmem
                  exact absurd hmem (by simp)
                exact hσfix c (fun hv => hv.elim hnotvac hnotKB)
            simp [Base.permute, hσc]
  · constructor
    · intro j
      show (u.piles j).hidden = (u.piles (σ.invFun j)).hidden
      by_cases hvacj : VacantSpot u j
      · have hiVac : VacantSpot u (σ.invFun j) := by
          by_cases hkbiB : kingBottomB u (σ.invFun j) = true
          · exfalso
            have hkbj : KingBottom u j := by
              have h := hσK (σ.invFun j) (kingBottomB_eq_true.mp hkbiB)
              rwa [σ.right_inv j] at h
            exact hnotKB_of_vacant j hvacj hkbj
          · have hkbi : ¬ KingBottom u (σ.invFun j) :=
              fun h => hkbiB (kingBottomB_eq_true.mpr h)
            by_cases hvkiB : vkSetB u (σ.invFun j) = true
            · have hvki : VKSet u (σ.invFun j) := vkSetB_eq_true.mp hvkiB
              exact hvki.resolve_right hkbi
            · exfalso
              have hvki : ¬ VKSet u (σ.invFun j) :=
                fun h => hvkiB (vkSetB_eq_true.mpr h)
              have hfixi : σ.toFun (σ.invFun j) = σ.invFun j :=
                hσfix (σ.invFun j) hvki
              rw [σ.right_inv j] at hfixi
              exact hvki (hfixi ▸ (Or.inl hvacj : VKSet u j))
        rw [((Pile.isEmpty_eq (u.piles j)).mp hvacj).1,
          ((Pile.isEmpty_eq (u.piles (σ.invFun j))).mp hiVac).1]
      · by_cases hkbjB : kingBottomB u j = true
        · have hkbj : KingBottom u j := kingBottomB_eq_true.mp hkbjB
          let b0 : Anchor := if j = a then a' else if j = a' then a else j
          have hb0_KB : KingBottom u b0 := by
            by_cases hja : j = a
            · have hb0 : b0 = a' := by
                show (if j = a then a' else if j = a' then a else j) = a'
                rw [ite_eq_left hja]
              rw [hb0]; exact hKB_a'
            · by_cases hja' : j = a'
              · have hb0 : b0 = a := by
                  show (if j = a then a' else if j = a' then a else j) = a
                  rw [ite_eq_right hja, ite_eq_left hja']
                rw [hb0]; exact hKB_a
              · have hb0 : b0 = j := by
                  show (if j = a then a' else if j = a' then a else j) = j
                  rw [ite_eq_right hja, ite_eq_right hja']
                rw [hb0]; exact hkbj
          have hσb0 : σ.toFun b0 = j := by
            by_cases hja : j = a
            · have hb0 : b0 = a' := by
                show (if j = a then a' else if j = a' then a else j) = a'
                rw [ite_eq_left hja]
              rw [hb0, hσa', hja]
            · by_cases hja' : j = a'
              · have hb0 : b0 = a := by
                  show (if j = a then a' else if j = a' then a else j) = a
                  rw [ite_eq_right hja, ite_eq_left hja']
                rw [hb0, hσa, hja']
              · have hb0 : b0 = j := by
                  show (if j = a then a' else if j = a' then a else j) = j
                  rw [ite_eq_right hja, ite_eq_right hja']
                rw [hb0, hσKB j hkbj hja hja']
          have hi : σ.invFun j = b0 := by
            have h := congrArg σ.invFun hσb0
            rw [σ.left_inv b0] at h
            exact h.symm
          rw [hi]
          obtain ⟨-, -, -, hhid0⟩ := hb0_KB
          obtain ⟨-, -, -, hhidj⟩ := hkbj
          rw [hhidj, hhid0]
        · have hkbj : ¬ KingBottom u j :=
            fun h => hkbjB (kingBottomB_eq_true.mpr h)
          have hvkj : ¬ VKSet u j := fun hv => hv.elim hvacj hkbj
          have hfixj : σ.toFun j = j := hσfix j hvkj
          have hi : σ.invFun j = j := by
            have h := congrArg σ.invFun hfixj
            rw [σ.left_inv j] at h
            exact h.symm
          rw [hi]
    · rfl
  · intro su
    rfl
  · rfl
  · rfl
  · rfl

#print axioms twinPairSwapStrict_permute_of_anchorSwap

/-! ## §4. The swap injection on the bottomed kings -/

/-- The anchor assignment realizing the king pair swap: `x` goes to the
twin's anchor, `x.twin` to `x`'s anchor, and every other card keeps its
bottom anchor (the default is irrelevant off the bottomed kings). -/
private def kingSwapAnchor (s : State) (x : Card) (a a' : Anchor) : Card → Anchor :=
  fun c => if c = x then a' else if c = x.twin then a else anchorOf s c

private theorem kingSwapAnchor_self (s : State) (x : Card) (a a' : Anchor) :
    kingSwapAnchor s x a a' x = a' := by
  simp [kingSwapAnchor]

private theorem kingSwapAnchor_twin (s : State) (x : Card) (a a' : Anchor) :
    kingSwapAnchor s x a a' x.twin = a := by
  simp [kingSwapAnchor, card_twin_ne x]

private theorem kingSwapAnchor_other {s : State} {x c : Card} {a a' : Anchor}
    (hcx : c ≠ x) (hct : c ≠ x.twin) :
    kingSwapAnchor s x a a' c = anchorOf s c := by
  simp [kingSwapAnchor, hcx, hct]

/-- The swap assignment is a `KingInjection` at a state where both cards are
bare bottomed kings. -/
private theorem kingSwapAnchor_kingInjection
    {s : State} {x : Card} {a a' : Anchor}
    (hking : x.rank = Rank.king)
    (hx : seatOf s x = some (Sum.inl a))
    (hxt : seatOf s x.twin = some (Sum.inl a'))
    (hne : a ≠ a')
    (hhidA : (s.piles a).hidden = [])
    (hhidB : (s.piles a').hidden = []) :
    KingInjection s (kingSwapAnchor s x a a') := by
  have hkingt : x.twin.rank = Rank.king := by
    simpa [Card.twin] using hking
  constructor
  · intro c hc
    by_cases hcx : c = x
    · subst c
      rw [kingSwapAnchor_self]
      exact Or.inr ⟨x.twin, hxt, hkingt, hhidB⟩
    · by_cases hct : c = x.twin
      · subst c
        rw [kingSwapAnchor_twin]
        exact Or.inr ⟨x, hx, hking, hhidA⟩
      · rw [kingSwapAnchor_other hcx hct]
        obtain ⟨b, hkb, hse⟩ := hc
        have hb : anchorOf s c = b := by simp [anchorOf, hse]
        rw [hb]
        exact Or.inr hkb
  · intro c c' hc hc' heq
    by_cases hcx : c = x
    · subst c
      by_cases hc'x : c' = x
      · subst c'; rfl
      · by_cases hc't : c' = x.twin
        · subst c'
          rw [kingSwapAnchor_self, kingSwapAnchor_twin] at heq
          exact absurd heq.symm hne
        · rw [kingSwapAnchor_self, kingSwapAnchor_other hc'x hc't] at heq
          obtain ⟨b, hkb, hse⟩ := hc'
          have hb : anchorOf s c' = b := by simp [anchorOf, hse]
          rw [hb] at heq
          have hct_seat : seatOf s x.twin = some (Sum.inl b) := by
            rw [← heq]; exact hxt
          exact absurd (king_seat_injective hse hct_seat) hc't
    · by_cases hct : c = x.twin
      · subst c
        by_cases hc'x : c' = x
        · subst c'
          rw [kingSwapAnchor_twin, kingSwapAnchor_self] at heq
          exact absurd heq hne
        · by_cases hc't : c' = x.twin
          · subst c'; rfl
          · rw [kingSwapAnchor_twin, kingSwapAnchor_other hc'x hc't] at heq
            obtain ⟨b, hkb, hse⟩ := hc'
            have hb : anchorOf s c' = b := by simp [anchorOf, hse]
            rw [hb] at heq
            have hc_seat : seatOf s x = some (Sum.inl b) := by
              rw [← heq]; exact hx
            exact absurd (king_seat_injective hse hc_seat) hc'x
      · by_cases hc'x : c' = x
        · subst c'
          rw [kingSwapAnchor_other hcx hct, kingSwapAnchor_self] at heq
          obtain ⟨b, hkb, hse⟩ := hc
          have hb : anchorOf s c = b := by simp [anchorOf, hse]
          rw [hb] at heq
          have hct_seat : seatOf s x.twin = some (Sum.inl b) := by
            rw [heq]; exact hxt
          exact absurd (king_seat_injective hse hct_seat) hct
        · by_cases hc't : c' = x.twin
          · subst c'
            rw [kingSwapAnchor_other hcx hct, kingSwapAnchor_twin] at heq
            obtain ⟨b, hkb, hse⟩ := hc
            have hb : anchorOf s c = b := by simp [anchorOf, hse]
            rw [hb] at heq
            have hc_seat : seatOf s x = some (Sum.inl b) := by
              rw [heq]; exact hx
            exact absurd (king_seat_injective hse hc_seat) hcx
          · rw [kingSwapAnchor_other hcx hct,
              kingSwapAnchor_other hc'x hc't] at heq
            obtain ⟨b, hkb, hse⟩ := hc
            obtain ⟨b', hkb', hse'⟩ := hc'
            have hb : anchorOf s c = b := by simp [anchorOf, hse]
            have hb' : anchorOf s c' = b' := by simp [anchorOf, hse']
            rw [hb, hb'] at heq
            exact king_seat_injective hse (by rw [heq]; exact hse')

#print axioms kingSwapAnchor_kingInjection

/-! ## §5. The exact-permutation realization in a vacant class -/

/-- **The vacancy-arm strengthening.**  In a class with a vacancy, the king
pair swap is realized by a class-mate of the exact shape `s.permute π`, where
`π` swaps the two king anchors, fixes every other bottomed-king anchor and
every non-VK anchor.  This is exactly the permutation the strict letter
consumes; `π` may additionally permute vacant anchors, which carry no cards.

The proof splits on whether `s` itself carries a vacancy.  If it does, the
assignment theorem's realization is a `KingShuffle` and hence an anchor
relabeling.  If it does not, the first-vacancy split raises a bare king, the
swap permutation is realized at the unique-vacancy state, and the reverse
path is relabeled back to `s` (`realize_perm` + `sameOrbit_permute`). -/
theorem exists_permute_of_kingPair_vacant
    {s : State} {x : Card} {a a' : Anchor}
    (hwf : s.WF) (hking : x.rank = Rank.king)
    (hx : seatOf s x = some (Sum.inl a))
    (hxt : seatOf s x.twin = some (Sum.inl a'))
    (hne : a ≠ a')
    (hbareA : (s.piles a).faceUp = [x] ∧ (s.piles a).hidden = [])
    (hbareB : (s.piles a').faceUp = [x.twin] ∧ (s.piles a').hidden = [])
    (hvac : SameOrbitVacant s) :
    ∃ π : AnchorPerm,
      π.toFun a = a' ∧ π.toFun a' = a ∧
      (∀ b, KingBottom s b → b ≠ a → b ≠ a' → π.toFun b = b) ∧
      (∀ j, ¬ VKSet s j → π.toFun j = j) ∧
      sameOrbitSetoid.r s (s.permute π) := by
  have hkingt : x.twin.rank = Rank.king := by
    simpa [Card.twin] using hking
  have hKB_a : KingBottom s a := ⟨x, hx, hking, hbareA.2⟩
  have hKB_a' : KingBottom s a' := ⟨x.twin, hxt, hkingt, hbareB.2⟩
  let τ := kingSwapAnchor s x a a'
  have hτ : KingInjection s τ :=
    kingSwapAnchor_kingInjection hking hx hxt hne hbareA.2 hbareB.2
  have hτx : τ x = a' := kingSwapAnchor_self s x a a'
  have hτt : τ x.twin = a := kingSwapAnchor_twin s x a a'
  have hτo : ∀ c, c ≠ x → c ≠ x.twin → τ c = anchorOf s c :=
    fun c hcx hct => kingSwapAnchor_other hcx hct
  by_cases hb : hasVacancyB s = true
  · -- the reference state itself carries a vacancy
    have hHvac : HasVacancy s := hasVacancyB_eq_true.mp hb
    have hcs : ∀ c, c ∈ kingsOf s ↔ KingBottomCard s c :=
      fun c => mem_kingsOf hwf
    obtain ⟨w', hks, hseat⟩ :=
      king_assignment_reachable hwf hHvac τ (kingsOf s)
        (fun c hc => (hcs c).mp hc)
        (fun c hc => hτ.1 c ((hcs c).mp hc))
        (kingsOf_nodup s)
        (fun c hc c' hc' heq =>
          hτ.2 c c' ((hcs c).mp hc) ((hcs c').mp hc') heq)
    obtain ⟨π, hw', -, hπfix⟩ := KingShuffle.is_permute_vk hks hwf
    have hx_card : KingBottomCard s x := ⟨a, hKB_a, hx⟩
    have hxt_card : KingBottomCard s x.twin := ⟨a', hKB_a', hxt⟩
    have hx_mem : x ∈ kingsOf s := (hcs x).mpr hx_card
    have hxt_mem : x.twin ∈ kingsOf s := (hcs x.twin).mpr hxt_card
    have hπa : π.toFun a = a' := by
      have h1 : seatOf (s.permute π) x = some (Sum.inl (π.toFun a)) := by
        rw [State.seatOf_permute (σ := π) (st := s) hwf x, hx]
        rfl
      have h2 : seatOf (s.permute π) x = some (Sum.inl a') := by
        rw [← hw', hseat x hx_mem, hτx]
      exact Sum.inl.inj (Option.some.inj (h1.symm.trans h2))
    have hπa' : π.toFun a' = a := by
      have h1 : seatOf (s.permute π) x.twin = some (Sum.inl (π.toFun a')) := by
        rw [State.seatOf_permute (σ := π) (st := s) hwf x.twin, hxt]
        rfl
      have h2 : seatOf (s.permute π) x.twin = some (Sum.inl a) := by
        rw [← hw', hseat x.twin hxt_mem, hτt]
      exact Sum.inl.inj (Option.some.inj (h1.symm.trans h2))
    have hπKB : ∀ b, KingBottom s b → b ≠ a → b ≠ a' → π.toFun b = b := by
      intro b hkb hba hba'
      obtain ⟨c, hse, hkc, hhid⟩ := hkb
      have hc_card : KingBottomCard s c := ⟨b, ⟨c, hse, hkc, hhid⟩, hse⟩
      have hc_mem : c ∈ kingsOf s := (hcs c).mpr hc_card
      have hcx : c ≠ x := by
        intro hcx
        apply hba
        rw [hcx] at hse
        exact Sum.inl.inj (Option.some.inj (hse.symm.trans hx))
      have hct : c ≠ x.twin := by
        intro hct
        apply hba'
        rw [hct] at hse
        exact Sum.inl.inj (Option.some.inj (hse.symm.trans hxt))
      have hτc : τ c = anchorOf s c := hτo c hcx hct
      have hao : anchorOf s c = b := by simp [anchorOf, hse]
      have h1 : seatOf (s.permute π) c = some (Sum.inl (π.toFun b)) := by
        rw [State.seatOf_permute (σ := π) (st := s) hwf c, hse]
        rfl
      have h2 : seatOf (s.permute π) c = some (Sum.inl b) := by
        rw [← hw', hseat c hc_mem, hτc, hao]
      exact Sum.inl.inj (Option.some.inj (h1.symm.trans h2))
    have hbc : BareCargoEquiv s (s.permute π) := by
      rw [← hw']
      exact king_shuffle_closure hwf hks
    exact ⟨π, hπa, hπa', hπKB, hπfix, bareCargo_sameOrbit hbc⟩
  · -- no vacancy at the reference state: split at the first vacancy
    have hno : NoVacancy s :=
      (noVacancy_iff_not_hasVacancy s).mpr
        (fun h => hb (hasVacancyB_eq_true.mpr h))
    obtain ⟨u, hsu, hvacu⟩ := hvac
    obtain ⟨ρu, hu_s, σs, hs_u⟩ := hsu
    obtain ⟨pre, x0, e0, s0, s1, suffix, hpre, hstep, hp, hno0, hvac_s1,
      hrev_raise, hsuffix⟩ := first_vacancy_split hwf hs_u hno hvacu
    have hwfs0 : s0.WF := NVWalk_wf hpre hwf
    have hwfs1 : s1.WF := step_wf hwfs0 hstep
    have hraise_sh : ShufflePlayW s0 [Move.tabToFound x0] s1 :=
      Walk.cons hrev_raise hstep (Walk.nil s1)
    have hfwd : ShufflePlayW s (pre ++ [Move.tabToFound x0]) s1 :=
      ShufflePlayW_append hpre.to_shuffle hraise_sh
    have hback : ShufflePlayW s1 (suffix ++ ρu) s :=
      ShufflePlayW_append hsuffix hu_s
    have hclass_s1 : sameOrbitSetoid.r s s1 :=
      ⟨suffix ++ ρu, hback, pre ++ [Move.tabToFound x0], hfwd⟩
    have huniq_s1 : ∀ a' b, (s1.piles a').isEmpty = true →
        (s1.piles b).isEmpty = true → a' = b := by
      obtain ⟨hn, e, hp0, hvals⟩ := step_tabToFound_inv hstep
      have he : e = e0 := by
        rw [hp] at hp0
        exact (Option.some.inj hp0).symm
      rw [he] at hvals
      intro a' b ha' hb'
      by_cases hba : b = e0
      · rw [hba] at hb'
        by_cases ha'e : a' = e0
        · exact ha'e.trans hba.symm
        · exfalso
          have hs1a' : s1.piles a' = s0.piles a' := by
            rw [hvals]
            dsimp only
            rw [ite_eq_right ha'e]
          rw [hs1a'] at ha'
          exact hno0 a' ha'
      · exfalso
        have hs1b : s1.piles b = s0.piles b := by
          rw [hvals]
          dsimp only
          rw [ite_eq_right hba]
        rw [hs1b] at hb'
        exact hno0 b hb'
    let σ : AnchorPerm := AnchorPerm.swap a a'
    have hσa : σ.toFun a = a' := AnchorPerm.swap_apply_a a a'
    have hσa' : σ.toFun a' = a := AnchorPerm.swap_apply_e a a'
    have hσKB : ∀ b, KingBottom s b → b ≠ a → b ≠ a' → σ.toFun b = b :=
      fun _ _ hba hba' => AnchorPerm.swap_apply_of_ne hba hba'
    have hσfix : ∀ j, ¬ VKSet s j → σ.toFun j = j := by
      intro j hj
      exact AnchorPerm.swap_apply_of_ne
        (fun h => hj (by rw [h]; exact Or.inr hKB_a))
        (fun h => hj (by rw [h]; exact Or.inr hKB_a'))
    have hσVK : ∀ j, VKSet s j ↔ VKSet s (σ.toFun j) := by
      intro j
      exact (vk_swap_iff (P := fun j => VKSet s j)
        (Or.inr hKB_a) (Or.inr hKB_a') j).symm
    have hvk : ∀ j, VKSet s j ↔ VKSet s1 j :=
      vk_sameOrbit_invariant hwf hclass_s1
    have hσVK1 : ∀ j, VKSet s1 j ↔ VKSet s1 (σ.toFun j) := by
      intro j
      exact (hvk j).symm.trans ((hσVK j).trans (hvk (σ.toFun j)))
    have hσfix1 : ∀ j, ¬ VKSet s1 j → σ.toFun j = j := by
      intro j hnot
      exact hσfix j (fun hj => hnot ((hvk j).mp hj))
    obtain ⟨v_s, hks, hv_s⟩ :=
      KingShuffle.realize_perm hwfs1 ⟨e0, hvac_s1⟩ huniq_s1 σ hσVK1 hσfix1
    have h_s1_vs : sameOrbitSetoid.r s1 v_s :=
      bareCargo_sameOrbit (king_shuffle_closure hwfs1 hks)
    have h_vs_perm : sameOrbitSetoid.r v_s (s.permute σ) := by
      have h3 : sameOrbitSetoid.r (s1.permute σ) (s.permute σ) :=
        sameOrbitSetoid.iseqv.symm (sameOrbit_permute (σ := σ) hclass_s1 hwf)
      rwa [← hv_s] at h3
    have horb : sameOrbitSetoid.r s (s.permute σ) :=
      sameOrbitSetoid.iseqv.trans hclass_s1
        (sameOrbitSetoid.iseqv.trans h_s1_vs h_vs_perm)
    exact ⟨σ, hσa, hσa', hσKB, hσfix, horb⟩

#print axioms exists_permute_of_kingPair_vacant

/-- **The vacancy arm.**  A bare king pair at distinct anchors is strictly
swappable in any class that carries a vacancy. -/
theorem swappableIn_king_of_vacancy
    {s : State} {x : Card} {a a' : Anchor}
    (hwf : s.WF) (hking : x.rank = Rank.king)
    (hx : seatOf s x = some (Sum.inl a))
    (hxt : seatOf s x.twin = some (Sum.inl a'))
    (hne : a ≠ a')
    (hbareA : (s.piles a).faceUp = [x] ∧ (s.piles a).hidden = [])
    (hbareB : (s.piles a').faceUp = [x.twin] ∧ (s.piles a').hidden = [])
    (hvac : SameOrbitVacant s) :
    SwappableIn s x := by
  obtain ⟨π, hπa, hπa', hπKB, hπfix, horb⟩ :=
    exists_permute_of_kingPair_vacant hwf hking hx hxt hne hbareA hbareB hvac
  exact ⟨s.permute π,
    twinPairSwapStrict_permute_of_anchorSwap π hwf hking hx hxt hne hbareA hbareB
      hπa hπa' hπKB hπfix,
    horb⟩

#print axioms swappableIn_king_of_vacancy

/-- **The no-vacancy arm.**  In a vacancy-free class no bare king pair is
strictly swappable.  The proof feeds the actual king injection (swap the pair,
fix every other bottomed king) to `kingAssignmentFixed_of_not_vacant`: any
class-mate realizing that assignment must preserve `x`'s seat, contradicting
the strict swap clause.

The displayed statement of the task omits the bare/seat facts; without them
it is false (a pair already in the foundation satisfies the strict letter with
`v = s`).  The hypotheses below are the exact ones the fixed clause needs:
`x` and `x.twin` must bottom bare king piles (`hidden = []`), and their
anchors must differ.  The singleton face-up hypothesis is not needed here. -/
theorem not_swappableIn_king_of_not_vacant
    {s : State} {x : Card} {a a' : Anchor}
    (hwf : s.WF) (hking : x.rank = Rank.king)
    (hx : seatOf s x = some (Sum.inl a))
    (hxt : seatOf s x.twin = some (Sum.inl a'))
    (hne : a ≠ a')
    (hhidA : (s.piles a).hidden = [])
    (hhidB : (s.piles a').hidden = [])
    (hnv : ¬ SameOrbitVacant s) :
    ¬ SwappableIn s x := by
  intro hswap
  obtain ⟨v, hstrict, horb⟩ := hswap
  let τ := kingSwapAnchor s x a a'
  have hτ : KingInjection s τ :=
    kingSwapAnchor_kingInjection hking hx hxt hne hhidA hhidB
  have hτx : τ x = a' := kingSwapAnchor_self s x a a'
  have hτt : τ x.twin = a := kingSwapAnchor_twin s x a a'
  have hτo : ∀ c, c ≠ x → c ≠ x.twin → τ c = anchorOf s c :=
    fun c hcx hct => kingSwapAnchor_other hcx hct
  have hassign : ∀ c, KingBottomCard s c → seatOf v c = some (Sum.inl (τ c)) := by
    intro c hc
    by_cases hcx : c = x
    · subst c
      rw [hstrict.1, hxt, hτx]
    · by_cases hct : c = x.twin
      · subst c
        rw [hstrict.2.1, hx, hτt]
      · rw [hstrict.2.2.1 c hcx hct, hτo c hcx hct]
        obtain ⟨b, hkb, hse⟩ := hc
        simp [anchorOf, hse]
  have hx_card : KingBottomCard s x := ⟨a, ⟨x, hx, hking, hhidA⟩, hx⟩
  have hsame : seatOf v x = seatOf s x :=
    kingAssignmentFixed_of_not_vacant hwf hnv s (sameOrbitSetoid.iseqv.refl s)
      v horb τ hτ hassign x hx_card
  have h1 : seatOf v x = some (Sum.inl a') := hstrict.1.trans hxt
  have h2 : seatOf v x = some (Sum.inl a) := hsame.trans hx
  have hcontra : a' = a := Sum.inl.inj (Option.some.inj (h1.symm.trans h2))
  exact hne hcontra.symm

#print axioms not_swappableIn_king_of_not_vacant

/-! ## §5. The KingBottom-grade generalizations (fresh, 2026-10-25)

The owner''s completion of the king dichotomy: the bare hypotheses of
the section-3 rows are UNUSED by their proofs (the singleton face-up
clauses never appear - only the hidden = [] parts feed KingBottom and
the injection), so the same proofs realize the strict letter at the
KingBottom grade - runs on top of the kings are allowed.  With
not_swappableIn_king_of_not_vacant (already hidden-only), the king
dichotomy reads: a KingBottom king pair is strictly swappable iff
the class carries a vacancy. -/

/-- **The anchor-permutation form of the king swap, KingBottom grade**
(the run-topped generalization - the verbatim proof of the bare
original with the unused singleton hypotheses dropped). -/theorem twinPairSwapStrict_permute_of_anchorSwap'
    {u : State} {x : Card} {a a' : Anchor} (σ : AnchorPerm)
    (hwf : u.WF) (hking : x.rank = Rank.king)
    (hx : seatOf u x = some (Sum.inl a))
    (hxt : seatOf u x.twin = some (Sum.inl a'))
    (hne : a ≠ a')
    (hhidA : (u.piles a).hidden = [])
    (hhidB : (u.piles a').hidden = [])
    (hσa : σ.toFun a = a') (hσa' : σ.toFun a' = a)
    (hσKB : ∀ b, KingBottom u b → b ≠ a → b ≠ a' → σ.toFun b = b)
    (hσfix : ∀ j, ¬ VKSet u j → σ.toFun j = j) :
    twinPairSwapStrict u (u.permute σ) x := by
  have hkingt : x.twin.rank = Rank.king := by
    simpa [Card.twin] using hking
  have hKB_a : KingBottom u a := ⟨x, hx, hking, hhidA⟩
  have hKB_a' : KingBottom u a' := ⟨x.twin, hxt, hkingt, hhidB⟩
  have hσK : ∀ b, KingBottom u b → KingBottom u (σ.toFun b) := by
    intro b hb
    by_cases hba : b = a
    · rw [hba, hσa]; exact hKB_a'
    · by_cases hba' : b = a'
      · rw [hba', hσa']; exact hKB_a
      · rw [hσKB b hb hba hba']; exact hb
  have hσ_inj : Function.Injective σ.toFun := by
    intro p q hpq
    have h := congrArg σ.invFun hpq
    rwa [σ.left_inv p, σ.left_inv q] at h
  have hnotKB_of_vacant : ∀ j, VacantSpot u j → ¬ KingBottom u j := by
    intro j hvacj hkb
    obtain ⟨c, hse, -, -⟩ := hkb
    have hmem : c ∈ (u.piles j).faceUp :=
      pileHolding_mem (tfc_seatOf_of_inl hse).1
    have hface : (u.piles j).faceUp = [] := ((Pile.isEmpty_eq (u.piles j)).mp hvacj).2
    rw [hface] at hmem
    exact absurd hmem (by simp)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [State.seatOf_permute (σ := σ) (st := u) hwf x, hx]
    simp [Base.permute, hσa, hxt]
  · rw [State.seatOf_permute (σ := σ) (st := u) hwf x.twin, hxt]
    simp [Base.permute, hσa', hx]
  · intro y hyx hyt
    rw [State.seatOf_permute (σ := σ) (st := u) hwf y]
    cases hse : seatOf u y with
    | none => rfl
    | some b =>
        cases b with
        | inr z => simp [Base.permute]
        | inl c =>
            have hσc : σ.toFun c = c := by
              by_cases hkbB : kingBottomB u c = true
              · have hkb : KingBottom u c := kingBottomB_eq_true.mp hkbB
                have hca : c ≠ a := by
                  intro h
                  exact hyx (king_seat_injective hse (by rw [h]; exact hx))
                have hca' : c ≠ a' := by
                  intro h
                  exact hyt (king_seat_injective hse (by rw [h]; exact hxt))
                exact hσKB c hkb hca hca'
              · have hnotKB : ¬ KingBottom u c :=
                  fun h => hkbB (kingBottomB_eq_true.mpr h)
                have hnotvac : ¬ VacantSpot u c := by
                  intro hemp
                  have hmem : y ∈ (u.piles c).faceUp :=
                    pileHolding_mem (tfc_seatOf_of_inl hse).1
                  have hface : (u.piles c).faceUp = [] :=
                    ((Pile.isEmpty_eq (u.piles c)).mp hemp).2
                  rw [hface] at hmem
                  exact absurd hmem (by simp)
                exact hσfix c (fun hv => hv.elim hnotvac hnotKB)
            simp [Base.permute, hσc]
  · constructor
    · intro j
      show (u.piles j).hidden = (u.piles (σ.invFun j)).hidden
      by_cases hvacj : VacantSpot u j
      · have hiVac : VacantSpot u (σ.invFun j) := by
          by_cases hkbiB : kingBottomB u (σ.invFun j) = true
          · exfalso
            have hkbj : KingBottom u j := by
              have h := hσK (σ.invFun j) (kingBottomB_eq_true.mp hkbiB)
              rwa [σ.right_inv j] at h
            exact hnotKB_of_vacant j hvacj hkbj
          · have hkbi : ¬ KingBottom u (σ.invFun j) :=
              fun h => hkbiB (kingBottomB_eq_true.mpr h)
            by_cases hvkiB : vkSetB u (σ.invFun j) = true
            · have hvki : VKSet u (σ.invFun j) := vkSetB_eq_true.mp hvkiB
              exact hvki.resolve_right hkbi
            · exfalso
              have hvki : ¬ VKSet u (σ.invFun j) :=
                fun h => hvkiB (vkSetB_eq_true.mpr h)
              have hfixi : σ.toFun (σ.invFun j) = σ.invFun j :=
                hσfix (σ.invFun j) hvki
              rw [σ.right_inv j] at hfixi
              exact hvki (hfixi ▸ (Or.inl hvacj : VKSet u j))
        rw [((Pile.isEmpty_eq (u.piles j)).mp hvacj).1,
          ((Pile.isEmpty_eq (u.piles (σ.invFun j))).mp hiVac).1]
      · by_cases hkbjB : kingBottomB u j = true
        · have hkbj : KingBottom u j := kingBottomB_eq_true.mp hkbjB
          let b0 : Anchor := if j = a then a' else if j = a' then a else j
          have hb0_KB : KingBottom u b0 := by
            by_cases hja : j = a
            · have hb0 : b0 = a' := by
                show (if j = a then a' else if j = a' then a else j) = a'
                rw [ite_eq_left hja]
              rw [hb0]; exact hKB_a'
            · by_cases hja' : j = a'
              · have hb0 : b0 = a := by
                  show (if j = a then a' else if j = a' then a else j) = a
                  rw [ite_eq_right hja, ite_eq_left hja']
                rw [hb0]; exact hKB_a
              · have hb0 : b0 = j := by
                  show (if j = a then a' else if j = a' then a else j) = j
                  rw [ite_eq_right hja, ite_eq_right hja']
                rw [hb0]; exact hkbj
          have hσb0 : σ.toFun b0 = j := by
            by_cases hja : j = a
            · have hb0 : b0 = a' := by
                show (if j = a then a' else if j = a' then a else j) = a'
                rw [ite_eq_left hja]
              rw [hb0, hσa', hja]
            · by_cases hja' : j = a'
              · have hb0 : b0 = a := by
                  show (if j = a then a' else if j = a' then a else j) = a
                  rw [ite_eq_right hja, ite_eq_left hja']
                rw [hb0, hσa, hja']
              · have hb0 : b0 = j := by
                  show (if j = a then a' else if j = a' then a else j) = j
                  rw [ite_eq_right hja, ite_eq_right hja']
                rw [hb0, hσKB j hkbj hja hja']
          have hi : σ.invFun j = b0 := by
            have h := congrArg σ.invFun hσb0
            rw [σ.left_inv b0] at h
            exact h.symm
          rw [hi]
          obtain ⟨-, -, -, hhid0⟩ := hb0_KB
          obtain ⟨-, -, -, hhidj⟩ := hkbj
          rw [hhidj, hhid0]
        · have hkbj : ¬ KingBottom u j :=
            fun h => hkbjB (kingBottomB_eq_true.mpr h)
          have hvkj : ¬ VKSet u j := fun hv => hv.elim hvacj hkbj
          have hfixj : σ.toFun j = j := hσfix j hvkj
          have hi : σ.invFun j = j := by
            have h := congrArg σ.invFun hfixj
            rw [σ.left_inv j] at h
            exact h.symm
          rw [hi]
    · rfl
  · intro su
    rfl
  · rfl
  · rfl
  · rfl

#print axioms twinPairSwapStrict_permute_of_anchorSwap'
/-- **The king-pair vacancy arm, KingBottom grade** (the run-topped
generalization - the verbatim proof with the unused singleton
hypotheses dropped). -/theorem exists_permute_of_kingPair_vacant'
    {s : State} {x : Card} {a a' : Anchor}
    (hwf : s.WF) (hking : x.rank = Rank.king)
    (hx : seatOf s x = some (Sum.inl a))
    (hxt : seatOf s x.twin = some (Sum.inl a'))
    (hne : a ≠ a')
    (hhidA : (s.piles a).hidden = [])
    (hhidB : (s.piles a').hidden = [])
    (hvac : SameOrbitVacant s) :
    ∃ π : AnchorPerm,
      π.toFun a = a' ∧ π.toFun a' = a ∧
      (∀ b, KingBottom s b → b ≠ a → b ≠ a' → π.toFun b = b) ∧
      (∀ j, ¬ VKSet s j → π.toFun j = j) ∧
      sameOrbitSetoid.r s (s.permute π) := by
  have hkingt : x.twin.rank = Rank.king := by
    simpa [Card.twin] using hking
  have hKB_a : KingBottom s a := ⟨x, hx, hking, hhidA⟩
  have hKB_a' : KingBottom s a' := ⟨x.twin, hxt, hkingt, hhidB⟩
  let τ := kingSwapAnchor s x a a'
  have hτ : KingInjection s τ :=
    kingSwapAnchor_kingInjection hking hx hxt hne hhidA hhidB
  have hτx : τ x = a' := kingSwapAnchor_self s x a a'
  have hτt : τ x.twin = a := kingSwapAnchor_twin s x a a'
  have hτo : ∀ c, c ≠ x → c ≠ x.twin → τ c = anchorOf s c :=
    fun c hcx hct => kingSwapAnchor_other hcx hct
  by_cases hb : hasVacancyB s = true
  · -- the reference state itself carries a vacancy
    have hHvac : HasVacancy s := hasVacancyB_eq_true.mp hb
    have hcs : ∀ c, c ∈ kingsOf s ↔ KingBottomCard s c :=
      fun c => mem_kingsOf hwf
    obtain ⟨w', hks, hseat⟩ :=
      king_assignment_reachable hwf hHvac τ (kingsOf s)
        (fun c hc => (hcs c).mp hc)
        (fun c hc => hτ.1 c ((hcs c).mp hc))
        (kingsOf_nodup s)
        (fun c hc c' hc' heq =>
          hτ.2 c c' ((hcs c).mp hc) ((hcs c').mp hc') heq)
    obtain ⟨π, hw', -, hπfix⟩ := KingShuffle.is_permute_vk hks hwf
    have hx_card : KingBottomCard s x := ⟨a, hKB_a, hx⟩
    have hxt_card : KingBottomCard s x.twin := ⟨a', hKB_a', hxt⟩
    have hx_mem : x ∈ kingsOf s := (hcs x).mpr hx_card
    have hxt_mem : x.twin ∈ kingsOf s := (hcs x.twin).mpr hxt_card
    have hπa : π.toFun a = a' := by
      have h1 : seatOf (s.permute π) x = some (Sum.inl (π.toFun a)) := by
        rw [State.seatOf_permute (σ := π) (st := s) hwf x, hx]
        rfl
      have h2 : seatOf (s.permute π) x = some (Sum.inl a') := by
        rw [← hw', hseat x hx_mem, hτx]
      exact Sum.inl.inj (Option.some.inj (h1.symm.trans h2))
    have hπa' : π.toFun a' = a := by
      have h1 : seatOf (s.permute π) x.twin = some (Sum.inl (π.toFun a')) := by
        rw [State.seatOf_permute (σ := π) (st := s) hwf x.twin, hxt]
        rfl
      have h2 : seatOf (s.permute π) x.twin = some (Sum.inl a) := by
        rw [← hw', hseat x.twin hxt_mem, hτt]
      exact Sum.inl.inj (Option.some.inj (h1.symm.trans h2))
    have hπKB : ∀ b, KingBottom s b → b ≠ a → b ≠ a' → π.toFun b = b := by
      intro b hkb hba hba'
      obtain ⟨c, hse, hkc, hhid⟩ := hkb
      have hc_card : KingBottomCard s c := ⟨b, ⟨c, hse, hkc, hhid⟩, hse⟩
      have hc_mem : c ∈ kingsOf s := (hcs c).mpr hc_card
      have hcx : c ≠ x := by
        intro hcx
        apply hba
        rw [hcx] at hse
        exact Sum.inl.inj (Option.some.inj (hse.symm.trans hx))
      have hct : c ≠ x.twin := by
        intro hct
        apply hba'
        rw [hct] at hse
        exact Sum.inl.inj (Option.some.inj (hse.symm.trans hxt))
      have hτc : τ c = anchorOf s c := hτo c hcx hct
      have hao : anchorOf s c = b := by simp [anchorOf, hse]
      have h1 : seatOf (s.permute π) c = some (Sum.inl (π.toFun b)) := by
        rw [State.seatOf_permute (σ := π) (st := s) hwf c, hse]
        rfl
      have h2 : seatOf (s.permute π) c = some (Sum.inl b) := by
        rw [← hw', hseat c hc_mem, hτc, hao]
      exact Sum.inl.inj (Option.some.inj (h1.symm.trans h2))
    have hbc : BareCargoEquiv s (s.permute π) := by
      rw [← hw']
      exact king_shuffle_closure hwf hks
    exact ⟨π, hπa, hπa', hπKB, hπfix, bareCargo_sameOrbit hbc⟩
  · -- no vacancy at the reference state: split at the first vacancy
    have hno : NoVacancy s :=
      (noVacancy_iff_not_hasVacancy s).mpr
        (fun h => hb (hasVacancyB_eq_true.mpr h))
    obtain ⟨u, hsu, hvacu⟩ := hvac
    obtain ⟨ρu, hu_s, σs, hs_u⟩ := hsu
    obtain ⟨pre, x0, e0, s0, s1, suffix, hpre, hstep, hp, hno0, hvac_s1,
      hrev_raise, hsuffix⟩ := first_vacancy_split hwf hs_u hno hvacu
    have hwfs0 : s0.WF := NVWalk_wf hpre hwf
    have hwfs1 : s1.WF := step_wf hwfs0 hstep
    have hraise_sh : ShufflePlayW s0 [Move.tabToFound x0] s1 :=
      Walk.cons hrev_raise hstep (Walk.nil s1)
    have hfwd : ShufflePlayW s (pre ++ [Move.tabToFound x0]) s1 :=
      ShufflePlayW_append hpre.to_shuffle hraise_sh
    have hback : ShufflePlayW s1 (suffix ++ ρu) s :=
      ShufflePlayW_append hsuffix hu_s
    have hclass_s1 : sameOrbitSetoid.r s s1 :=
      ⟨suffix ++ ρu, hback, pre ++ [Move.tabToFound x0], hfwd⟩
    have huniq_s1 : ∀ a' b, (s1.piles a').isEmpty = true →
        (s1.piles b).isEmpty = true → a' = b := by
      obtain ⟨hn, e, hp0, hvals⟩ := step_tabToFound_inv hstep
      have he : e = e0 := by
        rw [hp] at hp0
        exact (Option.some.inj hp0).symm
      rw [he] at hvals
      intro a' b ha' hb'
      by_cases hba : b = e0
      · rw [hba] at hb'
        by_cases ha'e : a' = e0
        · exact ha'e.trans hba.symm
        · exfalso
          have hs1a' : s1.piles a' = s0.piles a' := by
            rw [hvals]
            dsimp only
            rw [ite_eq_right ha'e]
          rw [hs1a'] at ha'
          exact hno0 a' ha'
      · exfalso
        have hs1b : s1.piles b = s0.piles b := by
          rw [hvals]
          dsimp only
          rw [ite_eq_right hba]
        rw [hs1b] at hb'
        exact hno0 b hb'
    let σ : AnchorPerm := AnchorPerm.swap a a'
    have hσa : σ.toFun a = a' := AnchorPerm.swap_apply_a a a'
    have hσa' : σ.toFun a' = a := AnchorPerm.swap_apply_e a a'
    have hσKB : ∀ b, KingBottom s b → b ≠ a → b ≠ a' → σ.toFun b = b :=
      fun _ _ hba hba' => AnchorPerm.swap_apply_of_ne hba hba'
    have hσfix : ∀ j, ¬ VKSet s j → σ.toFun j = j := by
      intro j hj
      exact AnchorPerm.swap_apply_of_ne
        (fun h => hj (by rw [h]; exact Or.inr hKB_a))
        (fun h => hj (by rw [h]; exact Or.inr hKB_a'))
    have hσVK : ∀ j, VKSet s j ↔ VKSet s (σ.toFun j) := by
      intro j
      exact (vk_swap_iff (P := fun j => VKSet s j)
        (Or.inr hKB_a) (Or.inr hKB_a') j).symm
    have hvk : ∀ j, VKSet s j ↔ VKSet s1 j :=
      vk_sameOrbit_invariant hwf hclass_s1
    have hσVK1 : ∀ j, VKSet s1 j ↔ VKSet s1 (σ.toFun j) := by
      intro j
      exact (hvk j).symm.trans ((hσVK j).trans (hvk (σ.toFun j)))
    have hσfix1 : ∀ j, ¬ VKSet s1 j → σ.toFun j = j := by
      intro j hnot
      exact hσfix j (fun hj => hnot ((hvk j).mp hj))
    obtain ⟨v_s, hks, hv_s⟩ :=
      KingShuffle.realize_perm hwfs1 ⟨e0, hvac_s1⟩ huniq_s1 σ hσVK1 hσfix1
    have h_s1_vs : sameOrbitSetoid.r s1 v_s :=
      bareCargo_sameOrbit (king_shuffle_closure hwfs1 hks)
    have h_vs_perm : sameOrbitSetoid.r v_s (s.permute σ) := by
      have h3 : sameOrbitSetoid.r (s1.permute σ) (s.permute σ) :=
        sameOrbitSetoid.iseqv.symm (sameOrbit_permute (σ := σ) hclass_s1 hwf)
      rwa [← hv_s] at h3
    have horb : sameOrbitSetoid.r s (s.permute σ) :=
      sameOrbitSetoid.iseqv.trans hclass_s1
        (sameOrbitSetoid.iseqv.trans h_s1_vs h_vs_perm)
    exact ⟨σ, hσa, hσa', hσKB, hσfix, horb⟩

#print axioms exists_permute_of_kingPair_vacant'
/-- **The vacancy arm, KingBottom grade - the owner''s dichotomy
completed**: a KingBottom king pair at distinct anchors (runs on top
allowed) is strictly swappable in any class that carries a vacancy. -/
theorem swappableIn_king_of_vacancy'
    {s : State} {x : Card} {a a' : Anchor}
    (hwf : s.WF) (hking : x.rank = Rank.king)
    (hx : seatOf s x = some (Sum.inl a))
    (hxt : seatOf s x.twin = some (Sum.inl a'))
    (hne : a ≠ a')
    (hhidA : (s.piles a).hidden = [])
    (hhidB : (s.piles a').hidden = [])
    (hvac : SameOrbitVacant s) :
    SwappableIn s x := by
  obtain ⟨π, hπa, hπa', hπKB, hπfix, horb⟩ :=
    exists_permute_of_kingPair_vacant' hwf hking hx hxt hne hhidA hhidB hvac
  exact ⟨s.permute π,
    twinPairSwapStrict_permute_of_anchorSwap' π hwf hking hx hxt hne hhidA hhidB
      hπa hπa' hπKB hπfix,
    horb⟩

#print axioms swappableIn_king_of_vacancy'
