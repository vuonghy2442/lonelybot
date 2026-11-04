import Orig2.Fork.Split.ForkSplit

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Orig2/ForkDecide — `ShortestPlayExists` eliminated CONSTRUCTIVELY

SCRATCH card (`Temp/`); read-only on the repository; nothing committed.
No `sorry`, no `native_decide`, no `Classical.choice`, no `Classical.em`.

## The point

`Orig2/Fork/Class/ForkMin.lean` showed that `ValleyElim.ShortestPlayExists`
(`Orig2/Fork/Split/ForkSplit.lean:874`) is, at bottom, the least-element principle for
`Nat` — and that the general principle is exactly excluded middle
(`MinKit.natHasMin_iff_em`).  The escape is that the *specific* length
predicate is **decidable**: at a least witness we only ever have to search
the finitely many move lists below an explicit bound.  So no general
well-ordering is needed, and no classical logic is used.

The enumeration is **symbolic only**: `allListsOfLen n allMoves` has
`|allMoves|^n` elements (~`9300^n`); it is never evaluated, only reasoned
about through `mem_allListsOfLen` / `List.any_eq_true`.

## Pieces

1. `stateEqB` / `stateEqB_eq_true_iff` / `instDecidableEqState` — a public
   `DecidableEq State` (pointwise over `Suit.all` / `Anchor.all`, following the
   idea of the private `decSt` bridges at `Orig/Canonical.lean:4428` and
   `Orig/Dominance.lean:9780` — idea only, not the private name).
2. `allBases` / `allMoves` / `mem_allMoves` — an exhaustive move alphabet.
3. `allListsOfLen` / `mem_allListsOfLen` — bounded list enumeration.
4. `playOK` / `playOK_true_iff`, `isPlay` / `isPlay_iff` — the Bool play
   checker bridged to `ShufflePlayW` through the WF oracle
   (`Classification.reversibleOf_iff_reversibleAtW`).
5. `playExistsLen` / `playExistsLen_iff`, `exists_first_le` — bounded
   minimum over a *decidable* predicate.
6. `shortestPlayExists_choiceFree` — and the ungated form.
-/

namespace DecideKit

/-! ## Piece 1: a public `DecidableEq State` -/

/-- Pointwise state equality as a `Bool`: foundations and piles are compared
on the two finite enumerations (`Suit.all`, `Anchor.all`), the list fields
and the draw step directly. -/
def stateEqB (s t : State) : Bool :=
  (Suit.all.all (fun σ => decide (s.found σ = t.found σ))) &&
  (Anchor.all.all (fun a => decide (s.piles a = t.piles a))) &&
  decide (s.stock = t.stock) && decide (s.waste = t.waste) &&
  decide (s.drawStep = t.drawStep)

/-- **THE EQUALITY BRIDGE.** -/
theorem stateEqB_eq_true_iff (s t : State) : stateEqB s t = true ↔ s = t := by
  constructor
  · intro h
    simp only [stateEqB, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨hf, hp⟩, hs⟩, hw⟩, hd⟩ := h
    have hf' : s.found = t.found :=
      funext fun σ => of_decide_eq_true (hf σ (Suit.mem_all σ))
    have hp' : s.piles = t.piles :=
      funext fun a => of_decide_eq_true (hp a (Anchor.mem_all a))
    have hs' : s.stock = t.stock := of_decide_eq_true hs
    have hw' : s.waste = t.waste := of_decide_eq_true hw
    have hd' : s.drawStep = t.drawStep := of_decide_eq_true hd
    exact State.ext hf' hp' hs' hw' hd'
  · rintro rfl
    simp [stateEqB]

/-- **PIECE 1 (public).**  A `DecidableEq State` for the whole development.
Earlier homes keep their private copies (`Orig/Canonical.lean:4428`,
`Orig/Dominance.lean:9780`); this one is the public home. -/
instance instDecidableEqState : DecidableEq State := fun s t =>
  decidable_of_decidable_of_iff (p := stateEqB s t = true) (stateEqB_eq_true_iff s t)

/-- The `Option` lift used by the checker (deliberately a `Bool` rather than a
`decide`, so that no proof ever unfolds the equality decision on a symbolic
state). -/
def stateOptEqB : Option State → Option State → Bool
  | some s, some t => stateEqB s t
  | none, none => true
  | _, _ => false

theorem stateOptEqB_some_iff (o : Option State) (v : State) :
    stateOptEqB o (some v) = true ↔ o = some v := by
  cases o with
  | none => exact ⟨fun h => absurd h (Bool.false_ne_true), fun h => by cases h⟩
  | some s => exact ⟨fun h => congrArg some ((stateEqB_eq_true_iff s v).mp h),
      fun h => (stateEqB_eq_true_iff s v).mpr (Option.some.inj h)⟩

/-! ## Piece 2: an exhaustive move alphabet -/

/-- All bases: the seven empty tableau seats and the 52 pile-top cards. -/
def allBases : List Base :=
  Anchor.all.map Sum.inl ++ Card.universe.map Sum.inr

theorem mem_allBases (b : Base) : b ∈ allBases := by
  cases b with
  | inl a => simp [allBases, Anchor.mem_all]
  | inr z => simp [allBases, Card.mem_universe]

/-- Every move of the game, built from the finite enumerations. -/
def allMoves : List Move :=
  Move.draw ::
  (Card.universe.map Move.wasteToFound ++
  (Card.universe.flatMap fun c => allBases.map (Move.wasteToTab c)) ++
  Card.universe.map Move.tabToFound ++
  (Card.universe.flatMap fun c => allBases.map (Move.foundToTab c)) ++
  (Card.universe.flatMap fun c => allBases.map (Move.tabToTab c)))

/-- **PIECE 2.**  The alphabet is exhaustive.  Kept cheap: `allMoves` is only
ever unfolded here, never in a heavy goal. -/
theorem mem_allMoves (m : Move) : m ∈ allMoves := by
  cases m with
  | draw => simp [allMoves]
  | wasteToFound c => simp [allMoves, Card.mem_universe]
  | wasteToTab c b => simp [allMoves, mem_allBases, Card.mem_universe]
  | tabToFound c => simp [allMoves, Card.mem_universe]
  | foundToTab c b => simp [allMoves, mem_allBases, Card.mem_universe]
  | tabToTab c b => simp [allMoves, mem_allBases, Card.mem_universe]

/-! ## Piece 3: bounded list enumeration -/

/-- All lists of length `n` over `L`.  Symbolic only — never evaluated. -/
def allListsOfLen {α : Type} : Nat → List α → List (List α)
  | 0, _ => [[]]
  | n + 1, L => L.flatMap fun x => (allListsOfLen n L).map fun t => x :: t

/-- **PIECE 3.**  The enumeration is exact. -/
theorem mem_allListsOfLen {α : Type} (n : Nat) (L : List α) (l : List α) :
    l ∈ allListsOfLen n L ↔ l.length = n ∧ ∀ x ∈ l, x ∈ L := by
  induction n generalizing l with
  | zero =>
      constructor
      · intro h
        have hh : l ∈ ([[]] : List (List α)) := h
        have hl : l = [] := by simpa using hh
        subst hl
        exact ⟨rfl, by simp⟩
      · rintro ⟨hlen, _⟩
        have hl : l = [] := by
          cases l with
          | nil => rfl
          | cons x t => exact absurd hlen (Nat.succ_ne_zero t.length)
        subst hl
        change [] ∈ ([[]] : List (List α))
        exact List.mem_cons_self
  | succ n ih =>
      constructor
      · intro h
        change l ∈ (L.flatMap fun x => (allListsOfLen n L).map fun t => x :: t) at h
        rw [List.mem_flatMap] at h
        obtain ⟨x, hxL, hx⟩ := h
        rw [List.mem_map] at hx
        obtain ⟨t, ht, hxt⟩ := hx
        subst hxt
        obtain ⟨hlen, hmem⟩ := (ih t).mp ht
        refine ⟨by simp [hlen], ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hyt
        · exact hxL
        · exact hmem y hyt
      · rintro ⟨hlen, hmem⟩
        cases l with
        | nil => exact absurd hlen.symm (Nat.succ_ne_zero n)
        | cons x t =>
            change (x :: t) ∈ (L.flatMap fun x => (allListsOfLen n L).map fun t => x :: t)
            rw [List.mem_flatMap]
            refine ⟨x, hmem x List.mem_cons_self, ?_⟩
            rw [List.mem_map]
            refine ⟨t, ?_, rfl⟩
            exact (ih t).mpr ⟨by simpa using hlen,
              fun y hy => hmem y (List.mem_cons_of_mem _ hy)⟩

/-! ## Piece 4: the Bool play checker and the WF oracle bridge -/

/-- **PIECE 4a.**  `playOK st ρ` checks that every letter is reversible at its
origin, following the deterministic step function.  Note
`reversibleOf` is `false` on the two waste letters
(`Orig2/Substrate/Vocab.lean:196, 201-202`) — exact at WF states, so those letters are
simply never witness-reversible. -/
def playOK (st : State) : List Move → Bool
  | [] => true
  | m :: ms =>
      match State.step st m with
      | none => false
      | some st' => reversibleOf st m && playOK st' ms

/-- Inversion of a nonempty walk. -/
theorem walk_cons_inv {P : State → Move → Prop} {st : State} {m : Move}
    {ms : List Move} {W : State} (h : Walk P st (m :: ms) W) :
    ∃ s₁ : State, P st m ∧ State.step st m = some s₁ ∧ Walk P s₁ ms W := by
  cases h with
  | cons hlet hstep hrest => exact ⟨_, hlet, hstep, hrest⟩

/-- **PIECE 4b (the oracle bridge).**  At a WF origin, `playOK` is exactly the
`ShufflePlayW` walk. -/
theorem playOK_true_iff {st : State} (hwf : st.WF) (ρ : List Move) :
    playOK st ρ = true ↔
      ∃ W : State, Walk (fun st m => reversibleAtW st m) st ρ W := by
  induction ρ generalizing st with
  | nil => exact ⟨fun _ => ⟨st, Walk.nil st⟩, fun _ => rfl⟩
  | cons m ms ih =>
      have hdef : playOK st (m :: ms) =
          (match State.step st m with
           | none => false
           | some st' => reversibleOf st m && playOK st' ms) := rfl
      rw [hdef]
      cases hs : State.step st m with
      | none =>
          constructor
          · intro h; exact absurd h (Bool.false_ne_true)
          · rintro ⟨W, hW⟩
            obtain ⟨s₁, _, hstep, _⟩ := walk_cons_inv hW
            rw [hs] at hstep
            exact absurd hstep (by simp)
      | some st' =>
          constructor
          · intro h
            rw [Bool.and_eq_true] at h
            obtain ⟨W, hW⟩ := (ih (step_wf hwf hs)).mp h.2
            exact ⟨W, Walk.cons ((reversibleOf_iff_reversibleAtW hwf m).mp h.1) hs hW⟩
          · rintro ⟨W, hW⟩
            rw [Bool.and_eq_true]
            obtain ⟨s₁, hlet, hstep, hrest⟩ := walk_cons_inv hW
            have hsome : some st' = some s₁ := by
              rw [hs] at hstep
              exact hstep
            have he : s₁ = st' := (Option.some.inj hsome).symm
            have hrest' : Walk (fun st m => reversibleAtW st m) st' ms W := he ▸ hrest
            exact ⟨(reversibleOf_iff_reversibleAtW hwf m).mpr hlet,
              (ih (st := st') (step_wf hwf hs)).mpr ⟨W, hrest'⟩⟩

/-- **PIECE 4c.**  A full play check: legal, all letters reversible, and the
run lands exactly on `v`. -/
def isPlay (u v : State) (ρ : List Move) : Bool :=
  playOK u ρ && stateOptEqB (u.run ρ) (some v)

/-- **PIECE 4d.**  `isPlay` decides `ShufflePlayW` at a WF origin. -/
theorem isPlay_iff {u v : State} (huwf : u.WF) (ρ : List Move) :
    isPlay u v ρ = true ↔ ShufflePlayW u ρ v := by
  rw [isPlay, Bool.and_eq_true]
  constructor
  · rintro ⟨hok, hrun⟩
    obtain ⟨W, hW⟩ := (playOK_true_iff huwf ρ).mp hok
    have h1 : u.run ρ = some W := Walk_run _ hW
    have h2 : u.run ρ = some v := (stateOptEqB_some_iff _ v).mp hrun
    have hWv : W = v := Option.some.inj (h1.symm.trans h2)
    subst hWv
    exact hW
  · intro h
    exact ⟨(playOK_true_iff huwf ρ).mpr ⟨v, h⟩,
      (stateOptEqB_some_iff _ v).mpr (Walk_run _ h)⟩

/-! ## Piece 5: the bounded minimum over a decidable predicate -/

/-- **PIECE 5a.**  "There is a play of length exactly `n`", decided by brute
force over the symbolic alphabet. -/
def playExistsLen (u v : State) (n : Nat) : Bool :=
  (allListsOfLen n allMoves).any (isPlay u v)

/-- **PIECE 5b.**  Exactness of the bounded search at a WF origin. -/
theorem playExistsLen_iff {u v : State} (huwf : u.WF) (n : Nat) :
    playExistsLen u v n = true ↔
      ∃ ρ : List Move, ρ.length = n ∧ ShufflePlayW u ρ v := by
  rw [playExistsLen, List.any_eq_true]
  constructor
  · rintro ⟨ρ, hmem, his⟩
    obtain ⟨hlen, -⟩ := (mem_allListsOfLen n allMoves ρ).mp hmem
    exact ⟨ρ, hlen, (isPlay_iff huwf ρ).mp his⟩
  · rintro ⟨ρ, hlen, hplay⟩
    refine ⟨ρ, (mem_allListsOfLen n allMoves ρ).mpr ⟨hlen, fun m _ => mem_allMoves m⟩, ?_⟩
    exact (isPlay_iff huwf ρ).mpr hplay

/-- **PIECE 5c (the finite minimum).**  Over a *decidable* predicate with an
explicit upper bound there is a first `true` — plain recursion on the bound,
no choice, no well-ordering, no EM. -/
theorem exists_first_le (p : Nat → Bool) :
    ∀ B : Nat, p B = true →
      ∃ n, n ≤ B ∧ p n = true ∧ ∀ m, m < n → p m = false := by
  intro B
  induction B generalizing p with
  | zero =>
      intro h
      exact ⟨0, Nat.zero_le _, h, fun m hm => absurd hm (Nat.not_lt_zero m)⟩
  | succ B ih =>
      intro h
      by_cases h0 : p 0 = true
      · exact ⟨0, Nat.zero_le _, h0, fun m hm => absurd hm (Nat.not_lt_zero m)⟩
      · have hp0 : p 0 = false := by
          cases hh : p 0 with
          | true => exact absurd hh h0
          | false => rfl
        obtain ⟨n, hnle, hpn, hmin⟩ := ih (fun k => p (k + 1)) h
        refine ⟨n + 1, Nat.succ_le_succ hnle, hpn, ?_⟩
        intro m hm
        cases m with
        | zero => exact hp0
        | succ k => exact hmin k (Nat.lt_of_succ_lt_succ hm)

/-! ## Piece 6: assembly -/

/-- **THE UNGATED FORM.**  No `SSaturated`, no rung difference — only the
`u.WF` needed by the oracle bridge (the target's same-state `WF` is not even
needed for `v`). -/
theorem shortestPlayExists_ungated_choiceFree (u v : State) (huwf : u.WF)
    (hcls : sameOrbitSetoid.r u v) :
    ∃ ρ : List Move, ShufflePlayW u ρ v ∧
      ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length := by
  obtain ⟨ρ₀, hρ₀⟩ := sameOrbit_reachable hcls
  have hB : playExistsLen u v ρ₀.length = true :=
    (playExistsLen_iff huwf ρ₀.length).mpr ⟨ρ₀, rfl, hρ₀⟩
  obtain ⟨n, _hnB, hn, hmin⟩ := exists_first_le (playExistsLen u v) ρ₀.length hB
  obtain ⟨ρ, hlen, hplay⟩ := (playExistsLen_iff huwf n).mp hn
  refine ⟨ρ, hplay, fun ρ' hρ' => ?_⟩
  have hnot : ¬ ρ'.length < n := by
    intro hlt
    have hfalse : playExistsLen u v ρ'.length = false := hmin ρ'.length hlt
    have htrue : playExistsLen u v ρ'.length = true :=
      (playExistsLen_iff huwf ρ'.length).mpr ⟨ρ', rfl, hρ'⟩
    rw [hfalse] at htrue
    exact Bool.false_ne_true htrue
  rw [hlen]
  exact Nat.le_of_not_lt hnot

/-- **THE DELIVERABLE.**  `ValleyElim.ShortestPlayExists`
(`Orig2/Fork/Split/ForkSplit.lean:874`) holds constructively: the gates are ignored,
the rung difference is ignored, and the *only* input is the orbit relation
the theorem itself hypothesises. -/
theorem shortestPlayExists_choiceFree : ValleyElim.ShortestPlayExists := by
  intro u v huwf _hsu _hsv hcls _hdiff
  exact shortestPlayExists_ungated_choiceFree u v huwf hcls

/-- The residual of `Orig2/Fork/Class/ForkMin.lean` (`PlayLenMin`, the least element of
the play-length set) discharged at `WF` origins: the `WF` gate is exactly the
decidability of the length predicate. -/
theorem playLenMin_at_wf (u v : State) (huwf : u.WF)
    (hex : ∃ ρ : List Move, ShufflePlayW u ρ v) :
    ∃ m : Nat,
      (∃ ρ : List Move, ShufflePlayW u ρ v ∧ ρ.length = m) ∧
        ∀ k : Nat, k < m → ¬ ∃ ρ : List Move, ShufflePlayW u ρ v ∧ ρ.length = k := by
  obtain ⟨ρ₀, hρ₀⟩ := hex
  have hB : playExistsLen u v ρ₀.length = true :=
    (playExistsLen_iff huwf ρ₀.length).mpr ⟨ρ₀, rfl, hρ₀⟩
  obtain ⟨n, _hnB, hn, hmin⟩ := exists_first_le (playExistsLen u v) ρ₀.length hB
  obtain ⟨ρ, hlen, hplay⟩ := (playExistsLen_iff huwf n).mp hn
  refine ⟨n, ⟨ρ, hplay, hlen⟩, ?_⟩
  intro k hk hkex
  obtain ⟨ρ', hplay', hlen'⟩ := hkex
  have htrue : playExistsLen u v k = true :=
    (playExistsLen_iff huwf k).mpr ⟨ρ', hlen', hplay'⟩
  rw [hmin k hk] at htrue
  exact Bool.false_ne_true htrue

/-- **THE INTERFACE HYPOTHESIS IS GONE.**  Valley elimination alone gives
`SatDifferForkWF`: the `ShortestPlayExists` input of
`satDifferForkWF_of_valleyElimNonfork` (`Orig2/Fork/Split/ForkSplit.lean:886`) is
discharged here. -/
theorem satDifferForkWF_of_valleyElimNonfork_choiceFree
    (h : ValleyElim.ValleyElimNonfork) : SatDifferForkWF :=
  ValleyElim.satDifferForkWF_of_valleyElimNonfork h shortestPlayExists_choiceFree

end DecideKit

/-! ## Axiom battery

Expected: no `Classical.choice`, no `Classical.em`, no `sorryAx`,
no `Lean.ofReduceBool` (i.e. no `native_decide`). -/

#print axioms DecideKit.stateEqB_eq_true_iff
#print axioms DecideKit.instDecidableEqState
#print axioms DecideKit.mem_allMoves
#print axioms DecideKit.mem_allListsOfLen
#print axioms DecideKit.playOK_true_iff
#print axioms DecideKit.isPlay_iff
#print axioms DecideKit.playExistsLen_iff
#print axioms DecideKit.exists_first_le
#print axioms DecideKit.shortestPlayExists_ungated_choiceFree
#print axioms DecideKit.shortestPlayExists_choiceFree
#print axioms DecideKit.playLenMin_at_wf
#print axioms DecideKit.satDifferForkWF_of_valleyElimNonfork_choiceFree
#print axioms ValleyElim.ShortestPlayExists
