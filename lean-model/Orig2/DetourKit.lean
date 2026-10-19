import Orig2.TwinEquivariance
import Orig2.SeatMateStack

/-!
# Orig2.DetourKit — the pair-foundation detour plumbing

The pair-foundation predicate, the first-detour split, and the
pair-free play's seated preservation for the twin pair.

House compliance: additive scratch leaf; axiom-clean.
-/

/-! ## §1. The pair-foundation predicate -/

/-- The four pair-foundation moves of the twin pair `{x, x.twin}`:
raising either twin, or pulling either twin from its foundation. -/
def IsPairFound (x : Card) (m : Move) : Prop :=
  m = Move.tabToFound x ∨ m = Move.tabToFound x.twin ∨
    (∃ b : Base, m = Move.foundToTab x b) ∨
    (∃ b : Base, m = Move.foundToTab x.twin b)

/-- `NotFoundPair` is exactly the negation of `IsPairFound`. -/
theorem notFoundPair_iff_not_isPairFound (x : Card) (m : Move) :
    NotFoundPair x m ↔ ¬ IsPairFound x m := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩ (h | h | ⟨b, hb⟩ | ⟨b, hb⟩)
    · exact h1 h
    · exact h2 h
    · exact h3 b hb
    · exact h4 b hb
  · intro h
    exact ⟨fun hm => h (Or.inl hm),
      fun hm => h (Or.inr (Or.inl hm)),
      fun b hm => h (Or.inr (Or.inr (Or.inl ⟨b, hm⟩))),
      fun b hm => h (Or.inr (Or.inr (Or.inr ⟨b, hm⟩)))⟩

/-! ## §2. The first-detour split -/

/-- A computable read of the pair-foundation predicate. -/
private def isPairFoundB (x : Card) (m : Move) : Bool :=
  match m with
  | .draw => false
  | .wasteToFound _ => false
  | .wasteToTab _ _ => false
  | .tabToFound c => decide (c = x ∨ c = x.twin)
  | .foundToTab c _ => decide (c = x ∨ c = x.twin)
  | .tabToTab _ _ => false

/-- The computable read is exact. -/
private theorem isPairFoundB_iff (x : Card) (m : Move) :
    isPairFoundB x m = true ↔ IsPairFound x m := by
  cases m <;> simp [isPairFoundB, IsPairFound]

/-- A play either avoids the pair-foundation moves entirely, or has a
first pair-foundation move: a prefix of pair-free letters, that move,
and an arbitrary suffix. -/
theorem exists_pairFound_split (x : Card) (play : List Move) :
    (∀ m ∈ play, ¬ IsPairFound x m) ∨
    ∃ pre m post, play = pre ++ m :: post ∧ IsPairFound x m ∧
      (∀ n ∈ pre, ¬ IsPairFound x n) := by
  induction play with
  | nil => exact Or.inl (by simp)
  | cons a t ih =>
      by_cases ha : isPairFoundB x a = true
      · exact Or.inr ⟨[], a, t, rfl, (isPairFoundB_iff x a).mp ha, by simp⟩
      · have ha' : ¬ IsPairFound x a := fun h => ha ((isPairFoundB_iff x a).mpr h)
        rcases ih with hno | ⟨pre, m, post, hsplit, hm, hpre⟩
        · exact Or.inl (by
            intro n hn
            rcases List.mem_cons.mp hn with rfl | hnt
            · exact ha'
            · exact hno n hnt)
        · exact Or.inr ⟨a :: pre, m, post, by
            rw [List.cons_append, hsplit], hm, by
            intro n hn
            rcases List.mem_cons.mp hn with rfl | hnp
            · exact ha'
            · exact hpre n hnp⟩

/-! ## §3. The card-count measure -/

namespace DetourKit

/-- The pile's own card count. -/
private def pileCount (p : Pile) : Nat := p.hidden.length + p.faceUp.length

/-- The foundation card total. -/
private def foundTotal (st : State) : Nat :=
  (Suit.all.map (fun s => (st.found s).length)).sum

/-- The tableau card total. -/
private def pileTotal (st : State) : Nat :=
  (Anchor.all.map (fun a => pileCount (st.piles a))).sum

/-- The whole-board card total (foundations, tableau, stock, waste). -/
private def totalCards (st : State) : Nat :=
  foundTotal st + pileTotal st + st.stock.length + st.waste.length

/-- Every pile's count is bounded by the tableau total. -/
private theorem pileCount_le_pileTotal (st : State) (a : Anchor) :
    pileCount (st.piles a) ≤ pileTotal st := by
  unfold pileTotal
  cases a <;> simp [Anchor.all] <;> omega

/-- Appending a fresh card to a foundation row raises the foundation total by one. -/
private theorem foundTotal_setFound_append (st : State) (s : Suit) (c : Card) :
    foundTotal (st.setFound s (st.found s ++ [c])) = foundTotal st + 1 := by
  unfold foundTotal State.setFound
  cases s <;> simp [Suit.all] <;> omega

/-- Chopping a nonempty foundation row lowers the foundation total by one. -/
private theorem foundTotal_setFound_chop (st : State) (s : Suit) {c : Card}
    (h : lastOf (st.found s) = some c) :
    foundTotal (st.setFound s (chop (st.found s))) + 1 = foundTotal st := by
  have hsnoc : st.found s = chop (st.found s) ++ [c] := lastOf_chop h
  have hlen : (st.found s).length = (chop (st.found s)).length + 1 := by
    rw [congrArg List.length hsnoc, List.length_append]
    simp
  unfold foundTotal State.setFound
  cases s <;> simp [Suit.all] <;> omega

/-- The pile-total point update. -/
private theorem pileTotal_setPile (st : State) (a : Anchor) (p : Pile) :
    pileTotal (st.setPile a p) =
      pileTotal st - pileCount (st.piles a) + pileCount p := by
  unfold pileTotal State.setPile
  cases a <;> simp [Anchor.all] <;> omega

/-- The run removal drops exactly the run's length from the source pile. -/
private theorem pileCount_afterRunRemoved_add_run {p : Pile} {c : Card}
    (_hmem : c ∈ p.faceUp) :
    pileCount (Pile.afterRunRemoved p (below c p.faceUp)) +
      (fromCard c p.faceUp).length = pileCount p := by
  have hsplit : below c p.faceUp ++ fromCard c p.faceUp = p.faceUp :=
    tfc_below_fromCard c p.faceUp
  unfold pileCount
  cases hp : below c p.faceUp with
  | nil =>
      have hlen : p.faceUp.length = (fromCard c p.faceUp).length := by
        simpa [hp] using congrArg List.length hsplit.symm
      cases hh : p.hidden with
      | nil =>
          simp [Pile.afterRunRemoved, Pile.revealTop, hh]
          omega
      | cons h t =>
          simp [Pile.afterRunRemoved, Pile.revealTop, hh]
          omega
  | cons x xs =>
      have hlen : (below c p.faceUp).length + (fromCard c p.faceUp).length =
          p.faceUp.length := by
        rw [← List.length_append, hsplit]
      rw [hp] at hlen
      simp only [List.length_cons] at hlen
      simp [Pile.afterRunRemoved]
      omega

/-- The source pile loses exactly the run length in the slide. -/
private theorem pileTotal_afterRunRemoved_add_run (st : State) (a : Anchor) (c : Card)
    (hmem : c ∈ (st.piles a).faceUp) :
    pileTotal (st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))) +
      (fromCard c (st.piles a).faceUp).length = pileTotal st := by
  rw [pileTotal_setPile]
  have hpc := pileCount_afterRunRemoved_add_run (p := st.piles a) hmem
  have hle := pileCount_le_pileTotal st a
  omega

/-- A run write adds at most the run's length to the tableau total. -/
private theorem pileTotal_putRun_le (u : State) (run : List Card) (b : Base) :
    pileTotal (u.putRun run b) ≤ pileTotal u + run.length := by
  cases b with
  | inl a =>
      rw [show u.putRun run (Sum.inl a) = u.setPile a ⟨[], run⟩ from rfl,
        pileTotal_setPile]
      have hle := pileCount_le_pileTotal u a
      unfold pileCount
      simp
  | inr z =>
      cases hz : u.pileOfTop z with
      | none =>
          simp only [State.putRun, hz]
          omega
      | some k =>
          rw [show u.putRun run (Sum.inr z) =
            u.setPile k { u.piles k with faceUp := (u.piles k).faceUp ++ run } from by
              simp only [State.putRun, hz]]
          rw [pileTotal_setPile]
          have hle : (u.piles k).hidden.length + (u.piles k).faceUp.length ≤
              pileTotal u := by
            simpa [pileCount] using pileCount_le_pileTotal u k
          unfold pileCount
          simp only [List.length_append]
          omega

/-- The raise removal drops exactly one card from the source pile. -/
private theorem pileCount_afterRunRemoved_chop_add_one {p : Pile} {c : Card}
    (h : lastOf p.faceUp = some c) :
    pileCount (Pile.afterRunRemoved p (chop p.faceUp)) + 1 = pileCount p := by
  have hsnoc : p.faceUp = chop p.faceUp ++ [c] := lastOf_chop h
  have hlen : p.faceUp.length = (chop p.faceUp).length + 1 := by
    rw [congrArg List.length hsnoc, List.length_append]
    simp
  unfold pileCount
  cases hc : chop p.faceUp with
  | nil =>
      have hface : p.faceUp = [c] := by rw [hsnoc, hc]; rfl
      cases hh : p.hidden with
      | nil =>
          simp [Pile.afterRunRemoved, Pile.revealTop, hh, hface]
      | cons hd t =>
          simp [Pile.afterRunRemoved, Pile.revealTop, hh, hface]
  | cons x xs =>
      rw [hc] at hlen
      simp only [List.length_cons] at hlen
      simp only [Pile.afterRunRemoved, List.length_cons]
      omega

/-- The source pile loses exactly one card in a raise. -/
private theorem pileTotal_afterRunRemoved_chop_add_one (st : State) (a : Anchor) (c : Card)
    (h : lastOf (st.piles a).faceUp = some c) :
    pileTotal (st.setPile a
        (Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp))) + 1 =
      pileTotal st := by
  rw [pileTotal_setPile]
  have hpc := pileCount_afterRunRemoved_chop_add_one (p := st.piles a) h
  have hle := pileCount_le_pileTotal st a
  omega

/-- A single-card write with a placement license adds exactly one card. -/
private theorem pileTotal_putCard (u : State) {c : Card} {b : Base}
    (hcp : u.canPlace c b = true) :
    pileTotal (u.putCard c b) = pileTotal u + 1 := by
  cases b with
  | inl a =>
      obtain ⟨hemp, -⟩ := canPlace_inl hcp
      obtain ⟨hhd, hfu⟩ := (Pile.isEmpty_eq _).mp hemp
      rw [show u.putCard c (Sum.inl a) = u.setPile a ⟨[], [c]⟩ from rfl,
        pileTotal_setPile]
      have hpc : pileCount (u.piles a) = 0 := by
        unfold pileCount
        rw [hhd, hfu]
        simp
      rw [hpc]
      unfold pileCount
      simp only [List.length_nil, List.length_singleton]
      omega
  | inr z =>
      obtain ⟨k, hz, -⟩ := canPlace_inr hcp
      rw [show u.putCard c (Sum.inr z) =
        u.setPile k { u.piles k with faceUp := (u.piles k).faceUp ++ [c] } from by
          simp only [State.putCard, hz]]
      rw [pileTotal_setPile]
      have hle : (u.piles k).hidden.length + (u.piles k).faceUp.length ≤ pileTotal u := by
        simpa [pileCount] using pileCount_le_pileTotal u k
      unfold pileCount
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

/-- Foundation totals are blind to points outside `found`. -/
private theorem foundTotal_congr_found {u v : State} (h : v.found = u.found) :
    foundTotal v = foundTotal u := by
  unfold foundTotal
  rw [h]

/-- Tableau totals are blind to points outside `piles`. -/
private theorem pileTotal_congr_piles {u v : State} (h : v.piles = u.piles) :
    pileTotal v = pileTotal u := by
  unfold pileTotal
  rw [h]

/-- No legal move raises the whole-board card total. -/
private theorem totalCards_step_le {u v : State} {m : Move}
    (h : State.step u m = some v) : totalCards v ≤ totalCards u := by
  cases m with
  | draw =>
      have hd : u.stepDraw = some v := h
      have hf := draw_footprint hd
      have hcy := hf.2.2.2.1
      unfold cycleCount at hcy
      unfold totalCards
      rw [foundTotal_congr_found hf.2.1, pileTotal_congr_piles hf.2.2.1]
      omega
  | wasteToFound c =>
      obtain ⟨-, x, xs, hw, hs⟩ := step_wasteToFound_inv h
      rw [hs]
      dsimp only []
      have hfv : foundTotal { u.setFound c.suit (u.found c.suit ++ [c]) with waste := xs } =
          foundTotal (u.setFound c.suit (u.found c.suit ++ [c])) :=
        foundTotal_congr_found rfl
      have hft := foundTotal_setFound_append u c.suit c
      have hpt : pileTotal { u.setFound c.suit (u.found c.suit ++ [c]) with waste := xs } =
          pileTotal u :=
        (pileTotal_congr_piles rfl).trans
          (pileTotal_congr_piles (setFound_piles u c.suit (u.found c.suit ++ [c])))
      have hstock : ({ u.setFound c.suit (u.found c.suit ++ [c]) with waste := xs } : State).stock =
          u.stock := by
        dsimp only []
        rw [setFound_stock]
      have hwaste : ({ u.setFound c.suit (u.found c.suit ++ [c]) with waste := xs } : State).waste =
          xs := rfl
      unfold totalCards
      rw [hfv, hft, hpt, hstock, hwaste, hw]
      simp only [List.length_cons]
      omega
  | wasteToTab c b =>
      obtain ⟨hguard, x, xs, hw, hs⟩ := step_wasteToTab_inv h
      rw [Bool.and_eq_true] at hguard
      obtain ⟨-, hcp⟩ := hguard
      rw [hs]
      dsimp only []
      have hfv : foundTotal { u.putCard c b with waste := xs } =
          foundTotal (u.putCard c b) := foundTotal_congr_found rfl
      have hfv' : foundTotal (u.putCard c b) = foundTotal u :=
        foundTotal_congr_found (putCard_found u c b)
      have hpt : pileTotal { u.putCard c b with waste := xs } =
          pileTotal (u.putCard c b) := pileTotal_congr_piles rfl
      have hpt' : pileTotal (u.putCard c b) = pileTotal u + 1 := pileTotal_putCard u hcp
      have hstock : ({ u.putCard c b with waste := xs } : State).stock = u.stock := by
        dsimp only []
        rw [putCard_stock]
      have hwaste : ({ u.putCard c b with waste := xs } : State).waste = xs := rfl
      unfold totalCards
      rw [hfv, hfv', hpt, hpt', hstock, hwaste, hw]
      simp only [List.length_cons]
      omega
  | tabToFound c =>
      obtain ⟨-, a, hpa, hs⟩ := step_tabToFound_inv h
      have hlast : lastOf (u.piles a).faceUp = some c := by
        have hsound := firstWhere_sound (p := fun a' => decide (u.topOf a' = some c)) hpa
        exact of_decide_eq_true hsound
      rw [hs]
      dsimp only []
      have hfv : foundTotal
          { u.setFound c.suit (u.found c.suit ++ [c]) with
            piles := fun a' => if a' = a then
              Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp)
            else u.piles a' } =
          foundTotal (u.setFound c.suit (u.found c.suit ++ [c])) :=
        foundTotal_congr_found rfl
      have hft := foundTotal_setFound_append u c.suit c
      have hpt : pileTotal
          { u.setFound c.suit (u.found c.suit ++ [c]) with
            piles := fun a' => if a' = a then
              Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp)
            else u.piles a' } =
          pileTotal (u.setPile a (Pile.afterRunRemoved (u.piles a)
            (chop (u.piles a).faceUp))) :=
        pileTotal_congr_piles rfl
      have hdrop := pileTotal_afterRunRemoved_chop_add_one u a c hlast
      have hstock : ({ u.setFound c.suit (u.found c.suit ++ [c]) with
          piles := fun a' => if a' = a then
            Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp)
          else u.piles a' } : State).stock = u.stock := by
        dsimp only []
        rw [setFound_stock]
      have hwaste : ({ u.setFound c.suit (u.found c.suit ++ [c]) with
          piles := fun a' => if a' = a then
            Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp)
          else u.piles a' } : State).waste = u.waste := by
        dsimp only []
        rw [setFound_waste]
      unfold totalCards
      rw [hfv, hft, hpt, hstock, hwaste]
      omega
  | foundToTab c b =>
      obtain ⟨c', htop, hc'c, hcp, hs⟩ := step_foundToTab_inv h
      have hlast : lastOf (u.found c.suit) = some c := by
        unfold State.foundTop at htop
        rw [hc'c] at htop
        exact htop
      rw [hs]
      have hFv : foundTotal ((u.setFound c.suit (chop (u.found c.suit))).putCard c b) =
          foundTotal (u.setFound c.suit (chop (u.found c.suit))) :=
        foundTotal_congr_found (putCard_found _ c b)
      have hFc : foundTotal (u.setFound c.suit (chop (u.found c.suit))) + 1 =
          foundTotal u := foundTotal_setFound_chop u c.suit hlast
      have hPv : pileTotal ((u.setFound c.suit (chop (u.found c.suit))).putCard c b) =
          pileTotal (u.setFound c.suit (chop (u.found c.suit))) + 1 :=
        pileTotal_putCard _ hcp
      have hPc : pileTotal (u.setFound c.suit (chop (u.found c.suit))) = pileTotal u :=
        pileTotal_congr_piles (setFound_piles u c.suit (chop (u.found c.suit)))
      have hstock : ((u.setFound c.suit (chop (u.found c.suit))).putCard c b).stock =
          u.stock := by
        rw [putCard_stock, setFound_stock]
      have hwaste : ((u.setFound c.suit (chop (u.found c.suit))).putCard c b).waste =
          u.waste := by
        rw [putCard_waste, setFound_waste]
      unfold totalCards
      rw [hFv, hPv, hPc, hstock, hwaste]
      omega
  | tabToTab c b =>
      obtain ⟨a, hhold, hcp, hne, hs⟩ := step_tabToTab_inv h
      have hmem := pileHolding_mem hhold
      rw [hs]
      have hsrc := pileTotal_afterRunRemoved_add_run u a c hmem
      have hdst := pileTotal_putRun_le
        (u.setPile a (Pile.afterRunRemoved (u.piles a) (below c (u.piles a).faceUp)))
        (fromCard c (u.piles a).faceUp) b
      have hfoundEq : ((u.setPile a (Pile.afterRunRemoved (u.piles a)
            (below c (u.piles a).faceUp))).putRun (fromCard c (u.piles a).faceUp) b).found =
          u.found := by
        rw [putRun_found, setPile_found]
      have hF : foundTotal ((u.setPile a (Pile.afterRunRemoved (u.piles a)
            (below c (u.piles a).faceUp))).putRun (fromCard c (u.piles a).faceUp) b) =
          foundTotal u := foundTotal_congr_found hfoundEq
      have hP : pileTotal ((u.setPile a (Pile.afterRunRemoved (u.piles a)
            (below c (u.piles a).faceUp))).putRun (fromCard c (u.piles a).faceUp) b) ≤
          pileTotal u := by omega
      have hstock : ((u.setPile a (Pile.afterRunRemoved (u.piles a)
            (below c (u.piles a).faceUp))).putRun (fromCard c (u.piles a).faceUp) b).stock =
          u.stock := by
        rw [putRun_stock, setPile_stock]
      have hwaste : ((u.setPile a (Pile.afterRunRemoved (u.piles a)
            (below c (u.piles a).faceUp))).putRun (fromCard c (u.piles a).faceUp) b).waste =
          u.waste := by
        rw [putRun_waste, setPile_waste]
      unfold totalCards
      rw [hF, hstock, hwaste]
      omega

/-- A play cannot raise the whole-board card total. -/
private theorem totalCards_run_le {u v : State} {play : List Move}
    (h : u.run play = some v) : totalCards v ≤ totalCards u :=
  mono_run totalCards (fun _ _ _ hs => totalCards_step_le hs) h

/-- A face-up card has a seat (the local restatement of the private
`SeatMateStack` row). -/
private theorem seatOf_ne_of_mem_faceUp' {st : State} {c : Card} {a : Anchor}
    (h : c ∈ (st.piles a).faceUp) : seatOf st c ≠ none := by
  intro hse
  have hh : st.pileHolding c = none := by
    by_cases hhold : st.pileHolding c = none
    · exact hhold
    · obtain ⟨a', ha'⟩ := option_some_of_ne_none hhold
      rw [tfc_seatOf_pair ha'] at hse
      cases hg : List.getLast? (below c (st.piles a').faceUp) with
      | none =>
          rw [hg] at hse
          exact absurd hse (by simp)
      | some z =>
          rw [hg] at hse
          exact absurd hse (by simp)
  exact tfc_not_mem_faceUp_of_holdNone hh a h

/-- A seated card is face-up somewhere. -/
private theorem mem_faceUp_of_seat_ne_none {st : State} {c : Card}
    (h : seatOf st c ≠ none) : ∃ a, c ∈ (st.piles a).faceUp := by
  have hh : st.pileHolding c ≠ none := by
    intro hnone
    exact h (tfc_seatOf_none hnone)
  obtain ⟨a, ha⟩ := option_some_of_ne_none hh
  exact ⟨a, pileHolding_mem ha⟩

/-- A single-card write with a placement license never loses an existing
face-up card. -/
private theorem putCard_faceUp_mem_of_mem {u : State} {c0 x : Card} {b : Base}
    (hcp : u.canPlace x b = true) {a : Anchor} (h : c0 ∈ (u.piles a).faceUp) :
    ∃ a', c0 ∈ ((u.putCard x b).piles a').faceUp := by
  cases b with
  | inl t =>
      obtain ⟨hemp, -⟩ := canPlace_inl hcp
      have hfalse := Pile.isEmpty_eq_false_of_mem h
      have hat : a ≠ t := by
        intro hatt
        rw [hatt] at hfalse
        rw [hemp] at hfalse
        exact Bool.noConfusion hfalse
      rw [putCard_piles_inl]
      dsimp only
      refine ⟨a, ?_⟩
      rw [ite_eq_right hat]
      exact h
  | inr z =>
      obtain ⟨k, hz, -⟩ := canPlace_inr hcp
      rw [putCard_piles_inr _ _ _ _ hz]
      dsimp only
      by_cases hak : a = k
      · subst hak
        refine ⟨a, ?_⟩
        rw [ite_eq_left rfl]
        exact List.mem_append_left _ h
      · refine ⟨a, ?_⟩
        rw [ite_eq_right hak]
        exact h

/-- A run write never loses an existing face-up card, as long as its
`inl` landing is elsewhere. -/
private theorem putRun_faceUp_mem_of_mem {u : State} {run : List Card} {b : Base}
    {c : Card} {a : Anchor} (h : c ∈ (u.piles a).faceUp)
    (hinl : ∀ a', b = Sum.inl a' → a' ≠ a) :
    ∃ a', c ∈ ((u.putRun run b).piles a').faceUp := by
  cases b with
  | inl t =>
      rw [putRun_piles_inl]
      dsimp only
      refine ⟨a, ?_⟩
      rw [ite_eq_right (fun (hta : a = t) => hinl t rfl hta.symm)]
      exact h
  | inr z =>
      cases hz : u.pileOfTop z with
      | none =>
          refine ⟨a, ?_⟩
          simp only [State.putRun, hz]
          exact h
      | some k =>
          rw [putRun_piles_inr _ _ _ _ hz]
          dsimp only
          by_cases hak : a = k
          · subst hak
            refine ⟨a, ?_⟩
            rw [ite_eq_left rfl]
            exact List.mem_append_left _ h
          · refine ⟨a, ?_⟩
            rw [ite_eq_right hak]
            exact h

/-- The no-op `tabToTab` landing strictly drops the whole-board total. -/
private theorem totalCards_lt_of_tabToTab_noop {u v : State} {c z : Card} {a : Anchor}
    (hhold : u.pileHolding c = some a)
    (hs : v = (u.setPile a
        (Pile.afterRunRemoved (u.piles a) (below c (u.piles a).faceUp))).putRun
          (fromCard c (u.piles a).faceUp) (Sum.inr z))
    (hnone : (u.setPile a
        (Pile.afterRunRemoved (u.piles a) (below c (u.piles a).faceUp))).pileOfTop z = none) :
    totalCards v < totalCards u := by
  have hmem := pileHolding_mem hhold
  have hsrc := pileTotal_afterRunRemoved_add_run u a c hmem
  have hrunpos : 0 < (fromCard c (u.piles a).faceUp).length := by
    obtain ⟨t, ht⟩ := fromCard_eq_head_of_mem hmem
    rw [ht]
    simp
  have hv : v = u.setPile a
      (Pile.afterRunRemoved (u.piles a) (below c (u.piles a).faceUp)) := by
    rw [hs]
    simp only [State.putRun, hnone]
  have hF : foundTotal (u.setPile a
      (Pile.afterRunRemoved (u.piles a) (below c (u.piles a).faceUp))) = foundTotal u :=
    foundTotal_congr_found (setPile_found u a _)
  have hstock : (u.setPile a
      (Pile.afterRunRemoved (u.piles a) (below c (u.piles a).faceUp))).stock = u.stock :=
    setPile_stock u a _
  have hwaste : (u.setPile a
      (Pile.afterRunRemoved (u.piles a) (below c (u.piles a).faceUp))).waste = u.waste :=
    setPile_waste u a _
  unfold totalCards
  rw [hv, hF, hstock, hwaste]
  omega

/-- A pair-free reversible letter keeps both seated twins seated. -/
private theorem pairFree_step_seated {u v : State} {x : Card} {m : Move}
    (hstep : State.step u m = some v)
    (hrev : reversibleAtW u m)
    (hno : ¬ IsPairFound x m)
    (hx : seatOf u x ≠ none) (hxt : seatOf u x.twin ≠ none) :
    seatOf v x ≠ none ∧ seatOf v x.twin ≠ none := by
  have hmain : ∀ c, (c = x ∨ c = x.twin) → seatOf u c ≠ none →
      seatOf v c ≠ none := by
    intro c hc hse
    cases m with
    | draw =>
        rw [(chart_draw hstep).1 c]
        exact hse
    | wasteToFound y =>
        exact absurd hrev (wasteToFound_not_reversibleAtW u y)
    | wasteToTab y b =>
        exact absurd hrev (wasteToTab_not_reversibleAtW u y b)
    | tabToFound y =>
        have hno' : NotFoundPair x (Move.tabToFound y) :=
          (notFoundPair_iff_not_isPairFound x (Move.tabToFound y)).mpr hno
        have hyx : y ≠ x := by
          intro h
          exact hno'.1 (by rw [h])
        have hyt : y ≠ x.twin := by
          intro h
          exact hno'.2.1 (by rw [h])
        have hcy : c ≠ y := by
          rcases hc with rfl | rfl
          · exact fun h => hyx h.symm
          · exact fun h => hyt h.symm
        rw [raise_seat_change_of_seated hstep hrev hse hcy]
        exact hse
    | foundToTab y b =>
        obtain ⟨-, -, -, hcp, hs⟩ := step_foundToTab_inv hstep
        have hcp' : (u.setFound y.suit (chop (u.found y.suit))).canPlace y b = true := hcp
        obtain ⟨ap, hap⟩ := mem_faceUp_of_seat_ne_none hse
        have hap' : c ∈ ((u.setFound y.suit (chop (u.found y.suit))).piles ap).faceUp := by
          rw [setFound_piles]
          exact hap
        obtain ⟨a', ha'⟩ := putCard_faceUp_mem_of_mem hcp' hap'
        rw [hs]
        exact seatOf_ne_of_mem_faceUp' ha'
    | tabToTab y b =>
        obtain ⟨asrc, hhold, hcp, hrunne, hs⟩ := step_tabToTab_inv hstep
        let inter : State := u.setPile asrc
          (Pile.afterRunRemoved (u.piles asrc) (below y (u.piles asrc).faceUp))
        let run : List Card := fromCard y (u.piles asrc).faceUp
        have hs' : v = inter.putRun run b := by
          simpa only [inter, run] using hs
        have hmemY : y ∈ (u.piles asrc).faceUp := pileHolding_mem hhold
        have hsplit : below y (u.piles asrc).faceUp ++ run = (u.piles asrc).faceUp := by
          simpa only [run] using tfc_below_fromCard y (u.piles asrc).faceUp
        obtain ⟨ap, hap⟩ := mem_faceUp_of_seat_ne_none hse
        have hsurvive : (∃ ap, c ∈ (inter.piles ap).faceUp) → seatOf v c ≠ none := by
          rintro ⟨ap, hap⟩
          have hinl : ∀ a', b = Sum.inl a' → a' ≠ ap := by
            intro a' hb ha'
            subst hb
            obtain ⟨hemp, -⟩ := canPlace_inl hcp
            have hmem' : c ∈ (inter.piles a').faceUp := by
              rw [ha']
              exact hap
            have hfalse := Pile.isEmpty_eq_false_of_mem hmem'
            have hempty_inter : (inter.piles a').isEmpty = true := by
              by_cases haa : a' = asrc
              · exfalso
                have hfalseY := Pile.isEmpty_eq_false_of_mem hmemY
                rw [haa] at hemp
                rw [hemp] at hfalseY
                exact Bool.noConfusion hfalseY
              · have hpile : inter.piles a' = u.piles a' := by
                  simp only [inter, State.setPile]
                  rw [ite_eq_right haa]
                rw [hpile]
                exact hemp
            rw [hempty_inter] at hfalse
            exact Bool.noConfusion hfalse
          obtain ⟨a', ha'⟩ := putRun_faceUp_mem_of_mem hap hinl
          rw [hs']
          exact seatOf_ne_of_mem_faceUp' ha'
        by_cases hapsrc : ap = asrc
        · rw [hapsrc] at hap
          have hunion : c ∈ below y (u.piles asrc).faceUp ++ run := by
            rwa [← hsplit] at hap
          rcases List.mem_append.mp hunion with hpre | hrun
          · apply hsurvive
            refine ⟨asrc, ?_⟩
            have hpne : below y (u.piles asrc).faceUp ≠ [] := by
              intro hnil
              rw [hnil] at hpre
              exact List.not_mem_nil hpre
            dsimp only [inter, State.setPile]
            rw [ite_eq_left rfl, afterRunRemoved_ne hpne]
            exact hpre
          · cases b with
            | inl a' =>
                rw [hs']
                have hmemv : c ∈ ((inter.putRun run (Sum.inl a')).piles a').faceUp := by
                  rw [putRun_piles_inl_self]
                  exact hrun
                exact seatOf_ne_of_mem_faceUp' hmemv
            | inr z =>
                cases hz : inter.pileOfTop z with
                | some k =>
                    rw [hs']
                    have hmemv : c ∈ ((inter.putRun run (Sum.inr z)).piles k).faceUp := by
                      rw [putRun_piles_inr_self _ _ _ _ hz]
                      exact List.mem_append_right _ hrun
                    exact seatOf_ne_of_mem_faceUp' hmemv
                | none =>
                    exfalso
                    obtain ⟨v', play, hstep', hrun'⟩ := hrev
                    rw [hstep] at hstep'
                    have hv' : v' = v := (Option.some.inj hstep').symm
                    rw [hv'] at hrun'
                    have hle := totalCards_run_le hrun'
                    have hlt : totalCards v < totalCards u :=
                      totalCards_lt_of_tabToTab_noop hhold hs (by
                        show (u.setPile asrc (Pile.afterRunRemoved (u.piles asrc)
                          (below y (u.piles asrc).faceUp))).pileOfTop z = none
                        simpa only [inter] using hz)
                    omega
        · apply hsurvive
          refine ⟨ap, ?_⟩
          have hpile : inter.piles ap = u.piles ap := by
            dsimp only [inter, State.setPile]
            rw [ite_eq_right hapsrc]
          rw [hpile]
          exact hap
  exact ⟨hmain x (Or.inl rfl) hx, hmain x.twin (Or.inr rfl) hxt⟩

/-- Pair-free reversible plays preserve both twins' seats. -/
private theorem pairFree_play_seated_aux {x : Card} :
    ∀ {s w : State} {play : List Move},
      ShufflePlayW s play w →
      (∀ m ∈ play, ¬ IsPairFound x m) →
      (∃ b, seatOf s x = some b) →
      (∃ b, seatOf s x.twin = some b) →
      (∃ b, seatOf w x = some b) ∧ (∃ b, seatOf w x.twin = some b) := by
  intro s w play hplay
  induction hplay with
  | nil st =>
      intro hno hx hxt
      exact ⟨hx, hxt⟩
  | @cons st s₁ W m ρ hrev hstep hrest ih =>
      intro hno hx hxt
      have hxne : seatOf st x ≠ none := by
        obtain ⟨b, hb⟩ := hx
        rw [hb]
        simp
      have hxtne : seatOf st x.twin ≠ none := by
        obtain ⟨b, hb⟩ := hxt
        rw [hb]
        simp
      have hstepres := pairFree_step_seated hstep hrev (hno m (by simp)) hxne hxtne
      have hx₁ : ∃ b, seatOf s₁ x = some b := option_some_of_ne_none hstepres.1
      have hxt₁ : ∃ b, seatOf s₁ x.twin = some b := option_some_of_ne_none hstepres.2
      exact ih (fun n hn => hno n (List.mem_cons_of_mem m hn)) hx₁ hxt₁

end DetourKit

/-- A pair-free reversible play preserves both seated twins. -/
theorem pairFree_play_seated {s w : State} {x : Card} {play : List Move}
    (hplay : ShufflePlayW s play w)
    (hno : ∀ m ∈ play, ¬ IsPairFound x m)
    (hx : ∃ b, seatOf s x = some b) (hxt : ∃ b, seatOf s x.twin = some b) :
    (∃ b, seatOf w x = some b) ∧ (∃ b, seatOf w x.twin = some b) :=
  DetourKit.pairFree_play_seated_aux hplay hno hx hxt

#print axioms exists_pairFound_split
#print axioms pairFree_play_seated

