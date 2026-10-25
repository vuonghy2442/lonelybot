import Orig2.TwinAbstract7L
import Orig2.TwinPreludePath
import Orig2.TwinSwapRecipe
import Orig2.TwinSpliceUnique

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Temp/TwinAbstractLadder — the abstract rider-ladder twin-swap block

The 5L and 7L cards prove the one-rider and two-rider both-covered
blocks: raise the riders top-down, run the frozen 3-leg recipe at the
exposed `x`, then pull the riders back bottom-up onto their original
parents.  Every rider's `seatOf` parent is unchanged, so the endpoint
is the strict twin swap of `x` / `x.twin`.

This card runs the same pattern over an arbitrary bottom-to-top rider
stack.  `RiderChain s x ys` records that the first entry of `ys` sits
on `x`, the second on the first, and so on.  `ladderPlay` raises the
stack from the top, runs `[raise x, slide x.twin onto z, pull x onto
z.twin]`, and pulls the stack back from the bottom.

The proof is a reverse induction over the stack.  The top rider `y` is
split off as `l ++ [y]`; its raise and final pull bracket the inner
ladder, which is the induction hypothesis at the after-raise state.
The bracket composition only touches the rider `y`, so the strict
fields of the inner ladder compose with the two one-step footprints.

Zero `sorry`, zero `Classical.choice`.
-/

open State
open TwinSpliceComm

/-! ## §0. Walk and seat-footprint helpers -/


/-- Expose the first step of a walk. -/
private theorem walk_cons_inv {P : State → Move → Prop}
    {st s' : State} {m : Move} {ρ : List Move}
    (h : Walk P st (m :: ρ) s') :
    ∃ s1, P st m ∧ State.step st m = some s1 ∧ Walk P s1 ρ s' := by
  cases h with
  | cons hlet hstep hrest => exact ⟨_, hlet, hstep, hrest⟩

/-- Split a walk at an append. -/
private theorem walk_append_inv {P : State → Move → Prop} :
    ∀ {l₁ l₂ : List Move} {s w : State}, Walk P s (l₁ ++ l₂) w →
      ∃ u, Walk P s l₁ u ∧ Walk P u l₂ w := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ s w h
      exact ⟨s, Walk.nil s, by simpa using h⟩
  | cons m ms ih =>
      intro l₂ s w h
      obtain ⟨s1, hlet, hstep, hrest⟩ := walk_cons_inv h
      obtain ⟨u, h1, h2⟩ := ih hrest
      exact ⟨u, Walk.cons hlet hstep h1, h2⟩

/-- A raise changes the seat of every card other than its mover. -/
private theorem raise_seat_change_all {u v : State} {d c : Card}
    (hwf : u.WF) (hstep : State.step u (Move.tabToFound d) = some v)
    (hrev : reversibleAtW u (Move.tabToFound d)) (hcd : c ≠ d) :
    seatOf v c = seatOf u c := by
  by_cases hnone : seatOf u c = none
  · obtain ⟨-, a, hpa, -⟩ := step_tabToFound_inv hstep
    rw [raise_seat_none hwf hstep hrev hpa hnone hcd, hnone]
  · exact raise_seat_change_of_seated hstep hrev hnone hcd

/-- A card seated on a card parent is exactly one rank above it. -/
private theorem seatOf_inr_rank {s : State} (hwf : s.WF) {c p : Card}
    (h : seatOf s c = some (Sum.inr p)) :
    c.rank.toIdx + 1 = p.rank.toIdx := by
  obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr h
  exact ((canSitOn_eq c p).mp (tfc_seat_parent hwf hhold hlast).1).1

/-! ## §1. The rider chain and the ladder play -/

/-- **`RiderChain s x ys`** — the stack `ys`, written bottom-to-top:
the first rider sits on `x`, the next on the first, and so on. -/
def RiderChain (s : State) (x : Card) : List Card → Prop
  | [] => True
  | y :: ys => seatOf s y = some (Sum.inr x) ∧ RiderChain s y ys

/-- The head of a list, with a fallback for the empty list. -/
def topOr (d : Card) : List Card → Card
  | [] => d
  | c :: _ => c

/-- **`ladderPlayRev x z rev`** — the ladder play for a stack written
top-to-bottom (`rev`), with the 3-leg recipe at the bottom.  The top
rider is raised, the play recurses on the riders below it, and the top
rider is pulled back onto the head of the remaining stack. -/
def ladderPlayRev (x z : Card) : List Card → List Move
  | [] =>
      [Move.tabToFound x, Move.tabToTab x.twin (Sum.inr z),
        Move.foundToTab x (Sum.inr z.twin)]
  | y :: ys =>
      Move.tabToFound y ::
        (ladderPlayRev x z ys ++
          [Move.foundToTab y (Sum.inr (topOr x ys))])

/-- **`ladderPlay x z ys`** — the ladder play for a bottom-to-top stack
`ys`.  Raising the stack is top-down; the final pulls are bottom-up. -/
def ladderPlay (x z : Card) (ys : List Card) : List Move :=
  ladderPlayRev x z ys.reverse

/-- The recursive step of `ladderPlay` at a bottom-to-top stack
`l ++ [y]`: the top rider `y` is raised first and pulled last. -/
theorem ladderPlay_append_singleton (x z : Card) (l : List Card) (y : Card) :
    ladderPlay x z (l ++ [y]) =
      Move.tabToFound y ::
        (ladderPlay x z l ++
          [Move.foundToTab y (Sum.inr (topOr x l.reverse))]) := by
  simp [ladderPlay, ladderPlayRev, List.reverse_append]

/-- Head of an append-to-singleton. -/
private theorem topOr_append_singleton (d : Card) (l : List Card) (c : Card) :
    topOr d (l ++ [c]) = topOr c l := by
  cases l with
  | nil => rfl
  | cons q qs => rfl

/-- Split the chain at its top rider. -/
private theorem riderChain_append_singleton {s : State} {x y : Card} {l : List Card}
    (h : RiderChain s x (l ++ [y])) :
    RiderChain s x l ∧ seatOf s y = some (Sum.inr (topOr x l.reverse)) := by
  induction l generalizing x with
  | nil =>
      simpa [RiderChain, topOr] using h
  | cons p ps ih =>
      obtain ⟨hp, hrest⟩ := h
      obtain ⟨hchain, hy⟩ := ih (x := p) hrest
      refine ⟨⟨hp, hchain⟩, ?_⟩
      rw [List.reverse_cons, topOr_append_singleton]
      exact hy

/-- Ranks strictly decrease upward along a rider chain. -/
private theorem riderChain_ranks {s : State} (hwf : s.WF) :
    ∀ {x : Card} {ys : List Card}, RiderChain s x ys →
      (∀ c ∈ ys, c.rank.toIdx < x.rank.toIdx) ∧
      ys.Pairwise (fun a b => b.rank.toIdx < a.rank.toIdx) := by
  intro x ys h
  induction ys generalizing x with
  | nil => simp
  | cons y ys ih =>
      obtain ⟨hxy, hrest⟩ := h
      obtain ⟨ihgt, ihpw⟩ := ih hrest
      have hlt : y.rank.toIdx < x.rank.toIdx := by
        have h1 := seatOf_inr_rank hwf hxy
        omega
      refine ⟨?_, List.Pairwise.cons ?_ ihpw⟩
      · intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hlt
        · exact Nat.lt_trans (ihgt c hc) hlt
      · intro b hb
        exact ihgt b hb

/-- The rank-decreasing order is irreflexive, so a chain is a nodup list. -/
private theorem pairwise_rank_nodup {l : List Card}
    (h : l.Pairwise (fun a b => b.rank.toIdx < a.rank.toIdx)) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a l ih =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp h
      rw [List.nodup_cons]
      refine ⟨?_, ih htail⟩
      intro ha
      exact Nat.lt_irrefl _ (hhead a ha)

/-- A rider chain at a WF state is a nodup list. -/
private theorem riderChain_nodup {s : State} (hwf : s.WF) {x : Card} {ys : List Card}
    (h : RiderChain s x ys) : ys.Nodup :=
  pairwise_rank_nodup (riderChain_ranks hwf h).2

/-- Raising a card outside the chain leaves the chain intact. -/
private theorem riderChain_raise_other {s s1 : State} {y x : Card} {l : List Card}
    (hwf : s.WF) (hstep : State.step s (Move.tabToFound y) = some s1)
    (hrev : reversibleAtW s (Move.tabToFound y)) (hyl : y ∉ l)
    (h : RiderChain s x l) : RiderChain s1 x l := by
  induction l generalizing x with
  | nil => trivial
  | cons c cs ih =>
      have hyc : y ≠ c := fun h => hyl (List.mem_cons.mpr (Or.inl h))
      have hycs : y ∉ cs := fun hm => hyl (List.mem_cons.mpr (Or.inr hm))
      obtain ⟨hc, hcs⟩ := h
      refine ⟨?_, ih hycs hcs⟩
      rw [raise_seat_change_all hwf hstep hrev (Ne.symm hyc)]
      exact hc

/-! ## §2. The 3-leg base recipe -/

/-- **The mirror 3-leg recipe is a strict twin swap.**  `x` is raised,
`x.twin` slides onto `x`'s vacated parent `z`, and `x` is pulled onto
`x.twin`'s vacated parent `z.twin`. -/
private theorem twinPairSwapStrict_recipe3
    {s w : State} {x z : Card}
    (hwf : s.WF) (_hwf' : w.WF)
    (hx : seatOf s x = some (Sum.inr z))
    (hxt : seatOf s x.twin = some (Sum.inr z.twin))
    (hplay : ShufflePlayW s
      [Move.tabToFound x, Move.tabToTab x.twin (Sum.inr z),
        Move.foundToTab x (Sum.inr z.twin)] w) :
    twinPairSwapStrict s w x := by
  -- §2.0 Expose the three steps.
  obtain ⟨s1, hrev1, hstep1, rest1⟩ := walk_cons_inv hplay
  obtain ⟨s2, hrev2, hstep2, rest2⟩ := walk_cons_inv rest1
  obtain ⟨s3, hrev3, hstep3, rest3⟩ := walk_cons_inv rest2
  have h3w : s3 = w :=
    Option.some.inj (by simpa [State.run] using Walk_run _ rest3)
  subst s3
  have hwf1 : s1.WF := step_wf hwf hstep1
  have hwf2 : s2.WF := step_wf hwf1 hstep2
  -- §2.1 Step inversions.
  obtain ⟨-, a1, hpa1, hs1⟩ := step_tabToFound_inv hstep1
  obtain ⟨a2, hhold2, hcp2, hfr2, hs2⟩ := step_tabToTab_inv hstep2
  obtain ⟨c3, htop3, hc3, hcp3, hs3⟩ := step_foundToTab_inv hstep3
  subst c3
  -- §2.2 The two exchanged seats.
  have hs1_xt : seatOf s1 x.twin = some (Sum.inr z.twin) :=
    (raise_seat_change_of_seated hstep1 hrev1 (by rw [hxt]; simp)
      (card_twin_ne x)).trans hxt
  have hs2_x : seatOf s2 x = none := by
    rw [tfc_seat_point_edit hwf1 hstep2 hrev2 x]
    rw [ite_eq_right (fun h => card_twin_ne x h.symm)]
    exact seatOf_tabToFound_mover_none hwf hstep1
  have hs2_xt : seatOf s2 x.twin = some (Sum.inr z) := by
    rw [tfc_seat_point_edit hwf1 hstep2 hrev2 x.twin, ite_eq_left rfl]
  have hw_x : seatOf w x = some (Sum.inr z.twin) :=
    seatOf_foundToTab_mover hwf2 hstep3
  have hw_xt : seatOf w x.twin = some (Sum.inr z) :=
    (pull_seat_change hstep3 x.twin (card_twin_ne x)).trans hs2_xt
  -- §2.3 Every other seat is unchanged.
  have hother : ∀ c, c ≠ x → c ≠ x.twin → seatOf w c = seatOf s c := by
    intro c hcx hcxt
    have h1 : seatOf s1 c = seatOf s c :=
      raise_seat_change_all hwf hstep1 hrev1 hcx
    have h2 : seatOf s2 c = seatOf s1 c := by
      rw [tfc_seat_point_edit hwf1 hstep2 hrev2 c]
      rw [ite_eq_right hcxt]
    have h3 : seatOf w c = seatOf s2 c := pull_seat_change hstep3 c hcx
    rw [h3, h2, h1]
  -- §2.4 The fixed readouts.
  have hhidden : boardFixed s w := by
    refine ⟨?_, ?_⟩
    · intro a
      have h1 := hidden_eq_of_rev_step hwf hstep1 hrev1 a
      have h2 := hidden_eq_of_rev_step hwf1 hstep2 hrev2 a
      have h3 := hidden_eq_of_rev_step hwf2 hstep3 hrev3 a
      exact h1.symm.trans (h2.symm.trans h3.symm)
    · have hd1 : s1.drawStep = s.drawStep := by rw [hs1]; rfl
      have hd2 : s2.drawStep = s1.drawStep := by
        rw [hs2, putRun_drawStep, setPile_drawStep]
      have hd3 : w.drawStep = s2.drawStep := by
        rw [hs3, putCard_drawStep, setFound_drawStep]
      exact hd1.symm.trans (hd2.symm.trans hd3.symm)
  have hf1_self : s1.found x.suit = s.found x.suit ++ [x] := by
    rw [hs1]; exact setFound_found_self
  have hf1_other : ∀ σ, σ ≠ x.suit → s1.found σ = s.found σ := by
    intro σ hσ
    rw [hs1]; exact setFound_found_ne hσ
  have hf2 : s2.found = s1.found := by
    rw [hs2, putRun_found, setPile_found]
  have hf3_self : w.found x.suit = chop (s2.found x.suit) := by
    rw [hs3, putCard_found]; exact setFound_found_self
  have hf3_other : ∀ σ, σ ≠ x.suit → w.found σ = s2.found σ := by
    intro σ hσ
    rw [hs3, putCard_found]; exact setFound_found_ne hσ
  have hfound : foundsFixed s w := by
    intro σ
    by_cases hσ : σ = x.suit
    · subst σ
      rw [hf3_self, hf2, hf1_self, chop_snoc]
    · rw [hf3_other σ hσ, hf2, hf1_other σ hσ]
  have hstock1 : s1.stock = s.stock := by rw [hs1]; rfl
  have hstock2 : s2.stock = s1.stock := by rw [hs2, putRun_stock, setPile_stock]
  have hstock3 : w.stock = s2.stock := by rw [hs3, putCard_stock, setFound_stock]
  have hstock : s.stock = w.stock :=
    hstock1.symm.trans (hstock2.symm.trans hstock3.symm)
  have hwaste1 : s1.waste = s.waste := by rw [hs1]; rfl
  have hwaste2 : s2.waste = s1.waste := by rw [hs2, putRun_waste, setPile_waste]
  have hwaste3 : w.waste = s2.waste := by rw [hs3, putCard_waste, setFound_waste]
  have hwaste : s.waste = w.waste :=
    hwaste1.symm.trans (hwaste2.symm.trans hwaste3.symm)
  -- §2.5 Assemble the strict letter.
  refine ⟨?_, ?_, hother, hhidden, hfound, hstock, hwaste, ?_⟩
  · rw [hw_x, hxt]
  · rw [hw_xt, hx]
  · unfold cutOf
    rw [hstock]

/-! ## §3. The bracket: raise the top rider, ladder, pull it back -/

/-- **The bracket step.**  If the top rider `y` is raised off `p`, an
inner strict twin swap of `x` runs, and `y` is pulled back onto `p`,
the composite is a strict twin swap of `x` from the original state. -/
private theorem twinPairSwapStrict_bracket
    {s s1 u w : State} {x y p z : Card}
    (hwf : s.WF)
    (huwf : u.WF)
    (hx : seatOf s x = some (Sum.inr z))
    (hxt : seatOf s x.twin = some (Sum.inr z.twin))
    (hy : seatOf s y = some (Sum.inr p))
    (hyx : y ≠ x) (hyt : y ≠ x.twin)
    (hstep1 : State.step s (Move.tabToFound y) = some s1)
    (hrev1 : reversibleAtW s (Move.tabToFound y))
    (hstrict : twinPairSwapStrict s1 u x)
    (hstep2 : State.step u (Move.foundToTab y (Sum.inr p)) = some w)
    (hrev2 : reversibleAtW u (Move.foundToTab y (Sum.inr p))) :
    twinPairSwapStrict s w x := by
  obtain ⟨hst1x, hst1xt, hst1other, hst1board, hst1found, hst1stock,
    hst1waste, hst1cut⟩ := hstrict
  obtain ⟨_hn1, a1, hpa1, hshape1⟩ := step_tabToFound_inv hstep1
  obtain ⟨c2, htop2, hc2, hcp2, hshape2⟩ := step_foundToTab_inv hstep2
  have hx1 : seatOf s1 x = seatOf s x :=
    raise_seat_change_all hwf hstep1 hrev1 hyx.symm
  have hxt1 : seatOf s1 x.twin = seatOf s x.twin :=
    raise_seat_change_all hwf hstep1 hrev1 hyt.symm
  -- §3.1 The two exchanged seats.
  have hw_x : seatOf w x = seatOf s x.twin := by
    calc
      seatOf w x = seatOf u x := pull_seat_change hstep2 x (Ne.symm hyx)
      _ = seatOf s1 x.twin := hst1x
      _ = seatOf s x.twin := hxt1
  have hw_xt : seatOf w x.twin = seatOf s x := by
    calc
      seatOf w x.twin = seatOf u x.twin :=
        pull_seat_change hstep2 x.twin (Ne.symm hyt)
      _ = seatOf s1 x := hst1xt
      _ = seatOf s x := hx1
  -- §3.2 Every other seat is unchanged; the rider itself round-trips.
  have hother : ∀ c, c ≠ x → c ≠ x.twin → seatOf w c = seatOf s c := by
    intro c hcx hcxt
    by_cases hcy : c = y
    · subst c
      rw [seatOf_foundToTab_mover huwf hstep2, hy]
    · calc
        seatOf w c = seatOf u c := pull_seat_change hstep2 c hcy
        _ = seatOf s1 c := hst1other c hcx hcxt
        _ = seatOf s c := raise_seat_change_all hwf hstep1 hrev1 hcy
  -- §3.3 The fixed readouts.
  have hhidden : ∀ a, (s.piles a).hidden = (w.piles a).hidden := by
    intro a
    have h1 : (s1.piles a).hidden = (s.piles a).hidden :=
      hidden_eq_of_rev_step hwf hstep1 hrev1 a
    have h2 : (s1.piles a).hidden = (u.piles a).hidden := hst1board.1 a
    have h3 : (w.piles a).hidden = (u.piles a).hidden :=
      hidden_eq_of_rev_step huwf hstep2 hrev2 a
    exact h1.symm.trans (h2.trans h3.symm)
  have hd1 : s1.drawStep = s.drawStep := by rw [hshape1]; rfl
  have hd2 : w.drawStep = u.drawStep := by
    rw [hshape2, putCard_drawStep, setFound_drawStep]
  have hdraw : s.drawStep = w.drawStep :=
    hd1.symm.trans (hst1board.2.trans hd2.symm)
  have hf1_self : s1.found y.suit = s.found y.suit ++ [y] := by
    rw [hshape1]; exact setFound_found_self
  have hf1_other : ∀ σ, σ ≠ y.suit → s1.found σ = s.found σ := by
    intro σ hσ
    rw [hshape1]; exact setFound_found_ne hσ
  have hf2_self : w.found y.suit = chop (u.found y.suit) := by
    rw [hshape2, putCard_found]; exact setFound_found_self
  have hf2_other : ∀ σ, σ ≠ y.suit → w.found σ = u.found σ := by
    intro σ hσ
    rw [hshape2, putCard_found]; exact setFound_found_ne hσ
  have hfound : foundsFixed s w := by
    intro σ
    by_cases hσ : σ = y.suit
    · subst σ
      rw [hf2_self, ← hst1found y.suit, hf1_self, chop_snoc]
    · rw [hf2_other σ hσ, ← hst1found σ, hf1_other σ hσ]
  have hs1_stock : s1.stock = s.stock := by rw [hshape1]; rfl
  have hw_stock : w.stock = u.stock := by
    rw [hshape2, putCard_stock, setFound_stock]
  have hstock : s.stock = w.stock :=
    hs1_stock.symm.trans (hst1stock.trans hw_stock.symm)
  have hs1_waste : s1.waste = s.waste := by rw [hshape1]; rfl
  have hw_waste : w.waste = u.waste := by
    rw [hshape2, putCard_waste, setFound_waste]
  have hwaste : s.waste = w.waste :=
    hs1_waste.symm.trans (hst1waste.trans hw_waste.symm)
  -- §3.4 Assemble.
  refine ⟨hw_x, hw_xt, hother, ⟨hhidden, hdraw⟩, hfound, hstock, hwaste, ?_⟩
  unfold cutOf
  rw [hstock]

/-! ## §4. The general ladder -/

/-- **The abstract rider-ladder endpoint.**  From a WF state where `x`
sits on `z` and `x.twin` on `z.twin`, with the bottom-to-top rider
stack `ys` above `x`, the ladder play raises the stack top-down, runs
the 3-leg recipe, and pulls the stack bottom-up; the endpoint is the
strict twin swap of `x` / `x.twin`. -/
theorem twinPairSwapStrict_abstractLadder
    {s w : State} {x z : Card} {ys : List Card}
    (hwf : s.WF) (hwf' : w.WF)
    (hx : seatOf s x = some (Sum.inr z))
    (hxt : seatOf s x.twin = some (Sum.inr z.twin))
    (hchain : RiderChain s x ys)
    (hplay : ShufflePlayW s (ladderPlay x z ys) w) :
    twinPairSwapStrict s w x := by
  -- Reverse induction on the stack.
  let P : List Card → Prop := fun ys =>
    ∀ (s w : State) (x z : Card),
      s.WF → w.WF →
      seatOf s x = some (Sum.inr z) →
      seatOf s x.twin = some (Sum.inr z.twin) →
      RiderChain s x ys →
      ShufflePlayW s (ladderPlay x z ys) w →
      twinPairSwapStrict s w x
  have hP : ∀ ys, P ys := by
    intro ys
    have hrev : ∀ r : List Card, P r.reverse := by
      intro r
      induction r with
      | nil =>
          intro s w x z hwf hwf' hx hxt hchain hplay
          exact twinPairSwapStrict_recipe3 hwf hwf' hx hxt
            (by simpa [ladderPlay, ladderPlayRev] using hplay)
      | cons y rest ih =>
          intro s w x z hwf hwf' hx hxt hchain hplay
          -- The stack under the goal is `(y :: rest).reverse = rest.reverse ++ [y]`.
          have hchain' : RiderChain s x (rest.reverse ++ [y]) := by
            simpa [List.reverse_cons] using hchain
          have hplay0 : ShufflePlayW s (ladderPlay x z (rest.reverse ++ [y])) w := by
            simpa [List.reverse_cons] using hplay
          obtain ⟨hchain_l, hy⟩ :=
            riderChain_append_singleton (l := rest.reverse) hchain'
          have hy' : seatOf s y = some (Sum.inr (topOr x rest)) := by
            simpa [List.reverse_reverse] using hy
          -- Split the top rider `y` off.
          have hplay' : ShufflePlayW s
              (Move.tabToFound y ::
                (ladderPlay x z rest.reverse ++
                  [Move.foundToTab y (Sum.inr (topOr x rest))])) w := by
            have hdecomp := ladderPlay_append_singleton x z rest.reverse y
            have hdecomp' : ladderPlay x z (rest.reverse ++ [y]) =
                Move.tabToFound y ::
                  (ladderPlay x z rest.reverse ++
                    [Move.foundToTab y (Sum.inr (topOr x rest))]) := by
              simpa [List.reverse_reverse] using hdecomp
            rw [hdecomp'] at hplay0
            exact hplay0
          obtain ⟨s1, hrev1, hstep1, rest1⟩ := walk_cons_inv hplay'
          obtain ⟨u, hinner, hpost⟩ :=
            walk_append_inv (l₁ := ladderPlay x z rest.reverse)
              (l₂ := [Move.foundToTab y (Sum.inr (topOr x rest))]) rest1
          have hwf1 : s1.WF := step_wf hwf hstep1
          have huwf : u.WF := run_wf hwf1 (Walk_run _ hinner)
          -- The ranks separate `y` from the pair.
          have hlt : y.rank.toIdx < x.rank.toIdx :=
            (riderChain_ranks hwf hchain').1 y
              (List.mem_append_right _ (List.mem_singleton.mpr rfl))
          have hyx : y ≠ x := by
            intro h
            rw [h] at hlt
            exact Nat.lt_irrefl _ hlt
          have hyt : y ≠ x.twin := by
            intro h
            rw [h] at hlt
            have hrank : x.twin.rank = x.rank := rfl
            rw [hrank] at hlt
            exact Nat.lt_irrefl _ hlt
          have hnodup : (rest.reverse ++ [y]).Nodup :=
            riderChain_nodup hwf hchain'
          have hyl : y ∉ rest.reverse := by
            intro hyrest
            have hdisj := (List.nodup_append.mp hnodup).2.2
            exact (hdisj y hyrest y (List.mem_singleton.mpr rfl)) rfl
          have hchain_s1 : RiderChain s1 x rest.reverse :=
            riderChain_raise_other hwf hstep1 hrev1 hyl hchain_l
          have hx1 : seatOf s1 x = some (Sum.inr z) := by
            rw [raise_seat_change_all hwf hstep1 hrev1 hyx.symm]; exact hx
          have hxt1 : seatOf s1 x.twin = some (Sum.inr z.twin) := by
            rw [raise_seat_change_all hwf hstep1 hrev1 hyt.symm]; exact hxt
          -- The induction hypothesis at the after-raise state.
          have hmid : twinPairSwapStrict s1 u x :=
            ih s1 u x z hwf1 huwf hx1 hxt1 hchain_s1 hinner
          -- The final one-step pull.
          obtain ⟨w1, hrev2, hstep2, rest2⟩ := walk_cons_inv hpost
          have hw1 : w1 = w :=
            Option.some.inj (by simpa [State.run] using Walk_run _ rest2)
          subst w1
          exact twinPairSwapStrict_bracket hwf huwf hx hxt hy' hyx hyt
            hstep1 hrev1 hmid hstep2 hrev2
    simpa [List.reverse_reverse] using hrev ys.reverse
  exact hP ys s w x z hwf hwf' hx hxt hchain hplay

/-- **The abstract rider-ladder `SelfSwapSeg`.**  The strict endpoint
feeds `selfSwapSeg_of_strict`; the recorded segment is `ladderPlay`. -/
theorem selfSwapSeg_abstractLadder
    {s w : State} {x z : Card} {ys : List Card}
    (hwf : s.WF) (hwf' : w.WF)
    (hx : seatOf s x = some (Sum.inr z))
    (hxt : seatOf s x.twin = some (Sum.inr z.twin))
    (hchain : RiderChain s x ys)
    (hplay : ShufflePlayW s (ladderPlay x z ys) w) :
    SelfSwapSeg x s w (ladderPlay x z ys) :=
  selfSwapSeg_of_strict hwf hwf' ⟨z, hx⟩ ⟨z, hxt⟩
    (twinPairSwapStrict_abstractLadder hwf hwf' hx hxt hchain hplay) hplay

#print axioms twinPairSwapStrict_abstractLadder
#print axioms selfSwapSeg_abstractLadder
