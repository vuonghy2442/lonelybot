import Orig2.TwinPointFunctor
import Orig2.TwinSpliceUnique
import Orig2.TwinEquivariance
import Orig2.DetourKit

set_option linter.unusedSectionVars false

namespace Move

def relabelMover (x : Card) : Move → Move
  | .draw => .draw
  | .wasteToFound c => .wasteToFound (Card.relabelTwin x c)
  | .wasteToTab c b => .wasteToTab (Card.relabelTwin x c) b
  | .tabToFound c => .tabToFound (Card.relabelTwin x c)
  | .foundToTab c b => .foundToTab (Card.relabelTwin x c) b
  | .tabToTab c b => .tabToTab (Card.relabelTwin x c) b

end Move

open State

namespace TwinSpliceComm

def sufOf (c : Card) (l : List Card) : List Card := (fromCard c l).tail

theorem fromCard_cons_suf {c : Card} {l : List Card} (hmem : c ∈ l) :
    fromCard c l = c :: sufOf c l := by
  obtain ⟨r, hr⟩ := tfc_fromCard_cons_head (c := c) l hmem
  unfold sufOf
  rw [hr]
  rfl

theorem fromCard_append_not_mem {c : Card} : ∀ (A B : List Card), c ∉ A →
    fromCard c (A ++ B) = fromCard c B := by
  intro A
  induction A with
  | nil => intro B _; rfl
  | cons u t ih =>
      intro B hc
      have hat : c ∉ t := fun h => hc (List.mem_cons_of_mem u h)
      have huc : u ≠ c := fun h => hc (List.mem_cons.mpr (Or.inl h.symm))
      rw [List.cons_append, tfc_fromCard_cons, ite_eq_right huc, ih B hat]

theorem fromCard_append_of_mem {c : Card} : ∀ (A B : List Card), c ∈ A →
    fromCard c (A ++ B) = fromCard c A ++ B := by
  intro A
  induction A with
  | nil => intro B h; cases h
  | cons u t ih =>
      intro B h
      by_cases huc : u = c
      · subst huc
        simp only [List.cons_append]
        rw [tfc_fromCard_cons, ite_eq_left rfl, tfc_fromCard_cons, ite_eq_left rfl]
        rfl
      · have hat : c ∈ t := by
          rcases List.mem_cons.mp h with h | h
          · exact absurd h.symm huc
          · exact h
        simp only [List.cons_append]
        rw [tfc_fromCard_cons, ite_eq_right huc, tfc_fromCard_cons, ite_eq_right huc,
          ih B hat]

theorem below_eq_self_of_not_mem {c : Card} : ∀ {l : List Card}, c ∉ l → below c l = l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons u t ih =>
      intro h
      have hat : c ∉ t := fun hc => h (List.mem_cons_of_mem u hc)
      have huc : u ≠ c := fun hc => h (List.mem_cons.mpr (Or.inl hc.symm))
      rw [below_cons, ite_eq_right huc, ih hat]

theorem below_append_cons {c : Card} (P S : List Card) (hP : c ∉ P) :
    below c (P ++ c :: S) = P := by
  have hb := (tfc_below_fromCard_excl c P (c :: S) hP).1
  rw [hb, below_cons, ite_eq_left rfl, List.append_nil]

theorem fromCard_append_cons {c : Card} (P S : List Card) (hP : c ∉ P) :
    fromCard c (P ++ c :: S) = c :: S := by
  have hf := (tfc_below_fromCard_excl c P (c :: S) hP).2
  rw [hf, tfc_fromCard_cons, ite_eq_left rfl]

theorem below_append_eq {c : Card} {A B : List Card} (h : c ∉ A) :
    below c (A ++ B) = A ++ below c B :=
  (tfc_below_fromCard_excl c A B h).1

theorem runOK_rank_distinct {l : List Card} (hok : runOK l = true)
    {u v : Card} (hu : u ∈ l) (hv : v ∈ l) (hr : u.rank = v.rank) : u = v := by
  induction l with
  | nil => cases hu
  | cons c t ih =>
      cases t with
      | nil =>
          rw [List.mem_singleton] at hu hv
          rw [hu, hv]
      | cons d t' =>
          have hok' : runOK (d :: t') = true := runOK_cons_tail hok
          rcases List.mem_cons.mp hu with rfl | hu'
          · rcases List.mem_cons.mp hv with rfl | hv'
            · rfl
            · have hlt := runOK_head_gt hok hv'
              have hidx : u.rank.toIdx = v.rank.toIdx := congrArg Rank.toIdx hr
              omega
          · rcases List.mem_cons.mp hv with rfl | hv'
            · have hlt := runOK_head_gt hok hu'
              have hidx : u.rank.toIdx = v.rank.toIdx := congrArg Rank.toIdx hr
              omega
            · exact ih hok' hu' hv'

theorem run_split_disjoint {l : List Card} (hok : runOK l = true)
    {c y : Card} (hyP : y ∈ below c l) (hyR : y ∈ fromCard c l) : False := by
  have hrun : runOK (below c l ++ fromCard c l) = true := by
    rw [tfc_below_fromCard c l]
    exact hok
  have hlt := runOK_desc hrun hyP hyR
  omega

section SpliceSetup

variable (s : State) (x : Card) (a b : Anchor)

def preA : List Card := below x (s.piles a).faceUp
def sufA : List Card := sufOf x (s.piles a).faceUp
def preB : List Card := below x.twin (s.piles b).faceUp
def sufB : List Card := sufOf x.twin (s.piles b).faceUp

end SpliceSetup

section Splice

variable {s : State} {x : Card} {a b : Anchor}

theorem faceUp_A (ha : s.pileHolding x = some a) :
    (s.piles a).faceUp = preA s x a ++ x :: sufA s x a := by
  have hmem : x ∈ (s.piles a).faceUp := pileHolding_mem ha
  have hsplit := tfc_below_fromCard x (s.piles a).faceUp
  have hfc := fromCard_cons_suf hmem
  calc
    (s.piles a).faceUp = below x (s.piles a).faceUp ++ fromCard x (s.piles a).faceUp :=
      hsplit.symm
    _ = below x (s.piles a).faceUp ++ x :: sufOf x (s.piles a).faceUp := by rw [hfc]
    _ = preA s x a ++ x :: sufA s x a := rfl

theorem faceUp_B (hb : s.pileHolding x.twin = some b) :
    (s.piles b).faceUp = preB s x b ++ x.twin :: sufB s x b := by
  have hmem : x.twin ∈ (s.piles b).faceUp := pileHolding_mem hb
  have hsplit := tfc_below_fromCard x.twin (s.piles b).faceUp
  have hfc := fromCard_cons_suf hmem
  calc
    (s.piles b).faceUp =
        below x.twin (s.piles b).faceUp ++ fromCard x.twin (s.piles b).faceUp :=
      hsplit.symm
    _ = below x.twin (s.piles b).faceUp ++ x.twin :: sufOf x.twin (s.piles b).faceUp := by
      rw [hfc]
    _ = preB s x b ++ x.twin :: sufB s x b := rfl

theorem splice_piles_a_nf (ha : s.pileHolding x = some a)
    (hb : s.pileHolding x.twin = some b) (hab : a ≠ b) :
    (s.spliceTwinRuns x).piles a =
      { hidden := (s.piles a).hidden
        faceUp := preA s x a ++ x.twin :: sufB s x b } := by
  rw [spliceTwinRuns_piles_self ha hb hab, faceUp_A ha, faceUp_B hb]
  rw [below_append_cons (preA s x a) (sufA s x a)
        (by simpa [preA] using tfc_below_not_mem_self x (s.piles a).faceUp)]
  rw [fromCard_append_cons (preB s x b) (sufB s x b)
        (by simpa [preB] using tfc_below_not_mem_self x.twin (s.piles b).faceUp)]

theorem splice_piles_b_nf (ha : s.pileHolding x = some a)
    (hb : s.pileHolding x.twin = some b) (hab : a ≠ b) :
    (s.spliceTwinRuns x).piles b =
      { hidden := (s.piles b).hidden
        faceUp := preB s x b ++ x :: sufA s x a } := by
  rw [spliceTwinRuns_piles_second ha hb hab, faceUp_A ha, faceUp_B hb]
  rw [below_append_cons (preB s x b) (sufB s x b)
        (by simpa [preB] using tfc_below_not_mem_self x.twin (s.piles b).faceUp)]
  rw [fromCard_append_cons (preA s x a) (sufA s x a)
        (by simpa [preA] using tfc_below_not_mem_self x (s.piles a).faceUp)]

end Splice

/-- Every card of `fromCard c l` has rank at most `c` in a legal run. -/
theorem runOK_fromCard_le : ∀ {l : List Card} {c y : Card},
    runOK l = true → y ∈ fromCard c l → y.rank.toIdx ≤ c.rank.toIdx := by
  intro l
  induction l with
  | nil => intro c y _ hmem; exact absurd hmem (by simp [fromCard])
  | cons u t ih =>
      intro c y hok hmem
      rw [fromCard] at hmem
      split at hmem
      · rename_i huc
        rcases List.mem_cons.1 hmem with heq | hyt
        · subst heq; subst huc; exact Nat.le_refl _
        · have hgt := runOK_head_gt hok hyt
          have hu : u.rank.toIdx = c.rank.toIdx := by rw [huc]
          omega
      · rename_i huc
        exact ih (runOK_cons_tail hok) hmem

/-- The last of a list ending in a nonempty suffix. -/
theorem lastOf_three {P S : List Card} {c : Card} (hS : S ≠ []) :
    lastOf (P ++ c :: S) = lastOf S := by
  have h : P ++ c :: S = (P ++ [c]) ++ S := by
    simp [List.append_assoc]
  rw [h]
  exact tfc_lastOf_append_ne (P ++ [c]) hS

/-- The last of a list ending in a singleton. -/
theorem lastOf_three_nil {P : List Card} {c : Card} :
    lastOf (P ++ c :: ([] : List Card)) = some c := by
  show lastOf (P ++ [c]) = some c
  exact lastOf_snoc

theorem ne_nil_of_mem {α : Type} {l : List α} {u : α} (h : u ∈ l) : l ≠ [] :=
  fun hc => by rw [hc] at h; cases h

namespace Pile

theorem isEmpty_eq_false_of_faceUp_ne_nil {p : Pile} (h : p.faceUp ≠ []) :
    p.isEmpty = false := by
  rcases p with ⟨hd, f⟩
  cases f with
  | nil => exact absurd rfl h
  | cons u t => cases hd <;> rfl

end Pile

/-! ## §2. Pile-top relocation under the splice -/

section SpliceTop

variable {s : State} {x : Card} {a b : Anchor}

theorem pileOfTop_splice_a
    (hwf : s.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (ha : s.pileHolding x = some a) (hb : s.pileHolding x.twin = some b)
    (hab : a ≠ b) {z : Card} (hz : s.pileOfTop z = some a) :
    (s.spliceTwinRuns x).pileOfTop z = some b := by
  have hPwf := wf_spliceTwinRuns hwf hx hxt
  rw [pileOfTop_eq_some_iff hPwf]
  have hsTop : (s.piles a).top = some z := (pileOfTop_eq_some_iff hwf).mp hz
  have hsTop' : lastOf (preA s x a ++ x :: sufA s x a) = some z := by
    simpa [Pile.top, faceUp_A ha] using hsTop
  show ((s.spliceTwinRuns x).piles b).top = some z
  rw [splice_piles_b_nf ha hb hab]
  show lastOf (preB s x b ++ x :: sufA s x a) = some z
  by_cases hSA : sufA s x a = []
  · have hzA : lastOf (preA s x a ++ x :: sufA s x a) = some x := by
      rw [hSA]
      exact lastOf_three_nil
    have hzx : z = x := Option.some.inj (hsTop'.symm.trans hzA)
    subst hzx
    rw [hSA]
    exact lastOf_three_nil
  · have hzA : lastOf (preA s x a ++ x :: sufA s x a) = lastOf (sufA s x a) :=
      lastOf_three hSA
    have hzS : lastOf (sufA s x a) = some z := by rw [← hzA]; exact hsTop'
    rw [lastOf_three hSA, hzS]

theorem pileOfTop_splice_b
    (hwf : s.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (ha : s.pileHolding x = some a) (hb : s.pileHolding x.twin = some b)
    (hab : a ≠ b) {z : Card} (hz : s.pileOfTop z = some b) :
    (s.spliceTwinRuns x).pileOfTop z = some a := by
  have hPwf := wf_spliceTwinRuns hwf hx hxt
  rw [pileOfTop_eq_some_iff hPwf]
  have hsTop : (s.piles b).top = some z := (pileOfTop_eq_some_iff hwf).mp hz
  have hsTop' : lastOf (preB s x b ++ x.twin :: sufB s x b) = some z := by
    simpa [Pile.top, faceUp_B hb] using hsTop
  show ((s.spliceTwinRuns x).piles a).top = some z
  rw [splice_piles_a_nf ha hb hab]
  show lastOf (preA s x a ++ x.twin :: sufB s x b) = some z
  by_cases hSB : sufB s x b = []
  · have hzB : lastOf (preB s x b ++ x.twin :: sufB s x b) = some x.twin := by
      rw [hSB]
      exact lastOf_three_nil
    have hzx : z = x.twin := Option.some.inj (hsTop'.symm.trans hzB)
    subst hzx
    rw [hSB]
    exact lastOf_three_nil
  · have hzB : lastOf (preB s x b ++ x.twin :: sufB s x b) = lastOf (sufB s x b) :=
      lastOf_three hSB
    have hzS : lastOf (sufB s x b) = some z := by rw [← hzB]; exact hsTop'
    rw [lastOf_three hSB, hzS]

theorem pileOfTop_splice_other
    (hwf : s.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (ha : s.pileHolding x = some a) (hb : s.pileHolding x.twin = some b)
    (hab : a ≠ b) {z : Card} {d : Anchor} (hz : s.pileOfTop z = some d)
    (hda : d ≠ a) (hdb : d ≠ b) :
    (s.spliceTwinRuns x).pileOfTop z = some d := by
  have hPwf := wf_spliceTwinRuns hwf hx hxt
  rw [pileOfTop_eq_some_iff hPwf, spliceTwinRuns_piles_other ha hb hab hda hdb]
  exact (pileOfTop_eq_some_iff hwf).mp hz

end SpliceTop

/-! ## §3. Set-up: the two hosts and their twin parents -/

private theorem canSitOn_twin_left_comm (c b : Card) :
    canSitOn c.twin b = canSitOn c b := by
  rcases c with ⟨cs, cr⟩
  rcases b with ⟨bs, br⟩
  cases cs <;> cases bs <;> rfl

/-- The two `.inr` seats pin the two hosts and their twin parents. -/
theorem splice_setup {s : State} {x : Card}
    (hwf : s.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin)) :
    ∃ (a b : Anchor) (z : Card),
      s.pileHolding x = some a ∧ s.pileHolding x.twin = some b ∧ a ≠ b ∧
      lastOf (below x (s.piles a).faceUp) = some z ∧
      lastOf (below x.twin (s.piles b).faceUp) = some z.twin := by
  obtain ⟨z, hzse⟩ := hx
  obtain ⟨a, ha, _, hzlast⟩ := tfc_seatOf_of_inr hzse
  obtain ⟨z₀, hz₀se⟩ := hxt
  obtain ⟨b, hb, _, hz₀last⟩ := tfc_seatOf_of_inr hz₀se
  have hab : a ≠ b := by
    intro hab
    subst hab
    have hxmem : x ∈ (s.piles a).faceUp := pileHolding_mem ha
    have htmem : x.twin ∈ (s.piles a).faceUp := pileHolding_mem hb
    have heq : x = x.twin :=
      runOK_rank_distinct (hwf.runOK_of a) hxmem htmem rfl
    exact card_twin_ne x heq.symm
  have hcanz : canSitOn x z = true := (tfc_seat_parent hwf ha hzlast).1
  have hcanz₀ : canSitOn x.twin z₀.twin = true := (tfc_seat_parent hwf hb hz₀last).1
  have hcanz₀' : canSitOn x z₀.twin = true := by
    rw [← canSitOn_twin_left_comm x z₀.twin]
    exact hcanz₀
  have hfit := tfc_fitting_parent hcanz₀' hcanz
  have hz₀eq : z₀ = z := by
    rcases hfit with h | h
    · -- `z₀.twin = z`: the twin would sit on the same card as `x`
      exfalso
      have hzA : z ∈ (s.piles a).faceUp := mem_below _ (lastOf_mem hzlast)
      have hzB : z ∈ (s.piles b).faceUp := by
        rw [← h]
        exact mem_below _ (lastOf_mem hz₀last)
      exact (mem_faceUp_unique hwf hzA b (Ne.symm hab)).1 hzB
    · exact card_twin_inj h
  refine ⟨a, b, z, ha, hb, hab, hzlast, ?_⟩
  rw [hz₀eq] at hz₀last
  exact hz₀last

/-! ## §4. The draw commutes with the splice -/

theorem recycle_with_piles (st : State) (ps : Anchor → Pile) :
    State.recycle { st with piles := ps } = { State.recycle st with piles := ps } := by
  by_cases hs : st.stock = []
  · by_cases hw : st.waste = []
    · rw [recycle_allEmpty _ (by simpa using hs) (by simpa using hw),
        recycle_allEmpty st hs hw]
    · rw [recycle_nil _ (by simpa using hs) (by simpa using hw),
        recycle_nil st hs hw]
  · rw [recycle_keep _ (by simpa using hs), recycle_keep st hs]

theorem dealStock_with_piles (st : State) (ps : Anchor → Pile) :
    State.dealStock { st with piles := ps } =
      (State.dealStock st).map (fun u => { u with piles := ps }) := by
  by_cases hs : st.stock = []
  · rw [dealStock_nil _ (by simpa using hs), dealStock_nil st hs]
    rfl
  · rw [dealStock_eq_of_ne_nil _ (by simpa using hs),
      dealStock_eq_of_ne_nil st hs]
    rfl

theorem stepDraw_with_piles (st : State) (ps : Anchor → Pile) :
    ({ st with piles := ps } : State).stepDraw =
      (st.stepDraw).map (fun u => { u with piles := ps }) := by
  unfold State.stepDraw
  rw [recycle_with_piles, dealStock_with_piles]

theorem spliceTwinRuns_piles_congr {u v : State} {x : Card} (h : u.piles = v.piles) :
    (u.spliceTwinRuns x).piles = (v.spliceTwinRuns x).piles := by
  have hx : u.pileHolding x = v.pileHolding x := pileHolding_congr h
  have hxt : u.pileHolding x.twin = v.pileHolding x.twin := pileHolding_congr h
  cases hvx : v.pileHolding x with
  | none =>
      have hux : u.pileHolding x = none := by rw [hx, hvx]
      cases hvt : v.pileHolding x.twin with
      | none =>
          have hut : u.pileHolding x.twin = none := by rw [hxt, hvt]
          rw [spliceTwinRuns_of_none_left hux, spliceTwinRuns_of_none_left hvx]
          exact h
      | some b =>
          have hut : u.pileHolding x.twin = some b := by rw [hxt, hvt]
          rw [spliceTwinRuns_of_none_left hux, spliceTwinRuns_of_none_left hvx]
          exact h
  | some a =>
      have hua : u.pileHolding x = some a := by rw [hx]; exact hvx
      cases hvt : v.pileHolding x.twin with
      | none =>
          have hut : u.pileHolding x.twin = none := by rw [hxt, hvt]
          rw [spliceTwinRuns_of_none_right hut, spliceTwinRuns_of_none_right hvt]
          exact h
      | some b =>
          have hub : u.pileHolding x.twin = some b := by rw [hxt]; exact hvt
          by_cases hab : a = b
          · subst hab
            rw [spliceTwinRuns_of_eq hua hub, spliceTwinRuns_of_eq hvx hvt]
            exact h
          · funext a'
            by_cases h1 : a' = a
            · rw [h1, spliceTwinRuns_piles_self hua hub hab,
                spliceTwinRuns_piles_self hvx hvt hab, h]
            · by_cases h2 : a' = b
              · rw [h2, spliceTwinRuns_piles_second hua hub hab,
                  spliceTwinRuns_piles_second hvx hvt hab, h]
              · rw [spliceTwinRuns_piles_other hua hub hab h1 h2,
                  spliceTwinRuns_piles_other hvx hvt hab h1 h2, h]
theorem spliceTwinRuns_as_update {s : State} {x : Card} {a b : Anchor}
    (ha : s.pileHolding x = some a) (hb : s.pileHolding x.twin = some b)
    (hab : a ≠ b) :
    s.spliceTwinRuns x = { s with piles := (s.spliceTwinRuns x).piles } := by
  apply State.ext
  · funext su
    exact congrFun (spliceTwinRuns_found ha hb hab) su
  · rfl
  · exact spliceTwinRuns_stock ha hb hab
  · exact spliceTwinRuns_waste ha hb hab
  · exact spliceTwinRuns_drawStep ha hb hab

/-! ## §5. One-card top edits -/

theorem putCard_pileHolding_ne {st : State} (hwf : st.WF) {y v : Card} {k : Anchor}
    (hk : st.pileOfTop v = some k) {c : Card} {c' : Anchor}
    (hc : st.pileHolding c = some c') (hcy : c ≠ y) :
    (st.putCard y (Sum.inr v)).pileHolding c = some c' := by
  have hmem : c ∈ (st.piles c').faceUp := pileHolding_mem hc
  have hother : ∀ j, j ≠ c' → c ∉ (st.piles j).faceUp :=
    fun j hj => (mem_faceUp_unique hwf hmem j hj).1
  refine tfc_pileHolding_pin ?_ ?_
  · rw [putCard_inr_eq hk]
    by_cases hck : c' = k
    · rw [hck, setPile_piles_self]
      exact List.mem_append_left _ (by rwa [hck] at hmem)
    · rw [setPile_piles_ne hck]
      exact hmem
  · intro j hj
    rw [putCard_inr_eq hk]
    by_cases hjk : j = k
    · rw [hjk, setPile_piles_self]
      intro hmemj
      rcases List.mem_append.mp hmemj with h | h
      · exact hother k (by rwa [hjk] at hj) h
      · exact hcy (List.mem_singleton.mp h)
    · rw [setPile_piles_ne hjk]
      exact hother j hj
theorem below_append_singleton_mem {c y : Card} {l : List Card} (h : c ∈ l) :
    below c (l ++ [y]) = below c l :=
  tfc_below_mem_append_left l [y] h

theorem fromCard_append_singleton_mem {c y : Card} {l : List Card} (h : c ∈ l) :
    fromCard c (l ++ [y]) = fromCard c l ++ [y] :=
  fromCard_append_of_mem l [y] h

theorem splice_putCard_inr {s : State} {x : Card} {a b : Anchor}
    (hwf : s.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (ha : s.pileHolding x = some a) (hb : s.pileHolding x.twin = some b)
    (hab : a ≠ b) {y v : Card} {k : Anchor}
    (hyx : y ≠ x) (hyt : y ≠ x.twin)
    (hk : s.pileOfTop v = some k) :
    (s.spliceTwinRuns x).putCard y (Sum.inr v) =
      (s.putCard y (Sum.inr v)).spliceTwinRuns x := by
  have ha' : (s.putCard y (Sum.inr v)).pileHolding x = some a :=
    putCard_pileHolding_ne hwf hk ha (Ne.symm hyx)
  have hb' : (s.putCard y (Sum.inr v)).pileHolding x.twin = some b :=
    putCard_pileHolding_ne hwf hk hb (Ne.symm hyt)
  have hxmem : x ∈ (s.piles a).faceUp := pileHolding_mem ha
  have htmem : x.twin ∈ (s.piles b).faceUp := pileHolding_mem hb
  have hfcA : fromCard x (s.piles a).faceUp = x :: sufA s x a := by
    simpa [sufA] using fromCard_cons_suf hxmem
  have hfcB : fromCard x.twin (s.piles b).faceUp = x.twin :: sufB s x b := by
    simpa [sufB] using fromCard_cons_suf htmem
  have hbA : below x (s.piles a).faceUp = preA s x a := rfl
  have hbB : below x.twin (s.piles b).faceUp = preB s x b := rfl
  by_cases hka : k = a
  · subst k
    have hloc : (s.spliceTwinRuns x).pileOfTop v = some b :=
      pileOfTop_splice_a hwf hx hxt ha hb hab hk
    have hfa : ((s.putCard y (Sum.inr v)).piles a).faceUp =
        (s.piles a).faceUp ++ [y] := by
      rw [putCard_inr_eq hk, setPile_piles_self]
    have hha : ((s.putCard y (Sum.inr v)).piles a).hidden = (s.piles a).hidden := by
      rw [putCard_inr_eq hk, setPile_piles_self]
    have hfb : ((s.putCard y (Sum.inr v)).piles b).faceUp =
        (s.piles b).faceUp := by
      rw [putCard_inr_eq hk, setPile_piles_ne (Ne.symm hab)]
    have hhb : ((s.putCard y (Sum.inr v)).piles b).hidden = (s.piles b).hidden := by
      rw [putCard_inr_eq hk, setPile_piles_ne (Ne.symm hab)]
    have hs'other : ∀ a', a' ≠ a → a' ≠ b →
        (s.putCard y (Sum.inr v)).piles a' = s.piles a' := by
      intro a' h1 h2
      rw [putCard_inr_eq hk, setPile_piles_ne h1]
    have hSs'a : ((s.putCard y (Sum.inr v)).spliceTwinRuns x).piles a =
        { hidden := (s.piles a).hidden
          faceUp := preA s x a ++ x.twin :: sufB s x b } := by
      rw [spliceTwinRuns_piles_self ha' hb' hab, hha, hfa, hfb,
        below_append_singleton_mem hxmem, hbA, hfcB]
    have hSs'b : ((s.putCard y (Sum.inr v)).spliceTwinRuns x).piles b =
        { hidden := (s.piles b).hidden
          faceUp := preB s x b ++ x :: sufA s x a ++ [y] } := by
      rw [spliceTwinRuns_piles_second ha' hb' hab, hhb, hfb, hfa,
        hbB, fromCard_append_singleton_mem hxmem, hfcA]
      simp only [List.append_assoc]
    have hSsa : (s.spliceTwinRuns x).piles a =
        { hidden := (s.piles a).hidden
          faceUp := preA s x a ++ x.twin :: sufB s x b } :=
      splice_piles_a_nf ha hb hab
    have hSsb : (s.spliceTwinRuns x).piles b =
        { hidden := (s.piles b).hidden
          faceUp := preB s x b ++ x :: sufA s x a } :=
      splice_piles_b_nf ha hb hab
    rw [putCard_inr_eq hloc]
    apply State.ext
    · funext su
      rw [setPile_found, spliceTwinRuns_found ha' hb' hab,
        putCard_found, spliceTwinRuns_found ha hb hab]
    · funext a'
      by_cases h1 : a' = b
      · rw [h1]
        rw [setPile_piles_self, hSsb, hSs'b]
      · by_cases h2 : a' = a
        · rw [h2]
          rw [setPile_piles_ne hab, hSsa, hSs'a]
        · rw [setPile_piles_ne h1, spliceTwinRuns_piles_other ha hb hab h2 h1,
            spliceTwinRuns_piles_other ha' hb' hab h2 h1, hs'other a' h2 h1]
    · rw [setPile_stock, spliceTwinRuns_stock ha' hb' hab,
        putCard_stock, spliceTwinRuns_stock ha hb hab]
    · rw [setPile_waste, spliceTwinRuns_waste ha' hb' hab,
        putCard_waste, spliceTwinRuns_waste ha hb hab]
    · rw [setPile_drawStep, spliceTwinRuns_drawStep ha' hb' hab,
        putCard_drawStep, spliceTwinRuns_drawStep ha hb hab]
  · by_cases hkb : k = b
    · subst k
      have hloc : (s.spliceTwinRuns x).pileOfTop v = some a :=
        pileOfTop_splice_b hwf hx hxt ha hb hab hk
      have hfb : ((s.putCard y (Sum.inr v)).piles b).faceUp =
          (s.piles b).faceUp ++ [y] := by
        rw [putCard_inr_eq hk, setPile_piles_self]
      have hhb : ((s.putCard y (Sum.inr v)).piles b).hidden = (s.piles b).hidden := by
        rw [putCard_inr_eq hk, setPile_piles_self]
      have hfa : ((s.putCard y (Sum.inr v)).piles a).faceUp = (s.piles a).faceUp := by
        rw [putCard_inr_eq hk, setPile_piles_ne hab]
      have hha : ((s.putCard y (Sum.inr v)).piles a).hidden = (s.piles a).hidden := by
        rw [putCard_inr_eq hk, setPile_piles_ne hab]
      have hs'other : ∀ a', a' ≠ a → a' ≠ b →
          (s.putCard y (Sum.inr v)).piles a' = s.piles a' := by
        intro a' h1 h2
        rw [putCard_inr_eq hk, setPile_piles_ne h2]
      have hSs'a : ((s.putCard y (Sum.inr v)).spliceTwinRuns x).piles a =
          { hidden := (s.piles a).hidden
            faceUp := preA s x a ++ x.twin :: sufB s x b ++ [y] } := by
        rw [spliceTwinRuns_piles_self ha' hb' hab, hha, hfa, hfb,
          hbA, fromCard_append_singleton_mem htmem, hfcB]
        simp only [List.append_assoc]
      have hSs'b : ((s.putCard y (Sum.inr v)).spliceTwinRuns x).piles b =
          { hidden := (s.piles b).hidden
            faceUp := preB s x b ++ x :: sufA s x a } := by
        rw [spliceTwinRuns_piles_second ha' hb' hab, hhb, hfb, hfa,
          below_append_singleton_mem htmem, hbB, hfcA]
      have hSsa : (s.spliceTwinRuns x).piles a =
          { hidden := (s.piles a).hidden
            faceUp := preA s x a ++ x.twin :: sufB s x b } :=
        splice_piles_a_nf ha hb hab
      have hSsb : (s.spliceTwinRuns x).piles b =
          { hidden := (s.piles b).hidden
            faceUp := preB s x b ++ x :: sufA s x a } :=
        splice_piles_b_nf ha hb hab
      rw [putCard_inr_eq hloc]
      apply State.ext
      · funext su
        rw [setPile_found, spliceTwinRuns_found ha' hb' hab,
          putCard_found, spliceTwinRuns_found ha hb hab]
      · funext a'
        by_cases h1 : a' = a
        · rw [h1]
          rw [setPile_piles_self, hSsa, hSs'a]
        · by_cases h2 : a' = b
          · rw [h2]
            rw [setPile_piles_ne (Ne.symm hab), hSsb, hSs'b]
          · rw [setPile_piles_ne h1, spliceTwinRuns_piles_other ha hb hab h1 h2,
              spliceTwinRuns_piles_other ha' hb' hab h1 h2, hs'other a' h1 h2]
      · rw [setPile_stock, spliceTwinRuns_stock ha' hb' hab,
          putCard_stock, spliceTwinRuns_stock ha hb hab]
      · rw [setPile_waste, spliceTwinRuns_waste ha' hb' hab,
          putCard_waste, spliceTwinRuns_waste ha hb hab]
      · rw [setPile_drawStep, spliceTwinRuns_drawStep ha' hb' hab,
          putCard_drawStep, spliceTwinRuns_drawStep ha hb hab]
    · have hloc : (s.spliceTwinRuns x).pileOfTop v = some k :=
        pileOfTop_splice_other hwf hx hxt ha hb hab hk hka hkb
      have hfk : ((s.putCard y (Sum.inr v)).piles k).faceUp =
          (s.piles k).faceUp ++ [y] := by
        rw [putCard_inr_eq hk, setPile_piles_self]
      have hhk : ((s.putCard y (Sum.inr v)).piles k).hidden = (s.piles k).hidden := by
        rw [putCard_inr_eq hk, setPile_piles_self]
      have hfa : ((s.putCard y (Sum.inr v)).piles a).faceUp = (s.piles a).faceUp := by
        rw [putCard_inr_eq hk, setPile_piles_ne (Ne.symm hka)]
      have hha : ((s.putCard y (Sum.inr v)).piles a).hidden = (s.piles a).hidden := by
        rw [putCard_inr_eq hk, setPile_piles_ne (Ne.symm hka)]
      have hfb : ((s.putCard y (Sum.inr v)).piles b).faceUp = (s.piles b).faceUp := by
        rw [putCard_inr_eq hk, setPile_piles_ne (Ne.symm hkb)]
      have hhb : ((s.putCard y (Sum.inr v)).piles b).hidden = (s.piles b).hidden := by
        rw [putCard_inr_eq hk, setPile_piles_ne (Ne.symm hkb)]
      have hs'other : ∀ a', a' ≠ k → (s.putCard y (Sum.inr v)).piles a' = s.piles a' := by
        intro a' h
        rw [putCard_inr_eq hk, setPile_piles_ne h]
      have hSs'a : ((s.putCard y (Sum.inr v)).spliceTwinRuns x).piles a =
          { hidden := (s.piles a).hidden
            faceUp := preA s x a ++ x.twin :: sufB s x b } := by
        rw [spliceTwinRuns_piles_self ha' hb' hab, hha, hfa, hfb,
          hbA, hfcB]
      have hSs'b : ((s.putCard y (Sum.inr v)).spliceTwinRuns x).piles b =
          { hidden := (s.piles b).hidden
            faceUp := preB s x b ++ x :: sufA s x a } := by
        rw [spliceTwinRuns_piles_second ha' hb' hab, hhb, hfb, hfa,
          hbB, hfcA]
      have hSs'k : ((s.putCard y (Sum.inr v)).spliceTwinRuns x).piles k =
          { hidden := (s.piles k).hidden, faceUp := (s.piles k).faceUp ++ [y] } := by
        rw [spliceTwinRuns_piles_other ha' hb' hab hka hkb]
        apply Pile.ext
        · exact hhk
        · exact hfk
      have hSsa : (s.spliceTwinRuns x).piles a =
          { hidden := (s.piles a).hidden
            faceUp := preA s x a ++ x.twin :: sufB s x b } :=
        splice_piles_a_nf ha hb hab
      have hSsb : (s.spliceTwinRuns x).piles b =
          { hidden := (s.piles b).hidden
            faceUp := preB s x b ++ x :: sufA s x a } :=
        splice_piles_b_nf ha hb hab
      have hSsk : (s.spliceTwinRuns x).piles k = s.piles k :=
        spliceTwinRuns_piles_other ha hb hab hka hkb
      rw [putCard_inr_eq hloc]
      apply State.ext
      · funext su
        rw [setPile_found, spliceTwinRuns_found ha' hb' hab,
          putCard_found, spliceTwinRuns_found ha hb hab]
      · funext a'
        by_cases h1 : a' = k
        · rw [h1]
          rw [setPile_piles_self, hSsk, hSs'k]
        · by_cases h2 : a' = a
          · rw [h2] at h1 ⊢
            rw [setPile_piles_ne h1, hSsa, hSs'a]
          · by_cases h3 : a' = b
            · rw [h3] at h1 ⊢
              rw [setPile_piles_ne h1, hSsb, hSs'b]
            · rw [setPile_piles_ne h1, spliceTwinRuns_piles_other ha hb hab h2 h3,
                spliceTwinRuns_piles_other ha' hb' hab h2 h3, hs'other a' h1]
      · rw [setPile_stock, spliceTwinRuns_stock ha' hb' hab,
          putCard_stock, spliceTwinRuns_stock ha hb hab]
      · rw [setPile_waste, spliceTwinRuns_waste ha' hb' hab,
          putCard_waste, spliceTwinRuns_waste ha hb hab]
      · rw [setPile_drawStep, spliceTwinRuns_drawStep ha' hb' hab,
          putCard_drawStep, spliceTwinRuns_drawStep ha hb hab]
theorem splice_putCard_inl {s : State} {x : Card} {a b e : Anchor}
    (hwf : s.WF)
    (ha : s.pileHolding x = some a) (hb : s.pileHolding x.twin = some b)
    (hab : a ≠ b) {y : Card}
    (hyx : y ≠ x) (hyt : y ≠ x.twin)
    (hneA : e ≠ a) (hneB : e ≠ b) :
    (s.spliceTwinRuns x).putCard y (Sum.inl e) =
      (s.putCard y (Sum.inl e)).spliceTwinRuns x := by
  have ha' : (s.setPile e ⟨[], [y]⟩).pileHolding x = some a := by
    refine tfc_pileHolding_pin ?_ ?_
    · rw [setPile_piles_ne (Ne.symm hneA)]
      exact pileHolding_mem ha
    · intro j hj
      by_cases hje : j = e
      · rw [hje, setPile_piles_self]
        intro hmem
        exact hyx (List.mem_singleton.mp hmem).symm
      · rw [setPile_piles_ne hje]
        exact (mem_faceUp_unique hwf (pileHolding_mem ha) j hj).1
  have hb' : (s.setPile e ⟨[], [y]⟩).pileHolding x.twin = some b := by
    refine tfc_pileHolding_pin ?_ ?_
    · rw [setPile_piles_ne (Ne.symm hneB)]
      exact pileHolding_mem hb
    · intro j hj
      by_cases hje : j = e
      · rw [hje, setPile_piles_self]
        intro hmem
        exact hyt (List.mem_singleton.mp hmem).symm
      · rw [setPile_piles_ne hje]
        exact (mem_faceUp_unique hwf (pileHolding_mem hb) j hj).1
  have hs'a : (s.setPile e ⟨[], [y]⟩).piles a = s.piles a := setPile_piles_ne (Ne.symm hneA)
  have hs'b : (s.setPile e ⟨[], [y]⟩).piles b = s.piles b := setPile_piles_ne (Ne.symm hneB)
  rw [putCard_eq_inl, putCard_eq_inl]
  apply State.ext
  · funext su
    rw [setPile_found, spliceTwinRuns_found ha' hb' hab,
      setPile_found, spliceTwinRuns_found ha hb hab]
  · funext a'
    by_cases h1 : a' = e
    · rw [h1]
      rw [setPile_piles_self, spliceTwinRuns_piles_other ha' hb' hab hneA hneB,
        setPile_piles_self]
    · by_cases h2 : a' = a
      · rw [h2]
        rw [setPile_piles_ne (Ne.symm hneA), splice_piles_a_nf ha hb hab,
          splice_piles_a_nf ha' hb' hab]
        simp only [preA, sufB, hs'a, hs'b]
      · by_cases h3 : a' = b
        · rw [h3]
          rw [setPile_piles_ne (Ne.symm hneB), splice_piles_b_nf ha hb hab,
            splice_piles_b_nf ha' hb' hab]
          simp only [preB, sufA, hs'a, hs'b]
        · rw [setPile_piles_ne h1, spliceTwinRuns_piles_other ha hb hab h2 h3,
            spliceTwinRuns_piles_other ha' hb' hab h2 h3, setPile_piles_ne h1]
  · rw [setPile_stock, spliceTwinRuns_stock ha' hb' hab,
      setPile_stock, spliceTwinRuns_stock ha hb hab]
  · rw [setPile_waste, spliceTwinRuns_waste ha' hb' hab,
      setPile_waste, spliceTwinRuns_waste ha hb hab]
  · rw [setPile_drawStep, spliceTwinRuns_drawStep ha' hb' hab,
      setPile_drawStep, spliceTwinRuns_drawStep ha hb hab]
private theorem canSitOn_king_false_comm {c z : Card} (hk : c.rank = Rank.king) :
    canSitOn c z = false := by
  rw [canSitOn]
  have hkidx : c.rank.toIdx = 12 := by rw [hk]; rfl
  have hzlt : z.rank.toIdx < 13 := Rank.toIdx_lt z.rank
  have h13 : decide (13 = z.rank.toIdx) = false := decide_eq_false (by omega)
  simp [hkidx, h13]

/-- A legal `tabToTab` can never move either twin: all fitting parents are
covered and a king seat is impossible under an `.inr` seat. -/
theorem tabToTab_mover_off {s t : State} {x y : Card} {b : Base}
    (hwf : s.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (hstep : State.step s (Move.tabToTab y b) = some t) :
    y ≠ x ∧ y ≠ x.twin := by
  obtain ⟨a, bb, z, ha, hb, hab, hza, hzb⟩ := splice_setup hwf hx hxt
  have hzx : canSitOn x z = true := (tfc_seat_parent hwf ha hza).1
  have hzxT : canSitOn x.twin z.twin = true := (tfc_seat_parent hwf hb hzb).1
  have hztop : s.pileOfTop z = none := (tfc_seat_parent hwf ha hza).2
  have hztopT : s.pileOfTop z.twin = none := (tfc_seat_parent hwf hb hzb).2
  have hxk : x.rank ≠ Rank.king := by
    intro hk
    have hf := canSitOn_king_false_comm (z := z) hk
    rw [hzx] at hf
    exact Bool.noConfusion hf
  have hxtk : x.twin.rank ≠ Rank.king := by
    intro hk
    have hxrk : x.rank = Rank.king := by
      rcases x with ⟨xs, xr⟩
      simpa [Card.twin] using hk
    exact hxk hxrk
  obtain ⟨a0, hhold0, hcp, hrunne, hs⟩ := step_tabToTab_inv hstep
  constructor
  · intro hyx
    have hcp' : s.canPlace x b = true := by simpa [hyx] using hcp
    cases b with
    | inl e =>
        exact hxk (canPlace_inl hcp').2
    | inr v =>
        obtain ⟨k, hpk, hfit⟩ := canPlace_inr hcp'
        rcases tfc_fitting_parent hfit hzx with h | h
        · rw [h, hztop] at hpk
          cases hpk
        · rw [h, hztopT] at hpk
          cases hpk
  · intro hyt
    have hcp' : s.canPlace x.twin b = true := by simpa [hyt] using hcp
    cases b with
    | inl e =>
        exact hxtk (canPlace_inl hcp').2
    | inr v =>
        obtain ⟨k, hpk, hfit⟩ := canPlace_inr hcp'
        rcases tfc_fitting_parent hfit hzxT with h | h
        · rw [h, hztopT] at hpk
          cases hpk
        · have hzz : z.twin.twin = z := by
            rcases z with ⟨zs, zr⟩
            simp [Card.twin]
          rw [hzz] at h
          rw [h, hztop] at hpk
          cases hpk
theorem canPlace_splice {s : State} {x : Card} {a b : Anchor}
    (hwf : s.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (ha : s.pileHolding x = some a) (hb : s.pileHolding x.twin = some b)
    (hab : a ≠ b) {y : Card} {base : Base}
    (hcp : s.canPlace y base = true) :
    (s.spliceTwinRuns x).canPlace y base = true := by
  cases base with
  | inl e =>
      obtain ⟨hemp, hking⟩ := canPlace_inl hcp
      have hane : e ≠ a := by
        intro he
        subst he
        obtain ⟨-, hface⟩ := (Pile.isEmpty_eq _).mp hemp
        have hxmem := pileHolding_mem ha
        rw [hface] at hxmem
        exact absurd hxmem (by simp)
      have hbne : e ≠ b := by
        intro he
        subst he
        obtain ⟨-, hface⟩ := (Pile.isEmpty_eq _).mp hemp
        have htmem := pileHolding_mem hb
        rw [hface] at htmem
        exact absurd htmem (by simp)
      have hempS : ((s.spliceTwinRuns x).piles e).isEmpty = true := by
        rw [spliceTwinRuns_piles_other ha hb hab hane hbne]
        exact hemp
      simp [State.canPlace, hempS, hking]
  | inr v =>
      obtain ⟨k, hk, hfit⟩ := canPlace_inr hcp
      by_cases hka : k = a
      · subst k
        have hloc := pileOfTop_splice_a hwf hx hxt ha hb hab hk
        simp [State.canPlace, hloc, hfit]
      · by_cases hkb : k = b
        · subst k
          have hloc := pileOfTop_splice_b hwf hx hxt ha hb hab hk
          simp [State.canPlace, hloc, hfit]
        · have hloc := pileOfTop_splice_other hwf hx hxt ha hb hab hk hka hkb
          simp [State.canPlace, hloc, hfit]

theorem tabToFoundR_splice {s : State} {x y : Card} {a b : Anchor}
    (hwf : s.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (ha : s.pileHolding x = some a) (hb : s.pileHolding x.twin = some b)
    (hab : a ≠ b) (hyx : y ≠ x) (hyt : y ≠ x.twin)
    (h : tabToFoundR s y = true) :
    tabToFoundR (s.spliceTwinRuns x) y = true := by
  have hnext : s.nextUp y = true := by
    by_cases hn : s.nextUp y = true
    · exact hn
    · simp [tabToFoundR, hn] at h
  have hnextS : (s.spliceTwinRuns x).nextUp y = true := by
    unfold State.nextUp State.foundHeight
    rw [spliceTwinRuns_found ha hb hab]
    exact hnext
  obtain ⟨k, hk⟩ : ∃ k, s.pileOfTop y = some k := by
    cases hp : s.pileOfTop y with
    | none =>
        simp [tabToFoundR, hnext, hp] at h
    | some k => exact ⟨k, rfl⟩
  by_cases hka : k = a
  · subst k
    have hloc := pileOfTop_splice_a hwf hx hxt ha hb hab hk
    have hU : sufA s x a ≠ [] := by
      intro hU
      have htop : lastOf (s.piles a).faceUp = some y := (tfc_pileOfTop_top hk).2
      rw [faceUp_A ha, hU] at htop
      have : y = x := Option.some.inj (htop.symm.trans lastOf_three_nil)
      exact hyx this
    obtain ⟨v, hv⟩ := lastOf_exists hU
    obtain ⟨U', hU'⟩ := lastOf_eq_snoc hv
    have hchop : chop ((s.spliceTwinRuns x).piles b).faceUp =
        preB s x b ++ x :: U' := by
      rw [splice_piles_b_nf ha hb hab, hU']
      rw [show preB s x b ++ x :: (U' ++ [v]) = (preB s x b ++ x :: U') ++ [v] by
        simp [List.append_assoc]]
      rw [chop_snoc]
    have hchopne : chop ((s.spliceTwinRuns x).piles b).faceUp ≠ [] := by
      rw [hchop]
      simp
    unfold tabToFoundR
    rw [hnextS]
    simp only []
    rw [hloc]
    simp only []
    rw [hchop]
    cases hpre : preB s x b with
    | nil => rfl
    | cons hd tl => rfl
  · by_cases hkb : k = b
    · subst k
      have hloc := pileOfTop_splice_b hwf hx hxt ha hb hab hk
      have hV : sufB s x b ≠ [] := by
        intro hV
        have htop : lastOf (s.piles b).faceUp = some y := (tfc_pileOfTop_top hk).2
        rw [faceUp_B hb, hV] at htop
        have : y = x.twin := Option.some.inj (htop.symm.trans lastOf_three_nil)
        exact hyt this
      obtain ⟨v, hv⟩ := lastOf_exists hV
      obtain ⟨V', hV'⟩ := lastOf_eq_snoc hv
      have hchop : chop ((s.spliceTwinRuns x).piles a).faceUp =
          preA s x a ++ x.twin :: V' := by
        rw [splice_piles_a_nf ha hb hab, hV']
        rw [show preA s x a ++ x.twin :: (V' ++ [v]) = (preA s x a ++ x.twin :: V') ++ [v] by
          simp [List.append_assoc]]
        rw [chop_snoc]
      have hchopne : chop ((s.spliceTwinRuns x).piles a).faceUp ≠ [] := by
        rw [hchop]
        simp
      unfold tabToFoundR
      rw [hnextS]
      simp only []
      rw [hloc]
      simp only []
      rw [hchop]
      cases hpre : preA s x a with
      | nil => rfl
      | cons hd tl => rfl
    · have hloc := pileOfTop_splice_other hwf hx hxt ha hb hab hk hka hkb
      have hSsk := spliceTwinRuns_piles_other ha hb hab hka hkb
      simp only [tabToFoundR, hnextS, hloc, hnext, hk, hSsk] at h ⊢
      exact h
theorem tabToTab_condition_splice {s : State} {x : Card} {a b c : Anchor}
    (hwf : s.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (ha : s.pileHolding x = some a) (hb : s.pileHolding x.twin = some b)
    (hab : a ≠ b) {y : Card} (hyx : y ≠ x) (hyt : y ≠ x.twin)
    (hc : s.pileHolding y = some c)
    (hcond : below y (s.piles c).faceUp ≠ [] ∨
      ((s.piles c).hidden = [] ∧ y.rank = Rank.king)) :
    ∃ c', (s.spliceTwinRuns x).pileHolding y = some c' ∧
      (below y ((s.spliceTwinRuns x).piles c').faceUp ≠ [] ∨
        (((s.spliceTwinRuns x).piles c').hidden = [] ∧ y.rank = Rank.king)) := by
  have hwfS : (s.spliceTwinRuns x).WF := wf_spliceTwinRuns hwf hx hxt
  have hpin : ∀ a', (s.spliceTwinRuns x).pileHolding y = some a' ↔
      y ∈ ((s.spliceTwinRuns x).piles a').faceUp :=
    fun a' => pileHolding_eq_some_iff hwfS
  by_cases hca : c = a
  · subst c
    have hface := faceUp_A ha
    have hyface : y ∈ (s.piles a).faceUp := pileHolding_mem hc
    rw [hface] at hyface
    rcases List.mem_append.mp hyface with hyPre | hyRest
    · have hyPre' : y ∈ preA s x a := hyPre
      have hbel : below y (s.piles a).faceUp = below y (preA s x a) := by
        rw [hface]
        exact tfc_below_mem_append_left (preA s x a) (x :: sufA s x a) hyPre'
      refine ⟨a, ?_, ?_⟩
      · rw [hpin]
        rw [splice_piles_a_nf ha hb hab]
        change y ∈ preA s x a ++ x.twin :: sufB s x b
        exact List.mem_append_left _ hyPre'
      · rcases hcond with h | h
        · left
          rw [splice_piles_a_nf ha hb hab]
          rw [tfc_below_mem_append_left (preA s x a) (x.twin :: sufB s x b) hyPre']
          rwa [hbel] at h
        · right
          refine ⟨?_, h.2⟩
          rw [splice_piles_a_nf ha hb hab]
          exact h.1
    · rcases List.mem_cons.mp hyRest with hyx' | hySuf
      · exact absurd hyx' hyx
      · refine ⟨b, ?_, ?_⟩
        · rw [hpin]
          rw [splice_piles_b_nf ha hb hab]
          change y ∈ preB s x b ++ x :: sufA s x a
          exact List.mem_append_right _ (List.mem_cons_of_mem x hySuf)
        · left
          rw [splice_piles_b_nf ha hb hab]
          have hyB : y ∉ preB s x b := by
            have hyA : y ∈ (s.piles a).faceUp := by
              rw [hface]
              exact List.mem_append_right _ (List.mem_cons_of_mem x hySuf)
            exact fun h => (mem_faceUp_unique hwf hyA b (Ne.symm hab)).1 (mem_below _ h)
          rw [below_append_eq (A := preB s x b) (B := x :: sufA s x a) hyB]
          rw [below_cons y x (sufA s x a)]
          rw [ite_eq_right (fun h => hyx h.symm)]
          simp
  · by_cases hcb : c = b
    · subst c
      have hface := faceUp_B hb
      have hyface : y ∈ (s.piles b).faceUp := pileHolding_mem hc
      rw [hface] at hyface
      rcases List.mem_append.mp hyface with hyPre | hyRest
      · have hyPre' : y ∈ preB s x b := hyPre
        have hbel : below y (s.piles b).faceUp = below y (preB s x b) := by
          rw [hface]
          exact tfc_below_mem_append_left (preB s x b) (x.twin :: sufB s x b) hyPre'
        refine ⟨b, ?_, ?_⟩
        · rw [hpin]
          rw [splice_piles_b_nf ha hb hab]
          change y ∈ preB s x b ++ x :: sufA s x a
          exact List.mem_append_left _ hyPre'
        · rcases hcond with h | h
          · left
            rw [splice_piles_b_nf ha hb hab]
            change below y (preB s x b ++ x :: sufA s x a) ≠ []
            rw [tfc_below_mem_append_left (preB s x b) (x :: sufA s x a) hyPre']
            rwa [hbel] at h
          · right
            refine ⟨?_, h.2⟩
            rw [splice_piles_b_nf ha hb hab]
            exact h.1
      · rcases List.mem_cons.mp hyRest with hyt' | hySuf
        · exact absurd hyt' hyt
        · refine ⟨a, ?_, ?_⟩
          · rw [hpin]
            rw [splice_piles_a_nf ha hb hab]
            change y ∈ preA s x a ++ x.twin :: sufB s x b
            exact List.mem_append_right _ (List.mem_cons_of_mem x.twin hySuf)
          · left
            rw [splice_piles_a_nf ha hb hab]
            have hyA : y ∉ preA s x a := by
              have hyB : y ∈ (s.piles b).faceUp := by
                rw [hface]
                exact List.mem_append_right _ (List.mem_cons_of_mem x.twin hySuf)
              exact fun h => (mem_faceUp_unique hwf hyB a hab).1 (mem_below _ h)
            rw [below_append_eq (A := preA s x a) (B := x.twin :: sufB s x b) hyA]
            rw [below_cons y x.twin (sufB s x b)]
            rw [ite_eq_right (fun h => hyt h.symm)]
            simp
    · refine ⟨c, ?_, ?_⟩
      · rw [hpin]
        rw [spliceTwinRuns_piles_other ha hb hab hca hcb]
        exact pileHolding_mem hc
      · rw [spliceTwinRuns_piles_other ha hb hab hca hcb]
        exact hcond
theorem tabToTabR_splice {s : State} {x y : Card} {a b : Anchor} {base : Base}
    (hwf : s.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (ha : s.pileHolding x = some a) (hb : s.pileHolding x.twin = some b)
    (hab : a ≠ b) (hyx : y ≠ x) (hyt : y ≠ x.twin)
    (h : tabToTabR s y base = true) :
    tabToTabR (s.spliceTwinRuns x) y base = true := by
  obtain ⟨c, hc⟩ : ∃ c, s.pileHolding y = some c := by
    cases hh : s.pileHolding y with
    | none => simp [tabToTabR, hh] at h
    | some c => exact ⟨c, rfl⟩
  have hcp : s.canPlace y base = true := by
    by_cases hcp : s.canPlace y base = true
    · exact hcp
    · simp [tabToTabR, hc, hcp] at h
  have hcond : below y (s.piles c).faceUp ≠ [] ∨
      ((s.piles c).hidden = [] ∧ y.rank = Rank.king) := by
    by_cases hp : below y (s.piles c).faceUp = []
    · right
      have hh : (s.piles c).hidden = [] := by
        by_cases hh : (s.piles c).hidden = []
        · exact hh
        · cases hhid : (s.piles c).hidden with
          | nil => exact absurd hhid hh
          | cons g gs =>
              simp [tabToTabR, hc, hcp, hp, hhid] at h
      have hk : y.rank = Rank.king := by
        have hdec : decide (y.rank = Rank.king) = true := by
          simpa [tabToTabR, hc, hcp, hp, hh] using h
        exact of_decide_eq_true hdec
      exact ⟨hh, hk⟩
    · left; exact hp
  obtain ⟨c', hc', hcond'⟩ :=
    tabToTab_condition_splice hwf hx hxt ha hb hab hyx hyt hc hcond
  have hcpS := canPlace_splice hwf hx hxt ha hb hab hcp
  unfold tabToTabR
  rw [hc']
  simp only []
  rw [hcpS]
  simp only []
  rcases hcond' with hb' | ⟨hhid, hking⟩
  · cases hbelow : below y ((s.spliceTwinRuns x).piles c').faceUp with
    | nil => exact absurd hbelow hb'
    | cons hd tl => rfl
  · cases hbelow : below y ((s.spliceTwinRuns x).piles c').faceUp with
    | nil => simp [hhid, hking]
    | cons hd tl => rfl
theorem reversibleAtW_splice_tabToFound {s : State} {x y : Card} {a b : Anchor}
    (hwf : s.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (ha : s.pileHolding x = some a) (hb : s.pileHolding x.twin = some b)
    (hab : a ≠ b) (hyx : y ≠ x) (hyt : y ≠ x.twin)
    (hrev : reversibleAtW s (Move.tabToFound y)) :
    reversibleAtW (s.spliceTwinRuns x) (Move.tabToFound y) := by
  have hR : tabToFoundR s y = true :=
    (tabToFoundR_iff_reversibleAtW hwf y).mpr hrev
  have hRS := tabToFoundR_splice hwf hx hxt ha hb hab hyx hyt hR
  have hwfS : (s.spliceTwinRuns x).WF := wf_spliceTwinRuns hwf hx hxt
  exact (reversibleOf_iff_reversibleAtW hwfS (Move.tabToFound y)).mp
    (by simpa [reversibleOf] using hRS)

theorem reversibleAtW_splice_tabToTab {s : State} {x y : Card} {a b : Anchor} {base : Base}
    (hwf : s.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (ha : s.pileHolding x = some a) (hb : s.pileHolding x.twin = some b)
    (hab : a ≠ b) (hyx : y ≠ x) (hyt : y ≠ x.twin)
    (hrev : reversibleAtW s (Move.tabToTab y base)) :
    reversibleAtW (s.spliceTwinRuns x) (Move.tabToTab y base) := by
  have hR : tabToTabR s y base = true :=
    (tabToTabR_iff_reversibleAtW hwf y base).mpr hrev
  have hRS := tabToTabR_splice hwf hx hxt ha hb hab hyx hyt hR
  have hwfS : (s.spliceTwinRuns x).WF := wf_spliceTwinRuns hwf hx hxt
  exact (reversibleOf_iff_reversibleAtW hwfS (Move.tabToTab y base)).mp
    (by simpa [reversibleOf] using hRS)

theorem hidden_eq_of_rev_step {u v : State} {m : Move}
    (hwf : u.WF) (hstep : State.step u m = some v)
    (hrev : reversibleAtW u m) :
    ∀ a : Anchor, (v.piles a).hidden = (u.piles a).hidden := by
  intro a
  cases m with
  | draw => rw [stepDraw_piles hstep]
  | wasteToFound x =>
      obtain ⟨-, y, ys, -, hs⟩ := step_wasteToFound_inv hstep
      rw [hs]
      rfl
  | wasteToTab x base =>
      exact absurd hrev (wasteToTab_not_reversibleAtW u x base)
  | tabToFound x =>
      obtain ⟨hnxt, a', hpa, hs⟩ := step_tabToFound_inv hstep
      rw [hs]
      dsimp only
      by_cases ha : a = a'
      · rw [ite_eq_left ha, ha]
        rcases afterRunRemoved_hidden (u.piles a') (chop (u.piles a').faceUp) with
          ⟨-, h⟩ | ⟨-, hhid0, h⟩ | ⟨hchop, hhidne, -⟩
        · exact h
        · exact h
        · exfalso
          have hR : tabToFoundR u x = true :=
            (tabToFoundR_iff_reversibleAtW hwf x).mpr hrev
          cases hh : (u.piles a').hidden with
          | nil => exact hhidne hh
          | cons g gs =>
              simp only [tabToFoundR, hnxt, hpa, hchop, hh] at hR
              exact Bool.noConfusion hR
      · rw [ite_eq_right ha]
  | foundToTab x base =>
      obtain ⟨c', htop, hc'c, hcp, hs⟩ := step_foundToTab_inv hstep
      rw [hs]
      exact putCard_hidden_eq
        (st := u.setFound x.suit (chop (u.found x.suit)))
        (c := x) (b := base) hcp a
  | tabToTab x base =>
      exact ((tfa_slide_conserves hwf hstep hrev).1.1 a).symm

theorem seatOf_tabToFound_mover_none {u v : State} {y : Card}
    (hwf : u.WF) (hstep : State.step u (Move.tabToFound y) = some v) :
    seatOf v y = none := by
  obtain ⟨-, a, hpa, hs⟩ := step_tabToFound_inv hstep
  have hfound : y ∈ v.found y.suit := by
    have h1 := (tabToFound_found_trio hs).1
    rw [h1]
    simp
  have hwv : v.WF := step_wf hwf hstep
  apply tfc_seatOf_none
  apply tfc_pileHolding_none
  intro j hmem
  exact wf_pile_found_ne hwv (by simpa [pileZone] using List.mem_append_right _ hmem) hfound

theorem seatOf_foundToTab_mover {u v : State} {y : Card} {base : Base}
    (hwf : u.WF) (hstep : State.step u (Move.foundToTab y base) = some v) :
    seatOf v y = some base := by
  obtain ⟨c', htop, hc'c, hcp, hs⟩ := step_foundToTab_inv hstep
  have hyfound : y ∈ u.found y.suit := by
    have hmem := lastOf_mem htop
    simpa [hc'c] using hmem
  have hynopile : ∀ j, y ∉ (u.piles j).faceUp :=
    fun j hmem => wf_pile_found_ne hwf (by simpa [pileZone] using List.mem_append_right _ hmem) hyfound
  rw [hs]
  have hpiles := KingFuel.kf_setFound_putCard_piles u y.suit (chop (u.found y.suit)) y base
  rw [show seatOf ((u.setFound y.suit (chop (u.found y.suit))).putCard y base) y =
      seatOf (u.putCard y base) y from seatOf_congr_piles hpiles y]
  cases base with
  | inl a =>
      rw [putCard_eq_inl]
      refine tfc_seatOf_inl_intro (a := a) ?_ ?_
      · refine tfc_pileHolding_pin ?_ ?_
        · rw [setPile_piles_self]; simp
        · intro j hj
          rw [setPile_piles_ne hj]
          exact hynopile j
      · rw [setPile_piles_self]
        simp [below_cons]
  | inr z =>
      obtain ⟨k, hk, hfit⟩ := canPlace_inr hcp
      rw [putCard_inr_eq hk]
      refine tfc_seatOf_inr_intro (a := k) ?_ ?_
      · refine tfc_pileHolding_pin ?_ ?_
        · rw [setPile_piles_self]; simp
        · intro j hj
          rw [setPile_piles_ne hj]
          exact hynopile j
      · rw [setPile_piles_self]
        rw [below_append_eq (A := (u.piles k).faceUp) (B := [y]) (hynopile k)]
        simp only [below_cons, ite_true, List.append_nil]
        exact (tfc_pileOfTop_top hk).2
theorem reversibleAtW_splice_foundToTab {s : State} {x y : Card} {a b : Anchor} {base : Base}
    (hwf : s.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (ha : s.pileHolding x = some a) (hb : s.pileHolding x.twin = some b)
    (hab : a ≠ b)
    (hrev : reversibleAtW s (Move.foundToTab y base)) :
    reversibleAtW (s.spliceTwinRuns x) (Move.foundToTab y base) := by
  have hR : foundToTabR s y base = true :=
    (foundToTabR_iff_reversibleAtW hwf y base).mpr hrev
  have hfound : (s.spliceTwinRuns x).found = s.found := spliceTwinRuns_found ha hb hab
  have hcp : s.canPlace y base = true := by
    have hR0 := hR
    unfold foundToTabR at hR0
    cases htop : s.foundTop y.suit with
    | none => simp [htop] at hR0
    | some c' =>
        by_cases hcy : c' = y
        · simpa [htop, hcy] using hR0
        · simp [htop, hcy] at hR0
  have hcpS := canPlace_splice hwf hx hxt ha hb hab hcp
  have hRS : foundToTabR (s.spliceTwinRuns x) y base = true := by
    unfold foundToTabR
    rw [show (s.spliceTwinRuns x).foundTop y.suit = s.foundTop y.suit by
      unfold State.foundTop
      rw [hfound]]
    cases htop : s.foundTop y.suit with
    | none => simp [foundToTabR, htop] at hR
    | some c' =>
        by_cases hcy : c' = y
        · simp [hcy, hcpS]
        · simp [foundToTabR, htop, hcy] at hR
  have hwfS : (s.spliceTwinRuns x).WF := wf_spliceTwinRuns hwf hx hxt
  exact (reversibleOf_iff_reversibleAtW hwfS (Move.foundToTab y base)).mp
    (by simpa [reversibleOf] using hRS)

theorem spliceTwinRuns_hidden {s : State} {x : Card} {a b : Anchor}
    (ha : s.pileHolding x = some a) (hb : s.pileHolding x.twin = some b)
    (hab : a ≠ b) :
    ∀ a', ((s.spliceTwinRuns x).piles a').hidden = (s.piles a').hidden := by
  intro a'
  by_cases h1 : a' = a
  · rw [h1, spliceTwinRuns_piles_self ha hb hab]
  · by_cases h2 : a' = b
    · rw [h2, spliceTwinRuns_piles_second ha hb hab]
    · rw [spliceTwinRuns_piles_other ha hb hab h1 h2]

private theorem holding_none_of_seat_none {st : State} {c : Card}
    (h : seatOf st c = none) : st.pileHolding c = none := by
  cases hh : st.pileHolding c with
  | none => rfl
  | some a =>
      rw [tfc_seatOf_pair hh] at h
      cases hg : List.getLast? (below c (st.piles a).faceUp) <;> simp [hg] at h

theorem raise_seat_none {u v : State} {d y : Card} {a : Anchor}
    (hwf : u.WF) (hstep : State.step u (Move.tabToFound d) = some v)
    (hrev : reversibleAtW u (Move.tabToFound d))
    (hpa : u.pileOfTop d = some a)
    (hseat : seatOf u y = none) (_hyd : y ≠ d) :
    seatOf v y = none := by
  have hnone : u.pileHolding y = none := holding_none_of_seat_none hseat
  have hnotmem : ∀ a', y ∉ (u.piles a').faceUp :=
    fun a' => tfc_not_mem_faceUp_of_holdNone hnone a'
  obtain ⟨-, a', hpa', hv⟩ := step_tabToFound_inv hstep
  have hae : a' = a := pileOfTop_inj hpa' hpa
  rw [hae] at hv
  rw [hv]
  apply tfc_seatOf_none
  apply tfc_pileHolding_none
  intro a' hm
  dsimp only at hm
  by_cases ha' : a' = a
  · rw [ite_eq_left ha'] at hm
    by_cases hchop : chop (u.piles a).faceUp = []
    · have hR : tabToFoundR u d = true :=
        (tabToFoundR_iff_reversibleAtW hwf d).mpr hrev
      have hnext : u.nextUp d = true := by
        by_cases hn : u.nextUp d = true
        · exact hn
        · simp [tabToFoundR, hn] at hR
      have hhid : (u.piles a).hidden = [] := by
        by_cases hh : (u.piles a).hidden = []
        · exact hh
        · exfalso
          cases hhid : (u.piles a).hidden with
          | nil => exact hh hhid
          | cons g gs =>
              simp [tabToFoundR, hnext, hpa, hchop, hhid] at hR
      simp [Pile.afterRunRemoved, hchop, hhid, Pile.revealTop] at hm
    · rw [afterRunRemoved_faceUp_ne hchop] at hm
      exact hnotmem a (chop_mem hm)
  · rw [ite_eq_right ha'] at hm
    exact hnotmem a' hm
theorem stepDraw_splice {s t : State} {x : Card} {a b : Anchor}
    (ha : s.pileHolding x = some a) (hb : s.pileHolding x.twin = some b)
    (hab : a ≠ b) (h : s.stepDraw = some t) :
    (s.spliceTwinRuns x).stepDraw = some (t.spliceTwinRuns x) := by
  rw [spliceTwinRuns_as_update ha hb hab, stepDraw_with_piles, h]
  apply congrArg some
  have ht_piles : t.piles = s.piles := stepDraw_piles h
  have ht_found : t.found = s.found := stepDraw_found h
  have ht_ds : t.drawStep = s.drawStep := draw_drawStep h
  have ha_t : t.pileHolding x = some a := by
    rw [pileHolding_congr ht_piles]
    exact ha
  have hb_t : t.pileHolding x.twin = some b := by
    rw [pileHolding_congr ht_piles]
    exact hb
  apply State.ext
  · funext su
    rw [spliceTwinRuns_found ha_t hb_t hab, ht_found]
  · exact spliceTwinRuns_piles_congr ht_piles.symm
  · exact (spliceTwinRuns_stock ha_t hb_t hab).symm
  · exact (spliceTwinRuns_waste ha_t hb_t hab).symm
  · rw [spliceTwinRuns_drawStep ha_t hb_t hab, ht_ds]
/-! ## §6. The main commutation -/

theorem splice_step_comm_rev {s t : State} {x : Card} {m : Move}
    (hwf : s.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (hstep : State.step s m = some t)
    (hrev : reversibleAtW s m)
    (hno : NotFoundPair x m) :
    State.step (s.spliceTwinRuns x) (Move.relabelMover x m) = some (t.spliceTwinRuns x) := by
  obtain ⟨a, b, z, ha, hb, hab, hza, hzb⟩ := splice_setup hwf hx hxt
  have hxmem : x ∈ (s.piles a).faceUp := pileHolding_mem ha
  have htmem : x.twin ∈ (s.piles b).faceUp := pileHolding_mem hb
  have hwfS : (s.spliceTwinRuns x).WF := wf_spliceTwinRuns hwf hx hxt
  have htwf : t.WF := step_wf hwf hstep
  have hSself : seatOf (s.spliceTwinRuns x) x = seatOf s x.twin :=
    seatOf_splice_self hwf ha hb hab
  have hStwin : seatOf (s.spliceTwinRuns x) x.twin = seatOf s x :=
    seatOf_splice_twin hwf ha hb hab
  have hse_x : seatOf s x ≠ none := by
    obtain ⟨z, hz⟩ := hx; rw [hz]; simp
  have hse_xt : seatOf s x.twin ≠ none := by
    obtain ⟨z, hz⟩ := hxt; rw [hz]; simp
  cases m with
  | draw =>
      exact stepDraw_splice ha hb hab hstep
  | wasteToFound y =>
      exact absurd hrev (wasteToFound_not_reversibleAtW s y)
  | wasteToTab y base =>
      exact absurd hrev (wasteToTab_not_reversibleAtW s y base)
  | tabToFound y =>
      have hnoI := (notFoundPair_iff_not_isPairFound x (Move.tabToFound y)).mp hno
      have hyx : y ≠ x := fun h => hnoI (Or.inl (by rw [h]))
      have hyt : y ≠ x.twin := fun h => hnoI (Or.inr (Or.inl (by rw [h])))
      have hrel : Move.relabelMover x (Move.tabToFound y) = Move.tabToFound y := by
        simp [Move.relabelMover, card_relabelTwin_ne hyx hyt]
      rw [hrel]
      have hrevS := reversibleAtW_splice_tabToFound hwf hx hxt ha hb hab hyx hyt hrev
      have hrevS' := hrevS
      obtain ⟨u, play, hu_step, hrun⟩ := hrevS'
      have huwf : u.WF := step_wf hwfS hu_step
      obtain ⟨-, ay, hpay, hs_t⟩ := step_tabToFound_inv hstep
      obtain ⟨-, au, hpaU, hs_u⟩ := step_tabToFound_inv hu_step
      have htx : seatOf t x = seatOf s x :=
        raise_seat_change_of_seated hstep hrev hse_x (Ne.symm hyx)
      have htxt : seatOf t x.twin = seatOf s x.twin :=
        raise_seat_change_of_seated hstep hrev hse_xt (Ne.symm hyt)
      have hseS_x : seatOf (s.spliceTwinRuns x) x ≠ none := by
        rw [hSself]; exact hse_xt
      have hseS_xt : seatOf (s.spliceTwinRuns x) x.twin ≠ none := by
        rw [hStwin]; exact hse_x
      have hux : seatOf u x = seatOf (s.spliceTwinRuns x) x :=
        raise_seat_change_of_seated hu_step hrevS hseS_x (Ne.symm hyx)
      have huxt : seatOf u x.twin = seatOf (s.spliceTwinRuns x) x.twin :=
        raise_seat_change_of_seated hu_step hrevS hseS_xt (Ne.symm hyt)
      have hseat1 : seatOf u x = seatOf t x.twin := by
        rw [hux, hSself, htxt]
      have hseat2 : seatOf u x.twin = seatOf t x := by
        rw [huxt, hStwin, htx]
      have hother : ∀ c, c ≠ x → c ≠ x.twin → seatOf u c = seatOf t c := by
        intro c hcx hcxt
        by_cases hcy : c = y
        · rw [hcy]
          rw [seatOf_tabToFound_mover_none hwfS hu_step,
            seatOf_tabToFound_mover_none hwf hstep]
        · by_cases hcseat : seatOf s c = none
          · have hcseatS : seatOf (s.spliceTwinRuns x) c = none := by
              rw [seatOf_splice_other hwf hcx hcxt]; exact hcseat
            rw [raise_seat_none hwfS hu_step hrevS hpaU hcseatS hcy,
              raise_seat_none hwf hstep hrev hpay hcseat hcy]
          · have hcseatS : seatOf (s.spliceTwinRuns x) c ≠ none := by
              rw [seatOf_splice_other hwf hcx hcxt]; exact hcseat
            rw [raise_seat_change_of_seated hu_step hrevS hcseatS hcy,
              raise_seat_change_of_seated hstep hrev hcseat hcy,
              seatOf_splice_other hwf hcx hcxt]
      have hbf : boardFixed t u := by
        refine ⟨?_, ?_⟩
        · intro a'
          rw [hidden_eq_of_rev_step hwf hstep hrev a',
            hidden_eq_of_rev_step hwfS hu_step hrevS a',
            spliceTwinRuns_hidden ha hb hab a']
        · simp [hs_t, hs_u]
          exact (spliceTwinRuns_drawStep ha hb hab).symm
      have hff : foundsFixed t u := by
        intro su
        simp [hs_t, hs_u, State.setFound, spliceTwinRuns_found ha hb hab]
      have hstock : t.stock = u.stock := by
        simp [hs_t, hs_u]
        exact (spliceTwinRuns_stock ha hb hab).symm
      have hwaste : t.waste = u.waste := by
        simp [hs_t, hs_u]
        exact (spliceTwinRuns_waste ha hb hab).symm
      have hcut : cutOf t = cutOf u := by
        show t.stock.length = u.stock.length
        rw [hstock]
      have hstrict : twinPairSwapStrict t u x :=
        ⟨hseat1, hseat2, hother, hbf, hff, hstock, hwaste, hcut⟩
      have hx_t : ∃ z, seatOf t x = some (Sum.inr z) := by
        rw [htx]; exact hx
      have hxt_t : ∃ z : Card, seatOf t x.twin = some (Sum.inr z.twin) := by
        rw [htxt]; exact hxt
      have hEq : u = t.spliceTwinRuns x :=
        eq_splice_of_twinPairSwapStrict htwf huwf hx_t hxt_t hstrict
      rw [hu_step]
      exact congrArg some hEq
  | foundToTab y base =>
      have hnoI := (notFoundPair_iff_not_isPairFound x (Move.foundToTab y base)).mp hno
      have hyx : y ≠ x := fun h =>
        hnoI (Or.inr (Or.inr (Or.inl ⟨base, by rw [h]⟩)))
      have hyt : y ≠ x.twin := fun h =>
        hnoI (Or.inr (Or.inr (Or.inr ⟨base, by rw [h]⟩)))
      have hrel : Move.relabelMover x (Move.foundToTab y base) = Move.foundToTab y base := by
        simp [Move.relabelMover, card_relabelTwin_ne hyx hyt]
      rw [hrel]
      have hrevS := reversibleAtW_splice_foundToTab hwf hx hxt ha hb hab hrev
      have hrevS' := hrevS
      obtain ⟨u, play, hu_step, hrun⟩ := hrevS'
      have huwf : u.WF := step_wf hwfS hu_step
      obtain ⟨ct, htopt, hct, hcpt, hs_t⟩ := step_foundToTab_inv hstep
      obtain ⟨cu, htopu, hcu, hcpu, hs_u⟩ := step_foundToTab_inv hu_step
      have htx : seatOf t x = seatOf s x :=
        pull_seat_change hstep x (Ne.symm hyx)
      have htxt : seatOf t x.twin = seatOf s x.twin :=
        pull_seat_change hstep x.twin (Ne.symm hyt)
      have hux : seatOf u x = seatOf (s.spliceTwinRuns x) x :=
        pull_seat_change hu_step x (Ne.symm hyx)
      have huxt : seatOf u x.twin = seatOf (s.spliceTwinRuns x) x.twin :=
        pull_seat_change hu_step x.twin (Ne.symm hyt)
      have hseat1 : seatOf u x = seatOf t x.twin := by rw [hux, hSself, htxt]
      have hseat2 : seatOf u x.twin = seatOf t x := by rw [huxt, hStwin, htx]
      have hother : ∀ c, c ≠ x → c ≠ x.twin → seatOf u c = seatOf t c := by
        intro c hcx hcxt
        by_cases hcy : c = y
        · rw [hcy]
          rw [seatOf_foundToTab_mover hwfS hu_step, seatOf_foundToTab_mover hwf hstep]
        · rw [pull_seat_change hu_step c hcy, pull_seat_change hstep c hcy,
            seatOf_splice_other hwf hcx hcxt]
      have hbf : boardFixed t u := by
        refine ⟨?_, ?_⟩
        · intro a'
          have h1 : (t.piles a').hidden = (s.piles a').hidden :=
            hidden_eq_of_rev_step hwf hstep hrev a'
          have h2 : (u.piles a').hidden = (s.piles a').hidden := by
            rw [hidden_eq_of_rev_step hwfS hu_step hrevS a',
              spliceTwinRuns_hidden ha hb hab a']
          exact h1.trans h2.symm
        · rw [hs_t, hs_u]
          rw [putCard_drawStep, putCard_drawStep]
          exact (spliceTwinRuns_drawStep ha hb hab).symm
      have hff : foundsFixed t u := by
        intro su
        rw [hs_t, hs_u, putCard_found, putCard_found]
        simp [State.setFound, spliceTwinRuns_found ha hb hab]
      have hstock : t.stock = u.stock := by
        rw [hs_t, hs_u]
        rw [putCard_stock, putCard_stock]
        exact (spliceTwinRuns_stock ha hb hab).symm
      have hwaste : t.waste = u.waste := by
        rw [hs_t, hs_u]
        rw [putCard_waste, putCard_waste]
        exact (spliceTwinRuns_waste ha hb hab).symm
      have hcut : cutOf t = cutOf u := by
        show t.stock.length = u.stock.length
        rw [hstock]
      have hstrict : twinPairSwapStrict t u x :=
        ⟨hseat1, hseat2, hother, hbf, hff, hstock, hwaste, hcut⟩
      have hx_t : ∃ z, seatOf t x = some (Sum.inr z) := by rw [htx]; exact hx
      have hxt_t : ∃ z : Card, seatOf t x.twin = some (Sum.inr z.twin) := by
        rw [htxt]; exact hxt
      have hEq : u = t.spliceTwinRuns x :=
        eq_splice_of_twinPairSwapStrict htwf huwf hx_t hxt_t hstrict
      rw [hu_step]
      exact congrArg some hEq
  | tabToTab y base =>
      obtain ⟨hyx, hyt⟩ := tabToTab_mover_off hwf hx hxt hstep
      have hrel : Move.relabelMover x (Move.tabToTab y base) = Move.tabToTab y base := by
        simp [Move.relabelMover, card_relabelTwin_ne hyx hyt]
      rw [hrel]
      have hrevS := reversibleAtW_splice_tabToTab hwf hx hxt ha hb hab hyx hyt hrev
      have hrevS' := hrevS
      obtain ⟨u, play, hu_step, hrun⟩ := hrevS'
      have huwf : u.WF := step_wf hwfS hu_step
      have htx : seatOf t x = seatOf s x := by
        have h := tfc_seat_point_edit hwf hstep hrev x
        rwa [ite_eq_right (Ne.symm hyx)] at h
      have htxt : seatOf t x.twin = seatOf s x.twin := by
        have h := tfc_seat_point_edit hwf hstep hrev x.twin
        rwa [ite_eq_right (Ne.symm hyt)] at h
      have hux : seatOf u x = seatOf (s.spliceTwinRuns x) x := by
        have h := tfc_seat_point_edit hwfS hu_step hrevS x
        rwa [ite_eq_right (Ne.symm hyx)] at h
      have huxt : seatOf u x.twin = seatOf (s.spliceTwinRuns x) x.twin := by
        have h := tfc_seat_point_edit hwfS hu_step hrevS x.twin
        rwa [ite_eq_right (Ne.symm hyt)] at h
      have hseat1 : seatOf u x = seatOf t x.twin := by rw [hux, hSself, htxt]
      have hseat2 : seatOf u x.twin = seatOf t x := by rw [huxt, hStwin, htx]
      have hother : ∀ c, c ≠ x → c ≠ x.twin → seatOf u c = seatOf t c := by
        intro c hcx hcxt
        by_cases hcy : c = y
        · rw [hcy]
          rw [tfc_seat_point_edit hwfS hu_step hrevS y,
            tfc_seat_point_edit hwf hstep hrev y]
          simp
        · have h1 := tfc_seat_point_edit hwfS hu_step hrevS c
          have h2 := tfc_seat_point_edit hwf hstep hrev c
          rw [ite_eq_right hcy] at h1 h2
          rw [h1, h2, seatOf_splice_other hwf hcx hcxt]
      have hcons_t := tfa_slide_conserves hwf hstep hrev
      have hcons_u := tfa_slide_conserves hwfS hu_step hrevS
      have hbf : boardFixed t u := by
        refine ⟨?_, ?_⟩
        · intro a'
          rw [(hcons_t.1.1 a').symm, (hcons_u.1.1 a').symm,
            spliceTwinRuns_hidden ha hb hab a']
        · rw [(hcons_t.1.2).symm, (hcons_u.1.2).symm, spliceTwinRuns_drawStep ha hb hab]
      have hff : foundsFixed t u := by
        intro su
        rw [(hcons_t.2.1 su).symm, (hcons_u.2.1 su).symm, spliceTwinRuns_found ha hb hab]
      have ht_stock : t.stock = s.stock := by
        obtain ⟨aT, hholdT, hcpT, hrunneT, hsT⟩ := step_tabToTab_inv hstep
        rw [hsT, putRun_stock, setPile_stock]
      have hu_stock : u.stock = s.stock := by
        obtain ⟨aU, hholdU, hcpU, hrunneU, hsU⟩ := step_tabToTab_inv hu_step
        rw [hsU, putRun_stock, setPile_stock, spliceTwinRuns_stock ha hb hab]
      have hstock : t.stock = u.stock := ht_stock.trans hu_stock.symm
      have ht_waste : t.waste = s.waste := by
        obtain ⟨aT, hholdT, hcpT, hrunneT, hsT⟩ := step_tabToTab_inv hstep
        rw [hsT, putRun_waste, setPile_waste]
      have hu_waste : u.waste = s.waste := by
        obtain ⟨aU, hholdU, hcpU, hrunneU, hsU⟩ := step_tabToTab_inv hu_step
        rw [hsU, putRun_waste, setPile_waste, spliceTwinRuns_waste ha hb hab]
      have hwaste : t.waste = u.waste := ht_waste.trans hu_waste.symm
      have hcut : cutOf t = cutOf u := by
        show t.stock.length = u.stock.length
        rw [hstock]
      have hstrict : twinPairSwapStrict t u x :=
        ⟨hseat1, hseat2, hother, hbf, hff, hstock, hwaste, hcut⟩
      have hx_t : ∃ z, seatOf t x = some (Sum.inr z) := by rw [htx]; exact hx
      have hxt_t : ∃ z : Card, seatOf t x.twin = some (Sum.inr z.twin) := by
        rw [htxt]; exact hxt
      have hEq : u = t.spliceTwinRuns x :=
        eq_splice_of_twinPairSwapStrict htwf huwf hx_t hxt_t hstrict
      rw [hu_step]
      exact congrArg some hEq
end TwinSpliceComm


