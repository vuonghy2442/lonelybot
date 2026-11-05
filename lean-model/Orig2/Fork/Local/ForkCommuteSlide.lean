import Orig2.Fork.Local.ForkCommute

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkCommuteSlide - the slide commutation squares (source)

Additive promotion of the scratch card Temp/SlideAsm_{Kit,Pull,Raise}.lean.
The canonical slide successor slideSt, its normal form (two-pile write),
the search-transfer rows, the one-leg data slide_data, and the two
remaining local squares:

* step_comm_slide_pull - a reversible slide and a reversible pull
  commute (no side condition: the pulled card is founded, hence in no
  pile, hence never inside the slide's run);
* step_comm_slide_raise - a reversible slide and a reversible raise
  commute.  The three overlap cases close: the raise from the slide's
  source either founds the run head (kill: the slide would need a card
  that is already in the foundation) or chops the run at its own top
  card (both orders end at 1 = pre, k1 = f1 ++ w); the raise from
  the slide's target is killed by the burial of the target's top card.

The slide/slide square is NOT stated here: it is false without the side
condition c1 ≠ c2 (the bare-king counterexample, see
Temp/Commute_Slide_Report.md §4).

No sorry, no Classical.choice, no 
ative_decide.
-/

namespace CommuteStep

-- ===== from Temp/SlideAsm_Kit.lean =====

/-! ## 1. Run append algebra -/

/-- `fromCard` ignores a prefix that does not contain its card. -/
theorem fromCard_append_notmem {t : Card} {xs : List Card} (h : t ∉ xs) (l : List Card) :
    fromCard t (xs ++ l) = fromCard t l := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx : x ≠ t := fun heq => h (List.mem_cons.mpr (Or.inl heq.symm))
      have hrest : t ∉ xs := fun hm => h (List.mem_cons.mpr (Or.inr hm))
      rw [List.cons_append, tfc_fromCard_cons, ite_eq_right hx, ih hrest]

/-- `below` stops exactly at the card. -/
theorem below_append_stop {t : Card} {xs ys : List Card} (h : t ∉ xs) :
    below t (xs ++ t :: ys) = xs := by
  rw [below_append_notmem h, below_cons_self, List.append_nil]

/-- `fromCard` starts exactly at the card. -/
theorem fromCard_append_stop {t : Card} {xs ys : List Card} (h : t ∉ xs) :
    fromCard t (xs ++ t :: ys) = t :: ys := by
  rw [fromCard_append_notmem h, fromCard_head_eq]

/-- `fromCard` cuts at the card, so a right extension is appended. -/
theorem fromCard_append_of_mem {c : Card} {l m : List Card} (h : c ∈ l) :
    fromCard c (l ++ m) = fromCard c l ++ m := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons x t ih =>
      by_cases hxc : x = c
      · subst hxc
        rw [List.cons_append, tfc_fromCard_cons, ite_eq_left rfl, tfc_fromCard_cons,
          ite_eq_left rfl, List.cons_append]
      · have hct : c ∈ t := (List.mem_cons.mp h).resolve_left (fun h' => hxc h'.symm)
        rw [List.cons_append, tfc_fromCard_cons, ite_eq_right hxc, tfc_fromCard_cons,
          ite_eq_right hxc]
        rw [ih hct]

/-- `below` only sees what is left of the card, so a right extension is
invisible. -/
theorem below_append_of_mem {c : Card} {l m : List Card} (h : c ∈ l) :
    below c (l ++ m) = below c l := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons x t ih =>
      by_cases hxc : x = c
      · subst hxc
        rw [List.cons_append, below_cons, ite_eq_left rfl, below_cons, ite_eq_left rfl]
      · have hct : c ∈ t := (List.mem_cons.mp h).resolve_left (fun h' => hxc h'.symm)
        rw [List.cons_append, below_cons, ite_eq_right hxc, below_cons, ite_eq_right hxc]
        rw [ih hct]

/-- A card not in `l` is `below` all of it. -/
theorem below_eq_self_of_not_mem {c : Card} {l : List Card} (h : c ∉ l) :
    below c l = l := by
  induction l with
  | nil => rfl
  | cons x t ih =>
      have hx : x ≠ c := fun heq => h (List.mem_cons.mpr (Or.inl heq.symm))
      have ht : c ∉ t := fun hm => h (List.mem_cons.mpr (Or.inr hm))
      rw [below_cons, ite_eq_right hx, ih ht]

/-- The last of a nonempty right part. -/
theorem lastOf_append_of_ne_nil {l m : List Card} (hm : m ≠ []) :
    lastOf (l ++ m) = lastOf m := by
  induction l with
  | nil => rfl
  | cons x t ih =>
      cases m with
      | nil => exact absurd rfl hm
      | cons y ys =>
          cases t with
          | nil =>
              cases ys with
              | nil => rfl
              | cons z zs => rfl
          | cons w ws =>
              rw [List.cons_append]
              exact ih

/-- The `chop`-edited pile's face-up run is a sub-run of the original. -/
theorem mem_afterRunRemoved_chop_faceUp {p : Pile} {x : Card}
    (h : x ∈ (p.afterRunRemoved (chop p.faceUp)).faceUp) :
    x ∈ p.faceUp ∨ x ∈ p.hidden := by
  cases p with
  | mk hid fu =>
      cases fu with
      | nil =>
          cases hid with
          | nil => exact absurd h List.not_mem_nil
          | cons g gs =>
              have hx : x = g := by
                simpa [Pile.afterRunRemoved, Pile.revealTop, chop] using h
              exact Or.inr (by rw [hx]; exact List.mem_cons_self ..)
      | cons y t =>
          cases t with
          | nil =>
              cases hid with
              | nil => exact absurd h List.not_mem_nil
              | cons g gs =>
                  have hx : x = g := by
                    simpa [Pile.afterRunRemoved, Pile.revealTop, chop] using h
                  exact Or.inr (by rw [hx]; exact List.mem_cons_self ..)
          | cons z zs =>
              have h' : x ∈ y :: chop (z :: zs) := by
                simpa [Pile.afterRunRemoved, chop] using h
              rcases List.mem_cons.mp h' with hxy | hcx
              · exact Or.inl (by rw [hxy]; exact List.mem_cons_self ..)
              · exact Or.inl (List.mem_cons.mpr (Or.inr (chop_mem hcx)))

/-- The `chop`-edited pile's hidden deck stays in the original zone. -/
theorem mem_afterRunRemoved_chop_hidden {p : Pile} {x : Card}
    (h : x ∈ (p.afterRunRemoved (chop p.faceUp)).hidden) :
    x ∈ p.hidden ++ p.faceUp := by
  cases p with
  | mk hid fu =>
      cases fu with
      | nil =>
          cases hid with
          | nil => exact absurd h List.not_mem_nil
          | cons g gs =>
              simp only [chop, Pile.afterRunRemoved, Pile.revealTop] at h
              exact List.mem_append.mpr (Or.inl (List.mem_cons.mpr (Or.inr h)))
      | cons y t =>
          cases t with
          | nil =>
              cases hid with
              | nil => exact absurd h List.not_mem_nil
              | cons g gs =>
                  simp only [chop, Pile.afterRunRemoved, Pile.revealTop] at h
                  exact List.mem_append.mpr (Or.inl (List.mem_cons.mpr (Or.inr h)))
          | cons z zs =>
              simp only [chop, Pile.afterRunRemoved] at h
              exact List.mem_append.mpr (Or.inl h)

/-- Membership in the `chop`-edited pile's zone is membership in the
original zone. -/
theorem mem_afterRunRemoved_chop_zone {p : Pile} {x : Card}
    (hx : x ∈ (p.afterRunRemoved (chop p.faceUp)).hidden
        ++ (p.afterRunRemoved (chop p.faceUp)).faceUp) :
    x ∈ p.hidden ++ p.faceUp := by
  rcases List.mem_append.mp hx with h' | h'
  · exact mem_afterRunRemoved_chop_hidden h'
  · rcases mem_afterRunRemoved_chop_faceUp h' with h'' | h''
    · exact List.mem_append.mpr (Or.inr h'')
    · exact List.mem_append.mpr (Or.inl h'')

/-! ## 2. The reversible leg never reveals -/

/-- At a reversible slide with company beneath (`pre ≠ []`) or a bare
king seat (empty hidden), the edited source pile is exactly the input
pile with `faceUp` replaced by `pre`. -/
theorem afterRunRemoved_eq_faceUp {p : Pile} {pre : List Card}
    (h : pre ≠ [] ∨ (pre = [] ∧ p.hidden = [])) :
    p.afterRunRemoved pre = { p with faceUp := pre } := by
  rcases h with hne | ⟨h0, hhid⟩
  · rw [afterRunRemoved_ne hne]
  · subst h0
    cases p with
    | mk hid fu =>
        have hh : hid = [] := hhid
        subst hh
        rfl

theorem setPile_afterRunRemoved_pileOfTop {st : State} (hwf : st.WF)
    {z : Card} {k a : Anchor} (hk : st.pileOfTop z = some k) (hak : k ≠ a)
    (c : Card) :
    (st.setPile a ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp))).pileOfTop z
      = some k := by
  obtain ⟨-, hzlast⟩ := pileOfTop_top hk
  have hzmem : z ∈ (st.piles k).faceUp := lastOf_mem hzlast
  have huniq := mem_faceUp_unique hwf hzmem a (Ne.symm hak)
  have hznot : ∀ j : Anchor, j ≠ k → (st.piles j).top ≠ some z := by
    intro j hj ht
    exact (mem_faceUp_unique hwf hzmem j hj).1 (Pile.mem_of_top ht)
  have hedit : ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp)).top
      ≠ some z := by
    intro ht
    have hzone : z ∈ (st.piles a).hidden ++ (st.piles a).faceUp :=
      tfc_mem_afterRunRemoved_below_zone (x := z) (c := c)
        (List.mem_append.mpr (Or.inr (Pile.mem_of_top ht)))
    rcases List.mem_append.mp hzone with hh | hh
    · exact huniq.2.1 hh
    · exact huniq.1 hh
  show firstWhere (fun a' => decide ((st.setPile a
      ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp))).topOf a' = some z))
    Anchor.all = some k
  refine firstWhere_find (Anchor.mem_all k) ?_ ?_
  · show decide ((st.setPile a
      ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp))).topOf k = some z) = true
    have hp : (st.setPile a
        ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp))).piles k = st.piles k :=
      setPile_piles_ne hak
    have htop : (st.setPile a
        ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp))).topOf k
        = (st.piles k).top := by
      show ((st.setPile a
        ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp))).piles k).top
        = (st.piles k).top
      rw [hp]
    rw [htop, show (st.piles k).top = some z from (pileOfTop_eq_some_iff hwf).mp hk]
    exact decide_eq_true rfl
  · intro x _ hxk
    show decide ((st.setPile a
      ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp))).topOf x = some z) = false
    apply decide_false_of_not
    intro ht
    by_cases hxa : x = a
    · rw [hxa] at ht
      have ht' : ((st.setPile a
          ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp))).piles a).top
          = some z := ht
      rw [setPile_piles_self] at ht'
      exact hedit ht'
    · have htop : (st.setPile a
          ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp))).topOf x
          = (st.piles x).top := by
        show ((st.setPile a
          ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp))).piles x).top
          = (st.piles x).top
        rw [setPile_piles_ne hxa]
      rw [htop] at ht
      exact hznot x hxk ht

/-! ## 3b. Pile-map congruence -/

theorem topOf_congr_piles {u v : State} (hp : u.piles = v.piles) (a : Anchor) :
    u.topOf a = v.topOf a := by
  show (u.piles a).top = (v.piles a).top
  rw [hp]

theorem pileOfTop_congr_piles {u v : State} (hp : u.piles = v.piles) (z : Card) :
    u.pileOfTop z = v.pileOfTop z := by
  show firstWhere (fun a => decide (u.topOf a = some z)) Anchor.all
      = firstWhere (fun a => decide (v.topOf a = some z)) Anchor.all
  have h : (fun a => decide (u.topOf a = some z))
      = (fun a => decide (v.topOf a = some z)) := by
    funext a
    rw [topOf_congr_piles hp a]
  rw [h]

theorem canPlace_congr_piles {u v : State} (hp : u.piles = v.piles) (c : Card) (b : Base) :
    u.canPlace c b = v.canPlace c b := by
  cases b with
  | inl a =>
      show ((u.piles a).isEmpty && decide (c.rank = Rank.king))
        = ((v.piles a).isEmpty && decide (c.rank = Rank.king))
      rw [show u.piles a = v.piles a from congrFun hp a]
  | inr z =>
      show (match u.pileOfTop z with
          | some _ => canSitOn c z
          | none => false)
        = (match v.pileOfTop z with
          | some _ => canSitOn c z
          | none => false)
      rw [pileOfTop_congr_piles hp z]

/-- A unique topping pile is found. -/
theorem pileOfTop_of_top_unique {u : State} {z : Card} {k : Anchor}
    (htop : (u.piles k).top = some z)
    (hno : ∀ j : Anchor, j ≠ k → (u.piles j).top ≠ some z) :
    u.pileOfTop z = some k := by
  show firstWhere (fun a => decide (u.topOf a = some z)) Anchor.all = some k
  refine firstWhere_find (Anchor.mem_all k) ?_ ?_
  · show decide ((u.piles k).top = some z) = true
    rw [htop]; exact decide_eq_true rfl
  · intro x _ hxk
    apply decide_false_of_not
    exact hno x hxk

theorem pileOfTop_none_of_no_top {u : State} {z : Card}
    (hno : ∀ j : Anchor, (u.piles j).top ≠ some z) :
    u.pileOfTop z = none := by
  show firstWhere (fun a => decide (u.topOf a = some z)) Anchor.all = none
  refine tfc_firstWhere_none Anchor.all ?_
  intro y _
  apply decide_false_of_not
  exact hno y

/-! ## 4. The canonical slide successor -/

/-- The canonical `.tabToTab` successor at a legal slide. -/
def slideSt (u : State) (c : Card) (b : Base) (a : Anchor) : State :=
  (u.setPile a
      (Pile.afterRunRemoved (u.piles a) (below c (u.piles a).faceUp))).putRun
    (fromCard c (u.piles a).faceUp) b

theorem slideSt_found (u : State) (c : Card) (b : Base) (a : Anchor) :
    (slideSt u c b a).found = u.found := by
  rw [slideSt, putRun_found, setPile_found]

theorem slideSt_stock (u : State) (c : Card) (b : Base) (a : Anchor) :
    (slideSt u c b a).stock = u.stock := by
  rw [slideSt, putRun_stock, setPile_stock]

theorem slideSt_waste (u : State) (c : Card) (b : Base) (a : Anchor) :
    (slideSt u c b a).waste = u.waste := by
  rw [slideSt, putRun_waste, setPile_waste]

theorem slideSt_drawStep (u : State) (c : Card) (b : Base) (a : Anchor) :
    (slideSt u c b a).drawStep = u.drawStep := by
  rw [slideSt, putRun_drawStep, setPile_drawStep]

theorem putRun_piles_congr {u v : State} (hp : u.piles = v.piles) (run : List Card) (b : Base) :
    (u.putRun run b).piles = (v.putRun run b).piles := by
  cases b with
  | inl a => rw [putRun_piles_inl, putRun_piles_inl, hp]
  | inr z =>
      have hpq : u.pileOfTop z = v.pileOfTop z := pileOfTop_congr_piles hp z
      cases hz : u.pileOfTop z with
      | none =>
          have hz' : v.pileOfTop z = none := by rw [← hpq]; exact hz
          simp only [State.putRun, hz, hz', hp]
      | some k =>
          have hz' : v.pileOfTop z = some k := by rw [← hpq]; exact hz
          rw [putRun_piles_inr _ _ _ _ hz, putRun_piles_inr _ _ _ _ hz', hp]

theorem step_tabToTab_slideSt {u s : State} {c : Card} {b : Base}
    (hs : State.step u (Move.tabToTab c b) = some s) :
    ∃ a, u.pileHolding c = some a ∧ u.canPlace c b = true ∧
      fromCard c (u.piles a).faceUp ≠ [] ∧ s = slideSt u c b a := by
  obtain ⟨a, hh, hcp, hne, hs'⟩ := step_tabToTab_inv hs
  exact ⟨a, hh, hcp, hne, by rw [hs']; rfl⟩

/-! ## 5. The slide's three pile values -/

/-- The source pile after the slide. -/
theorem slideSt_piles_source {st : State} {c : Card} {b : Base} {a k : Anchor}
    (hwf : st.WF) (hcp : st.canPlace c b = true) (hk : tgt st b = some k)
    (hak : k ≠ a)
    (hcell : below c (st.piles a).faceUp ≠ [] ∨
      (below c (st.piles a).faceUp = [] ∧ (st.piles a).hidden = [])) :
    (slideSt st c b a).piles a =
      { st.piles a with faceUp := below c (st.piles a).faceUp } := by
  have hQ : (st.piles a).afterRunRemoved (below c (st.piles a).faceUp)
      = { st.piles a with faceUp := below c (st.piles a).faceUp } :=
    afterRunRemoved_eq_faceUp hcell
  cases b with
  | inl k' =>
      obtain rfl : k = k' := (Option.some.inj hk).symm
      rw [slideSt, putRun_piles_inl]
      show (if a = k then ({ hidden := [], faceUp := fromCard c (st.piles a).faceUp } : Pile)
        else (st.setPile a ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp))).piles a)
        = { st.piles a with faceUp := below c (st.piles a).faceUp }
      rw [ite_eq_right (Ne.symm hak), setPile_piles_self, hQ]
  | inr z =>
      have hz : st.pileOfTop z = some k := hk
      rw [slideSt, putRun_piles_inr _ _ _ _
        (setPile_afterRunRemoved_pileOfTop hwf hz hak c)]
      show (if a = k then _ else
        (st.setPile a ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp))).piles a)
        = { st.piles a with faceUp := below c (st.piles a).faceUp }
      rw [ite_eq_right (Ne.symm hak), setPile_piles_self, hQ]

/-- The target pile after the slide. -/
theorem slideSt_piles_target {st : State} {c : Card} {b : Base} {a k : Anchor}
    (hwf : st.WF) (hcp : st.canPlace c b = true) (hk : tgt st b = some k)
    (hak : k ≠ a)
    (hcell : below c (st.piles a).faceUp ≠ [] ∨
      (below c (st.piles a).faceUp = [] ∧ (st.piles a).hidden = [])) :
    (slideSt st c b a).piles k =
      { st.piles k with faceUp := (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp } := by
  have hQ : (st.piles a).afterRunRemoved (below c (st.piles a).faceUp)
      = { st.piles a with faceUp := below c (st.piles a).faceUp } :=
    afterRunRemoved_eq_faceUp hcell
  cases b with
  | inl k' =>
      obtain rfl : k = k' := (Option.some.inj hk).symm
      rw [slideSt, putRun_piles_inl]
      show (if k = k then ({ hidden := [], faceUp := fromCard c (st.piles a).faceUp } : Pile)
        else (st.setPile a ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp))).piles k)
        = { st.piles k with faceUp := (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp }
      rw [ite_eq_left rfl]
      obtain ⟨hhid, hfu⟩ := (Pile.isEmpty_eq _).mp ((canPlace_inl hcp).1)
      show ({ hidden := [], faceUp := fromCard c (st.piles a).faceUp } : Pile)
        = ({ hidden := (st.piles k).hidden,
             faceUp := (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp } : Pile)
      rw [hhid, hfu, List.nil_append]
  | inr z =>
      have hz : st.pileOfTop z = some k := hk
      rw [slideSt, putRun_piles_inr _ _ _ _
        (setPile_afterRunRemoved_pileOfTop hwf hz hak c)]
      show (if k = k then _ else
        (st.setPile a ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp))).piles k)
        = { st.piles k with faceUp := (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp }
      rw [ite_eq_left rfl]
      rw [show (st.setPile a ((st.piles a).afterRunRemoved
            (below c (st.piles a).faceUp))).piles k = st.piles k from
        setPile_piles_ne hak]

/-- Every third pile is untouched. -/
theorem slideSt_piles_other {st : State} {c : Card} {b : Base} {a k : Anchor}
    (hwf : st.WF) (hcp : st.canPlace c b = true) (hk : tgt st b = some k)
    (hak : k ≠ a)
    (hcell : below c (st.piles a).faceUp ≠ [] ∨
      (below c (st.piles a).faceUp = [] ∧ (st.piles a).hidden = []))
    {j : Anchor} (hja : j ≠ a) (hjk : j ≠ k) :
    (slideSt st c b a).piles j = st.piles j := by
  cases b with
  | inl k' =>
      obtain rfl : k = k' := (Option.some.inj hk).symm
      rw [slideSt, putRun_piles_inl]
      show (if j = k then _ else
        (st.setPile a ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp))).piles j)
        = st.piles j
      rw [ite_eq_right hjk, setPile_piles_ne hja]
  | inr z =>
      have hz : st.pileOfTop z = some k := hk
      rw [slideSt, putRun_piles_inr _ _ _ _
        (setPile_afterRunRemoved_pileOfTop hwf hz hak c)]
      show (if j = k then _ else
        (st.setPile a ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp))).piles j)
        = st.piles j
      rw [ite_eq_right hjk, setPile_piles_ne hja]

/-- **The single pointwise normal form of a slide.** -/
theorem slideSt_piles_at {st : State} {c : Card} {b : Base} {a k : Anchor}
    (hwf : st.WF) (hcp : st.canPlace c b = true) (hk : tgt st b = some k)
    (hak : k ≠ a)
    (hcell : below c (st.piles a).faceUp ≠ [] ∨
      (below c (st.piles a).faceUp = [] ∧ (st.piles a).hidden = []))
    (j : Anchor) :
    (slideSt st c b a).piles j =
      (if j = a then { st.piles a with faceUp := below c (st.piles a).faceUp }
       else if j = k then
         { st.piles k with faceUp := (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp }
       else st.piles j) := by
  by_cases hja : j = a
  · subst hja
    rw [ite_eq_left rfl]
    exact slideSt_piles_source hwf hcp hk hak hcell
  · by_cases hjk : j = k
    · subst hjk
      rw [ite_eq_right hja, ite_eq_left rfl]
      exact slideSt_piles_target hwf hcp hk hak hcell
    · rw [ite_eq_right hja, ite_eq_right hjk]
      exact slideSt_piles_other hwf hcp hk hak hcell hja hjk

/-! ## 6. Search transfer across `putRun` / `putCard` / `pullSt` -/

theorem putCard_inl_pileOfTop_ne {u : State} (hwf : u.WF) {c : Card} {a : Anchor}
    (hfound : c ∈ u.found c.suit) {z : Card} {m : Anchor}
    (hz : u.pileOfTop z = some m) (ham : a ≠ m) :
    (u.putCard c (Sum.inl a)).pileOfTop z = some m := by
  have hzmem : z ∈ (u.piles m).faceUp := lastOf_mem (pileOfTop_top hz).2
  have htopm : (u.piles m).top = some z := (pileOfTop_eq_some_iff hwf).mp hz
  have hcz : c ≠ z := by
    intro h
    exact ((mem_found_unique hwf hfound).1 m).2 (h ▸ hzmem)
  have hno : ∀ j : Anchor, j ≠ m → ((u.putCard c (Sum.inl a)).piles j).top ≠ some z := by
    intro j hjm ht
    by_cases hja : j = a
    · rw [hja] at ht
      have ht1 : ((if a = a then (Pile.mk [] [c] : Pile) else u.piles a)).top = some z := ht
      rw [ite_eq_left rfl] at ht1
      have ht2 : lastOf ([c] : List Card) = some z := ht1
      rw [show lastOf ([c] : List Card) = some c from rfl] at ht2
      exact hcz (Option.some.inj ht2)
    · rw [show (u.putCard c (Sum.inl a)).piles j = u.piles j from by
        rw [show (u.putCard c (Sum.inl a)).piles = fun a' =>
          if a' = a then (Pile.mk [] [c]) else u.piles a' from putCard_piles_inl u c a]
        exact ite_eq_right hja] at ht
      exact (mem_faceUp_unique hwf hzmem j hjm).1 (Pile.mem_of_top ht)
  have htopm' : ((u.putCard c (Sum.inl a)).piles m).top = some z := by
    rw [show (u.putCard c (Sum.inl a)).piles m = u.piles m from by
      rw [show (u.putCard c (Sum.inl a)).piles = fun a' =>
        if a' = a then (Pile.mk [] [c]) else u.piles a' from putCard_piles_inl u c a]
      exact ite_eq_right (Ne.symm ham)]
    exact htopm
  exact pileOfTop_of_top_unique htopm' hno

/-- `putCard` onto a located card leaves every other top search alone. -/
theorem putCard_inr_pileOfTop_ne {u : State} (hwf : u.WF) {c w : Card} {k : Anchor}
    (hk : u.pileOfTop w = some k) {z : Card} {m : Anchor}
    (hz : u.pileOfTop z = some m) (hkm : k ≠ m) (hcz : c ≠ z) :
    (u.putCard c (Sum.inr w)).pileOfTop z = some m := by
  have hzmem : z ∈ (u.piles m).faceUp := lastOf_mem (pileOfTop_top hz).2
  have htopm : (u.piles m).top = some z := (pileOfTop_eq_some_iff hwf).mp hz
  have hno : ∀ j : Anchor, j ≠ m → ((u.putCard c (Sum.inr w)).piles j).top ≠ some z := by
    intro j hjm ht
    by_cases hjk : j = k
    · rw [hjk] at ht
      rw [putCard_piles_inr u c w k hk] at ht
      have ht1 : ((if k = k then
          { u.piles k with faceUp := (u.piles k).faceUp ++ [c] }
          else u.piles k)).top = some z := ht
      rw [ite_eq_left rfl] at ht1
      have ht2 : lastOf ((u.piles k).faceUp ++ [c]) = some z := ht1
      rw [lastOf_snoc] at ht2
      exact hcz (Option.some.inj ht2)
    · rw [show (u.putCard c (Sum.inr w)).piles j = u.piles j from by
        rw [show (u.putCard c (Sum.inr w)).piles = fun a' =>
          if a' = k then { u.piles k with faceUp := (u.piles k).faceUp ++ [c] }
          else u.piles a' from putCard_piles_inr u c w k hk]
        exact ite_eq_right hjk] at ht
      exact (mem_faceUp_unique hwf hzmem j hjm).1 (Pile.mem_of_top ht)
  have htopm' : ((u.putCard c (Sum.inr w)).piles m).top = some z := by
    rw [show (u.putCard c (Sum.inr w)).piles m = u.piles m from by
      rw [show (u.putCard c (Sum.inr w)).piles = fun a' =>
        if a' = k then { u.piles k with faceUp := (u.piles k).faceUp ++ [c] }
        else u.piles a' from putCard_piles_inr u c w k hk]
      exact ite_eq_right (Ne.symm hkm)]
    exact htopm
  exact pileOfTop_of_top_unique htopm' hno

/-- The pull's top search leaves every pile but its target alone. -/
theorem pullSt_pileOfTop_ne {st : State} (hwf : st.WF) {c : Card} {b : Base} {k : Anchor}
    (hk : tgt st b = some k) (hfound : c ∈ st.found c.suit)
    {z : Card} {m : Anchor} (hz : st.pileOfTop z = some m) (hkm : k ≠ m) (hcz : c ≠ z) :
    (pullSt st c b).pileOfTop z = some m := by
  rw [show (pullSt st c b).pileOfTop z = (st.putCard c b).pileOfTop z from
    pileOfTop_congr_piles (pullSt_piles st c b) z]
  cases b with
  | inl a =>
      have hka : k = a := (Option.some.inj hk).symm
      exact putCard_inl_pileOfTop_ne hwf hfound hz (fun h => hkm (hka.trans h))
  | inr w =>
      exact putCard_inr_pileOfTop_ne hwf hk hz hkm hcz

/-- The pull leaves the holding search of a card outside its target pile
alone. -/
theorem pullSt_pileHolding_ne {st : State} (hwf : st.WF) {c : Card} {b : Base} {k : Anchor}
    (hk : tgt st b = some k) (hfound : c ∈ st.found c.suit)
    {x : Card} {a : Anchor} (hx : st.pileHolding x = some a) (hxa : a ≠ k) :
    (pullSt st c b).pileHolding x = some a := by
  have hxmem : x ∈ (st.piles a).faceUp := pileHolding_mem hx
  cases b with
  | inl a' =>
      have hka : k = a' := (Option.some.inj hk).symm
      subst hka
      refine tfc_pileHolding_pin ?_ ?_
      · rw [pullSt_piles_inl_apply]
        rw [ite_eq_right hxa]
        exact hxmem
      · intro j hja
        rw [pullSt_piles_inl_apply]
        by_cases hjk : j = k
        · rw [hjk, ite_eq_left rfl]
          intro hmem
          have hxc : x = c := by
            rcases List.mem_cons.mp hmem with h | h
            · exact h
            · exact absurd h List.not_mem_nil
          exact ((mem_found_unique hwf hfound).1 a).2 (hxc ▸ hxmem)
        · rw [ite_eq_right hjk]
          intro hmem
          exact (mem_faceUp_unique hwf hxmem j hja).1 hmem
  | inr w =>
      refine tfc_pileHolding_pin ?_ ?_
      · rw [pullSt_piles_inr_apply _ _ _ _ hk]
        rw [ite_eq_right hxa]
        exact hxmem
      · intro j hja
        rw [pullSt_piles_inr_apply _ _ _ _ hk]
        by_cases hjk : j = k
        · rw [hjk, ite_eq_left rfl]
          intro hmem
          rcases List.mem_append.mp hmem with h | h
          · exact (mem_faceUp_unique hwf hxmem k (Ne.symm hxa)).1 h
          · have hxc : x = c := by
              rcases List.mem_cons.mp h with h' | h'
              · exact h'
              · exact absurd h' List.not_mem_nil
            exact ((mem_found_unique hwf hfound).1 a).2 (hxc ▸ hxmem)
        · rw [ite_eq_right hjk]
          intro hmem
          exact (mem_faceUp_unique hwf hxmem j hja).1 hmem

/-! ## 7. Search transfer across a whole slide -/

/-- A card topping a third pile keeps its search across the slide. -/
theorem slideSt_pileOfTop_third {st : State} {c : Card} {b : Base} {a k : Anchor}
    (hwf : st.WF) (hcp : st.canPlace c b = true) (hk : tgt st b = some k) (hak : k ≠ a)
    (hrunv : fromCard c (st.piles a).faceUp ≠ [])
    (hcell : below c (st.piles a).faceUp ≠ [] ∨
      (below c (st.piles a).faceUp = [] ∧ (st.piles a).hidden = []))
    {z : Card} {m : Anchor} (hzm : st.pileOfTop z = some m) (hma : m ≠ a) (hmk : m ≠ k) :
    (slideSt st c b a).pileOfTop z = some m := by
  have hzmem : z ∈ (st.piles m).faceUp := lastOf_mem (pileOfTop_top hzm).2
  have htopm : ((slideSt st c b a).piles m).top = some z := by
    rw [slideSt_piles_other hwf hcp hk hak hcell hma hmk]
    exact (pileOfTop_eq_some_iff hwf).mp hzm
  have hno : ∀ j : Anchor, j ≠ m → ((slideSt st c b a).piles j).top ≠ some z := by
    intro j hjm ht
    by_cases hja : j = a
    · rw [hja] at ht
      rw [slideSt_piles_source hwf hcp hk hak hcell] at ht
      have hzpre : z ∈ below c (st.piles a).faceUp := by
        have : lastOf (below c (st.piles a).faceUp) = some z := ht
        exact lastOf_mem this
      exact (mem_faceUp_unique hwf hzmem a (Ne.symm hma)).1 (mem_below _ hzpre)
    · by_cases hjk : j = k
      · rw [hjk] at ht
        rw [slideSt_piles_target hwf hcp hk hak hcell] at ht
        have hzrun : z ∈ fromCard c (st.piles a).faceUp := by
          have hlast : lastOf ((st.piles k).faceUp ++
              fromCard c (st.piles a).faceUp) = some z := ht
          rw [lastOf_append_of_ne_nil hrunv] at hlast
          exact lastOf_mem hlast
        exact (mem_faceUp_unique hwf hzmem a (Ne.symm hma)).1
          (tfc_mem_fromCard _ hzrun)
      · rw [slideSt_piles_other hwf hcp hk hak hcell hja hjk] at ht
        exact (mem_faceUp_unique hwf hzmem j hjm).1 (Pile.mem_of_top ht)
  exact pileOfTop_of_top_unique htopm hno

/-- A card topping the *source* pile moves with the run: after the
slide its top search lands on the target. -/
theorem slideSt_pileOfTop_source {st : State} {c : Card} {b : Base} {a k : Anchor}
    (hwf : st.WF) (hcp : st.canPlace c b = true) (hk : tgt st b = some k)
    (hak : k ≠ a) (hrunv : fromCard c (st.piles a).faceUp ≠ [])
    (hcell : below c (st.piles a).faceUp ≠ [] ∨
      (below c (st.piles a).faceUp = [] ∧ (st.piles a).hidden = []))
    {z : Card} (hz : st.pileOfTop z = some a) :
    (slideSt st c b a).pileOfTop z = some k := by
  have hfa : (st.piles a).faceUp =
      below c (st.piles a).faceUp ++ fromCard c (st.piles a).faceUp :=
    (tfc_below_fromCard _ _).symm
  have hzlast : lastOf (st.piles a).faceUp = some z := (pileOfTop_eq_some_iff hwf).mp hz
  have hzmem : z ∈ (st.piles a).faceUp := lastOf_mem hzlast
  have hzrun_last : lastOf (fromCard c (st.piles a).faceUp) = some z := by
    rw [hfa, lastOf_append_of_ne_nil hrunv] at hzlast
    exact hzlast
  have hzrun : z ∈ fromCard c (st.piles a).faceUp := lastOf_mem hzrun_last
  have htopk : ((slideSt st c b a).piles k).top = some z := by
    rw [slideSt_piles_target hwf hcp hk hak hcell]
    show lastOf ((st.piles k).faceUp ++ fromCard c (st.piles a).faceUp) = some z
    rw [lastOf_append_of_ne_nil hrunv]
    exact hzrun_last
  have hno : ∀ j : Anchor, j ≠ k → ((slideSt st c b a).piles j).top ≠ some z := by
    intro j hjk ht
    by_cases hja : j = a
    · rw [hja] at ht
      rw [slideSt_piles_source hwf hcp hk hak hcell] at ht
      have hzpre : z ∈ below c (st.piles a).faceUp := by
        have : lastOf (below c (st.piles a).faceUp) = some z := ht
        exact lastOf_mem this
      exact tfc_two_mem_faceUp_absurd hwf hfa hzpre hzrun
    · rw [slideSt_piles_other hwf hcp hk hak hcell hja hjk] at ht
      exact (mem_faceUp_unique hwf hzmem j hja).1 (Pile.mem_of_top ht)
  exact pileOfTop_of_top_unique htopk hno

/-- A card topping the *target* pile is buried by the run: after the
slide its top search is empty. -/
theorem slideSt_pileOfTop_target {st : State} {c : Card} {b : Base} {a k : Anchor}
    (hwf : st.WF) (hcp : st.canPlace c b = true) (hk : tgt st b = some k)
    (hak : k ≠ a) (hrunv : fromCard c (st.piles a).faceUp ≠ [])
    (hcell : below c (st.piles a).faceUp ≠ [] ∨
      (below c (st.piles a).faceUp = [] ∧ (st.piles a).hidden = []))
    {z : Card} (hz : st.pileOfTop z = some k) :
    (slideSt st c b a).pileOfTop z = none := by
  have hfa : (st.piles a).faceUp =
      below c (st.piles a).faceUp ++ fromCard c (st.piles a).faceUp :=
    (tfc_below_fromCard _ _).symm
  have hzmemk : z ∈ (st.piles k).faceUp := lastOf_mem (pileOfTop_top hz).2
  have hno : ∀ j : Anchor, ((slideSt st c b a).piles j).top ≠ some z := by
    intro j ht
    by_cases hja : j = a
    · rw [hja] at ht
      rw [slideSt_piles_source hwf hcp hk hak hcell] at ht
      have hzpre : z ∈ below c (st.piles a).faceUp := by
        have : lastOf (below c (st.piles a).faceUp) = some z := ht
        exact lastOf_mem this
      exact (mem_faceUp_unique hwf hzmemk a (Ne.symm hak)).1 (mem_below _ hzpre)
    · by_cases hjk : j = k
      · rw [hjk] at ht
        rw [slideSt_piles_target hwf hcp hk hak hcell] at ht
        have hzrun : z ∈ fromCard c (st.piles a).faceUp := by
          have hlast : lastOf ((st.piles k).faceUp ++
              fromCard c (st.piles a).faceUp) = some z := ht
          rw [lastOf_append_of_ne_nil hrunv] at hlast
          exact lastOf_mem hlast
        have hzfa : z ∈ (st.piles a).faceUp := by
          rw [hfa]
          exact List.mem_append.mpr (Or.inr hzrun)
        exact (mem_faceUp_unique hwf hzfa k hak).1 hzmemk
      · rw [slideSt_piles_other hwf hcp hk hak hcell hja hjk] at ht
        exact (mem_faceUp_unique hwf hzmemk j hjk).1 (Pile.mem_of_top ht)
  exact pileOfTop_none_of_no_top hno

/-! ## 8. One-leg slide data -/

/-- The data of one reversible slide at `st`, as a proposition. -/
theorem slide_data {st : State} {c : Card} {b : Base}
    (hwf : st.WF) (hrev : reversibleAtW st (Move.tabToTab c b)) :
    ∃ (a k : Anchor),
      st.pileHolding c = some a ∧ st.canPlace c b = true ∧ tgt st b = some k ∧
      k ≠ a ∧
      (st.piles a).faceUp =
        below c (st.piles a).faceUp ++ fromCard c (st.piles a).faceUp ∧
      fromCard c (st.piles a).faceUp ≠ [] ∧
      (below c (st.piles a).faceUp ≠ [] ∨
        (below c (st.piles a).faceUp = [] ∧ (st.piles a).hidden = [])) := by
  obtain ⟨a, tr, s', hhold, hcp, hface, hcrr, hcell, hstep⟩ := tfc_leg_shape hwf hrev
  have hmem : c ∈ (st.piles a).faceUp := pileHolding_mem hhold
  have hface' : (st.piles a).faceUp =
      below c (st.piles a).faceUp ++ fromCard c (st.piles a).faceUp := by
    have hb1 : below c (below c (st.piles a).faceUp ++ c :: tr)
        = below c (st.piles a).faceUp := by
      rw [below_append_notmem (below_not_mem_self (c := c) (st.piles a).faceUp)
        (c :: tr), below_cons_self, List.append_nil]
    have hb2 : fromCard c (below c (st.piles a).faceUp ++ c :: tr) = c :: tr := by
      rw [fromCard_append_notmem (below_not_mem_self (c := c) (st.piles a).faceUp)
        (c :: tr), fromCard_head_eq]
    rw [hface, hb1, hb2]
  have hrun : fromCard c (st.piles a).faceUp ≠ [] := by
    rw [hcrr]; exact List.cons_ne_nil _ _
  have hcell' : below c (st.piles a).faceUp ≠ [] ∨
      (below c (st.piles a).faceUp = [] ∧ (st.piles a).hidden = []) := by
    rcases hcell with h | ⟨h1, h2, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2⟩
  cases b with
  | inl a' =>
      have hne : a' ≠ a := by
        intro h
        subst h
        obtain ⟨hE, -⟩ := canPlace_inl hcp
        obtain ⟨hhid, hfu⟩ := (Pile.isEmpty_eq _).mp hE
        rw [hfu] at hmem
        exact absurd hmem List.not_mem_nil
      exact ⟨a, a', hhold, hcp, rfl, hne, hface', hrun, hcell'⟩
  | inr w =>
      obtain ⟨k, hz, hsit⟩ := canPlace_inr hcp
      have hne : k ≠ a := tfc_mover_pile_not_target hwf hhold hz hsit
      exact ⟨a, k, hhold, hcp, hz, hne, hface', hrun, hcell'⟩

/-! ## 8b. More run/chop algebra -/

/- KIT-HOIST STRIKE (2026-11-01): `chop_append_singleton` is hoisted to
`Orig2/Substrate/Kit.lean` (one home below both former copies); the cite below
re-points there. -/

/-- `fromCard` of a member is nonempty. -/
theorem fromCard_ne_nil_of_mem : ∀ {l : List Card} {c : Card}, c ∈ l → fromCard c l ≠ [] := by
  intro l
  induction l with
  | nil => intro c h; exact absurd h List.not_mem_nil
  | cons x t ih =>
      intro c h
      rw [tfc_fromCard_cons]
      by_cases hxc : x = c
      · rw [ite_eq_left hxc]
        exact List.cons_ne_nil _ _
      · rw [ite_eq_right hxc]
        exact ih ((List.mem_cons.mp h).resolve_left (fun hh => hxc hh.symm))

/-- A member that is not the last card survives the `chop`. -/
theorem mem_chop_of_mem_of_ne_last {c w : Card} {l : List Card}
    (hc : c ∈ l) (hlast : lastOf l = some w) (hcw : c ≠ w) : c ∈ chop l := by
  obtain ⟨front, hfe⟩ := lastOf_eq_snoc hlast
  have hc' : c ∈ front := by
    rw [hfe] at hc
    rcases List.mem_append.mp hc with h' | h'
    · exact h'
    · rcases List.mem_cons.mp h' with h'' | h''
      · exact absurd h'' hcw
      · exact absurd h'' List.not_mem_nil
  rw [hfe, chop_snoc]
  exact hc'

/-! ## 9. Raise-side rows -/

/-- A raise of `d` at pile `a` leaves the holding search of a card in
another pile alone. -/
theorem pileHolding_raiseSt_ne {u : State} (hwf : u.WF) {d x : Card} {a b : Anchor}
    (hda : u.pileOfTop d = some a) (hxb : x ∈ (u.piles b).faceUp) (hba : b ≠ a) :
    (raiseSt u d a).pileHolding x = some b := by
  refine tfc_pileHolding_pin ?_ ?_
  · rw [raiseSt_piles_apply, ite_eq_right hba]
    exact hxb
  · intro j hjb
    rw [raiseSt_piles_apply]
    intro hmem
    by_cases hja : j = a
    · rw [hja] at hmem
      rw [ite_eq_left rfl] at hmem
      have hzone := mem_afterRunRemoved_chop_zone
        (x := x) (List.mem_append.mpr (Or.inr hmem))
      rcases List.mem_append.mp hzone with h' | h'
      · exact ((mem_faceUp_unique hwf hxb a (Ne.symm hba)).2.1) h'
      · exact ((mem_faceUp_unique hwf hxb a (Ne.symm hba)).1) h'
    · rw [ite_eq_right hja] at hmem
      exact (mem_faceUp_unique hwf hxb j hjb).1 hmem

/-- Splitting the moved run at the last card of the source pile. -/
theorem fromCard_eq_fromCard_chop_append {c w : Card} {l : List Card}
    (hc : c ∈ l) (hlast : lastOf l = some w) (hcw : c ≠ w) :
    fromCard c l = fromCard c (chop l) ++ [w] := by
  obtain ⟨front, hfe⟩ := lastOf_eq_snoc hlast
  have hcw' : c ∈ front := by
    rw [hfe] at hc
    rcases List.mem_append.mp hc with h' | h'
    · exact h'
    · rcases List.mem_cons.mp h' with h'' | h''
      · exact absurd h'' hcw
      · exact absurd h'' List.not_mem_nil
  rw [hfe, chop_snoc, fromCard_append_of_mem hcw']

/-- Splitting `below` at the last card of the source pile. -/
theorem below_eq_below_chop {c w : Card} {l : List Card}
    (hc : c ∈ l) (hlast : lastOf l = some w) (hcw : c ≠ w) :
    below c l = below c (chop l) := by
  obtain ⟨front, hfe⟩ := lastOf_eq_snoc hlast
  have hc' : c ∈ front := by
    rw [hfe] at hc
    rcases List.mem_append.mp hc with h' | h'
    · exact h'
    · rcases List.mem_cons.mp h' with h'' | h''
      · exact absurd h'' hcw
      · exact absurd h'' List.not_mem_nil
  rw [hfe, chop_snoc]
  exact below_append_of_mem hc'


-- ===== from Temp/SlideAsm_Raise.lean =====

theorem step_comm_slide_raise {st s1 s2 s12 s21 : State} {c1 c2 : Card} {b1 : Base}
    (hwf : st.WF)
    (hrev1 : reversibleAtW st (Move.tabToTab c1 b1))
    (hrev2 : reversibleAtW st (Move.tabToFound c2))
    (h1 : State.step st (Move.tabToTab c1 b1) = some s1)
    (h2 : State.step st (Move.tabToFound c2) = some s2)
    (h12 : State.step s1 (Move.tabToFound c2) = some s12)
    (h21 : State.step s2 (Move.tabToTab c1 b1) = some s21) :
    s12 = s21 := by
  -- the two legs
  obtain ⟨a1, hhold1, hcp1, hrun1, hs1⟩ := step_tabToTab_slideSt h1
  obtain ⟨hnext2, a2, hpa2, hs2⟩ := step_tabToFound_inv h2
  -- the reversible cell of the slide
  obtain ⟨aD, kD, hholdD, hcpD, hkD, hkDne, hfaD, hrunD, hcellD⟩ := slide_data hwf hrev1
  have haD : aD = a1 := Option.some.inj (hholdD.symm.trans hhold1)
  obtain ⟨k1, hk1⟩ := exists_tgt_of_canPlace hcp1
  have hkD' : kD = k1 := Option.some.inj (hkD.symm.trans hk1)
  have hk1ne : k1 ≠ a1 := by
    have h := hkDne
    rw [haD, hkD'] at h
    exact h
  have hcell : below c1 (st.piles a1).faceUp ≠ [] ∨
      (below c1 (st.piles a1).faceUp = [] ∧ (st.piles a1).hidden = []) := by
    simpa [haD] using hcellD
  have hmem1 : c1 ∈ (st.piles a1).faceUp := pileHolding_mem hhold1
  -- canonical successors
  subst s1
  have hs2' : s2 = raiseSt st c2 a2 := by rw [hs2]; rfl
  clear hs2
  subst s2
  obtain ⟨-, a2', hpa12, hs12⟩ := step_tabToFound_inv h12
  have hs12' : s12 = raiseSt (slideSt st c1 b1 a1) c2 a2' := by rw [hs12]; rfl
  have hwfS2 : (raiseSt st c2 a2).WF := step_wf hwf h2
  obtain ⟨a1', hhold1', hcp1', hrun1', hs21⟩ := step_tabToTab_slideSt h21
  clear hs12
  subst s12
  subst s21
  -- the field rows that do not depend on the case
  have hfound : (raiseSt (slideSt st c1 b1 a1) c2 a2').found =
      (slideSt (raiseSt st c2 a2) c1 b1 a1').found := by
    funext s
    rw [raiseSt_found_apply, slideSt_found, slideSt_found, raiseSt_found_apply]
  have hstock : (raiseSt (slideSt st c1 b1 a1) c2 a2').stock =
      (slideSt (raiseSt st c2 a2) c1 b1 a1').stock := by
    simp only [raiseSt_stock, slideSt_stock]
  have hwaste : (raiseSt (slideSt st c1 b1 a1) c2 a2').waste =
      (slideSt (raiseSt st c2 a2) c1 b1 a1').waste := by
    simp only [raiseSt_waste, slideSt_waste]
  have hdraw : (raiseSt (slideSt st c1 b1 a1) c2 a2').drawStep =
      (slideSt (raiseSt st c2 a2) c1 b1 a1').drawStep := by
    simp only [raiseSt_drawStep, slideSt_drawStep]
  by_cases ha2a1 : a2 = a1
  · subst a2
    -- ---------- the raise comes from the slide's source ----------
    have hlast : lastOf (st.piles a1).faceUp = some c2 :=
      (pileOfTop_eq_some_iff hwf).mp hpa2
    by_cases hc2c1 : c2 = c1
    · -- the raise founds the run head: the second slide is dead
      exfalso
      subst c2
      have hcfound : c1 ∈ (raiseSt st c1 a1).found c1.suit := by
        rw [raiseSt_found_apply, ite_eq_left rfl]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
      exact ((mem_found_unique hwfS2 hcfound).1 a1').2 (pileHolding_mem hhold1')
    · -- the raise chops the run at its own top card
      have hcne : c1 ≠ c2 := fun h => hc2c1 h.symm
      have hmem_chop : c1 ∈ chop (st.piles a1).faceUp :=
        mem_chop_of_mem_of_ne_last hmem1 hlast hcne
      have hchop_ne : chop (st.piles a1).faceUp ≠ [] := by
        intro h
        rw [h] at hmem_chop
        exact absurd hmem_chop List.not_mem_nil
      have hw_ne : fromCard c1 (chop (st.piles a1).faceUp) ≠ [] :=
        fromCard_ne_nil_of_mem hmem_chop
      have hpresplit : below c1 (st.piles a1).faceUp =
          below c1 (chop (st.piles a1).faceUp) :=
        below_eq_below_chop hmem1 hlast hcne
      have hrunsplit : fromCard c1 (st.piles a1).faceUp =
          fromCard c1 (chop (st.piles a1).faceUp) ++ [c2] :=
        fromCard_eq_fromCard_chop_append hmem1 hlast hcne
      have hs2_a1 : (raiseSt st c2 a1).piles a1 =
          { st.piles a1 with faceUp := chop (st.piles a1).faceUp } := by
        rw [raiseSt_piles_apply, ite_eq_left rfl]
        exact afterRunRemoved_eq_faceUp (Or.inl hchop_ne)
      have hs2_k1 : (raiseSt st c2 a1).piles k1 = st.piles k1 := by
        rw [raiseSt_piles_apply]
        exact ite_eq_right hk1ne
      have hhold2 : (raiseSt st c2 a1).pileHolding c1 = some a1 := by
        refine tfc_pileHolding_pin ?_ ?_
        · rw [hs2_a1]
          exact hmem_chop
        · intro j hja
          rw [raiseSt_piles_apply, ite_eq_right hja]
          intro hmem
          exact (mem_faceUp_unique hwf hmem1 j hja).1 hmem
      have ha1' : a1' = a1 := Option.some.inj (hhold1'.symm.trans hhold2)
      subst a1'
      -- the raise card tops the slide's target after the slide
      have hpatgt : (slideSt st c1 b1 a1).pileOfTop c2 = some k1 :=
        slideSt_pileOfTop_source hwf hcp1 hk1 hk1ne hrun1 hcell hpa2
      have ha2' : a2' = k1 := Option.some.inj (hpa12.symm.trans hpatgt)
      subst a2'
      have htgt2 : tgt (raiseSt st c2 a1) b1 = some k1 := by
        cases b1 with
        | inl a => exact hk1
        | inr z =>
            exact raiseSt_pileOfTop_ne (u := st) (d := z) (a := a1) (b := k1) hwf hk1
              (fun h : a1 = k1 => hk1ne h.symm)
      have hcell2 : below c1 ((raiseSt st c2 a1).piles a1).faceUp ≠ [] ∨
          (below c1 ((raiseSt st c2 a1).piles a1).faceUp = [] ∧
            ((raiseSt st c2 a1).piles a1).hidden = []) := by
        rw [hs2_a1]
        show below c1 (chop (st.piles a1).faceUp) ≠ [] ∨
          (below c1 (chop (st.piles a1).faceUp) = [] ∧ (st.piles a1).hidden = [])
        rw [← hpresplit]
        exact hcell
      have hrunv2 : fromCard c1 ((raiseSt st c2 a1).piles a1).faceUp ≠ [] := by
        rw [hs2_a1]
        exact fromCard_ne_nil_of_mem hmem_chop
      have hrun2 : fromCard c1 ((raiseSt st c2 a1).piles a1).faceUp =
          fromCard c1 (chop (st.piles a1).faceUp) := by rw [hs2_a1]
      -- the raise's write at `k1`
      have hs12_k1 : (raiseSt (slideSt st c1 b1 a1) c2 k1).piles k1 =
          { st.piles k1 with faceUp :=
              (st.piles k1).faceUp ++ fromCard c1 (chop (st.piles a1).faceUp) } := by
        rw [raiseSt_piles_apply, ite_eq_left rfl]
        rw [slideSt_piles_target hwf hcp1 hk1 hk1ne hcell]
        rw [hrunsplit]
        rw [← List.append_assoc]
        have hchop : chop (((st.piles k1).faceUp ++
            fromCard c1 (chop (st.piles a1).faceUp)) ++ [c2]) =
            (st.piles k1).faceUp ++ fromCard c1 (chop (st.piles a1).faceUp) :=
          chop_append_singleton
        have hne : chop (((st.piles k1).faceUp ++
            fromCard c1 (chop (st.piles a1).faceUp)) ++ [c2]) ≠ [] := by
          rw [hchop]
          intro h
          exact hw_ne (List.append_eq_nil_iff.mp h).2
        rw [afterRunRemoved_eq_faceUp
          (p := { st.piles k1 with faceUp := ((st.piles k1).faceUp ++
            fromCard c1 (chop (st.piles a1).faceUp)) ++ [c2] })
          (pre := chop (((st.piles k1).faceUp ++
            fromCard c1 (chop (st.piles a1).faceUp)) ++ [c2])) (Or.inl hne)]
        rw [hchop]
      have hkey : (raiseSt (slideSt st c1 b1 a1) c2 k1).piles k1 =
          (slideSt (raiseSt st c2 a1) c1 b1 a1).piles k1 := by
        rw [hs12_k1]
        rw [slideSt_piles_target hwfS2 hcp1' htgt2 hk1ne hcell2, hs2_k1, hrun2]
      apply State.ext
      · exact hfound
      · funext j
        by_cases hjk : j = k1
        · subst j
          exact hkey
        · rw [raiseSt_piles_apply (u := slideSt st c1 b1 a1) (c := c2) (a := k1) (a' := j)]
          rw [slideSt_piles_at (st := raiseSt st c2 a1) (c := c1) (b := b1) (a := a1)
                (k := k1) hwfS2 hcp1' htgt2 hk1ne hcell2 j]
          rw [ite_eq_right hjk]
          by_cases hja : j = a1
          · subst j
            rw [ite_eq_left rfl]
            apply Pile.ext
            · rw [slideSt_piles_source hwf hcp1 hk1 hk1ne hcell, hs2_a1]
            · rw [slideSt_piles_source hwf hcp1 hk1 hk1ne hcell, hs2_a1, hpresplit]
          · rw [ite_eq_right hja]
            rw [slideSt_piles_other hwf hcp1 hk1 hk1ne hcell hja hjk]
            rw [ite_eq_right hjk]
            rw [raiseSt_piles_apply (u := st) (c := c2) (a := a1) (a' := j)]
            rw [ite_eq_right hja]
      · exact hstock
      · exact hwaste
      · exact hdraw
  · by_cases ha2k1 : a2 = k1
    · -- the slide buries the raise card: the raise is dead at `s1`
      exfalso
      have hz : st.pileOfTop c2 = some k1 := by
        rw [← ha2k1]
        exact hpa2
      have hnone := slideSt_pileOfTop_target hwf hcp1 hk1 hk1ne hrun1 hcell hz
      rw [hnone] at hpa12
      exact absurd hpa12 (by simp)
    · -- ---------- disjoint piles ----------
      have hsrca1 : (raiseSt st c2 a2).piles a1 = st.piles a1 := by
        rw [raiseSt_piles_apply]
        exact ite_eq_right (fun h => ha2a1 h.symm)
      have hsrck1 : (raiseSt st c2 a2).piles k1 = st.piles k1 := by
        rw [raiseSt_piles_apply]
        exact ite_eq_right (fun h => ha2k1 h.symm)
      have hhold2 : (raiseSt st c2 a2).pileHolding c1 = some a1 :=
        pileHolding_raiseSt_ne hwf hpa2 hmem1 (fun h : a1 = a2 => ha2a1 h.symm)
      have ha1' : a1' = a1 := Option.some.inj (hhold1'.symm.trans hhold2)
      subst a1'
      have hpatgt : (slideSt st c1 b1 a1).pileOfTop c2 = some a2 :=
        slideSt_pileOfTop_third hwf hcp1 hk1 hk1ne hrun1 hcell hpa2 ha2a1 ha2k1
      have ha2' : a2' = a2 := Option.some.inj (hpa12.symm.trans hpatgt)
      subst a2'
      have htgt2 : tgt (raiseSt st c2 a2) b1 = some k1 := by
        cases b1 with
        | inl a => exact hk1
        | inr z =>
            exact raiseSt_pileOfTop_ne (u := st) (d := z) (a := a2) (b := k1) hwf hk1 ha2k1
      have hcell2 : below c1 ((raiseSt st c2 a2).piles a1).faceUp ≠ [] ∨
          (below c1 ((raiseSt st c2 a2).piles a1).faceUp = [] ∧
            ((raiseSt st c2 a2).piles a1).hidden = []) := by
        rw [hsrca1]
        exact hcell
      have hrunv2 : fromCard c1 ((raiseSt st c2 a2).piles a1).faceUp ≠ [] := by
        rw [hsrca1]
        exact hrun1
      have hkey : (raiseSt (slideSt st c1 b1 a1) c2 a2).piles k1 =
          (slideSt (raiseSt st c2 a2) c1 b1 a1).piles k1 := by
        rw [raiseSt_piles_apply, ite_eq_right (fun h : k1 = a2 => ha2k1 h.symm)]
        rw [slideSt_piles_target hwf hcp1 hk1 hk1ne hcell]
        rw [slideSt_piles_target hwfS2 hcp1' htgt2 hk1ne hcell2, hsrck1, hsrca1]
      apply State.ext
      · exact hfound
      · funext j
        by_cases hjk : j = k1
        · subst j
          exact hkey
        · rw [raiseSt_piles_apply (u := slideSt st c1 b1 a1) (c := c2) (a := a2) (a' := j)]
          rw [slideSt_piles_at (st := raiseSt st c2 a2) (c := c1) (b := b1) (a := a1)
                (k := k1) hwfS2 hcp1' htgt2 hk1ne hcell2 j]
          rw [ite_eq_right hjk]
          by_cases hja : j = a1
          · subst j
            rw [ite_eq_right (fun h : a1 = a2 => ha2a1 h.symm), ite_eq_left rfl]
            apply Pile.ext
            · rw [slideSt_piles_source hwf hcp1 hk1 hk1ne hcell, hsrca1]
            · rw [slideSt_piles_source hwf hcp1 hk1 hk1ne hcell, hsrca1]
          · by_cases hja2 : j = a2
            · subst j
              rw [ite_eq_left rfl]
              rw [ite_eq_right ha2a1]
              rw [slideSt_piles_other hwf hcp1 hk1 hk1ne hcell ha2a1 ha2k1]
              rw [raiseSt_piles_apply (u := st) (c := c2) (a := a2) (a' := a2)]
              rw [ite_eq_left rfl]
            · rw [ite_eq_right hja2]
              rw [ite_eq_right hja]
              rw [slideSt_piles_other hwf hcp1 hk1 hk1ne hcell hja hjk]
              rw [raiseSt_piles_apply (u := st) (c := c2) (a := a2) (a' := j)]
              rw [ite_eq_right hja2]
      · exact hstock
      · exact hwaste
      · exact hdraw




-- ===== from Temp/SlideAsm_Pull.lean =====

theorem step_comm_slide_pull {st s1 s2 s12 s21 : State} {c1 c2 : Card} {b1 b2 : Base}
    (hwf : st.WF)
    (hrev1 : reversibleAtW st (Move.tabToTab c1 b1))
    (hrev2 : reversibleAtW st (Move.foundToTab c2 b2))
    (h1 : State.step st (Move.tabToTab c1 b1) = some s1)
    (h2 : State.step st (Move.foundToTab c2 b2) = some s2)
    (h12 : State.step s1 (Move.foundToTab c2 b2) = some s12)
    (h21 : State.step s2 (Move.tabToTab c1 b1) = some s21) :
    s12 = s21 := by
  -- the two legs
  obtain ⟨a1, hhold1, hcp1, hrun1, hs1⟩ := step_tabToTab_slideSt h1
  obtain ⟨c2', htop2', hc2', hcp2, hs2⟩ := step_foundToTab_pullSt h2
  rw [hc2'] at htop2'
  -- targets
  obtain ⟨k1, hk1⟩ := exists_tgt_of_canPlace hcp1
  obtain ⟨k2, hk2⟩ := exists_tgt_of_canPlace hcp2
  -- the reversible cell of the slide
  obtain ⟨aD, kD, hholdD, hcpD, hkD, hkDne, hfaD, hrunD, hcellD⟩ := slide_data hwf hrev1
  have haD : aD = a1 := Option.some.inj (hholdD.symm.trans hhold1)
  have hkD' : kD = k1 := Option.some.inj (hkD.symm.trans hk1)
  have hk1ne : k1 ≠ a1 := by
    have h := hkDne
    rw [haD, hkD'] at h
    exact h
  have hcell : below c1 (st.piles a1).faceUp ≠ [] ∨
      (below c1 (st.piles a1).faceUp = [] ∧ (st.piles a1).hidden = []) := by
    simpa [haD] using hcellD
  have hmem1 : c1 ∈ (st.piles a1).faceUp := pileHolding_mem hhold1
  have hfound2 : c2 ∈ st.found c2.suit := lastOf_mem htop2'
  -- canonical successors
  subst s1
  subst s2
  obtain ⟨-, -, -, hcpS2, hs12⟩ := step_foundToTab_pullSt h12
  have hwfS2 : (pullSt st c2 b2).WF := step_wf hwf h2
  obtain ⟨a1', hhold1', hcp1', hrun1', hs21⟩ := step_tabToTab_slideSt h21
  subst s12
  subst s21
  -- the slide's source pile is the same in both orders
  have hhold2 : (pullSt st c2 b2).pileHolding c1 = some a1 := by
    by_cases hk2a : k2 = a1
    · have hb2 : ∃ w, b2 = Sum.inr w := by
        cases b2 with
        | inl a =>
            exfalso
            have hka : k2 = a := (Option.some.inj hk2).symm
            have haa : a = a1 := hka.symm.trans hk2a
            obtain ⟨hemp, -⟩ := canPlace_inl hcp2
            rw [haa] at hemp
            obtain ⟨-, hfu⟩ := (Pile.isEmpty_eq _).mp hemp
            rw [hfu] at hmem1
            exact absurd hmem1 List.not_mem_nil
        | inr w => exact ⟨w, rfl⟩
      obtain ⟨w, rfl⟩ := hb2
      have hz : st.pileOfTop w = some a1 := by
        have h := hk2
        rw [hk2a] at h
        exact h
      refine tfc_pileHolding_pin ?_ ?_
      · rw [pullSt_piles_inr_apply _ _ _ _ hz, ite_eq_left rfl]
        exact List.mem_append.mpr (Or.inl hmem1)
      · intro j hja
        rw [pullSt_piles_inr_apply _ _ _ _ hz, ite_eq_right hja]
        intro hmem
        exact (mem_faceUp_unique hwf hmem1 j hja).1 hmem
    · exact pullSt_pileHolding_ne hwf hk2 hfound2 hhold1 (fun h => hk2a h.symm)
  have ha1' : a1' = a1 := Option.some.inj (hhold1'.symm.trans hhold2)
  subst a1'
  -- ===== foundations =====
  apply State.ext
  · rw [slideSt_found]
    exact pullSt_found_congr (slideSt_found st c1 b1 a1) c2 b2
  · -- ===== piles =====
    by_cases hk2a : k2 = a1
    · -- ---------- CASE B: the pull lands on the slide's source ----------
      have hb2 : ∃ w, b2 = Sum.inr w := by
        cases b2 with
        | inl a =>
            exfalso
            have hka : k2 = a := (Option.some.inj hk2).symm
            have haa : a = a1 := hka.symm.trans hk2a
            obtain ⟨hemp, -⟩ := canPlace_inl hcp2
            rw [haa] at hemp
            obtain ⟨-, hfu⟩ := (Pile.isEmpty_eq _).mp hemp
            rw [hfu] at hmem1
            exact absurd hmem1 List.not_mem_nil
        | inr w => exact ⟨w, rfl⟩
      obtain ⟨w, hb2eq⟩ := hb2
      subst hb2eq
      have hz : st.pileOfTop w = some a1 := by
        have h := hk2
        rw [hk2a] at h
        exact h
      -- the pull's writes
      have hpull_a1 : (pullSt st c2 (Sum.inr w)).piles a1 =
          { st.piles a1 with faceUp := (st.piles a1).faceUp ++ [c2] } := by
        rw [pullSt_piles_inr_apply _ _ _ _ hz, ite_eq_left rfl]
      have hpull_k1 : (pullSt st c2 (Sum.inr w)).piles k1 = st.piles k1 := by
        rw [pullSt_piles_inr_apply _ _ _ _ hz, ite_eq_right hk1ne]
      have hfa2 : ((pullSt st c2 (Sum.inr w)).piles a1).faceUp =
          (st.piles a1).faceUp ++ [c2] := by rw [hpull_a1]
      have hhd2 : ((pullSt st c2 (Sum.inr w)).piles a1).hidden = (st.piles a1).hidden := by
        rw [hpull_a1]
      have hpre2 : below c1 ((pullSt st c2 (Sum.inr w)).piles a1).faceUp =
          below c1 (st.piles a1).faceUp := by
        rw [hfa2, below_append_of_mem hmem1]
      have hrun2 : fromCard c1 ((pullSt st c2 (Sum.inr w)).piles a1).faceUp =
          fromCard c1 (st.piles a1).faceUp ++ [c2] := by
        rw [hfa2, fromCard_append_of_mem hmem1]
      have hrunv2 : fromCard c1 ((pullSt st c2 (Sum.inr w)).piles a1).faceUp ≠ [] := by
        rw [hrun2]
        intro h
        exact hrun1 (List.append_eq_nil_iff.mp h).1
      have hcell2 : below c1 ((pullSt st c2 (Sum.inr w)).piles a1).faceUp ≠ [] ∨
          (below c1 ((pullSt st c2 (Sum.inr w)).piles a1).faceUp = [] ∧
            ((pullSt st c2 (Sum.inr w)).piles a1).hidden = []) := by
        rw [hpre2, hhd2]
        exact hcell
      -- the targets after the other leg
      have htgt1 : tgt (slideSt st c1 b1 a1) (Sum.inr w) = some k1 :=
        slideSt_pileOfTop_source hwf hcp1 hk1 hk1ne hrun1 hcell hz
      have htgt2 : tgt (pullSt st c2 (Sum.inr w)) b1 = some k1 := by
        cases b1 with
        | inl a => exact hk1
        | inr z =>
            have hz1 : st.pileOfTop z = some k1 := hk1
            have hcz : c2 ≠ z := by
              intro hcz'
              have htop : (st.piles k1).top = some c2 := by
                rw [hcz']
                exact (pileOfTop_eq_some_iff hwf).mp hz1
              exact not_top_of_found hwf hfound2 k1 htop
            exact pullSt_pileOfTop_ne hwf hk2 hfound2 hz1
              (fun h => hk1ne (hk2a.symm.trans h).symm) hcz
      funext j
      rw [pullSt_piles_inr_apply (u := slideSt st c1 b1 a1) (c := c2) (z := w)
            (k := k1) htgt1 j]
      rw [slideSt_piles_at (st := pullSt st c2 (Sum.inr w)) (c := c1)
            (b := b1) (a := a1) (k := k1) hwfS2 hcp1' htgt2 hk1ne hcell2 j]
      by_cases hja : j = a1
      · subst j
        rw [ite_eq_right (fun h => hk1ne h.symm), ite_eq_left rfl]
        apply Pile.ext
        · rw [slideSt_piles_source hwf hcp1 hk1 hk1ne hcell, hpull_a1]
        · rw [slideSt_piles_source hwf hcp1 hk1 hk1ne hcell, hpre2]
      · by_cases hjk : j = k1
        · subst j
          rw [ite_eq_left rfl, ite_eq_right hk1ne, ite_eq_left rfl]
          apply Pile.ext
          · rw [slideSt_piles_target hwf hcp1 hk1 hk1ne hcell, hpull_k1]
          · rw [slideSt_piles_target hwf hcp1 hk1 hk1ne hcell, hpull_k1,
                hrun2, List.append_assoc]
        · rw [ite_eq_right hjk, ite_eq_right hja, ite_eq_right hjk]
          rw [slideSt_piles_other hwf hcp1 hk1 hk1ne hcell hja hjk]
          rw [pullSt_piles_inr_apply (u := st) (c := c2)
                (z := w) (k := a1) hz j]
          rw [ite_eq_right hja]
    · by_cases hk2k1 : k2 = k1
      · -- ---------- CASE C: the pull's target is the slide's target ----------
        exfalso
        cases b2 with
        | inl a =>
            have hk2a' : k2 = a := (Option.some.inj hk2).symm
            have hak1 : a = k1 := hk2a'.symm.trans hk2k1
            obtain ⟨hemp, -⟩ := canPlace_inl hcpS2
            rw [hak1] at hemp
            have hne : ((slideSt st c1 b1 a1).piles k1).faceUp ≠ [] := by
              rw [slideSt_piles_target hwf hcp1 hk1 hk1ne hcell]
              intro h
              exact hrun1 (List.append_eq_nil_iff.mp h).2
            have hfu : ((slideSt st c1 b1 a1).piles k1).faceUp = [] :=
              ((Pile.isEmpty_eq _).mp hemp).2
            exact hne hfu
        | inr z =>
            have hz : st.pileOfTop z = some k1 := by
              have h := hk2
              rw [hk2k1] at h
              exact h
            have hnone := slideSt_pileOfTop_target hwf hcp1 hk1 hk1ne hrun1 hcell hz
            obtain ⟨k'', hz', -⟩ := canPlace_inr hcpS2
            rw [hnone] at hz'
            exact absurd hz' (by simp)
      · -- ---------- CASE A: the pull lands on a third pile ----------
        have hs1_a1 : (slideSt st c1 b1 a1).piles a1 =
            { st.piles a1 with faceUp := below c1 (st.piles a1).faceUp } :=
          slideSt_piles_source hwf hcp1 hk1 hk1ne hcell
        have hs1_k1 : (slideSt st c1 b1 a1).piles k1 =
            { st.piles k1 with faceUp :=
                (st.piles k1).faceUp ++ fromCard c1 (st.piles a1).faceUp } :=
          slideSt_piles_target hwf hcp1 hk1 hk1ne hcell
        have hs1_k2 : (slideSt st c1 b1 a1).piles k2 = st.piles k2 :=
          slideSt_piles_other hwf hcp1 hk1 hk1ne hcell hk2a hk2k1
        have htgt2 : tgt (pullSt st c2 b2) b1 = some k1 := by
          cases b1 with
          | inl a => exact hk1
          | inr z =>
              have hz1 : st.pileOfTop z = some k1 := hk1
              have hcz : c2 ≠ z := by
                intro hcz'
                have htop : (st.piles k1).top = some c2 := by
                  rw [hcz']
                  exact (pileOfTop_eq_some_iff hwf).mp hz1
                exact not_top_of_found hwf hfound2 k1 htop
              exact pullSt_pileOfTop_ne hwf hk2 hfound2 hz1
                (fun h => hk2k1 h) hcz
        cases b2 with
        | inl a =>
            have hka : k2 = a := (Option.some.inj hk2).symm
            have hs2_a1 : (pullSt st c2 (Sum.inl a)).piles a1 = st.piles a1 := by
              rw [pullSt_piles_inl_apply,
                ite_eq_right (fun h : a1 = a => hk2a (hka.trans h.symm))]
            have hs2_k1 : (pullSt st c2 (Sum.inl a)).piles k1 = st.piles k1 := by
              rw [pullSt_piles_inl_apply,
                ite_eq_right (fun h : k1 = a => hk2k1 (h.trans hka.symm).symm)]
            have hcell2 : below c1 ((pullSt st c2 (Sum.inl a)).piles a1).faceUp ≠ [] ∨
                (below c1 ((pullSt st c2 (Sum.inl a)).piles a1).faceUp = [] ∧
                  ((pullSt st c2 (Sum.inl a)).piles a1).hidden = []) := by
              rw [hs2_a1]
              exact hcell
            funext j
            rw [pullSt_piles_inl_apply (u := slideSt st c1 b1 a1) (c := c2)
                  (a1 := a) (a := j)]
            rw [slideSt_piles_at (st := pullSt st c2 (Sum.inl a)) (c := c1)
                  (b := b1) (a := a1) (k := k1) hwfS2 hcp1' htgt2 hk1ne hcell2 j]
            by_cases hja : j = a1
            · subst j
              rw [ite_eq_right (fun h : a1 = a => hk2a (hka.trans h.symm)), ite_eq_left rfl]
              apply Pile.ext
              · rw [hs1_a1, hs2_a1]
              · rw [hs1_a1, hs2_a1]
            · by_cases hjk : j = k1
              · subst j
                rw [ite_eq_right (fun h : k1 = a => hk2k1 (h.trans hka.symm).symm),
                  ite_eq_right hk1ne, ite_eq_left rfl]
                apply Pile.ext
                · rw [hs1_k1, hs2_k1, hs2_a1]
                · rw [hs1_k1, hs2_k1, hs2_a1]
              · by_cases hjk2 : j = k2
                · subst j
                  rw [ite_eq_left hka]
                  rw [ite_eq_right hk2a, ite_eq_right hk2k1]
                  rw [pullSt_piles_inl_apply (u := st) (c := c2)
                        (a1 := a) (a := k2), ite_eq_left hka]
                · rw [ite_eq_right (fun h : j = a => hjk2 (h.trans hka.symm))]
                  rw [ite_eq_right hja, ite_eq_right hjk]
                  rw [slideSt_piles_other hwf hcp1 hk1 hk1ne hcell hja hjk]
                  rw [pullSt_piles_inl_apply (u := st) (c := c2)
                        (a1 := a) (a := j)]
                  rw [ite_eq_right (fun h : j = a => hjk2 (h.trans hka.symm))]
        | inr z =>
            have hs1_k2' : (slideSt st c1 b1 a1).piles k2 = st.piles k2 := hs1_k2
            have hs2_a1 : (pullSt st c2 (Sum.inr z)).piles a1 = st.piles a1 := by
              rw [pullSt_piles_inr_apply _ _ _ _ hk2, ite_eq_right (fun h => hk2a h.symm)]
            have hs2_k1 : (pullSt st c2 (Sum.inr z)).piles k1 = st.piles k1 := by
              rw [pullSt_piles_inr_apply _ _ _ _ hk2, ite_eq_right (fun h => hk2k1 h.symm)]
            have hcell2 : below c1 ((pullSt st c2 (Sum.inr z)).piles a1).faceUp ≠ [] ∨
                (below c1 ((pullSt st c2 (Sum.inr z)).piles a1).faceUp = [] ∧
                  ((pullSt st c2 (Sum.inr z)).piles a1).hidden = []) := by
              rw [hs2_a1]
              exact hcell
            have htgt1 : tgt (slideSt st c1 b1 a1) (Sum.inr z) = some k2 :=
              slideSt_pileOfTop_third hwf hcp1 hk1 hk1ne hrun1 hcell hk2 hk2a hk2k1
            funext j
            rw [pullSt_piles_inr_apply (u := slideSt st c1 b1 a1) (c := c2) (z := z)
                  (k := k2) htgt1 j]
            rw [slideSt_piles_at (st := pullSt st c2 (Sum.inr z)) (c := c1)
                  (b := b1) (a := a1) (k := k1) hwfS2 hcp1' htgt2 hk1ne hcell2 j]
            by_cases hja : j = a1
            · subst j
              rw [ite_eq_right (fun h => hk2a h.symm), ite_eq_left rfl]
              apply Pile.ext
              · rw [hs1_a1, hs2_a1]
              · rw [hs1_a1, hs2_a1]
            · by_cases hjk : j = k1
              · subst j
                rw [ite_eq_right (fun h => hk2k1 h.symm), ite_eq_right hk1ne, ite_eq_left rfl]
                apply Pile.ext
                · rw [hs1_k1, hs2_k1, hs2_a1]
                · rw [hs1_k1, hs2_k1, hs2_a1]
              · by_cases hjk2 : j = k2
                · subst j
                  rw [ite_eq_left rfl]
                  rw [ite_eq_right hk2a, ite_eq_right hk2k1]
                  rw [pullSt_piles_inr_apply (u := st) (c := c2) (z := z) (k := k2) hk2,
                        ite_eq_left rfl]
                  rw [hs1_k2']
                · rw [ite_eq_right hjk2]
                  rw [ite_eq_right hja, ite_eq_right hjk]
                  rw [slideSt_piles_other hwf hcp1 hk1 hk1ne hcell hja hjk]
                  rw [pullSt_piles_inr_apply (u := st) (c := c2) (z := z) (k := k2) hk2 j]
                  rw [ite_eq_right hjk2]
  · simp only [pullSt_stock, slideSt_stock]
  · simp only [pullSt_waste, slideSt_waste]
  · simp only [pullSt_drawStep, slideSt_drawStep]




end CommuteStep

#print axioms CommuteStep.slideSt_piles_at
#print axioms CommuteStep.slide_data
#print axioms CommuteStep.step_comm_slide_pull
#print axioms CommuteStep.step_comm_slide_raise