import Orig2.KingOrbitFull
import Orig2.SeatMateStack


/-!
# Orig2.KingShufflePerm — the king-shuffle/anchor-permutation bridge

A `KingShuffle.hop` moves a bare bottomed king from its anchor `a` into
an empty anchor `e`.  The king bottoms its pile, the donor hidden deck
is empty, and the target is empty, so the moved run is the whole
face-up pile at `a`, and the step only exchanges the two piles: it is
exactly the anchor transposition `swap a e`.  This card lands that
transposition, its inverse laws, and the bridge

`KingShuffle u v → ∃ σ : AnchorPerm, v = u.permute σ`.

The proof is choice-free: the only classical-looking ingredient is
decidable equality on the seven anchors.
-/

namespace AnchorPerm

/-- The underlying function of the anchor transposition swapping `a`
and `e` (the identity when `a = e`). -/
def swapFun (a e : Anchor) (x : Anchor) : Anchor :=
  if x = a then e else if x = e then a else x

/-- The transposition sends its left point to its right point. -/
@[simp] theorem swapFun_a (a e : Anchor) : swapFun a e a = e := by
  unfold swapFun
  rw [ite_eq_left rfl]

/-- The transposition sends its right point to its left point. -/
@[simp] theorem swapFun_e (a e : Anchor) : swapFun a e e = a := by
  unfold swapFun
  by_cases h : e = a
  · rw [ite_eq_left h]
    exact h
  · rw [ite_eq_right h, ite_eq_left rfl]

/-- Away from both points the transposition is the identity. -/
theorem swapFun_of_ne {a e x : Anchor} (hxa : x ≠ a) (hxe : x ≠ e) :
    swapFun a e x = x := by
  unfold swapFun
  rw [ite_eq_right hxa, ite_eq_right hxe]

/-- The transposition is an involution (both inverse laws at once). -/
theorem swapFun_involutive (a e : Anchor) :
    ∀ x, swapFun a e (swapFun a e x) = x := by
  intro x
  by_cases hxa : x = a
  · subst hxa
    rw [swapFun_a, swapFun_e]
  · by_cases hxe : x = e
    · subst hxe
      rw [swapFun_e, swapFun_a]
    · rw [swapFun_of_ne hxa hxe, swapFun_of_ne hxa hxe]

/-- `AnchorPerm.swap a e` — the transposition of the anchors `a` and
`e`; the identity when `a = e`. -/
def swap (a e : Anchor) : AnchorPerm where
  toFun := swapFun a e
  invFun := swapFun a e
  left_inv := swapFun_involutive a e
  right_inv := swapFun_involutive a e

@[simp] theorem swap_toFun (a e x : Anchor) :
    (swap a e).toFun x = swapFun a e x := rfl

@[simp] theorem swap_invFun (a e x : Anchor) :
    (swap a e).invFun x = swapFun a e x := rfl

/-- The transposition acts on its left point. -/
theorem swap_apply_a (a e : Anchor) : (swap a e).toFun a = e :=
  swapFun_a a e

/-- The transposition acts on its right point. -/
theorem swap_apply_e (a e : Anchor) : (swap a e).toFun e = a :=
  swapFun_e a e

/-- The transposition fixes every other point. -/
theorem swap_apply_of_ne {a e x : Anchor} (hxa : x ≠ a) (hxe : x ≠ e) :
    (swap a e).toFun x = x :=
  swapFun_of_ne hxa hxe

end AnchorPerm

/-- A single bare-king hop is the anchor transposition of its donor and
target anchors: the step only exchanges the two piles. -/
theorem king_hop_permute {u v : State} {c : Card} {a e : Anchor}
    (hseat : seatOf u c = some (Sum.inl a))
    (hhid : (u.piles a).hidden = [])
    (hvac : (u.piles e).isEmpty = true)
    (hfired : State.step u (Move.tabToTab c (Sum.inl e)) = some v) :
    v = u.permute (AnchorPerm.swap a e) := by
  obtain ⟨hhold, hbelow⟩ := tfc_seatOf_of_inl hseat
  have hface : fromCard c (u.piles a).faceUp = (u.piles a).faceUp := by
    simpa [hbelow] using tfc_below_fromCard c ((u.piles a).faceUp)
  obtain ⟨a₀, hhold₀, -, -, hs⟩ := step_tabToTab_inv hfired
  have ha₀ : a₀ = a := Option.some.inj (hhold₀.symm.trans hhold)
  rw [ha₀] at hs
  rw [hs, hbelow, hface, Pile.afterRunRemoved_bare hhid, putRun_eq_inl]
  apply State.ext
  · rfl
  · funext x
    by_cases hxe : x = e
    · rw [hxe]
      simp only [State.setPile, State.permute,
        AnchorPerm.swap_invFun, AnchorPerm.swapFun_e]
      apply Pile.ext
      · exact hhid.symm
      · rfl
    · by_cases hxa : x = a
      · rw [hxa]
        have hae : a ≠ e := fun h => hxe (hxa.trans h)
        simp only [State.setPile, State.permute, ite_eq_right hae,
          AnchorPerm.swap_invFun, AnchorPerm.swapFun_a]
        obtain ⟨hhe, hfe⟩ := (Pile.isEmpty_eq (u.piles e)).mp hvac
        apply Pile.ext
        · exact hhe.symm
        · exact hfe.symm
      · simp only [State.setPile, State.permute, ite_eq_right hxe,
          ite_eq_right hxa, AnchorPerm.swap_invFun,
          AnchorPerm.swapFun_of_ne hxa hxe]
  · rfl
  · rfl
  · rfl

/-- **KingShuffle.is_permute** — every shuffle-reachable state is an
anchor relabeling of the origin: a sequence of bare-king hops composes
into one anchor permutation. -/
theorem KingShuffle.is_permute {u v : State} (h : KingShuffle u v) :
    ∃ σ : AnchorPerm, v = u.permute σ := by
  induction h with
  | refl u => exact ⟨AnchorPerm.id, by simp⟩
  | @hop u v w c a e hseat _hking hhid hvac hfired hrest ih =>
      obtain ⟨σ, hσ⟩ := ih
      refine ⟨σ.comp (AnchorPerm.swap a e), ?_⟩
      rw [hσ, king_hop_permute hseat hhid hvac hfired, State.permute_comp]

#print axioms KingShuffle.is_permute


/-!
# Orig2.KingVKPermExtend — extending a partial VK bijection to an anchor permutation
-/

/-- Computable test for `KingBottom w a`. -/
def kingBottomB (w : State) (a : Anchor) : Bool :=
  Card.universe.any (fun c =>
    decide (seatOf w c = some (Sum.inl a)) &&
    decide (c.rank = Rank.king) &&
    decide ((w.piles a).hidden = []))

/-- Computable test for `VKSet w a`. -/
def vkSetB (w : State) (a : Anchor) : Bool :=
  (w.piles a).isEmpty || kingBottomB w a

theorem kingBottomB_eq_true {w : State} {a : Anchor} :
    kingBottomB w a = true ↔ KingBottom w a := by
  unfold kingBottomB KingBottom
  rw [List.any_eq_true]
  constructor
  · rintro ⟨c, hc, h⟩
    simp only [Bool.and_eq_true] at h
    exact ⟨c, of_decide_eq_true h.1.1, of_decide_eq_true h.1.2,
      of_decide_eq_true h.2⟩
  · rintro ⟨c, hse, hk, hhid⟩
    exact ⟨c, Card.mem_universe c, by simp [hse, hk, hhid]⟩

theorem vkSetB_eq_true {w : State} {a : Anchor} :
    vkSetB w a = true ↔ VKSet w a := by
  unfold vkSetB VKSet VacantSpot
  rw [Bool.or_eq_true, kingBottomB_eq_true]

/-- Filtering a duplicate-free list stays duplicate-free. -/
theorem nodup_filter {α : Type} (p : α → Bool) {l : List α} (h : l.Nodup) :
    (l.filter p).Nodup := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
      rw [List.nodup_cons] at h
      rw [List.filter_cons]
      by_cases hp : p x = true
      · rw [if_pos hp, List.nodup_cons]
        refine ⟨?_, ih h.2⟩
        intro hx
        rw [List.mem_filter] at hx
        exact h.1 hx.1
      · rw [if_neg hp]
        exact ih h.2

/-- The computable enumeration of fuel-set anchors. -/
def vkList (w : State) : List Anchor :=
  Anchor.all.filter (vkSetB w)

theorem mem_vkList {w : State} {a : Anchor} :
    a ∈ vkList w ↔ VKSet w a := by
  unfold vkList
  rw [List.mem_filter]
  constructor
  · intro h
    exact vkSetB_eq_true.mp h.2
  · intro h
    exact ⟨Anchor.mem_all a, vkSetB_eq_true.mpr h⟩

theorem nodup_vkList (w : State) : (vkList w).Nodup := by
  unfold vkList
  exact nodup_filter _ (Anchor.all_nodup)

/-- Computable membership in a list. -/
def memB {α : Type} [DecidableEq α] (a : α) (l : List α) : Bool :=
  l.any (fun x => decide (x = a))

theorem memB_eq_true {α : Type} [DecidableEq α] {a : α} {l : List α} :
    memB a l = true ↔ a ∈ l := by
  unfold memB
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, h⟩
    rw [← of_decide_eq_true h]
    exact hx
  · intro h
    exact ⟨a, h, by simp⟩

/-- First-match lookup in a list of pairs. -/
def lookup {α β : Type} [DecidableEq α] (ps : List (α × β)) (a : α) : Option β :=
  match ps with
  | [] => none
  | (x, y) :: t => if x = a then some y else lookup t a

theorem lookup_eq_some_iff {α β : Type} [DecidableEq α] {ps : List (α × β)}
    {a : α} {b : β} (hnd : (ps.map Prod.fst).Nodup) :
    lookup ps a = some b ↔ (a, b) ∈ ps := by
  induction ps with
  | nil => simp [lookup]
  | cons p t ih =>
      obtain ⟨x, y⟩ := p
      rw [List.map_cons] at hnd
      rw [List.nodup_cons] at hnd
      simp only [lookup]
      by_cases hxa : x = a
      · subst a
        rw [if_pos rfl, Option.some.injEq]
        constructor
        · intro h
          subst h
          exact List.mem_cons_self ..
        · intro h
          rcases List.mem_cons.mp h with h | h
          · exact (Prod.mk.injEq ..).mp h |>.2.symm
          · exfalso
            exact hnd.1 (List.mem_map.mpr ⟨(x, b), h, rfl⟩)
      · rw [if_neg hxa, ih hnd.2]
        constructor
        · intro h
          rw [List.mem_cons]
          exact Or.inr h
        · intro h
          rw [List.mem_cons] at h
          rcases h with h | h
          · exfalso
            apply hxa
            exact (Prod.mk.injEq ..).mp h |>.1.symm
          · exact h

theorem lookup_eq_none_iff {α β : Type} [DecidableEq α] {ps : List (α × β)}
    {a : α} (hnd : (ps.map Prod.fst).Nodup) :
    lookup ps a = none ↔ a ∉ ps.map Prod.fst := by
  induction ps with
  | nil => simp [lookup]
  | cons p t ih =>
      obtain ⟨x, y⟩ := p
      rw [List.map_cons] at hnd
      rw [List.nodup_cons] at hnd
      simp only [lookup]
      by_cases hxa : x = a
      · subst a
        simp [hnd]
      · rw [if_neg hxa, ih hnd.2]
        constructor
        · intro h hmem
          rw [List.map_cons, List.mem_cons] at hmem
          rcases hmem with hx | hmem
          · exact hxa hx.symm
          · exact h hmem
        · intro h hmem
          exact h (by rw [List.map_cons, List.mem_cons]; exact Or.inr hmem)

#print axioms vkSetB_eq_true
#print axioms mem_vkList
#print axioms lookup_eq_some_iff
#print axioms lookup_eq_none_iff


/-- Removing one occurrence by filtering changes the length by one. -/
theorem length_filter_ne_of_mem {α : Type} [DecidableEq α] {d : List α} {x : α}
    (hd : d.Nodup) (hx : x ∈ d) :
    (d.filter (fun y => decide (y ≠ x))).length = d.length - 1 := by
  induction d with
  | nil => exact False.elim (by simpa using hx)
  | cons y ys ih =>
      rw [List.nodup_cons] at hd
      rw [List.filter_cons]
      by_cases hy : y = x
      · subst y
        have hfalse : decide (x ≠ x) = false := by simp
        rw [if_neg (by rw [hfalse]; simp)]
        have hfilter : ys.filter (fun z => decide (z ≠ x)) = ys := by
          rw [List.filter_eq_self]
          intro z hz
          have hzx : z ≠ x := by
            intro h
            subst h
            exact hd.1 hz
          exact decide_eq_true hzx
        rw [hfilter]
        simp
      · have hxys : x ∈ ys := by
          rcases List.mem_cons.mp hx with h | h
          · exact False.elim (hy h.symm)
          · exact h
        have htrue : decide (y ≠ x) = true := decide_eq_true hy
        rw [if_pos htrue]
        have hlen := ih hd.2 hxys
        simp only [List.length_cons]
        rw [hlen]
        have hpos : 0 < ys.length := List.length_pos_iff_exists_mem.mpr ⟨x, hxys⟩
        omega

/-- Counting the elements of a nodup sublist `d` inside a nodup list `l`. -/
theorem countP_memB_eq_length {α : Type} [DecidableEq α] {l d : List α}
    (hl : l.Nodup) (hd : d.Nodup) (hsub : ∀ a, a ∈ d → a ∈ l) :
    List.countP (fun a => memB a d) l = d.length := by
  induction l generalizing d with
  | nil =>
      cases d with
      | nil => simp [memB]
      | cons a t =>
          exact False.elim (by simpa using hsub a (List.mem_cons_self ..))
  | cons x xs ih =>
      rw [List.nodup_cons] at hl
      rw [List.countP_cons]
      by_cases hx : x ∈ d
      · let d' := d.filter (fun y => decide (y ≠ x))
        have hd' : d'.Nodup := nodup_filter _ hd
        have hdlen : d'.length = d.length - 1 := length_filter_ne_of_mem hd hx
        have hsub' : ∀ a, a ∈ d' → a ∈ xs := by
          intro a ha
          rw [List.mem_filter] at ha
          have ha_d : a ∈ d := ha.1
          have hane : decide (a ≠ x) = true := ha.2
          have hax : a ≠ x := of_decide_eq_true hane
          have ha_l : a ∈ x :: xs := hsub a ha_d
          rcases List.mem_cons.mp ha_l with h | h
          · exact False.elim (hax h)
          · exact h
        have hcount : List.countP (fun a => memB a d) xs =
            List.countP (fun a => memB a d') xs := by
          apply List.countP_congr
          intro y hy
          have hyx : y ≠ x := by
            intro h
            rw [h] at hy
            exact hl.1 hy
          rw [memB_eq_true, memB_eq_true, List.mem_filter]
          constructor
          · intro hyd
            exact ⟨hyd, decide_eq_true hyx⟩
          · intro h
            exact h.1
        have hih := ih hl.2 hd' hsub'
        have hxmem : memB x d = true := memB_eq_true.mpr hx
        rw [if_pos hxmem, hcount, hih, hdlen]
        have hpos : 0 < d.length := List.length_pos_iff_exists_mem.mpr ⟨x, hx⟩
        omega
      · have hxmem : memB x d = false := by
          cases hb : memB x d
          · rfl
          · exact False.elim (hx (memB_eq_true.mp hb))
        rw [if_neg (by rw [hxmem]; simp)]
        simpa using ih hl.2 hd (by
          intro a ha
          have ha_l : a ∈ x :: xs := hsub a ha
          rcases List.mem_cons.mp ha_l with h | h
          · exact False.elim (hx (by rwa [h] at ha))
          · exact h)
/-- The two complementary filters partition the list length. -/
theorem length_filter_add_filter_not {α : Type} (p : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter (fun a => p a == false)).length = l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.filter_cons, List.filter_cons]
      by_cases hp : p x = true
      · rw [if_pos hp]
        have h2 : (p x == false) = false := by simp [hp]
        rw [if_neg (by rw [h2]; simp)]
        simp only [List.length_cons] at ih ⊢
        omega
      · have h2 : (p x == false) = true := by
          cases h : p x
          · rfl
          · exact False.elim (hp h)
        rw [if_neg hp, if_pos h2]
        simp only [List.length_cons] at ih ⊢
        omega

#print axioms countP_memB_eq_length
#print axioms length_filter_add_filter_not



/-- The forward map of the extension: prescribed pairs first, then the
zipped complement pairs, and the identity outside the union. -/
def sigmaFun (pairs extra : List (Anchor × Anchor)) (a : Anchor) : Anchor :=
  if memB a (pairs.map Prod.fst) = true then
    (lookup pairs a).getD a
  else if memB a (extra.map Prod.fst) = true then
    (lookup extra a).getD a
  else a

theorem sigmaFun_of_mem_pairs {pairs extra : List (Anchor × Anchor)}
    (hnd : (pairs.map Prod.fst).Nodup) {a b : Anchor} (h : (a, b) ∈ pairs) :
    sigmaFun pairs extra a = b := by
  have hmem : memB a (pairs.map Prod.fst) = true := by
    rw [memB_eq_true]
    exact List.mem_map.mpr ⟨(a, b), h, rfl⟩
  have hl : lookup pairs a = some b :=
    (lookup_eq_some_iff (ps := pairs) (a := a) (b := b) hnd).mpr h
  simp [sigmaFun, hmem, hl]

theorem sigmaFun_of_mem_extra {pairs extra : List (Anchor × Anchor)}
    (hnd : (extra.map Prod.fst).Nodup) {a b : Anchor}
    (hdom : memB a (pairs.map Prod.fst) = false) (h : (a, b) ∈ extra) :
    sigmaFun pairs extra a = b := by
  have hmem : memB a (extra.map Prod.fst) = true := by
    rw [memB_eq_true]
    exact List.mem_map.mpr ⟨(a, b), h, rfl⟩
  have hl : lookup extra a = some b :=
    (lookup_eq_some_iff (ps := extra) (a := a) (b := b) hnd).mpr h
  rw [sigmaFun]
  rw [if_neg (by rw [hdom]; simp), if_pos hmem, hl]
  rfl

theorem sigmaFun_eq_self {pairs extra : List (Anchor × Anchor)} {a : Anchor}
    (hdom : memB a (pairs.map Prod.fst) = false)
    (hextra : memB a (extra.map Prod.fst) = false) :
    sigmaFun pairs extra a = a := by
  rw [sigmaFun]
  rw [if_neg (by rw [hdom]; simp), if_neg (by rw [hextra]; simp)]

/-- A Bool cannot be both `false` and `true`. -/
theorem false_of_eq_false_eq_true {b : Bool} (hf : b = false) (ht : b = true) : False := by
  rw [hf] at ht
  exact Bool.noConfusion ht

#print axioms sigmaFun_of_mem_pairs
#print axioms sigmaFun_of_mem_extra
#print axioms sigmaFun_eq_self

theorem exists_perm_extending_pairs {w : State} (pairs : List (Anchor × Anchor))
    (dom_nodup : (pairs.map Prod.fst).Nodup)
    (cod_nodup : (pairs.map Prod.snd).Nodup)
    (dom_VK : ∀ p ∈ pairs, VKSet w p.1)
    (cod_VK : ∀ p ∈ pairs, VKSet w p.2) :
    ∃ σ : AnchorPerm,
      (∀ p ∈ pairs, σ.toFun p.1 = p.2) ∧
      (∀ j, VKSet w j ↔ VKSet w (σ.toFun j)) ∧
      (∀ j, ¬ VKSet w j → σ.toFun j = j) := by
  let dom := pairs.map Prod.fst
  let cod := pairs.map Prod.snd
  let vk := vkList w
  let extraDom := vk.filter (fun a => memB a dom == false)
  let extraCod := vk.filter (fun b => memB b cod == false)
  have hvk : vk.Nodup := nodup_vkList w
  have hdomNodup : dom.Nodup := dom_nodup
  have hcodNodup : cod.Nodup := cod_nodup
  have hdom_sub : ∀ a, a ∈ dom → a ∈ vk := by
    intro a ha
    rw [mem_vkList]
    rcases List.mem_map.mp ha with ⟨p, hp, hfst⟩
    obtain ⟨x, y⟩ := p
    have hx : x = a := by simpa using hfst
    subst a
    exact dom_VK (x, y) hp
  have hcod_sub : ∀ a, a ∈ cod → a ∈ vk := by
    intro a ha
    rw [mem_vkList]
    rcases List.mem_map.mp ha with ⟨p, hp, hsnd⟩
    obtain ⟨x, y⟩ := p
    have hy : y = a := by simpa using hsnd
    subst a
    exact cod_VK (x, y) hp
  have hdomCount : (vk.filter (fun a => memB a dom)).length = dom.length := by
    rw [← List.countP_eq_length_filter]
    exact countP_memB_eq_length hvk hdomNodup hdom_sub
  have hcodCount : (vk.filter (fun b => memB b cod)).length = cod.length := by
    rw [← List.countP_eq_length_filter]
    exact countP_memB_eq_length hvk hcodNodup hcod_sub
  have hdomCodLen : dom.length = cod.length := by simp [dom, cod]
  have hpartDom : (vk.filter (fun a => memB a dom)).length + extraDom.length = vk.length := by
    exact length_filter_add_filter_not (fun a => memB a dom) vk
  have hpartCod : (vk.filter (fun b => memB b cod)).length + extraCod.length = vk.length := by
    exact length_filter_add_filter_not (fun b => memB b cod) vk
  have hExtraLen : extraDom.length = extraCod.length := by omega
  have hExtraDomNodup : extraDom.Nodup := nodup_filter _ hvk
  have hExtraCodNodup : extraCod.Nodup := nodup_filter _ hvk
  let extra := extraDom.zip extraCod
  have hExtraFst : extra.map Prod.fst = extraDom := by
    change (extraDom.zip extraCod).map Prod.fst = extraDom
    exact List.map_fst_zip (by omega)
  have hExtraSnd : extra.map Prod.snd = extraCod := by
    change (extraDom.zip extraCod).map Prod.snd = extraCod
    exact List.map_snd_zip (by omega)
  have hExtraNodupFst : (extra.map Prod.fst).Nodup := by
    rw [hExtraFst]
    exact hExtraDomNodup
  have hExtraNodupSnd : (extra.map Prod.snd).Nodup := by
    rw [hExtraSnd]
    exact hExtraCodNodup
  have hσ_mem_dom : ∀ {a b : Anchor}, (a, b) ∈ pairs → sigmaFun pairs extra a = b := by
    intro a b h
    exact sigmaFun_of_mem_pairs dom_nodup h
  have hσ_mem_extra : ∀ {a b : Anchor}, (a, b) ∈ extra → sigmaFun pairs extra a = b := by
    intro a b h
    have hfst : a ∈ extra.map Prod.fst := List.mem_map.mpr ⟨(a, b), h, rfl⟩
    have haExtraDom : a ∈ extraDom := by
      rw [← hExtraFst]
      exact hfst
    have hdomFalse : memB a dom = false := by
      rw [List.mem_filter] at haExtraDom
      simpa using haExtraDom.2
    exact sigmaFun_of_mem_extra hExtraNodupFst hdomFalse h
  have hσinv_mem_cod : ∀ {a b : Anchor},
      (a, b) ∈ pairs → sigmaFun (pairs.map Prod.swap) (extra.map Prod.swap) b = a := by
    intro a b h
    have hswap : (b, a) ∈ pairs.map Prod.swap := List.mem_map.mpr ⟨(a, b), h, rfl⟩
    have hnd : ((pairs.map Prod.swap).map Prod.fst).Nodup := by
      simpa [List.map_map, Function.comp_def] using cod_nodup
    exact sigmaFun_of_mem_pairs hnd hswap
  have hσinv_mem_extra : ∀ {a b : Anchor},
      (a, b) ∈ extra → sigmaFun (pairs.map Prod.swap) (extra.map Prod.swap) b = a := by
    intro a b h
    have hswap : (b, a) ∈ extra.map Prod.swap := List.mem_map.mpr ⟨(a, b), h, rfl⟩
    have hbSnd : b ∈ extra.map Prod.snd := List.mem_map.mpr ⟨(a, b), h, rfl⟩
    have hbExtraCod : b ∈ extraCod := by
      rw [← hExtraSnd]
      exact hbSnd
    have hcodFalse : memB b cod = false := by
      rw [List.mem_filter] at hbExtraCod
      simpa using hbExtraCod.2
    have hdomFalse : memB b ((pairs.map Prod.swap).map Prod.fst) = false := by
      simpa [List.map_map, Function.comp_def] using hcodFalse
    have hnd : ((extra.map Prod.swap).map Prod.fst).Nodup := by
      simpa [List.map_map, Function.comp_def, hExtraSnd] using hExtraCodNodup
    exact sigmaFun_of_mem_extra hnd hdomFalse hswap
  have hleft : ∀ a, sigmaFun (pairs.map Prod.swap) (extra.map Prod.swap)
      (sigmaFun pairs extra a) = a := by
    intro a
    by_cases hdomTrue : memB a dom = true
    · have haDom : a ∈ dom := memB_eq_true.mp hdomTrue
      rcases List.mem_map.mp haDom with ⟨p, hp, hfst⟩
      obtain ⟨x, y⟩ := p
      have hx : x = a := by simpa using hfst
      subst a
      have hpair : (x, y) ∈ pairs := hp
      have hσ : sigmaFun pairs extra x = y := hσ_mem_dom hpair
      rw [hσ]
      exact hσinv_mem_cod hpair
    · have hdomFalse : memB a dom = false := by
        cases hb : memB a dom
        · rfl
        · exact False.elim (hdomTrue hb)
      by_cases hextraTrue : memB a (extra.map Prod.fst) = true
      · have haExtra : a ∈ extra.map Prod.fst := memB_eq_true.mp hextraTrue
        rcases List.mem_map.mp haExtra with ⟨p, hp, hfst⟩
        obtain ⟨x, y⟩ := p
        have hx : x = a := by simpa using hfst
        subst a
        have hpair : (x, y) ∈ extra := hp
        have hσ : sigmaFun pairs extra x = y := hσ_mem_extra hpair
        rw [hσ]
        exact hσinv_mem_extra hpair
      · have hextraFalse : memB a (extra.map Prod.fst) = false := by
          cases hb : memB a (extra.map Prod.fst)
          · rfl
          · exact False.elim (hextraTrue hb)
        have hσ : sigmaFun pairs extra a = a := sigmaFun_eq_self hdomFalse hextraFalse
        rw [hσ]
        have hcodFalse : memB a cod = false := by
          have hnotCod : ¬ a ∈ cod := by
            intro hcodmem
            have hvk : a ∈ vk := hcod_sub a hcodmem
            have haExtraDom : a ∈ extraDom := by
              rw [List.mem_filter]
              exact ⟨hvk, by simp [hdomFalse]⟩
            have haFst : a ∈ extra.map Prod.fst := by
              rw [hExtraFst]
              exact haExtraDom
            exact False.elim (false_of_eq_false_eq_true hextraFalse (memB_eq_true.mpr haFst))
          cases hb : memB a cod
          · rfl
          · exact False.elim (hnotCod (memB_eq_true.mp hb))
        have hExtraSndFalse : memB a (extra.map Prod.snd) = false := by
          have hnotSnd : ¬ a ∈ extra.map Prod.snd := by
            intro hmem
            have haExtraCod : a ∈ extraCod := by
              rw [← hExtraSnd]
              exact hmem
            have haExtraDom : a ∈ extraDom := by
              rw [List.mem_filter] at haExtraCod
              rw [List.mem_filter]
              exact ⟨haExtraCod.1, by simp [hdomFalse]⟩
            have haFst : a ∈ extra.map Prod.fst := by
              rw [hExtraFst]
              exact haExtraDom
            exact False.elim (false_of_eq_false_eq_true hextraFalse (memB_eq_true.mpr haFst))
          cases hb : memB a (extra.map Prod.snd)
          · rfl
          · exact False.elim (hnotSnd (memB_eq_true.mp hb))
        have hcodFalse' : memB a ((pairs.map Prod.swap).map Prod.fst) = false := by
          simpa [List.map_map, Function.comp_def] using hcodFalse
        have hExtraSndFalse' : memB a ((extra.map Prod.swap).map Prod.fst) = false := by
          simpa [List.map_map, Function.comp_def] using hExtraSndFalse
        exact sigmaFun_eq_self hcodFalse' hExtraSndFalse'
  have hright : ∀ a, sigmaFun pairs extra
      (sigmaFun (pairs.map Prod.swap) (extra.map Prod.swap) a) = a := by
    intro a
    by_cases hcodTrue : memB a cod = true
    · have haCod : a ∈ cod := memB_eq_true.mp hcodTrue
      rcases List.mem_map.mp haCod with ⟨p, hp, hsnd⟩
      obtain ⟨x, y⟩ := p
      have hy : y = a := by simpa using hsnd
      subst a
      have hpair : (x, y) ∈ pairs := hp
      have hσinv : sigmaFun (pairs.map Prod.swap) (extra.map Prod.swap) y = x :=
        hσinv_mem_cod hpair
      rw [hσinv]
      exact hσ_mem_dom hpair
    · have hcodFalse : memB a cod = false := by
        cases hb : memB a cod
        · rfl
        · exact False.elim (hcodTrue hb)
      by_cases hextraTrue : memB a (extra.map Prod.snd) = true
      · have haExtra : a ∈ extra.map Prod.snd := memB_eq_true.mp hextraTrue
        rcases List.mem_map.mp haExtra with ⟨p, hp, hsnd⟩
        obtain ⟨x, y⟩ := p
        have hy : y = a := by simpa using hsnd
        subst a
        have hpair : (x, y) ∈ extra := hp
        have hσinv : sigmaFun (pairs.map Prod.swap) (extra.map Prod.swap) y = x :=
          hσinv_mem_extra hpair
        rw [hσinv]
        exact hσ_mem_extra hpair
      · have hextraFalse : memB a (extra.map Prod.snd) = false := by
          cases hb : memB a (extra.map Prod.snd)
          · rfl
          · exact False.elim (hextraTrue hb)
        have hcodFalse' : memB a ((pairs.map Prod.swap).map Prod.fst) = false := by
          simpa [List.map_map, Function.comp_def] using hcodFalse
        have hextraFalse' : memB a ((extra.map Prod.swap).map Prod.fst) = false := by
          simpa [List.map_map, Function.comp_def] using hextraFalse
        have hσinv : sigmaFun (pairs.map Prod.swap) (extra.map Prod.swap) a = a :=
          sigmaFun_eq_self hcodFalse' hextraFalse'
        rw [hσinv]
        have hdomFalse : memB a dom = false := by
          have hnotDom : ¬ a ∈ dom := by
            intro hdommem
            have hvk : a ∈ vk := hdom_sub a hdommem
            have haExtraCod : a ∈ extraCod := by
              rw [List.mem_filter]
              exact ⟨hvk, by simp [hcodFalse]⟩
            have haSnd : a ∈ extra.map Prod.snd := by
              rw [hExtraSnd]
              exact haExtraCod
            exact False.elim (false_of_eq_false_eq_true hextraFalse (memB_eq_true.mpr haSnd))
          cases hb : memB a dom
          · rfl
          · exact False.elim (hnotDom (memB_eq_true.mp hb))
        have hExtraFstFalse : memB a (extra.map Prod.fst) = false := by
          have hnotFst : ¬ a ∈ extra.map Prod.fst := by
            intro hmem
            have haExtraDom : a ∈ extraDom := by
              rw [← hExtraFst]
              exact hmem
            have haExtraCod : a ∈ extraCod := by
              rw [List.mem_filter] at haExtraDom
              rw [List.mem_filter]
              exact ⟨haExtraDom.1, by simp [hcodFalse]⟩
            have haSnd : a ∈ extra.map Prod.snd := by
              rw [hExtraSnd]
              exact haExtraCod
            exact False.elim (false_of_eq_false_eq_true hextraFalse (memB_eq_true.mpr haSnd))
          cases hb : memB a (extra.map Prod.fst)
          · rfl
          · exact False.elim (hnotFst (memB_eq_true.mp hb))
        exact sigmaFun_eq_self hdomFalse hExtraFstFalse
  let σ : AnchorPerm :=
    { toFun := sigmaFun pairs extra
      invFun := sigmaFun (pairs.map Prod.swap) (extra.map Prod.swap)
      left_inv := hleft
      right_inv := hright }
  refine ⟨σ, ?_, ?_, ?_⟩
  · intro p hp
    exact hσ_mem_dom hp
  · intro j
    constructor
    · intro hj
      have hjvk : j ∈ vk := (mem_vkList (w := w)).mpr hj
      by_cases hdomTrue : memB j dom = true
      · have haDom : j ∈ dom := memB_eq_true.mp hdomTrue
        rcases List.mem_map.mp haDom with ⟨p, hp, hfst⟩
        obtain ⟨x, y⟩ := p
        have hx : x = j := by simpa using hfst
        subst j
        have hpair : (x, y) ∈ pairs := hp
        have hσ : sigmaFun pairs extra x = y := hσ_mem_dom hpair
        change VKSet w (sigmaFun pairs extra x)
        rw [hσ]
        exact (mem_vkList (w := w)).mp (hcod_sub y (List.mem_map.mpr ⟨(x, y), hpair, rfl⟩))
      · have hdomFalse : memB j dom = false := by
          cases hb : memB j dom
          · rfl
          · exact False.elim (hdomTrue hb)
        have hjExtraDom : j ∈ extraDom := by
          rw [List.mem_filter]
          exact ⟨hjvk, by simp [hdomFalse]⟩
        have hjFst : j ∈ extra.map Prod.fst := by
          rw [hExtraFst]
          exact hjExtraDom
        rcases List.mem_map.mp hjFst with ⟨p, hp, hfst⟩
        obtain ⟨x, y⟩ := p
        have hx : x = j := by simpa using hfst
        subst j
        have hpair : (x, y) ∈ extra := hp
        have hσ : sigmaFun pairs extra x = y := hσ_mem_extra hpair
        change VKSet w (sigmaFun pairs extra x)
        rw [hσ]
        have hySnd : y ∈ extra.map Prod.snd := List.mem_map.mpr ⟨(x, y), hpair, rfl⟩
        have hyCod : y ∈ extraCod := by
          rw [← hExtraSnd]
          exact hySnd
        exact (mem_vkList (w := w)).mp (List.mem_filter.mp hyCod).1
    · intro hj
      by_cases hdomTrue : memB j dom = true
      · exact (mem_vkList (w := w)).mp (hdom_sub j (memB_eq_true.mp hdomTrue))
      · have hdomFalse : memB j dom = false := by
          cases hb : memB j dom
          · rfl
          · exact False.elim (hdomTrue hb)
        by_cases hextraTrue : memB j (extra.map Prod.fst) = true
        · have hjFst : j ∈ extra.map Prod.fst := memB_eq_true.mp hextraTrue
          have hjExtraDom : j ∈ extraDom := by
            rw [← hExtraFst]
            exact hjFst
          exact (mem_vkList (w := w)).mp ((List.mem_filter.mp hjExtraDom).1)
        · have hextraFalse : memB j (extra.map Prod.fst) = false := by
            cases hb : memB j (extra.map Prod.fst)
            · rfl
            · exact False.elim (hextraTrue hb)
          have hσ : sigmaFun pairs extra j = j := sigmaFun_eq_self hdomFalse hextraFalse
          exact hσ ▸ (by simpa [σ] using hj)
  · intro j hj
    have hnotvk : j ∉ vk := fun h => hj ((mem_vkList (w := w)).mp h)
    have hdomFalse : memB j dom = false := by
      cases hb : memB j dom
      · rfl
      · exact False.elim (hnotvk (hdom_sub j (memB_eq_true.mp hb)))
    have hextraFalse : memB j (extra.map Prod.fst) = false := by
      cases hb : memB j (extra.map Prod.fst)
      · rfl
      · have hjExtraDom : j ∈ extraDom := by
          rw [← hExtraFst]
          exact memB_eq_true.mp hb
        exact False.elim (hnotvk ((List.mem_filter.mp hjExtraDom).1))
    exact sigmaFun_eq_self hdomFalse hextraFalse

#print axioms exists_perm_extending_pairs





/-!
# Orig2.KingShuffleRealize — realizing a prescribed VK permutation

A `KingShuffle` only exchanges a bottomed bare king with the current
vacancy.  On the fuel set `VKSet` this is a permutation, and every
shuffle induces an anchor permutation (`KingShuffle.is_permute`).  This
card proves the converse form needed by the realization argument: a
prescribed `AnchorPerm` that preserves `VKSet` and fixes every non-VK
anchor is realized by a shuffle, i.e. the target state is exactly the
anchor relabeling by that permutation.

The proof enumerates the bottomed kings (`kingsOf`), sends each king to
the permutation image of its anchor, invokes
`king_assignment_reachable`, and then pins the induced permutation on
the fuel set: the king-bottom anchors are matched card by card, the
unique vacancy is the remaining fuel node, and non-VK anchors are fixed
by both permutations.
-/

namespace State

/-- Anchor relabeling acts on the seat readout by relabeling its anchor
face. -/
theorem seatOf_permute {σ : AnchorPerm} {st : State} (hwf : st.WF) (c : Card) :
    seatOf (st.permute σ) c = (seatOf st c).map (Base.permute σ) := by
  unfold seatOf
  rw [State.pileHolding_permute_option (σ := σ) hwf (c := c)]
  cases h : st.pileHolding c with
  | none => rfl
  | some a =>
      have hpile : (st.permute σ).piles (σ.toFun a) = st.piles a := by
        simp [State.permute, σ.left_inv]
      cases hlast : (below c (st.piles a).faceUp).getLast?
      · simp [hpile, hlast, Base.permute]
      · simp [hpile, hlast, Base.permute]

end State

namespace AnchorPerm

/-- An anchor permutation is determined by its forward map: the inverse
is forced because the forward map is injective. -/
theorem ext_toFun {π σ : AnchorPerm} (h : π.toFun = σ.toFun) : π = σ := by
  have hinv : π.invFun = σ.invFun := by
    funext x
    have h1 : π.toFun (π.invFun x) = x := π.right_inv x
    have h2 : σ.toFun (σ.invFun x) = x := σ.right_inv x
    have h2' : π.toFun (σ.invFun x) = x := by
      rw [h]
      exact h2
    have hfun : π.toFun (π.invFun x) = π.toFun (σ.invFun x) :=
      h1.trans h2'.symm
    have hinj : Function.Injective π.toFun := by
      intro a b hab
      have h' := congrArg π.invFun hab
      simpa [π.left_inv] using h'
    exact hinj hfun
  cases π with
  | mk f g hl hr =>
    cases σ with
    | mk f' g' hl' hr' =>
      simp only at h hinv
      subst h
      subst hinv
      rfl

end AnchorPerm

/-- Membership in a two-point swap is invariant when both swap points
satisfy the predicate. -/
theorem vk_swap_iff {P : Anchor → Prop} {a e : Anchor}
    (ha : P a) (he : P e) (j : Anchor) :
    P (AnchorPerm.swapFun a e j) ↔ P j := by
  unfold AnchorPerm.swapFun
  by_cases hja : j = a
  · subst hja
    rw [ite_eq_left rfl]
    exact ⟨fun _ => ha, fun _ => he⟩
  · by_cases hje : j = e
    · subst hje
      rw [ite_eq_right hja, ite_eq_left rfl]
      exact ⟨fun _ => he, fun _ => ha⟩
    · rw [ite_eq_right hja, ite_eq_right hje]

namespace KingShuffle

/-- The prescribed target of a card: the permutation image of the
anchor where the card bottoms.  Off a bottomed seat the value is
irrelevant; `Anchor.p0` is a choice-free default. -/
private def targetSeat (σ : AnchorPerm) (u : State) (c : Card) : Anchor :=
  match seatOf u c with
  | some (Sum.inl a) => σ.toFun a
  | _ => Anchor.p0

/-- On a bottomed seat the target is the permutation image. -/
private theorem targetSeat_of_seat {σ : AnchorPerm} {u : State} {c : Card}
    {a : Anchor} (h : seatOf u c = some (Sum.inl a)) :
    targetSeat σ u c = σ.toFun a := by
  unfold targetSeat
  rw [h]

/-- Computable test for a king-bottom anchor, searched through the
enumerated bottomed kings. -/
private def kingBottomBRealize (u : State) (j : Anchor) : Bool :=
  (kingsOf u).any (fun c => decide (seatOf u c = some (Sum.inl j)))

/-- The computable king-bottom test is exact. -/
private theorem kingBottomBRealize_iff {u : State} (hwf : u.WF) (j : Anchor) :
    kingBottomBRealize u j = true ↔ KingBottom u j := by
  unfold kingBottomBRealize
  rw [List.any_eq_true]
  constructor
  · rintro ⟨c, hc, hdec⟩
    have hse : seatOf u c = some (Sum.inl j) := of_decide_eq_true hdec
    obtain ⟨a, hkb, hse'⟩ := (mem_kingsOf hwf).mp hc
    have haj : a = j := Sum.inl.inj (Option.some.inj (hse'.symm.trans hse))
    subst haj
    exact hkb
  · intro hkb
    obtain ⟨c, hse, hkng, hhid⟩ := hkb
    have hc : c ∈ kingsOf u :=
      (mem_kingsOf hwf).mpr ⟨j, ⟨c, hse, hkng, hhid⟩, hse⟩
    exact ⟨c, hc, decide_eq_true hse⟩

/-- Computable test for `VKSet`. -/
private def vkSetBRealize (u : State) (j : Anchor) : Bool :=
  (u.piles j).isEmpty || kingBottomBRealize u j

/-- The computable `VKSet` test is exact. -/
private theorem vkSetBRealize_iff {u : State} (hwf : u.WF) (j : Anchor) :
    vkSetBRealize u j = true ↔ VKSet u j := by
  unfold vkSetBRealize VKSet
  rw [Bool.or_eq_true, kingBottomBRealize_iff hwf]

/-- **KingShuffle.is_permute_vk** — the anchor permutation induced by a
shuffle preserves `VKSet` and fixes every non-VK anchor.  The latter is
the semantic content of the fact that each hop transposes a king-bottom
anchor with the vacancy, both of which lie in `VKSet`. -/
theorem is_permute_vk {u v : State} (h : KingShuffle u v) :
    u.WF → ∃ π : AnchorPerm, v = u.permute π ∧
      (∀ j, VKSet u j ↔ VKSet u (π.toFun j)) ∧
      (∀ j, ¬ VKSet u j → π.toFun j = j) := by
  induction h with
  | refl u =>
      intro _
      exact ⟨AnchorPerm.id, by simp, fun _ => Iff.rfl, fun _ _ => rfl⟩
  | @hop u u2 v c a e hseat hking hhid hvac hfired hrest ih =>
      intro hwf
      have hwf2 : u2.WF := tfc_tabToTab_wf hwf hfired
      obtain ⟨π, hv, hVK, hfix⟩ := ih hwf2
      have hstep_perm : u2 = u.permute (AnchorPerm.swap a e) :=
        king_hop_permute hseat hhid hvac hfired
      have hrev : reversibleAtW u (Move.tabToTab c (Sum.inl e)) := by
        apply (tabToTabR_iff_reversibleAtW hwf c (Sum.inl e)).mp
        obtain ⟨hhold, hbelow⟩ := tfc_seatOf_of_inl hseat
        have hcp : u.canPlace c (Sum.inl e) = true := tfa_canPlace_inl hvac hking
        simp only [tabToTabR, hhold, hcp, hbelow, hhid]
        rw [decide_eq_true hking]
      have hVK_hop : ∀ j, VKSet u j ↔ VKSet u2 j :=
        orbit_vk_step hwf hfired hrev
      have ha_u : VKSet u a := Or.inr ⟨c, hseat, hking, hhid⟩
      have he_u : VKSet u e := Or.inl hvac
      have ha_2 : VKSet u2 a := (hVK_hop a).mp ha_u
      have he_2 : VKSet u2 e := (hVK_hop e).mp he_u
      refine ⟨π.comp (AnchorPerm.swap a e), ?_, ?_, ?_⟩
      · rw [hv, hstep_perm, State.permute_comp]
      · intro j
        rw [show (π.comp (AnchorPerm.swap a e)).toFun j =
            π.toFun ((AnchorPerm.swap a e).toFun j) from rfl]
        exact (hVK_hop j).trans
          (((vk_swap_iff ha_2 he_2 j).symm).trans
            ((hVK ((AnchorPerm.swap a e).toFun j)).trans
              (hVK_hop (π.toFun ((AnchorPerm.swap a e).toFun j))).symm))
      · intro j hj
        rw [show (π.comp (AnchorPerm.swap a e)).toFun j =
            π.toFun ((AnchorPerm.swap a e).toFun j) from rfl]
        have hja : j ≠ a := fun h => hj (h ▸ ha_u)
        have hje : j ≠ e := fun h => hj (h ▸ he_u)
        have hswap : (AnchorPerm.swap a e).toFun j = j :=
          AnchorPerm.swap_apply_of_ne hja hje
        rw [hswap]
        have hj2 : ¬ VKSet u2 j := fun h => hj ((hVK_hop j).mpr h)
        exact hfix j hj2

/-- **KingShuffle.realize_perm** — a VK-preserving anchor permutation
that fixes all non-VK anchors is realized by a shuffle: the prescribed
relabeling is reachable. -/
theorem realize_perm {u : State} (hwf : u.WF) (hvac : HasVacancy u)
    (huniq : ∀ a b, (u.piles a).isEmpty = true → (u.piles b).isEmpty = true → a = b)
    (σ : AnchorPerm)
    (hσVK : ∀ j, VKSet u j ↔ VKSet u (σ.toFun j))
    (hσfix : ∀ j, ¬ VKSet u j → σ.toFun j = j) :
    ∃ v : State, KingShuffle u v ∧ v = u.permute σ := by
  let cs : List Card := kingsOf u
  let τ : Card → Anchor := fun c => targetSeat σ u c
  have hk : ∀ c ∈ cs, KingBottomCard u c := by
    intro c hc
    exact (mem_kingsOf hwf).mp hc
  have hτ_of : ∀ {c a}, c ∈ cs → seatOf u c = some (Sum.inl a) →
      τ c = σ.toFun a := by
    intro c a _ hse
    exact targetSeat_of_seat hse
  have ht : ∀ c ∈ cs, VKSet u (τ c) := by
    intro c hc
    obtain ⟨a, hkb, hse⟩ := hk c hc
    rw [hτ_of hc hse]
    exact (hσVK a).mp (Or.inr hkb)
  have hnd : cs.Nodup := kingsOf_nodup u
  have hinj : ∀ c ∈ cs, ∀ c' ∈ cs, τ c = τ c' → c = c' := by
    intro c hc c' hc' heq
    obtain ⟨a, -, hse⟩ := hk c hc
    obtain ⟨a', -, hse'⟩ := hk c' hc'
    have hτ : τ c = σ.toFun a := hτ_of hc hse
    have hτ' : τ c' = σ.toFun a' := hτ_of hc' hse'
    have hσa : σ.toFun a = σ.toFun a' := by
      rw [← hτ, ← hτ', heq]
    have haa' : a = a' := by
      have h' := congrArg σ.invFun hσa
      simpa [σ.left_inv] using h'
    subst haa'
    exact king_seat_injective hse hse'
  obtain ⟨v, hks, hseat_v⟩ :=
    king_assignment_reachable hwf hvac τ cs hk ht hnd hinj
  obtain ⟨π, hv, hVK_π, hfix_π⟩ := KingShuffle.is_permute_vk hks hwf
  have hπ_king : ∀ a, KingBottom u a → π.toFun a = σ.toFun a := by
    intro a hkb
    obtain ⟨c, hse, hkng, hhid⟩ := hkb
    have hc : c ∈ cs :=
      (mem_kingsOf hwf).mpr ⟨a, ⟨c, hse, hkng, hhid⟩, hse⟩
    have hτc : τ c = σ.toFun a := hτ_of hc hse
    have h1 : seatOf (u.permute π) c = some (Sum.inl (π.toFun a)) := by
      rw [State.seatOf_permute hwf c, hse]
      rfl
    have h2 : seatOf (u.permute π) c = some (Sum.inl (σ.toFun a)) := by
      rw [← hv, hseat_v c hc, hτc]
    exact Sum.inl.inj (Option.some.inj (h1.symm.trans h2))
  obtain ⟨e0, he0⟩ := hvac
  have hnotKB_e0 : ¬ KingBottom u e0 := by
    rintro ⟨c, hse, -, -⟩
    obtain ⟨hhold, -⟩ := tfc_seatOf_of_inl hse
    have hmem : c ∈ (u.piles e0).faceUp := pileHolding_mem hhold
    obtain ⟨-, hface⟩ := (Pile.isEmpty_eq (u.piles e0)).mp he0
    rw [hface] at hmem
    exact absurd hmem (by simp)
  have hVK_dec : ∀ j, VKSet u j ↔ (KingBottom u j ∨ j = e0) := by
    intro j
    constructor
    · rintro (hv | hkb)
      · exact Or.inr (huniq j e0 hv he0)
      · exact Or.inl hkb
    · rintro (hkb | rfl)
      · exact Or.inr hkb
      · exact Or.inl he0
  have hπ_e0 : π.toFun e0 = σ.toFun e0 := by
    have he0VK : VKSet u e0 := Or.inl he0
    have hσe0VK : VKSet u (σ.toFun e0) := (hσVK e0).mp he0VK
    let j := π.invFun (σ.toFun e0)
    have hjπ : π.toFun j = σ.toFun e0 := π.right_inv (σ.toFun e0)
    have hjVK : VKSet u j := (hVK_π j).mpr (by rw [hjπ]; exact hσe0VK)
    rcases (hVK_dec j).mp hjVK with hkb | hje
    · exfalso
      have hπj : π.toFun j = σ.toFun j := hπ_king j hkb
      have hσeq : σ.toFun e0 = σ.toFun j := hjπ.symm.trans hπj
      have he0j : e0 = j := by
        have h' := congrArg σ.invFun hσeq
        simpa [σ.left_inv] using h'
      exact hnotKB_e0 (he0j.symm ▸ hkb)
    · rw [hje] at hjπ
      exact hjπ
  have hπσ_fun : π.toFun = σ.toFun := by
    funext j
    by_cases hkbB : kingBottomBRealize u j = true
    · exact hπ_king j ((kingBottomBRealize_iff hwf j).mp hkbB)
    · by_cases hvB : vkSetBRealize u j = true
      · have hjVK : VKSet u j := (vkSetBRealize_iff hwf j).mp hvB
        have hkb : ¬ KingBottom u j :=
          fun h => hkbB ((kingBottomBRealize_iff hwf j).mpr h)
        have hje : j = e0 := ((hVK_dec j).mp hjVK).resolve_left hkb
        subst hje
        exact hπ_e0
      · have hjVK : ¬ VKSet u j :=
          fun h => hvB ((vkSetBRealize_iff hwf j).mpr h)
        exact (hfix_π j hjVK).trans (hσfix j hjVK).symm
  have hπσ : π = σ := AnchorPerm.ext_toFun hπσ_fun
  refine ⟨v, hks, ?_⟩
  rw [hv, hπσ]

#print axioms KingShuffle.realize_perm
end KingShuffle


/-!
# Orig2.KingTrace — the first-vacancy split and the unconditional dichotomy

`KingOrbitFull` proves the fixed half of the king-orbit dichotomy and the
assignment theorem for members that already carry a vacancy.  This card adds
the first-vacancy split (a bare-king raise) and closes the completeness half by
conjugation:

* extend the desired king assignment to a permutation `σ` of the VK anchors
  (`exists_perm_extending_pairs`);
* realize `σ` by a `KingShuffle` at the first-vacancy state
  (`KingShuffle.realize_perm`);
* relabel the reverse path by `σ` (`sameOrbit_permute`).

The final state is `σ` applied to the target state, so its king seats are
`σ (seatOf w c) = τ c`.  This avoids a separate pending-king pull: the raised
king is carried by the relabeled reverse path.  Together with the fixed half
this yields `KingOrbitDichotomy`.
-/

/-- Convert `¬ (b = true)` to `b = false`. -/
theorem bool_eq_false_of_not_true {b : Bool} (h : ¬ b = true) : b = false := by
  cases b <;> simp_all

/-- A reversible slide out of a no-vacancy state cannot create a vacancy. -/
theorem no_vacancy_after_reversible_slide {u v : State} {x : Card} {b : Base}
    (hwf : u.WF) (hstep : State.step u (Move.tabToTab x b) = some v)
    (hrev : reversibleAtW u (Move.tabToTab x b))
    (hne : NoVacancy u) :
    NoVacancy v := by
  rcases orbit_empty_celldata hwf hstep hrev with
    hpoint | ⟨a, a', haa', hva, hua', hua, hva', hother⟩
  · intro j
    rw [← hpoint j]
    exact hne j
  · exfalso
    exact absurd hua' (hne a')

/-- A witness walk whose every step starts and ends in a no-vacancy state. -/
inductive NVWalk : State → List Move → State → Prop
  | nil (s : State) : NVWalk s [] s
  | cons {s s1 s' : State} {m : Move} {ρ : List Move}
      (hrev : reversibleAtW s m) (hno_s : NoVacancy s) (hno_s1 : NoVacancy s1)
      (hstep : State.step s m = some s1) (hrest : NVWalk s1 ρ s') :
      NVWalk s (m :: ρ) s'

theorem seatOf_NVWalk {w s0 : State} {ρ : List Move} (h : NVWalk w ρ s0)
    (hwf : w.WF) {c : Card} (hc : KingBottomCard w c) :
    seatOf s0 c = seatOf w c := by
  induction h with
  | nil s => rfl
  | @cons s s1 s' m ρ hrev hno_s hno_s1 hstep hrest ih =>
      have hwf1 : s1.WF := step_wf hwf hstep
      have hseat := seatOf_no_vacancy_step hwf hstep hrev hno_s hno_s1 hc
      have hc1 : KingBottomCard s1 c := by
        obtain ⟨a, hkb, hseat_c⟩ := hc
        have hvk : VKSet s1 a :=
          (vk_step_rev hwf hstep hrev a).mp (Or.inr hkb)
        have hkb1 : KingBottom s1 a :=
          (vkSet_kingBottom_of_no_vacancy hno_s1 a).mp hvk
        exact ⟨a, hkb1, by rw [hseat]; exact hseat_c⟩
      have ih' := ih hwf1 hc1
      exact ih'.trans hseat

theorem vk_NVWalk {w s0 : State} {ρ : List Move} (h : NVWalk w ρ s0)
    (hwf : w.WF) : ∀ j, VKSet w j ↔ VKSet s0 j := by
  induction h with
  | nil s => intro j; rfl
  | @cons s s1 s' m ρ hrev hno_s hno_s1 hstep hrest ih =>
      intro j
      have hwf1 : s1.WF := step_wf hwf hstep
      exact (vk_step_rev hwf hstep hrev j).trans (ih hwf1 j)

theorem NVWalk_noVacancy_end {w s0 : State} {ρ : List Move} (h : NVWalk w ρ s0)
    (hno_w : NoVacancy w) : NoVacancy s0 := by
  induction h with
  | nil s => exact hno_w
  | @cons s s1 s' m ρ hrev hno_s hno_s1 hstep hrest ih =>
      exact ih hno_s1

theorem kingBottomCard_NVWalk {w s0 : State} {ρ : List Move} (h : NVWalk w ρ s0)
    (hno_w : NoVacancy w) (hwf : w.WF) {c : Card} (hc : KingBottomCard w c) :
    KingBottomCard s0 c := by
  have hc_keep : KingBottomCard w c := hc
  obtain ⟨a, hkb, hseat_c⟩ := hc
  have hseat := seatOf_NVWalk h hwf hc_keep
  have hvk_w : VKSet w a := Or.inr hkb
  have hvk_s0 : VKSet s0 a := (vk_NVWalk h hwf a).mp hvk_w
  have hno_s0 := NVWalk_noVacancy_end h hno_w
  have hkb_s0 : KingBottom s0 a :=
    (vkSet_kingBottom_of_no_vacancy hno_s0 a).mp hvk_s0
  exact ⟨a, hkb_s0, by rw [hseat]; exact hseat_c⟩

/-- Bool test for the finite vacancy existential. -/
def hasVacancyB (st : State) : Bool :=
  Anchor.all.any (fun a => (st.piles a).isEmpty)

theorem hasVacancyB_eq_true {st : State} : hasVacancyB st = true ↔ HasVacancy st := by
  unfold hasVacancyB HasVacancy
  rw [List.any_eq_true]
  constructor
  · rintro ⟨a, ha, h⟩
    exact ⟨a, h⟩
  · rintro ⟨a, h⟩
    exact ⟨a, Anchor.mem_all a, h⟩

set_option maxHeartbeats 1200000 in
/-- Along a witness shuffle from a no-vacancy state to a vacancy state, the
first vacancy gain is a bare-king raise. -/
theorem first_vacancy_split {w u : State} {ρ : List Move}
    (hwf : w.WF) (h : ShufflePlayW w ρ u)
    (hne : NoVacancy w) (hve : HasVacancy u) :
    ∃ (pre : List Move) (x : Card) (a : Anchor) (s0 s1 : State) (suffix : List Move),
      NVWalk w pre s0 ∧
      State.step s0 (Move.tabToFound x) = some s1 ∧
      s0.pileOfTop x = some a ∧
      NoVacancy s0 ∧
      (s1.piles a).isEmpty = true ∧
      reversibleAtW s0 (Move.tabToFound x) ∧
      ShufflePlayW s1 suffix u := by
  induction h with
  | nil s =>
      obtain ⟨a, ha⟩ := hve
      exact absurd ha (hne a)
  | @cons st s1 W m ρ hrev hstep hrest ih =>
      by_cases hv1 : hasVacancyB s1 = true
      · have hv1' : HasVacancy s1 := hasVacancyB_eq_true.mp hv1
        have hne_false : ∀ a, (st.piles a).isEmpty = false :=
          fun a => bool_eq_false_of_not_true (hne a)
        rcases KingFuel.empty_gain_step_is_raise_or_slide hstep hne_false hv1' with
          ⟨x, a, hm, hp, hvac⟩ | ⟨x, b, hm⟩
        · refine ⟨[], x, a, st, s1, ρ, NVWalk.nil st, ?_, hp, hne, hvac, ?_, hrest⟩
          · rw [hm] at hstep
            exact hstep
          · rwa [hm] at hrev
        · exfalso
          rw [hm] at hstep
          have hrev' : reversibleAtW st (Move.tabToTab x b) := by
            rwa [hm] at hrev
          have hvno := no_vacancy_after_reversible_slide hwf hstep hrev' hne
          obtain ⟨a, ha⟩ := hv1'
          exact hvno a ha
      · have hv1' : ¬ HasVacancy s1 := fun h => hv1 (hasVacancyB_eq_true.mpr h)
        have hno1 : NoVacancy s1 := by
          rw [noVacancy_iff_not_hasVacancy]
          exact hv1'
        have hwf1 : s1.WF := step_wf hwf hstep
        obtain ⟨pre, x, a, s0, s1', suffix, hpre, hstep', hp, hno0, hvac,
          hrev_raise, hsuffix⟩ := ih hwf1 hno1 hve
        exact ⟨m :: pre, x, a, s0, s1', suffix,
          NVWalk.cons hrev hne hno1 hstep hpre,
          hstep', hp, hno0, hvac, hrev_raise, hsuffix⟩

#print axioms first_vacancy_split








/-- A bare-king raise creates no new bottomed card: every bottomed card after
the raise was already bottomed before it. -/
theorem kingBottomCard_raise_back {s0 s1 : State} {x : Card} {a : Anchor}
    (hwf0 : s0.WF) (hstep : State.step s0 (Move.tabToFound x) = some s1)
    (hp : s0.pileOfTop x = some a) (hvac : (s1.piles a).isEmpty = true)
    {c : Card} (hc1 : KingBottomCard s1 c) :
    KingBottomCard s0 c := by
  obtain ⟨ac, hkb1, hseat1⟩ := hc1
  obtain ⟨hn, a', hp', hv⟩ := step_tabToFound_inv hstep
  have haa : a' = a := by
    rw [hp] at hp'
    injection hp' with h
    exact h.symm
  rw [haa] at hv
  have hac_ne : ac ≠ a := by
    intro h
    rw [h] at hseat1
    have hmem : c ∈ (s1.piles a).faceUp :=
      pileHolding_mem (tfc_seatOf_of_inl hseat1).1
    rw [Pile.isEmpty_eq] at hvac
    rw [hvac.2] at hmem
    exact absurd hmem (by simp)
  have hpile : s1.piles ac = s0.piles ac := by
    rw [hv]
    dsimp only
    rw [if_neg hac_ne]
  have hwfs1 : s1.WF := step_wf hwf0 hstep
  have hkb0 : KingBottom s0 ac :=
    (kingBottom_congr_of_pile_eq hwf0 hwfs1 hpile).mpr hkb1
  have hhold1 : s1.pileHolding c = some ac := (tfc_seatOf_of_inl hseat1).1
  have hhold0 : s0.pileHolding c = some ac := by
    exact (pileHolding_eq_some_iff hwf0).mpr (by
      rw [← hpile]
      exact pileHolding_mem hhold1)
  have hseat0 : seatOf s0 c = some (Sum.inl ac) := by
    rw [tfc_seatOf_pair hhold0]
    rw [tfc_seatOf_pair hhold1] at hseat1
    rw [hpile] at hseat1
    exact hseat1
  exact ⟨ac, hkb0, hseat0⟩

/-- A card other than the raised king stays bottomed after a bare-king raise. -/
theorem kingBottomCard_raise_survivor {s0 s1 : State} {x : Card} {a : Anchor}
    (hwf0 : s0.WF) (hstep : State.step s0 (Move.tabToFound x) = some s1)
    (hp : s0.pileOfTop x = some a) (hvac : (s1.piles a).isEmpty = true)
    {c : Card} (hc0 : KingBottomCard s0 c) (hcx : c ≠ x) :
    KingBottomCard s1 c := by
  obtain ⟨ac, hkb0, hseat0⟩ := hc0
  obtain ⟨hn, a', hp', hv⟩ := step_tabToFound_inv hstep
  have haa : a' = a := by
    rw [hp] at hp'
    injection hp' with h
    exact h.symm
  rw [haa] at hv
  have hface_hid := (KingFuel.raise_empties_iff hstep hp).mp hvac
  have hseat_x : seatOf s0 x = some (Sum.inl a) := by
    have hhold : s0.pileHolding x = some a :=
      (pileHolding_eq_some_iff hwf0).mpr (by rw [hface_hid.1]; simp)
    have hbelow : below x (s0.piles a).faceUp = [] := by
      rw [hface_hid.1]; simp [below]
    exact tfc_seatOf_inl_intro hhold hbelow
  have hac_ne : ac ≠ a := by
    intro h
    apply hcx
    rw [h] at hseat0
    exact king_seat_injective hseat0 hseat_x
  have hpile : s1.piles ac = s0.piles ac := by
    rw [hv]
    dsimp only
    rw [if_neg hac_ne]
  have hwfs1 : s1.WF := step_wf hwf0 hstep
  have hkb1 : KingBottom s1 ac :=
    (kingBottom_congr_of_pile_eq hwf0 hwfs1 hpile).mp hkb0
  have hhold0 : s0.pileHolding c = some ac := (tfc_seatOf_of_inl hseat0).1
  have hhold1 : s1.pileHolding c = some ac := by
    exact (pileHolding_eq_some_iff hwfs1).mpr (by
      rw [hpile]
      exact pileHolding_mem hhold0)
  have hseat1 : seatOf s1 c = some (Sum.inl ac) := by
    rw [tfc_seatOf_pair hhold1]
    rw [tfc_seatOf_pair hhold0] at hseat0
    rw [hpile]
    exact hseat0
  exact ⟨ac, hkb1, hseat1⟩


/-- Forget the no-vacancy bookkeeping of an `NVWalk`. -/
theorem NVWalk.to_shuffle {w s0 : State} {ρ : List Move} (h : NVWalk w ρ s0) :
    ShufflePlayW w ρ s0 := by
  induction h with
  | nil s => exact Walk.nil s
  | @cons s s1 s' m ρ hrev hno_s hno_s1 hstep hrest ih =>
      exact Walk.cons hrev hstep ih

private theorem nodup_map_anchor {l : List Card} {f : Card → Anchor}
    (h : l.Nodup) (hinj : ∀ c ∈ l, ∀ c' ∈ l, f c = f c' → c = c') :
    (l.map f).Nodup := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons c cs ih =>
      rw [List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        rw [List.mem_map] at hmem
        obtain ⟨c', hc', hfc⟩ := hmem
        have hcc' : c = c' :=
          hinj c (List.mem_cons_self ..) c' (List.mem_cons_of_mem c hc') hfc.symm
        subst hcc'
        exact (List.nodup_cons.mp h).1 hc'
      · exact ih (List.nodup_cons.mp h).2
          (fun x hx x' hx' =>
            hinj x (List.mem_cons_of_mem c hx) x' (List.mem_cons_of_mem c hx'))

/-- The anchor of a bottomed king at `w` (default for non-bottomed cards). -/
def anchorOf (w : State) (c : Card) : Anchor :=
  match seatOf w c with
  | some (Sum.inl a) => a
  | _ => Anchor.p0

set_option maxHeartbeats 1600000 in
/-- The unconditional completeness half, via the conjugation route:
extend the desired assignment to a VK permutation, realize it by a KingShuffle
at the first-vacancy state, and relabel the reverse path. -/
theorem kingAssignmentComplete_of_sameOrbitVacant {st : State} (hwf : st.WF)
    (hvac : SameOrbitVacant st) : KingAssignmentComplete st := by
  intro w hw τ hτ
  by_cases hvacw : hasVacancyB w = true
  · have hvacw' : HasVacancy w := hasVacancyB_eq_true.mp hvacw
    obtain ⟨w', hst_w', hseat⟩ :=
      king_assignment_sameOrbit_of_vacancy hwf hw hvacw' hτ
    refine ⟨w', ?_, hseat⟩
    exact sameOrbitSetoid.iseqv.trans (sameOrbitSetoid.iseqv.symm hw) hst_w'
  · have hvacw' : ¬ HasVacancy w := fun h => hvacw (hasVacancyB_eq_true.mpr h)
    have hno_w : NoVacancy w := (noVacancy_iff_not_hasVacancy w).mpr hvacw'
    obtain ⟨u, hst_u, hvac_u⟩ := hvac
    have hw_keep : sameOrbitSetoid.r st w := hw
    have hst_u_keep : sameOrbitSetoid.r st u := hst_u
    -- the forward path w -> u
    obtain ⟨ρw, hw_st, σw, hst_w⟩ := hw
    obtain ⟨ρu, hu_st, σu, hst_u'⟩ := hst_u
    have hwfw : w.WF := run_wf hwf
      (Walk_run (P := fun st m => reversibleAtW st m) (st := st) (W := w) hst_w)
    have hforward : ShufflePlayW w (ρw ++ σu) u :=
      ShufflePlayW_append hw_st hst_u'
    obtain ⟨pre, x, a, s0, s1, suffix, hpre, hstep, hp, hno0, hvac_s1, hrev_raise, hsuffix⟩ :=
      first_vacancy_split hwfw hforward hno_w hvac_u
    -- the forward and reverse paths from w to s1
    have hpre_sh : ShufflePlayW w pre s0 := hpre.to_shuffle
    have hraise_sh : ShufflePlayW s0 [Move.tabToFound x] s1 :=
      Walk.cons hrev_raise hstep (Walk.nil s1)
    have hfwd_s1 : ShufflePlayW w (pre ++ [Move.tabToFound x]) s1 :=
      ShufflePlayW_append hpre_sh hraise_sh
    have hu_w : RevEqW u w :=
      RevEqW_trans hst_u_keep (RevEqW_symm hw_keep)
    obtain ⟨ρuw, hu_w_sh, σuw, hw_u_sh⟩ := hu_w
    have hrev_s1 : ShufflePlayW s1 (suffix ++ ρuw) w :=
      ShufflePlayW_append hsuffix hu_w_sh
    have hclass_s1 : sameOrbitSetoid.r w s1 :=
      ⟨suffix ++ ρuw, hrev_s1, pre ++ [Move.tabToFound x], hfwd_s1⟩
    have hwfs1 : s1.WF := run_wf hwfw
      (Walk_run (P := fun st m => reversibleAtW st m) (st := w) (W := s1) hfwd_s1)
    have huniq_s1 : ∀ a' b, (s1.piles a').isEmpty = true →
        (s1.piles b).isEmpty = true → a' = b := by
      obtain ⟨hn, a0, hp0, hv⟩ := step_tabToFound_inv hstep
      have ha0 : a0 = a := by
        rw [hp] at hp0
        injection hp0 with h
        exact h.symm
      rw [ha0] at hv
      intro a' b ha' hb
      by_cases hba : b = a
      · rw [hba] at hb
        by_cases ha'a : a' = a
        · exact ha'a.trans hba.symm
        · exfalso
          have hs1a' : s1.piles a' = s0.piles a' := by
            rw [hv]
            dsimp only
            rw [if_neg ha'a]
          rw [hs1a'] at ha'
          exact hno0 a' ha'
      · exfalso
        have hs1b : s1.piles b = s0.piles b := by
          rw [hv]
          dsimp only
          rw [if_neg hba]
        rw [hs1b] at hb
        exact hno0 b hb
    -- the finite pairs and the extended VK permutation
    let cs : List Card := kingsOf w
    let pairs : List (Anchor × Anchor) := cs.map (fun c => (anchorOf w c, τ c))
    have hcs_mem : ∀ c, c ∈ cs ↔ KingBottomCard w c := fun c => mem_kingsOf hwfw
    have hcs_nodup : cs.Nodup := kingsOf_nodup w
    have hanchor_of : ∀ c ∈ cs, ∃ a, seatOf w c = some (Sum.inl a) ∧ anchorOf w c = a := by
      intro c hc
      obtain ⟨a, hkb, hse⟩ := (hcs_mem c).mp hc
      exact ⟨a, hse, by simp [anchorOf, hse]⟩
    have hdom_nodup : (pairs.map Prod.fst).Nodup := by
      have hmap : pairs.map Prod.fst = cs.map (anchorOf w) := by
        simp [pairs, List.map_map, Function.comp_def]
      rw [hmap]
      refine nodup_map_anchor hcs_nodup ?_
      intro c hc c' hc' heq
      obtain ⟨a, hse, ha⟩ := hanchor_of c hc
      obtain ⟨a', hse', ha'⟩ := hanchor_of c' hc'
      have haa : a = a' := by rw [← ha, ← ha']; exact heq
      have hse'' : seatOf w c' = some (Sum.inl a) := by rwa [← haa] at hse'
      exact king_seat_injective hse hse''
    have hcod_nodup : (pairs.map Prod.snd).Nodup := by
      have hmap : pairs.map Prod.snd = cs.map τ := by
        simp [pairs, List.map_map, Function.comp_def]
      rw [hmap]
      refine nodup_map_anchor hcs_nodup ?_
      intro c hc c' hc' heq
      exact hτ.2 c c' ((hcs_mem c).mp hc) ((hcs_mem c').mp hc') heq
    have hdom_VK : ∀ p ∈ pairs, VKSet w p.1 := by
      intro p hp
      rw [List.mem_map] at hp
      obtain ⟨c, hc, rfl⟩ := hp
      obtain ⟨a, hkb, hse⟩ := (hcs_mem c).mp hc
      have ha : anchorOf w c = a := by simp [anchorOf, hse]
      rw [ha]
      exact Or.inr hkb
    have hcod_VK : ∀ p ∈ pairs, VKSet w p.2 := by
      intro p hp
      rw [List.mem_map] at hp
      obtain ⟨c, hc, rfl⟩ := hp
      exact hτ.1 c ((hcs_mem c).mp hc)
    obtain ⟨σ, hσ_pair, hσVK, hσfix⟩ :=
      exists_perm_extending_pairs pairs hdom_nodup hcod_nodup hdom_VK hcod_VK
    have hvk_w_s1 : ∀ j, VKSet w j ↔ VKSet s1 j :=
      vk_sameOrbit_invariant hwfw hclass_s1
    have hσVK_s1 : ∀ j, VKSet s1 j ↔ VKSet s1 (σ.toFun j) := by
      intro j
      exact (hvk_w_s1 j).symm.trans ((hσVK j).trans (hvk_w_s1 (σ.toFun j)))
    have hσfix_s1 : ∀ j, ¬ VKSet s1 j → σ.toFun j = j := by
      intro j hnot
      apply hσfix j
      intro hwj
      exact hnot ((hvk_w_s1 j).mp hwj)
    obtain ⟨v_s, hks, hv_s⟩ :=
      KingShuffle.realize_perm hwfs1 ⟨a, hvac_s1⟩ huniq_s1 σ hσVK_s1 hσfix_s1
    have hw_s1 : sameOrbitSetoid.r w s1 := hclass_s1
    have h_s1_vs : sameOrbitSetoid.r s1 v_s :=
      bareCargo_sameOrbit (king_shuffle_closure hwfs1 hks)
    have h_vs_perm : sameOrbitSetoid.r v_s (w.permute σ) := by
      have h3 : sameOrbitSetoid.r (s1.permute σ) (w.permute σ) :=
        sameOrbitSetoid.iseqv.symm (sameOrbit_permute (σ := σ) hclass_s1 hwfw)
      rwa [← hv_s] at h3
    have hw_w' : sameOrbitSetoid.r w (w.permute σ) :=
      sameOrbitSetoid.iseqv.trans hw_s1
        (sameOrbitSetoid.iseqv.trans h_s1_vs h_vs_perm)
    have hseat_w' : ∀ c, KingBottomCard w c →
        seatOf (w.permute σ) c = some (Sum.inl (τ c)) := by
      intro c hc
      have hc_cs : c ∈ cs := (hcs_mem c).mpr hc
      obtain ⟨anc, hkb, hse⟩ := hc
      have ha : anchorOf w c = anc := by simp [anchorOf, hse]
      have hpair : (anc, τ c) ∈ pairs := by
        rw [List.mem_map]
        refine ⟨c, hc_cs, ?_⟩
        simp [pairs, ha]
      have hσa : σ.toFun anc = τ c := by
        have := hσ_pair (anc, τ c) hpair
        simpa [ha] using this
      rw [State.seatOf_permute hwfw c, hse]
      simp [Base.permute, hσa]
    refine ⟨w.permute σ, ?_, hseat_w'⟩
    exact hw_w'

#print axioms kingAssignmentComplete_of_sameOrbitVacant




/-- **`kingOrbitDichotomy`** — the unconditional dichotomy: a class with a
vacancy has complete king assignment, and a vacancy-free class has fixed king
assignment. -/
theorem kingOrbitDichotomy {st : State} (hwf : st.WF) : KingOrbitDichotomy st :=
  ⟨kingAssignmentComplete_of_sameOrbitVacant hwf,
   kingAssignmentFixed_of_not_vacant hwf⟩

#print axioms kingOrbitDichotomy

