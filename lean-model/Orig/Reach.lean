import Orig.Combine
import Orig.Integrity

/-!
# Orig.Reach — the reachability spine and the reachable⇒WF fence

The reachability spine of the original game, ported from the old
model's `Klondike.Restriction` to the new `Orig` state: cards live
in the piles directly, the deal enters only through `State.initial`,
and `WF`'s draw-step clause has the new shape (`drawStep` is 1 or 3,
not merely positive).

* `initialReachable` — the deposit: a position reached from a dealt
  initial state by some play, where the deal deals every card once
  and the draw step is one of the two physical choices.
* `initialReachableR` — the recurrence: the dealt initial states,
  closed under one legal move.  The induction form every fence
  proof consumes; `initialReachableR_iff` hands any deposit to it.
* `step_wf` / `initial_wf` — the conservation fence itself: all six
  move kinds preserve `State.WF`, and a `Deal.WF` deal starts `WF`.
* `initialReachable_wf` — the combinator over both: nothing
  reachable from a dealt game ever loses a card, breaks a run, or
  corrupts the draw step.  The projections the downstream chapter
  wants (`initialReachable_runOK`, `initialReachable_cardCount`,
  `initialReachable_drawStep`) are exported alongside.

Self-contained: only `Orig.*` is imported; every list, count, last,
chop, and pile lemma needed is a private copy (farm isolation
convention, deduped at merge).  Axiom discipline:
`[propext, Quot.sound]`, no `Classical.choice` anywhere.
-/

/-! ## The deposit and the recurrence -/

/-- Reachable from a dealt game: some play from `State.initial d s`
lands exactly here, where `d` deals every card once and the draw
step is one of the two physical choices. -/
def initialReachable (st : State) : Prop :=
  ∃ (d : State.Deal) (s : Nat) (play : List Move),
    d.WF ∧ 0 < s ∧ (State.initial d s).run play = some st

/-- Reachability by recurrence: the dealt initial states, closed
under one legal move.  No move ever rewrites the deal or the draw
step, so the closure never leaves the dealt game it started in. -/
inductive initialReachableR : State → Prop
  /-- A dealt game's start. -/
  | initial (d : State.Deal) (s : Nat) (hd : d.WF) (hs : 0 < s) :
      initialReachableR (State.initial d s)
  /-- One legal move preserves reachability. -/
  | step (st : State) (m : Move) (st' : State)
      (h : State.step st m = some st') (hprev : initialReachableR st) :
      initialReachableR st'

/-- The recurrence presents every deposit: replay the play
backward, step by step, from its end. -/
theorem initialReachableR_of_run : ∀ (play : List Move) (st₀ st : State),
    st₀.run play = some st → initialReachableR st₀ → initialReachableR st := by
  intro play
  induction play with
  | nil =>
      intro st₀ st h hprev
      have he : st₀ = st := Option.some.inj h
      subst he
      exact hprev
  | cons m ms ih =>
      intro st₀ st h hprev
      obtain ⟨s₁, hm, hrest⟩ := State.run_cons h
      exact ih s₁ st hrest (initialReachableR.step st₀ m s₁ hm hprev)

/-- The recurrence has every deposit: exhibit the play, one
constructor per move, by induction on the derivation. -/
theorem initialReachable_of_initialReachableR {st : State}
    (h : initialReachableR st) : initialReachable st := by
  induction h with
  | initial d s hdw hs => exact ⟨d, s, [], hdw, hs, rfl⟩
  | step s₀ m s₁ hstep hprev ih =>
      obtain ⟨d, s, play, hdw, hs, hrun⟩ := ih
      refine ⟨d, s, play ++ [m], hdw, hs, ?_⟩
      have h1 : s₀.run [m] = some s₁ := by
        show (match State.step s₀ m with
          | some t => t.run []
          | none => none) = some s₁
        rw [hstep]
        rfl
      exact run_split play (State.initial d s) s₀ [m] s₁ hrun h1

/-- **The iff** — the recurrence presentation and the deposit
presentation carry the same states. -/
theorem initialReachableR_iff {st : State} :
    initialReachableR st ↔ initialReachable st :=
  ⟨initialReachable_of_initialReachableR,
   fun ⟨d, s, play, hdw, hs, hrun⟩ =>
     initialReachableR_of_run play (State.initial d s) st hrun
       (initialReachableR.initial d s hdw hs)⟩

/-- **The generic combinator** (the recurrence's `rec`,
packaged): to prove `I` of every dealt-reachable state, show `I` at
every dealt initial state and that one legal move preserves it.
The invariant-preservation form every future fence proof over the
reachable fragment takes. -/
theorem invariant_of_initialReachableR {I : State → Prop}
    (hinit : ∀ (d : State.Deal) (s : Nat), d.WF → 0 < s →
      I (State.initial d s))
    (hstep : ∀ (st st' : State) (m : Move), State.step st m = some st' →
      I st → I st') :
    ∀ st, initialReachableR st → I st := by
  intro st h
  induction h with
  | initial d s hdw hs => exact hinit d s hdw hs
  | step st m st' hs _ ih => exact hstep st st' m hs ih

/-- The combinator, deposit form: the reachability side of the iff
absorbed, so a fence proof reads directly off `initialReachable`. -/
theorem invariant_of_initialReachable {I : State → Prop}
    (hinit : ∀ (d : State.Deal) (s : Nat), d.WF → 0 < s →
      I (State.initial d s))
    (hstep : ∀ (st st' : State) (m : Move), State.step st m = some st' →
      I st → I st') :
    ∀ st, initialReachable st → I st := fun st hr =>
  invariant_of_initialReachableR hinit hstep st (initialReachableR_iff.mpr hr)

/-! ## Private kit: occurrence counts

A private recursive copy of the filter length `cardCount` is built
on, with the additive laws each move's conservation check needs,
plus the zone decomposition that turns `cardCount` into a sum over
the foundations, the piles, the stock, and the waste. -/

/-- The occurrence count of one card in a list. -/
private def cnt (c : Card) : List Card → Nat
  | [] => 0
  | x :: t => (if x = c then 1 else 0) + cnt c t

private theorem cnt_nil (c : Card) : cnt c [] = 0 := rfl

/-- The definitional cons law of `cnt`, in sum form. -/
private theorem cnt_def (c x : Card) (t : List Card) :
    cnt c (x :: t) = (if x = c then 1 else 0) + cnt c t := rfl

private theorem cnt_singleton (c x : Card) : cnt c [x] = if x = c then 1 else 0 := by
  show ((if x = c then 1 else 0) + cnt c []) = if x = c then 1 else 0
  rw [cnt_nil]
  omega

private theorem cnt_app (c : Card) : ∀ (l₁ l₂ : List Card),
    cnt c (l₁ ++ l₂) = cnt c l₁ + cnt c l₂ := by
  intro l₁ l₂
  induction l₁ with
  | nil => rw [List.nil_append, cnt_nil]; omega
  | cons x t ih =>
      show (if x = c then 1 else 0) + cnt c (t ++ l₂) = _
      rw [ih, cnt_def]
      omega

private theorem cnt_snoc (c x : Card) (l : List Card) :
    cnt c (l ++ [x]) = cnt c l + cnt c [x] := cnt_app c l [x]

private theorem cnt_reverse (c : Card) (l : List Card) :
    cnt c l.reverse = cnt c l := by
  induction l with
  | nil => rfl
  | cons x t ih =>
      rw [List.reverse_cons, cnt_snoc, cnt_singleton, ih, cnt_def]
      omega

private theorem mem_le_cnt {c : Card} : ∀ (l : List Card), c ∈ l → 1 ≤ cnt c l := by
  intro l
  induction l with
  | nil => intro h; exact absurd h List.not_mem_nil
  | cons x t ih =>
      intro h
      show 1 ≤ (if x = c then 1 else 0) + cnt c t
      rcases List.mem_cons.mp h with h' | h'
      · rw [ite_eq_left h'.symm]
        omega
      · have h1 : 1 ≤ cnt c t := ih h'
        by_cases hx : x = c
        · rw [ite_eq_left hx]; omega
        · rw [ite_eq_right hx]; omega

/-- A count of zero witnesses non-membership. -/
private theorem not_mem_of_cnt_zero {c : Card} {l : List Card}
    (h : cnt c l = 0) : c ∉ l := by
  intro hmem
  have := mem_le_cnt l hmem
  omega

/-- `cnt` is exactly the filter length `cardCount` is defined by. -/
private theorem cnt_filter (c : Card) (l : List Card) :
    cnt c l = (l.filter fun x => decide (x = c)).length := by
  induction l with
  | nil => rfl
  | cons x t ih =>
      show ((if x = c then 1 else 0) + cnt c t) = _
      rw [List.filter_cons]
      by_cases hxc : x = c
      · rw [decide_eq_true hxc, ite_eq_left rfl, List.length_cons, ite_eq_left hxc, ih]
        omega
      · have hdec : (decide (x = c)) = false := by simp [hxc]
        rw [hdec, ite_eq_right (fun h => Bool.noConfusion h),
          ite_eq_right hxc, ih]
        omega

/-- `cardCount` at a state is the `cnt` of its flattened zones. -/
private theorem cardCount_eq_cnt (st : State) (c : Card) :
    st.cardCount c = cnt c (st.zones.flatMap id) :=
  (cnt_filter c (st.zones.flatMap id)).symm

/-- The count of a card across a list of zone lists. -/
private def cntFlat (c : Card) : List (List Card) → Nat
  | [] => 0
  | z :: zs => cnt c z + cntFlat c zs

private theorem cntFlat_cons (c : Card) (z : List Card) (zs : List (List Card)) :
    cntFlat c (z :: zs) = cnt c z + cntFlat c zs := rfl

private theorem cntFlat_flatMap (c : Card) (zs : List (List Card)) :
    cntFlat c zs = cnt c (zs.flatMap id) := by
  induction zs with
  | nil => rfl
  | cons z t ih =>
      rw [cntFlat_cons, List.flatMap_cons, cnt_app, ih]
      rfl

/-- Count sums over mapped families only depend on per-index counts. -/
private theorem cntFlat_map_congr (c : Card) : ∀ {α : Type} (F G : α → List Card)
    (as : List α), (∀ j ∈ as, cnt c (F j) = cnt c (G j)) →
    cntFlat c (as.map F) = cntFlat c (as.map G) := by
  intro α F G as
  induction as with
  | nil => intro _; rfl
  | cons x t ih =>
      intro h
      simp only [List.map_cons, cntFlat_cons]
      rw [h x List.mem_cons_self, ih (fun j hj => h j (List.mem_cons_of_mem _ hj))]

private theorem cntFlat_map_nil {α : Type} : ∀ (as : List α) (F : α → List Card) (c : Card),
    (∀ j, F j = []) → cntFlat c (as.map F) = 0 := by
  intro as F c hF
  induction as with
  | nil => rfl
  | cons x t ih =>
      show cnt c (F x) + cntFlat c (List.map F t) = 0
      rw [hF x, cnt_nil, ih]

/-- The delta form: per-index count differences, summed by `δ`. -/
private theorem cntFlat_map_delta (c : Card) : ∀ {α : Type} (F G : α → List Card)
    (as : List α) (δ : α → Nat), (∀ j ∈ as, cnt c (F j) + δ j = cnt c (G j)) →
    cntFlat c (as.map F) + (as.map δ).sum = cntFlat c (as.map G) := by
  intro α F G as
  induction as with
  | nil => intro δ _; rfl
  | cons x t ih =>
      intro δ h
      simp only [List.map_cons, cntFlat_cons, List.sum_cons]
      have hx : cnt c (F x) + δ x = cnt c (G x) := h x List.mem_cons_self
      have hr := ih δ (fun j hj => h j (List.mem_cons_of_mem _ hj))
      omega

private theorem sum_map_zero {α : Type} : ∀ (L : List α) (δ : α → Nat),
    (∀ j ∈ L, δ j = 0) → (L.map δ).sum = 0 := by
  intro L δ
  induction L with
  | nil => intro _; rfl
  | cons x t ih =>
      intro h
      rw [List.map_cons, List.sum_cons, h x List.mem_cons_self]
      have := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
      omega

/-- On a duplicate-free index list, a delta sum concentrated at one
index collapses to the value there. -/
private theorem sum_map_single {α : Type} [DecidableEq α] :
    ∀ (L : List α) (δ : α → Nat) (a : α), L.Nodup → a ∈ L →
    (∀ j ∈ L, j ≠ a → δ j = 0) → (L.map δ).sum = δ a := by
  intro L
  induction L with
  | nil => intro δ a _ hmem _; exact absurd hmem List.not_mem_nil
  | cons x t ih =>
      intro δ a hnd hmem hzero
      obtain ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
      rcases Decidable.em (x = a) with hxa | hxa
      · have hxa' : a = x := hxa.symm
        subst hxa'
        have hz : (List.map δ t).sum = 0 :=
          sum_map_zero t δ
            (fun j hj => hzero j (List.mem_cons_of_mem _ hj)
              (fun hje => hx (hje ▸ hj)))
        rw [List.map_cons, List.sum_cons]
        omega
      · rw [List.map_cons, List.sum_cons, hzero x List.mem_cons_self hxa]
        rcases List.mem_cons.mp hmem with hmem' | hmem'
        · exact absurd hmem'.symm hxa
        · have := ih δ a hnd' hmem'
            (fun j hj hne2 => hzero j (List.mem_cons_of_mem _ hj) hne2)
          omega

private theorem flatMap_id_append : ∀ (A B : List (List Card)),
    (A ++ B).flatMap id = (A.flatMap id) ++ (B.flatMap id) := by
  intro A B
  induction A with
  | nil => rfl
  | cons z t ih =>
      show (z ++ ((t ++ B).flatMap id)) = (z ++ (t.flatMap id)) ++ (B.flatMap id)
      rw [show (t ++ B).flatMap id = (t.flatMap id) ++ (B.flatMap id) from ih]
      exact (List.append_assoc z (t.flatMap id) (B.flatMap id)).symm

/-- The zone sums decompose `cardCount` into foundations, piles,
stock, and waste — the transfer form every move's conservation
check plugs into. -/
private theorem cardCount_zones (st : State) (c : Card) :
    st.cardCount c =
      cntFlat c (Suit.all.map st.found)
      + cntFlat c (Anchor.all.map fun a => (st.piles a).hidden ++ (st.piles a).faceUp)
      + (cnt c st.stock + cnt c st.waste) := by
  rw [cardCount_eq_cnt]
  have h1 : ([st.waste] : List (List Card)).flatMap id = st.waste :=
    List.append_nil st.waste
  have h2 : ([st.stock, st.waste] : List (List Card)).flatMap id = st.stock ++ st.waste :=
    congrArg (st.stock ++ ·) h1
  show cnt c ((Suit.all.map st.found ++ (Anchor.all.map
      (fun a => (st.piles a).hidden ++ (st.piles a).faceUp) ++ [st.stock, st.waste])).flatMap id) = _
  rw [flatMap_id_append, flatMap_id_append, h2, cnt_app, cnt_app, cnt_app,
    cntFlat_flatMap, cntFlat_flatMap]
  omega

/-- The central conservation bridge: if the four zone sums agree
card by card, the two states' `cardCount`s agree. -/
private theorem cardCount_congr (c : Card) (st st' : State)
    (h : cntFlat c (Suit.all.map st.found)
        + cntFlat c (Anchor.all.map fun a => (st.piles a).hidden ++ (st.piles a).faceUp)
        + (cnt c st.stock + cnt c st.waste)
      = cntFlat c (Suit.all.map st'.found)
        + cntFlat c (Anchor.all.map fun a => (st'.piles a).hidden ++ (st'.piles a).faceUp)
        + (cnt c st'.stock + cnt c st'.waste)) :
    st.cardCount c = st'.cardCount c := by
  rw [cardCount_zones, cardCount_zones]
  exact h

/-! ## Private kit: lists at the ends

The `lastOf` / `chop` / `below` snoc kit, in the direct form the
count transfers and pile-top reasoning here consume.  The
`∃ front`-shaped companions live in `Orig.Integrity`
(`Pile.top_eq_lastOf_iff`); these are the count-level refinements
with `front = chop l`. -/

private theorem lastOf_snoc' : ∀ (front : List Card) (c : Card),
    lastOf (front ++ [c]) = some c := by
  intro front
  induction front with
  | nil => intro _; rfl
  | cons x t ih =>
      intro c
      cases t with
      | nil => rfl
      | cons y t' => exact ih c


private theorem lastOf_mem' : ∀ (l : List Card) {c : Card},
    lastOf l = some c → c ∈ l
  | [], _, h => absurd h (by simp [lastOf])
  | [y], c, h => by
      have h' : y = c := Option.some.inj h
      subst h'
      exact List.mem_cons_self ..
  | x :: y :: t, c, h =>
      List.mem_cons.mpr (Or.inr (lastOf_mem' (y :: t) h))

/-- Every nonempty list has a last. -/
private theorem lastOf_ne_nil : ∀ (l : List Card), l ≠ [] → ∃ x, lastOf l = some x
  | [], h => absurd rfl h
  | [y], _ => ⟨y, rfl⟩
  | x :: y :: t, _ => by
      obtain ⟨w, hw⟩ := lastOf_ne_nil (y :: t) (by cases t <;> simp)
      exact ⟨w, hw⟩

private theorem below_cons (c x : Card) (t : List Card) :
    below c (x :: t) = if x = c then [] else x :: below c t := rfl

private theorem fromCard_cons (c x : Card) (t : List Card) :
    fromCard c (x :: t) = if x = c then x :: t else fromCard c t := rfl

private theorem below_fromCard (c : Card) : ∀ (l : List Card),
    below c l ++ fromCard c l = l := by
  intro l
  induction l with
  | nil => rfl
  | cons x t ih =>
      rw [below_cons, fromCard_cons]
      by_cases hxc : x = c
      · rw [ite_eq_left hxc, ite_eq_left hxc]; rfl
      · rw [ite_eq_right hxc, ite_eq_right hxc, List.cons_append, ih]

private theorem mem_below {c x : Card} : ∀ (l : List Card), x ∈ below c l → x ∈ l := by
  intro l
  induction l with
  | nil => intro h; exact absurd h List.not_mem_nil
  | cons y t ih =>
      intro h
      rw [below_cons] at h
      by_cases hyc : y = c
      · rw [ite_eq_left hyc] at h; exact absurd h List.not_mem_nil
      · rw [ite_eq_right hyc] at h
        rcases List.mem_cons.mp h with h' | h'
        · exact List.mem_cons.mpr (Or.inl h')
        · exact List.mem_cons.mpr (Or.inr (ih h'))

private theorem mem_fromCard {c x : Card} : ∀ (l : List Card), x ∈ fromCard c l → x ∈ l := by
  intro l
  induction l with
  | nil => intro h; exact absurd h List.not_mem_nil
  | cons y t ih =>
      intro h
      rw [fromCard_cons] at h
      by_cases hyc : y = c
      · rw [ite_eq_left hyc] at h
        rcases List.mem_cons.mp h with h' | h'
        · exact List.mem_cons.mpr (Or.inl h')
        · exact List.mem_cons.mpr (Or.inr h')
      · rw [ite_eq_right hyc] at h
        exact List.mem_cons.mpr (Or.inr (ih h))

/-- The run `fromCard c l` is nonempty and headed by `c` whenever
`c` truly occurs in `l`. -/
private theorem fromCard_cons_head {c : Card} : ∀ (l : List Card), c ∈ l →
    ∃ r, fromCard c l = c :: r := by
  intro l
  induction l with
  | nil => intro h; exact absurd h List.not_mem_nil
  | cons x t ih =>
      intro h
      by_cases hxc : x = c
      · exact ⟨t, by rw [fromCard_cons, ite_eq_left hxc, hxc]⟩
      · obtain ⟨r, hr⟩ := ih (List.mem_cons.mp h |>.resolve_left (fun h' => hxc h'.symm))
        exact ⟨r, by rw [fromCard_cons, ite_eq_right hxc, hr]⟩

/-! ## Private kit: take and foundation prefixes -/

private theorem take_nil (n : Nat) : ([] : List Card).take n = [] := by
  cases n <;> rfl

private theorem take_ge : ∀ (l : List Card) {k : Nat}, l.length ≤ k → l.take k = l := by
  intro l
  induction l with
  | nil => intro k _; exact take_nil k
  | cons x t ih =>
      intro k hk
      cases k with
      | zero =>
          rw [List.length_cons] at hk
          exact absurd hk (by omega)
      | succ k' =>
          rw [List.length_cons] at hk
          show x :: t.take k' = x :: t
          rw [ih (by omega : t.length ≤ k')]

private theorem chop_eq_take : ∀ (l : List Card), chop l = l.take (l.length - 1)
  | [] => rfl
  | [x] => rfl
  | x :: y :: t => by
      have ih := chop_eq_take (y :: t)
      have hA : (y :: t).length = t.length + 1 := List.length_cons
      have hlen : (x :: y :: t).length - 1 = (y :: t).length - 1 + 1 := by
        rw [List.length_cons]
        omega
      rw [hlen]
      show x :: chop (y :: t) = x :: (y :: t).take ((y :: t).length - 1)
      rw [ih]

/-- Dealt pile cards reconstruct: `chop` is the take-the-front part
of a dealt hand. -/
private theorem chop_take_succ (L : List Card) (m : Nat) (h : m + 1 ≤ L.length) :
    chop (L.take (m + 1)) = L.take m := by
  rw [chop_eq_take, List.length_take, Nat.min_eq_left h, List.take_take,
    Nat.min_eq_left (by omega : m + 1 - 1 ≤ m + 1)]
  rfl

private theorem take_succ_snoc_some : ∀ (l : List Card) (m : Nat) (x : Card),
    l[m]? = some x → l.take (m + 1) = l.take m ++ [x]
  | [], 0, x, h => by simp at h
  | [], m + 1, x, h => by simp at h
  | y :: t, 0, x, h => by
      have hxy : x = y := (Option.some.inj h).symm
      subst hxy
      rfl
  | y :: t, m + 1, x, h => by
      rw [List.getElem?_cons_succ] at h
      have ih := take_succ_snoc_some t m x h
      show y :: t.take (m + 1) = (y :: t.take m) ++ [x]
      rw [List.cons_append, ih]

/-- The thirteen-way position pin: each rank sits at its own index
of `Rank.all`. -/
private theorem rank_all_pin (r : Rank) :
    (Rank.all : List Rank)[r.toIdx]? = some r := by
  cases r <;> rfl

/-- The build-order take-step: extending a foundation built to
`c`'s rank index takes exactly one more card — `c` itself. -/
private theorem upCards_take_succ {c : Card} :
    c.suit.upCards.take (c.rank.toIdx + 1) = c.suit.upCards.take c.rank.toIdx ++ [c] := by
  have h1 : (Rank.all : List Rank)[c.rank.toIdx]? = some c.rank := rank_all_pin c.rank
  have h2 : (c.suit.upCards)[c.rank.toIdx]? = some c := by
    rw [show c.suit.upCards = Rank.all.map (Card.mk c.suit) from rfl, List.getElem?_map, h1]
    rfl
  exact take_succ_snoc_some _ _ _ h2

/-- A taken prefix records its length: pins the foundation index
from the `nextUp` guard. -/
private theorem take_len_pin (σ : Suit) (n : Nat) :
    (σ.upCards.take n).length = min n 13 := by
  rw [List.length_take, Suit.upCards_length]

/-! ## Private kit: the runOK closures -/

private theorem runOK_two_true {x y : Card} {t : List Card}
    (h : runOK (x :: y :: t) = true) :
    canSitOn y x = true ∧ runOK (y :: t) = true := by
  rw [show runOK (x :: y :: t) = (canSitOn y x && runOK (y :: t)) from rfl,
    Bool.and_eq_true] at h
  exact h


/-- Everything strictly below a member of a legal run is a legal
run (the `below` half of the pile this card contributes). -/
private theorem runOK_below : ∀ (l : List Card) (c : Card),
    runOK l = true → runOK (below c l) = true
  | [], _, _ => rfl
  | [x], c, _ => by
      rw [below_cons]
      by_cases hxc : x = c
      · rw [ite_eq_left hxc]; rfl
      · rw [ite_eq_right hxc]; rfl
  | x :: y :: t, c, h => by
      obtain ⟨h1, h2⟩ := runOK_two_true h
      have ih := runOK_below (y :: t) c h2
      rw [below_cons]
      by_cases hxc : x = c
      · rw [ite_eq_left hxc]; rfl
      · rw [ite_eq_right hxc]
        rw [below_cons]
        by_cases hyc : y = c
        · rw [ite_eq_left hyc]; rfl
        · rw [ite_eq_right hyc]
          have hc : below c (y :: t) = y :: below c t := by
            rw [below_cons, ite_eq_right hyc]
          have ih' : runOK (y :: below c t) = true := by
            rw [← hc]; exact ih
          show (canSitOn y x && runOK (y :: below c t)) = true
          rw [ih', h1]
          rfl

/-- The run `fromCard c l` of a legal run is legal: it is a suffix
one, and legality is pairwise. -/
private theorem runOK_fromCard : ∀ (l : List Card) (c : Card),
    runOK l = true → runOK (fromCard c l) = true
  | [], _, _ => rfl
  | [x], c, _ => by
      rw [fromCard_cons]
      by_cases hxc : x = c
      · rw [ite_eq_left hxc]; rfl
      · rw [ite_eq_right hxc]; rfl
  | x :: y :: t, c, h => by
      obtain ⟨h1, h2⟩ := runOK_two_true h
      rw [fromCard_cons]
      by_cases hxc : x = c
      · rw [ite_eq_left hxc]; exact h
      · rw [ite_eq_right hxc]
        exact runOK_fromCard (y :: t) c h2

/-- A fitted append: a legal run extended at the top by a run whose
head fits under the old last card stays legal. -/
private theorem runOK_append_fit : ∀ (l : List Card) (c z : Card) (r : List Card),
    runOK l = true → runOK (c :: r) = true → lastOf l = some z →
    canSitOn c z = true → runOK (l ++ c :: r) = true
  | [], _, _, _, _, _, hlast, _ => absurd hlast (by simp [lastOf])
  | [y], c, z, r, h, hc, hlast, hfit => by
      show (canSitOn c y && runOK (c :: r)) = true
      rw [show y = z from Option.some.inj hlast, hfit, hc]
      rfl
  | x :: y :: t, c, z, r, h, hc, hlast, hfit => by
      obtain ⟨h1, h2⟩ := runOK_two_true h
      show (canSitOn y x && runOK ((y :: t) ++ c :: r)) = true
      rw [h1]
      exact runOK_append_fit (y :: t) c z r h2 hc
        (show lastOf (y :: t) = some z from hlast) hfit

/-! ## Private kit: state projections and guard unpackings -/

private theorem setFound_found_self {st : State} {s : Suit} {l : List Card} :
    (st.setFound s l).found s = l :=
  show (if s = s then l else st.found s) = l from ite_eq_left rfl

private theorem setFound_found_ne {st : State} {s s' : Suit} {l : List Card}
    (h : s' ≠ s) :
    (st.setFound s l).found s' = st.found s' :=
  show (if s' = s then l else st.found s') = _ from ite_eq_right h

/-- The searches only read the piles, so a foundation update leaves
them unchanged. -/
private theorem pileOfTop_setFound {st : State} {s : Suit} {l : List Card} {z : Card} :
    (st.setFound s l).pileOfTop z = st.pileOfTop z := rfl

private theorem canPlace_inl {st : State} {c : Card} {a : Anchor}
    (h : st.canPlace c (Sum.inl a) = true) :
    (st.piles a).isEmpty = true ∧ c.rank = Rank.king := by
  rw [show st.canPlace c (Sum.inl a) =
      ((st.piles a).isEmpty && decide (c.rank = Rank.king)) from rfl,
    Bool.and_eq_true] at h
  exact ⟨h.1, of_decide_eq_true h.2⟩

private theorem canPlace_inr {st : State} {c z : Card}
    (h : st.canPlace c (Sum.inr z) = true) :
    ∃ k, st.pileOfTop z = some k ∧ canSitOn c z = true := by
  rw [show st.canPlace c (Sum.inr z) =
      (match st.pileOfTop z with
        | some _ => canSitOn c z
        | none => false) from rfl] at h
  cases hps : st.pileOfTop z with
  | none => rw [hps] at h; exact absurd h (by simp)
  | some k => rw [hps] at h; exact ⟨k, rfl, by simpa using h⟩

private theorem wasteIs_head {st : State} {x : Card} {t : List Card}
    (hw : st.waste = x :: t) {c : Card} (h : st.wasteIs c = true) : x = c := by
  rw [State.wasteIs_cons hw c] at h
  exact of_decide_eq_true h

private theorem nextUp_true {st : State} {c : Card} (h : st.nextUp c = true) :
    c.rank.toIdx = (st.found c.suit).length := by
  have h' : c.rank.toIdx = st.foundHeight c.suit := of_decide_eq_true h
  exact h'

private theorem foundTop_lastOf {st : State} {c : Card}
    (h : st.foundTop c.suit = some c) : lastOf (st.found c.suit) = some c := h

private theorem step_draw_inv {st st' : State}
    (h : State.step st Move.draw = some st') : st.stepDraw = some st' := h

private theorem step_wasteToFound_inv {st st' : State} {c : Card}
    (h : State.step st (.wasteToFound c) = some st') :
    st.wasteIs c = true ∧ st.nextUp c = true ∧ ∃ ws, st.waste = c :: ws ∧
      st' = { st.setFound c.suit (st.found c.suit ++ [c]) with waste := ws } := by
  rw [show State.step st (.wasteToFound c) =
      (if st.wasteIs c && st.nextUp c then
        match st.waste with
        | _ :: ws => some { st.setFound c.suit (st.found c.suit ++ [c]) with waste := ws }
        | [] => none
      else none) from rfl] at h
  by_cases hg : (st.wasteIs c && st.nextUp c) = true
  · rw [ite_eq_left hg] at h
    rw [Bool.and_eq_true] at hg
    obtain ⟨h1, h2⟩ := hg
    split at h
    · rename_i x ws hw
      have hxc : x = c := wasteIs_head hw h1
      subst hxc
      exact ⟨h1, h2, ws, hw, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)
  · rw [ite_eq_right hg] at h; exact absurd h (by simp)

private theorem step_wasteToTab_inv {st st' : State} {c : Card} {b : Base}
    (h : State.step st (.wasteToTab c b) = some st') :
    st.wasteIs c = true ∧ st.canPlace c b = true ∧ ∃ ws, st.waste = c :: ws ∧
      st' = { st.putCard c b with waste := ws } := by
  rw [show State.step st (.wasteToTab c b) =
      (if st.wasteIs c && st.canPlace c b then
        match st.waste with
        | _ :: ws => some { st.putCard c b with waste := ws }
        | [] => none
      else none) from rfl] at h
  by_cases hg : (st.wasteIs c && st.canPlace c b) = true
  · rw [ite_eq_left hg] at h
    rw [Bool.and_eq_true] at hg
    obtain ⟨h1, h2⟩ := hg
    split at h
    · rename_i x ws hw
      have hxc : x = c := wasteIs_head hw h1
      subst hxc
      exact ⟨h1, h2, ws, hw, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)
  · rw [ite_eq_right hg] at h; exact absurd h (by simp)

private theorem step_tabToFound_inv {st st' : State} {c : Card}
    (h : State.step st (.tabToFound c) = some st') :
    st.nextUp c = true ∧ ∃ a, st.pileOfTop c = some a ∧
      st' = { st.setFound c.suit (st.found c.suit ++ [c]) with
               piles := fun a' =>
                 if a' = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
                 else st.piles a' } := by
  rw [show State.step st (.tabToFound c) =
      (if st.nextUp c then
        match st.pileOfTop c with
        | none => none
        | some a =>
            some { st.setFound c.suit (st.found c.suit ++ [c]) with
                     piles := fun a' =>
                       if a' = a then
                         Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
                       else st.piles a' }
      else none) from rfl] at h
  by_cases hg : st.nextUp c = true
  · rw [ite_eq_left hg] at h
    split at h
    · exact absurd h (by simp)
    · rename_i a hp
      exact ⟨hg, a, hp, (Option.some.inj h).symm⟩
  · rw [ite_eq_right hg] at h; exact absurd h (by simp)

private theorem step_foundToTab_inv {st st' : State} {c : Card} {b : Base}
    (h : State.step st (.foundToTab c b) = some st') :
    ∃ c', st.foundTop c.suit = some c' ∧ c' = c ∧ st.canPlace c b = true ∧
      st' = ((st.setFound c.suit (chop (st.found c.suit))).putCard c b) := by
  rw [show State.step st (.foundToTab c b) =
      (match st.foundTop c.suit with
        | some c' =>
            if decide (c' = c) && st.canPlace c b then
              some ((st.setFound c.suit (chop (st.found c.suit))).putCard c b)
            else none
        | none => none) from rfl] at h
  split at h
  · rename_i c0 hft
    by_cases hg : (decide (c0 = c) && st.canPlace c b) = true
    · rw [ite_eq_left hg] at h
      rw [Bool.and_eq_true] at hg
      obtain ⟨h1, h2⟩ := hg
      exact ⟨c0, hft, of_decide_eq_true h1, h2, (Option.some.inj h).symm⟩
    · rw [ite_eq_right hg] at h; exact absurd h (by simp)
  · exact absurd h (by simp)

private theorem step_tabToTab_inv {st st' : State} {c : Card} {b : Base}
    (h : State.step st (.tabToTab c b) = some st') :
    ∃ a, st.pileHolding c = some a ∧ st.canPlace c b = true ∧
      ∃ run, fromCard c (st.piles a).faceUp = run ∧
        st' = ((st.setPile a
          (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun run b) := by
  rw [show State.step st (.tabToTab c b) =
      (match st.pileHolding c with
        | none => none
        | some a =>
            if st.canPlace c b then
              match fromCard c (st.piles a).faceUp with
              | [] => none
              | run =>
                  some ((st.setPile a
                    (Pile.afterRunRemoved (st.piles a)
                      (below c (st.piles a).faceUp))).putRun run b)
            else none) from rfl] at h
  split at h
  · exact absurd h (by simp)
  · rename_i a hh
    by_cases hc : st.canPlace c b = true
    · rw [ite_eq_left hc] at h
      cases hrun : fromCard c (st.piles a).faceUp with
      | nil => rw [hrun] at h; exact absurd h (by simp)
      | cons y ys =>
          rw [hrun] at h
          exact ⟨a, hh, hc, (y :: ys), hrun, (Option.some.inj h).symm⟩
    · rw [ite_eq_right hc] at h; exact absurd h (by simp)

/-! ## Private kit: the draw, and pile update shapes -/


/-- Recycling moves no card between the counted zones. -/
private theorem recycle_pool_cnt (st : State) (c₀ : Card) :
    cnt c₀ (State.recycle st).stock + cnt c₀ (State.recycle st).waste
      = cnt c₀ st.stock + cnt c₀ st.waste := by
  by_cases hsne : st.stock = []
  · by_cases hwne : st.waste = []
    · rw [recycle_allEmpty st hsne hwne]
    · rw [recycle_nil st hsne hwne,
        show cnt c₀
            ({ st with stock := st.waste.reverse, waste := ([] : List Card) } : State).stock
          = cnt c₀ st.waste.reverse from rfl,
        show cnt c₀
            ({ st with stock := st.waste.reverse, waste := ([] : List Card) } : State).waste
          = cnt c₀ ([] : List Card) from rfl,
        cnt_reverse, hsne, cnt_nil]
      omega
  · rw [recycle_keep st hsne]



/-- The putters are pure pile updates at the located index. -/
private theorem putCard_eq_inl (st : State) (c : Card) (a : Anchor) :
    st.putCard c (Sum.inl a) = st.setPile a ⟨[], [c]⟩ := rfl

private theorem putCard_eq_inr {st : State} {c z : Card} {k : Anchor}
    (h : st.pileOfTop z = some k) :
    st.putCard c (Sum.inr z) =
      st.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] } := by
  show (match st.pileOfTop z with
    | some k' => st.setPile k' { st.piles k' with faceUp := (st.piles k').faceUp ++ [c] }
    | none => st) = _
  rw [h]

private theorem putRun_eq_inl (st : State) (run : List Card) (a : Anchor) :
    st.putRun run (Sum.inl a) = st.setPile a ⟨[], run⟩ := rfl

private theorem putRun_eq_inr {st : State} {run : List Card} {z : Card} {k : Anchor}
    (h : st.pileOfTop z = some k) :
    st.putRun run (Sum.inr z) =
      st.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ run } := by
  show (match st.pileOfTop z with
    | some k' => st.setPile k' { st.piles k' with faceUp := (st.piles k').faceUp ++ run }
    | none => st) = _
  rw [h]

/-! ## Private kit: the deal and the dealt piles -/

private theorem deal_pile_ne_nil {d : State.Deal}
    (hdlen : ∀ a, (d.piles a).length = a.toIdx + 1) (a : Anchor) : d.piles a ≠ [] := by
  intro hc
  have h := hdlen a
  rw [hc, show ([] : List Card).length = 0 from rfl] at h
  exact absurd h (fun hcon => Nat.succ_ne_zero a.toIdx hcon.symm)

/-- The dealt pile conserves its cards between the two fields: the
hidden cards are the reversed take, the face-up is the last, and
together they count the dealt list. -/
private theorem ofDealt_cnt (l : List Card) (h : l ≠ []) (c₀ : Card) :
    cnt c₀ ((Pile.ofDealt l).hidden ++ (Pile.ofDealt l).faceUp) = cnt c₀ l := by
  obtain ⟨x, hlast⟩ := lastOf_ne_nil l h
  have hhid : (Pile.ofDealt l).hidden = (l.take (l.length - 1)).reverse := rfl
  have hface : (Pile.ofDealt l).faceUp = [x] := by
    show (match lastOf l with | some c => [c] | none => ([] : List Card)) = _
    rw [hlast]
  have hstep1 : cnt c₀ ((Pile.ofDealt l).hidden ++ (Pile.ofDealt l).faceUp)
      = cnt c₀ ((chop l).reverse ++ [x]) := by
    rw [hhid, hface, ← chop_eq_take l]
  have hstep2 : cnt c₀ ((chop l).reverse ++ [x]) = cnt c₀ (chop l ++ [x]) := by
    simp only [cnt_snoc, cnt_singleton, cnt_reverse]
  have hdecomp : l = chop l ++ [x] := lastOf_chop hlast
  rw [hstep1, hstep2, ← hdecomp]

/-! ## The conservation fence at the deal -/

/-- `State.initial` of a `Deal.WF` deal is `WF` — the ticket at
`Orig.lean`'s plan: foundations start empty (take 0), each dealt
pile's face-up run is its dealt singleton, the card count is the
deal's own (conservation inherited through `ofDealt`), and the
draw step is the dealt one. -/
theorem initial_wf (d : State.Deal) (s : Nat) (hd : d.WF) (hs : 0 < s) :
    (State.initial d s).WF := by
  obtain ⟨hdlen, hstocklen, hcount⟩ := hd
  refine ⟨?_, ?_, ?_, hs⟩
  · intro σ
    exact ⟨0, rfl⟩
  · intro a
    have hne : d.piles a ≠ [] := deal_pile_ne_nil hdlen a
    obtain ⟨x, hlast⟩ := lastOf_ne_nil (d.piles a) hne
    have hface : ((State.initial d s).piles a).faceUp = [x] := by
      show (Pile.ofDealt (d.piles a)).faceUp = _
      show (match lastOf (d.piles a) with
        | some c => [c] | none => ([] : List Card)) = _
      rw [hlast]
    rw [hface]
    rfl
  · intro c₀ hc₀
    have hf : cntFlat c₀ (Suit.all.map (State.initial d s).found) = 0 :=
      cntFlat_map_nil Suit.all (State.initial d s).found c₀ (fun _ => rfl)
    have hp : cntFlat c₀ (Anchor.all.map fun a =>
          ((State.initial d s).piles a).hidden ++ ((State.initial d s).piles a).faceUp)
        = cnt c₀ ((Anchor.all.map d.piles).flatMap id) := by
      have h1 : cntFlat c₀ (Anchor.all.map fun a =>
          ((State.initial d s).piles a).hidden ++ ((State.initial d s).piles a).faceUp)
          = cntFlat c₀ (Anchor.all.map d.piles) :=
        cntFlat_map_congr c₀
          (fun a => ((State.initial d s).piles a).hidden ++ ((State.initial d s).piles a).faceUp)
          d.piles Anchor.all
          (fun j _ => ofDealt_cnt (d.piles j) (deal_pile_ne_nil hdlen j) c₀)
      rw [h1, cntFlat_flatMap]
    have hstock : cnt c₀ (State.initial d s).stock = cnt c₀ d.stock := rfl
    have hwaste : cnt c₀ (State.initial d s).waste = 0 := rfl
    rw [cardCount_zones, hf, hp, hstock, hwaste]
    have hc1 : cnt c₀ ((Anchor.all.map d.piles).flatMap id) + cnt c₀ d.stock = 1 := by
      have h2 := hcount c₀ hc₀
      rw [← cnt_filter] at h2
      rw [cnt_app] at h2
      exact h2
    omega

/-! ## Private kit: foundation prefix clauses -/

/-- `nextUp` pins the foundation prefix exactly at the next card's
index. -/
private theorem found_prefix_eq {st : State} {c : Card}
    (hpre : ∀ σ, ∃ n, st.found σ = σ.upCards.take n)
    (hnext : st.nextUp c = true) :
    ∃ n, st.found c.suit = c.suit.upCards.take n ∧ n = c.rank.toIdx := by
  obtain ⟨n, hn⟩ := hpre c.suit
  have hlen : c.rank.toIdx = (st.found c.suit).length := nextUp_true hnext
  have htakelen : (c.suit.upCards.take n).length = min n 13 := by
    rw [List.length_take, Suit.upCards_length]
  have hfl : (st.found c.suit).length = (c.suit.upCards.take n).length := by
    rw [hn]
  rcases Nat.lt_or_ge n 13 with hlt | hge
  · have hmin : min n 13 = n := Nat.min_eq_left (Nat.le_of_lt hlt)
    refine ⟨n, hn, ?_⟩
    omega
  · exfalso
    have hmin : min n 13 = 13 := Nat.min_eq_right hge
    have hc : c.rank.toIdx < 13 := Rank.toIdx_lt c.rank
    omega

/-- The appendix clause when a foundation gains its next card. -/
private theorem found_gain_clause {st st' : State} {c : Card}
    (hpre : ∀ σ, ∃ n, st.found σ = σ.upCards.take n)
    (hnext : st.nextUp c = true)
    (hself : st'.found c.suit = st.found c.suit ++ [c])
    (hne : ∀ σ ≠ c.suit, st'.found σ = st.found σ) :
    ∀ σ, ∃ n, st'.found σ = σ.upCards.take n := by
  intro σ
  rcases Decidable.em (σ = c.suit) with heq | hneσ
  · subst heq
    obtain ⟨n, hn, hnidx⟩ := found_prefix_eq hpre hnext
    refine ⟨n + 1, ?_⟩
    rw [hself, hn, hnidx, upCards_take_succ]
  · obtain ⟨n, hn⟩ := hpre σ
    exact ⟨n, by rw [hne σ hneσ, hn]⟩

/-- The prefix clause when a foundation loses its top card by the
`chop` of `foundTop`. -/
private theorem found_chop_prefix {st : State} {c : Card}
    (hpre : ∀ σ, ∃ n, st.found σ = σ.upCards.take n)
    (hlast : lastOf (st.found c.suit) = some c) :
    ∃ m, chop (st.found c.suit) = c.suit.upCards.take m := by
  obtain ⟨n, hn⟩ := hpre c.suit
  have hlmem : 1 ≤ (st.found c.suit).length :=
    List.length_pos_of_mem (lastOf_mem' _ hlast)
  have hfl : (st.found c.suit).length = (c.suit.upCards.take n).length := by
    rw [hn]
  have htakelen : (c.suit.upCards.take n).length = min n 13 := by
    rw [List.length_take, Suit.upCards_length]
  rcases Nat.lt_or_ge n 13 with hlt | hge
  · have hmin : min n 13 = n := Nat.min_eq_left (Nat.le_of_lt hlt)
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
    refine ⟨m, ?_⟩
    rw [hn, hm]
    have hguard : m + 1 ≤ c.suit.upCards.length := by
      rw [Suit.upCards_length]; omega
    exact chop_take_succ c.suit.upCards m hguard
  · refine ⟨12, ?_⟩
    have hup : c.suit.upCards = c.suit.upCards.take 13 :=
      (take_ge c.suit.upCards (by rw [Suit.upCards_length]; omega)).symm
    rw [hup]
    have hup2 : c.suit.upCards = c.suit.upCards.take 13 := hup
    rw [hn, take_ge c.suit.upCards (by rw [Suit.upCards_length]; omega), hup2]
    exact chop_take_succ c.suit.upCards 12 (by rw [Suit.upCards_length]; omega)

/-! ## The conservation fence, move by move -/

/-- The draw: only the stock and waste reshape (a recycle reverses
the waste into the stock; the deal takes and reverses), so all four
clauses survive. -/
private theorem draw_wf {st st' : State} (hwf : st.WF) (hstep : st.stepDraw = some st') :
    st'.WF := by
  obtain ⟨hpre, hpile, hcard, hstep1or3⟩ := hwf
  obtain ⟨r, hrec, hrne, hrw⟩ := draw_unfold hstep
  rw [← hrec] at hrw
  have hkeepsR : (State.recycle st).found = st.found ∧
      (State.recycle st).piles = st.piles ∧
      (State.recycle st).drawStep = st.drawStep := by
    by_cases hs : st.stock = []
    · by_cases hw : st.waste = []
      · rw [recycle_allEmpty st hs hw]
        exact ⟨rfl, rfl, rfl⟩
      · rw [recycle_nil st hs hw]
        exact ⟨rfl, rfl, rfl⟩
    · rw [recycle_keep st hs]
      exact ⟨rfl, rfl, rfl⟩
  obtain ⟨hk1, hk2, hk3⟩ := hkeepsR
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro σ
    have h1 : st'.found σ = st.found σ := by
      rw [hrw]
      show (State.recycle st).found σ = st.found σ
      rw [hk1]
    rw [h1]
    exact hpre σ
  · intro a
    have h1 : st'.piles a = st.piles a := by
      rw [hrw]
      show (State.recycle st).piles a = st.piles a
      rw [hk2]
    rw [h1]
    exact hpile a
  · intro c₀ hc₀
    have hcc := hcard c₀ hc₀
    rw [cardCount_zones] at hcc
    rw [cardCount_zones]
    have hst : st'.stock = r.stock.drop r.drawStep := by
      rw [hrw, hrec, dealUpTo_eq_take_drop]
    have hwst : st'.waste = (r.stock.take r.drawStep).reverse ++ r.waste := by
      rw [hrw, hrec, dealUpTo_eq_take_drop]
    have hs : cnt c₀ st'.stock + cnt c₀ st'.waste
        = cnt c₀ st.stock + cnt c₀ st.waste := by
      rw [hst, hwst, cnt_app, cnt_reverse]
      have hdealsplit : cnt c₀ (r.stock.take r.drawStep) + cnt c₀ (r.stock.drop r.drawStep)
          = cnt c₀ r.stock := by
        rw [← cnt_app, List.take_append_drop]
      have hpool := recycle_pool_cnt st c₀
      rw [hrec] at hpool
      omega
    have hf : cntFlat c₀ (Suit.all.map st'.found) = cntFlat c₀ (Suit.all.map st.found) := by
      rw [show st'.found = (State.recycle st).found from by rw [hrw], hk1]
    have hp : cntFlat c₀ (Anchor.all.map fun a => (st'.piles a).hidden ++ (st'.piles a).faceUp)
        = cntFlat c₀ (Anchor.all.map fun a => (st.piles a).hidden ++ (st.piles a).faceUp) := by
      have hp0 : st'.piles = (State.recycle st).piles := by rw [hrw]
      rw [show (fun a => (st'.piles a).hidden ++ (st'.piles a).faceUp) =
          (fun a => ((State.recycle st).piles a).hidden ++ ((State.recycle st).piles a).faceUp)
          from by rw [show (fun a : Anchor => (st'.piles a).hidden ++ (st'.piles a).faceUp) =
            (fun a : Anchor => (st'.piles a).hidden ++ (st'.piles a).faceUp) from rfl,
          hp0],
        hk2]
    omega
  · have hsd : st'.drawStep = st.drawStep := by
      rw [hrw]
      show (State.recycle st).drawStep = st.drawStep
      rw [hk3]
    rw [hsd]; exact hstep1or3

private theorem Suit_all_nodup : (Suit.all : List Suit).Nodup := by decide
private theorem Anchor_all_nodup : (Anchor.all : List Anchor).Nodup := by decide

/-- The `wasteToFound` move: the waste top joins its foundation. -/
private theorem wasteToFound_wf {st st' : State} {c : Card}
    (hwf : st.WF) (h : State.step st (.wasteToFound c) = some st') : st'.WF := by
  obtain ⟨hpre, hpile, hcard, hsd⟩ := hwf
  obtain ⟨hwasteis, hnextup, ws, hweq, hrw⟩ := step_wasteToFound_inv h
  have hf : st'.found c.suit = st.found c.suit ++ [c] := by
    rw [hrw]
    show (st.setFound c.suit (st.found c.suit ++ [c])).found c.suit = _
    rw [setFound_found_self]
  have hfne : ∀ σ ≠ c.suit, st'.found σ = st.found σ := by
    intro σ hσ
    rw [hrw]
    show (st.setFound c.suit (st.found c.suit ++ [c])).found σ = _
    rw [setFound_found_ne hσ]
  have hpp : st'.piles = st.piles := by rw [hrw]; rfl
  have hwr : st'.waste = ws := by rw [hrw]
  have hstock : st'.stock = st.stock := by rw [hrw]; rfl
  have hsd' : 0 < st'.drawStep := by
    have hdeq : st'.drawStep = st.drawStep := by
      rw [hrw]
      show (st.setFound c.suit (st.found c.suit ++ [c])).drawStep = st.drawStep
      rfl
    rw [hdeq]; exact hsd
  refine ⟨?_, ?_, ?_, hsd'⟩
  · exact found_gain_clause hpre hnextup hf hfne
  · intro a
    rw [show st'.piles a = st.piles a from by rw [hpp]]
    exact hpile a
  · intro c₀ hc₀
    have hcc := hcard c₀ hc₀
    rw [cardCount_zones] at hcc
    rw [cardCount_zones]
    have hp : cntFlat c₀ (Anchor.all.map fun a => (st'.piles a).hidden ++ (st'.piles a).faceUp)
        = cntFlat c₀ (Anchor.all.map fun a => (st.piles a).hidden ++ (st.piles a).faceUp) := by
      rw [hpp]
    have hfdelta : cntFlat c₀ (Suit.all.map st'.found)
        = cntFlat c₀ (Suit.all.map st.found) + cnt c₀ [c] := by
      have h1 := cntFlat_map_delta c₀ st.found st'.found Suit.all
        (fun σ => if σ = c.suit then cnt c₀ [c] else 0)
        (by intro σ _
            by_cases hσc : σ = c.suit
            · rw [hσc, hf, cnt_snoc, ite_eq_left rfl]
            · rw [hfne σ hσc, ite_eq_right hσc]
              omega)
      have h2 : (Suit.all.map (fun σ => if σ = c.suit then cnt c₀ [c] else 0)).sum
          = cnt c₀ [c] := by
        have h3 := sum_map_single Suit.all (fun σ => if σ = c.suit then cnt c₀ [c] else 0)
          c.suit Suit_all_nodup (Suit.mem_all c.suit)
          (by intro j _ hjc; rw [ite_eq_right hjc])
        have h4 : (if c.suit = c.suit then cnt c₀ [c] else 0) = cnt c₀ [c] :=
          by rw [ite_eq_left rfl]
        rw [h3, h4]
      rw [← h1, h2]
    have hwaste : cnt c₀ st'.waste + cnt c₀ [c] = cnt c₀ st.waste := by
      rw [hwr, hweq, cnt_def c₀ c ws, cnt_singleton c₀ c]
      omega
    have hstockc : cnt c₀ st'.stock = cnt c₀ st.stock := by rw [hstock]
    omega

/-- The search soundness fact the pile-top fit needs. -/
private theorem pileOfTop_top {st : State} {z : Card} {a : Anchor}
    (h : st.pileOfTop z = some a) : lastOf (st.piles a).faceUp = some z := by
  have h' : firstWhere (fun a' => decide (st.topOf a' = some z)) Anchor.all = some a := h
  have h2 := firstWhere_sound (fun a' => decide (st.topOf a' = some z)) h'
  have h3 : st.topOf a = some z := of_decide_eq_true h2
  exact h3


/-- An empty pile has both fields empty. -/
private theorem pile_isEmpty {p : Pile} (h : p.isEmpty = true) :
    p.hidden = [] ∧ p.faceUp = [] := by
  rcases p with ⟨hid, fu⟩
  cases hid <;> cases fu <;> simp_all [Pile.isEmpty]

/-- The `wasteToTab` move: the waste top joins the tableau, either a
king opening an empty position or a card fitted under a pile top. -/
private theorem wasteToTab_wf {st st' : State} {c : Card} {b : Base}
    (hwf : st.WF) (h : State.step st (.wasteToTab c b) = some st') : st'.WF := by
  obtain ⟨hpre, hpile, hcard, hsd⟩ := hwf
  obtain ⟨hwasteis, hcanplace, ws, hweq, hrw⟩ := step_wasteToTab_inv h
  have hwr : st'.waste = ws := by rw [hrw]
  have hwaste : ∀ c₀, cnt c₀ st'.waste + cnt c₀ [c] = cnt c₀ st.waste := by
    intro c₀
    rw [hwr, hweq, cnt_def c₀ c ws, cnt_singleton c₀ c]
    omega
  cases b with
  | inl a₁ =>
      obtain ⟨hempty, _⟩ := canPlace_inl hcanplace
      obtain ⟨hid, hfu⟩ := pile_isEmpty hempty
      have hstock : st'.stock = st.stock := by rw [hrw, putCard_eq_inl]; rfl
      have hfeq : st'.found = st.found := by rw [hrw, putCard_eq_inl]; rfl
      have hsd' : 0 < st'.drawStep := by
        have hdeq : st'.drawStep = st.drawStep := by
          rw [hrw, putCard_eq_inl]; rfl
        rw [hdeq]; exact hsd
      have hstockc : ∀ c₀, cnt c₀ st'.stock = cnt c₀ st.stock := fun c₀ => by rw [hstock]
      have hfcnt : ∀ c₀, cntFlat c₀ (Suit.all.map st'.found)
          = cntFlat c₀ (Suit.all.map st.found) := fun c₀ => by rw [hfeq]
      have hrp : st'.piles = (st.setPile a₁ ⟨[], [c]⟩).piles := by rw [hrw, putCard_eq_inl]
      refine ⟨?_, ?_, ?_, hsd'⟩
      · intro σ
        have h1 : st'.found σ = st.found σ := by rw [hfeq]
        rw [h1]
        exact hpre σ
      · intro a
        rcases Decidable.em (a = a₁) with ha | ha
        · rw [ha, show st'.piles a₁ = (st.setPile a₁ ⟨[], [c]⟩).piles a₁ from by rw [hrp],
            setPile_piles_self]
          show runOK ([c] : List Card) = true
          rfl
        · rw [show st'.piles a = (st.setPile a₁ ⟨[], [c]⟩).piles a from by rw [hrp],
            setPile_piles_ne ha]
          exact hpile a
      · intro c₀ hc₀
        have hcc := hcard c₀ hc₀
        rw [cardCount_zones] at hcc
        rw [cardCount_zones]
        have hpcnt : cntFlat c₀
              (Anchor.all.map fun j => (st'.piles j).hidden ++ (st'.piles j).faceUp)
            = cntFlat c₀ (Anchor.all.map fun j => (st.piles j).hidden ++ (st.piles j).faceUp)
              + cnt c₀ [c] := by
          have h1 := cntFlat_map_delta c₀
            (fun j => (st.piles j).hidden ++ (st.piles j).faceUp)
            (fun j => ((st.setPile a₁ ⟨[], [c]⟩).piles j).hidden
              ++ ((st.setPile a₁ ⟨[], [c]⟩).piles j).faceUp)
            Anchor.all
            (fun j => if j = a₁ then cnt c₀ [c] else 0)
            (by intro j _
                by_cases hj : j = a₁
                · have hGO : cnt c₀
                        (((st.setPile a₁ ⟨[], [c]⟩).piles a₁).hidden
                          ++ ((st.setPile a₁ ⟨[], [c]⟩).piles a₁).faceUp)
                      = cnt c₀ ([c] : List Card) := by
                    rw [setPile_piles_self]
                    show cnt c₀ (([] : List Card) ++ ([c] : List Card)) = cnt c₀ [c]
                    rw [cnt_app, cnt_nil]
                    omega
                  have hFO : cnt c₀ ((st.piles a₁).hidden ++ (st.piles a₁).faceUp)
                      = 0 := by rw [hid, hfu, cnt_app, cnt_nil]
                  rw [hj, hGO, ite_eq_left rfl, hFO]
                  omega
                · rw [ite_eq_right hj]
                  have hident : cnt c₀ ((st.piles j).hidden ++ (st.piles j).faceUp)
                      = cnt c₀ (((st.setPile a₁ ⟨[], [c]⟩).piles j).hidden
                        ++ ((st.setPile a₁ ⟨[], [c]⟩).piles j).faceUp) := by
                    rw [setPile_piles_ne hj]
                  rw [hident]
                  omega)
          have h2 : (Anchor.all.map (fun j => if j = a₁ then cnt c₀ [c] else 0)).sum
              = cnt c₀ [c] := by
            have h3 := sum_map_single Anchor.all
              (fun j => if j = a₁ then cnt c₀ [c] else 0) a₁
              Anchor_all_nodup (Anchor.mem_all a₁)
              (by intro j _ hjc; rw [ite_eq_right hjc])
            have h4 : (if a₁ = a₁ then cnt c₀ [c] else 0) = cnt c₀ [c] := by
              rw [ite_eq_left rfl]
            rw [h3, h4]
          have hfold : cntFlat c₀
              (Anchor.all.map fun j => (st'.piles j).hidden ++ (st'.piles j).faceUp)
              = cntFlat c₀
                  (Anchor.all.map fun j => ((st.setPile a₁ ⟨[], [c]⟩).piles j).hidden
                    ++ ((st.setPile a₁ ⟨[], [c]⟩).piles j).faceUp) := by
            rw [hrp]
          rw [hfold, ← h1, h2]
        rw [hpcnt, hfcnt c₀, hstockc c₀]
        have hwaste0 := hwaste c₀
        omega
  | inr z =>
      obtain ⟨k, hps, hfit⟩ := canPlace_inr hcanplace
      have htopk : lastOf (st.piles k).faceUp = some z := pileOfTop_top hps
      have hstock : st'.stock = st.stock := by rw [hrw, putCard_eq_inr hps]; rfl
      have hfeq : st'.found = st.found := by rw [hrw, putCard_eq_inr hps]; rfl
      have hsd' : 0 < st'.drawStep := by
        have hdeq : st'.drawStep = st.drawStep := by
          rw [hrw, putCard_eq_inr hps]; rfl
        rw [hdeq]; exact hsd
      have hstockc : ∀ c₀, cnt c₀ st'.stock = cnt c₀ st.stock := fun c₀ => by rw [hstock]
      have hfcnt : ∀ c₀, cntFlat c₀ (Suit.all.map st'.found)
          = cntFlat c₀ (Suit.all.map st.found) := fun c₀ => by rw [hfeq]
      have hrp : st'.piles
          = (st.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles := by
        rw [hrw, putCard_eq_inr hps]
      refine ⟨?_, ?_, ?_, hsd'⟩
      · intro σ
        have h1 : st'.found σ = st.found σ := by rw [hfeq]
        rw [h1]
        exact hpre σ
      · intro a
        rcases Decidable.em (a = k) with ha | ha
        · rw [ha, show st'.piles k = (st.setPile k
                { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles k from by rw [hrp],
            setPile_piles_self]
          show runOK ((st.piles k).faceUp ++ ([c] : List Card)) = true
          exact runOK_append_fit (st.piles k).faceUp c z ([] : List Card)
            (hpile k) rfl htopk hfit
        · rw [show st'.piles a = (st.setPile k
                { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles a from by rw [hrp],
            setPile_piles_ne ha]
          exact hpile a
      · intro c₀ hc₀
        have hcc := hcard c₀ hc₀
        rw [cardCount_zones] at hcc
        rw [cardCount_zones]
        have hpcnt : cntFlat c₀
              (Anchor.all.map fun j => (st'.piles j).hidden ++ (st'.piles j).faceUp)
            = cntFlat c₀ (Anchor.all.map fun j => (st.piles j).hidden ++ (st.piles j).faceUp)
              + cnt c₀ [c] := by
          have h1 := cntFlat_map_delta c₀
            (fun j => (st.piles j).hidden ++ (st.piles j).faceUp)
            (fun j => ((st.setPile k
                { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles j).hidden
              ++ ((st.setPile k
                { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles j).faceUp)
            Anchor.all
            (fun j => if j = k then cnt c₀ [c] else 0)
            (by intro j _
                by_cases hj : j = k
                · have hG : cnt c₀
                        (((st.setPile k
                            { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles k).hidden
                          ++ ((st.setPile k
                            { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles k).faceUp)
                      = cnt c₀ ((st.piles k).hidden ++ ((st.piles k).faceUp ++ [c])) := by
                    rw [setPile_piles_self]
                  rw [hj, hG, ite_eq_left rfl, ← List.append_assoc, cnt_snoc]
                · rw [ite_eq_right hj]
                  have hident : cnt c₀ ((st.piles j).hidden ++ (st.piles j).faceUp)
                      = cnt c₀ (((st.setPile k
                          { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles j).hidden
                        ++ ((st.setPile k
                          { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles j).faceUp) := by
                    rw [setPile_piles_ne hj]
                  rw [hident]
                  omega)
          have h2 : (Anchor.all.map (fun j => if j = k then cnt c₀ [c] else 0)).sum
              = cnt c₀ [c] := by
            have h3 := sum_map_single Anchor.all
              (fun j => if j = k then cnt c₀ [c] else 0) k
              Anchor_all_nodup (Anchor.mem_all k)
              (by intro j _ hjc; rw [ite_eq_right hjc])
            have h4 : (if k = k then cnt c₀ [c] else 0) = cnt c₀ [c] := by
              rw [ite_eq_left rfl]
            rw [h3, h4]
          have hfold : cntFlat c₀
              (Anchor.all.map fun j => (st'.piles j).hidden ++ (st'.piles j).faceUp)
              = cntFlat c₀
                  (Anchor.all.map fun j => ((st.setPile k
                      { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles j).hidden
                    ++ ((st.setPile k
                      { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles j).faceUp) := by
            rw [hrp]
          rw [hfold, ← h1, h2]
        rw [hpcnt, hfcnt c₀, hstockc c₀]
        have hwaste0 := hwaste c₀
        omega

/-! ## The three remaining move cases -/

/-- Removing a nonempty remainder keeps it as the face-up run. -/
private theorem afterRunRemoved_ne_nil (p : Pile) (pre : List Card)
    (hne : pre ≠ []) : Pile.afterRunRemoved p pre = { p with faceUp := pre } := by
  cases pre with
  | cons w ws => rfl
  | nil => exact absurd rfl hne

/-- The zone-count transfer law of run removal: the pile zone keeps
its multiset — the removed run counts on the other side of the
ledger. -/
private theorem afterRunRemoved_zone_cnt (p : Pile) (post : List Card) (c₀ : Card) :
    ∀ (pre : List Card), p.faceUp = pre ++ post →
    cnt c₀ ((Pile.afterRunRemoved p pre).hidden
        ++ (Pile.afterRunRemoved p pre).faceUp)
      + cnt c₀ post = cnt c₀ (p.hidden ++ p.faceUp) := by
  intro pre
  cases pre with
  | nil =>
      intro hsplit
      cases p with
      | mk hid fu =>
        cases hid with
        | nil =>
            have hf : fu = post := hsplit
            rw [hf]
            show cnt c₀ (([] : List Card) ++ ([] : List Card)) + cnt c₀ post
              = cnt c₀ (([] : List Card) ++ post)
            rw [cnt_app, cnt_app, cnt_nil]
        | cons y t =>
            have hf : fu = post := hsplit
            rw [hf]
            show cnt c₀ (t ++ ([y] : List Card)) + cnt c₀ post
              = cnt c₀ ((y :: t) ++ post)
            rw [cnt_snoc, List.cons_append, cnt_def c₀ y (t ++ post),
              cnt_app c₀ t post, cnt_def c₀ y ([] : List Card), cnt_nil c₀]
            omega
  | cons w ws =>
      intro hsplit
      have hfm : Pile.afterRunRemoved p (w :: ws) = { p with faceUp := w :: ws } := rfl
      rw [hfm]
      have hf : p.faceUp = (w :: ws) ++ post := hsplit
      rw [hf]
      show cnt c₀ (p.hidden ++ (w :: ws)) + cnt c₀ post
        = cnt c₀ (p.hidden ++ ((w :: ws) ++ post))
      rw [← List.append_assoc, cnt_app c₀ (p.hidden ++ (w :: ws)) post]

/-- In a legal face-up run every card strictly above the head sits
strictly below it in rank. -/
private theorem runOK_tail_lt : ∀ (t : List Card) (x y : Card),
    runOK (x :: t) = true → y ∈ t → y.rank.toIdx < x.rank.toIdx := by
  intro t
  induction t with
  | nil => intro x y _ hmem; exact absurd hmem List.not_mem_nil
  | cons w ws ih =>
      intro x y hrun hmem
      have hsplit := runOK_two_true hrun
      obtain ⟨hsit, hrest⟩ := hsplit
      have hwlt : w.rank.toIdx + 1 = x.rank.toIdx := (canSitOn_eq w x).mp hsit |>.1
      rcases List.mem_cons.mp hmem with hmem' | hmem'
      · rw [hmem']
        omega
      · have hy := ih w y hrest hmem'
        omega

/-- The top of a face-up run containing `c` lies inside the run
`fromCard c` removes. -/
private theorem lastOf_mem_fromCard : ∀ (l : List Card) (c : Card),
    c ∈ l → ∀ z, lastOf l = some z → z ∈ fromCard c l
  | [], _, hmem, _, _ => absurd hmem List.not_mem_nil
  | [w], c, hmem, z, hlast => by
      have hc : w = c := (List.mem_cons.mp hmem).elim
        (fun h => h.symm) (fun h => absurd h List.not_mem_nil)
      have hwz : w = z := Option.some.inj hlast
      rw [← hwz, ← hc, fromCard_cons, ite_eq_left rfl]
      exact List.mem_cons.mpr (Or.inl rfl)
  | x :: y :: t, c, hmem, z, hlast => by
      by_cases hxc : x = c
      · rw [fromCard_cons, ite_eq_left hxc]
        exact lastOf_mem' (x :: y :: t) hlast
      · rw [fromCard_cons, ite_eq_right hxc]
        have hc2 : c ∈ (y :: t) :=
          (List.mem_cons.mp hmem).elim
            (fun h => absurd h.symm hxc) (fun h => h)
        have hlast2 : lastOf (y :: t) = some z := hlast
        exact lastOf_mem_fromCard (y :: t) c hc2 z hlast2

/-- The revealed reveal: the afterRunRemoved-nil face-up run is
always legal (empty, or the flipped singleton). -/
private theorem runOK_afterRunRemoved_nil (p : Pile) :
    runOK (Pile.afterRunRemoved p []).faceUp = true := by
  cases p with
  | mk hid fu =>
    cases hid with
    | nil => rfl
    | cons y t => rfl

/-- The `tabToFound` move: the pile top joins its foundation; the
pile face-up run loses its last card, possibly revealing one hidden
card. -/
private theorem tabToFound_wf {st st' : State} {c : Card}
    (hwf : st.WF) (h : State.step st (.tabToFound c) = some st') : st'.WF := by
  obtain ⟨hpre, hpile, hcard, hsd⟩ := hwf
  obtain ⟨hnextup, a, hpstop, hrw⟩ := step_tabToFound_inv h
  have hf : st'.found c.suit = st.found c.suit ++ [c] := by
    rw [hrw]
    show (st.setFound c.suit (st.found c.suit ++ [c])).found c.suit = _
    rw [setFound_found_self]
  have hfne : ∀ σ ≠ c.suit, st'.found σ = st.found σ := by
    intro σ hσ
    rw [hrw]
    show (st.setFound c.suit (st.found c.suit ++ [c])).found σ = _
    rw [setFound_found_ne hσ]
  have hpj : ∀ j, st'.piles j =
      if j = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
      else st.piles j := by
    intro j
    rw [hrw]
  have hstockeq : st'.stock = st.stock := by
    rw [hrw]
    show (st.setFound c.suit (st.found c.suit ++ [c])).stock = st.stock
    rfl
  have hwasteq : st'.waste = st.waste := by
    rw [hrw]
    show (st.setFound c.suit (st.found c.suit ++ [c])).waste = st.waste
    rfl
  have hsd' : 0 < st'.drawStep := by
    have hdeq : st'.drawStep = st.drawStep := by
      rw [hrw]
      show (st.setFound c.suit (st.found c.suit ++ [c])).drawStep = st.drawStep
      rfl
    rw [hdeq]; exact hsd
  refine ⟨?_, ?_, ?_, hsd'⟩
  · exact found_gain_clause hpre hnextup hf hfne
  · intro j
    rcases Decidable.em (j = a) with hj | hj
    · rw [hj, hpj a, ite_eq_left rfl]
      cases hchop : chop (st.piles a).faceUp with
      | nil => exact runOK_afterRunRemoved_nil (st.piles a)
      | cons y t =>
          show runOK ((y :: t : List Card)) = true
          rw [← hchop]
          exact runOK_chop (hpile a)
    · rw [hpj j, ite_eq_right hj]
      exact hpile j
  · intro c₀ hc₀
    have hcc := hcard c₀ hc₀
    rw [cardCount_zones] at hcc
    rw [cardCount_zones]
    have hlastc : lastOf (st.piles a).faceUp = some c := pileOfTop_top hpstop
    have hsnoc : (st.piles a).faceUp = chop (st.piles a).faceUp ++ [c] :=
      lastOf_chop hlastc
    have hpcnt : cntFlat c₀
          (Anchor.all.map fun j => (st'.piles j).hidden ++ (st'.piles j).faceUp)
        + cnt c₀ [c]
        = cntFlat c₀ (Anchor.all.map fun j => (st.piles j).hidden ++ (st.piles j).faceUp) := by
      have h1 := cntFlat_map_delta c₀
        (fun j => (st'.piles j).hidden ++ (st'.piles j).faceUp)
        (fun j => (st.piles j).hidden ++ (st.piles j).faceUp)
        Anchor.all
        (fun j => if j = a then cnt c₀ [c] else 0)
        (by intro j _
            by_cases hj : j = a
            · rw [hj, hpj a, ite_eq_left rfl, ite_eq_left rfl]
              exact afterRunRemoved_zone_cnt (st.piles a) [c] c₀
                (chop (st.piles a).faceUp) hsnoc
            · rw [hpj j, ite_eq_right hj, ite_eq_right hj]
              omega)
      have h2 : (Anchor.all.map (fun j => if j = a then cnt c₀ [c] else 0)).sum
          = cnt c₀ [c] := by
        have h3 := sum_map_single Anchor.all
          (fun j => if j = a then cnt c₀ [c] else 0) a
          Anchor_all_nodup (Anchor.mem_all a)
          (by intro j _ hjc; rw [ite_eq_right hjc])
        have h4 : (if a = a then cnt c₀ [c] else 0) = cnt c₀ [c] := by
          rw [ite_eq_left rfl]
        rw [h3, h4]
      rw [← h1, h2]
    have hfdelta : cntFlat c₀ (Suit.all.map st'.found)
        = cntFlat c₀ (Suit.all.map st.found) + cnt c₀ [c] := by
      have h1 := cntFlat_map_delta c₀ st.found st'.found Suit.all
        (fun σ => if σ = c.suit then cnt c₀ [c] else 0)
        (by intro σ _
            by_cases hσc : σ = c.suit
            · rw [hσc, hf, cnt_snoc, ite_eq_left rfl]
            · rw [hfne σ hσc, ite_eq_right hσc]
              omega)
      have h2 : (Suit.all.map (fun σ => if σ = c.suit then cnt c₀ [c] else 0)).sum
          = cnt c₀ [c] := by
        have h3 := sum_map_single Suit.all
          (fun σ => if σ = c.suit then cnt c₀ [c] else 0) c.suit
          Suit_all_nodup (Suit.mem_all c.suit)
          (by intro j _ hjc; rw [ite_eq_right hjc])
        have h4 : (if c.suit = c.suit then cnt c₀ [c] else 0) = cnt c₀ [c] := by
          rw [ite_eq_left rfl]
        rw [h3, h4]
      rw [← h1, h2]
    have hstockc : cnt c₀ st'.stock = cnt c₀ st.stock := by rw [hstockeq]
    have hwastec : cnt c₀ st'.waste = cnt c₀ st.waste := by rw [hwasteq]
    omega

/-- The `foundToTab` move: the foundation top returns to the
tableau — the foundation loses its top card by `chop`, and the
empty position or pile top takes it. -/
private theorem foundToTab_wf {st st' : State} {c : Card} {b : Base}
    (hwf : st.WF) (h : State.step st (.foundToTab c b) = some st') : st'.WF := by
  obtain ⟨hpre, hpile, hcard, hsd⟩ := hwf
  obtain ⟨c₀', hft, hc'c, hcp, hrw⟩ := step_foundToTab_inv h
  have hc'' : st.foundTop c.suit = some c := hft.trans (congrArg some hc'c)
  have hlast : lastOf (st.found c.suit) = some c := foundTop_lastOf hc''
  have hsnocf : st.found c.suit = chop (st.found c.suit) ++ [c] :=
    lastOf_chop hlast
  have hR : ∀ c₀, cnt c₀ (st.found c.suit)
      = cnt c₀ (chop (st.found c.suit)) + cnt c₀ [c] := by
    intro c₀
    have h1 : cnt c₀ (chop (st.found c.suit) ++ [c])
        = cnt c₀ (chop (st.found c.suit)) + cnt c₀ [c] :=
      cnt_snoc c₀ c (chop (st.found c.suit))
    rw [← hsnocf] at h1
    exact h1
  cases b with
  | inl a₁ =>
      obtain ⟨hempty, _⟩ := canPlace_inl hcp
      have hfeq : st'.found
          = (st.setFound c.suit (chop (st.found c.suit))).found := by
        rw [hrw, putCard_eq_inl]
        rfl
      have hpil : st'.piles
          = (st.setFound c.suit (chop (st.found c.suit))
            |>.setPile a₁ ⟨[], [c]⟩).piles := by
        rw [hrw, putCard_eq_inl]
      have hstock : st'.stock = st.stock := by
        rw [hrw, putCard_eq_inl]
        show (st.setFound c.suit (chop (st.found c.suit))).stock = st.stock
        rfl
      have hwaste : st'.waste = st.waste := by
        rw [hrw, putCard_eq_inl]
        show (st.setFound c.suit (chop (st.found c.suit))).waste = st.waste
        rfl
      have hsd' : 0 < st'.drawStep := by
        have hdeq : st'.drawStep = st.drawStep := by
          rw [hrw, putCard_eq_inl]
          show (st.setFound c.suit (chop (st.found c.suit))).drawStep = st.drawStep
          rfl
        rw [hdeq]; exact hsd
      refine ⟨?_, ?_, ?_, hsd'⟩
      · intro σ
        rcases Decidable.em (σ = c.suit) with hσ | hσ
        · obtain ⟨m, hm⟩ := found_chop_prefix hpre hlast
          refine ⟨m, ?_⟩
          rw [hσ, hfeq, show (st.setFound c.suit (chop (st.found c.suit))).found c.suit
              = chop (st.found c.suit) from setFound_found_self, hm]
        · obtain ⟨n, hn⟩ := hpre σ
          refine ⟨n, ?_⟩
          rw [hfeq, setFound_found_ne hσ, hn]
      · intro j
        rcases Decidable.em (j = a₁) with hj | hj
        · rw [hj, show st'.piles a₁
              = (st.setFound c.suit (chop (st.found c.suit))
                  |>.setPile a₁ ⟨[], [c]⟩).piles a₁ from by rw [hpil],
            setPile_piles_self]
          show runOK ([c] : List Card) = true
          rfl
        · rw [show st'.piles j
              = (st.setFound c.suit (chop (st.found c.suit))
                  |>.setPile a₁ ⟨[], [c]⟩).piles j from by rw [hpil],
            setPile_piles_ne hj]
          exact hpile j
      · intro c₀ hc₀
        have hcc := hcard c₀ hc₀
        rw [cardCount_zones] at hcc
        rw [cardCount_zones]
        have hfdelta : cntFlat c₀ (Suit.all.map st'.found) + cnt c₀ [c]
            = cntFlat c₀ (Suit.all.map st.found) := by
          have h1 := cntFlat_map_delta c₀ st'.found st.found Suit.all
            (fun σ => if σ = c.suit then cnt c₀ [c] else 0)
            (by intro σ _
                by_cases hσ : σ = c.suit
                · rw [hσ, hfeq, setFound_found_self, ite_eq_left rfl, hR c₀]
                · rw [hfeq, setFound_found_ne hσ, ite_eq_right hσ]
                  omega)
          have h2 : (Suit.all.map (fun σ => if σ = c.suit then cnt c₀ [c] else 0)).sum
              = cnt c₀ [c] := by
            have h3 := sum_map_single Suit.all
              (fun σ => if σ = c.suit then cnt c₀ [c] else 0) c.suit
              Suit_all_nodup (Suit.mem_all c.suit)
              (by intro j _ hjc; rw [ite_eq_right hjc])
            have h4 : (if c.suit = c.suit then cnt c₀ [c] else 0) = cnt c₀ [c] := by
              rw [ite_eq_left rfl]
            rw [h3, h4]
          rw [← h1, h2]
        have hpcnt : cntFlat c₀
              (Anchor.all.map fun j => (st'.piles j).hidden ++ (st'.piles j).faceUp)
            = cntFlat c₀ (Anchor.all.map fun j => (st.piles j).hidden ++ (st.piles j).faceUp)
              + cnt c₀ [c] := by
          have h1 := cntFlat_map_delta c₀
            (fun j => (st.piles j).hidden ++ (st.piles j).faceUp)
            (fun j => ((st.setFound c.suit (chop (st.found c.suit))
                |>.setPile a₁ ⟨[], [c]⟩).piles j).hidden
              ++ ((st.setFound c.suit (chop (st.found c.suit))
                |>.setPile a₁ ⟨[], [c]⟩).piles j).faceUp)
            Anchor.all
            (fun j => if j = a₁ then cnt c₀ [c] else 0)
            (by intro j _
                by_cases hj : j = a₁
                · have hgo : cnt c₀
                        (((st.setFound c.suit (chop (st.found c.suit))
                          |>.setPile a₁ ⟨[], [c]⟩).piles a₁).hidden
                          ++ ((st.setFound c.suit (chop (st.found c.suit))
                          |>.setPile a₁ ⟨[], [c]⟩).piles a₁).faceUp)
                      = cnt c₀ ([c] : List Card) := by
                    rw [setPile_piles_self]
                    show cnt c₀ (([] : List Card) ++ ([c] : List Card)) = cnt c₀ [c]
                    rw [cnt_app, cnt_nil]
                    omega
                  have hF0 : cnt c₀ ((st.piles a₁).hidden ++ (st.piles a₁).faceUp)
                      = 0 := by
                    obtain ⟨hid, hfu⟩ := pile_isEmpty hempty
                    rw [hid, hfu, cnt_app, cnt_nil]
                  rw [hj, hgo, ite_eq_left rfl, hF0]
                  omega
                · rw [ite_eq_right hj]
                  have hident : cnt c₀ ((st.piles j).hidden ++ (st.piles j).faceUp)
                      = cnt c₀ (((st.setFound c.suit (chop (st.found c.suit))
                          |>.setPile a₁ ⟨[], [c]⟩).piles j).hidden
                        ++ ((st.setFound c.suit (chop (st.found c.suit))
                          |>.setPile a₁ ⟨[], [c]⟩).piles j).faceUp) := by
                    rw [setPile_piles_ne hj]
                    rfl
                  rw [hident]
                  omega)

          have h2 : (Anchor.all.map (fun j => if j = a₁ then cnt c₀ [c] else 0)).sum
              = cnt c₀ [c] := by
            have h3 := sum_map_single Anchor.all
              (fun j => if j = a₁ then cnt c₀ [c] else 0) a₁
              Anchor_all_nodup (Anchor.mem_all a₁)
              (by intro j _ hjc; rw [ite_eq_right hjc])
            have h4 : (if a₁ = a₁ then cnt c₀ [c] else 0) = cnt c₀ [c] := by
              rw [ite_eq_left rfl]
            rw [h3, h4]
          have hfold : cntFlat c₀
              (Anchor.all.map fun j => (st'.piles j).hidden ++ (st'.piles j).faceUp)
              = cntFlat c₀
                  (Anchor.all.map fun j => ((st.setFound c.suit (chop (st.found c.suit))
                      |>.setPile a₁ ⟨[], [c]⟩).piles j).hidden
                    ++ ((st.setFound c.suit (chop (st.found c.suit))
                      |>.setPile a₁ ⟨[], [c]⟩).piles j).faceUp) := by
            rw [hpil]
          rw [hfold, ← h1, h2]
        have hstockc : cnt c₀ st'.stock = cnt c₀ st.stock := by rw [hstock]
        have hwastec : cnt c₀ st'.waste = cnt c₀ st.waste := by rw [hwaste]
        omega
  | inr z =>
      obtain ⟨k, hps, hfit⟩ := canPlace_inr hcp
      have htopk : lastOf (st.piles k).faceUp = some z := pileOfTop_top hps
      have hpsA : (st.setFound c.suit (chop (st.found c.suit))).pileOfTop z
          = some k := by
        rw [pileOfTop_setFound]
        exact hps
      have hfeq : st'.found
          = (st.setFound c.suit (chop (st.found c.suit))).found := by
        rw [hrw]
        show (st.setFound c.suit (chop (st.found c.suit))
          |>.putCard c (Sum.inr z)).found = _
        rw [putCard_eq_inr hpsA]
        rfl
      have hpil : st'.piles
          = (st.setFound c.suit (chop (st.found c.suit))
            |>.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles := by
        rw [hrw]
        show (st.setFound c.suit (chop (st.found c.suit))
          |>.putCard c (Sum.inr z)).piles = _
        rw [putCard_eq_inr hpsA]
        rfl
      have hstock : st'.stock = st.stock := by
        rw [hrw]
        show (st.setFound c.suit (chop (st.found c.suit))
          |>.putCard c (Sum.inr z)).stock = st.stock
        rw [putCard_eq_inr hpsA]
        rfl
      have hwaste : st'.waste = st.waste := by
        rw [hrw]
        show (st.setFound c.suit (chop (st.found c.suit))
          |>.putCard c (Sum.inr z)).waste = st.waste
        rw [putCard_eq_inr hpsA]
        rfl
      have hsd' : 0 < st'.drawStep := by
        have hdeq : st'.drawStep = st.drawStep := by
          rw [hrw]
          show (st.setFound c.suit (chop (st.found c.suit))
            |>.putCard c (Sum.inr z)).drawStep = st.drawStep
          rw [putCard_eq_inr hpsA]
          rfl
        rw [hdeq]; exact hsd
      refine ⟨?_, ?_, ?_, hsd'⟩
      · intro σ
        rcases Decidable.em (σ = c.suit) with hσ | hσ
        · obtain ⟨m, hm⟩ := found_chop_prefix hpre hlast
          refine ⟨m, ?_⟩
          rw [hσ, hfeq, show (st.setFound c.suit (chop (st.found c.suit))).found c.suit
              = chop (st.found c.suit) from setFound_found_self, hm]
        · obtain ⟨n, hn⟩ := hpre σ
          refine ⟨n, ?_⟩
          rw [hfeq, setFound_found_ne hσ, hn]
      · intro j
        rcases Decidable.em (j = k) with hj | hj
        · rw [hj, show st'.piles k
              = (st.setFound c.suit (chop (st.found c.suit))
                  |>.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles k
              from by rw [hpil],
            setPile_piles_self]
          show runOK ((st.piles k).faceUp ++ ([c] : List Card)) = true
          exact runOK_append_fit (st.piles k).faceUp c z ([] : List Card)
            (hpile k) rfl htopk hfit
        · rw [show st'.piles j
              = (st.setFound c.suit (chop (st.found c.suit))
                  |>.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles j
              from by rw [hpil],
            setPile_piles_ne hj]
          exact hpile j
      · intro c₀ hc₀
        have hcc := hcard c₀ hc₀
        rw [cardCount_zones] at hcc
        rw [cardCount_zones]
        have hfdelta : cntFlat c₀ (Suit.all.map st'.found) + cnt c₀ [c]
            = cntFlat c₀ (Suit.all.map st.found) := by
          have h1 := cntFlat_map_delta c₀ st'.found st.found Suit.all
            (fun σ => if σ = c.suit then cnt c₀ [c] else 0)
            (by intro σ _
                by_cases hσ : σ = c.suit
                · rw [hσ, hfeq, setFound_found_self, ite_eq_left rfl, hR c₀]
                · rw [hfeq, setFound_found_ne hσ, ite_eq_right hσ]
                  omega)
          have h2 : (Suit.all.map (fun σ => if σ = c.suit then cnt c₀ [c] else 0)).sum
              = cnt c₀ [c] := by
            have h3 := sum_map_single Suit.all
              (fun σ => if σ = c.suit then cnt c₀ [c] else 0) c.suit
              Suit_all_nodup (Suit.mem_all c.suit)
              (by intro j _ hjc; rw [ite_eq_right hjc])
            have h4 : (if c.suit = c.suit then cnt c₀ [c] else 0) = cnt c₀ [c] := by
              rw [ite_eq_left rfl]
            rw [h3, h4]
          rw [← h1, h2]
        have hpcnt : cntFlat c₀
              (Anchor.all.map fun j => (st'.piles j).hidden ++ (st'.piles j).faceUp)
            = cntFlat c₀ (Anchor.all.map fun j => (st.piles j).hidden ++ (st.piles j).faceUp)
              + cnt c₀ [c] := by
          have h1 := cntFlat_map_delta c₀
            (fun j => (st.piles j).hidden ++ (st.piles j).faceUp)
            (fun j => ((st.setFound c.suit (chop (st.found c.suit))
                |>.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles j).hidden
              ++ ((st.setFound c.suit (chop (st.found c.suit))
                |>.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles j).faceUp)
            Anchor.all
            (fun j => if j = k then cnt c₀ [c] else 0)
            (by intro j _
                by_cases hj : j = k
                · have hgo : cnt c₀
                        (((st.setFound c.suit (chop (st.found c.suit))
                          |>.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles k).hidden
                          ++ ((st.setFound c.suit (chop (st.found c.suit))
                          |>.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles k).faceUp)
                      = cnt c₀ ((st.piles k).hidden ++ ((st.piles k).faceUp ++ [c])) := by
                    rw [setPile_piles_self]
                  rw [hj, hgo, ite_eq_left rfl, ← List.append_assoc, cnt_snoc]
                · rw [ite_eq_right hj]
                  have hident : cnt c₀ ((st.piles j).hidden ++ (st.piles j).faceUp)
                      = cnt c₀ (((st.setFound c.suit (chop (st.found c.suit))
                          |>.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles j).hidden
                        ++ ((st.setFound c.suit (chop (st.found c.suit))
                          |>.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles j).faceUp) := by
                    rw [setPile_piles_ne hj]
                    rfl
                  rw [hident]
                  omega)

          have h2 : (Anchor.all.map (fun j => if j = k then cnt c₀ [c] else 0)).sum
              = cnt c₀ [c] := by
            have h3 := sum_map_single Anchor.all
              (fun j => if j = k then cnt c₀ [c] else 0) k
              Anchor_all_nodup (Anchor.mem_all k)
              (by intro j _ hjc; rw [ite_eq_right hjc])
            have h4 : (if k = k then cnt c₀ [c] else 0) = cnt c₀ [c] := by
              rw [ite_eq_left rfl]
            rw [h3, h4]
          have hfold : cntFlat c₀
              (Anchor.all.map fun j => (st'.piles j).hidden ++ (st'.piles j).faceUp)
              = cntFlat c₀
                  (Anchor.all.map fun j => ((st.setFound c.suit (chop (st.found c.suit))
                      |>.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles j).hidden
                    ++ ((st.setFound c.suit (chop (st.found c.suit))
                      |>.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).piles j).faceUp) := by
            rw [hpil]
          rw [hfold, ← h1, h2]
        have hstockc : cnt c₀ st'.stock = cnt c₀ st.stock := by rw [hstock]
        have hwastec : cnt c₀ st'.waste = cnt c₀ st.waste := by rw [hwaste]
        omega
/-- A family's flat count is at least the count of any member's
zone. -/
private theorem cntFlat_map_ge1 {α : Type} {z : Card} (F : α → List Card) :
    ∀ (L : List α) (b : α), b ∈ L → z ∈ F b → 1 ≤ cntFlat z (L.map F) := by
  intro L
  induction L with
  | nil => intro b h; exact absurd h List.not_mem_nil
  | cons x t ih =>
      intro b hmem hz
      rw [List.map_cons, cntFlat_cons]
      rcases List.mem_cons.mp hmem with h' | h'
      · rw [h'] at hz
        have := mem_le_cnt _ hz
        omega
      · have := ih b h' hz
        omega

/-- Two distinct family members' zones hold the counted card at
least twice. -/
private theorem cntFlat_map_two_mem {α : Type} {z : Card} (F : α → List Card) :
    ∀ (L : List α) (b₁ b₂ : α), b₁ ∈ L → b₂ ∈ L → b₁ ≠ b₂ →
      z ∈ F b₁ → z ∈ F b₂ → 2 ≤ cntFlat z (L.map F) := by
  intro L
  induction L with
  | nil => intro b₁ b₂ h₁; exact absurd h₁ List.not_mem_nil
  | cons x t ih =>
      intro b₁ b₂ h₁ h₂ hne hz₁ hz₂
      rw [List.map_cons, cntFlat_cons]
      rcases List.mem_cons.mp h₁ with h₁' | h₁'
      · rw [h₁'] at hne hz₁
        rcases List.mem_cons.mp h₂ with h₂' | h₂'
        · exact absurd h₂'.symm hne
        · have e₁ : 1 ≤ cnt z (F x) := mem_le_cnt _ hz₁
          have e₂ : 1 ≤ cntFlat z (List.map F t) := cntFlat_map_ge1 F t b₂ h₂' hz₂
          omega
      · rcases List.mem_cons.mp h₂ with h₂' | h₂'
        · rw [h₂'] at hz₂
          have e₂ : 1 ≤ cnt z (F x) := mem_le_cnt _ hz₂
          have e₁ : 1 ≤ cntFlat z (List.map F t) := cntFlat_map_ge1 F t b₁ h₁' hz₁
          omega
        · have := ih b₁ b₂ h₁' h₂' hne hz₁ hz₂
          omega

/-- One occurrence per card: two pile zones cannot both hold `z`
when the global count is one. -/
private theorem two_pile_zone_absurd {st : State} {z : Card} {j k : Anchor} (hjk : j ≠ k)
    (hcc : st.cardCount z = 1)
    (hzj : z ∈ (st.piles j).hidden ++ (st.piles j).faceUp)
    (hzk : z ∈ (st.piles k).hidden ++ (st.piles k).faceUp) : False := by
  rw [cardCount_zones] at hcc
  have h2 := cntFlat_map_two_mem
    (fun a => (st.piles a).hidden ++ (st.piles a).faceUp) Anchor.all j k
    (Anchor.mem_all j) (Anchor.mem_all k) hjk hzj hzk
  omega

/-- The pile-top search is unique at `WF` states: two distinct
piles cannot both have top `z`. -/
private theorem top_search_unique {st : State} {z : Card} {j k : Anchor}
    (hcc : st.cardCount z = 1)
    (hj : st.topOf j = some z) (hk : st.topOf k = some z) : j = k := by
  by_cases hne : j = k
  · exact hne
  · exfalso
    have hzj : z ∈ (st.piles j).hidden ++ (st.piles j).faceUp :=
      List.mem_append.mpr (Or.inr (lastOf_mem' _ hj))
    have hzk : z ∈ (st.piles k).hidden ++ (st.piles k).faceUp :=
      List.mem_append.mpr (Or.inr (lastOf_mem' _ hk))
    exact two_pile_zone_absurd hne hcc hzj hzk
/-- Every card of the post-removal pile zone was already in the old
zone (the moving pile cannot re-grow a second copy of a card). -/
private theorem mem_afterRunRemoved_zone_aux : ∀ (hid fu : List Card) (x c : Card)
    (pre : List Card), pre = below c fu →
    x ∈ (Pile.afterRunRemoved ⟨hid, fu⟩ pre).hidden
      ++ (Pile.afterRunRemoved ⟨hid, fu⟩ pre).faceUp →
    x ∈ hid ++ fu
  | hid, fu, x, c, [], _ => by
      intro hz
      cases hid with
      | nil => exact absurd hz List.not_mem_nil
      | cons y t =>
          have hy : x ∈ t ++ ([y] : List Card) := hz
          rcases List.mem_append.mp hy with h' | h'
          · exact List.mem_append.mpr (Or.inl (List.mem_cons.mpr (Or.inr h')))
          · have hx : x = y := by
              rcases List.mem_cons.mp h' with hq | hq
              · exact hq
              · exact absurd hq List.not_mem_nil
            rw [hx]
            exact List.mem_append.mpr (Or.inl List.mem_cons_self)
  | hid, fu, x, c, w :: ws, heq => by
      intro hz
      have hz2 : x ∈ hid ++ (w :: ws) := hz
      rcases List.mem_append.mp hz2 with h' | h'
      · exact List.mem_append.mpr (Or.inl h')
      · exact List.mem_append.mpr
          (Or.inr (mem_below _ (heq ▸ h')))

/-- The wrapper over an opaque pile. -/
private theorem mem_afterRunRemoved_below_zone {p : Pile} {x c : Card}
    (hx : x ∈ (Pile.afterRunRemoved p (below c p.faceUp)).hidden
        ++ (Pile.afterRunRemoved p (below c p.faceUp)).faceUp) :
    x ∈ p.hidden ++ p.faceUp := by
  cases p with
  | mk hid fu =>
      exact mem_afterRunRemoved_zone_aux hid fu x c _ rfl hx

/-- The `tabToTab` move: a whole face-up run moves from its holding
pile to another base — either an empty position under a king, or a
pile whose top fits under the run's head. -/
private theorem tabToTab_wf {st st' : State} {c : Card} {b : Base}
    (hwf : st.WF) (h : State.step st (.tabToTab c b) = some st') : st'.WF := by
  obtain ⟨hpre, hpile, hcard, hsd⟩ := hwf
  obtain ⟨a, hhold, hcp, run0, hfrom, hrw⟩ := step_tabToTab_inv h
  have hmem : c ∈ (st.piles a).faceUp := pileHolding_mem hhold
  have hbelow : below c ((st.piles a).faceUp) ++ fromCard c ((st.piles a).faceUp)
      = (st.piles a).faceUp := below_fromCard c _
  obtain ⟨r, hcrr⟩ := fromCard_cons_head _ hmem
  have hrun0 : run0 = c :: r := by rw [← hfrom]; exact hcrr
  subst hrun0
  have hsplit : (st.piles a).faceUp
      = below c ((st.piles a).faceUp) ++ (c :: r) := by rw [← hcrr]; exact hbelow.symm
  have hzone : ∀ c₀, cnt c₀
        ((Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp)).hidden
          ++ (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp)).faceUp)
      + cnt c₀ (c :: r) = cnt c₀ ((st.piles a).hidden ++ (st.piles a).faceUp) :=
    fun c₀ => afterRunRemoved_zone_cnt (st.piles a) (c :: r) c₀
      (below c (st.piles a).faceUp) hsplit
  have hrok : runOK (c :: r) = true := by
    have hrunok := runOK_fromCard ((st.piles a).faceUp) c (hpile a)
    rw [hcrr] at hrunok
    exact hrunok
  have hmidne : ∀ j, j ≠ a →
      (st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles j
      = st.piles j := fun j hj => setPile_piles_ne hj
  have hmidself :
      (st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles a
      = Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp) :=
    setPile_piles_self
  cases b with
  | inl a₁ =>
      obtain ⟨hempty, _⟩ := canPlace_inl hcp
      have haa₁ : a ≠ a₁ := by
        intro heq
        subst heq
        obtain ⟨hid, hfu⟩ := pile_isEmpty hempty
        rw [hfu] at hmem
        exact absurd hmem List.not_mem_nil
      have hstp : st'.piles
          = (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))
            |>.setPile a₁ ⟨[], c :: r⟩).piles := by rw [hrw, putRun_eq_inl]
      have hfeq : st'.found = st.found := by rw [hrw, putRun_eq_inl]; rfl
      have hstock : st'.stock = st.stock := by rw [hrw, putRun_eq_inl]; rfl
      have hwaste : st'.waste = st.waste := by rw [hrw, putRun_eq_inl]; rfl
      have hsd' : 0 < st'.drawStep := by
        rw [hrw, putRun_eq_inl]; exact hsd
      refine ⟨?_, ?_, ?_, hsd'⟩
      · intro σ; rw [hfeq]; exact hpre σ
      · intro j
        rcases Decidable.em (j = a₁) with hj | hj
        · rw [hj, show st'.piles a₁
              = (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))
                  |>.setPile a₁ ⟨[], c :: r⟩).piles a₁ from by rw [hstp],
            setPile_piles_self]
          show runOK ((c :: r : List Card)) = true
          exact hrok
        · rw [show st'.piles j
              = (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))
                  |>.setPile a₁ ⟨[], c :: r⟩).piles j from by rw [hstp],
            setPile_piles_ne hj]
          rcases Decidable.em (j = a) with hj2 | hj2
          · rw [hj2, hmidself]
            cases hb : below c ((st.piles a).faceUp) with
            | nil => exact runOK_afterRunRemoved_nil (st.piles a)
            | cons y t =>
                have hrun := runOK_below ((st.piles a).faceUp) c (hpile a)
                rw [hb] at hrun
                exact hrun
          · rw [hmidne j hj2]
            exact hpile j
      · intro c₀ hc₀
        have hcc := hcard c₀ hc₀
        rw [cardCount_zones] at hcc
        rw [cardCount_zones]
        have hA : cntFlat c₀ (Anchor.all.map fun j =>
                (st.setPile a (Pile.afterRunRemoved (st.piles a)
                  (below c (st.piles a).faceUp)) |>.piles j).hidden
                  ++ (st.setPile a (Pile.afterRunRemoved (st.piles a)
                  (below c (st.piles a).faceUp)) |>.piles j).faceUp)
            + cnt c₀ (c :: r)
            = cntFlat c₀ (Anchor.all.map fun j =>
                (st.piles j).hidden ++ (st.piles j).faceUp) := by
          have h1 := cntFlat_map_delta c₀
            (fun j => (st.setPile a (Pile.afterRunRemoved (st.piles a)
                (below c (st.piles a).faceUp)) |>.piles j).hidden
              ++ (st.setPile a (Pile.afterRunRemoved (st.piles a)
                (below c (st.piles a).faceUp)) |>.piles j).faceUp)
            (fun j => (st.piles j).hidden ++ (st.piles j).faceUp)
            Anchor.all
            (fun j => if j = a then cnt c₀ (c :: r) else 0)
            (by intro j _
                by_cases hj : j = a
                · rw [hj, hmidself, ite_eq_left rfl]
                  exact hzone c₀
                · rw [hmidne j hj, ite_eq_right hj]
                  omega)
          have h2 : (Anchor.all.map
              (fun j => if j = a then cnt c₀ (c :: r) else 0)).sum
              = cnt c₀ (c :: r) := by
            have h3 := sum_map_single Anchor.all
              (fun j => if j = a then cnt c₀ (c :: r) else 0) a
              Anchor_all_nodup (Anchor.mem_all a)
              (by intro j _ hjc; rw [ite_eq_right hjc])
            have h4 : (if a = a then cnt c₀ (c :: r) else 0) = cnt c₀ (c :: r) :=
              by rw [ite_eq_left rfl]
            rw [h3, h4]
          rw [← h1, h2]
        have hB : cntFlat c₀
                (Anchor.all.map fun j => (st'.piles j).hidden ++ (st'.piles j).faceUp)
            = cntFlat c₀ (Anchor.all.map fun j =>
                (st.setPile a (Pile.afterRunRemoved (st.piles a)
                  (below c (st.piles a).faceUp)) |>.piles j).hidden
                  ++ (st.setPile a (Pile.afterRunRemoved (st.piles a)
                  (below c (st.piles a).faceUp)) |>.piles j).faceUp)
              + cnt c₀ (c :: r) := by
          have h1 := cntFlat_map_delta c₀
            (fun j => (st.setPile a (Pile.afterRunRemoved (st.piles a)
                (below c (st.piles a).faceUp)) |>.piles j).hidden
              ++ (st.setPile a (Pile.afterRunRemoved (st.piles a)
                (below c (st.piles a).faceUp)) |>.piles j).faceUp)
            (fun j => ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                (below c (st.piles a).faceUp)) |>.setPile a₁ ⟨[], c :: r⟩).piles
                j).hidden
              ++ ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                (below c (st.piles a).faceUp)) |>.setPile a₁ ⟨[], c :: r⟩).piles
                j).faceUp)
            Anchor.all
            (fun j => if j = a₁ then cnt c₀ (c :: r) else 0)
            (by intro j _
                by_cases hj : j = a₁
                · rw [hj]
                  have hgo : cnt c₀
                        (((st.setPile a (Pile.afterRunRemoved (st.piles a)
                          (below c (st.piles a).faceUp)) |>.setPile a₁ ⟨[], c :: r⟩).piles
                          a₁).hidden
                          ++ ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                          (below c (st.piles a).faceUp)) |>.setPile a₁ ⟨[], c :: r⟩).piles
                          a₁).faceUp)
                      = cnt c₀ (c :: r) := by
                    rw [setPile_piles_self]
                    show cnt c₀ (([] : List Card) ++ ((c :: r : List Card))) = _
                    rw [cnt_app, cnt_nil]
                    omega
                  have hzero : cnt c₀
                        ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                        (below c (st.piles a).faceUp)) |>.piles a₁).hidden
                        ++ (st.setPile a (Pile.afterRunRemoved (st.piles a)
                        (below c (st.piles a).faceUp)) |>.piles a₁).faceUp)
                      = 0 := by
                    have hpma₁ : (st.setPile a (Pile.afterRunRemoved (st.piles a)
                        (below c (st.piles a).faceUp))).piles a₁ = st.piles a₁ :=
                      hmidne a₁ (fun hh => haa₁ hh.symm)
                    rw [hpma₁]
                    obtain ⟨hid, hfu⟩ := pile_isEmpty hempty
                    rw [hid, hfu, cnt_app, cnt_nil]
                  rw [ite_eq_left rfl, hzero, hgo]
                  omega
                · rw [ite_eq_right hj]
                  have hident : cnt c₀
                        (((st.setPile a (Pile.afterRunRemoved (st.piles a)
                          (below c (st.piles a).faceUp))).piles j).hidden
                          ++ ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                          (below c (st.piles a).faceUp))).piles j).faceUp)
                      = cnt c₀
                        (((st.setPile a (Pile.afterRunRemoved (st.piles a)
                          (below c (st.piles a).faceUp)) |>.setPile a₁ ⟨[], c :: r⟩).piles
                          j).hidden
                          ++ ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                          (below c (st.piles a).faceUp)) |>.setPile a₁ ⟨[], c :: r⟩).piles
                          j).faceUp) := by
                    rw [show ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                        (below c (st.piles a).faceUp)) |>.setPile a₁ ⟨[], c :: r⟩).piles j)
                        = ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                        (below c (st.piles a).faceUp))).piles j)
                        from setPile_piles_ne hj]
                  rw [hident]
                  omega)
          have h2 : (Anchor.all.map
              (fun j => if j = a₁ then cnt c₀ (c :: r) else 0)).sum
              = cnt c₀ (c :: r) := by
            have h3 := sum_map_single Anchor.all
              (fun j => if j = a₁ then cnt c₀ (c :: r) else 0) a₁
              Anchor_all_nodup (Anchor.mem_all a₁)
              (by intro j _ hjc; rw [ite_eq_right hjc])
            have h4 : (if a₁ = a₁ then cnt c₀ (c :: r) else 0) = cnt c₀ (c :: r) :=
              by rw [ite_eq_left rfl]
            rw [h3, h4]
          have hfold : cntFlat c₀ (Anchor.all.map fun j =>
                (st'.piles j).hidden ++ (st'.piles j).faceUp)
              = cntFlat c₀ (Anchor.all.map fun j =>
                  ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                    (below c (st.piles a).faceUp)) |>.setPile a₁ ⟨[], c :: r⟩).piles
                    j).hidden
                  ++ ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                    (below c (st.piles a).faceUp)) |>.setPile a₁ ⟨[], c :: r⟩).piles
                    j).faceUp) := by
            rw [hstp]
          rw [hfold, ← h1, h2]
        have hfcnt : cntFlat c₀ (Suit.all.map st'.found)
            = cntFlat c₀ (Suit.all.map st.found) := by rw [hfeq]
        have hstockc : cnt c₀ st'.stock = cnt c₀ st.stock := by rw [hstock]
        have hwastec : cnt c₀ st'.waste = cnt c₀ st.waste := by rw [hwaste]
        omega
  | inr z =>
      obtain ⟨k, hps, hfit⟩ := canPlace_inr hcp
      have hkmem : st.topOf k = some z := pileOfTop_top hps
      have hzuni : z ∈ Card.universe := Card.mem_universe z
      have hccz : st.cardCount z = 1 := hcard z hzuni
      have hfitidx : c.rank.toIdx + 1 = z.rank.toIdx := (canSitOn_eq c z).mp hfit |>.1
      have hak : a ≠ k := by
        intro heq
        subst heq
        have hlast : lastOf ((st.piles a).faceUp) = some z := pileOfTop_top hps
        have hzr := lastOf_mem_fromCard ((st.piles a).faceUp) c hmem z hlast
        rw [hcrr] at hzr
        rcases List.mem_cons.mp hzr with hz | hz
        · rw [← hz] at hfitidx
          omega
        · have hlt := runOK_tail_lt r c z hrok hz
          omega
      have hpmid : (st.setPile a (Pile.afterRunRemoved (st.piles a)
            (below c (st.piles a).faceUp))).pileOfTop z = some k := by
        have hmidk : (st.setPile a (Pile.afterRunRemoved (st.piles a)
              (below c (st.piles a).faceUp))).topOf k = st.topOf k := by
          show ((st.setPile a (Pile.afterRunRemoved (st.piles a)
              (below c (st.piles a).faceUp))).piles k).top = ((st.piles k).top)
          rw [show (st.setPile a (Pile.afterRunRemoved (st.piles a)
              (below c (st.piles a).faceUp))).piles k = (st.piles k)
              from hmidne k (fun hh => hak hh.symm)]
        refine firstWhere_find (Anchor.mem_all k) ?_ ?_
        · rw [hmidk, hkmem]
          exact decide_eq_true rfl
        · intro j _ hjk
          by_cases hja : j = a
          · rw [hja]
            have hnot : (st.setPile a (Pile.afterRunRemoved (st.piles a)
                  (below c (st.piles a).faceUp))).topOf a ≠ some z := by
              intro hcon
              have hznew : z ∈ ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                    (below c (st.piles a).faceUp))).piles a).hidden
                  ++ ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                    (below c (st.piles a).faceUp))).piles a).faceUp :=
                List.mem_append.mpr (Or.inr (lastOf_mem' _ hcon))
              rw [hmidself] at hznew
              have hzold : z ∈ (st.piles a).hidden ++ (st.piles a).faceUp :=
                mem_afterRunRemoved_below_zone hznew
              have hzk : z ∈ (st.piles k).hidden ++ (st.piles k).faceUp :=
                List.mem_append.mpr (Or.inr (lastOf_mem' _ hkmem))
              exact two_pile_zone_absurd hak hccz hzold hzk
            exact decide_eq_false hnot
          · have hnot : (st.setPile a (Pile.afterRunRemoved (st.piles a)
                  (below c (st.piles a).faceUp))).topOf j ≠ some z := by
              intro hcon
              have hx := congrArg Pile.top (hmidne j hja)
              have hcon2 : (st.piles j).top = some z := by
                rw [← hx]; exact hcon
              exact hjk (top_search_unique hccz hcon2 hkmem)
            exact decide_eq_false hnot
      have hstp : st'.piles
          = (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))
            |>.setPile k { (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k with faceUp := ((st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k).faceUp ++ (c :: r) }).piles := by
        rw [hrw, putRun_eq_inr hpmid]
      have hfeq : st'.found = st.found := by rw [hrw, putRun_eq_inr hpmid]; rfl
      have hstock : st'.stock = st.stock := by rw [hrw, putRun_eq_inr hpmid]; rfl
      have hwaste : st'.waste = st.waste := by rw [hrw, putRun_eq_inr hpmid]; rfl
      have hsd' : 0 < st'.drawStep := by
        rw [hrw, putRun_eq_inr hpmid]; exact hsd
      refine ⟨?_, ?_, ?_, hsd'⟩
      · intro σ; rw [hfeq]; exact hpre σ
      · intro j
        rcases Decidable.em (j = k) with hj | hj
        · rw [hj, show st'.piles k
              = (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))
                  |>.setPile k { (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k with faceUp := ((st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k).faceUp ++ (c :: r) }).piles k
              from by rw [hstp],
            setPile_piles_self, hmidne k (fun hh => hak hh.symm)]
          show runOK (((st.piles k).faceUp) ++ (c :: r)) = true
          exact runOK_append_fit ((st.piles k).faceUp) c z r
            (hpile k) hrok hkmem hfit
        · rw [show st'.piles j
              = (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))
                  |>.setPile k { (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k with faceUp := ((st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k).faceUp ++ (c :: r) }).piles j
              from by rw [hstp],
            setPile_piles_ne hj]
          rcases Decidable.em (j = a) with hj2 | hj2
          · rw [hj2, hmidself]
            cases hb : below c ((st.piles a).faceUp) with
            | nil => exact runOK_afterRunRemoved_nil (st.piles a)
            | cons y t =>
                have hrun := runOK_below ((st.piles a).faceUp) c (hpile a)
                rw [hb] at hrun
                exact hrun
          · rw [hmidne j hj2]
            exact hpile j
      · intro c₀ hc₀
        have hcc := hcard c₀ hc₀
        rw [cardCount_zones] at hcc
        rw [cardCount_zones]
        have hA : cntFlat c₀ (Anchor.all.map fun j =>
                (st.setPile a (Pile.afterRunRemoved (st.piles a)
                  (below c (st.piles a).faceUp)) |>.piles j).hidden
                  ++ (st.setPile a (Pile.afterRunRemoved (st.piles a)
                  (below c (st.piles a).faceUp)) |>.piles j).faceUp)
            + cnt c₀ (c :: r)
            = cntFlat c₀ (Anchor.all.map fun j =>
                (st.piles j).hidden ++ (st.piles j).faceUp) := by
          have h1 := cntFlat_map_delta c₀
            (fun j => (st.setPile a (Pile.afterRunRemoved (st.piles a)
                (below c (st.piles a).faceUp)) |>.piles j).hidden
              ++ (st.setPile a (Pile.afterRunRemoved (st.piles a)
                (below c (st.piles a).faceUp)) |>.piles j).faceUp)
            (fun j => (st.piles j).hidden ++ (st.piles j).faceUp)
            Anchor.all
            (fun j => if j = a then cnt c₀ (c :: r) else 0)
            (by intro j _
                by_cases hj : j = a
                · rw [hj, hmidself, ite_eq_left rfl]
                  exact hzone c₀
                · rw [hmidne j hj, ite_eq_right hj]
                  omega)
          have h2 : (Anchor.all.map
              (fun j => if j = a then cnt c₀ (c :: r) else 0)).sum
              = cnt c₀ (c :: r) := by
            have h3 := sum_map_single Anchor.all
              (fun j => if j = a then cnt c₀ (c :: r) else 0) a
              Anchor_all_nodup (Anchor.mem_all a)
              (by intro j _ hjc; rw [ite_eq_right hjc])
            have h4 : (if a = a then cnt c₀ (c :: r) else 0) = cnt c₀ (c :: r) :=
              by rw [ite_eq_left rfl]
            rw [h3, h4]
          rw [← h1, h2]
        have hB : cntFlat c₀
                (Anchor.all.map fun j => (st'.piles j).hidden ++ (st'.piles j).faceUp)
            = cntFlat c₀ (Anchor.all.map fun j =>
                (st.setPile a (Pile.afterRunRemoved (st.piles a)
                  (below c (st.piles a).faceUp)) |>.piles j).hidden
                  ++ (st.setPile a (Pile.afterRunRemoved (st.piles a)
                  (below c (st.piles a).faceUp)) |>.piles j).faceUp)
              + cnt c₀ (c :: r) := by
          have h1 := cntFlat_map_delta c₀
            (fun j => (st.setPile a (Pile.afterRunRemoved (st.piles a)
                (below c (st.piles a).faceUp)) |>.piles j).hidden
              ++ (st.setPile a (Pile.afterRunRemoved (st.piles a)
                (below c (st.piles a).faceUp)) |>.piles j).faceUp)
            (fun j => ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                (below c (st.piles a).faceUp)) |>.setPile k
                { (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k with faceUp := ((st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k).faceUp ++ (c :: r) }).piles
                j).hidden
              ++ ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                (below c (st.piles a).faceUp)) |>.setPile k
                { (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k with faceUp := ((st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k).faceUp ++ (c :: r) }).piles
                j).faceUp)
            Anchor.all
            (fun j => if j = k then cnt c₀ (c :: r) else 0)
            (by intro j _
                by_cases hj : j = k
                · have hgo : cnt c₀
                        (((st.setPile a (Pile.afterRunRemoved (st.piles a)
                          (below c (st.piles a).faceUp)) |>.setPile k
                          { (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k with faceUp := ((st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k).faceUp ++ (c :: r) }).piles
                          k).hidden
                          ++ ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                          (below c (st.piles a).faceUp)) |>.setPile k
                          { (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k with faceUp := ((st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k).faceUp ++ (c :: r) }).piles
                          k).faceUp)
                      = cnt c₀
                        (((st.setPile a (Pile.afterRunRemoved (st.piles a)
                          (below c (st.piles a).faceUp))).piles k).hidden
                          ++ (((st.setPile a (Pile.afterRunRemoved (st.piles a)
                          (below c (st.piles a).faceUp))).piles k).faceUp ++ (c :: r))) := by
                    rw [setPile_piles_self]
                  rw [hj, hgo, ite_eq_left rfl, hmidne k (fun hh => hak hh.symm),
                    ← List.append_assoc, cnt_app, cnt_app, cnt_app]
                · rw [ite_eq_right hj]
                  have hident : cnt c₀
                        (((st.setPile a (Pile.afterRunRemoved (st.piles a)
                          (below c (st.piles a).faceUp))).piles j).hidden
                          ++ ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                          (below c (st.piles a).faceUp))).piles j).faceUp)
                      = cnt c₀
                        (((st.setPile a (Pile.afterRunRemoved (st.piles a)
                          (below c (st.piles a).faceUp)) |>.setPile k
                          { (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k with faceUp := ((st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k).faceUp ++ (c :: r) }).piles
                          j).hidden
                          ++ ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                          (below c (st.piles a).faceUp)) |>.setPile k
                          { (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k with faceUp := ((st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k).faceUp ++ (c :: r) }).piles
                          j).faceUp) := by
                    rw [show ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                        (below c (st.piles a).faceUp)) |>.setPile k
                        { (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k with faceUp := ((st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k).faceUp ++ (c :: r) }).piles j)
                        = ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                        (below c (st.piles a).faceUp))).piles j)
                        from setPile_piles_ne hj]
                  rw [hident]
                  omega)
          have h2 : (Anchor.all.map
              (fun j => if j = k then cnt c₀ (c :: r) else 0)).sum
              = cnt c₀ (c :: r) := by
            have h3 := sum_map_single Anchor.all
              (fun j => if j = k then cnt c₀ (c :: r) else 0) k
              Anchor_all_nodup (Anchor.mem_all k)
              (by intro j _ hjc; rw [ite_eq_right hjc])
            have h4 : (if k = k then cnt c₀ (c :: r) else 0) = cnt c₀ (c :: r) :=
              by rw [ite_eq_left rfl]
            rw [h3, h4]
          have hfold : cntFlat c₀ (Anchor.all.map fun j =>
                (st'.piles j).hidden ++ (st'.piles j).faceUp)
              = cntFlat c₀ (Anchor.all.map fun j =>
                  ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                    (below c (st.piles a).faceUp)) |>.setPile k
                    { (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k with faceUp := ((st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k).faceUp ++ (c :: r) }).piles
                    j).hidden
                  ++ ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                    (below c (st.piles a).faceUp)) |>.setPile k
                    { (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k with faceUp := ((st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k).faceUp ++ (c :: r) }).piles
                    j).faceUp) := by
            rw [hstp]
          rw [hfold, ← h1, h2]
        have hfcnt : cntFlat c₀ (Suit.all.map st'.found)
            = cntFlat c₀ (Suit.all.map st.found) := by rw [hfeq]
        have hstockc : cnt c₀ st'.stock = cnt c₀ st.stock := by rw [hstock]
        have hwastec : cnt c₀ st'.waste = cnt c₀ st.waste := by rw [hwaste]
        omega

/-! ## The conservation fence -/

theorem step_wf {st st' : State} {m : Move} (hwf : st.WF)
    (h : State.step st m = some st') : st'.WF := by
  cases m with
  | draw => exact draw_wf hwf h
  | wasteToFound c => exact wasteToFound_wf hwf h
  | wasteToTab c b => exact wasteToTab_wf hwf h
  | tabToFound c => exact tabToFound_wf hwf h
  | foundToTab c b => exact foundToTab_wf hwf h
  | tabToTab c b => exact tabToTab_wf hwf h

/-- The reachable⇒WF fence: every state reachable from a dealt game
is well-formed — the conservation invariant, the foundation prefix
discipline, and the draw-step clause all hold along every legal
play. -/
theorem initialReachable_wf {st : State} (h : initialReachable st) : st.WF :=
  invariant_of_initialReachable (I := State.WF)
    (fun d s hdw hs => initial_wf d s hdw hs)
    (fun _ _ _ hs hwf => step_wf hwf hs) st h

theorem initialReachable_runOK {st : State} (h : initialReachable st) (a : Anchor) :
    runOK (st.piles a).faceUp = true := (initialReachable_wf h).2.1 a

theorem initialReachable_cardCount {st : State} (h : initialReachable st)
    (c : Card) (hc : c ∈ Card.universe) :
    st.cardCount c = 1 := (initialReachable_wf h).2.2.1 c hc

theorem initialReachable_drawStep {st : State} (h : initialReachable st) :
    0 < st.drawStep := (initialReachable_wf h).2.2.2
