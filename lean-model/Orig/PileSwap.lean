import Orig.Reach
import Orig.Fate

/-!
# Orig — the pile transposition (the position symmetry, Orig's own)

`Orig/TwinExchangeBoth.lean` exchanges *cargo* (twin hosts' riding
suffixes, anchors fixed); this file is the position analogue: the
transposition of whole piles.  In Orig, `Pile = {hidden, faceUp}`
lives at the anchor — the macro model's deal/board split (the slates
that blocked Klondike's pile swap at `Deal.WF`) does not exist at
this layer, so a pile transposition is one record field and the
symmetry carries the whole state, `State.WF` included.

The family (the wave-24 infrastructure card A):

* §1 `Anchor.swap i j`, `Base.swapBase` — the index action and the
  base re-anchoring (anchor seats re-anchor, card seats ride along),
  with the involutivity kit.
* §2 `State.swapPiles i j` — the piles field composed with
  `Anchor.swap` (found/stock/waste/drawStep fixed), and the move
  co-action `Move.swapM i j` (the base-carrying kinds —
  `wasteToTab`/`foundToTab`/`tabToTab` — re-anchor their bases;
  `draw`/`wasteToFound`/`tabToFound` are fixed points).
* §3 the reader conjugations — piles/topOf/isEmpty by rfl; the
  `firstWhere` searches (`pileOfTop`, `pileHolding`) by
  permutation-covariance, exact only at `State.WF` (the searches
  are order-sensitive; WF supplies unique tops/holders through
  `Orig.Integrity`); hence `canPlace`, `setPile`, `putCard`,
  `putRun` conjugate (the searches' rows carry the WF premise).
* §4 `step_swapPiles` — `step (swapPiles st) (swapM m)` is
  `(step st m).map swapPiles` in both `Option` directions, per move
  kind at WF; `legal_swapPiles` the legality shadow.  The draw arm
  rides the `stepDraw` conjugation, the placement arms the reader
  rows, in the `State.twin_step` house style (`Orig/Twin.lean`).
* §6 (before §5: the lift's reverse leg needs it) `wf_swapPiles_iff`
  — **the Orig-only upgrade**: the conservation clauses literally
  permute (the card-count block rides `List.Perm` through the
  flatMap/filter/length chain), so WF transfers in both directions —
  provable right where Klondike's `swapPiles_dealWF_blocked` stood.
* §5 the lift: `run_swapPiles` (WF threaded by `Orig.Reach.step_wf`),
  `WinFrom_swapPiles_iff` (both directions by involutivity; `isWin`
  reads `found` only).

Deliberately NOT ported from `Klondike/PileSwap.lean`: its §6 (the
`depthsZero` deal-inertness) and §7 (the same-deal obstruction) —
deal bookkeeping does not exist at the Orig layer.

Dedup note (the wave-24 sweep, documentation-only): the private
`swapAnch` + `_left`/`_right`/`_ne` kit in `Orig/TwinExchangeBoth.lean`
is the same transposition function carried privately for
cargo-exchange bookkeeping (`exch_topOf_swap` and
`exch_pileOfTop_swap` there are cargo-exchange rows — anchors
stable, contents moving — with position-shaped conclusions; they are
NOT absorbed here).  The private kit could cite this public one at
the harvest; recorded in the wave-24 FARM block, the sibling file
not touched.
-/

/-! ## §1. The index transposition and its base action -/

/-- The anchor transposition: `i ↔ j`, every other pile fixed. -/
def Anchor.swap (i j : Anchor) : Anchor → Anchor :=
  fun a => if a = i then j else if a = j then i else a

theorem Anchor.swap_self_left (i j : Anchor) : Anchor.swap i j i = j := by
  show (if (i : Anchor) = i then j else _) = j
  rw [if_pos rfl]

theorem Anchor.swap_self_right (i j : Anchor) : Anchor.swap i j j = i := by
  unfold Anchor.swap
  by_cases hij : j = i
  · rw [if_pos hij]
    exact hij
  · rw [if_neg hij, if_pos rfl]

theorem Anchor.swap_eq_self (i j : Anchor) {a : Anchor}
    (h1 : a ≠ i) (h2 : a ≠ j) : Anchor.swap i j a = a := by
  unfold Anchor.swap
  rw [if_neg h1, if_neg h2]

/-- The two-arm involution: swapping twice is the identity. -/
theorem Anchor.swap_swap (i j : Anchor) (a : Anchor) :
    Anchor.swap i j (Anchor.swap i j a) = a := by
  by_cases hai : a = i
  · rw [hai, Anchor.swap_self_left, Anchor.swap_self_right]
  · by_cases haj : a = j
    · rw [haj, Anchor.swap_self_right, Anchor.swap_self_left]
    · rw [Anchor.swap_eq_self _ _ hai haj, Anchor.swap_eq_self _ _ hai haj]

/-- The degenerate transposition is the identity. -/
theorem Anchor.swap_refl (i : Anchor) (a : Anchor) :
    Anchor.swap i i a = a := by
  unfold Anchor.swap
  by_cases hai : a = i
  · rw [if_pos hai, hai]
  · rw [if_neg hai, if_neg hai]

/-- The cross-order involution: `i↔j` then `j↔i` is the identity. -/
theorem Anchor.swap_rev (i j : Anchor) (x : Anchor) :
    Anchor.swap j i (Anchor.swap i j x) = x := by
  by_cases hxi : x = i
  · rw [hxi, Anchor.swap_self_left, Anchor.swap_self_left]
  · by_cases hxj : x = j
    · rw [hxj, Anchor.swap_self_right, Anchor.swap_self_right]
    · rw [Anchor.swap_eq_self i j hxi hxj, Anchor.swap_eq_self j i hxj hxi]

/-- Injectivity of the transposition (via the involution). -/
theorem Anchor.swap_inj (i j : Anchor) {a b : Anchor}
    (h : Anchor.swap i j a = Anchor.swap i j b) : a = b := by
  have h2 := congrArg (Anchor.swap i j) h
  rw [Anchor.swap_swap, Anchor.swap_swap] at h2
  exact h2

/-- The base action: anchor seats re-anchor, card seats ride along. -/
def Base.swapBase (b : Base) (i j : Anchor) : Base :=
  Sum.map (Anchor.swap i j) id b

theorem Base.swapBase_inl (i j : Anchor) (a : Anchor) :
    Base.swapBase (Sum.inl a) i j = Sum.inl (Anchor.swap i j a) := rfl

theorem Base.swapBase_inr (i j : Anchor) (c : Card) :
    Base.swapBase (Sum.inr c) i j = Sum.inr c := rfl

theorem Base.swapBase_swapBase (b : Base) (i j : Anchor) :
    (b.swapBase i j).swapBase i j = b := by
  cases b with
  | inl a => rw [Base.swapBase_inl, Base.swapBase_inl, Anchor.swap_swap]
  | inr c => rfl

/-- Injectivity of the base action (via the involution). -/
theorem Base.swapBase_inj (_b : Base) (i j : Anchor) {b₁ b₂ : Base}
    (h : b₁.swapBase i j = b₂.swapBase i j) : b₁ = b₂ := by
  have h2 := congrArg (fun x : Base => x.swapBase i j) h
  rw [Base.swapBase_swapBase, Base.swapBase_swapBase] at h2
  exact h2

theorem Base.swapBase_rev (b : Base) (i j : Anchor) :
    (b.swapBase i j).swapBase j i = b := by
  cases b with
  | inl a => rw [Base.swapBase_inl, Base.swapBase_inl, Anchor.swap_rev]
  | inr c => rfl

/-! ## §2. The state action and the move co-action -/

/-- The pile transposition on states: the two piles' contents
(hidden stack included) exchange seats; the foundations, the stock,
the waste and the draw step stay fixed. -/
def State.swapPiles (st : State) (i j : Anchor) : State :=
  { st with piles := fun a => st.piles (Anchor.swap i j a) }

theorem State.swapPiles_piles (st : State) (i j : Anchor) (a : Anchor) :
    (st.swapPiles i j).piles a = st.piles (Anchor.swap i j a) := rfl

/-- The reader that sees through the involution. -/
@[simp] theorem State.swapPiles_piles_self (st : State) (i j : Anchor) (a : Anchor) :
    (st.swapPiles i j).piles (Anchor.swap i j a) = st.piles a := by
  show st.piles (Anchor.swap i j (Anchor.swap i j a)) = st.piles a
  rw [Anchor.swap_swap]

theorem State.swapPiles_swapPiles (st : State) (i j : Anchor) :
    (st.swapPiles i j).swapPiles i j = st := by
  refine State.ext rfl (funext (fun a => ?_)) rfl rfl rfl
  show st.piles (Anchor.swap i j (Anchor.swap i j a)) = st.piles a
  rw [Anchor.swap_swap]

/-- The degenerate transposition is the identity on states. -/
theorem State.swapPiles_self (st : State) (i : Anchor) :
    st.swapPiles i i = st := by
  refine State.ext rfl (funext (fun a => ?_)) rfl rfl rfl
  show st.piles (Anchor.swap i i a) = st.piles a
  rw [Anchor.swap_refl]

@[simp] theorem State.swapPiles_found (st : State) (i j : Anchor) :
    (st.swapPiles i j).found = st.found := rfl

@[simp] theorem State.swapPiles_found_apply (st : State) (i j : Anchor) (s : Suit) :
    (st.swapPiles i j).found s = st.found s := rfl

@[simp] theorem State.swapPiles_stock (st : State) (i j : Anchor) :
    (st.swapPiles i j).stock = st.stock := rfl

@[simp] theorem State.swapPiles_waste (st : State) (i j : Anchor) :
    (st.swapPiles i j).waste = st.waste := rfl

@[simp] theorem State.swapPiles_drawStep (st : State) (i j : Anchor) :
    (st.swapPiles i j).drawStep = st.drawStep := rfl

@[simp] theorem State.swapPiles_wasteIs (st : State) (i j : Anchor) (c : Card) :
    (st.swapPiles i j).wasteIs c = st.wasteIs c := rfl

@[simp] theorem State.swapPiles_nextUp (st : State) (i j : Anchor) (c : Card) :
    (st.swapPiles i j).nextUp c = st.nextUp c := rfl

@[simp] theorem State.swapPiles_foundTop (st : State) (i j : Anchor) (s : Suit) :
    (st.swapPiles i j).foundTop s = st.foundTop s := rfl

theorem State.swapPiles_isWin (st : State) (i j : Anchor) :
    (st.swapPiles i j).isWin = st.isWin := rfl

/-- Non-pile updates commute with the transposition (the fieldwise
`rfl` behind every draw-arm assembly). -/
theorem State.swapPiles_with (st : State) (i j : Anchor) (X Y : List Card) :
    { st with stock := X, waste := Y }.swapPiles i j
      = { st.swapPiles i j with stock := X, waste := Y } := rfl

/-- The move co-action: a landing's base re-anchors; the base-free
kinds (`draw`, `wasteToFound`, `tabToFound`) are fixed points. -/
def Move.swapM (i j : Anchor) : Move → Move
  | .draw => .draw
  | .wasteToFound c => .wasteToFound c
  | .wasteToTab c b => .wasteToTab c (b.swapBase i j)
  | .tabToFound c => .tabToFound c
  | .foundToTab c b => .foundToTab c (b.swapBase i j)
  | .tabToTab c b => .tabToTab c (b.swapBase i j)

theorem Move.swapM_swapM (i j : Anchor) (m : Move) :
    Move.swapM i j (Move.swapM i j m) = m := by
  cases m with
  | draw => rfl
  | wasteToFound c => rfl
  | wasteToTab c b =>
      show Move.wasteToTab c ((b.swapBase i j).swapBase i j) = _
      rw [Base.swapBase_swapBase]
  | tabToFound c => rfl
  | foundToTab c b =>
      show Move.foundToTab c ((b.swapBase i j).swapBase i j) = _
      rw [Base.swapBase_swapBase]
  | tabToTab c b =>
      show Move.tabToTab c ((b.swapBase i j).swapBase i j) = _
      rw [Base.swapBase_swapBase]

/-! ## §3. The reader conjugations

The `firstWhere` searches are order-sensitive, so their conjugation
is licensed by `State.WF` (through `Orig.Integrity`'s uniqueness
rows: at a WF state a given top/holder is unique, so the search's
answer permutes with the piles). -/

/-- The top search conjugates: the answer re-anchors. -/
theorem State.pileOfTop_swapPiles {st : State} {i j : Anchor} (hwf : st.WF)
    (z : Card) :
    (st.swapPiles i j).pileOfTop z
      = (st.pileOfTop z).map (Anchor.swap i j) := by
  have hsome : ∀ {k : Anchor}, st.pileOfTop z = some k →
      (st.swapPiles i j).pileOfTop z = some (Anchor.swap i j k) := by
    intro k h
    show firstWhere (fun a => decide ((st.swapPiles i j).topOf a = some z)) Anchor.all = _
    rw [firstWhere_congr
      (fun (a : Anchor) => show decide ((st.swapPiles i j).topOf a = some z)
        = decide (st.topOf (Anchor.swap i j a) = some z) from rfl)]
    refine firstWhere_find (Anchor.mem_all _)
      (show decide (st.topOf (Anchor.swap i j (Anchor.swap i j k)) = some z) = true from by
        rw [Anchor.swap_swap, decide_eq_true_eq]
        exact pileOfTop_eq_some_iff hwf |>.mp h)
      (fun y _hy hyne => by
        by_cases htor : st.topOf (Anchor.swap i j y) = some z
        · exfalso
          have hs2 := (pileOfTop_eq_some_iff (a := Anchor.swap i j y) hwf).mpr htor
          have hyk := pileOfTop_inj h hs2
          apply hyne
          have h3 := congrArg (Anchor.swap i j) hyk
          rw [Anchor.swap_swap] at h3
          exact h3.symm
        · show decide (st.topOf (Anchor.swap i j y) = some z) = false
          rw [decide_eq_false_iff_not]
          exact htor)
  have hnone : st.pileOfTop z = none →
      (st.swapPiles i j).pileOfTop z = none := by
    intro h
    cases hσ : (st.swapPiles i j).pileOfTop z with
    | none => rfl
    | some y =>
        have hnd : st.topOf (Anchor.swap i j y) = some z :=
          of_decide_eq_true
            (firstWhere_sound (fun a => decide ((st.swapPiles i j).topOf a = some z)) hσ)
        have hs2 := (pileOfTop_eq_some_iff (a := Anchor.swap i j y) hwf).mpr hnd
        rw [h] at hs2
        exact absurd hs2 (by simp)
  cases h : st.pileOfTop z with
  | none => rw [hnone h, Option.map_none]
  | some k => rw [hsome h, Option.map_some]

/-- The holding search conjugates: the answer re-anchors. -/
theorem State.pileHolding_swapPiles {st : State} {i j : Anchor} (hwf : st.WF)
    (c : Card) :
    (st.swapPiles i j).pileHolding c
      = (st.pileHolding c).map (Anchor.swap i j) := by
  have hsome : ∀ {k : Anchor}, st.pileHolding c = some k →
      (st.swapPiles i j).pileHolding c = some (Anchor.swap i j k) := by
    intro k h
    show firstWhere (fun a => decide (c ∈ ((st.swapPiles i j).piles a).faceUp)) Anchor.all = _
    rw [firstWhere_congr
      (fun (a : Anchor) => show decide (c ∈ ((st.swapPiles i j).piles a).faceUp)
        = decide (c ∈ (st.piles (Anchor.swap i j a)).faceUp) from rfl)]
    refine firstWhere_find (Anchor.mem_all _)
      (show decide (c ∈ (st.piles (Anchor.swap i j (Anchor.swap i j k))).faceUp) = true from by
        rw [Anchor.swap_swap, decide_eq_true_eq]
        exact pileHolding_eq_some_iff hwf |>.mp h)
      (fun y _hy hyne => by
        by_cases htor : c ∈ (st.piles (Anchor.swap i j y)).faceUp
        · exfalso
          have hs2 := (pileHolding_eq_some_iff (a := Anchor.swap i j y) hwf).mpr htor
          have hyk := pileHolding_inj h hs2
          apply hyne
          have h3 := congrArg (Anchor.swap i j) hyk
          rw [Anchor.swap_swap] at h3
          exact h3.symm
        · show decide (c ∈ (st.piles (Anchor.swap i j y)).faceUp) = false
          rw [decide_eq_false_iff_not]
          exact htor)
  have hnone : st.pileHolding c = none →
      (st.swapPiles i j).pileHolding c = none := by
    intro h
    cases hσ : (st.swapPiles i j).pileHolding c with
    | none => rfl
    | some y =>
        have hnd : c ∈ (st.piles (Anchor.swap i j y)).faceUp :=
          of_decide_eq_true
            (firstWhere_sound (fun a => decide (c ∈ ((st.swapPiles i j).piles a).faceUp)) hσ)
        have hs2 := (pileHolding_eq_some_iff (a := Anchor.swap i j y) hwf).mpr hnd
        rw [h] at hs2
        exact absurd hs2 (by simp)
  cases h : st.pileHolding c with
  | none => rw [hnone h, Option.map_none]
  | some k => rw [hsome h, Option.map_some]
theorem State.swapPiles_topOf (st : State) (i j : Anchor) (a : Anchor) :
    (st.swapPiles i j).topOf a = st.topOf (Anchor.swap i j a) := rfl

theorem State.swapPiles_pile_isEmpty (st : State) (i j : Anchor) (a : Anchor) :
    ((st.swapPiles i j).piles a).isEmpty
      = (st.piles (Anchor.swap i j a)).isEmpty := rfl

/-- The placement guard conjugates: guard the swapped base at the
unswapped state. -/
theorem State.canPlace_swapPiles {st : State} {i j : Anchor} (hwf : st.WF)
    (c : Card) (b : Base) :
    (st.swapPiles i j).canPlace c b = st.canPlace c (b.swapBase i j) := by
  cases b with
  | inl a => rfl
  | inr z =>
      show (match (st.swapPiles i j).pileOfTop z with
        | some _ => canSitOn c z
        | none => false)
        = (match st.pileOfTop z with
          | some _ => canSitOn c z
          | none => false)
      rw [State.pileOfTop_swapPiles hwf z]
      cases h : st.pileOfTop z with
      | none => rfl
      | some k => rfl

/-- The pile writer conjugates: writing pile `a` after the swap is
writing the swapped pile before it, then swapping. -/
theorem State.setPile_swapPiles (st : State) (i j : Anchor) (a : Anchor)
    (p : Pile) :
    (st.swapPiles i j).setPile a p
      = (st.setPile (Anchor.swap i j a) p).swapPiles i j := by
  refine State.ext rfl (funext (fun x => ?_)) rfl rfl rfl
  show (if x = a then p else st.piles (Anchor.swap i j x))
    = (if Anchor.swap i j x = Anchor.swap i j a then p
        else st.piles (Anchor.swap i j x))
  by_cases hxa : x = a
  · have hsa : Anchor.swap i j x = Anchor.swap i j a := congrArg _ hxa
    rw [if_pos hxa, if_pos hsa]
  · have hne : Anchor.swap i j x ≠ Anchor.swap i j a := by
      intro hcon
      have h3 := congrArg (Anchor.swap i j) hcon
      rw [Anchor.swap_swap, Anchor.swap_swap] at h3
      exact hxa h3
    rw [if_neg hxa, if_neg hne]

/-- The top search only reads piles: pile-equal states answer
alike. -/
theorem State.pileOfTop_congr_piles {S T : State}
    (h : ∀ a, S.piles a = T.piles a) (z : Card) :
    S.pileOfTop z = T.pileOfTop z := by
  show (firstWhere (fun a => decide (S.topOf a = some z)) Anchor.all) =
    (firstWhere (fun a => decide (T.topOf a = some z)) Anchor.all)
  rw [firstWhere_congr (fun (a : Anchor) =>
    show decide (S.topOf a = some z) = decide (T.topOf a = some z) from by
      show decide ((S.piles a).top = some z) = decide ((T.piles a).top = some z)
      rw [h a])]

/-- The run placement conjugates, given the located-reader
conjugation for the state at hand (the single-card case is
`putCard_swapPiles'`; this is the inr seat with the located answer
supplied directly). -/
theorem State.putRun_swapPiles'_inr {S : State} {i j : Anchor} {z : Card}
    (hpt : (S.swapPiles i j).pileOfTop z
      = (S.pileOfTop z).map (Anchor.swap i j))
    (run : List Card) :
    (S.swapPiles i j).putRun run (Sum.inr z)
      = (S.putRun run (Sum.inr z)).swapPiles i j := by
  show (match (S.swapPiles i j).pileOfTop z with
    | some k => (S.swapPiles i j).setPile k
        { (S.swapPiles i j).piles k with
            faceUp := ((S.swapPiles i j).piles k).faceUp ++ run }
    | none => S.swapPiles i j)
    = ((match S.pileOfTop z with
        | some k => S.setPile k
            { S.piles k with faceUp := (S.piles k).faceUp ++ run }
        | none => S).swapPiles i j)
  rw [hpt]
  cases h : S.pileOfTop z with
  | none => rfl
  | some k =>
      rw [Option.map_some]
      show (S.swapPiles i j).setPile (Anchor.swap i j k)
          { (S.swapPiles i j).piles (Anchor.swap i j k) with
              faceUp := ((S.swapPiles i j).piles (Anchor.swap i j k)).faceUp ++ run }
        = (S.setPile k
            { S.piles k with faceUp := (S.piles k).faceUp ++ run }).swapPiles i j
      rw [State.swapPiles_piles_self S i j k]
      rw [State.setPile_swapPiles]
      rw [Anchor.swap_swap]

/-- The single-card placement conjugates, given the located-reader
conjugation for the state at hand (the post-writer states are not
WF, so the WF route is suspended). -/
theorem State.putCard_swapPiles' {S : State} {i j : Anchor}
    (hpt : ∀ z, (S.swapPiles i j).pileOfTop z
      = (S.pileOfTop z).map (Anchor.swap i j))
    (c : Card) (b : Base) :
    (S.swapPiles i j).putCard c b
      = (S.putCard c (b.swapBase i j)).swapPiles i j := by
  cases b with
  | inl a => exact State.setPile_swapPiles S i j a ⟨[], [c]⟩
  | inr z =>
      have hptz := hpt z
      show (match (S.swapPiles i j).pileOfTop z with
        | some k => (S.swapPiles i j).setPile k
            { (S.swapPiles i j).piles k with
                faceUp := ((S.swapPiles i j).piles k).faceUp ++ [c] }
        | none => S.swapPiles i j)
        = ((match S.pileOfTop z with
            | some k => S.setPile k
                { S.piles k with faceUp := (S.piles k).faceUp ++ [c] }
            | none => S).swapPiles i j)
      rw [hptz]
      cases h : S.pileOfTop z with
      | none => rfl
      | some k =>
          rw [Option.map_some]
          show (S.swapPiles i j).setPile (Anchor.swap i j k)
              { (S.swapPiles i j).piles (Anchor.swap i j k) with
                  faceUp := ((S.swapPiles i j).piles (Anchor.swap i j k)).faceUp ++ [c] }
            = (S.setPile k
                { S.piles k with faceUp := (S.piles k).faceUp ++ [c] }).swapPiles i j
          rw [State.swapPiles_piles_self S i j k]
          rw [State.setPile_swapPiles]
          rw [Anchor.swap_swap]

/-- The run placement conjugates, given the located-reader
conjugation for the state at hand. -/
theorem State.putRun_swapPiles' {S : State} {i j : Anchor}
    (hpt : ∀ z, (S.swapPiles i j).pileOfTop z
      = (S.pileOfTop z).map (Anchor.swap i j))
    (run : List Card) (b : Base) :
    (S.swapPiles i j).putRun run b
      = (S.putRun run (b.swapBase i j)).swapPiles i j := by
  cases b with
  | inl a => exact State.setPile_swapPiles S i j a ⟨[], run⟩
  | inr z =>
      have hptz := hpt z
      show (match (S.swapPiles i j).pileOfTop z with
        | some k => (S.swapPiles i j).setPile k
            { (S.swapPiles i j).piles k with
                faceUp := ((S.swapPiles i j).piles k).faceUp ++ run }
        | none => S.swapPiles i j)
        = ((match S.pileOfTop z with
            | some k => S.setPile k
                { S.piles k with faceUp := (S.piles k).faceUp ++ run }
            | none => S).swapPiles i j)
      rw [hptz]
      cases h : S.pileOfTop z with
      | none => rfl
      | some k =>
          rw [Option.map_some]
          show (S.swapPiles i j).setPile (Anchor.swap i j k)
              { (S.swapPiles i j).piles (Anchor.swap i j k) with
                  faceUp := ((S.swapPiles i j).piles (Anchor.swap i j k)).faceUp ++ run }
            = (S.setPile k
                { S.piles k with faceUp := (S.piles k).faceUp ++ run }).swapPiles i j
          rw [State.swapPiles_piles_self S i j k]
          rw [State.setPile_swapPiles]
          rw [Anchor.swap_swap]



/-- The foundation writer conjugates (found is untouched by the
swap, so the writers commute fieldwise). -/
theorem State.setFound_swapPiles (st : State) (i j : Anchor) (s : Suit)
    (l : List Card) :
    (st.swapPiles i j).setFound s l
      = (st.setFound s l).swapPiles i j := rfl

/-- The single-card placement conjugates. -/
theorem State.putCard_swapPiles {st : State} {i j : Anchor} (hwf : st.WF)
    (c : Card) (b : Base) :
    (st.swapPiles i j).putCard c b
      = (st.putCard c (b.swapBase i j)).swapPiles i j := by
  cases b with
  | inl a => exact State.setPile_swapPiles st i j a ⟨[], [c]⟩
  | inr z =>
      have hpt : (st.swapPiles i j).pileOfTop z
          = (st.pileOfTop z).map (Anchor.swap i j) :=
        State.pileOfTop_swapPiles hwf z
      show (match (st.swapPiles i j).pileOfTop z with
        | some k => (st.swapPiles i j).setPile k
            { (st.swapPiles i j).piles k with
                faceUp := ((st.swapPiles i j).piles k).faceUp ++ [c] }
        | none => st.swapPiles i j)
        = ((match st.pileOfTop z with
            | some k => st.setPile k
                { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }
            | none => st).swapPiles i j)
      rw [hpt]
      cases h : st.pileOfTop z with
      | none => rfl
      | some k =>
          rw [Option.map_some]
          show (st.swapPiles i j).setPile (Anchor.swap i j k)
              { (st.swapPiles i j).piles (Anchor.swap i j k) with
                  faceUp := ((st.swapPiles i j).piles (Anchor.swap i j k)).faceUp ++ [c] }
            = (st.setPile k
                { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }).swapPiles i j
          rw [State.swapPiles_piles_self]
          rw [State.setPile_swapPiles]
          rw [Anchor.swap_swap]

/-- The run placement conjugates. -/
theorem State.putRun_swapPiles {st : State} {i j : Anchor} (hwf : st.WF)
    (run : List Card) (b : Base) :
    (st.swapPiles i j).putRun run b
      = (st.putRun run (b.swapBase i j)).swapPiles i j := by
  cases b with
  | inl a => exact State.setPile_swapPiles st i j a ⟨[], run⟩
  | inr z =>
      have hpt : (st.swapPiles i j).pileOfTop z
          = (st.pileOfTop z).map (Anchor.swap i j) :=
        State.pileOfTop_swapPiles hwf z
      show (match (st.swapPiles i j).pileOfTop z with
        | some k => (st.swapPiles i j).setPile k
            { (st.swapPiles i j).piles k with
                faceUp := ((st.swapPiles i j).piles k).faceUp ++ run }
        | none => st.swapPiles i j)
        = ((match st.pileOfTop z with
            | some k => st.setPile k
                { st.piles k with faceUp := (st.piles k).faceUp ++ run }
            | none => st).swapPiles i j)
      rw [hpt]
      cases h : st.pileOfTop z with
      | none => rfl
      | some k =>
          rw [Option.map_some]
          show (st.swapPiles i j).setPile (Anchor.swap i j k)
              { (st.swapPiles i j).piles (Anchor.swap i j k) with
                  faceUp := ((st.swapPiles i j).piles (Anchor.swap i j k)).faceUp ++ run }
            = (st.setPile k
                { st.piles k with faceUp := (st.piles k).faceUp ++ run }).swapPiles i j
          rw [State.swapPiles_piles_self]
          rw [State.setPile_swapPiles]
          rw [Anchor.swap_swap]

/-! ## §4. The step conjugation

The draw pipeline conjugates fieldwise; the placement arms
re-assemble through the reader rows, in the `State.twin_step` house
style. -/

/-- Nothing new enters a pile through the run removal (the
membership half of the private `mem_afterRunRemoved_below_zone` row
in `Orig/Reach.lean`, carried privately here; dedup-marked). -/
private theorem nmem_afterRunRemoved_below {p : Pile} {c z : Card}
    (hzh : z ∉ p.hidden) (hzf : z ∉ p.faceUp) :
    z ∉ (Pile.afterRunRemoved p (below c p.faceUp)).hidden ∧
    z ∉ (Pile.afterRunRemoved p (below c p.faceUp)).faceUp := by
  obtain ⟨hid, fu⟩ := p
  cases hb : below c fu with
  | nil =>
      show z ∉ (Pile.revealTop { hidden := hid, faceUp := ([] : List Card) }).hidden ∧
        z ∉ (Pile.revealTop { hidden := hid, faceUp := [] }).faceUp
      cases hid with
      | nil =>
          constructor <;> intro h <;> cases h
      | cons g gs =>
          rw [show (Pile.revealTop { hidden := g :: gs, faceUp := ([] : List Card) })
              = { hidden := gs, faceUp := ([] : List Card) ++ [g] } from rfl]
          refine ⟨?_, ?_⟩
          · intro h
            exact hzh (List.mem_cons.2 (Or.inr h))
          · intro h
            rcases List.mem_append.1 h with hnil | hcone
            · cases hnil
            · rcases List.mem_cons.1 hcone with rfl | hnil
              · exact hzh (List.mem_cons.2 (Or.inl rfl))
              · cases hnil
  | cons x xs =>
      refine ⟨fun h => hzh h, ?_⟩
      intro h
      rcases List.mem_cons.1 h with rfl | hxs
      · exact hzf (mem_below fu (by rw [hb]; exact List.mem_cons.2 (Or.inl rfl)))
      · exact hzf (mem_below fu (by rw [hb]; exact List.mem_cons.2 (Or.inr hxs)))

/-- The recycle conjugates. -/
theorem State.recycle_swapPiles (st : State) (i j : Anchor) :
    (st.swapPiles i j).recycle = (st.recycle).swapPiles i j := by
  cases hst : st.stock with
  | nil =>
      have hs : (st.swapPiles i j).stock = [] := by
        show st.stock = []
        exact hst
      cases hw : st.waste with
      | nil =>
          have hw2 : (st.swapPiles i j).waste = [] := by
            show st.waste = []
            exact hw
          rw [recycle_allEmpty _ hs hw2, recycle_allEmpty _ hst hw]
      | cons w ws =>
          rw [show (st.swapPiles i j).recycle = { st.swapPiles i j with
                stock := (st.swapPiles i j).waste.reverse, waste := [] } from
              recycle_nil _ hs (by show st.waste ≠ []; rw [hw]; simp),
            show st.recycle = { st with stock := st.waste.reverse, waste := [] } from
              recycle_nil _ hst (by rw [hw]; simp)]
          rfl
  | cons s ss =>
      have hneσ : (st.swapPiles i j).stock ≠ [] := by
        show st.stock ≠ []
        simp [hst]
      rw [recycle_keep _ hneσ, recycle_keep _ (by simp [hst])]

/-- The stock-deal conjugates. -/
theorem State.dealStock_swapPiles (st : State) (i j : Anchor) :
    (st.swapPiles i j).dealStock
      = (st.dealStock).map (fun s : State => s.swapPiles i j) := by
  have hs : (st.swapPiles i j).stock = st.stock := rfl
  cases hst : st.stock with
  | nil =>
      have hsσ : (st.swapPiles i j).stock = [] := by rw [hs]; exact hst
      rw [dealStock_nil _ hsσ, dealStock_nil _ hst, Option.map_none]
  | cons s ss =>
      have hneσ : (st.swapPiles i j).stock ≠ [] := by
        rw [hs]
        simp [hst]
      have hne : st.stock ≠ [] := by simp [hst]
      rw [dealStock_eq_of_ne_nil _ hneσ, dealStock_eq_of_ne_nil _ hne]
      rw [show (st.swapPiles i j).drawStep = st.drawStep from rfl,
          hs, show (st.swapPiles i j).waste = st.waste from rfl]
      rw [Option.map_some]
      rfl

/-- The draw step conjugates. -/
theorem State.stepDraw_swapPiles (st : State) (i j : Anchor) :
    (st.swapPiles i j).stepDraw
      = (st.stepDraw).map (fun s : State => s.swapPiles i j) := by
  show State.dealStock ((st.swapPiles i j).recycle)
    = (State.dealStock st.recycle).map (fun s : State => s.swapPiles i j)
  rw [State.recycle_swapPiles]
  exact State.dealStock_swapPiles st.recycle i j

/-- **The commutation lemma**: stepping the swapped state with the
swapped move is stepping the state with the move, swapped — every
kind at once, both `Option` directions, at `WF`. -/
theorem State.step_swapPiles {st : State} {i j : Anchor} (hwf : st.WF)
    (m : Move) :
    (st.swapPiles i j).step (Move.swapM i j m)
      = (st.step m).map (fun s : State => s.swapPiles i j) := by
  cases m with
  | draw => exact State.stepDraw_swapPiles st i j
  | wasteToFound c =>
      show (st.swapPiles i j).step (Move.wasteToFound c)
        = (st.step (Move.wasteToFound c)).map _
      by_cases hg : (st.wasteIs c && st.nextUp c) = true
      · cases hwl : st.waste with
        | nil =>
            rw [State.wasteIs_nil hwl] at hg
            exact absurd hg (by simp)
        | cons x t =>
            have hσw : (st.swapPiles i j).waste = x :: t := hwl
            rw [show (st.swapPiles i j).step (Move.wasteToFound c) =
                  some { (st.swapPiles i j).setFound c.suit (st.found c.suit ++ [c])
                    with waste := t } from by
                  simp only [State.step, State.swapPiles_wasteIs, State.swapPiles_nextUp,
                    State.swapPiles_found_apply, State.swapPiles_waste, hwl, hg, if_true]]
            rw [show st.step (Move.wasteToFound c) =
                  some { st.setFound c.suit (st.found c.suit ++ [c]) with waste := t } from by
                  simp only [State.step, hg, hwl, if_true]]
            rw [Option.map_some, Option.some.injEq]
            rw [State.setFound_swapPiles st i j c.suit (st.found c.suit ++ [c])]
            rfl
      · have hf : (st.wasteIs c && st.nextUp c) = false := by
          cases hg2 : (st.wasteIs c && st.nextUp c) with
          | true => exact absurd hg2 hg
          | false => rfl
        rw [show (st.swapPiles i j).step (Move.wasteToFound c) = none from by
              simp [State.step, State.swapPiles_wasteIs, State.swapPiles_nextUp, hf],
            show st.step (Move.wasteToFound c) = none from by
              simp [State.step, hf],
            Option.map_none]
  | wasteToTab c b =>
      show (st.swapPiles i j).step (Move.wasteToTab c (Base.swapBase b i j))
        = (st.step (Move.wasteToTab c b)).map _
      have hcpσ : (st.swapPiles i j).canPlace c (Base.swapBase b i j)
          = st.canPlace c b := by
        rw [State.canPlace_swapPiles hwf c (Base.swapBase b i j),
          Base.swapBase_swapBase]
      by_cases hg : (st.wasteIs c && st.canPlace c b) = true
      · cases hwl : st.waste with
        | nil =>
            rw [State.wasteIs_nil hwl] at hg
            exact absurd hg (by simp)
        | cons x t =>
            have hσw : (st.swapPiles i j).waste = x :: t := hwl
            rw [show (st.swapPiles i j).step (Move.wasteToTab c (Base.swapBase b i j)) =
                  some { (st.swapPiles i j).putCard c (Base.swapBase b i j)
                    with waste := t } from by
                  simp only [State.step, State.swapPiles_wasteIs, State.swapPiles_waste,
                    hcpσ, hwl, hg, if_true]]
            rw [show st.step (Move.wasteToTab c b) =
                  some { st.putCard c b with waste := t } from by
                  simp only [State.step, hg, hwl, if_true]]
            rw [Option.map_some, Option.some.injEq]
            rw [State.putCard_swapPiles hwf c (Base.swapBase b i j),
              Base.swapBase_swapBase]
            rfl
      · have hf : (st.wasteIs c && st.canPlace c b) = false := by
          cases hg2 : (st.wasteIs c && st.canPlace c b) with
          | true => exact absurd hg2 hg
          | false => rfl
        rw [show (st.swapPiles i j).step (Move.wasteToTab c (Base.swapBase b i j)) = none from by
              simp [State.step, State.swapPiles_wasteIs, hcpσ, hf],
            show st.step (Move.wasteToTab c b) = none from by
              simp [State.step, hf],
            Option.map_none]
  | tabToFound c =>
      show (st.swapPiles i j).step (Move.tabToFound c)
        = (st.step (Move.tabToFound c)).map _
      have hnσ : (st.swapPiles i j).nextUp c = st.nextUp c := rfl
      by_cases hu : st.nextUp c = true
      · cases hp : st.pileOfTop c with
        | none =>
            have hpσ : (st.swapPiles i j).pileOfTop c = none := by
              rw [State.pileOfTop_swapPiles hwf c, hp, Option.map_none]
            rw [show (st.swapPiles i j).step (Move.tabToFound c) =
                  none from by simp only [State.step, hnσ, hu, hpσ, if_true],
                show st.step (Move.tabToFound c) = none from by
                  simp only [State.step, hu, hp, if_true],
                Option.map_none]
        | some a =>
            have hpσ : (st.swapPiles i j).pileOfTop c
                = some (Anchor.swap i j a) := by
              rw [State.pileOfTop_swapPiles hwf c, hp, Option.map_some]
            rw [show (st.swapPiles i j).step (Move.tabToFound c) =
                  some { (st.swapPiles i j).setFound c.suit (st.found c.suit ++ [c]) with
                    piles := fun a' =>
                      if a' = Anchor.swap i j a then
                        Pile.afterRunRemoved
                          ((st.swapPiles i j).piles (Anchor.swap i j a))
                          (chop ((st.swapPiles i j).piles (Anchor.swap i j a)).faceUp)
                      else (st.swapPiles i j).piles a' } from by
                  simp only [State.step, hnσ, hu, hpσ, State.swapPiles_found_apply, ite_true]]
            rw [show st.step (Move.tabToFound c) =
                  some { st.setFound c.suit (st.found c.suit ++ [c]) with
                    piles := fun a' =>
                      if a' = a then
                        Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
                      else st.piles a' } from by
                  simp only [State.step, hu, hp, if_true]]
            rw [Option.map_some, Option.some.injEq]
            refine State.ext rfl (funext (fun a'' => ?_)) rfl rfl rfl
            rw [State.swapPiles_piles_self st i j a]
            show (if a'' = Anchor.swap i j a then
                    Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
                    else st.piles (Anchor.swap i j a''))
              = (if Anchor.swap i j a'' = a then
                    Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
                    else st.piles (Anchor.swap i j a''))
            by_cases hA : a'' = Anchor.swap i j a
            · have hσA : Anchor.swap i j a'' = a := by
                have h3 := congrArg (Anchor.swap i j) hA
                rw [Anchor.swap_swap] at h3
                exact h3
              rw [if_pos hA, if_pos hσA]
            · have hσA : Anchor.swap i j a'' ≠ a := by
                intro hcon
                have h3 := congrArg (Anchor.swap i j) hcon
                rw [Anchor.swap_swap] at h3
                exact hA h3
              rw [if_neg hA, if_neg hσA]
      · have hf : st.nextUp c = false := by
          cases hu2 : st.nextUp c with
          | true => exact absurd hu2 hu
          | false => rfl
        rw [show (st.swapPiles i j).step (Move.tabToFound c) = none from by
              simp [State.step, hnσ, hf],
            show st.step (Move.tabToFound c) = none from by
              simp [State.step, hf],
            Option.map_none]
  | foundToTab c b =>
      show (st.swapPiles i j).step (Move.foundToTab c (Base.swapBase b i j))
        = (st.step (Move.foundToTab c b)).map _
      have htσ : (st.swapPiles i j).foundTop c.suit = st.foundTop c.suit := rfl
      have hcpσ : (st.swapPiles i j).canPlace c (Base.swapBase b i j)
          = st.canPlace c b := by
        rw [State.canPlace_swapPiles hwf c (Base.swapBase b i j),
          Base.swapBase_swapBase]
      cases ht : st.foundTop c.suit with
      | none =>
          rw [show (st.swapPiles i j).step (Move.foundToTab c (Base.swapBase b i j)) = none from by
                simp [State.step, State.swapPiles_foundTop, ht],
              show st.step (Move.foundToTab c b) = none from by
                simp [State.step, ht],
              Option.map_none]
      | some c₀ =>
          by_cases hc₀ : c₀ = c
          · rw [hc₀] at ht
            cases hcp : st.canPlace c b with
            | false =>
                rw [show (st.swapPiles i j).step (Move.foundToTab c (Base.swapBase b i j)) =
                      none from by
                      simp only [State.step, htσ, ht]
                      rw [hcpσ, hcp]
                      rfl,
                    show st.step (Move.foundToTab c b) = none from by
                      simp only [State.step, ht]
                      rw [hcp]
                      rfl,
                    Option.map_none]
            | true =>
                rw [show (st.swapPiles i j).step (Move.foundToTab c (Base.swapBase b i j)) =
                      some (((st.swapPiles i j).setFound c.suit
                          (chop ((st.swapPiles i j).found c.suit))).putCard
                        c (Base.swapBase b i j)) from by
                      simp only [State.step, htσ, ht]
                      rw [hcpσ, hcp]
                      rfl]
                rw [show st.step (Move.foundToTab c b) =
                      some (((st.setFound c.suit (chop (st.found c.suit))).putCard c b)) from by
                      simp only [State.step, ht]
                      rw [hcp]
                      rfl]
                rw [Option.map_some, Option.some.injEq]
                rw [State.swapPiles_found_apply st i j c.suit]
                rw [State.setFound_swapPiles st i j c.suit (chop (st.found c.suit))]
                have hpt : ∀ z₀,
                    ((st.setFound c.suit (chop (st.found c.suit))).swapPiles i j).pileOfTop z₀
                      = Option.map (Anchor.swap i j)
                          ((st.setFound c.suit (chop (st.found c.suit))).pileOfTop z₀) := by
                  intro z₀
                  have h1 : ∀ x, ((st.setFound c.suit (chop (st.found c.suit))).swapPiles i j).piles x
                      = (st.swapPiles i j).piles x := fun x => rfl
                  rw [State.pileOfTop_congr_piles h1 z₀,
                    State.pileOfTop_swapPiles hwf z₀]
                  have h2 : ∀ x, (st.setFound c.suit (chop (st.found c.suit))).piles x
                      = st.piles x := fun _ => rfl
                  rw [State.pileOfTop_congr_piles h2 z₀]
                rw [State.putCard_swapPiles' hpt c (Base.swapBase b i j),
                  Base.swapBase_swapBase]
          · have hdec : decide (c₀ = c) = false := decide_false_of_not hc₀
            rw [show (st.swapPiles i j).step (Move.foundToTab c (Base.swapBase b i j)) =
                  none from by
                  simp only [State.step, htσ, ht]
                  rw [hcpσ, hdec]
                  rfl,
                show st.step (Move.foundToTab c b) = none from by
                  simp only [State.step, ht]
                  rw [hdec]
                  rfl,
                Option.map_none]
  | tabToTab c b =>
      show (st.swapPiles i j).step (Move.tabToTab c (Base.swapBase b i j))
        = (st.step (Move.tabToTab c b)).map _
      have hhσ : (st.swapPiles i j).pileHolding c = (st.pileHolding c).map (Anchor.swap i j) :=
        State.pileHolding_swapPiles hwf c
      have hcpσ : (st.swapPiles i j).canPlace c (Base.swapBase b i j)
          = st.canPlace c b := by
        rw [State.canPlace_swapPiles hwf c (Base.swapBase b i j),
          Base.swapBase_swapBase]
      cases hp : st.pileHolding c with
      | none =>
          have hpσ : (st.swapPiles i j).pileHolding c = none := by
            rw [hhσ, hp, Option.map_none]
          rw [show (st.swapPiles i j).step (Move.tabToTab c (Base.swapBase b i j)) = none from by
                simp [State.step, hpσ],
              show st.step (Move.tabToTab c b) = none from by
                simp [State.step, hp],
              Option.map_none]
      | some a =>
          have hpσ : (st.swapPiles i j).pileHolding c
              = some (Anchor.swap i j a) := by
            rw [hhσ, hp, Option.map_some]
          cases hcp : st.canPlace c b with
          | false =>
              rw [show (st.swapPiles i j).step (Move.tabToTab c (Base.swapBase b i j)) = none from by
                    simp [State.step, hpσ, hcpσ, hcp, if_false],
                  show st.step (Move.tabToTab c b) = none from by
                    simp [State.step, hp, hcp, if_false],
                  Option.map_none]
          | true =>
              cases hfc : fromCard c (st.piles a).faceUp with
              | nil =>
                  have hnilσ : fromCard c
                      ((st.swapPiles i j).piles (Anchor.swap i j a)).faceUp = [] := by
                    rw [State.swapPiles_piles_self st i j a]
                    exact hfc
                  rw [show (st.swapPiles i j).step (Move.tabToTab c (Base.swapBase b i j)) = none from by
                        simp only [State.step, hpσ, hcpσ, hcp, hnilσ, ite_true],
                      show st.step (Move.tabToTab c b) = none from by
                        simp only [State.step, hp, hcp, hfc, ite_true],
                      Option.map_none]
              | cons r rs =>
                  have hσfc : fromCard c
                      ((st.swapPiles i j).piles (Anchor.swap i j a)).faceUp = r :: rs := by
                    rw [State.swapPiles_piles_self st i j a]
                    exact hfc
                  rw [show (st.swapPiles i j).step (Move.tabToTab c (Base.swapBase b i j)) =
                        some ((((st.swapPiles i j).setPile (Anchor.swap i j a)
                            (Pile.afterRunRemoved ((st.swapPiles i j).piles (Anchor.swap i j a))
                              (below c ((st.swapPiles i j).piles (Anchor.swap i j a)).faceUp)))
                          ).putRun (r :: rs) (Base.swapBase b i j)) from by
                        simp only [State.step, hpσ, hcpσ, hcp, ite_true, hσfc]]
                  rw [show st.step (Move.tabToTab c b) =
                        some (((st.setPile a (Pile.afterRunRemoved (st.piles a)
                            (below c (st.piles a).faceUp))).putRun (r :: rs) b)) from by
                        simp only [State.step, hp, hcp, ite_true, hfc]]
                  rw [Option.map_some, Option.some.injEq]
                  rw [State.swapPiles_piles_self st i j a]
                  rw [State.setPile_swapPiles]
                  rw [Anchor.swap_swap]
                  cases b with
                  | inl x' =>
                      rw [show ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                              (below c (st.piles a).faceUp))).swapPiles i j).putRun (r :: rs)
                            (Base.swapBase (Sum.inl x') i j)
                            = ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                              (below c (st.piles a).faceUp))).swapPiles i j).setPile
                                (Anchor.swap i j x') ⟨[], r :: rs⟩ from rfl,
                               show ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                              (below c (st.piles a).faceUp))).putRun (r :: rs) (Sum.inl x'))
                            = (st.setPile a (Pile.afterRunRemoved (st.piles a)
                              (below c (st.piles a).faceUp))).setPile x' ⟨[], r :: rs⟩ from rfl]
                      rw [State.setPile_swapPiles (st.setPile a
                          (Pile.afterRunRemoved (st.piles a)
                            (below c (st.piles a).faceUp))) i j]
                      rw [Anchor.swap_swap]
                  | inr z =>
                      obtain ⟨k, hk⟩ : ∃ k, st.pileOfTop z = some k := by
                        cases hpz : st.pileOfTop z with
                        | none =>
                            exfalso
                            have hcan : st.canPlace c (Sum.inr z) = true := hcp
                            rw [show st.canPlace c (Sum.inr z)
                                = (match st.pileOfTop z with
                                  | some _ => canSitOn c z
                                  | none => false) from rfl] at hcan
                            rw [hpz] at hcan
                            exact absurd hcan (by simp)
                        | some k => exact ⟨k, rfl⟩
                      have hcan : st.canPlace c (Sum.inr z) = true := hcp
                      have hkmem : (st.piles k).top = some z :=
                        (pileOfTop_eq_some_iff hwf).mp hk
                      have hzmemk : z ∈ (st.piles k).faceUp := Pile.mem_of_top hkmem
                      have hcmem : c ∈ (st.piles a).faceUp := pileHolding_mem hp
                      have hne : st.pileOfTop z ≠ some a :=
                        canPlace_inr_target_pile_ne hwf hcan hcmem
                      have hka : k ≠ a := by
                        intro hcon
                        rw [hcon] at hk
                        exact hne hk
                      have hzna : z ∉ (st.piles a).hidden ∧ z ∉ (st.piles a).faceUp :=
                        ⟨fun hcon => (mem_faceUp_unique hwf hzmemk a hka.symm).2.1 hcon,
                         fun hcon => (mem_faceUp_unique hwf hzmemk a hka.symm).1 hcon⟩
                      have hPnoz : z ∉ (Pile.afterRunRemoved (st.piles a)
                          (below c (st.piles a).faceUp)).hidden ∧
                          z ∉ (Pile.afterRunRemoved (st.piles a)
                            (below c (st.piles a).faceUp)).faceUp :=
                        nmem_afterRunRemoved_below hzna.1 hzna.2
                      have hS' : ((st.setPile a
                          (Pile.afterRunRemoved (st.piles a)
                            (below c (st.piles a).faceUp))).pileOfTop z) = some k := by
                        show firstWhere (fun x =>
                            decide (((st.setPile a
                              (Pile.afterRunRemoved (st.piles a)
                                (below c (st.piles a).faceUp))).piles x).top
                              = some z)) Anchor.all = some k
                        have hslice : ∀ x, ((st.setPile a
                            (Pile.afterRunRemoved (st.piles a)
                              (below c (st.piles a).faceUp))).piles x)
                            = (if x = a then
                              (Pile.afterRunRemoved (st.piles a)
                                (below c (st.piles a).faceUp))
                            else st.piles x) := fun x => rfl
                        refine firstWhere_find (Anchor.mem_all k) ?_
                          (fun y _hy hyne => ?_)
                        · rw [hslice k, if_neg hka]
                          exact decide_eq_true_eq.mpr hkmem
                        · show decide (((st.setPile a
                              (Pile.afterRunRemoved (st.piles a)
                                (below c (st.piles a).faceUp))).piles y).top
                              = some z) = false
                          rw [hslice y]
                          by_cases hya : y = a
                          · rw [if_pos hya, decide_eq_false_iff_not]
                            intro hty
                            exact hPnoz.2 (Pile.mem_of_top hty)
                          · rw [if_neg hya, decide_eq_false_iff_not]
                            intro hty
                            have hs2 := (pileOfTop_eq_some_iff hwf).mpr hty
                            exact hyne (pileOfTop_inj hk hs2).symm
                      have hS'σ : ((st.setPile a
                          (Pile.afterRunRemoved (st.piles a)
                            (below c (st.piles a).faceUp))).swapPiles i j).pileOfTop z
                          = some (Anchor.swap i j k) := by
                        show firstWhere (fun x =>
                            decide ((((st.setPile a
                              (Pile.afterRunRemoved (st.piles a)
                                (below c (st.piles a).faceUp))).swapPiles i j).piles x).top
                              = some z)) Anchor.all = some (Anchor.swap i j k)
                        have hslice : ∀ x, (((st.setPile a
                            (Pile.afterRunRemoved (st.piles a)
                              (below c (st.piles a).faceUp))).swapPiles i j).piles x)
                            = (if Anchor.swap i j x = a then
                              (Pile.afterRunRemoved (st.piles a)
                                (below c (st.piles a).faceUp))
                            else st.piles (Anchor.swap i j x)) := fun x => rfl
                        refine firstWhere_find (Anchor.mem_all (Anchor.swap i j k)) ?_
                          (fun y _hy hyne => ?_)
                        · have hxx : (Anchor.swap i j
                              (Anchor.swap i j k)) = k := Anchor.swap_swap i j k
                          rw [hslice (Anchor.swap i j k), hxx, if_neg hka]
                          exact decide_eq_true_eq.mpr hkmem
                        · show decide ((((st.setPile a
                              (Pile.afterRunRemoved (st.piles a)
                                (below c (st.piles a).faceUp))).swapPiles i j).piles y).top
                              = some z) = false
                          rw [hslice y]
                          by_cases hya : Anchor.swap i j y = a
                          · rw [if_pos hya, decide_eq_false_iff_not]
                            intro hty
                            exact hPnoz.2 (Pile.mem_of_top hty)
                          · rw [if_neg hya, decide_eq_false_iff_not]
                            intro hty
                            have hs2 := (pileOfTop_eq_some_iff hwf).mpr hty
                            have hyk := pileOfTop_inj hk hs2
                            apply hyne
                            have h3 := congrArg (Anchor.swap i j) hyk
                            rw [Anchor.swap_swap] at h3
                            exact h3.symm
                      have hptz : ((st.setPile a
                          (Pile.afterRunRemoved (st.piles a)
                            (below c (st.piles a).faceUp))).swapPiles i j).pileOfTop z
                          = Option.map (Anchor.swap i j)
                          ((st.setPile a
                          (Pile.afterRunRemoved (st.piles a)
                            (below c (st.piles a).faceUp))).pileOfTop z) := by
                        rw [hS'σ, hS', Option.map_some]
                      rw [show (Base.swapBase (Sum.inr z) i j) = Sum.inr z from rfl,
                        State.putRun_swapPiles'_inr hptz (r :: rs)]

/-- Legality conjugates (defined-swapped iff defined). -/
theorem State.legal_swapPiles {st : State} {i j : Anchor} (hwf : st.WF)
    (m : Move) :
    (st.swapPiles i j).legal (Move.swapM i j m) = st.legal m := by
  simp only [State.legal]
  rw [State.step_swapPiles hwf m]
  cases st.step m with
  | none => rfl
  | some st' => rfl

/-! ## §6 (before §5: the lift's reverse leg needs it). The WF transfer
-/

/-- The anchor-list permutation: transposing the seven positions
permutes the all-list (decided on the literal). -/
theorem Anchor.all_map_swap_perm (i j : Anchor) :
    List.Perm (Anchor.all.map (Anchor.swap i j)) Anchor.all := by
  cases i <;> cases j <;> decide

/-- The pile zones permute as a block. -/
theorem State.swapPiles_zones_perm {st : State} {i j : Anchor} :
    List.Perm (st.swapPiles i j).zones st.zones := by
  show List.Perm (Suit.all.map st.found
      ++ Anchor.all.map (fun a =>
          ((st.swapPiles i j).piles a).hidden ++ ((st.swapPiles i j).piles a).faceUp)
      ++ [st.stock, st.waste])
    (Suit.all.map st.found
      ++ Anchor.all.map (fun a =>
          (st.piles a).hidden ++ (st.piles a).faceUp)
      ++ [st.stock, st.waste])
  have hblock : List.Perm (Anchor.all.map (fun a =>
          ((st.swapPiles i j).piles a).hidden ++ ((st.swapPiles i j).piles a).faceUp))
      (Anchor.all.map (fun a => (st.piles a).hidden ++ (st.piles a).faceUp)) := by
    have h := Anchor.all_map_swap_perm i j
    have h2 : List.Perm
        (Anchor.all.map (fun a =>
          ((st.swapPiles i j).piles a).hidden ++ ((st.swapPiles i j).piles a).faceUp))
        (Anchor.all.map (fun a => (st.piles a).hidden ++ (st.piles a).faceUp)) :=
      List.Perm.map (fun a => (st.piles a).hidden ++ (st.piles a).faceUp) h
    exact h2
  exact (List.Perm.refl (Suit.all.map st.found)).append
    (hblock.append (List.Perm.refl [st.stock, st.waste]))

/-- The card count is permutation-invariant. -/
theorem State.cardCount_swapPiles (st : State) (i j : Anchor) (c : Card) :
    (st.swapPiles i j).cardCount c = st.cardCount c := by
  show ((st.swapPiles i j).zones.flatMap id
      |>.filter (fun x => decide (x = c))).length
    = ((st.zones.flatMap id |>.filter (fun x => decide (x = c))).length)
  have hz := State.swapPiles_zones_perm (st := st) (i := i) (j := j)
  have hflat := List.Perm.flatMap_right id hz
  have hfilt := List.Perm.filter (fun x => decide (x = c)) hflat
  exact List.Perm.length_eq hfilt

/-- The forward WF transfer. -/
theorem State.wf_swapPiles {st : State} {i j : Anchor} (hwf : st.WF) :
    (st.swapPiles i j).WF := by
  refine ⟨fun s => hwf.1 s, fun a => hwf.2.1 (Anchor.swap i j a),
    fun c hc => ?_, hwf.2.2.2⟩
  have h := hwf.2.2.1 c hc
  rw [State.cardCount_swapPiles st i j c]
  exact h

/-- **The Orig-only upgrade**: WF transfers under the pile
transposition in both directions — the deal-shape clause that
blocked Klondike's swap does not exist here, and the conservation
block permutes. -/
theorem State.wf_swapPiles_iff {st : State} {i j : Anchor} :
    (st.swapPiles i j).WF ↔ st.WF := by
  constructor
  · intro hwfσ
    have h2 := State.wf_swapPiles (st := st.swapPiles i j) (i := i) (j := j) hwfσ
    rw [State.swapPiles_swapPiles] at h2
    exact h2
  · exact State.wf_swapPiles

/-! ## §5. The lift: runs and winnability -/

/-- The lift: whole plays conjugate, the WF threaded along by
`Orig.Reach.step_wf`. -/
theorem State.run_swapPiles (i j : Anchor) : ∀ (play : List Move) (st : State),
    st.WF → (st.swapPiles i j).run (play.map (Move.swapM i j))
      = (st.run play).map (fun s : State => s.swapPiles i j) := by
  intro play
  induction play with
  | nil => intro st _; rfl
  | cons m ms ih =>
      intro st hwf
      show (match (st.swapPiles i j).step (Move.swapM i j m) with
        | some s' => s'.run (ms.map (Move.swapM i j))
        | none => none)
        = (match st.step m with
          | some s' => s'.run ms
          | none => none).map (fun s : State => s.swapPiles i j)
      rw [State.step_swapPiles hwf m]
      cases hstep : st.step m with
      | none => rfl
      | some s₁ =>
          rw [Option.map_some]
          have hwf₁ : s₁.WF := step_wf hwf hstep
          show (s₁.swapPiles i j).run (ms.map (Move.swapM i j))
            = Option.map (fun s : State => s.swapPiles i j) (s₁.run ms)
          rw [ih s₁ hwf₁]

/-- Winnability transfers forward. -/
theorem WinFrom_of_swapPiles {st : State} {i j : Anchor} (hwf : st.WF)
    (h : WinFrom st) : WinFrom (st.swapPiles i j) := by
  obtain ⟨play, s, hrun, hwin⟩ := h
  refine ⟨play.map (Move.swapM i j), s.swapPiles i j, ?_, ?_⟩
  · rw [State.run_swapPiles i j play st hwf, hrun]
    rfl
  · rw [show (s.swapPiles i j).isWin = s.isWin from rfl]
    exact hwin

/-- The pile transposition preserves the verdict, both directions by
involutivity (`isWin` reads `found` only). -/
theorem WinFrom_swapPiles_iff {st : State} {i j : Anchor} (hwf : st.WF) :
    WinFrom st ↔ WinFrom (st.swapPiles i j) := by
  constructor
  · exact WinFrom_of_swapPiles hwf
  · intro h
    have hwfσ : (st.swapPiles i j).WF := State.wf_swapPiles hwf
    have h2 := WinFrom_of_swapPiles (st := st.swapPiles i j) (i := i) (j := j) hwfσ h
    rw [State.swapPiles_swapPiles] at h2
    exact h2
