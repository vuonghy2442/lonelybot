import Orig2.Fork.ForkThirdHigh
import Orig2.Fiber.SWDichotomy
import Orig2.Fork.ForkPinAt

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Temp/ForkFloor_Base — the PAIR-FLOOR lemma: provable fragments

SCRATCH.  Read-only w.r.t. repo source (nothing here is imported).

TARGET (`fork_pair_floor`):

```lean
theorem fork_pair_floor {F G : State} {x : Card}
    (hF : F.WF) (hG : G.WF) (hcls : sameOrbitSetoid.r F G)
    (hx : ForkWitness F x) (hsat : SSaturated G) :
    rungAt F x.suit ≤ rungAt G x.suit ∧
      rungAt F x.twin.suit ≤ rungAt G x.twin.suit
```

Since `rungAt F x.suit = rungAt F x.twin.suit = x.rank.toIdx`
(`forkState_witness_rungs`), this is the lower bound `r ≤ rungAt G σ` on both
pair suits — the half `oneFounding_pair_bound` (`Orig2/Fiber/SWDichotomy.lean:249`)
does not give.

What this file PROVES:

* `fork_pair_floor_of_fork`  — the EASY COROLLARY: if `G` is itself a fork
  state, rigidity (`forkPositionRigid_unconditional`,
  `Orig2/Fork/ForkThirdHigh.lean:845`) gives `RungEq F G` and the floor is
  immediate.  So the content is exactly the NON-FORK saturated `G`.
* `PairFloorNonFork` + `fork_pair_floor_of_nonfork` — the exact REDUCTION of
  the target to its non-fork-`G` instance (a case split on "is `G` a fork").
* `PairFloorLocal` + `fork_pair_floor_of_local` — the further reduction to a
  single LOCAL statement at `G` about ONE card (no fork at `G`, no rung
  equation at `G`).  This is the precise residual lemma.
* `no_supported_nextUp_zero` / `pairFloorLocalAt_zero` — the local lemma at
  rank index `0` (the bottom of the descent), PROVED: a next-up, supported
  card of rank index `0` (an ace) tops its pile, hence is vanilla-raisable,
  hence cannot sit at a saturated `WF` state.

House compliance: scratch only; zero `sorry`.
-/

namespace ForkFloor

/-! ## §1. The easy corollary: a fork `G` is rigid -/

/-- **THE FLOOR WHEN `G` IS A FORK.**  `forkPositionRigid_unconditional`
gives `RungEq F G`, and the pair rungs at `F` read `x.rank.toIdx`; so the
floor is equality on both pair suits. -/
theorem fork_pair_floor_of_fork {F G : State} {x : Card}
    (hF : F.WF) (hG : G.WF) (hcls : sameOrbitSetoid.r F G)
    (hx : ForkWitness F x) {y : Card} (hy : ForkWitness G y) :
    rungAt F x.suit ≤ rungAt G x.suit ∧
      rungAt F x.twin.suit ≤ rungAt G x.twin.suit := by
  have hrung := ThirdHigh.forkPositionRigid_unconditional F G x y hF hG hcls hx hy
  exact ⟨Nat.le_of_eq (hrung x.suit), Nat.le_of_eq (hrung x.twin.suit)⟩

/-- The same statement in the "rank lower bound" form used by the reduction. -/
theorem fork_pair_floor_of_fork' {F G : State} {x : Card}
    (hF : F.WF) (hG : G.WF) (hcls : sameOrbitSetoid.r F G)
    (hx : ForkWitness F x) {y : Card} (hy : ForkWitness G y) :
    x.rank.toIdx ≤ rungAt G x.suit ∧ x.rank.toIdx ≤ rungAt G x.twin.suit := by
  obtain ⟨h1, h2⟩ := fork_pair_floor_of_fork hF hG hcls hx hy
  have hF1 : rungAt F x.suit = x.rank.toIdx := (forkState_witness_rungs hx).1
  have hF2 : rungAt F x.twin.suit = x.rank.toIdx := (forkState_witness_rungs hx).2
  exact ⟨by omega, by omega⟩

/-! ## §2. The exact reduction to non-fork `G` -/

/-- **THE PAIR FLOOR, RESTRICTED TO NON-FORK `G`.** -/
def PairFloorNonFork : Prop :=
  ∀ (F G : State) (x : Card), F.WF → G.WF → sameOrbitSetoid.r F G →
    ForkWitness F x → SSaturated G → (∀ y : Card, ¬ ForkWitness G y) →
    rungAt F x.suit ≤ rungAt G x.suit ∧
      rungAt F x.twin.suit ≤ rungAt G x.twin.suit

/-! ### §2b. The constructive fork oracle (choice-free case split)

The previous reduction split on `∃ y, ForkWitness G y` with `by_cases`, which
compiles but drags in `Classical.choice` (the battery showed
`[propext, Classical.choice, Quot.sound]`).  The replacement below is a Bool
oracle over `Card.universe` — `canRaiseSB` for the S-spectrum and
`PinAt.canRaiseBL` for the vanilla pin — so the split is `cases` on a `Bool`,
which is constructive.  This is the same repair pattern as `Orig2/ForkDecide`
and `Orig2/ForkFace2`. -/

/-- Equality of `Bool`s from equality of their `true`-sets (constructive). -/
private theorem bool_eq_of_iff {a b : Bool} (h : (a = true) ↔ (b = true)) : a = b := by
  cases a <;> cases b <;> simp_all

/-- **`twinLivePairB st x`** — a constructive decision of `TwinLivePair st x`
over `Card.universe`, via the S-licence probe `canRaiseSB`. -/
def twinLivePairB (st : State) (x : Card) : Bool :=
  Card.universe.all (fun c =>
    decide (canRaiseSB st c = decide (c = x ∨ c = x.twin)))

/-- The oracle reads the live pair at `WF`. -/
theorem twinLivePairB_iff {st : State} {x : Card} (hwf : st.WF) :
    twinLivePairB st x = true ↔ TwinLivePair st x := by
  unfold twinLivePairB
  rw [List.all_eq_true]
  constructor
  · intro h c
    have hc : canRaiseSB st c = decide (c = x ∨ c = x.twin) :=
      of_decide_eq_true (h c (Card.mem_universe c))
    constructor
    · intro hS
      have h1 : canRaiseSB st c = true := (canRaiseSB_iff hwf).mpr hS
      rw [hc] at h1
      exact of_decide_eq_true h1
    · intro hP
      have h1 : decide (c = x ∨ c = x.twin) = true := decide_eq_true hP
      rw [← hc] at h1
      exact (canRaiseSB_iff hwf).mp h1
  · intro h c _
    have hiff : (canRaiseSB st c = true) ↔
        (decide (c = x ∨ c = x.twin) = true) := by
      rw [canRaiseSB_iff hwf, decide_eq_true_iff]
      exact h c
    exact decide_eq_true (bool_eq_of_iff hiff)

/-- **`forkWitnessB st x`** — a constructive decision of `ForkWitness st x`:
the live-pair oracle plus the vanilla pin via `PinAt.canRaiseBL`. -/
def forkWitnessB (st : State) (x : Card) : Bool :=
  twinLivePairB st x && !PinAt.canRaiseBL st x.twin

/-- The oracle reads the witness at `WF`. -/
theorem forkWitnessB_iff {st : State} {x : Card} (hwf : st.WF) :
    forkWitnessB st x = true ↔ ForkWitness st x := by
  rw [forkWitness_iff]
  unfold forkWitnessB
  rw [Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(twinLivePairB_iff hwf).mp h1, ?_⟩
    intro hc
    have htrue : PinAt.canRaiseBL st x.twin = true :=
      PinAt.canRaiseBL_true_iff.mpr hc
    rw [h2] at htrue
    exact Bool.noConfusion htrue
  · rintro ⟨h1, h2⟩
    refine ⟨(twinLivePairB_iff hwf).mpr h1, ?_⟩
    cases hb : PinAt.canRaiseBL st x.twin with
    | false => rfl
    | true => exact absurd (PinAt.canRaiseBL_true_iff.mp hb) h2

/-- **`forkExistsB st`** — the `Bool`-valued "does `G` carry a fork witness?"
used by the reduction below. -/
def forkExistsB (st : State) : Bool :=
  Card.universe.any (fun x => forkWitnessB st x)

/-- `forkExistsB = true` extracts a witness. -/
theorem forkExistsB_true {st : State} (hwf : st.WF) (h : forkExistsB st = true) :
    ∃ x, ForkWitness st x := by
  rw [forkExistsB, List.any_eq_true] at h
  obtain ⟨x, _, hx⟩ := h
  exact ⟨x, (forkWitnessB_iff hwf).mp hx⟩

/-- `forkExistsB = false` refutes every witness. -/
theorem forkExistsB_false {st : State} (hwf : st.WF) (h : forkExistsB st = false) :
    ∀ x, ¬ ForkWitness st x := by
  intro x hx
  have hb : forkWitnessB st x = true := (forkWitnessB_iff hwf).mpr hx
  rw [forkExistsB, List.any_eq_false] at h
  exact h x (Card.mem_universe x) hb

/-- **THE REDUCTION (CHOICE-FREE).**  The non-fork instance suffices for the
full target: if `G` carries a witness the easy corollary closes, and if it does
not the hypothesis is spent.  The split is on the Bool oracle `forkExistsB`, so
no `by_cases`/`Classical.choice` enters. -/
theorem fork_pair_floor_of_nonfork (h : PairFloorNonFork) {F G : State} {x : Card}
    (hF : F.WF) (hG : G.WF) (hcls : sameOrbitSetoid.r F G)
    (hx : ForkWitness F x) (hsat : SSaturated G) :
    rungAt F x.suit ≤ rungAt G x.suit ∧
      rungAt F x.twin.suit ≤ rungAt G x.twin.suit := by
  cases hb : forkExistsB G with
  | true =>
      obtain ⟨y, hy⟩ := forkExistsB_true hG hb
      exact fork_pair_floor_of_fork hF hG hcls hx hy
  | false =>
      exact h F G x hF hG hcls hx hsat (forkExistsB_false hG hb)

/-- The converse restriction (trivial): the full target implies the non-fork
instance.  Together with `fork_pair_floor_of_nonfork` this is an exact
reduction of the target to the non-fork branch. -/
theorem nonfork_of_fork_pair_floor
    (h : ∀ (F G : State) (x : Card), F.WF → G.WF → sameOrbitSetoid.r F G →
      ForkWitness F x → SSaturated G →
      rungAt F x.suit ≤ rungAt G x.suit ∧
        rungAt F x.twin.suit ≤ rungAt G x.twin.suit) :
    PairFloorNonFork := by
  intro F G x hF hG hcls hx hsat _
  exact h F G x hF hG hcls hx hsat

/-! ## §3. The local residual: one card at `G` -/

/-- **THE LOCAL RESIDUAL AT ONE RANK (`PairFloorLocalAt`).**  At a `WF`,
S-saturated `G` in the class of the fork `F`, no card `c` of a pair suit, of
rank index exactly `k < r`, that is founded at `F`, can be next-up AND
supported (sit on a card) at `G`.

This is exactly the content the exodus route produces: a floor violation
`rungAt G σ = k < r` names the frontier card `c = (σ, Rk k)`, which is
founded at `F`, absent from `G.found`, hence `Supported G c`
(`ThirdHigh.supported_of_forked_transit`, `Orig2/Fork/ForkThirdHigh.lean:295`) and
next-up at `G`.

The class relation `sameOrbitSetoid.r F G` is NOT droppable: the class-free
version of this statement is FALSE (`Temp/ForkFloor_negcheck.py`, board
`F<AS2S> P{0:4H3S2H ...}`: a `WF`, S-saturated state where `3S` is next-up
and supported, with `3S` founded at any planted fork of pair rank `> 2`; the
state is simply not in that fork's class).  This is the precise sense in
which the pair floor is a CLASS-GLOBAL statement. -/
def PairFloorLocalAt (F : State) (x : Card) (k : Nat) : Prop :=
  ∀ (G : State) (c : Card), G.WF → SSaturated G → sameOrbitSetoid.r F G →
    (c.suit = x.suit ∨ c.suit = x.twin.suit) →
    c.rank.toIdx = k → k < x.rank.toIdx →
    c ∈ F.found c.suit →
    G.nextUp c = true → ¬ ThirdHigh.Supported G c

/-- The local residual: every rank below the fork rank. -/
def PairFloorLocal (F : State) (x : Card) : Prop :=
  ∀ k : Nat, PairFloorLocalAt F x k

/-- A rank-uniform local residual gives the local one. -/
theorem pairFloorLocal_of_at {F : State} {x : Card}
    (h : ∀ k : Nat, PairFloorLocalAt F x k) : PairFloorLocal F x := h

/-- **THE PER-COORDINATE EXODUS LEMMA.**  A single pair-suit coordinate of
the floor.  If its rung at `G` were smaller, the rank-`(rungAt G σ)` card of
that suit is (i) founded at `F`, (ii) unfounded at `G`, (iii) supported at `G`
by the exodus, (iv) next-up at `G` — exactly the local residual's input. -/
theorem floor_coordinate {F G : State} {x : Card} {σ : Suit}
    (hF : F.WF) (hG : G.WF) (hcls : sameOrbitSetoid.r F G)
    (hx : ForkWitness F x) (hsat : SSaturated G)
    (hσ : σ = x.suit ∨ σ = x.twin.suit)
    (hrF : rungAt F σ = x.rank.toIdx)
    (hloc : PairFloorLocal F x) :
    rungAt F σ ≤ rungAt G σ := by
  refine Nat.le_of_not_lt ?_
  intro hcon
  have hlt : rungAt G σ < x.rank.toIdx := by omega
  have hr13 : rungAt G σ < 13 := by
    have h := Rank.toIdx_lt x.rank
    omega
  let c : Card := ⟨σ, FoundKit.Rk (rungAt G σ)⟩
  have hcidx : c.rank.toIdx = rungAt G σ := FoundKit.Rk_toIdx _ hr13
  have hcsuit : c.suit = σ := rfl
  have hcF : c ∈ F.found c.suit := by
    apply FoundKit.mem_found_of_rung hF
    rw [hcidx, hcsuit, hrF]
    exact hlt
  have hcG : c ∉ G.found c.suit := by
    intro hmem
    have h := (FoundKit.mem_found_iff_height hG).mp hmem
    rw [hcidx] at h
    exact Nat.lt_irrefl _ h
  have hnext : G.nextUp c = true := by
    unfold State.nextUp State.foundHeight
    rw [hcidx]
    exact decide_eq_true rfl
  have hsup : ThirdHigh.Supported G c := by
    obtain ⟨-, -, play, hplay⟩ := hcls
    exact ThirdHigh.supported_of_forked_transit hF hplay (by
      intro hk
      have hk' : c.rank.toIdx = 12 := by rw [hk]; rfl
      have h12 := Rank.toIdx_lt x.rank
      omega) hcF hcG
  exact hloc (rungAt G σ) G c hG hsat hcls
    (by rcases hσ with h | h; exact Or.inl (by rw [hcsuit, h]); exact Or.inr (by rw [hcsuit, h]))
    hcidx hlt hcF hnext hsup

/-- **THE SECOND REDUCTION.**  `PairFloorLocal` (one card, at `G`) implies the
pair floor, on both pair suits, by `floor_coordinate` twice. -/
theorem fork_pair_floor_of_local {F G : State} {x : Card}
    (hF : F.WF) (hG : G.WF) (hcls : sameOrbitSetoid.r F G)
    (hx : ForkWitness F x) (hsat : SSaturated G) (hloc : PairFloorLocal F x) :
    rungAt F x.suit ≤ rungAt G x.suit ∧
      rungAt F x.twin.suit ≤ rungAt G x.twin.suit := by
  constructor
  · exact floor_coordinate hF hG hcls hx hsat (Or.inl rfl)
      (forkState_witness_rungs hx).1 hloc
  · exact floor_coordinate hF hG hcls hx hsat (Or.inr rfl)
      (forkState_witness_rungs hx).2 hloc

/-! ## §4. The bottom of the descent: rank index `0` -/

/-- A supported card of rank index `0` (an ace) tops its pile: nothing can sit
above an ace in a legal run (the card above would have rank index `-1`). -/
theorem top_of_supported_ace {st : State} (hwf : st.WF) {c : Card}
    (hc0 : c.rank.toIdx = 0) (hsup : ThirdHigh.Supported st c) :
    ∃ a, st.pileOfTop c = some a := by
  obtain ⟨z, hz⟩ := hsup
  obtain ⟨a, hhold, hbne, hlast⟩ := tfc_seatOf_of_inr hz
  have hmem : c ∈ (st.piles a).faceUp := pileHolding_mem hhold
  have hrok : runOK (st.piles a).faceUp = true := hwf.2.1 a
  obtain ⟨rest, hrest⟩ := fromCard_eq_head_of_mem hmem
  cases rest with
  | nil =>
      have hlastc : lastOf (st.piles a).faceUp = some c := by
        have h0 := tfc_below_fromCard c (st.piles a).faceUp
        rw [hrest] at h0
        rw [← h0]
        exact lastOf_snoc
      exact ⟨a, (pileOfTop_eq_some_iff hwf).2 hlastc⟩
  | cons e rest' =>
      exfalso
      have hface : (st.piles a).faceUp
          = below c (st.piles a).faceUp ++ c :: e :: rest' := by
        have h0 := tfc_below_fromCard c (st.piles a).faceUp
        rw [hrest] at h0
        exact h0.symm
      have hrok' : runOK (below c (st.piles a).faceUp ++ c :: e :: rest') = true := by
        rw [← hface]; exact hrok
      have hfit : canSitOn e c = true :=
        SeedKit.runOK_adjacent_fit c e (below c (st.piles a).faceUp) rest' hrok'
      obtain ⟨hr, -⟩ := (canSitOn_eq e c).mp hfit
      omega

/-- **THE LOCAL LEMMA AT RANK `0`.**  At any `WF`, S-saturated state, a
next-up supported card of rank index `0` does not exist: it is an ace (so it
tops its pile, `top_of_supported_ace`) and it has a card below (`Supported`),
so `CanRaise` fires and `CanRaiseS.now` contradicts saturation. -/
theorem no_supported_nextUp_zero {G : State} (hG : G.WF) (hsat : SSaturated G)
    {c : Card} (hc0 : c.rank.toIdx = 0) (hnext : G.nextUp c = true) :
    ¬ ThirdHigh.Supported G c := by
  intro hsup
  obtain ⟨a, hpa⟩ := top_of_supported_ace hG hc0 hsup
  obtain ⟨z, hz⟩ := hsup
  obtain ⟨aZ, hholdZ, hbneZ, hlastZ⟩ := tfc_seatOf_of_inr hz
  have hholdA : G.pileHolding c = some a :=
    (pileHolding_eq_some_iff hG).2 (lastOf_mem (pileOfTop_top hpa).2)
  have haZ : aZ = a := Option.some.inj (hholdZ.symm.trans hholdA)
  rw [haZ] at hlastZ
  -- `c` is the top and has something strictly below it
  obtain ⟨L, hL⟩ := lastOf_eq_snoc ((pileOfTop_top hpa).2)
  have hnd : (L ++ [c]).Nodup := by
    rw [← hL]
    exact runOK_nodup (hG.2.1 a)
  have hcL : c ∉ L := by
    intro hmem
    exact ((List.nodup_append.1 hnd).2.2 c hmem c (List.mem_singleton_self c)) rfl
  have hchop : chop (G.piles a).faceUp ≠ [] := by
    have hb : below c (G.piles a).faceUp = L := by
      rw [hL]
      exact below_snoc_not_mem hcL
    have hzmem : z ∈ below c (G.piles a).faceUp := lastOf_mem hlastZ
    have hLne : L ≠ [] := by
      intro hnil
      rw [hb, hnil] at hzmem
      exact absurd hzmem (by simp)
    rw [hL, chop_snoc]
    exact hLne
  have hcan : CanRaise G c := ⟨hnext, a, hpa, Or.inl hchop⟩
  exact hsat c (CanRaiseS.now c hcan)

/-- **The `k = 0` slice of the local residual, PROVED.** -/
theorem pairFloorLocalAt_zero (F : State) (x : Card) (hxK : x.rank.toIdx ≠ 0) :
    PairFloorLocalAt F x 0 := by
  intro G c hG hsat _ _ hc0 _ _ hnext hsup
  exact no_supported_nextUp_zero hG hsat hc0 hnext hsup


/-! ## §5. The rank descent -/

/-! ## §6. Seats and pile tops -/

/-- A card face-up directly above `c` is seated on `c`, hence supported. -/
theorem supported_of_above {G : State} (hG : G.WF) {a : Anchor} {P S : List Card}
    {c e : Card} (h : (G.piles a).faceUp = P ++ c :: e :: S) :
    ThirdHigh.Supported G e := by
  have hmem : e ∈ (G.piles a).faceUp := by rw [h]; simp
  have hhold : G.pileHolding e = some a := (pileHolding_eq_some_iff hG).2 hmem
  have hnd : (P ++ c :: e :: S).Nodup := by
    rw [← h]; exact runOK_nodup (hG.2.1 a)
  have heP : e ∉ P := fun hmemP =>
    ((List.nodup_append.1 hnd).2.2 e hmemP e (by simp)) rfl
  have hnd2 : (c :: e :: S).Nodup := (List.nodup_append.1 hnd).2.1
  have hec : e ≠ c := by
    intro hec'
    have hmemc : c ∈ e :: S := by rw [hec']; exact List.mem_cons_self ..
    exact (List.nodup_cons.mp hnd2).1 hmemc
  have heL : e ∉ P ++ [c] := by
    intro hmemL
    rcases List.mem_append.mp hmemL with h' | h'
    · exact heP h'
    · exact hec (List.mem_singleton.mp h')
  have hbelow : below e (G.piles a).faceUp = P ++ [c] := by
    rw [h, show P ++ c :: e :: S = (P ++ [c]) ++ e :: S from by simp [List.append_assoc]]
    exact ThirdHigh.below_append_cons_notmem heL S
  refine ⟨c, tfc_seatOf_inr_intro hhold ?_⟩
  rw [hbelow]
  exact lastOf_snoc

/-- A supported pile top has a nonempty chop: the card seated on it is
strictly below the top. -/
theorem chop_ne_nil_of_supported_top {G : State} (hG : G.WF) {c : Card} {a : Anchor}
    (hpa : G.pileOfTop c = some a) (hsup : ThirdHigh.Supported G c) :
    chop (G.piles a).faceUp ≠ [] := by
  obtain ⟨z, hz⟩ := hsup
  obtain ⟨aZ, hholdZ, hbneZ, hlastZ⟩ := tfc_seatOf_of_inr hz
  have hholdA : G.pileHolding c = some a :=
    (pileHolding_eq_some_iff hG).2 (lastOf_mem (pileOfTop_top hpa).2)
  have haZ : aZ = a := Option.some.inj (hholdZ.symm.trans hholdA)
  rw [haZ] at hlastZ
  obtain ⟨L, hL⟩ := lastOf_eq_snoc ((pileOfTop_top hpa).2)
  have hnd : (L ++ [c]).Nodup := by
    rw [← hL]
    exact runOK_nodup (hG.2.1 a)
  have hcL : c ∉ L := by
    intro hmem
    exact ((List.nodup_append.1 hnd).2.2 c hmem c (List.mem_singleton_self c)) rfl
  have hb : below c (G.piles a).faceUp = L := by
    rw [hL]
    exact below_snoc_not_mem hcL
  have hzmem : z ∈ below c (G.piles a).faceUp := lastOf_mem hlastZ
  have hLne : L ≠ [] := by
    intro hnil
    rw [hb, hnil] at hzmem
    exact absurd hzmem (by simp)
  rw [hL, chop_snoc]
  exact hLne

/-- At a saturated `WF` state, a supported pile top is not next-up. -/
theorem not_nextUp_of_supported_top {G : State} (hG : G.WF) (hsat : SSaturated G)
    {c : Card} {a : Anchor} (hpa : G.pileOfTop c = some a)
    (hsup : ThirdHigh.Supported G c) : ¬ G.nextUp c = true := by
  intro hnext
  have hcan : CanRaise G c := ⟨hnext, a, hpa, Or.inl (chop_ne_nil_of_supported_top hG hpa hsup)⟩
  exact hsat c (CanRaiseS.now c hcan)

/-- At a saturated `WF` state, a supported next-up card carries a card
directly above it (it is not a pile top). -/
theorem exists_above_of_supported_nextUp {G : State} (hG : G.WF) (hsat : SSaturated G)
    {c : Card} (hnext : G.nextUp c = true) (hsup : ThirdHigh.Supported G c) :
    ∃ (a : Anchor) (P S : List Card) (e : Card),
      (G.piles a).faceUp = P ++ c :: e :: S := by
  obtain ⟨z, hz⟩ := hsup
  obtain ⟨a, hhold, hbne, hlast⟩ := tfc_seatOf_of_inr hz
  have hmem : c ∈ (G.piles a).faceUp := pileHolding_mem hhold
  obtain ⟨rest, hrest⟩ := fromCard_eq_head_of_mem hmem
  cases rest with
  | cons e S =>
      have h0 := tfc_below_fromCard c (G.piles a).faceUp
      rw [hrest] at h0
      exact ⟨a, below c (G.piles a).faceUp, S, e, h0.symm⟩
  | nil =>
      exfalso
      -- `c` is the last card of the pile
      have hlastc : lastOf (G.piles a).faceUp = some c := by
        have h0 := tfc_below_fromCard c (G.piles a).faceUp
        rw [hrest] at h0
        rw [← h0]
        exact lastOf_snoc
      have hpa : G.pileOfTop c = some a := (pileOfTop_eq_some_iff hG).2 hlastc
      exact not_nextUp_of_supported_top hG hsat hpa ⟨z, hz⟩ hnext

/-! ## §7. The residual at `k = 1` -/

/-- **THE RESIDUAL AT RANK `1`, PROVED.**  A next-up supported card of rank
index `1` at a saturated `WF` state is impossible: the card above it has rank
index `0`; its rung is automatically `0` (it is face-up), so it is next-up,
supported, and of rank `0` — `no_supported_nextUp_zero`. -/
theorem no_supported_nextUp_one {G : State} (hG : G.WF) (hsat : SSaturated G)
    {c : Card} (hc1 : c.rank.toIdx = 1) (hnext : G.nextUp c = true) :
    ¬ ThirdHigh.Supported G c := by
  intro hsup
  obtain ⟨a, P, S, e, hface⟩ := exists_above_of_supported_nextUp hG hsat hnext hsup
  -- the card above sits on `c`: its rank index is `0`
  have heidx : e.rank.toIdx = 0 := by
    have hrok : runOK (G.piles a).faceUp = true := hG.2.1 a
    have hrok' : runOK (P ++ c :: e :: S) = true := by rw [← hface]; exact hrok
    have hfit : canSitOn e c = true := SeedKit.runOK_adjacent_fit c e P S hrok'
    obtain ⟨hr, -⟩ := (canSitOn_eq e c).mp hfit
    omega
  have hsupE : ThirdHigh.Supported G e := supported_of_above hG hface
  -- `e` is face-up at index `0`, so its suit rung is `0`: it is next-up
  have hrung0 : rungAt G e.suit = 0 := by
    have hmem : e ∈ (G.piles a).faceUp := by rw [hface]; simp
    have hle := piled_rung hG hmem
    omega
  have hnextE : G.nextUp e = true := by
    have hfh : e.rank.toIdx = G.foundHeight e.suit := by
      show e.rank.toIdx = (G.found e.suit).length
      rw [heidx]
      exact hrung0.symm
    unfold State.nextUp
    exact decide_eq_true hfh
  exact no_supported_nextUp_zero hG hsat heidx hnextE hsupE

/-- The residual at `k = 1` (with the class relation, vacuously unused). -/
theorem pairFloorLocalAt_one (F : State) (x : Card) : PairFloorLocalAt F x 1 := by
  intro G c hG hsat _ _ hc1 _ _ hnext hsup
  exact no_supported_nextUp_one hG hsat hc1 hnext hsup

/-! ## §8. The exact shape at `k = 2` -/

/-- **THE `k = 2` SHAPE.**  At a saturated `WF` state, a next-up supported
pair card `c` of rank index `2` carries EXACTLY ONE card above it: a card `e`
of rank index `1` and of the opposite colour family, whose own suit rung is
`0` (so `e` is a stranded top, not next-up).

No second card can sit above `c`: the next card would be a rank-0 card of
`c`'s colour family; if its suit is `c.suit` it is founded
(`rungAt G c.suit = 2 > 0`), and if it is `c.suit.twin` then its rung is `0`
so it is next-up, supported and of rank `0` — `no_supported_nextUp_zero`. -/
theorem two_shape {G : State} (hG : G.WF) (hsat : SSaturated G) {c : Card}
    (hc2 : c.rank.toIdx = 2) (hnext : G.nextUp c = true)
    (hsup : ThirdHigh.Supported G c) :
    ∃ (a : Anchor) (L : List Card) (e : Card),
      (G.piles a).faceUp = L ++ c :: [e] ∧
        e.rank.toIdx = 1 ∧ e.suit.color ≠ c.suit.color ∧
        rungAt G e.suit = 0 ∧ ¬ G.nextUp e = true := by
  obtain ⟨a, P, S, e, hface⟩ := exists_above_of_supported_nextUp hG hsat hnext hsup
  have hrok : runOK (G.piles a).faceUp = true := hG.2.1 a
  have hfitEC : canSitOn e c = true := by
    have hrok' : runOK (P ++ c :: e :: S) = true := by rw [← hface]; exact hrok
    exact SeedKit.runOK_adjacent_fit c e P S hrok'
  obtain ⟨heidx, hecol⟩ := (canSitOn_eq e c).mp hfitEC
  have heidx1 : e.rank.toIdx = 1 := by omega
  -- `c`'s own rung is `2` (it is next-up)
  have hc2r : rungAt G c.suit = 2 := by
    have hfh : c.rank.toIdx = G.foundHeight c.suit := by
      unfold State.nextUp at hnext
      exact of_decide_eq_true hnext
    simp only [State.foundHeight] at hfh
    show (G.found c.suit).length = 2
    rw [← hfh, hc2]
  -- nothing sits above `e`: the next card would have rank index `-1`, and if
  -- it did sit there it would be a founded pair card or a live rank-`0` card
  have hS : S = [] := by
    cases S with
    | nil => rfl
    | cons e2 S' =>
        exfalso
        have hrok2 : runOK (P ++ c :: e :: e2 :: S') = true := by
          rw [← hface]; exact hrok
        have hfitE2 : canSitOn e2 e = true :=
          SeedKit.runOK_adjacent_fit e e2 (P ++ [c]) S' (by
            simpa [List.append_assoc] using hrok2)
        obtain ⟨he2idx, he2col⟩ := (canSitOn_eq e2 e).mp hfitE2
        have he2idx0 : e2.rank.toIdx = 0 := by omega
        have hcol : e2.suit.color = c.suit.color :=
          ThirdHigh.color_eq_of_ne he2col hecol
        -- nothing can sit above a rank-`0` card
        have hS' : S' = [] := by
          cases S' with
          | nil => rfl
          | cons e3 S'' =>
              exfalso
              have hrok3 : runOK (P ++ c :: e :: e2 :: e3 :: S'') = true := by
                rw [← hface]; exact hrok
              have hfit3 : canSitOn e3 e2 = true :=
                SeedKit.runOK_adjacent_fit e2 e3 (P ++ [c, e]) S'' (by
                  simpa [List.append_assoc] using hrok3)
              obtain ⟨he3idx, -⟩ := (canSitOn_eq e3 e2).mp hfit3
              omega
        subst hS'
        -- `e2` is now the pile top and is supported by `e`
        have hlastE2 : lastOf (G.piles a).faceUp = some e2 := by
          rw [hface]
          rw [show P ++ c :: e :: e2 :: ([] : List Card) = (P ++ [c, e]) ++ [e2] from by
            simp [List.append_assoc]]
          exact lastOf_snoc
        have hsup2 : ThirdHigh.Supported G e2 :=
          supported_of_above hG (a := a) (P := P ++ [c]) (S := []) (c := e) (by
            rw [hface]
            simp [List.append_assoc])
        have hmem2 : e2 ∈ (G.piles a).faceUp := by rw [hface]; simp
        rcases SeedKit.suit_family hcol with hs | hs
        · -- `e2` on the pair suit itself: founded (index `0` < rung `2`)
          have hfound : e2 ∈ G.found e2.suit := by
            apply FoundKit.mem_found_of_rung hG
            rw [hs]
            omega
          exact ((mem_faceUp_only hG hmem2).2.2.2.2 e2.suit) hfound
        · -- `e2` on the twin pair suit: rung `0`, so next-up, supported,
          -- rank `0` — `no_supported_nextUp_zero`
          have hrung0 : rungAt G e2.suit = 0 := by
            have hle := piled_rung hG hmem2
            omega
          have hnext2 : G.nextUp e2 = true := by
            have hfh : e2.rank.toIdx = G.foundHeight e2.suit := by
              simp only [State.foundHeight]
              rw [he2idx0]
              exact hrung0.symm
            unfold State.nextUp
            exact decide_eq_true hfh
          exact no_supported_nextUp_zero hG hsat he2idx0 hnext2 hsup2
  -- the shape, and `e` is a stranded (non-next-up) top
  have hface' : (G.piles a).faceUp = P ++ c :: [e] := by rw [hface, hS]
  have hlastE : lastOf (G.piles a).faceUp = some e := by
    rw [hface']
    rw [show P ++ c :: [e] = (P ++ [c]) ++ [e] from by simp [List.append_assoc]]
    exact lastOf_snoc
  have hpaE : G.pileOfTop e = some a := (pileOfTop_eq_some_iff hG).2 hlastE
  have hsupE : ThirdHigh.Supported G e := supported_of_above hG (by rw [hface'])
  have hnnext : ¬ G.nextUp e = true := not_nextUp_of_supported_top hG hsat hpaE hsupE
  have heface : e ∈ (G.piles a).faceUp := by rw [hface']; simp
  have hle := piled_rung hG heface
  have hrung0 : rungAt G e.suit = 0 := by
    by_cases hr : rungAt G e.suit = 1
    · exfalso
      apply hnnext
      have hfh : e.rank.toIdx = G.foundHeight e.suit := by
        simp only [State.foundHeight]
        rw [heidx1]
        exact hr.symm
      unfold State.nextUp
      exact decide_eq_true hfh
    · omega
  exact ⟨a, P, e, hface', heidx1, hecol, hrung0, hnnext⟩
/-! ## §9. Packaging: the residual is exactly its `k ≥ 2` half -/

/-- **THE RESIDUAL SPLIT.**  The local residual equals its `0`, `1`, and
`≥ 2` slices; the first two are theorems (`pairFloorLocalAt_zero`,
`pairFloorLocalAt_one`), so the pair floor is reduced to the `k ≥ 2` slice —
the part the rank descent cannot close (`two_shape` shows the `k = 2` shape is
realizable at a saturated state outside the class). -/
theorem pairFloorLocal_of_ge_two {F : State} {x : Card}
    (h2 : ∀ k : Nat, 2 ≤ k → PairFloorLocalAt F x k) (hxK : x.rank.toIdx ≠ 0) :
    PairFloorLocal F x := by
  intro k
  rcases Nat.lt_or_ge k 2 with hk | hk
  · have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with rfl | rfl
    · exact pairFloorLocalAt_zero F x hxK
    · exact pairFloorLocalAt_one F x
  · exact h2 k hk

/-- **THE PAIR FLOOR FROM THE `k ≥ 2` RESIDUAL.**  The end-to-end statement:
the `k ≥ 2` local residual plus the two proved bottom slices give
`fork_pair_floor`. -/
theorem fork_pair_floor_of_ge_two {F G : State} {x : Card}
    (hF : F.WF) (hG : G.WF) (hcls : sameOrbitSetoid.r F G)
    (hx : ForkWitness F x) (hsat : SSaturated G)
    (h2 : ∀ k : Nat, 2 ≤ k → PairFloorLocalAt F x k) :
    rungAt F x.suit ≤ rungAt G x.suit ∧
      rungAt F x.twin.suit ≤ rungAt G x.twin.suit :=
  fork_pair_floor_of_local hF hG hcls hx hsat
    (pairFloorLocal_of_ge_two h2 (by
      intro h0
      have hlt := (forkState_witness_rungs hx).1
      -- a fork always has rank index at least 2 (`ThirdRigid.fork_rank_ge_two`)
      have h2r := ThirdRigid.fork_rank_ge_two hF hx
      omega))

/-! ## §10. Axiom audit -/

#print axioms fork_pair_floor_of_fork
#print axioms fork_pair_floor_of_fork'
#print axioms twinLivePairB_iff
#print axioms forkWitnessB_iff
#print axioms forkExistsB_true
#print axioms forkExistsB_false
#print axioms fork_pair_floor_of_nonfork
#print axioms nonfork_of_fork_pair_floor
#print axioms floor_coordinate
#print axioms fork_pair_floor_of_local
#print axioms top_of_supported_ace
#print axioms no_supported_nextUp_zero
#print axioms pairFloorLocalAt_zero
#print axioms supported_of_above
#print axioms chop_ne_nil_of_supported_top
#print axioms not_nextUp_of_supported_top
#print axioms exists_above_of_supported_nextUp
#print axioms no_supported_nextUp_one
#print axioms pairFloorLocalAt_one
#print axioms two_shape
#print axioms pairFloorLocal_of_ge_two
#print axioms fork_pair_floor_of_ge_two

end ForkFloor
