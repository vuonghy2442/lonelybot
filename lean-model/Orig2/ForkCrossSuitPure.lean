import Orig2.ForkCrossSuit
import Orig2.ForkDirect

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkCrossSuitPure - the pull-free (pure) cross-suit corridor

**REFUTED — KERNEL-CERTIFIED.**  `Cert.not_crossSuitPureCorridorResidual`
(`Archive/Cert/ForkCertMain.lean`, leaf chain, build `Tools/build_crosssuit_cert.ps1`)
gives a shortest saturated→saturated play with `inv = 8`; its corridors are
clean but have a non-free window, so this card's residual and
`CrossSuitInnerRaiseResidual` do not cover it — the cross-suit case is REAL.
Do not cite the residuals here as dischargeable.

Source card (`Orig2/`).  Zero `sorry`, zero `Classical.choice`, zero
`native_decide`; axiom battery at the tail.

## The target

```text
CrossSuit.CrossSuitPureCorridorResidual        (Orig2/ForkCrossSuit.lean:586)
```

`ForkCrossSuit` reduced `crossSuitVacuity` to
`SameCardFreeInteriorShortens + CrossSuitPureCorridorResidual`, and showed
that a clean corridor which pulls at all pulls the raised card at its first
pull (`corridor_pull_is_c`), so the same-card lane eats it.  The surviving
shape is the **pull-free** corridor

```text
ρ = (pre ++ raise c :: γ) ++ pull d b :: tail,    c.suit ≠ d.suit,
γ pull-free,  γ clean at (c, d).
```

## What this card proves

* **§1 (THE STRUCTURE THEOREM, unconditional).**  A clean pull-free corridor
  has **at most one non-free letter**, and if it has one it is `raise d`
  itself, after which the interior is free
  (`pure_corridor_last_nonfree`, `pure_corridor_shape`).  Proof: the last
  non-free letter of `γ` must be a raise of suit `d.suit` (clean +
  pull-free); free letters after it preserve the `d`-column, so at the pull's
  origin the `d`-foundation top is exactly that raised card; the pull's own
  step forces that card to be `d`.  No same-card hypothesis is used.

  So every raise in a pure corridor other than a final `raise d` is
  impossible — in particular the whole "raises of the pull's suit" side of
  the corridor collapses.  The same argument works with pulls allowed
  (`corridor_last_d_raise`): in **any** clean cross-suit corridor the pull's
  column is touched by at most one raise, and it is `raise d`.

* **§2 (THE EQUIVALENCE, conditional — and FLAGGED).**  Under the assumed
  same-card lane
  `SameCardFreeInteriorShortens`, a surviving `raise d ; (free) ; pull d`
  inside the corridor *is* a same-card raise-before-pull pair and shortens
  the play against minimality.  Hence the pure corridor's interior is
  **entirely free** (`freeOnly_of_sameCard`), and the pure residual is
  **equivalent** to the free-corridor residual

  ```text
  CrossSuitFreeCorridorResidual :
    no minimal SSaturated→SSaturated play has  raise c ; (free*) ; pull d
    with c.suit ≠ d.suit            (`freeResidual_of_pure`, `pureResidual_of_free`).
  ```

  `CrossSuitFreeCorridorResidual` is strictly weaker than the pure residual
  (`freeResidual_of_pure` is a specialization: a free interior is clean and
  pull-free for free) and equivalent to it given the same-card lane.

  **FLAG (see `Temp/Pure_Report.md` §4): the probe exhibits a unit-shortest
  `SSaturated`-to-`SSaturated` play on the census board `F_t1_runshiftp2`
  containing `raise 5C ; slide 5S ; pull 5C` (a relocation with a FREE
  interior).  So `SameCardFreeInteriorShortens` is FALSE as stated and this
  conditional route is vacuous.**  The honest reduction is the same-card-free
  split of §2' (`CrossSuitFreeCorridorResidual` + `CrossSuitInnerRaiseResidual`
  implies the pure residual), which §1 makes exhaustive.

* **§3 (THE CAMPAIGN STATEMENT).**
  `crossSuitVacuity` follows from `CrossSuitFreeCorridorResidual` and
  `CrossSuitInnerRaiseResidual` (plus the campaign's same-card lane, used only
  for the corridors that pull): `crossSuitVacuity_of_free_and_inner`; and from
  the conditional route `crossSuitVacuity_of_freeCorridor`.

* **§4 (the corridor's endpoint facts).**  In a free corridor the pull's
  origin has `foundTop d.suit = some d` (`corridor_pull_top`, any corridor)
  and `foundTop c.suit = some c` (`free_corridor_c_top`, free interior): the
  pulled card and the raised card are the two relevant column tops at the
  very moment the cross-suit pair fires — the two-column picture the twin
  lock of `Temp/MtnRef_Report.md` §3 reads.  Plus the ledger row
  `last_pull_card_re_raised`: the last pull of a play ending saturated is
  always paid back by a raise of its card or its twin in the pull-free tail.

Evidence (probes `Temp/Pure_probe.py`, `Temp/Pure_probe2.py`,
`Temp/Pure_probe4.py`): free cross-suit corridors are **real and common** in
unit-shortest witness plays between arbitrary states (144/156 sampled sources
on the 13-board census carry one; interior lengths 0–3), while **none** occurs
between `SSaturated` pairs (CROSS = 0, PURE = 0, FREE = 0 over all 104
saturated ordered pairs of the 13 census boards).  The two M1 hits at
saturated pairs there (board `F_t1_runshiftp2`) are same-suit relocations —
cross-suit vacuity is untouched.  So the residual is exactly the saturation
lock, not a syntactic impossibility, and it cannot be reduced to the
*adjacent* pair by deletion.  (The `MtnRef` §3 twin-lock argument is *not* a
sound route to the lock: the same board's relocation play is its
counterexample — report §3.1/§4.)
-/

namespace CrossSuit

open ValleyElim

/-!
## §0. Free interiors
-/

/-- **`FreeOnly γ`** — every letter of the corridor is free (`draw` or a
tableau slide). -/
def FreeOnly (γ : List Move) : Prop := ∀ m ∈ γ, FreeMove m

theorem freeOnly_nil : FreeOnly [] := by
  intro m hm
  exact absurd hm (by simp)

theorem freeOnly_cons {m : Move} {γ : List Move} (hm : FreeMove m)
    (h : FreeOnly γ) : FreeOnly (m :: γ) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hm
  · exact h x hx

theorem freeOnly_append {γ₁ γ₂ : List Move} (h₁ : FreeOnly γ₁)
    (h₂ : FreeOnly γ₂) : FreeOnly (γ₁ ++ γ₂) := by
  intro m hm
  rcases List.mem_append.mp hm with hm | hm
  · exact h₁ m hm
  · exact h₂ m hm

theorem freeOnly_left {γ₁ γ₂ : List Move} (h : FreeOnly (γ₁ ++ γ₂)) :
    FreeOnly γ₁ :=
  fun m hm => h m (List.mem_append.mpr (Or.inl hm))

theorem freeOnly_right {γ₁ γ₂ : List Move} (h : FreeOnly (γ₁ ++ γ₂)) :
    FreeOnly γ₂ :=
  fun m hm => h m (List.mem_append.mpr (Or.inr hm))

theorem freeOnly_of_all_isFreeB {γ : List Move} (h : γ.all isFreeB = true) :
    FreeOnly γ :=
  fun m hm => isFreeB_eq_true_iff.mp (List.all_eq_true.mp h m hm)

theorem all_isFreeB_of_freeOnly {γ : List Move} (h : FreeOnly γ) :
    γ.all isFreeB = true := by
  apply List.all_eq_true.mpr
  intro m hm
  exact isFreeB_eq_true_iff.mpr (h m hm)

/-- A free corridor pulls nothing. -/
theorem freeOnly_pullFree {γ : List Move} (h : FreeOnly γ) : PullFree γ := by
  intro e b hmem
  rcases h (Move.foundToTab e b) hmem with hd | ⟨x, bb, hx⟩
  · cases hd
  · cases hx

/-- A free corridor avoids every suit. -/
theorem freeOnly_avoids {γ : List Move} {σ : Suit} (h : FreeOnly γ) :
    ∀ m ∈ γ, AvoidsSuit σ m := by
  intro m hm
  rcases h m hm with hd | ⟨x, bb, hx⟩
  · rw [hd]; exact trivial
  · rw [hx]; exact trivial

/-- A free corridor is clean at every pair of cards. -/
theorem freeOnly_corridorClean {γ : List Move} {c d : Card} (h : FreeOnly γ) :
    CorridorClean γ c d := by
  refine ⟨?_, ?_⟩
  · intro e he
    rcases h (Move.tabToFound e) he with hd | ⟨x, bb, hx⟩
    · cases hd
    · cases hx
  · intro e b he
    exact absurd he (freeOnly_pullFree h e b)

/-- Free letters contribute no raise of any suit. -/
theorem raisesOf_eq_zero_of_free {γ : List Move} {σ : Suit} (h : FreeOnly γ) :
    raisesOf γ σ = 0 := by
  induction γ with
  | nil => rfl
  | cons m t ih =>
      have hm : FreeMove m := h m (List.mem_cons_self ..)
      have ht : FreeOnly t := fun x hx => h x (List.mem_cons_of_mem m hx)
      rcases hm with rfl | ⟨x, bb, rfl⟩
      · exact ih ht
      · exact ih ht

/-- Free letters contribute no pull of any suit. -/
theorem pullsOf_eq_zero_of_free {γ : List Move} {σ : Suit} (h : FreeOnly γ) :
    pullsOf γ σ = 0 := by
  induction γ with
  | nil => rfl
  | cons m t ih =>
      have hm : FreeMove m := h m (List.mem_cons_self ..)
      have ht : FreeOnly t := fun x hx => h x (List.mem_cons_of_mem m hx)
      rcases hm with rfl | ⟨x, bb, rfl⟩
      · exact ih ht
      · exact ih ht

/-!
## §1. The structure of a pure corridor: at most one non-free letter
-/

/-- The indicator of a `σ`-suit raise letter. -/
def isSuitRaiseB (σ : Suit) : Move → Bool
  | Move.tabToFound x => decide (x.suit = σ)
  | _ => false

/-- **THE LAST `σ`-SUIT RAISE.**  A list that carries a raise of a card of suit
`σ` splits at its **last** such raise; nothing after it raises a `σ` card.
Constructive: the search is `exists_last_bool` at the Boolean indicator. -/
theorem exists_last_suit_raise (γ : List Move) (σ : Suit)
    (h : ∃ e : Card, Move.tabToFound e ∈ γ ∧ e.suit = σ) :
    ∃ γ₁ γ₂ : List Move, ∃ e : Card,
      γ = γ₁ ++ Move.tabToFound e :: γ₂ ∧ e.suit = σ ∧
        (∀ x : Card, Move.tabToFound x ∈ γ₂ → x.suit ≠ σ) := by
  obtain ⟨e₀, he₀, hs₀⟩ := h
  have hany : γ.any (isSuitRaiseB σ) = true :=
    any_eq_true_of_mem he₀
      (show isSuitRaiseB σ (Move.tabToFound e₀) = true from decide_eq_true hs₀)
  obtain ⟨γ₁, m, γ₂, hγ, hβ, hm⟩ := exists_last_bool (isSuitRaiseB σ) γ hany
  have hmform : ∃ e : Card, m = Move.tabToFound e ∧ e.suit = σ := by
    cases m with
    | draw => exact absurd hm (by simp [isSuitRaiseB])
    | wasteToFound x => exact absurd hm (by simp [isSuitRaiseB])
    | wasteToTab x b => exact absurd hm (by simp [isSuitRaiseB])
    | foundToTab x b => exact absurd hm (by simp [isSuitRaiseB])
    | tabToTab x b => exact absurd hm (by simp [isSuitRaiseB])
    | tabToFound x => exact ⟨x, rfl, of_decide_eq_true hm⟩
  obtain ⟨e, rfl, hes⟩ := hmform
  refine ⟨γ₁, γ₂, e, hγ, hes, ?_⟩
  intro x hx hxs
  have hf : isSuitRaiseB σ (Move.tabToFound x) = false := hβ _ hx
  have htrue : isSuitRaiseB σ (Move.tabToFound x) = true := decide_eq_true hxs
  rw [hf] at htrue
  exact Bool.false_ne_true htrue

/-- **THE GENERAL CORRIDOR STRUCTURE.**  In a **clean cross-suit corridor** —
pulls allowed — the column of the *pulled* suit can be touched by at most one
raise inside the corridor, and if it is, that raise is `raise d` itself, after
which every letter avoids the `d`-column (free letters and the corridor's own
`c`-suit pulls, `c.suit ≠ d.suit`).

This is `pure_corridor_last_nonfree` without the `PullFree` hypothesis: the
corridor's pulls are all of suit `c`, so they never disturb the `d`-column. -/
theorem corridor_last_d_raise
    {u v : State} {pre γ tail : List Move} {c d : Card} {b : Base}
    (hplay : ShufflePlayW u
      ((pre ++ Move.tabToFound c :: γ) ++ Move.foundToTab d b :: tail) v)
    (hclean : CorridorClean γ c d) (hne : c.suit ≠ d.suit)
    (h : ∃ e : Card, Move.tabToFound e ∈ γ ∧ e.suit = d.suit) :
    ∃ γ₁ γ₂ : List Move, γ = γ₁ ++ Move.tabToFound d :: γ₂ ∧
      (∀ m ∈ γ₂, AvoidsSuit d.suit m) := by
  obtain ⟨γ₁, γ₂, e, hγ, hes, hlast⟩ := exists_last_suit_raise γ d.suit h
  -- every letter after the last `d`-raise avoids the `d`-column
  have havoid : ∀ m ∈ γ₂, AvoidsSuit d.suit m := by
    intro m hm
    cases m with
    | draw => exact trivial
    | tabToTab x bb => exact trivial
    | wasteToFound x => exact trivial
    | wasteToTab x bb => exact trivial
    | tabToFound x =>
        exact hlast x hm
    | foundToTab x bb =>
        have hmem : Move.foundToTab x bb ∈ γ := by
          rw [hγ]
          exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hm))
        have hx : x.suit = c.suit := hclean.2 x bb hmem
        show x.suit ≠ d.suit
        rw [hx]
        exact hne
  rw [hγ] at hplay
  -- split before the raise `e`, then inside the corridor
  obtain ⟨Q₀, -, hrest⟩ := ShufflePlayW_split hplay
    (pre ++ Move.tabToFound c :: γ₁)
    (Move.tabToFound e :: (γ₂ ++ Move.foundToTab d b :: tail))
    (by simp only [List.append_assoc, List.cons_append])
  obtain ⟨Q, -, hstepE, htail⟩ := Bubble.walk_cons_inv hrest
  obtain ⟨-, a, -, hs⟩ := step_tabToFound_inv hstepE
  have hQ : Q = raiseSt Q₀ e a := by rw [hs]; rfl
  have hQtop : Q.foundTop d.suit = some e := by
    rw [hQ, ← hes]; exact BaseEn.foundTop_raiseSt_self Q₀ e a
  obtain ⟨P, hfreeplay, hpull⟩ := ShufflePlayW_split htail γ₂
    (Move.foundToTab d b :: tail) rfl
  have hPtop : P.foundTop d.suit = some e := by
    rw [foundTop_eq_of_avoids hfreeplay havoid, hQtop]
  obtain ⟨B, -, hstepP, -⟩ := Bubble.walk_cons_inv hpull
  obtain ⟨c', htop, hc', -, -⟩ := step_foundToTab_inv hstepP
  have hed : e = d := by
    have h1 : some e = some c' := hPtop.symm.trans htop
    exact (Option.some.inj h1).trans hc'
  exact ⟨γ₁, γ₂, by rw [hγ, hed], havoid⟩

/-- **THE LAST NON-FREE LETTER OF A PURE CORRIDOR IS `raise d`.**

A clean, pull-free corridor ending in `pull d b` carries **at most one
non-free letter**, and if it carries one it is `raise d` itself, followed by
free letters only.

Take the corridor's *last* non-free letter `m`.  It is not a pull
(`PullFree`), so it is a raise `e` with `e.suit = d.suit` (`CorridorClean`).
Every letter after it is free, hence preserves the foundation, so at the
pull's origin the `d`-foundation top is `e`; the pull's own step requires
that top to be `d` — so `e = d`. -/
theorem pure_corridor_last_nonfree
    {u v : State} {pre γ tail : List Move} {c d : Card} {b : Base}
    (hplay : ShufflePlayW u
      ((pre ++ Move.tabToFound c :: γ) ++ Move.foundToTab d b :: tail) v)
    (hclean : CorridorClean γ c d) (hpf : PullFree γ)
    (hnf : ∃ m ∈ γ, ¬ FreeMove m) :
    ∃ γ₁ γ₂ : List Move, γ = γ₁ ++ Move.tabToFound d :: γ₂ ∧ FreeOnly γ₂ := by
  obtain ⟨γ₁, m, γ₂, hγ, hfree₂, hnfm⟩ := exists_last_nonfree γ hnf
  -- the letter lies in the play
  have hmemγ : m ∈ γ := by
    rw [hγ]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  have hmemρ : m ∈ (pre ++ Move.tabToFound c :: γ) ++ Move.foundToTab d b :: tail := by
    have h2 : m ∈ Move.tabToFound c :: γ := List.mem_cons_of_mem _ hmemγ
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h2)))
  obtain ⟨st, hrev⟩ := shuffle_letter_reversible hplay m hmemρ
  rcases nonfree_reversible_is_pull_or_raise hrev hnfm with ⟨e, he⟩ | ⟨e, b', he⟩
  · -- the letter is a raise of `e`, and `e.suit = d.suit` (clean)
    have hmemγ' : Move.tabToFound e ∈ γ := by rw [← he]; exact hmemγ
    have hes : e.suit = d.suit := hclean.1 e hmemγ'
    have hγ' : γ = γ₁ ++ Move.tabToFound e :: γ₂ := by rw [hγ, he]
    rw [hγ'] at hplay
    -- split the play before the raise `e`
    obtain ⟨Q₀, hpre, hrest⟩ := ShufflePlayW_split hplay
      (pre ++ Move.tabToFound c :: γ₁)
      (Move.tabToFound e :: (γ₂ ++ Move.foundToTab d b :: tail))
      (by simp only [List.append_assoc, List.cons_append])
    obtain ⟨Q, -, hstepE, htail⟩ := Bubble.walk_cons_inv hrest
    -- `Q` is the raise's image; `Q.foundTop e.suit = some e`
    obtain ⟨-, a, -, hs⟩ := step_tabToFound_inv hstepE
    have hQ : Q = raiseSt Q₀ e a := by rw [hs]; rfl
    have hQtop : Q.foundTop e.suit = some e := by
      rw [hQ]; exact BaseEn.foundTop_raiseSt_self Q₀ e a
    -- the free remainder of the corridor
    obtain ⟨P, hfreeplay, hpull⟩ := ShufflePlayW_split htail γ₂
      (Move.foundToTab d b :: tail) rfl
    have hPtop : P.foundTop d.suit = some e := by
      rw [foundTop_eq_of_avoids hfreeplay (freeOnly_avoids hfree₂), ← hes]
      exact hQtop
    -- the pull's step reads the top
    obtain ⟨B, -, hstepP, -⟩ := Bubble.walk_cons_inv hpull
    obtain ⟨c', htop, hc', -, -⟩ := step_foundToTab_inv hstepP
    have hed : e = d := by
      have h1 : some e = some c' := hPtop.symm.trans htop
      exact (Option.some.inj h1).trans hc'
    exact ⟨γ₁, γ₂, by rw [hγ, he, hed], hfree₂⟩
  · -- a pull cannot sit in a pull-free corridor
    have hmem : Move.foundToTab e b' ∈ γ := by rw [← he]; exact hmemγ
    exact absurd hmem (hpf e b')

/-- **THE PURE CORRIDOR IS ALL-FREE, OR ENDS IN `raise d`.**  The
disjunctive face of `pure_corridor_last_nonfree`. -/
theorem pure_corridor_shape
    {u v : State} {pre γ tail : List Move} {c d : Card} {b : Base}
    (hplay : ShufflePlayW u
      ((pre ++ Move.tabToFound c :: γ) ++ Move.foundToTab d b :: tail) v)
    (hclean : CorridorClean γ c d) (hpf : PullFree γ) :
    FreeOnly γ ∨ ∃ γ₁ γ₂ : List Move, γ = γ₁ ++ Move.tabToFound d :: γ₂ ∧
      FreeOnly γ₂ := by
  by_cases hall : γ.all isFreeB = true
  · exact Or.inl (freeOnly_of_all_isFreeB hall)
  · exact Or.inr (pure_corridor_last_nonfree hplay hclean hpf
      (exists_nonfree_of_not_all_free γ
        (fun h => hall (all_isFreeB_of_freeOnly h))))

/-!
## §2. The same-card lane kills the last `raise d`

So the pure residual is exactly the free-corridor residual.
-/

/-- **A PURE CORRIDOR'S INTERIOR IS FREE** (given the same-card lane).

If `γ` still carried a `raise d`, the play would contain the same-card pair
`raise d ; … ; pull d` — with the rest of the corridor (pull-free, hence
free by §1) as its interior — and `SameCardFreeInteriorShortens` would
produce a strictly shorter play, against minimality. -/
theorem freeOnly_of_sameCard (hsc : SameCardFreeInteriorShortens)
    {u v : State} {ρ pre γ tail : List Move} {c d : Card} {b : Base}
    (huwf : u.WF) (hplay : ShufflePlayW u ρ v)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length)
    (heq : ρ = (pre ++ Move.tabToFound c :: γ) ++ Move.foundToTab d b :: tail)
    (hclean : CorridorClean γ c d) (hpf : PullFree γ) :
    FreeOnly γ := by
  by_cases hall : γ.all isFreeB = true
  · exact freeOnly_of_all_isFreeB hall
  · obtain ⟨γ₁, γ₂, hγ, hfree₂⟩ :=
      pure_corridor_last_nonfree (heq ▸ hplay) hclean hpf
        (exists_nonfree_of_not_all_free γ
          (fun h => hall (all_isFreeB_of_freeOnly h)))
    have heq' : ρ = ((pre ++ Move.tabToFound c :: γ₁) ++ Move.tabToFound d ::
        γ₂) ++ Move.foundToTab d b :: tail := by
      rw [heq, hγ]
      simp only [List.append_assoc, List.cons_append]
    obtain ⟨ρ', hρ', hlen'⟩ :=
      hsc u v ρ (pre ++ Move.tabToFound c :: γ₁) γ₂ tail d b huwf hplay heq'
    exact absurd hlen' (Nat.not_lt.mpr (hmin ρ' hρ'))

/-- **THE FREE-CORRIDOR RESIDUAL** — the exact residual.

A minimal witness play between `SSaturated` `WF` endpoints carries no
cross-suit pair of the shape

```text
raise c ; (free letters) ; pull d      (c.suit ≠ d.suit).
```

No cleanliness/pull-freeness hypotheses are needed: a free interior has both
for free (`freeOnly_corridorClean`, `freeOnly_pullFree`). -/
def CrossSuitFreeCorridorResidual : Prop :=
  ∀ (u v : State) (ρ pre γ tail : List Move) (c d : Card) (b : Base),
    u.WF → SSaturated u → SSaturated v → ShufflePlayW u ρ v →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
    ρ = (pre ++ Move.tabToFound c :: γ) ++ Move.foundToTab d b :: tail →
    c.suit ≠ d.suit → FreeOnly γ → False

/-- A pure corridor is a free corridor with extra hypotheses: the free
residual is *weaker*. -/
theorem freeResidual_of_pure (h : CrossSuitPureCorridorResidual) :
    CrossSuitFreeCorridorResidual := by
  intro u v ρ pre γ tail c d b hwf hu hv hplay hmin heq hne hfree
  exact h u v ρ pre γ tail c d b hwf hu hv hplay hmin heq hne
    (freeOnly_corridorClean hfree) (freeOnly_pullFree hfree)

/-- **THE EQUIVALENCE, one direction**: the pure residual follows from the
free-corridor residual plus the same-card lane (§2). -/
theorem pureResidual_of_free (h : CrossSuitFreeCorridorResidual)
    (hsc : SameCardFreeInteriorShortens) : CrossSuitPureCorridorResidual := by
  intro u v ρ pre γ tail c d b hwf hu hv hplay hmin heq hne hclean hpf
  exact h u v ρ pre γ tail c d b hwf hu hv hplay hmin heq hne
    (freeOnly_of_sameCard hsc hwf hplay hmin heq hclean hpf)

/-- **THE PURE RESIDUAL IS *IS* THE FREE-CORRIDOR RESIDUAL** (given the
same-card lane).  §1–§2: the only non-free letters a clean pull-free corridor
can carry are a final `raise d`, and those are exactly the same-card pairs the
same-card lane shortens.

FLAG (see `Temp/Pure_Report.md` §4): the probe finds a unit-shortest play
between two `SSaturated` states on the census board `F_t1_runshiftp2` which
contains `raise 5C ; slide 5S ; pull 5C` (a relocation), so
`SameCardFreeInteriorShortens` is FALSE as stated and this route is vacuous
in practice.  The honest split is `pureResidual_of_split` (§2', no same-card
hypothesis). -/
theorem pureResidual_iff_free (hsc : SameCardFreeInteriorShortens) :
    CrossSuitPureCorridorResidual ↔ CrossSuitFreeCorridorResidual :=
  ⟨freeResidual_of_pure, fun h => pureResidual_of_free h hsc⟩

/-! ### §2'. The honest split: free interior, or an inner `raise d`

§1 says a pure corridor is `raise c ; γ₁ ; [raise d] ; γ₂ ; pull d` with
`γ₂` free.  The two branches are the whole residual, and there is **no**
same-card hypothesis in the split. -/

/-- **THE INNER-RAISE RESIDUAL.**  A minimal `SSaturated`→`SSaturated` play
never carries the *second* pure-corridor shape §1 leaves open: a
cross-suit raise `c`, a clean pull-free stretch, then an inner same-card
`raise d ; (free) ; pull d` whose pull is the corridor's pull.

(This is the "twin-seat / relocation" face of the corridor: `d` is raised
from the tableau and comes straight back down - through the foundation - onto
the base the interior exposes.)

**REFUTED — KERNEL-CERTIFIED** (see the file header): the counterexample
corridor has a non-free window, so it is not this shape; the broad cross-suit
premise is false. -/
def CrossSuitInnerRaiseResidual : Prop :=
  ∀ (u v : State) (ρ pre γ₁ γ₂ tail : List Move) (c d : Card) (b : Base),
    u.WF → SSaturated u → SSaturated v → ShufflePlayW u ρ v →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
    ρ = ((pre ++ Move.tabToFound c :: γ₁) ++ Move.tabToFound d :: γ₂) ++
      Move.foundToTab d b :: tail →
    c.suit ≠ d.suit →
    (∀ e : Card, Move.tabToFound e ∈ γ₁ → e.suit = d.suit) →
    (∀ (e : Card) (b' : Base), Move.foundToTab e b' ∈ γ₁ → False) →
    FreeOnly γ₂ → False

/-- **THE SPLIT OF THE PURE RESIDUAL.**  §1 makes the two branches
exhaustive; each is a strictly narrower residual than the pure corridor. -/
theorem pureResidual_of_split (hfree : CrossSuitFreeCorridorResidual)
    (hinner : CrossSuitInnerRaiseResidual) : CrossSuitPureCorridorResidual := by
  intro u v ρ pre γ tail c d b hwf hu hv hplay hmin heq hne hclean hpf
  rcases pure_corridor_shape (heq ▸ hplay) hclean hpf with hfreeγ | ⟨γ₁, γ₂, hγ, hfree₂⟩
  · exact hfree u v ρ pre γ tail c d b hwf hu hv hplay hmin heq hne hfreeγ
  · have heq' : ρ = ((pre ++ Move.tabToFound c :: γ₁) ++ Move.tabToFound d :: γ₂) ++
        Move.foundToTab d b :: tail := by
      rw [heq, hγ]
      simp only [List.append_assoc, List.cons_append]
    refine hinner u v ρ pre γ₁ γ₂ tail c d b hwf hu hv hplay hmin heq' hne
      (fun e he => hclean.1 e ?_) (fun e b' he => hpf e b' ?_) hfree₂
    · rw [hγ]; exact List.mem_append.mpr (Or.inl he)
    · rw [hγ]; exact List.mem_append.mpr (Or.inl he)

/-!
## §3. The campaign statement
-/

/-- **CROSS-SUIT VACUITY FROM THE FREE + INNER-RAISE SPLIT.**  No same-card
hypothesis is used for the *pure* corridor; the pull-containing corridors are
delegated to the campaign's same-card lane (`crossSuitVacuity_of_split`). -/
theorem crossSuitVacuity_of_free_and_inner (hfree : CrossSuitFreeCorridorResidual)
    (hinner : CrossSuitInnerRaiseResidual) (hsc : SameCardFreeInteriorShortens)
    {u v : State} (huwf : u.WF) (hu : SSaturated u) (hv : SSaturated v)
    {ρ : List Move} (hplay : ShufflePlayW u ρ v)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length)
    {i j : Nat} {c d : Card} {b : Base} (hij : i < j)
    (hi : ρ[i]? = some (Move.tabToFound c))
    (hj : ρ[j]? = some (Move.foundToTab d b)) (hsu : c.suit ≠ d.suit) : False :=
  crossSuitVacuity_of_split (pureResidual_of_split hfree hinner) hsc
    huwf hu hv hplay hmin hij hi hj hsu

/-- **CROSS-SUIT VACUITY FROM THE FREE-CORRIDOR RESIDUAL.**  The sharpened
target: `SameCardFreeInteriorShortens` plus the free corridor. -/
theorem crossSuitVacuity_of_freeCorridor (hfree : CrossSuitFreeCorridorResidual)
    (hsc : SameCardFreeInteriorShortens)
    {u v : State} (huwf : u.WF) (hu : SSaturated u) (hv : SSaturated v)
    {ρ : List Move} (hplay : ShufflePlayW u ρ v)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length)
    {i j : Nat} {c d : Card} {b : Base} (hij : i < j)
    (hi : ρ[i]? = some (Move.tabToFound c))
    (hj : ρ[j]? = some (Move.foundToTab d b)) (hsu : c.suit ≠ d.suit) : False :=
  crossSuitVacuity_of_split (pureResidual_of_free hfree hsc) hsc
    huwf hu hv hplay hmin hij hi hj hsu

/-- **NO CROSS-SUIT PAIR, FROM THE FREE-CORRIDOR RESIDUAL.** -/
theorem noCrossCorridor_of_free (hfree : CrossSuitFreeCorridorResidual)
    (hsc : SameCardFreeInteriorShortens)
    {u v : State} (huwf : u.WF) (hu : SSaturated u) (hv : SSaturated v)
    {ρ : List Move} (hplay : ShufflePlayW u ρ v)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) :
    ¬ CrossCorridor ρ :=
  no_crossCorridor_of_residual (pureResidual_of_sameCard
    (pureResidual_of_free hfree hsc) hsc) huwf hu hv hplay hmin

/-!
## §4. The corridor's endpoint facts
-/

/-- **THE PULL'S ORIGIN.**  Splitting at the corridor's pull: the origin
state `P` carries the pulled card as its `d`-foundation top. -/
theorem corridor_pull_top
    {u v : State} {pre γ tail : List Move} {c d : Card} {b : Base}
    (hplay : ShufflePlayW u
      ((pre ++ Move.tabToFound c :: γ) ++ Move.foundToTab d b :: tail) v) :
    ∃ P : State, ShufflePlayW u (pre ++ Move.tabToFound c :: γ) P ∧
      P.foundTop d.suit = some d := by
  obtain ⟨P, hpre, hrest⟩ := ShufflePlayW_split hplay
    (pre ++ Move.tabToFound c :: γ) (Move.foundToTab d b :: tail) rfl
  obtain ⟨B, -, hstepP, -⟩ := Bubble.walk_cons_inv hrest
  obtain ⟨c', htop, hc', -, -⟩ := step_foundToTab_inv hstepP
  subst c'
  exact ⟨P, hpre, htop⟩

/-- **THE TWO COLUMN TOPS AT THE CORRIDOR'S PULL** (free interior).

At the pull's origin `P` the raised card `c` is the `c`-column top and the
pulled card `d` the `d`-column top.  This is the two-column picture the twin
lock reads: in `u`'s saturated position the raise was only possible because
`c`'s cover fell onto `c.twin`, while `d` has been sitting on the foundation
the whole way — so the pull lowers a column that the corridor never touched,
and `c`'s column is frozen one rung higher. -/
theorem free_corridor_two_tops
    {u v : State} {pre γ tail : List Move} {c d : Card} {b : Base}
    (hplay : ShufflePlayW u
      ((pre ++ Move.tabToFound c :: γ) ++ Move.foundToTab d b :: tail) v)
    (hfree : FreeOnly γ) :
    ∃ P : State, ShufflePlayW u (pre ++ Move.tabToFound c :: γ) P ∧
      P.foundTop c.suit = some c ∧ P.foundTop d.suit = some d := by
  obtain ⟨P, hpre, hrest⟩ := ShufflePlayW_split hplay
    (pre ++ Move.tabToFound c :: γ) (Move.foundToTab d b :: tail) rfl
  -- the `d`-top is read by the pull itself
  obtain ⟨B, -, hstepP, -⟩ := Bubble.walk_cons_inv hrest
  obtain ⟨c', htopD, hc', -, -⟩ := step_foundToTab_inv hstepP
  -- the `c`-top survives the free corridor
  obtain ⟨Q, hpreQ, hraise⟩ := ShufflePlayW_split hpre pre
    (Move.tabToFound c :: γ) rfl
  obtain ⟨Q₁, -, hstepc, hγplay⟩ := Bubble.walk_cons_inv hraise
  obtain ⟨-, a, -, hs⟩ := step_tabToFound_inv hstepc
  have hQ₁ : Q₁ = raiseSt Q c a := by rw [hs]; rfl
  have hQ₁top : Q₁.foundTop c.suit = some c := by
    rw [hQ₁]; exact BaseEn.foundTop_raiseSt_self Q c a
  have htopC : P.foundTop c.suit = some c := by
    rw [foundTop_eq_of_avoids hγplay (freeOnly_avoids hfree)]
    exact hQ₁top
  subst c'
  exact ⟨P, hpre, htopC, htopD⟩

/-- **THE RAISED CARD IS THE `c`-TOP AT THE PULL'S ORIGIN** (free interior).

Free letters preserve the foundation, so the raise's `c` is still the
`c`-column top when the cross-suit pull fires.  Together with
`corridor_pull_top`: at the corridor's pull origin both `c` and `d` are
foundation tops of their suits — the two-column picture the twin lock reads. -/
theorem free_corridor_c_top
    {u v : State} {pre γ tail : List Move} {c d : Card} {b : Base}
    (hplay : ShufflePlayW u
      ((pre ++ Move.tabToFound c :: γ) ++ Move.foundToTab d b :: tail) v)
    (hfree : FreeOnly γ) :
    ∃ P : State, ShufflePlayW u (pre ++ Move.tabToFound c :: γ) P ∧
      P.foundTop c.suit = some c := by
  obtain ⟨P, hpre, hrest⟩ := ShufflePlayW_split hplay
    (pre ++ Move.tabToFound c :: γ) (Move.foundToTab d b :: tail) rfl
  refine ⟨P, hpre, ?_⟩
  obtain ⟨Q, hpreQ, hraise⟩ := ShufflePlayW_split hpre pre
    (Move.tabToFound c :: γ) rfl
  obtain ⟨Q₁, -, hstepc, hγplay⟩ := Bubble.walk_cons_inv hraise
  obtain ⟨-, a, -, hs⟩ := step_tabToFound_inv hstepc
  have hQ₁ : Q₁ = raiseSt Q c a := by rw [hs]; rfl
  have hQ₁top : Q₁.foundTop c.suit = some c := by
    rw [hQ₁]; exact BaseEn.foundTop_raiseSt_self Q c a
  rw [foundTop_eq_of_avoids hγplay (freeOnly_avoids hfree)]
  exact hQ₁top

/-- **THE LAST PULL'S CARD IS RE-RAISED.**  In a witness play that ends at a
`SSaturated` state, the play's **last** pull `pull d b` is followed, inside the
pull-free tail, by a raise of `d` or of `d.twin`.

The pull makes `d` S-live at its landing (`pull_card_live`); the tail is
pull-free (`exists_last_pull`); over a pull-free leg a live card stays live
unless the leg raises it or its twin (`canRaiseS_end_or_bad_raise`); and `v` is
saturated.  The pull-free analogue of `last_nonfree_raise`: the last pull is
always paid back. -/
theorem last_pull_card_re_raised {u v : State} {ρ : List Move}
    (huwf : u.WF) (hv : SSaturated v) (hplay : ShufflePlayW u ρ v)
    (hpull : ∃ (d : Card) (b : Base), Move.foundToTab d b ∈ ρ) :
    ∃ (α β : List Move) (d : Card) (b : Base),
      ρ = α ++ Move.foundToTab d b :: β ∧
        (Direct.Occurs (Move.tabToFound d) β ∨ Direct.Occurs (Move.tabToFound d.twin) β) := by
  obtain ⟨α, d, b, β, hρ, hnoPull⟩ := exists_last_pull ρ hpull
  obtain ⟨A, hα, hrest⟩ := ShufflePlayW_split hplay α
    (Move.foundToTab d b :: β) hρ
  obtain ⟨B, -, hstep, hβ⟩ := Bubble.walk_cons_inv hrest
  have hAwf : A.WF := SatDifferCensus.ShufflePlayW.wf_end hα huwf
  have hlive : CanRaiseS B d := pull_card_live hAwf hstep
  have hnp : ∀ m ∈ β, ¬ Bubble.IsPull m := by
    intro m hm his
    obtain ⟨c, b', rfl⟩ := his
    exact hnoPull c b' hm
  rcases Direct.canRaiseS_end_or_bad_raise hβ (step_wf hAwf hstep) hnp hlive with
    h1 | h1 | h1
  · exact absurd h1 (hv d)
  · exact ⟨α, β, d, b, hρ, Or.inl h1⟩
  · exact ⟨α, β, d, b, hρ, Or.inr h1⟩

end CrossSuit

/-! ## §5. Axiom battery -/

#print axioms CrossSuit.freeOnly_of_all_isFreeB
#print axioms CrossSuit.all_isFreeB_of_freeOnly
#print axioms CrossSuit.freeOnly_pullFree
#print axioms CrossSuit.freeOnly_avoids
#print axioms CrossSuit.freeOnly_corridorClean
#print axioms CrossSuit.raisesOf_eq_zero_of_free
#print axioms CrossSuit.pullsOf_eq_zero_of_free
#print axioms CrossSuit.exists_last_suit_raise
#print axioms CrossSuit.corridor_last_d_raise
#print axioms CrossSuit.pure_corridor_last_nonfree
#print axioms CrossSuit.pure_corridor_shape
#print axioms CrossSuit.freeOnly_of_sameCard
#print axioms CrossSuit.freeResidual_of_pure
#print axioms CrossSuit.pureResidual_of_free
#print axioms CrossSuit.pureResidual_iff_free
#print axioms CrossSuit.pureResidual_of_split
#print axioms CrossSuit.crossSuitVacuity_of_free_and_inner
#print axioms CrossSuit.crossSuitVacuity_of_freeCorridor
#print axioms CrossSuit.noCrossCorridor_of_free
#print axioms CrossSuit.corridor_pull_top
#print axioms CrossSuit.free_corridor_two_tops
#print axioms CrossSuit.free_corridor_c_top
#print axioms CrossSuit.last_pull_card_re_raised

#check @CrossSuit.FreeOnly
#check @CrossSuit.CrossSuitFreeCorridorResidual
