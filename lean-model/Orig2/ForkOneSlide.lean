import Orig2.CargoRaise


set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Orig2/ForkOneSlide - the unconditional safe cargo path

SCRATCH PROBE (not a library card).  The one-slide argument for the
safe-cargo-path statement:

```lean
theorem safe_cargo_path_of_any
    {st z : State} {x : Card}
    (hwf : st.WF) (hpath : CargoPath st z) (hcan : CanRaise z x.twin)
    (hblock : ¬ CanRaise st x.twin)
    (hfloor : ∀ c, CanRaiseS st c → x.rank.toIdx ≤ c.rank.toIdx) :
    ∃ z', Steps (RevStepOf (safeMoves x.rank.toIdx x)) st z' ∧ CanRaise z' x.twin
```

MATHEMATICS.  Put `y = x.twin`.  `CanRaiseS st y` (from `hpath` and
`hcan`), and `canRaiseS_flat_necessity` (`Orig2/CargoRaise.lean:320`)
gives the flat shape

```text
st.nextUp y = true
(st.piles a).faceUp = bs ++ y :: run
bs ≠ [] ∨ ((st.piles a).hidden = [] ∧ y.rank = king)
run = [] ∨ st.pileOfTop y.twin ≠ none
```

If `run = []` then `y` tops `a` and the seat clause makes it vanilla
raisable, against `hblock`.  So `run = u1 :: rest`, and the last
clause yields `st.pileOfTop y.twin = some k`, i.e. (since
`y.twin = x`) `x` tops a pile.  The run's head `u1` fits `y`
(`runOK_adjacent_fit`), so it also fits `x` (`canSitOn` is twin-blind
on the target, `Basic.lean:119`): `u1` is one rank below `x` and of
opposite colour.  The single slide

```text
tabToTab u1 (inr x)
```

is legal (`canPlace_inr_located`, `State.lean:492`), reversible
(`tabToTabR_iff_reversibleAtW`, `Classification.lean:2350`; the card
has company beneath it, `below u1 = bs ++ [y] ≠ []`), and it lies in
`safeMoves x.rank.toIdx x`: the moved head has rank `x.rank.toIdx - 1`
and the landing top is `x` itself.  Its successor exposes `y` over
the original seat `bs`, so `CanRaise z' y` by the same `bs`/bare-king
split the flat clause supplies.

`hfloor` is not used: the safe move is the cover's, whose rank is
below `x.rank.toIdx` by the tableau fit alone.

House compliance: scratch/read-only; no source edits; zero `sorry`,
zero `Classical.choice`, zero `native_decide`.
-/

/-- **safeMoves** - the safe cargo alphabet (the brief's definition):
a reversible slide of a card strictly below `r`, whose landing top is
either below `r` or one of the twin pair. -/
def safeMoves (r : Nat) (x : Card) : MoveSet := fun m =>
  ∃ d b, m = Move.tabToTab d b ∧ d.rank.toIdx < r ∧
    (∀ z, b = Sum.inr z → z.rank.toIdx < r ∨ z = x ∨ z = x.twin)

namespace SafePathFiber

/-! ## §1. Bookkeeping steps -/

/-- **STEP 1 - the flat shape at the live twin** (restatement of
`canRaiseS_flat_necessity` at `y = x.twin`, with the twin's twin
already rewritten). -/
theorem twin_flat_data {st : State} {x : Card} (hwf : st.WF)
    (hlive : CanRaiseS st x.twin) :
    st.nextUp x.twin = true ∧
    ∃ a bs run, (st.piles a).faceUp = bs ++ x.twin :: run ∧
      (bs ≠ [] ∨ ((st.piles a).hidden = [] ∧ x.twin.rank = Rank.king)) ∧
      (run = [] ∨ st.pileOfTop x ≠ none) := by
  obtain ⟨hnext, a, bs, run, hshape, hseat, hdisj⟩ :=
    canRaiseS_flat_necessity hwf hlive
  refine ⟨hnext, a, bs, run, hshape, hseat, ?_⟩
  rcases hdisj with h | h
  · exact Or.inl h
  · exact Or.inr (by rwa [card_twin_twin] at h)

/-- **STEP 2 - the cover's run is nonempty.**  If the run above the
live twin were empty, the twin would top its pile over the flat seat
clause, i.e. would be vanilla raisable. -/
theorem twin_run_ne_nil {st : State} {x : Card} (hwf : st.WF)
    (hnext : st.nextUp x.twin = true) (hblock : ¬ CanRaise st x.twin)
    {a : Anchor} {bs run : List Card}
    (hshape : (st.piles a).faceUp = bs ++ x.twin :: run)
    (hseat : bs ≠ [] ∨ ((st.piles a).hidden = [] ∧ x.twin.rank = Rank.king)) :
    run ≠ [] := by
  intro hrn
  have htop : (st.piles a).top = some x.twin := by
    show lastOf (st.piles a).faceUp = some x.twin
    rw [hshape, hrn]
    exact lastOf_snoc
  have hpod : st.pileOfTop x.twin = some a := (pileOfTop_eq_some_iff hwf).2 htop
  have hchop : chop (st.piles a).faceUp ≠ [] ∨
      ((st.piles a).hidden = [] ∧ x.twin.rank = Rank.king) := by
    rcases hseat with hbs | hbk
    · refine Or.inl ?_
      rw [hshape, hrn, chop_snoc]
      exact hbs
    · exact Or.inr hbk
  exact hblock ⟨hnext, a, hpod, hchop⟩

/-- **STEP 3 - the twin `x` tops a pile.**  With a nonempty cover run,
the flat characterization's disjunction forces `pileOfTop x.twin.twin`
to be located, and `x.twin.twin = x`. -/
theorem twin_top_of_cover {st : State} {x : Card}
    {run : List Card} (hrun : run ≠ [])
    (hdisj : run = [] ∨ st.pileOfTop x ≠ none) :
    ∃ k, st.pileOfTop x = some k := by
  rcases hdisj with h | h
  · exact absurd h hrun
  · cases hk : st.pileOfTop x with
    | none => exact absurd hk h
    | some k => exact ⟨k, rfl⟩

/-- **STEP 4 - the cover fits the twin.**  If `u1` sits directly on
`y = x.twin` in a legal run, then it fits `x = y.twin` as well: the
tableau fit is twin-blind in the target (`canSitOn_twin_right`,
`Basic.lean:119`). -/
theorem cover_fit_twin {st : State} {x : Card} (hwf : st.WF) {a : Anchor}
    {bs rest : List Card} {u1 : Card}
    (hshape : (st.piles a).faceUp = bs ++ x.twin :: u1 :: rest) :
    canSitOn u1 x = true := by
  have hok : runOK (bs ++ x.twin :: u1 :: rest) = true := by
    rw [← hshape]; exact hwf.2.1 a
  have hfit : canSitOn u1 x.twin = true :=
    SeedKit.runOK_adjacent_fit x.twin u1 bs rest hok
  rw [show x = x.twin.twin from (card_twin_twin x).symm]
  rw [show x.twin.twin = { x.twin with suit := x.twin.suit.twin } from rfl,
    canSitOn_twin_right]
  exact hfit

/-! ## §2. The one-slide successor -/

/-- **STEP 5 - the cover's slide is safe, reversible, and exposes the
twin.**  Given the flat shape with a nonempty run (`u1 :: rest`) and
`x` topping pile `k`, the slide `tabToTab u1 (inr x)` lands in
`safeMoves x.rank.toIdx x`, is reversible, and its successor raises
`x.twin`. -/
theorem cover_slide_exists {st : State} {x : Card} (hwf : st.WF)
    (hnext : st.nextUp x.twin = true)
    {a k : Anchor} {bs rest : List Card} {u1 : Card}
    (hshape : (st.piles a).faceUp = bs ++ x.twin :: u1 :: rest)
    (hseat : bs ≠ [] ∨ ((st.piles a).hidden = [] ∧ x.twin.rank = Rank.king))
    (hxTop : st.pileOfTop x = some k) :
    ∃ z', RevStepOf (safeMoves x.rank.toIdx x) st z' ∧ CanRaise z' x.twin := by
  have hok : runOK (bs ++ x.twin :: u1 :: rest) = true := by
    rw [← hshape]; exact hwf.2.1 a
  have hfit : canSitOn u1 x.twin = true :=
    SeedKit.runOK_adjacent_fit x.twin u1 bs rest hok
  have hfittwin : canSitOn u1 x = true := by
    rw [show x = x.twin.twin from (card_twin_twin x).symm]
    rw [show x.twin.twin = { x.twin with suit := x.twin.suit.twin } from rfl,
      canSitOn_twin_right]
    exact hfit
  have hcpD : st.canPlace u1 (Sum.inr x) = true := by
    rw [canPlace_inr_located hxTop]
    exact hfittwin
  have hid : (bs ++ [x.twin]) ++ u1 :: rest = bs ++ x.twin :: u1 :: rest := by
    rw [List.append_assoc bs [x.twin], List.cons_append, List.nil_append]
  have hdnotin : u1 ∉ bs ++ [x.twin] :=
    nodup_mid_notmem u1 (bs ++ [x.twin]) rest
      (by rw [hid, ← hshape]; exact runOK_nodup (hwf.2.1 a))
  have hexcl := tfc_below_fromCard_excl u1 (bs ++ [x.twin]) (u1 :: rest) hdnotin
  have hbelD : below u1 ((st.piles a).faceUp) = bs ++ [x.twin] := by
    have h1 := hexcl.1
    rw [below_cons_self, List.append_nil] at h1
    rw [hshape, ← hid]
    exact h1
  have hfromD : fromCard u1 ((st.piles a).faceUp) = u1 :: rest := by
    have h2 := hexcl.2
    rw [fromCard_head_eq] at h2
    rw [hshape, ← hid]
    exact h2
  have hholdD : st.pileHolding u1 = some a :=
    (pileHolding_eq_some_iff hwf).2 (by
      rw [hshape]
      exact List.mem_append.mpr
        (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons_self ..)))))
  have hsteplit : st.step (Move.tabToTab u1 (Sum.inr x)) = some
      ((st.setPile a (Pile.afterRunRemoved (st.piles a) (bs ++ [x.twin]))).putRun
        (u1 :: rest) (Sum.inr x)) := by
    show (match st.pileHolding u1 with
      | none => none
      | some a₂ =>
          if st.canPlace u1 (Sum.inr x) then
            match fromCard u1 ((st.piles a₂).faceUp) with
            | [] => none
            | run => some ((st.setPile a₂
                (Pile.afterRunRemoved (st.piles a₂)
                  (below u1 ((st.piles a₂).faceUp)))).putRun run (Sum.inr x))
            else none) = _
    rw [hholdD]
    simp only [canPlace_inr_located hxTop, hfittwin]
    rw [hfromD, hbelD]
    rfl
  obtain ⟨s', hs'eq, hstep⟩ : ∃ s', s' =
      (st.setPile a (Pile.afterRunRemoved (st.piles a) (bs ++ [x.twin]))).putRun
        (u1 :: rest) (Sum.inr x) ∧
      st.step (Move.tabToTab u1 (Sum.inr x)) = some s' :=
    ⟨_, rfl, hsteplit⟩
  -- rank facts: the cover head is one rank below the twin pair
  have htr : x.rank = x.twin.rank := rfl
  have hxne : x ≠ x.twin := by
    have h := card_twin_ne x.twin
    rwa [card_twin_twin x] at h
  -- `k` (the twin's top pile) differs from `a` (the covered twin's pile):
  -- equal ranks inside one legal run force equal cards
  have hka : k ≠ a := by
    intro hcon
    rw [hcon] at hxTop
    have hmemT : x ∈ (st.piles a).faceUp :=
      Pile.mem_of_top (pileOfTop_top hxTop).2
    have hmemT' : x ∈ bs ++ x.twin :: u1 :: rest := by
      rw [← hshape]; exact hmemT
    have hmemY : x.twin ∈ bs ++ x.twin :: u1 :: rest :=
      List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    exact hxne (runOK_rank_distinct hok hmemT' hmemY rfl)
  -- the mid-state facts
  have hpre : bs ++ [x.twin] ≠ [] := by cases bs <;> simp
  have hmidFu : (Pile.afterRunRemoved (st.piles a) (bs ++ [x.twin])).faceUp
      = bs ++ [x.twin] := afterRunRemoved_faceUp_ne hpre
  have hmidHi : (Pile.afterRunRemoved (st.piles a) (bs ++ [x.twin])).hidden
      = (st.piles a).hidden := by
    rcases afterRunRemoved_hidden (st.piles a) (bs ++ [x.twin]) with
      ⟨hne, hhid⟩ | ⟨hnil, hph1, hph2⟩ | ⟨hnil, hph1, hph2⟩
    · exact hhid
    · exact absurd hnil hpre
    · exact absurd hnil hpre
  have htwinmemb : x ∈ (st.piles k).faceUp :=
    Pile.mem_of_top (pileOfTop_top hxTop).2
  have hnoTtwin : ∀ y : Anchor, y ≠ k → (st.piles y).top ≠ some x := by
    intro y hyk htop
    exact (mem_faceUp_unique hwf htwinmemb y hyk).1 (Pile.mem_of_top htop)
  have hmidA : (st.setPile a (Pile.afterRunRemoved (st.piles a) (bs ++ [x.twin]))).piles a
      = Pile.afterRunRemoved (st.piles a) (bs ++ [x.twin]) := setPile_piles_self
  have hmidTopA : (Pile.afterRunRemoved (st.piles a) (bs ++ [x.twin])).top = some x.twin := by
    show lastOf ((Pile.afterRunRemoved (st.piles a) (bs ++ [x.twin])).faceUp) = some x.twin
    rw [hmidFu]
    exact lastOf_snoc
  -- the twin still tops `k` at the mid-state
  have hmidpin : (st.setPile a (Pile.afterRunRemoved (st.piles a) (bs ++ [x.twin]))).pileOfTop x
      = some k := by
    show (firstWhere (fun a₂ => decide
        ((st.setPile a (Pile.afterRunRemoved (st.piles a) (bs ++ [x.twin]))).topOf a₂
          = some x)) Anchor.all) = some k
    refine firstWhere_find (Anchor.mem_all k) ?_ ?_
    · show decide (((st.setPile a
          (Pile.afterRunRemoved (st.piles a) (bs ++ [x.twin]))).topOf k) = some x) = true
      rw [setPile_topOf_ne hka]
      exact decide_eq_true (pileOfTop_top hxTop).2
    · intro y _hyp hyne
      show decide (((st.setPile a
          (Pile.afterRunRemoved (st.piles a) (bs ++ [x.twin]))).topOf y) = some x) = false
      by_cases hya : y = a
      · rw [hya]
        have htopA : (st.setPile a
            (Pile.afterRunRemoved (st.piles a) (bs ++ [x.twin]))).topOf a = some x.twin := by
          rw [show (st.setPile a
              (Pile.afterRunRemoved (st.piles a) (bs ++ [x.twin]))).topOf a
              = ((st.setPile a
                (Pile.afterRunRemoved (st.piles a) (bs ++ [x.twin]))).piles a).top from rfl,
            hmidA]
          exact hmidTopA
        rw [htopA]
        exact decide_false_of_not (fun hcon => hxne (Option.some.inj hcon).symm)
      · rw [setPile_topOf_ne hya]
        exact decide_false_of_not (fun hcon => hnoTtwin y hyne hcon)
  -- the successor's covered pile: `x.twin` exposed over `bs`
  have hwfs' : s'.WF := step_wf hwf hstep
  have hs'A : s'.piles a = Pile.afterRunRemoved (st.piles a) (bs ++ [x.twin]) := by
    rw [hs'eq, putRun_piles_inr_ne _ _ _ _ hmidpin (Ne.symm hka), hmidA]
  have hstop : (s'.piles a).top = some x.twin := by rw [hs'A]; exact hmidTopA
  have hpodS' : s'.pileOfTop x.twin = some a := (pileOfTop_eq_some_iff hwfs').2 hstop
  have hchopS' : chop (s'.piles a).faceUp = bs := by
    rw [hs'A, hmidFu, chop_snoc]
  have hseatS' : chop (s'.piles a).faceUp ≠ [] ∨
      ((s'.piles a).hidden = [] ∧ x.twin.rank = Rank.king) := by
    rcases hseat with hbs | hbk
    · exact Or.inl (by rw [hchopS']; exact hbs)
    · refine Or.inr ⟨?_, hbk.2⟩
      rw [hs'A, hmidHi]
      exact hbk.1
  have hfndS' : s'.found = st.found := by
    rw [hs'eq, putRun_found, setPile_found]
  have hnextS' : s'.nextUp x.twin = st.nextUp x.twin :=
    congrArg (fun (f : Suit → List Card) =>
      decide (x.twin.rank.toIdx = (f x.twin.suit).length)) hfndS'
  -- reversibility: the cover head has company beneath it
  have hor : tabToTabR st u1 (Sum.inr x) = true := by
    cases hbelow : below u1 ((st.piles a).faceUp) with
    | nil =>
        rw [hbelD] at hbelow
        exact absurd hbelow (by cases bs <;> simp)
    | cons w t =>
        simp only [tabToTabR, hholdD, hcpD, hbelow]
  have hrev : reversibleAtW st (Move.tabToTab u1 (Sum.inr x)) :=
    (tabToTabR_iff_reversibleAtW hwf u1 (Sum.inr x)).mp hor
  -- the move is safe: rank below `x.rank.toIdx`, landing top is `x`
  have hrank : u1.rank.toIdx < x.rank.toIdx := by
    have h1 := (canSitOn_eq u1 x.twin).mp hfit
    have htr' : x.rank.toIdx = x.twin.rank.toIdx := by rw [htr]
    omega
  have htarget : ∀ z : Card, (Sum.inr x : Base) = Sum.inr z →
      z.rank.toIdx < x.rank.toIdx ∨ z = x ∨ z = x.twin := by
    intro z hz
    cases hz
    exact Or.inr (Or.inl rfl)
  refine ⟨s', ⟨Move.tabToTab u1 (Sum.inr x), ?_, hstep, hrev⟩, ?_⟩
  · exact ⟨u1, Sum.inr x, rfl, hrank, htarget⟩
  · exact ⟨hnextS'.trans hnext, a, hpodS', hseatS'⟩

/-! ## §3. The main theorem -/

/-- **THE UNCONDITIONAL SAFE CARGO PATH** - exactly the brief's
statement.  `hpath`/`hcan` only serve to build `CanRaiseS st x.twin`;
`hfloor` is present for compatibility and is not used (the cover's
rank is below the pair's by the tableau fit itself). -/
theorem safe_cargo_path_of_any
    {st z : State} {x : Card}
    (hwf : st.WF) (hpath : CargoPath st z) (hcan : CanRaise z x.twin)
    (hblock : ¬ CanRaise st x.twin)
    (hfloor : ∀ c, CanRaiseS st c → x.rank.toIdx ≤ c.rank.toIdx) :
    ∃ z', Steps (RevStepOf (safeMoves x.rank.toIdx x)) st z' ∧ CanRaise z' x.twin := by
  have hlive : CanRaiseS st x.twin := ⟨z, hpath, hcan⟩
  obtain ⟨hnext, a, bs, run, hshape, hseat, hdisj⟩ :=
    twin_flat_data hwf hlive
  have hrun : run ≠ [] :=
    twin_run_ne_nil hwf hnext hblock hshape hseat
  obtain ⟨k, hxTop⟩ := twin_top_of_cover hrun hdisj
  cases run with
  | nil => exact absurd rfl hrun
  | cons u1 rest =>
      obtain ⟨z', hz', hz'raise⟩ :=
        cover_slide_exists hwf hnext hshape hseat hxTop
      exact ⟨z', Steps.cons hz' (Steps.refl z'), hz'raise⟩

/-- **The rank floor is redundant.**  The same conclusion holds with
no `hfloor` premise at all: the proof only moves the cover, whose
rank is `x.rank.toIdx - 1` by the tableau fit.  This is the form a
`Drain_Invariant` consumer can use without transporting a rank
floor. -/
theorem safe_cargo_path_of_any_no_floor
    {st z : State} {x : Card}
    (hwf : st.WF) (hpath : CargoPath st z) (hcan : CanRaise z x.twin)
    (hblock : ¬ CanRaise st x.twin) :
    ∃ z', Steps (RevStepOf (safeMoves x.rank.toIdx x)) st z' ∧ CanRaise z' x.twin := by
  have hlive : CanRaiseS st x.twin := ⟨z, hpath, hcan⟩
  obtain ⟨hnext, a, bs, run, hshape, hseat, hdisj⟩ :=
    twin_flat_data hwf hlive
  have hrun : run ≠ [] :=
    twin_run_ne_nil hwf hnext hblock hshape hseat
  obtain ⟨k, hxTop⟩ := twin_top_of_cover hrun hdisj
  cases run with
  | nil => exact absurd rfl hrun
  | cons u1 rest =>
      obtain ⟨z', hz', hz'raise⟩ :=
        cover_slide_exists hwf hnext hshape hseat hxTop
      exact ⟨z', Steps.cons hz' (Steps.refl z'), hz'raise⟩

/-- The brief's statement with the target's `x` kept as `y.twin`;
a convenience restatement for the `Drain_Invariant` consumer. -/
theorem safe_cargo_path_unconditional
    {st z : State} {x : Card}
    (hwf : st.WF) (hpath : CargoPath st z) (hcan : CanRaise z x.twin)
    (hblock : ¬ CanRaise st x.twin)
    (hfloor : ∀ c, CanRaiseS st c → x.rank.toIdx ≤ c.rank.toIdx) :
    ∃ z', Steps (RevStepOf (safeMoves x.rank.toIdx x)) st z' ∧ CanRaise z' x.twin :=
  safe_cargo_path_of_any hwf hpath hcan hblock hfloor

end SafePathFiber

/-! ## Battery -/

#print axioms SafePathFiber.twin_flat_data
#print axioms SafePathFiber.twin_run_ne_nil
#print axioms SafePathFiber.twin_top_of_cover
#print axioms SafePathFiber.cover_fit_twin
#print axioms SafePathFiber.cover_slide_exists
#print axioms SafePathFiber.safe_cargo_path_of_any
#print axioms SafePathFiber.safe_cargo_path_of_any_no_floor
#print axioms SafePathFiber.safe_cargo_path_unconditional
