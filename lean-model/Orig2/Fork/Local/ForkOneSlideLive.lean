import Orig2.Substrate.CargoRaise
import Orig2.Fork.Split.ForkDrain
import Orig2.Fork.Local.ForkSafeTransport

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Orig2/ForkOneSlideLive — the one-slide unblocking lemma for ANY blocked live card

READ-ONLY scratch card (no source edits, no commit).

TARGET 1 of the brief: generalize `Temp/SafePath_Fiber_OneSlide.lean`
(the twin case, `y = x.twin`) to an ARBITRARY blocked live card `c`.

`canRaiseS_flat_necessity` (`Orig2/Substrate/CargoRaise.lean:320`) gives the flat
shape `faceUp a = bs ++ c :: run`; `hblock` forces `run ≠ []` (an empty run
makes `c` the pile top over the flat seat clause, i.e. vanilla raisable).
So `run = u1 :: rest`, `u1` sits directly on `c`, the run-or-twin clause
puts `c.twin` on top of some pile `k`, and the single slide

```text
tabToTab u1 (inr c.twin)
```

is legal, reversible, and its successor `z` has `CanRaise z c` (the exposed
`chop bs`, or the bare-king cell).

House compliance: zero `sorry`, zero `Classical.choice`, zero
`native_decide`; battery at the tail.
-/

namespace OneSlide

/-! ## §1. Bookkeeping -/

/-- **STEP 1 — the cover's run is nonempty.**  If the run above the live
`c` were empty, `c` would top its pile over the flat seat clause, i.e. be
vanilla raisable.  (Generalizes `twin_run_ne_nil`,
`Temp/SafePath_Fiber_OneSlide.lean:89`.) -/
theorem run_ne_nil {st : State} {c : Card} (hwf : st.WF)
    (hnext : st.nextUp c = true) (hblock : ¬ CanRaise st c)
    {a : Anchor} {bs run : List Card}
    (hshape : (st.piles a).faceUp = bs ++ c :: run)
    (hseat : bs ≠ [] ∨ ((st.piles a).hidden = [] ∧ c.rank = Rank.king)) :
    run ≠ [] := by
  intro hrn
  have htop : (st.piles a).top = some c := by
    show lastOf (st.piles a).faceUp = some c
    rw [hshape, hrn]
    exact lastOf_snoc
  have hpod : st.pileOfTop c = some a := (pileOfTop_eq_some_iff hwf).2 htop
  have hchop : chop (st.piles a).faceUp ≠ [] ∨
      ((st.piles a).hidden = [] ∧ c.rank = Rank.king) := by
    rcases hseat with hbs | hbk
    · refine Or.inl ?_
      rw [hshape, hrn, chop_snoc]
      exact hbs
    · exact Or.inr hbk
  exact hblock ⟨hnext, a, hpod, hchop⟩

/-- **STEP 2 — the twin `c.twin` tops a pile.**  With a nonempty cover
run, the flat disjunction forces `pileOfTop c.twin` to be located. -/
theorem twin_top_of_cover {st : State} {c : Card}
    {run : List Card} (hrun : run ≠ [])
    (hdisj : run = [] ∨ st.pileOfTop c.twin ≠ none) :
    ∃ k, st.pileOfTop c.twin = some k := by
  rcases hdisj with h | h
  · exact absurd h hrun
  · cases hk : st.pileOfTop c.twin with
    | none => exact absurd hk h
    | some k => exact ⟨k, rfl⟩

/-- **STEP 3 — the cover fits the twin.**  If `u1` sits directly on `c` in
a legal run, it fits `c.twin` as well: the tableau fit is twin-blind in the
target (`canSitOn_twin_right`, `Orig/Basic.lean:119`). -/
theorem cover_fit_twin {st : State} {c : Card} (hwf : st.WF) {a : Anchor}
    {bs rest : List Card} {u1 : Card}
    (hshape : (st.piles a).faceUp = bs ++ c :: u1 :: rest) :
    canSitOn u1 c.twin = true := by
  have hok : runOK (bs ++ c :: u1 :: rest) = true := by
    rw [← hshape]; exact hwf.2.1 a
  have hfit : canSitOn u1 c = true :=
    SeedKit.runOK_adjacent_fit c u1 bs rest hok
  rw [show c.twin = { c with suit := c.suit.twin } from rfl,
    canSitOn_twin_right]
  exact hfit

/-! ## §2. The one-slide successor (general card) -/

/-- **STEP 4 — the cover's slide is reversible and exposes `c`.**
Generalizes `cover_slide_exists` (`Temp/SafePath_Fiber_OneSlide.lean:147`)
from the twin `x.twin` to an arbitrary card `c`: given the flat shape with
a nonempty run (`u1 :: rest`) and `c.twin` topping pile `k`, the slide
`tabToTab u1 (inr c.twin)` fires, is reversible, and its successor raises
`c`. -/
theorem cover_slide_exists {st : State} {c : Card} (hwf : st.WF)
    (hnext : st.nextUp c = true)
    {a k : Anchor} {bs rest : List Card} {u1 : Card}
    (hshape : (st.piles a).faceUp = bs ++ c :: u1 :: rest)
    (hseat : bs ≠ [] ∨ ((st.piles a).hidden = [] ∧ c.rank = Rank.king))
    (htwinTop : st.pileOfTop c.twin = some k) :
    ∃ z, st.step (Move.tabToTab u1 (Sum.inr c.twin)) = some z ∧
      reversibleAtW st (Move.tabToTab u1 (Sum.inr c.twin)) ∧
      CanRaise z c := by
  have hok : runOK (bs ++ c :: u1 :: rest) = true := by
    rw [← hshape]; exact hwf.2.1 a
  have hfit : canSitOn u1 c = true :=
    SeedKit.runOK_adjacent_fit c u1 bs rest hok
  have hfittwin : canSitOn u1 c.twin = true := by
    rw [show c.twin = { c with suit := c.suit.twin } from rfl,
      canSitOn_twin_right]
    exact hfit
  have hcpD : st.canPlace u1 (Sum.inr c.twin) = true := by
    rw [canPlace_inr_located htwinTop]
    exact hfittwin
  have hid : (bs ++ [c]) ++ u1 :: rest = bs ++ c :: u1 :: rest := by
    rw [List.append_assoc bs [c], List.cons_append, List.nil_append]
  have hdnotin : u1 ∉ bs ++ [c] :=
    nodup_mid_notmem u1 (bs ++ [c]) rest
      (by rw [hid, ← hshape]; exact runOK_nodup (hwf.2.1 a))
  have hexcl := tfc_below_fromCard_excl u1 (bs ++ [c]) (u1 :: rest) hdnotin
  have hbelD : below u1 ((st.piles a).faceUp) = bs ++ [c] := by
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
  have hsteplit : st.step (Move.tabToTab u1 (Sum.inr c.twin)) = some
      ((st.setPile a (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).putRun
        (u1 :: rest) (Sum.inr c.twin)) := by
    show (match st.pileHolding u1 with
      | none => none
      | some a₂ =>
          if st.canPlace u1 (Sum.inr c.twin) then
            match fromCard u1 ((st.piles a₂).faceUp) with
            | [] => none
            | run => some ((st.setPile a₂
                (Pile.afterRunRemoved (st.piles a₂)
                  (below u1 ((st.piles a₂).faceUp)))).putRun run (Sum.inr c.twin))
            else none) = _
    rw [hholdD]
    simp only [canPlace_inr_located htwinTop, hfittwin]
    rw [hfromD, hbelD]
    rfl
  obtain ⟨s', hs'eq, hstep⟩ : ∃ s', s' =
      (st.setPile a (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).putRun
        (u1 :: rest) (Sum.inr c.twin) ∧
      st.step (Move.tabToTab u1 (Sum.inr c.twin)) = some s' :=
    ⟨_, rfl, hsteplit⟩
  -- rank facts: the cover head is one rank below `c`, whose twin shares
  -- the rank
  have htr : c.twin.rank = c.rank := rfl
  -- `k` (the twin's top pile) differs from `a` (the covered card's pile)
  have hka : k ≠ a := by
    intro hcon
    rw [hcon] at htwinTop
    have hmemT : c.twin ∈ (st.piles a).faceUp :=
      Pile.mem_of_top (pileOfTop_top htwinTop).2
    rw [hshape] at hmemT
    rcases List.mem_append.mp hmemT with hbs' | hrun'
    · have h1 := runOK_desc hok hbs' (List.mem_cons_self ..)
      rw [htr] at h1
      omega
    · rcases List.mem_cons.mp hrun' with heq | hrest'
      · exact card_twin_ne c heq
      · have hokL : runOK ((bs ++ [c]) ++ u1 :: rest) = true := by
          rw [hid]; exact hok
        have h2 := runOK_desc hokL
          (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))) hrest'
        rw [htr] at h2
        omega
  -- the mid-state facts
  have hpre : bs ++ [c] ≠ [] := by cases bs <;> simp
  have hmidFu : (Pile.afterRunRemoved (st.piles a) (bs ++ [c])).faceUp
      = bs ++ [c] := afterRunRemoved_faceUp_ne hpre
  have hmidHi : (Pile.afterRunRemoved (st.piles a) (bs ++ [c])).hidden
      = (st.piles a).hidden := by
    rcases afterRunRemoved_hidden (st.piles a) (bs ++ [c]) with
      ⟨hne, hhid⟩ | ⟨hnil, hph1, hph2⟩ | ⟨hnil, hph1, hph2⟩
    · exact hhid
    · exact absurd hnil hpre
    · exact absurd hnil hpre
  have htwinmemb : c.twin ∈ (st.piles k).faceUp :=
    Pile.mem_of_top (pileOfTop_top htwinTop).2
  have hnoTtwin : ∀ y : Anchor, y ≠ k → (st.piles y).top ≠ some c.twin := by
    intro y hyk htop
    exact (mem_faceUp_unique hwf htwinmemb y hyk).1 (Pile.mem_of_top htop)
  have hmidA : (st.setPile a (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).piles a
      = Pile.afterRunRemoved (st.piles a) (bs ++ [c]) := setPile_piles_self
  have hmidTopA : (Pile.afterRunRemoved (st.piles a) (bs ++ [c])).top = some c := by
    show lastOf ((Pile.afterRunRemoved (st.piles a) (bs ++ [c])).faceUp) = some c
    rw [hmidFu]
    exact lastOf_snoc
  -- the twin still tops `k` at the mid-state
  have hmidpin : (st.setPile a (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).pileOfTop c.twin
      = some k := by
    show (firstWhere (fun a₂ => decide
        ((st.setPile a (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).topOf a₂
          = some c.twin)) Anchor.all) = some k
    refine firstWhere_find (Anchor.mem_all k) ?_ ?_
    · show decide (((st.setPile a
          (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).topOf k) = some c.twin) = true
      rw [setPile_topOf_ne hka]
      exact decide_eq_true (pileOfTop_top htwinTop).2
    · intro y _hyp hyne
      show decide (((st.setPile a
          (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).topOf y) = some c.twin) = false
      by_cases hya : y = a
      · rw [hya]
        have htopA : (st.setPile a
            (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).topOf a = some c := by
          rw [show (st.setPile a
              (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).topOf a
              = ((st.setPile a
                (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).piles a).top from rfl,
            hmidA]
          exact hmidTopA
        rw [htopA]
        exact decide_false_of_not (fun hcon => card_twin_ne c (Option.some.inj hcon).symm)
      · rw [setPile_topOf_ne hya]
        exact decide_false_of_not (fun hcon => hnoTtwin y hyne hcon)
  -- the successor's covered pile: `c` exposed over `bs`
  have hwfs' : s'.WF := step_wf hwf hstep
  have hs'A : s'.piles a = Pile.afterRunRemoved (st.piles a) (bs ++ [c]) := by
    rw [hs'eq, putRun_piles_inr_ne _ _ _ _ hmidpin (Ne.symm hka), hmidA]
  have hstop : (s'.piles a).top = some c := by rw [hs'A]; exact hmidTopA
  have hpodS' : s'.pileOfTop c = some a := (pileOfTop_eq_some_iff hwfs').2 hstop
  have hchopS' : chop (s'.piles a).faceUp = bs := by
    rw [hs'A, hmidFu, chop_snoc]
  have hseatS' : chop (s'.piles a).faceUp ≠ [] ∨
      ((s'.piles a).hidden = [] ∧ c.rank = Rank.king) := by
    rcases hseat with hbs | hbk
    · exact Or.inl (by rw [hchopS']; exact hbs)
    · refine Or.inr ⟨?_, hbk.2⟩
      rw [hs'A, hmidHi]
      exact hbk.1
  have hfndS' : s'.found = st.found := by
    rw [hs'eq, putRun_found, setPile_found]
  have hnextS' : s'.nextUp c = st.nextUp c :=
    congrArg (fun (f : Suit → List Card) =>
      decide (c.rank.toIdx = (f c.suit).length)) hfndS'
  -- reversibility: the cover head has company beneath it
  have hor : tabToTabR st u1 (Sum.inr c.twin) = true := by
    cases hbelow : below u1 ((st.piles a).faceUp) with
    | nil =>
        rw [hbelD] at hbelow
        exact absurd hbelow (by cases bs <;> simp)
    | cons w t =>
        simp only [tabToTabR, hholdD, hcpD, hbelow]
  have hrev : reversibleAtW st (Move.tabToTab u1 (Sum.inr c.twin)) :=
    (tabToTabR_iff_reversibleAtW hwf u1 (Sum.inr c.twin)).mp hor
  exact ⟨s', hstep, hrev, ⟨hnextS'.trans hnext, a, hpodS', hseatS'⟩⟩

/-! ## §3. THE TARGET -/

/-- **TARGET 1 — `one_slide_of_blocked_live`.**  Every blocked live card
`c` is unblocked by ONE slide: the card `u1` directly on `c` carries the
run above `c` onto `c.twin`'s pile, reversibly, and the successor raises
`c`.  The pair `(u1, z)` is the witness; `run` is the remainder of the
original run.  Generalizes the twin case
`Temp/SafePath_Fiber_OneSlide.lean:333`. -/
theorem one_slide_of_blocked_live {st : State} {c : Card}
    (hwf : st.WF) (hlive : CanRaiseS st c) (hblock : ¬ CanRaise st c) :
    ∃ (u1 : Card) (z : State),
      ∃ a bs run, (st.piles a).faceUp = bs ++ c :: u1 :: run ∧
        (st.step (Move.tabToTab u1 (Sum.inr c.twin)) = some z) ∧
        reversibleAtW st (Move.tabToTab u1 (Sum.inr c.twin)) ∧
        CanRaise z c := by
  obtain ⟨hnext, a, bs, run, hshape, hseat, hdisj⟩ :=
    canRaiseS_flat_necessity hwf hlive
  have hrun : run ≠ [] :=
    run_ne_nil hwf hnext hblock hshape hseat
  obtain ⟨k, htwinTop⟩ := twin_top_of_cover hrun hdisj
  cases run with
  | nil => exact absurd rfl hrun
  | cons u1 rest =>
      obtain ⟨z, hstep, hrev, hraise⟩ :=
        cover_slide_exists hwf hnext hshape hseat htwinTop
      exact ⟨u1, z, a, bs, rest, hshape, hstep, hrev, hraise⟩

/-! ## §4. Disjointness with a protected twin pair `{x, x.twin}`

Setup: `c` is a blocked live card (`hlive`, `hblock`), `c ∉ {x, x.twin}`,
and `{x, x.twin}` is the drain invariant's protected pair, i.e.

```text
CanRaise st x,  CanRaiseS st x.twin,  ¬ CanRaise st x.twin,
∀ d, CanRaiseS st d → x.rank ≤ d.rank.
```
-/

/-- **The twin involution keeps `c` out of the protected pair.**  If
`c ∉ {x, x.twin}` then `c.twin ∉ {x, x.twin}` (`card_twin_twin`,
`Orig2/Substrate/Vocab.lean:530`). -/
theorem twin_pair_disjoint {c x : Card} (hx : c ≠ x) (hxt : c ≠ x.twin) :
    c.twin ≠ x ∧ c.twin ≠ x.twin := by
  constructor
  · intro h
    have h2 : c.twin.twin = x.twin := congrArg Card.twin h
    rw [card_twin_twin] at h2
    exact hxt h2
  · intro h
    have h2 : c.twin.twin = x.twin.twin := congrArg Card.twin h
    rw [card_twin_twin, card_twin_twin] at h2
    exact hx h2

/-- **A card covers at most one card** (`seatOf` is a function): if `u1`
sits directly on both `z₁` and `z₂` then `z₁ = z₂`.  This is the formal
content of "`u1 ≠` the card covering `x.twin`" whenever `u1` already
sits on `c ≠ x.twin`. -/
theorem cover_unique {st : State} {u1 z₁ z₂ : Card}
    (h1 : seatOf st u1 = some (Sum.inr z₁))
    (h2 : seatOf st u1 = some (Sum.inr z₂)) : z₁ = z₂ := by
  have h := h1.symm.trans h2
  injection h with h
  exact Sum.inr.inj h

/-- **`u1` does not cover the protected twin.**  If `u1` sits directly on
`c` and `c ≠ x.twin`, then `u1` does not sit directly on `x.twin`:
that would force `c = x.twin` by `cover_unique`. -/
theorem u1_not_cover_twin {st : State} {u1 c x : Card}
    (h1 : seatOf st u1 = some (Sum.inr c)) (hct : c ≠ x.twin) :
    seatOf st u1 ≠ some (Sum.inr x.twin) := by
  intro h2
  exact hct (cover_unique h1 h2)

/-! ### §4.1 The dangerous case: which side is possible?

At the flat shape `faceUp a = bs ++ c :: u1 :: run` the cards *below* `c`
are `bs`, the cards *above* `c` are `u1 :: run`.  The brief asks whether
`x.twin` can be moved by the slide, i.e. lie in `u1 :: run` (equivalently:
`c` sits below the twin in the same pile).

* `x.twin ∈ bs` (**twin physically below `c`**) is IMPOSSIBLE: it forces
  `x.twin.rank < c.rank` (strict descent) while the drain invariant's
  rank floor forces `x.rank ≤ c.rank` with `x.rank = x.twin.rank`.
* `c ∈` the run of `x.twin`'s own flat split is the SAME statement, so it
  is impossible too.
* `x.twin ∈ u1 :: run` (**twin above `c`**) is NOT excluded by the floor:
  it only forces `c.rank > x.twin.rank`, which is consistent with
  `x.rank ≤ c.rank`.  But it is HARMLESS: the slide moves the whole run
  as a block, so the twin's relative position inside it is preserved; and
  the twin cannot be the run's top (else it would already be vanilla
  raisable at `st`, contradicting the block).
-/

/-- **The twin cannot lie below `c` in `c`'s pile.**  The rank floor
`x.rank ≤ every live rank` plus the strict descent of the legal run
`bs ++ c :: u1 :: run` contradict `x.twin ∈ bs`. -/
theorem no_twin_below_c {st : State} {x c : Card} (hwf : st.WF)
    (hfloor : ∀ d, CanRaiseS st d → x.rank.toIdx ≤ d.rank.toIdx)
    (hc : CanRaiseS st c) {a : Anchor} {bs run : List Card} {u1 : Card}
    (hshape : (st.piles a).faceUp = bs ++ c :: u1 :: run)
    (hmem : x.twin ∈ bs) : False := by
  have hok : runOK (bs ++ c :: u1 :: run) = true := by
    rw [← hshape]; exact hwf.2.1 a
  have hlt : c.rank.toIdx < x.twin.rank.toIdx :=
    runOK_desc hok hmem (List.mem_cons_self ..)
  have hlt' : c.rank.toIdx < x.rank.toIdx := hlt
  have hge : x.rank.toIdx ≤ c.rank.toIdx := hfloor c hc
  omega

/-- **`c` cannot sit above the twin in the twin's own pile** — the
mirror reading of `no_twin_below_c`: if `x.twin`'s flat split has `c` in
its upper run, then `c.rank < x.twin.rank = x.rank`, against the floor. -/
theorem no_c_above_twin {st : State} {x c : Card} (hwf : st.WF)
    (hfloor : ∀ d, CanRaiseS st d → x.rank.toIdx ≤ d.rank.toIdx)
    (hc : CanRaiseS st c) {p : Anchor} {B Run : List Card}
    (hshape : (st.piles p).faceUp = B ++ x.twin :: Run)
    (hmem : c ∈ Run) : False := by
  have hok : runOK ((B ++ [x.twin]) ++ Run) = true := by
    rw [List.append_assoc, List.cons_append, List.nil_append, ← hshape]
    exact hwf.2.1 p
  have hlt : c.rank.toIdx < x.twin.rank.toIdx :=
    runOK_desc hok (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))) hmem
  have hlt' : c.rank.toIdx < x.rank.toIdx := hlt
  have hge : x.rank.toIdx ≤ c.rank.toIdx := hfloor c hc
  omega

/-- **The surviving case only needs `c` one rank above the pair.**  If
`x.twin` does lie in the run above `c`, then `x.rank < c.rank` — a
strict inequality that the rank floor (`x.rank ≤ c.rank`) does not
refute.  So the drain invariant does NOT exclude this configuration. -/
theorem twin_above_c_rank {st : State} {x c : Card} (hwf : st.WF)
    {a : Anchor} {bs run : List Card} {u1 : Card}
    (hshape : (st.piles a).faceUp = bs ++ c :: u1 :: run)
    (hmem : x.twin ∈ u1 :: run) :
    x.rank.toIdx < c.rank.toIdx := by
  have hok : runOK ((bs ++ [c]) ++ u1 :: run) = true := by
    rw [List.append_assoc, List.cons_append, List.nil_append, ← hshape]
    exact hwf.2.1 a
  have hlt : x.twin.rank.toIdx < c.rank.toIdx :=
    runOK_desc hok
      (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))) hmem
  exact hlt

/-- **The twin is never the top of `c`'s pile.**  If it were, it would be
vanilla raisable at `st` = flat seat clause from the remaining `bs ++ [c]`
prefix — against `¬ CanRaise st x.twin`.  This is the fact that makes the
`x.twin ∈ run` case harmless: the twin keeps a card above it. -/
theorem twin_not_top_of_c_pile {st : State} {x c : Card}
    (hwf : st.WF) {a : Anchor} {bs run : List Card} {u1 : Card}
    (hct : c ≠ x.twin)
    (hnextT : st.nextUp x.twin = true)
    (hblockT : ¬ CanRaise st x.twin)
    (hshape : (st.piles a).faceUp = bs ++ c :: u1 :: run) :
    (st.piles a).top ≠ some x.twin := by
  intro htop
  have hpod : st.pileOfTop x.twin = some a := (pileOfTop_eq_some_iff hwf).2 htop
  have hchop : chop (st.piles a).faceUp ≠ [] := by
    rw [hshape]
    exact chop_ne_nil_of_two_le (by
      simp only [List.length_append, List.length_cons]
      omega)
  exact hblockT ⟨hnextT, a, hpod, Or.inl hchop⟩

/-- **No pile top is both S-live and blocked.**  If `c` tops a pile then
the flat characterization's seat clause is exactly `CanRaise`'s: the flat
witness is `c` on top of its own pile, so `CanRaiseS` collapses to
`CanRaise`.  Consequence: whenever the drain's two letters leave the
protected twin as a pile top, the twin clause
`CanRaiseS · x.twin ∧ ¬ CanRaise · x.twin` is necessarily broken. -/
theorem not_both_of_top {st : State} {c : Card} {a : Anchor}
    (hwf : st.WF) (htop : (st.piles a).top = some c) :
    ¬ (CanRaiseS st c ∧ ¬ CanRaise st c) := by
  rintro ⟨hlive, hblock⟩
  obtain ⟨hnext, b, bs, run, hshape, hseat, hdisj⟩ :=
    canRaiseS_flat_necessity hwf hlive
  have hmemA : c ∈ (st.piles a).faceUp := Pile.mem_of_top htop
  have hmemB : c ∈ (st.piles b).faceUp := by
    rw [hshape]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  have hba : b = a := by
    by_cases h : b = a
    · exact h
    · exact absurd hmemA ((mem_faceUp_unique hwf hmemB a (Ne.symm h)).1)
  rw [hba] at hshape hseat
  have hpod : st.pileOfTop c = some a := (pileOfTop_eq_some_iff hwf).2 htop
  have hchop : chop (st.piles a).faceUp ≠ [] ∨
      ((st.piles a).hidden = [] ∧ c.rank = Rank.king) := by
    rcases hseat with hbs | hbk
    · refine Or.inl ?_
      rw [hshape]
      apply chop_ne_nil_of_two_le
      cases bs with
      | nil => exact absurd rfl hbs
      | cons w ws =>
          simp only [List.length_append, List.length_cons]
          omega
    · exact Or.inr hbk
  exact hblock ⟨hnext, a, hpod, hchop⟩

/-! ### §4.2 The surviving case is harmless: the twin keeps a card above it

The slide moves the whole run `u1 :: run` as a block onto `c.twin`'s pile,
so the twin's position *inside* the run is preserved.  All that is needed
is that the twin is not the run's last (top) card — otherwise it would
already top `c`'s pile at `st` and be vanilla raisable.
-/

/-- Split a list at a member (the `List.mem_iff_append` normal form). -/
theorem split_of_mem {x : Card} {l : List Card} (hmem : x ∈ l) :
    ∃ pre post, l = pre ++ x :: post :=
  List.mem_iff_append.mp hmem

/-- **A member that is not the `lastOf` has something above it.**  If `x`
occurs in `l` but is not `l`'s last element, then `l` splits as
`pre ++ x :: post` with `post ≠ []`.  Applied to the run above `c`, this
says the protected twin keeps a card above it after the slide. -/
theorem post_ne_nil_of_lastOf_ne {x : Card} {l : List Card}
    (h : lastOf l ≠ some x) (hmem : x ∈ l) :
    ∃ pre post, l = pre ++ x :: post ∧ post ≠ [] := by
  obtain ⟨pre, post, hsplit⟩ := split_of_mem hmem
  refine ⟨pre, post, hsplit, ?_⟩
  cases post with
  | nil =>
      exfalso
      apply h
      rw [hsplit]
      exact lastOf_snoc
  | cons p ps => exact List.cons_ne_nil p ps

/-- **The `x.twin ∈ run` split.**  In the surviving dangerous case the run
above `c` splits as `pre ++ x.twin :: post` with `post ≠ []`: after the
slide the twin still has `post` above it on `c.twin`'s pile, so it keeps
being covered (and hence stays blocked) and its flat run stays nonempty
(and hence it stays S-live). -/
theorem twin_run_keeps_cover {st : State} {x c : Card} (hwf : st.WF)
    {a : Anchor} {bs run : List Card} {u1 : Card}
    (hct : c ≠ x.twin)
    (hnextT : st.nextUp x.twin = true)
    (hblockT : ¬ CanRaise st x.twin)
    (hshape : (st.piles a).faceUp = bs ++ c :: u1 :: run)
    (hmem : x.twin ∈ u1 :: run) :
    (∃ pre post, u1 :: run = pre ++ x.twin :: post ∧ post ≠ []) ∧
      x.rank.toIdx < c.rank.toIdx := by
  have htop : (st.piles a).top ≠ some x.twin :=
    twin_not_top_of_c_pile hwf hct hnextT hblockT hshape
  have hlast_face : lastOf (st.piles a).faceUp ≠ some x.twin := htop
  have hlast_run : lastOf (u1 :: run) ≠ some x.twin := by
    intro h
    apply hlast_face
    rw [hshape, tfc_lastOf_append_ne bs (List.cons_ne_nil c (u1 :: run))]
    rw [show lastOf (c :: u1 :: run) = lastOf (u1 :: run) from rfl]
    exact h
  exact ⟨post_ne_nil_of_lastOf_ne hlast_run hmem,
    twin_above_c_rank hwf hshape hmem⟩

/-! ## §5. Target 3: transporting the displaced invariant across the
two-letter drain (the reduction)

The two letters are `tabToTab u1 (inr c.twin)` (the slide) and then
`tabToFound c` (the raise).  Their endpoint `z` is characterised by
three frame facts:

* the twin's pile keeps a legal split `B ++ x.twin :: R` with `R ≠ []`
  (the twin stays covered);
* `z.nextUp x.twin = true` (the raise writes only `c`'s foundation, and
  `c.suit ≠ x.twin.suit` because both are next-up at rank `x.rank` only
  if `c = x.twin`);
* `x` still tops a pile with a nonempty chop (`CanRaise z x`).

The two clauses below are exactly the flat-characterization content; they
reduce target 3 to those frame facts plus the rank-floor transport.
-/

/-- **The twin clause at the endpoint, from the endpoint's flat split.**
If `x.twin` still has a *nonempty* run above it at the `WF` endpoint `z`,
then `CanRaiseS z x.twin` (flat sufficiency) and `¬ CanRaise z x.twin`
(the twin is covered, so it cannot top a pile). -/
theorem twin_clause_of_flat {z : State} {x : Card} {p : Anchor}
    {B R : List Card}
    (hwf : z.WF)
    (hnext : z.nextUp x.twin = true)
    (hshape : (z.piles p).faceUp = B ++ x.twin :: R)
    (hseat : B ≠ [] ∨ ((z.piles p).hidden = [] ∧ x.twin.rank = Rank.king))
    (hxtop : z.pileOfTop x ≠ none)
    (hR : R ≠ []) :
    CanRaiseS z x.twin ∧ ¬ CanRaise z x.twin := by
  have hxtop' : z.pileOfTop x.twin.twin ≠ none := by
    rw [card_twin_twin]; exact hxtop
  have hlive : CanRaiseS z x.twin :=
    canRaiseS_flat_sufficiency hwf ⟨hnext, p, B, R, hshape, hseat, Or.inr hxtop'⟩
  refine ⟨hlive, ?_⟩
  intro hcan
  obtain ⟨-, a, hpod, -⟩ := hcan
  have htopA : (z.piles a).top = some x.twin := (pileOfTop_top hpod).2
  have hmemA : x.twin ∈ (z.piles a).faceUp := Pile.mem_of_top htopA
  have hmemP : x.twin ∈ (z.piles p).faceUp := by
    rw [hshape]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  have hpa : p = a := by
    by_cases h : p = a
    · exact h
    · exact absurd hmemP ((mem_faceUp_unique hwf hmemA p h).1)
  rw [hpa] at hshape
  -- `x.twin` is last in pile `a` but `hshape` has `R ≠ []` after it
  have h1 : lastOf (B ++ x.twin :: R) = some x.twin := by
    rw [← hshape]; exact htopA
  cases R with
  | nil => exact absurd rfl hR
  | cons r rs =>
      rw [tfc_lastOf_append_ne B (List.cons_ne_nil x.twin (r :: rs))] at h1
      rw [show lastOf (x.twin :: r :: rs) = lastOf (r :: rs) from rfl] at h1
      have hmemR : x.twin ∈ r :: rs := lastOf_mem h1
      have hok : runOK (B ++ x.twin :: r :: rs) = true := by
        rw [← hshape]; exact hwf.2.1 a
      have hok' : runOK ((B ++ [x.twin]) ++ (r :: rs)) = true := by
        rw [List.append_assoc, List.cons_append, List.nil_append]; exact hok
      have hlt := runOK_desc hok'
        (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))) hmemR
      omega

/-- **`CanRaise` at the endpoint, from the endpoint's top split.** -/
theorem canRaise_of_flat_top {z : State} {x : Card} {q : Anchor}
    {B : List Card}
    (hnext : z.nextUp x = true)
    (hpod : z.pileOfTop x = some q)
    (hshape : (z.piles q).faceUp = B ++ [x])
    (hseat : B ≠ [] ∨ ((z.piles q).hidden = [] ∧ x.rank = Rank.king)) :
    CanRaise z x :=
  ⟨hnext, q, hpod, by rw [hshape, chop_snoc]; exact hseat⟩

/-- **TARGET 3 — `drain_step_other_live`, reduction form.**  For a blocked
live `c ∉ {x, x.twin}`, the two-letter drain (slide `c`'s run onto
`c.twin`, then raise `c`) preserves the whole displaced invariant
provided the endpoint has the frame listed above.  The rank-floor
conjunct is the one genuinely open transport (`rank_preserved`,
`Temp/Drain_Report.md:172`); it is *not* derivable from the three frame
facts alone, so it enters as the named hypothesis `hfloor`.

The twin-side frame needs NO side condition beyond the hypotheses below:
by `no_twin_below_c` the twin is not below `c`, and by
`twin_not_top_of_c_pile` the twin keeps a card above it in the run case
(so the run above it at the endpoint is again nonempty). -/
theorem drain_step_other_live {z : State} {x c : Card} {p q : Anchor}
    {B R Bx : List Card}
    (hwf : z.WF)
    (hc : c ≠ x) (hct : c ≠ x.twin)
    -- the twin clause's endpoint frame
    (hnextT : z.nextUp x.twin = true)
    (hshapeT : (z.piles p).faceUp = B ++ x.twin :: R)
    (hseatT : B ≠ [] ∨ ((z.piles p).hidden = [] ∧ x.twin.rank = Rank.king))
    (hxtop : z.pileOfTop x ≠ none)
    (hR : R ≠ [])
    -- the protected card `x`'s endpoint frame
    (hnextX : z.nextUp x = true)
    (hpodX : z.pileOfTop x = some q)
    (hshapeX : (z.piles q).faceUp = Bx ++ [x])
    (hseatX : Bx ≠ [] ∨ ((z.piles q).hidden = [] ∧ x.rank = Rank.king))
    -- the residual rank-floor transport
    (hfloor : ∀ d, CanRaiseS z d → x.rank.toIdx ≤ d.rank.toIdx) :
    CanRaiseS z x.twin ∧ ¬ CanRaise z x.twin ∧ CanRaise z x ∧
      (∀ d, CanRaiseS z d → x.rank.toIdx ≤ d.rank.toIdx) := by
  obtain ⟨hS, hB⟩ := twin_clause_of_flat hwf hnextT hshapeT hseatT hxtop hR
  exact ⟨hS, hB, canRaise_of_flat_top hnextX hpodX hshapeX hseatX, hfloor⟩

/-! ## §6. The RAISE letter is already closed in the library

The drain's second letter is `tabToFound c`.  Its effect on the protected
twin is fully available in `Orig2`:

* `CanRaiseS` is transported by
  `SafeTransport.canRaiseS_of_canRaiseS_raise_high`
  (`Orig2/Fork/Local/ForkSafeTransport.lean:151`) — the flat characterization route
  (no reversibility needed);
* `¬ CanRaise` is the contrapositive of
  `ValleyDrain.canRaise_of_raise_high` (`Orig2/Fork/Split/ForkDrain.lean:98`).

Both need only `c.suit ≠ x.twin.suit`, `c ≠ x` and
`x.twin.rank ≤ c.rank`, and the drain invariant supplies all three.
So the raise half of target 3 is *proved*, and the `CanRaiseS_preserved`
input of `Temp/Drain_Report.md:149` is discharged.
-/

/-- **`¬ CanRaise` survives a high raise** — the contrapositive of
`ValleyDrain.canRaise_of_raise_high` (`Orig2/Fork/Split/ForkDrain.lean:98`). -/
theorem not_canRaise_raise_high {st w : State} {c d : Card} {b : Anchor}
    (hwf : st.WF) (hstep : State.step st (Move.tabToFound c) = some w)
    (hsu : d.suit ≠ c.suit) (hrank : d.rank.toIdx ≤ c.rank.toIdx)
    (hd : st.pileHolding d = some b) (h : ¬ CanRaise st d) :
    ¬ CanRaise w d :=
  fun hw => h (ValleyDrain.canRaise_of_raise_high hwf hstep hsu hd hrank hw)

/-- **The raise letter preserves the twin clause** (both halves), given
the twin clause at the pre-state and the standard disjointness data. -/
theorem twin_clause_raise {u w : State} {x c : Card}
    (huwf : u.WF) (hstep : u.step (Move.tabToFound c) = some w)
    (hcs : c.suit ≠ x.twin.suit) (hcx : c ≠ x)
    (hrank : x.twin.rank.toIdx ≤ c.rank.toIdx)
    (hS : CanRaiseS u x.twin) (hB : ¬ CanRaise u x.twin) :
    CanRaiseS w x.twin ∧ ¬ CanRaise w x.twin := by
  obtain ⟨-, a, bs, run, hshape, -, -⟩ := canRaiseS_flat_necessity huwf hS
  have hmem : x.twin ∈ (u.piles a).faceUp := by
    rw [hshape]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  have hd : u.pileHolding x.twin = some a := (pileHolding_eq_some_iff huwf).2 hmem
  refine ⟨SafeTransport.canRaiseS_of_canRaiseS_raise_high huwf hstep hcs ?_ hrank hS,
    ?_⟩
  · -- `c ≠ x.twin.twin`
    intro h
    rw [card_twin_twin] at h
    exact hcx h
  · exact not_canRaise_raise_high huwf hstep (Ne.symm hcs) hrank hd hB

/-- **`CanRaiseS_preserved`, discharged** — the exact transport statement
that `Temp/Drain_Report.md:149` (`RaiseTransport.CanRaiseS_preserved`,
`Temp/Drain_Invariant.lean:558`) leaves as the open input: a raise of a
live card `c` outside the protected pair preserves `CanRaiseS · x.twin`.
The suit inequality is derived from `nextUp` (two cards next-up in the
same suit have equal rank, hence are equal). -/
theorem CanRaiseS_preserved_proved {u u' : State} {x c : Card}
    (huwf : u.WF) (hS : CanRaiseS u x.twin) (hB : ¬ CanRaise u x.twin)
    (hcan : CanRaise u c) (hcx : c ≠ x) (hct : c ≠ x.twin)
    (hfloor : ∀ d, CanRaiseS u d → x.rank.toIdx ≤ d.rank.toIdx)
    (hstep : u.step (Move.tabToFound c) = some u') :
    CanRaiseS u' x.twin ∧ ¬ CanRaise u' x.twin := by
  have hnextc : u.nextUp c = true := hcan.1
  have hnextT : u.nextUp x.twin = true := (canRaiseS_flat_necessity huwf hS).1
  have hcs : c.suit ≠ x.twin.suit := by
    intro hs
    have h1 : c.rank.toIdx = (u.found c.suit).length := of_decide_eq_true hnextc
    have h2 : x.twin.rank.toIdx = (u.found x.twin.suit).length :=
      of_decide_eq_true hnextT
    rw [hs] at h1
    have hrc : c.rank.toIdx = x.twin.rank.toIdx := by rw [h1, h2]
    have hce : c = x.twin := by
      cases c with
      | mk sc rc =>
        cases x with
        | mk sx rx =>
          simp only [Card.twin, Card.mk.injEq] at hs hrc ⊢
          exact ⟨hs, Rank.toIdx_inj hrc⟩
    exact hct hce
  have hfeq : x.twin.rank.toIdx = x.rank.toIdx := rfl
  have hrank : x.twin.rank.toIdx ≤ c.rank.toIdx := by
    rw [hfeq]
    exact hfloor c (CanRaiseS.now c hcan)
  exact twin_clause_raise huwf hstep hcs hcx hrank hS hB

end OneSlide

/-! ## Battery -/

#print axioms OneSlide.run_ne_nil
#print axioms OneSlide.twin_top_of_cover
#print axioms OneSlide.cover_fit_twin
#print axioms OneSlide.cover_slide_exists
#print axioms OneSlide.one_slide_of_blocked_live
#print axioms OneSlide.twin_pair_disjoint
#print axioms OneSlide.cover_unique
#print axioms OneSlide.u1_not_cover_twin
#print axioms OneSlide.no_twin_below_c
#print axioms OneSlide.no_c_above_twin
#print axioms OneSlide.twin_above_c_rank
#print axioms OneSlide.twin_not_top_of_c_pile
#print axioms OneSlide.split_of_mem
#print axioms OneSlide.post_ne_nil_of_lastOf_ne
#print axioms OneSlide.twin_run_keeps_cover
#print axioms OneSlide.not_both_of_top
#print axioms OneSlide.twin_clause_of_flat
#print axioms OneSlide.canRaise_of_flat_top
#print axioms OneSlide.drain_step_other_live
#print axioms OneSlide.not_canRaise_raise_high
#print axioms OneSlide.twin_clause_raise
#print axioms OneSlide.CanRaiseS_preserved_proved
