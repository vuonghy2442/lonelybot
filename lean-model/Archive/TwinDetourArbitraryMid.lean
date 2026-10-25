import Orig2.TwinLastPull
import Orig2.TwinSuffixCancel
import Orig2.TwinPreludeCollapse
import Orig2.TwinRaiseCommute
import Orig2.TwinAbstractLadder

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2.TwinDetourArbitraryMid — the single raise-pull detour

A single detour of the twin pair `{x, x.twin}` is a play

```
raise y  ++  mid  ++  pull y p
```

where `y ∈ {x, x.twin}`, `y` is seated on the card parent `p` at the
source, and `mid` never raises or pulls either twin.  This card studies
the two endpoint conclusions of the detour:

* **identity** — the pull returns `y` to its original parent `p`; the
  expected endpoint is pair-free orbit to the source;
* **exchange** — the pull lands on `p.twin`; the expected endpoint is
  pair-free orbit to the run splice `u.spliceTwinRuns x`.

The tractable cases are proved unconditionally:

* `pairFreeReversal_unseated`: pair-free witness shuffles are
  pair-free reversible **without any seat hypothesis at the source**
  (the public `TwinPairFreeRev.pairFreeReversal` asks both twins
  `.inr`-seated; the proof below deletes that bookkeeping);
* `singleDetour_identity_noMid`: the empty middle, where the raise and
  pull are a state-level round trip;
* `singleDetour_identity_drawMid`: the middle consists only of draws;
  the draw play is pair-free and reverses, so the endpoint is
  pair-free orbit to the source even though the draw zone moved;
* `singleDetour_exchange_canonical`: the canonical one-slide exchange
  `raise x, slide x.twin onto p, pull x onto p.twin`, whose endpoint
  is exactly the run splice.

The exact remaining goal for an arbitrary pair-free `mid` is stated at
the end (`SingleDetourIdentityArbitraryMid` and
`SingleDetourExchangeArbitraryMid`).  The obstruction is precisely the
one identified in `Orig2/TwinRaiseCommute.lean`: a pair-free `mid` may
raise the pull target `p` itself (or move cards of the raised card's
foundation row), and those letters cannot be re-associated past the
outer raise/pull by the available positive squares.  The endpoint
*pair* seats are nevertheless pinned (identity for the `p`-pull,
exchange for the `p.twin`-pull); only the state-level re-association is
missing.

Zero `sorry`, zero `Classical.choice`, no new axioms.
-/

open State

namespace TwinDetourArbitraryMid

/-! ## §0. Walk kit -/

/-- Expose the first letter of a witness walk. -/
private theorem walk_cons_inv {P : State → Move → Prop} {st s' : State}
    {m : Move} {ρ : List Move} (h : Walk P st (m :: ρ) s') :
    ∃ s1, P st m ∧ State.step st m = some s1 ∧ Walk P s1 ρ s' := by
  cases h with
  | cons hlet hstep hrest => exact ⟨_, hlet, hstep, hrest⟩

/-- A card seated on a card parent lies directly on it. -/
private theorem below_eq_chop_of_last {l : List Card} {c : Card}
    (hnd : l.Nodup) (hlast : lastOf l = some c) : below c l = chop l := by
  induction l with
  | nil =>
      rw [lastOf] at hlast
      exact absurd hlast (by simp)
  | cons y t ih =>
      cases t with
      | nil =>
          rw [lastOf] at hlast
          injection hlast with hcy
          subst hcy
          rw [below_cons, ite_eq_left rfl]
          rfl
      | cons z t' =>
          have hnd' : (z :: t').Nodup := (List.nodup_cons.mp hnd).2
          have hyc : y ≠ c := by
            intro hcon
            subst hcon
            exact (List.nodup_cons.mp hnd).1 (lastOf_mem hlast)
          have htl : lastOf (z :: t') = some c := hlast
          rw [below, ite_eq_right hyc]
          rw [show chop (y :: z :: t') = y :: chop (z :: t') from rfl]
          rw [ih hnd' htl]

/-! ## §1. Pair-free reversal without seat hypotheses -/

/-- **Pair-free reversal, unseated source.**  Every pair-free witness
shuffle is pair-free reversible, with no hypothesis on either twin's
seat.  This is the public reversal theorem with the seat bookkeeping
deleted; it is the engine used when the raised card is off the
tableau. -/
theorem pairFreeReversal_unseated {x : Card} :
    ∀ {u v : State} {play : List Move},
      u.WF → ShufflePlayW u play v →
      (∀ m ∈ play, NotFoundPair x m) → PairFreeOrbit x v u := by
  intro u v play
  induction play generalizing u with
  | nil =>
      intro _ hplay _
      cases hplay
      exact pairFreeOrbit_refl x _
  | cons m rest ih =>
      intro hwf hplay hno
      cases hplay with
      | @cons _ s1 _ _ _ hrev hstep hrest =>
          have hm : NotFoundPair x m := hno m (by simp)
          have hwf1 : s1.WF := step_wf hwf hstep
          have ih' := ih hwf1 hrest
            (fun n hn => hno n (List.mem_cons_of_mem m hn))
          by_cases hmd : m = Move.draw
          · have hstepD : State.step u Move.draw = some s1 := by
              rw [← hmd]; exact hstep
            have hrevD : reversibleAtW u Move.draw := by
              rw [← hmd]; exact hrev
            have horbit : PairFreeOrbit x s1 u :=
              TwinPairFreeRev.draw_inverse_orbit hwf hstepD hrevD
            exact PairFreeOrbit.trans ih' horbit
          · obtain ⟨m', hstep', hno', hrev'⟩ :=
              TwinPairFreeRev.exists_step_inverse_pairFree_noDraw hwf hstep hrev hmd hm
            have horbit : PairFreeOrbit x s1 u :=
              pairFreeOrbit_of_play (Walk.cons hrev' hstep' (Walk.nil u)) (by
                intro n hn
                rw [List.mem_singleton.mp hn]
                exact hno')
            exact PairFreeOrbit.trans ih' horbit

/-! ## §2. The empty-middle identity -/

/-- **Raise-then-pull cancellation (self-contained).**  Raising a card
off its card parent and then pulling it back onto that parent restores
the source exactly.  Verbatim copy of the private
`TwinSuffixCancel.tsc_raise_pull_self_eq`. -/
private theorem raise_pull_self_eq_copy {s s₁ s₂ : State} {c z : Card}
    (hwf : s.WF)
    (hx : seatOf s c = some (Sum.inr z))
    (hraise : State.step s (Move.tabToFound c) = some s₁)
    (hpull : State.step s₁ (Move.foundToTab c (Sum.inr z)) = some s₂) :
    s₂ = s := by
  obtain ⟨a, hhold, _hbelow_ne, hlast⟩ := tfc_seatOf_of_inr hx
  obtain ⟨_hnext, a₀, hpa₀, hs₁⟩ := step_tabToFound_inv hraise
  have htop₀ : (s.piles a₀).top = some c := (tfc_pileOfTop_top hpa₀).2
  have hhold₀ : s.pileHolding c = some a₀ :=
    (pileHolding_eq_some_iff hwf).mpr (Pile.mem_of_top htop₀)
  have ha₀ : a₀ = a := pileHolding_inj hhold₀ hhold
  subst a₀
  let st₁ : State :=
    { s.setFound c.suit (s.found c.suit ++ [c]) with
      piles := fun a' => if a' = a then
          Pile.afterRunRemoved (s.piles a) (chop (s.piles a).faceUp)
        else s.piles a' }
  have hs₁' : s₁ = st₁ := hs₁
  have htop : lastOf (s.piles a).faceUp = some c := (tfc_pileOfTop_top hpa₀).2
  have hface : (s.piles a).faceUp = chop (s.piles a).faceUp ++ [c] :=
    lastOf_chop htop
  have hnodup : (s.piles a).faceUp.Nodup := runOK_nodup (hwf.runOK_of a)
  have hc_not_chop : c ∉ chop (s.piles a).faceUp := by
    rw [hface] at hnodup
    exact List.snoc_nodup_notMem _ _ hnodup
  have hbelow_eq : below c (s.piles a).faceUp = chop (s.piles a).faceUp := by
    conv => lhs; rw [hface]
    exact below_snoc_not_mem hc_not_chop
  have hlast_chop : lastOf (chop (s.piles a).faceUp) = some z := by
    rw [← hbelow_eq]
    exact hlast
  have hchop_ne : chop (s.piles a).faceUp ≠ [] := by
    intro h
    rw [h] at hlast_chop
    nomatch hlast_chop
  have hs₁_pa : s₁.piles a =
      Pile.afterRunRemoved (s.piles a) (chop (s.piles a).faceUp) := by
    rw [hs₁']
    simp only [st₁, ite_true]
  have hs₁_pne : ∀ a' ≠ a, s₁.piles a' = s.piles a' := by
    intro a' ha'
    rw [hs₁']
    simp only [st₁, ite_eq_right ha']
  have hs₁_face : (s₁.piles a).faceUp = chop (s.piles a).faceUp := by
    rw [hs₁_pa, afterRunRemoved_faceUp_ne hchop_ne]
  have hwf₁ : s₁.WF := step_wf hwf hraise
  have hs₁_top_z : s₁.pileOfTop z = some a := by
    rw [pileOfTop_eq_some_iff hwf₁]
    show lastOf (s₁.piles a).faceUp = some z
    rw [hs₁_face]
    exact hlast_chop
  have hfit : canSitOn c z = true := (tfc_seat_parent hwf hhold hlast).1
  have hcp : s₁.canPlace c (Sum.inr z) = true := by
    rw [canPlace_inr_located hs₁_top_z]
    exact hfit
  have hfound_trio := tabToFound_found_trio (st := s) (s₁ := s₁)
    (c := c) (a := a) hs₁
  have hs₁_found_self : s₁.found c.suit = s.found c.suit ++ [c] :=
    hfound_trio.1
  have hs₁_found_ne : ∀ σ, σ ≠ c.suit → s₁.found σ = s.found σ :=
    hfound_trio.2.1
  have hs₁_foundTop : s₁.foundTop c.suit = some c := hfound_trio.2.2
  have hpull_eq : s₂ =
      (s₁.setFound c.suit (chop (s₁.found c.suit))).putCard c (Sum.inr z) := by
    have hfire := step_foundToTab_splice (st := s₁) (c := c)
      (b := Sum.inr z) hs₁_foundTop hcp
    rw [hfire] at hpull
    exact (Option.some.inj hpull).symm
  subst hpull_eq
  refine State.ext ?_ ?_ ?_ ?_ ?_
  · funext σ
    rw [putCard_found]
    by_cases hσ : σ = c.suit
    · rw [hσ, setFound_found_self, hs₁_found_self, chop_snoc]
    · rw [setFound_found_ne hσ, hs₁_found_ne σ hσ]
  · funext a'
    have hset_top : (s₁.setFound c.suit (chop (s₁.found c.suit))).pileOfTop z =
        some a := by
      unfold State.pileOfTop State.topOf
      rw [setFound_piles]
      exact hs₁_top_z
    rw [putCard_piles_inr (s₁.setFound c.suit (chop (s₁.found c.suit))) c z a
      hset_top]
    dsimp only
    by_cases ha' : a' = a
    · rw [ha', ite_eq_left rfl, setFound_piles]
      apply Pile.ext
      · rw [hs₁_pa, afterRunRemoved_ne hchop_ne]
      · rw [hs₁_face]
        exact hface.symm
    · rw [ite_eq_right ha', setFound_piles, hs₁_pne a' ha']
  · rw [putCard_stock, setFound_stock]
    rw [hs₁']
    rfl
  · rw [putCard_waste, setFound_waste]
    rw [hs₁']
    rfl
  · rw [putCard_drawStep, setFound_drawStep]
    rw [hs₁']
    rfl

/-- **The empty-middle detour is a state-level loop.**  Raising `y` and
pulling it straight back onto its original card parent `p` restores the
source. -/
theorem singleDetour_identity_noMid_eq
    {u v : State} {x y : Card} {p : Card}
    (hwf : u.WF)
    (hy : y = x ∨ y = x.twin)
    (hseatY : seatOf u y = some (Sum.inr p))
    (hplay : ShufflePlayW u
      (Move.tabToFound y :: ([] : List Move) ++ [Move.foundToTab y (Sum.inr p)]) v) :
    v = u := by
  obtain ⟨r, hrevR, hraise, hrest⟩ := walk_cons_inv hplay
  obtain ⟨v', hrevP, hpull, hnil⟩ := walk_cons_inv hrest
  cases hnil
  exact raise_pull_self_eq_copy hwf hseatY hraise hpull

/-- **The empty-middle identity detour.**  With `mid = []` the endpoint
is pair-free orbit to the source by reflexivity. -/
theorem singleDetour_identity_noMid
    {u v : State} {x y : Card} {p : Card}
    (hwf : u.WF)
    (hx : ∃ z, seatOf u x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin))
    (hy : y = x ∨ y = x.twin)
    (hseatY : seatOf u y = some (Sum.inr p))
    (hplay : ShufflePlayW u
      (Move.tabToFound y :: ([] : List Move) ++ [Move.foundToTab y (Sum.inr p)]) v)
    (_hvx : ∃ w, seatOf v x = some (Sum.inr w))
    (_hvt : ∃ w' : Card, seatOf v x.twin = some (Sum.inr w'.twin)) :
    PairFreeOrbit x v u := by
  rw [singleDetour_identity_noMid_eq hwf hy hseatY hplay]
  exact pairFreeOrbit_refl x u

/-! ## §3. The canonical exchange -/

/-- **The canonical exchange detour.**  Raising `x`, sliding `x.twin`
onto the vacated parent `p`, and pulling `x` onto `p.twin` is exactly
the three-leg ladder; its endpoint is the run splice. -/
theorem singleDetour_exchange_canonical
    {u v : State} {x p : Card}
    (hwf : u.WF)
    (hx : seatOf u x = some (Sum.inr p))
    (hxt : seatOf u x.twin = some (Sum.inr p.twin))
    (hplay : ShufflePlayW u
      (Move.tabToFound x :: [Move.tabToTab x.twin (Sum.inr p)] ++
        [Move.foundToTab x (Sum.inr p.twin)]) v)
    (_hvx : ∃ w, seatOf v x = some (Sum.inr w))
    (_hvt : ∃ w' : Card, seatOf v x.twin = some (Sum.inr w'.twin)) :
    PairFreeOrbit x v (u.spliceTwinRuns x) := by
  have hplay' : ShufflePlayW u (ladderPlay x p []) v := by
    simpa [ladderPlay, ladderPlayRev] using hplay
  have hwf' : v.WF := run_wf hwf (Walk_run _ hplay')
  have hseg : SelfSwapSeg x u v (ladderPlay x p []) :=
    selfSwapSeg_abstractLadder (ys := []) hwf hwf' hx hxt trivial hplay'
  obtain ⟨-, -, -, -, hveq⟩ := hseg
  rw [hveq]
  exact pairFreeOrbit_refl x (u.spliceTwinRuns x)

/-! ## §4. The exact residual -/

/-- **The arbitrary-middle identity residual.**  The exact remaining
Lean obligation for a `p`-pull: a pair-free middle between the raise
and the pull, with the pull restoring the original parent, must end
pair-free orbit to the source. -/
def SingleDetourIdentityArbitraryMid (x : Card) : Prop :=
  ∀ {u v : State} {y : Card} {p : Card} {mid : List Move},
    u.WF →
    (∃ z, seatOf u x = some (Sum.inr z)) →
    (∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin)) →
    (y = x ∨ y = x.twin) →
    seatOf u y = some (Sum.inr p) →
    ShufflePlayW u
      (Move.tabToFound y :: mid ++ [Move.foundToTab y (Sum.inr p)]) v →
    (∀ m ∈ mid, NotFoundPair x m) →
    (∃ w, seatOf v x = some (Sum.inr w)) →
    (∃ w' : Card, seatOf v x.twin = some (Sum.inr w'.twin)) →
    PairFreeOrbit x v u

/-- **The arbitrary-middle exchange residual.**  The exact remaining
Lean obligation for a `p.twin`-pull: the endpoint is pair-free orbit to
the run splice. -/
def SingleDetourExchangeArbitraryMid (x : Card) : Prop :=
  ∀ {u v : State} {y : Card} {p : Card} {mid : List Move},
    u.WF →
    (∃ z, seatOf u x = some (Sum.inr z)) →
    (∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin)) →
    (y = x ∨ y = x.twin) →
    seatOf u y = some (Sum.inr p) →
    ShufflePlayW u
      (Move.tabToFound y :: mid ++ [Move.foundToTab y (Sum.inr p.twin)]) v →
    (∀ m ∈ mid, NotFoundPair x m) →
    (∃ w, seatOf v x = some (Sum.inr w)) →
    (∃ w' : Card, seatOf v x.twin = some (Sum.inr w'.twin)) →
    PairFreeOrbit x v (u.spliceTwinRuns x)

/-! ## §5. Interface to the exact mandatory statements -/

/-- **The exact mandatory statement, conditional on the residual.**
This is the requested signature

```
theorem singleDetour_identity_arbitraryMid
    {u v : State} {x y : Card} {p : Card} {mid : List Move}
    (hwf : u.WF)
    (hx : ∃ z, seatOf u x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin))
    (hy : y = x ∨ y = x.twin)
    (hseatY : seatOf u y = some (Sum.inr p))
    (hplay : ShufflePlayW u
      (Move.tabToFound y :: mid ++ [Move.foundToTab y (Sum.inr p)]) v)
    (hnoMid : ∀ m ∈ mid, NotFoundPair x m)
    (hvx : ∃ w, seatOf v x = some (Sum.inr w))
    (_hvt : ∃ w' : Card, seatOf v x.twin = some (Sum.inr w'.twin)) :
    PairFreeOrbit x v u
```

with the still-open arbitrary-middle row supplied as a hypothesis. -/
theorem singleDetour_identity_arbitraryMid_of_residual
    {x : Card} (hres : SingleDetourIdentityArbitraryMid x)
    {u v : State} {y : Card} {p : Card} {mid : List Move}
    (hwf : u.WF)
    (hx : ∃ z, seatOf u x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin))
    (hy : y = x ∨ y = x.twin)
    (hseatY : seatOf u y = some (Sum.inr p))
    (hplay : ShufflePlayW u
      (Move.tabToFound y :: mid ++ [Move.foundToTab y (Sum.inr p)]) v)
    (hnoMid : ∀ m ∈ mid, NotFoundPair x m)
    (hvx : ∃ w, seatOf v x = some (Sum.inr w))
    (hvt : ∃ w' : Card, seatOf v x.twin = some (Sum.inr w'.twin)) :
    PairFreeOrbit x v u :=
  hres hwf hx hxt hy hseatY hplay hnoMid hvx hvt

/-- **The exact mandatory exchange statement, conditional on the
residual.** -/
theorem singleDetour_exchange_arbitraryMid_of_residual
    {x : Card} (hres : SingleDetourExchangeArbitraryMid x)
    {u v : State} {y : Card} {p : Card} {mid : List Move}
    (hwf : u.WF)
    (hx : ∃ z, seatOf u x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin))
    (hy : y = x ∨ y = x.twin)
    (hseatY : seatOf u y = some (Sum.inr p))
    (hplay : ShufflePlayW u
      (Move.tabToFound y :: mid ++ [Move.foundToTab y (Sum.inr p.twin)]) v)
    (hnoMid : ∀ m ∈ mid, NotFoundPair x m)
    (hvx : ∃ w, seatOf v x = some (Sum.inr w))
    (hvt : ∃ w' : Card, seatOf v x.twin = some (Sum.inr w'.twin)) :
    PairFreeOrbit x v (u.spliceTwinRuns x) :=
  hres hwf hx hxt hy hseatY hplay hnoMid hvx hvt

/-! ## §6. Audit -/

#print axioms pairFreeReversal_unseated
#print axioms singleDetour_identity_noMid_eq
#print axioms singleDetour_identity_noMid
#print axioms singleDetour_exchange_canonical
#print axioms singleDetour_identity_arbitraryMid_of_residual
#print axioms singleDetour_exchange_arbitraryMid_of_residual

/-! ## §7. Report: the exact residual

### File

`Orig2/TwinDetourArbitraryMid.lean` (this file).  It does not import
`Orig2.TwinSingleDetour`, so no duplicate `PairFreeOrbit` is introduced.

### Proved unconditionally

* `pairFreeReversal_unseated`: pair-free witness shuffles are pair-free
  reversible **with no seat hypothesis at the source** (the raised card
  may be off the tableau).
* `singleDetour_identity_noMid_eq` / `singleDetour_identity_noMid`:
  the empty middle is a state-level loop.
* `singleDetour_exchange_canonical`: the canonical one-slide exchange
  ends exactly at `u.spliceTwinRuns x`.

### Exact remaining Lean obligations

```
def SingleDetourIdentityArbitraryMid (x : Card) : Prop :=
  ∀ {u v : State} {y : Card} {p : Card} {mid : List Move},
    u.WF →
    (∃ z, seatOf u x = some (Sum.inr z)) →
    (∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin)) →
    (y = x ∨ y = x.twin) →
    seatOf u y = some (Sum.inr p) →
    ShufflePlayW u
      (Move.tabToFound y :: mid ++ [Move.foundToTab y (Sum.inr p)]) v →
    (∀ m ∈ mid, NotFoundPair x m) →
    (∃ w, seatOf v x = some (Sum.inr w)) →
    (∃ w' : Card, seatOf v x.twin = some (Sum.inr w'.twin)) →
    PairFreeOrbit x v u

def SingleDetourExchangeArbitraryMid (x : Card) : Prop :=
  ∀ {u v : State} {y : Card} {p : Card} {mid : List Move},
    u.WF →
    (∃ z, seatOf u x = some (Sum.inr z)) →
    (∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin)) →
    (y = x ∨ y = x.twin) →
    seatOf u y = some (Sum.inr p) →
    ShufflePlayW u
      (Move.tabToFound y :: mid ++ [Move.foundToTab y (Sum.inr p.twin)]) v →
    (∀ m ∈ mid, NotFoundPair x m) →
    (∃ w, seatOf v x = some (Sum.inr w)) →
    (∃ w' : Card, seatOf v x.twin = some (Sum.inr w'.twin)) →
    PairFreeOrbit x v (u.spliceTwinRuns x)
```

The precise geometric gap is the following.  Write `r` for the state
after `raise y` and `w` for the state before the final pull.  A
pair-free middle cannot place any card on the pull target `p`: the
only cards fitting `p` are the two twins (`p.rank = y.rank + 1` and
`y ∈ {x, x.twin}`), and both are excluded by `hnoMid`.  Hence `p` is
never covered during `mid`.  If `mid` also never raises `p`, the same
letter list runs from `u` with `y` riding on `p`; the resulting
pair-free play `u → v` reverses by `pairFreeReversal_unseated`, which
settles the identity case.  The obstruction is exactly a `p`-excursion
(`tabToFound p` followed later by `foundToTab p b`) or a move of the
foundation row of `y.suit`: `p` is off-tableau there, so the attached
lift is undefined, and `Orig2/TwinRaiseCommute.lean` has no positive
square for a slide or pull onto a card base `Sum.inr` target.  The
endpoint `pair` seats are already pinned (identity for the `p`-pull by
`tsc_seat_eq_of_pairFree_play`, exchange for the `p.twin`-pull by
`lastPull_base_eq_parent_or_twin`); only the state-level re-association
is missing.  No counterexample is known.
-/

end TwinDetourArbitraryMid
