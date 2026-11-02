import Orig2.Fork
import Orig2.Substrate.Classification

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-!
# Orig2/ForkDrainInduction — the DRAIN-TO-FORK induction

READ-ONLY scratch card (not source; no edits, no commit).

THE MISSION: formalize the drain-to-fork induction.  From a state carrying
the twin asymmetry (one twin raisable, the other S-live but vanilla-blocked),
if every other live card is drainable by a reversible raise that preserves
the invariant, then a fork exists in the class.

## What is proved here

* `DrainInvariant` / `DrainTerminal` — the two definitions of the mission.
* `drain_terminal_fork` (TARGET 1, unconditional) — a terminal drain state
  is a `ForkWitness`, and hence `forkState` (`forkState_of_forkWitness`).
* `canRaise_of_raise_high_fwd` (NEW kit) — raising a card of rank `≥ d` in a
  different suit preserves `CanRaise d` *forward* (the mirror of
  `ValleyDrain.canRaise_of_raise_high`).
* `raise_step_preserves` (TARGET 2) — a reversible raise of a non-twin
  raisable card keeps `CanRaise x` and `¬ CanRaise x.twin`; the
  `CanRaiseS st' x.twin` conjunct is the named hypothesis
  `CanRaiseS_preserved`, exactly as instructed.
* `sameOrbit_of_step` / `sameOrbit_of_raise` (TARGET 3) — the raised state
  is `sameOrbitSetoid`-related, through the reversible letter.
* `drain_to_fork` (TARGET 4) — the well-founded (`Nat.strongRecOn`)
  induction on an abstract state measure.
* `rungSum_tabToFound` / `rungSum_le_52` (NEW kit) — a raise climbs the
  foundation rank-sum by exactly one; at `WF` the sum is at most 52.
* `drain_raise_phase` (TARGET 5) — the unconditional-in-shape raise-only
  corollary: termination by `52 - rungSum`, endpoint a fork, conditional on
  the named `RaiseTransport` inputs (whose first field is exactly
  `CanRaiseS_preserved`; the other two are the honest third-card residues).

## Conditional inputs (see `Temp/Drain_Report.md`)

* `CanRaiseS_preserved` — the exact `CanRaiseS` transport: `x.twin` stays
  S-live after the raise.
* `rank_preserved` — the invariant's rank floor survives the raise.
* `raisable_preserved` — "every non-twin live card is vanilla-raisable"
  survives the raise (the third-blocked-card case: new S-live cards must
  still be raisable).
* `hcanrev` — the vanilla raise of a non-twin live card really is reversible
  (a bare non-king lift is `CanRaise` but NOT reversible).
* `hdec` (target 4 only) — decidability of `DrainTerminal` at invariant
  states; a constructivity device, not a mathematical assumption.  At `WF`
  it is discharged by the census probe `canRaiseSB` (`drainTerminal_decidable`).

House compliance: zero `sorry`, zero `Classical.choice`, zero
`native_decide`; battery at the tail.
-/

namespace Drain

/-! ## §1. The definitions -/

/-- The drain invariant: one twin raisable, the other S-live but blocked,
nothing live below their rank, and every other live card is drainable. -/
def DrainInvariant (st : State) (x : Card) : Prop :=
  CanRaise st x ∧ CanRaiseS st x.twin ∧ ¬ CanRaise st x.twin ∧
  (∀ c, CanRaiseS st c → x.rank.toIdx ≤ c.rank.toIdx)

/-- Terminal: the only live cards are the twins. -/
def DrainTerminal (st : State) (x : Card) : Prop :=
  DrainInvariant st x ∧ ∀ c, CanRaiseS st c → c = x ∨ c = x.twin

/-- The carry-on condition of the raise-only phase: every live card outside
the twin pair is vanilla-raisable. -/
def DrainRaisable (st : State) (x : Card) : Prop :=
  ∀ c, CanRaiseS st c → c = x ∨ c = x.twin ∨ CanRaise st c

/-! ## §2. Elementary projections -/

theorem drain_canRaise {st : State} {x : Card} (h : DrainInvariant st x) :
    CanRaise st x := h.1

theorem drain_twinS {st : State} {x : Card} (h : DrainInvariant st x) :
    CanRaiseS st x.twin := h.2.1

theorem drain_twinBlocked {st : State} {x : Card} (h : DrainInvariant st x) :
    ¬ CanRaise st x.twin := h.2.2.1

theorem drain_rank_floor {st : State} {x : Card} (h : DrainInvariant st x) :
    ∀ c, CanRaiseS st c → x.rank.toIdx ≤ c.rank.toIdx := h.2.2.2

/-! ## §3. TARGET 1 — the terminal state is a fork -/

/-- A `ForkWitness` is the existential detection. -/
theorem forkState_of_forkWitness {st : State} {x : Card}
    (h : ForkWitness st x) : forkState st :=
  forkState_iff.mpr ⟨x, h⟩

/-- **TARGET 1.**  A terminal drain state is a fork witness: the pair is
exactly the live set, `x` is live through its vanilla license and `x.twin`
through the invariant, and `x.twin` is blocked. -/
theorem drain_terminal_fork {st : State} {x : Card} (h : DrainTerminal st x) :
    ForkWitness st x := by
  refine ⟨?_, h.1.2.2.1⟩
  intro c
  constructor
  · intro hc
    rcases hc with hx | hx
    · rw [hx]; exact CanRaiseS.now x h.1.1
    · rw [hx]; exact h.1.2.1
  · exact h.2 c

/-- **TARGET 1, detection form.** -/
theorem drain_terminal_forkState {st : State} {x : Card} (h : DrainTerminal st x) :
    forkState st :=
  forkState_of_forkWitness (drain_terminal_fork h)

/-! ## §4. Pile and rung kit -/

/-- A top card is held by its pile. -/
theorem pileHolding_of_pileOfTop {st : State} (hwf : st.WF) {c : Card} {a : Anchor}
    (h : st.pileOfTop c = some a) : st.pileHolding c = some a :=
  (pileHolding_eq_some_iff hwf).2
    (Pile.mem_of_top ((pileOfTop_eq_some_iff hwf).mp h))

/-- An S-live card has a holding pile (the flat characterization's seat). -/
theorem pileHolding_of_canRaiseS {st : State} (hwf : st.WF) {c : Card}
    (h : CanRaiseS st c) : ∃ a, st.pileHolding c = some a := by
  obtain ⟨-, a, bs, run, hface, -, -⟩ := (canRaiseS_iff hwf).mp h
  exact ⟨a, (pileHolding_eq_some_iff hwf).2 (by rw [hface]; simp)⟩

/-- An S-live card is next-up on its rung (no `WF` needed). -/
theorem nextUp_of_canRaiseS {st : State} {c : Card} (h : CanRaiseS st c) :
    st.nextUp c = true := by
  have hr := canRaiseS_rung h
  unfold State.nextUp State.foundHeight
  apply decide_eq_true
  show c.rank.toIdx = (st.found c.suit).length
  rw [← hr]
  rfl

/-- Two distinct cards that are both next-up have different suits. -/
theorem suit_ne_of_nextUp {st : State} {d c : Card}
    (hd : st.nextUp d = true) (hc : st.nextUp c = true) (hne : d ≠ c) :
    d.suit ≠ c.suit := by
  intro hsu
  have hdi : d.rank.toIdx = (st.found d.suit).length := by
    simpa [State.nextUp, State.foundHeight] using of_decide_eq_true hd
  have hci : c.rank.toIdx = (st.found c.suit).length := by
    simpa [State.nextUp, State.foundHeight] using of_decide_eq_true hc
  have hidx : d.rank.toIdx = c.rank.toIdx := by rw [hdi, hci, hsu]
  have hrank : d.rank = c.rank := Rank.toIdx_inj hidx
  have hdc : d = c := by
    obtain ⟨ds, dr⟩ := d
    obtain ⟨cs, cr⟩ := c
    simp_all
  exact hne hdc

/-! ## §5. The forward raise lemma (the mirror of `Valley_Drain`) -/

/-- **A raise cannot create a new raisable card outside its own pile**
(copied verbatim from `Temp/Valley_Drain.lean:28`, `ValleyDrain.canRaise_of_raise_other`:
temp modules have no oleans).  If `d`'s suit is untouched and `d`'s pile is
unchanged by the raise, then `CanRaise w d → CanRaise st d`. -/
theorem canRaise_of_raise_other {st w : State} {c d : Card}
    (hwf : st.WF) (hstep : State.step st (Move.tabToFound c) = some w)
    (hsu : d.suit ≠ c.suit)
    {b : Anchor} (hd : st.pileHolding d = some b)
    (hpiles : w.piles b = st.piles b)
    (h : CanRaise w d) : CanRaise st d := by
  obtain ⟨hnext_w, a1, hpa_w, hclause_w⟩ := h
  have hwfw : w.WF := step_wf hwf hstep
  obtain ⟨-, a0, hpa0, hs⟩ := step_tabToFound_inv hstep
  have hf : w.found d.suit = st.found d.suit := by
    rw [hs]
    exact setFound_found_ne hsu
  have hnext_st : st.nextUp d = true := by
    have h1 : d.rank.toIdx = (w.found d.suit).length := by
      simpa [State.nextUp, State.foundHeight] using of_decide_eq_true hnext_w
    rw [hf] at h1
    unfold State.nextUp
    apply decide_eq_true
    show d.rank.toIdx = (st.found d.suit).length
    exact h1
  have htop_w : (w.piles a1).top = some d :=
    (pileOfTop_eq_some_iff hwfw).mp hpa_w
  have hmem_w : d ∈ (w.piles b).faceUp := by
    rw [hpiles]
    exact pileHolding_mem hd
  have ha1 : a1 = b := by
    by_cases hne : a1 = b
    · exact hne
    · exfalso
      have hmem_a1 : d ∈ (w.piles a1).faceUp := Pile.mem_of_top htop_w
      have hnot : d ∉ (w.piles b).faceUp :=
        (mem_faceUp_unique hwfw hmem_a1 b (Ne.symm hne)).1
      exact hnot hmem_w
  have htop_st : (st.piles b).top = some d := by
    rw [← hpiles, ← ha1]
    exact htop_w
  have hpile_st : st.pileOfTop d = some b :=
    (pileOfTop_eq_some_iff hwf).mpr htop_st
  refine ⟨hnext_st, b, hpile_st, ?_⟩
  rcases hclause_w with hchop | ⟨hhid, hking⟩
  · left
    intro hnil
    rw [← hpiles, ← ha1] at hnil
    exact hchop hnil
  · right
    refine ⟨?_, hking⟩
    rw [← hpiles, ← ha1]
    exact hhid

/-- **The rank condition removes the cover** (copied verbatim from
`Temp/Valley_Drain.lean:98`, `ValleyDrain.canRaise_of_raise_high`). -/
theorem canRaise_of_raise_high {st w : State} {c d : Card} {b : Anchor}
    (hwf : st.WF) (hstep : State.step st (Move.tabToFound c) = some w)
    (hsu : d.suit ≠ c.suit)
    (hd : st.pileHolding d = some b)
    (hrank : d.rank.toIdx ≤ c.rank.toIdx)
    (h : CanRaise w d) : CanRaise st d := by
  obtain ⟨-, a0, hpa0, hs⟩ := step_tabToFound_inv hstep
  have hb_ne : b ≠ a0 := by
    intro hba
    have htop_c : (st.piles a0).top = some c :=
      (pileOfTop_eq_some_iff hwf).mp hpa0
    have hlast : lastOf (st.piles a0).faceUp = some c := htop_c
    have hface : (st.piles a0).faceUp = chop (st.piles a0).faceUp ++ [c] :=
      lastOf_chop hlast
    have hdmem : d ∈ (st.piles a0).faceUp := by
      rw [← hba]
      exact pileHolding_mem hd
    have hdne : d ≠ c := fun hdc => hsu (by rw [hdc])
    have hdchop : d ∈ chop (st.piles a0).faceUp := by
      rw [hface] at hdmem
      rcases List.mem_append.mp hdmem with h' | h'
      · exact h'
      · exact absurd (List.mem_singleton.mp h') hdne
    have hok : runOK (chop (st.piles a0).faceUp ++ [c]) = true := by
      rw [← hface]
      exact hwf.2.1 a0
    have hlt : c.rank.toIdx < d.rank.toIdx :=
      runOK_desc hok hdchop (List.mem_singleton_self c)
    omega
  have hpiles : w.piles b = st.piles b := by
    rw [hs]
    show (if b = a0 then
        Pile.afterRunRemoved (st.piles a0) (chop (st.piles a0).faceUp)
      else st.piles b) = st.piles b
    rw [ite_eq_right hb_ne]
  exact canRaise_of_raise_other hwf hstep hsu hd hpiles h

/-- **A raise cannot destroy a raisable card outside its own pile** — if
`d`'s suit is untouched and `c` is not in `d`'s pile, then `CanRaise st d`
becomes `CanRaise w d` after the raise of `c`.  This is the *forward* mirror
of `ValleyDrain.canRaise_of_raise_other`; the rank hypothesis removes the
pile condition automatically. -/
theorem canRaise_of_raise_high_fwd {st w : State} {c d : Card} {b : Anchor}
    (hwf : st.WF) (hstep : State.step st (Move.tabToFound c) = some w)
    (hsu : d.suit ≠ c.suit) (hdc : d ≠ c)
    (hrank : d.rank.toIdx ≤ c.rank.toIdx)
    (hd : st.pileHolding d = some b)
    (h : CanRaise st d) : CanRaise w d := by
  obtain ⟨hnext, a1, hpa1, hclause⟩ := h
  obtain ⟨-, a0, hpa0, hs⟩ := step_tabToFound_inv hstep
  -- `a1` and `b` are the same pile
  have htop1 : (st.piles a1).top = some d := (pileOfTop_eq_some_iff hwf).mp hpa1
  have hmem1 : d ∈ (st.piles a1).faceUp := Pile.mem_of_top htop1
  have hmem_b : d ∈ (st.piles b).faceUp := pileHolding_mem hd
  have ha1 : a1 = b := by
    by_cases hne : a1 = b
    · exact hne
    · exfalso
      exact ((mem_faceUp_unique hwf hmem1 b (Ne.symm hne)).1) hmem_b
  -- `c` is not in `d`'s pile (rank argument)
  have hb_ne : b ≠ a0 := by
    intro hba
    have htop_c : (st.piles a0).top = some c := (pileOfTop_eq_some_iff hwf).mp hpa0
    have hlast : lastOf (st.piles a0).faceUp = some c := htop_c
    have hface : (st.piles a0).faceUp = chop (st.piles a0).faceUp ++ [c] :=
      lastOf_chop hlast
    have hdmem : d ∈ (st.piles a0).faceUp := by
      rw [← hba]
      exact pileHolding_mem hd
    have hdchop : d ∈ chop (st.piles a0).faceUp := by
      rw [hface] at hdmem
      rcases List.mem_append.mp hdmem with h' | h'
      · exact h'
      · exact absurd (List.mem_singleton.mp h') hdc
    have hok : runOK (chop (st.piles a0).faceUp ++ [c]) = true := by
      rw [← hface]
      exact hwf.2.1 a0
    have hlt : c.rank.toIdx < d.rank.toIdx :=
      runOK_desc hok hdchop (List.mem_singleton_self c)
    omega
  -- foundations of `d`'s suit are untouched
  have hfound : w.found d.suit = st.found d.suit := by
    rw [hs]
    exact setFound_found_ne hsu
  have hnext_w : w.nextUp d = true := by
    have h1 : d.rank.toIdx = (st.found d.suit).length := by
      simpa [State.nextUp, State.foundHeight] using of_decide_eq_true hnext
    unfold State.nextUp State.foundHeight
    rw [hfound]
    exact decide_eq_true h1
  have hpiles : w.piles b = st.piles b := by
    rw [hs]
    show (if b = a0 then
        Pile.afterRunRemoved (st.piles a0) (chop (st.piles a0).faceUp)
      else st.piles b) = st.piles b
    rw [ite_eq_right hb_ne]
  -- the seat clause survives
  have htop_st_b : (st.piles b).top = some d := by
    rw [← ha1]
    exact htop1
  have hwfw : w.WF := step_wf hwf hstep
  have htop_w : (w.piles b).top = some d := by rw [hpiles]; exact htop_st_b
  have hpile_w : w.pileOfTop d = some b := (pileOfTop_eq_some_iff hwfw).mpr htop_w
  have hclause_b : chop (st.piles b).faceUp ≠ [] ∨
      ((st.piles b).hidden = [] ∧ d.rank = Rank.king) := by
    simpa [ha1] using hclause
  refine ⟨hnext_w, b, hpile_w, ?_⟩
  rcases hclause_b with hchop | ⟨hhid, hking⟩
  · left
    rw [hpiles]
    exact hchop
  · right
    refine ⟨?_, hking⟩
    rw [hpiles]
    exact hhid

/-! ## §6. TARGET 2 — the invariant's vanilla half is stable -/

/-- **TARGET 2.**  Raising a non-twin raisable card `c` reversibly keeps
`CanRaise x` and `¬ CanRaise x.twin`.  The S-live conjunct of the invariant
is the named hypothesis `CanRaiseS_preserved` (the ONE explicit transport
input), not proved here.

`x` is unchanged by construction: the statement is at the same `x`. -/
theorem raise_step_preserves {st st' : State} {x c : Card}
    (hwf : st.WF)
    (h : DrainInvariant st x) (hc : CanRaise st c)
    (hx : c ≠ x) (hxt : c ≠ x.twin)
    (hrev : reversibleAtW st (Move.tabToFound c))
    (hstep : State.step st (Move.tabToFound c) = some st')
    (CanRaiseS_preserved : CanRaiseS st' x.twin) :
    CanRaise st' x ∧ CanRaiseS st' x.twin ∧ ¬ CanRaise st' x.twin := by
  -- the rank floor applies to the raised card
  have hrank_x : x.rank.toIdx ≤ c.rank.toIdx :=
    h.2.2.2 c (CanRaiseS.now c hc)
  have hrank_t : x.twin.rank.toIdx ≤ c.rank.toIdx := by
    rw [Card.twin_rank]
    exact hrank_x
  -- the raised card's suit differs from both twins' suits
  have hsu_x : x.suit ≠ c.suit :=
    suit_ne_of_nextUp h.1.1 hc.1 (Ne.symm hx)
  have hsu_t : x.twin.suit ≠ c.suit :=
    suit_ne_of_nextUp (nextUp_of_canRaiseS h.2.1) hc.1 (Ne.symm hxt)
  -- the twins' holding piles
  have hhold_x : ∃ b, st.pileHolding x = some b := by
    obtain ⟨-, a, hpa, -⟩ := h.1
    exact ⟨a, pileHolding_of_pileOfTop hwf hpa⟩
  obtain ⟨b, hhold_x⟩ := hhold_x
  obtain ⟨bt, hhold_t⟩ := pileHolding_of_canRaiseS hwf h.2.1
  refine ⟨?_, CanRaiseS_preserved, ?_⟩
  · exact canRaise_of_raise_high_fwd hwf hstep hsu_x (Ne.symm hx) hrank_x hhold_x h.1
  · intro hw
    exact h.2.2.1 (canRaise_of_raise_high hwf hstep hsu_t hhold_t hrank_t hw)

/-- **TARGET 2, invariant rebuild.**  With the rank floor transported
(`hdeg`), the pair above reassembles `DrainInvariant st' x`. -/
theorem raise_step_preserves_invariant {st st' : State} {x c : Card}
    (hwf : st.WF)
    (h : DrainInvariant st x) (hc : CanRaise st c)
    (hx : c ≠ x) (hxt : c ≠ x.twin)
    (hrev : reversibleAtW st (Move.tabToFound c))
    (hstep : State.step st (Move.tabToFound c) = some st')
    (CanRaiseS_preserved : CanRaiseS st' x.twin)
    (hdeg : ∀ d, CanRaiseS st' d → x.rank.toIdx ≤ d.rank.toIdx) :
    DrainInvariant st' x := by
  obtain ⟨h1, h2, h3⟩ :=
    raise_step_preserves hwf h hc hx hxt hrev hstep CanRaiseS_preserved
  exact ⟨h1, h2, h3, hdeg⟩

/-! ## §7. TARGET 3 — the raise stays in the class -/

/-- **TARGET 3.**  A fired reversible letter keeps the state in its
`sameOrbitSetoid` class: the singleton walk is a witness shuffle, and
`shufflePlayW_revEqW` upgrades it to `RevEqW` both ways. -/
theorem sameOrbit_of_step {st st' : State} {m : Move}
    (hrev : reversibleAtW st m) (hstep : State.step st m = some st') :
    sameOrbitSetoid.r st st' := by
  have hwalk : ShufflePlayW st [m] st' := Walk.cons hrev hstep (Walk.nil st')
  exact RevEqW_symm (shufflePlayW_revEqW hwalk)

/-- **TARGET 3, raise form.** -/
theorem sameOrbit_of_raise {st st' : State} {c : Card}
    (hrev : reversibleAtW st (Move.tabToFound c))
    (hstep : State.step st (Move.tabToFound c) = some st') :
    sameOrbitSetoid.r st st' :=
  sameOrbit_of_step hrev hstep

/-! ## §8. TARGET 4 — the well-founded induction -/

/-- **TARGET 4.**  The abstract drain-to-fork engine.  `measure` is any
`State → Nat`; `hstep` is the mission's step provider; `hdec` is the
decidability of the terminal predicate at invariant states (a constructivity
device — at `WF` supplied by `drainTerminal_decidable`, no `Classical`). -/
theorem drain_to_fork {measure : State → Nat} {st : State} {x : Card}
    (h : DrainInvariant st x)
    (hdec : ∀ u, DrainInvariant u x → Decidable (DrainTerminal u x))
    (hstep : ∀ u, DrainInvariant u x → ¬ DrainTerminal u x →
        ∃ u', sameOrbitSetoid.r u u' ∧ DrainInvariant u' x ∧
          measure u' < measure u) :
    ∃ F, sameOrbitSetoid.r st F ∧ forkState F := by
  have key : ∀ n, ∀ u, measure u = n → DrainInvariant u x →
      ∃ F, sameOrbitSetoid.r u F ∧ forkState F := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro u hmeas hu
        cases hdec u hu with
        | isTrue hterm =>
            exact ⟨u, sameOrbitSetoid.iseqv.refl u,
              forkState_of_forkWitness (drain_terminal_fork hterm)⟩
        | isFalse hnt =>
            obtain ⟨u', hru', hu', hlt⟩ := hstep u hu hnt
            obtain ⟨F, hrF, hfork⟩ := ih (measure u') (by omega) u' rfl hu'
            exact ⟨F, sameOrbitSetoid.iseqv.trans hru' hrF, hfork⟩
  exact key (measure st) st rfl h

/-! ## §9. The rank-sum termination measure -/

/-- The rank sum: the sum of the four foundation rungs. -/
def rungSum (st : State) : Nat :=
  (Suit.all.map (fun s => rungAt st s)).sum

theorem suit_all_nodup : (Suit.all : List Suit).Nodup := by decide

/-- Summing a nodup list with one entry bumped by one raises the sum by one. -/
theorem sum_map_ite_bump (l : List Suit) (f : Suit → Nat) (a : Suit)
    (hnd : l.Nodup) (ha : a ∈ l) :
    (l.map (fun s => if s = a then f s + 1 else f s)).sum = (l.map f).sum + 1 := by
  induction l with
  | nil => cases ha
  | cons y t ih =>
      have hnd' : t.Nodup := (List.nodup_cons.mp hnd).2
      have hyt : y ∉ t := (List.nodup_cons.mp hnd).1
      by_cases hya : y = a
      · subst y
        have hmap : (t.map (fun s => if s = a then f s + 1 else f s)) = t.map f := by
          apply List.map_congr_left
          intro s hs
          rw [ite_eq_right (fun h : s = a => hyt (h ▸ hs))]
        rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, hmap,
          ite_eq_left rfl]
        omega
      · have ha' : a ∈ t := by
          rcases List.mem_cons.mp ha with h | h
          · exact absurd h.symm hya
          · exact h
        have hmap := ih hnd' ha'
        rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
          ite_eq_right hya, hmap]
        omega

/-- **A raise climbs the rank sum by exactly one.** -/
theorem rungSum_tabToFound {u v : State} {c : Card}
    (hstep : State.step u (Move.tabToFound c) = some v) :
    rungSum v = rungSum u + 1 := by
  unfold rungSum
  have h : ∀ σ : Suit, rungAt v σ = if σ = c.suit then rungAt u σ + 1 else rungAt u σ :=
    fun σ => rungAt_tabToFound hstep σ
  calc (Suit.all.map (fun s => rungAt v s)).sum
      = (Suit.all.map (fun s => if s = c.suit then rungAt u s + 1 else rungAt u s)).sum := by
        congr 1
        apply List.map_congr_left
        intro s _
        exact h s
    _ = (Suit.all.map (fun s => rungAt u s)).sum + 1 :=
        sum_map_ite_bump Suit.all (fun s => rungAt u s) c.suit suit_all_nodup
          (Suit.mem_all c.suit)

/-- **The rank sum is bounded by the deck** — four rungs of at most 13. -/
theorem rungSum_le_52 {st : State} (hwf : st.WF) : rungSum st ≤ 52 := by
  have h1 := rungAt_le13 hwf Suit.spade
  have h2 := rungAt_le13 hwf Suit.heart
  have h3 := rungAt_le13 hwf Suit.diamond
  have h4 := rungAt_le13 hwf Suit.club
  unfold rungSum
  simp only [Suit.all, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    at h1 h2 h3 h4 ⊢
  omega

/-! ## §10. The census probe (constructive decidability of terminality) -/

/-- Constructive witness extraction from a `List.all` failure (the core
`List.all_eq_false` drags `Classical.choice`; this one does not). -/
theorem exists_of_all_false {α : Type} {l : List α} {p : α → Bool}
    (h : l.all p = false) : ∃ x, x ∈ l ∧ p x = false := by
  induction l with
  | nil => simp at h
  | cons y t ih =>
      cases hp : p y with
      | false => exact ⟨y, List.mem_cons_self, hp⟩
      | true =>
          simp only [List.all_cons, hp, Bool.true_and] at h
          obtain ⟨x, hx, hpx⟩ := ih h
          exact ⟨x, List.mem_cons_of_mem y hx, hpx⟩

/-- The live-census Bool read: no live card outside the twin pair. -/
def drainLiveB (st : State) (x : Card) : Bool :=
  Card.universe.all (fun c =>
    !(canRaiseSB st c) || decide (c = x) || decide (c = x.twin))

/-- **The census agrees with the terminal live-set clause** (at `WF`). -/
theorem drainLiveB_iff {st : State} (hwf : st.WF) (x : Card) :
    drainLiveB st x = true ↔ ∀ c, CanRaiseS st c → c = x ∨ c = x.twin := by
  unfold drainLiveB
  rw [List.all_eq_true]
  constructor
  · rintro h c hc
    have hb := h c (Card.mem_universe c)
    have hprobe : canRaiseSB st c = true := (canRaiseSB_iff hwf).mpr hc
    rw [hprobe] at hb
    simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at hb
    rcases hb with h' | h'
    · exact Or.inl (of_decide_eq_true h')
    · exact Or.inr (of_decide_eq_true h')
  · intro h c _
    cases hb : canRaiseSB st c with
    | false => simp
    | true =>
        have hS : CanRaiseS st c := (canRaiseSB_iff hwf).mp hb
        rcases h c hS with hcx | hcx
        · rw [hcx]; simp
        · rw [hcx]; simp

/-- **Constructive decidability of `DrainTerminal` at `WF`.**  The census
probe is a Bool, so the case split of the induction never touches
`Classical.choice`. -/
def drainTerminal_decidable {st : State} {x : Card}
    (hwf : st.WF) (h : DrainInvariant st x) : Decidable (DrainTerminal st x) :=
  decidable_of_iff (drainLiveB st x = true) ⟨
    fun hb => ⟨h, (drainLiveB_iff hwf x).mp hb⟩,
    fun ht => (drainLiveB_iff hwf x).mpr ht.2⟩

/-! ## §11. The raise transport inputs (the named unproved rows) -/

/-- **The raise-transport bundle.**  Its first field is the exact statement
required by TARGET 2: `CanRaiseS st' x.twin` survives the raise.  The other
two fields are the honest residues — the invariant's rank floor and the
"every other live card is drainable" clause.  The third one is the
third-blocked-card case: the raise may expose new S-live cards, which must
still be vanilla-raisable. -/
structure RaiseTransport (x : Card) : Prop where
  /-- THE EXACT `CanRaiseS` TRANSPORT STATEMENT: `x.twin` stays S-live. -/
  CanRaiseS_preserved :
    ∀ (u u' : State) (c : Card),
      u.WF → DrainInvariant u x → DrainRaisable u x →
      CanRaise u c → c ≠ x → c ≠ x.twin →
      reversibleAtW u (Move.tabToFound c) →
      State.step u (Move.tabToFound c) = some u' →
      CanRaiseS u' x.twin
  /-- The invariant's rank floor survives the raise. -/
  rank_preserved :
    ∀ (u u' : State) (c : Card),
      u.WF → DrainInvariant u x → DrainRaisable u x →
      CanRaise u c → c ≠ x → c ≠ x.twin →
      reversibleAtW u (Move.tabToFound c) →
      State.step u (Move.tabToFound c) = some u' →
      ∀ d, CanRaiseS u' d → x.rank.toIdx ≤ d.rank.toIdx
  /-- The raise-only carry-on condition survives the raise. -/
  raisable_preserved :
    ∀ (u u' : State) (c : Card),
      u.WF → DrainInvariant u x → DrainRaisable u x →
      CanRaise u c → c ≠ x → c ≠ x.twin →
      reversibleAtW u (Move.tabToFound c) →
      State.step u (Move.tabToFound c) = some u' →
      DrainRaisable u' x

/-! ## §12. TARGET 5 — the raise-only phase -/

/-- **TARGET 5, terminal endpoint.**  If every non-twin live card is
vanilla-raisable and every such raise is reversible and transports the
invariant (`RaiseTransport`, whose first field is `CanRaiseS_preserved`),
then the raise-only drain reaches a TERMINAL state in the class.

TERMINATION: the measure is `52 - rungSum`; each raise climbs `rungSum` by
exactly one (`rungSum_tabToFound`) and `rungSum ≤ 52` at `WF`
(`rungSum_le_52`), so the measure strictly decreases.  No `Classical.choice`:
the terminal split is the census Bool. -/
theorem drain_raise_phase_terminal {st : State} {x : Card}
    (hwf : st.WF) (h : DrainInvariant st x) (hra : DrainRaisable st x)
    (hcanrev : ∀ (u : State) (c : Card),
      u.WF → DrainInvariant u x → DrainRaisable u x →
      CanRaise u c → c ≠ x → c ≠ x.twin →
      reversibleAtW u (Move.tabToFound c))
    (htrans : RaiseTransport x) :
    ∃ T, sameOrbitSetoid.r st T ∧ DrainTerminal T x := by
  have key : ∀ n, ∀ u, u.WF → DrainInvariant u x → DrainRaisable u x →
      52 - rungSum u = n → ∃ T, sameOrbitSetoid.r u T ∧ DrainTerminal T x := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro u huwf hu hru hmeas
        cases hb : drainLiveB u x with
        | true =>
            have hterm : DrainTerminal u x :=
              ⟨hu, (drainLiveB_iff huwf x).mp hb⟩
            exact ⟨u, sameOrbitSetoid.iseqv.refl u, hterm⟩
        | false =>
            -- extract the offending live card from the census
            have hall : (Card.universe.all (fun c =>
                !(canRaiseSB u c) || decide (c = x) || decide (c = x.twin))) = false := hb
            obtain ⟨c, hcmem, hcfalse⟩ := exists_of_all_false hall
            rw [Bool.or_eq_false_iff, Bool.or_eq_false_iff] at hcfalse
            obtain ⟨⟨hnot, hdeq⟩, hteq⟩ := hcfalse
            have hprobe : canRaiseSB u c = true := by
              cases hpc : canRaiseSB u c with
              | true => rfl
              | false => rw [hpc] at hnot; simp at hnot
            have hcx : c ≠ x := of_decide_eq_false hdeq
            have hct : c ≠ x.twin := of_decide_eq_false hteq
            have hSc : CanRaiseS u c := (canRaiseSB_iff huwf).mp hprobe
            have hc : CanRaise u c := by
              rcases hru c hSc with h1 | h1 | h1
              · exact absurd h1 hcx
              · exact absurd h1 hct
              · exact h1
            have hrev := hcanrev u c huwf hu hru hc hcx hct
            obtain ⟨u', hplay, hstep, hrun⟩ := hrev
            have hrevex : reversibleAtW u (Move.tabToFound c) :=
              ⟨u', hplay, hstep, hrun⟩
            have hpres := htrans.CanRaiseS_preserved u u' c huwf hu hru hc hcx hct
              hrevex hstep
            have hdeg := htrans.rank_preserved u u' c huwf hu hru hc hcx hct
              hrevex hstep
            have hu'ra := htrans.raisable_preserved u u' c huwf hu hru hc hcx hct
              hrevex hstep
            have hu'inv : DrainInvariant u' x :=
              raise_step_preserves_invariant huwf hu hc hcx hct hrevex hstep hpres hdeg
            have hu'wf : u'.WF := step_wf huwf hstep
            have hsum : rungSum u' = rungSum u + 1 := rungSum_tabToFound hstep
            have hbound' : rungSum u + 1 ≤ 52 := by
              have := rungSum_le_52 hu'wf
              rwa [hsum] at this
            have hlt : 52 - rungSum u' < n := by
              rw [hsum, ← hmeas]
              omega
            obtain ⟨T, hrT, hT⟩ :=
              ih (52 - rungSum u') hlt u' hu'wf hu'inv hu'ra rfl
            exact ⟨T, sameOrbitSetoid.iseqv.trans (sameOrbit_of_raise hrevex hstep) hrT,
              hT⟩
  exact key (52 - rungSum st) st hwf h hra rfl

/-- **TARGET 5, fork endpoint.**  The terminal endpoint of the raise-only
phase is a fork in the class (target 1 applied at the endpoint). -/
theorem drain_raise_phase {st : State} {x : Card}
    (hwf : st.WF) (h : DrainInvariant st x) (hra : DrainRaisable st x)
    (hcanrev : ∀ (u : State) (c : Card),
      u.WF → DrainInvariant u x → DrainRaisable u x →
      CanRaise u c → c ≠ x → c ≠ x.twin →
      reversibleAtW u (Move.tabToFound c))
    (htrans : RaiseTransport x) :
    ∃ F, sameOrbitSetoid.r st F ∧ forkState F := by
  obtain ⟨T, hrT, hT⟩ :=
    drain_raise_phase_terminal hwf h hra hcanrev htrans
  exact ⟨T, hrT, forkState_of_forkWitness (drain_terminal_fork hT)⟩

/-! ## §13. Battery -/

#print axioms drain_terminal_fork
#print axioms drain_terminal_forkState
#print axioms pileHolding_of_pileOfTop
#print axioms pileHolding_of_canRaiseS
#print axioms nextUp_of_canRaiseS
#print axioms suit_ne_of_nextUp
#print axioms canRaise_of_raise_high_fwd
#print axioms raise_step_preserves
#print axioms raise_step_preserves_invariant
#print axioms sameOrbit_of_step
#print axioms sameOrbit_of_raise
#print axioms drain_to_fork
#print axioms sum_map_ite_bump
#print axioms rungSum_tabToFound
#print axioms rungSum_le_52
#print axioms drainLiveB_iff
#print axioms exists_of_all_false
#print drainTerminal_decidable
#print axioms drain_raise_phase_terminal
#print axioms drain_raise_phase

end Drain
