import Orig2.Fork.Class.ForkRaiseReorder
import Orig2.Fiber.FreeOrbit
import Orig2.Fiber.LockRung
import Orig2.Fork.Local.ForkCriticalPair

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Orig2.Fork.Class.ForkRaiseReorderKit — the rank-front toolkit

The infrastructure half of the port of the (proved) rank-front theorem into
`Orig2`.  The statement it serves is the card's `RankFront`
(`Orig2/Fork/Class/ForkRaiseReorder.lean`); the proof is in
`Orig2/Fork/Class/ForkRaiseReorderProof.lean`.

Contents, in order:

* the list bookkeeping of a raise's run removal (`chop` / `below` / `afterRunRemoved`);
* the landing state of `tabToFound` (piles, foundations, face-up membership,
  `Parented` / `Bare`);
* monotonicity of the readiness probe `freeCardS` along a raise;
* cargo slides preserve the reads (`RevEqW`, `sameOrbitSetoid`, `nextUp`) and
  foundations (`found_cargoLeg`, `found_cargoPath`, `parented_of_cargoPath`);
* `specShift_sem_fwd` — the forward licence shift;
* R1 (`canRaiseS_step_of_rank_ne`, `canRaiseS_persist_of_rank_ne`);
* R2 (`cover_rank_lt`, `above_rank_lt`, `above_rank_lt_of_pile`);
* the state-level cover lock (`no_canPlace_of_seated`, `twin_covered_persists`,
  `step_none_of_twin_covered`);
* sequence plumbing (`raiseStepS_of_canRaiseS`, `raiseSSeq_append`,
  `raiseSSeq_wf`, `exists_append_cons_of_mem`, `erase_append_cons_of_not_mem`);
* the licensed relation's accessors and adequacy
  (`RaiseSSeqLicensed.toSeq`, `.wf`, `.append`, `.step_s`, `.cargoPath`,
  `.canRaiseS_head`, `canRaise_of_canRaiseS_of_step`,
  `raiseSSeqLicensed_step_of_canRaiseS`), R1 at the licensed grade and
  `swap_of_licensed`;
* R3 at the play level (`cover_must_be_raised : CoverMustBeRaisedWord`).

No new `Prop` predicate is introduced: every theorem is stated in the repo's
standard terms (`CanRaise`, `CanRaiseS`, `reversibleAtW`, `CargoPath`,
`CargoLeg`, `ShufflePlayW`, `RevEqW`, `seatOf`, `runOK`, `List.Perm`).

House rules: no `sorry`, no `Classical`, no `noncomputable`.
-/

namespace OneColourClosure

/-! ## §1. List bookkeeping for the run removal -/

/-- `chop` never adds cards. -/
theorem mem_chop_of_mem_chop {l : List Card} {x : Card} (h : x ∈ chop l) : x ∈ l := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons y t ih =>
      cases t with
      | nil => simp [chop] at h
      | cons z zs =>
          rw [show chop (y :: z :: zs) = y :: chop (z :: zs) from rfl] at h
          rcases List.mem_cons.mp h with h' | h'
          · exact List.mem_cons.mpr (Or.inl h')
          · exact List.mem_cons.mpr (Or.inr (ih h'))

/-- A member other than the last element survives the chop. -/
theorem mem_chop_of_mem_of_ne_last : ∀ {l : List Card} {x c : Card},
    x ∈ l → lastOf l = some c → x ≠ c → x ∈ chop l
  | [], _, _, hmem, _, _ => absurd hmem List.not_mem_nil
  | [y], x, c, hmem, hlast, hx => by
      rw [List.mem_singleton] at hmem
      have hy : y = c := by simpa [lastOf] using hlast
      exact absurd (hmem.trans hy) hx
  | y :: z :: zs, x, c, hmem, hlast, hx => by
      rw [show chop (y :: z :: zs) = y :: chop (z :: zs) from rfl]
      rcases List.mem_cons.mp hmem with h' | h'
      · exact List.mem_cons.mpr (Or.inl h')
      · have hlast' : lastOf (z :: zs) = some c := by simpa [lastOf] using hlast
        exact List.mem_cons.mpr
          (Or.inr (mem_chop_of_mem_of_ne_last h' hlast' hx))

/-- For a member, `below` is blind to the (removed) last element. -/
theorem below_chop_of_mem_of_ne_last : ∀ {l : List Card} {x c : Card},
    x ∈ l → lastOf l = some c → x ≠ c → below x (chop l) = below x l
  | [], _, _, hmem, _, _ => absurd hmem List.not_mem_nil
  | [y], x, c, hmem, hlast, hx => by
      rw [List.mem_singleton] at hmem
      have hy : y = c := by simpa [lastOf] using hlast
      exact absurd (hmem.trans hy) hx
  | y :: z :: zs, x, c, hmem, hlast, hx => by
      rw [show chop (y :: z :: zs) = y :: chop (z :: zs) from rfl]
      have h1 : below x (y :: chop (z :: zs))
          = (if y = x then [] else y :: below x (chop (z :: zs))) :=
        below_cons x y _
      have h2 : below x (y :: z :: zs)
          = (if y = x then [] else y :: below x (z :: zs)) :=
        below_cons x y _
      rw [h1, h2]
      by_cases hyx : y = x
      · rw [ite_eq_left hyx, ite_eq_left hyx]
      · rw [ite_eq_right hyx, ite_eq_right hyx]
        have hmem' : x ∈ z :: zs := by
          rcases List.mem_cons.mp hmem with h' | h'
          · exact absurd h'.symm hyx
          · exact h'
        have hlast' : lastOf (z :: zs) = some c := by simpa [lastOf] using hlast
        rw [below_chop_of_mem_of_ne_last hmem' hlast' hx]

/-- A member other than the removed top survives the run removal. -/
theorem mem_afterRunRemoved_faceUp_of_mem_of_ne_last {p : Pile} {x c : Card}
    (hmem : x ∈ p.faceUp) (hlast : lastOf p.faceUp = some c) (hx : x ≠ c) :
    x ∈ (p.afterRunRemoved (chop p.faceUp)).faceUp := by
  have hchop : x ∈ chop p.faceUp := mem_chop_of_mem_of_ne_last hmem hlast hx
  have hne : chop p.faceUp ≠ [] := fun h => by
    rw [h] at hchop
    exact absurd hchop List.not_mem_nil
  rw [afterRunRemoved_faceUp_ne hne]
  exact hchop

/-- `afterRunRemoved` at the empty prefix over an empty hidden deck is bare. -/
theorem afterRunRemoved_faceUp_bare {p : Pile} (h : p.hidden = []) :
    (Pile.afterRunRemoved p ([] : List Card)).faceUp = [] := by
  rcases p with ⟨hd, fq⟩
  cases hd with
  | nil => rfl
  | cons x xs => exact absurd h (by simp)

/-- **The backwards read of the run removal** — a member whose `below`-part is
nonempty at the landing state was already face-up, with the same below-part,
before the removal.  (The `below`-nonemptiness excludes the hidden reveal.) -/
theorem mem_and_below_of_mem_afterRunRemoved {p : Pile} {x c : Card}
    (hlast : lastOf p.faceUp = some c) (hx : x ≠ c)
    (hmem : x ∈ (p.afterRunRemoved (chop p.faceUp)).faceUp)
    (hbel : below x (p.afterRunRemoved (chop p.faceUp)).faceUp ≠ []) :
    x ∈ p.faceUp ∧
      below x (p.afterRunRemoved (chop p.faceUp)).faceUp = below x p.faceUp := by
  by_cases hchop : chop p.faceUp = []
  · exfalso
    have hrev : p.afterRunRemoved (chop p.faceUp)
        = Pile.revealTop { p with faceUp := [] } := by
      rw [hchop]; rfl
    rw [hrev, revealTop_faceUp_empty] at hmem hbel
    cases hhid : p.hidden with
    | nil => rw [hhid] at hmem; simp at hmem
    | cons g gs =>
        rw [hhid] at hmem hbel
        simp only [List.mem_singleton] at hmem
        subst hmem
        exact hbel (by rw [below_cons]; simp)
  · have hshape : (p.afterRunRemoved (chop p.faceUp)).faceUp = chop p.faceUp := by
      rw [afterRunRemoved_faceUp_ne hchop]
    rw [hshape] at hmem hbel ⊢
    have hmemf : x ∈ p.faceUp := mem_chop_of_mem_chop hmem
    exact ⟨hmemf, below_chop_of_mem_of_ne_last hmemf hlast hx⟩

/-! ## §2. The landing state of a raise -/

/-- The pile map of a `tabToFound` landing. -/
theorem piles_tabToFound {z z' : State} {c : Card}
    (hstep : State.step z (Move.tabToFound c) = some z') :
    ∃ a0, z.pileOfTop c = some a0 ∧
      ∀ a, z'.piles a =
        (if a = a0 then
          Pile.afterRunRemoved (z.piles a0) (chop (z.piles a0).faceUp)
        else z.piles a) := by
  obtain ⟨-, a0, hpa0, hs⟩ := step_tabToFound_inv hstep
  refine ⟨a0, hpa0, fun a => ?_⟩
  rw [hs]

/-- The foundation map of a `tabToFound` landing. -/
theorem found_tabToFound {z z' : State} {c : Card}
    (hstep : State.step z (Move.tabToFound c) = some z') (σ : Suit) :
    z'.found σ = (if σ = c.suit then z.found σ ++ [c] else z.found σ) := by
  obtain ⟨-, a0, hpa0, hs⟩ := step_tabToFound_inv hstep
  rw [hs]
  show (if σ = c.suit then z.found c.suit ++ [c] else z.found σ)
      = (if σ = c.suit then z.found σ ++ [c] else z.found σ)
  by_cases h : σ = c.suit <;> simp [h]

/-- **Face-up membership survives a raise** for every card that is not the
raised one: the raise removes the pile *top*. -/
theorem mem_piles_tabToFound_of_mem_of_ne {z z' : State} {c x : Card} {a : Anchor}
    (hstep : State.step z (Move.tabToFound c) = some z')
    (hx : x ≠ c) (hmem : x ∈ (z.piles a).faceUp) :
    x ∈ (z'.piles a).faceUp := by
  obtain ⟨a0, hpa0, hpiles⟩ := piles_tabToFound hstep
  have hlast : lastOf (z.piles a0).faceUp = some c := (pileOfTop_top hpa0).2
  rw [hpiles a]
  by_cases ha : a = a0
  · subst a
    rw [ite_eq_left rfl]
    exact mem_afterRunRemoved_faceUp_of_mem_of_ne_last hmem hlast hx
  · rw [ite_eq_right ha]
    exact hmem

/-- **The raised card is off the tableau.** -/
theorem not_mem_piles_tabToFound_self {z z' : State} {c : Card}
    (hwf : z.WF) (hstep : State.step z (Move.tabToFound c) = some z') (a : Anchor) :
    c ∉ (z'.piles a).faceUp := by
  have hwf' : z'.WF := step_wf hwf hstep
  have hfound : c ∈ z'.found c.suit := by
    rw [found_tabToFound hstep c.suit]
    rw [ite_eq_left rfl]
    exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
  exact ((mem_found_unique hwf' hfound).1 a).2

/-- **`Parented` survives a raise** for a card that is not the raised one. -/
theorem parented_tabToFound_of_ne {z z' : State} {c x : Card}
    (hwf : z.WF) (hstep : State.step z (Move.tabToFound c) = some z')
    (hx : x ≠ c) (hp : Parented z x) : Parented z' x := by
  obtain ⟨w, hse⟩ := hp
  obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hse
  have hmem : x ∈ (z.piles a).faceUp := pileHolding_mem hhold
  have hmem' : x ∈ (z'.piles a).faceUp :=
    mem_piles_tabToFound_of_mem_of_ne hstep hx hmem
  have hhold' : z'.pileHolding x = some a :=
    (pileHolding_eq_some_iff (step_wf hwf hstep)).2 hmem'
  have hlast' : lastOf (below x (z'.piles a).faceUp) = some w := by
    obtain ⟨a0, hpa0, hpiles⟩ := piles_tabToFound hstep
    have hlastf : lastOf (z.piles a0).faceUp = some c := (pileOfTop_top hpa0).2
    rw [hpiles a]
    by_cases ha : a = a0
    · subst a
      rw [ite_eq_left rfl]
      have hchopmem : x ∈ chop (z.piles a0).faceUp :=
        mem_chop_of_mem_of_ne_last hmem hlastf hx
      have hne : chop (z.piles a0).faceUp ≠ [] := fun h => by
        rw [h] at hchopmem
        exact absurd hchopmem List.not_mem_nil
      rw [afterRunRemoved_faceUp_ne hne]
      rw [below_chop_of_mem_of_ne_last hmem hlastf hx]
      exact hlast
    · rw [ite_eq_right ha]
      exact hlast
  refine ⟨w, ?_⟩
  rw [tfc_seatOf_pair hhold', tfc_getLast?_lastOf, hlast']

/-- **`Bare` survives a raise** for a card that is not the raised one. -/
theorem bare_tabToFound_of_ne {z z' : State} {c x : Card}
    (hwf : z.WF) (hstep : State.step z (Move.tabToFound c) = some z')
    (hx : x ≠ c) (hb : Bare z x) : Bare z' x := by
  obtain ⟨a, hhold, hhid⟩ := hb
  have hmem : x ∈ (z.piles a).faceUp := pileHolding_mem hhold
  have hmem' : x ∈ (z'.piles a).faceUp :=
    mem_piles_tabToFound_of_mem_of_ne hstep hx hmem
  refine ⟨a, (pileHolding_eq_some_iff (step_wf hwf hstep)).2 hmem', ?_⟩
  obtain ⟨a0, hpa0, hpiles⟩ := piles_tabToFound hstep
  have hlastf : lastOf (z.piles a0).faceUp = some c := (pileOfTop_top hpa0).2
  rw [hpiles a]
  by_cases ha : a = a0
  · subst a
    rw [ite_eq_left rfl]
    have hchopmem : x ∈ chop (z.piles a0).faceUp :=
      mem_chop_of_mem_of_ne_last hmem hlastf hx
    have hne : chop (z.piles a0).faceUp ≠ [] := fun h => by
      rw [h] at hchopmem
      exact absurd hchopmem List.not_mem_nil
    rcases afterRunRemoved_hidden (z.piles a0) (chop (z.piles a0).faceUp) with
      ⟨-, hh⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [hh, hhid]
    · exact absurd h1 hne
    · exact absurd h1 hne
  · rw [ite_eq_right ha]
    exact hhid

/-- **`Parented` is antitone along a raise** — a card that is parented after
the raise was already parented before it.  (Only the raised card can lose its
seat; the hidden reveal cannot produce a parented card.) -/
theorem parented_of_tabToFound {z z' : State} {c x : Card}
    (hwf : z.WF) (hstep : State.step z (Move.tabToFound c) = some z')
    (hp : Parented z' x) : Parented z x := by
  have hwf' : z'.WF := step_wf hwf hstep
  obtain ⟨w, hse⟩ := hp
  obtain ⟨a, hhold', hbel', hlast'⟩ := tfc_seatOf_of_inr hse
  have hmem' : x ∈ (z'.piles a).faceUp := pileHolding_mem hhold'
  have hxc : x ≠ c := by
    intro hxc0
    subst hxc0
    exact (not_mem_piles_tabToFound_self hwf hstep a) hmem'
  obtain ⟨a0, hpa0, hpiles⟩ := piles_tabToFound hstep
  have hlastf : lastOf (z.piles a0).faceUp = some c := (pileOfTop_top hpa0).2
  have hback : x ∈ (z.piles a).faceUp ∧
      below x (z'.piles a).faceUp = below x (z.piles a).faceUp := by
    rw [hpiles a] at hmem' hbel' ⊢
    by_cases ha : a = a0
    · subst a
      rw [ite_eq_left rfl] at hmem' hbel' ⊢
      exact mem_and_below_of_mem_afterRunRemoved hlastf hxc hmem' hbel'
    · rw [ite_eq_right ha] at hmem' hbel' ⊢
      exact ⟨hmem', rfl⟩
  obtain ⟨hmem, hbeq⟩ := hback
  have hhold : z.pileHolding x = some a := (pileHolding_eq_some_iff hwf).2 hmem
  have hlast : lastOf (below x (z.piles a).faceUp) = some w := by
    rw [← hbeq]
    exact hlast'
  refine ⟨w, ?_⟩
  rw [tfc_seatOf_pair hhold, tfc_getLast?_lastOf, hlast]

/-! ## §3. The readiness probe is monotone along a raise -/

/-- **`freeCardS` is monotone along a raise** for every card except the raised
one and its twin.  This is the semantic re-derivation of the triple at the
landing state. -/
theorem freeCardS_mono_of_ne_twin {z z' : State} {c d : Card}
    (hstep : State.step z (Move.tabToFound c) = some z')
    (hz : z.WF) (hd : d ≠ c) (hdt : d ≠ c.twin) :
    freeCardS z d = true → freeCardS z' d = true := by
  intro hfree
  have hwf' : z'.WF := step_wf hz hstep
  rw [freeCardS_sem hz] at hfree
  obtain ⟨a, hhold, hseat, hhatch⟩ := hfree
  rw [freeCardS_sem hwf']
  have hmem : d ∈ (z.piles a).faceUp := pileHolding_mem hhold
  have hmem' : d ∈ (z'.piles a).faceUp :=
    mem_piles_tabToFound_of_mem_of_ne hstep hd hmem
  have hhold' : z'.pileHolding d = some a := (pileHolding_eq_some_iff hwf').2 hmem'
  have hdtc : d.twin ≠ c := fun h =>
    hdt (by have h2 := congrArg Card.twin h; simpa [card_twin_twin] using h2)
  refine ⟨a, hhold', ?_, ?_⟩
  · rcases hseat with ⟨hp, hk⟩ | ⟨hb, hk⟩
    · exact Or.inl ⟨parented_tabToFound_of_ne hz hstep hd hp, hk⟩
    · exact Or.inr ⟨bare_tabToFound_of_ne hz hstep hd hb, hk⟩
  · intro e he
    rcases hhatch e he with ⟨hne, hnet⟩ | ⟨hwit, hnen⟩
    · exact Or.inl
        ⟨fun hp => hne (parented_of_tabToFound hz hstep hp),
          fun hp => hnet (parented_of_tabToFound hz hstep hp)⟩
    · obtain ⟨a', ha'⟩ := hwit
      exact Or.inr
        ⟨⟨a', mem_piles_tabToFound_of_mem_of_ne hstep hdtc ha'⟩,
          fun ⟨hp, hpt⟩ => hnen
            ⟨parented_of_tabToFound hz hstep hp,
              parented_of_tabToFound hz hstep hpt⟩⟩

/-! ## §4. Slides preserve the reads -/

/-- A cargo path is a witness shuffle (each cargo leg is reversible). -/
theorem revEqW_of_cargoPath {a b : State} (h : CargoPath a b) : RevEqW a b := by
  have hex : ∃ play, ShufflePlayW a play b := by
    induction h with
    | refl s => exact ⟨[], Walk.nil s⟩
    | cons hleg hrest ih =>
        obtain ⟨c, base, hfire, hrev⟩ := hleg
        obtain ⟨play, hplay⟩ := ih
        exact ⟨Move.tabToTab c base :: play, Walk.cons hrev hfire hplay⟩
  obtain ⟨play, hplay⟩ := hex
  exact shufflePlayW_revEqW hplay

/-- A cargo path is an orbit move. -/
theorem sameOrbit_of_cargoPath {a b : State} (h : CargoPath a b) :
    sameOrbitSetoid.r a b :=
  RevEqW_symm (revEqW_of_cargoPath h)

/-- Rungs — hence `nextUp` — are cargo-path invariant. -/
theorem nextUp_cargoPath {a b : State} (h : CargoPath a b) (x : Card) :
    b.nextUp x = a.nextUp x := by
  have hr := rungAt_cargoPath h x.suit
  simp only [rungAt] at hr
  simp only [State.nextUp, State.foundHeight, hr]
  rfl

/-- Foundations are cargo-leg invariant. -/
theorem found_cargoLeg {a b : State} (h : CargoLeg a b) : b.found = a.found := by
  obtain ⟨c, bb, hstep, -⟩ := h
  obtain ⟨a₀, -, -, -, hv⟩ := step_tabToTab_inv hstep
  rw [hv, putRun_found, setPile_found]

/-- Foundations are cargo-path invariant. -/
theorem found_cargoPath {a b : State} (h : CargoPath a b) : b.found = a.found := by
  induction h with
  | refl => rfl
  | cons hleg _ ih => rw [ih, found_cargoLeg hleg]

/-- `Parented` is cargo-path invariant. -/
theorem parented_of_cargoPath {a b : State} (hwf : a.WF) (h : CargoPath a b)
    {x : Card} (hk : x.rank ≠ Rank.king) (hp : Parented a x) : Parented b x :=
  (parented_orbit_rung hwf (sameOrbit_of_cargoPath h) (fun σ => rungAt_cargoPath h σ)
    hk).mp hp

/-! ## §5. `SpecShift`, forward direction -/

/-- **`SpecShift` — the forward direction.**  Raising `c` (via any cargo slide
plus the raise) preserves every other card's S-readiness, except possibly its
twin's.  The `nextUp` half is `nextUp_raise_ne`; the readiness half is
`freeCardS_mono_of_ne_twin` transported along the slide by
`freeCardS_orbit_rung`. -/
theorem specShift_sem_fwd {z z' : State} {c d : Card}
    (hz : z.WF) (hstep : RaiseStepS z z' c) (hd : d ≠ c) (hdt : d ≠ c.twin) :
    CanRaiseS z d → CanRaiseS z' d := by
  intro hS
  obtain ⟨z₀, hpath, hstep₀⟩ := hstep
  have hz₀ : z₀.WF := cargoPath_wf hz hpath
  have hz' : z'.WF := step_wf hz₀ hstep₀
  rw [canRaiseS_split hz] at hS
  obtain ⟨hnext, hfree⟩ := hS
  rw [canRaiseS_split hz']
  -- the readiness transport
  have hfree₀ : freeCardS z₀ d = true :=
    (freeCardS_orbit_rung hz (sameOrbit_of_cargoPath hpath)
      (rungAt_cargoPath hpath) (c := d)).mp hfree
  have hfree' : freeCardS z' d = true :=
    freeCardS_mono_of_ne_twin hstep₀ hz₀ hd hdt hfree₀
  -- the raised card's suit differs from `d`'s (else `d = c`)
  have hsu : d.suit ≠ c.suit := by
    intro hs
    have hnextc : z₀.nextUp c = true := (step_tabToFound_inv hstep₀).1
    have hdrank : d.rank.toIdx = rungAt z d.suit := by
      simpa [State.nextUp, State.foundHeight, rungAt] using of_decide_eq_true hnext
    have hcrank : c.rank.toIdx = rungAt z c.suit := by
      have h1 : c.rank.toIdx = rungAt z₀ c.suit := by
        simpa [State.nextUp, State.foundHeight, rungAt] using of_decide_eq_true hnextc
      rw [← rungAt_cargoPath hpath c.suit] at h1
      exact h1
    have hrank : d.rank.toIdx = c.rank.toIdx := by
      rw [hdrank, hcrank, hs]
    exact hd (card_eq_of_suit_rank hs hrank)
  have hnext' : z'.nextUp d = true := by
    rw [nextUp_raise_ne hstep₀ hsu, nextUp_cargoPath hpath d]
    exact hnext
  exact ⟨hnext', hfree'⟩

/-! ## §6. R1 — licence propagation across a strictly different rank -/

/-- A `CanRaiseS` licence fires a `RaiseStepS`. -/
theorem raiseStepS_of_canRaiseS {z : State} {c : Card} (h : CanRaiseS z c) :
    ∃ z', RaiseStepS z z' c := by
  obtain ⟨z₀, hp, hcr⟩ := h
  obtain ⟨z', hs⟩ := step_tabToFound_of_canRaise hcr
  exact ⟨z', z₀, hp, hs⟩

/-- Append one raise to a raiseS sequence. -/
theorem raiseSSeq_snoc {s z : State} {ws : List Card} {c : Card}
    (h : RaiseSSeq s ws z) (hz : ∃ z', RaiseStepS z z' c) :
    ∃ z', RaiseSSeq s (c :: ws) z' := by
  obtain ⟨z', z₀, hp, hs⟩ := hz
  exact ⟨z', RaiseSSeq.cons h hp hs⟩

/-- Sequence composition (`w₁` first, then `w₂`, gives the word `w₂ ++ w₁`). -/
theorem raiseSSeq_append {s u v : State} {w₁ w₂ : List Card}
    (h₁ : RaiseSSeq s w₁ u) (h₂ : RaiseSSeq u w₂ v) :
    RaiseSSeq s (w₂ ++ w₁) v := by
  induction h₂ generalizing s with
  | nil => exact h₁
  | cons _ hp hs ih =>
      rw [List.cons_append]
      exact RaiseSSeq.cons (ih h₁) hp hs

/-- A raiseS word transports well-formedness. -/
theorem raiseSSeq_wf {s z : State} {ws : List Card} (h : RaiseSSeq s ws z)
    (hwf : s.WF) : z.WF := by
  revert hwf
  induction h with
  | nil => exact id
  | cons _ hp hs ih => exact fun hwf => step_wf (cargoPath_wf (ih hwf) hp) hs

/-- A `RaiseStepS` lands well-formed. -/
theorem raiseStepS_wf {z z' : State} {c : Card} (hz : z.WF) (h : RaiseStepS z z' c) :
    z'.WF := by
  obtain ⟨z₀, hp, hs⟩ := h
  exact step_wf (cargoPath_wf hz hp) hs

/-- **R1, one step.**  Raising a card of different rank preserves `c`'s licence;
both `specShift_sem_fwd` side conditions are automatic by rank. -/
theorem canRaiseS_step_of_rank_ne {z z' : State} {d c : Card}
    (hz : z.WF) (hstep : RaiseStepS z z' d) (hr : d.rank ≠ c.rank) :
    CanRaiseS z c → CanRaiseS z' c := by
  intro hc
  refine specShift_sem_fwd hz hstep ?_ ?_ hc
  · intro h; exact hr (by rw [h])
  · intro h; exact hr (by rw [h, Card.twin_rank])

/-- **R1, a word.**  If every raised card has rank different from `c`'s, `c`'s
licence survives the whole sequence. -/
theorem canRaiseS_persist_of_rank_ne {s z : State} {ws : List Card} {c : Card}
    (h : RaiseSSeq s ws z) (hwf : s.WF)
    (hr : ∀ d ∈ ws, d.rank ≠ c.rank) (hc : CanRaiseS s c) :
    CanRaiseS z c := by
  revert hwf hr hc
  induction h with
  | nil => intro _ _ hc; exact hc
  | cons htail hp hs ih =>
      rename_i zz zz0 zz' cc wws
      intro hwf hr hc
      have hr' : ∀ d ∈ wws, d.rank ≠ c.rank :=
        fun d hd => hr d (List.mem_cons_of_mem _ hd)
      have hcc : cc.rank ≠ c.rank := hr cc (List.mem_cons_self ..)
      have hzwf : zz.WF := raiseSSeq_wf htail hwf
      have hz : CanRaiseS zz c := ih hwf hr' hc
      exact canRaiseS_step_of_rank_ne hzwf ⟨zz0, hp, hs⟩ hcc hz

/-! ## §7. R2 — a card above another in a pile has strictly lower rank -/

/-- A card that may sit on `y` is strictly lower-ranked than `y`. -/
theorem cover_rank_lt {x y : Card} (h : canSitOn x y = true) :
    x.rank.toIdx < y.rank.toIdx := by
  have := ((canSitOn_eq x y).mp h).1
  omega

/-- A card that may sit on `y` has strictly different rank from `y`. -/
theorem cover_rank_ne {x y : Card} (h : canSitOn x y = true) : x.rank ≠ y.rank := by
  intro hcon
  have := cover_rank_lt h
  rw [hcon] at this
  omega

/-- **The R2 primitive.**  In a legal face-up run, a card that appears *after*
`y` (i.e. above `y`) has strictly lower rank than `y`. -/
theorem above_rank_lt {l : List Card} (h : runOK l = true) :
    ∀ (B : List Card) (A : List Card) (y x : Card),
      l = A ++ y :: B → x ∈ B → x.rank.toIdx < y.rank.toIdx := by
  intro B
  induction B with
  | nil => intro A y x _ hx; exact absurd hx List.not_mem_nil
  | cons z B' ih =>
      intro A y x hl hx
      have hzy : canSitOn z y = true :=
        SeedKit.runOK_adjacent_fit y z A B' (by rw [← hl]; exact h)
      have hzlt : z.rank.toIdx < y.rank.toIdx := cover_rank_lt hzy
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hzlt
      · have hl' : l = (A ++ [y]) ++ z :: B' := by rw [hl]; simp [List.append_assoc]
        have := ih (A ++ [y]) z x hl' hx'
        omega

/-- The same fact read on a pile. -/
theorem above_rank_lt_of_pile {st : State} (hwf : st.WF) {a : Anchor} {y x : Card}
    {A B : List Card} (hl : (st.piles a).faceUp = A ++ y :: B) (hx : x ∈ B) :
    x.rank.toIdx < y.rank.toIdx :=
  above_rank_lt (hwf.2.1 a) B A y x hl hx

/-! ## §8. The state-level cover lock -/

/-- **`x` cannot be placed anywhere** while it sits on `t` and `t.twin` is
founded: its only two seats are `t` (not a pile top — `x` is on it) and
`t.twin` (founded, hence not a pile top). -/
theorem no_canPlace_of_seated {w : State} (hwf : w.WF) {x t : Card}
    (hseat : seatOf w x = some (Sum.inr t))
    (hfound : t.twin ∈ w.found t.twin.suit) :
    ∀ b : Base, w.canPlace x b = false := by
  intro b
  obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hseat
  have hfit : canSitOn x t = true := (tfc_seat_parent hwf hhold hlast).1
  have hxking : x.rank ≠ Rank.king := tfc_seatOf_inr_rank_ne_king hwf hseat
  cases b with
  | inl a' => simp [State.canPlace, hxking]
  | inr y =>
      cases hpt : w.pileOfTop y with
      | none => simp [State.canPlace, hpt]
      | some k =>
          have hnots : canSitOn x y = false := by
            by_cases hxy : canSitOn x y = true
            · rcases cover_seats_cases hfit hxy with h | h
              · rw [h] at hpt
                exact absurd hpt (by rw [no_top_of_seat hwf hseat]; simp)
              · rw [h] at hpt
                exact absurd hpt (by rw [pileOfTop_eq_none_of_found hwf hfound]; simp)
            · cases hcan : canSitOn x y with
              | false => rfl
              | true => exact absurd hcan hxy
          simp only [State.canPlace, hpt]
          exact hnots

/-- **R3, transportation**: across a whole cargo path, the cover `x` stays on
`t`, so `t` is never a pile top. -/
theorem twin_covered_persists {w v : State} (hwf : w.WF) {x t : Card}
    (hseat : seatOf w x = some (Sum.inr t))
    (hfound : t.twin ∈ w.found t.twin.suit)
    (hpath : CargoPath w v) : v.pileOfTop t = none := by
  have hwv : v.WF := cargoPath_wf hwf hpath
  have hxking : x.rank ≠ Rank.king := tfc_seatOf_inr_rank_ne_king hwf hseat
  have hparv : Parented v x :=
    parented_of_cargoPath hwf hpath hxking ⟨t, hseat⟩
  obtain ⟨z, hz⟩ := hparv
  obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hseat
  have hfit : canSitOn x t = true := (tfc_seat_parent hwf hhold hlast).1
  obtain ⟨a', hhold', -, hlast'⟩ := tfc_seatOf_of_inr hz
  have hfitz : canSitOn x z = true := (tfc_seat_parent hwv hhold' hlast').1
  have hfund : t.twin ∈ v.found t.twin.suit := by
    rw [found_cargoPath hpath]; exact hfound
  rcases cover_seats_cases hfit hfitz with h | h
  · rw [h] at hz
    exact no_top_of_seat hwv hz
  · exfalso
    rw [h] at hlast'
    have hmem : t.twin ∈ (v.piles a').faceUp := mem_below _ (lastOf_mem hlast')
    exact ((mem_found_unique hwv hfund).1 a').2 hmem

/-- **R3, final form for one state**: if the cover `x` of `t` is present and
`t.twin` is founded, then `t` cannot be raised from any cargo mate — the cover
can only be removed by *raising* it. -/
theorem step_none_of_twin_covered {w v : State} (hwf : w.WF) {x t : Card}
    (hseat : seatOf w x = some (Sum.inr t))
    (hfound : t.twin ∈ w.found t.twin.suit)
    (hpath : CargoPath w v) :
    State.step v (Move.tabToFound t) = none := by
  have htop : v.pileOfTop t = none := twin_covered_persists hwf hseat hfound hpath
  rw [step_tabToFound_eq]
  by_cases hnext : v.nextUp t = true
  · rw [if_pos hnext, htop]
  · rw [if_neg hnext]

/-! ## §9. A word splits at its first occurrence of a card -/

/-- Splitting a word at its first occurrence of `c`. -/
theorem exists_append_cons_of_mem : ∀ {l : List Card} {c : Card}, c ∈ l →
    ∃ A B, l = A ++ c :: B ∧ c ∉ A := by
  intro l
  induction l with
  | nil => intro c hc; exact absurd hc List.not_mem_nil
  | cons x t ih =>
      intro c hc
      by_cases hx : x = c
      · subst hx
        exact ⟨[], t, rfl, List.not_mem_nil⟩
      · have hmem : c ∈ t := by
          rcases List.mem_cons.mp hc with h | h
          · exact absurd h.symm hx
          · exact h
        obtain ⟨A, B, hAB, hA⟩ := ih hmem
        refine ⟨x :: A, B, by rw [hAB, List.cons_append], ?_⟩
        intro hmem2
        rcases List.mem_cons.mp hmem2 with h | h
        · exact hx h.symm
        · exact hA h

/-- `erase` removes the split card. -/
theorem erase_append_cons_of_not_mem : ∀ {A B : List Card} {c : Card}, c ∉ A →
    (A ++ c :: B).erase c = A ++ B := by
  intro A
  induction A with
  | nil =>
      intro B c _
      exact List.erase_cons_head c B
  | cons x t ih =>
      intro B c hc
      have hx : x ≠ c := fun h => hc (by rw [h]; exact List.mem_cons_self ..)
      show (x :: (t ++ c :: B)).erase c = x :: (t ++ B)
      rw [List.erase_cons_tail (by simp [hx])]
      rw [ih (fun h => hc (List.mem_cons_of_mem _ h))]

/-! ## §10. The licensed raiseS relation -/

/-- A cargo path does not change the S-licence (same orbit, same rungs). -/
theorem canRaiseS_cargoPath_bicond {z z' : State} (hz : z.WF) (hpath : CargoPath z z')
    {c : Card} : CanRaiseS z' c ↔ CanRaiseS z c := by
  have hz' : z'.WF := cargoPath_wf hz hpath
  constructor
  · intro h
    exact (canRaiseS_orbit_rung hz' (sameOrbitSetoid.iseqv.symm (sameOrbit_of_cargoPath hpath))
      (fun σ => (rungAt_cargoPath hpath σ).symm)).mp h
  · intro h
    exact (canRaiseS_orbit_rung hz (sameOrbit_of_cargoPath hpath)
      (rungAt_cargoPath hpath)).mp h

/-- `chop` of a list of length at least two is nonempty. -/
theorem chop_ne_nil_of_two_le {l : List Card} (h : 2 ≤ l.length) : chop l ≠ [] := by
  cases l with
  | nil => simp at h
  | cons x t =>
      cases t with
      | nil => simp at h
      | cons y t => simp [chop]

/-- **The card-word licence is the vanilla licence at the slide's end.**  Along a
cargo path the seat/hatch disjunct of a licence is invariant, so once the raise
*step* fires at the path's end the licence is vanilla there. -/
theorem canRaise_of_canRaiseS_of_step {z z₀ z' : State} {c : Card}
    (hz : z.WF) (hS : CanRaiseS z c) (hpath : CargoPath z z₀)
    (hstep : State.step z₀ (Move.tabToFound c) = some z') :
    CanRaise z₀ c := by
  have hz₀ : z₀.WF := cargoPath_wf hz hpath
  have hS₀ : CanRaiseS z₀ c := (canRaiseS_cargoPath_bicond hz hpath).mpr hS
  obtain ⟨hnu, a, hpa, -⟩ := step_tabToFound_inv hstep
  obtain ⟨-, a₂, bs, run, hshape, hseat, -⟩ := (canRaiseS_iff hz₀).mp hS₀
  have hmem : c ∈ (z₀.piles a₂).faceUp := by
    rw [hshape]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  have h1 : z₀.pileHolding c = some a₂ := (pileHolding_eq_some_iff hz₀).mpr hmem
  have h2 : z₀.pileHolding c = some a :=
    (pileHolding_eq_some_iff hz₀).mpr
      (Pile.mem_of_top (show (z₀.piles a).top = some c from (pileOfTop_top hpa).2))
  have haa : a₂ = a := Option.some.inj (h1.symm.trans h2)
  rw [haa] at hshape hseat
  refine ⟨hnu, a, hpa, ?_⟩
  rcases hseat with hbs | hbk
  · left
    rw [hshape]
    refine chop_ne_nil_of_two_le ?_
    cases bs with
    | nil => exact absurd rfl hbs
    | cons b bs' =>
        simp only [List.length_append, List.length_cons]
        omega
  · exact Or.inr hbk

namespace RaiseSSeqLicensed

/-- Every licensed play is a play. -/
theorem toSeq {s z : State} {ws : List Card} (h : RaiseSSeqLicensed s ws z) :
    RaiseSSeq s ws z := by
  induction h with
  | nil => exact RaiseSSeq.nil s
  | cons _ _ hp hs ih => exact RaiseSSeq.cons ih hp hs

/-- **The last step's licence.**  The origin of the last step is licensed for
its card. -/
theorem canRaiseS_head {s z' : State} {c : Card} {ws : List Card}
    (h : RaiseSSeqLicensed s (c :: ws) z') :
    ∃ z, RaiseSSeqLicensed s ws z ∧ CanRaiseS z c := by
  cases h with
  | cons htail hS _ _ => exact ⟨_, htail, hS⟩

/-- Well-formedness transports forward. -/
theorem wf {s z : State} {ws : List Card} (h : RaiseSSeqLicensed s ws z) :
    s.WF → z.WF := by
  induction h with
  | nil => exact id
  | cons _ _ hp hs ih => exact fun hwf => step_wf (cargoPath_wf (ih hwf) hp) hs

/-- **`step_s`** — the last step of a nonempty licensed play, with all its data
(the slide's end carries the *vanilla* licence, by
`canRaise_of_canRaiseS_of_step`). -/
theorem step_s {s z' : State} {c : Card} {ws : List Card}
    (h : RaiseSSeqLicensed s (c :: ws) z') (hwf : s.WF) :
    ∃ z z₀, RaiseSSeqLicensed s ws z ∧ CargoPath z z₀ ∧ CanRaise z₀ c ∧
      State.step z₀ (Move.tabToFound c) = some z' := by
  cases h with
  | cons htail hS hp hs =>
      exact ⟨_, _, htail, hp, canRaise_of_canRaiseS_of_step (wf htail hwf) hS hp hs, hs⟩

/-- **`cargoPath`** — the slide of the last step. -/
theorem cargoPath {s z' : State} {c : Card} {ws : List Card}
    (h : RaiseSSeqLicensed s (c :: ws) z') (hwf : s.WF) :
    ∃ z z₀, RaiseSSeqLicensed s ws z ∧ CargoPath z z₀ := by
  obtain ⟨z, z₀, htail, hp, -, -⟩ := step_s h hwf
  exact ⟨z, z₀, htail, hp⟩

/-- Licensed plays concatenate (`w₁` first, then `w₂`, gives the word `w₂ ++ w₁`). -/
theorem append {s u v : State} {w₁ w₂ : List Card}
    (h₁ : RaiseSSeqLicensed s w₁ u) (h₂ : RaiseSSeqLicensed u w₂ v) :
    RaiseSSeqLicensed s (w₂ ++ w₁) v := by
  induction h₂ generalizing s with
  | nil => exact h₁
  | cons _ hS hp hs ih =>
      rw [List.cons_append]
      exact RaiseSSeqLicensed.cons (ih h₁) hS hp hs

end RaiseSSeqLicensed

/-- **Adequacy, forward.**  The head card of a licensed play is `CanRaiseS` at
the state just before it is raised. -/
theorem canRaiseS_of_raiseSSeqLicensed_head {z z' : State} {c : Card}
    (h : RaiseSSeqLicensed z [c] z') : CanRaiseS z c := by
  have hh := RaiseSSeqLicensed.canRaiseS_head h
  obtain ⟨u, hnil, hc⟩ := hh
  cases hnil
  exact hc

/-- **Adequacy, backward.**  Every `CanRaiseS` licence is realisable as one
licensed step. -/
theorem raiseSSeqLicensed_step_of_canRaiseS {z : State} {c : Card}
    (h : CanRaiseS z c) : ∃ z', RaiseSSeqLicensed z [c] z' := by
  obtain ⟨z₀, hp, hcr⟩ := h
  obtain ⟨z', hs⟩ := step_tabToFound_of_canRaise hcr
  exact ⟨z', RaiseSSeqLicensed.cons (RaiseSSeqLicensed.nil z) ⟨z₀, hp, hcr⟩ hp hs⟩

/-- **R1, one licensed step.**  Raising a strictly different rank preserves a
card's licence (the forward direction of `specShift_sem_fwd`). -/
theorem canRaiseS_step_of_rank_ne_L {z z' : State} {d c : Card}
    (hz : z.WF) (hstep : RaiseStepS z z' d) (hr : d.rank ≠ c.rank) :
    CanRaiseS z c → CanRaiseS z' c :=
  canRaiseS_step_of_rank_ne hz hstep hr

/-- **R1, a licensed word.**  If every raised card has rank different from `c`'s,
`c`'s licence survives the whole play. -/
theorem RaiseSSeqLicensed.canRaiseS_persist_of_rank_ne {s z : State} {ws : List Card}
    {c : Card} (h : RaiseSSeqLicensed s ws z) (hwf : s.WF)
    (hr : ∀ d ∈ ws, d.rank ≠ c.rank) (hc : CanRaiseS s c) :
    CanRaiseS z c := by
  revert hwf hr hc
  induction h with
  | nil => intro _ _ hc; exact hc
  | cons htail hS hp hs ih =>
      rename_i zz zz0 zz' cc wws
      intro hwf hr hc
      have hr' : ∀ d ∈ wws, d.rank ≠ c.rank :=
        fun d hd => hr d (List.mem_cons_of_mem _ hd)
      have hcc : cc.rank ≠ c.rank := hr cc (List.mem_cons_self ..)
      have hzwf : zz.WF := RaiseSSeqLicensed.wf htail hwf
      have hz : CanRaiseS zz c := ih hwf hr' hc
      exact canRaiseS_step_of_rank_ne hzwf ⟨zz0, hp, hs⟩ hcc hz

/-- **`swap_of_licensed`** (the sharp adjacent swap).  If the prefix `A` has been
played from `s` to `u`, and **both** `d` and `e` are licensed at `u` with
`d.rank < e.rank`, then the two-step play `A · d · e` is realisable. -/
theorem swap_of_licensed {s u : State} {A : List Card} {d e : Card}
    (hpre : RaiseSSeqLicensed s A.reverse u) (hu : u.WF)
    (hd : CanRaiseS u d) (he : CanRaiseS u e)
    (hr : d.rank.toIdx < e.rank.toIdx) :
    ∃ z', RaiseSSeqLicensed s (e :: d :: A.reverse) z' := by
  obtain ⟨z₀, hp_d, hcr_d⟩ := hd
  obtain ⟨z₂, hs_d⟩ := step_tabToFound_of_canRaise hcr_d
  have hstep_d : RaiseStepS u z₂ d := ⟨z₀, hp_d, hs_d⟩
  have hde : d.rank ≠ e.rank := by intro h; rw [h] at hr; omega
  have he₂ : CanRaiseS z₂ e := canRaiseS_step_of_rank_ne hu hstep_d hde he
  obtain ⟨z₁, hp_e, hcr_e⟩ := he₂
  obtain ⟨z₃, hs_e⟩ := step_tabToFound_of_canRaise hcr_e
  refine ⟨z₃, ?_⟩
  exact RaiseSSeqLicensed.cons
    (RaiseSSeqLicensed.cons hpre ⟨z₀, hp_d, hcr_d⟩ hp_d hs_d)
    ⟨z₁, hp_e, hcr_e⟩ hp_e hs_e

/-! ## §11. R3 — the cover must be raised (play level) -/

/-- A raise of a card different from a seated card preserves its seat. -/
theorem seatOf_tabToFound_of_seated_ne {z z' : State} {c x t : Card}
    (hz : z.WF) (hstep : State.step z (Move.tabToFound c) = some z')
    (hseat : seatOf z x = some (Sum.inr t)) (hxc : x ≠ c) :
    seatOf z' x = some (Sum.inr t) := by
  obtain ⟨a, hhold, hbel, hlast⟩ := tfc_seatOf_of_inr hseat
  obtain ⟨a0, hpa0, hpiles⟩ := piles_tabToFound hstep
  have hwz' : z'.WF := step_wf hz hstep
  have hlastf : lastOf (z.piles a0).faceUp = some c := (pileOfTop_top hpa0).2
  have hmem : x ∈ (z.piles a).faceUp := pileHolding_mem hhold
  by_cases ha : a = a0
  · rw [ha] at hhold hbel hlast hmem
    have hchopmem : x ∈ chop (z.piles a0).faceUp :=
      mem_chop_of_mem_of_ne_last hmem hlastf hxc
    have hne : chop (z.piles a0).faceUp ≠ [] := fun h => by
      rw [h] at hchopmem
      exact absurd hchopmem List.not_mem_nil
    have hp0 : z'.piles a0 =
        Pile.afterRunRemoved (z.piles a0) (chop (z.piles a0).faceUp) := by
      rw [hpiles a0, ite_eq_left rfl]
    refine tfc_seatOf_inr_intro (a := a0) ?_ ?_
    · exact (pileHolding_eq_some_iff hwz').mpr (by
        rw [hp0, afterRunRemoved_faceUp_ne hne]
        exact hchopmem)
    · rw [hp0, afterRunRemoved_faceUp_ne hne,
        below_chop_of_mem_of_ne_last hmem hlastf hxc]
      exact hlast
  · have hmem' : x ∈ (z'.piles a).faceUp := by
      rw [hpiles a, ite_eq_right ha]
      exact hmem
    refine tfc_seatOf_inr_intro (a := a) ?_ ?_
    · exact (pileHolding_eq_some_iff hwz').mpr hmem'
    · rw [hpiles a, ite_eq_right ha]
      exact hlast

/-- A cargo leg preserves the seat of every card except its mover; a *seated*
card (non-king, sitting on a card) can never be the mover while its twin-mate's
cover is founded. -/
theorem seatOf_cargoLeg_of_seated {w v : State} {x t : Card}
    (hwf : w.WF) (hleg : CargoLeg w v)
    (hseat : seatOf w x = some (Sum.inr t))
    (hfound : t.twin ∈ w.found t.twin.suit) :
    seatOf v x = some (Sum.inr t) := by
  obtain ⟨c, b, hstep, hrev⟩ := hleg
  have hxnotking : x.rank ≠ Rank.king := tfc_seatOf_inr_rank_ne_king hwf hseat
  have hxc : x ≠ c := by
    intro hxc
    have hseat_c : seatOf w c = some (Sum.inr t) := by rw [← hxc]; exact hseat
    have hnk : c.rank ≠ Rank.king := by rw [← hxc]; exact hxnotking
    have hR : tabToTabR w c b = true :=
      (tabToTabR_iff_reversibleAtW hwf c b).mpr hrev
    obtain ⟨a, hhold, hcp, -⟩ := tfc_tabToTabR_inv hR
    cases b with
    | inl a' => exact hnk (canPlace_inl hcp).2
    | inr y =>
        obtain ⟨k, hk, hfit⟩ := canPlace_inr hcp
        obtain ⟨a2, hhold2, -, hlast2⟩ := tfc_seatOf_of_inr hseat_c
        have hfitt : canSitOn c t = true := (tfc_seat_parent hwf hhold2 hlast2).1
        rcases cover_seats_cases hfitt hfit with h | h
        · rw [h] at hk
          exact absurd hk (by rw [no_top_of_seat hwf hseat_c]; simp)
        · rw [h] at hk
          exact absurd hk (by rw [pileOfTop_eq_none_of_found hwf hfound]; simp)
  have hpoint := tfc_seat_point_edit hwf hstep hrev x
  rw [hpoint, ite_eq_right hxc]
  exact hseat

/-- A cargo path preserves a seated card's seat. -/
theorem seatOf_cargoPath_of_seated {w v : State} {x t : Card}
    (hwf : w.WF) (hpath : CargoPath w v)
    (hseat : seatOf w x = some (Sum.inr t))
    (hfound : t.twin ∈ w.found t.twin.suit) :
    seatOf v x = some (Sum.inr t) := by
  revert hwf hseat hfound
  induction hpath with
  | refl => intro _ hs _; exact hs
  | @cons w zmid v hleg hrest ih =>
      intro hwf hs hf
      have hw' : zmid.WF := cargoPath_wf hwf (Steps.cons hleg (Steps.refl zmid))
      have hs' : seatOf zmid x = some (Sum.inr t) :=
        seatOf_cargoLeg_of_seated hwf hleg hs hf
      have hf' : t.twin ∈ zmid.found t.twin.suit := by
        rw [found_cargoLeg hleg]; exact hf
      exact ih hw' hs' hf'

/-- **The seat invariant.**  If `x` sits on `t` and `t.twin` is founded at the
start, then along any play that does not raise `x`, `x` still sits on `t` and
`t.twin` is still founded. -/
theorem seat_invariant_of_not_mem {s z : State} {ws : List Card} {x t : Card}
    (h : RaiseSSeq s ws z) (hwf : s.WF)
    (hseat : seatOf s x = some (Sum.inr t))
    (hfound : t.twin ∈ s.found t.twin.suit)
    (hx : x ∉ ws) :
    seatOf z x = some (Sum.inr t) ∧ t.twin ∈ z.found t.twin.suit := by
  revert hwf hseat hfound hx
  induction h with
  | nil => intro _ hs hf _; exact ⟨hs, hf⟩
  | cons htail hp hs ih =>
      rename_i zz zz0 zz' cc wws
      intro hwf hseat hfound hx
      have hx' : x ∉ wws := fun hmem => hx (List.mem_cons_of_mem _ hmem)
      have hxc : x ≠ cc := fun hcon => hx (by rw [hcon]; exact List.mem_cons_self ..)
      have hzwf : zz.WF := raiseSSeq_wf htail hwf
      obtain ⟨hseat_zz, hfound_zz⟩ := ih hwf hseat hfound hx'
      by_cases htc : t = cc
      · exfalso
        have hnotop : zz0.pileOfTop cc = none := by
          rw [← htc]
          exact twin_covered_persists hzwf hseat_zz hfound_zz hp
        obtain ⟨-, a, hpa, -⟩ := step_tabToFound_inv hs
        rw [hnotop] at hpa
        exact absurd hpa (by simp)
      · have hseat_zz0 : seatOf zz0 x = some (Sum.inr t) :=
          seatOf_cargoPath_of_seated hzwf hp hseat_zz hfound_zz
        have hfound_zz0 : t.twin ∈ zz0.found t.twin.suit := by
          rw [found_cargoPath hp]; exact hfound_zz
        have hseat' : seatOf zz' x = some (Sum.inr t) :=
          seatOf_tabToFound_of_seated_ne (cargoPath_wf hzwf hp) hs hseat_zz0 hxc
        have hfound' : t.twin ∈ zz'.found t.twin.suit := by
          rw [found_tabToFound hs t.twin.suit]
          by_cases hsu : t.twin.suit = cc.suit
          · rw [ite_eq_left hsu]
            exact List.mem_append.mpr (Or.inl hfound_zz0)
          · rw [ite_eq_right hsu]
            exact hfound_zz0
        exact ⟨hseat', hfound'⟩

/-- **R3 (`CoverMustBeRaisedWord`), proved at the `RaiseSSeq` level.**  If `x`
sits on `t` and `t.twin` is founded at a WF start, every play that raises `t`
also raises `x`. -/
theorem cover_must_be_raised : CoverMustBeRaisedWord := by
  intro s z ws x t h
  induction h with
  | nil =>
      intro hwf hseat hfound ht
      exact absurd ht List.not_mem_nil
  | cons htail hp hs ih =>
      rename_i zz zz0 zz' cc wws
      intro hwf hseat hfound ht
      rcases List.mem_cons.mp ht with htc | htws
      · by_cases hxw : x ∈ wws
        · exact List.mem_cons_of_mem _ hxw
        · exfalso
          obtain ⟨hseat_zz, hfound_zz⟩ :=
            seat_invariant_of_not_mem htail hwf hseat hfound hxw
          have hnotop : zz0.pileOfTop cc = none := by
            rw [← htc]
            exact twin_covered_persists (raiseSSeq_wf htail hwf)
              hseat_zz hfound_zz hp
          obtain ⟨-, a, hpa, -⟩ := step_tabToFound_inv hs
          rw [hnotop] at hpa
          exact absurd hpa (by simp)
      · exact List.mem_cons_of_mem _ (ih hwf hseat hfound htws)

/-- **R3 for the licensed relation** (immediate from `cover_must_be_raised`). -/
theorem cover_must_be_raised_L {s z : State} {ws : List Card} {x t : Card}
    (h : RaiseSSeqLicensed s ws z) (hwf : s.WF)
    (hseat : seatOf s x = some (Sum.inr t))
    (hfound : t.twin ∈ s.found t.twin.suit)
    (ht : t ∈ ws) : x ∈ ws :=
  cover_must_be_raised h.toSeq hwf hseat hfound ht

end OneColourClosure

#print axioms OneColourClosure.mem_chop_of_mem_chop
#print axioms OneColourClosure.mem_and_below_of_mem_afterRunRemoved
#print axioms OneColourClosure.parented_tabToFound_of_ne
#print axioms OneColourClosure.bare_tabToFound_of_ne
#print axioms OneColourClosure.parented_of_tabToFound
#print axioms OneColourClosure.freeCardS_mono_of_ne_twin
#print axioms OneColourClosure.specShift_sem_fwd
#print axioms OneColourClosure.found_cargoPath
#print axioms OneColourClosure.parented_of_cargoPath
#print axioms OneColourClosure.raiseSSeq_append
#print axioms OneColourClosure.raiseSSeq_wf
#print axioms OneColourClosure.canRaiseS_step_of_rank_ne
#print axioms OneColourClosure.canRaiseS_persist_of_rank_ne
#print axioms OneColourClosure.above_rank_lt
#print axioms OneColourClosure.above_rank_lt_of_pile
#print axioms OneColourClosure.no_canPlace_of_seated
#print axioms OneColourClosure.twin_covered_persists
#print axioms OneColourClosure.step_none_of_twin_covered
#print axioms OneColourClosure.exists_append_cons_of_mem
#print axioms OneColourClosure.erase_append_cons_of_not_mem
#print axioms OneColourClosure.canRaiseS_cargoPath_bicond
#print axioms OneColourClosure.canRaise_of_canRaiseS_of_step
#print axioms OneColourClosure.RaiseSSeqLicensed.toSeq
#print axioms OneColourClosure.RaiseSSeqLicensed.wf
#print axioms OneColourClosure.RaiseSSeqLicensed.step_s
#print axioms OneColourClosure.RaiseSSeqLicensed.append
#print axioms OneColourClosure.canRaiseS_of_raiseSSeqLicensed_head
#print axioms OneColourClosure.raiseSSeqLicensed_step_of_canRaiseS
#print axioms OneColourClosure.RaiseSSeqLicensed.canRaiseS_persist_of_rank_ne
#print axioms OneColourClosure.swap_of_licensed
#print axioms OneColourClosure.seatOf_tabToFound_of_seated_ne
#print axioms OneColourClosure.seatOf_cargoLeg_of_seated
#print axioms OneColourClosure.seatOf_cargoPath_of_seated
#print axioms OneColourClosure.seat_invariant_of_not_mem
#print axioms OneColourClosure.cover_must_be_raised
#print axioms OneColourClosure.cover_must_be_raised_L

/-! ## §12. The battery (rest of the deck) -/

#print axioms OneColourClosure.mem_chop_of_mem_of_ne_last
#print axioms OneColourClosure.below_chop_of_mem_of_ne_last
#print axioms OneColourClosure.mem_afterRunRemoved_faceUp_of_mem_of_ne_last
#print axioms OneColourClosure.afterRunRemoved_faceUp_bare
#print axioms OneColourClosure.piles_tabToFound
#print axioms OneColourClosure.found_tabToFound
#print axioms OneColourClosure.mem_piles_tabToFound_of_mem_of_ne
#print axioms OneColourClosure.not_mem_piles_tabToFound_self
#print axioms OneColourClosure.revEqW_of_cargoPath
#print axioms OneColourClosure.sameOrbit_of_cargoPath
#print axioms OneColourClosure.nextUp_cargoPath
#print axioms OneColourClosure.found_cargoLeg
#print axioms OneColourClosure.raiseStepS_of_canRaiseS
#print axioms OneColourClosure.raiseSSeq_snoc
#print axioms OneColourClosure.raiseStepS_wf
#print axioms OneColourClosure.canRaiseS_persist_of_rank_ne
#print axioms OneColourClosure.cover_rank_lt
#print axioms OneColourClosure.cover_rank_ne
#print axioms OneColourClosure.chop_ne_nil_of_two_le
#print axioms OneColourClosure.RaiseSSeqLicensed.toSeq
#print axioms OneColourClosure.RaiseSSeqLicensed.canRaiseS_head
#print axioms OneColourClosure.RaiseSSeqLicensed.cargoPath
#print axioms OneColourClosure.canRaiseS_step_of_rank_ne_L


