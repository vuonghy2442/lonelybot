import Orig2.Fork.Class.ForkRaiseReorder

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# `SpecShift` by the independent semantic route

The read that a raise must preserve is `freeCardS` (the tableau half of the
S-license).  We prove the one-directional form

    freeCardS z d = true → freeCardS z' d = true

for a fired `tabToFound c` with `d ≠ c`, `d ≠ c.twin`, by rebuilding the
`freeCardS_sem` triple at the landing state:

* the holding is carried by face-up membership (`d` is not the removed top);
* `Parented`/`Bare` of `d` are untouched (the raise removes a *pile top*,
  which is never *below* anything);
* the hatch clause only needs `¬ Parented` of cards (antitone along the raise)
  and face-up membership of `d.twin` (which is not `c`).

Then `SpecShift`'s forward direction follows by combining with the slide leg
(`freeCardS_orbit_rung`) and `nextUp_raise_ne`.
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
  rw [afterRunRemoved_ne hne]
  exact hchop

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
      rw [afterRunRemoved_ne hchop]
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
      rw [afterRunRemoved_ne hne]
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
    rw [afterRunRemoved_ne hne]
    exact hhid
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

/-! ## §6. Why the converse is not available from these hypotheses

The `SpecShift` statement as written only excludes `d = c` and `d = c.twin`.
It does *not* exclude the **same-suit successor** of `c`: a card `d` with
`d.suit = c.suit` and `d.rank = c.rank + 1`.  Raising `c` advances that
suit's rung by one, so such a `d` becomes next-up at the landing state while
it was not next-up before.  The `nextUp` half of the reverse direction is
therefore false whenever such a `d` exists; `CanRaiseS` (which is
`nextUp ∧ freeCardS`) inherits the failure as soon as the successor is
tableau-ready at the landing. -/

/-- **The same-suit successor flips `nextUp`.** -/
theorem nextUp_raise_same_suit_succ {z z' : State} {c d : Card}
    (hstep : State.step z (Move.tabToFound c) = some z')
    (hsu : d.suit = c.suit)
    (hrank : d.rank.toIdx = c.rank.toIdx + 1) :
    z'.nextUp d = true ∧ z.nextUp d = false := by
  have hnextc : z.nextUp c = true := (step_tabToFound_inv hstep).1
  have hcz : c.rank.toIdx = z.foundHeight c.suit := of_decide_eq_true hnextc
  have hfound : z'.found d.suit = z.found d.suit ++ [c] := by
    rw [found_tabToFound hstep d.suit]
    rw [ite_eq_left hsu]
  have hlen : z'.foundHeight d.suit = z.foundHeight d.suit + 1 := by
    unfold State.foundHeight
    rw [hfound, List.length_append, List.length_singleton]
  have hzlen : z.foundHeight d.suit = c.rank.toIdx := by
    rw [show z.foundHeight d.suit = z.foundHeight c.suit from by rw [hsu]]
    exact hcz.symm
  constructor
  · unfold State.nextUp
    rw [hlen, hzlen, hrank]
    simp
  · unfold State.nextUp
    rw [hzlen, hrank]
    exact decide_eq_false (by omega)

/-- **The reverse direction of `SpecShift` fails** for a same-suit successor
that is S-raisable at the landing state.  Hence the `↔` of the card cannot be
proved from `d ≠ c`, `d ≠ c.twin` alone; the forward direction
(`specShift_sem_fwd`) is the usable half. -/
theorem not_canRaiseS_iff_of_same_suit_succ {z z' : State} {c d : Card}
    (hz : z.WF) (hstep : State.step z (Move.tabToFound c) = some z')
    (hsu : d.suit = c.suit)
    (hrank : d.rank.toIdx = c.rank.toIdx + 1)
    (hS' : CanRaiseS z' d) :
    ¬ (CanRaiseS z d ↔ CanRaiseS z' d) := by
  obtain ⟨-, hfalse⟩ := nextUp_raise_same_suit_succ hstep hsu hrank
  intro hiff
  have hS : CanRaiseS z d := hiff.mpr hS'
  have hnext : z.nextUp d = true := (canRaiseS_split hz).mp hS |>.1
  rw [hfalse] at hnext
  exact absurd hnext (by simp)

end OneColourClosure

#print axioms OneColourClosure.mem_chop_of_mem_of_ne_last
#print axioms OneColourClosure.mem_and_below_of_mem_afterRunRemoved
#print axioms OneColourClosure.parented_tabToFound_of_ne
#print axioms OneColourClosure.bare_tabToFound_of_ne
#print axioms OneColourClosure.parented_of_tabToFound
#print axioms OneColourClosure.freeCardS_mono_of_ne_twin
#print axioms OneColourClosure.specShift_sem_fwd
#print axioms OneColourClosure.nextUp_raise_same_suit_succ
#print axioms OneColourClosure.not_canRaiseS_iff_of_same_suit_succ
