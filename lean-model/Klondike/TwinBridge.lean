import Klondike.TwinReplay

/-!
# The merge bridge scaffold — [H] and [H′] assembled modulo named
premises

This file assembles the merge bridge (`State.solvable_of_exchange_merge`,
TwinQuotient's [H] crux) from the machinery already landed in TwinExchange,
TwinQuotient and TwinReplay, taking THREE premises by name:

* **the window** (`hwin`, TwinReplay's `solvable_of_twinCorr_window`, being
  delivered concurrently): the climb-out replay — a twin-correlated pair
  (`TwinCorr τ_u u.suit S M`) at a WF, solvable source has a solvable
  mirror;
* **the rider-prefix normalization** (`hrp`, `State.ExchangeRiderPrefix`
  below): the source's winning line can be scheduled so that a prefix
  clears z's riders BEFORE the merge, the merge re-fires at the cleared
  state with a solvable successor, and the prefix replays verbatim in the
  exchanged state (the successors staying exchanged);
* **the deep-landing normalization, ITERATED** (`hdet`,
  `State.ExchangeDeepNorm` below): at a hole-shaped state (the first
  rider fits neither cargo), a `CleanAt` clearing prefix exists after
  which the rider run has a legal detach whose follow-up merge keeps
  the source solvable.  The plain single-detach form is FALSE at WF —
  detour.lean's non-king rider (both candidate tops occupied, the one
  free anchor king-locked) and detour2.lean's king rider (all seven
  anchors filled) leave NO detach base; the iterated repair (the
  clearing stack, then the detach, then the same merge) is validated on
  both sides at both witnesses (plays `playIter`/`playIterX`,
  `playIter2`/`playIter2X`, all winning, heights [13,13,13,13]).

The assembly itself — everything between the premises — is PROVEN here:

* `State.twinCorr_of_ply`: the ply conclusion (the mirror's board is the
  source's, twin-swapped at the cargo z, every other field equal) IS the
  climb-out correspondence `TwinCorr τ_z z.suit` — the per-card stacked-set
  invariant holds because both twin suits sit at or below z's rank at a WF
  post-merge state (the cargos are seated, `founds_gone`), so the
  cross-cases are false on both sides.
* `State.exchange_merge_ply_deep_fit` (route step 2b, the FIT case): at a
  riders-cleared licensed state whose first rider r₁ fits z, the mirror
  plays the RIDER TRANSFER `pilePile r₁ (inr z)` — landing r₁'s run on the
  bare z — and that one move conjugates the exchange into the board-only
  twin swap: the mirror state after it IS `S.swapTwinBoard z` (the per-seat
  analysis: the four twin seats carry the swapped values, the two moved
  seats the attach/detach updates, everywhere else the inj-pinned
  cargo-freeness fixes the value).  The ORIGINAL merge then conjugates
  verbatim by `apply_swapTwinBoard_clean` (a `pilePile` is unconditionally
  clean, and c, d are off the cargo pair by the guard and the case split),
  so the two-ply lands at exactly `a₁.swapTwinBoard z` — fithole2's
  validated statement.  The premise form is RUN-SHAPE-FREE (the `hexc`/
  `hexd` exclusions instead of the [H] run-passes-twin clause), so the
  ROOTED bridge [H′] reuses this one ply lemma at `c := t`.
* `State.solvable_of_exchange_merge_cleared`: the assembly at a
  riders-cleared state — the landing case analysis (the own-cargo side
  dies by `merge_own_landing_absurd`, the source's self-landing guard;
  ROOT = d = z' cites the proven `exchange_merge_ply_root`; DEEP+FIT cites
  the two-ply above; DEEP+HOLE plays hdet's ITERATED detour — the CleanAt
  clearing prefix π₀, replayed in the exchange by the run-level
  clean-replay lemma `exchangeTwinCargo_run_cleanAt`, then the detach,
  replayed by the clean-run mirror step — and then the SAME merge is a
  passing move in both games by `exchangeTwinCargo_step_pilePile_passing`,
  the mirror's result being the seat-exchange of the source's normalized
  successor, which equals its twin swap at z because the merge preserves
  the cargos' covers of the twins (`Board.exchangeTwin_eq_mapByTwin_of_covers`)),
  then the correspondence, then `hwin`, then the explicit play.
* `State.solvable_of_exchange_merge_bridge` / `_bridge_flip` /
  `_bridge_full`: the [H]-shaped wrappers — the full signature of
  `solvable_of_exchange_merge` (at the license's pinned cargo pair), the
  t'/t-flipped dual, and the disjunctive-hmerge combination.

§7 below repeats the tier for the ROOTED twin of the crux — [H′],
`State.solvable_of_exchange_merge_rooted` (the merge whose run is the
twin's OWN — the move `pilePile t b`, the run [t, z] — landing deep in
the z'-stack) — modulo the same three premises in their rooted readings
(`State.ExchangeRiderPrefixRooted`, `State.ExchangeDeepNormRooted`):

* `State.solvable_of_exchange_merge_rooted_cleared`: the rooted assembly
  at a riders-cleared state — SIMPLER than [H]'s: the landing is always
  DEEP (the merge's own fit excludes the root d = z' by the rung gap and
  the own cargo by the antisymm, both derived here), so the dispatch is
  only the first rider's FIT/HOLE case; FIT is [H]'s two-ply at c := t
  (the rider transfer onto the bare z, then the mirror's rooted merge
  [t, z'] onto d — landing exactly at a₁ twin-swapped at the cargo);
  HOLE is hdet's ITERATED detour — the CleanAt clearing prefix (the
  run-level clean-replay), the detach (the clean-run mirror step), the
  passing merge, the covers→twin-swap, the correspondence, `hwin`, the
  play.
* `State.solvable_of_exchange_merge_rooted_bridge` / `_rooted_bridge_flip`
  / `_rooted_bridge_full`: the [H′]-shaped wrappers — the pinned-pair
  scaffold, the t'/t-flipped dual, and the exact signature of
  `solvable_of_exchange_merge_rooted` (the ∃z-package of the two
  normalization premises standing in for the license's unpacked z).

§8 below is the DIRECT reduction — the endgame simplification on the
STRENGTHENED window (TwinReplay's `solvable_of_twinCorr_window'`,
commit 33a7d22: the stack skew GONE — misaligned pair-stacks route to
the growth; only the pair-deckStack exclusion [vacuous at licensed
states, `apply_deckStack_ne_of_vis`], the pre-episode unstack
anti-skew, and the mid-episode tableau exclusion remain): at a licensed
WF state whose BOTH cargo stacks are bare, the exchange is
twin-correlated with the source at the CARGO pair
(`State.twinCorr_exchangeTwinCargo` — the covers identify the seat
exchange with the cargo twin swap), so the window' replays the source's
ENTIRE window'-admitted winning play, the merge included (a `pilePile`
is unconditionally admitted in the pre-episode phase, composed by
`State.solvableWindow'_cons_pilePile`), and the exchange wins
(`State.solvable_of_exchange_merge_direct`).  The window's added
premises are discharged: `hMle` by the correspondence lemma,
`hhid`/`hstock` by `State.swapTwin_hid_stock_of_covers` (WF + the
covers — the cargos seated, hence visible, hence off the hidden slices
and the stock; the shrink lemmas
`State.swapTwin_hid_stock_sub_apply` cover the alternative
through-the-prefix route); what replaces plain solvability is `hsolw'`
at z (NOT `swapTwin z` — the strengthened window's own convention).  The naive twin-pair form
of the correspondence is FALSE at licensed states (rootedprobe3.lean:
the exchange swaps seat contents without relabeling card identities, so
the value-relabeling board clause fails at the twins' own bases — and
its requirements are mutually exclusive with the founds_gone
cross-case); the deep corners (riders on z') obstruct even the
cargo-pair form, and are served either by the §5/§7 scaffolds or by
the double-clearing premise (`State.ExchangeDoubleClear` +
`State.solvable_of_exchange_merge_rooted_direct` — the successor
premise window'-shaped), which restores the direct route and supersedes
hdet there.  The TRANSFER characterization (the playWindow'-of-solvable
question): `State.playWindow'_adjacent_pair` proves the sufficiency
half - the adjacent pair-stacking [pileStack z; pileStack z'; rest]
with the first stack's skew failing is FULLY admitted (growth ->
catch-up -> post, the rest unconditional); `apply_deckStack_ne_of_vis`
kills the pair-deckStack exclusion at licensed states;
`State.playWindow'_adjacent_pair_skew` closes the SKEW-HOLDING adjacent
case modulo the tail's pre-admission (the second stack's skew DERIVED
from the first's rung-exact firing; the twin rungs EQUALIZE at
z.rank + 1), and `State.playWindow'_of_eq_heights` composes the two
into the equal-heights sufficiency theorem at the adjacent-head shape
(the "equal heights" a CONSEQUENCE - the exchange's heights are
rfl-equal, the stackings equalize the twin rungs; validated end-to-end
at the dblclear2 witness's both-bare state, eqheights.lean); the
residuals are the unstack anti-skew for non-pair twin-suit worry-backs
pulled below a raised partner rung (the L1/L2 interleaving) and the
ADJACENCY itself (the z'-suit rung-raisers between the stackings
CANNOT commute past the second stacking - they raise its firing rung;
they are themselves window'-admitted, their skews holding from the
first stacking's raised rung).

The ADJACENCY residual is closed SELECTIVELY (§11, the re-scheduling):
the raisers must stay, but every HEIGHT-BLIND move commutes — and the
height-blind kinds (draw/reveal/deckPile/pilePile — `Move.heightBlind`)
are exactly the non-raisers.  `State.ZClean`/`State.ZCleanRun` package
the cleanliness (the touched cards off z', the touched bases off
z''s own seat), `State.stacking_swap_zclean` is the SINGLE SWAP with
the full firing transfer (both orders fire, the same final state),
`State.run_bubble_stacking` bubbles the second stacking past a whole
z-clean segment, and `State.playWindow'_of_rescheduled` composes the
bubble with the adjacent-head sufficiency — a winning play
[pileStack z; π₂; pileStack z'; π₃] with π₂ z'-clean gives
`solvableWindow'`, the height-blind π₂ unconditionally pre-admitted
so the tail premise reduces to π₃'s.  The remaining residuals are the
unstack anti-skew above and the raisers themselves (they must stay
between the stackings — the re-scheduled play keeps them in place).

§9 attacks that premise and REDUCES it: probed at the blockade
witnesses (dblclear.lean), no refuting witness exists — the cycle
constructions dissolve at the solvability hypothesis (draws/deckStacks
are clean, and a rider's suit is disjoint from both cargos' suits, so
no rung-raiser is ever protected) — but a full proof needs the L1/O3
scheduling machinery, so the premise STAYS, with its hardest-looking
clause DERIVED: `State.exchangeDoubleClear_of_sched` converts it to the
SCHEDULED form (a CleanStack prefix — `pileStack`s of off-pair cards,
riders allowed — running to a both-bare licensed state where the merge
re-fires with a solvable successor), the mirror's verbatim replay being
the run-level lemma `State.exchangeTwinCargo_run_cleanStack`.
`State.solvable_of_exchange_merge_rooted_sched` is the scheduled direct
bridge; `State.rider_clear_sched` is the single-swap commutation —
COMPLETE with its firing transfer (the swapped order's firing derived
from the disjointness plus the root-not-on-q corner, through the
attach/detach congruences), the L1/O0 building block unconditional in
the run.

§10 is the CONSTRUCTIVE route (dblclear2.lean): the blockade witness
rebuilt with the blocker's rung NOT yet arrived and the missing rung
card in the stock — the constructive schedule [deckStack the raiser; 
pileStack the blocker; the z'-detour; the merge; the climbs] wins on
BOTH sides.  Landed: `State.rung_raiser_off_pairs` (the rank-ladder
arithmetic — every rung-raiser of a fit-seated rider is off the
protected four; stock cards are never protected outright by WF's
vis_off_cycle) and the MIXED scheduled form
`State.exchangeDoubleClear_of_sched_mixed` (a CleanStack prefix plus
the z'-detour, the mirror's verbatim replay derived for the WHOLE mixed
prefix) with its direct bridge
`State.solvable_of_exchange_merge_rooted_sched_mixed`.  The residue:
the schedule's EXISTENCE at arbitrary WF+licensed+solvable states (the
raisers' reachability and the blocker-chain's termination) and the
successor's WINDOW-solvability (the solvableFrom-to-solvableWindow
transfer is the L1/O0 residue) — the constructive evidence covers the
probed geometries.

**Honest boundaries, recorded for the later sessions:**

1. The license enters UNPACKED and PINNED (`State.TwinLicensedAt`): the
   packaged `st.twinLicensed t` does not pin z, z', and the landing
   hypothesis is only meaningful at the license's witnesses (the
   simulation's call site unpacks them, so this is the drop-in form).
2. The rider-prefix normalization is NOT premise-free here: the source-side
   commutation ([merge; π₁] ≈ [π₁; merge]) is an L1/O3-shaped play
   normalization, and the prefix's exchange-replay needs per-move premises
   (a general winning prefix may stack the twins themselves).  This is
   `State.ExchangeRiderPrefix`'s content (and, read at the rooted run,
   `State.ExchangeRiderPrefixRooted`'s — the riders cleared are those of
   the MOVED run's own cargo z).
3. The deep-landing normalization is NOT premise-free: the plain
   single-detach form is FALSE at WF (detour.lean's and detour2.lean's
   blockades), so the premise carries the ITERATED repair — a CleanAt
   clearing prefix, then the detach — and the follow-up source
   solvability is another commutation with two in-principle breaking
   channels (the detour occupying a needed base; an e-inversion stalling
   a suit), neither observed.  This is `State.ExchangeDeepNorm`'s (and,
   read at the rooted run, `State.ExchangeDeepNormRooted`'s) content.
-/

/-! ## §1. Small helpers -/

/-- One bare cover: if `r` covers `u` and `r` itself is bare, the walk
from `u` collects exactly `r`. -/
theorem Board.aboveOf_cover_bare {bd : Board} {u r : Card}
    (hcover : bd.topOf (Sum.inr u) = some r) (hbare : bd.topOf (Sum.inr r) = none) :
    bd.aboveOf u = [r] := by
  have hnc : r ∉ bd.aboveOf r := by
    rw [Board.aboveOf_step_none hbare]; simp
  rw [Board.aboveOf_step_some hcover hnc, Board.aboveOf_step_none hbare]
  rfl

/-- The unpacked exchange license, PINNED to the given cargo pair: the
packaged `twinLicensed` bundles the same fields behind an existential
over the cargos, which does not pin `z, z'`. -/
def State.TwinLicensedAt (st : State) (t z z' : Card) : Prop :=
  st.isVis t = true ∧ st.isVis t.flipSuit = true ∧
    st.board.bottomOf z = some (Sum.inr t) ∧
    st.board.bottomOf z' = some (Sum.inr t.flipSuit) ∧
    canSitOn z t = true ∧ canSitOn z' t.flipSuit = true ∧
    (t ∉ st.board.aboveOf z ∧ t.flipSuit ∉ st.board.aboveOf z) ∧
    (t ∉ st.board.aboveOf z' ∧ t.flipSuit ∉ st.board.aboveOf z')

/-- The packaged license, pinned by the twins' covers (the witnesses of the
existential are the cargos covering the twins, so the cover equations
identify them). -/
theorem State.twinLicensedAt_of_twinLicensed {st : State} {t z z' : Card}
    (h : st.twinLicensed t)
    (hz : st.board.topOf (Sum.inr t) = some z)
    (hz' : st.board.topOf (Sum.inr t.flipSuit) = some z') :
    st.TwinLicensedAt t z z' := by
  obtain ⟨z₀, z₀', hvis, hvis', h₀, h₀', hfit, hfit', hnb, hnb'⟩ := h
  have hzz₀ : z₀ = z := Option.some.inj
    (((Board.bottomOf_eq st.board z₀ (Sum.inr t)).mp h₀).symm.trans hz)
  have hzz₀' : z₀' = z' := Option.some.inj
    (((Board.bottomOf_eq st.board z₀' (Sum.inr t.flipSuit)).mp h₀').symm.trans hz')
  subst hzz₀
  subst hzz₀'
  exact ⟨hvis, hvis', h₀, h₀', hfit, hfit', hnb, hnb'⟩

/-- A `pilePile` never moves another card's base: the detach removes only
the moved root from its own seat, the attach seats only the moved root,
and every other card's base is untouched (a non-moved card cannot sit at
the free landing, nor at the detach seat whose occupant is the moved
root). -/
theorem State.apply_pilePile_bottomOf {st st' : State} {c : Card} {b : Base}
    (hstep : st.apply (Move.pilePile c b) = some st') :
    ∀ {d : Card}, d ≠ c → st'.board.bottomOf d = st.board.bottomOf d := by
  have happ := hstep
  rw [apply_pilePile_iff] at happ
  obtain ⟨β₀, hbot, -, hcmr, bd, hatt, rfl⟩ := happ
  have hcp : st.canPlace c b = true := by
    simp only [State.canMoveRun, Bool.and_eq_true_iff] at hcmr
    exact hcmr.1
  have hfree : st.board.topOf b = none := topOf_of_canPlace hcp
  have hβ₀c : st.board.topOf β₀ = some c := (Board.bottomOf_eq _ _ _).mp hbot
  intro d hd
  cases hb : st.board.bottomOf d with
  | none =>
      refine (Board.bottomOf_eq_none _ _).mpr (fun β' hβ' => ?_)
      by_cases hbb : β' = b
      · rw [hbb, Board.attach_topOf _ _ _ hatt] at hβ'
        exact hd (Option.some.inj hβ').symm
      · rw [Board.attach_topOf_ne _ _ _ hatt hbb] at hβ'
        by_cases hbβ : β' = β₀
        · rw [hbβ, Board.detach_topOf] at hβ'
          exact absurd hβ' (by simp)
        · rw [Board.detach_topOf_ne _ _ _ hbβ] at hβ'
          exact absurd ((Board.bottomOf_eq _ _ _).mpr hβ') (by rw [hb]; simp)
  | some β' =>
      have hβ'd : st.board.topOf β' = some d := (Board.bottomOf_eq _ _ _).mp hb
      have hbb : β' ≠ b := by
        intro hcon
        rw [hcon, hfree] at hβ'd
        exact absurd hβ'd (by simp)
      have hbβ : β' ≠ β₀ := by
        intro hcon
        rw [hcon] at hβ'd
        exact hd (Option.some.inj (hβ₀c.symm.trans hβ'd)).symm
      exact (Board.bottomOf_eq _ _ _).mpr (by
        rw [Board.attach_topOf_ne _ _ _ hatt hbb, Board.detach_topOf_ne _ _ _ hbβ]
        exact hβ'd)

/-- A `pilePile` preserves every seat reading away from its own attach
base and its own detach base (the moved root's base). -/
theorem State.apply_pilePile_topOf {st st' : State} {c : Card} {b β₀ : Base}
    (hstep : st.apply (Move.pilePile c b) = some st')
    (hbot : st.board.bottomOf c = some β₀) {β : Base}
    (hβb : β ≠ b) (hββ₀ : β ≠ β₀) :
    st'.board.topOf β = st.board.topOf β := by
  have happ := hstep
  rw [apply_pilePile_iff] at happ
  obtain ⟨β₀', hbot', -, -, bd, hatt, rfl⟩ := happ
  have hbb₀ : β₀' = β₀ := Option.some.inj (hbot'.symm.trans hbot)
  subst hbb₀
  rw [Board.attach_topOf_ne _ _ _ hatt hβb, Board.detach_topOf_ne _ _ _ hββ₀]

/-- When both cargos still cover the twins (`z` on `t`, `z'` on `t'`), the
cargos are a twin pair, and both cargo seats read bare (the run's top and
the emptied stack), the seat exchange at the twins IS the board twin swap
at the cargo: at the two twin seats the swapped values and the relabelled
values agree (each cargo covers a twin, and only those seats carry the
cargo values); at the two cargo seats both operations read `none`; and
everywhere else both fix the seat reading (the values are off the cargo
pair by `inj`). -/
theorem Board.exchangeTwin_eq_mapByTwin_of_covers {bd : Board} {t z z' : Card}
    (hztop : bd.topOf (Sum.inr t) = some z)
    (hztop' : bd.topOf (Sum.inr t.flipSuit) = some z')
    (hcargo : z' = z.flipSuit)
    (hzne : z ≠ t ∧ z ≠ t.flipSuit)
    (hbare : bd.topOf (Sum.inr z) = none ∧ bd.topOf (Sum.inr z') = none) :
    bd.exchangeTwin t = bd.mapByTwin z := by
  have hzne' : z' ≠ t ∧ z' ≠ t.flipSuit := by
    constructor
    · intro h
      rw [hcargo] at h
      have h2 := congrArg Card.flipSuit h
      rw [Card.flipSuit_flipSuit] at h2
      exact hzne.2 h2
    · intro h
      have h2 := congrArg Card.flipSuit (h.symm.trans hcargo)
      rw [Card.flipSuit_flipSuit, Card.flipSuit_flipSuit] at h2
      exact hzne.1 h2.symm
  have htz : t ≠ z := fun h => hzne.1 h.symm
  have htzfs : t ≠ z.flipSuit := fun h => hzne'.1 (h.trans hcargo.symm).symm
  have ht'z : t.flipSuit ≠ z := fun h => hzne.2 h.symm
  have ht'zfs : t.flipSuit ≠ z.flipSuit := fun h => hzne'.2 (h.trans hcargo.symm).symm
  have hstz : Base.swapTwin t (Sum.inr z) = Sum.inr z :=
    Base.swapTwin_eq_self (fun h => hzne.1 (Sum.inr.inj h))
      (fun h => hzne.2 (Sum.inr.inj h))
  have hstz' : Base.swapTwin t (Sum.inr z') = Sum.inr z' :=
    Base.swapTwin_eq_self (fun h => hzne'.1 (Sum.inr.inj h))
      (fun h => hzne'.2 (Sum.inr.inj h))
  have hsz : Base.swapTwin z (Sum.inr z) = Sum.inr z' := by
    show Sum.inr (Card.swapTwin z z) = _
    rw [Card.swapTwin_self_left, hcargo]
  have hsz' : Base.swapTwin z (Sum.inr z') = Sum.inr z := by
    show Sum.inr (Card.swapTwin z z') = _
    rw [hcargo, Card.swapTwin_self_right]
  apply Board.ext_topOf
  funext b
  rw [Board.exchangeTwin_topOf, mapByTwin_topOf]
  by_cases hbt : b = Sum.inr t
  · have hstt : Base.swapTwin t (Sum.inr t) = Sum.inr t.flipSuit := by
      show Sum.inr (Card.swapTwin t t) = _
      rw [Card.swapTwin_self_left]
    have hszt : Base.swapTwin z (Sum.inr t) = Sum.inr t :=
      Base.swapTwin_eq_self (fun h => htz (Sum.inr.inj h))
        (fun h => htzfs (Sum.inr.inj h))
    rw [hbt, hstt, hszt, hztop', hztop]
    show some z' = some (Card.swapTwin z z)
    rw [Card.swapTwin_self_left, ← hcargo]
  · by_cases hbt' : b = Sum.inr t.flipSuit
    · have hstt' : Base.swapTwin t (Sum.inr t.flipSuit) = Sum.inr t := by
        show Sum.inr (Card.swapTwin t t.flipSuit) = _
        rw [Card.swapTwin_self_right]
      have hsztt' : Base.swapTwin z (Sum.inr t.flipSuit) = Sum.inr t.flipSuit :=
        Base.swapTwin_eq_self (fun h => ht'z (Sum.inr.inj h))
          (fun h => ht'zfs (Sum.inr.inj h))
      rw [hbt', hstt', hsztt', hztop, hztop']
      show some z = some (Card.swapTwin z z')
      rw [hcargo, Card.swapTwin_self_right]
    · by_cases hbz : b = Sum.inr z
      · rw [hbz, hstz, hsz, hbare.1, hbare.2]
        rfl
      · by_cases hbz' : b = Sum.inr z'
        · rw [hbz', hstz', hsz', hbare.2, hbare.1]
          rfl
        · have hfixt : b.swapTwin t = b := Base.swapTwin_eq_self hbt hbt'
          have hfixz : b.swapTwin z = b :=
            Base.swapTwin_eq_self hbz (fun h => hbz' (h.trans (congrArg Sum.inr hcargo.symm)))
          rw [hfixt, hfixz]
          cases hval : bd.topOf b with
          | none => rfl
          | some v =>
              have hvz : v ≠ z := by
                intro hcon
                rw [hcon] at hval
                exact hbt (bd.inj b (Sum.inr t) z hval hztop)
              have hvz' : v ≠ z' := by
                intro hcon
                rw [hcon] at hval
                exact hbt' (bd.inj b (Sum.inr t.flipSuit) z' hval hztop')
              have hvzfs : v ≠ z.flipSuit := fun h => hvz' (h.trans hcargo.symm)
              show some v = Option.map z.swapTwin (some v)
              show some v = some (Card.swapTwin z v)
              rw [Card.swapTwin_of_ne hvz hvzfs]

/-- The first rider (the card directly on `z'`) is off the twin pair and
off both cargos: it covers `z'`, so it cannot be `z'` (a seat hosts one
card) nor `z` (that would re-seat `z` off `t`), and a twin above it would
braid the `z'`-stack. -/
theorem State.first_rider_off {S : State} {t z z' r₁ : Card}
    (h₀ : S.board.bottomOf z = some (Sum.inr t))
    (h₀' : S.board.bottomOf z' = some (Sum.inr t.flipSuit))
    (hfit' : canSitOn z' t.flipSuit = true)
    (hnb' : t ∉ S.board.aboveOf z' ∧ t.flipSuit ∉ S.board.aboveOf z')
    (hr₁ : S.board.topOf (Sum.inr z') = some r₁) :
    r₁ ≠ z ∧ r₁ ≠ z' ∧ r₁ ≠ t ∧ r₁ ≠ t.flipSuit := by
  have hzne' : z' ≠ t ∧ z' ≠ t.flipSuit := by
    obtain ⟨ha, hb⟩ := Card.ne_pair_of_canSitOn hfit'
    exact ⟨by rwa [Card.flipSuit_flipSuit] at hb, ha⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hcon
    rw [hcon] at hr₁
    have hb := (Board.bottomOf_eq S.board z (Sum.inr z')).mpr hr₁
    rw [h₀] at hb
    exact hzne'.1 (Sum.inr.inj (Option.some.inj hb)).symm
  · intro hcon
    rw [hcon] at hr₁
    have hb := (Board.bottomOf_eq S.board z' (Sum.inr z')).mpr hr₁
    rw [h₀'] at hb
    exact hzne'.2 (Sum.inr.inj (Option.some.inj hb)).symm
  · intro hcon
    rw [hcon] at hr₁
    exact hnb'.1 (Board.mem_aboveOf_of_topOf hr₁)
  · intro hcon
    rw [hcon] at hr₁
    exact hnb'.2 (Board.mem_aboveOf_of_topOf hr₁)

/-- WF is run-invariant: every firing move of a run preserves it
(`apply_wf`, inducted over the play). -/
theorem State.wf_run {st st' : State} {π : List Move}
    (hwf : st.WF) (hrun : st.run π = some st') : st'.WF := by
  induction π generalizing st st' with
  | nil =>
      have hst := run_nil_elim hrun
      subst hst
      exact hwf
  | cons m ms ih =>
      obtain ⟨S₁, hap, hrest⟩ := run_cons_elim hrun
      exact ih (apply_wf hwf _ _ hap) hrest

/-! ## §2. The climb-out correspondence from the ply conclusion -/

/-- **The ply conclusion IS the correspondence**: if the mirror's board is
the source's, twin-swapped at the cargo `z`, with every other field
equal, then the pair carries `TwinCorr τ_z z.suit` — the field clauses are
immediate, and the per-card stacked-set invariant holds because both twin
suits' rungs sit at or below z's rank at the WF source (the cargos are
seated, hence visible, hence not foundation-passed), so the cross-cases
(z and its flip) are false on both sides. -/
theorem State.twinCorr_of_ply {S M : State} {z : Card}
    (hwf : S.WF)
    (hvisz : S.isVis z = true) (hvisz' : S.isVis (Card.flipSuit z) = true)
    (hboard : M.board = S.board.mapByTwin z)
    (hdeal : M.deal = S.deal) (hheights : M.heights = S.heights)
    (hdepths : M.depths = S.depths) (hstock : M.stock = S.stock)
    (hdraw : M.drawStep = S.drawStep) :
    State.TwinCorr (Card.swapTwin z) z.suit S M := by
  have hρ : Card.IsTwinMap (Card.swapTwin z) := Card.IsTwinMap.swapTwin z
  have hboundz : S.heights z.suit ≤ z.rank.toIdx := by
    cases Nat.lt_or_ge (z.rank.toIdx) (S.heights z.suit) with
    | inl hlt =>
        have hvis := (hwf.founds_gone z hlt).1
        rw [hvis] at hvisz
        exact absurd hvisz (by simp)
    | inr h => exact h
  have hboundz' : S.heights (Card.flipSuit z).suit ≤ z.rank.toIdx := by
    have hrk : (Card.flipSuit z).rank.toIdx = z.rank.toIdx := by
      rw [Card.flipSuit_rank]
    cases Nat.lt_or_ge ((Card.flipSuit z).rank.toIdx) (S.heights (Card.flipSuit z).suit) with
    | inl hlt =>
        have hvis := (hwf.founds_gone (Card.flipSuit z) hlt).1
        rw [hvis] at hvisz'
        exact absurd hvisz' (by simp)
    | inr h => omega
  refine ⟨⟨hρ, ?_, hdeal, hdepths, hstock, hdraw, ?_, ?_⟩, ?_⟩
  · intro c h1 h2
    refine Card.swapTwin_of_ne ?_ ?_
    · intro hcon; rw [hcon] at h1; exact h1 rfl
    · intro hcon; rw [hcon] at h2; exact h2 rfl
  · intro s _ _
    exact congrFun hheights s
  · intro c hon
    rcases hρ.pair c with hc | hc
    · rw [hc, congrFun hheights c.suit]
    · have hcpair : c = z ∨ c = Card.flipSuit z := by
        by_cases h1 : c = z
        · exact Or.inl h1
        · by_cases h2 : c = Card.flipSuit z
          · exact Or.inr h2
          · exfalso
            have hfix := Card.swapTwin_of_ne (t := z) h1 h2
            rw [hfix] at hc
            exact Card.flipSuit_ne c hc.symm
      rcases hcpair with hc2 | hc2
      · rw [hc2] at hc
        rw [hc2, hc, congrFun hheights (Card.flipSuit z).suit, Card.flipSuit_rank]
        constructor <;> intro hlt <;> omega
      · rw [hc2] at hc
        rw [hc2, hc, Card.flipSuit_flipSuit, congrFun hheights z.suit, Card.flipSuit_rank]
        constructor <;> intro hlt <;> omega
  · intro b
    rw [hboard, Board.mapByTwin_eq_mapByRho, Board.mapByRho_topOf]

/-! ## §3. The deep-fit two-ply (route step 2b, the fitting rider) -/

/-- **The deep-fit two-ply** (fithole2's validated statement): at a
riders-cleared licensed state whose first rider `r₁` (the card directly on
`z'`) fits the other cargo `z`, the exchanged game plays the RIDER
TRANSFER `pilePile r₁ (inr z)` — r₁'s run onto the bare `z` — and that
one move lands the mirror at the board-only twin swap of the source; the
ORIGINAL merge then conjugates verbatim (`apply_swapTwinBoard_clean`: a
`pilePile` is clean, `c` and `d` are off the cargo pair), so the two-ply
lands at exactly the twin-swapped merge successor.

The premise form is RUN-SHAPE-FREE: only the moved root `c` and the
landing `d` must be off the cargo pair (`hexc`, `hexd`) — the [H] caller
derives these from the run-passes-twin shape, and the ROOTED caller
([H′], `c = t`) derives them from the license fits and the landing's own
fit — so both bridges share this one ply lemma. -/
theorem State.exchange_merge_ply_deep_fit {S a₁ : State} {t z z' c d r₁ : Card}
    (hwf : S.WF)
    (h₀ : S.board.bottomOf z = some (Sum.inr t))
    (h₀' : S.board.bottomOf z' = some (Sum.inr t.flipSuit))
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.flipSuit = true)
    (hnb : t ∉ S.board.aboveOf z ∧ t.flipSuit ∉ S.board.aboveOf z)
    (hnb' : t ∉ S.board.aboveOf z' ∧ t.flipSuit ∉ S.board.aboveOf z')
    (hrid : S.board.topOf (Sum.inr z) = none)
    (hr₁ : S.board.topOf (Sum.inr z') = some r₁)
    (hfitr : canSitOn r₁ z = true)
    (hstep : S.apply (Move.pilePile c (Sum.inr d)) = some a₁)
    (hexc : c ≠ z ∧ c ≠ z.flipSuit)
    (hexd : d ≠ z ∧ d ≠ z.flipSuit) :
    ∃ M₁ : State, (S.exchangeTwinCargo t).apply (Move.pilePile r₁ (Sum.inr z)) = some M₁ ∧
      M₁.apply (Move.pilePile c (Sum.inr d)) = some (a₁.swapTwinBoard z) := by
  have hztop : S.board.topOf (Sum.inr t) = some z := (Board.bottomOf_eq _ _ _).mp h₀
  have hztop' : S.board.topOf (Sum.inr t.flipSuit) = some z' :=
    (Board.bottomOf_eq _ _ _).mp h₀'
  have hcargo : z' = z.flipSuit := State.cargo_flipSuit hfit hfit' hztop hztop'
  have hzne : z ≠ t ∧ z ≠ t.flipSuit := Card.ne_pair_of_canSitOn hfit
  have hzne' : z' ≠ t ∧ z' ≠ t.flipSuit := by
    obtain ⟨ha, hb⟩ := Card.ne_pair_of_canSitOn hfit'
    exact ⟨by rwa [Card.flipSuit_flipSuit] at hb, ha⟩
  have hzz' : z ≠ z' := by
    intro h
    have h2 : z = z.flipSuit := h.trans hcargo
    exact Card.flipSuit_ne z h2.symm
  have hroff := State.first_rider_off h₀ h₀' hfit' hnb' hr₁
  have hnezz' : (Sum.inr z : Base) ≠ Sum.inr z' := fun h => hzz' (Sum.inr.inj h)
  -- the off-cargo facts, now premise-carried: the [H] caller derives
  -- them from the run-passes-twin shape, the rooted caller from the
  -- license fits and the landing's own fit
  obtain ⟨hcz, hczfs⟩ := hexc
  obtain ⟨hdz, hdzfs⟩ := hexd
  -- §1 the rider transfer fires in the exchanged game
  have hbotr₁ : S.board.bottomOf r₁ = some (Sum.inr z') :=
    (Board.bottomOf_eq _ _ _).mpr hr₁
  have hbotr₁M : (S.exchangeTwinCargo t).board.bottomOf r₁ = some (Sum.inr z') := by
    rw [State.exchangeTwinCargo_board, Board.bottomOf_exchangeTwin, hbotr₁]
    show some (Base.swapTwin t (Sum.inr z')) = _
    rw [Base.swapTwin_eq_self (fun h => hzne'.1 (Sum.inr.inj h))
      (fun h => hzne'.2 (Sum.inr.inj h))]
  have htopzM : (S.exchangeTwinCargo t).board.topOf (Sum.inr z) = none := by
    rw [State.exchangeTwinCargo_board, Board.exchangeTwin_topOf,
      Base.swapTwin_eq_self (fun h => hzne.1 (Sum.inr.inj h))
        (fun h => hzne.2 (Sum.inr.inj h))]
    exact hrid
  have hviszM : (S.exchangeTwinCargo t).isVis z = true := by
    show (((S.exchangeTwinCargo t).board.bottomOf z).isSome) = true
    rw [State.exchangeTwinCargo_board, Board.bottomOf_exchangeTwin, h₀, Option.map_some,
      show Base.swapTwin t (Sum.inr t) = Sum.inr t.flipSuit from by
        show Sum.inr (Card.swapTwin t t) = _
        rw [Card.swapTwin_self_left]]
    rfl
  have hselfM : z ∉ (S.exchangeTwinCargo t).board.aboveOf r₁ :=
    State.exchangeTwin_mirror_guard_zstack hztop hztop' hfit hfit' hnb hnb'
      (Board.mem_aboveOf_of_topOf hr₁)
  have hcmrM : (S.exchangeTwinCargo t).canMoveRun r₁ (Sum.inr z) = true := by
    refine canMoveRun_inr_iff.mpr ⟨canPlace_inr_iff.mpr ⟨htopzM, hviszM, hfitr⟩, ?_⟩
    exact lcontains_false_of_notMem hselfM
  have hfree : ((S.exchangeTwinCargo t).board.detach (Sum.inr z')).topOf (Sum.inr z) = none := by
    rw [Board.detach_topOf_ne _ _ _ hnezz']
    exact htopzM
  have htopz'M : (S.exchangeTwinCargo t).board.topOf (Sum.inr z') = some r₁ := by
    rw [State.exchangeTwinCargo_board, Board.exchangeTwin_topOf,
      Base.swapTwin_eq_self (fun h => hzne'.1 (Sum.inr.inj h))
        (fun h => hzne'.2 (Sum.inr.inj h))]
    exact hr₁
  have hnew : ((S.exchangeTwinCargo t).board.detach (Sum.inr z')).bottomOf r₁ = none :=
    Board.bottomOf_detach_self htopz'M
  have hattex : ∃ bdM : Board, Board.attach
      ((S.exchangeTwinCargo t).board.detach (Sum.inr z')) (Sum.inr z) r₁ = some bdM := by
    have hne : Board.attach ((S.exchangeTwinCargo t).board.detach (Sum.inr z'))
        (Sum.inr z) r₁ ≠ none :=
      (Board.attach_eq_some_iff _ _ _).mpr ⟨hfree, hnew⟩
    cases hattc : Board.attach ((S.exchangeTwinCargo t).board.detach (Sum.inr z'))
        (Sum.inr z) r₁ with
    | none => exact absurd hattc hne
    | some bd => exact ⟨bd, rfl⟩
  obtain ⟨bdM, hattM⟩ := hattex
  refine ⟨{S.exchangeTwinCargo t with board := bdM},
    apply_pilePile_iff.mpr ⟨Sum.inr z', hbotr₁M, hnezz'.symm, hcmrM, bdM, hattM, rfl⟩, ?_⟩
  -- §2 the rider transfer lands the mirror at the twin swap of the source
  have hM₁ : {S.exchangeTwinCargo t with board := bdM} = S.swapTwinBoard z := by
    apply state_ext
    · rfl
    · show bdM = S.board.mapByTwin z
      have htz : t ≠ z := fun h => hzne.1 h.symm
      have htzfs : t ≠ z.flipSuit := fun h => hzne'.1 (h.trans hcargo.symm).symm
      have ht'z : t.flipSuit ≠ z := fun h => hzne.2 h.symm
      have ht'zfs : t.flipSuit ≠ z.flipSuit := fun h => hzne'.2 (h.trans hcargo.symm).symm
      apply Board.ext_topOf
      funext b
      rw [mapByTwin_topOf]
      by_cases hbz : b = Sum.inr z
      · rw [hbz, Board.attach_topOf _ _ _ hattM,
        show Base.swapTwin z (Sum.inr z) = Sum.inr z' from by
          show Sum.inr (Card.swapTwin z z) = _
          rw [Card.swapTwin_self_left, hcargo],
        hr₁]
        show some r₁ = some (Card.swapTwin z r₁)
        rw [Card.swapTwin_of_ne hroff.1 (fun h => hroff.2.1 (h.trans hcargo.symm))]
      · by_cases hbz' : b = Sum.inr z'
        · rw [hbz',
          Board.attach_topOf_ne _ _ _ hattM hnezz'.symm,
          Board.detach_topOf,
          show Base.swapTwin z (Sum.inr z') = Sum.inr z from by
            show Sum.inr (Card.swapTwin z z') = _
            rw [hcargo, Card.swapTwin_self_right],
          hrid]
          rfl
        · have hL : bdM.topOf b = S.board.topOf (b.swapTwin t) := by
            rw [Board.attach_topOf_ne _ _ _ hattM (fun h => hbz h),
              Board.detach_topOf_ne _ _ _ (fun h => hbz' h),
              State.exchangeTwinCargo_board, Board.exchangeTwin_topOf]
          rw [hL]
          by_cases hbt : b = Sum.inr t
          · rw [hbt,
            show Base.swapTwin t (Sum.inr t) = Sum.inr t.flipSuit from by
              show Sum.inr (Card.swapTwin t t) = _
              rw [Card.swapTwin_self_left],
            hztop',
            show Base.swapTwin z (Sum.inr t) = Sum.inr t from by
              show Sum.inr (Card.swapTwin z t) = _
              rw [Card.swapTwin_of_ne htz htzfs],
            hztop]
            show some z' = some (Card.swapTwin z z)
            rw [Card.swapTwin_self_left, ← hcargo]
          · by_cases hbt' : b = Sum.inr t.flipSuit
            · rw [hbt',
              show Base.swapTwin t (Sum.inr t.flipSuit) = Sum.inr t from by
                show Sum.inr (Card.swapTwin t t.flipSuit) = _
                rw [Card.swapTwin_self_right],
              hztop,
              show Base.swapTwin z (Sum.inr t.flipSuit) = Sum.inr t.flipSuit from by
                show Sum.inr (Card.swapTwin z t.flipSuit) = _
                rw [Card.swapTwin_of_ne ht'z ht'zfs],
              hztop']
              show some z = some (Card.swapTwin z z')
              rw [hcargo, Card.swapTwin_self_right]
            · rw [Base.swapTwin_eq_self hbt hbt',
              Base.swapTwin_eq_self hbz
                (fun h => hbz' (h.trans (congrArg Sum.inr hcargo.symm)))]
              cases hval : S.board.topOf b with
              | none => rfl
              | some v =>
                  have hvz : v ≠ z := by
                    intro hcon
                    rw [hcon] at hval
                    exact hbt (S.board.inj b (Sum.inr t) z hval hztop)
                  have hvz' : v ≠ z' := by
                    intro hcon
                    rw [hcon] at hval
                    exact hbt' (S.board.inj b (Sum.inr t.flipSuit) z' hval hztop')
                  show some v = Option.map z.swapTwin (some v)
                  show some v = some (Card.swapTwin z v)
                  rw [Card.swapTwin_of_ne hvz (fun h => hvz' (h.trans hcargo.symm))]
    · rfl
    · rfl
    · rfl
    · rfl
  rw [hM₁]
  -- §3 the merge conjugates verbatim at the twin-swapped board
  have hvisz : S.isVis z = true := by
    show (S.board.bottomOf z).isSome = true
    rw [h₀]
    rfl
  have hvisz' : S.isVis z.flipSuit = true := by
    show (S.board.bottomOf (Card.flipSuit z)).isSome = true
    rw [← hcargo, h₀']
    rfl
  have hhid : ∀ a, z ∉ S.hidden a ∧ z.flipSuit ∉ S.hidden a := by
    intro a
    constructor
    · intro hmem
      exact hwf.vis_not_hidden z hvisz a hmem
    · intro hmem
      exact hwf.vis_not_hidden z.flipSuit hvisz' a hmem
  have hstock : z ∉ S.stock.cards ∧ z.flipSuit ∉ S.stock.cards := by
    constructor
    · intro hmem
      have hpm := Cycle.posOf_mem hmem
      rw [hwf.vis_off_cycle z hvisz] at hpm
      exact absurd hpm (by simp)
    · intro hmem
      have hpm := Cycle.posOf_mem hmem
      rw [hwf.vis_off_cycle z.flipSuit hvisz'] at hpm
      exact absurd hpm (by simp)
  have hm : (Move.pilePile c (Sum.inr d)).swapTwin z = Move.pilePile c (Sum.inr d) := by
    simp only [Move.swapTwin]
    rw [Card.swapTwin_of_ne hcz hczfs,
      Base.swapTwin_eq_self (fun h => hdz (Sum.inr.inj h))
        (fun h => hdzfs (Sum.inr.inj h))]
  have hconj := State.apply_swapTwinBoard_clean (z := z) (S := S) (R := a₁)
    (m := Move.pilePile c (Sum.inr d)) hhid hstock rfl hstep
  rw [hm] at hconj
  exact hconj

/-! ## §4. The two named normalization premises, and the clearing kit -/

/-- **The clean-move condition for the clearing prefix π₀**: a `pileStack
q` with q off the protected zone — the twin pair {t, t'}, both cargos
{z, z'}, the merge root c, and the first rider r₁.  This is the
witnesses' clearing shape (the off-pair foundation stack that frees a
blocked detour base — `pileStack ♥10` at both detour.lean and
detour2.lean), and it is exactly what the bridge's replay machinery
consumes: the step kit mirrors such a stack
(`exchangeTwinCargo_step_pileStack` — the guards are frame-inherited),
and the invariant transfer (`twinLicensedAt_apply_pileStack` below)
preserves the pinned license, z's bareness, and r₁'s ridership on z'
— the detach at q's own base is off every protected seat (each hosts
another card, or — z — is bare, and both exclude q).  The condition is
STATE-FREE by design: the per-move mirror premises are license bits,
carried as run-invariants by `exchangeTwinCargo_run_cleanAt` rather
than re-checked per move.  The residue: richer clearing kinds (draws,
reveals, other runs' detours) would extend the kit — the witnesses need
none. -/
def State.CleanAt (m : Move) (t z z' c r₁ : Card) : Prop :=
  ∃ q : Card, m = Move.pileStack q ∧
    q ≠ t ∧ q ≠ t.flipSuit ∧ q ≠ z ∧ q ≠ z' ∧ q ≠ c ∧ q ≠ r₁

/-- **The clearing step's invariant transfer**: a `CleanAt` `pileStack q`
at an invariant-carrying state preserves the pinned license, z's
bareness, and r₁'s ridership on z' — the board only loses q (the detach
at q's own base, off every protected seat: the twin seats host the
cargos, z is bare, z' hosts r₁), and the no-braid walks only shrink. -/
theorem State.twinLicensedAt_apply_pileStack {st a₁ : State} {t z z' r₁ q : Card}
    (hlic : State.TwinLicensedAt st t z z')
    (hz : st.board.topOf (Sum.inr z) = none)
    (hr₁ : st.board.topOf (Sum.inr z') = some r₁)
    (hq : q ≠ t ∧ q ≠ t.flipSuit ∧ q ≠ z ∧ q ≠ z' ∧ q ≠ r₁)
    (hstep : st.apply (Move.pileStack q) = some a₁) :
    State.TwinLicensedAt a₁ t z z' ∧
      a₁.board.topOf (Sum.inr z) = none ∧
      a₁.board.topOf (Sum.inr z') = some r₁ := by
  obtain ⟨hvis, hvis', h₀, h₀', hfit, hfit', hnb, hnb'⟩ := hlic
  obtain ⟨hqt, hqt', hqz, hqz', hqr₁⟩ := hq
  have hztop : st.board.topOf (Sum.inr t) = some z := (Board.bottomOf_eq _ _ _).mp h₀
  have hztop' : st.board.topOf (Sum.inr t.flipSuit) = some z' :=
    (Board.bottomOf_eq _ _ _).mp h₀'
  have happ := hstep
  rw [apply_pileStack_iff] at happ
  obtain ⟨htop, b, hb, hrk, rfl⟩ := happ
  have hbtopq : st.board.topOf b = some q := (Board.bottomOf_eq st.board q b).mp hb
  have hbt : b ≠ Sum.inr t := by
    intro hcon
    rw [hcon] at hbtopq
    exact hqz (Option.some.inj (hbtopq.symm.trans hztop))
  have hbt' : b ≠ Sum.inr t.flipSuit := by
    intro hcon
    rw [hcon] at hbtopq
    exact hqz' (Option.some.inj (hbtopq.symm.trans hztop'))
  have hbz : b ≠ Sum.inr z := by
    intro hcon
    rw [hcon] at hbtopq
    exact absurd hbtopq (by rw [hz]; simp)
  have hbz' : b ≠ Sum.inr z' := by
    intro hcon
    rw [hcon] at hbtopq
    exact hqr₁ (Option.some.inj (hbtopq.symm.trans hr₁))
  refine ⟨⟨?_, ?_, ?_, ?_, hfit, hfit', ?_, ?_⟩, ?_, ?_⟩
  · show ((st.board.detach b).bottomOf t).isSome = true
    rw [bottomOf_detach_ne hbtopq (fun h => hqt h.symm)]
    exact hvis
  · show ((st.board.detach b).bottomOf t.flipSuit).isSome = true
    rw [bottomOf_detach_ne hbtopq (fun h => hqt' h.symm)]
    exact hvis'
  · show (st.board.detach b).bottomOf z = some (Sum.inr t)
    rw [bottomOf_detach_ne hbtopq (fun h => hqz h.symm)]
    exact h₀
  · show (st.board.detach b).bottomOf z' = some (Sum.inr t.flipSuit)
    rw [bottomOf_detach_ne hbtopq (fun h => hqz' h.symm)]
    exact h₀'
  · show t ∉ (st.board.detach b).aboveOf z ∧ t.flipSuit ∉ (st.board.detach b).aboveOf z
    constructor
    · intro hmem
      exact hnb.1 (Board.aboveOf_sub_detach 52 z [] t hmem)
    · intro hmem
      exact hnb.2 (Board.aboveOf_sub_detach 52 z [] t.flipSuit hmem)
  · show t ∉ (st.board.detach b).aboveOf z' ∧ t.flipSuit ∉ (st.board.detach b).aboveOf z'
    constructor
    · intro hmem
      exact hnb'.1 (Board.aboveOf_sub_detach 52 z' [] t hmem)
    · intro hmem
      exact hnb'.2 (Board.aboveOf_sub_detach 52 z' [] t.flipSuit hmem)
  · show (st.board.detach b).topOf (Sum.inr z) = none
    rw [Board.detach_topOf_ne _ _ _ hbz.symm]
    exact hz
  · show (st.board.detach b).topOf (Sum.inr z') = some r₁
    rw [Board.detach_topOf_ne _ _ _ hbz'.symm]
    exact hr₁

/-- **The run-level clean replay**: a `CleanAt` clearing prefix replays
verbatim in the exchanged game (the successors staying exchanged), the
three invariants — the pinned license, z's bareness, r₁'s ridership on
z' — riding to the prefix's end state.  The induction consumes the step
kit's `pileStack` mirror lemma and the invariant transfer above. -/
theorem State.exchangeTwinCargo_run_cleanAt {st st' : State} {t z z' c r₁ : Card}
    {π₀ : List Move}
    (hlic : State.TwinLicensedAt st t z z')
    (hz : st.board.topOf (Sum.inr z) = none)
    (hr₁ : st.board.topOf (Sum.inr z') = some r₁)
    (hclean : ∀ m ∈ π₀, State.CleanAt m t z z' c r₁)
    (hrun : st.run π₀ = some st') :
    (st.exchangeTwinCargo t).run π₀ = some (st'.exchangeTwinCargo t) ∧
      State.TwinLicensedAt st' t z z' ∧
      st'.board.topOf (Sum.inr z) = none ∧
      st'.board.topOf (Sum.inr z') = some r₁ := by
  induction π₀ generalizing st st' with
  | nil =>
      have hst := run_nil_elim hrun
      subst hst
      exact ⟨rfl, hlic, hz, hr₁⟩
  | cons m ms ih =>
      obtain ⟨q, rfl, hqt, hqt', hqz, hqz', -, hqr₁⟩ := hclean m (by simp)
      obtain ⟨S₁, hap, hrest⟩ := run_cons_elim hrun
      obtain ⟨hlic₁, hz₁, hr₁₁⟩ :=
        State.twinLicensedAt_apply_pileStack hlic hz hr₁ ⟨hqt, hqt', hqz, hqz', hqr₁⟩ hap
      obtain ⟨hvis, hvis', h₀, h₀', hfit, hfit', hnb, hnb'⟩ := hlic
      have hfire : (st.exchangeTwinCargo t).apply (Move.pileStack q)
          = some (S₁.exchangeTwinCargo t) :=
        State.exchangeTwinCargo_step_pileStack h₀ h₀' ⟨hqz, hqz'⟩ ⟨hqt, hqt'⟩ hap
      obtain ⟨hrunX, hlic', hz', hr₁'⟩ :=
        ih hlic₁ hz₁ hr₁₁ (fun m' hm' => hclean m' (List.mem_cons_of_mem _ hm')) hrest
      exact ⟨run_cons_intro hfire hrunX, hlic', hz', hr₁'⟩

/-- **The rider-prefix normalization premise** (route step 1, the honest
boundary): the source's winning line can be scheduled so that a prefix π₁
clears z's riders BEFORE the merge — reaching a state S₀ at which the
license still holds pinned, z is bare, the run still passes t, the SAME
merge move re-fires with a solvable successor, and the landing is on the
z'-side — and π₁ replays verbatim in the exchanged game (the successors
staying exchanged).  Premise-free this needs the source-side commutation
`[merge; π₁] ≈ [π₁; merge]` (an L1/O3-shaped play normalization) and the
prefix's exchange-cleanliness — the residue for a later session. -/
def State.ExchangeRiderPrefix (st : State) (t z z' c : Card) (b : Base) : Prop :=
  ∃ (π₁ : List Move) (S₀ : State),
    st.run π₁ = some S₀ ∧
    (st.exchangeTwinCargo t).run π₁ = some (S₀.exchangeTwinCargo t) ∧
    S₀.WF ∧ State.TwinLicensedAt S₀ t z z' ∧
    S₀.board.topOf (Sum.inr z) = none ∧
    t ∈ S₀.board.aboveOf c ∧
    (∃ a₁' : State, S₀.apply (Move.pilePile c b) = some a₁' ∧ a₁'.solvableFrom) ∧
    (∃ d, b = Sum.inr d ∧
      (d = z ∨ d ∈ S₀.board.aboveOf z ∨ d = z' ∨ d ∈ S₀.board.aboveOf z'))

/-- **The deep-landing normalization premise, ITERATED form** (route step
2b-deep, the fit hole): at a licensed WF riders-cleared merge-shaped
state whose first rider r₁ (directly on z') fits NEITHER cargo, a CLEAN
CLEARING PREFIX π₀ (each member a `CleanAt` move) reaches a state at
which the rider run has a legal detach `pilePile r₁ β` whose follow-up
merge (the same move) still fires with a solvable successor.

The plain single-detach form (∃ β, the detach at the given state) is
FALSE at WF — two independent witnesses (detour.lean, detour2.lean)
satisfy every hypothesis while NO detach base exists: (1) r₁ = ♣J, a
non-king whose candidate tops {♥Q, ♦Q} are both occupied (the merge
root's own run; a deal-adjacent blocker), with the one free anchor
closed by `canPlace`'s king guard; (2) r₁ = ♥K, a king, with ALL SEVEN
anchors occupied by `founds_gone`-legal fillers.  The iterated repair is
validated at both witnesses: the clearing stack (pileStack ♥10 at both)
frees the blocked base, then the detach, then the SAME merge — the four
plays (playIter/playIterX, playIter2/playIter2X) win on BOTH sides,
heights [13,13,13,13] (the probes' #evals).

The honest residue: the `S₂.solvableFrom` conjunct is NOT structurally
free (two breaking channels exist in principle: the detour occupying a
base the original line needs; an e-inversion stalling a suit) — no
witness for either channel was found (detour3.lean: the detour is
structurally harmless to the merge's premises — it cannot land inside
c's run, the hole killing exactly the one bare card z; it empties z′'s
stack making the no-braids trivial; d rides along still bare; the
self-landing guard survives), so the conjunct stays inside the premise. -/
def State.ExchangeDeepNorm (t z z' c : Card) (b : Base) : Prop :=
  ∀ {S A : State} {r₁ : Card},
    S.WF → State.TwinLicensedAt S t z z' →
    S.board.topOf (Sum.inr z) = none →
    t ∈ S.board.aboveOf c →
    S.board.topOf (Sum.inr z') = some r₁ → canSitOn r₁ z = false →
    S.apply (Move.pilePile c b) = some A → A.solvableFrom →
    ∃ (π₀ : List Move) (S₀' : State) (β : Base) (S₁ S₂ : State),
      S.run π₀ = some S₀' ∧
      (∀ m ∈ π₀, State.CleanAt m t z z' c r₁) ∧
      S₀'.apply (Move.pilePile r₁ β) = some S₁ ∧
      S₁.apply (Move.pilePile c b) = some S₂ ∧
      S₂.solvableFrom

/-! ## §5. The assembly at a riders-cleared state -/

/-- **The merge bridge, cleared form**: at a licensed WF state whose z is
bare (riders-cleared), the merge move (whose run passes t, landing on the
z'-side) transfers solvability to the exchanged state — modulo the window
(`hwin`) and the deep normalization (`hdet`).  The route: the landing
case analysis (the own-cargo side is self-landing at the source, so only
the z'-side is live), the ply (ROOT: `exchange_merge_ply_root`; DEEP+FIT:
`exchange_merge_ply_deep_fit`; DEEP+HOLE: hdet's ITERATED detour — the
CleanAt clearing prefix π₀ first, replayed in the exchange by the
run-level clean-replay lemma with the license/z-bareness/r₁-ridership
invariants riding to its end state, then the detach replayed by the
clean-run mirror step, then the merge as a passing move in both games,
with the seat-exchanged result equal to the twin swap by the preserved
covers), the correspondence (`twinCorr_of_ply`), the climb-out (`hwin`),
and the explicit play composition (`solvable_step` + `run_append_some`). -/
theorem State.solvable_of_exchange_merge_cleared {st a₁ : State} {t z z' c : Card} {b : Base}
    (hwin : ∀ {S M : State} {u : Card}, State.TwinCorr (Card.swapTwin u) u.suit S M →
      S.WF → S.solvableFrom → M.solvableFrom)
    (hdet : State.ExchangeDeepNorm t z z' c b)
    (hwf : st.WF) (hlic : st.TwinLicensedAt t z z')
    (hrid : st.board.topOf (Sum.inr z) = none)
    (hstep : st.apply (Move.pilePile c b) = some a₁)
    (hmerge : t ∈ st.board.aboveOf c)
    (hland : ∃ d, b = Sum.inr d ∧
      (d = z ∨ d ∈ st.board.aboveOf z ∨ d = z' ∨ d ∈ st.board.aboveOf z'))
    (hsol : a₁.solvableFrom) :
    (st.exchangeTwinCargo t).solvableFrom := by
  obtain ⟨hvis, hvis', h₀, h₀', hfit, hfit', hnb, hnb'⟩ := hlic
  have hztop : st.board.topOf (Sum.inr t) = some z := (Board.bottomOf_eq _ _ _).mp h₀
  have hztop' : st.board.topOf (Sum.inr t.flipSuit) = some z' :=
    (Board.bottomOf_eq _ _ _).mp h₀'
  have hcargo : z' = z.flipSuit := State.cargo_flipSuit hfit hfit' hztop hztop'
  have hzne : z ≠ t ∧ z ≠ t.flipSuit := Card.ne_pair_of_canSitOn hfit
  have hzz' : z ≠ z' := by
    intro h
    have h2 : z = z.flipSuit := h.trans hcargo
    exact Card.flipSuit_ne z h2.symm
  -- the source's self-landing guard (from the merge's own firing)
  have hguard : ∀ {d : Card}, b = Sum.inr d → d ∉ st.board.aboveOf c := by
    intro d hd hmem
    have happ := hstep
    rw [apply_pilePile_iff] at happ
    obtain ⟨-, -, -, hcmr, -, -, -⟩ := happ
    rw [hd] at hcmr
    have hfalse := (canMoveRun_inr_iff.mp hcmr).2
    rw [List.contains_iff_mem.mpr hmem] at hfalse
    exact absurd hfalse (by simp)
  obtain ⟨d, hbd, hld⟩ := hland
  -- the own-cargo side of the landing is self-landing at the source
  have hown : d = z ∨ d ∈ st.board.aboveOf z → False := fun h =>
    State.merge_own_landing_absurd hztop hmerge (hguard hbd) h
  have hlive : d = z' ∨ d ∈ st.board.aboveOf z' := by
    rcases hld with h | h | h | h
    · exact (hown (Or.inl h)).elim
    · exact (hown (Or.inr h)).elim
    · exact Or.inl h
    · exact Or.inr h
  -- c is off the twin pair: c = t dies on the bare cover (the walk from t
  -- is exactly [z]); c = t' dies on the guard (the landing rides t''s run)
  have hcovt : st.board.aboveOf t = [z] := Board.aboveOf_cover_bare hztop hrid
  have hct : c ≠ t ∧ c ≠ t.flipSuit := by
    constructor
    · intro hcon
      have hm := hmerge
      rw [hcon, hcovt] at hm
      have hz : t = z := List.mem_singleton.mp hm
      rw [← hz] at hztop hrid
      exact absurd (hztop.symm.trans hrid) (by simp)
    · intro hcon
      have hg : d ∉ st.board.aboveOf t.flipSuit := by
        rw [← hcon]
        exact hguard hbd
      rcases hlive with h | h
      · exact hg (by rw [h]; exact Board.mem_aboveOf_of_topOf hztop')
      · exact hg (Board.aboveOf_trans (Board.mem_aboveOf_of_topOf hztop') h)
  have hc : c ≠ z ∧ c ≠ z' := by
    constructor
    · intro hcon
      have hm := hmerge
      rw [hcon] at hm
      exact hnb.1 hm
    · intro hcon
      have hm := hmerge
      rw [hcon] at hm
      exact hnb'.1 hm
  have hdz : d ≠ z := by
    intro hcon
    have hzin : z ∈ st.board.aboveOf c :=
      Board.aboveOf_trans hmerge (Board.mem_aboveOf_of_topOf hztop)
    rw [← hcon] at hzin
    exact hguard hbd hzin
  -- the merge successor keeps both cargos seated (the base preservation)
  have hbz₁ : a₁.board.bottomOf z = some (Sum.inr t) :=
    (State.apply_pilePile_bottomOf hstep (Ne.symm hc.1)).trans h₀
  have hbz₁' : a₁.board.bottomOf z' = some (Sum.inr t.flipSuit) :=
    (State.apply_pilePile_bottomOf hstep (Ne.symm hc.2)).trans h₀'
  have hvisz : a₁.isVis z = true := by
    show (a₁.board.bottomOf z).isSome = true
    rw [hbz₁]
    rfl
  have hvisz' : a₁.isVis (Card.flipSuit z) = true := by
    show (a₁.board.bottomOf (Card.flipSuit z)).isSome = true
    rw [← hcargo, hbz₁']
    rfl
  by_cases hdne : d = z'
  · -- ROOT (d = z'): the mirror merge, the proven ply
    have hstepr : st.apply (Move.pilePile c (Sum.inr z')) = some a₁ := by
      rw [← hdne, ← hbd]
      exact hstep
    obtain ⟨M', hfire, hboard, hdeal, hheights, hdepths, hstock, hdraw⟩ :=
      State.exchange_merge_ply_root hztop hztop' hfit hfit' hnb hnb' hmerge hct hrid hstepr
    have hcorr := State.twinCorr_of_ply (apply_wf hwf _ _ hstep) hvisz hvisz'
      hboard hdeal hheights hdepths hstock hdraw
    exact State.solvable_step hfire (hwin hcorr (apply_wf hwf _ _ hstep) hsol)
  · -- DEEP (d ∈ aboveOf z', d ≠ z')
    have hdeep : d ∈ st.board.aboveOf z' := by
      rcases hld with h | h | h | h
      · exact (hown (Or.inl h)).elim
      · exact (hown (Or.inr h)).elim
      · exact absurd h hdne
      · exact h
    cases htopz' : st.board.topOf (Sum.inr z') with
    | none => exact absurd hdeep (by rw [Board.aboveOf_step_none htopz']; simp)
    | some r₁ =>
      by_cases hfitr : canSitOn r₁ z = true
      · -- DEEP + FIT: the two-ply
        have hstepr : st.apply (Move.pilePile c (Sum.inr d)) = some a₁ := by
          rw [← hbd]
          exact hstep
        obtain ⟨M₁, hfire₁, hfire₂⟩ :=
          State.exchange_merge_ply_deep_fit hwf h₀ h₀' hfit hfit' hnb hnb' hrid
            htopz' hfitr hstepr ⟨hc.1, fun h => hc.2 (h.trans hcargo.symm)⟩
            ⟨hdz, fun h => hdne (h.trans hcargo.symm)⟩
        have hcorr := State.twinCorr_of_ply (apply_wf hwf _ _ hstep) hvisz hvisz'
          (State.swapTwinBoard_board z a₁) (State.swapTwinBoard_deal z a₁)
          (State.swapTwinBoard_heights z a₁) (State.swapTwinBoard_depths z a₁)
          (State.swapTwinBoard_stock z a₁) rfl
        exact State.solvable_step hfire₁ (State.solvable_step hfire₂
          (hwin hcorr (apply_wf hwf _ _ hstep) hsol))
      · -- DEEP + HOLE: the iterated detour (hdet) — the clean clearing
        -- prefix π₀ first, then the detach, then the passing merge
        have hfitrf : canSitOn r₁ z = false := by
          cases hf : canSitOn r₁ z with
          | false => rfl
          | true => exact absurd hf hfitr
        obtain ⟨π₀, S₀', β, S₁, S₂, hrunπ₀, hcleanπ₀, hdetour, hmerge₁, hsol₂⟩ :=
          hdet hwf ⟨hvis, hvis', h₀, h₀', hfit, hfit', hnb, hnb'⟩ hrid hmerge htopz'
            hfitrf hstep hsol
        -- the mirror replays the clearing prefix verbatim (the run-level
        -- clean-replay lemma), the invariants riding to S₀'
        obtain ⟨hrunπ₀X, hlic₀, hrid₀, htopz'₀⟩ :=
          State.exchangeTwinCargo_run_cleanAt
            ⟨hvis, hvis', h₀, h₀', hfit, hfit', hnb, hnb'⟩ hrid htopz' hcleanπ₀ hrunπ₀
        obtain ⟨hvis, hvis', h₀, h₀', hfit, hfit', hnb, hnb'⟩ := hlic₀
        have hztop : S₀'.board.topOf (Sum.inr t) = some z :=
          (Board.bottomOf_eq _ _ _).mp h₀
        have hztop' : S₀'.board.topOf (Sum.inr t.flipSuit) = some z' :=
          (Board.bottomOf_eq _ _ _).mp h₀'
        -- the detour's landing is off the twin seats and the cargo seats
        have hroff := State.first_rider_off h₀ h₀' hfit' hnb' htopz'₀
        have hdapp := hdetour
        rw [apply_pilePile_iff] at hdapp
        obtain ⟨β₀', hbotr₁', -, hcmrβ, bdd, hattβ, rfl⟩ := hdapp
        have hcpβ : S₀'.canPlace r₁ β = true := by
          simp only [State.canMoveRun, Bool.and_eq_true_iff] at hcmrβ
          exact hcmrβ.1
        have hfreeβ : S₀'.board.topOf β = none := topOf_of_canPlace hcpβ
        have hβz : β ≠ Sum.inr z := by
          intro hcon
          rw [hcon] at hcpβ
          have hfit2 := (canPlace_inr_iff.mp hcpβ).2.2
          rw [hfit2] at hfitr
          exact absurd hfitr (by simp)
        have hβz' : β ≠ Sum.inr z' := by
          intro hcon
          rw [hcon] at hfreeβ
          rw [hfreeβ] at htopz'₀
          exact absurd htopz'₀ (by simp)
        have hβt : β ≠ Sum.inr t := by
          intro hcon
          rw [hcon] at hfreeβ
          rw [hfreeβ] at hztop
          exact absurd hztop (by simp)
        have hβt' : β ≠ Sum.inr t.flipSuit := by
          intro hcon
          rw [hcon] at hfreeβ
          rw [hfreeβ] at hztop'
          exact absurd hztop' (by simp)
        have hbotr₁st : S₀'.board.bottomOf r₁ = some (Sum.inr z') :=
          (Board.bottomOf_eq _ _ _).mpr htopz'₀
        have hβ₀' : β₀' = Sum.inr z' :=
          (Option.some.inj (hbotr₁st.symm.trans hbotr₁')).symm
        have hzsz' : (Sum.inr z : Base) ≠ β₀' := by
          rw [hβ₀']
          exact fun h => hzz' (Sum.inr.inj h)
        have htopz₁ : {S₀' with board := bdd}.board.topOf (Sum.inr z) = none := by
          show bdd.topOf (Sum.inr z) = none
          rw [Board.attach_topOf_ne _ _ _ hattβ hβz.symm, Board.detach_topOf_ne _ _ _ hzsz']
          exact hrid₀
        have htopz'₁ : {S₀' with board := bdd}.board.topOf (Sum.inr z') = none := by
          show bdd.topOf (Sum.inr z') = none
          rw [Board.attach_topOf_ne _ _ _ hattβ hβz'.symm, hβ₀', Board.detach_topOf]
        have hemptyz : {S₀' with board := bdd}.board.aboveOf z = [] :=
          Board.aboveOf_step_none htopz₁
        have hemptyz' : {S₀' with board := bdd}.board.aboveOf z' = [] :=
          Board.aboveOf_step_none htopz'₁
        -- the license survives the detour at the pinned pair (both stacks
        -- are empty: z was bare, and the detach emptied z')
        have hbz₁ : {S₀' with board := bdd}.board.bottomOf z = some (Sum.inr t) :=
          (State.apply_pilePile_bottomOf hdetour (Ne.symm hroff.1)).trans h₀
        have hbz₁' : {S₀' with board := bdd}.board.bottomOf z' =
            some (Sum.inr t.flipSuit) :=
          (State.apply_pilePile_bottomOf hdetour (Ne.symm hroff.2.1)).trans h₀'
        have hnb₁ : t ∉ {S₀' with board := bdd}.board.aboveOf z ∧
            t.flipSuit ∉ {S₀' with board := bdd}.board.aboveOf z := by
          rw [hemptyz]
          exact ⟨fun h => absurd h (by simp), fun h => absurd h (by simp)⟩
        have hnb₁' : t ∉ {S₀' with board := bdd}.board.aboveOf z' ∧
            t.flipSuit ∉ {S₀' with board := bdd}.board.aboveOf z' := by
          rw [hemptyz']
          exact ⟨fun h => absurd h (by simp), fun h => absurd h (by simp)⟩
        -- the mirror replays the detour (the clean-run mirror step)
        have hcleanr : t ∉ S₀'.board.aboveOf r₁ ∧ t.flipSuit ∉ S₀'.board.aboveOf r₁ := by
          constructor
          · intro hmem
            exact hnb'.1 (Board.aboveOf_trans (Board.mem_aboveOf_of_topOf htopz'₀) hmem)
          · intro hmem
            exact hnb'.2 (Board.aboveOf_trans (Board.mem_aboveOf_of_topOf htopz'₀) hmem)
        have hfireD : (S₀'.exchangeTwinCargo t).apply (Move.pilePile r₁ β)
            = some ({S₀' with board := bdd}.exchangeTwinCargo t) :=
          State.exchangeTwinCargo_step_pilePile h₀ h₀' ⟨hroff.1, hroff.2.1⟩
            ⟨hroff.2.2.1, hroff.2.2.2⟩ hcleanr hdetour
        -- the merge is a passing move in both games
        have hoff : ∀ d', b = Sum.inr d' →
            d' ≠ z ∧ d' ≠ z' ∧
            d' ∉ {S₀' with board := bdd}.board.aboveOf z ∧
            d' ∉ {S₀' with board := bdd}.board.aboveOf z' := by
          intro d' hd'
          have hdeq : d' = d := Sum.inr.inj (hd'.symm.trans hbd)
          rw [hdeq]
          exact ⟨hdz, hdne, fun h => absurd h (by rw [hemptyz]; simp),
            fun h => absurd h (by rw [hemptyz']; simp)⟩
        have hfireM : ({S₀' with board := bdd}.exchangeTwinCargo t).apply (Move.pilePile c b)
            = some (S₂.exchangeTwinCargo t) :=
          State.exchangeTwinCargo_step_pilePile_passing hbz₁ hbz₁' hfit hfit' hnb₁ hnb₁'
            hc hoff hmerge₁
        -- the covers survive, so the seat exchange IS the twin swap
        have hbz₂ : S₂.board.bottomOf z = some (Sum.inr t) :=
          (State.apply_pilePile_bottomOf hmerge₁ (Ne.symm hc.1)).trans hbz₁
        have hbz₂' : S₂.board.bottomOf z' = some (Sum.inr t.flipSuit) :=
          (State.apply_pilePile_bottomOf hmerge₁ (Ne.symm hc.2)).trans hbz₁'
        have hcovert : S₂.board.topOf (Sum.inr t) = some z :=
          (Board.bottomOf_eq _ _ _).mp hbz₂
        have hcovert' : S₂.board.topOf (Sum.inr t.flipSuit) = some z' :=
          (Board.bottomOf_eq _ _ _).mp hbz₂'
        have hnezsz : (Sum.inr z : Base) ≠ b := fun h =>
          hdz (Sum.inr.inj (h.trans hbd)).symm
        have hnezsz' : (Sum.inr z' : Base) ≠ b := fun h =>
          hdne (Sum.inr.inj (h.trans hbd)).symm
        have hdapp₂ := hmerge₁
        rw [apply_pilePile_iff] at hdapp₂
        obtain ⟨βc, hbotc₁, -, -, bd₂, hatt₂, hst₂⟩ := hdapp₂
        have hβcz : βc ≠ Sum.inr z := by
          intro hcon
          rw [hcon] at hbotc₁
          rw [(Board.bottomOf_eq _ _ _).mp hbotc₁] at htopz₁
          exact absurd htopz₁ (by simp)
        have hβcz' : βc ≠ Sum.inr z' := by
          intro hcon
          rw [hcon] at hbotc₁
          rw [(Board.bottomOf_eq _ _ _).mp hbotc₁] at htopz'₁
          exact absurd htopz'₁ (by simp)
        have htopz₂ : S₂.board.topOf (Sum.inr z) = none :=
          (State.apply_pilePile_topOf hmerge₁ hbotc₁ hnezsz hβcz.symm).trans htopz₁
        have htopz₂' : S₂.board.topOf (Sum.inr z') = none :=
          (State.apply_pilePile_topOf hmerge₁ hbotc₁ hnezsz' hβcz'.symm).trans htopz'₁
        have hboardM : (S₂.exchangeTwinCargo t).board = S₂.board.mapByTwin z := by
          rw [State.exchangeTwinCargo_board,
            Board.exchangeTwin_eq_mapByTwin_of_covers hcovert hcovert' hcargo hzne
              ⟨htopz₂, htopz₂'⟩]
        have hvisz₂ : S₂.isVis z = true := by
          show (S₂.board.bottomOf z).isSome = true
          rw [hbz₂]
          rfl
        have hvisz₂' : S₂.isVis (Card.flipSuit z) = true := by
          show (S₂.board.bottomOf (Card.flipSuit z)).isSome = true
          rw [← hcargo, hbz₂']
          rfl
        have hwf₂ : S₂.WF :=
          apply_wf (apply_wf (State.wf_run hwf hrunπ₀) _ _ hdetour) _ _ hmerge₁
        have hcorr := State.twinCorr_of_ply hwf₂ hvisz₂ hvisz₂'
          hboardM (State.exchangeTwinCargo_deal S₂ t) (State.exchangeTwinCargo_heights S₂ t)
          (State.exchangeTwinCargo_depths S₂ t) (State.exchangeTwinCargo_stock S₂ t)
          (State.exchangeTwinCargo_drawStep S₂ t)
        obtain ⟨π', W, hrun', hwin'⟩ := hwin hcorr hwf₂ hsol₂
        exact ⟨π₀ ++ (Move.pilePile r₁ β :: Move.pilePile c b :: π'), W,
          run_append_some hrunπ₀X (run_cons_intro hfireD (run_cons_intro hfireM hrun')),
          hwin'⟩

/-! ## §6. The [H]-shaped bridges -/

/-- **The merge bridge, scaffolded** — [H] modulo three named premises:
the window (`hwin`, the climb-out replay), the rider-prefix normalization
(`hrp`), and the ITERATED deep-landing normalization (`hdet`: the
`CleanAt` clearing prefix, then the detach, then the solvable
follow-up).  The fixed
premises `_hwf _h _hstep _hmerge _hland _hsol` are the [H] shape at the
pinned cargo pair (kept for signature fidelity, `_`-prefixed because the
assembly itself runs at the cleared state `S₀` that `hrp` provides — they
are consumed by `hrp`'s proof, the normalization, not by the assembly).
The mirror's winning play is `π₁` (replayed, exchanged) followed by the
cleared assembly's play. -/
theorem State.solvable_of_exchange_merge_bridge {st a₁ : State} {t z z' c : Card} {b : Base}
    (hwin : ∀ {S M : State} {u : Card}, State.TwinCorr (Card.swapTwin u) u.suit S M →
      S.WF → S.solvableFrom → M.solvableFrom)
    (hrp : st.ExchangeRiderPrefix t z z' c b)
    (hdet : State.ExchangeDeepNorm t z z' c b)
    (_hwf : st.WF) (_h : st.twinLicensed t)
    (_hstep : st.apply (Move.pilePile c b) = some a₁)
    (_hmerge : t ∈ st.board.aboveOf c)
    (_hland : ∃ d, b = Sum.inr d ∧
      (d = z ∨ d ∈ st.board.aboveOf z ∨ d = z' ∨ d ∈ st.board.aboveOf z'))
    (_hsol : a₁.solvableFrom) :
    (st.exchangeTwinCargo t).solvableFrom := by
  obtain ⟨π₁, S₀, -, hrunM, hwf₀, hlic₀, hrid₀, hmerge₀, ha₁', hland₀⟩ := hrp
  obtain ⟨a₁', hstep₀, hsol₀⟩ := ha₁'
  have hres := State.solvable_of_exchange_merge_cleared hwin hdet hwf₀ hlic₀ hrid₀ hstep₀
    hmerge₀ hland₀ hsol₀
  obtain ⟨π', W, hrun', hwin'⟩ := hres
  exact ⟨π₁ ++ π', W, run_append_some hrunM hrun', hwin'⟩

/-- **The flip-dual**: the t'/t-flipped merge — the run passes the OTHER
twin — at the flipped premises (the flipped rider-prefix and deep
normalizations, i.e. the same shapes read at `(t.flipSuit, z', z)`).
The route carries over verbatim (`twinLicensed_flipSuit` re-seats the
license; `exchangeTwinCargo_pair` identifies the two exchanges). -/
theorem State.solvable_of_exchange_merge_bridge_flip {st a₁ : State} {t z z' c : Card}
    {b : Base}
    (hwin : ∀ {S M : State} {u : Card}, State.TwinCorr (Card.swapTwin u) u.suit S M →
      S.WF → S.solvableFrom → M.solvableFrom)
    (hrp : st.ExchangeRiderPrefix t.flipSuit z' z c b)
    (hdet : State.ExchangeDeepNorm t.flipSuit z' z c b)
    (hwf : st.WF) (h : st.twinLicensed t)
    (hstep : st.apply (Move.pilePile c b) = some a₁)
    (hmerge : t.flipSuit ∈ st.board.aboveOf c)
    (hland : ∃ d, b = Sum.inr d ∧
      (d = z ∨ d ∈ st.board.aboveOf z ∨ d = z' ∨ d ∈ st.board.aboveOf z'))
    (hsol : a₁.solvableFrom) :
    (st.exchangeTwinCargo t).solvableFrom := by
  have hlandf : ∃ d, b = Sum.inr d ∧
      (d = z' ∨ d ∈ st.board.aboveOf z' ∨ d = z ∨ d ∈ st.board.aboveOf z) := by
    obtain ⟨d, hbd, hld⟩ := hland
    rcases hld with h | h | h | h
    · exact ⟨d, hbd, Or.inr (Or.inr (Or.inl h))⟩
    · exact ⟨d, hbd, Or.inr (Or.inr (Or.inr h))⟩
    · exact ⟨d, hbd, Or.inl h⟩
    · exact ⟨d, hbd, Or.inr (Or.inl h)⟩
  have hres := State.solvable_of_exchange_merge_bridge (t := t.flipSuit) (z := z')
    (z' := z) hwin hrp hdet hwf (State.twinLicensed_flipSuit h) hstep hmerge hlandf hsol
  rwa [State.exchangeTwinCargo_pair] at hres

/-- **The merge bridge, full form** — exactly `solvable_of_exchange_merge`'s
signature (the disjunctive hmerge), at the pinned cargo pair, with both
orientations' normalization premises supplied (the deep ones in the
ITERATED form: a `CleanAt` clearing prefix before the detach). -/
theorem State.solvable_of_exchange_merge_bridge_full {st a₁ : State} {t z z' c : Card}
    {b : Base}
    (hwin : ∀ {S M : State} {u : Card}, State.TwinCorr (Card.swapTwin u) u.suit S M →
      S.WF → S.solvableFrom → M.solvableFrom)
    (hrp : st.ExchangeRiderPrefix t z z' c b)
    (hrpf : st.ExchangeRiderPrefix t.flipSuit z' z c b)
    (hdet : State.ExchangeDeepNorm t z z' c b)
    (hdetf : State.ExchangeDeepNorm t.flipSuit z' z c b)
    (hwf : st.WF) (h : st.twinLicensed t)
    (hstep : st.apply (Move.pilePile c b) = some a₁)
    (hmerge : t ∈ st.board.aboveOf c ∨ t.flipSuit ∈ st.board.aboveOf c)
    (hland : ∃ d, b = Sum.inr d ∧
      (d = z ∨ d ∈ st.board.aboveOf z ∨ d = z' ∨ d ∈ st.board.aboveOf z'))
    (hsol : a₁.solvableFrom) :
    (st.exchangeTwinCargo t).solvableFrom := by
  rcases hmerge with hm | hm
  · exact State.solvable_of_exchange_merge_bridge hwin hrp hdet hwf h hstep hm hland hsol
  · exact State.solvable_of_exchange_merge_bridge_flip hwin hrpf hdetf hwf h hstep hm hland hsol

/-! ## §7. The rooted merge bridge — [H′] assembled modulo the same
named premises

The [H] shape at the ROOTED corner: the merge's run is the twin's own
(the move `pilePile t b` — the run [t, z], the cargo riding the twin),
landing on the OTHER cargo's run (`d ∈ aboveOf z'`).  The corner is
geometrically SIMPLER than [H]: the landing is necessarily DEEP (the
merge's own fit excludes the root `d = z'` — d hosts t while z' hosts
t', one rung above and one below t — and the own cargo by the fit
antisymm), so the assembly's dispatch is only the first rider's
FIT/HOLE case, and the FIT case reuses [H]'s two-ply VERBATIM (the ply
lemma `exchange_merge_ply_deep_fit` is run-shape-free — §3's refactor:
its `hexc`/`hexd` exclusions are derivable at the rooted corner from the
license fits and the landing's own fit).  The mirror's two-ply: the
RIDER TRANSFER `pilePile r₁ (inr z)` (the z'-riders onto the bare z,
now riding t'), then the ROOTED MERGE `pilePile t (inr d)` (the mirror's
[t, z'] — the run the exchange left on t — landing on d, now the top of
the transferred stack): the result is exactly `a₁`, twin-swapped at the
CARGO z.  The HOLE case replays hdet's detour by the clean-run mirror
step, then the merge is a PASSING move in both games (both cargo stacks
emptied), the covers survive, the seat exchange IS the twin swap, the
correspondence, `hwin`, the explicit play. -/

/-- **The rooted rider-prefix normalization premise** (route step 1, the
honest boundary): the source's winning line can be scheduled so that a
prefix π₁ clears z's riders BEFORE the rooted merge — reaching a state
S₀ at which the license still holds pinned, z is bare (the merged run is
exactly [t, z]), the SAME rooted merge move re-fires with a solvable
successor, and the landing is on the z'-side (the only live side: the
root d = z' dies on the rung gap, the own cargo on the fit antisymm —
both derived at the assembly) — and π₁ replays verbatim in the exchanged
game (the successors staying exchanged).  Premise-free this needs the
source-side commutation `[merge; π₁] ≈ [π₁; merge]` (an L1/O3-shaped play
normalization) and the prefix's exchange-cleanliness — the same residue
as [H]'s `ExchangeRiderPrefix`, read at the rooted run (the riders
cleared are those of the MOVED run's own cargo z, not the landing
side's).  At the simulation's call site (the `c = t` branch of
`solvable_exchangeTwinCargo_go`, the `hdz' : d ∈ aboveOf z'` sub-case)
the st-level premises pin the same landing d, so the S₀-level landing
clause is instantiated by the prefix's not disturbing the z'-stack. -/
def State.ExchangeRiderPrefixRooted (st : State) (t z z' : Card) (b : Base) : Prop :=
  ∃ (π₁ : List Move) (S₀ : State),
    st.run π₁ = some S₀ ∧
    (st.exchangeTwinCargo t).run π₁ = some (S₀.exchangeTwinCargo t) ∧
    S₀.WF ∧ State.TwinLicensedAt S₀ t z z' ∧
    S₀.board.topOf (Sum.inr z) = none ∧
    (∃ a₁' : State, S₀.apply (Move.pilePile t b) = some a₁' ∧ a₁'.solvableFrom) ∧
    (∃ d, b = Sum.inr d ∧ d ∈ S₀.board.aboveOf z')

/-- **The rooted deep-landing normalization premise, ITERATED form**
(route step 2-deep, the fit hole): at a licensed WF riders-cleared
rooted-merge state whose first rider r₁ (directly on z') fits NEITHER
cargo, a CLEAN CLEARING PREFIX π₀ (each member a `CleanAt` move) reaches
a state at which the rider run has a legal detach `pilePile r₁ β` whose
follow-up rooted merge (the same move) still fires with a solvable
successor.  The plain single-detach form is FALSE at WF — the same two
witnesses that killed [H]'s (detour.lean: the non-king r₁ with both
candidate tops occupied; detour2.lean: the king r₁ with all seven
anchors filled) sit at the rooted corner's geometry — and the same
iterated repair validates it (the clearing stack, the detach, the merge,
winning on both sides).  The [H] shape MINUS the run-passes-twin clause
(the rooted run is pinned by the move itself, `pilePile t b`); no
landing clause either (the rooted merge's own fit forces the landing
deep into the z'-stack, as the assembly derives).  The honest residue:
the `S₂.solvableFrom` conjunct stays inside the premise (the same two
in-principle breaking channels, unobserved — detour3.lean's structural
harmlessness analysis carries over verbatim: the run above t is [z]
with z bare, and the hole kills exactly that base). -/
def State.ExchangeDeepNormRooted (t z z' : Card) (b : Base) : Prop :=
  ∀ {S A : State} {r₁ : Card},
    S.WF → State.TwinLicensedAt S t z z' →
    S.board.topOf (Sum.inr z) = none →
    S.board.topOf (Sum.inr z') = some r₁ → canSitOn r₁ z = false →
    S.apply (Move.pilePile t b) = some A → A.solvableFrom →
    ∃ (π₀ : List Move) (S₀' : State) (β : Base) (S₁ S₂ : State),
      S.run π₀ = some S₀' ∧
      (∀ m ∈ π₀, State.CleanAt m t z z' t r₁) ∧
      S₀'.apply (Move.pilePile r₁ β) = some S₁ ∧
      S₁.apply (Move.pilePile t b) = some S₂ ∧
      S₂.solvableFrom

/-- **The rooted merge bridge, cleared form**: at a licensed WF state
whose z is bare (riders-cleared), the rooted merge move (the twin's own
run [t, z], landing on d deep in the z'-stack) transfers solvability to
the exchanged state — modulo the window (`hwin`) and the deep
normalization (`hdet`).  The route: the landing exclusions from the
merge's own firing (d ≠ z by the fit antisymm, d ≠ z' by the rung gap —
so the landing is always DEEP and the first rider r₁ exists), the
rider's FIT/HOLE case (FIT: the two-ply `exchange_merge_ply_deep_fit` at
c := t; HOLE: hdet's ITERATED detour — the CleanAt clearing prefix π₀
first, replayed in the exchange by the run-level clean-replay lemma
with the invariants riding, then the detach by the clean-run mirror
step, then the merge as a passing move in both games, the
seat-exchanged result equal to the twin swap by the preserved covers),
the correspondence (`twinCorr_of_ply`), the climb-out (`hwin`), and the
explicit play composition (`solvable_step` + `run_append_some`). -/
theorem State.solvable_of_exchange_merge_rooted_cleared {st a₁ : State} {t z z' : Card} {b : Base}
    (hwin : ∀ {S M : State} {u : Card}, State.TwinCorr (Card.swapTwin u) u.suit S M →
      S.WF → S.solvableFrom → M.solvableFrom)
    (hdet : State.ExchangeDeepNormRooted t z z' b)
    (hwf : st.WF) (hlic : st.TwinLicensedAt t z z')
    (hrid : st.board.topOf (Sum.inr z) = none)
    (hstep : st.apply (Move.pilePile t b) = some a₁)
    (hland : ∃ d, b = Sum.inr d ∧ d ∈ st.board.aboveOf z')
    (hsol : a₁.solvableFrom) :
    (st.exchangeTwinCargo t).solvableFrom := by
  obtain ⟨hvis, hvis', h₀, h₀', hfit, hfit', hnb, hnb'⟩ := hlic
  have hztop : st.board.topOf (Sum.inr t) = some z := (Board.bottomOf_eq _ _ _).mp h₀
  have hztop' : st.board.topOf (Sum.inr t.flipSuit) = some z' :=
    (Board.bottomOf_eq _ _ _).mp h₀'
  have hcargo : z' = z.flipSuit := State.cargo_flipSuit hfit hfit' hztop hztop'
  have hzne : z ≠ t ∧ z ≠ t.flipSuit := Card.ne_pair_of_canSitOn hfit
  have hzne' : z' ≠ t ∧ z' ≠ t.flipSuit := by
    obtain ⟨ha, hb⟩ := Card.ne_pair_of_canSitOn hfit'
    exact ⟨fun h => hb (by rw [h, Card.flipSuit_flipSuit]), ha⟩
  have hzz' : z ≠ z' := by
    intro h
    have h2 : z = z.flipSuit := h.trans hcargo
    exact Card.flipSuit_ne z h2.symm
  -- the landing's d, pinned; the merge's own fit buys the exclusions
  obtain ⟨d, hbd, hdz'⟩ := hland
  have happ := hstep
  rw [apply_pilePile_iff] at happ
  obtain ⟨-, -, -, hcmr, -, -, -⟩ := happ
  simp only [State.canMoveRun, Bool.and_eq_true_iff] at hcmr
  obtain ⟨hcp, -⟩ := hcmr
  rw [hbd] at hcp
  obtain ⟨-, -, hfitd⟩ := canPlace_inr_iff.mp hcp
  -- d ≠ z (t sits on d, z sits on t — the antisymm); d ≠ z' (d is one
  -- rung above t, z' one below): the ROOT landing is impossible, the
  -- rooted merge is always the DEEP shape
  have hdz : d ≠ z := by
    intro hcon
    rw [hcon] at hfitd
    exact (canSitOn_antisymm hfit) hfitd
  have hdz'ne : d ≠ z' := by
    intro hcon
    obtain ⟨hrk, -⟩ := (canSitOn_eq t d).mp hfitd
    obtain ⟨hrk', -⟩ := (canSitOn_eq z' t.flipSuit).mp hfit'
    rw [Card.flipSuit_rank] at hrk'
    rw [hcon] at hrk
    omega
  -- the moved root is off the cargo pair (the license fits)
  have htz : t ≠ z := fun h => hzne.1 h.symm
  have htz' : t ≠ z' := fun h => hzne'.1 h.symm
  have htzfs : t ≠ z.flipSuit := fun h => htz' (h.trans hcargo.symm)
  cases htopz' : st.board.topOf (Sum.inr z') with
  | none => exact absurd hdz' (by rw [Board.aboveOf_step_none htopz']; simp)
  | some r₁ =>
      by_cases hfitr : canSitOn r₁ z = true
      · -- FIT: the two-ply (the rider transfer, then the rooted merge)
        have hstepr : st.apply (Move.pilePile t (Sum.inr d)) = some a₁ := by
          rw [← hbd]
          exact hstep
        obtain ⟨M₁, hfire₁, hfire₂⟩ :=
          State.exchange_merge_ply_deep_fit hwf h₀ h₀' hfit hfit' hnb hnb' hrid
            htopz' hfitr hstepr ⟨htz, htzfs⟩ ⟨hdz, fun h => hdz'ne (h.trans hcargo.symm)⟩
        -- the correspondence at the merge successor (the twin-swapped image)
        have hbz₁ : a₁.board.bottomOf z = some (Sum.inr t) :=
          (State.apply_pilePile_bottomOf hstep hzne.1).trans h₀
        have hbz₁' : a₁.board.bottomOf z' = some (Sum.inr t.flipSuit) :=
          (State.apply_pilePile_bottomOf hstep hzne'.1).trans h₀'
        have hvisz : a₁.isVis z = true := by
          show (a₁.board.bottomOf z).isSome = true
          rw [hbz₁]
          rfl
        have hvisz' : a₁.isVis (Card.flipSuit z) = true := by
          show (a₁.board.bottomOf (Card.flipSuit z)).isSome = true
          rw [← hcargo, hbz₁']
          rfl
        have hcorr := State.twinCorr_of_ply (apply_wf hwf _ _ hstep) hvisz hvisz'
          (State.swapTwinBoard_board z a₁) (State.swapTwinBoard_deal z a₁)
          (State.swapTwinBoard_heights z a₁) (State.swapTwinBoard_depths z a₁)
          (State.swapTwinBoard_stock z a₁) rfl
        exact State.solvable_step hfire₁ (State.solvable_step hfire₂
          (hwin hcorr (apply_wf hwf _ _ hstep) hsol))
      · -- HOLE: the iterated detour (hdet) — the clean clearing prefix
        -- π₀ first, then the detach, then the passing merge
        have hfitrf : canSitOn r₁ z = false := by
          cases hf : canSitOn r₁ z with
          | false => rfl
          | true => exact absurd hf hfitr
        obtain ⟨π₀, S₀', β, S₁, S₂, hrunπ₀, hcleanπ₀, hdetour, hmerge₁, hsol₂⟩ :=
          hdet hwf ⟨hvis, hvis', h₀, h₀', hfit, hfit', hnb, hnb'⟩ hrid htopz'
            hfitrf hstep hsol
        -- the mirror replays the clearing prefix verbatim (the run-level
        -- clean-replay lemma), the invariants riding to S₀'
        obtain ⟨hrunπ₀X, hlic₀, hrid₀, htopz'₀⟩ :=
          State.exchangeTwinCargo_run_cleanAt
            ⟨hvis, hvis', h₀, h₀', hfit, hfit', hnb, hnb'⟩ hrid htopz' hcleanπ₀ hrunπ₀
        obtain ⟨hvis, hvis', h₀, h₀', hfit, hfit', hnb, hnb'⟩ := hlic₀
        have hztop : S₀'.board.topOf (Sum.inr t) = some z :=
          (Board.bottomOf_eq _ _ _).mp h₀
        have hztop' : S₀'.board.topOf (Sum.inr t.flipSuit) = some z' :=
          (Board.bottomOf_eq _ _ _).mp h₀'
        -- the detour's landing is off the twin seats and the cargo seats
        have hroff := State.first_rider_off h₀ h₀' hfit' hnb' htopz'₀
        have hdapp := hdetour
        rw [apply_pilePile_iff] at hdapp
        obtain ⟨β₀', hbotr₁', -, hcmrβ, bdd, hattβ, rfl⟩ := hdapp
        have hcpβ : S₀'.canPlace r₁ β = true := by
          simp only [State.canMoveRun, Bool.and_eq_true_iff] at hcmrβ
          exact hcmrβ.1
        have hfreeβ : S₀'.board.topOf β = none := topOf_of_canPlace hcpβ
        have hβz : β ≠ Sum.inr z := by
          intro hcon
          rw [hcon] at hcpβ
          have hfit2 := (canPlace_inr_iff.mp hcpβ).2.2
          rw [hfit2] at hfitr
          exact absurd hfitr (by simp)
        have hβz' : β ≠ Sum.inr z' := by
          intro hcon
          rw [hcon] at hfreeβ
          rw [hfreeβ] at htopz'₀
          exact absurd htopz'₀ (by simp)
        have hβt : β ≠ Sum.inr t := by
          intro hcon
          rw [hcon] at hfreeβ
          rw [hfreeβ] at hztop
          exact absurd hztop (by simp)
        have hβt' : β ≠ Sum.inr t.flipSuit := by
          intro hcon
          rw [hcon] at hfreeβ
          rw [hfreeβ] at hztop'
          exact absurd hztop' (by simp)
        have hbotr₁st : S₀'.board.bottomOf r₁ = some (Sum.inr z') :=
          (Board.bottomOf_eq _ _ _).mpr htopz'₀
        have hβ₀' : β₀' = Sum.inr z' :=
          (Option.some.inj (hbotr₁st.symm.trans hbotr₁')).symm
        have hzsz' : (Sum.inr z : Base) ≠ β₀' := by
          rw [hβ₀']
          exact fun h => hzz' (Sum.inr.inj h)
        have htopz₁ : {S₀' with board := bdd}.board.topOf (Sum.inr z) = none := by
          show bdd.topOf (Sum.inr z) = none
          rw [Board.attach_topOf_ne _ _ _ hattβ hβz.symm, Board.detach_topOf_ne _ _ _ hzsz']
          exact hrid₀
        have htopz'₁ : {S₀' with board := bdd}.board.topOf (Sum.inr z') = none := by
          show bdd.topOf (Sum.inr z') = none
          rw [Board.attach_topOf_ne _ _ _ hattβ hβz'.symm, hβ₀', Board.detach_topOf]
        have hemptyz : {S₀' with board := bdd}.board.aboveOf z = [] :=
          Board.aboveOf_step_none htopz₁
        have hemptyz' : {S₀' with board := bdd}.board.aboveOf z' = [] :=
          Board.aboveOf_step_none htopz'₁
        -- the license survives the detour at the pinned pair (both stacks
        -- are empty: z was bare, and the detach emptied z')
        have hbz₁ : {S₀' with board := bdd}.board.bottomOf z = some (Sum.inr t) :=
          (State.apply_pilePile_bottomOf hdetour (Ne.symm hroff.1)).trans h₀
        have hbz₁' : {S₀' with board := bdd}.board.bottomOf z' =
            some (Sum.inr t.flipSuit) :=
          (State.apply_pilePile_bottomOf hdetour (Ne.symm hroff.2.1)).trans h₀'
        have hnb₁ : t ∉ {S₀' with board := bdd}.board.aboveOf z ∧
            t.flipSuit ∉ {S₀' with board := bdd}.board.aboveOf z := by
          rw [hemptyz]
          exact ⟨fun h => absurd h (by simp), fun h => absurd h (by simp)⟩
        have hnb₁' : t ∉ {S₀' with board := bdd}.board.aboveOf z' ∧
            t.flipSuit ∉ {S₀' with board := bdd}.board.aboveOf z' := by
          rw [hemptyz']
          exact ⟨fun h => absurd h (by simp), fun h => absurd h (by simp)⟩
        -- the mirror replays the detour (the clean-run mirror step)
        have hcleanr : t ∉ S₀'.board.aboveOf r₁ ∧ t.flipSuit ∉ S₀'.board.aboveOf r₁ := by
          constructor
          · intro hmem
            exact hnb'.1 (Board.aboveOf_trans (Board.mem_aboveOf_of_topOf htopz'₀) hmem)
          · intro hmem
            exact hnb'.2 (Board.aboveOf_trans (Board.mem_aboveOf_of_topOf htopz'₀) hmem)
        have hfireD : (S₀'.exchangeTwinCargo t).apply (Move.pilePile r₁ β)
            = some ({S₀' with board := bdd}.exchangeTwinCargo t) :=
          State.exchangeTwinCargo_step_pilePile h₀ h₀' ⟨hroff.1, hroff.2.1⟩
            ⟨hroff.2.2.1, hroff.2.2.2⟩ hcleanr hdetour
        -- the merge is a passing move in both games
        have hoff : ∀ d', b = Sum.inr d' →
            d' ≠ z ∧ d' ≠ z' ∧
            d' ∉ {S₀' with board := bdd}.board.aboveOf z ∧
            d' ∉ {S₀' with board := bdd}.board.aboveOf z' := by
          intro d' hd'
          have hdeq : d' = d := Sum.inr.inj (hd'.symm.trans hbd)
          rw [hdeq]
          exact ⟨hdz, hdz'ne, fun h => absurd h (by rw [hemptyz]; simp),
            fun h => absurd h (by rw [hemptyz']; simp)⟩
        have hfireM : ({S₀' with board := bdd}.exchangeTwinCargo t).apply (Move.pilePile t b)
            = some (S₂.exchangeTwinCargo t) :=
          State.exchangeTwinCargo_step_pilePile_passing hbz₁ hbz₁' hfit hfit' hnb₁ hnb₁'
            ⟨htz, htz'⟩ hoff hmerge₁
        -- the covers survive, so the seat exchange IS the twin swap
        have hbz₂ : S₂.board.bottomOf z = some (Sum.inr t) :=
          (State.apply_pilePile_bottomOf hmerge₁ hzne.1).trans hbz₁
        have hbz₂' : S₂.board.bottomOf z' = some (Sum.inr t.flipSuit) :=
          (State.apply_pilePile_bottomOf hmerge₁ hzne'.1).trans hbz₁'
        have hcovert : S₂.board.topOf (Sum.inr t) = some z :=
          (Board.bottomOf_eq _ _ _).mp hbz₂
        have hcovert' : S₂.board.topOf (Sum.inr t.flipSuit) = some z' :=
          (Board.bottomOf_eq _ _ _).mp hbz₂'
        have hnezsz : (Sum.inr z : Base) ≠ b := fun h =>
          hdz (Sum.inr.inj (h.trans hbd)).symm
        have hnezsz' : (Sum.inr z' : Base) ≠ b := fun h =>
          hdz'ne (Sum.inr.inj (h.trans hbd)).symm
        have hdapp₂ := hmerge₁
        rw [apply_pilePile_iff] at hdapp₂
        obtain ⟨βc, hbotc₁, -, -, bd₂, hatt₂, hst₂⟩ := hdapp₂
        have hβcz : βc ≠ Sum.inr z := by
          intro hcon
          rw [hcon] at hbotc₁
          rw [(Board.bottomOf_eq _ _ _).mp hbotc₁] at htopz₁
          exact absurd htopz₁ (by simp)
        have hβcz' : βc ≠ Sum.inr z' := by
          intro hcon
          rw [hcon] at hbotc₁
          rw [(Board.bottomOf_eq _ _ _).mp hbotc₁] at htopz'₁
          exact absurd htopz'₁ (by simp)
        have htopz₂ : S₂.board.topOf (Sum.inr z) = none :=
          (State.apply_pilePile_topOf hmerge₁ hbotc₁ hnezsz hβcz.symm).trans htopz₁
        have htopz₂' : S₂.board.topOf (Sum.inr z') = none :=
          (State.apply_pilePile_topOf hmerge₁ hbotc₁ hnezsz' hβcz'.symm).trans htopz'₁
        have hboardM : (S₂.exchangeTwinCargo t).board = S₂.board.mapByTwin z := by
          rw [State.exchangeTwinCargo_board,
            Board.exchangeTwin_eq_mapByTwin_of_covers hcovert hcovert' hcargo hzne
              ⟨htopz₂, htopz₂'⟩]
        have hvisz₂ : S₂.isVis z = true := by
          show (S₂.board.bottomOf z).isSome = true
          rw [hbz₂]
          rfl
        have hvisz₂' : S₂.isVis (Card.flipSuit z) = true := by
          show (S₂.board.bottomOf (Card.flipSuit z)).isSome = true
          rw [← hcargo, hbz₂']
          rfl
        have hwf₂ : S₂.WF :=
          apply_wf (apply_wf (State.wf_run hwf hrunπ₀) _ _ hdetour) _ _ hmerge₁
        have hcorr := State.twinCorr_of_ply hwf₂ hvisz₂ hvisz₂'
          hboardM (State.exchangeTwinCargo_deal S₂ t) (State.exchangeTwinCargo_heights S₂ t)
          (State.exchangeTwinCargo_depths S₂ t) (State.exchangeTwinCargo_stock S₂ t)
          (State.exchangeTwinCargo_drawStep S₂ t)
        obtain ⟨π', W, hrun', hwin'⟩ := hwin hcorr hwf₂ hsol₂
        exact ⟨π₀ ++ (Move.pilePile r₁ β :: Move.pilePile t b :: π'), W,
          run_append_some hrunπ₀X (run_cons_intro hfireD (run_cons_intro hfireM hrun')),
          hwin'⟩

/-! ### The [H′]-shaped bridges -/

/-- **The rooted merge bridge, scaffolded** — [H′] modulo the same named
premises as [H] (the window hwin; the rooted rider-prefix; the rooted
ITERATED deep-landing normalization), at the pinned cargo pair.  The fixed
premises `_hwf _h _hstep _hc _hland _hsol` are the [H′] shape at the
pinned pair (kept for signature fidelity, `_`-prefixed because the
assembly itself runs at the cleared state `S₀` that `hrp` provides — they
are consumed by `hrp`'s proof, the normalization, not by the assembly).
The mirror's winning play is `π₁` (replayed, exchanged) followed by the
cleared assembly's play. -/
theorem State.solvable_of_exchange_merge_rooted_bridge {st a₁ : State} {t z z' c : Card}
    {b : Base}
    (hwin : ∀ {S M : State} {u : Card}, State.TwinCorr (Card.swapTwin u) u.suit S M →
      S.WF → S.solvableFrom → M.solvableFrom)
    (hrp : st.ExchangeRiderPrefixRooted t z z' b)
    (hdet : State.ExchangeDeepNormRooted t z z' b)
    (_hwf : st.WF) (_h : st.twinLicensed t)
    (_hstep : st.apply (Move.pilePile c b) = some a₁) (_hc : c = t)
    (_hland : ∃ d, b = Sum.inr d ∧ d ∈ st.board.aboveOf z')
    (_hsol : a₁.solvableFrom) :
    (st.exchangeTwinCargo t).solvableFrom := by
  obtain ⟨π₁, S₀, -, hrunM, hwf₀, hlic₀, hrid₀, ha₁', hland₀⟩ := hrp
  obtain ⟨a₁', hstep₀, hsol₀⟩ := ha₁'
  have hres := State.solvable_of_exchange_merge_rooted_cleared hwin hdet hwf₀ hlic₀ hrid₀
    hstep₀ hland₀ hsol₀
  obtain ⟨π', W, hrun', hwin'⟩ := hres
  exact ⟨π₁ ++ π', W, run_append_some hrunM hrun', hwin'⟩

/-- **The rooted flip-dual**: the t'/t-flipped rooted merge — the OTHER
twin's own run landing on the z-side — at the flipped premises (the
flipped rider-prefix and deep normalizations, i.e. the same shapes read
at `(t.flipSuit, z', z)`).  The route carries over verbatim
(`twinLicensed_flipSuit` re-seats the license; `exchangeTwinCargo_pair`
identifies the two exchanges). -/
theorem State.solvable_of_exchange_merge_rooted_bridge_flip {st a₁ : State} {t z z' c : Card}
    {b : Base}
    (hwin : ∀ {S M : State} {u : Card}, State.TwinCorr (Card.swapTwin u) u.suit S M →
      S.WF → S.solvableFrom → M.solvableFrom)
    (hrp : st.ExchangeRiderPrefixRooted t.flipSuit z' z b)
    (hdet : State.ExchangeDeepNormRooted t.flipSuit z' z b)
    (hwf : st.WF) (h : st.twinLicensed t)
    (hstep : st.apply (Move.pilePile c b) = some a₁) (hc : c = t.flipSuit)
    (hland : ∃ d, b = Sum.inr d ∧ d ∈ st.board.aboveOf z)
    (hsol : a₁.solvableFrom) :
    (st.exchangeTwinCargo t).solvableFrom := by
  have hres := State.solvable_of_exchange_merge_rooted_bridge (t := t.flipSuit) (z := z')
    (z' := z) hwin hrp hdet hwf (State.twinLicensed_flipSuit h) hstep hc hland hsol
  rwa [State.exchangeTwinCargo_pair] at hres

/-- **The rooted merge bridge, full form** — exactly
`solvable_of_exchange_merge_rooted`'s signature, with the normalization
premises supplied as one ∃z-package (the rider-prefix and the deep norm
sharing the license's cargo pin — at the simulation's call sites the
witness is the license's unpacked z and the caller's z' its z'-witness,
so the package is instantiated by the license's covers via
`twinLicensedAt_of_twinLicensed`).  The st-level premises
`hwf h hstep hc hland hsol` are the [H′] shape (kept for signature
fidelity — they are consumed by the package's proof, the normalization,
not by the assembly). -/
theorem State.solvable_of_exchange_merge_rooted_bridge_full {st a₁ : State} {t z' c : Card}
    {b : Base}
    (hwin : ∀ {S M : State} {u : Card}, State.TwinCorr (Card.swapTwin u) u.suit S M →
      S.WF → S.solvableFrom → M.solvableFrom)
    (hnorm : ∃ z : Card, st.ExchangeRiderPrefixRooted t z z' b ∧
      State.ExchangeDeepNormRooted t z z' b)
    (hwf : st.WF) (h : st.twinLicensed t)
    (hstep : st.apply (Move.pilePile c b) = some a₁) (hc : c = t)
    (hland : ∃ d, b = Sum.inr d ∧ d ∈ st.board.aboveOf z')
    (hsol : a₁.solvableFrom) :
    (st.exchangeTwinCargo t).solvableFrom := by
  obtain ⟨z, hrp, hdet⟩ := hnorm
  exact State.solvable_of_exchange_merge_rooted_bridge hwin hrp hdet hwf h hstep hc hland hsol

/-! ## §8. The direct reduction — the window at a both-bare state

The endgame simplification, validated with its boundary: the window has
LANDED (TwinReplay's `solvable_of_twinCorr_window`, commit 861d775), and
this section wires it in.  A licensed WF state whose BOTH cargo stacks
are bare (z and z' riders-cleared) needs NO merge analysis at all — the
exchange state is twin-correlated with the source at the CARGO pair, so
the window replays the source's ENTIRE window-admitted winning play —
the merge included — through the correspondence, and the exchange wins.
The window's added premises over the old abstract `hwin` are all
discharged or relocated: `hMle` (the mirror's heights rfl + WF's
`heights_le` — carried by the correspondence lemma), `hhid`/`hstock`
(the hidden/stock cards ρ-fixed — DERIVED here from WF + the covers:
the cargos are seated, hence visible, hence off the hidden slices and
the stock, and `swapTwin z` fixes everything off the pair), and `hsolw`
in place of plain solvability — the winning play must satisfy the
window condition (the skew/anti-skew + pair-deckStack exclusion), so
the consumers' solvability premises become `solvableWindow`-shaped,
composed through the merge move (a `pilePile` is windowOK-always —
height-blind) by the cons-glue below.  The window is CONSUMED at the
both-bare state (the correspondence's S-side): its premises derive
from THAT state's WF + the surviving covers — which the license-carrying
run lemmas already provide — so no st-level preservation through the
prefix is needed (the shrink lemmas are landed anyway for the
alternative route).

**The boundary, probed (rootedprobe3.lean):** the naive twin-pair form
`TwinCorr (swapTwin t) t.suit st (st.exchangeTwinCargo t)` is FALSE at
licensed states.  `TwinCorr`'s board clause demands the VALUE-relabeling
conjugation (`M.board = mapByRho (swapTwin t) st.board`), while the
exchange swaps the twin seats' CONTENTS without relabeling card
identities; the two disagree exactly at the seats carrying t or t' as
their top — the twins' own bases — and licensed twins ARE seated
(that is `isVis`).  At fithole's witness the claimed clause reads
`some ♥Q ≠ some ♦Q` at c's seat.  The two requirements are even
mutually exclusive: the board clause needs NO seat carrying t/t' (the
twins unseated), while the stacked-set cross-case needs them visible
for `founds_gone`.  The correct direct correspondence is at the CARGO
pair (the license's covers identify the seat exchange with the cargo
twin swap — §1's `exchangeTwin_eq_mapByTwin_of_covers`), and it needs
BOTH cargo seats bare — exactly what the deep landing's z'-riders
obstruct, hence the double-clearing premise below for the deep corners.
The direct route supersedes the two-ply scaffolds wherever its regime
holds; the hrp/hdet scaffolds remain as the fallback for
non-window-shaped winning plays and rider-carrying states. -/

/-- **The strengthened window's cons-glue, tableau kinds**: the
height-blind moves — `draw`, `reveal`, `deckPile`, and `pilePile` — are
UNCONDITIONALLY admitted in the pre-episode phase (the def's arm carries
no condition), so a firing one composes with any window'-admitted
continuation.  The merge (a `pilePile`) is the consumers' composition
point. -/
theorem State.solvableWindow'_cons_pilePile {S R : State} {z : Card} {σ : Suit}
    {c : Card} {b : Base}
    (hstep : S.apply (Move.pilePile c b) = some R)
    (hrest : R.solvableWindow' z σ) : S.solvableWindow' z σ := by
  obtain ⟨play, W, hrun, hwin, hplay⟩ := hrest
  refine ⟨Move.pilePile c b :: play, W, run_cons_intro hstep hrun, hwin, ?_⟩
  show State.playWindow' z σ State.WindowEp.pre S (Move.pilePile c b :: play) = true
  rw [State.playWindow', hstep]
  exact hplay

/-- **The window's hidden/stock premises, from WF + the covers**: the two
cargos are seated (the covers), hence visible, hence — by WF — off every
hidden slice (`vis_not_hidden`) and out of the stock (`vis_off_cycle`);
`swapTwin z` fixes every card off the pair, so the hidden and stock cards
are all ρ-fixed.  This packages the window's WF-derivations; it applies
at ANY state carrying the covers (the both-bare states of the scheduled
routes included — the window's S-side). -/
theorem State.swapTwin_hid_stock_of_covers {S : State} {t z z' : Card}
    (hwf : S.WF)
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.flipSuit = true)
    (hztop : S.board.topOf (Sum.inr t) = some z)
    (hztop' : S.board.topOf (Sum.inr t.flipSuit) = some z') :
    (∀ a, ∀ c ∈ S.hidden a, Card.swapTwin z c = c) ∧
      (∀ c ∈ S.stock.cards, Card.swapTwin z c = c) := by
  have hcargo : z' = z.flipSuit := State.cargo_flipSuit hfit hfit' hztop hztop'
  have hvisz : S.isVis z = true := by
    show (S.board.bottomOf z).isSome = true
    rw [(Board.bottomOf_eq S.board z (Sum.inr t)).mpr hztop]
    rfl
  have hvisz' : S.isVis (Card.flipSuit z) = true := by
    show (S.board.bottomOf (Card.flipSuit z)).isSome = true
    rw [← hcargo, (Board.bottomOf_eq S.board z' (Sum.inr t.flipSuit)).mpr hztop']
    rfl
  have hzh : ∀ a, z ∉ S.hidden a := fun a hmem => hwf.vis_not_hidden z hvisz a hmem
  have hz'h : ∀ a, Card.flipSuit z ∉ S.hidden a :=
    fun a hmem => hwf.vis_not_hidden (Card.flipSuit z) hvisz' a hmem
  have hzs : z ∉ S.stock.cards := by
    intro hmem
    have hpm := Cycle.posOf_mem hmem
    rw [hwf.vis_off_cycle z hvisz] at hpm
    exact absurd hpm (by simp)
  have hz's : Card.flipSuit z ∉ S.stock.cards := by
    intro hmem
    have hpm := Cycle.posOf_mem hmem
    rw [hwf.vis_off_cycle (Card.flipSuit z) hvisz'] at hpm
    exact absurd hpm (by simp)
  refine ⟨fun a c hc => Card.swapTwin_of_ne (fun h => hzh a (h ▸ hc))
      (fun h => hz'h a (h ▸ hc)), ?_⟩
  intro c hc
  exact Card.swapTwin_of_ne (fun h => hzs (h ▸ hc)) (fun h => hz's (h ▸ hc))

/-- **The window's hidden/stock premises survive any move** (the
alternative route — not needed by the consumers, which re-derive the
premises at the both-bare state from the covers): the hidden slices
shrink monotonically and the stock only loses cards (TwinReplay's
`hidden_sub_apply`/`stock_cards_sub_apply`). -/
theorem State.swapTwin_hid_stock_sub_apply {S R : State} {z : Card} {m : Move}
    (hS : S.apply m = some R)
    (hhid : ∀ a, ∀ c ∈ S.hidden a, Card.swapTwin z c = c)
    (hstock : ∀ c ∈ S.stock.cards, Card.swapTwin z c = c) :
    (∀ a, ∀ c ∈ R.hidden a, Card.swapTwin z c = c) ∧
      (∀ c ∈ R.stock.cards, Card.swapTwin z c = c) :=
  ⟨fun a c hc => hhid a c (State.hidden_sub_apply hS a c hc),
    fun c hc => hstock c (State.stock_cards_sub_apply hS c hc)⟩

/-- **The post-episode phase is run-unconditional**: every move of a
firing play is admitted (the identity correspondence aligns everything),
by the run induction. -/
theorem State.playWindow'_post_of_run {z : Card} {σ : Suit} {S W : State}
    {play : List Move}
    (hrun : S.run play = some W) :
    State.playWindow' z σ State.WindowEp.post S play = true := by
  induction play generalizing S W with
  | nil =>
      have hW : S = W := run_nil_elim hrun
      subst hW
      rfl
  | cons m ms ih =>
      obtain ⟨R, hS, hrest⟩ := run_cons_elim hrun
      show State.playWindow' z σ State.WindowEp.post S (m :: ms) = true
      rw [State.playWindow', hS]
      exact ih hrest

/-- **A visible card cannot deckStack** (the pair-deckStack exclusion's
vacuity at licensed states): the stock's `prev` is a stock card, and a
visible card is out of the stock (`vis_off_cycle` + `posOf_mem`).  So
the strengthened window's pair-deckStack exclusion is VACUOUS at any
state where the pair card is visible — the cargos at the licensed
states always. -/
theorem State.apply_deckStack_ne_of_vis {S : State} {q : Card}
    (hwf : S.WF) (hvis : S.isVis q = true) :
    S.apply (Move.deckStack q) = none := by
  cases hap : S.apply (Move.deckStack q) with
  | none => rfl
  | some R =>
      rw [apply_deckStack_iff] at hap
      obtain ⟨hprev, -⟩ := hap
      have hmem : q ∈ S.stock.cards := by
        cases hc : S.stock.cursor with
        | zero =>
            simp only [Cycle.prev, hc] at hprev
            exact absurd hprev (by simp)
        | succ n =>
            have hidx : S.stock.cards[n]? = some q := by
              simp only [Cycle.prev, hc] at hprev
              simpa using hprev
            obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hidx
            exact hget ▸ List.getElem_mem hlt
      have hpm := Cycle.posOf_mem hmem
      rw [hwf.vis_off_cycle q hvis] at hpm
      exact absurd hpm (by simp)

/-- **The adjacent-pair-stacking transfer (the sufficiency half)**: at a
both-bare licensed state, the play [pileStack z; pileStack z'; rest] —
the two cargos stacked ADJACENTLY, z first — with the first stack's
skew FAILING at S is window'-ADMITTED with the WHOLE REST
UNCONDITIONAL.  The route: the first stack is admitted by the GROWTH
ARM (its source-side premises hold at the both-bare state: z is the
pair card, the twin z' is seated and bare, the corner freedoms are the
covers' off-pair bases), the failed skew ROUTES TO THE GROWTH (the
strand is z'), and the second stack is the CATCH-UP (its skew then
holds: the first stack's firing was rung-EXACT, so the partner rung
rose to the pair's rank plus one), draining to the POST-episode where
every move translates.  The skew-HOLDING case admits the two stacks too
(both by the skew arm, staying pre) but the REST then needs the
pre-episode's remaining conditions (the unstack anti-skew; the
pair-deckStack is vacuous by `apply_deckStack_ne_of_vis`); the
non-adjacent case (tableau moves between the two stackings) meets the
mid-episode's tableau exclusion — the L1/L2 re-homing residual. -/
theorem State.playWindow'_adjacent_pair {S W : State} {t z z' : Card} {play : List Move}
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.flipSuit = true)
    (hztop : S.board.topOf (Sum.inr t) = some z)
    (hztop' : S.board.topOf (Sum.inr t.flipSuit) = some z')
    (hbare : S.board.topOf (Sum.inr z) = none ∧ S.board.topOf (Sum.inr z') = none)
    (hskew : ¬ (z.rank.toIdx ≤ S.heights (Card.flipSuit z).suit))
    (hrun : S.run (Move.pileStack z :: Move.pileStack z' :: play) = some W) :
    State.playWindow' z z.suit State.WindowEp.pre S
        (Move.pileStack z :: Move.pileStack z' :: play) = true := by
  obtain ⟨S₁, hstep1, hrest1⟩ := run_cons_elim hrun
  obtain ⟨S₂, hstep2, hrest2⟩ := run_cons_elim hrest1
  have hcargo : z' = z.flipSuit := State.cargo_flipSuit hfit hfit' hztop hztop'
  have hzne : z ≠ t ∧ z ≠ t.flipSuit := Card.ne_pair_of_canSitOn hfit
  have hzne' : z' ≠ t ∧ z' ≠ t.flipSuit := by
    obtain ⟨ha, hb⟩ := Card.ne_pair_of_canSitOn hfit'
    exact ⟨fun h => hb (by rw [h, Card.flipSuit_flipSuit]), ha⟩
  -- move 1's firing shape: the base (the cover) and the rung-exactness
  have hd1 := hstep1
  rw [apply_pileStack_iff] at hd1
  obtain ⟨htop1, bq, hbq, hrk1, rfl⟩ := hd1
  have hbqt : bq = Sum.inr t :=
    Option.some.inj (hbq.symm.trans
      ((Board.bottomOf_eq S.board z (Sum.inr t)).mpr hztop))
  subst hbqt
  have hbotq' : S.board.bottomOf (Card.flipSuit z) = some (Sum.inr t.flipSuit) := by
    rw [← hcargo]
    exact (Board.bottomOf_eq S.board z' (Sum.inr t.flipSuit)).mpr hztop'
  have hbfs : S.board.topOf (Sum.inr (Card.flipSuit z)) = none := by
    rw [← hcargo]
    exact hbare.2
  -- the corner ne's (the twin seats' bases are off the pair seats)
  have hc1 : t ≠ z := fun h => hzne.1 h.symm
  have hc2 : t ≠ Card.flipSuit z := fun h => hzne'.1 (hcargo.trans h.symm)
  have hc3 : t.flipSuit ≠ z := fun h => hzne.2 h.symm
  have hc4 : t.flipSuit ≠ Card.flipSuit z := fun h => hzne'.2 (hcargo.trans h.symm)
  -- the pair's rank identification
  have hrkz' : z'.rank.toIdx = z.rank.toIdx := by
    rw [hcargo, Card.flipSuit_rank]
  -- the tail: the post-episode is run-unconditional
  have hpost : State.playWindow' z z.suit State.WindowEp.post S₂ play = true :=
    State.playWindow'_post_of_run hrest2
  -- step 1's admission (the growth arm) and routing condition
  have hcond1 : ¬ ((z.suit ≠ z.suit ∧ z.suit ≠ z.suit.flipPair) ∨
      (z.rank.toIdx ≤ S.heights (Card.flipSuit z).suit)) := by
    rintro (⟨h, -⟩ | h)
    · exact h rfl
    · exact hskew h
  have hgrowth : decide ((z = z ∨ z = Card.flipSuit z) ∧
      (S.board.bottomOf (Card.flipSuit z)).isSome ∧
      S.board.topOf (Sum.inr (Card.flipSuit z)) = none ∧
      (S.board.bottomOf z).elim true
        (fun b => decide (b ≠ Sum.inr z ∧ b ≠ Sum.inr (Card.flipSuit z))) ∧
      (S.board.bottomOf (Card.flipSuit z)).elim true
        (fun b => decide (b ≠ Sum.inr z ∧ b ≠ Sum.inr (Card.flipSuit z)))) = true := by
    simp [hbotq', hbfs, hbq, hc1, hc2, hc3, hc4]
  -- step 2's catch-up equality (the strand is z') and its skew
  have hstr : z' = Card.swapTwin z z := by
    rw [Card.swapTwin_self_left]
    exact hcargo
  -- the computation
  show State.playWindow' z z.suit State.WindowEp.pre S
      (Move.pileStack z :: Move.pileStack z' :: play) = true
  rw [State.playWindow', hstep1]
  refine Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩
  · exact Bool.or_eq_true_iff.mpr (Or.inr hgrowth)
  · rw [if_neg hcond1]
    simp only [State.playWindow', hstep2]
    rw [if_pos hstr]
    refine Bool.and_eq_true_iff.mpr ⟨?_, hpost⟩
    rw [hcargo]
    simp only [decide_eq_true_eq, Card.flipSuit_flipSuit, Card.flipSuit_rank]
    show z.rank.toIdx ≤ S.heights z.suit + 1
    omega

/-- **The adjacent-pair-stacking transfer, the SKEW-HOLDING case**: at a
both-bare licensed state, the play [pileStack z; pileStack z'; rest]
with the first stack's skew HOLDING at S is window'-admitted through
the two stackings, the phase staying PRE, given the tail's
pre-admission.  The content: BOTH stackings are admitted by the SKEW
arm — the first by hypothesis; the second DERIVED (the first's firing
was rung-EXACT, so the partner rung sits at z.rank + 1 ≥ z'.rank), and
the twin rungs EQUALIZE at z.rank + 1 after the two firings (the
"equal-heights" of the sufficiency theorem — a consequence, not a
premise: the exchange's own heights are rfl-equal throughout).  The
tail's pre-admission is the honest boundary (§12's audit): the
remaining pre-conditions are the on-suit deckStack/pileStack SKEWS
(state-dependent — the rungs' co-climb must ALTERNATE: two own-suit
climbs in a row break the second's skew, so only the interleaved
ladder is admitted) and the unstack ANTI-SKEW — whose load-bearing
cases are the pair-card worry-backs (the partner rung can be pushed
past c.rank + 1 by climbing the partner first) and the just-below-pair
worry-backs (the crossed configuration while the partner stays
stacked) — exactly the multi-unstack obstruction of
`TwinCore.rung_eq_unstack_of_ne`'s honest stays. -/
theorem State.playWindow'_adjacent_pair_skew {S W : State} {t z z' : Card}
    {play : List Move}
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.flipSuit = true)
    (hztop : S.board.topOf (Sum.inr t) = some z)
    (hztop' : S.board.topOf (Sum.inr t.flipSuit) = some z')
    (_hbare : S.board.topOf (Sum.inr z) = none ∧ S.board.topOf (Sum.inr z') = none)
    (hskew : z.rank.toIdx ≤ S.heights (Card.flipSuit z).suit)
    (hrun : S.run (Move.pileStack z :: Move.pileStack z' :: play) = some W)
    (hrest : ∀ S₂ : State, S.run [Move.pileStack z, Move.pileStack z'] = some S₂ →
      State.playWindow' z z.suit State.WindowEp.pre S₂ play = true) :
    State.playWindow' z z.suit State.WindowEp.pre S
        (Move.pileStack z :: Move.pileStack z' :: play) = true := by
  obtain ⟨S₁, hstep1, hrest1⟩ := run_cons_elim hrun
  obtain ⟨S₂, hstep2, hrest2⟩ := run_cons_elim hrest1
  have hcargo : z' = z.flipSuit := State.cargo_flipSuit hfit hfit' hztop hztop'
  have hrest' : State.playWindow' z z.suit State.WindowEp.pre S₂ play = true :=
    hrest S₂ (run_cons_intro hstep1 (run_cons_intro hstep2 rfl))
  -- the first firing's rung-exactness (z's own rung before the bump)
  have hd1 := hstep1
  rw [apply_pileStack_iff] at hd1
  obtain ⟨htop1, bq, hbq, hrk1, hS₁⟩ := hd1
  -- the first stack's skew, as a decidability equation
  have hskewd : decide (z.rank.toIdx ≤ S.heights (Card.flipSuit z).suit) = true := by
    simp only [decide_eq_true_eq]
    exact hskew
  -- the second stacking's skew, DERIVED: the first firing was rung-EXACT
  -- (heights z.suit = z.rank), so the partner rung after the bump sits at
  -- z.rank + 1 ≥ z'.rank (the pair shares the rank)
  have hskew2 : z'.rank.toIdx ≤ S₁.heights (Card.flipSuit z').suit := by
    rw [hS₁, hcargo, Card.flipSuit_flipSuit, Card.flipSuit_rank]
    show z.rank.toIdx ≤ (if z.suit = z.suit then S.heights z.suit + 1 else S.heights z.suit)
    rw [if_pos rfl]
    omega
  -- the computation
  show State.playWindow' z z.suit State.WindowEp.pre S
      (Move.pileStack z :: Move.pileStack z' :: play) = true
  rw [State.playWindow', hstep1]
  refine Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩
  · exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr (Or.inr hskewd)))
  · rw [if_pos (Or.inr hskew)]
    rw [State.playWindow', hstep2]
    refine Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩
    · refine Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr (Or.inr ?_)))
      rw [decide_eq_true_eq]
      exact hskew2
    · rw [if_pos (Or.inr hskew2)]
      exact hrest'

/-- **The equal-heights sufficiency theorem** (the last `hsolw'` gap, at
the adjacent-head shape): at a both-bare licensed WF state, a winning
play whose head is the ADJACENT PAIR-STACKING [pileStack z; pileStack
z'; rest] gives `solvableWindow' z z.suit` — the skew-failing branch by
`playWindow'_adjacent_pair` (the tail UNCONDITIONAL: growth → catch-up
→ post), the skew-holding branch by `playWindow'_adjacent_pair_skew`
(the tail's pre-admission carried as the premise — the honest boundary).
The "equal heights" of the title is a CONSEQUENCE, not a premise: the
exchange's heights are rfl-equal throughout (board-only), and the two
stackings' rung-exact firings EQUALIZE the twin suits' rungs at
z.rank + 1 — from which the tail's on-suit skews hold for every
INTERLEAVED rung-climber (the co-climb alternates) and the anti-skew
for the pair-card worry-backs holds at the equalized state itself.
The remaining residual — the tail premise, carried as a premise in
the skew-holding branch — is precisely the ON-PAIR foundation moves'
state-dependent arms (§12's audit): the on-suit stacks' skews (the
co-climb must alternate), the pair-member and just-below-pair
worry-backs' anti-skews (the crossed configurations — the
multi-unstack obstruction), and nothing else (every other kind is
state-independently admitted — `State.playWindow'_tail_of_eq_heights`);
the non-pair non-adjacent worry-backs were discharged by the third
disjunct (`rung_eq_unstack_of_ne`, 12259ae).  The ADJACENCY residual
is closed by the re-scheduling (§11, `playWindow'_of_rescheduled`). -/
theorem State.playWindow'_of_eq_heights {st : State} {t z z' : Card}
    (_hwf : st.WF)
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.flipSuit = true)
    (hztop : st.board.topOf (Sum.inr t) = some z)
    (hztop' : st.board.topOf (Sum.inr t.flipSuit) = some z')
    (hbare : st.board.topOf (Sum.inr z) = none ∧ st.board.topOf (Sum.inr z') = none)
    (hplay : ∃ (play : List Move) (W : State),
      st.run (Move.pileStack z :: Move.pileStack z' :: play) = some W ∧ W.isWin = true ∧
      (¬ (z.rank.toIdx ≤ st.heights (Card.flipSuit z).suit) ∨
        ∀ S₂ : State, st.run [Move.pileStack z, Move.pileStack z'] = some S₂ →
          State.playWindow' z z.suit State.WindowEp.pre S₂ play = true))
    (_hsol : st.solvableFrom) :
    st.solvableWindow' z z.suit := by
  obtain ⟨play, W, hrun, hwin, hcase⟩ := hplay
  refine ⟨Move.pileStack z :: Move.pileStack z' :: play, W, hrun, hwin, ?_⟩
  rcases hcase with hfailskew | htail
  · exact State.playWindow'_adjacent_pair hfit hfit' hztop hztop' hbare hfailskew hrun
  · by_cases hskew : z.rank.toIdx ≤ st.heights (Card.flipSuit z).suit
    · exact State.playWindow'_adjacent_pair_skew hfit hfit' hztop hztop' hbare hskew hrun htail
    · exact State.playWindow'_adjacent_pair hfit hfit' hztop hztop' hbare hskew hrun

/-- **The direct correspondence at a both-bare licensed state**: the
exchange is the source's twin-correlated partner at the CARGO pair —
the board clause by the covers lemma (§1: the license's covers + both
cargo seats bare identify the seat exchange with `mapByTwin z`), the
other fields rfl (the exchange is board-only), and the per-card
stacked-set invariant because both cargos are seated — hence visible,
hence below their rungs by `founds_gone` — so the cross-cases (z and
z') are false on both sides.  The mirror's heights are the source's
(rfl), bounded by 13 (WF's `heights_le`). -/
theorem State.twinCorr_exchangeTwinCargo {st : State} {t z z' : Card}
    (hwf : st.WF)
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.flipSuit = true)
    (hztop : st.board.topOf (Sum.inr t) = some z)
    (hztop' : st.board.topOf (Sum.inr t.flipSuit) = some z')
    (hbare : st.board.topOf (Sum.inr z) = none ∧ st.board.topOf (Sum.inr z') = none) :
    State.TwinCorr (Card.swapTwin z) z.suit st (st.exchangeTwinCargo t) ∧
      (∀ s, (st.exchangeTwinCargo t).heights s ≤ 13) := by
  have hρ : Card.IsTwinMap (Card.swapTwin z) := Card.IsTwinMap.swapTwin z
  have hcargo : z' = z.flipSuit := State.cargo_flipSuit hfit hfit' hztop hztop'
  have hzne : z ≠ t ∧ z ≠ t.flipSuit := Card.ne_pair_of_canSitOn hfit
  -- the cargos are seated (the covers), hence visible
  have hvisz : st.isVis z = true := by
    show (st.board.bottomOf z).isSome = true
    rw [(Board.bottomOf_eq st.board z (Sum.inr t)).mpr hztop]
    rfl
  have hvisz' : st.isVis (Card.flipSuit z) = true := by
    show (st.board.bottomOf (Card.flipSuit z)).isSome = true
    rw [← hcargo, (Board.bottomOf_eq st.board z' (Sum.inr t.flipSuit)).mpr hztop']
    rfl
  have hheights : (st.exchangeTwinCargo t).heights = st.heights :=
    State.exchangeTwinCargo_heights st t
  -- both cargos sit below their rungs (visible + founds_gone)
  have hboundz : st.heights z.suit ≤ z.rank.toIdx := by
    cases Nat.lt_or_ge (z.rank.toIdx) (st.heights z.suit) with
    | inl hlt =>
        have hvis := (hwf.founds_gone z hlt).1
        rw [hvis] at hvisz
        exact absurd hvisz (by simp)
    | inr h => exact h
  have hboundz' : st.heights (Card.flipSuit z).suit ≤ z.rank.toIdx := by
    have hrk : (Card.flipSuit z).rank.toIdx = z.rank.toIdx := by
      rw [Card.flipSuit_rank]
    cases Nat.lt_or_ge ((Card.flipSuit z).rank.toIdx) (st.heights (Card.flipSuit z).suit) with
    | inl hlt =>
        have hvis := (hwf.founds_gone (Card.flipSuit z) hlt).1
        rw [hvis] at hvisz'
        exact absurd hvisz' (by simp)
    | inr h => omega
  refine ⟨⟨⟨hρ, ?_, State.exchangeTwinCargo_deal st t,
    State.exchangeTwinCargo_depths st t, State.exchangeTwinCargo_stock st t,
    State.exchangeTwinCargo_drawStep st t, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro c h1 h2
    refine Card.swapTwin_of_ne ?_ ?_
    · intro hcon; rw [hcon] at h1; exact h1 rfl
    · intro hcon; rw [hcon] at h2; exact h2 rfl
  · intro s _ _
    exact congrFun hheights s
  · intro c hon
    rcases hρ.pair c with hc | hc
    · rw [hc, congrFun hheights c.suit]
    · have hcpair : c = z ∨ c = Card.flipSuit z := by
        by_cases h1 : c = z
        · exact Or.inl h1
        · by_cases h2 : c = Card.flipSuit z
          · exact Or.inr h2
          · exfalso
            have hfix := Card.swapTwin_of_ne (t := z) h1 h2
            rw [hfix] at hc
            exact Card.flipSuit_ne c hc.symm
      rcases hcpair with hc2 | hc2
      · rw [hc2] at hc
        rw [hc2, hc, congrFun hheights (Card.flipSuit z).suit, Card.flipSuit_rank]
        constructor <;> intro hlt <;> omega
      · rw [hc2] at hc
        rw [hc2, hc, Card.flipSuit_flipSuit, congrFun hheights z.suit, Card.flipSuit_rank]
        constructor <;> intro hlt <;> omega
  · intro b
    have hbd : (st.exchangeTwinCargo t).board = st.board.mapByTwin z := by
      rw [State.exchangeTwinCargo_board,
        Board.exchangeTwin_eq_mapByTwin_of_covers hztop hztop' hcargo hzne hbare]
    rw [hbd, Board.mapByTwin_eq_mapByRho, Board.mapByRho_topOf]
  · intro s
    have h13 : ∀ s', st.heights s' ≤ 13 := hwf.heights_le
    rw [hheights]
    exact h13 s

/-- **The direct merge bridge — the STRENGTHENED window at a both-bare
licensed state**: NO merge analysis (no ROOT/DEEP dispatch, no rider
transfer, no detour, no hdet) — the merge move is just one legal move of
the winning line; the strengthened window (TwinReplay's
`solvable_of_twinCorr_window'`) replays the source's ENTIRE
window'-admitted play (the merge included — a `pilePile` is
unconditionally admitted in the pre-episode phase, composed by
`solvableWindow'_cons_pilePile`) through the direct correspondence.
The window's added premises are all discharged: `hMle` by the
correspondence lemma, `hhid`/`hstock` by the WF+covers derivation; what
REPLACES plain solvability is `hsolw'` — the successor's winning play
must be window'-admitted (the weakened condition: the stack skew is
GONE — misaligned pair-stacks route to the growth; the remaining
exclusions are the pair-deckStack (vacuous at licensed states — see
`apply_deckStack_ne_of_vis`), the pre-episode unstack anti-skew, and
the mid-episode tableau moves).  The route never inspects the move: ANY
legal move of a both-bare licensed WF state with a window'-solvable
successor transfers.  The DEEP corners (riders on z', the landing among
them) fall outside this regime — the correspondence itself dies there —
and are handled either by the §5/§7 scaffolds or by the double-clearing
premise (`ExchangeDoubleClear` below), which restores this direct
route. -/
theorem State.solvable_of_exchange_merge_direct {st a₁ : State} {t z z' c : Card} {b : Base}
    (hwf : st.WF)
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.flipSuit = true)
    (hztop : st.board.topOf (Sum.inr t) = some z)
    (hztop' : st.board.topOf (Sum.inr t.flipSuit) = some z')
    (hbare : st.board.topOf (Sum.inr z) = none ∧ st.board.topOf (Sum.inr z') = none)
    (hstep : st.apply (Move.pilePile c b) = some a₁)
    (hsolw' : a₁.solvableWindow' z z.suit) :
    (st.exchangeTwinCargo t).solvableFrom := by
  obtain ⟨hcorr, hmle⟩ :=
    State.twinCorr_exchangeTwinCargo hwf hfit hfit' hztop hztop' hbare
  obtain ⟨hhid, hstock⟩ :=
    State.swapTwin_hid_stock_of_covers hwf hfit hfit' hztop hztop'
  have hwin' : st.solvableWindow' z z.suit :=
    State.solvableWindow'_cons_pilePile hstep hsolw'
  exact State.solvable_of_twinCorr_window' hcorr hmle hwf hhid hstock hwin'

/-- **The double-cleared normalization premise** (the direct route's
honest boundary at the deep corners): the source's winning line can be
scheduled so that a prefix π clears the riders on BOTH cargo stacks —
reaching a state S₀ at which the license's covers still hold, both z
and z' are bare, and the SAME merge move re-fires (the landing d riding
along with the cleared z'-riders, still bare, wherever the clearing
left it — the merge's landing is the CARD d's seat, not a position) with
a STRENGTHENED-WINDOW-solvable successor — and π replays verbatim in
the exchanged game.  This is `ExchangeRiderPrefixRooted`'s shape with
the z'-side clearing added; the successor's premise is
`solvableWindow'`-shaped at z (the weakened play condition the
strengthened window consumes — the plain-solvability transfer is the
L1/O0 residue); the discharge of the whole schedule is the same
L1/O3-shaped play normalization and exchange-cleanliness residue —
NOT the detour machinery (`hdet` and the two-ply are superseded by this
route). -/
def State.ExchangeDoubleClear (st : State) (t z z' c : Card) (b : Base) : Prop :=
  ∃ (π : List Move) (S₀ : State),
    st.run π = some S₀ ∧
    (st.exchangeTwinCargo t).run π = some (S₀.exchangeTwinCargo t) ∧
    S₀.WF ∧
    canSitOn z t = true ∧ canSitOn z' t.flipSuit = true ∧
    S₀.board.topOf (Sum.inr t) = some z ∧
    S₀.board.topOf (Sum.inr t.flipSuit) = some z' ∧
    S₀.board.topOf (Sum.inr z) = none ∧
    S₀.board.topOf (Sum.inr z') = none ∧
    (∃ a₁' : State, S₀.apply (Move.pilePile c b) = some a₁' ∧
      a₁'.solvableWindow' z z.suit)

/-- **The rooted direct bridge** — [H′] closed by the STRENGTHENED
window, modulo the double-clearing premise: the mirror replays the
clearing prefix (the premise's verbatim-replay clause), landing at the
exchanged cleared state, where the direct bridge applies — the ENTIRE
merge analysis (the FIT two-ply, the HOLE detour, `hdet`) is
superseded.  The
fixed premises `_hwf _h _hstep _hc _hland _hsol` are the [H′] shape
(signature fidelity, consumed by the premise's discharge).  The theorem
is MOVE-AGNOSTIC in c (only the premise's re-firing move mentions it),
so the [H]-deep case is the same wrapper at c ≠ t. -/
theorem State.solvable_of_exchange_merge_rooted_direct {st a₁ : State} {t z z' c : Card}
    {b : Base}
    (hdcl : st.ExchangeDoubleClear t z z' c b)
    (_hwf : st.WF) (_h : st.twinLicensed t)
    (_hstep : st.apply (Move.pilePile c b) = some a₁) (_hc : c = t)
    (_hland : ∃ d, b = Sum.inr d ∧ d ∈ st.board.aboveOf z')
    (_hsol : a₁.solvableFrom) :
    (st.exchangeTwinCargo t).solvableFrom := by
  obtain ⟨π, S₀, hrunπ, hrunπX, hwf₀, hfit, hfit', hztop, hztop', hbz, hbz', a₁', hstep₀, hsolw'₀⟩ :=
    hdcl
  have hres := State.solvable_of_exchange_merge_direct hwf₀ hfit hfit' hztop hztop'
    ⟨hbz, hbz'⟩ hstep₀ hsolw'₀
  obtain ⟨π', W, hrun', hwin'⟩ := hres
  exact ⟨π ++ π', W, run_append_some hrunπX hrun', hwin'⟩

/-! ## §9. The double-clearing premise, reduced — the scheduled form

The premise attack's verdict (probed at the blockade witnesses,
dblclear.lean): NO refuting witness — the hard-blockade failure modes
dissolve at the solvability hypothesis.  The cycle construction (riders
circularly blocking each other's candidate tops, anchors filled, rungs
too low) can always be dissolved through the stock: draws and deckStacks
are exchange-clean, a rider's suit is DISJOINT from both cargos' suits
(the fit's color structure: a rider on a cargo is opposite-colored to
it, and the two cargos share a color), so no rung-raiser is ever a
protected card, and the twin shares at most the suit, never the rung
(its rank sits one above the cargo's).  Both known blockades
(detour.lean's non-king, detour2.lean's king) are dissolved by ONE clean
stack each; the field-wise replay check at the first witness validates
the premise's verbatim-replay clause empirically.  What stays is the
SCHEDULING — pulling the clearings before the merge and keeping the
merge's successor solvable — the L1/O3 commutation, exactly hrp's
residue extended to the z'-side.  So ExchangeDoubleClear is NOT provable
at WF without the interleaving machinery; below it is REDUCED: the
hardest-looking clause (the mirror's verbatim replay of the clearing
prefix) is DERIVED from per-move stacking-cleanliness, leaving the
scheduled form — the clearings, the both-bare outcome, and the merge's
re-firing with a WINDOW-solvable successor — as the honest residue (the
window consumes at the both-bare state, where hhid/hstock derive from
that state's WF + the surviving covers, which the license-carrying run
lemmas already provide). -/

/-- **The stacking-clean condition for the double-clearing prefix**: a
`pileStack q` with q off the protected pair set {t, t', z, z'}.  Unlike
§4's `CleanAt`, the RIDER is allowed — the double-clear's whole point is
that the riders leave — so the invariant carried is the license ALONE
(the riders' own seatings are exactly what changes). -/
def State.CleanStack (m : Move) (t z z' : Card) : Prop :=
  ∃ q : Card, m = Move.pileStack q ∧
    q ≠ t ∧ q ≠ t.flipSuit ∧ q ≠ z ∧ q ≠ z'

/-- **The stacking step's license transfer**: a `CleanStack` move
preserves the pinned license — the board only loses q (the detach at q's
own base), every other card's base survives (`bottomOf_detach_ne`), and
the no-braid walks only shrink.  The twin seats' hosting is untouched:
q is neither cargo, and a cargo's base is not q's (the seats are
occupied by the cargos themselves). -/
theorem State.twinLicensedAt_apply_pileStack_off {st a₁ : State} {t z z' q : Card}
    (hlic : State.TwinLicensedAt st t z z')
    (hq : q ≠ t ∧ q ≠ t.flipSuit ∧ q ≠ z ∧ q ≠ z')
    (hstep : st.apply (Move.pileStack q) = some a₁) :
    State.TwinLicensedAt a₁ t z z' := by
  obtain ⟨hvis, hvis', h₀, h₀', hfit, hfit', hnb, hnb'⟩ := hlic
  obtain ⟨hqt, hqt', hqz, hqz'⟩ := hq
  have happ := hstep
  rw [apply_pileStack_iff] at happ
  obtain ⟨htop, b, hb, hrk, rfl⟩ := happ
  have hbtopq : st.board.topOf b = some q := (Board.bottomOf_eq st.board q b).mp hb
  refine ⟨?_, ?_, ?_, ?_, hfit, hfit', ?_, ?_⟩
  · show ((st.board.detach b).bottomOf t).isSome = true
    rw [bottomOf_detach_ne hbtopq (fun h => hqt h.symm)]
    exact hvis
  · show ((st.board.detach b).bottomOf t.flipSuit).isSome = true
    rw [bottomOf_detach_ne hbtopq (fun h => hqt' h.symm)]
    exact hvis'
  · show (st.board.detach b).bottomOf z = some (Sum.inr t)
    rw [bottomOf_detach_ne hbtopq (fun h => hqz h.symm)]
    exact h₀
  · show (st.board.detach b).bottomOf z' = some (Sum.inr t.flipSuit)
    rw [bottomOf_detach_ne hbtopq (fun h => hqz' h.symm)]
    exact h₀'
  · show t ∉ (st.board.detach b).aboveOf z ∧ t.flipSuit ∉ (st.board.detach b).aboveOf z
    constructor
    · intro hmem
      exact hnb.1 (Board.aboveOf_sub_detach 52 z [] t hmem)
    · intro hmem
      exact hnb.2 (Board.aboveOf_sub_detach 52 z [] t.flipSuit hmem)
  · show t ∉ (st.board.detach b).aboveOf z' ∧ t.flipSuit ∉ (st.board.detach b).aboveOf z'
    constructor
    · intro hmem
      exact hnb'.1 (Board.aboveOf_sub_detach 52 z' [] t hmem)
    · intro hmem
      exact hnb'.2 (Board.aboveOf_sub_detach 52 z' [] t.flipSuit hmem)

/-- **The run-level stacking-clean replay**: a CleanStack clearing prefix
replays verbatim in the exchanged game (the successors staying
exchanged), the pinned license riding to the end state. -/
theorem State.exchangeTwinCargo_run_cleanStack {st st' : State} {t z z' : Card}
    {π : List Move}
    (hlic : State.TwinLicensedAt st t z z')
    (hclean : ∀ m ∈ π, State.CleanStack m t z z')
    (hrun : st.run π = some st') :
    (st.exchangeTwinCargo t).run π = some (st'.exchangeTwinCargo t) ∧
      State.TwinLicensedAt st' t z z' := by
  induction π generalizing st st' with
  | nil =>
      have hst := run_nil_elim hrun
      subst hst
      exact ⟨rfl, hlic⟩
  | cons m ms ih =>
      obtain ⟨q, rfl, hqt, hqt', hqz, hqz'⟩ := hclean m (by simp)
      obtain ⟨S₁, hap, hrest⟩ := run_cons_elim hrun
      have hlic₁ := State.twinLicensedAt_apply_pileStack_off hlic ⟨hqt, hqt', hqz, hqz'⟩ hap
      obtain ⟨hvis, hvis', h₀, h₀', hfit, hfit', hnb, hnb'⟩ := hlic
      have hfire : (st.exchangeTwinCargo t).apply (Move.pileStack q)
          = some (S₁.exchangeTwinCargo t) :=
        State.exchangeTwinCargo_step_pileStack h₀ h₀' ⟨hqz, hqz'⟩ ⟨hqt, hqt'⟩ hap
      obtain ⟨hrunX, hlic'⟩ :=
        ih hlic₁ (fun m' hm' => hclean m' (List.mem_cons_of_mem _ hm')) hrest
      exact ⟨run_cons_intro hfire hrunX, hlic'⟩

/-- **The double-clearing premise, REDUCED to the scheduled form**: the
premise's hardest-looking clause — the mirror's verbatim replay of the
clearing prefix — is DERIVED here from the per-move stacking-cleanliness
(the run-level replay above); what stays scheduled is the outcome (both
cargo seats bare) and the merge's re-firing with a WINDOW-solvable
successor (the real window's play condition — the plain-solvability
transfer is the L1/O0 residue).  This is the strongest conditional
form: the L1/O3 scheduling residue is exactly the extraction of such a
schedule from the winning play (the commutation `rider_clear_sched`
below is the single-swap building block).  Detach-based clearings (the
z'-detour of the deep corners) extend the kit the same way — compose
this run lemma with `exchangeTwinCargo_step_pilePile` at the prefix's
end, as §5/§7's HOLE routes already do inline. -/
theorem State.exchangeDoubleClear_of_sched {st : State} {t z z' c : Card} {b : Base}
    (hwf : st.WF)
    (hlic : State.TwinLicensedAt st t z z')
    {π : List Move} {S₀ : State}
    (hrun : st.run π = some S₀)
    (hclean : ∀ m ∈ π, State.CleanStack m t z z')
    (hbare : S₀.board.topOf (Sum.inr z) = none ∧ S₀.board.topOf (Sum.inr z') = none)
    (hmerge : ∃ a₁' : State, S₀.apply (Move.pilePile c b) = some a₁' ∧
      a₁'.solvableWindow' z z.suit) :
    st.ExchangeDoubleClear t z z' c b := by
  obtain ⟨hrunX, hlic₀⟩ := State.exchangeTwinCargo_run_cleanStack hlic hclean hrun
  obtain ⟨hvis, hvis', h₀, h₀', hfit, hfit', hnb, hnb'⟩ := hlic₀
  exact ⟨π, S₀, hrun, hrunX, State.wf_run hwf hrun, hfit, hfit',
    (Board.bottomOf_eq S₀.board z (Sum.inr t)).mp h₀,
    (Board.bottomOf_eq S₀.board z' (Sum.inr t.flipSuit)).mp h₀',
    hbare.1, hbare.2, hmerge⟩

/-- **The scheduled direct bridge**: the [H′] shape closed from the
SCHEDULE alone — the clearing prefix's mirror-replay is derived, the
REAL window applies at the both-bare end state (the license's covers
surviving the clean prefix), and the mirror's winning play is the
replayed prefix followed by the window's translated play.  The residual
hypotheses are exactly the schedule: the clean prefix running to a
both-bare licensed state at which the merge re-fires with a
window-solvable successor. -/
theorem State.solvable_of_exchange_merge_rooted_sched {st a₁ : State} {t z z' c : Card}
    {b : Base}
    (hwf : st.WF) (hlic : State.TwinLicensedAt st t z z')
    {π : List Move} {S₀ : State}
    (hrun : st.run π = some S₀)
    (hclean : ∀ m ∈ π, State.CleanStack m t z z')
    (hbare : S₀.board.topOf (Sum.inr z) = none ∧ S₀.board.topOf (Sum.inr z') = none)
    (hstep : S₀.apply (Move.pilePile c b) = some a₁)
    (hsolw' : a₁.solvableWindow' z z.suit) :
    (st.exchangeTwinCargo t).solvableFrom := by
  obtain ⟨hrunX, hlic₀⟩ := State.exchangeTwinCargo_run_cleanStack hlic hclean hrun
  obtain ⟨hvis, hvis', h₀, h₀', hfit, hfit', hnb, hnb'⟩ := hlic₀
  have hztop₀ : S₀.board.topOf (Sum.inr t) = some z :=
    (Board.bottomOf_eq S₀.board z (Sum.inr t)).mp h₀
  have hztop₀' : S₀.board.topOf (Sum.inr t.flipSuit) = some z' :=
    (Board.bottomOf_eq S₀.board z' (Sum.inr t.flipSuit)).mp h₀'
  have hres := State.solvable_of_exchange_merge_direct (State.wf_run hwf hrun)
    hfit hfit' hztop₀ hztop₀' hbare hstep hsolw'
  obtain ⟨π', W, hrun', hwin'⟩ := hres
  exact ⟨π ++ π', W, run_append_some hrunX hrun', hwin'⟩

/-- **The rider-stacking commutation, with the firing transfer**: a
rider's clean `pileStack q` can be pulled EARLIER past a following
`pilePile c b'` whose touch-set is disjoint from the stacking's at st
(neither q's seat nor the merge's landing/detach bases nor the run
overlap), and whose root does not sit on q (`hroot` — else the stacking
could not fire first).  The SWAPPED order's firing is DERIVED here: the
stacking's guards at st are the merge's invariants (q's bareness
survives the merge's two-seat edit — the landing cannot be q's own
seat, for then q would not be bare after; the detach base is not it, by
hroot — q's base and rung are untouched by construction), and the
merge's guards at the stacked state are the stacking's (the run's walk
only shrinks, the landing and root bases are untouched, the rung is
heights-blind).  Both orders land on the SAME state (Commutation's
`comm_pileStack_pilePile`), so the run reaches the same winner.  This
is the L1/O0 building block complete: with the disjointness + hroot,
the swap is unconditional in the run. -/
theorem State.rider_clear_sched {st w : State} {q c : Card} {b' : Base} {π : List Move}
    (hdisj : disjointTouch ((Move.pileStack q).touch st) ((Move.pilePile c b').touch st))
    (hroot : st.board.bottomOf c ≠ some (Sum.inr q))
    (hrun : st.run (Move.pilePile c b' :: Move.pileStack q :: π) = some w) :
    st.run (Move.pileStack q :: Move.pilePile c b' :: π) = some w := by
  obtain ⟨s₁, happ1, hrest1⟩ := run_cons_elim hrun
  obtain ⟨s₂, hps2, hrest2⟩ := run_cons_elim hrest1
  -- the merge's shape at st (substituting s₁ := {st with board := bd})
  have hdapp := happ1
  rw [apply_pilePile_iff] at hdapp
  obtain ⟨β₀, hbotc, hne, hcmr, bd, hatt, rfl⟩ := hdapp
  -- the stacking's shape at s₁ (substituting s₂)
  have hdps := hps2
  rw [apply_pileStack_iff] at hdps
  obtain ⟨htopq, bq, hbq, hrkq, rfl⟩ := hdps
  have htopq' : bd.topOf (Sum.inr q) = none := htopq
  have hbqbd : bd.bottomOf q = some bq := hbq
  have hrkq' : q.rank.toIdx = st.heights q.suit := hrkq
  -- q ≠ c (the disjointness's card half, raw) and q's base at st survives
  -- the merge (the run untouched: q ≠ c)
  have hqc : q ≠ c := by
    intro hcon
    exact hdisj.2 q (by simp [Move.touch]) (by rw [hcon]; simp [Move.touch])
  have hbotqst : st.board.bottomOf q = some bq := by
    have h := State.apply_pilePile_bottomOf happ1 hqc
    rw [← h]; exact hbqbd
  have htopbq : st.board.topOf bq = some q := (Board.bottomOf_eq st.board q bq).mp hbotqst
  -- the touch sets, spelled out at the two bases
  have hPSt : (Move.pileStack q).touch st = ([bq], [q]) := by
    simp only [Move.touch, hbotqst, Option.toList_some]
  have hPPt : (Move.pilePile c b').touch st = (b' :: [β₀], c :: st.board.aboveOf c) := by
    simp only [Move.touch, hbotc, Option.toList_some]
  have hdisj₀ := hdisj
  rw [hPSt, hPPt] at hdisj
  have hbqb' : bq ≠ b' := fun hcon => hdisj.1 bq (by simp) (by rw [hcon]; simp)
  have hbqβ₀ : bq ≠ β₀ := fun hcon => hdisj.1 bq (by simp) (by simp [hcon])
  -- the merge's landing is not q's own seat (else q would not be bare after)
  have hb'q : b' ≠ Sum.inr q := by
    intro hcon
    rw [hcon] at hatt
    have hc1 : bd.topOf (Sum.inr q) = some c := Board.attach_topOf _ _ _ hatt
    rw [hc1] at htopq'
    exact absurd htopq' (by simp)
  -- and the detach base is not q's own seat (the root does not sit on q)
  have hβ₀q : β₀ ≠ Sum.inr q := by
    intro hcon
    rw [hcon] at hbotc
    exact hroot hbotc
  -- (1) the stacking's firing at st: q's bareness survived the merge
  have htopqst : st.board.topOf (Sum.inr q) = none := by
    have h1 : bd.topOf (Sum.inr q) = none := htopq
    rw [Board.attach_topOf_ne _ _ _ hatt (fun hcon => hb'q hcon.symm),
      Board.detach_topOf_ne _ _ _ (fun hcon => hβ₀q hcon.symm)] at h1
    exact h1
  obtain ⟨t₁, hfireS⟩ : ∃ t₁, st.apply (Move.pileStack q) = some t₁ :=
    ⟨_, apply_pileStack_iff.mpr ⟨htopqst, bq, hbotqst, hrkq', rfl⟩⟩
  -- pin t₁ to its successor form (the stacking's state equation)
  have hdpsS := hfireS
  rw [apply_pileStack_iff] at hdpsS
  obtain ⟨-, bq₂, hbq₂, -, ht₁eq⟩ := hdpsS
  have hbqeq : bq₂ = bq := Option.some.inj (hbq₂.symm.trans hbotqst)
  rw [hbqeq] at ht₁eq
  subst ht₁eq
  -- (2) the merge's re-firing at the stacked state: the root's base, the
  -- landing, the guard, and the attach all survive the one-seat edit
  have hbotct₁ : (st.board.detach bq).bottomOf c = some β₀ := by
    rw [bottomOf_detach_ne htopbq (fun h => hqc h.symm)]
    exact hbotc
  have hcpst : st.canPlace c b' = true := by
    simp only [State.canMoveRun, Bool.and_eq_true_iff] at hcmr
    exact hcmr.1
  have hcpt₁ : ({st with board := st.board.detach bq, heights := fun s => if s = q.suit then st.heights s + 1 else st.heights s}).canPlace c b' = true := by
    cases b' with
    | inl a =>
        have h2 := canPlace_inl_iff.mp hcpst
        refine canPlace_inl_iff.mpr ⟨?_, h2.2⟩
        have h1 : (st.board.detach bq).topOf (Sum.inl a) = st.board.topOf (Sum.inl a) :=
          Board.detach_topOf_ne _ _ _ (fun hcon => hbqb' hcon.symm)
        rw [h1]
        exact h2.1
    | inr d =>
        have h3 := canPlace_inr_iff.mp hcpst
        refine canPlace_inr_iff.mpr ⟨?_, ?_, h3.2.2⟩
        · have h1 : (st.board.detach bq).topOf (Sum.inr d) = st.board.topOf (Sum.inr d) :=
            Board.detach_topOf_ne _ _ _ (fun hcon => hbqb' hcon.symm)
          rw [h1]
          exact h3.1
        · have hdq : d ≠ q := fun hcon => hb'q (by rw [hcon])
          have h2 : (st.board.detach bq).bottomOf d = st.board.bottomOf d :=
            bottomOf_detach_ne htopbq (fun h => hdq h)
          show ((st.board.detach bq).bottomOf d).isSome = true
          rw [h2]
          exact h3.2.1
  have hcmrt₁ : ({st with board := st.board.detach bq, heights := fun s => if s = q.suit then st.heights s + 1 else st.heights s}).canMoveRun c b' = true := by
    cases b' with
    | inl a => simp only [State.canMoveRun, hcpt₁]; rfl
    | inr d =>
        refine canMoveRun_inr_iff.mpr ⟨hcpt₁, ?_⟩
        show ((st.board.detach bq).aboveOf c).contains d = false
        cases hcon : ((st.board.detach bq).aboveOf c).contains d with
        | false => rfl
        | true =>
            have hmem : d ∈ (st.board.detach bq).aboveOf c := (List.contains_iff_mem).mp hcon
            have hmem' : d ∈ st.board.aboveOf c :=
              Board.aboveOf_sub_detach 52 c [] d hmem
            have hfalse := (canMoveRun_inr_iff.mp hcmr).2
            rw [List.contains_iff_mem.mpr hmem'] at hfalse
            exact absurd hfalse (by simp)
  -- the attach: the stacked board's landing seat is free and the root is off it
  have hfree₀ : (st.board.detach β₀).topOf b' = none :=
    (Board.attach_eq_some_iff _ _ _).mp (by rw [hatt]; simp) |>.1
  have htopβ₀q : (st.board.detach β₀).topOf bq = some q := by
    rw [Board.detach_topOf_ne _ _ _ hbqβ₀]
    exact htopbq
  have hne' : ((st.board.detach bq).detach β₀).attach b' c ≠ none := by
    refine (Board.attach_eq_some_iff _ _ _).mpr ⟨?_, ?_⟩
    · rw [detach_detach_comm hbqβ₀, Board.detach_topOf_ne _ _ _
        (fun hcon => hbqb' hcon.symm)]
      exact hfree₀
    · rw [detach_detach_comm hbqβ₀,
        bottomOf_detach_ne htopβ₀q (fun h => hqc h.symm),
        Board.bottomOf_detach_self ((Board.bottomOf_eq st.board c β₀).mp hbotc)]
  obtain ⟨bd', hatt'⟩ : ∃ bd', ((st.board.detach bq).detach β₀).attach b' c = some bd' := by
    cases htt : ((st.board.detach bq).detach β₀).attach b' c with
    | none => exact absurd htt hne'
    | some bd'' => exact ⟨bd'', rfl⟩
  obtain ⟨t₂, hfireM⟩ : ∃ t₂, ({st with board := st.board.detach bq, heights := fun s => if s = q.suit then st.heights s + 1 else st.heights s}).apply (Move.pilePile c b') = some t₂ :=
    ⟨_, apply_pilePile_iff.mpr ⟨β₀, hbotct₁, hne, hcmrt₁, bd', hatt', rfl⟩⟩
  -- both orders fire and agree; reassemble the swapped run
  have hbind₁ : (st.apply (Move.pileStack q) >>= fun s => s.apply (Move.pilePile c b'))
      = some t₂ := Option.bind_eq_some_iff.mpr ⟨_, hfireS, hfireM⟩
  have hbind₂ := Option.bind_eq_some_iff.mpr ⟨_, happ1, hps2⟩
  have hcomm := comm_pileStack_pilePile hdisj₀ hbind₁ hbind₂
  subst hcomm
  exact run_cons_intro hfireS (run_cons_intro hfireM hrest2)

/-! ## §10. The constructive double-clearing — the rung-raising route

The constructive lead, probed (dblclear2.lean): the blockade witness
REBUILT with the blocker's rung NOT yet arrived (heart height 8) and the
missing rung card ♥9 as the state stock's waste top.  The CONSTRUCTIVE
schedule — no extraction from a winning play — wins on BOTH sides:
(a) RAISE the rung (`deckStack ♥9`: a stock card, hence never a
protected card — WF's `vis_off_cycle` keeps the visible protected four
out of the stock; draws/deckStacks are UNCONDITIONALLY exchange-clean,
the step kit carries them premise-free);
(b) STACK the blocker (`pileStack ♥10`: CleanStack);
(c) THE z'-DETOUR (the validated iterated repair);
(d) the merge, then the climbs.
Below: (i) the rung-raiser disjointness — the rank-ladder arithmetic
behind "no rung-raiser is ever a protected card"; (ii) the MIXED
scheduled form of `ExchangeDoubleClear` — the constructive schedule's
shape (a CleanStack prefix, then the z'-detour), with the mirror's
verbatim replay DERIVED for the whole mixed prefix.  The honest
boundary: the schedule's EXISTENCE at arbitrary WF+licensed+solvable
states (the reachability of the raisers, the termination of the
blocker-chain recursion) and the successor's solvability stay premises
— the constructive evidence covers the probed geometries. -/

/-- **The rung-raiser disjointness** (the constructive route's core
arithmetic — dblclear2.lean's (i)-check): every rung-raiser of a
FIT-SEATED rider on a cargo is off the protected four {t, t', z, z'}.
The ladder: the raiser sits strictly below the rider (the rung), the
rider strictly below the cargo (the fit), the cargo strictly below the
twin (the license's fit), and the cargo pair shares the rank — so the
raiser's rank is strictly below all four protected ranks.  (The color
refinement: the rider's color opposes the cargo's, so the rider's suit
differs from both cargos' suits outright; the twin may share the
rider's suit but never the rung.) -/
theorem State.rung_raiser_off_pairs {x r z z' t : Card}
    (hx : x.rank.toIdx < r.rank.toIdx)
    (hr : r.rank.toIdx + 1 = z.rank.toIdx)
    (hzt : z.rank.toIdx + 1 = t.rank.toIdx)
    (hz' : z'.rank.toIdx = z.rank.toIdx) :
    x ≠ t ∧ x ≠ t.flipSuit ∧ x ≠ z ∧ x ≠ z' := by
  have ht'r : t.flipSuit.rank.toIdx = t.rank.toIdx := by
    rw [Card.flipSuit_rank]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hcon
    have h1 := congrArg (fun c => c.rank.toIdx) hcon
    omega
  · intro hcon
    have h1 := congrArg (fun c => c.rank.toIdx) hcon
    omega
  · intro hcon
    have h1 := congrArg (fun c => c.rank.toIdx) hcon
    omega
  · intro hcon
    have h1 := congrArg (fun c => c.rank.toIdx) hcon
    omega

/-- **The double-clearing premise, the MIXED scheduled form** — the
constructive route's shape (dblclear2.lean's validated schedule): a
CleanStack prefix (the rung-raisings and blocker-stackings) reaching a
state where the first rider r₁ still rides z'; then the z'-DETOUR (the
whole rider run, the landing d riding along, still bare), emptying z'
and leaving BOTH cargo seats bare with the license intact.  The
mirror's verbatim replay is DERIVED for the WHOLE mixed prefix — the
stacking part by the run-level lemma (the license riding), the detour
by the clean-run mirror step (the no-braids plus r₁'s direct seat under
z' giving the twins-off-r₁-run premise).  This strengthens
`exchangeDoubleClear_of_sched` to the actual [H′] geometry — the z'-side
clearing is necessarily a DETACH, for the landing d must stay seated
for the merge's re-firing (the riders cannot all stack away).  The
residue stays: the schedule's existence and the successor's
solvability. -/
theorem State.exchangeDoubleClear_of_sched_mixed {st : State} {t z z' c : Card} {b : Base}
    (hwf : st.WF) (hlic : State.TwinLicensedAt st t z z')
    {πₛ : List Move} {Sₛ S₀ : State} {r₁ : Card} {β : Base}
    (hrunₛ : st.run πₛ = some Sₛ)
    (hclean : ∀ m ∈ πₛ, State.CleanStack m t z z')
    (hr₁ : Sₛ.board.topOf (Sum.inr z') = some r₁)
    (hr₁off : r₁ ≠ t ∧ r₁ ≠ t.flipSuit ∧ r₁ ≠ z ∧ r₁ ≠ z')
    (hdetour : Sₛ.apply (Move.pilePile r₁ β) = some S₀)
    (hbare : S₀.board.topOf (Sum.inr z) = none ∧ S₀.board.topOf (Sum.inr z') = none)
    (hmerge : ∃ a₁' : State, S₀.apply (Move.pilePile c b) = some a₁' ∧
      a₁'.solvableWindow' z z.suit) :
    st.ExchangeDoubleClear t z z' c b := by
  -- the stacking prefix replays verbatim, the license riding to Sₛ
  obtain ⟨hrunX, hlicₛ⟩ := State.exchangeTwinCargo_run_cleanStack hlic hclean hrunₛ
  obtain ⟨hvis, hvis', h₀ₛ, h₀ₛ', hfit, hfit', hnbₛ, hnbₛ'⟩ := hlicₛ
  -- the detour's mirror step: the twins sit off r₁'s run (the no-braids
  -- plus r₁'s direct seat under z')
  have hcleanr : t ∉ Sₛ.board.aboveOf r₁ ∧ t.flipSuit ∉ Sₛ.board.aboveOf r₁ := by
    have hr₁in : r₁ ∈ Sₛ.board.aboveOf z' := Board.mem_aboveOf_of_topOf hr₁
    constructor
    · intro hmem
      exact hnbₛ'.1 (Board.aboveOf_trans hr₁in hmem)
    · intro hmem
      exact hnbₛ'.2 (Board.aboveOf_trans hr₁in hmem)
  have hfireD : (Sₛ.exchangeTwinCargo t).apply (Move.pilePile r₁ β)
      = some (S₀.exchangeTwinCargo t) :=
    State.exchangeTwinCargo_step_pilePile h₀ₛ h₀ₛ' ⟨hr₁off.2.2.1, hr₁off.2.2.2⟩
      ⟨hr₁off.1, hr₁off.2.1⟩ hcleanr hdetour
  -- the source runs the mixed prefix to S₀
  have hrunπ : st.run (πₛ ++ [Move.pilePile r₁ β]) = some S₀ :=
    run_append_some hrunₛ (run_cons_intro hdetour rfl)
  -- the covers survive the detour (the rider run is off both cargos)
  have hbz₀ : S₀.board.bottomOf z = some (Sum.inr t) :=
    (State.apply_pilePile_bottomOf hdetour (fun h => hr₁off.2.2.1 h.symm)).trans h₀ₛ
  have hbz₀' : S₀.board.bottomOf z' = some (Sum.inr t.flipSuit) :=
    (State.apply_pilePile_bottomOf hdetour (fun h => hr₁off.2.2.2 h.symm)).trans h₀ₛ'
  refine ⟨πₛ ++ [Move.pilePile r₁ β], S₀, hrunπ, ?_, State.wf_run hwf hrunπ, hfit, hfit',
    (Board.bottomOf_eq S₀.board z (Sum.inr t)).mp hbz₀,
    (Board.bottomOf_eq S₀.board z' (Sum.inr t.flipSuit)).mp hbz₀',
    hbare.1, hbare.2, hmerge⟩
  exact run_append_some hrunX (run_cons_intro hfireD rfl)

/-- **The scheduled direct bridge, MIXED form**: the [H′] shape closed
from the CONSTRUCTIVE schedule alone — the CleanStack prefix's replay
and the detour's mirror step are derived, the REAL window applies at the
both-bare end state (the covers surviving the detour), and the mirror's
winning play is the replayed mixed prefix followed by the window's
translated play.  The successor's premise is window-shaped
(`solvableWindow` at the merge's successor). -/
theorem State.solvable_of_exchange_merge_rooted_sched_mixed {st a₁ : State} {t z z' c : Card}
    {b : Base}
    (hwf : st.WF) (hlic : State.TwinLicensedAt st t z z')
    {πₛ : List Move} {Sₛ S₀ : State} {r₁ : Card} {β : Base}
    (hrunₛ : st.run πₛ = some Sₛ)
    (hclean : ∀ m ∈ πₛ, State.CleanStack m t z z')
    (hr₁ : Sₛ.board.topOf (Sum.inr z') = some r₁)
    (hr₁off : r₁ ≠ t ∧ r₁ ≠ t.flipSuit ∧ r₁ ≠ z ∧ r₁ ≠ z')
    (hdetour : Sₛ.apply (Move.pilePile r₁ β) = some S₀)
    (hbare : S₀.board.topOf (Sum.inr z) = none ∧ S₀.board.topOf (Sum.inr z') = none)
    (hstep : S₀.apply (Move.pilePile c b) = some a₁)
    (hsolw' : a₁.solvableWindow' z z.suit) :
    (st.exchangeTwinCargo t).solvableFrom := by
  obtain ⟨hrunX, hlicₛ⟩ := State.exchangeTwinCargo_run_cleanStack hlic hclean hrunₛ
  obtain ⟨hvis, hvis', h₀ₛ, h₀ₛ', hfit, hfit', hnbₛ, hnbₛ'⟩ := hlicₛ
  have hcleanr : t ∉ Sₛ.board.aboveOf r₁ ∧ t.flipSuit ∉ Sₛ.board.aboveOf r₁ := by
    have hr₁in : r₁ ∈ Sₛ.board.aboveOf z' := Board.mem_aboveOf_of_topOf hr₁
    constructor
    · intro hmem
      exact hnbₛ'.1 (Board.aboveOf_trans hr₁in hmem)
    · intro hmem
      exact hnbₛ'.2 (Board.aboveOf_trans hr₁in hmem)
  have hfireD : (Sₛ.exchangeTwinCargo t).apply (Move.pilePile r₁ β)
      = some (S₀.exchangeTwinCargo t) :=
    State.exchangeTwinCargo_step_pilePile h₀ₛ h₀ₛ' ⟨hr₁off.2.2.1, hr₁off.2.2.2⟩
      ⟨hr₁off.1, hr₁off.2.1⟩ hcleanr hdetour
  have hrunπ : st.run (πₛ ++ [Move.pilePile r₁ β]) = some S₀ :=
    run_append_some hrunₛ (run_cons_intro hdetour rfl)
  have hbz₀ : S₀.board.bottomOf z = some (Sum.inr t) :=
    (State.apply_pilePile_bottomOf hdetour (fun h => hr₁off.2.2.1 h.symm)).trans h₀ₛ
  have hbz₀' : S₀.board.bottomOf z' = some (Sum.inr t.flipSuit) :=
    (State.apply_pilePile_bottomOf hdetour (fun h => hr₁off.2.2.2 h.symm)).trans h₀ₛ'
  have hztop₀ : S₀.board.topOf (Sum.inr t) = some z :=
    (Board.bottomOf_eq S₀.board z (Sum.inr t)).mp hbz₀
  have hztop₀' : S₀.board.topOf (Sum.inr t.flipSuit) = some z' :=
    (Board.bottomOf_eq S₀.board z' (Sum.inr t.flipSuit)).mp hbz₀'
  have hres := State.solvable_of_exchange_merge_direct (State.wf_run hwf hrunπ)
    hfit hfit' hztop₀ hztop₀' hbare hstep hsolw'
  obtain ⟨π', W, hrun', hwin'⟩ := hres
  refine ⟨(πₛ ++ [Move.pilePile r₁ β]) ++ π', W, ?_, hwin'⟩
  exact run_append_some (run_append_some hrunX (run_cons_intro hfireD rfl)) hrun'

/-! ## §11. The selective re-scheduling — the non-adjacent case

The normalization design (from the equal-heights session's discovery):
the z'-suit rung-raisers between the two cargo-stackings CANNOT commute
past the second stacking (they raise its firing rung), but every
HEIGHT-BLIND move can — and the height-blind kinds are exactly the
non-raisers.  The kit:

* `Move.heightBlind` — the raiser classification (decidable): the
  kinds that never change any foundation height (draw, reveal,
  deckPile, pilePile) vs the foundation moves (which change their own
  suit's height — the z'-suit ones are the raisers that must stay
  between the stackings);
* `State.ZClean` / `State.ZCleanRun` — the z'-cleanliness of an
  intervening move at a state (height-blind, z' not among the moved
  cards, z''s own seat `inr z'` not among the touched bases — it
  neither lands on z' nor detaches from it, so z' stays bare), and its
  state-indexed version along a run segment;
* `State.stacking_swap_zclean` — the SINGLE SWAP with the full firing
  transfer: a z-clean height-blind move and the stacking commute, both
  orders firing, the same final state (the transfer: the stacking's
  guards survive the move — z' bare, seated, rung-exact, by the
  touched-base/card exclusions and the height-blindness; the move's
  guards survive the stacking — its landing/detach bases off the
  stacking's edit, its stock/deal/depths reads untouched);
* `State.run_bubble_stacking` — the BUBBLE: the second stacking
  commutes past a whole z-clean segment, the terminal state preserved
  (the left-decomposition induction: the IH bubbles the tail, the
  single swap reorders the head);
* `State.playWindow'_of_rescheduled` — the normalization: at a
  both-bare licensed state, a winning play [pileStack z; π₂; pileStack
  z'; π₃] with π₂ z'-clean gives `solvableWindow'` — the bubbled play
  [pileStack z; pileStack z'; π₂; π₃] wins identically, and the
  ADJACENT-HEAD sufficiency (`playWindow'_of_eq_heights`) applies, the
  height-blind π₂ being unconditionally pre-admitted so the tail
  premise reduces to π₃'s. -/

/-- **The raiser classification**: the height-blind kinds — the moves
that never change any foundation height.  Everything else is a
foundation move (deckStack/pileStack/stackPile) changing its own
suit's height; the z'-suit ones are exactly the rung-raisers that must
stay between the two cargo-stackings. -/
def Move.heightBlind : Move → Bool
  | .draw | .reveal _ | .deckPile _ _ | .pilePile _ _ => true
  | _ => false

/-- **The z'-cleanliness of an intervening move at a state**: the move
is height-blind (a non-raiser), its touched cards exclude z' (it does
not move z'), and its touched bases exclude z''s own seat `inr z'` (it
neither lands on z' nor detaches from it — z' stays bare). -/
def State.ZClean (m : Move) (z' : Card) (S : State) : Prop :=
  Move.heightBlind m = true ∧
    (∀ x ∈ (m.touch S).2, x ≠ z') ∧
    (∀ b ∈ (m.touch S).1, b ≠ Sum.inr z')

/-- The state-indexed cleanliness along a run segment (each move clean
at the state it fires from). -/
def State.ZCleanRun (z' : Card) : List Move → State → Prop
  | [], _ => True
  | m :: ms, S => State.ZClean m z' S ∧ (match S.apply m with
    | some R => State.ZCleanRun z' ms R
    | none => True)

/-- **The single swap, with the full firing transfer**: a z-clean
height-blind move and the stacking of z' commute in the run — both
orders fire and the final state is the same.  The transfer: the
stacking's guards survive the move (z' stays bare — the move's touched
bases exclude `inr z'`; z' stays seated at the same base — the move's
touched cards exclude z'; the rung survives — the height-blind kinds
never touch heights), and the move's guards survive the stacking (its
landing and detach bases are off the stacking's detach seat `bq` — the
landing by the canPlace failure at the occupied seat, the detach by the
card exclusion; its stock/deal/depths reads are untouched by the
board+height edit).  The state equality is the comm kit's
`commute_of_disjoint_touch` on the derived touch disjointness. -/
theorem State.stacking_swap_zclean {S w : State} {z' : Card} {m : Move}
    {rest : List Move}
    (hclean : State.ZClean m z' S)
    (hrun : S.run (m :: Move.pileStack z' :: rest) = some w) :
    S.run (Move.pileStack z' :: m :: rest) = some w := by
  obtain ⟨hkind, hcards, hbases⟩ := hclean
  obtain ⟨R, hm, hrest1⟩ := run_cons_elim hrun
  obtain ⟨T, hstack, hrest⟩ := run_cons_elim hrest1
  -- the stacking's firing shape at R (T pinned to its successor form)
  have hbind := hstack
  rw [apply_pileStack_iff] at hstack
  obtain ⟨htopR, bq, hbotR, hrkR, -⟩ := hstack
  cases m with
  | draw =>
      have hmraw := hm
      rw [apply_draw_iff] at hm
      obtain ⟨rfl⟩ := hm
      -- the stock edit cannot move z' or its seat: both reads are rfl
      have htopS : S.board.topOf (Sum.inr z') = none := htopR
      have hbotS : S.board.bottomOf z' = some bq := hbotR
      have hrkS : z'.rank.toIdx = S.heights z'.suit := hrkR
      have hstackS : S.apply (Move.pileStack z') = some
          {S with
            board := S.board.detach bq,
            heights := fun s => if s = z'.suit then S.heights s + 1 else S.heights s} :=
        apply_pileStack_iff.mpr ⟨htopS, bq, hbotS, hrkS, rfl⟩
      obtain ⟨T', hmv⟩ : ∃ T' : State, ({S with
          board := S.board.detach bq,
          heights := fun s => if s = z'.suit then S.heights s + 1 else S.heights s}).apply
          Move.draw = some T' := ⟨_, apply_draw_iff.mpr rfl⟩
      have hcomm : T = T' := Option.some.inj
        ((Option.bind_eq_some_iff.mpr ⟨_, hmraw, hbind⟩).symm.trans
          ((deal_commutes_nonStock S (Move.pileStack z') rfl).symm.trans
            (Option.bind_eq_some_iff.mpr ⟨_, hstackS, hmv⟩)))
      subst hcomm
      exact run_cons_intro hstackS (run_cons_intro hmv hrest)
  | reveal c =>
      have hmraw := hm
      rw [apply_reveal_iff] at hm
      obtain ⟨htopc, r, a, bd₀, hbotc, hp, hatt, rfl⟩ := hm
      -- the exclusions from the z'-cleanliness
      have hhz : Sum.inr z' ≠ S.hiddenBase a :=
        fun hcon => hbases (S.hiddenBase a) (by simp [Move.touch, hbotc, hp]) hcon.symm
      have hczz : c ≠ z' := hcards c (by simp [Move.touch, hbotc, hp])
      have hrzz : r ≠ z' := hcards r (by simp [Move.touch, hbotc, hp])
      -- the invariances: z' bare, seated, rung-exact at S too
      have htopS : S.board.topOf (Sum.inr z') = none :=
        (Board.attach_topOf_ne S.board (S.hiddenBase a) r hatt hhz).symm.trans htopR
      have hbotS : S.board.bottomOf z' = some bq :=
        (bottomOf_attach_ne hatt (fun hcon => hrzz hcon.symm)).symm.trans hbotR
      have hrkS : z'.rank.toIdx = S.heights z'.suit := hrkR
      have hbq : S.board.topOf bq = some z' :=
        (Board.bottomOf_eq S.board z' bq).mp hbotS
      -- the reveal's attach seat is off the stacking's detach seat
      have hhhb : S.hiddenBase a ≠ bq := by
        intro hcon
        have hfree : S.board.topOf (S.hiddenBase a) = none :=
          ((Board.attach_eq_some_iff S.board (S.hiddenBase a) r).mp
            (by rw [hatt]; simp)).1
        rw [hcon] at hfree
        rw [hfree] at hbq
        exact absurd hbq (by simp)
      have hicbq : Sum.inr c ≠ bq := by
        intro hcon
        rw [← hcon] at hbq
        rw [hbq] at htopc
        exact absurd htopc (by simp)
      have hstackS : S.apply (Move.pileStack z') = some
          {S with
            board := S.board.detach bq,
            heights := fun s => if s = z'.suit then S.heights s + 1 else S.heights s} :=
        apply_pileStack_iff.mpr ⟨htopS, bq, hbotS, hrkS, rfl⟩
      -- the reveal at the stacked state: every guard survives the edit
      have htopc₀ : (S.board.detach bq).topOf (Sum.inr c) = none := by
        rw [Board.detach_topOf_ne _ _ _ hicbq]
        exact htopc
      have hbotc₀ : (S.board.detach bq).bottomOf c = some (Sum.inr r) := by
        rw [bottomOf_detach_ne hbq hczz]
        exact hbotc
      have hfreehb : S.board.topOf (S.hiddenBase a) = none :=
        ((Board.attach_eq_some_iff S.board (S.hiddenBase a) r).mp
          (by rw [hatt]; simp)).1
      have hbotr : S.board.bottomOf r = none :=
        ((Board.attach_eq_some_iff S.board (S.hiddenBase a) r).mp
          (by rw [hatt]; simp)).2
      obtain ⟨bd₁, hatt₁⟩ : ∃ bd₁, (S.board.detach bq).attach (S.hiddenBase a) r
          = some bd₁ := by
        have hne : ((S.board.detach bq).attach (S.hiddenBase a) r) ≠ none :=
          (Board.attach_eq_some_iff _ _ _).mpr
            ⟨by rw [Board.detach_topOf_ne _ _ _ hhhb];
                exact hfreehb,
             by rw [bottomOf_detach_ne hbq hrzz]; exact hbotr⟩
        cases hx : (S.board.detach bq).attach (S.hiddenBase a) r with
        | none => rw [hx] at hne; exact absurd hne (by simp)
        | some bd₁ => exact ⟨bd₁, rfl⟩
      obtain ⟨T', hmv⟩ : ∃ T' : State, ({S with
          board := S.board.detach bq,
          heights := fun s => if s = z'.suit then S.heights s + 1 else S.heights s}).apply
          (Move.reveal c) = some T' :=
        ⟨_, apply_reveal_iff
          (st := {S with
            board := S.board.detach bq,
            heights := fun s => if s = z'.suit then S.heights s + 1 else S.heights s}).mpr
          ⟨htopc₀, r, a, bd₁, hbotc₀, hp, hatt₁, rfl⟩⟩
      have hdisj : disjointTouch ((Move.reveal c).touch S)
          ((Move.pileStack z').touch S) := by
        refine ⟨?_, ?_⟩
        · intro b hbmem hbmem'
          simp only [Move.touch, hbotc, hp] at hbmem
          simp only [Move.touch, hbotS, Option.toList_some] at hbmem'
          have hb₁ : b = S.hiddenBase a := List.mem_singleton.mp hbmem
          have hb₂ : b = bq := List.mem_singleton.mp hbmem'
          exact hhhb (hb₁.symm.trans hb₂)
        · intro x hxmem hxmem'
          simp only [Move.touch] at hxmem'
          exact hcards x hxmem (List.mem_singleton.mp hxmem')
      have hcomm : T = T' := comm_reveal_pileStack hdisj
          (Option.bind_eq_some_iff.mpr ⟨_, hmraw, hbind⟩)
          (Option.bind_eq_some_iff.mpr ⟨_, hstackS, hmv⟩)
      subst hcomm
      exact run_cons_intro hstackS (run_cons_intro hmv hrest)
  | deckPile c b =>
      have hmraw := hm
      rw [apply_deckPile_iff] at hm
      obtain ⟨hprev, hcp, bd₀, hatt, rfl⟩ := hm
      -- the exclusions and the landing's freedom
      have hbbz : b ≠ Sum.inr z' := hbases b (by simp [Move.touch])
      have hccz : c ≠ z' := hcards c (by simp [Move.touch])
      -- the invariances: z' bare, seated, rung-exact at S too
      have htopS : S.board.topOf (Sum.inr z') = none :=
        (Board.attach_topOf_ne S.board b c hatt (fun hcon => hbbz hcon.symm)).symm.trans htopR
      have hbotS : S.board.bottomOf z' = some bq :=
        (bottomOf_attach_ne hatt (fun hcon => hccz hcon.symm)).symm.trans hbotR
      have hrkS : z'.rank.toIdx = S.heights z'.suit := hrkR
      have hbq : S.board.topOf bq = some z' :=
        (Board.bottomOf_eq S.board z' bq).mp hbotS
      have hbne : b ≠ bq := by
        intro hcon
        have hfree : S.board.topOf b = none := topOf_of_canPlace hcp
        rw [hcon] at hfree
        rw [hfree] at hbq
        exact absurd hbq (by simp)
      have hstackS : S.apply (Move.pileStack z') = some
          {S with
            board := S.board.detach bq,
            heights := fun s => if s = z'.suit then S.heights s + 1 else S.heights s} :=
        apply_pileStack_iff.mpr ⟨htopS, bq, hbotS, hrkS, rfl⟩
      -- the deckPile at the stacked state: the stock read is untouched
      -- and the placement guards survive the one-seat edit
      have htopb₀ : (S.board.detach bq).topOf b = none := by
        rw [Board.detach_topOf_ne _ _ _ hbne]
        exact topOf_of_canPlace hcp
      have hbotc₀ : (S.board.detach bq).bottomOf c = none := by
        rw [bottomOf_detach_ne hbq hccz]
        exact ((Board.attach_eq_some_iff S.board b c).mp (by rw [hatt]; simp)).2
      obtain ⟨bd₁, hatt₁⟩ : ∃ bd₁, (S.board.detach bq).attach b c = some bd₁ := by
        have hne : ((S.board.detach bq).attach b c) ≠ none :=
          (Board.attach_eq_some_iff _ _ _).mpr ⟨htopb₀, hbotc₀⟩
        cases hx : (S.board.detach bq).attach b c with
        | none => rw [hx] at hne; exact absurd hne (by simp)
        | some bd₁ => exact ⟨bd₁, rfl⟩
      have hcp₀ : ({S with
            board := S.board.detach bq,
            heights := fun s => if s = z'.suit then S.heights s + 1 else S.heights s}).canPlace
            c b = true := by
        cases b with
        | inl a =>
            have h2 := canPlace_inl_iff.mp hcp
            refine canPlace_inl_iff.mpr ⟨?_, h2.2⟩
            have h1 : (S.board.detach bq).topOf (Sum.inl a) = S.board.topOf (Sum.inl a) :=
              Board.detach_topOf_ne _ _ _ hbne
            rw [h1]
            exact h2.1
        | inr d =>
            have h3 := canPlace_inr_iff.mp hcp
            have hdz : d ≠ z' := fun hcon => hbbz (by rw [hcon])
            refine canPlace_inr_iff.mpr ⟨?_, ?_, h3.2.2⟩
            · have h1 : (S.board.detach bq).topOf (Sum.inr d)
                  = S.board.topOf (Sum.inr d) :=
                Board.detach_topOf_ne _ _ _ hbne
              rw [h1]
              exact h3.1
            · have h2 : (S.board.detach bq).bottomOf d = S.board.bottomOf d :=
                bottomOf_detach_ne hbq hdz
              show ((S.board.detach bq).bottomOf d).isSome = true
              rw [h2]
              exact h3.2.1
      obtain ⟨T', hmv⟩ : ∃ T' : State, ({S with
          board := S.board.detach bq,
          heights := fun s => if s = z'.suit then S.heights s + 1 else S.heights s}).apply
          (Move.deckPile c b) = some T' :=
        ⟨_, apply_deckPile_iff
          (st := {S with
            board := S.board.detach bq,
            heights := fun s => if s = z'.suit then S.heights s + 1 else S.heights s}).mpr
          ⟨hprev, hcp₀, bd₁, hatt₁, rfl⟩⟩
      have hdisj : disjointTouch ((Move.deckPile c b).touch S)
          ((Move.pileStack z').touch S) := by
        refine ⟨?_, ?_⟩
        · intro b₁ hbmem hbmem'
          simp only [Move.touch] at hbmem
          simp only [Move.touch, hbotS, Option.toList_some] at hbmem'
          have hb₁ : b₁ = b := List.mem_singleton.mp hbmem
          have hb₂ : b₁ = bq := List.mem_singleton.mp hbmem'
          exact hbne (hb₁.symm.trans hb₂)
        · intro x hxmem hxmem'
          simp only [Move.touch] at hxmem'
          exact hcards x hxmem (List.mem_singleton.mp hxmem')
      have hcomm : T = T' := comm_deckPile_pileStack hdisj
          (Option.bind_eq_some_iff.mpr ⟨_, hmraw, hbind⟩)
          (Option.bind_eq_some_iff.mpr ⟨_, hstackS, hmv⟩)
      subst hcomm
      exact run_cons_intro hstackS (run_cons_intro hmv hrest)
  | pilePile c b =>
      have hmraw := hm
      rw [apply_pilePile_iff] at hm
      obtain ⟨β₀, hbotc, hne, hcmr, bd₀, hatt, rfl⟩ := hm
      have htopβ₀ : S.board.topOf β₀ = some c :=
        (Board.bottomOf_eq S.board c β₀).mp hbotc
      have hccz : c ≠ z' := hcards c (by simp [Move.touch])
      have hbbz : b ≠ Sum.inr z' := hbases b (by simp [Move.touch])
      have hβ₀bz : β₀ ≠ Sum.inr z' :=
        hbases β₀ (by simp [Move.touch, hbotc, Option.toList_some])
      have hcpst : S.canPlace c b = true := by
        simp only [State.canMoveRun, Bool.and_eq_true_iff] at hcmr
        exact hcmr.1
      -- the invariances: z' bare, seated, rung-exact at S too
      have htopS : S.board.topOf (Sum.inr z') = none := by
        have h1 : bd₀.topOf (Sum.inr z') = none := htopR
        rw [Board.attach_topOf_ne _ _ _ hatt (fun hcon => hbbz hcon.symm),
          Board.detach_topOf_ne _ _ _ (fun hcon => hβ₀bz hcon.symm)] at h1
        exact h1
      have hbotS : S.board.bottomOf z' = some bq := by
        have h1 : bd₀.bottomOf z' = some bq := hbotR
        rw [bottomOf_attach_ne hatt (fun hcon => hccz hcon.symm),
          bottomOf_detach_ne htopβ₀ (fun hcon => hccz hcon.symm)] at h1
        exact h1
      have hrkS : z'.rank.toIdx = S.heights z'.suit := hrkR
      -- the two touched bases are off the stacking's detach seat
      have hbq : S.board.topOf bq = some z' :=
        (Board.bottomOf_eq S.board z' bq).mp hbotS
      have hbne : b ≠ bq := by
        intro hcon
        have hfree : S.board.topOf b = none := topOf_of_canPlace hcpst
        rw [hcon] at hfree
        rw [hfree] at hbq
        exact absurd hbq (by simp)
      have hβ₀ne : β₀ ≠ bq := by
        intro hcon
        rw [hcon] at hbotc
        have hcq : S.board.topOf bq = some c := (Board.bottomOf_eq S.board c bq).mp hbotc
        rw [hbq] at hcq
        exact hccz (Option.some.inj hcq).symm
      have hstackS : S.apply (Move.pileStack z') = some
          {S with
            board := S.board.detach bq,
            heights := fun s => if s = z'.suit then S.heights s + 1 else S.heights s} :=
        apply_pileStack_iff.mpr ⟨htopS, bq, hbotS, hrkS, rfl⟩
      -- the pilePile at the stacked state: the root's base, the
      -- landing, the run guard, and the attach all survive the edit
      have hbotc₀ : (S.board.detach bq).bottomOf c = some β₀ := by
        rw [bottomOf_detach_ne hbq hccz]
        exact hbotc
      have hcp₀ : ({S with
            board := S.board.detach bq,
            heights := fun s => if s = z'.suit then S.heights s + 1 else S.heights s}).canPlace
            c b = true := by
        cases b with
        | inl a =>
            have h2 := canPlace_inl_iff.mp hcpst
            refine canPlace_inl_iff.mpr ⟨?_, h2.2⟩
            have h1 : (S.board.detach bq).topOf (Sum.inl a) = S.board.topOf (Sum.inl a) :=
              Board.detach_topOf_ne _ _ _ hbne
            rw [h1]
            exact h2.1
        | inr d =>
            have h3 := canPlace_inr_iff.mp hcpst
            have hdz : d ≠ z' := fun hcon => hbbz (by rw [hcon])
            refine canPlace_inr_iff.mpr ⟨?_, ?_, h3.2.2⟩
            · have h1 : (S.board.detach bq).topOf (Sum.inr d)
                  = S.board.topOf (Sum.inr d) :=
                Board.detach_topOf_ne _ _ _ hbne
              rw [h1]
              exact h3.1
            · have h2 : (S.board.detach bq).bottomOf d = S.board.bottomOf d :=
                bottomOf_detach_ne hbq hdz
              show ((S.board.detach bq).bottomOf d).isSome = true
              rw [h2]
              exact h3.2.1
      have hcmr₀ : ({S with
            board := S.board.detach bq,
            heights := fun s => if s = z'.suit then S.heights s + 1 else S.heights s}).canMoveRun
            c b = true := by
        cases b with
        | inl a => simp only [State.canMoveRun, hcp₀]; rfl
        | inr d =>
            refine canMoveRun_inr_iff.mpr ⟨hcp₀, ?_⟩
            show ((S.board.detach bq).aboveOf c).contains d = false
            cases hcon : ((S.board.detach bq).aboveOf c).contains d with
            | false => rfl
            | true =>
                have hmem : d ∈ (S.board.detach bq).aboveOf c :=
                  (List.contains_iff_mem).mp hcon
                have hmem' : d ∈ S.board.aboveOf c :=
                  Board.aboveOf_sub_detach 52 c [] d hmem
                have hfalse := (canMoveRun_inr_iff.mp hcmr).2
                rw [List.contains_iff_mem.mpr hmem'] at hfalse
                exact absurd hfalse (by simp)
      -- the attach at the doubly-detached board
      have hfree₀ : (S.board.detach β₀).topOf b = none := by
        rw [Board.detach_topOf_ne _ _ _ (fun hcon => hne hcon.symm)]
        exact topOf_of_canPlace hcpst
      have hbqβ₀ : bq ≠ β₀ := fun hcon => hβ₀ne hcon.symm
      have htopbqβ₀ : (S.board.detach β₀).topOf bq = some z' := by
        rw [Board.detach_topOf_ne _ _ _ hbqβ₀]
        exact hbq
      have hne' : ((S.board.detach bq).detach β₀).attach b c ≠ none := by
        refine (Board.attach_eq_some_iff _ _ _).mpr ⟨?_, ?_⟩
        · rw [detach_detach_comm hbqβ₀, Board.detach_topOf_ne _ _ _ hbne]
          exact hfree₀
        · rw [detach_detach_comm hbqβ₀, bottomOf_detach_ne htopbqβ₀ hccz,
            Board.bottomOf_detach_self htopβ₀]
      obtain ⟨bd₁, hatt₁⟩ : ∃ bd₁, ((S.board.detach bq).detach β₀).attach b c
          = some bd₁ := by
        have := hne'
        cases hx : ((S.board.detach bq).detach β₀).attach b c with
        | none => rw [hx] at this; exact absurd this (by simp)
        | some bd₁ => exact ⟨bd₁, rfl⟩
      obtain ⟨T', hmv⟩ : ∃ T' : State, ({S with
          board := S.board.detach bq,
          heights := fun s => if s = z'.suit then S.heights s + 1 else S.heights s}).apply
          (Move.pilePile c b) = some T' :=
        ⟨_, apply_pilePile_iff.mpr ⟨β₀, hbotc₀, hne, hcmr₀, bd₁, hatt₁, rfl⟩⟩
      have hdisj : disjointTouch ((Move.pilePile c b).touch S)
          ((Move.pileStack z').touch S) := by
        refine ⟨?_, ?_⟩
        · intro b₁ hbmem hbmem'
          simp only [Move.touch, hbotc, Option.toList_some] at hbmem
          simp only [Move.touch, hbotS, Option.toList_some] at hbmem'
          rcases List.mem_cons.mp hbmem with hb₁ | hb₁
          · exact hbne (hb₁.symm.trans (List.mem_singleton.mp hbmem'))
          · exact hβ₀ne ((List.mem_singleton.mp hb₁).symm.trans
              (List.mem_singleton.mp hbmem'))
        · intro x hxmem hxmem'
          simp only [Move.touch] at hxmem'
          exact hcards x hxmem (List.mem_singleton.mp hxmem')
      have hcomm : T = T' :=
        (comm_pileStack_pilePile (disjointTouch_symm hdisj)
          (Option.bind_eq_some_iff.mpr ⟨_, hstackS, hmv⟩)
          (Option.bind_eq_some_iff.mpr ⟨_, hmraw, hbind⟩)).symm
      subst hcomm
      exact run_cons_intro hstackS (run_cons_intro hmv hrest)
  | deckStack c => exact absurd hkind (by simp [Move.heightBlind])
  | pileStack c => exact absurd hkind (by simp [Move.heightBlind])
  | stackPile c b => exact absurd hkind (by simp [Move.heightBlind])

/-- **The bubble**: the second stacking commutes past a whole z'-clean
segment, the terminal state preserved — the left-decomposition
induction (the IH bubbles the tail at the post-head state, the single
swap reorders the head). -/
theorem State.run_bubble_stacking (z' : Card) : ∀ (π₂ : List Move) (S T : State),
    S.run (π₂ ++ [Move.pileStack z']) = some T →
    State.ZCleanRun z' π₂ S →
    ∃ T' : State, S.run (Move.pileStack z' :: π₂) = some T' ∧ T' = T := by
  intro π₂
  induction π₂ with
  | nil =>
      intro S T hrun _
      exact ⟨T, hrun, rfl⟩
  | cons m rest ih =>
      intro S T hrun hclean
      obtain ⟨R, hm, hrest1⟩ := run_cons_elim hrun
      obtain ⟨hcm, hcr⟩ := hclean
      rw [hm] at hcr
      obtain ⟨T'', hrun'', heq⟩ := ih R T hrest1 hcr
      exact ⟨T'', State.stacking_swap_zclean hcm (run_cons_intro hm hrun''), heq⟩

/-- The height-blind kinds' pre-episode admission carries no condition:
a firing draw/reveal/deckPile/pilePile at a pre-phase state continues
the play pre-admitted, the phase unchanged. -/
theorem State.playWindow'_cons_heightBlind {z : Card} {σ : Suit} {S R : State}
    {m : Move} {ms : List Move}
    (hkind : Move.heightBlind m = true) (hS : S.apply m = some R) :
    State.playWindow' z σ State.WindowEp.pre S (m :: ms)
      = State.playWindow' z σ State.WindowEp.pre R ms := by
  cases m with
  | draw => simp only [State.playWindow', hS]
  | reveal c => simp only [State.playWindow', hS]
  | deckPile c b => simp only [State.playWindow', hS]
  | pilePile c b => simp only [State.playWindow', hS]
  | deckStack c => exact absurd hkind (by simp [Move.heightBlind])
  | pileStack c => exact absurd hkind (by simp [Move.heightBlind])
  | stackPile c b => exact absurd hkind (by simp [Move.heightBlind])

/-- The kinds-only extraction from a z-clean run segment: along a run
the segment's moves are all height-blind. -/
theorem State.zcleanRun_heightBlind_of_run {z' : Card} :
    ∀ (π : List Move) (S T : State), S.run π = some T → State.ZCleanRun z' π S →
    ∀ m ∈ π, Move.heightBlind m = true := by
  intro π
  induction π with
  | nil => intro S T _ _ m hm; exact absurd hm (by simp)
  | cons m rest ih =>
      intro S T hrun hclean m' hm'
      obtain ⟨R, hm, hrest1⟩ := run_cons_elim hrun
      obtain ⟨hcm, hcr⟩ := hclean
      rw [hm] at hcr
      rcases List.mem_cons.mp hm' with rfl | hm''
      · exact hcm.1
      · exact ih R T hrest1 hcr m' hm''

/-- **The height-blind prefix admission**: a run of height-blind moves
that ends admitted at `T` is admitted from the start `S` — the
pre-phase arms carry no condition, so each firing kind just extends the
admitted play frontward. -/
theorem State.playWindow'_append_heightBlind {z : Card} {σ : Suit} :
    ∀ (π : List Move) (S T : State) (tail : List Move),
    S.run π = some T →
    (∀ m ∈ π, Move.heightBlind m = true) →
    State.playWindow' z σ State.WindowEp.pre T tail = true →
    State.playWindow' z σ State.WindowEp.pre S (π ++ tail) = true := by
  intro π
  induction π with
  | nil =>
      intro S T tail hrun _ htail
      obtain rfl := run_nil_elim hrun
      exact htail
  | cons m rest ih =>
      intro S T tail hrun hkinds htail
      obtain ⟨R, hm, hrest1⟩ := run_cons_elim hrun
      rw [List.cons_append, State.playWindow'_cons_heightBlind
        (hkinds m (by simp)) hm]
      exact ih R T tail hrest1 (fun m' hm' => hkinds m' (List.mem_cons_of_mem _ hm'))
        htail

/-- **The selective re-scheduling normalization**: at a both-bare
licensed state, a winning play whose head is the z-stacking followed by
a z'-clean height-blind segment, the z'-stacking, and an arbitrary
winning tail gives `solvableWindow'` — the bubbled play
[pileStack z; pileStack z'; π₂; π₃] wins identically (the bubble, the
terminal state preserved), so the ADJACENT-HEAD sufficiency
(`playWindow'_of_eq_heights`) applies, the height-blind π₂ being
unconditionally pre-admitted so the tail premise reduces to π₃'s at
the same terminal state. -/
theorem State.playWindow'_of_rescheduled {st : State} {t z z' : Card}
    (hwf : st.WF)
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.flipSuit = true)
    (hztop : st.board.topOf (Sum.inr t) = some z)
    (hztop' : st.board.topOf (Sum.inr t.flipSuit) = some z')
    (hbare : st.board.topOf (Sum.inr z) = none ∧ st.board.topOf (Sum.inr z') = none)
    (hplay : ∃ (π₂ π₃ : List Move) (W : State),
      st.run (Move.pileStack z :: π₂ ++ Move.pileStack z' :: π₃) = some W ∧
      W.isWin = true ∧
      ∃ S₁ : State, st.apply (Move.pileStack z) = some S₁ ∧
        State.ZCleanRun z' π₂ S₁ ∧
        ∃ T₃ : State, S₁.run (π₂ ++ [Move.pileStack z']) = some T₃ ∧
          (¬ (z.rank.toIdx ≤ st.heights (Card.flipSuit z).suit) ∨
            State.playWindow' z z.suit State.WindowEp.pre T₃ π₃ = true))
    (_hsol : st.solvableFrom) :
    st.solvableWindow' z z.suit := by
  obtain ⟨π₂, π₃, W, hrunW, hwin, S₁, hfire₁, hclean, T₃, hrun₃, hcase⟩ := hplay
  -- the middle's decomposition (the determinism plumbing, once)
  have hmid := hrun₃
  rw [run_append] at hmid
  obtain ⟨R₂, hrunπ₂, htail⟩ := Option.bind_eq_some_iff.mp hmid
  obtain ⟨T₃b, hfirez, hnileq⟩ := run_cons_elim htail
  rw [run_nil_elim hnileq] at hfirez
  -- the winning tail from the original play
  have hrunπ₃ : T₃.run π₃ = some W := by
    obtain ⟨S₁', hfire₁', hrest⟩ := run_cons_elim hrunW
    rw [show S₁' = S₁ from Option.some.inj (hfire₁'.symm.trans hfire₁)] at hrest
    obtain ⟨R₂', hrunπ₂', hpost⟩ := Option.bind_eq_some_iff.mp
      ((run_append S₁ π₂ (Move.pileStack z' :: π₃)).symm.trans hrest)
    rw [show R₂' = R₂ from Option.some.inj (hrunπ₂'.symm.trans hrunπ₂)] at hpost
    obtain ⟨T₃', hfirez', hrest'⟩ := run_cons_elim hpost
    rw [show T₃' = T₃ from Option.some.inj (hfirez'.symm.trans hfirez)] at hrest'
    exact hrest'
  -- the kinds of π₂ (the cleanliness gives the height-blindness along the run)
  have hkinds : ∀ m ∈ π₂, Move.heightBlind m = true :=
    State.zcleanRun_heightBlind_of_run π₂ S₁ R₂ hrunπ₂ hclean
  -- the bubble: the second stacking past π₂, the composite state preserved
  obtain ⟨T', hbubble, hT'⟩ := State.run_bubble_stacking z' π₂ S₁ T₃ hrun₃ hclean
  obtain ⟨S₂, hfire₂, hrunπ₂'⟩ := run_cons_elim hbubble
  have hrunπ₃' : T'.run π₃ = some W := by rw [hT']; exact hrunπ₃
  -- the bubbled adjacent-head play wins identically
  have hbubbled : st.run (Move.pileStack z :: Move.pileStack z' :: π₂ ++ π₃)
      = some W := by
    refine run_cons_intro hfire₁ ?_
    exact run_append_some hbubble hrunπ₃'
  -- the adjacent-head sufficiency applies; the tail premise reduces to π₃'s
  refine State.playWindow'_of_eq_heights hwf hfit hfit' hztop hztop' hbare
    ⟨π₂ ++ π₃, W, hbubbled, hwin, ?_⟩ _hsol
  rcases hcase with hfailskew | htail
  · exact Or.inl hfailskew
  · refine Or.inr ?_
    intro S₂' hS₂'
    obtain ⟨S₁'', hfire₁'', hrestz⟩ := run_cons_elim hS₂'
    rw [show S₁'' = S₁ from Option.some.inj (hfire₁''.symm.trans hfire₁)] at hrestz
    obtain ⟨S₂'', hfire₂'', hfin⟩ := run_cons_elim hrestz
    rw [show S₂' = S₂ from (run_nil_elim hfin).symm.trans
      (Option.some.inj (hfire₂''.symm.trans hfire₂))]
    exact State.playWindow'_append_heightBlind π₂ S₂ T' π₃ hrunπ₂' hkinds
      (by rw [hT']; exact htail)

/-! ## §12. The skew-branch tail premise — the verdict and the residue

The tail premise of `playWindow'_adjacent_pair_skew` was audited for
the kill (the mission's two vacuity hypotheses): BOTH FAIL.  The
pair-member worry-backs are NOT vacuous in the tail — after the head,
both pair members sit on the foundations (their unstacks fire at the
equalized rungs), and the partner rung CAN climb past z.rank+1 (the
co-climb alternation: the partner's (z.rank+1)-card admits via its own
skew at equality, raising the partner rung to z.rank+2, after which
the pair-member worry-back's anti-skew FAILS while its firing guard
still holds) — the crossed configuration `rung_eq_unstack_of_ne`'s
docstring names the obstruction (the multi-unstack: the mirror would
have to drop its rung past the stranded pair card — not a single
in-kind move).  The just-below-pair worry-backs are likewise reachable
with the partner still stacked (the anti-skew needs the partner rung
down at c.rank+1 — the crossed configuration is present in the tail
whenever the partner's unstack has not yet fired).  And the tail
premise carries MORE than the anti-skew: the on-suit STACKS' skews are
equally state-dependent (two own-suit climbs in a row break the
second's skew — the co-climb must alternate), so the premise is the
honest price of the pre-episode admission's state-dependent arms.

What IS true — and lands here — is the precise residue: the tail
admission reduces to exactly the on-pair foundation moves (the on-suit
`pileStack`/`deckStack` skews and the on-suit `stackPile`
anti-skews).  `State.PreAdmitClean` names the complement — the moves
whose pre-episode arms carry NO state-dependent condition (the four
height-blind kinds, the off-pair foundation moves, and the ρ-fixed
non-just-below-pair worry-backs — the `rung_eq_unstack_of_ne` class)
— and `State.playWindow'_tail_of_eq_heights` discharges the tail
premise for any tail of that class: the admission is per-move
state-independent, so the firing run alone carries the induction. -/

/-- The state-independently pre-admitted class: the height-blind kinds
(`Move.heightBlind`), the off-pair foundation moves (the first
disjunct of every foundation arm is the suit test — no rung read), and
the ρ-fixed non-just-below-pair worry-backs (the third `stackPile`
disjunct — the `rung_eq_unstack_of_ne` class).  Every pre-episode arm
these moves hit carries no state-dependent condition. -/
def State.PreAdmitClean (z : Card) (σ : Suit) (m : Move) : Prop :=
  Move.heightBlind m = true ∨
    (∃ q : Card, (m = Move.pileStack q ∨ m = Move.deckStack q) ∧
      q.suit ≠ σ ∧ q.suit ≠ σ.flipPair) ∨
    (∃ c : Card, ∃ b : Base, m = Move.stackPile c b ∧
      Card.swapTwin z c = c ∧ c.rank.toIdx + 1 ≠ z.rank.toIdx)

/-- **The tail admission at the equal-heights route — the residue
characterization**: a tail consisting of `PreAdmitClean` moves is
pre-admitted from ANY state it runs through (the per-move arms carry
no rung conditions — the firing run alone carries the induction; the
phase stays `.pre` throughout, no growth routing: the off-pair arms
take the then-branch, the ρ-fixed worry-backs the third disjunct).
Together with the §11 kit this reduces the skew-branch's tail premise
to exactly the on-pair foundation moves — the on-suit stacks' skews
(the co-climb alternation) and the on-suit worry-backs' anti-skews
(the pair-member and just-below-pair crossed configurations), which
are the honest boundary of the equal-heights sufficiency. -/
theorem State.playWindow'_tail_of_eq_heights {z : Card} {σ : Suit} :
    ∀ (play : List Move) (S T : State),
    S.run play = some T →
    (∀ m ∈ play, State.PreAdmitClean z σ m) →
    State.playWindow' z σ State.WindowEp.pre S play = true := by
  intro play
  induction play with
  | nil => intro S T _ _; rfl
  | cons m rest ih =>
      intro S T hrun hclean
      obtain ⟨R, hm, hrest1⟩ := run_cons_elim hrun
      have hih := ih R T hrest1 (fun m' hm' => hclean m' (List.mem_cons_of_mem _ hm'))
      rcases hclean m (by simp) with hkind | ⟨q, hmeq, hqσ, hqσ'⟩ | ⟨c, b, hmeq, hρ, hrne⟩
      · rw [State.playWindow'_cons_heightBlind hkind hm]
        exact hih
      · rcases hmeq with rfl | rfl
        · -- an off-pair pileStack: the suit disjunct, the then-branch
          rw [State.playWindow', hm]
          refine Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩
          · exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr
              (Or.inl (decide_eq_true_eq.mpr ⟨hqσ, hqσ'⟩))))
          · rw [if_pos (Or.inl ⟨hqσ, hqσ'⟩)]
            exact hih
        · -- an off-pair deckStack: the suit disjunct alone
          rw [State.playWindow', hm]
          refine Bool.and_eq_true_iff.mpr ⟨?_, hih⟩
          exact Bool.or_eq_true_iff.mpr
            (Or.inl (decide_eq_true_eq.mpr ⟨hqσ, hqσ'⟩))
      · -- a ρ-fixed non-just-below-pair worry-back: the third disjunct
        subst hmeq
        rw [State.playWindow', hm]
        refine Bool.and_eq_true_iff.mpr ⟨?_, hih⟩
        exact Bool.or_eq_true_iff.mpr
          (Or.inr (decide_eq_true_eq.mpr ⟨hρ, hrne⟩))

/-! ### §12.1. The extraction lemma — the double-clear schedule's
foundation

The constructive schedule (§13) needs the riders' own stackings to be
IN the source's winning play.  The positional fact: the
tableau→foundation transition of a card is its own `pileStack` ALONE —
every other kind either leaves the card's base untouched (the board
edit is an attach at another card's seat — `q ≠ c` from the attach's
own unplacedness guard — or a detach at another card's base), or
moves the card within the tableau (the `pilePile` run-move — the run's
root lands at the landing seat, the members' bases ride along).  So a
card seated on the tableau at the start of a run either meets its own
`pileStack` in the play or is still seated at the end.  (The isWin-side
corollary — a winning play stacks every tableau card — additionally
needs the card-conservation invariant, 52 = tableau + hidden + stock
+ foundations, which the model does not yet carry as a lemma; that is
the honest residue of the full extraction, recorded here.) -/

/-- **The positional extraction**: along a run, a tableau card either
has its own `pileStack` in the play or is STILL on the tableau at the
end — no other move kind can unseat it to a foundation. -/
theorem State.bottomOf_run_mem_pileStack :
    ∀ (π : List Move) (S T : State), S.run π = some T →
    ∀ (q : Card) (b : Base), S.board.bottomOf q = some b →
    Move.pileStack q ∈ π ∨ ∃ b', T.board.bottomOf q = some b' := by
  intro π
  induction π with
  | nil =>
      intro S T hrun q b hbot
      obtain rfl := run_nil_elim hrun
      exact Or.inr ⟨b, hbot⟩
  | cons m rest ih =>
      intro S T hrun q b hbot
      obtain ⟨R, hm, hrest1⟩ := run_cons_elim hrun
      by_cases hmeq : m = Move.pileStack q
      · exact Or.inl (by rw [hmeq]; exact List.mem_cons_self)
      have hbotR : ∃ b', R.board.bottomOf q = some b' := by
        cases m with
        | draw =>
            rw [apply_draw_iff] at hm
            obtain ⟨rfl⟩ := hm
            exact ⟨b, hbot⟩
        | reveal c =>
            rw [apply_reveal_iff] at hm
            obtain ⟨htop, r, a, bd, hbotc, hp, hatt, rfl⟩ := hm
            have hqr : q ≠ r := by
              intro hcon
              have hnone : S.board.bottomOf r = none :=
                ((Board.attach_eq_some_iff S.board (S.hiddenBase a) r).mp
                  (by rw [hatt]; simp)).2
              rw [hcon] at hbot
              rw [hbot] at hnone
              exact absurd hnone (by simp)
            exact ⟨b, (bottomOf_attach_ne hatt hqr).trans hbot⟩
        | deckPile c b' =>
            rw [apply_deckPile_iff] at hm
            obtain ⟨hprev, hcp, bd, hatt, rfl⟩ := hm
            have hqc : q ≠ c := by
              intro hcon
              have hnone : S.board.bottomOf c = none :=
                ((Board.attach_eq_some_iff S.board b' c).mp (by rw [hatt]; simp)).2
              rw [hcon] at hbot
              rw [hbot] at hnone
              exact absurd hnone (by simp)
            exact ⟨b, (bottomOf_attach_ne hatt hqc).trans hbot⟩
        | deckStack q' =>
            rw [apply_deckStack_iff] at hm
            obtain ⟨hprev, hrk, rfl⟩ := hm
            exact ⟨b, hbot⟩
        | pileStack q' =>
            have hqq' : q' ≠ q := by
              intro hcon
              rw [hcon] at hmeq
              exact hmeq rfl
            rw [apply_pileStack_iff] at hm
            obtain ⟨htop, bq, hbq, hrk, rfl⟩ := hm
            have htopbq : S.board.topOf bq = some q' :=
              (Board.bottomOf_eq S.board q' bq).mp hbq
            exact ⟨b, (bottomOf_detach_ne htopbq (fun hcon => hqq' hcon.symm)).trans hbot⟩
        | stackPile c b' =>
            rw [apply_stackPile_iff] at hm
            obtain ⟨hrk, hcp, bd, hatt, rfl⟩ := hm
            have hqc : q ≠ c := by
              intro hcon
              have hnone : S.board.bottomOf c = none :=
                ((Board.attach_eq_some_iff S.board b' c).mp (by rw [hatt]; simp)).2
              rw [hcon] at hbot
              rw [hbot] at hnone
              exact absurd hnone (by simp)
            exact ⟨b, (bottomOf_attach_ne hatt hqc).trans hbot⟩
        | pilePile c b' =>
            have hmraw := hm
            rw [apply_pilePile_iff] at hm
            obtain ⟨β₀, hbotc, hne, hcmr, bd, hatt, rfl⟩ := hm
            by_cases hqc : q = c
            · rw [hqc]
              exact ⟨b', (Board.bottomOf_eq bd c b').mpr (Board.attach_topOf _ _ _ hatt)⟩
            · exact ⟨b, (State.apply_pilePile_bottomOf hmraw hqc).trans hbot⟩
      obtain ⟨b', hb'⟩ := hbotR
      rcases ih R T hrest1 q b' hb' with hmem | hseated
      · exact Or.inl (List.mem_cons_of_mem _ hmem)
      · exact Or.inr hseated
