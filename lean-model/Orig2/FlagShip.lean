import Orig2.OrbitFactor
import Orig2.RevSteps
import Orig2.FloatOrbit

/-!
# Orig2.FlagShip — THE FLAGSHIP DOOR (the library's single-question
export card)

WHAT THIS DOOR IS: the one-file answer to "what did Orig2 prove" —
the owner-adjudicated flagship (asked and answered 2026-10-17),
re-exported at citable names so the library's headline is reachable
without the machinery tour.  NO NEW MATHEMATICS lives here: every
row below is a trivial forward of a certified card (the
`c2_two_option_nonKing_windows` precedent), proofs untouched,
battery profiles inherited verbatim from the proving cards.

## THE FLAGSHIP — the phase factorization (`sameOrbit_factor`)

```
theorem flagship_sameOrbitFactor {u v : State} (hwf₁ : u.WF) (hwf₂ : v.WF) :
    sameOrbitSetoid.r u v ↔ ∃ z, NoDrawPlayW u z ∧ SWRotW z v
```

In words: a reversible-class membership is a draw-free board
reshuffle to a phase-mate, then a pure rotation round — every
classmate's board-difference and phase-difference FACTOR into
independent channels.  Everything else in the tree either feeds it
(the R-shapes, the reversibility carrier, the walk/steps generics),
rides it (the spine candidates, the pins, the fiber program), or
follows from it (`phaseFixed` as a class invariant, the
`class_card_zone` row).  Certified home: `Orig2/OrbitFactor.lean`
§4b — the claims ledger's `Orig2/Claims.lean` §1B row, discharged at
promotion 2026-10-17; five green batches; the frozen tier's
3,000-line engine route beaten by the general commutation square and
the restated pull core; battery [propext, Quot.sound], zero sorry,
zero `Classical.choice`.

## THE COMPANION KEYSTONE — the license (`rev_steps_iff`)

Over ANY letter family, the dumb both-ways span closure equals the
reversible closure — the adjudication's named runner-up, installed
the same hour: the row the flagship's every leg rides by construction
(witness closures enforce per-leg reversibility at DEFINITION time;
this row proved once and for all that the enforcement never shrank a
closure).  Certified home: `Orig2/RevSteps.lean` (installed
2026-10-17; battery [propext]; WF-free, oracle-free, choice-free).

## THE CARGO-TIER KEYSTONE — the conservation law
(`floater_orbit_invariant`)

Along a reversible cargo leg — and hence along the whole bare-cargo
orbit — floater-hood per card is FIXED: which cards are floaters is
a `BareCargoEquiv`-class invariant, the tier's conservation law and
the row the flat class characterization rides ("the conservation
keystone that makes the flat class characterization derivable", the
claims book §1F).  Ranked below the class tier and honest about it:
bare cargo, not the certified class; one program (the floater
books), not the whole tree; invariance, not structure.  The door's
  third row by owner call 2026-10-17.  Certified home:
`Orig2/FloatOrbit.lean` §H6 (the chain lift is now shared as
`CargoKit.tfa_chain_lift`; promoted from the
`Temp/float_agent_check.lean` dry-run; WF-gated — the leg engine
consumes occurrence uniqueness off the gate; battery [propext,
Quot.sound], zero sorry, zero choice).

## THE CLASS IFF — the un-mediated king arm (`bareCargo_iff_vk`)

The bare-cargo class is EXACTLY the flat chart, with no mediator
binder: identity, the twin edge, or a king landing on a node of the
origin's FUEL SET (`VKSet st a'` = vacant or bare-king-bottom), plus
the readouts and the origin-side licensing.  The king arm is
`VKSet`, not "empty at st": the empty-target clause is refuted by the
two-king swap (a mediator vacates the target before the mover lands),
while the fuel set is what every reversible leg preserves
(`bareCargo_orbit_vk`, pointwise).  The `→` is
`bareCargo_to_chartDiff_vk`; the `←` is the schedule
(`king_assignment_reachable`, greedy cycle-fixer over the fuel set)
plus the residual twin chart.  The per-rank factorization is
`bareCargo_iff_split` (king half over `VKSet`, twin half).
Certified home: `Orig2/FloatOrbit.lean` §M11 and §§M11a–g; battery
[propext, Quot.sound], zero sorry, zero `Classical.choice`; the WF
gate supplies the chart round trip, so no ambient rigidity binder.

## HONORABLE MENTIONS (the lower tier — certified rows ranked below
the seats; named and cited, never re-exported)
What lands here: proved-real, battery-clean rows the adjudication
judged feeder-grade — everything consumes them, nothing follows
from them — at TREE grade (every program's letters cross the row;
tier-local heads do not qualify, however green).  The distinction
against the debt ledger below: mention rows are GREEN (nothing
holds them back but their rank); ledger rows are held back FOR
CAUSE (a sorry, a hoisted premise, a fence).  A mention grows into
a seat only by owner call.  The roll:

* `reversibleOf_iff_reversibleAtW` (home:
  `Orig2/Classification.lean` §7, the card's battery) — the
  zero-choice carrier dictionary: at WF, the Bool undoability
  oracle decides the constructive witness carrier exactly, per
  move — `reversibleOf st m = true ↔ reversibleAtW st m`.  The
  vocabulary's own promised substitute for the classical
  unconditioned iff (the carrier's design note,
  `reversibleAtW`'s docstring in `Orig2/Vocab.lean`: that iff
  drags `Classical.choice` through the vocabulary; this row
  supplies the effective dichotomy instead, both halves
  constructive).  The most-cited practical row in the tree —
  every letter of every witness definition crosses it, "find a
  return play" becoming "check a Bool" — and feeder-tier exactly
  for that: no class, no orbit, no structure; a dictionary between
  two readings of one predicate.  The adjudication's near-miss for
  the fourth seat (owner call pending, 2026-10-17).

* Below the roll's bar, verdict recorded (2026-10-17):
  `floater_classification` (`Floater` iff `FloaterSpec`,
  `Orig2/FloatFiber.lean` §H3) — certified green, no sorry and no
  hoist of its own; excluded by RANK, not debt: its consumers are
  the floater books alone (the flat-iff harnesses and the
  conservation seat's own engine, `Orig2/FloatOrbit.lean`'s chain
  lift) — a def-vs-spec characterization, feeder-grade within one
  tier.  The roll stays tree-grade; opening it here queues the
  quartet and the kit behind.  The debt in its program belongs to
  the capstones, not this row — see the ledger below.

## NOT THIS DOOR (honesty ledger)

By DEBT — the floater books' capstones still re-hoist the priced
`chart_round_trip` as a hypothesis (`floater_seat_to_equiv'`, the
`floater_iff_cargoEdit` harness, and the flat class
characterization `bareCargo_iff_chartEdits`,
`Orig2/FloatFiber.lean` §H4-§H5): nothing they cover exports
until that stub discharges, at which point the hoists drop per the
debt linkage.  AMENDMENT (2026-10-18): the stub's UNGATED shape is
refuted — the chart card landed it WF-GATED with a kernel
refutation of the ungated form (`Orig2/Chart.lean` §10-§11,
battery [propext, Quot.sound] / [propext]) — so the hoists above do
not drop verbatim: they await each site's mate-pinning amendment
(mate-side WF, or the card's conservation grade
`chart_round_trip_counts` via a count-neutral SeatEdit) — the
floater books' own debt, see the ledger's §1F UPDATE.  The
scrutiny phase's own flagship
candidate — `fiber_product_schematic`, the (Z/2)^k bit-group
decomposition over the `twinBit` index, `Orig2/ClaimsScrutiny.lean`
§S4 — is a PRICED SCHEMATIC carrying its honest sorry; it remains
the successor candidate, entering this door the day its quotient
formalization discharges.  No sorry, no forced premise, no
schematic ever exports as flagship.

## HOUSE COMPLIANCE

Additive leaf (import surface: `Orig2.OrbitFactor` +
`Orig2.RevSteps` + `Orig2.FloatOrbit`, hence the certified seam);
zero sorry; zero `Classical.choice`; per-file battery below —
profiles inherited from the proving cards, re-printed here per the
audit discipline.
-/

/-- **THE FLAGSHIP EXPORT** — the phase factorization at a citable
name: a reversible-class membership factors as a draw-free board
reshuffle to a phase-mate followed by a pure rotation round.  Trivial
forward of `sameOrbit_factor` (`Orig2/OrbitFactor.lean` §4b, battery
[propext, Quot.sound], zero sorry, zero choice) — every leg of both
channels reversible by construction, the license row below. -/
theorem flagship_sameOrbitFactor {u v : State} (hwf₁ : u.WF) (hwf₂ : v.WF) :
    sameOrbitSetoid.r u v ↔ ∃ z, NoDrawPlayW u z ∧ SWRotW z v :=
  sameOrbit_factor hwf₁ hwf₂

/-- **THE KEYSTONE LICENSE EXPORT** — over ANY letter family the dumb
both-ways span closure equals the reversible closure: the row the
flagship's every leg rides by construction.  Trivial forward of
`rev_steps_iff` (`Orig2/RevSteps.lean`, battery [propext], zero
sorry, zero choice). -/
theorem flagship_revStepsLicense (P : State → Move → Prop) (A B : State) :
    (Steps (StepOf P) A B ∧ Steps (StepOf P) B A) ↔
    (Steps (RevStep P) A B ∧ Steps (RevStep P) B A) :=
  rev_steps_iff P A B

/-- **THE CARGO-TIER KEYSTONE EXPORT** — the conservation law at a
citable name: along a whole bare-cargo class, which cards are
floaters is FIXED, card by card.  Trivial forward of
`floater_orbit_invariant` (`Orig2/FloatOrbit.lean`, promoted from
the dry-run 2026-10-17; battery [propext, Quot.sound], zero sorry,
zero choice; WF-gated). -/
theorem flagship_floaterOrbitInvariant {st w : State} {c : Card}
    (hpair : BareCargoEquiv st w) (hwf : st.WF) : Floater st c ↔ Floater w c :=
  floater_orbit_invariant hpair hwf

/-- **THE CLASS IFF EXPORT** — the bare-cargo class at a citable name, in
changed-card normal form: every card whose seat changes is either a licensed
twin hop or a licensed king landing on a node of the origin's fuel set, and
the readouts agree.  Trivial forward of `bareCargo_iff_vk`
(`Orig2/FloatOrbit.lean` §M11; battery [propext, Quot.sound], zero sorry,
zero choice; WF-gated both sides, which also supplies the chart round trip).
The redundant total per-card relation (unchanged arm and st-side king anchor)
stays in the direction lemmas `bareCargo_to_chartDiff_vk` /
`bareCargo_of_chartVK`. -/
theorem flagship_bareCargoIffVK {st w : State} (hwfst : st.WF) (hw : w.WF) :
    BareCargoEquiv st w ↔
      (∀ x, seatOf st x ≠ seatOf w x →
          (((∃ z', seatOf st x = some (Sum.inr z') ∧
                seatOf w x = some (Sum.inr z'.twin)) ∨
            (x.rank = Rank.king ∧ ∃ a', seatOf w x = some (Sum.inl a') ∧
              VKSet st a')) ∧ FloaterSpec st x)) ∧
      (boardFixed st w ∧ foundsFixed st w ∧
        drawPool st = drawPool w ∧ cutOf st = cutOf w) :=
  bareCargo_iff_vk hwfst hw

/-! ## The audit battery

Per exported head, re-printed per the per-file discipline: profiles
inherited verbatim from the proving cards. -/

#print axioms flagship_sameOrbitFactor
#print axioms flagship_revStepsLicense
#print axioms flagship_floaterOrbitInvariant
#print axioms flagship_bareCargoIffVK
