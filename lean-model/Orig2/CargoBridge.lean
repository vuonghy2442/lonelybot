import Orig2.Vocab
import Orig2.Claims

/-!
# Orig2.CargoBridge — THE EXCHANGE-BRIDGE CARD

THE CARD'S MISSION: the claims ledger's third priced stub — the
exchange bridge — discharged at span grade and promoted per the
rule.  Frozen bank (`Orig2/Claims.lean` §1C-3):

```
theorem dumbSpan_iff_exchange (A B : State) :
    (Steps (StepOf CargoLetter) A B ∧
      Steps (StepOf CargoLetter) B A) ↔ BareCargoEquiv A B
```

with `BareCargoEquiv A B := CargoPath A B ∧ CargoPath B A`
(registry §7 — the owner's enforcement restate: the official
exchange carries its `reversibleAtW` per leg BY CONSTRUCTION,
"so that it stays in class").  The claim's real content is the
ENFORCEMENT'S SOUNDNESS: the RAW both-ways dumb spans already
close into the enforced exchange — each leg of a both-ways dumb
span IS reversible, by the chain composite.

MID-MISSION RESTATE (recorded honestly): this card's charter at
issue was the WF-gated `bareCargo_iff_cargoPath` (the dumb
span-play closure vs. the dumb both-ways plays, agreed at WF).
While the card was in research the owner restated the exchange
at the enforcement (registry §7 + claims §1C-3, same day), and
the claim was trued to the gateless shape above — the original
deep half's WF gate priced out entirely.  This card builds the
trued bank; the WF premises never return.

THE GATE LEDGER: ZERO GATES.  The original charter priced the
deep half as a gated consumption of the classification claim
`reversibleOf_iff_reversibleAtW` (the tabToTabR-tabbed
dichotomy's slide half, then a sorry'd stub); the chain-composite
route below consumes NO classification row — the returning span,
realized through the banked bridge `steps_to_walk`, IS the
`reversibleAtW` witness, definitionally.  (For the record: the
classification sibling's claim has since DISCHARGED AND PROMOTED
anyway — five letters landed, c705fe4 — so the gate this card
never needed is green regardless.  Nothing gated, nothing
sorry'd, no physics kit, no WF accessor, no zone row enters this
card.)

LINEAGE (the frozen templates, read and cited, never imported):
`Orig/ForklessCeiling.lean` §0a-§0d — the dumb closure's frozen
home.  `CargoLetter` (:95) rides verbatim at the registry (§7);
`BareCargoEquiv` (:137) was frozen DUMB there, with per-leg
reversibility a THEOREM of the both-ways structure — and the
frozen file's insight, §0c.1's returning cycle ("each leg sits on
a returning cycle: its own tail plays joined through the
endpoint to the origin, then the origin's one-move re-entry",
`CargoPlayRF_of_return` :416-430, over the composite-position
kernel `cargoLeg_revealfree` :374), is EXACTLY this card's chain
half.  THE HONEST DEPARTURE, one step: the frozen route spent the
returning cycle on ARM-CLASSIFICATION physics — the hidden-total
monotone (`fcHiddenTotal_step` :286), §0c's burn/reveal
exclusion, §0d's one-move mirrors (`cargo_refines_sameOrbit`)
— because its destination was the surviving-alphabet packaging
(`CargoShuffle`) and the ceiling dream's Grade-B; the steps-first
restate (spans over `StepOf CargoLetter`, plays realized through
the banked generic bridges) lets the chain bank ONE STEP
EARLIER, at the witness grade: the leg's return span realizes to
a play, and that play IS the carrier's own existential.  The
zone-fix rows (`fc_step_zone` :162, `CargoPlay_fix_zone` :177)
never ride — the claim stands at the journey grade, and those
rows service the §0e/ceiling consumer tier (priced residue, §4).

House compliance: additive leaf over `Orig2.Vocab` +
`Orig2.Claims` (the closed seam — nothing above the certified
core enters the import graph); per-row provenance docstrings;
sections per half; zero sorry; zero `Classical.choice`; the
battery at the file's tail; frozen statements never
force-premised; commits staged green per batch.
-/

/-!
## §1. THE FORGETFUL HALF (the claim's easy direction)

A `CargoLeg` IS the shadow letter realized with its witness:
the leg's `∃ c b` unpacks into the `CargoLetter` payload plus
the fired step, and the span maps across letter-wise, both
directions at once.  No WF, no physics — the witness carries
MORE than the shadow asks.
-/

/-- A reversible cargo leg is a dumb shadow leg: the letter
unpacks, the step is read off the leg's own data.  The dual of
the registry's CargoLeg "trivial bridge" note (`Orig2/Vocab.lean`
§4 — a FlatStep with its cargo-kind witness IS a `CargoLeg`;
this is the same row read forgetfully); frozen template: the
pass-to-cargo forgetful row `CargoPlayRF_cargo`
(`Orig/ForklessCeiling.lean:403`). -/
theorem cargoLeg_to_shadow {w z : State} (h : CargoLeg w z) :
    StepOf CargoLetter w z := by
  obtain ⟨c, b, hstep, -⟩ := h
  exact ⟨Move.tabToTab c b, ⟨c, b, rfl⟩, hstep⟩

/-- Spans map across letters — the letter-wise cons-induction
(the span-side twin of the registry's `Walk_run`/`Walk_append`
support pattern: one induction for every letter grade, in the
Steps instance).  Private kit, per the dedup discipline. -/
private theorem steps_map {Q Q' : State → State → Prop}
    (hQ : ∀ w z, Q w z → Q' w z) {w u : State} :
    Steps Q w u → Steps Q' w u := by
  intro hs
  induction hs with
  | refl s => exact Steps.refl s
  | cons hleg t ih => exact Steps.cons (hQ _ _ hleg) ih

/-- Span transitivity — cons-induction on the leading span: the
span-grade restatement of the closure's transitivity engine (the
frozen `CargoPlay_append` at `Orig/ForklessCeiling.lean:118`,
which the §0c.1 frozen route consumed at the play grade through
`fc_run_append` :348; here the composite never leaves the span
grade).  Private kit, per the dedup discipline. -/
private theorem steps_trans {Q : State → State → Prop} :
    ∀ {a b c : State}, Steps Q a b → Steps Q b c → Steps Q a c := by
  intro a b c h1
  induction h1 with
  | refl s => intro h2; exact h2
  | cons hleg t ih => intro h2; exact Steps.cons hleg (ih h2)

/-- **THE FORGETFUL HALF** — the enforced exchange forgets to
the raw dumb spans: each witness leg is a dumb leg (§1's kernel),
and the span map carries both directions. -/
theorem exchange_to_dumbSpan {A B : State} (h : BareCargoEquiv A B) :
    Steps (StepOf CargoLetter) A B ∧
      Steps (StepOf CargoLetter) B A := by
  obtain ⟨hAB, hBA⟩ := h
  exact ⟨steps_map (fun _ _ hleg => cargoLeg_to_shadow hleg) hAB,
    steps_map (fun _ _ hleg => cargoLeg_to_shadow hleg) hBA⟩

/-!
## §2. THE CHAIN HALF (the claim's deep direction)

THE CROWN INSIGHT, §0c.1's returning cycle banked one step
earlier: a leg riding a both-ways exchange sits on a RETURNING
CYCLE — its successor spans back to its own origin by the
composite of the span's SUFFIX, the PARTNER span, and the
ACCUMULATED PREFIX.  THE STEPS-FIRST DIVIDEND: the composite
stays at the span grade all the way down, and the return span
realizes — one call through the banked bridge `steps_to_walk` —
into the return PLAY the carrier demands.  The witness is
HANDED by the exchange: no oracle, no WF, no physics.
-/

/-- **THE COMPOSITE-POSITION KERNEL, at the witness grade** —
a dumb leg whose successor spans back to its own origin IS
reversible: the return span realizes through the banked bridge
to a play, and the play IS the `reversibleAtW` witness,
definitionally.  Template: `cargoLeg_revealfree`
(`Orig/ForklessCeiling.lean:374-385`) — the frozen kernel bought
the SAME composite (a leg with a return, by any return play)
and spent it on reveal-freeness (a physics denial through the
hidden-total monotones); this row banks the composite on the
carrier itself, one step earlier. -/
theorem cargoLeg_of_dumbLeg {w z : State}
    (hleg : StepOf CargoLetter w z)
    (hret : Steps (StepOf CargoLetter) z w) : CargoLeg w z := by
  obtain ⟨m, ⟨c, b, hm⟩, hstep⟩ := hleg
  subst hm
  obtain ⟨ρ, hρ⟩ := steps_to_walk CargoLetter hret
  exact ⟨c, b, hstep, z, ρ, hstep, Walk_run CargoLetter hρ⟩

/-- **THE CHAIN INDUCTION** — every leg of a dumb span whose
endpoint carries a partner span back to the chain root is
reversible: the per-leg return is the composite suffix ++
partner span ++ accumulated prefix, walked by cons-induction
with the prefix transporter growing one leg per step.  The
span-grade restatement of the frozen returning-cycle freeze
`CargoPlayRF_of_return` (`Orig/ForklessCeiling.lean:416-430`);
the accumulator replaces the frozen route's join play
`fc_run_append` (:348) — at span grade, composition IS the
transport.  Private to the card; the public row below is its
specialization, and the same induction read at the partner
direction services the exchange's second account. -/
private theorem cargoPath_of_dumbSpan_aux (A : State) :
    ∀ {B X : State}, Steps (StepOf CargoLetter) X B →
      Steps (StepOf CargoLetter) B A →
      Steps (StepOf CargoLetter) A X →
      CargoPath X B := by
  intro B X s1
  induction s1 with
  | refl s => intro _ _; exact Steps.refl s
  | cons hleg t ih =>
      intro hBA π
      exact Steps.cons
        (cargoLeg_of_dumbLeg hleg (steps_trans (steps_trans t hBA) π))
        (ih hBA (steps_trans π (Steps.cons hleg (Steps.refl _))))

/-- **THE CHAIN HALF, ONE DIRECTION** — a both-ways dumb span
pair closes into the witness cargo path, leg by leg: each leg's
return is the rotated exchange. -/
theorem cargoPath_of_dumbSpan {A B : State}
    (hAB : Steps (StepOf CargoLetter) A B)
    (hBA : Steps (StepOf CargoLetter) B A) : CargoPath A B :=
  cargoPath_of_dumbSpan_aux A hAB hBA (Steps.refl A)

/-- **THE CHAIN HALF** — the raw both-ways dumb spans close
into the enforced exchange: each account by the chain
induction, the partner span playing the return. -/
theorem dumbSpan_to_exchange {A B : State}
    (hAB : Steps (StepOf CargoLetter) A B)
    (hBA : Steps (StepOf CargoLetter) B A) : BareCargoEquiv A B :=
  ⟨cargoPath_of_dumbSpan_aux A hAB hBA (Steps.refl A),
   cargoPath_of_dumbSpan_aux B hBA hAB (Steps.refl B)⟩

/-!
## §3. THE ASSEMBLY — THE CLAIM, DISCHARGED AND PROMOTED

The two halves compose into the frozen bank: the raw both-ways
dumb spans ARE the official exchange, exactly — the forgetful
map one way, the chain composite the other.  The statement
below is the frozen bank of `Orig2/Claims.lean` §1C-3, proved
here per the promotion rule (the stub deleted there, the
Claims battery line moved into this card's battery).
-/

/-- **CLAIM `dumbSpan_iff_exchange`** — the raw both-ways dumb
spans are the official exchange, exactly: the forgetful
letter-unpack one way, the returning-cycle chain composite the
other — gateless, WF-free, no oracle anywhere. -/
theorem dumbSpan_iff_exchange (A B : State) :
    (Steps (StepOf CargoLetter) A B ∧
      Steps (StepOf CargoLetter) B A) ↔ BareCargoEquiv A B :=
  ⟨fun h => dumbSpan_to_exchange h.1 h.2, exchange_to_dumbSpan⟩

/-!
## §4. PRICED RESIDUES (finer content this card does NOT carry)

One-line prices, for any future consumer:

* THE ONE-MOVE MIRRORS — "every surviving leg's undo collapses
  to ONE move at WF" — are the classification card's slide
  half (`tabToTabR_iff_reversibleAtW`, `Orig2/Classification.lean`;
  frozen homes `Orig/Classify.lean:1297,1417,1498,1653`,
  consumed there): this card's witness play is the full rotated
  exchange (any length); the collapse is strictly finer and
  stays upstream.
* THE ZONE-FIX ROWS (`fc_step_zone` :162, `CargoPlay_fix_zone`
  :177 — founds/stock/waste/deal size invariant under cargo
  travel) service the ceiling card's §0e fix tier; a future
  Grade-B consumer restates them at `Orig2` per the dedup
  discipline.  No zone row rides here.
* THE SURVIVING-ALPHABET PACKAGING (the frozen §0c-§0d route:
  reveal/burn arm exclusion then mirrors, `CargoShuffle`,
  `cargo_refines_sameOrbit`) is subsumed at witness grade by
  the chain half plus the classification card's denials (a
  shape-false leg admits no return span of any grain, so it
  cannot ride a both-ways pair); the arm-level analysis is the
  frozen tier's boundary data.

## §5. The audit battery

Per proved head, this card.  Expected profile: `[propext]` —
never `sorryAx`, never `Classical.choice`.  The claim's battery
line lives here since the promotion (see §3). -/

#print axioms cargoLeg_to_shadow
#print axioms exchange_to_dumbSpan
#print axioms cargoLeg_of_dumbLeg
#print axioms cargoPath_of_dumbSpan
#print axioms dumbSpan_to_exchange
#print axioms dumbSpan_iff_exchange
