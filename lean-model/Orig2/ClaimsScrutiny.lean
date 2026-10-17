import Orig2.Vocab
import Orig2.RevSteps
import Orig2.FloatFiber

/-!
# Orig2.ClaimsScrutiny — THE CANDIDATE LEDGER (the statements under
active scrutiny, 2026-10-17)

The scrutiny phase's products — the collapse program's refutations
(the four tombstones), its constructive survivors (the class spine,
the pins, the product decomposition), and the candidate vocabulary
they need — banked in one ledger at the claims layer.  STATUS
vocabulary per row:

* REFUTED-PROBE-COMPILED: the negative witness is compiled in the
  probe's scratch (`Temp/collapse_probe.lean`, battery
  `[propext, Quot.sound]`, zero sorry; memo
  `Temp/collapse_probe_memo.md`): the stub below is the statement,
  the verdict-grade proof already exists outside the tree, and
  promotion = porting the scratch rows into a card (the four
  tombstones then carry the fences as early warnings rather than
  the false statements ever re-landing);
* POSITIVE-PROBE-WITNESSED: a positive instance compiled, the
  general row still open;
* CANDIDATE: the statement is the corrected formulation of the
  scrutiny's surviving content, priced for the pending
  verification round (a re-aimed probe pass over the registry
  alphabet).

House compliance: additive leaf (import surface:
`Orig2.Vocab` + `Orig2.RevSteps` + `Orig2.FloatFiber`, hence the
certified seam); the candidate DEFS live here with
candidate-vocabulary markers (they promote to the registry, never
owned here past the scrutiny); the stubs carry their
evidence/price docstrings; zero forced premises; battery lines on
whatever proves in-place. -/

/-! ## §S0. Candidate vocabulary (scrutiniy-grade; promote to
`Orig2/Vocab.lean` when their rows certify) -/

/-- **ExchLetter w u** — THE ENRICHED-ALPHABET CANDIDATE: fired
reversible `tabToTab` legs ∪ the registry's uniform twin letter at
located pairs.  The COARSEST reading (a superset of the frozen licensed + both-occupied forms — so any refutation over it is a fortiori). -/
def ExchLetter (w u : State) : Prop :=
  (∃ c b, w.step (Move.tabToTab c b) = some u ∧
      reversibleAtW w (Move.tabToTab c b)) ∨
  ∃ t, twinPairSwap w u t

/-- **ExchBoth u v** — the two-way enriched closure over ExchLetter. -/
def ExchBoth (u v : State) : Prop :=
  Steps ExchLetter u v ∧ Steps ExchLetter v u

/-- **twinBit st c** — THE GENUINE-BIT INDEX (the corrected bit
inventory): the twin interchange of ⟨c, c.twin⟩ is in-class yet
cargo-blind.  Occupancy is a proxy (wrong for kings and for
licensed pairs cargo already realizes); reachability-discrepancy is
the honest index — with a staging anchor a king pair is absorbed
into the pure orbit (three bare-king vacates are cargo legs);
without one it is unswappable (no bit); rider-locked pairs are the
genuine bits. -/
def twinBit (st : State) (c : Card) : Prop :=
  ∃ v, twinPairSwap st v c ∧ sameOrbitSetoid.r st v ∧
    ¬ BareCargoEquiv st v

/-! ## §S1. The layer-collapse family — REFUTED-PROBE-COMPILED (the
four tombstones; strongest premise sets; never re-land as stated) -/

/-- **TOMBSTONE T1a** — the pure layer-collapse lemma is FALSE
(WF-gated reading — and a fortiori ungated).  Witness A: 7 bare
singleton piles, the licensed kings swapped through found-grade
round trips; the pure cargo closure of the seed is the singleton.
EVIDENCE: `collapse_pure_false` compiled at
`Temp/collapse_probe.lean` (battery [propext, Quot.sound]); memo
§2-§4.  PRICE (promotion): mechanical port of the scratch rows
into a tribunal card. -/
theorem tombstone_pure :
    ¬ (∀ u z : State, u.WF → z.WF → NoDrawPlayW u z → u.found = z.found →
        BareCargoEquiv u z) := by
  sorry

/-- **TOMBSTONE T1b** — the TwinExchangeBoth-absorbed (enriched)
lemma is FALSE as stated, over the coarsest ExchLetter.  Witness A
again: every swap letter degenerates at both-bare pairs, the
enriched closure is the singleton `= {uA}`.  EVIDENCE:
`collapse_exchboth_false`, same scratch/memo. -/
theorem tombstone_enriched :
    ¬ (∀ u z : State, u.WF → z.WF → NoDrawPlayW u z → u.found = z.found →
        ExchBoth u z) := by
  sorry

/-- **TOMBSTONE T2a** — the honest-orientation class corollary is
FALSE (u's board at v's frame — the only orientation with content
against the certified phase factorization).  EVIDENCE:
`collapse_classCorollary_honest_false` (witness A; atSplitOf is the
identity there).  The atSplitOf record edit is a candidate def
(u with v's stock/waste split); stated abstractly here to keep the
ledger self-contained — the scratch rows carry the concrete form. -/
theorem tombstone_corollary_honest :
    ¬ (∀ (u v : State), u.WF → v.WF → sameOrbitSetoid.r u v →
        u.found = v.found →
        (v.stock = u.stock ∨ v.waste = u.waste ∨
          u.stock = [] ∧ u.waste = [] ∧ v.stock = [] ∧ v.waste = []) ∧
        ExchBoth u v) := by
  sorry

/-- **TOMBSTONE T2b** — the charter-literal corollary orientation
is FALSE as well (split-invariance grade: exchange letters pin the
split, the rotation lives on the other axis; witness u_s/v_s, a
reversible one-draw pair).  EVIDENCE:
`charter_split_orientation_false` (memo §4: the split-rotation
witness).  WORDING REPAIR upstream: the honest orientation is T2a's;
neither survives. -/
theorem tombstone_corollary_literal :
    ¬ (∀ u v : State, u.WF → v.WF → sameOrbitSetoid.r u v →
        u.found = v.found → ExchBoth u v) := by
  sorry

/-! ## §S2. The positive instance — POSITIVE-PROBE-WITNESSED -/

/-- **WITNESS B** — the owner's twin-suffix obstruction, repaired
by the letter: a both-occupied twin-adjacent pair whose pure cargo
connection fails by the frozen seat lock closes in ONE enriched
letter.  EVIDENCE: `witnessB_enriched` compiled; the pure-side
840-state cargo closure was model-checked exhaustively (the seat
lock, `Orig/TwinExchangeBoth.lean` §4).  PRICE (promotion): the
positive row firms as the suffix-face absorption row (the licensed + both-occupied forms realize in-class; the one-swap bound was
already refuted globally, so the row is the FIRST nontrivial
absorption instance, not a bridge claim). -/
theorem witnessB_suffix_positive :
    ∃ (u w : State) (c : Card), u.WF ∧ w.WF ∧ NoDrawPlayW u w ∧
      u.found = w.found ∧ ExchBoth u w ∧
      (∃ v, twinPairSwap u v c ∧ ¬ BareCargoEquiv u v) := by
  sorry

/-! ## §S3. The surviving spine — CANDIDATE (probe-witnessed at
every world measured; the honest refactor of the refuted towers) -/

/-- **THE CLASS SPINE** — a class membership decomposes as the
pins (hidden decks, deal quantum, pool content), the phase
compatibility (`phaseFixed`, the frozen `SWComp` shape — a genuine
class invariant, draw legs keep it), and the certified
board-closure-then-rotation factor.  EVIDENCE: consequence rows
are all certified consequences of the closure(s) — pins hold along
every witness leg (probe memo §1; `class_pins` price in §S3.1),
`sameOrbit_factor` is the certified card
(`Orig2/OrbitFactor.lean`), and the ⟸ direction IS that card at
the pins-compatible phase.  PRICE (promotion): assemble the three
consequence rows (pins, phase) out of the frozen-certified
`shuffle_hiddenPinned`, the cycle pins, and the draw-keeps-inPhase
kit (all already in-tree at frozen grade); the iff then rides the
certified factor for both directions. -/
theorem spine_class :
    ∀ (u v : State), u.WF → v.WF →
      (sameOrbitSetoid.r u v ↔
        ((∀ a, (u.piles a).hidden = (v.piles a).hidden) ∧
          u.drawStep = v.drawStep ∧ drawPool u = drawPool v ∧
          phaseFixed u v ∧
          (∃ z, NoDrawPlayW u z ∧ SWRotW z v))) := by
  sorry

/-! ## §S3.1 The pins — CANDIDATE (probe-witnessed consequence
rows; the analysis's `class_pins` + card-zone) -/

/-- **THE CLASS PINS** — hidden decks, deal quantum, pool content,
phase line: preserved along every same-orbit journey.  EVIDENCE:
probe memo §1 (all legs keep them; the reversible cells' arm
analysis is the mechanism — reveal arms are exactly the commit
cells).  Frozen homes: `shuffle_hiddenPinned`,
`cycle_zone_pin`-family, the zero-write ledger. -/
theorem class_pins_row :
    ∀ (u v : State), u.WF → v.WF → sameOrbitSetoid.r u v →
      ((∀ a, (u.piles a).hidden = (v.piles a).hidden) ∧
        u.drawStep = v.drawStep ∧ drawPool u = drawPool v ∧
        phaseFixed u v) := by
  sorry

/-- **THE CARD-ZONE INVARIANT** — stock-or-waste membership is
exactly preserved along the class.  EVIDENCE: memo §1 (`class_cardZone`); frozen home the cycle census (pool + membership conservation). -/
theorem class_card_zone :
    ∀ (u v : State), sameOrbitSetoid.r u v → ∀ (c : Card),
      (c ∈ u.stock ∨ c ∈ u.waste) ↔ (c ∈ v.stock ∨ c ∈ v.waste) := by
  sorry

/-! ## §S4. The fiber decomposition — CANDIDATE (EVIDENCE UPGRADED
2026-10-17 by the re-run: memo §17, the torseur 86/86, and the
product-exactness table; the price is largely PAID — see the row) -/

/-- **THE FIBER PRODUCT** — over fixed founds, the enriched
component quotients into pure exchange orbits crossed with a
genuine (Z/2)^k twin-pair bit group over the twinBit index: the
enriched connectivity between two fiber-mates factors as same
pure-orbit-component times the bit-parity over their live bits
(same-family bits serialized-recomputed, cross-family
column-decomposed; k is per-member — availability is
member-dependent, world D).  EVIDENCE (UPGRADED): the re-run at the
REGISTRY alphabet (memo §17, instrument `--rerun11`,
`Temp/probe_rerun11_report.txt`): the product factorization
`closure = pureOrbit × 2^k` held EXACTLY at every exhaustive seed
(A: 4 = 1·2²; B: 6720 = 840·2³; C'' 13440; D: 128; E: 30720); the
torseur test (memo §13, §14's reduction, instrument `--torseur`):
86/86 subsets certified EXACT by explicit serialized synthesis,
zero order-freedom violations (the earlier violations were an
instrument bug, re-verified rfl-grade); one-swap thinness FALSE at
every seed under the uniform alphabet (the arena where a thin
bridge could have recovered).  REMAINING PRICE (shrunk): (i) the
quotient formalization over ExchBoth-orbit components; (ii) the
prelude family's completeness beyond depth-2 ladders (budget-open
at dense worlds, §12/H3); (iii) witness A's cross-pair boundary
belongs to the CLASS program (the lattice covers the fiber's
measured class slices; cross-pair transpositions stay outside —
the tombstones' exact reason).  The statement below is the honest
schematic until the quotient formalization lands. -/
theorem fiber_product_schematic :
    ∀ (u v : State), u.WF → v.WF → u.found = v.found →
      (ExchBoth u v ∨ ¬ ExchBoth u v) := by
  sorry

/-! ## §S4.5 The corrected fiber-transfer — CANDIDATE (SURVIVED
BOTH KILL-TARGETS at probe grade; memo §16, the addendum-#10 form) -/

/-- **FIBER-TRANSFER, CORRECTED** — within one foundation fiber,
swap-availability transfers along the class: if the twin
interchange of ⟨x, x.twin⟩ is in-class at s, then at any
class-mate s′ with the SAME founds and both twins still seated,
the interchange is in-class too.  The founds hypothesis is
necessary-and-EXHIBITED (memo §16 Target 1: cross-fiber walks
shut licensure windows — height-indexed reads — at distance; and
Target 2's bare-vs-covered divergence sits across fibers) but
never breaches a fiber from inside: the window-walk's own debris
RE-ARMS the licensure ladder (pulled window-cards land as
licensed raisable tops, the self-arming law), and the
both-covered deadlock dissolves at licensed windows (the cover's
self-raise) or dissolves into ladders (a 7-legged route, labeled
TRUNCATED-at-budget, never falsely "failing").  EVIDENCE: memo
§§9/14/16/17 — transfer member-invariant at every sampled member
of every seed under the REGISTRY availability reading (A
informative at 2 bits); the counterexample pair did not
materialize at any probed world.  PRICE (promotion): the
addendum-#8 reduction rides (transfer + the 3-line induction ⇒
closure), so this row firms together with the torseur
formalization of §S4. -/
theorem fiber_transfer_corrected :
    ∀ (s s' : State) (x : Card), s.WF → s'.WF →
      sameOrbitSetoid.r s s' → s.found = s'.found →
      (∃ v, twinPairSwap s v x ∧ sameOrbitSetoid.r s v) →
      (∃ seatA, s'.pileHolding x = some seatA) →
      (∃ seatA', s'.pileHolding x.twin = some seatA') →
      (∃ v', twinPairSwap s' v' x ∧ sameOrbitSetoid.r s' v') := by
  sorry

/- §S5. The keystone reference (ALREADY CERTIFIED — the license
every spine/fiber row rides) -/

/- rev_steps_iff (`Orig2/RevSteps.lean`, [propext], installed
2026-10-17): over ANY letter family, the dumb both-ways span closure
equals the reversible closure — every witness leg above is
reversible BY CONSTRUCTION, never by force.  No stub here; the row
certified and carded the same hour. -/

/- ALSO CERTIFIED THIS HOUR (no stub here; the license rows the
   ledger's every spine/fiber row rides): `rev_steps_iff` at
   `Orig2/RevSteps.lean` ([propext] — every witness leg reversible
   by construction) AND `floater_orbit_invariant` at
   `Orig2/FloatOrbit.lean` ([propext, Quot.sound] — the twin-fiber
   forcing conservation; the owner's proof, the coordinator
   retraction logged) both certified and carded the same hour. -/

/-! ## The audit battery

This ledger's stubs deliberately carry their sorry as the honest
debt of the SCRUTINY STATUS — each stub's docstring carries its
evidence and its promotion price.  A stub discharges when its
scratch rows port to a tribunal card (refutations) or its
verification round lands (candidates); the ledger then promotes and
the stub is deleted per the claims-layer rule. -/

#print axioms tombstone_pure
#print axioms tombstone_enriched
#print axioms tombstone_corollary_honest
#print axioms tombstone_corollary_literal
#print axioms witnessB_suffix_positive
#print axioms spine_class
#print axioms class_pins_row
#print axioms class_card_zone
#print axioms fiber_product_schematic
#print axioms fiber_transfer_corrected
