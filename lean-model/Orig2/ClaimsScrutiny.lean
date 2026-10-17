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

/-! ## §S4. The fiber decomposition — CANDIDATE (the corrected
product claim; the pending re-run time-stamps the empirical side) -/

/-- **THE FIBER PRODUCT** — over fixed founds, the enriched
component quotients into pure exchange orbits crossed with a
genuine (Z/2)^k twin-pair bit group over the twinBit index: the
enriched connectivity between two fiber-mates factors as same
pure-orbit-component times the bit-parity over their live bits
(same-family bits serialized-recomputed, cross-family
column-decomposed; k is per-member — availability is
member-dependent, world D).  EVIDENCE: memo §8 (the Q₃ cube, the
compiled Hamming-2 pair), §10-§12 (legality-by-construction, the
ladder-clause canonical route, the three holes measured).
PRICE (promotion): the re-aimed probe pass over the registry
alphabet (memo §16, in flight) + the Hamming quotient
formalization over ExchBoth-pure-orbit components; the world-D
liberty refute keeps k member-indexed.  The statement below is
the honest schematic (the quotient-formalization is part of the
priced work): -/
theorem fiber_product_schematic :
    ∀ (u v : State), u.WF → v.WF → u.found = v.found →
      (ExchBoth u v ∨ ¬ ExchBoth u v) := by
  sorry

/-! ## §S5. The keystone reference (ALREADY CERTIFIED —
the license every spine/fiber row rides) -/

/- `rev_steps_iff` (`Orig2/RevSteps.lean`, [propext], installed
2026-10-17): over ANY letter family, the dumb both-ways span closure
equals the reversible closure — every witness leg above is
reversible BY CONSTRUCTION, never by force.  No stub here; the row
certified and carded the same hour. -/

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
-- schematic placeholder battery line: the fiber row carries the
-- priced schematic pending the quotient formalization (see the row's docstring); the battery line below will name the discharged head at promotion. -/
-- #print axioms fiber_product_schematic (priced schematic)
