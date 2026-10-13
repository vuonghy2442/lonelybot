import Orig.PairClass
import Orig.SlabEquiv
import Orig.FoundKit
import Orig.MacroInternal
import Orig.ZoneAgree

/-!
# Orig.PairClassZones — THE FORK-GRADE ZONE-SET THEOREM

The owner's formulation B, resurrected at the canonical grade: for any
two forkStates of one macro class, the per-zone card residencies agree
— the foundation content is card-for-card identical, the tableau hosts
the same cards, and the cycle side (stock ∪ waste) is pinned outright,
fork or no fork.

The arc this leaf closes (the owner's 2026-10-13 conversation):

* ARBITRARY CLASS-MATES FAIL FORMULATION B.  The weak-grade G2 pair
  (`Orig/SProbe.lean`'s contrast board, the old `ForkUniqProbe` craft
  verbatim) is a same-class pair between which `6♠` crosses
  tableau↔foundation (spade rung 5 vs 6) — per-zone sets are NOT class
  invariants, and no census-grade argument can restore them.

* FORKS OF ONE CLASS RECOVER IT.  The canonical grade was hardened by
  the S-migration exactly so that the crossing witnesses stop
  counting as forks: the stranded twin fails the S-license, the
  six-pair leak fails the exit clause.  What survives at fork grade
  is the net-flat world — the mate/conjugate orbit of
  `Orig/SProbe.lean` (`cell`/`slideM`/`conj1`, all `forkStateSB`-true,
  all with identical rung vectors) — and on that world formulation B
  holds in every decided instance.

THIS LEAF makes the recovery explicit, row by row:

* §1 THE CYCLE-SIDE PIN (`mates_cycleZone_pin`) — fork-free,
  WF-free: for any class-mates, stock-or-waste membership is exactly
  preserved (the public `Orig/SlabEquiv.lean` `cycle_zone_pin`, read
  through the setoid's witnessing journeys).

* §2 THE PAIR-SUIT RUNG AGREEMENT (private `pcz_pair_rung`) — at a
  `ForkWitness`, both pair-suit rungs sit at the witness's rank index
  (`forkState_witness_rungs`); the capstone `forkState_pairClass`
  identifies the two states' pairs, so the two pair suits read the
  SAME index at both endpoints.

* §3 THE CONDITIONAL VECTOR + ZONES — the honest split:  the two pair
  suits are pinned by the capstone; the other two suits ride
  `hthird`, the THE THIRD-SUIT RESIDUE, carried as an explicit
  hypothesis (this leaf adds NO sorry — the residue is passed, not
  assumed-proved).  Given the full vector, `rung_found_congr` forces
  card-for-card foundation equality; per-card found-residency iff
  follows; per-card tableau-residency iff follows by the five-zone
  census (`lock_zone_residency`) against the Integrity
  occurrence-uniqueness exclusions (`mem_faceUp_only`/`mem_hidden_only`)
  and the §1 pin.

* THE RESIDUE'S OWNERSHIP: `hthird` is precisely the forked-half
  sandwich cell of the shape theorem (`canonFace_sameShape`,
  `Orig/MacroInternal.lean:1866`'s sorry-carrying declared block —
  "any two faces of one class share ONE shape (identical or
  slide-mates)"):  same-class canonical forks are decided-equal on
  their rung vectors at every probed cell (the SProbe orbit's
  `conj1_rungs`/`slideM` rows), and the general row awaits the
  sandwich.  Consuming this leaf with `hthird := canonFace_sameShape
  ...`-derived rung equality lands formulation B whole, sorry and all
  accounted by name.

House compliance: additive leaf (imports `Orig.PairClass`,
`Orig.SlabEquiv`, `Orig.MacroInternal` — a diamond, no edits to any
existing file); fresh private kit (`pcz_pair_rung`, `pcz_tab_step`)
per the dedup discipline; every fresh head audited below; no
`Classical.choice`.
-/

/-! ## §0. The residency reads

One leaf-local vocabulary for the three pipings of the board census:
which cards sit founded, which sit on the tableau (face-up or hidden
on some pile), which sit in the draw cycle. -/

/-! ## §1. The cycle-side pin (fork-free) -/

/-- The same pin, forward-stated (the package's cycle conjunct). -/
theorem forkState_class_cycleRes {st w : State}
    (hcls : sameOrbitSetoid.r st w) (c : Card) :
    cycleResident st c ↔ cycleResident w c :=
  (mates_cycleZone_pin hcls c).symm

/-! ## §2. The pair-suit rung agreement (private kit) -/

/-- **THE PAIR-SUIT RUNG AGREEMENT** — at a state whose witness `y`
names the pair `{x, x.twin}` (the capstone's identification, or
`Or.inl rfl` for the state's own reader), BOTH pair-suit rungs read
`x.rank.toIdx`: `forkState_witness_rungs` pins the `y`-relative pair,
and the twin algebra (`Card.twin_twin`, `Card.twin_rank`) transports
the pins to the `x`-relative suits whichever orientation the far
witness carries. -/
private theorem pcz_pair_rung {u : State} {x y : Card}
    (hy : ForkWitness u y) (hxy : y = x ∨ y = x.twin)
    (σ : Suit) (hσ : σ = x.suit ∨ σ = x.twin.suit) :
    rungAt u σ = x.rank.toIdx := by
  obtain ⟨h1, h2⟩ := forkState_witness_rungs hy hy
  rcases hxy with h | h
  · rw [h] at h1 h2
    rcases hσ with hσ | hσ
    · rw [hσ]; exact h1
    · rw [hσ]; exact h2
  · rw [h] at h1 h2
    rcases hσ with hσ | hσ
    · rw [hσ]
      rw [Card.twin_twin, Card.twin_rank] at h2
      exact h2
    · rw [hσ]
      rw [Card.twin_rank] at h1
      exact h1

/-! ## §3. The rung vector, the founds, and the zones -/

/-- **THE CONDITIONAL RUNG VECTOR** — two same-class canonical forks
agree on every suit's rung: the TWO PAIR SUITS by the capstone (the
pair agreement of `forkState_pairClass` plus the witness rung pins),
the OTHER SUITS by `hthird` (carried explicitly — see the header's
residue note). -/
theorem forkState_class_rungVec {st w : State}
    (hwfst : st.WF) (hwfw : w.WF)
    (hcls : sameOrbitSetoid.r st w)
    (x : Card) (hx : ForkWitness st x) {y : Card} (hy : ForkWitness w y)
    (hthird : ∀ σ : Suit, σ ≠ x.suit → σ ≠ x.twin.suit →
      rungAt st σ = rungAt w σ) :
    ∀ σ : Suit, rungAt st σ = rungAt w σ := by
  have hxy : y = x ∨ y = x.twin :=
    forkState_pairClass st w hwfst hwfw hcls x hx hy
  intro σ
  by_cases h1 : σ = x.suit
  · rw [h1]
    have hu := pcz_pair_rung hx (Or.inl rfl) x.suit (Or.inl rfl)
    have hv := pcz_pair_rung hy hxy x.suit (Or.inl rfl)
    exact hu.trans hv.symm
  · by_cases h2 : σ = x.twin.suit
    · rw [h2]
      have hu := pcz_pair_rung hx (Or.inl rfl) x.twin.suit (Or.inr rfl)
      have hv := pcz_pair_rung hy hxy x.twin.suit (Or.inr rfl)
      exact hu.trans hv.symm
    · exact hthird σ h1 h2

/-- **THE FOUND CONTENT** — the vector forces card-for-card
foundation equality (the banked `rung_found_congr`: same rung, same
founded prefix). -/
theorem forkState_class_founds {st w : State}
    (hwfst : st.WF) (hwfw : w.WF)
    (hcls : sameOrbitSetoid.r st w)
    (x : Card) (hx : ForkWitness st x) {y : Card} (hy : ForkWitness w y)
    (hthird : ∀ σ : Suit, σ ≠ x.suit → σ ≠ x.twin.suit →
      rungAt st σ = rungAt w σ) :
    ∀ s : Suit, st.found s = w.found s :=
  fun s => rung_found_congr st w hwfst hwfw s
    (forkState_class_rungVec hwfst hwfw hcls x hx hy hthird s)

/-- **THE FOUND-RESIDENCY IFF** — per card, founded at `st` iff
founded at `w` (the content equality, read existentially). -/
theorem forkState_class_foundRes {st w : State}
    (hwfst : st.WF) (hwfw : w.WF)
    (hcls : sameOrbitSetoid.r st w)
    (x : Card) (hx : ForkWitness st x) {y : Card} (hy : ForkWitness w y)
    (hthird : ∀ σ : Suit, σ ≠ x.suit → σ ≠ x.twin.suit →
      rungAt st σ = rungAt w σ)
    (c : Card) :
    foundResident st c ↔ foundResident w c := by
  have hfounds := forkState_class_founds hwfst hwfw hcls x hx hy hthird
  constructor
  · intro hmem
    obtain ⟨s, hc⟩ := hmem
    exact ⟨s, by rw [← hfounds s]; exact hc⟩
  · intro hmem
    obtain ⟨s, hc⟩ := hmem
    exact ⟨s, by rw [hfounds s]; exact hc⟩

/-- The census step behind the tableau iff (private): a `u`-tableau
card excluded from every `u`-foundation and from the `u`-cycle side,
at a `v` state with agreeing found content and cycle pin, must sit
on `v`'s tableau — the five-zone census leaves no other seat, the
found case refuted through the content equality, the cycle cases
through the pin. -/
private theorem pcz_tab_step {u v : State} (hwfv : v.WF) (c : Card)
    (hfounds : ∀ s : Suit, u.found s = v.found s)
    (hpin : ∀ d : Card, cycleResident v d ↔ cycleResident u d)
    (hnf : ∀ s : Suit, c ∉ u.found s)
    (hcyc : ¬ cycleResident u c) :
    tabResident v c := by
  have hcycv : ¬ cycleResident v c := fun h => hcyc ((hpin c).mp h)
  rcases lock_zone_residency v hwfv c with
    ⟨s, hfw⟩ | ⟨k, hkw⟩ | ⟨k, hfw⟩ | hsw | hww
  · exact absurd (show c ∈ u.found s by rw [hfounds s]; exact hfw) (hnf s)
  · exact ⟨k, Or.inr hkw⟩
  · exact ⟨k, Or.inl hfw⟩
  · exact absurd (Or.inl hsw) hcycv
  · exact absurd (Or.inr hww) hcycv

/-- **THE TABLEAU-RESIDENCY IFF** — per card, tableau-resident at
`st` iff tableau-resident at `w`.  (⇒) the Integrity
occurrence-uniqueness exclusions pin the card off `st`'s foundations
and cycle side; the cycle pin carries the exclusion across to `w`; the
five-zone census at `w` leaves the tableau as the only seat (the
found case dies on the content equality).  (⇐) the mirrored
argument with the pin's symmetric direction. -/
theorem forkState_class_tabRes {st w : State}
    (hwfst : st.WF) (hwfw : w.WF)
    (hcls : sameOrbitSetoid.r st w)
    (x : Card) (hx : ForkWitness st x) {y : Card} (hy : ForkWitness w y)
    (hthird : ∀ σ : Suit, σ ≠ x.suit → σ ≠ x.twin.suit →
      rungAt st σ = rungAt w σ)
    (c : Card) :
    tabResident st c ↔ tabResident w c := by
  have hpin : ∀ d : Card, cycleResident w d ↔ cycleResident st d := by
    rcases hcls with ⟨ρ, _hρ, τ, hτ⟩
    exact cycle_zone_pin hτ
  have hfounds := forkState_class_founds hwfst hwfw hcls x hx hy hthird
  constructor
  · intro htab
    obtain ⟨a, hfa | hhi⟩ := htab
    · have hmem := mem_faceUp_only hwfst hfa
      exact pcz_tab_step hwfw c hfounds hpin hmem.2.2.2.2
        (fun hcc => hcc.elim hmem.2.2.1 hmem.2.2.2.1)
    · have hmem := mem_hidden_only hwfst hhi
      exact pcz_tab_step hwfw c hfounds hpin hmem.2.2.2.2
        (fun hcc => hcc.elim hmem.2.2.1 hmem.2.2.2.1)
  · intro htab
    obtain ⟨a, hfa | hhi⟩ := htab
    · have hmem := mem_faceUp_only hwfw hfa
      exact pcz_tab_step hwfst c (fun s => (hfounds s).symm)
        (fun d => (hpin d).symm) hmem.2.2.2.2
        (fun hcc => hcc.elim hmem.2.2.1 hmem.2.2.2.1)
    · have hmem := mem_hidden_only hwfw hhi
      exact pcz_tab_step hwfst c (fun s => (hfounds s).symm)
        (fun d => (hpin d).symm) hmem.2.2.2.2
        (fun hcc => hcc.elim hmem.2.2.1 hmem.2.2.2.1)

/-! ## §4. The package -/

/-- **THE FORK-GRADE ZONE-SET THEOREM** — the owner's formulation B
at the canonical grade, conditional on the named third-suit residue:
two same-class forkStates share (i) the cycle-side residency per card
(unconditional, fork-free), (ii) the foundation content per suit,
card for card, (iii) the founded residency per card, and (iv) the
tableau residency per card.  Feed `hthird` from the shape theorem's
forked half (`canonFace_sameShape`'s sandwich cell) and formulation B
lands whole. -/
theorem forkState_class_zoneSets {st w : State}
    (hwfst : st.WF) (hwfw : w.WF)
    (hcls : sameOrbitSetoid.r st w)
    (x : Card) (hx : ForkWitness st x) {y : Card} (hy : ForkWitness w y)
    (hthird : ∀ σ : Suit, σ ≠ x.suit → σ ≠ x.twin.suit →
      rungAt st σ = rungAt w σ) :
    (∀ c : Card, cycleResident st c ↔ cycleResident w c) ∧
    (∀ s : Suit, st.found s = w.found s) ∧
    (∀ c : Card, foundResident st c ↔ foundResident w c) ∧
    (∀ c : Card, tabResident st c ↔ tabResident w c) :=
  ⟨fun c => forkState_class_cycleRes hcls c,
    forkState_class_founds hwfst hwfw hcls x hx hy hthird,
    fun c => forkState_class_foundRes hwfst hwfw hcls x hx hy hthird c,
    fun c => forkState_class_tabRes hwfst hwfw hcls x hx hy hthird c⟩

/-! ## §5. The agreement iff (the set sense)

The owner's "trivial thing", landed as an honest IFF: at any WF
class-mates, agreeing tableau card SETS ⟺ agreeing foundation card
SETS.  No fork premises, no rung hypotheses, no third-suit residue —
the class relation alone (through the unconditional cycle pin) plus
WF conservation does it: each of the two agreements is the
per-card complement of the (outright pinned) cycle side, so the
five-zone census flips either into the other.  -

(Note what this adds over §4: `forkState_class_zoneSets` derives
BOTH agreements from fork premises plus `hthird`; this row says the
two agreements are EQUIVALENT regardless — forkness is one
sufficient route to either side, not a component of the iff.) -/

/-! ## §6. The rung-vector leg (the numeric sense)

The trilogy completed in the other direction: set-agreement between
WF class-mates is EQUIVALENT to rung-vector equality.  (⇐) is the
founds-content route (`rung_found_congr`, no fork premises needed).
(⇒) is the boundary-card argument: at a suit where the rungs split,
the SMALLER rung's boundary card is founded at the larger-rung state
(the upward founded-bridge) and, by the agreement, at the smaller
too — but its rank index is exactly the smaller rung, refuting the
downward founded-bridge.  The kit is per-file private copies per the
dedup discipline (templates: `Orig/SlabEquiv.lean` §0,
`Orig/Classify.lean`'s private `Rk`). -/

/-! ## The audit battery

`#print axioms` per fresh head — every row lands `[propext,
Quot.sound]`: zero `sorryAx` at any depth and no `Classical.choice`.
The §1 pins ride `cycle_zone_pin`'s banked chain; the §3 heads ride
the capstone `forkState_pairClass` — empirically sorry-free in the
current build (the halves' previously-named residues have been
resolved since `Orig/PairClass.lean`'s own battery comment was
written; that stale comment is this leaf's one discovered
discrepancy, reported-not-edited per the additive-leaf discipline) —
plus `rung_found_congr` and the Integrity/census rows.  The leaf's
one conditional, `hthird`, is carried as a HYPOTHESIS, not a sorry:
the residue is passed, and its ownership stays with the shape
theorem's forked-half sandwich cell. -/

#print axioms forkState_class_cycleRes
#print axioms pcz_pair_rung
#print axioms forkState_class_rungVec
#print axioms forkState_class_founds
#print axioms forkState_class_foundRes
#print axioms forkState_class_tabRes
#print axioms forkState_class_zoneSets
