import Orig.PairClass
import Orig.SlabEquiv
import Orig.MacroInternal

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

/-- Foundation residency: the card sits on some suit's foundation. -/
def foundResident (st : State) (c : Card) : Prop :=
  ∃ s, c ∈ st.found s

/-- Tableau residency: the card sits face-up or hidden on some pile. -/
def tabResident (st : State) (c : Card) : Prop :=
  ∃ a, c ∈ (st.piles a).faceUp ∨ c ∈ (st.piles a).hidden

/-- Cycle residency: the card sits in the stock or the waste. -/
def cycleResident (st : State) (c : Card) : Prop :=
  c ∈ st.stock ∨ c ∈ st.waste

/-! ## §1. The cycle-side pin (fork-free) -/

/-- **THE CYCLE-SIDE PIN** — for ANY two class-mates (no WF, no fork
grades): stock-or-waste membership is exactly preserved.  The setoid
unfolds to the witnessing journeys (`RevEqW` both ways), and the
second conjunct feeds `Orig/SlabEquiv.lean`'s public
`cycle_zone_pin`; the pin's own iff already covers both directions,
so one journey suffices. -/
theorem mates_cycleZone_pin {st w : State}
    (hcls : sameOrbitSetoid.r st w) (c : Card) :
    cycleResident w c ↔ cycleResident st c := by
  rcases hcls with ⟨ρ, _hρ, τ, hτ⟩
  exact cycle_zone_pin hτ c

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

/-- The census floor for the founded direction (private): a card
excluded from `u`'s tableau and cycle side — at a `v` agreeing on the
tableau and cycle — must be founded at `v`; the five-zone census
leaves no other seat. -/
private theorem pcz_found_floor {u v : State} (hwfv : v.WF) (c : Card)
    (htab : ∀ d : Card, tabResident u d ↔ tabResident v d)
    (hpin : ∀ d : Card, cycleResident v d ↔ cycleResident u d)
    (hntab : ¬ tabResident u c) (hcyc : ¬ cycleResident u c) :
    foundResident v c := by
  have hntabv : ¬ tabResident v c := fun h => hntab ((htab c).mpr h)
  have hcycv : ¬ cycleResident v c := fun h => hcyc ((hpin c).mp h)
  rcases lock_zone_residency v hwfv c with
    ⟨s, hfw⟩ | ⟨k, hkw⟩ | ⟨k, hfw⟩ | hsw | hww
  · exact ⟨s, hfw⟩
  · exact absurd ⟨k, Or.inr hkw⟩ hntabv
  · exact absurd ⟨k, Or.inl hfw⟩ hntabv
  · exact absurd (Or.inl hsw) hcycv
  · exact absurd (Or.inr hww) hcycv

/-- The census floor for the tableau direction (private): a card
excluded from `u`'s foundations and cycle side — at a `v` agreeing on
the founds and cycle — must sit on `v`'s tableau. -/
private theorem pcz_tab_floor {u v : State} (hwfv : v.WF) (c : Card)
    (hfound : ∀ d : Card, foundResident u d ↔ foundResident v d)
    (hpin : ∀ d : Card, cycleResident v d ↔ cycleResident u d)
    (hnf : ¬ foundResident u c) (hcyc : ¬ cycleResident u c) :
    tabResident v c := by
  have hnuv : ¬ foundResident v c := fun h => hnf ((hfound c).mpr h)
  have hcycv : ¬ cycleResident v c := fun h => hcyc ((hpin c).mp h)
  rcases lock_zone_residency v hwfv c with
    ⟨s, hfw⟩ | ⟨k, hkw⟩ | ⟨k, hfw⟩ | hsw | hww
  · exact absurd ⟨s, hfw⟩ hnuv
  · exact ⟨k, Or.inr hkw⟩
  · exact ⟨k, Or.inl hfw⟩
  · exact absurd (Or.inl hsw) hcycv
  · exact absurd (Or.inr hww) hcycv

/-- **THE AGREEMENT IFF** — at WF class-mates, same tableau card set
⟺ same foundation card set.  (⇒) a founded card is pinned off `u`'s
tableau and cycle side (`mem_found_unique`); the tableau agreement
and the cycle pin carry both exclusions to `v`; the census leaves
`v`'s foundations as the only seat.  (⇐) the mirror with
`mem_faceUp_only`/`mem_hidden_only` against the founded agreement;
the census leaves `v`'s tableau. -/
theorem class_zoneAgree_iff {st w : State} (hwfst : st.WF) (hwfw : w.WF)
    (hcls : sameOrbitSetoid.r st w) :
    (∀ c : Card, tabResident st c ↔ tabResident w c) ↔
      (∀ c : Card, foundResident st c ↔ foundResident w c) := by
  have hpin : ∀ d : Card, cycleResident w d ↔ cycleResident st d :=
    mates_cycleZone_pin hcls
  constructor
  · intro htab c
    constructor
    · intro hfound
      obtain ⟨s, hfs⟩ := hfound
      have hmem := mem_found_unique hwfst hfs
      refine pcz_found_floor hwfw c htab hpin ?_
        (fun hcc => hcc.elim hmem.2.1 hmem.2.2.1)
      intro htu
      obtain ⟨a, hf | hh⟩ := htu
      · exact (hmem.1 a).2 hf
      · exact (hmem.1 a).1 hh
    · intro hfound
      obtain ⟨s, hfw⟩ := hfound
      have hmem := mem_found_unique hwfw hfw
      refine pcz_found_floor hwfst c (fun d => (htab d).symm)
        (fun d => (hpin d).symm) ?_
        (fun hcc => hcc.elim hmem.2.1 hmem.2.2.1)
      intro htu
      obtain ⟨a, hf | hh⟩ := htu
      · exact (hmem.1 a).2 hf
      · exact (hmem.1 a).1 hh
  · intro hfound c
    constructor
    · intro htab
      obtain ⟨a, hf | hh⟩ := htab
      · have hmem := mem_faceUp_only hwfst hf
        refine pcz_tab_floor hwfw c hfound hpin ?_
          (fun hcc => hcc.elim hmem.2.2.1 hmem.2.2.2.1)
        intro hfr
        obtain ⟨s, hcs⟩ := hfr
        exact hmem.2.2.2.2 s hcs
      · have hmem := mem_hidden_only hwfst hh
        refine pcz_tab_floor hwfw c hfound hpin ?_
          (fun hcc => hcc.elim hmem.2.2.1 hmem.2.2.2.1)
        intro hfr
        obtain ⟨s, hcs⟩ := hfr
        exact hmem.2.2.2.2 s hcs
    · intro htab
      obtain ⟨a, hf | hh⟩ := htab
      · have hmem := mem_faceUp_only hwfw hf
        refine pcz_tab_floor hwfst c (fun d => (hfound d).symm)
          (fun d => (hpin d).symm) ?_
          (fun hcc => hcc.elim hmem.2.2.1 hmem.2.2.2.1)
        intro hfr
        obtain ⟨s, hcs⟩ := hfr
        exact hmem.2.2.2.2 s hcs
      · have hmem := mem_hidden_only hwfw hh
        refine pcz_tab_floor hwfst c (fun d => (hfound d).symm)
          (fun d => (hpin d).symm) ?_
          (fun hcc => hcc.elim hmem.2.2.1 hmem.2.2.2.1)
        intro hfr
        obtain ⟨s, hcs⟩ := hfr
        exact hmem.2.2.2.2 s hcs

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

/-- The position of `x` in `l` (its first-occurrence index) — the
per-file copy of the take-position kit (template:
`Orig/SlabEquiv.lean` §0's `sequ_posOf`). -/
private def pcz_posOf {α : Type} [DecidableEq α] (x : α) : List α → Nat
  | [] => 0
  | y :: t => if y = x then 0 else pcz_posOf x t + 1

/-- Membership in a bounded take bounds the first-occurrence position
(the per-file copy of `sequ_mem_take_pos`). -/
private theorem pcz_mem_take_pos {α : Type} [DecidableEq α] :
    ∀ (n : Nat) (l : List α) (x : α), x ∈ l.take n → pcz_posOf x l < n := by
  intro n
  induction n with
  | zero =>
      intro l x hmem
      simp [List.take] at hmem
  | succ n ih =>
      intro l x hmem
      cases l with
      | nil => simp [List.take] at hmem
      | cons y t =>
          rw [List.take_succ_cons] at hmem
          by_cases hyx : y = x
          · have hp : pcz_posOf x (y :: t) = 0 := by
              show (if y = x then 0 else pcz_posOf x t + 1) = 0
              rw [ite_eq_left hyx]
            omega
          · have hp : pcz_posOf x (y :: t) = pcz_posOf x t + 1 := by
              show (if y = x then 0 else pcz_posOf x t + 1) = _
              rw [ite_eq_right hyx]
            have hmem' : x ∈ t.take n := by
              rcases List.mem_cons.1 hmem with he | hrest
              · exact absurd he.symm hyx
              · exact hrest
            have hlt := ih t x hmem'
            omega

/-- The build order is the rank order (the per-file copy of
`sequ_posOf_upCards`). -/
private theorem pcz_posOf_upCards (σ : Suit) (r : Rank) :
    pcz_posOf (Card.mk σ r) (Suit.upCards σ) = r.toIdx := by
  cases σ <;> cases r <;> rfl

/-- **THE FOUNDED-BRIDGE, DOWNWARD** — a founded card's rank index
sits strictly below its suit's rung (the per-file copy of
`sequ_mem_found_rank_lt`). -/
private theorem pcz_mem_found_rank_lt {st : State} (hwf : st.WF) {d : Card}
    (hmem : d ∈ st.found d.suit) :
    d.rank.toIdx < rungAt st d.suit := by
  have hpre := rung_found_prefix st hwf d.suit
  rw [hpre] at hmem
  have hpos : pcz_posOf d d.suit.upCards < rungAt st d.suit :=
    pcz_mem_take_pos _ _ _ hmem
  rcases d with ⟨s, r⟩
  have hnorm : pcz_posOf (Card.mk s r) (Suit.upCards s) < rungAt st s := hpos
  have hidx : pcz_posOf (Card.mk s r) (Suit.upCards s) = r.toIdx :=
    pcz_posOf_upCards s r
  show r.toIdx < rungAt st s
  omega

/-- Membership in a take is membership in the list (the per-file copy
of `sequ_mem_of_take`). -/
private theorem pcz_mem_of_take : ∀ {α : Type} (l : List α) (n : Nat) {x : α},
    x ∈ l.take n → x ∈ l := by
  intro α l n
  induction n generalizing l with
  | zero =>
      intro x h
      simp [List.take] at h
  | succ n ih =>
      intro x h
      cases l with
      | nil => simp [List.take] at h
      | cons a t =>
          rw [List.take_succ_cons] at h
          rcases List.mem_cons.mp h with he | hrest
          · subst he; exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem a (ih t hrest)

/-- An element at position `i` belongs to the first `n` entries of the
list when `i < n` (the per-file copy of `sequ_get_in_take`). -/
private theorem pcz_get_in_take : ∀ {α : Type} (l : List α) (n i : Nat)
    (hl : i < l.length) (_hn : i < n), l.get ⟨i, hl⟩ ∈ l.take n := by
  intro α l n i hl hn
  induction n generalizing l i hl with
  | zero => exact absurd hn (by omega)
  | succ n ih =>
      cases l with
      | nil => exact absurd hl (by simp)
      | cons a t =>
          cases i with
          | zero =>
              show a ∈ a :: t.take n
              exact List.mem_cons.2 (Or.inl rfl)
          | succ i' =>
              simp only [List.length_cons] at hl
              refine List.mem_cons_of_mem a (ih t i' (by omega) (by omega))

/-- A card sits at its own build index in its suit's foundation order
(the per-file copy of `sequ_upCards_get`). -/
private theorem pcz_upCards_get (z : Card)
    (h : z.rank.toIdx < z.suit.upCards.length) :
    z.suit.upCards.get ⟨z.rank.toIdx, h⟩ = z := by
  rcases z with ⟨zs, zr⟩
  cases zr <;> rfl

/-- **THE FOUNDED-BRIDGE, UPWARD** — a suit rung strictly above a
card's rank index has already founded it (the per-file copy of
`sequ_mem_found_of_rung`). -/
private theorem pcz_mem_found_of_rung {st : State} (hwf : st.WF) {c : Card}
    (hlt : c.rank.toIdx < rungAt st c.suit) : c ∈ st.found c.suit := by
  have hpre := rung_found_prefix st hwf c.suit
  have h13 : c.suit.upCards.length = 13 := Suit.upCards_length c.suit
  have hget : c.suit.upCards.get ⟨c.rank.toIdx, by
      rw [h13]; exact Rank.toIdx_lt c.rank⟩ = c :=
    pcz_upCards_get c (by rw [h13]; exact Rank.toIdx_lt c.rank)
  have hmem0 : c.suit.upCards.get ⟨c.rank.toIdx, by
      rw [h13]; exact Rank.toIdx_lt c.rank⟩ ∈
      c.suit.upCards.take (rungAt st c.suit) :=
    pcz_get_in_take c.suit.upCards (rungAt st c.suit) c.rank.toIdx
      (show c.rank.toIdx < c.suit.upCards.length by
        rw [h13]; exact Rank.toIdx_lt c.rank) hlt
  rw [hget] at hmem0
  have hmem : c ∈ c.suit.upCards.take (rungAt st c.suit) := hmem0
  rwa [← hpre] at hmem

/-- A foundation row holds only its own suit's cards (the per-file
copy of `sequ_found_suit`). -/
private theorem pcz_found_suit {st : State} (hwf : st.WF) {c : Card} {s : Suit}
    (hmem : c ∈ st.found s) : c.suit = s := by
  obtain ⟨n, hn⟩ := hwf.found_prefix s
  rw [hn] at hmem
  have hmem2 : c ∈ s.upCards := pcz_mem_of_take _ _ hmem
  obtain ⟨r, -, hmk⟩ := List.mem_map.mp hmem2
  subst hmk
  rfl

/-- The take never outgrows the list (the length bound; the per-file
mini-induction, avoiding core-name variance). -/
private theorem pcz_take_len_le : ∀ {α : Type} (l : List α) (n : Nat),
    (l.take n).length ≤ l.length := by
  intro α l n
  induction n generalizing l with
  | zero => cases l <;> simp [List.take]
  | succ n ih =>
      cases l with
      | nil => simp [List.take]
      | cons a t =>
          simp only [List.take, List.length_cons]
          have h2 := ih t
          omega

/-- The rung never passes the build order's length (WF's prefix is a
bounded take). -/
private theorem pcz_rung_le {st : State} (hwf : st.WF) (σ : Suit) :
    rungAt st σ ≤ 13 := by
  have hpre := rung_found_prefix st hwf σ
  have h13 : σ.upCards.length = 13 := Suit.upCards_length σ
  have h1 : (σ.upCards.take (rungAt st σ)).length ≤ σ.upCards.length :=
    pcz_take_len_le _ _
  rw [h13] at h1
  show (st.found σ).length ≤ 13
  rw [hpre]
  exact h1

/-- The rank of a zero-based index, tabulated by kernel computation
(the per-file copy of `Orig/Classify.lean`'s private `Rk`). -/
private def pczRk : Nat → Rank
  | 0 => .ace | 1 => .two | 2 => .three | 3 => .four | 4 => .five | 5 => .six
  | 6 => .seven | 7 => .eight | 8 => .nine | 9 => .ten | 10 => .jack | 11 => .queen
  | 12 => .king | _ => .ace

private theorem pczRk_toIdx : ∀ (k : Nat), k < 13 → (pczRk k).toIdx = k := by
  intro k hk
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | 9 => rfl
  | 10 => rfl
  | 11 => rfl
  | 12 => rfl
  | j + 13 => exact absurd hk (by omega)

/-- The boundary-card refutation (private): suit rungs cannot split
between WF class-mates with agreeing founded sets — the smaller
rung's boundary card would be founded at both states, its rank index
refuting the smaller rung's own downward bridge. -/
private theorem pcz_rung_lt {u v : State} (hwfu : u.WF) (hwfv : v.WF)
    (hagg : ∀ d : Card, foundResident u d ↔ foundResident v d) (σ : Suit)
    (hlt : rungAt u σ < rungAt v σ) : False := by
  have hu13 : rungAt u σ < 13 :=
    Nat.lt_of_lt_of_le hlt (pcz_rung_le hwfv σ)
  have hcidx : (Card.mk σ (pczRk (rungAt u σ))).rank.toIdx = rungAt u σ :=
    pczRk_toIdx _ hu13
  have hcf : Card.mk σ (pczRk (rungAt u σ)) ∈ v.found σ :=
    pcz_mem_found_of_rung hwfv (by
      show (Card.mk σ (pczRk (rungAt u σ))).rank.toIdx < rungAt v σ
      rw [hcidx]
      exact hlt)
  have hcfs : foundResident u (Card.mk σ (pczRk (rungAt u σ))) :=
    (hagg _).mpr ⟨σ, hcf⟩
  obtain ⟨s, hcs⟩ := hcfs
  have hfix := pcz_found_suit hwfu hcs
  rw [← hfix] at hcs
  have hclt : (Card.mk σ (pczRk (rungAt u σ))).rank.toIdx < rungAt u σ :=
    pcz_mem_found_rank_lt hwfu hcs
  omega

/-- **THE RUNG-VECTOR IFF** — agreeing foundation card SETS between
ANY two WF states ⟺ identical rung vectors (no class premise: the
boundary-card argument reads the foundations alone, so this leg is
strictly stronger than the class-mates setting).  With §5 — whose
cycle pin is where the class relation does the work — the three
readings of "same board census" at WF class-mates — tableau sets,
foundation sets, rung vector — collapse into one equivalence. -/
theorem wf_foundRung_iff {st w : State} (hwfst : st.WF) (hwfw : w.WF) :
    (∀ σ : Suit, rungAt st σ = rungAt w σ) ↔
      (∀ c : Card, foundResident st c ↔ foundResident w c) := by
  constructor
  · intro hr
    have hfounds : ∀ s : Suit, st.found s = w.found s :=
      fun s => rung_found_congr st w hwfst hwfw s (hr s)
    intro c
    constructor
    · intro hmem
      obtain ⟨s, hc⟩ := hmem
      exact ⟨s, by rw [← hfounds s]; exact hc⟩
    · intro hmem
      obtain ⟨s, hc⟩ := hmem
      exact ⟨s, by rw [hfounds s]; exact hc⟩
  · intro hagg σ
    rcases Nat.lt_trichotomy (rungAt st σ) (rungAt w σ) with h | h | h
    · exact (pcz_rung_lt hwfst hwfw hagg σ h).elim
    · exact h
    · exact (pcz_rung_lt hwfw hwfst (fun d => (hagg d).symm) σ h).elim

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

#print axioms mates_cycleZone_pin
#print axioms forkState_class_cycleRes
#print axioms pcz_pair_rung
#print axioms forkState_class_rungVec
#print axioms forkState_class_founds
#print axioms forkState_class_foundRes
#print axioms forkState_class_tabRes
#print axioms forkState_class_zoneSets
#print axioms class_zoneAgree_iff
#print axioms pcz_rung_lt
#print axioms wf_foundRung_iff
