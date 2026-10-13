import Orig.FoundKit
import Orig.SlabEquiv

/-!
# Orig.ZoneAgree — the census-stratum zone-agreement leaf

The owner-endorsed split (landed 2026-10-13): the FORK-FREE census rows
of `Orig/PairClassZones.lean` — the zone-residency vocabulary, the
unconditional cycle pin, the agreement iff, and the rung-vector iff —
re-homed to a stratum leaf beside SlabEquiv, so every chapter below
the fork grades reads zone agreements without dragging the capstone
cone.  The fork-grade family (`forkState_class_zoneSets` and friends,
conditional on the named `hthird`) stays in `Orig/PairClassZones.lean`
— this leaf is its census floor.

Statement of the three census readings at WF class-mates (the class
relation's only load-bearing census work is the cycle pin):
cycle side — pinned outright; tableau set ⟺ foundation set
(`class_zoneAgree_iff`); foundation set ⟺ rung vector
(`wf_foundRung_iff`, which needs NO class premise at all — the
boundary-card argument reads foundations alone).
-/

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
second conjunct feeds SlabEquiv's public `cycle_zone_pin`; the pin's
own iff already covers both directions, so one journey suffices. -/
theorem mates_cycleZone_pin {st w : State}
    (hcls : sameOrbitSetoid.r st w) (c : Card) :
    cycleResident w c ↔ cycleResident st c := by
  rcases hcls with ⟨ρ, _hρ, τ, hτ⟩
  exact cycle_zone_pin hτ c

/-! ## §2. The agreement iff (the set sense) -/

/-- The census floor for the founded direction (private): a card
excluded from `u`'s tableau and cycle side — at a `v` agreeing on the
tableau and cycle — must be founded at `v`; the five-zone census
leaves no other seat. -/
private theorem za_found_floor {u v : State} (hwfv : v.WF) (c : Card)
    (htab : ∀ d : Card, tabResident u d ↔ tabResident v d)
    (hpin : ∀ d : Card, cycleResident v d ↔ cycleResident u d)
    (hntab : ¬ tabResident u c) (hcyc : ¬ cycleResident u c) :
    foundResident v c := by
  have hntabv : ¬ tabResident v c := fun h => hntab ((htab c).mpr h)
  have hcycv : ¬ cycleResident v c := fun h => hcyc ((hpin c).mp h)
  rcases FoundKit.zone_residency v hwfv c with
    ⟨s, hfw⟩ | ⟨k, hkw⟩ | ⟨k, hfw⟩ | hsw | hww
  · exact ⟨s, hfw⟩
  · exact absurd ⟨k, Or.inr hkw⟩ hntabv
  · exact absurd ⟨k, Or.inl hfw⟩ hntabv
  · exact absurd (Or.inl hsw) hcycv
  · exact absurd (Or.inr hww) hcycv

/-- The census floor for the tableau direction (private): a card
excluded from `u`'s foundations and cycle side — at a `v` agreeing on
the founds and cycle — must sit on `v`'s tableau. -/
private theorem za_tab_floor {u v : State} (hwfv : v.WF) (c : Card)
    (hfound : ∀ d : Card, foundResident u d ↔ foundResident v d)
    (hpin : ∀ d : Card, cycleResident v d ↔ cycleResident u d)
    (hnf : ¬ foundResident u c) (hcyc : ¬ cycleResident u c) :
    tabResident v c := by
  have hnuv : ¬ foundResident v c := fun h => hnf ((hfound c).mpr h)
  have hcycv : ¬ cycleResident v c := fun h => hcyc ((hpin c).mp h)
  rcases FoundKit.zone_residency v hwfv c with
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
      refine za_found_floor hwfw c htab hpin ?_
        (fun hcc => hcc.elim hmem.2.1 hmem.2.2.1)
      intro htu
      obtain ⟨a, hf | hh⟩ := htu
      · exact (hmem.1 a).2 hf
      · exact (hmem.1 a).1 hh
    · intro hfound
      obtain ⟨s, hfw⟩ := hfound
      have hmem := mem_found_unique hwfw hfw
      refine za_found_floor hwfst c (fun d => (htab d).symm)
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
        refine za_tab_floor hwfw c hfound hpin ?_
          (fun hcc => hcc.elim hmem.2.2.1 hmem.2.2.2.1)
        intro hfr
        obtain ⟨s, hcs⟩ := hfr
        exact hmem.2.2.2.2 s hcs
      · have hmem := mem_hidden_only hwfst hh
        refine za_tab_floor hwfw c hfound hpin ?_
          (fun hcc => hcc.elim hmem.2.2.1 hmem.2.2.2.1)
        intro hfr
        obtain ⟨s, hcs⟩ := hfr
        exact hmem.2.2.2.2 s hcs
    · intro htab
      obtain ⟨a, hf | hh⟩ := htab
      · have hmem := mem_faceUp_only hwfw hf
        refine za_tab_floor hwfst c (fun d => (hfound d).symm)
          (fun d => (hpin d).symm) ?_
          (fun hcc => hcc.elim hmem.2.2.1 hmem.2.2.2.1)
        intro hfr
        obtain ⟨s, hcs⟩ := hfr
        exact hmem.2.2.2.2 s hcs
      · have hmem := mem_hidden_only hwfw hh
        refine za_tab_floor hwfst c (fun d => (hfound d).symm)
          (fun d => (hpin d).symm) ?_
          (fun hcc => hcc.elim hmem.2.2.1 hmem.2.2.2.1)
        intro hfr
        obtain ⟨s, hcs⟩ := hfr
        exact hmem.2.2.2.2 s hcs

/-! ## §3. The rung-vector leg (the numeric sense) -/

/-- The boundary-card refutation (private): suit rungs cannot split
between WF class-mates with agreeing founded sets — the smaller
rung's boundary card would be founded at both states, its rank index
refuting the smaller rung's own downward bridge. -/
private theorem za_rung_lt {u v : State} (hwfu : u.WF) (hwfv : v.WF)
    (hagg : ∀ d : Card, foundResident u d ↔ foundResident v d) (σ : Suit)
    (hlt : rungAt u σ < rungAt v σ) : False := by
  have hu13 : rungAt u σ < 13 :=
    Nat.lt_of_lt_of_le hlt (FoundKit.rung_le hwfv σ)
  have hcidx : (Card.mk σ (FoundKit.Rk (rungAt u σ))).rank.toIdx = rungAt u σ :=
    FoundKit.Rk_toIdx _ hu13
  have hcf : Card.mk σ (FoundKit.Rk (rungAt u σ)) ∈ v.found σ :=
    FoundKit.mem_found_of_rung hwfv (by
      show (Card.mk σ (FoundKit.Rk (rungAt u σ))).rank.toIdx < rungAt v σ
      rw [hcidx]
      exact hlt)
  have hcfs : foundResident u (Card.mk σ (FoundKit.Rk (rungAt u σ))) :=
    (hagg _).mpr ⟨σ, hcf⟩
  obtain ⟨s, hcs⟩ := hcfs
  have hfix := FoundKit.found_suit hwfu hcs
  rw [← hfix] at hcs
  have hclt : (Card.mk σ (FoundKit.Rk (rungAt u σ))).rank.toIdx < rungAt u σ :=
    FoundKit.mem_found_rank_lt hwfu hcs
  omega

/-- **THE RUNG-VECTOR IFF** — agreeing foundation card SETS between
ANY two WF states ⟺ identical rung vectors (no class premise: the
boundary-card argument reads the foundations alone, so this leg is
strictly stronger than the class-mates setting).  With §1 — whose
cycle pin is where the class relation does the work — the three
readings of "same board census" at WF class-mates — tableau sets,
foundation sets, rung vector — collapse into one equivalence. -/
theorem wf_foundRung_iff {st w : State} (hwfst : st.WF) (hwfw : w.WF) :
    (∀ σ : Suit, rungAt st σ = rungAt w σ) ↔
      (∀ c : Card, foundResident st c ↔ foundResident w c) := by
  constructor
  · intro hr
    have hfounds : ∀ s : Suit, st.found s = w.found s :=
      fun s => FoundKit.found_congr st w hwfst hwfw s (hr s)
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
    · exact (za_rung_lt hwfst hwfw hagg σ h).elim
    · exact h
    · exact (za_rung_lt hwfw hwfst (fun d => (hagg d).symm) σ h).elim

/-! ## The audit battery -/

#print axioms mates_cycleZone_pin
#print axioms class_zoneAgree_iff
#print axioms wf_foundRung_iff
