import Orig.ForklessCeiling

/-!
# Orig.ForklessCeilingProbe — THE CEILING FALSIFIER BOARDS

The falsifier-first probe leaf of `Orig.ForklessCeiling.lean`'s
graded conjectures (the descent twin's lesson, banked: probes
decide before proofs; the verdicts land here, kernel-certified).

Boards, per the mission's exact order:

* **§1 BOARD (i) `fcS` — THE ASCENT-TWIN OF THE OWNER'S CONTENTION
  BOARD, verdict FIRST, before anything else.**  Twin red suits at
  equal rungs; the tableau holds ONE black burying host `5♠`; the
  two lone contenders `4♥`/`4♦` sit BARE over empty hidden decks —
  each seats onto the host by a one-leg run.  **THE DECISIVE VERDICT
  (decided):** the class is certified FORKLESS (`classCensusB fcS =
  false`: every 26-board candidate's cover window or twin is
  entombed in `p0`'s hidden deck) — and yet GRADE-A SURVIVES the
  board: the endpoints' rung vectors AGREE on all four suits, the
  twin freeze holding (both contenders `MobileTwin` at every leg —
  the full-time no-eat guard declines both raises forever).  The
  second boundary datum: the two distinct maximal endpoints are
  OUT OF REACH of bare cargo — Grade-C's expected-falsifier shape,
  and Grade-B's load-bearing class-mate premise exhibited.
* **§2 BOARD `fcH` — THE FRAGILE lb-STYLE DERIVATIVE WITH THE PAIR
  CELL ENTOMBED, doubling as the (iii) CONTENTION HUNT.**  Hearts
  founded to rung 3, everything else entombed; the hot member `4♥`
  SEATED on its parent `5♠` (a working, guard-free raise — the pair
  cell `4♦` is entombed), plus one burn lever `3♠` fitting ON the
  hot member.  THE TWO MAXIMAL RUNS: bury (burn-armed cover; the
  license dies, the heart rung never climbs) vs. raise (the
  mirror-backed in-class climb to rung 4).  **THE SPLIT IS REAL**
  (heart rungs 3 ≠ 4) but the bury-run's endpoint is FROZEN and
  certified OUT OF THE CLASS; the raise-run's endpoint IS a
  class-mate.  The hunt verdict: the one-seat/two-consumers split
  exists only OUTSIDE the class — irreversibility bars it — and the
  two endpoints are NOT `BareCargoEquiv`, certified through the
  main leaf's own `cargo_fix_rungs`.
* **THE (ii) READING** — both boards are single-family-fragile
  entombed economies (the `Orig/ForkFloorProbe.lean` pattern:
  whole color families sunk in one hidden deck, classes that
  cannot fork by construction, certified by the decidable census);
  the maximal-endpoint enumerations are the two-run exhibits, the
  rung vectors agree WITHIN the class, and the cargo-conversion
  check runs through the fix machinery.

House compliance: additive probe leaf (`import Orig.ForklessCeiling`
only — everything else transitive); decide/kernel grade for every
verdict; ZERO SORRY; zero `Classical.choice` (the matrices are
decide instances on literal boards); per-file private kit;
`#print axioms` battery for every fresh head; no other file touched.
Every maximal-ascent verdict below is checked against `AscentStuck`
(ForkAscent's exhaustion read) — never a halt trigger. -/

set_option linter.unusedVariables false

/-! ## §0. The probe kit (private, per-file copies) -/

private def fcc (s : Suit) (r : Rank) : Card := ⟨s, r⟩

private def fcT (st : State) (m : Move) : State :=
  match st.step m with
  | none => st
  | some s' => s'

private def H4 : Card := fcc .heart .four
private def D4 : Card := fcc .diamond .four
private def S5 : Card := fcc .spade .five
private def S3 : Card := fcc .spade .three

private def fcS_hmap : Suit → Nat
  | .heart => 3 | .diamond => 3 | .spade => 0 | .club => 0

/-- The forty-three entombed cards of the (i) board — all blacks
minus the lone host, all red tails above the rungs, including BOTH
black fours (the cover window that decides the census). -/
private def fcS_deck : List Card :=
  [fcc .spade .ace, fcc .spade .two, fcc .spade .three, fcc .spade .four,
   fcc .spade .six, fcc .spade .seven, fcc .spade .eight, fcc .spade .nine,
   fcc .spade .ten, fcc .spade .jack, fcc .spade .queen, fcc .spade .king,
   fcc .heart .five, fcc .heart .six, fcc .heart .seven, fcc .heart .eight,
   fcc .heart .nine, fcc .heart .ten, fcc .heart .jack, fcc .heart .queen,
   fcc .heart .king,
   fcc .diamond .five, fcc .diamond .six, fcc .diamond .seven,
   fcc .diamond .eight, fcc .diamond .nine, fcc .diamond .ten,
   fcc .diamond .jack, fcc .diamond .queen, fcc .diamond .king,
   fcc .club .ace, fcc .club .two, fcc .club .three, fcc .club .four,
   fcc .club .five, fcc .club .six, fcc .club .seven, fcc .club .eight,
   fcc .club .nine, fcc .club .ten, fcc .club .jack, fcc .club .queen,
   fcc .club .king]

/-- **THE ASCENT-TWIN CONTENTION BOARD `fcS`** — ♥ 3 = ♦ 3, the
red aces-through-threes founded, everything else entombed in
`p0`'s hidden deck; the twin contenders `4♥`/`4♦` bare at
`p1`/`p2`; the lone black burying host `5♠` bare at `p3`; both
zones empty. -/
private def fcS : State where
  found := fun s => s.upCards.take (fcS_hmap s)
  piles := fun a => match a with
    | .p0 => ⟨fcS_deck, []⟩
    | .p1 => ⟨[], [H4]⟩
    | .p2 => ⟨[], [D4]⟩
    | .p3 => ⟨[], [S5]⟩
    | .p4 => ⟨[], []⟩
    | .p5 => ⟨[], []⟩
    | .p6 => ⟨[], []⟩
  stock := []
  waste := []
  drawStep := 1

private theorem fcS_wf_found : ∀ s : Suit, ∃ n, fcS.found s = s.upCards.take n := by
  intro s
  cases s <;> exact ⟨fcS_hmap _, rfl⟩

private theorem fcS_wf_runs : ∀ a : Anchor, runOK (fcS.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem fcS_wf_count : ∀ c ∈ Card.universe, fcS.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

theorem fcS_wf : fcS.WF :=
  ⟨fcS_wf_found, fcS_wf_runs, fcS_wf_count, by decide⟩

/-- **THE (i) DECISIVE VERDICT: THE CLASS IS CERTIFIED FORKLESS**
(decided) — the 26-board census is silent for every candidate: each
founded pair's cover window is entombed (all black lows live in
`p0`'s hidden deck), each face-up candidate's twin is entombed, the
lone host's twin is entombed.  The decidable no-go certificate
applies; the verdict everything else reads against. -/
theorem fcS_censusB : classCensusB fcS = false := by decide

theorem fcS_forkless : Forkless fcS :=
  classCensus_false_forkless fcS_wf fcS_censusB

/-- **THE CONTENTION SHAPE IS REAL** — the twin reds are a LOCATED
CANDIDATE PAIR at the certified-forkless head (both members mobile,
both face-up and located): the exclusion of this class from the
fork-carrying scope is a genuine arrangeability fact, not an
artifact of absent content. -/
theorem fcS_pairCandidate : PairCandidate fcS H4 :=
  ⟨faceUp_mobile (a := Anchor.p1) fcS_wf (by decide),
    faceUp_mobile (a := Anchor.p2) fcS_wf (by decide),
    ⟨Anchor.p1, by decide⟩, ⟨Anchor.p2, by decide⟩⟩

/-- **§1 THE TWO MAXIMAL ASCENT RUNS: bury the heart twin vs. bury
the diamond twin** — one-leg slide-arm `AscentRun`s (no guard rides
the slide arm), landing at the exhaustion endpoints `fcS_A`/`fcS_B`
(both `AscentStuck`, below).  THE BURN-ARMED SEATING: each contender
departs a bare over-empty-hidden pile (both sources burn — the
class-exit shape, the descent twin's lesson wearing the ascent's
clothes). -/
private def fcS_A : State := fcT fcS (Move.tabToTab H4 (Sum.inr S5))

private def fcS_B : State := fcT fcS (Move.tabToTab D4 (Sum.inr S5))

theorem fcS_stepA : State.step fcS (Move.tabToTab H4 (Sum.inr S5)) = some fcS_A := rfl

theorem fcS_stepB : State.step fcS (Move.tabToTab D4 (Sum.inr S5)) = some fcS_B := rfl

theorem fcS_runA : AscentRun fcS [Move.tabToTab H4 (Sum.inr S5)] fcS_A :=
  AscentRun.cons (Or.inr ⟨H4, Sum.inr S5, rfl⟩) fcS_stepA (AscentRun.nil fcS_A)

theorem fcS_runB : AscentRun fcS [Move.tabToTab D4 (Sum.inr S5)] fcS_B :=
  AscentRun.cons (Or.inr ⟨D4, Sum.inr S5, rfl⟩) fcS_stepB (AscentRun.nil fcS_B)

/-- **GRADE-A AT THE BOARD: THE TWIN-FREEZE WITNESSES** — at
endpoint A both contenders are `MobileTwin` (both face-up, both at
their frontier rungs), so the full-time no-eat guard declines
`4♥`'s raise forever; symmetrically at B for `4♦`.  Witnessed, not
assumed — these are the rows the stuckness reads. -/
theorem fcS_A_mobileH4 : MobileTwin fcS_A H4 :=
  ⟨⟨Anchor.p3, by decide⟩, by decide, ⟨Anchor.p2, by decide⟩, by decide⟩

theorem fcS_A_mobileD4 : MobileTwin fcS_A D4 :=
  ⟨⟨Anchor.p2, by decide⟩, by decide, ⟨Anchor.p3, by decide⟩, by decide⟩

theorem fcS_B_mobileH4 : MobileTwin fcS_B H4 :=
  ⟨⟨Anchor.p1, by decide⟩, by decide, ⟨Anchor.p3, by decide⟩, by decide⟩

theorem fcS_B_mobileD4 : MobileTwin fcS_B D4 :=
  ⟨⟨Anchor.p3, by decide⟩, by decide, ⟨Anchor.p1, by decide⟩, by decide⟩

/-- The endpoint face-up inventories (the stuckness kit's input). -/
theorem fcS_A_faceUp : ∀ c : Card, (∃ a, c ∈ (fcS_A.piles a).faceUp) →
    c = H4 ∨ c = D4 ∨ c = S5 := by
  intro c hcu
  obtain ⟨a, hc⟩ := hcu
  cases a with
  | p0 =>
      rw [show (fcS_A.piles Anchor.p0).faceUp = ([] : List Card) from rfl] at hc
      cases hc
  | p1 =>
      rw [show (fcS_A.piles Anchor.p1).faceUp = ([] : List Card) from rfl] at hc
      cases hc
  | p2 =>
      rw [show (fcS_A.piles Anchor.p2).faceUp = [D4] from rfl] at hc
      rcases List.mem_cons.mp hc with h | h
      · exact Or.inr (Or.inl h)
      · cases h
  | p3 =>
      rw [show (fcS_A.piles Anchor.p3).faceUp = [S5, H4] from rfl] at hc
      rcases List.mem_cons.mp hc with h | h
      · exact Or.inr (Or.inr h)
      · rcases List.mem_cons.mp h with h | h
        · exact Or.inl h
        · cases h
  | p4 =>
      rw [show (fcS_A.piles Anchor.p4).faceUp = ([] : List Card) from rfl] at hc
      cases hc
  | p5 =>
      rw [show (fcS_A.piles Anchor.p5).faceUp = ([] : List Card) from rfl] at hc
      cases hc
  | p6 =>
      rw [show (fcS_A.piles Anchor.p6).faceUp = ([] : List Card) from rfl] at hc
      cases hc

theorem fcS_B_faceUp : ∀ c : Card, (∃ a, c ∈ (fcS_B.piles a).faceUp) →
    c = H4 ∨ c = D4 ∨ c = S5 := by
  intro c hcu
  obtain ⟨a, hc⟩ := hcu
  cases a with
  | p0 =>
      rw [show (fcS_B.piles Anchor.p0).faceUp = ([] : List Card) from rfl] at hc
      cases hc
  | p1 =>
      rw [show (fcS_B.piles Anchor.p1).faceUp = [H4] from rfl] at hc
      rcases List.mem_cons.mp hc with h | h
      · exact Or.inl h
      · cases h
  | p2 =>
      rw [show (fcS_B.piles Anchor.p2).faceUp = ([] : List Card) from rfl] at hc
      cases hc
  | p3 =>
      rw [show (fcS_B.piles Anchor.p3).faceUp = [S5, D4] from rfl] at hc
      rcases List.mem_cons.mp hc with h | h
      · exact Or.inr (Or.inr h)
      · rcases List.mem_cons.mp h with h | h
        · exact Or.inr (Or.inl h)
        · cases h
  | p4 =>
      rw [show (fcS_B.piles Anchor.p4).faceUp = ([] : List Card) from rfl] at hc
      cases hc
  | p5 =>
      rw [show (fcS_B.piles Anchor.p5).faceUp = ([] : List Card) from rfl] at hc
      cases hc
  | p6 =>
      rw [show (fcS_B.piles Anchor.p6).faceUp = ([] : List Card) from rfl] at hc
      cases hc

/-- **§1 THE CARGO-FREEZE MATRICES** — no `tabToTab` letter of any
shape fires at either endpoint: the exhausted boards are out of
reach of bare cargo (kernel matrices). -/
theorem fcS_A_slides_none : ∀ (c : Card) (b : Base),
    State.step fcS_A (Move.tabToTab c b) = none := by
  intro c b
  cases b with
  | inl n =>
      rcases c with ⟨s, r⟩ <;> cases s <;> cases r <;> cases n <;> decide
  | inr z =>
      rcases c with ⟨s, r⟩ <;> rcases z with ⟨zs, zr⟩ <;>
        cases s <;> cases r <;> cases zs <;> cases zr <;> decide

theorem fcS_B_slides_none : ∀ (c : Card) (b : Base),
    State.step fcS_B (Move.tabToTab c b) = none := by
  intro c b
  cases b with
  | inl n =>
      rcases c with ⟨s, r⟩ <;> cases s <;> cases r <;> cases n <;> decide
  | inr z =>
      rcases c with ⟨s, r⟩ <;> rcases z with ⟨zs, zr⟩ <;>
        cases s <;> cases r <;> cases zs <;> cases zr <;> decide

/-- **THE (i) VERDICT'S CARDINAL ROW: GRADE-A SURVIVES THE BOARD** —
both maximal ascent endpoints AGREE on EVERY rung: the twin freeze
(both contenders `MobileTwin` at every leg) pins the twin raises
forever, and the lone host is cold; the slides write no foundation.
Certified through the main leaf's own zone-fix row (the plays are
cargo plays, and cargo never writes a found). -/
theorem fcS_AB_rungsAgree : ∀ σ : Suit, rungAt fcS_A σ = rungAt fcS_B σ := by
  have hpA : CargoPlay fcS [Move.tabToTab H4 (Sum.inr S5)] fcS_A :=
    CargoPlay.cons ⟨H4, Sum.inr S5, rfl⟩ fcS_stepA (CargoPlay.nil fcS_A)
  have hpB : CargoPlay fcS [Move.tabToTab D4 (Sum.inr S5)] fcS_B :=
    CargoPlay.cons ⟨D4, Sum.inr S5, rfl⟩ fcS_stepB (CargoPlay.nil fcS_B)
  have hA := (CargoPlay_fix_zone hpA).1
  have hB := (CargoPlay_fix_zone hpB).1
  intro σ
  show (fcS_A.found σ).length = (fcS_B.found σ).length
  rw [hA, hB]

theorem fcS_AB_ne : fcS_A ≠ fcS_B := by
  intro h
  have h2 : (fcS_A.piles Anchor.p2).faceUp = (fcS_B.piles Anchor.p2).faceUp :=
    congrArg (fun s => (s.piles Anchor.p2).faceUp) h
  exact absurd h2 (by decide)

/-- **GRADE-C'S EXPECTED-FALSIFIER SHAPE, CARGO-SIDE** — the two
distinct maximal endpoints of the certified-forkless start are NOT
joined by bare cargo: at either endpoint NO cargo letter fires at
all (the twins' raises are legal STEPS there — the twin freeze is
the ascent guard's doing, and the raw step raises them — but bare
cargo is the tabToTab alphabet, and it is silent), so the only
cargo play from either endpoint is empty, and the endpoints differ.
(Whether each endpoint is a class-MATE of the start is exactly the
burn-exit boundary the fcH board certifies; the (i) board's seating
legs are burn-armed — each contender departed a bare
over-empty-hidden pile — so the class-mate premise of the frozen
grades is load-bearing here, documented, not shouldered.) -/
theorem fcS_A_nocargo : ∀ (play : List Move) (w : State),
    CargoPlay fcS_A play w → w = fcS_A := by
  intro play w h
  cases h with
  | nil s => rfl
  | @cons s s₁ W m ρ hlet hstep hrest =>
      obtain ⟨c, b, hm⟩ := hlet
      rw [hm] at hstep
      have hnone := fcS_A_slides_none c b
      rw [hnone] at hstep
      exact absurd hstep (by simp)

theorem fcS_B_nocargo : ∀ (play : List Move) (w : State),
    CargoPlay fcS_B play w → w = fcS_B := by
  intro play w h
  cases h with
  | nil s => rfl
  | @cons s s₁ W m ρ hlet hstep hrest =>
      obtain ⟨c, b, hm⟩ := hlet
      rw [hm] at hstep
      have hnone := fcS_B_slides_none c b
      rw [hnone] at hstep
      exact absurd hstep (by simp)

theorem fcS_AB_notBareCargo : ¬ BareCargoEquiv fcS_A fcS_B := by
  rintro ⟨τ, hτ, ρ, hρ⟩
  have hw := fcS_A_nocargo τ fcS_B hτ
  exact fcS_AB_ne hw.symm

/-- **THE BURN-SEAT MIRROR EXHIBITS (the (i) board's class-mate
boundary datum)** — at each maximal endpoint the contender's departed
pile stands VACANT (bare over an empty hidden deck from the start;
the seating leg took its only card), and the obvious mirror return
leg — the four coming home onto that empty seat — DOES NOT FIRE:
empty seats receive KINGS only (`canPlace`'s king bar), and no four
is a king.  Burn-armed seating COMMITS, exactly as the main leaf's
Grade-C docstring reads ("each run's seating slide is burn-armed and
COMMITS — the boundary datum the probe leaf certifies"); each row
below is the named instance of the landed cargo-freeze matrix
(kernel-certified there). -/
theorem fcS_A_return_leg_blocked :
    State.step fcS_A (Move.tabToTab H4 (Sum.inl Anchor.p1)) = none :=
  fcS_A_slides_none H4 (Sum.inl Anchor.p1)

/-- The diamond twin's mirror, symmetric: `4♦` cannot take its burned
seat `p2` back. -/
theorem fcS_B_return_leg_blocked :
    State.step fcS_B (Move.tabToTab D4 (Sum.inl Anchor.p2)) = none :=
  fcS_B_slides_none D4 (Sum.inl Anchor.p2)

/-- **§1 THE EXHAUSTION VERDICTS** — both one-leg runs are maximal:
each endpoint is `AscentStuck` (the raise arm dies on the twin
freeze — the guard witnesses above; the lone host is cold; the
slide arm dies on the cargo-freeze matrices), and the START is not
stuck (the seating slides fire there). -/
theorem fcS_A_stuck : AscentStuck fcS_A := by
  intro m hm
  rcases hm with ⟨c, hmEq, hhot, hface, hguard⟩ | ⟨c, b, hmEq⟩
  · rw [hmEq]
    obtain ⟨a, hcma⟩ := hface
    rcases fcS_A_faceUp c ⟨a, hcma⟩ with h | h | h
    · subst h
      exact absurd rfl (hguard H4 fcS_A_mobileH4).1
    · subst h
      exact absurd rfl (hguard D4 fcS_A_mobileD4).1
    · subst h
      exact absurd hhot (by decide)
  · rw [hmEq]
    exact fcS_A_slides_none c b

theorem fcS_B_stuck : AscentStuck fcS_B := by
  intro m hm
  rcases hm with ⟨c, hmEq, hhot, hface, hguard⟩ | ⟨c, b, hmEq⟩
  · rw [hmEq]
    obtain ⟨a, hcma⟩ := hface
    rcases fcS_B_faceUp c ⟨a, hcma⟩ with h | h | h
    · subst h
      exact absurd rfl (hguard H4 fcS_B_mobileH4).1
    · subst h
      exact absurd rfl (hguard D4 fcS_B_mobileD4).1
    · subst h
      exact absurd hhot (by decide)
  · rw [hmEq]
    exact fcS_B_slides_none c b

theorem fcS_A_maximal : MaxAscentEndpoint fcS fcS_A :=
  ⟨[Move.tabToTab H4 (Sum.inr S5)], fcS_runA, fcS_A_stuck⟩

theorem fcS_B_maximal : MaxAscentEndpoint fcS fcS_B :=
  ⟨[Move.tabToTab D4 (Sum.inr S5)], fcS_runB, fcS_B_stuck⟩

theorem fcS_notStuck : ¬ AscentStuck fcS := by
  intro h
  have hnone := h _ (Or.inr ⟨H4, Sum.inr S5, rfl⟩)
  rw [fcS_stepA] at hnone
  exact absurd hnone (by simp)

/-! ## §2. The board `fcH`: the fragile lb-style derivative with
the pair cell entombed, doubling as the (iii) contention hunt -/

private def fcH_hmap : Suit → Nat
  | .heart => 3 | .diamond => 0 | .spade => 0 | .club => 0

/-- The forty-six entombed cards: everything except the three
founded hearts and the three face-up cards (`5♠`, `4♥`, the burn
lever `3♠`) — the pair cell `4♦` lives here (the guard is off; the
lb-heritage entombed economy). -/
private def fcH_deck : List Card :=
  [fcc .spade .ace, fcc .spade .two, fcc .spade .four, fcc .spade .six,
   fcc .spade .seven, fcc .spade .eight, fcc .spade .nine,
   fcc .spade .ten, fcc .spade .jack, fcc .spade .queen, fcc .spade .king,
   fcc .heart .five, fcc .heart .six, fcc .heart .seven, fcc .heart .eight,
   fcc .heart .nine, fcc .heart .ten, fcc .heart .jack, fcc .heart .queen,
   fcc .heart .king,
   fcc .diamond .ace, fcc .diamond .two, fcc .diamond .three,
   fcc .diamond .four, fcc .diamond .five, fcc .diamond .six,
   fcc .diamond .seven, fcc .diamond .eight, fcc .diamond .nine,
   fcc .diamond .ten, fcc .diamond .jack, fcc .diamond .queen,
   fcc .diamond .king,
   fcc .club .ace, fcc .club .two, fcc .club .three, fcc .club .four,
   fcc .club .five, fcc .club .six, fcc .club .seven, fcc .club .eight,
   fcc .club .nine, fcc .club .ten, fcc .club .jack, fcc .club .queen,
   fcc .club .king]

private def fcH : State where
  found := fun s => s.upCards.take (fcH_hmap s)
  piles := fun a => match a with
    | .p0 => ⟨fcH_deck, []⟩
    | .p1 => ⟨[], [S5, H4]⟩
    | .p2 => ⟨[], [S3]⟩
    | .p3 => ⟨[], []⟩
    | .p4 => ⟨[], []⟩
    | .p5 => ⟨[], []⟩
    | .p6 => ⟨[], []⟩
  stock := []
  waste := []
  drawStep := 1

private theorem fcH_wf_found : ∀ s : Suit, ∃ n, fcH.found s = s.upCards.take n := by
  intro s
  cases s <;> exact ⟨fcH_hmap _, rfl⟩

private theorem fcH_wf_runs : ∀ a : Anchor, runOK (fcH.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem fcH_wf_count : ∀ c ∈ Card.universe, fcH.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

theorem fcH_wf : fcH.WF :=
  ⟨fcH_wf_found, fcH_wf_runs, fcH_wf_count, by decide⟩

/-- **THE (ii)/(iii) CENSUS VERDICT: CERTIFIED FORKLESS** (decided)
— every candidate fails: the founded low pairs' covers are entombed,
the seated member's twin is entombed, the lone host's twin is
entombed.  The lb-heritage entombed economy, certified. -/
theorem fcH_censusB : classCensusB fcH = false := by decide

theorem fcH_forkless : Forkless fcH :=
  classCensus_false_forkless fcH_wf fcH_censusB

private def C5 : Card := fcc .club .five

/-- The board's face-up inventory, anchor-parameterized. -/
theorem fcH_faceUp_which : ∀ (c : Card) (a : Anchor),
    c ∈ (fcH.piles a).faceUp → c = S5 ∨ c = H4 ∨ c = S3 := by
  intro c a hc
  cases a with
  | p0 =>
      rw [show (fcH.piles Anchor.p0).faceUp = ([] : List Card) from rfl] at hc
      cases hc
  | p1 =>
      rw [show (fcH.piles Anchor.p1).faceUp = [S5, H4] from rfl] at hc
      rcases List.mem_cons.mp hc with h | h
      · exact Or.inl h
      · rcases List.mem_cons.mp h with h | h
        · exact Or.inr (Or.inl h)
        · cases h
  | p2 =>
      rw [show (fcH.piles Anchor.p2).faceUp = [S3] from rfl] at hc
      rcases List.mem_cons.mp hc with h | h
      · exact Or.inr (Or.inr h)
      · cases h
  | p3 =>
      rw [show (fcH.piles Anchor.p3).faceUp = ([] : List Card) from rfl] at hc
      cases hc
  | p4 =>
      rw [show (fcH.piles Anchor.p4).faceUp = ([] : List Card) from rfl] at hc
      cases hc
  | p5 =>
      rw [show (fcH.piles Anchor.p5).faceUp = ([] : List Card) from rfl] at hc
      cases hc
  | p6 =>
      rw [show (fcH.piles Anchor.p6).faceUp = ([] : List Card) from rfl] at hc
      cases hc

/-- **THE PAIR CELL IS ENTOMBED** — no `MobileTwin` pair lives at
the board: every face-up card's twin is entombed in `p0`'s hidden
deck (the (iii) hunt's release: the hot member's raise is
GUARD-FREE — that is exactly why the contention hunt can even be
staged here). -/
theorem fcH_noMobileTwin : ∀ (y : Card), ¬ MobileTwin fcH y := by
  intro y hy
  obtain ⟨⟨a, hca⟩, -, ⟨b, hcb⟩, -⟩ := hy
  have hy := fcH_faceUp_which y a hca
  have hyt := fcH_faceUp_which y.twin b hcb
  rcases hy with h | h | h <;> rcases hyt with ht | ht | ht
  all_goals
    (subst h
     exact absurd ht (by decide))

/-- **§2 THE TWO MAXIMAL RUNS: BURY VS. RAISE** — the burn-armed
cover of the hot member (its license dies with the bury; the heart
rung never climbs) against the guard-free in-class raise (the
mirror-backed climb to rung 4). -/
private def fcH_H1 : State := fcT fcH (Move.tabToTab S3 (Sum.inr H4))

private def fcH_H2 : State := fcT fcH (Move.tabToFound H4)

theorem fcH_stepBurn : State.step fcH (Move.tabToTab S3 (Sum.inr H4)) = some fcH_H1 := rfl

theorem fcH_stepRaise : State.step fcH (Move.tabToFound H4) = some fcH_H2 := rfl

theorem fcH_runBurn : AscentRun fcH [Move.tabToTab S3 (Sum.inr H4)] fcH_H1 :=
  AscentRun.cons (Or.inr ⟨S3, Sum.inr H4, rfl⟩) fcH_stepBurn (AscentRun.nil fcH_H1)

theorem fcH_runRaise : AscentRun fcH [Move.tabToFound H4] fcH_H2 :=
  AscentRun.cons (Or.inl ⟨H4, rfl, by decide, ⟨Anchor.p1, by decide⟩,
    fun y hy => absurd hy (fcH_noMobileTwin y)⟩)
    fcH_stepRaise (AscentRun.nil fcH_H2)

theorem fcH_H1_slides_none : ∀ (c : Card) (b : Base),
    State.step fcH_H1 (Move.tabToTab c b) = none := by
  intro c b
  cases b with
  | inl n =>
      rcases c with ⟨s, r⟩ <;> cases s <;> cases r <;> cases n <;> decide
  | inr z =>
      rcases c with ⟨s, r⟩ <;> rcases z with ⟨zs, zr⟩ <;>
        cases s <;> cases r <;> cases zs <;> cases zr <;> decide

theorem fcH_H2_slides_none : ∀ (c : Card) (b : Base),
    State.step fcH_H2 (Move.tabToTab c b) = none := by
  intro c b
  cases b with
  | inl n =>
      rcases c with ⟨s, r⟩ <;> cases s <;> cases r <;> cases n <;> decide
  | inr z =>
      rcases c with ⟨s, r⟩ <;> rcases z with ⟨zs, zr⟩ <;>
        cases s <;> cases r <;> cases zs <;> cases zr <;> decide

theorem fcH_H1_stuck : AscentStuck fcH_H1 := by
  intro m hm
  rcases hm with ⟨c, hmEq, hhot, hface, hguard⟩ | ⟨c, b, hmEq⟩
  · rw [hmEq]
    obtain ⟨a, hcma⟩ := hface
    have hc : c = S5 ∨ c = H4 ∨ c = S3 := by
      cases a with
      | p0 =>
          rw [show (fcH_H1.piles Anchor.p0).faceUp = ([] : List Card) from rfl] at hcma
          cases hcma
      | p1 =>
          rw [show (fcH_H1.piles Anchor.p1).faceUp = [S5, H4, S3] from rfl] at hcma
          rcases List.mem_cons.mp hcma with h | h
          · exact Or.inl h
          · rcases List.mem_cons.mp h with h | h
            · exact Or.inr (Or.inl h)
            · rcases List.mem_cons.mp h with h | h
              · exact Or.inr (Or.inr h)
              · cases h
      | p2 =>
          rw [show (fcH_H1.piles Anchor.p2).faceUp = ([] : List Card) from rfl] at hcma
          cases hcma
      | p3 =>
          rw [show (fcH_H1.piles Anchor.p3).faceUp = ([] : List Card) from rfl] at hcma
          cases hcma
      | p4 =>
          rw [show (fcH_H1.piles Anchor.p4).faceUp = ([] : List Card) from rfl] at hcma
          cases hcma
      | p5 =>
          rw [show (fcH_H1.piles Anchor.p5).faceUp = ([] : List Card) from rfl] at hcma
          cases hcma
      | p6 =>
          rw [show (fcH_H1.piles Anchor.p6).faceUp = ([] : List Card) from rfl] at hcma
          cases hcma
    rcases hc with h | h | h
    · subst h
      decide
    · subst h
      decide
    · subst h
      decide
  · rw [hmEq]
    exact fcH_H1_slides_none c b

theorem fcH_H2_stuck : AscentStuck fcH_H2 := by
  intro m hm
  rcases hm with ⟨c, hmEq, hhot, hface, hguard⟩ | ⟨c, b, hmEq⟩
  · rw [hmEq]
    obtain ⟨a, hcma⟩ := hface
    have hc : c = S5 ∨ c = S3 := by
      cases a with
      | p0 =>
          rw [show (fcH_H2.piles Anchor.p0).faceUp = ([] : List Card) from rfl] at hcma
          cases hcma
      | p1 =>
          rw [show (fcH_H2.piles Anchor.p1).faceUp = [S5] from rfl] at hcma
          rcases List.mem_cons.mp hcma with h | h
          · exact Or.inl h
          · cases h
      | p2 =>
          rw [show (fcH_H2.piles Anchor.p2).faceUp = [S3] from rfl] at hcma
          rcases List.mem_cons.mp hcma with h | h
          · exact Or.inr h
          · cases h
      | p3 =>
          rw [show (fcH_H2.piles Anchor.p3).faceUp = ([] : List Card) from rfl] at hcma
          cases hcma
      | p4 =>
          rw [show (fcH_H2.piles Anchor.p4).faceUp = ([] : List Card) from rfl] at hcma
          cases hcma
      | p5 =>
          rw [show (fcH_H2.piles Anchor.p5).faceUp = ([] : List Card) from rfl] at hcma
          cases hcma
      | p6 =>
          rw [show (fcH_H2.piles Anchor.p6).faceUp = ([] : List Card) from rfl] at hcma
          cases hcma
    rcases hc with h | h
    · subst h
      decide
    · subst h
      decide
  · rw [hmEq]
    exact fcH_H2_slides_none c b

theorem fcH_H1_maximal : MaxAscentEndpoint fcH fcH_H1 :=
  ⟨[Move.tabToTab S3 (Sum.inr H4)], fcH_runBurn, fcH_H1_stuck⟩

theorem fcH_H2_maximal : MaxAscentEndpoint fcH fcH_H2 :=
  ⟨[Move.tabToFound H4], fcH_runRaise, fcH_H2_stuck⟩

/-- **THE (iii) SPLIT VERDICT: THE BURN-RUN'S ENDPOINT EXITS THE
CLASS** — `fcH_H1` is FROZEN (no move at all fires there: the
resource died with the license, kernel-decided family by family),
so no legal play leaves it, hence no witness journey joins it back
to the start: the one-seat/two-consumers split exists only OUTSIDE
the class.  IRREVERSIBILITY bars the hunt. -/
theorem fcH_H1_frozen : ∀ (m : Move), State.step fcH_H1 m = none := by
  intro m
  cases m with
  | draw => rfl
  | wasteToFound c =>
      rcases c with ⟨s, r⟩ <;> cases s <;> cases r <;> decide
  | wasteToTab c b => rfl
  | tabToFound c =>
      rcases c with ⟨s, r⟩ <;> cases s <;> cases r <;> decide
  | foundToTab c b =>
      cases b with
      | inl n =>
          rcases c with ⟨s, r⟩ <;> cases s <;> cases r <;> cases n <;> decide
      | inr z =>
          rcases c with ⟨s, r⟩ <;> rcases z with ⟨zs, zr⟩ <;>
            cases s <;> cases r <;> cases zs <;> cases zr <;> decide
  | tabToTab c b => exact fcH_H1_slides_none c b

theorem fcH_H1_noplay : ∀ (play : List Move) (w : State),
    fcH_H1.run play = some w → w = fcH_H1 := by
  intro play
  induction play with
  | nil =>
      intro w h
      injection h with h'
      exact h'.symm
  | cons m t ih =>
      intro w h
      have hnone := fcH_H1_frozen m
      rw [show fcH_H1.run (m :: t) = none from by
        show (match State.step fcH_H1 m with
          | some s' => s'.run t
          | none => none) = none
        rw [hnone]] at h
      exact absurd h (by simp)

theorem fcH_H1_notSameOrbit : ¬ sameOrbitSetoid.r fcH fcH_H1 := by
  intro h
  obtain ⟨σ, hσ, -⟩ := h
  have hrun := ShufflePlayW_run hσ
  have hw := fcH_H1_noplay σ fcH hrun
  refine absurd (congrArg (fun s => (s.piles Anchor.p2).faceUp) hw) (by decide)

/-- **THE RAISE-RUN'S ENDPOINT IS A CLASS-MATE** — the raise is
mirror-backed: the giveback `4♥` onto `5♠` returns the start
exactly (the component dance below), so the leg is `reversibleAtW`
and the witness shuffles both ways. -/
private def fcH_H2m : State := fcT fcH_H2 (Move.foundToTab H4 (Sum.inr S5))

theorem fcH_H2m_step :
    State.step fcH_H2 (Move.foundToTab H4 (Sum.inr S5)) = some fcH_H2m := rfl

theorem fcH_H2m_eq : fcH_H2m = fcH := by
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
  · cases σ <;> rfl
  · cases a <;> rfl
  · rfl
  · rfl
  · rfl

theorem fcH_H2_mirrorStep :
    State.step fcH_H2 (Move.foundToTab H4 (Sum.inr S5)) = some fcH := by
  rw [← fcH_H2m_eq]
  exact fcH_H2m_step

theorem fcH_H2_sameOrbit : sameOrbitSetoid.r fcH fcH_H2 :=
  ⟨[Move.foundToTab H4 (Sum.inr S5)],
    ShufflePlayW.cons
      ⟨fcH, [Move.tabToFound H4], fcH_H2_mirrorStep,
        run_one fcH_stepRaise⟩
      fcH_H2_mirrorStep (ShufflePlayW.nil fcH),
    [Move.tabToFound H4],
    ShufflePlayW.cons
      ⟨fcH_H2, [Move.foundToTab H4 (Sum.inr S5)], fcH_stepRaise,
        run_one fcH_H2_mirrorStep⟩
      fcH_stepRaise (ShufflePlayW.nil fcH_H2)⟩

/-- **THE RUNG SPLIT IS REAL** — the bury-run's endpoint reads the
heart rung at 3 (the license died), the raise-run's at 4 (the
mirror-backed climb); and the two are NOT `BareCargoEquiv`,
certified through the main leaf's own fix row (the rungs differ
under the fixed founds — the fix theorem's first application). -/
theorem fcH_rungSplit : rungAt fcH_H1 Suit.heart = 3 ∧
    rungAt fcH_H2 Suit.heart = 4 := ⟨rfl, rfl⟩

theorem fcH_H1H2_notBareCargo : ¬ BareCargoEquiv fcH_H1 fcH_H2 := by
  intro h
  have hσ := (cargo_fix_rungs h).2 Suit.heart
  rw [fcH_rungSplit.1, fcH_rungSplit.2] at hσ
  exact absurd hσ (by decide)

/-! ## §3. The verdict packager -/

/-- **THE PROBE LEDGER** — every board, one conjunction:

* BOARD (i) `fcS`: the ascent-twin contention board is WF and
CERTIFIED FORKLESS (census silent, decided); the twin reds are a
located candidate pair (the contention shape is real); the two
maximal runs (bury the heart twin / bury the diamond twin) land at
`AscentStuck` endpoints whose rung vectors AGREE ON ALL FOUR SUITS
(the twin freeze — GRADE-A SURVIVES THE DECISIVE BOARD); the
endpoints are distinct, NOT `BareCargoEquiv` (cargo-frozen both),
and the start is not itself stuck.
* BOARD `fcH` (the (ii) lb-derivative with the pair cell entombed,
  doubling as the (iii) hunt): WF and CERTIFIED FORKLESS; no
  `MobileTwin` lives at the head (the raise is guard-free); the
  two maximal runs (the burn-bury vs. the raise) land at stuck
  endpoints with heart rungs 3 ≠ 4 — THE SPLIT IS REAL — the
  bury-endpoint is FROZEN and EXITS THE CLASS, the raise-endpoint
  IS a class-mate, and the two are NOT `BareCargoEquiv` (certified
  through the main leaf's fix row). -/
theorem ForklessCeilingProbe_verdicts :
    fcS.WF ∧ classCensusB fcS = false ∧ Forkless fcS ∧
      PairCandidate fcS H4 ∧
        AscentRun fcS [Move.tabToTab H4 (Sum.inr S5)] fcS_A ∧
          AscentStuck fcS_A ∧ MaxAscentEndpoint fcS fcS_A ∧
            AscentRun fcS [Move.tabToTab D4 (Sum.inr S5)] fcS_B ∧
              AscentStuck fcS_B ∧ MaxAscentEndpoint fcS fcS_B ∧
                (∀ σ : Suit, rungAt fcS_A σ = rungAt fcS_B σ) ∧
                  fcS_A ≠ fcS_B ∧ ¬ BareCargoEquiv fcS_A fcS_B ∧ ¬ AscentStuck fcS ∧
      fcH.WF ∧ classCensusB fcH = false ∧ Forkless fcH ∧
        (∀ y : Card, ¬ MobileTwin fcH y) ∧
          AscentRun fcH [Move.tabToTab S3 (Sum.inr H4)] fcH_H1 ∧
            AscentStuck fcH_H1 ∧ MaxAscentEndpoint fcH fcH_H1 ∧
              AscentRun fcH [Move.tabToFound H4] fcH_H2 ∧
                AscentStuck fcH_H2 ∧ MaxAscentEndpoint fcH fcH_H2 ∧
                  rungAt fcH_H1 Suit.heart ≠ rungAt fcH_H2 Suit.heart ∧
                    ¬ sameOrbitSetoid.r fcH fcH_H1 ∧
                      sameOrbitSetoid.r fcH fcH_H2 ∧
                        ¬ BareCargoEquiv fcH_H1 fcH_H2 := by
  refine ⟨fcS_wf, fcS_censusB, fcS_forkless, fcS_pairCandidate, fcS_runA,
    fcS_A_stuck, fcS_A_maximal, fcS_runB, fcS_B_stuck, fcS_B_maximal,
    fcS_AB_rungsAgree, fcS_AB_ne, fcS_AB_notBareCargo, fcS_notStuck,
    fcH_wf, fcH_censusB, fcH_forkless, fcH_noMobileTwin, fcH_runBurn,
    fcH_H1_stuck, fcH_H1_maximal, fcH_runRaise, fcH_H2_stuck, fcH_H2_maximal,
    ?_, fcH_H1_notSameOrbit, fcH_H2_sameOrbit, fcH_H1H2_notBareCargo⟩
  intro h
  rw [fcH_rungSplit.1, fcH_rungSplit.2] at h
  exact absurd h (by decide)

/-- **THE GRADE-C KILL RECORD** — Grade-C re-phrased WITHOUT the
class-mate premises (the frozen `ceiling_gradeC` signature with the
two `sameOrbitSetoid.r st W` rows struck) is REFUTED at the (i) board
`fcS`: the certified-forkless start carries the two maximal ascent
runs of `ForklessCeilingProbe_verdicts`'s (i)-board conjuncts — bury
the heart twin (`fcS_runA` → `fcS_A`, `fcS_A_stuck`) vs. bury the
diamond twin (`fcS_runB` → `fcS_B`, `fcS_B_stuck`), both packaged as
`MaxAscentEndpoint` — and the class-mate-free phrasing asserts
`fcS_A = fcS_B` of exactly those endpoints; `fcS_AB_ne` refutes it on
the nose.  THE SHAPE KILLED IS THE FULL LOCAL DATA, NOT A WEAK
SHELL: the endpoints AGREE on every rung (`fcS_AB_rungsAgree`) and
are not `BareCargoEquiv` (`fcS_AB_notBareCargo`) — Grade-A and
Grade-B survive this board; Grade-C's state-identity does not.  THE
RECORD, IN TRUTH: the main leaf's `ceiling_gradeC` itself stays
BYTE-FROZEN — EXPECTED FALSE, documented, not chased, its `sorry` the
honest witness of a FALSE statement — and this row is the exhibit
its own docstring promises ("the probe leaf's boundary exhibits are
the expected witnesses"), landed as the house refutation record
(cf. `ascent_cover_cell_refuted`, `lowslab_waste_reseat_refuted`).
The struck class-mate premise is the phrasing's load-bearing guard
at this board: the seating legs are burn-armed — their mirror
returns barred, the §1 `fcS_A_return_leg_blocked`/
`fcS_B_return_leg_blocked` exhibits the boundary datum toward the
commit story (the fuller orbit-exit read is not certified here; the
bars are). -/
theorem ceiling_gradeC_unconditioned_refuted :
    ¬ ∀ (st : State), st.WF → Forkless st →
      ∀ {ρ₁ : List Move} {W₁ : State},
        AscentRun st ρ₁ W₁ → AscentStuck W₁ →
        ∀ {ρ₂ : List Move} {W₂ : State},
        AscentRun st ρ₂ W₂ → AscentStuck W₂ →
        W₁ = W₂ := by
  intro h
  exact absurd
    (h fcS fcS_wf fcS_forkless fcS_runA fcS_A_stuck fcS_runB fcS_B_stuck)
    fcS_AB_ne

/-- **THE PACKAGE EXTENDED WITHOUT AN EDIT UPSTREAM** — this round's
extension packaged as one conjunction (the landed
`ForklessCeilingProbe_verdicts` statement above is untouched; read
the two together for the full falsifier ledger): the Grade-C
unconditioned kill record and the two burn-seat mirror exhibits
(the class-mate boundary datum, A-side / B-side). -/
theorem ForklessCeilingProbe_verdicts2 :
    (¬ ∀ (st : State), st.WF → Forkless st →
      ∀ {ρ₁ : List Move} {W₁ : State},
        AscentRun st ρ₁ W₁ → AscentStuck W₁ →
        ∀ {ρ₂ : List Move} {W₂ : State},
        AscentRun st ρ₂ W₂ → AscentStuck W₂ →
        W₁ = W₂) ∧
      State.step fcS_A (Move.tabToTab H4 (Sum.inl Anchor.p1)) = none ∧
      State.step fcS_B (Move.tabToTab D4 (Sum.inl Anchor.p2)) = none :=
  ⟨ceiling_gradeC_unconditioned_refuted, fcS_A_return_leg_blocked,
    fcS_B_return_leg_blocked⟩

/-! ## The audit battery

Zero SORRY, zero `Classical.choice` — every fresh head at the
house's clean decide/kernel grade (`[propext]` or
`[propext, Quot.sound]` per its consumption; the big matrices are
kernel folds).  The Grade-C kill record and the burn-seat exhibits
ride the (i) board's landed rows at the same clean grade — this
leaf stays ZERO-SORRY; the ceiling Grades' sorries live only in the
main leaf, frozen as the honest FALSE witnesses their docstrings
record. -/

#print axioms fcS_wf
#print axioms fcS_censusB
#print axioms fcS_forkless
#print axioms fcS_pairCandidate
#print axioms fcS_runA
#print axioms fcS_runB
#print axioms fcS_A_mobileH4
#print axioms fcS_A_mobileD4
#print axioms fcS_B_mobileH4
#print axioms fcS_B_mobileD4
#print axioms fcS_A_faceUp
#print axioms fcS_B_faceUp
#print axioms fcS_A_slides_none
#print axioms fcS_B_slides_none
#print axioms fcS_AB_rungsAgree
#print axioms fcS_AB_ne
#print axioms fcS_A_nocargo
#print axioms fcS_B_nocargo
#print axioms fcS_AB_notBareCargo
#print axioms fcS_A_stuck
#print axioms fcS_B_stuck
#print axioms fcS_A_maximal
#print axioms fcS_B_maximal
#print axioms fcS_notStuck
#print axioms fcS_A_return_leg_blocked
#print axioms fcS_B_return_leg_blocked
#print axioms fcH_wf
#print axioms fcH_censusB
#print axioms fcH_forkless
#print axioms fcH_faceUp_which
#print axioms fcH_noMobileTwin
#print axioms fcH_runBurn
#print axioms fcH_runRaise
#print axioms fcH_H1_slides_none
#print axioms fcH_H2_slides_none
#print axioms fcH_H1_stuck
#print axioms fcH_H2_stuck
#print axioms fcH_H1_maximal
#print axioms fcH_H2_maximal
#print axioms fcH_H1_frozen
#print axioms fcH_H1_noplay
#print axioms fcH_H1_notSameOrbit
#print axioms fcH_H2m_eq
#print axioms fcH_H2_mirrorStep
#print axioms fcH_H2_sameOrbit
#print axioms fcH_rungSplit
#print axioms fcH_H1H2_notBareCargo
#print axioms ForklessCeilingProbe_verdicts
#print axioms ceiling_gradeC_unconditioned_refuted
#print axioms ForklessCeilingProbe_verdicts2

/-! ## §7. THE P1 LIFTER HARNESS `gL` — THE ILLEGAL TOWER CARRIED
off-WF

The P1 verdict block, the lifter round's append: the artificial
NON-WF board `gL` — `p0` carries the illegal-under-king tower
(`[K♠, 7♥]`, `runOK`'s bottom-first read: the `7♥` is SEATED ON the
`K♠`, and only a QUEEN of the other color may sit on a king, so the
face-up run breaks the `WF` invariant's second conjunct); `p1`
stands fully bare (the lift's empty seat); every other pile is
trivial; the foundations are cold; the zones empty.  THE LIFTER:
the king-headed run — tower and all — rides the king bar of
`canPlace` OUT to `p1`, and the same king-headed run rides it BACK
HOME to the emptied `p0`; the empty-seat letters read only the run
HEAD, so the two-card illegal CARGO crosses both legs unseen (the
king bar never consults `runOK`, and `canSitOn` is never asked for
the cards behind the head).  ON-WF THE CARRY IS BANNED: a `WF`
state's every face-up run is `runOK`-legal — its king-headed runs
carry exactly a QUEEN of the other color — so NO ILLEGAL TOWER
COULD EVER ASSEMBLE to be carried; no `runOK` protection survives
off-WF, and that is precisely the lifter's legality.  This is the
`CARRIED`-off-WF arm's P1 exhibit, its verdicts landed below:
`gL_nonWF` (the board's certification), `gL_lift_fires` and
`gL_dropback_fires` (the MirrorLetter certificate's both halves at
the board — the out leg and the one-move in-place drop-back retrace
re-landing at `gL` exactly), and `gL_both_ways` (the two-letter
out-and-back play literal returning `some gL`, the bare both-ways
witness beyond the trivial `[]`-identity).  THE P2 HUNT APPEND (the
slides-which round, the burn-hunt's resolved reading): the
decide-grade inventory of the WHOLE move alphabet at both boards —
`gL_fires_iff`/`gL'_fires_iff`, the boards' entire firing alphabet
is the KING BAR (at `gL` exactly the six letters
`tabToTab ♠K (Sum.inl a)` with `a ≠ p0`; at `gL'` the six drops
with `a ≠ p1`; every other letter of every kind refuses by the
boards' cold facts) — and the hunt's VERDICT read straight off it,
`gL_noburn`/`gL'_noburn`: NO BURN AT THE LIFTER BOARD — every
firing leg is one-move-retraceable in place (the mirror letter
EXISTS for every firing pair), the illegal tower travels only by
its king head, every lift reversible, the `7♥` board-locked — its
seat-takers (the black sixes `canSitOn` would admit onto a red
seven) and its landing pads (the black eights it would ride onto)
are all absent, so the six-on-seven fact is RANK-TRUE but
BOARD-UNLOCATABLE (the subsumed matrix cell); the fcS §1 orbit-exit
read stays where §1 left it (the bars are; the fuller orbit-exit
read is not certified here — not chased this round). -/

private def SK : Card := fcc .spade .king
private def H7 : Card := fcc .heart .seven

/-- The harness's foundation heights: every suit cold (lift boards
write no foundation and read none). -/
private def gL_hmap : Suit → Nat
  | .heart => 0 | .diamond => 0 | .spade => 0 | .club => 0

/-- **THE LIFTER BOARD `gL`** — the artificial NON-WF state: `p0`'s
face-up run is the illegal-under-king tower `[K♠, 7♥]` (the `7♥`
seated on the king; the hidden deck empty), `p1` is the lift's
vacant empty seat, the other piles are trivial, and the foundations
are cold (the boards' house take-spelling at height zero). -/
private def gL : State where
  found := fun s => s.upCards.take (gL_hmap s)
  piles := fun a => match a with
    | .p0 => ⟨[], [SK, H7]⟩
    | .p1 => ⟨[], []⟩
    | .p2 => ⟨[], []⟩
    | .p3 => ⟨[], []⟩
    | .p4 => ⟨[], []⟩
    | .p5 => ⟨[], []⟩
    | .p6 => ⟨[], []⟩
  stock := []
  waste := []
  drawStep := 1

/-- **ROW (a): THE BOARD IS NON-WF** (decided) — the second `WF`
conjunct's `runOK` hole, read at the tower's pile: the heart
seven's seat on the king is rank-barred. -/
theorem gL_nonWF : ¬ gL.WF := by
  intro h
  exact absurd (h.2.1 Anchor.p0) (by decide)

/-- **THE LIFTED BOARD `gL'`** — the successor the lifter leg
writes: the whole king-headed tower rides out to `p1` and `p0`
stands emptied (the drop-back's vacant home seat). -/
private def gL' : State := fcT gL (Move.tabToTab SK (Sum.inl Anchor.p1))

/-- **ROW (b): THE LIFTER LEG FIRES** — `K♠` heads the face-up run
and `p1` is empty: the king bar of `canPlace` admits the head, and
the entire two-card tower lifts out as one run, `p0` emptying
behind it. -/
theorem gL_lift_fires :
    State.step gL (Move.tabToTab SK (Sum.inl Anchor.p1)) = some gL' := rfl

private def gLb : State := fcT gL' (Move.tabToTab SK (Sum.inl Anchor.p0))

theorem gLb_step :
    State.step gL' (Move.tabToTab SK (Sum.inl Anchor.p0)) = some gLb := rfl

theorem gLb_eq : gLb = gL := by
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
  · cases σ <;> rfl
  · cases a <;> rfl
  · rfl
  · rfl
  · rfl

/-- **ROW (c): THE DROP-BACK FIRES — THE IN-PLACE RETRACE** — the
same king-headed run returns home to the EMPTIED `p0`: the retrace
letter is the empty-seat letter (the sketched seating letter
`Sum.inr 7♥` — a king ONTO a seven — is rank-barred by `canSitOn`
and refuses; the king bar of the vacant home seat is the letter
that fires), and the `putRun` restores the tower to its exact pile,
re-landing at `gL` precisely — the MirrorLetter certificate's both
halves at the board, `gL_lift_fires` out and this back. -/
theorem gL_dropback_fires :
    State.step gL' (Move.tabToTab SK (Sum.inl Anchor.p0)) = some gL := by
  rw [← gLb_eq]
  exact gLb_step

/-- **ROW (d): THE BARE BOTH-WAYS WITNESS** — the out-and-back play
literal returns `some gL`: the two letters compose at the board
into the identity on it (a two-letter both-ways pair beyond the
trivial `[]`-identity, the illegal tower carried off-WF out and
back with neither leg ever consulting `runOK`). -/
theorem gL_both_ways :
    State.run gL [Move.tabToTab SK (Sum.inl Anchor.p1),
      Move.tabToTab SK (Sum.inl Anchor.p0)] = some gL := by
  have h2 : State.run gL' [Move.tabToTab SK (Sum.inl Anchor.p0)] = some gL :=
    run_one gL_dropback_fires
  show (match State.step gL (Move.tabToTab SK (Sum.inl Anchor.p1)) with
    | some s' => s'.run [Move.tabToTab SK (Sum.inl Anchor.p0)]
    | none => none) = some gL
  rw [gL_lift_fires]
  exact h2

/- The harness's own four-line battery, the audit tail's pattern:
every fresh non-`rfl` head at the clean decide/kernel grade. -/
#print axioms gL_nonWF
#print axioms gLb_eq
#print axioms gL_dropback_fires
#print axioms gL_both_ways

/-! ### §7. THE P2 SLIDES-WHICH HUNT — THE MIRROR-CERTIFICATE KITS

The hunt round's board kits, ahead of the inventory rows: (1) at
`gL` the five remaining lift targets `gL2`–`gL6` (the `p1` target is
the landed `gL'`), each with its drop-back mirror kit `gLnb` — the
one-move home-drop retrace `tabToTab ♠K (Sum.inl p0)` re-landing
at `gL` exactly, the UNIFORM mirror letter every lift at the board
shares; (2) at `gL'` the five fresh drop targets `gD2`–`gD6` (the
`p0` drop is the landed `gLb`, whose OWN mirror is the landed lift
itself read through `gLb_eq`), each with its lift-back mirror kit
`gDnb` — the re-ascent `tabToTab ♠K (Sum.inl p1)` re-landing at
`gL'` exactly.  Six lifts mirror to six drops; the noburn rows
below are exactly this uniformity, certified. -/

/-- The `p2` lift board (the tower seated at `p2`, the source `p0`
emptied behind it). -/
private def gL2 : State := fcT gL (Move.tabToTab SK (Sum.inl Anchor.p2))

theorem gL2_step :
    State.step gL (Move.tabToTab SK (Sum.inl Anchor.p2)) = some gL2 := rfl

private def gL2b : State := fcT gL2 (Move.tabToTab SK (Sum.inl Anchor.p0))

theorem gL2b_step :
    State.step gL2 (Move.tabToTab SK (Sum.inl Anchor.p0)) = some gL2b := rfl

theorem gL2b_eq : gL2b = gL := by
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
  · cases σ <;> rfl
  · cases a <;> rfl
  · rfl
  · rfl
  · rfl

/-- The `p2`-lift's one-move drop-back home (the uniform home-seat
letter at work: the emptied `p0` re-admits the king-headed tower). -/
theorem gL2_dropback :
    State.step gL2 (Move.tabToTab SK (Sum.inl Anchor.p0)) = some gL := by
  rw [← gL2b_eq]
  exact gL2b_step

/-- The `p3` lift board. -/
private def gL3 : State := fcT gL (Move.tabToTab SK (Sum.inl Anchor.p3))

theorem gL3_step :
    State.step gL (Move.tabToTab SK (Sum.inl Anchor.p3)) = some gL3 := rfl

private def gL3b : State := fcT gL3 (Move.tabToTab SK (Sum.inl Anchor.p0))

theorem gL3b_step :
    State.step gL3 (Move.tabToTab SK (Sum.inl Anchor.p0)) = some gL3b := rfl

theorem gL3b_eq : gL3b = gL := by
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
  · cases σ <;> rfl
  · cases a <;> rfl
  · rfl
  · rfl
  · rfl

theorem gL3_dropback :
    State.step gL3 (Move.tabToTab SK (Sum.inl Anchor.p0)) = some gL := by
  rw [← gL3b_eq]
  exact gL3b_step

/-- The `p4` lift board. -/
private def gL4 : State := fcT gL (Move.tabToTab SK (Sum.inl Anchor.p4))

theorem gL4_step :
    State.step gL (Move.tabToTab SK (Sum.inl Anchor.p4)) = some gL4 := rfl

private def gL4b : State := fcT gL4 (Move.tabToTab SK (Sum.inl Anchor.p0))

theorem gL4b_step :
    State.step gL4 (Move.tabToTab SK (Sum.inl Anchor.p0)) = some gL4b := rfl

theorem gL4b_eq : gL4b = gL := by
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
  · cases σ <;> rfl
  · cases a <;> rfl
  · rfl
  · rfl
  · rfl

theorem gL4_dropback :
    State.step gL4 (Move.tabToTab SK (Sum.inl Anchor.p0)) = some gL := by
  rw [← gL4b_eq]
  exact gL4b_step

/-- The `p5` lift board. -/
private def gL5 : State := fcT gL (Move.tabToTab SK (Sum.inl Anchor.p5))

theorem gL5_step :
    State.step gL (Move.tabToTab SK (Sum.inl Anchor.p5)) = some gL5 := rfl

private def gL5b : State := fcT gL5 (Move.tabToTab SK (Sum.inl Anchor.p0))

theorem gL5b_step :
    State.step gL5 (Move.tabToTab SK (Sum.inl Anchor.p0)) = some gL5b := rfl

theorem gL5b_eq : gL5b = gL := by
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
  · cases σ <;> rfl
  · cases a <;> rfl
  · rfl
  · rfl
  · rfl

theorem gL5_dropback :
    State.step gL5 (Move.tabToTab SK (Sum.inl Anchor.p0)) = some gL := by
  rw [← gL5b_eq]
  exact gL5b_step

/-- The `p6` lift board. -/
private def gL6 : State := fcT gL (Move.tabToTab SK (Sum.inl Anchor.p6))

theorem gL6_step :
    State.step gL (Move.tabToTab SK (Sum.inl Anchor.p6)) = some gL6 := rfl

private def gL6b : State := fcT gL6 (Move.tabToTab SK (Sum.inl Anchor.p0))

theorem gL6b_step :
    State.step gL6 (Move.tabToTab SK (Sum.inl Anchor.p0)) = some gL6b := rfl

theorem gL6b_eq : gL6b = gL := by
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
  · cases σ <;> rfl
  · cases a <;> rfl
  · rfl
  · rfl
  · rfl

theorem gL6_dropback :
    State.step gL6 (Move.tabToTab SK (Sum.inl Anchor.p0)) = some gL := by
  rw [← gL6b_eq]
  exact gL6b_step

/-- **P2 ROW (e) — THE COLD KINDS AT `gL`** (decided, the
whole-alphabet refusal half for the five non-`tabToTab` kinds): the
draw deals nothing (stock and waste both empty); the waste arms
starve (`wasteIs` is false for every card); the rung pass is cold
(no ace tops any pile — the only top on the board is the `7♥`,
rungs away from every foundation); no foundation top exists to
worry back down. -/
theorem gL_cold_kinds_none :
    State.step gL Move.draw = none ∧
    (∀ (c : Card), State.step gL (Move.wasteToFound c) = none) ∧
    (∀ (c : Card) (b : Base), State.step gL (Move.wasteToTab c b) = none) ∧
    (∀ (c : Card), State.step gL (Move.tabToFound c) = none) ∧
    (∀ (c : Card) (b : Base), State.step gL (Move.foundToTab c b) = none) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · intro c
    rcases c with ⟨s, r⟩ <;> cases s <;> cases r <;> decide
  · intro c b
    rfl
  · intro c
    rcases c with ⟨s, r⟩ <;> cases s <;> cases r <;> decide
  · intro c b
    rcases c with ⟨s, r⟩ <;> cases s <;> cases r <;>
      cases b with
      | inl n => cases n <;> decide
      | inr z => rcases z with ⟨zs, zr⟩ <;> cases zs <;> cases zr <;> decide

/-- **P2 ROW (f) — THE SEAT INVENTORY AT `gL`** (the iff-row,
decide-grade, POSITIVE: the firing letters enumerated): a seat
letter `tabToTab c (Sum.inl a)` fires iff its head is the tower's
king ` ♠K` and the seat is one of the six empty non-source
positions (`a ≠ p0`, i.e. `a ∈ {p1, …, p6}` — `p0` itself is the
tower's live home and refuses the king bar). -/
theorem gL_tabToTab_inl_iff : ∀ (c : Card) (a : Anchor),
    State.step gL (Move.tabToTab c (Sum.inl a)) ≠ none ↔
      c = SK ∧ a ≠ Anchor.p0 := by
  intro c a
  rcases c with ⟨s, r⟩ <;> cases s <;> cases r <;> cases a <;> decide

/-- **P2 ROW (g) — THE TARGET MATRIX AT `gL`** (decided): no
onto-card letter fires — the only locatable pile top on the whole
board is the `7♥` itself: it seats no king (rank off by six) and
no card of its own rank/color (twin-barred), and `♠K` is not a top
at all (the seven sits on it), so no `inr` target ever locates. -/
theorem gL_tabToTab_inr_none : ∀ (c : Card) (z : Card),
    State.step gL (Move.tabToTab c (Sum.inr z)) = none := by
  intro c z
  rcases c with ⟨s, r⟩ <;> rcases z with ⟨zs, zr⟩ <;>
    cases s <;> cases r <;> cases zs <;> cases zr <;> decide

/-- **P2 ROW 1 — THE WHOLE-ALPHABET INVENTORY AT `gL`** (the hunt's
exhaustive reading, decide-grade): a move `m` fires at `gL` iff it
is one of the SIX lifter letters `tabToTab ♠K (Sum.inl a)` with
`a ≠ p0` (`a ∈ {p1, …, p6}`); every letter of every other kind
refuses (the cold rows), and within `tabToTab` only the six
king-to-empty-seat letters fire (the seat iff plus the target
matrix).  THE ILLEGAL TOWER TRAVELS ONLY BY ITS KING HEAD. -/
theorem gL_fires_iff : ∀ (m : Move), State.step gL m ≠ none ↔
    ∃ (a : Anchor), a ≠ Anchor.p0 ∧ m = Move.tabToTab SK (Sum.inl a) := by
  intro m
  constructor
  · intro h
    cases m with
    | draw =>
        rw [gL_cold_kinds_none.1] at h
        exact absurd rfl h
    | wasteToFound c =>
        rw [gL_cold_kinds_none.2.1 c] at h
        exact absurd rfl h
    | wasteToTab c b =>
        rw [gL_cold_kinds_none.2.2.1 c b] at h
        exact absurd rfl h
    | tabToFound c =>
        rw [gL_cold_kinds_none.2.2.2.1 c] at h
        exact absurd rfl h
    | foundToTab c b =>
        rw [gL_cold_kinds_none.2.2.2.2 c b] at h
        exact absurd rfl h
    | tabToTab c b =>
        cases b with
        | inl a =>
            obtain ⟨hc, hne⟩ := (gL_tabToTab_inl_iff c a).mp h
            subst hc
            exact ⟨a, hne, rfl⟩
        | inr z =>
            rw [gL_tabToTab_inr_none c z] at h
            exact absurd rfl h
  · rintro ⟨a, hne, rfl⟩
    exact (gL_tabToTab_inl_iff SK a).mpr ⟨rfl, hne⟩

/-- **P2 ROW 2 (half) — THE NO-BURN VERDICT AT `gL`** (the hunt's
burn row, the strongest honest form): every firing leg at the
lifter board is one-move-retraceable IN PLACE — for every `(m, s')`
with `step gL m = some s'` the mirror letter EXISTS.  The six lifts
mirror by the ONE uniform home-drop letter `tabToTab ♠K (inl p0)`,
each re-landing at `gL` exactly (the `p1`-lift by the landed
`gL_dropback_fires`, the others by their kits).  NO LEG IS
BURN-ARMED in the house sense: every departure empties its source
pile over an empty hidden deck, and the emptied seat re-admits
precisely the king-headed run that left — the illegal tower's
carrier never strands its retake. -/
theorem gL_noburn : ∀ (m : Move) (s' : State),
    State.step gL m = some s' → ∃ (mr : Move), State.step s' mr = some gL := by
  intro m s' hs
  have hfire : State.step gL m ≠ none := by
    intro hnone
    rw [hnone] at hs
    exact absurd hs (by simp)
  obtain ⟨a, hne, hm⟩ := (gL_fires_iff m).mp hfire
  subst hm
  cases a with
  | p0 => exact absurd rfl hne
  | p1 =>
      rw [gL_lift_fires] at hs
      injection hs with hsub
      subst hsub
      exact ⟨Move.tabToTab SK (Sum.inl Anchor.p0), gL_dropback_fires⟩
  | p2 =>
      rw [gL2_step] at hs
      injection hs with hsub
      subst hsub
      exact ⟨Move.tabToTab SK (Sum.inl Anchor.p0), gL2_dropback⟩
  | p3 =>
      rw [gL3_step] at hs
      injection hs with hsub
      subst hsub
      exact ⟨Move.tabToTab SK (Sum.inl Anchor.p0), gL3_dropback⟩
  | p4 =>
      rw [gL4_step] at hs
      injection hs with hsub
      subst hsub
      exact ⟨Move.tabToTab SK (Sum.inl Anchor.p0), gL4_dropback⟩
  | p5 =>
      rw [gL5_step] at hs
      injection hs with hsub
      subst hsub
      exact ⟨Move.tabToTab SK (Sum.inl Anchor.p0), gL5_dropback⟩
  | p6 =>
      rw [gL6_step] at hs
      injection hs with hsub
      subst hsub
      exact ⟨Move.tabToTab SK (Sum.inl Anchor.p0), gL6_dropback⟩

/-- The `gLb` board's own mirror: the lifted board's drop-land is
`gL` itself by `gLb_eq`, so its lift-back is the landed lift. -/
theorem gLb_liftback :
    State.step gLb (Move.tabToTab SK (Sum.inl Anchor.p1)) = some gL' := by
  rw [gLb_eq]
  exact gL_lift_fires

/-- The `p2` drop board (the tower re-dropped at `p2`, the source
`p1` emptied). -/
private def gD2 : State := fcT gL' (Move.tabToTab SK (Sum.inl Anchor.p2))

theorem gD2_step :
    State.step gL' (Move.tabToTab SK (Sum.inl Anchor.p2)) = some gD2 := rfl

private def gD2b : State := fcT gD2 (Move.tabToTab SK (Sum.inl Anchor.p1))

theorem gD2b_step :
    State.step gD2 (Move.tabToTab SK (Sum.inl Anchor.p1)) = some gD2b := rfl

theorem gD2b_eq : gD2b = gL' := by
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
  · cases σ <;> rfl
  · cases a <;> rfl
  · rfl
  · rfl
  · rfl

/-- The `p2`-drop's one-move lift-back home (the uniform lift letter
at work: the emptied `p1` re-admits the king-headed tower). -/
theorem gD2_liftback :
    State.step gD2 (Move.tabToTab SK (Sum.inl Anchor.p1)) = some gL' := by
  rw [← gD2b_eq]
  exact gD2b_step

/-- The `p3` drop board. -/
private def gD3 : State := fcT gL' (Move.tabToTab SK (Sum.inl Anchor.p3))

theorem gD3_step :
    State.step gL' (Move.tabToTab SK (Sum.inl Anchor.p3)) = some gD3 := rfl

private def gD3b : State := fcT gD3 (Move.tabToTab SK (Sum.inl Anchor.p1))

theorem gD3b_step :
    State.step gD3 (Move.tabToTab SK (Sum.inl Anchor.p1)) = some gD3b := rfl

theorem gD3b_eq : gD3b = gL' := by
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
  · cases σ <;> rfl
  · cases a <;> rfl
  · rfl
  · rfl
  · rfl

theorem gD3_liftback :
    State.step gD3 (Move.tabToTab SK (Sum.inl Anchor.p1)) = some gL' := by
  rw [← gD3b_eq]
  exact gD3b_step

/-- The `p4` drop board. -/
private def gD4 : State := fcT gL' (Move.tabToTab SK (Sum.inl Anchor.p4))

theorem gD4_step :
    State.step gL' (Move.tabToTab SK (Sum.inl Anchor.p4)) = some gD4 := rfl

private def gD4b : State := fcT gD4 (Move.tabToTab SK (Sum.inl Anchor.p1))

theorem gD4b_step :
    State.step gD4 (Move.tabToTab SK (Sum.inl Anchor.p1)) = some gD4b := rfl

theorem gD4b_eq : gD4b = gL' := by
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
  · cases σ <;> rfl
  · cases a <;> rfl
  · rfl
  · rfl
  · rfl

theorem gD4_liftback :
    State.step gD4 (Move.tabToTab SK (Sum.inl Anchor.p1)) = some gL' := by
  rw [← gD4b_eq]
  exact gD4b_step

/-- The `p5` drop board. -/
private def gD5 : State := fcT gL' (Move.tabToTab SK (Sum.inl Anchor.p5))

theorem gD5_step :
    State.step gL' (Move.tabToTab SK (Sum.inl Anchor.p5)) = some gD5 := rfl

private def gD5b : State := fcT gD5 (Move.tabToTab SK (Sum.inl Anchor.p1))

theorem gD5b_step :
    State.step gD5 (Move.tabToTab SK (Sum.inl Anchor.p1)) = some gD5b := rfl

theorem gD5b_eq : gD5b = gL' := by
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
  · cases σ <;> rfl
  · cases a <;> rfl
  · rfl
  · rfl
  · rfl

theorem gD5_liftback :
    State.step gD5 (Move.tabToTab SK (Sum.inl Anchor.p1)) = some gL' := by
  rw [← gD5b_eq]
  exact gD5b_step

/-- The `p6` drop board. -/
private def gD6 : State := fcT gL' (Move.tabToTab SK (Sum.inl Anchor.p6))

theorem gD6_step :
    State.step gL' (Move.tabToTab SK (Sum.inl Anchor.p6)) = some gD6 := rfl

private def gD6b : State := fcT gD6 (Move.tabToTab SK (Sum.inl Anchor.p1))

theorem gD6b_step :
    State.step gD6 (Move.tabToTab SK (Sum.inl Anchor.p1)) = some gD6b := rfl

theorem gD6b_eq : gD6b = gL' := by
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
  · cases σ <;> rfl
  · cases a <;> rfl
  · rfl
  · rfl
  · rfl

theorem gD6_liftback :
    State.step gD6 (Move.tabToTab SK (Sum.inl Anchor.p1)) = some gL' := by
  rw [← gD6b_eq]
  exact gD6b_step

/-- **P2 ROW (e') — THE COLD KINDS AT `gL'`** (decided): the lifted
board's cold facts are its twin's — zones empty, foundations cold,
the `7♥` still the only pile top, still rungs away from every
foundation, still no locatable under-card. -/
theorem gL'_cold_kinds_none :
    State.step gL' Move.draw = none ∧
    (∀ (c : Card), State.step gL' (Move.wasteToFound c) = none) ∧
    (∀ (c : Card) (b : Base), State.step gL' (Move.wasteToTab c b) = none) ∧
    (∀ (c : Card), State.step gL' (Move.tabToFound c) = none) ∧
    (∀ (c : Card) (b : Base), State.step gL' (Move.foundToTab c b) = none) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · intro c
    rcases c with ⟨s, r⟩ <;> cases s <;> cases r <;> decide
  · intro c b
    rfl
  · intro c
    rcases c with ⟨s, r⟩ <;> cases s <;> cases r <;> decide
  · intro c b
    rcases c with ⟨s, r⟩ <;> cases s <;> cases r <;>
      cases b with
      | inl n => cases n <;> decide
      | inr z => rcases z with ⟨zs, zr⟩ <;> cases zs <;> cases zr <;> decide

/-- **P2 ROW (f') — THE SEAT INVENTORY AT `gL'`** (the iff-row,
decide-grade): a seat letter fires iff its head is ` ♠K` and the
seat is one of the six seats empty at the LIFTED board
(`a ≠ p1` — the tower's new home — i.e. `a ∈ {p0, p2, …, p6}`: the
home seat `p0` is back in the alphabet, the tower's `p1` is out). -/
theorem gL'_tabToTab_inl_iff : ∀ (c : Card) (a : Anchor),
    State.step gL' (Move.tabToTab c (Sum.inl a)) ≠ none ↔
      c = SK ∧ a ≠ Anchor.p1 := by
  intro c a
  rcases c with ⟨s, r⟩ <;> cases s <;> cases r <;> cases a <;> decide

/-- **P2 ROW (g') — THE TARGET MATRIX AT `gL'`** (decided): the
twin read — the `7♥` is again the only locatable pile top on the
whole board, and again seats nothing. -/
theorem gL'_tabToTab_inr_none : ∀ (c : Card) (z : Card),
    State.step gL' (Move.tabToTab c (Sum.inr z)) = none := by
  intro c z
  rcases c with ⟨s, r⟩ <;> rcases z with ⟨zs, zr⟩ <;>
    cases s <;> cases r <;> cases zs <;> cases zr <;> decide

/-- **P2 ROW 2 — THE WHOLE-ALPHABET INVENTORY AT `gL'`** (the six
drops): a move fires at the lifted board iff it is one of
`tabToTab ♠K (Sum.inl a)` with `a ≠ p1` (the SIX DROPS,
`a ∈ {p0, p2, …, p6}`); every other letter of every kind refuses. -/
theorem gL'_fires_iff : ∀ (m : Move), State.step gL' m ≠ none ↔
    ∃ (a : Anchor), a ≠ Anchor.p1 ∧ m = Move.tabToTab SK (Sum.inl a) := by
  intro m
  constructor
  · intro h
    cases m with
    | draw =>
        rw [gL'_cold_kinds_none.1] at h
        exact absurd rfl h
    | wasteToFound c =>
        rw [gL'_cold_kinds_none.2.1 c] at h
        exact absurd rfl h
    | wasteToTab c b =>
        rw [gL'_cold_kinds_none.2.2.1 c b] at h
        exact absurd rfl h
    | tabToFound c =>
        rw [gL'_cold_kinds_none.2.2.2.1 c] at h
        exact absurd rfl h
    | foundToTab c b =>
        rw [gL'_cold_kinds_none.2.2.2.2 c b] at h
        exact absurd rfl h
    | tabToTab c b =>
        cases b with
        | inl a =>
            obtain ⟨hc, hne⟩ := (gL'_tabToTab_inl_iff c a).mp h
            subst hc
            exact ⟨a, hne, rfl⟩
        | inr z =>
            rw [gL'_tabToTab_inr_none c z] at h
            exact absurd rfl h
  · rintro ⟨a, hne, rfl⟩
    exact (gL'_tabToTab_inl_iff SK a).mpr ⟨rfl, hne⟩

/-- **P2 ROW 2 (noburn half) — THE NO-BURN VERDICT AT `gL'`** (the
burn row at the lifted board, the strongest honest form): the six
drops mirror back by the ONE uniform lift letter
`tabToTab ♠K (inl p1)`, each re-landing at `gL'` exactly (the
`p0`-drop is the landed `gLb_step`, whose mirror is the landed
lift read through `gLb_eq`); no firing leg is burn-armed here
either — the lifted board strands no retake. -/
theorem gL'_noburn : ∀ (m : Move) (s' : State),
    State.step gL' m = some s' → ∃ (mr : Move), State.step s' mr = some gL' := by
  intro m s' hs
  have hfire : State.step gL' m ≠ none := by
    intro hnone
    rw [hnone] at hs
    exact absurd hs (by simp)
  obtain ⟨a, hne, hm⟩ := (gL'_fires_iff m).mp hfire
  subst hm
  cases a with
  | p0 =>
      rw [gLb_step] at hs
      injection hs with hsub
      subst hsub
      exact ⟨Move.tabToTab SK (Sum.inl Anchor.p1), gLb_liftback⟩
  | p1 => exact absurd rfl hne
  | p2 =>
      rw [gD2_step] at hs
      injection hs with hsub
      subst hsub
      exact ⟨Move.tabToTab SK (Sum.inl Anchor.p1), gD2_liftback⟩
  | p3 =>
      rw [gD3_step] at hs
      injection hs with hsub
      subst hsub
      exact ⟨Move.tabToTab SK (Sum.inl Anchor.p1), gD3_liftback⟩
  | p4 =>
      rw [gD4_step] at hs
      injection hs with hsub
      subst hsub
      exact ⟨Move.tabToTab SK (Sum.inl Anchor.p1), gD4_liftback⟩
  | p5 =>
      rw [gD5_step] at hs
      injection hs with hsub
      subst hsub
      exact ⟨Move.tabToTab SK (Sum.inl Anchor.p1), gD5_liftback⟩
  | p6 =>
      rw [gD6_step] at hs
      injection hs with hsub
      subst hsub
      exact ⟨Move.tabToTab SK (Sum.inl Anchor.p1), gD6_liftback⟩

/- The hunt block's own battery, the audit tail's pattern: every
fresh non-`rfl` head at the clean decide/kernel grade. -/
#print axioms gL_cold_kinds_none
#print axioms gL_tabToTab_inl_iff
#print axioms gL_tabToTab_inr_none
#print axioms gL_fires_iff
#print axioms gL_noburn
#print axioms gLb_liftback
#print axioms gL2b_eq
#print axioms gL3b_eq
#print axioms gL4b_eq
#print axioms gL5b_eq
#print axioms gL6b_eq
#print axioms gL2_dropback
#print axioms gL3_dropback
#print axioms gL4_dropback
#print axioms gL5_dropback
#print axioms gL6_dropback
#print axioms gL'_cold_kinds_none
#print axioms gL'_tabToTab_inl_iff
#print axioms gL'_tabToTab_inr_none
#print axioms gL'_fires_iff
#print axioms gL'_noburn
#print axioms gD2b_eq
#print axioms gD3b_eq
#print axioms gD4b_eq
#print axioms gD5b_eq
#print axioms gD6b_eq
#print axioms gD2_liftback
#print axioms gD3_liftback
#print axioms gD4_liftback
#print axioms gD5_liftback
#print axioms gD6_liftback
