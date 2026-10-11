import Orig.Canonical

/-! # CanonV3Probe — the V3-canonicalizer gating census (landing 1)

The V3 scaffold-pull fork fix (branch `orig-canon-v3`, rebased onto
macro-game `5ebef39`) was designed against the exchlaw B2
worried-king fork exhibit: the five-definition skeleton —
`TwinContended`, `Unblocker`, `HardContended`, `FinalV3`, and the
two-macro-leg runner (raise legs refuse to fire at contentions;
`scaffoldCycle` welds an unblocking pull with its
immediately-enabled stack and the cleanup re-raise; the boundary
measure Φ = foundation length strictly increasing at every
macro-leg boundary).  Per the house rule the skeleton is GATED on
one census question, decided here BEFORE any proof effort:

  **Is `TwinContended` inhabited at WF?**
     `TwinContended st c := both twins licensed-raise at st
     ∧ stacking either forecloses the other.`

THE VERDICT (this battery): **EMPTY at WF — under every pinned
FORECLOSE reading.**  The theorem-grade half rides the BANKED
monotone-stackability row `canRaise_lifted` (`Orig/Canonical.lean`:
"after a licensed lift of another card, `c`'s license survives"):
the two twins' licenses read zone-disjoint components (each one's
own suit rung, each one's own pile seat), and a licensed lift
writes only the lifted card's two zones — so the landed state of
either twin's raise CANNOT foreclose the other's license.  The
observed forks (the exchlaw B2 twin-kings cell, consumed here as
common material — hearts climbed A..Q, ♥K bare on p1, ♦K under ♣Q
on p5 — are CROSS-MATE: in each single state at most one twin is
licensed, so the fork lives across exchange mates, never inside a
state; its joining road is the A2 pull-highway (pull, exchange,
pull — every leg reversible), and the scaffold-pull rule has no
case to fire.  The skeleton retires as unneeded; it stays ledgered
as dormant design in `FUTURES-ORIG.md` §11, and no library file is
touched.

THE FORECLOSE READ — probe-pinned and marked (per the card): the
reading that could carry content at WF is LICENSE-DEATH — the
landed state of one twin's licensed raise forecloses the other's
license (`¬ CanRaise s' c.twin` at the landed `s'`).  The
alternates are struck at the cells:

* RAW-stackability death — refuted (the same zone argument; the
  probes carry the twin's rung and seat verbatim through the
  landing);
* FINAL-divergence — struck: both greedy orders of the twin pair
  land at `canon st`, literally (V2 confluence `canon_unique`,
  banked; the cells decide the join);
* UNDO-death — struck: the landed undo family survives the twin's
  own landing (cells decide: each saturated twin pulls back onto
  its exposed bases, and every pulled excursion re-saturates
  home).

Probe families (all WF-crafted full-deck cells, census-clean via
the stock mover; negative controls included; every gate throws on
failure — `lake env lean probes/CanonV3Probe.lean`):

* **V1** both-bare twin kings — the freeness suggestion of the
  exchlaw battery held up: both licensed, both fire, both orders
  land at `canon st`, the exchange-pair pose is the identity.
* **V2** both under-seat twin queens on conjugate bases (♣K / ♠K,
  the §1.8 crossed-pair geometry read at licensed seats) —
  independence, order-convergence, twin-blindness, and the undo
  round trip (each saturated queen pulls off onto either exposed
  base, and every pulled excursion re-saturates home).
* **V3** the mixed seat census (bare-king licensed twin with the
  twin mate unseatable above any base — kings sit under nothing —
  so a mixed licensed TWIN PAIR cannot exist; the queen leg of
  the cell carries the bare-king + under-seat queen coexistence).
* **V4** the ENABLEMENT mediation (a licensed lift that lights a
  NEW license: ♥J fires, ♥Q's rung arrives) — the only coupling
  the ceiling allows is monotone enablement, never foreclosure.
* **V5** the B2 twin-kings fork family (common material, consumed)
  — the intra-state refuter: at every state of the family at most
  one twin licenses; the canon wings split; the wing pull-home
  fires; every scaffold choice re-saturates to the same wing.
* **V6-V9** negative controls — unlicensable shapes never
  register: under-covered twins (the cargo corner), waste-resident
  and stock-resident mates, both-bare non-kings (the seat physics
  bar), the hidden-under reveal bar.

House discipline: this file is EVIDENCE, not theorems — nothing
here is imported by the library; state-equality verdicts ride a
probe-local `DecidableEq` bridge (the dedup-marked 14-field shape
used by the witness archives and the sibling probes).  The three
census theorems at the bottom (twin fixed-point-freeness, the
emptiness core, the Bool bridge) are the systematic half and are
#print-axioms-audited in-file. -/
/-! ## Kit
-/


/-- The state-equality bridge (probe-local re-derivation of the
dedup-marked 14-field shape; the library's own copy is private in
`Orig/Canonical.lean`). -/
private def v3DecSt (s t : State) : Decidable (s = t) :=
  decidable_of_decidable_of_iff (p :=
    (s.found .spade = t.found .spade ∧ s.found .heart = t.found .heart ∧
      s.found .diamond = t.found .diamond ∧ s.found .club = t.found .club ∧
      s.piles .p0 = t.piles .p0 ∧ s.piles .p1 = t.piles .p1 ∧
      s.piles .p2 = t.piles .p2 ∧ s.piles .p3 = t.piles .p3 ∧
      s.piles .p4 = t.piles .p4 ∧ s.piles .p5 = t.piles .p5 ∧
      s.piles .p6 = t.piles .p6 ∧
      s.stock = t.stock ∧ s.waste = t.waste ∧ s.drawStep = t.drawStep))
    (by
      constructor
      · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
        apply State.ext
        · funext σ; cases σ <;> assumption
        · funext a; cases a <;> assumption
        · assumption
        · assumption
        · assumption
      · rintro rfl
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

local instance : DecidableEq State := fun s t => v3DecSt s t

/-- The WF check, as an evaluable Bool mirror (the dedup-marked
four-conjunct shape; every crafted state partitions the full deck). -/
def v3WfB (st : State) : Bool :=
  Suit.all.all (fun s => decide (s.upCards.take (st.found s).length == st.found s)) &&
  Anchor.all.all (fun a => runOK (st.piles a).faceUp) &&
  Card.universe.all (fun c => decide (st.cardCount c == 1)) &&
  decide (0 < st.drawStep)


/-- The stock as the deck minus the excluded cards (seated or
founded) — the census-clean mover (the exchlaw lesson: the
foundation cards join the exclusion list or the cell fails its own
WF gate). -/
def v3Stock (exclude : List Card) : List Card :=
  Card.universe.filter fun c => decide (c ∉ exclude)

/-- The licensed-raise card list at `st`. -/
def v3Lic (st : State) : List Card :=
  Card.universe.filter (canRaiseB st)

/-- The registered twin-candidate list at `st`: cards whose whole
twin pair holds the license (the TwinContended first conjunct). -/
def v3TwinCand (st : State) : List Card :=
  Card.universe.filter (fun c => canRaiseB st c && canRaiseB st c.twin)

/-- The census reading of one license death: the landed state of
`raiser`'s licensed lift, `none`-safe (at licensed cells the lift
always fires). -/
def v3ForecloseB (st : State) (raiser twin : Card) : Bool :=
  match raise st raiser with
  | none => false
  | some s' => !canRaiseB s' twin

/-- THE CENSUS Bool, the pinned FORECLOSE read decide-graded: both
twins licensed at `st`, and stacking either forecloses the other. -/
def v3TwinContendedB (st : State) (c : Card) : Bool :=
  canRaiseB st c && canRaiseB st c.twin &&
    (v3ForecloseB st c c.twin || v3ForecloseB st c.twin c)

/-- The fired state of `c`'s lift (probe helper; the `st` fallback
branch is dead at licensed cells). -/
def v3Fired (st : State) (c : Card) : State :=
  match raise st c with
  | some s' => s'
  | none => st

/-- The MONOTONE permission census: raising `c` kills no other
license in the whole universe (the banked `canRaise_lifted` row,
decided). -/
def v3LicMonotone (st : State) (c : Card) : Bool :=
  Card.universe.all (fun x =>
    decide (x = c) || !(canRaiseB st x) || canRaiseB (v3Fired st c) x)

/-- The whole pull menu: every `foundToTab` command the move
alphabet can name. -/
def v3PullMenu : List Move :=
  Card.universe.flatMap fun c =>
    (Anchor.all.map fun a => Move.foundToTab c (Sum.inl a)) ++
    (Card.universe.map fun z => Move.foundToTab c (Sum.inr z))

/-- The licensed `foundToTab` pulls at `st` (the scaffold's menu):
every legal pull-back from the foundations. -/
def v3PullsAt (st : State) : List State :=
  (v3PullMenu).filterMap (fun m => st.step m)


/-- The fired-selected reader. -/
theorem v3ForecloseB_fired {st : State} {r tw : Card} {s' : State}
    (h : raise st r = some s') : v3ForecloseB st r tw = !canRaiseB s' tw := by
  show (match raise st r with
    | none => false
    | some s'' => !canRaiseB s'' tw) = _
  rw [h]

theorem v3ForecloseB_none {st : State} {r tw : Card} (h : raise st r = none) :
    v3ForecloseB st r tw = false := by
  show (match raise st r with
    | none => false
    | some s'' => !canRaiseB s'' tw) = _
  rw [h]

/-! ## The census theorems — the systematic half, prove-grade -/


/-- A card is never its own twin (the pair's two seats are always
two seats: spade pairs with club, heart with diamond). -/
theorem v3Card_twin_ne (c : Card) : c.twin ≠ c := by
  intro h
  have hs : c.suit.twin = c.suit := by
    have h1 : c.twin.suit = c.suit := by rw [h]
    rw [show c.twin.suit = c.suit.twin from rfl] at h1
    exact h1
  exact Suit.twin_ne c.suit hs

/-- Twinning is an involution on cards. -/
theorem v3Card_twin_twin (c : Card) : c.twin.twin = c := by
  cases c
  simp [Card.twin, Suit.twin_twin]

/-- THE EMPTINESS CORE: at a `WF` state, if both twins hold the
license and `c`'s lift fires, the twin's license survives the
landing — the zone-disjointness of the license reads (own rung,
own seat) and of the lift writes (own suit foundation, own pile).
This is the banked monotone-stackability row `canRaise_lifted`,
instantiated at the twin seats. -/
theorem v3twin_raise_independent {st : State} {c : Card} {s' : State}
    (hwf : st.WF) (hc : CanRaise st c) (ht : CanRaise st c.twin)
    (hstep : State.step st (Move.tabToFound c) = some s') :
    CanRaise s' c.twin :=
  canRaise_lifted hwf ht hc (v3Card_twin_ne c) hstep

/-- The census predicate, Prop form.  **THE FORECLOSE READ, pinned
(see the file header): LICENSE-DEATH** — the landed state of either
twin's licensed raise forecloses the other's license.  The raw
stackability, final-divergence and undo-death alternates are
struck at the cells below. -/
def TwinContended (st : State) (c : Card) : Prop :=
  CanRaise st c ∧ CanRaise st c.twin ∧
    ((∃ s', State.step st (Move.tabToFound c) = some s' ∧ ¬ CanRaise s' c.twin) ∨
      (∃ s', State.step st (Move.tabToFound c.twin) = some s' ∧ ¬ CanRaise s' c))

/-- THE CENSUS VERDICT (theorem grade): `TwinContended` is EMPTY
at `WF` — no state ever shows both twins licensed with stacking
either foreclosing the other. -/
theorem v3TwinContended_empty_at_wf {st : State} {c : Card}
    (hwf : st.WF) (h : TwinContended st c) : False := by
  obtain ⟨hc, ht, hfore | hfore⟩ := h
  · obtain ⟨s', hstep, hnot⟩ := hfore
    exact hnot (v3twin_raise_independent hwf hc ht hstep)
  · obtain ⟨s', hstep, hnot⟩ := hfore
    have hc' : CanRaise st c.twin.twin := by rw [v3Card_twin_twin]; exact hc
    have hsurv := v3twin_raise_independent hwf ht hc' hstep
    rw [v3Card_twin_twin] at hsurv
    exact hnot hsurv

/-- The Bool bridge: the decide-graded census speaks the Prop. -/
theorem v3TwinContendedB_true_iff (st : State) (c : Card) :
    v3TwinContendedB st c = true ↔ TwinContended st c := by
  constructor
  · intro h
    rw [v3TwinContendedB, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨hcB, htB⟩, hfore⟩ := h
    have hc : CanRaise st c := canRaiseB_true_iff.1 hcB
    have ht : CanRaise st c.twin := canRaiseB_true_iff.1 htB
    obtain ⟨s1, h1⟩ := raise_eq_some_of_canRaise st hc
    obtain ⟨s2, h2⟩ := raise_eq_some_of_canRaise st ht
    refine ⟨hc, ht, ?_⟩
    rw [Bool.or_eq_true] at hfore
    rcases hfore with hl | hr
    · rw [v3ForecloseB_fired h1] at hl
      have : canRaiseB s1 c.twin = false := by
        cases hb : canRaiseB s1 c.twin with
        | true => rw [hb] at hl; simp at hl
        | false => rfl
      left
      refine ⟨s1, h1, ?_⟩
      intro hlic
      rw [canRaiseB_true_iff.2 hlic] at this
      exact absurd this (by simp)
    · rw [v3ForecloseB_fired h2] at hr
      have : canRaiseB s2 c = false := by
        cases hb : canRaiseB s2 c with
        | true => rw [hb] at hr; simp at hr
        | false => rfl
      right
      refine ⟨s2, h2, ?_⟩
      intro hlic
      rw [canRaiseB_true_iff.2 hlic] at this
      exact absurd this (by simp)
  · rintro ⟨hc, ht, (⟨s1, h1, hnot1⟩ | ⟨s2, h2, hnot2⟩)⟩
    · have hb1 : canRaiseB s1 c.twin = false := by
        cases hb : canRaiseB s1 c.twin with
        | true => exact absurd (canRaiseB_true_iff.1 hb) hnot1
        | false => rfl
      rw [v3TwinContendedB, canRaiseB_true_iff.2 hc, canRaiseB_true_iff.2 ht,
        Bool.true_and, Bool.true_and, Bool.or_eq_true]
      left
      rw [v3ForecloseB_fired h1, hb1]
      rfl
    · have hb2 : canRaiseB s2 c = false := by
        cases hb : canRaiseB s2 c with
        | true => exact absurd (canRaiseB_true_iff.1 hb) hnot2
        | false => rfl
      rw [v3TwinContendedB, canRaiseB_true_iff.2 hc, canRaiseB_true_iff.2 ht,
        Bool.true_and, Bool.true_and, Bool.or_eq_true]
      right
      rw [v3ForecloseB_fired h2, hb2]
      rfl

/-! ## The card constants -/
def v3HK : Card := ⟨Suit.heart, Rank.king⟩
def v3DK : Card := ⟨Suit.diamond, Rank.king⟩
def v3HQ : Card := ⟨Suit.heart, Rank.queen⟩
def v3DQ : Card := ⟨Suit.diamond, Rank.queen⟩
def v3HJ : Card := ⟨Suit.heart, Rank.jack⟩
def v3DJ : Card := ⟨Suit.diamond, Rank.jack⟩
def v3SK : Card := ⟨Suit.spade, Rank.king⟩
def v3CK : Card := ⟨Suit.club, Rank.king⟩
def v3SQ : Card := ⟨Suit.spade, Rank.queen⟩
def v3CQ : Card := ⟨Suit.club, Rank.queen⟩
def v3S2 : Card := ⟨Suit.spade, Rank.two⟩

/-! ## Family V1 — both-bare twin kings (the freeness suggestion verified) -/


/-- Hearts and diamonds climbed A..Q; both rung-ready kings stand
BARE on their own empty anchors.  Both licensed; both raise. -/
def v3Bare : State where
  found := fun s =>
    match s with
    | .heart => Suit.heart.upCards.take 12
    | .diamond => Suit.diamond.upCards.take 12
    | _ => []
  piles := fun a =>
    match a with
    | .p1 => ⟨[], [v3HK]⟩
    | .p5 => ⟨[], [v3DK]⟩
    | _ => ⟨[], []⟩
  stock := v3Stock (Suit.heart.upCards ++ Suit.diamond.upCards)
  waste := []
  drawStep := 1

/-- V1 gates: WF, the pair census (exactly the two kings licensed,
exactly the two kings registered as candidates), contention DEAD,
both lifts fire and each keeps the other licensed (the monotone
permission census), both orders land at one state — canon —
which saturates BOTH kings simultaneously (the freeness reading:
independence, no foreclosure), and the canon is twin-blind at the
cell. -/
def v3GateV1 : Bool :=
  v3WfB v3Bare &&
  decide ((v3Lic v3Bare).length = 2) &&
  decide ((v3TwinCand v3Bare).length = 2) &&
  decide ((v3Lic v3Bare).all (fun c => !(v3TwinContendedB v3Bare c))) &&
  (canRaiseB v3Bare v3HK && canRaiseB v3Bare v3DK) &&
  v3LicMonotone v3Bare v3HK && v3LicMonotone v3Bare v3DK &&
  -- both orders of the twin pair land at ONE state
  decide (v3Fired (v3Fired v3Bare v3HK) v3DK = v3Fired (v3Fired v3Bare v3DK) v3HK) &&
  decide ((v3Fired (v3Fired v3Bare v3HK) v3DK).found .heart = Suit.heart.upCards) &&
  decide ((v3Fired (v3Fired v3Bare v3HK) v3DK).found .diamond = Suit.diamond.upCards) &&
  -- canon consumes BOTH twins from either order (the simultaneous datum)
  decide (canon v3Bare = v3Fired (v3Fired v3Bare v3HK) v3DK) &&
  decide (canon v3Bare = v3Fired (v3Fired v3Bare v3DK) v3HK) &&
  decide ((canon v3Bare).piles .p1 = ⟨[], []⟩) &&
  decide ((canon v3Bare).piles .p5 = ⟨[], []⟩) &&
  -- twin-blindness at the cell (the banked canon_twinMap, decided)
  decide (canon v3Bare.twinMap = (canon v3Bare).twinMap)

/-! ## Family V2 — both under-seat twin queens on conjugate bases -/


/-- Hearts and diamonds climbed A..J; the rung-ready queens sit
UNDER SEAT on twin bases (♣K / ♠K — the bases are themselves twins,
the §1.8 crossed-pair geometry read at licensed seats; anatomically
a twin pair cannot sit mixed: kings sit under nothing, so a
licensed twin pair is either both-bare (kings) or both-under
(non-kings)). -/
def v3Under : State where
  found := fun s =>
    match s with
    | .heart => Suit.heart.upCards.take 11
    | .diamond => Suit.diamond.upCards.take 11
    | _ => []
  piles := fun a =>
    match a with
    | .p1 => ⟨[], [v3CK, v3HQ]⟩
    | .p5 => ⟨[], [v3SK, v3DQ]⟩
    | _ => ⟨[], []⟩
  stock := v3Stock (Suit.heart.upCards.take 11 ++ Suit.diamond.upCards.take 11 ++
    [v3CK, v3SK, v3HQ, v3DQ])
  waste := []
  drawStep := 1

/-- V2 gates: the conjugate-base interlock still couples nothing —
both queens licensed, contention dead, orders converge at canon,
twin-blindness holds (twinMap swaps the twin-seated piles), and
the UNDO-death alternate is struck: after the double saturation
BOTH queens' `foundToTab` returns fire onto their exposed bases. -/
def v3GateV2 : Bool :=
  v3WfB v3Under &&
  decide ((v3Lic v3Under).length = 2) &&
  (canRaiseB v3Under v3HQ && canRaiseB v3Under v3DQ) &&
  v3LicMonotone v3Under v3HQ && v3LicMonotone v3Under v3DQ &&
  decide ((v3Lic v3Under).all (fun c => !(v3TwinContendedB v3Under c))) &&
  -- both orders land at canon
  decide (v3Fired (v3Fired v3Under v3HQ) v3DQ = v3Fired (v3Fired v3Under v3DQ) v3HQ) &&
  decide (canon v3Under = v3Fired (v3Fired v3Under v3HQ) v3DQ) &&
  decide ((canon v3Under).found .heart = Suit.heart.upCards.take 12) &&
  decide ((canon v3Under).found .diamond = Suit.diamond.upCards.take 12) &&
  -- the bases stay seated, bare, unlicensed (black suits never climb)
  decide ((canon v3Under).piles .p1 = ⟨[], [v3CK]⟩) &&
  decide ((canon v3Under).piles .p5 = ⟨[], [v3SK]⟩) &&
  -- UNDO SURVIVAL after the double saturation (the undo-death
  -- alternate struck): both queens pull off the saturated
  -- foundations onto either exposed base (♣K or ♠K — two targets
  -- each, four pulls), and every pulled excursion re-saturates
  -- home (the round trip is the undo family's content)
  decide ((v3PullsAt (canon v3Under)).length = 4) &&
  decide ((v3PullsAt (canon v3Under)).all (fun s => canon s = canon v3Under)) &&
  -- twin-blindness (twinMap swaps the twin-seated piles)
  decide (canon v3Under.twinMap = (canon v3Under).twinMap)

/-! ## Family V3 — the mixed-seat census point -/


/-- A bare licensed king and an under-seat licensed queen of the
other color coexist; the king's twin (♦K) is STOCK-resident (the
V6 stock control doubles here), and the queen's twin (♥Q) likewise.
A licensed twin pair cannot sit mixed seat types — kings sit
under nothing — so the cross-type coexistence carries the census
without ever licensing a pair. -/
def v3Mixed : State where
  found := fun s =>
    match s with
    | .heart => Suit.heart.upCards.take 12
    | .diamond => Suit.diamond.upCards.take 11
    | _ => []
  piles := fun a =>
    match a with
    | .p1 => ⟨[], [v3HK]⟩
    | .p5 => ⟨[], [v3SK, v3DQ]⟩
    | _ => ⟨[], []⟩
  stock := v3Stock (Suit.heart.upCards.take 12 ++ Suit.diamond.upCards.take 11 ++
    [v3HK, v3SK, v3DQ])
  waste := []
  drawStep := 1

/-- V3 gates: WF, exactly two licensed (the bare king and the
under-seat queen — no twin pair registers: ♦K and ♥Q are
stock-resident, never piled), contention dead, monotone
permissions through both fires, and the exhaustion data: the canon
saturates hearts to the king and diamonds to the queen, the stock
residents untouched by the canonicalizer. -/
def v3GateV3 : Bool :=
  v3WfB v3Mixed &&
  decide ((v3Lic v3Mixed).length = 2) &&
  (canRaiseB v3Mixed v3HK && canRaiseB v3Mixed v3DQ) &&
  decide (!(canRaiseB v3Mixed v3DK) && !(canRaiseB v3Mixed v3HQ)) &&
  decide ((v3Lic v3Mixed).all (fun c => !(v3TwinContendedB v3Mixed c))) &&
  v3LicMonotone v3Mixed v3HK && v3LicMonotone v3Mixed v3DQ &&
  decide (canon v3Mixed = v3Fired (v3Fired v3Mixed v3HK) v3DQ) &&
  decide (canon v3Mixed = v3Fired (v3Fired v3Mixed v3DQ) v3HK) &&
  -- the stock residents stay stock-resident through canonicalization
  decide ((canon v3Mixed).stock = v3Mixed.stock)

/-! ## Family V4 — the mediation candidate that only ever ENABLES -/


/-- Hearts and diamonds climbed A..10; the rungs-ready jacks sit
under seat on twin bases, and ♥Q sits under seat on ♣K one rung
short.  Raising ♥J lights ♥Q's license — the ENABLEMENT mediation:
the only coupling a licensed lift can induce anywhere is MORE
license, never less. -/
def v3Chain : State where
  found := fun s =>
    match s with
    | .heart => Suit.heart.upCards.take 10
    | .diamond => Suit.diamond.upCards.take 10
    | _ => []
  piles := fun a =>
    match a with
    | .p1 => ⟨[], [v3CQ, v3HJ]⟩
    | .p5 => ⟨[], [v3SQ, v3DJ]⟩
    | .p3 => ⟨[], [v3CK, v3HQ]⟩
    | _ => ⟨[], []⟩
  stock := v3Stock (Suit.heart.upCards.take 10 ++ Suit.diamond.upCards.take 10 ++
    [v3CQ, v3SQ, v3HJ, v3DJ, v3CK, v3HQ])
  waste := []
  drawStep := 1

/-- V4 gates: WF; the two jacks licensed, ♦J's license rides
♥J's lift (independence); the enablement fires (♥Q licenses exactly
when hearts reach J) and ♦J survives it; contention dead
everywhere through the chain; the canon walks the enabled ladder
and saturates hearts A..Q, diamonds A..J; nothing else was ever
licensed (♣Q, ♠Q, ♣K stay seated and unlicensed). -/
def v3GateV4 : Bool :=
  v3WfB v3Chain &&
  decide ((v3Lic v3Chain).length = 2) &&
  (canRaiseB v3Chain v3HJ && canRaiseB v3Chain v3DJ) &&
  !(canRaiseB v3Chain v3HQ) &&
  -- independence of the pair under ♥J's lift, and the enablement datum
  v3LicMonotone v3Chain v3HJ &&
  canRaiseB (v3Fired v3Chain v3HJ) v3HQ &&
  canRaiseB (v3Fired v3Chain v3HJ) v3DJ &&
  decide ((v3Lic (v3Fired v3Chain v3HJ)).length = 2) &&
  -- contention dead everywhere along the chain
  decide ((v3Lic v3Chain).all (fun c => !(v3TwinContendedB v3Chain c))) &&
  decide ((v3Lic (v3Fired v3Chain v3HJ)).all
    (fun c => !(v3TwinContendedB (v3Fired v3Chain v3HJ) c))) &&
  decide ((v3Lic (canon v3Chain)).all
    (fun c => !(v3TwinContendedB (canon v3Chain) c))) &&
  -- the saturated end of the chain
  decide ((canon v3Chain).found .heart = Suit.heart.upCards.take 12) &&
  decide ((canon v3Chain).found .diamond = Suit.diamond.upCards.take 11) &&
  decide ((v3Lic (canon v3Chain)).length = 0) &&
  decide (canon v3Chain.twinMap = (canon v3Chain).twinMap)

/-! ## Family V5 — the B2 twin-kings fork family (common material,
consumed from the exchlaw battery's committed verdicts) -/


/-- The worried-king fork cell, exchlaw B2 verbatim: hearts and
diamonds climbed A..Q; ♥K BARE on p1, ♦K under ♣Q on p5.  In this
single state only ONE twin is licensed — the TwinContended first
conjunct dies here; the fork lives ACROSS the twin-exchange mates. -/
def v3Fork : State where
  found := fun s =>
    match s with
    | .heart => Suit.heart.upCards.take 12
    | .diamond => Suit.diamond.upCards.take 12
    | _ => []
  piles := fun a =>
    match a with
    | .p1 => ⟨[], [v3HK]⟩
    | .p5 => ⟨[], [v3DK, v3CQ]⟩
    | _ => ⟨[], []⟩
  stock := v3Stock (Suit.heart.upCards.take 12 ++ Suit.diamond.upCards.take 12 ++
    [v3HK, v3DK, v3CQ])
  waste := []
  drawStep := 1

/-- The exchange-mate (the concern's steering slide realized as
the one-move noreveal `tabToTab`): the fork's other face. -/
def v3ForkX : State where
  found := fun s =>
    match s with
    | .heart => Suit.heart.upCards.take 12
    | .diamond => Suit.diamond.upCards.take 12
    | _ => []
  piles := fun a =>
    match a with
    | .p1 => ⟨[], [v3HK, v3CQ]⟩
    | .p5 => ⟨[], [v3DK]⟩
    | _ => ⟨[], []⟩
  stock := v3Stock (Suit.heart.upCards.take 12 ++ Suit.diamond.upCards.take 12 ++
    [v3HK, v3DK, v3CQ])
  waste := []
  drawStep := 1

/-- The tombstone census: no card in the universe registers
contention at `st`. -/
def v3FamilyClean (st : State) : Bool :=
  Card.universe.all (fun c => !(v3TwinContendedB st c))

/-- V5 gates: the intra-state refuter, consumed and re-decided in
the census language.  Every single state of the family licenses at
most ONE twin; the whole universe shows no contention; the canon
wings split foundations 13/12 vs 12/13 (the fork the card names);
the steering slide and the wing pull-home fire step-exactly; every
licensed scaffold pull from a wing re-saturates to the SAME wing
(the scaffold choices converge — there is no hard contention at a
wing: the founded twin always pulls home); twin-blindness holds on
every face (the conjugate route agrees with the committed route),
and the wing itself saturates to Final. -/
def v3GateV5 : Bool :=
  v3WfB v3Fork && v3WfB v3ForkX && v3FamilyClean v3Fork && v3FamilyClean v3ForkX &&
  -- exactly one twin licensed at each face of the fork
  (canRaiseB v3Fork v3HK && !(canRaiseB v3Fork v3DK)) &&
  (!(canRaiseB v3ForkX v3HK) && canRaiseB v3ForkX v3DK) &&
  decide ((v3Lic v3Fork).length = 1) && decide ((v3Lic v3ForkX).length = 1) &&
  -- the steering slide, step-exact both directions (the exchange
  -- realized as a noreveal relocation — the exchlaw datum)
  decide (v3Fork.step (Move.tabToTab v3CQ (Sum.inr v3HK)) = some v3ForkX) &&
  decide (v3ForkX.step (Move.tabToTab v3CQ (Sum.inr v3DK)) = some v3Fork) &&
  -- the canon wings split (the fork): hearts 13 vs diamonds 13
  decide ((canon v3Fork).found .heart = Suit.heart.upCards) &&
  decide ((canon v3Fork).found .diamond = Suit.diamond.upCards.take 12) &&
  decide ((canon v3ForkX).found .diamond = Suit.diamond.upCards) &&
  decide ((canon v3ForkX).found .heart = Suit.heart.upCards.take 12) &&
  decide ((canon v3Fork ≠ canon v3ForkX)) &&
  -- the wings are Final (saturation spent) and contention-clean
  decide ((v3Lic (canon v3Fork)).length = 0) &&
  decide ((v3Lic (canon v3ForkX)).length = 0) &&
  v3FamilyClean (canon v3Fork) && v3FamilyClean (canon v3ForkX) &&
  -- the A2 pull-highway (the unblocker): the wing pulls its
  -- founded twin home, step-exact, THE original state
  decide ((canon v3Fork).step (Move.foundToTab v3HK (Sum.inl Anchor.p1)) = some v3Fork) &&
  decide ((canon v3ForkX).step (Move.foundToTab v3DK (Sum.inl Anchor.p5)) = some v3ForkX) &&
  -- scaffold choices are plenty and ALL converge home: every
  -- licensed pull from the wing re-saturates to the same wing
  -- (the pull menu: the founded king onto the six empty anchors;
  -- kings sit under nothing, so no seat target exists here)
  decide ((v3PullsAt (canon v3Fork)).length = 6) &&
  decide ((v3PullsAt (canon v3Fork)).all (fun s => canon s = canon v3Fork)) &&
  decide ((v3PullsAt (canon v3ForkX)).length = 6) &&
  decide ((v3PullsAt (canon v3ForkX)).all (fun s => canon s = canon v3ForkX)) &&
  -- twin-blindness at every face (conjugate routes agree)
  decide (canon v3Fork.twinMap = (canon v3Fork).twinMap) &&
  decide (canon v3ForkX.twinMap = (canon v3ForkX).twinMap)

/-! ## Families V6–V9 — negative controls, unlicensable shapes -/


/-- V6a, the cargo corner (§1.8's premise family): both twin kings
CARRY twin cargos (♣Q / ♠Q, the crossed pair) — covered tops license
nothing, and no black card is ever rung-ready here. -/
def v3Cargo : State where
  found := fun s =>
    match s with
    | .heart => Suit.heart.upCards.take 12
    | .diamond => Suit.diamond.upCards.take 12
    | _ => []
  piles := fun a =>
    match a with
    | .p1 => ⟨[], [v3HK, v3CQ]⟩
    | .p5 => ⟨[], [v3DK, v3SQ]⟩
    | _ => ⟨[], []⟩
  stock := v3Stock (Suit.heart.upCards ++ Suit.diamond.upCards ++ [v3CQ, v3SQ])
  waste := []
  drawStep := 1

/-- V6b, the waste-resident mate: ♥K licensed bare, ♦K resident in
the WASTE — no pile search ever finds it. -/
def v3WasteRes : State where
  found := fun s =>
    match s with
    | .heart => Suit.heart.upCards.take 12
    | .diamond => Suit.diamond.upCards.take 12
    | _ => []
  piles := fun a =>
    match a with
    | .p1 => ⟨[], [v3HK]⟩
    | _ => ⟨[], []⟩
  stock := v3Stock (Suit.heart.upCards ++ Suit.diamond.upCards)
  waste := [v3DK]
  drawStep := 1

/-- V6c, the both-bare NON-king bar: two rung-ready bare queens.
The seat physics refuses them (the emptied seat readmits only a
king) — §3.0's OUT-list, decided.  -/
def v3BareNonKing : State where
  found := fun s =>
    match s with
    | .heart => Suit.heart.upCards.take 11
    | .diamond => Suit.diamond.upCards.take 11
    | _ => []
  piles := fun a =>
    match a with
    | .p1 => ⟨[], [v3HQ]⟩
    | .p5 => ⟨[], [v3DQ]⟩
    | _ => ⟨[], []⟩
  stock := v3Stock (Suit.heart.upCards.take 11 ++ Suit.diamond.upCards.take 11 ++
    [v3HQ, v3DQ])
  waste := []
  drawStep := 1

/-- V6d, the reveal bar: a rung-ready bare king pinned over a
HIDDEN card — lifting it would flip the reveal (a commitment);
the license demands the hidden stack empty. -/
def v3RevealBar : State where
  found := fun s =>
    match s with
    | .heart => Suit.heart.upCards.take 12
    | .diamond => Suit.diamond.upCards.take 12
    | _ => []
  piles := fun a =>
    match a with
    | .p1 => ⟨[v3S2], [v3HK]⟩
    | .p5 => ⟨[], [v3DK]⟩
    | _ => ⟨[], []⟩
  stock := v3Stock (Suit.heart.upCards ++ Suit.diamond.upCards ++ [v3S2])
  waste := []
  drawStep := 1

/-- Negative-control gates: every shape is WF, and NONE ever
registers a contented pair anywhere in the universe; the covered
cargo cell licenses nothing at all; the waste-resident mate is
never licensed (though its bare twin is); the bare queens license
nothing (the seat-physics bar); the hidden-under king is refused
though rung-ready while its free twin licenses. -/
def v3GateV6 : Bool :=
  v3WfB v3Cargo && v3FamilyClean v3Cargo && decide ((v3Lic v3Cargo).length = 0) &&
  v3WfB v3WasteRes && v3FamilyClean v3WasteRes &&
  (canRaiseB v3WasteRes v3HK && !(canRaiseB v3WasteRes v3DK)) &&
  v3WfB v3BareNonKing && v3FamilyClean v3BareNonKing &&
  decide ((v3Lic v3BareNonKing).length = 0) &&
  v3WfB v3RevealBar && v3FamilyClean v3RevealBar &&
  (!(canRaiseB v3RevealBar v3HK) && canRaiseB v3RevealBar v3DK)

/-! ## The verdicts -/


/-- All gates, as the recorded census battery. -/
def v3AllGates : Bool :=
  v3GateV1 && v3GateV2 && v3GateV3 && v3GateV4 && v3GateV5 && v3GateV6

-- The census numbers the verdicts pin (printed for the ledger; the
-- gates above carry the load-bearing checks):
#eval v3GateV1 -- expect true: both-bare twin kings, independent and converging
#eval v3GateV2 -- expect true: under-seat twin queens on conjugate bases
#eval v3GateV3 -- expect true: the mixed-seat census point
#eval v3GateV4 -- expect true: the enablement-only mediation
#eval v3GateV5 -- expect true: the cross-mate fork family
#eval v3GateV6 -- expect true: the negative controls
#eval (v3Lic v3Bare).length -- expect 2: both bare kings licensed
#eval (v3TwinCand v3Bare).length -- expect 2: the one twin pair, both members
#eval (v3Lic v3Under).length -- expect 2: both under-seat queens licensed
#eval (v3Lic v3Chain).length -- expect 2: the jacks, pre-enablement
#eval (v3Lic (v3Fired v3Chain v3HJ)).length -- expect 2: ♥Q enabled, ♦J kept
#eval (v3Lic v3Fork).length -- expect 1: ♥K only — ♦K covered
#eval (v3Lic v3ForkX).length -- expect 1: ♦K only — ♥K covered
#eval (v3Lic (canon v3Fork)).length -- expect 0: the wing is Final
#eval (v3PullsAt (canon v3Fork)).length -- expect 6: every empty anchor, no seat fits a king
#eval ((canon v3Fork).found .heart).length -- expect 13: the heart wing
#eval ((canon v3ForkX).found .diamond).length -- expect 13: the diamond wing
#eval (v3Lic v3Cargo).length -- expect 0: covered tops never license
#eval (v3Lic v3BareNonKing).length -- expect 0: bare non-kings barred

#print axioms v3Card_twin_ne
#print axioms v3Card_twin_twin
#print axioms v3twin_raise_independent
#print axioms v3TwinContended_empty_at_wf
#print axioms v3TwinContendedB_true_iff

#eval! do
  if v3AllGates then
    IO.println "CANONV3: ALL GATES HOLD — THE GATING CENSUS RETURNS EMPTY —"
    IO.println "TwinContended is EMPTY at WF under the pinned FORECLOSE reading"
    IO.println "(LICENSE-DEATH), and the alternates (raw-stackability death, final"
    IO.println "divergence, undo death) are struck at the cells. Both-bare twin kings:"
    IO.println "both licensed, both fire, both orders land at canon — the freeness"
    IO.println "suggestion verified. Both under-seat twin queens on conjugate bases:"
    IO.println "independence holds; each saturated queen pulls back onto either"
    IO.println "exposed base and the excursion re-saturates home (the round trip)."
    IO.println "The enablement cell couples by lighting MORE license and never less."
    IO.println "The B2 twin-kings family (consumed): every single state licenses at"
    IO.println "most ONE twin; the fork is CROSS-MATE (across the exchange slide),"
    IO.println "the canon wings split 13/12 vs 12/13, and every licensed pull from a"
    IO.println "wing re-saturates home — scaffold choices converge, no hard contention"
    IO.println "anywhere in the family; canon is twin-blind on every face. Negative"
    IO.println "controls: covered cargo, waste-resident mates, bare non-kings, and"
    IO.println "the hidden-under reveal bar never license a pair, never a contention."
    IO.println ""
    IO.println "VERDICT BRANCH (b): the V3 scaffold-pull rule RETIRES as unneeded —"
    IO.println "forks are exchange-steered, commit-side, priced by the A2 witness at"
    IO.println "tip level; the skeleton stays ledgered as dormant design (FUTURES §11)."
  else
    throw (IO.userError "CANONV3: A GATE FAILED — see the numbers above")
