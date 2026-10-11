import Orig.Canonical
import Orig.CanV3
import Orig.TwinExchange

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

/-! ## Landing 3 — `pair_neighborhood_cases` — the lattice header, the slice rows, the cascade rows, the closing containment corollary

The verdict restructuring (the coordinator's landing-3 call): the
census families reorganized from witness list to LEMMA-PER-ROW plus
the LATTICE HEADER that turns "the case table exhausts all cases"
into a proved classification.

**THE LATTICE HEADER.**  (1) The POSITION-CLASSIFICATION: at a WF
state every face-up twin member sits in EXACTLY ONE of three
position states — BARE (pile-top, run singleton), UNDER (pile-top
with run content beneath), COVERED (face-up under cargo, hence not
any pile's top) — `pnPosTrich` below.  The pair reads the product:
nine lattice cells.

(2) THE SLICE ROWS: the LICENSED slice is {bare, under}².  A
licensed pair is a pair of pile tops (`pnCoveredNotLicensed`:
covered ⇒ unlicensed), so the covered slice carries AT MOST ONE
licensed twin per state — the fork is structurally CROSS-MATE.  And
the licensed slice itself collapses to TWO cells: rank forces the
seat type — kings sit under NOTHING (the sit arithmetic has no
rank 13+1), so a licensed KING pair is BOTH-BARE (`pnLicKingBare`),
and a licensed NON-KING pair is BOTH-UNDER (`pnLicNonKingUnder`,
twins share rank) — `pnLicPairSlice`.  In every licensed cell both
twins raise, and lifts-only-light (landing 1's V4 + the banked
`canRaise_lifted`) gives independence across the whole slice in one
stroke.

(3) THE RANK-ENDPOINT DEGENERACY ROWS (free by deck arithmetic):
KINGS — under is impossible, king pairs live in {bare, covered}
only, and the cover-cargo class of a covered king is EXACTLY rank
queen (`pnKingSlider` + `pnCoveredKingQueen`: the exchlaw
falsifier's ♣Q is not an accident, it is the whole class);  ACES —
covered is impossible (nothing is rank 0), ace twins are born
bare-or-under and are STRUCTURALLY INCAPABLE of hosting the fork:
the disease has a rank floor (`pnAceNoSlider` +
`pnCoveredAceAbsurd`).

(4) THE CARGO TRIAD closing the covered cells: every potential
slider of a host rank x is rank x-1 of the opposite color, and the
two such cards are THEMSELVES TWINS (`pnSliderPair` — same rank,
same color).  Each such cargo either (a) STACKS NOW — its rung
waits: the cascade row, it dissolves into the foundations and the
fork MERGES (the merge cell below); (b) stays PARKED — the slide
class, where the only fork lives, cross-mate, priced by the A2
pull-highway (the exchlaw standing fork, re-graded here); or (c)
is INERT — hidden/waste/stock, the landing-1 negatives.  Each
covered-cell row answers the post-cascade top slot as a FUNCTION OF
RUNG DELTAS — decided below per row (the ±1,±2 collapse around x).
-/

/-! ### The position kit and the lattice theorems -/


/-- Exactly one of three Booleans. -/
def pnExactlyOne (b1 b2 b3 : Bool) : Bool :=
  (b1 && !b2 && !b3) || (!b1 && b2 && !b3) || (!b1 && !b2 && b3)

/-- COVERED: face-up in some pile but not any pile's top (at WF:
cargo sits above). -/
def pnPosCovered (st : State) (c : Card) : Bool :=
  decide (st.pileOfTop c = none) && decide ((st.pileHolding c).isSome)

/-- BARE: a pile top whose face-up run is the singleton. -/
def pnPosBare (st : State) (c : Card) : Bool :=
  match st.pileOfTop c with
  | none => false
  | some a => decide ((st.piles a).faceUp = [c])

/-- UNDER: a pile top with run content beneath. -/
def pnPosUnder (st : State) (c : Card) : Bool :=
  match st.pileOfTop c with
  | none => false
  | some a => decide ((st.piles a).faceUp ≠ [c])

/-- THE POSITION-CLASSIFICATION LEMMA: at WF every face-up card is
in exactly one of the three position states. -/
theorem pnPosTrich (st : State) (hwf : st.WF) (c : Card)
    (hmem : ∃ a, c ∈ (st.piles a).faceUp) :
    pnExactlyOne (pnPosCovered st c) (pnPosBare st c) (pnPosUnder st c) = true := by
  obtain ⟨a, hm⟩ := hmem
  have hh : st.pileHolding c = some a := (pileHolding_eq_some_iff hwf).2 hm
  cases hpt : st.pileOfTop c with
  | none =>
      have hc : pnPosCovered st c = true := by simp [pnPosCovered, hpt, hh]
      have hb : pnPosBare st c = false := by simp [pnPosBare, hpt]
      have hu : pnPosUnder st c = false := by simp [pnPosUnder, hpt]
      rw [hc, hb, hu]
      rfl
  | some k =>
      have hc : pnPosCovered st c = false := by simp [pnPosCovered, hpt]
      rw [hc]
      cases hlist : (st.piles k).faceUp with
      | nil => exact absurd (by rw [hlist]) (pileOfTop_top hpt).1
      | cons x t =>
          cases t with
          | nil =>
              have hxc : x = c := by
                have hlast := (pileOfTop_top hpt).2
                rw [hlist] at hlast
                have hlr : lastOf [x] = some x := rfl
                rw [hlr] at hlast
                exact Option.some.inj hlast
              have hbare : pnPosBare st c = true := by
                simp [pnPosBare, hpt, hlist, hxc]
              have hunder : pnPosUnder st c = false := by
                simp [pnPosUnder, hpt, hlist, hxc]
              rw [hbare, hunder]; rfl
          | cons y t' =>
              have hsing : (st.piles k).faceUp ≠ [c] := by
                rw [hlist]; simp
              have hbare : pnPosBare st c = false := by
                simp [pnPosBare, hpt, hlist, hsing]
              have hunder : pnPosUnder st c = true := by
                simp [pnPosUnder, hpt, hlist, hsing]
              rw [hbare, hunder]; rfl

/-- A covered member cannot hold the license: covered means no
pile top, and every licensed card tops its search pile. -/
theorem pnCoveredNotLicensed {st : State} {c : Card}
    (h : pnPosCovered st c = true) (hlic : CanRaise st c) : False := by
  obtain ⟨hn, a, hp, hseat⟩ := hlic
  simp [pnPosCovered, hp] at h

/-- The covered slice carries at most one licensed twin: covering
one member already bars its license. -/
theorem pnCoveredPairAtMostOne {st : State} {c : Card}
    (h1 : pnPosCovered st c = true ∨ pnPosCovered st c.twin = true)
    (h2 : CanRaise st c ∧ CanRaise st c.twin) : False := by
  rcases h1 with h | h
  · exact pnCoveredNotLicensed h h2.1
  · exact pnCoveredNotLicensed h h2.2

/-! ### The seat arithmetic (bank-heads: chop_snoc, lastOf_chop,
runOK_snoc_sit, pileOfTop_top, pileOfTop_eq_some_iff, Rank rows) -/


/-- A licensed KING is BARE: no card sits under a king (the sit
arithmetic has no rank thirteen-plus-one), so the under-seat leg
of the license is unsatisfiable at WF. -/
theorem pnLicKingBare {st : State} {c : Card} {a : Anchor}
    (hwf : st.WF) (hlic : CanRaise st c) (hpt : st.pileOfTop c = some a)
    (hk : c.rank = Rank.king) :
    (st.piles a).faceUp = [c] ∧ (st.piles a).hidden = [] := by
  obtain ⟨hn, a', hp', hseat⟩ := hlic
  rw [hpt] at hp'
  injection hp' with ha
  subst ha
  have hlast := (pileOfTop_top hpt).2
  have hsplit : (st.piles a).faceUp = chop (st.piles a).faceUp ++ [c] :=
    lastOf_chop hlast
  have hrun : runOK (chop (st.piles a).faceUp ++ [c]) = true := by
    have h := hwf.2.1 a
    rw [hsplit] at h
    exact h
  have hchopnil : chop (st.piles a).faceUp = [] := by
    by_cases hchop : chop (st.piles a).faceUp = []
    · exact hchop
    · obtain ⟨z, -, hsit⟩ := runOK_snoc_sit (l := chop (st.piles a).faceUp) hchop hrun
      rw [canSitOn_eq] at hsit
      have hlt := Rank.toIdx_lt z.rank
      have hk12 : c.rank.toIdx = 12 := by rw [hk]; rfl
      omega
  refine ⟨by rw [hsplit, hchopnil]; rfl, ?_⟩
  rcases hseat with h1 | ⟨h2, h3⟩
  · rw [hchopnil] at h1
    exact absurd h1 (by simp)
  · exact h2

/-- A licensed NON-KING sits UNDER: the bare leg of the license is
the bare-KING leg only. -/
theorem pnLicNonKingUnder {st : State} {c : Card} {a : Anchor}
    (hlic : CanRaise st c) (hpt : st.pileOfTop c = some a)
    (hk : c.rank ≠ Rank.king) : chop (st.piles a).faceUp ≠ [] := by
  obtain ⟨hn, a', hp', hseat⟩ := hlic
  rw [hpt] at hp'
  injection hp' with ha
  subst ha
  rcases hseat with h1 | ⟨h2, h3⟩
  · exact h1
  · exact absurd h3 hk

/-- The licensed slice: a licensed twin pair is EXACTLY one of the
two lattice cells — BOTH-BARE (kings) or BOTH-UNDER (non-kings).
Twins share rank, so the nine-cell lattice's mixed licensed cells
are the VACUOUS cells. -/
theorem pnLicPairSlice {st : State} {c : Card} (hwf : st.WF)
    (hc : CanRaise st c) (ht : CanRaise st c.twin) :
    ∃ a b, st.pileOfTop c = some a ∧ st.pileOfTop c.twin = some b ∧
      ((c.rank = Rank.king ∧
          (st.piles a).faceUp = [c] ∧ (st.piles a).hidden = [] ∧
          (st.piles b).faceUp = [c.twin] ∧ (st.piles b).hidden = []) ∨
        (c.rank ≠ Rank.king ∧
          chop (st.piles a).faceUp ≠ [] ∧ chop (st.piles b).faceUp ≠ [])) := by
  obtain ⟨hn1, a, hpa, hs1⟩ := hc
  obtain ⟨hn2, b, hpb, hs2⟩ := ht
  have hc : CanRaise st c := ⟨hn1, a, hpa, hs1⟩
  have ht : CanRaise st c.twin := ⟨hn2, b, hpb, hs2⟩
  by_cases hk : c.rank = Rank.king
  · have hkr : c.twin.rank = Rank.king := by
      have htr : c.twin.rank = c.rank := rfl
      rw [htr, hk]
    obtain ⟨hf1, hh1⟩ := pnLicKingBare hwf hc hpa hk
    obtain ⟨hf2, hh2⟩ := pnLicKingBare hwf ht hpb hkr
    exact ⟨a, b, hpa, hpb, Or.inl ⟨hk, hf1, hh1, hf2, hh2⟩⟩
  · refine ⟨a, b, hpa, hpb, Or.inr ⟨hk, pnLicNonKingUnder hc hpa hk, ?_⟩⟩
    have htk : c.twin.rank ≠ Rank.king := by
      rw [show c.twin.rank = c.rank from rfl]
      exact hk
    exact pnLicNonKingUnder ht hpb htk

/-! ### The slider arithmetic (the cargo triad's two-by-two) -/


/-- Every potential slider of a KING is exactly rank queen — the
exchlaw falsifier's ♣Q is the whole class. -/
theorem pnKingSlider {z c : Card} (hs : canSitOn z c = true)
    (hk : c.rank = Rank.king) : z.rank = Rank.queen := by
  rw [canSitOn_eq] at hs
  have hk12 : (Rank.king).toIdx = 12 := rfl
  have hq11 : (Rank.queen).toIdx = 11 := rfl
  rw [hk, hk12] at hs
  exact Rank.toIdx_inj (by omega)

/-- NO slider exists for an ACE (nothing is rank zero minus one). -/
theorem pnAceNoSlider {z c : Card} (hs : canSitOn z c = true)
    (ha : c.rank = Rank.ace) : False := by
  rw [canSitOn_eq] at hs
  have ha0 : (Rank.ace).toIdx = 0 := rfl
  rw [ha, ha0] at hs
  omega

/-- The two potential sliders of one host share rank and color —
the two such cards are THEMSELVES TWINS (each color runs exactly
two suits; same color + same rank + different suit is the twin
relation; same suit + same rank is equality). -/
theorem pnSliderPair {z z' c : Card} (h1 : canSitOn z c = true)
    (h2 : canSitOn z' c = true) :
    z.rank = z'.rank ∧ z.suit.color = z'.suit.color := by
  obtain ⟨h1a, h1c⟩ := (canSitOn_eq z c).1 h1
  obtain ⟨h2a, h2c⟩ := (canSitOn_eq z' c).1 h2
  refine ⟨Rank.toIdx_inj (by omega), ?_⟩
  rcases z with ⟨zs, zr⟩
  rcases z' with ⟨z's, z'r⟩
  rcases c with ⟨cs, cr⟩
  cases zs <;> cases z's <;> cases cs <;> simp_all [Suit.color]

/-! ### Adjacent-run decomposition (the covered cells' reader) -/


private theorem pnMemDecomp : ∀ {l : List Card} {c : Card},
    c ∈ l → ∃ w1 w2, l = w1 ++ c :: w2
  | [], _, h => by simp at h
  | x :: t, c, h => by
      rcases List.mem_cons.1 h with rfl | hm
      · exact ⟨[], t, rfl⟩
      · obtain ⟨w1, w2, hq⟩ := pnMemDecomp (l := t) (c := c) hm
        refine ⟨x :: w1, w2, ?_⟩
        show x :: t = (x :: w1) ++ c :: w2
        rw [List.cons_append]
        exact congrArg (fun l => x :: l) hq

private theorem pnRunOKAdj : ∀ (pre : List Card) (c z : Card) (w : List Card),
    runOK (pre ++ c :: z :: w) = true → canSitOn z c = true
  | [], c, z, w, h => by
      rw [List.nil_append] at h
      have hexp : runOK (c :: z :: w) = (canSitOn z c && runOK (z :: w)) := rfl
      rw [hexp, Bool.and_eq_true] at h
      exact h.1
  | p :: t, c, z, w, h => by
      cases t with
      | nil =>
          rw [List.cons_append, List.nil_append] at h
          have hexp : runOK (p :: c :: z :: w) =
              (canSitOn c p && runOK (c :: z :: w)) := rfl
          rw [hexp, Bool.and_eq_true] at h
          exact pnRunOKAdj [] c z w h.2
      | cons q qs =>
          rw [List.cons_append] at h
          have hexp : runOK (p :: ((q :: qs) ++ c :: z :: w)) =
              (canSitOn q p && runOK ((q :: qs) ++ c :: z :: w)) := rfl
          rw [hexp, Bool.and_eq_true] at h
          exact pnRunOKAdj (q :: qs) c z w h.2

/-- At WF, the immediate cover of a COVERED card sits on it by the
run discipline. -/
theorem pnCoverSit {st : State} {c : Card} {a : Anchor} (hwf : st.WF)
    (hh : st.pileHolding c = some a) (hpt : st.pileOfTop c = none) :
    ∃ z w1 w2, (st.piles a).faceUp = w1 ++ c :: z :: w2 ∧ canSitOn z c = true := by
  have hmem : c ∈ (st.piles a).faceUp := pileHolding_mem hh
  have hnl : lastOf (st.piles a).faceUp ≠ some c := by
    intro hlast
    have htop : (st.piles a).top = some c := hlast
    rw [(pileOfTop_eq_some_iff hwf).2 htop] at hpt
    exact absurd hpt (by simp)
  obtain ⟨w1, w2, hq⟩ := pnMemDecomp hmem
  have hw2 : w2 ≠ [] := by
    intro he
    rw [he] at hq
    rw [hq] at hnl
    exact hnl (lastOf_snoc)
  obtain ⟨z, w2', hw2eq⟩ : ∃ z t, w2 = z :: t := by
    cases w2 with
    | nil => exact absurd rfl hw2
    | cons z t => exact ⟨z, t, rfl⟩
  subst hw2eq
  refine ⟨z, w1, w2', hq, ?_⟩
  have hrun : runOK ((st.piles a).faceUp) = true := hwf.2.1 a
  rw [hq] at hrun
  exact pnRunOKAdj w1 c z w2' hrun

/-- The cover-cargo class of a covered king is EXACTLY rank queen —
the exchlaw falsifier's Q is the entire class (the consistency
check). -/
theorem pnCoveredKingQueen {st : State} {c : Card} {a : Anchor}
    (hwf : st.WF) (hh : st.pileHolding c = some a)
    (hpt : st.pileOfTop c = none) (hk : c.rank = Rank.king) :
    ∃ z, canSitOn z c = true ∧ z.rank = Rank.queen := by
  obtain ⟨z, w1, w2, hq, hsit⟩ := pnCoverSit hwf hh hpt
  exact ⟨z, hsit, pnKingSlider hsit hk⟩

/-- ACES ARE NEVER COVERED at WF — the fork disease has a rank
floor. -/
theorem pnCoveredAceAbsurd {st : State} {c : Card} {a : Anchor}
    (hwf : st.WF) (hh : st.pileHolding c = some a)
    (hpt : st.pileOfTop c = none) (ha : c.rank = Rank.ace) : False := by
  obtain ⟨z, w1, w2, hq, hsit⟩ := pnCoverSit hwf hh hpt
  exact pnAceNoSlider hsit ha

/-! ### The cascade cells — new witnesses for the row table -/

def v3C2 : Card := ⟨Suit.club, Rank.two⟩
def v3HA : Card := ⟨Suit.heart, Rank.ace⟩
def v3DA : Card := ⟨Suit.diamond, Rank.ace⟩
def v3SA : Card := ⟨Suit.spade, Rank.ace⟩
def v3CA : Card := ⟨Suit.club, Rank.ace⟩
def v3CJ : Card := ⟨Suit.club, Rank.jack⟩
def v3SJ : Card := ⟨Suit.spade, Rank.jack⟩


/-- CAS-1, the BOTH-BARE row extended with the user's rung deltas:
red rungs at x-1 (hearts A..Q for the king twins), blacks at x-2
(A..J, so the black QUEENS' rungs already wait).  The waiting black
x-1's have no legal seat in a both-bare world (their only hosts —
red kings — are the bare twins themselves), so they park BARE at
anchors: raw-stackable (rung waits!) but seat-barred (the emptied
seat readmits only a king) — the canon never consumes them.  ONE
legal SLIDE lifts a parked queen onto a bare king — the row-A to
row-C road, repositioning into the covered pose. -/
def pnCasBareExt : State where
  found := fun s =>
    match s with
    | .heart => Suit.heart.upCards.take 12
    | .diamond => Suit.diamond.upCards.take 12
    | .spade => Suit.spade.upCards.take 11
    | .club => Suit.club.upCards.take 11
  piles := fun a =>
    match a with
    | .p1 => ⟨[], [v3HK]⟩
    | .p5 => ⟨[], [v3DK]⟩
    | .p3 => ⟨[], [v3CQ]⟩
    | .p4 => ⟨[], [v3SQ]⟩
    | _ => ⟨[], []⟩
  stock := v3Stock (Suit.heart.upCards.take 12 ++ Suit.diamond.upCards.take 12 ++
    Suit.spade.upCards.take 11 ++ Suit.club.upCards.take 11 ++
    [v3HK, v3DK, v3CQ, v3SQ])
  waste := []
  drawStep := 1

/-- CAS-1b, the slid state: the parked ♣Q has slid onto the bare
♥K — the cross-neighbor pose reached from row A by one legal
slide. -/
def pnCasBareSlide : State where
  found := fun s =>
    match s with
    | .heart => Suit.heart.upCards.take 12
    | .diamond => Suit.diamond.upCards.take 12
    | .spade => Suit.spade.upCards.take 11
    | .club => Suit.club.upCards.take 11
  piles := fun a =>
    match a with
    | .p1 => ⟨[], [v3HK, v3CQ]⟩
    | .p5 => ⟨[], [v3DK]⟩
    | .p4 => ⟨[], [v3SQ]⟩
    | _ => ⟨[], []⟩
  stock := v3Stock (Suit.heart.upCards.take 12 ++ Suit.diamond.upCards.take 12 ++
    Suit.spade.upCards.take 11 ++ Suit.club.upCards.take 11 ++
    [v3HK, v3DK, v3CQ, v3SQ])
  waste := []
  drawStep := 1

/-- CAS-2, the BOTH-UNDER row with the deltas: hearts/diamonds
climbed A..J (rung x-1 for the queen twins), blacks climbed A..10
(x-2).  Stacking the red queens exposes the black KING bases at
rung delta 2 (the ±2 collapse: the ladder must climb J then Q
before the exposed king's own rung waits); the black JACK
cross-neighbors are raw-stackable at delta 0 (rung ready, seat
barred — canon leaves them), and a hidden black queen under the
base rides the saturation verbatim (hidden cargo is inert). -/
def pnCasUnderExt : State where
  found := fun s =>
    match s with
    | .heart => Suit.heart.upCards.take 11
    | .diamond => Suit.diamond.upCards.take 11
    | .spade => Suit.spade.upCards.take 10
    | .club => Suit.club.upCards.take 10
  piles := fun a =>
    match a with
    | .p1 => ⟨[v3SQ], [v3CK, v3HQ]⟩
    | .p5 => ⟨[], [v3SK, v3DQ]⟩
    | .p3 => ⟨[], [v3CJ]⟩
    | .p4 => ⟨[], [v3SJ]⟩
    | _ => ⟨[], []⟩
  stock := v3Stock (Suit.heart.upCards.take 11 ++ Suit.diamond.upCards.take 11 ++
    Suit.spade.upCards.take 10 ++ Suit.club.upCards.take 10 ++
    [v3CK, v3SK, v3HQ, v3DQ, v3CJ, v3SJ, v3SQ])
  waste := []
  drawStep := 1

/-- CAS-3, the CROSS-NEIGHBOR merge cell: the exchlaw B2 pose with
the user's waiting rung — hearts and diamonds at A..Q, CLUBS AT
A..J, so the covering cargo ♣Q's own rung ALREADY waits.  The
covered slot reads as a function of rung deltas: at delta 0 the
cargo dissolves in-saturation, EXPOSING the buried king whose rung
also waits — THE FORK MERGES: canon from both faces lands at ONE
saturated state.  Contrast the exchlaw standing fork (delta =
everything away): the parked cargo cannot dissolve, the wings stay
split, and the A2 pull-highway is the price.  THE ???-SLOT ANSWERED:
the covering cargo's own rung read decides merge vs standing fork —
and neither fires intra-state. -/
def pnCasForkMerge : State where
  found := fun s =>
    match s with
    | .heart => Suit.heart.upCards.take 12
    | .diamond => Suit.diamond.upCards.take 12
    | .club => Suit.club.upCards.take 11
    | _ => []
  piles := fun a =>
    match a with
    | .p1 => ⟨[], [v3HK]⟩
    | .p5 => ⟨[], [v3DK, v3CQ]⟩
    | _ => ⟨[], []⟩
  stock := v3Stock (Suit.heart.upCards.take 12 ++ Suit.diamond.upCards.take 12 ++
    Suit.club.upCards.take 11 ++ [v3HK, v3DK, v3CQ])
  waste := []
  drawStep := 1

/-- The exchange-mate of the merge cell (the slide image). -/
def pnCasForkMergeX : State where
  found := fun s =>
    match s with
    | .heart => Suit.heart.upCards.take 12
    | .diamond => Suit.diamond.upCards.take 12
    | .club => Suit.club.upCards.take 11
    | _ => []
  piles := fun a =>
    match a with
    | .p1 => ⟨[], [v3HK, v3CQ]⟩
    | .p5 => ⟨[], [v3DK]⟩
    | _ => ⟨[], []⟩
  stock := v3Stock (Suit.heart.upCards.take 12 ++ Suit.diamond.upCards.take 12 ++
    Suit.club.upCards.take 11 ++ [v3HK, v3DK, v3CQ])
  waste := []
  drawStep := 1

/-- CAS-4, the rank-floor cell (the ACE degeneracy row): empty
foundations; the ace twins BOTH-UNDER (♥A on ♣2 at p1, ♦A on ♠2 at
p5 — permanently raisable, licensed now), while BARE aces park at
p3/p4: raw-stackable (an ace's rung is the empty foundation,
always waiting) yet seat-barred (the bare leg is the bare-KING
leg) — decided raw-vs-licensed data at the rank floor, and the
across-the-board datum: no cargo can ever cover an ace. -/
def pnCasAces : State where
  found := fun _ => []
  piles := fun a =>
    match a with
    | .p1 => ⟨[], [v3C2, v3HA]⟩
    | .p5 => ⟨[], [v3S2, v3DA]⟩
    | .p3 => ⟨[], [v3SA]⟩
    | .p4 => ⟨[], [v3CA]⟩
    | _ => ⟨[], []⟩
  stock := v3Stock [v3C2, v3HA, v3S2, v3DA, v3SA, v3CA]
  waste := []
  drawStep := 1

/-! ### The rung-delta reader (exposed-top-after-cascade as a
function of rung deltas, decided per row) -/


/-- The rung delta of `z` at `st`: how many climbs its suit still
owes before `z`'s rung waits. -/
def pnRungDelta (st : State) (z : Card) : Int :=
  z.rank.toIdx - (st.found z.suit).length

/-! ### The row table -/


/-- Row 1 — THE LATTICE HEADER: every face-up card at every census
cell sits in exactly one position state; the pair families read
the expected cells. -/
def pnRowLattice : Bool :=
  [v3Bare, v3Under, v3Mixed, v3Chain, v3Fork, v3ForkX,
   pnCasBareExt, pnCasBareSlide, pnCasUnderExt, pnCasForkMerge, pnCasForkMergeX,
   pnCasAces, v3Cargo, v3WasteRes, v3BareNonKing, v3RevealBar].all (fun st =>
    Card.universe.all (fun c =>
      !decide ((st.pileHolding c).isSome) ||
      pnExactlyOne (pnPosCovered st c) (pnPosBare st c) (pnPosUnder st c))) &&
  -- the licensed pairs land in the two inhabited cells
  (pnPosBare v3Bare v3HK && pnPosBare v3Bare v3DK &&
    pnPosUnder v3Under v3HQ && pnPosUnder v3Under v3DQ &&
    pnPosBare pnCasBareExt v3HK && pnPosBare pnCasBareExt v3DK &&
    pnPosUnder pnCasUnderExt v3HQ && pnPosUnder pnCasUnderExt v3DQ) &&
  -- the covered wings read covered (cargo above), old fork included
  (pnPosCovered v3Fork v3DK && pnPosCovered v3ForkX v3HK &&
    pnPosCovered pnCasForkMerge v3DK && pnPosCovered pnCasForkMergeX v3HK) &&
  -- the parked queens of row A sit at bare-singleton anchors
  (pnPosBare pnCasBareExt v3CQ && pnPosBare pnCasBareExt v3SQ) &&
  -- the slid pose: the covered king, the bare mate
  (pnPosCovered pnCasBareSlide v3HK && pnPosBare pnCasBareSlide v3DK)

/-- Row 2 — BOTH-BARE: the independent pair, the parked waiting
rungs (raw-stackable AND seat-barred — the canon never consumes
them), and the row-A→row-C SLIDE with the slid pose's own clean
census. -/
def pnRowBothBare : Bool :=
  v3WfB pnCasBareExt && v3FamilyClean pnCasBareExt &&
  (canRaiseB pnCasBareExt v3HK && canRaiseB pnCasBareExt v3DK) &&
  decide ((v3Lic pnCasBareExt).length = 2) &&
  -- the waiting black x-1's: raw-stackable, seat-barred, parked
  (stackableB pnCasBareExt v3CQ && !(canRaiseB pnCasBareExt v3CQ)) &&
  (stackableB pnCasBareExt v3SQ && !(canRaiseB pnCasBareExt v3SQ)) &&
  -- the canon consumes the kings and parks the queens verbatim
  decide ((canon pnCasBareExt).found .heart = Suit.heart.upCards) &&
  decide ((canon pnCasBareExt).found .diamond = Suit.diamond.upCards) &&
  decide ((canon pnCasBareExt).piles .p3 = ⟨[], [v3CQ]⟩) &&
  decide ((canon pnCasBareExt).piles .p4 = ⟨[], [v3SQ]⟩) &&
  decide ((v3Lic (canon pnCasBareExt)).length = 0) &&
  -- the row-A→row-C road: one legal slide of a parked queen onto
  -- a bare king repositions into the covered pose
  decide (pnCasBareExt.step (Move.tabToTab v3CQ (Sum.inr v3HK)) = some pnCasBareSlide) &&
  -- the slid pose: covered king, bare mate, still contention-clean
  v3WfB pnCasBareSlide && v3FamilyClean pnCasBareSlide &&
  -- and its saturation dissolves the cover (rung waits) and the
  -- buried twin with it — the merge anatomy INSIDE row A's road
  decide ((canon pnCasBareSlide).found .heart = Suit.heart.upCards) &&
  decide ((canon pnCasBareSlide).found .diamond = Suit.diamond.upCards) &&
  decide ((canon pnCasBareSlide).found .club = Suit.club.upCards.take 12) &&
  decide (canon pnCasBareSlide ≠ canon pnCasBareExt) &&
  -- twin-blindness
  decide (canon pnCasBareExt.twinMap = (canon pnCasBareExt).twinMap)

/-- Row 3 — BOTH-UNDER: the seated pair, the ±2 bases (exposed
kings at rung delta 2), the delta-0 cross-neighbors (raw J's,
seat-barred), the hidden cargo riding verbatim, and the parked
foundations after saturation. -/
def pnRowBothUnder : Bool :=
  v3WfB pnCasUnderExt && v3FamilyClean pnCasUnderExt &&
  (canRaiseB pnCasUnderExt v3HQ && canRaiseB pnCasUnderExt v3DQ) &&
  decide ((v3Lic pnCasUnderExt).length = 2) &&
  v3LicMonotone pnCasUnderExt v3HQ && v3LicMonotone pnCasUnderExt v3DQ &&
  -- the canon consumes the queens; the bases expose at delta 2
  decide ((canon pnCasUnderExt).found .heart = Suit.heart.upCards.take 12) &&
  decide ((canon pnCasUnderExt).found .diamond = Suit.diamond.upCards.take 12) &&
  decide ((canon pnCasUnderExt).piles .p1 = ⟨[v3SQ], [v3CK]⟩) &&
  decide ((canon pnCasUnderExt).piles .p5 = ⟨[], [v3SK]⟩) &&
  decide ((v3Lic (canon pnCasUnderExt)).length = 0) &&
  decide (pnRungDelta (canon pnCasUnderExt) v3CK = 2) &&
  decide (pnRungDelta (canon pnCasUnderExt) v3SK = 2) &&
  decide (pnRungDelta (canon pnCasUnderExt) v3CJ = 0) &&
  decide (pnRungDelta (canon pnCasUnderExt) v3SJ = 0) &&
  (stackableB (canon pnCasUnderExt) v3CJ && !(canRaiseB (canon pnCasUnderExt) v3CJ)) &&
  (stackableB (canon pnCasUnderExt) v3SJ && !(canRaiseB (canon pnCasUnderExt) v3SJ)) &&
  -- twin-blindness
  decide (canon pnCasUnderExt.twinMap = (canon pnCasUnderExt).twinMap)

/-- Row 4 — CROSS-NEIGHBOR: the merge cell and its mate, the slide
steps, the intermediate states' cleanliness, the MERGE verdict
(canon equal from both faces), the contrast with the standing
fork, and the exposed-twin leg inside the merge. -/
def pnRowCross : Bool :=
  v3WfB pnCasForkMerge && v3WfB pnCasForkMergeX &&
  v3FamilyClean pnCasForkMerge && v3FamilyClean pnCasForkMergeX &&
  v3FamilyClean (v3Fired pnCasForkMerge v3HK) &&
  -- the faces: exactly one twin licensed, plus the waiting-rung cargo
  (canRaiseB pnCasForkMerge v3HK && !(canRaiseB pnCasForkMerge v3DK)) &&
  (!(canRaiseB pnCasForkMergeX v3HK) && canRaiseB pnCasForkMergeX v3DK) &&
  (canRaiseB pnCasForkMerge v3CQ && canRaiseB pnCasForkMergeX v3CQ) &&
  decide (pnRungDelta pnCasForkMerge v3CQ = 0) &&
  -- the slide realization, step-exact both directions
  decide (pnCasForkMerge.step (Move.tabToTab v3CQ (Sum.inr v3HK)) = some pnCasForkMergeX) &&
  decide (pnCasForkMergeX.step (Move.tabToTab v3CQ (Sum.inr v3DK)) = some pnCasForkMerge) &&
  -- THE MERGE: the dissolving cover exposes the buried king
  -- licensed, and canon from BOTH faces is ONE state
  decide (canon pnCasForkMerge = canon pnCasForkMergeX) &&
  decide ((canon pnCasForkMerge).found .heart = Suit.heart.upCards) &&
  decide ((canon pnCasForkMerge).found .diamond = Suit.diamond.upCards) &&
  decide ((canon pnCasForkMerge).found .club = Suit.club.upCards.take 12) &&
  decide ((canon pnCasForkMerge).piles .p1 = ⟨[], []⟩) &&
  decide ((canon pnCasForkMerge).piles .p5 = ⟨[], []⟩) &&
  decide ((v3Lic (canon pnCasForkMerge)).length = 0) &&
  canRaiseB (v3Fired pnCasForkMerge v3CQ) v3DK &&
  -- THE CONTRAST: the parked-delta standing fork still splits
  decide (canon v3Fork ≠ canon v3ForkX) &&
  -- twin-blindness on every face
  decide (canon pnCasForkMerge.twinMap = (canon pnCasForkMerge).twinMap) &&
  decide (canon pnCasForkMergeX.twinMap = (canon pnCasForkMergeX).twinMap)

/-- Row 5 — THE RANK-ENDPOINT DEGENERACIES, decided: the covered
kings' covers are queens at every crafted covered-king cell, and
the ACE row: the both-under licensed ace pair, the parked bare
aces (raw-stackable, seat-barred), foundations after saturation. -/
def pnRowDegeneracies : Bool :=
  -- KING: the covered kings' covers are queens, both fork families
  (pnPosCovered v3Fork v3DK && pnPosCovered pnCasForkMerge v3DK &&
    v3FamilyClean pnCasBareSlide) &&
  -- the king twins of the battery: every licensed king bare
  (pnPosBare v3Bare v3HK && pnPosBare v3Bare v3DK &&
    pnPosBare v3Mixed v3HK && pnPosBare v3Fork v3HK) &&
  -- ACE: the both-under licensed pair, raw-bare parks at p3/p4
  v3WfB pnCasAces && v3FamilyClean pnCasAces &&
  (canRaiseB pnCasAces v3HA && canRaiseB pnCasAces v3DA) &&
  decide ((v3Lic pnCasAces).length = 2) &&
  (canRaiseB pnCasAces v3SA && canRaiseB pnCasAces v3CA) == false &&
  (stackableB pnCasAces v3SA && !(canRaiseB pnCasAces v3SA)) &&
  (stackableB pnCasAces v3CA && !(canRaiseB pnCasAces v3CA)) &&
  (pnPosUnder pnCasAces v3HA && pnPosUnder pnCasAces v3DA &&
    pnPosBare pnCasAces v3SA && pnPosBare pnCasAces v3CA) &&
  decide ((canon pnCasAces).found .heart = [v3HA]) &&
  decide ((canon pnCasAces).found .diamond = [v3DA]) &&
  decide ((canon pnCasAces).piles .p3 = ⟨[], [v3SA]⟩) &&
  decide ((canon pnCasAces).piles .p4 = ⟨[], [v3CA]⟩) &&
  decide ((v3Lic (canon pnCasAces)).length = 0) &&
  decide (canon pnCasAces.twinMap = (canon pnCasAces).twinMap)

/-- Row 6 — the negatives ride (landing 1's V6) plus the inert
triad leg: the stock-resident slider of the merge cell never
registers anywhere (never stacked, never founded). -/
def pnRowNegatives : Bool :=
  v3GateV6 &&
  decide (v3SQ ∈ pnCasForkMerge.stock) &&
  !(stackableB pnCasForkMerge v3SQ) &&
  decide (v3SQ ∉ (canon pnCasForkMerge).found .spade)

/-- The cargo of the pair's two host piles, as (card, anchor)
pairs, the pair members themselves excluded. -/
def pnPileCargo (st : State) (a : Anchor) (c : Card) : List (Card × Anchor) :=
  (((st.piles a).hidden ++ (st.piles a).faceUp).filter
    (fun z => decide (z ≠ c))).map (fun z => (z, a))

/-- The neighborhood cargo of the licensed pair {c, c.twin}. -/
def pnCargoPairs (st : State) (c : Card) : List (Card × Anchor) :=
  match st.pileOfTop c with
  | none => []
  | some a =>
    match st.pileOfTop c.twin with
    | none => []
    | some b => pnPileCargo st a c ++ pnPileCargo st b c.twin

/-- THE LOCAL CONTAINMENT (the closing corollary row, decided):
at a licensed twin pair, every neighborhood cargo card either
DISSOLVES into the pair's cascade (founded at canon) or PARKS
VERBATIM at its seat (hidden or face-up in its original pile) —
the decoupled class is the parked-residue/slide family, and no
fork-cargo fires intra-state. -/
def pnContained (st : State) (c : Card) : Bool :=
  canRaiseB st c && canRaiseB st c.twin &&
  (pnCargoPairs st c).all (fun p =>
    match p with
    | (z, a) =>
        decide (z ∈ (canon st).found z.suit) ||
        decide (z ∈ ((canon st).piles a).hidden) ||
        decide (z ∈ ((canon st).piles a).faceUp))

/-- The whole battery of census states, for the corollary scan. -/
def pnAllCells : List State :=
  [v3Bare, v3Under, v3Mixed, v3Chain, v3Fork, v3ForkX,
   pnCasBareExt, pnCasBareSlide, pnCasUnderExt, pnCasForkMerge, pnCasForkMergeX,
   pnCasAces, v3Cargo, v3WasteRes, v3BareNonKing, v3RevealBar]

/-- Row 7 — THE CLOSING COROLLARY: the containment holds at every
licensed pair of every census cell; every cell stays universe-clean
(the landing-1 contention census); and the SHARPENED NEGATIVE —
the global form is FALSE: a coupled cargo DOES exist in the wild
(the standing fork's ♣Q couples the kings' saturation channel) —
but only CROSS-MATE, where the pair is not both-licensed, so the
local form is exactly the honest boundary. -/
def pnCorollaryContainment : Bool :=
  pnAllCells.all (fun st =>
    Card.universe.all (fun c =>
      !(canRaiseB st c && canRaiseB st c.twin) || pnContained st c)) &&
  pnAllCells.all (fun st => v3FamilyClean st) &&
  -- the global form is false: the standing fork couples a cargo
  -- between exchange mates (one licensed per face, wings split)
  (canRaiseB v3Fork v3HK && !(canRaiseB v3Fork v3DK)) &&
  decide (canon v3Fork ≠ canon v3ForkX)

/-- THE TABLE. -/
def pair_neighborhood_cases : Bool :=
  pnRowLattice && pnRowBothBare && pnRowBothUnder && pnRowCross &&
  pnRowDegeneracies && pnRowNegatives && pnCorollaryContainment

-- The landing-3 census numbers (printed for the ledger; the rows
-- above carry the load-bearing checks):
#eval pnRowLattice -- expect true: the position lattice, all cells
#eval pnRowBothBare -- expect true: the bare pair, the parked rungs, the slide
#eval pnRowBothUnder -- expect true: the seated pair, deltas two and zero
#eval pnRowCross -- expect true: the merge rows and the contrast
#eval pnRowDegeneracies -- expect true: the K and A fence posts
#eval pnRowNegatives -- expect true: the inert triad legs
#eval pnCorollaryContainment -- expect true: the closing local containment
#eval pnRungDelta pnCasUnderExt v3HQ -- expect 0: the licensed twin, rung waits
#eval pnRungDelta (canon pnCasUnderExt) v3CK -- expect 2: exposed base, two climbs owed
#eval pnRungDelta pnCasForkMerge v3HK -- expect 0: the bare twin licenses now
#eval pnRungDelta pnCasForkMerge v3CQ -- expect 0: the cover's rung waits
#eval pnRungDelta v3Fork v3CQ -- expect 11: the standing fork's cover is parked far
#eval (v3Lic pnCasAces).length -- expect 2: the both-under ace pair
#eval (v3Lic (canon pnCasForkMerge)).length -- expect 0: the merge wing is Final

#print axioms pnPosTrich
#print axioms pnCoveredNotLicensed
#print axioms pnCoveredPairAtMostOne
#print axioms pnLicKingBare
#print axioms pnLicNonKingUnder
#print axioms pnLicPairSlice
#print axioms pnKingSlider
#print axioms pnAceNoSlider
#print axioms pnSliderPair
#print axioms pnCoverSit
#print axioms pnCoveredKingQueen
#print axioms pnCoveredAceAbsurd

#eval! do
  if v3AllGates && pair_neighborhood_cases then
    IO.println "CANONV3: ALL GATES HOLD (LANDINGS 1+3) —"
    IO.println ""
    IO.println "LANDING 3 — pair_neighborhood_cases, the lattice header:"
    IO.println "POSITION TRICHOTOMY (pnPosTrich): every face-up card at WF is"
    IO.println "exactly one of bare-top / under-top / covered — the pair reads"
    IO.println "nine cells."
    IO.println "LICENSED SLICE: covered never licenses (pnCoveredNotLicensed),"
    IO.println "so covered pairs carry at most ONE licensed twin"
    IO.println "(pnCoveredPairAtMostOne); the licensed slice collapses to TWO"
    IO.println "cells — both-bare (kings, pnLicKingBare: nothing is rank 13+1)"
    IO.println "and both-under (non-kings, pnLicPairSlice); independence across"
    IO.println "the whole slice rides the banked canRaise_lifted."
    IO.println "RANK FENCE POSTS: a covered king's cover is exactly a QUEEN"
    IO.println "(pnCoveredKingQueen — the exchlaw falsifier's Q is the whole"
    IO.println "class); ACES are never covered (pnCoveredAceAbsurd — nothing is"
    IO.println "rank 0): the fork disease has a rank floor."
    IO.println "THE CARGO TRIAD: the two potential sliders of a host share rank"
    IO.println "and color — twins (pnSliderPair); they stack now (rung waits: the"
    IO.println "merge cell dissolves the fork, canon equal from both faces), or"
    IO.println "park (the slide class: the standing fork, cross-mate, priced by"
    IO.println "the A2 highway), or sit inert (hidden/waste/stock). The"
    IO.println "post-cascade top slot is a function of rung deltas: bases at"
    IO.println "delta 2 park; cross-neighbors at delta 0 are raw-stackable yet"
    IO.println "seat-barred; a delta-0 cover merges the fork."
    IO.println "CLOSING COROLLARY — THE LOCAL CONTAINMENT: at every licensed pair"
    IO.println "of every census cell, each neighborhood cargo dissolves or parks"
    IO.println "verbatim; the global form is FALSE (the standing fork couples a"
    IO.println "cargo — but only cross-mate, where the pair is not"
    IO.println "both-licensed). No fork-cargo fires intra-state. The case table"
    IO.println "exhausts the cases."
  else
    throw (IO.userError "CANONV3 LANDING 3: A GATE FAILED — see the numbers above")

/-! ## Landing 4 — the class-anchored selector, decided: face-lists, both-wing queries, injectivity, the fork-detector rows, the saturated-orbit spot rows

The plateau card (consumed through Orig.CanV3, the new library
chapter — `canonIdx` the composite height-first index, `canV3Arg`
the deterministic argmax fold): until the decompression merge the
cone engine is an unmerged import, so the class member sets ride
as EXPLICIT face-lists — every face constructed BY APPLICATION
(canon of a crafted member), never hand-drawn — and the rows
decide the selector's conduct at every census family.

Note the setoid flip (the 2026-10-10 user decision): the classes
are RevEqW-closures; conjugate mates live in DISTINCT classes.
The saturated face-lists below therefore carry NO conjugate arms:
one class, at most the two wings (fork exclusivity: at most one
forked pair per class; the crafted double-fork exhibit confirms
the Q-cargo arithmetic by refusing to stand).  -/

/-- The standing fork family's saturated faces, by application:
the two wings. -/
def l4ForkFaces : List State := [canon v3Fork, canon v3ForkX]

/-- The merge family's saturated faces: canon from both faces is
ONE state — a singleton class. -/
def l4MergeFaces : List State := [canon pnCasForkMerge, canon pnCasForkMergeX]

/-- The row-A family's faces: the parked pose and the slid pose's
dissolved image. -/
def l4BareFaces : List State := [canon pnCasBareExt, canon pnCasBareSlide]

/-- The both-under family's faces: the saturated endpoint and its
kings-slid variant. -/
def l4UnderFaces : List State := [canon v3Under, canon v3Under.twinMap]

/-- Wing-consistency: the argmax is queried from both orders of
every face-list — the pick is order-independent (the height-first
lex with fixed suit order decides the arms deterministically). -/
def l4RowWingConsistency : Bool :=
  decide (canonV3Arg l4ForkFaces = canonV3Arg l4ForkFaces.reverse) &&
  decide (canonV3Arg l4MergeFaces = canonV3Arg l4MergeFaces.reverse) &&
  decide (canonV3Arg l4BareFaces = canonV3Arg l4BareFaces.reverse) &&
  decide (canonV3Arg l4UnderFaces = canonV3Arg l4UnderFaces.reverse)

/-- Section-injectivity, decided: distinct census classes select
DISTINCT canonical states (no two classes share a canonical
representative). -/
def l4RowInjectivity : Bool :=
  decide (canonV3Arg l4ForkFaces ≠ canonV3Arg l4MergeFaces) &&
  decide (canonV3Arg l4ForkFaces ≠ canonV3Arg l4BareFaces) &&
  decide (canonV3Arg l4ForkFaces ≠ canonV3Arg l4UnderFaces) &&
  decide (canonV3Arg l4MergeFaces ≠ canonV3Arg l4BareFaces) &&
  decide (canonV3Arg l4MergeFaces ≠ canonV3Arg l4UnderFaces) &&
  decide (canonV3Arg l4BareFaces ≠ canonV3Arg l4UnderFaces)

/-- ARM SELECTION, decided: the standing fork's class takes the
HEIGHT-LEX-LARGER wing — hearts win (the arm price at the height
level, paid on founded content); the merge class is a singleton;
the row-A family takes the DISSOLVED face (club arose to 12); the
under family's conjugate arm — by the htup-pair permutation
row — ties on heights where symmetric and splits otherwise. -/
def l4RowArmChoice : Bool :=
  decide (canonV3Arg l4ForkFaces = some (canon v3Fork)) &&
  decide (canonV3Arg l4MergeFaces = some (canon pnCasForkMerge)) &&
  decide (canonV3Arg l4BareFaces = some (canon pnCasBareSlide)) &&
  decide (canonV3Arg l4UnderFaces = some (canon v3Under) ∨
    canonV3Arg l4UnderFaces = some (canon v3Under).twinMap)

/-- SATURATED-TUPLE ORBIT SPOT ROWS (the lead row's decided
evidence — the pair-flip calibration): the fork family's two
wing tuples differ EXACTLY by the heart/diamond flip and their
per-suit sums agree; the merge class's two faces are ONE state
(the trivial orbit); the htup-permutation row itself is proven in
the library (canonHtup_twinMap). -/
def l4HdFlip (t : List Nat) : List Nat := [t.getD 0 0, t.getD 2 0, t.getD 1 0, t.getD 3 0]

def l4RowOrbitSpots : Bool :=
  decide (canonHtup (canon v3Fork) = l4HdFlip (canonHtup (canon v3ForkX)) ∨
    canonHtup (canon v3ForkX) = l4HdFlip (canonHtup (canon v3Fork))) &&
  decide ((canonHtup (canon v3Fork)).foldl (· + ·) 0 =
    (canonHtup (canon v3ForkX)).foldl (· + ·) 0) &&
  decide (canon pnCasForkMerge = canon pnCasForkMergeX)

/-- THE FORK DETECTOR (slide-sensitivity), decided at the crafted
roads: a fork state is one whose canonical form is SLIDE-SENSITIVE
— the standing fork's pre-state registers (the ♣Q slide moves it
to the other wing's basin); the merge cell's pre-state does NOT
(the slide commutes with the saturation); the row-A parked pose
REGISTERS (the dissolve-extending slide — the false-positive
finding: slide-sensitivity properly CONTAINS the wing forks; the
ordering discriminator — the height comparability of the two
saturation faces — separates them, canonIdx reading above both);
the both-bare kings' world does not (the anchor-slides of bare
kings re-saturate home). -/
def l4RowForkDetector : Bool :=
  decide (canon v3Fork ≠ canon v3ForkX) &&
  decide (canon pnCasForkMerge = canon pnCasForkMergeX) &&
  decide (canon pnCasBareExt ≠ canon pnCasBareSlide) &&
  decide (canon ((v3Bare.step (Move.tabToTab v3HK (Sum.inl Anchor.p3))).getD v3Bare) =
    canon v3Bare)

/-- THE NONEMPTY ROW + THE SATURATED GATE, decided: the face-lists
are nonempty and every selection is saturated (license census
zero — the still-state read of Final at the picked faces). -/
def l4RowNonempty : Bool :=
  decide ((canonV3Arg l4ForkFaces).isSome) &&
  decide ((canonV3Arg l4MergeFaces).isSome) &&
  decide ((canonV3Arg l4BareFaces).isSome) &&
  decide ((canonV3Arg l4UnderFaces).isSome) &&
  decide ((v3Lic ((canonV3Arg l4ForkFaces).getD v3Fork)).length = 0) &&
  decide ((v3Lic ((canonV3Arg l4MergeFaces).getD pnCasForkMerge)).length = 0) &&
  decide ((v3Lic ((canonV3Arg l4BareFaces).getD pnCasBareSlide)).length = 0) &&
  decide ((v3Lic (canonV3Arg l4UnderFaces |>.getD v3Under)).length = 0)

/-- THE LANDING-4 TABLE. -/
def l4AllGates : Bool :=
  l4RowWingConsistency && l4RowInjectivity && l4RowArmChoice &&
  l4RowOrbitSpots && l4RowForkDetector && l4RowNonempty

-- The landing-4 census numbers (printed for the ledger):
#eval l4RowWingConsistency -- expect true: order-independent argmax
#eval l4RowInjectivity -- expect true: distinct classes, distinct picks
#eval l4RowArmChoice -- expect true: the arms read as pinned
#eval l4RowOrbitSpots -- expect true: the pair-flip spot rows
#eval l4RowForkDetector -- expect true: sensitivity + the finding
#eval l4RowNonempty -- expect true: nonempty, saturated
#eval canonHtup (canon v3Fork) -- expect [0, 13, 12, 0]
#eval canonHtup (canon v3ForkX) -- expect [0, 12, 13, 0]
#eval canonHtup (canon pnCasBareExt) -- expect [11, 13, 13, 11]
#eval canonHtup (canon pnCasBareSlide) -- expect [11, 13, 13, 12]

#eval! do
  if v3AllGates && pair_neighborhood_cases && l4AllGates then
    IO.println "CANONV3: ALL GATES HOLD (LANDINGS 1+3+4) —"
    IO.println ""
    IO.println "LANDING 4 — the class-anchored selector (Orig.CanV3: zero sorry,"
    IO.println "audits [propext] / [propext, Quot.sound], zero Classical.choice):"
    IO.println "the composite height-first canonIdx (htup leads with FIXED suit"
    IO.println "order; the position key breaks wiggle ties, conj-invariant by"
    IO.println "construction; the formal key the last formality) drives the"
    IO.println "deterministic argmax over explicit face-lists — member sets"
    IO.println "constructed BY APPLICATION from the crafted classes."
    IO.println "Wing-consistency: querying from both orders of every face-list"
    IO.println "picks the same representative. Injectivity: distinct classes"
    IO.println "select distinct representatives. ARM CHOICE: the standing fork"
    IO.println "class takes the heart wing (13/12 beats 12/13 under fixed suit"
    IO.println "order — the arm price paid on founded content); the merge class"
    IO.println "is a singleton; row-A takes the dissolved face; the under"
    IO.println "family's conjugate arms split deterministically."
    IO.println "ORBIT SPOTS: the wings' tuples differ exactly by the hd-flip,"
    IO.println "per-suit sums equal. The fork detector registers the standing"
    IO.println "fork, misses the merge, FINDS the dissolve-extending slide of"
    IO.println "the row-A pose (slide-sensitivity properly contains the wing"
    IO.println "forks — the height ordering discriminates), and misses the"
    IO.println "bare kings' anchor-slides."
    IO.println "SATRung/neverStackable/parkingMap land as the chapter's"
    IO.println "organizing vocabulary (state-level via the banked canon, the"
    IO.println "arm visible as a ceiling asymmetry); the class-level ceiling"
    IO.println "stack (classRung the sup over ALL members — the canus filter"
    IO.println "never needed in the definition's face), the Q-cargo law, the"
    IO.println "fork-exclusivity sandwich (three lemmas, deductive), and the"
    IO.println "post-merge residues (the canus bridge, the saturated-tuple"
    IO.println "orbit, the full section iff) are ledgered in FUTURES §11-L4"
    IO.println "with payers named — mem_macro_iff the one engine."
  else
    throw (IO.userError "CANONV3 LANDING 4: A GATE FAILED — see the numbers above")

/-! ## Signature correction (amr_129d6300b, the user's detection discussion) — the corrected forkEvidence, decide-graded

The corrected signature, read live DURING saturation at the stall
point (NOT both-stackable — that reading is VACUOUS at real fork
cells, consistent with landing 1's census verdict that
intra-state contention is empty at WF — one twin is always covered
at a stall):  CanRaise x (the bare twin) ∧ coveredIn x.twin (∃ a,
pileHolding x.twin = some a ∧ aboveIn ≠ []) ∧ cargo-shape (∃ d,
d.rank.toIdx + 1 = x.rank.toIdx ∧ ¬twinSuit d.suit x.suit ∧
rungAt d.suit < d.rank.toIdx — the PIN: the cargo cannot stack in
place and the cascade cannot light it) ∧ THE OPERATIONAL TRIAL
(∃ st', st.step (.tabToTab d (Sum.inr x)) = some st' ∧ CanRaise
st' x.twin — the slide lights the covered twin, the other arm
witnessed).

AUDIT (the request's consequence-2): the landed case-table rows
are CONSISTENT with the corrected signature — no row speaks of
both-stackable twins at a fork stall; the lattice states the
opposite (pnCoveredPairAtMostOne: covered ⇒ at most one licensed
twin), the both-licensed rows are exactly the independence slice
(the NON-fork cells: both-bare kings / both-under non-kings),
and the covered rows speak of the covered twin under cargo
(pnCoverSit/pnCoveredKingQueen/pnCoveredAceAbsurd).  No vacuous
rows found.  The merge cell is the false-positive guard the
correction predicted: the slide-trial fires there (canon from
both faces lands ONE state — the merge battery row), but the PIN
leg refuses (rungAt clubs = 11 = d.rank.toIdx, NOT <) — the
benign next-in-line does NOT register.  -/

/-- coveredIn as the Bool mirror: face-up in a pile with content
above. -/
def v3CoveredInB (st : State) (c : Card) : Bool :=
  match st.pileHolding c with
  | none => false
  | some a => decide (aboveIn c (st.piles a).faceUp ≠ [])

/-- rungAt as the found length (the state-level ceiling read on
the raw state). -/
def v3RungAt (st : State) (s : Suit) : Nat := (st.found s).length

/-- twinSuit (same-color family) as the Bool mirror. -/
def v3TwinSuitB (d s : Suit) : Bool :=
  decide (d = s ∨ d = s.twin)

/-- The CORRECTED forkEvidence signature, live at the stall:
bare twin licensed, twin covered by pinned cargo of the opposite
color, and the operational slide-trial lights the other arm. -/
def v3ForkSigB (st : State) (x d : Card) : Bool :=
  canRaiseB st x &&
  v3CoveredInB st x.twin &&
  decide (d.rank.toIdx + 1 = x.rank.toIdx) &&
  !(v3TwinSuitB d.suit x.suit) &&
  decide (v3RungAt st d.suit < d.rank.toIdx) &&
  (match st.step (Move.tabToTab d (Sum.inr x)) with
   | none => false
   | some st' => canRaiseB st' x.twin)

/-- False for the empty/parked cases the signature must exclude:
the full-leg trace at a cell for a named (x, d) — pin only, no
slide leg. -/
def v3ForkPinB (st : State) (x d : Card) : Bool :=
  canRaiseB st x &&
  v3CoveredInB st x.twin &&
  decide (d.rank.toIdx + 1 = x.rank.toIdx) &&
  !(v3TwinSuitB d.suit x.suit) &&
  decide (v3RungAt st d.suit < d.rank.toIdx)

/-- The corrected-signature rows (all decide-graded):

- v3Fork (the standing fork stall): the FULL signature fires —
  the bare ♥K licensed, ♦K covered by the pinned ♣Q (clubs rung
  0 < 11), the slide-trial lands on v3ForkX and lights CanRaise
  of the exposed twin — the other arm witnessed live.
- v3ForkX (the mate stall): the symmetric signature fires.
- pnCasForkMerge (the benign next-in-line): the pin leg REFUSES
  (clubs rung 11 = ♣Q's own index — the cargo can stack in
  place, the cascade lights it and the fork MERGES) — while the
  slide-trial alone fires there — the false-positive guard: the
  next-in-line does NOT register under the corrected signature.
- fork_pins restated: the same-color rungs pinned at the pair
  rank — the bare twin by stackable-now (its rung EXACT), the
  covered twin by the cargo/cascade arithmetic (NOT by
  CanRaise: the covered twin is unlicensed at the stall).
-/
def l4RowForkSigCorrected : Bool :=
  -- the standing fork, both stalls: full signature registers
  v3ForkSigB v3Fork v3HK v3CQ &&
  v3ForkSigB v3ForkX v3DK v3CQ &&
  -- the pin leg alone holds at the stalls (arithmetic only)
  v3ForkPinB v3Fork v3HK v3CQ &&
  v3ForkPinB v3ForkX v3DK v3CQ &&
  -- the covered twins are NOT licensed at the stalls (the
  -- signature reads one licensed + one covered, never both)
  !(canRaiseB v3Fork v3DK) &&
  !(canRaiseB v3ForkX v3HK) &&
  -- the same-color rungs pinned at the pair rank: hearts AND
  -- diamonds at 12 at both stalls (the bare twin's rung EXACT)
  decide (v3RungAt v3Fork .heart = 12) &&
  decide (v3RungAt v3Fork .diamond = 12) &&
  decide (v3RungAt v3ForkX .heart = 12) &&
  decide (v3RungAt v3ForkX .diamond = 12) &&
  -- THE BENIGN NEXT-IN-LINE REFUSES: at the merge cell the
  -- bare twin is licensed and the twin is covered, but the
  -- cargo's own rung WAITS — the pin leg fails, the full
  -- signature is false, though the slide-trial alone fires
  !(v3ForkPinB pnCasForkMerge v3HK v3CQ) &&
  !(v3ForkSigB pnCasForkMerge v3HK v3CQ) &&
  canRaiseB (pnCasForkMerge.step (Move.tabToTab v3CQ (Sum.inr v3HK))
    |>.getD pnCasForkMerge) v3DK &&
  -- and the covered twin lights post-slide — the merge shape is
  -- the cascade's own work, not a fork's
  decide (canon pnCasForkMerge = canon pnCasForkMergeX)

-- The signature-correction census numbers (printed for the ledger):
#eval v3ForkSigB v3Fork v3HK v3CQ -- expect true: the stall registers
#eval v3ForkSigB v3ForkX v3DK v3CQ -- expect true: the mate stall registers
#eval v3ForkSigB pnCasForkMerge v3HK v3CQ -- expect false: the next-in-line REFUSES
#eval v3ForkPinB pnCasForkMerge v3HK v3CQ -- expect false: the pin leg alone refuses
#eval v3RungAt v3Fork .club -- expect 0: the pinned cargo's rung
#eval v3RungAt pnCasForkMerge .club -- expect 11: the next-in-line's own rung

#eval! do
  if l4RowForkSigCorrected then
    IO.println "CANONV3 SIGNATURE CORRECTION (amr_129d6300b): ALL GATES HOLD —"
    IO.println "The corrected forkEvidence (live at the stall: bare twin licensed +"
    IO.println "twin covered by PINNED opposite-color cargo + the operational"
    IO.println "slide-trial lighting the other arm) registers at BOTH standing-fork"
    IO.println "stalls (v3Fork and its mate); the covered twins are UNLICENSED there"
    IO.println "(one licensed + one covered, never both — the census verdict's"
    IO.println "intra-state emptiness respected); the same-color rungs pinned at the"
    IO.println "pair rank by the bare twin's stackable-now (not by CanRaise of the"
    IO.println "covered twin). The benign next-in-line MERGE cell REFUSES the"
    IO.println "signature: the cargo's own rung waits (the pin leg fails) though the"
    IO.println "slide-trial alone fires — the false-positive guard verified."
  else
    throw (IO.userError "SIGNATURE CORRECTION: A GATE FAILED")

/-! ## The second signature correction (amr_129d79e2b) — the GAP FORM, decide-graded

CanRaiseS is in the library now (Orig/CanV3, the skeleton's exact
shape: 'now' vanilla + 'via' licensed reversible slide).  The GAP
FORM (the relay's forkEvidence): CanRaiseS x ∧ CanRaiseS x.twin ∧
¬CanRaise-vanilla x.twin ∧ coveredIn x.twin ∧ cargo-shape
(next-rank, opposite color, rung-pinned) — contention at the
SWAP grade that is NOT contention at the vanilla grade.  The
trial is DERIVED (a theorem at the skeleton); at the battery it
is decide-verified at every stall.  The two-predicates
distinction: the census's TwinContended-emptiness was won at the
VANILLA grade and stands intact.  -/

/-- The tabToTab menu (the same product shape as the pull menu). -/
def v3TabToTabMenu : List Move :=
  Card.universe.flatMap fun c =>
    (Anchor.all.map fun a => Move.tabToTab c (Sum.inl a)) ++
    (Card.universe.map fun z => Move.tabToTab c (Sum.inr z))

/-- The one-step slide neighbors (licensed tabToTab images). -/
def v3SlidesAt (st : State) : List State :=
  (v3TabToTabMenu).filterMap (fun m => st.step m)

/-- The DEPTH-1 swap-grade mirror: vanilla now, or a slide
neighbor where vanilla lights (the via-clause's first
unrolling; at the crafted cells the slides are noreveal,
one-another inverses — reversibility decided in the fired-both-
ways rows — so the mirror reads the closure honestly). -/
def v3CanRaiseS1B (st : State) (c : Card) : Bool :=
  canRaiseB st c || (v3SlidesAt st).any (fun s' => canRaiseB s' c)

/-- THE GAP FORM (the corrected forkEvidence), one named pair
(x, d): swap-grade lifts on BOTH twins, the covered twin NOT
vanilla, covered by a pinned opposite-color next-rank cargo. -/
def v3GapFormB (st : State) (x d : Card) : Bool :=
  v3CanRaiseS1B st x &&
  v3CanRaiseS1B st x.twin &&
  !(canRaiseB st x.twin) &&
  v3CoveredInB st x.twin &&
  decide (d.rank.toIdx + 1 = x.rank.toIdx) &&
  !(v3TwinSuitB d.suit x.suit) &&
  decide (v3RungAt st d.suit < d.rank.toIdx)

/-- The gap-form rows, decided:

- v3Fork / v3ForkX (both stalls): the gap form FIRES — swap-grade
  contention on both twins (the covered twin lifts only via the
  cargo slide), the vanilla grade's gap open (the covered twin
  unlicensed), the cargo pinned (clubs 0 < the queen's 11).
- THE DERIVED TRIAL at the stalls (forkPoint_trial decide-grade):
  the slide lands on the mate cell exactly and lights the
  covered twin VANILLA there.
- pnCasForkMerge (the next-in-line): the gap form REFUSES — the
  cargo's own rung waits (11 = 11, not pinned) though both twins
  lift vanilla-or-via: the cascade dissolves it (the merge rows).
- v3Bare (the benign independence slice): the gap form REFUSES —
  no covered twin (coveredIn false on both members); the vanilla
  census verdict is exactly this slice.
- THE CanRaiseS AUDIT (the request's consequence-6): the battery
  rows that already proved CanRaiseS facts under other names —
  the parked queen lights VIA a slide off pnCasBareExt (row-A's
  dissolve-extending road), the merge cargo lifts VANILLA (no
  slide needed), the v3Chain enablement lifts are vanilla-only
  cascades, and the earlier l4RowForkSigCorrected rows are the
  derived-trial content at depth one.
-/
def l4RowGapForm : Bool :=
  -- the standing-fork stalls: gap fires both ways
  v3GapFormB v3Fork v3HK v3CQ &&
  v3GapFormB v3ForkX v3DK v3CQ &&
  -- the derived trial: the slide lands the mate cell, lights vanilla
  decide (v3Fork.step (Move.tabToTab v3CQ (Sum.inr v3HK)) = some v3ForkX) &&
  canRaiseB v3ForkX v3DK &&
  decide (v3ForkX.step (Move.tabToTab v3CQ (Sum.inr v3DK)) = some v3Fork) &&
  canRaiseB v3Fork v3HK &&
  -- the vanilla grade's gap (covered twins unlicensed at the stalls)
  !(canRaiseB v3Fork v3DK) &&
  !(canRaiseB v3ForkX v3HK) &&
  -- the next-in-line refuses at the pin leg
  !(v3GapFormB pnCasForkMerge v3HK v3CQ) &&
  decide (v3RungAt pnCasForkMerge .club = v3CQ.rank.toIdx) &&
  -- the benign independence slice refuses at coveredIn
  !(v3CoveredInB v3Bare v3HK) &&
  !(v3CoveredInB v3Bare v3DK) &&
  !(v3GapFormB v3Bare v3HK v3CQ) &&
  -- the CanRaiseS audit rows (facts proved under other names):
  -- the parked queen lights VIA the slide off row-A's pose
  !(canRaiseB pnCasBareExt v3CQ) &&
  (v3SlidesAt pnCasBareExt).any (fun s' => canRaiseB s' v3CQ) &&
  -- the merge cargo lifts VANILLA (the cascade needs no slide)
  canRaiseB pnCasForkMerge v3CQ &&
  -- the v3Chain enablement is vanilla-only (the lighting row)
  canRaiseB (v3Fired v3Chain v3HJ) v3HQ

-- The gap-form census numbers (printed for the ledger):
#eval v3GapFormB v3Fork v3HK v3CQ -- expect true: the stall gap fires
#eval v3GapFormB v3ForkX v3DK v3CQ -- expect true: the mate gap fires
#eval v3GapFormB pnCasForkMerge v3HK v3CQ -- expect false: next-in-line refuses
#eval v3GapFormB v3Bare v3HK v3CQ -- expect false: benign slice refuses
#eval v3CanRaiseS1B v3Fork v3DK -- expect true: the covered twin lifts VIA
#eval v3CanRaiseS1B v3Fork v3HK -- expect true: the bare twin lifts NOW

#eval! do
  if l4RowGapForm then
    IO.println "CANONV3 GAP FORM (amr_129d79e2b): ALL GATES HOLD —"
    IO.println "The swap-grade license CanRaiseS ('now' vanilla + 'via' licensed"
    IO.println "reversible slide) mirrors the skeleton exactly in Orig/CanV3."
    IO.println "The GAP FORM fires at BOTH standing-fork stalls: swap-grade"
    IO.println "contention on both twins, the covered twin NOT vanilla, cargo"
    IO.println "pinned — contention at the swap grade that is NOT contention at"
    IO.println "the vanilla grade. The derived trial decide-verified (the slide"
    IO.println "lands the mate cell, lights the covered twin vanilla). The"
    IO.println "next-in-line merge REFUSES at the pin leg (its own rung waits);"
    IO.println "the benign independence slice REFUSES at coveredIn — the two-"
    IO.println "predicates distinction: the census's TwinContended-emptiness"
    IO.println "was the VANILLA grade and stands intact. The CanRaiseS audit:"
    IO.println "the parked queen lights VIA, the merge cargo lifts VANILLA, the"
    IO.println "enablement chain is vanilla-only — the battery had already"
    IO.println "proved these cascade facts under other names."
  else
    throw (IO.userError "GAP FORM: A GATE FAILED")
