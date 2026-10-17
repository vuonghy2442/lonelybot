import Orig2.Vocab
import Orig2.Kit

/-!
# Orig2.OrbitFactor — THE ORBIT-FACTOR MACHINERY CARD

THE ORBIT-FACTOR MIGRATION, chartered 2026-10-17 (the claims
ledger's `sameOrbit_factor`, `Orig2/Claims.lean` §1B): the card
that discharges the phase factorization —

```
theorem sameOrbit_factor {u v : State} (hwf₁ : u.WF) (hwf₂ : v.WF) :
    sameOrbitSetoid.r u v ↔ ∃ z, NoDrawPlayW u z ∧ SWRotW z v
```

— a class membership is a draw-free board reshuffle to a
phase-mate, then a pure rotation round.

## LINEAGE (the frozen templates this card restates)

The frozen pair `Orig/OrbitFactor.lean` + `Orig/OrbitFactorC.lean`
is the correctness oracle; every row here cites its template's
file:line.  The frozen homes are NOT importable in this library
(the seam collision: everything above `Orig.Play` transitively
re-exports the root `reversibleAtW` of `Orig.Fate.lean`, which
would re-declare the registry's carrier), so per the house dedup
discipline ALL supporting rows arrive here as PER-FILE PRIVATE
KIT, ported from the frozen tier with per-row source citations.

## THE MIGRATION'S ONE TECHNICAL DEPARTURE (recorded honestly)

The frozen witness-grade bubbling (`pull_one`,
`Orig/OrbitFactorC.lean:297`) re-witnesses a pulled BOARD leg
through the frozen classification bridge
(`reversibleAtW_stepDraw_frame` rides `reversible_iff_of`, the
`Orig/Classify.lean` oracle at WF).  That bridge is the
classification card's territory here (claims §1, still a priced
stub), so this card takes a WITNESS-TRANSPORT route instead: the
general commutation square's LANDING-EXCHANGE grade (the board
leg crossed before the draw lands at the board leg's own landing
exact) lets the pulled leg's ORIGINAL return play re-run verbatim
behind one re-drawn letter, closing with the front draw's own
certified return play — an explicit composite undo play with no
classification, no WF transport (no `step_wf` freight at all),
and no draw-cycle injectivity.  The per-leg gates shrink from
`WF` to `0 < drawStep` (carried by zone-keeps from the theorem's
own WF premises).

## THE PIECES (landed per green batch)

* §1 THE GENERAL DISJOINT-FIELD COMMUTATION — one general square
  at the field-equation grade (templates: the three ~50-line
  squares of `Orig/OrbitFactor.lean:73-260`, now ONE row plus a
  few lines per table move).
* §2 THE DRAWS-LAST BUBBLING — `shuffle_drawsLast` (template
  `Orig/OrbitFactorC.lean:371`), via the restated `pull_one`.
* §3 THE DRAW-BLOCK TRANSPLANT — `draw_play_transplant`
  (template `Orig/OrbitFactor.lean:520-566`), riding the private
  Phase loop algebra port of §0.
* §4 THE ASSEMBLY — `sameOrbit_factor_fwd` +
  `sameOrbit_factor` (templates `Orig/OrbitFactorC.lean:442-487`)
  and the claims-layer promotion.

NOT this card's territory (the frozen §4 quotient plumbing —
`swCompSetoid`/`SWPhase`/`mkSW`, `Orig/OrbitFactor.lean:579-676`):
deliberately cut per the 2026-10-17 clean split; resurrecting it
needs an owner intent line.

## HOUSE COMPLIANCE

Zero sorry on proved heads; zero `Classical.choice` (all splits
decide); per-file private kit for every frozen row (cited); the
audit battery at the file's end prints each proved head —
`[propext]`/`[propext, Quot.sound]` only.
-/

/-! ## §0. THE PRIVATE KIT (restatements, cited — the general rows
promoted to `Orig2/Kit.lean`, owner decree 2026-10-17; the cards'
own letters stay here) -/

/-! ### §0.1 Field-reader congruences (Twin ports)

The search-read congruences every board leg's firing transfer
rides: each `State` read consumed by the three table movers is
determined by its field (`Orig/Twin.lean:143-201`). -/

/-- The `firstWhere` congruence (PORTED VERBATIM from
`Orig/Twin.lean:143`). -/
private theorem firstWhere_congr {α : Type} {p q : α → Bool}
    (h : ∀ x, p x = q x) : ∀ {l : List α}, firstWhere p l = firstWhere q l := by
  intro l
  induction l with
  | nil => rfl
  | cons x t ih =>
      rw [firstWhere, firstWhere, h x]
      split
      · rfl
      · exact ih

/-- The pile-top read is a piles-field read (PORTED VERBATIM from
`Orig/Twin.lean:164`). -/
private theorem topOf_congr {u v : State} (a : Anchor) (h : u.piles = v.piles) :
    u.topOf a = v.topOf a := by
  show (u.piles a).top = (v.piles a).top
  exact congrArg Pile.top (congrFun h a)

/-- The top search is a piles-field read (PORTED VERBATIM from
`Orig/Twin.lean:170`). -/
private theorem pileOfTop_congr {u v : State} (z : Card) (h : u.piles = v.piles) :
    u.pileOfTop z = v.pileOfTop z := by
  show firstWhere (fun a => decide (u.topOf a = some z)) Anchor.all = _
  exact firstWhere_congr (p := fun a => decide (u.topOf a = some z))
    (q := fun a => decide (v.topOf a = some z)) (fun a => by rw [topOf_congr a h])
    (l := Anchor.all)

/-- The placement guard is a piles-field read (PORTED VERBATIM
from `Orig/Twin.lean:178`). -/
private theorem canPlace_congr {u v : State} (c : Card) (b : Base)
    (h : u.piles = v.piles) : u.canPlace c b = v.canPlace c b := by
  cases b with
  | inl a =>
      show ((u.piles a).isEmpty && decide (c.rank = Rank.king))
          = ((v.piles a).isEmpty && decide (c.rank = Rank.king))
      rw [congrArg Pile.isEmpty (congrFun h a)]
  | inr z =>
      show (match u.pileOfTop z with
        | some _ => canSitOn c z | none => false) = _
      rw [pileOfTop_congr z h]
      rfl

/-- The foundation-next read is a found-field read (PORTED
VERBATIM from `Orig/Twin.lean:192`). -/
private theorem nextUp_congr {u v : State} (c : Card) (h : u.found = v.found) :
    u.nextUp c = v.nextUp c :=
  congrArg (fun (f : Suit → List Card) => decide (c.rank.toIdx = (f c.suit).length)) h

/-- The foundation-top read is a found-field read (PORTED
VERBATIM from `Orig/Twin.lean:197`). -/
private theorem foundTop_congr {u v : State} (s : Suit) (h : u.found = v.found) :
    u.foundTop s = v.foundTop s := by
  simp only [State.foundTop]
  rw [congrFun h s]

/-! ### §0.2 The field-equation rows (Irreversible ports)

`setPile`/`setFound` read the zone fields off the parent record
by iota; the frozen projections ride these `rfl` rows
(`Orig/Irreversible.lean:191-221`). -/

/-! The field-equation rows (PORTED from
`Orig/Irreversible.lean:191-221`) ride the promoted physics kit
`Orig2/Kit.lean` (`setPile_stock/_waste/_drawStep`,
`setFound_stock/_waste/_piles/_drawStep`, the seam-carried
`putCard_stock/_waste/_found/_drawStep` and
`putRun_stock/_waste/_found/_drawStep`); this card keeps only the
one row the kit does not carry. -/

/-- `setPile`'s piles write, as the pointwise record (PORTED from
`Orig/Irreversible.lean:203`; kept here — the kit carries only the
afterRunRemoved readings). -/
private theorem setPile_piles (st : State) (a : Anchor) (p : Pile) :
    (st.setPile a p).piles = (fun a' => if a' = a then p else st.piles a') := rfl

/-! ### §0.3 The placement congruences (EdgeKit ports)

A `putCard`/`putRun` at equal piles boards agrees everywhere (the
placement walk reads only the piles; `Orig/EdgeLabel.lean:2682-2733`).
-/

/-- The `setPile` piles write agrees at equal boards (PORTED from
`Orig/EdgeLabel.lean:2682`). -/
private theorem setPile_piles_congr {u v : State} (a : Anchor) (p : Pile)
    (h : u.piles = v.piles) : (u.setPile a p).piles = (v.setPile a p).piles := by
  rw [setPile_piles, setPile_piles, h]

/-- A `putCard` at equal piles boards agrees everywhere (PORTED
VERBATIM from `Orig/EdgeLabel.lean:2688`). -/
private theorem putCard_piles_congr {u v : State} (c : Card) (b : Base)
    (h : u.piles = v.piles) : (u.putCard c b).piles = (v.putCard c b).piles := by
  cases b with
  | inl a =>
      rw [putCard_eq_inl u c a, putCard_eq_inl v c a,
        setPile_piles, setPile_piles, h]
  | inr z =>
      have hc : v.pileOfTop z = u.pileOfTop z := (pileOfTop_congr z h).symm
      cases hq : u.pileOfTop z with
      | none =>
          rw [show u.putCard c (Sum.inr z) = u from by simp only [State.putCard, hq],
              show v.putCard c (Sum.inr z) = v from by
                (simp only [State.putCard]; rw [hc, hq]),
              h]
      | some k =>
          rw [show u.putCard c (Sum.inr z)
                = u.setPile k { u.piles k with faceUp := (u.piles k).faceUp ++ [c] } from by
                simp only [State.putCard, hq],
              show v.putCard c (Sum.inr z)
                = v.setPile k { v.piles k with faceUp := (v.piles k).faceUp ++ [c] } from by
                (simp only [State.putCard]; rw [hc, hq]),
              setPile_piles, setPile_piles, h]

/-- A `putRun` at equal piles boards agrees everywhere (PORTED
VERBATIM from `Orig/EdgeLabel.lean:2712`). -/
private theorem putRun_piles_congr {u v : State} (run : List Card) (b : Base)
    (h : u.piles = v.piles) : (u.putRun run b).piles = (v.putRun run b).piles := by
  cases b with
  | inl a =>
      rw [putRun_eq_inl u run a, putRun_eq_inl v run a,
        setPile_piles, setPile_piles, h]
  | inr z =>
      have hc : v.pileOfTop z = u.pileOfTop z := (pileOfTop_congr z h).symm
      cases hq : u.pileOfTop z with
      | none =>
          rw [show u.putRun run (Sum.inr z) = u from by simp only [State.putRun, hq],
              show v.putRun run (Sum.inr z) = v from by
                (simp only [State.putRun]; rw [hc, hq]),
              h]
      | some k =>
          rw [show u.putRun run (Sum.inr z)
                = u.setPile k { u.piles k with faceUp := (u.piles k).faceUp ++ run } from by
                simp only [State.putRun, hq],
              show v.putRun run (Sum.inr z)
                = v.setPile k { v.piles k with faceUp := (v.piles k).faceUp ++ run } from by
                (simp only [State.putRun]; rw [hc, hq]),
              setPile_piles, setPile_piles, h]

/-! ### §0.4 The step inversions (Irreversible ports)

One per board-move constructor (`Orig/Irreversible.lean:471-590`).
-/

/-! The step inversions (PORTED VERBATIM from
`Orig/Irreversible.lean:511/:555/:572`) ride the promoted physics
kit `Orig2/Kit.lean` (`step_tabToFound_inv`,
`step_foundToTab_inv`, `step_tabToTab_inv`). -/

/-! ### §0.5 The draw record rows (Irreversible/EdgeLabel ports)

A fired draw keeps the board, the draw step, and conserves the
cycle pool (`Orig/Irreversible.lean:438-449`,
`Orig/EdgeLabel.lean:2736-2743`) — plus the ZONE-DETERMINED
REFIRE (`stepDraw_rel`, `Orig/Twin.lean:207`): the draw's firing
and landing zone are functions of the zone alone. -/

/-! The recycle and draw record rows (PORTED from
`Orig/Irreversible.lean:438/:445`, `Orig/Phase.lean:247`,
`Orig/EdgeLabel.lean:2736`) ride the promoted physics kit
`Orig2/Kit.lean` — `recycle_piles`, `recycle_found`,
`recycle_drawStep`, `stepDraw_piles`, `stepDraw_found`,
`draw_drawStep`; this card keeps its own `stepDraw_rel` (the Twin
field-determined row) and a name-compatible alias for
`draw_drawStep`. -/

/-- A successful draw keeps the draw step (PORTED from
`Orig/EdgeLabel.lean:2736`; a Kit alias over `draw_drawStep`). -/
private theorem stepDraw_drawStep {x u : State} (hd : x.stepDraw = some u) :
    u.drawStep = x.drawStep := draw_drawStep hd

/-- **The draw is field-determined** (PORTED VERBATIM from
`Orig/Twin.lean:207`): two states that agree on stock, waste and
draw step draw to outcomes that keep their own piles, found and
draw step and share the dealt stock and waste. -/
private theorem stepDraw_rel {u v u₁ : State}
    (hstock : v.stock = u.stock) (hwaste : v.waste = u.waste)
    (hdraw : v.drawStep = u.drawStep)
    (hu : u.stepDraw = some u₁) :
    ∃ v₁ : State, v.stepDraw = some v₁ ∧
      v₁.piles = v.piles ∧ u₁.piles = u.piles ∧ v₁.found = v.found ∧
      u₁.found = u.found ∧ v₁.drawStep = v.drawStep ∧ u₁.drawStep = u.drawStep ∧
      v₁.stock = u₁.stock ∧ v₁.waste = u₁.waste := by
  cases hus : u.stock with
  | nil =>
      cases huw : u.waste with
      | nil =>
          exfalso
          have hdead : u.stepDraw = none := by
            simp [State.stepDraw, State.dealStock, State.recycle, hus, huw]
          rw [hdead] at hu
          exact absurd hu (by simp)
      | cons w ws =>
          have hvs : v.stock = [] := hstock.trans hus
          have hvw : v.waste = w :: ws := hwaste.trans huw
          have hru : State.recycle u = { u with stock := (w :: ws).reverse, waste := [] } := by
            simp [State.recycle, hus, huw]
          have hrv : State.recycle v = { v with stock := (w :: ws).reverse, waste := [] } := by
            simp [State.recycle, hvs, hvw]
          rw [show u.stepDraw = State.dealStock (State.recycle u) from rfl, hru] at hu
          cases hrr : (w :: ws).reverse with
          | nil =>
              have hd : State.dealStock { u with stock := (w :: ws).reverse, waste := [] } = none := by
                rw [hrr]
                rfl
              rw [hd] at hu
              exact absurd hu (by simp)
          | cons r rs =>
              rw [hrr] at hu hru hrv
              have hfU : State.dealStock { u with stock := (r :: rs), waste := [] } =
                  some { u with stock := (State.dealUpTo u.drawStep (r :: rs)).snd, waste := (State.dealUpTo u.drawStep (r :: rs)).fst.reverse ++ [] } := by
                simp [State.dealStock]
              have hu' : State.dealStock { u with stock := (r :: rs), waste := [] } = some u₁ := hu
              have hui : u₁ = { u with stock := (State.dealUpTo u.drawStep (r :: rs)).snd, waste := (State.dealUpTo u.drawStep (r :: rs)).fst.reverse ++ [] } :=
                Option.some.inj (hu'.symm.trans hfU)
              rw [hui]
              refine ⟨{ v with stock := (State.dealUpTo v.drawStep (r :: rs)).snd, waste := (State.dealUpTo v.drawStep (r :: rs)).fst.reverse ++ [] }, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
              · rw [show v.stepDraw = State.dealStock (State.recycle v) from rfl, hrv]
                simp [State.dealStock]
              · rw [hdraw]
              · rw [hdraw]
  | cons s ss =>
      have hvs : v.stock = s :: ss := hstock.trans hus
      have hru : State.recycle u = u := by simp [State.recycle, hus]
      have hrv : State.recycle v = v := by simp [State.recycle, hvs]
      rw [show u.stepDraw = State.dealStock (State.recycle u) from rfl, hru] at hu
      have hfU : State.dealStock u = some { u with stock := (State.dealUpTo u.drawStep (s :: ss)).snd, waste := (State.dealUpTo u.drawStep (s :: ss)).fst.reverse ++ u.waste } := by
        simp [State.dealStock, hus]
      have hui : u₁ = { u with stock := (State.dealUpTo u.drawStep (s :: ss)).snd, waste := (State.dealUpTo u.drawStep (s :: ss)).fst.reverse ++ u.waste } :=
        Option.some.inj (hu.symm.trans hfU)
      rw [hui]
      refine ⟨{ v with stock := (State.dealUpTo v.drawStep (s :: ss)).snd, waste := (State.dealUpTo v.drawStep (s :: ss)).fst.reverse ++ v.waste }, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
      · rw [show v.stepDraw = State.dealStock (State.recycle v) from rfl, hrv]
        simp [State.dealStock, hvs]
      · rw [hdraw]
      · rw [hdraw, hwaste]

/-! ### §0.6 The cycle-count rows (Irreversible/Phase ports)

`cycleCount` — cards outside the foundations, the strictly-dropping
measure of the waste rows (`Orig/Irreversible.lean:66`); the two
waste spenders and the never-rising play lift
(`Orig/Phase.lean:382-417, 497-512`). -/

/-! The cycle-count rows (PORTED from `Orig/Phase.lean:123/:181/:204/:382/:401/:473/:497`) ride the promoted physics kit `Orig2/Kit.lean` — the `cycleCount` measure, `dealUpTo_lens`, `recycle_cycle`, `run_cycleCount_le`, `draw_cycleCount` (by name), and the inversions-shaped strict rows `cycleCount_step_wasteToFound/_wasteToTab`.  The card's own `cycleCount_lt_*` heads stay below as one-line Kit delegations (its journey rows keep these letters), and `step_cycleCount_le` delegates to Kit's `cycleCount_step`. -/

/-- Building the waste top onto its foundation spends exactly one
cycle-count unit (PORTED VERBATIM from `Orig/Phase.lean:382`;
now a Kit delegation over `cycleCount_step_wasteToFound`). -/
private theorem cycleCount_lt_wasteToFound {x y : State} {c : Card}
    (h : State.step x (.wasteToFound c) = some y) :
    cycleCount y < cycleCount x := by
  have := cycleCount_step_wasteToFound h
  omega

/-- Building the waste top onto the tableau spends exactly one
cycle-count unit (PORTED VERBATIM from `Orig/Phase.lean:401`;
now a Kit delegation over `cycleCount_step_wasteToTab`). -/
private theorem cycleCount_lt_wasteToTab {x y : State} {c : Card} {b : Base}
    (h : State.step x (.wasteToTab c b) = some y) :
    cycleCount y < cycleCount x := by
  have := cycleCount_step_wasteToTab h
  omega

/-- **The per-move step table** (PORTED from `Orig/Phase.lean:473`;
now a Kit delegation over `cycleCount_step`). -/
private theorem step_cycleCount_le {x y : State} : ∀ m : Move,
    State.step x m = some y → cycleCount y ≤ cycleCount x :=
  fun _ h => cycleCount_step h
/-! ### §0.7 No waste mover is ever a witness leg

The two commitment rows at WITNESS grade and UNCONDITIONALLY in
the position (the descent needs nothing but the witness's own
firing) — restated directly (the frozen route via
`Orig/Mono.lean`'s `irr_of_desc` and the `Orig/Fate.lean` semantic
pair is not importable here; the direct descent refutes the
witness's own return play without them).  Templates:
`Orig/ForkStateUniqGate.lean:377-397` (fired-form there), the
measures `Orig/Irreversible.lean:66` and `Orig/Phase.lean:497-512`. -/

/-- **No waste raise ever rides** (restated at witness grade;
template `Orig/ForkStateUniqGate.lean:377`): the mover strictly
drops the cycle count while no play raises it, so the carrier's
own return play cannot exist. -/
private theorem journey_never_wasteToFound (st : State) (c : Card) :
    ¬ reversibleAtW st (Move.wasteToFound c) := by
  rintro ⟨s₁, play, hstep', hrun⟩
  have hlt : cycleCount s₁ < cycleCount st := cycleCount_lt_wasteToFound hstep'
  have hle := run_cycleCount_le hrun
  omega

/-- **No waste placement ever rides** (witness grade; template
`Orig/ForkStateUniqGate.lean:389`). -/
private theorem journey_never_wasteToTab (st : State) (c : Card) (b : Base) :
    ¬ reversibleAtW st (Move.wasteToTab c b) := by
  rintro ⟨s₁, play, hstep', hrun⟩
  have hlt : cycleCount s₁ < cycleCount st := cycleCount_lt_wasteToTab hstep'
  have hle := run_cycleCount_le hrun
  omega

/-! ## §1. THE GENERAL DISJOINT-FIELD COMMUTATION

The frozen card carried three ~50-line squares, one per table
mover (`Orig/OrbitFactor.lean:73-260`); this section's GENERAL
square runs once at the field-equation grade.  The two read/write
field-disjointness rows per mover (`board_fire_congr`,
`board_fire_zone`) are each a few lines over the congruence and
field kits; the square then assembles via the draw records' two
field facts: a fired draw keeps the board (`stepDraw_piles`/
`stepDraw_found`), and the draw refires zone-determined with the
same landing zone (`stepDraw_rel`). -/

/-- The three table movers (the board's move alphabet; the waste
movers never ride a witness journey by §0.7, the draw is its own
letter). -/
private def isBoardMove (m : Move) : Bool :=
  match m with
  | .tabToFound _ | .foundToTab _ _ | .tabToTab _ _ => true
  | _ => false

/-- **Board fire congruence** (the READ half of the field
disjointness): a fired board leg at `x` fires equally at any state
sharing its board (piles and found), with the same landing board —
replaces the guard-transfer halves of the frozen squares
(templates `Orig/OrbitFactor.lean:73-260`, generalized). -/
private theorem board_fire_congr {x y s' : State} {m : Move}
    (hboard : isBoardMove m = true)
    (hp : x.piles = y.piles) (hf : x.found = y.found)
    (h : x.step m = some s') :
    ∃ t, y.step m = some t ∧ t.piles = s'.piles ∧ t.found = s'.found := by
  cases m with
  | draw => simp [isBoardMove] at hboard
  | wasteToFound c => simp [isBoardMove] at hboard
  | wasteToTab c b => simp [isBoardMove] at hboard
  | tabToFound c =>
      obtain ⟨hnext₁, k, hpo₁, hrec⟩ := step_tabToFound_inv h
      have hnext : y.nextUp c = true := by rw [← nextUp_congr c hf]; exact hnext₁
      have hpo : y.pileOfTop c = some k := by rw [← pileOfTop_congr c hp]; exact hpo₁
      refine ⟨_, step_tabToFound_splice hnext hpo, ?_, ?_⟩
      · rw [hrec]
        show (fun a' => if a' = k then
                Pile.afterRunRemoved (y.piles k) (chop (y.piles k).faceUp) else y.piles a')
            = (fun a' => if a' = k then
                Pile.afterRunRemoved (x.piles k) (chop (x.piles k).faceUp) else x.piles a')
        simp only [hp]
      · rw [hrec]
        show (fun s'' => if s'' = c.suit then y.found c.suit ++ [c] else y.found s'')
            = (fun s'' => if s'' = c.suit then x.found c.suit ++ [c] else x.found s'')
        simp only [hf]
  | foundToTab c b =>
      obtain ⟨c', htop₁, hceq, hcp₁, hrec⟩ := step_foundToTab_inv h
      have htop : y.foundTop c.suit = some c := by
        rw [← foundTop_congr c.suit hf]
        rw [htop₁, hceq]
      have hcp : y.canPlace c b = true := by rw [← canPlace_congr c b hp]; exact hcp₁
      refine ⟨_, step_foundToTab_splice htop hcp, ?_, ?_⟩
      · rw [hrec]
        have hsp : (y.setFound c.suit (chop (y.found c.suit))).piles
            = (x.setFound c.suit (chop (x.found c.suit))).piles := hp.symm
        exact putCard_piles_congr c b hsp
      · rw [hrec, putCard_found, putCard_found]
        show (fun s'' => if s'' = c.suit then chop (y.found c.suit) else y.found s'')
            = (fun s'' => if s'' = c.suit then chop (x.found c.suit) else x.found s'')
        simp only [hf]
  | tabToTab c b =>
      obtain ⟨a, hh₁, hcp₁, hfr₁, hrec⟩ := step_tabToTab_inv h
      have hhy : y.pileHolding c = some a := by
        rw [pileHolding_congr hp.symm]
        exact hh₁
      have hcp : y.canPlace c b = true := by rw [← canPlace_congr c b hp]; exact hcp₁
      have hfrun : fromCard c (x.piles a).faceUp = fromCard c (y.piles a).faceUp :=
        congrArg (fromCard c) (congrArg Pile.faceUp (congrFun hp a))
      have hstepy : y.step (Move.tabToTab c b) = some
          ((y.setPile a (Pile.afterRunRemoved (y.piles a) (below c (y.piles a).faceUp))).putRun
            (fromCard c (y.piles a).faceUp) b) := by
        simp only [State.step, hhy, hcp]
        cases hwfr : fromCard c (y.piles a).faceUp with
        | nil =>
            rw [← hfrun] at hwfr
            exact absurd hwfr hfr₁
        | cons w ws => rfl
      refine ⟨_, hstepy, ?_, ?_⟩
      · rw [hrec, hfrun]
        exact putRun_piles_congr _ _ (show
            (y.setPile a
              (Pile.afterRunRemoved (y.piles a) (below c (y.piles a).faceUp))).piles
            = (x.setPile a
              (Pile.afterRunRemoved (x.piles a) (below c (x.piles a).faceUp))).piles from by
          show (fun a' => if a' = a then
                  Pile.afterRunRemoved (y.piles a) (below c (y.piles a).faceUp)
                else y.piles a')
              = (fun a' => if a' = a then
                  Pile.afterRunRemoved (x.piles a) (below c (x.piles a).faceUp)
                else x.piles a')
          simp only [hp])
      · rw [hrec, hfrun, putRun_found, putRun_found, setPile_found, setPile_found]
        exact hf.symm

/-- **Board fire zone-keep** (the WRITE half of the field
disjointness): a fired board leg keeps the draw zone (stock,
waste, draw step) verbatim — the zone-keep half of the frozen
squares, generalized (templates `Orig/Phase.lean:421-469`
`*_fixed` rows, `Orig/OrbitFactorC.lean:207` `leg_zone_keep`).
-/
private theorem board_fire_zone {x s' : State} {m : Move}
    (hboard : isBoardMove m = true) (h : x.step m = some s') :
    s'.stock = x.stock ∧ s'.waste = x.waste ∧ s'.drawStep = x.drawStep := by
  cases m with
  | draw => simp [isBoardMove] at hboard
  | wasteToFound c => simp [isBoardMove] at hboard
  | wasteToTab c b => simp [isBoardMove] at hboard
  | tabToFound c =>
      obtain ⟨-, a, -, hs⟩ := step_tabToFound_inv h
      rw [hs]
      exact ⟨rfl, rfl, rfl⟩
  | foundToTab c b =>
      obtain ⟨c₀, ht, hce, hcp, hs⟩ := step_foundToTab_inv h
      rw [hs]
      exact ⟨by rw [putCard_stock, setFound_stock],
        by rw [putCard_waste, setFound_waste],
        by rw [putCard_drawStep, setFound_drawStep]⟩
  | tabToTab c b =>
      obtain ⟨a, hh, hcp, hfr, hs⟩ := step_tabToTab_inv h
      rw [hs]
      exact ⟨by rw [putRun_stock, setPile_stock],
        by rw [putRun_waste, setPile_waste],
        by rw [putRun_drawStep, setPile_drawStep]⟩

/-- **THE GENERAL SQUARE** — the disjoint-field commutation row,
ONE for all three table movers: a Friedman-draw at `st` and a
fired board leg at the drawn landing exchange their order AND
their landings: the board leg fires at `st` with landing `t`, and
the draw refires at `t` to the very same successor `s₂` (the
fired pair's composite commutes exactly).  Replaces the three
~50-line squares of the frozen card
(`Orig/OrbitFactor.lean:73-260`) by one field-equation assembly:
the board leg's fire and landing-board are board-determined
(`board_fire_congr`, the draw kept the board), its landing zone is
`st`'s (`board_fire_zone`), and the draw refires zone-determined
with the drawn landing's own zone and `t`'s own board
(`stepDraw_rel`). -/
private theorem board_square {st s₁ s₂ : State} {m : Move}
    (hd : st.stepDraw = some s₁) (hm : s₁.step m = some s₂)
    (hboard : isBoardMove m = true) :
    ∃ t, st.step m = some t ∧ t.stepDraw = some s₂ := by
  have hbp : s₁.piles = st.piles := stepDraw_piles hd
  have hbf : s₁.found = st.found := stepDraw_found hd
  obtain ⟨t, hfireX, htp, htf⟩ := board_fire_congr hboard hbp hbf hm
  obtain ⟨hz1, hz2, hz3⟩ := board_fire_zone hboard hfireX
  obtain ⟨hE31, hE32, hE33⟩ := board_fire_zone hboard hm
  obtain ⟨w, hwfire, hpw, -, hfw, -, hdw, hsd, hws, hww⟩ :=
    stepDraw_rel hz1 hz2 hz3 hd
  have heq : w = s₂ := by
    apply State.ext
    · exact hfw.trans htf
    · exact hpw.trans htp
    · exact hws.trans hE31.symm
    · exact hww.trans hE32.symm
    · exact (hdw.trans hz3).trans (hE33.trans hsd).symm
  subst heq
  exact ⟨t, hfireX, hwfire⟩

/-- **§1: the disjoint-field commutation lemma** (dispatched;
template `Orig/OrbitFactor.lean:261`).  Any WITNESS leg at a
drawn landing commutes with the drawing step: the leg fires at
the origin too, and the draw fires at the leg's origin-landing
with the drawn landing's own successor.  A draw leg coincides
with the pushed draw (the identical move); the waste movers
cannot be witness legs (§0.7); the three board movers run THE
ONE general square. -/
theorem board_draw_commute {st s₁ s₂ : State} {m : Move}
    (hd : st.stepDraw = some s₁)
    (hm : s₁.step m = some s₂) (hw : reversibleAtW s₁ m) :
    ∃ t, st.step m = some t ∧ t.stepDraw = some s₂ := by
  cases m with
  | draw => exact ⟨s₁, hd, hm⟩
  | wasteToFound c => exact absurd hw (journey_never_wasteToFound s₁ c)
  | wasteToTab c b => exact absurd hw (journey_never_wasteToTab s₁ c b)
  | tabToFound c => exact board_square hd hm rfl
  | foundToTab c b => exact board_square hd hm rfl
  | tabToTab c b => exact board_square hd hm rfl

/-! ## §1.5. THE PHASE KIT (private ports for pieces §2 and §3)

The Phase loop algebra the bubbling and the transplant ride —
`inPhase`, the draw arithmetic, the waste-free play disciplines,
the pure-draw mints and the witness-grade commit rows — ported
from the frozen `Orig/Phase.lean` and `Orig/Classify.lean` below
(their homes transitively import `Orig.Fate`, so none of these is
importable here; every row carries its source cite). -/

/-! ### §1.5.1 The phase predicate (Phase ports, `Orig/Phase.lean:63-119`) -/

/-! The phase predicate rows (PORTED VERBATIM from
`Orig/Phase.lean:63/:70/:76/:82`) ride the promoted physics kit
`Orig2/Kit.lean` (`inPhase`, `inPhase_eq_decide_of_cons`,
`inPhase_congr`, `inPhase_eq_true_of_nil`). -/

/-! ### §1.5.2 The draw arithmetic (Phase ports, `Orig/Phase.lean:222-311`) -/

/-- A drawn-from stock strictly shrinks (PORTED VERBATIM from
`Orig/Phase.lean:224`). -/
private theorem draw_dropStock {x y : State} (hsuc : x.stepDraw = some y)
    (hd : 0 < x.drawStep) (hne : x.stock ≠ []) : y.stock.length < x.stock.length := by
  obtain ⟨r, hrec, hrne, hy⟩ := draw_unfold hsuc
  have hxr : x = r := ((recycle_keep x hne).symm).trans hrec
  rw [← hxr] at hy
  have hyS : y.stock = (State.dealUpTo x.drawStep x.stock).2 := by rw [hy]
  obtain ⟨h1, h2⟩ := dealUpTo_lens x.drawStep x.stock
  obtain ⟨c, t, hcon⟩ := list_cons_of_ne_nil hne
  have hsl : x.stock.length = 1 + t.length := by
    show (x.stock).length = 1 + t.length
    rw [hcon, List.length_cons]
    omega
  rcases Nat.lt_or_ge x.drawStep x.stock.length with hlt | hge
  · rw [Nat.min_eq_left (Nat.le_of_lt hlt)] at h1
    rw [hyS]
    omega
  · rw [Nat.min_eq_right hge] at h1
    rw [hyS]
    omega

/-! The draw-alignment trap (PORTED from `Orig/Phase.lean:268/:315`)
rides the promoted physics kit `Orig2/Kit.lean`
(`draw_nil_inPhase`, `draw_keeps_inPhase`); this card keeps its
own census row `draw_dropStock` (`Orig/Phase.lean:224`). -/

/-! ### §1.5.3 The waste-free play discipline (Phase ports,
`Orig/Phase.lean:363, 515-757`) -/

/-! The waste-free play discipline (PORTED from
`Orig/Phase.lean:363/:515/:559/:621/:645`) rides the promoted
physics kit `Orig2/Kit.lean` — `isWasteMove`,
`run_cycleCount_lt`, `run_cycleCount_le`,
`step_wasteNe_preserved`, `run_wasteNe`, `draw_pristine_s1`
(the appendix row `append_ne_nil_right` retires with the
consolidation); the commitment invariant below
(`beforeOriginOrAligned`, `step_inv_preserved`,
`run_inv_preserved`) is this card's own machinery and stays. -/

/-- The commitment invariant carried along a returning play
(VERBATIM from `Orig/Phase.lean:680`). -/
private def beforeOriginOrAligned (x₀ x : State) : Prop :=
  x.stock.length < x₀.stock.length ∨ inPhase x = true

/-- One step of a `wasteTo*`-free play preserves the commitment
invariant (PORTED from `Orig/Phase.lean:685`, board cells via this
card's `board_fire_zone`). -/
private theorem step_inv_preserved {x₀ x y : State} (hd : 0 < x₀.drawStep)
    {m : Move} (hsd : x.drawStep = x₀.drawStep)
    (hgood : isWasteMove m ≠ true) (hs : State.step x m = some y)
    (hinv : beforeOriginOrAligned x₀ x) :
    beforeOriginOrAligned x₀ y ∧ y.drawStep = x.drawStep := by
  have hdx : 0 < x.drawStep := by
    rw [hsd]
    exact hd
  cases m with
  | draw =>
      have hsuc : x.stepDraw = some y := hs
      refine ⟨?_, stepDraw_drawStep hsuc⟩
      rcases hinv with h | h
      · by_cases hst : x.stock = []
        · exact Or.inr (draw_nil_inPhase hst hsuc)
        · exact Or.inl (by
            have := draw_dropStock hsuc hdx hst
            omega)
      · exact Or.inr (draw_keeps_inPhase hsuc h)
  | wasteToFound c => simp [isWasteMove] at hgood
  | wasteToTab c b => simp [isWasteMove] at hgood
  | tabToFound c =>
      obtain ⟨h1, h2, h3⟩ := board_fire_zone rfl hs
      refine ⟨?_, h3⟩
      rcases hinv with h | h
      · exact Or.inl (by rw [h1]; exact h)
      · exact Or.inr (by
          have hc := inPhase_congr (x := y) (y := x) h1 h2 h3
          rw [hc]
          exact h)
  | foundToTab c b =>
      obtain ⟨h1, h2, h3⟩ := board_fire_zone rfl hs
      refine ⟨?_, h3⟩
      rcases hinv with h | h
      · exact Or.inl (by rw [h1]; exact h)
      · exact Or.inr (by
          have hc := inPhase_congr (x := y) (y := x) h1 h2 h3
          rw [hc]
          exact h)
  | tabToTab c b =>
      obtain ⟨h1, h2, h3⟩ := board_fire_zone rfl hs
      refine ⟨?_, h3⟩
      rcases hinv with h | h
      · exact Or.inl (by rw [h1]; exact h)
      · exact Or.inr (by
          have hc := inPhase_congr (x := y) (y := x) h1 h2 h3
          rw [hc]
          exact h)

/-- The play lift of the invariant (PORTED VERBATIM from
`Orig/Phase.lean:736`). -/
private theorem run_inv_preserved : ∀ {play : List Move} {x₀ x w : State},
    0 < x₀.drawStep → x.drawStep = x₀.drawStep →
    (∀ m ∈ play, isWasteMove m ≠ true) →
    beforeOriginOrAligned x₀ x →
    x.run play = some w → beforeOriginOrAligned x₀ w := by
  intro play
  induction play with
  | nil =>
      intro x₀ x w _hd _hsd _hgood hinv hrun
      have hx : some x = some w := hrun
      injection hx with h
      rw [← h]
      exact hinv
  | cons m rest ih =>
      intro x₀ x w hd hsd hgood hinv hrun
      obtain ⟨s₁, hm, hrs⟩ := State.run_cons hrun
      have hmne : isWasteMove m ≠ true := hgood m (by simp)
      obtain ⟨hinv', hsd'⟩ := step_inv_preserved hd hsd hmne hm hinv
      have hgood' : ∀ m' ∈ rest, isWasteMove m' ≠ true := by
        intro m' hm'
        exact hgood m' (by simp [hm'])
      exact ih hd (hsd'.trans hsd) hgood' hinv' hrs

/-! ### §1.5.4 The deal list kit (Phase ports, `Orig/Phase.lean:1207-1349`) -/

/-! The deal list kit and the pure-draw mints (PORTED from
`Orig/Phase.lean:1207-:1349`, `:1386`, `:1451`, `:1513`;
`Orig/Classify.lean:1091/:1124/:1133/:1206`) ride the promoted
physics kit `Orig2/Kit.lean` — `take_drop_add`, `take_ge_length`,
`drop_ge_length`, `drop_append_prefix`, `take_append_prefix`,
`dealUpTo_all`, `dealStock_full`, `plain_draw_shape`,
`base_draw_shape`, `draw_full_shape`, `selfRecycle_draw`,
`run_draw_cons`, `run_replicate_append`, `run_cons_shape`,
`drain_to_pass`, `draw_passBase_reversibleW`,
`drain_positions_one`, `base_positions_one`, and the in-phase
round trip.  One name-compatible alias below; the pass-base
short-waste row (`draw_reversible_selfRecycleW`) is subsumed by
Kit's `draw_passBase_reversibleW` and retires here. -/

/-- **The in-phase round trip**, witness grade (this card's private
name; PORTED VERBATIM from `Orig/Phase.lean:1513` — a Kit alias
over `draw_inphase_reversibleW`). -/
private theorem draw_reversible_inphaseW {st : State} (hd : 0 < st.drawStep)
    (hs : st.stock ≠ []) (hw : st.waste ≠ []) (hph : inPhase st = true) :
    reversibleAtW st Move.draw :=
  draw_inphase_reversibleW hd hs hw hph

/-! ### §1.5.6 The witness-grade draw commit rows (Phase
restatements)

The pristine/offset commitments restated DIRECTLY at witness
grade — the witness's own 4-tuple supplies the successor, play and
firing, so the frozen route's `Orig/Fate.lean` semantic pair and
`Orig/Mono.lean` descent bridge never enter (templates:
`Orig/Phase.lean:823` `draw_irreversible_offset` and `:853`
`draw_irreversible_pristine`, bodies carried verbatim). -/

/-- **Draws at pristine positions are commitments**, witness grade:
no returning play exists (RESTATE of `Orig/Phase.lean:853`; a Kit
delegation over `draw_notW_of_pristine`). -/
private theorem draw_not_revW_pristine {st : State}
    (hd : 0 < st.drawStep) (hs : st.stock ≠ []) (hw : st.waste = []) :
    ¬ reversibleAtW st Move.draw :=
  draw_notW_of_pristine hd hs hw

/-- **Draws at offset positions are commitments**, witness grade
(RESTATE of `Orig/Phase.lean:823`; a Kit delegation over
`draw_notW_of_offset`). -/
private theorem draw_not_revW_offset {st : State}
    (hd : 0 < st.drawStep) (hs : st.stock ≠ [])
    (hoff : st.waste.length % st.drawStep ≠ 0) :
    ¬ reversibleAtW st Move.draw :=
  draw_notW_of_offset hd hs hoff

/-! ### §1.5.7 The draw census

**A reversible draw stays reversible at any state sharing its draw
zone** (positive draw step, same stock/waste/draw step): the mint
rows are zone-determined (the pass-base and in-phase round trips
read only the zone), and the witness excludes the two commit
shapes outright (RESTATE of the frozen `draw_revW_congr`,
`Orig/OrbitFactor.lean:472`; the pristine/offset exclusions now
the §1.5.6 rows, the whole-game guide painted zone by zone at
witness grade). -/

private theorem draw_revW_congr {x x' : State} (hpos : 0 < x.drawStep)
    (hs : x.stock = x'.stock) (hw : x.waste = x'.waste)
    (hds : x.drawStep = x'.drawStep)
    (h : reversibleAtW x Move.draw) : reversibleAtW x' Move.draw := by
  have hx'pos : 0 < x'.drawStep := by rw [← hds]; exact hpos
  cases hst : x.stock with
  | nil =>
      cases hws : x.waste with
      | nil =>
          exfalso
          have hdead : x.stepDraw = none := by
            rw [show x.stepDraw = State.dealStock (State.recycle x) from rfl,
              recycle_allEmpty x hst hws, dealStock_nil x hst]
          obtain ⟨_s1o, _P0, hstep', _hrn⟩ := h
          rw [show State.step x Move.draw = x.stepDraw from rfl, hdead] at hstep'
          exact absurd hstep' (by simp)
      | cons w ws =>
          have hxw' : x'.waste = w :: ws := by rw [← hw]; exact hws
          have hxs' : x'.stock = [] := by rw [← hs]; exact hst
          exact draw_passBase_reversibleW hxs'
            (by rw [hxw']; exact fun hc => absurd hc (by simp)) hx'pos
  | cons c cs =>
      have hst' : x'.stock ≠ [] := by
        intro hc
        rw [← hs] at hc
        rw [hst] at hc
        exact nomatch hc
      by_cases hpr : x.waste = []
      · exact absurd h (draw_not_revW_pristine hpos
          (by rw [hst]; exact fun hc => absurd hc (by simp)) hpr)
      · by_cases hres : x.waste.length % x.drawStep = 0
        · obtain ⟨c', t', hcon'⟩ := list_cons_of_ne_nil hst'
          have hph' : inPhase x' = true := by
            rw [inPhase_eq_decide_of_cons hcon']
            refine decide_eq_true ?_
            rw [← hds, ← hw]
            exact hres
          exact draw_reversible_inphaseW hx'pos hst'
            (by
              intro hc
              exact hpr (hw.trans hc)) hph'
        · exact absurd h (draw_not_revW_offset hpos
            (by rw [hst]; exact fun hc => absurd hc (by simp)) hres)

/-! ## §2. THE DRAWS-LAST BUBBLING

Every witness journey permutes to draws-last — a draw-free board
segment to a mid-state, then an all-draw tail segment landing the
original end, BOTH still witness shuffles (template
`shuffle_drawsLast`, `Orig/OrbitFactorC.lean:371`).

THE RESTATED PULL.  The frozen `pull_one`
(`Orig/OrbitFactorC.lean:297`) re-witnessed each pulled board leg
through the classification bridge; this card's §1 square makes a
strictly lighter route available, and the migration takes it (the
departure is recorded in the mission header above):

* a crossed board leg `m` re-witnesses AT THE PULLING ORIGIN by a
  COMPOSITE undo play — one draw letter (the square's own
  `t.stepDraw = some mid` fires it at the crossed site), then the
  leg's ORIGINAL return play `P` verbatim (the square lands the
  re-drawn letter exactly where `P` started), closed by the front
  draw's own certified return play `Q`: `t --draw--> mid --P-->
  s₁ --Q--> x`.  No classification, no WF transfer, no
  draw-cycle injectivity — the exact-landing grade of the general
  square is the whole cost.
* the front draw re-witnesses at the crossed site by the §1.5.7
  census (board legs keep the zone); its gate is `0 < drawStep`,
  threaded by zone-keeps — not the frozen `WF` freight.

The waste movers never ride (§0.7's unconditional census rows at
the leg). -/

/-- A witnessed reversible non-draw leg keeps the draw zone
verbatim (PORTED from `Orig/OrbitFactorC.lean:207`
`leg_zone_keep`, per-kind bodies identical to the frozen). -/
private theorem leg_zone_keep {x y : State} {m : Move}
    (hw : reversibleAtW x m) (hstep : State.step x m = some y)
    (hnd : m ≠ Move.draw) :
    y.stock = x.stock ∧ y.waste = x.waste ∧ y.drawStep = x.drawStep := by
  cases m with
  | draw => exact absurd rfl hnd
  | wasteToFound c => exact absurd hw (journey_never_wasteToFound x c)
  | wasteToTab c b => exact absurd hw (journey_never_wasteToTab x c b)
  | tabToFound c =>
      obtain ⟨-, a, -, hs⟩ := step_tabToFound_inv hstep
      rw [hs]
      exact ⟨rfl, rfl, rfl⟩
  | foundToTab c b =>
      obtain ⟨c₀, ht, hce, hcp, hs⟩ := step_foundToTab_inv hstep
      rw [hs]
      exact ⟨by rw [putCard_stock, setFound_stock],
        by rw [putCard_waste, setFound_waste],
        by rw [putCard_drawStep, setFound_drawStep]⟩
  | tabToTab c b =>
      obtain ⟨a, hh, hcp, hfr, hs⟩ := step_tabToTab_inv hstep
      rw [hs]
      exact ⟨by rw [putRun_stock, setPile_stock],
        by rw [putRun_waste, setPile_waste],
        by rw [putRun_drawStep, setPile_drawStep]⟩

/-- A draw-free witness journey keeps the whole draw zone
verbatim (PORTED VERBATIM from `Orig/OrbitFactorC.lean:246`). -/
private theorem shuffleW_zone_keep : ∀ {x : State} {play : List Move} {y : State},
    ShufflePlayW x play y → (∀ m ∈ play, m ≠ Move.draw) →
    y.stock = x.stock ∧ y.waste = x.waste ∧ y.drawStep = x.drawStep := by
  intro x play y h
  induction h with
  | nil s => intro _; exact ⟨rfl, rfl, rfl⟩
  | @cons st₀ mid stEnd m rest hw hstep hrest ih =>
      intro hnd
      obtain ⟨h1, h2, h3⟩ := leg_zone_keep hw hstep (hnd m (by simp))
      obtain ⟨h4, h5, h6⟩ :=
        ih (fun m' hm' => hnd m' (List.mem_cons_of_mem _ hm'))
      exact ⟨h4.trans h1, h5.trans h2, h6.trans h3⟩

/-- A draws-only witness journey keeps the whole board verbatim
(PORTED VERBATIM from `Orig/OrbitFactorC.lean:260`). -/
private theorem shuffleW_board_keep : ∀ {x : State} {play : List Move} {y : State},
    ShufflePlayW x play y → (∀ m ∈ play, m = Move.draw) →
    y.piles = x.piles ∧ y.found = x.found := by
  intro x play y h
  induction h with
  | nil s => intro _; exact ⟨rfl, rfl⟩
  | @cons st₀ mid stEnd m rest hw hstep hrest ih =>
      intro hdr
      have hmd : m = Move.draw := hdr m (by simp)
      subst hmd
      have hstep' : st₀.stepDraw = some mid := hstep
      obtain ⟨h1, h2⟩ :=
        ih (fun m' hm' => hdr m' (List.mem_cons_of_mem _ hm'))
      exact ⟨h1.trans (stepDraw_piles hstep'), h2.trans (stepDraw_found hstep')⟩

/-- Cons-inversion for witness journeys (PORTED VERBATIM from
`Orig/OrbitFactorC.lean:277`). -/
private theorem shuffleW_cons_inv {st : State} {m : Move} {rest : List Move}
    {st' : State} (h : ShufflePlayW st (m :: rest) st') :
    ∃ mid, reversibleAtW st m ∧ State.step st m = some mid ∧
      ShufflePlayW mid rest st' := by
  cases h with
  | @cons _ mid _ _ _ hw hfire hrest => exact ⟨mid, hw, hfire, hrest⟩

/-- **THE RE-STATED PULL CORE** — a witnessed journey at the drawn
landing `x --draw--> s₁ --play--> y` re-runs wholesale at the
drawing origin `x`, still witness-shuffled leg by leg, landing
`y'` one draw before `y`, with the re-sited front draw's own
witness at `y'` delivered by the induction's bookkeeping.
RESTATE of `Orig/OrbitFactorC.lean:297`: the base case hands back
the front draw's very own witness, a draw leg hands the recursion
its own leg-witness as the next front, and a board leg crosses the
§1 square (`board_square` in place of the frozen dispatch),
re-witnesses itself at `x` by the composite undo play
(`draw :: P ++ Q` — the §2 header's construction), and re-witnesses
the front draw at the crossed site by the §1.5.7 census over the
leg's zone-keep.  Gate: `0 < x.drawStep` (zone-carried), NOT the
frozen `WF` pair. -/
private theorem pull_one : ∀ (play : List Move) (x s₁ y : State),
    x.stepDraw = some s₁ → reversibleAtW x Move.draw → 0 < x.drawStep →
    ShufflePlayW s₁ play y →
    ∃ y', ShufflePlayW x play y' ∧ y'.stepDraw = some y ∧
      reversibleAtW y' Move.draw := by
  intro play
  induction play with
  | nil =>
      intro x s₁ y hd hwfd hpos hJ
      cases hJ
      exact ⟨x, .nil x, hd, hwfd⟩
  | cons m rest ih =>
      intro x s₁ y hd hwfd hpos hJ
      obtain ⟨mid, hw, hfire, hrest⟩ := shuffleW_cons_inv hJ
      cases m with
      | draw =>
          have hd' : s₁.stepDraw = some mid := hfire
          have hposs : 0 < s₁.drawStep := by
            rw [stepDraw_drawStep hd]
            exact hpos
          obtain ⟨y', jlift, hstepD, hrevy⟩ := ih s₁ mid y hd' hw hposs hrest
          exact ⟨y', .cons hwfd hd jlift, hstepD, hrevy⟩
      | wasteToFound c => exact absurd hw (journey_never_wasteToFound s₁ c)
      | wasteToTab c b => exact absurd hw (journey_never_wasteToTab s₁ c b)
      | tabToFound c =>
          obtain ⟨q₀, Q, hq₀, hQ₀⟩ := hwfd
          have hq : q₀ = s₁ :=
            Option.some.inj (hq₀.symm.trans (show State.step x Move.draw = some s₁ from hd))
          have hQ : s₁.run Q = some x := by rw [← hq]; exact hQ₀
          have hfront : reversibleAtW x Move.draw :=
            ⟨s₁, Q, show State.step x Move.draw = some s₁ from hd, hQ⟩
          obtain ⟨t, hfireX, htD⟩ := board_square hd hfire rfl
          obtain ⟨s₂, P, hPs, hP⟩ := hw
          have hs2m : s₂ = mid := Option.some.inj (hPs.symm.trans hfire)
          rw [hs2m] at hP
          have hrevx : reversibleAtW x (Move.tabToFound c) :=
            ⟨t, Move.draw :: (P ++ Q), hfireX, by
              rw [run_draw_cons (show State.step t Move.draw = some mid from htD)]
              exact run_append mid P Q s₁ x hP hQ⟩
          obtain ⟨hz1, hz2, hz3⟩ := leg_zone_keep hrevx hfireX (by simp)
          have hrevt : reversibleAtW t Move.draw :=
            draw_revW_congr hpos hz1.symm hz2.symm hz3.symm hfront
          have hpost : 0 < t.drawStep := by rw [hz3]; exact hpos
          obtain ⟨y', jlift, hstepD, hrevy⟩ := ih t mid y htD hrevt hpost hrest
          exact ⟨y', .cons hrevx hfireX jlift, hstepD, hrevy⟩
      | tabToTab c b =>
          obtain ⟨q₀, Q, hq₀, hQ₀⟩ := hwfd
          have hq : q₀ = s₁ :=
            Option.some.inj (hq₀.symm.trans (show State.step x Move.draw = some s₁ from hd))
          have hQ : s₁.run Q = some x := by rw [← hq]; exact hQ₀
          have hfront : reversibleAtW x Move.draw :=
            ⟨s₁, Q, show State.step x Move.draw = some s₁ from hd, hQ⟩
          obtain ⟨t, hfireX, htD⟩ := board_square hd hfire rfl
          obtain ⟨s₂, P, hPs, hP⟩ := hw
          have hs2m : s₂ = mid := Option.some.inj (hPs.symm.trans hfire)
          rw [hs2m] at hP
          have hrevx : reversibleAtW x (Move.tabToTab c b) :=
            ⟨t, Move.draw :: (P ++ Q), hfireX, by
              rw [run_draw_cons (show State.step t Move.draw = some mid from htD)]
              exact run_append mid P Q s₁ x hP hQ⟩
          obtain ⟨hz1, hz2, hz3⟩ := leg_zone_keep hrevx hfireX (by simp)
          have hrevt : reversibleAtW t Move.draw :=
            draw_revW_congr hpos hz1.symm hz2.symm hz3.symm hfront
          have hpost : 0 < t.drawStep := by rw [hz3]; exact hpos
          obtain ⟨y', jlift, hstepD, hrevy⟩ := ih t mid y htD hrevt hpost hrest
          exact ⟨y', .cons hrevx hfireX jlift, hstepD, hrevy⟩
      | foundToTab c b =>
          obtain ⟨q₀, Q, hq₀, hQ₀⟩ := hwfd
          have hq : q₀ = s₁ :=
            Option.some.inj (hq₀.symm.trans (show State.step x Move.draw = some s₁ from hd))
          have hQ : s₁.run Q = some x := by rw [← hq]; exact hQ₀
          have hfront : reversibleAtW x Move.draw :=
            ⟨s₁, Q, show State.step x Move.draw = some s₁ from hd, hQ⟩
          obtain ⟨t, hfireX, htD⟩ := board_square hd hfire rfl
          obtain ⟨s₂, P, hPs, hP⟩ := hw
          have hs2m : s₂ = mid := Option.some.inj (hPs.symm.trans hfire)
          rw [hs2m] at hP
          have hrevx : reversibleAtW x (Move.foundToTab c b) :=
            ⟨t, Move.draw :: (P ++ Q), hfireX, by
              rw [run_draw_cons (show State.step t Move.draw = some mid from htD)]
              exact run_append mid P Q s₁ x hP hQ⟩
          obtain ⟨hz1, hz2, hz3⟩ := leg_zone_keep hrevx hfireX (by simp)
          have hrevt : reversibleAtW t Move.draw :=
            draw_revW_congr hpos hz1.symm hz2.symm hz3.symm hfront
          have hpost : 0 < t.drawStep := by rw [hz3]; exact hpos
          obtain ⟨y', jlift, hstepD, hrevy⟩ := ih t mid y htD hrevt hpost hrest
          exact ⟨y', .cons hrevx hfireX jlift, hstepD, hrevy⟩

/-- **§2: the witness-grade draws-last bubbling** — every witness
journey factors as a draw-free board segment to a mid-state, then
an all-draw tail segment landing the original end, both segments
still witness shuffles, every leg of both still carrying its own
`reversibleAtW` round trip.  PORT of `Orig/OrbitFactorC.lean:371`
with the restated pull core behind its draw case (the frozen's
`x.WF` gate is replaced by `0 < x.drawStep`, the only freight the
restated pull needs); at a head draw `pull_one` benches the head
draw behind the whole rest journey, at a head board move nothing
moves, and the waste movers never ride (§0.7). -/
theorem shuffle_drawsLast : ∀ (play : List Move) (x y : State),
    ShufflePlayW x play y → 0 < x.drawStep →
    ∃ B D z, (∀ m ∈ B, m ≠ Move.draw) ∧ (∀ m ∈ D, m = Move.draw) ∧
      ShufflePlayW x B z ∧ ShufflePlayW z D y := by
  intro play
  induction play with
  | nil =>
      intro x y h hpos
      cases h
      exact ⟨[], [], x, by simp, by simp, .nil x, .nil x⟩
  | cons m rest ih =>
      intro x y h hpos
      obtain ⟨mid, hw, hfire, hrest⟩ := shuffleW_cons_inv h
      cases m with
      | draw =>
          obtain ⟨y', jlift, hstepD, hrevy⟩ :=
            pull_one rest x mid y (show x.stepDraw = some mid from hfire) hw hpos hrest
          obtain ⟨B, D, z, hBnd, hDdr, hBz, hDz⟩ := ih x y' jlift hpos
          refine ⟨B, D ++ [Move.draw], z, hBnd, ?_, hBz, ?_⟩
          · intro m' hm'
            rcases List.mem_append.mp hm' with h1 | h2
            · exact hDdr m' h1
            · exact List.mem_singleton.mp h2
          · exact ShufflePlayW_append hDz
              (.cons hrevy hstepD (.nil y))
      | tabToFound c =>
          obtain ⟨hz1, hz2, hz3⟩ := board_fire_zone rfl hfire
          have hpos' : 0 < mid.drawStep := by rw [hz3]; exact hpos
          obtain ⟨B, D, z, hBnd, hDdr, hBz, hDz⟩ := ih mid y hrest hpos'
          refine ⟨Move.tabToFound c :: B, D, z, ?_, hDdr, ?_, hDz⟩
          · intro m' hm'
            cases List.mem_cons.mp hm' with
            | inl heq => intro hcon; rw [heq] at hcon; exact nomatch hcon
            | inr htl => exact hBnd m' htl
          · exact .cons hw hfire hBz
      | foundToTab c b =>
          obtain ⟨hz1, hz2, hz3⟩ := board_fire_zone rfl hfire
          have hpos' : 0 < mid.drawStep := by rw [hz3]; exact hpos
          obtain ⟨B, D, z, hBnd, hDdr, hBz, hDz⟩ := ih mid y hrest hpos'
          refine ⟨Move.foundToTab c b :: B, D, z, ?_, hDdr, ?_, hDz⟩
          · intro m' hm'
            cases List.mem_cons.mp hm' with
            | inl heq => intro hcon; rw [heq] at hcon; exact nomatch hcon
            | inr htl => exact hBnd m' htl
          · exact .cons hw hfire hBz
      | tabToTab c b =>
          obtain ⟨hz1, hz2, hz3⟩ := board_fire_zone rfl hfire
          have hpos' : 0 < mid.drawStep := by rw [hz3]; exact hpos
          obtain ⟨B, D, z, hBnd, hDdr, hBz, hDz⟩ := ih mid y hrest hpos'
          refine ⟨Move.tabToTab c b :: B, D, z, ?_, hDdr, ?_, hDz⟩
          · intro m' hm'
            cases List.mem_cons.mp hm' with
            | inl heq => intro hcon; rw [heq] at hcon; exact nomatch hcon
            | inr htl => exact hBnd m' htl
          · exact .cons hw hfire hBz
      | wasteToFound c => exact absurd hw (journey_never_wasteToFound _ c)
      | wasteToTab c b => exact absurd hw (journey_never_wasteToTab _ c b)

/-! ## §3. THE DRAW-BLOCK TRANSPLANT

Draws-only witness journeys re-root at any state sharing the draw
zone (template `draw_play_transplant`,
`Orig/OrbitFactor.lean:520-566`): each leg fires by the
field-determined draw (`stepDraw_rel`), each leg's `reversibleAtW`
re-instantiates by the §1.5.7 census (`draw_revW_congr`), and the
landing shares the original's zone while keeping the new frame's
board — the phase component runs equally at every board that
shares its zone. -/

/-- The frame-threading core: proved by list induction with BOTH
frames generalized, so the successor pair of a draw leg
(`stepDraw_rel`) chains (PORTED from
`Orig/OrbitFactor.lean:520`, trued to the Walk cons order and the
§1.5.7 census). -/
private theorem draw_play_transplant_aux : ∀ (x x' : State) (play : List Move)
    (y : State), ShufflePlayW x play y → (∀ m ∈ play, m = Move.draw) →
    0 < x.drawStep → x.stock = x'.stock → x.waste = x'.waste →
    x.drawStep = x'.drawStep →
    ∃ y', ShufflePlayW x' play y' ∧
      y'.stock = y.stock ∧ y'.waste = y.waste ∧ y'.drawStep = y.drawStep := by
  intro x x' play
  induction play generalizing x x' with
  | nil =>
      intro y hx hdraw hpos hst1 hst2 hst3
      cases hx
      exact ⟨x', .nil x', hst1.symm, hst2.symm, hst3.symm⟩
  | cons m rest ih =>
      intro y hx hdraw hpos hst1 hst2 hst3
      have hdrawer : ∀ m' ∈ rest, m' = Move.draw := fun m' hm' =>
        hdraw m' (List.mem_cons_of_mem _ hm')
      have hmd : m = Move.draw := hdraw m (by simp)
      subst hmd
      cases hx with
      | @cons _ mid _ _ _ hw hstep hrest =>
          have hb : x.stepDraw = some mid := hstep
          obtain ⟨mid', hfire', hpv, hpu, hfv, hfu, hdv2, hdu2, hz1, hz2⟩ :=
            stepDraw_rel hst1.symm hst2.symm hst3.symm hb
          have hleg : reversibleAtW x' Move.draw :=
            draw_revW_congr hpos hst1 hst2 hst3 hw
          have hdss : mid.drawStep = mid'.drawStep :=
            (stepDraw_drawStep hb).trans (hst3.trans (stepDraw_drawStep hfire').symm)
          obtain ⟨y'', hjrest, hz1', hz2', hdss'⟩ :=
            ih mid mid' y hrest hdrawer (by rw [stepDraw_drawStep hb]; exact hpos)
              hz1.symm hz2.symm hdss
          exact ⟨y'', .cons hleg hfire' hjrest, hz1', hz2', hdss'⟩

/-- **§3: re-rooting a draw block at the rotated position** — a
draws-only witness journey re-runs, legs still witnessed, at any
state sharing the draw zone (PORT from
`Orig/OrbitFactor.lean:560`; the per-leg census is this card's
§1.5.7 restatement, the firing field-determined by the §0.5
`stepDraw_rel` port). -/
theorem draw_play_transplant {x y x' : State} {play : List Move}
    (h : ShufflePlayW x play y) (hdraw : ∀ m ∈ play, m = Move.draw)
    (hpos : 0 < x.drawStep)
    (hs : x.stock = x'.stock) (hw : x.waste = x'.waste) (hd : x.drawStep = x'.drawStep) :
    ∃ y', ShufflePlayW x' play y' ∧
      y'.stock = y.stock ∧ y'.waste = y.waste ∧ y'.drawStep = y.drawStep :=
  draw_play_transplant_aux x x' play y h hdraw hpos hs hw hd

/-! ## §4. THE ASSEMBLY

→ extracts the two witness journeys from the rev-closure, bubbles
both draws-last, re-splits the composite at `zF`, and transplants
the `d`-block to `v`'s frame; ← composes the four witnesses (the
trivial glue).  Templates `sameOrbit_factor_fwd`/
`sameOrbit_factor_full`, `Orig/OrbitFactorC.lean:442-487`.  The
`WF` premises pay ONLY the draw-step positivity (the `WF` chain's
own fourth clause — the Integrity `drawStep_pos` grade): the bubbling's gate
travels to the split mid-points by zone-keeps, the transplant's by
the board journey's zone-keep — no `step_wf`, no WF-along-journeys
freight anywhere (the frozen card's `shuffleW_wf_end` ride retired
with the restated pull). -/

/-- **§4a: the forward factorization.**  Two `WF` same-orbit mates
decompose as the board component (`NoDrawPlayW`) onto the phase
component (`SWRotW`): the ←-journey of the class and the →-journey
both bubble draws-last; the composite `zF --D--> v --b--> zB --d-->
u` re-splits draws-last at `zF` (positivity carried there by the
`B`-journey's zone-keep), the re-split's own landing `z₂` closing
to `u` by the accounting (boards keep the zone, draws keep the
board — `State.ext`); and the `d`-block transplants to `v`'s frame
(`v` shares `zB`'s zone by the `b`-journey's zone-keep), the
transplanted landing closing to `zF` the same way.  PORT of
`Orig/OrbitFactorC.lean:442` on the restated pieces. -/
theorem sameOrbit_factor_fwd {u v : State} (hwf₁ : u.WF) (hwf₂ : v.WF)
    (h : sameOrbitSetoid.r u v) :
    ∃ z, NoDrawPlayW u z ∧ SWRotW z v := by
  have hpos₁ : 0 < u.drawStep := hwf₁.2.2.2
  have hpos₂ : 0 < v.drawStep := hwf₂.2.2.2
  have h' : RevEqW v u := h
  obtain ⟨σ, hσW, τ, hτW⟩ := h'
  obtain ⟨B, D, zF, hBnd, hDdr, hBz, hDz⟩ := shuffle_drawsLast τ u v hτW hpos₁
  obtain ⟨b, d, zB, hbnd, hddr, hbz, hdz⟩ := shuffle_drawsLast σ v u hσW hpos₂
  obtain ⟨kF1, kF2, kF3⟩ := shuffleW_zone_keep hBz hBnd
  obtain ⟨kB1, kB2, kB3⟩ := shuffleW_zone_keep hbz hbnd
  have hposzF : 0 < zF.drawStep := by rw [kF3]; exact hpos₁
  have hcomp : ShufflePlayW zF (D ++ b ++ d) u :=
    ShufflePlayW_append (ShufflePlayW_append hDz hbz) hdz
  obtain ⟨B₂, D₂, z₂, hB₂nd, hD₂dr, hB₂z, hD₂z⟩ :=
    shuffle_drawsLast (D ++ b ++ d) zF u hcomp hposzF
  obtain ⟨k₂1, k₂2, k₂3⟩ := shuffleW_zone_keep hB₂z hB₂nd
  obtain ⟨kD1, kD2⟩ := shuffleW_board_keep hD₂z hD₂dr
  have hz₂u : z₂ = u :=
    State.ext kD2.symm kD1.symm (k₂1.trans kF1) (k₂2.trans kF2) (k₂3.trans kF3)
  rw [hz₂u] at hB₂z
  have hposzB : 0 < zB.drawStep := by rw [kB3]; exact hpos₂
  obtain ⟨y', jμ, hyz1, hyz2, hyz3⟩ :=
    draw_play_transplant hdz hddr hposzB kB1 kB2 kB3
  obtain ⟨ky1, ky2⟩ := shuffleW_board_keep jμ hddr
  obtain ⟨kv1, kv2⟩ := shuffleW_board_keep hDz hDdr
  have hyeq : y' = zF :=
    State.ext (ky2.trans kv2) (ky1.trans kv1)
      (hyz1.trans kF1.symm) (hyz2.trans kF2.symm) (hyz3.trans kF3.symm)
  rw [hyeq] at jμ
  exact ⟨zF, ⟨B, hBz, hBnd, B₂, hB₂z, hB₂nd⟩, D, d, ⟨hDz, hDdr⟩, ⟨jμ, hddr⟩⟩

/-- **§4b: THE ORBIT-FACTOR CLAIM, DISCHARGED** (the claims ledger's
`sameOrbit_factor`, `Orig2/Claims.lean` §1B, promoted here): the
phase factorization — a class membership is a draw-free board
reshuffle to a phase-mate, then a pure rotation round.  `→` is
§4a; `←` composes the four witnesses (a `z` factored by both
components supplies the `v→u` journey as the rotation round
followed by the board back, and the `u→v` journey as the board
front followed by the rotation round — template
`sameOrbit_factor_full`, `Orig/OrbitFactorC.lean:482`). -/
theorem sameOrbit_factor {u v : State} (hwf₁ : u.WF) (hwf₂ : v.WF) :
    sameOrbitSetoid.r u v ↔ ∃ z, NoDrawPlayW u z ∧ SWRotW z v := by
  constructor
  · exact sameOrbit_factor_fwd hwf₁ hwf₂
  · rintro ⟨z, ⟨P₁, hP₁, hP₁nd, P₂, hP₂, hP₂nd⟩, σ, τ, ⟨hσW, -⟩, ⟨hτW, -⟩⟩
    exact ⟨τ ++ P₂, ShufflePlayW_append hτW hP₂, P₁ ++ σ, ShufflePlayW_append hP₁ hσW⟩

/-! ## §5. PROMOTION NOTE (for the claims ledger's §1B)

`sameOrbit_factor` is PROVED here real — the claims-layer stub
is deleted, the battery line moved to this card's battery block.
The four-piece PRICE (the general commutation §1, the restated
bubbling §2, the transplant §3, the assembly §4) is fully paid:
every ingredient is this card's private kit or the sanctioned
seam/registry rows, nothing rides the frozen tier, and the
discharge carries no `sorryAx`, no `Classical.choice`. -/

/-! ## THE AUDIT BATTERY

Per proved head: `[propext]`/`[propext, Quot.sound]` only; zero
`sorryAx`; zero `Classical.choice`.  Grows per green batch. -/

#print axioms stepDraw_rel
#print axioms stepDraw_piles
#print axioms stepDraw_found
#print axioms stepDraw_drawStep
#print axioms cycleCount_lt_wasteToFound
#print axioms cycleCount_lt_wasteToTab
#print axioms journey_never_wasteToFound
#print axioms journey_never_wasteToTab
#print axioms board_fire_congr
#print axioms board_fire_zone
#print axioms board_square
#print axioms board_draw_commute
#print axioms draw_nil_inPhase
#print axioms draw_keeps_inPhase
#print axioms draw_dropStock
#print axioms draw_not_revW_pristine
#print axioms draw_not_revW_offset
#print axioms drain_to_pass
#print axioms draw_passBase_reversibleW
#print axioms drain_positions_one
#print axioms base_positions_one
#print axioms draw_reversible_inphaseW
#print axioms draw_revW_congr
#print axioms leg_zone_keep
#print axioms shuffleW_zone_keep
#print axioms shuffleW_board_keep
#print axioms shuffleW_cons_inv
#print axioms pull_one
#print axioms shuffle_drawsLast
#print axioms draw_play_transplant_aux
#print axioms draw_play_transplant
#print axioms sameOrbit_factor_fwd
#print axioms sameOrbit_factor
