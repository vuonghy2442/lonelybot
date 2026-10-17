import Orig2.Vocab

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

/-! ## §0. THE PRIVATE KIT (per-file restatements, cited) -/

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

/-- `setPile` keeps the stock (PORTED from
`Orig/Irreversible.lean:191`, a `rfl` row). -/
private theorem setPile_stock (st : State) (a : Anchor) (p : Pile) :
    (st.setPile a p).stock = st.stock := rfl

/-- `setPile` keeps the waste (PORTED from
`Orig/Irreversible.lean:195`). -/
private theorem setPile_waste (st : State) (a : Anchor) (p : Pile) :
    (st.setPile a p).waste = st.waste := rfl

/-- `setPile` keeps the draw step (PORTED from
`Orig/Irreversible.lean:199`). -/
private theorem setPile_drawStep (st : State) (a : Anchor) (p : Pile) :
    (st.setPile a p).drawStep = st.drawStep := rfl

/-- `setPile`'s piles write, as the pointwise record (PORTED from
`Orig/Irreversible.lean:203`). -/
private theorem setPile_piles (st : State) (a : Anchor) (p : Pile) :
    (st.setPile a p).piles = (fun a' => if a' = a then p else st.piles a') := rfl

/-- `setFound` keeps the stock (PORTED from
`Orig/Irreversible.lean:208`). -/
private theorem setFound_stock (st : State) (s : Suit) (l : List Card) :
    (st.setFound s l).stock = st.stock := rfl

/-- `setFound` keeps the waste (PORTED from
`Orig/Irreversible.lean:212`). -/
private theorem setFound_waste (st : State) (s : Suit) (l : List Card) :
    (st.setFound s l).waste = st.waste := rfl

/-- `setFound` keeps the tableau (PORTED from
`Orig/Irreversible.lean:216`). -/
private theorem setFound_piles (st : State) (s : Suit) (l : List Card) :
    (st.setFound s l).piles = st.piles := rfl

/-- `setFound` keeps the draw step (PORTED from
`Orig/Irreversible.lean:220`). -/
private theorem setFound_drawStep (st : State) (s : Suit) (l : List Card) :
    (st.setFound s l).drawStep = st.drawStep := rfl

/-- `putCard` keeps the stock (PORTED from
`Orig/Irreversible.lean:224`); seam-carried shape via
`putCard_keep`. -/
private theorem putCard_stock {st : State} (c : Card) (b : Base) :
    (st.putCard c b).stock = st.stock := putCard_keep.2.1

/-- `putCard` keeps the waste (PORTED from
`Orig/Irreversible.lean:231`). -/
private theorem putCard_waste {st : State} (c : Card) (b : Base) :
    (st.putCard c b).waste = st.waste := putCard_keep.2.2.1

/-- `putCard` keeps the foundations (PORTED from
`Orig/Irreversible.lean:238`). -/
private theorem putCard_found {st : State} (c : Card) (b : Base) :
    (st.putCard c b).found = st.found := putCard_keep.1

/-- `putCard` keeps the draw step (PORTED from
`Orig/Irreversible.lean:245`). -/
private theorem putCard_drawStep {st : State} (c : Card) (b : Base) :
    (st.putCard c b).drawStep = st.drawStep := putCard_keep.2.2.2

/-- `putRun` keeps the stock (PORTED from
`Orig/Irreversible.lean:252`). -/
private theorem putRun_stock {st : State} (run : List Card) (b : Base) :
    (st.putRun run b).stock = st.stock := putRun_keep.2.1

/-- `putRun` keeps the waste (PORTED from
`Orig/Irreversible.lean:259`). -/
private theorem putRun_waste {st : State} (run : List Card) (b : Base) :
    (st.putRun run b).waste = st.waste := putRun_keep.2.2.1

/-- `putRun` keeps the foundations (PORTED from
`Orig/Irreversible.lean:266`). -/
private theorem putRun_found {st : State} (run : List Card) (b : Base) :
    (st.putRun run b).found = st.found := putRun_keep.1

/-- `putRun` keeps the draw step (PORTED from
`Orig/Irreversible.lean:273`). -/
private theorem putRun_drawStep {st : State} (run : List Card) (b : Base) :
    (st.putRun run b).drawStep = st.drawStep := putRun_keep.2.2.2

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

/-- A successful `.tabToFound` (PORTED VERBATIM from
`Orig/Irreversible.lean:511`). -/
private theorem step_tabToFound_inv {st : State} {c : Card} {s' : State}
    (h : State.step st (Move.tabToFound c) = some s') :
    st.nextUp c = true ∧
    ∃ a, st.pileOfTop c = some a ∧
      s' = { st.setFound c.suit (st.found c.suit ++ [c]) with
             piles := fun a' =>
               if a' = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
               else st.piles a' } := by
  simp only [State.step] at h
  split at h
  · rename_i hn
    split at h
    · exact absurd h (by simp)
    · rename_i _ a hp
      injection h with hEq
      exact ⟨hn, a, hp, hEq.symm⟩
  · exact absurd h (by simp)

/-- A successful `.foundToTab` (PORTED VERBATIM from
`Orig/Irreversible.lean:555`). -/
private theorem step_foundToTab_inv {st : State} {c : Card} {b : Base} {s' : State}
    (h : State.step st (Move.foundToTab c b) = some s') :
    ∃ c', st.foundTop c.suit = some c' ∧ c' = c ∧ st.canPlace c b = true ∧
      s' = (st.setFound c.suit (chop (st.found c.suit))).putCard c b := by
  simp only [State.step] at h
  split at h
  · split at h
    · rename_i _ c' ht hg
      rw [Bool.and_eq_true] at hg
      injection h with hEq
      exact ⟨c', ht, of_decide_eq_true hg.1, hg.2, hEq.symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A successful `.tabToTab` (PORTED VERBATIM from
`Orig/Irreversible.lean:572`). -/
private theorem step_tabToTab_inv {st : State} {c : Card} {b : Base} {s' : State}
    (h : State.step st (Move.tabToTab c b) = some s') :
    ∃ a, st.pileHolding c = some a ∧ st.canPlace c b = true ∧
      fromCard c (st.piles a).faceUp ≠ [] ∧
        s' = (st.setPile a
            (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
              (fromCard c (st.piles a).faceUp) b := by
  simp only [State.step] at h
  split at h
  · exact absurd h (by simp)
  · rename_i _ a hh
    split at h
    · rename_i hcp
      split at h
      · exact absurd h (by simp)
      · rename_i _ hne
        injection h with hEq
        exact ⟨a, hh, hcp, hne, hEq.symm⟩
    · exact absurd h (by simp)

/-! ### §0.5 The draw record rows (Irreversible/EdgeLabel ports)

A fired draw keeps the board, the draw step, and conserves the
cycle pool (`Orig/Irreversible.lean:438-449`,
`Orig/EdgeLabel.lean:2736-2743`) — plus the ZONE-DETERMINED
REFIRE (`stepDraw_rel`, `Orig/Twin.lean:207`): the draw's firing
and landing zone are functions of the zone alone. -/

/-- The recycle keeps the piles (a `rfl`-by-cases row over the
seam's recycle reading; the frozen home rides
`Orig/Irreversible.lean`'s `recycle_piles`). -/
private theorem recycle_piles (st : State) : (State.recycle st).piles = st.piles := by
  cases hs : st.stock with
  | nil =>
      cases hw : st.waste with
      | nil => rw [recycle_allEmpty st hs hw]
      | cons w ws =>
          rw [recycle_nil st hs (by rw [hw]; exact fun hc => absurd hc (by simp))]
  | cons c cs =>
      rw [recycle_keep st (by rw [hs]; exact fun hc => absurd hc (by simp))]

/-- The recycle keeps the foundations. -/
private theorem recycle_found (st : State) : (State.recycle st).found = st.found := by
  cases hs : st.stock with
  | nil =>
      cases hw : st.waste with
      | nil => rw [recycle_allEmpty st hs hw]
      | cons w ws =>
          rw [recycle_nil st hs (by rw [hw]; exact fun hc => absurd hc (by simp))]
  | cons c cs =>
      rw [recycle_keep st (by rw [hs]; exact fun hc => absurd hc (by simp))]

/-- The recycle keeps the draw step. -/
private theorem recycle_drawStep (st : State) :
    (State.recycle st).drawStep = st.drawStep := by
  cases hs : st.stock with
  | nil =>
      cases hw : st.waste with
      | nil => rw [recycle_allEmpty st hs hw]
      | cons w ws =>
          rw [recycle_nil st hs (by rw [hw]; exact fun hc => absurd hc (by simp))]
  | cons c cs =>
      rw [recycle_keep st (by rw [hs]; exact fun hc => absurd hc (by simp))]

/-- A successful draw keeps the piles (PORTED from
`Orig/Irreversible.lean:438`, restated over the seam's
`draw_unfold`). -/
private theorem stepDraw_piles {st s' : State} (h : st.stepDraw = some s') :
    s'.piles = st.piles := by
  obtain ⟨r, hrec, -, hy⟩ := draw_unfold h
  have h1 : s'.piles = r.piles := by rw [hy]
  rw [h1, ← hrec, recycle_piles st]

/-- A successful draw keeps the foundations (PORTED from
`Orig/Irreversible.lean:445`). -/
private theorem stepDraw_found {st s' : State} (h : st.stepDraw = some s') :
    s'.found = st.found := by
  obtain ⟨r, hrec, -, hy⟩ := draw_unfold h
  have h1 : s'.found = r.found := by rw [hy]
  rw [h1, ← hrec, recycle_found st]

/-- A successful draw keeps the draw step (PORTED from
`Orig/EdgeLabel.lean:2736`). -/
private theorem stepDraw_drawStep {x u : State} (hd : x.stepDraw = some u) :
    u.drawStep = x.drawStep := by
  obtain ⟨r, hrec, -, hy⟩ := draw_unfold hd
  have h1 : u.drawStep = r.drawStep := by rw [hy]
  rw [h1, ← hrec, recycle_drawStep x]

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

/-- The strictly-dropping waste measure (VERBATIM from
`Orig/Irreversible.lean:66`). -/
private def cycleCount (st : State) : Nat := st.stock.length + st.waste.length

/-- Lengths of the `dealUpTo` split (PORTED VERBATIM from
`Orig/Phase.lean:123`): the dealt part has `min k |l|` cards, and
the two parts recombine to `l`. -/
private theorem dealUpTo_lens (k : Nat) : ∀ (l : List Card),
    (State.dealUpTo k l).1.length = min k l.length ∧
    (State.dealUpTo k l).1.length + (State.dealUpTo k l).2.length = l.length := by
  induction k with
  | zero =>
      intro l
      refine ⟨?_, ?_⟩
      · exact (Nat.min_eq_left (Nat.zero_le l.length)).symm
      · exact Nat.zero_add l.length
  | succ k ih =>
      intro l
      cases l with
      | nil =>
          refine ⟨?_, ?_⟩
          · exact (Nat.min_eq_right (Nat.zero_le (k + 1))).symm
          · rfl
      | cons c cs =>
          obtain ⟨h1, h2⟩ := ih cs
          have hs1 : (State.dealUpTo (k + 1) (c :: cs)).1.length
              = (State.dealUpTo k cs).1.length + 1 := rfl
          have hs2 : (State.dealUpTo (k + 1) (c :: cs)).2.length
              = (State.dealUpTo k cs).2.length := rfl
          have hlen : List.length (c :: cs) = List.length cs + 1 := rfl
          rw [hs1, hs2, hlen]
          rcases Nat.lt_or_ge k cs.length with hlt | hge
          · rw [Nat.min_eq_left (Nat.le_of_lt hlt)] at h1
            refine ⟨?_, ?_⟩
            · rw [h1, Nat.min_eq_left (Nat.succ_le_succ (Nat.le_of_lt hlt))]
            · omega
          · rw [Nat.min_eq_right hge] at h1
            refine ⟨?_, ?_⟩
            · rw [h1, Nat.min_eq_right (Nat.succ_le_succ hge)]
            · omega

/-- Recycling conserves the cycle count (PORTED from
`Orig/Phase.lean:181`). -/
private theorem recycle_cycleCount (st : State) :
    cycleCount (State.recycle st) = cycleCount st := by
  by_cases hst : st.stock = []
  · by_cases hw : st.waste = []
    · rw [recycle_allEmpty st hst hw]
    · rw [recycle_nil st hst hw]
      show (st.waste.reverse).length + ([] : List Card).length
          = st.stock.length + st.waste.length
      rw [List.length_reverse, List.length_nil, hst, List.length_nil]
      omega
  · rw [recycle_keep st hst]

/-- A draw conserves the cycle count (PORTED from
`Orig/Phase.lean:204`). -/
private theorem draw_cycleCount {x y : State} (hsuc : x.stepDraw = some y) :
    cycleCount y = cycleCount x := by
  obtain ⟨r, hrec, hrne, hy⟩ := draw_unfold hsuc
  have h1 : y.stock = (State.dealUpTo r.drawStep r.stock).2 := by rw [hy]
  have h2 : y.waste = (State.dealUpTo r.drawStep r.stock).1.reverse ++ r.waste := by
    rw [hy]
  obtain ⟨-, hl⟩ := dealUpTo_lens r.drawStep r.stock
  have hrc : r.stock.length + r.waste.length = x.stock.length + x.waste.length := by
    rw [← hrec]
    exact recycle_cycleCount x
  show y.stock.length + y.waste.length = x.stock.length + x.waste.length
  rw [h1, h2, List.length_append, List.length_reverse]
  omega

/-- Building the waste top onto its foundation spends exactly one
cycle-count unit (PORTED VERBATIM from `Orig/Phase.lean:382`). -/
private theorem cycleCount_lt_wasteToFound {x y : State} {c : Card}
    (h : State.step x (.wasteToFound c) = some y) :
    cycleCount y < cycleCount x := by
  simp only [State.step] at h
  split at h
  · by_cases hw : x.waste = []
    · rw [hw] at h
      simp at h
    · obtain ⟨w', ws, hcon⟩ := list_cons_of_ne_nil hw
      rw [hcon] at h
      simp only [Option.some.injEq] at h
      subst h
      show x.stock.length + ws.length < x.stock.length + x.waste.length
      rw [hcon, List.length_cons]
      omega
  · simp at h

/-- Building the waste top onto the tableau spends exactly one
cycle-count unit (PORTED VERBATIM from `Orig/Phase.lean:401`). -/
private theorem cycleCount_lt_wasteToTab {x y : State} {c : Card} {b : Base}
    (h : State.step x (.wasteToTab c b) = some y) :
    cycleCount y < cycleCount x := by
  simp only [State.step] at h
  split at h
  · by_cases hw : x.waste = []
    · rw [hw] at h
      simp at h
    · obtain ⟨w', ws, hcon⟩ := list_cons_of_ne_nil hw
      rw [hcon] at h
      simp only [Option.some.injEq] at h
      subst h
      show (x.putCard c b).stock.length + ws.length
          < x.stock.length + x.waste.length
      rw [putCard_stock, hcon, List.length_cons]
      omega
  · simp at h

/-- **The per-move step table**: every legal move leaves the cycle
count weakly down (PORTED from `Orig/Phase.lean:473`; the board
cells ride this card's field equations instead of Phase's
`*_fixed` rows). -/
private theorem step_cycleCount_le {x y : State} : ∀ m : Move,
    State.step x m = some y → cycleCount y ≤ cycleCount x := by
  intro m h
  cases m with
  | draw => exact Nat.le_of_eq (draw_cycleCount h)
  | wasteToFound c =>
      have hlt := cycleCount_lt_wasteToFound h
      omega
  | wasteToTab c b =>
      have hlt := cycleCount_lt_wasteToTab h
      omega
  | tabToFound c =>
      obtain ⟨-, a, -, hs⟩ := step_tabToFound_inv h
      rw [hs]
      exact Nat.le_refl _
  | foundToTab c b =>
      obtain ⟨c₀, -, -, -, hs⟩ := step_foundToTab_inv h
      rw [hs]
      show ((x.setFound c.suit (chop (x.found c.suit))).putCard c b).stock.length
          + ((x.setFound c.suit (chop (x.found c.suit))).putCard c b).waste.length
          ≤ x.stock.length + x.waste.length
      rw [putCard_stock, putCard_waste, setFound_stock, setFound_waste]
      omega
  | tabToTab c b =>
      obtain ⟨a, -, -, -, hs⟩ := step_tabToTab_inv h
      rw [hs]
      show ((x.setPile a
            (Pile.afterRunRemoved (x.piles a) (below c (x.piles a).faceUp))).putRun
            (fromCard c (x.piles a).faceUp) b).stock.length
          + ((x.setPile a
            (Pile.afterRunRemoved (x.piles a) (below c (x.piles a).faceUp))).putRun
            (fromCard c (x.piles a).faceUp) b).waste.length
          ≤ x.stock.length + x.waste.length
      rw [putRun_stock, putRun_waste, setPile_stock, setPile_waste]
      omega

/-- The play lift: no play raises the cycle count (PORTED VERBATIM
from `Orig/Phase.lean:497`). -/
private theorem run_cycleCount_le : ∀ {play : List Move} {x w : State},
    x.run play = some w → cycleCount w ≤ cycleCount x := by
  intro play
  induction play with
  | nil =>
      intro x w hrun
      have hx : some x = some w := hrun
      injection hx with h
      rw [← h]
      exact Nat.le_refl _
  | cons m rest ih =>
      intro x w hrun
      obtain ⟨s₁, hm, hrs⟩ := State.run_cons hrun
      have h1 := ih hrs
      have h2 := step_cycleCount_le m hm
      omega

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

/-- `true` at the phase boundaries of the draw cycle (VERBATIM from
`Orig/Phase.lean:63`; the registry cut the tier per the clean
split — per-file kit here). -/
private def inPhase (st : State) : Bool :=
  match st.stock with
  | [] => true
  | _ => decide (st.waste.length % st.drawStep = 0)

/-- With cards left in the stock, `inPhase` is literally the decide
on the waste residue (PORTED VERBATIM from
`Orig/Phase.lean:70`). -/
private theorem inPhase_eq_decide_of_cons {st : State} {c : Card} {t : List Card}
    (hcon : st.stock = c :: t) :
    inPhase st = decide (st.waste.length % st.drawStep = 0) := by
  simp only [inPhase, hcon]

/-- `inPhase` depends only on the zone (PORTED VERBATIM from
`Orig/Phase.lean:76`). -/
private theorem inPhase_congr {x y : State} (h1 : x.stock = y.stock)
    (h2 : x.waste = y.waste) (h3 : x.drawStep = y.drawStep) :
    inPhase x = inPhase y := by
  simp only [inPhase, h1, h2, h3]

/-- No stock cards means aligned (PORTED VERBATIM from
`Orig/Phase.lean:82`). -/
private theorem inPhase_eq_true_of_nil {st : State} (hnil : st.stock = []) :
    inPhase st = true := by
  simp only [inPhase, hnil]

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

/-- A draw fired at the end of the stock lands phase-aligned (the
first half of the trap; PORTED VERBATIM from
`Orig/Phase.lean:268`). -/
private theorem draw_nil_inPhase {x y : State} (hst : x.stock = [])
    (hsuc : x.stepDraw = some y) : inPhase y = true := by
  obtain ⟨r, hrec, hrne, hy⟩ := draw_unfold hsuc
  by_cases hw : x.waste = []
  · exfalso
    have hrx : r = x := hrec.symm.trans (recycle_allEmpty x hst hw)
    rw [hrx] at hrne
    rw [hst] at hrne
    exact absurd rfl hrne
  · have hrfl : r = { x with stock := x.waste.reverse, waste := [] } :=
      hrec.symm.trans (recycle_nil x hst hw)
    rw [hrfl] at hy
    have hyS : y.stock = (State.dealUpTo x.drawStep x.waste.reverse).2 := by
      rw [hy]
    have hyW : y.waste =
        (State.dealUpTo x.drawStep x.waste.reverse).1.reverse ++ ([] : List Card) := by
      rw [hy]
    have hwr : (x.waste.reverse).length = x.waste.length := List.length_reverse
    obtain ⟨h1, h2⟩ := dealUpTo_lens x.drawStep x.waste.reverse
    rcases Nat.lt_or_ge x.drawStep x.waste.length with hlt | hge
    · rw [hwr, Nat.min_eq_left (Nat.le_of_lt hlt)] at h1
      have hyne : y.stock ≠ [] := by
        intro hc0
        have hc2 : (State.dealUpTo x.drawStep x.waste.reverse).2 = ([] : List Card) :=
          hyS.symm.trans hc0
        rw [hc2, List.length_nil] at h2
        omega
      obtain ⟨c', t', hys⟩ := list_cons_of_ne_nil hyne
      have hdec : inPhase y = decide (y.waste.length % y.drawStep = 0) := by
        simp only [inPhase, hys]
      have hywl : y.waste.length = x.drawStep := by
        rw [hyW, List.length_append, List.length_reverse, List.length_nil, h1]
        omega
      have hyD : y.drawStep = x.drawStep := by
        rw [hy]
      rw [hdec, hywl, hyD]
      exact decide_eq_true (Nat.mod_self x.drawStep)
    · rw [hwr, Nat.min_eq_right hge] at h1
      have hyv : y.stock = [] := by
        have hy0 : y.stock.length = 0 := by
          rw [hyS]
          omega
        exact List.length_eq_zero_iff.mp hy0
      exact inPhase_eq_true_of_nil hyv

/-- Alignment is drawn into (the second half of the trap; PORTED
VERBATIM from `Orig/Phase.lean:315`). -/
private theorem draw_keeps_inPhase {x y : State} (hsuc : x.stepDraw = some y)
    (hin : inPhase x = true) : inPhase y = true := by
  by_cases hst : x.stock = []
  · exact draw_nil_inPhase hst hsuc
  · obtain ⟨r, hrec, hrne, hy⟩ := draw_unfold hsuc
    have hxr : x = r := ((recycle_keep x hst).symm).trans hrec
    rw [← hxr] at hy
    obtain ⟨c, t, hcon⟩ := list_cons_of_ne_nil hst
    have hres : x.waste.length % x.drawStep = 0 := by
      rw [inPhase_eq_decide_of_cons hcon] at hin
      exact of_decide_eq_true hin
    have hyS : y.stock = (State.dealUpTo x.drawStep x.stock).2 := by
      rw [hy]
    have hyW : y.waste = (State.dealUpTo x.drawStep x.stock).1.reverse ++ x.waste := by
      rw [hy]
    have hyD : y.drawStep = x.drawStep := by
      rw [hy]
    obtain ⟨h1, h2⟩ := dealUpTo_lens x.drawStep x.stock
    have hsl : x.stock.length = 1 + t.length := by
      show (x.stock).length = 1 + t.length
      rw [hcon, List.length_cons]
      omega
    rcases Nat.lt_or_ge x.drawStep x.stock.length with hlt | hge
    · rw [Nat.min_eq_left (Nat.le_of_lt hlt)] at h1
      have hyne : y.stock ≠ [] := by
        intro hc0
        have hc2 : (State.dealUpTo x.drawStep x.stock).2 = ([] : List Card) :=
          hyS.symm.trans hc0
        rw [hc2, List.length_nil] at h2
        omega
      obtain ⟨c', t', hys⟩ := list_cons_of_ne_nil hyne
      have hdec : inPhase y = decide (y.waste.length % y.drawStep = 0) := by
        simp only [inPhase, hys]
      have hywl : y.waste.length = x.drawStep + x.waste.length := by
        rw [hyW, List.length_append, List.length_reverse, h1]
      rw [hdec, hywl, hyD, Nat.add_mod_left]
      exact decide_eq_true hres
    · rw [Nat.min_eq_right hge] at h1
      have hyv : y.stock = [] := by
        have hy0 : y.stock.length = 0 := by
          rw [hyS]
          omega
        exact List.length_eq_zero_iff.mp hy0
      exact inPhase_eq_true_of_nil hyv

/-! ### §1.5.3 The waste-free play discipline (Phase ports,
`Orig/Phase.lean:363, 515-757`) -/

/-- The two moves that spend a waste card (VERBATIM from
`Orig/Phase.lean:363`; the frozen `EdgeKit` twin is
`Orig/EdgeLabel.lean:2795`). -/
private def isWasteMove (m : Move) : Bool :=
  match m with
  | .wasteToFound _ => true
  | .wasteToTab _ _ => true
  | _ => false

/-- A play that spends a waste card strictly drops the cycle count
(PORTED VERBATIM from `Orig/Phase.lean:515`). -/
private theorem run_cycleCount_lt : ∀ {play : List Move} {x w : State},
    x.run play = some w → (∃ m ∈ play, isWasteMove m = true) →
    cycleCount w < cycleCount x := by
  intro play
  induction play with
  | nil =>
      intro x w _ hmem
      obtain ⟨m, hm, _⟩ := hmem
      exact absurd hm (by simp)
  | cons m rest ih =>
      intro x w hrun hmem
      obtain ⟨s₁, hm, hrs⟩ := State.run_cons hrun
      by_cases hmv : isWasteMove m = true
      · have hlt : cycleCount s₁ < cycleCount x := by
          cases m with
          | draw => simp [isWasteMove] at hmv
          | wasteToFound c => exact cycleCount_lt_wasteToFound hm
          | wasteToTab c b => exact cycleCount_lt_wasteToTab hm
          | tabToFound c => simp [isWasteMove] at hmv
          | foundToTab c b => simp [isWasteMove] at hmv
          | tabToTab c b => simp [isWasteMove] at hmv
        have hle := run_cycleCount_le hrs
        omega
      · obtain ⟨m', hm', hmis⟩ := hmem
        rcases List.mem_cons.1 hm' with heq | hmem2
        · exact absurd (heq ▸ hmis) hmv
        · have hlt := ih hrs ⟨m', hmem2, hmis⟩
          have hle := step_cycleCount_le m hm
          omega

/-- A list appended to a nonempty list is nonempty (PORTED VERBATIM
from `Orig/Phase.lean:548`). -/
private theorem append_ne_nil_right (A : List Card) {B : List Card}
    (h : B ≠ []) : A ++ B ≠ [] := by
  obtain ⟨b, bs, hb⟩ := list_cons_of_ne_nil h
  intro hc
  subst hb
  cases A <;> simp_all

/-- In a `wasteTo*`-free play at a positive draw step, a state with
a nonempty waste is never followed by one with an empty waste
(PORTED VERBATIM from `Orig/Phase.lean:559`; the board cells ride
this card's `board_fire_zone` in place of Phase's `*_fixed`
rows). -/
private theorem step_wasteNe_preserved {x y : State} (hd : 0 < x.drawStep)
    {m : Move} (hgood : isWasteMove m ≠ true) (hs : State.step x m = some y)
    (hw : x.waste ≠ []) : y.waste ≠ [] ∧ y.drawStep = x.drawStep := by
  cases m with
  | draw =>
      have hsuc : x.stepDraw = some y := hs
      refine ⟨?_, stepDraw_drawStep hsuc⟩
      by_cases hst : x.stock = []
      · obtain ⟨r, hrec, hrne, hy⟩ := draw_unfold hsuc
        have hrfl : r = { x with stock := x.waste.reverse, waste := [] } :=
          hrec.symm.trans (recycle_nil x hst hw)
        rw [hrfl] at hy
        have hyW : y.waste =
            (State.dealUpTo x.drawStep x.waste.reverse).1.reverse ++ ([] : List Card) := by
          rw [hy]
        obtain ⟨h1, _⟩ := dealUpTo_lens x.drawStep x.waste.reverse
        have hwr : (x.waste.reverse).length = x.waste.length := List.length_reverse
        have hwlen : 1 ≤ x.waste.length := by
          obtain ⟨c0, t0, hwcon⟩ := list_cons_of_ne_nil hw
          rw [hwcon, List.length_cons]
          omega
        rcases Nat.lt_or_ge x.drawStep x.waste.length with hlt | hge
        · rw [hwr, Nat.min_eq_left (Nat.le_of_lt hlt)] at h1
          intro hc0
          rw [hyW] at hc0
          have hlen := congrArg List.length hc0
          rw [List.length_append, List.length_reverse, List.length_nil] at hlen
          omega
        · rw [hwr, Nat.min_eq_right hge] at h1
          intro hc0
          rw [hyW] at hc0
          have hlen := congrArg List.length hc0
          rw [List.length_append, List.length_reverse, List.length_nil] at hlen
          omega
      · obtain ⟨r, hrec, hrne, hy⟩ := draw_unfold hsuc
        have hxr : x = r := ((recycle_keep x hst).symm).trans hrec
        rw [← hxr] at hy
        have hyW : y.waste = (State.dealUpTo x.drawStep x.stock).1.reverse ++ x.waste := by
          rw [hy]
        rw [hyW]
        exact append_ne_nil_right _ hw
  | wasteToFound c => simp [isWasteMove] at hgood
  | wasteToTab c b => simp [isWasteMove] at hgood
  | tabToFound c =>
      obtain ⟨-, h2, h3⟩ := board_fire_zone rfl hs
      exact ⟨by rw [h2]; exact hw, h3⟩
  | foundToTab c b =>
      obtain ⟨-, h2, h3⟩ := board_fire_zone rfl hs
      exact ⟨by rw [h2]; exact hw, h3⟩
  | tabToTab c b =>
      obtain ⟨-, h2, h3⟩ := board_fire_zone rfl hs
      exact ⟨by rw [h2]; exact hw, h3⟩

/-- The pristine run lift (PORTED VERBATIM from
`Orig/Phase.lean:621`). -/
private theorem run_wasteNe (st : State) : ∀ {play : List Move} {x w : State},
    0 < st.drawStep → (∀ m ∈ play, isWasteMove m ≠ true) →
    x.drawStep = st.drawStep → x.waste ≠ [] →
    x.run play = some w → w.waste ≠ [] ∧ w.drawStep = st.drawStep := by
  intro play
  induction play with
  | nil =>
      intro x w _hd _hgood hsd hw hrun
      have hx : some x = some w := hrun
      injection hx with h
      rw [← h]
      exact ⟨hw, hsd⟩
  | cons m rest ih =>
      intro x w hd hgood hsd hw hrun
      obtain ⟨s₁, hm, hrs⟩ := State.run_cons hrun
      have hmne : isWasteMove m ≠ true := hgood m (by simp)
      have hdx : 0 < x.drawStep := by
        rw [hsd]
        exact hd
      obtain ⟨hw', hsd'⟩ := step_wasteNe_preserved hdx hmne hm hw
      exact ih hd (fun m' hm' => hgood m' (by simp [hm'])) (hsd'.trans hsd) hw' hrs

/-- The committed successor of a pristine draw receives dealt cards
(PORTED VERBATIM from `Orig/Phase.lean:645`). -/
private theorem draw_pristine_s1 {st s₁ : State} (hd : 0 < st.drawStep)
    (hs : st.stock ≠ []) (hw : st.waste = []) (hsuc : st.stepDraw = some s₁) :
    s₁.waste ≠ [] ∧ s₁.drawStep = st.drawStep := by
  obtain ⟨r, hrec, hrne, hy⟩ := draw_unfold hsuc
  have hxr : st = r := ((recycle_keep st hs).symm).trans hrec
  rw [← hxr] at hy
  have hyW : s₁.waste =
      (State.dealUpTo st.drawStep st.stock).1.reverse ++ st.waste := by
    rw [hy]
  refine ⟨?_, stepDraw_drawStep hsuc⟩
  rw [hyW, hw]
  obtain ⟨h1, _⟩ := dealUpTo_lens st.drawStep st.stock
  obtain ⟨c, t, hcon⟩ := list_cons_of_ne_nil hs
  have hsl : st.stock.length = 1 + t.length := by
    show (st.stock).length = 1 + t.length
    rw [hcon, List.length_cons]
    omega
  rcases Nat.lt_or_ge st.drawStep st.stock.length with hlt | hge
  · rw [Nat.min_eq_left (Nat.le_of_lt hlt)] at h1
    intro hc0
    have hlen := congrArg List.length hc0
    rw [List.length_append, List.length_reverse, List.length_nil] at hlen
    omega
  · rw [Nat.min_eq_right hge] at h1
    intro hc0
    have hlen := congrArg List.length hc0
    rw [List.length_append, List.length_reverse, List.length_nil] at hlen
    omega

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

/-- The additive take split (PORTED VERBATIM from
`Orig/Phase.lean:1207`). -/
private theorem take_drop_add {α : Type} : ∀ (i j : Nat) (l : List α),
    l.take (i + j) = l.take i ++ (l.drop i).take j := by
  intro i
  induction i with
  | zero =>
      intro j l
      simp
  | succ i ih =>
      intro j l
      have hidx : i + 1 + j = i + j + 1 := by omega
      rw [hidx]
      cases l with
      | nil => simp only [List.take_nil, List.drop_nil, List.nil_append]
      | cons a t =>
          show a :: t.take (i + j) = a :: (t.take i ++ (t.drop i).take j)
          exact congrArg (a :: ·) (ih j t)

/-- The additive drop split (PORTED VERBATIM from
`Orig/Phase.lean:1232`). -/
private theorem drop_drop_add {α : Type} : ∀ (i j : Nat) (l : List α),
    (l.drop i).drop j = l.drop (i + j) := by
  intro i
  induction i with
  | zero =>
      intro j l
      simp
  | succ i ih =>
      intro j l
      have hidx : i + 1 + j = i + j + 1 := by omega
      rw [hidx]
      cases l with
      | nil => simp only [List.drop_nil]
      | cons a t =>
          show (t.drop i).drop j = t.drop (i + j)
          exact ih j t

/-- Take and drop recombine (PORTED VERBATIM from
`Orig/Phase.lean:1251`; the frozen `take_drop_join` of
`Orig/Classify.lean:1091` is this row's farm duplicate). -/
private theorem take_drop_append {α : Type} : ∀ (n : Nat) (l : List α),
    l.take n ++ l.drop n = l := by
  intro n
  induction n with
  | zero => intro l; simp
  | succ m ih =>
      intro l
      cases l with
      | nil => rfl
      | cons a t =>
          show a :: (t.take m ++ t.drop m) = a :: t
          exact congrArg (a :: ·) (ih t)

/-- Taking past (or exactly to) the end takes the whole (PORTED
VERBATIM from `Orig/Phase.lean:1266`). -/
private theorem take_ge_length {α : Type} : ∀ (l : List α) (n : Nat),
    l.length ≤ n → l.take n = l := by
  intro l
  induction l with
  | nil =>
      intro n _
      exact List.take_nil
  | cons a t ih =>
      intro n
      intro h
      match n with
      | 0 =>
          exact absurd h (by
            have hx : (a :: t).length = t.length + 1 := rfl
            omega)
      | m + 1 =>
          have hm : t.length ≤ m := by
            have hx : (a :: t).length = t.length + 1 := rfl
            omega
          show a :: t.take m = a :: t
          exact congrArg (a :: ·) (ih m hm)

/-! ### §1.5.5 The pure-draw mints (Phase/Classify ports) -/

/-- Dropping past (or exactly to) the end drops to nothing (PORTED
VERBATIM from `Orig/Phase.lean:1290`). -/
private theorem drop_ge_length {α : Type} : ∀ (l : List α) (n : Nat),
    l.length ≤ n → l.drop n = [] := by
  intro l
  induction l with
  | nil =>
      intro n _
      exact List.drop_nil
  | cons a t ih =>
      intro n
      intro h
      match n with
      | 0 =>
          exact absurd h (by
            have hx : (a :: t).length = t.length + 1 := rfl
            omega)
      | m + 1 =>
          have hm : t.length ≤ m := by
            have hx : (a :: t).length = t.length + 1 := rfl
            omega
          exact ih m hm

/-- The prefix clip on an appended list, drop side (PORTED VERBATIM
from `Orig/Phase.lean:1313`). -/
private theorem drop_append_prefix {α : Type} : ∀ (A B : List α),
    (A ++ B).drop A.length = B := by
  intro A
  induction A with
  | nil => intro B; rfl
  | cons a t ih =>
      intro B
      show (t ++ B).drop t.length = B
      exact ih B

/-- The prefix clip on an appended list, take side (PORTED VERBATIM
from `Orig/Phase.lean:1325`). -/
private theorem take_append_prefix {α : Type} : ∀ (A B : List α),
    (A ++ B).take A.length = A := by
  intro A
  induction A with
  | nil => intro B; rfl
  | cons a t ih =>
      intro B
      show a :: (t ++ B).take t.length = a :: t
      exact congrArg (a :: ·) (ih B)

/-- A full deal at a short stock (PORTED VERBATIM from
`Orig/Phase.lean:159`). -/
private theorem dealUpTo_all (k : Nat) : ∀ (l : List Card), l.length ≤ k →
    State.dealUpTo k l = (l, ([] : List Card)) := by
  induction k with
  | zero =>
      intro l hlen
      have hnil : l = [] := List.length_eq_zero_iff.mp (by omega)
      rw [hnil]
      rfl
  | succ k ih =>
      intro l hlen
      cases l with
      | nil => rfl
      | cons c cs =>
          have hcc : List.length (c :: cs) = List.length cs + 1 := List.length_cons
          have hcs : List.length cs ≤ k := by omega
          have hrs := ih cs hcs
          show State.dealUpTo (k+1) (c :: cs) = _
          rw [State.dealUpTo, hrs]

/-- The short-stock full deal, as a computed step (PORTED VERBATIM
from `Orig/Phase.lean:195`). -/
private theorem dealStock_full {st : State} (hs : st.stock ≠ [])
    (hsize : st.stock.length ≤ st.drawStep) :
    State.dealStock st = some
      { st with stock := ([] : List Card), waste := st.stock.reverse ++ st.waste } := by
  rw [dealStock_eq_of_ne_nil st hs, dealUpTo_all st.drawStep st.stock hsize]

/-- One plain draw (the stock is nonempty, so no recycle fires);
PORTED VERBATIM from `Orig/Phase.lean:1174`. -/
private theorem plain_draw_shape {x : State} (hne : x.stock ≠ []) :
    x.stepDraw = some
      { x with stock := x.stock.drop x.drawStep,
               waste := (x.stock.take x.drawStep).reverse ++ x.waste } := by
  rw [State.stepDraw, show State.recycle x = x from recycle_keep x hne,
    dealStock_eq_of_ne_nil x hne, dealUpTo_eq_take_drop]

/-- One pass-end draw (recycle fires, one clipped deal moves back);
PORTED VERBATIM from `Orig/Phase.lean:1184`. -/
private theorem base_draw_shape {x : State} (hstock : x.stock = ([] : List Card))
    (hw : x.waste ≠ []) :
    x.stepDraw = some
      { x with stock := x.waste.reverse.drop x.drawStep,
               waste := (x.waste.reverse.take x.drawStep).reverse ++ ([] : List Card) } := by
  have hrne : x.waste.reverse ≠ [] := by
    intro hc
    have hlen := congrArg List.length hc
    rw [List.length_reverse, List.length_nil] at hlen
    obtain ⟨c0, t0, hwcon0⟩ := list_cons_of_ne_nil hw
    have h1 : 1 ≤ x.waste.length := by
      rw [hwcon0, List.length_cons]
      omega
    omega
  rw [State.stepDraw, recycle_nil x hstock hw,
    dealStock_eq_of_ne_nil _ hrne, dealUpTo_eq_take_drop]

/-- The short-stock full deal as a computed `State.step` (PORTED
VERBATIM from `Orig/Phase.lean:1495`). -/
private theorem draw_full_shape (x : State) (hne : x.stock ≠ [])
    (hx : x.stock.length < x.drawStep) :
    State.step x Move.draw = some
      (State.mk x.found x.piles ([] : List Card) (x.stock.reverse ++ x.waste) x.drawStep) := by
  have ge := Nat.le_of_lt hx
  rw [show State.step x Move.draw = x.stepDraw from rfl, plain_draw_shape hne,
    drop_ge_length x.stock x.drawStep ge, take_ge_length x.stock x.drawStep ge]

/-- The pass-end full redeal, as a computed no-op step (PORTED
VERBATIM from `Orig/Phase.lean:775`). -/
private theorem selfRecycle_draw {st : State} (hstock : st.stock = [])
    (hw : st.waste ≠ []) (hsize : st.waste.length ≤ st.drawStep) :
    State.step st Move.draw = some st := by
  show st.stepDraw = some st
  rw [State.stepDraw, recycle_nil st hstock hw]
  have hrne : st.waste.reverse ≠ [] := by
    intro hc
    have hlen := congrArg List.length hc
    rw [List.length_reverse, List.length_nil] at hlen
    obtain ⟨c0, t0, hwcon0⟩ := list_cons_of_ne_nil hw
    have h1 : 1 ≤ st.waste.length := by
      rw [hwcon0, List.length_cons]
      omega
    omega
  have hfull : State.dealStock { st with stock := st.waste.reverse, waste := [] } = some { st with stock := ([] : List Card), waste := (st.waste.reverse).reverse ++ ([] : List Card) } :=
    dealStock_full (st := { st with stock := st.waste.reverse, waste := [] })
      (by
        show st.waste.reverse ≠ []
        exact hrne)
      (by
        show (st.waste.reverse).length ≤ st.drawStep
        rw [List.length_reverse]
        exact hsize)
  rw [hfull, List.reverse_reverse, List.append_nil, ← hstock]

/-- The pass-end full redeal, WITNESS form (PORTED VERBATIM from
`Orig/Phase.lean:884`). -/
private theorem draw_reversible_selfRecycleW {st : State} (hstock : st.stock = [])
    (hw : st.waste ≠ []) (hsize : st.waste.length ≤ st.drawStep) :
    reversibleAtW st Move.draw :=
  ⟨st, [], selfRecycle_draw hstock hw hsize, rfl⟩

/-- One draw followed by the rest of the play (PORTED VERBATIM from
`Orig/Phase.lean:1353`). -/
private theorem run_draw_cons {x y : State} {rest : List Move}
    (hstep : State.step x Move.draw = some y) :
    x.run (Move.draw :: rest) = y.run rest := by
  show (match State.step x Move.draw with
      | some st' => State.run st' rest
      | none => none) = State.run y rest
  rw [hstep]

/-- Append-glue for pure-draw plays (PORTED VERBATIM from
`Orig/Phase.lean:1363`). -/
private theorem run_replicate_append :
    ∀ (q : Nat) (x z : State) (rest : List Move),
    x.run (List.replicate q Move.draw) = some z →
    x.run (List.replicate q Move.draw ++ rest) = z.run rest := by
  intro q
  induction q with
  | zero =>
      intro x z rest h
      have hx : (some x : Option State) = some z := h
      injection hx with hx2
      rw [← hx2]
      rfl
  | succ q ih =>
      intro x z rest h
      obtain ⟨y, hstep, hrest⟩ := State.run_cons h
      show x.run (Move.draw :: (List.replicate q Move.draw ++ rest)) = z.run rest
      rw [run_draw_cons hstep]
      exact ih y z rest hrest

/-- The run-composition shape (PORTED VERBATIM from
`Orig/Classify.lean:1124`). -/
private theorem run_cons_shape {s : State} {m : Move} {rest : List Move} {s' w : State}
    (hstep : State.step s m = some s') (hrun : s'.run rest = some w) :
    s.run (m :: rest) = some w := by
  simp only [State.run, hstep]
  exact hrun

/-- The pure-draw drain to the pass base (PORTED VERBATIM from
`Orig/Classify.lean:1133`; `take_drop_join` there is this card's
`take_drop_append`, the Phase home). -/
private theorem drain_to_pass : ∀ (n : Nat) (l : List Card) (s : State), l.length ≤ n →
    0 < s.drawStep → s.stock = l →
    ∃ play, s.run play = some
      { s with stock := ([] : List Card), waste := l.reverse ++ s.waste } := by
  intro n
  induction n with
  | zero =>
      intro l s hlen hd hstock
      have hnil : l = [] := by
        cases l with
        | nil => rfl
        | cons w t =>
            have h1 : (w :: t).length = t.length + 1 := rfl
            omega
      subst hnil
      refine ⟨[], ?_⟩
      have hrfl : s.run [] = some s := rfl
      rw [hrfl]
      refine congrArg some (State.ext rfl rfl hstock ?_ rfl)
      rfl
  | succ n ih =>
      intro l s hlen hd hstock
      have hsplit : l = [] ∨ ∃ w t, l = w :: t := by
        cases l with
        | nil => exact Or.inl rfl
        | cons w t => exact Or.inr ⟨w, t, rfl⟩
      rcases hsplit with hnil | ⟨w, t, hcon⟩
      · subst hnil
        refine ⟨[], ?_⟩
        have hrfl : s.run [] = some s := rfl
        rw [hrfl]
        refine congrArg some (State.ext rfl rfl hstock ?_ rfl)
        rfl
      · subst hcon
        have hne : s.stock ≠ [] := by
          intro hc
          rw [hstock] at hc
          exact absurd hc (by simp)
        have hstep : State.step s Move.draw = some
            { s with stock := s.stock.drop s.drawStep, waste := (s.stock.take s.drawStep).reverse ++ s.waste } :=
          plain_draw_shape hne
        have hdrop : (s.stock.drop s.drawStep).length ≤ n := by
          rw [hstock]
          have hd2 := List.length_drop (l := w :: t) (i := s.drawStep)
          have hl : (w :: t).length = t.length + 1 := rfl
          omega
        have hstock₂ : { s with stock := s.stock.drop s.drawStep, waste := (s.stock.take s.drawStep).reverse ++ s.waste }.stock
            = s.stock.drop s.drawStep := rfl
        obtain ⟨play', hrun'⟩ := ih (s.stock.drop s.drawStep)
          { s with stock := s.stock.drop s.drawStep, waste := (s.stock.take s.drawStep).reverse ++ s.waste }
          hdrop hd hstock₂
        refine ⟨Move.draw :: play', ?_⟩
        refine run_cons_shape hstep ?_
        rw [hrun']
        have hEqd : (s.stock.drop s.drawStep).reverse
              ++ (s.stock.take s.drawStep).reverse = s.stock.reverse := by
          rw [show (s.stock.drop s.drawStep).reverse ++ (s.stock.take s.drawStep).reverse
                = ((s.stock.take s.drawStep) ++ s.stock.drop s.drawStep).reverse from
                by rw [List.reverse_append],
              take_drop_append s.drawStep s.stock]
        rw [show (s.stock.drop s.drawStep).reverse
              ++ ((s.stock.take s.drawStep).reverse ++ s.waste)
              = ((s.stock.drop s.drawStep).reverse ++ (s.stock.take s.drawStep).reverse) ++ s.waste from
              by rw [← List.append_assoc],
            hEqd]
        refine congrArg some (State.ext rfl rfl rfl ?_ rfl)
        rw [hstock]

/-- **The pass-base round trip** (PORTED VERBATIM from
`Orig/Classify.lean:1206`). -/
private theorem draw_passBase_reversibleW {st : State}
    (hstock : st.stock = ([] : List Card)) (hw : st.waste ≠ []) (hd : 0 < st.drawStep) :
    reversibleAtW st Move.draw := by
  by_cases hsize : st.waste.length ≤ st.drawStep
  · exact draw_reversible_selfRecycleW hstock hw hsize
  · have hstep : State.step st Move.draw = some
        { st with stock := st.waste.reverse.drop st.drawStep,
                  waste := (st.waste.reverse.take st.drawStep).reverse ++ ([] : List Card) } :=
      base_draw_shape hstock hw
    have hdropLen : (st.waste.reverse.drop st.drawStep).length ≤ st.waste.length := by
      have hd2 := List.length_drop (l := st.waste.reverse) (i := st.drawStep)
      have hrev : st.waste.reverse.length = st.waste.length := by rw [List.length_reverse]
      omega
    have hstock₂ : { st with stock := st.waste.reverse.drop st.drawStep, waste := (st.waste.reverse.take st.drawStep).reverse ++ ([] : List Card) }.stock
        = st.waste.reverse.drop st.drawStep := rfl
    have hstepPos : 0 < { st with stock := st.waste.reverse.drop st.drawStep, waste := (st.waste.reverse.take st.drawStep).reverse ++ ([] : List Card) }.drawStep := hd
    obtain ⟨play, hrun⟩ := drain_to_pass st.waste.length
      (st.waste.reverse.drop st.drawStep)
      { st with stock := st.waste.reverse.drop st.drawStep, waste := (st.waste.reverse.take st.drawStep).reverse ++ ([] : List Card) }
      hdropLen hstepPos hstock₂
    refine ⟨_, play, hstep, ?_⟩
    rw [hrun]
    have hwE : (st.waste.reverse.drop st.drawStep).reverse
        ++ ((st.waste.reverse.take st.drawStep).reverse ++ ([] : List Card))
        = st.waste := by
      rw [List.append_nil,
        show (st.waste.reverse.drop st.drawStep).reverse
            ++ (st.waste.reverse.take st.drawStep).reverse
            = ((st.waste.reverse.take st.drawStep) ++ st.waste.reverse.drop st.drawStep).reverse from
            by rw [List.reverse_append],
        take_drop_append st.drawStep st.waste.reverse, List.reverse_reverse]
    refine congrArg some (State.ext rfl rfl hstock.symm hwE rfl)

/-- **The drain positions** — `q` consecutive full deals move
exactly `q * drawStep` cards (PORTED VERBATIM from
`Orig/Phase.lean:1386`). -/
private theorem drain_positions_one :
    ∀ (q : Nat) (x : State) (n : Nat) (l : List Card),
    0 < x.drawStep → n = q * x.drawStep → n ≤ l.length → x.stock = l →
    x.run (List.replicate q Move.draw) = some
      { x with stock := l.drop n, waste := (l.take n).reverse ++ x.waste } := by
  intro q
  induction q with
  | zero =>
      intro x n l _hd hn _hle hstock
      have hn0 : n = 0 := by
        rw [Nat.zero_mul] at hn
        exact hn
      subst hn0
      show (some x : Option State) = some
        { x with stock := l.drop 0, waste := (l.take 0).reverse ++ x.waste }
      rw [List.drop_zero, List.take_zero, List.reverse_nil, List.nil_append,
        ← hstock]
  | succ q ih =>
      intro x n l hd hn hle hstock
      have hnsm : n = q * x.drawStep + x.drawStep := by
        rw [Nat.succ_mul] at hn
        exact hn
      have hlne : l ≠ [] := by
        intro hc
        have hlen : l.length = 0 := by rw [hc]; simp
        omega
      have hsne : x.stock ≠ [] := by
        intro hc
        apply hlne
        rw [← hstock]
        exact hc
      have hstep : State.step x Move.draw = some
          { x with stock := x.stock.drop x.drawStep,
                   waste := (x.stock.take x.drawStep).reverse ++ x.waste } :=
        plain_draw_shape hsne
      have hrep : List.replicate (q + 1) Move.draw
          = Move.draw :: List.replicate q Move.draw := rfl
      rw [hrep, run_draw_cons hstep, hstock]
      have hle' : q * x.drawStep ≤ (l.drop x.drawStep).length := by
        have h1 := List.length_drop (i := x.drawStep) (l := l)
        omega
      have hres := ih
        { x with stock := l.drop x.drawStep,
                 waste := (l.take x.drawStep).reverse ++ x.waste }
        (q * x.drawStep) (l.drop x.drawStep) hd rfl hle' rfl
      rw [hres]
      have hSw : (show State from
          { x with stock := l.drop x.drawStep,
                   waste := (l.take x.drawStep).reverse ++ x.waste }).waste
          = (l.take x.drawStep).reverse ++ x.waste := rfl
      rw [hSw]
      have hidx : x.drawStep + q * x.drawStep = n := by omega
      rw [drop_drop_add x.drawStep (q * x.drawStep) l, hidx]
      have hmerge : (List.take (q * x.drawStep) (List.drop x.drawStep l)).reverse
            ++ ((List.take x.drawStep l).reverse ++ x.waste)
          = (l.take (x.drawStep + q * x.drawStep)).reverse ++ x.waste := by
        rw [take_drop_add, List.reverse_append, List.append_assoc]
      rw [hmerge, hidx]

/-- **The redeal positions** — from a pass base, `k + 1`
consecutive draws move exactly that many cards back (PORTED
VERBATIM from `Orig/Phase.lean:1451`). -/
private theorem base_positions_one :
    ∀ (k : Nat) (x : State),
    x.stock = ([] : List Card) → x.waste ≠ [] → 0 < x.drawStep →
    (k + 1) * x.drawStep ≤ x.waste.length →
    x.run (List.replicate (k + 1) Move.draw) = some
      { x with stock := x.waste.reverse.drop ((k + 1) * x.drawStep),
               waste := (x.waste.reverse.take ((k + 1) * x.drawStep)).reverse ++ ([] : List Card) } := by
  intro k x hstock hw hd hsize
  rw [Nat.succ_mul] at hsize
  have hstep : State.step x Move.draw = some
      { x with stock := x.waste.reverse.drop x.drawStep,
               waste := (x.waste.reverse.take x.drawStep).reverse ++ ([] : List Card) } :=
    base_draw_shape hstock hw
  rw [show List.replicate (k + 1) Move.draw
        = Move.draw :: List.replicate k Move.draw from rfl,
    run_draw_cons hstep]
  have hle' : k * x.drawStep ≤ (x.waste.reverse.drop x.drawStep).length := by
    have h1 := List.length_drop (i := x.drawStep) (l := x.waste.reverse)
    have h2 : x.waste.reverse.length = x.waste.length := List.length_reverse
    omega
  have hres := drain_positions_one k
    { x with stock := x.waste.reverse.drop x.drawStep,
             waste := (x.waste.reverse.take x.drawStep).reverse ++ ([] : List Card) }
    (k * x.drawStep) (x.waste.reverse.drop x.drawStep) hd rfl hle' rfl
  rw [hres]
  have hSw : (show State from
      { x with stock := x.waste.reverse.drop x.drawStep,
               waste := (x.waste.reverse.take x.drawStep).reverse ++ ([] : List Card) }).waste
      = (x.waste.reverse.take x.drawStep).reverse ++ ([] : List Card) := rfl
  rw [hSw]
  have hidx : x.drawStep + k * x.drawStep = (k + 1) * x.drawStep := by
    rw [Nat.succ_mul]; omega
  rw [drop_drop_add x.drawStep (k * x.drawStep) x.waste.reverse, hidx]
  have hmerge : (List.take (k * x.drawStep)
          (List.drop x.drawStep x.waste.reverse)).reverse
        ++ ((List.take x.drawStep x.waste.reverse).reverse ++ ([] : List Card))
      = ((List.take (x.drawStep + k * x.drawStep) x.waste.reverse).reverse
          ++ ([] : List Card)) := by
    rw [take_drop_add, List.reverse_append, List.append_assoc]
  rw [hmerge, hidx]

/-- **The in-phase round trip, WITNESS form** — at a phase-aligned
position the draw is undone by an explicit pure-draw play: drain
the committed stock to the pass base (whole deals plus the
boundary deal), then redeal the waste's whole number of deals from
the recycled pool (PORTED VERBATIM from `Orig/Phase.lean:1513`).
-/
private theorem draw_reversible_inphaseW {st : State} (hd : 0 < st.drawStep)
    (hs : st.stock ≠ []) (hw : st.waste ≠ []) (hph : inPhase st = true) :
    reversibleAtW st Move.draw := by
  obtain ⟨c, t, hcon⟩ := list_cons_of_ne_nil hs
  have hres0 : st.waste.length % st.drawStep = 0 := by
    rw [inPhase_eq_decide_of_cons hcon] at hph
    exact of_decide_eq_true hph
  have hjd : st.drawStep * (st.waste.length / st.drawStep) = st.waste.length := by
    have := Nat.div_add_mod st.waste.length st.drawStep
    omega
  have hstep : State.step st Move.draw = some
      (State.mk st.found st.piles (st.stock.drop st.drawStep)
        ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep) :=
    plain_draw_shape hs
  obtain ⟨w0, t0, hwcon⟩ := list_cons_of_ne_nil hw
  have hw1 : 1 ≤ st.waste.length := by rw [hwcon, List.length_cons]; omega
  have hp1 : 1 ≤ st.stock.length := by rw [hcon, List.length_cons]; omega
  have hNl : (st.stock.reverse ++ st.waste).length
      = st.stock.length + st.waste.length := by
    rw [List.length_append, List.length_reverse]
  have hpool : (st.stock.drop st.drawStep).reverse
      ++ ((st.stock.take st.drawStep).reverse ++ st.waste)
      = st.stock.reverse ++ st.waste := by
    rw [show st.stock.reverse
          = (st.stock.take st.drawStep ++ st.stock.drop st.drawStep).reverse from
          congrArg List.reverse (take_drop_append st.drawStep st.stock).symm,
      List.reverse_append, List.append_assoc]
  rcases hqj : st.waste.length / st.drawStep with _ | jk
  · exfalso
    rw [hqj, Nat.mul_zero] at hjd
    omega
  rw [hqj] at hjd
  have hjd2 : (jk + 1) * st.drawStep = st.waste.length := by
    rw [Nat.mul_comm]
    exact hjd
  have hwB : (st.stock.reverse ++ st.waste) ≠ [] := by
    intro hc
    rw [hc] at hNl
    simp only [List.length_nil] at hNl
    omega
  have hsizeB : (jk + 1) * st.drawStep
      ≤ (st.stock.reverse ++ st.waste).length := by rw [hNl]; omega
  have hmfull :=
    Nat.div_add_mod (st.stock.drop st.drawStep).length st.drawStep
  have hmodlt : (st.stock.drop st.drawStep).length % st.drawStep < st.drawStep :=
    Nat.mod_lt _ hd
  by_cases hdr : (st.stock.drop st.drawStep).length % st.drawStep = 0
  · have hnA : (st.stock.drop st.drawStep).length
        = ((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep := by
      rw [Nat.mul_comm]
      omega
    have hDA := drain_positions_one
      ((st.stock.drop st.drawStep).length / st.drawStep)
      (State.mk st.found st.piles (st.stock.drop st.drawStep)
        ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep)
      (st.stock.drop st.drawStep).length
      (st.stock.drop st.drawStep)
      hd hnA (Nat.le_refl _) rfl
    have hdrop0 : (st.stock.drop st.drawStep).drop
        (st.stock.drop st.drawStep).length = [] :=
      drop_ge_length _ _ (Nat.le_refl _)
    have htake0 : (st.stock.drop st.drawStep).take
        (st.stock.drop st.drawStep).length = st.stock.drop st.drawStep :=
      take_ge_length _ _ (Nat.le_refl _)
    have hSw1 : (State.mk st.found st.piles (st.stock.drop st.drawStep)
        ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep).waste
        = (st.stock.take st.drawStep).reverse ++ st.waste := rfl
    refine ⟨State.mk st.found st.piles (st.stock.drop st.drawStep)
        ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep,
      List.replicate ((st.stock.drop st.drawStep).length / st.drawStep) Move.draw
        ++ List.replicate (jk + 1) Move.draw,
      hstep, ?_⟩
    rw [run_replicate_append _ _ _ (List.replicate (jk + 1) Move.draw) hDA,
      hdrop0, htake0, hSw1, hpool]
    have hb := base_positions_one jk
      (State.mk st.found st.piles ([] : List Card) (st.stock.reverse ++ st.waste) st.drawStep)
      rfl hwB hd hsizeB
    rw [hb]
    have hz1w : (State.mk st.found st.piles ([] : List Card)
        (st.stock.reverse ++ st.waste) st.drawStep).waste
        = st.stock.reverse ++ st.waste := rfl
    have hz1d : (State.mk st.found st.piles ([] : List Card)
        (st.stock.reverse ++ st.waste) st.drawStep).drawStep
        = st.drawStep := rfl
    rw [hz1w, hz1d]
    have hSpl : st.waste.reverse ++ st.stock
        = (st.stock.reverse ++ st.waste).reverse := by
      rw [List.reverse_append, List.reverse_reverse]
    rw [← hSpl, hjd2, ← List.length_reverse, drop_append_prefix, take_append_prefix,
      List.reverse_reverse, List.append_nil]
  · have hqB : ((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep
        + (st.stock.drop st.drawStep).length % st.drawStep
        = (st.stock.drop st.drawStep).length := by
      have h := hmfull
      rw [Nat.mul_comm] at h
      exact h
    have hDB := drain_positions_one
      ((st.stock.drop st.drawStep).length / st.drawStep)
      (State.mk st.found st.piles (st.stock.drop st.drawStep)
        ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep)
      (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep)
      (st.stock.drop st.drawStep)
      hd rfl (by omega) rfl
    have hDB2 : (State.mk st.found st.piles (st.stock.drop st.drawStep)
          ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep).run
          (List.replicate ((st.stock.drop st.drawStep).length / st.drawStep) Move.draw) = some
      (State.mk st.found st.piles
        ((st.stock.drop st.drawStep).drop
          (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep))
        ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
            (List.drop st.drawStep st.stock)).reverse
          ++ ((st.stock.take st.drawStep).reverse ++ st.waste))
        st.drawStep) := by
      have hXf : (State.mk st.found st.piles (st.stock.drop st.drawStep)
          ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep).found
          = st.found := rfl
      have hXp : (State.mk st.found st.piles (st.stock.drop st.drawStep)
          ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep).piles
          = st.piles := rfl
      have hXw : (State.mk st.found st.piles (st.stock.drop st.drawStep)
          ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep).waste
          = (st.stock.take st.drawStep).reverse ++ st.waste := rfl
      have hXd : (State.mk st.found st.piles (st.stock.drop st.drawStep)
          ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep).drawStep
          = st.drawStep := rfl
      rw [hDB, hXf, hXp, hXw, hXd]
    have hx₀ne : (st.stock.drop st.drawStep).drop
        (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep) ≠ [] := by
      intro hc
      have hld := List.length_drop
        (i := ((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep)
        (l := st.stock.drop st.drawStep)
      rw [hc] at hld
      simp only [List.length_nil] at hld
      omega
    have hx₀len : ((st.stock.drop st.drawStep).drop
        (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep)).length
        < st.drawStep := by
      have hld := List.length_drop
        (i := ((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep)
        (l := st.stock.drop st.drawStep)
      rw [hld]
      omega
    have hBstep : State.step
        (State.mk st.found st.piles
          ((st.stock.drop st.drawStep).drop
            (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep))
          ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
              (List.drop st.drawStep st.stock)).reverse
            ++ ((st.stock.take st.drawStep).reverse ++ st.waste))
          st.drawStep) Move.draw = some
        (State.mk (State.mk st.found st.piles
            ((st.stock.drop st.drawStep).drop
              (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep))
            ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
                (List.drop st.drawStep st.stock)).reverse
              ++ ((st.stock.take st.drawStep).reverse ++ st.waste))
            st.drawStep).found
          (State.mk st.found st.piles
            ((st.stock.drop st.drawStep).drop
              (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep))
            ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
                (List.drop st.drawStep st.stock)).reverse
              ++ ((st.stock.take st.drawStep).reverse ++ st.waste))
            st.drawStep).piles
          ([] : List Card)
          ((State.mk st.found st.piles
            ((st.stock.drop st.drawStep).drop
              (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep))
            ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
                (List.drop st.drawStep st.stock)).reverse
              ++ ((st.stock.take st.drawStep).reverse ++ st.waste))
            st.drawStep).stock.reverse
            ++ (State.mk st.found st.piles
                ((st.stock.drop st.drawStep).drop
                  (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep))
                ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
                    (List.drop st.drawStep st.stock)).reverse
                  ++ ((st.stock.take st.drawStep).reverse ++ st.waste))
                st.drawStep).waste)
          (State.mk st.found st.piles
            ((st.stock.drop st.drawStep).drop
              (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep))
            ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
                (List.drop st.drawStep st.stock)).reverse
              ++ ((st.stock.take st.drawStep).reverse ++ st.waste))
            st.drawStep).drawStep) :=
      draw_full_shape
        (State.mk st.found st.piles
          ((st.stock.drop st.drawStep).drop
            (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep))
          ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
              (List.drop st.drawStep st.stock)).reverse
            ++ ((st.stock.take st.drawStep).reverse ++ st.waste))
          st.drawStep)
        hx₀ne hx₀len
    have hySt : (show State from
        State.mk st.found st.piles
          ((st.stock.drop st.drawStep).drop
            (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep))
          ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
              (List.drop st.drawStep st.stock)).reverse
            ++ ((st.stock.take st.drawStep).reverse ++ st.waste))
          st.drawStep).stock
        = (st.stock.drop st.drawStep).drop
            (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep) := rfl
    have hyWs : (show State from
        State.mk st.found st.piles
          ((st.stock.drop st.drawStep).drop
            (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep))
          ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
              (List.drop st.drawStep st.stock)).reverse
            ++ ((st.stock.take st.drawStep).reverse ++ st.waste))
          st.drawStep).waste
        = (List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
              (List.drop st.drawStep st.stock)).reverse
            ++ ((st.stock.take st.drawStep).reverse ++ st.waste) := rfl
    have hpool2 : (((st.stock.drop st.drawStep).drop
            (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep)).reverse
          ++ ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
              (List.drop st.drawStep st.stock)).reverse
            ++ ((st.stock.take st.drawStep).reverse ++ st.waste)))
        = st.stock.reverse ++ st.waste := by
      rw [show st.stock.reverse
            = (st.stock.take st.drawStep ++ st.stock.drop st.drawStep).reverse from
            congrArg List.reverse (take_drop_append st.drawStep st.stock).symm,
        List.reverse_append,
        show (st.stock.drop st.drawStep).reverse
            = ((st.stock.drop st.drawStep).take
                (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep)
              ++ (st.stock.drop st.drawStep).drop
                (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep)).reverse from
            congrArg List.reverse
              (take_drop_append
                (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep)
                (st.stock.drop st.drawStep)).symm,
        List.reverse_append]
      simp only [List.append_assoc]
    refine ⟨State.mk st.found st.piles (st.stock.drop st.drawStep)
        ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep,
      List.replicate
        ((st.stock.drop st.drawStep).length / st.drawStep) Move.draw
        ++ (Move.draw :: List.replicate (jk + 1) Move.draw),
      hstep, ?_⟩
    rw [run_replicate_append _ _ _
      (Move.draw :: List.replicate (jk + 1) Move.draw) hDB2,
      run_draw_cons hBstep]
    rw [hySt, hyWs, hpool2]
    have hb := base_positions_one jk
      (State.mk st.found st.piles ([] : List Card) (st.stock.reverse ++ st.waste) st.drawStep)
      rfl hwB hd hsizeB
    rw [hb]
    have hz1w : (State.mk st.found st.piles ([] : List Card)
        (st.stock.reverse ++ st.waste) st.drawStep).waste
        = st.stock.reverse ++ st.waste := rfl
    have hz1d : (State.mk st.found st.piles ([] : List Card)
        (st.stock.reverse ++ st.waste) st.drawStep).drawStep
        = st.drawStep := rfl
    rw [hz1w, hz1d]
    have hSpl : st.waste.reverse ++ st.stock
        = (st.stock.reverse ++ st.waste).reverse := by
      rw [List.reverse_append, List.reverse_reverse]
    rw [← hSpl, hjd2, ← List.length_reverse, drop_append_prefix, take_append_prefix,
      List.reverse_reverse, List.append_nil]

/-! ### §1.5.6 The witness-grade draw commit rows (Phase
restatements)

The pristine/offset commitments restated DIRECTLY at witness
grade — the witness's own 4-tuple supplies the successor, play and
firing, so the frozen route's `Orig/Fate.lean` semantic pair and
`Orig/Mono.lean` descent bridge never enter (templates:
`Orig/Phase.lean:823` `draw_irreversible_offset` and `:853`
`draw_irreversible_pristine`, bodies carried verbatim). -/

/-- **Draws at pristine positions are commitments**, witness grade:
no returning play exists (RESTATE of `Orig/Phase.lean:853`).
-/
private theorem draw_not_revW_pristine {st : State}
    (hd : 0 < st.drawStep) (hs : st.stock ≠ []) (hw : st.waste = []) :
    ¬ reversibleAtW st Move.draw := by
  rintro ⟨s₁, play, hstep, hrun⟩
  have hsuc : st.stepDraw = some s₁ := hstep
  have hnoWaste : ∀ m ∈ play, isWasteMove m ≠ true := by
    intro m hm hc
    have hlt := run_cycleCount_lt hrun ⟨m, hm, hc⟩
    have hcc := draw_cycleCount hsuc
    rw [hcc] at hlt
    omega
  obtain ⟨hw₁, hsd₁⟩ := draw_pristine_s1 hd hs hw hsuc
  exact (run_wasteNe st hd hnoWaste hsd₁ hw₁ hrun).1 hw

/-- **Draws at offset positions are commitments**, witness grade
(RESTATE of `Orig/Phase.lean:823`; first-pass length never
re-attained, post-recycle alignment forever). -/
private theorem draw_not_revW_offset {st : State}
    (hd : 0 < st.drawStep) (hs : st.stock ≠ [])
    (hoff : st.waste.length % st.drawStep ≠ 0) :
    ¬ reversibleAtW st Move.draw := by
  rintro ⟨s₁, play, hstep, hrun⟩
  have hsuc : st.stepDraw = some s₁ := hstep
  obtain ⟨c, t, hcon⟩ := list_cons_of_ne_nil hs
  have hinF : inPhase st = false := by
    rw [inPhase_eq_decide_of_cons hcon, decide_eq_false hoff]
  have hnoWaste : ∀ m ∈ play, isWasteMove m ≠ true := by
    intro m hm hc
    have hlt := run_cycleCount_lt hrun ⟨m, hm, hc⟩
    have hcc := draw_cycleCount hsuc
    rw [hcc] at hlt
    omega
  have hsd : s₁.drawStep = st.drawStep := stepDraw_drawStep hsuc
  have hbase : beforeOriginOrAligned st s₁ := Or.inl (draw_dropStock hsuc hd hs)
  have hfinal : beforeOriginOrAligned st st :=
    run_inv_preserved hd hsd hnoWaste hbase hrun
  rcases hfinal with hlt | hph
  · exact absurd hlt (Nat.lt_irrefl _)
  · rw [hinF] at hph
    exact absurd hph (by simp)

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
#print axioms draw_reversible_selfRecycleW
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
