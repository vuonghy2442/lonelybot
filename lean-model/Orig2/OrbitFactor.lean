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
