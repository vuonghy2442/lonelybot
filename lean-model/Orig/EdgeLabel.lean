import Orig.Canonical
import Orig.Classify
import Orig.Reach
import Orig.Twin

/-!
# Orig — the member-form edge labels (the TipEdge scheme and the
class-pair fingerprint)

`FUTURES-ORIG.md` §3.1, THE EDGE-LABELING THEOREM (the user's
proposal, refined through the 2026-10-10 dialogue; the assembly's
SECOND milestone, standalone on landed content), with the same day's
restated headline: *what committed move can happen between two macro
neighbors is a property of the class pair* — a draw only from a
non-pure tip, a waste exit only of one pinned card, a tableau event
only at one pinned seat (and, in the reveal cell, of one pinned
revealed card).

## The design ledger (the day's arc, recorded)

The anchor-form scheme — a tip anchored at a canonical (Final) state,
carrying an explicit `ShufflePlayW` padding from the anchor to the
commit tip — was litigated field by field through the 2026-10-10 day
(the `hfin` saturation grade, the name, the padding), and the
member-form won on the merits; this drop is that recorded design
flip, not a fence.  Three dissolutions follow, each recorded in the
status section below:

* **the padding left the type.**  A macro transition is now one
  member of the source class plus its single commitment plus the
  class closure (`structure TipEdge (C D : SameOrbit)`) — the
  journey machinery the padding re-witnessed per edge is already the
  books' class relation, and the datum-carry the padding performed
  is the lift `datumOf` (the ladder's datums half is its soundness).
* **the canonical-anchor grade dissolved.**  Classes do not pretend
  literal-canonicality — saturation is member-relative (the residue
  exhibit is the recorded fact) — so `Final` downgrades from a
  structure field to `CanonicalTip`, one line of premise-sugar: the
  count program's discipline cites it as a premise, and the
  transport constructs it for free (the canon member is Final by
  construction).
* **the orbit-independence cell dissolved into the lift.**
  `canonLabel_orbit_indep` is removed, its content definitional: the
  read is independent of the member because `datumOf` is
  well-defined on classes (`labelOf_pair` is `rfl`), so the label is
  a literal function of the pair.

## The normal form

`TipEdge C D` — the recorded §3.1 structure, member-form: a macro
transition is **one WF member of the source class + its membership +
exactly one commitment firing at it + the class closure of the
landing**.  A macro transition does not have a unique underlying
MOVE (the twin-landing merge is one edge, two moves), but every
macro transition has this form; the single commit slot is structural
— a chain's first commit already exits its class
(`tipEdge_exits_source` is the phase-progress cell reading of
exactly that), so multi-commit edges are impossible: every subsequent
commit is its own edge.  The tip saturation the count program's
successor discipline rides is the premise-sugar `CanonicalTip`
(member-relative, never a structure field).

## The fingerprint route (why the label is a function of the pair)

Four journey-invariant datums are proved once, here, and consumed
everywhere; the quotient datum kernel descends them to the classes,
so the four are the class read's fields (`cycle`/`pool`/`hidden`/
`roots` — the field alignment `MacroDatums` was designed for):

* `cycleCount` — never rises under any single move; a witness-shuffle
  leg conserves it exactly (waste legs cannot appear at all — they
  are commitments at every position), so it is constant on macro
  classes — the `cycle` field;
* the per-anchor hidden lists — no witness leg ever touches them
  (only reveals move hidden cards, and reveals are commitments by
  the hidden-descent rows), so they are literal macro-class
  invariants — the `hidden` field — stronger than the hidden *total*
  the classification tables grade;
* `drawPool` — draws conserve the pool (the recycle reverses, the
  deal splits without loss), waste legs cannot appear, every other
  move keeps the draw zone verbatim — constant on macro classes —
  the `pool` field;
* `nzRoot` — the bare non-king root of a seat (its bottom face-up
  card when that is not a king) never moves under a witness leg
  (every root departure is a commitment: the seat-physics rows for
  non-kings, the hidden-descent rows for reveals) — a macro-class
  invariant per anchor — the `roots` field.

The committed move then writes exactly one of four signatures onto
the pair's class data:

* **draw** — nothing else changes (the draw moves stock to waste
  within one reservoir), and the committed draw fires only at a
  non-pure tip: pristine (empty waste) or offset (waste misaligned) —
  `tipEdge_draw_shape`;
* **waste exit** — the cycle strictly drops, and the popped card is
  the pair's pool-difference card (`poolMissCard`; uniqueness by
  the `WF` occurrence bookkeeping), so the card is a function of the
  pair — `wasteEntry`;
* **reveal** — a per-anchor hidden stack strictly dropped its head
  (the automatic flip); the seat is the pair's hidden-difference
  anchor `hiddenDropperAnchor`, and the revealed card is the
  class-visible head of that hidden stack — also pair functions;
* **vacate** — a hidden-free seat lost its bare non-king root; the
  seat is the pair's seat-difference anchor `rootFreedAnchor` —
  the arm-typing's fourth family riding the same positional label as
  the degenerate hidden-count-zero cell of the reveal family
  (`stackEvent`).

`labelOf (datumOf C) (datumOf D)` is the class-pair fingerprint — a
literal function of the pair classes, never of the member; the
determination rows unpack it at the member pair (the memberships
`hmem`/`cl` plus the lift's computation rule; `labelOf_pair` below is
definitional, with the state-grade read `CanonLabel c w` underneath),
so the anatomy of the anchor-form proofs runs unchanged with the
member in place of the padding tip.  The determinations tie each
commitment family to its fingerprint branch with the exact
card/anchor data, the disjointness cells keep the families exclusive,
and the assembled character (`pair_move_character`: the label
determines the committed move up to the recorded twin-landing merge)
closes the restated canonical property: two schemes over one class
pair commit the same *event*.

## The landing status of this drop (honest boundary)

This drop records the member-form flip (the design ledger above),
landed complete over its four coherent landings: the quotient datum
kernel, the scheme and label surface, the determination rows with the
disjointness cells, and the pair-move character.  What stands:

* **proved, green**: `leg_data` (the per-leg table: every witness leg
  conserves `cycleCount`, the pool, every per-anchor hidden list, and
  every seat root — the reveal and bare-nonking cells excluded as the
  hidden-descent/seat-physics commitments, the waste rows as the
  universal commitments, the under/bare-king shapes kept literally by
  the landed placement lemmas), `shuffleW_data`/`orbit_data` (the
  class-invariant lifts), the quotient datum kernel (`MacroDatums`
  with `MacroDatums.of`/`of_class`, the ungated class form
  `sameDatums_class`, and the lift `datumOf` with its definitional
  computation rule `datumOf_mk` — the same `sameDatums` machinery
  staged one section up, re-read as a quotient map's soundness; the
  staircase footing, landed as its own coherent staging ahead of the
  member-form restatement that stands on it), `TipEdge` (member-form:
  member + membership + commitment + class closure) with
  `TipEdge.landing_wf`, `tipEdge_exits_source` (the phase-progress
  cell — simpler than the anchor-form had: the class relation IS the
  returning journey, no padding composition),
  `tipEdge_ne_foundToTab` (the no-fourth-kind cell, part one:
  a committed move is never a foundation giveback — every legal WF
  `foundToTab` is reversible), and `tipEdge_draw_shape` (a draw edge
  starts non-pure: pristine or offset), the label surface
  (`MacroDatums.hiddenTotal`/`poolMiss`/`hiddenDropper`/`rootFreed`
  + `labelOf` + `labelOf_pair` — the definitional state-grade shadow
  — + `TipEdge.label` with `edge_label_unique` — definitional
  through the lift) and `CanonicalTip` (the premise-sugar saturation
  grade), and the full label-map kit (`nzRoot`, `EdgeLabel`,
  `WasteOf`, `RevealCellAt`, `VacateCellAt`, `poolMissCard`,
  `hiddenDropperAnchor`, `rootFreedAnchor`, `CanonLabel`).  The
  card-pinning census and the search reads ride the public packs
  (`Integrity`'s census-pack and search iffs, `State`/`Play`'s
  trivia/reader kits) — no farm-private recounting.
* **dissolved (removed, content definitional or re-homed)**:
  `CanonEdge` with `tip_wf`, `landing_wf`, `pad_data`, and `label`
  (the padding left the type; the member-tip's WF is the `hwf`
  field, the landing's is `TipEdge.landing_wf`, the datum-carry is
  the lift's business, the label reads the classes), and
  `canonLabel_orbit_indep` (the lift pays it once: `labelOf_pair` is
  `rfl`, and the label of the pair never reads the member).
* **proved, green** (the rows, re-landed): the four determination rows —
  `tipEdge_label_draw` (a draw-commit edge is draw-labeled — no datum
  changes, all three reads degenerate), the waste determination row
  `tipEdge_label_waste` (wasteEntry-labeled with exactly the popped
  card — the cycle drops and the pool-difference read pins the head,
  uniquely by the pool arithmetic), the reveal determination row
  `tipEdge_label_reveal` (stackEvent-labeled at the departing seat —
  the cycle conserved, the hidden total drops, the hidden-difference
  read is the seat), and the vacate determination row
  `tipEdge_label_vacate` (stackEvent-labeled at the freed seat — both
  tests die at the conserved counts and the seat-difference read is
  the seat) — through the one-line lens `label_read` (the membership
  transports plus `labelOf_pair`; the datum-carry the old `pad_data`
  performed rides it) with the anatomy otherwise unchanged (the faces
  of the moves read at the member exactly as they were read at the
  padding tip), and the four disjointness cells
  (`tipEdge_label_draw_ne`/`_waste_ne`/`_reveal_ne`/`_vacate_ne`: the
  label families stay exclusive on the commit — draw never
  card-labeled, waste never draw/stack-labeled, and the stack family —
  reveal or vacate, the recorded merge — never draw/waste-labeled).
* **proved, green (the close)**: the pair-move character
  (`pair_move_character`: the label determines the committed move up
  to the recorded twin-landing merge — the determination rows'
  converse, riding the memberships and the rows, the tableau seats
  read at the member; together with `edge_label_unique` it closes the
  restated canonical property: two schemes over one class pair commit
  the same *event*) and its switch form
  (`pair_move_character_switch`: the match the compiler exhaustively
  checks over the tripartite alphabet, the consumption form the count
  program cites).
* **milestone status**: COMPLETE in this module — the member-form
  restatement is done, the edge-labeling theorem's full arc landed at
  the member grade (the quotient datum kernel, the journey-invariant
  datums, the `TipEdge` normal form, the definitional
  pair-functionality of the read, the four determination rows, the
  family disjointness cells, and the pair-move character).  The
  downstream work (§3.1's count program: the transport bridge and the
  per-arm enumeration) consumes this module from outside and is not
  part of it — with ONE carve-out now opened as this module's own
  chapter below: the draw successor (the successor discipline's
  first small step, `b4f32e4`'s recon recorded above the proofs),
  landed COMPLETE over its three coherent landings: the interface
  recon (the fragment boundary, the commutation-transport route,
  the refused phase-collapse), the core at the ideal grade
  (`draw_landings_sameOrbit`, `draw_successor_unique` — the
  commutation transport through the field-local draw, ungated,
  premises derived never assumed), and the constructive envelope
  (`sameOrbit_cycleCount`, the junk-safe `drawNext`, the lift
  `drawNextQ` with `drawNextQ_mk`, the enumeration
  `tipEdge_draw_target`) — all green, sorry-free, audited
  `[propext, Quot.sound]`.  The `≤ 2`-per-label umbrella itself
  stays open by design: this chapter is the draw label's one
  share.

## The vacate cell is a genuine fourth signature — the honest boundary

The three-cause exhaustiveness ("reveals some card, or reduces some
waste, or draws from non-pure") is FALSE without the vacate cell: a
committed `tabToTab`/`tabToFound` of a dealt bare non-king off its
hidden-free anchor changes NO hidden count, pops no waste, draws
nothing — the seat-physics rows of the landed oracle.  The label
alphabet nevertheless stays TRIPARTITE (draw | wasteEntry c |
stackEvent a) per the recorded design: the vacate rides the reveal's
positional family as its degenerate no-reveal case, the pair itself
separating the two sub-cells by the hidden measure.

## Axiom discipline

`[propext, Quot.sound]` at worst; zero `Classical.choice`, zero
`sorry`, no `native_decide`; the only case splits go through
decidable equality and Bool dichotomies, and the card-uniqueness
bookkeeping is a self-contained counting kit.  Per-declaration
`#print axioms` audit at file bottom.
-/

/-! ## Step inversions

The five move-constructor inversions ride the public rows of
`Orig.Irreversible` since the dedup-collapse wave; the two waste
rows keep a one-step head-eq derivation at their sites (the public
rows name the waste head existentially, the sites need it `c`). -/

/-! ## Private kit: list, pile, and search helpers -/

/-! ## Private kit: list, pile, and search helpers -/

/- The card census cross-zone facts ride the public Integrity pack
(`mem_stock_unique`, `mem_waste_unique`, `mem_pile_unique`) and the
search soundness/completeness ride the public State kit
(`firstWhere_find`, `firstWhere_sound`, `firstWhere_none_complete`) —
no farm-private recounting. -/

/-- The bare-pile lemma: a run removal over an empty face-up remainder
with no hidden cards leaves the bare empty pile. -/
private theorem afterRunRemoved_bare_empty {p : Pile} (h : p.hidden = []) :
    Pile.afterRunRemoved p [] = ⟨[], []⟩ := by
  rcases p with ⟨hd, fq⟩
  cases hd with
  | nil => rfl
  | cons x xs => exact absurd h (by simp)

/-- A pile holding nothing has no top, so the top search cannot pin
it. -/
private theorem pileOfTop_ne_of_bare {st : State} {a : Anchor}
    (hemp : (st.piles a).hidden = [] ∧ (st.piles a).faceUp = [])
    (z : Card) : st.pileOfTop z ≠ some a := by
  intro hcon
  obtain ⟨hfe, -⟩ := pileOfTop_top hcon
  rw [hemp.2] at hfe
  exact absurd hfe (by simp)

private theorem head_eq_of_below_nil {c x : Card} {t : List Card}
    (h : below c (x :: t) = []) : x = c := by
  rw [below_cons] at h
  by_cases hx : x = c
  · exact hx
  · rw [ite_eq_right hx] at h
    exact absurd h (by simp)

/-- Below-nil at a nonempty run means the run is headed at `c`, so
`fromCard` is the whole run. -/
private theorem faceUp_eq_of_below {c x : Card} {t : List Card}
    (hbelow : below c (x :: t) = []) : fromCard c (x :: t) = x :: t := by
  have hx : x = c := head_eq_of_below_nil hbelow
  subst hx
  show (if x = x then (x :: t) else fromCard x t) = x :: t
  rw [ite_eq_left rfl]

/-- The chop keeps the head card of a nonempty face-up run. -/
private theorem faceUp_head_of_chop : ∀ {l : List Card} {g : Card} {t : List Card},
    chop l = g :: t → ∃ t', l = g :: t' := by
  intro l
  induction l with
  | nil => intro g t h; exact absurd h (by simp [chop])
  | cons x xs ih =>
      intro g t h
      cases xs with
      | nil =>
          have hnone : chop (x :: ([] : List Card)) = ([] : List Card) := rfl
          rw [hnone] at h
          exact absurd h (by simp)
      | cons y ys =>
          have hch : chop (x :: y :: ys) = x :: chop (y :: ys) := rfl
          rw [hch] at h
          injection h with hxg _
          exact ⟨y :: ys, by rw [hxg]⟩

/- The search reads ride the public State kit (`firstWhere_find`,
`firstWhere_sound`, `firstWhere_congr` in Twin) — consumed at the
determination call sites.  The none-completeness below is the ONE
search reader without a public home (Canonical keeps a private copy
over the card universe; dedup at merge). -/

/-- When every element fails the predicate, the search is `none`
(farm-private; Canonical's copy is specialised to the card universe —
dedup at merge). -/
private theorem firstWhere_none_of_forall {α : Type} (p : α → Bool) :
    ∀ {l : List α}, (∀ x ∈ l, p x = false) → firstWhere p l = none := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons z t ih =>
      intro h
      rw [firstWhere, h z (List.mem_cons.2 (Or.inl rfl))]
      exact ih fun x hx => h x (List.mem_cons.2 (Or.inr hx))

/-! ## The label alphabet and the seat-root datum -/

/-- The bare non-king root at a seat: the bottom face-up card when it
is not a king.  Witness journeys never move it (a root departure is
a commitment: the seat-physics rows for non-kings, the hidden-descent
rows for reveals), so it is a macro-class invariant per anchor — the
datum the vacate cell reads. -/
def nzRoot (st : State) (a : Anchor) : Option Card :=
  match (st.piles a).faceUp with
  | [] => none
  | g :: _ => if g.rank = Rank.king then none else some g

/-- The label of a directly-adjacent class pair — the recorded
tripartite alphabet (§3.1): the draw | the waste-card entry
(card-labeled: the single-zone waste has no position to name) | the
tableau event at a position (reveal or the degenerate vacate,
position-labeled: the twin conjugation permutes card identities only,
fixing the positions, so positional labels are twin-blind by
construction). -/
inductive EdgeLabel : Type where
  | draw
  | wasteEntry (c : Card)
  | stackEvent (a : Anchor)

/-- The waste family: the move hands card `c` out of the waste. -/
def WasteOf (c : Card) (m : Move) : Prop :=
  m = Move.wasteToFound c ∨ ∃ b, m = Move.wasteToTab c b

/-- The reveal cell of a committed stack move, located at the pile it
departs: the run leaving the pile carries the pile's whole face-up
content while hidden cards remain beneath — the automatic flip
fires. -/
inductive RevealCellAt : State → Anchor → Move → Prop
  | tabToFound {u : State} {a : Anchor} {c : Card}
      (hloc : u.pileOfTop c = some a)
      (hpre : chop (u.piles a).faceUp = [])
      (hhne : (u.piles a).hidden ≠ []) :
      RevealCellAt u a (Move.tabToFound c)
  | tabToTab {u : State} {a : Anchor} {c : Card} {b : Base}
      (hloc : u.pileHolding c = some a)
      (hpre : below c (u.piles a).faceUp = [])
      (hhne : (u.piles a).hidden ≠ []) :
      RevealCellAt u a (Move.tabToTab c b)

/-- The vacate cell: the departure empties a hidden-free seat whose
bare root is a non-king — the seat-physics door (the arm-typing's
fourth family; the seat frees and never receives a non-king back). -/
inductive VacateCellAt : State → Anchor → Move → Prop
  | tabToFound {u : State} {a : Anchor} {c : Card}
      (hloc : u.pileOfTop c = some a)
      (hpre : chop (u.piles a).faceUp = [])
      (hhd : (u.piles a).hidden = [])
      (hnk : c.rank ≠ Rank.king) :
      VacateCellAt u a (Move.tabToFound c)
  | tabToTab {u : State} {a : Anchor} {c : Card} {b : Base}
      (hloc : u.pileHolding c = some a)
      (hpre : below c (u.piles a).faceUp = [])
      (hhd : (u.piles a).hidden = [])
      (hnk : c.rank ≠ Rank.king) :
      VacateCellAt u a (Move.tabToTab c b)

private theorem nzRoot_nil {st : State} {a : Anchor}
    (h : (st.piles a).faceUp = []) : nzRoot st a = none := by
  show (match (st.piles a).faceUp with
    | [] => none
    | g :: _ => if g.rank = Rank.king then none else some g) = none
  rw [h]

private theorem nzRoot_head {st : State} {a : Anchor} {g : Card} {t : List Card}
    (h : (st.piles a).faceUp = g :: t) :
    nzRoot st a = if g.rank = Rank.king then none else some g := by
  show (match (st.piles a).faceUp with
    | [] => none
    | g' :: _ => if g'.rank = Rank.king then none else some g') = _
  rw [h]

/-- Equal piles give equal roots. -/
private theorem nzRoot_congr_pile {x y : State} {a : Anchor}
    (h : y.piles a = x.piles a) : nzRoot y a = nzRoot x a := by
  show (match (y.piles a).faceUp with
    | [] => none
    | g :: _ => if g.rank = Rank.king then none else some g) =
       (match (x.piles a).faceUp with
         | [] => none
         | g :: _ => if g.rank = Rank.king then none else some g)
  rw [← h]

/-- Equal face-up contents give equal roots (the form the placement
cases consume). -/
private theorem nzRoot_congr_faceUp {x y : State} {a : Anchor}
    (h : (y.piles a).faceUp = (x.piles a).faceUp) : nzRoot y a = nzRoot x a := by
  show (match (y.piles a).faceUp with
    | [] => none
    | g :: _ => if g.rank = Rank.king then none else some g) =
       (match (x.piles a).faceUp with
         | [] => none
         | g :: _ => if g.rank = Rank.king then none else some g)
  rw [h]

/-- The run landing on an empty seat, per anchor: target piles. -/
private theorem putRun_inl_landing {st : State} {run : List Card} {k : Anchor} :
    (st.putRun run (Sum.inl k)).piles k = ⟨[], run⟩ := by
  show (if k = k then ⟨[], run⟩ else st.piles k) = ⟨[], run⟩
  rw [ite_eq_left rfl]

/-- The run landing on an empty seat, per anchor: untouched piles. -/
private theorem putRun_inl_piles {st : State} {run : List Card} {k a' : Anchor}
    (h : a' ≠ k) : (st.putRun run (Sum.inl k)).piles a' = st.piles a' := by
  show (if a' = k then ⟨[], run⟩ else st.piles a') = st.piles a'
  exact ite_eq_right h

/-- The run landing on a located pile: the landing pile, face-up
extended. -/
private theorem putRun_inr_landing {st : State} {run : List Card} {z : Card} {k : Anchor}
    (hz : st.pileOfTop z = some k) :
    (st.putRun run (Sum.inr z)).piles k
      = { st.piles k with faceUp := (st.piles k).faceUp ++ run } := by
  show (match st.pileOfTop z with
    | some k' => st.setPile k' { st.piles k' with faceUp := (st.piles k').faceUp ++ run }
    | none => st).piles k = { st.piles k with faceUp := (st.piles k).faceUp ++ run }
  rw [hz]
  show (if k = k then { st.piles k with faceUp := (st.piles k).faceUp ++ run }
      else st.piles k) = { st.piles k with faceUp := (st.piles k).faceUp ++ run }
  rw [ite_eq_left rfl]

/-- A run landing on a located pile leaves the other piles alone. -/
private theorem putRun_inr_piles_ne {st : State} {run : List Card} {z : Card} {k a' : Anchor}
    (hz : st.pileOfTop z = some k) (h : a' ≠ k) :
    (st.putRun run (Sum.inr z)).piles a' = st.piles a' := by
  show (match st.pileOfTop z with
    | some k' => st.setPile k' { st.piles k' with faceUp := (st.piles k').faceUp ++ run }
    | none => st).piles a' = st.piles a'
  rw [hz]
  show (if a' = k then { st.piles k with faceUp := (st.piles k).faceUp ++ run }
      else st.piles a') = st.piles a'
  exact ite_eq_right h

/-- The card landing on an empty seat, per anchor: target pile. -/
private theorem putCard_inl_landing {st : State} {c : Card} {k : Anchor} :
    (st.putCard c (Sum.inl k)).piles k = ⟨[], [c]⟩ := by
  show (if k = k then (⟨[], [c]⟩ : Pile) else st.piles k) = ⟨[], [c]⟩
  rw [ite_eq_left rfl]

/-- The card landing on an empty seat, per anchor: untouched piles. -/
private theorem putCard_inl_piles {st : State} {c : Card} {k a' : Anchor}
    (h : a' ≠ k) : (st.putCard c (Sum.inl k)).piles a' = st.piles a' := by
  show (if a' = k then (⟨[], [c]⟩ : Pile) else st.piles a') = st.piles a'
  exact ite_eq_right h

/-- A card landing with no search hit changes nothing. -/
private theorem putCard_inr_none {st : State} {c : Card} {z : Card}
    (hz : st.pileOfTop z = none) (a' : Anchor) :
    (st.putCard c (Sum.inr z)).piles a' = st.piles a' := by
  show (match st.pileOfTop z with
    | some k => st.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }
    | none => st).piles a' = st.piles a'
  rw [hz]

/-- The card landing on a located pile: the landing pile, face-up
extended. -/
private theorem putCard_inr_landing {st : State} {c : Card} {z : Card} {k : Anchor}
    (hz : st.pileOfTop z = some k) :
    (st.putCard c (Sum.inr z)).piles k
      = { st.piles k with faceUp := (st.piles k).faceUp ++ [c] } := by
  show (match st.pileOfTop z with
    | some k' => st.setPile k' { st.piles k' with faceUp := (st.piles k').faceUp ++ [c] }
    | none => st).piles k = { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }
  rw [hz]
  show (if k = k then { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }
      else st.piles k) = { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }
  rw [ite_eq_left rfl]

/-- A card landing on a located pile leaves the other piles alone. -/
private theorem putCard_inr_piles_ne {st : State} {c : Card} {z : Card} {k a' : Anchor}
    (hz : st.pileOfTop z = some k) (h : a' ≠ k) :
    (st.putCard c (Sum.inr z)).piles a' = st.piles a' := by
  show (match st.pileOfTop z with
    | some k' => st.setPile k' { st.piles k' with faceUp := (st.piles k').faceUp ++ [c] }
    | none => st).piles a' = st.piles a'
  rw [hz]
  show (if a' = k then { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }
      else st.piles a') = st.piles a'
  exact ite_eq_right h

/-! ## The journey data: what a witness leg can change -/

/-- The deal cut reassembles (citing the public take/drop reader). -/
private theorem dealUpTo_append_copy (k : Nat) : ∀ (l : List Card),
    (State.dealUpTo k l).1 ++ (State.dealUpTo k l).2 = l := by
  intro l
  rw [dealUpTo_eq_take_drop k l]
  show l.take k ++ l.drop k = l
  exact List.take_append_drop k l

/-- Dealing from a nonempty stock keeps the pool: the split reverses
back onto itself. -/
private theorem dealStock_pool {r y : State} (h : State.dealStock r = some y) :
    drawPool y = drawPool r := by
  cases hs : r.stock with
  | nil =>
      rw [show State.dealStock r = none from by simp only [State.dealStock, hs]] at h
      exact absurd h (by simp)
  | cons x t =>
      rw [show State.dealStock r = some
          { r with stock := (State.dealUpTo r.drawStep (x :: t)).2,
                   waste := (State.dealUpTo r.drawStep (x :: t)).1.reverse ++ r.waste } from by
            simp only [State.dealStock, hs]] at h
      injection h with hEq
      subst hEq
      have hsplit : (State.dealUpTo r.drawStep (x :: t)).2.reverse ++
          (State.dealUpTo r.drawStep (x :: t)).1.reverse = (x :: t).reverse := by
        rw [show (x :: t).reverse =
              ((State.dealUpTo r.drawStep (x :: t)).1 ++
                (State.dealUpTo r.drawStep (x :: t)).2).reverse from by
              rw [dealUpTo_append_copy]]
        exact List.reverse_append.symm
      show (State.dealUpTo r.drawStep (x :: t)).2.reverse ++
            ((State.dealUpTo r.drawStep (x :: t)).1.reverse ++ r.waste)
              = r.stock.reverse ++ r.waste
      rw [hs, ← List.append_assoc, hsplit]

/-- A successful draw keeps the draw pool exactly (stock to waste
within one reservoir). -/
private theorem stepDraw_pool {x y : State} (h : x.stepDraw = some y) :
    drawPool y = drawPool x := by
  have hd : State.dealStock x.recycle = some y := h
  rw [dealStock_pool hd, recycle_pool]

/-- Equal draw zones give equal pools. -/
private theorem pool_congr {x y : State} (hst : y.stock = x.stock)
    (hwa : y.waste = x.waste) : drawPool y = drawPool x := by
  show y.stock.reverse ++ y.waste = x.stock.reverse ++ x.waste
  rw [hst, hwa]

/-- A waste-consuming move is no witness leg: it is a commitment at
every position (the universal rows), so it can never appear inside a
witness shuffle. -/
private theorem leg_ne_waste {x : State} {m : Move} (hw : reversibleAtW x m) :
    ∀ c b, m ≠ Move.wasteToFound c ∧ m ≠ Move.wasteToTab c b := by
  have hnr : ¬ irreversibleAt x m := reversibleAt_of_W hw
  intro c b
  constructor
  · intro hcon
    exact hnr (by rw [hcon]; exact irreversibleAt_wasteToFound x c)
  · intro hcon
    exact hnr (by rw [hcon]; exact irreversibleAt_wasteToTab x c b)

/-- **The per-leg data table.**  A witness-leg move conserves the
cycle count, the pool, every per-anchor hidden list, and every bare
non-king root.  The waste rows are impossible legs (universal
commitments); the reveal cells and the bare-nonking cells are
commitments (the hidden-descent, resp. seat-physics rows), also
impossible legs; every remaining shape keeps the data literally. -/
private theorem leg_data {x y : State} {m : Move}
    (hw : reversibleAtW x m) (hstep : State.step x m = some y) :
    cycleCount y = cycleCount x ∧ drawPool y = drawPool x ∧
    (∀ a, (y.piles a).hidden = (x.piles a).hidden) ∧
    (∀ a, nzRoot y a = nzRoot x a) := by
  cases m with
  | draw =>
      have hd : x.stepDraw = some y := hstep
      refine ⟨stepDraw_cycle hd, stepDraw_pool hd, ?_, ?_⟩
      · have hp : y.piles = x.piles := stepDraw_piles hd
        intro a; rw [hp]
      · intro a
        exact nzRoot_congr_pile (congrFun (stepDraw_piles hd) a)
  | wasteToFound c => exact absurd (irreversibleAt_wasteToFound x c) (reversibleAt_of_W hw)
  | wasteToTab c b => exact absurd (irreversibleAt_wasteToTab x c b) (reversibleAt_of_W hw)
  | tabToFound c =>
      obtain ⟨-, a, hpa, hs⟩ := step_tabToFound_inv hstep
      have hzone : y.stock = x.stock ∧ y.waste = x.waste := by
        rw [hs]; exact ⟨rfl, rfl⟩
      have hp (a' : Anchor) : y.piles a' =
          if a' = a then Pile.afterRunRemoved (x.piles a) (chop (x.piles a).faceUp)
          else x.piles a' := by rw [hs]
      refine ⟨cycleCount_eq_of_stock_waste hzone.1 hzone.2,
        pool_congr hzone.1 hzone.2, ?_⟩
      cases hchop : chop (x.piles a).faceUp with
      | nil =>
          cases hhid : (x.piles a).hidden with
          | nil =>
              have hArb : Pile.afterRunRemoved (x.piles a) [] = ⟨[], []⟩ :=
                afterRunRemoved_bare_empty hhid
              by_cases hk : c.rank = Rank.king
              · -- the bare-king lift: a legal leg shape; everything kept
                have hface : (x.piles a).faceUp = [c] := by
                  obtain ⟨-, hlast⟩ := pileOfTop_top hpa
                  rw [lastOf_chop hlast, hchop, List.nil_append]
                have hy : (y.piles a).faceUp = [] := by
                  rw [hp a, ite_eq_left rfl, hchop, hArb]
                refine ⟨?_, ?_⟩
                · intro a'
                  rw [hp a']
                  by_cases hae : a' = a
                  · subst hae
                    rw [ite_eq_left rfl, hchop, hArb]
                    exact hhid.symm
                  · rw [ite_eq_right hae]
                · intro a'
                  by_cases hae : a' = a
                  · subst hae
                    rw [nzRoot_nil hy, nzRoot_head hface, ite_eq_left hk]
                  · exact nzRoot_congr_pile (by rw [hp a', ite_eq_right hae])
              · -- the bare-nonking lift: a commitment, not a leg
                exact absurd
                  (tabToFound_irreversible_of_bare_nonking hstep hpa hchop hhid hk)
                  (reversibleAt_of_W hw)
          | cons g gs =>
              -- the reveal cell: a commitment, not a leg
              exact absurd
                (irr_of_desc hiddenTotal (fun s m s' hst => hiddenTotal_step hst) hstep
                  (by
                    have hd := hiddenTotal_step_tabToFound_reveal hstep hpa hchop
                      (by rw [hhid]; simp)
                    omega))
                (reversibleAt_of_W hw)
      | cons z' preT =>
          have hArb' : Pile.afterRunRemoved (x.piles a) (z' :: preT) =
              { x.piles a with faceUp := z' :: preT } := rfl
          obtain ⟨t', hfa⟩ := faceUp_head_of_chop hchop
          have hyF : (y.piles a).faceUp = z' :: preT := by
            rw [hp a, ite_eq_left rfl, hchop, hArb']
          have hxF : (x.piles a).faceUp = z' :: t' := hfa
          refine ⟨?_, ?_⟩
          · intro a'
            rw [hp a']
            by_cases hae : a' = a
            · subst hae
              rw [ite_eq_left rfl, hchop, hArb']
            · rw [ite_eq_right hae]
          · intro a'
            by_cases hae : a' = a
            · subst hae
              rw [nzRoot_head hyF, nzRoot_head hxF]
            · exact nzRoot_congr_pile (by rw [hp a', ite_eq_right hae])
  | foundToTab c b =>
      obtain ⟨-, -, hceq, hcp, hs⟩ := step_foundToTab_inv hstep
      have hzone : y.stock = x.stock ∧ y.waste = x.waste := by
        rw [hs]; exact ⟨putCard_stock _ _ _, putCard_waste _ _ _⟩
      have hcpS : (x.setFound c.suit (chop (x.found c.suit))).canPlace c b = true := hcp
      refine ⟨cycleCount_eq_of_stock_waste hzone.1 hzone.2, pool_congr hzone.1 hzone.2, ?_⟩
      refine ⟨fun a' => by rw [hs]; exact putCard_hidden_eq hcpS a', ?_⟩
      intro a'
      cases b with
      | inl k =>
          obtain ⟨hemp, hkng⟩ := canPlace_inl hcp
          obtain ⟨-, hfeK⟩ := (Pile.isEmpty_eq _).mp hemp
          by_cases hae : a' = k
          · subst hae
            have hyF : (y.piles a').faceUp = [c] := by rw [hs, putCard_inl_landing]
            rw [nzRoot_head hyF, ite_eq_left hkng, nzRoot_nil hfeK]
          · have hyF : (y.piles a').faceUp = (x.piles a').faceUp := by
              rw [hs, putCard_inl_piles hae]
              rfl
            exact nzRoot_congr_faceUp hyF
      | inr z =>
          obtain ⟨k, hz, -⟩ := canPlace_inr hcp
          have hzs : (x.setFound c.suit (chop (x.found c.suit))).pileOfTop z = some k := hz
          by_cases hae : a' = k
          · subst hae
            have hyF : (y.piles a').faceUp = (x.piles a').faceUp ++ [c] := by
              rw [hs, putCard_inr_landing hzs]
              rfl
            obtain ⟨hfxne, -⟩ := pileOfTop_top hz
            have hfxneX : (x.piles a').faceUp ≠ [] := hfxne
            cases hfx : (x.piles a').faceUp with
            | nil => rw [hfx] at hfxneX; exact absurd hfxneX (by simp)
            | cons g gs =>
              have hyC : (y.piles a').faceUp = g :: (gs ++ [c]) := by
                rw [hyF, hfx, List.cons_append]
              rw [nzRoot_head hyC, nzRoot_head hfx]
          · have hyF : (y.piles a').faceUp = (x.piles a').faceUp := by
              rw [hs, putCard_inr_piles_ne hzs hae]
              rfl
            exact nzRoot_congr_faceUp hyF
  | tabToTab c b =>
      obtain ⟨a, hh, hcp, hfr, hs⟩ := step_tabToTab_inv hstep
      have hzone : y.stock = x.stock ∧ y.waste = x.waste := by
        rw [hs]; exact ⟨putRun_stock _ _ _, putRun_waste _ _ _⟩
      have hmem : c ∈ (x.piles a).faceUp := pileHolding_mem hh
      have hrP (a' : Anchor) : (x.setPile a
          (Pile.afterRunRemoved (x.piles a) (below c (x.piles a).faceUp))).piles a'
          = if a' = a then Pile.afterRunRemoved (x.piles a) (below c (x.piles a).faceUp)
            else x.piles a' := by
        by_cases ha : a' = a
        · rw [ha, ite_eq_left rfl]
          exact setPile_piles_self
        · rw [ite_eq_right ha]
          exact setPile_piles_ne ha
      refine ⟨cycleCount_eq_of_stock_waste hzone.1 hzone.2, pool_congr hzone.1 hzone.2, ?_⟩
      cases hbelow : below c (x.piles a).faceUp with
      | nil =>
          cases hhid : (x.piles a).hidden with
          | nil =>
              by_cases hk : c.rank = Rank.king
              · -- the bare-king relocation: a legal leg shape; everything kept
                have hArb2 : Pile.afterRunRemoved (x.piles a) [] = ⟨[], []⟩ :=
                  afterRunRemoved_bare_empty hhid
                cases hfx0 : (x.piles a).faceUp with
                | nil => exact absurd hmem (by rw [hfx0]; simp)
                | cons g t =>
                    have hg : c = g := (head_eq_of_below_nil
                      (by rw [← hfx0]; exact hbelow)).symm
                    subst hg
                    have hrA : (x.setPile a
                        (Pile.afterRunRemoved (x.piles a)
                          (below c (x.piles a).faceUp))).piles a
                        = ⟨[], ([] : List Card)⟩ := by
                      rw [hrP a, ite_eq_left rfl, hbelow, hArb2]
                    have hrr : (fromCard c (x.piles a).faceUp) = c :: t := by
                      rw [hfx0]
                      exact faceUp_eq_of_below (by rw [← hfx0]; exact hbelow)
                    refine ⟨fun a' => by
                      rw [hs]
                      cases b with
                      | inl k =>
                          obtain ⟨hemp, -⟩ := canPlace_inl hcp
                          obtain ⟨hhdK, -⟩ := (Pile.isEmpty_eq _).mp hemp
                          by_cases hk' : a' = k
                          · rw [hk']
                            rw [putRun_inl_landing]
                            show ([] : List Card) = (x.piles k).hidden
                            rw [← hhdK]
                          · rw [putRun_inl_piles hk']
                            by_cases ha : a' = a
                            · rw [hrP a', ite_eq_left ha, hbelow, hArb2, ha]
                              exact hhid.symm
                            · rw [hrP a', ite_eq_right ha]
                      | inr z =>
                          cases hz : (x.setPile a
                              (Pile.afterRunRemoved (x.piles a)
                                (below c (x.piles a).faceUp))).pileOfTop z with
                          | none =>
                              rw [putRun_inr_none_piles hz]
                              by_cases ha : a' = a
                              · rw [hrP a', ite_eq_left ha, hbelow, hArb2, ha]
                                exact hhid.symm
                              · rw [hrP a', ite_eq_right ha]
                          | some k =>
                              by_cases hk' : a' = k
                              · rw [hk']
                                rw [putRun_inr_landing hz]
                                show ((x.setPile a
                                    (Pile.afterRunRemoved (x.piles a)
                                      (below c (x.piles a).faceUp))).piles k).hidden
                                    = (x.piles k).hidden
                                by_cases hka : k = a
                                · rw [hka]
                                  rw [hrA]
                                  exact hhid.symm
                                · rw [hrP k, ite_eq_right hka]
                              · rw [putRun_inr_piles_ne hz hk']
                                by_cases ha : a' = a
                                · rw [hrP a', ite_eq_left ha, hbelow, hArb2, ha]
                                  exact hhid.symm
                                · rw [hrP a', ite_eq_right ha], ?_⟩
                    intro a'
                    rw [hs]
                    cases b with
                    | inl k =>
                        obtain ⟨hemp, hkng⟩ := canPlace_inl hcp
                        obtain ⟨-, hfeK⟩ := (Pile.isEmpty_eq _).mp hemp
                        by_cases hk' : a' = k
                        · rw [hk']
                          have hyF : (((x.setPile a
                              (Pile.afterRunRemoved (x.piles a)
                                (below c (x.piles a).faceUp))).putRun
                              (fromCard c (x.piles a).faceUp) (Sum.inl k)).piles k).faceUp
                              = c :: t := by rw [putRun_inl_landing]; exact hrr
                          rw [nzRoot_head hyF, ite_eq_left hkng, nzRoot_nil hfeK]
                        · by_cases ha : a' = a
                          · have hyF : (((x.setPile a
                              (Pile.afterRunRemoved (x.piles a)
                                (below c (x.piles a).faceUp))).putRun
                              (fromCard c (x.piles a).faceUp) (Sum.inl k)).piles a').faceUp
                              = [] := by
                              rw [putRun_inl_piles hk', hrP a', ite_eq_left ha,
                                hbelow, hArb2]
                            have hxA : (x.piles a').faceUp = c :: t := by
                              rw [ha]; exact hfx0
                            rw [nzRoot_nil hyF, nzRoot_head hxA, ite_eq_left hk]
                          · exact nzRoot_congr_pile
                              ((putRun_inl_piles hk').trans
                                ((hrP a').trans (ite_eq_right ha)))
                    | inr z =>
                        cases hz : (x.setPile a
                            (Pile.afterRunRemoved (x.piles a)
                              (below c (x.piles a).faceUp))).pileOfTop z with
                        | none =>
                            by_cases ha : a' = a
                            · have hyF : (((x.setPile a
                                (Pile.afterRunRemoved (x.piles a)
                                  (below c (x.piles a).faceUp))).putRun
                                (fromCard c (x.piles a).faceUp) (Sum.inr z)).piles a').faceUp
                                = [] := by
                                rw [putRun_inr_none_piles hz, hrP a', ite_eq_left ha,
                                  hbelow, hArb2]
                              have hxA : (x.piles a').faceUp = c :: t := by
                                rw [ha]; exact hfx0
                              rw [nzRoot_nil hyF, nzRoot_head hxA, ite_eq_left hk]
                            · exact nzRoot_congr_pile
                                ((putRun_inr_none_piles hz a').trans
                                  ((hrP a').trans (ite_eq_right ha)))
                        | some k =>
                            have hka : k ≠ a := by
                              intro hcon
                              subst hcon
                              exact absurd hz (pileOfTop_ne_of_bare
                                (by rw [hrA]; exact ⟨rfl, rfl⟩) z)
                            have hsPk : (x.setPile a
                                (Pile.afterRunRemoved (x.piles a)
                                  (below c (x.piles a).faceUp))).piles k
                                = x.piles k := by rw [hrP k, ite_eq_right hka]
                            have hsne : (x.piles k).faceUp ≠ [] := by
                              rw [← hsPk]
                              exact (pileOfTop_top hz).1
                            cases hfxK : (x.piles k).faceUp with
                            | nil => rw [hfxK] at hsne; exact absurd hsne (by simp)
                            | cons g gs =>
                              by_cases hk' : a' = k
                              · rw [hk']
                                have hyF : (((x.setPile a
                                    (Pile.afterRunRemoved (x.piles a)
                                      (below c (x.piles a).faceUp))).putRun
                                    (fromCard c (x.piles a).faceUp) (Sum.inr z)).piles k).faceUp
                                    = g :: (gs ++ fromCard c (x.piles a).faceUp) := by
                                  rw [putRun_inr_landing hz, hsPk, hfxK, List.cons_append]
                                rw [nzRoot_head hyF, nzRoot_head hfxK]
                              · by_cases ha : a' = a
                                · have hyF : (((x.setPile a
                                    (Pile.afterRunRemoved (x.piles a)
                                      (below c (x.piles a).faceUp))).putRun
                                    (fromCard c (x.piles a).faceUp) (Sum.inr z)).piles a').faceUp
                                    = [] := by
                                    rw [putRun_inr_piles_ne hz hk', hrP a',
                                      ite_eq_left ha, hbelow, hArb2]
                                  have hxA : (x.piles a').faceUp = c :: t := by
                                    rw [ha]; exact hfx0
                                  rw [nzRoot_nil hyF, nzRoot_head hxA, ite_eq_left hk]
                                · exact nzRoot_congr_pile
                                    ((putRun_inr_piles_ne hz hk').trans
                                      ((hrP a').trans (ite_eq_right ha)))
              · -- the bare-nonking relocation: a commitment, not a leg
                exact absurd
                  (tabToTab_irreversible_of_bare_nonking hstep hh hbelow hhid hfr hk)
                  (reversibleAt_of_W hw)
          | cons g gs =>
              -- the reveal cell: a commitment, not a leg
              exact absurd
                (irr_of_desc hiddenTotal (fun s m s' hst => hiddenTotal_step hst) hstep
                  (by
                    have hd := hiddenTotal_step_tabToTab_reveal hstep hh hbelow
                      (by rw [hhid]; simp)
                    omega))
                (reversibleAt_of_W hw)
      | cons z₀ pre' =>
          -- the under relocation: a face-up remainder stays; everything is kept
          have hArb3 : Pile.afterRunRemoved (x.piles a) (z₀ :: pre')
              = { x.piles a with faceUp := z₀ :: pre' } := rfl
          cases hfx0 : (x.piles a).faceUp with
          | nil => exact absurd hmem (by rw [hfx0]; simp)
          | cons f r =>
              have hfz : f = z₀ := by
                have hbc : below c (f :: r) = z₀ :: pre' := by rw [← hfx0]; exact hbelow
                rw [below_cons, ite_eq_right (fun hfc =>
                  by rw [hfc, ite_eq_left rfl] at hbc; exact absurd hbc (by simp))] at hbc
                injection hbc with hfz' _
              have hhead : ((x.setPile a
                  (Pile.afterRunRemoved (x.piles a)
                    (below c (x.piles a).faceUp))).piles a).faceUp = z₀ :: pre' := by
                rw [hrP a, ite_eq_left rfl, hbelow, hArb3]
              have hhA : ((x.setPile a
                  (Pile.afterRunRemoved (x.piles a)
                    (below c (x.piles a).faceUp))).piles a).hidden
                  = (x.piles a).hidden := by
                rw [hrP a, ite_eq_left rfl, hbelow, hArb3]
              have hrrR : ∃ rr, fromCard c (x.piles a).faceUp = c :: rr :=
                fromCard_eq_head_of_mem hmem
              refine ⟨fun a' => by
                rw [hs]
                cases b with
                | inl k =>
                    obtain ⟨hemp, -⟩ := canPlace_inl hcp
                    obtain ⟨hhdK, -⟩ := (Pile.isEmpty_eq _).mp hemp
                    by_cases hk' : a' = k
                    · rw [hk']
                      rw [putRun_inl_landing]
                      show ([] : List Card) = (x.piles k).hidden
                      rw [← hhdK]
                    · rw [putRun_inl_piles hk']
                      by_cases ha : a' = a
                      · rw [hrP a', ite_eq_left ha, hbelow, hArb3, ha]
                      · rw [hrP a', ite_eq_right ha]
                | inr z =>
                    cases hz : (x.setPile a
                        (Pile.afterRunRemoved (x.piles a)
                          (below c (x.piles a).faceUp))).pileOfTop z with
                    | none =>
                        rw [putRun_inr_none_piles hz]
                        by_cases ha : a' = a
                        · rw [hrP a', ite_eq_left ha, hbelow, hArb3, ha]
                        · rw [hrP a', ite_eq_right ha]
                    | some k =>
                        by_cases hk' : a' = k
                        · rw [hk']
                          rw [putRun_inr_landing hz]
                          show ((x.setPile a
                              (Pile.afterRunRemoved (x.piles a)
                                (below c (x.piles a).faceUp))).piles k).hidden
                              = (x.piles k).hidden
                          by_cases hka : k = a
                          · rw [hka]
                            rw [hhA]
                          · rw [hrP k, ite_eq_right hka]
                        · rw [putRun_inr_piles_ne hz hk']
                          by_cases ha : a' = a
                          · rw [hrP a', ite_eq_left ha, hbelow, hArb3, ha]
                          · rw [hrP a', ite_eq_right ha], ?_⟩
              intro a'
              rw [hs]
              cases b with
              | inl k =>
                  obtain ⟨hemp, hkng⟩ := canPlace_inl hcp
                  obtain ⟨-, hfeK⟩ := (Pile.isEmpty_eq _).mp hemp
                  by_cases hk' : a' = k
                  · rw [hk']
                    obtain ⟨rr, hrr⟩ := hrrR
                    have hyF : (((x.setPile a
                        (Pile.afterRunRemoved (x.piles a)
                          (below c (x.piles a).faceUp))).putRun
                        (fromCard c (x.piles a).faceUp) (Sum.inl k)).piles k).faceUp
                        = c :: rr := by rw [putRun_inl_landing]; exact hrr
                    rw [nzRoot_head hyF, ite_eq_left hkng, nzRoot_nil hfeK]
                  · by_cases ha : a' = a
                    · have hyF : (((x.setPile a
                        (Pile.afterRunRemoved (x.piles a)
                          (below c (x.piles a).faceUp))).putRun
                        (fromCard c (x.piles a).faceUp) (Sum.inl k)).piles a').faceUp
                        = z₀ :: pre' := by
                        rw [putRun_inl_piles hk', hrP a', ite_eq_left ha,
                          hbelow, hArb3]
                      have hxF : (x.piles a').faceUp = z₀ :: r := by
                        rw [ha, hfx0, hfz]
                      rw [nzRoot_head hyF, nzRoot_head hxF]
                    · exact nzRoot_congr_pile
                        ((putRun_inl_piles hk').trans
                          ((hrP a').trans (ite_eq_right ha)))
              | inr z =>
                  cases hz : (x.setPile a
                      (Pile.afterRunRemoved (x.piles a)
                        (below c (x.piles a).faceUp))).pileOfTop z with
                  | none =>
                      by_cases ha : a' = a
                      · have hyF : (((x.setPile a
                          (Pile.afterRunRemoved (x.piles a)
                            (below c (x.piles a).faceUp))).putRun
                          (fromCard c (x.piles a).faceUp) (Sum.inr z)).piles a').faceUp
                          = z₀ :: pre' := by
                          rw [putRun_inr_none_piles hz, hrP a', ite_eq_left ha,
                            hbelow, hArb3]
                        have hxF : (x.piles a').faceUp = z₀ :: r := by
                          rw [ha, hfx0, hfz]
                        rw [nzRoot_head hyF, nzRoot_head hxF]
                      · exact nzRoot_congr_pile
                          ((putRun_inr_none_piles hz a').trans
                            ((hrP a').trans (ite_eq_right ha)))
                  | some k =>
                      by_cases hk' : a' = k
                      · rw [hk']
                        by_cases hka : k = a
                        · rw [hka]
                          rw [hka] at hz
                          have hyF : (((x.setPile a
                              (Pile.afterRunRemoved (x.piles a)
                                (below c (x.piles a).faceUp))).putRun
                              (fromCard c (x.piles a).faceUp) (Sum.inr z)).piles a).faceUp
                              = z₀ :: (pre' ++ fromCard c (x.piles a).faceUp) := by
                            rw [putRun_inr_landing hz, hrP a, ite_eq_left rfl, hbelow,
                              hArb3, List.cons_append]
                          have hxF : (x.piles a).faceUp = z₀ :: r := by rw [hfx0, hfz]
                          rw [nzRoot_head hyF, nzRoot_head hxF]
                        · have hsPk : (x.setPile a
                            (Pile.afterRunRemoved (x.piles a)
                              (below c (x.piles a).faceUp))).piles k
                            = x.piles k := by rw [hrP k, ite_eq_right hka]
                          have hxK : (x.piles k).faceUp ≠ [] := by
                            rw [← hsPk]
                            exact (pileOfTop_top hz).1
                          cases hfxK : (x.piles k).faceUp with
                          | nil => rw [hfxK] at hxK; exact absurd hxK (by simp)
                          | cons g gs =>
                            have hyF : (((x.setPile a
                                (Pile.afterRunRemoved (x.piles a)
                                  (below c (x.piles a).faceUp))).putRun
                                (fromCard c (x.piles a).faceUp) (Sum.inr z)).piles k).faceUp
                                = g :: (gs ++ fromCard c (x.piles a).faceUp) := by
                              rw [putRun_inr_landing hz, hsPk, hfxK, List.cons_append]
                            rw [nzRoot_head hyF, nzRoot_head hfxK]
                      · by_cases ha : a' = a
                        · have hyF : (((x.setPile a
                            (Pile.afterRunRemoved (x.piles a)
                              (below c (x.piles a).faceUp))).putRun
                            (fromCard c (x.piles a).faceUp) (Sum.inr z)).piles a').faceUp
                            = z₀ :: pre' := by
                            rw [putRun_inr_piles_ne hz hk', hrP a',
                              ite_eq_left ha, hbelow, hArb3]
                          have hxF : (x.piles a').faceUp = z₀ :: r := by
                            rw [ha, hfx0, hfz]
                          rw [nzRoot_head hyF, nzRoot_head hxF]
                        · exact nzRoot_congr_pile
                            ((putRun_inr_piles_ne hz hk').trans
                              ((hrP a').trans (ite_eq_right ha)))

/-! ## The journey lifts -/

/-- **What a witness shuffle cannot change.**  Every leg of a
`ShufflePlayW` journey conserves the four datums, so the whole
journey does: the tip's cycle count, draw pool, per-anchor hidden
lists, and seat roots are the source's. -/
private theorem shuffleW_data : ∀ {st z : State} {l : List Move},
    ShufflePlayW st l z →
    cycleCount z = cycleCount st ∧ drawPool z = drawPool st ∧
    (∀ a, (z.piles a).hidden = (st.piles a).hidden) ∧
    (∀ a, nzRoot z a = nzRoot st a) := by
  intro st z l h
  induction h with
  | nil s => exact ⟨rfl, rfl, fun _ => rfl, fun _ => rfl⟩
  | cons hw hstep hrest ih =>
      obtain ⟨c1, p1, h1, n1⟩ := leg_data hw hstep
      obtain ⟨c2, p2, h2, n2⟩ := ih
      exact ⟨c2.trans c1, p2.trans p1, fun a => (h2 a).trans (h1 a),
        fun a => (n2 a).trans (n1 a)⟩

/-- Witness journeys preserve WF (`step_wf` per leg). -/
private theorem shuffleW_wf_end : ∀ {st z : State} {l : List Move},
    ShufflePlayW st l z → st.WF → z.WF := by
  intro st z l h
  induction h with
  | nil s => intro hwf; exact hwf
  | cons hw hstep hrest ih =>
      intro hwf
      exact ih (step_wf hwf hstep)

/-- **What a macro-class journey cannot change** (WF-gated for the
`WF` transfer; the four datums are ungated). -/
theorem orbit_data {x y : State} (h : sameOrbitSetoid.r x y) (hwf : x.WF) :
    y.WF ∧ cycleCount y = cycleCount x ∧ drawPool y = drawPool x ∧
    (∀ a, (y.piles a).hidden = (x.piles a).hidden) ∧
    (∀ a, nzRoot y a = nzRoot x a) := by
  rcases h with ⟨σ, hσ, τ, hτ⟩
  obtain ⟨c1, p1, h1, n1⟩ := shuffleW_data hτ
  exact ⟨shuffleW_wf_end hτ hwf, c1, p1, h1, n1⟩

/-! ### The named invariant

The four-datum conjunction bundled under one name — the macro-class
invariant as a single citable predicate (the `BothOcc`/`BareLic`
pattern applied to the datum family), with the three-tier restatement
one line per rung.  The future chapter relocation hoists this block
verbatim; consumers downstream of the count program cite the class
form. -/

/-- The four macro-class datums, bundled: what a macro class carries. -/
def SameDatums (x y : State) : Prop :=
  cycleCount y = cycleCount x ∧ drawPool y = drawPool x ∧
    (∀ a, (y.piles a).hidden = (x.piles a).hidden) ∧
    (∀ a, nzRoot y a = nzRoot x a)

/-- The per-leg grade: each reversible witness leg preserves the
bundle. -/
theorem sameDatums_leg {x y : State} {m : Move}
    (hw : reversibleAtW x m) (hstep : State.step x m = some y) :
    SameDatums x y :=
  leg_data hw hstep

/-- The per-play grade: each witness shuffle preserves the bundle. -/
theorem sameDatums_play {st z : State} {l : List Move}
    (h : ShufflePlayW st l z) :
    SameDatums st z :=
  shuffleW_data h

/-- The macro-state invariant: members of a macro class share the
bundle (the WF accessor first, the datums beneath it). -/
theorem sameDatums_orbit {x y : State} (h : sameOrbitSetoid.r x y) (hwf : x.WF) :
    y.WF ∧ SameDatums x y := by
  obtain ⟨hwf', h1, h2, h3, h4⟩ := orbit_data h hwf
  exact ⟨hwf', h1, h2, h3, h4⟩

/-! ### The quotient datum kernel (the staircase footing)

The four journey-invariant datums descend to the macro classes as one
bundled carrier.  The map IS a `Quotient.lift`, and its soundness
argument is the SAME `sameDatums` machinery already staged one section
up: the datums half of `sameDatums_orbit` (the four equalities — the
WF accessor is not part of the map) at the `sameDatums_play` rung,
read through the witnessing journey of the class relation.  The reads
through the computation rule below are definitional: a consumer that
holds a member holds the class's data.  This kernel lands first as its
own coherent staging — the staircase footing the member-form tip
scheme stands on; the anchor-form's orbit-independence cell dissolves
into it (recorded at the flip landing). -/

/-- The bundled macro-class data: the four journey-invariant datums
(cycle count, draw-zone pool, per-anchor hidden stacks, per-anchor
bare non-king roots) under one carrier — what a macro class itself
reads, member-free. -/
structure MacroDatums where
  /-- the cycle count the class reads -/
  cycle : Nat
  /-- the draw-zone pool the class reads -/
  pool : List Card
  /-- the per-anchor hidden stacks the class reads -/
  hidden : Anchor → List Card
  /-- the per-anchor bare non-king roots the class reads -/
  roots : Anchor → Option Card

/-- The member read: the four datums of one state, bundled. -/
def MacroDatums.of (u : State) : MacroDatums :=
  ⟨cycleCount u, drawPool u, fun a => (u.piles a).hidden, fun a => nzRoot u a⟩

/-- The ungated class form of the datums ladder: class-mates share the
bundle with no WF hypothesis — the journey legs conserve the data, and
the WF accessor of `sameDatums_orbit` is not part of the datum map. -/
theorem sameDatums_class {x y : State} (h : sameOrbitSetoid.r x y) :
    SameDatums x y := by
  rcases h with ⟨σ, hσ, τ, hτ⟩
  exact sameDatums_play hτ

/-- The descent is well-defined: the bundled datums agree on
class-mates — the lift's soundness, one cite up the ladder. -/
theorem MacroDatums.of_class (x y : State) (h : sameOrbitSetoid.r x y) :
    MacroDatums.of x = MacroDatums.of y := by
  obtain ⟨h1, h2, h3, h4⟩ := sameDatums_class h
  show (⟨cycleCount x, drawPool x, fun a => (x.piles a).hidden, fun a => nzRoot x a⟩ : MacroDatums)
     = ⟨cycleCount y, drawPool y, fun a => (y.piles a).hidden, fun a => nzRoot y a⟩
  have e1 : cycleCount x = cycleCount y := h1.symm
  have e2 : drawPool x = drawPool y := h2.symm
  have e3 : (fun a => (x.piles a).hidden) = (fun a => (y.piles a).hidden) :=
    funext fun a => (h3 a).symm
  have e4 : (fun a => nzRoot x a) = (fun a => nzRoot y a) :=
    funext fun a => (h4 a).symm
  rw [e1, e2, e3, e4]

/-- **The class datum map**: every macro class carries the four journey
datums, read at any of its members.  The lift's soundness is the
ladder's datums half; the setoid rides the quotient type itself, never
instance search (`sameOrbitSetoid` shares the instance world with the
twin and exchange setoids — the corpus discipline: always passed
explicitly). -/
def datumOf (Q : SameOrbit) : MacroDatums :=
  Quotient.lift MacroDatums.of MacroDatums.of_class Q

/-- The computation rule: the class reads exactly the member's bundle
(definitional — the ordinary consumer-port equation). -/
theorem datumOf_mk (u : State) :
    datumOf ⟦u⟧ = MacroDatums.of u := rfl

/-! ## The tip scheme, member-form -/

/-- The member-form tip scheme, §3.1 restated: a macro transition is
one WF member of the source class, its membership, exactly one
commitment firing at it, and the class closure of the landing.  A
macro transition does not have a unique underlying MOVE (the
twin-landing merge is one edge, two moves), but it always has this
form; the single commit slot is structural — `tipEdge_exits_source`
below is the phase-progress cell reading of exactly that, so
multi-commit macro transitions cannot exist and every subsequent
commit is its own edge.  Every theorem of this chapter reads the
scheme's fields flat; the saturation the count program's successor
discipline rides is the premise-sugar `CanonicalTip` below. -/
structure TipEdge (C : SameOrbit) (D : SameOrbit) where
  /-- the member the edge reads at -/
  c : State
  /-- the member witnesses the source class -/
  hmem : ⟦c⟧ = C
  /-- the member is well-formed (realizability) -/
  hwf : c.WF
  /-- the single commitment, firing at the member -/
  m : Move
  hm : irreversibleAt c m
  /-- the landing -/
  w : State
  land : State.step c m = some w
  /-- the class closure: the target takes the landing's class -/
  cl : ⟦w⟧ = D

/-- TIP SATURATION, the premise-sugar grade: a tip edge whose member
is Final (no licensed lift remains there) — the discipline the count
program's successor construction cites as a premise.  The transport
constructs it for free (the canon member is Final by construction);
classes do not pretend literal-canonicality — saturation is
member-relative (the residue exhibit is the recorded fact). -/
def CanonicalTip {C D : SameOrbit} (e : TipEdge C D) : Prop := Final e.c

/-- The landing inherits WF from the member (`step_wf`). -/
theorem TipEdge.landing_wf {C D : SameOrbit} (e : TipEdge C D) :
    e.w.WF :=
  step_wf e.hwf e.land

/-- **The phase-progress cell**: a committed move strictly exits its
source class — the landing of a tip commit is never a class-mate of
the member, so a multi-commit macro transition cannot exist (its
second move's closure would fail).  The member-form is simpler than
the anchor-form was: if ⟦w⟧ = ⟦c⟧ held, the class relation itself
gives the returning journey (`Quotient.exact`), and the
irreversibility dies at the member directly — the journey carries
everything, no padding composition needed. -/
theorem tipEdge_exits_source {C D : SameOrbit} (e : TipEdge C D) :
    D ≠ C := by
  intro hcon
  have hclass : ⟦e.w⟧ = ⟦e.c⟧ :=
    e.cl.trans (hcon.trans e.hmem.symm)
  rcases Quotient.exact hclass with ⟨σ, hσ, τ, hτ⟩
  exact e.hm e.w τ e.land (ShufflePlayW_run hτ)

/-- **The no-fourth-kind cell (part one)**: a committed move at a WF
member is never a foundation-to-tableau giveback.  Every legal
`foundToTab` is reversible at WF (the landing-target search reads
only the piles, so its undo never dies), so it cannot be the one
commitment of a tip edge. -/
theorem tipEdge_ne_foundToTab {C D : SameOrbit} (e : TipEdge C D)
    (c : Card) (b : Base) : e.m ≠ Move.foundToTab c b := by
  intro hcon
  have hstep : e.c.step (Move.foundToTab c b) = some e.w := by
    rw [← hcon]
    exact e.land
  obtain ⟨c₀', htop0, hceq, hcp, -⟩ := step_foundToTab_inv hstep
  have htop : e.c.foundTop c.suit = some c := by rw [htop0, hceq]
  exact absurd (foundToTab_reversibleAtW_of_legal_wf e.hwf htop hcp)
    (by
      intro hrevW
      exact (reversibleAt_of_W hrevW) (by rw [← hcon]; exact e.hm))

/-- A both-empty draw zone cannot produce a draw: recycle is the identity
and there is nothing to deal (citing the public Play readers). -/
private theorem stepDraw_bothEmpty_none {st : State}
    (h1 : st.stock = []) (h2 : st.waste = []) : st.stepDraw = none := by
  show State.dealStock st.recycle = none
  rw [recycle_allEmpty st h1 h2]
  exact dealStock_nil st h1

/-- **A draw edge starts non-pure**: committed draws fire only at
pristine (empty waste) or offset (misaligned waste) tips — the pass-base
and in-phase draws are reversible and the both-empty draw is illegal. -/
theorem tipEdge_draw_shape {C D : SameOrbit} (e : TipEdge C D)
    (hm : e.m = Move.draw) :
    e.c.stock ≠ [] ∧
    (e.c.waste = [] ∨ e.c.waste.length % e.c.drawStep ≠ 0) := by
  have hsD : e.c.stepDraw = some e.w := by
    have h1 : e.c.step e.m = some e.w := e.land
    rw [hm] at h1
    exact h1
  have hrev (h : reversibleAtW e.c Move.draw) : False :=
    (reversibleAt_of_W h) (by rw [← hm]; exact e.hm)
  have hd : 0 < e.c.drawStep := e.hwf.2.2.2
  constructor
  · by_cases h1 : e.c.stock = []
    · by_cases h2 : e.c.waste = []
      · rw [stepDraw_bothEmpty_none h1 h2] at hsD
        exact absurd hsD (by simp)
      · exact (hrev (draw_passBase_reversibleW h1 h2 hd)).elim
    · exact h1
  · by_cases h2 : e.c.waste = []
    · exact Or.inl h2
    · by_cases h1 : e.c.stock = []
      · exact (hrev (draw_passBase_reversibleW h1 h2 hd)).elim
      · by_cases hres : e.c.waste.length % e.c.drawStep = 0
        · obtain ⟨s, t, hcon⟩ := list_cons_of_ne_nil h1
          have hph : inPhase e.c = true := by
            show (match e.c.stock with
              | [] => true
              | _ => decide (e.c.waste.length % e.c.drawStep = 0)) = true
            rw [hcon, hres]
            rfl
          exact (hrev (draw_reversible_inphaseW hd h1 h2 hph)).elim
        · exact Or.inr hres

/-! ## The fingerprint reads (the label-map surface) -/

/-- The waste-pop read: the unique member of the source state's draw pool
that the landing's pool lacks, first in universe order (the
cycle-difference card of the pair). -/
def poolMissCard (C w : State) : Option Card :=
  firstWhere (fun c => decide (c ∈ drawPool C ∧ c ∉ drawPool w)) Card.universe

/-- The reveal read: the unique anchor whose hidden count strictly fell
(the hidden-difference seat of the pair). -/
def hiddenDropperAnchor (C w : State) : Option Anchor :=
  firstWhere
    (fun a => decide ((w.piles a).hidden.length < (C.piles a).hidden.length))
    Anchor.all

/-- The vacate read: the unique anchor whose bare non-king root
departed (the seat-difference seat of the pair). -/
def rootFreedAnchor (C w : State) : Option Anchor :=
  firstWhere (fun a => decide (nzRoot C a ≠ nzRoot w a)) Anchor.all

/-- **The state-grade fingerprint**: the label a directly-adjacent pair
of states carries, read off the source state against the landing —
the working surface the determination rows' anatomy consumes, and the
definitional shadow of the class read (`labelOf_pair` below): the
three branches are the three channels of the fingerprint route (the
cycle-difference branch reads the pool-difference card; the
hidden-difference branch reads the hidden-difference anchor; the
degenerate zero-delta cell splits the draw from the vacate through
the seat-difference read). -/
def CanonLabel (C w : State) : EdgeLabel :=
  if cycleCount w < cycleCount C then
    match poolMissCard C w with
    | some c => EdgeLabel.wasteEntry c
    | none => EdgeLabel.draw
  else if hiddenTotal w < hiddenTotal C then
    match hiddenDropperAnchor C w with
    | some a => EdgeLabel.stackEvent a
    | none => EdgeLabel.draw
  else
    match rootFreedAnchor C w with
    | some a => EdgeLabel.stackEvent a
    | none => EdgeLabel.draw

/-- The hidden-total channel of the bundled data: the total the reveal
test grades, read off the per-anchor hidden stacks (the same shape
`hiddenTotal` reads off the piles). -/
def MacroDatums.hiddenTotal (d : MacroDatums) : Nat :=
  (Anchor.all.flatMap d.hidden).length

/-- The waste-pop channel over the bundled data: the unique member of
the source's pool the target's pool lacks, first in universe order. -/
def MacroDatums.poolMiss (d d' : MacroDatums) : Option Card :=
  firstWhere (fun c => decide (c ∈ d.pool ∧ c ∉ d'.pool)) Card.universe

/-- The hidden-difference channel over the bundled data: the unique
anchor whose hidden count strictly fell. -/
def MacroDatums.hiddenDropper (d d' : MacroDatums) : Option Anchor :=
  firstWhere
    (fun a => decide ((d'.hidden a).length < (d.hidden a).length))
    Anchor.all

/-- The seat-difference channel over the bundled data: the unique
anchor whose bare non-king root departed. -/
def MacroDatums.rootFreed (d d' : MacroDatums) : Option Anchor :=
  firstWhere (fun a => decide (d.roots a ≠ d'.roots a)) Anchor.all

/-- **The class-pair fingerprint over the bundled data**: the label a
directly-adjacent class pair carries, read off the class data alone —
the three branches are the three channels of the fingerprint route
(the cycle-difference branch reads the pool-difference card; the
hidden-difference branch reads the hidden-difference anchor; the
degenerate zero-delta cell splits the draw from the vacate through
the seat-difference read). -/
def labelOf (d d' : MacroDatums) : EdgeLabel :=
  if d'.cycle < d.cycle then
    match d.poolMiss d' with
    | some c => EdgeLabel.wasteEntry c
    | none => EdgeLabel.draw
  else if d'.hiddenTotal < d.hiddenTotal then
    match d.hiddenDropper d' with
    | some a => EdgeLabel.stackEvent a
    | none => EdgeLabel.draw
  else
    match d.rootFreed d' with
    | some a => EdgeLabel.stackEvent a
    | none => EdgeLabel.draw

/-- The state-grade read of the class fingerprint: DEFINITIONAL (the
lift's computation rule plus the readers' shared shapes) — the member
pair sees exactly the old anchor-form's `CanonLabel`.  This equation
is where `canonLabel_orbit_indep` dissolved: the read is independent
of the member because both sides ARE the class read (`rfl`). -/
theorem labelOf_pair (c w : State) :
    labelOf (datumOf ⟦c⟧) (datumOf ⟦w⟧) = CanonLabel c w := rfl

/-- The label of a class-pair edge: the class fingerprint over the
quotient data.  The binder is underscore-named deliberately: the label
never reads the edge — the pair-functionality is structural now. -/
def TipEdge.label {C D : SameOrbit} (_e : TipEdge C D) : EdgeLabel :=
  labelOf (datumOf C) (datumOf D)

/-- **The label is a function of the pair** — definitional through the
lift: two tip edges witnessing the same class pair carry the same
label because the label never reads the member, the commitment, or
the landing — only the classes.  (The old transport through
`canonLabel_orbit_indep` plus `landing_wf` is the lift's soundness,
paid once inside `datumOf`.) -/
theorem edge_label_unique {C D : SameOrbit}
    (e₁ e₂ : TipEdge C D) : e₁.label = e₂.label := rfl

/-! ## The determination rows (one commit family at a time)

The rows, re-landed at the member grade: the lens `label_read` turns
the class fingerprint into the state-grade anatomy (the memberships
transport the datum reads; `labelOf_pair` closes on the state
fingerprint underneath), and every row then runs the old anatomy at
(e.c, e.w) — the faces of the moves read at the member exactly as
they were read at the padding tip.  The spines sit between the rows
as before, now state-grade (the kit the rows share with the
vacate-recycling family and the commit-kind cells). -/

/-- **The label-read lens**: the class fingerprint reads at the member
pair — the memberships (hmem at the source, cl at the landing) become
pre-formed datum-level transports, and `labelOf_pair` closes on the
state-grade view underneath; the datum-carry the old padding
performed per edge now rides the class machinery, once, here. -/
private theorem label_read {C D : SameOrbit} (e : TipEdge C D) :
    e.label = CanonLabel e.c e.w := by
  show labelOf (datumOf C) (datumOf D) = _
  have hC : datumOf C = datumOf ⟦e.c⟧ := by rw [e.hmem]
  have hD : datumOf D = datumOf ⟦e.w⟧ := by rw [e.cl]
  rw [hC, hD]
  exact labelOf_pair e.c e.w

/-- **The draw row**: an edge whose single commitment is a draw is
draw-labeled — the draw moves stock to waste within one reservoir, so
no datum changes across the pair: the cycle test fails (the landing
reads the member's count), the hidden test fails (the landing reads
the member's total), and the seat read finds no differing root (the
landing reads the member's roots) — the fingerprint degenerates to
`draw`. -/
theorem tipEdge_label_draw {C D : SameOrbit} (e : TipEdge C D)
    (hm : e.m = Move.draw) : e.label = EdgeLabel.draw := by
  rw [label_read]
  have hsD : e.c.stepDraw = some e.w := by
    have h1 : e.c.step e.m = some e.w := e.land
    rw [hm] at h1
    exact h1
  have hpiles : e.w.piles = e.c.piles := stepDraw_piles hsD
  have hcyc : cycleCount e.w = cycleCount e.c := stepDraw_cycle hsD
  have hHT : hiddenTotal e.w = hiddenTotal e.c :=
    hiddenTotal_congr (fun a => congrArg Pile.hidden (congrFun hpiles a))
  have hnz : ∀ a, nzRoot e.c a = nzRoot e.w a :=
    fun a => (nzRoot_congr_pile (congrFun hpiles a)).symm
  unfold CanonLabel
  rw [hcyc, hHT]
  rw [ite_eq_right (Nat.lt_irrefl (cycleCount e.c))]
  rw [ite_eq_right (Nat.lt_irrefl (hiddenTotal e.c))]
  have hnone : rootFreedAnchor e.c e.w = none := by
    unfold rootFreedAnchor
    refine firstWhere_none_of_forall (fun a => decide (nzRoot e.c a ≠ nzRoot e.w a))
      (fun a _ => ?_)
    by_cases hEq : nzRoot e.c a = nzRoot e.w a
    · exact decide_eq_false (fun hne => hne hEq)
    · exact absurd (hnz a) hEq
  rw [hnone]

/-- **The waste row anatomy, state-grade**: the cycle test fires (the
waste head is gone from the conserved count) and the pool read pins
the head card — `c` is in the source pool and out of the landing's
(the stock is untouched and the tail carries over, so `c` in the tail
would sit twice in the landing — in the surviving waste and in its
found/pile landing zone — which `mem_waste_unique` at the landing
kills), and any other pool-difference card would have to come from the
untouched stock or the surviving tail, both of which stay in the
landing's pool.  (State-grade since the flip: the source-state
parameters took the old edge-fields' places; the row adds only the
memberships and the WF passage.) -/
private theorem waste_entry_spine {x w : State}
    (hwf : x.WF) (hhw : w.WF)
    (hcwlt : cycleCount w + 1 ≤ cycleCount x) {c : Card} {xs : List Card}
    (hwu : x.waste = c :: xs) (hstock : w.stock = x.stock)
    (hww : w.waste = xs)
    (hspot : (∃ s, c ∈ w.found s) ∨ (∃ a, c ∈ (w.piles a).faceUp)) :
    CanonLabel x w = EdgeLabel.wasteEntry c := by
  have hwmem : c ∈ x.waste := by rw [hwu]; exact List.mem_cons_self
  have hlt : cycleCount w < cycleCount x := by omega
  have hcIn : c ∈ drawPool x := by
    show c ∈ x.stock.reverse ++ x.waste
    rw [hwu]
    exact List.mem_append_right _ (by simp)
  have hLpool : drawPool w = x.stock.reverse ++ xs := by
    show w.stock.reverse ++ w.waste = _
    rw [hstock, hww]
  have hcOut : c ∉ drawPool w := by
    rw [hLpool]
    refine fun hmem => ?_
    rcases (List.mem_append).1 hmem with hrev | hxs
    · exact (mem_waste_unique hwf hwmem).2.1 (List.mem_reverse.mp hrev)
    · have hcwmem : c ∈ w.waste := by rw [hww]; exact hxs
      rcases hspot with ⟨s, hfs⟩ | ⟨a₀, hfa⟩
      · exact (mem_waste_unique hhw hcwmem).2.2 s hfs
      · exact ((mem_waste_unique hhw hcwmem).1 a₀).2 hfa
  have hread : poolMissCard x w = some c := by
    unfold poolMissCard
    refine firstWhere_find (p :=
      fun c' => decide (c' ∈ drawPool x ∧ c' ∉ drawPool w)) ?_ ?_ ?_
    · exact Card.mem_universe c
    · exact decide_eq_true ⟨hcIn, hcOut⟩
    · intro y _ hne
      show decide (y ∈ drawPool x ∧ y ∉ drawPool w) = false
      rw [decide_eq_false]
      refine fun hpred => ?_
      obtain ⟨hyIn, hyOut⟩ := hpred
      rcases (List.mem_append).1 hyIn with hstk | hws
      · exact absurd (by
          rw [hLpool]
          exact List.mem_append_left _ hstk) hyOut
      · rw [hwu] at hws
        rcases (List.mem_cons).1 hws with hyeq | hyxs
        · exact hne hyeq
        · exact absurd (by
            rw [hLpool]
            exact List.mem_append_right _ hyxs) hyOut
  unfold CanonLabel
  rw [ite_eq_left hlt, hread]

/-- **The waste row**: an edge whose single commitment hands `c` out of
the waste is wasteEntry-labeled with THAT card — the cycle strictly
drops across the pair, and the pool-difference read is exactly the
popped card (uniquely pinned by the pool arithmetic in the spine
above; the WF ports are the member's field and `TipEdge.landing_wf`). -/
theorem tipEdge_label_waste {C D : SameOrbit} (e : TipEdge C D)
    {c : Card} (hwm : WasteOf c e.m) :
    e.label = EdgeLabel.wasteEntry c := by
  rw [label_read]
  rcases hwm with heqm | ⟨b, heqm⟩
  · have hstep : e.c.step (Move.wasteToFound c) = some e.w := by
      rw [← heqm]
      exact e.land
    obtain ⟨hguard, x, xs, hws, hsucc⟩ := step_wasteToFound_inv hstep
    rw [Bool.and_eq_true] at hguard
    obtain ⟨hw, -⟩ := hguard
    have hxc : x = c := State.wasteIs_head_eq hws hw
    have hwu : e.c.waste = c :: xs := by rw [hws, hxc]
    have hstock : e.w.stock = e.c.stock := by
      rw [hsucc]
      exact setFound_stock e.c c.suit (e.c.found c.suit ++ [c])
    have hww : e.w.waste = xs := by rw [hsucc]
    have hfound : c ∈ e.w.found c.suit := by
      rw [hsucc]
      show c ∈ (if c.suit = c.suit then e.c.found c.suit ++ [c] else e.c.found c.suit)
      rw [ite_eq_left rfl]
      exact List.mem_append_right _ (by simp)
    exact waste_entry_spine e.hwf (TipEdge.landing_wf e)
      (cycleCount_step_wasteToFound hstep) hwu hstock hww
      (Or.inl ⟨c.suit, hfound⟩)
  · have hstep : e.c.step (Move.wasteToTab c b) = some e.w := by
      rw [← heqm]
      exact e.land
    obtain ⟨hguard, x, xs, hws, hsucc⟩ := step_wasteToTab_inv hstep
    rw [Bool.and_eq_true] at hguard
    obtain ⟨hw, hcp⟩ := hguard
    have hxc : x = c := State.wasteIs_head_eq hws hw
    have hwu : e.c.waste = c :: xs := by rw [hws, hxc]
    have hstock : e.w.stock = e.c.stock := by
      rw [hsucc]
      exact putCard_stock e.c c b
    have hww : e.w.waste = xs := by rw [hsucc]
    have hspot : (∃ s, c ∈ e.w.found s) ∨ (∃ a, c ∈ (e.w.piles a).faceUp) := by
      cases b with
      | inl a₀ =>
          refine Or.inr ⟨a₀, ?_⟩
          rw [hsucc]
          show c ∈ ((e.c.putCard c (Sum.inl a₀)).piles a₀).faceUp
          rw [putCard_inl_landing]
          exact by simp
      | inr z =>
          obtain ⟨k, hz, -⟩ := canPlace_inr hcp
          refine Or.inr ⟨k, ?_⟩
          rw [hsucc]
          show c ∈ ((e.c.putCard c (Sum.inr z)).piles k).faceUp
          rw [putCard_inr_landing hz]
          show c ∈ (e.c.piles k).faceUp ++ [c]
          exact List.mem_append_right _ (by simp)
    exact waste_entry_spine e.hwf (TipEdge.landing_wf e)
      (cycleCount_step_wasteToTab hstep) hwu hstock hww hspot

/-- The label-assembly spine of the reveal row, state-grade: the cycle
test dies at the conserved count, the hidden test fires, and the
hidden-difference read is exactly the departing seat (its hidden
dropped a card, every other seat's is verbatim). -/
private theorem reveal_spine {x w : State}
    (hcycC : cycleCount w = cycleCount x)
    (hltH : hiddenTotal w + 1 ≤ hiddenTotal x)
    {a : Anchor} (hdropA : (w.piles a).hidden.length + 1
      = (x.piles a).hidden.length)
    (hElse : ∀ a', a' ≠ a → (w.piles a').hidden = (x.piles a').hidden) :
    CanonLabel x w = EdgeLabel.stackEvent a := by
  have hRead : hiddenDropperAnchor x w = some a := by
    unfold hiddenDropperAnchor
    refine firstWhere_find (p :=
      fun a' => decide ((w.piles a').hidden.length < (x.piles a').hidden.length)) ?_ ?_ ?_
    · exact Anchor.mem_all a
    · exact decide_eq_true (by omega)
    · intro y _ hne
      by_cases hy : y = a
      · exact absurd hy hne
      · show decide ((w.piles y).hidden.length < (x.piles y).hidden.length) = false
        rw [decide_eq_false]
        intro hlt
        rw [hElse y hy] at hlt
        exact Nat.lt_irrefl _ hlt
  unfold CanonLabel
  rw [hcycC, ite_eq_right (Nat.lt_irrefl (cycleCount x))]
  rw [ite_eq_left (show hiddenTotal w < hiddenTotal x by omega)]
  rw [hRead]

/-- The cell predicates carry the move as a family index; this
non-indexed restatement lets the row unpack a cell against a
structure-field move. -/
private theorem RevealCell_shape {u : State} {a : Anchor} {m : Move}
    (h : RevealCellAt u a m) :
    (∃ c, m = Move.tabToFound c ∧ u.pileOfTop c = some a ∧
        chop (u.piles a).faceUp = [] ∧ (u.piles a).hidden ≠ []) ∨
    (∃ c b, m = Move.tabToTab c b ∧ u.pileHolding c = some a ∧
        below c (u.piles a).faceUp = [] ∧ (u.piles a).hidden ≠ []) := by
  cases h with
  | tabToFound hloc hpre hhne => exact Or.inl ⟨_, rfl, hloc, hpre, hhne⟩
  | tabToTab hloc hpre hhne => exact Or.inr ⟨_, _, rfl, hloc, hpre, hhne⟩

/-- **The reveal row**: an edge whose single commitment is a reveal
(the run departing a pile carries the pile's whole face-up content
over a nonempty hidden stack, so the automatic flip fires) is
stackEvent-labeled at THE seat it departs — the cycle test dies (the
tab move keeps the zone, so the landing reads the member's count),
the hidden test fires (the hidden stack lost its head), and the
hidden-difference read is exactly that seat:
`afterRunRemoved_hidden`'s head-drop disjunct gives the one-card loss
at the seat while every other seat's hidden survives verbatim (the
move touches one seat's pile only). -/
theorem tipEdge_label_reveal {C D : SameOrbit} (e : TipEdge C D)
    {a : Anchor} (hcell : RevealCellAt e.c a e.m) :
    e.label = EdgeLabel.stackEvent a := by
  rw [label_read]
  rcases RevealCell_shape hcell with
    ⟨c, heqm, hloc, hpre, hhne⟩ | ⟨c, b, heqm, hloc, hpre, hhne⟩
  · -- tabToFound
    have hstep : e.c.step (Move.tabToFound c) = some e.w := by
      rw [← heqm]
      exact e.land
    obtain ⟨-, a', hloc', hsucc⟩ := step_tabToFound_inv hstep
    have ha' : a = a' := Option.some.inj (hloc.symm.trans hloc')
    subst ha'
    have hWa : (e.w.piles a).hidden =
        (Pile.afterRunRemoved (e.c.piles a) (chop (e.c.piles a).faceUp)).hidden := by
      rw [hsucc]
      show (if a = a then
          Pile.afterRunRemoved (e.c.piles a) (chop (e.c.piles a).faceUp)
          else e.c.piles a).hidden = _
      rw [ite_eq_left rfl]
    have hElse : ∀ a', a' ≠ a → (e.w.piles a').hidden = (e.c.piles a').hidden := by
      intro a' hne
      rw [hsucc]
      show (if a' = a then
          Pile.afterRunRemoved (e.c.piles a) (chop (e.c.piles a).faceUp)
          else e.c.piles a').hidden = _
      rw [ite_eq_right hne]
    rw [hpre] at hWa
    have hdropA : (e.w.piles a).hidden.length + 1
        = (e.c.piles a).hidden.length := by
      rw [hWa]
      rcases afterRunRemoved_hidden (e.c.piles a) [] with ⟨he, -⟩ | ⟨-, he, -⟩ |
        ⟨-, he, hdrop⟩
      · exact absurd rfl he
      · exact absurd he hhne
      · exact hdrop
    have hhz : e.w.stock = e.c.stock ∧ e.w.waste = e.c.waste := by
      rw [hsucc]
      exact ⟨rfl, rfl⟩
    have hdrop' : hiddenTotal e.w + 1 ≤ hiddenTotal e.c := by
      refine hiddenTotal_mono_lt (a := a) (fun a' => ?_) ?_
      · by_cases hne : a' = a
        · rw [hne]; omega
        · rw [hElse a' hne]
          exact Nat.le_refl _
      · rw [hdropA]
        omega
    exact reveal_spine (cycleCount_eq_of_stock_waste hhz.1 hhz.2)
      hdrop' hdropA hElse
  · -- tabToTab
    have hstep : e.c.step (Move.tabToTab c b) = some e.w := by
      rw [← heqm]
      exact e.land
    obtain ⟨a₀, hh, hcp, hfr, hsucc⟩ := step_tabToTab_inv hstep
    have ha₀ : a = a₀ := Option.some.inj (hloc.symm.trans hh)
    subst ha₀
    -- the member's seat a holds c face-up (the run head is real)
    have hmem : c ∈ (e.c.piles a).faceUp := pileHolding_mem hloc
    -- the arrival hidden at the departing seat is the removal state's,
    -- and it drops one card (the flip); every other seat's is verbatim
    have hWa : (e.w.piles a).hidden =
        (Pile.afterRunRemoved (e.c.piles a) (below c (e.c.piles a).faceUp)).hidden := by
      cases b with
      | inl k =>
          obtain ⟨hemp, -⟩ := canPlace_inl hcp
          have hka : k ≠ a := by
            intro hcon
            rw [hcon] at hemp
            have hfe := ((Pile.isEmpty_eq _).mp hemp).2
            rw [hfe] at hmem
            exact absurd hmem (by simp)
          rw [hsucc, putRun_inl_piles (fun hc => hka hc.symm)]
          exact congrArg Pile.hidden setPile_piles_self
      | inr z =>
          cases hz : (e.c.setPile a
              (Pile.afterRunRemoved (e.c.piles a)
                (below c (e.c.piles a).faceUp))).pileOfTop z with
          | none =>
              rw [hsucc, putRun_inr_none_piles hz]
              exact congrArg Pile.hidden (setPile_piles_self)
          | some k =>
              have hpR : ((e.c.setPile a
                    (Pile.afterRunRemoved (e.c.piles a)
                      (below c (e.c.piles a).faceUp))).piles a).hidden
                  = (Pile.afterRunRemoved (e.c.piles a)
                    (below c (e.c.piles a).faceUp)).hidden :=
                congrArg Pile.hidden setPile_piles_self
              by_cases hka : k = a
              · have hza : (e.c.setPile a
                    (Pile.afterRunRemoved (e.c.piles a)
                      (below c (e.c.piles a).faceUp))).pileOfTop z = some a := hka ▸ hz
                rw [hsucc, putRun_inr_landing hza]
                show ({ ((e.c.setPile a
                    (Pile.afterRunRemoved (e.c.piles a)
                      (below c (e.c.piles a).faceUp))).piles a) with
                    faceUp := ((e.c.setPile a
                    (Pile.afterRunRemoved (e.c.piles a)
                      (below c (e.c.piles a).faceUp))).piles a).faceUp ++
                      fromCard c (e.c.piles a).faceUp } : Pile).hidden = _
                exact hpR
              · rw [hsucc, putRun_inr_piles_ne hz (fun hc => hka hc.symm)]
                exact congrArg Pile.hidden (setPile_piles_self)
    have hElse : ∀ a', a' ≠ a → (e.w.piles a').hidden = (e.c.piles a').hidden := by
      intro a' hne
      cases b with
      | inl k =>
          obtain ⟨hemp, -⟩ := canPlace_inl hcp
          by_cases hk' : a' = k
          · rw [hsucc, hk', putRun_inl_landing]
            show ([] : List Card) = (e.c.piles k).hidden
            exact (((Pile.isEmpty_eq _).mp hemp).1).symm
          · rw [hsucc, putRun_inl_piles hk']
            rw [setPile_piles_ne hne]
      | inr z =>
          cases hz : (e.c.setPile a
              (Pile.afterRunRemoved (e.c.piles a)
                (below c (e.c.piles a).faceUp))).pileOfTop z with
          | none =>
              rw [hsucc, putRun_inr_none_piles hz]
              rw [setPile_piles_ne hne]
          | some k =>
              by_cases hk' : a' = k
              · rw [hsucc, hk', putRun_inr_landing hz]
                show (((e.c.setPile a
                    (Pile.afterRunRemoved (e.c.piles a)
                      (below c (e.c.piles a).faceUp))).piles k).hidden) = _
                exact congrArg Pile.hidden
                  (setPile_piles_ne (fun hc => hne (by rw [hk']; exact hc)))
              · rw [hsucc, putRun_inr_piles_ne hz hk']
                rw [setPile_piles_ne hne]
    rw [hpre] at hWa
    have hdropA : (e.w.piles a).hidden.length + 1
        = (e.c.piles a).hidden.length := by
      rw [hWa]
      rcases afterRunRemoved_hidden (e.c.piles a) [] with ⟨he, -⟩ | ⟨-, he, -⟩ |
        ⟨-, he, hdrop⟩
      · exact absurd rfl he
      · exact absurd he hhne
      · exact hdrop
    have hhz : e.w.stock = e.c.stock ∧ e.w.waste = e.c.waste := by
      rw [hsucc]
      exact ⟨putRun_stock _ _ _, putRun_waste _ _ _⟩
    have hdrop' : hiddenTotal e.w + 1 ≤ hiddenTotal e.c := by
      refine hiddenTotal_mono_lt (a := a) (fun a' => ?_) ?_
      · by_cases hne2 : a' = a
        · rw [hne2]; omega
        · rw [hElse a' hne2]
          exact Nat.le_refl _
      · rw [hdropA]
        omega
    exact reveal_spine (cycleCount_eq_of_stock_waste hhz.1 hhz.2)
      hdrop' hdropA hElse


/-- The vacate cell predicates carry the move as a family index; this
non-indexed restatement lets the row unpack a cell against a
structure-field move. -/
private theorem VacateCell_shape {u : State} {a : Anchor} {m : Move}
    (h : VacateCellAt u a m) :
    (∃ c, m = Move.tabToFound c ∧ u.pileOfTop c = some a ∧
        chop (u.piles a).faceUp = [] ∧ (u.piles a).hidden = [] ∧
        c.rank ≠ Rank.king) ∨
    (∃ c b, m = Move.tabToTab c b ∧ u.pileHolding c = some a ∧
        below c (u.piles a).faceUp = [] ∧ (u.piles a).hidden = [] ∧
        c.rank ≠ Rank.king) := by
  cases h with
  | tabToFound hloc hpre hhd hnk =>
      exact Or.inl ⟨_, rfl, hloc, hpre, hhd, hnk⟩
  | tabToTab hloc hpre hhd hnk =>
      exact Or.inr ⟨_, _, rfl, hloc, hpre, hhd, hnk⟩

/-- The label-assembly spine of the vacate row, state-grade: both
tests die, and the seat-difference read is exactly the freed seat. -/
private theorem vacate_spine {x w : State}
    (hcycC : cycleCount w = cycleCount x)
    (hnhC : hiddenTotal w = hiddenTotal x)
    {a : Anchor} (hRootNe : nzRoot x a ≠ nzRoot w a)
    (hElseR : ∀ a', a' ≠ a → nzRoot x a' = nzRoot w a') :
    CanonLabel x w = EdgeLabel.stackEvent a := by
  have hRead : rootFreedAnchor x w = some a := by
    unfold rootFreedAnchor
    refine firstWhere_find (p :=
      fun a' => decide (nzRoot x a' ≠ nzRoot w a')) ?_ ?_ ?_
    · exact Anchor.mem_all a
    · exact decide_eq_true hRootNe
    · intro y _ hne
      by_cases hy : y = a
      · exact absurd hy hne
      · show decide (nzRoot x y ≠ nzRoot w y) = false
        rw [decide_eq_false]
        intro hne2
        rw [← hElseR y hy] at hne2
        exact hne2 rfl
  unfold CanonLabel
  rw [hcycC, ite_eq_right (Nat.lt_irrefl (cycleCount x))]
  rw [hnhC, ite_eq_right (Nat.lt_irrefl (hiddenTotal x))]
  rw [hRead]

/-- The vacate row's tabToTab-inr cell, fact one (`hwRootNone`): the
freed seat's root is `none` at the landing — the seat is BARE at the
removal (the hidden-free run departure empties it), and the located
landing can never sit back on it (the top search misses a bare pile:
`pileOfTop_ne_of_bare`), so whatever the search found, the seat is
carried into the landing empty and its root is gone. -/
private theorem vacate_inr_root_none {st : State} {a : Anchor} {c : Card}
    {z : Card} {run : List Card} {w : State}
    (hsucc : w = (st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
          run (Sum.inr z))
    (hpre : below c (st.piles a).faceUp = [])
    (hhd : (st.piles a).hidden = []) :
    nzRoot w a = none := by
  have hRbare : ((st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles a)
      = ⟨[], ([] : List Card)⟩ := by
    rw [setPile_piles_self, hpre]
    exact afterRunRemoved_bare_empty hhd
  have hRbareH : ((st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles a).hidden
      = [] := congrArg Pile.hidden hRbare
  have hRbareF : ((st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles a).faceUp
      = [] := congrArg Pile.faceUp hRbare
  have hPa : (w.piles a).faceUp = [] := by
    cases hz : (st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).pileOfTop z with
    | none =>
        rw [hsucc, putRun_inr_none_piles hz]
        exact hRbareF
    | some k =>
        have hka : k ≠ a :=
          fun hcon => pileOfTop_ne_of_bare ⟨hRbareH, hRbareF⟩ z (hcon ▸ hz)
        rw [hsucc, putRun_inr_piles_ne hz (fun hc => hka hc.symm)]
        exact hRbareF
  exact nzRoot_nil hPa

/-- The vacate row's tabToTab-inr cell, fact two (`hnh`): the move
conserves every seat's hidden stack — the freed seat's is empty at the
removal (and the landing can never sit back on a bare pile), and the
located landing extends FACE-UP content only, so the hidden lists
ride `putRun`'s placement untouched. -/
private theorem vacate_inr_hidden {st : State} {a : Anchor} {c : Card}
    {z : Card} {run : List Card} {w : State}
    (hsucc : w = (st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
          run (Sum.inr z))
    (hpre : below c (st.piles a).faceUp = [])
    (hhd : (st.piles a).hidden = []) :
    ∀ a', (w.piles a').hidden = (st.piles a').hidden := by
  have hRbare : ((st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles a)
      = ⟨[], ([] : List Card)⟩ := by
    rw [setPile_piles_self, hpre]
    exact afterRunRemoved_bare_empty hhd
  have hRbareH : ((st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles a).hidden
      = [] := congrArg Pile.hidden hRbare
  have hRbareF : ((st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles a).faceUp
      = [] := congrArg Pile.faceUp hRbare
  intro a'
  by_cases hEq2 : a' = a
  · rw [hEq2]
    cases hz : (st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).pileOfTop z with
    | none =>
        rw [hsucc, putRun_inr_none_piles hz, hRbareH]
        exact hhd.symm
    | some k =>
        have hka : k ≠ a :=
          fun hcon => pileOfTop_ne_of_bare ⟨hRbareH, hRbareF⟩ z (hcon ▸ hz)
        rw [hsucc, putRun_inr_piles_ne hz (fun hc => hka hc.symm), hRbareH]
        exact hhd.symm
  · cases hz : (st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).pileOfTop z with
    | none =>
        rw [hsucc, putRun_inr_none_piles hz, setPile_piles_ne hEq2]
    | some k =>
        by_cases hk' : a' = k
        · rw [hsucc, hk', putRun_inr_landing hz]
          have hka : k ≠ a := by rw [← hk']; exact hEq2
          show ((st.setPile a
              (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k).hidden
            = _
          rw [setPile_piles_ne hka]
        · rw [hsucc, putRun_inr_piles_ne hz hk', setPile_piles_ne hEq2]

/-- The vacate row's tabToTab-inr cell, fact three (`hElseR` — the
row's seat-difference side-condition): every OTHER seat's root survives
the landing verbatim.  An untouched seat reads through; the located
landing extends the landing pile's face-up run at its END, so the
pile's head — the root the read consumes — outlives the appended run
(`pileOfTop_top` supplies the nonempty face-up whose head survives).
The inl landing never gets here: it dies at the king guard in the
row, a non-king mover being the vacate cell's premise. -/
private theorem vacate_inr_root_keep {st : State} {a : Anchor} {c : Card}
    {z : Card} {run : List Card} {w : State}
    (hsucc : w = (st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
          run (Sum.inr z)) :
    ∀ a', a' ≠ a → nzRoot st a' = nzRoot w a' := by
  intro a' hne
  cases hz : (st.setPile a
      (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).pileOfTop z with
  | none =>
      have hPu : (w.piles a') = (st.piles a') := by
        rw [hsucc, putRun_inr_none_piles hz, setPile_piles_ne hne]
      exact (nzRoot_congr_pile hPu).symm
  | some k =>
      by_cases hk' : a' = k
      · rw [hk']
        have hka : k ≠ a := by rw [← hk']; exact hne
        obtain ⟨hfRne, -⟩ := pileOfTop_top hz
        cases hcase : ((st.setPile a
            (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k).faceUp
          with
        | nil => exact absurd hcase hfRne
        | cons g t =>
            have hwP : (w.piles k).faceUp = g :: (t ++ run) := by
              rw [hsucc, putRun_inr_landing hz, hcase]
              show (g :: t) ++ run = g :: (t ++ run)
              exact List.cons_append
            rw [nzRoot_congr_pile (setPile_piles_ne hka).symm, nzRoot_head hcase,
              nzRoot_head hwP]
      · have hPu : (w.piles a') = (st.piles a') := by
          rw [hsucc, putRun_inr_piles_ne hz hk', setPile_piles_ne hne]
        exact (nzRoot_congr_pile hPu).symm

/-- **The vacate row**: an edge whose single commitment is a bare
non-king departure from a hidden-free seat is stackEvent-labeled at
THE seat it frees — the cycle and hidden tests both die (the move
keeps the draw zone and every hidden list), and the seat-difference
read is exactly that seat: its non-king root departs (the seat's
face-up content — the mover at its head — leaves the pile bare), while
every other seat's root survives (the tabToTab landing can only sit
on an empty pile at the king guard — dead for a non-king mover — or
on a located nonempty pile whose head outlives the appended run). -/
theorem tipEdge_label_vacate {C D : SameOrbit} (e : TipEdge C D)
    {a : Anchor} (hcell : VacateCellAt e.c a e.m) :
    e.label = EdgeLabel.stackEvent a := by
  rw [label_read]
  rcases VacateCell_shape hcell with
    ⟨c, heqm, hloc, hpre, hhd, hnk⟩ | ⟨c, b, heqm, hloc, hpre, hhd, hnk⟩
  · -- tabToFound: the raise leaves the seat bare
    have hstep : e.c.step (Move.tabToFound c) = some e.w := by
      rw [← heqm]
      exact e.land
    obtain ⟨-, a', hloc', hsucc⟩ := step_tabToFound_inv hstep
    have ha' : a = a' := Option.some.inj (hloc.symm.trans hloc')
    subst ha'
    obtain ⟨-, hlast⟩ := pileOfTop_top hloc
    have hfeq : (e.c.piles a).faceUp
        = chop (e.c.piles a).faceUp ++ [c] := lastOf_chop hlast
    rw [hpre, List.nil_append] at hfeq
    have hfaceUp : (e.c.piles a).faceUp = [c] := hfeq
    have hWa : (e.w.piles a) = ⟨[], ([] : List Card)⟩ := by
      rw [hsucc]
      show (if a = a then
          Pile.afterRunRemoved (e.c.piles a) (chop (e.c.piles a).faceUp)
          else e.c.piles a) = _
      rw [ite_eq_left rfl, hpre]
      exact afterRunRemoved_bare_empty hhd
    have hElseP : ∀ a', a' ≠ a → (e.w.piles a') = (e.c.piles a') := by
      intro a' hne
      rw [hsucc]
      show (if a' = a then
          Pile.afterRunRemoved (e.c.piles a) (chop (e.c.piles a).faceUp)
          else e.c.piles a') = _
      rw [ite_eq_right hne]
    have hnh : ∀ a', (e.w.piles a').hidden = (e.c.piles a').hidden := by
      intro a'
      by_cases hne : a' = a
      · rw [hne, hWa]
        exact hhd.symm
      · exact congrArg Pile.hidden (hElseP a' hne)
    have hhz : e.w.stock = e.c.stock ∧ e.w.waste = e.c.waste := by
      rw [hsucc]
      exact ⟨rfl, rfl⟩
    have huRoot : nzRoot e.c a = some c := by
      rw [nzRoot_head hfaceUp, ite_eq_right hnk]
    have hWaF : (e.w.piles a).faceUp = [] := congrArg Pile.faceUp hWa
    have hwRootNone : nzRoot e.w a = none := nzRoot_nil hWaF
    refine vacate_spine (cycleCount_eq_of_stock_waste hhz.1 hhz.2)
      (hiddenTotal_congr hnh) ?_ ?_
    · rw [huRoot, hwRootNone]
      exact Option.some_ne_none c
    · intro a' hne
      rw [nzRoot_congr_pile (hElseP a' hne)]
  · -- tabToTab: the empty-seat landing dies at the king guard
    obtain ⟨a₂, hh, hcp, hfr, hsucc⟩ := step_tabToTab_inv (by
      rw [← heqm]
      exact e.land)
    have ha₂ : a = a₂ := Option.some.inj (hloc.symm.trans hh)
    subst ha₂
    have hmem : c ∈ (e.c.piles a).faceUp := pileHolding_mem hloc
    cases hbc : (e.c.piles a).faceUp with
    | nil =>
        rw [hbc] at hmem
        exact absurd hmem (by simp)
    | cons g t =>
        have hgc : c = g := (head_eq_of_below_nil (by rw [← hbc]; exact hpre)).symm
        subst hgc
        have huRoot : nzRoot e.c a = some c := by
          rw [nzRoot_head hbc, ite_eq_right hnk]
        have hcycC : cycleCount e.w = cycleCount e.c := by
          refine cycleCount_eq_of_stock_waste ?_ ?_
          · rw [hsucc]
            exact putRun_stock _ _ _
          · rw [hsucc]
            exact putRun_waste _ _ _
        cases b with
        | inl k =>
            obtain ⟨-, hkng⟩ := canPlace_inl hcp
            exact absurd hkng hnk
        | inr z =>
            refine vacate_spine hcycC
              (hiddenTotal_congr (vacate_inr_hidden hsucc hpre hhd)) ?_ ?_
            · rw [huRoot, vacate_inr_root_none hsucc hpre hhd]
              exact Option.some_ne_none c
            · intro a' hne'
              rw [vacate_inr_root_keep hsucc a' hne']

/-! ## The commit-kind cells (the character's working kit, state-grade) -/

/-- The commit-kind shape for a `.tabToFound` tip: legality locates the
departure seat and irreversibility forces the commit cell there.  The
witness `reversibleAtW` rows kill the reversible shapes — the under row
(nonempty chop) through the Classify lift, the bare king through the
landed `tabToFound_undo_bare` — leaving exactly the reveal cell (the
automatic flip over a nonempty hidden stack) and the vacate cell (the
hidden-free non-king departure). -/
private theorem tabToFound_commit_cell {st : State} {c : Card} {w : State}
    (hwf : st.WF) (hstep : st.step (Move.tabToFound c) = some w)
    (hIrr : irreversibleAt st (Move.tabToFound c)) :
    ∃ a, st.pileOfTop c = some a ∧
      (RevealCellAt st a (Move.tabToFound c) ∨
        VacateCellAt st a (Move.tabToFound c)) := by
  obtain ⟨hnext, a, hloc, -⟩ := step_tabToFound_inv hstep
  refine ⟨a, hloc, ?_⟩
  cases hch : chop (st.piles a).faceUp with
  | cons z' preT =>
      exact ((reversibleAt_of_W
        (tabToFound_reversibleAtW_under_wf hwf hnext hloc hch)) hIrr).elim
  | nil =>
      cases hhid : (st.piles a).hidden with
      | cons h t =>
          refine Or.inl (RevealCellAt.tabToFound hloc hch ?_)
          rw [hhid]
          exact List.cons_ne_nil h t
      | nil =>
          by_cases hking : c.rank = Rank.king
          · exact ((reversibleAt_of_W
              (tabToFound_undo_bare hstep hloc hch hhid hking)) hIrr).elim
          · exact Or.inr (VacateCellAt.tabToFound hloc hch hhid hking)

/-- The commit-kind shape for a `.tabToTab` tip: legality locates the
departure seat and irreversibility forces the commit cell there — the
under row through the Classify lift, the bare king through the landed
`tabToTab_reversibleAtW_bare_king_wf` — leaving exactly the reveal and
vacate cells. -/
private theorem tabToTab_commit_cell {st : State} {c : Card} {b : Base} {w : State}
    (hwf : st.WF) (hstep : st.step (Move.tabToTab c b) = some w)
    (hIrr : irreversibleAt st (Move.tabToTab c b)) :
    ∃ a, st.pileHolding c = some a ∧
      (RevealCellAt st a (Move.tabToTab c b) ∨
        VacateCellAt st a (Move.tabToTab c b)) := by
  obtain ⟨a, hh, hcp, -, -⟩ := step_tabToTab_inv hstep
  refine ⟨a, hh, ?_⟩
  cases hb : below c (st.piles a).faceUp with
  | cons z₀ pre' =>
      exact ((reversibleAt_of_W
        (tabToTab_reversibleAtW_under_wf hwf hh hcp hb)) hIrr).elim
  | nil =>
      cases hhid : (st.piles a).hidden with
      | cons h t =>
          refine Or.inl (RevealCellAt.tabToTab hh hb ?_)
          rw [hhid]
          exact List.cons_ne_nil h t
      | nil =>
          by_cases hking : c.rank = Rank.king
          · exact ((reversibleAt_of_W
              (tabToTab_reversibleAtW_bare_king_wf hwf hh hcp hb hhid hking))
              hIrr).elim
          · exact Or.inr (VacateCellAt.tabToTab hh hb hhid hking)

/-! ## The family disjointness cells -/

/-- **The draw disjointness cell**: a draw-commit edge is never
card-labeled — the determination row reads the pair as `draw`, and the
constructor disjointness of the label alphabet keeps the card-carrying
families (waste entries, stack events) out of reach: the landing read
all four datums verbatim, so neither card-carrying read fires. -/
theorem tipEdge_label_draw_ne {C D : SameOrbit} (e : TipEdge C D)
    (hm : e.m = Move.draw) :
    (∀ c, e.label ≠ EdgeLabel.wasteEntry c) ∧
    (∀ a, e.label ≠ EdgeLabel.stackEvent a) := by
  have hL : e.label = EdgeLabel.draw := tipEdge_label_draw e hm
  constructor
  · intro c hne
    rw [hL] at hne
    exact EdgeLabel.noConfusion hne
  · intro a hne
    rw [hL] at hne
    exact EdgeLabel.noConfusion hne

/-- **The waste disjointness cell**: a waste-commit edge is never
draw-labeled nor stack-labeled — the row reads the pair as the waste
entry `wasteEntry c`, and the cycle test that fires for the waste exit
dies for the draw (the draw conserves the draw zone) and for the stack
family (whose rows ride the conserved count). -/
theorem tipEdge_label_waste_ne {C D : SameOrbit} (e : TipEdge C D)
    {c : Card} (hw : WasteOf c e.m) :
    e.label ≠ EdgeLabel.draw ∧ (∀ a, e.label ≠ EdgeLabel.stackEvent a) := by
  have hL : e.label = EdgeLabel.wasteEntry c := tipEdge_label_waste e hw
  constructor
  · intro hne
    rw [hL] at hne
    exact EdgeLabel.noConfusion hne
  · intro a hne
    rw [hL] at hne
    exact EdgeLabel.noConfusion hne

/-- **The reveal disjointness cell**: a reveal-commit edge is never
draw-labeled nor waste-labeled — the row reads the pair as the stack
event at the departing seat. -/
theorem tipEdge_label_reveal_ne {C D : SameOrbit} (e : TipEdge C D)
    {a : Anchor} (hcell : RevealCellAt e.c a e.m) :
    e.label ≠ EdgeLabel.draw ∧ (∀ c, e.label ≠ EdgeLabel.wasteEntry c) := by
  have hL : e.label = EdgeLabel.stackEvent a := tipEdge_label_reveal e hcell
  constructor
  · intro hne
    rw [hL] at hne
    exact EdgeLabel.noConfusion hne
  · intro c hne
    rw [hL] at hne
    exact EdgeLabel.noConfusion hne

/-- **The vacate disjointness cell**: same shape as the reveal's — the
two sub-cells share the `stackEvent` constructor by the recorded merge
(the degenerate no-reveal case of the reveal family), so what the
label alphabet separates here is the stack family from draw and
waste, never reveal-from-vacate. -/
theorem tipEdge_label_vacate_ne {C D : SameOrbit} (e : TipEdge C D)
    {a : Anchor} (hcell : VacateCellAt e.c a e.m) :
    e.label ≠ EdgeLabel.draw ∧ (∀ c, e.label ≠ EdgeLabel.wasteEntry c) := by
  have hL : e.label = EdgeLabel.stackEvent a := tipEdge_label_vacate e hcell
  constructor
  · intro hne
    rw [hL] at hne
    exact EdgeLabel.noConfusion hne
  · intro c hne
    rw [hL] at hne
    exact EdgeLabel.noConfusion hne

/-! ## The pair-move character (the assembly's close) -/

/-- **The pair-move character (the assembly's close)**: the label of a
tip edge determines the committed move up to the recorded
twin-landing merge.  A draw-labeled edge commits the draw; a
`wasteEntry c`-labeled edge commits a waste exit of exactly `c` (the
landing base stays free — the twin-landing merge); a stackEvent-a-labeled
edge commits a tableau departure exactly at the seat `a` names (the
raise or the run move; the landing base again free) — the cells read
at the member now, so the character's converse directions ride the
memberships and the rows.  This is the determination rows' converse,
and together with `edge_label_unique` it closes the restated
canonical property: two schemes over one class pair commit the same
*event*. -/
theorem pair_move_character {C D : SameOrbit} (e : TipEdge C D) :
    (e.label = EdgeLabel.draw → e.m = Move.draw) ∧
    (∀ c, e.label = EdgeLabel.wasteEntry c → WasteOf c e.m) ∧
    (∀ a, e.label = EdgeLabel.stackEvent a →
      (∃ c, e.m = Move.tabToFound c ∧ e.c.pileOfTop c = some a) ∨
      (∃ c b, e.m = Move.tabToTab c b ∧ e.c.pileHolding c = some a)) := by
  cases hm : e.m with
  | draw =>
      refine ⟨?_, ?_, ?_⟩
      · intro _
        rfl
      · intro c hne
        rw [tipEdge_label_draw e hm] at hne
        exact EdgeLabel.noConfusion hne
      · intro a hne
        rw [tipEdge_label_draw e hm] at hne
        exact EdgeLabel.noConfusion hne
  | wasteToFound c₀ =>
      have hrow : e.label = EdgeLabel.wasteEntry c₀ :=
        tipEdge_label_waste e (by rw [hm]; exact Or.inl rfl)
      refine ⟨?_, ?_, ?_⟩
      · intro hne
        rw [hrow] at hne
        exact EdgeLabel.noConfusion hne
      · intro c hL2
        have hcon : EdgeLabel.wasteEntry c = EdgeLabel.wasteEntry c₀ :=
          hL2.symm.trans hrow
        injection hcon with hcc0
        exact Or.inl (by rw [hcc0])
      · intro a hne
        rw [hrow] at hne
        exact EdgeLabel.noConfusion hne
  | wasteToTab c₀ b₀ =>
      have hrow : e.label = EdgeLabel.wasteEntry c₀ :=
        tipEdge_label_waste e (by rw [hm]; exact Or.inr ⟨b₀, rfl⟩)
      refine ⟨?_, ?_, ?_⟩
      · intro hne
        rw [hrow] at hne
        exact EdgeLabel.noConfusion hne
      · intro c hL2
        have hcon : EdgeLabel.wasteEntry c = EdgeLabel.wasteEntry c₀ :=
          hL2.symm.trans hrow
        injection hcon with hcc0
        exact Or.inr ⟨b₀, by rw [hcc0]⟩
      · intro a hne
        rw [hrow] at hne
        exact EdgeLabel.noConfusion hne
  | tabToFound c₀ =>
      have hstep : e.c.step (Move.tabToFound c₀) = some e.w := by
        rw [← hm]
        exact e.land
      have hIrr : irreversibleAt e.c (Move.tabToFound c₀) := by
        rw [← hm]
        exact e.hm
      obtain ⟨a₀, hloc, hcell⟩ := tabToFound_commit_cell e.hwf hstep hIrr
      have hL : e.label = EdgeLabel.stackEvent a₀ := by
        rcases hcell with hrev | hvac
        · rw [← hm] at hrev
          exact tipEdge_label_reveal e hrev
        · rw [← hm] at hvac
          exact tipEdge_label_vacate e hvac
      refine ⟨?_, ?_, ?_⟩
      · intro hne
        rw [hL] at hne
        exact EdgeLabel.noConfusion hne
      · intro c hne
        rw [hL] at hne
        exact EdgeLabel.noConfusion hne
      · intro a hL2
        rw [hL] at hL2
        injection hL2 with haa0
        rw [haa0] at hloc
        exact Or.inl ⟨c₀, rfl, hloc⟩
  | foundToTab c b =>
      exact absurd hm (tipEdge_ne_foundToTab e c b)
  | tabToTab c₀ b₀ =>
      have hstep : e.c.step (Move.tabToTab c₀ b₀) = some e.w := by
        rw [← hm]
        exact e.land
      have hIrr : irreversibleAt e.c (Move.tabToTab c₀ b₀) := by
        rw [← hm]
        exact e.hm
      obtain ⟨a₀, hloc, hcell⟩ := tabToTab_commit_cell e.hwf hstep hIrr
      have hL : e.label = EdgeLabel.stackEvent a₀ := by
        rcases hcell with hrev | hvac
        · rw [← hm] at hrev
          exact tipEdge_label_reveal e hrev
        · rw [← hm] at hvac
          exact tipEdge_label_vacate e hvac
      refine ⟨?_, ?_, ?_⟩
      · intro hne
        rw [hL] at hne
        exact EdgeLabel.noConfusion hne
      · intro c hne
        rw [hL] at hne
        exact EdgeLabel.noConfusion hne
      · intro a hL2
        rw [hL] at hL2
        injection hL2 with haa0
        rw [haa0] at hloc
        exact Or.inr ⟨c₀, b₀, rfl, hloc⟩

/-- The character in switch form: match on the label, read the move.
Compiler-checked exhaustive over the tripartite alphabet (a fourth
constructor would fail to elaborate here, not pass silently) — the
consumption form the count program's per-label branch analysis cites;
the three-conjunct form above stays the honest accountant. -/
theorem pair_move_character_switch {C D : SameOrbit} (e : TipEdge C D) :
    match e.label with
    | EdgeLabel.draw => e.m = Move.draw
    | EdgeLabel.wasteEntry c => WasteOf c e.m
    | EdgeLabel.stackEvent a =>
        (∃ c, e.m = Move.tabToFound c ∧ e.c.pileOfTop c = some a) ∨
        (∃ c b, e.m = Move.tabToTab c b ∧ e.c.pileHolding c = some a) := by
  obtain ⟨h1, h2, h3⟩ := pair_move_character e
  cases hl : e.label with
  | draw => exact h1 hl
  | wasteEntry c => exact h2 c hl
  | stackEvent a => exact h3 a hl

/-! ## The draw successor (the successor discipline's first small step)

The count program's successor discipline wants each label to own
at most two successor classes; the ledger honestly records that the
`≤ 2` boundary is NOT yet cleanly characterized, so this chapter's
prime directive is prove-or-pin, never force.  The first small
step is the draw label's fragment, at the general member — the
smallest successor question the `TipEdge` world can ask.

### The interface recon (docs-first; committed as its own landing)

**(a) The candidate uniqueness route.**  A draw-labeled tip edge
commits `Move.draw` (`pair_move_character`'s first conjunct), so the
edge IS: one class member, its fired draw (the deterministic
`stepDraw`), and the landing's class closure.  Two draw-labeled
edges over one source class `C` read at class-mates `c₁ c₂` with
landings `w₁ w₂`; the disciplined statement
(`draw_successor_unique`) needs exactly `⟦w₁⟧ = ⟦w₂⟧` — the class
map induced by one fired draw is well-defined.  This is the
smaller step the user asked the program to find: not the umbrella's
per-label enumeration, but one label's class map, proved or pinned
at member grade.

**(b) The two roads to `⟦w₁⟧ = ⟦w₂⟧`, and the one that closes.**

* *The commutation-transport — the road this chapter takes, at the
  general grade, ungated.*  The draw is a field-local function: it
  reads and writes only the stock and the waste (the public play
  readers `recycle_allEmpty`/`_nil`/`_keep`, `dealStock_nil`,
  `dealStock_eq_of_ne_nil`, `dealUpTo_eq_take_drop`,
  `draw_unfold`), while every non-waste non-draw move — the whole
  board family `tabToFound`/`foundToTab`/`tabToTab` — guards and
  writes only the foundations and the piles (`nextUp`/`foundTop`
  read `found`; `pileOfTop`/`pileHolding`/`canPlace`/`below`/
  `fromCard` read `piles`).  So the draw commutes with every board
  leg definitionally — the `exch_step` pattern (`TwinExchangeBoth`)
  applied at the draw move, no `WF`, no shape analysis, only field
  disjointness — and a DRAW leg coincides with the pushed draw
  (the transposed position after a draw leg IS the original leg's
  landing).  A witnessed journey between class-mates therefore
  transports wholesale: running its move list at the drawn
  landing walks the same legs under the same guards (the draw
  keeps the board verbatim — `stepDraw_piles`/`_found`), each leg
  still reversible — its returning play contains no waste move,
  because a returning play cannot drop the cycle count
  (`cycleCount_step` runs never rise; `cycleCount_step_wasteToFound`/
  `_wasteToTab` drop strictly) — and the pushed journey lands the
  mate's own draw landing.  The transport is the A-session's "(A)
  is now a plain cite for up-to-sameCycle transports"
  (FARM_MEMORY, macro-game `b4f32e4`) made structural: no phase
  arithmetic at all, just field locality plus the counting that
  keeps journeys and their returning plays waste-free.
* *The phase-collapse — the road NOT taken, and why.*  One could
  try to prove class-mates phase-identical (`sameCycle` ⇒ same
  class) and reduce the two draws to one configuration.  The
  banked A-session finding is that phases are NOT mutually
  reachable at `drawStep = 1` — a full-stock state drains and the
  orbit never re-stocks it; the orbit misses the phase, and only
  the list-equality-of-`cycleOf` invariant survives — so the
  premise of a phase-collapse is false at the concrete census, and
  at general draw steps the §5.3 fragment proves its phase
  transports with plays in the waste anyway (the replay-engine
  program), not with class memberships.  The commutation-transport
  needs no collapse and pays for none: the pushed journey IS the
  class witness.

**(c) The precise statements this chapter attempts, at the
strongest provable grade.**

* `draw_landings_sameOrbit` — the member-grade core: two fired
  draws at class-mates have class-equal landings.  Ungated at its
  grade: no `WF`, no `drawStep` discipline, no `tipEdge_draw_shape`
  premise — the firing itself is the only hypothesis, carried as
  explicit witnesses.
* `draw_successor_unique` — the ideal, at full grade: two
  draw-labeled `TipEdge`s over one source class have equal
  targets.  Its premises derive (the character converts labels to
  draw commitments; the memberships give the mate relation); none
  are assumed.
* The constructive envelope, if and only if the core closes: the
  computable core `drawNext` (junk-safe at non-firing members),
  the class lift `drawNextQ` with `drawNextQ_mk` (the `datumOf`
  lift pattern; the soundness is the proven core, paid once), and
  the enumeration `tipEdge_draw_target` (a draw-labeled edge's
  target is `drawNextQ C`), which reads the uniqueness one level
  up.

**Where the banked transports live — the fragment boundary this
recon records.**  The dominance program's `cycleOf`/`sameCycle`
block (`Orig/Dominance.lean` §5.3, the draw-1 deck dominance)
publishes its two definitions but keeps its draw readers
(`draw_shape_plain`/`_base`, `draw_step_fires`, `draw_cycleOf`)
`private` and `drawStep = 1`-gated; the member-form successor
cannot cite them — and transpires to need none of them.  What the
general `TipEdge` world actually consumes sits entirely inside
this module's existing import closure, all public: the play
readers (`Orig/Play.lean`: recycle/deal readers, `draw_unfold`,
`State.run_cons`) — the draw as a deterministic field-local
function; the projection and counting rows
(`Orig/Irreversible.lean`: `setPile_*`/`setFound_*`/`putCard_*`/
`putRun_*` projections, `cycleCount_step`, the two strict
waste drops, `recycle_cycle`, `stepDraw_piles`/`_found`/
`_cycle`) — the draw as a board-preserving cycle-conserving
function, and the count mono that keeps journeys waste-free; and
Combine's witnessed setoid machinery (`ShufflePlayW`,
`Quotient.exact`, `Quotient.sound`) — journeys as inductive
objects and the class interface itself.  The small congruence
rows for the guard reads and the run-level counting mono land
here as private copies under the farm's private-isolation
convention (same shapes, same scripts, dedup at merge); the
dominance program keeps its own copies beside its §5.3 engine.
The draw reversibility rows (Phase's `draw_irreversible_*`,
Classify's in-phase and pass-base round trips) govern WHICH
draws are commitments — `tipEdge_draw_shape` already consumed
them once — and the uniqueness core does not need them again:
the edges carry their own commitments as data.

**The close, landed.** The member-grade transport kit and the two
closes are proved, green, sorry-free — the ideal `draw_successor_unique`
landed at full grade with its premises derived, never assumed:
the private kit (the guard congruences, the `setPile`/`putCard`/
`putRun` pile congruences, the field-determined draw `stepDraw_rel`,
the firing pair `stepDraw_pos_cycleCount`/`_of_pos_cycleCount`, the
counting mono and the waste-free-play rows
`run_ne_waste_of_return`/`reversibleAtW_isWaste_false`, the three
board squares with the step-square dispatch, the play push
`run_drawPush` and the journey push `ShufflePlayW_drawPush`),
then the member core `draw_landings_sameOrbit` and the ideal
`draw_successor_unique`, both audited
`[propext, Quot.sound]` (the class interface is `Quotient.sound`'s
business; nothing new enters).  The envelope landed with it at
exactly that grade: `sameOrbit_cycleCount` (mates share the cycle
count — a class draws together or not at all), the junk-safe
computable core `drawNext`, the class lift `drawNextQ` in the
`datumOf` pattern (`drawNext_sound` is its paid-once soundness —
the fired case is the proven core, the non-firing case is the
mate relation itself; both case splits are constructive `Option`
dichotomies), the definitional computation rule `drawNextQ_mk`,
and the enumeration `tipEdge_draw_target` — every draw-labeled
edge over a class has exactly one target, the class's
`drawNextQ`.  This chapter's honest boundary: the `≤
2`-per-label umbrella itself remains open — this closes the draw
label's one share at the general member, proved, computable, and
audited; the waste/tab shares are the successor program's next
small steps to find.
-/

/-! ### The transport kit (private copies; dedup-marked)

The guard congruences (the board reads are field reads), the
field-determined draw, and the run-level counting mono — the
farm's private-isolation convention: same shapes, same scripts
as the dominance program's copies beside its §5.3 engine and the
twin-exchange chapter's copies (they dedup at merge). -/

/-- The pile-top read is a piles-field read. -/
private theorem topOf_congr {u v : State} (a : Anchor) (h : u.piles = v.piles) :
    u.topOf a = v.topOf a := by
  show (u.piles a).top = (v.piles a).top
  exact congrArg Pile.top (congrFun h a)

/-- The top-search is a piles-field read. -/
private theorem pileOfTop_congr {u v : State} (z : Card) (h : u.piles = v.piles) :
    u.pileOfTop z = v.pileOfTop z := by
  show firstWhere (fun a => decide (u.topOf a = some z)) Anchor.all = _
  exact firstWhere_congr (p := fun a => decide (u.topOf a = some z))
    (q := fun a => decide (v.topOf a = some z)) (fun a => by rw [topOf_congr a h])
    (l := Anchor.all)

/-- The placement guard is a piles-field read. -/
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

/-- The foundation-next read is a found-field read. -/
private theorem nextUp_congr {u v : State} (c : Card) (h : u.found = v.found) :
    u.nextUp c = v.nextUp c :=
  congrArg (fun (f : Suit → List Card) => decide (c.rank.toIdx = (f c.suit).length)) h

/-- The foundation-top read is a found-field read. -/
private theorem foundTop_congr {u v : State} (s : Suit) (h : u.found = v.found) :
    u.foundTop s = v.foundTop s := by
  simp only [State.foundTop]
  rw [congrFun h s]

/-- A `setPile` at equal piles boards agrees everywhere. -/
private theorem setPile_piles_congr {u v : State} (a : Anchor) (p : Pile)
    (h : u.piles = v.piles) : (u.setPile a p).piles = (v.setPile a p).piles := by
  rw [setPile_piles, setPile_piles, h]

/-- A `putCard` at equal piles boards agrees everywhere (the
placement walk reads only the piles). -/
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

/-- A `putRun` at equal piles boards agrees everywhere. -/
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

/-- The draw is field-determined: two states that agree on stock,
waste and draw step draw to outcomes that keep their own piles,
found and draw step and share the dealt stock and waste.  A
dedup-marked port of the twin-exchange chapter's private copy
(same shape, same script). -/
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

/-- The draw keeps the draw step. -/
private theorem stepDraw_drawStep {x u : State} (hd : x.stepDraw = some u) :
    u.drawStep = x.drawStep := by
  obtain ⟨r, hrec, -, hshape⟩ := draw_unfold hd
  have h1 : u.drawStep = r.drawStep := by rw [hshape]
  rw [h1, ← hrec]
  cases hs : x.stock with
  | nil => cases hw : x.waste <;> simp only [State.recycle, hs, hw]
  | cons c cs => simp only [State.recycle, hs]

/-- A fired draw certifies a nonempty cycle. -/
private theorem stepDraw_pos_cycleCount {x u : State} (hd : x.stepDraw = some u) :
    0 < cycleCount x := by
  obtain ⟨r, hrec, hrne, -⟩ := draw_unfold hd
  have h1 : cycleCount r = cycleCount x := by rw [← hrec]; exact recycle_cycle x
  rw [← h1]
  obtain ⟨c, cs, hcon⟩ := list_cons_of_ne_nil hrne
  rw [show cycleCount r = r.stock.length + r.waste.length from rfl, hcon,
    List.length_cons]
  omega

/-- A nonempty cycle fires the draw — the unconditioned base: no
draw-step discipline, no shape premise, `dealStock` reads only
the zone. -/
private theorem stepDraw_of_pos_cycleCount {x : State}
    (h : 0 < cycleCount x) : ∃ u, x.stepDraw = some u := by
  cases hs : x.stock with
  | cons c cs =>
      exact ⟨_, by
        rw [show x.stepDraw = State.dealStock (State.recycle x) from rfl,
          show State.recycle x = x from recycle_keep x (by rw [hs]; exact fun hc => absurd hc (by simp)),
          dealStock_eq_of_ne_nil x (by rw [hs]; exact fun hc => absurd hc (by simp)), hs]⟩
  | nil =>
      cases hw : x.waste with
      | nil =>
          exact absurd h (by rw [show cycleCount x = x.stock.length + x.waste.length from rfl, hs, hw]; simp)
      | cons w ws =>
          have hne : x.waste ≠ [] := by rw [hw]; exact fun hc => absurd hc (by simp)
          have hrev : (w :: ws).reverse ≠ [] := by
            intro hc
            have hl := congrArg List.length hc
            rw [List.length_reverse, List.length_nil] at hl
            simp at hl
          exact ⟨_, by
            rw [show x.stepDraw = State.dealStock (State.recycle x) from rfl,
              show State.recycle x = { x with stock := x.waste.reverse, waste := ([] : List Card) } from recycle_nil x hs hne,
              dealStock_eq_of_ne_nil _ (show (({ x with stock := x.waste.reverse, waste := ([] : List Card) } : State)).stock ≠ [] from by rw [hw]; exact hrev)]⟩

/-- One step of a run, in equation form. -/
private theorem run_step_cons' {st s₁ : State} {m : Move} {rest : List Move}
    (hm : State.step st m = some s₁) : st.run (m :: rest) = s₁.run rest := by
  show (match State.step st m with
         | some s' => s'.run rest
         | none => none) = _
  rw [hm]

/-! ### The counting mono (the waste-free-plays calculus) -/

/-- The two moves that spend a waste card (farm copy of Phase's
private discriminator; dedup at merge). -/
private def isWasteMove (m : Move) : Bool :=
  match m with
  | .wasteToFound _ => true
  | .wasteToTab _ _ => true
  | _ => false

/-- The cycle count never rises along a play (the per-step row is
`cycleCount_step`). -/
private theorem run_cycleCount_le : ∀ {play : List Move} {x w : State},
    x.run play = some w → cycleCount w ≤ cycleCount x := by
  intro play
  induction play with
  | nil =>
      intro x w h
      injection h with hx
      subst hx
      exact Nat.le_refl _
  | cons m rest ih =>
      intro x w hrun
      obtain ⟨s₁, hm, hrs⟩ := State.run_cons hrun
      have h1 := ih hrs
      have h2 := cycleCount_step hm
      omega

/-- A play that spends a waste card strictly drops the cycle
count (the per-step strict rows are `cycleCount_step_wasteToFound`
and `cycleCount_step_wasteToTab`). -/
private theorem run_cycleCount_lt : ∀ {play : List Move} {x w : State},
    x.run play = some w → (∃ m ∈ play, isWasteMove m = true) →
    cycleCount w < cycleCount x := by
  intro play
  induction play with
  | nil =>
      intro x w _ hmem
      obtain ⟨m, hm, -⟩ := hmem
      exact absurd hm (by simp)
  | cons m rest ih =>
      intro x w hrun hmem
      obtain ⟨s₁, hm, hrs⟩ := State.run_cons hrun
      by_cases hmv : isWasteMove m = true
      · have hlt : cycleCount s₁ < cycleCount x := by
          cases m with
          | draw => simp [isWasteMove] at hmv
          | wasteToFound c =>
              have := cycleCount_step_wasteToFound hm
              omega
          | wasteToTab c b =>
              have := cycleCount_step_wasteToTab hm
              omega
          | tabToFound c => simp [isWasteMove] at hmv
          | foundToTab c b => simp [isWasteMove] at hmv
          | tabToTab c b => simp [isWasteMove] at hmv
        have hle := run_cycleCount_le hrs
        omega
      · obtain ⟨m', hm', hmis⟩ := hmem
        rcases List.mem_cons.1 hm' with heq | hmem2
        · exact absurd (heq ▸ hmis) hmv
        · have hlt := ih hrs ⟨m', hmem2, hmis⟩
          have hle := cycleCount_step hm
          omega

/-- Every non-draw, non-waste leg conserves the cycle count
(draws conserve it by `stepDraw_cycle`; the board writes keep the
zone by the projection rows). -/
private theorem step_cycleCount_of_ne_waste {x s₁ : State} {m : Move}
    (hstep : State.step x m = some s₁) (hmv : isWasteMove m = false) :
    cycleCount s₁ = cycleCount x := by
  cases m with
  | draw => exact stepDraw_cycle hstep
  | wasteToFound c => simp [isWasteMove] at hmv
  | wasteToTab c b => simp [isWasteMove] at hmv
  | tabToFound c =>
      obtain ⟨-, a, -, hs⟩ := step_tabToFound_inv hstep
      rw [hs]
      exact cycleCount_eq_of_stock_waste rfl rfl
  | foundToTab c b =>
      obtain ⟨-, -, -, -, hs⟩ := step_foundToTab_inv hstep
      rw [hs]
      exact cycleCount_eq_of_stock_waste
        (by rw [putCard_stock]; exact setFound_stock _ _ _)
        (by rw [putCard_waste]; exact setFound_waste _ _ _)
  | tabToTab c b =>
      obtain ⟨a, hh, hcp, hfr, hs⟩ := step_tabToTab_inv hstep
      rw [hs]
      exact cycleCount_eq_of_stock_waste
        (by rw [putRun_stock]; exact setPile_stock _ _ _)
        (by rw [putRun_waste]; exact setPile_waste _ _ _)

/-- A play that returns to a count-conserved origin never spends
the waste. -/
private theorem run_ne_waste_of_return {x y : State} {play : List Move}
    (hrun : x.run play = some y) (hcount : cycleCount y = cycleCount x) :
    ∀ m ∈ play, isWasteMove m = false := by
  intro m hm
  cases hmv : isWasteMove m with
  | false => rfl
  | true =>
      have hlt := run_cycleCount_lt hrun ⟨m, hm, hmv⟩
      rw [hcount] at hlt
      exact absurd hlt (by simp)

/-- No witness reversible leg spends the waste: the landing would
sit strictly below the origin's cycle count and no play ever
rises. -/
private theorem reversibleAtW_isWaste_false {x : State} {m : Move}
    (hr : reversibleAtW x m) : isWasteMove m = false := by
  obtain ⟨s₁, play, hstep, hrun⟩ := hr
  cases hmv : isWasteMove m with
  | false => rfl
  | true =>
      exfalso
      cases m with
      | draw => simp [isWasteMove] at hmv
      | wasteToFound c =>
          have h1 := cycleCount_step_wasteToFound hstep
          have h2 := run_cycleCount_le hrun
          omega
      | wasteToTab c b =>
          have h1 := cycleCount_step_wasteToTab hstep
          have h2 := run_cycleCount_le hrun
          omega
      | tabToFound c => simp [isWasteMove] at hmv
      | foundToTab c b => simp [isWasteMove] at hmv
      | tabToTab c b => simp [isWasteMove] at hmv

/-! ### The three board squares (the draw commutes with every board leg)

The `exch_step` pattern at the draw move, member grade, ungated: a
fired draw at `st` and a fired board move at `st` compose both ways
onto the same state — the board move at the drawn landing IS the
draw at the moved board.  The guards read only the board (the
congruence rows), the writes touch only the board (the projection
rows), and the draw is field-determined (`stepDraw_rel`); no `WF`,
no shape analysis, no draw-step discipline. -/

/-- **Board square, `tabToFound` leg.** -/
private theorem square_tabToFound {st r w : State} {c : Card}
    (hm : State.step st (Move.tabToFound c) = some r)
    (hd : st.stepDraw = some w) :
    ∃ r', w.step (Move.tabToFound c) = some r' ∧ r.stepDraw = some r' := by
  obtain ⟨hnext, a, hp, hs⟩ := step_tabToFound_inv hm
  have hpil : w.piles = st.piles := stepDraw_piles hd
  have hfnd : w.found = st.found := stepDraw_found hd
  have hz1 : r.stock = st.stock := by rw [hs]; rfl
  have hz2 : r.waste = st.waste := by rw [hs]; rfl
  have hz3 : r.drawStep = st.drawStep := by rw [hs]; rfl
  obtain ⟨z, hzstep, hzp, -, hzf, -, hzds, -, hzs, hzw⟩ := stepDraw_rel hz1 hz2 hz3 hd
  have hzd' : z.drawStep = w.drawStep := by
    rw [hzds, hz3, ← stepDraw_drawStep hd]
  have hwf1 : w.step (Move.tabToFound c) = some
      { w.setFound c.suit (w.found c.suit ++ [c]) with
        piles := fun a' =>
          if a' = a then Pile.afterRunRemoved (w.piles a) (chop (w.piles a).faceUp)
          else w.piles a' } := by
    have g1 : w.nextUp c = st.nextUp c := nextUp_congr c hfnd
    have g2 : w.pileOfTop c = st.pileOfTop c := pileOfTop_congr c hpil
    simp only [State.step, g1, hnext, g2, hp]
    rfl
  refine ⟨z, hwf1.trans (congrArg Option.some ?_), hzstep⟩
  apply State.ext
  · show { w.setFound c.suit (w.found c.suit ++ [c]) with
      piles := fun a' =>
        if a' = a then Pile.afterRunRemoved (w.piles a) (chop (w.piles a).faceUp)
        else w.piles a' }.found = z.found
    rw [show z.found = r.found from hzf, hs]
    simp only [hfnd, State.setFound]
  · show { w.setFound c.suit (w.found c.suit ++ [c]) with
      piles := fun a' =>
        if a' = a then Pile.afterRunRemoved (w.piles a) (chop (w.piles a).faceUp)
        else w.piles a' }.piles = z.piles
    rw [show z.piles = r.piles from hzp, hs]
    simp only [hpil]
  · rw [show z.stock = w.stock from hzs]; rfl
  · rw [show z.waste = w.waste from hzw]; rfl
  · rw [hzd']; rfl

/-- **Board square, `foundToTab` leg.** -/
private theorem square_foundToTab {st r w : State} {c : Card} {b : Base}
    (hm : State.step st (Move.foundToTab c b) = some r)
    (hd : st.stepDraw = some w) :
    ∃ r', w.step (Move.foundToTab c b) = some r' ∧ r.stepDraw = some r' := by
  obtain ⟨c₀, htop0, hceq, hcp, hs⟩ := step_foundToTab_inv hm
  have hft : st.foundTop c.suit = some c := by rw [htop0, hceq]
  have hpil : w.piles = st.piles := stepDraw_piles hd
  have hfnd : w.found = st.found := stepDraw_found hd
  have hz1 : r.stock = st.stock := by rw [hs, putCard_stock, setFound_stock]
  have hz2 : r.waste = st.waste := by rw [hs, putCard_waste, setFound_waste]
  have hz3 : r.drawStep = st.drawStep := by rw [hs, putCard_drawStep, setFound_drawStep]
  obtain ⟨z, hzstep, hzp, -, hzf, -, hzds, -, hzs, hzw⟩ := stepDraw_rel hz1 hz2 hz3 hd
  have hzd' : z.drawStep = w.drawStep := by
    rw [hzds, hz3, ← stepDraw_drawStep hd]
  have hC : (w.setFound c.suit (chop (w.found c.suit))).piles
      = (st.setFound c.suit (chop (st.found c.suit))).piles := by
    rw [setFound_piles, setFound_piles, hpil]
  have hCcp : ((w.setFound c.suit (chop (w.found c.suit))).putCard c b).piles
      = ((st.setFound c.suit (chop (st.found c.suit))).putCard c b).piles :=
    putCard_piles_congr c b hC
  have hCf : (w.setFound c.suit (chop (w.found c.suit))).found
      = (st.setFound c.suit (chop (st.found c.suit))).found := by
    simp only [State.setFound, hfnd]
  have hwf1 : w.step (Move.foundToTab c b) = some
      ((w.setFound c.suit (chop (w.found c.suit))).putCard c b) := by
    have g1 : w.foundTop c.suit = st.foundTop c.suit := foundTop_congr c.suit hfnd
    have g2 : w.canPlace c b = st.canPlace c b := canPlace_congr c b hpil
    simp only [State.step, g1, hft, g2, hcp]
    rfl
  refine ⟨z, hwf1.trans (congrArg Option.some ?_), hzstep⟩
  apply State.ext
  · show ((w.setFound c.suit (chop (w.found c.suit))).putCard c b).found = z.found
    rw [putCard_found, hCf, show z.found = r.found from hzf, hs, putCard_found]
  · show ((w.setFound c.suit (chop (w.found c.suit))).putCard c b).piles = z.piles
    rw [hCcp, show z.piles = r.piles from hzp, hs]
  · rw [putCard_stock, setFound_stock, show z.stock = w.stock from hzs]
  · rw [putCard_waste, setFound_waste, show z.waste = w.waste from hzw]
  · rw [putCard_drawStep, setFound_drawStep, hzd']

/-- **Board square, `tabToTab` leg.** -/
private theorem square_tabToTab {st r w : State} {c : Card} {b : Base}
    (hm : State.step st (Move.tabToTab c b) = some r)
    (hd : st.stepDraw = some w) :
    ∃ r', w.step (Move.tabToTab c b) = some r' ∧ r.stepDraw = some r' := by
  obtain ⟨a, hh, hcp, hfr, hs⟩ := step_tabToTab_inv hm
  have hpil : w.piles = st.piles := stepDraw_piles hd
  have hfnd : w.found = st.found := stepDraw_found hd
  have hz1 : r.stock = st.stock := by rw [hs, putRun_stock, setPile_stock]
  have hz2 : r.waste = st.waste := by rw [hs, putRun_waste, setPile_waste]
  have hz3 : r.drawStep = st.drawStep := by rw [hs, putRun_drawStep, setPile_drawStep]
  obtain ⟨z, hzstep, hzp, -, hzf, -, hzds, -, hzs, hzw⟩ := stepDraw_rel hz1 hz2 hz3 hd
  have hzd' : z.drawStep = w.drawStep := by
    rw [hzds, hz3, ← stepDraw_drawStep hd]
  have hPpa : w.piles a = st.piles a := congrFun hpil a
  have hrrp : Pile.afterRunRemoved (w.piles a) (below c (w.piles a).faceUp)
      = Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp) := by
    rw [hPpa]
  have hfrun : fromCard c (w.piles a).faceUp = fromCard c (st.piles a).faceUp :=
    congrArg (fromCard c) (congrArg Pile.faceUp hPpa)
  have hC : (w.setPile a
        (Pile.afterRunRemoved (w.piles a) (below c (w.piles a).faceUp))).piles
      = (st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles := by
    rw [setPile_piles, setPile_piles, hpil]
  have hCcp : ((w.setPile a
        (Pile.afterRunRemoved (w.piles a) (below c (w.piles a).faceUp))).putRun
        (fromCard c (st.piles a).faceUp) b).piles
      = ((st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
        (fromCard c (st.piles a).faceUp) b).piles :=
    putRun_piles_congr _ _ hC
  have hwf1 : w.step (Move.tabToTab c b) = some
      ((w.setPile a
        (Pile.afterRunRemoved (w.piles a) (below c (w.piles a).faceUp))).putRun
        (fromCard c (w.piles a).faceUp) b) := by
    have g1 : w.pileHolding c = st.pileHolding c := pileHolding_congr hpil
    have g2 : w.canPlace c b = st.canPlace c b := canPlace_congr c b hpil
    simp only [State.step, g1, hh, g2, hcp]
    cases hwfr : fromCard c (w.piles a).faceUp with
    | nil =>
        rw [hfrun] at hwfr
        exact absurd hwfr hfr
    | cons x xs =>
        rfl
  refine ⟨z, hwf1.trans (congrArg Option.some ?_), hzstep⟩
  apply State.ext
  · show ((w.setPile a
        (Pile.afterRunRemoved (w.piles a) (below c (w.piles a).faceUp))).putRun
        (fromCard c (w.piles a).faceUp) b).found = z.found
    rw [putRun_found, setPile_found, hfnd, show z.found = r.found from hzf, hs,
      putRun_found, setPile_found]
  · show ((w.setPile a
        (Pile.afterRunRemoved (w.piles a) (below c (w.piles a).faceUp))).putRun
        (fromCard c (w.piles a).faceUp) b).piles = z.piles
    rw [hfrun, hCcp, show z.piles = r.piles from hzp, hs]
  · rw [putRun_stock, setPile_stock, show z.stock = w.stock from hzs]
  · rw [putRun_waste, setPile_waste, show z.waste = w.waste from hzw]
  · rw [putRun_drawStep, setPile_drawStep, hzd']

/-- **The step-square, dispatched:** any waste-free non-draw leg
transports across a fired draw. -/
private theorem step_square {st r w : State} {m : Move}
    (hm : State.step st m = some r) (hmv : isWasteMove m = false)
    (hmd : m ≠ Move.draw)
    (hd : st.stepDraw = some w) :
    ∃ r', w.step m = some r' ∧ r.stepDraw = some r' := by
  cases m with
  | draw => exact absurd rfl hmd
  | wasteToFound c => simp [isWasteMove] at hmv
  | wasteToTab c b => simp [isWasteMove] at hmv
  | tabToFound c => exact square_tabToFound hm hd
  | foundToTab c b => exact square_foundToTab hm hd
  | tabToTab c b => exact square_tabToTab hm hd

/-! ### The push core -/

/-- The draw pushes through any waste-free play: running the play
at the drawn landing lands the draw of the play's own landing.
Board legs cross the square; a draw leg COINCIDES with the pushed
draw (the transposed prefix IS the original prefix's landing). -/
private theorem run_drawPush : ∀ (play : List Move) (x u y : State),
    x.stepDraw = some u → x.run play = some y →
      (∀ m ∈ play, isWasteMove m = false) →
      ∃ u', u.run play = some u' ∧ y.stepDraw = some u' := by
  intro play
  induction play with
  | nil =>
      intro x u y hd hrun hfree
      injection hrun with hx
      rw [hx] at hd
      exact ⟨u, rfl, hd⟩
  | cons m rest ih =>
      intro x u y hd hrun hwfree
      obtain ⟨s₁, hmst, hrest⟩ := State.run_cons hrun
      have hrfree : ∀ m' ∈ rest, isWasteMove m' = false := by
        intro m' hm'
        exact hwfree m' (List.mem_cons_of_mem _ hm')
      cases m with
      | draw =>
          have hueq : x.stepDraw = some s₁ := hmst
          have hs₁u : s₁ = u := Option.some.inj (hueq.symm.trans hd)
          have hcu := stepDraw_cycle hd
          have hpos := stepDraw_pos_cycleCount hd
          obtain ⟨u₂, hu₂⟩ := stepDraw_of_pos_cycleCount (by rw [hcu]; exact hpos)
          have hs₁u₂ : s₁.stepDraw = some u₂ := by rw [hs₁u]; exact hu₂
          obtain ⟨u'', hrun', hfire'⟩ := ih s₁ u₂ y hs₁u₂ hrest hrfree
          refine ⟨u'', ?_, hfire'⟩
          rw [show u.run (Move.draw :: rest) = u₂.run rest from
              run_step_cons' (show State.step u Move.draw = some u₂ from hu₂)]
          exact hrun'
      | wasteToFound c =>
          have : isWasteMove (Move.wasteToFound c) = false := hwfree _ (by simp)
          simp [isWasteMove] at this
      | wasteToTab c b =>
          have : isWasteMove (Move.wasteToTab c b) = false := hwfree _ (by simp)
          simp [isWasteMove] at this
      | tabToFound c =>
          obtain ⟨r', hwstep, hrfire⟩ :=
            step_square hmst (hwfree _ (by simp)) (by simp) hd
          obtain ⟨u'', hrun', hfire'⟩ := ih s₁ r' y hrfire hrest hrfree
          refine ⟨u'', ?_, hfire'⟩
          rw [show u.run (Move.tabToFound c :: rest) = r'.run rest from
              run_step_cons' hwstep]
          exact hrun'
      | foundToTab c b =>
          obtain ⟨r', hwstep, hrfire⟩ :=
            step_square hmst (hwfree _ (by simp)) (by simp) hd
          obtain ⟨u'', hrun', hfire'⟩ := ih s₁ r' y hrfire hrest hrfree
          refine ⟨u'', ?_, hfire'⟩
          rw [show u.run (Move.foundToTab c b :: rest) = r'.run rest from
              run_step_cons' hwstep]
          exact hrun'
      | tabToTab c b =>
          obtain ⟨r', hwstep, hrfire⟩ :=
            step_square hmst (hwfree _ (by simp)) (by simp) hd
          obtain ⟨u'', hrun', hfire'⟩ := ih s₁ r' y hrfire hrest hrfree
          refine ⟨u'', ?_, hfire'⟩
          rw [show u.run (Move.tabToTab c b :: rest) = r'.run rest from
              run_step_cons' hwstep]
          exact hrun'

/-- The witness journey pushes: a witnessed reversible journey at a
drawing member reruns wholesale at the drawn landing — same move
list, leg by leg still witness-reversible (each leg's returning
play is waste-free, so it pushes too, and lands the pushed source)
— and the pushed journey lands the mate's own draw landing. -/
private theorem ShufflePlayW_drawPush {x y : State} {play : List Move}
    (h : ShufflePlayW x play y) :
    ∀ {u : State}, x.stepDraw = some u →
      ∃ u', ShufflePlayW u play u' ∧ y.stepDraw = some u' := by
  induction h with
  | nil s =>
      intro u hd
      exact ⟨u, ShufflePlayW.nil u, hd⟩
  | @cons x₀ m s₁ rest y₀ hw hstep hrest ih =>
      intro u hd
      have hmfree := reversibleAtW_isWaste_false hw
      obtain ⟨s₁w, hplay, hstepleg, hrunleg⟩ := hw
      have hs₁us : s₁w = s₁ := Option.some.inj (hstepleg.symm.trans hstep)
      rw [hs₁us] at hstepleg hrunleg
      have hlecount : cycleCount s₁ = cycleCount x₀ :=
        step_cycleCount_of_ne_waste (show State.step x₀ m = some s₁ from hstepleg) hmfree
      have hrevcount : cycleCount x₀ = cycleCount s₁ := hlecount.symm
      cases m with
      | draw =>
          have hs₁u : s₁ = u := Option.some.inj
            ((show x₀.stepDraw = some s₁ from hstep).symm.trans hd)
          have hcu := stepDraw_cycle hd
          have hpos := stepDraw_pos_cycleCount hd
          obtain ⟨u₂, hu₂⟩ := stepDraw_of_pos_cycleCount (by rw [hcu]; exact hpos)
          have hs₁u₂ : s₁.stepDraw = some u₂ := by rw [hs₁u]; exact hu₂
          have hπfree := run_ne_waste_of_return hrunleg hrevcount
          obtain ⟨p', hp'run, hp'fire⟩ :=
            run_drawPush hplay s₁ u₂ x₀ hs₁u₂ hrunleg hπfree
          have hp'u : p' = u := Option.some.inj (hp'fire.symm.trans hd)
          rw [hp'u] at hp'run
          have hrevu : reversibleAtW u Move.draw :=
            ⟨u₂, hplay, (show State.step u Move.draw = some u₂ from hu₂), hp'run⟩
          obtain ⟨u'', hsh, hyfire⟩ := ih hs₁u₂
          exact ⟨u'', ShufflePlayW.cons hrevu hu₂ hsh, hyfire⟩
      | wasteToFound c => simp [isWasteMove] at hmfree
      | wasteToTab c b => simp [isWasteMove] at hmfree
      | tabToFound c =>
          obtain ⟨r', hwr', hrfire⟩ := step_square hstepleg hmfree (by simp) hd
          have hπfree := run_ne_waste_of_return hrunleg hrevcount
          obtain ⟨p', hp'run, hp'fire⟩ :=
            run_drawPush hplay s₁ r' x₀ hrfire hrunleg hπfree
          have hp'u : p' = u := Option.some.inj (hp'fire.symm.trans hd)
          rw [hp'u] at hp'run
          have hrevu : reversibleAtW u (Move.tabToFound c) :=
            ⟨r', hplay, hwr', hp'run⟩
          obtain ⟨u'', hsh, hyfire⟩ := ih hrfire
          exact ⟨u'', ShufflePlayW.cons hrevu hwr' hsh, hyfire⟩
      | foundToTab c b =>
          obtain ⟨r', hwr', hrfire⟩ := step_square hstepleg hmfree (by simp) hd
          have hπfree := run_ne_waste_of_return hrunleg hrevcount
          obtain ⟨p', hp'run, hp'fire⟩ :=
            run_drawPush hplay s₁ r' x₀ hrfire hrunleg hπfree
          have hp'u : p' = u := Option.some.inj (hp'fire.symm.trans hd)
          rw [hp'u] at hp'run
          have hrevu : reversibleAtW u (Move.foundToTab c b) :=
            ⟨r', hplay, hwr', hp'run⟩
          obtain ⟨u'', hsh, hyfire⟩ := ih hrfire
          exact ⟨u'', ShufflePlayW.cons hrevu hwr' hsh, hyfire⟩
      | tabToTab c b =>
          obtain ⟨r', hwr', hrfire⟩ := step_square hstepleg hmfree (by simp) hd
          have hπfree := run_ne_waste_of_return hrunleg hrevcount
          obtain ⟨p', hp'run, hp'fire⟩ :=
            run_drawPush hplay s₁ r' x₀ hrfire hrunleg hπfree
          have hp'u : p' = u := Option.some.inj (hp'fire.symm.trans hd)
          rw [hp'u] at hp'run
          have hrevu : reversibleAtW u (Move.tabToTab c b) :=
            ⟨r', hplay, hwr', hp'run⟩
          obtain ⟨u'', hsh, hyfire⟩ := ih hrfire
          exact ⟨u'', ShufflePlayW.cons hrevu hwr' hsh, hyfire⟩

/-! ### The class close -/

/-- **The draw class map is well-defined (the member core).**  Two
fired draws at class-mates land class-mates: the witnessed journeys
between the members push across either draw, so both pushed
journeys witness the landing pair both ways.  Ungated: firing is
carried as explicit witnesses, nothing else is assumed. -/
theorem draw_landings_sameOrbit {c₁ w₁ c₂ w₂ : State}
    (hmate : (⟦c₁⟧ : SameOrbit) = ⟦c₂⟧)
    (hd₁ : c₁.stepDraw = some w₁) (hd₂ : c₂.stepDraw = some w₂) :
    (⟦w₁⟧ : SameOrbit) = ⟦w₂⟧ := by
  rcases Quotient.exact hmate with ⟨σ, hσ, τ, hτ⟩
  obtain ⟨u₁, hsh₁, hu₁fire⟩ := ShufflePlayW_drawPush hτ hd₁
  have hu₁ : u₁ = w₂ := Option.some.inj (hu₁fire.symm.trans hd₂)
  rw [hu₁] at hsh₁
  obtain ⟨u₂, hsh₂, hu₂fire⟩ := ShufflePlayW_drawPush hσ hd₂
  have hu₂ : u₂ = w₁ := Option.some.inj (hu₂fire.symm.trans hd₁)
  rw [hu₂] at hsh₂
  exact Quotient.sound ⟨σ, hsh₂, τ, hsh₁⟩

/-- **The draw-label successor is unique (the ideal, landed at
full grade).**  Two draw-labeled tip edges over one source class
have the same target: the draw induces a well-defined class map,
which is the draw label's share of the `≤ 2`-per-label umbrella.
The premises derive — the character converts the labels into
commitments, the memberships give the mate relation — none are
assumed. -/
theorem draw_successor_unique {C D₁ D₂ : SameOrbit}
    (e₁ : TipEdge C D₁) (hd₁ : e₁.label = EdgeLabel.draw)
    (e₂ : TipEdge C D₂) (hd₂ : e₂.label = EdgeLabel.draw) :
    D₁ = D₂ := by
  have md₁ : e₁.m = Move.draw := (pair_move_character e₁).1 hd₁
  have md₂ : e₂.m = Move.draw := (pair_move_character e₂).1 hd₂
  have fire₁ : e₁.c.stepDraw = some e₁.w := by
    have h := e₁.land
    rw [md₁] at h
    exact (show e₁.c.stepDraw = State.step e₁.c Move.draw from rfl).symm.trans h
  have fire₂ : e₂.c.stepDraw = some e₂.w := by
    have h := e₂.land
    rw [md₂] at h
    exact (show e₂.c.stepDraw = State.step e₂.c Move.draw from rfl).symm.trans h
  have hmate : (⟦e₁.c⟧ : SameOrbit) = ⟦e₂.c⟧ :=
    e₁.hmem.trans e₂.hmem.symm
  exact e₁.cl.symm.trans
    ((draw_landings_sameOrbit hmate fire₁ fire₂).trans e₂.cl)

/-! ### The constructive envelope (the close is landed, so this
lands with it, at exactly the core's grade)

The computable core is junk-safe: at a non-firing member it is
the identity, and firing is a class invariant (mates conserve the
cycle count, so a class draws together or not at all) — the two
case splits of the lift's soundness are constructive `Option`
dichotomies, no `Classical.choice` anywhere.  The lift itself is
the `datumOf` pattern: the soundness is the proven core, paid
once. -/

/-- A witnessed journey conserves the cycle count (every leg is
waste-free by `reversibleAtW_isWaste_false`, and waste-free legs
conserve exactly). -/
private theorem ShufflePlayW_cycleCount {x y : State} :
    ∀ {play : List Move}, ShufflePlayW x play y →
      cycleCount x = cycleCount y := by
  intro play h
  induction h with
  | nil s => rfl
  | @cons x₀ m s₁ rest y₀ hw hstep hrest ih =>
      have h1 := step_cycleCount_of_ne_waste hstep (reversibleAtW_isWaste_false hw)
      omega

/-- **Class-mates share the cycle count** (the firing invariance
of the class: a macro class draws together or not at all). -/
theorem sameOrbit_cycleCount {x y : State} (h : sameOrbitSetoid.r x y) :
    cycleCount x = cycleCount y := by
  obtain ⟨σ, hσ, -⟩ := h
  exact (ShufflePlayW_cycleCount (y := x) hσ).symm

/-- **The computable core**: the draw's member successor, junk-safe
at non-firing members (the identity there). -/
def drawNext (u : State) : State :=
  match u.stepDraw with
  | some w => w
  | none => u

/-- **The lift's soundness**: the junk-safe core is a class map —
mates fire together (the count is a class invariant) and their
fired draws land class-mates by the proven core; at non-firing
mates the core is the identity and the classes are the mates'
own. -/
theorem drawNext_sound {x y : State} (h : sameOrbitSetoid.r x y) :
    (⟦drawNext x⟧ : SameOrbit) = ⟦drawNext y⟧ := by
  have hcount : cycleCount x = cycleCount y := sameOrbit_cycleCount h
  cases hx : x.stepDraw with
  | none =>
      rcases Nat.eq_zero_or_pos (cycleCount x) with h0 | hpos
      · cases hy : y.stepDraw with
        | none =>
            have hdx : drawNext x = x := by simp only [drawNext, hx]
            have hdy : drawNext y = y := by simp only [drawNext, hy]
            rw [hdx, hdy]
            exact Quotient.sound h
        | some w =>
            exfalso
            have hypos := stepDraw_pos_cycleCount (u := w) hy
            have hcy : cycleCount y = 0 := by rw [← hcount]; exact h0
            omega
      · exfalso
        obtain ⟨u, hu⟩ := stepDraw_of_pos_cycleCount hpos
        rw [hx] at hu
        exact absurd hu (by simp)
  | some w₁ =>
      have hxpos := stepDraw_pos_cycleCount (u := w₁) hx
      have hyc : 0 < cycleCount y := by rw [← hcount]; exact hxpos
      obtain ⟨w₂, hy⟩ := stepDraw_of_pos_cycleCount hyc
      have hdx : drawNext x = w₁ := by simp only [drawNext, hx]
      have hdy : drawNext y = w₂ := by simp only [drawNext, hy]
      rw [hdx, hdy]
      exact draw_landings_sameOrbit (Quotient.sound h) hx hy

/-- **The draw successor as a class map**: the `datumOf` lift
pattern — a `Quotient.lift` whose soundness is exactly the proven
core (`drawNext_sound`: the fired case is `draw_landings_sameOrbit`,
the non-firing case is the mate relation itself). -/
def drawNextQ : SameOrbit → SameOrbit :=
  Quotient.lift (fun u => (⟦drawNext u⟧ : SameOrbit))
    (fun {_ _} h => drawNext_sound h)

/-- The computation rule: a class's draw successor reads through
any member (definitionally — the ordinary lift equation). -/
theorem drawNextQ_mk (u : State) :
    drawNextQ (⟦u⟧ : SameOrbit) = ⟦drawNext u⟧ := rfl

/-- **The draw label's enumeration**: every draw-labeled tip edge
over a source class has exactly one target — the class's
`drawNextQ`.  With `draw_successor_unique` this reads the
successor discipline's draw share one level up: the label's
successor is the class map, unique and computable. -/
theorem tipEdge_draw_target {C D : SameOrbit} (e : TipEdge C D)
    (h : e.label = EdgeLabel.draw) : D = drawNextQ C := by
  have md : e.m = Move.draw := (pair_move_character e).1 h
  have fire : e.c.stepDraw = some e.w := by
    have hstep := e.land
    rw [md] at hstep
    exact (show e.c.stepDraw = State.step e.c Move.draw from rfl).symm.trans hstep
  have hdnext : drawNext e.c = e.w := by simp only [drawNext, fire]
  have hlift : drawNextQ (⟦e.c⟧ : SameOrbit) = ⟦e.w⟧ := by
    rw [drawNextQ_mk, hdnext]
  rw [e.hmem] at hlift
  exact e.cl.symm.trans hlift.symm

/-! ## The axiom audit (per-declaration) -/

#print axioms orbit_data
#print axioms sameDatums_class
#print axioms MacroDatums
#print axioms MacroDatums.of
#print axioms MacroDatums.of_class
#print axioms datumOf
#print axioms datumOf_mk
#print axioms TipEdge.landing_wf
#print axioms tipEdge_exits_source
#print axioms tipEdge_ne_foundToTab
#print axioms tipEdge_draw_shape
#print axioms CanonicalTip
#print axioms MacroDatums.hiddenTotal
#print axioms MacroDatums.poolMiss
#print axioms MacroDatums.hiddenDropper
#print axioms MacroDatums.rootFreed
#print axioms labelOf
#print axioms labelOf_pair
#print axioms TipEdge.label
#print axioms edge_label_unique
#print axioms tipEdge_label_draw
#print axioms tipEdge_label_waste
#print axioms tipEdge_label_reveal
#print axioms tipEdge_label_vacate
#print axioms tipEdge_label_draw_ne
#print axioms tipEdge_label_waste_ne
#print axioms tipEdge_label_reveal_ne
#print axioms tipEdge_label_vacate_ne
#print axioms pair_move_character
#print axioms pair_move_character_switch
#print axioms nzRoot
#print axioms EdgeLabel
#print axioms WasteOf
#print axioms RevealCellAt
#print axioms VacateCellAt
#print axioms poolMissCard
#print axioms hiddenDropperAnchor
#print axioms rootFreedAnchor
#print axioms CanonLabel
#print axioms draw_landings_sameOrbit
#print axioms draw_successor_unique
#print axioms sameOrbit_cycleCount
#print axioms drawNext
#print axioms drawNextQ
#print axioms drawNextQ_mk
#print axioms drawNext_sound
#print axioms tipEdge_draw_target