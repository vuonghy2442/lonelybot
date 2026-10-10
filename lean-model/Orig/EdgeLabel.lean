import Orig.Canonical
import Orig.Classify
import Orig.Reach
import Orig.Twin

/-!
# Orig — the canonical edge labels (the CanonEdge normal form and the
class-pair fingerprint)

`FUTURES-ORIG.md` §3.1, THE EDGE-LABELING THEOREM (the user's
proposal, refined through the 2026-10-10 dialogue; the assembly's
SECOND milestone, standalone on landed content), with the same day's
restated headline: *what committed move can happen between two macro
neighbors is a property of the class pair* — a draw only from a
non-pure tip, a waste exit only of one pinned card, a tableau event
only at one pinned seat (and, in the reveal cell, of one pinned
revealed card).

## The normal form

`CanonEdge C D` — the recorded §3.1 structure: a macro transition
anchored at the canonical form is **reversible padding from the
Final/WF source + exactly one commitment + class closure**.  A macro
transition does not have a unique underlying MOVE (the twin-landing
merge is one edge, two moves), but every macro transition has this
normal form; the single commit slot is structural — a chain's first
commit already exits its class (`canonEdge_exits_source` is the
phase-progress cell reading of exactly that), so multi-commit edges
are impossible: every subsequent commit is its own edge.  The
padding is the WITNESS form `ShufflePlayW` (every leg carries its
own returning play), and the tip `u` and landing `w` are explicit
data.

## The fingerprint route (why the label is a function of the pair)

Four journey-invariant datums are proved once, here, and consumed
everywhere:

* `cycleCount` — never rises under any single move; a witness-shuffle
  leg conserves it exactly (waste legs cannot appear at all — they
  are commitments at every position), so it is constant on macro
  classes and across CanonEdge paddings;
* the per-anchor hidden lists — no witness leg ever touches them
  (only reveals move hidden cards, and reveals are commitments by
  the hidden-descent rows), so they are literal macro-class
  invariants — stronger than the hidden *total* the classification
  tables grade;
* `drawPool` — draws conserve the pool (the recycle reverses, the
  deal splits without loss), waste legs cannot appear, every other
  move keeps the draw zone verbatim — constant on macro classes;
* `nzRoot` — the bare non-king root of a seat (its bottom face-up
  card when that is not a king) never moves under a witness leg
  (every root departure is a commitment: the seat-physics rows for
  non-kings, the hidden-descent rows for reveals) — a macro-class
  invariant per anchor.

The committed move then writes exactly one of four signatures onto the
pair (C, `⟦w⟧`):

* **draw** — nothing else changes (the draw moves stock to waste
  within one reservoir), and the committed draw fires only at a
  non-pure tip: pristine (empty waste) or offset (waste misaligned) —
  `canonEdge_draw_shape`;
* **waste exit** — the cycle strictly drops, and the popped card is
  the pair's pool-difference card (`poolMissCard C w`; uniqueness by
  the `WF` occurrence bookkeeping), so the card is a function of the
  pair — `wasteEntry`;
* **reveal** — a per-anchor hidden stack strictly dropped its head
  (the automatic flip); the seat is the pair's hidden-difference
  anchor `hiddenDropperAnchor C w`, and the revealed card is the
  class-visible head of that hidden stack — also pair functions;
* **vacate** — a hidden-free seat lost its bare non-king root; the
  seat is the pair's seat-difference anchor `rootFreedAnchor C w` —
  the arm-typing's fourth family riding the same positional label as
  the degenerate hidden-count-zero cell of the reveal family
  (`stackEvent`).

`CanonLabel C w` reads the fingerprint at the anchor form `C` against
any WF member `w` of the target class; the read is independent of the
member, so the edge label is a function of the pair, not of the scheme.
The determinations tie each commitment family to its fingerprint branch
with the exact card/anchor data; the assembled exhaustiveness is the
restated canonical property: two schemes over one class pair commit
the same *event*.

## The landing status of this drop (honest boundary)

This drop lands the JOURNEY-DATA core, the CANONEDGE normal form, and
two milestone cells of the commit table, plus the full label-map
surface (the tripartite alphabet, the cell predicates, and the
fingerprint reads whose three channels consume the four journey
invariants):

* **proved, green**: `leg_data` (the per-leg table: every witness leg
  conserves `cycleCount`, the pool, every per-anchor hidden list, and
  every seat root — the reveal and bare-nonking cells excluded as the
  hidden-descent/seat-physics commitments, the waste rows as the
  universal commitments, the under/bare-king shapes kept literally by
  the landed placement lemmas), `shuffleW_data`/`orbit_data` (the
  class-invariant lifts), `CanonEdge` with `tip_wf`/`landing_wf`,
  `canonEdge_exits_source` (the phase-progress cell: the commit
  strictly exits its class), `canonEdge_ne_foundToTab` (the
  no-fourth-kind cell, part one: a committed move is never a
  foundation giveback — every legal WF `foundToTab` is reversible),
  and `canonEdge_draw_shape` (a draw edge
  starts non-pure: pristine or offset), the orbit-independence of the
  read (`canonLabel_orbit_indep`: any two WF class-mates give the same
  fingerprint), the pair-function property (`edge_label_unique`: two
  schemes over one class pair carry the same label), and the draw
  determination row (`canonEdge_label_draw`: a draw-commit edge is
  draw-labeled — no datum changes, all three reads degenerate), plus
  the full label-map definitions (`nzRoot`, `EdgeLabel`, `WasteOf`,
  `RevealCellAt`, `VacateCellAt`, `poolMissCard`, `hiddenDropperAnchor`,
  `rootFreedAnchor`, `CanonLabel`, `CanonEdge.label`).  The card-pinning
  census and the search reads ride the public packs (`Integrity`'s
  census-pack and search iffs, `State`/`Play`'s trivia/reader kits) —
  no farm-private recounting.
* **next card** (the remaining cells of the theorem, consuming what is
  landed here): the per-commit signature tables at the four cells
  (cycle-drop + pool-difference for the waste exit; the head-drop for
  the reveal; the seat-root departure for the vacate), the remaining
  determination rows (waste/reveal/vacate — the draw row is landed),
  the draw-vs-card disjointness, and the pair-move character assembly.

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

/-! ## Private kit: step inversions (farm copies; dedup at merge) -/

/-- A successful `.wasteToFound`: the waste head is the moved card,
and the successor is the written foundation with the waste popped. -/
private theorem step_wasteToFound_inv {st : State} {c : Card} {s' : State}
    (h : State.step st (Move.wasteToFound c) = some s') :
    ∃ xs, st.waste = c :: xs ∧
      s' = { st.setFound c.suit (st.found c.suit ++ [c]) with waste := xs } := by
  simp only [State.step] at h
  split at h
  · rename_i hg
    simp only [Bool.and_eq_true] at hg
    split at h
    · rename_i x xs hws
      injection h with hEq
      have hxc : x = c := by
        have hconv : st.wasteIs c = decide (x = c) := State.wasteIs_cons hws c
        rw [hconv] at hg
        exact of_decide_eq_true hg.1
      refine ⟨xs, by rw [hws, hxc], hEq.symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A successful `.wasteToTab`: the waste head is the moved card, and
the successor is the placement with the waste popped. -/
private theorem step_wasteToTab_inv {st : State} {c : Card} {b : Base} {s' : State}
    (h : State.step st (Move.wasteToTab c b) = some s') :
    st.canPlace c b = true ∧
    ∃ xs, st.waste = c :: xs ∧
      s' = { st.putCard c b with waste := xs } := by
  simp only [State.step] at h
  split at h
  · rename_i hg
    simp only [Bool.and_eq_true] at hg
    split at h
    · rename_i x xs hws
      injection h with hEq
      have hxc : x = c := by
        have hconv : st.wasteIs c = decide (x = c) := State.wasteIs_cons hws c
        rw [hconv] at hg
        exact of_decide_eq_true hg.1
      exact ⟨hg.2, xs, by rw [hws, hxc], hEq.symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A successful `.tabToFound`: the card was next-up, its pile was
located, and the successor is the raised foundation with the
(chopped) run removed from that pile. -/
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
    · rename_i a hp
      injection h with hEq
      exact ⟨hn, a, hp, hEq.symm⟩
  · exact absurd h (by simp)

/-- A successful `.tabToTab`: the run head was located, the placement
is legal, the moved run is nonempty, and the successor is the
removal-then-placement literal. -/
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
  · rename_i a hh
    split at h
    · rename_i hcp
      split at h
      · exact absurd h (by simp)
      · rename_i hne
        injection h with hEq
        exact ⟨a, hh, hcp, hne, hEq.symm⟩
    · exact absurd h (by simp)

/-- A successful `.foundToTab`: the named card is the foundation top,
the placement is legal, and the successor is the chopped foundation
with the card placed. -/
private theorem step_foundToTab_inv {st : State} {c : Card} {b : Base} {s' : State}
    (h : State.step st (Move.foundToTab c b) = some s') :
    st.foundTop c.suit = some c ∧ st.canPlace c b = true ∧
      s' = (st.setFound c.suit (chop (st.found c.suit))).putCard c b := by
  simp only [State.step] at h
  split at h
  · split at h
    · rename_i c' ht hcp
      rw [Bool.and_eq_true] at hcp
      injection h with hEq
      obtain rfl : c' = c := of_decide_eq_true hcp.1
      exact ⟨by rw [ht], hcp.2, hEq.symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

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

private theorem below_cons (c x : Card) (t : List Card) :
    below c (x :: t) = if x = c then [] else x :: below c t := rfl

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

/-- The run a run-move moves is headed at its run-head card. -/
private theorem fromCard_head_eq {c : Card} : ∀ {l : List Card}, c ∈ l →
    ∃ t, fromCard c l = c :: t := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (by simp)
  | cons x t ih =>
      intro h
      rcases List.mem_cons.1 h with rfl | hm
      · refine ⟨t, ?_⟩
        show (if c = c then (c :: t) else fromCard c t) = c :: t
        rw [ite_eq_left rfl]
      · obtain ⟨t', hrun⟩ := ih hm
        by_cases hxc : x = c
        · refine ⟨t, ?_⟩
          show (if x = c then (x :: t) else fromCard c t) = c :: t
          rw [ite_eq_left hxc, hxc]
        · refine ⟨t', ?_⟩
          show (if x = c then (x :: t) else fromCard c t) = c :: t'
          rw [ite_eq_right hxc]
          exact hrun

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

/-- A run landing with no search hit changes nothing. -/
private theorem putRun_inr_none {st : State} {run : List Card} {z : Card}
    (hz : st.pileOfTop z = none) (a' : Anchor) :
    (st.putRun run (Sum.inr z)).piles a' = st.piles a' := by
  show (match st.pileOfTop z with
    | some k => st.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ run }
    | none => st).piles a' = st.piles a'
  rw [hz]

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

/-- Recycling keeps the pool: the waste reversed ahead of nothing is
the waste ahead of an empty stock. -/
private theorem recycle_pool (st : State) :
    drawPool st.recycle = drawPool st := by
  cases hs : st.stock with
  | nil =>
      cases hw : st.waste with
      | nil =>
          rw [show st.recycle = st from by simp only [State.recycle, hs, hw]]
      | cons x t =>
          rw [show st.recycle = { st with stock := (x :: t).reverse, waste := [] } from by
              simp only [State.recycle, hs, hw]]
          show ((x :: t).reverse).reverse ++ ([] : List Card) = st.stock.reverse ++ st.waste
          rw [hs, hw, List.reverse_reverse, List.append_nil]
          rfl
  | cons y s =>
      rw [show st.recycle = st from by simp only [State.recycle, hs]]

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
      obtain ⟨-, hcp, hs⟩ := step_foundToTab_inv hstep
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
                              rw [putRun_inr_none hz]
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
                                rw [putRun_inr_none hz, hrP a', ite_eq_left ha,
                                  hbelow, hArb2]
                              have hxA : (x.piles a').faceUp = c :: t := by
                                rw [ha]; exact hfx0
                              rw [nzRoot_nil hyF, nzRoot_head hxA, ite_eq_left hk]
                            · exact nzRoot_congr_pile
                                ((putRun_inr_none hz a').trans
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
                fromCard_head_eq hmem
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
                        rw [putRun_inr_none hz]
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
                          rw [putRun_inr_none hz, hrP a', ite_eq_left ha,
                            hbelow, hArb3]
                        have hxF : (x.piles a').faceUp = z₀ :: r := by
                          rw [ha, hfx0, hfz]
                        rw [nzRoot_head hyF, nzRoot_head hxF]
                      · exact nzRoot_congr_pile
                          ((putRun_inr_none hz a').trans
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

/-! ## The CanonEdge normal form -/

/-- The canonical edge normal form (§3.1): a macro transition anchored
at a canonical state is **witness padding from the Final/WF source +
exactly one commitment + class closure**.  A macro transition does not
have a unique underlying MOVE (the twin-landing merge is one edge, two
moves), but it always has this form; the single commit slot is
structural — `canonEdge_exits_source` shows the commit strictly exits
its class, so multi-commit macro transitions would fail the closure
here and every subsequent commit is its own edge. -/
structure CanonEdge (C : State) (D : SameOrbit) where
  /-- the anchor: the move chain starts from a Final, WF position -/
  hfin : Final C
  /-- the anchor is well-formed (realizability) -/
  hwf : C.WF
  /-- the witness-padding tip -/
  u : State
  /-- the padding itself: every leg carries its own returning play -/
  pad : List Move
  hpad : ShufflePlayW C pad u
  /-- the single commitment, firing at the tip -/
  m : Move
  hm : irreversibleAt u m
  /-- the landing -/
  w : State
  land : State.step u m = some w
  /-- the class closure: the target takes the landing's class -/
  cl : ⟦w⟧ = D

/-- The tip and the landing inherit WF from the anchor (`step_wf`). -/
theorem CanonEdge.tip_wf {C : State} {D : SameOrbit} (e : CanonEdge C D) :
    e.u.WF :=
  shuffleW_wf_end e.hpad e.hwf

theorem CanonEdge.landing_wf {C : State} {D : SameOrbit} (e : CanonEdge C D) :
    e.w.WF :=
  step_wf e.tip_wf e.land

/-- The pair data along the padding: the tip reads the anchor's numbers. -/
private theorem pad_data {C : State} {D : SameOrbit} (e : CanonEdge C D) :
    cycleCount e.u = cycleCount C ∧ drawPool e.u = drawPool C ∧
    (∀ a, (e.u.piles a).hidden = (C.piles a).hidden) ∧
    (∀ a, nzRoot e.u a = nzRoot C a) :=
  shuffleW_data e.hpad

/-- **The phase-progress cell**: a committed move strictly exits its
source class — the landing of a CanonEdge commit is never a class-mate
of the anchor, so a multi-commit macro transition cannot exist (its
second move's argument would fail). -/
theorem canonEdge_exits_source {C : State} {D : SameOrbit} (e : CanonEdge C D) :
    D ≠ ⟦C⟧ := by
  intro hcon
  have hclass : ⟦e.w⟧ = ⟦C⟧ := e.cl.trans hcon
  rcases Quotient.exact hclass with ⟨σ, hσ, τ, hτ⟩
  have hu : e.w.run (τ ++ e.pad) = some e.u :=
    run_split τ e.w C e.pad e.u (ShufflePlayW_run hτ) (ShufflePlayW_run e.hpad)
  exact e.hm e.w (τ ++ e.pad) e.land hu

/-- **The no-fourth-kind cell (part one)**: a committed move at a WF tip
is never a foundation-to-tableau giveback.  Every legal `foundToTab` is
reversible at WF (the landing-target search reads only the piles, so
its undo never dies), so it cannot be the one commitment of a
CanonEdge. -/
theorem canonEdge_ne_foundToTab {C : State} {D : SameOrbit} (e : CanonEdge C D)
    (c : Card) (b : Base) : e.m ≠ Move.foundToTab c b := by
  intro hcon
  have hstep : e.u.step (Move.foundToTab c b) = some e.w := by
    rw [← hcon]
    exact e.land
  obtain ⟨htop, hcp, -⟩ := step_foundToTab_inv hstep
  exact absurd (foundToTab_reversibleAtW_of_legal_wf e.tip_wf htop hcp)
    (by
      intro hrevW
      exact (reversibleAt_of_W hrevW) (by rw [← hcon]; exact e.hm))

/-! ## The fingerprint reads (the label-map surface) -/

/-- The waste-pop read: the unique member of the anchor's draw pool that
the target's pool lacks, first in universe order (the
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

/-- **The class-pair fingerprint**: the label a directly-adjacent class
pair carries, read off the pair alone — the anchor form `C` against any
WF member `w` of the target class.  The three branches are the three
channels of the fingerprint route: the cycle-difference (waste exit)
branch reads the pool-difference card; the hidden-difference (reveal)
branch reads the hidden-difference anchor; the degenerate zero-delta
cell splits the draw (no datum changes) from the vacate (the
seat-difference read).  That the read is independent of the member `w`
is the pair-function property the label theorems consume. -/
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

/-- The label of a canonical edge: the fingerprint read at the pair. -/
def CanonEdge.label {C : State} {D : SameOrbit} (e : CanonEdge C D) : EdgeLabel :=
  CanonLabel C e.w

/-- **The read is a function of the class**: any two WF class-mates of
the target class give the same fingerprint — the four datums the reads
consume (cycle count, pool, per-anchor hidden lists, seat roots) are
macro-class invariants, so the label of a directly-adjacent class pair
depends only on the pair, never on which member of the target class
the reading happens to use. -/
theorem canonLabel_orbit_indep {C : State} {w w' : State}
    (h : ⟦w⟧ = ⟦w'⟧) (hwf : w.WF) : CanonLabel C w = CanonLabel C w' := by
  obtain ⟨-, hc, hp, hh, hn⟩ := orbit_data (Quotient.exact h) hwf
  have hHT : hiddenTotal w' = hiddenTotal w := hiddenTotal_congr hh
  have hPool : poolMissCard C w = poolMissCard C w' := by
    unfold poolMissCard
    refine firstWhere_congr (fun c => ?_)
    rw [hp]
  have hDrop : hiddenDropperAnchor C w = hiddenDropperAnchor C w' := by
    unfold hiddenDropperAnchor
    refine firstWhere_congr (fun a => ?_)
    rw [hh a]
  have hRoot : rootFreedAnchor C w = rootFreedAnchor C w' := by
    unfold rootFreedAnchor
    refine firstWhere_congr (fun a => ?_)
    rw [hn a]
  unfold CanonLabel
  rw [hc, hHT]
  by_cases h1 : cycleCount w < cycleCount C
  · rw [ite_eq_left h1, ite_eq_left h1, hPool]
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : hiddenTotal w < hiddenTotal C
    · rw [ite_eq_left h2, ite_eq_left h2, hDrop]
    · rw [ite_eq_right h2, ite_eq_right h2, hRoot]

/-- **The label is a function of the pair**: two CanonEdge schemes
witnessing the same class pair carry the same label — the label does
not depend on the scheme (which padding, which commit instance), only
on the class pair itself. -/
theorem edge_label_unique {C : State} {D : SameOrbit}
    (e₁ e₂ : CanonEdge C D) : e₁.label = e₂.label :=
  canonLabel_orbit_indep (e₁.cl.trans e₂.cl.symm) e₁.landing_wf

/-! ## The determination rows (one commit family at a time) -/

/-- **The draw row**: an edge whose single commitment is a draw is
draw-labeled — the draw moves stock to waste within one reservoir, so
no datum changes across the pair: the cycle test fails (the landing
reads the anchor's count), the hidden test fails (the landing reads the
anchor's total), and the seat read finds no differing root (the
landing reads the anchor's roots) — the fingerprint degenerates to
`draw`. -/
theorem canonEdge_label_draw {C : State} {D : SameOrbit} (e : CanonEdge C D)
    (hm : e.m = Move.draw) : e.label = EdgeLabel.draw := by
  show CanonLabel C e.w = EdgeLabel.draw
  have hsD : e.u.stepDraw = some e.w := by
    have h1 : e.u.step e.m = some e.w := e.land
    rw [hm] at h1
    exact h1
  obtain ⟨hcE, hpE, hhE, hnE⟩ := pad_data e
  have hpiles : e.w.piles = e.u.piles := stepDraw_piles hsD
  have hcyc : cycleCount e.w = cycleCount C := (stepDraw_cycle hsD).trans hcE
  have hHT : hiddenTotal e.w = hiddenTotal C :=
    (hiddenTotal_congr (fun a => congrArg Pile.hidden (congrFun hpiles a))).trans
      (hiddenTotal_congr hhE)
  have hnz : ∀ a, nzRoot C a = nzRoot e.w a := by
    intro a
    exact ((nzRoot_congr_pile (congrFun hpiles a)).trans (hnE a)).symm
  unfold CanonLabel
  rw [hcyc, hHT]
  rw [ite_eq_right (Nat.lt_irrefl (cycleCount C))]
  rw [ite_eq_right (Nat.lt_irrefl (hiddenTotal C))]
  have hnone : rootFreedAnchor C e.w = none := by
    unfold rootFreedAnchor
    refine firstWhere_none_of_forall (fun a => decide (nzRoot C a ≠ nzRoot e.w a))
      (fun a _ => ?_)
    by_cases hEq : nzRoot C a = nzRoot e.w a
    · exact decide_eq_false (fun hne => hne hEq)
    · exact absurd (hnz a) hEq
  rw [hnone]


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
theorem canonEdge_draw_shape {C : State} {D : SameOrbit} (e : CanonEdge C D)
    (hm : e.m = Move.draw) :
    e.u.stock ≠ [] ∧
    (e.u.waste = [] ∨ e.u.waste.length % e.u.drawStep ≠ 0) := by
  have hsD : e.u.stepDraw = some e.w := by
    have h1 : e.u.step e.m = some e.w := e.land
    rw [hm] at h1
    exact h1
  have hrev (h : reversibleAtW e.u Move.draw) : False :=
    (reversibleAt_of_W h) (by rw [← hm]; exact e.hm)
  have hd : 0 < e.u.drawStep := e.tip_wf.2.2.2
  constructor
  · by_cases h1 : e.u.stock = []
    · by_cases h2 : e.u.waste = []
      · rw [stepDraw_bothEmpty_none h1 h2] at hsD
        exact absurd hsD (by simp)
      · exact (hrev (draw_passBase_reversibleW h1 h2 hd)).elim
    · exact h1
  · by_cases h2 : e.u.waste = []
    · exact Or.inl h2
    · by_cases h1 : e.u.stock = []
      · exact (hrev (draw_passBase_reversibleW h1 h2 hd)).elim
      · by_cases hres : e.u.waste.length % e.u.drawStep = 0
        · obtain ⟨s, t, hcon⟩ := list_cons_of_ne_nil h1
          have hph : inPhase e.u = true := by
            show (match e.u.stock with
              | [] => true
              | _ => decide (e.u.waste.length % e.u.drawStep = 0)) = true
            rw [hcon, hres]
            rfl
          exact (hrev (draw_reversible_inphaseW hd h1 h2 hph)).elim
        · exact Or.inr hres

/-! ## The axiom audit (per-declaration) -/

#print axioms orbit_data
#print axioms CanonEdge.tip_wf
#print axioms CanonEdge.landing_wf
#print axioms canonEdge_exits_source
#print axioms canonEdge_ne_foundToTab
#print axioms canonEdge_draw_shape
#print axioms canonLabel_orbit_indep
#print axioms edge_label_unique
#print axioms canonEdge_label_draw
#print axioms nzRoot
#print axioms EdgeLabel
#print axioms WasteOf
#print axioms RevealCellAt
#print axioms VacateCellAt
#print axioms poolMissCard
#print axioms hiddenDropperAnchor
#print axioms rootFreedAnchor
#print axioms CanonLabel
#print axioms CanonEdge.label