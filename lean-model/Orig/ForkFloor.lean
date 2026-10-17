import Orig.LowSlab
import Orig.Phase
import Orig.ForkStateSB

/-!
# Orig.ForkFloor — THE FORK-FLOOR CONJECTURE (fork-headedness under the commit DAG)

The VERTICAL companion of the Low-Slab program.  `Orig.LowSlab` walks
the HORIZONTAL face of a fork's neighborhood: every commitment OUT of
the fork's macro class is matched by a low duplicate INSIDE it.  This
file walks the VERTICAL face: fork-HEADEDNESS — the property "some
fork state is reachable from here" — is DOWNWARD-CLOSED under the
program's own commit grain: if a fork is reachable from `s`, a fork
stays reachable from `s ⊕ m` for every IRREVERSIBLE `m`.  The floor
(the set of fork-headed states) is closed under the commit DAG's
edges; the conjecture is that no single commitment can eat the last
fork.

THE MAIN ROW (the program owner's conjecture, statement VERBATIM —
byte-frozen):

* §5 **`fork_floor_of_commit`** [H, the routed head] — if some fork
  `F` is reachable from `s` (witness `x`), some fork remains
  reachable from the successor of any `irreversibleAt` move at `s`.
  Landed as a DISPATCH SKELETON in the house's
  `fork_neighbor_lowbridge` pattern: the six move constructors split
  by the in-tree FOUR-KIND taxonomy (raise-like `.tabToFound` /
  reveal `.tabToTab` / waste-jump `.wasteToFound` + `.wasteToTab` /
  draw-at-nonempty-stock `.draw`), the fifth constructor
  `.foundToTab` is VACUOUS at the WF grade
  (`lowslab_pull_never_commit_wf`, `Orig.LowSlab` — a foundation
  giveback never commits at a WF state), and the four live kinds
  route to four (five-arm) NAMED RESIDUES that carry exactly one
  `sorry` each with their complete routes in their docstrings.  The
  head itself adds NO content and NO fresh `sorry`: its `sorryAx`
  flows only through its named children — audit below.
  At this pass the HEAD-CASE REPAIR KIT of §5.0 is PROVED in-file
  (`p_survives_sameHead`, the distance-zero repair for every kind;
  `p_waste_eat_corridor`, the waste-eat's distance-one corridor
  repair; the committed-raise shape row of §3), and the
  disassembly goes further (§5.0b): the fork certificate is
  ARRANGEMENT-ONLY (`p_fork_boardTransfer` over the license
  congruences), so the draw kind's BOARD-ONLY exhibit is closed
  verbatim (`p_draw_board_repair`) and the waste-seating kind's
  founding-letter head is closed at distance one
  (`p_waste_seat_mirror`, the corridor's twin); every one of the
  five kind residues is now a DISPATCH over its exhibiting play's
  head, and what each routes to its own NAMED REMAINDER row
  (`p_draw_zone_rest`, `p_waste_found_rest`, `p_waste_seat_rest`,
  `p_raise_rest`, `p_reveal_rest`) is exactly the general-schedule
  repair time bound over the non-head plays — the probe program's
  surviving honest danger (`Orig/ForkFloorProbe.lean`: the
  multi-commit schedule, repairs beyond one leg); the crown
  `p_founded_seat_schedule` likewise closes its immediate-seat
  arm (`p_seatOffered`) and names its climb remainder
  (`p_seat_climb_rest`).

THE KIND-CENSUS SUB-ROWS (the per-kind availability rows the routes
apply; each priced, honesty over closure):

* §1 **`hidden_never_grows`** [E, PROVED zero-sorry] — no step ever
  appends to any pile's hidden list: per pile, the successor's hidden
  deck is either UNCHANGED or the one-card TAIL of the original (the
  reveal-only-shrinks law, tree-graded one-step form; the
  journey-graded lift `run_pile_hidden_le` lives with
  `Orig/ForkStateUniqGate.lean`'s hidden-pin machinery — this is the
  step-arm form of it, stated at the exact cons grain).
* §2 **`two_zone_exits_playable`** [E–M, PROVED zero-sorry] — the
  draw-zone exits land in playable zones: a `wasteToFound` founding
  leaves its card at the FOUNDATION TOP (the `foundToTab`
  guard-fetch reads exactly it) with piles and stock untouched; a
  `wasteToTab` landing seats its card FACE-UP in a tableau pile with
  foundations and stock untouched; a draw keeps every stock∪waste
  card inside the two playable cycle zones.  No card ever becomes
  unreachable-from-play through these letters.
* §3 **`founded_returnable_via_seats`** [M, PROVED zero-sorry] — the
  conditional return row: a founded card returns to the tableau by
  `foundToTab` AS SOON AS a fitting seat exists at the founding
  successor (the pull-back fires and re-seats the card face-up).
  Its named companion residue **`founded_late_seat_exists`** [H,
  THE SEAT-DELAY RESIDUE] carries the open HALF of the mission's
  third row: the general seat-delay argument (late-seat existence
  across the commit DAG) — precisely the defusing-schedule content
  the §5 residues consume, NOT a copy of the census (the proved
  census heads — `census_tabToFound_witness`, the seat mint/burn
  ledger family `seatLedger_pair` / `play_census_ledger` /
  `roundtrip_census_repay`, and the owner's-bet row
  `excursion_issues_noNewSeat`, all in `Orig/HostCensus.lean` —
  price WHICH seats an arrangement can still issue; the schedule's
  EXISTENCE across arbitrary commit DAGs is the residue's own
  content, priced for round-3 probes; at this pass the residue's
  input shape is LANDED in-file — `p_committed_raise_shape`: the
  committed founding empties the raised pile's chop and sits in
  one of exactly the two census arms, REVEAL or BARE-NON-KING, the
  under-seat and bare-king arms being barred by the commit premise
  itself — so its open content is the per-kind repair-time schedule
  for those two arms).
* §4 **`draws_permute_only`** [E, PROVED zero-sorry] — a step-draw
  never writes piles or foundations (the banked `stepDraw_piles` /
  `stepDraw_found`, `Orig/Irreversible.lean`), and the recycle
  permutes stock and waste only: the two-zone world's membership is
  conserved exactly (an iff at the draw), the finer cycle structure
  priced by `Orig/Phase.lean`'s tables
  (`draw_irreversibility_class`, `drawStep_one_class`).

House compliance: additive leaf (`import Orig.LowSlab` — brings the
sealed zone machinery, `familyBelowFrontier`, the commit-grade rows
and `lowslab_pull_never_commit_wf` — plus `import Orig.Phase` for the
draw tables, and `import Orig.ForkStateSB` (the decidable strong
detection, itself a one-import leaf over `Orig.ForkWeaker`, zero
`Classical` by its own battery; the probe family already binds it
beside this chapter) for the successor's-own-fork branch of the
per-kind remainders; everything else consumed is transitive: `ForkWitness`
via `Orig.PairName`, `irreversibleAt` via `Orig.Fate`, `step`/`run`
via `Orig.Play`, the step inversions and measure tables via
`Orig.Irreversible`, `mem_found_unique`/`mem_faceUp_only` via
`Orig.Integrity` in the routes' narrations, the hidden-pin dichotomy
via `Orig/ForkStateUniqGate`'s own private kit — mirrored here as
private copies per the per-file kit discipline); BOLD-named
docstrings with grades; `#print axioms` battery for every fresh head;
zero `Classical.choice` (the splits ride `Bool`-guard reads,
decidable-equality `by_cases`, and constructor mismatches by
`absurd … (by simp)` — no `omega` is ever fired at a non-arithmetic
goal); NEVER-regress: no other file is touched, the main statement
is byte-frozen from the mission text. -/

/-! ## §0. The private kit (per-file copies)

The list-membership trivium the draw rows ride (core has the
append/cons lemmas; the reverse/take/drop membership reads are this
file's own copies, proved by structural induction), and the
reveal-only-shrinks dichotomy for `Pile.afterRunRemoved` at the exact
cons grain §1 consumes. -/

/-- Membership in a reversed list is membership in the list (the
private copy; both directions used by the draw cycle rows). -/
private theorem p_mem_reverse_iff {l : List Card} {x : Card} :
    x ∈ l.reverse ↔ x ∈ l := by
  induction l with
  | nil => exact Iff.rfl
  | cons y t ih =>
      constructor
      · intro h
        rw [List.reverse_cons, List.mem_append] at h
        rcases h with h | h
        · exact List.mem_cons.2 (Or.inr (ih.mp h))
        · rcases List.mem_cons.1 h with rfl | hbot
          · exact List.mem_cons_self ..
          · exact absurd hbot (by simp)
      · intro h
        rcases List.mem_cons.1 h with rfl | h
        · rw [List.reverse_cons]
          exact List.mem_append.2 (Or.inr (List.mem_cons_self ..))
        · rw [List.reverse_cons]
          exact List.mem_append.2 (Or.inl (ih.mpr h))

/-- A member of a `take` is a member of the list. -/
private theorem p_mem_take {x : Card} : ∀ (k : Nat) (l : List Card),
    x ∈ l.take k → x ∈ l := by
  intro k
  induction k with
  | zero => intro l h; exact absurd h (by simp)
  | succ n ih =>
      intro l h
      cases l with
      | nil => exact absurd h (by simp)
      | cons y t =>
          have h2 : x ∈ y :: t.take n := h
          rcases List.mem_cons.1 h2 with rfl | hm
          · exact List.mem_cons_self ..
          · exact List.mem_cons.2 (Or.inr (ih t hm))

/-- A member of a `drop` is a member of the list. -/
private theorem p_mem_drop {x : Card} : ∀ (k : Nat) (l : List Card),
    x ∈ l.drop k → x ∈ l := by
  intro k
  induction k with
  | zero => intro l h; exact h
  | succ n ih =>
      intro l h
      cases l with
      | nil => exact absurd h (by simp)
      | cons y t =>
          have h2 : x ∈ t.drop n := h
          exact List.mem_cons.2 (Or.inr (ih t h2))

/-- **THE REVEAL DICHOTOMY, CONS GRAIN** — a run removal either keeps
the pile's hidden deck EXACTLY or pops its head (the reveal); it
never appends, in any arm.  The `Pile.afterRunRemoved` step-armed
copy of what the journey-graded pin consumes. -/
private theorem p_arr_hidden_shape (p : Pile) (pre : List Card) :
    (Pile.afterRunRemoved p pre).hidden = p.hidden ∨
      ∃ h, p.hidden = h :: (Pile.afterRunRemoved p pre).hidden := by
  cases pre with
  | cons v vs => exact Or.inl rfl
  | nil =>
      rcases p with ⟨hd, f⟩
      cases hd with
      | nil => exact Or.inl rfl
      | cons h t => exact Or.inr ⟨h, rfl⟩

/-- **THE RECYCLE MEMBERSHIP READ** — recycling conserves the
two-zone world's membership exactly: if `r` is the recycle of `s`,
every card's stock∪waste membership is the same at both states. -/
private theorem p_recycle_mem_iff {s r : State}
    (hrec : State.recycle s = r) (t : Card) :
    t ∈ s.stock ++ s.waste ↔ t ∈ r.stock ++ r.waste := by
  cases hs : s.stock with
  | cons y ys =>
      rw [recycle_keep s (by rw [hs]; simp)] at hrec
      subst hrec
      rw [hs]
  | nil =>
      by_cases hw : s.waste = []
      · rw [recycle_allEmpty s hs hw] at hrec
        subst hrec
        rw [hs]
      · rw [recycle_nil s hs hw] at hrec
        subst hrec
        constructor
        · intro hm
          rcases List.mem_append.1 hm with hm | hm
          · exact absurd hm (by simp)
          · exact List.mem_append.2
              (Or.inl (p_mem_reverse_iff.mpr hm))
        · intro hm
          rcases List.mem_append.1 hm with hm | hm
          · exact List.mem_append.2
              (Or.inr (p_mem_reverse_iff.mp hm))
          · exact absurd hm (by simp)

/-- **THE DRAW CYCLE MEMBERSHIP READ** — a successful draw conserves
the two-zone world's membership exactly: the recycle permutes
stock↔waste and `dealUpTo` splits without loss
(`dealUpTo_eq_take_drop` + `List.take_append_drop`), so every card
sits in the stock∪waste of the successor iff it sat there before.
Both §2 (the exit direction) and §4 (the permutation row) ride this
one copy. -/
private theorem p_draw_cycle_mem_iff {s s' : State}
    (hstep : State.step s Move.draw = some s') (t : Card) :
    t ∈ s'.stock ++ s'.waste ↔ t ∈ s.stock ++ s.waste := by
  have hs : s.stepDraw = some s' := hstep
  obtain ⟨r, hrec, -, hs'⟩ := draw_unfold hs
  have hsd : s'.stock = r.stock.drop r.drawStep ∧
      s'.waste = (r.stock.take r.drawStep).reverse ++ r.waste := by
    rw [hs', dealUpTo_eq_take_drop]
    exact ⟨rfl, rfl⟩
  rw [hsd.1, hsd.2]
  constructor
  · intro hm
    rcases List.mem_append.1 hm with hm | hm
    · exact (p_recycle_mem_iff hrec t).mpr
        (List.mem_append.2 (Or.inl (p_mem_drop _ _ hm)))
    · rcases List.mem_append.1 hm with hm | hm
      · exact (p_recycle_mem_iff hrec t).mpr
          (List.mem_append.2 (Or.inl
            (p_mem_take _ _ (p_mem_reverse_iff.mp hm))))
      · exact (p_recycle_mem_iff hrec t).mpr
          (List.mem_append.2 (Or.inr hm))
  · intro hm
    have hrc : t ∈ r.stock ++ r.waste :=
      (p_recycle_mem_iff hrec t).mp hm
    rcases List.mem_append.1 hrc with hm | hm
    · rw [← List.take_append_drop r.drawStep r.stock] at hm
      rcases List.mem_append.1 hm with hm | hm
      · exact List.mem_append.2
          (Or.inr (List.mem_append.2 (Or.inl (p_mem_reverse_iff.mpr hm))))
      · exact List.mem_append.2 (Or.inl hm)
    · exact List.mem_append.2 (Or.inr (List.mem_append.2 (Or.inr hm)))

/-- A legal play preserves well-formedness (the run-lift of
`step_wf`, the per-file kit row the board transport below rides). -/
private theorem p_run_wf : ∀ (st : State) (play : List Move) (w : State),
    st.run play = some w → st.WF → w.WF := by
  intro st play
  induction play generalizing st with
  | nil => intro w h hwf; injection h with hsw; subst hsw; exact hwf
  | cons m rest ih =>
      intro w h hwf
      obtain ⟨s₁, hstep, hrest⟩ := State.run_cons h
      exact ih s₁ w hrest (step_wf hwf hstep)

/-! ## §1. The reveal-only-shrinks law (the one-step tree form) -/

/-- **`hidden_never_grows`** — **THE REVEAL-ONLY-SHRINKS LAW**, the
tree-graded one-step form: no step ever appends to any pile's hidden
list.  Per pile, the successor's hidden deck is either EXACTLY the
predecessor's, or the predecessor's with its head popped — the only
writer of a hidden list is the automatic reveal inside
`Pile.afterRunRemoved`, which only ever pops the next-to-flip card.
[E] — assembly over the step arms (`stepDraw_piles`,
`step_wasteToFound_inv`, `step_wasteToTab_inv` +
`putCard_hidden_eq`, `step_tabToFound_inv`, `step_foundToTab_inv`,
`step_tabToTab_inv` + the `setPile_afterRunRemoved_piles_*`
readers), with `p_arr_hidden_shape` closing the two reveal-carrying
arms.  No `WF` anywhere. -/
theorem hidden_never_grows {s s' : State} {m : Move}
    (hstep : State.step s m = some s') (a : Anchor) :
    (s'.piles a).hidden = (s.piles a).hidden ∨
      ∃ h, (s.piles a).hidden = h :: (s'.piles a).hidden := by
  cases m with
  | draw =>
      have hs : s.stepDraw = some s' := hstep
      rw [← stepDraw_piles hs]
      exact Or.inl rfl
  | wasteToFound c =>
      obtain ⟨-, x, xs, -, hs⟩ := step_wasteToFound_inv hstep
      rw [hs]
      exact Or.inl rfl
  | wasteToTab c b =>
      obtain ⟨hg, x, xs, -, hs⟩ := step_wasteToTab_inv hstep
      rw [Bool.and_eq_true] at hg
      rw [hs]
      exact Or.inl (putCard_hidden_eq hg.2 a)
  | tabToFound c =>
      obtain ⟨-, k, -, hs⟩ := step_tabToFound_inv hstep
      rw [hs]
      show (if a = k then
          Pile.afterRunRemoved (s.piles k) (chop (s.piles k).faceUp)
          else s.piles a).hidden = (s.piles a).hidden ∨
        ∃ h, (s.piles a).hidden = h ::
          (if a = k then
            Pile.afterRunRemoved (s.piles k) (chop (s.piles k).faceUp)
            else s.piles a).hidden
      by_cases hak : a = k
      · rw [hak, ite_eq_left rfl]
        exact p_arr_hidden_shape (s.piles k) (chop (s.piles k).faceUp)
      · rw [ite_eq_right hak]
        exact Or.inl rfl
  | foundToTab c b =>
      obtain ⟨c', ht, hc'c, hcp, hs⟩ := step_foundToTab_inv hstep
      rw [hs]
      have hcp' : (s.setFound c.suit (chop (s.found c.suit))).canPlace c b = true :=
        hcp
      exact Or.inl (putCard_hidden_eq hcp' a)
  | tabToTab c b =>
      obtain ⟨k, hh, hcp, -, hs⟩ := step_tabToTab_inv hstep
      rw [hs]
      cases b with
      | inl a₁ =>
          obtain ⟨hemp, -⟩ := canPlace_inl hcp
          obtain ⟨hhd, -⟩ := (Pile.isEmpty_eq _).mp hemp
          simp only [putRun_piles_inl]
          by_cases hae : a = a₁
          · rw [hae, ite_eq_left rfl, hhd]
            exact Or.inl rfl
          · rw [ite_eq_right hae]
            by_cases hak : a = k
            · rw [hak, setPile_afterRunRemoved_piles_self s k c]
              exact p_arr_hidden_shape (s.piles k)
                (below c (s.piles k).faceUp)
            · rw [setPile_afterRunRemoved_piles_ne s k c a hak]
              exact Or.inl rfl
      | inr z =>
          cases hz : (s.setPile k
              (Pile.afterRunRemoved (s.piles k)
                (below c (s.piles k).faceUp))).pileOfTop z with
          | none =>
              rw [putRun_inr_none hz]
              by_cases hak : a = k
              · rw [hak, setPile_afterRunRemoved_piles_self s k c]
                exact p_arr_hidden_shape (s.piles k)
                  (below c (s.piles k).faceUp)
              · rw [setPile_afterRunRemoved_piles_ne s k c a hak]
                exact Or.inl rfl
          | some kk =>
              simp only [putRun_piles_inr _ _ _ _ hz]
              by_cases hae : a = kk
              · rw [hae, ite_eq_left rfl]
                show ((s.setPile k
                    (Pile.afterRunRemoved (s.piles k)
                      (below c (s.piles k).faceUp))).piles kk).hidden
                  = (s.piles kk).hidden ∨ _
                by_cases hkk : kk = k
                · rw [hkk, setPile_afterRunRemoved_piles_self s k c]
                  exact p_arr_hidden_shape (s.piles k)
                    (below c (s.piles k).faceUp)
                · rw [setPile_afterRunRemoved_piles_ne s k c kk hkk]
                  exact Or.inl rfl
              · rw [ite_eq_right hae]
                by_cases hak : a = k
                · rw [hak, setPile_afterRunRemoved_piles_self s k c]
                  exact p_arr_hidden_shape (s.piles k)
                    (below c (s.piles k).faceUp)
                · rw [setPile_afterRunRemoved_piles_ne s k c a hak]
                  exact Or.inl rfl

/-! ## §2. The two-zone exits -/

/-- **THE WASTE-FOUNDING EXIT** — the `wasteToFound` landing read: the
founded card sits at its suit's FOUNDATION TOP at the successor (so
the pull-back move type's own guard-fetch — `foundToTab`'s
`foundTop` consult — names EXACTLY it), and the move writes neither
the tableau nor the stock. -/
private theorem p_wasteToFound_exits {s s' : State} {c : Card}
    (hstep : State.step s (Move.wasteToFound c) = some s') :
    s'.foundTop c.suit = some c ∧ s'.piles = s.piles ∧ s'.stock = s.stock := by
  obtain ⟨-, x, xs, -, hs⟩ := step_wasteToFound_inv hstep
  rw [hs]
  refine ⟨?_, ?_, ?_⟩
  · show lastOf ((s.setFound c.suit (s.found c.suit ++ [c])).found c.suit) = some c
    rw [setFound_found_self]
    exact lastOf_snoc
  · show (s.setFound c.suit (s.found c.suit ++ [c])).piles = s.piles
    exact setFound_piles s c.suit _
  · show (s.setFound c.suit (s.found c.suit ++ [c])).stock = s.stock
    exact setFound_stock s c.suit _

/-- **THE WASTE-SEATING EXIT** — the `wasteToTab` landing read: the
moved card lands FACE-UP in a tableau pile of the successor (the
playable zone par excellence), and the move writes neither the
foundations nor the stock. -/
private theorem p_wasteToTab_exits {s s' : State} {c : Card} {b : Base}
    (hstep : State.step s (Move.wasteToTab c b) = some s') :
    (∃ a, c ∈ (s'.piles a).faceUp) ∧ s'.found = s.found ∧ s'.stock = s.stock := by
  obtain ⟨hg, x, xs, -, hs⟩ := step_wasteToTab_inv hstep
  rw [Bool.and_eq_true] at hg
  rw [hs]
  refine ⟨?_, ?_, ?_⟩
  · cases b with
    | inl k =>
        refine ⟨k, ?_⟩
        show c ∈ ((s.putCard c (Sum.inl k)).piles k).faceUp
        rw [putCard_piles_inl]
        show c ∈ (if k = k then (⟨[], [c]⟩ : Pile) else s.piles k).faceUp
        rw [ite_eq_left rfl]
        exact List.mem_cons_self ..
    | inr z =>
        obtain ⟨k, hz, -⟩ := canPlace_inr hg.2
        refine ⟨k, ?_⟩
        rw [putCard_inr_eq hz, setPile_piles_self]
        exact List.mem_append.2 (Or.inr (List.mem_cons_self ..))
  · show (s.putCard c b).found = s.found
    exact putCard_found s c b
  · show (s.putCard c b).stock = s.stock
    exact putCard_stock s c b

/-- **`two_zone_exits_playable`** — **THE TWO-ZONE EXIT CENSUS**:
`wasteToFound` / `wasteToTab` / `stepDraw` move cards only among
{piles, found, stock, waste}, and no card ever becomes
unreachable-from-play.  The founding exit lands the card at the
FOUNDATION TOP — the one zone whose pull-back move type
(`foundToTab`) is a first-class letter of the game, and whose own
guard-fetch reads exactly the founded card — with the tableau and
stock untouched; the seating exit lands the card FACE-UP in a pile
with foundations and stock untouched; the draw exit keeps every
stock∪waste card inside the two playable cycle zones (the recycle
permutes, the deal deposits).  [E–M] — assembly over
`p_wasteToFound_exits`, `p_wasteToTab_exits`, and
`p_draw_cycle_mem_iff`'s exit direction; the three prongs are
constructor-disjoint, so the case split is shape-only. -/
theorem two_zone_exits_playable {s s' : State} {m : Move}
    (hstep : State.step s m = some s') :
    (∀ c, m = Move.wasteToFound c →
        s'.foundTop c.suit = some c ∧ s'.piles = s.piles ∧ s'.stock = s.stock) ∧
    (∀ c b, m = Move.wasteToTab c b →
        (∃ a, c ∈ (s'.piles a).faceUp) ∧ s'.found = s.found ∧ s'.stock = s.stock) ∧
    (m = Move.draw →
        ∀ t, t ∈ s.stock ++ s.waste → t ∈ s'.stock ++ s'.waste) := by
  cases m with
  | draw =>
      refine ⟨?_, ?_, ?_⟩
      · intro c hcon; exact absurd hcon (by simp)
      · intro c b hcon; exact absurd hcon (by simp)
      · intro _ t hm; exact (p_draw_cycle_mem_iff hstep t).mpr hm
  | wasteToFound c =>
      refine ⟨?_, ?_, ?_⟩
      · intro c' hcon
        injection hcon with hcc
        subst hcc
        exact p_wasteToFound_exits hstep
      · intro c' b hcon; exact absurd hcon (by simp)
      · intro hcon; exact absurd hcon (by simp)
  | wasteToTab c b =>
      refine ⟨?_, ?_, ?_⟩
      · intro c' hcon; exact absurd hcon (by simp)
      · intro c' b' hcon
        injection hcon with hcc hbb
        subst hcc
        subst hbb
        exact p_wasteToTab_exits hstep
      · intro hcon; exact absurd hcon (by simp)
  | tabToFound c =>
      refine ⟨?_, ?_, ?_⟩
      · intro c' hcon; exact absurd hcon (by simp)
      · intro c' b hcon; exact absurd hcon (by simp)
      · intro hcon; exact absurd hcon (by simp)
  | tabToTab c b =>
      refine ⟨?_, ?_, ?_⟩
      · intro c' hcon; exact absurd hcon (by simp)
      · intro c' b hcon; exact absurd hcon (by simp)
      · intro hcon; exact absurd hcon (by simp)
  | foundToTab c b =>
      refine ⟨?_, ?_, ?_⟩
      · intro c' hcon; exact absurd hcon (by simp)
      · intro c' b hcon; exact absurd hcon (by simp)
      · intro hcon; exact absurd hcon (by simp)

/-! ## §3. The founded-card return -/

/-- **`founded_returnable_via_seats`** — **THE SEATED RETURN ROW**: a
founded card returns to the tableau by `foundToTab` AS SOON AS a
fitting seat exists.  Two prongs, both from the founding's own
record: (i) the successor's foundation top IS the founded card
(`tabToFound_found_trio` — the pull-back move's guard-fetch reads
exactly it), and (ii) with any legal placement of it, the pull-back
FIRES and re-seats the card FACE-UP in a pile
(`step_foundToTab_splice` + the `putCard` seat readers).  [M] —
assembly over the banked trio/splice row, zero fresh content.  No
`WF` anywhere.  The waste-founding sibling arm (`wasteToFound`) has
the identical found-side record (the same `setFound` literal +
`lastOf_snoc`), and its pull-back consult is the same move type
exactly; this row is stated at the commit DAG's canonical founding
letter (`tabToFound`), the §5 raise-kind's own. -/
theorem founded_returnable_via_seats {s s' : State} {c : Card}
    (hstep : State.step s (Move.tabToFound c) = some s') :
    s'.foundTop c.suit = some c ∧
      ∀ (b : Base), s'.canPlace c b = true →
        ∃ (t : State) (a : Anchor),
          State.step s' (Move.foundToTab c b) = some t ∧ c ∈ (t.piles a).faceUp := by
  obtain ⟨-, k, -, hs⟩ := step_tabToFound_inv hstep
  obtain ⟨hf, -, hft⟩ := tabToFound_found_trio hs
  refine ⟨hft, ?_⟩
  intro b hcp
  have hsp := step_foundToTab_splice (st := s') hft hcp
  have hcpq : (s'.setFound c.suit (chop (s'.found c.suit))).canPlace c b = true :=
    hcp
  cases b with
  | inl k' =>
      refine ⟨(s'.setFound c.suit (chop (s'.found c.suit))).putCard c (Sum.inl k'),
        k', hsp, ?_⟩
      rw [putCard_eq_inl, setPile_piles_self]
      exact List.mem_cons_self ..
  | inr z =>
      obtain ⟨kk, hz, -⟩ := canPlace_inr hcpq
      refine ⟨(s'.setFound c.suit (chop (s'.found c.suit))).putCard c (Sum.inr z),
        kk, hsp, ?_⟩
      rw [putCard_inr_eq hz, setPile_piles_self]
      exact List.mem_append.2 (Or.inr (List.mem_cons_self ..))

/-- **THE COMMITTED-RAISE SHAPE** (the seat-delay residue's
dichotomy arm, landed): at a WF state a COMMITTED `.tabToFound c`
has the raised pile's face-up chop EMPTY, and the emptied seat is one
of exactly the two census arms — the REVEAL (a hidden head still to
flip) or the BARE-NON-KING.  The under-seat arm is refuted by the
commit premise itself (`tabToFound_undo_under`'s one-move mirror: the
exposed below-card `z` re-hosts the card, the WF search exactness
handing the mirror its seat), and the bare-KING arm by
`tabToFound_undo_bare` (the emptied anchor re-hosts its king) — so
what survives is exactly the pair of arms the census's §2 pin names.
This is `founded_late_seat_exists`'s live content, shrunk to the two
per-kind repair-time schedule arms. -/
private theorem p_committed_raise_shape {s s' : State} {c : Card} {k : Anchor}
    (hwf : s.WF)
    (hstep : State.step s (Move.tabToFound c) = some s')
    (hiv : irreversibleAt s (Move.tabToFound c))
    (hpo : s.pileOfTop c = some k) :
    chop (s.piles k).faceUp = [] ∧
      ((s.piles k).hidden ≠ [] ∨ c.rank ≠ Rank.king) := by
  -- the under-seat arm refutes against the commit premise
  by_cases hchop : chop (s.piles k).faceUp = []
  · refine ⟨hchop, ?_⟩
    by_cases hhid : (s.piles k).hidden = []
    · by_cases hking : c.rank = Rank.king
      · exact absurd (tabToFound_undo_bare hstep hpo hchop hhid hking)
          (not_reversibleAtW_of_irreversibleAt hiv)
      · exact Or.inr hking
    · exact Or.inl hhid
  · exfalso
    obtain ⟨z, hz, hsit⟩ :=
      runOK_snoc_sit (l := chop (s.piles k).faceUp) hchop
        (by rw [← lastOf_chop (pileOfTop_top hpo).2]; exact hwf.2.1 k)
    obtain ⟨-, k', hpo', hs⟩ := step_tabToFound_inv hstep
    have hk' : k' = k := Option.some.inj (hpo'.symm.trans hpo)
    rw [hk'] at hs
    have hwfs' : s'.WF := step_wf hwf hstep
    have hpilk : s'.piles k
        = Pile.afterRunRemoved (s.piles k) (chop (s.piles k).faceUp) := by
      rw [hs]
      show (if k = k then
          Pile.afterRunRemoved (s.piles k) (chop (s.piles k).faceUp)
        else s.piles k) = _
      rw [ite_eq_left rfl]
    have htopz : (s'.piles k).top = some z := by
      rw [hpilk, afterRunRemoved_ne hchop]
      show lastOf (chop (s.piles k).faceUp) = some z
      exact hz
    exact absurd (tabToFound_undo_under hstep hpo hz hsit
        ((pileOfTop_eq_some_iff hwfs').2 htopz))
      (not_reversibleAtW_of_irreversibleAt hiv)

/-- **THE SEAT SCAN** — does some base accept the card right NOW?
The decidable probe of fitting-seat existence (the seven anchors'
empty-seat arms plus the fifty-two host arms of the card-wide
placement guard), chosen as a `Bool` fold so the schedule's
dispatch below stays choice-free per the house discipline. -/
private def p_seatOffered (st : State) (c : Card) : Bool :=
  Anchor.all.any (fun a => st.canPlace c (Sum.inl a)) ||
    Card.universe.any (fun z => st.canPlace c (Sum.inr z))

/-- The scan is exact: it reads true exactly when a fitting seat
exists (the anchor arm by `Anchor.mem_all`, the host arm by
`Card.mem_universe`). -/
private theorem p_seatOffered_iff (st : State) (c : Card) :
    p_seatOffered st c = true ↔ ∃ b, st.canPlace c b = true := by
  constructor
  · intro h
    rw [p_seatOffered, Bool.or_eq_true] at h
    rcases h with hl | hr
    · obtain ⟨a, -, hval⟩ := List.any_eq_true.mp hl
      exact ⟨Sum.inl a, hval⟩
    · obtain ⟨z, -, hval⟩ := List.any_eq_true.mp hr
      exact ⟨Sum.inr z, hval⟩
  · intro ⟨b, hval⟩
    cases b with
    | inl a =>
        rw [p_seatOffered, Bool.or_eq_true]
        exact Or.inl (List.any_eq_true.mpr ⟨a, Anchor.mem_all a, hval⟩)
    | inr z =>
        rw [p_seatOffered, Bool.or_eq_true]
        exact Or.inr (List.any_eq_true.mpr ⟨z, Card.mem_universe z, hval⟩)

/-- **THE FRONTIER-CELL UNIQUENESS** (the climb's host-reduction
kernel): same suit and same rank index name the SAME card — so each
host cell of the founded card is ONE named card, and the two cells
the route speaks of are the twin pair one rank above it. -/
private theorem p_card_of_suit_toIdx {e e' : Card}
    (hss : e.suit = e'.suit) (hr : e.rank.toIdx = e'.rank.toIdx) :
    e = e' := by
  obtain ⟨es, er⟩ := e
  obtain ⟨e's, e'r⟩ := e'
  have hs : es = e's := hss
  simp only [Card.mk.injEq]
  exact ⟨hs, Rank.toIdx_inj hr⟩

/-- **THE NON-KING'S EMPTY-SEAT REFUSAL** [E] (route step 1, the
bare arm's datum): the empty-anchor consult is king-only, so for a
non-king the inl arm of the placement guard refuses at EVERY state —
the BARE-NON-KING arm's climb is purely a HOST-SURFACING question
(the inl arm never re-opens for it). -/
private theorem p_king_inl_refusal (c : Card) (hk : c.rank ≠ Rank.king)
    (t : State) (a : Anchor) : t.canPlace c (Sum.inl a) = false := by
  show ((t.piles a).isEmpty && decide (c.rank = Rank.king)) = false
  rw [decide_false_of_not hk]
  simp

/-- **THE CLIMB'S ACCEPTANCE SHAPE** [M] (route step 2, the
host-pair reduction): every placement acceptance is one of exactly
two shapes — the EMPTY-SEAT VACATE (an inl consult: the seat is
empty and the card is a king) or the CARD-HOST consult (an inr: the
host tops some pile, exactly one rank above the card, of the
opposite color family).  With `p_card_of_suit_toIdx` this pins every
climbing cell to the twin pair one rank above the founded card: the
HOST-SURFACING question the route's step 2 names. -/
private theorem p_climb_accept_shape {t : State} {c : Card} {b : Base}
    (hcp : t.canPlace c b = true) :
    (∃ a, b = Sum.inl a ∧ c.rank = Rank.king ∧ (t.piles a).isEmpty = true) ∨
      (∃ z a, b = Sum.inr z ∧ c.rank.toIdx + 1 = z.rank.toIdx ∧
        c.suit.color ≠ z.suit.color ∧ t.pileOfTop z = some a) := by
  cases b with
  | inl a =>
      obtain ⟨hemp, hking⟩ := canPlace_inl hcp
      exact Or.inl ⟨a, rfl, hking, hemp⟩
  | inr z =>
      obtain ⟨k, hpo, hsit⟩ := canPlace_inr hcp
      obtain ⟨hidx, hcol⟩ := (canSitOn_eq c z).mp hsit
      exact Or.inr ⟨z, k, rfl, hidx, hcol, hpo⟩

/-- **THE GUARD-REFUSED ECONOMY'S DISTANCE-ZERO CENSUS** [E–M]
(route step 2's input datum): when the founding successor's seat
scan reads FALSE, (i) every placement consult refuses the founded
card at the successor, (ii) a king's empty-seat vacate is barred —
no pile at the successor is empty at all, and (iii) no FITTING host
tops any pile — both host cells of the twin pair start
buried-or-absent.  This is the climb's starting shape: the schedule
must SURFACE a host (or, for a king, empty a pile) before any
consult accepts. -/
private theorem p_seat_refused_census {s' : State} {c : Card}
    (hno : p_seatOffered s' c = false) :
    (∀ b, s'.canPlace c b = false) ∧
      (∀ a, c.rank = Rank.king → (s'.piles a).isEmpty = false) ∧
      (∀ z, canSitOn c z = true → s'.pileOfTop z = none) := by
  have hnot : ¬ p_seatOffered s' c = true := by rw [hno]; simp
  refine ⟨?_, ?_, ?_⟩
  · intro b
    cases hb : s'.canPlace c b with
    | true => exact absurd ((p_seatOffered_iff s' c).mpr ⟨b, hb⟩) hnot
    | false => rfl
  · intro a hking
    show (s'.piles a).isEmpty = false
    cases he : (s'.piles a).isEmpty with
    | true =>
        have hcp : s'.canPlace c (Sum.inl a) = true := by
          show ((s'.piles a).isEmpty && decide (c.rank = Rank.king)) = true
          rw [he, hking]
          rfl
        exact absurd ((p_seatOffered_iff s' c).mpr ⟨Sum.inl a, hcp⟩) hnot
    | false => rfl
  · intro z hsit
    cases hp : s'.pileOfTop z with
    | some a =>
        have hcp : s'.canPlace c (Sum.inr z) = true := by
          show (match s'.pileOfTop z with
              | some _ => canSitOn c z
              | none => false) = true
          rw [hp]
          exact hsit
        exact absurd ((p_seatOffered_iff s' c).mpr ⟨Sum.inr z, hcp⟩) hnot
    | none => rfl

/-- **THE REVEAL ARM'S SURFACING DATUM** [E] (route step 1, the
reveal arm's own record): the emptied pile's hidden head surfaces at
the founding successor as the raised pile's BARE SINGLETON TOP — the
face-up record is exactly the surfaced card over the surviving
hidden tail, the surfaced head tops the pile, and the top-search
locates it.  Together with `p_seat_refused_census`: the surfaced
head is not itself a fitting host (else the guard refused nothing),
so the reveal arm's climb starts one leg deep. -/
private theorem p_climb_reveal_surface {s s' : State} {c : Card} {k : Anchor}
    {h : Card} {t : List Card}
    (hwf : s.WF)
    (hstep : State.step s (Move.tabToFound c) = some s')
    (hpo : s.pileOfTop c = some k)
    (hchop : chop (s.piles k).faceUp = [])
    (hhid : (s.piles k).hidden = h :: t) :
    (s'.piles k).faceUp = [h] ∧ s'.topOf k = some h ∧
      s'.pileOfTop h = some k := by
  have hwfs' : s'.WF := step_wf hwf hstep
  obtain ⟨-, k', hpo', hs'⟩ := step_tabToFound_inv hstep
  have hk' : k' = k := Option.some.inj (hpo'.symm.trans hpo)
  rw [hk'] at hs'
  have hpilk : s'.piles k
      = Pile.afterRunRemoved (s.piles k) (chop (s.piles k).faceUp) := by
    rw [hs']
    show (if k = k then
        Pile.afterRunRemoved (s.piles k) (chop (s.piles k).faceUp)
      else s.piles k) = _
    rw [ite_eq_left rfl]
  rcases hp : s.piles k with ⟨hd, fu⟩
  rw [hp] at hhid
  have hhd : hd = h :: t := hhid
  subst hhd
  have hfk : (s'.piles k).faceUp = [h] := by
    rw [hpilk, hchop, hp]
    rfl
  have htop : (s'.piles k).top = some h := by
    rw [hpilk, hchop, hp]
    rfl
  exact ⟨hfk, htop, (pileOfTop_eq_some_iff hwfs').2 htop⟩

/-- **THE SEAT-DELAY CLIMB** [H, THE CROWN'S NAMED SUB-ROW, settled
into isolation after honest effort, per the mission's discipline]:
the late-seat existence schedule in the GUARD-REFUSED economy —
every base at the founding successor refuses the founded card
(the scan reads false), so the seat must be RE-ISSUED by a
repair-time-bounded schedule of legal moves from the successor.

ROUTE (complete; the open step named):

 1. THE TWO ARMS, PINNED (the input shape): a committed founding
    at WF is one of exactly the two census arms
    (`p_committed_raise_shape`): the REVEAL arm — the emptied
    pile surfaces its hidden head, the hidden total strictly
    drops (`hiddenTotal_step_tabToFound_reveal`) and never rides
    back (§1's own law: the surfaced head never re-hides) — or the
    BARE-NON-KING arm — the emptied seat is refilled only
    king-headed (the pillar: an emptied pile's first arrival is
    an empty-anchor vacate, and `canPlace`'s king demand bars
    every other first card; `bare_lift_irreversibleAt` is the
    commitment that witnessed this very shape), so the BARE arm's
    founded card is NEVER a king (`harm`'s right disjunct at the
    emptied hidden-nil seat; a bare-KING raise is reversible
    anyway, `tabToFound_undo_bare`, barred by the commit
    premise): the inl empty-anchor arm never re-opens for THAT
    arm's climb.  In the REVEAL arm the founded card's rank is
    unconditioned, and the inl arm stays live exactly for a king
    — one more schedule shape the route prices with the rest.
 2. THE HOST-PAIR REDUCTION (the census's own):
    `canSitOn c z` pins the host cell exactly — z must be one of
    the TWO opposite-family cards at index c.rank.toIdx + 1 (the
    twin pair one rank above c) — so the climb is a HOST-SURFACING
    question: SOME reachable state has one of those two cards
    TOPPING a pile.  The mint/burn ledger
    (`seatLedger_pair`/`play_census_ledger`) telescopes the
    sequence; `census_tabToFound_witness`
    /`census_foundToTab_inr` name the only cells the board letters
    mint; and the crane's loan-and-repay
    (`excursion_issues_noNewSeat`) bars any host a RETURNED
    excursion would introduce — the arrangement's own census is
    the budget the climb spends.
 3. THE CLIMB ITSELF (the open step): within that budget the
    schedule raises/seats/slides until a host pair-member tops
    some pile — the EXPOSE-AND-SEAT heartbeat of the probes
    (found the covered raise to surface its host; seat the cycle
    card onto the surfaced host; the founded card's takeback
    unfreezes) — with the stock-reply tables (Table 1's
    `cycleCount_step`: never rising, strictly dropping at the
    waste letters) keeping the cycle reads honest.  The
    REPAIR-TIME BOUND — a measure strictly decreasing along the
    climb — is the residual content, carried here and nowhere
    else, exactly one `sorry`.

PROBE PRICING (round-3, cited as evidence, not imported, per the
mission): `fb1`'s economy is this remainder's OWN board at
decided grade — the direct return seats refused both arms
(`fb1S_sealRefused`: the seal real), ALL hosts of the taken card
refused at every snapshot probed, and the multi-leg
expose-and-seat repair minting the host — `5♥` surfaces hot,
seats onto the surfaced `5♠`-host, hosts the seal — the
`fb1`/`fb2`/`fb3` verdicts all repaired within reach, showing the
climb's floor is one-to-two legs on these economies, but the
universes of plays were not exhausted by hand (HUNTING-FLOOR
HONESTY): the multi-leg bound is the surviving open content.
`fb3X_notFork` is the honest-tail datapoint: the OPPOSING
schedule (surfacing lows into corridor content) saturates
nothing — live member with dead twin, decided — so the climb's
danger is bounded on its probed cases.

LANDED THIS PASS (the staging census, §0-kernel rows above):
route steps 1-2 are now staged at theorem grade —
`p_climb_reveal_surface` (the REVEAL arm's surfacing datum: the
emptied pile's hidden head surfaces as the raised pile's bare
singleton top, the exact reveal the hidden-total drop of
`hiddenTotal_step_tabToFound_reveal` prices), `p_king_inl_refusal`
(the BARE arm's king-only vacate: a non-king's empty-seat consult
refuses at EVERY state, so that arm's climb is purely
host-surfacing), `p_climb_accept_shape` (route step 2's
host-pair reduction: every acceptance is the EMPTY-SEAT VACATE
or the CARD-HOST consult, one rank above, opposite family),
`p_card_of_suit_toIdx` (each cell names ONE card — the twin pair
one rank above), and `p_seat_refused_census` (the guard-refused
economy's distance-zero read: no consult accepts, a king vacate
bars every empty seat, no fitting host tops anywhere — the
schedule's starting shape).  The census budget rows the route
names (`seatLedger_pair`, `play_census_ledger`,
`roundtrip_census_repay`, `census_tabToFound_witness`,
`census_foundToTab_inr`, `excursion_issues_noNewSeat`, the
public heads of `Orig/HostCensus.lean`) stay CITED, not copied.
What no census prices is exactly what remains: the REPAIR-TIME
BOUND of the route's step 3 — this row's sole `sorry`, now staged
from the refused census's ground state. -/
private theorem p_seat_climb_rest {s s' : State} {c : Card} {k : Anchor}
    (hwf : s.WF)
    (hstep : State.step s (Move.tabToFound c) = some s')
    (hchop : chop (s.piles k).faceUp = [])
    (harm : (s.piles k).hidden ≠ [] ∨ c.rank ≠ Rank.king)
    (hpo : s.pileOfTop c = some k)
    (hno : p_seatOffered s' c = false) :
    ∃ (ρ : List Move) (t : State) (b : Base),
      s'.run ρ = some t ∧ t.canPlace c b = true := by
  sorry

/-- **THE PER-KIND REPAIR-TIME SCHEDULE** — the NAMED SUB-RESIDUE of
`founded_late_seat_exists` (the isolate-the-remainder discipline,
applied after the honest stall): the seat-delay content, stated over
the PROVED dichotomy shape alone.  For either of the two census arms
of a committed founding at a WF state — the REVEAL arm (the emptied
pile still holds a hidden head to surface) or the BARE-NON-KING arm
(the emptied pile is fully bare at a non-king) — the founding
successor issues a fitting seat after a repair-time-bounded schedule
of legal moves.  The census heads (`excursion_issues_noNewSeat` and
the ledger family) price WHICH seats the arrangement can still issue;
this row is the schedule's EXISTENCE across the commit DAG — the
composition content, carried here and nowhere else.

ASSEMBLY STRUCTURE (this pass): the IMMEDIATE-SEAT arm is now
CLOSED (`p_seatOffered` + `p_seatOffered_iff`: when any base
accepts the card at the successor, the schedule is the EMPTY
play); the guard-refused economy falls to the named sub-row
`p_seat_climb_rest` (the expose-and-seat climb, the route above),
which carries the row's sole `sorry`. -/
private theorem p_founded_seat_schedule {s s' : State} {c : Card} {k : Anchor}
    (hwf : s.WF)
    (hstep : State.step s (Move.tabToFound c) = some s')
    (hchop : chop (s.piles k).faceUp = [])
    (harm : (s.piles k).hidden ≠ [] ∨ c.rank ≠ Rank.king)
    (hpo : s.pileOfTop c = some k) :
    ∃ (ρ : List Move) (t : State) (b : Base),
      s'.run ρ = some t ∧ t.canPlace c b = true := by
  by_cases ho : p_seatOffered s' c = true
  · obtain ⟨β, hb⟩ := (p_seatOffered_iff s' c).mp ho
    exact ⟨[], s', β, rfl, hb⟩
  · have hfalse : p_seatOffered s' c = false := by
      cases h : p_seatOffered s' c with
      | true => exact absurd h ho
      | false => rfl
    exact p_seat_climb_rest hwf hstep hchop harm hpo hfalse

/-- **`founded_late_seat_exists`** — **THE SEAT-DELAY RESIDUE** [H,
named residue, exactly one `sorry`]: the general seat-delay
argument of the mission's third row — late-seat existence across
the commit DAG.  A COMMITTED founding at a WF state cannot
permanently destroy its own takeback inventory (§1: no letter
grows a hidden deck; §2: the exits land in playable zones), so
the schedule claim: SOME state reachable from the founding
successor issues a fitting seat for the founded card — the row
§5's raise-kind consumes as its defusing first installment.

ROUTE (complete; the open step named):

 1. THE LOCAL AVAILABILITY (banked, §§1–2): every card the takeback
    consults stays in a playable zone along the DAG's letters — the
    hidden decks only shrink (§1), the draw zone permutes (§4), the
    waste exits land playable (§2).
 2. THE CENSUS PRICING (proved heads only, `Orig/HostCensus.lean`):
    `census_tabToFound_witness` prices the riding raise's exposed
    below-card (opposite family, index + 1, unfounded); the
    mint/burn ledger (`seatLedger_pair`, `play_census_ledger`,
    `roundtrip_census_repay`) telescopes any play's seat budgets;
    the owner's bet `excursion_issues_noNewSeat` bars NEW hosting
    capacity along returned excursions.  These price WHICH seats
    the arrangement can still issue — the residue deliberately
    does NOT copy them; what the census does NOT price is the
    schedule's EXISTENCE across the commit DAG, and that is where
    the row's own content lives (carried by the named sub-residue
    `p_founded_seat_schedule` below, per the isolate-the-remainder
    discipline).
 3. THE SCHEDULE, ISOLATED AS THE NAMED SUB-RESIDUE — per the
    settle-if-stalled discipline: the public row is now a pure
    ASSEMBLY of the PROVED dichotomy (`p_committed_raise_shape`:
    the raised pile's chop is EMPTY; the emptied seat is one of
    exactly two arms — the REVEAL arm, a hidden head surfacing at
    the successor, or the BARE-NON-KING arm; the under-seat and
    bare-king arms are refuted by `hivr` itself through the
    one-move mirrors `tabToFound_undo_under` / `tabToFound_undo_bare`)
    and `p_founded_seat_schedule`, itself an assembly — the
    IMMEDIATE-SEAT arm closed at the EMPTY play (the seat scan
    `p_seatOffered`, exact through `p_seatOffered_iff`), with the
    guard-refused economy in the NAMED carrier
    `p_seat_climb_rest`: the per-kind repair-time bound for those
    two arms — the schedule that re-issues a fitting seat from
    the founding successor (the reveal arm's surface-and-climb
    reads; the bare-non-king arm's climb), or the entombment
    certificate (no seat anywhere below) as the falsification
    witness.  THIS composition is the open content, not any
    census row.

PROBE PRICING (round-3; boards NOT added here, per the mission):
the falsification target is exactly the sub-residue's negation —
see the §5 main row's FALSIFICATION TARGET paragraph
(single-family-fragile economies, the sole pair member eaten, the
takeback seat permanently seat-less).  If that shape is real, THE
SUB-RESIDUE is the honest casualty and the main row's repair
disjunct documents it alongside. -/
theorem founded_late_seat_exists {s s' : State} {c : Card}
    (hwf : s.WF)
    (hstep : State.step s (Move.tabToFound c) = some s')
    (hivr : irreversibleAt s (Move.tabToFound c)) :
    ∃ (ρ : List Move) (t : State) (b : Base),
      s'.run ρ = some t ∧ t.canPlace c b = true := by
  -- the raised pile, located by the step's own record
  obtain ⟨-, k, hpo, -⟩ := step_tabToFound_inv hstep
  -- the committed founding's shape: dichotomy (proved) + the named schedule
  obtain ⟨hchop, harm⟩ := p_committed_raise_shape hwf hstep hivr hpo
  exact p_founded_seat_schedule hwf hstep hchop harm hpo

/-! ## §4. The draw permutation -/

/-- **`draws_permute_only`** — **THE DRAW PERMUTATION ROW**: a
step-draw writes neither the tableau nor the foundations (the banked
`stepDraw_piles` / `stepDraw_found` rows, cited not re-proved), and
the recycle permutes stock↔waste only — the two-zone world's
MEMBERSHIP is conserved exactly (the iff; `dealUpTo` splits without
loss, the recycle reverses).  [E] — the never-writes prongs are the
two cited banked rows; the membership iff is the private kit's
`p_draw_cycle_mem_iff`.  The finer cycle STRUCTURE (phase alignment,
the drawStep classes) is `Orig/Phase.lean`'s own pricing
(`draw_irreversibility_class`, `drawStep_one_class`,
`draw_reversible_inphaseW`) — deliberately not restated here. -/
theorem draws_permute_only {s s' : State}
    (hstep : State.step s Move.draw = some s') :
    s'.piles = s.piles ∧ s'.found = s.found ∧
      ∀ t, t ∈ s'.stock ++ s'.waste ↔ t ∈ s.stock ++ s.waste := by
  have hs : s.stepDraw = some s' := hstep
  exact ⟨stepDraw_piles hs, stepDraw_found hs, fun t => p_draw_cycle_mem_iff hstep t⟩

/-! ## §5. The main row, routed

The four-kind case split on the commit `m` (the four-kind taxonomy
is theorem-grade in-tree: the waste letters pop the cycle strictly
and never ride witness journeys — `journey_never_wasteToFound` /
`journey_never_wasteToTab`, `Orig/ForkStateUniqGate.lean`, over
Table 1; the committed draw fires at a nonempty stock, Phase's
`draw_irreversible_pristine` regime versus the banked empty-stock
reversibles; the raise and reveal letters carry the
`hiddenTotal`/`foundTotal` reveal cells).  Per kind, the per-kind
residue applies the kind sub-rows (§§1–4) and concludes the
defusing-schedule repair; the fifth constructor is vacuous at WF. -/

/-! ### §5.0. The head-case repair kit (proved)

The shapes the per-kind routes price their defusing schedules
against, landed at theorem grade so the open remainder is named
exactly: the SAME-HEAD repair (distance zero — the exhibiting fork
play begins with the very move that committed), for the waste-eat
the CORRIDOR repair (distance one — the exhibiting play
begins by seating the eaten head onto a base; the one-leg pull
`foundToTab c b` from the eat successor lands the corridor state
EXACTLY, and the rest replays verbatim), and for the waste-seating
its mirror image §5.0b's MIRROR (the exhibiting play begins with
the founding of the seated head; the one-move raise lands the
play's second state EXACTLY again).  These are the probe
program's fb1/fb2 verdict shapes, generalized
(`Orig/ForkFloorProbe.lean`: SURVIVES DISTANCE 0 / DISTANCE 1, the
attained-one-leg repair).  The congruence trio beneath them is the
per-file private kit: the placement guard and the board search read
the tableau only.  §5.0b beneath adds the board-thread kit —
the license congruences, the certificate rod, and the two closed
kind-fragments that ride them (the draw's board-only exhibit; the
seating's mirror). -/

/-- The top-search reads only the tableau (the per-file congruence
row; `State.pileOfTop` is a firstWhere over pile tops). -/
private theorem p_pileOfTop_congr {x y : State} (z : Card)
    (hp : x.piles = y.piles) :
    x.pileOfTop z = y.pileOfTop z := by
  show (firstWhere (fun a => decide (((x.piles a).top) = some z)) Anchor.all)
      = (firstWhere (fun a => decide (((y.piles a).top) = some z)) Anchor.all)
  rw [hp]

/-- The placement guard reads only the tableau (the per-file
congruence row over the guard's two branches). -/
private theorem p_canPlace_congr {x y : State} (c : Card) (b : Base)
    (hp : x.piles = y.piles) :
    x.canPlace c b = y.canPlace c b := by
  cases b with
  | inl a =>
      show ((x.piles a).isEmpty && decide (c.rank = Rank.king))
          = ((y.piles a).isEmpty && decide (c.rank = Rank.king))
      rw [hp]
  | inr z =>
      show (match x.pileOfTop z with
          | some _ => canSitOn c z
          | none => false)
          = (match y.pileOfTop z with
          | some _ => canSitOn c z
          | none => false)
      rw [p_pileOfTop_congr z hp]

/-- The seating write's tableau is determined by the pre-state's
tableau (the per-file congruence row; `putCard`'s branches read only
the top-search). -/
private theorem p_putCard_piles_congr {x y : State} (c : Card) (b : Base)
    (hp : x.piles = y.piles) :
    (x.putCard c b).piles = (y.putCard c b).piles := by
  cases b with
  | inl a =>
      show (fun a' => if a' = a then (⟨[], [c]⟩ : Pile) else x.piles a')
          = (fun a' => if a' = a then (⟨[], [c]⟩ : Pile) else y.piles a')
      rw [hp]
  | inr z =>
      cases hx : x.pileOfTop z with
      | none =>
          have hy : y.pileOfTop z = none := by
            rw [← p_pileOfTop_congr z hp, hx]
          rw [show x.putCard c (Sum.inr z) = x from by
              simp only [State.putCard, hx],
            show y.putCard c (Sum.inr z) = y from by
              simp only [State.putCard, hy]]
          exact hp
      | some k =>
          have hy : y.pileOfTop z = some k := by
            rw [← p_pileOfTop_congr z hp, hx]
          rw [show x.putCard c (Sum.inr z)
                = x.setPile k { x.piles k with faceUp := (x.piles k).faceUp ++ [c] } from by
              simp only [State.putCard, hx],
            show y.putCard c (Sum.inr z)
                = y.setPile k { y.piles k with faceUp := (y.piles k).faceUp ++ [c] } from by
              simp only [State.putCard, hy],
            setPile_piles, setPile_piles, hp]

/-- **THE SAME-HEAD REPAIR** (distance zero) — when the very move
that committed at `s` also HEADS the exhibiting fork play, the
successor IS the play's second state: the tail replays verbatim and
the same fork `F` is exhibited from `s'` with an empty repair — the
probe program's fb1-shape verdict, generalized. -/
private theorem p_survives_sameHead {s s' F : State} {τ : List Move} {m : Move}
    {x : Card}
    (hstep : State.step s m = some s')
    (hhead : s.run (m :: τ) = some F)
    (hwit : ForkWitness F x) :
    ∃ (F' : State) (π' : List Move) (x' : Card),
      s'.run π' = some F' ∧ ForkWitness F' x' := by
  obtain ⟨q, hq, hrest⟩ := State.run_cons hhead
  have hqs : q = s' := Option.some.inj (hq.symm.trans hstep)
  subst hqs
  exact ⟨F, τ, x, hrest, hwit⟩

/-- **THE CORRIDOR REPAIR** (distance one) — the waste-eat's
fb2-shape verdict, generalized: the committed founding
`wasteToFound c` ate the waste head `c`, and the exhibiting fork
play begins with the OTHER waste letter on the same head — the
seating `wasteToTab c b`.  The eat's exit leaves the tableau
untouched (`p_wasteToFound_exits`), so the pull `foundToTab c b`
fires at the successor (the founding's own `foundTop` consult names
the card; the placement guard reads the same tableau), the pull's
landing IS the corridor state (the founding is undone at the one
suit's row, `chop_snoc`; the seating write is the same `putCard` over
the same tableau), and the tail replays verbatim — the SAME fork `F`,
exhibited one leg later. -/
private theorem p_waste_eat_corridor {s s' F q₁ : State} {c : Card} {b : Base}
    {τ : List Move} {x : Card}
    (heat : State.step s (Move.wasteToFound c) = some s')
    (hcorr : State.step s (Move.wasteToTab c b) = some q₁)
    (htail : q₁.run τ = some F)
    (hwit : ForkWitness F x) :
    ∃ (F' : State) (π' : List Move) (x' : Card),
      s'.run π' = some F' ∧ ForkWitness F' x' := by
  obtain ⟨-, w, ws, hwaste, hsf⟩ := step_wasteToFound_inv heat
  obtain ⟨hgc, w', ws', hwaste', hsq⟩ := step_wasteToTab_inv hcorr
  rw [Bool.and_eq_true] at hgc
  have hww : w :: ws = w' :: ws' := by
    rw [← hwaste, ← hwaste']
  injection hww with hwd hws
  subst hwd
  subst hws
  -- the eat successor's landing reads: foundTop pinned, tableau untouched
  obtain ⟨htop, hpiles, -⟩ := p_wasteToFound_exits heat
  -- the eat successor's field facts, off its landing record
  have hs'fs : s'.found c.suit = s.found c.suit ++ [c] := by
    rw [hsf,
      show ({ s.setFound c.suit (s.found c.suit ++ [c]) with waste := ws } : State).found c.suit
          = (s.setFound c.suit (s.found c.suit ++ [c])).found c.suit from rfl,
      setFound_found_self]
  have hs'fo : ∀ σ, σ ≠ c.suit → s'.found σ = s.found σ := by
    intro σ hσ
    rw [hsf,
      show ({ s.setFound c.suit (s.found c.suit ++ [c]) with waste := ws } : State).found σ
          = (s.setFound c.suit (s.found c.suit ++ [c])).found σ from rfl,
      setFound_found_ne hσ]
  have hs's : s'.stock = s.stock := by
    rw [hsf,
      show ({ s.setFound c.suit (s.found c.suit ++ [c]) with waste := ws } : State).stock
          = (s.setFound c.suit (s.found c.suit ++ [c])).stock from rfl,
      setFound_stock]
  have hs'w : s'.waste = ws := by rw [hsf]
  have hs'd : s'.drawStep = s.drawStep := by
    rw [hsf,
      show ({ s.setFound c.suit (s.found c.suit ++ [c]) with waste := ws } : State).drawStep
          = (s.setFound c.suit (s.found c.suit ++ [c])).drawStep from rfl,
      setFound_drawStep]
  -- the pull's landing is the corridor state, exactly
  have hteq : (s'.setFound c.suit (chop (s'.found c.suit))).putCard c b
      = { s.putCard c b with waste := ws } := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · -- found
      rw [show ({ s.putCard c b with waste := ws } : State).found
            = (s.putCard c b).found from rfl,
        putCard_found, putCard_found]
      show (if σ = c.suit then chop (s'.found c.suit) else s'.found σ) = s.found σ
      by_cases hσ : σ = c.suit
      · rw [ite_eq_left hσ, hs'fs, chop_snoc]
        show s.found c.suit = s.found σ
        rw [hσ]
      · rw [ite_eq_right hσ, hs'fo σ hσ]
    · -- piles
      have hbasep : (s'.setFound c.suit (chop (s'.found c.suit))).piles = s.piles := by
        rw [setFound_piles, hpiles]
      rw [show ({ s.putCard c b with waste := ws } : State).piles
            = (s.putCard c b).piles from rfl,
        p_putCard_piles_congr c b hbasep]
    · -- stock
      have hL : ((s'.setFound c.suit (chop (s'.found c.suit))).putCard c b).stock
          = s.stock := by
        rw [putCard_stock, setFound_stock, hs's]
      have hR : ({ s.putCard c b with waste := ws } : State).stock = s.stock := by
        show (s.putCard c b).stock = s.stock
        exact putCard_stock s c b
      rw [hL, hR]
    · -- waste
      have hL : ((s'.setFound c.suit (chop (s'.found c.suit))).putCard c b).waste
          = ws := by
        rw [putCard_waste, setFound_waste, hs'w]
      have hR : ({ s.putCard c b with waste := ws } : State).waste = ws := rfl
      rw [hL, hR]
    · -- drawStep
      have hL : ((s'.setFound c.suit (chop (s'.found c.suit))).putCard c b).drawStep
          = s.drawStep := by
        rw [(putCard_keep (st := s'.setFound c.suit (chop (s'.found c.suit)))).2.2.2,
          setFound_drawStep, hs'd]
      have hR : ({ s.putCard c b with waste := ws } : State).drawStep
          = s.drawStep := by
        show (s.putCard c b).drawStep = s.drawStep
        exact (putCard_keep (st := s)).2.2.2
      rw [hL, hR]
  have htq : (s'.setFound c.suit (chop (s'.found c.suit))).putCard c b = q₁ :=
    hteq.trans hsq.symm
  -- the pull fires at the eat successor: the guard reads the same tableau
  have hcp : s'.canPlace c b = true := by
    have hc := p_canPlace_congr (x := s') (y := s) c b hpiles
    rw [hc]
    exact hgc.2
  refine ⟨F, Move.foundToTab c b :: τ, x, ?_, hwit⟩
  show (match State.step s' (Move.foundToTab c b) with
      | some st' => st'.run τ
      | none => none) = some F
  rw [step_foundToTab_splice htop hcp, htq]
  exact htail

/-! ### §5.0b. The board-thread kit (the fork certificate is
arrangement-only)

The rods the draw kind's board-only fragment and the seating arm's
mirror ride: the two licenses are board reads (through the flat
characterization for the S-grade), so a fork witness RE-CERTIFIES
at any state agreeing on piles and foundations; and the committed
draw, which writes no board cell, preserves the exhibiting play's
board-thread verbatim.  These are the probe program's fb-shape
"the fork never rode the eaten cell" verdicts, generalized to the
arrangement-blind relation the basin already carries (`boardEq`,
`Orig/HostCensus.lean` §9). -/

/-- The vanilla license reads only the board: two `boardEq`
states license exactly the same vanilla raises (the per-file
assembly of the banked `Twin.lean` congruence rows at the
`CanRaise` grain). -/
private theorem p_canRaise_congr {u v : State} (hb : boardEq u v)
    (c : Card) : CanRaise u c ↔ CanRaise v c := by
  constructor
  · rintro ⟨hn, a, hp, (hbs | ⟨hhid, hking⟩)⟩
    · refine ⟨by rw [← nextUp_congr c hb.2]; exact hn, a, ?_, Or.inl ?_⟩
      · rw [← pileOfTop_congr c hb.1]; exact hp
      · have hf : (u.piles a).faceUp = (v.piles a).faceUp :=
          congrArg Pile.faceUp (congrFun hb.1 a)
        rw [← hf]; exact hbs
    · refine ⟨by rw [← nextUp_congr c hb.2]; exact hn, a, ?_, Or.inr ⟨?_, hking⟩⟩
      · rw [← pileOfTop_congr c hb.1]; exact hp
      · have hh : (u.piles a).hidden = (v.piles a).hidden :=
          congrArg Pile.hidden (congrFun hb.1 a)
        rw [← hh]; exact hhid
  · rintro ⟨hn, a, hp, (hbs | ⟨hhid, hking⟩)⟩
    · refine ⟨by rw [nextUp_congr c hb.2]; exact hn, a, ?_, Or.inl ?_⟩
      · rw [pileOfTop_congr c hb.1]; exact hp
      · have hf : (u.piles a).faceUp = (v.piles a).faceUp :=
          congrArg Pile.faceUp (congrFun hb.1 a)
        rw [hf]; exact hbs
    · refine ⟨by rw [nextUp_congr c hb.2]; exact hn, a, ?_, Or.inr ⟨?_, hking⟩⟩
      · rw [pileOfTop_congr c hb.1]; exact hp
      · have hh : (u.piles a).hidden = (v.piles a).hidden :=
          congrArg Pile.hidden (congrFun hb.1 a)
        rw [hh]; exact hhid

/-- The maneuver license reads only the board at WF: through the
flat characterization (`canRaiseS_iff`), two WF `boardEq` states
license exactly the same S-raises. -/
private theorem p_canRaiseS_congr {u v : State} (hwfu : u.WF) (hwfv : v.WF)
    (hb : boardEq u v) (c : Card) : CanRaiseS u c ↔ CanRaiseS v c := by
  constructor
  · intro h
    obtain ⟨hn, a, bs, run, hshape, hseat, hdisj⟩ := (canRaiseS_iff hwfu).1 h
    have hf : (u.piles a).faceUp = (v.piles a).faceUp :=
      congrArg Pile.faceUp (congrFun hb.1 a)
    have hh : (u.piles a).hidden = (v.piles a).hidden :=
      congrArg Pile.hidden (congrFun hb.1 a)
    refine (canRaiseS_iff hwfv).2 ⟨by rw [← nextUp_congr c hb.2]; exact hn,
      a, bs, run, by rw [← hf]; exact hshape, ?_, ?_⟩
    · rcases hseat with hbs | ⟨hhid, hking⟩
      · exact Or.inl hbs
      · exact Or.inr ⟨by rw [← hh]; exact hhid, hking⟩
    · rcases hdisj with rfl | htwin
      · exact Or.inl rfl
      · exact Or.inr (by rw [← pileOfTop_congr c.twin hb.1]; exact htwin)
  · intro h
    obtain ⟨hn, a, bs, run, hshape, hseat, hdisj⟩ := (canRaiseS_iff hwfv).1 h
    have hf : (u.piles a).faceUp = (v.piles a).faceUp :=
      congrArg Pile.faceUp (congrFun hb.1 a)
    have hh : (u.piles a).hidden = (v.piles a).hidden :=
      congrArg Pile.hidden (congrFun hb.1 a)
    refine (canRaiseS_iff hwfu).2 ⟨by rw [nextUp_congr c hb.2]; exact hn,
      a, bs, run, by rw [hf]; exact hshape, ?_, ?_⟩
    · rcases hseat with hbs | ⟨hhid, hking⟩
      · exact Or.inl hbs
      · exact Or.inr ⟨by rw [hh]; exact hhid, hking⟩
    · rcases hdisj with rfl | htwin
      · exact Or.inl rfl
      · exact Or.inr (by rw [pileOfTop_congr c.twin hb.1]; exact htwin)

/-- **THE FORK CERTIFICATE IS ARRANGEMENT-ONLY** — a fork witness
at one state re-certifies at any state agreeing with it on piles
and foundations: both conjuncts of the parcel read only the board
(the S-grade through the flat characterization), so the fork
travels the board-thread relation verbatim.  The probe program's
per-board SURVIVES verdicts are all instances of this rod at
decideddistance zero-to-one; the general instances ride the
board-thread replay row below. -/
private theorem p_fork_boardTransfer {u v : State} {x : Card}
    (hwfu : u.WF) (hwfv : v.WF) (hb : boardEq u v)
    (hw : ForkWitness u x) : ForkWitness v x := by
  obtain ⟨hiff, hnt⟩ := hw
  refine ⟨fun c => (hiff c).trans (p_canRaiseS_congr hwfu hwfv hb c), ?_⟩
  intro hcan
  exact hnt ((p_canRaise_congr hb x.twin).mpr hcan)

/-- **THE BOARD-ONLY EXHIBIT REPAIR** — the draw kind's closed
fragment: when the exhibiting play touches no zone cell, the
committed draw cannot disturb it.  The draw writes no pile and
no foundation (`stepDraw_piles` / `stepDraw_found`), so the play
re-runs verbatim from the successor along the board thread
(`board_run_congr`), and the fork certificate travels the thread
(`p_fork_boardTransfer`).  Distance zero, same witness, the
zone-cursor content untouched — the fb1-style "the floor never
rode the eaten cell" shape at the draw kind's own grain. -/
private theorem p_draw_board_repair {s s' F : State} {π : List Move} {x : Card}
    (hwf : s.WF)
    (hstep : State.step s Move.draw = some s')
    (hπ : ∀ m ∈ π, boardMove m)
    (hrun : s.run π = some F)
    (hwit : ForkWitness F x) :
    ∃ (F' : State) (π' : List Move) (x' : Card),
      s'.run π' = some F' ∧ ForkWitness F' x' := by
  have hs : s.stepDraw = some s' := hstep
  have hb : boardEq s s' :=
    ⟨(stepDraw_piles hs).symm, (stepDraw_found hs).symm⟩
  have hwfs' : s'.WF := step_wf hwf hstep
  obtain ⟨F', hrun', hbF, -, -, -, -, -, -⟩ :=
    board_run_congr π hπ s s' hb F hrun
  exact ⟨F', π, x, hrun',
    p_fork_boardTransfer (p_run_wf s π F hrun hwf) (p_run_wf s' π F' hrun' hwfs')
      hbF hwit⟩

/-- **THE SEATING-EAT MIRROR** (the waste-jump seating arm's
distance-one repair) — the mirror image of the waste-eat corridor,
generalized from the probe program's fb2-shape sibling
(`Orig/ForkFloorProbe.lean` §2: the corridor guarded by the eat).
The committed seating `wasteToTab c b` seated the waste head, and
the exhibiting play begins with the OTHER waste letter on the same
head — the founding `wasteToFound c`.  The seating writes no
foundation (`putCard_found`), so the founding's own next-up guard
still reads true at the successor; the seated card TOPS its
landing pile; and the one-move raise `tabToFound c` from the
successor lands the original play's second state EXACTLY — the
inr arm's raise restores the seat-appended pile to its pre-seat
record (`chop_snoc` + `afterRunRemoved_ne`), the inl arm's raise
empties the king seat back to its pre-seat empty record — and the
tail replays verbatim: the SAME fork `F`, exhibited one leg later. -/
private theorem p_waste_seat_mirror {s s' F q₁ : State} {c : Card} {b : Base}
    {τ : List Move} {x : Card}
    (hwf : s.WF)
    (hseat : State.step s (Move.wasteToTab c b) = some s')
    (hfound : State.step s (Move.wasteToFound c) = some q₁)
    (htail : q₁.run τ = some F)
    (hwit : ForkWitness F x) :
    ∃ (F' : State) (π' : List Move) (x' : Card),
      s'.run π' = some F' ∧ ForkWitness F' x' := by
  obtain ⟨hgseat, w, ws, hwaste, hsq⟩ := step_wasteToTab_inv hseat
  obtain ⟨hgeat, w', ws', hwe, hsq₁⟩ := step_wasteToFound_inv hfound
  rw [Bool.and_eq_true] at hgseat hgeat
  -- the two letters name the same waste head (the head is unique)
  obtain ⟨w₀, hw₀⟩ := wasteIs_head hgeat.1
  injection hwaste.symm.trans hw₀ with hwc hws0
  injection hwe.symm.trans hw₀ with hwc' hws0'
  have hc1 : c = w := hwc.symm
  have hc2 : c = w' := hwc'.symm
  have ht1 : w₀ = ws := hws0.symm
  have ht2 : w₀ = ws' := hws0'.symm
  subst hc1
  subst hc2
  subst ht1
  subst ht2
  -- the successor's board reads: found verbatim, nextUp re-read
  have hs'f : s'.found = s.found := by
    rw [hsq]; show (s.putCard c b).found = s.found; exact putCard_found s c b
  have hnext' : s'.nextUp c = true := by
    rw [nextUp_congr (u := s') (v := s) c hs'f]; exact hgeat.2
  have hwfs' : s'.WF := step_wf hwf hseat
  cases b with
  | inl k =>
      obtain ⟨hemp, hking⟩ := canPlace_inl hgseat.2
      rcases hp : s.piles k with ⟨hdk, hfk⟩
      rw [hp] at hemp
      obtain ⟨hhid, hfu⟩ := (Pile.isEmpty_eq _).mp hemp
      have hhdk : hdk = [] := hhid
      have hhfk : hfk = [] := hfu
      subst hhdk
      subst hhfk
      have hpilek : s'.piles k = ⟨[], [c]⟩ := by
        rw [hsq]; show (s.putCard c (Sum.inl k)).piles k = _
        rw [putCard_eq_inl]; exact setPile_piles_self
      have htop' : s'.topOf k = some c := by
        show (s'.piles k).top = some c; rw [hpilek]; rfl
      have hpo' : s'.pileOfTop c = some k :=
        (pileOfTop_eq_some_iff hwfs').2 htop'
      have hsplice := step_tabToFound_splice hnext' hpo'
      have hrest : Pile.afterRunRemoved (s'.piles k)
          (chop (s'.piles k).faceUp) = s.piles k := by
        rw [hpilek, hp]; rfl
      have hstep' : State.step s' (Move.tabToFound c) = some q₁ := by
        rw [hsplice, hsq₁]
        refine congrArg some (State.ext (funext fun σ => ?_)
          (funext fun a => ?_) ?_ ?_ ?_)
        · show (if σ = c.suit then s'.found c.suit ++ [c] else s'.found σ)
            = (if σ = c.suit then s.found c.suit ++ [c] else s.found σ)
          by_cases hσ : σ = c.suit
          · rw [ite_eq_left hσ, ite_eq_left hσ, hs'f]
          · rw [ite_eq_right hσ, ite_eq_right hσ]
            exact congrFun hs'f σ
        · show (if a = k then
              Pile.afterRunRemoved (s'.piles k) (chop (s'.piles k).faceUp)
              else s'.piles a) = s.piles a
          by_cases hak : a = k
          · rw [ite_eq_left hak, hak, hrest]
          · rw [ite_eq_right hak]
            show s'.piles a = s.piles a
            rw [hsq]
            show (s.putCard c (Sum.inl k)).piles a = _
            rw [putCard_eq_inl]
            exact setPile_piles_ne hak
        · show s'.stock = s.stock
          rw [hsq]
          show (s.putCard c (Sum.inl k)).stock = s.stock
          exact putCard_stock s c (Sum.inl k)
        · show s'.waste = w₀
          rw [hsq]
        · show s'.drawStep = s.drawStep
          rw [hsq]
          show (s.putCard c (Sum.inl k)).drawStep = s.drawStep
          exact putCard_drawStep s c (Sum.inl k)
      refine ⟨F, Move.tabToFound c :: τ, x, ?_, hwit⟩
      show (match State.step s' (Move.tabToFound c) with
          | some st' => st'.run τ
          | none => none) = some F
      rw [hstep']; exact htail
  | inr z =>
      obtain ⟨k, hz, -⟩ := canPlace_inr hgseat.2
      have hpilek : s'.piles k
          = { s.piles k with faceUp := (s.piles k).faceUp ++ [c] } := by
        rw [hsq]; show (s.putCard c (Sum.inr z)).piles k = _
        rw [putCard_inr_eq hz]; exact setPile_piles_self
      have hchop : chop (s'.piles k).faceUp = (s.piles k).faceUp := by
        rw [hpilek]
        show chop ((s.piles k).faceUp ++ [c]) = _
        rw [chop_snoc]
      have htop' : s'.topOf k = some c := by
        show (s'.piles k).top = some c; rw [hpilek]; exact lastOf_snoc
      have hpo' : s'.pileOfTop c = some k :=
        (pileOfTop_eq_some_iff hwfs').2 htop'
      have hsplice := step_tabToFound_splice hnext' hpo'
      have hfune : (s.piles k).faceUp ≠ [] := by
        intro hcon
        have htopz : (s.piles k).top = some z := (pileOfTop_top hz).2
        have hlt : (s.piles k).top = lastOf ((s.piles k).faceUp) := rfl
        have hnone : lastOf ([] : List Card) = none := rfl
        rw [hlt, hcon, hnone] at htopz
        exact absurd htopz (by simp)
      have hrest : Pile.afterRunRemoved (s'.piles k)
          (chop (s'.piles k).faceUp) = s.piles k := by
        rw [hchop, afterRunRemoved_ne hfune, hpilek]
      have hstep' : State.step s' (Move.tabToFound c) = some q₁ := by
        rw [hsplice, hsq₁]
        refine congrArg some (State.ext (funext fun σ => ?_)
          (funext fun a => ?_) ?_ ?_ ?_)
        · show (if σ = c.suit then s'.found c.suit ++ [c] else s'.found σ)
            = (if σ = c.suit then s.found c.suit ++ [c] else s.found σ)
          by_cases hσ : σ = c.suit
          · rw [ite_eq_left hσ, ite_eq_left hσ, hs'f]
          · rw [ite_eq_right hσ, ite_eq_right hσ]
            exact congrFun hs'f σ
        · show (if a = k then
              Pile.afterRunRemoved (s'.piles k) (chop (s'.piles k).faceUp)
              else s'.piles a) = s.piles a
          by_cases hak : a = k
          · rw [ite_eq_left hak, hak, hrest]
          · rw [ite_eq_right hak]
            show s'.piles a = s.piles a
            rw [hsq]
            show (s.putCard c (Sum.inr z)).piles a = _
            rw [putCard_inr_eq hz]
            exact setPile_piles_ne hak
        · show s'.stock = s.stock
          rw [hsq]
          show (s.putCard c (Sum.inr z)).stock = s.stock
          exact putCard_stock s c (Sum.inr z)
        · show s'.waste = w₀
          rw [hsq]
        · show s'.drawStep = s.drawStep
          rw [hsq]
          show (s.putCard c (Sum.inr z)).drawStep = s.drawStep
          exact putCard_drawStep s c (Sum.inr z)
      refine ⟨F, Move.tabToFound c :: τ, x, ?_, hwit⟩
      show (match State.step s' (Move.tabToFound c) with
          | some st' => st'.run τ
          | none => none) = some F
      rw [hstep']; exact htail

/-- **THE SUCCESSOR'S OWN FORK** — the decider's own exhibit: when
the successor itself is fork-headed, the empty play exhibits it.
The banked census bridge (`forkStateSB_true_iff`: the `Bool` fold
is the predicate, both ways) plus the witness soundness
(`forkWitnessSB_sound`) hand over the full two-conjunct parcel;
distance zero, at the successor.  This row is the blunt first
branch every per-kind remainder consults: the exhibit's fork never
needs to travel when the landing is itself a fork — the forkless
successor is, in every kind, the residues' sole carried content. -/
private theorem p_successor_fork_repair {s' : State}
    (hwfs' : s'.WF)
    (hfb : forkStateSB s' = true) :
    ∃ (F' : State) (π' : List Move) (x' : Card),
      s'.run π' = some F' ∧ ForkWitness F' x' := by
  obtain ⟨x, hxiff, hxnt⟩ := (forkStateSB_true_iff hwfs').mp hfb
  exact ⟨s', [], x, rfl, ⟨hxiff, hxnt⟩⟩

/-- The board-letter scan for the draw kind's leg-profile split:
true exactly on the three tableau/foundation letters (the
decidable shadow of `boardMove`, `Orig/HostCensus.lean` §9 — the
case read stays choice-free by deciding the profile as a `Bool`
fold, never by pushing a negation through a membership
universal). -/
private def p_boardMoveB (m : Move) : Bool :=
  match m with
  | .tabToFound _ => true
  | .foundToTab _ _ => true
  | .tabToTab _ _ => true
  | _ => false

private theorem p_boardMoveB_true (m : Move) (h : p_boardMoveB m = true) :
    boardMove m := by
  cases m with
  | draw => exact absurd h (by simp [p_boardMoveB])
  | wasteToFound c₀ => exact absurd h (by simp [p_boardMoveB])
  | wasteToTab c₀ b₀ => exact absurd h (by simp [p_boardMoveB])
  | tabToFound c₀ => exact Or.inl ⟨c₀, rfl⟩
  | foundToTab c₀ b₀ => exact Or.inr (Or.inl ⟨c₀, b₀, rfl⟩)
  | tabToTab c₀ b₀ => exact Or.inr (Or.inr ⟨c₀, b₀, rfl⟩)

private theorem p_boardMoveB_of (m : Move) (h : boardMove m) :
    p_boardMoveB m = true := by
  obtain ⟨c₀, hc⟩ | ⟨c₀, b₀, hc⟩ | ⟨c₀, b₀, hc⟩ := h
  · subst hc; rfl
  · subst hc; rfl
  · subst hc; rfl

/-! ### §5.0c. The per-kind one-commit census (this pass)

The PROVED arrangement rows the five named remainders' route-steps 1
consume.  The shared engine is the OFF-RUNG license congruence: two
states that agree on the piles and on every foundation row but one
suit carry IDENTICAL `CanRaiseS`-license worlds off that suit — the
flat `canRaiseS_iff` package's clauses read only the piles, the
top-search (a piles read), and the card's own suit's rung.  Each
committed kind's own row then packages its step's zone/board
arithmetic at theorem grade: the SEAL's write record (the seal rest's
"The Seal's Zone Arithmetic" paragraph, landed), the SEATING's read
census (the covered-top refusal — the guard-refusal transport the
seat rest names — the seated cell's own `nextUp` read, the off-pile
pile and search congruences), the REVEAL's two-cell rung-free write
(the two-cell fact the reveal rest carries as structural prose), and
the BOARD-PREFIX SPLIT the draw rest's residue dispatches on.  No row
here carries an open step; they are the data the repair-time
schedules of the named remainders climb from. -/

/-- The top-search transports over pointwise-equal decide vectors
(the per-file copy at the exact grain the censuses read; template:
`Orig/Twin.lean`'s public `firstWhere_congr`). -/
private theorem p_census_vec {u v : State} (z : Card)
    (hvec : ∀ a, decide (u.topOf a = some z) = decide (v.topOf a = some z)) :
    u.pileOfTop z = v.pileOfTop z := by
  show (firstWhere (fun a => decide (u.topOf a = some z)) Anchor.all) =
    (firstWhere (fun a => decide (v.topOf a = some z)) Anchor.all)
  exact firstWhere_congr hvec

/-- Every test failing gives `none` (the per-file copy of the search's
none-completeness half; template: `Orig/Canonical.lean`'s private
`firstWhere_none_of_all`). -/
private theorem p_census_none {α : Type} (p : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, p x = false) → firstWhere p l = none := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x t ih =>
      intro h
      rw [firstWhere, h x (List.mem_cons.2 (Or.inl rfl)),
        ih (fun y hy => h y (List.mem_cons.2 (Or.inr hy)))]

/-- **THE OFF-RUNG LICENSE CONGRUENCE** [E–M] — two states that agree
on the piles and on every foundation row except (at most) the suit `σ`
carry IDENTICAL `CanRaiseS`-license worlds at every card of every
other suit: the license's flat package reads the piles, the
top-search (a piles read), and the card's own suit's rung — all
verbatim off `σ`.  The seal's census and every future shadow-weld
ride this single engine. -/
private theorem p_license_offRung {u v : State} (σ : Suit)
    (hwfu : u.WF) (hwfv : v.WF)
    (hp : u.piles = v.piles)
    (hf : ∀ σ' : Suit, σ' ≠ σ → u.found σ' = v.found σ') :
    ∀ {e : Card}, e.suit ≠ σ → (CanRaiseS u e ↔ CanRaiseS v e) := by
  intro e he
  have hnu : u.nextUp e = v.nextUp e := by
    show decide (e.rank.toIdx = (u.found e.suit).length)
        = decide (e.rank.toIdx = (v.found e.suit).length)
    rw [hf e.suit he]
  have hpA : ∀ a, u.piles a = v.piles a := fun a => congrFun hp a
  constructor
  · intro hlic
    obtain ⟨hnext, a, bs, run, hshape, hseat, hdisj⟩ :=
      (canRaiseS_iff hwfu).1 hlic
    refine (canRaiseS_iff hwfv).2 ⟨?_, a, bs, run, ?_, ?_, ?_⟩
    · rw [← hnu]; exact hnext
    · rw [← hpA a]; exact hshape
    · rw [← hpA a]; exact hseat
    · rcases hdisj with hrun | hpo
      · exact Or.inl hrun
      · exact Or.inr (by rw [← p_pileOfTop_congr e.twin hp]; exact hpo)
  · intro hlic
    obtain ⟨hnext, a, bs, run, hshape, hseat, hdisj⟩ :=
      (canRaiseS_iff hwfv).1 hlic
    refine (canRaiseS_iff hwfu).2 ⟨?_, a, bs, run, ?_, ?_, ?_⟩
    · rw [hnu]; exact hnext
    · rw [hpA a]; exact hshape
    · rw [hpA a]; exact hseat
    · rcases hdisj with hrun | hpo
      · exact Or.inl hrun
      · exact Or.inr (by rw [p_pileOfTop_congr e.twin hp]; exact hpo)

/-- **THE SEAL'S ZONE ARITHMETIC** [E] — the committed waste
founding's full write record, at theorem grade: piles and stock
untouched, the waste popped by the sealed head, every foundation row
but the sealed suit VERBATIM, and the sealed suit's row grown by
exactly the sealed card (its rung one higher).  Together with the
off-rung congruence this PINS the seal's license conflict to the
sealed suit's frontier cell alone — the datum the seal rest's route
step 1 prices, and the arithmetic `SlabEquiv.cycle_zone_pin`'s
two-zone world sits behind through the step's own zone rows. -/
private theorem p_seal_zone_rows {s s' : State} {c : Card}
    (hstep : State.step s (Move.wasteToFound c) = some s') :
    s'.piles = s.piles ∧ s'.stock = s.stock ∧
      ∃ xs, s'.waste = xs ∧ s.waste = c :: xs ∧
        (∀ σ' : Suit, σ' ≠ c.suit → s'.found σ' = s.found σ') ∧
        s'.found c.suit = s.found c.suit ++ [c] := by
  obtain ⟨hg, w, ws, hwaste, hs⟩ := step_wasteToFound_inv hstep
  rw [Bool.and_eq_true] at hg
  have hw2 : w = c := State.wasteIs_head_eq hwaste hg.1
  rw [hw2] at hwaste
  rw [hs]
  refine ⟨?_, ?_, ws, rfl, hwaste, ?_, ?_⟩
  · show (s.setFound c.suit (s.found c.suit ++ [c])).piles = s.piles
    exact setFound_piles s c.suit (s.found c.suit ++ [c])
  · show (s.setFound c.suit (s.found c.suit ++ [c])).stock = s.stock
    exact setFound_stock s c.suit (s.found c.suit ++ [c])
  · intro σ' hσ'
    show (s.setFound c.suit (s.found c.suit ++ [c])).found σ'
        = s.found σ'
    exact setFound_found_ne hσ'
  · show (s.setFound c.suit (s.found c.suit ++ [c])).found c.suit
         = s.found c.suit ++ [c]
    exact setFound_found_self

/-- **THE SHADOW-THREAD LEG CLASS** (the seal's head-replay spine):
a leg is SHADOW-CLEAN at the sealed suit when its guards read no
sealed row and no zone cell — the three board letters whose raise /
pull cards avoid the sealed suit (their guards read piles and the
card's own suit's row only), and every cargo slide (rung-free by
`p_reveal_rung`'s own census).  The dirty legs are the draws, the
waste letters (zone consults on the popped head), and the sealed-suit
raises/pulls (rung consults against the shadow's one-ahead row). -/
private def p_shadowLeg (z : Suit) (m : Move) : Bool :=
  match m with
  | .draw => false
  | .wasteToFound _ => false
  | .wasteToTab _ _ => false
  | .tabToFound c => decide (c.suit ≠ z)
  | .foundToTab c _ => decide (c.suit ≠ z)
  | .tabToTab _ _ => true

/-- **THE SHADOW-PREFIX SPLIT** [E] — every play splits as a
shadow-clean prefix (possibly empty) followed by its end or the
FIRST DIRTY LEG (the first leg whose guard consults the sealed row
or the popped zone).  The structural fact the seal rest's new spine
rides. -/
private theorem p_shadow_prefix_split (z : Suit) : ∀ (l : List Move),
    ∃ C D, l = C ++ D ∧ C.all (p_shadowLeg z) = true ∧
      (D = [] ∨ (∃ d D', D = d :: D' ∧ p_shadowLeg z d = false)) := by
  intro l
  induction l with
  | nil => exact ⟨[], [], rfl, rfl, Or.inl rfl⟩
  | cons m t ih =>
      obtain ⟨C, D, hsplit, hC, hD⟩ := ih
      cases hm : p_shadowLeg z m with
      | true =>
          refine ⟨m :: C, D, ?_, ?_, hD⟩
          · rw [hsplit]; rfl
          · exact List.all_eq_true.mpr (fun x hx => by
              rcases List.mem_cons.1 hx with rfl | hmem
              · exact hm
              · exact List.all_eq_true.mp hC x hmem)
      | false => exact ⟨[], m :: t, rfl, rfl, Or.inr ⟨m, t, rfl, hm⟩⟩

/-- The pointwise `setPile` congruence (the per-file copy; template:
HostCensus's private `setPile_piles_aux`). -/
private theorem p_setPile_piles_aux {x y : State} (hp : x.piles = y.piles)
    (a : Anchor) (p p' : Pile) (hpp : p = p') (a' : Anchor) :
    (x.setPile a p).piles a' = (y.setPile a p').piles a' := by
  by_cases h : a' = a
  · rw [h]
    show (if a = a then p else x.piles a) = (if a = a then p' else y.piles a)
    rw [ite_eq_left rfl, ite_eq_left rfl, hpp]
  · show (if a' = a then p else x.piles a') = (if a' = a then p' else y.piles a')
    rw [ite_eq_right h, ite_eq_right h, congrFun hp a']

/-- **THE CARGO-SLIDE STEP SPLICE** (the per-file copy; template:
HostCensus's private `step_tabToTab_succ` — none of Play's public
splices covers this arm): the located, legal, run-shaped slide is
the exact `setPile`-then-`putRun` record. -/
private theorem p_step_tabToTab_succ {st : State} {c : Card} {b : Base}
    {a : Anchor} {r : Card} {rr : List Card}
    (hh : st.pileHolding c = some a)
    (hcp : st.canPlace c b = true)
    (hfc : fromCard c (st.piles a).faceUp = r :: rr) :
    State.step st (Move.tabToTab c b) =
      some ((st.setPile a
        (Pile.afterRunRemoved (st.piles a)
          (below c (st.piles a).faceUp))).putRun (r :: rr) b) := by
  have hR : State.step st (Move.tabToTab c b) =
      some ((st.setPile a
        (Pile.afterRunRemoved (st.piles a)
          (below c (st.piles a).faceUp))).putRun (r :: rr) b) := by
    simp only [State.step, hh, hcp, hfc]
    rfl
  rw [hR]

/-- The `putRun` tableau is determined by the pre-state's tableau
(the per-file copy of the `putCard` congruence row's pattern). -/
private theorem p_putRun_piles_congr {x y : State} {run : List Card} {b : Base}
    (hp : x.piles = y.piles) :
    (x.putRun run b).piles = (y.putRun run b).piles := by
  cases b with
  | inl n => rw [putRun_eq_inl, putRun_eq_inl, setPile_piles, setPile_piles, hp]
  | inr z =>
      have hc : y.pileOfTop z = x.pileOfTop z := (p_pileOfTop_congr z hp).symm
      cases hx : x.pileOfTop z with
      | none =>
          rw [show x.putRun run (Sum.inr z) = x from by
              simp only [State.putRun, hx],
            show y.putRun run (Sum.inr z) = y from by
              simp only [State.putRun, hc, hx],
            hp]
      | some k =>
          rw [show x.putRun run (Sum.inr z)
                = x.setPile k { x.piles k with faceUp := (x.piles k).faceUp ++ run } from by
              simp only [State.putRun, hx],
            show y.putRun run (Sum.inr z)
                = y.setPile k { y.piles k with faceUp := (y.piles k).faceUp ++ run } from by
              simp only [State.putRun, hc, hx],
            setPile_piles, setPile_piles, hp]

/-- **THE SHADOW-THREAD SHAPE** — the read-world the seal's mirror
maintains between the origin thread `P` (the original play's landing,
with the sealed card still IN THE WASTE) and the successor thread `Q`
(the committed seal's mirror, with the sealed card FOUNDED one rung
high): agreeing piles, agreeing foundation rows at every suit but
the sealed one, the sealed rows pinned at the two threads' own base
records, and the origin thread's waste verbatim (the popped head
still resident there). -/
private def p_shadowShape (s s' : State) (c : Card) (P Q : State) : Prop :=
  P.piles = Q.piles ∧
    (∀ σ' : Suit, σ' ≠ c.suit → P.found σ' = Q.found σ') ∧
    P.found c.suit = s.found c.suit ∧
    Q.found c.suit = s'.found c.suit ∧
    P.waste = s.waste

/-- **THE SHADOW STEP** [E–M] — the mirror of one shadow-clean leg:
a legal clean letter at the origin thread re-fires VERBATIM at the
successor thread (its guards read only the agreeing piles and the
card's own off-sealed row), and the landing pair carries the same
read-world (the write is the same function of the agreeged data:
piles verbatim, the written row off the sealed suit, the sealed rows
untouched, the waste verbatim on the origin thread). -/
private theorem p_shadow_step {s s' : State} {c : Card} {m : Move}
    {P Q P₁ : State}
    (hthr : p_shadowLeg c.suit m = true)
    (hsh : p_shadowShape s s' c P Q)
    (hstep : State.step P m = some P₁) :
    ∃ Q₁, State.step Q m = some Q₁ ∧ p_shadowShape s s' c P₁ Q₁ := by
  obtain ⟨hPp, hR, hPs, hQs, hPw⟩ := hsh
  cases m with
  | draw => exact absurd hthr (by simp [p_shadowLeg])
  | wasteToFound c₀ => exact absurd hthr (by simp [p_shadowLeg])
  | wasteToTab c₀ b₀ => exact absurd hthr (by simp [p_shadowLeg])
  | tabToTab e b =>
      obtain ⟨a, hh, hcp, hne, hs⟩ := step_tabToTab_inv hstep
      have hva' : P.piles a = Q.piles a := congrFun hPp a
      have hhQ : Q.pileHolding e = some a := by
        rw [show Q.pileHolding e = P.pileHolding e from
          pileHolding_congr (st := P) (s' := Q) hPp.symm]
        exact hh
      have hcpQ : Q.canPlace e b = true := by
        rw [← p_canPlace_congr e b hPp]
        exact hcp
      cases hrun : fromCard e (P.piles a).faceUp with
      | nil =>
          rw [hrun] at hne
          exact absurd hne (by simp)
      | cons r rr =>
          rw [hrun] at hs
          have hfcQ : fromCard e (Q.piles a).faceUp = r :: rr := by
            rw [show (Q.piles a).faceUp = (P.piles a).faceUp from
              (congrArg Pile.faceUp hva').symm]
            exact hrun
          have hfP : P₁.found = P.found := by
            rw [hs]
            show ((P.setPile a
              (Pile.afterRunRemoved (P.piles a)
                (below e (P.piles a).faceUp))).putRun (r :: rr) b).found
              = P.found
            rw [putRun_keep.1, setPile_found]
          have hfQ : ((Q.setPile a
              (Pile.afterRunRemoved (Q.piles a)
                (below e (Q.piles a).faceUp))).putRun (r :: rr) b).found
              = Q.found := by
            show ((Q.setPile a
              (Pile.afterRunRemoved (Q.piles a)
                (below e (Q.piles a).faceUp))).putRun (r :: rr) b).found
              = Q.found
            rw [putRun_keep.1, setPile_found]
          have hwP : P₁.waste = P.waste := by
            rw [hs]
            show ((P.setPile a
              (Pile.afterRunRemoved (P.piles a)
                (below e (P.piles a).faceUp))).putRun (r :: rr) b).waste
              = P.waste
            rw [putRun_keep.2.2.1, setPile_waste]
          refine ⟨(Q.setPile a
              (Pile.afterRunRemoved (Q.piles a)
                (below e (Q.piles a).faceUp))).putRun (r :: rr) b, ?_, ?_⟩
          · exact p_step_tabToTab_succ hhQ hcpQ hfcQ
          · refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · have hpair : (P.setPile a
                  (Pile.afterRunRemoved (P.piles a)
                    (below e (P.piles a).faceUp))).piles
                  = (Q.setPile a
                    (Pile.afterRunRemoved (Q.piles a)
                      (below e (Q.piles a).faceUp))).piles := by
                funext a'
                exact p_setPile_piles_aux hPp a
                  (Pile.afterRunRemoved (P.piles a)
                    (below e (P.piles a).faceUp))
                  (Pile.afterRunRemoved (Q.piles a)
                    (below e (Q.piles a).faceUp))
                  (by rw [hva']) a'
              funext a'
              rw [hs]
              exact congrFun (p_putRun_piles_congr hpair) a'
            · intro σ' hσ'
              rw [show P₁.found σ' = P.found σ' from congrFun hfP σ',
                  show ((Q.setPile a
                    (Pile.afterRunRemoved (Q.piles a)
                      (below e (Q.piles a).faceUp))).putRun (r :: rr) b).found σ'
                    = Q.found σ' from congrFun hfQ σ']
              exact hR σ' hσ'
            · rw [show P₁.found c.suit = P.found c.suit from congrFun hfP c.suit]
              exact hPs
            · rw [show ((Q.setPile a
                  (Pile.afterRunRemoved (Q.piles a)
                    (below e (Q.piles a).faceUp))).putRun (r :: rr) b).found c.suit
                   = Q.found c.suit from congrFun hfQ c.suit]
              exact hQs
            · exact hwP.trans hPw
  | tabToFound e =>
      have hne : e.suit ≠ c.suit := by
        simp only [p_shadowLeg] at hthr
        exact of_decide_eq_true hthr
      obtain ⟨hn, a, hpo, hs⟩ := step_tabToFound_inv hstep
      have hnQ : Q.nextUp e = true := by
        show decide (e.rank.toIdx = (Q.found e.suit).length) = true
        rw [show Q.found e.suit = P.found e.suit from (hR e.suit hne).symm]
        exact hn
      have hpoQ : Q.pileOfTop e = some a := (p_pileOfTop_congr e hPp).symm.trans hpo
      refine ⟨{ Q.setFound e.suit (Q.found e.suit ++ [e]) with
          piles := fun a' =>
            if a' = a then
              Pile.afterRunRemoved (Q.piles a) (chop (Q.piles a).faceUp)
            else Q.piles a' }, ?_, ?_⟩
      · exact step_tabToFound_splice hnQ hpoQ
      · refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · funext a'
          rw [hs]
          show (if a' = a then
              Pile.afterRunRemoved (P.piles a) (chop (P.piles a).faceUp)
            else P.piles a')
              = (if a' = a then
              Pile.afterRunRemoved (Q.piles a) (chop (Q.piles a).faceUp)
            else Q.piles a')
          by_cases ha : a' = a
          · rw [ha, ite_eq_left rfl, ite_eq_left rfl]
            rw [congrFun hPp a]
          · rw [ite_eq_right ha, ite_eq_right ha]
            exact congrFun hPp a'
        · intro σ' hσ'
          rw [hs]
          show (if σ' = e.suit then P.found e.suit ++ [e] else P.found σ')
              = (if σ' = e.suit then Q.found e.suit ++ [e] else Q.found σ')
          by_cases hse : σ' = e.suit
          · rw [hse, ite_eq_left rfl, ite_eq_left rfl]
            rw [hR e.suit hne]
          · rw [ite_eq_right hse, ite_eq_right hse]
            exact hR σ' hσ'
        · rw [hs]
          show (if c.suit = e.suit then P.found e.suit ++ [e] else P.found c.suit)
              = s.found c.suit
          rw [ite_eq_right (fun hcon => hne hcon.symm)]
          exact hPs
        · show (if c.suit = e.suit then Q.found e.suit ++ [e] else Q.found c.suit)
              = s'.found c.suit
          rw [ite_eq_right (fun hcon => hne hcon.symm)]
          exact hQs
        · rw [hs]
          show P.waste = s.waste
          exact hPw
  | foundToTab e b =>
      have hne : e.suit ≠ c.suit := by
        simp only [p_shadowLeg] at hthr
        exact of_decide_eq_true hthr
      obtain ⟨c₀, htop, hc₀c, hcp, hs⟩ := step_foundToTab_inv hstep
      rw [hc₀c] at htop
      have htopQ : Q.foundTop e.suit = some e := by
        show lastOf (Q.found e.suit) = some e
        rw [show Q.found e.suit = P.found e.suit from (hR e.suit hne).symm]
        exact htop
      have hcpQ : Q.canPlace e b = true := by
        rw [← p_canPlace_congr e b hPp]
        exact hcp
      refine ⟨(Q.setFound e.suit (chop (Q.found e.suit))).putCard e b, ?_, ?_⟩
      · exact step_foundToTab_splice htopQ hcpQ
      · refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · have hp2 : (P.setFound e.suit (chop (P.found e.suit))).piles
              = (Q.setFound e.suit (chop (Q.found e.suit))).piles := by
            show P.piles = Q.piles
            exact hPp
          rw [hs]
          exact p_putCard_piles_congr e b hp2
        · intro σ' hσ'
          rw [hs]
          rw [show ((P.setFound e.suit (chop (P.found e.suit))).putCard e b).found σ'
                = (P.setFound e.suit (chop (P.found e.suit))).found σ' from
              congrFun (putCard_keep (st := P.setFound e.suit
                (chop (P.found e.suit))) (c := e) (b := b)).1 σ',
            show ((Q.setFound e.suit (chop (Q.found e.suit))).putCard e b).found σ'
                = (Q.setFound e.suit (chop (Q.found e.suit))).found σ' from
              congrFun (putCard_keep (st := Q.setFound e.suit
                (chop (Q.found e.suit))) (c := e) (b := b)).1 σ']
          show (if σ' = e.suit then chop (P.found e.suit) else P.found σ')
              = (if σ' = e.suit then chop (Q.found e.suit) else Q.found σ')
          by_cases hse : σ' = e.suit
          · rw [hse, ite_eq_left rfl, ite_eq_left rfl]
            rw [hR e.suit hne]
          · rw [ite_eq_right hse, ite_eq_right hse]
            exact hR σ' hσ'
        · rw [hs]
          rw [show ((P.setFound e.suit (chop (P.found e.suit))).putCard e b).found c.suit
                = (P.setFound e.suit (chop (P.found e.suit))).found c.suit from
              congrFun (putCard_keep (st := P.setFound e.suit
                (chop (P.found e.suit))) (c := e) (b := b)).1 c.suit]
          show (if c.suit = e.suit then chop (P.found e.suit) else P.found c.suit)
              = s.found c.suit
          rw [ite_eq_right (fun hcon => hne hcon.symm)]
          exact hPs
        · rw [show ((Q.setFound e.suit (chop (Q.found e.suit))).putCard e b).found c.suit
              = (Q.setFound e.suit (chop (Q.found e.suit))).found c.suit from
            congrFun (putCard_keep (st := Q.setFound e.suit
              (chop (Q.found e.suit))) (c := e) (b := b)).1 c.suit]
          show (if c.suit = e.suit then chop (Q.found e.suit) else Q.found c.suit)
              = s'.found c.suit
          rw [ite_eq_right (fun hcon => hne hcon.symm)]
          rw [show Q.found c.suit = s'.found c.suit from hQs]
        · rw [hs]
          rw [show ((P.setFound e.suit (chop (P.found e.suit))).putCard e b).waste
                = (P.setFound e.suit (chop (P.found e.suit))).waste from
              (putCard_keep (st := P.setFound e.suit
                (chop (P.found e.suit))) (c := e) (b := b)).2.2.1]
          show P.waste = s.waste
          exact hPw

/-- **THE SHADOW RUN** [E–M] — the mirror of a whole shadow-clean
play: what the origin thread runs, the successor thread runs too,
landing the read-world's mirror. -/
private theorem p_shadow_run {s s' : State} {c : Card} :
    ∀ (l : List Move), l.all (p_shadowLeg c.suit) = true →
      ∀ {P Q W : State}, P.run l = some W → p_shadowShape s s' c P Q →
        ∃ W', Q.run l = some W' ∧ p_shadowShape s s' c W W' := by
  intro l
  induction l with
  | nil =>
      intro _ P Q W hrun hsh
      injection hrun with hPW
      subst hPW
      exact ⟨Q, rfl, hsh⟩
  | cons m rest ih =>
      intro hall P Q W hrun hsh
      obtain ⟨P₁, hm, hrest⟩ := State.run_cons hrun
      obtain ⟨Q₁, hQm⟩ :=
        p_shadow_step (List.all_eq_true.mp hall m (List.mem_cons_self ..)) hsh hm
      obtain ⟨W', hrest', hsh'⟩ :=
        ih (List.all_eq_true.mpr (fun y hy =>
          List.all_eq_true.mp hall y (List.mem_cons.2 (Or.inr hy))))
          hrest hQm.2
      exact ⟨W', by
        show (match State.step Q m with
            | some st' => st'.run rest
            | none => none) = some W'
        rw [show State.step Q m = some Q₁ from hQm.1]
        exact hrest', hsh'⟩

/-- **THE VANILLA LICENSE IS OFF-RUNG-ONLY TOO** [E–M] — the vanilla
raise reads the card's own suit's rung and the piles alone, so the
off-rung congruence carries it verbatim at every card of every other
suit. -/
private theorem p_canRaise_offRung {u v : State} (σ : Suit)
    (hp : u.piles = v.piles)
    (hf : ∀ σ' : Suit, σ' ≠ σ → u.found σ' = v.found σ') :
    ∀ {e : Card}, e.suit ≠ σ → (CanRaise u e ↔ CanRaise v e) := by
  intro e he
  have hva : ∀ a : Anchor, u.piles a = v.piles a := fun a => congrFun hp a
  have hvf : ∀ a : Anchor, (v.piles a).faceUp = (u.piles a).faceUp :=
    fun a => (congrArg Pile.faceUp (hva a)).symm
  have hvh : ∀ a : Anchor, (v.piles a).hidden = (u.piles a).hidden :=
    fun a => (congrArg Pile.hidden (hva a)).symm
  constructor
  · rintro ⟨hn, a, hpo, (hbs | ⟨hhid, hking⟩)⟩
    · have hnV : v.nextUp e = true := by
        show decide (e.rank.toIdx = (v.found e.suit).length) = true
        rw [(hf e.suit he).symm]
        exact hn
      have hpoV : v.pileOfTop e = some a := by
        rw [show v.pileOfTop e = u.pileOfTop e from
          (p_pileOfTop_congr e hp).symm]
        exact hpo
      exact ⟨hnV, a, hpoV, Or.inl (by
        rw [show chop (v.piles a).faceUp = chop (u.piles a).faceUp from
          congrArg chop (hvf a)]
        exact hbs)⟩
    · have hnV : v.nextUp e = true := by
        show decide (e.rank.toIdx = (v.found e.suit).length) = true
        rw [(hf e.suit he).symm]
        exact hn
      have hpoV : v.pileOfTop e = some a := by
        rw [show v.pileOfTop e = u.pileOfTop e from
          (p_pileOfTop_congr e hp).symm]
        exact hpo
      exact ⟨hnV, a, hpoV, Or.inr ⟨by
        rw [show (v.piles a).hidden = (u.piles a).hidden from hvh a]
        exact hhid, hking⟩⟩
  · rintro ⟨hn, a, hpo, (hbs | ⟨hhid, hking⟩)⟩
    · have hnU : u.nextUp e = true := by
        show decide (e.rank.toIdx = (u.found e.suit).length) = true
        rw [hf e.suit he]
        exact hn
      have hpoU : u.pileOfTop e = some a := by
        rw [show u.pileOfTop e = v.pileOfTop e from p_pileOfTop_congr e hp]
        exact hpo
      exact ⟨hnU, a, hpoU, Or.inl (by
        rw [show chop (u.piles a).faceUp = chop (v.piles a).faceUp from
          congrArg chop (hvf a).symm]
        exact hbs)⟩
    · have hnU : u.nextUp e = true := by
        show decide (e.rank.toIdx = (u.found e.suit).length) = true
        rw [hf e.suit he]
        exact hn
      have hpoU : u.pileOfTop e = some a := by
        rw [show u.pileOfTop e = v.pileOfTop e from p_pileOfTop_congr e hp]
        exact hpo
      exact ⟨hnU, a, hpoU, Or.inr ⟨by
        rw [show (u.piles a).hidden = (v.piles a).hidden from (hvh a).symm]
        exact hhid, hking⟩⟩

/-- **THE OFF-RUNG CERTIFICATE TRANSFER** [M] — the fork certificate
travels the shadow thread at a witness whose whole pair avoids the
sealed suit: both conjuncts of the parcel read the piles and the
off-sealed rungs only (`p_license_offRung` for the S-world, the row
above for the vanilla pin), and the sealed-suit cards are priced
dead at the shadow landing by the scan. -/
private theorem p_fork_offRung_transfer {P Q : State} {x : Card} {σ : Suit}
    (hwfP : P.WF) (hwfQ : Q.WF)
    (hp : P.piles = Q.piles)
    (hf : ∀ σ' : Suit, σ' ≠ σ → P.found σ' = Q.found σ')
    (hx : x.suit ≠ σ) (hxT : x.twin.suit ≠ σ)
    (hdead : ∀ e, e.suit = σ → ¬ CanRaiseS Q e)
    (hwit : ForkWitness P x) : ForkWitness Q x := by
  obtain ⟨hiff, hnt⟩ := hwit
  have hoffS : ∀ {e : Card}, e.suit ≠ σ → (CanRaiseS P e ↔ CanRaiseS Q e) :=
    p_license_offRung σ hwfP hwfQ hp hf
  have hoffV : ∀ {e : Card}, e.suit ≠ σ → (CanRaise P e ↔ CanRaise Q e) :=
    p_canRaise_offRung σ hp hf
  refine ⟨fun c₀ => ⟨fun hmem => ?_, fun hS₀ => ?_⟩, ?_⟩
  · rcases hmem with h | h
    · rw [h]
      exact (hoffS hx).mp ((hiff x).mp (Or.inl rfl))
    · rw [h]
      exact (hoffS hxT).mp ((hiff x.twin).mp (Or.inr rfl))
  · rcases Decidable.em (c₀.suit = σ) with hs | hs
    · exact absurd hS₀ (hdead c₀ hs)
    · rcases (hiff c₀).mpr ((hoffS hs).mpr hS₀) with h | h
      · exact Or.inl h
      · exact Or.inr h
  · intro hcr
    exact hnt ((hoffV hxT).mpr hcr)

/-- **THE SEATING WRITE RECORD, EMPTY-ANCHOR ARM** [E] — the committed
seating onto the empty anchor `k`: the guard demands a king and an
empty seat; the successor keeps the foundations and every other pile
VERBATIM, and the written pile is the king's bare singleton record. -/
private theorem p_seat_inl_records {s s' : State} {c : Card} {k : Anchor}
    (hstep : State.step s (Move.wasteToTab c (Sum.inl k)) = some s') :
    (s.piles k).isEmpty = true ∧ c.rank = Rank.king ∧ s'.found = s.found ∧
      (∀ a, a ≠ k → s'.piles a = s.piles a) ∧
      s'.piles k = ⟨[], [c]⟩ := by
  obtain ⟨hg, w, _, hwaste, hs⟩ := step_wasteToTab_inv hstep
  rw [Bool.and_eq_true] at hg
  have hw2 : w = c := State.wasteIs_head_eq hwaste hg.1
  rw [hw2] at hwaste
  obtain ⟨hemp, hking⟩ := canPlace_inl hg.2
  refine ⟨hemp, hking, ?_, ?_, ?_⟩
  · rw [hs]
    show (s.putCard c (Sum.inl k)).found = s.found
    exact putCard_found s c (Sum.inl k)
  · intro a ha
    rw [hs]
    show (s.putCard c (Sum.inl k)).piles a = s.piles a
    rw [putCard_eq_inl]
    show (if a = k then (⟨[], [c]⟩ : Pile) else s.piles a) = s.piles a
    rw [ite_eq_right ha]
  · rw [hs]
    show (s.putCard c (Sum.inl k)).piles k = ⟨[], [c]⟩
    rw [putCard_eq_inl]
    exact setPile_piles_self

/-- **THE SEATING WRITE RECORD, CARD-HOST ARM** [E] — the committed
seating onto the card host `z`: the successor keeps the foundations
and every other pile VERBATIM, and the written pile is the host's own
record with the seated card appended at its top. -/
private theorem p_seat_inr_records {s s' : State} {c z : Card}
    (hstep : State.step s (Move.wasteToTab c (Sum.inr z)) = some s') :
    ∃ k : Anchor, s.pileOfTop z = some k ∧ canSitOn c z = true ∧
      s'.found = s.found ∧
      (∀ a, a ≠ k → s'.piles a = s.piles a) ∧
      s'.piles k = { s.piles k with faceUp := (s.piles k).faceUp ++ [c] } := by
  obtain ⟨hg, w, _, hwaste, hs⟩ := step_wasteToTab_inv hstep
  rw [Bool.and_eq_true] at hg
  have hw2 : w = c := State.wasteIs_head_eq hwaste hg.1
  rw [hw2] at hwaste
  obtain ⟨k, hpo, hfil⟩ := canPlace_inr hg.2
  refine ⟨k, hpo, hfil, ?_, ?_, ?_⟩
  · rw [hs]
    show (s.putCard c (Sum.inr z)).found = s.found
    exact putCard_found s c (Sum.inr z)
  · intro a ha
    rw [hs]
    show (s.putCard c (Sum.inr z)).piles a = s.piles a
    rw [putCard_inr_eq hpo]
    show (if a = k then
        { (s.piles k) with faceUp := (s.piles k).faceUp ++ [c] } else s.piles a)
        = s.piles a
    rw [ite_eq_right ha]
  · rw [hs]
    show (s.putCard c (Sum.inr z)).piles k = _
    rw [putCard_inr_eq hpo]
    exact setPile_piles_self

/-- **THE SEATED CELL** [E–M] — after the committed seating, the
seated card TOPS its landing pile over a surviving seat (the
card-host arm's below-part, or its own bare-king record at the empty
anchor, both read off the write record): the flat package's seat
clause resolves TRUE on the commit's own write, so the seated card's
S-license at the successor is EXACTLY its (unchanged) `nextUp` read —
the hot question alone remains. -/
private theorem p_seat_gain {s s' : State} {c : Card} {b : Base}
    (hwf : s.WF) (hstep : State.step s (Move.wasteToTab c b) = some s')
    (hn : s.nextUp c = true) : CanRaiseS s' c := by
  have hwfs' : s'.WF := step_wf hwf hstep
  cases b with
  | inl k =>
      obtain ⟨-, hking, hs'f, -, hpilek⟩ := p_seat_inl_records hstep
      have hnext : s'.nextUp c = true := by
        rw [nextUp_congr c hs'f]; exact hn
      exact (canRaiseS_iff hwfs').2 ⟨hnext, k, [], [],
        by rw [hpilek]; rfl,
        Or.inr ⟨by rw [hpilek], hking⟩, Or.inl rfl⟩
  | inr z =>
      obtain ⟨k, hpo, -, hs'f, -, hpilek⟩ := p_seat_inr_records hstep
      have hnext : s'.nextUp c = true := by
        rw [nextUp_congr c hs'f]; exact hn
      exact (canRaiseS_iff hwfs').2 ⟨hnext, k, (s.piles k).faceUp, [],
        by rw [hpilek],
        Or.inl (pileOfTop_top hpo).1, Or.inl rfl⟩

/-- **THE COVERED-TOP REFUSAL** [M] — after the committed seating onto
the card host `z`, NO placement consult can ever again aim at `z`:
the seat write covered the ONE pile that topped it (a card tops at
most one pile at a WF state), so the top-search at the successor
returns `none` and the card-hosted placement guard refuses every
mover.  THE GUARD-REFUSAL TRANSPORT of the seating arm — the probe
program's junk-cell refusal verdicts made theorem-grade, and the
datum the seat rest's guard-refusal route prices. -/
private theorem p_seat_refusal_cover {s s' : State} {c z : Card}
    (hwf : s.WF) (hstep : State.step s (Move.wasteToTab c (Sum.inr z)) = some s')
    (e : Card) : s'.canPlace e (Sum.inr z) = false := by
  obtain ⟨k, hpo, hfil, -, hpA, hpilek⟩ := p_seat_inr_records hstep
  have hcne : c ≠ z := ne_of_canSitOn hfil
  have htopz : (s.piles k).top = some z := (pileOfTop_top hpo).2
  have hzmem : z ∈ (s.piles k).faceUp := lastOf_mem htopz
  have hzno : ∀ a', a' ≠ k → z ∉ (s.piles a').faceUp :=
    fun a' ha' => (mem_faceUp_unique hwf hzmem a' ha').1
  have hnone : s'.pileOfTop z = none := by
    show (firstWhere (fun a => decide (s'.topOf a = some z)) Anchor.all) = none
    refine p_census_none _ Anchor.all ?_
    intro a _
    by_cases hak : a = k
    · rw [hak]
      show decide ((s'.piles k).top = some z) = false
      have h1 : (s'.piles k).top = some c := by
        rw [hpilek]; exact lastOf_snoc
      rw [h1]
      exact decide_false_of_not (fun hcon => hcne (Option.some.inj hcon) :
        ¬((some c : Option Card) = some z))
    · show decide ((s'.piles a).top = some z) = false
      rw [hpA a hak]
      exact decide_false_of_not
        (fun hcon => hzno a hak (lastOf_mem hcon) :
          ¬((s.piles a).top = some z))
  show (match s'.pileOfTop z with
      | some _ => canSitOn e z
      | none => false) = false
  rw [hnone]

/-- **THE SEATING READ CENSUS, EMPTY-ANCHOR ARM** [E–M] — off the
written pile every read is verbatim, and the top-search answers the
same at every card except the seated one (whose top was BORN at the
write): foundations, rungs, piles, and all searches off `c` carry
across the commit unchanged. -/
private theorem p_seat_reads_inl {s s' : State} {c : Card} {k : Anchor}
    (hstep : State.step s (Move.wasteToTab c (Sum.inl k)) = some s') :
    s'.found = s.found ∧ (∀ d : Card, s'.nextUp d = s.nextUp d) ∧
      (∀ a, a ≠ k → s'.piles a = s.piles a) ∧ s'.piles k = ⟨[], [c]⟩ ∧
      ∀ w : Card, w ≠ c → s'.pileOfTop w = s.pileOfTop w := by
  obtain ⟨hemp, -, hs'f, hpA, hpilek⟩ := p_seat_inl_records hstep
  obtain ⟨-, hfu⟩ := (Pile.isEmpty_eq _).mp hemp
  have hvec : ∀ w : Card, w ≠ c →
      (∀ a, decide (s'.topOf a = some w) = decide (s.topOf a = some w)) := by
    intro w hwW a
    by_cases hak : a = k
    · rw [hak]
      show decide ((s'.piles k).top = some w) = decide ((s.piles k).top = some w)
      have h1 : (s'.piles k).top = some c := by
        rw [hpilek]
        rfl
      have h2 : (s.piles k).top = none := by
        show lastOf (s.piles k).faceUp = none
        rw [hfu]
        rfl
      rw [h1, h2,
        decide_false_of_not
          (fun hcon : (some c : Option Card) = some w =>
            hwW (Option.some.inj hcon).symm),
        decide_false_of_not
          (fun hcon : (none : Option Card) = some w => nomatch hcon)]
    · show decide ((s'.piles a).top = some w)
          = decide ((s.piles a).top = some w)
      rw [hpA a hak]
  exact ⟨hs'f, fun d => nextUp_congr d hs'f, hpA, hpilek,
    fun w hwW => p_census_vec w (hvec w hwW)⟩

/-- **THE SEATING READ CENSUS, CARD-HOST ARM** [E–M] — the same read
world as the empty-anchor arm, with the search exceptions now TWO
named cells: the seated card `c` (its top born at the written pile)
and the covered host `z` (its one top dead there); off {c, z} every
search reads verbatim across the commit. -/
private theorem p_seat_reads_inr {s s' : State} {c z : Card}
    (hstep : State.step s (Move.wasteToTab c (Sum.inr z)) = some s') :
    s'.found = s.found ∧ (∀ d : Card, s'.nextUp d = s.nextUp d) ∧
      (∃ k, s.pileOfTop z = some k ∧
        (∀ a, a ≠ k → s'.piles a = s.piles a) ∧
        s'.piles k = { s.piles k with faceUp := (s.piles k).faceUp ++ [c] } ∧
        (∀ w : Card, w ≠ c ∧ w ≠ z → s'.pileOfTop w = s.pileOfTop w)) := by
  obtain ⟨k, hpo, -, hs'f, hpA, hpilek⟩ := p_seat_inr_records hstep
  have hvec : ∀ w : Card, w ≠ c ∧ w ≠ z →
      (∀ a, decide (s'.topOf a = some w) = decide (s.topOf a = some w)) := by
    intro w hwW a
    obtain ⟨hwc, hwz⟩ := hwW
    by_cases hak : a = k
    · rw [hak]
      show decide ((s'.piles k).top = some w)
          = decide ((s.piles k).top = some w)
      have h1 : (s'.piles k).top = some c := by
        rw [hpilek]; exact lastOf_snoc
      have h2 : (s.piles k).top = some z := (pileOfTop_top hpo).2
      rw [h1, h2,
        decide_false_of_not
          (fun hcon : (some c : Option Card) = some w =>
            hwc (Option.some.inj hcon).symm),
        decide_false_of_not
          (fun hcon : (some z : Option Card) = some w =>
            hwz (Option.some.inj hcon).symm)]
    · show decide ((s'.piles a).top = some w)
          = decide ((s.piles a).top = some w)
      rw [hpA a hak]
  exact ⟨hs'f, fun d => nextUp_congr d hs'f, k, hpo, hpA, hpilek,
    fun w hwW => p_census_vec w (hvec w hwW)⟩

/-- **THE RUN-REMOVAL MEMBERSHIP ROW** [E] (the per-file copy; template:
`Orig/TwinExchangeBoth.lean`'s private `mem_revealTop`) — every face-up
card of the run-removed pile's new record sat in the old pile's two
decks (the below-part kept, the revealed head flipped out of the
hidden deck with everything else face-up dropped) or belonged to the
removed prefix itself. -/
private theorem p_mem_afterRunRemoved {q : Pile} {pre : List Card} {e : Card}
    (h : e ∈ (Pile.afterRunRemoved q pre).faceUp) :
    e ∈ pre ∨ (pre = [] ∧ (e ∈ q.faceUp ∨ e ∈ q.hidden)) := by
  cases pre with
  | cons v vs => exact Or.inl h
  | nil =>
      refine Or.inr ⟨rfl, ?_⟩
      rcases q with ⟨hid, fu⟩
      cases hid with
      | nil =>
          rw [show ({ hidden := [], faceUp := fu } : Pile).afterRunRemoved
                ([] : List Card)
              = { hidden := ([] : List Card), faceUp := [] } from rfl,
            show ({ hidden := ([] : List Card), faceUp := [] } : Pile).faceUp
              = ([] : List Card) from rfl] at h
          exact absurd h (by simp)
      | cons g gt =>
          rw [show ({ hidden := g :: gt, faceUp := fu } : Pile).afterRunRemoved
                ([] : List Card)
              = { hidden := gt, faceUp := ([] : List Card) ++ [g] } from rfl,
            show ({ hidden := gt, faceUp := ([] : List Card) ++ [g] } : Pile).faceUp
              = ([] : List Card) ++ [g] from rfl] at h
          rcases List.mem_append.1 h with h | h
          · exact absurd h (by simp)
          · rcases List.mem_cons.1 h with rfl | h
            · exact Or.inr (List.mem_cons_self ..)
            · exact absurd h (by simp)

/-- **THE REVEAL CENSUS, RUNG HALF** [E] — the committed slide writes
no foundation AT ALL: every card's `nextUp` read is VERBATIM across
the commit.  The reveal kind's license conflicts are confined to the
two written piles' arrangement cells, never a rung — the rung world
the reveal rest's route step 1 prices. -/
private theorem p_reveal_rung {s s' : State} {c : Card} {b : Base}
    (hstep : State.step s (Move.tabToTab c b) = some s') :
    s'.found = s.found ∧ ∀ (e : Card), s'.nextUp e = s.nextUp e := by
  obtain ⟨a, -, -, -, hs⟩ := step_tabToTab_inv hstep
  rw [hs]
  refine ⟨?_, ?_⟩
  · show (((s.setPile a (Pile.afterRunRemoved (s.piles a)
        (below c (s.piles a).faceUp))).putRun
        (fromCard c (s.piles a).faceUp) b).found) = s.found
    rw [(putRun_keep (st := s.setPile a (Pile.afterRunRemoved (s.piles a)
        (below c (s.piles a).faceUp)))).1, setPile_found]
  · intro e
    exact nextUp_congr e ((putRun_keep (st := s.setPile a
        (Pile.afterRunRemoved (s.piles a) (below c (s.piles a).faceUp)))).1
      |>.trans (setPile_found s a (Pile.afterRunRemoved (s.piles a)
        (below c (s.piles a).faceUp))))

/-- **THE BOARD-PREFIX SPLIT** [E] — every play is a board-letter
prefix (possibly empty) followed by either its end or a ZONE leg (a
draw or a waste letter — the first leg the draw rest's cursor
content can live at).  The structural fact the draw rest's new
dispatch rides. -/
private theorem p_board_prefix_split : ∀ (l : List Move),
    ∃ B R, l = B ++ R ∧ B.all p_boardMoveB = true ∧
      (R = [] ∨ (∃ z R', R = z :: R' ∧ p_boardMoveB z = false)) := by
  intro l
  induction l with
  | nil => exact ⟨[], [], rfl, rfl, Or.inl rfl⟩
  | cons m t ih =>
      obtain ⟨B, R, hsplit, hB, hR⟩ := ih
      cases hm : p_boardMoveB m with
      | true =>
          refine ⟨m :: B, R, ?_, ?_, hR⟩
          · rw [hsplit]; rfl
          · exact List.all_eq_true.mpr (fun x hx => by
              rcases List.mem_cons.1 hx with rfl | hmem
              · exact hm
              · exact List.all_eq_true.mp hB x hmem)
      | false => exact ⟨[], m :: t, rfl, rfl, Or.inr ⟨m, t, rfl, hm⟩⟩

/-- **THE RUN JOIN** (the per-file copy; template: `Orig.Macro`'s
public `run_split`) — a play landing `s₁` spliced with a play from
`s₁` landing `w` is one play landing `w`. -/
private theorem p_run_join : ∀ (A : List Move) (st s₁ : State)
    (B : List Move) (w : State),
    st.run A = some s₁ → s₁.run B = some w → st.run (A ++ B) = some w := by
  intro A
  induction A with
  | nil =>
      intro st s₁ B w h₁ h₂
      injection h₁ with h
      subst h
      exact h₂
  | cons m t ih =>
      intro st s₁ B w h₁ h₂
      obtain ⟨r, hstep, hrest⟩ := State.run_cons h₁
      show st.run (m :: (t ++ B)) = some w
      rw [show st.run (m :: (t ++ B)) = (match State.step st m with
        | some st' => st'.run (t ++ B)
        | none => none) from rfl, hstep]
      exact ih r s₁ B w hrest h₂

/-- **THE DRAWN ZONE IS A ZONE FUNCTION** (the per-file copy; template:
`Orig/HostCensus.lean`'s private `draw_zone_det`, over `Orig/Phase.lean`'s
public `plain_draw_shape` / `base_draw_shape`) — two states agreeing on
stock, waste, and draw step whose draws both FIRE land agreeing zones:
the draw is recycle-then-deal, a function of the zone triple alone, so
the whole landing is determined by the data the board-thread carries
(the draw piece's mate-weld at its exactest grain: same data, same
landing, no orbit machinery needed at the residue's own cut). -/
private theorem p_draw_zone_det {x xd y yd : State}
    (hz : x.stock = y.stock ∧ x.waste = y.waste ∧ x.drawStep = y.drawStep)
    (hx : State.step x Move.draw = some xd)
    (hy : State.step y Move.draw = some yd) :
    xd.stock = yd.stock ∧ xd.waste = yd.waste ∧ xd.drawStep = yd.drawStep := by
  have hss := hz.1
  have hws := hz.2.1
  have hds := hz.2.2
  have hx' : State.stepDraw x = some xd := hx
  have hy' : State.stepDraw y = some yd := hy
  cases hst : x.stock with
  | nil =>
      have hsty0 : y.stock = ([] : List Card) := by rw [← hss, hst]
      cases hwsx : x.waste with
      | nil =>
          exfalso
          rw [show State.stepDraw x = State.dealStock x.recycle from rfl,
            recycle_allEmpty x hst hwsx, dealStock_nil x hst] at hx'
          exact absurd hx' (by simp)
      | cons w ws =>
          have hxw : x.waste ≠ [] := by rw [hwsx]; simp
          have hyw : y.waste ≠ [] := by rw [← hws]; exact hxw
          rw [base_draw_shape hst hxw] at hx'
          rw [base_draw_shape hsty0 hyw] at hy'
          injection hx' with hrx
          injection hy' with hry
          rw [← hrx, ← hry]
          refine ⟨?_, ?_, ?_⟩
          · show (x.waste.reverse.drop x.drawStep)
              = (y.waste.reverse.drop y.drawStep)
            rw [hws, hds]
          · show ((x.waste.reverse.take x.drawStep).reverse ++ ([] : List Card))
              = ((y.waste.reverse.take y.drawStep).reverse ++ ([] : List Card))
            rw [hws, hds]
          · rw [show x.drawStep = y.drawStep from hds]
  | cons s ss =>
      have hxs : x.stock ≠ [] := by rw [hst]; simp
      have hsty : y.stock ≠ [] := by rw [← hss]; exact hxs
      rw [plain_draw_shape hxs] at hx'
      rw [plain_draw_shape hsty] at hy'
      injection hx' with hrx
      injection hy' with hry
      rw [← hrx, ← hry]
      refine ⟨?_, ?_, ?_⟩
      · show x.stock.drop x.drawStep = y.stock.drop y.drawStep
        rw [hss, hds]
      · show (x.stock.take x.drawStep).reverse ++ x.waste
          = (y.stock.take y.drawStep).reverse ++ y.waste
        rw [hss, hds, hws]
      · rw [show x.drawStep = y.drawStep from hds]

/-- **THE SEAL'S HOT SCAN** — the decidable probe of the interloper
census: does some card of the sealed suit, exactly one rung above
the sealed card, hold the S-license at the scan state?  A `Bool`
fold over the 52-card universe so the interloper census below stays
choice-free per the house discipline (the `p_seatOffered` pattern). -/
private def p_sealHotScan (st : State) (c : Card) : Bool :=
  Card.universe.any (fun e =>
    decide (e.suit = c.suit) &&
    decide (e.rank.toIdx = c.rank.toIdx + 1) &&
    canRaiseSB st e)

/-- The scan is exact: it reads true exactly when an interloper
exists (the fold's found witness carries the triple, both ways). -/
private theorem p_sealHotScan_iff {st : State} {c : Card} (hwf : st.WF) :
    p_sealHotScan st c = true ↔
      ∃ e, e.suit = c.suit ∧ e.rank.toIdx = c.rank.toIdx + 1 ∧
        CanRaiseS st e := by
  rw [p_sealHotScan, List.any_eq_true]
  constructor
  · rintro ⟨e₀, -, hval⟩
    rw [Bool.and_eq_true] at hval
    obtain ⟨h1, h2⟩ := hval
    rw [Bool.and_eq_true] at h1
    exact ⟨e₀, of_decide_eq_true h1.1, of_decide_eq_true h1.2,
      (canRaiseSB_true_iff hwf).1 h2⟩
  · intro ⟨e₀, hs, hr, hS⟩
    refine ⟨e₀, Card.mem_universe e₀, ?_⟩
    rw [Bool.and_eq_true]
    refine ⟨?_, (canRaiseSB_true_iff hwf).2 hS⟩
    rw [Bool.and_eq_true]
    exact ⟨decide_eq_true hs, decide_eq_true hr⟩

/-- **THE SEAL'S INTERLOPER-FORCING** [M] — the empty-exhibit census
of the waste-founding kind, landed: when the exhibiting fork play is
EMPTY (the fork sat AT the origin, witness `x`) and the seal's
successor is NOT itself fork-headed, the successor's S-license world
is FORCED to grow — some card of the SEALED SUIT is S-live at the
successor, its rung exactly one above the sealed card's.  The
census, CONSTRUCTIVELY (zero `Classical`, the house discipline): the
interloper question is DECIDED as a `Bool` scan first
(`p_sealHotScan` over the 52-card universe, `canRaiseSB` the
S-shadow); a true scan hands the interloper over directly, and a
false scan makes the successor's S-license world read EXACTLY the
origin's — the seal's write record (`p_seal_zone_rows`) leaves every
license input verbatim off the sealed suit, the origin pair cannot
read the sealed suit at all (the suit's one frontier card IS the
eaten waste head, and an S-live card must sit in the tableau), and a
sealed-suit card only S-live on the next rung — so the origin's own
parcel re-certifies at the EMPTY play, `forkStateSB_true_iff`
against the assumed forklessness.  The waste-founding remainder's
empty-exhibit schedule carries this card as its input datum; the
multi-leg expose-and-found re-scheduling that defuses it remains
the probe program's honest danger, priced there. -/
private theorem p_seal_interloper_forced {s s' : State} {c x : Card}
    (hwf : s.WF)
    (hstep : State.step s (Move.wasteToFound c) = some s')
    (hwit : ForkWitness s x)
    (hfb : ¬ forkStateSB s' = true) :
    ∃ e, e.suit = c.suit ∧ e.rank.toIdx = c.rank.toIdx + 1 ∧
      CanRaiseS s' e := by
  have hwfs' : s'.WF := step_wf hwf hstep
  by_cases hscan : p_sealHotScan s' c = true
  · exact (p_sealHotScan_iff hwfs').mp hscan
  · -- the interloper-free census: no sealed-suit card is S-live at
    -- the successor, so the origin parcel re-certifies verbatim
    -- the seal's write record, and the eaten head's residency/guard
    obtain ⟨hpiles, -, ws, -, hwaste, hrows, hseal⟩ := p_seal_zone_rows hstep
    have hcw : c ∈ s.waste := by rw [hwaste]; exact List.mem_cons_self ..
    obtain ⟨hgc, -, -, -, -⟩ := step_wasteToFound_inv hstep
    rw [Bool.and_eq_true] at hgc
    have hcnext : s.nextUp c = true := hgc.2
    have hcrung : c.rank.toIdx = s.foundHeight c.suit := of_decide_eq_true hcnext
    -- the suit's frontier card at the origin IS the waste head
    have hkey : ∀ y : Card, y.suit = c.suit → CanRaiseS s y → y = c := by
      intro y hy hSy
      obtain ⟨hnexty, -, -, -, -, -, -⟩ := (canRaiseS_iff hwf).mp hSy
      have h0 : y.rank.toIdx = s.foundHeight y.suit := of_decide_eq_true hnexty
      rw [hy] at h0
      obtain ⟨ys, yr⟩ := y
      obtain ⟨cs, cr⟩ := c
      have hss : ys = cs := hy
      simp only [Card.mk.injEq]
      exact ⟨hss, Rank.toIdx_inj (h0.trans hcrung.symm)⟩
    -- an S-live card sits in the tableau, so the waste head is not S-live
    have hcolof : ∀ {y : Card}, CanRaiseS s y → ∃ a, y ∈ (s.piles a).faceUp := by
      intro y hSy
      obtain ⟨-, a, bs, run, hlist, -, -⟩ := (canRaiseS_iff hwf).mp hSy
      refine ⟨a, ?_⟩
      rw [hlist]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    have hwastenot : ∀ {y : Card}, CanRaiseS s y → y ≠ c := by
      intro y hSy hcon
      obtain ⟨a, hmem⟩ := hcolof hSy
      rw [hcon] at hmem
      exact absurd hcw ((mem_faceUp_only hwf hmem).2.2.2.1)
    -- the origin pair reads no sealed-suit card
    have hSx : CanRaiseS s x := (hwit.1 x).mp (Or.inl rfl)
    have hSxt : CanRaiseS s x.twin := (hwit.1 x.twin).mp (Or.inr rfl)
    have hxsuit : x.suit ≠ c.suit := by
      intro hcon
      exact hwastenot hSx (hkey x hcon hSx)
    have hxtsuit : x.twin.suit ≠ c.suit := by
      intro hcon
      exact hwastenot hSxt (hkey x.twin hcon hSxt)
    -- off the sealed suit the license world is verbatim (§5.0c)
    have hoff : ∀ {e : Card}, e.suit ≠ c.suit → (CanRaiseS s' e ↔ CanRaiseS s e) :=
      p_license_offRung c.suit hwfs' hwf hpiles hrows
    -- no sealed-suit card is S-live at the successor: the scan is
    -- exact, and an S-live one would sit exactly one rung up the
    -- seal, reading the scan true against its false dichotomy
    have hdead : ∀ e : Card, e.suit = c.suit → ¬ CanRaiseS s' e := by
      intro e he hS'
      have hnextE := (canRaiseS_iff hwfs').mp hS'
      have h0 : e.rank.toIdx = s'.foundHeight e.suit :=
        of_decide_eq_true hnextE.1
      rw [he] at h0
      rw [show s'.foundHeight c.suit = (s'.found c.suit).length from rfl,
          hseal, List.length_append, List.length_singleton] at h0
      have hclen : c.rank.toIdx = (s.found c.suit).length := hcrung
      exact absurd ((p_sealHotScan_iff hwfs').mpr ⟨e, he, by omega, hS'⟩)
        hscan
    -- the origin's parcel re-certifies at the successor: forklessness
    -- contra the interloper-free census
    have hwit' : ForkWitness s' x := by
      refine ⟨fun c₀ => ⟨fun hmem => ?_, fun hS' => ?_⟩, ?_⟩
      · rcases hmem with rfl | rfl
        · exact (hoff hxsuit).mpr hSx
        · exact (hoff hxtsuit).mpr hSxt
      · by_cases hs : c₀.suit = c.suit
        · exact absurd hS' (hdead c₀ hs)
        · exact (hwit.1 c₀).mpr ((hoff hs).mp hS')
      · -- the vanilla conjunct: every clause reads off the sealed row
        intro hcr
        obtain ⟨hn, a, hp, hseat⟩ := hcr
        have hrowt : s'.found x.twin.suit = s.found x.twin.suit :=
          hrows x.twin.suit hxtsuit
        rw [show s'.nextUp x.twin = s.nextUp x.twin from by
            show decide (x.twin.rank.toIdx = (s'.found x.twin.suit).length)
              = decide (x.twin.rank.toIdx = (s.found x.twin.suit).length)
            rw [hrowt]] at hn
        rw [show s'.pileOfTop x.twin = s.pileOfTop x.twin from
            p_pileOfTop_congr x.twin hpiles] at hp
        rw [show s'.piles a = s.piles a from congrFun hpiles a] at hseat
        exact hwit.2 ⟨hn, a, hp, hseat⟩
    exact absurd ((forkStateSB_true_iff hwfs').mpr
      (forkState_iff.mpr ⟨x, hwit'⟩)) hfb

/-- **THE SEAT'S HOT-FORCING, EMPTY-ANCHOR ARM** [M] — the
empty-exhibit census of the waste-seating kind at the king seat: at
a forkless successor of the ORIGIN's fork, some c-family card went
HOT — the seated head `c` itself, or its twin.  The census: the
seating writes NO rung (the read census `p_seat_reads_inl`: every
`nextUp` is verbatim), the written pile was EMPTY before the seat
(so no license column ever read it) and is the seated king's bare
singleton after (so no certificate can live there but the king's
own), the origin pair holds no c-family card (the seated head was
waste-resident at the origin, and the pair closure kills the twin
corner the same way), and the top-search transports verbatim off
the born cell — so a c-cold successor re-certifies the origin's own
parcel at the EMPTY play, `forkStateSB_true_iff` against the assumed
forklessness.  Both interference reads are DECIDED as `Bool` case
splits — zero `Classical`.  The covered-host (inr) arm's interference
census is deliberately NOT priced here — its corners (the covered
host's top dying, the twin-cover corners) are the seating kind's own
open geometry, carried at the row's token. -/
private theorem p_seat_inl_hot_forced {s s' : State} {c x : Card} {k : Anchor}
    (hwf : s.WF)
    (hstep : State.step s (Move.wasteToTab c (Sum.inl k)) = some s')
    (hwit : ForkWitness s x)
    (hfb : ¬ forkStateSB s' = true) :
    s.nextUp c = true ∨ s.nextUp c.twin = true := by
  have hwfs' : s'.WF := step_wf hwf hstep
  by_cases hcn : s.nextUp c = true
  · exact Or.inl hcn
  by_cases hctn : s.nextUp c.twin = true
  · exact Or.inr hctn
  -- both hot reads pinned false (decided, zero Classical)
  have hcB : s.nextUp c = false := by
    cases hb : s.nextUp c with
    | true => exact absurd hb hcn
    | false => rfl
  have hctB : s.nextUp c.twin = false := by
    cases hb : s.nextUp c.twin with
    | true => exact absurd hb hctn
    | false => rfl
  -- the seating's read census, and the empty seat's records
  obtain ⟨-, hnextA, hpA, hpilk, hsearch⟩ := p_seat_reads_inl hstep
  obtain ⟨hemp, -, -, -, -⟩ := p_seat_inl_records hstep
  obtain ⟨-, hkFu⟩ := (Pile.isEmpty_eq _).mp hemp
  -- the seated head was waste-resident at the origin
  obtain ⟨hg, w, ws, hwaste, -⟩ := step_wasteToTab_inv hstep
  rw [Bool.and_eq_true] at hg
  have hw2 : w = c := State.wasteIs_head_eq hwaste hg.1
  rw [hw2] at hwaste
  have hcw : c ∈ s.waste := by rw [hwaste]; exact List.mem_cons_self ..
  -- an S-live card sits in the tableau, so the waste head is not S-live
  have hcolof : ∀ {y : Card}, CanRaiseS s y → ∃ a, y ∈ (s.piles a).faceUp := by
    intro y hSy
    obtain ⟨-, a, bs, run, hlist, -, -⟩ := (canRaiseS_iff hwf).mp hSy
    refine ⟨a, ?_⟩
    rw [hlist]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  -- the origin pair reads no c-family card (the head itself by the
  -- waste residency, the twin corner by the pair closure)
  have hxc : x ≠ c ∧ x ≠ c.twin := by
    constructor
    · intro hcon
      obtain ⟨a, hmem⟩ := hcolof ((hwit.1 c).mp (Or.inl hcon.symm))
      exact absurd hcw ((mem_faceUp_only hwf hmem).2.2.2.1)
    · intro hcon
      rw [hcon] at hwit
      obtain ⟨a, hmem⟩ := hcolof ((hwit.1 c).mp (Or.inr (Card.twin_twin c).symm))
      exact absurd hcw ((mem_faceUp_only hwf hmem).2.2.2.1)
  -- the per-card transport: off the c-family every license moves
  -- verbatim across the seat (nextUp verbatim by the read census;
  -- columns off the written pile, verbatim by the pile records;
  -- top-searches verbatim off the born cell)
  have htrans : ∀ y : Card, y ≠ c → y ≠ c.twin →
      (CanRaiseS s' y ↔ CanRaiseS s y) := by
    intro y hyc hyct
    have hytc : y.twin ≠ c := by
      intro hcon
      have h2 : y.twin.twin = c.twin := congrArg Card.twin hcon
      rw [Card.twin_twin y] at h2
      exact hyct h2
    constructor
    · intro hSy'
      obtain ⟨hnext', a, bs, run, hshape, hseat, hdisj⟩ :=
        (canRaiseS_iff hwfs').mp hSy'
      -- the certificate column is not the written pile: its face-up
      -- record is the seated king's bare singleton, and y is not it
      have hak : a ≠ k := by
        intro hcon
        rw [hcon, hpilk] at hshape
        have h2 : ([c] : List Card) = bs ++ y :: run := hshape
        cases bs with
        | nil =>
            rw [List.nil_append] at h2
            injection h2 with hy _
            exact hyc hy.symm
        | cons b bt => exact absurd h2 (by simp)
      rw [hpA a hak] at hshape
      rw [hpA a hak] at hseat
      refine (canRaiseS_iff hwf).2
        ⟨by rw [← hnextA y]; exact hnext', a, bs, run, hshape, hseat, ?_⟩
      rcases hdisj with rfl | htw
      · exact Or.inl rfl
      · exact Or.inr (by rw [hsearch y.twin hytc] at htw; exact htw)
    · intro hSy
      obtain ⟨hnext, a, bs, run, hshape, hseat, hdisj⟩ :=
        (canRaiseS_iff hwf).mp hSy
      -- the origin column is not the written pile: the seat was empty
      have hak : a ≠ k := by
        intro hcon
        rw [hcon] at hshape
        rw [hkFu] at hshape
        exact absurd hshape.symm (by simp)
      have hs' : (s'.piles a).faceUp = bs ++ y :: run := by
        rw [hpA a hak]; exact hshape
      have hseat' : bs ≠ [] ∨
          ((s'.piles a).hidden = [] ∧ y.rank = Rank.king) := by
        rw [hpA a hak]; exact hseat
      refine (canRaiseS_iff hwfs').2
        ⟨by rw [hnextA y]; exact hnext, a, bs, run, hs', hseat', ?_⟩
      rcases hdisj with rfl | htw
      · exact Or.inl rfl
      · exact Or.inr (by rw [← hsearch y.twin hytc] at htw; exact htw)
  -- the origin parcel re-certifies at the successor
  have hwit' : ForkWitness s' x := by
    refine ⟨fun c₀ => ⟨fun hmem => ?_, fun hS' => ?_⟩, ?_⟩
    · rcases hmem with h | h
      · rw [h]
        exact (htrans x hxc.1 hxc.2).mpr ((hwit.1 x).mp (Or.inl rfl))
      · rw [h]
        exact (htrans x.twin
          (by
            intro hcon
            have h2 : x.twin.twin = c.twin := congrArg Card.twin hcon
            rw [Card.twin_twin x] at h2
            exact hxc.2 h2)
          (by
            intro hcon
            have h2 : x.twin.twin = c.twin.twin := congrArg Card.twin hcon
            rw [Card.twin_twin x, Card.twin_twin c] at h2
            exact hxc.1 h2)).mpr
          ((hwit.1 x.twin).mp (Or.inr rfl))
    · by_cases hc₀c : c₀ = c
      · have hnext' := (canRaiseS_iff hwfs').mp hS'
        rw [hc₀c, hnextA c, hcB] at hnext'
        exact absurd hnext' (by simp)
      by_cases hc₀ct : c₀ = c.twin
      · have hnext' := (canRaiseS_iff hwfs').mp hS'
        rw [hc₀ct, hnextA c.twin, hctB] at hnext'
        exact absurd hnext' (by simp)
      · exact (hwit.1 c₀).mpr ((htrans c₀ hc₀c hc₀ct).mp hS')
    · -- the vanilla conjunct: all clauses read off the written cell
      intro hcr
      obtain ⟨hn, a, hp, hseat⟩ := hcr
      have hytc : x.twin ≠ c := by
        intro hcon
        have h2 : x.twin.twin = c.twin := congrArg Card.twin hcon
        rw [Card.twin_twin x] at h2
        exact hxc.2 h2
      rw [hnextA x.twin] at hn
      rw [hsearch x.twin hytc] at hp
      have hak : a ≠ k := by
        intro hcon
        rw [hcon] at hp
        have htop := (pileOfTop_top hp).2
        have hnone : lastOf (s.piles k).faceUp = none := by
          rw [hkFu]
          rfl
        exact absurd (htop.symm.trans hnone) (by simp)
      rw [hpA a hak] at hseat
      exact hwit.2 ⟨hn, a, hp, hseat⟩
  exact absurd ((forkStateSB_true_iff hwfs').mpr
    (forkState_iff.mpr ⟨x, hwit'⟩)) hfb

/-- **THE SEAT'S INTERFERENCE-FORCING** — the seating kind's
empty-exhibit census, base-uniform: at a forkless successor of the
ORIGIN's fork, either a c-family card went hot (the empty-anchor
economy, priced by `p_seat_inl_hot_forced`: the seated king's own
rung, or its twin's own rung), or the seat was a CARD-HOST arm —
the covered-host economy whose corners (the covered top's death,
the twin-cover corners, the search exceptions of
`p_seat_reads_inr`) remain the seating kind's own open geometry,
priced at the probe program's fb2E junk-refusal verdicts. -/
private theorem p_seat_interference_forced {s s' : State} {c x : Card} {b : Base}
    (hwf : s.WF)
    (hstep : State.step s (Move.wasteToTab c b) = some s')
    (hwit : ForkWitness s x)
    (hfb : ¬ forkStateSB s' = true) :
    s.nextUp c = true ∨ s.nextUp c.twin = true ∨
      ∃ z : Card, b = Sum.inr z := by
  cases b with
  | inl k =>
      cases p_seat_inl_hot_forced hwf hstep hwit hfb with
      | inl h => exact Or.inl h
      | inr h => exact Or.inr (Or.inl h)
  | inr z => exact Or.inr (Or.inr ⟨z, rfl⟩)

/-- **THE WASTE-HEAD SHADOW** [H, the cursor birth's named narrow
sub-residue, exactly one `sorryAx`]: the exhibiting play's first
load-bearing zone leg is a WASTE letter — the leg `z` (a
`wasteToFound` or a `wasteToTab`) fired at the boardEq twin `u` of
the forkless mirror `u'`, consuming the waste head of the cycle at
`u` — exactly the head the COMMIT's deal left MOVED (the board
prefix wrote no zone cell, so `u` carries the origin's zone while
`u'` carries the once-drawn zone: the dealt stock binds the waste's
front, so the leg's own guard `wasteIs` reads the shifted cursor and
the leg does not fire at `u'` at all).

ROUTE (complete; the open step named):

1. THE SHIFT, PRICED: the commit's draw pushed the cycle once; the
   consumed head (the letter's own card) still lives in the
   successor's two-zone world — the drawn zone is the SAME zone's
   rotation (`p_draw_zone_det` the function read; the membership
   conservation the iff row of §4) — so the availability survives at
   a rotated cursor.
2. THE RE-PHASING (the open step): rotate the successor's own cycle
   (draws are legal while the count is positive, and the count is a
   rotation of the origin's) until the consumed head heads the waste
   again, then fire the leg's counterpart letter and replay the
   remaining tail — against the shifted tail guards the same
   induction recurses at a strictly shorter remaining play.  The
   REPAIR-TIME BOUND (the rotation's leg count, the measure strictly
   decreasing along the schedule until a fresh fork witness
   re-assembles) is the residual content, carried here and nowhere
   else; the crane's round-trip rows price WHAT the rotation may
   disturb (a returned excursion issues no seat the arrangement did
   not already carry), not WHEN.
3. REMAINING CONTENT: the multi-commit schedule's time bound — the
   probe program's surviving honest danger (HUNTING-FLOOR HONESTY,
   `Orig/ForkFloorProbe.lean`: fb2E/fb3E's waste economies, decided
   only at their snapshots). -/
private theorem p_draw_zone_shift {s s' u u' w₀ F : State} {z : Move}
    {R' : List Move} {x : Card}
    (hwf : s.WF)
    (hstep : State.step s Move.draw = some s')
    (hzU : u.stock = s.stock ∧ u.waste = s.waste ∧ u.drawStep = s.drawStep)
    (hzU' : u'.stock = s'.stock ∧ u'.waste = s'.waste ∧ u'.drawStep = s'.drawStep)
    (hfbU : ¬ forkStateSB u' = true)
    (hz : (∃ c', z = Move.wasteToFound c') ∨ (∃ c' b', z = Move.wasteToTab c' b'))
    (hw₀ : State.step u z = some w₀)
    (hR' : w₀.run R' = some F)
    (hwit : ForkWitness F x) :
    ∃ (F' : State) (π' : List Move) (x' : Card),
      u'.run π' = some F' ∧ ForkWitness F' x' := by
  sorry

/-- **THE DRAW ARM'S NAMED ZONE REMAINDER** [H, named sub-residue,
exactly one `sorry` — the draw kind's carried content once the two
closed fragments are dispatched]: the exhibiting play heads with a
NON-draw move and carries at least one zone leg (a draw or a waste
letter) below its head.

ROUTE (complete; the open step named):

1. THE KIND SUB-ROWS APPLIED (§§1, 4): the committed draws keep the
   whole board verbatim (the draw writes neither piles nor found,
   `draws_permute_only`), so every PAIR-CONTENT cell the consumed
   fork needs — members, covers, seats — sits exactly where it sat,
   and the two-zone membership is conserved exactly (§4's iff): no
   card becomes unreachable-from-play and no card becomes reachable
   early through the cycle.
2. THE RE-SCHEDULING (the open step): the exhibiting play's zone
   legs — draws at inner positions, waste letters on heads the
   cursor may reach shifted — must be RE-PHASED: commute the
   board-segment prefixes past the successor's own cursor
   alignment.  HostCensus §9's closed half is the assemble-grade
   toolshere (`drawfree_commute_witness` for the draw-free
   prefixes; `interleave_leg_conjugation` welding a draw inside a
   returned witness through the macro class), and the two dashed
   landings weld through the banked draw push
   (`EdgeLabel.draw_landings_sameOrbit`): the commit's own landing
   is a zone-mate of the play's forced draws.  What is NOT banked
   anywhere is the repair-time bound once the re-phased prefix
   hits a waste-head shift (a `wasteToFound`/`wasteToTab` leg of
   the play reading the head the commit's deal left moved) — the
   probe program's surviving honest danger (the multi-commit
   schedule), carried here and nowhere else.
3. REMAINING CONTENT: the defusing-schedule repair TIME bound of
   the route's step 2 — a measure on the two-zone arrangement that
   strictly decreases along the re-phased schedule until a fork
   witness re-assembles.  Phase's offset/pristine tables
   (`draw_irreversibility_class`, `drawStep_one_class`) price the
   cycle's own irreversibility, not the schedule.

PROBE PRICING (round-3; boards NOT added here, per the mission):
the fragile-pair economies all kept a downward fork in reach with
the cycle untouched (`fb2`/`fb3`: the corridor never rode the
cycle), and the pristine one-cell stock of `fb1` could not feed a
corridor either way — evidence the zone remainder is TRAVEL
content (re-phasing), not content death.

CLOSED ALSO (this pass): THE SUCCESSOR'S OWN FORK — when the
successor is itself fork-headed, the empty play exhibits it
(`p_successor_fork_repair`: the census `forkStateSB` decides,
`forkStateSB_true_iff` bridges, `forkWitnessSB_sound` hands the
full two-conjunct parcel).  The row's sole carried content is
its FORKLESS-SUCCESSOR branch: the phase re-phasing schedule
above, from a successor that is NOT already a fork.

CLOSED THIS PASS (the succession): THE BOARD-PASSAGE EXHIBITS --
the play splits as a board-letter prefix before its FIRST ZONE
LEG (`p_board_prefix_split`), and the committed draw wrote no
board cell, so the prefix re-runs from the successor verbatim
along §4's board thread (`board_run_congr` over the `boardEq`
the draw commit leaves); when the prefix's mirror LANDING is
itself fork-headed the prefix IS the successor's exhibit (the
      zone legs all ride strictly AFTER a fork's arrival -- they were
      never load-bearing).  What remains is exactly the CURSOR BIRTH,
      and this pass SPLITS IT BY THE FIRST ZONE LEG'S KIND: the DRAW
      leg is CLOSED VERBATIM (the drawn zone is a ZONE FUNCTION,
      `p_draw_zone_det` -- the commit's own push and the play's inner
      draw read the same zone triple, so the play's draw at the
      prefix landing IS the mirror state the successor thread already
      sits at, and the remaining tail replays verbatim, the same fork
      one leg sooner); the WASTE leg is the named narrow sub-residue
      `p_draw_zone_shift` below -- the head the commit's deal left
      moved, the re-phasing schedule's sole honest stake, which
      `Orig/EdgeLabel.lean`'s banked share explicitly does not cover
      (the waste/tab share of the successor program is open there);
      the `draw_landings_sameOrbit` class-weld stays the
      assemble-grade record for the not-needed half -- at the draw
      cut the landing equality is EXACT, one state, stronger than
      class-mates, so the orbit machinery is spent nowhere new). -/
private theorem p_draw_zone_rest {s s' F : State} {x : Card}
    {m₀ : Move} {τ : List Move}
    (hwf : s.WF)
    (hstep : State.step s Move.draw = some s')
    (hivr : irreversibleAt s Move.draw)
    (hrun : s.run (m₀ :: τ) = some F)
    (hwit : ForkWitness F x)
    (hhead : m₀ ≠ Move.draw)
    (hzone : (m₀ :: τ).all p_boardMoveB = false) :
    ∃ (F' : State) (π' : List Move) (x' : Card),
      s'.run π' = some F' ∧ ForkWitness F' x' := by
  by_cases hfb : forkStateSB s' = true
  · exact p_successor_fork_repair (step_wf hwf hstep) hfb
  · -- the forkless successor: this row's sole carried content, at its
    --  narrowest shape THIS PASS: the CURSOR BIRTH alone.
    --  (1) the successor's board thread (§4): the committed draw
    --      wrote no board cell, so the exhibiting play's board-letter
    --      prefix re-runs from s' verbatim, landing its boardEq
    --      mirror (`board_run_congr`).
    have hsDrw : s.stepDraw = some s' := hstep
    have hbss : boardEq s s' :=
      ⟨(stepDraw_piles hsDrw).symm, (stepDraw_found hsDrw).symm⟩
    --  (2) the play's board-prefix split (§5.0c): a board-letter
    --      prefix, then either the end or the FIRST ZONE LEG.
    obtain ⟨B, R, hsplit, hB, hR⟩ := p_board_prefix_split (m₀ :: τ)
    obtain ⟨u, hrunB, hrest⟩ :=
      run_append_split s B R F (by rw [← hsplit]; exact hrun)
    obtain ⟨u', hrunB', hbU, hzU, hwU, hdU, hzU', hwU', hdU'⟩ :=
      board_run_congr B (fun mb hmem =>
        p_boardMoveB_true mb (List.all_eq_true.mp hB mb hmem))
        s s' hbss u hrunB
    rcases hR with rfl | ⟨z, R', rfl, hfz⟩
    · exfalso
      -- the play has no zone leg at all: contradicts hzone
      rw [List.append_nil] at hsplit
      rw [hsplit] at hzone
      rw [hB] at hzone
      exact absurd hzone (by simp)
    by_cases hfbU : forkStateSB u' = true
    · -- CLOSED THIS PASS: the board prefix's mirror is ITSELF
      -- fork-headed -- the play's first zone leg rides strictly
      -- AFTER a fork's arrival and was never load-bearing; the
      -- board prefix exhibits the successor's fork directly.
      obtain ⟨xU, hxiff, hxnt⟩ :=
        (forkStateSB_true_iff (p_run_wf s' B u' hrunB'
          (step_wf hwf hstep))).mp hfbU
      exact ⟨u', B, xU, hrunB', ⟨hxiff, hxnt⟩⟩
    · -- THE CURSOR BIRTH, at the first zone leg's own kind.  The
      -- play's first zone leg `z` fired at the boardEq twin `u` of
      -- the mirror `u'`; the leg's record is in `p_draw_zone_det`'s
      -- zone function and the named shift row below.
      obtain ⟨w₀, hw₀, hR'⟩ := State.run_cons hrest
      cases z with
      | draw =>
          -- THE DRAW LEG, CLOSED: the commit's own push and the
          -- play's inner draw read the SAME zone triple (the board
          -- prefix wrote no zone cell), so the play's draw at `u`
          -- lands EXACTLY the mirror `u'` -- and the remaining tail
          -- replays verbatim: the SAME fork `F`, the same witness,
          -- the exhibit one leg shorter.
          have hdw : u.stepDraw = some w₀ := hw₀
          have hdet := p_draw_zone_det ⟨hzU, hwU, hdU⟩ hw₀ hstep
          have heq : w₀ = u' := by
            refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
            · rw [stepDraw_found hdw, hbU.2]
            · rw [stepDraw_piles hdw, hbU.1]
            · rw [hdet.1]; exact hzU'.symm
            · rw [hdet.2.1]; exact hwU'.symm
            · rw [hdet.2.2]; exact hdU'.symm
          rw [heq] at hR'
          exact ⟨F, B ++ R', x, p_run_join B s' u' R' F hrunB' hR', hwit⟩
      | wasteToFound c' =>
          -- THE WASTE LETTER: the named narrow sub-residue
          obtain ⟨F', π'', x', hrun'', hwit'⟩ :=
            p_draw_zone_shift hwf hstep ⟨hzU, hwU, hdU⟩ ⟨hzU', hwU', hdU'⟩
              hfbU (Or.inl ⟨c', rfl⟩) hw₀ hR' hwit
          exact ⟨F', B ++ π'', x', p_run_join B s' u' π'' F' hrunB' hrun'',
            hwit'⟩
      | wasteToTab c' b' =>
          -- the seating waste letter: the same named shift
          obtain ⟨F', π'', x', hrun'', hwit'⟩ :=
            p_draw_zone_shift hwf hstep ⟨hzU, hwU, hdU⟩ ⟨hzU', hwU', hdU'⟩
              hfbU (Or.inr ⟨c', b', rfl⟩) hw₀ hR' hwit
          exact ⟨F', B ++ π'', x', p_run_join B s' u' π'' F' hrunB' hrun'',
            hwit'⟩
      | tabToFound c' => exact absurd hfz (by simp [p_boardMoveB])
      | foundToTab c' b' => exact absurd hfz (by simp [p_boardMoveB])
      | tabToTab c' b' => exact absurd hfz (by simp [p_boardMoveB])

/-- **`fork_floor_draw`** — **THE DRAW-CURSOR KIND RESIDUE** [H,
named residue, exactly one `sorry`]: the committed draw
(draw-at-nonempty-stock per Phase's pristine regime) preserves
fork-headedness.

ROUTE (the kind read, complete):

1. THE KIND SUB-ROWS APPLIED: a draw writes no pile and no
   foundation (§4's two banked prongs), conserves the cycle
   membership exactly (§4's iff), and the hidden decks are
   untouched (§1's draw arm is exact equality) — so NO content
   availability dies: the pair members the consumed fork needs, its
   cover candidates, and the family lows on its climb all stay
   where they were, at the possibly different cycle cursor.
2. THE REPAIR: the consumed fork's own package (pair mobility,
   cover mobility, low-card raisability per the index-exact climb)
   therefore survives at s' at least to within a defusing-schedule
   repair — re-scheduling the cycle reads (which face the waste
   top) to re-fire the founding/slide letters on the way to a
   fresh fork; the crane's loan-and-repay is
   `excursion_issues_noNewSeat` — no hosting capacity is issued a
   returned excursion does not reclaim — with
   `census_step_draw`'s flatness carrying the draw legs.
3. REMAINING CONTENT: the defusing-schedule repair TIME bound — a
   measure on the cycle-zone arrangement that strictly decreases
   along the schedule until a fork witness re-assembles (the
   crux's own content; Phase's offset/pristine tables price the
   cycle's irreversibility, not the schedule).

HEAD-CASE LANDED (§5.0, this pass): when the exhibiting fork play
HEADS with the very draw that committed (π = Move.draw :: τ), the
same-fork climb is `p_survives_sameHead` — the successor IS the
play's second state, the tail replays verbatim, distance zero.

ASSEMBLY STRUCTURE (this pass): the kind is now a DISPATCH over
the exhibiting play's leg profile, with two fragments CLOSED and
the remainder isolated as its own NAMED SUB-RESIDUE
(`p_draw_zone_rest` below, per the isolation discipline):

* CLOSED, distance zero — the head-case above (`p_survives_sameHead`).
* CLOSED, distance zero — the BOARD-ONLY EXHIBIT (§5.0b's
  `p_draw_board_repair`): a play whose every leg is a board letter
  (raise / pull / cargo — no draws, no waste letters) cannot be
  disturbed by the commit at all: the draw writes no board cell
  (`draws_permute_only`'s own two prongs), the play re-runs
  verbatim along the board thread (`board_run_congr`), and the
  fork certificate travels the thread verbatim
  (`p_fork_boardTransfer`: the certificate is arrangement-only).
  The empty exhibit (π = [], the fork AT the origin: the successor
  IS the exhibit) rides this same fragment.
* NAMED REMAINDER — `p_draw_zone_rest`: the play heads with a
  non-draw move and carries at least one zone leg (a draw or a
  waste letter) below its head.  This is the phase content
  proper: the cursor read / repair time bound of the route's
  step 3, carried under its own name with the full route;
  `Orig/EdgeLabel.lean`'s `draw_landings_sameOrbit` (the two
  dashed landings weld through the same orbit) and HostCensus
  §9's interleave rows are the assemble-grade tools the route
  names for it. -/
private theorem fork_floor_draw {s s' : State}
    (hwf : s.WF)
    (hstep : State.step s Move.draw = some s')
    (hivr : irreversibleAt s Move.draw)
    (hhed : ∃ (F : State) (π : List Move) (x : Card),
        s.run π = some F ∧ ForkWitness F x) :
    ∃ (F' : State) (π' : List Move) (x' : Card),
        s'.run π' = some F' ∧ ForkWitness F' x' := by
  obtain ⟨F, π, x, hrun, hwit⟩ := hhed
  by_cases hball : π.all p_boardMoveB = true
  · -- the board-only exhibit (the empty play included): closed
    refine p_draw_board_repair hwf hstep ?_ hrun hwit
    intro m hm
    exact p_boardMoveB_true m (List.all_eq_true.mp hball m hm)
  · have hbfalse : π.all p_boardMoveB = false := by
      cases h : π.all p_boardMoveB with
      | true => exact absurd h hball
      | false => rfl
    cases π with
    | nil => exact absurd rfl hball
    | cons m₀ τ =>
        cases m₀ with
        | draw => exact p_survives_sameHead hstep hrun hwit
        | wasteToFound c₀ =>
            exact p_draw_zone_rest hwf hstep hivr hrun hwit
              (fun hcon => absurd hcon (by simp)) hbfalse
        | wasteToTab c₀ b₀ =>
            exact p_draw_zone_rest hwf hstep hivr hrun hwit
              (fun hcon => absurd hcon (by simp)) hbfalse
        | tabToFound c₀ =>
            exact p_draw_zone_rest hwf hstep hivr hrun hwit
              (fun hcon => absurd hcon (by simp)) hbfalse
        | foundToTab c₀ b₀ =>
            exact p_draw_zone_rest hwf hstep hivr hrun hwit
              (fun hcon => absurd hcon (by simp)) hbfalse
        | tabToTab c₀ b₀ =>
            exact p_draw_zone_rest hwf hstep hivr hrun hwit
              (fun hcon => absurd hcon (by simp)) hbfalse

/-- **THE WASTE-FOUNDING ARM'S NAMED REMAINDER** [M–H, named
sub-residue, exactly one `sorryAx` — the waste-founding kind's
carried content once the head-case and the corridor are
dispatched]: the exhibiting play is EMPTY (the fork sits at the
origin, with the eaten head sealed one rung up) or heads with a
board letter (raise / pull / cargo) or a draw.

ROUTE (complete; the open step named):

1. THE KIND SUB-ROWS APPLIED (§§1–2): the seal sits at its
   foundation top, the stock, the piles, and the waste tail keep
   their cells (`p_wasteToFound_exits`: foundTop pinned, piles and
   stock untouched; §1: no hidden deck moves at all) — so every
   fork-content cell outside the raised suit-rung row is where it
   was, and the taken card is on the board's most protected zone,
   returnable the moment a fitting seat exists (§3's
   `founded_returnable_via_seats` — the seal is a LOAN, and the
   crane's census prices its repayment options:
   `excursion_issues_noNewSeat`, `census_foundToTab_inr` /
   `census_foundToTab_inl` mint exactly the pulled card's cell).
2. THE BOARD-HEADED EXHIBIT (the open step): the head re-fires
   verbatim (guards read piles and foundations; only the eaten
   suit's rung moved) — so the exhibit SHADOWS the commit's seal
   one rung high until (i) a tail leg consults the raised row
   (a `tabToFound`/`foundToTab` of the eaten suit: the rung is
   one ahead, so the successor card is the legal one instead), or
   (ii) the shadow stocks misalign on a recycle.  The repair-time
   schedule is the multi-commit danger the probe program priced
   (`Orig/ForkFloorProbe.lean`: HUNTING-FLOOR HONESTY — the
   finite-economy caveat); the stock REPLY tables (Table 1's
   `cycleCount_step`: the cycle count never rises, drops strictly
   at the waste letters, and the draw conserves it) keep the
   cursor honest on the way: once a cycle read surfaces the
   shifted head, the zone leg re-fires at the successor's own
   cursor, never earlier.
3. THE EMPTY EXHIBIT (the open step): the fork AT the origin keeps
   its pair census outside the raised row; the successor card of
   the raised suit is the one new next-up, and it belongs to the
   schedule's fresh-pair case: either it is pair content (a
   one-rank-up fork re-assembles at s' itself — the fork
   certificate transfers along the board-cells the seal did not
   touch, the flat `canRaiseS_iff` doing the census), or the
   census prices it dead and the seal's own takeback inventory
   re-issues the origin fork (the fb1 heartbeat: expose the
   covering raise, seat the cycle card, rehost the taken seal —
   the `fb1_survives` datapoint is the shape, at decided grade).

PROBE PRICING (round-3; boards NOT added here, per the mission):
`fb2E`/`fb3E` are exactly this remainder's sealed economies —
forkless at the successor, decided — and the corridor's repair
was one leg (`fb2_survives`); the named remainder carries the
eats those snapshots do not cover, the MULTI-LEG repairs, with
the stock-reply tables as the honesty rail.

THE ZONE ARITHMETIC (structural, for the next assembly): the
seal raises exactly ONE suit-rung by one, so at most ONE card's
heat can change at the successor — the unique successor-rank
card of the eaten suit (ABSENT when the eaten card is a king: the
suit tops out; `Rank.toIdx`-uniqueness in suit pins the hot cards
to one).  A waste-resident eaten head is a THIRD PARTY to any
origin fork (the flat shape demands pile residency, against
`mem_waste_unique`), and the eaten card's suit cannot be an
origin-pair suit when the head is hot (the pair-rung pins
forbid).  So the empty-exhibit branch's king-seal and
dead-successor shapes re-exhibit the origin fork VERBATIM — the
LIVE-SUCCESSOR leak is the shape to defuse, and the board-headed
branch's raised-row shadow is the other.

LANDED ALSO (this pass): THE EMPTY-EXHIBIT INTERLOPER CENSUS
(`p_seal_interloper_forced`, §5.0c) — when the exhibiting play is
EMPTY (the fork sits AT the origin, witness `x`) and the successor is
forkless, the interloper census is now theorem-grade: the origin pair
provably reads NO sealed-suit card (the suit's one frontier card is
the eaten waste head, unstackable by `mem_faceUp_only`), and the
license world off the sealed suit is verbatim across the commit, so
the successor's forklessness is FORCED to mint one hot sealed-suit
interloper — S-live at the successor, its rung exactly the sealed
rung plus one.  The empty-exhibit schedule now carries that card as
its input datum in the open branch; the multi-leg expose-and-found
re-scheduling that defuses it (found the interloper when it tops,
dig when it is covered, keeping the origin pair mobile) is the
branch's surviving open content, priced at the probe program's
HUNTING-FLOOR HONESTY.

CLOSED ALSO (this pass): THE SUCCESSOR'S OWN FORK — when the
successor is itself fork-headed, the empty play exhibits it
(`p_successor_fork_repair`, the decidable census bridge).  The
row's sole carried content is its FORKLESS-SUCCESSOR branch.

THIS PASS'S SPINE (the seal-feeding restructure): the forkless
branch is now a SHADOW SPINE — the exhibit splits at its first
SEALED-SUIT OR ZONE consult (`p_shadow_prefix_split`), the
shadow-clean prefix RE-RUNS FROM s' VERBATIM (`p_shadow_run` over
`p_shadow_step`'s letter mirrors: guard reads and writes are
functions of the agreeing piles and the card's own off-sealed row;
the base shape is `p_seal_zone_rows`, and the origin thread's waste
stays resident for the census below), landing the read-world's
mirror `W'`.  The spine prices the residue to exactly two tokens:

* THE ALL-CLEAN ECONOMY, SCAN-FREE — CLOSED HERE.  When the shadow
  landing carries no hot sealed-suit card (`p_sealHotScan` false),
  the witness pair pins prove the pair names NO sealed-suit card
  (a sealed-suit member's rung would read the origin-side sealed
  row — one behind the shadow's — pinning it to the eaten waste
  head itself, which the WF census bars from liveness), and the
  whole fork certificate transfers to the shadow landing along the
  off-rung license world (`p_fork_offRung_transfer` over
  `p_license_offRung` and the vanilla mirror `p_canRaise_offRung`
  built this pass): the exhibit C itself, played from s'.
* THE ALL-CLEAN ECONOMY, SCAN-HOT — the interloper at the shadow
  landing IS the scan's find (sealed suit, rung the sealed rung plus
  one, S-live at W'): the climb's input datum in hand, the token
  carries the expose-and-found re-scheduling alone.
* THE FIRST-CONSULT EXHIBIT — the shadow thread stands congruent at
  the consult's pre-state, and the token carries the repair-time
  schedule ACROSS the consult leg (the raised-row shadow on a
  sealed-suit raise/pull; the cursor read on a draw or waste letter
  over the popped head) — route steps 2-3, the probe program's
  honest danger.

The EMPTY EXHIBIT rides the all-clean arm at the EMPTY prefix (its
forced interloper — `p_seal_interloper_forced`, still the census of
record for the origin economy — is the scan-hot case there), so the
row's two tokens now carry exactly: the interloper climb, and the
first-consult schedule. -/
private theorem p_waste_found_rest {s s' F : State} {c : Card} {x : Card}
    {π : List Move}
    (hwf : s.WF)
    (hstep : State.step s (Move.wasteToFound c) = some s')
    (hivr : irreversibleAt s (Move.wasteToFound c))
    (hrun : s.run π = some F)
    (hwit : ForkWitness F x)
    (hprof : π = [] ∨ ∃ m₀ τ, π = m₀ :: τ ∧ (∀ c', m₀ ≠ Move.wasteToFound c')
      ∧ (∀ c' b', m₀ ≠ Move.wasteToTab c' b')) :
    ∃ (F' : State) (π' : List Move) (x' : Card),
      s'.run π' = some F' ∧ ForkWitness F' x' := by
  by_cases hfb : forkStateSB s' = true
  · exact p_successor_fork_repair (step_wf hwf hstep) hfb
  · -- THE SHADOW SPINE (this pass): the forkless-successor repair.
    --  The exhibit splits at its first SEALED-SUIT OR ZONE consult
    --  (`p_shadow_prefix_split`); the SHADOW-CLEAN prefix re-runs
    --  from s' verbatim along the off-rung mirror (`p_shadow_run`:
    --  the seal's write record `p_seal_zone_rows` is the base shape,
    --  `p_shadow_step`'s letter mirrors are the legs), landing the
    --  read-world's mirror.  What the spine leaves is exactly the
    --  honest danger: the FIRST-CONSULT exhibit below, and — on the
    --  all-clean economy — the one sealed-suit cell the scan can
    --  still find hot at the shadow landing (the climb's input
    --  datum).  THE EMPTY EXHIBIT rides the all-clean arm at the
    --  EMPTY prefix (its interloper IS the scan's hot find).
    obtain ⟨C, D, hsplit, hclean, hD⟩ := p_shadow_prefix_split c.suit π
    obtain ⟨W, hrunC, hrest⟩ :=
      run_append_split s C D F (by rw [← hsplit]; exact hrun)
    obtain ⟨hpiles, -, xs', -, hwaste, hrows, hseal⟩ :=
      p_seal_zone_rows hstep
    obtain ⟨hgC, wC, wsC, -, -⟩ := step_wasteToFound_inv hstep
    rw [Bool.and_eq_true] at hgC
    have hcnext : s.nextUp c = true := hgC.2
    have hcw : c ∈ s.waste := by
      rw [hwaste]
      exact List.mem_cons_self ..
    obtain ⟨W', hrunC', hsh⟩ := p_shadow_run C hclean hrunC
      ⟨hpiles.symm, fun σ' hσ' => (hrows σ' hσ').symm, rfl, rfl, rfl⟩
    obtain ⟨hPp, hR, hPs, hQs, hPw⟩ := hsh
    have hwfW : W.WF := p_run_wf s C W hrunC hwf
    have hwfW' : W'.WF :=
      p_run_wf s' C W' hrunC' (step_wf hwf hstep)
    rcases hD with rfl | ⟨d, D', rfl, hdirty⟩
    · -- THE ALL-CLEAN EXHIBIT: the shadow landing W' mirrors F
      --  itself (W = F here); the scan decides the one question the
      --  spine leaves — is any sealed-suit card still hot at the
      --  shadow landing?
      injection hrest with hWq
      rw [← hWq] at hwit
      by_cases hscan : p_sealHotScan W' c = true
      · -- THE INTERLOPER AT THE SHADOW LANDING (the scan's hot
        --  find: sealed suit, rung exactly the sealed rung plus
        --  one, S-live at W'): the datum the expose-and-found
        --  climb consumes is in hand; the multi-leg re-scheduling
        --  that defuses it (found the interloper when it tops, dig
        --  when it is covered, keeping the origin pair mobile) is
        --  the surviving content, at the probe program's
        --  HUNTING-FLOOR HONESTY.
        sorry
      · -- NO SEALED-SUIT HEAT at the shadow landing: the witness's
        --  pair names no sealed-suit card (a sealed-suit pair
        --  member's rung would read the origin-side sealed row,
        --  pinning it to the sealed card itself — but the sealed
        --  head is WASTE-resident on this thread, and the WF census
        --  bars a card both live and wasted), and the whole
        --  certificate transfers along the off-rung license world:
        --  the exhibit is C itself, played from s'.  CLOSED.
        have hcrl : c.rank.toIdx = (s.found c.suit).length :=
          of_decide_eq_true hcnext
        have hdead : ∀ e, e.suit = c.suit → ¬ CanRaiseS W' e := by
          intro e he hS
          obtain ⟨hnext, -, -, -, -, -, -⟩ := (canRaiseS_iff hwfW').mp hS
          have hr : e.rank.toIdx = (W'.found e.suit).length :=
            of_decide_eq_true hnext
          rw [he] at hr
          rw [show W'.found c.suit = s'.found c.suit from hQs, hseal,
            List.length_append, List.length_singleton] at hr
          exact absurd ((p_sealHotScan_iff hwfW').mpr
            ⟨e, he, by omega, hS⟩) hscan
        obtain ⟨hiff, hnt⟩ := hwit
        have hxpin : x.suit ≠ c.suit ∧ x.twin.suit ≠ c.suit := by
          constructor
          · intro hcon
            obtain ⟨hnext, a, bs, run, hshape, -, -⟩ :=
              (canRaiseS_iff hwfW).mp ((hiff x).mp (Or.inl rfl))
            have hmem : x ∈ (W.piles a).faceUp := by
              rw [hshape]
              exact List.mem_append.2 (Or.inr (List.mem_cons_self ..))
            have hr : x.rank.toIdx = (W.found x.suit).length :=
              of_decide_eq_true hnext
            rw [hcon, hPs] at hr
            have hxc : x = c := by
              have hc₂ : x.rank = c.rank :=
                Rank.toIdx_inj (hr.trans hcrl.symm)
              show (⟨x.suit, x.rank⟩ : Card) = (⟨c.suit, c.rank⟩ : Card)
              rw [hcon, hc₂]
            have hxw : x ∉ W.waste := (mem_faceUp_only hwfW hmem).2.2.2.1
            rw [hxc] at hxw
            exact hxw (by rw [hPw]; exact hcw)
          · intro hcon
            obtain ⟨hnext, a, bs, run, hshape, -, -⟩ :=
              (canRaiseS_iff hwfW).mp ((hiff x.twin).mp (Or.inr rfl))
            have hmem : x.twin ∈ (W.piles a).faceUp := by
              rw [hshape]
              exact List.mem_append.2 (Or.inr (List.mem_cons_self ..))
            have hr : x.twin.rank.toIdx = (W.found x.twin.suit).length :=
              of_decide_eq_true hnext
            rw [hcon, hPs] at hr
            have hxtc : x.twin = c := by
              have hc₂ : x.twin.rank = c.rank :=
                Rank.toIdx_inj (hr.trans hcrl.symm)
              show (⟨x.twin.suit, x.twin.rank⟩ : Card) =
                (⟨c.suit, c.rank⟩ : Card)
              rw [hcon, hc₂]
            have hxw : x.twin ∉ W.waste :=
              (mem_faceUp_only hwfW hmem).2.2.2.1
            rw [hxtc] at hxw
            exact hxw (by rw [hPw]; exact hcw)
        exact ⟨W', C, x, hrunC',
          p_fork_offRung_transfer hwfW hwfW' hPp hR hxpin.1 hxpin.2 hdead
            ⟨hiff, hnt⟩⟩
    · -- THE FIRST-CONSULT EXHIBIT: the shadow thread stands at the
      --  mirror of the consult leg's pre-state ((W, W') congruent);
      --  the leg itself — a sealed-suit raise/pull reading the
      --  one-ahead rung, or a draw/waste letter reading the popped
      --  head the commit's seal removed from the waste — does not
      --  re-fire at the shadow side, and the repair-time schedule
      --  that re-phases across it is the surviving content: the
      --  raised-row shadow and the cursor read, the probe
      --  program's honest danger, the route's steps 2-3 above.
      sorry

/-- **`fork_floor_waste_found`** — **THE WASTE-JUMP KIND RESIDUE**
(pop-to-foundation arm) [M, named residue, exactly one `sorry`]:
the committed waste founding preserves fork-headedness.

ROUTE (the kind read, complete):

1. THE KIND SUB-ROWS APPLIED: the founding exit lands its card at
   the FOUNDATION TOP (§2's prong one — the pull-back letter's own
   guard-fetch names exactly it), stock and piles untouched, hidden
   decks untouched (§1) — the rest of the economy keeps its content
   availability intact.
2. THE REPAIR: the founded card is returnable the moment a fitting
   seat exists (§3's `founded_returnable_via_seats`); the crane's
   census (`excursion_issues_noNewSeat` + the mint/burn ledger)
   prices which seats the arrangement can still issue, so the
   defusing schedule only ever waits out the cycle reads — the
   waste letters never ride witness journeys
   (`witness_leg_letters` in `Orig/HostCensus.lean`), the cycle
   count strictly drops (Table 1) and cannot be re-grown.
3. REMAINING CONTENT: the defusing-schedule repair time bound, in
   this kind the cursor read — matching the cycle arrangement so
   the founding's counterpart letters re-fire on the way to a
   fresh fork.

HEAD-CASES LANDED (§5.0, this pass): the same-head repair
(`p_survives_sameHead`: π = Move.wasteToFound c :: τ, distance zero
— the successor is the play's second state) and the CORRIDOR repair
(`p_waste_eat_corridor`: π = Move.wasteToTab c b :: τ — the other
waste letter on the same head; the one-leg pull `foundToTab c b`
lands the corridor state exactly and the tail replays verbatim,
distance one — the fb2-shape probe verdict, generalized).

ASSEMBLY STRUCTURE (this pass): the kind is now a DISPATCH over
the exhibiting play's head, with the two closed fragments consumed
and the remainder isolated as its own NAMED SUB-RESIDUE
(`p_waste_found_rest` below, per the isolation discipline).  The
SEAL + the STOCK REPLY—— the ate head sits at its foundation top
with the stock, the piles, and the waste tail all untouched except
the found row grew by one card (`p_wasteToFound_exits` +
`step_wasteToFound_inv`'s zone rows) — are the datum the two
fragments ride:

* CLOSED, distance zero — the head-case (`p_survives_sameHead`).
* CLOSED, distance one — the corridor (`p_waste_eat_corridor`):
  the play heads with the sibling waste letter on the eaten head;
  the pull-back lands the corridor state EXACTLY.
* NAMED REMAINDER — `p_waste_found_rest`: the empty exhibit (the
  fork AT the origin: the stock reply cannot help, the seal is
  already down a rung) and the exhibits heading with a board
  letter or a draw.  This is the SEATED-RAISE INTERFERENCE and the
  CURSOR READ together: a board-headed tail re-fires guard-for-guard
  UNTIL it consults the raised row (the successor of the eaten
  card's suit), and a draw-headed tail re-fires until the recycle
  reads the popped zone; the defusing schedule re-derives a fresh
  fork from the seal's takeback inventory (§3's return row prices
  the pull already, `founded_returnable_via_seats`), with
  `excursion_issues_noNewSeat` pricing which seats the arrangement
  can still issue along the way. -/
private theorem fork_floor_waste_found {s s' : State} {c : Card}
    (hwf : s.WF)
    (hstep : State.step s (Move.wasteToFound c) = some s')
    (hivr : irreversibleAt s (Move.wasteToFound c))
    (hhed : ∃ (F : State) (π : List Move) (x : Card),
        s.run π = some F ∧ ForkWitness F x) :
    ∃ (F' : State) (π' : List Move) (x' : Card),
        s'.run π' = some F' ∧ ForkWitness F' x' := by
  -- the eaten head, read off the commit's own guard (the two waste
  -- letters of this kind both name it)
  obtain ⟨hgC, wC, wsC, hwC, -⟩ := step_wasteToFound_inv hstep
  rw [Bool.and_eq_true] at hgC
  obtain ⟨w₀, hw₀⟩ := wasteIs_head hgC.1
  obtain ⟨F, π, x, hrun, hwit⟩ := hhed
  cases π with
  | nil =>
      exact p_waste_found_rest hwf hstep hivr hrun hwit (Or.inl rfl)
  | cons m₀ τ =>
      obtain ⟨q₁, hstep₀, htail⟩ := State.run_cons hrun
      cases m₀ with
      | draw =>
          exact p_waste_found_rest hwf hstep hivr hrun hwit
            (Or.inr ⟨Move.draw, τ, rfl,
              fun c' hcon => absurd hcon (by simp),
              fun c' b' hcon => absurd hcon (by simp)⟩)
      | wasteToFound c₀ =>
          obtain ⟨hg₀, w₁, ws₁, hw₁, -⟩ := step_wasteToFound_inv hstep₀
          rw [Bool.and_eq_true] at hg₀
          obtain ⟨w₂, hw₂⟩ := wasteIs_head hg₀.1
          injection hw₂.symm.trans hw₀ with hc₀ _
          have hc : c = c₀ := hc₀.symm
          subst hc
          exact p_survives_sameHead hstep hrun hwit
      | wasteToTab c₀ b₀ =>
          obtain ⟨hg₀, w₁, ws₁, hw₁, -⟩ := step_wasteToTab_inv hstep₀
          rw [Bool.and_eq_true] at hg₀
          obtain ⟨w₂, hw₂⟩ := wasteIs_head hg₀.1
          injection hw₂.symm.trans hw₀ with hc₀ _
          have hc : c = c₀ := hc₀.symm
          subst hc
          exact p_waste_eat_corridor hstep hstep₀ htail hwit
      | tabToFound c₀ =>
          exact p_waste_found_rest hwf hstep hivr hrun hwit
            (Or.inr ⟨Move.tabToFound c₀, τ, rfl,
              fun c' hcon => absurd hcon (by simp),
              fun c' b' hcon => absurd hcon (by simp)⟩)
      | foundToTab c₀ b₀ =>
          exact p_waste_found_rest hwf hstep hivr hrun hwit
            (Or.inr ⟨Move.foundToTab c₀ b₀, τ, rfl,
              fun c' hcon => absurd hcon (by simp),
              fun c' b' hcon => absurd hcon (by simp)⟩)
      | tabToTab c₀ b₀ =>
          exact p_waste_found_rest hwf hstep hivr hrun hwit
            (Or.inr ⟨Move.tabToTab c₀ b₀, τ, rfl,
              fun c' hcon => absurd hcon (by simp),
              fun c' b' hcon => absurd hcon (by simp)⟩)

/-- **THE EMPTY-ANCHOR KING'S ONE-LEG ROTATION** [E–M, PROVED] —
the seating kind's rotation datum for the empty exhibit: when the
seated head is a king whose own rung was ALREADY hot at the origin,
the ONE-LEG raise `tabToFound c` re-fires at the seating successor
and lands EXACTLY the state the DIRECT seal `wasteToFound c`
produces at the origin — the seating's popped waste tail and the
foundation row carry verbatim, and the raised pile's record empties
back to the origin's own fully-empty seat (the pre-seat pile was
empty in both decks, so the raise's chop restores the empty
record).  The fb1-heartbeat shape at theorem grade; consumed by
`p_seat_inl_rotation_fork` below. -/
private theorem p_seat_inl_seal_rotate {s s' : State} {c : Card} {k : Anchor}
    (hwf : s.WF)
    (hstep : State.step s (Move.wasteToTab c (Sum.inl k)) = some s')
    (hhot : s.nextUp c = true) :
    ∃ r, State.step s' (Move.tabToFound c) = some r ∧
      State.step s (Move.wasteToFound c) = some r := by
  obtain ⟨hg, w, ws, hwaste, hsq⟩ := step_wasteToTab_inv hstep
  rw [Bool.and_eq_true] at hg
  have hcw : w = c := State.wasteIs_head_eq hwaste hg.1
  rw [hcw] at hwaste
  obtain ⟨hemp, -, hs'f, -, hpilek⟩ := p_seat_inl_records hstep
  obtain ⟨-, hnextA, -, -, -⟩ := p_seat_reads_inl hstep
  rcases hp : s.piles k with ⟨hdk, hfk⟩
  rw [hp] at hemp
  obtain ⟨hhid, hfu⟩ := (Pile.isEmpty_eq _).mp hemp
  have hhdk : hdk = [] := hhid
  have hhfk : hfk = [] := hfu
  subst hhdk
  subst hhfk
  have hwfs' : s'.WF := step_wf hwf hstep
  have hnext' : s'.nextUp c = true := by rw [hnextA c]; exact hhot
  have htop' : s'.topOf k = some c := by
    show (s'.piles k).top = some c
    rw [hpilek]
    rfl
  have hpo' : s'.pileOfTop c = some k := (pileOfTop_eq_some_iff hwfs').2 htop'
  have hsplice := step_tabToFound_splice hnext' hpo'
  have hrest : Pile.afterRunRemoved (s'.piles k)
      (chop (s'.piles k).faceUp) = s.piles k := by
    rw [hpilek, hp]
    rfl
  have hgt : (s.wasteIs c && s.nextUp c) = true := by
    rw [Bool.and_eq_true]
    exact ⟨hg.1, hhot⟩
  have hseal : State.step s (Move.wasteToFound c)
      = some { s.setFound c.suit (s.found c.suit ++ [c]) with waste := ws } := by
    show (if s.wasteIs c && s.nextUp c then
        match s.waste with
        | _ :: wsl => some { s.setFound c.suit (s.found c.suit ++ [c]) with waste := wsl }
        | [] => none
      else none) = some _
    rw [ite_eq_left hgt, hwaste]
  refine ⟨{ s.setFound c.suit (s.found c.suit ++ [c]) with waste := ws }, ?_, ?_⟩
  · rw [hsplice]
    refine congrArg some (State.ext (funext fun σ => ?_)
      (funext fun a => ?_) ?_ ?_ ?_)
    · show (if σ = c.suit then s'.found c.suit ++ [c] else s'.found σ)
        = (if σ = c.suit then s.found c.suit ++ [c] else s.found σ)
      by_cases hσ : σ = c.suit
      · rw [ite_eq_left hσ, ite_eq_left hσ, hs'f]
      · rw [ite_eq_right hσ, ite_eq_right hσ]
        exact congrFun hs'f σ
    · show (if a = k then
          Pile.afterRunRemoved (s'.piles k) (chop (s'.piles k).faceUp)
        else s'.piles a) = s.piles a
      by_cases hak : a = k
      · rw [ite_eq_left hak, hak, hrest]
      · rw [ite_eq_right hak]
        show s'.piles a = s.piles a
        rw [hsq]
        show (s.putCard c (Sum.inl k)).piles a = _
        rw [putCard_eq_inl]
        exact setPile_piles_ne hak
    · show s'.stock = s.stock
      rw [hsq]
      show (s.putCard c (Sum.inl k)).stock = s.stock
      exact putCard_stock s c (Sum.inl k)
    · show s'.waste = ws
      rw [hsq]
    · show s'.drawStep = s.drawStep
      rw [hsq]
      show (s.putCard c (Sum.inl k)).drawStep = s.drawStep
      exact putCard_drawStep s c (Sum.inl k)
  · exact hseal

/-- **THE EMPTY-ANCHOR ROTATION CLOSURE** [M, PROVED AS AN ASSEMBLY
over the sibling residue — its `sorryAx` flows only from the
consumed `p_waste_found_rest`]: at the empty exhibit with the seated
head a king whose own rung was already hot at the origin, the
seating economy ROUTES INTO the waste-founding kind's own residue:
the one-leg rotation lands the direct seal's successor verbatim
(`p_seat_inl_seal_rotate`, the seal's irreversibility the banked
unconditional `irreversibleAt_wasteToFound` of `Orig/Classify.lean`),
the origin fork rides as the seal's EMPTY exhibit, and any fork the
seal schedule re-issues from the seal successor lifts back to the
seating successor along the rotation's own first leg.  The
COLD-king corner (the born top keeps the twin's maneuver disjunct
alive at the successor while the origin's waste residency forbids
it — the twin-cover face of the covered-host search freedom) and the
CARD-HOST arm stay at the seating kind's own token; the headed
exhibits carry the covered-top shadow and the cursor read as
before. -/
private theorem p_seat_inl_rotation_fork {s s' : State} {c : Card} {k : Anchor}
    {x : Card}
    (hwf : s.WF)
    (hstep : State.step s (Move.wasteToTab c (Sum.inl k)) = some s')
    (hhot : s.nextUp c = true)
    (hwit : ForkWitness s x) :
    ∃ (F' : State) (π' : List Move) (x' : Card),
      s'.run π' = some F' ∧ ForkWitness F' x' := by
  obtain ⟨r, hraise, hseal⟩ := p_seat_inl_seal_rotate hwf hstep hhot
  obtain ⟨F', π', x', hrun', hwit'⟩ :=
    p_waste_found_rest hwf hseal (irreversibleAt_wasteToFound s c)
      (rfl : s.run ([] : List Move) = some s) hwit (Or.inl rfl)
  refine ⟨F', Move.tabToFound c :: π', x', ?_, hwit'⟩
  show (match State.step s' (Move.tabToFound c) with
      | some st' => st'.run π'
      | none => none) = some F'
  rw [hraise]
  exact hrun'

/-- **THE WASTE-SEATING ARM'S NAMED REMAINDER** [M–H, named
sub-residue, exactly one `sorry` — the waste-seating kind's
carried content once the same-head and the mirror are
dispatched]: the exhibiting play is EMPTY, heads with a board
letter (raise / pull / cargo) or a draw, or seats the SAME eaten
head at a DIFFERENT base.

ROUTE (complete; the open step named):

1. THE KIND SUB-ROWS APPLIED (§§1–2): the seated card lands
   FACE-UP in a playable pile with foundations, stock, and the
   waste tail untouched (`p_wasteToTab_exits` + the zone rows of
   `step_wasteToTab_inv`) — the economy outside the landing pile
   keeps its availability intact, and no hidden deck moved at all
   (§1).
2. THE GUARD REFUSAL (the open step, the kind's own): a re-seat
   consult `canPlace c b'` reads a pile-top record the commit's
   own write may have changed — the seated card COVERS the landing
   pile's old top, so a π-head consult on that old top now
   refuses, and the different-base re-seat of the same head must
   wait out the schedule (slide the run atop the old top's cover
   first, or route the seat elsewhere) — the guard refusal is
   the honest entry point of the multi-commit schedule, the probe
   program's surviving danger (HUNTING-FLOOR HONESTY,
   `Orig/ForkFloorProbe.lean`); the mint/burn ledger
   (`seatLedger_pair`, `play_census_ledger`) prices the seat the
   commit minted, and `excursion_issues_noNewSeat` bounds what
   returned excursions can add.
3. THE OTHER EXHIBITS (the open step): the board-headed tails
   shadow the commit's pile-write (the added card rides atop
   whatever run consults the landing pile, the mirror's own
   chop-restoration gone) until a tail leg consumes it; the
   draw-headed tails fork into the same cursor read as the
   founding arm (`p_waste_found_rest`'s step 2 — the zone
   tables of Table 1 ride both arms identically).  The
   repair-time bound is the same multi-commit danger, unchanged.

PROBE PRICING: `fb2E`'s junk cells refused on color
   (`fb2_junkCold`: decided both grades) are this remainder's
   guard-refusal content at decided grade — the refuses are
   REAL, and the schedule must route around them, as the boards'
   repairs did in one leg (`fb2_survives`).

THE GUARD-REFUSAL TRANSPORT (structural, for the next assembly):
the seating writes NO rung (pair-rung pins untouched) and writes
exactly one pile — the landing pile: the old top covered, the
seated card atop it.  The empty-exhibit branch's genuine danger
is the seating DIRECTLY ONTO the origin witness: the pair's
mutual twin-top pin dies BOTH ways (the covered witness's
covered-arm needs its twin topping; the covered twin's arm needs
the witness topping — the mutual freeze).  The re-seat consults
(`canPlace c b'` over the covered-top record) and the
witness-cover schedules are the shapes to defuse.

CLOSED ALSO (this pass): THE SUCCESSOR'S OWN FORK — when the
successor is itself fork-headed, the empty play exhibits it
(`p_successor_fork_repair`, the decidable census bridge).  The
row's sole carried content is its FORKLESS-SUCCESSOR branch.

LANDED ALSO (this pass): THE EMPTY-EXHIBIT INTERFERENCE CENSUS
(`p_seat_interference_forced`, §5.0c) — when the exhibiting play is
EMPTY (the fork sits AT the origin) and the successor is forkless,
the origin pair provably reads no c-family card (the seated head was
waste-resident before the commit; the twin corner falls to the pair
closure the same way), and at the EMPTY-ANCHOR economy the seating
writes no rung at all, so the successor's forklessness is FORCED to
mint a c-family HOT read — the seated king's own rung, or its
twin's (`p_seat_inl_hot_forced`, proved zero-`sorryAx`).  The
CARD-HOST economy is the disjunct's remaining arm: the covered top,
the twin-cover corners, and the search exceptions of
`p_seat_reads_inr` are the row's own open geometry, carried at the
token below with the probe program's fb2E junk-refusal pricing.

THIS PASS narrows the empty-exhibit token to exactly those honest
corners: the EMPTY-ANCHOR HOT-KING sub-case is now CLOSED through
the ONE-LEG ROTATION (`p_seat_inl_seal_rotate` +
`p_seat_inl_rotation_fork`, landed between this row and its sibling
kind): the seated king's own-rung hot read is the rotation's
premise, and the whole sub-case dispatches to the waste-founding
kind's own residue over the origin fork.  The COLD-king corner
(where the born top keeps the twin's maneuver disjunct alive — the
inl-side face of the covered-host search freedom) and the
CARD-HOST arm stay at the token. -/
private theorem p_waste_seat_rest {s s' F : State} {c : Card} {b : Base}
    {x : Card} {π : List Move}
    (hwf : s.WF)
    (hstep : State.step s (Move.wasteToTab c b) = some s')
    (hivr : irreversibleAt s (Move.wasteToTab c b))
    (hrun : s.run π = some F)
    (hwit : ForkWitness F x)
    (hprof : π = [] ∨ ∃ m₀ τ, π = m₀ :: τ ∧ m₀ ≠ Move.wasteToFound c
      ∧ m₀ ≠ Move.wasteToTab c b) :
    ∃ (F' : State) (π' : List Move) (x' : Card),
      s'.run π' = some F' ∧ ForkWitness F' x' := by
  by_cases hfb : forkStateSB s' = true
  · exact p_successor_fork_repair (step_wf hwf hstep) hfb
  · -- the forkless-successor repair: this row's sole carried content,
    --  over the SEAT CENSUS LANDED THIS PASS (§5.0c): the commit's
    --  write records `p_seat_inl_records`/`p_seat_inr_records`
    --  (foundations verbatim, one pile written, the seated card
    --  appended atop its host or the anchor's bare king record),
    --  `p_seat_gain` (the seated cell's license is exactly its
    --  unchanged `nextUp` read), `p_seat_refusal_cover` (the
    --  GUARD-REFUSAL TRANSPORT: after the seat covers its host top,
    --  every card-hosted placement consult on that host refuses),
    --  and `p_seat_reads_inl`/`p_seat_reads_inr` (every rung, pile,
    --  and top-search read outside the written pile and the two
    --  named cells is verbatim).  THE EMPTY-EXHIBIT ARM'S FIRST
    --  CENSUS IS LANDED THIS PASS (`p_seat_interference_forced`):
    --  at the empty-anchor economy the forklessness forces a
    --  c-family HOT read (the seated king's rung or its twin's), and
    --  the card-host arm names the covered-host economy — the token
    --  below carries the forced disjunction as its input datum; the
    --  guard-refusal re-scheduling (route steps 2-4) is the
    --  surviving content.  The HEADED exhibits (board/draw heads)
    --  carry the covered-top shadow and the cursor read as before.
    rcases hprof with rfl | ⟨m₀, τ, hheadEq, hneF, hneT⟩
    · -- the empty exhibit: the fork sat at the origin.  THIS PASS
      -- closes the EMPTY-ANCHOR HOT-KING sub-case through the
      -- ONE-LEG ROTATION into the waste-founding kind's own residue
      -- (`p_seat_inl_rotation_fork`: the raise `tabToFound c`
      -- re-fires at the seating successor and lands the DIRECT
      -- seal's successor verbatim, the origin fork riding as the
      -- seal's empty exhibit).  Surviving corners at the token:
      -- the COLD seated king (the born top keeps the twin's
      -- maneuver disjunct alive at the successor — the twin-cover
      -- face of the covered-host search freedom) and the CARD-HOST
      -- arm's covered-top geometry, with the §5.0c forced
      -- disjunction the cold-king corner's input datum.
      injection hrun with hFs
      subst hFs
      have hcase : ((∃ k₀, b = Sum.inl k₀ ∧ s.nextUp c = false) ∨
          ∃ z, b = Sum.inr z) ∨
          ∃ k₀, b = Sum.inl k₀ ∧ s.nextUp c = true := by
        cases b with
        | inl k₀ =>
            by_cases hhot : s.nextUp c = true
            · exact Or.inr ⟨k₀, rfl, hhot⟩
            · refine Or.inl (Or.inl ⟨k₀, rfl, ?_⟩)
              cases hb : s.nextUp c with
              | true => exact absurd hb hhot
              | false => rfl
        | inr z => exact Or.inl (Or.inr ⟨z, rfl⟩)
      rcases hcase with hleft | ⟨k₀, hbk, hhot⟩
      · sorry
      · subst hbk
        exact p_seat_inl_rotation_fork hwf hstep hhot hwit
    · -- the headed exhibits: the board/draw heads carry the
      -- covered-top shadow and the cursor read as before
      sorry

/-- **`fork_floor_waste_seat`** — **THE WASTE-JUMP KIND RESIDUE**
(seating arm) [M, named residue, exactly one `sorry`]: the committed
waste seating preserves fork-headedness.

ROUTE (the kind read, complete): as the pop-to-foundation arm
(`fork_floor_waste_found`'s steps 1–3), with the exit's landing read
off §2's prong two — the moved card lands FACE-UP in a pile (the
playable zone), foundations and stock untouched — and the
defusing schedule additionally consulting the landing base's top
seat, census-priced by the ledger family
(`census_tabToTab_inr_witness`, `census_foundToTab_inr`) as in
`Orig/HostCensus.lean`'s §3–§5; the same cycle-cells and the same
remaining content (the cursor read / repair time bound).

HEAD-CASE LANDED (§5.0, this pass): `p_survives_sameHead` — when the
exhibiting play heads with the very seating that committed (π =
Move.wasteToTab c b :: τ), the successor is the play's second state
and the tail replays verbatim, distance zero.

ASSEMBLY STRUCTURE (this pass): the kind is now a DISPATCH over
the exhibiting play's head, with two fragments CLOSED and the
remainder isolated as its own NAMED SUB-RESIDUE
(`p_waste_seat_rest` below, per the isolation discipline) — the
GUARD REFUSAL datum rides the remainder's premise (every fall
shape heads neither with the commit itself nor with the founding
letter on the seated head):

* CLOSED, distance zero — the same-seating head-case
  (`p_survives_sameHead`).
* CLOSED, distance one — THE MIRROR (`p_waste_seat_mirror`, §5.0b):
  the play heads with the OTHER waste letter on the same head, the
  founding `wasteToFound c`; the seating wrote no foundation, so
  the founding's own next-up guard still reads true at the
  successor and the one-move raise `tabToFound c` lands the
  play's second state EXACTLY — the fb2-shape sibling, mirrored
  (the probe's `fb2_corridor` was the eat-with-seat-head pairing;
  this is the seat-with-eat-head one).  Both landing arms are
  theorems: the seat-appended pile restores (`chop_snoc` +
  `afterRunRemoved_ne`, the inr base) and the king seat empties
  back to its pre-seat record (the inl base, `putCard_eq_inl`).
* NAMED REMAINDER — `p_waste_seat_rest`: the empty exhibit, the
  board/draw-headed exhibits, and the exhibits seating the SAME
  head at a DIFFERENT base: the GUARD REFUSAL cases (the re-seat
  consult `canPlace c b'` reads a pile-of-top record the commit's
  own seat write may have moved), plus the cursor read — this
  remainder carries them with the full route. -/
private theorem fork_floor_waste_seat {s s' : State} {c : Card} {b : Base}
    (hwf : s.WF)
    (hstep : State.step s (Move.wasteToTab c b) = some s')
    (hivr : irreversibleAt s (Move.wasteToTab c b))
    (hhed : ∃ (F : State) (π : List Move) (x : Card),
        s.run π = some F ∧ ForkWitness F x) :
    ∃ (F' : State) (π' : List Move) (x' : Card),
        s'.run π' = some F' ∧ ForkWitness F' x' := by
  -- the seated head, off the commit's own guard
  obtain ⟨hgC, wC, wsC, hwC, -⟩ := step_wasteToTab_inv hstep
  rw [Bool.and_eq_true] at hgC
  obtain ⟨w₀, hw₀⟩ := wasteIs_head hgC.1
  obtain ⟨F, π, x, hrun, hwit⟩ := hhed
  cases π with
  | nil =>
      exact p_waste_seat_rest hwf hstep hivr hrun hwit (Or.inl rfl)
  | cons m₀ τ =>
      obtain ⟨q₁, hstep₀, htail⟩ := State.run_cons hrun
      cases m₀ with
      | draw =>
          exact p_waste_seat_rest hwf hstep hivr hrun hwit
            (Or.inr ⟨Move.draw, τ, rfl,
              fun hcon => absurd hcon (by simp),
              fun hcon => absurd hcon (by simp)⟩)
      | wasteToFound c₀ =>
          obtain ⟨hg₀, w₁, ws₁, hw₁, -⟩ := step_wasteToFound_inv hstep₀
          rw [Bool.and_eq_true] at hg₀
          obtain ⟨w₂, hw₂⟩ := wasteIs_head hg₀.1
          injection hw₂.symm.trans hw₀ with hc₀ _
          have hc : c = c₀ := hc₀.symm
          subst hc
          exact p_waste_seat_mirror hwf hstep hstep₀ htail hwit
      | wasteToTab c₀ b₀ =>
          obtain ⟨hg₀, w₁, ws₁, hw₁, -⟩ := step_wasteToTab_inv hstep₀
          rw [Bool.and_eq_true] at hg₀
          obtain ⟨w₂, hw₂⟩ := wasteIs_head hg₀.1
          injection hw₂.symm.trans hw₀ with hc₀ _
          have hc : c = c₀ := hc₀.symm
          subst hc
          by_cases hb : b₀ = b
          · have hbb : b = b₀ := hb.symm
            subst hbb
            exact p_survives_sameHead hstep hrun hwit
          · exact p_waste_seat_rest hwf hstep hivr hrun hwit
              (Or.inr ⟨Move.wasteToTab c b₀, τ, rfl,
                fun hcon => absurd hcon (by simp),
                fun hcon => by
                  injection hcon with _ hcc
                  exact absurd hcc hb⟩)
      | tabToFound c₀ =>
          exact p_waste_seat_rest hwf hstep hivr hrun hwit
            (Or.inr ⟨Move.tabToFound c₀, τ, rfl,
              fun hcon => absurd hcon (by simp),
              fun hcon => absurd hcon (by simp)⟩)
      | foundToTab c₀ b₀ =>
          exact p_waste_seat_rest hwf hstep hivr hrun hwit
            (Or.inr ⟨Move.foundToTab c₀ b₀, τ, rfl,
              fun hcon => absurd hcon (by simp),
              fun hcon => absurd hcon (by simp)⟩)
      | tabToTab c₀ b₀ =>
          exact p_waste_seat_rest hwf hstep hivr hrun hwit
            (Or.inr ⟨Move.tabToTab c₀ b₀, τ, rfl,
              fun hcon => absurd hcon (by simp),
              fun hcon => absurd hcon (by simp)⟩)

/-- **THE RAISE ARM'S NAMED REMAINDER** [H, named sub-residue,
exactly one `sorry` — the raise kind's carried content once the
head-case is dispatched]: the exhibiting play is EMPTY, or heads
with a letter other than the very founding that committed (a
different founding letter, a pull, a cargo slide, a waste letter,
or a draw).

ROUTE (complete; the open step named):

1. THE KIND SUB-ROWS APPLIED (§§1, 3): the committed founding
   empties the raised pile's chop and is one of exactly the two
   census arms (`p_committed_raise_shape`: reveal — the hidden
   head surfaces — or bare-non-king — the seat goes fully bare);
   the founded card sits at its foundation top, returnable the
   moment a fitting seat exists (§3's `founded_returnable_via_seats`,
   both prongs); the zone cells are untouched (Table 1 flat
   through the board letters); the reveal arm strictly drops the
   hidden total (`hiddenTotal_step_tabToFound_reveal`) and never
   rides back.
2. THE RAISED-ROW SHADOW (the open step): the raised suit's rung
   is one ahead of every pre-commit read, so a tail's
   `tabToFound`/`foundToTab` legs on that suit consult a rung the
   shadow does not carry — the same raised-row interference as
   the waste-founding arm's step 2, read at the raise kind's own
   grain; the census classification prices the exchange
   (`census_tabToFound_witness`: the riding raise exchanges exact
   cells with the exposed below-card — opposite family, index +
   1, unfounded), and the seat re-issue schedule is the crown's
   own content, consumed here as `founded_late_seat_exists`'s
   installment.
3. REMAINING CONTENT: the defusing-schedule repair TIME bound — a
   measure strictly decreasing along the schedule that re-fires
   the raise letters (and the founding's takeback) until a fresh
   fork witness re-assembles; the rung bracket
   (`witness_rung_census`-grade bookkeeping) is shared with the
   Low-Slab program's own raise route, not re-priced here.

PROBE PRICING: `fb1` IS this remainder's own board — the
committed bare-non-king raise, its pair census untouched by the
seat clause (`fb1S_forkSB`: the successor itself the fork,
distance zero because the eaten cell was never pair content);
the direct return seats refused (`fb1S_sealRefused`), the
multi-leg expose-and-seat repair attested (`fb1_survives` rides
the trivial journey — the LEGGED repair the probe did not need
in that economy is what this remainder carries, with
`fb2`/`fb3`'s one-leg corridors as the attained floor).

THE SINGLE-RUNG FACT (structural, for the next assembly): the
founding raises exactly ONE suit-rung by one (the index-exact
climb), so the successor's heat change is confined to the
founding suit's successor-rank card; the raised pile's own
emptied record (revealed or fully bare, `p_committed_raise_shape`)
is the other written cell.  The shapes to defuse: the
live-successor leak and the emptied-pile shadow.

CLOSED ALSO (this pass): THE SUCCESSOR'S OWN FORK — when the
successor is itself fork-headed, the empty play exhibits it
(`p_successor_fork_repair`, the decidable census bridge).  The
row's sole carried content is its FORKLESS-SUCCESSOR branch. -/
private theorem p_raise_rest {s s' F : State} {c : Card} {x : Card}
    {π : List Move}
    (hwf : s.WF)
    (hstep : State.step s (Move.tabToFound c) = some s')
    (hivr : irreversibleAt s (Move.tabToFound c))
    (hrun : s.run π = some F)
    (hwit : ForkWitness F x)
    (hprof : π = [] ∨ ∃ m₀ τ, π = m₀ :: τ ∧ m₀ ≠ Move.tabToFound c) :
    ∃ (F' : State) (π' : List Move) (x' : Card),
      s'.run π' = some F' ∧ ForkWitness F' x' := by
  by_cases hfb : forkStateSB s' = true
  · exact p_successor_fork_repair (step_wf hwf hstep) hfb
  · -- the forkless-successor repair: this row's sole carried content,
    --  over the RAISE-SHAPE CENSUS LANDED AT THE PRIOR PASS and the
    --  reveal-membership kit landed this pass (§5.0c:
    --  `p_committed_raise_shape` pins the commit's two arms — the
    --  surface reveal with its hidden tail, or the bare-non-king
    --  emptying — and `p_mem_afterRunRemoved` reads the raised
    --  pile's new face-up record against the old two decks); the
    --  raise-kind's own per-card license census (the rung cell at
    --  the raised suit, the two written pile cells) remains to be
    --  landed, and the seat-lease re-scheduling (route steps 2-4)
    --  remains this row's content.
    sorry

/-- **`fork_floor_raise`** — **THE RAISE-LIKE KIND RESIDUE** [H,
named residue, exactly one `sorry`]: the committed tableau founding
preserves fork-headedness.

ROUTE (the kind read, complete):

1. THE KIND SUB-ROWS APPLIED: the founding raises its suit's rung
   by exactly one (the index-exact climb); the touched pile's
   hidden deck either survives or reveals (§1's cons-tail form) —
   a reveal strictly drops the hidden total and never rides back;
   the foundations elsewhere and the whole draw zone are untouched
   — so the consumed fork's package (pair mobility, cover
   mobility, low-card raisability per the index-exact climb)
   survives at s' at least to within a defusing-schedule repair.
2. THE REPAIR, VIA §3: the founded card sits at its foundation top
   (`founded_returnable_via_seats` prong one), returns the moment a
   fitting seat exists (prong two); `founded_late_seat_exists` is
   this kind's schedule installment — the seat is re-issued along
   the commit DAG below the founding successor.  The census heads
   price everything local: `census_tabToFound_witness` (the riding
   raise exchanges exact cells with the exposed below-card, which
   is opposite-family, index + 1, unfounded) and
   `excursion_issues_noNewSeat` (the crane's loan-and-repay — no
   hosting capacity survives a returned excursion the arrangement
   did not already carry).
3. REMAINING CONTENT: the defusing-schedule repair time bound — a
   measure strictly decreasing along the schedule that re-fires
   the raise letters (and the founding's takeback) until a fresh
   fork witness re-assembles; the rung bracket (`witness_rung_census`-grade
   bookkeeping) is shared with the Low-Slab program's own raise
   route, not re-priced here.

HEAD-CASES LANDED (this pass): `p_survives_sameHead` (§5.0: the
exhibiting play heads with the very founding that committed, π =
Move.tabToFound c :: τ, distance zero); and the input-shape
dichotomy `p_committed_raise_shape` (§3): a committed founding at
WF empties the raised pile's chop and is one of exactly the two
census arms — reveal, or bare-non-king — so the defusing schedule's
starting shape is pinned for this kind.

ASSEMBLY STRUCTURE (this pass): the kind is now a DISPATCH over
the exhibiting play's head, with the head-case CLOSED and the
remainder isolated as its own NAMED SUB-RESIDUE (`p_raise_rest`
below, per the isolation discipline): the exhibits heading with
the very same founding ride `p_survives_sameHead` verbatim; the
empty exhibit and the exhibits heading with a DIFFERENT founding
letter, a pull, a cargo slide, or a draw fall to the remainder,
whose premise records the excluded head.  The census
classification the route names (`census_tabToFound_witness`'s
two reversible arms — seated transfer, with the exposed below-card
OPPOSITE family, index + 1, unfounded, and the bare-king
departure) plus the bracket bar (`p_committed_raise_shape`) are
the SIM SHAPE the remainder's schedule climbs from. -/
private theorem fork_floor_raise {s s' : State} {c : Card}
    (hwf : s.WF)
    (hstep : State.step s (Move.tabToFound c) = some s')
    (hivr : irreversibleAt s (Move.tabToFound c))
    (hhed : ∃ (F : State) (π : List Move) (x : Card),
        s.run π = some F ∧ ForkWitness F x) :
    ∃ (F' : State) (π' : List Move) (x' : Card),
        s'.run π' = some F' ∧ ForkWitness F' x' := by
  obtain ⟨F, π, x, hrun, hwit⟩ := hhed
  cases π with
  | nil => exact p_raise_rest hwf hstep hivr hrun hwit (Or.inl rfl)
  | cons m₀ τ =>
      cases m₀ with
      | draw =>
          exact p_raise_rest hwf hstep hivr hrun hwit
            (Or.inr ⟨Move.draw, τ, rfl, fun hcon => absurd hcon (by simp)⟩)
      | tabToFound c₀ =>
          by_cases hc : c₀ = c
          · have hcc : c = c₀ := hc.symm
            subst hcc
            exact p_survives_sameHead hstep hrun hwit
          · exact p_raise_rest hwf hstep hivr hrun hwit
              (Or.inr ⟨Move.tabToFound c₀, τ, rfl, by
                  intro hcon
                  injection hcon with hcc₂
                  exact absurd hcc₂ hc⟩)
      | wasteToFound c₀ =>
          exact p_raise_rest hwf hstep hivr hrun hwit
            (Or.inr ⟨Move.wasteToFound c₀, τ, rfl,
              fun hcon => absurd hcon (by simp)⟩)
      | wasteToTab c₀ b₀ =>
          exact p_raise_rest hwf hstep hivr hrun hwit
            (Or.inr ⟨Move.wasteToTab c₀ b₀, τ, rfl,
              fun hcon => absurd hcon (by simp)⟩)
      | foundToTab c₀ b₀ =>
          exact p_raise_rest hwf hstep hivr hrun hwit
            (Or.inr ⟨Move.foundToTab c₀ b₀, τ, rfl,
              fun hcon => absurd hcon (by simp)⟩)
      | tabToTab c₀ b₀ =>
          exact p_raise_rest hwf hstep hivr hrun hwit
            (Or.inr ⟨Move.tabToTab c₀ b₀, τ, rfl,
              fun hcon => absurd hcon (by simp)⟩)

/-- **THE REVEAL ARM'S NAMED REMAINDER** [H, named sub-residue,
exactly one `sorry` — the reveal kind's carried content once the
exact-slide head-case is dispatched]: the exhibiting play is EMPTY,
or heads with a letter other than the very slide that committed (a
different slide letter or a different base, a raise, a waste
letter, a pull, or a draw).

ROUTE (complete; the open step named):

1. THE KIND SUB-ROWS APPLIED (§§1–2): the committed slide is one
   of the two census-barred shapes — a REVEALING slide (the
   source pile's deck pays its head; the hidden total strictly
   drops, `journey_tabToTab_never_reveal` +
   `hiddenTotal_step_tabToTab_reveal`) or a BARE BURN (the bare
   source empties entirely, `bare_burn_irreversibleAt`); in both
   the SOURCE PILE's face-up run departs whole, so the successor
   differs from the commit predecessor exactly at the source
   pile's record (revealed or empty) and at the cargo-landing
   pile — the two-cell WRITE the schedule must absorb.  The
   foundations and the whole draw zone are untouched (the
   ratchet board is the tableau); the zone RE-ENTRY is closed by
   the reveal cell of the pillar argument.
2. THE TWO-CELL SHADOW (the open step): a tail leg consults the
   written cells as soon as it reads the source pile's old top
   (now covered or revealed) or seats on the moved run (whose
   below-record changed at the landing pile) — the exhibits that
   headed accordingly cannot replay verbatim, and the repair
   re-schedules the slide so the mobile run re-forms at a
   slab-side member; `census_tabToTab_inr_witness`'s identity-cell
   neutrality (the exposed below-card sits in the consumed host's
   exact cell) and the crane's loan-and-repay
   (`excursion_issues_noNewSeat`) price which hosts the
   arrangement can still issue on the way — the census LOANS
   are the schedule's budget.
3. REMAINING CONTENT: the defusing-schedule repair TIME bound
   over the two-census-arm write — the multi-commit danger, the
   probe program's surviving honest danger (the written cells
   can never be un-written: the reveal arm's surfaced head never
   re-hides, §1's own law), carried here and nowhere else.

PROBE PRICING: `fb3`'s committed reveal channel is this
remainder's own board (`fb3_revealA_commit`: jury-barred,
monotone-graded) and its cascades are priced at decided grade —
the surfaced low S-DEAD at the surfacing (`fb3W_lowSeatedBar`,
the seat clause), the seated attempt another commitment
(`fb3_seatTryCommit`), the seated state forkless with the twin
entombed behind the frozen host (`fb3X_notFork`, `fb3X_twinBuried`)
while the EAT arm's corridor was one leg (`fb3_survives`) — the
evidence that even on the reveal-heavy economies the floor's
danger is the schedule's LENGTH, not a break.

THE TWO-CELL FACT (structural, for the next assembly): the slide
writes exactly two piles — the source pile (revealed, or
emptied bare) and the run's landing pile — and no rung and no
zone cell; the surfaced card is priced S-DEAD at the surfacing
whenever its seat clause fails (the bare-over-hidden shape,
the fb3W datapoint).  The shape to defuse: the run-re-forming
schedule over the two written cells.

CLOSED ALSO (this pass): THE SUCCESSOR'S OWN FORK — when the
successor is itself fork-headed, the empty play exhibits it
(`p_successor_fork_repair`, the decidable census bridge).  The
row's sole carried content is its FORKLESS-SUCCESSOR branch. -/
private theorem p_reveal_rest {s s' F : State} {c : Card} {b : Base}
    {x : Card} {π : List Move}
    (hwf : s.WF)
    (hstep : State.step s (Move.tabToTab c b) = some s')
    (hivr : irreversibleAt s (Move.tabToTab c b))
    (hrun : s.run π = some F)
    (hwit : ForkWitness F x)
    (hprof : π = [] ∨ ∃ m₀ τ, π = m₀ :: τ ∧ m₀ ≠ Move.tabToTab c b) :
    ∃ (F' : State) (π' : List Move) (x' : Card),
      s'.run π' = some F' ∧ ForkWitness F' x' := by
  by_cases hfb : forkStateSB s' = true
  · exact p_successor_fork_repair (step_wf hwf hstep) hfb
  · -- the forkless-successor repair: this row's sole carried content,
    --  with the RUNG HALF of the two-cell fact LANDED THIS PASS
    --  (§5.0c: `p_reveal_rung` — the committed slide writes no
    --  foundation at all, so every `nextUp` read is verbatim across
    --  the commit; and `p_mem_afterRunRemoved` — the source pile's
    --  new face-up record lives in the old two decks); the
    --  PILE-CELL half (two written cells verbatim outside) and the
    --  run-re-forming schedule over them remain this row's content.
    sorry

/-- **`fork_floor_reveal`** — **THE REVEAL KIND RESIDUE** [H, named
residue, exactly one `sorry`]: the committed run relocation
preserves fork-headedness.

ROUTE (the kind read, complete): the move never touches the
foundations or the draw zone (the whole ratchet board is the
tableau), so the climb's index-exactness is untouched — §1's cons
form grades the source pile's reveal (a revealing slide is
irreversible and never rides back, the hidden total strictly
dropping; a bare-burn slide fares the same at
`bare_burn_irreversibleAt`); the consumed fork's package therefore
survives at s' at least to within a defusing-schedule repair of
the ARRANGEMENT alone.  The census prices the cargo legs
cell-for-cell (`census_tabToTab_inr_witness`, with the king-headed
empty-anchor arm `census_tabToTab_inl` census-neutral); the crane
(`excursion_issues_noNewSeat`) bounds the loan flows; the
remaining content is again the defusing-schedule repair time bound
(here: re-scheduling the slide so the mobile run re-forms at a
slab-side member).

HEAD-CASE LANDED (§5.0, this pass): `p_survives_sameHead` — when the
exhibiting play heads with the very slide that committed (π =
Move.tabToTab c b :: τ), the successor is the play's second state
and the tail replays verbatim, distance zero.

ASSEMBLY STRUCTURE (this pass): the kind is now a DISPATCH over
the exhibiting play's head, with the exact-slide head-case CLOSED
and the remainder isolated as its own NAMED SUB-RESIDUE
(`p_reveal_rest` below, per the isolation discipline) — the
empty exhibit, the OTHER-slide heads (same kind, different letter
or different base), and the pull/raise/waste/draw heads fall to
the remainder, whose premise records the excluded head.  The
inventory datum the route name rides is §1's own:
`hidden_never_grows` grades the source pile's reveal — the
surfaced card is EXPANDED INVENTORY (face-up where a hidden deck
was), census-minted at its own cell
(`census_tabToTab_reveal`'s transfer) and priced against the
seat clause immediately (a bare-over-hidden surfacing is S-DEAD
at the surfacing itself, the fb3W datapoint); the loans the
schedule takes on the way are crane-priced
(`excursion_issues_noNewSeat` — a returned excursion issues no
seat the arrangement did not already carry). -/
private theorem fork_floor_reveal {s s' : State} {c : Card} {b : Base}
    (hwf : s.WF)
    (hstep : State.step s (Move.tabToTab c b) = some s')
    (hivr : irreversibleAt s (Move.tabToTab c b))
    (hhed : ∃ (F : State) (π : List Move) (x : Card),
        s.run π = some F ∧ ForkWitness F x) :
    ∃ (F' : State) (π' : List Move) (x' : Card),
        s'.run π' = some F' ∧ ForkWitness F' x' := by
  obtain ⟨F, π, x, hrun, hwit⟩ := hhed
  cases π with
  | nil => exact p_reveal_rest hwf hstep hivr hrun hwit (Or.inl rfl)
  | cons m₀ τ =>
      cases m₀ with
      | draw =>
          exact p_reveal_rest hwf hstep hivr hrun hwit
            (Or.inr ⟨Move.draw, τ, rfl, fun hcon => absurd hcon (by simp)⟩)
      | tabToTab c₀ b₀ =>
          by_cases hc : c₀ = c
          · by_cases hb : b₀ = b
            · have hcc : c = c₀ := hc.symm
              subst hcc
              have hbb : b = b₀ := hb.symm
              subst hbb
              exact p_survives_sameHead hstep hrun hwit
            · exact p_reveal_rest hwf hstep hivr hrun hwit
                (Or.inr ⟨Move.tabToTab c₀ b₀, τ, rfl, by
                    intro hcon
                    injection hcon with _ hbb
                    exact absurd hbb hb⟩)
          · exact p_reveal_rest hwf hstep hivr hrun hwit
              (Or.inr ⟨Move.tabToTab c₀ b₀, τ, rfl, by
                  intro hcon
                  injection hcon with hcc₂ _
                  exact absurd hcc₂ hc⟩)
      | tabToFound c₀ =>
          exact p_reveal_rest hwf hstep hivr hrun hwit
            (Or.inr ⟨Move.tabToFound c₀, τ, rfl,
              fun hcon => absurd hcon (by simp)⟩)
      | wasteToFound c₀ =>
          exact p_reveal_rest hwf hstep hivr hrun hwit
            (Or.inr ⟨Move.wasteToFound c₀, τ, rfl,
              fun hcon => absurd hcon (by simp)⟩)
      | wasteToTab c₀ b₀ =>
          exact p_reveal_rest hwf hstep hivr hrun hwit
            (Or.inr ⟨Move.wasteToTab c₀ b₀, τ, rfl,
              fun hcon => absurd hcon (by simp)⟩)
      | foundToTab c₀ b₀ =>
          exact p_reveal_rest hwf hstep hivr hrun hwit
            (Or.inr ⟨Move.foundToTab c₀ b₀, τ, rfl,
              fun hcon => absurd hcon (by simp)⟩)

/-- **`fork_floor_of_commit`** — **THE FORK-FLOOR CONJECTURE** (the
program owner's statement, byte-frozen): if some fork `F` is
reachable from `s`, some fork remains reachable from `s ⊕ m` for
every irreversible move at `s` — fork-headedness is downward-closed
under the commit DAG.  The vertical companion of
`Orig.LowSlab`'s neighbor form.

ROUTE (the complete four-kind split; the head itself is a pure
dispatch):

* THE FOUR-KIND TAXONOMY (theorem-grade in-tree, applied here): a
  committed move at a WF state is one of — raise-like
  (`.tabToFound`), reveal (`.tabToTab`), waste-jump
  (`.wasteToFound` / `.wasteToTab`), draw-at-nonempty-stock
  (`.draw`).  The fifth constructor (`.foundToTab`) never commits
  at WF (`lowslab_pull_never_commit_wf`), which is exactly where
  the statement's `hwf` hypothesis is load-bearing.
* PER KIND, APPLY THE KIND SUB-ROWS (§§1–4): no kind destroys
  content availability — the hidden decks only shrink (§1), the
  two-zone exits and foundings land in playable zones with the
  pull-back letter's guard-fetch intact (§2), the founded card
  returns the moment a fitting seat exists (§3), the draw
  permutes the cycle without touching the ratchet board (§4).
  Hence the consumed fork's own package (pair mobility, cover
  mobility, low-card raisability per the index-exact climb)
  survives at `s'` at least to within a defusing-schedule repair
  — the repair is exactly the crane's loan-and-repay
  (`excursion_issues_noNewSeat`, `Orig/HostCensus.lean`: no
  hosting capacity is issued a returned excursion does not
  reclaim, per-cell, `roundtrip_census_repay`), and the remaining
  content is the defusing-schedule repair time bound — a strictly
  decreasing schedule measure from `s'` to a fresh fork witness.
  Each kind's named residue above is now a DISPATCH ASSEMBLY
  over its own named remainder row; the CLOSED fraction of every
  route — the SAME-HEAD repair (`p_survives_sameHead`, every
  kind), the CORRIDOR (the waste-eat's sibling-letter shape,
  `p_waste_eat_corridor`), the MIRROR (the waste-seating's
  founding-letter shape, `p_waste_seat_mirror`), and the
  BOARD-ONLY EXHIBIT (the draw kind's `p_draw_board_repair` over
  the certificate rod `p_fork_boardTransfer`) — is proved
  in-file, so each kind's named remainder row
  (`p_draw_zone_rest`, `p_waste_found_rest`, `p_waste_seat_rest`,
  `p_raise_rest`, `p_reveal_rest`) carries exactly the non-head,
  non-closed-shape defusing schedule alone.
* THE FALSIFICATION TARGET (documented for round-3 probes — no
  boards added anywhere): single-family-fragile economies —
  exactly one viable frontier pair, everything else entombed —
  with the commit eating the sole pair member while its takeback
  seat is permanently seat-less (`founded_late_seat_exists`'s
  negation).  If that shape is real, the honest repair weakens
  the statement to "fork-headed OR the irrevocable-eaten-seal
  condition", documented alongside like the `pullEscape`
  precedent — the weakening, if forced, belongs to the statement
  owner, not this leaf.
* THE ALTERNATIVE REDUCTION (route note, prose only —
  `Orig/ForkAscent.lean`'s rows are still residues and are NOT
  imported): floor-by-ascent — run the greedy stacking script
  from `s'` (the full-time no-eat guard, ascent slides and
  raises only, exhaustion as the only end) and read its
  exhaustion row `ascent_exhaustion_forks` with the §1 assembly
  `orientation_assembly_fork`: from a below-frontier start whose
  pair members are mobile, EVERY exhausted ascent run delivers
  the double-hot pair with a fitting cover — one slide from the
  full fork parcel.  A dispatch on this reduction consumes the
  four kind sub-rows to produce `ascent_exhaustion_forks`'s
  `hbelow` premise at `s'` and concludes; the exhaustion row's
  own sorryAx is deliberately not made to flow here.

GRADE: [H] overall; the five per-kind children are sorry-free
ASSEMBLIES, each routing exactly one `sorry` through its own
named remainder row, with a complete route; the head adds none
(audit below).  Statement VERBATIM from the mission; byte-frozen. -/
theorem fork_floor_of_commit {s s' : State} {m : Move}
    (hwf : s.WF)
    (hstep : State.step s m = some s')
    (hivr : irreversibleAt s m)
    (hhed : ∃ (F : State) (π : List Move) (x : Card),
        s.run π = some F ∧ ForkWitness F x) :
    ∃ (F' : State) (π' : List Move) (x' : Card),
        s'.run π' = some F' ∧ ForkWitness F' x' := by
  cases m with
  | draw => exact fork_floor_draw hwf hstep hivr hhed
  | wasteToFound c => exact fork_floor_waste_found hwf hstep hivr hhed
  | wasteToTab c b => exact fork_floor_waste_seat hwf hstep hivr hhed
  | tabToFound c => exact fork_floor_raise hwf hstep hivr hhed
  | foundToTab c b =>
      exact absurd hivr (lowslab_pull_never_commit_wf hwf hstep)
  | tabToTab c b => exact fork_floor_reveal hwf hstep hivr hhed

/-! ## The audit battery

`#print axioms` per fresh head.  Expected: the four kind-census
rows (§§1–4) banked-clean — `[propext]`-grade or
`[propext, Quot.sound]`-grade through the banked step-inversion
chain, zero `sorryAx`, zero `Classical.choice`; the seat-delay
residue `founded_late_seat_exists` is a THREE-DEEP ASSEMBLY —
the proved dichotomy `p_committed_raise_shape` (§3), the proved
immediate-seat arm (`p_seatOffered` + `p_seatOffered_iff` behind
`p_founded_seat_schedule`'s dispatch: any base accepting the
card closes the schedule at the EMPTY play), and the NAMED SUB-ROW
`p_seat_climb_rest` (the expose-and-seat climb, the row's exact
remaining content and its sole `sorryAx` carrier) — and reads
`[propext, sorryAx, Quot.sound]`; the five §5 per-kind residues
are now DISPATCH ASSEMBLIES over their own named remainder rows
(`p_draw_zone_rest`, `p_waste_found_rest`, `p_waste_seat_rest`,
`p_raise_rest`, `p_reveal_rest`), each remainder carrying
exactly the one `sorryAx` of its kind over the banked chain; the
main row `fork_floor_of_commit` is a pure dispatch and must read
exactly `[propext, sorryAx, Quot.sound]` — its `sorryAx` flowing
only through the five named children and their named sub-rows
(the seat-delay row and its schedule are NOT consumed by the
head), `propext`/`Quot.sound` only through the banked clean
chains, no `Classical.choice` anywhere.

THIS PASS added fresh PROVED heads, audited below — the repair
kit of §5.0 and the shape row of §3 from the prior pass
(kernel-observed: `p_pileOfTop_congr` reads NO axioms at all;
`p_canPlace_congr`, `p_putCard_piles_congr` and
`p_survives_sameHead` read `[propext]`; `p_committed_raise_shape`
and `p_waste_eat_corridor` read `[propext, Quot.sound]` through
the step-inversion/undo chain), plus the BOARD-THREAD KIT, the
CLOSED FRAGMENTS, and THE SUCCESSOR'S-OWN-FORK BRANCH of this
pass — the run-lift `p_run_wf`, the license congruences
`p_canRaise_congr` / `p_canRaiseS_congr`, the certificate rod
`p_fork_boardTransfer`, the draw kind's `p_draw_board_repair`,
the seating kind's `p_waste_seat_mirror`, the board-letter scan
`p_boardMoveB` with its two rows, the crown's seat scan
`p_seatOffered` with `p_seatOffered_iff`, and the decidable
census exhibit `p_successor_fork_repair` (over `forkStateSB`
of the newly imported one-import leaf `Orig.ForkStateSB`, zero
`Classical` and zero own-`sorryAx` by its own battery; consumed
only through the bridge `forkStateSB_true_iff` and
`forkWitnessSB_sound`) — every one zero-`sorryAx`,
zero-`Classical.choice` — plus SIX NAMED REMAINDER ROWS
(`p_seat_climb_rest` under the schedule assembly, and the five
per-kind rows under the five children), each exactly one
`sorryAx` with a complete route, each now carrying its kind's
FORKLESS-SUCCESSOR branch alone (the successor's-own-fork case
closed inside each row); the sorry COUNT stays exactly the SIX,
and `fork_floor_of_commit`'s profile is unchanged.

THE SUCCESSION PASS added the §5.0c ONE-COMMIT CENSUS heads, every
one zero-`sorryAx` and zero-`Classical.choice`, audited below —
the search/read transport helpers (`p_census_vec` over
`Twin.firstWhere_congr`; `p_census_none`, the none-completeness
half), the OFF-RUNG license congruence `p_license_offRung` (the
flat `canRaiseS_iff` package transported clause by clause across
states agreeing on piles and every found row but one suit), the
seal's write record `p_seal_zone_rows`, the two seating write
records (`p_seat_inl_records`, `p_seat_inr_records`), the seated
cell's license read `p_seat_gain`, the GUARD-REFUSAL TRANSPORT
`p_seat_refusal_cover` (after the seat covers its host top, every
card-hosted placement consult on that host refuses — the probe
program's junk-refusal verdicts at theorem grade), the seating
read censuses (`p_seat_reads_inl`, `p_seat_reads_inr` — rungs,
piles, and top-searches verbatim off the named cells), the
reveal-membership kit `p_mem_afterRunRemoved` (template:
`Orig/TwinExchangeBoth.lean`'s private copy, per-file per
discipline), the reveal census's RUNG HALF `p_reveal_rung`, and
the BOARD-PREFIX SPLIT `p_board_prefix_split` — AND restructured
the draw kind's named remainder into its NARROW residue: the
BOARD-PASSAGE EXHIBITS are now closed verbatim inside
`p_draw_zone_rest` (the play's board-letter prefix re-runs from
the draw successor along the boardEq thread, and when the
mirror landing is fork-headed the prefix itself exhibits the
successor's fork), so the row's sole remaining `sorryAx` carries
exactly the CURSOR BIRTH — the load-bearing first zone leg,
firing from the commit-shifted cycle at the boardEq twin of a
forkless mirror.  The sorry COUNT stays exactly the SIX; the
draw child's and the head's axiom profiles are UNCHANGED by the
restructure (`p_draw_zone_rest` still
`[propext, sorryAx, Quot.sound]`, one `sorryAx`, whole and
entire the cursor birth).

THE INTERLOPER PASS adds the waste-founding kind's empty-exhibit
census — **`p_sealHotScan_iff`** + **`p_seal_interloper_forced`**
[M, PROVED zero-`sorryAx`, zero-`Classical.choice`]: the interloper
question is DECIDED constructively as a `Bool` scan over the
52-card universe (`p_sealHotScan` over `canRaiseSB`, the S-shadow —
the `p_seatOffered` pattern, no `by_contra`/`Classical` anywhere in
the house), and at a forkless wasteToFound-successor of an origin
fork a hot sealed-suit interloper (rung exactly one above the
sealed card's) is forced into S-liveness — the origin pair reads no
sealed-suit card (`mem_faceUp_only` against the eaten waste head),
the license world off the sealed suit is verbatim (`p_license_offRung`
over `p_seal_zone_rows`), and interloper-freeness would re-certify
the origin's own parcel at the EMPTY play against
`forkStateSB_true_iff`.  The waste-founding remainder's
empty-exhibit arm now carries the interloper as its schedule's
input datum at its token; the row's `sorryAx` profile is unchanged
(one carrier, the row itself); the sorry count stays exactly the SIX
carrying rows.

THE INTERFERENCE PASS adds the waste-seating kind's empty-exhibit
census — **`p_seat_inl_hot_forced`** and its base-uniform wrapper
**`p_seat_interference_forced`** [M, PROVED zero-`sorryAx`,
zero-`Classical.choice`]: at a forkless wasteToTab-successor of an
origin fork, the seating kind's interference is forced into the
named disjunction — at the EMPTY-ANCHOR economy a c-family HOT
read (the seated king's own rung, or its twin's — the seat writes
no rung, the written pile was empty before and is the king's bare
singleton after, the origin pair holds no c-family card by the
waste residency and the pair closure, RANKS VERBATIM via
`p_seat_reads_inl`, searches verbatim off the born cell), or the
seat was a CARD-HOST arm — the covered-host economy whose corners
(the covered top's death, the twin-cover corners, the exceptions of
`p_seat_reads_inr`) remain the seating kind's own open geometry,
priced at the fb2E probe verdicts.  The seating remainder's
empty-exhibit arm carries the disjunction as its input datum at the
token; the row's `sorryAx` profile is unchanged; the sorry count
stays exactly the SIX carrying rows.

THE DRAW-CUT PASS restructures the draw kind's named remainder at
the first zone leg's KIND — **`p_draw_zone_det`** + **`p_run_join`**
[E, PROVED zero-`sorryAx`, zero-`Classical.choice`: the drawn zone is
a ZONE FUNCTION (two states agreeing on stock/waste/drawStep whose
draws both fire land agreeing zones; the per-file copy of
HostCensus's private `draw_zone_det` over Phase's public
`plain_draw_shape` / `base_draw_shape`, with the run-splice copy
`p_run_join` of Macro's public `run_split`)], and with it the CURSOR
BIRTH's DRAW leg closes verbatim inside `p_draw_zone_rest`: the
board prefix wrote no zone cell, so the play's inner draw reads the
commit's own zone triple and lands EXACTLY the mirror state the
successor thread already sits at — the remaining tail replays
verbatim, the same fork, one leg sooner — so `p_draw_zone_rest` is
now a sorry-free THREE-ARM dispatch (successor-fork / mirror-fork /
first zone leg by kind), and the cursor birth's WASTE leg is
isolated as its own named narrow sub-residue **`p_draw_zone_shift`**
[H, one `sorryAx`, complete route] — the waste-head shift, the
honest danger the `Orig/EdgeLabel.lean` banked successor share
explicitly does not cover (the waste/tab share is open there).  The
carrying row set is again exactly the SIX (`p_seat_climb_rest`,
`p_draw_zone_shift`, `p_waste_found_rest`, `p_waste_seat_rest`,
`p_raise_rest`, `p_reveal_rest`); the draw child's and the head's
axiom profiles are unchanged by the restructure.

THE SHADOW-SPINE PASS restructures the waste-founding kind's named
remainder over the seal's head-replay spine — the leg class
`p_shadowLeg` with its prefix split `p_shadow_prefix_split`, the
per-letter step mirrors (`p_step_tabToTab_succ`, `p_setPile_piles_aux`,
`p_putRun_piles_congr`, `p_shadow_step`) and their run composition
`p_shadow_run`, the vanilla license mirror `p_canRaise_offRung`, and
the off-rung certificate transfer `p_fork_offRung_transfer` — every
one zero-`sorryAx`, zero-`Classical.choice`, audited below.  The
forkless branch of `p_waste_found_rest` now prices its residue to
two tokens: the all-clean economy's SCAN-FREE case is CLOSED (the
heat scan `p_sealHotScan` reads false, the witness pair's rung pins
prove the pair names no sealed-suit card — a sealed-suit member's
rung would pin it to the eaten waste head itself, which the WF
census bars from liveness — and the whole certificate transfers
along the off-rung license world, the exhibit the clean prefix
itself played from the successor), while the scan-hot case carries
the interloper as the climb's input datum, and the first-consult
exhibit carries the repair-time schedule across the consult leg
(the raised-row shadow, the cursor read over the popped head).  The
seat-delay climb `p_seat_climb_rest` stays parked as the crown's
named sub-row over the proved dichotomy `p_committed_raise_shape`
(the repair-time bound is its sole content, the probe program's
honest danger); the three outer arms (`p_waste_seat_rest`,
`p_raise_rest`, `p_reveal_rest`) collapse to their own honest stakes
as declared — the seating kind's covered-host geometry, the
raised-row-plus-emptied-pile shadow, and the run-formed reveal —
each one `sorryAx`, the main dispatch untouched and pure.  The
carrying row set stays exactly the SIX; the head's axiom profile
is unchanged.

THE STAGING PASS lands the seat-delay row's route steps 1-2 as
theorem-grade kit (the §0-kernel block above the climb):
**`p_card_of_suit_toIdx`** (the frontier-cell uniqueness: same
suit and same rank index name one card), **`p_king_inl_refusal`**
(a non-king's empty-seat consult refuses at every state),
**`p_climb_accept_shape`** (every acceptance is the empty-seat
vacate or the pinned card-host cell), **`p_seat_refused_census`**
(no consult accepts at the guard-refused successor, no empty seat
at a king, no fitting host topping anywhere), and
**`p_climb_reveal_surface`** (the reveal arm's surfaced head
topping the raised pile as a bare singleton) — every one zero-
`sorryAx`, zero-`Classical.choice`, audited below — AND the
seating kind's empty-exhibit ROTATION: **`p_seat_inl_seal_rotate`**
(the one-leg raise at the hot seated king lands the direct seal's
successor EXACTLY; PROVED, zero-`sorryAx`) with its assembly
**`p_seat_inl_rotation_fork`** (the empty-anchor hot-king
sub-case routes into the waste-founding kind's own residue; a
sorry-free assembly whose `sorryAx` flows only from the consumed
sibling `p_waste_found_rest`).  The `sorry` TOKENS stay exactly
the EIGHT (the direct-sorry keywords: one each in
`p_seat_climb_rest`, `p_draw_zone_shift`, `p_raise_rest`,
`p_reveal_rest`, two each in `p_waste_found_rest` and
`p_waste_seat_rest`) and the declaration-level warnings exactly
the SIX: `p_waste_seat_rest`'s empty-exhibit arm is NARROWED (its
hot-king sub-case closed via the rotation) but keeps its token for
the COLD-king and CARD-HOST corners; the head's axiom profile is
unchanged. -/

#print axioms hidden_never_grows
#print axioms two_zone_exits_playable
#print axioms founded_returnable_via_seats
#print axioms founded_late_seat_exists
#print axioms draws_permute_only
#print axioms p_pileOfTop_congr
#print axioms p_canPlace_congr
#print axioms p_putCard_piles_congr
#print axioms p_survives_sameHead
#print axioms p_waste_eat_corridor
#print axioms p_committed_raise_shape
#print axioms p_run_wf
#print axioms p_canRaise_congr
#print axioms p_canRaiseS_congr
#print axioms p_fork_boardTransfer
#print axioms p_draw_board_repair
#print axioms p_waste_seat_mirror
#print axioms p_seatOffered_iff
#print axioms p_successor_fork_repair
#print axioms p_census_vec
#print axioms p_census_none
#print axioms p_license_offRung
#print axioms p_shadow_prefix_split
#print axioms p_setPile_piles_aux
#print axioms p_step_tabToTab_succ
#print axioms p_putRun_piles_congr
#print axioms p_shadow_step
#print axioms p_shadow_run
#print axioms p_canRaise_offRung
#print axioms p_fork_offRung_transfer
#print axioms p_seal_zone_rows
#print axioms p_seat_inl_records
#print axioms p_seat_inr_records
#print axioms p_seat_gain
#print axioms p_seat_refusal_cover
#print axioms p_seat_reads_inl
#print axioms p_seat_reads_inr
#print axioms p_mem_afterRunRemoved
#print axioms p_reveal_rung
#print axioms p_board_prefix_split
#print axioms p_run_join
#print axioms p_draw_zone_det
#print axioms p_sealHotScan_iff
#print axioms p_seal_interloper_forced
#print axioms p_seat_inl_hot_forced
#print axioms p_seat_interference_forced
#print axioms p_card_of_suit_toIdx
#print axioms p_king_inl_refusal
#print axioms p_climb_accept_shape
#print axioms p_seat_refused_census
#print axioms p_climb_reveal_surface
#print axioms p_seat_climb_rest
#print axioms p_founded_seat_schedule
#print axioms p_draw_zone_shift
#print axioms p_draw_zone_rest
#print axioms p_waste_found_rest
#print axioms p_waste_seat_rest
#print axioms p_raise_rest
#print axioms p_reveal_rest
#print axioms fork_floor_draw
#print axioms fork_floor_waste_found
#print axioms p_seat_inl_seal_rotate
#print axioms p_seat_inl_rotation_fork
#print axioms fork_floor_waste_seat
#print axioms fork_floor_raise
#print axioms fork_floor_reveal
#print axioms fork_floor_of_commit
