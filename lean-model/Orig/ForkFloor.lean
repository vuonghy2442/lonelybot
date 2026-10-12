import Orig.LowSlab
import Orig.Phase

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
  content, priced for round-3 probes).
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
draw tables; everything else consumed is transitive: `ForkWitness`
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
   does NOT copy them.
3. THE SCHEDULE [THE OPEN STEP]: composing 1–2 across the commit
   DAG — the letters' census budgets at the reachable states can
   only be spent down along irreversible letters, so a fitting
   seat either is issued directly by play, or the entombment
   certificate (no seat anywhere below) is itself the
   falsification witness.  THIS composition is the open content,
   not any census row.

PROBE PRICING (round-3; boards NOT added here, per the mission):
the falsification target is exactly this row's negation — see the
§5 main row's FALSIFICATION TARGET paragraph (single-family-fragile
economies, the sole pair member eaten, the takeback seat
permanently seat-less).  If that shape is real, THIS row is the
honest casualty and the main row's repair disjunct documents it
alongside. -/
theorem founded_late_seat_exists {s s' : State} {c : Card}
    (hwf : s.WF)
    (hstep : State.step s (Move.tabToFound c) = some s')
    (hivr : irreversibleAt s (Move.tabToFound c)) :
    ∃ (ρ : List Move) (t : State) (b : Base),
      s'.run ρ = some t ∧ t.canPlace c b = true := by
  sorry

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
   cycle's irreversibility, not the schedule). -/
private theorem fork_floor_draw {s s' : State}
    (hwf : s.WF)
    (hstep : State.step s Move.draw = some s')
    (hivr : irreversibleAt s Move.draw)
    (hhed : ∃ (F : State) (π : List Move) (x : Card),
        s.run π = some F ∧ ForkWitness F x) :
    ∃ (F' : State) (π' : List Move) (x' : Card),
        s'.run π' = some F' ∧ ForkWitness F' x' := by
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
   fresh fork. -/
private theorem fork_floor_waste_found {s s' : State} {c : Card}
    (hwf : s.WF)
    (hstep : State.step s (Move.wasteToFound c) = some s')
    (hivr : irreversibleAt s (Move.wasteToFound c))
    (hhed : ∃ (F : State) (π : List Move) (x : Card),
        s.run π = some F ∧ ForkWitness F x) :
    ∃ (F' : State) (π' : List Move) (x' : Card),
        s'.run π' = some F' ∧ ForkWitness F' x' := by
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
remaining content (the cursor read / repair time bound). -/
private theorem fork_floor_waste_seat {s s' : State} {c : Card} {b : Base}
    (hwf : s.WF)
    (hstep : State.step s (Move.wasteToTab c b) = some s')
    (hivr : irreversibleAt s (Move.wasteToTab c b))
    (hhed : ∃ (F : State) (π : List Move) (x : Card),
        s.run π = some F ∧ ForkWitness F x) :
    ∃ (F' : State) (π' : List Move) (x' : Card),
        s'.run π' = some F' ∧ ForkWitness F' x' := by
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
   route, not re-priced here. -/
private theorem fork_floor_raise {s s' : State} {c : Card}
    (hwf : s.WF)
    (hstep : State.step s (Move.tabToFound c) = some s')
    (hivr : irreversibleAt s (Move.tabToFound c))
    (hhed : ∃ (F : State) (π : List Move) (x : Card),
        s.run π = some F ∧ ForkWitness F x) :
    ∃ (F' : State) (π' : List Move) (x' : Card),
        s'.run π' = some F' ∧ ForkWitness F' x' := by
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
slab-side member). -/
private theorem fork_floor_reveal {s s' : State} {c : Card} {b : Base}
    (hwf : s.WF)
    (hstep : State.step s (Move.tabToTab c b) = some s')
    (hivr : irreversibleAt s (Move.tabToTab c b))
    (hhed : ∃ (F : State) (π : List Move) (x : Card),
        s.run π = some F ∧ ForkWitness F x) :
    ∃ (F' : State) (π' : List Move) (x' : Card),
        s'.run π' = some F' ∧ ForkWitness F' x' := by
  sorry

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
  Each kind's named residue above carries its own route.
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

GRADE: [H] overall; the five per-kind children each carry exactly
one `sorry` with a complete route; the head adds none (audit
below).  Statement VERBATIM from the mission; byte-frozen. -/
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
residue `founded_late_seat_exists` carries its own one `sorryAx`;
the five §5 per-kind residues each carry exactly their one
`sorryAx` over the banked chain; the main row
`fork_floor_of_commit` is a pure dispatch and must read exactly
`[propext, sorryAx, Quot.sound]` — its `sorryAx` flowing only
through the five named children, `propext`/`Quot.sound` only
through the banked clean chain (`lowslab_pull_never_commit_wf`'s
side), no `Classical.choice` anywhere. -/

#print axioms hidden_never_grows
#print axioms two_zone_exits_playable
#print axioms founded_returnable_via_seats
#print axioms founded_late_seat_exists
#print axioms draws_permute_only
#print axioms fork_floor_draw
#print axioms fork_floor_waste_found
#print axioms fork_floor_waste_seat
#print axioms fork_floor_raise
#print axioms fork_floor_reveal
#print axioms fork_floor_of_commit
