import Orig.PairName
import Orig.BracketDecomp

/-!
# Orig.LowSlab — THE LOW-SLAB SUFFICIENCY (the fork's exploration budget)

The fork's NEIGHBORHOOD is visible entirely from its LOW SLAB: every
COMMITMENT out of a fork's macro class — every `irreversibleAt` move,
the program's own commit grain (the selector `win_iff_macro`'s
decomposition commits by) — is matched by a LOW DUPLICATE: a
commitment from a class member whose family foundations sit at or
below the fork point, into the same target class.  The exploration
consequence: a solver or counter program walking the macro lattice
from a fork never has to inhabit states above the fork point to see
which classes are reachable — the ≤ frontier members enumerate the
full adjacency.

* §1 `familyBelowFrontier` — the slab: the two family suits' rungs
  sit at or below the witness's rank index (the pair is not founded).
* §2 `fork_self_low` (proved, zero-sorry) — the fork state itself
  sits on its own slab: both family rungs read EXACTLY the fork
  index (`canRaiseS_rung` on each live member).
* §3 The commit-grade support rows (all proved, zero-sorry):
  `p_run_append` (the run-append compose), `commit_exits_class`
  (a semantic commit exits the setoid class), and
  `commit_blocks_class_return` (a slab duplicate's irreversibility
  is free — any class-matched return composes into a forbidden
  return against the original commitment).
* §4 `fork_neighbor_lowbridge` — THE LOW-SLAB SUFFICIENCY, the named
  residue: the routing content only; the commit grades of the
  duplicate are banked in §3.  Route in its docstring; refuter-first
  per the house discipline.

GRADE NOTE (the design decision): the theorem is stated at the
PROGRAM'S OWN commit grain — `irreversibleAt`, the full no-return
notion of `Orig/Fate.lean` (plays of any grain) — not at the softer
setoid-exit grade `¬ sameOrbitSetoid.r`; the bridge row of §3 shows
the semantic grade implies the setoid exit, so the statement carries
the stronger, more useful hypothesis while remaining comparable with
the class algebra.  A soft exit (a move that leaves the class but
keeps a non-witness return somewhere) is deliberately not the
explorer's primitive.

House compliance: additive leaf (`import Orig.BracketDecomp`, the
`sameOrbit_forward` grade); the fresh def is statement-facing; the
named residue carries its complete route; every fresh head audited.
-/

/-! ## §1. The slab -/

/-- **THE LOW SLAB** — the state's family foundations sit at or below
the fork point: neither pair member of `x`'s family has been founded
(no family suit's rung has walked past the witness's rank index). -/
def familyBelowFrontier (w : State) (x : Card) : Prop :=
  rungAt w x.suit ≤ x.rank.toIdx ∧ rungAt w x.twin.suit ≤ x.rank.toIdx

/-! ## §2. The fork sits on its own slab -/

/-- **THE SELF-SLAB ROW** — a fork state is a member of its own low
slab: both live members force their suits' rungs EXACTLY to the fork
index (`canRaiseS_rung` on each member of the saturated pair), so the
slab is never vacuous — the statement of §4 always has at least the
fork itself among its candidate manifestations. -/
theorem fork_self_low {st : State} {x : Card} (hx : ForkWitness st x) :
    familyBelowFrontier st x := by
  unfold familyBelowFrontier
  constructor
  · exact Nat.le_of_eq (canRaiseS_rung ((hx.1 x).mp (Or.inl rfl)))
  · have h2 := canRaiseS_rung ((hx.1 x.twin).mp (Or.inr rfl))
    rw [Card.twin_rank] at h2
    exact Nat.le_of_eq h2

/-! ## §3. The commit-grade support rows -/

/-- The run-append compose: two successful runs concatenate into one
(the forward-facing companion of `Orig/Play.lean`'s split reader
`run_append_split`; needed here to join the class witness plays into
a single return play). -/
private theorem p_run_append : ∀ (a : State) (A B : List Move) (z w : State),
    a.run A = some z → z.run B = some w → a.run (A ++ B) = some w := by
  intro a A
  induction A generalizing a with
  | nil =>
      intro B z w h1 h2
      have hz : some a = some z := h1
      injection hz with hc
      subst hc
      exact h2
  | cons m rest ih =>
      intro B z w h1 h2
      obtain ⟨a₁, hs, hr⟩ := State.run_cons h1
      have h3 := ih a₁ B z w hr h2
      rw [List.cons_append]
      show (match State.step a m with
        | some st' => st'.run (rest ++ B)
        | none => none) = some w
      rw [hs]
      exact h3

/-- **THE COMMIT-CROSSING BRIDGE** — a semantic commitment exits the
setoid class: the successor of an `irreversibleAt` move is never
class-connected back, since a class connection carries a FORWARD
witness play (`sameOrbit_forward` through the setoid's symmetry)
and therefore, in particular, a legal return play — which the
no-future-read of `irreversibleAt` rules out in full generality
(plays of any grain, committed or not). -/
theorem commit_exits_class {u v : State} {m : Move}
    (hstep : State.step u m = some v)
    (hiv : irreversibleAt u m) :
    ¬ sameOrbitSetoid.r u v := by
  intro hcon
  have hrvu : sameOrbitSetoid.r v u := sameOrbitSetoid.iseqv.symm hcon
  obtain ⟨ρ, hρ⟩ := sameOrbit_forward hrvu
  exact hiv v ρ hstep (ShufflePlayW_run hρ)

/-- **THE SLAB DUPLICATE's IRREVERSIBILITY IS FREE** — whenever the
duplicate target lands in the same class as the original commitment's
successor, and the duplicate's origin rides the original's class,
any return play from the duplicate's successor composes — through
the two class witness plays — into a return play from the original
successor, against the original's `irreversibleAt`.  The row lets the
§4 residue conclude its duplicate's commit-grade without re-arguing
it: the routing only has to produce the class links. -/
theorem commit_blocks_class_return {u v u₀ v₀ : State} {m : Move}
    (hstep : State.step u m = some v)
    (hiv : irreversibleAt u m)
    (hlink : sameOrbitSetoid.r u₀ u)
    (hmatch : sameOrbitSetoid.r v₀ v)
    (hback : ∃ play, State.run v₀ play = some u₀) :
    False := by
  obtain ⟨πback, hrb⟩ := hback
  -- the class joins: v ⇝ v₀ (the match, read backward) and u₀ ⇝ u
  obtain ⟨πv, hv⟩ := sameOrbit_forward (st := v) (w := v₀)
    (sameOrbitSetoid.iseqv.symm hmatch)
  obtain ⟨πu, hu⟩ := sameOrbit_forward (st := u₀) (w := u) hlink
  -- compose the forbidden return: v ⇝ v₀ ⇝ u₀ ⇝ u
  have hmid : v₀.run (πback ++ πu) = some u :=
    p_run_append v₀ πback πu u₀ u hrb (ShufflePlayW_run hu)
  have h1 : v.run (πv ++ (πback ++ πu)) = some u :=
    p_run_append v πv (πback ++ πu) v₀ u (ShufflePlayW_run hv) hmid
  exact hiv v (πv ++ (πback ++ πu)) hstep h1

/-! ## §4. The named residue -/

/-- **THE LOW-SLAB SUFFICIENCY** — the fork's exploration budget: any
COMMITMENT out of a fork's macro class — any `irreversibleAt` move,
the program's own commit grain — is matched by a LOW DUPLICATE: a
commitment from a class member whose family foundations sit at or
below the fork point (`familyBelowFrontier`), into the SAME target
class.  An explorer of the neighboring macro classes therefore only
ever needs to probe the low slab.

Hypotheses read: `st` is the fork (witness `x`, fork point
`x.rank.toIdx`); `u` rides the fork's class and `m` commits there
(`hstep` names the successor `v`; `hiv` the commit — no play of any
grain returns; `commit_exits_class` derives the setoid-class exit for
consumers of that reading).  Conclusion: a slab member `u₀` of the
same class, a move `m₀` from it with successor `v₀`, ITSELF a commit
(`irreversibleAt u₀ m₀` — free by `commit_blocks_class_return` once
the class links are routed), with `v₀` IN THE SAME TARGET CLASS.

This is the NEIGHBOR form of the reach-corridor claim ("to explore
any reachable macro class, states above the fork point never need be
inhabited"): the corridor form follows by recursion over the macro
descent, each frontier class spending its own slab — deferred until
this row lands.

ROUTE (refute-first; each step priced against banked rows or
named-to-land sub-rows):

1. THE EMPTY ARM — if the committing member `u` already sits on the
   slab, `u₀ := u` closes the row (its own `hiv` serving as the
   duplicate's commit grade); ALL the content lives in commitments
   departing from ELEVATED members (some family rung strictly past
   the fork point).
2. THE ELEVATION MECHANISM — how can the fork's class contain an
   elevated member at all?  Only by a REVERSIBLE family lift: the
   raise's takeback staged by the `tabToFound_undo_under`-shaped
   witness (founding the member off a face-up stack leaves the
   below-card as the pull-back base).  The takeback seat needs a
   face-up `(y-family, r+1)`-top — a LONE over its hidden deck
   suffices (lone tops sit without fit), and fork boards may legally
   carry them: so elevation cannot be barred a priori, and the row's
   real fight is not "no elevated members" but "elevated members are
   corridor-transparent".
3. THE CRANE CORRESPONDENCE — replay the elevation's receipts
   downward along the witnessing journey `st ⇝ u`: its takeback
   checklist names seats that are arrangement-cards (face-up and
   above-frontier at the fork) plus whatever `u` exhumed; the census
   brackets (`witness_rung_census` with the LIFO pop law
   `foundToTab_pops_currentTop`) price the exhumable set, and each
   exhumation's own takeback host is again an arrangement-card — so
   the checklist is executable at the slab by the same reversible
   crane, reproducing `u`'s relevant commit availability there.
4. THE COMMIT REPLAY — each commitment at `u` re-routes off the slab
   duplicate: a raise-like commit's departing index sits at most at
   the family frontier on the slab; a reveal commit's stripping path
   re-schedules off the slab's hosts (hidden lists are class
   invariants — `shuffle_hiddenPinned` — so the revealed target is
   the same pile content); a waste commit's feed re-locates likewise
   (the stock/waste zone is class-closed, the
   `witness_stockWaste_closed` pattern, re-derived at this leaf's
   grade per the dedup discipline).  The duplicate lands in the same
   class by the replay's reversibility, and its commit grade is
   `commit_blocks_class_return`'s free read.

REFUTER-FIRST — the `LowSlabProbe` boards (the `CrossFamilyProbe`
harness, one small edit away):  Q(A) do fork boards carrying lone
above-frontier y-tops admit witness round-trips above the frontier
(the elevation of step 2 realizable in-class)?  Q(B) at such
elevated members, is every legal COMMITMENT matched by a
slab-departing commitment into the same target class?  A single Q(B)
counterexample board reshapes the frontier (per-suit relaxation),
the repair documented alongside — the `pullEscape` precedent.

Grading: [H] research-grade; the residue carries this route; the
fresh heads audited below. -/
theorem fork_neighbor_lowbridge {st : State} {x : Card}
    (hx : ForkWitness st x)
    {u v : State} (hmem : sameOrbitSetoid.r st u)
    {m : Move} (hstep : State.step u m = some v)
    (hiv : irreversibleAt u m) :
    ∃ (u₀ : State) (m₀ : Move) (v₀ : State),
      sameOrbitSetoid.r st u₀ ∧
      familyBelowFrontier u₀ x ∧
      State.step u₀ m₀ = some v₀ ∧
      irreversibleAt u₀ m₀ ∧
      sameOrbitSetoid.r v₀ v := by
  sorry

/-! ## The audit battery

`#print axioms` per fresh head: the slab def is statement-facing;
`fork_self_low`, the run-append compose, both commit-grade rows are
zero-sorry and read banked-chain grade; `fork_neighbor_lowbridge`
carries this file's single `sorryAx` and NOTHING else flows into it. -/

#print axioms fork_self_low
#print axioms commit_exits_class
#print axioms commit_blocks_class_return
#print axioms fork_neighbor_lowbridge
