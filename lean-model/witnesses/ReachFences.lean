import Klondike.Restriction
import Witnesses.KingAnchorReachProbe

/-!
# The reachability fences, refit onto the induction combinator

The wave-20 migration pattern proof (Task A's second refit).  The
wave-19B probe fences were initial-plus-run-shaped over the deposit:
`accounted` seeds at the dealt game (`initial_accounted`) and rides
any play (`run_accounted`, a per-fence run-induction).  The new
`invariant_of_initialReachable` (Restriction.lean, wave-20) factors
exactly that induction — so this file re-derives the conservation
fence through the combinator and re-attaches the probe's seat
theorem, proving the pattern carries existing fences verbatim: every
future reachability gate is one `hinit` + one `hstep` pair, and no
fence ever re-proves a run-induction again.

The per-file isolation rule holds: this is a NEW addendum file, the
probe itself is untouched.  The addendum imports the probe (the
facade cross-import precedent, namespace-hygienic) because the
probe's public `accounted`, `apply_accounted` and `initial_accounted`
ARE the per-step and seed lemmas — the migration reuses the probe's
entire step content, changing only the induction driver.
-/

namespace ReachFences

/-- **The conservation fence, refit**: every dealt-reachable state is
`accounted` — each dealt pile card is hidden in its pile, visible on
the matching, or on its foundation — now by the combinator, WF riding
along (`apply_accounted` reads WF at its reveal arm, so the packaged
invariant is `WF ∧ accounted`). -/
theorem accounted_of_initialReachable {st : State}
    (hr : initialReachable st) : KingAnchorReach.accounted st :=
  (invariant_of_initialReachable
    (I := fun st => st.WF ∧ KingAnchorReach.accounted st)
    (fun _ s hdw hs =>
      ⟨initial_wf hdw hs, KingAnchorReach.initial_accounted hdw s⟩)
    (fun _ st' m hap h =>
      ⟨apply_wf h.1 m st' hap, KingAnchorReach.apply_accounted h.1 h.2 hap⟩)
    st hr).2

/-- **The seat theorem, re-derived from the combinator-driven
account** (the probe's `KingAnchorReach.pileCards_seated_of_
initialReachable`, same statement): at a dealt-reachable state with
all depths and all heights zero, every dealt pile card is visible —
the 28 buried cards cannot all vanish, so the matching must show
them. -/
theorem pileCards_seated_of_initialReachable {st : State}
    (hr : initialReachable st)
    (hd : ∀ a, st.depths a = 0) (hh : ∀ s, st.heights s = 0) :
    ∀ a : Anchor, ∀ c : Card, c ∈ st.deal.piles a → st.isVis c = true := by
  intro a c hc
  rcases accounted_of_initialReachable hr a c hc with h | h | h
  · have h' : c ∈ (st.deal.piles a).take (st.depths a) := h
    rw [hd a] at h'
    rw [List.take_zero] at h'
    exact absurd h' (by simp)
  · exact h
  · have h' : decide (c.rank.toIdx < st.heights c.suit) = true := h
    rw [hh c.suit] at h'
    exact absurd (of_decide_eq_true h') (by omega)

/-- The dead-corner reading, combinator form: a dealt-reachable state
cannot have zero depths, zero heights, and an unseated dealt pile
card. -/
theorem unseated_pileCard_unreachable {st : State}
    (hr : initialReachable st)
    (hd : ∀ a, st.depths a = 0) (hh : ∀ s, st.heights s = 0)
    (hex : ∃ a : Anchor, ∃ c : Card,
      c ∈ st.deal.piles a ∧ st.isVis c = false) : False := by
  obtain ⟨a, c, hc, hvis⟩ := hex
  rw [pileCards_seated_of_initialReachable hr hd hh a c hc] at hvis
  exact Bool.noConfusion hvis

end ReachFences

#print axioms ReachFences.accounted_of_initialReachable
#print axioms ReachFences.pileCards_seated_of_initialReachable
#print axioms ReachFences.unseated_pileCard_unreachable
