import Klondike.Theorems

/-!
# The closure-goal kills (the K-rules — the engine's `goal_dead`)

Cheap necessary conditions for an accommodation goal to open *anywhere*
in the reversible closure (the engine's macro-game BFS — see the
`ClosureCtx` doc in `src/macro_game.rs`, whose K1/K2/K4/K5/K6 rules the
search applies before walking).  A killed goal provably has no BFS
answer, so skipping it is pure search cost; the rules are stated here
as *closure invariants* over `safeAccommodates` (Theorems.lean).

Everything rides on one keystone, `vis_of_safeAccommodates`: shuffles
never deal, never reveal, and never stack a locked card, so a card
visible in the closure was root-visible or worried back from the root
foundation.  K4 (first-layer kings) and K5 (the saturated-board gate)
are not yet statable — the model has no first-layer predicate and no
path state; see FARM.md's wave-12 notes.

Refute-first gate for the sorried rows: the Rust differential probe
(`macro_direct_matches_oracle` — a wrong kill counts as a missing
outcome) is the falsification instrument; there is no Lean-side
executable closure walk, do **not** hand-probe these with `#eval`.
-/

/-- **The closure's visibility bound** (the K-rules' shared premise):
inside the safe accommodation closure, every visible card was
root-visible or sits below its suit's root foundation height (a
worry-back from the root foundation).  Deck and buried cards never
enter `vis`.

TODO(proof) [M]: induction on the play.  Carry the conjunction with
its foundation-side shadow: *a card on the foundation in the closure
was on the root foundation or was root-visible* (the foundation grows
only by `pileStack` of a visible card).  `pileStack` — the visible
image only loses the stacked card; `stackPile` — `x` enters the image
from the firing state's foundation, the shadow bounds it.  No WF
hypothesis believed needed; add `hwf` (and record the repair) only if
the shadow's induction needs `founds_gone`. -/
theorem vis_of_safeAccommodates {st st' : State} (h : safeAccommodates st st')
    (c : Card) (hvis : st'.isVis c = true) :
    st.isVis c = true ∨ c.rank.toIdx < st.heights c.suit := sorry

/-- The frontier's witness spec: below 13 the frontier is a real
missing rank — at or above the height, not visible-and-unlocked, with
every prefix rank below it visible and unlocked.

TODO(proof) [M]: `List.find?_eq_some_iff`-family fishing over the
filtered `Rank.all`; the minimality (last conjunct) needs the filter's
`toIdx`-monotonicity — `Rank.all` is `toIdx`-sorted (`decide`-checkable
as a list fact, then a `find?`-prefix argument). -/
theorem State.frontier_spec (st : State) (s : Suit) (hlt : st.frontier s < 13) :
    ∃ r : Rank, st.frontier s = r.toIdx ∧ st.heights s ≤ r.toIdx ∧
      (st.isVis ⟨s, r⟩ = false ∨ st.isLocked ⟨s, r⟩ = true) ∧
      ∀ r' : Rank, st.heights s ≤ r'.toIdx → r'.toIdx < r.toIdx →
        st.isVis ⟨s, r'⟩ = true ∧ st.isLocked ⟨s, r'⟩ = false := sorry

/-- **K1 (the climb kill, `goal_dead`'s Stack arm)**: with the suit's
frontier below the target rank, the suit never climbs to `X` anywhere
in the closure — i.e. `X` is never stacked.  (The climb from `h₀` to
`rank X` stacks each prefix card; the frontier card can never fire:
not root-visible by `frontier_spec` — worry-backs surface only ranks
below the root height — or locked — excluded by `playSafeAccomm`.)

TODO(proof) [M]: the climb lemma is the sub-item — induction on the
accommodation play: `heights s` grows only via `pileStack` of exactly
the next prefix card, so `st'.heights s > X.rank.toIdx` stack-fires
every rank of `[h₀, X.rank)`; restate as "heights rose above `k` ⟹
rank `k` was `pileStack`-fired".  Then: the frontier card's firing
state has it visible (`bottomOf` some), `vis_of_safeAccommodates`
forces root-visible (its rank `≥ h₀` kills the second disjunct — it
is `st.heights`-bounded by `frontier_spec`'s first conjunct), and
`playSafeAccomm` forces unlocked — contradicting `frontier_spec`'s
second conjunct. -/
theorem K1_stack_goal_dead {st : State} {X : Card}
    (hfront : st.frontier X.suit < X.rank.toIdx) :
    ∀ st' : State, safeAccommodates st st' → st'.heights X.suit ≤ X.rank.toIdx := sorry

/-- **K2 (the receiver kill, `goal_dead`'s Tableau arm for
non-kings)**: if neither receiver can ever surface in the closure
(not root-visible, and ranked at-or-above its suit's root height so
no worry-back can surface it — the keystone's second disjunct), `X`
has no legal tableau placement anywhere in the closure.

PROOF LANDED 2026-10-05 (the wave-12 K2 farm session; the row's own
`sorry` marker is discharged — but the proof is
keystone-tainted until `vis_of_safeAccommodates` lands:
`#print axioms` carries `sorryAx` through it): the staged route —
`canPlace X b = true` case-splits on `b`: the anchor arm
(`canPlace_inl_iff`) needs a king, killed by `hking`; the tableau arm
is `d` visible (`isVis_of_canPlace_inr`) with `X` fitting
(`canSitOn_of_canPlace_inr`), `Card.mem_receivers_iff` puts `d` in
the receiver set, and the keystone `vis_of_safeAccommodates`
contradicts `hrecv d` both ways (root-visible contra the first
conjunct; the worry-back range `rank < h₀` contra the second, which
bounds the receiver out of it by the root heights — the engine's
`dead` test `!root.vis ∧ !root-stacked`).  This is the §8.5
visibility door: the engine-side reading is the receiver *pair*
(`or_vis` on it, §8.1's first conjunct — `Card.orVis_of_movableOf`,
Klondike/Movability.lean); the model's `canPlace` reads the pair's
visible members directly, and both receivers being dead pins the
pair invisible at every closure word.

Kings are excluded (the empty-pile gate — K5's jurisdiction, not
K2's): the anchor arm is the *only* king opening, and it has no
receiver to kill. -/
theorem K2_tableau_goal_dead {st : State} {X : Card} (hking : X.rank ≠ Rank.king)
    (hrecv : ∀ r, r ∈ X.receivers →
      st.isVis r = false ∧ st.heights r.suit ≤ r.rank.toIdx) :
    ∀ st' : State, safeAccommodates st st' → ∀ b : Base, st'.canPlace X b = false := by
  intro st' hacc b
  rcases Bool.eq_false_or_eq_true (st'.canPlace X b) with h | h
  · exfalso
    cases b with
    | inl a => exact hking (king_of_canPlace_inl h)
    | inr d =>
        obtain ⟨-, hvis', hcs⟩ := canPlace_inr_iff.mp h
        obtain ⟨hvis0, hrk⟩ := hrecv d ((Card.mem_receivers_iff X d).mpr hcs)
        rcases vis_of_safeAccommodates hacc d hvis' with h1 | h2
        · rw [h1] at hvis0
          simp at hvis0
        · omega
  · exact h
