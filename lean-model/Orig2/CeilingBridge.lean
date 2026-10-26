import Orig2.PairClassSeed

/-!
# Orig2.CeilingBridge — THE FORKLESS-CEILING REDUCTION CARD
(the campaign's first landing, 2026-10-26)

THE MISSION (the owner's forkless-ceiling campaign): in a forkless
macro class, two saturated endpoints share their foundations —

  `sameOrbitSetoid.r s s' → (∀ u, sameOrbitSetoid.r s u →
  ¬forkState u) → SSaturated s → SSaturated s' → s.found = s'.found`

— landed here as THE REDUCTION: the theorem is ONE residue away,
and the residue is named, graded, and routed in the registry
(`SatDifferFork`, `Orig2/Vocab.lean` §5.1).  Everything else the
proof needs is certified below:

* **§1 THE FINISHING KIT** — the rung→found congruence at `WF`
  (the take-prefix discipline: `rungAt_le13`,
  `found_congr_of_rungs`), plus the premise-spelling iff
  (`ssaturated_iff`).
* **§2 THE REDUCTION** — `forkless_rungs_agree` (the residue's
  contrapositive: forkless + saturated + differing rungs is
  absurd) and `forkless_found_unique` (the campaign theorem,
  conditional on the residue).
* **§3 THE ATTACK'S FIRST EXHIBIT** — `rung_diff_exhibit`:
  differing rungs already name the differing card — founded at the
  deep endpoint, at-rung and missing at the shallow one — the
  split the dip argument starts from.

THE RESIDUE'S ROUTE (priced; the full route lives on the registry
def's own docstring): the witness-journey dip — the rung ledger
nets the difference into a σ-pull (LIFO exodus) plus a twin-raise
(first passage), the dip state between the last pull and the first
raise, and the `SSaturated` endpoints' two bars (cargo above
frontier; twin tops no pile) confining the dip's live set to the
pair.

House compliance: additive leaf (`Orig2.PairClassSeed` only — the
seed kit plus the certified seam); per-row provenance docstrings;
zero `sorry`, zero `Classical.choice`; the battery at the tail.
-/

/-! ## §1. The finishing kit (rungs → founds) -/

/-- **Rungs live at or below the suit's size** — the take-prefix
discipline at `WF` bounds every rung by 13.  (The frozen precedent
`rung_le`, `Orig/FoundKit.lean:412`.) -/
theorem rungAt_le13 {st : State} (hwf : st.WF) (σ : Suit) :
    rungAt st σ ≤ 13 := by
  obtain ⟨n, hn⟩ := hwf.found_prefix σ
  show (st.found σ).length ≤ 13
  rw [hn, List.length_take, Suit.upCards_length]
  omega

/-- **THE RUNG→FOUND CONGRUENCE** — at `WF` states, equal rungs on a
suit give identical foundations on that suit: both founds are
take-prefixes of the one build order, cut at the same index.  (The
frozen precedent `rung_found_congr`, `Orig/MacroInternal.lean:760`,
delegating `FoundKit.found_congr`.) -/
theorem found_congr_of_rungs {u v : State} (hu : u.WF) (hv : v.WF)
    {σ : Suit} (h : rungAt u σ = rungAt v σ) : u.found σ = v.found σ := by
  obtain ⟨n, hn⟩ := hu.found_prefix σ
  obtain ⟨m, hm⟩ := hv.found_prefix σ
  have hlen : (σ.upCards.take n).length = (σ.upCards.take m).length := by
    have h' : (u.found σ).length = (v.found σ).length := h
    rw [hn, hm] at h'
    exact h'
  rw [List.length_take, List.length_take, Suit.upCards_length] at hlen
  rcases Nat.lt_or_ge n 13 with h1 | h1
  · rw [hn, hm, (by omega : n = m)]
  · rw [hn, hm,
      take_ge_length σ.upCards n (by rw [Suit.upCards_length]; exact h1),
      take_ge_length σ.upCards m (by rw [Suit.upCards_length]; omega)]

/-- The grade subsumes the campaign's premise spelling: saturation
is the `¬∃` read of the same license. -/
theorem ssaturated_iff {st : State} :
    SSaturated st ↔ ¬ ∃ c, CanRaiseS st c :=
  ⟨fun h ⟨c, hc⟩ => h c hc, fun h c hc => h ⟨c, hc⟩⟩

/-! ## §2. The reduction (the residue as premise) -/

/-- **THE REDUCTION'S RUNG HALF** — the residue's contrapositive: in
a class whose every member refuses the fork, two saturated
endpoints cannot disagree on any rung.  The proof is the residue's
elim: a disagreement hands back a `ForkWitness` at a class-mate,
and the forkless premise refutes it on the spot. -/
theorem forkless_rungs_agree (hres : SatDifferFork) {s s' : State}
    (hclass : sameOrbitSetoid.r s s')
    (hfrk : ∀ u, sameOrbitSetoid.r s u → ¬ forkState u)
    (hsat : SSaturated s) (hsat' : SSaturated s') :
    ∀ σ, rungAt s σ = rungAt s' σ := by
  intro σ
  rcases Nat.lt_trichotomy (rungAt s σ) (rungAt s' σ) with h | h | h
  · obtain ⟨F, x, hF, hfx⟩ :=
      hres s s' hsat hsat' hclass ⟨σ, Nat.ne_of_lt h⟩
    exact absurd (forkState_iff.mpr ⟨x, hfx⟩) (hfrk F hF)
  · exact h
  · obtain ⟨F, x, hF, hfx⟩ :=
      hres s s' hsat hsat' hclass ⟨σ, (Nat.ne_of_lt h).symm⟩
    exact absurd (forkState_iff.mpr ⟨x, hfx⟩) (hfrk F hF)

/-- **THE CAMPAIGN THEOREM, REDUCED** — in a forkless macro class,
two saturated endpoints share their foundations verbatim, one
`SatDifferFork` away: the residue kills the rung disagreement, and
the finishing kit converts agreeing rungs into agreeing foundations
at `WF`.  Discharging the residue IS the campaign's remaining
program (the dip route, the registry def's docstring). -/
theorem forkless_found_unique (hres : SatDifferFork) {s s' : State}
    (hwf : s.WF) (hwf' : s'.WF)
    (hclass : sameOrbitSetoid.r s s')
    (hfrk : ∀ u, sameOrbitSetoid.r s u → ¬ forkState u)
    (hsat : SSaturated s) (hsat' : SSaturated s') :
    s.found = s'.found := by
  have hrungs := forkless_rungs_agree hres hclass hfrk hsat hsat'
  funext σ
  exact found_congr_of_rungs hwf hwf' (hrungs σ)

/-! ## §3. The attack's first exhibit -/

/-- **THE SPLIT EXHIBIT** — differing rungs on one suit already NAME
the differing card: the σ-card at the shallow rung is FOUNDED at
the deep endpoint and merely at-rung (missing) at the shallow one.
This is the split the dip argument starts from (the frozen-tier
precedent derives the same shape from the register's flip —
`crossarm_flip_benign_or_forked`, `Orig/ConeCrossarm.lean:158`;
here the difference is arbitrary — no register, no corridor
needed). -/
theorem rung_diff_exhibit {u v : State} (hu : u.WF) (hv : v.WF)
    {σ : Suit} (hlt : rungAt v σ < rungAt u σ) :
    ∃ c : Card, c.suit = σ ∧ c.rank.toIdx = rungAt v σ ∧
      c ∈ u.found σ ∧ c ∉ v.found σ := by
  have hk : rungAt v σ < 13 := Nat.lt_of_lt_of_le hlt (rungAt_le13 hu σ)
  refine ⟨Card.mk σ (FoundKit.Rk (rungAt v σ)), rfl, FoundKit.Rk_toIdx _ hk, ?_, ?_⟩
  · exact (FoundKit.mem_found_iff_height hu).mpr (by
      show (FoundKit.Rk (rungAt v σ)).toIdx < rungAt u (Card.mk σ (FoundKit.Rk (rungAt v σ))).suit
      rw [FoundKit.Rk_toIdx _ hk]
      show rungAt v σ < rungAt u σ
      exact hlt)
  · intro hmem
    have hlt' := (FoundKit.mem_found_iff_height hv).mp hmem
    rw [show (Card.mk σ (FoundKit.Rk (rungAt v σ))).rank.toIdx = rungAt v σ from
      FoundKit.Rk_toIdx _ hk] at hlt'
    exact Nat.lt_irrefl _ hlt'

/-! ## §4. The battery -/

#print axioms rungAt_le13
#print axioms found_congr_of_rungs
#print axioms ssaturated_iff
#print axioms forkless_rungs_agree
#print axioms forkless_found_unique
#print axioms rung_diff_exhibit
