import Orig2.Fork.Class.ForkReadBracket

/-! ## Merged from `ForkExist.lean` (2026-11-02) -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Exist_Kit — the MINIMALITY-GATED read bracket residual

Scratch card.  READ-ONLY on repository source; no commit.

`Temp/Exist_Refute.lean` proves that `R12.ReadBracketElim` is FALSE as
stated: a four-letter witness *loop* (`pull 5H ; slide 4C -> 5H ;
slide 4C -> 5D ; raise 5H`, returning to its own start) has a non-fork
valley bottom whose only same-card bracket has an `S2`-violating interior.

This card isolates the corrected residual: the same statement with the
play's minimality as a hypothesis (which the campaign always has, via
`ShortestPlayExists`).  Three facts:

1. `ReadBracketElimMin ↔ ValleyForkAtMin` — the minimality-gated residual is
   EXACTLY "every minimal valley bottom is a fork".  A bracket at a minimal
   play would delete (`NonforkKit.bracket_delete_gen`), contradicting
   minimality; hence the bracket disjunct is never the load-bearing one.
2. `ReadBracketElimMin → ValleyElimNonforkMin` (the gated elimination).
3. `ValleyElimNonforkMin → SatDifferForkWF` under the campaign's
   `ShortestPlayExists`, so `ValleyForkAtMin` is the exact remaining input.

Everything here is constructive (no `Classical.choice`; the `by_cases` in the
refutation card is on a decidable card equality only).
-/

namespace ExistKit

open ValleyElim

/-- **`ReadBracketElimMin`** — `R12.ReadBracketElim` with the minimality of
`ρ` added.  This is the only form in which the bracket can be asked for: the
un-gated form is refuted by `ExistRefute.not_readBracketElim`. -/
def ReadBracketElimMin : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State),
    u.WF → SSaturated u → SSaturated v →
    ShufflePlayW u ρ v →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
    ValleySplitAt u v ρ F →
    (∃ x : Card, ForkWitness F x) ∨
    (∃ (α γ β : List Move) (z : Card) (bz : Base) (P Q : State),
      ρ = α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z :: β ∧
      ShufflePlayW u α P ∧
      State.step P (Move.foundToTab z bz) = some Q ∧
      CanRaise Q z ∧
      (∀ q ∈ γ, R12.ReadOK z q))

/-- **`ValleyForkAtMin`** — every valley split of a MINIMAL witness play has
a fork at its bottom.  This is the census's 4010/4010 minimal-bottom
statement (`Temp/SplitProbe_Report.md`), stated as the residual. -/
def ValleyForkAtMin : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State),
    u.WF → SSaturated u → SSaturated v →
    ShufflePlayW u ρ v →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
    ValleySplitAt u v ρ F →
    ∃ x : Card, ForkWitness F x

/-- **`ValleyElimNonforkMin`** — `ValleyElimNonfork` restricted to minimal
plays (the form the campaign actually consumes). -/
def ValleyElimNonforkMin : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State),
    u.WF → SSaturated u → SSaturated v →
    ShufflePlayW u ρ v →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
    ValleySplitAt u v ρ F →
    (∃ x : Card, ForkWitness F x) ∨
      (∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length)

/-! ## §0. The un-gated residual implies the gated one -/

theorem readBracketElimMin_of_readBracket (h : R12.ReadBracketElim) :
    ReadBracketElimMin := by
  intro u v ρ F huwf hsu hsv hplay _ hsplit
  exact h u v ρ F huwf hsu hsv hplay hsplit

/-! ## §0b. The exact existence certificate: a same-card window

`ReadBracketElim`'s data is a same-card pair whose interior is `ReadOK`.  The
converse packaging is unconditional — this isolates the *existence* half as a
single `ReadWindowExists` predicate (which `Temp/Exist_Refute.lean` refutes in
the un-gated form). -/

/-- **A read-safe same-card window gives the bracket data.**  `CanRaise` at
the pull landing is automatic (`ValleyStep.pull_card_canRaise`). -/
theorem bracket_of_samecard_window
    {u v : State} {ρ α γ β : List Move} {z : Card} {bz : Base}
    (huwf : u.WF) (hplay : ShufflePlayW u ρ v)
    (hρ : ρ = α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z :: β)
    (hread : ∀ q ∈ γ, R12.ReadOK z q) :
    ∃ (α γ β : List Move) (z : Card) (bz : Base) (P Q : State),
      ρ = α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z :: β ∧
      ShufflePlayW u α P ∧
      State.step P (Move.foundToTab z bz) = some Q ∧
      CanRaise Q z ∧
      (∀ q ∈ γ, R12.ReadOK z q) := by
  have hρ' : ρ = α ++ (Move.foundToTab z bz :: (γ ++ Move.tabToFound z :: β)) := by
    rw [hρ]
    simp only [List.cons_append, List.append_assoc, List.nil_append]
  obtain ⟨P, hα, hrest⟩ :=
    ShufflePlayW_split hplay α
      (Move.foundToTab z bz :: (γ ++ Move.tabToFound z :: β)) hρ'
  obtain ⟨Q, -, hstep, -⟩ := Bubble.walk_cons_inv hrest
  have hPwf : P.WF := SatDifferCensus.ShufflePlayW.wf_end hα huwf
  have hcan : CanRaise Q z := ValleyStep.pull_card_canRaise hPwf hstep
  exact ⟨α, γ, β, z, bz, P, Q, hρ, hα, hstep, hcan, hread⟩

/-- **`ReadWindowExists`** — the exact existence half: at every non-fork
valley split there is a same-card pair whose interior is `ReadOK`. -/
def ReadWindowExists : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State),
    u.WF → SSaturated u → SSaturated v →
    ShufflePlayW u ρ v →
    ValleySplitAt u v ρ F →
    (∃ x : Card, ForkWitness F x) ∨
    (∃ (α γ β : List Move) (z : Card) (bz : Base),
      ρ = α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z :: β ∧
      (∀ q ∈ γ, R12.ReadOK z q))

theorem readBracketElim_of_windowExists (h : ReadWindowExists) :
    R12.ReadBracketElim := by
  intro u v ρ F huwf hsu hsv hplay hsplit
  rcases h u v ρ F huwf hsu hsv hplay hsplit with
    hf | ⟨α, γ, β, z, bz, hρ, hread⟩
  · exact Or.inl hf
  · exact Or.inr (bracket_of_samecard_window huwf hplay hρ hread)

/-! ## §1. A read-safe bracket deletes at a minimal play -/

/-- The deletion step: from the bracket's landing play and the per-letter
`ReadOK` certificate, a strictly shorter witness play. -/
theorem shorter_of_readBracket
    {u v : State} {ρ α γ β : List Move} {z : Card} {bz : Base} {P Q : State}
    (huwf : u.WF) (hplay : ShufflePlayW u ρ v)
    (hρ : ρ = α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z :: β)
    (hα : ShufflePlayW u α P)
    (hstep : State.step P (Move.foundToTab z bz) = some Q)
    (hcan : CanRaise Q z) (hread : ∀ q ∈ γ, R12.ReadOK z q) :
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length := by
  have hPwf : P.WF := SatDifferCensus.ShufflePlayW.wf_end hα huwf
  have hQwf : Q.WF := step_wf hPwf hstep
  have hplayQ : ShufflePlayW Q (γ ++ Move.tabToFound z :: β) v :=
    R12.bracket_landing_play hplay hρ hα hstep
  have hsw : NonforkKit.RaiseSwaps Q z γ :=
    R12.raiseSwaps_of_read hQwf hplayQ hcan hread
  exact NonforkKit.bracket_delete_gen huwf hplay hρ hα hstep hsw

/-! ## §2. The gated residual is exactly "minimal bottoms are forks" -/

/-- `ReadBracketElimMin` forces the fork at every minimal valley split: the
bracket branch would delete and contradict minimality. -/
theorem forkAtMin_of_readBracketMin (h : ReadBracketElimMin) : ValleyForkAtMin := by
  intro u v ρ F huwf hsu hsv hplay hmin hsplit
  rcases h u v ρ F huwf hsu hsv hplay hmin hsplit with
    hf | ⟨α, γ, β, z, bz, P, Q, hρ, hα, hstep, hcan, hread⟩
  · exact hf
  · exfalso
    obtain ⟨ρ', hρ'play, hρ'len⟩ :=
      shorter_of_readBracket huwf hplay hρ hα hstep hcan hread
    exact absurd (hmin ρ' hρ'play) (by omega)

theorem readBracketMin_of_forkAtMin (h : ValleyForkAtMin) : ReadBracketElimMin := by
  intro u v ρ F huwf hsu hsv hplay hmin hsplit
  exact Or.inl (h u v ρ F huwf hsu hsv hplay hmin hsplit)

/-- **THE CORRECTION.**  At minimal plays the read-safe-bracket residual is
EQUIVALENT to the fork statement: the bracket branch is never the content. -/
theorem readBracketElimMin_iff_forkAtMin :
    ReadBracketElimMin ↔ ValleyForkAtMin :=
  ⟨forkAtMin_of_readBracketMin, readBracketMin_of_forkAtMin⟩

/-! ## §3. The gated elimination and the campaign reduction -/

theorem valleyElimNonforkMin_of_readBracketMin (h : ReadBracketElimMin) :
    ValleyElimNonforkMin := by
  intro u v ρ F huwf hsu hsv hplay hmin hsplit
  rcases h u v ρ F huwf hsu hsv hplay hmin hsplit with
    hf | ⟨α, γ, β, z, bz, P, Q, hρ, hα, hstep, hcan, hread⟩
  · exact Or.inl hf
  · exact Or.inr (shorter_of_readBracket huwf hplay hρ hα hstep hcan hread)

/-- **THE CAMPAIGN REDUCTION FROM THE GATED RESIDUAL.** -/
theorem satDifferForkWF_of_valleyElimNonforkMin
    (h : ValleyElimNonforkMin) (hmin : ShortestPlayExists) :
    SatDifferForkWF := by
  intro u v huwf hsu hsv hcls hdiff
  obtain ⟨ρ, hρ, hminlen⟩ := hmin u v huwf hsu hsv hcls hdiff
  obtain ⟨F, hFsplit⟩ := valley_exists huwf hsu hsv hdiff hρ
  obtain ⟨left, right, c, d, b, pre, post, tail,
    hsplitEq, hleft, hright, hshape, hfree, hrightShape⟩ := hFsplit
  rcases h u v ρ F huwf hsu hsv hρ hminlen
      ⟨left, right, c, d, b, pre, post, tail,
        hsplitEq, hleft, hright, hshape, hfree, hrightShape⟩ with
    hfork | ⟨ρ', hρ'play, hρ'len⟩
  · obtain ⟨x, hx⟩ := hfork
    exact ⟨F, x, RevEqW_symm (shufflePlayW_revEqW hleft), hx⟩
  · exact absurd hρ'len (Nat.not_lt.mpr (hminlen ρ' hρ'play))

/-- **THE CORRECTED FRONTIER.**  `ValleyForkAtMin` (every minimal valley
bottom is a fork) plus the choice-free shortest-play interface yields the
ceiling campaign's `SatDifferForkWF`.  This replaces the refuted
`ReadBracketElim` route. -/
theorem satDifferForkWF_of_forkAtMin
    (h : ValleyForkAtMin) (hmin : ShortestPlayExists) : SatDifferForkWF :=
  satDifferForkWF_of_valleyElimNonforkMin
    (valleyElimNonforkMin_of_readBracketMin (readBracketMin_of_forkAtMin h)) hmin

end ExistKit

#print axioms ExistKit.readBracketElimMin_of_readBracket
#print axioms ExistKit.bracket_of_samecard_window
#print axioms ExistKit.readBracketElim_of_windowExists
#print axioms ExistKit.shorter_of_readBracket
#print axioms ExistKit.forkAtMin_of_readBracketMin
#print axioms ExistKit.readBracketMin_of_forkAtMin
#print axioms ExistKit.readBracketElimMin_iff_forkAtMin
#print axioms ExistKit.valleyElimNonforkMin_of_readBracketMin
#print axioms ExistKit.satDifferForkWF_of_valleyElimNonforkMin
#print axioms ExistKit.satDifferForkWF_of_forkAtMin


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# ForkMinCross — the fork may occur ANYWHERE on the minimal play

`ExistKit.ValleyForkAtMin` pins the fork to the valley bottom `F`.  That is
strictly stronger than the campaign needs: `SatDifferForkWF` asks only for a
fork state in `u`'s orbit, and EVERY state on a witness play from `u` is in
that orbit (`ShufflePlayW u α F → RevEqW u F`).

So the honest residual is the weaker

  `MinCrossesFork`: every minimal witness play between differing-rung
  saturated class-mates visits a fork somewhere.

Its contrapositive is the statement the fork-free-path probes actually
compute: *a fork-free witness play is not minimal* (the kernel's own
`Orig2/Boundary/BoundaryForkFree.lean` play is the canonical test object: 14 moves,
fork-free, while the fork-crossing play has 12).

Two facts here:

1. `ValleyForkAtMin → MinCrossesFork` (the split's left leg is the prefix);
2. `MinCrossesFork → ShortestPlayExists → SatDifferForkWF`.

This card changes no existing statement; it only records that the pinned
bottom is not needed.
-/

namespace MinKit

open ValleyElim

/-- **A fork occurs at a state on the play**: `α` is a prefix landing at `F`. -/
def ForkOnPrefix (u : State) (ρ : List Move) : Prop :=
  ∃ (F : State) (x : Card) (α β : List Move),
    ρ = α ++ β ∧ ShufflePlayW u α F ∧ ForkWitness F x

/-- **`MinCrossesFork`** — every minimal witness play between differing-rung
saturated states visits a fork.  Weaker than `ExistKit.ValleyForkAtMin`, which
demands the fork at the valley bottom. -/
def MinCrossesFork : Prop :=
  ∀ (u v : State) (ρ : List Move),
    u.WF → SSaturated u → SSaturated v →
    ShufflePlayW u ρ v →
    (∃ σ : Suit, rungAt u σ ≠ rungAt v σ) →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
    ForkOnPrefix u ρ

/-- **`ValleyForkAtMin` IMPLIES `MinCrossesFork`.**  `valley_exists` supplies
the split; its left leg is the prefix, and `ValleyForkAtMin` puts the fork at
the bottom `F`. -/
theorem minCrossesFork_of_valleyForkAtMin (h : ExistKit.ValleyForkAtMin) :
    MinCrossesFork := by
  intro u v ρ huwf hsu hsv hplay hdiff hmin
  obtain ⟨F, hF⟩ := valley_exists huwf hsu hsv hdiff hplay
  obtain ⟨left, right, c, d, b, pre, post, tail,
    hsplitEq, hleft, hright, hshape, hfree, hrightShape⟩ := hF
  obtain ⟨x, hx⟩ :=
    h u v ρ F huwf hsu hsv hplay hmin
      ⟨left, right, c, d, b, pre, post, tail,
        hsplitEq, hleft, hright, hshape, hfree, hrightShape⟩
  exact ⟨F, x, left, right, hsplitEq, hleft, hx⟩

/-- **THE CAMPAIGN REDUCTION FROM THE WEAKER RESIDUAL.**  Any state on a
witness play from `u` is in `u`'s orbit, so a fork anywhere on the minimal
play discharges `SatDifferForkWF`. -/
theorem satDifferForkWF_of_minCrossesFork
    (h : MinCrossesFork) (hmin : ShortestPlayExists) : SatDifferForkWF := by
  intro u v huwf hsu hsv hcls hdiff
  obtain ⟨ρ, hρ, hminlen⟩ := hmin u v huwf hsu hsv hcls hdiff
  obtain ⟨F, x, α, β, _heq, hα, hx⟩ :=
    h u v ρ huwf hsu hsv hρ hdiff hminlen
  exact ⟨F, x, RevEqW_symm (shufflePlayW_revEqW hα), hx⟩

#print axioms MinKit.minCrossesFork_of_valleyForkAtMin
#print axioms MinKit.satDifferForkWF_of_minCrossesFork

end MinKit
