import Temp.PullReplay
import Temp.RungMono
import Temp.FrozenSuit
import Orig2.Fork.Class.ForkRaiseReorderProof

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-!
# Temp/PullTwin — the pull case, twin included

The target is the `hPull` hypothesis of `Temp/RaisesOrForkMain.lean`:

```lean
theorem pull_case {s u t v : State} {c : Card} {b : Base} {ws : List Card}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hρ : RaiseSSeqLicensed u ws v) (ht : RungLe t v)
    (hno : ∀ d ∈ ws, d.suit ≠ c.suit) :
    (∃ v', RaiseSSeqLicensed s (playWord (sortByRank ws)) v' ∧
      RungLe s v' ∧ RungLe t v') ∨ Fork s
```

This card proves the branch on which the endpoint still licenses the pulled
card, and records the twin residual precisely.

## What is proved

* `pull_case_of_live` — the whole pull case **given** `CanRaiseS v c`
  (Case A of the brief).  No deficit hypothesis at all.
* `twin_mem_of_dead` — if the endpoint no longer licenses `c`, then the word
  must raise `c.twin` (Case B0).
* `orbit_source_block` — the pull source and the block end are orbit-mates.
* `lock_contradiction` — the commit-lock disjunct at a block end at which `c`
  is still a pile top is impossible (the frozen-suit rung bound contradicts
  the pull's `+1`).
* `pull_case_noTwin` — the unconditional non-twin case, reused from
  `Temp/PullReplay.lean`.
* `pull_case_or_twin_dead` — the exhaustive dichotomy with the one open case
  isolated.
* `pull_case_of_dead_twin_fork` — the target, from the single missing input
  "the dead-twin configuration produces a fork".

## The residual

`pull_case_or_twin_dead` isolates the only shape not closed here:

```lean
c.twin ∈ ws ∧ ¬ CanRaiseS v c
```

(the twin is raised and the pulled card dies).  The target is
`pull_case_of_dead_twin_fork`, whose extra input

```lean
hfork : c.twin ∈ ws → ¬ CanRaiseS v c → Fork s
```

is not derivable from the present library: `SpectrumCollapse`'
`spectrum_pair_fork_or_both` leaves the both-vanilla collapsed-spectrum arm,
in which neither twin is vanilla-blocked.  The acceptance board below
(`counter_board_twin_kill`) is an instance of the residual where the fork arm
does hold, through the pull landing.

Everything below is constructive: no `sorry`, no `Classical`, no
`noncomputable`, no new `Prop` wrapper.
-/

namespace OneColourClosure

/-! ## §0. The pull's rung ledger, in successor form -/

/-- **The pull lowers its suit's rung by exactly one, so the source is one
above the landing.**  (Successor form, so no truncated subtraction.) -/
theorem pull_rung_succ {s u : State} {c : Card} {b : Base}
    (hpull : State.step s (Move.foundToTab c b) = some u) :
    rungAt s c.suit = rungAt u c.suit + 1 := by
  obtain ⟨c', htop, hc', hcp, hv⟩ := step_foundToTab_inv hpull
  rw [hc'] at htop
  have hlast : lastOf (s.found c.suit) = some c := htop
  have hsplit : s.found c.suit = chop (s.found c.suit) ++ [c] := lastOf_chop hlast
  have hpos : 0 < rungAt s c.suit := by
    unfold rungAt
    exact List.length_pos_iff.mpr (by rw [hsplit]; simp)
  have h := rungAt_foundToTab hpull c.suit
  rw [ite_eq_left rfl] at h
  omega

/-! ## §1. Case A — the endpoint still licenses the pulled card -/

/-- **The pull case when `c` survives.**  If `c` is still `S`-live at the
endpoint `v` of the licensed play from the pull landing `u`, then the
play from `s` with word `playWord (sortByRank ws)` exists and dominates
both `s` and any `t` below `v`.

The play itself is `pull_case_of_end_live`; the two rung comparisons are the
pull's ledger (`s` is one rung above `u` on `c`'s suit and equal elsewhere)
and the play's monotonicity. -/
theorem pull_case_of_live {s u t v : State} {c : Card} {b : Base}
    {ws : List Card}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hρ : RaiseSSeqLicensed u ws v) (ht : RungLe t v)
    (hno : ∀ d ∈ ws, d.suit ≠ c.suit) (hcz : CanRaiseS v c) :
    ∃ v', RaiseSSeqLicensed s (playWord (sortByRank ws)) v' ∧
      RungLe s v' ∧ RungLe t v' := by
  obtain ⟨v', hplay, hrung_ne, hrung_c⟩ :=
    pull_case_of_end_live hs hpull hρ hno hcz
  -- the pull's ledger: `u` is `s` except one rung down on `c`'s suit
  have hs_eq : rungAt s c.suit = rungAt u c.suit + 1 := pull_rung_succ hpull
  have hs_ne : ∀ σ, σ ≠ c.suit → rungAt s σ = rungAt u σ := by
    intro σ hσ
    have h := rungAt_foundToTab hpull σ
    rw [ite_eq_right hσ] at h
    exact h.symm
  -- `ws` has no letter of `c`'s suit, so `v` agrees with `u` there
  have hv_c : rungAt v c.suit = rungAt u c.suit :=
    RungMono.rungAt_eq_of_no_letter hρ hno
  refine ⟨v', hplay, ?_, ?_⟩
  · intro σ
    by_cases hσ : σ = c.suit
    · subst hσ
      rw [hrung_c, hs_eq]
      exact Nat.le_refl _
    · rw [hrung_ne σ hσ, hs_ne σ hσ]
      exact RungMono.rungAt_le hρ σ
  · intro σ
    by_cases hσ : σ = c.suit
    · subst hσ
      have ht' : rungAt t c.suit ≤ rungAt v c.suit := ht c.suit
      rw [hrung_c, ← hv_c]
      exact Nat.le_succ_of_le ht'
    · rw [hrung_ne σ hσ]
      exact ht σ

/-! ## §2. Case B0 — a dead endpoint forces the twin into the word -/

/-- **If `c` dies, the word raises `c.twin`.**  `c` is live at the pull
landing (`SatDifferConfig.canRaiseS_after_pull`), the word is silent on
`c`'s suit (so it raises neither `c`), and a licensed word avoiding both
`c` and `c.twin` preserves `c`'s licence. -/
theorem twin_mem_of_dead {u v : State} {ws : List Card} {c : Card}
    (hu : u.WF) (hρ : RaiseSSeqLicensed u ws v) (hc : CanRaiseS u c)
    (hno : ∀ d ∈ ws, d.suit ≠ c.suit) (hdead : ¬ CanRaiseS v c) :
    c.twin ∈ ws := by
  by_cases htw : c.twin ∈ ws
  · exact htw
  · exact absurd (canRaiseS_of_word_notMem hρ hu hc
      (fun hmem => hno c hmem rfl) htw) hdead

/-! ## §3. The commit lock at the block end is impossible -/

/-- The pull source and the block end are orbit-mates (the pull is
reversible; the low block is a licensed play). -/
theorem orbit_source_block {s u bnd : State} {c : Card} {b : Base}
    {low : List Card}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hlow : RaiseSSeqLicensed u (playWord low) bnd) :
    sameOrbitSetoid.r bnd s := by
  have hu : u.WF := step_wf hs hpull
  have hback : State.step u (Move.tabToFound c) = some s :=
    step_tabToFound_of_foundToTab hs hpull
  have hrev : reversibleAtW s (Move.foundToTab c b) :=
    reversible_mirrorW hpull hback
  have hsu : sameOrbitSetoid.r s u :=
    sameOrbitSetoid.iseqv.symm
      (shufflePlayW_revEqW (Walk.cons hrev hpull (Walk.nil u)))
  have hbu : sameOrbitSetoid.r bnd u := hlow.revEqW hu
  exact sameOrbitSetoid.iseqv.trans hbu (sameOrbitSetoid.iseqv.symm hsu)

/-- **No commit lock at a block end that still has `c` on top.**  If the
block end is next-up for `c` and `c` is a pile top whose face-up run starts
at `c` (so raising it would reveal hidden cards, or it is a non-king), the
frozen-suit bound says that no orbit-mate has a higher `c`-suit rung than
the block end.  But the pull source is one rung higher. -/
theorem lock_contradiction {s u bnd : State} {c : Card} {b : Base}
    {low : List Card}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hlow : RaiseSSeqLicensed u (playWord low) bnd)
    (hnoLow : ∀ d ∈ playWord low, d.suit ≠ c.suit)
    (hnext : bnd.nextUp c = true) {a : Anchor}
    (htop : bnd.pileOfTop c = some a)
    (hbel : below c (bnd.piles a).faceUp = [])
    (hlk : (bnd.piles a).hidden ≠ [] ∨ c.rank ≠ Rank.king) : False := by
  have hu : u.WF := step_wf hs hpull
  have hbnd : bnd.WF := hlow.wf hu
  have horb : sameOrbitSetoid.r bnd s := orbit_source_block hs hpull hlow
  have hle : rungAt s c.suit ≤ rungAt bnd c.suit := by
    rcases hlk with hh | hk
    · exact FrozenSuit.commitLocked_rung_le hbnd horb hnext htop hbel hh
    · exact FrozenSuit.commitLocked_rung_le_of_not_king hbnd horb hnext htop hbel hk
  -- the block end's rung on `c`'s suit is pinned by `nextUp`
  have hbndR : rungAt bnd c.suit = c.rank.toIdx := by
    have h : c.rank.toIdx = rungAt bnd c.suit := by
      simpa [State.foundHeight, rungAt] using of_decide_eq_true hnext
    exact h.symm
  -- the pull source is one rung above the landing, and the low block is silent
  have hlowR : rungAt bnd c.suit = rungAt u c.suit :=
    RungMono.rungAt_eq_of_no_letter hlow hnoLow
  have hsR : rungAt s c.suit = c.rank.toIdx + 1 := by
    have hnextU : u.nextUp c = true :=
      SatDifferConfig.nextUp_after_pull hs hpull
    have huR : rungAt u c.suit = c.rank.toIdx := by
      have h : c.rank.toIdx = rungAt u c.suit := by
        simpa [State.foundHeight, rungAt] using of_decide_eq_true hnextU
      exact h.symm
    rw [pull_rung_succ hpull, huR]
  rw [hsR, hbndR] at hle
  omega

/-! ## §4. The non-twin case, reused -/

/-- **The unconditional non-twin pull case** (Route 1).  This is
`Temp/PullReplay.lean`'s `pull_case_sorted_rungLe`, restated in the
`hPull` shape. -/
theorem pull_case_noTwin {s u t v : State} {c : Card} {b : Base}
    {ws : List Card}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hρ : RaiseSSeqLicensed u ws v) (ht : RungLe t v)
    (hno : ∀ d ∈ ws, d.suit ≠ c.suit) (htwin : c.twin ∉ ws) :
    ∃ v', RaiseSSeqLicensed s (playWord (sortByRank ws)) v' ∧
      RungLe s v' ∧ RungLe t v' :=
  pull_case_sorted_rungLe hs hpull hρ hno htwin ht

/-! ## §4b. What closes, and the exact residual

The two proved branches cover

* the endpoint still licensing `c` (Case A, `pull_case_of_live`);
* the word avoiding `c.twin` (Route 1, `pull_case_noTwin`).

The only remaining shape is

```
c.twin ∈ ws  ∧  ¬ CanRaiseS v c
```

i.e. the twin is raised and the pulled card dies.  The theorem below makes this
exhaustive: the target `pull_case` is exactly this theorem with the third
disjunct replaced by `Fork s`. -/

/-- **The pull-case dichotomy, with the twin-dead case isolated.**  Either the
play from `s` exists, or `s` is already a fork, or the word raises `c.twin`
while the endpoint no longer licenses `c`. -/
theorem pull_case_or_twin_dead {s u t v : State} {c : Card} {b : Base}
    {ws : List Card}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hρ : RaiseSSeqLicensed u ws v) (ht : RungLe t v)
    (hno : ∀ d ∈ ws, d.suit ≠ c.suit) :
    (∃ v', RaiseSSeqLicensed s (playWord (sortByRank ws)) v' ∧
      RungLe s v' ∧ RungLe t v')
      ∨ Fork s ∨ (c.twin ∈ ws ∧ ¬ CanRaiseS v c) := by
  have hu : u.WF := step_wf hs hpull
  have hv : v.WF := hρ.wf hu
  by_cases hlive : canRaiseSB v c = true
  · have hlive' : CanRaiseS v c := (canRaiseSB_iff hv).mp hlive
    exact Or.inl (pull_case_of_live hs hpull hρ ht hno hlive')
  · have hdead : ¬ CanRaiseS v c :=
      fun h => hlive ((canRaiseSB_iff hv).mpr h)
    by_cases htw : c.twin ∈ ws
    · exact Or.inr (Or.inr ⟨htw, hdead⟩)
    · exact Or.inl (pull_case_noTwin hs hpull hρ ht hno htw)

/-- **The target, from the one missing twin-dead input.**  If the dead-twin
configuration always produces a fork, the pull case closes with no other
hypothesis.  This is the exact shape of the residual. -/
theorem pull_case_of_dead_twin_fork {s u t v : State} {c : Card} {b : Base}
    {ws : List Card}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hρ : RaiseSSeqLicensed u ws v) (ht : RungLe t v)
    (hno : ∀ d ∈ ws, d.suit ≠ c.suit)
    (hfork : c.twin ∈ ws → ¬ CanRaiseS v c → Fork s) :
    (∃ v', RaiseSSeqLicensed s (playWord (sortByRank ws)) v' ∧
      RungLe s v' ∧ RungLe t v')
      ∨ Fork s := by
  rcases pull_case_or_twin_dead hs hpull hρ ht hno with hplay | hfork' | ⟨htw, hdead⟩
  · exact Or.inl hplay
  · exact Or.inr hfork'
  · exact Or.inr (hfork htw hdead)

end OneColourClosure

/-! ## §5. The acceptance boards

`Temp/PullReplay_Counter.lean`'s board is

```
♥ = A..4,  ♦ = A..4,  p0 = [6♣, 5♥, 4♠],  p1 = [6♠, 5♦],  c = 5♥,  ws = [5♦]
```

Two consistent readings are checked:

* **A (`counter_board_literal`)** — the board is the pull *landing* `u`; the
  pulled card is the cover `4♠`, pulled from a source with `♠ = A..4` and
  `p0 = [6♣, 5♥]`.  The play `ws = [5♦]` then kills the counter's `5♥` at the
  endpoint (its twin `5♦` leaves the tableau).  This is an instance of the
  non-twin route (`4♠.twin = 4♣ ∉ ws`).
* **B (`counter_board_twin_kill`)** — the pulled card is `5♥` itself; the cover
  `4♠` is slid onto it by the cargo path of the `5♦` letter.  At the endpoint
  `5♥` is dead, `4♠` is not raisable, and `CanRaiseS s 5♦` **fails** (the twin
  is buried at the source too).  The conclusion survives through the `Fork s`
  arm: the pull landing `u` has collapsed spectrum `{5♥, 5♦}` and `5♦` is
  vanilla-blocked.
-/

namespace PullTwinBoard

open OneColourClosure

/-! ### §5.0 Cards -/

def H1 : Card := ⟨.heart, .ace⟩
def H2 : Card := ⟨.heart, .two⟩
def H3 : Card := ⟨.heart, .three⟩
def H4 : Card := ⟨.heart, .four⟩
def H5 : Card := ⟨.heart, .five⟩
def D1 : Card := ⟨.diamond, .ace⟩
def D2 : Card := ⟨.diamond, .two⟩
def D3 : Card := ⟨.diamond, .three⟩
def D4 : Card := ⟨.diamond, .four⟩
def D5 : Card := ⟨.diamond, .five⟩
def S1 : Card := ⟨.spade, .ace⟩
def S2 : Card := ⟨.spade, .two⟩
def S3 : Card := ⟨.spade, .three⟩
def S4 : Card := ⟨.spade, .four⟩
def S6 : Card := ⟨.spade, .six⟩
def C6 : Card := ⟨.club, .six⟩

/-! ### §5.1 Board A — the literal counter board as a pull landing -/

def placedA : List Card :=
  [H1, H2, H3, H4, D1, D2, D3, D4, S1, S2, S3, S4, H5, D5, C6, S6]

def restA : List Card :=
  Card.universe.filter (fun x => decide (x ∉ placedA))

/-- The pull source: `4♠` is founded, `5♥` sits alone on `6♣`. -/
def sA : State where
  found := fun s => match s with
    | .heart => [H1, H2, H3, H4]
    | .diamond => [D1, D2, D3, D4]
    | .spade => [S1, S2, S3, S4]
    | .club => []
  piles := fun a => match a with
    | .p0 => ⟨[], [C6, H5]⟩
    | .p1 => ⟨[], [S6, D5]⟩
    | _ => ⟨[], []⟩
  stock := restA
  waste := []
  drawStep := 1

/-- The pull landing: exactly the counter board (with `♠ = A..3`). -/
def uA : State where
  found := fun s => match s with
    | .heart => [H1, H2, H3, H4]
    | .diamond => [D1, D2, D3, D4]
    | .spade => [S1, S2, S3]
    | .club => []
  piles := fun a => match a with
    | .p0 => ⟨[], [C6, H5, S4]⟩
    | .p1 => ⟨[], [S6, D5]⟩
    | _ => ⟨[], []⟩
  stock := restA
  waste := []
  drawStep := 1

/-- The endpoint: `5♦` is founded and the counter's `5♥` is dead. -/
def vA : State where
  found := fun s => match s with
    | .heart => [H1, H2, H3, H4]
    | .diamond => [D1, D2, D3, D4, D5]
    | .spade => [S1, S2, S3]
    | .club => []
  piles := fun a => match a with
    | .p0 => ⟨[], [C6, H5, S4]⟩
    | .p1 => ⟨[], [S6]⟩
    | _ => ⟨[], []⟩
  stock := restA
  waste := []
  drawStep := 1

theorem sA_wf : sA.WF :=
  ⟨by
     intro s
     cases s
     · exact ⟨4, by decide⟩
     · exact ⟨4, by decide⟩
     · exact ⟨4, by decide⟩
     · exact ⟨0, by decide⟩,
   by intro a; cases a <;> decide,
   by intro c _; rcases c with ⟨s, r⟩; cases s <;> cases r <;> decide,
   by decide⟩

theorem uA_wf : uA.WF :=
  ⟨by
     intro s
     cases s
     · exact ⟨3, by decide⟩
     · exact ⟨4, by decide⟩
     · exact ⟨4, by decide⟩
     · exact ⟨0, by decide⟩,
   by intro a; cases a <;> decide,
   by intro c _; rcases c with ⟨s, r⟩; cases s <;> cases r <;> decide,
   by decide⟩

theorem vA_wf : vA.WF :=
  ⟨by
     intro s
     cases s
     · exact ⟨3, by decide⟩
     · exact ⟨4, by decide⟩
     · exact ⟨5, by decide⟩
     · exact ⟨0, by decide⟩,
   by intro a; cases a <;> decide,
   by intro c _; rcases c with ⟨s, r⟩; cases s <;> cases r <;> decide,
   by decide⟩

theorem pullA : State.step sA (Move.foundToTab S4 (Sum.inr H5)) = some uA := by
  rw [step_foundToTab_splice (by decide) (by decide)]
  congr 1
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) rfl rfl rfl
  · cases σ <;> decide
  · cases a <;> decide

theorem uA_live_D5 : CanRaiseS uA D5 :=
  (canRaiseSB_iff uA_wf).mp (by decide)

theorem raiseA : State.step uA (Move.tabToFound D5) = some vA := by
  rw [step_tabToFound_splice (k := Anchor.p1) (by decide) (by decide)]
  congr 1
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) rfl rfl rfl
  · cases σ <;> decide
  · cases a <;> decide

theorem playA : RaiseSSeqLicensed uA [D5] vA :=
  RaiseSSeqLicensed.cons (RaiseSSeqLicensed.nil uA) uA_live_D5
    (Steps.refl uA) raiseA

theorem hnoA : ∀ d ∈ [D5], d.suit ≠ S4.suit := by
  intro d hd
  rw [List.mem_singleton] at hd
  subst hd
  decide

/-- **Board A, the pull case.**  `4♣ = (4♠).twin ∉ ws`, so the non-twin route
applies and produces the play from the pull source. -/
theorem counter_board_literal :
    ∃ v', RaiseSSeqLicensed sA (playWord (sortByRank [D5])) v' ∧
      RungLe sA v' ∧ RungLe uA v' :=
  pull_case_noTwin sA_wf pullA playA (RungMono.rungAt_le playA) hnoA (by decide)

/-- The counter's `5♥` is dead at the endpoint (its twin `5♦` has left the
tableau, the cover `4♠` cannot be cargo-moved). -/
theorem vA_dead_H5 : ¬ CanRaiseS vA H5 := by
  intro h
  have hSB : canRaiseSB vA H5 = true := (canRaiseSB_iff vA_wf).mpr h
  have hfalse : canRaiseSB vA H5 = false := by decide
  rw [hfalse] at hSB
  exact Bool.noConfusion hSB

/-! ### §5.2 Board B — the twin kill (the counter's mechanism) -/

def placedB : List Card :=
  [H1, H2, H3, H4, H5, D1, D2, D3, D4, S6, D5, S4, C6]

def restB : List Card :=
  Card.universe.filter (fun x => decide (x ∉ placedB))

/-- The pull source: `5♥` is founded, `5♦` sits on `6♠` with `4♠` above it. -/
def sB : State where
  found := fun s => match s with
    | .heart => [H1, H2, H3, H4, H5]
    | .diamond => [D1, D2, D3, D4]
    | _ => []
  piles := fun a => match a with
    | .p0 => ⟨[], [C6]⟩
    | .p1 => ⟨[], [S6, D5, S4]⟩
    | _ => ⟨[], []⟩
  stock := restB
  waste := []
  drawStep := 1

/-- The pull landing: `5♥` exposed on `6♣`. -/
def uB : State where
  found := fun s => match s with
    | .heart => [H1, H2, H3, H4]
    | .diamond => [D1, D2, D3, D4]
    | _ => []
  piles := fun a => match a with
    | .p0 => ⟨[], [C6, H5]⟩
    | .p1 => ⟨[], [S6, D5, S4]⟩
    | _ => ⟨[], []⟩
  stock := restB
  waste := []
  drawStep := 1

/-- After the cargo slide of `4♠` onto `5♥`: `5♦` is exposed. -/
def uB0 : State where
  found := fun s => match s with
    | .heart => [H1, H2, H3, H4]
    | .diamond => [D1, D2, D3, D4]
    | _ => []
  piles := fun a => match a with
    | .p0 => ⟨[], [C6, H5, S4]⟩
    | .p1 => ⟨[], [S6, D5]⟩
    | _ => ⟨[], []⟩
  stock := restB
  waste := []
  drawStep := 1

/-- The twin-kill endpoint: `5♦` founded, `5♥` buried under `4♠`. -/
def vB : State where
  found := fun s => match s with
    | .heart => [H1, H2, H3, H4]
    | .diamond => [D1, D2, D3, D4, D5]
    | _ => []
  piles := fun a => match a with
    | .p0 => ⟨[], [C6, H5, S4]⟩
    | .p1 => ⟨[], [S6]⟩
    | _ => ⟨[], []⟩
  stock := restB
  waste := []
  drawStep := 1

theorem sB_wf : sB.WF :=
  ⟨by
     intro s
     cases s
     · exact ⟨0, by decide⟩
     · exact ⟨5, by decide⟩
     · exact ⟨4, by decide⟩
     · exact ⟨0, by decide⟩,
   by intro a; cases a <;> decide,
   by intro c _; rcases c with ⟨s, r⟩; cases s <;> cases r <;> decide,
   by decide⟩

theorem uB_wf : uB.WF :=
  ⟨by
     intro s
     cases s
     · exact ⟨0, by decide⟩
     · exact ⟨4, by decide⟩
     · exact ⟨4, by decide⟩
     · exact ⟨0, by decide⟩,
   by intro a; cases a <;> decide,
   by intro c _; rcases c with ⟨s, r⟩; cases s <;> cases r <;> decide,
   by decide⟩

theorem uB0_wf : uB0.WF :=
  ⟨by
     intro s
     cases s
     · exact ⟨0, by decide⟩
     · exact ⟨4, by decide⟩
     · exact ⟨4, by decide⟩
     · exact ⟨0, by decide⟩,
   by intro a; cases a <;> decide,
   by intro c _; rcases c with ⟨s, r⟩; cases s <;> cases r <;> decide,
   by decide⟩

theorem vB_wf : vB.WF :=
  ⟨by
     intro s
     cases s
     · exact ⟨0, by decide⟩
     · exact ⟨4, by decide⟩
     · exact ⟨5, by decide⟩
     · exact ⟨0, by decide⟩,
   by intro a; cases a <;> decide,
   by intro c _; rcases c with ⟨s, r⟩; cases s <;> cases r <;> decide,
   by decide⟩

theorem pullB : State.step sB (Move.foundToTab H5 (Sum.inr C6)) = some uB := by
  rw [step_foundToTab_splice (by decide) (by decide)]
  congr 1
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) rfl rfl rfl
  · cases σ <;> decide
  · cases a <;> decide

theorem slideB : State.step uB (Move.tabToTab S4 (Sum.inr H5)) = some uB0 := by
  have hph : uB.pileHolding S4 = some Anchor.p1 := by decide
  have hcp : uB.canPlace S4 (Sum.inr H5) = true := by decide
  have hfrom : fromCard S4 (uB.piles Anchor.p1).faceUp = [S4] := by decide
  have hbelow : below S4 (uB.piles Anchor.p1).faceUp = [S6, D5] := by decide
  rw [step_tabToTab_eq]
  simp only [hph, hcp, hfrom, hbelow, ite_true]
  congr 1
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) rfl rfl rfl
  · cases σ <;> decide
  · cases a <;> decide

theorem slideB_back : State.step uB0 (Move.tabToTab S4 (Sum.inr D5)) = some uB := by
  have hph : uB0.pileHolding S4 = some Anchor.p0 := by decide
  have hcp : uB0.canPlace S4 (Sum.inr D5) = true := by decide
  have hfrom : fromCard S4 (uB0.piles Anchor.p0).faceUp = [S4] := by decide
  have hbelow : below S4 (uB0.piles Anchor.p0).faceUp = [C6, H5] := by decide
  rw [step_tabToTab_eq]
  simp only [hph, hcp, hfrom, hbelow, ite_true]
  congr 1
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) rfl rfl rfl
  · cases σ <;> decide
  · cases a <;> decide

theorem legB : CargoLeg uB uB0 :=
  ⟨S4, Sum.inr H5, slideB, reversible_mirrorW slideB slideB_back⟩

theorem pathB : CargoPath uB uB0 := Steps.cons legB (Steps.refl uB0)

theorem uB_live_D5 : CanRaiseS uB D5 :=
  (canRaiseSB_iff uB_wf).mp (by decide)

theorem raiseB : State.step uB0 (Move.tabToFound D5) = some vB := by
  rw [step_tabToFound_splice (k := Anchor.p1) (by decide) (by decide)]
  congr 1
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) rfl rfl rfl
  · cases σ <;> decide
  · cases a <;> decide

theorem playB : RaiseSSeqLicensed uB [D5] vB :=
  RaiseSSeqLicensed.cons (RaiseSSeqLicensed.nil uB) uB_live_D5 pathB raiseB

theorem hnoB : ∀ d ∈ [D5], d.suit ≠ H5.suit := by
  intro d hd
  rw [List.mem_singleton] at hd
  subst hd
  decide

/-- **The counter's `5♥` is dead at the twin-kill endpoint.** -/
theorem vB_dead_H5 : ¬ CanRaiseS vB H5 := by
  intro h
  have hSB : canRaiseSB vB H5 = true := (canRaiseSB_iff vB_wf).mpr h
  have hfalse : canRaiseSB vB H5 = false := by decide
  rw [hfalse] at hSB
  exact Bool.noConfusion hSB

/-- **The twin letter is not revivable at the source** (it is buried under
`4♠`, and `5♥` is on the foundation, so the twin-top disjunct is unavailable). -/
theorem sB_dead_D5 : ¬ CanRaiseS sB D5 := by
  intro h
  have hSB : canRaiseSB sB D5 = true := (canRaiseSB_iff sB_wf).mpr h
  have hfalse : canRaiseSB sB D5 = false := by decide
  rw [hfalse] at hSB
  exact Bool.noConfusion hSB

/-- `5♦` is not vanilla-raisable at the landing (it is buried under `4♠`). -/
theorem uB_not_vanilla_D5 : ¬ CanRaise uB D5 := by
  rintro ⟨-, a, hpa, -⟩
  have hnone : uB.pileOfTop D5 = none := by decide
  rw [hnone] at hpa
  cases hpa

/-- **The landing's spectrum is exactly the twin pair `{5♥, 5♦}`.** -/
theorem uB_spectrum : ∀ c : Card, (c = H5 ∨ c = D5) ↔ CanRaiseS uB c := by
  intro c
  constructor
  · rintro (rfl | rfl)
    · exact (canRaiseSB_iff uB_wf).mp (by decide)
    · exact uB_live_D5
  · intro hc
    have hSB : canRaiseSB uB c = true := (canRaiseSB_iff uB_wf).mpr hc
    rcases c with ⟨σ, r⟩
    cases σ <;> cases r <;>
      first
        | decide
        | (exfalso; revert hSB; decide)

theorem fork_uB : Fork uB :=
  ⟨uB, H5, RevEqW_refl uB,
    forkWitness_of_spectrum (by
      intro c
      rw [show H5.twin = D5 from rfl]
      exact uB_spectrum c) uB_not_vanilla_D5⟩

/-- The pull source and the landing are orbit-mates. -/
theorem orbit_sB_uB : sameOrbitSetoid.r sB uB := by
  have hrev : reversibleAtW sB (Move.foundToTab H5 (Sum.inr C6)) :=
    reversible_mirrorW pullB (step_tabToFound_of_foundToTab sB_wf pullB)
  exact sameOrbitSetoid.iseqv.symm
    (shufflePlayW_revEqW (Walk.cons hrev pullB (Walk.nil uB)))

/-- **Board B, the twin kill: the conclusion holds through the `Fork s` arm.** -/
theorem fork_sB : Fork sB := by
  obtain ⟨F, x, hF, hw⟩ := fork_uB
  exact ⟨F, x, sameOrbitSetoid.iseqv.trans orbit_sB_uB hF, hw⟩

/-- **Board B, the theorem's conclusion.**  `c = 5♥` is dead at the endpoint,
`4♠` is not raisable, `CanRaiseS sB 5♦` fails — but the disjunction survives
through `Fork sB`. -/
theorem counter_board_twin_kill :
    (∃ v', RaiseSSeqLicensed sB (playWord (sortByRank [D5])) v' ∧
      RungLe sB v' ∧ RungLe uB v') ∨ Fork sB :=
  Or.inr fork_sB

/-! ### §5.3 Board C — the twin present and revivable (Case A) -/

def placedC : List Card :=
  [H1, H2, H3, H4, H5, D1, D2, D3, D4, S6, D5, C6]

def restC : List Card :=
  Card.universe.filter (fun x => decide (x ∉ placedC))

/-- The pull source: `5♥` founded, `5♦` exposed on `6♠`. -/
def sC : State where
  found := fun s => match s with
    | .heart => [H1, H2, H3, H4, H5]
    | .diamond => [D1, D2, D3, D4]
    | _ => []
  piles := fun a => match a with
    | .p0 => ⟨[], [C6]⟩
    | .p1 => ⟨[], [S6, D5]⟩
    | _ => ⟨[], []⟩
  stock := restC
  waste := []
  drawStep := 1

def uC : State where
  found := fun s => match s with
    | .heart => [H1, H2, H3, H4]
    | .diamond => [D1, D2, D3, D4]
    | _ => []
  piles := fun a => match a with
    | .p0 => ⟨[], [C6, H5]⟩
    | .p1 => ⟨[], [S6, D5]⟩
    | _ => ⟨[], []⟩
  stock := restC
  waste := []
  drawStep := 1

def vC : State where
  found := fun s => match s with
    | .heart => [H1, H2, H3, H4]
    | .diamond => [D1, D2, D3, D4, D5]
    | _ => []
  piles := fun a => match a with
    | .p0 => ⟨[], [C6, H5]⟩
    | .p1 => ⟨[], [S6]⟩
    | _ => ⟨[], []⟩
  stock := restC
  waste := []
  drawStep := 1

theorem sC_wf : sC.WF :=
  ⟨by
     intro s
     cases s
     · exact ⟨0, by decide⟩
     · exact ⟨5, by decide⟩
     · exact ⟨4, by decide⟩
     · exact ⟨0, by decide⟩,
   by intro a; cases a <;> decide,
   by intro c _; rcases c with ⟨s, r⟩; cases s <;> cases r <;> decide,
   by decide⟩

theorem uC_wf : uC.WF :=
  ⟨by
     intro s
     cases s
     · exact ⟨0, by decide⟩
     · exact ⟨4, by decide⟩
     · exact ⟨4, by decide⟩
     · exact ⟨0, by decide⟩,
   by intro a; cases a <;> decide,
   by intro c _; rcases c with ⟨s, r⟩; cases s <;> cases r <;> decide,
   by decide⟩

theorem vC_wf : vC.WF :=
  ⟨by
     intro s
     cases s
     · exact ⟨0, by decide⟩
     · exact ⟨4, by decide⟩
     · exact ⟨5, by decide⟩
     · exact ⟨0, by decide⟩,
   by intro a; cases a <;> decide,
   by intro c _; rcases c with ⟨s, r⟩; cases s <;> cases r <;> decide,
   by decide⟩

theorem pullC : State.step sC (Move.foundToTab H5 (Sum.inr C6)) = some uC := by
  rw [step_foundToTab_splice (by decide) (by decide)]
  congr 1
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) rfl rfl rfl
  · cases σ <;> decide
  · cases a <;> decide

theorem uC_live_D5 : CanRaiseS uC D5 :=
  (canRaiseSB_iff uC_wf).mp (by decide)

theorem raiseC : State.step uC (Move.tabToFound D5) = some vC := by
  rw [step_tabToFound_splice (k := Anchor.p1) (by decide) (by decide)]
  congr 1
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) rfl rfl rfl
  · cases σ <;> decide
  · cases a <;> decide

theorem playC : RaiseSSeqLicensed uC [D5] vC :=
  RaiseSSeqLicensed.cons (RaiseSSeqLicensed.nil uC) uC_live_D5
    (Steps.refl uC) raiseC

theorem hnoC : ∀ d ∈ [D5], d.suit ≠ H5.suit := by
  intro d hd
  rw [List.mem_singleton] at hd
  subst hd
  decide

theorem uC_live_H5 : CanRaiseS uC H5 :=
  (canRaiseSB_iff uC_wf).mp (by decide)

/-- **Board C: the twin is present and revivable at the source; `c` survives
at the endpoint, so Case A closes it.** -/
theorem counter_board_twin_replay :
    ∃ v', RaiseSSeqLicensed sC (playWord (sortByRank [D5])) v' ∧
      RungLe sC v' ∧ RungLe uC v' :=
  pull_case_of_live sC_wf pullC playC (RungMono.rungAt_le playC) hnoC
    ((canRaiseSB_iff vC_wf).mp (by decide))

/-- `CanRaiseS sC 5♦`: the twin letter is exposed at the source (the hypothesis
the replay route needs). -/
theorem sC_live_D5 : CanRaiseS sC D5 :=
  (canRaiseSB_iff sC_wf).mp (by decide)

end PullTwinBoard

#print axioms OneColourClosure.pull_rung_succ
#print axioms OneColourClosure.pull_case_of_live
#print axioms OneColourClosure.twin_mem_of_dead
#print axioms OneColourClosure.orbit_source_block
#print axioms OneColourClosure.lock_contradiction
#print axioms OneColourClosure.pull_case_noTwin
#print axioms OneColourClosure.pull_case_or_twin_dead
#print axioms OneColourClosure.pull_case_of_dead_twin_fork
#print axioms PullTwinBoard.sA_wf
#print axioms PullTwinBoard.counter_board_literal
#print axioms PullTwinBoard.vA_dead_H5
#print axioms PullTwinBoard.sB_wf
#print axioms PullTwinBoard.pullB
#print axioms PullTwinBoard.slideB
#print axioms PullTwinBoard.playB
#print axioms PullTwinBoard.vB_dead_H5
#print axioms PullTwinBoard.sB_dead_D5
#print axioms PullTwinBoard.uB_not_vanilla_D5
#print axioms PullTwinBoard.uB_spectrum
#print axioms PullTwinBoard.fork_uB
#print axioms PullTwinBoard.fork_sB
#print axioms PullTwinBoard.counter_board_twin_kill
#print axioms PullTwinBoard.counter_board_twin_replay
#print axioms PullTwinBoard.sC_live_D5
