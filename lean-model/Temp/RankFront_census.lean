import Temp.RankFront_probe

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Systematic rank-front census — kernel-checked half

Companion to `Temp/RankFront_census.py` (the full enumeration).  Six WF states
are used (T1 is `probeState` from `Temp/RankFront_probe.lean`, reused):

| tag | shape |
|---|---|
| T1 `probeState` | twin pair, one bare (K♥) one covered (K♦ under Q♠) |
| T2 `t2` | twin pair 8♥/8♦ *both* covered (10♦/10♥ beneath) |
| T3 `t3` | chain `10♦ / 9♠ / 8♥` (rank-nested enabling), twin-free |
| T4 `t4` | reveal shape: raising 9♠ flips the hidden 10♥ |
| T5 `t5` | twin-free, two independent piles (9♠/8♥ and J♣/10♦) |
| T6 `t6` | three live cards of the same rank (three bare kings) |

Chronological plays are `P = [σ₁, …, σₙ]` (σ₁ raised first); the `RaiseSSeq`
**word is the reverse** (`Real s P := ∃ z, RaiseSSeq s P.reverse z`).

## Census verdict (full enumeration in the Python file)

| shape | valid / tested |
|---|---|
| rank-front `[c] ++ sortByRank (P.erase c)` | **107 / 107** |
| unsorted front `[c] ++ P.erase c` | 105 / 107 (both failures in T1) |
| rank-sorted play `sortByRank P` | 107 / 107 |
| adjacent rank-swap in context | **13 / 13** |
| bubble-chain intermediate words | **all valid** (0 failures) |

Both unsorted-front failures are in T1 (`P = [K♥,Q♠,K♦], c = K♦` and
`P = [K♦,Q♠,K♥], c = K♥`); the failing step is the second one, with the
*seat/cover* precondition (the cover `Q♠` has only `K♥` and `K♦` as seats, and
one of them is founded).  Kernel-checked cases here: one rank-front success per
state (T1 is `probe_rankfront_exists`), the full T5 bubble chain (all three
words), and the T5 context dependence (the bare swap `[9♠,10♦]` is *impossible*,
yet it is legal after the prefix `8♥`).
-/

namespace OneColourClosure

/-! ## §1. Building blocks -/

def e8H : Card := ⟨Suit.heart, Rank.eight⟩
def e8D : Card := ⟨Suit.diamond, Rank.eight⟩
def e8C : Card := ⟨Suit.club, Rank.eight⟩
def e9S : Card := ⟨Suit.spade, Rank.nine⟩
def e9C : Card := ⟨Suit.club, Rank.nine⟩
def e9H : Card := ⟨Suit.heart, Rank.nine⟩
def eTD : Card := ⟨Suit.diamond, Rank.ten⟩
def eTH : Card := ⟨Suit.heart, Rank.ten⟩
def eJC : Card := ⟨Suit.club, Rank.jack⟩
def eJS : Card := ⟨Suit.spade, Rank.jack⟩
def eKS : Card := ⟨Suit.spade, Rank.king⟩

/-- The foundation map from the four heights. -/
def fndOf (n : Suit → Nat) : Suit → List Card := fun s => (Suit.upCards s).take (n s)

/-- The stock: every card that is neither on a foundation nor in `tab`. -/
def stockOf (n : Suit → Nat) (tab : List Card) : List Card :=
  Card.universe.filter (fun c =>
    !(decide (c ∈ tab)) && Suit.all.all (fun s => !(decide (c ∈ (Suit.upCards s).take (n s)))))

/-- **Chronological realisability**: `P` is a valid play (first card raised
first) iff the reversed word is a `RaiseSSeq` word. -/
def Real (s : State) (P : List Card) : Prop := ∃ z', RaiseSSeq s P.reverse z'

/-! ## §2. T2 — twin pair `8♥ / 8♦`, both covered -/

def f2 : Suit → Nat := fun s =>
  match s with | .spade => 8 | .heart => 7 | .diamond => 7 | .club => 8

def t2 : State where
  found := fndOf f2
  piles := fun a =>
    match a with
    | .p0 => ⟨[], [eTD, e9S, e8H]⟩
    | .p1 => ⟨[], [eTH, e9C, e8D]⟩
    | _ => ⟨[], []⟩
  stock := stockOf f2 [eTD, e9S, e8H, eTH, e9C, e8D]
  waste := []
  drawStep := 1

theorem t2_WF : t2.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    exact ⟨f2 s, rfl⟩
  · intro a
    match a with
    | .p0 => decide
    | .p1 => decide
    | .p2 => decide
    | .p3 => decide
    | .p4 => decide
    | .p5 => decide
    | .p6 => decide
  · intro c _
    rcases c with ⟨su, r⟩
    cases su <;> cases r <;> decide
  · decide

def t2a : State :=
  { t2.setFound e8D.suit (t2.found e8D.suit ++ [e8D]) with
    piles := fun a' =>
      if a' = Anchor.p1 then
        Pile.afterRunRemoved (t2.piles Anchor.p1) (chop (t2.piles Anchor.p1).faceUp)
      else t2.piles a' }

theorem t2_step_8D : State.step t2 (Move.tabToFound e8D) = some t2a :=
  step_tabToFound_splice (by decide) (by decide)

def t2b : State :=
  { t2a.setFound e8H.suit (t2a.found e8H.suit ++ [e8H]) with
    piles := fun a' =>
      if a' = Anchor.p0 then
        Pile.afterRunRemoved (t2a.piles Anchor.p0) (chop (t2a.piles Anchor.p0).faceUp)
      else t2a.piles a' }

theorem t2a_step_8H : State.step t2a (Move.tabToFound e8H) = some t2b :=
  step_tabToFound_splice (by decide) (by decide)

def t2c : State :=
  { t2b.setFound e9S.suit (t2b.found e9S.suit ++ [e9S]) with
    piles := fun a' =>
      if a' = Anchor.p0 then
        Pile.afterRunRemoved (t2b.piles Anchor.p0) (chop (t2b.piles Anchor.p0).faceUp)
      else t2b.piles a' }

theorem t2b_step_9S : State.step t2b (Move.tabToFound e9S) = some t2c :=
  step_tabToFound_splice (by decide) (by decide)

/-- **T2 success**: for `P = [8♥, 9♠, 8♦]`, `c = 8♦`, the rank-front word is
`[8♦, 8♥, 9♠]` (the cover `8♥` follows `c`), and it is legal. -/
theorem t2_rankfront : Real t2 [e8D, e8H, e9S] := by
  have hw : ([e8D, e8H, e9S] : List Card).reverse = [e9S, e8H, e8D] := by decide
  refine ⟨t2c, ?_⟩
  rw [hw]
  exact RaiseSSeq.cons
    (RaiseSSeq.cons
      (RaiseSSeq.cons (RaiseSSeq.nil t2) (Steps.refl t2) t2_step_8D)
      (Steps.refl t2a) t2a_step_8H)
    (Steps.refl t2b) t2b_step_9S

/-! ## §3. T3 — the chain `10♦ / 9♠ / 8♥` (twin-free) -/

def f3 : Suit → Nat := fun s =>
  match s with | .spade => 8 | .heart => 7 | .diamond => 9 | .club => 0

def t3 : State where
  found := fndOf f3
  piles := fun a =>
    match a with
    | .p0 => ⟨[], [eTD, e9S, e8H]⟩
    | _ => ⟨[], []⟩
  stock := stockOf f3 [eTD, e9S, e8H]
  waste := []
  drawStep := 1

theorem t3_WF : t3.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    exact ⟨f3 s, rfl⟩
  · intro a
    match a with
    | .p0 => decide
    | .p1 => decide
    | .p2 => decide
    | .p3 => decide
    | .p4 => decide
    | .p5 => decide
    | .p6 => decide
  · intro c _
    rcases c with ⟨su, r⟩
    cases su <;> cases r <;> decide
  · decide

def t3a : State :=
  { t3.setFound e8H.suit (t3.found e8H.suit ++ [e8H]) with
    piles := fun a' =>
      if a' = Anchor.p0 then
        Pile.afterRunRemoved (t3.piles Anchor.p0) (chop (t3.piles Anchor.p0).faceUp)
      else t3.piles a' }

theorem t3_step_8H : State.step t3 (Move.tabToFound e8H) = some t3a :=
  step_tabToFound_splice (by decide) (by decide)

def t3b : State :=
  { t3a.setFound e9S.suit (t3a.found e9S.suit ++ [e9S]) with
    piles := fun a' =>
      if a' = Anchor.p0 then
        Pile.afterRunRemoved (t3a.piles Anchor.p0) (chop (t3a.piles Anchor.p0).faceUp)
      else t3a.piles a' }

theorem t3a_step_9S : State.step t3a (Move.tabToFound e9S) = some t3b :=
  step_tabToFound_splice (by decide) (by decide)

def t3c : State :=
  { t3b.setFound eTD.suit (t3b.found eTD.suit ++ [eTD]) with
    piles := fun a' =>
      if a' = Anchor.p0 then
        Pile.afterRunRemoved (t3b.piles Anchor.p0) (chop (t3b.piles Anchor.p0).faceUp)
      else t3b.piles a' }

theorem t3b_step_TD : State.step t3b (Move.tabToFound eTD) = some t3c :=
  step_tabToFound_splice (by decide) (by decide)

/-- **T3 success**: the chain `[8♥, 9♠, 10♦]` is already rank-sorted
(rank-front = the play), and all three steps fire, each exposing the next. -/
theorem t3_rankfront : Real t3 [e8H, e9S, eTD] := by
  have hw : ([e8H, e9S, eTD] : List Card).reverse = [eTD, e9S, e8H] := by decide
  refine ⟨t3c, ?_⟩
  rw [hw]
  exact RaiseSSeq.cons
    (RaiseSSeq.cons
      (RaiseSSeq.cons (RaiseSSeq.nil t3) (Steps.refl t3) t3_step_8H)
      (Steps.refl t3a) t3a_step_9S)
    (Steps.refl t3b) t3b_step_TD

/-! ## §4. T4 — the reveal shape -/

def f4 : Suit → Nat := fun s =>
  match s with | .spade => 8 | .heart => 7 | .diamond => 0 | .club => 0

def t4 : State where
  found := fndOf f4
  piles := fun a =>
    match a with
    | .p0 => ⟨[eTH], [e9S, e8H]⟩
    | _ => ⟨[], []⟩
  stock := stockOf f4 [e9S, e8H, eTH]
  waste := []
  drawStep := 1

theorem t4_WF : t4.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    exact ⟨f4 s, rfl⟩
  · intro a
    match a with
    | .p0 => decide
    | .p1 => decide
    | .p2 => decide
    | .p3 => decide
    | .p4 => decide
    | .p5 => decide
    | .p6 => decide
  · intro c _
    rcases c with ⟨su, r⟩
    cases su <;> cases r <;> decide
  · decide

def t4a : State :=
  { t4.setFound e8H.suit (t4.found e8H.suit ++ [e8H]) with
    piles := fun a' =>
      if a' = Anchor.p0 then
        Pile.afterRunRemoved (t4.piles Anchor.p0) (chop (t4.piles Anchor.p0).faceUp)
      else t4.piles a' }

theorem t4_step_8H : State.step t4 (Move.tabToFound e8H) = some t4a :=
  step_tabToFound_splice (by decide) (by decide)

def t4b : State :=
  { t4a.setFound e9S.suit (t4a.found e9S.suit ++ [e9S]) with
    piles := fun a' =>
      if a' = Anchor.p0 then
        Pile.afterRunRemoved (t4a.piles Anchor.p0) (chop (t4a.piles Anchor.p0).faceUp)
      else t4a.piles a' }

theorem t4a_step_9S : State.step t4a (Move.tabToFound e9S) = some t4b :=
  step_tabToFound_splice (by decide) (by decide)

/-- **T4 success**: `[8♥, 9♠]` (rank-front = play) is legal; the second step is a
*commit* raise (it flips the hidden `10♥`), which `RaiseSSeq` allows. -/
theorem t4_rankfront : Real t4 [e8H, e9S] := by
  have hw : ([e8H, e9S] : List Card).reverse = [e9S, e8H] := by decide
  refine ⟨t4b, ?_⟩
  rw [hw]
  exact RaiseSSeq.cons
    (RaiseSSeq.cons (RaiseSSeq.nil t4) (Steps.refl t4) t4_step_8H)
    (Steps.refl t4a) t4a_step_9S

/-! ## §5. T5 — twin-free, two independent piles; the full bubble chain -/

def f5 : Suit → Nat := fun s =>
  match s with | .spade => 8 | .heart => 7 | .diamond => 9 | .club => 10

def t5 : State where
  found := fndOf f5
  piles := fun a =>
    match a with
    | .p0 => ⟨[], [e9S, e8H]⟩
    | .p1 => ⟨[], [eJC, eTD]⟩
    | _ => ⟨[], []⟩
  stock := stockOf f5 [e9S, e8H, eJC, eTD]
  waste := []
  drawStep := 1

theorem t5_WF : t5.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    exact ⟨f5 s, rfl⟩
  · intro a
    match a with
    | .p0 => decide
    | .p1 => decide
    | .p2 => decide
    | .p3 => decide
    | .p4 => decide
    | .p5 => decide
    | .p6 => decide
  · intro c _
    rcases c with ⟨su, r⟩
    cases su <;> cases r <;> decide
  · decide

/-! ### Lane A: `10♦` first -/

def t5a : State :=
  { t5.setFound eTD.suit (t5.found eTD.suit ++ [eTD]) with
    piles := fun a' =>
      if a' = Anchor.p1 then
        Pile.afterRunRemoved (t5.piles Anchor.p1) (chop (t5.piles Anchor.p1).faceUp)
      else t5.piles a' }

theorem t5_step_TD : State.step t5 (Move.tabToFound eTD) = some t5a :=
  step_tabToFound_splice (by decide) (by decide)

def t5b : State :=
  { t5a.setFound e8H.suit (t5a.found e8H.suit ++ [e8H]) with
    piles := fun a' =>
      if a' = Anchor.p0 then
        Pile.afterRunRemoved (t5a.piles Anchor.p0) (chop (t5a.piles Anchor.p0).faceUp)
      else t5a.piles a' }

theorem t5a_step_8H : State.step t5a (Move.tabToFound e8H) = some t5b :=
  step_tabToFound_splice (by decide) (by decide)

def t5bJ : State :=
  { t5b.setFound eJC.suit (t5b.found eJC.suit ++ [eJC]) with
    piles := fun a' =>
      if a' = Anchor.p1 then
        Pile.afterRunRemoved (t5b.piles Anchor.p1) (chop (t5b.piles Anchor.p1).faceUp)
      else t5b.piles a' }

theorem t5b_step_JC : State.step t5b (Move.tabToFound eJC) = some t5bJ :=
  step_tabToFound_splice (by decide) (by decide)

def t5aJ : State :=
  { t5a.setFound eJC.suit (t5a.found eJC.suit ++ [eJC]) with
    piles := fun a' =>
      if a' = Anchor.p1 then
        Pile.afterRunRemoved (t5a.piles Anchor.p1) (chop (t5a.piles Anchor.p1).faceUp)
      else t5a.piles a' }

theorem t5a_step_JC : State.step t5a (Move.tabToFound eJC) = some t5aJ :=
  step_tabToFound_splice (by decide) (by decide)

def t5aJ8 : State :=
  { t5aJ.setFound e8H.suit (t5aJ.found e8H.suit ++ [e8H]) with
    piles := fun a' =>
      if a' = Anchor.p0 then
        Pile.afterRunRemoved (t5aJ.piles Anchor.p0) (chop (t5aJ.piles Anchor.p0).faceUp)
      else t5aJ.piles a' }

theorem t5aJ_step_8H : State.step t5aJ (Move.tabToFound e8H) = some t5aJ8 :=
  step_tabToFound_splice (by decide) (by decide)

/-- The play `[10♦, J♣, 8♥]` is legal. -/
theorem t5_play : Real t5 [eTD, eJC, e8H] := by
  have hw : ([eTD, eJC, e8H] : List Card).reverse = [e8H, eJC, eTD] := by decide
  refine ⟨t5aJ8, ?_⟩
  rw [hw]
  exact RaiseSSeq.cons
    (RaiseSSeq.cons
      (RaiseSSeq.cons (RaiseSSeq.nil t5) (Steps.refl t5) t5_step_TD)
      (Steps.refl t5a) t5a_step_JC)
    (Steps.refl t5aJ) t5aJ_step_8H

/-- **The first rank-swap** `[10♦, J♣, 8♥] → [10♦, 8♥, J♣]` — this is exactly the
rank-front word for `c = 10♦`, and it is legal. -/
theorem t5_swap1 : Real t5 [eTD, e8H, eJC] := by
  have hw : ([eTD, e8H, eJC] : List Card).reverse = [eJC, e8H, eTD] := by decide
  refine ⟨t5bJ, ?_⟩
  rw [hw]
  exact RaiseSSeq.cons
    (RaiseSSeq.cons
      (RaiseSSeq.cons (RaiseSSeq.nil t5) (Steps.refl t5) t5_step_TD)
      (Steps.refl t5a) t5a_step_8H)
    (Steps.refl t5b) t5b_step_JC

/-! ### Lane B: `8♥` first -/

def t5A : State :=
  { t5.setFound e8H.suit (t5.found e8H.suit ++ [e8H]) with
    piles := fun a' =>
      if a' = Anchor.p0 then
        Pile.afterRunRemoved (t5.piles Anchor.p0) (chop (t5.piles Anchor.p0).faceUp)
      else t5.piles a' }

theorem t5_step_8H : State.step t5 (Move.tabToFound e8H) = some t5A :=
  step_tabToFound_splice (by decide) (by decide)

def t5AT : State :=
  { t5A.setFound eTD.suit (t5A.found eTD.suit ++ [eTD]) with
    piles := fun a' =>
      if a' = Anchor.p1 then
        Pile.afterRunRemoved (t5A.piles Anchor.p1) (chop (t5A.piles Anchor.p1).faceUp)
      else t5A.piles a' }

theorem t5A_step_TD : State.step t5A (Move.tabToFound eTD) = some t5AT :=
  step_tabToFound_splice (by decide) (by decide)

def t5ATJ : State :=
  { t5AT.setFound eJC.suit (t5AT.found eJC.suit ++ [eJC]) with
    piles := fun a' =>
      if a' = Anchor.p1 then
        Pile.afterRunRemoved (t5AT.piles Anchor.p1) (chop (t5AT.piles Anchor.p1).faceUp)
      else t5AT.piles a' }

theorem t5AT_step_JC : State.step t5AT (Move.tabToFound eJC) = some t5ATJ :=
  step_tabToFound_splice (by decide) (by decide)

/-- **The second rank-swap** `[10♦, 8♥, J♣] → [8♥, 10♦, J♣]` (the fully sorted
play) is legal.  Together with `t5_play` and `t5_swap1` this shows the whole
bubble chain is a path of *valid* words. -/
theorem t5_swap2 : Real t5 [e8H, eTD, eJC] := by
  have hw : ([e8H, eTD, eJC] : List Card).reverse = [eJC, eTD, e8H] := by decide
  refine ⟨t5ATJ, ?_⟩
  rw [hw]
  exact RaiseSSeq.cons
    (RaiseSSeq.cons
      (RaiseSSeq.cons (RaiseSSeq.nil t5) (Steps.refl t5) t5_step_8H)
      (Steps.refl t5A) t5A_step_TD)
    (Steps.refl t5AT) t5AT_step_JC

/-! ### Context dependence: the bare swap `[9♠, 10♦]` is impossible

`9♠` is buried under `8♥`, and no *reversible* slide fires at `t5` (the one
slide that fires, `9♠` onto `10♦`, is a commit: `9♠` is a pile bottom).  So `9♠`
is never a pile top in the cargo class, and the play `[9♠, 10♦]` cannot start —
while `[8♥, 9♠, 10♦]` (the same swap after the prefix `8♥`) *is* legal. -/

theorem t5_no_revSlide (x : Card) (b : Base) : tabToTabR t5 x b = false := by
  -- only `8♥` (top of p0) and `10♦` (top of p1) can be moved;
  -- `8♥` has no seat, `10♦` has no seat; the buried cards are commits.
  rcases x with ⟨sx, rx⟩
  cases sx <;> cases rx <;> (cases b with
    | inl a => cases a <;> decide
    | inr y => cases y with
      | mk sy ry => cases sy <;> cases ry <;> decide)

theorem t5_no_cargoLeg {v : State} : ¬ CargoLeg t5 v := by
  rintro ⟨x, b, hstep, hrev⟩
  have hR : tabToTabR t5 x b = true :=
    (tabToTabR_iff_reversibleAtW t5_WF x b).mpr hrev
  rw [t5_no_revSlide x b] at hR
  exact absurd hR (by simp)

theorem t5_cargoPath_eq {v : State} (h : CargoPath t5 v) : v = t5 := by
  cases h with
  | refl => rfl
  | cons hl _ => exact absurd hl t5_no_cargoLeg

theorem t5_pileOfTop_9S : t5.pileOfTop e9S = none := by decide

/-- **The bare swap is impossible** (chronological `[9♠, 10♦]`): `9♠` is never a
pile top in the cargo class of `t5`. -/
theorem t5_bare_swap_false : ¬ Real t5 [e9S, eTD] := by
  rintro ⟨z', hz'⟩
  have hw : ([e9S, eTD] : List Card).reverse = [eTD, e9S] := by decide
  rw [hw] at hz'
  cases hz' with
  | cons htail hp hs =>
      cases htail with
      | cons hnil hp2 hs2 =>
          cases hnil
          have hv : _ = t5 := t5_cargoPath_eq hp2
          subst hv
          obtain ⟨-, a, hpa, -⟩ := step_tabToFound_inv hs2
          rw [t5_pileOfTop_9S] at hpa
          exact absurd hpa (by simp)

/-! ## §6. T6 — three live cards of the same rank (three bare kings) -/

def f6 : Suit → Nat := fun s =>
  match s with | .spade => 12 | .heart => 12 | .diamond => 12 | .club => 0

def t6 : State where
  found := fndOf f6
  piles := fun a =>
    match a with
    | .p0 => ⟨[], [eKS]⟩
    | .p1 => ⟨[], [cKH]⟩
    | .p2 => ⟨[], [cKD]⟩
    | _ => ⟨[], []⟩
  stock := stockOf f6 [eKS, cKH, cKD]
  waste := []
  drawStep := 1

theorem t6_WF : t6.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    exact ⟨f6 s, rfl⟩
  · intro a
    match a with
    | .p0 => decide
    | .p1 => decide
    | .p2 => decide
    | .p3 => decide
    | .p4 => decide
    | .p5 => decide
    | .p6 => decide
  · intro c _
    rcases c with ⟨su, r⟩
    cases su <;> cases r <;> decide
  · decide

def t6a : State :=
  { t6.setFound cKD.suit (t6.found cKD.suit ++ [cKD]) with
    piles := fun a' =>
      if a' = Anchor.p2 then
        Pile.afterRunRemoved (t6.piles Anchor.p2) (chop (t6.piles Anchor.p2).faceUp)
      else t6.piles a' }

theorem t6_step_KD : State.step t6 (Move.tabToFound cKD) = some t6a :=
  step_tabToFound_splice (by decide) (by decide)

def t6b : State :=
  { t6a.setFound eKS.suit (t6a.found eKS.suit ++ [eKS]) with
    piles := fun a' =>
      if a' = Anchor.p0 then
        Pile.afterRunRemoved (t6a.piles Anchor.p0) (chop (t6a.piles Anchor.p0).faceUp)
      else t6a.piles a' }

theorem t6a_step_KS : State.step t6a (Move.tabToFound eKS) = some t6b :=
  step_tabToFound_splice (by decide) (by decide)

def t6c : State :=
  { t6b.setFound cKH.suit (t6b.found cKH.suit ++ [cKH]) with
    piles := fun a' =>
      if a' = Anchor.p1 then
        Pile.afterRunRemoved (t6b.piles Anchor.p1) (chop (t6b.piles Anchor.p1).faceUp)
      else t6b.piles a' }

theorem t6b_step_KH : State.step t6b (Move.tabToFound cKH) = some t6c :=
  step_tabToFound_splice (by decide) (by decide)

/-- **T6 success**: three live cards of the same rank; for `P = [K♠, K♥, K♦]`,
`c = K♦`, the rank-front word is `[K♦, K♠, K♥]` (ties keep their order) and it
is legal. -/
theorem t6_rankfront : Real t6 [cKD, eKS, cKH] := by
  have hw : ([cKD, eKS, cKH] : List Card).reverse = [cKH, eKS, cKD] := by decide
  refine ⟨t6c, ?_⟩
  rw [hw]
  exact RaiseSSeq.cons
    (RaiseSSeq.cons
      (RaiseSSeq.cons (RaiseSSeq.nil t6) (Steps.refl t6) t6_step_KD)
      (Steps.refl t6a) t6a_step_KS)
    (Steps.refl t6b) t6b_step_KH

end OneColourClosure

#print axioms OneColourClosure.t2_WF
#print axioms OneColourClosure.t2_rankfront
#print axioms OneColourClosure.t3_WF
#print axioms OneColourClosure.t3_rankfront
#print axioms OneColourClosure.t4_WF
#print axioms OneColourClosure.t4_rankfront
#print axioms OneColourClosure.t5_WF
#print axioms OneColourClosure.t5_play
#print axioms OneColourClosure.t5_swap1
#print axioms OneColourClosure.t5_swap2
#print axioms OneColourClosure.t5_no_revSlide
#print axioms OneColourClosure.t5_bare_swap_false
#print axioms OneColourClosure.t6_WF
#print axioms OneColourClosure.t6_rankfront
