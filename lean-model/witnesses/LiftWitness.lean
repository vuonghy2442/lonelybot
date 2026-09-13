import Klondike.Bridge

/-! Scratch: `toEngine_lifts` was UNSOUND as stated (draw-1, WF state).
RESOLVED 2026-09-13 by the invariant-layer repair (Repair B).

Witness `stX`: hearts/diamonds/clubs complete, spades at 12 (♠K next).
The model's board seats ♥Q ON ♠K (a legal `canSitOn` edge), so the
model's `pileStack ♠K` is blocked — and ♥Q is immovable (its only
engine exits need heights it can never reach).

The abstract `pileStack ♠K` succeeded with the witness board `bdW`
seating ♥Q on ♣5 — its deal-adjacent neighbor in pile p2 — which
`Board.Fits`'s deal-adjacency clause accepted WITHOUT requiring the
base to be visible or hidden (the buried-base hole).

THE WITNESS IS NOW KILLED: `board_edges`/`Fits` demand a
deal-adjacent base be some pile's `topHidden` or a placed card, and
WF gained `founds_gone`.  `stX` fails WF twice over: (a) its own
board's edge ♥Q→♠K needs ♠K placed-or-boundary (it is: p0's head —
no, depths are 0, so ♠K must be PLACED — it is, on inl p0 — that
edge survives); the KILLER is (b) `founds_gone`: ♥Q is visible with
`heights ♥ = 13 > 11 = toIdx ♥Q`.  So `¬ stX.WF` (below), the
refutation's premise is gone, and the remaining `toEngine_lifts`
sorry is the honest B4 accommodation argument.

The deadness facts below still hold for `stX` as a state (they are
just no longer about a WF state), but the ABSTRACT WIN IS GONE: the
`bdW`-witnessed `eStep` no longer typechecks — `bdW` fails the
strengthened `Fits` (exactly the closed hole) — so the one-move
abstract win no longer exists even as a scratch fact. -/

namespace LiftWitness

abbrev heA : Card := ⟨Suit.heart, Rank.ace⟩
abbrev he2 : Card := ⟨Suit.heart, Rank.two⟩
abbrev he3 : Card := ⟨Suit.heart, Rank.three⟩
abbrev he4 : Card := ⟨Suit.heart, Rank.four⟩
abbrev he5 : Card := ⟨Suit.heart, Rank.five⟩
abbrev he6 : Card := ⟨Suit.heart, Rank.six⟩
abbrev he7 : Card := ⟨Suit.heart, Rank.seven⟩
abbrev he8 : Card := ⟨Suit.heart, Rank.eight⟩
abbrev he9 : Card := ⟨Suit.heart, Rank.nine⟩
abbrev he10 : Card := ⟨Suit.heart, Rank.ten⟩
abbrev heJ : Card := ⟨Suit.heart, Rank.jack⟩
abbrev heQ : Card := ⟨Suit.heart, Rank.queen⟩
abbrev heK : Card := ⟨Suit.heart, Rank.king⟩
abbrev spA : Card := ⟨Suit.spade, Rank.ace⟩
abbrev sp2 : Card := ⟨Suit.spade, Rank.two⟩
abbrev sp3 : Card := ⟨Suit.spade, Rank.three⟩
abbrev sp4 : Card := ⟨Suit.spade, Rank.four⟩
abbrev sp5 : Card := ⟨Suit.spade, Rank.five⟩
abbrev sp6 : Card := ⟨Suit.spade, Rank.six⟩
abbrev sp7 : Card := ⟨Suit.spade, Rank.seven⟩
abbrev sp8 : Card := ⟨Suit.spade, Rank.eight⟩
abbrev sp9 : Card := ⟨Suit.spade, Rank.nine⟩
abbrev sp10 : Card := ⟨Suit.spade, Rank.ten⟩
abbrev spJ : Card := ⟨Suit.spade, Rank.jack⟩
abbrev spQ : Card := ⟨Suit.spade, Rank.queen⟩
abbrev spK : Card := ⟨Suit.spade, Rank.king⟩
abbrev diA : Card := ⟨Suit.diamond, Rank.ace⟩
abbrev di2 : Card := ⟨Suit.diamond, Rank.two⟩
abbrev di3 : Card := ⟨Suit.diamond, Rank.three⟩
abbrev di4 : Card := ⟨Suit.diamond, Rank.four⟩
abbrev di5 : Card := ⟨Suit.diamond, Rank.five⟩
abbrev di6 : Card := ⟨Suit.diamond, Rank.six⟩
abbrev di7 : Card := ⟨Suit.diamond, Rank.seven⟩
abbrev di8 : Card := ⟨Suit.diamond, Rank.eight⟩
abbrev di9 : Card := ⟨Suit.diamond, Rank.nine⟩
abbrev di10 : Card := ⟨Suit.diamond, Rank.ten⟩
abbrev diJ : Card := ⟨Suit.diamond, Rank.jack⟩
abbrev diQ : Card := ⟨Suit.diamond, Rank.queen⟩
abbrev diK : Card := ⟨Suit.diamond, Rank.king⟩
abbrev clA : Card := ⟨Suit.club, Rank.ace⟩
abbrev cl2 : Card := ⟨Suit.club, Rank.two⟩
abbrev cl3 : Card := ⟨Suit.club, Rank.three⟩
abbrev cl4 : Card := ⟨Suit.club, Rank.four⟩
abbrev cl5 : Card := ⟨Suit.club, Rank.five⟩
abbrev cl6 : Card := ⟨Suit.club, Rank.six⟩
abbrev cl7 : Card := ⟨Suit.club, Rank.seven⟩
abbrev cl8 : Card := ⟨Suit.club, Rank.eight⟩
abbrev cl9 : Card := ⟨Suit.club, Rank.nine⟩
abbrev cl10 : Card := ⟨Suit.club, Rank.ten⟩
abbrev clJ : Card := ⟨Suit.club, Rank.jack⟩
abbrev clQ : Card := ⟨Suit.club, Rank.queen⟩
abbrev clK : Card := ⟨Suit.club, Rank.king⟩

def dealX : Deal where
  piles := fun a => match a with
    | .p0 => [he2]
    | .p1 => [sp10, sp4]
    | .p2 => [di10, cl5, heQ]
    | .p3 => [cl10, he3, he4, he5]
    | .p4 => [he10, sp3, sp5, sp6, sp7]
    | .p5 => [sp9, di3, di4, di5, di6, di7]
    | .p6 => [di9, cl2, cl3, cl4, cl6, cl7, cl8]
  stock := [heA, he6, he7, he8, he9, heJ, heK, spA, sp2, sp8, spJ, spQ, spK,
    diA, di2, di8, diJ, diQ, diK, clA, cl9, clJ, clQ, clK]

theorem dealX_wf : dealX.WF := by
  refine ⟨fun a => ?_, by decide, ?_⟩
  · cases a <;> rfl
  · intro i j hi hj heq
    have hlen : ((Anchor.all.flatMap fun a => dealX.piles a) ++ dealX.stock).length = 52 := by
      decide
    rw [hlen] at hi hj
    have hall : ∀ i ∈ List.range 52, ∀ j ∈ List.range 52,
        ((Anchor.all.flatMap fun a => dealX.piles a) ++ dealX.stock)[i]?
          = ((Anchor.all.flatMap fun a => dealX.piles a) ++ dealX.stock)[j]? → i = j := by
      decide
    exact hall i (List.mem_range.mpr hi) j (List.mem_range.mpr hj) heq

/-- The model's board: ♥Q on ♠K; ♠K on p0; the six deal-heads on
their anchors. -/
def bdX : Board where
  topOf := fun b =>
    if b = Sum.inr spK then some heQ
    else if b = Sum.inl Anchor.p0 then some spK
    else if b = Sum.inl Anchor.p1 then some sp10
    else if b = Sum.inl Anchor.p2 then some di10
    else if b = Sum.inl Anchor.p3 then some cl10
    else if b = Sum.inl Anchor.p4 then some he10
    else if b = Sum.inl Anchor.p5 then some sp9
    else if b = Sum.inl Anchor.p6 then some di9
    else none
  inj := by
    intro b₁ b₂ c h₁ h₂
    cases b₁ with
    | inl a =>
        cases b₂ with
        | inl a' =>
            cases a <;> cases a' <;> simp_all
            all_goals exact absurd (h₁.trans h₂.symm) (by decide)
        | inr d =>
            by_cases hd : d = spK
            · rw [if_pos (by simp [hd])] at h₂
              cases a <;> simp_all
              all_goals exact absurd (h₁.trans h₂.symm) (by decide)
            · rw [if_neg (by simp [hd])] at h₂
              simp at h₂
    | inr d =>
        by_cases hd : d = spK
        · rw [if_pos (by simp [hd]), Option.some.injEq] at h₁
          subst h₁
          cases b₂ with
          | inl a' =>
              cases a' <;> simp_all
              all_goals exact absurd (h₂.trans h₁.symm) (by decide)
          | inr d' =>
              by_cases hd' : d' = spK
              · rw [if_pos (by simp [hd']), Option.some.injEq] at h₂
                exact congrArg Sum.inr (hd.trans hd'.symm)
              · rw [if_neg (by simp [hd'])] at h₂
                simp at h₂
        · rw [if_neg (by simp [hd])] at h₁
          simp at h₁

/-- The abstract witness board: ♥Q on its deal-neighbor ♣5 (invisible
in any model reachable sense — the point of the counterexample). -/
def bdW : Board where
  topOf := fun b =>
    if b = Sum.inr cl5 then some heQ
    else if b = Sum.inl Anchor.p0 then some spK
    else if b = Sum.inl Anchor.p1 then some sp10
    else if b = Sum.inl Anchor.p2 then some di10
    else if b = Sum.inl Anchor.p3 then some cl10
    else if b = Sum.inl Anchor.p4 then some he10
    else if b = Sum.inl Anchor.p5 then some sp9
    else if b = Sum.inl Anchor.p6 then some di9
    else none
  inj := by
    intro b₁ b₂ c h₁ h₂
    cases b₁ with
    | inl a =>
        cases b₂ with
        | inl a' =>
            cases a <;> cases a' <;> simp_all
            all_goals exact absurd (h₁.trans h₂.symm) (by decide)
        | inr d =>
            by_cases hd : d = cl5
            · rw [if_pos (by simp [hd])] at h₂
              cases a <;> simp_all
              all_goals exact absurd (h₁.trans h₂.symm) (by decide)
            · rw [if_neg (by simp [hd])] at h₂
              simp at h₂
    | inr d =>
        by_cases hd : d = cl5
        · rw [if_pos (by simp [hd]), Option.some.injEq] at h₁
          subst h₁
          cases b₂ with
          | inl a' =>
              cases a' <;> simp_all
              all_goals exact absurd (h₂.trans h₁.symm) (by decide)
          | inr d' =>
              by_cases hd' : d' = cl5
              · rw [if_pos (by simp [hd']), Option.some.injEq] at h₂
                exact congrArg Sum.inr (hd.trans hd'.symm)
              · rw [if_neg (by simp [hd'])] at h₂
                simp at h₂
        · rw [if_neg (by simp [hd])] at h₁
          simp at h₁

def stX : State where
  deal := dealX
  board := bdX
  heights := fun s => if s = Suit.heart then 13 else if s = Suit.spade then 12 else 13
  depths := fun _ => 0
  stock := ⟨[], 0⟩
  drawStep := 1

/-- KILLED: the witness is no longer WF — `founds_gone` fails on the
visible, foundation-passed ♥Q (toIdx 11 < heights ♥ 13), and the
bdW-seating (♥Q on ♣5) fails the buried-base clause of `Fits` (♣5 is
neither p2's boundary — depths are 0 — nor placed). -/
theorem stX_not_wf : ¬ stX.WF := by
  intro h
  have htrig : heQ.rank.toIdx < stX.heights heQ.suit := by
    have h1 : heQ.rank.toIdx = 11 := rfl
    have h2 : stX.heights heQ.suit = 13 := rfl
    omega
  have hfg := h.founds_gone heQ htrig
  have h1 : stX.isVis heQ = true := by
    show (stX.board.bottomOf heQ).isSome = true
    rw [(Board.bottomOf_eq stX.board heQ (Sum.inr spK)).mpr
      (show stX.board.topOf (Sum.inr spK) = some heQ from rfl)]
    rfl
  rw [hfg.1] at h1
  exact Bool.noConfusion h1

/-- The abstract witness board no longer realizes the projection: the
♥Q→♣5 edge's deal-adjacent justification now needs ♣5 to be some
pile's boundary or placed — it is neither (depths are 0 everywhere,
and bdW seats nothing on ♣5). -/
theorem stX_not_realizedBy_bdW : ¬ (toEngine stX).realizedBy bdW := by
  rintro ⟨hfits, -⟩
  have htop : bdW.topOf (Sum.inr cl5) = some heQ := rfl
  have hleg := hfits (Sum.inr cl5) heQ htop
  have hnd : bdW.bottomOf cl5 = none := by decide
  rcases hleg with ⟨-, -, -, -, hbase⟩ | ⟨his, -⟩
  · rcases hbase with ⟨a', hth⟩ | hpl
    · have hz : (toEngine stX).depths a' = 0 := rfl
      rw [hz] at hth
      simp at hth
    · rw [hnd] at hpl
      simp at hpl
  · rw [hnd] at his
    simp at his

/-! ## The model engine game is dead -/

theorem stX_pileStack_none : ∀ (c : Card), stX.apply (Move.pileStack c) = none := by
  intro c
  rcases c with ⟨⟨cl, p⟩, r⟩
  cases cl <;> cases p <;> cases r <;> rfl

theorem stX_reveal_none : ∀ (c : Card), stX.apply (Move.reveal c) = none := by
  intro c
  rcases c with ⟨⟨cl, p⟩, r⟩
  cases cl <;> cases p <;> cases r <;> rfl

theorem stX_deckPile_none : ∀ (c : Card) (b : Base), stX.apply (Move.deckPile c b) = none := by
  intro c b
  rfl

theorem stX_deckStack_none : ∀ (c : Card), stX.apply (Move.deckStack c) = none := by
  intro c
  rfl

theorem stX_stackPile_none : ∀ (c : Card) (b : Base), stX.apply (Move.stackPile c b) = none := by
  intro c b
  rcases c with ⟨⟨cl, p⟩, r⟩
  cases cl <;> cases p <;> cases r <;>
    (cases b with
     | inl a => cases a <;> rfl
     | inr d => rcases d with ⟨⟨cl', p'⟩, r'⟩ <;> cases cl' <;> cases p' <;> cases r' <;> rfl)

theorem stX_draw_id : stX.apply Move.draw = some stX := rfl

theorem stX_engine_fixed : ∀ (play : List Move) (st' : State),
    (∀ m ∈ play, m.isEngine = true) → stX.run play = some st' → st' = stX := by
  intro play
  induction play with
  | nil =>
      intro st' _ h
      exact (Option.some.inj h).symm
  | cons m ms ih =>
      intro st' heng h
      obtain ⟨s₁, hap, hrest, _⟩ := run_cons_inv h
      have hm := heng m (by simp)
      have hms : ∀ m' ∈ ms, m'.isEngine = true :=
        fun m' hm' => heng m' (List.mem_cons_of_mem _ hm')
      cases m with
      | draw =>
          have hid : s₁ = stX := by
            have hd := apply_draw_iff.mp hap
            rw [hd]
            rfl
          rw [hid] at hrest
          exact ih st' hms hrest
      | pilePile c b => simp [Move.isEngine] at hm
      | pileStack c => rw [stX_pileStack_none c] at hap; simp at hap
      | reveal c => rw [stX_reveal_none c] at hap; simp at hap
      | deckPile c b => rw [stX_deckPile_none c b] at hap; simp at hap
      | deckStack c => rw [stX_deckStack_none c] at hap; simp at hap
      | stackPile c b => rw [stX_stackPile_none c b] at hap; simp at hap

theorem stX_not_solvableEngine : ¬ stX.solvableEngine := by
  rintro ⟨play, heng, st', hrun, hwin⟩
  have hst := stX_engine_fixed play st' heng hrun
  rw [hst] at hwin
  have hf : stX.isWin = false := rfl
  rw [hf] at hwin
  exact Bool.noConfusion hwin

/-! ## The abstract "win" is gone with the hole

Before the repair, `bdW` realized `(toEngine stX)` (the deal-adjacency
clause asked nothing of the base ♣5), and the abstract game won in one
move: `pileStack ♠K` through it.  With the strengthened `Fits`, `bdW`
no longer realizes the projection (see `stX_not_realizedBy_bdW`), and
the model's own board `bdX` cannot witness the step either (♠K is not
a free surface — ♥Q sits on it).  The one-move abstract win no longer
exists, which is exactly the content of the repair. -/

/-! ## The hole is closed (2026-09-13 repair)

The refutation below is the one that HELD before the invariant-layer
repair: with the old `Fits`/`board_edges` (no buried-base condition)
and the old WF (no `founds_gone`), `stX.WF` was provable and these
∀-statements were refuted through it.  Now `stX.WF` is FALSE
(`stX_not_wf` above), so these refutations no longer go through —
`toEngine_lifts`/`engine_iff` are no longer known-unsound, and their
remaining `sorry`s are the honest B4 accommodation work.

What the repair does NOT claim: a proof of the lift.  It only
removes the counterexample: the abstraction's realizing boards are
now honest (deal-adjacent bases are real boundary-or-placed cards),
so the witness boards can no longer be strictly more permissive than
the model's game through buried bases. -/

/-- The old refutation's premise is dead: no WF state of this shape
exists to instantiate the lift with. -/
example : ¬ (stX.WF ∧ stX.drawStep = 1 ∧
    ∃ eplay w, eRun (toEngine stX) eplay w ∧ w.isWin = true ∧ ¬ stX.solvableEngine) := by
  rintro ⟨hwf, -, -, -, -⟩
  exact stX_not_wf hwf

end LiftWitness

#print axioms LiftWitness.stX_not_wf
#print axioms LiftWitness.stX_not_realizedBy_bdW
