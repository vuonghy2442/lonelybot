import Orig2.ForkFrontier
import Orig2.ForkNoSelf
import Orig2.ForkRungGe
import Orig2.ForkRungGePair

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkJoint — the joint strong induction over shortest-play length

READ-ONLY scratch card.  No source file is modified; nothing is committed.
Zero `sorry`, zero `Classical.choice`, zero `native_decide`; `#print axioms`
battery at the tail.

## The bundle

    JointClause F c  :=  ¬ CanRaise F c
                       ∧ (∀ e, CanRaiseS F e → e.suit = c.suit ∨ e.suit = c.twin.suit)
                       ∧ F.nextUp c.twin = true

i.e. `SplitBlock` ∧ `SplitContainment` ∧ `SplitTwinRungPin`, read at ONE split
bottom `F`.  `JointUpTo n` is the graded form: every valley split of a witness
play of length `≤ n` satisfies it; `JointAll := ∀ n, JointUpTo n`.

## What is proved

* `segment_shortest` — **every sub-play of a shortest play is shortest between
  its own endpoints** (splicing: replacing a segment by a shorter play between
  the same endpoints would shorten `ρ`).  This is the instrument that makes a
  strong induction on `ρ.length` usable at all: `SplitHyp` demands the
  shortest-play conjunct.

* `splitHyp_free_head` — **the shift lemma**: if the split's `pre` begins with
  a free letter, the play from the state *after* that letter to `v` is again a
  `SplitHyp`, with the SAME bottom `F`, the SAME `c d b post tail`, and a
  STRICTLY shorter play.  So the three clauses at `F` are inherited from the
  shorter play.

* `jointAll_of_base` — **the strong induction**: `Nat.strongRecOn` on
  `ρ.length`; the step either applies the IH directly (shorter play), or strips
  a free head (`splitHyp_free_head`) and applies the IH at the shorter play, or
  lands in the BASE case: `pre = []` or `pre`'s head is non-free.  Hence

      (∀ n, JointBase n) → JointAll.

* `jointAll_iff_jointBase` — the reduction is EXACT: `JointAll` and the base
  bundle are equivalent (the base is a restriction of the bundle).  So the
  joint strong induction is a *reparametrisation*: it consumes every split
  whose `pre` has a free head and leaves exactly the splits that begin at the
  pull.  **The base case is where the induction cannot fire** — see the report
  `Temp/Joint_Report.md` for the exact missing construction.

* `jointBase_of_standing` — the base bundle is not a strengthening of the
  campaign: it follows from `SplitLivePair` + `MountainSplit` + `TailCovers`
  (the standing inputs of the block lane), because those give `SplitBlock`
  (`NoSelfKit.splitBlock_of_livePair_mountain`), the pin
  (`RungGe.splitTwinRungPin_of_splitLivePair`) and the containment
  (`splitContainment_of_livePair_block`).

* `splitHyp_length_eq` / `no_shift_of_pre_nil` — **the obstruction, proved.**
  A split's play length is `|pre| + |post| + |tail| + 2`, so a `pre = []` split
  admits NO strictly shorter split with the same bottom data.  At `pre = []` the
  induction provably cannot fire.

* `TailCoversHead` / `jointBase_of_head_cover` — **the sharp residual**: the
  base bundle follows from `SplitLivePair` + `NoEmptyTail` (both already in the
  tree) + the cover half `CoveredAt F c` demanded ONLY at pull-first splits.
  `tailCovers_of_head_cover` turns that back into the unrestricted
  `BlockKit.TailCovers`, so the joint induction really does discharge the
  general cover half from its pull-first restriction.

* `BaseTransfer` / `jointAll_of_transfer` — the exact IH shape a base case
  would need (a shorter split plus an implication from ITS bundle instance),
  named as a `def`.  Nothing in the tree produces it; the shift lemma is the
  only instance and it needs a free head in `pre`.

* `satDifferForkWF_of_jointAll` — the campaign: `JointAll` +
  `ValleyElim.ShortestPlayExists` give `SatDifferForkWF`.

## What is NOT proved

The base bundle itself.  Measured (`Temp/Joint_probe.py`, 281 census splits on
the 20 named/CutSep classes): `pre = []` 31, `pre` head a pull 232, `pre` head
free 18.  The induction fires on 6.4% of the measured splits; the remaining
93.6% is exactly the base, i.e. the block lane's cover obligation at pull-first
splits.  See `Temp/Joint_Report.md`.
-/

namespace JointKit

open SplitKit

/-! ## §1. The bundle -/

/-- **The three clauses at one bottom.**  `SplitBlock` ∧ `SplitContainment` ∧
`SplitTwinRungPin`, read at the split bottom `F` with pull card `c`. -/
def JointClause (F : State) (c : Card) : Prop :=
  ¬ CanRaise F c ∧
    (∀ e : Card, CanRaiseS F e → e.suit = c.suit ∨ e.suit = c.twin.suit) ∧
    F.nextUp c.twin = true

/-- **The graded bundle.**  Every valley split of a witness play of length
`≤ n` satisfies the three clauses at its bottom. -/
def JointUpTo (n : Nat) : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    ρ.length ≤ n →
    SplitHyp u v ρ F left right c d b pre post tail →
    JointClause F c

/-- **The bundle**: `JointUpTo` at every length. -/
def JointAll : Prop := ∀ n, JointUpTo n

/-- **The base bundle** — the bundle restricted to the splits the induction
cannot shift: `pre = []`, or `pre` whose head is not free. -/
def JointBase (n : Nat) : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    ρ.length ≤ n →
    SplitHyp u v ρ F left right c d b pre post tail →
    (pre = [] ∨ ∃ (m : Move) (pre₂ : List Move), pre = m :: pre₂ ∧
      ¬ ValleyElim.FreeMove m) →
    JointClause F c

/-! ## §2. Every sub-play of a shortest play is shortest -/

/-- **SUB-PLAY SHORTESTNESS.**  If `ρ` is a shortest witness play `u → v`, and
`ρ = α ++ seg ++ β` with `seg : A → T`, then `seg` is shortest between `A` and
`T`: a shorter play `seg'` would splice into `α ++ seg' ++ β`, a shorter
witness play `u → v`.

This is the row that lets a strong induction on `ρ.length` reach the
split data of a shifted play: `SplitHyp` demands shortestness of its own play,
and shortestness is inherited by every segment. -/
theorem segment_shortest {u v : State} {ρ α seg β : List Move}
    {A T : State}
    (hplay : ShufflePlayW u ρ v) (hρ : ρ = α ++ seg ++ β)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length)
    (hα : ShufflePlayW u α A) (hseg : ShufflePlayW A seg T) :
    ∀ seg' : List Move, ShufflePlayW A seg' T → seg.length ≤ seg'.length := by
  intro seg' hseg'
  -- split the original play at `α` and at `α ++ seg`
  have hρ1 : ρ = (α ++ seg) ++ β := by
    rw [hρ, List.append_assoc]
  obtain ⟨T₁, hαseg, hβ⟩ := ValleyElim.ShufflePlayW_split hplay _ _ hρ1
  obtain ⟨A₁, hα₁, hseg₁⟩ := ValleyElim.ShufflePlayW_split hαseg α seg rfl
  -- determinism of the run fixes the segment endpoints
  have hA : A₁ = A := by
    have h1 := Walk_run _ hα₁
    have h2 := Walk_run _ hα
    exact Option.some.inj (h1.symm.trans h2)
  subst hA
  have hT : T₁ = T := by
    have h1 := Walk_run _ hseg₁
    have h2 := Walk_run _ hseg
    exact Option.some.inj (h1.symm.trans h2)
  subst hT
  -- splice the shorter segment
  have hsplice : ShufflePlayW u (α ++ seg' ++ β) v := by
    have h1 : ShufflePlayW u (α ++ (seg' ++ β)) v :=
      ShufflePlayW_append hα (ShufflePlayW_append hseg' hβ)
    simpa [List.append_assoc] using h1
  have hlen := hmin (α ++ seg' ++ β) hsplice
  rw [hρ] at hlen
  simp only [List.length_append] at hlen ⊢
  omega

/-! ## §3. The shift lemma: strip a free head of `pre` -/

/-- **THE SHIFT LEMMA.**  Let a split have `pre = m :: pre₂` with `m` free.
Then `m` is a legal step from `u` to some `A''`, and the play from `A''` on is
again a `SplitHyp` with the SAME bottom `F`, the same `c d b post tail`, and a
STRICTLY shorter move list.

Concretely: `pre` is a free prefix, so `A''` is saturated, and the split data
at `F` is unchanged — the bundle at `F` is thereby inherited from the shorter
play. -/
theorem splitHyp_free_head
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail)
    {m : Move} {pre₂ : List Move} (hpre : pre = m :: pre₂)
    (hm : ValleyElim.FreeMove m) :
    ∃ (A'' : State) (ρ'' : List Move),
      ρ''.length < ρ.length ∧
      SplitHyp A'' v ρ'' F (pre₂ ++ Move.foundToTab c b :: post) right
        c d b pre₂ post tail := by
  obtain ⟨huwf, hsu, hsv, hplay, hsplitAt, hmin, hρ, hleft, hright, hshape,
    hfree, hrightShape⟩ := h
  -- the left leg begins with the free letter
  have hshape' : left = m :: (pre₂ ++ Move.foundToTab c b :: post) := by
    rw [hshape, hpre]; rfl
  have hleft' : ShufflePlayW u (m :: (pre₂ ++ Move.foundToTab c b :: post)) F :=
    hshape' ▸ hleft
  obtain ⟨s₁, hrev, hstep, hrest⟩ := Bubble.walk_cons_inv hleft'
  -- the state after the free head
  have hsingle : ShufflePlayW u [m] s₁ := Walk.cons hrev hstep (Walk.nil s₁)
  have hsingleFree : ∀ x ∈ [m], ValleyElim.FreeMove x := by
    intro x hx
    rw [List.mem_singleton] at hx
    exact hx ▸ hm
  have hsat : SSaturated s₁ :=
    ValleyElim.ssaturated_free_prefix hsingle hsingleFree huwf hsu
  have hwf : s₁.WF := step_wf huwf hstep
  -- the shifted play
  have hplay'' : ShufflePlayW s₁ ((pre₂ ++ Move.foundToTab c b :: post) ++ right) v :=
    ShufflePlayW_append hrest hright
  -- its own minimality, from the splicing row
  have hρm : ρ = m :: ((pre₂ ++ Move.foundToTab c b :: post) ++ right) := by
    rw [hρ, hshape']
    rfl
  have hmin'' : ∀ ρ' : List Move,
      ShufflePlayW s₁ ρ' v →
      ((pre₂ ++ Move.foundToTab c b :: post) ++ right).length ≤ ρ'.length := by
    intro ρ' hρ'
    refine segment_shortest
      (seg := (pre₂ ++ Move.foundToTab c b :: post) ++ right) (β := [])
      hplay ?_ hmin (Walk.cons hrev hstep (Walk.nil s₁)) hplay'' ρ' hρ'
    rw [hρm]
    simp only [List.singleton_append, List.append_nil]
  refine ⟨s₁, (pre₂ ++ Move.foundToTab c b :: post) ++ right, ?_, ?_⟩
  · rw [hρm]
    simp only [List.length_cons]
    omega
  · exact ⟨hwf, hsat, hsv, hplay'',
      ⟨pre₂ ++ Move.foundToTab c b :: post, right, c, d, b,
        pre₂, post, tail, rfl, hrest, hright, rfl, hfree, hrightShape⟩,
      hmin'', rfl, hrest, hright, rfl, hfree, hrightShape⟩

/-! ## §4. The joint strong induction over the play length -/

/-- **THE JOINT STRONG INDUCTION.**  `Nat.strongRecOn` on `ρ.length`.

At a split of length `n`:
* if `ρ.length < n` the IH applies outright;
* if `pre = m :: pre₂` with `m` free, the shift lemma (`splitHyp_free_head`)
  produces a split at the SAME bottom `F` on a strictly shorter play, and the
  IH gives the three clauses there — i.e. here;
* otherwise the split is in the base bundle `JointBase n` (`pre = []`, or a
  non-free head).

Nothing else is needed: the shift lemma makes the induction step a pure
length descent, and it is exactly the base bundle that the induction CANNOT
reach. -/
theorem jointAll_of_base (hbase : ∀ n, JointBase n) : JointAll := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro u v ρ F left right c d b pre post tail hlen hsplit
      rcases Nat.lt_or_eq_of_le hlen with hlt | heq
      · exact ih ρ.length hlt u v ρ F left right c d b pre post tail
          (Nat.le_refl _) hsplit
      · rcases pre with _ | ⟨m, pre₂⟩
        · exact hbase n u v ρ F left right c d b [] post tail hlen hsplit
            (Or.inl rfl)
        · by_cases hb : ValleyElim.isFreeB m = true
          · have hm : ValleyElim.FreeMove m := ValleyElim.isFreeB_eq_true_iff.mp hb
            obtain ⟨A'', ρ'', hlt', hsplit'⟩ :=
              splitHyp_free_head hsplit rfl hm
            have hltn : ρ''.length < n := by omega
            exact ih ρ''.length hltn A'' v ρ'' F
              (pre₂ ++ Move.foundToTab c b :: post) right c d b pre₂ post tail
              (Nat.le_refl _) hsplit'
          · have hm : ¬ ValleyElim.FreeMove m :=
              fun h => hb (ValleyElim.isFreeB_eq_true_iff.mpr h)
            exact hbase n u v ρ F left right c d b (m :: pre₂) post tail hlen
              hsplit (Or.inr ⟨m, pre₂, rfl, hm⟩)

/-- **THE REDUCTION IS EXACT.**  The joint strong induction turns `JointAll`
into its base restriction and back; it therefore neither proves the bundle nor
weakens it.  The base case `pre = [] ∨ pre.head non-free` is the exact
frontier of the induction. -/
theorem jointAll_iff_jointBase : JointAll ↔ ∀ n, JointBase n := by
  constructor
  · intro h n u v ρ F left right c d b pre post tail hlen hsplit _
    exact h n u v ρ F left right c d b pre post tail hlen hsplit
  · exact jointAll_of_base

/-- The bundle at an exact length (the form the report quotes). -/
theorem jointAt_length (h : JointAll) (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move)
    (hsplit : SplitHyp u v ρ F left right c d b pre post tail) :
    JointClause F c :=
  h ρ.length u v ρ F left right c d b pre post tail (Nat.le_refl _) hsplit

/-! ## §5. The bundle's three projections -/

/-- `JointAll` gives `SplitKit.SplitBlock`. -/
theorem splitBlock_of_jointAll (h : JointAll) : SplitBlock :=
  fun u v ρ F left right c d b pre post tail hh =>
    (jointAt_length h u v ρ F left right c d b pre post tail hh).1

/-- `JointAll` gives `TwinKit.SplitContainment`. -/
theorem splitContainment_of_jointAll (h : JointAll) : TwinKit.SplitContainment :=
  fun u v ρ F left right c d b pre post tail hh =>
    (jointAt_length h u v ρ F left right c d b pre post tail hh).2.1

/-- `JointAll` gives `TwinKit.SplitTwinRungPin`. -/
theorem splitTwinRungPin_of_jointAll (h : JointAll) : TwinKit.SplitTwinRungPin :=
  fun u v ρ F left right c d b pre post tail hh =>
    (jointAt_length h u v ρ F left right c d b pre post tail hh).2.2

/-! ## §6. The base bundle from the campaign's standing inputs -/

/-- **CONTAINMENT FROM THE LIVE PAIR + THE BLOCK.**  `SplitLivePair` confines the
bottom's live set to `{d, d.twin}`; the block upgrades `d = c.twin`
(`splitTwin_of_livePair_block`); hence every S-live card's suit is `c`'s or
`c.twin`'s.  One of the three clauses is therefore not independent of the
other two *given* `SplitLivePair`. -/
theorem splitContainment_of_livePair_block (hl : SplitLivePair) (hb : SplitBlock) :
    TwinKit.SplitContainment := by
  intro u v ρ F left right c d b pre post tail h e he
  have htwin : d = c.twin :=
    splitTwin_of_livePair_block hl hb u v ρ F left right c d b pre post tail h
  rcases ((hl u v ρ F left right c d b pre post tail h) e).mp he with h' | h'
  · exact Or.inr (by rw [h', htwin])
  · exact Or.inl (by rw [h', htwin, card_twin_twin])

/-- The three clauses at one split, from `SplitLivePair` + `SplitBlock`. -/
theorem jointClause_of_livePair_block (hl : SplitLivePair) (hb : SplitBlock)
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail) :
    JointClause F c :=
  ⟨hb u v ρ F left right c d b pre post tail h,
    splitContainment_of_livePair_block hl hb
      u v ρ F left right c d b pre post tail h,
    RungGe.splitTwinRungPin_of_splitLivePair hl
      u v ρ F left right c d b pre post tail h⟩

/-- **THE BASE BUNDLE IS NOT A STRENGTHENING.**  It follows from the standing
inputs of the block lane: `SplitLivePair` + the mountain split + the cover
half `BlockKit.TailCovers` give `SplitBlock`
(`NoSelfKit.splitBlock_of_livePair_mountain`), whence all three clauses.  The
joint induction therefore loses nothing: its frontier is implied by the
campaign's own residual set. -/
theorem jointBase_of_standing (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hcov : BlockKit.TailCovers) : ∀ n, JointBase n := by
  intro n u v ρ F left right c d b pre post tail _ hsplit _
  exact jointClause_of_livePair_block hl
    (NoSelfKit.splitBlock_of_livePair_mountain hl hms hcov) hsplit

/-! ## §7. Why the induction stops: the base is a genuine minimum -/

/-- **THE LENGTH FORMULA.**  A split's play length is exactly
`|pre| + |post| + |tail| + 2`: the two turn letters plus the three pieces. -/
theorem splitHyp_length_eq
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail) :
    ρ.length = pre.length + post.length + tail.length + 2 := by
  obtain ⟨-, -, -, -, -, -, hρ, -, -, hshape, -, hrightShape⟩ := h
  rw [hρ, hshape, hrightShape]
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- **NO SHORTER PLAY AT THE SAME BOTTOM WHEN `pre = []`.**  Two splits with the
same `F c d b post tail` have lengths differing exactly by `|pre|`.  Hence a
`pre = []` split admits NO strictly shorter split with the same bottom data:
the strong induction provably cannot fire there, and the base case must be
discharged by a different instrument (not by a smaller instance of itself). -/
theorem no_shift_of_pre_nil
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {post tail : List Move}
    (h₁ : SplitHyp u v ρ F left right c d b [] post tail)
    {u₂ v₂ : State} {ρ₂ : List Move} {left₂ right₂ : List Move}
    {pre₂ : List Move}
    (h₂ : SplitHyp u₂ v₂ ρ₂ F left₂ right₂ c d b pre₂ post tail) :
    ρ.length ≤ ρ₂.length := by
  rw [splitHyp_length_eq h₁, splitHyp_length_eq h₂]
  simp only [List.length_nil]
  omega

/-! ## §7b. The SHARP base reduction: the cover half only at pull-first splits -/

/-- **THE THREE CLAUSES AT ONE SPLIT, FROM THE LIVE PAIR AND A *LOCAL* BLOCK.**
No global `SplitBlock` is used: the containment and the pin are read off the
live pair at this split, using the local obstruction only. -/
theorem jointClause_of_livePair_local (hl : SplitLivePair)
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail)
    (hblock : ¬ CanRaise F c) :
    JointClause F c := by
  obtain ⟨-, hSc, hcanD, -⟩ := splitHyp_green h
  have hpair : TwinLivePair F d := hl u v ρ F left right c d b pre post tail h
  have hct : c = d.twin := by
    rcases (hpair c).mp hSc with h' | h'
    · exact absurd (h' ▸ hcanD) hblock
    · exact h'
  have htwin : d = c.twin := by rw [hct, card_twin_twin]
  refine ⟨hblock, ?_, ?_⟩
  · intro e he
    rcases (hpair e).mp he with h' | h'
    · exact Or.inr (by rw [h', htwin])
    · exact Or.inl (by rw [h', htwin, card_twin_twin])
  · exact RungGe.nextUp_twin_of_live (RungGe.canRaiseS_twin_of_livePair hSc hpair)

/-- **`TailCovers` RESTRICTED TO PULL-FIRST SPLITS** — the cover half demanded
only where the joint induction cannot shift the split, i.e. `pre = []` or
`pre` with a non-free head.  Strictly weaker than `BlockKit.TailCovers`. -/
def TailCoversHead : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitHyp u v ρ F left right c d b pre post tail →
    (pre = [] ∨ ∃ (m : Move) (pre₂ : List Move), pre = m :: pre₂ ∧
      ¬ ValleyElim.FreeMove m) →
    post ≠ [] → CoveredAt F c

/-- The full cover half restricts to the pull-first one. -/
theorem tailCoversHead_of_tailCovers (h : BlockKit.TailCovers) : TailCoversHead :=
  fun u v ρ F left right c d b pre post tail hh _ hpost =>
    h u v ρ F left right c d b pre post tail hh hpost

/-- **THE BASE BUNDLE FROM THE RESTRICTED COVER HALF.**  At a base split,
`post = []` is impossible (`BlockKit.NoEmptyTail`); with `post ≠ []` the
restricted cover half gives `CoveredAt F c`, hence `¬ CanRaise F c`
(`not_canRaise_of_covered`), and the live pair supplies the other two clauses
(`jointClause_of_livePair_local`). -/
theorem jointBase_of_head_cover (hl : SplitLivePair)
    (hne : BlockKit.NoEmptyTail) (hhead : TailCoversHead) :
    ∀ n, JointBase n := by
  intro n u v ρ F left right c d b pre post tail _ hsplit hbasecase
  by_cases hpost : post = []
  · exact absurd hpost (hne u v ρ F left right c d b pre post tail hsplit)
  · have hF : F.WF := (splitHyp_green hsplit).1
    exact jointClause_of_livePair_local hl hsplit
      (not_canRaise_of_covered hF
        (hhead u v ρ F left right c d b pre post tail hsplit hbasecase hpost))

/-! ## §8. The campaign chain -/
/-- **THE CAMPAIGN FROM THE BUNDLE.**  The bundle's three projections satisfy
the minimal hypothesis set, so `ShortestPlayExists` finishes
(`TwinKit.satDifferForkWF_of_block_containment_of_pin`). -/
theorem satDifferForkWF_of_jointAll (h : JointAll)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  TwinKit.satDifferForkWF_of_block_containment_of_pin
    (splitBlock_of_jointAll h) (splitContainment_of_jointAll h)
    (splitTwinRungPin_of_jointAll h) hmin

/-- **THE SAME CHAIN THROUGH THE INDUCTION.**  The standing inputs give the
base bundle (`jointBase_of_standing`), the strong induction gives `JointAll`
(`jointAll_of_base`), and the campaign closes.  (A consistency check: this is
the `NoSelfKit.satDifferForkWF_of_livePair_mountain` conclusion, re-derived
through the joint-induction card.) -/
theorem satDifferForkWF_of_standing_via_joint (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hcov : BlockKit.TailCovers) (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  satDifferForkWF_of_jointAll (jointAll_of_base (jointBase_of_standing hl hms hcov))
    hmin

/-- **THE SHARP CHAIN: THE COVER HALF ONLY AT PULL-FIRST SPLITS.**  The
campaign's cover residual is needed only on the splits the joint induction
cannot shift.  Everything else is consumed by the induction. -/
theorem satDifferForkWF_of_head_cover (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hhead : TailCoversHead) (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  satDifferForkWF_of_jointAll
    (jointAll_of_base
      (jointBase_of_head_cover hl
        (SlideFwd.noEmptyTail_of_noSelfSlide hl hms
          (NoSelfKit.emptyTailNoSelfSlide_of_livePair_mountain hl hms))
        hhead))
    hmin

/-- The full cover half is a special case. -/
theorem satDifferForkWF_of_tailCovers_via_joint (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hcov : BlockKit.TailCovers) (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  satDifferForkWF_of_head_cover hl hms (tailCoversHead_of_tailCovers hcov) hmin

/-! ## §8b. The exact IH shape that would close the base case

`BaseTransfer` is the *named* missing construction, in the only form that can
settle a base split: a **strictly shorter split at a (possibly different)
bottom**, together with an implication from ITS bundle instance to ours.  The
shift lemma (`splitHyp_free_head`) is the one instance of that shape the tree
can produce, and it needs a free head in `pre`; `no_shift_of_pre_nil` proves
that at `pre = []` no shorter same-bottom split exists at all. -/

/-- **THE MISSING TRANSFER ROW.**  At a base split (the joint induction cannot
shift it), a strictly shorter split whose bundle instance implies ours.  This
is a named `def`, not an axiom: it records exactly what an induction step in
the base case would have to consume. -/
def BaseTransfer : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitHyp u v ρ F left right c d b pre post tail →
    (pre = [] ∨ ∃ (m : Move) (pre₂ : List Move), pre = m :: pre₂ ∧
      ¬ ValleyElim.FreeMove m) →
    ∃ (u₂ v₂ : State) (ρ₂ : List Move) (F₂ : State) (c₂ : Card)
      (l₂ r₂ : List Move) (d₂ : Card) (b₂ : Base) (p₂ q₂ t₂ : List Move),
      ρ₂.length < ρ.length ∧
      (JointClause F₂ c₂ → JointClause F c) ∧
      SplitHyp u₂ v₂ ρ₂ F₂ l₂ r₂ c₂ d₂ b₂ p₂ q₂ t₂

/-- **THE JOINT INDUCTION WITH A BASE TRANSFER ROW.**  A shorter split plus a
transfer is consumed exactly as the shift lemma is: the IH supplies the shorter
split's bundle instance and the transfer row lands it at `F`. -/
theorem jointAll_of_transfer (htr : BaseTransfer) : JointAll := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro u v ρ F left right c d b pre post tail hlen hsplit
      rcases Nat.lt_or_eq_of_le hlen with hlt | heq
      · exact ih ρ.length hlt u v ρ F left right c d b pre post tail
          (Nat.le_refl _) hsplit
      · rcases pre with _ | ⟨m, pre₂⟩
        · obtain ⟨u₂, v₂, ρ₂, F₂, c₂, l₂, r₂, d₂, b₂, p₂, q₂, t₂,
            hlt', htrans, hsplit₂⟩ :=
            htr u v ρ F left right c d b [] post tail hsplit (Or.inl rfl)
          have hltn : ρ₂.length < n := by omega
          exact htrans (ih ρ₂.length hltn u₂ v₂ ρ₂ F₂ l₂ r₂ c₂ d₂ b₂ p₂ q₂ t₂
            (Nat.le_refl _) hsplit₂)
        · by_cases hb : ValleyElim.isFreeB m = true
          · have hm : ValleyElim.FreeMove m := ValleyElim.isFreeB_eq_true_iff.mp hb
            obtain ⟨A'', ρ'', hlt', hsplit'⟩ := splitHyp_free_head hsplit rfl hm
            have hltn : ρ''.length < n := by omega
            exact ih ρ''.length hltn A'' v ρ'' F
              (pre₂ ++ Move.foundToTab c b :: post) right c d b pre₂ post tail
              (Nat.le_refl _) hsplit'
          · have hm : ¬ ValleyElim.FreeMove m :=
              fun h => hb (ValleyElim.isFreeB_eq_true_iff.mpr h)
            obtain ⟨u₂, v₂, ρ₂, F₂, c₂, l₂, r₂, d₂, b₂, p₂, q₂, t₂,
              hlt', htrans, hsplit₂⟩ :=
              htr u v ρ F left right c d b (m :: pre₂) post tail hsplit
                (Or.inr ⟨m, pre₂, rfl, hm⟩)
            have hltn : ρ₂.length < n := by omega
            exact htrans (ih ρ₂.length hltn u₂ v₂ ρ₂ F₂ l₂ r₂ c₂ d₂ b₂ p₂ q₂ t₂
              (Nat.le_refl _) hsplit₂)

/-- The campaign from a base transfer row. -/
theorem satDifferForkWF_of_transfer (htr : BaseTransfer)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  satDifferForkWF_of_jointAll (jointAll_of_transfer htr) hmin

/-! ## §9. The bundle IS the frontier's three clauses -/
/-- **THE FULL BLOCK FROM THE PULL-FIRST COVER HALF.**  The joint induction
proves the unrestricted `SplitBlock` from the restricted cover clause. -/
theorem splitBlock_of_head_cover (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hhead : TailCoversHead) : SplitBlock :=
  splitBlock_of_jointAll
    (jointAll_of_base
      (jointBase_of_head_cover hl
        (SlideFwd.noEmptyTail_of_noSelfSlide hl hms
          (NoSelfKit.emptyTailNoSelfSlide_of_livePair_mountain hl hms))
        hhead))

/-- **THE UNRESTRICTED COVER HALF, PROVED FROM THE RESTRICTED ONE.**  This is
the induced reduction stated in the frontier's own vocabulary:
`BlockKit.TailCovers` at every split, from `TailCoversHead` at the
pull-first ones. -/
theorem tailCovers_of_head_cover (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hhead : TailCoversHead) : BlockKit.TailCovers :=
  BlockKit.tailCovers_of_splitBlock (splitBlock_of_head_cover hl hms hhead)
/-- **THE BUNDLE'S IDENTITY.**  `JointAll` is exactly the conjunction of the
three frontier residuals of `Orig2/ForkFrontier.lean` — no more, no less. -/
theorem jointAll_iff_parts :
    JointAll ↔ SplitBlock ∧ TwinKit.SplitContainment ∧ TwinKit.SplitTwinRungPin := by
  constructor
  · intro h
    exact ⟨splitBlock_of_jointAll h, splitContainment_of_jointAll h,
      splitTwinRungPin_of_jointAll h⟩
  · rintro ⟨hb, hc, hp⟩ n u v ρ F left right c d b pre post tail hlen hsplit
    exact ⟨hb u v ρ F left right c d b pre post tail hsplit,
      hc u v ρ F left right c d b pre post tail hsplit,
      hp u v ρ F left right c d b pre post tail hsplit⟩

end JointKit

/-! ## §10. Battery — every row; `[]` / `[propext]` / `[propext, Quot.sound]` only -/

#print axioms JointKit.segment_shortest
#print axioms JointKit.splitHyp_free_head
#print axioms JointKit.jointAll_of_base
#print axioms JointKit.jointAll_iff_jointBase
#print axioms JointKit.jointAt_length
#print axioms JointKit.splitBlock_of_jointAll
#print axioms JointKit.splitContainment_of_jointAll
#print axioms JointKit.splitTwinRungPin_of_jointAll
#print axioms JointKit.splitContainment_of_livePair_block
#print axioms JointKit.jointClause_of_livePair_block
#print axioms JointKit.jointBase_of_standing
#print axioms JointKit.splitHyp_length_eq
#print axioms JointKit.no_shift_of_pre_nil
#print axioms JointKit.jointClause_of_livePair_local
#print axioms JointKit.tailCoversHead_of_tailCovers
#print axioms JointKit.jointBase_of_head_cover
#print axioms JointKit.satDifferForkWF_of_jointAll
#print axioms JointKit.satDifferForkWF_of_standing_via_joint
#print axioms JointKit.satDifferForkWF_of_head_cover
#print axioms JointKit.satDifferForkWF_of_tailCovers_via_joint
#print axioms JointKit.jointAll_of_transfer
#print axioms JointKit.satDifferForkWF_of_transfer
#print axioms JointKit.splitBlock_of_head_cover
#print axioms JointKit.tailCovers_of_head_cover
#print axioms JointKit.jointAll_iff_parts
