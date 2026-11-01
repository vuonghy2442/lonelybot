import Orig2.ForkBoth

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Temp/SC — the same-card `d = c` branch at a `pre = []` split, and the last
corner of `Pin.BottomNotBothRaisable` (`pre` pull-headed)

READ-ONLY scratch card.  No source edit, no commit.  Zero `sorry`, zero
`Classical.choice`, zero `native_decide`; axiom battery at the tail.

See `Temp/SC_Report.md` for the full account.

## Task 1 (`Both.SameCardNilBlock`, `Orig2/ForkBoth.lean:445`)

`SameCardNilBlock` is **not** a cover obligation.  `splitHyp_green` gives
`CanRaise F d` at every split, so `d = c` already yields `CanRaise F c`; the
conclusion `¬ CanRaise F c` is therefore *false* at any same-card split.  Hence

```text
SameCardNilBlock  ↔  no nil-prefix split has `d = c`
                  ↔  NilPreNoSameCard
                  ↔  the `pre = []` block clause itself
                  ⇐  SplitNe   ⇐  SplitBlock            (all proved, §D)
```

and any counterexample has a nonempty free tail with a cover slide on `c` and
**at least two slides** (`sameCard_counterexample_shape`).  This is exactly the
nil-prefix corner of the tree's existing `SplitKit.SplitNe`; it is not an
independent geometric obligation.

## Task 2 (`Both.BottomNotBothPullPre`, the `pre` pull-headed lane)

§A adds the three missing state rows (a pull preserves every other card's
`seatOf`; a cover survives a pull; a vanilla-raisable non-pulled card at a
landing was already S-live before the pull).  §B turns them into **the backward
walk**: along a raise-free leg, an S-live card at the end is either itself
pulled on the leg, or one of `{y, y.twin}` is covered at the end, or it was
live at the saturated origin.  §C applies the walk at every pull landing of a
split and obtains, *without* any prefix hypothesis,

```text
both x and x.twin vanilla-raisable at the bottom  ⟹  x and x.twin are both
                                                     pulled on the left leg
```

so the raise-free lane of the gated vacuity is exactly the named card residual
`NoBothPulledTwin`, and (given it) `Pin.BottomNotBothRaisable` is exactly the
lane where `left` contains a raise (`LeftRaiseLane`).  As a cross-check the
same walk re-proves `Both.BottomNotBothRaisableNil` (`bottomNotBothRaisableNil_of_walk`).
-/

namespace SC

open SplitKit

/-! ## §A.1  `below`, `pileHolding`, `seatOf` under a pull -/

/-- `below x` ignores a trailing append, provided `x` occurs. -/
theorem below_append_snoc_of_mem {x y : Card} :
    ∀ {l : List Card}, x ∈ l → below x (l ++ [y]) = below x l
  | [], h => absurd h List.not_mem_nil
  | a :: t, h => by
      have h' : x = a ∨ x ∈ t := List.mem_cons.mp h
      rw [List.cons_append, below_cons, below_cons]
      by_cases hax : a = x
      · rw [ite_eq_left hax, ite_eq_left hax]
      · rw [ite_eq_right hax, ite_eq_right hax]
        rcases h' with rfl | h'
        · exact absurd rfl hax
        · exact congrArg (List.cons a) (below_append_snoc_of_mem h')

/-- Membership in a face-up run ignores a trailing append of another card. -/
theorem mem_faceUp_snoc_iff {l : List Card} {x y : Card} (hxy : x ≠ y) :
    x ∈ l ++ [y] ↔ x ∈ l := by
  rw [List.mem_append, List.mem_singleton]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h hxy
  · exact Or.inl

/-- **A PULL DOES NOT MOVE ANY OTHER CARD'S PILE.** -/
theorem pileHolding_pull_ne {A B : State} {c x : Card} {b : Base}
    (hstep : A.step (Move.foundToTab c b) = some B) (hx : x ≠ c) :
    B.pileHolding x = A.pileHolding x := by
  unfold State.pileHolding
  refine SplitKit.firstWhere_congr_local (p := fun a => decide (x ∈ (B.piles a).faceUp))
    (q := fun a => decide (x ∈ (A.piles a).faceUp)) ?_ Anchor.all
  intro a
  have hface := Both.pull_faceUp_cases hstep a
  have hiff : x ∈ (B.piles a).faceUp ↔ x ∈ (A.piles a).faceUp := by
    rcases hface with h | h
    · rw [h]
    · rw [h]; exact mem_faceUp_snoc_iff hx
  by_cases hp : x ∈ (A.piles a).faceUp
  · rw [decide_eq_true (hiff.mpr hp), decide_eq_true hp]
  · rw [decide_eq_false (fun hq => hp (hiff.mp hq)), decide_eq_false hp]

/-- **A PULL PRESERVES THE SEAT OF EVERY OTHER CARD.** -/
theorem seatOf_pull_ne {A B : State} {c x : Card} {b : Base}
    (hstep : A.step (Move.foundToTab c b) = some B) (hx : x ≠ c) :
    seatOf B x = seatOf A x := by
  have hph := pileHolding_pull_ne hstep hx
  unfold seatOf
  rw [hph]
  cases hA : A.pileHolding x with
  | none => rfl
  | some a =>
      have hmem : x ∈ (A.piles a).faceUp := pileHolding_mem hA
      rcases Both.pull_faceUp_cases hstep a with h | h
      · simp only [h]
      · simp only [h, below_append_snoc_of_mem hmem]

/-! ## §A.2  A cover survives a pull -/

/-- A card seated on another card is on the tableau. -/
theorem mem_faceUp_of_seat_inr {st : State} {c y : Card}
    (h : seatOf st c = some (Sum.inr y)) : ∃ a, c ∈ (st.piles a).faceUp := by
  unfold seatOf at h
  cases hph : st.pileHolding c with
  | none => rw [hph] at h; exact absurd h (by simp)
  | some a => exact ⟨a, pileHolding_mem hph⟩

/-- A foundation-top card is on no face-up run. -/
theorem not_faceUp_of_foundTop {st : State} (hwf : st.WF) {c : Card}
    (htop : st.foundTop c.suit = some c) (a : Anchor) :
    c ∉ (st.piles a).faceUp :=
  ((mem_found_unique hwf (lastOf_mem htop)).1 a).2

/-- **A COVER AT A PULL'S ORIGIN IS CARRIED FORWARD.**  The cover card cannot
be the pulled card (`c` is a foundation top just before the pull), so its seat
is untouched. -/
theorem covered_pull_forward {A B : State} {c y : Card} {b : Base}
    (hA : A.WF) (hstep : A.step (Move.foundToTab c b) = some B)
    (hcov : CoveredAt A y) : CoveredAt B y := by
  obtain ⟨d, hd⟩ := hcov
  obtain ⟨c0, htop, hc0, hcp, heq⟩ := step_foundToTab_inv hstep
  rw [hc0] at htop
  have hdc : d ≠ c := by
    intro hdc
    rw [hdc] at hd
    obtain ⟨a, hmem⟩ := mem_faceUp_of_seat_inr hd
    exact not_faceUp_of_foundTop hA htop a hmem
  exact ⟨d, by rw [seatOf_pull_ne hstep hdc]; exact hd⟩

/-- **A COVER IS CARRIED FORWARD ALONG A FREE TAIL** (the twin pair form). -/
theorem covered_forward_free {d y : Card} (hfit : canSitOn d y = true)
    {st st' : State} {γ : List Move} (hplay : ShufflePlayW st γ st')
    (hwf : st.WF) (hfree : ∀ m ∈ γ, ValleyElim.FreeMove m)
    (hcov : seatOf st d = some (Sum.inr y)) :
    seatOf st' d = some (Sum.inr y) ∨ seatOf st' d = some (Sum.inr y.twin) := by
  have hfit' : canSitOn d y.twin.twin = true := by rwa [card_twin_twin]
  have hnk : d.rank ≠ Rank.king := Both.rank_ne_king_of_fit hfit'
  have hinv : seatOf st d = some (Sum.inr y.twin.twin) ∨
      seatOf st d = some (Sum.inr y.twin) := by
    rw [card_twin_twin]; exact Or.inl hcov
  have hres := Both.seat_inv_play hfit' hnk hplay hwf hinv hfree
  rwa [card_twin_twin] at hres

/-- The `CoveredAt` form of the forward carry. -/
theorem covered_mono_free {st st' : State} {γ : List Move} {y : Card}
    (hplay : ShufflePlayW st γ st') (hwf : st.WF)
    (hfree : ∀ m ∈ γ, ValleyElim.FreeMove m) (hcov : CoveredAt st y) :
    CoveredAt st' y ∨ CoveredAt st' y.twin := by
  obtain ⟨d, hd⟩ := hcov
  have hfit : canSitOn d y = true := LiveKit.canSitOn_of_seat hwf hd
  rcases covered_forward_free hfit hplay hwf hfree hd with h | h
  · exact Or.inl ⟨d, h⟩
  · exact Or.inr ⟨d, h⟩

/-! ## §A.3  The backward transfer of the vanilla licence across a pull -/

/-- **THE TWIN CASE OF THE BACKWARD TRANSFER.**  If `c.twin` is vanilla-raisable
at the landing of the pull of `c`, it was S-live just before: the pull either
leaves its pile alone (licence transfers) or appends `c` on top (then `c` would
be the pile top, not `c.twin`). -/
theorem canRaiseS_twin_of_canRaise_landing {A B : State} {c : Card} {b : Base}
    (hA : A.WF) (hstep : A.step (Move.foundToTab c b) = some B)
    (hcanB : CanRaise B c.twin) : CanRaiseS A c.twin := by
  obtain ⟨hnextB, a, hpodB, hseatB⟩ := hcanB
  have htopB : lastOf (B.piles a).faceUp = some c.twin := (pileOfTop_top hpodB).2
  have hnextA : A.nextUp c.twin = true :=
    Both.nextUp_of_step_pull_ne_suit hstep (Suit.twin_ne c.suit) hnextB
  rcases Both.pull_faceUp_cases hstep a with hface | hface
  · have htopA : A.topOf a = some c.twin := by
      show lastOf (A.piles a).faceUp = some c.twin
      rw [← hface]; exact htopB
    have hpodA : A.pileOfTop c.twin = some a := (pileOfTop_eq_some_iff hA).mpr htopA
    have hseatA : chop (A.piles a).faceUp ≠ [] ∨
        ((A.piles a).hidden = [] ∧ c.twin.rank = Rank.king) := by
      rcases hseatB with h | ⟨hh, hk⟩
      · exact Or.inl (by rw [← hface]; exact h)
      · exact Or.inr ⟨by rw [← Both.pull_hidden_eq hstep a]; exact hh, hk⟩
    exact CanRaiseS.now c.twin ⟨hnextA, a, hpodA, hseatA⟩
  · have hlast : lastOf (B.piles a).faceUp = some c := by
      rw [hface]; exact lastOf_snoc
    have hct : c.twin = c := Option.some.inj (htopB.symm.trans hlast)
    exact absurd hct (SplitKit.card_twin_ne c)

/-- **A VANILLA-RAISABLE NON-PULLED CARD WAS ALREADY S-LIVE BEFORE THE PULL.**
`Both.top_case_false` is the `y = c.twin` case of this row with saturation of
the origin appended. -/
theorem canRaiseS_of_canRaise_of_pull {A B : State} {c y : Card} {b : Base}
    (hA : A.WF) (hstep : A.step (Move.foundToTab c b) = some B)
    (hy : y ≠ c) (hcanB : CanRaise B y) : CanRaiseS A y := by
  by_cases hyt : y = c.twin
  · rw [hyt]
    exact canRaiseS_twin_of_canRaise_landing hA hstep (hyt ▸ hcanB)
  · exact LandKit.canRaiseS_of_pull_of_ne_twin hA hstep (CanRaiseS.now y hcanB) hy hyt

/-- The pair form of the forward carry along a free tail. -/
theorem covered_carry_free {st st' : State} {γ : List Move} {y : Card}
    (hplay : ShufflePlayW st γ st') (hwf : st.WF)
    (hfree : ∀ m ∈ γ, ValleyElim.FreeMove m)
    (hcov : CoveredAt st y ∨ CoveredAt st y.twin) :
    CoveredAt st' y ∨ CoveredAt st' y.twin := by
  rcases hcov with hc | hc
  · rcases covered_mono_free hplay hwf hfree hc with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rcases covered_mono_free hplay hwf hfree hc with h | h
    · exact Or.inr h
    · rw [card_twin_twin] at h; exact Or.inl h

/-- The pair form of the forward carry across a pull. -/
theorem covered_carry_pull {A B : State} {c y : Card} {b : Base}
    (hA : A.WF) (hstep : A.step (Move.foundToTab c b) = some B)
    (hcov : CoveredAt A y ∨ CoveredAt A y.twin) :
    CoveredAt B y ∨ CoveredAt B y.twin := by
  rcases hcov with hc | hc
  · exact Or.inl (covered_pull_forward hA hstep hc)
  · exact Or.inr (covered_pull_forward hA hstep hc)

/-! ## §B  The backward walk over a raise-free leg

The dichotomy `canRaise_or_covered` is applied at *every pull landing* on the
way back.  Its vanilla branch is pushed one pull further back
(`canRaiseS_of_canRaise_of_pull`), its covered branch is carried forward to the
end of the leg (`covered_pull_forward` + `covered_mono_free`).  Only a card
that *is itself pulled* stops the walk. -/

/-- Reverse induction on lists (last letter first). -/
theorem list_rev_induction {α : Type} {motive : List α → Prop} (h0 : motive [])
    (hs : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) : ∀ l, motive l := by
  have key : ∀ (l t : List α), motive t → motive (t ++ l) := by
    intro l
    induction l with
    | nil => intro t ht; simpa using ht
    | cons a l ih =>
        intro t ht
        have h1 : motive (t ++ [a]) := hs t a ht
        have h2 : motive ((t ++ [a]) ++ l) := ih (t ++ [a]) h1
        rwa [List.append_assoc, List.singleton_append] at h2
  intro l
  simpa using key l [] h0

/-- Splitting a witness play at its **last** letter. -/
theorem shuffle_snoc {u A : State} {γ : List Move} {m : Move}
    (huwf : u.WF) (h : ShufflePlayW u (γ ++ [m]) A) :
    ∃ A1, ShufflePlayW u γ A1 ∧ reversibleAtW A1 m ∧ State.step A1 m = some A ∧ A1.WF := by
  induction γ generalizing u with
  | nil =>
      rw [List.nil_append] at h
      cases h with
      | cons hrev hstep hrest =>
          cases hrest
          exact ⟨u, Walk.nil u, hrev, hstep, huwf⟩
  | cons a t ih =>
      cases h with
      | cons hrev hstep hrest =>
          have hs1 := step_wf huwf hstep
          obtain ⟨A1, hplay, hrevA, hstepA, hwfA⟩ := ih hs1 hrest
          exact ⟨A1, Walk.cons hrev hstep hplay, hrevA, hstepA, hwfA⟩

/-- **THE BACKWARD WALK.**  Along a raise-free witness leg from a saturated
origin, an S-live card at the end is either *itself pulled on the leg*, or one
of `{y, y.twin}` is covered at the end (a cover found on the way is carried
forward to the end), or it was already S-live at the origin. -/
theorem live_back_aux {u : State} (huwf : u.WF) (hsat : SSaturated u) :
    ∀ (γ : List Move) (A : State) (y : Card),
      ShufflePlayW u γ A → (∀ m ∈ γ, ¬ Bubble.IsRaise m) → A.WF → CanRaiseS A y →
      (∃ (z : Card) (bz : Base), Move.foundToTab z bz ∈ γ ∧ y = z) ∨
        CoveredAt A y ∨ CoveredAt A y.twin := by
  intro γ
  refine list_rev_induction (motive := fun γ => ∀ (A : State) (y : Card),
      ShufflePlayW u γ A → (∀ m ∈ γ, ¬ Bubble.IsRaise m) → A.WF → CanRaiseS A y →
      (∃ (z : Card) (bz : Base), Move.foundToTab z bz ∈ γ ∧ y = z) ∨
        CoveredAt A y ∨ CoveredAt A y.twin) ?_ ?_ γ
  · intro A y hplay _ _ hy
    cases hplay with
    | nil => exact absurd hy (hsat y)
  · intro γ' m ih A y hplay hnr hA hy
    obtain ⟨A1, hplay', hrev, hstep, hA1⟩ := shuffle_snoc huwf hplay
    have hnr' : ∀ q ∈ γ', ¬ Bubble.IsRaise q :=
      fun q hq => hnr q (by rw [List.mem_append]; exact Or.inl hq)
    have hnrLast : ¬ Bubble.IsRaise m :=
      hnr m (by rw [List.mem_append]; exact Or.inr (List.mem_singleton_self m))
    have hsingle : ShufflePlayW A1 [m] A := Walk.cons hrev hstep (Walk.nil A)
    have hsub : ∀ (z : Card) (bz : Base), Move.foundToTab z bz ∈ γ' →
        Move.foundToTab z bz ∈ γ' ++ [m] :=
      fun z bz hz => by rw [List.mem_append]; exact Or.inl hz
    cases m with
    | draw =>
        have hfree : ∀ q ∈ [Move.draw], ValleyElim.FreeMove q := by
          intro q hq; rw [List.mem_singleton] at hq; subst hq; exact ValleyElim.free_draw
        have hy1 : CanRaiseS A1 y :=
          ((Bridge.canRaiseS_of_free_play_iff hsingle hfree hA1 y).mpr hy)
        rcases ih A1 y hplay' hnr' hA1 hy1 with hp | hc
        · obtain ⟨z, bz, hmem, hyz⟩ := hp
          exact Or.inl ⟨z, bz, hsub z bz hmem, hyz⟩
        · exact Or.inr (covered_carry_free hsingle hA1 hfree hc)
    | tabToTab x0 bb =>
        have hfree : ∀ q ∈ [Move.tabToTab x0 bb], ValleyElim.FreeMove q := by
          intro q hq; rw [List.mem_singleton] at hq; subst hq
          exact ValleyElim.free_slide x0 bb
        have hy1 : CanRaiseS A1 y :=
          ((Bridge.canRaiseS_of_free_play_iff hsingle hfree hA1 y).mpr hy)
        rcases ih A1 y hplay' hnr' hA1 hy1 with hp | hc
        · obtain ⟨z, bz, hmem, hyz⟩ := hp
          exact Or.inl ⟨z, bz, hsub z bz hmem, hyz⟩
        · exact Or.inr (covered_carry_free hsingle hA1 hfree hc)
    | wasteToFound x0 =>
        exact absurd hrev (wasteToFound_not_reversibleAtW A1 x0)
    | wasteToTab x0 bb =>
        exact absurd hrev (wasteToTab_not_reversibleAtW A1 x0 bb)
    | tabToFound x0 => exact absurd ⟨x0, rfl⟩ hnrLast
    | foundToTab z bz =>
        by_cases hyz : y = z
        · refine Or.inl ⟨z, bz, ?_, hyz⟩
          rw [List.mem_append]; exact Or.inr (List.mem_singleton_self _)
        · rcases canRaise_or_covered hA hy with hcan | hcov
          · have hy1 : CanRaiseS A1 y := canRaiseS_of_canRaise_of_pull hA1 hstep hyz hcan
            rcases ih A1 y hplay' hnr' hA1 hy1 with hp | hc
            · obtain ⟨z0, bz0, hmem, hyz0⟩ := hp
              exact Or.inl ⟨z0, bz0, hsub z0 bz0 hmem, hyz0⟩
            · exact Or.inr (covered_carry_pull hA1 hstep hc)
          · exact Or.inr (Or.inl hcov)

/-! ## §C  The `pre` pull-headed lane: both members of a live pair are pulled -/

/-- `PulledIn γ y` — the card `y` itself is pulled somewhere on the leg `γ`. -/
def PulledIn (γ : List Move) (y : Card) : Prop :=
  ∃ bz : Base, Move.foundToTab y bz ∈ γ

theorem pulledIn_mono {γ δ : List Move} {y : Card} (hsub : ∀ m ∈ γ, m ∈ δ)
    (h : PulledIn γ y) : PulledIn δ y := by
  obtain ⟨bz, hbz⟩ := h
  exact ⟨bz, hsub _ hbz⟩

/-- A cover never coexists with a raisable membership `x`. -/
theorem not_covered_pair_x {F : State} {x : Card} (hF : F.WF)
    (hx : CanRaise F x) (hxt : CanRaise F x.twin) :
    ¬ (CoveredAt F x ∨ CoveredAt F x.twin) := by
  rintro (hc | hc)
  · exact not_canRaise_of_covered hF hc hx
  · exact not_canRaise_of_covered hF hc hxt

/-- The same for the twin membership. -/
theorem not_covered_pair_xt {F : State} {x : Card} (hF : F.WF)
    (hx : CanRaise F x) (hxt : CanRaise F x.twin) :
    ¬ (CoveredAt F x.twin ∨ CoveredAt F x.twin.twin) := by
  rintro (hc | hc)
  · exact not_canRaise_of_covered hF hc hxt
  · rw [card_twin_twin] at hc
    exact not_canRaise_of_covered hF hc hx

/-- A cover never coexists with a raisable member of the pair `{x, x.twin}`. -/
theorem not_covered_twin_pair {F : State} {x z : Card} (hF : F.WF)
    (hz : z = x ∨ z = x.twin) (hx : CanRaise F x) (hxt : CanRaise F x.twin) :
    ¬ (CoveredAt F z ∨ CoveredAt F z.twin) := by
  rcases hz with h | h
  · rw [h]; exact not_covered_pair_x hF hx hxt
  · rw [h]; exact not_covered_pair_xt hF hx hxt

/-- **THE PULL-HEADED REDUCTION.**  At a split with a raise-free left leg, if
both twins of a live pair are vanilla-raisable at the bottom, then *each of
them is itself pulled on the left leg*.  (No pull-headedness is needed: the
valley pull's own card is pulled at the valley, and every other card is walked
back by §B.) -/
theorem pulled_of_both_raiseFree
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail)
    (hnr : ∀ m ∈ left, ¬ Bubble.IsRaise m)
    {x : Card} (hF : F.WF) (hx : CanRaise F x) (hxt : CanRaise F x.twin) :
    PulledIn left x ∧ PulledIn left x.twin := by
  obtain ⟨A', B, hpreplay, hrevP, hstepP, hpost, hA', hB, hcanB, hfreePost⟩ :=
    TailHead.split_pull_landing h
  obtain ⟨huwf, hsu, -, -, -, -, -, hleft, -, hshape, hfree, -⟩ := h
  have hnrPre : ∀ m ∈ pre, ¬ Bubble.IsRaise m :=
    fun m hm => hnr m (by rw [hshape]; exact List.mem_append_left _ hm)
  have hsubPre : ∀ m ∈ pre, m ∈ left :=
    fun m hm => by rw [hshape]; exact List.mem_append_left _ hm
  -- the key row: any raisable member of the pair that is not the valley pull
  -- is pulled in `pre`
  have key : ∀ y : Card, (y = x ∨ y = x.twin) → y ≠ c → PulledIn pre y := by
    intro y hy hnc
    have hycan : CanRaise F y := by
      rcases hy with hyx | hyx
      · rw [hyx]; exact hx
      · rw [hyx]; exact hxt
    have hcontra : ¬ (CoveredAt F y ∨ CoveredAt F y.twin) := by
      rcases hy with hyx | hyx
      · rw [hyx]; exact not_covered_pair_x hF hx hxt
      · rw [hyx]; exact not_covered_pair_xt hF hx hxt
    have hSB : CanRaiseS B y :=
      (Bridge.canRaiseS_of_free_play_iff hpost hfreePost hB y).mpr (CanRaiseS.now y hycan)
    rcases canRaise_or_covered hB hSB with hvan | hcov
    · have hyA' : CanRaiseS A' y := canRaiseS_of_canRaise_of_pull hA' hstepP hnc hvan
      rcases live_back_aux huwf hsu pre A' y hpreplay hnrPre hA' hyA' with hp | hc
      · obtain ⟨z, bz, hmem, hyz⟩ := hp
        exact ⟨bz, by rw [hyz]; exact hmem⟩
      · exact absurd (covered_carry_free hpost hB hfreePost (covered_carry_pull hA' hstepP hc))
          hcontra
    · exact absurd (covered_mono_free hpost hB hfreePost hcov) hcontra
  have hvalley : PulledIn left c := by
    refine ⟨b, ?_⟩
    rw [hshape]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  by_cases hxc : x = c
  · have hxtc : x.twin ≠ c := by rw [hxc]; exact SplitKit.card_twin_ne c
    refine ⟨?_, pulledIn_mono hsubPre (key x.twin (Or.inr rfl) hxtc)⟩
    rw [hxc]; exact hvalley
  · by_cases hxtc : x.twin = c
    · refine ⟨pulledIn_mono hsubPre (key x (Or.inl rfl) hxc), ?_⟩
      rw [hxtc]; exact hvalley
    · exact ⟨pulledIn_mono hsubPre (key x (Or.inl rfl) hxc),
        pulledIn_mono hsubPre (key x.twin (Or.inr rfl) hxtc)⟩

/-- **THE NAMED RESIDUAL.**  No raise-free split has a both-raisable live pair
whose *both* members are pulled on the left leg.  A pure card-occurrence
statement: no cover, no seat, no rank, no bottom coordinate. -/
def NoBothPulledTwin : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State) (left right : List Move)
    (c d : Card) (b : Base) (pre post tail : List Move),
    SplitHyp u v ρ F left right c d b pre post tail →
    (∀ m ∈ left, ¬ Bubble.IsRaise m) →
    ∀ x : Card, F.WF → TwinLivePair F x → CanRaise F x → CanRaise F x.twin →
      ¬ (PulledIn left x ∧ PulledIn left x.twin)

/-- **THE RAISE-FREE LANE OF `BottomNotBothRaisable` IS THE RESIDUAL.** -/
theorem bottomNotBoth_raiseFree_of_noBothPulledTwin (hres : NoBothPulledTwin) :
    ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      (∀ m ∈ left, ¬ Bubble.IsRaise m) →
      ∀ x : Card, F.WF → TwinLivePair F x →
        ¬ (CanRaise F x ∧ CanRaise F x.twin) := by
  intro u v ρ F left right c d b pre post tail h hnr x hF hl hboth
  exact hres u v ρ F left right c d b pre post tail h hnr x hF hl hboth.1 hboth.2
    (pulled_of_both_raiseFree h hnr hF hboth.1 hboth.2)

/-- The pull-headed sub-lane, in the shape `Both.BottomNotBothPullPre` uses. -/
theorem bottomNotBothPullPre_of_noBothPulledTwin (hres : NoBothPulledTwin) :
    ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      (∃ (m : Move) (pre2 : List Move), pre = m :: pre2 ∧ ¬ ValleyElim.FreeMove m) →
      (∀ m ∈ left, ¬ Bubble.IsRaise m) →
      ∀ x : Card, F.WF → TwinLivePair F x →
        ¬ (CanRaise F x ∧ CanRaise F x.twin) :=
  fun u v ρ F left right c d b pre post tail h _ hnr =>
    bottomNotBoth_raiseFree_of_noBothPulledTwin hres
      u v ρ F left right c d b pre post tail h hnr

/-- The same lane under the mountain datum (which supplies the raise-freeness
that `SplitHyp` itself does not carry). -/
theorem bottomNotBothPullPreMountain_of_noBothPulledTwin (hres : NoBothPulledTwin)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State) (left right : List Move)
      (c d : Card) (b : Base) (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right) :
    ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      (∃ (m : Move) (pre2 : List Move), pre = m :: pre2 ∧ ¬ ValleyElim.FreeMove m) →
      ∀ x : Card, F.WF → TwinLivePair F x →
        ¬ (CanRaise F x ∧ CanRaise F x.twin) := by
  intro u v ρ F left right c d b pre post tail h _ x hF hl
  exact bottomNotBoth_raiseFree_of_noBothPulledTwin hres
    u v ρ F left right c d b pre post tail h
    (hms u v ρ F left right c d b pre post tail h).1 x hF hl

/-- **THE RAISE-CARRYING LANE** — the part of the split space the walk cannot
enter (a raise in `left` can *create* S-liveness, and can *undo* a cover). -/
def LeftRaiseLane : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State) (left right : List Move)
    (c d : Card) (b : Base) (pre post tail : List Move),
    SplitHyp u v ρ F left right c d b pre post tail →
    (∃ m ∈ left, Bubble.IsRaise m) →
    ∀ x : Card, F.WF → TwinLivePair F x →
      ¬ (CanRaise F x ∧ CanRaise F x.twin)

/-- **THE EXACT DECOMPOSITION OF THE GATED VACUITY.**  Given the residual, the
whole statement is the raises-in-`left` lane. -/
theorem bottomNotBoth_iff_leftRaise_of_noBothPulled (hres : NoBothPulledTwin) :
    Pin.BottomNotBothRaisable ↔ LeftRaiseLane := by
  have isRaise_of_true : ∀ {m : Move}, Bubble.isRaiseB m = true → Bubble.IsRaise m := by
    intro m h
    cases m with
    | tabToFound c => exact ⟨c, rfl⟩
    | draw => exact Bool.noConfusion h
    | wasteToFound c => exact Bool.noConfusion h
    | wasteToTab c b => exact Bool.noConfusion h
    | foundToTab c b => exact Bool.noConfusion h
    | tabToTab c b => exact Bool.noConfusion h
  have not_isRaise_of_false : ∀ {m : Move}, Bubble.isRaiseB m = false → ¬ Bubble.IsRaise m := by
    intro m h hr
    rw [Bubble.isRaiseB_eq_true hr] at h
    exact Bool.noConfusion h
  constructor
  · intro h u v ρ F left right c d b pre post tail hs _ x hF hl
    exact h u v ρ F left right c d b pre post tail hs x hF hl
  · intro hr u v ρ F left right c d b pre post tail hs x hF hl
    by_cases hany : left.any Bubble.isRaiseB = true
    · obtain ⟨m, hm, hmtrue⟩ := List.any_eq_true.mp hany
      exact hr u v ρ F left right c d b pre post tail hs ⟨m, hm, isRaise_of_true hmtrue⟩
        x hF hl
    · have hfalse : left.any Bubble.isRaiseB = false := by
        cases hv : left.any Bubble.isRaiseB with
        | false => rfl
        | true => exact absurd hv hany
      have hall := ValleyElim.any_eq_false hfalse
      exact bottomNotBoth_raiseFree_of_noBothPulledTwin hres
        u v ρ F left right c d b pre post tail hs
        (fun m hm => not_isRaise_of_false (hall m hm)) x hF hl

/-- **VALIDATION OF THE WALK.**  At a nil prefix the conclusion of
`pulled_of_both_raiseFree` is impossible (the free tail carries no pull), so
the walk re-proves `Both.bottomNotBothRaisableNil` *without* the seat/rank
argument. -/
theorem nilPre_no_both_of_walk
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {post tail : List Move}
    (hs : SplitHyp u v ρ F left right c d b [] post tail)
    (hnr : ∀ m ∈ left, ¬ Bubble.IsRaise m)
    {x : Card} (hF : F.WF) : ¬ (CanRaise F x ∧ CanRaise F x.twin) := by
  rintro ⟨hx, hxt⟩
  obtain ⟨hp1, hp2⟩ := pulled_of_both_raiseFree hs hnr hF hx hxt
  obtain ⟨-, -, -, -, -, -, -, hleft, -, hshape, hfree, -⟩ := hs
  have hleft' : left = Move.foundToTab c b :: post := by rw [hshape]; rfl
  have hpostFree : ∀ z : Card, ∀ bz : Base, Move.foundToTab z bz ∈ post → False :=
    fun z bz hmem => PinRight.foundToTab_not_free (hfree (Move.foundToTab z bz) hmem)
  -- a pull in `left` is the valley pull or lies in the free tail
  have hloc : ∀ z : Card, (∃ bz : Base, Move.foundToTab z bz ∈ left) →
      z = c := by
    intro z hz
    obtain ⟨bz, hbz⟩ := hz
    rw [hleft'] at hbz
    rcases List.mem_cons.mp hbz with heq | hpost
    · exact Move.foundToTab.inj heq |>.1
    · exact absurd hpost (hpostFree z bz)
  have hxc : x = c := hloc x hp1
  have hxtc : x.twin = c := hloc x.twin hp2
  exact SplitKit.card_twin_ne c (hxc ▸ hxtc)

/-- **CROSS-CHECK: the walk re-proves `Both.bottomNotBothRaisableNil`.**  (The
nil lane is the case where the walk's conclusion is impossible.) -/
theorem bottomNotBothRaisableNil_of_walk : Both.BottomNotBothRaisableNil := by
  intro u v ρ F left right c d b post tail hs x hF hl
  have hnr : ∀ m ∈ left, ¬ Bubble.IsRaise m := by
    obtain ⟨-, -, -, -, -, -, -, -, -, hshape, hfree, -⟩ := hs
    intro m hm hraise
    rw [hshape] at hm
    rcases List.mem_cons.mp hm with heq | hpost
    · subst heq
      obtain ⟨c0, hc0⟩ := hraise
      exact Move.noConfusion hc0
    · rcases hfree m hpost with hd | ⟨x0, b0, hsl⟩
      · subst hd
        obtain ⟨c0, hc0⟩ := hraise
        exact Move.noConfusion hc0
      · subst hsl
        obtain ⟨c0, hc0⟩ := hraise
        exact Move.noConfusion hc0
  exact nilPre_no_both_of_walk hs hnr hF

/-- **THE CAMPAIGN CHAIN FROM THE RAISE LANE.**  With the residual, the gated
vacuity and hence `SatDifferForkWF` follow from the raises-in-`left` lane. -/
theorem satDifferForkWF_of_leftRaise (hres : NoBothPulledTwin) (hr : LeftRaiseLane)
    (hl : SplitLivePair) (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  Pin.satDifferForkWF_of_notBoth hl
    ((bottomNotBoth_iff_leftRaise_of_noBothPulled hres).mpr hr) hmin

/-! ## §D  `SameCardNilBlock` is the nil-prefix corner of `SplitNe` -/

/-- `NilPreNoSameCard` — no nil-prefix split has `d = c`. -/
def NilPreNoSameCard : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State) (left right : List Move)
    (c d : Card) (b : Base) (post tail : List Move),
    SplitHyp u v ρ F left right c d b [] post tail → d ≠ c

/-- `NilPreBlock` — the `pre = []` block clause with a nonempty free tail. -/
def NilPreBlock : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State) (left right : List Move)
    (c d : Card) (b : Base) (post tail : List Move),
    SplitHyp u v ρ F left right c d b [] post tail → post ≠ [] → ¬ CanRaise F c

/-- **AT A SAME-CARD SPLIT THE FREE TAIL IS NONEMPTY.**  `post = []` makes the
pull and the raise adjacent, and `ValleyStep.valley_cancel_same` deletes the
pair — against shortestness. -/
theorem nilPre_post_ne_nil_of_sameCard
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b [] post tail) (hdc : d = c) :
    post ≠ [] := by
  intro hpost
  have hlenEq : ρ.length = tail.length + 2 := by
    have hh := JointKit.splitHyp_length_eq h
    rw [hpost] at hh
    simpa using hh
  obtain ⟨huwf, -, -, -, -, hmin, -, hleft, hright, hshape, -, hrightShape⟩ := h
  have hleft' : left = [Move.foundToTab c b] := by
    rw [hshape, hpost]; rfl
  rw [hleft'] at hleft
  have hstep : State.step u (Move.foundToTab c b) = some F := by
    cases hleft with
    | cons hrev hs hrest => cases hrest; exact hs
  have hright' : ShufflePlayW F (Move.tabToFound c :: tail) v := by
    have hh := hright
    rw [hrightShape, hdc] at hh
    exact hh
  have hnew : ShufflePlayW u tail v :=
    ValleyStep.valley_cancel_same huwf (Walk.nil u) hstep hright'
  have hlen : tail.length < ρ.length := by
    rw [hlenEq]
    omega
  exact absurd (hmin tail hnew) (Nat.not_le.mpr hlen)

/-- **`SameCardNilBlock` ⟺ no nil-prefix same-card split.**  The block
conclusion is `¬ CanRaise F c`, but `splitHyp_green` already gives
`CanRaise F d`; with `d = c` the conclusion is false. -/
theorem sameCardNilBlock_iff_nilPreNoSameCard :
    Both.SameCardNilBlock ↔ NilPreNoSameCard := by
  constructor
  · intro h u v ρ F left right c d b post tail hs hdc
    obtain ⟨-, -, hcanD, -⟩ := splitHyp_green hs
    exact h u v ρ F left right c d b post tail hs hdc (hdc ▸ hcanD)
  · intro h u v ρ F left right c d b post tail hs hdc
    exact absurd hdc (h u v ρ F left right c d b post tail hs)

/-- **`SameCardNilBlock` ⟺ the `pre = []` block clause.** -/
theorem nilPreBlock_iff_sameCardNilBlock :
    NilPreBlock ↔ Both.SameCardNilBlock := by
  constructor
  · intro hblock u v ρ F left right c d b post tail hs hdc
    exact hblock u v ρ F left right c d b post tail hs
      (nilPre_post_ne_nil_of_sameCard hs hdc)
  · intro hsame
    exact Both.nilPreBlock_of_parts hsame

/-- `SameCardNilBlock` is the nil-prefix corner of the tree's `SplitNe`. -/
theorem sameCardNilBlock_of_splitNe (hn : SplitKit.SplitNe) : Both.SameCardNilBlock := by
  rw [sameCardNilBlock_iff_nilPreNoSameCard]
  intro u v ρ F left right c d b post tail hs hdc
  exact absurd hdc.symm (hn u v ρ F left right c d b [] post tail hs)

/-- ... hence a consequence of `SplitBlock`. -/
theorem sameCardNilBlock_of_splitBlock (hb : SplitBlock) : Both.SameCardNilBlock :=
  sameCardNilBlock_of_splitNe (SplitKit.splitNe_of_block hb)

/-- **THE BRANCH IS NOT VACUOUS-BY-FIAT**: any same-card nil-prefix split
refutes `SameCardNilBlock` outright. -/
theorem not_sameCardNilBlock_of_witness
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {post tail : List Move}
    (hs : SplitHyp u v ρ F left right c d b [] post tail) (hdc : d = c) :
    ¬ Both.SameCardNilBlock := by
  intro h
  obtain ⟨-, -, hcanD, -⟩ := splitHyp_green hs
  exact h u v ρ F left right c d b post tail hs hdc (hdc ▸ hcanD)

/-- **THE SHAPE OF ANY COUNTEREXAMPLE.**  A same-card nil-prefix split has a
nonempty free tail containing a slide landing on `c`, and the tail is never
"draws plus at most one slide": the cover is created *and later undone*. -/
theorem nilPre_sameCard_shape
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {post tail : List Move}
    (hs : SplitHyp u v ρ F left right c d b [] post tail) (hdc : d = c) :
    post ≠ [] ∧ post.any (TailHead.isCoverB c) = true ∧
      ¬ TailHead.AtMostOneSlide post := by
  have hcov := TailHead.sameCard_turn_has_cover hs hdc
  refine ⟨?_, hcov, fun hpost => TailHead.sameCard_turn_atLeastTwoSlides hs hdc hpost⟩
  intro hpost
  rw [hpost] at hcov
  exact Bool.noConfusion hcov

/-- **THE EXACT STATE OF THE BRANCH.**  `SameCardNilBlock` is equivalent to
`NoSameCard` at `pre = []`, to the block clause there, and is implied by
`SplitNe` (hence by `SplitBlock`). -/
theorem sameCard_residual_summary :
    (Both.SameCardNilBlock ↔ NilPreNoSameCard) ∧
      (NilPreBlock ↔ Both.SameCardNilBlock) ∧
      (SplitKit.SplitNe → Both.SameCardNilBlock) :=
  ⟨sameCardNilBlock_iff_nilPreNoSameCard, nilPreBlock_iff_sameCardNilBlock,
    sameCardNilBlock_of_splitNe⟩

/-- **THE `pre = []` BLOCK LANE FROM `SplitNe`.**  (The branch is not an
independent obligation: the tree's `SplitNe` already implies it.) -/
theorem nilPreBlock_of_splitNe (hn : SplitKit.SplitNe) : NilPreBlock :=
  nilPreBlock_iff_sameCardNilBlock.mpr (sameCardNilBlock_of_splitNe hn)

/-- ... and hence from `SplitBlock`. -/
theorem nilPreBlock_of_splitBlock (hb : SplitBlock) : NilPreBlock :=
  nilPreBlock_of_splitNe (SplitKit.splitNe_of_block hb)

/-- **THE `d = c` BRANCH FROM `SplitNe`** in the exact shape `ForkBoth` uses. -/
theorem nilPreBlock_of_splitNe_apply (hn : SplitKit.SplitNe)
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {post tail : List Move}
    (hs : SplitHyp u v ρ F left right c d b [] post tail) (hpost : post ≠ []) :
    ¬ CanRaise F c :=
  nilPreBlock_of_splitNe hn u v ρ F left right c d b post tail hs hpost

/-! ## §D2  What a counterexample must look like (the sharpened residual)

If a nil-prefix same-card split exists, it is a **minimal valley split** whose
free tail has at least two slides, one of them landing on `c`.  Combined with
§A.2 the cover slide cannot be undone inside the free tail without a later
*raise* of the covering card (the pull/raise re-route lane), which is exactly
the known `LandRes.UncoverResidual` shape. -/

/-- **A COUNTEREXAMPLE CARRIES A COVER SLIDE AND AT LEAST TWO SLIDES.** -/
theorem sameCard_counterexample_shape
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {post tail : List Move}
    (hs : SplitHyp u v ρ F left right c d b [] post tail) (hdc : d = c)
    (hc : CanRaise F c) :
    (∃ (x : Card) (s1 s2 : List Move),
        post = s1 ++ Move.tabToTab x (Sum.inr c) :: s2) ∧
      ¬ TailHead.AtMostOneSlide post ∧ post ≠ [] := by
  have hcov := TailHead.sameCard_turn_has_cover hs hdc
  obtain ⟨s1, m, s2, heq, -, hm⟩ := ValleyElim.exists_first_bool (TailHead.isCoverB c) post hcov
  obtain ⟨x, hx⟩ := TailHead.isCoverB_eq_true_iff.mp hm
  refine ⟨⟨x, s1, s2, by rw [heq, hx]⟩, ?_, ?_⟩
  · intro hpost
    exact TailHead.sameCard_turn_atLeastTwoSlides hs hdc hpost
  · intro hpost
    rw [hpost] at hcov
    exact Bool.noConfusion hcov

/-! ## §E  Axiom battery -/

#print axioms SC.below_append_snoc_of_mem
#print axioms SC.mem_faceUp_snoc_iff
#print axioms SC.pileHolding_pull_ne
#print axioms SC.seatOf_pull_ne
#print axioms SC.mem_faceUp_of_seat_inr
#print axioms SC.not_faceUp_of_foundTop
#print axioms SC.covered_pull_forward
#print axioms SC.covered_forward_free
#print axioms SC.covered_mono_free
#print axioms SC.covered_carry_free
#print axioms SC.covered_carry_pull
#print axioms SC.canRaiseS_twin_of_canRaise_landing
#print axioms SC.canRaiseS_of_canRaise_of_pull
#print axioms SC.list_rev_induction
#print axioms SC.shuffle_snoc
#print axioms SC.live_back_aux
#print axioms SC.pulledIn_mono
#print axioms SC.not_covered_twin_pair
#print axioms SC.pulled_of_both_raiseFree
#print axioms SC.bottomNotBoth_raiseFree_of_noBothPulledTwin
#print axioms SC.bottomNotBothPullPre_of_noBothPulledTwin
#print axioms SC.bottomNotBothPullPreMountain_of_noBothPulledTwin
#print axioms SC.bottomNotBoth_iff_leftRaise_of_noBothPulled
#print axioms SC.nilPre_no_both_of_walk
#print axioms SC.bottomNotBothRaisableNil_of_walk
#print axioms SC.satDifferForkWF_of_leftRaise
#print axioms SC.nilPre_post_ne_nil_of_sameCard
#print axioms SC.sameCardNilBlock_iff_nilPreNoSameCard
#print axioms SC.nilPreBlock_iff_sameCardNilBlock
#print axioms SC.sameCardNilBlock_of_splitNe
#print axioms SC.sameCardNilBlock_of_splitBlock
#print axioms SC.not_sameCardNilBlock_of_witness
#print axioms SC.nilPre_sameCard_shape
#print axioms SC.sameCard_residual_summary
#print axioms SC.nilPreBlock_of_splitNe
#print axioms SC.nilPreBlock_of_splitBlock
#print axioms SC.nilPreBlock_of_splitNe_apply
#print axioms SC.sameCard_counterexample_shape
