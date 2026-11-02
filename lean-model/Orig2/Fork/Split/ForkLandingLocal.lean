import Orig2.Fork.Split.ForkLanding

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-!
# Orig2/ForkLandingLocal — the pull-crossing dichotomy for `Mech.LandingLivePair`

READ-ONLY scratch card: no source edit, no commit.  Zero `sorry`, zero
`Classical.choice`, zero `native_decide`; battery at the tail.

## What is proved here

1. `canRaiseS_below_form` — the flat characterization of `CanRaiseS`
   (`CargoRaise.canRaiseS_iff`) in its *deterministic* `below`/`fromCard`
   shape.  This is the form in which the pull's pile edit is visible.
2. `canRaiseS_of_pull_of_ne_twin` — **THE LOCAL STEP LEMMA**: a pull of `c`
   cannot make a card `e ∉ {c, c.twin}` newly S-live.  Equivalently, a pull
   creates only the S-liveness of `c` (and possibly `c.twin`).
3. `local_dichotomy` — the dichotomy asked for in the brief: an S-live card
   `e ≠ c` at the landing was either S-live before the pull, or is `c.twin`.
4. `landingLivePair_iff_local` — **THE EXACT REDUCTION**: over one pull,
   `LandingLivePair B c` is exactly
   ```
   CanRaiseS B c.twin  ∧  (∀ e, CanRaiseS A e → CanRaiseS B e →
      e.suit = c.suit ∨ e.suit = c.twin.suit)
   ```
   i.e. the third-suit exclusion is a statement about the *pull crossing*,
   not about any cargo descendant.
5. `landingThirdFree_of_free_pre` — **the third-suit exclusion is PROVED**
   whenever the prefix `pre` of the split (everything before the valley
   pull) is a free play: `u` is saturated, free plays preserve the S-live
   set, so *no* card is S-live just before the pull, and the local lemma
   leaves only `{c, c.twin}` at the landing.
-/

namespace LandKit

/-! ## §0. The deterministic normal form of the S-license -/

/-- **THE `below`/`fromCard` FORM OF `CanRaiseS`.**  At `WF`, `CanRaiseS st c`
is exactly: `c` is next-up, it sits face up in some pile, it has company
below (or is a bare king), and either it is the pile's top card or its twin
tops some pile.  This is `canRaiseS_iff` with the raw split `bs ++ c :: run`
identified with `below`/`fromCard`, which is what makes the pull's
single-pile edit transportable. -/
theorem canRaiseS_below_form {st : State} (hwf : st.WF) {c : Card} :
    CanRaiseS st c ↔
      st.nextUp c = true ∧
      ∃ a : Anchor, c ∈ (st.piles a).faceUp ∧
        (below c (st.piles a).faceUp ≠ [] ∨
          ((st.piles a).hidden = [] ∧ c.rank = Rank.king)) ∧
        (fromCard c (st.piles a).faceUp = [c] ∨ st.pileOfTop c.twin ≠ none) := by
  rw [canRaiseS_iff hwf]
  constructor
  · rintro ⟨hnext, a, bs, run, hshape, hseat, hdisj⟩
    have hmem : c ∈ (st.piles a).faceUp := by
      rw [hshape]
      exact List.mem_append_right _ (List.mem_cons_self ..)
    have hnd : (bs ++ c :: run).Nodup := by
      rw [← hshape]
      exact runOK_nodup (hwf.2.1 a)
    have hcNbs : c ∉ bs := nodup_mid_notmem c bs run hnd
    have hbelow : below c (st.piles a).faceUp = bs := by
      have hexcl := tfc_below_fromCard_excl c bs (c :: run) hcNbs
      have h1 := hexcl.1
      rw [below_cons_self, List.append_nil] at h1
      rw [hshape]
      exact h1
    have hfc : fromCard c (st.piles a).faceUp = c :: run := by
      have hexcl := tfc_below_fromCard_excl c bs (c :: run) hcNbs
      have h2 := hexcl.2
      rw [fromCard_head_eq] at h2
      rw [hshape]
      exact h2
    refine ⟨hnext, a, hmem, ?_, ?_⟩
    · rcases hseat with h | h
      · exact Or.inl (by rw [hbelow]; exact h)
      · exact Or.inr h
    · rcases hdisj with h | h
      · exact Or.inl (by rw [hfc, h])
      · exact Or.inr h
  · rintro ⟨hnext, a, hmem, hseat, hdisj⟩
    obtain ⟨run, hfc⟩ := tfc_fromCard_cons_head (st.piles a).faceUp hmem
    refine ⟨hnext, a, below c (st.piles a).faceUp, run, ?_, ?_, ?_⟩
    · rw [← hfc]
      exact (tfc_below_fromCard c (st.piles a).faceUp).symm
    · exact hseat
    · rcases hdisj with h | h
      · left
        rw [hfc] at h
        simpa using h
      · exact Or.inr h

/-! ## §1. The pile edit of a pull -/

/-- **THE PULL MOVES NO OTHER PILE.** -/
theorem pullSt_piles_of_ne {A : State} {c : Card} {b : Base} {k j : Anchor}
    (hk : CommuteStep.tgt A b = some k) (hj : j ≠ k) :
    (CommuteStep.pullSt A c b).piles j = A.piles j :=
  CommuteStep.pullSt_piles_ne hk hj

/-- **THE PULL ONLY WRITES `c` ON ITS TARGET PILE'S TOP.**  Hence no other
card can become — or stop being — a pile top, except that `c` becomes one. -/
theorem pileOfTop_twin_prev_of_pull {A B : State} {c : Card} {b : Base} {k : Anchor}
    (hA : A.WF) (hB : B.WF) (hBpull : B = CommuteStep.pullSt A c b)
    (hk : CommuteStep.tgt A b = some k) {e : Card} (het : e.twin ≠ c)
    (h : B.pileOfTop e.twin ≠ none) :
    A.pileOfTop e.twin ≠ none := by
  obtain ⟨j, hj⟩ := option_some_of_ne_none h
  have htopj : (B.piles j).top = some e.twin := (pileOfTop_eq_some_iff hB).mp hj
  have htopk : (B.piles k).top = some c := by
    rw [hBpull]
    exact CommuteStep.pullSt_top_written hk
  have hjk : j ≠ k := by
    intro hjk
    rw [hjk] at htopj
    rw [htopk] at htopj
    exact het (Option.some.inj htopj).symm
  have hpj : B.piles j = A.piles j := by
    rw [hBpull]
    exact CommuteStep.pullSt_piles_ne hk hjk
  have htopAj : (A.piles j).top = some e.twin := by
    rw [← hpj]
    exact htopj
  rw [show A.pileOfTop e.twin = some j from (pileOfTop_eq_some_iff hA).mpr htopAj]
  simp

/-! ## §2. The local step: a pull creates no third-suit S-liveness -/

/-- The `below`/`fromCard` data at `A` from the data at `B` when the pull left
pile `a` alone. -/
theorem below_form_transfer_eq {A B : State} {e : Card} {a : Anchor}
    (hface : (B.piles a).faceUp = (A.piles a).faceUp)
    (hhid : (B.piles a).hidden = (A.piles a).hidden)
    (hmem : e ∈ (B.piles a).faceUp)
    (hseat : below e (B.piles a).faceUp ≠ [] ∨
      ((B.piles a).hidden = [] ∧ e.rank = Rank.king))
    (hdisj : fromCard e (B.piles a).faceUp = [e] ∨ B.pileOfTop e.twin ≠ none)
    (hdisjA : B.pileOfTop e.twin ≠ none → A.pileOfTop e.twin ≠ none) :
    e ∈ (A.piles a).faceUp ∧
      (below e (A.piles a).faceUp ≠ [] ∨
        ((A.piles a).hidden = [] ∧ e.rank = Rank.king)) ∧
      (fromCard e (A.piles a).faceUp = [e] ∨ A.pileOfTop e.twin ≠ none) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← hface]; exact hmem
  · rcases hseat with h | h
    · exact Or.inl (by rw [← hface]; exact h)
    · exact Or.inr ⟨by rw [← hhid]; exact h.1, h.2⟩
  · rcases hdisj with h | h
    · exact Or.inl (by rw [← hface]; exact h)
    · exact Or.inr (hdisjA h)

/-- The `below`/`fromCard` data at `A` from the data at `B` when the pull
appended `c` on pile `a`'s top, and `e ≠ c` sits below it. -/
theorem below_form_transfer_snoc {A B : State} {c e : Card} {a : Anchor}
    (hface : (B.piles a).faceUp = (A.piles a).faceUp ++ [c])
    (hhid : (B.piles a).hidden = (A.piles a).hidden)
    (hmem : e ∈ (B.piles a).faceUp) (hec : e ≠ c)
    (hseat : below e (B.piles a).faceUp ≠ [] ∨
      ((B.piles a).hidden = [] ∧ e.rank = Rank.king))
    (hdisj : fromCard e (B.piles a).faceUp = [e] ∨ B.pileOfTop e.twin ≠ none)
    (hdisjA : B.pileOfTop e.twin ≠ none → A.pileOfTop e.twin ≠ none) :
    e ∈ (A.piles a).faceUp ∧
      (below e (A.piles a).faceUp ≠ [] ∨
        ((A.piles a).hidden = [] ∧ e.rank = Rank.king)) ∧
      (fromCard e (A.piles a).faceUp = [e] ∨ A.pileOfTop e.twin ≠ none) := by
  have hmemA : e ∈ (A.piles a).faceUp := by
    rw [hface] at hmem
    rcases List.mem_append.mp hmem with h | h
    · exact h
    · rw [List.mem_singleton] at h
      exact absurd h hec
  refine ⟨hmemA, ?_, ?_⟩
  · rcases hseat with h | h
    · exact Or.inl (by rw [hface, CommuteStep.below_append_of_mem hmemA] at h; exact h)
    · exact Or.inr ⟨by rw [← hhid]; exact h.1, h.2⟩
  · rcases hdisj with h | h
    · exfalso
      rw [hface, CommuteStep.fromCard_append_of_mem hmemA] at h
      obtain ⟨r, hr⟩ := tfc_fromCard_cons_head (A.piles a).faceUp hmemA
      rw [hr] at h
      exact absurd h (by simp)
    · exact Or.inr (hdisjA h)

/-- **A PULL CANNOT CREATE THE S-LIVENESS OF A CARD OTHER THAN `c`, `c.twin`.**

This is `BlockKit.canRaise_of_pull_of_ne`'s S-grade counterpart, and it needs
no cargo commutation: the flat characterization
(`canRaiseS_below_form`) reads only `nextUp`, the *piles* map and the
`below`/`fromCard` split, all of which the pull edits in one place. -/
theorem canRaiseS_of_pull_of_ne_twin {A B : State} {c e : Card} {b : Base}
    (hA : A.WF) (hstep : State.step A (Move.foundToTab c b) = some B)
    (he : CanRaiseS B e) (hec : e ≠ c) (het : e ≠ c.twin) :
    CanRaiseS A e := by
  have hB : B.WF := step_wf hA hstep
  obtain ⟨hcp, hBpull⟩ : A.canPlace c b = true ∧ B = CommuteStep.pullSt A c b := by
    obtain ⟨c', htop, hc', hcp, heq⟩ := step_foundToTab_inv hstep
    exact ⟨hcp, heq⟩
  obtain ⟨k, hk⟩ := CommuteStep.exists_tgt_of_canPlace hcp
  obtain ⟨hnextB, a, hmemB, hseatB, hdisjB⟩ := (canRaiseS_below_form hB).mp he
  have hnextA : A.nextUp e = true :=
    ValleyNoPull.nextUp_of_pull_of_ne hA hstep hec hnextB
  have hetc : e.twin ≠ c := fun h => het (by rw [← card_twin_twin e, h])
  have hdisjA : B.pileOfTop e.twin ≠ none → A.pileOfTop e.twin ≠ none :=
    fun h => pileOfTop_twin_prev_of_pull hA hB hBpull hk hetc h
  have hdata : e ∈ (A.piles a).faceUp ∧
      (below e (A.piles a).faceUp ≠ [] ∨
        ((A.piles a).hidden = [] ∧ e.rank = Rank.king)) ∧
      (fromCard e (A.piles a).faceUp = [e] ∨ A.pileOfTop e.twin ≠ none) := by
    cases b with
    | inl kk =>
        have hpile : ∀ j : Anchor, (B.piles j) =
            (if j = kk then (⟨[], [c]⟩ : Pile) else A.piles j) := by
          intro j
          rw [hBpull]
          exact CommuteStep.pullSt_piles_inl_apply A c kk j
        by_cases hak : a = kk
        · exfalso
          have hface : (B.piles a).faceUp = [c] := by
            rw [hpile a, ite_eq_left hak]
          rw [hface] at hmemB
          rw [List.mem_singleton] at hmemB
          exact hec hmemB
        · have hface : (B.piles a).faceUp = (A.piles a).faceUp := by
            rw [hpile a, ite_eq_right hak]
          have hhid : (B.piles a).hidden = (A.piles a).hidden := by
            rw [hpile a, ite_eq_right hak]
          exact below_form_transfer_eq hface hhid hmemB hseatB hdisjB hdisjA
    | inr z =>
        have hz : A.pileOfTop z = some k := hk
        have hpile : ∀ j : Anchor, (B.piles j) =
            (if j = k then ({ A.piles k with faceUp := (A.piles k).faceUp ++ [c] } : Pile)
              else A.piles j) := by
          intro j
          rw [hBpull]
          exact CommuteStep.pullSt_piles_inr_apply A c z k hz j
        by_cases hak : a = k
        · have hkdata : e ∈ (A.piles k).faceUp ∧
              (below e (A.piles k).faceUp ≠ [] ∨
                ((A.piles k).hidden = [] ∧ e.rank = Rank.king)) ∧
              (fromCard e (A.piles k).faceUp = [e] ∨ A.pileOfTop e.twin ≠ none) := by
            have hmemk : e ∈ (B.piles k).faceUp := by rw [← hak]; exact hmemB
            have hseatk : below e (B.piles k).faceUp ≠ [] ∨
                ((B.piles k).hidden = [] ∧ e.rank = Rank.king) := by
              rw [← hak]
              exact hseatB
            have hdisjk : fromCard e (B.piles k).faceUp = [e] ∨
                B.pileOfTop e.twin ≠ none := by
              rw [← hak]
              exact hdisjB
            have hface : (B.piles k).faceUp = (A.piles k).faceUp ++ [c] := by
              rw [hpile k, ite_eq_left rfl]
            have hhid : (B.piles k).hidden = (A.piles k).hidden := by
              rw [hpile k, ite_eq_left rfl]
            exact below_form_transfer_snoc hface hhid hmemk hec hseatk hdisjk hdisjA
          rw [← hak] at hkdata
          exact hkdata
        · have hface : (B.piles a).faceUp = (A.piles a).faceUp := by
            rw [hpile a, ite_eq_right hak]
          have hhid : (B.piles a).hidden = (A.piles a).hidden := by
            rw [hpile a, ite_eq_right hak]
          exact below_form_transfer_eq hface hhid hmemB hseatB hdisjB hdisjA
  exact (canRaiseS_below_form hA).mpr ⟨hnextA, a, hdata.1, hdata.2.1, hdata.2.2⟩

/-- **THE CREATION FORM.**  A pull of `c` can only create S-liveness among
`{c, c.twin}`. -/
theorem canRaiseS_pull_creation {A B : State} {c e : Card} {b : Base}
    (hA : A.WF) (hstep : State.step A (Move.foundToTab c b) = some B)
    (he : CanRaiseS B e) :
    e = c ∨ e = c.twin ∨ CanRaiseS A e := by
  by_cases h1 : e = c
  · exact Or.inl h1
  · by_cases h2 : e = c.twin
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (canRaiseS_of_pull_of_ne_twin hA hstep he h1 h2))

/-- **THE LOCAL DICHOTOMY.**  An S-live card at the pull's landing is either
the pulled card's twin, or was already S-live before the pull. -/
theorem local_dichotomy {A B : State} {c e : Card} {b : Base}
    (hA : A.WF) (hstep : State.step A (Move.foundToTab c b) = some B)
    (he : CanRaiseS B e) (hec : e ≠ c) :
    e = c.twin ∨ CanRaiseS A e := by
  by_cases het : e = c.twin
  · exact Or.inl het
  · exact Or.inr (canRaiseS_of_pull_of_ne_twin hA hstep he hec het)

/-! ## §3. The exact reduction of `LandingLivePair` -/

/-- **`LandingThirdFreeAt A B c b`** — the third-suit exclusion read AT THE
PULL CROSSING: no card of a third suit is S-live both before and after the
pull of `c`.  (The `b` binder only names the pull's base.) -/
def LandingThirdFreeAt (A B : State) (c : Card) (b : Base) : Prop :=
  ∀ e, CanRaiseS A e → CanRaiseS B e →
    e.suit = c.suit ∨ e.suit = c.twin.suit

/-- **THE REDUCTION: dichotomy ⟹ the landing live pair.**  Given the twin's
liveness at the landing and the third-suit exclusion *at the crossing*,
`LandingLivePair B c` follows from `local_dichotomy`. -/
theorem landingLivePair_of_local {A B : State} {c : Card} {b : Base}
    (hA : A.WF) (hstep : State.step A (Move.foundToTab c b) = some B)
    (htwin : CanRaiseS B c.twin) (hthird : LandingThirdFreeAt A B c b) :
    Mech.LandingLivePair B c := by
  refine ⟨htwin, ?_⟩
  intro e he
  by_cases h1 : e = c
  · exact Or.inl (congrArg Card.suit h1)
  · by_cases h2 : e = c.twin
    · exact Or.inr (congrArg Card.suit h2)
    · rcases local_dichotomy hA hstep he h1 with h | h
      · exact absurd h h2
      · exact hthird e h he

/-- **THE EXACT REDUCTION.**  Over a single pull, `LandingLivePair` at the
landing is *equivalent* to (twin live at the landing) ∧ (no third-suit card
survives the pull).  Nothing is lost and nothing is weakened: the converse
direction is the definition. -/
theorem landingLivePair_iff_local {A B : State} {c : Card} {b : Base}
    (hA : A.WF) (hstep : State.step A (Move.foundToTab c b) = some B) :
    Mech.LandingLivePair B c ↔
      CanRaiseS B c.twin ∧ LandingThirdFreeAt A B c b := by
  constructor
  · intro h
    exact ⟨h.1, fun e _ he => h.2 e he⟩
  · rintro ⟨ht, h3⟩
    exact landingLivePair_of_local hA hstep ht h3

/-! ## §4. The bottom/landing interchange (documentation of the brief's Q3) -/

/-- **`B` AND `F` HAVE THE SAME LIVE SET.**  The brief asks whether
`LandingLivePair` may equivalently be read at the bottom `F`.  It can: the
free tail `B → F` preserves every card's S-license in *both* directions
(`Mech.canRaiseS_landing_iff`, which is an iff).  So `LandingLivePair` is a
cargo-fibre invariant along `post`, and the two readings are interchangeable. -/
theorem landingLivePair_landing_iff {B F : State} {post : List Move} {c : Card}
    (hB : B.WF) (hplay : ShufflePlayW B post F)
    (hfree : ∀ m ∈ post, ValleyElim.FreeMove m) :
    Mech.LandingLivePair B c ↔ Mech.LandingLivePair F c := by
  constructor
  · intro h
    refine ⟨(Mech.canRaiseS_landing_iff hB hplay hfree c.twin).mp h.1, ?_⟩
    intro e he
    exact h.2 e ((Mech.canRaiseS_landing_iff hB hplay hfree e).mpr he)
  · intro h
    refine ⟨(Mech.canRaiseS_landing_iff hB hplay hfree c.twin).mpr h.1, ?_⟩
    intro e he
    exact h.2 e ((Mech.canRaiseS_landing_iff hB hplay hfree e).mp he)

/-! ## §5. The `pre`-free case: the third-suit exclusion is PROVED -/

/-- A split letter is either free (draw / slide) or a pull.  This is the
whole alphabet of the prefix `pre` of a genuine valley split. -/
def FreeOrPull (m : Move) : Prop :=
  ValleyElim.FreeMove m ∨ ∃ (c : Card) (b : Base), m = Move.foundToTab c b

/-- **A PULL CREATION SCAN.**  Along a witness play whose letters are free or
pull, an S-live card at the end is either S-live at the start or is one of the
cards pulled along the way (or its twin).  Free letters preserve the S-license
exactly; a pull creates nothing but the pulled card and its twin
(`canRaiseS_of_pull_of_ne_twin`). -/
theorem live_of_play_creation {u A' : State} {pre : List Move}
    (hplay : ShufflePlayW u pre A') :
    ∀ (_ : u.WF) (_ : ∀ m ∈ pre, FreeOrPull m) (e : Card), CanRaiseS A' e →
      CanRaiseS u e ∨
        ∃ (α : List Move) (z : Card) (bz : Base) (β : List Move),
          pre = α ++ Move.foundToTab z bz :: β ∧ (e = z ∨ e = z.twin) := by
  induction hplay with
  | nil st => intro _ _ e he; exact Or.inl he
  | @cons st s1 W m ρ hrev hstep hrest ih =>
      intro hwf hall e he
      have hwfS : s1.WF := step_wf hwf hstep
      have hallTail : ∀ x ∈ ρ, FreeOrPull x :=
        fun x hx => hall x (List.mem_cons_of_mem m hx)
      rcases ih hwfS hallTail e he with hpre | ⟨α, z, bz, β, heq, hmem⟩
      · rcases hall m (List.mem_cons_self ..) with hfree | ⟨zc, bc, hm⟩
        · have hlive : CanRaiseS st e := by
            rcases hfree with rfl | ⟨cc, bb, rfl⟩
            · exact (ValleyElim.canRaiseS_congr_found_piles hwf hwfS
                (stepDraw_found hstep).symm (stepDraw_piles hstep).symm e).mpr hpre
            · exact (Bridge.canRaiseS_cargoLeg_iff hwf ⟨cc, bb, hstep, hrev⟩ e).mpr hpre
          exact Or.inl hlive
        · subst hm
          by_cases h1 : e = zc
          · exact Or.inr ⟨[], zc, bc, ρ, rfl, Or.inl h1⟩
          · by_cases h2 : e = zc.twin
            · exact Or.inr ⟨[], zc, bc, ρ, rfl, Or.inr h2⟩
            · exact Or.inl (canRaiseS_of_pull_of_ne_twin hwf hstep hpre h1 h2)
      · exact Or.inr ⟨m :: α, z, bz, β, by rw [List.cons_append, heq], hmem⟩

/-- **EVERY CARD LIVE BEFORE THE VALLEY PULL IS AN EARLIER-PULL CARD.**  From
a saturated start, nothing is live; the only letters that create S-liveness
are the pulls, and a pull creates only its own card and that card's twin.  So
the live set just before the valley pull is a subset of `{z, z.twin}` over the
earlier pulls `z` of `pre`. -/
theorem live_before_valley_pull {u A' : State} {pre : List Move}
    (hplay : ShufflePlayW u pre A') (huwf : u.WF) (hsat : SSaturated u)
    (hall : ∀ m ∈ pre, FreeOrPull m) :
    ∀ e, CanRaiseS A' e →
      ∃ (α : List Move) (z : Card) (bz : Base) (β : List Move),
        pre = α ++ Move.foundToTab z bz :: β ∧ (e = z ∨ e = z.twin) := by
  intro e he
  rcases live_of_play_creation hplay huwf hall e he with h | h
  · exact absurd h (hsat e)
  · exact h

/-- **THE THIRD-SUIT VIOLATION IS ALWAYS AN EARLIER-PULL CARD.**  A third-suit
S-live card at the landing is (i) already live before the valley pull
(`local_dichotomy`) and hence (ii) the card of an earlier pull in `pre`, or its
twin.  This is the exact shape the residual must kill. -/
theorem landing_third_suit_earlier_pull
    {u A' B : State} {pre : List Move} {c e : Card} {b : Base}
    (hplay : ShufflePlayW u pre A') (huwf : u.WF) (hsat : SSaturated u)
    (hall : ∀ m ∈ pre, FreeOrPull m)
    (hstep : State.step A' (Move.foundToTab c b) = some B)
    (he : CanRaiseS B e) (hec : e ≠ c) (het : e ≠ c.twin) :
    ∃ (α : List Move) (z : Card) (bz : Base) (β : List Move),
      pre = α ++ Move.foundToTab z bz :: β ∧ (e = z ∨ e = z.twin) := by
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hplay huwf
  exact live_before_valley_pull hplay huwf hsat hall e
    (canRaiseS_of_pull_of_ne_twin hA' hstep he hec het)

/-- **THE THIRD-SUIT EXCLUSION IS FREE WHEN `pre` IS FREE.**  If every letter
before the valley pull is a free letter, the start's saturation transports to
`A'` (`Bridge.canRaiseS_of_free_play_iff`), so *nothing* is S-live just before
the pull and the crossing condition is vacuous. -/
theorem landingThirdFree_of_free_pre
    {u A' B : State} {pre : List Move} {c : Card} {b : Base}
    (huwf : u.WF) (hsat : SSaturated u) (hpre : ShufflePlayW u pre A')
    (hfreePre : ∀ m ∈ pre, ValleyElim.FreeMove m)
    (hstep : State.step A' (Move.foundToTab c b) = some B) :
    LandingThirdFreeAt A' B c b := by
  intro e hA' _
  exact absurd ((Bridge.canRaiseS_of_free_play_iff hpre hfreePre huwf e).mpr hA')
    (hsat e)

/-- **THE LANDING LIVE PAIR WHEN `pre` IS FREE**: only the twin clause is
left. -/
theorem landingLivePair_of_free_pre
    {u A' B : State} {pre : List Move} {c : Card} {b : Base}
    (huwf : u.WF) (hsat : SSaturated u) (hpre : ShufflePlayW u pre A')
    (hfreePre : ∀ m ∈ pre, ValleyElim.FreeMove m)
    (hstep : State.step A' (Move.foundToTab c b) = some B)
    (htwin : CanRaiseS B c.twin) :
    Mech.LandingLivePair B c := by
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  exact landingLivePair_of_local hA' hstep htwin
    (landingThirdFree_of_free_pre huwf hsat hpre hfreePre hstep)

/-! ## §6. The residual at the split level, and its exactness -/

/-- **`SplitLandingResidual`** — the two clauses of `LandingLivePair` read at
the pull crossing of every split.  Clause 2 is `LandingThirdFreeAt`, i.e. "no
third-suit card survives the pull", which by `local_dichotomy` is exactly the
third-suit exclusion at the landing. -/
def SplitLandingResidual : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    ∀ (A' B : State), ShufflePlayW u pre A' →
      State.step A' (Move.foundToTab c b) = some B →
      CanRaiseS B c.twin ∧ LandingThirdFreeAt A' B c b

/-- **`SplitLandingResidual` gives `LandingAll`.** -/
theorem landingAll_of_splitLandingResidual (h : SplitLandingResidual) :
    Landing.LandingAll := by
  intro u v ρ F left right c d b pre post tail hs A' B hpre hstep
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre hs.1
  exact (landingLivePair_iff_local hA' hstep).mpr
    (h u v ρ F left right c d b pre post tail hs A' B hpre hstep)

/-- **`LandingAll` gives `SplitLandingResidual`** — the residual is not a
weakening. -/
theorem splitLandingResidual_of_landingAll (h : Landing.LandingAll) :
    SplitLandingResidual := by
  intro u v ρ F left right c d b pre post tail hs A' B hpre hstep
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre hs.1
  exact (landingLivePair_iff_local hA' hstep).mp
    (h u v ρ F left right c d b pre post tail hs A' B hpre hstep)

/-- **THE RESIDUAL IS EXACTLY `LandingAll`.** -/
theorem splitLandingResidual_iff_landingAll :
    SplitLandingResidual ↔ Landing.LandingAll :=
  ⟨landingAll_of_splitLandingResidual, splitLandingResidual_of_landingAll⟩

/-- **THE RESIDUAL IS EXACTLY `SplitLivePair`** (via
`Landing.landingAll_iff_splitLivePair`). -/
theorem splitLivePair_of_splitLandingResidual (h : SplitLandingResidual) :
    SplitKit.SplitLivePair :=
  Landing.landingAll_iff_splitLivePair.mp (landingAll_of_splitLandingResidual h)

/-- **THE TWIN-ONLY RESIDUAL.**  The first clause of `SplitLandingResidual`
alone. -/
def SplitLandingTwin : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    ∀ (A' B : State), ShufflePlayW u pre A' →
      State.step A' (Move.foundToTab c b) = some B →
      CanRaiseS B c.twin

/-- **FREE `pre` KILLS THE WHOLE THIRD-SUIT HALF.**  If every split's `pre` is
free, then `SplitLivePair` follows from the twin clause `SplitLandingTwin`
alone — the third-suit exclusion is not an input in that case. -/
theorem splitLandingResidual_of_free_pre_twin
    (hpre : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
      ∀ m ∈ pre, ValleyElim.FreeMove m)
    (htwin : SplitLandingTwin) : SplitLandingResidual := by
  intro u v ρ F left right c d b pre post tail hs A' B hplay hstep
  exact ⟨htwin u v ρ F left right c d b pre post tail hs A' B hplay hstep,
    landingThirdFree_of_free_pre hs.1 hs.2.1 hplay
      (hpre u v ρ F left right c d b pre post tail hs) hstep⟩

/-- **THE CAMPAIGN THEOREM MODULO THE TWIN CLAUSE, WHEN `pre` IS FREE.** -/
theorem splitLivePair_of_free_pre_twin
    (hpre : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
      ∀ m ∈ pre, ValleyElim.FreeMove m)
    (htwin : SplitLandingTwin) : SplitKit.SplitLivePair :=
  splitLivePair_of_splitLandingResidual (splitLandingResidual_of_free_pre_twin hpre htwin)

/-! ## §7. The sharpened survivor residual (only earlier-pull cards) -/

/-- **`SplitLandingSurvivor`** — the *sharpened* third-suit residual: the only
cards that can carry a third suit at the landing are the cards pulled earlier
in `pre` (or their twins) — `landing_third_suit_earlier_pull` — so the
exclusion only has to be checked on those, not on the whole deck. -/
def SplitLandingSurvivor : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    ∀ (A' B : State), ShufflePlayW u pre A' →
      State.step A' (Move.foundToTab c b) = some B →
      ∀ e, CanRaiseS B e →
        (∃ (α : List Move) (z : Card) (bz : Base) (β : List Move),
          pre = α ++ Move.foundToTab z bz :: β ∧ (e = z ∨ e = z.twin)) →
        e.suit = c.suit ∨ e.suit = c.twin.suit

/-- **THE RESIDUAL FROM ITS TWO SHARPENED HALVES.**  `SplitLandingTwin` plus
`SplitLandingSurvivor` (and the alphabet hypothesis on `pre`) give the full
`SplitLandingResidual`; the third-suit half is only consulted on the
earlier-pull cards. -/
theorem splitLandingResidual_of_twin_survivor
    (hall : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
      ∀ m ∈ pre, FreeOrPull m)
    (htwin : SplitLandingTwin) (hsurv : SplitLandingSurvivor) :
    SplitLandingResidual := by
  intro u v ρ F left right c d b pre post tail hs A' B hplay hstep
  refine ⟨htwin u v ρ F left right c d b pre post tail hs A' B hplay hstep, ?_⟩
  intro e hA' hB
  by_cases h1 : e = c
  · exact Or.inl (congrArg Card.suit h1)
  · by_cases h2 : e = c.twin
    · exact Or.inr (congrArg Card.suit h2)
    · exact hsurv u v ρ F left right c d b pre post tail hs A' B hplay hstep e hB
        (live_before_valley_pull hplay hs.1 hs.2.1
          (hall u v ρ F left right c d b pre post tail hs) e hA')

#check @canRaiseS_below_form
#check @canRaiseS_of_pull_of_ne_twin
#check @local_dichotomy
#check @landingLivePair_iff_local
#check @landingLivePair_landing_iff
#check @live_of_play_creation
#check @live_before_valley_pull
#check @landing_third_suit_earlier_pull
#check @landingThirdFree_of_free_pre
#check @landingLivePair_of_free_pre
#check @SplitLandingResidual
#check @splitLandingResidual_iff_landingAll
#check @splitLivePair_of_splitLandingResidual
#check @splitLivePair_of_free_pre_twin

#print axioms canRaiseS_below_form
#print axioms pullSt_piles_of_ne
#print axioms pileOfTop_twin_prev_of_pull
#print axioms below_form_transfer_eq
#print axioms below_form_transfer_snoc
#print axioms canRaiseS_of_pull_of_ne_twin
#print axioms canRaiseS_pull_creation
#print axioms local_dichotomy
#print axioms landingLivePair_of_local
#print axioms landingLivePair_iff_local
#print axioms landingLivePair_landing_iff
#print axioms live_of_play_creation
#print axioms live_before_valley_pull
#print axioms landing_third_suit_earlier_pull
#print axioms landingThirdFree_of_free_pre
#print axioms landingLivePair_of_free_pre
#print axioms landingAll_of_splitLandingResidual
#print axioms splitLandingResidual_of_landingAll
#print axioms splitLandingResidual_iff_landingAll
#print axioms splitLivePair_of_splitLandingResidual
/-! ## §8. Composition with the mechanism: the full chain -/

/-- **`SplitLandingResidual` + `SplitBlock` give `MechanismResidual`.**  The
landing clause is the residual of this card; the cover clause is
`Mech.coverEvent_of_block` from `SplitBlock` (`BlockKit`'s half).  This is
exactly the brief's "`LandingLivePair` + `SplitBlock` is the whole remaining
content". -/
theorem mechanismResidual_of_splitLanding_and_block
    (hl : SplitLandingResidual) (hb : SplitKit.SplitBlock) : Mech.MechanismResidual := by
  intro u v ρ F left right c d b pre post tail hs
  have hk := hs
  obtain ⟨huwf, -, -, -, -, -, -, hleft, -, hshape, hfree, -⟩ := hs
  obtain ⟨A', hpre, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hleft pre (Move.foundToTab c b :: post) hshape
  cases hrest with
  | @cons _ B _ _ _ hrev hstep hpost =>
      have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
      have hB : B.WF := step_wf hA' hstep
      have hcanB : CanRaise B c := ValleyStep.pull_card_canRaise hA' hstep
      obtain ⟨-, hSc, -, -⟩ := SplitKit.splitHyp_green hk
      have hblock : ¬ CanRaise F c := hb u v ρ F left right c d b pre post tail hk
      refine ⟨A', B, hpre, hstep, hpost, ?_,
        Mech.coverEvent_of_block hB hpost hfree hcanB hSc hblock⟩
      exact (landingLivePair_iff_local hA' hstep).mpr
        (hl u v ρ F left right c d b pre post tail hk A' B hpre hstep)

/-- **THE FULL CHAIN FROM THIS CARD'S RESIDUAL.**  `SplitLandingResidual`
(the exact landing reduction) plus `SplitBlock` (the cover half) plus the
choice-free shortest-play interface give `SatDifferForkWF`. -/
theorem satDifferForkWF_of_splitLanding_drainClosed
    (hl : SplitLandingResidual) (hb : SplitKit.SplitBlock)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  Mech.satDifferForkWF_of_mechanismResidual_drainClosed
    (mechanismResidual_of_splitLanding_and_block hl hb) hmin

/-! ## §9. Why the `c.twin` exception is real (structural, not an artefact) -/

/-- **AT THE PRE-PULL STATE, `c` TOPS NO PILE.**  `c` is the foundation top, so
it is on no pile (`CommuteStep.not_top_of_found`); this is exactly the `expose`
clause of its flat S-witness failing. -/
theorem pull_card_not_pile_top {A B : State} {c : Card} {b : Base}
    (hA : A.WF) (hstep : State.step A (Move.foundToTab c b) = some B) :
    A.pileOfTop c = none := by
  obtain ⟨c', htop, hc', -, -⟩ := step_foundToTab_inv hstep
  rw [hc'] at htop
  have hfound : c ∈ A.found c.suit := lastOf_mem htop
  cases hp : A.pileOfTop c with
  | none => rfl
  | some k =>
      exact absurd ((pileOfTop_eq_some_iff hA).mp hp)
        (CommuteStep.not_top_of_found hA hfound k)

/-- **AT THE LANDING, `c` TOPS THE PULL'S TARGET PILE.** -/
theorem pull_card_pile_top_at_landing {A B : State} {c : Card} {b : Base}
    (hB : B.WF) (hstep : State.step A (Move.foundToTab c b) = some B) :
    ∃ k : Anchor, B.pileOfTop c = some k := by
  obtain ⟨c', htop0, hc', hcp, heq⟩ := step_foundToTab_inv hstep
  obtain ⟨k, hk⟩ := CommuteStep.exists_tgt_of_canPlace hcp
  refine ⟨k, ?_⟩
  have htop : (B.piles k).top = some c := by
    rw [heq]
    exact CommuteStep.pullSt_top_written hk
  exact (pileOfTop_eq_some_iff hB).mpr htop

/-- **THE LANDING SUPPLIES `c.twin`'s HATCH LICENCE FOR FREE.**  In the flat
characterization, the clause "the run above the card is empty, or the card's
twin tops some pile" is `run = [] ∨ pileOfTop c.twin ≠ none`
(`canRaiseS_below_form`).  For `c.twin` the twin is `c`, which the pull has
just made the target pile's top — so that clause is *always* satisfied at the
landing and never at `A`.  Hence `CanRaiseS B c.twin` reduces to the
foundation gate plus the exposure/seat data at `c.twin`. -/
theorem canRaiseS_twin_of_landing {A B : State} {c : Card} {b : Base}
    (hB : B.WF) (hstep : State.step A (Move.foundToTab c b) = some B)
    (hnext : B.nextUp c.twin = true) {a : Anchor}
    (hmem : c.twin ∈ (B.piles a).faceUp)
    (hseat : below c.twin (B.piles a).faceUp ≠ [] ∨
      ((B.piles a).hidden = [] ∧ c.twin.rank = Rank.king)) :
    CanRaiseS B c.twin := by
  obtain ⟨k, htop⟩ := pull_card_pile_top_at_landing hB hstep
  exact (canRaiseS_below_form hB).mpr
    ⟨hnext, a, hmem, hseat, Or.inr (by rw [card_twin_twin, htop]; simp)⟩

#check @splitLandingResidual_of_free_pre_twin
#print axioms splitLandingResidual_of_free_pre_twin
#print axioms splitLivePair_of_free_pre_twin
#print axioms SplitLandingSurvivor
#print axioms splitLandingResidual_of_twin_survivor
#print axioms mechanismResidual_of_splitLanding_and_block
#print axioms satDifferForkWF_of_splitLanding_drainClosed
#print axioms pull_card_not_pile_top
#print axioms pull_card_pile_top_at_landing
#print axioms canRaiseS_twin_of_landing

end LandKit
