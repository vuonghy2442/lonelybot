import Orig2.ForkSurvivor
import Orig2.ForkThirdLive
import Orig2.ForkMountainAccount

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Orig2/ForkMate -- the `z = e` case of `Surv.SurvivorMateBracket` is EMPTY

READ-ONLY scratch (no source edit, no commit).  Zero `sorry`, zero
`Classical.choice`, zero `native_decide`; axiom battery at the tail.

## Verdict

The `z = e` disjunct of the pinned residual `Surv.SurvivorMateBracket`
(`Orig2/ForkSurvivor.lean:497`) is **not real content: it is impossible.**
The reason is not local to the survivor -- it is `SplitHyp`'s shortest-play
conjunct.  Any same-card bracket `pull z ; gamma ; raise z` with a READ-SAFE
interior, `z` arbitrary, is deletable (`NonforkKit.bracket_delete_gen`), so a
`SplitHyp` contains **no** such bracket at all (`splitHyp_not_readBracket`).
In particular the pinned witness with `z = e` cannot exist, so every witness of
`Surv.SurvivorMateBracket` has `e = z.twin` (`survivorMateBracket_witness_twin`)
and the pinned residual is *equivalent* to its twin-only form
(`survivorMateBracket_iff_twin`).

Two independent second reasons are recorded, both about the prefix `pre`:

* `self_pull_nextUp` / `self_pull_canRaise`: after `pull e` the card `e` is
  **already** `nextUp` and **already** vanilla-raisable at the pull's landing.
  The licence therefore never forces the returning `raise e`; the raise is a
  choice, not a consequence (`rungAt_self_pull` is the arithmetic).
* `noSigma_after_self_pull_of_live`: if the play continues (free-or-pull) to a
  state where `e` is still S-live, then the rung is frozen at `e.rank.toIdx`,
  so the whole continuation is `e.suit`-**silent** (`ThirdLive.NoSigmaLetter`).
  This is the read-safety reduction: only the two *slide* clauses of
  `R12.ReadOK e` survive (`readOK_of_freeOrPull_of_noSigma`).
* `self_pull_raise_not_forced` / `not_selfPullRaiseInPre`: a concrete kernel
  witness (`ExistRefute`'s board) shows that a free-or-pull prefix which
  contains `pull e` and ends with `e` live need **not** contain `raise e`.  So
  even the existence half of the `z = e` bracket is not a local theorem; it
  would have to come from minimality -- and minimality kills the bracket
  outright (§1).
-/

namespace Mate

open ValleyElim

/-! ## §1. No read-safe same-card bracket exists at a `SplitHyp` -/

/-- **THE DECISIVE FACT.**  At every `SplitHyp` there is **no** same-card
bracket with a read-safe interior, for **any** card `z`.  The bracket's raise
bubbles left across the read-safe interior (`R12.raiseSwaps_of_read`) and the
adjacent `pull z ; raise z` pair is deleted (`NonforkKit.bracket_delete_gen`),
strictly shortening the play -- contradicting the split's shortest-play
conjunct.  (This is the deletion half of
`ThirdLive.landingThirdSuitFree_of_thirdBracketRead`
(`Orig2/ForkThirdResidual.lean:114`), stated without its `ThirdBracketRead`
hypothesis, so it applies to the pinned residual's witness directly.) -/
theorem splitHyp_not_readBracket
    {u v : State} {rho : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hs : SplitKit.SplitHyp u v rho F left right c d b pre post tail)
    {α γ β : List Move} {z : Card} {bz : Base} {P Q : State}
    (hρ : rho = α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z :: β)
    (hα : ShufflePlayW u α P)
    (hstep : State.step P (Move.foundToTab z bz) = some Q)
    (hread : ∀ q ∈ γ, R12.ReadOK z q) : False := by
  obtain ⟨huwf, -, -, hplay, -, hmin, -, -, -, -, -, -⟩ := hs
  have hPwf : P.WF := SatDifferCensus.ShufflePlayW.wf_end hα huwf
  have hQwf : Q.WF := step_wf hPwf hstep
  have hcanQ : CanRaise Q z := ValleyStep.pull_card_canRaise hPwf hstep
  have hplayQ : ShufflePlayW Q (γ ++ Move.tabToFound z :: β) v :=
    R12.bracket_landing_play hplay hρ hα hstep
  have hsw : NonforkKit.RaiseSwaps Q z γ :=
    R12.raiseSwaps_of_read hQwf hplayQ hcanQ hread
  obtain ⟨ρ', hρ'play, hlen⟩ :=
    NonforkKit.bracket_delete_gen huwf hplay hρ hα hstep hsw
  exact absurd hlen (Nat.not_lt.mpr (hmin ρ' hρ'play))

/-- **THE `z = e` CASE IS EMPTY.**  Specialisation of
`splitHyp_not_readBracket` to the pinned self-card: a bracket whose card is
`e` itself can never be read-safe inside a `SplitHyp`.  This is exactly what
the target `PairPullRaiseInPre` asks for when `z = e` (the pull in `pre` and the
matching raise later with `R12.ReadOK e` on the interior). -/
theorem splitHyp_self_bracket_impossible
    {u v : State} {rho : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hs : SplitKit.SplitHyp u v rho F left right c d b pre post tail)
    {α γ β : List Move} {e : Card} {bz : Base} {P Q : State}
    (hρ : rho = α ++ Move.foundToTab e bz :: γ ++ Move.tabToFound e :: β)
    (hα : ShufflePlayW u α P)
    (hstep : State.step P (Move.foundToTab e bz) = some Q)
    (hread : ∀ q ∈ γ, R12.ReadOK e q) : False :=
  splitHyp_not_readBracket hs hρ hα hstep hread

/-- **EVERY PINNED WITNESS IS A TWIN WITNESS.**  Under `SplitHyp`, the
witness of `Surv.SurvivorMateBracket` cannot have `e = z`; hence it has
`e = z.twin`.  The whole content of the pinned residual is the twin case. -/
theorem survivorMateBracket_witness_twin
    (h : Surv.SurvivorMateBracket)
    {u v : State} {rho : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hs : SplitKit.SplitHyp u v rho F left right c d b pre post tail)
    {A' B : State} (hpre : ShufflePlayW u pre A')
    (hstep : State.step A' (Move.foundToTab c b) = some B)
    {e : Card} (he : CanRaiseS B e) (h1 : e.suit ≠ c.suit)
    (h2 : e.suit ≠ c.twin.suit) :
    ∃ (α γ β : List Move) (z : Card) (bz : Base) (P Q : State),
      e = z.twin ∧
      rho = α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z :: β ∧
      ShufflePlayW u α P ∧
      State.step P (Move.foundToTab z bz) = some Q ∧
      (∀ q ∈ γ, R12.ReadOK z q) := by
  obtain ⟨α, γ, β, z, bz, P, Q, hmem, hρ, hα, hstepP, hread⟩ :=
    h u v rho F left right c d b pre post tail hs A' B hpre hstep e he h1 h2
  rcases hmem with hz | hz
  · exfalso
    rw [← hz] at hρ hstepP hread
    exact splitHyp_self_bracket_impossible hs hρ hα hstepP hread
  · exact ⟨α, γ, β, z, bz, P, Q, hz, hρ, hα, hstepP, hread⟩

/-- **THE TWIN-ONLY FORM OF THE PINNED RESIDUAL.**  The same statement as
`Surv.SurvivorMateBracket` with the disjunction replaced by the single clause
`e = z.twin`. -/
def SurvivorTwinBracket : Prop :=
  ∀ (u v : State) (rho : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v rho F left right c d b pre post tail →
    ∀ (A' B : State), ShufflePlayW u pre A' →
      State.step A' (Move.foundToTab c b) = some B →
      ∀ e : Card, CanRaiseS B e → e.suit ≠ c.suit → e.suit ≠ c.twin.suit →
      ∃ (α γ β : List Move) (z : Card) (bz : Base) (P Q : State),
        e = z.twin ∧
        rho = α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z :: β ∧
        ShufflePlayW u α P ∧
        State.step P (Move.foundToTab z bz) = some Q ∧
        (∀ q ∈ γ, R12.ReadOK z q)

/-- **THE PIN IS EXACTLY THE TWIN CASE.**  The pinned residual is *equivalent*
to its `z = e.twin` half; the `z = e` half is vacuous at every `SplitHyp`. -/
theorem survivorMateBracket_iff_twin :
    Surv.SurvivorMateBracket ↔ SurvivorTwinBracket := by
  constructor
  · intro h u v rho F left right c d b pre post tail hs A' B hpre hstep e he h1 h2
    exact survivorMateBracket_witness_twin h hs hpre hstep he h1 h2
  · intro h u v rho F left right c d b pre post tail hs A' B hpre hstep e he h1 h2
    obtain ⟨α, γ, β, z, bz, P, Q, hz, hρ, hα, hstepP, hread⟩ :=
      h u v rho F left right c d b pre post tail hs A' B hpre hstep e he h1 h2
    exact ⟨α, γ, β, z, bz, P, Q, Or.inr hz, hρ, hα, hstepP, hread⟩

/-- **THE PINNED RESIDUAL IS THE CONTAINMENT, NOT A BRACKET.**  If
`Surv.SurvivorMateBracket` holds, no third-suit card can be S-live at any
split's pull landing.  Combined with §1 (a read-safe witness cannot exist at a
`SplitHyp` anyway), this says the pin contributes no bracket content beyond the
containment itself: `Surv.SurvivorMateBracket` can only be proved by proving
that its survivor hypothesis is empty. -/
theorem survivorMateBracket_elim (h : Surv.SurvivorMateBracket)
    {u v : State} {rho : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hs : SplitKit.SplitHyp u v rho F left right c d b pre post tail)
    {A' B : State} (hpre : ShufflePlayW u pre A')
    (hstep : State.step A' (Move.foundToTab c b) = some B)
    {e : Card} (he : CanRaiseS B e) (h1 : e.suit ≠ c.suit)
    (h2 : e.suit ≠ c.twin.suit) : False :=
  ThirdLive.landingThirdSuitFree_of_thirdBracketRead
    (Surv.survivorMateBracket_thirdBracketRead h)
    u v rho F left right c d b pre post tail hs A' B hpre hstep e he h1 h2

/-- **THE BRACKET CANNOT BE A BRACKET INSIDE `pre`.**  The exact shape of the
target `PairPullRaiseInPre`: a same-card bracket `pull z ; γ ; raise z` whose
three parts all lie in the split's prefix, with `γ` read-safe for `z`.  This is
a `SplitHyp`-local contradiction by `splitHyp_not_readBracket` (the prefix is a
sub-word of `rho`). -/
theorem splitHyp_not_readBracket_in_pre
    {u v : State} {rho : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hs : SplitKit.SplitHyp u v rho F left right c d b pre post tail)
    {α γ β : List Move} {z : Card} {bz : Base} {P Q : State}
    (hpre : pre = α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z :: β)
    (hα : ShufflePlayW u α P)
    (hstep : State.step P (Move.foundToTab z bz) = some Q)
    (hread : ∀ q ∈ γ, R12.ReadOK z q) : False := by
  have hsk := hs
  obtain ⟨-, -, -, -, -, -, hρlr, -, -, hshape, -, hright⟩ := hs
  have hρ0 : rho = pre ++ (Move.foundToTab c b :: (post ++ right)) := by
    rw [hρlr, hshape, hright]
    simp only [List.cons_append, List.append_assoc]
  have hρ : rho = α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z ::
      (β ++ Move.foundToTab c b :: (post ++ right)) := by
    rw [hρ0, hpre]
    simp only [List.cons_append, List.append_assoc]
  exact splitHyp_not_readBracket hsk hρ hα hstep hread

/-- The twin's suit is third-suit too: if `e`'s suit differs from `c.twin`'s,
then `e.twin`'s suit differs from `c`'s. -/
theorem twin_suit_ne_of_third {e c : Card} (h2 : e.suit ≠ c.twin.suit) :
    e.twin.suit ≠ c.suit := by
  intro h
  exact h2 (by
    have h' := congrArg Suit.twin h
    simpa [Card.twin, Suit.twin_twin] using h')

/-- **THE TWIN WITNESS'S PULL LIES IN `pre`** (given the pull-free right leg of
the frozen branch).  The pull `pull z` of a bracket with `z = e.twin` cannot be
the valley pull (`z.suit ≠ c.suit`), cannot be in the free tail `post` (free
letters are not pulls), and cannot be in `right` (pull-free).  Hence it is a
letter of `pre`.  So in the twin case the surviving residual is again a
prefix-internal occurrence statement. -/
theorem twin_bracket_pull_in_pre
    {u v : State} {rho : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hs : SplitKit.SplitHyp u v rho F left right c d b pre post tail)
    (hnp : ∀ m ∈ right, ¬ Bubble.IsPull m)
    {α γ β : List Move} {z : Card} {bz : Base} {P Q : State}
    (hρ : rho = α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z :: β)
    {e : Card} (hz : e = z.twin) (h2 : e.suit ≠ c.twin.suit) :
    ∃ γ₁ γ₂ : List Move, pre = γ₁ ++ Move.foundToTab z bz :: γ₂ := by
  obtain ⟨-, -, -, -, -, -, hρlr, -, -, hshape, hfree, hright⟩ := hs
  have hρ0 : rho = pre ++ (Move.foundToTab c b :: (post ++ right)) := by
    rw [hρlr, hshape, hright]
    simp only [List.cons_append, List.append_assoc]
  have hmem : Move.foundToTab z bz ∈ rho := by rw [hρ]; simp
  rw [hρ0] at hmem
  have hzs : z.suit ≠ c.suit := by
    have hz' : z = e.twin := by rw [hz, card_twin_twin]
    rw [hz']
    exact twin_suit_ne_of_third h2
  rcases List.mem_append.mp hmem with hin | hin
  · exact List.mem_iff_append.mp hin
  · exfalso
    rcases List.mem_cons.mp hin with heq | hin'
    · injection heq with hzc _
      exact hzs (by rw [hzc])
    · rcases List.mem_append.mp hin' with hpost | hright'
      · rcases hfree _ hpost with hd | ⟨cc, bb, ht⟩
        · exact absurd hd (by simp)
        · exact absurd ht (by simp)
      · exact hnp _ hright' ⟨z, bz, rfl⟩

/-- **THE TWIN CASE RECOVERED FROM THE PIN.**  Under `Surv.SurvivorMateBracket`
and the pull-free right leg, the earlier pull of the survivor's rank-mate is a
pull of `e.twin`, and it sits in `pre`. -/
theorem survivorMateBracket_twin_pull_in_pre
    (h : Surv.SurvivorMateBracket)
    {u v : State} {rho : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hs : SplitKit.SplitHyp u v rho F left right c d b pre post tail)
    (hnp : ∀ m ∈ right, ¬ Bubble.IsPull m)
    {A' B : State} (hpre : ShufflePlayW u pre A')
    (hstep : State.step A' (Move.foundToTab c b) = some B)
    {e : Card} (he : CanRaiseS B e) (h1 : e.suit ≠ c.suit)
    (h2 : e.suit ≠ c.twin.suit) :
    ∃ (γ₁ γ₂ : List Move) (bz : Base),
      pre = γ₁ ++ Move.foundToTab e.twin bz :: γ₂ := by
  obtain ⟨α, γ, β, z, bz, P, Q, hz, hρ, -, -, -⟩ :=
    survivorMateBracket_witness_twin h hs hpre hstep he h1 h2
  rcases twin_bracket_pull_in_pre (P := P) (Q := Q) hs hnp hρ hz h2 with ⟨g1, g2, hpull⟩
  refine ⟨g1, g2, bz, ?_⟩
  rw [hz, card_twin_twin]
  exact hpull

/-! ## §2. The rung arithmetic: the self-pull already satisfies the licence -/

/-- **A `foundToTab` OF `e` LOWERS `e`'s RUNG TO `e`'s RANK INDEX.**  The
pull's found card must be `e` itself, which is the last slot of the (prefix)
foundation, so the top's rank index is the rung minus one. -/
theorem rungAt_self_pull {A B : State} {e : Card} {b : Base}
    (hwf : A.WF) (hstep : State.step A (Move.foundToTab e b) = some B) :
    rungAt B e.suit = e.rank.toIdx := by
  obtain ⟨c', htop, hc', -, -⟩ := step_foundToTab_inv hstep
  have hidx : e.rank.toIdx + 1 = rungAt A e.suit := by
    rw [hc'] at htop
    exact SatDifferCensus.foundTop_rank_succ hwf htop
  have hrung : rungAt B e.suit = rungAt A e.suit - 1 := by
    have h := rungAt_foundToTab hstep e.suit
    rw [ite_eq_left rfl] at h
    exact h
  omega

/-- `nextUp` is exactly "the card is its suit's frontier". -/
theorem nextUp_iff_rank_eq_rung {st : State} {e : Card} :
    st.nextUp e = true ↔ e.rank.toIdx = rungAt st e.suit := by
  unfold State.nextUp State.foundHeight rungAt
  constructor
  · intro h; exact of_decide_eq_true h
  · intro h; exact decide_eq_true h

/-- **`e` IS ALREADY `nextUp` AT THE PULL'S LANDING.**  No raise is needed for
the frontier licence. -/
theorem self_pull_nextUp {A B : State} {e : Card} {b : Base}
    (hwf : A.WF) (hstep : State.step A (Move.foundToTab e b) = some B) :
    B.nextUp e = true := by
  rw [nextUp_iff_rank_eq_rung, rungAt_self_pull hwf hstep]

/-- **`e` IS ALREADY VANILLA-RAISABLE AT THE PULL'S LANDING** (source:
`ValleyStep.pull_card_canRaise`, `Orig2/ForkValley.lean:90`).  A `raise e`
later in the play is therefore a *choice*, never a licence requirement. -/
theorem self_pull_canRaise {A B : State} {e : Card} {b : Base}
    (hwf : A.WF) (hstep : State.step A (Move.foundToTab e b) = some B) :
    CanRaise B e :=
  ValleyStep.pull_card_canRaise hwf hstep

/-- A `FreeOrPull` letter is never a raise. -/
theorem not_isRaise_of_freeOrPull {m : Move} (h : LandKit.FreeOrPull m) :
    ¬ Bubble.IsRaise m := by
  rintro ⟨c, hc⟩
  rcases h with hf | ⟨d, b, hd⟩
  · rcases hf with rfl | ⟨x, y, rfl⟩
    · cases hc
    · cases hc
  · rw [hd] at hc
    cases hc

/-- **THE CONTINUATION AFTER A SELF-PULL IS `e.suit`-SILENT.**  If the rest of
the play (`γ`, free-or-pull) ends at a state where `e` is still S-live, then the
rung cannot have dropped below `e.rank.toIdx` -- and it started there.  So no
pull of `e`'s suit can occur in `γ` (a second pull would have to lower the
rung again), and no raise can occur at all (`γ` is free-or-pull).  That is
exactly `ThirdLive.NoSigmaLetter e.suit` on every letter of `γ`. -/
theorem noSigma_after_self_pull_of_live
    {P Q A' : State} {e : Card} {bz : Base} {γ : List Move}
    (hPwf : P.WF) (hstep : State.step P (Move.foundToTab e bz) = some Q)
    (hplay : ShufflePlayW Q γ A')
    (hall : ∀ m ∈ γ, LandKit.FreeOrPull m)
    (hlive : CanRaiseS A' e) :
    ∀ m ∈ γ, ThirdLive.NoSigmaLetter e.suit m := by
  have hQwf : Q.WF := step_wf hPwf hstep
  have hA'wf : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hplay hQwf
  have hliveR : e.rank.toIdx = rungAt A' e.suit :=
    ThirdLive.rank_eq_rungAt_of_canRaiseS hA'wf hlive
  have hQrung : rungAt Q e.suit = e.rank.toIdx := rungAt_self_pull hPwf hstep
  have hno : ∀ m ∈ γ, ¬ Bubble.IsRaise m :=
    fun m hm => not_isRaise_of_freeOrPull (hall m hm)
  have hpull : pullsOf γ e.suit = 0 := by
    have h := MountainKit.pullsOf_add_rung_eq_of_no_raise hplay hno
      (σ := e.suit)
    omega
  have hraise : raisesOf γ e.suit = 0 :=
    MountainKit.raisesOf_eq_zero_of_no_raise hno
  exact ThirdLive.noSigma_iff_counts.mpr ⟨hpull, hraise⟩

/-- **THE READ-SAFETY REDUCTION.**  On a free-or-pull letter, `R12.ReadOK z`
reduces to (`z.suit`-silence) plus the two *slide* avoidance clauses: a pull of
another suit is read-safe unless it lands on `z`.  So after §2's rung argument
the only read-safety obligations left in the `z = e` interior are "no slide
moves `e`" and "no slide lands on `e`". -/
theorem readOK_of_freeOrPull_of_noSigma {z : Card} {q : Move}
    (hfp : LandKit.FreeOrPull q)
    (hns : ThirdLive.NoSigmaLetter z.suit q)
    (hslide : ∀ (x : Card) (b : Base), q = Move.tabToTab x b →
      x ≠ z ∧ b ≠ Sum.inr z)
    (hland : ∀ (x : Card) (b : Base), q = Move.foundToTab x b →
      b ≠ Sum.inr z) :
    R12.ReadOK z q := by
  rcases hfp with hfree | ⟨x, b, rfl⟩
  · rcases hfree with rfl | ⟨y, b', rfl⟩
    · exact R12.readOK_draw z
    · exact R12.readOK_slide_of_ne (hslide y b' rfl).1 (hslide y b' rfl).2
  · exact R12.readOK_pull_of_ne (hns.1 x b rfl) (hland x b rfl)

/-! ## §3. A concrete witness: `pull e` does **not** force `raise e` in `pre`

The board is `ExistRefute.u` (`Orig2/ForkExistRefute.lean:113`), whose heart
foundation is `[AH,...,H5]`.  The one-letter prefix `pre = [pull 5H -> 6C]` is
free-or-pull, is a witness shuffle, contains `pull 5H`, and lands with `5H`
S-live -- but no `raise 5H` follows inside `pre`.  So the `z = e` bracket's
*existence* is not a local consequence; §1 shows it is not a `SplitHyp`
consequence either. -/

/-- `[a] = l₁ ++ a :: l₂` forces `l₂ = []`. -/
theorem eq_nil_of_singleton_eq_append_cons {α : Type} {a : α} {l₁ l₂ : List α}
    (h : [a] = l₁ ++ a :: l₂) : l₂ = [] := by
  have hlen := congrArg List.length h
  simp only [List.length_cons, List.length_nil, List.length_append] at hlen
  have h0 : l₂.length = 0 := by omega
  exact List.length_eq_zero_iff.mp h0

theorem pull_self_shuffle : ShufflePlayW ExistRefute.u [ExistRefute.mPull] ExistRefute.B :=
  Walk.cons ExistRefute.pull_rev ExistRefute.step_pull (Walk.nil ExistRefute.B)

theorem pull_self_freeOrPull :
    ∀ m ∈ [ExistRefute.mPull], LandKit.FreeOrPull m := by
  intro m hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  subst hm
  exact Or.inr ⟨ExistRefute.H5, Sum.inr ExistRefute.C6, rfl⟩

/-- No `raise 5H` occurs after `pull 5H` inside the one-letter prefix.  The
list length pins the right side of the decomposition to `[]`. -/
theorem no_self_raise_in_one_letter_pre
    {γ₁ γ₂ : List Move}
    (h : [ExistRefute.mPull] =
      γ₁ ++ Move.foundToTab ExistRefute.H5 (Sum.inr ExistRefute.C6) :: γ₂) :
    Move.tabToFound ExistRefute.H5 ∉ γ₂ := by
  have h' : [Move.foundToTab ExistRefute.H5 (Sum.inr ExistRefute.C6)] =
      γ₁ ++ Move.foundToTab ExistRefute.H5 (Sum.inr ExistRefute.C6) :: γ₂ := h
  have h₂ : γ₂ = [] := eq_nil_of_singleton_eq_append_cons h'
  rw [h₂]
  exact List.not_mem_nil

/-- **THE LOCAL `z = e` PULL EXISTS BUT THE RAISE NEED NOT.**  Formally: there
is a well-formed start, a free-or-pull prefix, a witness shuffle, a card `e`
and a base `bz` such that `pre` contains `pull e`, `e` is S-live at the
landing, and no `raise e` occurs after the pull inside `pre`. -/
theorem self_pull_raise_not_forced :
    ∃ (u A' : State) (pre : List Move) (e : Card) (bz : Base),
      u.WF ∧ ShufflePlayW u pre A' ∧
      (∀ m ∈ pre, LandKit.FreeOrPull m) ∧
      (∃ γ₁ γ₂ : List Move, pre = γ₁ ++ Move.foundToTab e bz :: γ₂) ∧
      CanRaiseS A' e ∧
      ¬ ∃ γ₁ γ₂ : List Move,
          pre = γ₁ ++ Move.foundToTab e bz :: γ₂ ∧ Move.tabToFound e ∈ γ₂ := by
  refine ⟨ExistRefute.u, ExistRefute.B, [ExistRefute.mPull], ExistRefute.H5,
    Sum.inr ExistRefute.C6, ExistRefute.u_wf, pull_self_shuffle,
    pull_self_freeOrPull, ⟨[], [], rfl⟩, Surv.loop_B_H5_live, ?_⟩
  rintro ⟨γ₁, γ₂, h, hraise⟩
  exact no_self_raise_in_one_letter_pre h hraise

/-- **THE TARGET'S RAISE CLAUSE IS NOT A THEOREM.**  If `pre` is free-or-pull,
contains `pull e`, and ends with `e` S-live, one cannot conclude that `raise e`
occurs in `pre` after the pull.  (`PairPullRaiseInPre`'s existence half, with
exactly the brief's survivor hypothesis `CanRaiseS`.) -/
def SelfPullRaiseInPre : Prop :=
  ∀ (u A' : State) (pre : List Move) (e : Card) (bz : Base),
    ShufflePlayW u pre A' →
    (∀ m ∈ pre, LandKit.FreeOrPull m) →
    (∃ γ₁ γ₂ : List Move, pre = γ₁ ++ Move.foundToTab e bz :: γ₂) →
    CanRaiseS A' e →
    ∃ γ₁ γ₂ : List Move,
      pre = γ₁ ++ Move.foundToTab e bz :: γ₂ ∧ Move.tabToFound e ∈ γ₂

theorem not_selfPullRaiseInPre : ¬ SelfPullRaiseInPre := by
  intro h
  obtain ⟨u, A', pre, e, bz, -, hplay, hall, hmem, hlive, hcon⟩ :=
    self_pull_raise_not_forced
  exact hcon (h u A' pre e bz hplay hall hmem hlive)

/-- The same refutation with the survivor hypothesis weakened to `nextUp`
(which `CanRaiseS` implies); this is the strongest form of the local claim. -/
def SelfPullRaiseInPreNextUp : Prop :=
  ∀ (u A' : State) (pre : List Move) (e : Card) (bz : Base),
    ShufflePlayW u pre A' →
    (∀ m ∈ pre, LandKit.FreeOrPull m) →
    (∃ γ₁ γ₂ : List Move, pre = γ₁ ++ Move.foundToTab e bz :: γ₂) →
    A'.nextUp e = true →
    ∃ γ₁ γ₂ : List Move,
      pre = γ₁ ++ Move.foundToTab e bz :: γ₂ ∧ Move.tabToFound e ∈ γ₂

theorem not_selfPullRaiseInPre_nextUp : ¬ SelfPullRaiseInPreNextUp := by
  intro h
  obtain ⟨u, A', pre, e, bz, huwf, hplay, hall, hmem, hlive, hcon⟩ :=
    self_pull_raise_not_forced
  have hA'wf : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hplay huwf
  have hnext : A'.nextUp e = true := ThirdLive.nextUp_of_canRaiseS hA'wf hlive
  exact hcon (h u A' pre e bz hplay hall hmem hnext)

end Mate

#print axioms Mate.splitHyp_not_readBracket
#print axioms Mate.splitHyp_self_bracket_impossible
#print axioms Mate.survivorMateBracket_witness_twin
#print axioms Mate.SurvivorTwinBracket
#print axioms Mate.survivorMateBracket_iff_twin
#print axioms Mate.survivorMateBracket_elim
#print axioms Mate.splitHyp_not_readBracket_in_pre
#print axioms Mate.twin_suit_ne_of_third
#print axioms Mate.twin_bracket_pull_in_pre
#print axioms Mate.survivorMateBracket_twin_pull_in_pre
#print axioms Mate.rungAt_self_pull
#print axioms Mate.nextUp_iff_rank_eq_rung
#print axioms Mate.self_pull_nextUp
#print axioms Mate.self_pull_canRaise
#print axioms Mate.not_isRaise_of_freeOrPull
#print axioms Mate.noSigma_after_self_pull_of_live
#print axioms Mate.readOK_of_freeOrPull_of_noSigma
#print axioms Mate.eq_nil_of_singleton_eq_append_cons
#print axioms Mate.pull_self_shuffle
#print axioms Mate.pull_self_freeOrPull
#print axioms Mate.no_self_raise_in_one_letter_pre
#print axioms Mate.self_pull_raise_not_forced
#print axioms Mate.SelfPullRaiseInPre
#print axioms Mate.not_selfPullRaiseInPre
#print axioms Mate.SelfPullRaiseInPreNextUp
#print axioms Mate.not_selfPullRaiseInPre_nextUp
