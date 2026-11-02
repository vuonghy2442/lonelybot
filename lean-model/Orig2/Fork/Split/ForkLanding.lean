import Orig2.Fork.Local.ForkMechanism
import Orig2.Fork.Class.ForkLivePair

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false

/-!
# Orig2/ForkLanding — `Mech.LandingLivePair` at the pull landing

READ-ONLY scratch card: the repository source is not modified and nothing is
committed.  Zero `sorry`, zero `Classical.choice`, zero `native_decide`; the
axiom battery is at the tail.

## What is proved here

Let `B` be the state right after the split's pull `foundToTab c b` (the pull
landing) and `F` the split's bottom, with `ShufflePlayW B post F` and `post`
free.  `LandingLivePair B c` (`Orig2/Fork/Local/ForkMechanism.lean:310`) is

```
CanRaiseS B c.twin ∧
  (∀ e, CanRaiseS B e → e.suit = c.suit ∨ e.suit = c.twin.suit).
```

The card proves, kernel-checked:

* **`twinLivePair_of_fork` / `landingLivePair_of_bottomFork`** — the
  *unconditional local* half: a `ForkWitness` at the bottom `F` (whose live
  set is exactly `{x, x.twin}`) forces `LandingLivePair B c` for any live
  pull card `c`.  This is the third-suit exclusion **at a forked bottom**;
  the pull card `c` is one of the fork's twins, so the fork's pair suits are
  exactly `{c.suit, c.twin.suit}`, and `c.twin` is the other twin.
* **`landingLivePair_of_twinLivePair_F`** — the same at the level of
  `TwinLivePair F c` (no blocked-twin pin needed).
* **`landingAll_iff_splitLivePair`** — **the exact equivalence**: over all
  `SplitHyp`s and their landings, the landing statement is *exactly* the
  campaign's `SplitKit.SplitLivePair`.  Hence the third-suit exclusion is not
  a weaker local residual: it is the same open live-pair obligation.
* **`landingAll_of_valleyElim`** — therefore `ValleyElim.ValleyElimNonfork`
  (the campaign's accepted residual, already feeding `SplitLivePair` via
  `LiveKit.splitLivePair_of_valleyElim`) proves `LandingLivePair` at every
  landing, with no extra input.
* **`landingThirdSuitFree_of_bracket`** — the *exact missing lemma* of the
  strategy, stated as `ThirdSuitBracket`: a third-suit live card at the
  landing yields a same-card `pull z ; raise z` bracket whose raise commutes
  left across the interior; W3 (`LiveKit.pull_raise_pair_shortens`) then
  deletes the bracket and contradicts the split's minimality.

### What is NOT proved (and cannot be, from the current kit)

There is no unconditional proof of `LandingThirdSuitFree`: by
`landingAll_iff_splitLivePair` it is *equivalent* (together with
`LandingTwinLive`) to `SplitLivePair`, which the repository itself carries as
the open residual `ValleyElimNonfork` / `SplitBlock`.  The only remaining
input is therefore `ThirdSuitBracket` (the "violation ⇒ deletable bracket"
step), not a bookkeeping fact.
-/

namespace Landing

/-! ## §1. The third-suit exclusion at a fork -/

/-- At a fork, no third-suit card is S-live: the fork's live set is exactly
the two suits of its twin pair. -/
theorem not_live_third_of_fork {F : State} {x e : Card}
    (hx : ForkWitness F x) (he : CanRaiseS F e)
    (h1 : e.suit ≠ x.suit) (h2 : e.suit ≠ x.twin.suit) : False := by
  rcases (hx.1 e).mpr he with h | h
  · exact h1 (congrArg Card.suit h)
  · exact h2 (congrArg Card.suit h)

/-- At a fork, the twin of a live card is live. -/
theorem fork_pair_live_twin {F : State} {x c : Card}
    (hx : ForkWitness F x) (hc : CanRaiseS F c) : CanRaiseS F c.twin := by
  have hc' := (hx.1 c).mpr hc
  rcases hc' with h | h
  · rw [h]
    exact (hx.1 x.twin).mp (Or.inr rfl)
  · rw [h, card_twin_twin]
    exact (hx.1 x).mp (Or.inl rfl)

/-- At a fork, every live card has one of the two suits of the fork's pair. -/
theorem fork_pair_live_suits {F : State} {x c e : Card}
    (hx : ForkWitness F x) (hc : CanRaiseS F c) (he : CanRaiseS F e) :
    e.suit = c.suit ∨ e.suit = c.twin.suit := by
  have hc' := (hx.1 c).mpr hc
  have he' := (hx.1 e).mpr he
  rcases hc' with h | h
  · subst h
    rcases he' with h' | h'
    · subst h'; exact Or.inl rfl
    · subst h'; exact Or.inr rfl
  · subst h
    rcases he' with h' | h'
    · subst h'
      exact Or.inr (by rw [card_twin_twin])
    · subst h'
      exact Or.inl rfl

/-- A live card at a forked bottom, together with the fork, gives the live
pair at that card (the pivot may be either twin). -/
theorem twinLivePair_of_fork {F : State} {x c : Card}
    (hx : ForkWitness F x) (hc : CanRaiseS F c) : TwinLivePair F c := by
  have hpair : TwinLivePair F x := fun e => (hx.1 e).symm
  rcases (hx.1 c).mpr hc with h | h
  · subst h
    exact hpair
  · subst h
    exact ThirdRigid.twinLivePair_twin hpair

/-! ## §2. The landing live pair from a live pair at the bottom -/

/-- **THE LANDING FORM FROM A LIVE PAIR AT THE BOTTOM.**  If the bottom's
live set is exactly `{c, c.twin}`, the free tail transports it back to the
pull landing `B`: the containment and the liveness of `c.twin` both follow
from `Mech.canRaiseS_landing_iff` (`Orig2/Fork/Local/ForkMechanism.lean:256`). -/
theorem landingLivePair_of_twinLivePair_F
    {B F : State} {post : List Move} {c : Card}
    (hB : B.WF) (hpost : ShufflePlayW B post F)
    (hfree : ∀ m ∈ post, ValleyElim.FreeMove m)
    (h : TwinLivePair F c) : Mech.LandingLivePair B c := by
  refine ⟨?_, ?_⟩
  · exact (Mech.canRaiseS_landing_iff hB hpost hfree c.twin).mpr
      ((h c.twin).mpr (Or.inr rfl))
  · intro e he
    have heF : CanRaiseS F e :=
      (Mech.canRaiseS_landing_iff hB hpost hfree e).mp he
    rcases (h e).mp heF with h' | h'
    · exact Or.inl (congrArg Card.suit h')
    · exact Or.inr (congrArg Card.suit h')

/-- **THE LANDING FORM FROM A FORK AT THE BOTTOM.**  The third-suit exclusion
and the twin liveness at the landing, from a `ForkWitness` at the bottom and
the pull card's S-liveness there. -/
theorem landingLivePair_of_bottomFork
    {B F : State} {post : List Move} {c : Card} {x : Card}
    (hB : B.WF) (hpost : ShufflePlayW B post F)
    (hfree : ∀ m ∈ post, ValleyElim.FreeMove m)
    (hx : ForkWitness F x) (hcF : CanRaiseS F c) :
    Mech.LandingLivePair B c :=
  landingLivePair_of_twinLivePair_F hB hpost hfree
    (twinLivePair_of_fork hx hcF)

/-! ## §3. The SplitHyp-level residuals -/

/-- The pull landing of a split: from `pre` and the pull letter, the split's
`post` is a free witness play from the landing `B` to the bottom `F`. -/
theorem post_play_of_landing
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    {A' B : State} (hpre : ShufflePlayW u pre A')
    (hstep : State.step A' (Move.foundToTab c b) = some B) :
    ShufflePlayW B post F ∧ B.WF := by
  obtain ⟨huwf, -, -, -, -, -, -, hleft, -, hshape, -, -⟩ := h
  obtain ⟨A'', hpre'', hrest⟩ :=
    ValleyElim.ShufflePlayW_split hleft pre (Move.foundToTab c b :: post) hshape
  have hA'eq : A'' = A' := by
    have r1 := Walk_run (fun st m => reversibleAtW st m) hpre''
    have r2 := Walk_run (fun st m => reversibleAtW st m) hpre
    exact Option.some.inj (r1.symm.trans r2)
  subst hA'eq
  cases hrest with
  | @cons _ B' _ _ _ hrev hstep' hpost =>
      have hBeq : B' = B := Option.some.inj (hstep'.symm.trans hstep)
      subst hBeq
      exact ⟨hpost,
        step_wf (SatDifferCensus.ShufflePlayW.wf_end hpre huwf) hstep⟩

/-- **The landing's live-pair clause at every split.** -/
def LandingAll : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    ∀ (A' B : State), ShufflePlayW u pre A' →
      State.step A' (Move.foundToTab c b) = some B →
      Mech.LandingLivePair B c

/-- **The first clause alone**: `c.twin` is S-live at the landing. -/
def LandingTwinLive : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    ∀ (A' B : State), ShufflePlayW u pre A' →
      State.step A' (Move.foundToTab c b) = some B →
      CanRaiseS B c.twin

/-- **The second clause alone (THE THIRD-SUIT EXCLUSION)**: no card of a
third suit is S-live at the landing. -/
def LandingThirdSuitFree : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    ∀ (A' B : State), ShufflePlayW u pre A' →
      State.step A' (Move.foundToTab c b) = some B →
      ∀ e : Card, CanRaiseS B e →
        e.suit ≠ c.suit → e.suit ≠ c.twin.suit → False

/-- `LandingAll` unpacks into its two clauses. -/
theorem landingAll_iff_parts :
    LandingAll ↔ LandingTwinLive ∧ LandingThirdSuitFree := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro u v ρ F left right c d b pre post tail hs A' B hpre hstep
      exact (h u v ρ F left right c d b pre post tail hs A' B hpre hstep).1
    · intro u v ρ F left right c d b pre post tail hs A' B hpre hstep e he h1 h2
      rcases (h u v ρ F left right c d b pre post tail hs A' B hpre hstep).2 e he
        with h' | h'
      · exact h1 h'
      · exact h2 h'
  · rintro ⟨ht, hf⟩
    intro u v ρ F left right c d b pre post tail hs A' B hpre hstep
    refine ⟨ht u v ρ F left right c d b pre post tail hs A' B hpre hstep, ?_⟩
    intro e he
    by_cases h1 : e.suit = c.suit
    · exact Or.inl h1
    · by_cases h2 : e.suit = c.twin.suit
      · exact Or.inr h2
      · exact (hf u v ρ F left right c d b pre post tail hs A' B hpre hstep
          e he h1 h2).elim

/-- **The bottom-fork existence residual**: at every split, the bottom `F` is
a `ForkWitness`.  This is exactly the fork branch of
`ValleyElim.ValleyElimNonfork` after the split's minimality kills the
shortening branch. -/
def BottomForkExists : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    ∀ (A' B : State), ShufflePlayW u pre A' →
      State.step A' (Move.foundToTab c b) = some B →
      ∃ x : Card, ForkWitness F x

/-- The first landing clause from a forked bottom. -/
theorem landingTwinLive_of_bottomFork (hb : BottomForkExists) :
    LandingTwinLive := by
  intro u v ρ F left right c d b pre post tail h A' B hpre hstep
  have hk := h
  obtain ⟨hpost, hB⟩ := post_play_of_landing h hpre hstep
  obtain ⟨huwf, -, -, -, -, -, -, hleft, -, hshape, hfree, -⟩ := h
  obtain ⟨x, hx⟩ :=
    hb u v ρ F left right c d b pre post tail hk A' B hpre hstep
  have hcF : CanRaiseS F c := Bridge.bottom_pull_live huwf hleft hshape hfree
  exact (landingLivePair_of_bottomFork hB hpost hfree hx hcF).1

/-- **THE THIRD-SUIT EXCLUSION AT A FORKED BOTTOM.**  This is the strategy's
step 2 done unconditionally once the bottom carries a fork: the landing live
set is transported to `F`, where the fork's live set is exactly its twin
pair, so the pull card and `e` are both in `{x, x.twin}`. -/
theorem landingThirdSuitFree_of_bottomFork (hb : BottomForkExists) :
    LandingThirdSuitFree := by
  intro u v ρ F left right c d b pre post tail h A' B hpre hstep e he h1 h2
  have hk := h
  obtain ⟨hpost, hB⟩ := post_play_of_landing h hpre hstep
  obtain ⟨huwf, -, -, -, -, -, -, hleft, -, hshape, hfree, -⟩ := h
  obtain ⟨x, hx⟩ :=
    hb u v ρ F left right c d b pre post tail hk A' B hpre hstep
  have hcF : CanRaiseS F c := Bridge.bottom_pull_live huwf hleft hshape hfree
  have hland := landingLivePair_of_bottomFork hB hpost hfree hx hcF
  rcases hland.2 e he with h' | h'
  · exact h1 h'
  · exact h2 h'

/-- The landing live pair from a forked bottom. -/
theorem landingAll_of_bottomFork (hb : BottomForkExists) : LandingAll :=
  landingAll_iff_parts.mpr
    ⟨landingTwinLive_of_bottomFork hb, landingThirdSuitFree_of_bottomFork hb⟩

/-- **`ValleyElimNonfork` supplies the forked bottom** (the shortening branch
is killed by the split's minimality). -/
theorem bottomFork_of_valleyElim (helim : ValleyElim.ValleyElimNonfork) :
    BottomForkExists := by
  intro u v ρ F left right c d b pre post tail h A' B hpre hstep
  have hk := h
  rcases LiveKit.valleyElimForkAtRaise_of_valleyElim helim
      u v ρ F left right c d b pre post tail hk with hx | ⟨ρ', hρ', hlen⟩
  · exact ⟨d, hx⟩
  · exfalso
    obtain ⟨-, -, -, -, -, hmin, -, -, -, -, -, -⟩ := hk
    exact absurd hlen (Nat.not_lt.mpr (hmin ρ' hρ'))

/-! ## §4. The exact equivalence with `SplitKit.SplitLivePair` -/

/-- The live pair at the bottom, with the pull card as pivot, from the
campaign's `SplitLivePair`.  The raise card `d` is live at the bottom, hence
the pull card `c` is one of `{d, d.twin}`; moving the pivot to the twin
preserves the live pair. -/
theorem twinLivePair_at_F_of_splitLivePair
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (hl : SplitKit.SplitLivePair)
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail) :
    TwinLivePair F c := by
  have hk := h
  obtain ⟨huwf, -, -, -, -, -, -, hleft, -, hshape, hfree, -⟩ := h
  have hd : TwinLivePair F d := hl u v ρ F left right c d b pre post tail hk
  have hcF : CanRaiseS F c := Bridge.bottom_pull_live huwf hleft hshape hfree
  rcases (hd c).mp hcF with hcd | hcd
  · subst hcd
    exact hd
  · subst hcd
    exact ThirdRigid.twinLivePair_twin hd

/-- `SplitLivePair` gives both landing clauses. -/
theorem landing_parts_of_splitLivePair (hl : SplitKit.SplitLivePair) :
    LandingTwinLive ∧ LandingThirdSuitFree := by
  refine ⟨?_, ?_⟩
  · intro u v ρ F left right c d b pre post tail h A' B hpre hstep
    obtain ⟨hpost, hB⟩ := post_play_of_landing h hpre hstep
    have hk := h
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hfree, -⟩ := h
    have htwin := twinLivePair_at_F_of_splitLivePair hl hk
    exact (Mech.canRaiseS_landing_iff hB hpost hfree c.twin).mpr
      ((htwin c.twin).mpr (Or.inr rfl))
  · intro u v ρ F left right c d b pre post tail h A' B hpre hstep e he h1 h2
    obtain ⟨hpost, hB⟩ := post_play_of_landing h hpre hstep
    have hk := h
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hfree, -⟩ := h
    have htwin := twinLivePair_at_F_of_splitLivePair hl hk
    have heF : CanRaiseS F e :=
      (Mech.canRaiseS_landing_iff hB hpost hfree e).mp he
    rcases (htwin e).mp heF with h' | h'
    · exact h1 (congrArg Card.suit h')
    · exact h2 (congrArg Card.suit h')

/-- Both landing clauses give `SplitLivePair`: transport the two clauses to
the bottom, use the landing rung pins to upgrade the suit containment to card
equality (`Mech.live_eq_of_suit_left` / `_twin`), and move the pivot to `d`. -/
theorem splitLivePair_of_landing_parts
    (ht : LandingTwinLive) (hf : LandingThirdSuitFree) :
    SplitKit.SplitLivePair := by
  intro u v ρ F left right c d b pre post tail h
  have hk := h
  obtain ⟨huwf, -, -, -, -, -, -, hleft, -, hshape, hfree, -⟩ := h
  obtain ⟨A', hpre, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hleft pre (Move.foundToTab c b :: post) hshape
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  cases hrest with
  | @cons _ B _ _ _ hrev hstep hpost =>
      have hB : B.WF := step_wf hA' hstep
      have hcF : CanRaiseS F c := Bridge.bottom_pull_live huwf hleft hshape hfree
      have hctF : CanRaiseS F c.twin :=
        (Mech.canRaiseS_landing_iff hB hpost hfree c.twin).mp
          (ht u v ρ F left right c d b pre post tail hk A' B hpre hstep)
      have hrungBF : rungAt F c.suit = c.rank.toIdx := by
        rw [ValleyElim.rungAt_eq_of_free_play hpost hfree c.suit]
        exact Mech.rungAt_landing_eq hA' hstep
      have hrungTF : rungAt F c.twin.suit = c.rank.toIdx := by
        have h1 := canRaiseS_rung hctF
        rw [Card.twin_rank] at h1
        exact h1
      have hTwinC : TwinLivePair F c := by
        intro e
        constructor
        · intro he
          have heB : CanRaiseS B e :=
            (Mech.canRaiseS_landing_iff hB hpost hfree e).mpr he
          by_cases hs1 : e.suit = c.suit
          · exact Or.inl (Mech.live_eq_of_suit_left hrungBF he hs1)
          · by_cases hs2 : e.suit = c.twin.suit
            · exact Or.inr (Mech.live_eq_of_suit_twin hrungTF he hs2)
            · exact (hf u v ρ F left right c d b pre post tail hk A' B hpre hstep
                e heB hs1 hs2).elim
        · rintro (rfl | rfl)
          · exact hcF
          · exact hctF
      obtain ⟨-, -, -, hSFd⟩ := SplitKit.splitHyp_green hk
      rcases (hTwinC d).mp hSFd with hdc | hdc
      · subst hdc
        exact hTwinC
      · exact Mech.twinLivePair_of_eq_twin hTwinC hdc

/-- **THE EXACT EQUIVALENCE.**  The landing live pair (over every split) is
exactly the campaign's `SplitKit.SplitLivePair`; there is no weaker local
landing statement. -/
theorem landingAll_iff_splitLivePair :
    LandingAll ↔ SplitKit.SplitLivePair := by
  constructor
  · intro h
    obtain ⟨ht, hf⟩ := landingAll_iff_parts.mp h
    exact splitLivePair_of_landing_parts ht hf
  · intro hl
    exact landingAll_iff_parts.mpr (landing_parts_of_splitLivePair hl)

/-- **THE LANDING LIVE PAIR FROM THE CAMPAIGN'S RESIDUAL.**  `ValleyElimNonfork`
already gives `SplitLivePair` (`LiveKit.splitLivePair_of_valleyElim`), hence
`LandingLivePair` at every pull landing, with no extra input. -/
theorem landingAll_of_valleyElim
    (helim : ValleyElim.ValleyElimNonfork) : LandingAll :=
  landingAll_iff_splitLivePair.mpr (LiveKit.splitLivePair_of_valleyElim helim)

/-- **THE LIVE-PAIR ITSELF AT THE LANDING.**  With the landing rung pin
(`Mech.rungAt_landing_eq`) and the pull card's vanilla raisability
(`ValleyStep.pull_card_canRaise`), `LandingLivePair` upgrades to
`TwinLivePair B c` (`Mech.twinLivePair_of_landing`).  Hence, from
`ValleyElimNonfork`, the landing's S-live set is exactly `{c, c.twin}`. -/
theorem twinLivePair_at_landing_of_valleyElim
    (helim : ValleyElim.ValleyElimNonfork) :
    ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
      ∀ (A' B : State), ShufflePlayW u pre A' →
        State.step A' (Move.foundToTab c b) = some B →
        TwinLivePair B c := by
  intro u v ρ F left right c d b pre post tail h A' B hpre hstep
  have hk := h
  obtain ⟨huwf, -, -, -, -, -, -, -, -, -, -, -⟩ := h
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  exact Mech.twinLivePair_of_landing
    (ValleyStep.pull_card_canRaise hA' hstep)
    (Mech.rungAt_landing_eq hA' hstep)
    (landingAll_of_valleyElim helim u v ρ F left right c d b pre post tail hk
      A' B hpre hstep)

/-- **THE MECHANISM'S LIVE-PAIR CLAUSE, in `SplitMechanism`'s ∃-form**
(`Orig2/Fork/Local/ForkMechanism.lean:376`): every split has a pull landing whose live
set is `LandingLivePair`.  This is the first conjunct of `SplitMechanism`
with the `CoverEvent` conjunct removed. -/
def MechanismLivePair : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    ∃ A' B : State,
      ShufflePlayW u pre A' ∧
      State.step A' (Move.foundToTab c b) = some B ∧
      Mech.LandingLivePair B c

/-- The ∃-form and the ∀-form of the landing residual agree. -/
theorem mechanismLivePair_iff_landingAll :
    MechanismLivePair ↔ LandingAll := by
  constructor
  · intro hm u v ρ F left right c d b pre post tail h A' B hpre hstep
    obtain ⟨A₀, B₀, hpre₀, hstep₀, hland⟩ :=
      hm u v ρ F left right c d b pre post tail h
    have hAeq : A₀ = A' := by
      have r1 := Walk_run (fun st m => reversibleAtW st m) hpre₀
      have r2 := Walk_run (fun st m => reversibleAtW st m) hpre
      exact Option.some.inj (r1.symm.trans r2)
    subst hAeq
    have hBeq : B₀ = B := Option.some.inj (hstep₀.symm.trans hstep)
    subst hBeq
    exact hland
  · intro h u v ρ F left right c d b pre post tail hs
    have hk := hs
    obtain ⟨huwf, -, -, -, -, -, -, hleft, -, hshape, -, -⟩ := hs
    obtain ⟨A', hpre, hrest⟩ :=
      ValleyElim.ShufflePlayW_split hleft pre (Move.foundToTab c b :: post) hshape
    cases hrest with
    | @cons _ B _ _ _ hrev hstep hpost =>
        exact ⟨A', B, hpre, hstep,
          h u v ρ F left right c d b pre post tail hk A' B hpre hstep⟩

/-- **`MechanismLivePair` from the campaign's residual.** -/
theorem mechanismLivePair_of_valleyElim
    (helim : ValleyElim.ValleyElimNonfork) : MechanismLivePair :=
  mechanismLivePair_iff_landingAll.mpr (landingAll_of_valleyElim helim)

/-! ## §5. The exact missing bracket lemma -/

/-- **THE EXACT MISSING LEMMA OF THE THIRD-SUIT EXCLUSION.**  A third-suit
`CanRaiseS` card `e` at the pull landing forces a same-card bracket in the
split's play: an earlier `pull z` and a later `raise z`, whose raise commutes
left across the interior to become adjacent, so W3 deletes the pair and
strictly shortens the play.  This is precisely the strategy's
"violation ⇒ deletable bracket" step, stated as one named hypothesis. -/
def ThirdSuitBracket : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    ∀ (A' B : State), ShufflePlayW u pre A' →
      State.step A' (Move.foundToTab c b) = some B →
      ∀ e : Card, CanRaiseS B e →
        e.suit ≠ c.suit → e.suit ≠ c.twin.suit →
        ∃ (α γ β : List Move) (z : Card) (bz : Base) (P Q : State),
          ρ = α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z :: β ∧
          ShufflePlayW u
            (α ++ Move.foundToTab z bz :: Move.tabToFound z :: (γ ++ β)) v ∧
          ShufflePlayW u α P ∧
          State.step P (Move.foundToTab z bz) = some Q

/-- **THE THIRD-SUIT EXCLUSION FROM THE BRACKET LEMMA.**  The bracket's
commuted form contains the adjacent identity pair `pull z ; raise z`; W3
(`LiveKit.pull_raise_pair_shortens`) deletes it, and the commuted play has
the same length as `ρ`, contradicting the split's minimality. -/
theorem landingThirdSuitFree_of_bracket (hb : ThirdSuitBracket) :
    LandingThirdSuitFree := by
  intro u v ρ F left right c d b pre post tail h A' B hpre hstep e he h1 h2
  obtain ⟨α, γ, β, z, bz, P, Q, hρ, hcomm, hα, hstepP⟩ :=
    hb u v ρ F left right c d b pre post tail h A' B hpre hstep e he h1 h2
  obtain ⟨huwf, -, -, -, -, hmin, -, -, -, -, -, -⟩ := h
  have hPwf : P.WF := SatDifferCensus.ShufflePlayW.wf_end hα huwf
  obtain ⟨ρ', hρ'play, hlen⟩ :=
    LiveKit.pull_raise_pair_shortens
      (u := u) (v := v)
      (ρ := α ++ Move.foundToTab z bz :: Move.tabToFound z :: (γ ++ β))
      (α := α) (β := γ ++ β) (c := z) (b := bz) (A := P) (B := Q)
      hcomm rfl hα hPwf hstepP
  have hlenC : (α ++ Move.foundToTab z bz :: Move.tabToFound z :: (γ ++ β)).length
      = ρ.length := by
    rw [hρ]
    simp only [List.length_append, List.length_cons]
    omega
  rw [hlenC] at hlen
  exact absurd hlen (Nat.not_lt.mpr (hmin ρ' hρ'play))

/-- The bracket premise is not a weaker obligation: its hypothesis set is
contradictory whenever the third-suit exclusion holds, so the exclusion
constructively supplies the (vacuous) bracket witness.  Together with
`landingThirdSuitFree_of_bracket` this pins the residual exactly. -/
theorem bracket_of_landingThirdSuitFree (hf : LandingThirdSuitFree) :
    ThirdSuitBracket := by
  intro u v ρ F left right c d b pre post tail h A' B hpre hstep e he h1 h2
  exact (hf u v ρ F left right c d b pre post tail h A' B hpre hstep
    e he h1 h2).elim

/-- **`ThirdSuitBracket` is exactly the third-suit exclusion.** -/
theorem thirdSuitBracket_iff_landingThirdSuitFree :
    ThirdSuitBracket ↔ LandingThirdSuitFree :=
  ⟨landingThirdSuitFree_of_bracket, bracket_of_landingThirdSuitFree⟩

/-- **`LandingLivePair` FROM THE TWO NAMED PIECES**: the first clause
(`c.twin` live at the landing) and the exact bracket lemma for the
third-suit exclusion. -/
theorem landingAll_of_twinLive_and_bracket
    (ht : LandingTwinLive) (hb : ThirdSuitBracket) : LandingAll :=
  landingAll_iff_parts.mpr ⟨ht, landingThirdSuitFree_of_bracket hb⟩

/-! ## §6. Axiom battery -/

#print axioms not_live_third_of_fork
#print axioms fork_pair_live_twin
#print axioms fork_pair_live_suits
#print axioms twinLivePair_of_fork
#print axioms landingLivePair_of_twinLivePair_F
#print axioms landingLivePair_of_bottomFork
#print axioms post_play_of_landing
#print axioms landingAll_iff_parts
#print axioms twinLivePair_at_F_of_splitLivePair
#print axioms landing_parts_of_splitLivePair
#print axioms splitLivePair_of_landing_parts
#print axioms landingAll_iff_splitLivePair
#print axioms landingAll_of_valleyElim
#print axioms twinLivePair_at_landing_of_valleyElim
#print axioms landingTwinLive_of_bottomFork
#print axioms landingThirdSuitFree_of_bottomFork
#print axioms landingAll_of_bottomFork
#print axioms bottomFork_of_valleyElim
#print axioms mechanismLivePair_iff_landingAll
#print axioms mechanismLivePair_of_valleyElim
#print axioms landingThirdSuitFree_of_bracket
#print axioms bracket_of_landingThirdSuitFree
#print axioms thirdSuitBracket_iff_landingThirdSuitFree
#print axioms landingAll_of_twinLive_and_bracket

end Landing
