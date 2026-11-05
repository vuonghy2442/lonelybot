import Orig2.Substrate.Vocab
import Orig2.Substrate.Integrity
import Orig2.Substrate.Position
import Orig2.Substrate.Classification
import Orig2.Substrate.PairClassSeed
import Orig2.Substrate.Kit
import Orig2.Substrate.StepWF
import Orig2.Fork.Local.ForkCriticalPair
import Orig2.Fork.Class.ForkTwinLive
import Orig2.Fork.Split.ForkDrainInduction
import Orig2.Fork.Split.ForkDrainClose
import Orig2.Fork.Class.ForkOneColourClosure

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkPrefixClimb - the cap-directed raise climb

THE OBJECT.  A cap `cap : Suit -> Nat`; the surplus set
`S(st,cap) = { (k,s) : rungAt st s <= k < cap s }` is exactly the set of cards
that must still be founded to bring the four rungs to `cap`.  A raise
(`tabToFound`) removes a pile top and advances one rung, so the climb is a
removal schedule on the piles.

THE INVARIANT.  `PrefixOK` says the surplus is face-up and sits at the top of
every pile (a prefix read top-down).  It is preserved by every capped raise
(`step_preserves`), and a PREFIX state below the cap always has a capped raise
(`stepExists_of_minCard`, from the min-rank card plus the measured
`MinCardLicence`).

THE THEOREM.  `prefixClimb`: from a PREFIX state under the cap, the raise
closure reaches the cap.  Induction on `capSum cap - rungSum`, choice-free.

THE NAMED INPUT.  `MinCardLicence` - the min-rank surplus card is not a lone
face-up card over a nonempty hidden stack (the third `CanRaise` clause).
Measured 251,729 / 0 across random8, high59h and draw59b.  The `PrefixOK` start
itself comes from the campaign's fibre-prefix residual (0 / 33.1M), which is
not stated here.

House compliance: root-imported card, zero sorry, zero `Classical.choice`.
-/

namespace PrefixClimb

inductive RaiseReach (u : State) : State -> Prop
  | refl : RaiseReach u u
  | step {v w : State} {c : Card} :
      RaiseReach u v -> CanRaise v c ->
      State.step v (Move.tabToFound c) = some w -> RaiseReach u w

def InS (st : State) (cap : Suit -> Nat) (card : Card) : Prop :=
  rungAt st card.suit <= card.rank.toIdx /\ card.rank.toIdx < cap card.suit

def Above (x y : Card) (l : List Card) : Prop :=
  exists P Q : List Card, l = P ++ y :: Q /\ x ∈ Q

def PrefixOK (st : State) (cap : Suit -> Nat) : Prop :=
  (forall card, InS st cap card -> exists a : Anchor, card ∈ (st.piles a).faceUp) /\
  (forall (a : Anchor) card, card ∈ (st.piles a).faceUp -> InS st cap card ->
     forall x, Above x card (st.piles a).faceUp -> InS st cap x)

def Under (st : State) (cap : Suit -> Nat) : Prop :=
  forall σ : Suit, rungAt st σ <= cap σ

def capSum (cap : Suit -> Nat) : Nat := (Suit.all.map cap).sum

/-! ## Geometric kit -/

theorem above_rank_lt {l : List Card} (hok : runOK l = true)
    {y x : Card} (h : Above x y l) : x.rank.toIdx < y.rank.toIdx := by
  obtain ⟨P, Q, rfl, hx⟩ := h
  have hok' : runOK ((P ++ [y]) ++ Q) = true := by
    simpa [List.append_assoc] using hok
  exact runOK_desc hok' (by simp) hx

theorem not_above_of_min {st : State} (hwf : st.WF) {cap : Suit -> Nat}
    (hpre : PrefixOK st cap) {z : Card} (hz : InS st cap z)
    (hmin : forall y, InS st cap y -> z.rank.toIdx <= y.rank.toIdx)
    {a : Anchor} (ha : z ∈ (st.piles a).faceUp) :
    forall x, ¬ Above x z (st.piles a).faceUp := by
  intro x hx
  have hS : InS st cap x := hpre.2 a z ha hz x hx
  have hlt := above_rank_lt (hwf.runOK_of a) hx
  have hge := hmin x hS
  omega

theorem lastOf_append_singleton (P : List Card) (z : Card) :
    lastOf (P ++ [z]) = some z := by
  rw [tfc_lastOf_append_ne P (by simp)]
  rfl

theorem lastOf_eq_some_of_mem_of_no_above {l : List Card} {z : Card}
    (hz : z ∈ l) (h : forall x, ¬ Above x z l) : lastOf l = some z := by
  obtain ⟨P, Q, rfl⟩ := List.mem_iff_append.mp hz
  have hQ : Q = [] := by
    rcases Q with _ | ⟨x, xs⟩
    · rfl
    · exact absurd ⟨P, x :: xs, rfl, by simp⟩ (h x)
  subst hQ
  exact lastOf_append_singleton P z

theorem minCard_top {st : State} (hwf : st.WF) {cap : Suit -> Nat}
    (hpre : PrefixOK st cap) {z : Card} (hz : InS st cap z)
    (hmin : forall y, InS st cap y -> z.rank.toIdx <= y.rank.toIdx)
    {a : Anchor} (ha : z ∈ (st.piles a).faceUp) :
    st.pileOfTop z = some a := by
  have hno := not_above_of_min hwf hpre hz hmin ha
  exact (pileOfTop_eq_some_iff hwf).mpr
    (lastOf_eq_some_of_mem_of_no_above ha hno)

theorem minCard_rank_eq_rung {st : State} {cap : Suit -> Nat}
    (hunder : Under st cap) {z : Card} (hz : InS st cap z)
    (hmin : forall y, InS st cap y -> z.rank.toIdx <= y.rank.toIdx) :
    rungAt st z.suit = z.rank.toIdx := by
  refine Nat.le_antisymm hz.1 (Nat.le_of_not_lt ?_)
  intro hlt
  have hr13 : rungAt st z.suit < 13 := by
    have := Rank.toIdx_lt z.rank
    omega
  have hltcap : rungAt st z.suit < cap z.suit := by
    have h1 : z.rank.toIdx < cap z.suit := hz.2
    have h2 : rungAt st z.suit <= cap z.suit := hunder z.suit
    omega
  let w : Card := Card.mk z.suit (FoundKit.Rk (rungAt st z.suit))
  have hw_rank : w.rank.toIdx = rungAt st z.suit := by
    show (FoundKit.Rk (rungAt st z.suit)).toIdx = rungAt st z.suit
    exact FoundKit.Rk_toIdx _ hr13
  have hw_suit : w.suit = z.suit := rfl
  have hwS : InS st cap w := by
    refine ⟨?_, ?_⟩
    · rw [hw_suit, hw_rank]; exact Nat.le_refl _
    · rw [hw_suit, hw_rank]; exact hltcap
  have := hmin w hwS
  rw [hw_rank] at this
  omega

theorem minCard_nextUp {st : State} {cap : Suit -> Nat}
    (hunder : Under st cap) {z : Card} (hz : InS st cap z)
    (hmin : forall y, InS st cap y -> z.rank.toIdx <= y.rank.toIdx) :
    st.nextUp z = true :=
  TwinKit.nextUp_true_iff.mpr (minCard_rank_eq_rung hunder hz hmin)

/-! ## The measure -/

theorem sum_le_sum_map {l : List Suit} {f g : Suit -> Nat}
    (h : forall s, s ∈ l -> f s <= g s) : (l.map f).sum <= (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (h a (by simp)) (ih (fun s hs => h s (by simp [hs])))

theorem sum_lt_of_map_le_of_lt {l : List Suit} {f g : Suit -> Nat}
    (h : forall s, s ∈ l -> f s <= g s) {a : Suit} (ha : a ∈ l) (hlt : f a < g a) :
    (l.map f).sum < (l.map g).sum := by
  induction l with
  | nil => cases ha
  | cons x t ih =>
      simp only [List.map_cons, List.sum_cons]
      rcases List.mem_cons.1 ha with rfl | hat
      · have ht : (t.map f).sum <= (t.map g).sum :=
          sum_le_sum_map (fun s hs => h s (by simp [hs]))
        omega
      · have hx : f x <= g x := h x (by simp)
        have := ih (fun s hs => h s (by simp [hs])) hat
        omega

theorem rungSum_le_capSum {st : State} {cap : Suit -> Nat} (h : Under st cap) :
    Drain.rungSum st <= capSum cap :=
  sum_le_sum_map (l := Suit.all) (f := fun s => rungAt st s) (g := cap)
    (fun s _ => h s)

theorem Under.step {st v : State} {cap : Suit -> Nat} {c : Card}
    (h : Under st cap) (hstep : State.step st (Move.tabToFound c) = some v)
    (hlt : rungAt st c.suit < cap c.suit) : Under v cap := by
  intro σ
  rw [rungAt_tabToFound hstep σ]
  by_cases hσ : σ = c.suit
  · rw [if_pos hσ, hσ]; omega
  · rw [if_neg hσ]; exact h σ

theorem rungs_eq_of_sum_eq {st : State} {cap : Suit -> Nat} (h : Under st cap)
    (hsum : Drain.rungSum st = capSum cap) : forall σ : Suit, rungAt st σ = cap σ := by
  intro σ
  have hσ := h σ
  rcases Nat.lt_or_eq_of_le hσ with hlt | heq
  · exfalso
    have hmem : σ ∈ Suit.all := by cases σ <;> simp [Suit.all]
    have hstrict := sum_lt_of_map_le_of_lt (l := Suit.all)
      (f := fun s => rungAt st s) (g := cap) (fun s _ => h s) hmem hlt
    exact absurd hsum (Nat.ne_of_lt hstrict)
  · exact heq

/-- Some suit is below the cap (constructive: four `Nat` comparisons). -/
theorem exists_lt_of_sum_lt {st : State} {cap : Suit -> Nat} (h : Under st cap)
    (hlt : Drain.rungSum st < capSum cap) : exists σ, rungAt st σ < cap σ := by
  rcases Nat.lt_or_ge (rungAt st .spade) (cap .spade) with h0 | h0
  · exact ⟨.spade, h0⟩
  · rcases Nat.lt_or_ge (rungAt st .heart) (cap .heart) with h1 | h1
    · exact ⟨.heart, h1⟩
    · rcases Nat.lt_or_ge (rungAt st .diamond) (cap .diamond) with h2 | h2
      · exact ⟨.diamond, h2⟩
      · rcases Nat.lt_or_ge (rungAt st .club) (cap .club) with h3 | h3
        · exact ⟨.club, h3⟩
        · exfalso
          have e0 : rungAt st .spade = cap .spade := by have := h .spade; omega
          have e1 : rungAt st .heart = cap .heart := by have := h .heart; omega
          have e2 : rungAt st .diamond = cap .diamond := by have := h .diamond; omega
          have e3 : rungAt st .club = cap .club := by have := h .club; omega
          have hmap : Suit.all.map (fun s => rungAt st s) = Suit.all.map cap :=
            List.map_congr_left (fun s _ => by cases s <;> assumption)
          have hsum : Drain.rungSum st = capSum cap := by
            show (Suit.all.map (fun s => rungAt st s)).sum = (Suit.all.map cap).sum
            rw [hmap]
          omega

/-! ## The two measured inputs -/

/-- MEASURED (H `G-A1`: 0/255k failures): a PREFIX state below the cap has a
capped raise. -/
def StepExists (cap : Suit -> Nat) : Prop :=
  forall st, st.WF -> Under st cap -> PrefixOK st cap ->
    (exists σ, rungAt st σ < cap σ) ->
    exists c, CanRaise st c /\ rungAt st c.suit < cap c.suit

/-- MEASURED (H `G-A1`, preservation column: 0/255k failures): every capped
raise preserves `PREFIX`. -/
def StepPreserves (cap : Suit -> Nat) : Prop :=
  forall st w c, st.WF -> Under st cap -> PrefixOK st cap -> CanRaise st c ->
    State.step st (Move.tabToFound c) = some w -> PrefixOK w cap

/-! ## The climb -/

theorem prefixClimb {u : State} {cap : Suit -> Nat}
    (hE : StepExists cap) (hP : StepPreserves cap)
    (hwf : u.WF) (hunder : Under u cap) (hpre : PrefixOK u cap) :
    exists w, RaiseReach u w /\ forall σ, rungAt w σ = cap σ := by
  have main : forall n, forall v, RaiseReach u v -> v.WF -> Under v cap -> PrefixOK v cap ->
      capSum cap - Drain.rungSum v <= n ->
      exists w, RaiseReach u w /\ forall σ, rungAt w σ = cap σ := by
    intro n
    induction n with
    | zero =>
        intro v hrv hwf hunder hpre hle
        have hge : capSum cap <= Drain.rungSum v := by omega
        have hsum : Drain.rungSum v = capSum cap :=
          Nat.le_antisymm (rungSum_le_capSum hunder) hge
        exact ⟨v, hrv, rungs_eq_of_sum_eq hunder hsum⟩
    | succ n ih =>
        intro v hrv hwf hunder hpre hle
        by_cases hfin : Drain.rungSum v = capSum cap
        · exact ⟨v, hrv, rungs_eq_of_sum_eq hunder hfin⟩
        · have hlt : Drain.rungSum v < capSum cap := by
            have := rungSum_le_capSum hunder
            omega
          obtain ⟨σ, hσ⟩ := exists_lt_of_sum_lt hunder hlt
          obtain ⟨c, hcan, hcap⟩ := hE v hwf hunder hpre ⟨σ, hσ⟩
          obtain ⟨w, hsw⟩ := step_tabToFound_of_canRaise hcan
          have hrv' : RaiseReach u w := RaiseReach.step hrv hcan hsw
          have hwf' : w.WF := step_wf hwf hsw
          have hun' : Under w cap := Under.step hunder hsw hcap
          have hpr' : PrefixOK w cap := hP v w c hwf hunder hpre hcan hsw
          have hs : Drain.rungSum w = Drain.rungSum v + 1 := DrainClose.rungSum_raise hsw
          exact ih w hrv' hwf' hun' hpr' (by omega)
  exact main (capSum cap - Drain.rungSum u) u RaiseReach.refl hwf hunder hpre (by omega)

#print axioms above_rank_lt
#print axioms minCard_top
#print axioms minCard_rank_eq_rung
#print axioms rungSum_le_capSum
#print axioms rungs_eq_of_sum_eq
#print axioms exists_lt_of_sum_lt
/-! ## The step interface: which surplus cards survive a raise -/

theorem InS_step {st w : State} {cap : Suit -> Nat} {c : Card}
    (hstep : State.step st (Move.tabToFound c) = some w)
    (hnext : rungAt st c.suit = c.rank.toIdx) :
    forall card, InS w cap card ↔ InS st cap card ∧ card ≠ c := by
  intro card
  obtain ⟨s, r⟩ := card
  by_cases hs : s = c.suit
  · subst hs
    have hnext' : c.rank.toIdx = rungAt st c.suit := hnext.symm
    have hrw : rungAt w c.suit = rungAt st c.suit + 1 := by
      rw [rungAt_tabToFound hstep c.suit, if_pos rfl]
    have hne : (Card.mk c.suit r ≠ c) ↔ r.toIdx ≠ rungAt st c.suit := by
      constructor
      · intro hne hk
        have hrank : r = c.rank := Rank.toIdx_inj (by rw [hk, hnext'])
        exact hne (by
          rw [show c = Card.mk c.suit c.rank from rfl, Card.mk.injEq]
          exact ⟨rfl, hrank⟩)
      · intro hne hc
        have hrank : r = c.rank := congrArg Card.rank hc
        exact hne (by rw [hrank, hnext'])
    simp only [InS]
    rw [hrw, hne]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨by omega, h2⟩, by omega⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨by omega, h2⟩
  · have hrw : rungAt w s = rungAt st s := by
      rw [rungAt_tabToFound hstep s, if_neg hs]
    have hne : Card.mk s r ≠ c := by
      intro h
      exact hs (congrArg Card.suit h)
    simp only [InS]
    rw [hrw]
    simp [hne]

/-! ## The footprint of a raise -/

theorem Above.append_right {x y : Card} {P rest : List Card}
    (h : Above x y P) : Above x y (P ++ rest) := by
  obtain ⟨P0, Q, hP, hx⟩ := h
  refine ⟨P0, Q ++ rest, ?_, List.mem_append.mpr (Or.inl hx)⟩
  rw [hP]
  simp [List.append_assoc]

theorem mem_of_mem_snoc_ne {x c : Card} {P : List Card}
    (h : x ∈ P ++ [c]) (hne : x ≠ c) : x ∈ P := by
  rcases List.mem_append.1 h with h | h
  · exact h
  · simp at h
    exact absurd h hne

/-- With the `CanRaise` side condition, removing the run leaves `faceUp` and
`hidden` alone (the reveal branch is excluded). -/
theorem afterRunRemoved_chop {p : Pile} {c : Card}
    (hside : chop p.faceUp ≠ [] ∨ (p.hidden = [] ∧ c.rank = Rank.king)) :
    p.afterRunRemoved (chop p.faceUp) =
      { hidden := p.hidden, faceUp := chop p.faceUp } := by
  by_cases hchop : chop p.faceUp = []
  · rcases hside with h | ⟨hh, -⟩
    · exact absurd hchop h
    · simp [Pile.afterRunRemoved, hchop, hh, Pile.revealTop]
  · cases h : chop p.faceUp with
    | nil => exact absurd h hchop
    | cons x xs => simp [Pile.afterRunRemoved, h]

theorem step_preserves {st w : State} {cap : Suit -> Nat} {c : Card}
    (hwf : st.WF) (hpre : PrefixOK st cap)
    (hcan : CanRaise st c)
    (hstep : State.step st (Move.tabToFound c) = some w) : PrefixOK w cap := by
  obtain ⟨hnext, a, hpod, hside⟩ := hcan
  have hnextR : rungAt st c.suit = c.rank.toIdx := TwinKit.nextUp_true_iff.mp hnext
  obtain ⟨-, a', hpod', hw⟩ := step_tabToFound_inv hstep
  have haa : a' = a := pileOfTop_inj hpod' hpod
  rw [haa] at hw
  have htop : (st.piles a).top = some c := (pileOfTop_eq_some_iff hwf).mp hpod
  have hlast : lastOf (st.piles a).faceUp = some c := htop
  obtain ⟨P, hP⟩ := lastOf_eq_snoc hlast
  have hchop : chop (st.piles a).faceUp = P := by rw [hP, chop_snoc]
  have harm := afterRunRemoved_chop (p := st.piles a) (c := c) hside
  have hcmem : c ∈ (st.piles a).faceUp := by rw [hP]; simp
  have hpile_a : (w.piles a).faceUp = P := by
    rw [hw]
    simp only [if_pos rfl]
    rw [harm]
    simp [hchop]
  have hpile_ne : ∀ b, b ≠ a → (w.piles b).faceUp = (st.piles b).faceUp := by
    intro b hb
    rw [hw]
    simp [hb]
  have hpile : ∀ b, (w.piles b).faceUp =
      (if b = a then P else (st.piles b).faceUp) := by
    intro b
    by_cases hb : b = a
    · subst b
      rw [if_pos rfl]
      exact hpile_a
    · rw [if_neg hb]
      exact hpile_ne b hb
  constructor
  · -- (i) every surplus card of w is face-up
    intro card hcard
    obtain ⟨hcard_st, hne⟩ := (InS_step hstep hnextR card).mp hcard
    obtain ⟨b, hb⟩ := hpre.1 card hcard_st
    refine ⟨b, ?_⟩
    rw [hpile b]
    by_cases hba : b = a
    · subst b
      rw [if_pos rfl]
      exact mem_of_mem_snoc_ne (by rw [← hP]; exact hb) hne
    · rw [if_neg hba]
      exact hb
  · -- (ii) the prefix property transfers
    intro b card hcard_w hcard_S x habove
    obtain ⟨hcard_st, hne_card⟩ := (InS_step hstep hnextR card).mp hcard_S
    have hmem_st : card ∈ (st.piles b).faceUp := by
      rw [hpile b] at hcard_w
      by_cases hba : b = a
      · subst b
        rw [if_pos rfl] at hcard_w
        rw [hP]
        exact List.mem_append.mpr (Or.inl hcard_w)
      · rw [if_neg hba] at hcard_w
        exact hcard_w
    have habove_st : Above x card (st.piles b).faceUp := by
      have h := habove
      rw [hpile b] at h
      by_cases hba : b = a
      · subst b
        rw [if_pos rfl] at h
        rw [hP]
        exact Above.append_right (rest := [c]) h
      · rw [if_neg hba] at h
        exact h
    have hx_st : InS st cap x := hpre.2 b card hmem_st hcard_st x habove_st
    refine (InS_step hstep hnextR x).mpr ⟨hx_st, ?_⟩
    by_cases hba : b = a
    · subst b
      intro hxc
      have hxA : Above x card P := by
        rw [hpile a, if_pos rfl] at habove
        exact habove
      have hxP : x ∈ P := by
        obtain ⟨P0, Q, hPQ, hxQ⟩ := hxA
        rw [hPQ]
        simp [hxQ]
      have hnd : (P ++ [c]).Nodup := by
        rw [← hP]
        exact runOK_nodup (hwf.runOK_of a)
      have hxcne : x ≠ c := by
        intro h
        have := (List.nodup_append.1 hnd).2.2 x hxP c (by simp)
        exact this h
      exact hxcne hxc
    · intro hxc
      have hxmem : x ∈ (st.piles b).faceUp := by
        rw [hpile b, if_neg hba] at habove
        obtain ⟨P0, Q, hPQ, hxQ⟩ := habove
        rw [hPQ]
        simp [hxQ]
      exact (mem_faceUp_unique hwf hcmem b hba).1 (hxc ▸ hxmem)

/-- The min-rank surplus card is raisable once its licence clause is supplied. -/
theorem canRaise_of_min {st : State} {cap : Suit -> Nat} {z : Card}
    (hwf : st.WF) (hunder : Under st cap) (hpre : PrefixOK st cap)
    (hz : InS st cap z)
    (hmin : forall y, InS st cap y -> z.rank.toIdx <= y.rank.toIdx)
    {a : Anchor} (ha : z ∈ (st.piles a).faceUp)
    (hlic : chop (st.piles a).faceUp ≠ [] ∨
      ((st.piles a).hidden = [] ∧ z.rank = Rank.king)) :
    CanRaise st z :=
  ⟨minCard_nextUp hunder hz hmin, a, minCard_top hwf hpre hz hmin ha, hlic⟩

/-- THE RESIDUAL, exactly: the min-rank surplus card is not a lone face-up card
sitting on a nonempty hidden stack.  (`CanRaise`'s third clause.) -/
def MinCardLicence (cap : Suit -> Nat) : Prop :=
  forall st, st.WF -> Under st cap -> PrefixOK st cap ->
    forall z, InS st cap z ->
      (forall y, InS st cap y -> z.rank.toIdx <= y.rank.toIdx) ->
      exists a, st.pileOfTop z = some a /\
        (chop (st.piles a).faceUp ≠ [] ∨
          ((st.piles a).hidden = [] ∧ z.rank = Rank.king))

/-- The Bool view of the surplus set. -/
def inSB (st : State) (cap : Suit -> Nat) (card : Card) : Bool :=
  decide (rungAt st card.suit <= card.rank.toIdx) &&
    decide (card.rank.toIdx < cap card.suit)

theorem inSB_true_iff {st : State} {cap : Suit -> Nat} {card : Card} :
    inSB st cap card = true ↔ InS st cap card := by
  unfold inSB InS
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨of_decide_eq_true h1, of_decide_eq_true h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨decide_eq_true h1, decide_eq_true h2⟩

/-- A list has a min-rank `p`-true element (structural, choice-free). -/
theorem exists_min_bool {p : Card -> Bool} (l : List Card)
    (hne : exists c, c ∈ l ∧ p c = true) :
    exists z, z ∈ l ∧ p z = true ∧
      forall y, y ∈ l -> p y = true -> z.rank.toIdx <= y.rank.toIdx := by
  induction l with
  | nil => rcases hne with ⟨c, hc, -⟩; cases hc
  | cons a t ih =>
      by_cases ha : p a = true
      · by_cases ht : exists c, c ∈ t ∧ p c = true
        · obtain ⟨z, hz, hpz, hmin⟩ := ih ht
          by_cases hle : a.rank.toIdx <= z.rank.toIdx
          · refine ⟨a, List.mem_cons_self, ha, ?_⟩
            intro y hy hpy
            rcases List.mem_cons.1 hy with rfl | hyt
            · exact Nat.le_refl _
            · exact Nat.le_trans hle (hmin y hyt hpy)
          · refine ⟨z, List.mem_cons_of_mem a hz, hpz, ?_⟩
            intro y hy hpy
            rcases List.mem_cons.1 hy with rfl | hyt
            · exact Nat.le_of_lt (Nat.lt_of_not_le hle)
            · exact hmin y hyt hpy
        · refine ⟨a, List.mem_cons_self, ha, ?_⟩
          intro y hy hpy
          rcases List.mem_cons.1 hy with rfl | hyt
          · exact Nat.le_refl _
          · exact absurd ⟨y, hyt, hpy⟩ ht
      · obtain ⟨c, hc, hpc⟩ := hne
        rcases List.mem_cons.1 hc with rfl | hct
        · exact absurd hpc ha
        · obtain ⟨z, hz, hpz, hmin⟩ := ih ⟨c, hct, hpc⟩
          refine ⟨z, List.mem_cons_of_mem a hz, hpz, ?_⟩
          intro y hy hpy
          rcases List.mem_cons.1 hy with rfl | hyt
          · exact absurd hpy ha
          · exact hmin y hyt hpy

/-- The combinatorial statement: a min-rank surplus card exists, given the
rung bound on the cap (caps come from rung vectors, so `cap σ ≤ 13`). -/
def MinCardExists (cap : Suit -> Nat) : Prop :=
  forall st, st.WF -> Under st cap -> PrefixOK st cap ->
    (forall σ, cap σ <= 13) ->
    (exists σ, rungAt st σ < cap σ) ->
    exists z, InS st cap z /\
      (forall y, InS st cap y -> z.rank.toIdx <= y.rank.toIdx)

/-- THE COMBINATORIAL RESIDUAL, PROVED: the min-rank surplus card exists. -/
theorem minCardExists (cap : Suit -> Nat) (hcap13 : forall σ, cap σ <= 13) :
    MinCardExists cap := by
  intro st hwf hunder hpre _hc13 hne
  obtain ⟨σ, hσ⟩ := hne
  have hr13 : rungAt st σ < 13 := Nat.lt_of_lt_of_le hσ (hcap13 σ)
  let z0 : Card := Card.mk σ (FoundKit.Rk (rungAt st σ))
  have hz0rank : z0.rank.toIdx = rungAt st σ := by
    show (FoundKit.Rk (rungAt st σ)).toIdx = rungAt st σ
    exact FoundKit.Rk_toIdx _ hr13
  have hz0S : InS st cap z0 := by
    refine ⟨?_, ?_⟩
    · show rungAt st z0.suit <= z0.rank.toIdx
      rw [hz0rank]
      exact Nat.le_refl _
    · show z0.rank.toIdx < cap z0.suit
      rw [hz0rank]
      exact hσ
  obtain ⟨z, _hzmem, hzS, hzmin⟩ :=
    exists_min_bool (p := inSB st cap) Card.universe
      ⟨z0, Card.mem_universe z0, inSB_true_iff.mpr hz0S⟩
  refine ⟨z, ?_, ?_⟩
  · exact inSB_true_iff.mp hzS
  · intro y hyS
    exact hzmin y (Card.mem_universe y) (inSB_true_iff.mpr hyS)

/-- `StepExists` reduces to the min-card selection plus the licence clause. -/
theorem stepExists_of_minCard {cap : Suit -> Nat} (hcap13 : forall σ, cap σ <= 13)
    (hsel : MinCardExists cap) (hlic : MinCardLicence cap) :
    StepExists cap := by
  intro st hwf hunder hpre hne
  obtain ⟨z, hz, hmin⟩ := hsel st hwf hunder hpre hcap13 hne
  obtain ⟨a, hpod, hside⟩ := hlic st hwf hunder hpre z hz hmin
  have htop : (st.piles a).top = some z := (pileOfTop_eq_some_iff hwf).mp hpod
  have ha : z ∈ (st.piles a).faceUp := Pile.mem_of_top htop
  refine ⟨z, canRaise_of_min hwf hunder hpre hz hmin ha hside, ?_⟩
  have h1 : z.rank.toIdx < cap z.suit := hz.2
  have hr := minCard_rank_eq_rung hunder hz hmin
  rw [hr]
  exact h1

/-- `StepPreserves` is DISCHARGED: the proved `step_preserves` does not even
need the `Under` hypothesis. -/
theorem stepPreserves_proved (cap : Suit -> Nat) : StepPreserves cap :=
  fun st w c hwf _hunder hpre hcan hstep => step_preserves hwf hpre hcan hstep

#print axioms inSB_true_iff
#print axioms exists_min_bool
#print axioms minCardExists
#print axioms stepPreserves_proved
#print axioms stepExists_of_minCard
#print axioms afterRunRemoved_chop
#print axioms step_preserves

/-! ## Orbit preservation and the campaign corollary -/

theorem RaiseReach.wf_and_orbit {u v : State} (h : RaiseReach u v) (hu : u.WF) :
    v.WF /\ sameOrbitSetoid.r u v := by
  induction h with
  | refl => exact ⟨hu, sameOrbitSetoid.iseqv.refl u⟩
  | step _ hcan hstep ih =>
      obtain ⟨hwf, horb⟩ := ih
      have hrev := DrainClose.reversibleAtW_tabToFound_of_canRaise hwf hcan
      have hso := Drain.sameOrbit_of_step hrev hstep
      exact ⟨step_wf hwf hstep, sameOrbitSetoid.iseqv.trans horb hso⟩

#print axioms RaiseReach.wf_and_orbit










/-! ## The lone-over-hidden blocker -/

/-- A card that is the only face-up card of its pile, over nonempty hidden
cards, is NOT raisable (the reveal ban, at the licence level). -/
theorem canRaise_false_of_lone {st : State} {a : Anchor} {z : Card}
    (hpod : st.pileOfTop z = some a)
    (hface : (st.piles a).faceUp = [z])
    (hhid : (st.piles a).hidden ≠ []) :
    ¬ CanRaise st z := by
  intro hcan
  obtain ⟨-, a', hpod', hside⟩ := hcan
  have haa : a' = a := pileOfTop_inj hpod' hpod
  subst haa
  rcases hside with h | ⟨hh, -⟩
  · rw [hface] at h
    exact h rfl
  · exact hhid hh

#print axioms canRaise_false_of_lone

/-- A lone-over-hidden next-up card blocks all raise-only progress in its suit. -/
theorem lone_hidden_blocks {st w0 : State} {a : Anchor} {z : Card} {s : Suit}
    (hwf : st.WF)
    (hpod : st.pileOfTop z = some a)
    (hface : (st.piles a).faceUp = [z])
    (hhid : (st.piles a).hidden ≠ [])
    (hzs : z.suit = s)
    (hzr : z.rank.toIdx = rungAt st s)
    (hreach : RaiseReach st w0) :
    rungAt w0 s = rungAt st s := by
  have H : forall u, RaiseReach st u ->
      u.WF /\ u.pileOfTop z = some a /\ (u.piles a).faceUp = [z] /\
      (u.piles a).hidden = (st.piles a).hidden /\ rungAt u s = rungAt st s := by
    intro u hru
    induction hru with
    | refl => exact ⟨hwf, hpod, hface, rfl, rfl⟩
    | step hrv hcan hstep ih =>
        rename_i v w c
        obtain ⟨hwu, hpodu, hfaceu, hhidu, hrungu⟩ := ih
        obtain ⟨-, a', hpodc, hw⟩ := step_tabToFound_inv hstep
        by_cases hane : a' = a
        · exfalso
          have hpodc' : v.pileOfTop c = some a := by rw [hane] at hpodc; exact hpodc
          have htopc : (v.piles a).top = some c := (pileOfTop_eq_some_iff hwu).mp hpodc'
          have htopz : (v.piles a).top = some z := (pileOfTop_eq_some_iff hwu).mp hpodu
          have hcz : c = z := Option.some.inj (htopc.symm.trans htopz)
          have hhidv : (v.piles a).hidden ≠ [] := by rw [hhidu]; exact hhid
          exact canRaise_false_of_lone hpodu hfaceu hhidv (hcz ▸ hcan)
        · have hpile : w.piles a = v.piles a := by
            rw [hw]
            simp [Ne.symm hane]
          have hfacew : (w.piles a).faceUp = [z] := by rw [hpile]; exact hfaceu
          have hhidw : (w.piles a).hidden = (st.piles a).hidden := by
            rw [hpile]; exact hhidu
          have hpodu' : w.pileOfTop z = some a :=
            (pileOfTop_eq_some_iff (step_wf hwu hstep)).mpr (by
              rw [hpile]
              exact (pileOfTop_eq_some_iff hwu).mp hpodu)
          have hrungw : rungAt w s = rungAt st s := by
            rw [rungAt_tabToFound hstep s]
            by_cases hcs : s = c.suit
            · exfalso
              have hnext : rungAt v c.suit = c.rank.toIdx :=
                TwinKit.nextUp_true_iff.mp hcan.1
              have hcsz : c.suit = z.suit := by rw [← hcs, hzs]
              have hrk : c.rank = z.rank := Rank.toIdx_inj (by
                rw [← hnext, ← hcs, hrungu, hzr])
              have hcz : c = z := by
                rw [show c = Card.mk c.suit c.rank from rfl,
                    show z = Card.mk z.suit z.rank from rfl, hcsz, hrk]
              exact hane (pileOfTop_inj (hcz ▸ hpodc) hpodu)
            · rw [if_neg hcs]; exact hrungu
          exact ⟨step_wf hwu hstep, hpodu', hfacew, hhidw, hrungw⟩
  exact (H w0 hreach).2.2.2.2

#print axioms lone_hidden_blocks

/-- The licence for climbable states: if the climb advances suit `s` past `z`,
then `z` was not a lone-over-hidden card. -/
theorem licence_of_climbable {st w0 : State} {a : Anchor} {z : Card} {s : Suit}
    (hwf : st.WF) (hpod : st.pileOfTop z = some a)
    (hface : (st.piles a).faceUp = [z]) (hhid : (st.piles a).hidden ≠ [])
    (hzs : z.suit = s) (hzr : z.rank.toIdx = rungAt st s)
    (hreach : RaiseReach st w0) (hgt : z.rank.toIdx < rungAt w0 s) : False := by
  have h := lone_hidden_blocks hwf hpod hface hhid hzs hzr hreach
  rw [h, ← hzr] at hgt
  exact Nat.lt_irrefl _ hgt

/-- The climbable form of the residual: a PREFIX witness from which the cap is
raise-reachable.  (Measured: M1, 100%.) -/
def ClimbablePrefixWitness : Prop :=
  forall (u s s' : State) (cap : Suit -> Nat),
    u.WF -> OneColourClosure.Forkless u ->
    sameOrbitSetoid.r u s -> sameOrbitSetoid.r u s' ->
    (forall σ, cap σ <= 13) ->
    (forall σ, rungAt s σ <= cap σ) -> (forall σ, rungAt s' σ <= cap σ) ->
    exists w, sameOrbitSetoid.r u w /\ w.WF /\ Under w cap /\ PrefixOK w cap /\
      exists c, RaiseReach w c /\ forall σ, rungAt c σ = cap σ

/-- The consumer from the climbable residual: no `StepExists` argument. -/
theorem minimalFullJoin_of_climbable {u s s' : State} {cap : Suit -> Nat}
    (hW : ClimbablePrefixWitness)
    (hwf : u.WF) (hfl : OneColourClosure.Forkless u)
    (hcls : sameOrbitSetoid.r u s) (hcls' : sameOrbitSetoid.r u s')
    (hcap13 : forall σ, cap σ <= 13)
    (hup : forall σ, Nat.max (rungAt s σ) (rungAt s' σ) <= cap σ)
    (hmin : forall v, sameOrbitSetoid.r s v ->
        (forall σ, Nat.max (rungAt s σ) (rungAt s' σ) <= rungAt v σ) ->
        forall σ, cap σ <= rungAt v σ) :
    exists w, OneColourClosure.MinimalFullJoin s s' w := by
  have hs : forall σ, rungAt s σ <= cap σ :=
    fun σ => Nat.le_trans (Nat.le_max_left _ _) (hup σ)
  have hs' : forall σ, rungAt s' σ <= cap σ :=
    fun σ => Nat.le_trans (Nat.le_max_right _ _) (hup σ)
  obtain ⟨w0, hw0cls, hw0wf, -, -, c, hreach, hrungs⟩ :=
    hW u s s' cap hwf hfl hcls hcls' hcap13 hs hs'
  obtain ⟨-, horb⟩ := RaiseReach.wf_and_orbit hreach hw0wf
  have hwcls : sameOrbitSetoid.r u c := sameOrbitSetoid.iseqv.trans hw0cls horb
  refine ⟨c, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · exact sameOrbitSetoid.iseqv.trans (sameOrbitSetoid.iseqv.symm hcls) hwcls
    · intro σ
      rw [hrungs σ]
      exact hup σ
  · intro v hv σ
    rw [hrungs σ]
    exact hmin v hv.1 hv.2 σ

#print axioms licence_of_climbable
#print axioms minimalFullJoin_of_climbable

/-- The campaign-facing assembly: the one-colour-exact join from the three
measured inputs (climbable witness, closure law, cap certificate). -/
theorem fullJoinAtLeastOneColour_of_climbable {u s s' : State} {cap : Suit -> Nat}
    (hW : ClimbablePrefixWitness)
    (hcl : OneColourClosure.ForklessOneColourClosure)
    (hwf : u.WF) (hfl : OneColourClosure.Forkless u)
    (hcls : sameOrbitSetoid.r u s) (hcls' : sameOrbitSetoid.r u s')
    (hws : s.WF)
    (hcap13 : forall σ, cap σ <= 13)
    (hup : forall σ, Nat.max (rungAt s σ) (rungAt s' σ) <= cap σ)
    (hmin : forall v, sameOrbitSetoid.r s v ->
        (forall σ, Nat.max (rungAt s σ) (rungAt s' σ) <= rungAt v σ) ->
        forall σ, cap σ <= rungAt v σ) :
    exists w, OneColourClosure.FullJoinAtLeastOneColour s s' w := by
  obtain ⟨w, hminjoin⟩ :=
    minimalFullJoin_of_climbable hW hwf hfl hcls hcls' hcap13 hup hmin
  have hfls : OneColourClosure.Forkless s := by
    intro F hsF
    exact hfl F (sameOrbitSetoid.iseqv.trans hcls hsF)
  have hss' : sameOrbitSetoid.r s s' :=
    sameOrbitSetoid.iseqv.trans (sameOrbitSetoid.iseqv.symm hcls) hcls'
  exact ⟨w, hminjoin.1,
    OneColourClosure.minimalFullJoin_oneColourExact hcl hws hfls hss' hminjoin⟩

#print axioms fullJoinAtLeastOneColour_of_climbable

end PrefixClimb





