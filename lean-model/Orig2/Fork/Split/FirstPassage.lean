import Orig2.Substrate.Position
import Orig2.Substrate.CargoRaise

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
/-!
# Orig2.FirstPassage — the per-suit first-passage ledger

THE COMBINATORIAL HALF of the `SatDifferFork` dip.  Along a witness
play `ρ : u → v`, a suit `σ` whose rung differs at the endpoints has an
exact FIRST PASSAGE: a longest prefix on which `rungAt · σ` still reads
the origin rung, followed by exactly one legal move that changes it.
The changing move is a `tabToFound` raise or a `foundToTab` pull of a
`σ`-card:

* at a raise, the card is S-live at the prior state
  (`canRaiseS_flat_necessity` gives the flat seat shape);
* at a pull, the card is the `σ`-foundation top and the rung lands on
  its rank index.

The kit exposes:

* `firstPassage_exists`, `FirstPassage.shape`, `FirstPassage.shape_flat`;
* `FirstRise`, `firstRise_of_rung_lt`, `FirstRise.card_live` — the
  threshold form (first state above a level `k` is the rank-`k` raise),
  the registry restatement of the frozen `lowslab_rung_walk`.

The down-dual `FirstFall` (the last pull before the first raise) is now
proved as well: `firstRise_or_firstFall_of_rung_ne` gives both halves of
the dip boundary.

House compliance: additive leaf (`Orig2.Position` + `Orig2.CargoRaise`);
zero `sorry`, zero `Classical.choice`; battery at tail.
-/

namespace SatDifferCensus

/-! ## §0. The foundation-top rank row -/

/-- **THE FOUNDATION TOP'S RANK IS THE RUNG MINUS ONE.**  At a `WF`
state the top card of a suit's foundation sits at rank index
`rungAt st s - 1`.

Proof route (fresh; the Classification card's copy is private at
`Orig2/Substrate/Classification.lean:871`): a `WF` foundation is a take of the
build order `upCards` (`found_prefix`), the last slot of a take at
index `m - 1` is the build card of rank index `m - 1`
(`List.getElem?_take` + the tabulation `FoundKit.Rk`), so the top's
rank index is the take length minus one. -/
theorem foundTop_rank_succ {st : State} (hwf : st.WF) {s : Suit} {c : Card}
    (h : st.foundTop s = some c) :
    c.rank.toIdx + 1 = rungAt st s := by
  obtain ⟨n, hn⟩ := hwf.found_prefix s
  have hlast : lastOf (st.found s) = some c := h
  have hne : st.found s ≠ [] := by
    intro hc
    rw [hc] at hlast
    exact absurd hlast (by simp [lastOf])
  have hpos : 0 < (st.found s).length := by
    cases hf : st.found s with
    | nil => exact absurd hf hne
    | cons x xs => simp
  -- the top as the last slot of the take
  have hget : (s.upCards.take n)[(s.upCards.take n).length - 1]? = some c := by
    have h1 : (st.found s).getLast? = some c := by
      rw [tfc_getLast?_lastOf]
      exact hlast
    rw [List.getLast?_eq_getElem?] at h1
    rw [hn] at h1
    exact h1
  -- the take length is the rung
  have hlen : (s.upCards.take n).length = min n 13 := by
    rw [List.length_take, Suit.upCards_length]
  have hpos' : 0 < min n 13 := by
    rw [← hlen]
    simpa [hn] using hpos
  have hi_lt_n : min n 13 - 1 < n := by omega
  have hi_lt_13 : min n 13 - 1 < 13 := by omega
  -- read the last slot off the take
  have htake : s.upCards[min n 13 - 1]? = some c := by
    have h' := hget
    rw [hlen] at h'
    rw [List.getElem?_take] at h'
    rw [ite_eq_left hi_lt_n] at h'
    exact h'
  -- the build order's slot at index `i` is the rank-`i` card
  have hup : s.upCards[min n 13 - 1]? =
      some (Card.mk s (FoundKit.Rk (min n 13 - 1))) := by
    have hpin : (Rank.all : List Rank)[min n 13 - 1]? =
        some (FoundKit.Rk (min n 13 - 1)) := by
      have hidx : (FoundKit.Rk (min n 13 - 1)).toIdx = min n 13 - 1 :=
        FoundKit.Rk_toIdx (min n 13 - 1) hi_lt_13
      rw [← hidx]
      generalize FoundKit.Rk (min n 13 - 1) = rk
      cases rk <;> rfl
    show (Rank.all.map (Card.mk s))[min n 13 - 1]? =
      some (Card.mk s (FoundKit.Rk (min n 13 - 1)))
    rw [List.getElem?_map, hpin]
    rfl
  have hc : c = Card.mk s (FoundKit.Rk (min n 13 - 1)) := by
    rw [hup] at htake
    exact (Option.some.inj htake).symm
  have hcidx : c.rank.toIdx = min n 13 - 1 := by
    rw [hc]
    exact FoundKit.Rk_toIdx (min n 13 - 1) hi_lt_13
  have hrung : rungAt st s = min n 13 := by
    show (st.found s).length = min n 13
    rw [hn]
    exact hlen
  omega

/-! ## §1. First passage: the predicate and its existence -/

/-- Every state reached by a legal walk from a `WF` state is `WF`
(`step_wf`, `Orig2/Substrate/StepWF.lean:995`, along the walk). -/
theorem Walk_wf_end {P : State → Move → Prop} {a b : State} {ρ : List Move}
    (h : Walk P a ρ b) (hwf : a.WF) : b.WF := by
  induction h with
  | nil st => exact hwf
  | cons _ hstep _ ih => exact ih (step_wf hwf hstep)

/-- A witness shuffle preserves well-formedness. -/
theorem ShufflePlayW.wf_end {a b : State} {ρ : List Move}
    (h : ShufflePlayW a ρ b) (hwf : a.WF) : b.WF :=
  Walk_wf_end h hwf

/-- **A FIRST PASSAGE of suit `σ` along a witness play `ρ : u → v`.**

`ρ` splits as `pre ++ m :: rest`; `pre` is a witness play to `mid` on
which EVERY prefix still reads the origin rung `rungAt u σ`, and the
single letter `m` (witnessed reversible at `mid`) is the first one
that changes that rung.  (`post` is `m`'s landing.)  Prop-valued so it
composes with the campaign's statements. -/
def FirstPassage (u v : State) (ρ : List Move) (σ : Suit) : Prop :=
  ∃ (pre : List Move) (m : Move) (rest : List Move) (mid post : State),
    ρ = pre ++ m :: rest ∧
    ShufflePlayW u pre mid ∧
    State.step mid m = some post ∧
    ShufflePlayW post rest v ∧
    reversibleAtW mid m ∧
    (∀ (a b : List Move), pre = a ++ b → ∀ y : State,
      u.run a = some y → rungAt y σ = rungAt u σ) ∧
    rungAt post σ ≠ rungAt mid σ

/-- **FIRST PASSAGE EXISTS** whenever the endpoints' `σ`-rungs differ.
(The play is finite, the rung is `Nat`-valued, and the empty play cannot
change anything.) -/
theorem firstPassage_exists {u v : State} {ρ : List Move} {σ : Suit}
    (h : ShufflePlayW u ρ v) (hne : rungAt u σ ≠ rungAt v σ) :
    FirstPassage u v ρ σ := by
  revert hne
  induction h with
  | nil st =>
      intro hne
      exact absurd rfl hne
  | @cons st s₁ W m ρ hlet hstep hrest ih =>
      intro hne
      by_cases hchg : rungAt s₁ σ = rungAt st σ
      · -- the letter does not change the rung: the passage is later
        have hne' : rungAt s₁ σ ≠ rungAt W σ := by
          rw [hchg]
          exact hne
        obtain ⟨pre, m', rest', mid, post, hplay, hpre, hstep', hrest',
          hlet', hstable', hchange'⟩ := ih hne'
        refine ⟨m :: pre, m', rest', mid, post, ?_, ?_, hstep', hrest',
          hlet', ?_, hchange'⟩
        · rw [hplay]
          rfl
        · exact Walk.cons hlet hstep hpre
        · intro a b hab y hrun
          cases a with
          | nil =>
              have hy : st = y := Option.some.inj hrun
              subst hy
              rfl
          | cons m'' a' =>
              simp only [List.cons_append] at hab
              injection hab with hm htl
              subst hm
              obtain ⟨s, hsd, hrt⟩ := State.run_cons hrun
              have hs : s = s₁ := Option.some.inj (hsd.symm.trans hstep)
              rw [hs] at hrt
              exact (hstable' a' b htl y hrt).trans hchg
      · -- the head letter is the passage
        refine ⟨[], m, ρ, st, s₁, rfl, Walk.nil st, hstep, hrest, hlet, ?_,
          hchg⟩
        intro a b hab y hrun
        cases a with
        | nil =>
            have hy : st = y := Option.some.inj hrun
            subst hy
            rfl
        | cons m' a' =>
            exact absurd hab (by simp)

/-! ## §2. The changing letter is a `σ`-raise or a `σ`-pull -/

/-- **THE SINGLE-STEP RUNG CLASSIFICATION.**  A witnessed reversible
letter that changes the `σ`-rung is a `tabToFound` of a `σ`-card
(climbing by one) or a `foundToTab` of a `σ`-card (descending by one).
Draw and tableau-slide letters hold the rung; the waste letters never
ride a witness play.  `hmid` pins the prior rung to the origin. -/
theorem step_rung_classification {u mid post : State} {m : Move} {σ : Suit}
    (hstep : State.step mid m = some post) (hlet : reversibleAtW mid m)
    (hmid : rungAt mid σ = rungAt u σ)
    (hchange : rungAt post σ ≠ rungAt mid σ) :
    (∃ c : Card, m = Move.tabToFound c ∧ c.suit = σ ∧
        rungAt post σ = rungAt u σ + 1) ∨
      (∃ (c : Card) (b : Base), m = Move.foundToTab c b ∧ c.suit = σ ∧
        rungAt post σ = rungAt u σ - 1) := by
  cases hm : m with
  | draw =>
      exact absurd (rungAt_draw (hm ▸ hstep) σ) hchange
  | wasteToFound c =>
      exact absurd (hm ▸ hlet) (wasteToFound_not_reversibleAtW mid c)
  | wasteToTab c b =>
      exact absurd (hm ▸ hlet) (wasteToTab_not_reversibleAtW mid c b)
  | tabToFound c =>
      have hr := rungAt_tabToFound (hm ▸ hstep) σ
      by_cases hσ : σ = c.suit
      · refine Or.inl ⟨c, rfl, hσ.symm, ?_⟩
        rw [hr, ite_eq_left hσ, hmid]
      · exact absurd (by rw [hr, ite_eq_right hσ]) hchange
  | foundToTab c b =>
      have hr := rungAt_foundToTab (hm ▸ hstep) σ
      by_cases hσ : σ = c.suit
      · refine Or.inr ⟨c, b, rfl, hσ.symm, ?_⟩
        rw [hr, ite_eq_left hσ, hmid]
      · exact absurd (by rw [hr, ite_eq_right hσ]) hchange
  | tabToTab c b =>
      exact absurd (rungAt_tabToTab (hm ▸ hstep) σ) hchange

/-- The first-passage classification: the changing letter is a `σ`-raise
or a `σ`-pull, with the exact rung arithmetic against the origin. -/
theorem FirstPassage.classification {u v : State} {ρ : List Move} {σ : Suit}
    (fp : FirstPassage u v ρ σ) :
    ∃ (pre : List Move) (m : Move) (rest : List Move) (mid post : State),
      ρ = pre ++ m :: rest ∧
      ShufflePlayW u pre mid ∧ State.step mid m = some post ∧
      ShufflePlayW post rest v ∧
      ((∃ c : Card, m = Move.tabToFound c ∧ c.suit = σ ∧
          rungAt post σ = rungAt u σ + 1) ∨
        (∃ (c : Card) (b : Base), m = Move.foundToTab c b ∧ c.suit = σ ∧
          rungAt post σ = rungAt u σ - 1)) := by
  obtain ⟨pre, m, rest, mid, post, hplay, hpre, hstep, hrest, hlet, hstable,
    hchange⟩ := fp
  have hrung : rungAt mid σ = rungAt u σ :=
    hstable pre [] (List.append_nil pre).symm mid (Walk_run _ hpre)
  exact ⟨pre, m, rest, mid, post, hplay, hpre, hstep, hrest,
    step_rung_classification hstep hlet hrung hchange⟩

/-- **EVERY PREFIX BEFORE THE PASSAGE READS THE ORIGIN RUNG.** -/
theorem FirstPassage.pre_rung {u v : State} {ρ : List Move} {σ : Suit}
    (fp : FirstPassage u v ρ σ) :
    ∃ (pre : List Move) (m : Move) (rest : List Move) (mid post : State),
      ρ = pre ++ m :: rest ∧ ShufflePlayW u pre mid ∧
      rungAt mid σ = rungAt u σ ∧
      (∀ (a b : List Move), pre = a ++ b → ∀ y : State,
        u.run a = some y → rungAt y σ = rungAt u σ) := by
  obtain ⟨pre, m, rest, mid, post, hplay, hpre, hstep, hrest, hlet, hstable,
    hchange⟩ := fp
  exact ⟨pre, m, rest, mid, post, hplay, hpre,
    hstable pre [] (List.append_nil pre).symm mid (Walk_run _ hpre), hstable⟩

/-! ## §3. The local shapes at the passage -/

/-- `tabToFoundR` is the decidability shape of `CanRaise`: the seat
clause of `CanRaise` is exactly the chop/king clause of the shape. -/
theorem canRaise_of_tabToFoundR {st : State} {c : Card}
    (h : tabToFoundR st c = true) : CanRaise st c := by
  unfold tabToFoundR at h
  split at h
  · exact absurd h (by simp)
  · rename_i hn
    split at h
    · exact absurd h (by simp)
    · rename_i a hp
      refine ⟨hn, a, hp, ?_⟩
      split at h
      · -- chop empty: only a bare king seat
        rename_i hchop
        split at h
        · rename_i hhidden
          exact Or.inr ⟨hhidden, of_decide_eq_true h⟩
        · exact absurd h (by simp)
      · -- chop nonempty: the giveback seat
        rename_i hchop
        exact Or.inl (by intro hc; rw [hchop] at hc; exact absurd hc (by simp))

/-- **AT A RAISE THE CARD IS S-LIVE** — a reversible `tabToFound c` at
`WF` reads `tabToFoundR` (`Orig2/Substrate/Classification.lean:1871`), whose seat
clause is exactly `CanRaise`; the zero-leg span gives `CanRaiseS`. -/
theorem step_raise_live {mid post : State} {c : Card} (hwf : mid.WF)
    (hstep : State.step mid (Move.tabToFound c) = some post)
    (hlet : reversibleAtW mid (Move.tabToFound c)) :
    CanRaiseS mid c :=
  CanRaiseS.now c
    (canRaise_of_tabToFoundR ((tabToFoundR_iff_reversibleAtW hwf c).mpr hlet))

/-- **THE FLAT SEAT SHAPE AT A RAISE** — the `canRaiseS_flat_necessity`
row (`Orig2/Substrate/CargoRaise.lean:329`) instantiated at the passage state:
`c` is next-up, sits face-up as `bs ++ c :: run`, has company below or
the bare-king cell, and either no run above or its twin tops a pile.
These are exactly the two escapes the `SSaturated` endpoints bar (the
cover's own raise; the covered card's slide cascade). -/
theorem step_raise_flat {mid post : State} {c : Card} (hwf : mid.WF)
    (hstep : State.step mid (Move.tabToFound c) = some post)
    (hlet : reversibleAtW mid (Move.tabToFound c)) :
    mid.nextUp c = true ∧
      ∃ a bs run, (mid.piles a).faceUp = bs ++ c :: run ∧
        (bs ≠ [] ∨ ((mid.piles a).hidden = [] ∧ c.rank = Rank.king)) ∧
        (run = [] ∨ mid.pileOfTop c.twin ≠ none) :=
  canRaiseS_flat_necessity hwf (step_raise_live hwf hstep hlet)

/-- **AT A PULL THE PULLED CARD IS THE FOUNDATION TOP** and the rung
lands on its rank index (`foundTop_rank_succ`). -/
theorem step_pull_shape {mid post : State} {c : Card} {b : Base} {σ : Suit}
    (hwf : mid.WF) (hstep : State.step mid (Move.foundToTab c b) = some post)
    (hchange : rungAt post σ ≠ rungAt mid σ) :
    mid.foundTop σ = some c ∧ c.rank.toIdx = rungAt post σ := by
  have hr := rungAt_foundToTab hstep σ
  have hσ : σ = c.suit := by
    by_cases h : σ = c.suit
    · exact h
    · exact absurd (by rw [hr, ite_eq_right h]) hchange
  obtain ⟨c', htop, hc'c, -, -⟩ := step_foundToTab_inv hstep
  rw [hc'c] at htop
  have htop' : mid.foundTop σ = some c := by
    rw [hσ]
    exact htop
  have hidx : c.rank.toIdx + 1 = rungAt mid σ :=
    foundTop_rank_succ hwf htop'
  have hpost : rungAt post σ = rungAt mid σ - 1 := by
    rw [hr, ite_eq_left hσ]
  refine ⟨htop', ?_⟩
  omega

/-- **THE STRONGEST CLEAN FIRST-PASSAGE LEMMA** — existence and local
shape in one row: the play splits at a longest rung-preserving prefix;
the changing letter is a `σ`-raise (the raised card S-live at the moved
origin, the rung climbing one) or a `σ`-pull (the pulled card the
foundation top, the rung landing on its rank index). -/
theorem FirstPassage.shape {u v : State} {ρ : List Move} {σ : Suit}
    (hwf : u.WF) (fp : FirstPassage u v ρ σ) :
    ∃ (pre : List Move) (m : Move) (rest : List Move) (mid post : State),
      ρ = pre ++ m :: rest ∧
      ShufflePlayW u pre mid ∧ State.step mid m = some post ∧
      ShufflePlayW post rest v ∧
      (∀ (a b : List Move), pre = a ++ b → ∀ y : State,
        u.run a = some y → rungAt y σ = rungAt u σ) ∧
      ((∃ c : Card, m = Move.tabToFound c ∧ c.suit = σ ∧
          CanRaiseS mid c ∧ rungAt post σ = rungAt u σ + 1) ∨
        (∃ (c : Card) (b : Base), m = Move.foundToTab c b ∧ c.suit = σ ∧
          mid.foundTop σ = some c ∧ c.rank.toIdx = rungAt post σ ∧
          rungAt post σ = rungAt u σ - 1)) := by
  obtain ⟨pre, m, rest, mid, post, hplay, hpre, hstep, hrest, hlet, hstable,
    hchange⟩ := fp
  have hmid : mid.WF := Walk_wf_end hpre hwf
  have hrung : rungAt mid σ = rungAt u σ :=
    hstable pre [] (List.append_nil pre).symm mid (Walk_run _ hpre)
  refine ⟨pre, m, rest, mid, post, hplay, hpre, hstep, hrest, hstable, ?_⟩
  rcases step_rung_classification hstep hlet hrung hchange with
    ⟨c, hm, hs, hr⟩ | ⟨c, b, hm, hs, hr⟩
  · refine Or.inl ⟨c, hm, hs, ?_, hr⟩
    exact step_raise_live hmid (hm ▸ hstep) (hm ▸ hlet)
  · refine Or.inr ⟨c, b, hm, hs, ?_, ?_, hr⟩
    · exact (step_pull_shape hmid (hm ▸ hstep) hchange).1
    · exact (step_pull_shape hmid (hm ▸ hstep) hchange).2

/-- **THE DIP FEED, FLAT-SEAT FORM** — the same census with the raise
arm expanded by `canRaiseS_flat_necessity` (`Orig2/Substrate/CargoRaise.lean:329`):
the raised `σ`-card is next-up, its face-up seat is `bs ++ c :: run`,
it has company below (or is the bare king), and either no run above it
or its twin tops a pile.  These are exactly the two escapes the
`SSaturated` endpoints bar (the cover's own raise; the covered card's
slide cascade). -/
theorem FirstPassage.shape_flat {u v : State} {ρ : List Move} {σ : Suit}
    (hwf : u.WF) (fp : FirstPassage u v ρ σ) :
    ∃ (pre : List Move) (m : Move) (rest : List Move) (mid post : State),
      ρ = pre ++ m :: rest ∧
      ShufflePlayW u pre mid ∧ State.step mid m = some post ∧
      ShufflePlayW post rest v ∧
      (∀ (a b : List Move), pre = a ++ b → ∀ y : State,
        u.run a = some y → rungAt y σ = rungAt u σ) ∧
      ((∃ (c : Card) (a : Anchor) (bs run : List Card),
          m = Move.tabToFound c ∧ c.suit = σ ∧ mid.nextUp c = true ∧
          (mid.piles a).faceUp = bs ++ c :: run ∧
          (bs ≠ [] ∨ ((mid.piles a).hidden = [] ∧ c.rank = Rank.king)) ∧
          (run = [] ∨ mid.pileOfTop c.twin ≠ none) ∧
          rungAt post σ = rungAt u σ + 1) ∨
        (∃ (c : Card) (b : Base), m = Move.foundToTab c b ∧ c.suit = σ ∧
          mid.foundTop σ = some c ∧ c.rank.toIdx = rungAt post σ ∧
          rungAt post σ = rungAt u σ - 1)) := by
  obtain ⟨pre, m, rest, mid, post, hplay, hpre, hstep, hrest, hstable,
    hdisj⟩ := FirstPassage.shape hwf fp
  have hmid : mid.WF := Walk_wf_end hpre hwf
  refine ⟨pre, m, rest, mid, post, hplay, hpre, hstep, hrest, hstable, ?_⟩
  rcases hdisj with ⟨c, hm, hs, hS, hr⟩ | ⟨c, b, hm, hs, htop, hidx, hr⟩
  · obtain ⟨hn, a, bs, run, hface, hseat, hrun⟩ :=
      canRaiseS_flat_necessity hmid hS
    exact Or.inl ⟨c, a, bs, run, hm, hs, hn, hface, hseat, hrun, hr⟩
  · exact Or.inr ⟨c, b, hm, hs, htop, hidx, hr⟩

/-! ## §4. The first rise above a level (the dip's "first raise") -/

/-- **A FIRST RISE of suit `σ` above the level `k`** along `ρ : u → v`:
a longest prefix all of whose states read `≤ k`, then a single legal
`tabToFound` of a `σ`-card of rank index exactly `k` at a state whose
`σ`-rung is exactly `k`, landing at `k + 1`.  This is the frozen
`lowslab_rung_walk` (`Orig/LowSlab.lean:1239`) restated over the
registry's `rungAt`; it is the dip's "first raise of the twin at the
rung exactly". -/
def FirstRise (u v : State) (ρ : List Move) (σ : Suit) (k : Nat) : Prop :=
  ∃ (pre : List Move) (m : Move) (rest : List Move) (mid post : State)
      (c : Card),
    ρ = pre ++ m :: rest ∧
    ShufflePlayW u pre mid ∧
    State.step mid m = some post ∧
    ShufflePlayW post rest v ∧
    reversibleAtW mid m ∧
    (∀ (a b : List Move), pre = a ++ b → ∀ y : State,
      u.run a = some y → rungAt y σ ≤ k) ∧
    rungAt mid σ = k ∧
    m = Move.tabToFound c ∧ c.suit = σ ∧ c.rank.toIdx = k ∧
    rungAt post σ = k + 1

/-- The crossing letter: a witnessed reversible step whose `σ`-rung
leaves the half-line `≤ k` is a `σ`-raise of the rank-`k` card, firing
at rung exactly `k` and landing at `k + 1`. -/
private theorem step_rise_classification {st s₁ : State} {m : Move} {σ : Suit}
    {k : Nat} (hstep : State.step st m = some s₁) (hlet : reversibleAtW st m)
    (hle : rungAt st σ ≤ k) (hk : k < rungAt s₁ σ) :
    ∃ (c : Card), m = Move.tabToFound c ∧ c.suit = σ ∧
      c.rank.toIdx = k ∧ rungAt st σ = k ∧ rungAt s₁ σ = k + 1 := by
  cases hm : m with
  | draw =>
      have hd := rungAt_draw (hm ▸ hstep) σ
      exfalso
      omega
  | wasteToFound c =>
      exact absurd (hm ▸ hlet) (wasteToFound_not_reversibleAtW st c)
  | wasteToTab c b =>
      exact absurd (hm ▸ hlet) (wasteToTab_not_reversibleAtW st c b)
  | tabToFound c =>
      have hr := rungAt_tabToFound (hm ▸ hstep) σ
      by_cases hσ : σ = c.suit
      · have hstk : rungAt st σ = k := by
          have h1 : rungAt s₁ σ = rungAt st σ + 1 := by
            rw [hr, ite_eq_left hσ]
          omega
        have hs₁ : rungAt s₁ σ = k + 1 := by
          have h1 : rungAt s₁ σ = rungAt st σ + 1 := by
            rw [hr, ite_eq_left hσ]
          omega
        have hnxt : st.nextUp c = true :=
          (step_tabToFound_inv (hm ▸ hstep)).1
        have hcrank : c.rank.toIdx = k := by
          have h2 : c.rank.toIdx = rungAt st c.suit := by
            simpa [State.nextUp, State.foundHeight, rungAt]
              using (of_decide_eq_true hnxt)
          rw [h2, ← hσ]
          exact hstk
        exact ⟨c, rfl, hσ.symm, hcrank, hstk, hs₁⟩
      · have h1 : rungAt s₁ σ = rungAt st σ := by
          rw [hr, ite_eq_right hσ]
        exfalso
        omega
  | foundToTab c b =>
      have hr := rungAt_foundToTab (hm ▸ hstep) σ
      by_cases hσ : σ = c.suit
      · have h1 : rungAt s₁ σ = rungAt st σ - 1 := by
          rw [hr, ite_eq_left hσ]
        exfalso
        omega
      · have h1 : rungAt s₁ σ = rungAt st σ := by
          rw [hr, ite_eq_right hσ]
        exfalso
        omega
  | tabToTab c b =>
      have h1 := rungAt_tabToTab (hm ▸ hstep) σ
      exfalso
      omega

/-- A first rise whose crossing letter is the head of the play. -/
private theorem firstRise_head {st s₁ W : State} {m : Move} {ρ : List Move}
    {σ : Suit} {k : Nat} (hstep : State.step st m = some s₁)
    (hlet : reversibleAtW st m) (hrest : ShufflePlayW s₁ ρ W)
    (hle : rungAt st σ ≤ k) (hk : k < rungAt s₁ σ) :
    FirstRise st W (m :: ρ) σ k := by
  obtain ⟨c, hm, hcs, hcr, hstk, hs₁⟩ :=
    step_rise_classification hstep hlet hle hk
  refine ⟨[], m, ρ, st, s₁, c, by simp, Walk.nil st, hstep, hrest, hlet, ?_,
    hstk, hm, hcs, hcr, hs₁⟩
  intro a b hab y hrun
  cases a with
  | nil =>
      have hy : st = y := Option.some.inj hrun
      subst hy
      exact hle
  | cons m' a' => exact absurd hab (by simp)

/-- Carrying a first rise through a rung-preserving head letter. -/
private theorem firstRise_carry {st s₁ W : State} {m : Move} {ρ : List Move}
    {σ : Suit} {k : Nat} (hstep : State.step st m = some s₁)
    (hlet : reversibleAtW st m) (hle : rungAt st σ ≤ k)
    (hinner : FirstRise s₁ W ρ σ k) :
    FirstRise st W (m :: ρ) σ k := by
  obtain ⟨pre, m', rest', mid, post, c, hplay, hpre', hstep', hrest',
    hlet', hprele', hmidr, hm', hcs, hcr, hpostr⟩ := hinner
  refine ⟨m :: pre, m', rest', mid, post, c, ?_, ?_, hstep', hrest',
    hlet', ?_, hmidr, hm', hcs, hcr, hpostr⟩
  · rw [hplay]
    rfl
  · exact Walk.cons hlet hstep hpre'
  · intro a b hab y hrun
    cases a with
    | nil =>
        have hy : st = y := Option.some.inj hrun
        subst hy
        exact hle
    | cons m'' a' =>
        simp only [List.cons_append] at hab
        injection hab with hm htl
        subst hm
        obtain ⟨s, hsd, hrt⟩ := State.run_cons hrun
        have hs : s = s₁ := Option.some.inj (hsd.symm.trans hstep)
        rw [hs] at hrt
        exact hprele' a' b htl y hrt

/-- **A FIRST RISE EXISTS** whenever the start reads `≤ k` and the end
reads `> k`.  (Per-leg arithmetic: only a `σ`-raise can carry the rung
past `k`, and it fires at rung exactly `k`.) -/
theorem firstRise_exists {u v : State} {ρ : List Move} {σ : Suit} {k : Nat}
    (h : ShufflePlayW u ρ v) (hle : rungAt u σ ≤ k) (hgt : k < rungAt v σ) :
    FirstRise u v ρ σ k := by
  revert hle hgt
  induction h with
  | nil st =>
      intro hle hgt
      exfalso
      omega
  | @cons st s₁ W m ρ hlet hstep hrest ih =>
      intro hle hgt
      by_cases hle₁ : rungAt s₁ σ ≤ k
      · -- no crossing yet: carry the walk
        exact firstRise_carry hstep hlet hle (ih hle₁ hgt)
      · -- the head letter crosses
        have hk : k < rungAt s₁ σ := by omega
        exact firstRise_head hstep hlet hrest hle hk

/-- The differing-rung read: a strict climb of `σ` gives the first rise
above the STARTING rung — the first state whose rung exceeds
`rungAt u σ` is a `σ`-raise from rung `rungAt u σ` itself. -/
theorem firstRise_of_rung_lt {u v : State} {ρ : List Move} {σ : Suit}
    (h : ShufflePlayW u ρ v) (hlt : rungAt u σ < rungAt v σ) :
    FirstRise u v ρ σ (rungAt u σ) :=
  firstRise_exists h (Nat.le_refl _) hlt

/-- **THE FIRST-RISE CARD IS S-LIVE** — the dip's twin-raise local
shape, extracted at the moved origin (`step_raise_live`). -/
theorem FirstRise.card_live {u v : State} {ρ : List Move} {σ : Suit} {k : Nat}
    (hwf : u.WF) (fr : FirstRise u v ρ σ k) :
    ∃ (mid post : State) (c : Card),
      CanRaiseS mid c ∧ c.suit = σ ∧ c.rank.toIdx = k ∧
        rungAt mid σ = k ∧ rungAt post σ = k + 1 := by
  obtain ⟨pre, m, rest, mid, post, c, hplay, hpre, hstep, hrest, hlet,
    hprele, hmidr, hm, hcs, hcr, hpostr⟩ := fr
  have hmid : mid.WF := Walk_wf_end hpre hwf
  exact ⟨mid, post, c, step_raise_live hmid (hm ▸ hstep) (hm ▸ hlet),
    hcs, hcr, hmidr, hpostr⟩

/-! ## §0. Local copy of the pull-liveness lemma (promotion-clean) -/

/-- **A PULL'S CARD IS VANILLA-LIVE AT THE LANDING.** -/
theorem canRaise_post_of_pull {st w : State} (hwf : st.WF) {c : Card} {b : Base}
    (hstep : State.step st (Move.foundToTab c b) = some w)
    (hnext : w.nextUp c = true) : CanRaise w c := by
  obtain ⟨c', htop, hc', hcp, hs⟩ := step_foundToTab_inv hstep
  subst c'
  have hwfw : w.WF := step_wf hwf hstep
  cases b with
  | inl a0 =>
      have hp : w.piles a0 = (⟨[], [c]⟩ : Pile) := by
        rw [hs]
        simp [State.putCard, State.setPile]
      have hpa : w.pileOfTop c = some a0 :=
        (pileOfTop_eq_some_iff hwfw).2 (by rw [hp]; rfl)
      refine ⟨hnext, a0, hpa, Or.inr ⟨?_, (canPlace_inl hcp).2⟩⟩
      rw [hp]
  | inr z =>
      obtain ⟨k, hkz, hfit⟩ := canPlace_inr hcp
      have hp : w.piles k =
          { st.piles k with faceUp := (st.piles k).faceUp ++ [c] } := by
        rw [hs]
        simp [State.putCard, State.setPile, setFound_piles, hkz]
      have hpa : w.pileOfTop c = some k :=
        (pileOfTop_eq_some_iff hwfw).2 (by rw [hp]; exact lastOf_snoc)
      have hne : (st.piles k).faceUp ≠ [] := (pileOfTop_top hkz).1
      obtain ⟨x, xs, hx⟩ : ∃ x xs, (st.piles k).faceUp = x :: xs := by
        cases hh : (st.piles k).faceUp with
        | nil => exact absurd hh hne
        | cons x xs => exact ⟨x, xs, rfl⟩
      refine ⟨hnext, k, hpa, Or.inl ?_⟩
      rw [hp, hx]
      simp [chop]

/-! ## §1. The down-dual predicate -/

/-- **A FIRST FALL of suit `σ` below the level `k`** along `ρ : u → v`:
a longest prefix all of whose states read `≥ k`, then a single legal
`foundToTab` of a `σ`-card `c` at a state whose `σ`-rung is exactly `k`,
landing at `k - 1`.  The card's rank index is `k - 1`, i.e. the landing
rung.  Mirror of `FirstRise` (`Orig2/Fork/Split/FirstPassage.lean:413`). -/
def FirstFall (u v : State) (ρ : List Move) (σ : Suit) (k : Nat) : Prop :=
  ∃ (pre : List Move) (m : Move) (rest : List Move) (mid post : State)
      (c : Card) (b : Base),
    ρ = pre ++ m :: rest ∧
    ShufflePlayW u pre mid ∧
    State.step mid m = some post ∧
    ShufflePlayW post rest v ∧
    reversibleAtW mid m ∧
    (∀ (a b₂ : List Move), pre = a ++ b₂ → ∀ y : State,
      u.run a = some y → k ≤ rungAt y σ) ∧
    rungAt mid σ = k ∧
    m = Move.foundToTab c b ∧ c.suit = σ ∧ c.rank.toIdx = k - 1 ∧
    rungAt post σ = k - 1

/-! ## §2. Per-leg classification: only a `σ`-pull leaves `≥ k` -/

/-- **THE CROSSING LETTER IS A `σ`-PULL OF THE RANK-`k-1` TOP** — a
witnessed reversible step whose `σ`-rung leaves the half-line `≥ k`
fires at rung exactly `k`, pulls the foundation top, and lands at
`k - 1`.  Mirror of `step_rise_classification`
(`Orig2/Fork/Split/FirstPassage.lean:430`); `WF` is needed only for the
foundation-top rank row (`foundTop_rank_succ`). -/
private theorem step_fall_classification {st s₁ : State} {m : Move} {σ : Suit}
    {k : Nat} (hwf : st.WF) (hstep : State.step st m = some s₁)
    (hlet : reversibleAtW st m) (hge : k ≤ rungAt st σ)
    (hlt : rungAt s₁ σ < k) :
    ∃ (c : Card) (b : Base), m = Move.foundToTab c b ∧ c.suit = σ ∧
      st.foundTop σ = some c ∧ c.rank.toIdx = k - 1 ∧
      rungAt st σ = k ∧ rungAt s₁ σ = k - 1 := by
  cases hm : m with
  | draw =>
      have hd := rungAt_draw (hm ▸ hstep) σ
      exfalso
      omega
  | wasteToFound c =>
      exact absurd (hm ▸ hlet) (wasteToFound_not_reversibleAtW st c)
  | wasteToTab c b =>
      exact absurd (hm ▸ hlet) (wasteToTab_not_reversibleAtW st c b)
  | tabToFound c =>
      have hr := rungAt_tabToFound (hm ▸ hstep) σ
      by_cases hσ : σ = c.suit
      · have h1 : rungAt s₁ σ = rungAt st σ + 1 := by
          rw [hr, ite_eq_left hσ]
        exfalso
        omega
      · have h1 : rungAt s₁ σ = rungAt st σ := by
          rw [hr, ite_eq_right hσ]
        exfalso
        omega
  | foundToTab c b =>
      have hr := rungAt_foundToTab (hm ▸ hstep) σ
      by_cases hσ : σ = c.suit
      · have h1 : rungAt s₁ σ = rungAt st σ - 1 := by
          rw [hr, ite_eq_left hσ]
        have hstk : rungAt st σ = k := by omega
        have hs₁ : rungAt s₁ σ = k - 1 := by omega
        have hchg : rungAt s₁ σ ≠ rungAt st σ := by
          rw [hstk, hs₁]
          omega
        obtain ⟨htop, hidx⟩ := step_pull_shape hwf (hm ▸ hstep) hchg
        exact ⟨c, b, rfl, hσ.symm, htop, by rw [hidx, hs₁], hstk, hs₁⟩
      · have h1 : rungAt s₁ σ = rungAt st σ := by
          rw [hr, ite_eq_right hσ]
        exfalso
        omega
  | tabToTab c b =>
      have h1 := rungAt_tabToTab (hm ▸ hstep) σ
      exfalso
      omega

/-! ## §3. Existence -/

/-- A first fall whose crossing letter is the head of the play. -/
private theorem firstFall_head {st s₁ W : State} {m : Move} {ρ : List Move}
    {σ : Suit} {k : Nat} (hwf : st.WF) (hstep : State.step st m = some s₁)
    (hlet : reversibleAtW st m) (hrest : ShufflePlayW s₁ ρ W)
    (hge : k ≤ rungAt st σ) (hlt : rungAt s₁ σ < k) :
    FirstFall st W (m :: ρ) σ k := by
  obtain ⟨c, b, hm, hcs, htop, hcr, hstk, hs₁⟩ :=
    step_fall_classification hwf hstep hlet hge hlt
  refine ⟨[], m, ρ, st, s₁, c, b, by simp, Walk.nil st, hstep, hrest, hlet, ?_,
    hstk, hm, hcs, hcr, hs₁⟩
  intro a b₂ hab y hrun
  cases a with
  | nil =>
      have hy : st = y := Option.some.inj hrun
      subst hy
      exact hge
  | cons m' a' => exact absurd hab (by simp)

/-- Carrying a first fall through a still-`≥ k` head letter. -/
private theorem firstFall_carry {st s₁ W : State} {m : Move} {ρ : List Move}
    {σ : Suit} {k : Nat} (hstep : State.step st m = some s₁)
    (hlet : reversibleAtW st m) (hge : k ≤ rungAt st σ)
    (hinner : FirstFall s₁ W ρ σ k) :
    FirstFall st W (m :: ρ) σ k := by
  obtain ⟨pre, m', rest', mid, post, c, b, hplay, hpre', hstep', hrest',
    hlet', hprege', hmidr, hm', hcs, hcr, hpostr⟩ := hinner
  refine ⟨m :: pre, m', rest', mid, post, c, b, ?_, ?_, hstep', hrest',
    hlet', ?_, hmidr, hm', hcs, hcr, hpostr⟩
  · rw [hplay]
    rfl
  · exact Walk.cons hlet hstep hpre'
  · intro a b₂ hab y hrun
    cases a with
    | nil =>
        have hy : st = y := Option.some.inj hrun
        subst hy
        exact hge
    | cons m'' a' =>
        simp only [List.cons_append] at hab
        injection hab with hm htl
        subst hm
        obtain ⟨s, hsd, hrt⟩ := State.run_cons hrun
        have hs : s = s₁ := Option.some.inj (hsd.symm.trans hstep)
        rw [hs] at hrt
        exact hprege' a' b₂ htl y hrt

/-- **A FIRST FALL EXISTS** whenever the start reads `≥ k` and the end
reads `< k`.  (Per-leg arithmetic: only a `σ`-pull can carry the rung
below `k`, and it fires at rung exactly `k`.) -/
theorem firstFall_exists {u v : State} {ρ : List Move} {σ : Suit} {k : Nat}
    (hwf : u.WF) (h : ShufflePlayW u ρ v) (hge : k ≤ rungAt u σ)
    (hlt : rungAt v σ < k) : FirstFall u v ρ σ k := by
  revert hge hlt
  revert hwf
  induction h with
  | nil st =>
      intro hwf hge hlt
      exfalso
      omega
  | @cons st s₁ W m ρ hlet hstep hrest ih =>
      intro hwf hge hlt
      by_cases hge₁ : k ≤ rungAt s₁ σ
      · exact firstFall_carry hstep hlet hge (ih (step_wf hwf hstep) hge₁ hlt)
      · have hlt₁ : rungAt s₁ σ < k := by omega
        exact firstFall_head hwf hstep hlet hrest hge hlt₁

/-- The differing-rung read: a strict drop of `σ` gives the first fall
below the STARTING rung — the last pull before leaving `rungAt u σ`.
Mirror of `firstRise_of_rung_lt` (`Orig2/Fork/Split/FirstPassage.lean:554`). -/
theorem firstFall_of_rung_lt {u v : State} {ρ : List Move} {σ : Suit}
    (hwf : u.WF) (h : ShufflePlayW u ρ v) (hlt : rungAt v σ < rungAt u σ) :
    FirstFall u v ρ σ (rungAt u σ) :=
  firstFall_exists hwf h (Nat.le_refl _) hlt

/-! ## §4. The local shapes at the fall -/

/-- **THE STRONGEST DOWN-DUAL SHAPE** — existence plus every local row in
one: the play splits at a longest `≥ k` prefix; the changing letter is a
`σ`-pull whose card is the foundation top at the prior state, whose rank
index is exactly the landing rung `k - 1`, and which is vanilla-raisable
(hence S-live) at the landing.  Mirror of `FirstPassage.shape`
(`Orig2/Fork/Split/FirstPassage.lean:343`) with the raise arm replaced by the pull's
flat row (`canRaise_post_of_pull`). -/
theorem FirstFall.shape {u v : State} {ρ : List Move} {σ : Suit} {k : Nat}
    (hwf : u.WF) (ff : FirstFall u v ρ σ k) :
    ∃ (pre : List Move) (m : Move) (rest : List Move) (mid post : State)
      (c : Card) (b : Base),
      ρ = pre ++ m :: rest ∧
      ShufflePlayW u pre mid ∧ State.step mid m = some post ∧
      ShufflePlayW post rest v ∧
      (∀ (a b₂ : List Move), pre = a ++ b₂ → ∀ y : State,
        u.run a = some y → k ≤ rungAt y σ) ∧
      m = Move.foundToTab c b ∧ c.suit = σ ∧
      mid.foundTop σ = some c ∧ c.rank.toIdx = rungAt post σ ∧
      CanRaise post c ∧ CanRaiseS post c ∧
      rungAt mid σ = k ∧ rungAt post σ = k - 1 := by
  obtain ⟨pre, m, rest, mid, post, c, b, hplay, hpre, hstep, hrest, hlet,
    hprege, hmidr, hm, hcs, hcr, hpostr⟩ := ff
  have hmid : mid.WF := Walk_wf_end hpre hwf
  -- the pulled card tops the foundation at `mid`, so `k ≥ 1`
  obtain ⟨c', htop', hc'c, -, -⟩ := step_foundToTab_inv (hm ▸ hstep)
  rw [hc'c] at htop'
  have htopσ : mid.foundTop σ = some c := by simpa [hcs] using htop'
  have hidxmid : c.rank.toIdx + 1 = k := by
    have h := foundTop_rank_succ hmid htopσ
    rw [hmidr] at h
    exact h
  have hk1 : 1 ≤ k := by omega
  have hchg : rungAt post σ ≠ rungAt mid σ := by
    rw [hpostr, hmidr]
    omega
  obtain ⟨-, hidx⟩ := step_pull_shape hmid (hm ▸ hstep) hchg
  -- the landing is next-up for the pulled card, hence vanilla-raisable
  have hfh : post.foundHeight c.suit = c.rank.toIdx := by
    rw [hcs]
    show (post.found σ).length = c.rank.toIdx
    rw [hidx]
    rfl
  have hnext : post.nextUp c = true := by
    unfold State.nextUp
    rw [hfh]
    exact decide_eq_true rfl
  have hcr' : CanRaise post c := canRaise_post_of_pull hmid (hm ▸ hstep) hnext
  exact ⟨pre, m, rest, mid, post, c, b, hplay, hpre, hstep, hrest, hprege,
    hm, hcs, htopσ, hidx, hcr', CanRaiseS.now c hcr', hmidr, hpostr⟩

/-- **THE FALL'S CARD IS LIVE AT THE LANDING** — the dip's pulled-card
local row, extracted from `FirstFall.shape`: the pulled `σ`-card is the
prior foundation top, its rank index is the landing rung, and it carries
the vanilla license (hence the S-license) at the landing.  Mirror of
`FirstRise.card_live` (`Orig2/Fork/Split/FirstPassage.lean:561`). -/
theorem FirstFall.card_live {u v : State} {ρ : List Move} {σ : Suit} {k : Nat}
    (hwf : u.WF) (ff : FirstFall u v ρ σ k) :
    ∃ (mid post : State) (c : Card) (b : Base),
      State.step mid (Move.foundToTab c b) = some post ∧ c.suit = σ ∧
      mid.foundTop σ = some c ∧ c.rank.toIdx = rungAt post σ ∧
      CanRaise post c ∧ CanRaiseS post c ∧
      rungAt mid σ = k ∧ rungAt post σ = k - 1 := by
  obtain ⟨pre, m, rest, mid, post, c, b, -, -, hstep, -, -, hm, hcs, htop,
    hidx, hcr, hcrS, hmidr, hpostr⟩ := FirstFall.shape hwf ff
  exact ⟨mid, post, c, b, hm ▸ hstep, hcs, htop, hidx, hcr, hcrS, hmidr,
    hpostr⟩

/-- **THE FALL'S RUNG IS EXACTLY ONE BELOW** — the census-compatible
summary row: the crossing letter is a `σ`-pull at rung `k`, landing at
`k - 1`, and the pulled card is the top of rank index `k - 1`. -/
theorem FirstFall.rung_step {u v : State} {ρ : List Move} {σ : Suit} {k : Nat}
    (hwf : u.WF) (ff : FirstFall u v ρ σ k) :
    ∃ (mid post : State) (c : Card) (b : Base),
      State.step mid (Move.foundToTab c b) = some post ∧
      reversibleAtW mid (Move.foundToTab c b) ∧
      mid.foundTop σ = some c ∧ c.rank.toIdx = k - 1 ∧
      rungAt mid σ = k ∧ rungAt post σ = k - 1 := by
  obtain ⟨pre, m, rest, mid, post, c, b, hplay, hpre, hstep, hrest, hlet,
    hprege, hmidr, hm, hcs, hcr, hpostr⟩ := ff
  have hmid : mid.WF := Walk_wf_end hpre hwf
  obtain ⟨c', htop', hc'c, -, -⟩ := step_foundToTab_inv (hm ▸ hstep)
  rw [hc'c] at htop'
  have htopσ : mid.foundTop σ = some c := by simpa [hcs] using htop'
  have hidxmid : c.rank.toIdx + 1 = k := by
    have h := foundTop_rank_succ hmid htopσ
    rw [hmidr] at h
    exact h
  have hk1 : 1 ≤ k := by omega
  have hchg : rungAt post σ ≠ rungAt mid σ := by
    rw [hpostr, hmidr]
    omega
  obtain ⟨-, hidx⟩ := step_pull_shape hmid (hm ▸ hstep) hchg
  exact ⟨mid, post, c, b, hm ▸ hstep, hm ▸ hlet, htopσ, by omega,
    hmidr, hpostr⟩

/-! ## §5. The pairing: the full dip boundary -/

/-- **THE FULL DIP BOUNDARY, BOTH DIRECTIONS** — along a witness play with
differing `σ`-rungs, either the rung climbs (a `FirstRise` at the origin
rung) or it drops (a `FirstFall` below the origin rung).  This is the row
`Orig2/Fork/Split/FirstPassage.lean:29` names as missing: with `FirstRise` (up) and
`FirstFall` (down) both proved, the first-passage ledger is complete for
either sign of the rung difference. -/
theorem firstRise_or_firstFall_of_rung_ne {u v : State} {ρ : List Move} {σ : Suit}
    (hwf : u.WF) (h : ShufflePlayW u ρ v) (hne : rungAt u σ ≠ rungAt v σ) :
    (rungAt u σ < rungAt v σ ∧ FirstRise u v ρ σ (rungAt u σ)) ∨
      (rungAt v σ < rungAt u σ ∧ FirstFall u v ρ σ (rungAt u σ)) := by
  rcases Nat.lt_trichotomy (rungAt u σ) (rungAt v σ) with hlt | heq | hgt
  · exact Or.inl ⟨hlt, firstRise_of_rung_lt h hlt⟩
  · exact absurd heq hne
  · exact Or.inr ⟨hgt, firstFall_of_rung_lt hwf h hgt⟩


/-! ## §5. The battery -/

#print axioms foundTop_rank_succ
#print axioms Walk_wf_end
#print axioms firstPassage_exists
#print axioms step_rung_classification
#print axioms FirstPassage.classification
#print axioms FirstPassage.pre_rung
#print axioms canRaise_of_tabToFoundR
#print axioms step_raise_live
#print axioms step_raise_flat
#print axioms step_pull_shape
#print axioms FirstPassage.shape
#print axioms FirstPassage.shape_flat
#print axioms step_rise_classification
#print axioms firstRise_head
#print axioms firstRise_carry
#print axioms firstRise_exists
#print axioms firstRise_of_rung_lt
#print axioms FirstRise.card_live

end SatDifferCensus

#print axioms SatDifferCensus.canRaise_post_of_pull
#print axioms SatDifferCensus.step_fall_classification
#print axioms SatDifferCensus.firstFall_head
#print axioms SatDifferCensus.firstFall_carry
#print axioms SatDifferCensus.firstFall_exists
#print axioms SatDifferCensus.firstFall_of_rung_lt
#print axioms SatDifferCensus.FirstFall.shape
#print axioms SatDifferCensus.FirstFall.card_live
#print axioms SatDifferCensus.FirstFall.rung_step
#print axioms SatDifferCensus.firstRise_or_firstFall_of_rung_ne