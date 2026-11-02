import Orig2.Fork.Split.FirstPassage
import Orig2.Fork.Class.ForkMinCross
import Orig2.Fork.Split.ForkBridge

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Ledger_Core — the rung ledger and the first-passage exodus

READ-ONLY scratch card.  No source file is modified; nothing is committed.

This is steps 1 and 2 of the `MinKit.MinCrossesFork` route named in the
`SatDifferFork` docstring (`Orig2/Substrate/Vocab.lean:610-629`):

* **§1 the ledger.**  Along a witness play `ρ : u → v`, the per-suit
  play-taxonomy counters `pullsOf` / `raisesOf` (`Orig2/Substrate/Vocab.lean:65-89`)
  satisfy the exact balance

      rungAt v σ + pullsOf ρ σ = rungAt u σ + raisesOf ρ σ.

  Consequently a differing suit has a `σ`-letter, and the *sign* of the
  difference names which kind must occur: a drop forces a pull, a rise
  forces a raise.  (The brief's literal "the first `σ`-letter is a pull"
  is FALSE for a suit whose rung rises; the correct sharp statement is
  the sign-conditioned one, and §1 records both.)

* **§2 first passage.**  Importing the repository's `FirstFall` /
  `FirstRise` ledger (`Orig2/Fork/Split/FirstPassage.lean:414,617`), the first
  crossing of a suit is a pull (fall) or a raise (rise), and at a fall
  the pulled card is the **exodus card**: the foundation top, pinned to
  rank `rungAt u σ - 1`, vanilla-raisable at the landing.

* **§3 the exodus cut.**  Because `u` is saturated, the first non-free
  letter of every differing-rung play is a pull (`first_nonfree_pull`,
  `Orig2/Fork/Split/ForkSplit.lean:714`); §3 packages its data, proves no fork can
  sit on the free prefix, and proves that a raise still occurs after the
  pull (the endpoint `v` is saturated: `last_nonfree_raise`).

House compliance: `sorry`-free, choice-free, `native_decide`-free; the
axiom battery is at the tail.
-/

namespace LedgerKit

open ValleyElim

/-! ## §0. Foundation-top positivity -/

/-- A founded top forces a positive rung. -/
theorem rungAt_pos_of_foundTop {st : State} {σ : Suit} {c : Card}
    (h : st.foundTop σ = some c) : 0 < rungAt st σ := by
  unfold State.foundTop at h
  unfold rungAt
  cases hf : st.found σ with
  | nil => rw [hf] at h; simp [lastOf] at h
  | cons x xs => simp

/-! ## §1. The rung ledger -/

/-- `raisesOf ρ σ > 0` iff `ρ` contains a `tabToFound` raise of a
`σ`-card. -/
theorem raisesOf_pos_iff {ρ : List Move} {σ : Suit} :
    0 < raisesOf ρ σ ↔ ∃ c : Card, c.suit = σ ∧ Move.tabToFound c ∈ ρ := by
  induction ρ with
  | nil => simp [raisesOf]
  | cons m t ih =>
      cases m with
      | tabToFound c =>
          by_cases hc : c.suit = σ
          · simp only [raisesOf, ite_eq_left hc]
            constructor
            · intro _
              exact ⟨c, hc, List.mem_cons_self ..⟩
            · intro _
              omega
          · simp only [raisesOf, ite_eq_right hc, Nat.zero_add]
            constructor
            · intro h
              obtain ⟨d, hd, hmem⟩ := ih.mp h
              exact ⟨d, hd, List.mem_cons_of_mem _ hmem⟩
            · rintro ⟨d, hd, hmem⟩
              rcases List.mem_cons.mp hmem with heq | hmem'
              · have hdc : d = c := by cases heq; rfl
                exact absurd (hdc ▸ hd) hc
              · exact ih.mpr ⟨d, hd, hmem'⟩
      | draw => simpa [raisesOf] using ih
      | wasteToFound c => simpa [raisesOf] using ih
      | wasteToTab c b => simpa [raisesOf] using ih
      | foundToTab c b => simpa [raisesOf] using ih
      | tabToTab c b => simpa [raisesOf] using ih

/-- `pullsOf ρ σ > 0` iff `ρ` contains a `foundToTab` pull of a
`σ`-card. -/
theorem pullsOf_pos_iff {ρ : List Move} {σ : Suit} :
    0 < pullsOf ρ σ ↔ ∃ (c : Card) (b : Base), c.suit = σ ∧
      Move.foundToTab c b ∈ ρ := by
  induction ρ with
  | nil => simp [pullsOf]
  | cons m t ih =>
      cases m with
      | foundToTab c b =>
          by_cases hc : c.suit = σ
          · simp only [pullsOf, ite_eq_left hc]
            constructor
            · intro _
              exact ⟨c, b, hc, List.mem_cons_self ..⟩
            · intro _
              omega
          · simp only [pullsOf, ite_eq_right hc, Nat.zero_add]
            constructor
            · intro h
              obtain ⟨d, bd, hd, hmem⟩ := ih.mp h
              exact ⟨d, bd, hd, List.mem_cons_of_mem _ hmem⟩
            · rintro ⟨d, bd, hd, hmem⟩
              rcases List.mem_cons.mp hmem with heq | hmem'
              · have hdc : d = c := by cases heq; rfl
                exact absurd (hdc ▸ hd) hc
              · exact ih.mpr ⟨d, bd, hd, hmem'⟩
      | draw => simpa [pullsOf] using ih
      | wasteToFound c => simpa [pullsOf] using ih
      | wasteToTab c b => simpa [pullsOf] using ih
      | tabToFound c => simpa [pullsOf] using ih
      | tabToTab c b => simpa [pullsOf] using ih

/-- **THE RUNG LEDGER.**  Along a witness play the per-suit balance is
exact: the rung at the end plus the `σ`-pulls equals the rung at the
start plus the `σ`-raises.  Only `tabToFound` writes `+1` and only
`foundToTab` writes `-1` (`Orig2/Substrate/Position.lean:166,183`); every other
witness letter preserves the rung. -/
theorem rungAt_ledger {u v : State} {ρ : List Move} {σ : Suit}
    (h : ShufflePlayW u ρ v) :
    rungAt v σ + pullsOf ρ σ = rungAt u σ + raisesOf ρ σ := by
  induction h with
  | nil st => simp [pullsOf, raisesOf]
  | @cons st s₁ W m ρ hrev hstep hrest ih =>
      cases m with
      | draw =>
          simpa [pullsOf, raisesOf, rungAt_draw hstep σ] using ih
      | wasteToFound c =>
          exact absurd hrev (wasteToFound_not_reversibleAtW st c)
      | wasteToTab c b =>
          exact absurd hrev (wasteToTab_not_reversibleAtW st c b)
      | tabToFound c =>
          by_cases hc : c.suit = σ
          · have hcs : σ = c.suit := hc.symm
            simp only [raisesOf, pullsOf, ite_eq_left hc]
            have hr : rungAt s₁ σ = rungAt st σ + 1 := by
              rw [rungAt_tabToFound hstep σ, ite_eq_left hcs]
            omega
          · have hcs : ¬ σ = c.suit := fun h => hc h.symm
            simp only [raisesOf, pullsOf, ite_eq_right hc]
            have hr : rungAt s₁ σ = rungAt st σ := by
              rw [rungAt_tabToFound hstep σ, ite_eq_right hcs]
            omega
      | foundToTab c b =>
          by_cases hc : c.suit = σ
          · obtain ⟨c', htop, hc', -, -⟩ := step_foundToTab_inv hstep
            rw [hc'] at htop
            have hpos : 0 < rungAt st σ := by
              rw [← hc]; exact rungAt_pos_of_foundTop htop
            have hcs : σ = c.suit := hc.symm
            simp only [pullsOf, raisesOf, ite_eq_left hc]
            have hr : rungAt s₁ σ = rungAt st σ - 1 := by
              rw [rungAt_foundToTab hstep σ, ite_eq_left hcs]
            omega
          · have hcs : ¬ σ = c.suit := fun h => hc h.symm
            simp only [pullsOf, raisesOf, ite_eq_right hc]
            have hr : rungAt s₁ σ = rungAt st σ := by
              rw [rungAt_foundToTab hstep σ, ite_eq_right hcs]
            omega
      | tabToTab c b =>
          simpa [pullsOf, raisesOf, rungAt_tabToTab hstep σ] using ih

/-- **A DIFFERING SUIT HAS A `σ`-LETTER.**  The ledger balance plus the
sign of the difference: a drop forces a `σ`-pull, a rise forces a
`σ`-raise. -/
theorem sigma_letter_of_rung_ne {u v : State} {ρ : List Move} {σ : Suit}
    (hplay : ShufflePlayW u ρ v) (hne : rungAt u σ ≠ rungAt v σ) :
    (∃ (c : Card) (b : Base), c.suit = σ ∧ Move.foundToTab c b ∈ ρ) ∨
      (∃ c : Card, c.suit = σ ∧ Move.tabToFound c ∈ ρ) := by
  have hled : rungAt v σ + pullsOf ρ σ = rungAt u σ + raisesOf ρ σ :=
    @rungAt_ledger u v ρ σ hplay
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · -- the rung rises: a `σ`-raise must occur
    right
    apply raisesOf_pos_iff.mp
    omega
  · -- the rung drops: a `σ`-pull must occur
    left
    apply pullsOf_pos_iff.mp
    omega

/-- The drop form: a strict drop forces a `σ`-pull. -/
theorem pull_of_rung_lt {u v : State} {ρ : List Move} {σ : Suit}
    (hplay : ShufflePlayW u ρ v) (hlt : rungAt v σ < rungAt u σ) :
    ∃ (c : Card) (b : Base), c.suit = σ ∧ Move.foundToTab c b ∈ ρ := by
  have hled : rungAt v σ + pullsOf ρ σ = rungAt u σ + raisesOf ρ σ :=
    @rungAt_ledger u v ρ σ hplay
  exact pullsOf_pos_iff.mp (by omega)

/-- The rise form: a strict rise forces a `σ`-raise. -/
theorem raise_of_rung_gt {u v : State} {ρ : List Move} {σ : Suit}
    (hplay : ShufflePlayW u ρ v) (hlt : rungAt u σ < rungAt v σ) :
    ∃ c : Card, c.suit = σ ∧ Move.tabToFound c ∈ ρ := by
  have hled : rungAt v σ + pullsOf ρ σ = rungAt u σ + raisesOf ρ σ :=
    @rungAt_ledger u v ρ σ hplay
  exact raisesOf_pos_iff.mp (by omega)

/-- Either some suit drops from `u` to `v` or some suit rises. -/
theorem drop_or_rise_of_diff {u v : State}
    (hdiff : ∃ σ : Suit, rungAt u σ ≠ rungAt v σ) :
    (∃ σ : Suit, rungAt v σ < rungAt u σ) ∨
      (∃ σ : Suit, rungAt u σ < rungAt v σ) := by
  obtain ⟨σ, hσ⟩ := hdiff
  rcases Nat.lt_or_gt_of_ne hσ with hlt | hgt
  · exact Or.inr ⟨σ, hlt⟩
  · exact Or.inl ⟨σ, hgt⟩

/-! ## §2. First passage: the repository rows -/

/-- **THE FIRST FALL IS A `σ`-PULL, AND ITS CARD IS THE EXODUS CARD.**
Wrapper of `SatDifferCensus.FirstFall.shape` (`Orig2/Fork/Split/FirstPassage.lean:772`)
at `k = rungAt u σ`: the first time the `σ`-rung leaves `≥ rungAt u σ`
it pulls the foundation top `c`, whose rank index is `rungAt u σ - 1`,
and `c` is vanilla- and S-raisable at the landing. -/
theorem exodus_of_rung_lt {u v : State} {ρ : List Move} {σ : Suit}
    (huwf : u.WF) (hplay : ShufflePlayW u ρ v)
    (hlt : rungAt v σ < rungAt u σ) :
    ∃ (pre : List Move) (m : Move) (rest : List Move) (mid post : State)
      (c : Card) (b : Base),
      ρ = pre ++ m :: rest ∧
      ShufflePlayW u pre mid ∧ State.step mid m = some post ∧
      ShufflePlayW post rest v ∧
      (∀ (a b₂ : List Move), pre = a ++ b₂ → ∀ y : State,
        u.run a = some y → rungAt u σ ≤ rungAt y σ) ∧
      m = Move.foundToTab c b ∧ c.suit = σ ∧
      mid.foundTop σ = some c ∧ c.rank.toIdx = rungAt post σ ∧
      CanRaise post c ∧ CanRaiseS post c ∧
      rungAt mid σ = rungAt u σ ∧ rungAt post σ = rungAt u σ - 1 :=
  SatDifferCensus.FirstFall.shape huwf
    (SatDifferCensus.firstFall_of_rung_lt huwf hplay hlt)

/-- **THE FIRST RISE IS A `σ`-RAISE AT THE RUNG EXACTLY.**  Wrapper of
`SatDifferCensus.firstRise_of_rung_lt` / `FirstRise.card_live`
(`Orig2/Fork/Split/FirstPassage.lean:554,561`): the first state whose `σ`-rung
exceeds `rungAt u σ` is a `σ`-raise from rung exactly `rungAt u σ`, and
the raised card is S-live at the moved origin. -/
theorem twin_raise_of_rung_gt {u v : State} {ρ : List Move} {σ : Suit}
    (huwf : u.WF) (hplay : ShufflePlayW u ρ v)
    (hlt : rungAt u σ < rungAt v σ) :
    ∃ (pre : List Move) (m : Move) (rest : List Move) (mid post : State)
      (c : Card),
      ρ = pre ++ m :: rest ∧
      ShufflePlayW u pre mid ∧ State.step mid m = some post ∧
      ShufflePlayW post rest v ∧
      (∀ (a b₂ : List Move), pre = a ++ b₂ → ∀ y : State,
        u.run a = some y → rungAt y σ ≤ rungAt u σ) ∧
      m = Move.tabToFound c ∧ c.suit = σ ∧ c.rank.toIdx = rungAt u σ ∧
      CanRaiseS mid c ∧ rungAt mid σ = rungAt u σ ∧
      rungAt post σ = rungAt u σ + 1 := by
  obtain ⟨pre, m, rest, mid, post, c, hρ, hpre, hstep, hrest, hrev, hle,
    hrungMid, hm, hcs, hcr, hpost⟩ :=
    SatDifferCensus.firstRise_of_rung_lt hplay hlt
  have hmidwf : mid.WF := SatDifferCensus.Walk_wf_end hpre huwf
  have hS : CanRaiseS mid c :=
    SatDifferCensus.step_raise_live hmidwf (hm ▸ hstep) (hm ▸ hrev)
  exact ⟨pre, m, rest, mid, post, c, hρ, hpre, hstep, hrest, hle, hm, hcs,
    hcr, hS, hrungMid, hpost⟩

/-! ## §3. The exodus cut: the first non-free letter is a pull -/

/-- **A NON-FREE LETTER EXISTS** whenever a rung differs: a free play
preserves every rung (`rungAt_eq_of_free_play`). -/
theorem exists_nonfree_of_rung_ne {u v : State} {ρ : List Move}
    (hplay : ShufflePlayW u ρ v)
    (hdiff : ∃ σ : Suit, rungAt u σ ≠ rungAt v σ) :
    ∃ m ∈ ρ, ¬ FreeMove m := by
  apply exists_nonfree_of_not_all_free
  intro hall
  obtain ⟨σ, hσ⟩ := hdiff
  exact hσ (rungAt_eq_of_free_play hplay hall σ).symm

/-- **THE EXODUS CUT.**  From a saturated `WF` origin, every witness play
with a differing rung splits at its first non-free letter, which is a
pull `foundToTab c b`; the free prefix `pre` reaches `mid`, the pull
lands at `post`, and the exodus card `c` is the `mid` foundation top,
live (vanilla and S) at `post`, with the rung one below `mid`'s.

This is the step-1 + step-2 package consumed by the residual card. -/
theorem exodus_cut {u v : State} {ρ : List Move}
    (huwf : u.WF) (hu : SSaturated u) (hplay : ShufflePlayW u ρ v)
    (hdiff : ∃ σ : Suit, rungAt u σ ≠ rungAt v σ) :
    ∃ (pre : List Move) (m : Move) (rest : List Move) (mid post : State)
      (c : Card) (b : Base),
      ρ = pre ++ m :: rest ∧
      (∀ x ∈ pre, FreeMove x) ∧
      ShufflePlayW u pre mid ∧
      State.step mid m = some post ∧
      ShufflePlayW post rest v ∧
      m = Move.foundToTab c b ∧
      mid.foundTop c.suit = some c ∧
      c.rank.toIdx = rungAt post c.suit ∧
      CanRaise post c ∧ CanRaiseS post c ∧
      rungAt post c.suit = rungAt mid c.suit - 1 := by
  obtain ⟨m₀, hm₀, hnf₀⟩ := exists_nonfree_of_rung_ne hplay hdiff
  obtain ⟨pre, c, b, rest, heq, hpre⟩ :=
    first_nonfree_pull huwf hu hplay ⟨m₀, hm₀, hnf₀⟩
  obtain ⟨mid, hpreplay, hrest⟩ :=
    ShufflePlayW_split hplay pre (Move.foundToTab c b :: rest) heq
  have hmidwf : mid.WF := SatDifferCensus.ShufflePlayW.wf_end hpreplay huwf
  cases hrest with
  | @cons _ post _ _ _ hrev hstep htail =>
      obtain ⟨c', htop', hc', -, -⟩ := step_foundToTab_inv hstep
      rw [hc'] at htop'
      have htop : mid.foundTop c.suit = some c := htop'
      have hidxTop : c.rank.toIdx + 1 = rungAt mid c.suit :=
        SatDifferCensus.foundTop_rank_succ hmidwf htop
      have hrung : rungAt post c.suit = rungAt mid c.suit - 1 := by
        have hr := rungAt_foundToTab hstep c.suit
        rw [ite_eq_left rfl] at hr
        exact hr
      have hpos : 0 < rungAt mid c.suit := rungAt_pos_of_foundTop htop
      have hidx : c.rank.toIdx = rungAt post c.suit := by
        rw [hrung]; omega
      have hfh : post.foundHeight c.suit = c.rank.toIdx := by
        show (post.found c.suit).length = c.rank.toIdx
        rw [show (post.found c.suit).length = rungAt post c.suit from rfl, hidx]
      have hnext : post.nextUp c = true := by
        unfold State.nextUp
        rw [hfh]
        exact decide_eq_true rfl
      have hcan : CanRaise post c :=
        SatDifferCensus.canRaise_post_of_pull hmidwf hstep hnext
      exact ⟨pre, Move.foundToTab c b, rest, mid, post, c, b, heq, hpre,
        hpreplay, hstep, htail, rfl, htop, hidx, hcan, CanRaiseS.now c hcan,
        hrung⟩

/-! ## §3b. The exodus card is the deep endpoint's foundation top -/

/-- **THE EXODUS CARD IS FOUNDED AT THE DEEP ENDPOINT.**  When the `σ`-rung
drops, the first-fall card `c` is not only the `mid` foundation top: `mid`
and the origin `u` have the same `σ`-rung, so their foundations agree
(`found_congr_of_rungs`) and `c` was already `u`'s foundation top — the
"differing card, founded at the deep endpoint" of the docstring route. -/
theorem exodus_card_deep_top {u v : State} {ρ : List Move} {σ : Suit}
    (huwf : u.WF) (hplay : ShufflePlayW u ρ v)
    (hlt : rungAt v σ < rungAt u σ) :
    ∃ (c : Card) (b : Base) (mid post : State),
      u.foundTop σ = some c ∧ mid.foundTop σ = some c ∧
      c.rank.toIdx = rungAt post σ ∧
      CanRaise post c ∧ CanRaiseS post c ∧
      rungAt mid σ = rungAt u σ ∧ rungAt post σ = rungAt u σ - 1 := by
  obtain ⟨pre, m, rest, mid, post, c, b, hρ, hpre, hstep, hrest, hle, hm,
    hcs, htop, hidx, hcan, hS, hrungMid, hrungPost⟩ :=
    exodus_of_rung_lt huwf hplay hlt
  have hmidwf : mid.WF := SatDifferCensus.Walk_wf_end hpre huwf
  have hfound : u.found σ = mid.found σ :=
    found_congr_of_rungs huwf hmidwf hrungMid.symm
  have htopU : u.foundTop σ = some c := by
    unfold State.foundTop
    rw [hfound]
    exact htop
  exact ⟨c, b, mid, post, htopU, htop, hidx, hcan, hS, hrungMid, hrungPost⟩

/-! ## §3c. Nothing forks on the free prefix -/

/-- A fork state is not saturated: the witness card is S-live. -/
theorem not_ssaturated_of_fork {F : State} {x : Card}
    (hx : ForkWitness F x) : ¬ SSaturated F :=
  fun hs => hs x ((hx.1 x).mp (Or.inl rfl))

/-- **NO FORK ON A FREE PREFIX FROM A SATURATED ORIGIN.**  Free letters
preserve saturation (`ssaturated_free_prefix`), and a fork state is not
saturated. -/
theorem not_fork_of_free_play {u F : State} {pre : List Move}
    (huwf : u.WF) (hu : SSaturated u)
    (hplay : ShufflePlayW u pre F) (hfree : ∀ m ∈ pre, FreeMove m)
    {x : Card} : ¬ ForkWitness F x := by
  intro hx
  exact not_ssaturated_of_fork hx (ssaturated_free_prefix hplay hfree huwf hu)

/-! ## §3d. A raise still occurs after the exodus pull -/

/-- **THE MATCHING RAISE OCCURS AFTER THE PULL.**  The first non-free
letter is the exodus pull; the last non-free letter of the play is a
raise (`last_nonfree_raise`, using `SSaturated v`).  Since a pull is not
a raise, that raise lies strictly after the pull — i.e. in `rest`. -/
theorem raise_in_rest_of_exodus {u v : State} {ρ pre rest : List Move}
    {m : Move} {mid post : State} {c : Card} {b : Base}
    (huwf : u.WF) (hv : SSaturated v)
    (hplay : ShufflePlayW u ρ v)
    (heq : ρ = pre ++ m :: rest) (hpre : ∀ x ∈ pre, FreeMove x)
    (hm : m = Move.foundToTab c b) :
    ∃ (d : Card) (γ β : List Move),
      rest = γ ++ Move.tabToFound d :: β := by
  have hex : ∃ m' ∈ ρ, ¬ FreeMove m' :=
    ⟨m, by rw [heq]; exact List.mem_append_right _ (List.mem_cons_self ..),
      by rw [hm]; intro hf; rcases hf with h | ⟨c', b', h⟩ <;> cases h⟩
  obtain ⟨α, d, β, hρ, hβfree⟩ := last_nonfree_raise huwf hv hplay hex
  have hmem : Move.tabToFound d ∈ ρ := by
    rw [hρ]; exact List.mem_append_right _ (List.mem_cons_self ..)
  rw [heq] at hmem
  rcases List.mem_append.mp hmem with hmemPre | hmemRest
  · have hfree := hpre _ hmemPre
    rcases hfree with h | ⟨c', b', h⟩ <;> cases h
  · rcases List.mem_cons.mp hmemRest with hEq | hmemTail
    · rw [hm] at hEq
      cases hEq
    · obtain ⟨γ, d', β', hdecomp, -⟩ :=
        exists_first_raise rest ⟨d, hmemTail⟩
      exact ⟨d', γ, β', hdecomp⟩

/-- **THE TAIL OF THE EXODUS IS NOT FREE.**  The exodus card `c` is
S-live at the landing `post`; were `rest` free, `CanRaiseS` would be
transported to `v` (`Bridge.canRaiseS_of_free_play_iff`), contradicting
`SSaturated v`.  So some non-free letter occurs after the exodus pull. -/
theorem rest_has_nonfree_of_exodus {post v : State} {rest : List Move} {c : Card}
    (hpost : post.WF) (hplay : ShufflePlayW post rest v)
    (hlive : CanRaiseS post c) (hsat : SSaturated v) :
    ∃ m ∈ rest, ¬ FreeMove m := by
  apply exists_nonfree_of_not_all_free
  intro hall
  have h := (Bridge.canRaiseS_of_free_play_iff hplay hall hpost c).mp hlive
  exact hsat c h

/-! ## §4. Axiom battery -/

#print axioms LedgerKit.rungAt_pos_of_foundTop
#print axioms LedgerKit.raisesOf_pos_iff
#print axioms LedgerKit.pullsOf_pos_iff
#print axioms LedgerKit.rungAt_ledger
#print axioms LedgerKit.sigma_letter_of_rung_ne
#print axioms LedgerKit.pull_of_rung_lt
#print axioms LedgerKit.raise_of_rung_gt
#print axioms LedgerKit.drop_or_rise_of_diff
#print axioms LedgerKit.exodus_of_rung_lt
#print axioms LedgerKit.twin_raise_of_rung_gt
#print axioms LedgerKit.exists_nonfree_of_rung_ne
#print axioms LedgerKit.exodus_cut
#print axioms LedgerKit.exodus_card_deep_top
#print axioms LedgerKit.not_ssaturated_of_fork
#print axioms LedgerKit.not_fork_of_free_play
#print axioms LedgerKit.raise_in_rest_of_exodus
#print axioms LedgerKit.rest_has_nonfree_of_exodus

end LedgerKit
