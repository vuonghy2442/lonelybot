import Orig2.Fork.ForkPosition

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Orig2.ForkThird — the third-suit residue of fork Position rigidity

THE `ForkThirdRigid` REDUCTION.  `ForkPosition` reduced Position
rigidity to the two non-pair suits (`ForkThirdRigid`).  This card splits
that residue in two:

* `seated_twin_rung_eq` / `fork_cover_suit_rigid` — ANY card seated on a
  twin of a fork has a class-invariant suit rung; in particular the
  COVER suit is rigid, with no same-orientation hypothesis (it strictly
  generalises `coverSuit_rung_eq_of_sameOrientation`).
* `lock_of_third_low` — a third suit whose rung is `≤ r - 1` at one fork
  is rigid: the frontier card `(rung, σ)` has no parent
  (`third_low_first` / `third_top_parent_is_pair`), so `LockInv` /
  `lockInv_play` freezes it out of every descendant foundation.
* `forkThirdRigid_of_high` — the assembly: `ForkThirdRigid` follows from
  the residual row `ForkThirdRigidHigh` (both endpoints at third rung
  `≥ r`).

NOT proved here: `ForkThirdRigidHigh`, the rank-equal / super-rank
third-suit leak.  The naive bound `rung ≤ r` is FALSE — a WF fork can
have a non-cover third rung at `r + 1` (`Temp/ThirdRigid_bound2.py`).
The suggested next route is "a pulled/relocated third-suit card cannot
be non-`S`-live at the far fork", via `found_exodus`.

House compliance: additive leaf (`Orig2.ForkPosition`, which carries the
target and the unconditional class theorem); zero `sorry`, zero
`Classical.choice`; battery at tail.
-/
namespace ThirdRigid

/-! ## §1. Suit/colour algebra -/

theorem third_color_ne {x σ : Suit} (h1 : σ ≠ x) (h2 : σ ≠ x.twin) :
    σ.color ≠ x.color := by
  intro h
  rcases SeedKit.suit_family h with h' | h'
  · exact h1 h'
  · exact h2 h'

/-! ## §2. Splitting a run at the card below a member -/

theorem below_split {l : List Card} {c : Card} (hmem : c ∈ l)
    (h : below c l ≠ []) :
    ∃ (P : List Card) (d : Card) (S : List Card),
      below c l = P ++ [d] ∧ l = P ++ d :: c :: S := by
  obtain ⟨r, hfc⟩ := tfc_fromCard_cons_head l hmem
  obtain ⟨d, hd⟩ := lastOf_exists h
  obtain ⟨P, hP⟩ := lastOf_eq_snoc hd
  refine ⟨P, d, r, hP, ?_⟩
  have h0 : below c l ++ fromCard c l = l := tfc_below_fromCard c l
  rw [hP, hfc] at h0
  rw [← h0]
  simp [List.append_assoc]

theorem pred_fit {l : List Card} {c : Card} (hrok : runOK l = true)
    (hmem : c ∈ l) (h : below c l ≠ []) :
    ∃ (P : List Card) (d : Card) (S : List Card),
      l = P ++ d :: c :: S ∧ canSitOn c d = true := by
  obtain ⟨P, d, S, hb, hl⟩ := below_split hmem h
  refine ⟨P, d, S, hl, ?_⟩
  rw [hl] at hrok
  exact SeedKit.runOK_adjacent_fit d c P S hrok

/-- A nodup run whose top is its own head is a singleton. -/
theorem tail_eq_nil_of_lastOf_head {c : Card} {t : List Card}
    (hnd : (c :: t).Nodup) (h : lastOf (c :: t) = some c) : t = [] := by
  cases t with
  | nil => rfl
  | cons u us =>
      exfalso
      have h2 : lastOf (u :: us) = some c := by
        change lastOf (c :: u :: us) = some c at h
        exact h
      have hmem : c ∈ u :: us := lastOf_mem h2
      exact (List.nodup_cons.mp hnd).1 hmem

/-! ## §3. `NoParent` and the low third-suit card -/

/-- **NoParent st c** — no card sits directly below `c`. -/
def NoParent (st : State) (c : Card) : Prop :=
  ∀ z : Card, seatOf st c ≠ some (Sum.inr z)

theorem noParent_of_head {st : State} (hwf : st.WF) {c : Card} {a : Anchor}
    {t : List Card} (h : (st.piles a).faceUp = c :: t) : NoParent st c := by
  intro z hz
  have hmem : c ∈ (st.piles a).faceUp := by rw [h]; exact List.mem_cons_self ..
  have hhold : st.pileHolding c = some a := (pileHolding_eq_some_iff hwf).2 hmem
  have hb : below c (st.piles a).faceUp = [] := by rw [h]; exact below_cons_self c t
  have hseat : seatOf st c = some (Sum.inl a) := tfc_seatOf_inl_intro hhold hb
  rw [hseat] at hz
  exact absurd hz (by simp)

theorem seatOf_inr_of_below_ne_nil {st : State} (hwf : st.WF) {c : Card} {a : Anchor}
    (hmem : c ∈ (st.piles a).faceUp) (h : below c (st.piles a).faceUp ≠ []) :
    ∃ z, seatOf st c = some (Sum.inr z) := by
  obtain ⟨z, hz⟩ := lastOf_exists h
  exact ⟨z, tfc_seatOf_inr_intro ((pileHolding_eq_some_iff hwf).2 hmem) hz⟩

theorem below_nil_of_noParent {st : State} (hwf : st.WF) {c : Card}
    (hno : NoParent st c) {a : Anchor} (hmem : c ∈ (st.piles a).faceUp) :
    below c (st.piles a).faceUp = [] := by
  by_cases hb : below c (st.piles a).faceUp = []
  · exact hb
  · obtain ⟨z, hz⟩ := seatOf_inr_of_below_ne_nil hwf hmem hb
    exact absurd hz (hno z)

/-- **LOW THIRD CARD HAS NO PARENT.** -/
theorem third_low_first {F : State} (hwf : F.WF) {w : Card} (hw : ForkWitness F w)
    {σ : Suit} (hσ : σ.color ≠ w.suit.color)
    {k : Nat} (hk : k + 2 ≤ w.rank.toIdx) {a : Anchor}
    (hmem : (⟨σ, FoundKit.Rk k⟩ : Card) ∈ (F.piles a).faceUp) :
    below (⟨σ, FoundKit.Rk k⟩ : Card) (F.piles a).faceUp = [] := by
  have hr13 : w.rank.toIdx < 13 := Rank.toIdx_lt w.rank
  have hidx : (⟨σ, FoundKit.Rk k⟩ : Card).rank.toIdx = k :=
    FoundKit.Rk_toIdx k (by omega)
  by_cases hb : below (⟨σ, FoundKit.Rk k⟩ : Card) (F.piles a).faceUp = []
  · exact hb
  · exfalso
    obtain ⟨P, d, S, hl, hfit⟩ := pred_fit (hwf.2.1 a) hmem hb
    obtain ⟨hr, hcol⟩ := (canSitOn_eq _ _).mp hfit
    have hdr : d.rank.toIdx = k + 1 := by rw [hidx] at hr; omega
    have hcolx : d.suit.color = w.suit.color := SeedKit.color_pair hcol hσ
    have hdfound : d ∈ F.found d.suit :=
      pair_lowFamily_founded hwf hw hcolx (by omega)
    have hdmem : d ∈ (F.piles a).faceUp := by
      rw [hl]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    exact (mem_faceUp_only hwf hdmem).2.2.2.2 d.suit hdfound

/-- **THE RANK-(r-1) THIRD CARD'S PARENT IS A PAIR CARD** (when it has one). -/
theorem third_top_parent_is_pair {F : State} (hwf : F.WF) {w : Card} {σ : Suit}
    (hσ : σ.color ≠ w.suit.color) (hr : 1 ≤ w.rank.toIdx) {c z : Card}
    (hc : c = (⟨σ, FoundKit.Rk (w.rank.toIdx - 1)⟩ : Card))
    (hz : seatOf F c = some (Sum.inr z)) : z = w ∨ z = w.twin := by
  subst hc
  have hr13 : w.rank.toIdx < 13 := Rank.toIdx_lt w.rank
  have hidx : (⟨σ, FoundKit.Rk (w.rank.toIdx - 1)⟩ : Card).rank.toIdx
      = w.rank.toIdx - 1 := FoundKit.Rk_toIdx _ (by omega)
  obtain ⟨a, hhold, hbne, hlast⟩ := tfc_seatOf_of_inr hz
  have hmem := pileHolding_mem hhold
  obtain ⟨r, hfc⟩ := tfc_fromCard_cons_head _ hmem
  obtain ⟨P, hP⟩ := lastOf_eq_snoc hlast
  have hl : (F.piles a).faceUp
      = P ++ z :: (⟨σ, FoundKit.Rk (w.rank.toIdx - 1)⟩ : Card) :: r := by
    have h0 := tfc_below_fromCard (⟨σ, FoundKit.Rk (w.rank.toIdx - 1)⟩ : Card)
      (F.piles a).faceUp
    rw [hP, hfc] at h0
    rw [← h0]
    simp [List.append_assoc]
  have hfit : canSitOn (⟨σ, FoundKit.Rk (w.rank.toIdx - 1)⟩ : Card) z = true := by
    have hrok := hwf.2.1 a
    rw [hl] at hrok
    exact SeedKit.runOK_adjacent_fit z _ P r hrok
  obtain ⟨hrk, hcol⟩ := (canSitOn_eq _ _).mp hfit
  have hdr : z.rank.toIdx = w.rank.toIdx := by rw [hidx] at hrk; omega
  have hcolx : z.suit.color = w.suit.color := SeedKit.color_pair hcol hσ
  exact SeedKit.rankColor_pair hdr hcolx

/-! ## §4. Fork bookkeeping -/

theorem twinLivePair_twin {st : State} {x : Card} (h : TwinLivePair st x) :
    TwinLivePair st x.twin := by
  intro c
  have hc := h c
  rw [tfc_card_twin_twin]
  exact ⟨fun hh => Or.symm (hc.mp hh), fun hh => hc.mpr (Or.symm hh)⟩

theorem twinLivePair_of_forkWitness {st : State} {x y : Card}
    (hy : ForkWitness st y) (h : y = x ∨ y = x.twin) : TwinLivePair st x := by
  intro c
  rcases h with h | h
  · subst h; exact (hy.1 c).symm
  · subst h
    have hc := hy.1 c
    rw [tfc_card_twin_twin] at hc
    exact ⟨fun hh => Or.symm (hc.mpr hh), fun hh => hc.mp (Or.symm hh)⟩

theorem fork_pair_rungs {G : State} {x y : Card} (hy : ForkWitness G y)
    (hxy : y = x ∨ y = x.twin) :
    rungAt G x.suit = x.rank.toIdx ∧ rungAt G x.twin.suit = x.rank.toIdx := by
  obtain ⟨h1, h2⟩ := forkState_witness_rungs hy
  rcases hxy with h | h
  · subst h; exact ⟨h1, h2⟩
  · subst h
    refine ⟨?_, ?_⟩
    · rw [tfc_card_twin_twin, Card.twin_rank] at h2
      exact h2
    · rw [Card.twin_rank] at h1
      exact h1

/-- A fork always has pair rank at least 2 (the cover pin `rung + 2 ≤ r`). -/
theorem fork_rank_ge_two {st : State} (hwf : st.WF) {x : Card} (hx : ForkWitness st x) :
    2 ≤ x.rank.toIdx := by
  have hyS : CanRaiseS st x.twin := (hx.1 x.twin).mp (Or.inr rfl)
  have hcov : CoveredAt st x.twin :=
    covered_of_live_not_canRaise hwf hyS hx.2
  obtain ⟨d, hd⟩ := hcov
  obtain ⟨-, -, -, -, -, hdef⟩ := cover_pins_of_fork hwf hx rfl hd
  omega

/-! ## §5. The cover token: any card seated on a twin stays on a twin -/

theorem seated_twin_stays {F Z : State} {x c : Card} {play : List Move}
    (hF : F.WF) (hlive : TwinLivePair F x) (hplay : ShufflePlayW F play Z)
    (hc : seatOf F c = some (Sum.inr x) ∨ seatOf F c = some (Sum.inr x.twin)) :
    seatOf Z c = some (Sum.inr x) ∨ seatOf Z c = some (Sum.inr x.twin) := by
  rcases hc with hc | hc
  · have h2 := cover_token_invariant hF (x := x.twin) (y := x) (d := c)
      (by rw [tfc_card_twin_twin]) (twinLivePair_twin hlive) hc hplay
    exact Or.symm h2
  · exact cover_token_invariant hF (x := x) (y := x.twin) (d := c) rfl hlive hc hplay

/-- **THE FROZEN SEAT.**  Any card seated on a twin of a fork has a
class-invariant suit rung. -/
theorem seated_twin_rung_eq {F G : State} {x y c : Card}
    (hF : F.WF) (hG : G.WF) (hcls : sameOrbitSetoid.r F G)
    (hx : ForkWitness F x) (hy : ForkWitness G y) (hxy : y = x ∨ y = x.twin)
    (hc : seatOf F c = some (Sum.inr x) ∨ seatOf F c = some (Sum.inr x.twin)) :
    rungAt F c.suit = rungAt G c.suit := by
  obtain ⟨ρ, hρ, τ, hτ⟩ := hcls
  have hliveF : TwinLivePair F x := fun z => (hx.1 z).symm
  have hliveG : TwinLivePair G x := twinLivePair_of_forkWitness hy hxy
  have h1 : rungAt G c.suit ≤ rungAt F c.suit := by
    rcases hc with hc | hc
    · exact (cover_rung_frozen hF (x := x.twin) (y := x) (d := c)
        (by rw [tfc_card_twin_twin]) (twinLivePair_twin hliveF) hc hτ).1
    · exact (cover_rung_frozen hF (x := x) (y := x.twin) (d := c)
        rfl hliveF hc hτ).1
  have hcG : seatOf G c = some (Sum.inr x) ∨ seatOf G c = some (Sum.inr x.twin) :=
    seated_twin_stays hF hliveF hτ hc
  have h2 : rungAt F c.suit ≤ rungAt G c.suit := by
    rcases hcG with hc' | hc'
    · exact (cover_rung_frozen hG (x := x.twin) (y := x) (d := c)
        (by rw [tfc_card_twin_twin]) (twinLivePair_twin hliveG) hc' hρ).1
    · exact (cover_rung_frozen hG (x := x) (y := x.twin) (d := c)
        rfl hliveG hc' hρ).1
  omega

/-- **THE COVER SUIT IS CLASS-RIGID AT ANY FORK.**  The `hthird` row on the
cover suit, with NO orientation hypothesis: `Orig2/Fiber/LockRung.lean`'s
`coverSuit_rung_eq_of_sameOrientation` needs the same cover on the same twin at
both ends, which the token invariant supplies for free. -/
theorem fork_cover_suit_rigid {F G : State} {x y d : Card}
    (hF : F.WF) (hG : G.WF) (hcls : sameOrbitSetoid.r F G)
    (hx : ForkWitness F x) (hy : ForkWitness G y) (hxy : y = x ∨ y = x.twin)
    (hd : seatOf F d = some (Sum.inr x.twin)) :
    rungAt F d.suit = rungAt G d.suit :=
  seated_twin_rung_eq hF hG hcls hx hy hxy (Or.inr hd)

/-! ## §6. The low third-suit row -/

/-- **THE LOW THIRD SUIT IS FROZEN.**  If at the fork `F` (witness `w`, rank
`r`) the third suit `σ` sits at rung `≤ r - 1` and the rank-`(r-1)` third card
has no parent, then no witness descendant raises `σ` past that rung. -/
theorem lock_of_third_low {F Z : State} {w : Card} {σ : Suit} {play : List Move}
    (hF : F.WF) (hw : ForkWitness F w)
    (hσcol : σ.color ≠ w.suit.color) (hr1 : 1 ≤ w.rank.toIdx)
    (hno : NoParent F (⟨σ, FoundKit.Rk (w.rank.toIdx - 1)⟩ : Card))
    (hle : rungAt F σ ≤ w.rank.toIdx - 1)
    (hplay : ShufflePlayW F play Z) :
    rungAt Z σ ≤ rungAt F σ := by
  have hr13 : w.rank.toIdx < 13 := Rank.toIdx_lt w.rank
  have hnk : rungAt F σ < 13 := by omega
  have hnk11 : rungAt F σ ≤ 11 := by omega
  have hfrank : (⟨σ, FoundKit.Rk (rungAt F σ)⟩ : Card).rank.toIdx = rungAt F σ :=
    FoundKit.Rk_toIdx _ hnk
  have hfk : (⟨σ, FoundKit.Rk (rungAt F σ)⟩ : Card).rank ≠ Rank.king := by
    intro hk
    have h12 : (⟨σ, FoundKit.Rk (rungAt F σ)⟩ : Card).rank.toIdx = 12 := by
      rw [hk]; rfl
    omega
  have hinv : LockInv F (⟨σ, FoundKit.Rk (rungAt F σ)⟩ : Card) (rungAt F σ) := by
    refine ⟨?_, ?_, ?_⟩
    · intro a hmem
      by_cases hcase : rungAt F σ + 2 ≤ w.rank.toIdx
      · exact third_low_first hF hw hσcol hcase hmem
      · have hnn : rungAt F σ = w.rank.toIdx - 1 := by omega
        have hno' : NoParent F (⟨σ, FoundKit.Rk (rungAt F σ)⟩ : Card) := by
          rw [hnn]; exact hno
        exact below_nil_of_noParent hF hno' hmem
    · intro hmem
      have hlt := (FoundKit.mem_found_iff_height hF).mp hmem
      rw [hfrank] at hlt
      have hlt' : rungAt F σ < rungAt F σ := hlt
      omega
    · exact Nat.le_refl _
  obtain ⟨-, hinvZ⟩ := lockInv_play hplay hF hinv (by simpa using hfrank) hfk
  have hnot : ¬ (rungAt F σ < rungAt Z σ) := by
    intro hlt
    have hfound : (⟨σ, FoundKit.Rk (rungAt F σ)⟩ : Card) ∈ Z.found σ := by
      apply FoundKit.mem_found_of_rung (wf_of_shuffle hplay hF)
      rw [hfrank]
      exact hlt
    have hnf : (⟨σ, FoundKit.Rk (rungAt F σ)⟩ : Card) ∉ Z.found σ := by
      have h := hinvZ.2.1
      simpa using h
    exact hnf hfound
  omega

/-! ## §7. NoParent transport and the residual high row -/

/-- **NoParent TRANSPORTS ALONG THE CLASS.**  If the rank-`(r-1)` third card
has no parent at `F`, it has none at any class-mate carrying the same pair. -/
theorem noParent_transfer {F G : State} {x y : Card} {σ : Suit}
    (hF : F.WF) (hG : G.WF) (hcls : sameOrbitSetoid.r F G)
    (hx : ForkWitness F x) (hy : ForkWitness G y) (hxy : y = x ∨ y = x.twin)
    (hσcol : σ.color ≠ x.suit.color) (hr1 : 1 ≤ x.rank.toIdx)
    (hno : NoParent F (⟨σ, FoundKit.Rk (x.rank.toIdx - 1)⟩ : Card)) :
    NoParent G (⟨σ, FoundKit.Rk (x.rank.toIdx - 1)⟩ : Card) := by
  obtain ⟨ρ, hρ, τ, hτ⟩ := hcls
  have hyrank : y.rank = x.rank := by
    rcases hxy with h | h
    · rw [h]
    · rw [h, Card.twin_rank]
  have hycol : y.suit.color = x.suit.color := by
    rcases hxy with h | h
    · rw [h]
    · rw [h, Card.twin_suit]; exact Suit.color_twin x.suit
  intro z hz
  obtain ⟨a, hhold, -, -⟩ := tfc_seatOf_of_inr hz
  have hmem := pileHolding_mem hhold
  have hcw : (⟨σ, FoundKit.Rk (x.rank.toIdx - 1)⟩ : Card)
      = (⟨σ, FoundKit.Rk (y.rank.toIdx - 1)⟩ : Card) := by rw [hyrank]
  rw [hcw] at hmem
  have hzw : seatOf G (⟨σ, FoundKit.Rk (y.rank.toIdx - 1)⟩ : Card) = some (Sum.inr z) := by
    rw [← hcw]; exact hz
  have hzt := third_top_parent_is_pair hG (w := y) (σ := σ)
    (by rw [hycol]; exact hσcol) (by rw [hyrank]; exact hr1)
    (c := (⟨σ, FoundKit.Rk (y.rank.toIdx - 1)⟩ : Card)) rfl hzw
  have hzt' : z = x ∨ z = x.twin := by
    rcases hzt with h | h
    · rcases hxy with h1 | h1
      · exact Or.inl (h.trans h1)
      · exact Or.inr (h.trans h1)
    · rcases hxy with h1 | h1
      · refine Or.inr ?_
        rw [h, h1]
      · refine Or.inl ?_
        rw [h, h1, tfc_card_twin_twin]
  have hliveG : TwinLivePair G x := twinLivePair_of_forkWitness hy hxy
  have hdisj : seatOf G (⟨σ, FoundKit.Rk (x.rank.toIdx - 1)⟩ : Card) = some (Sum.inr x)
      ∨ seatOf G (⟨σ, FoundKit.Rk (x.rank.toIdx - 1)⟩ : Card) = some (Sum.inr x.twin) := by
    rcases hzt' with h | h
    · exact Or.inl (h ▸ hz)
    · exact Or.inr (h ▸ hz)
  have hstay := seated_twin_stays hG hliveG hρ hdisj
  rcases hstay with h' | h'
  · exact hno x h'
  · exact hno x.twin h'

/-- **THE RESIDUAL HIGH ROW** — the only unproved case left: both endpoints
sit at third rung `≥ r` (the rank-equal / super-rank leak). -/
def ForkThirdRigidHigh : Prop :=
  ∀ (F G : State) (x y : Card), F.WF → G.WF → sameOrbitSetoid.r F G →
    ForkWitness F x → ForkWitness G y → (y = x ∨ y = x.twin) →
    ∀ σ : Suit, σ ≠ x.suit → σ ≠ x.twin.suit →
      x.rank.toIdx ≤ rungAt F σ → x.rank.toIdx ≤ rungAt G σ →
      rungAt F σ = rungAt G σ

/-- **THE ASSEMBLY.**  Cover-seat freezing + the low row + the high row give
`ForkThirdRigid`. -/
theorem forkThirdRigid_of_high (hh : ForkThirdRigidHigh) : ForkThirdRigid := by
  intro F G x y hF hG hcls hx hy hxy σ hσ1 hσ2
  have hcls' : sameOrbitSetoid.r F G := hcls
  obtain ⟨ρ, hρ, τ, hτ⟩ := hcls
  have hr2 := fork_rank_ge_two hF hx
  have hr1 : 1 ≤ x.rank.toIdx := by omega
  have hσcol : σ.color ≠ x.suit.color := third_color_ne hσ1 hσ2
  have hyrank : y.rank = x.rank := by
    rcases hxy with h | h
    · rw [h]
    · rw [h, Card.twin_rank]
  have hycol : y.suit.color = x.suit.color := by
    rcases hxy with h | h
    · rw [h]
    · rw [h, Card.twin_suit]; exact Suit.color_twin x.suit
  have hyidx : y.rank.toIdx = x.rank.toIdx := by rw [hyrank]
  by_cases hx' : seatOf F (⟨σ, FoundKit.Rk (x.rank.toIdx - 1)⟩ : Card)
      = some (Sum.inr x)
  · exact seated_twin_rung_eq hF hG hcls' hx hy hxy (Or.inl hx')
  by_cases ht' : seatOf F (⟨σ, FoundKit.Rk (x.rank.toIdx - 1)⟩ : Card)
      = some (Sum.inr x.twin)
  · exact seated_twin_rung_eq hF hG hcls' hx hy hxy (Or.inr ht')
  · have hno : NoParent F (⟨σ, FoundKit.Rk (x.rank.toIdx - 1)⟩ : Card) := by
      intro z hz
      obtain ⟨a, hhold, -, -⟩ := tfc_seatOf_of_inr hz
      have hmem := pileHolding_mem hhold
      have hzt := third_top_parent_is_pair hF (w := x) (σ := σ) hσcol hr1
        (c := (⟨σ, FoundKit.Rk (x.rank.toIdx - 1)⟩ : Card)) rfl hz
      rcases hzt with rfl | rfl
      · exact hx' hz
      · exact ht' hz
    have hnoG := noParent_transfer hF hG hcls' hx hy hxy hσcol hr1 hno
    have hnoY : NoParent G (⟨σ, FoundKit.Rk (y.rank.toIdx - 1)⟩ : Card) := by
      rw [hyrank]; exact hnoG
    have hσcolY : σ.color ≠ y.suit.color := by rw [hycol]; exact hσcol
    have hr1Y : 1 ≤ y.rank.toIdx := by rw [hyrank]; exact hr1
    by_cases hle : rungAt F σ ≤ x.rank.toIdx - 1
    · have h1 : rungAt G σ ≤ rungAt F σ :=
        lock_of_third_low hF hx hσcol hr1 hno hle hτ
      by_cases hleG : rungAt G σ ≤ y.rank.toIdx - 1
      · have h2 : rungAt F σ ≤ rungAt G σ :=
          lock_of_third_low hG hy hσcolY hr1Y hnoY hleG hρ
        omega
      · omega
    · by_cases hleG : rungAt G σ ≤ y.rank.toIdx - 1
      · have h2 : rungAt F σ ≤ rungAt G σ :=
          lock_of_third_low hG hy hσcolY hr1Y hnoY hleG hρ
        omega
      · exact hh F G x y hF hG hcls' hx hy hxy σ hσ1 hσ2 (by omega) (by omega)

end ThirdRigid

#print axioms ThirdRigid.third_low_first
#print axioms ThirdRigid.third_top_parent_is_pair
#print axioms ThirdRigid.seated_twin_stays
#print axioms ThirdRigid.seated_twin_rung_eq
#print axioms ThirdRigid.fork_cover_suit_rigid
#print axioms ThirdRigid.lock_of_third_low
#print axioms ThirdRigid.noParent_transfer
#print axioms ThirdRigid.forkThirdRigid_of_high
