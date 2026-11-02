import Orig2.Fork.ForkThird

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Orig2.ForkThirdHigh - the third-suit residue, unconditional

`ForkThirdRigidHigh` is proved in full, including the king fork.  The
non-king half is `forkThirdRigidHigh_of_not_king`; the king slice is
`KingExodusSeated`, proved here via the `KingKeep` invariant (§8), which
yields `forkThirdRigidHigh_unconditional`, `forkThirdRigid_unconditional`
and `forkPositionRigid_unconditional`.

* `third_rung_le_succ` — at a non-king fork every third-suit rung is at
  most `r + 1` (the rank-`(r+1)` third card is one of the two distinct
  under-cards of `fork_under_cards`, hence face-up and not founded).
* `pull_landing_supported` / `found_or_supported_step` /
  `supported_of_forked_transit` — the exodus invariant: a card founded at
  one endpoint and unfounded at the other is supported
  (`seatOf c = some (.inr z)`) at the far end unless founded there.
* `no_supported_nextUp_third` — a supported, next-up third-suit card of
  rank `≥ r` at a fork is impossible: it is vanilla-raisable (hence
  S-live, hence a pair member) or covered by a founded rank-`(r-1)`
  pair card (`pair_lowFamily_founded`).
* `forkThirdRigidHigh_of_not_king` — the non-king half, PROVED.
* `forkThirdRigidHigh_of_nonKing_and_king` - the king slice is exactly
  `ForkThirdRigidHighKing`.
* `KingExodusSeated` - the king exodus: a king founded deep and unfounded
  shallow is seated at the shallow fork with `hidden = []`.
  `forkThirdRigidHigh_of_kingSeated` proves the high row from it, and
  §8 proves `KingExodusSeated` itself, hence
  `forkThirdRigidHigh_unconditional`, `forkThirdRigid_unconditional` and
  `forkPositionRigid_unconditional`.

The naive bound `rung ≤ r` is false; the sharp non-king bound is
`rung ≤ r + 1`.  Do not chase a `k > r` descent: `third_rung_le_succ`
leaves only the `k = r` floor.

House compliance: additive leaf (`Orig2.ForkThird`); zero `sorry`, zero
`Classical.choice`; battery at tail.
-/
namespace ThirdHigh

/-! ## §1. The two under-cards are distinct -/

/-- `below` of `L ++ c :: R` is `L`, when `c` does not occur in `L`. -/
theorem below_append_cons_notmem {c : Card} :
    ∀ {L : List Card}, c ∉ L → ∀ R : List Card, below c (L ++ c :: R) = L
  | [], _, _ => by simp [below_cons]
  | y :: t, hyt, R => by
      have hyt' : c ∉ t := fun h => hyt (List.mem_cons_of_mem y h)
      have hyc : y ≠ c := fun h => hyt (List.mem_cons.mpr (Or.inl h.symm))
      rw [List.cons_append, below_cons, ite_eq_right hyc,
        below_append_cons_notmem hyt' R]

/-- The card directly under the twin is not the card directly under the
witness: the two `r+1` under-cards of `fork_under_cards` are distinct
cards. -/
theorem under_cards_ne {st : State} (hwf : st.WF) {x u v : Card}
    {a b : Anchor} {P S Q T : List Card}
    (hu : (st.piles a).faceUp = P ++ u :: x :: S)
    (hv : (st.piles b).faceUp = Q ++ v :: x.twin :: T)
    (huv : u = v) : False := by
  subst huv
  have humemA : u ∈ (st.piles a).faceUp := by rw [hu]; simp
  have humemB : u ∈ (st.piles b).faceUp := by rw [hv]; simp
  have hab : a = b := by
    by_cases h : a = b
    · exact h
    · exact absurd humemB (mem_faceUp_unique hwf humemA b (Ne.symm h)).1
  subst hab
  have heq : P ++ u :: x :: S = Q ++ u :: x.twin :: T := by rw [← hu, ← hv]
  have hndB : (st.piles a).faceUp.Nodup := runOK_nodup (hwf.2.1 a)
  have hnd : (P ++ u :: x :: S).Nodup := by rw [heq, ← hv]; exact hndB
  have huP : u ∉ P := by
    intro hmem
    exact ((List.nodup_append.1 hnd).2.2 u hmem) u (List.mem_cons_self ..) rfl
  have hndQ : (Q ++ u :: x.twin :: T).Nodup := by rw [← hv]; exact hndB
  have huQ : u ∉ Q := by
    intro hmem
    exact ((List.nodup_append.1 hndQ).2.2 u hmem) u (List.mem_cons_self ..) rfl
  have hP : P = Q := by
    have h1 : below u (P ++ u :: x :: S) = P := below_append_cons_notmem huP _
    have h2 : below u (Q ++ u :: x.twin :: T) = Q := below_append_cons_notmem huQ _
    rw [heq] at h1
    rw [← h1, h2]
  have hsuffix : x :: S = x.twin :: T := by
    have h2 : (Q ++ [u]) ++ x :: S = (Q ++ [u]) ++ x.twin :: T := by
      rw [hP] at heq
      simpa [List.append_assoc] using heq
    exact List.append_cancel_left h2
  have hx : x = x.twin := by
    have := congrArg List.head? hsuffix
    simpa using this
  have hsuit : x.suit = x.suit.twin := congrArg Card.suit hx
  exact Suit.twin_ne x.suit hsuit.symm

/-! ## §2. The non-king third-rung bound -/

/-- **THE THIRD RUNG IS AT MOST `r + 1`.**  At a non-king fork, the
rank-`(r+1)` card of any third suit is one of the two distinct
under-cards of `fork_under_cards`, hence face-up, hence not founded. -/
theorem third_rung_le_succ {st : State} (hwf : st.WF) {x : Card}
    (hx : ForkWitness st x) (hk : x.rank ≠ Rank.king) {σ : Suit}
    (hσ : σ.color ≠ x.suit.color) :
    rungAt st σ ≤ x.rank.toIdx + 1 := by
  have hrlt : x.rank.toIdx < 13 := Rank.toIdx_lt x.rank
  have hrle : x.rank.toIdx ≤ 11 := by
    have hne : x.rank.toIdx ≠ 12 := fun h => hk (Rank.toIdx_inj h)
    omega
  obtain ⟨⟨a, u, P, S, hshapeu, hranku, hcolu⟩,
    ⟨b, v, Q, T, hshapev, hrankv, hcolv⟩⟩ := fork_under_cards hwf hx hk
  let e : Card := ⟨σ, FoundKit.Rk (x.rank.toIdx + 1)⟩
  have heidx : e.rank.toIdx = x.rank.toIdx + 1 :=
    FoundKit.Rk_toIdx _ (by omega)
  have hucol : u.suit.color = σ.color :=
    SeedKit.color_pair (Ne.symm hcolu) (Ne.symm hσ)
  have hvcol : v.suit.color = σ.color :=
    SeedKit.color_pair (Ne.symm hcolv) (Ne.symm hσ)
  have heuv : e = u ∨ e = v := by
    have huf := SeedKit.suit_family hucol
    have hvf := SeedKit.suit_family hvcol
    rcases huf with hu1 | hu1
    · exact Or.inl (card_eq_of_suit_rank (c := e) (c' := u)
        (by simpa using hu1) (by rw [heidx, hranku])).symm
    · rcases hvf with hv1 | hv1
      · exact Or.inr (card_eq_of_suit_rank (c := e) (c' := v)
          (by simpa using hv1) (by rw [heidx, hrankv])).symm
      · exfalso
        have huv : u = v :=
          card_eq_of_suit_rank (by rw [hu1, hv1]) (by rw [hranku, hrankv])
        exact under_cards_ne hwf hshapeu hshapev huv
  have hemem : e ∈ (st.piles a).faceUp ∨ e ∈ (st.piles b).faceUp := by
    rcases heuv with h | h
    · exact Or.inl (by rw [h, hshapeu]; simp)
    · exact Or.inr (by rw [h, hshapev]; simp)
  have hle : rungAt st σ ≤ e.rank.toIdx := by
    rcases hemem with hm | hm
    · exact piled_rung hwf hm
    · exact piled_rung hwf hm
  rwa [heidx] at hle

/-! ## §3. The pull landing: a non-king pull sits on a card -/

/-- `Supported st c` — `c` sits directly on a card of the tableau. -/
def Supported (st : State) (c : Card) : Prop :=
  ∃ z, seatOf st c = some (Sum.inr z)

/-- **THE LANDING SEED** — a non-king `foundToTab` landing places the
pulled card directly on a tableau card (the `inl` branch is king-gated).
(Frozen precedent: `seat_landing_seed`, `Orig/OrphanSeat.lean:1411`.) -/
theorem pull_landing_supported {st s' : State} (hwf : st.WF) {c : Card}
    {b : Base} (hstep : State.step st (Move.foundToTab c b) = some s')
    (hnk : c.rank ≠ Rank.king) : Supported s' c := by
  obtain ⟨c', htop, hc'c, hcp, hs⟩ := step_foundToTab_inv hstep
  rw [hc'c] at htop
  cases b with
  | inl k => exact absurd (canPlace_inl hcp).2 hnk
  | inr z =>
      obtain ⟨k, hpok, hfit⟩ := canPlace_inr hcp
      have hmidpo : (st.setFound c.suit (chop (st.found c.suit))).pileOfTop z = some k := by
        rw [State.setFound_pileOfTop]; exact hpok
      obtain ⟨-, hlastk⟩ := pileOfTop_top hmidpo
      obtain ⟨Lk, hLk⟩ := lastOf_eq_snoc hlastk
      have hpiles : (st.setFound c.suit (chop (st.found c.suit))).piles k = st.piles k := by
        rw [setFound_piles]
      have hLk' : (st.piles k).faceUp = Lk ++ [z] := by rw [← hpiles, hLk]
      have hface : (s'.piles k).faceUp = Lk ++ z :: c :: ([] : List Card) := by
        rw [hs, putCard_piles_inr _ _ _ _ hmidpo]
        dsimp only []
        rw [hpiles, hLk']
        simp [List.append_assoc]
      have hcLk : c ∉ Lk := by
        intro hmem
        have hmem' : c ∈ (st.piles k).faceUp := by
          rw [hLk']; exact List.mem_append_left _ hmem
        exact ((mem_found_unique hwf (lastOf_mem htop)).1 k).2 hmem'
      have hzc : z ≠ c := by
        intro h
        have hr := (canSitOn_eq c z).mp hfit |>.1
        rw [h] at hr
        omega
      have hwf' : s'.WF := step_wf hwf hstep
      have hck : c ∈ (s'.piles k).faceUp := by rw [hface]; simp
      refine ⟨z, tfc_seatOf_inr_intro ((pileHolding_eq_some_iff hwf').2 hck) ?_⟩
      have hnot : c ∉ Lk ++ [z] := by
        intro hmem
        rcases List.mem_append.mp hmem with h1 | h2
        · exact hcLk h1
        · exact hzc (List.mem_singleton.mp h2).symm
      rw [hface]
      rw [show Lk ++ z :: c :: ([] : List Card) = (Lk ++ [z]) ++ c :: []
        from by simp]
      rw [below_append_cons_notmem (c := c) hnot]
      exact lastOf_snoc

/-! ## §4. The exodus invariant -/

/-- **ONE WITNESS LETTER.**  `founded ∨ supported` survives every
reversible step: the raise keeps/sets the founded arm, the pull's
landing (non-king) sets the supported arm, a slide keeps or twin-hops
the seat (`tfc_leg_seat_rel`), the draw leaves the board alone. -/
theorem found_or_supported_step {st s₁ : State} {m : Move} {c : Card}
    (hwf : st.WF) (hrev : reversibleAtW st m) (hstep : State.step st m = some s₁)
    (hnk : c.rank ≠ Rank.king)
    (hcur : c ∈ st.found c.suit ∨ Supported st c) :
    c ∈ s₁.found c.suit ∨ Supported s₁ c := by
  rcases m with _ | cf | ⟨cf, bf⟩ | cf | ⟨cf, bf⟩ | ⟨cf, bf⟩
  · -- draw
    have hd : st.stepDraw = some s₁ := hstep
    rcases hcur with hf | hsup
    · left
      rw [stepDraw_found hd]
      exact hf
    · obtain ⟨z, hz⟩ := hsup
      right
      exact ⟨z, by rw [seatOf_congr_piles (stepDraw_piles hd)]; exact hz⟩
  · exact absurd hrev (wasteToFound_not_reversibleAtW st cf)
  · exact absurd hrev (wasteToTab_not_reversibleAtW st cf bf)
  · -- tabToFound cf
    obtain ⟨hnext, a, hpa, hsV⟩ := step_tabToFound_inv hstep
    rcases hcur with hf | hsup
    · left
      rw [hsV]
      show c ∈ (st.setFound cf.suit (st.found cf.suit ++ [cf])).found c.suit
      by_cases hcf : c.suit = cf.suit
      · rw [hcf.symm, setFound_found_self]
        exact List.mem_append_left _ hf
      · rw [setFound_found_ne hcf]
        exact hf
    · obtain ⟨z, hz⟩ := hsup
      by_cases hcf : c = cf
      · subst hcf
        left
        rw [hsV]
        show c ∈ (st.setFound c.suit (st.found c.suit ++ [c])).found c.suit
        rw [setFound_found_self]
        exact List.mem_append_right _ (List.mem_singleton_self c)
      · right
        exact ⟨z, by
          rw [raise_seat_change_of_seated hstep hrev (by rw [hz]; simp) hcf]
          exact hz⟩
  · -- foundToTab cf bf
    rcases hcur with hf | hsup
    · by_cases hcf : c = cf
      · subst hcf
        right
        exact pull_landing_supported hwf hstep hnk
      · left
        obtain ⟨c', htop, hc'c, hcp, hsV⟩ := step_foundToTab_inv hstep
        rw [hsV]
        show c ∈ ((st.setFound cf.suit (chop (st.found cf.suit))).putCard cf bf).found c.suit
        rw [putCard_found]
        by_cases hcs : c.suit = cf.suit
        · have hsnoc : st.found c.suit = chop (st.found c.suit) ++ [cf] := by
            have htop' : st.foundTop c.suit = some cf := by
              rw [hcs, htop, hc'c]
            exact lastOf_chop htop'
          rw [hcs.symm, setFound_found_self]
          rw [hsnoc] at hf
          rcases List.mem_append.mp hf with h | h
          · exact h
          · exact absurd (List.mem_singleton.mp h) hcf
        · rw [setFound_found_ne hcs]
          exact hf
    · by_cases hcf : c = cf
      · subst hcf
        right
        exact pull_landing_supported hwf hstep hnk
      · obtain ⟨z, hz⟩ := hsup
        right
        refine ⟨z, ?_⟩
        rw [pull_seat_change hstep c hcf]
        exact hz
  · -- tabToTab cf bf
    rcases hcur with hf | hsup
    · left
      obtain ⟨a, hhold, hcp, hne0, hsV⟩ := step_tabToTab_inv hstep
      rw [hsV, putRun_found, setPile_found]
      exact hf
    · obtain ⟨z, hz⟩ := hsup
      have hrel := tfc_leg_seat_rel hwf hstep hrev c
      rcases hrel with heq | ⟨z', hz', hz'm⟩ | ⟨hk, h1, h2, h3⟩
      · right; exact ⟨z, by rw [heq]; exact hz⟩
      · right; exact ⟨z'.twin, hz'm⟩
      · exact absurd hk hnk

/-- **THE EXODUS TRANSIT** — a card founded at the origin of a witness
play and unfounded at its end is SUPPORTED at the end: it left the
foundation through its own pull (the only removal letter,
`found_exodus`), and from that landing on it always sits on a card
(the landing seed) until it is founded again. -/
theorem supported_of_forked_transit {A B : State} {c : Card} {play : List Move}
    (hwf : A.WF) (hplay : ShufflePlayW A play B) (hnk : c.rank ≠ Rank.king)
    (hA : c ∈ A.found c.suit) (hB : c ∉ B.found c.suit) : Supported B c := by
  have key : ∀ (U : State) (ρ : List Move) (V : State), ShufflePlayW U ρ V →
      U.WF → (c ∈ U.found c.suit ∨ Supported U c) →
      (c ∈ V.found c.suit ∨ Supported V c) := by
    intro U ρ V hp
    induction hp with
    | nil st => intro _ h; exact h
    | @cons st s₁ W m ρ' hrev hstep hrest ih =>
        intro hwfU hcur
        exact ih (step_wf hwfU hstep)
          (found_or_supported_step hwfU hrev hstep hnk hcur)
  exact (key A play B hplay hwf (Or.inl hA)).resolve_left hB

/-- Two-colour elimination: `a ≠ b` and `b ≠ c` force `a = c`. -/
theorem color_eq_of_ne {a b c : Color} (h1 : a ≠ b) (h2 : b ≠ c) : a = c := by
  cases a <;> cases b <;> cases c <;> simp_all

/-! ## §5. The supported next-up third card at a fork -/

/-- **THE FIRST HIGH PASSAGE** — at a `WF` fork, a third-suit card
`c` of rank `≤ r` that is next-up and sits on a card is impossible.

If `c` tops its pile it is vanilla-raisable (the card beneath makes the
chop nonempty), hence `S`-live, hence a pair member by `ForkWitness` —
suit contradiction.  Otherwise the card `d` directly above it covers it:
`d` is one rank below, opposite colour (hence a pair-family card), and
`pair_lowFamily_founded` founds it, against its being face-up. -/
theorem no_supported_nextUp_third {st : State} (hwf : st.WF) {x c : Card}
    (hx : ForkWitness st x) (hcnk : c.rank ≠ Rank.king)
    (hσ : c.suit.color ≠ x.suit.color)
    (hcrank : c.rank.toIdx ≤ x.rank.toIdx)
    (hnext : st.nextUp c = true) (hsup : Supported st c) : False := by
  obtain ⟨z, hz⟩ := hsup
  obtain ⟨a, hhold, hbne, hlast⟩ := tfc_seatOf_of_inr hz
  have hmem : c ∈ (st.piles a).faceUp := pileHolding_mem hhold
  have hrok : runOK (st.piles a).faceUp = true := hwf.2.1 a
  obtain ⟨rest, hrest⟩ := fromCard_eq_head_of_mem hmem
  have hsplit : (st.piles a).faceUp = below c (st.piles a).faceUp ++ c :: rest := by
    have h0 := tfc_below_fromCard c (st.piles a).faceUp
    rw [hrest] at h0
    exact h0.symm
  obtain ⟨L, hL⟩ := lastOf_eq_snoc hlast
  cases rest with
  | nil =>
      have hface : (st.piles a).faceUp = L ++ z :: c :: ([] : List Card) := by
        rw [hsplit, hL]; simp [List.append_assoc]
      have htop : lastOf (st.piles a).faceUp = some c := by
        rw [hface]; exact lastOf_snoc2 L z c
      have hpa : st.pileOfTop c = some a := (pileOfTop_eq_some_iff hwf).2 htop
      have hchop : chop (st.piles a).faceUp ≠ [] := by
        rw [hface, show L ++ z :: c :: ([] : List Card) = (L ++ [z]) ++ [c]
          from by simp, chop_snoc]
        cases L with
        | nil => simp
        | cons w ws => simp
      have hcan : CanRaise st c := ⟨hnext, a, hpa, Or.inl hchop⟩
      have hS : CanRaiseS st c := CanRaiseS.now c hcan
      rcases (hx.1 c).mpr hS with h | h
      · rw [h] at hσ; exact hσ rfl
      · rw [h, Card.twin_suit] at hσ
        exact hσ (Suit.color_twin x.suit)
  | cons d rest' =>
      have hface : (st.piles a).faceUp = L ++ z :: c :: d :: rest' := by
        rw [hsplit, hL]; simp [List.append_assoc]
      have hfit : canSitOn d c = true := by
        have hrok' : runOK (L ++ z :: c :: d :: rest') = true := by
          rw [← hface]; exact hrok
        exact SeedKit.runOK_adjacent_fit c d (L ++ [z]) rest'
          (by simpa [List.append_assoc] using hrok')
      obtain ⟨hrank, hcol⟩ := (canSitOn_eq d c).mp hfit
      have hcolx : d.suit.color = x.suit.color :=
        SeedKit.color_pair (a := c.suit.color) (Ne.symm hcol) hσ
      have hdlt : d.rank.toIdx < x.rank.toIdx := by omega
      have hdfound : d ∈ st.found d.suit := pair_lowFamily_founded hwf hx hcolx hdlt
      have hdmem : d ∈ (st.piles a).faceUp := by rw [hface]; simp
      exact ((mem_found_unique hwf hdfound).1 a).2 hdmem

/-! ## §6. The assembly: everything but the king fork -/

/-- In the "shallow at `F`" orientation, a third rung at least `r` at
both forks and strictly smaller at `F` is impossible. -/
theorem high_false_of_lt {F G : State} (hF : F.WF) (hG : G.WF)
    (hcls : sameOrbitSetoid.r F G) {x y : Card}
    (hx : ForkWitness F x) (hy : ForkWitness G y) (hxy : y = x ∨ y = x.twin)
    (hxK : x.rank ≠ Rank.king) {σ : Suit} (hσ1 : σ ≠ x.suit)
    (hσ2 : σ ≠ x.twin.suit) (hgeF : x.rank.toIdx ≤ rungAt F σ)
    (hlt : rungAt F σ < rungAt G σ) : False := by
  have hσcol : σ.color ≠ x.suit.color := ThirdRigid.third_color_ne hσ1 hσ2
  have hyK : y.rank ≠ Rank.king := by
    rcases hxy with h | h
    · rw [h]; exact hxK
    · rw [h, Card.twin_rank]; exact hxK
  have hσcolG : σ.color ≠ y.suit.color := by
    rcases hxy with h | h
    · rw [h]; exact hσcol
    · rw [h, Card.twin_suit, Suit.color_twin]; exact hσcol
  have hbF := third_rung_le_succ hF hx hxK hσcol
  have hbG := third_rung_le_succ hG hy hyK hσcolG
  have hyidx : y.rank.toIdx = x.rank.toIdx := by
    rcases hxy with h | h
    · rw [h]
    · rw [h, Card.twin_rank]
  have hrF : rungAt F σ = x.rank.toIdx := by omega
  let c : Card := ⟨σ, FoundKit.Rk x.rank.toIdx⟩
  have hcidx : c.rank.toIdx = x.rank.toIdx :=
    FoundKit.Rk_toIdx _ (Rank.toIdx_lt x.rank)
  have hcG : c ∈ G.found c.suit := by
    apply (FoundKit.mem_found_iff_height hG).mpr
    rw [hcidx]
    have hg : rungAt G c.suit = rungAt G σ := rfl
    rw [hg]
    omega
  have hcF : c ∉ F.found c.suit := by
    intro hmem
    have h := (FoundKit.mem_found_iff_height hF).mp hmem
    have hf : rungAt F c.suit = rungAt F σ := rfl
    rw [hf] at h
    rw [hcidx] at h
    omega
  obtain ⟨play, hplay, -⟩ := hcls
  have hcnk : c.rank ≠ Rank.king := by
    intro hk
    apply hxK
    apply Rank.toIdx_inj
    rw [← hcidx]
    exact congrArg Rank.toIdx hk
  have hsup : Supported F c :=
    supported_of_forked_transit hG hplay hcnk hcG hcF
  have hnext : F.nextUp c = true := by
    unfold State.nextUp State.foundHeight
    rw [hcidx]
    have hlen : (F.found σ).length = x.rank.toIdx := by
      show rungAt F σ = x.rank.toIdx
      exact hrF
    rw [hlen]
    exact decide_eq_true rfl
  exact no_supported_nextUp_third hF hx hcnk (by show σ.color ≠ x.suit.color; exact hσcol)
    (by rw [hcidx]; exact Nat.le_refl _) hnext hsup

/-- **THE HIGH ROW, NON-KING FORKS.**  `ForkThirdRigidHigh` for every
witness whose rank is not the king rank. -/
theorem forkThirdRigidHigh_of_not_king :
    ∀ (F G : State) (x y : Card), F.WF → G.WF → sameOrbitSetoid.r F G →
      ForkWitness F x → ForkWitness G y → (y = x ∨ y = x.twin) →
      x.rank ≠ Rank.king →
      ∀ σ : Suit, σ ≠ x.suit → σ ≠ x.twin.suit →
        x.rank.toIdx ≤ rungAt F σ → x.rank.toIdx ≤ rungAt G σ →
        rungAt F σ = rungAt G σ := by
  intro F G x y hF hG hcls hx hy hxy hxK σ hσ1 hσ2 hgeF hgeG
  rcases Nat.lt_trichotomy (rungAt F σ) (rungAt G σ) with hlt | heq | hgt
  · exact (high_false_of_lt hF hG hcls hx hy hxy hxK hσ1 hσ2 hgeF hlt).elim
  · exact heq
  · have hyK : y.rank ≠ Rank.king := by
      rcases hxy with h | h
      · rw [h]; exact hxK
      · rw [h, Card.twin_rank]; exact hxK
    have hxy' : x = y ∨ x = y.twin := by
      rcases hxy with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h, tfc_card_twin_twin])
    have hσ1' : σ ≠ y.suit := by
      rcases hxy with h | h
      · rw [h]; exact hσ1
      · rw [h, Card.twin_suit]; exact hσ2
    have hσ2' : σ ≠ y.twin.suit := by
      rcases hxy with h | h
      · rw [h]; exact hσ2
      · rw [h, tfc_card_twin_twin]; exact hσ1
    have hyrank : y.rank.toIdx = x.rank.toIdx := by
      rcases hxy with h | h
      · rw [h]
      · rw [h, Card.twin_rank]
    have hcls' : sameOrbitSetoid.r G F := RevEqW_symm hcls
    exact (high_false_of_lt hG hF hcls' hy hx hxy' hyK hσ1' hσ2'
      (by rw [hyrank]; exact hgeG) hgt).elim

/-! ## §7. The king residue -/

/-- **THE EXACT KING RESIDUE.**  The only shape
`forkThirdRigidHigh_of_not_king` leaves: a king fork (`r = 12`) whose
third suit reads `12` at one endpoint and `13` (a COMPLETE third suit)
at the other.  (`RungAt ≤ 13` caps the rungs, so `(12, 13)` is the only
differing pair; a king fork is exactly `r = 12`.) -/
def ForkThirdRigidHighKing : Prop :=
  ∀ (F G : State) (x y : Card), F.WF → G.WF → sameOrbitSetoid.r F G →
    ForkWitness F x → ForkWitness G y → (y = x ∨ y = x.twin) →
    x.rank = Rank.king →
    ∀ σ : Suit, σ ≠ x.suit → σ ≠ x.twin.suit →
      rungAt F σ = 12 → rungAt G σ = 13 → False

/-- **THE KING RESIDUE, ASSEMBLED.**  `ForkThirdRigidHigh` for king
forks is exactly the `(12, 13)` slice: the rungs live in `[12, 13]` and
a differing pair must be `(12, 13)`. -/
theorem forkThirdRigidHigh_of_nonKing_and_king (hK : ForkThirdRigidHighKing) :
    ThirdRigid.ForkThirdRigidHigh := by
  intro F G x y hF hG hcls hx hy hxy σ hσ1 hσ2 hgeF hgeG
  by_cases hxK : x.rank ≠ Rank.king
  · exact forkThirdRigidHigh_of_not_king F G x y hF hG hcls hx hy hxy hxK
      σ hσ1 hσ2 hgeF hgeG
  · have hxk : x.rank = Rank.king := by
      by_cases h : x.rank = Rank.king
      · exact h
      · exact absurd h hxK
    have hr12 : x.rank.toIdx = 12 := by rw [hxk]; rfl
    have hbF := rungAt_le13 hF σ
    have hbG := rungAt_le13 hG σ
    have hyrank : y.rank.toIdx = x.rank.toIdx := by
      rcases hxy with h | h
      · rw [h]
      · rw [h, Card.twin_rank]
    have hyk : y.rank = Rank.king := by
      apply Rank.toIdx_inj
      rw [hyrank, hr12]
      rfl
    rcases Nat.lt_trichotomy (rungAt F σ) (rungAt G σ) with hlt | heq | hgt
    · have h1 : rungAt F σ = 12 := by omega
      have h2 : rungAt G σ = 13 := by omega
      exact (hK F G x y hF hG hcls hx hy hxy hxk σ hσ1 hσ2 h1 h2).elim
    · exact heq
    · have h1 : rungAt G σ = 12 := by omega
      have h2 : rungAt F σ = 13 := by omega
      have hxy' : x = y ∨ x = y.twin := by
        rcases hxy with h | h
        · exact Or.inl h.symm
        · exact Or.inr (by rw [h, tfc_card_twin_twin])
      have hσ1' : σ ≠ y.suit := by
        rcases hxy with h | h
        · rw [h]; exact hσ1
        · rw [h, Card.twin_suit]; exact hσ2
      have hσ2' : σ ≠ y.twin.suit := by
        rcases hxy with h | h
        · rw [h]; exact hσ2
        · rw [h, tfc_card_twin_twin]; exact hσ1
      exact (hK G F y x hG hF (RevEqW_symm hcls) hy hx hxy' hyk
        σ hσ1' hσ2' h1 h2).elim

/-- **THE EXACT MISSING KING LEMMA.**  A king that is FOUNDED at the
deep endpoint of a witness class and UNFOUNDED at the shallow one is, at
the shallow endpoint, seated with a HIDDEN-FREE pile.

INFORMAL PROOF (the `found_exodus` mechanism in the king slice):
* a founded king leaves the foundation only through its own
  `foundToTab`; the step guard's `canPlace` sends a king to an EMPTY
  anchor (`canPlace_inl`: `isEmpty`), so the landing pile has
  `hidden = []`;
* hidden decks never grow (`afterRunRemoved_hidden_le`, `putCard` /
  `putRun` leave `hidden` alone); and a king is the BOTTOM card of its
  pile (no rank above the king), so it can only slide as a bare bottomed
  king — `tfc_tabToTabR_inv` forces `hidden = []` at the source and
  `canPlace_inl` gives `hidden = []` at the target;
* hence every pile that ever holds the exodus king has `hidden = []`.
So at the shallow fork the king is handed back with an empty hidden deck,
and the §5 dichotomy closes: top + empty chop + empty hidden is a BARE
KING (vanilla-raisable), non-top is covered by a rank-`11` pair card,
which is founded at the king fork's pair rung `12`. -/
def KingExodusSeated : Prop :=
  ∀ (F G : State) (c : Card),
    F.WF → G.WF → sameOrbitSetoid.r F G →
    c.rank = Rank.king →
    c ∉ F.found c.suit → c ∈ G.found c.suit →
    ∃ a, F.pileHolding c = some a ∧ (F.piles a).hidden = []

/-- **THE KING SLICE, from `KingExodusSeated`.** -/
theorem forkThirdRigidHighKing_of_seated (hseat : KingExodusSeated) :
    ForkThirdRigidHighKing := by
  intro F G x y hF hG hcls hx hy hxy hxk σ hσ1 hσ2 h12 h13
  have hσcol : σ.color ≠ x.suit.color := ThirdRigid.third_color_ne hσ1 hσ2
  let c : Card := ⟨σ, Rank.king⟩
  have hcidx : c.rank.toIdx = 12 := rfl
  have hcF : c ∉ F.found c.suit := by
    intro hmem
    have h := (FoundKit.mem_found_iff_height hF).mp hmem
    have hf : rungAt F c.suit = rungAt F σ := rfl
    rw [hf] at h
    rw [hcidx] at h
    omega
  have hcG : c ∈ G.found c.suit := by
    apply (FoundKit.mem_found_iff_height hG).mpr
    rw [hcidx]
    have hg : rungAt G c.suit = rungAt G σ := rfl
    rw [hg]
    omega
  obtain ⟨a, hhold, hhid⟩ := hseat F G c hF hG hcls rfl hcF hcG
  have hnext : F.nextUp c = true := by
    unfold State.nextUp State.foundHeight
    rw [hcidx]
    have hlen : (F.found σ).length = 12 := by
      show rungAt F σ = 12
      exact h12
    rw [hlen]
    exact decide_eq_true rfl
  -- the top/covered dichotomy
  by_cases htop : lastOf (F.piles a).faceUp = some c
  · by_cases hchop : chop (F.piles a).faceUp = []
    · -- bare king
      have hpa : F.pileOfTop c = some a := (pileOfTop_eq_some_iff hF).2 htop
      have hcan : CanRaise F c := ⟨hnext, a, hpa, Or.inr ⟨hhid, rfl⟩⟩
      have hS : CanRaiseS F c := CanRaiseS.now c hcan
      rcases (hx.1 c).mpr hS with h | h
      · have hs : σ = x.suit := by rw [← h]
        exact hσ1 hs
      · have hs : σ = x.twin.suit := by rw [← h]
        exact hσ2 hs
    · -- chop nonempty: vanilla raisable
      have hpa : F.pileOfTop c = some a := (pileOfTop_eq_some_iff hF).2 htop
      have hcan : CanRaise F c := ⟨hnext, a, hpa, Or.inl hchop⟩
      have hS : CanRaiseS F c := CanRaiseS.now c hcan
      rcases (hx.1 c).mpr hS with h | h
      · have hs : σ = x.suit := by rw [← h]
        exact hσ1 hs
      · have hs : σ = x.twin.suit := by rw [← h]
        exact hσ2 hs
  · -- covered by the card directly above
    have hmem : c ∈ (F.piles a).faceUp := pileHolding_mem hhold
    obtain ⟨t, ht⟩ := fromCard_eq_head_of_mem hmem
    have htne : t ≠ [] := by
      intro hnil
      apply htop
      have h0 := tfc_below_fromCard c (F.piles a).faceUp
      rw [ht, hnil] at h0
      rw [← h0]
      exact lastOf_snoc
    obtain ⟨d, rest, hdrest⟩ := List.exists_cons_of_ne_nil htne
    rw [hdrest] at ht
    have hface : (F.piles a).faceUp = below c (F.piles a).faceUp ++ c :: d :: rest := by
      have h0 := tfc_below_fromCard c (F.piles a).faceUp
      rw [ht] at h0
      exact h0.symm
    have hrok : runOK (below c (F.piles a).faceUp ++ c :: d :: rest) = true := by
      rw [← hface]; exact hF.2.1 a
    have hfit : canSitOn d c = true :=
      SeedKit.runOK_adjacent_fit c d (below c (F.piles a).faceUp) rest hrok
    obtain ⟨hrank, hcol⟩ := (canSitOn_eq d c).mp hfit
    have hcolx : d.suit.color = x.suit.color :=
      SeedKit.color_pair (a := c.suit.color) (Ne.symm hcol) hσcol
    have hdlt : d.rank.toIdx < x.rank.toIdx := by
      have hc12 : c.rank.toIdx = 12 := hcidx
      have hx12 : x.rank.toIdx = 12 := by rw [hxk]; rfl
      omega
    have hdfound : d ∈ F.found d.suit := pair_lowFamily_founded hF hx hcolx hdlt
    have hdmem : d ∈ (F.piles a).faceUp := by rw [hface]; simp
    exact ((mem_found_unique hF hdfound).1 a).2 hdmem

/-- **THE FULL HIGH ROW, from the king-seated lemma.** -/
theorem forkThirdRigidHigh_of_kingSeated (hseat : KingExodusSeated) :
    ThirdRigid.ForkThirdRigidHigh :=
  forkThirdRigidHigh_of_nonKing_and_king (forkThirdRigidHighKing_of_seated hseat)

/-- **THE FULL THIRD-SUIT RESIDUE FROM THE KING PREMISE.** -/
theorem forkThirdRigid_of_kingSeated (hseat : KingExodusSeated) :
    ForkThirdRigid :=
  ThirdRigid.forkThirdRigid_of_high (forkThirdRigidHigh_of_kingSeated hseat)

/-! ## §8. `KingExodusSeated` — the premise, proved

The invariant is `KingKeep st c`: the king `c` is either founded, or it is
`.inl`-seated (the bottom of a pile) over a HIDDEN-FREE pile.

* A king never sits on a tableau card (`canSitOn_king_false`), so it never
  takes an `.inr` seat.
* Every landing / slide of a king is therefore an `.inl` landing on an
  EMPTY anchor (`king_base_inl`), whose pile the letter writes with
  `hidden := []`.
* `hidden` never grows (`rev_step_hidden_eq`).

So the invariant survives every reversible letter (`king_keep_step`), hence
every witness play (`king_keep_transit`), and the exodus pull of
`found_exodus` seeds it.
-/

/-- **`KingKeep st c`** — `c` is founded, or it bottoms a hidden-free pile. -/
def KingKeep (st : State) (c : Card) : Prop :=
  c ∈ st.found c.suit ∨ ∃ a, seatOf st c = some (Sum.inl a) ∧ (st.piles a).hidden = []

/-- **A king's `foundToTab` landing base is an empty anchor.** -/
theorem king_base_inl {st : State} {c : Card} {b : Base}
    (hk : c.rank = Rank.king) (hcp : st.canPlace c b = true) :
    ∃ a, b = Sum.inl a := by
  cases b with
  | inl a => exact ⟨a, rfl⟩
  | inr z =>
      exfalso
      obtain ⟨k, hpk, hfit⟩ := canPlace_inr hcp
      rw [canSitOn_king_false hk] at hfit
      exact Bool.noConfusion hfit

/-- **THE KING TRACE IS CLOSED UNDER EVERY REVERSIBLE STEP.** -/
theorem king_keep_step {st s1 : State} {m : Move} {c : Card}
    (hwf : st.WF) (hrev : reversibleAtW st m) (hstep : State.step st m = some s1)
    (hk : c.rank = Rank.king) (hcur : KingKeep st c) : KingKeep s1 c := by
  cases m with
  | draw =>
      have hse := (chart_draw hstep).1
      rcases hcur with hf | ⟨a, hseat, hhid⟩
      · left
        rw [stepDraw_found hstep]
        exact hf
      · right
        exact ⟨a, by rw [hse c, hseat],
          by rw [rev_step_hidden_eq hwf hstep hrev a]; exact hhid⟩
  | wasteToFound y => exact absurd hrev (wasteToFound_not_reversibleAtW st y)
  | wasteToTab y b => exact absurd hrev (wasteToTab_not_reversibleAtW st y b)
  | tabToFound d =>
      obtain ⟨-, a, hpa, hsV⟩ := step_tabToFound_inv hstep
      by_cases hcd : c = d
      · left
        rw [hsV]
        rw [hcd.symm, setFound_found_self]
        exact List.mem_append_right _ (List.mem_singleton_self c)
      · rcases hcur with hf | ⟨a', hseat, hhid⟩
        · left
          rw [hsV]
          by_cases hcs : c.suit = d.suit
          · rw [hcs.symm, setFound_found_self]
            exact List.mem_append_left _ hf
          · rw [setFound_found_ne hcs]
            exact hf
        · right
          refine ⟨a', ?_, ?_⟩
          · rw [raise_seat_change_of_seated hstep hrev (by rw [hseat]; simp) hcd]
            exact hseat
          · rw [rev_step_hidden_eq hwf hstep hrev a']
            exact hhid
  | foundToTab y b =>
      obtain ⟨c', htop, hc', hcp, hsV⟩ := step_foundToTab_inv hstep
      by_cases hcy : c = y
      · right
        subst hcy
        obtain ⟨t, rfl⟩ := king_base_inl hk hcp
        have hpile : s1.piles t = (⟨[], [c]⟩ : Pile) := by
          rw [hsV, putCard_piles_inl]
          simp
        have hwf1 : s1.WF := step_wf hwf hstep
        have hmem : c ∈ (s1.piles t).faceUp := by rw [hpile]; simp
        have hhold : s1.pileHolding c = some t := (pileHolding_eq_some_iff hwf1).2 hmem
        have hbelow : below c (s1.piles t).faceUp = [] := by rw [hpile, below_cons, ite_eq_left rfl]
        exact ⟨t, tfc_seatOf_inl_intro hhold hbelow, by rw [hpile]⟩
      · rcases hcur with hf | ⟨a, hseat, hhid⟩
        · left
          rw [hsV, putCard_found]
          by_cases hcs : c.suit = y.suit
          · have htop' : st.foundTop c.suit = some y := by
              rw [hcs, htop, hc']
            have hsnoc : st.found c.suit = chop (st.found c.suit) ++ [y] :=
              lastOf_chop htop'
            rw [hcs.symm, setFound_found_self]
            rw [hsnoc] at hf
            rcases List.mem_append.mp hf with h | h
            · exact h
            · exact absurd (List.mem_singleton.mp h) hcy
          · rw [setFound_found_ne hcs]
            exact hf
        · right
          refine ⟨a, ?_, ?_⟩
          · rw [pull_seat_change hstep c hcy]
            exact hseat
          · rw [rev_step_hidden_eq hwf hstep hrev a]
            exact hhid
  | tabToTab y b =>
      obtain ⟨a0, hhold, hcp, hrun, hsV⟩ := step_tabToTab_inv hstep
      rcases hcur with hf | ⟨a, hseat, hhid⟩
      · left
        rw [hsV, putRun_found, setPile_found]
        exact hf
      · right
        by_cases hcy : c = y
        · subst hcy
          obtain ⟨t, rfl⟩ := king_base_inl hk hcp
          refine ⟨t, ?_, ?_⟩
          · rw [tfc_seat_point_edit hwf hstep hrev c, ite_eq_left rfl]
          · rw [hsV, putRun_piles_inl_self]
        · refine ⟨a, ?_, ?_⟩
          · rw [tfc_seat_point_edit hwf hstep hrev c, ite_eq_right hcy]
            exact hseat
          · rw [rev_step_hidden_eq hwf hstep hrev a]
            exact hhid

/-- **THE KING TRACE SURVIVES A WITNESS PLAY.** -/
theorem king_keep_transit {A B : State} {ρ : List Move} (h : ShufflePlayW A ρ B)
    (hwf : A.WF) {c : Card} (hk : c.rank = Rank.king) (hcur : KingKeep A c) :
    KingKeep B c := by
  revert hwf hcur
  induction h with
  | nil st => intro _ h; exact h
  | @cons st s1 W m ρ' hrev hstep hrest ih =>
      intro hwf hcur
      exact ih (step_wf hwf hstep) (king_keep_step hwf hrev hstep hk hcur)

/-- **SPLIT A WALK AT A LETTER.** -/
theorem walk_split {A B : State} {ρ : List Move} (h : ShufflePlayW A ρ B)
    {c : Card} {b : Base} (hm : Move.foundToTab c b ∈ ρ) :
    ∃ (U U' : State) (l₁ l₂ : List Move),
      ShufflePlayW A l₁ U ∧ U.step (Move.foundToTab c b) = some U' ∧
        ShufflePlayW U' l₂ B ∧ ρ = l₁ ++ Move.foundToTab c b :: l₂ := by
  induction h with
  | nil st => exact absurd hm (by simp)
  | @cons st s1 W m ρ' hrev hstep hrest ih =>
      by_cases hmeq : m = Move.foundToTab c b
      · subst hmeq
        exact ⟨st, s1, [], ρ', .nil st, hstep, hrest, rfl⟩
      · have hm' : Move.foundToTab c b ∈ ρ' := by
          rcases List.mem_cons.mp hm with h' | h'
          · exact (hmeq h'.symm).elim
          · exact h'
        obtain ⟨U, U', l₁, l₂, h1, h2, h3, h4⟩ := ih hm'
        exact ⟨U, U', m :: l₁, l₂, .cons hrev hstep h1, h2, h3, by rw [h4]; rfl⟩

/-- **`KingExodusSeated` — PROVED.**  A king founded at the deep end of a
witness class and unfounded at the shallow one bottoms a hidden-free pile
at the shallow end.

Route: the exodus pull (`found_exodus`) hands the king to an empty anchor
(`canPlace_inl`); from there `KingKeep` rides every letter to the shallow
fork (`king_keep_transit`), and the unfoundedness at that end removes the
`found` arm. -/
theorem kingExodusSeated_proved : KingExodusSeated := by
  intro F G c hF hG hcls hk hcF hcG
  obtain ⟨play, hplay, -⟩ := hcls
  obtain ⟨b, hb⟩ := found_exodus hplay hcG hcF
  obtain ⟨U, U', l₁, l₂, h₁, hstep, h₂, hsplit⟩ := walk_split hplay hb
  obtain ⟨c', htop, hc', hcp, hsV⟩ := step_foundToTab_inv hstep
  obtain ⟨a, rfl⟩ := king_base_inl hk hcp
  have hpile : U'.piles a = (⟨[], [c]⟩ : Pile) := by
    rw [hsV, putCard_piles_inl]
    simp
  have hwfU : U.WF := wf_of_shuffle h₁ hG
  have hwfU' : U'.WF := step_wf hwfU hstep
  have hcur : KingKeep U' c := by
    right
    have hmem : c ∈ (U'.piles a).faceUp := by rw [hpile]; simp
    have hhold : U'.pileHolding c = some a := (pileHolding_eq_some_iff hwfU').2 hmem
    have hbelow : below c (U'.piles a).faceUp = [] := by rw [hpile, below_cons, ite_eq_left rfl]
    exact ⟨a, tfc_seatOf_inl_intro hhold hbelow, by rw [hpile]⟩
  have hfin : KingKeep F c := king_keep_transit h₂ hwfU' hk hcur
  rcases hfin with hf | ⟨a', hseat, hhid⟩
  · exact absurd hf hcF
  · obtain ⟨hhold, -⟩ := tfc_seatOf_of_inl hseat
    exact ⟨a', hhold, hhid⟩

/-- **`ForkThirdRigidHigh` — UNCONDITIONAL.** -/
theorem forkThirdRigidHigh_unconditional : ThirdRigid.ForkThirdRigidHigh :=
  forkThirdRigidHigh_of_kingSeated kingExodusSeated_proved

/-- **`ForkThirdRigid` — UNCONDITIONAL.** -/
theorem forkThirdRigid_unconditional : ForkThirdRigid :=
  forkThirdRigid_of_kingSeated kingExodusSeated_proved

/-- **`ForkPositionRigid` — UNCONDITIONAL.** -/
theorem forkPositionRigid_unconditional : ForkPositionRigid :=
  forkPositionRigid_of_third forkThirdRigid_unconditional

/-! ## §9. The unconditional `Position` consequences -/

/-- **`ForkFoundRigid` — UNCONDITIONAL.** -/
theorem forkFoundRigid_unconditional : ForkFoundRigid :=
  forkFoundRigid_iff_forkPositionRigid.mpr forkPositionRigid_unconditional

/-- **A fork class carries AT MOST ONE fork `Position`.**  All its fork
states present the same grid vertex. -/
theorem fork_one_position {F G : State} (x y : Card) (hF : F.WF) (hG : G.WF)
    (hcls : sameOrbitSetoid.r F G) (hx : ForkWitness F x) (hy : ForkWitness G y) :
    (Quotient.mk orbitRungSetoid ⟨F, hF⟩ : Position) =
      Quotient.mk orbitRungSetoid ⟨G, hG⟩ :=
  fork_one_position_of_rigid forkPositionRigid_unconditional x y hF hG hcls hx hy


#print axioms ThirdHigh.below_append_cons_notmem
#print axioms ThirdHigh.under_cards_ne
#print axioms ThirdHigh.third_rung_le_succ
#print axioms ThirdHigh.pull_landing_supported
#print axioms ThirdHigh.found_or_supported_step
#print axioms ThirdHigh.supported_of_forked_transit
#print axioms ThirdHigh.no_supported_nextUp_third
#print axioms ThirdHigh.high_false_of_lt
#print axioms ThirdHigh.forkThirdRigidHigh_of_not_king
#print axioms ThirdHigh.forkThirdRigidHigh_of_nonKing_and_king
#print axioms ThirdHigh.forkThirdRigidHighKing_of_seated
#print axioms ThirdHigh.forkThirdRigidHigh_of_kingSeated
#print axioms ThirdHigh.forkThirdRigid_of_kingSeated
#print axioms ThirdHigh.king_base_inl
#print axioms ThirdHigh.king_keep_step
#print axioms ThirdHigh.king_keep_transit
#print axioms ThirdHigh.walk_split
#print axioms ThirdHigh.kingExodusSeated_proved
#print axioms ThirdHigh.forkThirdRigidHigh_unconditional
#print axioms ThirdHigh.forkThirdRigid_unconditional
#print axioms ThirdHigh.forkPositionRigid_unconditional
#print axioms ThirdHigh.forkFoundRigid_unconditional
#print axioms ThirdHigh.fork_one_position

end ThirdHigh