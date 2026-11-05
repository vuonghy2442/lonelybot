import Orig2.Fork.Class.RungLeRaise
import Orig2.Fiber.FreeOrbit

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/Fork/Class/RungLeRaiseClose — closing `MinCardFree`

The static seat-shortage proof of the minimal-card run-or-twin lemma.
This card builds the closing rows for `RungLeRaise.MinCardFree`.
-/

namespace OneColourClosure

/-! ## §0. The zone census (private restatements) -/

/-- Every card sits in some zone. -/
private theorem rl_mem_zones_of_wf {st : State} (hwf : st.WF) (c : Card) :
    c ∈ st.zones.flatMap id := by
  have h1 : st.cardCount c = 1 := hwf.2.2.1 c (Card.mem_universe c)
  unfold State.cardCount at h1
  cases hf : ((st.zones.flatMap id).filter fun x => decide (x = c)) with
  | nil => rw [hf] at h1; simp at h1
  | cons x t =>
      have hx : x ∈ ((st.zones.flatMap id).filter fun x => decide (x = c)) := by
        rw [hf]; exact List.mem_cons_self ..
      obtain ⟨hm, hxc⟩ := List.mem_filter.mp hx
      rw [← of_decide_eq_true hxc]
      exact hm

/-- A card that is nowhere face-up is founded, hidden, or in the pool. -/
private theorem rl_zone_notFaceUp {st : State} (hwf : st.WF) {c : Card}
    (h : ¬ ∃ a, c ∈ (st.piles a).faceUp) :
    (∃ σ, c ∈ st.found σ) ∨ (∃ a, c ∈ (st.piles a).hidden) ∨
      (c ∈ st.stock ∨ c ∈ st.waste) := by
  obtain ⟨zs, hzs, hczs⟩ := List.mem_flatMap.mp (rl_mem_zones_of_wf hwf c)
  rcases List.mem_append.mp hzs with h1 | h1
  · rcases List.mem_append.mp h1 with h2 | h2
    · obtain ⟨σ, -, hzeq⟩ := List.mem_map.mp h2
      rw [← hzeq] at hczs
      exact Or.inl ⟨σ, hczs⟩
    · obtain ⟨a, -, hzeq⟩ := List.mem_map.mp h2
      rw [← hzeq] at hczs
      rcases List.mem_append.mp hczs with hmem | hmem
      · exact Or.inr (Or.inl ⟨a, hmem⟩)
      · exact absurd ⟨a, hmem⟩ h
  · rcases List.mem_cons.mp h1 with rfl | h1
    · exact Or.inr (Or.inr (Or.inl hczs))
    · rcases List.mem_cons.mp h1 with rfl | h1
      · exact Or.inr (Or.inr (Or.inr hczs))
      · exact absurd h1 (List.not_mem_nil)

/-- A founded card's suit is the foundation's suit. -/
private theorem rl_suit_eq_of_mem_found {st : State} (hwf : st.WF) {c : Card} {σ : Suit}
    (hmem : c ∈ st.found σ) : c.suit = σ := by
  obtain ⟨n, hn⟩ := hwf.found_prefix σ
  rw [hn] at hmem
  have hmem' : c ∈ σ.upCards := List.mem_of_mem_take hmem
  obtain ⟨r, -, hr⟩ := List.mem_map.mp hmem'
  rw [← hr]

/-- Constructive zone decomposition: a card in no foundation, no hidden deck
and not in the pool is face-up somewhere. -/
private theorem rl_zone_faceUp {st : State} (hwf : st.WF) {c : Card}
    (hnf : ∀ σ, c ∉ st.found σ)
    (hnh : ∀ a, c ∉ (st.piles a).hidden)
    (hns : c ∉ st.stock) (hnw : c ∉ st.waste) :
    ∃ a, c ∈ (st.piles a).faceUp := by
  obtain ⟨zs, hzs, hczs⟩ := List.mem_flatMap.mp (rl_mem_zones_of_wf hwf c)
  rcases List.mem_append.mp hzs with h1 | h1
  · rcases List.mem_append.mp h1 with h2 | h2
    · obtain ⟨σ, -, hzeq⟩ := List.mem_map.mp h2
      rw [← hzeq] at hczs
      exact absurd hczs (hnf σ)
    · obtain ⟨a, -, hzeq⟩ := List.mem_map.mp h2
      rw [← hzeq] at hczs
      rcases List.mem_append.mp hczs with hmem | hmem
      · exact absurd hmem (hnh a)
      · exact ⟨a, hmem⟩
  · rcases List.mem_cons.mp h1 with rfl | h1
    · exact absurd hczs hns
    · rcases List.mem_cons.mp h1 with rfl | h1
      · exact absurd hczs hnw
      · exact absurd h1 (List.not_mem_nil)

/-- Constructive four-way zone decomposition. -/
private theorem rl_zone_cases {st : State} (hwf : st.WF) (c : Card) :
    (∃ σ, c ∈ st.found σ) ∨ (∃ a, c ∈ (st.piles a).hidden) ∨
      (c ∈ st.stock ∨ c ∈ st.waste) ∨ (∃ a, c ∈ (st.piles a).faceUp) := by
  obtain ⟨zs, hzs, hczs⟩ := List.mem_flatMap.mp (rl_mem_zones_of_wf hwf c)
  rcases List.mem_append.mp hzs with h1 | h1
  · rcases List.mem_append.mp h1 with h2 | h2
    · obtain ⟨σ, -, hzeq⟩ := List.mem_map.mp h2
      rw [← hzeq] at hczs
      exact Or.inl ⟨σ, hczs⟩
    · obtain ⟨a, -, hzeq⟩ := List.mem_map.mp h2
      rw [← hzeq] at hczs
      rcases List.mem_append.mp hczs with hmem | hmem
      · exact Or.inr (Or.inl ⟨a, hmem⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨a, hmem⟩))
  · rcases List.mem_cons.mp h1 with rfl | h1
    · exact Or.inr (Or.inr (Or.inl (Or.inl hczs)))
    · rcases List.mem_cons.mp h1 with rfl | h1
      · exact Or.inr (Or.inr (Or.inl (Or.inr hczs)))
      · exact absurd h1 (List.not_mem_nil)

/-! ## §1. `c` is face-up -/

/-- The deficient next-up card of a suit is face-up at `u`. -/
theorem minCard_faceUp {u v : State} {c : Card}
    (hu : u.WF) (horb : sameOrbitSetoid.r u v)
    (hfix : c.rank.toIdx = rungAt u c.suit)
    (hdef : rungAt u c.suit < rungAt v c.suit) :
    ∃ a, c ∈ (u.piles a).faceUp := by
  have horb' := horb
  obtain ⟨_, _, τ, hτ⟩ := horb
  have hv : v.WF := walk_wf hu hτ
  have hcfv : c ∈ v.found c.suit :=
    FoundKit.mem_found_of_rung hv (by rw [hfix]; exact hdef)
  have hfuniq := mem_found_unique hv hcfv
  have hhidden := walk_hidden_eq hu hτ
  have hpool := walk_pool_rev hτ
  have hnotfound : c ∉ u.found c.suit := by
    intro hmem
    have hlt := (FoundKit.mem_found_iff_height hu).mp hmem
    rw [hfix] at hlt
    exact Nat.lt_irrefl _ hlt
  have hnothidden : ∀ a, c ∉ (u.piles a).hidden := by
    intro a hmem
    have hmemv : c ∈ (v.piles a).hidden := by rw [hhidden a]; exact hmem
    exact ((hfuniq.1 a).1) hmemv
  have hnotstock : c ∉ u.stock := by
    intro hmem
    rcases hpool c (Or.inl hmem) with h | h
    · exact hfuniq.2.1 h
    · exact hfuniq.2.2.1 h
  have hnotwaste : c ∉ u.waste := by
    intro hmem
    rcases hpool c (Or.inr hmem) with h | h
    · exact hfuniq.2.1 h
    · exact hfuniq.2.2.1 h
  have hnotfound_all : ∀ σ, c ∉ u.found σ := by
    intro σ hmem
    have hσ : c.suit = σ := rl_suit_eq_of_mem_found hu hmem
    rw [← hσ] at hmem
    exact hnotfound hmem
  exact rl_zone_faceUp hu hnotfound_all hnothidden hnotstock hnotwaste

/-! ## §2. The cover rows -/

/-- If `y` sits directly on `c`, the below-part of `y` ends in `c`. -/
private theorem rl_below_succ_of_fromCard {l : List Card} {c e : Card} {rest : List Card}
    (hnd : l.Nodup) (h : fromCard c l = c :: e :: rest) :
    below e l = below c l ++ [c] := by
  have hsplit : below c l ++ c :: e :: rest = l := by
    have h0 := tfc_below_fromCard c l
    rw [h] at h0
    exact h0
  have hnd' : (below c l ++ c :: e :: rest).Nodup := by
    rw [hsplit]; exact hnd
  have hnot : e ∉ below c l := by
    intro hmem
    exact (((List.nodup_append.1 hnd').2.2 e hmem) e
      (List.mem_cons_of_mem c (List.mem_cons_self ..))) rfl
  have htail : (c :: e :: rest).Nodup := (List.nodup_append.1 hnd').2.1
  have hcnot : c ∉ e :: rest := (List.nodup_cons.1 htail).1
  have hcne : c ≠ e := fun hce =>
    hcnot (by rw [hce]; exact List.mem_cons_self ..)
  have hstep : below e (c :: e :: rest) = [c] := by
    show (if c = e then [] else c :: below e (e :: rest)) = [c]
    rw [ite_eq_right hcne]
    show c :: (if e = e then [] else e :: below e rest) = [c]
    rw [ite_eq_left rfl]
  calc below e l = below e (below c l ++ c :: e :: rest) := by rw [hsplit]
    _ = below c l ++ below e (c :: e :: rest) := below_append_notmem hnot _
    _ = below c l ++ [c] := by rw [hstep]

/-- A cover of the minimal deficient card lives in a non-deficient suit. -/
theorem cover_suit_nonDeficient {u v : State} {c y : Card}
    (hyc : canSitOn y c = true)
    (hfix : c.rank.toIdx = rungAt u c.suit)
    (hmin : ∀ τ : Suit, rungAt u τ < rungAt v τ → rungAt u c.suit ≤ rungAt u τ)
    (hyface : rungAt u y.suit ≤ y.rank.toIdx) :
    ¬ (rungAt u y.suit < rungAt v y.suit) := by
  intro hdefy
  have hle := hmin y.suit hdefy
  have hrank : y.rank.toIdx + 1 = c.rank.toIdx := ((canSitOn_eq y c).mp hyc).1
  omega

/-- A cover of the minimal deficient card is face-up at `v`. -/
theorem cover_faceUp_at_v {u v : State} {y : Card}
    (hu : u.WF) (horb : sameOrbitSetoid.r u v) (hle : RungLe u v)
    (hnotdef : ¬ (rungAt u y.suit < rungAt v y.suit))
    (hyu : ∃ a, y ∈ (u.piles a).faceUp) :
    ∃ a, y ∈ (v.piles a).faceUp := by
  obtain ⟨τrev, hτrev, τ, hτ⟩ := horb
  have hv : v.WF := walk_wf hu hτ
  have hrunge : rungAt v y.suit = rungAt u y.suit := by
    have h := hle y.suit
    omega
  obtain ⟨a0, hfaceu⟩ := hyu
  have hpile := mem_pile_unique hu (Or.inr hfaceu)
  have hhidden := walk_hidden_eq hu hτ
  have hpoolrev := walk_pool_rev hτrev
  have hnotfound_v : y ∉ v.found y.suit := by
    intro hmem
    have hlt := (FoundKit.mem_found_iff_height hv).mp hmem
    rw [hrunge] at hlt
    have hltu : y.rank.toIdx < rungAt u y.suit := hlt
    have hmemu2 : y ∈ u.found y.suit := FoundKit.mem_found_of_rung hu hltu
    exact ((mem_found_unique hu hmemu2).1 a0).2 hfaceu
  have hnothidden_v : ∀ a, y ∉ (v.piles a).hidden := by
    intro a hmem
    have hmemh : y ∈ (u.piles a).hidden := by rw [← hhidden a]; exact hmem
    by_cases ha : a = a0
    · subst ha
      exact (mem_faceUp_not_hidden hu hfaceu) hmemh
    · exact (hpile.1 a ha).1 hmemh
  have hnotstock : y ∉ v.stock := by
    intro hmem
    rcases hpoolrev y (Or.inl hmem) with h | h
    · exact hpile.2.1 h
    · exact hpile.2.2.1 h
  have hnotwaste : y ∉ v.waste := by
    intro hmem
    rcases hpoolrev y (Or.inr hmem) with h | h
    · exact hpile.2.1 h
    · exact hpile.2.2.1 h
  have hnotfound_all : ∀ σ, y ∉ v.found σ := by
    intro σ hmem
    have hσ : y.suit = σ := rl_suit_eq_of_mem_found hv hmem
    rw [← hσ] at hmem
    exact hnotfound_v hmem
  exact rl_zone_faceUp hv hnotfound_all hnothidden_v hnotstock hnotwaste

/-- The cover `y` of `c` ends up sitting on `c.twin` at `v`. -/
theorem cover_parent_twin {u v : State} {c y : Card} {a : Anchor} {rest : List Card}
    (hu : u.WF) (horb : sameOrbitSetoid.r u v) (hle : RungLe u v)
    (hfix : c.rank.toIdx = rungAt u c.suit)
    (hdef : rungAt u c.suit < rungAt v c.suit)
    (hmin : ∀ τ : Suit, rungAt u τ < rungAt v τ → rungAt u c.suit ≤ rungAt u τ)
    (hfacec : c ∈ (u.piles a).faceUp)
    (hfc : fromCard c (u.piles a).faceUp = c :: y :: rest) :
    seatOf v y = some (Sum.inr c.twin) := by
  have horb' := horb
  obtain ⟨_, _, τ, hτ⟩ := horb
  have hv : v.WF := walk_wf hu hτ
  have hrok : runOK (u.piles a).faceUp = true := hu.2.1 a
  have hbelow : below c (u.piles a).faceUp ++ (c :: y :: rest) = (u.piles a).faceUp := by
    have h0 := tfc_below_fromCard c (u.piles a).faceUp
    rw [hfc] at h0
    exact h0
  have hyc : canSitOn y c = true :=
    SeedKit.runOK_adjacent_fit c y (below c (u.piles a).faceUp) rest
      (by rw [hbelow]; exact hrok)
  have hyface : y ∈ (u.piles a).faceUp := by
    rw [← hbelow]
    exact List.mem_append.mpr
      (Or.inr (List.mem_cons_of_mem c (List.mem_cons_self ..)))
  have hyrank : rungAt u y.suit ≤ y.rank.toIdx := by
    apply Nat.le_of_not_lt
    intro hlt
    have hf : y ∈ u.found y.suit := FoundKit.mem_found_of_rung hu hlt
    exact ((mem_found_unique hu hf).1 a).2 hyface
  have hnotdef : ¬ (rungAt u y.suit < rungAt v y.suit) :=
    cover_suit_nonDeficient hyc hfix hmin hyrank
  have hyfacev : ∃ a', y ∈ (v.piles a').faceUp :=
    cover_faceUp_at_v hu horb' hle hnotdef ⟨a, hyface⟩
  have hrank : y.rank.toIdx + 1 = c.rank.toIdx := ((canSitOn_eq y c).mp hyc).1
  have hrv : rungAt v c.suit ≤ 13 := rungAt_le13 hv c.suit
  have hyng : y.rank ≠ Rank.king := by
    intro hk
    have h12 : y.rank.toIdx = 12 := by rw [hk]; rfl
    omega
  have hhold_y : u.pileHolding y = some a :=
    (pileHolding_eq_some_iff hu).2 hyface
  have hnd : (u.piles a).faceUp.Nodup := runOK_nodup hrok
  have hbelow_y : below y (u.piles a).faceUp = below c (u.piles a).faceUp ++ [c] :=
    rl_below_succ_of_fromCard hnd hfc
  have hlast_y : lastOf (below y (u.piles a).faceUp) = some c := by
    rw [hbelow_y]; exact lastOf_snoc
  have hseat_y : seatOf u y = some (Sum.inr c) :=
    tfc_seatOf_inr_intro hhold_y hlast_y
  have hpar_v : Parented v y :=
    walk_parented hu hτ y hyng hyfacev (Or.inr ⟨c, hseat_y⟩)
  obtain ⟨z, hseatv⟩ := hpar_v
  obtain ⟨a', hhold_yv, _hbelowne, hlast_z⟩ := tfc_seatOf_of_inr hseatv
  have hzfit : canSitOn y z = true := (tfc_seat_parent hv hhold_yv hlast_z).1
  have hzt : z = c ∨ z = c.twin := canSitOn_twin_pair hyc hzfit
  have hcfv : c ∈ v.found c.suit :=
    FoundKit.mem_found_of_rung hv (by rw [hfix]; exact hdef)
  have hfuniq := mem_found_unique hv hcfv
  have hzc : z = c.twin := by
    rcases hzt with h | h
    · exfalso
      have hmemz : z ∈ below y (v.piles a').faceUp := lastOf_mem hlast_z
      have hin : c ∈ (v.piles a').faceUp := by
        rw [h] at hmemz
        exact mem_below (v.piles a').faceUp hmemz
      exact ((hfuniq.1 a').2) hin
    · exact h
  rw [hzc] at hseatv
  exact hseatv

/-! ## §3. The generic (`d`-rank) cover lemma -/

/-- Generalized non-deficiency: a cover of a rank-`r` card lives in a
non-deficient suit, where `r` is the minimal deficient rung. -/
theorem cover_suit_nonDeficient' {u v : State} {d y : Card} {r : Nat}
    (hyd : canSitOn y d = true)
    (hd : d.rank.toIdx = r)
    (hmin : ∀ τ : Suit, rungAt u τ < rungAt v τ → r ≤ rungAt u τ)
    (hyface : rungAt u y.suit ≤ y.rank.toIdx) :
    ¬ (rungAt u y.suit < rungAt v y.suit) := by
  intro hdefy
  have hle := hmin y.suit hdefy
  have hrank : y.rank.toIdx + 1 = d.rank.toIdx := ((canSitOn_eq y d).mp hyd).1
  omega

/-- **THE COVER LEMMA, `d`-FOUNDED BRANCH.**  If `d` itself is founded at
`v`, its cover `y` sits on `d.twin` at `v`. -/
theorem cover_parent_of_founded {u v : State} {d y : Card} {a : Anchor} {rest : List Card}
    {r : Nat}
    (hu : u.WF) (horb : sameOrbitSetoid.r u v) (hle : RungLe u v)
    (hd : d.rank.toIdx = r) (hr13 : r < 13)
    (hmin : ∀ τ : Suit, rungAt u τ < rungAt v τ → r ≤ rungAt u τ)
    (hface : d ∈ (u.piles a).faceUp)
    (hfc : fromCard d (u.piles a).faceUp = d :: y :: rest)
    (hfound : d ∈ v.found d.suit) :
    seatOf v y = some (Sum.inr d.twin) := by
  have horb' := horb
  obtain ⟨_, _, τ, hτ⟩ := horb
  have hv : v.WF := walk_wf hu hτ
  have hrok : runOK (u.piles a).faceUp = true := hu.2.1 a
  have hbelow : below d (u.piles a).faceUp ++ (d :: y :: rest) = (u.piles a).faceUp := by
    have h0 := tfc_below_fromCard d (u.piles a).faceUp
    rw [hfc] at h0
    exact h0
  have hyd : canSitOn y d = true :=
    SeedKit.runOK_adjacent_fit d y (below d (u.piles a).faceUp) rest
      (by rw [hbelow]; exact hrok)
  have hyface : y ∈ (u.piles a).faceUp := by
    rw [← hbelow]
    exact List.mem_append.mpr
      (Or.inr (List.mem_cons_of_mem d (List.mem_cons_self ..)))
  have hyrank : rungAt u y.suit ≤ y.rank.toIdx := by
    apply Nat.le_of_not_lt
    intro hlt
    have hf : y ∈ u.found y.suit := FoundKit.mem_found_of_rung hu hlt
    exact ((mem_found_unique hu hf).1 a).2 hyface
  have hnotdef : ¬ (rungAt u y.suit < rungAt v y.suit) :=
    cover_suit_nonDeficient' hyd hd hmin hyrank
  have hyfacev : ∃ a', y ∈ (v.piles a').faceUp :=
    cover_faceUp_at_v hu horb' hle hnotdef ⟨a, hyface⟩
  have hrank : y.rank.toIdx + 1 = d.rank.toIdx := ((canSitOn_eq y d).mp hyd).1
  have hyng : y.rank ≠ Rank.king := by
    intro hk
    have h12 : y.rank.toIdx = 12 := by rw [hk]; rfl
    omega
  have hhold_y : u.pileHolding y = some a :=
    (pileHolding_eq_some_iff hu).2 hyface
  have hnd : (u.piles a).faceUp.Nodup := runOK_nodup hrok
  have hbelow_y : below y (u.piles a).faceUp = below d (u.piles a).faceUp ++ [d] :=
    rl_below_succ_of_fromCard hnd hfc
  have hlast_y : lastOf (below y (u.piles a).faceUp) = some d := by
    rw [hbelow_y]; exact lastOf_snoc
  have hseat_y : seatOf u y = some (Sum.inr d) :=
    tfc_seatOf_inr_intro hhold_y hlast_y
  have hpar_v : Parented v y :=
    walk_parented hu hτ y hyng hyfacev (Or.inr ⟨d, hseat_y⟩)
  obtain ⟨z, hseatv⟩ := hpar_v
  obtain ⟨a', hhold_yv, _hbelowne, hlast_z⟩ := tfc_seatOf_of_inr hseatv
  have hzfit : canSitOn y z = true := (tfc_seat_parent hv hhold_yv hlast_z).1
  have hzt : z = d ∨ z = d.twin := canSitOn_twin_pair hyd hzfit
  have hfuniq := mem_found_unique hv hfound
  have hzc : z = d.twin := by
    rcases hzt with h | h
    · exfalso
      have hmemz : z ∈ below y (v.piles a').faceUp := lastOf_mem hlast_z
      have hin : d ∈ (v.piles a').faceUp := by
        rw [h] at hmemz
        exact mem_below (v.piles a').faceUp hmemz
      exact ((hfuniq.1 a').2) hin
    · exact h
  rw [hzc] at hseatv
  exact hseatv

/-- **THE COVER LEMMA, `d.twin`-FOUNDED BRANCH.**  If `d.twin` is founded
at `v`, the cover `y` of `d` sits on `d` itself at `v`. -/
theorem cover_parent_of_twinFounded {u v : State} {d y : Card} {a : Anchor} {rest : List Card}
    {r : Nat}
    (hu : u.WF) (horb : sameOrbitSetoid.r u v) (hle : RungLe u v)
    (hd : d.rank.toIdx = r) (hr13 : r < 13)
    (hmin : ∀ τ : Suit, rungAt u τ < rungAt v τ → r ≤ rungAt u τ)
    (hface : d ∈ (u.piles a).faceUp)
    (hfc : fromCard d (u.piles a).faceUp = d :: y :: rest)
    (hfound : d.twin ∈ v.found d.twin.suit) :
    seatOf v y = some (Sum.inr d) := by
  have horb' := horb
  obtain ⟨_, _, τ, hτ⟩ := horb
  have hv : v.WF := walk_wf hu hτ
  have hrok : runOK (u.piles a).faceUp = true := hu.2.1 a
  have hbelow : below d (u.piles a).faceUp ++ (d :: y :: rest) = (u.piles a).faceUp := by
    have h0 := tfc_below_fromCard d (u.piles a).faceUp
    rw [hfc] at h0
    exact h0
  have hyd : canSitOn y d = true :=
    SeedKit.runOK_adjacent_fit d y (below d (u.piles a).faceUp) rest
      (by rw [hbelow]; exact hrok)
  have hyface : y ∈ (u.piles a).faceUp := by
    rw [← hbelow]
    exact List.mem_append.mpr
      (Or.inr (List.mem_cons_of_mem d (List.mem_cons_self ..)))
  have hyrank : rungAt u y.suit ≤ y.rank.toIdx := by
    apply Nat.le_of_not_lt
    intro hlt
    have hf : y ∈ u.found y.suit := FoundKit.mem_found_of_rung hu hlt
    exact ((mem_found_unique hu hf).1 a).2 hyface
  have hnotdef : ¬ (rungAt u y.suit < rungAt v y.suit) :=
    cover_suit_nonDeficient' hyd hd hmin hyrank
  have hyfacev : ∃ a', y ∈ (v.piles a').faceUp :=
    cover_faceUp_at_v hu horb' hle hnotdef ⟨a, hyface⟩
  have hrank : y.rank.toIdx + 1 = d.rank.toIdx := ((canSitOn_eq y d).mp hyd).1
  have hyng : y.rank ≠ Rank.king := by
    intro hk
    have h12 : y.rank.toIdx = 12 := by rw [hk]; rfl
    omega
  have hhold_y : u.pileHolding y = some a :=
    (pileHolding_eq_some_iff hu).2 hyface
  have hnd : (u.piles a).faceUp.Nodup := runOK_nodup hrok
  have hbelow_y : below y (u.piles a).faceUp = below d (u.piles a).faceUp ++ [d] :=
    rl_below_succ_of_fromCard hnd hfc
  have hlast_y : lastOf (below y (u.piles a).faceUp) = some d := by
    rw [hbelow_y]; exact lastOf_snoc
  have hseat_y : seatOf u y = some (Sum.inr d) :=
    tfc_seatOf_inr_intro hhold_y hlast_y
  have hpar_v : Parented v y :=
    walk_parented hu hτ y hyng hyfacev (Or.inr ⟨d, hseat_y⟩)
  obtain ⟨z, hseatv⟩ := hpar_v
  obtain ⟨a', hhold_yv, _hbelowne, hlast_z⟩ := tfc_seatOf_of_inr hseatv
  have hzfit : canSitOn y z = true := (tfc_seat_parent hv hhold_yv hlast_z).1
  have hzt : z = d ∨ z = d.twin := canSitOn_twin_pair hyd hzfit
  have hfuniq := mem_found_unique hv hfound
  have hzc : z = d := by
    rcases hzt with h | h
    · exact h
    · exfalso
      have hmemz : z ∈ below y (v.piles a').faceUp := lastOf_mem hlast_z
      have hin : d.twin ∈ (v.piles a').faceUp := by
        rw [h] at hmemz
        exact mem_below (v.piles a').faceUp hmemz
      exact ((hfuniq.1 a').2) hin
  rw [hzc] at hseatv
  exact hseatv

/-- **CASE A — THE DOUBLE-COVER CONTRADICTION.**  If both `c` and `c.twin`
are covered at `u` (by `y` and `y'`), and `c` is founded at `v`, then the
two covers both end up on `c.twin` at `v`, contradicting
`seat_inr_inj`. -/
theorem double_cover_false {u v : State} {c y y' : Card}
    {a a' : Anchor} {rest rest' : List Card} {r : Nat}
    (hu : u.WF) (horb : sameOrbitSetoid.r u v) (hle : RungLe u v)
    (hcrank : c.rank.toIdx = r) (hr13 : r < 13)
    (hmin : ∀ τ : Suit, rungAt u τ < rungAt v τ → r ≤ rungAt u τ)
    (hc_found : c ∈ v.found c.suit)
    (hfacec : c ∈ (u.piles a).faceUp)
    (hfc : fromCard c (u.piles a).faceUp = c :: y :: rest)
    (hfacct : c.twin ∈ (u.piles a').faceUp)
    (hfc' : fromCard c.twin (u.piles a').faceUp = c.twin :: y' :: rest') :
    False := by
  have horb' := horb
  obtain ⟨_, _, τ, hτ⟩ := horb
  have hv : v.WF := walk_wf hu hτ
  -- both covers land on `c.twin`
  have hy : seatOf v y = some (Sum.inr c.twin) :=
    cover_parent_of_founded hu horb' hle hcrank hr13 hmin hfacec hfc hc_found
  have hctrank : (c.twin).rank.toIdx = r := by
    rw [Card.twin_rank]; exact hcrank
  have hctfound : (c.twin).twin ∈ v.found (c.twin).twin.suit := by
    rw [card_twin_twin]; exact hc_found
  have hy' : seatOf v y' = some (Sum.inr c.twin) :=
    cover_parent_of_twinFounded hu horb' hle hctrank hr13 hmin hfacct hfc' hctfound
  have hyeq : y = y' := seat_inr_inj hv hy hy'
  -- their seats at `u` are distinct
  have hyface : y ∈ (u.piles a).faceUp := by
    have hbold : below c (u.piles a).faceUp ++ (c :: y :: rest) = (u.piles a).faceUp := by
      have h0 := tfc_below_fromCard c (u.piles a).faceUp
      rw [hfc] at h0
      exact h0
    rw [← hbold]
    exact List.mem_append.mpr
      (Or.inr (List.mem_cons_of_mem c (List.mem_cons_self ..)))
  have hholdy : u.pileHolding y = some a := (pileHolding_eq_some_iff hu).2 hyface
  have hnd : (u.piles a).faceUp.Nodup := runOK_nodup (hu.2.1 a)
  have hlasty : lastOf (below y (u.piles a).faceUp) = some c := by
    rw [rl_below_succ_of_fromCard hnd hfc]; exact lastOf_snoc
  have hyu : seatOf u y = some (Sum.inr c) := tfc_seatOf_inr_intro hholdy hlasty
  have hy'face : y' ∈ (u.piles a').faceUp := by
    have hbold : below c.twin (u.piles a').faceUp ++ (c.twin :: y' :: rest') =
        (u.piles a').faceUp := by
      have h0 := tfc_below_fromCard c.twin (u.piles a').faceUp
      rw [hfc'] at h0
      exact h0
    rw [← hbold]
    exact List.mem_append.mpr
      (Or.inr (List.mem_cons_of_mem c.twin (List.mem_cons_self ..)))
  have hholdy' : u.pileHolding y' = some a' := (pileHolding_eq_some_iff hu).2 hy'face
  have hnd' : (u.piles a').faceUp.Nodup := runOK_nodup (hu.2.1 a')
  have hlasty' : lastOf (below y' (u.piles a').faceUp) = some c.twin := by
    rw [rl_below_succ_of_fromCard hnd' hfc']; exact lastOf_snoc
  have hy'u : seatOf u y' = some (Sum.inr c.twin) := tfc_seatOf_inr_intro hholdy' hlasty'
  rw [hyeq] at hyu
  have hEq : some (Sum.inr c) = some (Sum.inr c.twin) := hyu.symm.trans hy'u
  have hSum : Sum.inr c = (Sum.inr c.twin : Base) := Option.some.inj hEq
  have hc : c = c.twin := Sum.inr.inj hSum
  exact card_twin_ne c hc.symm

/-- **THE RUN-OR-TWIN ROW.**  For the minimal deficient next-up card `c`,
either `c` or `c.twin` tops a pile at `u`. -/
theorem minCard_top_or_twinTop {u v : State} {c : Card} {r : Nat}
    (hu : u.WF) (horb : sameOrbitSetoid.r u v) (hle : RungLe u v)
    (hfix : c.rank.toIdx = rungAt u c.suit)
    (hcrank : c.rank.toIdx = r)
    (hr13 : r < 13)
    (hdef : rungAt u c.suit < rungAt v c.suit)
    (hmin : ∀ τ : Suit, rungAt u τ < rungAt v τ → r ≤ rungAt u τ) :
    (∃ a, u.pileOfTop c = some a) ∨ (∃ a, u.pileOfTop c.twin = some a) := by
  have hv : v.WF := wf_of_sameOrbit horb hu
  have hc_found : c ∈ v.found c.suit :=
    FoundKit.mem_found_of_rung hv (by rw [hfix]; exact hdef)
  cases hctop : u.pileOfTop c with
  | some a => exact Or.inl ⟨a, rfl⟩
  | none =>
    cases httop : u.pileOfTop c.twin with
    | some a => exact Or.inr ⟨a, rfl⟩
    | none =>
      exfalso
      have horb' := horb
      obtain ⟨_, _, τ, hτ⟩ := horb'
      obtain ⟨a, hfacec⟩ := minCard_faceUp hu horb hfix hdef
      obtain ⟨t, hfct⟩ := fromCard_eq_head_of_mem hfacec
      have htne : t ≠ [] := by
        intro ht
        have hlast : lastOf (u.piles a).faceUp = some c := by
          have h0 := tfc_below_fromCard c (u.piles a).faceUp
          rw [hfct, ht] at h0
          rw [← h0]; exact lastOf_snoc
        have hsome : u.pileOfTop c = some a := (pileOfTop_eq_some_iff hu).2 hlast
        rw [hctop] at hsome
        exact absurd hsome (by simp)
      cases t with
      | nil => exact absurd rfl htne
      | cons y rest =>
        have hy : seatOf v y = some (Sum.inr c.twin) :=
          cover_parent_of_founded hu horb hle hcrank hr13 hmin hfacec hfct hc_found
        have hvface_ct : ∃ av, c.twin ∈ (v.piles av).faceUp := by
          obtain ⟨av, _, _, hlastv⟩ := tfc_seatOf_of_inr hy
          exact ⟨av, mem_below (v.piles av).faceUp (lastOf_mem hlastv)⟩
        rcases rl_zone_cases hu c.twin with
          ⟨σ, hmemf⟩ | ⟨ah, hmemh⟩ | hpool | ⟨a', hfacct⟩
        · -- c.twin founded at u
          have hσ : c.twin.suit = σ := rl_suit_eq_of_mem_found hu hmemf
          rw [← hσ] at hmemf
          have hlt := (FoundKit.mem_found_iff_height hu).mp hmemf
          have hltv : c.twin.rank.toIdx < rungAt v c.twin.suit := by
            have := hle c.twin.suit
            omega
          have hfv := FoundKit.mem_found_of_rung hv hltv
          obtain ⟨av, hvface⟩ := hvface_ct
          exact ((mem_found_unique hv hfv).1 av).2 hvface
        · -- c.twin hidden at u
          have hmemv : c.twin ∈ (v.piles ah).hidden := by
            rw [walk_hidden_eq hu hτ ah]
            exact hmemh
          obtain ⟨av, hvface⟩ := hvface_ct
          by_cases hav : av = ah
          · subst hav
            exact (mem_faceUp_not_hidden hv hvface) hmemv
          · exact (((mem_faceUp_unique hv hvface ah (fun h => hav h.symm)).2).1) hmemv
        · -- c.twin in the pool at u
          rcases hpool with hs | hw
          · have hpv := walk_pool_rev hτ c.twin (Or.inl hs)
            obtain ⟨av, hvface⟩ := hvface_ct
            rcases hpv with hs' | hw'
            · exact ((mem_stock_unique hv hs').1 av).2 hvface
            · exact ((mem_waste_unique hv hw').1 av).2 hvface
          · have hpv := walk_pool_rev hτ c.twin (Or.inr hw)
            obtain ⟨av, hvface⟩ := hvface_ct
            rcases hpv with hs' | hw'
            · exact ((mem_stock_unique hv hs').1 av).2 hvface
            · exact ((mem_waste_unique hv hw').1 av).2 hvface
        · -- c.twin face-up at u: covered (it is not a top), so Case A
          obtain ⟨t', hfct'⟩ := fromCard_eq_head_of_mem hfacct
          have htne' : t' ≠ [] := by
            intro ht
            have hlast : lastOf (u.piles a').faceUp = some c.twin := by
              have h0 := tfc_below_fromCard c.twin (u.piles a').faceUp
              rw [hfct', ht] at h0
              rw [← h0]; exact lastOf_snoc
            have hsome : u.pileOfTop c.twin = some a' := (pileOfTop_eq_some_iff hu).2 hlast
            rw [httop] at hsome
            exact absurd hsome (by simp)
          cases t' with
          | nil => exact absurd rfl htne'
          | cons y' rest' =>
            exact double_cover_false hu horb hle hcrank hr13 hmin hc_found
              hfacec hfct hfacct hfct'

/-! ## §4. The final reduction to the licence residual -/

/-- **THE LICENCE RESIDUAL.**  For the minimal deficient card, the
`freeCardS` seat condition holds: it is either parented (non-king) or a
bare king.  This is exactly the bare-non-king-bottom frozen statement. -/
def MinCardLicence : Prop :=
  ∀ (u v : State), u.WF → sameOrbitSetoid.r u v → RungLe u v →
    (∃ σ : Suit, rungAt u σ < rungAt v σ) →
    ∃ (c : Card) (r : Nat),
      c.rank.toIdx = rungAt u c.suit ∧
      c.rank.toIdx = r ∧
      r < 13 ∧
      rungAt u c.suit < rungAt v c.suit ∧
      (∀ τ : Suit, rungAt u τ < rungAt v τ → r ≤ rungAt u τ) ∧
      ((Parented u c ∧ c.rank ≠ Rank.king) ∨ (Bare u c ∧ c.rank = Rank.king))

/-- If `run ≠ []`, `c` is covered, hence not a pile top. -/
private theorem rl_run_nil_of_top_exists {u : State} {c : Card} {a : Anchor} {run : List Card}
    (hu : u.WF) (hhold : u.pileHolding c = some a)
    (hfc : fromCard c (u.piles a).faceUp = c :: run)
    (htop : ∃ a', u.pileOfTop c = some a') : run = [] := by
  by_cases hr : run = []
  · exact hr
  · exfalso
    obtain ⟨d, hd⟩ := cover_of_run hu hhold hfc hr
    have hnone : u.pileOfTop c = none := no_top_of_seat hu hd
    rcases htop with ⟨a', ha'⟩
    rw [hnone] at ha'
    exact absurd ha' (by simp)

/-- **`MinCardFree` from the licence residual.**  The face-up, run-or-twin,
`hatch_iff`, and `freeCardS_sem` rows assemble. -/
theorem minCardFree_of_licence (h : MinCardLicence) : MinCardFree := by
  intro u v hu horb hle hne
  obtain ⟨c, r, hfix, hcrank, hr13, hdef, hmin, hlic⟩ := h u v hu horb hle hne
  obtain ⟨a, hfacec⟩ := minCard_faceUp hu horb hfix hdef
  have hhold : u.pileHolding c = some a := (pileHolding_eq_some_iff hu).2 hfacec
  obtain ⟨run, hfc⟩ := fromCard_eq_head_of_mem hfacec
  have htop := minCard_top_or_twinTop hu horb hle hfix hcrank hr13 hdef hmin
  have hrot : run = [] ∨ u.pileOfTop c.twin ≠ none := by
    rcases htop with ⟨a', ha'⟩ | ht
    · left
      exact rl_run_nil_of_top_exists hu hhold hfc ⟨a', ha'⟩
    · right
      intro hcon
      rcases ht with ⟨a'', ha''⟩
      rw [hcon] at ha''
      exact absurd ha'' (by simp)
  have hhatch := (hatch_iff hu hhold hfc).mp hrot
  exact ⟨c, hfix, hdef, (freeCardS_sem hu).mpr ⟨a, hhold, hlic, hhatch⟩⟩

/-- The bare-non-king-bottom freeze (the last mathematical residual): a
card that is the bottom of its face-up run over an empty hidden deck
cannot have its suit advanced by a reversible play. -/
def BareBottomFrozen : Prop :=
  ∀ (u v : State) (c : Card) (a : Anchor),
    u.WF → sameOrbitSetoid.r u v →
    c ∈ (u.piles a).faceUp →
    below c (u.piles a).faceUp = [] →
    c.rank.toIdx = rungAt u c.suit →
    rungAt u c.suit < rungAt v c.suit →
    (u.piles a).hidden = [] ∧ c.rank = Rank.king

/-- The selection predicate: a deficient next-up card. -/
private def rlMinPred (u v : State) (c : Card) : Bool :=
  decide (rungAt u c.suit < rungAt v c.suit) &&
    decide (c.rank.toIdx = rungAt u c.suit)

/-- **`MinCardLicence` from the bare-bottom freeze.**  Selects the minimal
deficient next-up card via `PrefixClimb.exists_min_bool`; the parented arm
is immediate, the bare arm is the freeze. -/
theorem minCardLicence_of_frozen (hfrozen : BareBottomFrozen) : MinCardLicence := by
  intro u v hu horb hle hne
  have hv : v.WF := wf_of_sameOrbit horb hu
  obtain ⟨σ0, hσ0⟩ := hne
  have hσ13 : rungAt u σ0 < 13 := Nat.lt_of_lt_of_le hσ0 (rungAt_le13 hv σ0)
  let c0 : Card := Card.mk σ0 (FoundKit.Rk (rungAt u σ0))
  have hc0rank : c0.rank.toIdx = rungAt u σ0 := FoundKit.Rk_toIdx _ hσ13
  have hp0 : rlMinPred u v c0 = true := by
    unfold rlMinPred
    rw [Bool.and_eq_true]
    exact ⟨decide_eq_true hσ0, decide_eq_true hc0rank⟩
  obtain ⟨c, _hmem, hpc, hcmin⟩ :=
    PrefixClimb.exists_min_bool (l := Card.universe) (p := rlMinPred u v)
      ⟨c0, Card.mem_universe c0, hp0⟩
  have hp : rungAt u c.suit < rungAt v c.suit ∧ c.rank.toIdx = rungAt u c.suit := by
    unfold rlMinPred at hpc
    rw [Bool.and_eq_true] at hpc
    exact ⟨of_decide_eq_true hpc.1, of_decide_eq_true hpc.2⟩
  obtain ⟨hdef, hfix⟩ := hp
  let r : Nat := c.rank.toIdx
  have hcrank : c.rank.toIdx = r := rfl
  have hr13 : r < 13 := by
    show c.rank.toIdx < 13
    have h1 : c.rank.toIdx < rungAt v c.suit := by rw [hfix]; exact hdef
    have h2 := rungAt_le13 hv c.suit
    omega
  have hmin : ∀ τ : Suit, rungAt u τ < rungAt v τ → r ≤ rungAt u τ := by
    intro τ hτ
    show c.rank.toIdx ≤ rungAt u τ
    have hτ13 : rungAt u τ < 13 := Nat.lt_of_lt_of_le hτ (rungAt_le13 hv τ)
    let cτ : Card := Card.mk τ (FoundKit.Rk (rungAt u τ))
    have hcτrank : cτ.rank.toIdx = rungAt u τ := FoundKit.Rk_toIdx _ hτ13
    have hpτ : rlMinPred u v cτ = true := by
      unfold rlMinPred
      rw [Bool.and_eq_true]
      exact ⟨decide_eq_true hτ, decide_eq_true hcτrank⟩
    have hle := hcmin cτ (Card.mem_universe cτ) hpτ
    rwa [hcτrank] at hle
  obtain ⟨a, hfacec⟩ := minCard_faceUp hu horb hfix hdef
  have hhold : u.pileHolding c = some a := (pileHolding_eq_some_iff hu).2 hfacec
  have hlic : (Parented u c ∧ c.rank ≠ Rank.king) ∨ (Bare u c ∧ c.rank = Rank.king) := by
    by_cases hbelow : below c (u.piles a).faceUp = []
    · right
      have hfz := hfrozen u v c a hu horb hfacec hbelow hfix hdef
      exact ⟨⟨a, hhold, hfz.1⟩, hfz.2⟩
    · left
      refine ⟨(parented_iff_below hhold).2 hbelow, ?_⟩
      intro hk
      obtain ⟨z, hz⟩ := (parented_iff_below hhold).2 hbelow
      obtain ⟨az, hholdz, _, hlastz⟩ := tfc_seatOf_of_inr hz
      have haz : az = a := Option.some.inj (hholdz.symm.trans hhold)
      subst haz
      have hfit : canSitOn c z = true := (tfc_seat_parent hu hhold hlastz).1
      have hrank := ((canSitOn_eq c z).mp hfit).1
      have hkidx : c.rank.toIdx = 12 := by rw [hk]; rfl
      have hlt := Rank.toIdx_lt z.rank
      omega
  exact ⟨c, r, hfix, hcrank, hr13, hdef, hmin, hlic⟩

/-- **THE BARE-BOTTOM FREEZE, PROVED.**  The seat censuses (`walk_parented`,
`walk_king_bare`) applied to the *reverse* play say: a card that is
unparented and face-up at `u`, with `v` founding it, cannot be a non-king
(`walk_parented` would parent it at `u`), and a king cannot have a nonempty
hidden deck (`walk_king_bare` would make it bare at `u`). -/
theorem bareBottomFrozen_proved : BareBottomFrozen := by
  intro u v c a hu horb hface hbelow hnext hdef
  have hv : v.WF := wf_of_sameOrbit horb hu
  have hcfv : c ∈ v.found c.suit :=
    FoundKit.mem_found_of_rung hv (by rw [hnext]; exact hdef)
  have hnotfacev : ¬ ∃ a', c ∈ (v.piles a').faceUp := by
    rintro ⟨a', hmem⟩
    exact ((mem_found_unique hv hcfv).1 a').2 hmem
  obtain ⟨ρrev, hρrev, _, _⟩ := horb
  have hhold : u.pileHolding c = some a := (pileHolding_eq_some_iff hu).2 hface
  have hnotparu : ¬ Parented u c := by
    intro hp
    have hne : below c (u.piles a).faceUp ≠ [] := (parented_iff_below hhold).mp hp
    exact hne hbelow
  have hking : c.rank = Rank.king := by
    by_cases hk : c.rank = Rank.king
    · exact hk
    · exfalso
      have hparu : Parented u c :=
        walk_parented hv hρrev c hk ⟨a, hface⟩ (Or.inl hnotfacev)
      exact hnotparu hparu
  have hbareu : Bare u c :=
    walk_king_bare hv hρrev c hking ⟨a, hface⟩ (Or.inl hnotfacev)
  obtain ⟨a', hhold', hhid'⟩ := hbareu
  have haz : a' = a := Option.some.inj (hhold'.symm.trans hhold)
  subst haz
  exact ⟨hhid', hking⟩

/-- **`(R)` — UNCONDITIONAL.** -/
theorem rungLe_raiseReach_proved :
    ∀ (u v : State), u.WF → sameOrbitSetoid.r u v → RungLe u v →
      ∃ (ws : List Card) (z : State),
        RaiseSSeqLicensed u ws z ∧ ∀ σ : Suit, rungAt z σ = rungAt v σ :=
  rungLe_raiseReach_of_climbProgress
    (climbProgress_of_minCardFree
      (minCardFree_of_licence
        (minCardLicence_of_frozen bareBottomFrozen_proved)))

#check @minCard_faceUp
#check @cover_suit_nonDeficient
#check @cover_faceUp_at_v
#check @cover_parent_twin
#check @cover_suit_nonDeficient'
#check @cover_parent_of_founded
#check @cover_parent_of_twinFounded
#check @double_cover_false

#print axioms minCard_faceUp
#print axioms cover_suit_nonDeficient
#print axioms cover_faceUp_at_v
#print axioms cover_parent_twin
#print axioms cover_suit_nonDeficient'
#print axioms cover_parent_of_founded
#print axioms cover_parent_of_twinFounded
#print axioms double_cover_false
#print axioms minCard_top_or_twinTop
#print axioms minCardFree_of_licence
#print axioms minCardLicence_of_frozen
#print axioms bareBottomFrozen_proved
#print axioms rungLe_raiseReach_proved

#check @minCard_top_or_twinTop
#check @MinCardLicence
#check @minCardFree_of_licence
#check @BareBottomFrozen
#check @minCardLicence_of_frozen

end OneColourClosure
