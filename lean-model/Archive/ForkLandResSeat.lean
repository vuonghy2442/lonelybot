import Orig2.Fork.Local.ForkStraddle

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkLandResSeat — the cover pile is frozen unless a letter reads its seat

`SeatSafe c q` says the letter `q` neither names `c` nor lands on `c` (and, for
the moves that cannot occur in the straddle interior, is `False`).

The main row proves that such a letter leaves the *pile top search* of `c`
alone, provided the letter's own source pile is not `c`'s pile:

```text
st.pileOfTop c = some k  ⇒  (step st q).pileOfTop c = some k
```

This is the frame fact behind the brief's "the interior should not read `x`'s
seat": if `x` sits on top of `d`, anything that neither names `x` nor lands on
it nor slides the pile under it cannot move `x`, and in particular cannot
uncover `d`.

No `sorry`, no `Classical.choice`, no `native_decide`.
-/

namespace LandResSeat

open CommuteStep

/-- The letters that do not read `c`'s seat: they never name `c` and never land
on `c`.  Waste moves cannot occur in the straddle interior (`FreeOrPull`), so
they are excluded outright. -/
def SeatSafe (c : Card) : Move → Prop
  | Move.draw => True
  | Move.wasteToFound _ => False
  | Move.wasteToTab _ _ => False
  | Move.tabToFound w => w ≠ c
  | Move.foundToTab x b => x ≠ c ∧ b ≠ Sum.inr c
  | Move.tabToTab x b => x ≠ c ∧ b ≠ Sum.inr c

theorem seatSafe_raise {c w : Card} (h : w ≠ c) : SeatSafe c (Move.tabToFound w) := h

theorem seatSafe_pull {c x : Card} {b : Base} (hx : x ≠ c) (hb : b ≠ Sum.inr c) :
    SeatSafe c (Move.foundToTab x b) := ⟨hx, hb⟩

theorem seatSafe_slide {c x : Card} {b : Base} (hx : x ≠ c) (hb : b ≠ Sum.inr c) :
    SeatSafe c (Move.tabToTab x b) := ⟨hx, hb⟩

/-- **THE SEAT IS FROZEN.**  A `SeatSafe` letter whose own source pile is not
`c`'s pile preserves the pile top search of `c`. -/
theorem pileOfTop_of_seatSafe {st s' : State} {c : Card} {q : Move} {k : Anchor}
    (hwf : st.WF) (hrev : reversibleAtW st q) (hstep : State.step st q = some s')
    (htop : st.pileOfTop c = some k) (hsafe : SeatSafe c q)
    (hsource : ∀ (x : Card) (b : Base), q = Move.tabToTab x b →
      st.pileHolding x ≠ some k) :
    s'.pileOfTop c = some k := by
  cases q with
  | draw =>
      have hp : s'.piles = st.piles := stepDraw_piles hstep
      rw [pileOfTop_congr_piles hp c, htop]
  | wasteToFound w => exact absurd hsafe (by simp [SeatSafe])
  | wasteToTab w b => exact absurd hsafe (by simp [SeatSafe])
  | tabToFound w =>
      have hwc : w ≠ c := hsafe
      obtain ⟨-, a, hpa, hs⟩ := step_tabToFound_inv hstep
      have hka : k ≠ a := by
        intro hEq
        have h1 : (st.piles a).top = some c :=
          (pileOfTop_eq_some_iff hwf).mp (hEq ▸ htop)
        have h2 : (st.piles a).top = some w := (pileOfTop_eq_some_iff hwf).mp hpa
        exact hwc (Option.some.inj (h1.symm.trans h2)).symm
      subst hs
      exact SafeTransport.pileOfTop_tabToFound_ne hwf hstep hpa htop hka
  | foundToTab x b =>
      obtain ⟨x', hx', hxc, hcp, hs⟩ := step_foundToTab_pullSt hstep
      have hx : x ≠ c := hsafe.1
      have hb : b ≠ Sum.inr c := hsafe.2
      have hfound : x ∈ st.found x.suit := by
        subst hxc
        exact lastOf_mem hx'
      obtain ⟨k2, hk2⟩ := exists_tgt_of_canPlace hcp
      have hk2ne : k2 ≠ k := by
        intro hEq
        cases b with
        | inl a =>
            have hka : k2 = a := (Option.some.inj hk2).symm
            have hak : a = k := hka.symm.trans hEq
            obtain ⟨hemp, -⟩ := canPlace_inl hcp
            rw [hak] at hemp
            obtain ⟨-, hfu⟩ := (Pile.isEmpty_eq _).mp hemp
            have hc_top : (st.piles k).top = some c :=
              (pileOfTop_eq_some_iff hwf).mp htop
            have h2 : lastOf (st.piles k).faceUp = some c := hc_top
            rw [hfu] at h2
            simp [lastOf] at h2
        | inr z =>
            have hz : st.pileOfTop z = some k2 := hk2
            have hzc : z = c := by
              have h1 : (st.piles k).top = some z :=
                (pileOfTop_eq_some_iff hwf).mp (by rw [hEq] at hz; exact hz)
              have h2 : (st.piles k).top = some c :=
                (pileOfTop_eq_some_iff hwf).mp htop
              exact Option.some.inj (h1.symm.trans h2)
            exact hb (by rw [hzc])
      subst hs
      exact pullSt_pileOfTop_ne hwf hk2 hfound htop hk2ne hx
  | tabToTab x b =>
      obtain ⟨a1, hhold1, hcp1, hrunv1, hs1⟩ := step_tabToTab_slideSt hstep
      obtain ⟨a0, k0, hhold0, hcp0, hk0, hka0, hface0, hrunv0, hcell0⟩ :=
        slide_data hwf hrev
      have hx : x ≠ c := hsafe.1
      have hb : b ≠ Sum.inr c := hsafe.2
      have hae : a0 = a1 := Option.some.inj (hhold0.symm.trans hhold1)
      -- `k0` is the target anchor; `exists_tgt_of_canPlace` gives the same one
      obtain ⟨k2, hk2⟩ := exists_tgt_of_canPlace hcp1
      have hke' : k0 = k2 := Option.some.inj (hk0.symm.trans hk2)
      have hk2ne : k2 ≠ k := by
        intro hEq
        cases b with
        | inl a =>
            have hka : k2 = a := (Option.some.inj hk2).symm
            have hak : a = k := hka.symm.trans hEq
            obtain ⟨hemp, -⟩ := canPlace_inl hcp1
            rw [hak] at hemp
            obtain ⟨-, hfu⟩ := (Pile.isEmpty_eq _).mp hemp
            have hc_top : (st.piles k).top = some c :=
              (pileOfTop_eq_some_iff hwf).mp htop
            have h2 : lastOf (st.piles k).faceUp = some c := hc_top
            rw [hfu] at h2
            simp [lastOf] at h2
        | inr z =>
            have hz : st.pileOfTop z = some k2 := hk2
            have hzc : z = c := by
              have h1 : (st.piles k).top = some z :=
                (pileOfTop_eq_some_iff hwf).mp (by rw [hEq] at hz; exact hz)
              have h2 : (st.piles k).top = some c :=
                (pileOfTop_eq_some_iff hwf).mp htop
              exact Option.some.inj (h1.symm.trans h2)
            exact hb (by rw [hzc])
      -- the slide does not start in `c`'s pile
      have hne : st.pileHolding x ≠ some k := hsource x b rfl
      have hkne_a : k ≠ a1 := by
        intro hEq
        apply hne
        rw [hEq]
        rw [hhold1]
      subst hs1
      have hak1 : k2 ≠ a1 := by rw [← hke', ← hae]; exact hka0
      have hrunv1' : fromCard x (st.piles a1).faceUp ≠ [] := by rwa [← hae]
      have hcell1' : below x (st.piles a1).faceUp ≠ [] ∨
          (below x (st.piles a1).faceUp = [] ∧ (st.piles a1).hidden = []) := by
        rwa [← hae]
      exact slideSt_pileOfTop_third hwf hcp1 hk2 hak1 hrunv1' hcell1' htop
        hkne_a (Ne.symm hk2ne)

#print axioms LandResSeat.pileOfTop_of_seatSafe

end LandResSeat
