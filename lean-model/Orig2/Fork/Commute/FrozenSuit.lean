import Orig2.Fiber.LockRung
import Orig2.Fork.Class.ForkRaiseReorderProof

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Temp/FrozenSuit — a commit-locked card is frozen across the orbit

**The claim.**  If `w` is next-up at `s` and sits as the *only* face-up card
of its pile with a non-empty hidden deck under it (`below w faceUp = []` plus
`hidden ≠ []`), then no orbit-mate of `s` has a *higher* rung in `w`'s suit
than `s` does.

Note that `below w faceUp = []` combined with `pileOfTop s w = some a` already
forces the face-up run to be exactly `[w]` at a `WF` state, so the "only
face-up card" reading is not an extra hypothesis: it is what `below = []`
means at the pile top.

**Why it is true.**  Such a `w` is a *commit lock*:

* it can never be founded, because founding it needs `CanRaise`, whose seat
  disjunct is `chop faceUp ≠ [] ∨ (hidden = [] ∧ w king)`; here
  `below w faceUp = []` forces `faceUp = [w]` (so `chop faceUp = []`) while
  `hidden ≠ []`;
* every reversible letter keeps `w` at the *head* of its pile's face-up run
  (so it is either not the pile top at all, or the top with `chop = []`) and
  never shortens that pile's hidden deck.  No reversible letter can put a card
  *beneath* `w` (landings append) nor move `w` (a slide moving `w` needs
  `below w faceUp ≠ []`, i.e. `tabToTabR` fails), and the hidden deck is only
  flipped by `afterRunRemoved` at an *empty* prefix, which cannot occur at a
  run headed by `w`.

The invariance lemma actually used is `lock_step` below.  Its conclusion —
stated as a conjunction, not as a new `Prop` wrapper — is

```
(∃ t, (V.piles a).faceUp = w :: t) ∧ (V.piles a).hidden ≠ [] ∧ w ∉ V.found w.suit
```

`w ∉ found` converts to the rung bound via `le_rung_of_not_found`
(equivalently `FoundKit.mem_found_of_rung`), and `nextUp` pins
`rungAt s w.suit = w.rank.toIdx`, giving `rungAt z w.suit ≤ rungAt s w.suit`.

House rules: no `sorry`, no `Classical`, no `noncomputable`; no new `Prop`
wrapper definition.  `Orig2` is not modified and nothing in it is reproved:
`lockInv_step`'s seat/step kit, `step_tabToFound_inv`/`step_tabToTab_inv`/
`step_foundToTab_inv`, `mem_faceUp_unique`, `pileOfTop_top`, `runOK_nodup`,
`le_rung_of_not_found` are reused.
-/

namespace FrozenSuit

/-! ## §1. Elementary list/pile facts -/

/-- `below` of a cons whose head is not the target keeps the head. -/
theorem below_cons_of_ne {cf w : Card} {t : List Card} (hne : w ≠ cf) :
    below cf (w :: t) = w :: below cf t := by
  rw [below_cons]
  exact ite_eq_right hne

/-- A nodup run whose last card is its head is the singleton. -/
theorem faceUp_singleton_of_head_top {l : List Card} {w : Card}
    (hnd : l.Nodup) (hhead : ∃ t, l = w :: t) (htop : lastOf l = some w) :
    l = [w] := by
  obtain ⟨t, rfl⟩ := hhead
  cases t with
  | nil => rfl
  | cons e es =>
      exfalso
      have hnc : w ∉ e :: es := (List.nodup_cons.mp hnd).1
      have hlast : lastOf (e :: es) = some w := htop
      exact hnc (lastOf_mem hlast)

/-- A run headed by `w` has `chop = w :: chop tail` when the tail is non-empty. -/
theorem chop_cons_of_ne_nil {w : Card} {t : List Card} (ht : t ≠ []) :
    chop (w :: t) = w :: chop t := by
  cases t with
  | nil => exact absurd rfl ht
  | cons e es => rfl

/-- Forgetting `fromCard` preserves non-membership. -/
theorem not_mem_fromCard_of_not_mem {c w : Card} {l : List Card} (h : w ∉ l) :
    w ∉ fromCard c l := fun hc => h (mem_fromCard hc)

/-- The pointwise read of a single-card empty-seat landing. -/
theorem putCard_piles_inl_apply {st : State} {card : Card} (a0 a : Anchor) :
    (st.putCard card (Sum.inl a0)).piles a
      = if a = a0 then (⟨[], [card]⟩ : Pile) else st.piles a := by
  rw [putCard_piles_inl]

/-- The pointwise read of a single-card card-base landing. -/
theorem putCard_piles_inr_apply {st : State} {card : Card} {z : Card} {k : Anchor}
    (hz : st.pileOfTop z = some k) (a : Anchor) :
    (st.putCard card (Sum.inr z)).piles a
      = if a = k then ({ st.piles k with faceUp := (st.piles k).faceUp ++ [card] } : Pile)
        else st.piles a := by
  rw [putCard_piles_inr _ _ _ _ hz]

/-- The pointwise read of a run empty-seat landing. -/
theorem putRun_piles_inl_apply {st : State} {run : List Card} (a0 a : Anchor) :
    (st.putRun run (Sum.inl a0)).piles a
      = if a = a0 then (⟨[], run⟩ : Pile) else st.piles a := by
  rw [putRun_piles_inl]

/-- The pointwise read of a run card-base landing. -/
theorem putRun_piles_inr_apply {st : State} {run : List Card} {z : Card} {k : Anchor}
    (hz : st.pileOfTop z = some k) (a : Anchor) :
    (st.putRun run (Sum.inr z)).piles a
      = if a = k then ({ st.piles k with faceUp := (st.piles k).faceUp ++ run } : Pile)
        else st.piles a := by
  rw [putRun_piles_inr _ _ _ _ hz]

/-! ## §2. The lock denies `CanRaise` -/

/-- **A head-of-run card with a hidden deck beneath it is never raisable.**
(`below w faceUp = []` at a pile top forces the run to be `[w]`, killing the
chop disjunct; `hidden ≠ []` kills the bare-king disjunct.) -/
theorem not_canRaise_of_head_hidden {U : State} (hwf : U.WF) {w : Card}
    {a : Anchor} (hhead : ∃ t, (U.piles a).faceUp = w :: t)
    (hhid : (U.piles a).hidden ≠ []) :
    ¬ CanRaise U w := by
  rintro ⟨-, a', hpa', hseat⟩
  have hlast : lastOf (U.piles a').faceUp = some w := (pileOfTop_top hpa').2
  have hmem' : w ∈ (U.piles a').faceUp := lastOf_mem hlast
  obtain ⟨t, ht⟩ := hhead
  have hmem : w ∈ (U.piles a).faceUp := by rw [ht]; exact List.mem_cons_self ..
  have haa : a' = a := by
    by_cases hne : a' = a
    · exact hne
    · exfalso
      exact (mem_faceUp_unique hwf hmem a' hne).1 hmem'
  have hnd : (U.piles a').faceUp.Nodup := runOK_nodup (hwf.2.1 a')
  have hsingle : (U.piles a').faceUp = [w] :=
    faceUp_singleton_of_head_top hnd ⟨t, by rw [haa]; exact ht⟩ hlast
  have hchop : chop (U.piles a').faceUp = [] := by rw [hsingle]; rfl
  rcases hseat with h | ⟨h0, -⟩
  · exact h hchop
  · exact hhid (haa ▸ h0)

/-- A `canPlace` landing on an empty seat cannot be the locked pile. -/
theorem not_inl_of_lock {st : State} {card w : Card} {b : Base} {a : Anchor}
    (hcp : st.canPlace card b = true)
    (hhead : ∃ t, (st.piles a).faceUp = w :: t) :
    ∀ a0, b = Sum.inl a0 → a ≠ a0 := by
  intro a0 hb ha
  obtain ⟨t, ht⟩ := hhead
  have hcp' : st.canPlace card (Sum.inl a0) = true := by rw [← hb]; exact hcp
  have h1 : (st.piles a0).isEmpty = true := (canPlace_inl hcp').1
  rw [← ha] at h1
  have h2 : (st.piles a).isEmpty = false :=
    Pile.isEmpty_eq_false_of_mem (by rw [ht]; exact List.mem_cons_self ..)
  rw [h1] at h2
  exact Bool.noConfusion h2

/-! ## §3. Pile surgery keeps the lock -/

/-- Removing `chop faceUp` from a run headed by `w`, with a non-empty tail,
keeps `w` at the head. -/
theorem head_afterRunRemoved_chop {p : Pile} {w : Card} {t : List Card}
    (hface : p.faceUp = w :: t) (ht : t ≠ []) :
    ∃ s, (Pile.afterRunRemoved p (chop p.faceUp)).faceUp = w :: s := by
  have hchop : chop p.faceUp = w :: chop t := by rw [hface]; exact chop_cons_of_ne_nil ht
  have hpre : chop p.faceUp ≠ [] := by rw [hchop]; simp
  refine ⟨chop t, ?_⟩
  rw [afterRunRemoved_ne hpre]
  exact hchop

/-- `putCard` keeps `w` at the head of its run, given that the landing is not
an empty-seat landing on `w`'s own pile. -/
theorem putCard_faceUp_head {st : State} {card w : Card} {b : Base} {a : Anchor}
    (hface : ∃ t, (st.piles a).faceUp = w :: t)
    (hinl : ∀ a0, b = Sum.inl a0 → a ≠ a0) :
    ∃ t, ((st.putCard card b).piles a).faceUp = w :: t := by
  obtain ⟨t, ht⟩ := hface
  cases b with
  | inl a0 =>
      by_cases ha : a = a0
      · exact absurd ha (hinl a0 rfl)
      · rw [putCard_piles_inl_apply, ite_eq_right ha]
        exact ⟨t, ht⟩
  | inr z =>
      cases hz : st.pileOfTop z with
      | none =>
          rw [show st.putCard card (Sum.inr z) = st from by simp [State.putCard, hz]]
          exact ⟨t, ht⟩
      | some k =>
          rw [putCard_piles_inr_apply hz]
          show ∃ s, (if a = k then
              ({ st.piles k with faceUp := (st.piles k).faceUp ++ [card] } : Pile)
            else st.piles a).faceUp = w :: s
          by_cases ha : a = k
          · rw [ite_eq_left ha]
            refine ⟨t ++ [card], ?_⟩
            rw [← ha, ht]
            rfl
          · rw [ite_eq_right ha]
            exact ⟨t, ht⟩

/-- `putRun` keeps `w` at the head of its run and keeps the hidden deck, when
the run avoids `w` and the landing is not an empty seat at `w`'s pile. -/
theorem putRun_lock {st : State} {run : List Card} {w : Card} {b : Base} {a : Anchor}
    (hface : ∃ t, (st.piles a).faceUp = w :: t)
    (hinl : ∀ a0, b = Sum.inl a0 → a ≠ a0) :
    (∃ t, ((st.putRun run b).piles a).faceUp = w :: t) ∧
      ((st.putRun run b).piles a).hidden = (st.piles a).hidden := by
  obtain ⟨t, ht⟩ := hface
  cases b with
  | inl a0 =>
      by_cases ha : a = a0
      · exact absurd ha (hinl a0 rfl)
      · rw [putRun_piles_inl_apply, ite_eq_right ha]
        exact ⟨⟨t, ht⟩, rfl⟩
  | inr z =>
      cases hz : st.pileOfTop z with
      | none =>
          rw [show st.putRun run (Sum.inr z) = st from by simp [State.putRun, hz]]
          exact ⟨⟨t, ht⟩, rfl⟩
      | some k =>
          rw [putRun_piles_inr_apply hz]
          show (∃ s, (if a = k then
              ({ st.piles k with faceUp := (st.piles k).faceUp ++ run } : Pile)
            else st.piles a).faceUp = w :: s) ∧
            (if a = k then
              ({ st.piles k with faceUp := (st.piles k).faceUp ++ run } : Pile)
            else st.piles a).hidden = (st.piles a).hidden
          by_cases ha : a = k
          · rw [ite_eq_left ha]
            refine ⟨⟨t ++ run, ?_⟩, ?_⟩
            · rw [← ha, ht]; rfl
            · rw [← ha]
          · rw [ite_eq_right ha]
            exact ⟨⟨t, ht⟩, rfl⟩

/-- The `setPile`-of-`afterRunRemoved` stage of a slide keeps the lock at `w`'s
pile. -/
theorem setPile_afterRunRemoved_lock {st : State} {cf w : Card} {a a' : Anchor}
    (hface : ∃ t, (st.piles a).faceUp = w :: t) (hne : w ≠ cf) :
    (∃ t, ((st.setPile a'
        (Pile.afterRunRemoved (st.piles a') (below cf (st.piles a').faceUp))).piles a).faceUp
          = w :: t) ∧
      ((st.setPile a'
        (Pile.afterRunRemoved (st.piles a') (below cf (st.piles a').faceUp))).piles a).hidden
          = (st.piles a).hidden := by
  by_cases ha : a = a'
  · have hface' : ∃ t, (st.piles a').faceUp = w :: t := by rw [← ha]; exact hface
    obtain ⟨t, ht⟩ := hface'
    have hpre : below cf (st.piles a').faceUp = w :: below cf t := by
      rw [ht]; exact below_cons_of_ne hne
    have hne0 : below cf (st.piles a').faceUp ≠ [] := by rw [hpre]; simp
    refine ⟨⟨below cf t, ?_⟩, ?_⟩
    · rw [ha, setPile_piles_self, afterRunRemoved_ne hne0]
      exact hpre
    · rw [ha, setPile_piles_self, afterRunRemoved_ne hne0]
  · rw [setPile_piles_ne ha]
    exact ⟨hface, rfl⟩

/-! ## §4. The step lemma -/

/-- **THE INVARIANCE LEMMA.**  The lock is closed under every reversible
letter: `w` stays at the head of its pile's face-up run, its pile keeps a
non-empty hidden deck, and `w` stays off its foundation row. -/
theorem lock_step {U V : State} {w : Card} {a : Anchor} {m : Move}
    (hwf : U.WF) (hstep : U.step m = some V) (hrev : reversibleAtW U m)
    (hhead : ∃ t, (U.piles a).faceUp = w :: t)
    (hhid : (U.piles a).hidden ≠ [])
    (hnf : w ∉ U.found w.suit) :
    (∃ t, (V.piles a).faceUp = w :: t) ∧ (V.piles a).hidden ≠ [] ∧
      w ∉ V.found w.suit := by
  obtain ⟨t0, ht0⟩ := hhead
  have hmem : w ∈ (U.piles a).faceUp := by rw [ht0]; exact List.mem_cons_self ..
  rcases m with _ | cf | ⟨cf, bf⟩ | cf | ⟨cf, bf⟩ | ⟨cf, bf⟩
  · -- draw
    have hd : U.stepDraw = some V := hstep
    exact ⟨by rw [stepDraw_piles hd]; exact ⟨t0, ht0⟩,
      by rw [stepDraw_piles hd]; exact hhid,
      by rw [stepDraw_found hd]; exact hnf⟩
  · exact absurd hrev (wasteToFound_not_reversibleAtW U cf)
  · exact absurd hrev (wasteToTab_not_reversibleAtW U cf bf)
  · -- tabToFound cf
    obtain ⟨hnext, a', hpa', hsV⟩ := step_tabToFound_inv hstep
    obtain ⟨hF1, hF2, -⟩ := tabToFound_found_trio hsV
    have hcan : CanRaise U cf := OneColourClosure.canRaise_of_reversibleAtW hwf hrev
    have hcf_ne : cf ≠ w := by
      intro hcw
      exact not_canRaise_of_head_hidden hwf ⟨t0, ht0⟩ hhid (hcw ▸ hcan)
    have hpile : V.piles a =
        (if a = a' then Pile.afterRunRemoved (U.piles a') (chop (U.piles a').faceUp)
          else U.piles a) := by rw [hsV]
    have hnfV : w ∉ V.found w.suit := by
      by_cases hsu : cf.suit = w.suit
      · have hVf : V.found w.suit = U.found w.suit ++ [cf] := by
          rw [show w.suit = cf.suit from hsu.symm]; exact hF1
        rw [hVf]
        intro hm
        rcases List.mem_append.mp hm with h | h
        · exact hnf h
        · rw [List.mem_singleton] at h
          exact hcf_ne h.symm
      · rw [show V.found w.suit = U.found w.suit from hF2 w.suit (Ne.symm hsu)]
        exact hnf
    refine ⟨?_, ?_, hnfV⟩
    · rw [hpile]
      by_cases ha : a = a'
      · rw [ite_eq_left ha, ← ha]
        have hlast : lastOf (U.piles a).faceUp = some cf := by
          rw [ha]; exact (pileOfTop_top hpa').2
        have htne : t0 ≠ [] := by
          intro ht
          rw [ht0, ht] at hlast
          have hwcf : w = cf := by simpa [lastOf] using hlast
          exact hcf_ne hwcf.symm
        exact head_afterRunRemoved_chop ht0 htne
      · rw [ite_eq_right ha]
        exact ⟨t0, ht0⟩
    · rw [hpile]
      by_cases ha : a = a'
      · rw [ite_eq_left ha, ← ha]
        have hlast : lastOf (U.piles a).faceUp = some cf := by
          rw [ha]; exact (pileOfTop_top hpa').2
        have htne : t0 ≠ [] := by
          intro ht
          rw [ht0, ht] at hlast
          have hwcf : w = cf := by simpa [lastOf] using hlast
          exact hcf_ne hwcf.symm
        have hchopne : chop (U.piles a).faceUp ≠ [] := by
          rw [ht0, chop_cons_of_ne_nil htne]; simp
        rw [afterRunRemoved_ne hchopne]
        exact hhid
      · rw [ite_eq_right ha]
        exact hhid
  · -- foundToTab cf bf
    obtain ⟨cg, htop, hcgeq, hcp, hsV⟩ := step_foundToTab_inv hstep
    have hcg : cg ∈ U.found cf.suit :=
      lastOf_mem (show lastOf (U.found cf.suit) = some cg from htop)
    have hcfmem : cf ∈ U.found cf.suit := by rw [hcgeq] at hcg; exact hcg
    have hw_ne : w ≠ cf := by
      intro hwc
      exact hnf (by rw [hwc]; exact hcfmem)
    have hinl : ∀ a0, bf = Sum.inl a0 → a ≠ a0 :=
      not_inl_of_lock hcp ⟨t0, ht0⟩
    have hVp : V.piles = (U.putCard cf bf).piles := by
      rw [hsV]
      cases bf with
      | inl a0 => simp [State.putCard, State.setPile, setFound_piles]
      | inr z =>
          cases hz : U.pileOfTop z with
          | none => simp [State.putCard, State.setFound_pileOfTop, setFound_piles, hz]
          | some k => simp [State.putCard, State.setPile, State.setFound_pileOfTop,
              setFound_piles, hz]
    have hnfV : w ∉ V.found w.suit := by
      by_cases hsu : cf.suit = w.suit
      · have hVf : V.found w.suit = chop (U.found w.suit) := by
          rw [hsV, putCard_found, show w.suit = cf.suit from hsu.symm, setFound_found_self]
        rw [hVf]
        intro hm
        exact hnf (chop_mem hm)
      · have hVf : V.found w.suit = U.found w.suit := by
          rw [hsV, putCard_found]
          exact setFound_found_ne (Ne.symm hsu)
        rw [hVf]
        exact hnf
    exact ⟨by rw [hVp]; exact putCard_faceUp_head ⟨t0, ht0⟩ hinl,
      by rw [hVp, putCard_hidden_eq hcp a]; exact hhid,
      hnfV⟩
  · -- tabToTab cf bf
    obtain ⟨a', hhold, hcp, _hne0, hsV⟩ := step_tabToTab_inv hstep
    have hmemcf : cf ∈ (U.piles a').faceUp := pileHolding_mem hhold
    have hcf_ne : cf ≠ w := by
      intro hcw
      have hmem_w : w ∈ (U.piles a').faceUp := by rw [← hcw]; exact hmemcf
      have haa : a' = a := by
        by_cases hne : a' = a
        · exact hne
        · exfalso
          exact (mem_faceUp_unique hwf hmem a' hne).1 hmem_w
      have hR : tabToTabR U cf bf = true := by
        have h := (reversibleOf_iff_reversibleAtW hwf (Move.tabToTab cf bf)).mpr hrev
        simpa [reversibleOf] using h
      simp only [tabToTabR, hhold, hcp] at hR
      have hbelow : below w (U.piles a).faceUp = [] := by
        rw [ht0, below_cons, ite_eq_left rfl]
      rw [hcw, haa, hbelow] at hR
      cases hhid' : (U.piles a).hidden with
      | nil => exact hhid hhid'
      | cons y ys => rw [hhid'] at hR; exact absurd hR (by simp)
    obtain ⟨hWhead, hWhid⟩ :=
      setPile_afterRunRemoved_lock (st := U) (cf := cf) (a := a) (a' := a')
        ⟨t0, ht0⟩ (Ne.symm hcf_ne)
    have hinl : ∀ a0, bf = Sum.inl a0 → a ≠ a0 := not_inl_of_lock hcp ⟨t0, ht0⟩
    have hres := putRun_lock
      (st := U.setPile a' (Pile.afterRunRemoved (U.piles a') (below cf (U.piles a').faceUp)))
      (run := fromCard cf (U.piles a').faceUp) (w := w) (b := bf) (a := a)
      hWhead hinl
    have hVeq : V = (U.setPile a'
        (Pile.afterRunRemoved (U.piles a') (below cf (U.piles a').faceUp))).putRun
          (fromCard cf (U.piles a').faceUp) bf := hsV
    exact ⟨by rw [hVeq]; exact hres.1,
      by rw [hVeq, hres.2, hWhid]; exact hhid,
      by rw [hVeq, putRun_found, setPile_found]; exact hnf⟩

/-! ## §5. The play closure -/

/-- **The lock rides every witness shuffle.** -/
theorem lock_play {s z : State} {w : Card} {a : Anchor} {play : List Move}
    (hplay : ShufflePlayW s play z) (hwf : s.WF)
    (hhead : ∃ t, (s.piles a).faceUp = w :: t)
    (hhid : (s.piles a).hidden ≠ [])
    (hnf : w ∉ s.found w.suit) :
    (∃ t, (z.piles a).faceUp = w :: t) ∧ (z.piles a).hidden ≠ [] ∧
      w ∉ z.found w.suit ∧ z.WF := by
  have key : ∀ (A : State) (ρ : List Move) (B : State), ShufflePlayW A ρ B →
      A.WF → (∃ t, (A.piles a).faceUp = w :: t) → (A.piles a).hidden ≠ [] →
      w ∉ A.found w.suit →
      (∃ t, (B.piles a).faceUp = w :: t) ∧ (B.piles a).hidden ≠ [] ∧
        w ∉ B.found w.suit ∧ B.WF := by
    intro A ρ B hp
    induction hp with
    | nil st => intro hw hh hb hf; exact ⟨hh, hb, hf, hw⟩
    | @cons st s₁ W m ρ hlet hstep hrest ih =>
        intro hw hh hb hf
        obtain ⟨hh', hb', hf'⟩ := lock_step hw hstep hlet hh hb hf
        exact ih (step_wf hw hstep) hh' hb' hf'
  exact key s play z hplay hwf hhead hhid hnf

/-! ## §6. The claim -/

/-- **A commit-locked card cannot be passed by its suit's rung.**

`w` is next-up at `s`, sits as the last (here: only) face-up card of its pile
`a`, and the hidden deck under it is non-empty.  Then every orbit-mate `z` of
`s` satisfies `rungAt z w.suit ≤ rungAt s w.suit`.

The `below w faceUp = []` hypothesis, together with `pileOfTop s w = some a`,
already says the face-up run is exactly `[w]`; the proof needs nothing more.
The conclusion is exactly the `≤ rungAt s w.suit` form the campaign consumes.
-/
theorem commitLocked_rung_le {s z : State} {w : Card} {a : Anchor}
    (hs : s.WF) (horb : sameOrbitSetoid.r s z)
    (hnext : s.nextUp w = true)
    (htop : s.pileOfTop w = some a)
    (hbel : below w (s.piles a).faceUp = [])
    (hhid : (s.piles a).hidden ≠ []) :
    rungAt z w.suit ≤ rungAt s w.suit := by
  -- the head shape at `s`
  have hmemW : w ∈ (s.piles a).faceUp := lastOf_mem (pileOfTop_top htop).2
  have hhead : ∃ t, (s.piles a).faceUp = w :: t :=
    eq_cons_of_below_nil hmemW hbel
  -- `w` is off its foundation row at `s`
  have hnf : w ∉ s.found w.suit := by
    intro hf
    exact ((mem_found_unique hs hf).1 a).2 hmemW
  -- `nextUp` pins the rung at `w`'s index
  have hsR : rungAt s w.suit = w.rank.toIdx := by
    have h : w.rank.toIdx = rungAt s w.suit := by
      simpa [State.foundHeight, rungAt] using of_decide_eq_true hnext
    exact h.symm
  -- unpack the orbit relation: the forward play `s → z`
  obtain ⟨_, _, play, hplay⟩ := horb
  obtain ⟨_, _, hnfZ, hwfZ⟩ := lock_play hplay hs hhead hhid hnf
  have hle : rungAt z w.suit ≤ w.rank.toIdx := le_rung_of_not_found hwfZ hnfZ
  rw [hsR]
  exact hle

/-- **The non-king form: `hidden ≠ []` is not needed.**  When `w` is known not
to be a king, the *existing* `LockInv` machinery already freezes the rung, so
`hhid` can be dropped.  (For a king the `hidden ≠ []` hypothesis is exactly
what kills the last `CanRaise` disjunct; see `commitLocked_rung_le`.)

This form is also the honest reading of the claim when the caller's `w` is
non-royal: the lock's force comes from `below w faceUp = []`, not from the
hidden deck. -/
theorem commitLocked_rung_le_of_not_king {s z : State} {w : Card} {a : Anchor}
    (hs : s.WF) (horb : sameOrbitSetoid.r s z)
    (hnext : s.nextUp w = true)
    (htop : s.pileOfTop w = some a)
    (hbel : below w (s.piles a).faceUp = [])
    (hk : w.rank ≠ Rank.king) :
    rungAt z w.suit ≤ rungAt s w.suit := by
  have hmemW : w ∈ (s.piles a).faceUp := lastOf_mem (pileOfTop_top htop).2
  have hnf : w ∉ s.found w.suit := by
    intro hf
    exact ((mem_found_unique hs hf).1 a).2 hmemW
  have hsR : rungAt s w.suit = w.rank.toIdx := by
    have h : w.rank.toIdx = rungAt s w.suit := by
      simpa [State.foundHeight, rungAt] using of_decide_eq_true hnext
    exact h.symm
  have hlow : ∀ a', w ∈ (s.piles a').faceUp → below w (s.piles a').faceUp = [] := by
    intro a' hm
    by_cases ha : a' = a
    · rw [ha]; exact hbel
    · exact absurd hm ((mem_faceUp_unique hs hmemW a' ha).1)
  have hinv : LockInv s w w.rank.toIdx :=
    ⟨hlow, hnf, by rw [hsR]; exact Nat.le_refl _⟩
  obtain ⟨_, _, play, hplay⟩ := horb
  obtain ⟨_, hinvZ⟩ := lockInv_play hplay hs hinv rfl hk
  have hle : rungAt z w.suit ≤ w.rank.toIdx := hinvZ.2.2
  rw [hsR]
  exact hle

end FrozenSuit

#print axioms FrozenSuit.below_cons_of_ne
#print axioms FrozenSuit.faceUp_singleton_of_head_top
#print axioms FrozenSuit.chop_cons_of_ne_nil
#print axioms FrozenSuit.not_mem_fromCard_of_not_mem
#print axioms FrozenSuit.putCard_piles_inl_apply
#print axioms FrozenSuit.putCard_piles_inr_apply
#print axioms FrozenSuit.putRun_piles_inl_apply
#print axioms FrozenSuit.putRun_piles_inr_apply
#print axioms FrozenSuit.not_canRaise_of_head_hidden
#print axioms FrozenSuit.not_inl_of_lock
#print axioms FrozenSuit.head_afterRunRemoved_chop
#print axioms FrozenSuit.putCard_faceUp_head
#print axioms FrozenSuit.putRun_lock
#print axioms FrozenSuit.setPile_afterRunRemoved_lock
#print axioms FrozenSuit.lock_step
#print axioms FrozenSuit.lock_play
#print axioms FrozenSuit.commitLocked_rung_le
#print axioms FrozenSuit.commitLocked_rung_le_of_not_king
