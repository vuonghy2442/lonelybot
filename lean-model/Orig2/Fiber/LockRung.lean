import Orig2.Fiber.ArmFiber
import Orig2.Fork.CeilingBridge
import Orig2.Fork.ForkClass

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Orig2.LockRung — the mutual-lock invariant, discharged

THE TWO RESIDUES OF `Orig2/Fork/ForkClass.lean` ARE PROVED HERE.

* `cover_rung_frozen` — at a fork, the cover `d`'s suit rung never
  exceeds its value at the fork, and `d` is never founded.  The next-up
  card of `d.suit` is a lone non-king bottom (or hidden/stock); no
  reversible move can put a card below it, so it can never be raised.
* `cover_token_invariant` — the cover stays seated on `x` or `x.twin`
  along every witness play (the `CoverToken` residue).
* `forkState_one_founding_orig2` — the two pair-suit rungs never both
  exceed their at-fork values (the `OneFounding` residue).
* `CoverToken_holds` / `OneFounding_holds` — the two residues, proved.
* `fork_label_class` / `twinPair_founds` — the unconditional
  class theorem and the twin-pair founds.

The route is structural, not a one-move chase: the cover's next-up card
`c = ⟨d.suit, Rk (rungAt F d.suit)⟩` is, whenever face-up, the BOTTOM of
its face-up run (`LockInv`), so it is never a non-king top with a
nonempty chop; the reversibility gates `tabToFoundR`/`tabToTabR` supply
the move classification.  The token half uses the repo's seat-change
rows (`raise_seat_change_of_seated`, `pull_seat_change`,
`tfc_seat_point_edit`).

House compliance: additive leaf (`Orig2.ForkClass` and the certified
kit); zero `sorry`, zero `Classical.choice`; battery at the tail.
-/

/-! ## §0. List helpers -/

/-- `below` of an append whose head part contains the target. -/
theorem below_append_of_mem {c : Card} :
    ∀ {xs : List Card}, c ∈ xs → ∀ ys, below c (xs ++ ys) = below c xs := by
  intro xs
  induction xs with
  | nil => intro h; exact absurd h List.not_mem_nil
  | cons x xs ih =>
      intro h ys
      rcases List.mem_cons.mp h with rfl | hmem
      · simp [below_cons]
      · by_cases hxc : x = c
        · subst hxc
          simp [below_cons]
        · rw [List.cons_append, below_cons c x (xs ++ ys), below_cons c x xs,
            ite_eq_right hxc, ite_eq_right hxc, ih hmem ys]

/-- A card below which nothing face-up stands is the head of its list. -/
theorem eq_cons_of_below_nil {c : Card} :
    ∀ {l : List Card}, c ∈ l → below c l = [] → ∃ t, l = c :: t := by
  intro l
  induction l with
  | nil => intro h; exact absurd h List.not_mem_nil
  | cons x xs ih =>
      intro hmem hlow
      rw [below_cons c x xs] at hlow
      by_cases hxc : x = c
      · exact ⟨xs, by rw [hxc]⟩
      · rw [ite_eq_right hxc] at hlow
        exact absurd hlow (by simp)

/-- In a nodup list whose last card is `c` and with nothing face-up below
`c`, the list is the singleton `[c]` (so its chop is empty). -/
theorem chop_eq_nil_of_lock {c : Card} :
    ∀ {l : List Card}, l.Nodup → lastOf l = some c → below c l = [] →
      chop l = [] := by
  intro l hnd hlast hlow
  have hmem : c ∈ l := lastOf_mem hlast
  obtain ⟨t, rfl⟩ := eq_cons_of_below_nil hmem hlow
  have hnc : c ∉ t := (List.nodup_cons.mp hnd).1
  have ht : t = [] := by
    cases t with
    | nil => rfl
    | cons e es =>
        have h2 : lastOf (e :: es) = some c := hlast
        exact absurd (lastOf_mem h2) hnc
  rw [ht]
  rfl

/- `chop` only removes cards — one home at the shared kit
(`Orig2/Substrate/Kit.lean`'s `chop_mem`) since the 2026-10-31 shared-kit
strike; this copy struck (the cites re-point there). -/

/-- `chop` cannot lengthen. -/
theorem length_chop_le : ∀ l : List Card, (chop l).length ≤ l.length := by
  intro l
  induction l with
  | nil => simp [chop]
  | cons x xs ih =>
      cases xs with
      | nil => simp [chop]
      | cons y ys =>
          have h1 : chop (x :: y :: ys) = x :: chop (y :: ys) := rfl
          rw [h1, List.length_cons, List.length_cons]
          omega

/-- The face-up read of `revealTop` at an emptied run. -/
theorem revealTop_faceUp_empty (p : Pile) :
    (Pile.revealTop { p with faceUp := [] }).faceUp
      = match p.hidden with
        | [] => []
        | h :: _ => [h] := by
  cases hh : p.hidden with
  | nil => simp [Pile.revealTop]
  | cons h t => simp [Pile.revealTop]

/-- `fromCard` only returns cards of its list. -/
theorem mem_fromCard {c x : Card} : ∀ {l : List Card},
    x ∈ fromCard c l → x ∈ l := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (by simp [fromCard])
  | cons y t ih =>
      intro h
      rw [fromCard] at h
      split at h
      · exact h
      · exact List.mem_cons_of_mem _ (ih h)

/-- Cards of the same suit and rank index coincide. -/
theorem card_eq_of_suit_rank {c c' : Card} (hs : c'.suit = c.suit)
    (hr : c'.rank.toIdx = c.rank.toIdx) : c' = c := by
  obtain ⟨s', r'⟩ := c'
  obtain ⟨s, r⟩ := c
  simp only at hs hr
  subst hs
  have hr' : r' = r := Rank.toIdx_inj hr
  subst hr'
  rfl

/-! ## §1. The lock invariant -/

/-- **LockInv st c h** — the cover's next-up card `c` is never a pile top
with a nonempty under-run: if it is face up at all, it is the bottom card
of its face-up list.  Together with `c` being unfounded and the suit's
rung not exceeding `h`, this is preserved by every reversible move. -/
def LockInv (st : State) (c : Card) (h : Nat) : Prop :=
  (∀ a, c ∈ (st.piles a).faceUp → below c ((st.piles a).faceUp) = [])
  ∧ c ∉ st.found c.suit
  ∧ rungAt st c.suit ≤ h

/-- A locked card is not raisable (it is never a non-king top with a
nonempty under-run). -/
theorem not_canRaise_of_lock {U : State} (hwf : U.WF) {c : Card} {h : Nat}
    (hk : c.rank ≠ Rank.king) (hU : LockInv U c h) : ¬ CanRaise U c := by
  rintro ⟨-, a, hpa, hseat⟩
  have htop : lastOf (U.piles a).faceUp = some c := (pileOfTop_top hpa).2
  have hmem : c ∈ (U.piles a).faceUp := lastOf_mem htop
  have hlow : below c (U.piles a).faceUp = [] := hU.1 a hmem
  have hnd : (U.piles a).faceUp.Nodup := runOK_nodup (hwf.2.1 a)
  have hchop : chop (U.piles a).faceUp = [] := chop_eq_nil_of_lock hnd htop hlow
  rcases hseat with h | ⟨-, hk2⟩
  · exact h hchop
  · exact hk hk2

/-- `c` is a lock witness: it is not founded, so its index is at least the
rung. -/
theorem le_rung_of_not_found {U : State} (hwf : U.WF) {c : Card}
    (h : c ∉ U.found c.suit) : rungAt U c.suit ≤ c.rank.toIdx := by
  have hnot : ¬ c.rank.toIdx < rungAt U c.suit :=
    fun hlt => h (FoundKit.mem_found_of_rung hwf hlt)
  omega

/-- Low after `afterRunRemoved`: the removal keeps the "bottom card" shape. -/
theorem low_afterRunRemoved {p : Pile} {c : Card} {pre : List Card}
    (hmem : c ∈ (Pile.afterRunRemoved p pre).faceUp)
    (hpre : c ∈ pre → below c pre = []) :
    below c (Pile.afterRunRemoved p pre).faceUp = [] := by
  by_cases h0 : pre = []
  · have hstep : Pile.afterRunRemoved p pre = Pile.revealTop { p with faceUp := [] } := by
      rw [h0]; rfl
    rw [hstep, revealTop_faceUp_empty] at hmem ⊢
    cases hhid : p.hidden with
    | nil =>
        simp only [hhid] at hmem ⊢
        exact absurd hmem (by simp)
    | cons hd tl =>
        simp only [hhid] at hmem ⊢
        rw [List.mem_singleton] at hmem
        rw [← hmem]
        simp [below_cons]
  · rw [afterRunRemoved_ne h0] at hmem ⊢
    exact hpre hmem

/-- Low on `chop`, given that `c` heads the run. -/
theorem low_chop {f : List Card} {c : Card}
    (hcons : ∃ t, f = c :: t) (hmem : c ∈ chop f) : below c (chop f) = [] := by
  obtain ⟨t, rfl⟩ := hcons
  cases t with
  | nil => exact absurd hmem (by simp [chop])
  | cons e es =>
      show below c (c :: chop (e :: es)) = []
      simp [below_cons]

/-- Low on `below c'`, given that `c` heads the run. -/
theorem low_below {f : List Card} {c c' : Card}
    (hcons : ∃ t, f = c :: t) (hmem : c ∈ below c' f) :
    below c (below c' f) = [] := by
  obtain ⟨t, rfl⟩ := hcons
  by_cases hcc : c = c'
  · rw [hcc, below_cons c' c' t, ite_eq_left rfl] at hmem
    exact absurd hmem (by simp)
  · rw [below_cons c' c t, ite_eq_right hcc]
    show below c (c :: below c' t) = []
    simp [below_cons]

/-- `putRun` preserves Low when the moved run avoids `c`. -/
theorem low_putRun {W V : State} {run : List Card} {b : Base} {c : Card}
    (hV : V = W.putRun run b)
    (hlow : ∀ a, c ∈ (W.piles a).faceUp → below c ((W.piles a).faceUp) = [])
    (hnotrun : c ∉ run) :
    ∀ a, c ∈ (V.piles a).faceUp → below c ((V.piles a).faceUp) = [] := by
  intro a hmem
  rw [hV] at hmem ⊢
  cases b with
  | inl a0 =>
      have hp : (W.putRun run (Sum.inl a0)).piles a
          = (if a = a0 then (⟨[], run⟩ : Pile) else W.piles a) := by
        rw [putRun_piles_inl]
      rw [hp] at hmem ⊢
      by_cases ha : a = a0
      · rw [ite_eq_left ha] at hmem ⊢
        exact absurd (show c ∈ run from hmem) hnotrun
      · rw [ite_eq_right ha] at hmem ⊢
        exact hlow a hmem
  | inr z =>
      by_cases hz : W.pileOfTop z = none
      · rw [show W.putRun run (Sum.inr z) = W from by simp [State.putRun, hz]] at hmem ⊢
        exact hlow a hmem
      · obtain ⟨k, hk⟩ := option_some_of_ne_none hz
        have hp : (W.putRun run (Sum.inr z)).piles a
            = (if a = k then
                { W.piles k with faceUp := (W.piles k).faceUp ++ run }
                else W.piles a) := by
          rw [putRun_piles_inr W run z k hk]
        rw [hp] at hmem ⊢
        by_cases ha : a = k
        · rw [ite_eq_left ha] at hmem ⊢
          rcases List.mem_append.mp hmem with hfk | hr
          · rw [below_append_of_mem hfk]
            exact hlow k hfk
          · exact absurd hr hnotrun
        · rw [ite_eq_right ha] at hmem ⊢
          exact hlow a hmem

/-- `putCard` preserves Low when the placed card differs from `c`. -/
theorem low_putCard {W V : State} {card : Card} {b : Base} {c : Card}
    (hV : V.piles = (W.putCard card b).piles)
    (hlow : ∀ a, c ∈ (W.piles a).faceUp → below c ((W.piles a).faceUp) = [])
    (hne : c ≠ card) :
    ∀ a, c ∈ (V.piles a).faceUp → below c ((V.piles a).faceUp) = [] := by
  intro a hmem
  rw [hV] at hmem ⊢
  cases b with
  | inl a0 =>
      have hp : (W.putCard card (Sum.inl a0)).piles a
          = (if a = a0 then (⟨[], [card]⟩ : Pile) else W.piles a) := by
        rw [putCard_piles_inl]
      rw [hp] at hmem ⊢
      by_cases ha : a = a0
      · rw [ite_eq_left ha] at hmem ⊢
        rw [List.mem_singleton] at hmem
        exact absurd hmem hne
      · rw [ite_eq_right ha] at hmem ⊢
        exact hlow a hmem
  | inr z =>
      by_cases hz : W.pileOfTop z = none
      · rw [show W.putCard card (Sum.inr z) = W from by simp [State.putCard, hz]] at hmem ⊢
        exact hlow a hmem
      · obtain ⟨k, hk⟩ := option_some_of_ne_none hz
        have hp : (W.putCard card (Sum.inr z)).piles a
            = (if a = k then
                { W.piles k with faceUp := (W.piles k).faceUp ++ [card] }
                else W.piles a) := by
          rw [putCard_piles_inr W card z k hk]
        rw [hp] at hmem ⊢
        by_cases ha : a = k
        · rw [ite_eq_left ha] at hmem ⊢
          rcases List.mem_append.mp hmem with hfk | hl
          · rw [below_append_of_mem hfk]
            exact hlow k hfk
          · rw [List.mem_singleton] at hl
            exact absurd hl hne
        · rw [ite_eq_right ha] at hmem ⊢
          exact hlow a hmem

/-- **THE LOCK IS CLOSED UNDER EVERY REVERSIBLE STEP.** -/
theorem lockInv_step {U V : State} {c : Card} {h : Nat} {m : Move}
    (hwfU : U.WF) (hinv : LockInv U c h) (hidx : c.rank.toIdx = h)
    (hk : c.rank ≠ Rank.king) (hrev : reversibleAtW U m)
    (hstep : U.step m = some V) : LockInv V c h := by
  rcases m with _ | cf | ⟨cf, bf⟩ | cf | ⟨cf, bf⟩ | ⟨cf, bf⟩
  · -- draw
    have hd : U.stepDraw = some V := hstep
    refine ⟨?_, ?_, ?_⟩
    · intro a hmem
      rw [stepDraw_piles hd] at hmem ⊢
      exact hinv.1 a hmem
    · rw [stepDraw_found hd]
      exact hinv.2.1
    · rw [show rungAt V c.suit = rungAt U c.suit from by
        show (V.found c.suit).length = (U.found c.suit).length
        rw [stepDraw_found hd]]
      exact hinv.2.2
  · exact absurd hrev (wasteToFound_not_reversibleAtW U cf)
  · exact absurd hrev (wasteToTab_not_reversibleAtW U cf bf)
  · -- tabToFound cf
    obtain ⟨hnext, a, hpa, hsV⟩ := step_tabToFound_inv hstep
    obtain ⟨hF1, hF2, -⟩ := tabToFound_found_trio hsV
    have hR : tabToFoundR U cf = true := by
      have h := (reversibleOf_iff_reversibleAtW hwfU (Move.tabToFound cf)).mpr hrev
      simpa [reversibleOf] using h
    simp only [tabToFoundR, hnext, hpa] at hR
    have hseat : chop (U.piles a).faceUp ≠ []
        ∨ ((U.piles a).hidden = [] ∧ cf.rank = Rank.king) := by
      cases hchop : chop (U.piles a).faceUp with
      | cons x xs => exact Or.inl (by simp)
      | nil =>
          rw [hchop] at hR
          cases hhid : (U.piles a).hidden with
          | cons y ys =>
              rw [hhid] at hR
              exact absurd hR (by simp)
          | nil =>
              rw [hhid] at hR
              exact Or.inr ⟨rfl, of_decide_eq_true hR⟩
    have hcf_ne : c ≠ cf := by
      intro hce
      have hcan : CanRaise U c := by
        refine ⟨?_, a, ?_, ?_⟩
        · rw [hce]; exact hnext
        · rw [hce]; exact hpa
        · rw [hce]; exact hseat
      exact not_canRaise_of_lock hwfU hk hinv hcan
    refine ⟨?_, ?_, ?_⟩
    · -- Low
      intro a' hmem
      have hp : V.piles a' = (if a' = a then
          Pile.afterRunRemoved (U.piles a) (chop (U.piles a).faceUp)
          else U.piles a') := by
        rw [hsV]
      rw [hp] at hmem ⊢
      by_cases ha : a' = a
      · rw [ite_eq_left ha] at hmem ⊢
        have hpre : c ∈ chop (U.piles a).faceUp →
            below c (chop (U.piles a).faceUp) = [] := by
          intro hmemc
          have hmemf : c ∈ (U.piles a).faceUp := chop_mem hmemc
          have hlow := hinv.1 a hmemf
          exact low_chop (eq_cons_of_below_nil hmemf hlow) hmemc
        exact low_afterRunRemoved hmem hpre
      · rw [ite_eq_right ha] at hmem ⊢
        exact hinv.1 a' hmem
    · -- not founded
      by_cases hsu : cf.suit = c.suit
      · have hVf : V.found c.suit = U.found c.suit ++ [cf] := by
          rw [show c.suit = cf.suit from hsu.symm]
          exact hF1
        rw [hVf]
        intro hmem
        rcases List.mem_append.mp hmem with h | h
        · exact hinv.2.1 h
        · rw [List.mem_singleton] at h
          exact hcf_ne h
      · rw [show V.found c.suit = U.found c.suit from hF2 c.suit (Ne.symm hsu)]
        exact hinv.2.1
    · -- rung
      by_cases hsu : cf.suit = c.suit
      · have hlen : rungAt V c.suit = rungAt U c.suit + 1 := by
          show (V.found c.suit).length = (U.found c.suit).length + 1
          have hVf : V.found c.suit = U.found c.suit ++ [cf] := by
            rw [show c.suit = cf.suit from hsu.symm]
            exact hF1
          rw [hVf, List.length_append, List.length_singleton]
        rw [hlen]
        have hlt' : rungAt U c.suit < h := by
          rcases Nat.lt_or_eq_of_le hinv.2.2 with hlt | heq
          · exact hlt
          · exfalso
            have hrankC' : cf.rank.toIdx = rungAt U cf.suit := by
              have h := of_decide_eq_true (show decide
                (cf.rank.toIdx = U.foundHeight cf.suit) = true from hnext)
              simpa [State.foundHeight, rungAt] using h
            rw [hsu] at hrankC'
            have hcfc : cf = c :=
              card_eq_of_suit_rank hsu (by rw [hrankC', heq, hidx])
            have hcan : CanRaise U c := by
              refine ⟨?_, a, ?_, ?_⟩
              · rw [← hcfc]; exact hnext
              · rw [← hcfc]; exact hpa
              · rw [← hcfc]; exact hseat
            exact not_canRaise_of_lock hwfU hk hinv hcan
        omega
      · rw [show rungAt V c.suit = rungAt U c.suit from by
          show (V.found c.suit).length = (U.found c.suit).length
          rw [hF2 c.suit (Ne.symm hsu)]]
        exact hinv.2.2
  · -- foundToTab cf bf
    obtain ⟨cg, htop, hcgeq, hcp, hsV⟩ := step_foundToTab_inv hstep
    have hcg : cg ∈ U.found cf.suit :=
      lastOf_mem (show lastOf (U.found cf.suit) = some cg from htop)
    have hcfmem : cf ∈ U.found cf.suit := by
      rw [hcgeq] at hcg
      exact hcg
    have hne : c ≠ cf := by
      intro hce
      have hm : c ∈ U.found c.suit := by rw [hce]; exact hcfmem
      exact hinv.2.1 hm
    have hVp : V.piles = (U.putCard cf bf).piles := by
      rw [hsV]
      cases bf with
      | inl a0 => simp [State.putCard, State.setPile, setFound_piles]
      | inr z =>
          cases hz : U.pileOfTop z with
          | none =>
              simp [State.putCard, State.setFound_pileOfTop, setFound_piles, hz]
          | some k =>
              simp [State.putCard, State.setPile, State.setFound_pileOfTop,
                setFound_piles, hz]
    have hVf_same : cf.suit = c.suit → V.found c.suit = chop (U.found c.suit) := by
      intro hsu
      rw [hsV, putCard_found, show c.suit = cf.suit from hsu.symm,
        setFound_found_self]
    have hVf_ne : cf.suit ≠ c.suit → V.found c.suit = U.found c.suit := by
      intro hsu
      rw [hsV, putCard_found]
      exact setFound_found_ne (Ne.symm hsu)
    refine ⟨low_putCard hVp hinv.1 hne, ?_, ?_⟩
    · intro hmem
      by_cases hsu : cf.suit = c.suit
      · rw [hVf_same hsu] at hmem
        exact hinv.2.1 (chop_mem hmem)
      · rw [hVf_ne hsu] at hmem
        exact hinv.2.1 hmem
    · by_cases hsu : cf.suit = c.suit
      · rw [show rungAt V c.suit = (chop (U.found c.suit)).length from by
          show (V.found c.suit).length = (chop (U.found c.suit)).length
          rw [hVf_same hsu]]
        have hl := length_chop_le (U.found c.suit)
        have hr : (U.found c.suit).length ≤ h := hinv.2.2
        omega
      · rw [show rungAt V c.suit = rungAt U c.suit from by
          show (V.found c.suit).length = (U.found c.suit).length
          rw [hVf_ne hsu]]
        exact hinv.2.2
  · -- tabToTab cf bf
    obtain ⟨a, hhold, hcp, hne0, hsV⟩ := step_tabToTab_inv hstep
    have hfmem : cf ∈ (U.piles a).faceUp := pileHolding_mem hhold
    have hR : tabToTabR U cf bf = true := by
      have h := (reversibleOf_iff_reversibleAtW hwfU (Move.tabToTab cf bf)).mpr hrev
      simpa [reversibleOf] using h
    simp only [tabToTabR, hhold, hcp] at hR
    have hking_of_below_nil : below cf (U.piles a).faceUp = [] →
        (U.piles a).hidden = [] ∧ cf.rank = Rank.king := by
      intro hbn
      have hR' := hR
      rw [hbn] at hR'
      cases hhid : (U.piles a).hidden with
      | nil =>
          exact ⟨rfl, of_decide_eq_true (by simpa [hhid] using hR')⟩
      | cons y ys =>
          rw [hhid] at hR'
          exact absurd hR' (by simp)
    have hnotrun : c ∉ fromCard cf (U.piles a).faceUp := by
      intro hcrun
      have hcf : c ∈ (U.piles a).faceUp := mem_fromCard hcrun
      have hlowf := hinv.1 a hcf
      obtain ⟨t, hf⟩ := eq_cons_of_below_nil hcf hlowf
      by_cases hcfc : cf = c
      · have hbn : below cf (U.piles a).faceUp = [] := by rw [hcfc]; exact hlowf
        have hkcf := (hking_of_below_nil hbn).2
        exact hk (by rw [hcfc] at hkcf; exact hkcf)
      · have hfrom : fromCard cf (U.piles a).faceUp = fromCard cf t := by
          rw [hf]
          show (if c = cf then c :: t else fromCard cf t) = fromCard cf t
          exact ite_eq_right (Ne.symm hcfc)
        have hcrun' : c ∈ fromCard cf t := by rw [← hfrom]; exact hcrun
        have hct : c ∈ t := mem_fromCard hcrun'
        have hnd : (c :: t).Nodup := by rw [← hf]; exact runOK_nodup (hwfU.2.1 a)
        exact (List.nodup_cons.mp hnd).1 hct
    let W : State := U.setPile a
      (Pile.afterRunRemoved (U.piles a) (below cf (U.piles a).faceUp))
    have hWlow : ∀ a', c ∈ (W.piles a').faceUp → below c ((W.piles a').faceUp) = [] := by
      intro a' hmem
      by_cases ha : a' = a
      · have hWp : W.piles a' = Pile.afterRunRemoved (U.piles a)
            (below cf (U.piles a).faceUp) := by
          rw [ha]
          exact setPile_piles_self
        rw [hWp] at hmem ⊢
        have hpre : c ∈ below cf (U.piles a).faceUp →
            below c (below cf (U.piles a).faceUp) = [] := by
          intro hm
          have hmf : c ∈ (U.piles a).faceUp := mem_below _ hm
          exact low_below (eq_cons_of_below_nil hmf (hinv.1 a hmf)) hm
        exact low_afterRunRemoved hmem hpre
      · have hWp : W.piles a' = U.piles a' := setPile_piles_ne ha
        rw [hWp] at hmem ⊢
        exact hinv.1 a' hmem
    have hVeq : V = W.putRun (fromCard cf (U.piles a).faceUp) bf := hsV
    refine ⟨low_putRun hVeq hWlow hnotrun, ?_, ?_⟩
    · intro hmem
      rw [hsV, putRun_found, setPile_found] at hmem
      exact hinv.2.1 hmem
    · rw [show rungAt V c.suit = rungAt U c.suit from by
        show (V.found c.suit).length = (U.found c.suit).length
        rw [hsV, putRun_found, setPile_found]]
      exact hinv.2.2

/-! ## §2. Play-level closure -/

theorem lockInv_play {c : Card} {h : Nat} {F Z : State} {play : List Move}
    (hplay : ShufflePlayW F play Z) (hwf : F.WF) (hinv : LockInv F c h)
    (hidx : c.rank.toIdx = h) (hk : c.rank ≠ Rank.king) :
    Z.WF ∧ LockInv Z c h := by
  have key : ∀ (A : State) (ρ : List Move) (B : State), ShufflePlayW A ρ B →
      A.WF → LockInv A c h → B.WF ∧ LockInv B c h := by
    intro A ρ B hp
    induction hp with
    | nil st => intro hwf h; exact ⟨hwf, h⟩
    | @cons st s₁ W m ρ hlet hstep hrest ih =>
        intro hwf h
        exact ih (step_wf hwf hstep) (lockInv_step hwf h hidx hk hlet hstep)
  exact key F play Z hplay hwf hinv

/-! ## §3. The fork-side facts -/

/-- **THE COVER'S RANK SITS ONE BELOW THE PAIR.** -/
theorem cover_rank_succ {F : State} {x y d : Card} (hwf : F.WF)
    (_hxy : y = x.twin) (hd : seatOf F d = some (Sum.inr y)) :
    d.rank.toIdx + 1 = y.rank.toIdx ∧ d.suit.color ≠ y.suit.color := by
  obtain ⟨ad, hhold, -, hlast⟩ := tfc_seatOf_of_inr hd
  exact (canSitOn_eq d y).mp (tfc_seat_parent hwf hhold hlast).1

/-- The cover is face up, hence not founded. -/
theorem cover_not_found {F : State} {y d : Card} (hwf : F.WF)
    (hd : seatOf F d = some (Sum.inr y)) : d ∉ F.found d.suit := by
  obtain ⟨ad, hhold, -, -⟩ := tfc_seatOf_of_inr hd
  intro hmem
  have hfu : d ∈ (F.piles ad).faceUp := pileHolding_mem hhold
  exact ((mem_found_unique hwf hmem).1 ad).2 hfu

/-- The cover is not S-live (it is not a twin of the live pair). -/
theorem cover_not_canRaiseS {F : State} {x y d : Card} (hwf : F.WF)
    (hxy : y = x.twin) (hlive : TwinLivePair F x)
    (hd : seatOf F d = some (Sum.inr y)) : ¬ CanRaiseS F d := by
  have hr := (cover_rank_succ hwf hxy hd).1
  have hrankxy : y.rank.toIdx = x.rank.toIdx := by rw [hxy]; rfl
  intro hS
  rcases (hlive d).mp hS with h | h
  · subst h
    omega
  · subst h
    rw [show x.twin.rank = x.rank from rfl] at hr
    omega

/-- **THE COVER IS NEVER FOUNDED AT THE FORK.**  Its index is strictly above
the suit rung: if the rung reached the cover's index the cover would be a
non-king top with a nonempty under-run, hence S-live. -/
theorem cover_rung_lt_rank {F : State} {x y d : Card} (hwf : F.WF)
    (hxy : y = x.twin) (hlive : TwinLivePair F x)
    (hd : seatOf F d = some (Sum.inr y)) :
    rungAt F d.suit < d.rank.toIdx := by
  have hr := (cover_rank_succ hwf hxy hd).1
  have hnf := cover_not_found hwf hd
  have hle : rungAt F d.suit ≤ d.rank.toIdx := le_rung_of_not_found hwf hnf
  have hne : rungAt F d.suit ≠ d.rank.toIdx := by
    intro heq
    have hnext : F.nextUp d = true := by
      have h1 : d.rank.toIdx = (F.found d.suit).length := by
        rw [← heq]
        rfl
      unfold State.nextUp State.foundHeight
      rw [h1]
      simp
    obtain ⟨a, hpa⟩ := cover_top_of_fork hwf hxy hlive hd
    obtain ⟨ad, hholdd, hbne, hlastd⟩ := tfc_seatOf_of_inr hd
    have hdmemAd : d ∈ (F.piles ad).faceUp := pileHolding_mem hholdd
    have hdmemA : d ∈ (F.piles a).faceUp := Pile.mem_of_top (pileOfTop_top hpa).2
    have haad : a = ad := by
      by_cases h : a = ad
      · exact h
      · exact absurd hdmemA (mem_faceUp_unique hwf hdmemAd a h).1
    have hpa' : F.pileOfTop d = some ad := by
      rw [haad] at hpa
      exact hpa
    have hlast : lastOf (F.piles ad).faceUp = some d := (pileOfTop_top hpa').2
    have hchop : chop (F.piles ad).faceUp ≠ [] := by
      intro hc
      have hzero : below d (F.piles ad).faceUp = [] := by
        rw [lastOf_chop hlast, hc]
        simp [below_cons]
      exact hbne hzero
    have hcan : CanRaise F d := ⟨hnext, ad, hpa', Or.inl hchop⟩
    exact cover_not_canRaiseS hwf hxy hlive hd (CanRaiseS.now d hcan)
  omega

/-- The auxiliary card: the next-up card of the cover's suit, of rank
index `rungAt F d.suit`. -/
def auxCard (F : State) (d : Card) : Card :=
  ⟨d.suit, FoundKit.Rk (rungAt F d.suit)⟩

/-- The auxiliary card's rank is the cover suit's rung (needs the bound). -/
theorem auxCard_toIdx {F : State} {x y d : Card} (hwf : F.WF)
    (hxy : y = x.twin) (hlive : TwinLivePair F x)
    (hd : seatOf F d = some (Sum.inr y)) :
    (auxCard F d).rank.toIdx = rungAt F d.suit := by
  have hlt := cover_rung_lt_rank hwf hxy hlive hd
  have hlt13 : rungAt F d.suit < 13 := by
    have hdr : d.rank.toIdx < 13 := Rank.toIdx_lt d.rank
    omega
  exact FoundKit.Rk_toIdx _ hlt13

/-- The auxiliary card `c` of the freeze: the next-up card of the cover's
suit, of rank index `rungAt F d.suit`.  It is not a king. -/
theorem aux_rank_ne_king {F : State} {x y d : Card} (hwf : F.WF)
    (hxy : y = x.twin) (hlive : TwinLivePair F x)
    (hd : seatOf F d = some (Sum.inr y)) :
    (auxCard F d).rank ≠ Rank.king := by
  have hr := (cover_rank_succ hwf hxy hd).1
  have hlt := cover_rung_lt_rank hwf hxy hlive hd
  have hdr : d.rank.toIdx < 13 := Rank.toIdx_lt d.rank
  have hidx : (auxCard F d).rank.toIdx = rungAt F d.suit :=
    auxCard_toIdx hwf hxy hlive hd
  intro hk
  rw [hk] at hidx
  have h12 : (Rank.king).toIdx = 12 := rfl
  omega

/-- **THE AUXILIARY CARD IS NOT S-LIVE AT THE FORK.** -/
theorem aux_not_canRaiseS {F : State} {x y d : Card} (hwf : F.WF)
    (hxy : y = x.twin) (hlive : TwinLivePair F x)
    (hd : seatOf F d = some (Sum.inr y)) :
    ¬ CanRaiseS F (auxCard F d) := by
  have hr := (cover_rank_succ hwf hxy hd).1
  have hlt := cover_rung_lt_rank hwf hxy hlive hd
  have hidx : (auxCard F d).rank.toIdx = rungAt F d.suit :=
    auxCard_toIdx hwf hxy hlive hd
  have hrankxy : y.rank.toIdx = x.rank.toIdx := by rw [hxy]; rfl
  intro hS
  rcases (hlive (auxCard F d)).mp hS with h | h
  · rw [h] at hidx
    omega
  · rw [h] at hidx
    rw [show x.twin.rank = x.rank from rfl] at hidx
    omega

/-- **THE AUXILIARY CARD IS NOT COVERED AT THE FORK** — any card sitting on
it has the pair's colour and a rank strictly below the pair's, hence is
already founded, contradicting its being face up. -/
theorem aux_not_covered {F : State} {x y d : Card} (hwf : F.WF)
    (hxy : y = x.twin) (hlive : TwinLivePair F x)
    (hd : seatOf F d = some (Sum.inr y)) :
    ¬ CoveredAt F (auxCard F d) := by
  have hr := (cover_rank_succ hwf hxy hd).1
  have hcolD := (cover_rank_succ hwf hxy hd).2
  have hlt := cover_rung_lt_rank hwf hxy hlive hd
  have hidx : (auxCard F d).rank.toIdx = rungAt F d.suit :=
    auxCard_toIdx hwf hxy hlive hd
  have hx : ForkWitness F x := by
    refine ⟨fun z => (hlive z).symm, ?_⟩
    rw [← hxy]
    exact not_canRaise_of_covered hwf ⟨d, hd⟩
  rintro ⟨e, heseat⟩
  obtain ⟨ae, hholde, -, hlaste⟩ := tfc_seatOf_of_inr heseat
  have hfit : canSitOn e (auxCard F d) = true :=
    (tfc_seat_parent hwf hholde hlaste).1
  obtain ⟨hrankE, hcolE⟩ := (canSitOn_eq e (auxCard F d)).mp hfit
  have hcolc : (auxCard F d).suit.color ≠ y.suit.color := by
    show d.suit.color ≠ y.suit.color
    exact hcolD
  have hcol : e.suit.color = y.suit.color := by
    revert hcolE hcolc
    generalize (auxCard F d).suit.color = cc
    generalize y.suit.color = yy
    generalize e.suit.color = ee
    intro h1 h2
    cases ee <;> cases cc <;> cases yy <;> simp_all
  have hltE : e.rank.toIdx < x.rank.toIdx := by
    have hrankxy : y.rank.toIdx = x.rank.toIdx := by rw [hxy]; rfl
    omega
  have hcolx : e.suit.color = x.suit.color := by
    rw [hcol, hxy]
    exact Suit.color_twin x.suit
  have hfound : e ∈ F.found e.suit := pair_lowFamily_founded hwf hx hcolx hltE
  have hfu : e ∈ (F.piles ae).faceUp := pileHolding_mem hholde
  exact ((mem_found_unique hwf hfound).1 ae).2 hfu

/-- **THE AUXILIARY CARD'S LOCK AT THE FORK.** -/
theorem aux_lock {F : State} {x y d : Card} (hwf : F.WF)
    (hxy : y = x.twin) (hlive : TwinLivePair F x)
    (hd : seatOf F d = some (Sum.inr y)) :
    LockInv F (auxCard F d) (rungAt F d.suit) := by
  obtain ⟨hr, -⟩ := cover_rank_succ hwf hxy hd
  have hlt := cover_rung_lt_rank hwf hxy hlive hd
  have hidx : (auxCard F d).rank.toIdx = rungAt F d.suit :=
    auxCard_toIdx hwf hxy hlive hd
  have hS := aux_not_canRaiseS hwf hxy hlive hd
  have hcov := aux_not_covered hwf hxy hlive hd
  have hnf : (auxCard F d) ∉ F.found (auxCard F d).suit := by
    intro hf
    have hlt' := (FoundKit.mem_found_iff_height hwf).mp hf
    rw [hidx] at hlt'
    exact Nat.lt_irrefl _ hlt'
  refine ⟨?_, hnf, Nat.le_refl _⟩
  intro a hmem
  -- c is the last face-up card of pile a
  have hlast : lastOf (F.piles a).faceUp = some (auxCard F d) := by
    obtain ⟨tr, hfc⟩ :=
      tfc_fromCard_cons_head (c := auxCard F d) (F.piles a).faceUp hmem
    cases tr with
    | nil =>
        have hsingle : fromCard (auxCard F d) (F.piles a).faceUp
            = [auxCard F d] := by simpa using hfc
        have h0 := tfc_below_fromCard (auxCard F d) (F.piles a).faceUp
        rw [hsingle] at h0
        rw [← h0]
        exact lastOf_snoc
    | cons e rest =>
        exfalso
        have hface : (F.piles a).faceUp
            = below (auxCard F d) (F.piles a).faceUp
              ++ auxCard F d :: e :: rest := by
          have h0 := tfc_below_fromCard (auxCard F d) (F.piles a).faceUp
          rw [hfc] at h0
          exact h0.symm
        exact hcov ⟨e, by
          have hnd : (F.piles a).faceUp.Nodup := runOK_nodup (hwf.2.1 a)
          have hsplit : below (auxCard F d) (F.piles a).faceUp
              ++ auxCard F d :: e :: rest = (F.piles a).faceUp := hface.symm
          have hnd' : (below (auxCard F d) (F.piles a).faceUp
              ++ auxCard F d :: e :: rest).Nodup := by rw [hsplit]; exact hnd
          have hnot : e ∉ below (auxCard F d) (F.piles a).faceUp := by
            intro hmem'
            exact (((List.nodup_append.1 hnd').2.2 e hmem') e
              (List.mem_cons_of_mem _ (List.mem_cons_self ..))) rfl
          have htail : (auxCard F d :: e :: rest).Nodup :=
            (List.nodup_append.1 hnd').2.1
          have hcnot : auxCard F d ∉ e :: rest := (List.nodup_cons.1 htail).1
          have hcne : auxCard F d ≠ e := fun hce =>
            hcnot (by rw [hce]; exact List.mem_cons_self ..)
          have hstep : below e (auxCard F d :: e :: rest) = [auxCard F d] := by
            show (if auxCard F d = e then []
              else auxCard F d :: below e (e :: rest)) = [auxCard F d]
            rw [ite_eq_right hcne]
            show auxCard F d :: (if e = e then [] else e :: below e rest)
              = [auxCard F d]
            rw [ite_eq_left rfl]
          have hbel : below e (F.piles a).faceUp
              = below (auxCard F d) (F.piles a).faceUp ++ [auxCard F d] := by
            calc below e (F.piles a).faceUp
                = below e (below (auxCard F d) (F.piles a).faceUp
                    ++ auxCard F d :: e :: rest) := congrArg (below e) hface
              _ = below (auxCard F d) (F.piles a).faceUp
                    ++ below e (auxCard F d :: e :: rest) :=
                  below_append_notmem hnot _
              _ = below (auxCard F d) (F.piles a).faceUp
                    ++ [auxCard F d] := by rw [hstep]
          have hlastE : lastOf (below e (F.piles a).faceUp) = some (auxCard F d) := by
            rw [hbel]; exact lastOf_snoc
          have heMem : e ∈ (F.piles a).faceUp := by
            rw [hface]
            exact List.mem_append.mpr
              (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons_self ..))))
          have hholdE : F.pileHolding e = some a :=
            (pileHolding_eq_some_iff hwf).2 heMem
          exact tfc_seatOf_inr_intro hholdE hlastE⟩
  -- if the rung were at c's index, c would top a pile with a nonempty chop
  have hnext : F.nextUp (auxCard F d) = true := by
    show decide ((auxCard F d).rank.toIdx = F.foundHeight (auxCard F d).suit) = true
    rw [hidx]
    exact decide_eq_true rfl
  have hpa : F.pileOfTop (auxCard F d) = some a :=
    (pileOfTop_eq_some_iff hwf).2
      (show (F.piles a).top = some (auxCard F d) from hlast)
  have hchop : chop (F.piles a).faceUp = [] := by
    by_cases hc : chop (F.piles a).faceUp = []
    · exact hc
    · exact False.elim (hS (CanRaiseS.now (auxCard F d) ⟨hnext, a, hpa, Or.inl hc⟩))
  rw [lastOf_chop hlast, hchop, List.nil_append, below_cons, ite_eq_left rfl]

/-- **THE FROZEN COVER RUNG (target 1).**  Along every witness play from
the fork, the cover's suit rung never exceeds its at-fork value, and the
cover is never founded. -/
theorem cover_rung_frozen {F : State} {x y d : Card} (hwf : F.WF)
    (hxy : y = x.twin) (hlive : TwinLivePair F x)
    (hd : seatOf F d = some (Sum.inr y)) :
    ∀ {play : List Move} {Z : State}, ShufflePlayW F play Z →
      rungAt Z d.suit ≤ rungAt F d.suit ∧ d ∉ Z.found d.suit := by
  intro play Z hplay
  have hinv : LockInv F (auxCard F d) (rungAt F d.suit) := aux_lock hwf hxy hlive hd
  have hidx : (auxCard F d).rank.toIdx = rungAt F d.suit :=
    auxCard_toIdx hwf hxy hlive hd
  have hk : (auxCard F d).rank ≠ Rank.king := aux_rank_ne_king hwf hxy hlive hd
  obtain ⟨hwfZ, hinvZ⟩ := lockInv_play hplay hwf hinv hidx hk
  have hle : rungAt Z d.suit ≤ rungAt F d.suit := hinvZ.2.2
  have hlt := cover_rung_lt_rank hwf hxy hlive hd
  refine ⟨hle, ?_⟩
  intro hmem
  have hltZ := (FoundKit.mem_found_iff_height hwfZ).mp hmem
  omega

/-! ## §4. The cover token invariant -/

/-- The cover's seat moves at most to the pair partner. -/
theorem seat_lock_step {U V : State} {c d x y : Card} {h : Nat} {m : Move}
    (hwfU : U.WF) (hstep : U.step m = some V) (hrev : reversibleAtW U m)
    (hinv : LockInv U c h) (hidx : c.rank.toIdx = h) (hk : c.rank ≠ Rank.king)
    (hsuit : c.suit = d.suit) (hdlt : h < d.rank.toIdx) (hdk : d.rank ≠ Rank.king)
    (hbase : ∀ z, canSitOn d z = true → z = x ∨ z = y)
    (hseat : seatOf U d = some (Sum.inr x) ∨ seatOf U d = some (Sum.inr y)) :
    LockInv V c h ∧
      (seatOf V d = some (Sum.inr x) ∨ seatOf V d = some (Sum.inr y)) := by
  have hinvV := lockInv_step hwfU hinv hidx hk hrev hstep
  refine ⟨hinvV, ?_⟩
  have hrU : rungAt U d.suit ≤ h := by
    rw [← hsuit]
    exact hinv.2.2
  have hfoundU : d ∉ U.found d.suit := by
    intro hmem
    have hl := (FoundKit.mem_found_iff_height hwfU).mp hmem
    omega
  have hnotnext : U.nextUp d = false := by
    have hrlt : rungAt U d.suit < d.rank.toIdx := by omega
    have hne : ¬ (d.rank.toIdx = U.foundHeight d.suit) := by
      intro heq
      have : d.rank.toIdx = rungAt U d.suit := by
        simpa [State.foundHeight, rungAt] using heq
      omega
    exact decide_false_of_not hne
  have hseatne : seatOf U d ≠ none := by
    rcases hseat with h | h <;> rw [h] <;> simp
  rcases m with _ | cf | ⟨cf, bf⟩ | cf | ⟨cf, bf⟩ | ⟨cf, bf⟩
  · -- draw
    have hd := hstep
    have hsp := seatOf_congr_piles (stepDraw_piles hd) d
    rw [hsp]
    exact hseat
  · exact absurd hrev (wasteToFound_not_reversibleAtW U cf)
  · exact absurd hrev (wasteToTab_not_reversibleAtW U cf bf)
  · -- tabToFound cf
    obtain ⟨hnext, a, hpa, hsV⟩ := step_tabToFound_inv hstep
    have hcd : d ≠ cf := by
      intro hdc
      have h1 : U.nextUp d = true := by rw [← hdc] at hnext; exact hnext
      rw [hnotnext] at h1
      exact absurd h1 (by simp)
    rw [raise_seat_change_of_seated hstep hrev hseatne hcd]
    exact hseat
  · -- foundToTab cf bf
    obtain ⟨cg, htop, hcgeq, hcp, hsV⟩ := step_foundToTab_inv hstep
    have hcg : cg ∈ U.found cf.suit :=
      lastOf_mem (show lastOf (U.found cf.suit) = some cg from htop)
    have hcfmem : cf ∈ U.found cf.suit := by
      rw [hcgeq] at hcg
      exact hcg
    have hcd : d ≠ cf := by
      intro hdc
      have hm : d ∈ U.found d.suit := by rw [hdc]; exact hcfmem
      exact hfoundU hm
    rw [pull_seat_change hstep d hcd]
    exact hseat
  · -- tabToTab cf bf
    obtain ⟨a, hhold, hcp, hne0, hsV⟩ := step_tabToTab_inv hstep
    by_cases hdc : d = cf
    · have hsp := tfc_seat_point_edit hwfU hstep hrev d
      rw [ite_eq_left hdc] at hsp
      rw [hsp]
      rw [← hdc] at hcp
      cases bf with
      | inl a' =>
          exact absurd (canPlace_inl hcp).2 hdk
      | inr z =>
          obtain ⟨k, hkz, hfit⟩ := canPlace_inr hcp
          rcases hbase z hfit with hz | hz
          · left; rw [hz]
          · right; rw [hz]
    · have hsp := tfc_seat_point_edit hwfU hstep hrev d
      rw [ite_eq_right hdc] at hsp
      rw [hsp]
      exact hseat

theorem seat_lock_play {c d x y : Card} {h : Nat} {F Z : State} {play : List Move}
    (hplay : ShufflePlayW F play Z) (hwf : F.WF)
    (hinv : LockInv F c h) (hidx : c.rank.toIdx = h) (hk : c.rank ≠ Rank.king)
    (hsuit : c.suit = d.suit) (hdlt : h < d.rank.toIdx) (hdk : d.rank ≠ Rank.king)
    (hbase : ∀ z, canSitOn d z = true → z = x ∨ z = y)
    (hseat : seatOf F d = some (Sum.inr x) ∨ seatOf F d = some (Sum.inr y)) :
    Z.WF ∧ LockInv Z c h ∧
      (seatOf Z d = some (Sum.inr x) ∨ seatOf Z d = some (Sum.inr y)) := by
  have key : ∀ (A : State) (ρ : List Move) (B : State), ShufflePlayW A ρ B →
      A.WF → LockInv A c h →
      (seatOf A d = some (Sum.inr x) ∨ seatOf A d = some (Sum.inr y)) →
      B.WF ∧ LockInv B c h ∧
        (seatOf B d = some (Sum.inr x) ∨ seatOf B d = some (Sum.inr y)) := by
    intro A ρ B hp
    induction hp with
    | nil st => intro hwf hi hse; exact ⟨hwf, hi, hse⟩
    | @cons st s₁ W m ρ hlet hstep hrest ih =>
        intro hwf hi hse
        obtain ⟨hi1, hse1⟩ :=
          seat_lock_step hwf hstep hlet hi hidx hk hsuit hdlt hdk hbase hse
        exact ih (step_wf hwf hstep) hi1 hse1
  exact key F play Z hplay hwf hinv hseat

/-- **THE COVER TOKEN INVARIANT (target 2).**  At every witness
descendant of the fork, the cover sits on one of the two twins. -/
theorem cover_token_invariant {F : State} {x y d : Card} (hwf : F.WF)
    (hxy : y = x.twin) (hlive : TwinLivePair F x)
    (hd : seatOf F d = some (Sum.inr y)) :
    ∀ {play : List Move} {Z : State}, ShufflePlayW F play Z →
      seatOf Z d = some (Sum.inr x) ∨ seatOf Z d = some (Sum.inr y) := by
  intro play Z hplay
  have hinv : LockInv F (auxCard F d) (rungAt F d.suit) := aux_lock hwf hxy hlive hd
  have hidx : (auxCard F d).rank.toIdx = rungAt F d.suit :=
    auxCard_toIdx hwf hxy hlive hd
  have hk : (auxCard F d).rank ≠ Rank.king := aux_rank_ne_king hwf hxy hlive hd
  have hdlt := cover_rung_lt_rank hwf hxy hlive hd
  have hdk := cover_rank_ne_king hwf hd
  have hbase : ∀ z, canSitOn d z = true → z = x ∨ z = y :=
    fun z hz => cover_base_is_twin hwf hxy hd hz
  have hseat : seatOf F d = some (Sum.inr x) ∨ seatOf F d = some (Sum.inr y) :=
    Or.inr hd
  exact (seat_lock_play (c := auxCard F d) (d := d) (x := x) (y := y)
    (h := rungAt F d.suit) hplay hwf hinv hidx hk rfl hdlt hdk hbase hseat).2.2

/-! ## §5. WF transit and the one-founding invariant -/

/-- WF travels a witness shuffle. -/
theorem wf_of_shuffle {a b : State} {play : List Move}
    (h : ShufflePlayW a play b) (hwf : a.WF) : b.WF := by
  have key : ∀ (A : State) (ρ : List Move) (B : State), ShufflePlayW A ρ B →
      A.WF → B.WF := by
    intro A ρ B hp
    induction hp with
    | nil st => intro hw; exact hw
    | @cons st s1 W m ρ hlet hstep hrest ih =>
        intro hw
        exact ih (step_wf hw hstep)
  exact key a play b h hwf

/-- **THE ONE-FOUNDING INVARIANT (target 3)** — in a macro class
containing a fork, the two pair-suit rungs never both exceed their
at-fork values. -/
theorem forkState_one_founding_orig2 {st st' : State} (hwf : st.WF)
    (_h : forkState st) (hjourney : sameOrbitSetoid.r st st')
    (x : Card) (hx : ForkWitness st x) :
    ¬ (rungAt st' x.suit > rungAt st x.suit ∧
       rungAt st' x.twin.suit > rungAt st x.twin.suit) := by
  intro ⟨hA, hB⟩
  have hlive : TwinLivePair st x := fun c => (hx.1 c).symm
  have hyS : CanRaiseS st x.twin := (hx.1 x.twin).mp (Or.inr rfl)
  have hcov : CoveredAt st x.twin :=
    (forkWitness_iff_covered (y := x.twin) hwf rfl hlive hyS).mp hx
  obtain ⟨d, hd⟩ := hcov
  obtain ⟨σ, hσ, play, hplay⟩ : RevEqW st' st := hjourney
  have hwf' : st'.WF := wf_of_shuffle hplay hwf
  have hr0 : rungAt st x.suit = x.rank.toIdx :=
    (forkState_witness_rungs hx).1
  have hr1 : rungAt st x.twin.suit = x.rank.toIdx :=
    (forkState_witness_rungs hx).2
  have hxfound : x ∈ st'.found x.suit := by
    apply FoundKit.mem_found_of_rung hwf'
    rw [hr0] at hA
    omega
  have hxtfound : x.twin ∈ st'.found x.twin.suit := by
    apply FoundKit.mem_found_of_rung hwf'
    have htr : x.twin.rank.toIdx = x.rank.toIdx := rfl
    rw [hr1] at hB
    omega
  have hseat : seatOf st' d = some (Sum.inr x) ∨
      seatOf st' d = some (Sum.inr x.twin) :=
    cover_token_invariant (x := x) (y := x.twin) (d := d) hwf rfl hlive hd hplay
  rcases hseat with hs | hs
  · obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hs
    have hmem : x ∈ (st'.piles a).faceUp := mem_below _ (lastOf_mem hlast)
    exact ((mem_found_unique hwf' hxfound).1 a).2 hmem
  · obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hs
    have hmem : x.twin ∈ (st'.piles a).faceUp := mem_below _ (lastOf_mem hlast)
    exact ((mem_found_unique hwf' hxtfound).1 a).2 hmem

/-- **ONE FOUNDING HOLDS** — the class-grade packaging. -/
theorem OneFounding_holds : OneFounding :=
  fun _st _st' _x hwf hfork hcls hx =>
    forkState_one_founding_orig2 hwf hfork hcls _x hx

/-- **COVER TOKEN HOLDS** — the repo's `CoverToken` residue, discharged. -/
theorem CoverToken_holds : CoverToken :=
  fun _F _Z x y d _ρ hwf hxy hlive hd hplay =>
    cover_token_invariant (x := x) (y := y) (d := d) hwf hxy hlive hd hplay

/-- **THE FROZEN CLASS THEOREM, UNCONDITIONALLY** — the fork pair is
unique up to the twin flip in any macro class (the frozen
`fork_label_class`). -/
theorem fork_label_class {F G : State} (hwfF : F.WF) (hwfG : G.WF)
    (hcls : sameOrbitSetoid.r F G) {w v : Card}
    (hw : ForkWitness F w) (hv : ForkWitness G v) :
    v = w ∨ v = w.twin :=
  fork_label_class_of_token_and_oneFounding CoverToken_holds OneFounding_holds
    hwfF hwfG hcls hw hv

/-- **THE TWIN-PAIR FOUNDS AGREE, UNCONDITIONALLY.** -/
theorem twinPair_founds {F G : State} (hwfF : F.WF) (hwfG : G.WF)
    (hcls : sameOrbitSetoid.r F G) {w v : Card}
    (hw : ForkWitness F w) (hv : ForkWitness G v) :
    F.found w.suit = G.found w.suit ∧
      F.found w.twin.suit = G.found w.twin.suit :=
  twinPair_founds_of_token_and_oneFounding CoverToken_holds OneFounding_holds
    hwfF hwfG hcls hw hv

/-- **THE RANK CEILING (target 4a).** -/
theorem sameFamily_rankCeiling_orig2 {st st' : State} (hwf : st.WF)
    (hwf' : st'.WF) (h : forkState st) (hcls : sameOrbitSetoid.r st st')
    (x : Card) (hx : ForkWitness st x) {y : Card} (hy : ForkWitness st' y)
    (hys : y.suit = x.suit ∨ y.suit = x.twin.suit) :
    y.rank.toIdx ≤ x.rank.toIdx :=
  rankCeiling_of_oneFounding OneFounding_holds hwf hwf' h hcls x hx hy hys

/-- **THE RANK FLOOR (target 4b).** -/
theorem family_rankFloor_orig2 {st st' : State} (hwf : st.WF)
    (hwf' : st'.WF) (h : forkState st) (hcls : sameOrbitSetoid.r st st')
    (x : Card) (hx : ForkWitness st x) {y : Card} (hy : ForkWitness st' y)
    (hys : y.suit = x.suit ∨ y.suit = x.twin.suit) :
    x.rank.toIdx ≤ y.rank.toIdx :=
  rankFloor_of_oneFounding OneFounding_holds hwf hwf' h hcls x hx hy hys

/-- **SAME-FAMILY FORK PAIRS AGREE (target 4c).** -/
theorem family_pairClass_orig2 {st st' : State} (hwf : st.WF)
    (hwf' : st'.WF) (h : forkState st) (hcls : sameOrbitSetoid.r st st')
    (x : Card) (hx : ForkWitness st x) {y : Card} (hy : ForkWitness st' y)
    (hys : y.suit = x.suit ∨ y.suit = x.twin.suit) :
    y.rank.toIdx = x.rank.toIdx ∧ (y = x ∨ y = x.twin) :=
  family_pairClass_of_oneFounding OneFounding_holds hwf hwf' h hcls x hx hy hys

/-- **THE COVER-SUIT RUNG IS CLASS-INVARIANT (same orientation).**
With the same witness `x` and the cover `d` on `x.twin` at both ends,
`cover_rung_frozen` reads the inequality in both directions.  The
general orientation is the both-covered lock; the fourth suit
(`d.twin.suit`) is not covered by this row. -/
theorem coverSuit_rung_eq_of_sameOrientation
    {F G : State} (hwfF : F.WF) (hwfG : G.WF)
    (hcls : sameOrbitSetoid.r F G)
    {x d : Card} (hx : ForkWitness F x)
    (hd : seatOf F d = some (Sum.inr x.twin))
    (hxG : ForkWitness G x)
    (hdG : seatOf G d = some (Sum.inr x.twin)) :
    rungAt G d.suit = rungAt F d.suit := by
  obtain ⟨σ, hσ, τ, hτ⟩ := hcls
  have hliveF : TwinLivePair F x := ((forkWitness_iff F x).mp hx).1
  have hliveG : TwinLivePair G x := ((forkWitness_iff G x).mp hxG).1
  have h1 := (cover_rung_frozen hwfF rfl hliveF hd hτ).1
  have h2 := (cover_rung_frozen hwfG rfl hliveG hdG hσ).1
  omega

/-! ## §6. The audit battery -/

#print axioms cover_rung_frozen
#print axioms cover_token_invariant
#print axioms CoverToken_holds
#print axioms OneFounding_holds
#print axioms forkState_one_founding_orig2
#print axioms fork_label_class
#print axioms twinPair_founds
#print axioms sameFamily_rankCeiling_orig2
#print axioms family_rankFloor_orig2
#print axioms family_pairClass_orig2
#print axioms coverSuit_rung_eq_of_sameOrientation