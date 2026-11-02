import Orig2.Fork.Third.ForkFace1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# CrossSuit_Face2 — the window's tableau transport, and the unconditional twin cover

READ-ONLY scratch card (`Temp/`).  No source edit, no commit.  Zero `sorry`,
zero `Classical.choice`, zero `native_decide`; battery at the tail.

## What this card proves

Face 1's twin-cover theorem (`CrossSuitF1.cover_is_twin`) carried one
hypothesis: that the buried base card `z` is face-up covered at the window's
start `B`.  This card discharges it.

* §1 `mem_fromCard` — the run from a card is a sublist.
* §2 the `setPile`/`putRun` pile equations — placement is pile surgery:
  `inl` overwrites the empty pile with the run, `inr` appends the run to the
  base pile's face-up, everything else is untouched.
* §3 `mem_of_afterRunRemoved` + **the reveal ban** — a *reversible* slide
  never empties a face-up prefix over a nonempty hidden stack: such a slide
  strictly drops `hiddenTotal` (`hiddenTotal_step_tabToTab_reveal`), which
  no step ever raises (`hiddenTotal_step`), so it is a commitment
  (`irr_of_desc`), contradicting the witness play's per-letter
  reversibility.  So the afterRunRemoved source pile keeps exactly its
  below-prefix.
* §4 **the backward slide transport** — a reversible slide preserves
  face-up membership: a card face-up after the slide was face-up before
  (it was either unmoved, in the below-prefix, or in the moved run, which
  is a sublist of the source).
* §5 `faceUp_of_pileOfTop` — a pile top is face-up (`firstWhere_sound` +
  `Pile.top = lastOf` + `lastOf_mem`).
* §6 **the window transport** — a free window preserves face-up membership
  backwards (draws do not touch piles; slides by §4).
* §7 **THE UNCONDITIONAL TWIN COVER** — `cover_is_twin'`: face 1b needs no
  `hface` hypothesis anymore.  The cover on the prepared seat is exactly
  `d.twin`, always.
-/

namespace CrossSuitF2

/-! ## §1. The run is a sublist -/

theorem mem_fromCard : ∀ (c x : Card) (l : List Card),
    x ∈ fromCard c l → x ∈ l := by
  intro c x l
  induction l with
  | nil => intro hm; exact absurd hm (by simp [fromCard])
  | cons y t ih =>
      intro hm
      have hm' : x ∈ (if y = c then y :: t else fromCard c t) := hm
      by_cases hyc : y = c
      · rw [if_pos hyc] at hm'; exact hm'
      · rw [if_neg hyc] at hm'; exact List.mem_cons_of_mem _ (ih hm')

/-! ## §2. The pile equations of placement -/

theorem setPile_piles_self (st : State) (a : Anchor) (p : Pile) :
    (st.setPile a p).piles a = p := by
  show (if a = a then p else st.piles a) = p
  rw [if_pos rfl]

theorem setPile_piles_ne {st : State} {a a' : Anchor} (p : Pile) (h : a' ≠ a) :
    (st.setPile a p).piles a' = st.piles a' := by
  show (if a' = a then p else st.piles a') = st.piles a'
  rw [if_neg h]

theorem putRun_inl_eq (st : State) (run : List Card) (a : Anchor) :
    st.putRun run (Sum.inl a) = st.setPile a ⟨[], run⟩ := rfl

theorem putRun_inr_some {st : State} {run : List Card} {y : Card} {k : Anchor}
    (h : st.pileOfTop y = some k) :
    st.putRun run (Sum.inr y)
      = st.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ run } := by
  show (match st.pileOfTop y with
      | some k => st.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ run }
      | none => st) = _
  rw [h]

theorem putRun_inr_none {st : State} {run : List Card} {y : Card}
    (h : st.pileOfTop y = none) : st.putRun run (Sum.inr y) = st := by
  show (match st.pileOfTop y with
      | some k => st.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ run }
      | none => st) = st
  rw [h]

/-! ## §3. The reveal ban and the source pile's face-up -/

/-- **A REVERSIBLE SLIDE NEVER REVEALS.**  Emptying the from-pile's face-up
prefix over a nonempty hidden stack strictly drops `hiddenTotal` — a
commitment, since no step ever raises it (`Kit.not_W_of_desc`) —
contradicting the witness play's per-letter reversibility. -/
theorem slide_reveal_irrev {st s' : State} {c : Card} {b : Base} {a : Anchor}
    (hstep : State.step st (Move.tabToTab c b) = some s')
    (hh : st.pileHolding c = some a)
    (hbl : below c (st.piles a).faceUp = [])
    (hhne : (st.piles a).hidden ≠ []) : ¬ reversibleAtW st (Move.tabToTab c b) := by
  intro hrev
  have hdrop : hiddenTotal s' < hiddenTotal st := by
    have h1 := hiddenTotal_step_tabToTab_reveal hstep hh hbl hhne
    omega
  exact not_W_of_desc hiddenTotal (fun s m s' hst => hiddenTotal_step hst)
    hstep hdrop hrev

/-- The source pile of a non-revealing run removal keeps exactly its
below-prefix. -/
theorem mem_of_afterRunRemoved {p : Pile} {pre : List Card} {z : Card}
    (hban : pre = [] → p.hidden = [])
    (hz : z ∈ (Pile.afterRunRemoved p pre).faceUp) : z ∈ pre := by
  cases pre with
  | nil =>
      simp only [Pile.afterRunRemoved, Pile.revealTop, hban rfl] at hz
      exact absurd hz (by simp)
  | cons w t => exact hz

/-! ## §4. The backward slide transport -/

/-- **A REVERSIBLE SLIDE PRESERVES FACE-UP MEMBERSHIP.**  A card face-up
after the slide was face-up before: it was either unmoved (any pile other
than the two touched), in the source's below-prefix, or in the moved run —
and the run is a sublist of the source. -/
theorem faceUp_of_slide {st s' : State} {c : Card} {b : Base} {z : Card}
    (hstep : State.step st (Move.tabToTab c b) = some s')
    (hrev : reversibleAtW st (Move.tabToTab c b))
    (hz : ∃ a : Anchor, z ∈ (s'.piles a).faceUp) :
    ∃ a : Anchor, z ∈ (st.piles a).faceUp := by
  obtain ⟨a₀, hh, -, -, hs⟩ := step_tabToTab_inv hstep
  have hban : below c (st.piles a₀).faceUp = [] → (st.piles a₀).hidden = [] := by
    intro hbl
    by_cases hhid : (st.piles a₀).hidden = []
    · exact hhid
    · exact absurd hrev (slide_reveal_irrev hstep hh hbl hhid)
  obtain ⟨a, hza⟩ := hz
  rw [hs] at hza
  cases b with
  | inl a' =>
      rw [putRun_inl_eq] at hza
      by_cases ha : a = a'
      · rw [ha, setPile_piles_self] at hza
        exact ⟨a₀, mem_fromCard c z (st.piles a₀).faceUp hza⟩
      · by_cases ha0 : a = a₀
        · rw [ha0, setPile_piles_ne _ (fun h => ha (ha0.trans h)),
              setPile_piles_self] at hza
          exact ⟨a₀, mem_below (st.piles a₀).faceUp
            (mem_of_afterRunRemoved hban hza)⟩
        · rw [setPile_piles_ne _ ha, setPile_piles_ne _ ha0] at hza
          exact ⟨a, hza⟩
  | inr y =>
      cases hpot : (st.setPile a₀
          (Pile.afterRunRemoved (st.piles a₀)
            (below c (st.piles a₀).faceUp))).pileOfTop y with
      | none =>
          rw [putRun_inr_none hpot] at hza
          by_cases ha0 : a = a₀
          · rw [ha0, setPile_piles_self] at hza
            exact ⟨a₀, mem_below (st.piles a₀).faceUp
              (mem_of_afterRunRemoved hban hza)⟩
          · rw [setPile_piles_ne _ ha0] at hza
            exact ⟨a, hza⟩
      | some k =>
          rw [putRun_inr_some hpot] at hza
          by_cases hak : a = k
          · rw [hak, setPile_piles_self] at hza
            rcases List.mem_append.mp hza with hz1 | hz2
            · by_cases hk0 : k = a₀
              · rw [hk0, setPile_piles_self] at hz1
                exact ⟨a₀, mem_below (st.piles a₀).faceUp
                  (mem_of_afterRunRemoved hban hz1)⟩
              · rw [setPile_piles_ne _ hk0] at hz1
                exact ⟨k, hz1⟩
            · exact ⟨a₀, mem_fromCard c z (st.piles a₀).faceUp hz2⟩
          · by_cases ha0 : a = a₀
            · rw [ha0, setPile_piles_ne _ (fun h => hak (ha0.trans h)),
                  setPile_piles_self] at hza
              exact ⟨a₀, mem_below (st.piles a₀).faceUp
                (mem_of_afterRunRemoved hban hza)⟩
            · rw [setPile_piles_ne _ hak, setPile_piles_ne _ ha0] at hza
              exact ⟨a, hza⟩

/-! ## §5. A pile top is face-up -/

theorem faceUp_of_pileOfTop {st : State} {z : Card}
    (h : st.pileOfTop z ≠ none) : ∃ a : Anchor, z ∈ (st.piles a).faceUp := by
  cases hp : st.pileOfTop z with
  | some a =>
      have hp' : firstWhere (fun a' => decide (st.topOf a' = some z)) Anchor.all
          = some a := hp
      have h1 := firstWhere_sound (fun a' => decide (st.topOf a' = some z)) hp'
      have h3 : lastOf ((st.piles a).faceUp) = some z := of_decide_eq_true h1
      exact ⟨a, lastOf_mem h3⟩
  | none => exact absurd hp h

/-! ## §6. The window transport -/

/-- **A FREE WINDOW PRESERVES FACE-UP MEMBERSHIP BACKWARDS.**  Draws do not
touch the piles; slides permute cards between them (§4); so a card that is
face-up at the window's end was face-up at its start. -/
theorem faceUp_window_back :
    ∀ (γ : List Move) {Q P : State},
      ShufflePlayW Q γ P → Canon.FreeOnly γ →
      ∀ z : Card, (∃ a : Anchor, z ∈ (P.piles a).faceUp) →
        (∃ a : Anchor, z ∈ (Q.piles a).faceUp) := by
  intro γ
  induction γ with
  | nil => intro Q P hplay _ _ hz; cases hplay; exact hz
  | cons m t ih =>
      intro Q P hplay hfree z hz
      obtain ⟨S1, hrevA, hstep, hrest⟩ := Bubble.walk_cons_inv hplay
      have hz1 : ∃ a : Anchor, z ∈ (S1.piles a).faceUp :=
        ih hrest (fun y hy => hfree y (List.mem_cons_of_mem _ hy)) z hz
      rcases hfree m (List.mem_cons_self ..) with rfl | ⟨cx, bx, rfl⟩
      · rw [stepDraw_piles hstep] at hz1
        exact hz1
      · exact faceUp_of_slide hstep hrevA hz1

/-! ## §7. The unconditional twin cover -/

/-- **THE COVER ON THE PREPARED SEAT IS ALWAYS THE PULLEE'S TWIN.**  Face
1b's `hface` hypothesis is now a theorem: `z` is face-up at the window's
end (it is a pile top there), hence face-up at its start (§6).  The twin
cover of `Orig2/Fork/Third/ForkFace1.lean` is unconditional. -/
theorem cover_is_twin' {B P C0 : State} {γ : List Move} {d z : Card}
    (hwfB : B.WF)
    (hγ : ShufflePlayW B γ P) (hfree : Canon.FreeOnly γ)
    (hfire : State.step P (Move.foundToTab d (Sum.inr z)) = some C0)
    (hB : ¬ PullKit.Pullable B d (Sum.inr z)) :
    ∃ (x : Card) (front rest : List Card) (a0 : Anchor),
      (B.piles a0).faceUp = front ++ z :: x :: rest ∧ x = d.twin := by
  have hP : PullKit.Pullable P d (Sum.inr z) := CrossSuitF1.pullable_of_step hfire
  obtain ⟨htopP, -⟩ := CrossSuitF1.canPlace_inr_true_iff.mp hP.2
  have hzp : ∃ a : Anchor, z ∈ (P.piles a).faceUp := faceUp_of_pileOfTop htopP
  have hzb : ∃ a : Anchor, z ∈ (B.piles a).faceUp :=
    faceUp_window_back γ hγ hfree z hzp
  exact CrossSuitF1.cover_is_twin hwfB hγ hfree hfire hB hzb

end CrossSuitF2

#print axioms CrossSuitF2.mem_fromCard
#print axioms CrossSuitF2.setPile_piles_self
#print axioms CrossSuitF2.setPile_piles_ne
#print axioms CrossSuitF2.putRun_inl_eq
#print axioms CrossSuitF2.putRun_inr_some
#print axioms CrossSuitF2.putRun_inr_none
#print axioms CrossSuitF2.slide_reveal_irrev
#print axioms CrossSuitF2.mem_of_afterRunRemoved
#print axioms CrossSuitF2.faceUp_of_slide
#print axioms CrossSuitF2.faceUp_of_pileOfTop
#print axioms CrossSuitF2.faceUp_window_back
#print axioms CrossSuitF2.cover_is_twin'
