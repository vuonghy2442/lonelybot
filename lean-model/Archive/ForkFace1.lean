import Orig2.Fork.Local.ForkSafeTransport

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CrossSuit

/-- **`AvoidsSuit σ m`** — the letter `m` does not touch suit `σ`: it is a
`draw`/`tabToTab` (`FreeMove`, rung-preserving) or a raise/pull of another suit.
(The waste letters are never witness letters; they are deliberately `True` here
so the predicate is total.) -/
def AvoidsSuit (σ : Suit) : Move → Prop
  | Move.tabToFound c => c.suit ≠ σ
  | Move.foundToTab c _ => c.suit ≠ σ
  | _ => True

theorem avoidsSuit_raise {σ : Suit} {c : Card} (h : c.suit ≠ σ) :
    AvoidsSuit σ (Move.tabToFound c) := h

theorem avoidsSuit_pull {σ : Suit} {c : Card} {b : Base} (h : c.suit ≠ σ) :
    AvoidsSuit σ (Move.foundToTab c b) := h

/-- A slide moves only piles: the whole foundation is fixed. -/
theorem found_tabToTab_eq {st w : State} {c : Card} {b : Base}
    (hstep : State.step st (Move.tabToTab c b) = some w) : w.found = st.found := by
  obtain ⟨a, -, -, -, hw⟩ := step_tabToTab_inv hstep
  rw [hw, putRun_found, setPile_found]

/-- A pull of another suit leaves the `σ`-column alone. -/
theorem found_foundToTab_ne {st w : State} {c : Card} {b : Base}
    (hstep : State.step st (Move.foundToTab c b) = some w) {s : Suit} (hs : s ≠ c.suit) :
    w.found s = st.found s := by
  obtain ⟨c', -, hc', -, hw⟩ := step_foundToTab_inv hstep
  rw [hw, putCard_found]
  exact setFound_found_ne hs

/-- **A `σ`-free witness letter leaves the `σ`-column alone.** -/
theorem found_step_of_avoids {st w : State} {m : Move} {σ : Suit}
    (hstep : State.step st m = some w) (hrev : reversibleAtW st m)
    (h : AvoidsSuit σ m) : w.found σ = st.found σ := by
  cases m with
  | draw => rw [stepDraw_found hstep]
  | tabToTab c b => rw [found_tabToTab_eq hstep]
  | tabToFound c =>
      exact SafeTransport.found_tabToFound_ne hstep (fun hh => h hh.symm)
  | foundToTab c b =>
      exact found_foundToTab_ne hstep (fun hh => h hh.symm)
  | wasteToFound c => exact absurd hrev (wasteToFound_not_reversibleAtW st c)
  | wasteToTab c b => exact absurd hrev (wasteToTab_not_reversibleAtW st c b)

/-- **THE COLUMN-TRANSPORT.**  Along a witness play whose every letter avoids
`σ`, the `σ`-column of the foundation is unchanged. -/
theorem found_eq_of_avoids {u v : State} {ρ : List Move} {σ : Suit}
    (hplay : ShufflePlayW u ρ v) (h : ∀ m ∈ ρ, AvoidsSuit σ m) :
    v.found σ = u.found σ := by
  induction hplay with
  | nil st => rfl
  | @cons st s₁ W m ρ' hrev hstep hrest ih =>
      have hm : AvoidsSuit σ m := h m (List.mem_cons_self ..)
      have ht : ∀ m' ∈ ρ', AvoidsSuit σ m' :=
        fun m' hm' => h m' (List.mem_cons_of_mem m hm')
      rw [ih ht]
      exact found_step_of_avoids hstep hrev hm

/-- **THE TOP-TRANSPORT.**  Along a `σ`-free witness play the `σ`-foundation top
is unchanged. -/
theorem foundTop_eq_of_avoids {u v : State} {ρ : List Move} {σ : Suit}
    (hplay : ShufflePlayW u ρ v) (h : ∀ m ∈ ρ, AvoidsSuit σ m) :
    v.foundTop σ = u.foundTop σ := by
  unfold State.foundTop
  rw [found_eq_of_avoids hplay h]

end CrossSuit

/-!
# CrossSuit_Face1 — the geometry of the prepared-seat face

READ-ONLY scratch card (`Temp/`).  No source edit, no commit.  Zero `sorry`,
zero `Classical.choice`, zero `native_decide`; battery at the tail.

## What face 1 is

`Temp/CrossSuit_Partition.lean` split the cross-suit corridor universe into
four faces.  Face 1 is `NoWindowPreparedSeat`: the pull is **not** ready at
the raise's landing `B` (`¬ Pullable B d b`), so the seat is prepared
*inside* the free window.  This card gives that face its geometry.

## What this card proves

* §1 the two `canPlace` characterizations — `inl` is
  empty-pile-and-king; `inr` is pile-topness plus the **static** fit
  `canSitOn d z` (state-independent, the exact tableau stacking law:
  one rank below, opposite color).  So a `¬Pullable` failure at `B` with the
  pull firing later is *purely* the base's availability.
* §3 **the sub-shape dichotomy** (face 1 splits exactly like the parallel
  lane's shapes 1 and 3, but with the window — not the raise — preparing
  the seat):
  - **1a**: `b = inl a`, `d` is a KING, pile `a` NONEMPTY at `B` and EMPTY
    at `P` — the window empties the king's landing pile;
  - **1b**: `b = inr z`, `z` is NOT a pile-top at `B` (buried) and IS one at
    `P` (exposed) — the window exposes the seat — and `canSitOn d z`.
* §4 **THE TWIN COVER.**  In shape 1b, if the buried `z` is face-up covered
  at `B`, then the card sitting directly on `z` — the cover the window must
  slide away — is **exactly `d.twin`**: it has `d`'s rank (both sit one
  below `z`) and `d`'s color (both opposite to `z`), and it cannot be `d`
  itself because `d` is on the foundation at `B`.  This is the mirror of
  the parallel lane's shape-3 fact (`d = c.twin`: the puller is the
  raise's twin); here the *cover* is the pullee's twin.  Either way, a
  twin pair brackets the corridor — exactly the input shape the twin-swap
  machinery (`TwinSplice`, `TwinRelocate`, `TwinEquivariance`) and the
  twin-source law (`ForkWindow.false_of_slide_onto_of_twin_found`) expect.

## Named next moves (recorded, not proved here)

* The window's tableau transport (free windows preserve face-up
  membership — slides permute, draws never touch piles), which would make
  §4's face-up hypothesis a theorem rather than a hypothesis.
* The cover's own slide: it must leave `z` during the window, and by the
  twin-source law it either lands on an empty pile or on `z.twin` —
  combined with §4, `d.twin` lands on `z.twin`, a twin-swap of the seat.
-/

namespace CrossSuitF1

/-! ## §0. The helpers -/

/-- A passing test anywhere in the list makes `firstWhere` succeed. -/
theorem firstWhere_ne_none_of_mem {p : Anchor → Bool} {a : Anchor} :
    ∀ {l : List Anchor}, a ∈ l → p a = true → firstWhere p l ≠ none := by
  intro l
  induction l with
  | nil => intro ha; exact absurd ha (by simp)
  | cons b t ih =>
      intro ha hp
      by_cases hpb : p b = true
      · have heq : firstWhere p (b :: t) = some b := by simp [firstWhere, hpb]
        rw [heq]
        intro hc
        cases hc
      · have heq : firstWhere p (b :: t) = firstWhere p t := by simp [firstWhere, hpb]
        rw [heq]
        have hmt : a ∈ t := by
          rcases List.mem_cons.mp ha with h | h
          · exact absurd (h ▸ hp) hpb
          · exact h
        exact ih hmt hp

/-- A card that tops a pile is found by `pileOfTop`. -/
theorem pileOfTop_ne_none_of_topOf {st : State} {a : Anchor} {z : Card}
    (h : st.topOf a = some z) : st.pileOfTop z ≠ none :=
  firstWhere_ne_none_of_mem (Anchor.mem_all a) (by simp [h])

/-- Cards are determined by suit and rank. -/
theorem card_eq_of_suit_rank {x y : Card} (hs : x.suit = y.suit) (hr : x.rank = y.rank) :
    x = y := by
  cases x <;> cases y <;> simp_all

/-- Cards of equal rung index are equal. -/
theorem rank_eq_of_toIdx_eq : ∀ {r s : Rank}, r.toIdx = s.toIdx → r = s := by
  intro r s h
  cases r <;> cases s <;> simp_all [Rank.toIdx]

/-- A member that is not the last element has a successor in place. -/
theorem split_at_not_last : ∀ {l : List Card} {z : Card},
    z ∈ l → lastOf l ≠ some z →
    ∃ (front : List Card) (x : Card) (rest : List Card),
      l = front ++ z :: x :: rest := by
  intro l
  induction l with
  | nil => intro z hm; exact absurd hm (by simp)
  | cons y t ih =>
      intro z hm hlast
      by_cases hyz : y = z
      · cases t with
        | nil => exact absurd (by rw [hyz]; rfl) hlast
        | cons w t' => exact ⟨[], w, t', by rw [hyz]; rfl⟩
      · have hmt : z ∈ t := by
          rcases List.mem_cons.mp hm with h | h
          · exact absurd h.symm hyz
          · exact h
        have hrest : lastOf t ≠ some z := by
          cases t with
          | nil => intro hc; exact absurd hc (by simp [lastOf])
          | cons w t' => intro hc; exact hlast hc
        obtain ⟨front, x, rest, hsplit⟩ := ih hmt hrest
        exact ⟨y :: front, x, rest, by rw [hsplit]; rfl⟩

/-- A legal run's in-place successor pair satisfies the stacking law. -/
theorem canSitOn_of_runOK_append :
    ∀ (front : List Card) {z x : Card} {rest : List Card},
      runOK (front ++ z :: x :: rest) = true → canSitOn x z = true := by
  intro front
  induction front with
  | nil =>
      intro z x rest h
      rw [show runOK ([] ++ z :: x :: rest) =
            (canSitOn x z && runOK (x :: rest)) from rfl,
          Bool.and_eq_true] at h
      exact h.1
  | cons w f ih =>
      intro z x rest h
      rw [List.cons_append] at h
      cases f with
      | nil =>
          rw [List.nil_append] at h
          rw [show runOK (w :: z :: x :: rest) =
                (canSitOn z w && runOK (z :: x :: rest)) from rfl,
              Bool.and_eq_true] at h
          exact ih h.2
      | cons w' f' =>
          rw [List.cons_append] at h
          rw [show runOK (w :: w' :: (f' ++ z :: x :: rest)) =
                (canSitOn w' w && runOK (w' :: f' ++ z :: x :: rest)) from rfl,
              Bool.and_eq_true] at h
          exact ih h.2

/-! ## §1. The `canPlace` characterizations -/

theorem canPlace_inl_true_iff {st : State} {d : Card} {a : Anchor} :
    st.canPlace d (Sum.inl a) = true ↔
      (st.piles a).isEmpty ∧ d.rank = Rank.king := by
  simp [State.canPlace, Bool.and_eq_true]

theorem canPlace_inr_true_iff {st : State} {d z : Card} :
    st.canPlace d (Sum.inr z) = true ↔
      st.pileOfTop z ≠ none ∧ canSitOn d z = true := by
  show (match st.pileOfTop z with
      | some _ => canSitOn d z | none => false) = true ↔ _
  cases h : st.pileOfTop z with
  | some a => simp
  | none => simp

/-! ## §2. The window transport (from the partition card) -/

/-- Free letters avoid every suit (the `AvoidsSuit` catch-all). -/
theorem avoidsSuit_of_free {σ : Suit} {m : Move}
    (h : ValleyElim.FreeMove m) : CrossSuit.AvoidsSuit σ m := by
  rcases h with rfl | ⟨c, b, rfl⟩
  · trivial
  · trivial

/-- A free window preserves every suit's foundation top. -/
theorem foundTop_free_window {Q P : State} {γ : List Move} (σ : Suit)
    (hγ : ShufflePlayW Q γ P) (hfree : ∀ m ∈ γ, ValleyElim.FreeMove m) :
    Q.foundTop σ = P.foundTop σ :=
  (CrossSuit.foundTop_eq_of_avoids hγ
    (fun m hm => avoidsSuit_of_free (hfree m hm))).symm

/-- The pull's own firing is `Pullable` at its origin. -/
theorem pullable_of_step {P C : State} {d : Card} {b : Base}
    (h : State.step P (Move.foundToTab d b) = some C) :
    PullKit.Pullable P d b := by
  obtain ⟨d', htop, hd'd, hcp, -⟩ := step_foundToTab_inv h
  subst hd'd
  exact ⟨htop, hcp⟩

/-! ## §3. The face-1 sub-shape dichotomy -/

/-- **FACE 1 SPLITS LIKE THEIR SHAPES, WITH THE WINDOW AS THE SEAT-PREPARER.**
If the pull of `d` onto `b` fires after a free window but was not ready at
the window's start `B`, then either the base is an empty pile (`d` is a
king and the window EMPTIES the pile) or a card (`z` is buried at `B`, the
window EXPOSES it), and in the second case the pull's fit on `z` is the
static stacking law. -/
theorem face1_dichotomy {B P C0 : State} {γ : List Move} {d : Card} {b : Base}
    (hγ : ShufflePlayW B γ P) (hfree : Canon.FreeOnly γ)
    (hfire : State.step P (Move.foundToTab d b) = some C0)
    (hB : ¬ PullKit.Pullable B d b) :
    (∃ a : Anchor, b = Sum.inl a ∧ d.rank = Rank.king ∧
        ¬(B.piles a).isEmpty ∧ (P.piles a).isEmpty)
    ∨ (∃ z : Card, b = Sum.inr z ∧ B.pileOfTop z = none ∧
        P.pileOfTop z ≠ none ∧ canSitOn d z = true) := by
  have hP : PullKit.Pullable P d b := pullable_of_step hfire
  have hftB : B.foundTop d.suit = some d :=
    (foundTop_free_window d.suit hγ hfree).trans hP.1
  have hcpB : B.canPlace d b ≠ true := by
    intro hc
    exact hB ⟨hftB, hc⟩
  cases b with
  | inl a =>
      obtain ⟨hpe, hk⟩ := canPlace_inl_true_iff.mp hP.2
      have hne : ¬(B.piles a).isEmpty := fun h =>
        hcpB (canPlace_inl_true_iff.mpr ⟨h, hk⟩)
      exact Or.inl ⟨a, rfl, hk, hne, hpe⟩
  | inr z =>
      obtain ⟨htopP, hsitd⟩ := canPlace_inr_true_iff.mp hP.2
      have hnone : B.pileOfTop z = none := by
        cases h : B.pileOfTop z with
        | some a =>
            exact absurd (canPlace_inr_true_iff.mpr
              ⟨(fun hc => by rw [h] at hc; cases hc), hsitd⟩) hcpB
        | none => rfl
      exact Or.inr ⟨z, rfl, hnone, htopP, hsitd⟩

/-! ## §4. The twin cover -/

/-- **THE COVER ON THE PREPARED SEAT IS THE PULLEE'S TWIN.**  In shape 1b,
if the buried base card `z` is face-up covered at `B` (in pile `a0`'s run,
not the top), then the card sitting directly on `z` — the cover the window
must slide away to expose the seat — is exactly `d.twin`: same rank as
`d` (both one below `z`), same color (both opposite to `z`), and not `d`
itself (`d` is founded at `B`, the cover is on the tableau). -/
theorem cover_is_twin {B P C0 : State} {γ : List Move} {d z : Card}
    (hwfB : B.WF)
    (hγ : ShufflePlayW B γ P) (hfree : Canon.FreeOnly γ)
    (hfire : State.step P (Move.foundToTab d (Sum.inr z)) = some C0)
    (hB : ¬ PullKit.Pullable B d (Sum.inr z))
    (hface : ∃ a0 : Anchor, z ∈ (B.piles a0).faceUp) :
    ∃ (x : Card) (front rest : List Card) (a0 : Anchor),
      (B.piles a0).faceUp = front ++ z :: x :: rest ∧ x = d.twin := by
  have hP : PullKit.Pullable P d (Sum.inr z) := pullable_of_step hfire
  obtain ⟨htopP, hsitd⟩ := canPlace_inr_true_iff.mp hP.2
  have hftB : B.foundTop d.suit = some d :=
    (foundTop_free_window d.suit hγ hfree).trans hP.1
  have hcpB : B.canPlace d (Sum.inr z) ≠ true := by
    intro hc
    exact hB ⟨hftB, hc⟩
  have hnone : B.pileOfTop z = none := by
    cases h : B.pileOfTop z with
    | some a =>
        exact absurd (canPlace_inr_true_iff.mpr
          ⟨(fun hc => by rw [h] at hc; cases hc), hsitd⟩) hcpB
    | none => rfl
  obtain ⟨a0, hmem⟩ := hface
  have hnotlast : lastOf ((B.piles a0).faceUp) ≠ some z := by
    intro hl
    exact (pileOfTop_ne_none_of_topOf
      (show (B.piles a0).top = some z from hl)) hnone
  obtain ⟨front, x, rest, hsplit⟩ := split_at_not_last hmem hnotlast
  have hrun : runOK ((B.piles a0).faceUp) = true := hwfB.2.1 a0
  have hsitx : canSitOn x z = true :=
    canSitOn_of_runOK_append front (by rw [← hsplit]; exact hrun)
  have hxmem : x ∈ (B.piles a0).faceUp := by
    rw [hsplit]
    exact List.mem_append_right front
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hxpile : x ∈ pileZone B a0 := List.mem_append_right _ hxmem
  have hdfd : d ∈ B.found d.suit := lastOf_mem hftB
  have hne : x ≠ d := fun hxd => wf_pile_found_ne hwfB (hxd ▸ hxpile) hdfd
  rw [canSitOn_eq] at hsitx
  obtain ⟨hrx, hcx⟩ := hsitx
  rw [canSitOn_eq] at hsitd
  obtain ⟨hrd, hcd⟩ := hsitd
  have htoIdx : x.rank.toIdx = d.rank.toIdx := by omega
  have hr : x.rank = d.rank := rank_eq_of_toIdx_eq htoIdx
  have hcol : x.suit.color = d.suit.color := Blocks.color_eq_of_ne_ne hcx hcd
  have hsu : x.suit ≠ d.suit := by
    intro hsu
    exact hne (card_eq_of_suit_rank hsu hr)
  have htwinSuit : x.suit = d.suit.twin :=
    Blocks.eq_twin_of_color_eq_ne hcol.symm hsu.symm
  have hx : x = d.twin :=
    card_eq_of_suit_rank (by rw [htwinSuit, Card.twin_suit])
      (by rw [Card.twin_rank]; exact hr)
  exact ⟨x, front, rest, a0, hsplit, hx⟩

end CrossSuitF1

#print axioms CrossSuitF1.firstWhere_ne_none_of_mem
#print axioms CrossSuitF1.pileOfTop_ne_none_of_topOf
#print axioms CrossSuitF1.card_eq_of_suit_rank
#print axioms CrossSuitF1.split_at_not_last
#print axioms CrossSuitF1.canSitOn_of_runOK_append
#print axioms CrossSuitF1.canPlace_inl_true_iff
#print axioms CrossSuitF1.canPlace_inr_true_iff
#print axioms CrossSuitF1.avoidsSuit_of_free
#print axioms CrossSuitF1.foundTop_free_window
#print axioms CrossSuitF1.pullable_of_step
#print axioms CrossSuitF1.face1_dichotomy
#print axioms CrossSuitF1.cover_is_twin
