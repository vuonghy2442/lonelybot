import Klondike.Restriction
import Witnesses.C2KingAnchorWitness

/-!
# The reachability probe — both pristine-family witnesses live off the
dealt-reachable fragment

The wave-18/19 refutation witnesses counterexample four + one as-stated
C2 universals at hand-crafted WF states:
`Witnesses.C2KingAnchorWitness` (the pristine empty board whose stocked,
climb-blocked king splits its landings seven ways, killing the as-stated
`wk_c2`, `wk_same_pin`, `wk_p2_direct` and `wk_crease`) and
`Witnesses.SuccLabeledWitness` (the anchored-head board killing the
as-stated `wk_succ_labeled`).  This file decides the restoration datum:
none of the witness roots, nor the KingAnchor commitment's landing
successors, is `initialReachable` (Restriction.lean), so every
initialReachable-gated re-statement of those five universals is beyond
this witness family's reach.  The five verdicts are tabulated at the
file's end.

## The obstruction class — pile-card conservation, not stock composition

The rule inventory: no `Move` ever adds a card to the stock cycle
(`deckPile`/`deckStack` splice the waste top out, `draw` only advances
the cursor), and `stock_wf` keeps the cycle inside the deal's stock,
which `Deal.piles_stock_disj` keeps disjoint from the dealt piles.  So
along any play every one of the deal's pile cards always sits in one of
three static zones: hidden in its pile, visible on the matching, or on
its foundation.  That is the invariant `accounted` below, and it is
preserved by every move:
`reveal` moves the boundary card hidden to visible (the only pile
cards leaving the hidden slice are the boundary itself, and the attach
seats exactly it); `pilePile` rewrites the matching without losing its
image (the moved root re-seats, riders keep their edges);
`pileStack` and `deckStack` bump one suit's height where the only card
newly founded is the moved card itself (same suit and same rank decide
the same card); `stackPile` drops one suit's height, unfounding exactly
its own re-seated card (the same uniqueness); `draw` and `deckPile`
touch nothing seated.

The witness deals are themselves honest 52-card deals (the spade
counts close: twelve spades across the piles plus the stocked king),
so stock composition is NOT the obstruction.  The obstruction is the
vanishing pile: a reached state with all depths and heights zero must
show EVERY dealt pile card on its board (`pileCards_seated_of_
initialReachable`), but the pristine board shows none, each landing
successor shows only the stocked king (a stock card), and the
anchored-head board shows only the seven heads, burying the other
twenty-one dealt pile cards nowhere.

## Deliverables

* `KingAnchorReach.accounted`, `apply_accounted`, `initial_accounted`,
  `run_accounted` — the conserved invariant and its maintenance;
* `KingAnchorReach.pileCards_seated_of_initialReachable` — the fence;
* `KingAnchorReach.wstate_not_initialReachable`,
  `KingAnchorReach.wsucc_not_initialReachable`,
  `KingAnchorReach.ustate_not_initialReachable` — the per-root verdicts.
  The three replica constants are public, field-identical spellings
  of the read-only witnesses' private states (their privateness is why
  the verdicts are stated at replicas; each also carries a WF exhibit,
  so the fence separates two genuinely inhabited worlds: the corners
  are WF-inhabited but deal-unreachable).

The verdicts do NOT prove the restricted universals — the corpus's
weak corners (a lone climb-blocked anchored king, with hidden cards and
piles elsewhere) are dealt-reachable, so the restricted statements
carry real content.  This file removes the pristine witness family as
a countermodel and states the exact fence the restorations may lean on.
-/

namespace KingAnchorReach

/-! ## The conserved pile cards

`accounted st`: every card dealt into one of `st`'s piles is hidden in
its pile, visible on the matching, or on its foundation. -/

/-- The conservation invariant: every dealt pile card is hidden,
visible, or founded — never stocked (the cycle never gains cards and
starts disjoint from the piles), never destroyed. -/
def accounted (st : State) : Prop :=
  ∀ a : Anchor, ∀ c : Card, c ∈ st.deal.piles a →
    c ∈ st.hidden a ∨ st.isVis c = true ∨ st.onFound c = true

/-! ### A card-uniqueness fact for the height-drop move -/

/-- A same-suit card different from the moved card stays strictly below
the rung when the foundation drops the rung card back. -/
private theorem lt_rung_of_drop {st : State} {c q : Card}
    (hfit : c.rank.toIdx + 1 = st.heights c.suit)
    (hsuit : q.suit = c.suit) (hne : q ≠ c)
    (hold : q.rank.toIdx < st.heights c.suit) :
    q.rank.toIdx < st.heights c.suit - 1 := by
  have h1 : q.rank.toIdx ≠ c.rank.toIdx := by
    intro hcon
    have h2 : q.rank = c.rank := Rank.toIdx_inj hcon
    exact hne (by cases q with
      | mk sq rq => cases c with
        | mk sc rc =>
            rw [Card.mk.injEq]
            exact ⟨hsuit, h2⟩)
  have h3 : q.rank.toIdx < c.rank.toIdx := by omega
  omega

/-! ### The maintenance -/

/-- A surviving old seat stays a seat through the rewrite of one run:
the moved root re-seats at the landing base, every other card keeps its
own seat (the `bottomOf` search only ever reads `topOf`). -/
private theorem bottomOf_isSome_pilePile {bd : Board} {c : Card} {b b' : Base}
    {bd' : Board}
    (hne : b' ≠ b)
    (hbot : bd.bottomOf c = some b')
    (hatt : (bd.detach b').attach b c = some bd')
    {q : Card} (hq : (bd.bottomOf q).isSome = true) :
    (bd'.bottomOf q).isSome = true := by
  have hbn : b ≠ b' := fun hh => hne hh.symm
  by_cases hqc : q = c
  · rw [hqc]
    have hseatC : bd'.bottomOf c = some b :=
      (Board.bottomOf_eq bd' c b).mpr (Board.attach_topOf (bd.detach b') b c hatt)
    rw [hseatC]
    rfl
  · obtain ⟨b₁, hb₁⟩ : ∃ b₁, bd.bottomOf q = some b₁ := by
      cases hh : bd.bottomOf q with
      | none => rw [hh] at hq; simp at hq
      | some b₁ => exact ⟨b₁, rfl⟩
    have hseat : bd.topOf b₁ = some q := (Board.bottomOf_eq bd q b₁).mp hb₁
    have hhold : bd.topOf b' = some c := (Board.bottomOf_eq bd c b').mp hbot
    have hb₁ne : b₁ ≠ b' := by
      intro hcon
      rw [hcon] at hseat
      exact hqc (Option.some.inj (hseat.symm.trans hhold))
    have hb₁nb : b₁ ≠ b := by
      intro hcon
      rw [hcon] at hseat
      have hfree : (bd.detach b').topOf b = none :=
        (Board.attach_eq_some_iff (bd.detach b') b c).mp
          (show (bd.detach b').attach b c ≠ none from by rw [hatt]; simp) |>.1
      rw [Board.detach_topOf_ne bd b' b hbn] at hfree
      rw [hfree] at hseat
      exact absurd hseat (by simp)
    have hnew : bd'.bottomOf q = some b₁ :=
      (Board.bottomOf_eq bd' q b₁).mpr (by
        rw [Board.attach_topOf_ne (bd.detach b') b c hatt hb₁nb,
          Board.detach_topOf_ne bd b' b₁ hb₁ne]
        exact hseat)
    rw [hnew]
    rfl

/-- **Maintenance**: the conservation invariant survives every legal
move (the full move set).  WF is needed only by the reveal arm (the
boundary card's index extraction reads `depths_le`). -/
theorem apply_accounted {st st' : State} {m : Move} (hwf : st.WF)
    (ha : accounted st) (h : st.apply m = some st') : accounted st' := by
  cases m with
  | draw =>
      rw [apply_draw_iff] at h
      obtain rfl := h
      intro a q hq
      exact ha a q hq
  | reveal a₀ =>
      rw [apply_reveal_iff] at h
      obtain ⟨r, bd, htoph, hbare, hatt, rfl⟩ := h
      intro a q hq
      have hq' : q ∈ st.deal.piles a := hq
      rcases ha a q hq' with hhid | hvis | hfon
      · by_cases haa : a = a₀
        · rw [haa] at hhid ⊢
          have hhid' : q ∈ (st.deal.piles a₀).take (st.depths a₀) := hhid
          by_cases hnew : q ∈ (st.deal.piles a₀).take (st.depths a₀ - 1)
          · refine Or.inl ?_
            show q ∈ (st.deal.piles a₀).take
              (if a₀ = a₀ then st.depths a₀ - 1 else st.depths a₀)
            rw [ite_eq_left rfl]
            exact hnew
          · obtain ⟨mm, hmm, hget⟩ := mem_take_index hhid'
            have hne : ¬ (mm < st.depths a₀ - 1) :=
              fun hlt => hnew (mem_take_of_index hlt hget)
            have hme : mm = st.depths a₀ - 1 := by omega
            have hle : st.depths a₀ ≤ (st.deal.piles a₀).length := hwf.depths_le a₀
            have hgetr := topHidden_get hle htoph
            rw [hme] at hget
            have hqr : q = r := Option.some.inj (hget.symm.trans hgetr)
            refine Or.inr (Or.inl ?_)
            rw [hqr]
            have hseatR : bd.bottomOf r = some (st.hiddenBase a₀) :=
              (Board.bottomOf_eq bd r (st.hiddenBase a₀)).mpr
                (Board.attach_topOf st.board (st.hiddenBase a₀) r hatt)
            show (bd.bottomOf r).isSome = true
            rw [hseatR]
            rfl
        · refine Or.inl ?_
          show q ∈ (st.deal.piles a).take (if a = a₀ then st.depths a₀ - 1 else st.depths a)
          rw [ite_eq_right haa]
          exact hhid
      · refine Or.inr (Or.inl ?_)
        exact bottomOf_isSome_attach hatt hvis
      · exact Or.inr (Or.inr hfon)
  | deckPile c₀ b₀ =>
      rw [apply_deckPile_iff] at h
      obtain ⟨hp, hcp, bd, hatt, rfl⟩ := h
      intro a q hq
      have hq' : q ∈ st.deal.piles a := hq
      rcases ha a q hq' with hhid | hvis | hfon
      · exact Or.inl hhid
      · exact Or.inr (Or.inl (bottomOf_isSome_attach hatt hvis))
      · exact Or.inr (Or.inr hfon)
  | deckStack c₀ =>
      rw [apply_deckStack_iff] at h
      obtain ⟨hp, hrk, rfl⟩ := h
      intro a q hq
      have hq' : q ∈ st.deal.piles a := hq
      rcases ha a q hq' with hhid | hvis | hfon
      · exact Or.inl hhid
      · exact Or.inr (Or.inl hvis)
      · refine Or.inr (Or.inr ?_)
        show decide (q.rank.toIdx <
          (if q.suit = c₀.suit then st.heights q.suit + 1 else st.heights q.suit)) = true
        by_cases hsu : q.suit = c₀.suit
        · rw [ite_eq_left hsu]
          exact decide_eq_true (by have := of_decide_eq_true hfon; omega)
        · rw [ite_eq_right hsu]
          exact hfon
  | pileStack c₀ =>
      rw [apply_pileStack_iff] at h
      obtain ⟨htopn, b₀, hbot, hrk, rfl⟩ := h
      intro a q hq
      have hq' : q ∈ st.deal.piles a := hq
      rcases ha a q hq' with hhid | hvis | hfon
      · exact Or.inl hhid
      · by_cases hqc : q = c₀
        · rw [hqc]
          exact Or.inr (Or.inr (by
            show decide (c₀.rank.toIdx <
              (if c₀.suit = c₀.suit then st.heights c₀.suit + 1 else st.heights c₀.suit)) = true
            rw [ite_eq_left rfl]
            exact decide_eq_true (by omega)))
        · refine Or.inr (Or.inl ?_)
          have hseat : st.board.topOf b₀ = some c₀ := (Board.bottomOf_eq st.board c₀ b₀).mp hbot
          show ((st.board.detach b₀).bottomOf q).isSome = true
          rw [bottomOf_detach_ne hseat hqc]
          exact hvis
      · refine Or.inr (Or.inr ?_)
        show decide (q.rank.toIdx <
          (if q.suit = c₀.suit then st.heights q.suit + 1 else st.heights q.suit)) = true
        by_cases hsu : q.suit = c₀.suit
        · rw [ite_eq_left hsu]
          exact decide_eq_true (by have := of_decide_eq_true hfon; omega)
        · rw [ite_eq_right hsu]
          exact hfon
  | stackPile c₀ b₀ =>
      rw [apply_stackPile_iff] at h
      obtain ⟨hrg, hcp, bd, hatt, rfl⟩ := h
      intro a q hq
      have hq' : q ∈ st.deal.piles a := hq
      rcases ha a q hq' with hhid | hvis | hfon
      · exact Or.inl hhid
      · exact Or.inr (Or.inl (bottomOf_isSome_attach hatt hvis))
      · by_cases hqc : q = c₀
        · rw [hqc]
          refine Or.inr (Or.inl ?_)
          show (bd.bottomOf c₀).isSome = true
          rw [(Board.bottomOf_eq bd c₀ b₀).mpr (Board.attach_topOf st.board b₀ c₀ hatt)]
          rfl
        · by_cases hsu : q.suit = c₀.suit
          · refine Or.inr (Or.inr ?_)
            show decide (q.rank.toIdx <
              (if q.suit = c₀.suit then st.heights q.suit - 1 else st.heights q.suit)) = true
            rw [ite_eq_left hsu]
            have hold : q.rank.toIdx < st.heights c₀.suit := by
              have := of_decide_eq_true hfon
              rw [hsu] at this
              exact this
            have hlt := lt_rung_of_drop hrg hsu hqc hold
            rw [hsu]
            exact decide_eq_true (by omega)
          · refine Or.inr (Or.inr ?_)
            show decide (q.rank.toIdx <
              (if q.suit = c₀.suit then st.heights q.suit - 1 else st.heights q.suit)) = true
            rw [ite_eq_right hsu]
            exact hfon
  | pilePile c₀ b₀ =>
      rw [apply_pilePile_iff] at h
      obtain ⟨b₁, hbot, hne, hcmr, bd, hatt, rfl⟩ := h
      intro a q hq
      have hq' : q ∈ st.deal.piles a := hq
      rcases ha a q hq' with hhid | hvis | hfon
      · exact Or.inl hhid
      · refine Or.inr (Or.inl ?_)
        exact bottomOf_isSome_pilePile hne hbot hatt hvis
      · exact Or.inr (Or.inr hfon)

/-! ### The run packaging -/

/-- Both invariants ride any successful play (WF via `apply_wf`). -/
theorem run_accounted : ∀ (play : List Move) (st st' : State),
    st.WF → accounted st → st.run play = some st' → accounted st' := by
  intro play
  induction play with
  | nil =>
      intro st st' hwf ha h
      simp only [State.run] at h
      obtain rfl := Option.some.inj h
      exact ha
  | cons m ms ih =>
      intro st st' hwf ha h
      simp only [State.run] at h
      cases hap : st.apply m with
      | none => rw [hap] at h; exact absurd h (by simp)
      | some R =>
          rw [hap] at h
          exact ih R st' (apply_wf hwf m R hap) (apply_accounted hwf ha hap) h

/-! ### The initial state -/

/-- The last element, by its index (the element at `length - 1` is the
last). -/
private theorem getLast?_of_index : ∀ (l : List Card) (c : Card),
    l[l.length - 1]? = some c → l.getLast? = some c := by
  intro l
  induction l with
  | nil => intro c h; simp at h
  | cons x t ih =>
      intro c h
      cases t with
      | nil =>
          have hxc : x = c := by
            have hh := h
            simp only [List.length_cons, List.length_nil] at hh
            exact Option.some.inj hh
          rw [hxc]
          rfl
      | cons y u =>
          have hc : (y :: u)[(y :: u).length - 1]? = some c := by
            have hh := h
            rw [show (x :: y :: u).length - 1 = ((y :: u).length - 1) + 1 from by
                simp only [List.length_cons]
                omega] at hh
            rw [List.getElem?_cons_succ] at hh
            exact hh
          have hlast : (y :: u).getLast? = some c := ih c hc
          have hcons : (x :: y :: u).getLast? = (y :: u).getLast? := rfl
          rw [hcons]
          exact hlast

/-- The running board image during the initial dealing: every seat
written so far is a processed pile's top dealt card at its own base,
and every processed pile's top sits at its base. -/
private def InitImg (d : Deal) (proc : List Anchor) (bd : Board) : Prop :=
  (∀ a ∈ proc, bd.topOf (initBase d a) = (d.piles a).getLast?) ∧
  (∀ b c, bd.topOf b = some c →
    ∃ a, a ∈ proc ∧ b = initBase d a ∧ (d.piles a).getLast? = some c)

private theorem initImg_empty : InitImg d [] Board.empty := by
  refine ⟨fun a ha => absurd ha (by simp), ?_⟩
  intro b c hb
  rw [Board.empty_topOf] at hb
  exact absurd hb (by simp)

/-- The pile index decides the anchor. -/
private theorem anchor_toIdx_inj {a a' : Anchor} (h : a.toIdx = a'.toIdx) :
    a = a' := by
  cases a <;> cases a' <;> simp_all [Anchor.toIdx]

/-- The dealt under-card form of `initBase`: an anchor for `p0`, the
under-card otherwise (WF pile lengths keep the index in range). -/
private theorem initBase_shape (d : Deal) (hd : d.WF) (a : Anchor) :
    a = Anchor.p0 ∨ ∃ u, initBase d a = Sum.inr u ∧ u ∈ d.piles a := by
  cases hti : a.toIdx with
  | zero => exact Or.inl (anchor_toIdx_inj hti)
  | succ k =>
      refine Or.inr ?_
      have hlen : (d.piles a).length = k + 2 := by rw [hd.1 a, hti]
      cases hgt : (d.piles a)[k]? with
      | none =>
          have hbad := List.getElem?_eq_none_iff.mp hgt
          rw [hlen] at hbad
          exact absurd hbad (by omega)
      | some u =>
          refine ⟨u, ?_, ?_⟩
          · show initBase d a = Sum.inr u
            simp only [initBase, hti, hgt]
          · exact List.mem_iff_getElem?.mpr ⟨k, hgt⟩

/-- `initBase` is injective in the anchor at a WF deal. -/
private theorem initBase_eq_of_eq (d : Deal) (hd : d.WF) {a a' : Anchor}
    (h : initBase d a = initBase d a') : a = a' := by
  have hp0 : initBase d Anchor.p0 = Sum.inl Anchor.p0 := rfl
  rcases initBase_shape d hd a with hap | ⟨u, hu, hmu⟩
  · rcases initBase_shape d hd a' with hap' | ⟨u', hu', hmu'⟩
    · rw [hap, hap']
    · rw [hap, hp0, hu'] at h
      exact absurd h (by simp)
  · rcases initBase_shape d hd a' with hap' | ⟨u', hu', hmu'⟩
    · rw [hu, hap', hp0] at h
      exact absurd h (by simp)
    · rw [hu, hu'] at h
      have huu : u = u' := Sum.inr.inj h
      have hmu2 : u ∈ d.piles a' := by rw [huu]; exact hmu'
      exact Deal.piles_disj hd hmu hmu2

/-- The next pile's base is free in the running board: all written seats
belong to processed piles. -/
private theorem initBase_free (d : Deal) (hd : d.WF) {proc : List Anchor}
    {bd : Board} (himg : InitImg d proc bd) {a₀ : Anchor} (hnot : a₀ ∉ proc) :
    bd.topOf (initBase d a₀) = none := by
  cases hocc : bd.topOf (initBase d a₀) with
  | none => rfl
  | some c =>
      exfalso
      obtain ⟨a, ham, hbase, -⟩ := himg.2 _ c hocc
      exact hnot (by rw [initBase_eq_of_eq d hd hbase]; exact ham)

/-- One deal step of the initial fold preserves (and extends) the
board image. -/
private theorem initStep_preserves_Img (d : Deal) (hd : d.WF)
    {proc : List Anchor} {bd : Board} {a₀ : Anchor}
    (himg : InitImg d proc bd) (hnot : a₀ ∉ proc) :
    InitImg d (a₀ :: proc) (initStep d bd a₀) := by
  obtain ⟨h1, h2⟩ := himg
  cases hgt : (d.piles a₀).getLast? with
  | none =>
      have hstep : initStep d bd a₀ = bd := by simp only [initStep, hgt]
      rw [hstep]
      refine ⟨?_, ?_⟩
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | hap
        · rw [initBase_free d hd ⟨h1, h2⟩ hnot, hgt]
        · exact h1 a hap
      · intro b c hb
        obtain ⟨a, ham, hbase, hlast⟩ := h2 b c hb
        exact ⟨a, List.mem_cons_of_mem _ ham, hbase, hlast⟩
  | some top =>
      have hfree := initBase_free d hd ⟨h1, h2⟩ hnot
      have hbotnone : bd.bottomOf top = none := by
        refine (Board.bottomOf_eq_none bd top).mpr (fun b' hb => ?_)
        obtain ⟨a, ham, hb, hlast⟩ := h2 b' top hb
        have hmema : top ∈ d.piles a := mem_of_getLast hlast
        have hmem0 : top ∈ d.piles a₀ := mem_of_getLast hgt
        have hae := Deal.piles_disj hd hmem0 hmema
        rw [← hae] at ham
        exact hnot ham
      have hattach : bd.attach (initBase d a₀) top ≠ none :=
        (Board.attach_eq_some_iff bd (initBase d a₀) top).mpr ⟨hfree, hbotnone⟩
      cases hatt : bd.attach (initBase d a₀) top with
      | none => rw [hatt] at hattach; exact absurd hattach (by simp)
      | some bd' =>
          have hstep : initStep d bd a₀ = bd' := by
            simp only [initStep, hgt, hatt, Option.getD]
          rw [hstep]
          refine ⟨?_, ?_⟩
          · intro a ha
            rcases List.mem_cons.mp ha with hhead | hap
            · rw [hhead]
              rw [Board.attach_topOf bd (initBase d a₀) top hatt, hgt]
            · have hne : initBase d a ≠ initBase d a₀ := by
                intro hcon
                exact hnot (by
                  have heq := (initBase_eq_of_eq d hd hcon).symm
                  rw [heq]
                  exact hap)
              rw [Board.attach_topOf_ne bd (initBase d a₀) top hatt hne]
              exact h1 a hap
          · intro b c hb
            by_cases hbb : b = initBase d a₀
            · rw [hbb, Board.attach_topOf bd (initBase d a₀) top hatt,
                Option.some.injEq] at hb
              exact ⟨a₀, (by simp), hbb, by rw [← hb]; exact hgt⟩
            · rw [Board.attach_topOf_ne bd (initBase d a₀) top hatt hbb] at hb
              obtain ⟨a, ham, hbase, hlast⟩ := h2 b c hb
              exact ⟨a, List.mem_cons_of_mem _ ham, hbase, hlast⟩

/-- The fold driver: the whole dealing sequence boards every pile's top
card. -/
private theorem initFold_img_aux (d : Deal) (hd : d.WF) :
    ∀ (as proc : List Anchor) (bd : Board),
    as.Nodup → proc.Nodup → (∀ a ∈ as, a ∉ proc) →
    (∀ a ∈ as, a ∈ Anchor.all) → (∀ a ∈ proc, a ∈ Anchor.all) →
    InitImg d proc bd →
    InitImg d (as.reverse ++ proc) (as.foldl (initStep d) bd) := by
  intro as
  induction as with
  | nil =>
      intro proc bd _ _ _ _ _ himg
      exact himg
  | cons a₀ rest ih =>
      intro proc bd hnd hndp hdis hallp hallproc himg
      have hstep := initStep_preserves_Img d hd himg (hdis a₀ (by simp))
      obtain ⟨ha0nr, hndr⟩ := List.nodup_cons.mp hnd
      have hproc' : (a₀ :: proc).Nodup :=
        List.nodup_cons.mpr ⟨hdis a₀ (by simp), hndp⟩
      have hdis' : ∀ a ∈ rest, a ∉ a₀ :: proc := by
        intro a har hap
        rcases List.mem_cons.mp hap with heq | happ
        · rw [heq] at har
          exact ha0nr har
        · exact hdis a (List.mem_cons_of_mem _ har) happ
      have hallas : ∀ a ∈ rest, a ∈ Anchor.all :=
        fun a har => hallp a (List.mem_cons_of_mem _ har)
      have hallproc' : ∀ a ∈ a₀ :: proc, a ∈ Anchor.all := by
        intro a hap
        rcases List.mem_cons.mp hap with heq | hp
        · rw [heq]
          exact a₀.mem_all
        · exact hallproc a hp
      have hmm := ih (a₀ :: proc) (initStep d bd a₀) hndr hproc' hdis'
        hallas hallproc' hstep
      rw [show (a₀ :: rest).reverse ++ proc = rest.reverse ++ a₀ :: proc from by
        rw [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]]
      exact hmm

/-- **The initial board seats every pile's top dealt card** at its base
(the deal-adjacent face-up). -/
private theorem initialBoard_seats (d : Deal) (hd : d.WF) (a : Anchor) :
    (initialBoard d).topOf (initBase d a) = (d.piles a).getLast? := by
  have hall := initFold_img_aux d hd Anchor.all [] Board.empty
    (by decide) (by decide)
    (fun _ _ ha => absurd ha (by simp))
    (fun a _ => a.mem_all) (fun _ ha => absurd ha (by simp))
    initImg_empty
  refine hall.1 a ?_
  exact List.mem_reverse.mpr a.mem_all

/-- The dealt game starts `accounted` — every pile card is hidden, or is
its pile's top dealt card, and that card is seated on the initial
board. -/
theorem initial_accounted {d : Deal} (hd : d.WF) (drawStep : Nat) :
    accounted (State.initial d drawStep) := by
  intro a q hq
  have hq' : q ∈ d.piles a := hq
  by_cases hmem : q ∈ (d.piles a).take a.toIdx
  · refine Or.inl ?_
    show q ∈ (d.piles a).take a.toIdx
    exact hmem
  · refine Or.inr (Or.inl ?_)
    obtain ⟨mm, hget⟩ := List.mem_iff_getElem?.mp hq'
    have hlt : mm < (d.piles a).length := (List.getElem?_eq_some_iff.mp hget).1
    have hmi : mm = a.toIdx := by
      by_cases hmi' : mm < a.toIdx
      · exact absurd (mem_take_of_index hmi' hget) hmem
      · rw [hd.1 a] at hlt
        omega
    have hlen : (d.piles a).length - 1 = a.toIdx := by
      have := hd.1 a
      omega
    have hlastidx : (d.piles a)[(d.piles a).length - 1]? = some q := by
      rw [hlen, ← hmi]
      exact hget
    have hlast : (d.piles a).getLast? = some q :=
      getLast?_of_index _ q hlastidx
    have hseat : (initialBoard d).topOf (initBase d a) = some q := by
      rw [initialBoard_seats d hd a, hlast]
    show ((initialBoard d).bottomOf q).isSome = true
    rw [(Board.bottomOf_eq (initialBoard d) q (initBase d a)).mpr hseat]
    rfl

/-! ### The reachability packaging -/

/-- Every dealt-reachable state is `accounted`. -/
theorem accounted_of_initialReachable {st : State}
    (hr : initialReachable st) : accounted st := by
  obtain ⟨d, s, play, hdw, hs, hrun⟩ := hr
  exact run_accounted play (State.initial d s) st (initial_wf hdw hs)
    (initial_accounted hdw s) hrun

/-- **The fence**: at a dealt-reachable state with all depths and all
heights zero, every dealt pile card is visible — the 28 buried cards
cannot all vanish, so the matching must show them. -/
theorem pileCards_seated_of_initialReachable {st : State}
    (hr : initialReachable st)
    (hd : ∀ a, st.depths a = 0) (hh : ∀ s, st.heights s = 0) :
    ∀ a : Anchor, ∀ c : Card, c ∈ st.deal.piles a → st.isVis c = true := by
  intro a c hc
  rcases accounted_of_initialReachable hr a c hc with h | h | h
  · have h' : c ∈ (st.deal.piles a).take (st.depths a) := h
    rw [hd a] at h'
    rw [List.take_zero] at h'
    exact absurd h' (by simp)
  · exact h
  · have h' : decide (c.rank.toIdx < st.heights c.suit) = true := h
    rw [hh c.suit] at h'
    exact absurd (of_decide_eq_true h') (by omega)

/-- The dead-corner reading of the fence: an initialReachable state
cannot have zero depths, zero heights, and an unseated dealt pile
card. -/
theorem unseated_pileCard_unreachable {st : State}
    (hr : initialReachable st)
    (hd : ∀ a, st.depths a = 0) (hh : ∀ s, st.heights s = 0)
    (hex : ∃ a : Anchor, ∃ c : Card,
      c ∈ st.deal.piles a ∧ st.isVis c = false) : False := by
  obtain ⟨a, c, hc, hvis⟩ := hex
  rw [pileCards_seated_of_initialReachable hr hd hh a c hc] at hvis
  exact Bool.noConfusion hvis

/-! ## The KingAnchor replica

Field-identical spelling of `Witnesses.C2KingAnchorWitness`'s private
`wState` (the pristine board, the spade-blocked stock, draw step 1) and
its landing successors, as public constants so the verdict is citable;
each also carries the WF exhibit (the corner is no degenerate junk
state — the fence separates two inhabited worlds). -/

/-- Spades. -/
private def S (r : Rank) : Card := ⟨Suit.spade, r⟩
/-- Hearts. -/
private def H (r : Rank) : Card := ⟨Suit.heart, r⟩
/-- Diamonds. -/
private def D (r : Rank) : Card := ⟨Suit.diamond, r⟩
/-- Clubs. -/
private def C (r : Rank) : Card := ⟨Suit.club, r⟩

/-- The spade-blocked stock (the state's cycle cards are the same
list). -/
private def wStockList : List Card :=
  [S .king, H .king, D .king, C .king] ++
  [C .ace, C .two, C .three, C .four, C .five, C .six, C .seven, C .eight,
   C .nine, C .ten, C .jack, C .queen] ++
  [D .five, D .six, D .seven, D .eight, D .nine, D .ten, D .jack, D .queen]

/-- The witness deal: 28 pile cards (1+2+…+7), 24 stock cards, all 52
distinct (twelve spades in the piles, so the spade count closes). -/
private def wDeal : Deal where
  piles := fun a =>
    match a with
    | .p0 => [S .ace]
    | .p1 => [S .two, S .three]
    | .p2 => [S .four, S .five, S .six]
    | .p3 => [S .seven, S .eight, S .nine, S .ten]
    | .p4 => [S .jack, S .queen, H .ace, H .two, H .three]
    | .p5 => [H .four, H .five, H .six, H .seven, H .eight, H .nine]
    | .p6 => [H .ten, H .jack, H .queen, D .ace, D .two, D .three, D .four]
  stock := wStockList

/-- The replica of the pristine witness state. -/
def wstate : State where
  deal := wDeal
  board := Board.empty
  heights := fun _ => 0
  depths := fun _ => 0
  stock := ⟨wStockList, 0⟩
  drawStep := 1

/-- The landing successor on anchor `a` (the Draw-commitment splice of
the stocked king — the matching-first-card shape). -/
private def wBoard (a : Anchor) : Board where
  topOf := fun b => if b = Sum.inl a then some (S .king) else none
  inj := by
    intro b₁ b₂ c h₁ h₂
    by_cases h1 : b₁ = Sum.inl a
    · rw [ite_eq_left h1] at h₁
      by_cases h2 : b₂ = Sum.inl a
      · rw [h1, h2]
      · rw [ite_eq_right h2] at h₂
        simp at h₂
    · rw [ite_eq_right h1] at h₁
      simp at h₁

/-- The replica of the king's landing successor on anchor `a`. -/
def wsucc (a : Anchor) : State :=
  { wstate with board := wBoard a, stock := ⟨Cycle.removeIdx wStockList 0, 0⟩ }

/-! ### WF exhibits -/

private theorem wDeal_wf : wDeal.WF := by
  refine ⟨fun a => ?_, by decide, ?_⟩
  · cases a <;> decide
  · intro i j hi hj heq
    have hflat : (Anchor.all.flatMap wDeal.piles).length = 28 := by decide
    have hstock : wDeal.stock.length = 24 := by decide
    rw [List.length_append, hflat, hstock] at hi hj
    have hall : ∀ i ∈ List.range 52, ∀ j ∈ List.range 52,
        (Anchor.all.flatMap wDeal.piles ++ wDeal.stock)[i]? =
          (Anchor.all.flatMap wDeal.piles ++ wDeal.stock)[j]? → i = j := by decide
    exact hall i (List.mem_range.mpr hi) j (List.mem_range.mpr hj) heq

/-- The pristine corner is WF — the replica of the read-only witness's
own exhibit. -/
theorem wstate_wf : wstate.WF := by
  refine State.WF.intro wDeal_wf ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a
    show (0 : Nat) ≤ (wDeal.piles a).length
    cases a <;> decide
  · intro b _ htop
    have hnone : wstate.board.topOf b = none := Board.empty_topOf b
    rw [hnone] at htop
    exact absurd htop (by simp)
  · intro c hc
    have hc' : (wstate.board.bottomOf c).isSome = true := hc
    have hn : wstate.board.bottomOf c = none := Board.empty_bottomOf c
    rw [hn] at hc'
    simp at hc'
  · intro c h
    have h0 : wstate.heights c.suit = 0 := rfl
    have hc : decide (c.rank.toIdx < wstate.heights c.suit) = true := h
    rw [h0] at hc
    simp at hc
  · intro c hc
    have h0 : wstate.heights c.suit = 0 := rfl
    rw [h0] at hc
    exact absurd hc (by omega)
  · intro c hc a hc'
    have hc'' : (wstate.board.bottomOf c).isSome = true := hc
    have hn : wstate.board.bottomOf c = none := Board.empty_bottomOf c
    rw [hn] at hc''
    simp at hc''
  · intro _
    exact Nat.zero_le _
  · show wstate.stock.cursor ≤ wstate.stock.cards.length
    decide
  · exact Nat.zero_lt_one
  · refine ⟨fun i j hi hj heq => ?_, fun _ hmem => hmem⟩
    have hall : ∀ i ∈ List.range 24, ∀ j ∈ List.range 24,
        wStockList[i]? = wStockList[j]? → i = j := by decide
    exact hall i (List.mem_range.mpr hi) j (List.mem_range.mpr hj) heq

private theorem wsucc_board_eq (a : Anchor) : (wsucc a).board = wBoard a := rfl

private theorem wsucc_topOf (a : Anchor) (b : Base) :
    (wsucc a).board.topOf b = (if b = Sum.inl a then some (S .king) else none) := by
  rw [wsucc_board_eq]
  rfl

private theorem wsucc_topOf_base (a : Anchor) :
    (wsucc a).board.topOf (Sum.inl a) = some (S .king) := by
  have htb := wsucc_topOf a (Sum.inl a)
  rw [ite_eq_left rfl] at htb
  exact htb

private theorem wsucc_topOf_inr (a : Anchor) (d : Card) :
    (wsucc a).board.topOf (Sum.inr d) = none := by
  have htb := wsucc_topOf a (Sum.inr d)
  rw [ite_eq_right (by simp : (Sum.inr d : Base) ≠ Sum.inl a)] at htb
  exact htb

/-- Only the stocked king sits on a landing successor's board. -/
private theorem wsucc_bottomOf_of_ne (a : Anchor) {c : Card} (hnc : c ≠ S .king) :
    (wsucc a).board.bottomOf c = none := by
  refine (Board.bottomOf_eq_none _ _).mpr (fun b hb => ?_)
  have htb := wsucc_topOf a b
  rw [htb] at hb
  by_cases hba : b = Sum.inl a
  · rw [ite_eq_left hba] at hb
    exact hnc (Option.some.inj hb).symm
  · rw [ite_eq_right hba] at hb
    exact absurd hb (by simp)

/-- The stock slice is duplicate-free at every index (kernel-decided
over the bounded range). -/
private theorem wStockList_noDup : noDupCards wStockList := by
  have hall : ∀ i ∈ List.range 24, ∀ j ∈ List.range 24,
      wStockList[i]? = wStockList[j]? → i = j := by decide
  intro i j hi hj heq
  exact hall i (List.mem_range.mpr hi) j (List.mem_range.mpr hj) heq

/-- The landing successor is WF too (the stock splice and the one-edge
board preserve shape). -/
theorem wsucc_wf (a : Anchor) : (wsucc a).WF := by
  refine State.WF.intro wDeal_wf ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a'
    show (0 : Nat) ≤ (wDeal.piles a').length
    cases a' <;> decide
  · intro b c htop
    have htb := wsucc_topOf a b
    rw [htb] at htop
    by_cases hbb : b = Sum.inl a
    · rw [ite_eq_left hbb, Option.some.injEq] at htop
      have hcK : c = S .king := htop.symm
      refine ⟨?_, ?_⟩
      · show (wsucc a).board.bottomOf c = some b
        rw [hcK]
        exact (Board.bottomOf_eq _ _ b).mpr (by
          rw [hbb]
          exact wsucc_topOf_base a)
      · rw [hbb, hcK]
        exact Or.inl rfl
    · rw [ite_eq_right hbb] at htop
      exact absurd htop (by simp)
  · intro c hc
    have hc' : ((wsucc a).board.bottomOf c).isSome = true := hc
    by_cases hck : c = S .king
    · rw [hck]
      exact Cycle.posOf_eq_none
        (Cycle.notMem_removeIdx_self (by
          intro j hj
          have hlt := (List.getElem?_eq_some_iff.mp hj).1
          have hall : ∀ i ∈ List.range 24,
              wStockList[i]? = some (S .king) → i = 0 := by decide
          exact hall j (List.mem_range.mpr hlt) hj))
    · rw [wsucc_bottomOf_of_ne a hck] at hc'
      exact absurd hc' (by simp)
  · intro c h
    have h0 : (wsucc a).heights c.suit = 0 := rfl
    have hc : decide (c.rank.toIdx < (wsucc a).heights c.suit) = true := h
    rw [h0] at hc
    simp at hc
  · intro c hc
    have h0 : (wsucc a).heights c.suit = 0 := rfl
    rw [h0] at hc
    exact absurd hc (by omega)
  · intro c hc a' hc'
    have hc'' : ((wsucc a).board.bottomOf c).isSome = true := hc
    by_cases hck : c = S .king
    · exfalso
      have hm : S .king ∉ (wsucc a).hidden a' := by
        show S .king ∉ (wDeal.piles a').take (0 : Nat)
        rw [List.take_zero]
        intro hh
        exact absurd hh (by simp)
      rw [hck] at hc'
      exact hm hc'
    · rw [wsucc_bottomOf_of_ne a hck] at hc''
      exact absurd hc'' (by simp)
  · intro _
    exact Nat.zero_le _
  · show (0 : Nat) ≤ ((wsucc a).stock.cards).length
    exact Nat.zero_le _
  · exact Nat.zero_lt_one
  · refine ⟨noDupCards_removeIdx wStockList 0 wStockList_noDup,
      fun _ hmem => Cycle.mem_removeIdx wStockList 0 hmem⟩

/-! ### The verdicts: the KingAnchor corner is unreachable -/

/-- The KingAnchor pristine state is not dealt-reachable: the fence
demands every pile card seated, the board is empty. -/
theorem wstate_not_initialReachable : ¬ initialReachable KingAnchorReach.wstate := by
  intro hr
  refine unseated_pileCard_unreachable hr (fun _ => rfl) (fun _ => rfl)
    ⟨Anchor.p0, S .ace, by decide, ?_⟩
  show (wstate.board.bottomOf (S .ace)).isSome = false
  rw [show wstate.board.bottomOf (S .ace) = none from
    Board.empty_bottomOf (S .ace)]
  rfl

/-- Every landing successor of the stocked king is not dealt-reachable
either: the fence demands every pile card seated, the board shows only
the king (a stock card). -/
theorem wsucc_not_initialReachable (a : Anchor) :
    ¬ initialReachable (KingAnchorReach.wsucc a) := by
  intro hr
  refine unseated_pileCard_unreachable hr (fun _ => rfl) (fun _ => rfl)
    ⟨Anchor.p0, S .ace, by show S .ace ∈ wDeal.piles Anchor.p0; decide, ?_⟩
  show ((wsucc a).board.bottomOf (S .ace)).isSome = false
  rw [wsucc_bottomOf_of_ne a (by decide : S .ace ≠ S .king)]
  rfl

/-! ## The anchored-heads replica (the succLabeled family)

Field-identical spelling of `Witnesses.SuccLabeledWitness`'s private
`uState`: every anchor seated by its own dealt head (♥A, ♦2, ♣5, ♣6,
♣7, ♣8, ♣9), all heights and depths zero, the spade-blocked stock with
♠K drawn first — the board that kills the as-stated `succ_labeled`.
The fence demands every pile card seated; this board seats only the
seven heads, and e.g. `uDeal.piles p1 = [♦2, ♠A]` buries ♠A nowhere.
-/

/-- The dealt head seated on anchor `a`. -/
private def uHead : Anchor → Card
  | .p0 => H .ace
  | .p1 => D .two
  | .p2 => C .five
  | .p3 => C .six
  | .p4 => C .seven
  | .p5 => C .eight
  | .p6 => C .nine

private theorem uHead_ne (a a' : Anchor) (h : uHead a = uHead a') : a = a' := by
  cases a <;> cases a' <;> first
    | rfl
    | exact absurd h (by decide)

private theorem uHead_notSpade (a : Anchor) : (uHead a).suit ≠ Suit.spade := by
  cases a <;> decide

/-- The board function: the head on each anchor's base, nothing on any
card base. -/
private def uTopOf : Base → Option Card := fun b =>
  match b with
  | Sum.inl a => some (uHead a)
  | Sum.inr _ => none

private theorem uTopOf_inl (a : Anchor) : uTopOf (Sum.inl a) = some (uHead a) := rfl
private theorem uTopOf_inr (d : Card) : uTopOf (Sum.inr d) = none := rfl

private theorem uBoard_inj : ∀ (b₁ b₂ : Base) (c : Card),
    uTopOf b₁ = some c → uTopOf b₂ = some c → b₁ = b₂ := by
  intro b₁ b₂ c h₁ h₂
  cases b₁ with
  | inl a₁ =>
      cases b₂ with
      | inl a₂ =>
          rw [uTopOf_inl] at h₁
          rw [uTopOf_inl] at h₂
          have h₃ : uHead a₁ = uHead a₂ :=
            (Option.some.inj h₁).trans (Option.some.inj h₂).symm
          exact congrArg Sum.inl (uHead_ne a₁ a₂ h₃)
      | inr d₂ =>
          rw [uTopOf_inr] at h₂
          exact absurd h₂ (by simp)
  | inr d₁ =>
      rw [uTopOf_inr] at h₁
      exact absurd h₁ (by simp)

/-- The anchored-heads witness board — seven anchor-head edges. -/
private def uBoard : Board := ⟨uTopOf, uBoard_inj⟩

private theorem uBoard_topOf_inl (a : Anchor) :
    uBoard.topOf (Sum.inl a) = some (uHead a) := rfl

private theorem uBoard_topOf_inr (d : Card) : uBoard.topOf (Sum.inr d) = none := rfl

private def uStockList : List Card :=
  [S .king, H .jack, H .queen, H .king] ++
  [D .ace, D .three, D .four, D .five, D .six, D .seven, D .eight,
   D .nine, D .ten, D .jack, D .queen, D .king] ++
  [C .ace, C .two, C .three, C .four, C .ten, C .jack, C .queen, C .king]

private def uDeal : Deal where
  piles := fun a =>
    match a with
    | .p0 => [H .ace]
    | .p1 => [D .two, S .ace]
    | .p2 => [C .five, S .two, S .three]
    | .p3 => [C .six, S .four, S .five, S .six]
    | .p4 => [C .seven, S .seven, S .eight, S .nine, S .ten]
    | .p5 => [C .eight, S .jack, S .queen, H .two, H .three, H .four]
    | .p6 => [C .nine, H .five, H .six, H .seven, H .eight, H .nine, H .ten]
  stock := uStockList

/-- The replica of the anchored-heads witness state. -/
def ustate : State where
  deal := uDeal
  board := uBoard
  heights := fun _ => 0
  depths := fun _ => 0
  stock := ⟨uStockList, 0⟩
  drawStep := 1

/-! ### The verdict: the anchored-heads corner is unreachable -/

/-- Only the dealt heads sit on the anchored-heads board — no other
pile card has a seat. -/
private theorem ustate_bottomOf_spades (c : Card)
    (hcs : c.suit = Suit.spade) : ustate.board.bottomOf c = none := by
  refine (Board.bottomOf_eq_none _ _).mpr (fun b hb => ?_)
  cases b with
  | inl a =>
      have hba : uBoard.topOf (Sum.inl a) = some c := hb
      rw [uBoard_topOf_inl] at hba
      have hEq : uHead a = c := Option.some.inj hba
      have hs : (uHead a).suit = Suit.spade := by rw [hEq]; exact hcs
      exact uHead_notSpade a hs
  | inr d =>
      have hba : uBoard.topOf (Sum.inr d) = some c := hb
      rw [uBoard_topOf_inr] at hba
      exact absurd hba (by simp)

/-- The succLabeled corner state is not dealt-reachable: the fence
demands every pile card seated, but ♠A (dealt in pile 1 behind the
anchored head ♦2) is neither hidden, nor founded, and the board holds
only the seven non-spade heads. -/
theorem ustate_not_initialReachable : ¬ initialReachable KingAnchorReach.ustate := by
  intro hr
  refine unseated_pileCard_unreachable hr (fun _ => rfl) (fun _ => rfl)
    ⟨Anchor.p1, S .ace, by decide, ?_⟩
  show (ustate.board.bottomOf (S .ace)).isSome = false
  rw [ustate_bottomOf_spades (S .ace) rfl]
  rfl

end KingAnchorReach

/-! ## The per-pillar verdict table

Witness-grade countermodels exist (the five negations hold at the
WF corners) but every root below is OUTSIDE the dealt-reachable
fragment (`KingAnchorReach.wstate_not_initialReachable`,
`.wsucc_not_initialReachable`, `.ustate_not_initialReachable`), so the
initialReachable-gated restorations lose this witness family:

* `wk_c2_as_stated_false` — RESTORED under hreach (witness unreachable;
  obstruction: pile-card conservation);
* `wk_same_pin_as_stated_false` — RESTORED under hreach (same);
* `wk_p2_direct_as_stated_false` — RESTORED under hreach (same);
* `wk_crease_as_stated_false` — RESTORED under hreach (same);
* `wk_succ_labeled_as_stated_false` — RESTORED under hreach (same).

None of the restricted universals is proven here — the corpus-observed
weak corners are dealt-reachable, so their proofs carry real content.
-/

#print axioms KingAnchorReach.pileCards_seated_of_initialReachable
#print axioms KingAnchorReach.wstate_not_initialReachable
#print axioms KingAnchorReach.wsucc_not_initialReachable
#print axioms KingAnchorReach.ustate_not_initialReachable
