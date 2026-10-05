import Klondike.Restriction
import Witnesses.C2KingAnchorWitness
import Witnesses.SuccLabeledWitness

/-!
# The reachability probe — both pristine-family witnesses live off the
dealt-reachable fragment

(NOTE wave-20: this file now imports `Witnesses.SuccLabeledWitness` —
the second witness-file cross-import after the wave-19B facade edit —
because the third verdict is stated at the deprivatized
`SuccLabeled.uState`; the import chain stays acyclic, the two files
disagree on no names.)

The wave-18/19 refutation witnesses counterexample four + one as-stated
C2 universals at hand-crafted WF states:
`Witnesses.C2KingAnchorWitness` (the pristine empty board whose stocked,
climb-blocked king splits its landings seven ways, killing the as-stated
`wk_c2`, `wk_same_pin`, `wk_p2_direct` and `wk_crease`) and
`Witnesses.SuccLabeledWitness` (the anchored-head board killing the
as-stated `wk_succ_labeled`).  This file decided the wave-19B
restoration datum — none of the witness roots, nor the KingAnchor
commitment's landing
successors, is `initialReachable` (Restriction.lean) — so no gated
re-statement of the five universals is within THIS family's reach.
The wave-20 session re-stated all three verdicts at the deprivatized
originals (`KingAnchor.wState`/`KingAnchor.wSucc`, `SuccLabeled.uState`)
and revised the table at the file's end: the reachable fragment has
its own machine-checked countermodels, so the naive gated readings
still fail — the proven regimes are the rung and weak-corner theorems
of `Klondike.C2Streamlined` (§12.5, §15).

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
* `KingAnchorReach.wState_not_initialReachable`,
  `KingAnchorReach.wSucc_not_initialReachable (a)`,
  `KingAnchorReach.uState_not_initialReachable` — the per-root
  verdicts, stated (wave-20) directly at the deprivatized witness
  originals — the wave-19B replica spellings are retired.  Each
  original's own file carries its WF exhibit, so the fence separates
  two genuinely inhabited worlds: the corners are WF-inhabited but
  deal-unreachable;
* (`Klondike.Initial.initialBoard_seats` — the deal-fold forward
  seating theorem this file's initial case needs — was moved INTO the
  lib at wave-20 so it is reusable everywhere; `getLast?_of_index`
  went with it.)

The verdicts do NOT prove the restricted universals — and wave-20
sharpened that caveat from "carry real content" to "fail at reachable
corners": the reachable fragment presents the same shapes
(`Witnesses.SuccLabeledWitness`, the reachable-corner addendum), so
the gated restorations hold only in the proven regimes (the
stackable-rung §12.5 and the weak-corner §15 of `Klondike.C2Streamlined`),
with the residue as explicit premises.  This file states the exact
fence the restorations may lean on.
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

/-! ### The initial state

The forward seating theorem the initial case needs — the deal fold
boards EVERY pile's top card at its `initBase` — moved to the lib at
wave-20: `Klondike.Initial.initialBoard_seats` (with
`getLast?_of_index`).  Only the deal-adjacent `accounted` packaging
remains here. -/

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

/-! ## The three verdicts, at the witness corners themselves (wave-20)

The wave-19B replicas are retired.  The as-stated witnesses' states
were deprivatized (`KingAnchor.wDeal`/`KingAnchor.wState`/
`KingAnchor.wSucc`/`KingAnchor.wS_shape`/`KingAnchor.wBoard`/
`KingAnchor.wS_bot_none` in `Witnesses.C2KingAnchorWitness`,
`SuccLabeled.uState` in `Witnesses.SuccLabeledWitness`), so each
verdict is now stated directly at the original it is about.  Every
proof is the fence applied to the original's own fields — one
`unseated_pileCard_unreachable` per corner, as before, but with no
replica spelling in between.  The WF exhibits stay with the originals
(their own files carry them); the fence separates two genuinely
inhabited worlds — the corners are WF-inhabited but deal-unreachable. -/

/-- Spades. -/
private def S (r : Rank) : Card := ⟨Suit.spade, r⟩

/-- The KingAnchor pristine root is not dealt-reachable: the fence
demands every dealt pile card seated at zero depths and heights, and
the pristine board is empty. -/
theorem wState_not_initialReachable :
    ¬ initialReachable KingAnchor.wState := by
  intro hr
  refine unseated_pileCard_unreachable hr (fun _ => rfl) (fun _ => rfl)
    ⟨Anchor.p0, S .ace, by show S .ace ∈ KingAnchor.wDeal.piles Anchor.p0; decide, ?_⟩
  show (KingAnchor.wState.board.bottomOf (S .ace)).isSome = false
  have hb : KingAnchor.wState.board.bottomOf (S .ace) = none :=
    Board.empty_bottomOf (S .ace)
  rw [hb]
  rfl

/-- Every landing successor of the stocked king is not dealt-reachable
either: the fence demands every dealt pile card seated, while the
landing board shows only the king (a stock card). -/
theorem wSucc_not_initialReachable (a : Anchor) :
    ¬ initialReachable (KingAnchor.wSucc a) := by
  intro hr
  rw [KingAnchor.wS_shape a] at hr
  refine unseated_pileCard_unreachable hr (fun _ => rfl) (fun _ => rfl)
    ⟨Anchor.p0, S .ace, by show S .ace ∈ KingAnchor.wDeal.piles Anchor.p0; decide, ?_⟩
  show ((KingAnchor.wBoard a).bottomOf (S .ace)).isSome = false
  have hb : (KingAnchor.wBoard a).bottomOf (S .ace) = none := by
    refine (Board.bottomOf_eq_none _ _).mpr (fun b htb => ?_)
    have htop : (KingAnchor.wBoard a).topOf b
        = (if b = Sum.inl a then some (S .king) else none) := rfl
    rw [htop] at htb
    by_cases hba : b = Sum.inl a
    · rw [ite_eq_left hba] at htb
      exact absurd (Option.some.inj htb).symm (by decide)
    · rw [ite_eq_right hba] at htb
      exact absurd htb (by simp)
  rw [hb]
  rfl

/-- The succLabeled corner state is not dealt-reachable: the fence
demands every dealt pile card seated, but ♠A (dealt in pile 1 behind
the anchored head ♦2) is neither hidden, nor founded, and the anchored
heads board holds only its seven non-spade heads. -/
theorem uState_not_initialReachable :
    ¬ initialReachable SuccLabeled.uState := by
  intro hr
  refine unseated_pileCard_unreachable hr (fun _ => rfl) (fun _ => rfl)
    ⟨Anchor.p1, S .ace, by decide, ?_⟩
  show (SuccLabeled.uState.board.bottomOf (S .ace)).isSome = false
  have hb : SuccLabeled.uState.board.bottomOf (S .ace) = none := by
    refine (Board.bottomOf_eq_none _ _).mpr (fun b htb => ?_)
    cases b with
    | inl a =>
        cases a <;> exact absurd htb (by decide)
    | inr d =>
        have htb2 : SuccLabeled.uState.board.topOf (Sum.inr d) = none := rfl
        rw [htb2] at htb
        exact absurd htb (by simp)
  rw [hb]
  rfl

end KingAnchorReach

/-! ## The per-pillar verdict table

Witness-grade countermodels exist (the five negations hold at the WF
corners) and every root below is OUTSIDE the dealt-reachable fragment
(`KingAnchorReach.wState_not_initialReachable`,
`.wSucc_not_initialReachable (a)`, `.uState_not_initialReachable`),
which excludes THIS pristine witness family from any gated
restatement:

* `wk_c2_as_stated_false` — the pristine root unreachable;
* `wk_same_pin_as_stated_false` — same;
* `wk_p2_direct_as_stated_false` — same (and all seven landing
  successors unreachable, so successor-side reachability premises are
  safe from this family too);
* `wk_crease_as_stated_false` — same;
* `wk_succ_labeled_as_stated_false` — the anchored-heads root
  unreachable.

**WAVE-20 REVISION** (2026-10-05, the C2-restoration session): the
wave-19B row read these verdicts as "RESTORED under hreach" — the
pristine refutations cannot touch the gated world.  That reading was
too strong: the fences exclude only the pristine SHAPES (empty board,
zero depths); the reachable fragment presents the same countermodel
and route shapes at honest dealt **initial states**, built as
machine-checked reachable countermodels in `Witnesses.SuccLabeledWitness`
(the reachable-corner addendum: `SuccLabeled.wk_c2_reachable_false`,
`.wk_same_pin_reachable_false`, `.wk_p2_direct_reachable_false`,
`.wk_crease_reachable_false`, and `.wk_succ_labeled_reachable_false`).
So none of the five gated universals holds in the naive gated form;
what IS proven lives in `Klondike.C2Streamlined` — the stackable-rung
regime (§9.5/§12.5, ungated) and the wave-20 weak-corner shapes
(§15: at-most-one free anchor, frozen suit).  The corpus-observed
weak corners are dealt-reachable, so those proofs carry real content. -/

#print axioms KingAnchorReach.pileCards_seated_of_initialReachable
#print axioms KingAnchorReach.wState_not_initialReachable
#print axioms KingAnchorReach.wSucc_not_initialReachable
#print axioms KingAnchorReach.uState_not_initialReachable
