import Klondike.TwinAgnostic
import Klondike.TwinExchange

/-!
# The twin quotient — the pair group and the license (layers 0–1)

The quotient layer for `exchangeTwinCargo` (TwinExchange.lean): the
tableau's twin pairs are interchangeable as CARGO SEATS, and the twin
quotient representation identifies states up to that exchange.  This
file lands the branch-independent stones:

* **Layer 0 — the pair group**: the exchange names the PAIR, not the
  twin (`exchangeTwinCargo_pair`), and exchanges at disjoint pairs
  COMMUTE (`exchangeTwinCargo_comm`) — the elementary-abelian-2
  structure that makes a canonical normal form (Layer 5's `canon`)
  order-independent.
* **Layer 1 — the license and its descent**: `State.twinLicensed`
  bundles the both-occupied row's shape premises (the hypotheses of
  TwinExchange's `solvable_cargoTwin_exchange`, minus `hwf`, which
  rides separately); `wf_exchangeTwinCargo` descends WF through the
  exchange — the two swapped ROOT edges re-derive through the fit
  disjunct of `board_edges` (the `hfit` corner's formal content: the
  deal-adjacency clause cannot transfer across the swap, so the base
  stays placed and the cargo must still fit it); and
  `twinLicensed_exchangeTwinCargo` transfers the license through the
  exchange (visibility and the `aboveOf` walks are exchange-invariant
  off the pair, the fits ride twin-blindness) — which hands the row
  its iff from one direction, via the involution.

Also exported for the later layers: the pointwise visibility law
(cite `State.isVis_exchangeTwin`, TwinExchange.lean:960) and the
no-braid walk congruence (`Board.aboveOf_exchangeTwin`) — the Layer 3
merge bookkeeping and the Layer 5 `canon` both consume them.

Layers 3–4 (the scaffold): the seventh clean-step mechanic
(`exchangeTwinCargo_step_pileStack`, proven), the twin-rooted
`pilePile` mirror (`exchangeTwinCargo_step_pilePile_root`, proven) and
the row's iff from the forward direction (`solvable_iff_exchangeTwinCargo`,
proven modulo the simulation) are landed; the merge bridge
(`solvable_of_exchange_merge`) and its twin-rooted companion
(`solvable_of_exchange_merge_rooted`) are the named TODOs — the [H]
crux and its rooted corner.  Layer 5 (`canon`/confluence) remains
future.
-/

/-! ## Layer 0 — the pair group -/

/-- Off the pair transfers across the flip: `b` off `t`'s pair has
`b.flipSuit` off it too (each pair is flipSuit-closed). -/
theorem Card.offPair_flipSuit {t b : Card} (h₁ : b ≠ t) (h₂ : b ≠ t.flipSuit) :
    b.flipSuit ≠ t ∧ b.flipSuit ≠ t.flipSuit := by
  constructor
  · intro h
    have h' := congrArg Card.flipSuit h
    simp only [Card.flipSuit_flipSuit] at h'
    exact h₂ h'
  · intro h
    have h' := congrArg Card.flipSuit h
    simp only [Card.flipSuit_flipSuit] at h'
    exact h₁ h'

/-- Disjoint twin transpositions commute, pointwise (two swaps with
disjoint support). -/
theorem Card.swapTwin_comm {t u : Card} (h₁ : u ≠ t) (h₂ : u ≠ t.flipSuit) (x : Card) :
    Card.swapTwin t (Card.swapTwin u x) = Card.swapTwin u (Card.swapTwin t x) := by
  have hu := Card.offPair_flipSuit h₁ h₂
  by_cases hxu : x = u
  · subst hxu
    rw [Card.swapTwin_self_left, Card.swapTwin_of_ne hu.1 hu.2,
      Card.swapTwin_of_ne h₁ h₂, Card.swapTwin_self_left]
  · by_cases hxu' : x = u.flipSuit
    · subst hxu'
      rw [Card.swapTwin_self_right, Card.swapTwin_of_ne h₁ h₂,
        Card.swapTwin_of_ne hu.1 hu.2, Card.swapTwin_self_right]
    · rw [Card.swapTwin_of_ne hxu hxu']
      by_cases hxt : x = t
      · subst hxt
        rw [Card.swapTwin_self_left, Card.swapTwin_of_ne (Ne.symm h₂) (Ne.symm hu.2)]
      · by_cases hxt' : x = t.flipSuit
        · subst hxt'
          rw [Card.swapTwin_self_right, Card.swapTwin_of_ne (Ne.symm h₁) (Ne.symm hu.1)]
        · rw [Card.swapTwin_of_ne hxt hxt', Card.swapTwin_of_ne hxu hxu']

/-- Base-level commutation: disjoint pairs' seat relabelings commute. -/
theorem Base.swapTwin_comm {t u : Card} (h₁ : u ≠ t) (h₂ : u ≠ t.flipSuit) (b : Base) :
    (b.swapTwin u).swapTwin t = (b.swapTwin t).swapTwin u := by
  cases b with
  | inl a => rfl
  | inr x =>
      show Sum.inr (Card.swapTwin t (Card.swapTwin u x))
        = Sum.inr (Card.swapTwin u (Card.swapTwin t x))
      rw [Card.swapTwin_comm h₁ h₂ x]

/-- **The pair group is abelian**: exchanges at disjoint twin pairs
commute (the substrate for Layer 5's order-independent canonical
form). -/
theorem Board.exchangeTwin_comm (bd : Board) (t u : Card)
    (h₁ : u ≠ t) (h₂ : u ≠ t.flipSuit) :
    (bd.exchangeTwin t).exchangeTwin u = (bd.exchangeTwin u).exchangeTwin t := by
  apply Board.ext_topOf
  funext b
  simp only [Board.exchangeTwin_topOf]
  rw [Base.swapTwin_comm h₁ h₂ b]

/-- State-level commutation (the board-only lift). -/
theorem State.exchangeTwinCargo_comm (st : State) (t u : Card)
    (h₁ : u ≠ t) (h₂ : u ≠ t.flipSuit) :
    (st.exchangeTwinCargo t).exchangeTwinCargo u
      = (st.exchangeTwinCargo u).exchangeTwinCargo t := by
  apply state_ext
  · rfl
  · exact Board.exchangeTwin_comm st.board t u h₁ h₂
  · rfl
  · rfl
  · rfl
  · rfl

/-- The exchange names the pair: `t` and `t.flipSuit` generate the
same exchange (the pair is unordered). -/
theorem Board.exchangeTwin_pair (bd : Board) (t : Card) :
    bd.exchangeTwin t.flipSuit = bd.exchangeTwin t := by
  apply Board.ext_topOf
  funext b
  simp only [Board.exchangeTwin_topOf]
  exact congrArg bd.topOf (Base.swapTwin_flipSuit t b)

/-- State-level pair-naming (the license below is a predicate of the
pair, not of the twin). -/
theorem State.exchangeTwinCargo_pair (st : State) (t : Card) :
    st.exchangeTwinCargo t.flipSuit = st.exchangeTwinCargo t := by
  apply state_ext
  · rfl
  · exact Board.exchangeTwin_pair st.board t
  · rfl
  · rfl
  · rfl
  · rfl

/-! ## Layer 1 — the license and its descent -/

/-- The exchange re-seats every card's base but never empties or
fills one: placedness (and so visibility) is pointwise
exchange-invariant. -/
theorem State.bottomOf_isSome_exchangeTwinCargo (st : State) (t d : Card) :
    ((st.exchangeTwinCargo t).board.bottomOf d).isSome
      = (st.board.bottomOf d).isSome := by
  rw [State.exchangeTwinCargo_board, Board.bottomOf_exchangeTwin]
  cases st.board.bottomOf d <;> rfl

/-- The hidden boundary is untouched (deal and depths ride the
board-only lift). -/
theorem State.exchangeTwinCargo_topHidden (st : State) (t : Card) (a : Anchor) :
    (st.exchangeTwinCargo t).topHidden a = st.topHidden a := rfl

/-- **The no-braid walk congruence**: the run above an off-pair card
never reads the exchanged seats (the no-braid premises exclude the
twins from the walk), so it is exchange-invariant.  Layer 3's merge
bookkeeping and the license transfer below both consume this. -/
theorem Board.aboveOf_exchangeTwin {bd : Board} {t c : Card}
    (hoff : c ≠ t) (hoff' : c ≠ t.flipSuit)
    (hnb : t ∉ bd.aboveOf c ∧ t.flipSuit ∉ bd.aboveOf c) :
    (bd.exchangeTwin t).aboveOf c = bd.aboveOf c := by
  apply Board.aboveOf_congr
  intro x hx
  have hx' : x ≠ t ∧ x ≠ t.flipSuit := by
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact ⟨hoff, hoff'⟩
    · exact ⟨fun h => hnb.1 (h ▸ hmem), fun h => hnb.2 (h ▸ hmem)⟩
  have hxe : Base.swapTwin t (Sum.inr x) = Sum.inr x :=
    congrArg Sum.inr (Card.swapTwin_of_ne hx'.1 hx'.2)
  rw [Board.exchangeTwin_topOf, hxe]

/-! ### The walk transitivity — the missing keystone

`aboveOf` is transitive on RAW boards (no WF): the matching's `inj`
makes the up-chain from any card unique, so the walk from `x` is a
tail of the walk from `y` whenever `x ∈ aboveOf y` — the
guard-truncation is symmetric around cycles, so nothing is lost.
The merge case's landing analysis (the off-cargo split below)
consumes this; the seed-tricks elsewhere dance around it.
-/

/-- **The walk reaches every card it collects**: either the card was
seeded, or the walk, at some recursion depth, sits ON the card's seat
with the card heading the accumulator — carrying the fuel/length
bookkeeping (one fuel unit per collected card) and the accumulator's
duplicate-freeness, so the seat-split never runs on empty fuel (53
collected cards would be needed; the deck has 52). -/
theorem Board.aboveOf_go_reaches {bd : Board} :
    ∀ (n : Nat) (b : Base) (acc : List Card) (u : Card),
      acc.Nodup →
      u ∈ Board.aboveOf.go bd n b acc →
      u ∈ acc ∨ ∃ (m : Nat) (A : List Card),
        Board.aboveOf.go bd n b acc = Board.aboveOf.go bd m (Sum.inr u) (u :: A) ∧
          m + (u :: A).length = n + acc.length ∧ (u :: A).Nodup := by
  intro n
  induction n with
  | zero => intro b acc u _ hu; exact Or.inl hu
  | succ k ih =>
      intro b acc u hnd hu
      cases ht : bd.topOf b with
      | none => rw [Board.aboveOf_go_topOf_none ht] at hu; exact Or.inl hu
      | some c' =>
          by_cases hc : acc.contains c' = true
          · rw [Board.aboveOf_go_stop ht hc] at hu; exact Or.inl hu
          · rw [Board.aboveOf_go_step ht hc] at hu
            have hnd' : (c' :: acc).Nodup :=
              List.nodup_cons.mpr ⟨fun hmem => hc ((List.contains_iff_mem).mpr hmem), hnd⟩
            rcases ih (Sum.inr c') (c' :: acc) u hnd' hu with h | ⟨m, A, heq, hlen, hndA⟩
            · rcases List.mem_cons.mp h with heq' | h'
              · subst heq'
                refine Or.inr ⟨k, acc, Board.aboveOf_go_step ht hc, ?_, hnd'⟩
                have hl : (u :: acc).length = acc.length + 1 := rfl
                omega
              · exact Or.inl h'
            · refine Or.inr ⟨m, A, (Board.aboveOf_go_step ht hc).trans heq, ?_, hndA⟩
              have hl : (c' :: acc).length = acc.length + 1 := rfl
              omega

/-- **The walk's successor closure**: a collected card's own successor
was read one step past it — the seat-split lemma at fuel 53 (the
empty-fuel corner dies on the 52-count). -/
theorem Board.aboveOf_succ_closed {bd : Board} {y u v : Card}
    (hu : u ∈ bd.aboveOf y) (hv : bd.topOf (Sum.inr u) = some v) :
    v ∈ bd.aboveOf y := by
  rw [Board.aboveOf_eq_go 53 (by omega)] at hu ⊢
  rcases Board.aboveOf_go_reaches 53 (Sum.inr y) [] u (by simp) hu with h | ⟨m, A, heq, hlen, hndA⟩
  · exact absurd h (by simp)
  · rw [heq]
    cases m with
    | zero =>
        exfalso
        have h0 : ([] : List Card).length = 0 := rfl
        have h52 := Board.nodup_cards_length_le hndA
        omega
    | succ k =>
        by_cases hcon : (u :: A).contains v = true
        · rw [Board.aboveOf_go_stop hv hcon]
          exact (List.contains_iff_mem).mp hcon
        · rw [Board.aboveOf_go_step hv hcon]
          exact Board.aboveOf_go_mem bd k (Sum.inr v) (v :: u :: A) v (by simp)

/-- The membership induction: a walk whose seat card is already
collected stays inside `aboveOf y` — each read is closed by
`aboveOf_succ_closed`, the accumulator rides the hypothesis. -/
theorem Board.aboveOf_go_of_mem {bd : Board} {y : Card} :
    ∀ (n : Nat) (u : Card) (acc : List Card) (w : Card),
      u ∈ bd.aboveOf y → (∀ c ∈ acc, c ∈ bd.aboveOf y) →
      w ∈ Board.aboveOf.go bd n (Sum.inr u) acc →
      w ∈ bd.aboveOf y := by
  intro n
  induction n with
  | zero => intro u acc w _ hacc hw; exact hacc w hw
  | succ k ih =>
      intro u acc w hu hacc hw
      cases ht : bd.topOf (Sum.inr u) with
      | none => rw [Board.aboveOf_go_topOf_none ht] at hw; exact hacc w hw
      | some c' =>
          have hc' : c' ∈ bd.aboveOf y := Board.aboveOf_succ_closed hu ht
          by_cases hcon : acc.contains c' = true
          · rw [Board.aboveOf_go_stop ht hcon] at hw; exact hacc w hw
          · rw [Board.aboveOf_go_step ht hcon] at hw
            exact ih c' (c' :: acc) w hc'
              (by intro c hc
                  rcases List.mem_cons.mp hc with heq | hc'
                  · rw [heq]; exact hc'
                  · exact hacc c hc') hw

/-- **Walk transitivity** — `aboveOf` is transitive on raw boards (no
WF needed): the matching's `inj` makes the up-chain unique, so the
walk from `x` is a tail of the walk from `y`; the guard-truncation is
symmetric around cycles. -/
theorem Board.aboveOf_trans {bd : Board} {x y : Card}
    (hxy : x ∈ bd.aboveOf y) {w : Card} (hw : w ∈ bd.aboveOf x) :
    w ∈ bd.aboveOf y :=
  Board.aboveOf_go_of_mem 52 x [] w hxy (by simp) hw

/-- A fitting cargo is off its host's twin pair (the fit forces the
rank gap — the cargos never confuse the license's seats). -/
theorem Card.ne_pair_of_canSitOn {z t : Card} (h : canSitOn z t = true) :
    z ≠ t ∧ z ≠ t.flipSuit := by
  simp only [canSitOn_eq] at h
  obtain ⟨hr, -⟩ := h
  constructor
  · intro hz; subst hz; omega
  · intro hz; subst hz; rw [Card.flipSuit_rank] at hr; omega

/-- **The both-occupied exchange license**: the shape premises of
TwinExchange's general row, bundled as one predicate — both twins
visible, both seats hosting a cargo, both fits, no braid.  `hwf` is
NOT part of the license: it rides as its own hypothesis (WF descends
through the exchange by `wf_exchangeTwinCargo` below), and the
quotient's classes live in the WF layer. -/
def State.twinLicensed (st : State) (t : Card) : Prop :=
  ∃ z z', st.isVis t = true ∧ st.isVis t.flipSuit = true ∧
    st.board.bottomOf z = some (Sum.inr t) ∧
    st.board.bottomOf z' = some (Sum.inr t.flipSuit) ∧
    canSitOn z t = true ∧ canSitOn z' t.flipSuit = true ∧
    (t ∉ st.board.aboveOf z ∧ t.flipSuit ∉ st.board.aboveOf z) ∧
    (t ∉ st.board.aboveOf z' ∧ t.flipSuit ∉ st.board.aboveOf z')

/-- **WF's `board_edges` descends through the exchange**.  Every edge
re-seats at its translated base with its clause intact: off-pair
bases transfer verbatim (the base is fixed, occupancy preserved,
deal-adjacency untouched); the two ROOT edges at the twin seats
re-derive through the fit disjunct — the base stays placed
(visibility) and the cargo still fits it (twin-blindness, the `hfit`
premises) — the corner's formal content: the deal-adjacency clause
cannot transfer across the swap, so without the fits the descent
dies. -/
theorem State.board_edges_exchangeTwinCargo {st : State} {t : Card}
    (hbe : st.board_edges)
    (hvis : st.isVis t = true) (hvis' : st.isVis t.flipSuit = true)
    (hfit : ∀ c, st.board.topOf (Sum.inr t) = some c → canSitOn c t.flipSuit = true)
    (hfit' : ∀ c, st.board.topOf (Sum.inr t.flipSuit) = some c → canSitOn c t = true) :
    (st.exchangeTwinCargo t).board_edges := by
  intro b c hb
  have hbt : st.board.topOf (b.swapTwin t) = some c := hb
  obtain ⟨-, hb2⟩ := hbe _ _ hbt
  refine ⟨(Board.bottomOf_eq _ _ _).mpr hb, ?_⟩
  cases b with
  | inl a => exact hb2
  | inr d =>
      by_cases hdt : t = d
      · -- E's seat `t` hosts the other cargo: the fit disjunct
        subst hdt
        refine Or.inr ⟨?_, ?_⟩
        · rw [State.bottomOf_isSome_exchangeTwinCargo]
          exact hvis
        · have hse : Base.swapTwin t (Sum.inr t) = Sum.inr t.flipSuit :=
            congrArg Sum.inr (Card.swapTwin_self_left t)
          exact hfit' c (by rw [← hse]; exact hbt)
      · by_cases hdt' : t.flipSuit = d
        · -- E's seat `t.flipSuit` hosts the other cargo: the fit disjunct
          subst hdt'
          refine Or.inr ⟨?_, ?_⟩
          · rw [State.bottomOf_isSome_exchangeTwinCargo]
            exact hvis'
          · have hse : Base.swapTwin t (Sum.inr t.flipSuit) = Sum.inr t :=
              congrArg Sum.inr (Card.swapTwin_self_right t)
            exact hfit c (by rw [← hse]; exact hbt)
        · -- off the pair: the clause transfers verbatim
          have hd : Card.swapTwin t d = d := Card.swapTwin_of_ne (Ne.symm hdt) (Ne.symm hdt')
          have hb2' : (∃ a l rest, st.deal.piles a
                = l ++ Card.swapTwin t d :: c :: rest ∧
                ((∃ a', st.topHidden a' = some (Card.swapTwin t d)) ∨
                  (st.board.bottomOf (Card.swapTwin t d)).isSome = true)) ∨
              ((st.board.bottomOf (Card.swapTwin t d)).isSome = true ∧
                canSitOn c (Card.swapTwin t d) = true) := hb2
          rw [hd] at hb2'
          rcases hb2' with ⟨a, l, rest, hslice, hside⟩ | ⟨his, hcs⟩
          · refine Or.inl ⟨a, l, rest, hslice, ?_⟩
            rcases hside with ⟨a', hth⟩ | hisb
            · exact Or.inl ⟨a', hth⟩
            · exact Or.inr (by
                rw [State.bottomOf_isSome_exchangeTwinCargo]
                exact hisb)
          · exact Or.inr ⟨by
              rw [State.bottomOf_isSome_exchangeTwinCargo]
              exact his, hcs⟩

/-- **WF descends through the exchange** (the licensed form): ten
conjuncts ride the board-only lift and pointwise visibility
invariance; `board_edges` is the descent above.  The fit premises
face the seats (`topOf`) — `wf_exchangeTwinCargo_of_twinLicensed`
recovers them from the license's cargos. -/
theorem State.wf_exchangeTwinCargo {st : State} {t : Card}
    (hwf : st.WF)
    (hvis : st.isVis t = true) (hvis' : st.isVis t.flipSuit = true)
    (hfit : ∀ c, st.board.topOf (Sum.inr t) = some c → canSitOn c t.flipSuit = true)
    (hfit' : ∀ c, st.board.topOf (Sum.inr t.flipSuit) = some c → canSitOn c t = true) :
    (st.exchangeTwinCargo t).WF := by
  refine State.WF.intro
    (deal_wf := hwf.deal_wf) (depths_le := fun a => hwf.depths_le a)
    (board_edges := State.board_edges_exchangeTwinCargo hwf.board_edges hvis hvis' hfit hfit')
    (vis_off_cycle := fun c h => hwf.vis_off_cycle c
      (by rw [State.isVis_exchangeTwin] at h; exact h))
    (found_off_cycle := fun c h => hwf.found_off_cycle c h)
    (founds_gone := fun c h => by
      rw [State.isVis_exchangeTwin]
      exact hwf.founds_gone c h)
    (vis_not_hidden := fun c h => hwf.vis_not_hidden c
      (by rw [State.isVis_exchangeTwin] at h; exact h))
    (heights_le := fun s => hwf.heights_le s)
    (cursor_le := hwf.cursor_le) (step_pos := hwf.step_pos)
    (stock_wf := hwf.stock_wf)

/-- The license gives the seats' fits: the row's cargo-facing premises
imply the seat-facing form `wf_exchangeTwinCargo` consumes (the
`bottomOf` roundtrip). -/
theorem State.wf_exchangeTwinCargo_of_twinLicensed {st : State} {t : Card}
    (hwf : st.WF) (h : st.twinLicensed t) :
    (st.exchangeTwinCargo t).WF := by
  obtain ⟨z, z', hvis, hvis', h₀, h₀', hfit, hfit', -⟩ := h
  have heq : ∀ x : Card, canSitOn x t = canSitOn x t.flipSuit := by
    intro x
    have h2 := canSitOn_swapTwin_right t x t.flipSuit
    rwa [Card.swapTwin_self_right] at h2
  refine State.wf_exchangeTwinCargo hwf hvis hvis' ?_ ?_
  · intro c hc
    have hz : st.board.topOf (Sum.inr t) = some z :=
      (Board.bottomOf_eq st.board z (Sum.inr t)).mp h₀
    rw [hz] at hc
    have hzc : z = c := Option.some.inj hc
    subst hzc
    rw [← heq z]
    exact hfit
  · intro c hc
    have hz' : st.board.topOf (Sum.inr t.flipSuit) = some z' :=
      (Board.bottomOf_eq st.board z' (Sum.inr t.flipSuit)).mp h₀'
    rw [hz'] at hc
    have hzc : z' = c := Option.some.inj hc
    subst hzc
    rw [heq z']
    exact hfit'

/-- **The license transfers through the exchange** — the row's iff
from one direction, via the involution: the cargos swap seats, the
fits ride twin-blindness, and the runs above the cargos never read
the exchanged seats (the no-braid premises, via
`Board.aboveOf_exchangeTwin`). -/
theorem State.twinLicensed_exchangeTwinCargo {st : State} {t : Card}
    (h : st.twinLicensed t) : (st.exchangeTwinCargo t).twinLicensed t := by
  obtain ⟨z, z', hvis, hvis', h₀, h₀', hfit, hfit', hnb, hnb'⟩ := h
  have heq : ∀ x : Card, canSitOn x t = canSitOn x t.flipSuit := by
    intro x
    have h2 := canSitOn_swapTwin_right t x t.flipSuit
    rwa [Card.swapTwin_self_right] at h2
  have hz : z ≠ t ∧ z ≠ t.flipSuit := Card.ne_pair_of_canSitOn hfit
  have hz' : z' ≠ t ∧ z' ≠ t.flipSuit := by
    obtain ⟨ha, hb⟩ := Card.ne_pair_of_canSitOn hfit'
    exact ⟨by intro h; exact hb (by rw [h, Card.flipSuit_flipSuit]), ha⟩
  refine ⟨z', z, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [State.isVis_exchangeTwin]; exact hvis
  · rw [State.isVis_exchangeTwin]; exact hvis'
  · rw [State.exchangeTwinCargo_board, Board.bottomOf_exchangeTwin, h₀']
    show some (Sum.inr (Card.swapTwin t t.flipSuit)) = some (Sum.inr t)
    rw [Card.swapTwin_self_right]
  · rw [State.exchangeTwinCargo_board, Board.bottomOf_exchangeTwin, h₀]
    show some (Sum.inr (Card.swapTwin t t)) = some (Sum.inr t.flipSuit)
    rw [Card.swapTwin_self_left]
  · rw [heq z']; exact hfit'
  · rw [← heq z]; exact hfit
  · constructor
    · intro hmem
      rw [State.exchangeTwinCargo_board,
        Board.aboveOf_exchangeTwin hz'.1 hz'.2 hnb'] at hmem
      exact hnb'.1 hmem
    · intro hmem
      rw [State.exchangeTwinCargo_board,
        Board.aboveOf_exchangeTwin hz'.1 hz'.2 hnb'] at hmem
      exact hnb'.2 hmem
  · constructor
    · intro hmem
      rw [State.exchangeTwinCargo_board,
        Board.aboveOf_exchangeTwin hz.1 hz.2 hnb] at hmem
      exact hnb.1 hmem
    · intro hmem
      rw [State.exchangeTwinCargo_board,
        Board.aboveOf_exchangeTwin hz.1 hz.2 hnb] at hmem
      exact hnb.2 hmem

/-- The license names the pair: it is symmetric in `t ↔ t.flipSuit`
(the flipped bundle the z'-side freedom case consumes, together with
`exchangeTwinCargo_pair`). -/
theorem State.twinLicensed_flipSuit {st : State} {t : Card}
    (h : st.twinLicensed t) : st.twinLicensed t.flipSuit := by
  obtain ⟨z, z', hvis, hvis', h₀, h₀', hfit, hfit', hnb, hnb'⟩ := h
  refine ⟨z', z, hvis', ?_, h₀', ?_, hfit', ?_, ⟨hnb'.2, ?_⟩, ⟨hnb.2, ?_⟩⟩
  · rw [Card.flipSuit_flipSuit]; exact hvis
  · rw [Card.flipSuit_flipSuit]; exact h₀
  · rw [Card.flipSuit_flipSuit]; exact hfit
  · rw [Card.flipSuit_flipSuit]; exact hnb'.1
  · rw [Card.flipSuit_flipSuit]; exact hnb.1

/-! ## Layers 3–4 — the g-simulation (the scaffold)

The assembly plan, as named targets.  Each case of the play induction
cites a proven mechanic (the six step lemmas of TwinExchange, the
`step_pileStack` below, the freedom-first bridge
`solvable_of_exchange_pileStack`) or one of the two TODOs: the merge
bridge (the [H] crux, gated by the witness hunt at
TwinExchange.lean:1247) and the forward simulation's premise
transfers.  The iff from one direction and the licensed form of the
row are PROVEN modulo the forward simulation — the involution plus
the Layer 1 license/WF transfers do the other direction.

Final wiring decision (recorded, not taken): TwinExchange's
`solvable_cargoTwin_exchange` (line 1267, sorried) closes over the
licensed form here once the import direction settles — re-home the
row to this file, or lift the Layer 0–1 stones into TwinExchange.
-/

/-- **The seventh clean-step mechanic**: `pileStack` of an off-pair,
off-cargo card mirrors — the guards (the card's own bareness, the
rung) are frame-inherited, and the detach rides the off-seat
congruence `exchangeTwin_detach_ne`.  The cargos' own `pileStack`s
are the freedom moves (the bridge, TwinExchange.lean:486); the twins
cannot stack pre-freedom (their seats host the cargos). -/
theorem State.exchangeTwinCargo_step_pileStack {st a₁ : State} {t z z' c : Card}
    (h₀ : st.board.bottomOf z = some (Sum.inr t))
    (h₀' : st.board.bottomOf z' = some (Sum.inr t.flipSuit))
    (hc : c ≠ z ∧ c ≠ z')
    (hct : c ≠ t ∧ c ≠ t.flipSuit)
    (hstep : st.apply (Move.pileStack c) = some a₁) :
    (st.exchangeTwinCargo t).apply (Move.pileStack c)
      = some (a₁.exchangeTwinCargo t) := by
  have hztop : st.board.topOf (Sum.inr t) = some z := (Board.bottomOf_eq _ _ _).mp h₀
  have hztop' : st.board.topOf (Sum.inr t.flipSuit) = some z' :=
    (Board.bottomOf_eq _ _ _).mp h₀'
  rw [apply_pileStack_iff] at hstep ⊢
  obtain ⟨htop, b₀, hb₀, hrk, hA₁⟩ := hstep
  have hb₀t : b₀ ≠ Sum.inr t := by
    intro h
    rw [h] at hb₀
    exact hc.1 (Option.some.inj (hztop.symm.trans
      ((Board.bottomOf_eq st.board c (Sum.inr t)).mp hb₀))).symm
  have hb₀t' : b₀ ≠ Sum.inr t.flipSuit := by
    intro h
    rw [h] at hb₀
    exact hc.2 (Option.some.inj (hztop'.symm.trans
      ((Board.bottomOf_eq st.board c (Sum.inr t.flipSuit)).mp hb₀))).symm
  refine ⟨?_, b₀, ?_, ?_, ?_⟩
  · rw [State.exchangeTwinCargo_board, Board.exchangeTwin_topOf,
      Base.swapTwin_eq_self (fun h => hct.1 (Sum.inr.inj h))
        (fun h => hct.2 (Sum.inr.inj h))]
    exact htop
  · rw [State.exchangeTwinCargo_board, Board.bottomOf_exchangeTwin, hb₀]
    show some (Base.swapTwin t b₀) = some b₀
    rw [Base.swapTwin_eq_self hb₀t hb₀t']
  · rw [State.exchangeTwinCargo_heights]
    exact hrk
  · rw [hA₁]
    apply state_ext
    · rfl
    · show (st.board.detach b₀).exchangeTwin t
        = (st.board.exchangeTwin t).detach b₀
      exact (Board.exchangeTwin_detach_ne st.board t hb₀t hb₀t').symm
    · rfl
    · rfl
    · rfl
    · rfl

/-- One step of the walk: the card directly on `t` is above `t`. -/
theorem Board.mem_aboveOf_of_topOf {bd : Board} {t z : Card}
    (h : bd.topOf (Sum.inr t) = some z) : z ∈ bd.aboveOf t := by
  rw [Board.aboveOf_eq_go 53 (by omega), Board.aboveOf_go_succ, h]
  show z ∈ (if ([] : List Card).contains z = true then ([] : List Card)
    else aboveOf.go bd 52 (Sum.inr z) [z])
  by_cases hcon : ([] : List Card).contains z = true
  · simp at hcon
  · rw [if_neg hcon]
    exact Board.aboveOf_go_mem bd 52 (Sum.inr z) [z] z (by simp)

/-- **The merge bridge — the [H] crux, now exactly the cargo-top
landing**: the pilePile-root freedom — a run whose walk reaches a
twin (carrying a cargo's stack off its seat), landing ON a cargo
stack — the one frozen-phase move whose same-move mirror is
self-landing in the exchanged state.  The off-cargo landings mirror
(`exchangeTwinCargo_step_pilePile_passing` — session-7's
correction); the own-cargo landings are self-landing at the SOURCE
(the guard plus walk transitivity: a card of the own cargo's run is
above the passing twin, hence above the run's root), so the hland
cases are exactly the other-cargo tops.

TODO(proof) **[H]** — the route (updated 2026-09-14, sessions 8-11):
the gate FIRED EMPTY; the cycle threat resolved (license rigidity); the
mirror's self-landing guard is LANDED (`exchangeTwin_mirror_guard`,
c-run form; `exchangeTwin_mirror_guard_zstack`, the z'-stack form —
the rider transfer's guard, dying by transitivity alone).  The
strategy, complete via the TWO-PLY TRANSFER: **(1)** the rider-prefix
(π's own moves, identical heights/bareness).  **(2a)** ROOT landing
(d = z'): the MIRROR merge `pilePile c (inr z)` — the c-run guard +
the twin-blind fit.  **(2b)** DEEP landing (d ∈ aboveOf z'): the RIDER
TRANSFER `pilePile r₁ (inr z)` (the z'-stack guard ✓ landed; the fit
twin-blind — NOTE the fit hole: a deal-adjacent first rider (not
fitting z') breaks the transfer — that sub-case needs either the
replay's normalization or a premise repair), then the ORIGINAL merge
`pilePile c (inr d)` (the original fit; the guard at stx₂ — a
non-exchange board — needs the walk-computation argument, not the
bound).  In both ply-completed cases the result is the TWIN-SWAP of
a₁-after-prefix.  **(3)** the climb-out = the twin-swap replay of
π-after-prefix: the clean moves conjugate (`apply_swapTwin_clean`),
the z/z' foundation moves are the exception set, and the
non-adjacent window is precisely L1/O3 — TwinAgnostic's open
interleaving lemma, now reached from a second direction.  The suit-level
relabel (`solvable_relabel`) does NOT shortcut it: the needed
correspondence is the two-card transposition τ_z, and ρ'∘τ_z (the
residual 12 black transpositions) meets the same window per pair.
**The L1/O3 decomposition (sessions 11-12)**: the window splits.
**(i) THE SEPARATED CASE is provable**: if π = prefix ++ [stack z] ++
mid ++ [stack z'] ++ suffix with the mid containing NO move whose
legality reads the twin suits' heights, the mirror replays
[prefix*, stack z', mid*, stack z, suffix*] — the rung-EXACTNESS of
`pileStack` (rank.toIdx = heights, exactly) does the heavy lifting:
during the source's mid (spade = 11, club = 10), the only stackable
twin-suit cards are ♠Q (rung 11) and the twin ♣J itself (rung 10 =
the second twin move); during the mirror's mid (spade = 10, club =
11), dually — so a twin-suit-free mid is exactly a mid whose red/
region moves replay verbatim (identical red heights, identical
bareness order on the swapped stack), and the twins stack at their
translated positions with their rungs already correct.  **(ii) THE
RESIDUE = the catch-up deferral**: the mid's possible twin-suit
activity (the exact-rung ♠Q/♣Q stackings and the spade/club
worry-backs) must be deferred to the suffix — a commutation whose
obstruction is the worry-backs' board interactions (a backed card
can host a later mid landing).  This is the precise remaining content
of the window; the separated case generalizes TwinAgnostic's paired
shape (a mid at all, vs. none).

**(i) is now LANDED** (below, after the walk-kit): the cross-skew
machinery — `State.twinHeightRel`/`apply_twinHeightRel` (ortho moves
fire identically under twin-height differences) +
`apply_ortho_preserves` (the twin heights are ortho-invariant),
`State.crossTwin`/`apply_crossTwin_ortho`/`run_crossTwin_ortho` (the
mid crosses wholesale, via `crossTwin = twinHeightSwap ∘ swapTwin`),
`apply_swapTwin_stack_flip` + `twinSkew_eq_crossTwin` (the first
stacking lands the cross-skew under the rung-alignment both firings
supply), `apply_crossTwin_stack` (the second re-syncs onto the plain
swapTwin correspondence), and the assembly
`solvable_swapTwin_separated` (+ `_back`).  The remaining bridge
content is exactly (ii).

**(2a) is LANDED too** (`State.exchange_merge_ply_root`): the
structural discovery behind it — the CARGOS ARE A TWIN PAIR
(`State.cargo_flipSuit`: the fits pin both to the twins' shared rank
and the shared other color, so `z' = z.flipSuit`) — makes the fit
twin-blind and identifies the ply's landing as the merge-successor's
board, twin-swapped AT THE CARGO z.  THE OPEN ITEM the climb-out now
faces: the full `swapTwin z` also relabels the deal piles and the
stock, while the ply keeps the source's deal — and board cards stay
listed in the deal piles (the reveal keeps `deal`), so the
state-level correspondence between the ply result and `a₁.swapTwin z`
needs a deal reconciliation (the climb-out's replay machinery must
either work board-only, or the deal difference must be bridged).  The
stock is z-free (`vis_off_cycle` at seated z/z'); only the deal
piles carry the difference. -/
theorem State.solvable_of_exchange_merge {st a₁ : State} {t z z' c : Card} {b : Base}
    (hwf : st.WF) (h : st.twinLicensed t)
    (hstep : st.apply (Move.pilePile c b) = some a₁)
    (hmerge : t ∈ st.board.aboveOf c ∨ t.flipSuit ∈ st.board.aboveOf c)
    (hland : ∃ d, b = Sum.inr d ∧
      (d = z ∨ d ∈ st.board.aboveOf z ∨ d = z' ∨ d ∈ st.board.aboveOf z'))
    (hsol : a₁.solvableFrom) :
    (st.exchangeTwinCargo t).solvableFrom := sorry

/-! ### The forward simulation's substrate (the [M] assembly)

The per-kind license transfers and the twin-rooted `pilePile` mirror,
plus the two walk laws the assembly needs beyond TwinExchange's kit:
the seed containment (`Board.aboveOf_sub_of_seated` — the cargo's run
rides inside its host's, the fact that turns the twin-rooted
self-landing guard into a cargo-run exclusion) and the phantom-stack
killer (`State.topOf_inr_eq_none` — session-6's finding: at WF, an
unplaced card in no hidden slice carries no stack, so the attach-move
run growth is bounded by the moved card alone).  The one genuine
residual is the twin-rooted merge (`solvable_of_exchange_merge_rooted`)
— the [H] shape with the run rooted AT the twin instead of reaching
one. -/

/-- The head of a list is a member (`hiddenBase`'s membership half
needs it). -/
theorem mem_of_head? {l : List Card} {c : Card} (h : l.head? = some c) : c ∈ l := by
  cases l with
  | nil => exact absurd h (by simp)
  | cons a t =>
      rw [show (a :: t).head? = some a from rfl] at h
      exact List.mem_cons.mpr (Or.inl (Option.some.inj h.symm))

/-- The boundary card is hidden in its pile (`pileOfTopHidden`'s
membership half, via `findFirst_mem` + `mem_of_getLast`). -/
theorem State.mem_hidden_of_pileOfTopHidden {st : State} {r : Card} {a : Anchor}
    (h : st.pileOfTopHidden r = some a) : r ∈ st.hidden a := by
  obtain ⟨-, hth⟩ := findFirst_mem (fun a' => decide (st.topHidden a' = some r)) Anchor.all a h
  exact mem_of_getLast (of_decide_eq_true hth)

/-- The card under the boundary is hidden too (`hiddenBase`'s
membership half). -/
theorem State.mem_hidden_of_hiddenBase {st : State} {a : Anchor} {d : Card}
    (h : st.hiddenBase a = Sum.inr d) : d ∈ st.hidden a := by
  unfold State.hiddenBase at h
  cases hr : ((st.hidden a).reverse.drop 1).head? with
  | none => rw [hr] at h; exact absurd h (by simp)
  | some d' =>
      rw [hr] at h
      have hdd : d' = d := Sum.inr.inj h
      rw [← hdd]
      exact List.mem_reverse.mp (List.drop_subset 1 _ (mem_of_head? hr))

/-- **The phantom-stack killer** (session-6's finding, formal): at a
WF state, an unplaced card that lies in no hidden slice carries no
stack — `board_edges`' base-side condition (State.lean:130-131)
demands the base be the hidden boundary or itself seated, and both
die.  The deckPile/stackPile no-braid transfers ride this: the
attach-growth (`Board.mem_aboveOf_attach`) is then bounded by the
moved card, which is not a twin. -/
theorem State.topOf_inr_eq_none {st : State} {c : Card} (hwf : st.WF)
    (hbot : st.board.bottomOf c = none) (hhid : ∀ a, c ∉ st.hidden a) :
    st.board.topOf (Sum.inr c) = none := by
  cases ht : st.board.topOf (Sum.inr c) with
  | none => rfl
  | some x =>
      obtain ⟨-, hd⟩ := hwf.board_edges (Sum.inr c) x ht
      rcases hd with ⟨a, l, rest, -, hside⟩ | ⟨his, -⟩
      · rcases hside with ⟨a', hth⟩ | hisb
        · exact absurd (mem_of_getLast hth) (hhid a')
        · rw [hbot] at hisb; simp at hisb
      · rw [hbot] at his; simp at his

/-- Walk cards are seated: every card a run collects sits on some
base (the walk only collects what a `topOf` read returns).  The reveal
transfer consumes this — the hidden attach base cannot be on a
(visible) run. -/
theorem Board.seated_of_mem_aboveOf_go (bd : Board) :
    ∀ (n : Nat) (x : Card) (acc : List Card) (y : Card),
      y ∈ Board.aboveOf.go bd n (Sum.inr x) acc → y ∈ acc ∨ bd.bottomOf y ≠ none := by
  intro n
  induction n with
  | zero => intro x acc y hy; exact Or.inl hy
  | succ n ih =>
      intro x acc y hy
      cases ht : bd.topOf (Sum.inr x) with
      | none => rw [Board.aboveOf_go_topOf_none ht] at hy; exact Or.inl hy
      | some c' =>
          by_cases hcon : acc.contains c' = true
          · rw [Board.aboveOf_go_stop ht hcon] at hy; exact Or.inl hy
          · rw [Board.aboveOf_go_step ht hcon] at hy
            rcases ih c' (c' :: acc) y hy with h | h
            · rcases List.mem_cons.mp h with heq | h'
              · rw [heq]
                exact Or.inr (by
                  rw [(Board.bottomOf_eq bd c' (Sum.inr x)).mpr ht]
                  simp)
              · exact Or.inl h'
            · exact Or.inr h

theorem Board.seated_of_mem_aboveOf {bd : Board} {c y : Card}
    (hy : y ∈ bd.aboveOf c) : bd.bottomOf y ≠ none := by
  rcases Board.seated_of_mem_aboveOf_go bd 52 c [] y
    (by rw [Board.aboveOf_eq] at hy; exact hy) with h | h
  · exact absurd h (by simp)
  · exact h

/-- The walk from the seed's own seat stops immediately: with `z`
already collected and `z`'s own cover collected (the walk's first
collect), the next read re-reads a member and the guard fires. -/
theorem Board.aboveOf_go_stop_at_seed (bd : Board) (z : Card) :
    ∀ (n : Nat) (A : List Card), (∀ c, bd.topOf (Sum.inr z) = some c → c ∈ A ∨ c = z) →
      Board.aboveOf.go bd n (Sum.inr z) (z :: A) = z :: A := by
  intro n
  induction n with
  | zero => intro A _; rfl
  | succ n _ =>
      intro A hI3
      cases ht : bd.topOf (Sum.inr z) with
      | none => rw [Board.aboveOf_go_topOf_none ht]
      | some c₁ =>
          have hc : (z :: A).contains c₁ = true :=
            (List.contains_iff_mem).mpr (List.mem_cons.mpr ((hI3 c₁ ht).symm))
          rw [Board.aboveOf_go_stop ht hc]

/-- Seed monotonicity: with the same start and fuel, the unseeded
walk's members are all members of the `z`-seeded walk's.  The two
walks read the same cells and collect the same cards; the seeded
walk's guard can only fire earlier — at `z` — and there the unseeded
walk collects `z` and stops at the very next read
(`aboveOf_go_stop_at_seed`, via the invariant that `z`'s cover is
always already collected). -/
theorem Board.aboveOf_go_seed_mono (bd : Board) (z : Card) :
    ∀ (n : Nat) (b : Base) (A B : List Card) (y : Card),
      (∀ x ∈ A, x ∈ B) → (∀ x ∈ B, x ∈ A ∨ x = z) →
      (∀ c, bd.topOf (Sum.inr z) = some c → c ∈ A) →
      y ∈ Board.aboveOf.go bd n b A → y ∈ Board.aboveOf.go bd n b B := by
  intro n
  induction n with
  | zero =>
      intro b A B y hAB _ _ hy
      exact hAB _ hy
  | succ n ih =>
      intro b A B y hAB hBA hI3 hy
      cases ht : bd.topOf b with
      | none =>
          rw [Board.aboveOf_go_topOf_none ht] at hy ⊢
          exact hAB _ hy
      | some c =>
          by_cases hcA : A.contains c = true
          · rw [Board.aboveOf_go_stop ht hcA] at hy
            have hcB : B.contains c = true :=
              (List.contains_iff_mem).mpr (hAB c ((List.contains_iff_mem).mp hcA))
            rw [Board.aboveOf_go_stop ht hcB]
            exact hAB _ hy
          · rw [Board.aboveOf_go_step ht hcA] at hy
            by_cases hcB : B.contains c = true
            · have hcz : c = z := by
                rcases hBA c ((List.contains_iff_mem).mp hcB) with h | h
                · exact absurd ((List.contains_iff_mem).mpr h) hcA
                · exact h
              rw [Board.aboveOf_go_stop ht hcB]
              rw [hcz] at hy
              rw [Board.aboveOf_go_stop_at_seed bd z n A (fun c hc => Or.inl (hI3 c hc))] at hy
              rcases List.mem_cons.mp hy with heq | hy'
              · rw [heq]
                have hzB : z ∈ B := by
                  have hzc : z = c := hcz.symm
                  rw [hzc]
                  exact (List.contains_iff_mem).mp hcB
                exact hzB
              · exact hAB _ hy'
            · rw [Board.aboveOf_go_step ht hcB]
              refine ih (Sum.inr c) (c :: A) (c :: B) y ?_ ?_ ?_ hy
              · intro x hx
                rcases List.mem_cons.mp hx with heq | hx'
                · rw [heq]; exact List.mem_cons_self
                · exact List.mem_cons_of_mem _ (hAB x hx')
              · intro x hx
                rcases List.mem_cons.mp hx with heq | hx'
                · rw [heq]; exact Or.inl List.mem_cons_self
                · rcases hBA x hx' with h | h
                  · exact Or.inl (List.mem_cons_of_mem _ h)
                  · exact Or.inr h
              · intro c' hc'
                exact List.mem_cons_of_mem _ (hI3 c' hc')

/-- **The run rides inside the host's run** (seed containment, the
hard direction): everything above the cargo `z` is above its host
`t`.  The `z`-seeded walk from `z` IS the `t`-walk one step in (with
the fuel counted from 53 so both walks carry 52), and the unseeded
walk collecting `z` re-reads its own first collect at the next step
and stops.  The twin-rooted `pilePile` case consumes this: the source
self-landing guard `d ∉ aboveOf t` excludes the landing from the
cargo's run too. -/
theorem Board.aboveOf_sub_of_seated {bd : Board} {t z : Card}
    (h : bd.topOf (Sum.inr t) = some z) {y : Card} (hy : y ∈ bd.aboveOf z) :
    y ∈ bd.aboveOf t := by
  have hT : bd.aboveOf t = Board.aboveOf.go bd 52 (Sum.inr z) [z] := by
    have h53 : bd.aboveOf t = Board.aboveOf.go bd 53 (Sum.inr t) [] :=
      Board.aboveOf_eq_go 53 (by omega)
    rw [h53]
    show Board.aboveOf.go bd (52 + 1) (Sum.inr t) [] = _
    rw [Board.aboveOf_go_step h (by simp)]
  rw [hT]
  rw [Board.aboveOf_eq] at hy
  have hy' : y ∈ Board.aboveOf.go bd (51 + 1) (Sum.inr z) [] := hy
  show y ∈ Board.aboveOf.go bd (51 + 1) (Sum.inr z) [z]
  cases ht : bd.topOf (Sum.inr z) with
  | none =>
      rw [Board.aboveOf_go_topOf_none ht] at hy'
      exact absurd hy' (by simp)
  | some c₁ =>
      rw [Board.aboveOf_go_step ht (by simp)] at hy'
      by_cases hc₁z : c₁ = z
      · rw [hc₁z] at hy'
        rw [Board.aboveOf_go_stop ht (by rw [hc₁z]; simp)]
        have hI3 : ∀ c, bd.topOf (Sum.inr z) = some c → c ∈ ([] : List Card) ∨ c = z := by
          intro c hc
          refine Or.inr ?_
          have hcc : c = c₁ := Option.some.inj (hc.symm.trans ht)
          rw [hcc, hc₁z]
        rw [Board.aboveOf_go_stop_at_seed bd z 51 [] hI3] at hy'
        exact hy'
      · rw [Board.aboveOf_go_step ht
          (fun hcon => hc₁z (List.mem_singleton.mp ((List.contains_iff_mem).mp hcon)))]
        refine Board.aboveOf_go_seed_mono bd z 51 (Sum.inr c₁) [c₁] [c₁, z] y ?_ ?_ ?_ hy'
        · intro x hx
          rcases List.mem_cons.mp hx with heq | hx'
          · rw [heq]; exact List.mem_cons_self
          · exact absurd hx' (by simp)
        · intro x hx
          rcases List.mem_cons.mp hx with heq | hx'
          · rw [heq]; exact Or.inl List.mem_cons_self
          · exact Or.inr (List.mem_singleton.mp hx')
        · intro c hc
          have hcc : c = c₁ := Option.some.inj (hc.symm.trans ht)
          rw [hcc]; exact List.mem_cons_self

/-- The license is board-only: it transfers verbatim across a
board-preserving successor (`draw`, `deckStack`). -/
theorem State.twinLicensed_congr {st a₁ : State} {t : Card}
    (hb : a₁.board = st.board) (h : st.twinLicensed t) : a₁.twinLicensed t := by
  obtain ⟨z, z', hvis, hvis', h₀, h₀', hfit, hfit', hnb, hnb'⟩ := h
  refine ⟨z, z', ?_, ?_, ?_, ?_, hfit, hfit', ?_, ?_⟩
  · show (a₁.board.bottomOf t).isSome = true
    rw [hb]; exact hvis
  · show (a₁.board.bottomOf t.flipSuit).isSome = true
    rw [hb]; exact hvis'
  · show a₁.board.bottomOf z = some (Sum.inr t)
    rw [hb]; exact h₀
  · show a₁.board.bottomOf z' = some (Sum.inr t.flipSuit)
    rw [hb]; exact h₀'
  · show t ∉ a₁.board.aboveOf z ∧ t.flipSuit ∉ a₁.board.aboveOf z
    rw [hb]; exact hnb
  · show t ∉ a₁.board.aboveOf z' ∧ t.flipSuit ∉ a₁.board.aboveOf z'
    rw [hb]; exact hnb'

/-- The non-freedom `pileStack` license transfer: the detach at the
moved card's own base is off the twin seats (the seats host the
cargos), the twins keep their bases (`bottomOf_detach_ne`), and the
no-braid walks only shrink (`Board.aboveOf_sub_detach`). -/
theorem State.twinLicensed_apply_pileStack {st a₁ : State} {t z z' c : Card}
    (hvis : st.isVis t = true) (hvis' : st.isVis t.flipSuit = true)
    (h₀ : st.board.bottomOf z = some (Sum.inr t))
    (h₀' : st.board.bottomOf z' = some (Sum.inr t.flipSuit))
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.flipSuit = true)
    (hnb : t ∉ st.board.aboveOf z ∧ t.flipSuit ∉ st.board.aboveOf z)
    (hnb' : t ∉ st.board.aboveOf z' ∧ t.flipSuit ∉ st.board.aboveOf z')
    (hct : c ≠ t ∧ c ≠ t.flipSuit) (hc : c ≠ z ∧ c ≠ z')
    (hstep : st.apply (Move.pileStack c) = some a₁) : a₁.twinLicensed t := by
  have hztop : st.board.topOf (Sum.inr t) = some z := (Board.bottomOf_eq _ _ _).mp h₀
  have hztop' : st.board.topOf (Sum.inr t.flipSuit) = some z' :=
    (Board.bottomOf_eq _ _ _).mp h₀'
  rw [apply_pileStack_iff] at hstep
  obtain ⟨htop, b, hb, hrk, rfl⟩ := hstep
  have hbt : b ≠ Sum.inr t := by
    intro hcon
    rw [hcon] at hb
    exact hc.1 (Option.some.inj (hztop.symm.trans
      ((Board.bottomOf_eq st.board c (Sum.inr t)).mp hb))).symm
  have hbt' : b ≠ Sum.inr t.flipSuit := by
    intro hcon
    rw [hcon] at hb
    exact hc.2 (Option.some.inj (hztop'.symm.trans
      ((Board.bottomOf_eq st.board c (Sum.inr t.flipSuit)).mp hb))).symm
  refine ⟨z, z', ?_, ?_, ?_, ?_, hfit, hfit', ?_, ?_⟩
  · show ((st.board.detach b).bottomOf t).isSome = true
    rw [bottomOf_detach_ne ((Board.bottomOf_eq st.board c b).mp hb)
      (fun h => hct.1 h.symm)]
    exact hvis
  · show ((st.board.detach b).bottomOf t.flipSuit).isSome = true
    rw [bottomOf_detach_ne ((Board.bottomOf_eq st.board c b).mp hb)
      (fun h => hct.2 h.symm)]
    exact hvis'
  · show (st.board.detach b).bottomOf z = some (Sum.inr t)
    exact (Board.bottomOf_eq _ _ _).mpr (by
      rw [Board.detach_topOf_ne _ _ _ (fun hcon => hbt hcon.symm)]
      exact hztop)
  · show (st.board.detach b).bottomOf z' = some (Sum.inr t.flipSuit)
    exact (Board.bottomOf_eq _ _ _).mpr (by
      rw [Board.detach_topOf_ne _ _ _ (fun hcon => hbt' hcon.symm)]
      exact hztop')
  · show t ∉ (st.board.detach b).aboveOf z ∧ t.flipSuit ∉ (st.board.detach b).aboveOf z
    constructor
    · intro hmem
      exact hnb.1 (Board.aboveOf_sub_detach 52 z [] t hmem)
    · intro hmem
      exact hnb.2 (Board.aboveOf_sub_detach 52 z [] t.flipSuit hmem)
  · show t ∉ (st.board.detach b).aboveOf z' ∧ t.flipSuit ∉ (st.board.detach b).aboveOf z'
    constructor
    · intro hmem
      exact hnb'.1 (Board.aboveOf_sub_detach 52 z' [] t hmem)
    · intro hmem
      exact hnb'.2 (Board.aboveOf_sub_detach 52 z' [] t.flipSuit hmem)

/-- The single-attach license transfer (`deckPile`/`stackPile`): the
cargos stay seated (the landing is off the twin seats, the moved card
is not a twin — it is invisible, the twins are visible), and the
no-braid premises survive because the moved card carries no stack at
WF (`State.topOf_inr_eq_none` — the growth `Board.mem_aboveOf_attach`
is then bounded by the twin-free moved card). -/
theorem State.twinLicensed_attach {st : State} {t c : Card} {b : Base} {bd : Board}
    (hwf : st.WF) (h : st.twinLicensed t)
    (hatt : st.board.attach b c = some bd)
    (hct : c ≠ t ∧ c ≠ t.flipSuit)
    (hbot : st.board.bottomOf c = none) (hhid : ∀ a, c ∉ st.hidden a)
    (hbt : b ≠ Sum.inr t ∧ b ≠ Sum.inr t.flipSuit) :
    {st with board := bd}.twinLicensed t := by
  obtain ⟨z, z', hvis, hvis', h₀, h₀', hfit, hfit', hnb, hnb'⟩ := h
  have hztop : st.board.topOf (Sum.inr t) = some z := (Board.bottomOf_eq _ _ _).mp h₀
  have hztop' : st.board.topOf (Sum.inr t.flipSuit) = some z' :=
    (Board.bottomOf_eq _ _ _).mp h₀'
  have hbare : st.board.topOf (Sum.inr c) = none := State.topOf_inr_eq_none hwf hbot hhid
  have habovec : st.board.aboveOf c = [] := Board.aboveOf_step_none hbare
  refine ⟨z, z', ?_, ?_, ?_, ?_, hfit, hfit', ?_, ?_⟩
  · show (bd.bottomOf t).isSome = true
    exact bottomOf_isSome_attach hatt hvis
  · show (bd.bottomOf t.flipSuit).isSome = true
    exact bottomOf_isSome_attach hatt hvis'
  · show bd.bottomOf z = some (Sum.inr t)
    exact (Board.bottomOf_eq _ _ _).mpr (by
      rw [Board.attach_topOf_ne _ _ _ hatt (fun hcon => hbt.1 hcon.symm)]
      exact hztop)
  · show bd.bottomOf z' = some (Sum.inr t.flipSuit)
    exact (Board.bottomOf_eq _ _ _).mpr (by
      rw [Board.attach_topOf_ne _ _ _ hatt (fun hcon => hbt.2 hcon.symm)]
      exact hztop')
  · constructor
    · intro hmem
      rcases Board.mem_aboveOf_attach hatt hmem with hmem' | hmem' | hmem'
      · exact hnb.1 hmem'
      · exact hct.1 hmem'.symm
      · rw [habovec] at hmem'; exact absurd hmem' (by simp)
    · intro hmem
      rcases Board.mem_aboveOf_attach hatt hmem with hmem' | hmem' | hmem'
      · exact hnb.2 hmem'
      · exact hct.2 hmem'.symm
      · rw [habovec] at hmem'; exact absurd hmem' (by simp)
  · constructor
    · intro hmem
      rcases Board.mem_aboveOf_attach hatt hmem with hmem' | hmem' | hmem'
      · exact hnb'.1 hmem'
      · exact hct.1 hmem'.symm
      · rw [habovec] at hmem'; exact absurd hmem' (by simp)
    · intro hmem
      rcases Board.mem_aboveOf_attach hatt hmem with hmem' | hmem' | hmem'
      · exact hnb'.2 hmem'
      · exact hct.2 hmem'.symm
      · rw [habovec] at hmem'; exact absurd hmem' (by simp)

/-- The `reveal` license transfer: the moved card is the hidden
boundary (the twins are visible — `vis_not_hidden` keeps them apart),
the attach base is the next hidden card down (or the anchor) — off the
twin seats (occupied) — and the no-braid walks are literally
unchanged: every card the walks read is seated, the attach base is
hidden, and `vis_not_hidden` keeps them apart (`Board.aboveOf_congr`). -/
theorem State.twinLicensed_apply_reveal {st a₁ : State} {t c : Card}
    (hwf : st.WF) (h : st.twinLicensed t)
    (hstep : st.apply (Move.reveal c) = some a₁) : a₁.twinLicensed t := by
  obtain ⟨z, z', hvis, hvis', h₀, h₀', hfit, hfit', hnb, hnb'⟩ := h
  have hztop : st.board.topOf (Sum.inr t) = some z := (Board.bottomOf_eq _ _ _).mp h₀
  have hztop' : st.board.topOf (Sum.inr t.flipSuit) = some z' :=
    (Board.bottomOf_eq _ _ _).mp h₀'
  rw [apply_reveal_iff] at hstep
  obtain ⟨htop, r, a, bd, hbot, hpile, hatt, rfl⟩ := hstep
  have hrmem : r ∈ st.hidden a := State.mem_hidden_of_pileOfTopHidden hpile
  have hrt : r ≠ t ∧ r ≠ t.flipSuit := by
    constructor
    · intro hcon; rw [hcon] at hrmem; exact hwf.vis_not_hidden t hvis a hrmem
    · intro hcon; rw [hcon] at hrmem; exact hwf.vis_not_hidden t.flipSuit hvis' a hrmem
  obtain ⟨hgb, -⟩ := (Board.attach_eq_some_iff _ _ _).mp (by rw [hatt]; simp)
  have hgbt : st.hiddenBase a ≠ Sum.inr t := by
    intro hcon
    rw [hcon] at hgb
    rw [hztop] at hgb
    simp at hgb
  have hgbt' : st.hiddenBase a ≠ Sum.inr t.flipSuit := by
    intro hcon
    rw [hcon] at hgb
    rw [hztop'] at hgb
    simp at hgb
  -- the no-braid walks: the only changed cell (the hidden base) is not
  -- on any (seated) run
  have hagree : ∀ (w : Card), w = z ∨ w = z' → ∀ x ∈ w :: st.board.aboveOf w,
      st.board.topOf (Sum.inr x) = bd.topOf (Sum.inr x) := by
    intro w hw x hx
    by_cases hcell : Sum.inr x = st.hiddenBase a
    · exfalso
      obtain ⟨d, hd⟩ : ∃ d, st.hiddenBase a = Sum.inr d := by
        cases hbb : st.hiddenBase a with
        | inl a' => exact absurd hcell (by rw [hbb]; simp)
        | inr d => exact ⟨d, rfl⟩
      have hdmem : d ∈ st.hidden a := State.mem_hidden_of_hiddenBase hd
      have hxd : x = d := Sum.inr.inj (hcell.trans hd)
      have hxvis : st.isVis x = true := by
        rcases List.mem_cons.mp hx with heq | hx'
        · rw [heq]
          rcases hw with heq2 | heq2
          · rw [heq2]
            exact (by
              show (st.board.bottomOf z).isSome = true
              rw [h₀]; rfl)
          · rw [heq2]
            exact (by
              show (st.board.bottomOf z').isSome = true
              rw [h₀']; rfl)
        · show (st.board.bottomOf x).isSome = true
          cases hbx : st.board.bottomOf x with
          | none => exact absurd hbx (Board.seated_of_mem_aboveOf hx')
          | some β => rfl
      rw [hxd] at hxvis
      exact hwf.vis_not_hidden d hxvis a hdmem
    · rw [Board.attach_topOf_ne _ _ _ hatt (fun hcon => hcell hcon)]
  refine ⟨z, z', ?_, ?_, ?_, ?_, hfit, hfit', ?_, ?_⟩
  · show (bd.bottomOf t).isSome = true
    exact bottomOf_isSome_attach hatt hvis
  · show (bd.bottomOf t.flipSuit).isSome = true
    exact bottomOf_isSome_attach hatt hvis'
  · show bd.bottomOf z = some (Sum.inr t)
    exact (Board.bottomOf_eq _ _ _).mpr (by
      rw [Board.attach_topOf_ne _ _ _ hatt (fun hcon => hgbt hcon.symm)]
      exact hztop)
  · show bd.bottomOf z' = some (Sum.inr t.flipSuit)
    exact (Board.bottomOf_eq _ _ _).mpr (by
      rw [Board.attach_topOf_ne _ _ _ hatt (fun hcon => hgbt' hcon.symm)]
      exact hztop')
  · show t ∉ bd.aboveOf z ∧ t.flipSuit ∉ bd.aboveOf z
    rw [Board.aboveOf_congr (hagree z (Or.inl rfl))]
    exact hnb
  · show t ∉ bd.aboveOf z' ∧ t.flipSuit ∉ bd.aboveOf z'
    rw [Board.aboveOf_congr (hagree z' (Or.inr rfl))]
    exact hnb'

/-- The clean-run `pilePile` license transfer: the moved root is off
the pair and the cargos, and the run carries no twin (`hclean`) —
the seats survive (the detach and attach bases are off them), and the
no-braid premises ride the detach-shrink (`Board.aboveOf_sub_detach`)
plus the attach-growth bound (`Board.mem_aboveOf_attach`: the growth
is the moved card and its run — both twin-free). -/
theorem State.twinLicensed_apply_pilePile {st a₁ : State} {t z z' c : Card} {b : Base}
    (hvis : st.isVis t = true) (hvis' : st.isVis t.flipSuit = true)
    (h₀ : st.board.bottomOf z = some (Sum.inr t))
    (h₀' : st.board.bottomOf z' = some (Sum.inr t.flipSuit))
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.flipSuit = true)
    (hnb : t ∉ st.board.aboveOf z ∧ t.flipSuit ∉ st.board.aboveOf z)
    (hnb' : t ∉ st.board.aboveOf z' ∧ t.flipSuit ∉ st.board.aboveOf z')
    (hct : c ≠ t ∧ c ≠ t.flipSuit) (hc : c ≠ z ∧ c ≠ z')
    (hclean : t ∉ st.board.aboveOf c ∧ t.flipSuit ∉ st.board.aboveOf c)
    (hstep : st.apply (Move.pilePile c b) = some a₁) : a₁.twinLicensed t := by
  have hztop : st.board.topOf (Sum.inr t) = some z := (Board.bottomOf_eq _ _ _).mp h₀
  have hztop' : st.board.topOf (Sum.inr t.flipSuit) = some z' :=
    (Board.bottomOf_eq _ _ _).mp h₀'
  rw [apply_pilePile_iff] at hstep
  obtain ⟨b₀, hbot, hne, hcmr, bd, hatt, rfl⟩ := hstep
  simp only [State.canMoveRun, Bool.and_eq_true_iff] at hcmr
  obtain ⟨hcp, -⟩ := hcmr
  have hb₀t : b₀ ≠ Sum.inr t := by
    intro hcon
    rw [hcon] at hbot
    exact hc.1 (Option.some.inj (hztop.symm.trans
      ((Board.bottomOf_eq st.board c (Sum.inr t)).mp hbot))).symm
  have hb₀t' : b₀ ≠ Sum.inr t.flipSuit := by
    intro hcon
    rw [hcon] at hbot
    exact hc.2 (Option.some.inj (hztop'.symm.trans
      ((Board.bottomOf_eq st.board c (Sum.inr t.flipSuit)).mp hbot))).symm
  have hbt : b ≠ Sum.inr t ∧ b ≠ Sum.inr t.flipSuit := by
    constructor
    · intro hcon
      cases b with
      | inl a => exact absurd hcon (by simp)
      | inr d =>
          obtain ⟨htopb, -, -⟩ := canPlace_inr_iff.mp hcp
          rw [hcon, hztop] at htopb
          simp at htopb
    · intro hcon
      cases b with
      | inl a => exact absurd hcon (by simp)
      | inr d =>
          obtain ⟨htopb, -, -⟩ := canPlace_inr_iff.mp hcp
          rw [hcon, hztop'] at htopb
          simp at htopb
  have hzbot : st.board.topOf b₀ = some c := (Board.bottomOf_eq st.board c b₀).mp hbot
  refine ⟨z, z', ?_, ?_, ?_, ?_, hfit, hfit', ?_, ?_⟩
  · show (bd.bottomOf t).isSome = true
    refine bottomOf_isSome_attach hatt ?_
    show ((st.board.detach b₀).bottomOf t).isSome = true
    rw [bottomOf_detach_ne hzbot (fun h => hct.1 h.symm)]
    exact hvis
  · show (bd.bottomOf t.flipSuit).isSome = true
    refine bottomOf_isSome_attach hatt ?_
    show ((st.board.detach b₀).bottomOf t.flipSuit).isSome = true
    rw [bottomOf_detach_ne hzbot (fun h => hct.2 h.symm)]
    exact hvis'
  · show bd.bottomOf z = some (Sum.inr t)
    exact (Board.bottomOf_eq _ _ _).mpr (by
      rw [Board.attach_topOf_ne _ _ _ hatt (fun hcon => hbt.1 hcon.symm),
        Board.detach_topOf_ne _ _ _ (fun hcon => hb₀t hcon.symm)]
      exact hztop)
  · show bd.bottomOf z' = some (Sum.inr t.flipSuit)
    exact (Board.bottomOf_eq _ _ _).mpr (by
      rw [Board.attach_topOf_ne _ _ _ hatt (fun hcon => hbt.2 hcon.symm),
        Board.detach_topOf_ne _ _ _ (fun hcon => hb₀t' hcon.symm)]
      exact hztop')
  · constructor
    · intro hmem
      rcases Board.mem_aboveOf_attach hatt hmem with hmem' | hmem' | hmem'
      · exact hnb.1 (Board.aboveOf_sub_detach 52 z [] t hmem')
      · exact hct.1 hmem'.symm
      · exact hclean.1 (Board.aboveOf_sub_detach 52 c [] t hmem')
    · intro hmem
      rcases Board.mem_aboveOf_attach hatt hmem with hmem' | hmem' | hmem'
      · exact hnb.2 (Board.aboveOf_sub_detach 52 z [] t.flipSuit hmem')
      · exact hct.2 hmem'.symm
      · exact hclean.2 (Board.aboveOf_sub_detach 52 c [] t.flipSuit hmem')
  · constructor
    · intro hmem
      rcases Board.mem_aboveOf_attach hatt hmem with hmem' | hmem' | hmem'
      · exact hnb'.1 (Board.aboveOf_sub_detach 52 z' [] t hmem')
      · exact hct.1 hmem'.symm
      · exact hclean.1 (Board.aboveOf_sub_detach 52 c [] t hmem')
    · intro hmem
      rcases Board.mem_aboveOf_attach hatt hmem with hmem' | hmem' | hmem'
      · exact hnb'.2 (Board.aboveOf_sub_detach 52 z' [] t.flipSuit hmem')
      · exact hct.2 hmem'.symm
      · exact hclean.2 (Board.aboveOf_sub_detach 52 c [] t.flipSuit hmem')

/-- **The twin-rooted `pilePile` mirror step**: relocating the twin's
own run (the cargo riding on top of it) mirrors across the exchange —
the detach/attach congruences fire at the off-pair bases (the moved
card is irrelevant to them), `canPlace` transfers off the pair, and
the self-landing guard is handed over as `hself` (the exchanged walk
from `t` is the other twin's — bounded by the two cargo runs via
`Board.aboveOf_exchangeTwin_bound`).  The anchor arm needs no guard;
the tableau arm's guard is the caller's. -/
theorem State.exchangeTwinCargo_step_pilePile_root {st a₁ : State} {t z z' c : Card}
    {b : Base}
    (h₀ : st.board.bottomOf z = some (Sum.inr t))
    (h₀' : st.board.bottomOf z' = some (Sum.inr t.flipSuit))
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.flipSuit = true)
    (hstep : st.apply (Move.pilePile c b) = some a₁) (hc : c = t)
    (hself : ∀ d, b = Sum.inr d → d ∉ (st.board.exchangeTwin t).aboveOf c) :
    (st.exchangeTwinCargo t).apply (Move.pilePile c b)
      = some (a₁.exchangeTwinCargo t) := by
  rw [hc] at hstep hself ⊢
  have hztop : st.board.topOf (Sum.inr t) = some z := (Board.bottomOf_eq _ _ _).mp h₀
  have hztop' : st.board.topOf (Sum.inr t.flipSuit) = some z' :=
    (Board.bottomOf_eq _ _ _).mp h₀'
  have hzt : z ≠ t := (Card.ne_pair_of_canSitOn hfit).1
  have hzt' : z' ≠ t := by
    obtain ⟨-, hb⟩ := Card.ne_pair_of_canSitOn hfit'
    exact fun h => hb (by rw [h, Card.flipSuit_flipSuit])
  rw [apply_pilePile_iff] at hstep ⊢
  obtain ⟨b₀, hbot, hne, hcmr, bd, hatt, rfl⟩ := hstep
  have hb₀t : b₀ ≠ Sum.inr t := by
    intro hcon
    rw [hcon] at hbot
    exact hzt (Option.some.inj (hztop.symm.trans
      ((Board.bottomOf_eq st.board t (Sum.inr t)).mp hbot)))
  have hb₀t' : b₀ ≠ Sum.inr t.flipSuit := by
    intro hcon
    rw [hcon] at hbot
    exact hzt' (Option.some.inj (hztop'.symm.trans
      ((Board.bottomOf_eq st.board t (Sum.inr t.flipSuit)).mp hbot)))
  simp only [State.canMoveRun, Bool.and_eq_true_iff] at hcmr
  obtain ⟨hcp, -⟩ := hcmr
  have hbt : b ≠ Sum.inr t ∧ b ≠ Sum.inr t.flipSuit := by
    constructor
    · intro hcon
      cases b with
      | inl a => exact absurd hcon (by simp)
      | inr d =>
          obtain ⟨htopb, -, -⟩ := canPlace_inr_iff.mp hcp
          rw [hcon, hztop] at htopb
          simp at htopb
    · intro hcon
      cases b with
      | inl a => exact absurd hcon (by simp)
      | inr d =>
          obtain ⟨htopb, -, -⟩ := canPlace_inr_iff.mp hcp
          rw [hcon, hztop'] at htopb
          simp at htopb
  have hb₀E : (st.exchangeTwinCargo t).board.bottomOf t = some b₀ := by
    rw [State.exchangeTwinCargo_board, Board.bottomOf_exchangeTwin, hbot]
    show some (Base.swapTwin t b₀) = some b₀
    rw [Base.swapTwin_eq_self hb₀t hb₀t']
  have hcpE : (st.exchangeTwinCargo t).canPlace t b = true := by
    rw [State.canPlace_exchangeTwin hbt.1 hbt.2]
    exact hcp
  have hcmrE : (st.exchangeTwinCargo t).canMoveRun t b = true := by
    simp only [State.canMoveRun, Bool.and_eq_true_iff]
    refine ⟨hcpE, ?_⟩
    cases b with
    | inl a => rfl
    | inr d =>
        show (!((st.exchangeTwinCargo t).board.aboveOf t).contains d) = true
        rw [State.exchangeTwinCargo_board, lcontains_false_of_notMem (hself d rfl)]
        rfl
  have hattE : ((st.exchangeTwinCargo t).board.detach b₀).attach b t
      = some (bd.exchangeTwin t) := by
    rw [State.exchangeTwinCargo_board,
      Board.exchangeTwin_detach_ne _ _ hb₀t hb₀t']
    exact Board.exchangeTwin_attach_ne _ _ hbt.1 hbt.2 hatt
  exact ⟨b₀, hb₀E, hne, hcmrE, bd.exchangeTwin t, hattE, rfl⟩

/-- The twin-rooted `pilePile` license transfer (the non-braid arm):
the cargos ride the twins (only the roots' own bases change), and the
no-braid walks survive because the detach side only shrinks
(`Board.aboveOf_sub_detach`) while the attach side's cell is not on
the (detached) walk — the landing is off both cargo runs (`hland`,
the own side via seed containment from the source self-landing guard). -/
theorem State.twinLicensed_apply_pilePile_root {st a₁ : State} {t z z' c : Card} {b : Base}
    (hvis' : st.isVis t.flipSuit = true)
    (h₀ : st.board.bottomOf z = some (Sum.inr t))
    (h₀' : st.board.bottomOf z' = some (Sum.inr t.flipSuit))
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.flipSuit = true)
    (hnb : t ∉ st.board.aboveOf z ∧ t.flipSuit ∉ st.board.aboveOf z)
    (hnb' : t ∉ st.board.aboveOf z' ∧ t.flipSuit ∉ st.board.aboveOf z')
    (hstep : st.apply (Move.pilePile c b) = some a₁) (hc : c = t)
    (hland : ∀ d, b = Sum.inr d → d ∉ st.board.aboveOf z ∧ d ∉ st.board.aboveOf z') :
    a₁.twinLicensed t := by
  rw [hc] at hstep
  have hztop : st.board.topOf (Sum.inr t) = some z := (Board.bottomOf_eq _ _ _).mp h₀
  have hztop' : st.board.topOf (Sum.inr t.flipSuit) = some z' :=
    (Board.bottomOf_eq _ _ _).mp h₀'
  have hzt : z ≠ t := (Card.ne_pair_of_canSitOn hfit).1
  have hzt' : z' ≠ t := by
    obtain ⟨-, hb⟩ := Card.ne_pair_of_canSitOn hfit'
    exact fun h => hb (by rw [h, Card.flipSuit_flipSuit])
  rw [apply_pilePile_iff] at hstep
  obtain ⟨b₀, hbot, hne, hcmr, bd, hatt, rfl⟩ := hstep
  simp only [State.canMoveRun, Bool.and_eq_true_iff] at hcmr
  obtain ⟨hcp, -⟩ := hcmr
  have hb₀t : b₀ ≠ Sum.inr t := by
    intro hcon
    rw [hcon] at hbot
    exact hzt (Option.some.inj (hztop.symm.trans
      ((Board.bottomOf_eq st.board t (Sum.inr t)).mp hbot)))
  have hb₀t' : b₀ ≠ Sum.inr t.flipSuit := by
    intro hcon
    rw [hcon] at hbot
    exact hzt' (Option.some.inj (hztop'.symm.trans
      ((Board.bottomOf_eq st.board t (Sum.inr t.flipSuit)).mp hbot)))
  have hbt : b ≠ Sum.inr t ∧ b ≠ Sum.inr t.flipSuit := by
    constructor
    · intro hcon
      cases b with
      | inl a => exact absurd hcon (by simp)
      | inr d =>
          obtain ⟨htopb, -, -⟩ := canPlace_inr_iff.mp hcp
          rw [hcon, hztop] at htopb
          simp at htopb
    · intro hcon
      cases b with
      | inl a => exact absurd hcon (by simp)
      | inr d =>
          obtain ⟨htopb, -, -⟩ := canPlace_inr_iff.mp hcp
          rw [hcon, hztop'] at htopb
          simp at htopb
  have hzbot : st.board.topOf b₀ = some t := (Board.bottomOf_eq st.board t b₀).mp hbot
  -- the attach cell is off the detached walks: the landing is off both
  -- cargo runs and never the run's root
  have hcongrz : bd.aboveOf z = (st.board.detach b₀).aboveOf z := by
    apply Board.aboveOf_congr
    intro x hx
    by_cases hxb : b = Sum.inr x
    · exfalso
      have hcp' : st.canPlace t (Sum.inr x) = true := by rw [← hxb]; exact hcp
      obtain ⟨-, -, hfitdx⟩ := canPlace_inr_iff.mp hcp'
      have h1 : x ≠ z := by
        intro hcon
        rw [hcon] at hfitdx
        exact (canSitOn_antisymm hfit) hfitdx
      rcases List.mem_cons.mp hx with heq | hx'
      · exact h1 heq
      · exact (hland x hxb).1 (Board.aboveOf_sub_detach 52 z [] x hx')
    · rw [Board.attach_topOf_ne _ _ _ hatt (fun hcon => hxb hcon.symm)]

  have hcongrz' : bd.aboveOf z' = (st.board.detach b₀).aboveOf z' := by
    apply Board.aboveOf_congr
    intro x hx
    by_cases hxb : b = Sum.inr x
    · exfalso
      have hcp' : st.canPlace t (Sum.inr x) = true := by rw [← hxb]; exact hcp
      obtain ⟨-, -, hfitdx⟩ := canPlace_inr_iff.mp hcp'
      have h2 : x ≠ z' := by
        intro hcon
        obtain ⟨hrk, -⟩ := (canSitOn_eq t x).mp hfitdx
        obtain ⟨hrk', -⟩ := (canSitOn_eq z' t.flipSuit).mp hfit'
        rw [Card.flipSuit_rank] at hrk'
        rw [hcon] at hrk
        omega
      rcases List.mem_cons.mp hx with heq | hx'
      · exact h2 heq
      · exact (hland x hxb).2 (Board.aboveOf_sub_detach 52 z' [] x hx')
    · rw [Board.attach_topOf_ne _ _ _ hatt (fun hcon => hxb hcon.symm)]

  refine ⟨z, z', ?_, ?_, ?_, ?_, hfit, hfit', ?_, ?_⟩
  · show (bd.bottomOf t).isSome = true
    rw [(Board.bottomOf_eq bd t b).mpr (Board.attach_topOf _ _ _ hatt)]
    rfl
  · show (bd.bottomOf t.flipSuit).isSome = true
    refine bottomOf_isSome_attach hatt ?_
    show ((st.board.detach b₀).bottomOf t.flipSuit).isSome = true
    rw [bottomOf_detach_ne hzbot (Card.flipSuit_ne t)]
    exact hvis'
  · show bd.bottomOf z = some (Sum.inr t)
    exact (Board.bottomOf_eq _ _ _).mpr (by
      rw [Board.attach_topOf_ne _ _ _ hatt (fun hcon => hbt.1 hcon.symm),
        Board.detach_topOf_ne _ _ _ (fun hcon => hb₀t hcon.symm)]
      exact hztop)
  · show bd.bottomOf z' = some (Sum.inr t.flipSuit)
    exact (Board.bottomOf_eq _ _ _).mpr (by
      rw [Board.attach_topOf_ne _ _ _ hatt (fun hcon => hbt.2 hcon.symm),
        Board.detach_topOf_ne _ _ _ (fun hcon => hb₀t' hcon.symm)]
      exact hztop')
  · show t ∉ bd.aboveOf z ∧ t.flipSuit ∉ bd.aboveOf z
    rw [hcongrz]
    constructor
    · intro hmem
      exact hnb.1 (Board.aboveOf_sub_detach 52 z [] t hmem)
    · intro hmem
      exact hnb.2 (Board.aboveOf_sub_detach 52 z [] t.flipSuit hmem)
  · show t ∉ bd.aboveOf z' ∧ t.flipSuit ∉ bd.aboveOf z'
    rw [hcongrz']
    constructor
    · intro hmem
      exact hnb'.1 (Board.aboveOf_sub_detach 52 z' [] t hmem)
    · intro hmem
      exact hnb'.2 (Board.aboveOf_sub_detach 52 z' [] t.flipSuit hmem)

/-- **The t-passing `pilePile` mirror step** (the off-cargo landing —
the session-7 correction, formal): a run whose walk reaches a twin,
landing off both cargo stacks — the SAME move is legal in the
exchanged state and the successors stay exchanged.  The self-landing
guard transfers by `Board.selfLanding_exchangeTwin_of_off_cargo`
(the exchanged walk grows by the other cargo's run, which the
landing is off); the detach/attach congruences fire at the off-pair
bases. -/
theorem State.exchangeTwinCargo_step_pilePile_passing {st a₁ : State} {t z z' c : Card} {b : Base}
    (h₀ : st.board.bottomOf z = some (Sum.inr t))
    (h₀' : st.board.bottomOf z' = some (Sum.inr t.flipSuit))
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.flipSuit = true)
    (hnb : t ∉ st.board.aboveOf z ∧ t.flipSuit ∉ st.board.aboveOf z)
    (hnb' : t ∉ st.board.aboveOf z' ∧ t.flipSuit ∉ st.board.aboveOf z')
    (hc : c ≠ z ∧ c ≠ z')
    (hoff : ∀ d, b = Sum.inr d →
      d ≠ z ∧ d ≠ z' ∧ d ∉ st.board.aboveOf z ∧ d ∉ st.board.aboveOf z')
    (hstep : st.apply (Move.pilePile c b) = some a₁) :
    (st.exchangeTwinCargo t).apply (Move.pilePile c b)
      = some (a₁.exchangeTwinCargo t) := by
  have hztop : st.board.topOf (Sum.inr t) = some z := (Board.bottomOf_eq _ _ _).mp h₀
  have hztop' : st.board.topOf (Sum.inr t.flipSuit) = some z' :=
    (Board.bottomOf_eq _ _ _).mp h₀'
  have hzne : z ≠ t := (Card.ne_pair_of_canSitOn hfit).1
  have hzne' : z ≠ t.flipSuit := (Card.ne_pair_of_canSitOn hfit).2
  have hz't : z' ≠ t := by
    obtain ⟨-, hb⟩ := Card.ne_pair_of_canSitOn hfit'
    exact fun h => hb (by rw [h, Card.flipSuit_flipSuit])
  have hz't' : z' ≠ t.flipSuit := (Card.ne_pair_of_canSitOn hfit').1
  rw [apply_pilePile_iff] at hstep ⊢
  obtain ⟨b₀, hbot, hbne, hcmr, bd, hatt, rfl⟩ := hstep
  simp only [State.canMoveRun, Bool.and_eq_true_iff] at hcmr
  obtain ⟨hcp, hselfm⟩ := hcmr
  have hb₀t : b₀ ≠ Sum.inr t := by
    intro hcon
    rw [hcon] at hbot
    exact hc.1 (Option.some.inj (hztop.symm.trans
      ((Board.bottomOf_eq st.board c (Sum.inr t)).mp hbot))).symm
  have hb₀t' : b₀ ≠ Sum.inr t.flipSuit := by
    intro hcon
    rw [hcon] at hbot
    exact hc.2 (Option.some.inj (hztop'.symm.trans
      ((Board.bottomOf_eq st.board c (Sum.inr t.flipSuit)).mp hbot))).symm
  have hbt : b ≠ Sum.inr t ∧ b ≠ Sum.inr t.flipSuit := by
    constructor
    · intro hcon
      cases b with
      | inl a => exact absurd hcon (by simp)
      | inr d =>
          obtain ⟨htopb, -, -⟩ := canPlace_inr_iff.mp hcp
          rw [hcon, hztop] at htopb
          simp at htopb
    · intro hcon
      cases b with
      | inl a => exact absurd hcon (by simp)
      | inr d =>
          obtain ⟨htopb, -, -⟩ := canPlace_inr_iff.mp hcp
          rw [hcon, hztop'] at htopb
          simp at htopb
  have hselfSrc : ∀ d, b = Sum.inr d → d ∉ st.board.aboveOf c := by
    intro d hd
    have h2 : (!(st.board.aboveOf c).contains d) = true := by
      have h3 := hselfm
      rw [hd] at h3
      exact h3
    intro hmem
    have hc2 : (st.board.aboveOf c).contains d = true :=
      (List.contains_iff_mem).mpr hmem
    rw [hc2] at h2
    simp at h2
  have hselfE : ∀ d, b = Sum.inr d → d ∉ (st.board.exchangeTwin t).aboveOf c := by
    intro d hd
    exact Board.selfLanding_exchangeTwin_of_off_cargo hztop hztop'
      ⟨hzne, hzne', hz't, hz't'⟩ hnb hnb' (hoff d hd) (hselfSrc d hd)
  have hb₀E : (st.exchangeTwinCargo t).board.bottomOf c = some b₀ := by
    rw [State.exchangeTwinCargo_board, Board.bottomOf_exchangeTwin, hbot]
    show some (Base.swapTwin t b₀) = some b₀
    rw [Base.swapTwin_eq_self hb₀t hb₀t']
  have hcpE : (st.exchangeTwinCargo t).canPlace c b = true := by
    rw [State.canPlace_exchangeTwin hbt.1 hbt.2]
    exact hcp
  have hcmrE : (st.exchangeTwinCargo t).canMoveRun c b = true := by
    simp only [State.canMoveRun, Bool.and_eq_true_iff]
    refine ⟨hcpE, ?_⟩
    cases b with
    | inl a => rfl
    | inr d =>
        show (!((st.exchangeTwinCargo t).board.aboveOf c).contains d) = true
        rw [State.exchangeTwinCargo_board, lcontains_false_of_notMem (hselfE d rfl)]
        rfl
  have hattE : ((st.exchangeTwinCargo t).board.detach b₀).attach b c
      = some (bd.exchangeTwin t) := by
    rw [State.exchangeTwinCargo_board,
      Board.exchangeTwin_detach_ne _ _ hb₀t hb₀t']
    exact Board.exchangeTwin_attach_ne _ _ hbt.1 hbt.2 hatt
  exact ⟨b₀, hb₀E, hbne, hcmrE, bd.exchangeTwin t, hattE, rfl⟩

/-- **The t-passing `pilePile` license transfer** (the off-cargo
landing): the cargos ride the twins (only the root's own base
changes), and the no-braid walks survive because the attach cell is
on neither cargo's walk — the landing premise (`hoff`) plus the
detach-shrink (`aboveOf_sub_detach`) close the congruence. -/
theorem State.twinLicensed_apply_pilePile_passing {st a₁ : State} {t z z' c : Card} {b : Base}
    (hvis : st.isVis t = true) (hvis' : st.isVis t.flipSuit = true)
    (h₀ : st.board.bottomOf z = some (Sum.inr t))
    (h₀' : st.board.bottomOf z' = some (Sum.inr t.flipSuit))
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.flipSuit = true)
    (hnb : t ∉ st.board.aboveOf z ∧ t.flipSuit ∉ st.board.aboveOf z)
    (hnb' : t ∉ st.board.aboveOf z' ∧ t.flipSuit ∉ st.board.aboveOf z')
    (hct : c ≠ t ∧ c ≠ t.flipSuit) (hc : c ≠ z ∧ c ≠ z')
    (hoff : ∀ d, b = Sum.inr d →
      d ≠ z ∧ d ≠ z' ∧ d ∉ st.board.aboveOf z ∧ d ∉ st.board.aboveOf z')
    (hstep : st.apply (Move.pilePile c b) = some a₁) : a₁.twinLicensed t := by
  have hztop : st.board.topOf (Sum.inr t) = some z := (Board.bottomOf_eq _ _ _).mp h₀
  have hztop' : st.board.topOf (Sum.inr t.flipSuit) = some z' :=
    (Board.bottomOf_eq _ _ _).mp h₀'
  rw [apply_pilePile_iff] at hstep
  obtain ⟨b₀, hbot, hbne, hcmr, bd, hatt, rfl⟩ := hstep
  simp only [State.canMoveRun, Bool.and_eq_true_iff] at hcmr
  obtain ⟨hcp, -⟩ := hcmr
  have hzbot : st.board.topOf b₀ = some c := (Board.bottomOf_eq st.board c b₀).mp hbot
  have hb₀t : b₀ ≠ Sum.inr t := by
    intro hcon
    rw [hcon] at hbot
    exact hc.1 (Option.some.inj (hztop.symm.trans
      ((Board.bottomOf_eq st.board c (Sum.inr t)).mp hbot))).symm
  have hb₀t' : b₀ ≠ Sum.inr t.flipSuit := by
    intro hcon
    rw [hcon] at hbot
    exact hc.2 (Option.some.inj (hztop'.symm.trans
      ((Board.bottomOf_eq st.board c (Sum.inr t.flipSuit)).mp hbot))).symm
  have hbt : b ≠ Sum.inr t ∧ b ≠ Sum.inr t.flipSuit := by
    constructor
    · intro hcon
      cases b with
      | inl a => exact absurd hcon (by simp)
      | inr d =>
          obtain ⟨htopb, -, -⟩ := canPlace_inr_iff.mp hcp
          rw [hcon, hztop] at htopb
          simp at htopb
    · intro hcon
      cases b with
      | inl a => exact absurd hcon (by simp)
      | inr d =>
          obtain ⟨htopb, -, -⟩ := canPlace_inr_iff.mp hcp
          rw [hcon, hztop'] at htopb
          simp at htopb
  have hcongrz : bd.aboveOf z = (st.board.detach b₀).aboveOf z := by
    apply Board.aboveOf_congr
    intro x hx
    by_cases hxb : b = Sum.inr x
    · exfalso
      obtain ⟨h1, -, h3, -⟩ := hoff x hxb
      rcases List.mem_cons.mp hx with heq | hx'
      · exact h1 heq
      · exact h3 (Board.aboveOf_sub_detach 52 z [] x hx')
    · rw [Board.attach_topOf_ne _ _ _ hatt (fun hcon => hxb hcon.symm)]
  have hcongrz' : bd.aboveOf z' = (st.board.detach b₀).aboveOf z' := by
    apply Board.aboveOf_congr
    intro x hx
    by_cases hxb : b = Sum.inr x
    · exfalso
      obtain ⟨-, h2, -, h4⟩ := hoff x hxb
      rcases List.mem_cons.mp hx with heq | hx'
      · exact h2 heq
      · exact h4 (Board.aboveOf_sub_detach 52 z' [] x hx')
    · rw [Board.attach_topOf_ne _ _ _ hatt (fun hcon => hxb hcon.symm)]
  refine ⟨z, z', ?_, ?_, ?_, ?_, hfit, hfit', ?_, ?_⟩
  · show (bd.bottomOf t).isSome = true
    refine bottomOf_isSome_attach hatt ?_
    show ((st.board.detach b₀).bottomOf t).isSome = true
    rw [bottomOf_detach_ne hzbot (fun h => hct.1 h.symm)]
    exact hvis
  · show (bd.bottomOf t.flipSuit).isSome = true
    refine bottomOf_isSome_attach hatt ?_
    show ((st.board.detach b₀).bottomOf t.flipSuit).isSome = true
    rw [bottomOf_detach_ne hzbot (fun h => hct.2 h.symm)]
    exact hvis'
  · show bd.bottomOf z = some (Sum.inr t)
    exact (Board.bottomOf_eq _ _ _).mpr (by
      rw [Board.attach_topOf_ne _ _ _ hatt (fun hcon => hbt.1 hcon.symm),
        Board.detach_topOf_ne _ _ _ (fun hcon => hb₀t hcon.symm)]
      exact hztop)
  · show bd.bottomOf z' = some (Sum.inr t.flipSuit)
    exact (Board.bottomOf_eq _ _ _).mpr (by
      rw [Board.attach_topOf_ne _ _ _ hatt (fun hcon => hbt.2 hcon.symm),
        Board.detach_topOf_ne _ _ _ (fun hcon => hb₀t' hcon.symm)]
      exact hztop')
  · show t ∉ bd.aboveOf z ∧ t.flipSuit ∉ bd.aboveOf z
    rw [hcongrz]
    constructor
    · intro hmem
      exact hnb.1 (Board.aboveOf_sub_detach 52 z [] t hmem)
    · intro hmem
      exact hnb.2 (Board.aboveOf_sub_detach 52 z [] t.flipSuit hmem)
  · show t ∉ bd.aboveOf z' ∧ t.flipSuit ∉ bd.aboveOf z'
    rw [hcongrz']
    constructor
    · intro hmem
      exact hnb'.1 (Board.aboveOf_sub_detach 52 z' [] t hmem)
    · intro hmem
      exact hnb'.2 (Board.aboveOf_sub_detach 52 z' [] t.flipSuit hmem)

/-- **The walk collects the predecessor** (the pred-reaches
primitive): if the walk from `y` collected `z`, and `z` sits on `u`,
then the walk collected `u` first — or started there.  With the
license's rigidity (h₀ pins the cargos' bases, the braids pin the
twins off the cargo chains), this is the engine of the mirror's
self-landing guard: `z ∈ aboveOf_stx c` forces `t'` onto the
walk-from-`c`, and the braid case analysis kills every route. -/
theorem Board.aboveOf_pred_reaches {bd : Board} :
    ∀ (n : Nat) (b : Base) (acc : List Card) (z u : Card),
      bd.topOf (Sum.inr u) = some z →
      z ∈ Board.aboveOf.go bd n b acc →
      z ∈ acc ∨ u ∈ acc ∨ u ∈ Board.aboveOf.go bd n b acc ∨ b = Sum.inr u := by
  intro n
  induction n with
  | zero => intro b acc z u _ hz; exact Or.inl hz
  | succ k ih =>
      intro b acc z u hu hz
      cases ht : bd.topOf b with
      | none => rw [Board.aboveOf_go_topOf_none ht] at hz; exact Or.inl hz
      | some c' =>
          by_cases hcon : acc.contains c' = true
          · rw [Board.aboveOf_go_stop ht hcon] at hz; exact Or.inl hz
          · rw [Board.aboveOf_go_step ht hcon] at hz
            rcases ih (Sum.inr c') (c' :: acc) z u hu hz with h | h | h | h
            · rcases List.mem_cons.mp h with heq | h'
              · rw [heq] at hu
                exact Or.inr (Or.inr (Or.inr (bd.inj b (Sum.inr u) c' ht hu)))
              · exact Or.inl h'
            · rcases List.mem_cons.mp h with heq | h'
              · rw [heq]
                refine Or.inr (Or.inr (Or.inl ?_))
                rw [Board.aboveOf_go_step ht hcon]
                exact Board.aboveOf_go_mem bd k (Sum.inr c') (c' :: acc) c' (by simp)
              · exact Or.inr (Or.inl h')
            · exact Or.inr (Or.inr (Or.inl (Board.aboveOf_go_step ht hcon ▸ h)))
            · rw [(Sum.inr.inj h).symm]
              refine Or.inr (Or.inr (Or.inl ?_))
              rw [Board.aboveOf_go_step ht hcon]
              exact Board.aboveOf_go_mem bd k (Sum.inr c') (c' :: acc) c' (by simp)

/-- The 52 form: the walk from `y` collected `z` ⟹ `z`'s base card
`u` was collected too (or is the start). -/
theorem Board.aboveOf_pred {bd : Board} {y z u : Card}
    (hu : bd.topOf (Sum.inr u) = some z) (hz : z ∈ bd.aboveOf y) :
    u = y ∨ u ∈ bd.aboveOf y := by
  rcases Board.aboveOf_pred_reaches 52 (Sum.inr y) [] z u hu hz with h | h | h | h
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact Or.inr h
  · exact Or.inl (Sum.inr.inj h).symm

/-- **Walk comparability** (the tail-fact): two distinct cards
collected by the same walk are comparable — the later-collected is
above the earlier.  The engine is the seeded-walk bound (session-7):
the continuation past the earlier card is a walk seeded with the
cards before it, and the fresh walk from the earlier card collects
everything the continuation does.  The mirror-guard's last
primitive. -/
theorem Board.aboveOf_comp {bd : Board} :
    ∀ (n : Nat) (b : Base) (acc : List Card) (x y : Card),
      x ∈ Board.aboveOf.go bd n b acc → y ∈ Board.aboveOf.go bd n b acc →
      x ∉ acc → y ∉ acc → x ≠ y →
      x ∈ bd.aboveOf y ∨ y ∈ bd.aboveOf x := by
  intro n
  induction n with
  | zero => intro b acc x y hx _ hxa _ _; exact absurd hx hxa
  | succ k ih =>
      intro b acc x y hx hy hxa hya hne
      cases ht : bd.topOf b with
      | none => rw [Board.aboveOf_go_topOf_none ht] at hx; exact absurd hx hxa
      | some c' =>
          by_cases hcon : acc.contains c' = true
          · rw [Board.aboveOf_go_stop ht hcon] at hx; exact absurd hx hxa
          · rw [Board.aboveOf_go_step ht hcon] at hx hy
            by_cases hxc : x = c'
            · subst hxc
              rcases Board.aboveOf_go_seeded_subset (52 - k) k x (x :: acc) [] y
                (List.nil_subset _) hy with h | h
              · rcases List.mem_cons.mp h with heq | h'
                · exact absurd heq.symm hne
                · exact absurd h' hya
              · refine Or.inr ?_
                rw [Board.aboveOf_eq_go (52 - k + k) (by omega)]
                exact h
            · by_cases hyc : y = c'
              · subst hyc
                rcases Board.aboveOf_go_seeded_subset (52 - k) k y (y :: acc) [] x
                  (List.nil_subset _) hx with h | h
                · rcases List.mem_cons.mp h with heq | h'
                  · exact absurd heq hne
                  · exact absurd h' hxa
                · refine Or.inl ?_
                  rw [Board.aboveOf_eq_go (52 - k + k) (by omega)]
                  exact h
              · exact ih (Sum.inr c') (c' :: acc) x y hx hy
                  (fun h => (List.mem_cons.mp h).elim hxc hxa)
                  (fun h => (List.mem_cons.mp h).elim hyc hya) hne

/-- **The mirror's self-landing guard**: in the exchanged state, the
walk from `c` never reaches `z` — so the mirror merge (the run riding
the other cargo, landing on the now-bare `z`) is never self-landing
via `z`.  The assembly: pred-reaches puts `t'` on the exchanged walk
(z's base there is `t'` — the seat swap), the exchange walk-bound
transfers `t'` to the source side, and every case dies by a braid:
`t'` above a cargo is `hnb`/`hnb'` outright; `t'` on the source
c-run (with `hmerge`'s `t`) makes the twins comparable, and each
comparability branch chains through the covers (`z`, `z'`) back into
the braids.  The rank exclusions come from the fits. -/
theorem State.exchangeTwin_mirror_guard {st : State} {t z z' c : Card}
    (hztop : st.board.topOf (Sum.inr t) = some z)
    (hztop' : st.board.topOf (Sum.inr t.flipSuit) = some z')
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.flipSuit = true)
    (hnb : t ∉ st.board.aboveOf z ∧ t.flipSuit ∉ st.board.aboveOf z)
    (hnb' : t ∉ st.board.aboveOf z' ∧ t.flipSuit ∉ st.board.aboveOf z')
    (hmerge : t ∈ st.board.aboveOf c)
    (hct : c ≠ t ∧ c ≠ t.flipSuit) :
    z ∉ (st.board.exchangeTwin t).aboveOf c := by
  have hzne : z ≠ t := by
    intro hcon
    rw [hcon] at hfit
    obtain ⟨hr, -⟩ := (canSitOn_eq t t).mp hfit
    omega
  have hzne' : z ≠ t.flipSuit := by
    intro hcon
    rw [hcon] at hfit
    obtain ⟨hr, -⟩ := (canSitOn_eq t.flipSuit t).mp hfit
    rw [Card.flipSuit_rank] at hr
    omega
  have hz'ne : z' ≠ t := by
    intro hcon
    rw [hcon] at hfit'
    obtain ⟨hr, -⟩ := (canSitOn_eq t t.flipSuit).mp hfit'
    rw [Card.flipSuit_rank] at hr
    omega
  have hz'ne' : z' ≠ t.flipSuit := by
    intro hcon
    rw [hcon] at hfit'
    obtain ⟨hr, -⟩ := (canSitOn_eq t.flipSuit t.flipSuit).mp hfit'
    omega
  have ht'z : t.flipSuit ≠ z := by
    intro hcon
    rw [← hcon] at hfit
    obtain ⟨hr, -⟩ := (canSitOn_eq t.flipSuit t).mp hfit
    rw [Card.flipSuit_rank] at hr
    omega
  have htz' : t ≠ z' := by
    intro hcon
    rw [← hcon] at hfit'
    obtain ⟨hr, -⟩ := (canSitOn_eq t t.flipSuit).mp hfit'
    rw [Card.flipSuit_rank] at hr
    omega
  have htt' : t ≠ t.flipSuit := (Card.flipSuit_ne t).symm
  have hzz' : z ≠ z' := by
    intro hcon
    rw [hcon] at hztop
    exact htt' (Sum.inr.inj (st.board.inj (Sum.inr t) (Sum.inr t.flipSuit) z' hztop hztop'))
  intro hmem
  have htopstx : (st.board.exchangeTwin t).topOf (Sum.inr t.flipSuit) = some z := by
    rw [Board.exchangeTwin_topOf]
    have hsw : Base.swapTwin t (Sum.inr t.flipSuit) = Sum.inr t := by
      show Sum.inr (Card.swapTwin t t.flipSuit) = Sum.inr t
      rw [Card.swapTwin_self_right]
    rw [hsw]
    exact hztop
  rcases Board.aboveOf_pred htopstx hmem with h | h
  · exact hct.2 h.symm
  · rcases Board.aboveOf_exchangeTwin_bound hztop hztop'
      ⟨hzne, hzne', hz'ne, hz'ne'⟩ hnb hnb' h with h | h | h | h | h
    · -- t' on the source c-run: both twins — comparability
      have hz1 : z ∈ st.board.aboveOf t := Board.mem_aboveOf_of_topOf hztop
      have hz1' : z' ∈ st.board.aboveOf t.flipSuit :=
        Board.mem_aboveOf_of_topOf hztop'
      rcases Board.aboveOf_comp 52 (Sum.inr c) [] t.flipSuit t h hmerge
        (by simp) (by simp) (fun hcon => htt' hcon.symm) with hc | hc
      · -- t' above t: compare with z (t's cover)
        rcases Board.aboveOf_comp 52 (Sum.inr t) [] t.flipSuit z hc hz1
          (by simp) (by simp) (fun hcon => ht'z hcon) with hc2 | hc2
        · exact hnb.2 hc2
        · rcases Board.aboveOf_comp 52 (Sum.inr t.flipSuit) [] z z' hc2 hz1'
            (by simp) (by simp) (fun hcon => hzz' hcon) with hc3 | hc3
          · rcases Board.aboveOf_pred hztop hc3 with h4 | h4
            · exact htz' h4
            · exact hnb'.1 h4
          · rcases Board.aboveOf_pred hztop' hc3 with h4 | h4
            · exact ht'z h4
            · exact hnb.2 h4
      · -- t above t': compare with z' (t''s cover)
        rcases Board.aboveOf_comp 52 (Sum.inr t.flipSuit) [] t z' hc hz1'
          (by simp) (by simp) (fun hcon => htz' hcon) with hc2 | hc2
        · exact hnb'.1 hc2
        · rcases Board.aboveOf_comp 52 (Sum.inr t) [] z' z hc2 hz1
            (by simp) (by simp) (fun hcon => hzz' hcon.symm) with hc3 | hc3
          · rcases Board.aboveOf_pred hztop' hc3 with h4 | h4
            · exact ht'z h4
            · exact hnb.2 h4
          · rcases Board.aboveOf_pred hztop hc3 with h4 | h4
            · exact htz' h4
            · exact hnb'.1 h4
    · exact ht'z h
    · exact hz'ne' h.symm
    · exact hnb.2 h
    · exact hnb'.2 h

/-- **The mirror-guard, z'-stack form**: for any card of the other
cargo's run (y above z'), the exchanged walk from y never reaches z —
the rider transfer's guard.  Simpler than the c-run form: the first
bound case dies by transitivity directly (y is above z', so t' above
y forces t' above z' — the braid), no both-twins comparability
needed. -/
theorem State.exchangeTwin_mirror_guard_zstack {st : State} {t z z' y : Card}
    (hztop : st.board.topOf (Sum.inr t) = some z)
    (hztop' : st.board.topOf (Sum.inr t.flipSuit) = some z')
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.flipSuit = true)
    (hnb : t ∉ st.board.aboveOf z ∧ t.flipSuit ∉ st.board.aboveOf z)
    (hnb' : t ∉ st.board.aboveOf z' ∧ t.flipSuit ∉ st.board.aboveOf z')
    (hy : y ∈ st.board.aboveOf z') :
    z ∉ (st.board.exchangeTwin t).aboveOf y := by
  have hzne : z ≠ t := by
    intro hcon
    rw [hcon] at hfit
    obtain ⟨hr, -⟩ := (canSitOn_eq t t).mp hfit
    omega
  have hzne' : z ≠ t.flipSuit := by
    intro hcon
    rw [hcon] at hfit
    obtain ⟨hr, -⟩ := (canSitOn_eq t.flipSuit t).mp hfit
    rw [Card.flipSuit_rank] at hr
    omega
  have hz'ne : z' ≠ t := by
    intro hcon
    rw [hcon] at hfit'
    obtain ⟨hr, -⟩ := (canSitOn_eq t t.flipSuit).mp hfit'
    rw [Card.flipSuit_rank] at hr
    omega
  have hz'ne' : z' ≠ t.flipSuit := by
    intro hcon
    rw [hcon] at hfit'
    obtain ⟨hr, -⟩ := (canSitOn_eq t.flipSuit t.flipSuit).mp hfit'
    omega
  have ht'z : t.flipSuit ≠ z := by
    intro hcon
    rw [← hcon] at hfit
    obtain ⟨hr, -⟩ := (canSitOn_eq t.flipSuit t).mp hfit
    rw [Card.flipSuit_rank] at hr
    omega
  have ht'z' : t.flipSuit ≠ z' := by
    intro hcon
    rw [← hcon] at hfit'
    obtain ⟨hr, -⟩ := (canSitOn_eq t.flipSuit t.flipSuit).mp hfit'
    omega
  intro hmem
  have htopstx : (st.board.exchangeTwin t).topOf (Sum.inr t.flipSuit) = some z := by
    rw [Board.exchangeTwin_topOf]
    have hsw : Base.swapTwin t (Sum.inr t.flipSuit) = Sum.inr t := by
      show Sum.inr (Card.swapTwin t t.flipSuit) = Sum.inr t
      rw [Card.swapTwin_self_right]
    rw [hsw]
    exact hztop
  rcases Board.aboveOf_pred htopstx hmem with h | h
  · rw [← h] at hy
    exact hnb'.2 hy
  · rcases Board.aboveOf_exchangeTwin_bound hztop hztop'
      ⟨hzne, hzne', hz'ne, hz'ne'⟩ hnb hnb' h with h | h | h | h | h
    · exact hnb'.2 (Board.aboveOf_trans hy h)
    · exact ht'z h
    · exact ht'z' h
    · exact hnb.2 h
    · exact hnb'.2 h

/-! ## The twin-swap replay, separated case (L1/O3, part i)

The provable half of the interleaving window: when the winning
play's twin foundation moves are separated by a mid whose moves
never touch the twin suits' heights, the local swap preserves
solvability.  The mirror plays [prefix*, stack t', mid*, stack t,
suffix*]; between the twin stackings the two games correspond by
the CROSS-SKEW (the twin suits' heights exchanged — each game has
stacked exactly one twin), the ortho mid maintains it step-by-step,
and the second stackings re-sync (both suits gain their twin's rank
once), so the tail conjugates again. -/

/-- A move whose legality never reads the twin suits' heights: the
three height-reading kinds with their moved card off the twin suits;
everything else is height-blind (draw/reveal/deckPile/pilePile never
probe heights). -/
def Move.orthoTwin (t : Card) : Move → Bool
  | .pileStack c => decide (c.suit ≠ t.suit ∧ c.suit ≠ t.flipSuit.suit)
  | .deckStack c => decide (c.suit ≠ t.suit ∧ c.suit ≠ t.flipSuit.suit)
  | .stackPile c _ => decide (c.suit ≠ t.suit ∧ c.suit ≠ t.flipSuit.suit)
  | _ => true

/-- Two states differing only in the twin suits' heights. -/
def State.twinHeightRel (t : Card) (S S' : State) : Prop :=
  S.board = S'.board ∧ S.deal = S'.deal ∧ S.depths = S'.depths ∧
    S.stock = S'.stock ∧ S.drawStep = S'.drawStep ∧
    ∀ s, s ≠ t.suit → s ≠ t.flipSuit.suit → S.heights s = S'.heights s

/-- **The height-congruence**: an ortho move's firing and effects
agree on states differing only in the twin suits' heights — the
reading kinds probe the moved card's suit (off the twin suits, so
agreeing); the height-blind kinds never probe; the successors keep
the relation (the height update touches only the moved card's
suit). -/
theorem State.apply_twinHeightRel {t : Card} {S S' : State} {m : Move}
    (hrel : State.twinHeightRel t S S') (hort : Move.orthoTwin t m = true)
    {R : State} (hS : S.apply m = some R) :
    ∃ R', S'.apply m = some R' ∧ State.twinHeightRel t R R' := by
  obtain ⟨hb, hd, hdp, hst, hds, hh⟩ := hrel
  cases m with
  | draw =>
      rw [apply_draw_iff] at hS
      obtain rfl := hS
      refine ⟨{S' with stock := S'.stock.dealOnce S'.drawStep}, apply_draw_iff.mpr rfl, hb, hd, hdp, ?_, hds, ?_⟩
      · show S.stock.dealOnce S.drawStep = S'.stock.dealOnce S'.drawStep
        rw [hst, hds]
      · intro s h1 h2
        show S.heights s = S'.heights s
        exact hh s h1 h2
  | reveal c =>
      rw [apply_reveal_iff] at hS
      obtain ⟨ht, r, a, bd, hbot, hp, ha, rfl⟩ := hS
      have ht' : S'.board.topOf (Sum.inr c) = none := by rw [← hb]; exact ht
      have hbot' : S'.board.bottomOf c = some (Sum.inr r) := by rw [← hb]; exact hbot
      have hp' : S'.pileOfTopHidden r = some a := by
        rw [← Frame.pileOfTopHidden_congr hd hdp]
        exact hp
      have ha' : S'.board.attach (S'.hiddenBase a) r = some bd := by
        rw [show S'.hiddenBase a = S.hiddenBase a from (Frame.hiddenBase_congr hd hdp a).symm, ← hb]
        exact ha
      refine ⟨{S' with board := bd, depths := fun a' => if a' = a then S'.depths a - 1 else S'.depths a'}, apply_reveal_iff.mpr ⟨ht', r, a, bd, hbot', hp', ha', rfl⟩, rfl, hd, ?_, hst, hds, ?_⟩
      · funext a'
        by_cases ha' : a' = a
        · show (if a' = a then S.depths a - 1 else S.depths a') = (if a' = a then S'.depths a - 1 else S'.depths a')
          rw [if_pos ha', if_pos ha', hdp]
        · show (if a' = a then S.depths a - 1 else S.depths a') = (if a' = a then S'.depths a - 1 else S'.depths a')
          rw [if_neg ha', if_neg ha']
          show S.depths a' = S'.depths a'
          rw [hdp]
      · intro s h1 h2
        show S.heights s = S'.heights s
        exact hh s h1 h2
  | deckPile c b =>
      rw [apply_deckPile_iff] at hS
      obtain ⟨hprev, hcp, bd, hatt, rfl⟩ := hS
      have hprev' : S'.stock.prev = some c := by rw [← hst]; exact hprev
      have hisVis : ∀ d, S'.isVis d = S.isVis d := by
        intro d
        simp only [State.isVis, hb]
      have hcp' : S'.canPlace c b = true := by
        cases b with
        | inl a =>
            obtain ⟨htb, hking⟩ := canPlace_inl_iff.mp hcp
            exact canPlace_inl_iff.mpr ⟨by rw [← hb]; exact htb, hking⟩
        | inr d =>
            obtain ⟨htb, hvis, hcs⟩ := canPlace_inr_iff.mp hcp
            refine canPlace_inr_iff.mpr ⟨by rw [← hb]; exact htb, ?_, hcs⟩
            rw [hisVis d]
            exact hvis
      have hatt' : S'.board.attach b c = some bd := by rw [← hb]; exact hatt
      refine ⟨{S' with board := bd, stock := S'.stock.removeAt (S'.stock.cursor - 1)}, apply_deckPile_iff.mpr ⟨hprev', hcp', bd, hatt', rfl⟩, rfl, hd, hdp, ?_, hds, ?_⟩
      · show S.stock.removeAt (S.stock.cursor - 1) = S'.stock.removeAt (S'.stock.cursor - 1)
        rw [hst]
      · intro s h1 h2
        show S.heights s = S'.heights s
        exact hh s h1 h2
  | deckStack c =>
      rw [apply_deckStack_iff] at hS
      obtain ⟨hprev, hrk, rfl⟩ := hS
      obtain ⟨hsu, hsu'⟩ := (decide_eq_true_iff).mp hort
      have hrk' : c.rank.toIdx = S'.heights c.suit := by
        rw [← hh c.suit hsu hsu']
        exact hrk
      refine ⟨{S' with stock := S'.stock.removeAt (S'.stock.cursor - 1), heights := fun s => if s = c.suit then S'.heights s + 1 else S'.heights s}, apply_deckStack_iff.mpr ⟨by rw [← hst]; exact hprev, hrk', rfl⟩, hb, hd, hdp, ?_, hds, ?_⟩
      · show S.stock.removeAt (S.stock.cursor - 1) = S'.stock.removeAt (S'.stock.cursor - 1)
        rw [hst]
      · intro s h1 h2
        show (if s = c.suit then S.heights s + 1 else S.heights s) = (if s = c.suit then S'.heights s + 1 else S'.heights s)
        by_cases hsc : s = c.suit
        · rw [if_pos hsc, if_pos hsc, hh s h1 h2]
        · rw [if_neg hsc, if_neg hsc]
          exact hh s h1 h2
  | pileStack c =>
      rw [apply_pileStack_iff] at hS
      obtain ⟨ht, b, hbot, hrk, rfl⟩ := hS
      obtain ⟨hsu, hsu'⟩ := (decide_eq_true_iff).mp hort
      have hrk' : c.rank.toIdx = S'.heights c.suit := by
        rw [← hh c.suit hsu hsu']
        exact hrk
      refine ⟨{S' with board := S'.board.detach b, heights := fun s => if s = c.suit then S'.heights s + 1 else S'.heights s}, apply_pileStack_iff.mpr ⟨by rw [← hb]; exact ht, b, by rw [← hb]; exact hbot, hrk', rfl⟩, by rw [hb], hd, hdp, hst, hds, ?_⟩
      · intro s h1 h2
        show (if s = c.suit then S.heights s + 1 else S.heights s) = (if s = c.suit then S'.heights s + 1 else S'.heights s)
        by_cases hsc : s = c.suit
        · rw [if_pos hsc, if_pos hsc, hh s h1 h2]
        · rw [if_neg hsc, if_neg hsc]
          exact hh s h1 h2
  | stackPile c b =>
      rw [apply_stackPile_iff] at hS
      obtain ⟨hrk, hcp, bd, hatt, rfl⟩ := hS
      obtain ⟨hsu, hsu'⟩ := (decide_eq_true_iff).mp hort
      have hrk' : c.rank.toIdx + 1 = S'.heights c.suit := by
        rw [← hh c.suit hsu hsu']
        exact hrk
      have hisVis : ∀ d, S'.isVis d = S.isVis d := by
        intro d
        simp only [State.isVis, hb]
      have hcp' : S'.canPlace c b = true := by
        cases b with
        | inl a =>
            obtain ⟨htb, hking⟩ := canPlace_inl_iff.mp hcp
            exact canPlace_inl_iff.mpr ⟨by rw [← hb]; exact htb, hking⟩
        | inr d =>
            obtain ⟨htb, hvis, hcs⟩ := canPlace_inr_iff.mp hcp
            refine canPlace_inr_iff.mpr ⟨by rw [← hb]; exact htb, ?_, hcs⟩
            rw [hisVis d]
            exact hvis
      have hatt' : S'.board.attach b c = some bd := by rw [← hb]; exact hatt
      refine ⟨{S' with board := bd, heights := fun s => if s = c.suit then S'.heights s - 1 else S'.heights s}, apply_stackPile_iff.mpr ⟨hrk', hcp', bd, hatt', rfl⟩, rfl, hd, hdp, hst, hds, ?_⟩
      · intro s h1 h2
        show (if s = c.suit then S.heights s - 1 else S.heights s) = (if s = c.suit then S'.heights s - 1 else S'.heights s)
        by_cases hsc : s = c.suit
        · rw [if_pos hsc, if_pos hsc, hh s h1 h2]
        · rw [if_neg hsc, if_neg hsc]
          exact hh s h1 h2
  | pilePile c b =>
      rw [apply_pilePile_iff] at hS
      obtain ⟨b₀, hbot, hne, hcmr, bd, hatt, rfl⟩ := hS
      have hbot' : S'.board.bottomOf c = some b₀ := by rw [← hb]; exact hbot
      have hatt' : (S'.board.detach b₀).attach b c = some bd := by rw [← hb]; exact hatt
      have hcmr' : S'.canMoveRun c b = true := by
        cases b with
        | inl a =>
            have hcpa : S.canPlace c (Sum.inl a) = true := canMoveRun_inl_iff.mp hcmr
            obtain ⟨htb, hking⟩ := canPlace_inl_iff.mp hcpa
            exact canMoveRun_inl_iff.mpr (canPlace_inl_iff.mpr ⟨by rw [← hb]; exact htb, hking⟩)
        | inr d =>
            obtain ⟨hcpa, hac⟩ := canMoveRun_inr_iff.mp hcmr
            obtain ⟨htb, hvis, hcs⟩ := canPlace_inr_iff.mp hcpa
            refine canMoveRun_inr_iff.mpr ⟨canPlace_inr_iff.mpr
              ⟨by rw [← hb]; exact htb, ?_, hcs⟩, by rw [← hb]; exact hac⟩
            show S'.isVis d = true
            rw [show S'.isVis d = S.isVis d from by simp only [State.isVis, hb]]
            exact hvis
      refine ⟨{S' with board := bd}, apply_pilePile_iff.mpr ⟨b₀, hbot', hne, hcmr', bd, hatt', rfl⟩, rfl, hd, hdp, hst, hds, ?_⟩
      · intro s h1 h2
        show S.heights s = S'.heights s
        exact hh s h1 h2

/-- **The twin suits' heights are ortho-invariant**: an ortho move
changes at most the moved card's suit (off the twin suits). -/
theorem State.apply_ortho_preserves {t : Card} {S R : State} {m : Move}
    (hort : Move.orthoTwin t m = true) (hS : S.apply m = some R) :
    R.heights t.suit = S.heights t.suit ∧
      R.heights t.flipSuit.suit = S.heights t.flipSuit.suit := by
  cases m with
  | draw =>
      rw [apply_draw_iff] at hS
      obtain rfl := hS
      exact ⟨rfl, rfl⟩
  | reveal c =>
      rw [apply_reveal_iff] at hS
      obtain ⟨-, -, -, -, -, -, -, rfl⟩ := hS
      exact ⟨rfl, rfl⟩
  | deckPile c b =>
      rw [apply_deckPile_iff] at hS
      obtain ⟨-, -, -, -, rfl⟩ := hS
      exact ⟨rfl, rfl⟩
  | deckStack c =>
      rw [apply_deckStack_iff] at hS
      obtain ⟨-, -, rfl⟩ := hS
      obtain ⟨hsu, hsu'⟩ := (decide_eq_true_iff).mp hort
      refine ⟨?_, ?_⟩
      · show (if t.suit = c.suit then S.heights t.suit + 1 else S.heights t.suit) = S.heights t.suit
        rw [if_neg (fun hc => hsu hc.symm)]
      · show (if t.flipSuit.suit = c.suit then S.heights t.flipSuit.suit + 1 else S.heights t.flipSuit.suit) = S.heights t.flipSuit.suit
        rw [if_neg (fun hc => hsu' hc.symm)]
  | pileStack c =>
      rw [apply_pileStack_iff] at hS
      obtain ⟨-, -, -, -, rfl⟩ := hS
      obtain ⟨hsu, hsu'⟩ := (decide_eq_true_iff).mp hort
      refine ⟨?_, ?_⟩
      · show (if t.suit = c.suit then S.heights t.suit + 1 else S.heights t.suit) = S.heights t.suit
        rw [if_neg (fun hc => hsu hc.symm)]
      · show (if t.flipSuit.suit = c.suit then S.heights t.flipSuit.suit + 1 else S.heights t.flipSuit.suit) = S.heights t.flipSuit.suit
        rw [if_neg (fun hc => hsu' hc.symm)]
  | stackPile c b =>
      rw [apply_stackPile_iff] at hS
      obtain ⟨-, -, -, -, rfl⟩ := hS
      obtain ⟨hsu, hsu'⟩ := (decide_eq_true_iff).mp hort
      refine ⟨?_, ?_⟩
      · show (if t.suit = c.suit then S.heights t.suit - 1 else S.heights t.suit) = S.heights t.suit
        rw [if_neg (fun hc => hsu hc.symm)]
      · show (if t.flipSuit.suit = c.suit then S.heights t.flipSuit.suit - 1 else S.heights t.flipSuit.suit) = S.heights t.flipSuit.suit
        rw [if_neg (fun hc => hsu' hc.symm)]
  | pilePile c b =>
      rw [apply_pilePile_iff] at hS
      obtain ⟨-, -, -, -, -, -, rfl⟩ := hS
      exact ⟨rfl, rfl⟩

/-! ### Chunk B: the cross-skew and the separated replay -/

/-- An ortho move is clean (its moved card's suit is off the twin
suits, so the card is off the pair). -/
theorem Move.orthoTwin_clean {t : Card} {m : Move} (hort : Move.orthoTwin t m = true) :
    Move.cleanTwin t m = true := by
  cases m with
  | draw | reveal _ | deckPile _ _ | pilePile _ _ => rfl
  | deckStack c | pileStack c | stackPile c _ =>
      obtain ⟨hsu, hsu'⟩ := (decide_eq_true_iff).mp hort
      show Card.offPair t c = true
      exact Card.offPair_true (fun h => hsu (by rw [h])) (fun h => hsu' (by rw [h]))

/-- The twin-height exchange: only the two twin suits' height entries
are swapped, everything else is kept. -/
def State.twinHeightSwap (t : Card) (st : State) : State :=
  { st with heights := fun s => if s = t.suit then st.heights t.flipSuit.suit
      else if s = t.flipSuit.suit then st.heights t.suit else st.heights s }

theorem State.twinHeightSwap_heights_eq (t : Card) (st : State) (s : Suit) :
    (st.twinHeightSwap t).heights s =
      (if s = t.suit then st.heights t.flipSuit.suit
        else if s = t.flipSuit.suit then st.heights t.suit else st.heights s) := rfl

theorem State.twinHeightRel_heightSwap (t : Card) (st : State) :
    State.twinHeightRel t st (st.twinHeightSwap t) :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun s h1 h2 => by
    show st.heights s = (if s = t.suit then st.heights t.flipSuit.suit
      else if s = t.flipSuit.suit then st.heights t.suit else st.heights s)
    rw [if_neg h1, if_neg h2]⟩

/-- The cross-skew: the exchanged state with the twin suits' heights
exchanged — the correspondence between the two games while exactly one
twin has been stacked on each side. -/
def State.crossTwin (t : Card) (st : State) : State :=
  { st.swapTwin t with
    heights := fun s => if s = t.suit then st.heights t.flipSuit.suit
      else if s = t.flipSuit.suit then st.heights t.suit else st.heights s }

theorem State.crossTwin_heights_eq (t : Card) (st : State) (s : Suit) :
    (st.crossTwin t).heights s =
      (if s = t.suit then st.heights t.flipSuit.suit
        else if s = t.flipSuit.suit then st.heights t.suit else st.heights s) := rfl

theorem State.crossTwin_board (t : Card) (st : State) :
    (st.crossTwin t).board = st.board.mapByTwin t := by
  show (st.swapTwin t).board = _
  rw [swapTwin_board]

/-- The cross-skew factors: the height exchange commutes with the
local twin swap (they touch disjoint fields). -/
theorem State.crossTwin_eq (t : Card) (st : State) :
    st.crossTwin t = (st.twinHeightSwap t).swapTwin t := by
  apply state_ext
  · rfl
  · rw [State.crossTwin_board, swapTwin_board]
    rfl
  · rw [swapTwin_heights]
    rfl
  · rfl
  · rfl
  · rfl

/-- **The ortho step crosses**: an ortho move fires in the cross-skew
image under the relabeled move, landing on the cross-skew image of the
successor — the height-commute (chunk A) composed with the clean
mirror step. -/
theorem State.apply_crossTwin_ortho {t : Card} {S R : State} {m : Move}
    (hort : Move.orthoTwin t m = true) (hS : S.apply m = some R) :
    (S.crossTwin t).apply (m.swapTwin t) = some (R.crossTwin t) := by
  have hcl : Move.cleanTwin t m = true := Move.orthoTwin_clean hort
  obtain ⟨R', hfire, hrel⟩ := State.apply_twinHeightRel (S' := S.twinHeightSwap t)
    (State.twinHeightRel_heightSwap t S) hort hS
  have hpin : R' = R.twinHeightSwap t := by
    obtain ⟨hb, hd, hdp, hst, hds, hh⟩ := hrel
    have hsne : t.flipSuit.suit ≠ t.suit := fun h => Suit.flipPair_ne t.suit h
    have hS' := State.apply_ortho_preserves (t := t) (S := S.twinHeightSwap t) (R := R') hort hfire
    have hR := State.apply_ortho_preserves (t := t) (S := S) (R := R) hort hS
    apply state_ext
    · exact hd.symm
    · exact hb.symm
    · funext s
      by_cases h1 : s = t.suit
      · rw [h1, hS'.1, State.twinHeightSwap_heights_eq, State.twinHeightSwap_heights_eq,
          if_pos rfl, if_pos rfl]
        exact hR.2.symm
      · by_cases h2 : s = t.flipSuit.suit
        · rw [h2, hS'.2, State.twinHeightSwap_heights_eq, State.twinHeightSwap_heights_eq,
            if_neg hsne, if_pos rfl, if_neg hsne, if_pos rfl]
          exact hR.1.symm
        · rw [State.twinHeightSwap_heights_eq, if_neg h1, if_neg h2]
          exact (hh s h1 h2).symm
    · exact hdp.symm
    · exact hst.symm
    · exact hds.symm
  rw [hpin] at hfire
  have hstep := apply_swapTwin_clean_some (st := S.twinHeightSwap t) hcl hfire
  rw [← State.crossTwin_eq t S, ← State.crossTwin_eq t R] at hstep
  exact hstep

/-- The play-level crossing: an ortho play crosses wholesale. -/
theorem State.run_crossTwin_ortho (t : Card) : ∀ (st : State) (play : List Move),
    (∀ m ∈ play, Move.orthoTwin t m = true) → ∀ {C : State}, st.run play = some C →
    (st.crossTwin t).run (play.map (Move.swapTwin t)) = some (C.crossTwin t) := by
  intro st play
  revert st
  induction play with
  | nil => intro st _ C hrun; simp only [State.run] at hrun; obtain rfl := Option.some.inj hrun; rfl
  | cons m ms ih =>
      intro st hort C hrun
      simp only [List.map_cons, State.run] at hrun ⊢
      cases hS : st.apply m with
      | none => rw [hS] at hrun; exact absurd hrun (by simp)
      | some R =>
          rw [hS] at hrun
          rw [State.apply_crossTwin_ortho (hort m List.mem_cons_self) hS]
          exact ih R (fun m' hm' => hort m' (List.mem_cons_of_mem _ hm')) hrun

/-- The twin suits' heights are ortho-invariant along a whole play. -/
theorem State.run_ortho_preserves {t : Card} : ∀ (st : State) (play : List Move),
    (∀ m ∈ play, Move.orthoTwin t m = true) → ∀ {C : State}, st.run play = some C →
    C.heights t.suit = st.heights t.suit ∧
      C.heights t.flipSuit.suit = st.heights t.flipSuit.suit := by
  intro st play
  revert st
  induction play with
  | nil => intro st _ C hrun; simp only [State.run] at hrun; obtain rfl := Option.some.inj hrun; exact ⟨rfl, rfl⟩
  | cons m ms ih =>
      intro st hort C hrun
      simp only [State.run] at hrun
      cases hS : st.apply m with
      | none => rw [hS] at hrun; exact absurd hrun (by simp)
      | some R =>
          rw [hS] at hrun
          obtain ⟨h1, h2⟩ := State.apply_ortho_preserves (hort m List.mem_cons_self) hS
          obtain ⟨h3, h4⟩ := ih R (fun m' hm' => hort m' (List.mem_cons_of_mem _ hm')) hrun
          exact ⟨h3.trans h1, h4.trans h2⟩

/-- **The skew step**: the mirror's first twin stacking — in the
exchanged state the twin's stack fires at the twin's rung (the
alignment premise pins the other suit), landing on the skew state. -/
theorem State.apply_swapTwin_stack_flip {st : State} {t : Card} {β : Base}
    (htop : st.board.topOf (Sum.inr t) = none)
    (hβ : st.board.bottomOf t = some β)
    (hs₂ : st.heights t.flipSuit.suit = t.rank.toIdx) :
    (st.swapTwin t).apply (Move.pileStack t.flipSuit) = some (st.twinSkew t β) := by
  rw [apply_pileStack_iff]
  refine ⟨?_, β.swapTwin t, ?_, ?_, rfl⟩
  · rw [swapTwin_board, mapByTwin_topOf_flipSuit, htop]
    rfl
  · rw [swapTwin_board, mapByTwin_bottomOf_flipSuit st.board t hβ]
  · rw [Card.flipSuit_rank, swapTwin_heights]
    exact hs₂.symm

/-- The alignment conversion: under the two firings' shared rung, the
skew state IS the cross-skew of the source's stacking successor. -/
theorem State.twinSkew_eq_crossTwin {st B : State} {t : Card} {β : Base}
    (hshape : B = {st with board := st.board.detach β, heights := fun s => if s = t.suit then st.heights s + 1 else st.heights s})
    (halign : st.heights t.suit = st.heights t.flipSuit.suit) :
    st.twinSkew t β = B.crossTwin t := by
  have hsne : t.flipSuit.suit ≠ t.suit := fun h => Suit.flipPair_ne t.suit h
  have hBh : ∀ s, B.heights s = if s = t.suit then st.heights s + 1 else st.heights s := by
    intro s
    rw [hshape]
  apply state_ext
  · rw [hshape]
    rfl
  · rw [twinSkew_board, State.crossTwin_board, hshape]
  · funext s
    rw [State.crossTwin_heights_eq]
    show (if s = t.flipSuit.suit then (st.swapTwin t).heights s + 1 else (st.swapTwin t).heights s)
      = (if s = t.suit then B.heights t.flipSuit.suit
        else if s = t.flipSuit.suit then B.heights t.suit else B.heights s)
    rw [swapTwin_heights, hBh t.flipSuit.suit, hBh t.suit, hBh s]
    by_cases h1 : s = t.suit
    · rw [if_neg (fun h => hsne (h.symm.trans h1)), if_pos h1, if_neg hsne, h1]
      exact halign
    · by_cases h2 : s = t.flipSuit.suit
      · rw [if_pos h2, if_neg h1, if_pos h2, if_pos rfl, h2]
        omega
      · rw [if_neg h2, if_neg h1, if_neg h2, if_neg h1]
  · rw [hshape]
    rfl
  · rw [hshape]
    rfl
  · rw [hshape]
    rfl

/-- **The re-sync step**: the mirror's second twin stacking — at the
cross-skew state the source's twin fires at ITS rung (the rung read
through the exchange), and the landing is back on the plain exchanged
correspondence: the heights re-sync (both suits gained once on both
sides), so the tail conjugates again. -/
theorem State.apply_crossTwin_stack {C D : State} {t : Card} {β' : Base}
    (htop' : C.board.topOf (Sum.inr t.flipSuit) = none)
    (hβ' : C.board.bottomOf t.flipSuit = some β')
    (hrk' : t.flipSuit.rank.toIdx = C.heights t.flipSuit.suit)
    (halign₂ : C.heights t.suit = C.heights t.flipSuit.suit + 1)
    (hshape : D = {C with board := C.board.detach β', heights := fun s => if s = t.flipSuit.suit then C.heights s + 1 else C.heights s}) :
    (C.crossTwin t).apply (Move.pileStack t) = some (D.swapTwin t) := by
  have hsne : t.flipSuit.suit ≠ t.suit := fun h => Suit.flipPair_ne t.suit h
  have hDh : ∀ s, D.heights s = if s = t.flipSuit.suit then C.heights s + 1 else C.heights s := by
    intro s
    rw [hshape]
  rw [apply_pileStack_iff]
  refine ⟨?_, β'.swapTwin t, ?_, ?_, ?_⟩
  · rw [State.crossTwin_board, mapByTwin_topOf_flip, htop']
    rfl
  · rw [State.crossTwin_board]
    exact mapByTwin_bottomOf_flip C.board t hβ'
  · rw [State.crossTwin_heights_eq, if_pos rfl, ← Card.flipSuit_rank]
    exact hrk'
  · apply state_ext
    · rw [hshape]
      rfl
    · rw [swapTwin_board, State.crossTwin_board, mapByTwin_detach, hshape]
    · funext s
      show (D.swapTwin t).heights s = (if s = t.suit then (C.crossTwin t).heights s + 1
        else (C.crossTwin t).heights s)
      rw [swapTwin_heights, hDh s, State.crossTwin_heights_eq]
      by_cases h1 : s = t.suit
      · rw [h1, if_pos rfl, if_pos rfl, if_neg (Ne.symm hsne)]
        exact halign₂
      · by_cases h2 : s = t.flipSuit.suit
        · rw [h2, if_pos rfl, if_neg hsne, if_neg hsne, if_pos rfl]
          exact halign₂.symm
        · rw [if_neg h2, if_neg h1, if_neg h1, if_neg h2]
    · rw [hshape]
      rfl
    · rw [hshape]
      rfl
    · rw [hshape]
      rfl

/-- **The separated twin-swap replay (L1/O3, part i).**  If the source
game wins via a play whose twin foundation stackings are separated by
an ORTHO mid (no move whose legality reads the twin suits' heights),
the exchanged game is solvable: the clean prefix and tail mirror
verbatim, the first stacking lands the games in the cross-skew (each
side has stacked exactly one twin — the twin suits' heights exchanged),
the ortho mid crosses step-by-step, and the second stacking re-syncs
onto the plain exchanged correspondence.  The rung-exactness of
`pileStack` supplies the alignment: both firings pin their suit to the
shared rank, so each side's other suit is exactly at the rung its
mirror needs. -/
theorem solvable_swapTwin_separated {st : State} {t : Card} {p₁ mid p₂ : List Move}
    (hc₁ : ∀ m ∈ p₁, Move.cleanTwin t m = true)
    (hc₂ : ∀ m ∈ p₂, Move.cleanTwin t m = true)
    (ho : ∀ m ∈ mid, Move.orthoTwin t m = true)
    {W : State}
    (hrun : st.run (p₁ ++ [Move.pileStack t] ++ mid ++ [Move.pileStack t.flipSuit] ++ p₂)
      = some W)
    (hwin : W.isWin = true) :
    (st.swapTwin t).solvableFrom := by
  simp only [List.append_assoc] at hrun
  rw [run_split_bind st p₁
    ([Move.pileStack t] ++ (mid ++ ([Move.pileStack t.flipSuit] ++ p₂)))] at hrun
  cases hA : st.run p₁ with
  | none => rw [hA] at hrun; simp at hrun
  | some A =>
    rw [hA] at hrun
    have hrun1 : A.run ([Move.pileStack t] ++ (mid ++ ([Move.pileStack t.flipSuit] ++ p₂)))
      = some W := hrun
    rw [run_split_bind A [Move.pileStack t] (mid ++ ([Move.pileStack t.flipSuit] ++ p₂))] at hrun1
    simp only [State.run] at hrun1
    cases hB₀ : A.apply (Move.pileStack t) with
    | none => rw [hB₀] at hrun1; simp at hrun1
    | some B =>
        rw [hB₀] at hrun1
        have hrun2 : B.run (mid ++ ([Move.pileStack t.flipSuit] ++ p₂)) = some W := hrun1
        rw [run_split_bind B mid ([Move.pileStack t.flipSuit] ++ p₂)] at hrun2
        cases hC : B.run mid with
        | none => rw [hC] at hrun2; simp at hrun2
        | some C =>
            rw [hC] at hrun2
            have hrun3 : C.run ([Move.pileStack t.flipSuit] ++ p₂) = some W := hrun2
            rw [run_split_bind C [Move.pileStack t.flipSuit] p₂] at hrun3
            simp only [State.run] at hrun3
            cases hD₀ : C.apply (Move.pileStack t.flipSuit) with
            | none => rw [hD₀] at hrun3; simp at hrun3
            | some D =>
                rw [hD₀] at hrun3
                have hWD : D.run p₂ = some W := hrun3
                rw [apply_pileStack_iff] at hB₀
                obtain ⟨htop, β, hβ, hrk, hBshape⟩ := hB₀
                rw [apply_pileStack_iff] at hD₀
                obtain ⟨htop', β', hβ', hrk', hDshape⟩ := hD₀
                have hsne : t.flipSuit.suit ≠ t.suit := fun h => Suit.flipPair_ne t.suit h
                obtain ⟨hCt, hCt'⟩ := State.run_ortho_preserves B mid ho hC
                have hB' : B.heights t.flipSuit.suit = A.heights t.flipSuit.suit := by
                  rw [hBshape]
                  show (if t.flipSuit.suit = t.suit then A.heights t.flipSuit.suit + 1
                    else A.heights t.flipSuit.suit) = A.heights t.flipSuit.suit
                  rw [if_neg hsne]
                have hs₂ : A.heights t.flipSuit.suit = t.rank.toIdx := by
                  have h2 : t.flipSuit.rank.toIdx = C.heights t.flipSuit.suit := hrk'
                  rw [Card.flipSuit_rank, hCt', hB'] at h2
                  exact h2.symm
                have halign₁ : A.heights t.suit = A.heights t.flipSuit.suit := by
                  rw [hs₂, hrk]
                have halign₂ : C.heights t.suit = C.heights t.flipSuit.suit + 1 := by
                  have h1 : C.heights t.suit = A.heights t.suit + 1 := by
                    rw [hCt, hBshape]
                    show (if t.suit = t.suit then A.heights t.suit + 1 else A.heights t.suit)
                      = A.heights t.suit + 1
                    rw [if_pos rfl]
                  have h2 : C.heights t.flipSuit.suit = t.rank.toIdx := by
                    rw [← Card.flipSuit_rank]
                    exact hrk'.symm
                  rw [h1, h2, ← hrk]
                have hR₁ : (st.swapTwin t).run (p₁.map (Move.swapTwin t))
                    = some (A.swapTwin t) := by
                  rw [run_swapTwin_clean t st p₁ hc₁, hA]
                  rfl
                have hM₁ : (A.swapTwin t).apply (Move.pileStack t.flipSuit)
                    = some (B.crossTwin t) := by
                  rw [State.apply_swapTwin_stack_flip htop hβ hs₂]
                  rw [State.twinSkew_eq_crossTwin hBshape halign₁]
                have hS₁ : (A.swapTwin t).run [Move.pileStack t.flipSuit]
                    = some (B.crossTwin t) := by
                  simp only [State.run, hM₁]
                have hS₂ : (B.crossTwin t).run (mid.map (Move.swapTwin t))
                    = some (C.crossTwin t) := State.run_crossTwin_ortho t B mid ho hC
                have hS₃ : (C.crossTwin t).run [Move.pileStack t]
                    = some (D.swapTwin t) := by
                  simp only [State.run, State.apply_crossTwin_stack htop' hβ' hrk' halign₂ hDshape]
                have hS₄ : (D.swapTwin t).run (p₂.map (Move.swapTwin t))
                    = some (W.swapTwin t) := by
                  rw [run_swapTwin_clean t D p₂ hc₂, hWD]
                  rfl
                refine ⟨_, W.swapTwin t, run_append_some (run_append_some (run_append_some
                  (run_append_some hR₁ hS₁) hS₂) hS₃) hS₄, hwin⟩

/-- The ortho predicate is flip-dual (the two off-suits swap). -/
theorem Move.orthoTwin_flipSuit (t : Card) (m : Move) :
    Move.orthoTwin t.flipSuit m = Move.orthoTwin t m := by
  cases m with
  | draw | reveal _ | deckPile _ _ | pilePile _ _ => rfl
  | deckStack c | pileStack c | stackPile c _ =>
      simp only [Move.orthoTwin, Card.flipSuit_flipSuit, and_comm]

/-- **The separated twin-swap replay, backward.**  The same statement
with the twin stackings reversed (the mirror image of the forward
shape): the forward theorem at the exchanged state with the flipped
twin, whose exchange is the source by the involution. -/
theorem solvable_swapTwin_separated_back {st : State} {t : Card} {q₁ mid q₂ : List Move}
    (hc₁ : ∀ m ∈ q₁, Move.cleanTwin t m = true)
    (hc₂ : ∀ m ∈ q₂, Move.cleanTwin t m = true)
    (ho : ∀ m ∈ mid, Move.orthoTwin t m = true)
    {W : State}
    (hrun : (st.swapTwin t).run (q₁ ++ [Move.pileStack t.flipSuit] ++ mid
      ++ [Move.pileStack t] ++ q₂) = some W)
    (hwin : W.isWin = true) :
    st.solvableFrom := by
  have hc₁' : ∀ m ∈ q₁, Move.cleanTwin t.flipSuit m = true := by
    intro m hm
    rw [← Move.cleanTwin_flipSuit]
    exact hc₁ m hm
  have hc₂' : ∀ m ∈ q₂, Move.cleanTwin t.flipSuit m = true := by
    intro m hm
    rw [← Move.cleanTwin_flipSuit]
    exact hc₂ m hm
  have ho' : ∀ m ∈ mid, Move.orthoTwin t.flipSuit m = true := by
    intro m hm
    rw [Move.orthoTwin_flipSuit]
    exact ho m hm
  have hrun' : (st.swapTwin t).run (q₁ ++ [Move.pileStack t.flipSuit] ++ mid
    ++ [Move.pileStack t.flipSuit.flipSuit] ++ q₂) = some W := by
    rw [Card.flipSuit_flipSuit]
    exact hrun
  have h := solvable_swapTwin_separated (st := st.swapTwin t) (t := t.flipSuit)
    hc₁' hc₂' ho' hrun' hwin
  rw [State.swapTwin_flipSuit, State.swapTwin_swapTwin] at h
  exact h

/-- **The merge's landing is on the OTHER cargo's stack** — the
own-cargo side is self-landing at the SOURCE: a card of the own
cargo's run is above the passing twin (one step,
`mem_aboveOf_of_topOf`), hence above the run's root (walk
transitivity) — the source guard's territory.  The w15wfmerge probe's
z-side hland disjuncts are therefore vacuous. -/
theorem State.merge_own_landing_absurd {st : State} {t z c d : Card}
    (hztop : st.board.topOf (Sum.inr t) = some z)
    (hmerge : t ∈ st.board.aboveOf c)
    (hguard : d ∉ st.board.aboveOf c)
    (hd : d = z ∨ d ∈ st.board.aboveOf z) : False := by
  rcases hd with rfl | hd'
  · exact hguard (Board.aboveOf_trans hmerge (Board.mem_aboveOf_of_topOf hztop))
  · exact hguard (Board.aboveOf_trans hmerge (Board.aboveOf_sub_of_seated hztop hd'))

/-- **The cargo twin**: the two cargo cards are themselves a twin pair.
The fits pin both cargos to the twins' shared rank (one below, the
rungs) and to the shared other color; distinct cards of one rank-color
class are twins. -/
theorem State.cargo_flipSuit {st : State} {t z z' : Card}
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.flipSuit = true)
    (hztop : st.board.topOf (Sum.inr t) = some z)
    (hztop' : st.board.topOf (Sum.inr t.flipSuit) = some z') :
    z' = z.flipSuit := by
  obtain ⟨hrk, hcol⟩ := (canSitOn_eq z t).mp hfit
  obtain ⟨hrk', hcol'⟩ := (canSitOn_eq z' t.flipSuit).mp hfit'
  rw [Card.flipSuit_color] at hcol'
  have hfr : t.flipSuit.rank.toIdx = t.rank.toIdx :=
    congrArg Rank.toIdx (Card.flipSuit_rank t)
  have hr : z.rank = z'.rank := Rank.toIdx_inj (by omega)
  have hc : z.suit.color = z'.suit.color := by
    by_cases ht : t.suit.color = Color.red
    · rw [ht] at hcol hcol'
      rw [Color.eq_of_ne_red hcol, Color.eq_of_ne_red hcol']
    · have htb : t.suit.color = Color.black := Color.eq_of_ne_red ht
      rw [htb] at hcol hcol'
      rw [Color.eq_of_ne_black hcol, Color.eq_of_ne_black hcol']
  have hbb₁ : st.board.bottomOf z = some (Sum.inr t) := (Board.bottomOf_eq _ _ _).mpr hztop
  have hbb₁' : st.board.bottomOf z' = some (Sum.inr t.flipSuit) :=
    (Board.bottomOf_eq _ _ _).mpr hztop'
  have hne : z ≠ z' := by
    intro hcon
    have hbb : st.board.bottomOf z = st.board.bottomOf z' := by rw [hcon]
    rw [hbb₁, hbb₁'] at hbb
    exact Card.flipSuit_ne t (Sum.inr.inj (Option.some.inj hbb)).symm
  exact Card.flipSuit_eq_of_color_rank hc hr hne

/-- **The merge ply, root landing (route step 2a)**: at a riders-cleared
state (the seat over `z` bare), the exchanged game plays the mirror
merge — the same run, landed on the other cargo — and the successor's
board is the merge-successor's board, twin-swapped at the CARGO `z`;
every other field is the exchange's (the source's: the merge touches
only the board).  The fit is twin-blind (`canSitOn_flipSuit_right` at
the cargo twin, `cargo_flipSuit`); the self-landing guard is
`exchangeTwin_mirror_guard`; the board commutation is the per-seat
analysis — the four twin seats carry the exchanged/skewed values, the
landing seats the two attach-updates, and everywhere else the
inj-pinned z-freeness makes the relabeling fix the value.

NOTE (the climb-out's open item): the full `swapTwin z` also relabels
the deal piles and the stock, while this successor keeps the source's
deal — and board cards stay listed in the deal piles (the reveal keeps
it), so the state-level correspondence between the ply result and
`a₁.swapTwin z` has a deal reconciliation to do. -/
theorem State.exchange_merge_ply_root {st a₁ : State} {t z z' c : Card}
    (hztop : st.board.topOf (Sum.inr t) = some z)
    (hztop' : st.board.topOf (Sum.inr t.flipSuit) = some z')
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.flipSuit = true)
    (hnb : t ∉ st.board.aboveOf z ∧ t.flipSuit ∉ st.board.aboveOf z)
    (hnb' : t ∉ st.board.aboveOf z' ∧ t.flipSuit ∉ st.board.aboveOf z')
    (hmerge : t ∈ st.board.aboveOf c)
    (hct : c ≠ t ∧ c ≠ t.flipSuit)
    (hrid : st.board.topOf (Sum.inr z) = none)
    (hstep : st.apply (Move.pilePile c (Sum.inr z')) = some a₁) :
    ∃ M', (st.exchangeTwinCargo t).apply (Move.pilePile c (Sum.inr z)) = some M' ∧
      M'.board = a₁.board.mapByTwin z ∧ M'.deal = a₁.deal ∧ M'.heights = a₁.heights ∧
      M'.depths = a₁.depths ∧ M'.stock = a₁.stock ∧ M'.drawStep = a₁.drawStep := by
  rw [apply_pilePile_iff] at hstep
  obtain ⟨b₀, hbot, hne, hcmr, bd₁, hatt₁, ha₁⟩ := hstep
  have hcargo : z' = z.flipSuit := State.cargo_flipSuit hfit hfit' hztop hztop'
  have hzr : z.rank.toIdx + 1 = t.rank.toIdx := ((canSitOn_eq z t).mp hfit).1
  have hz'r : z'.rank.toIdx + 1 = t.flipSuit.rank.toIdx := ((canSitOn_eq z' _).mp hfit').1
  have hfr : t.flipSuit.rank.toIdx = t.rank.toIdx := congrArg Rank.toIdx (Card.flipSuit_rank t)
  have hzne : z ≠ t := fun h => by rw [h] at hzr; omega
  have hzne' : z ≠ t.flipSuit := fun h => by rw [h] at hzr; rw [hfr] at hzr; omega
  have hz'ne : z' ≠ t := fun h => by rw [h] at hz'r; omega
  have hz'ne' : z' ≠ t.flipSuit := fun h => by rw [h] at hz'r; omega
  have htz : t ≠ z := fun h => hzne h.symm
  have htz' : t ≠ z' := fun h => hz'ne h.symm
  have ht'z : t.flipSuit ≠ z := fun h => hzne' h.symm
  have ht'z' : t.flipSuit ≠ z' := fun h => hz'ne' h.symm
  have hzzone : z ≠ z' := fun h => by
    rw [h] at hcargo
    exact (Card.flipSuit_ne z') hcargo.symm
  have hcz : c ≠ z := by
    intro hcon
    rw [hcon] at hmerge
    exact hnb.1 hmerge
  have hcz' : c ≠ z' := by
    intro hcon
    rw [hcon] at hmerge
    exact hnb'.1 hmerge
  have hselfm := hcmr
  rw [State.canMoveRun, Bool.and_eq_true_iff] at hselfm
  obtain ⟨hcp, -⟩ := hselfm
  obtain ⟨hz'bare, -, hfitcz'⟩ := canPlace_inr_iff.mp hcp
  -- the base exclusions
  have hb₀z : b₀ ≠ Sum.inr z := by
    intro hcon
    have htc : st.board.topOf (Sum.inr z) = some c := (Board.bottomOf_eq _ _ _).mp (hcon ▸ hbot)
    rw [htc] at hrid
    exact absurd hrid (by simp)
  have hb₀t : b₀ ≠ Sum.inr t := by
    intro hcon
    have htc : st.board.topOf (Sum.inr t) = some c := (Board.bottomOf_eq _ _ _).mp (hcon ▸ hbot)
    rw [hztop] at htc
    exact hcz (Option.some.inj htc).symm
  have hb₀t' : b₀ ≠ Sum.inr t.flipSuit := by
    intro hcon
    have htc : st.board.topOf (Sum.inr t.flipSuit) = some c :=
      (Board.bottomOf_eq _ _ _).mp (hcon ▸ hbot)
    rw [hztop'] at htc
    exact hcz' (Option.some.inj htc).symm
  -- the seat-fixing equations
  have hfixz : Base.swapTwin t (Sum.inr z) = Sum.inr z :=
    Base.swapTwin_eq_self (fun h => hzne (Sum.inr.inj h)) (fun h => hzne' (Sum.inr.inj h))
  have hfixz' : Base.swapTwin t (Sum.inr z') = Sum.inr z' :=
    Base.swapTwin_eq_self (fun h => hz'ne (Sum.inr.inj h)) (fun h => hz'ne' (Sum.inr.inj h))
  have hfixb₀ : Base.swapTwin t b₀ = b₀ :=
    Base.swapTwin_eq_self hb₀t hb₀t'
  have hzsz : Base.swapTwin z (Sum.inr z') = Sum.inr z := by
    show Sum.inr (Card.swapTwin z z') = Sum.inr z
    rw [hcargo]
    exact congrArg Sum.inr (Card.swapTwin_self_right z)
  have hzs' : Base.swapTwin z (Sum.inr z) = Sum.inr z' := by
    show Sum.inr (Card.swapTwin z z) = Sum.inr z'
    rw [Card.swapTwin_self_left]
    exact (congrArg Sum.inr hcargo).symm
  have hselfzt : Base.swapTwin z (Sum.inr t) = Sum.inr t :=
    Base.swapTwin_eq_self (fun h => htz (Sum.inr.inj h)) (fun h => htz' (by
      rw [← hcargo] at h
      exact Sum.inr.inj h))
  have hselfzt' : Base.swapTwin z (Sum.inr t.flipSuit) = Sum.inr t.flipSuit :=
    Base.swapTwin_eq_self (fun h => ht'z (Sum.inr.inj h)) (fun h => ht'z' (by
      rw [← hcargo] at h
      exact Sum.inr.inj h))
  have hselfzb₀ : Base.swapTwin z b₀ = b₀ := by
    refine Base.swapTwin_eq_self hb₀z ?_
    intro h
    rw [← hcargo] at h
    exact hne h
  have hselftt : Base.swapTwin t (Sum.inr t) = Sum.inr t.flipSuit := by
    show Sum.inr (Card.swapTwin t t) = Sum.inr t.flipSuit
    exact congrArg Sum.inr (Card.swapTwin_self_left t)
  have hselftt' : Base.swapTwin t (Sum.inr t.flipSuit) = Sum.inr t := by
    show Sum.inr (Card.swapTwin t t.flipSuit) = Sum.inr t
    exact congrArg Sum.inr (Card.swapTwin_self_right t)
  -- the mirror's guard components
  have hbotM : (st.exchangeTwinCargo t).board.bottomOf c = some b₀ := by
    rw [State.exchangeTwinCargo_board, Board.bottomOf_exchangeTwin, hbot]
    simp [hfixb₀]
  have htopzM : (st.exchangeTwinCargo t).board.topOf (Sum.inr z) = none := by
    rw [State.exchangeTwinCargo_board, Board.exchangeTwin_topOf, hfixz]
    exact hrid
  have hvisM : (st.exchangeTwinCargo t).isVis z = true := by
    rw [State.isVis, State.exchangeTwinCargo_board, Board.bottomOf_exchangeTwin,
      (Board.bottomOf_eq _ _ _).mpr hztop]
    simp
  have hfitM : canSitOn c z = true := by
    have hzz : z = z'.flipSuit := by rw [hcargo, Card.flipSuit_flipSuit]
    rw [hzz, canSitOn_flipSuit_right]
    exact hfitcz'
  have hczf : c ≠ z.flipSuit := fun h => hcz' (by rw [← hcargo] at h; exact h)
  have hselfM : z ∉ (st.board.exchangeTwin t).aboveOf c :=
    State.exchangeTwin_mirror_guard hztop hztop' hfit hfit' hnb hnb' hmerge hct
  have hcmrM : (st.exchangeTwinCargo t).canMoveRun c (Sum.inr z) = true := by
    refine canMoveRun_inr_iff.mpr ⟨canPlace_inr_iff.mpr ⟨htopzM, hvisM, hfitM⟩, ?_⟩
    show ((st.board.exchangeTwin t).aboveOf c).contains z = false
    cases hcon : ((st.board.exchangeTwin t).aboveOf c).contains z with
    | false => rfl
    | true => exact absurd ((List.contains_iff_mem).mp hcon) hselfM
  -- the mirror's attach
  have htopzM' : ((st.board.exchangeTwin t).detach b₀).topOf (Sum.inr z) = none := by
    rw [Board.detach_topOf_ne _ _ _ (fun h => hb₀z h.symm)]
    exact htopzM
  have hbotM' : ((st.board.exchangeTwin t).detach b₀).bottomOf c = none := by
    have htc : (st.board.exchangeTwin t).topOf b₀ = some c := by
      rw [Board.exchangeTwin_topOf, hfixb₀]
      exact (Board.bottomOf_eq _ _ _).mp hbot
    exact Board.bottomOf_detach_self htc
  have hattne : ((st.board.exchangeTwin t).detach b₀).attach (Sum.inr z) c ≠ none :=
    (Board.attach_eq_some_iff _ _ _).mpr ⟨htopzM', hbotM'⟩
  have hattex : ∃ bdM, ((st.board.exchangeTwin t).detach b₀).attach (Sum.inr z) c = some bdM := by
    cases hattc : ((st.board.exchangeTwin t).detach b₀).attach (Sum.inr z) c with
    | none => exact (hattne hattc).elim
    | some bd => exact ⟨bd, rfl⟩
  obtain ⟨bdM, hatt⟩ := hattex
  refine ⟨{st.exchangeTwinCargo t with board := bdM},
    apply_pilePile_iff.mpr ⟨b₀, hbotM, hb₀z, hcmrM, bdM, hatt, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- the board commutation: bdM = bd₁.mapByTwin z
  have hL : ∀ (b' : Base), b' ≠ Sum.inr z → b' ≠ b₀ →
      bdM.topOf b' = st.board.topOf (b'.swapTwin t) := by
    intro b' h1 h2
    rw [Board.attach_topOf_ne _ _ _ hatt h1, Board.detach_topOf_ne _ _ _ h2,
      Board.exchangeTwin_topOf]
  have hR : ∀ (b' : Base), b' ≠ Sum.inr z' → b' ≠ b₀ →
      bd₁.topOf b' = st.board.topOf b' := by
    intro b' h1 h2
    rw [Board.attach_topOf_ne _ _ _ hatt₁ h1, Board.detach_topOf_ne _ _ _ h2]
  rw [ha₁]
  show bdM = bd₁.mapByTwin z
  apply Board.ext_topOf
  funext b'
  rw [mapByTwin_topOf]
  by_cases hz : b' = Sum.inr z
  · rw [hz, Board.attach_topOf _ _ _ hatt, hzs', Board.attach_topOf _ _ _ hatt₁]
    show some c = some (Card.swapTwin z c)
    rw [Card.swapTwin_of_ne hcz hczf]
  · by_cases hz' : b' = Sum.inr z'
    · rw [hz', hL (Sum.inr z') (fun h => hzzone (Sum.inr.inj h).symm)
        (fun h => hne h.symm), hfixz', hz'bare, hzsz,
        hR (Sum.inr z) (fun h => hzzone (Sum.inr.inj h)) (fun h => hb₀z h.symm), hrid]
      rfl
    · by_cases ht : b' = Sum.inr t
      · rw [ht, hL (Sum.inr t) (fun h => htz (Sum.inr.inj h))
          (fun h => hb₀t h.symm), hselftt, hselfzt,
          hR (Sum.inr t) (fun h => htz' (Sum.inr.inj h)) (fun h => hb₀t h.symm), hztop]
        show st.board.topOf (Sum.inr t.flipSuit) = some (Card.swapTwin z z)
        rw [Card.swapTwin_self_left, ← hcargo]
        exact hztop'
      · by_cases ht' : b' = Sum.inr t.flipSuit
        · rw [ht', hL (Sum.inr t.flipSuit) (fun h => ht'z (Sum.inr.inj h))
            (fun h => hb₀t' h.symm), hselftt', hselfzt',
            hR (Sum.inr t.flipSuit) (fun h => ht'z' (Sum.inr.inj h))
              (fun h => hb₀t' h.symm), hztop']
          show st.board.topOf (Sum.inr t) = some (Card.swapTwin z z')
          rw [show Card.swapTwin z z' = z from by rw [hcargo]; exact Card.swapTwin_self_right z]
          exact hztop
        · by_cases hb₀ : b' = b₀
          · rw [hb₀, Board.attach_topOf_ne _ _ _ hatt (fun h => hb₀z h),
              Board.detach_topOf, hselfzb₀,
              Board.attach_topOf_ne _ _ _ hatt₁ (fun h => hne h), Board.detach_topOf]
            rfl
          · -- everywhere else: both read through, and the value is z-free by inj
            have hfixt : b'.swapTwin t = b' := Base.swapTwin_eq_self ht ht'
            have hfixz2 : b'.swapTwin z = b' :=
              Base.swapTwin_eq_self hz (fun h => hz' (by rw [← hcargo] at h; exact h))
            rw [hL b' hz (fun h => hb₀ h), hfixt, hfixz2,
              hR b' hz' (fun h => hb₀ h)]
            cases hb : st.board.topOf b' with
            | none => rfl
            | some x =>
                show some x = some (Card.swapTwin z x)
                have hxz : x ≠ z := by
                  intro hcon
                  have hinj := st.board.inj (Sum.inr t) b' x (by rw [hztop, hcon]) hb
                  exact ht hinj.symm
                have hxz' : x ≠ z' := by
                  intro hcon
                  have hinj := st.board.inj (Sum.inr t.flipSuit) b' x (by rw [hztop', hcon]) hb
                  exact ht' hinj.symm
                rw [Card.swapTwin_of_ne hxz (fun h => hxz' (by rw [← hcargo] at h; exact h))]
  · rw [ha₁]; rfl
  · rw [ha₁]; rfl
  · rw [ha₁]; rfl
  · rw [ha₁]; rfl
  · rw [ha₁]; rfl
/-- **The twin-rooted merge — the [H] residual**: the frozen-phase
move whose root is the twin itself, landing on the other cargo's run —
the twin's own run (the cargo riding on top of it) merges onto the
other twin's stack, braiding `t` into `aboveOf z'` (the license dies
at the successor) while the same-move mirror is self-landing in the
exchanged state (the exchanged walk from `t` is the other twin's — it
contains the landing).

TODO(proof) **[H']**: the [H] crux at the rooted corner — the merge
bridge's shape (`solvable_of_exchange_merge` above) with the run
rooted AT the twin instead of reaching one; the gate (the witness
hunt at WF states) and the routes (piecewise bookkeeping, play
normalization) carry over verbatim.  The c = t' side is this lemma at
the flipped license (`twinLicensed_flipSuit`), closed by
`exchangeTwinCargo_pair`. -/
theorem State.solvable_of_exchange_merge_rooted {st a₁ : State} {t z' c : Card} {b : Base}
    (hwf : st.WF) (h : st.twinLicensed t)
    (hstep : st.apply (Move.pilePile c b) = some a₁) (hc : c = t)
    (hland : ∃ d, b = Sum.inr d ∧ d ∈ st.board.aboveOf z')
    (hsol : a₁.solvableFrom) :
    (st.exchangeTwinCargo t).solvableFrom := sorry

/-- One legal move in front of a winning play. -/
theorem State.solvable_step {S S' : State} {m : Move}
    (hstep : S.apply m = some S') (hsol : S'.solvableFrom) : S.solvableFrom := by
  obtain ⟨π, w, hrun, hwin⟩ := hsol
  refine ⟨m :: π, w, ?_, hwin⟩
  simp only [State.run, hstep]
  exact hrun

/-- **The forward simulation, generalized** (the g-simulation, g ∈
{id, e}): from a licensed winning state, the exchanged state wins —
the play induction over the frozen phase, with the state generalized
so the license re-seats at every step.  The case ledger per the
source play's head move (the mechanics: TwinExchange's six step
lemmas, the seventh here, the twin-rooted mirror above; the bridges:
the freedom-first and the two merges). -/
theorem State.solvable_exchangeTwinCargo_go :
    ∀ (play : List Move) (st : State) (t : Card),
    st.twinLicensed t → st.WF → (∃ w, st.run play = some w ∧ w.isWin = true) →
    (st.exchangeTwinCargo t).solvableFrom := by
  intro play
  induction play with
  | nil =>
      intro st t hlic hwf ⟨w, hrun, hwin⟩
      have hw : st = w := Option.some.inj hrun
      subst hw
      refine ⟨[], st.exchangeTwinCargo t, rfl, ?_⟩
      have hE : (st.exchangeTwinCargo t).isWin = st.isWin := rfl
      rw [hE]
      exact hwin
  | cons m ms ih =>
      intro st t hlic hwf ⟨w, hrun, hwin⟩
      cases hap : st.apply m with
      | none =>
          simp only [State.run, hap] at hrun
          exact absurd hrun (by simp)
      | some a₁ =>
          simp only [State.run, hap] at hrun
          have hsol₁ : a₁.solvableFrom := ⟨ms, w, hrun, hwin⟩
          obtain ⟨z, z', hvis, hvis', h₀, h₀', hfit, hfit', hnb, hnb'⟩ := hlic
          have hlicb : st.twinLicensed t :=
            ⟨z, z', hvis, hvis', h₀, h₀', hfit, hfit', hnb, hnb'⟩
          have hztop : st.board.topOf (Sum.inr t) = some z :=
            (Board.bottomOf_eq _ _ _).mp h₀
          have hztop' : st.board.topOf (Sum.inr t.flipSuit) = some z' :=
            (Board.bottomOf_eq _ _ _).mp h₀'
          have hzne : z ≠ t ∧ z ≠ t.flipSuit := Card.ne_pair_of_canSitOn hfit
          have hzne' : z' ≠ t ∧ z' ≠ t.flipSuit := by
            obtain ⟨ha, hb⟩ := Card.ne_pair_of_canSitOn hfit'
            exact ⟨fun h => hb (by rw [h, Card.flipSuit_flipSuit]), ha⟩
          cases m with
          | draw =>
              have hbd : a₁.board = st.board := by
                have happ := hap
                rw [apply_draw_iff] at happ
                obtain ⟨rfl⟩ := happ
                rfl
              exact State.solvable_step (State.exchangeTwinCargo_step_draw hap)
                (ih a₁ t (State.twinLicensed_congr hbd hlicb)
                  (apply_wf hwf _ _ hap) ⟨w, hrun, hwin⟩)
          | deckStack c =>
              have hbd : a₁.board = st.board := by
                have happ := hap
                rw [apply_deckStack_iff] at happ
                obtain ⟨-, -, rfl⟩ := happ
                rfl
              exact State.solvable_step (State.exchangeTwinCargo_step_deckStack hap)
                (ih a₁ t (State.twinLicensed_congr hbd hlicb)
                  (apply_wf hwf _ _ hap) ⟨w, hrun, hwin⟩)
          | deckPile c b =>
              have happ := hap
              rw [apply_deckPile_iff] at happ
              obtain ⟨hprev, hcp, bd, hatt, ha₁⟩ := happ
              have hmem : c ∈ st.stock.cards := by
                simp only [Cycle.prev] at hprev
                split at hprev
                · exact absurd hprev (by simp)
                · exact List.mem_iff_getElem?.mpr ⟨st.stock.cursor - 1, hprev⟩
              have hcvis : st.isVis c = false := by
                have hpos := Cycle.posOf_mem hmem
                cases hc : st.isVis c with
                | false => rfl
                | true =>
                    rw [hwf.vis_off_cycle c hc] at hpos
                    exact absurd hpos (by simp)
              have hct : c ≠ t ∧ c ≠ t.flipSuit := by
                constructor
                · intro hcon
                  rw [hcon] at hcvis
                  rw [hvis] at hcvis
                  exact absurd hcvis (by simp)
                · intro hcon
                  rw [hcon] at hcvis
                  rw [hvis'] at hcvis
                  exact absurd hcvis (by simp)
              have hbotc : st.board.bottomOf c = none :=
                (Board.attach_eq_some_iff _ _ _).mp (by rw [hatt]; simp) |>.2
              have hhid : ∀ a, c ∉ st.hidden a := by
                intro a' hcm
                have hpm : c ∈ st.deal.piles a' := List.take_subset _ _ hcm
                exact (Deal.piles_stock_disj hwf.deal_wf hpm
                  (hwf.stock_wf.2 c hmem)).elim
              have hbt : b ≠ Sum.inr t ∧ b ≠ Sum.inr t.flipSuit := by
                constructor
                · intro hcon
                  cases b with
                  | inl a => exact absurd hcon (by simp)
                  | inr d =>
                      obtain ⟨htopb, -, -⟩ := canPlace_inr_iff.mp hcp
                      rw [hcon, hztop] at htopb
                      simp at htopb
                · intro hcon
                  cases b with
                  | inl a => exact absurd hcon (by simp)
                  | inr d =>
                      obtain ⟨htopb, -, -⟩ := canPlace_inr_iff.mp hcp
                      rw [hcon, hztop'] at htopb
                      simp at htopb
              have hlic₁ : a₁.twinLicensed t := by
                rw [ha₁]
                exact State.twinLicensed_attach hwf hlicb hatt hct hbotc hhid hbt
              exact State.solvable_step (State.exchangeTwinCargo_step_deckPile h₀ h₀' hap)
                (ih a₁ t hlic₁ (apply_wf hwf _ _ hap) ⟨w, hrun, hwin⟩)
          | stackPile c b =>
              have happ := hap
              rw [apply_stackPile_iff] at happ
              obtain ⟨hrk, hcp, bd, hatt, ha₁⟩ := happ
              have hfound : c.rank.toIdx < st.heights c.suit := by omega
              have hfg := hwf.founds_gone c hfound
              have hcvis : st.isVis c = false := hfg.1
              have hct : c ≠ t ∧ c ≠ t.flipSuit := by
                constructor
                · intro hcon
                  rw [hcon] at hcvis
                  rw [hvis] at hcvis
                  exact absurd hcvis (by simp)
                · intro hcon
                  rw [hcon] at hcvis
                  rw [hvis'] at hcvis
                  exact absurd hcvis (by simp)
              have hbotc : st.board.bottomOf c = none := by
                cases hh : st.board.bottomOf c with
                | none => rfl
                | some β =>
                    have hc2 : (st.board.bottomOf c).isSome = false := hcvis
                    rw [hh] at hc2
                    simp at hc2
              have hhid : ∀ a, c ∉ st.hidden a := fun a => hfg.2.2 a
              have hbt : b ≠ Sum.inr t ∧ b ≠ Sum.inr t.flipSuit := by
                constructor
                · intro hcon
                  cases b with
                  | inl a => exact absurd hcon (by simp)
                  | inr d =>
                      obtain ⟨htopb, -, -⟩ := canPlace_inr_iff.mp hcp
                      rw [hcon, hztop] at htopb
                      simp at htopb
                · intro hcon
                  cases b with
                  | inl a => exact absurd hcon (by simp)
                  | inr d =>
                      obtain ⟨htopb, -, -⟩ := canPlace_inr_iff.mp hcp
                      rw [hcon, hztop'] at htopb
                      simp at htopb
              have hlic₁ : a₁.twinLicensed t := by
                rw [ha₁]
                exact State.twinLicensed_attach hwf hlicb hatt hct hbotc hhid hbt
              exact State.solvable_step (State.exchangeTwinCargo_step_stackPile h₀ h₀' hap)
                (ih a₁ t hlic₁ (apply_wf hwf _ _ hap) ⟨w, hrun, hwin⟩)
          | reveal c =>
              have hlic₁ : a₁.twinLicensed t :=
                State.twinLicensed_apply_reveal hwf hlicb hap
              exact State.solvable_step
                (State.exchangeTwinCargo_step_reveal hvis hvis' h₀ h₀' hap)
                (ih a₁ t hlic₁ (apply_wf hwf _ _ hap) ⟨w, hrun, hwin⟩)
          | pileStack c =>
              by_cases hcz : c = z
              · rw [hcz] at hap
                exact State.solvable_of_exchange_pileStack hfit hvis' h₀ h₀' hfit' hnb' hap
                  hsol₁
              · by_cases hcz' : c = z'
                · rw [hcz'] at hap
                  have hvisF : st.isVis (t.flipSuit).flipSuit = true := by
                    rw [Card.flipSuit_flipSuit]; exact hvis
                  have h₀F : st.board.bottomOf z = some (Sum.inr (t.flipSuit).flipSuit) := by
                    rw [Card.flipSuit_flipSuit]; exact h₀
                  have hfitF : canSitOn z (t.flipSuit).flipSuit = true := by
                    rw [Card.flipSuit_flipSuit]; exact hfit
                  have hnbF : (t.flipSuit).flipSuit ∉ st.board.aboveOf z := by
                    intro hmem
                    rw [Card.flipSuit_flipSuit] at hmem
                    exact hnb.1 hmem
                  have hres := State.solvable_of_exchange_pileStack (st := st) (z := z')
                    (z' := z) (t := t.flipSuit) hfit' hvisF h₀' h₀F hfitF
                    ⟨hnb.2, hnbF⟩ hap hsol₁
                  rw [State.exchangeTwinCargo_pair] at hres
                  exact hres
                · have happ := hap
                  rw [apply_pileStack_iff] at happ
                  obtain ⟨htopc, -, -, -, -⟩ := happ
                  have hct : c ≠ t ∧ c ≠ t.flipSuit := by
                    constructor
                    · intro hcon
                      rw [hcon, hztop] at htopc
                      simp at htopc
                    · intro hcon
                      rw [hcon, hztop'] at htopc
                      simp at htopc
                  have hlic₁ : a₁.twinLicensed t :=
                    State.twinLicensed_apply_pileStack hvis hvis' h₀ h₀' hfit hfit' hnb hnb'
                      hct ⟨hcz, hcz'⟩ hap
                  exact State.solvable_step
                    (State.exchangeTwinCargo_step_pileStack h₀ h₀' ⟨hcz, hcz'⟩ hct hap)
                    (ih a₁ t hlic₁ (apply_wf hwf _ _ hap) ⟨w, hrun, hwin⟩)
          | pilePile c b =>
              by_cases hcz : c = z
              · -- the seat lock: the cargo's own run cannot leave pre-freedom
                rw [hcz] at hap
                have happ := hap
                rw [apply_pilePile_iff] at happ
                obtain ⟨b₀, hbot, hne, hcmr, bd, hatt, rfl⟩ := happ
                simp only [State.canMoveRun, Bool.and_eq_true_iff] at hcmr
                obtain ⟨hcp, -⟩ := hcmr
                have hb₀ : b₀ = Sum.inr t := Option.some.inj (hbot.symm.trans h₀)
                rw [hb₀] at hne
                cases b with
                | inl a =>
                    obtain ⟨-, hking⟩ := canPlace_inl_iff.mp hcp
                    obtain ⟨hrk, -⟩ := (canSitOn_eq z t).mp hfit
                    rw [hking] at hrk
                    have hk : Rank.king.toIdx = 12 := rfl
                    have hlt := Rank.toIdx_lt t.rank
                    omega
                | inr d =>
                    obtain ⟨-, -, hczd⟩ := canPlace_inr_iff.mp hcp
                    rcases canSitOn_hosts_are_twins hfit hczd with rfl | rfl
                    · exact (hne rfl).elim
                    · obtain ⟨htopb, -, -⟩ := canPlace_inr_iff.mp hcp
                      rw [hztop'] at htopb
                      simp at htopb
              · by_cases hcz' : c = z'
                · rw [hcz'] at hap
                  have happ := hap
                  rw [apply_pilePile_iff] at happ
                  obtain ⟨b₀, hbot, hne, hcmr, bd, hatt, rfl⟩ := happ
                  simp only [State.canMoveRun, Bool.and_eq_true_iff] at hcmr
                  obtain ⟨hcp, -⟩ := hcmr
                  have hb₀ : b₀ = Sum.inr t.flipSuit :=
                    Option.some.inj (hbot.symm.trans h₀')
                  rw [hb₀] at hne
                  cases b with
                  | inl a =>
                      obtain ⟨-, hking⟩ := canPlace_inl_iff.mp hcp
                      obtain ⟨hrk, -⟩ := (canSitOn_eq z' t.flipSuit).mp hfit'
                      rw [hking] at hrk
                      have hk : Rank.king.toIdx = 12 := rfl
                      have hlt := Rank.toIdx_lt t.flipSuit.rank
                      omega
                  | inr d =>
                      obtain ⟨-, -, hczd⟩ := canPlace_inr_iff.mp hcp
                      rcases canSitOn_hosts_are_twins hfit' hczd with rfl | rfl
                      · exact (hne rfl).elim
                      · obtain ⟨htopb, -, -⟩ := canPlace_inr_iff.mp hcp
                        rw [Card.flipSuit_flipSuit] at htopb
                        rw [hztop] at htopb
                        simp at htopb
                · by_cases hct : c = t
                  · -- the twin-rooted runs
                    rw [hct] at hap
                    have happ := hap
                    rw [apply_pilePile_iff] at happ
                    obtain ⟨b₀, hbot, hne, hcmr, bd, hatt, ha₁⟩ := happ
                    simp only [State.canMoveRun, Bool.and_eq_true_iff] at hcmr
                    obtain ⟨hcp, hselfm⟩ := hcmr
                    cases b with
                    | inl a =>
                        have hselfE : ∀ d, Sum.inl a = Sum.inr d →
                            d ∉ (st.board.exchangeTwin t).aboveOf t :=
                          fun d hd => absurd hd (by simp)
                        have hland : ∀ d, Sum.inl a = Sum.inr d →
                            d ∉ st.board.aboveOf z ∧ d ∉ st.board.aboveOf z' :=
                          fun d hd => absurd hd (by simp)
                        have hstepE := State.exchangeTwinCargo_step_pilePile_root h₀ h₀' hfit
                          hfit' hap rfl hselfE
                        have hlic₁ : a₁.twinLicensed t :=
                          State.twinLicensed_apply_pilePile_root hvis' h₀ h₀' hfit hfit'
                            hnb hnb' hap rfl hland
                        exact State.solvable_step hstepE
                          (ih a₁ t hlic₁ (apply_wf hwf _ _ hap) ⟨w, hrun, hwin⟩)
                    | inr d =>
                        have hselfgt : d ∉ st.board.aboveOf t := by
                          intro hmem
                          have hc : (st.board.aboveOf t).contains d = true :=
                            (List.contains_iff_mem).mpr hmem
                          have hselfm' : (!((st.board.aboveOf t).contains d)) = true :=
                            hselfm
                          rw [hc] at hselfm'
                          simp at hselfm'
                        -- seed containment: the own cargo's run rides inside
                        have hdz : d ∉ st.board.aboveOf z := fun hmem =>
                          hselfgt (Board.aboveOf_sub_of_seated hztop hmem)
                        obtain ⟨-, -, hfitd⟩ := canPlace_inr_iff.mp hcp
                        have hdzne : d ≠ z := by
                          intro hcon
                          rw [hcon] at hfitd
                          exact (canSitOn_antisymm hfit) hfitd
                        have hdz'ne : d ≠ z' := by
                          intro hcon
                          obtain ⟨hrk, -⟩ := (canSitOn_eq t d).mp hfitd
                          obtain ⟨hrk', -⟩ := (canSitOn_eq z' t.flipSuit).mp hfit'
                          rw [Card.flipSuit_rank] at hrk'
                          rw [hcon] at hrk
                          omega
                        by_cases hdz' : d ∈ st.board.aboveOf z'
                        · -- the twin-rooted merge
                          exact State.solvable_of_exchange_merge_rooted hwf hlicb hap rfl
                            ⟨d, rfl, hdz'⟩ hsol₁
                        · have hselfE : d ∉ (st.board.exchangeTwin t).aboveOf t := by
                            intro hmem
                            rcases Board.aboveOf_exchangeTwin_bound hztop hztop'
                              ⟨hzne.1, hzne.2, hzne'.1, hzne'.2⟩ hnb hnb' hmem
                              with h | h | h | h | h
                            · exact hselfgt h
                            · exact hdzne h
                            · exact hdz'ne h
                            · exact hdz h
                            · exact absurd h hdz'
                          have hstepE := State.exchangeTwinCargo_step_pilePile_root h₀ h₀'
                            hfit hfit' hap rfl
                            (fun d' hd' => by
                              rw [show d' = d from Sum.inr.inj hd'.symm]
                              exact hselfE)
                          have hland : ∀ d', (Sum.inr d : Base) = Sum.inr d' →
                              d' ∉ st.board.aboveOf z ∧ d' ∉ st.board.aboveOf z' := by
                            intro d' hd'
                            rw [show d' = d from Sum.inr.inj hd'.symm]
                            exact ⟨hdz, hdz'⟩
                          have hlic₁ : a₁.twinLicensed t :=
                            State.twinLicensed_apply_pilePile_root hvis' h₀ h₀' hfit
                              hfit' hnb hnb' hap rfl hland
                          exact State.solvable_step hstepE
                            (ih a₁ t hlic₁ (apply_wf hwf _ _ hap) ⟨w, hrun, hwin⟩)
                  · by_cases hct' : c = t.flipSuit
                    · -- the twin-rooted runs, the flipped pair
                      rw [hct'] at hap
                      obtain ⟨zf, zf', hvisf, hvisf', h₀f, h₀f', hfitf, hfitf', hnbf, hnbf'⟩ :=
                        State.twinLicensed_flipSuit hlicb
                      have hlicfb : st.twinLicensed t.flipSuit :=
                        ⟨zf, zf', hvisf, hvisf', h₀f, h₀f', hfitf, hfitf', hnbf, hnbf'⟩
                      have hztopf : st.board.topOf (Sum.inr t.flipSuit) = some zf :=
                        (Board.bottomOf_eq _ _ _).mp h₀f
                      have hztopf' : st.board.topOf (Sum.inr (t.flipSuit).flipSuit)
                          = some zf' := (Board.bottomOf_eq _ _ _).mp h₀f'
                      have hnef : zf ≠ t.flipSuit ∧ zf ≠ (t.flipSuit).flipSuit :=
                        Card.ne_pair_of_canSitOn hfitf
                      have hnef' : zf' ≠ (t.flipSuit).flipSuit ∧
                          zf' ≠ (t.flipSuit).flipSuit.flipSuit :=
                        Card.ne_pair_of_canSitOn hfitf'
                      have hzf't : zf' ≠ t.flipSuit := by
                        intro hcon
                        obtain ⟨-, hb⟩ := hnef'
                        exact hb (by rw [hcon, Card.flipSuit_flipSuit])
                      have happ := hap
                      rw [apply_pilePile_iff] at happ
                      obtain ⟨b₀, hbot, hne, hcmr, bd, hatt, ha₁⟩ := happ
                      simp only [State.canMoveRun, Bool.and_eq_true_iff] at hcmr
                      obtain ⟨hcp, hselfm⟩ := hcmr
                      cases b with
                      | inl a =>
                          have hselfE : ∀ d, Sum.inl a = Sum.inr d →
                              d ∉ (st.board.exchangeTwin t.flipSuit).aboveOf t.flipSuit :=
                            fun d hd => absurd hd (by simp)
                          have hland : ∀ d, Sum.inl a = Sum.inr d →
                              d ∉ st.board.aboveOf zf ∧ d ∉ st.board.aboveOf zf' :=
                            fun d hd => absurd hd (by simp)
                          have hstepE := State.exchangeTwinCargo_step_pilePile_root h₀f h₀f'
                            hfitf hfitf' hap rfl hselfE
                          have hlic₁ : a₁.twinLicensed t.flipSuit :=
                            State.twinLicensed_apply_pilePile_root hvisf' h₀f h₀f'
                              hfitf hfitf' hnbf hnbf' hap rfl hland
                          have hres := State.solvable_step hstepE
                            (ih a₁ t.flipSuit hlic₁ (apply_wf hwf _ _ hap) ⟨w, hrun, hwin⟩)
                          rw [← State.exchangeTwinCargo_pair]
                          exact hres
                      | inr d =>
                          have hselfgt : d ∉ st.board.aboveOf t.flipSuit := by
                            intro hmem
                            have hc : (st.board.aboveOf t.flipSuit).contains d = true :=
                              (List.contains_iff_mem).mpr hmem
                            have hselfm' :
                                (!((st.board.aboveOf t.flipSuit).contains d)) = true := hselfm
                            rw [hc] at hselfm'
                            simp at hselfm'
                          -- seed containment: the own cargo's run rides inside
                          have hdzf : d ∉ st.board.aboveOf zf := fun hmem =>
                            hselfgt (Board.aboveOf_sub_of_seated hztopf hmem)
                          obtain ⟨-, -, hfitd⟩ := canPlace_inr_iff.mp hcp
                          by_cases hdzf' : d ∈ st.board.aboveOf zf'
                          · -- the twin-rooted merge, the flipped pair
                            have hres := State.solvable_of_exchange_merge_rooted hwf hlicfb
                              hap rfl ⟨d, rfl, hdzf'⟩ hsol₁
                            rw [State.exchangeTwinCargo_pair] at hres
                            exact hres
                          · have hdzfne : d ≠ zf := by
                              intro hcon
                              rw [hcon] at hfitd
                              exact (canSitOn_antisymm hfitf) hfitd
                            have hdzf'ne : d ≠ zf' := by
                              intro hcon
                              obtain ⟨hrk, -⟩ := (canSitOn_eq t.flipSuit d).mp hfitd
                              obtain ⟨hrk', -⟩ :=
                                (canSitOn_eq zf' (t.flipSuit).flipSuit).mp hfitf'
                              rw [hcon, Card.flipSuit_rank] at hrk
                              rw [Card.flipSuit_flipSuit] at hrk'
                              omega
                            have hselfE : d ∉ (st.board.exchangeTwin t.flipSuit).aboveOf
                                t.flipSuit := by
                              intro hmem
                              rcases Board.aboveOf_exchangeTwin_bound hztopf hztopf'
                                ⟨hnef.1, hnef.2, hzf't, hnef'.1⟩ hnbf hnbf' hmem
                                with h | h | h | h | h
                              · exact hselfgt h
                              · exact hdzfne h
                              · exact hdzf'ne h
                              · exact hdzf h
                              · exact absurd h hdzf'
                            have hstepE := State.exchangeTwinCargo_step_pilePile_root h₀f
                              h₀f' hfitf hfitf' hap rfl
                              (fun d' hd' => by
                                rw [show d' = d from Sum.inr.inj hd'.symm]
                                exact hselfE)
                            have hland : ∀ d', (Sum.inr d : Base) = Sum.inr d' →
                                d' ∉ st.board.aboveOf zf ∧ d' ∉ st.board.aboveOf zf' := by
                              intro d' hd'
                              rw [show d' = d from Sum.inr.inj hd'.symm]
                              exact ⟨hdzf, hdzf'⟩
                            have hlic₁ : a₁.twinLicensed t.flipSuit :=
                              State.twinLicensed_apply_pilePile_root hvisf' h₀f h₀f'
                                hfitf hfitf' hnbf hnbf' hap rfl hland
                            have hres := State.solvable_step hstepE
                              (ih a₁ t.flipSuit hlic₁ (apply_wf hwf _ _ hap)
                                ⟨w, hrun, hwin⟩)
                            rw [← State.exchangeTwinCargo_pair]
                            exact hres
                    · -- off the pair: merge or clean
                      by_cases hmerge : t ∈ st.board.aboveOf c ∨
                        t.flipSuit ∈ st.board.aboveOf c
                      · -- the merge: split on the landing (off-cargo
                        -- landings mirror — session-7's correction)
                        cases b with
                        | inl a =>
                            have hoff : ∀ d, Sum.inl a = Sum.inr d →
                                d ≠ z ∧ d ≠ z' ∧ d ∉ st.board.aboveOf z ∧
                                  d ∉ st.board.aboveOf z' :=
                              fun d hd => absurd hd (by simp)
                            have hlic₁ : a₁.twinLicensed t :=
                              State.twinLicensed_apply_pilePile_passing hvis hvis' h₀ h₀'
                                hfit hfit' hnb hnb' ⟨hct, hct'⟩ ⟨hcz, hcz'⟩ hoff hap
                            exact State.solvable_step
                              (State.exchangeTwinCargo_step_pilePile_passing h₀ h₀'
                                hfit hfit' hnb hnb' ⟨hcz, hcz'⟩ hoff hap)
                              (ih a₁ t hlic₁ (apply_wf hwf _ _ hap) ⟨w, hrun, hwin⟩)
                        | inr d =>
                            by_cases hland : d = z ∨ d ∈ st.board.aboveOf z ∨
                              d = z' ∨ d ∈ st.board.aboveOf z'
                            · exact State.solvable_of_exchange_merge hwf hlicb hap hmerge
                                ⟨d, rfl, hland⟩ hsol₁
                            · have hoff : ∀ d', (Sum.inr d : Base) = Sum.inr d' →
                                d' ≠ z ∧ d' ≠ z' ∧ d' ∉ st.board.aboveOf z ∧
                                  d' ∉ st.board.aboveOf z' := by
                                intro d' hd'
                                have hdeq : d' = d := Sum.inr.inj hd'.symm
                                rw [hdeq]
                                exact ⟨fun h => hland (Or.inl h),
                                  fun h => hland (Or.inr (Or.inr (Or.inl h))),
                                  fun h => hland (Or.inr (Or.inl h)),
                                  fun h => hland (Or.inr (Or.inr (Or.inr h)))⟩
                              have hlic₁ : a₁.twinLicensed t :=
                                State.twinLicensed_apply_pilePile_passing hvis hvis' h₀ h₀'
                                  hfit hfit' hnb hnb' ⟨hct, hct'⟩ ⟨hcz, hcz'⟩ hoff hap
                              exact State.solvable_step
                                (State.exchangeTwinCargo_step_pilePile_passing h₀ h₀'
                                  hfit hfit' hnb hnb' ⟨hcz, hcz'⟩ hoff hap)
                                (ih a₁ t hlic₁ (apply_wf hwf _ _ hap) ⟨w, hrun, hwin⟩)
                      · have hclean : t ∉ st.board.aboveOf c ∧
                          t.flipSuit ∉ st.board.aboveOf c :=
                          ⟨fun h => hmerge (Or.inl h), fun h => hmerge (Or.inr h)⟩
                        have happ := hap
                        rw [apply_pilePile_iff] at happ
                        obtain ⟨b₀, hbot, hne, hcmr, bd, hatt, ha₁⟩ := happ
                        have hlic₁ : a₁.twinLicensed t :=
                          State.twinLicensed_apply_pilePile hvis hvis' h₀ h₀' hfit hfit'
                            hnb hnb' ⟨hct, hct'⟩ ⟨hcz, hcz'⟩ hclean hap
                        exact State.solvable_step
                          (State.exchangeTwinCargo_step_pilePile h₀ h₀' ⟨hcz, hcz'⟩
                            ⟨hct, hct'⟩ hclean hap)
                          (ih a₁ t hlic₁ (apply_wf hwf _ _ hap) ⟨w, hrun, hwin⟩)

/-- **The forward simulation** (the g-simulation, g ∈ {id, e}): from a
licensed winning state, the exchanged state wins — the play induction
over the frozen phase (`solvable_exchangeTwinCargo_go`, the state
generalized so the license re-seats at every step).  Per the source
play's head move: the freedom `pileStack`s close by the freedom-first
bridge (the z'-side at the flipped license, closed by
`exchangeTwinCargo_pair`); `pilePile z`/`pilePile z'` are impossible
(the seat lock: `canSitOn_hosts_are_twins` + the occupied seats + the
rank gap kills the anchor arm); the twin-rooted `pilePile`s mirror by
`exchangeTwinCargo_step_pilePile_root` (the self-landing guard
transfers by `aboveOf_exchangeTwin_bound`, the landing excluded from
the own cargo's run by seed containment) or close by the rooted merge
(`solvable_of_exchange_merge_rooted`, the [H] residual); everything
else cites the seven clean-step mechanics with their license
transfers; a terminal win transfers because `isWin` is
exchange-invariant (heights `rfl`). -/
theorem State.solvable_exchangeTwinCargo {st : State} {t : Card}
    (hwf : st.WF) (h : st.twinLicensed t) (hsol : st.solvableFrom) :
    (st.exchangeTwinCargo t).solvableFrom := by
  obtain ⟨π, w, hrun, hwin⟩ := hsol
  exact State.solvable_exchangeTwinCargo_go π st t h hwf ⟨w, hrun, hwin⟩

/-- **The row's iff from the forward direction** — PROVEN modulo the
simulation: the other direction is the forward simulation at the
exchanged state (the involution returns it to `st`, the license
transfers by `twinLicensed_exchangeTwinCargo`, WF descends by
`wf_exchangeTwinCargo_of_twinLicensed`). -/
theorem State.solvable_iff_exchangeTwinCargo {st : State} {t : Card}
    (hwf : st.WF) (h : st.twinLicensed t) :
    (st.exchangeTwinCargo t).solvableFrom ↔ st.solvableFrom := by
  constructor
  · intro hsol
    have hwf' : (st.exchangeTwinCargo t).WF :=
      State.wf_exchangeTwinCargo_of_twinLicensed hwf h
    have h' : (st.exchangeTwinCargo t).twinLicensed t :=
      State.twinLicensed_exchangeTwinCargo h
    have hinv : (st.exchangeTwinCargo t).exchangeTwinCargo t = st :=
      State.exchangeTwinCargo_exchangeTwinCargo st t
    rw [← hinv]
    exact State.solvable_exchangeTwinCargo hwf' h' hsol
  · exact State.solvable_exchangeTwinCargo hwf h

/-- **The general row, licensed form**: exactly TwinExchange's
`solvable_cargoTwin_exchange` premise bundle (TwinExchange.lean:1267),
with the license as the carrier.  PROVEN modulo the forward
simulation. -/
theorem State.solvable_cargoTwin_exchange_licensed {st : State} {z z' t : Card}
    (hwf : st.WF)
    (hvis : st.isVis t = true) (hvis' : st.isVis t.flipSuit = true)
    (h₀ : st.board.bottomOf z = some (Sum.inr t))
    (h₀' : st.board.bottomOf z' = some (Sum.inr t.flipSuit))
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.flipSuit = true)
    (hnb : t ∉ st.board.aboveOf z ∧ t.flipSuit ∉ st.board.aboveOf z)
    (hnb' : t ∉ st.board.aboveOf z' ∧ t.flipSuit ∉ st.board.aboveOf z') :
    (st.exchangeTwinCargo t).solvableFrom ↔ st.solvableFrom :=
  State.solvable_iff_exchangeTwinCargo hwf
    ⟨z, z', hvis, hvis', h₀, h₀', hfit, hfit', hnb, hnb'⟩
