import Klondike.Move
import Klondike.Tactics

/-!
# The separation discipline: `Frame`, `reads`, `writes`, the two laws

THE THEORY — the frame layer, sitting between `Move.comps` (Commutation's
four components) and `Move.touch` (its state-dependent base/card sets):
the state's semantic fields as a `Frame` enum, with the stock SPLIT
(cards vs cursor — `posOf` reads cards only, `prev`/`dealOnce`/`removeAt`
read both) and the foundation heights SPLIT PER SUIT (a `pileStack c`
reads and writes only `c`'s cell).  Each move's `reads`/`writes` are
PURE functions of the move.  Two master laws, each proven once:

* **Frame congruence** (`frame_congr`, `frame_congr_none`): two states
  agreeing on a move's read-frames get the same verdict, and successors
  agreeing on every frame the sources agreed on.  Combined with
  `frame_invar` (unread frames are inherited), this is the whole
  blindness kit.
* **Disjoint-frames commute** (`commute_of_disjoint_frames`):
  read/write-disjoint moves commute — both orders land on the same
  state, no legality hypotheses.  This subsumes `commute_of_compsDisjoint`
  and DERIVES the `hnc` guard of `commute_of_disjoint_touch` (the
  non-consuming condition is exactly "no stock frames in reads"; see
  `deal_commutes_nonStock_frame`).

THE HONEST REFINEMENT STORY (why reads/writes are pure and what that
costs).  A pure move-to-frames function cannot see *where* inside a
frame a move reads: `deckPile`'s legality reads the waste top (so the
stock frames are in `reads` even though the interesting write is the
splice), `canPlace`'s `isVis` reads a card's seat — an arbitrary board
cell.  The sub-frame refinement — board cells with card-witnessed
reads — is the touch layer's territory (`Move.touch`, Commutation) and
the per-card specialization (`Move.seatsOrReads`, this file): the frame
layer deliberately stops at the granularity where a move's reads and
writes stay state-independent.  What that buys: the sixteen fine
`comm_*` pairs that interact INSIDE the board frame (all but the two
`deckStack` pairs — see `comm_deckStack_pileStack_frame`) do not fall
out here; the boundary is recorded at the file's end.
-/

/-- The state's semantic fields at the granularity the moves separate
on.  Not split: the board (per-base writes and per-card seat reads are
state-dependent — the touch layer's), `depths`/`deal` per pile
(`reveal`'s write anchor is `pileOfTopHidden`-chosen). -/
inductive Frame where
  /-- The fixed deal (never written). -/
  | deal
  /-- The visible tableau matching (atomic — see the header). -/
  | board
  /-- The foundation height of one suit. -/
  | heightsOf (s : Suit)
  /-- The hidden boundary depths. -/
  | depths
  /-- The stock's remaining cards. -/
  | stockCards
  /-- The stock's draw cursor (read apart from the cards). -/
  | stockCursor
  /-- The game's draw step. -/
  | drawStep
  deriving DecidableEq, Repr

/-- Two states agree on `f` when their `f`-projections coincide. -/
def Frame.agree (f : Frame) (st st' : State) : Prop :=
  match f with
  | .deal => st.deal = st'.deal
  | .board => st.board = st'.board
  | .heightsOf s => st.heights s = st'.heights s
  | .depths => st.depths = st'.depths
  | .stockCards => st.stock.cards = st'.stock.cards
  | .stockCursor => st.stock.cursor = st'.stock.cursor
  | .drawStep => st.drawStep = st'.drawStep

/-- Agreement on a list of frames. -/
def Frame.agrees (fs : List Frame) (st st' : State) : Prop := ∀ f ∈ fs, f.agree st st'

/-! ## The reads/writes tables

Each table is def-derived from `State.apply`'s arms (Move.lean):
legality guards and successor fields alike.  Two table invariants,
both checked by `writes_subset_reads` and the acceptance test: a move
never writes a frame it does not read, and `drawStep` is read by
`draw` alone.  Legality-vs-write honesty: `deckPile`/`deckStack` read
the stock for legality AND write it (the splice); `reveal` reads
`deal`+`depths` for its boundary views but writes only `depths`;
`draw` reads the stock to advance the cursor but writes ONLY the
cursor (`dealOnce` preserves the cards). -/

/-- Which frames a move's legality and result read. -/
def Move.reads : Move → List Frame
  | .draw => [.stockCards, .stockCursor, .drawStep]
  | .reveal _ => [.board, .deal, .depths]
  | .deckPile _ _ => [.stockCards, .stockCursor, .board]
  | .deckStack c => [.stockCards, .stockCursor, .heightsOf c.suit]
  | .pileStack c => [.board, .heightsOf c.suit]
  | .stackPile c _ => [.heightsOf c.suit, .board]
  | .pilePile _ _ => [.board]

/-- Which frames a move's successor changes. -/
def Move.writes : Move → List Frame
  | .draw => [.stockCursor]
  | .reveal _ => [.board, .depths]
  | .deckPile _ _ => [.board, .stockCards, .stockCursor]
  | .deckStack c => [.stockCards, .stockCursor, .heightsOf c.suit]
  | .pileStack c => [.board, .heightsOf c.suit]
  | .stackPile c _ => [.board, .heightsOf c.suit]
  | .pilePile _ _ => [.board]

/-- The discipline's invariant: no move writes a frame it does not
read (so an unread frame is always an inherited one — `frame_invar`). -/
theorem Move.writes_subset_reads (m : Move) (f : Frame) (h : f ∈ m.writes) : f ∈ m.reads := by
  cases m with
  | draw => simp_all [Move.reads, Move.writes]
  | reveal _ =>
      simp [Move.writes] at h
      rcases h with rfl | rfl <;> simp [Move.reads]
  | deckPile _ _ =>
      simp [Move.writes] at h
      rcases h with rfl | rfl | rfl <;> simp [Move.reads]
  | deckStack _ => simp_all [Move.reads, Move.writes]
  | pileStack _ => simp_all [Move.reads, Move.writes]
  | stackPile _ _ =>
      simp [Move.writes] at h
      rcases h with rfl | rfl <;> simp [Move.reads]
  | pilePile _ _ => simp_all [Move.reads, Move.writes]

/-! ## The local agreement kit

Twins of Relabel/Commutation lemmas, namespaced under `Frame` (this
file sits below both in the import DAG; the duplication is the
consolidation queue's, not a design choice). -/

/-- `findFirst` respects pointwise predicate agreement (Relabel's
`findFirst_congr`, namespaced). -/
theorem Frame.findFirst_congr {α : Type} {p q : α → Bool} (h : ∀ a, p a = q a) :
    ∀ (l : List α), findFirst p l = findFirst q l
  | [] => rfl
  | a :: t => by
      rw [findFirst_cons, findFirst_cons, h a]
      by_cases hq : q a = true
      · rw [if_pos hq, if_pos hq]
      · rw [if_neg hq, if_neg hq]
        exact Frame.findFirst_congr h t

/-- The hidden-pile views read only the deal and the depths (the
board/stock/heights-blindness of `topHidden`/`pileOfTopHidden`/
`hiddenBase`, at the source of every reveal-transfer route). -/
theorem Frame.topHidden_congr {st st' : State} (hdeal : st.deal = st'.deal)
    (hdpt : st.depths = st'.depths) (a : Anchor) :
    st.topHidden a = st'.topHidden a := by
  show ((st.deal.piles a).take (st.depths a)).getLast?
      = ((st'.deal.piles a).take (st'.depths a)).getLast?
  rw [show st'.deal.piles a = st.deal.piles a from by rw [hdeal], hdpt]

theorem Frame.pileOfTopHidden_congr {st st' : State} (hdeal : st.deal = st'.deal)
    (hdpt : st.depths = st'.depths) (r : Card) :
    st.pileOfTopHidden r = st'.pileOfTopHidden r := by
  show findFirst (fun a => decide (st.topHidden a = some r)) Anchor.all
      = findFirst (fun a => decide (st'.topHidden a = some r)) Anchor.all
  exact Frame.findFirst_congr (fun a => by rw [Frame.topHidden_congr hdeal hdpt a]) Anchor.all

theorem Frame.hiddenBase_congr {st st' : State} (hdeal : st.deal = st'.deal)
    (hdpt : st.depths = st'.depths) (a : Anchor) :
    st.hiddenBase a = st'.hiddenBase a := by
  show (match ((st.hidden a).reverse.drop 1).head? with
        | some d => Sum.inr d
        | none => Sum.inl a)
      = (match ((st'.hidden a).reverse.drop 1).head? with
        | some d => Sum.inr d
        | none => Sum.inl a)
  have hh : st.hidden a = st'.hidden a := by
    show (st.deal.piles a).take (st.depths a) = (st'.deal.piles a).take (st'.depths a)
    rw [show st'.deal.piles a = st.deal.piles a from by rw [hdeal], hdpt]
  rw [hh]

/-- The stock ops' agreement faces: equal cards+cursor give equal
`dealOnce`, `prev` (and `removeAt`, via `cycle_ext`). -/
theorem Frame.dealOnce_congr {s s' : Nat} {cy cy' : Cycle Card}
    (hc : cy.cards = cy'.cards) (hu : cy.cursor = cy'.cursor) (hs : s = s') :
    cy.dealOnce s = cy'.dealOnce s' := by
  show (if cy.cursor ≥ cy.cards.length then { cy with cursor := 0 }
      else { cy with cursor := min (cy.cursor + s) cy.cards.length })
      = (if cy'.cursor ≥ cy'.cards.length then { cy' with cursor := 0 }
      else { cy' with cursor := min (cy'.cursor + s') cy'.cards.length })
  rw [hu, hc, hs]

theorem Frame.prev_congr {cy cy' : Cycle Card}
    (hc : cy.cards = cy'.cards) (hu : cy.cursor = cy'.cursor) :
    cy.prev = cy'.prev := by
  show (if cy.cursor = 0 then none else cy.cards[cy.cursor - 1]?)
      = (if cy'.cursor = 0 then none else cy'.cards[cy'.cursor - 1]?)
  rw [hu, hc]

/-- `canPlace` reads only the board (plus the card-pure `canSitOn`). -/
theorem canPlace_congr {st st' : State} (hb : st.board = st'.board) (c : Card) (b : Base) :
    st.canPlace c b = st'.canPlace c b := by
  simp only [State.canPlace, State.isVis]
  rw [show st'.board = st.board from hb.symm]

/-- `canMoveRun` reads only the board (the run walk included). -/
theorem canMoveRun_congr {st st' : State} (hb : st.board = st'.board) (c : Card) (b : Base) :
    st.canMoveRun c b = st'.canMoveRun c b := by
  simp only [State.canMoveRun, State.canPlace, State.isVis]
  rw [show st'.board = st.board from hb.symm]

theorem cycle_ext {cy cy' : Cycle Card}
    (hc : cy.cards = cy'.cards) (hu : cy.cursor = cy'.cursor) : cy = cy' := by
  cases cy with
  | mk cs cu =>
    cases cy' with
    | mk cs' cu' =>
      have h1 : cs = cs' := hc
      have h2 : cu = cu' := hu
      rw [h1, h2]

/-- Agreement on every frame is state equality (the heights by their
four suit cells, the stock by its two). -/
theorem state_ext_of_frames {st st' : State} (h : ∀ (f : Frame), f.agree st st') : st = st' := by
  have hdeal : st.deal = st'.deal := h Frame.deal
  have hboard : st.board = st'.board := h Frame.board
  have hhs : st.heights = st'.heights := by
    funext s
    exact h (Frame.heightsOf s)
  have hdpt : st.depths = st'.depths := h Frame.depths
  have hstock : st.stock = st'.stock :=
    cycle_ext (h Frame.stockCards) (h Frame.stockCursor)
  have hds : st.drawStep = st'.drawStep := h Frame.drawStep
  have hη : st = ⟨st.deal, st.board, st.heights, st.depths, st.stock, st.drawStep⟩ := rfl
  have hη' : st' = ⟨st'.deal, st'.board, st'.heights, st'.depths, st'.stock, st'.drawStep⟩ := rfl
  rw [hη, hη', hdeal, hboard, hhs, hdpt, hstock, hds]

/-! ## Master law 0 — the inheritance law

Unwritten frames pass through untouched; this plus congruence is the
whole blindness kit. -/

/-- The successor inherits every frame the move does not write. -/
theorem frame_invar {m : Move} {st s₁ : State} (h : st.apply m = some s₁) :
    ∀ (f : Frame), f ∉ m.writes → f.agree s₁ st := by
  move_cases h with
  | draw =>
      intro f hf
      cases f with
      | deal => rfl
      | board => rfl
      | heightsOf s => rfl
      | depths => rfl
      | stockCards => exact Cycle.dealOnce_cards st.drawStep st.stock
      | stockCursor => exact absurd (by simp [Move.writes]) hf
      | drawStep => rfl
  | reveal c =>
      intro f hf
      cases f with
      | deal => rfl
      | board => exact absurd (by simp [Move.writes]) hf
      | heightsOf s => rfl
      | depths => exact absurd (by simp [Move.writes]) hf
      | stockCards => rfl
      | stockCursor => rfl
      | drawStep => rfl
  | deckPile c b =>
      intro f hf
      cases f with
      | deal => rfl
      | board => exact absurd (by simp [Move.writes]) hf
      | heightsOf s => rfl
      | depths => rfl
      | stockCards => exact absurd (by simp [Move.writes]) hf
      | stockCursor => exact absurd (by simp [Move.writes]) hf
      | drawStep => rfl
  | deckStack c =>
      intro f hf
      cases f with
      | deal => rfl
      | board => rfl
      | heightsOf s =>
          by_cases hss : s = c.suit
          · exact absurd (by simp [Move.writes, hss]) hf
          · show (if s = c.suit then st.heights s + 1 else st.heights s) = st.heights s
            rw [if_neg hss]
      | depths => rfl
      | stockCards => exact absurd (by simp [Move.writes]) hf
      | stockCursor => exact absurd (by simp [Move.writes]) hf
      | drawStep => rfl
  | pileStack c =>
      intro f hf
      cases f with
      | deal => rfl
      | board => exact absurd (by simp [Move.writes]) hf
      | heightsOf s =>
          by_cases hss : s = c.suit
          · exact absurd (by simp [Move.writes, hss]) hf
          · show (if s = c.suit then st.heights s + 1 else st.heights s) = st.heights s
            rw [if_neg hss]
      | depths => rfl
      | stockCards => rfl
      | stockCursor => rfl
      | drawStep => rfl
  | stackPile c b =>
      intro f hf
      cases f with
      | deal => rfl
      | board => exact absurd (by simp [Move.writes]) hf
      | heightsOf s =>
          by_cases hss : s = c.suit
          · exact absurd (by simp [Move.writes, hss]) hf
          · show (if s = c.suit then st.heights s - 1 else st.heights s) = st.heights s
            rw [if_neg hss]
      | depths => rfl
      | stockCards => rfl
      | stockCursor => rfl
      | drawStep => rfl
  | pilePile c b =>
      intro f hf
      cases f with
      | deal => rfl
      | board => exact absurd (by simp [Move.writes]) hf
      | heightsOf s => rfl
      | depths => rfl
      | stockCards => rfl
      | stockCursor => rfl
      | drawStep => rfl

/-! ## Master law 1 — frame congruence -/

/-- **Frame congruence**: two states agreeing on a move's read-frames
get the same verdict, and the successors agree on every frame the
sources agreed on.  Together with `frame_invar` (unread frames are
inherited from the TARGET), the successor is fully determined: the
with-update wrapper corollaries below are the packaged form. -/
theorem frame_congr {m : Move} {st st' : State} (hr : Frame.agrees m.reads st st')
    {s₁ : State} (h : st.apply m = some s₁) :
    ∃ s₁' : State, st'.apply m = some s₁' ∧
      (∀ (f : Frame), f.agree st st' → f.agree s₁ s₁') := by
  cases m with
  | draw =>
      have hc : st.stock.cards = st'.stock.cards := hr Frame.stockCards (by simp [Move.reads])
      have hu : st.stock.cursor = st'.stock.cursor := hr Frame.stockCursor (by simp [Move.reads])
      have hs : st.drawStep = st'.drawStep := hr Frame.drawStep (by simp [Move.reads])
      have hcyc : st.stock = st'.stock := cycle_ext hc hu
      rw [apply_draw_iff] at h
      obtain rfl := h
      refine ⟨{ st' with stock := st'.stock.dealOnce st'.drawStep }, ?_, ?_⟩
      · rw [apply_draw_iff]
      · intro f hf
        cases f with
        | deal => exact hf
        | board => exact hf
        | heightsOf s => exact hf
        | depths => exact hf
        | stockCards =>
            show (st.stock.dealOnce st.drawStep).cards = (st'.stock.dealOnce st'.drawStep).cards
            rw [Cycle.dealOnce_cards, Cycle.dealOnce_cards, hc]
        | stockCursor =>
            show (st.stock.dealOnce st.drawStep).cursor = (st'.stock.dealOnce st'.drawStep).cursor
            rw [hcyc, hs]
        | drawStep => exact hf
  | reveal c =>
      rw [apply_reveal_iff] at h
      obtain ⟨htop, r, a, bd, hbot, hpile, hatt, hs₁⟩ := h
      have hb : st.board = st'.board := hr Frame.board (by simp [Move.reads])
      have hd : st.deal = st'.deal := hr Frame.deal (by simp [Move.reads])
      have hdp : st.depths = st'.depths := hr Frame.depths (by simp [Move.reads])
      have htop' : st'.board.topOf (Sum.inr c) = none := by
        rw [show st'.board = st.board from hb.symm]; exact htop
      have hbot' : st'.board.bottomOf c = some (Sum.inr r) := by
        rw [show st'.board = st.board from hb.symm]; exact hbot
      have hpile' : st'.pileOfTopHidden r = some a := by
        rw [(Frame.pileOfTopHidden_congr hd hdp r).symm]
        exact hpile
      have hatt' : st'.board.attach (st'.hiddenBase a) r = some bd := by
        rw [(Frame.hiddenBase_congr hd hdp a).symm,
          show st'.board = st.board from hb.symm]
        exact hatt
      refine ⟨{ st' with
        board := bd,
        depths := fun a' => if a' = a then st'.depths a - 1 else st'.depths a' }, ?_, ?_⟩
      · rw [apply_reveal_iff]
        exact ⟨htop', r, a, bd, hbot', hpile', hatt', rfl⟩
      · rw [hs₁]
        intro f hf
        cases f with
        | deal => exact hf
        | board => rfl
        | heightsOf s => exact hf
        | depths =>
            funext a'
            show (if a' = a then st.depths a - 1 else st.depths a')
              = (if a' = a then st'.depths a - 1 else st'.depths a')
            by_cases h'a : a' = a
            · rw [if_pos h'a, if_pos h'a, congrFun hdp a]
            · rw [if_neg h'a, if_neg h'a, congrFun hdp a']
        | stockCards => exact hf
        | stockCursor => exact hf
        | drawStep => exact hf
  | deckPile c b =>
      rw [apply_deckPile_iff] at h
      obtain ⟨hprev, hcp, bd, hatt, hs₁⟩ := h
      have hc : st.stock.cards = st'.stock.cards := hr Frame.stockCards (by simp [Move.reads])
      have hu : st.stock.cursor = st'.stock.cursor := hr Frame.stockCursor (by simp [Move.reads])
      have hb : st.board = st'.board := hr Frame.board (by simp [Move.reads])
      have hprev' : st'.stock.prev = some c := by
        rw [(Frame.prev_congr hc hu).symm]; exact hprev
      have hcp' : st'.canPlace c b = true := by
        rw [(canPlace_congr hb c b).symm]; exact hcp
      refine ⟨{ st' with
        board := bd,
        stock := st'.stock.removeAt (st'.stock.cursor - 1) }, ?_, ?_⟩
      · rw [apply_deckPile_iff]
        refine ⟨hprev', hcp', bd, ?_, rfl⟩
        rw [show st'.board = st.board from hb.symm]
        exact hatt
      · rw [hs₁]
        intro f hf
        cases f with
        | deal => exact hf
        | board => rfl
        | heightsOf s => exact hf
        | depths => exact hf
        | stockCards =>
            show Cycle.removeIdx st.stock.cards (st.stock.cursor - 1)
                = Cycle.removeIdx st'.stock.cards (st'.stock.cursor - 1)
            rw [hc, hu]
        | stockCursor =>
            show (if st.stock.cursor - 1 < st.stock.cursor then st.stock.cursor - 1
                else st.stock.cursor)
                = (if st'.stock.cursor - 1 < st'.stock.cursor then st'.stock.cursor - 1
                else st'.stock.cursor)
            rw [hu]
        | drawStep => exact hf
  | deckStack c =>
      rw [apply_deckStack_iff] at h
      obtain ⟨hprev, hrk, hs₁⟩ := h
      have hc : st.stock.cards = st'.stock.cards := hr Frame.stockCards (by simp [Move.reads])
      have hu : st.stock.cursor = st'.stock.cursor := hr Frame.stockCursor (by simp [Move.reads])
      have hh : st.heights c.suit = st'.heights c.suit :=
        hr (Frame.heightsOf c.suit) (by simp [Move.reads])
      have hprev' : st'.stock.prev = some c := by
        rw [(Frame.prev_congr hc hu).symm]; exact hprev
      refine ⟨{ st' with
        stock := st'.stock.removeAt (st'.stock.cursor - 1),
        heights := fun s => if s = c.suit then st'.heights s + 1 else st'.heights s }, ?_, ?_⟩
      · rw [apply_deckStack_iff]
        exact ⟨hprev', by rw [← hh]; exact hrk, rfl⟩
      · rw [hs₁]
        intro f hf
        cases f with
        | deal => exact hf
        | board => exact hf
        | heightsOf s =>
            show (if s = c.suit then st.heights s + 1 else st.heights s)
              = (if s = c.suit then st'.heights s + 1 else st'.heights s)
            by_cases hss : s = c.suit
            · rw [if_pos hss, if_pos hss, hss, hh]
            · rw [if_neg hss, if_neg hss]
              exact hf
        | depths => exact hf
        | stockCards =>
            show Cycle.removeIdx st.stock.cards (st.stock.cursor - 1)
                = Cycle.removeIdx st'.stock.cards (st'.stock.cursor - 1)
            rw [hc, hu]
        | stockCursor =>
            show (if st.stock.cursor - 1 < st.stock.cursor then st.stock.cursor - 1
                else st.stock.cursor)
                = (if st'.stock.cursor - 1 < st'.stock.cursor then st'.stock.cursor - 1
                else st'.stock.cursor)
            rw [hu]
        | drawStep => exact hf
  | pileStack c =>
      rw [apply_pileStack_iff] at h
      obtain ⟨htop, b₀, hb, hrk, hs₁⟩ := h
      have hbb : st.board = st'.board := hr Frame.board (by simp [Move.reads])
      have hh : st.heights c.suit = st'.heights c.suit :=
        hr (Frame.heightsOf c.suit) (by simp [Move.reads])
      have htop' : st'.board.topOf (Sum.inr c) = none := by
        rw [show st'.board = st.board from hbb.symm]; exact htop
      have hb' : st'.board.bottomOf c = some b₀ := by
        rw [show st'.board = st.board from hbb.symm]; exact hb
      refine ⟨{ st' with
        board := st'.board.detach b₀,
        heights := fun s => if s = c.suit then st'.heights s + 1 else st'.heights s }, ?_, ?_⟩
      · rw [apply_pileStack_iff]
        exact ⟨htop', b₀, hb', by rw [← hh]; exact hrk, rfl⟩
      · rw [hs₁]
        intro f hf
        cases f with
        | deal => exact hf
        | board =>
            show st.board.detach b₀ = st'.board.detach b₀
            rw [show st'.board = st.board from hbb.symm]
        | heightsOf s =>
            show (if s = c.suit then st.heights s + 1 else st.heights s)
              = (if s = c.suit then st'.heights s + 1 else st'.heights s)
            by_cases hss : s = c.suit
            · rw [if_pos hss, if_pos hss, hss, hh]
            · rw [if_neg hss, if_neg hss]
              exact hf
        | depths => exact hf
        | stockCards => exact hf
        | stockCursor => exact hf
        | drawStep => exact hf
  | stackPile c b =>
      rw [apply_stackPile_iff] at h
      obtain ⟨hrk, hcp, bd, hatt, hs₁⟩ := h
      have hbb : st.board = st'.board := hr Frame.board (by simp [Move.reads])
      have hh : st.heights c.suit = st'.heights c.suit :=
        hr (Frame.heightsOf c.suit) (by simp [Move.reads])
      have hcp' : st'.canPlace c b = true := by
        rw [(canPlace_congr hbb c b).symm]; exact hcp
      refine ⟨{ st' with
        board := bd,
        heights := fun s => if s = c.suit then st'.heights s - 1 else st'.heights s }, ?_, ?_⟩
      · rw [apply_stackPile_iff]
        exact ⟨by rw [← hh]; exact hrk, hcp', bd,
          by rw [show st'.board = st.board from hbb.symm]; exact hatt, rfl⟩
      · rw [hs₁]
        intro f hf
        cases f with
        | deal => exact hf
        | board => rfl
        | heightsOf s =>
            show (if s = c.suit then st.heights s - 1 else st.heights s)
              = (if s = c.suit then st'.heights s - 1 else st'.heights s)
            by_cases hss : s = c.suit
            · rw [if_pos hss, if_pos hss, hss, hh]
            · rw [if_neg hss, if_neg hss]
              exact hf
        | depths => exact hf
        | stockCards => exact hf
        | stockCursor => exact hf
        | drawStep => exact hf
  | pilePile c b =>
      rw [apply_pilePile_iff] at h
      obtain ⟨b₀, hb, hne, hcmr, bd, hatt, hs₁⟩ := h
      have hbb : st.board = st'.board := hr Frame.board (by simp [Move.reads])
      have hb' : st'.board.bottomOf c = some b₀ := by
        rw [show st'.board = st.board from hbb.symm]; exact hb
      have hcmr' : st'.canMoveRun c b = true := by
        rw [(canMoveRun_congr hbb c b).symm]; exact hcmr
      refine ⟨{ st' with board := bd }, ?_, ?_⟩
      · rw [apply_pilePile_iff]
        exact ⟨b₀, hb', hne, hcmr', bd,
          by rw [show st'.board = st.board from hbb.symm]; exact hatt, rfl⟩
      · rw [hs₁]
        intro f hf
        cases f with
        | deal => exact hf
        | board => rfl
        | heightsOf s => exact hf
        | depths => exact hf
        | stockCards => exact hf
        | stockCursor => exact hf
        | drawStep => exact hf

/-- `Frame.agree` chains and flips (the match form is an `Eq` at every
concrete frame, so these are `Eq.trans`/`Eq.symm` up to iota). -/
theorem Frame.agree_trans {f : Frame} {s₁ s₂ s₃ : State}
    (h1 : f.agree s₁ s₂) (h2 : f.agree s₂ s₃) : f.agree s₁ s₃ := by
  cases f <;> exact h1.trans h2

theorem Frame.agree_symm {f : Frame} {s₁ s₂ : State} (h : f.agree s₁ s₂) : f.agree s₂ s₁ := by
  cases f <;> exact h.symm

theorem Frame.agrees_symm {fs : List Frame} {st st' : State} (h : Frame.agrees fs st st') :
    Frame.agrees fs st' st := fun _ hf => Frame.agree_symm (h _ hf)

/-- **Frame congruence, none half**: the verdict transfers — the move
fails in the source iff it fails in the read-agreeing target. -/
theorem frame_congr_none {m : Move} {st st' : State} (hr : Frame.agrees m.reads st st')
    (h : st.apply m = none) : st'.apply m = none := by
  cases h' : st'.apply m with
  | none => rfl
  | some s₁' =>
      exfalso
      obtain ⟨_, hc, _⟩ := frame_congr (Frame.agrees_symm hr) h'
      rw [h] at hc
      exact absurd hc (by simp)

/-! ## Master law 2 — disjoint-frames commute -/

/-- **Disjoint-frames commute**: when `m`'s reads miss `m'`'s writes and
vice versa, and the write-sets are disjoint, both orders land on the
same state — with NO legality hypotheses.  A failing move fails in
both compositions (the frames it reads are preserved by the other
move, `frame_invar` + `frame_congr_none`); two succeeding moves write
independent frames, and each order's result agrees framewise with the
common write-source merge. -/
theorem commute_of_disjoint_frames (st : State) (m m' : Move)
    (h1 : ∀ f ∈ m.reads, f ∉ m'.writes)
    (h2 : ∀ f ∈ m.writes, f ∉ m'.reads)
    (h3 : ∀ f ∈ m.writes, f ∉ m'.writes) :
    (st.apply m >>= fun s => s.apply m') = (st.apply m' >>= fun s => s.apply m) := by
  cases hm : st.apply m with
  | none =>
      cases hm' : st.apply m' with
      | none => rfl
      | some t₁ =>
          have hrm : Frame.agrees m.reads t₁ st := fun f hf => frame_invar hm' f (h1 f hf)
          show (none : Option State) = t₁.apply m
          rw [frame_congr_none (Frame.agrees_symm hrm) hm]
  | some s₁ =>
      cases hm' : st.apply m' with
      | none =>
          have hrm' : Frame.agrees m'.reads s₁ st :=
            fun f hf => frame_invar hm f (fun hmem => h2 f hmem hf)
          show s₁.apply m' = (none : Option State)
          rw [frame_congr_none (Frame.agrees_symm hrm') hm']
      | some t₁ =>
          have hrm' : Frame.agrees m'.reads s₁ st :=
            fun f hf => frame_invar hm f (fun hmem => h2 f hmem hf)
          have hrm : Frame.agrees m.reads t₁ st := fun f hf => frame_invar hm' f (h1 f hf)
          cases hw : s₁.apply m' with
          | none => exact absurd (hm'.symm.trans (frame_congr_none hrm' hw)) (by simp)
          | some w =>
              cases hw' : t₁.apply m with
              | none => exact absurd (hm.symm.trans (frame_congr_none hrm hw')) (by simp)
              | some w' =>
                  have heq : w = w' := by
                    apply state_ext_of_frames
                    intro f
                    by_cases hwm : f ∈ m.writes
                    · have e1 : f.agree w s₁ := frame_invar hw f (h3 f hwm)
                      have hst : f.agree st t₁ := Frame.agree_symm
                        (frame_invar hm' f (fun hmem => h3 f hwm hmem))
                      obtain ⟨s₁'', hc'', hcl2''⟩ := frame_congr (Frame.agrees_symm hrm) hm
                      have hs₁'' : s₁'' = w' := Option.some.inj (hc''.symm.trans hw')
                      subst hs₁''
                      exact Frame.agree_trans e1 (hcl2'' f hst)
                    · by_cases hwm' : f ∈ m'.writes
                      · have e2 : f.agree w' t₁ :=
                          frame_invar hw' f (fun hmem => h3 f hmem hwm')
                        have hst' : f.agree s₁ st :=
                          frame_invar hm f (fun hmem => h3 f hmem hwm')
                        obtain ⟨s₁''', hc''', hcl2'''⟩ := frame_congr hrm' hw
                        have hs₁''' : s₁''' = t₁ := Option.some.inj (hc'''.symm.trans hm')
                        subst hs₁'''
                        exact Frame.agree_trans (hcl2''' f hst') (Frame.agree_symm e2)
                      · have e1 : f.agree w s₁ := frame_invar hw f hwm'
                        have e2 : f.agree w' t₁ := frame_invar hw' f hwm
                        exact Frame.agree_trans e1 (Frame.agree_trans (frame_invar hm f hwm)
                          (Frame.agree_trans (Frame.agree_symm (frame_invar hm' f hwm'))
                            (Frame.agree_symm e2)))
                  show s₁.apply m' = t₁.apply m
                  rw [hw, hw', heq]

/-! ## The with-update wrapper corollaries

The packaged form of laws 0+1: a move that never reads the replaced
frames replays from the replaced state with the replacement carried
into the successor — the whole blindness kit in three shapes. -/

/-- The unread frames of the TARGET's successor come from the target
itself (law 0 through the target's application). -/
theorem frame_congr_unread {m : Move} {st' s₁' : State} (h1 : st'.apply m = some s₁')
    (f : Frame) (hf : f ∉ m.reads) : f.agree s₁' st' :=
  frame_invar h1 f (fun hmem => hf (Move.writes_subset_reads m f hmem))

/-- The stock+heights replacement form (Commutation's `reveal_blind_*`
and `pilePile_blind_*`, one frame-congruence application). -/
theorem apply_blind_stock_heights {m : Move} {st s₁ : State} {cy : Cycle Card}
    {hs : Suit → Nat}
    (hrd : Frame.stockCards ∉ m.reads) (hru : Frame.stockCursor ∉ m.reads)
    (hrh : ∀ s, Frame.heightsOf s ∉ m.reads)
    (h : st.apply m = some s₁) :
    ({ st with stock := cy, heights := hs } : State).apply m
      = some { s₁ with stock := cy, heights := hs } := by
  have hr : Frame.agrees m.reads st { st with stock := cy, heights := hs } := by
    intro f hf
    cases f with
    | deal => rfl
    | board => rfl
    | heightsOf s => exact absurd hf (hrh s)
    | depths => rfl
    | stockCards => exact absurd hf hrd
    | stockCursor => exact absurd hf hru
    | drawStep => rfl
  obtain ⟨s₁', h1, h2⟩ := frame_congr hr h
  have he : s₁' = { s₁ with stock := cy, heights := hs } := by
    apply state_ext_of_frames
    intro f
    cases f with
    | deal => exact Frame.agree_symm (h2 Frame.deal rfl)
    | board => exact Frame.agree_symm (h2 Frame.board rfl)
    | heightsOf s => exact frame_congr_unread h1 _ (hrh s)
    | depths => exact Frame.agree_symm (h2 Frame.depths rfl)
    | stockCards => exact frame_congr_unread h1 _ hrd
    | stockCursor => exact frame_congr_unread h1 _ hru
    | drawStep => exact Frame.agree_symm (h2 Frame.drawStep rfl)
  rw [he] at h1
  exact h1

theorem apply_blind_stock_heights_none {m : Move} {st : State} {cy : Cycle Card}
    {hs : Suit → Nat}
    (hrd : Frame.stockCards ∉ m.reads) (hru : Frame.stockCursor ∉ m.reads)
    (hrh : ∀ s, Frame.heightsOf s ∉ m.reads)
    (h : st.apply m = none) :
    ({ st with stock := cy, heights := hs } : State).apply m = none := by
  refine frame_congr_none ?_ h
  intro f hf
  cases f with
  | deal => rfl
  | board => rfl
  | heightsOf s => exact absurd hf (hrh s)
  | depths => rfl
  | stockCards => exact absurd hf hrd
  | stockCursor => exact absurd hf hru
  | drawStep => rfl

/-- The board+depths replacement form (Commutation's `deckStack_blind_*`). -/
theorem apply_blind_board_depths {m : Move} {st s₁ : State} {bd : Board} {dpt : Anchor → Nat}
    (hrb : Frame.board ∉ m.reads) (hrd : Frame.depths ∉ m.reads)
    (h : st.apply m = some s₁) :
    ({ st with board := bd, depths := dpt } : State).apply m
      = some { s₁ with board := bd, depths := dpt } := by
  have hr : Frame.agrees m.reads st { st with board := bd, depths := dpt } := by
    intro f hf
    cases f with
    | deal => rfl
    | board => exact absurd hf hrb
    | heightsOf s => rfl
    | depths => exact absurd hf hrd
    | stockCards => rfl
    | stockCursor => rfl
    | drawStep => rfl
  obtain ⟨s₁', h1, h2⟩ := frame_congr hr h
  have he : s₁' = { s₁ with board := bd, depths := dpt } := by
    apply state_ext_of_frames
    intro f
    cases f with
    | deal => exact Frame.agree_symm (h2 Frame.deal rfl)
    | board => exact frame_congr_unread h1 _ hrb
    | heightsOf s => exact Frame.agree_symm (h2 (Frame.heightsOf s) rfl)
    | depths => exact frame_congr_unread h1 _ hrd
    | stockCards => exact Frame.agree_symm (h2 Frame.stockCards rfl)
    | stockCursor => exact Frame.agree_symm (h2 Frame.stockCursor rfl)
    | drawStep => exact Frame.agree_symm (h2 Frame.drawStep rfl)
  rw [he] at h1
  exact h1

theorem apply_blind_board_depths_none {m : Move} {st : State} {bd : Board} {dpt : Anchor → Nat}
    (hrb : Frame.board ∉ m.reads) (hrd : Frame.depths ∉ m.reads)
    (h : st.apply m = none) :
    ({ st with board := bd, depths := dpt } : State).apply m = none := by
  refine frame_congr_none ?_ h
  intro f hf
  cases f with
  | deal => rfl
  | board => exact absurd hf hrb
  | heightsOf s => rfl
  | depths => exact absurd hf hrd
  | stockCards => rfl
  | stockCursor => rfl
  | drawStep => rfl

/-- The stock-only replacement form (Commutation's `pileStack_blind_*`
and `stackPile_blind_*`). -/
theorem apply_blind_stock {m : Move} {st s₁ : State} {cy : Cycle Card}
    (hrd : Frame.stockCards ∉ m.reads) (hru : Frame.stockCursor ∉ m.reads)
    (h : st.apply m = some s₁) :
    ({ st with stock := cy } : State).apply m = some { s₁ with stock := cy } := by
  have hr : Frame.agrees m.reads st { st with stock := cy } := by
    intro f hf
    cases f with
    | deal => rfl
    | board => rfl
    | heightsOf s => rfl
    | depths => rfl
    | stockCards => exact absurd hf hrd
    | stockCursor => exact absurd hf hru
    | drawStep => rfl
  obtain ⟨s₁', h1, h2⟩ := frame_congr hr h
  have he : s₁' = { s₁ with stock := cy } := by
    apply state_ext_of_frames
    intro f
    cases f with
    | deal => exact Frame.agree_symm (h2 Frame.deal rfl)
    | board => exact Frame.agree_symm (h2 Frame.board rfl)
    | heightsOf s => exact Frame.agree_symm (h2 (Frame.heightsOf s) rfl)
    | depths => exact Frame.agree_symm (h2 Frame.depths rfl)
    | stockCards => exact frame_congr_unread h1 _ hrd
    | stockCursor => exact frame_congr_unread h1 _ hru
    | drawStep => exact Frame.agree_symm (h2 Frame.drawStep rfl)
  rw [he] at h1
  exact h1

theorem apply_blind_stock_none {m : Move} {st : State} {cy : Cycle Card}
    (hrd : Frame.stockCards ∉ m.reads) (hru : Frame.stockCursor ∉ m.reads)
    (h : st.apply m = none) :
    ({ st with stock := cy } : State).apply m = none := by
  refine frame_congr_none ?_ h
  intro f hf
  cases f with
  | deal => rfl
  | board => rfl
  | heightsOf s => rfl
  | depths => rfl
  | stockCards => exact absurd hf hrd
  | stockCursor => exact absurd hf hru
  | drawStep => rfl

/-! ### The blindness kit, re-derived

Each of Commutation's `*_blind_*` lemmas is one wrapper application;
the non-membership side conditions are `decide`-level facts about the
reads table. -/

/-- `reveal_blind_some` (Commutation.lean), re-derived. -/
theorem reveal_blind_some_frame {st : State} {c : Card} {cy : Cycle Card} {hs : Suit → Nat}
    {s₁ : State} (h : st.apply (Move.reveal c) = some s₁) :
    ({ st with stock := cy, heights := hs } : State).apply (Move.reveal c)
      = some { s₁ with stock := cy, heights := hs } :=
  apply_blind_stock_heights (by simp [Move.reads]) (by simp [Move.reads])
    (by simp [Move.reads]) h

/-- `reveal_blind_none` (Commutation.lean), re-derived. -/
theorem reveal_blind_none_frame {st : State} {c : Card} {cy : Cycle Card} {hs : Suit → Nat}
    (h : st.apply (Move.reveal c) = none) :
    ({ st with stock := cy, heights := hs } : State).apply (Move.reveal c) = none :=
  apply_blind_stock_heights_none (by simp [Move.reads]) (by simp [Move.reads])
    (by simp [Move.reads]) h

/-- `pilePile_blind_some` (Commutation.lean), re-derived. -/
theorem pilePile_blind_some_frame {st : State} {c : Card} {b : Base} {cy : Cycle Card}
    {hs : Suit → Nat} {s₁ : State} (h : st.apply (Move.pilePile c b) = some s₁) :
    ({ st with stock := cy, heights := hs } : State).apply (Move.pilePile c b)
      = some { s₁ with stock := cy, heights := hs } :=
  apply_blind_stock_heights (by simp [Move.reads]) (by simp [Move.reads])
    (by simp [Move.reads]) h

/-- `deckStack_blind_some` (Commutation.lean), re-derived. -/
theorem deckStack_blind_some_frame {st : State} {c : Card} {bd : Board} {dpt : Anchor → Nat}
    {sd : State} (h : st.apply (Move.deckStack c) = some sd) :
    ({ st with board := bd, depths := dpt } : State).apply (Move.deckStack c)
      = some { sd with board := bd, depths := dpt } :=
  apply_blind_board_depths (by simp [Move.reads]) (by simp [Move.reads]) h

/-- `deckStack_blind_none` (Commutation.lean), re-derived. -/
theorem deckStack_blind_none_frame {st : State} {c : Card} {bd : Board} {dpt : Anchor → Nat}
    (h : st.apply (Move.deckStack c) = none) :
    ({ st with board := bd, depths := dpt } : State).apply (Move.deckStack c) = none :=
  apply_blind_board_depths_none (by simp [Move.reads]) (by simp [Move.reads]) h

/-- `pileStack_blind_some` (Commutation.lean), re-derived. -/
theorem pileStack_blind_some_frame {st : State} {c : Card} {cy : Cycle Card} {st₁ : State}
    (h : st.apply (Move.pileStack c) = some st₁) :
    ({ st with stock := cy } : State).apply (Move.pileStack c)
      = some { st₁ with stock := cy } :=
  apply_blind_stock (by simp [Move.reads]) (by simp [Move.reads]) h

/-- `stackPile_blind_none` (Commutation.lean), re-derived. -/
theorem stackPile_blind_none_frame {st : State} {c : Card} {b : Base} {cy : Cycle Card}
    (h : st.apply (Move.stackPile c b) = none) :
    ({ st with stock := cy } : State).apply (Move.stackPile c b) = none :=
  apply_blind_stock_none (by simp [Move.reads]) (by simp [Move.reads]) h

/-! ### The commutation layer, re-derived -/

/-- The frame form of `deal_commutes_nonStock` (Commutation): the deal
commutes with every move that never reads the stock frames — this is
the hnc guard of `commute_of_disjoint_touch` DERIVED, not assumed (the
guard's content is exactly "no stock frames in reads"; the
non-consuming non-draw moves are precisely those, and `draw` itself is
the same-term case Commutation handles directly). -/
theorem deal_commutes_nonStock_frame (st : State) (m : Move)
    (hr : Frame.stockCursor ∉ m.reads ∧ Frame.stockCards ∉ m.reads ∧ Frame.drawStep ∉ m.reads) :
    (st.apply m >>= fun s => s.apply Move.draw) = (st.apply Move.draw >>= fun s => s.apply m) := by
  have h2 : ∀ f ∈ m.writes, f ∉ (Move.draw).reads := by
    intro f hf
    have hfr : f ∈ m.reads := Move.writes_subset_reads m f hf
    cases f <;> simp_all [Move.reads, Move.writes]
  have h3 : ∀ f ∈ m.writes, f ∉ (Move.draw).writes := by
    intro f hf
    have hfr : f ∈ m.reads := Move.writes_subset_reads m f hf
    cases f <;> simp_all [Move.reads, Move.writes]
  exact commute_of_disjoint_frames st m Move.draw
    (fun f hf => by cases f <;> simp_all [Move.reads, Move.writes]) h2 h3

/-- `draw_comm_reveal` (Commutation), re-derived. -/
theorem draw_comm_reveal_frame (st : State) (c : Card) :
    (st.apply Move.draw >>= fun s => s.apply (Move.reveal c)) =
    (st.apply (Move.reveal c) >>= fun s => s.apply Move.draw) :=
  (deal_commutes_nonStock_frame st (Move.reveal c) (by simp [Move.reads])).symm

/-- `draw_comm_pileStack` (Commutation), re-derived. -/
theorem draw_comm_pileStack_frame (st : State) (c : Card) :
    (st.apply Move.draw >>= fun s => s.apply (Move.pileStack c)) =
    (st.apply (Move.pileStack c) >>= fun s => s.apply Move.draw) :=
  (deal_commutes_nonStock_frame st (Move.pileStack c) (by simp [Move.reads])).symm

/-- `draw_comm_stackPile` (Commutation), re-derived. -/
theorem draw_comm_stackPile_frame (st : State) (c : Card) (b : Base) :
    (st.apply Move.draw >>= fun s => s.apply (Move.stackPile c b)) =
    (st.apply (Move.stackPile c b) >>= fun s => s.apply Move.draw) :=
  (deal_commutes_nonStock_frame st (Move.stackPile c b) (by simp [Move.reads])).symm

/-- `draw_comm_pilePile` (Commutation), re-derived. -/
theorem draw_comm_pilePile_frame (st : State) (c : Card) (b : Base) :
    (st.apply Move.draw >>= fun s => s.apply (Move.pilePile c b)) =
    (st.apply (Move.pilePile c b) >>= fun s => s.apply Move.draw) :=
  (deal_commutes_nonStock_frame st (Move.pilePile c b) (by simp [Move.reads])).symm

/-- The reveal·deckStack arm of `commute_of_compsDisjoint`
(Commutation), re-derived — the C-IND clean sector. -/
theorem reveal_deckStack_comm_frame (st : State) (c c' : Card) :
    (st.apply (Move.reveal c) >>= fun s => s.apply (Move.deckStack c')) =
    (st.apply (Move.deckStack c') >>= fun s => s.apply (Move.reveal c)) :=
  commute_of_disjoint_frames st (Move.reveal c) (Move.deckStack c')
    (fun f hf => by cases f <;> simp_all [Move.reads, Move.writes])
    (fun f hf => by cases f <;> simp_all [Move.reads, Move.writes])
    (fun f hf => by cases f <;> simp_all [Move.writes])

/-- The deckStack·pilePile arm of `commute_of_compsDisjoint`
(Commutation), re-derived. -/
theorem deckStack_pilePile_comm_frame (st : State) (c : Card) (c' : Card) (b : Base) :
    (st.apply (Move.deckStack c) >>= fun s => s.apply (Move.pilePile c' b)) =
    (st.apply (Move.pilePile c' b) >>= fun s => s.apply (Move.deckStack c)) :=
  commute_of_disjoint_frames st (Move.deckStack c) (Move.pilePile c' b)
    (fun f hf => by cases f <;> simp_all [Move.reads, Move.writes])
    (fun f hf => by cases f <;> simp_all [Move.reads, Move.writes])
    (fun f hf => by cases f <;> simp_all [Move.writes])

/-- `comm_deckStack_pileStack` (Commutation), re-derived and
STRENGTHENED (the touch-disjointness hypothesis dropped): the
different-suit case is `commute_of_disjoint_frames` — the per-suit
height cells are independent, so a foundation waste-draw and a
tableau foundation-build commute; the same-suit case is vacuous (the
two deckStack guards read the height on either side of the pileStack
bump). -/
theorem comm_deckStack_pileStack_frame {st : State} {c c' : Card} {st₂ st₃ : State}
    (h₁ : (st.apply (Move.deckStack c) >>= fun s => s.apply (Move.pileStack c')) = some st₂)
    (h₂ : (st.apply (Move.pileStack c') >>= fun s => s.apply (Move.deckStack c)) = some st₃) :
    st₂ = st₃ := by
  by_cases hσ : c.suit = c'.suit
  · exfalso
    obtain ⟨s₁, hDS, hPS⟩ := Option.bind_eq_some_iff.mp h₁
    obtain ⟨s₃, hPS', hDS'⟩ := Option.bind_eq_some_iff.mp h₂
    rw [apply_deckStack_iff] at hDS
    obtain ⟨hprev, hrk, hs₁⟩ := hDS
    rw [apply_pileStack_iff] at hPS
    obtain ⟨htop', b₀', hb', hrk', hs₂⟩ := hPS
    rw [apply_pileStack_iff] at hPS'
    obtain ⟨htop₂, b₀, hb, hrk₂, hs₃⟩ := hPS'
    rw [apply_deckStack_iff] at hDS'
    obtain ⟨hprev', hrk'', hs₄⟩ := hDS'
    rw [hs₁] at hrk'
    rw [hs₃] at hrk''
    have hrk'₂ : c'.rank.toIdx
        = (if c'.suit = c.suit then st.heights c'.suit + 1 else st.heights c'.suit) := hrk'
    have hrk''₂ : c.rank.toIdx
        = (if c.suit = c'.suit then st.heights c.suit + 1 else st.heights c.suit) := hrk''
    rw [if_pos hσ.symm] at hrk'₂
    rw [if_pos hσ] at hrk''₂
    omega
  · refine Option.some.inj ?_
    rw [← h₁, ← h₂]
    exact commute_of_disjoint_frames st (Move.deckStack c) (Move.pileStack c')
      (fun f hf => by cases f <;> simp_all [Move.reads, Move.writes])
      (fun f hf => by cases f <;> simp_all [Move.reads, Move.writes])
      (fun f hf => by cases f <;> simp_all [Move.writes])

/-- `comm_deckStack_stackPile` (Commutation), re-derived and
STRENGTHENED (touch-disjointness dropped): different suits are
frame-disjoint; the same-suit case dies on the drop's truncated
subtraction (both orders legal forces the height past zero). -/
theorem comm_deckStack_stackPile_frame {st : State} {c c' : Card} {b' : Base} {st₂ st₃ : State}
    (h₁ : (st.apply (Move.deckStack c) >>= fun s => s.apply (Move.stackPile c' b')) = some st₂)
    (h₂ : (st.apply (Move.stackPile c' b') >>= fun s => s.apply (Move.deckStack c)) = some st₃) :
    st₂ = st₃ := by
  by_cases hσ : c.suit = c'.suit
  · exfalso
    obtain ⟨s₁, hDS, hSP⟩ := Option.bind_eq_some_iff.mp h₁
    obtain ⟨s₃, hSP', hDS'⟩ := Option.bind_eq_some_iff.mp h₂
    rw [apply_deckStack_iff] at hDS
    obtain ⟨hprev, hrk, hs₁⟩ := hDS
    rw [apply_stackPile_iff] at hSP
    obtain ⟨hrk', hcp', bd₂, hatt', hs₂⟩ := hSP
    rw [apply_stackPile_iff] at hSP'
    obtain ⟨hrk₂, hcp, bd₃, hatt₁, hs₃⟩ := hSP'
    rw [apply_deckStack_iff] at hDS'
    obtain ⟨hprev', hrk'', hs₄⟩ := hDS'
    rw [hs₁] at hrk'
    rw [hs₃] at hrk''
    have hrk'₂ : c'.rank.toIdx + 1
        = (if c'.suit = c.suit then st.heights c'.suit + 1 else st.heights c'.suit) := hrk'
    have hrk''₂ : c.rank.toIdx
        = (if c.suit = c'.suit then st.heights c.suit - 1 else st.heights c.suit) := hrk''
    rw [if_pos hσ.symm] at hrk'₂
    rw [if_pos hσ] at hrk''₂
    omega
  · refine Option.some.inj ?_
    rw [← h₁, ← h₂]
    exact commute_of_disjoint_frames st (Move.deckStack c) (Move.stackPile c' b')
      (fun f hf => by cases f <;> simp_all [Move.reads, Move.writes])
      (fun f hf => by cases f <;> simp_all [Move.reads, Move.writes])
      (fun f hf => by cases f <;> simp_all [Move.writes])

/-! ### The cursor-blindness API, re-derived -/

/-- `apply_nonConsuming_stock_invar` (Commutation), frame form: a
move that writes no stock frame keeps the stock bit-for-bit. -/
theorem apply_stock_invar_frame {m : Move} {st st₁ : State}
    (hw : Frame.stockCards ∉ m.writes ∧ Frame.stockCursor ∉ m.writes)
    (h : st.apply m = some st₁) : st₁.stock = st.stock :=
  cycle_ext (frame_invar h Frame.stockCards hw.1) (frame_invar h Frame.stockCursor hw.2)

/-- `apply_nonConsuming_cursor_blind` (Commutation), frame form: from
two states differing only in the stock cursor, a move that never reads
the stock frames replays with the results again differing only in the
cursor — the "replay the prefix verbatim" step of every pace lemma.
(The original's `draw` arm is NOT frame-covered — `draw` reads the
cursor — and stays with Commutation's `dealOnce_cards` argument.) -/
theorem apply_cursor_blind_frame {st st' st₁ : State} {m : Move}
    (hd : st.diffCursor st')
    (hr : Frame.stockCards ∉ m.reads ∧ Frame.stockCursor ∉ m.reads)
    (h : st.apply m = some st₁) :
    ∃ st₁', st'.apply m = some st₁' ∧ st₁.diffCursor st₁' := by
  have hr' : Frame.agrees m.reads st st' := by
    intro f hf
    cases f with
    | deal => exact hd.1
    | board => exact hd.2.1
    | heightsOf s => exact congrFun hd.2.2.1 s
    | depths => exact hd.2.2.2.1
    | stockCards => exact absurd hf hr.1
    | stockCursor => exact absurd hf hr.2
    | drawStep => exact hd.2.2.2.2.2
  obtain ⟨st₁', h1, h2⟩ := frame_congr hr' h
  refine ⟨st₁', h1, ?_⟩
  refine ⟨h2 Frame.deal hd.1, h2 Frame.board hd.2.1, ?_, h2 Frame.depths hd.2.2.2.1, ?_,
    h2 Frame.drawStep hd.2.2.2.2.2⟩
  · funext s
    exact h2 (Frame.heightsOf s) (congrFun hd.2.2.1 s)
  · show st₁.stock.cards = st₁'.stock.cards
    rw [frame_invar h Frame.stockCards (fun hmem => hr.1 (Move.writes_subset_reads m _ hmem)),
      hd.2.2.2.2.1]
    exact Frame.agree_symm (frame_congr_unread h1 Frame.stockCards hr.1)
/-! ## The per-card specialization — W3's `seatsOrReads`

ENDGAME §5 W3's excursion lemma needs a blindness predicate for the
intermediate segment γ: "no move in γ reads the dropped height or
`x`'s seat".  The HEIGHT half is frame-native — `Frame.heightsOf x.suit
∉ m.reads`, the extractor below.  The SEAT half is ENDGAME §7.2's
def-level choice; this file's answer:

`Move.seatsOrReads x m = true` iff `m`'s board-frame interaction
MENTIONS `x` — as the moved card, or as the base card of its target.
The move-only form is honest because every OTHER seat-read is
self-guarded by the source run's own legality (the lemmas below): with
`x` seated at `b`, no placement can target `b` (`canPlace` demands a
free base), and the run-root sitting at `b` is `x` itself (the
`bottomOf` round trip) — so a legal γ never reads the occupied seat
without mentioning `x`.  What stays genuinely state-dependent is the
`pilePile` run walk reading THROUGH `x`'s edge (`aboveOf`) — the W3
taker's φ simulation (below) handles it; its walk-agreement piece is
Board-level kit since R1 (`Board.aboveOf_congr` / `Board.aboveOf_sub`,
the `aboveOf_congr_off` generalization), and W3's one-step replay
itself landed in Theorems (`excursionSim_step`). -/

/-- Does the base (as a seat to land on) mention the card `x`? -/
def Base.seats (b : Base) (x : Card) : Bool :=
  match b with
  | Sum.inl _ => false
  | Sum.inr d => decide (d = x)

/-- The per-card frame specialization: does `m`'s board-frame
interaction mention `x` — as the moved card, or as the base card of
its target?  (`deckStack` never touches the board; `draw` never
does.) -/
def Move.seatsOrReads (x : Card) : Move → Bool
  | .draw => false
  | .reveal c => decide (c = x)
  | .deckPile c b => decide (c = x) || b.seats x
  | .deckStack _ => false
  | .pileStack c => decide (c = x)
  | .stackPile c b => decide (c = x) || b.seats x
  | .pilePile c b => decide (c = x) || b.seats x

/-- The height-cell extractor (W3's `cSuitMove`, frame-native): a move
reads suit `s`'s height iff it is a foundation move of an `s`-suit
card — `draw`, `reveal`, `deckPile`, `pilePile` never read heights. -/
theorem Move.heightsOf_mem_reads_iff (s : Suit) : ∀ (m : Move),
    Frame.heightsOf s ∈ m.reads ↔
      match m with
      | .deckStack c | .pileStack c | .stackPile c _ => s = c.suit
      | _ => False := by
  intro m
  cases m with
  | draw => simp [Move.reads]
  | reveal c => simp [Move.reads]
  | deckPile c b => simp [Move.reads]
  | deckStack c => simp [Move.reads]
  | pileStack c => simp [Move.reads]
  | stackPile c b => simp [Move.reads]
  | pilePile c b => simp [Move.reads]

/-- The suit-cell blindness (W3's height half, as a frame instance): a
move that never reads suit `σ`'s height is blind to it — legality and
successor both, with the `σ`-cell carried from the source.  The
excursion pair's dropped height is invisible to exactly the
`seatsOrReads`-clean, `x`-suit-blind γ. -/
theorem apply_heights_blind {m : Move} {st s₁ : State} {σ : Suit} {hσ : Nat}
    (hread : Frame.heightsOf σ ∉ m.reads)
    (h : st.apply m = some s₁) :
    ({ st with heights := fun s => if s = σ then hσ else st.heights s } : State).apply m
      = some { s₁ with heights := fun s => if s = σ then hσ else s₁.heights s } := by
  have hr : Frame.agrees m.reads st
      { st with heights := fun s => if s = σ then hσ else st.heights s } := by
    intro f hf
    cases f with
    | deal => rfl
    | board => rfl
    | heightsOf s =>
        show st.heights s = (if s = σ then hσ else st.heights s)
        rw [if_neg (fun hcon => hread (by rw [← hcon]; exact hf))]
    | depths => rfl
    | stockCards => rfl
    | stockCursor => rfl
    | drawStep => rfl
  obtain ⟨s₁', h1, h2⟩ := frame_congr hr h
  have he : s₁' = { s₁ with heights := fun s => if s = σ then hσ else s₁.heights s } := by
    apply state_ext_of_frames
    intro f
    cases f with
    | deal => exact Frame.agree_symm (h2 Frame.deal rfl)
    | board => exact Frame.agree_symm (h2 Frame.board rfl)
    | heightsOf s =>
        show s₁'.heights s = (if s = σ then hσ else s₁.heights s)
        by_cases hss : s = σ
        · rw [hss, if_pos rfl]
          have hu : s₁'.heights σ = (if σ = σ then hσ else st.heights σ) :=
            frame_congr_unread h1 (Frame.heightsOf σ) hread
          rw [if_pos rfl] at hu
          exact hu
        · rw [if_neg hss]
          exact Frame.agree_symm (h2 (Frame.heightsOf s)
            (by show st.heights s = (if s = σ then hσ else st.heights s)
                rw [if_neg hss]))
    | depths => exact Frame.agree_symm (h2 Frame.depths rfl)
    | stockCards => exact Frame.agree_symm (h2 Frame.stockCards rfl)
    | stockCursor => exact Frame.agree_symm (h2 Frame.stockCursor rfl)
    | drawStep => exact Frame.agree_symm (h2 Frame.drawStep rfl)
  rw [he] at h1
  exact h1

/-! ### Why the move-only form is honest — the self-guarding lemmas -/

/-- Self-guarding I: with `x` seated at `b`, no placement can target
`b` — `canPlace` demands a free base.  This is why `seatsOrReads` needs
no seat witness: in a legal source run, γ's placements never read the
occupied seat. -/
theorem canPlace_eq_false_of_seated {st : State} {c x : Card} {b : Base}
    (hseat : st.board.topOf b = some x) : st.canPlace c b = false := by
  show (decide (st.board.topOf b = none) && _) = false
  rw [hseat]
  simp

/-- Self-guarding II: the base under `c` really has `c` on top — so
the run-root sitting at `x`'s seat is `x` itself (excluded by
`seatsOrReads`' card arm), and a `pileStack`/`pilePile` detaching at
`x`'s seat is a move mentioning `x`. -/
theorem topOf_of_bottomOf {bd : Board} {c : Card} {b : Base}
    (hbot : bd.bottomOf c = some b) : bd.topOf b = some c :=
  (Board.bottomOf_eq bd c b).mp hbot

/- Self-guarding III: nothing can be attached ON `x` (the cell
`Sum.inr x`) while `x` is foundation-passed in the replay — `attach`
demands the card unplaced, and in the source run the only way onto
`x` is a move whose base mentions `x` (the `b.seats x` arm).  Together
with I and II, every γ-seat-read either mentions `x` or dies in the
source run. -/

/-- The W3 replay simulation's state relation (ENDGAME §7.2's φ — the
interface handed to the W3 taker): `τ` is `σ` with `x`'s single board
edge removed and the `x`-suit height one higher (the excursion's
dropped height restored).  The one-step replay for a γ of
`seatsOrReads x = false`, height-cell-blind moves is the remaining W3
kit piece: the board edits are single-base updates away from `b`
(self-guarding I), so they commute with the `detach b` (the
attach/detach commutations), the heights and stock transfer by
`apply_heights_blind` / `frame_invar`, and the `aboveOf` walk
agreement is Board-level kit since R1 (`Board.aboveOf_congr` /
`Board.aboveOf_sub`) — the one-step replay itself landed in Theorems
(`excursionSim_step`). -/
def excursionSim (x : Card) (b : Base) (σ τ : State) : Prop :=
  σ.deal = τ.deal ∧ σ.depths = τ.depths ∧ σ.stock = τ.stock ∧ σ.drawStep = τ.drawStep ∧
    σ.heights x.suit + 1 = τ.heights x.suit ∧
    (∀ s, s ≠ x.suit → σ.heights s = τ.heights s) ∧
    σ.board.topOf b = some x ∧ τ.board = σ.board.detach b ∧ σ.board.topOf (Sum.inr x) = none

/-! ## The honest boundary

What this file's laws DO subsume, with the guards derived:

* the blindness kit (`reveal_blind_*`, `pilePile_blind_*`,
  `deckStack_blind_*`, `pileStack/stackPile_blind_*` — the wrappers
  above);
* the whole coarse commutation layer `commute_of_compsDisjoint` (the
  twelve genuinely disjoint pairs: the four `draw_comm_*` and
  `reveal_deckStack_comm_frame`/`deckStack_pilePile_comm_frame` with
  their symmetries — the frame-disjointness grid over the 49 pairs
  returns exactly these);
* the hnc guard of `commute_of_disjoint_touch` (`deal_commutes_nonStock_frame`:
  the non-consuming condition IS "no stock frames in reads" — the
  guard is derived, not assumed);
* the cursor-blindness API (`apply_nonConsuming_cursor_blind`'s
  non-draw sector, `apply_nonConsuming_stock_invar`).

What they do NOT subsume — recorded, not forced:

* the fourteen `comm_*` pair lemmas that interact INSIDE the board
  frame (reveal·deckPile/pileStack/stackPile/pilePile/reveal,
  deckPile·{pileStack, stackPile, pilePile}, pileStack·{pileStack,
  stackPile, pilePile}, stackPile·{stackPile, pilePile},
  pilePile·pilePile): their commutation is per-base (attach/detach at
  distinct bases) and per-card (seat transfers), which a pure
  move→frames function cannot see — `isVis c` reads the seat of `c`,
  an arbitrary board cell.  That refinement IS `Move.touch`
  (Commutation): reads with card witnesses.  The two exceptions,
  `comm_deckStack_pileStack/stackPile`, fall out because `deckStack`
  never touches the board and the per-suit height split suffices —
  they are re-derived above, with the touch-disjointness hypothesis
  dropped.
* `draw`·`draw`: not frame-disjoint (a move never frame-commutes with
  itself when it writes anything) — the trivial same-term case.
* the W3 one-step replay through `excursionSim`: stated, not proven
  here — proven in Theorems (`excursionSim_step`, 2026-09-14); the
  walk-agreement lemma it needed is Board-level kit since R1
  (`Board.aboveOf_congr` / `Board.aboveOf_sub`).

-/
