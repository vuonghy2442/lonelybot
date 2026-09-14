import Klondike.TwinSwap

/-!
# The twin pair, both-cargo exchange (wave 15)

The engine's twin-transposition reasoning at the both-occupied shape:
states A (cargo `z` on twin `t`, cargo `z'` on twin `t'`) and B (the two
cargos exchanged, everything else untouched) are solvability-equivalent
*without* the exchange being executable — no legal `pilePile` can swap
both cargos while both seats are taken (`canPlace` demands a bare
target), and the seats themselves never move.  Wave 14's
`State.solvable_cargoTwin` (TwinSwap.lean) is exactly the one-bare-twin
boundary case of this claim, discharged by an executable transfer; the
rows below remove executability from the statement.

The state-transform: `Board.exchangeTwin` swaps the two twin seats'
VALUES — `topOf := bd.topOf ∘ (·.swapTwin t)` — because the cargo
stacks ride (every card above a cargo root names its own seat, so only
the two root edges change; anchors and all other bases are untouched).
`State.exchangeTwinCargo` lifts it to states board-only: the deal,
heights, depths, stock and draw step are untouched ("everything else
untouched", made structural).  The kit is proven: the pointwise
characterization, the involution, the `bottomOf` seat-swap law, and the
two transfer realizations of the exchange (`pilePile_exchangeTwinCargo_fwd`,
`exchangeTwinCargo_pilePile_back` — the detach/attach composite IS the
two-slot swap, both directions, given the bare premise).

**LANDED (2026-09-14)**: the one-bare-twin companion
(`solvable_cargoTwin_exchange_bare`) — proven via the *backward*
realization: from the exchanged state, the cargo's `pilePile` onto its
original twin is legal (that seat is bare by construction, the host
visible, the fit carried) and lands exactly on the original state — so
the exchange is one move away from the original, and the original's
winning play replays through it.  The twin card is never consulted,
which is why no visibility or zone premise survives: the statement is
strictly stronger than the scaffold planned (its `hzone` case split and
`hwf` were dropped).  This subsumes wave 14's coverage of the visible
twin and settles the forward direction at every phantom-twin shape
(stocked, buried, foundationed) at once.

**REMAINING**: the both-occupied row (`solvable_cargoTwin_exchange`) —
the scheduling argument below.

## The proof shape (the scheduling argument, three links)

1. **Frozen-phase mirroring**: while both seats are occupied, replay
   the winning play in the exchanged state, maintaining the invariant
   that the two states differ only at the two twin seats
   (`exchangeTwin_topOf` is the invariant's witness function).  Landings
   on the twin seats are rejected in both threads (`canPlace` demands a
   bare seat); the subtlety is the run walk — a walk passing the CARD
   `t` reads the `inr t` seat and so continues into the OTHER thread's
   cargo — so the correspondence is structural, not the same move: a
   `pilePile` landing a run on a cargo's top maps to the move landing
   it on the OTHER cargo's top (`canSitOn_swapTwin_right/_left` is the
   fit transfer, `Board.aboveOf_congr_off` the walk congruence off the
   exchanged seats).
2. **Bridge at the first freedom**: the instant a cargo's run leaves
   its twin (a `pilePile` of the run's root, or the cargo's own
   `pileStack`), both threads have one occupied and one bare seat —
   `State.solvable_cargoTwin` (TwinSwap.lean, proven) transfers the
   remaining cargo, and the identification "the post-transfer state IS
   the exchange" (`pilePile_exchangeTwinCargo_fwd`, LANDED) merges the
   threads literally.
3. **Tails coincide**: post-bridge the states are equal and the tail
   replays verbatim.  Even with no freedom ever (the cargos ride to the
   end), the height-writing moves mirror exactly, so a terminal win
   transfers — no "freedom must exist" premise is needed.

## Refute-first gate (run BEFORE farming the remaining row)

The corner: **deal-inherited cargo/host adjacency**.  The `hfit`
premises below are the anticipated repair — without them the bridge's
transfer dies at `canSitOn` (the Bridge.lean:466 trap shape: the deal
stacks non-fitting pairs, and the game cannot re-seat across them).
Witness-hunt first: a both-occupied state where some `canSitOn z t` is
false and solvability diverges between `st` and
`st.exchangeTwinCargo t` kills the premiseless form and confirms the
repair; no divergence found weakens the premise.  (The companion's
direction question is settled in the strong direction — proven with no
zone premise; the reverse `stx → st` at invisible twins remains the open
half, candidate stuck shape in FARM_MEMORY's wave-15 note.)
-/

/-! ## The substrate (proven; cite these, don't re-derive) -/

/-- Injectivity for the two-slot value swap (mirrors `mapByTwin_inj`:
`bd.inj` plus the `Base.swapTwin` involution only). -/
theorem Board.exchangeTwin_inj (bd : Board) (t : Card) :
    ∀ (b₁ b₂ : Base) (c : Card), bd.topOf (b₁.swapTwin t) = some c →
      bd.topOf (b₂.swapTwin t) = some c → b₁ = b₂ := by
  intro b₁ b₂ c h₁ h₂
  have hb : b₁.swapTwin t = b₂.swapTwin t := bd.inj _ _ c h₁ h₂
  have hb2 := congrArg (fun b => b.swapTwin t) hb
  rw [Base.swapTwin_swapTwin, Base.swapTwin_swapTwin] at hb2
  exact hb2

/-- **The both-cargo exchange at the board level**: the two twin seats'
values swap — the cargo stacks ride, because only the two root edges
change (every card above a cargo root names its own seat).  Total and
guard-free: swapping values at two bases of a matching is a matching,
whatever sits (or does not sit) at the seats — the one-bare-twin
companion shape included, an empty stack riding for free. -/
def Board.exchangeTwin (bd : Board) (t : Card) : Board where
  topOf := fun b => bd.topOf (b.swapTwin t)
  inj := Board.exchangeTwin_inj bd t

@[simp] theorem Board.exchangeTwin_topOf (bd : Board) (t : Card) (b : Base) :
    (bd.exchangeTwin t).topOf b = bd.topOf (b.swapTwin t) := rfl

/-- The exchange is an involution (the seat swap twice is the identity). -/
theorem Board.exchangeTwin_exchangeTwin (bd : Board) (t : Card) :
    (bd.exchangeTwin t).exchangeTwin t = bd := by
  apply Board.ext_topOf
  funext b
  simp only [Board.exchangeTwin_topOf, Base.swapTwin_swapTwin]

/-- The seat-swap law for the derived search: under the exchange, a
card's base is its old base with the seat swapped (`bottomOf` is a
`findFirst` over `enumBase`, so the law goes through `bottomOf_eq`). -/
theorem Board.bottomOf_exchangeTwin (bd : Board) (t : Card) (c : Card) :
    (bd.exchangeTwin t).bottomOf c = (bd.bottomOf c).map (fun b => b.swapTwin t) := by
  cases hb : bd.bottomOf c with
  | none =>
      refine (Board.bottomOf_eq_none _ c).mpr (fun b hbi => ?_)
      rw [Board.exchangeTwin_topOf] at hbi
      exact (Board.bottomOf_eq_none _ c).mp hb _ hbi
  | some b =>
      show (bd.exchangeTwin t).bottomOf c = some (b.swapTwin t)
      refine (Board.bottomOf_eq _ _ _).mpr ?_
      rw [Board.exchangeTwin_topOf, Base.swapTwin_swapTwin]
      exact (Board.bottomOf_eq _ _ _).mp hb

/-- **The both-cargo exchange at the state level**: the board's two twin
seats swap values; everything else is untouched. -/
def State.exchangeTwinCargo (st : State) (t : Card) : State :=
  { st with board := st.board.exchangeTwin t }

@[simp] theorem State.exchangeTwinCargo_board (st : State) (t : Card) :
    (st.exchangeTwinCargo t).board = st.board.exchangeTwin t := rfl

theorem State.exchangeTwinCargo_deal (st : State) (t : Card) :
    (st.exchangeTwinCargo t).deal = st.deal := rfl

theorem State.exchangeTwinCargo_heights (st : State) (t : Card) :
    (st.exchangeTwinCargo t).heights = st.heights := rfl

theorem State.exchangeTwinCargo_depths (st : State) (t : Card) :
    (st.exchangeTwinCargo t).depths = st.depths := rfl

theorem State.exchangeTwinCargo_stock (st : State) (t : Card) :
    (st.exchangeTwinCargo t).stock = st.stock := rfl

theorem State.exchangeTwinCargo_drawStep (st : State) (t : Card) :
    (st.exchangeTwinCargo t).drawStep = st.drawStep := rfl

/-- The exchange is an involution at the state level too. -/
theorem State.exchangeTwinCargo_exchangeTwinCargo (st : State) (t : Card) :
    (st.exchangeTwinCargo t).exchangeTwinCargo t = st := by
  apply state_ext
  · rfl
  · exact Board.exchangeTwin_exchangeTwin st.board t
  · rfl
  · rfl
  · rfl
  · rfl

/-! ## The transfer realizations of the exchange (the identification)

The two lemmas the rows' routes cite: the `pilePile` transfer (forward
from `st`, backward from the exchange) realizes and inverts
`exchangeTwinCargo` at the one-bare-twin shape — the detach/attach
composite IS the two-slot swap.  The backward direction is the surprise
that closed the companion: its guards never consult the twin card
itself, so no visibility/zone premise is needed. -/

/-- The seat swap fixes every base outside the twin pair (anchors, and
every card seat off the pair). -/
theorem Base.swapTwin_eq_self {t : Card} {b : Base}
    (h₁ : b ≠ Sum.inr t) (h₂ : b ≠ Sum.inr t.flipSuit) : b.swapTwin t = b := by
  cases b with
  | inl a => rfl
  | inr x =>
      show Sum.inr (Card.swapTwin t x) = Sum.inr x
      rw [Card.swapTwin_of_ne (fun h => h₁ (by rw [h])) (fun h => h₂ (by rw [h]))]

/-- **The forward realization**: with a bare, visible twin seat, the
executable transfer `pilePile z (inr t')` from `st` lands exactly on
`st.exchangeTwinCargo t`.  Wave 14's `solvable_cargoTwin` applies
whenever its executability premise holds; this lemma identifies the
post-transfer state with the exchange, which is what the main row's
bridge step consumes. -/
theorem State.pilePile_exchangeTwinCargo_fwd {st : State} {z t : Card}
    (hvis' : st.isVis t.flipSuit = true)
    (h₀ : st.board.bottomOf z = some (Sum.inr t))
    (hbare : st.board.topOf (Sum.inr t.flipSuit) = none)
    (hfit : canSitOn z t = true)
    (hnb : t.flipSuit ∉ st.board.aboveOf z) :
    st.apply (Move.pilePile z (Sum.inr t.flipSuit)) = some (st.exchangeTwinCargo t) := by
  have hztop : st.board.topOf (Sum.inr t) = some z := (Board.bottomOf_eq _ _ _).mp h₀
  have hsw' : Base.swapTwin t (Sum.inr t) = Sum.inr t.flipSuit := by
    show Sum.inr (Card.swapTwin t t) = Sum.inr t.flipSuit
    rw [Card.swapTwin_self_left]
  have hsw : Base.swapTwin t (Sum.inr t.flipSuit) = Sum.inr t := by
    show Sum.inr (Card.swapTwin t t.flipSuit) = Sum.inr t
    rw [Card.swapTwin_self_right]
  have hcs' : canSitOn z t.flipSuit = true := by
    rw [show t.flipSuit = Card.swapTwin t t from (Card.swapTwin_self_left t).symm,
      canSitOn_swapTwin_right]
    exact hfit
  have hcp' : st.canPlace z (Sum.inr t.flipSuit) = true := by
    rw [State.canPlace]
    show (decide (st.board.topOf (Sum.inr t.flipSuit) = none) &&
        (st.isVis t.flipSuit && canSitOn z t.flipSuit)) = true
    rw [hbare, hvis', hcs']
    rfl
  have hcmr' : st.canMoveRun z (Sum.inr t.flipSuit) = true := by
    rw [State.canMoveRun]
    show (st.canPlace z (Sum.inr t.flipSuit) &&
        !(st.board.aboveOf z).contains t.flipSuit) = true
    rw [hcp', lcontains_false_of_notMem hnb]
    rfl
  have hdetT' : (st.board.detach (Sum.inr t)).topOf (Sum.inr t.flipSuit) = none := by
    rw [Board.detach_topOf_ne _ _ _ (fun h => Card.flipSuit_ne t (Sum.inr.inj h))]
    exact hbare
  have hbotD : (st.board.detach (Sum.inr t)).bottomOf z = none :=
    Board.bottomOf_detach_self hztop
  rw [apply_pilePile_iff]
  refine ⟨Sum.inr t, h₀, fun h => Card.flipSuit_ne t (Sum.inr.inj h).symm, hcmr',
    st.board.exchangeTwin t, ?_, rfl⟩
  unfold Board.attach
  rw [dif_pos hdetT', dif_pos hbotD]
  apply congrArg Option.some
  apply Board.ext_topOf
  funext base
  dsimp only
  by_cases hbt' : base = Sum.inr t.flipSuit
  · rw [hbt', Board.update_self, Board.exchangeTwin_topOf, hsw]
    exact hztop.symm
  · rw [Board.update_ne _ _ _ _ hbt']
    by_cases hbt : base = Sum.inr t
    · rw [hbt, Board.detach_topOf, Board.exchangeTwin_topOf, hsw']
      exact hbare.symm
    · rw [Board.detach_topOf_ne _ _ _ hbt, Board.exchangeTwin_topOf,
        Base.swapTwin_eq_self hbt hbt']

/-- **The backward realization**: from the exchanged state, the cargo's
`pilePile` back onto its original twin fires and lands on the original
state — the exchange's one-move inverse.  The guards read only the (now
bare) original seat, the host's visibility (carried across the exchange
by the `bottomOf` seat-swap law), and the fit; the run walk agrees by
`aboveOf_congr_off` (the run above the cargo visits neither twin — the
no-braid premises).  The twin card itself is never consulted — which is
what makes the companion below hold with no visibility or zone premise
at all. -/
theorem State.exchangeTwinCargo_pilePile_back {st : State} {z t : Card}
    (hvis : st.isVis t = true)
    (h₀ : st.board.bottomOf z = some (Sum.inr t))
    (hbare : st.board.topOf (Sum.inr t.flipSuit) = none)
    (hfit : canSitOn z t = true)
    (hnb : t ∉ st.board.aboveOf z ∧ t.flipSuit ∉ st.board.aboveOf z) :
    (st.exchangeTwinCargo t).apply (Move.pilePile z (Sum.inr t)) = some st := by
  have hztop : st.board.topOf (Sum.inr t) = some z := (Board.bottomOf_eq _ _ _).mp h₀
  have hsw' : Base.swapTwin t (Sum.inr t) = Sum.inr t.flipSuit := by
    show Sum.inr (Card.swapTwin t t) = Sum.inr t.flipSuit
    rw [Card.swapTwin_self_left]
  have hsw : Base.swapTwin t (Sum.inr t.flipSuit) = Sum.inr t := by
    show Sum.inr (Card.swapTwin t t.flipSuit) = Sum.inr t
    rw [Card.swapTwin_self_right]
  have hzt : z ≠ t := by
    obtain ⟨hrk, -⟩ := (canSitOn_eq _ _).mp hfit
    intro hcon
    subst hcon
    omega
  have hcs' : canSitOn z t.flipSuit = true := by
    rw [show t.flipSuit = Card.swapTwin t t from (Card.swapTwin_self_left t).symm,
      canSitOn_swapTwin_right]
    exact hfit
  have hzt' : z ≠ t.flipSuit := by
    obtain ⟨hrk, -⟩ := (canSitOn_eq _ _).mp hcs'
    intro hcon
    subst hcon
    omega
  have hgt : (st.exchangeTwinCargo t).board.topOf (Sum.inr t) = none := by
    rw [State.exchangeTwinCargo_board, Board.exchangeTwin_topOf, hsw']
    exact hbare
  have hgz : (st.exchangeTwinCargo t).board.topOf (Sum.inr t.flipSuit) = some z := by
    rw [State.exchangeTwinCargo_board, Board.exchangeTwin_topOf, hsw]
    exact hztop
  have hbotE : (st.exchangeTwinCargo t).board.bottomOf z = some (Sum.inr t.flipSuit) := by
    rw [State.exchangeTwinCargo_board, Board.bottomOf_exchangeTwin, h₀]
    show some (Base.swapTwin t (Sum.inr t)) = some (Sum.inr t.flipSuit)
    rw [hsw']
  have hvisb : (st.exchangeTwinCargo t).isVis t = true := by
    obtain ⟨β, hβ⟩ := Option.isSome_iff_exists.mp hvis
    rw [State.isVis, State.exchangeTwinCargo_board, Board.bottomOf_exchangeTwin, hβ]
    rfl
  have hagree : ∀ x : Card, x ≠ t → x ≠ t.flipSuit →
      st.board.topOf (Sum.inr x) = (st.exchangeTwinCargo t).board.topOf (Sum.inr x) := by
    intro x hx₁ hx₂
    rw [State.exchangeTwinCargo_board, Board.exchangeTwin_topOf,
      Base.swapTwin_eq_self (fun h => hx₁ (Sum.inr.inj h))
        (fun h => hx₂ (Sum.inr.inj h))]
  have habove : (st.exchangeTwinCargo t).board.aboveOf z = st.board.aboveOf z :=
    Board.aboveOf_congr_off hagree
      (fun x hx => ⟨fun h => hnb.1 (h ▸ hx), fun h => hnb.2 (h ▸ hx)⟩)
      ⟨hzt, hzt'⟩
  have hcp : (st.exchangeTwinCargo t).canPlace z (Sum.inr t) = true := by
    rw [State.canPlace]
    show (decide ((st.exchangeTwinCargo t).board.topOf (Sum.inr t) = none) &&
        ((st.exchangeTwinCargo t).isVis t && canSitOn z t)) = true
    rw [hgt, hvisb, hfit]
    rfl
  have hcmr : (st.exchangeTwinCargo t).canMoveRun z (Sum.inr t) = true := by
    rw [State.canMoveRun]
    show ((st.exchangeTwinCargo t).canPlace z (Sum.inr t) &&
        !((st.exchangeTwinCargo t).board.aboveOf z).contains t) = true
    rw [hcp, habove, lcontains_false_of_notMem hnb.1]
    rfl
  have hdetT : ((st.exchangeTwinCargo t).board.detach (Sum.inr t.flipSuit)).topOf
      (Sum.inr t) = none := by
    rw [Board.detach_topOf_ne _ _ _ (fun h => Card.flipSuit_ne t (Sum.inr.inj h).symm)]
    exact hgt
  have hbotD : ((st.exchangeTwinCargo t).board.detach (Sum.inr t.flipSuit)).bottomOf z = none :=
    Board.bottomOf_detach_self hgz
  rw [apply_pilePile_iff]
  refine ⟨Sum.inr t.flipSuit, hbotE, fun h => Card.flipSuit_ne t (Sum.inr.inj h), hcmr,
    st.board, ?_, rfl⟩
  unfold Board.attach
  rw [dif_pos hdetT, dif_pos hbotD]
  apply congrArg Option.some
  apply Board.ext_topOf
  funext base
  dsimp only
  by_cases hbt : base = Sum.inr t
  · rw [hbt, Board.update_self]
    exact hztop.symm
  · rw [Board.update_ne _ _ _ _ hbt]
    by_cases hbt' : base = Sum.inr t.flipSuit
    · rw [hbt', Board.detach_topOf]
      exact hbare.symm
    · rw [Board.detach_topOf_ne _ _ _ hbt', State.exchangeTwinCargo_board,
        Board.exchangeTwin_topOf, Base.swapTwin_eq_self hbt hbt']

/-! ## Route support (the [H] row's structural facts) -/

/-- **The seat lock**: a card's only landing seats are the twins of its
current host — the run rooted at `z` can never leave `inr t` except for
the other twin (or the foundation, via `pileStack`).  The rank/color
dual of `Card.only_blocker_is_twin` (which bounds the tenants of a
base; this bounds the hosts of a tenant).  Canonical home Basic.lean
(the consolidation queue's). -/
theorem canSitOn_hosts_are_twins {z t d : Card}
    (hfit : canSitOn z t = true) (hfitd : canSitOn z d = true) :
    d = t ∨ d = t.flipSuit := by
  rcases z with ⟨⟨zc, _⟩, zr⟩
  rcases t with ⟨⟨tc, tp⟩, tr⟩
  rcases d with ⟨⟨dc, dp⟩, dr⟩
  obtain ⟨h1, h2⟩ := (canSitOn_eq _ _).mp hfit
  obtain ⟨h3, h4⟩ := (canSitOn_eq _ _).mp hfitd
  have h1' : zr.toIdx + 1 = tr.toIdx := h1
  have h3' : zr.toIdx + 1 = dr.toIdx := h3
  have h2' : zc ≠ tc := h2
  have h4' : zc ≠ dc := h4
  have hrank : dr = tr := Rank.toIdx_inj (by omega)
  have hcolor : dc = tc := by
    cases tc <;> cases dc <;> cases zc <;> simp_all
  subst hrank hcolor
  cases tp <;> cases dp <;> simp [Card.flipSuit, Suit.flipPair]

/-! ### The pair lemmas (the exchange's symmetry group)

`Card.swapTwin_flipSuit`/`Base.swapTwin_flipSuit` live in
Klondike/Relabel.lean (the canonical home, below the Theorems chain). -/

/-- Hence the twin's exchange is the same exchange. -/
theorem Board.exchangeTwin_flipSuit (bd : Board) (t : Card) :
    bd.exchangeTwin t.flipSuit = bd.exchangeTwin t := by
  apply Board.ext_topOf
  funext b
  show bd.topOf (b.swapTwin t.flipSuit) = bd.topOf (b.swapTwin t)
  rw [Base.swapTwin_flipSuit]

theorem State.exchangeTwinCargo_flipSuit (st : State) (t : Card) :
    st.exchangeTwinCargo t.flipSuit = st.exchangeTwinCargo t := by
  apply state_ext
  · rfl
  · show st.board.exchangeTwin t.flipSuit = st.board.exchangeTwin t
    rw [Board.exchangeTwin_flipSuit]
  · rfl
  · rfl
  · rfl
  · rfl

/-- **The detach-at-twin congruence**: detaching the exchanged board at
one twin seat is the exchange of the detach at the other — the freedom
move (`pileStack` of a cargo, detaching at its host) mirrors across the
exchange by this lemma. -/
theorem Board.exchangeTwin_detach (bd : Board) (t : Card) :
    (bd.exchangeTwin t).detach (Sum.inr t.flipSuit) =
      (bd.detach (Sum.inr t)).exchangeTwin t := by
  have hsw : Base.swapTwin t (Sum.inr t.flipSuit) = Sum.inr t := by
    show Sum.inr (Card.swapTwin t t.flipSuit) = Sum.inr t
    rw [Card.swapTwin_self_right]
  have hsw' : Base.swapTwin t (Sum.inr t) = Sum.inr t.flipSuit := by
    show Sum.inr (Card.swapTwin t t) = Sum.inr t.flipSuit
    rw [Card.swapTwin_self_left]
  apply Board.ext_topOf
  funext b
  by_cases hbt' : b = Sum.inr t.flipSuit
  · rw [hbt', Board.detach_topOf, Board.exchangeTwin_topOf, hsw, Board.detach_topOf]
  · by_cases hbt : b = Sum.inr t
    · rw [hbt,
        Board.detach_topOf_ne _ _ _ (fun h => Card.flipSuit_ne t (Sum.inr.inj h).symm),
        Board.exchangeTwin_topOf, hsw', Board.exchangeTwin_topOf, hsw',
        Board.detach_topOf_ne _ _ _ (fun h => Card.flipSuit_ne t (Sum.inr.inj h))]
    · rw [Board.detach_topOf_ne _ _ _ hbt', Board.exchangeTwin_topOf,
        Base.swapTwin_eq_self hbt hbt', Board.exchangeTwin_topOf,
        Base.swapTwin_eq_self hbt hbt', Board.detach_topOf_ne _ _ _ hbt]

/-- **The detach congruence off the twin pair**: detaching at any
non-twin base commutes with the exchange. -/
theorem Board.exchangeTwin_detach_ne (bd : Board) (t : Card) {b : Base}
    (hb : b ≠ Sum.inr t) (hb' : b ≠ Sum.inr t.flipSuit) :
    (bd.exchangeTwin t).detach b = (bd.detach b).exchangeTwin t := by
  have hfix : b.swapTwin t = b := Base.swapTwin_eq_self hb hb'
  apply Board.ext_topOf
  funext base
  by_cases hbb : base = b
  · rw [hbb, Board.detach_topOf, Board.exchangeTwin_topOf, hfix, Board.detach_topOf]
  · rw [Board.detach_topOf_ne _ _ _ hbb, Board.exchangeTwin_topOf,
      Board.exchangeTwin_topOf, Board.detach_topOf_ne _ _ _
        (fun h => hbb (by
          have h2 := Base.swapTwin_swapTwin t base
          rw [h, hfix] at h2
          exact h2.symm))]

/-- **The attach congruence off the twin pair**: attaching at any
non-twin base commutes with the exchange (both sides fire together, and
the results are exchanged). -/
theorem Board.exchangeTwin_attach_ne (bd : Board) (t : Card) {b : Base} {c : Card}
    {bd' : Board} (hb : b ≠ Sum.inr t) (hb' : b ≠ Sum.inr t.flipSuit)
    (hatt : bd.attach b c = some bd') :
    (bd.exchangeTwin t).attach b c = some (bd'.exchangeTwin t) := by
  have hfix : b.swapTwin t = b := Base.swapTwin_eq_self hb hb'
  have hne : bd.attach b c ≠ none := by
    intro h
    rw [hatt] at h
    simp at h
  obtain ⟨hg1, hg2⟩ := (Board.attach_eq_some_iff _ _ _).mp hne
  have hg1' : (bd.exchangeTwin t).topOf b = none := by
    rw [Board.exchangeTwin_topOf, hfix]
    exact hg1
  have hg2' : (bd.exchangeTwin t).bottomOf c = none := by
    rw [Board.bottomOf_exchangeTwin, hg2]
    rfl
  unfold Board.attach
  rw [dif_pos hg1', dif_pos hg2']
  apply congrArg Option.some
  apply Board.ext_topOf
  funext base
  dsimp only
  by_cases hbb : base = b
  · rw [hbb, Board.update_self, Board.exchangeTwin_topOf, hfix, Board.attach_topOf _ _ _ hatt]
  · rw [Board.update_ne _ _ _ _ hbb, Board.exchangeTwin_topOf,
      Board.exchangeTwin_topOf, Board.attach_topOf_ne _ _ _ hatt
        (fun h => hbb (by
          have h2 := Base.swapTwin_swapTwin t base
          rw [h, hfix] at h2
          exact h2.symm))]

/-! ### The freedom-first bridge (the scheduling induction's base case) -/

/-- **The freedom-first bridge**: when the winning play's first move is
already the cargo's `pileStack z`, the exchanged state is solvable — it
plays the SAME `pileStack z` (the guards are common: z's bareness and
the rung; the base is the twin seat either way), landing on
`A₁.exchangeTwinCargo t` by the detach congruence; then the REMAINING
cargo's backward transfer (`exchangeTwinCargo_pilePile_back`, at the
flipped roles — `exchangeTwinCargo_flipSuit` identifies the two
exchanges) returns to `A₁` literally, and the tail replays verbatim.
The no-braid premise transfers across `pileStack z`: the move touches
only z's own run and the seat `inr t`, which the walk from `z'` never
reads.  The z'-side freedom (`pileStack z'` first) is this same lemma
at the flipped roles. -/
theorem State.solvable_of_exchange_pileStack {st : State} {z z' t : Card}
    (hfit : canSitOn z t = true)
    (hvis' : st.isVis t.flipSuit = true)
    (h₀ : st.board.bottomOf z = some (Sum.inr t))
    (h₀' : st.board.bottomOf z' = some (Sum.inr t.flipSuit))
    (hfit' : canSitOn z' t.flipSuit = true)
    (hnb' : t ∉ st.board.aboveOf z' ∧ t.flipSuit ∉ st.board.aboveOf z')
    {A₁ : State} (hstep : st.apply (Move.pileStack z) = some A₁)
    (hwin : A₁.solvableFrom) :
    (st.exchangeTwinCargo t).solvableFrom := by
  obtain ⟨π, w, hrun, hwinw⟩ := hwin
  rw [apply_pileStack_iff] at hstep
  obtain ⟨htop, b₀, hb₀, hrk, hA₁⟩ := hstep
  have hbt : b₀ = Sum.inr t := Option.some.inj (hb₀.symm.trans h₀)
  subst hbt
  have hztop : st.board.topOf (Sum.inr t) = some z := (Board.bottomOf_eq _ _ _).mp h₀
  have hzt : z ≠ t := by
    obtain ⟨hrkz, -⟩ := (canSitOn_eq _ _).mp hfit
    intro hcon
    subst hcon
    omega
  have hcs' : canSitOn z t.flipSuit = true := by
    rw [show t.flipSuit = Card.swapTwin t t from (Card.swapTwin_self_left t).symm,
      canSitOn_swapTwin_right]
    exact hfit
  have hzt' : z ≠ t.flipSuit := by
    obtain ⟨hrkz, -⟩ := (canSitOn_eq _ _).mp hcs'
    intro hcon
    subst hcon
    omega
  have hzne : z ≠ z' := by
    intro hcon
    have hbb : st.board.bottomOf z = st.board.bottomOf z' := by rw [hcon]
    rw [h₀, h₀'] at hbb
    exact Card.flipSuit_ne t (Sum.inr.inj (Option.some.inj hbb)).symm
  -- the mirror of the freedom move: same pileStack, at the twin seat
  have htopE : (st.exchangeTwinCargo t).board.topOf (Sum.inr z) = none := by
    rw [State.exchangeTwinCargo_board, Board.exchangeTwin_topOf,
      Base.swapTwin_eq_self (fun h => hzt (Sum.inr.inj h))
        (fun h => hzt' (Sum.inr.inj h))]
    exact htop
  have hbotE : (st.exchangeTwinCargo t).board.bottomOf z = some (Sum.inr t.flipSuit) := by
    rw [State.exchangeTwinCargo_board, Board.bottomOf_exchangeTwin, h₀]
    show some (Base.swapTwin t (Sum.inr t)) = some (Sum.inr t.flipSuit)
    rw [show Base.swapTwin t (Sum.inr t) = Sum.inr t.flipSuit from by
      show Sum.inr (Card.swapTwin t t) = Sum.inr t.flipSuit
      rw [Card.swapTwin_self_left]]
  have hrkE : z.rank.toIdx = (st.exchangeTwinCargo t).heights z.suit := by
    rw [State.exchangeTwinCargo_heights]
    exact hrk
  have hstepE : (st.exchangeTwinCargo t).apply (Move.pileStack z) = some
      { st.exchangeTwinCargo t with
        board := (st.exchangeTwinCargo t).board.detach (Sum.inr t.flipSuit),
        heights := fun s => if s = z.suit then st.heights s + 1 else st.heights s } := by
    rw [apply_pileStack_iff]
    exact ⟨htopE, Sum.inr t.flipSuit, hbotE, hrkE, rfl⟩
  have hB₁ : { st.exchangeTwinCargo t with
        board := (st.exchangeTwinCargo t).board.detach (Sum.inr t.flipSuit),
        heights := fun s => if s = z.suit then st.heights s + 1 else st.heights s }
      = A₁.exchangeTwinCargo t := by
    rw [hA₁]
    apply state_ext
    · rfl
    · show (st.board.exchangeTwin t).detach (Sum.inr t.flipSuit) = _
      rw [Board.exchangeTwin_detach]
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
  -- the premises of the backward transfer at (A₁, z', t')
  have hvis₁ : A₁.isVis t.flipSuit = true := by
    have hb : A₁.board.bottomOf t.flipSuit = st.board.bottomOf t.flipSuit := by
      rw [hA₁]
      exact bottomOf_detach_ne hztop (fun h => hzt' h.symm)
    rw [State.isVis, hb]
    exact hvis'
  have hbot₁ : A₁.board.bottomOf z' = some (Sum.inr t.flipSuit) := by
    have hb : A₁.board.bottomOf z' = st.board.bottomOf z' := by
      rw [hA₁]
      exact bottomOf_detach_ne hztop (fun h => hzne h.symm)
    rw [hb]
    exact h₀'
  have hbare₁ : A₁.board.topOf (Sum.inr t.flipSuit.flipSuit) = none := by
    rw [show t.flipSuit.flipSuit = t from Card.flipSuit_flipSuit t, hA₁]
    exact Board.detach_topOf st.board (Sum.inr t)
  have habove₁ : A₁.board.aboveOf z' = st.board.aboveOf z' := by
    have hfr : t.flipSuit.rank.toIdx = t.rank.toIdx :=
      congrArg Rank.toIdx (Card.flipSuit_rank t)
    have hzt'' : z' ≠ t := by
      obtain ⟨hrkz, -⟩ := (canSitOn_eq _ _).mp hfit'
      intro hcon
      rw [hcon] at hrkz
      rw [hfr] at hrkz
      omega
    have hzt''' : z' ≠ t.flipSuit := by
      obtain ⟨hrkz, -⟩ := (canSitOn_eq _ _).mp hfit'
      intro hcon
      rw [hcon] at hrkz
      omega
    apply Board.aboveOf_congr_off
    · intro x hx₁ hx₂
      rw [hA₁]
      show st.board.topOf (Sum.inr x) = (st.board.detach (Sum.inr t)).topOf (Sum.inr x)
      rw [Board.detach_topOf_ne _ _ _ (fun h => hx₁ (Sum.inr.inj h))]
    · intro x hx
      exact ⟨fun h => hnb'.1 (h ▸ hx), fun h => hnb'.2 (h ▸ hx)⟩
    · exact ⟨hzt'', hzt'''⟩
  have hmem : ∀ x, x ∈ A₁.board.aboveOf z' → x ∈ st.board.aboveOf z' := by
    intro x hx
    rw [← habove₁]
    exact hx
  have hback : (A₁.exchangeTwinCargo t).apply
      (Move.pilePile z' (Sum.inr t.flipSuit)) = some A₁ := by
    have h := State.exchangeTwinCargo_pilePile_back (st := A₁) (z := z') (t := t.flipSuit)
      hvis₁ hbot₁ hbare₁ hfit'
      ⟨fun h => hnb'.2 (hmem _ h), fun h => by
        have hx := hmem _ h
        rw [Card.flipSuit_flipSuit t] at hx
        exact hnb'.1 hx⟩
    rw [State.exchangeTwinCargo_flipSuit] at h
    exact h
  -- the assembly: the mirrored freedom, the backward transfer, the tail
  refine ⟨Move.pileStack z :: Move.pilePile z' (Sum.inr t.flipSuit) :: π, w, ?_, hwinw⟩
  simp only [State.run, hstepE, hB₁, hback]
  exact hrun

/-! ### The premise-transfer substrate (the hnb persistence rides these)

The walk laws behind the no-braid premise transfer — the unplaced-card
argument — and behind the step lemma's v2 (the user's session-7
correction: t-passing runs landing off the cargo stacks mirror fine).
Landed 2026-09-14, sessions 6-7: `aboveOf_sub_detach` (the
detach-shrink), the seeded-walk bounds, the attach-growth law, the
exchange walk-bound, and the off-cargo self-landing corollary.  The WF
dependency (session 6): the deckPile/stackPile/reveal premise-transfer
cases need the moved card to carry no stack, which holds at WF states
by board_edges (a stock, foundationed, or non-boundary-hidden base
admits no edge — the deal-adjacent disjunct's own topHidden-or-seated
side condition); the pilePile case needs no WF (the self-landing guard
does the work). -/

/-- **Detaching shrinks every run**: the walk in the detached board
collects a subset of the original walk's cards (the only changed seat
reads `none`; until then the walks — and hence the accumulator
contains-checks — coincide).  The hnb-premise transfer through the
detach half of pilePile/pileStack rides this. -/
theorem Board.aboveOf_sub_detach {bd : Board} {b : Base} :
    ∀ (n : Nat) (c₀ : Card) (acc : List Card) (x : Card),
      x ∈ Board.aboveOf.go (bd.detach b) n (Sum.inr c₀) acc →
      x ∈ Board.aboveOf.go bd n (Sum.inr c₀) acc := by
  intro n
  induction n with
  | zero => intro c₀ acc x hx; exact hx
  | succ n ih =>
      intro c₀ acc x hx
      rw [aboveOf_go_succ (bd.detach b)] at hx
      rw [aboveOf_go_succ bd]
      cases hd : (bd.detach b).topOf (Sum.inr c₀) with
      | none =>
          rw [hd] at hx
          exact Board.aboveOf_go_mono (n + 1) (Sum.inr c₀) acc hx
      | some c' =>
          rw [hd] at hx
          dsimp only at hx
          have hne : Sum.inr c₀ ≠ b := by
            intro h
            rw [h, Board.detach_topOf] at hd
            simp at hd
          have hbd : bd.topOf (Sum.inr c₀) = some c' := by
            rw [← Board.detach_topOf_ne _ _ _ hne]
            exact hd
          rw [hbd]
          show x ∈ (if acc.contains c' = true then acc
              else Board.aboveOf.go bd n (Sum.inr c') (c' :: acc))
          by_cases hcon : acc.contains c' = true
          · rw [if_pos hcon] at hx ⊢
            exact hx
          · rw [if_neg hcon] at hx ⊢
            exact ih c' (c' :: acc) x hx

/-- The seeded-walk bound, two-accumulator form: a run walked with a
larger accumulator `B` (fuel `m`) outputs only members of `B` and what
the walk with the smaller accumulator `S ⊆ B` (fuel `j + m`) outputs —
the two walks read the same seats while both run, and the bigger
accumulator's contains-guard only fires earlier. -/
theorem Board.aboveOf_go_seeded_subset {bd : Board} (j : Nat) :
    ∀ (m : Nat) (x : Card) (B S : List Card) (y : Card),
    S ⊆ B → y ∈ Board.aboveOf.go bd m (Sum.inr x) B →
    y ∈ B ∨ y ∈ Board.aboveOf.go bd (j + m) (Sum.inr x) S := by
  intro m
  induction m with
  | zero => intro x B S y _ hy; exact Or.inl hy
  | succ n ih =>
      intro x B S y hsub hy
      cases ht : bd.topOf (Sum.inr x) with
      | none =>
          rw [Board.aboveOf_go_topOf_none ht] at hy
          exact Or.inl hy
      | some d =>
          by_cases hBd : B.contains d = true
          · rw [Board.aboveOf_go_stop ht hBd] at hy
            exact Or.inl hy
          · rw [Board.aboveOf_go_step ht hBd] at hy
            have hSd : S.contains d ≠ true := by
              intro hc
              exact hBd ((List.contains_iff_mem).mpr (hsub ((List.contains_iff_mem).mp hc)))
            have hsub' : (d :: S) ⊆ (d :: B) := by
              intro z hz
              rcases List.mem_cons.mp hz with heq | hz'
              · rw [heq]; exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ (hsub hz')
            have hgoal : Board.aboveOf.go bd (j + (n + 1)) (Sum.inr x) S
                = Board.aboveOf.go bd (j + n) (Sum.inr d) (d :: S) := by
              have hfuel : j + (n + 1) = (j + n) + 1 := by omega
              rw [hfuel]
              exact Board.aboveOf_go_step ht hSd
            rw [hgoal]
            rcases ih d (d :: B) (d :: S) y hsub' hy with h | h
            · rcases List.mem_cons.mp h with heq | h'
              · rw [heq]
                exact Or.inr
                  (Board.aboveOf_go_mem bd (j + n) (Sum.inr d) (d :: S) d List.mem_cons_self)
              · exact Or.inl h'
            · exact Or.inr h

/-- The seeded-walk bound, 52 form: a walk seeded with `B` (any fuel
`m ≤ 52`) outputs only `B`'s members and the plain run above `x`. -/
theorem Board.aboveOf_go_seeded_bound {bd : Board} :
    ∀ (m : Nat) (x : Card) (B : List Card) (y : Card), m ≤ 52 →
    y ∈ Board.aboveOf.go bd m (Sum.inr x) B →
    y ∈ B ∨ y ∈ bd.aboveOf x := by
  intro m x B y hm hy
  rcases Board.aboveOf_go_seeded_subset (52 - m) m x B [] y (List.nil_subset _) hy with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    have hf : (52 - m) + m = 52 := by omega
    rw [hf, ← Board.aboveOf_eq] at h
    exact h

/-- **The attach-growth law**: attaching `c` at `b` grows any run by at
most `c`'s own contribution — everything in the new run above `c₀` was
already above `c₀`, or is `c`, or was above `c`.  The hnb premise
transfer through the attach half of pilePile/pilePile rides this. -/
theorem Board.mem_aboveOf_attach {bd : Board} {b : Base} {c c₀ x : Card}
    {bd' : Board} (hatt : bd.attach b c = some bd') (hx : x ∈ bd'.aboveOf c₀) :
    x ∈ bd.aboveOf c₀ ∨ x = c ∨ x ∈ bd.aboveOf c := by
  have hnn : bd.attach b c ≠ none := by rw [hatt]; simp
  obtain ⟨hfree, -⟩ := (Board.attach_eq_some_iff bd b c).mp hnn
  have hb : bd'.topOf b = some c := Board.attach_topOf bd b c hatt
  have hne : ∀ (b₁ : Base), b₁ ≠ b → bd'.topOf b₁ = bd.topOf b₁ :=
    fun b₁ h₁ => Board.attach_topOf_ne bd b c hatt h₁
  -- The two boards run the identical walk once `c` is in the
  -- accumulator: the only differing seat reads `some c` (guard fires)
  -- on one side and `none` (walk ends) on the other.
  have lem_eq : ∀ (n : Nat) (b₀ : Base) (acc : List Card), c ∈ acc →
      Board.aboveOf.go bd' n b₀ acc = Board.aboveOf.go bd n b₀ acc := by
    intro n
    induction n with
    | zero => intro b₀ acc _; rfl
    | succ n ih =>
        intro b₀ acc hc
        by_cases hbb : b₀ = b
        · rw [hbb]
          rw [Board.aboveOf_go_stop hb ((List.contains_iff_mem).mpr hc),
              Board.aboveOf_go_topOf_none hfree]
        · have hread : bd'.topOf b₀ = bd.topOf b₀ := hne b₀ hbb
          cases ht : bd.topOf b₀ with
          | none =>
              rw [Board.aboveOf_go_topOf_none (hread.trans ht),
                  Board.aboveOf_go_topOf_none ht]
          | some d =>
              by_cases hcon : acc.contains d = true
              · rw [Board.aboveOf_go_stop (hread.trans ht) hcon,
                    Board.aboveOf_go_stop ht hcon]
              · rw [Board.aboveOf_go_step (hread.trans ht) hcon,
                    Board.aboveOf_go_step ht hcon]
                exact ih (Sum.inr d) (d :: acc) (List.mem_cons_of_mem _ hc)
  -- The main induction: the walks agree until the first read of `b`;
  -- there the attach-side walk may continue into `c`'s own stack.
  have main : ∀ (n : Nat) (b₀ : Base) (acc : List Card) (y : Card), n ≤ 52 →
      y ∈ Board.aboveOf.go bd' n b₀ acc →
      y ∈ Board.aboveOf.go bd n b₀ acc ∨ y = c ∨ y ∈ bd.aboveOf c := by
    intro n
    induction n with
    | zero => intro b₀ acc y _ hy; exact Or.inl hy
    | succ n ih =>
        intro b₀ acc y hn hy
        by_cases hbb : b₀ = b
        · rw [hbb] at hy
          by_cases hcon : acc.contains c = true
          · rw [Board.aboveOf_go_stop hb hcon] at hy
            exact Or.inl (Board.aboveOf_go_mem bd (n + 1) b₀ acc y hy)
          · rw [Board.aboveOf_go_step hb hcon] at hy
            rw [lem_eq n (Sum.inr c) (c :: acc) List.mem_cons_self] at hy
            rcases Board.aboveOf_go_seeded_bound n c (c :: acc) y (by omega) hy with h | h
            · rcases List.mem_cons.mp h with heq | h'
              · exact Or.inr (Or.inl heq)
              · exact Or.inl (Board.aboveOf_go_mem bd (n + 1) b₀ acc y h')
            · exact Or.inr (Or.inr h)
        · have hread : bd'.topOf b₀ = bd.topOf b₀ := hne b₀ hbb
          cases ht : bd.topOf b₀ with
          | none =>
              rw [Board.aboveOf_go_topOf_none (hread.trans ht)] at hy
              exact Or.inl (Board.aboveOf_go_mem bd (n + 1) b₀ acc y hy)
          | some d =>
              by_cases hcon : acc.contains d = true
              · rw [Board.aboveOf_go_stop (hread.trans ht) hcon] at hy
                exact Or.inl (Board.aboveOf_go_mem bd (n + 1) b₀ acc y hy)
              · rw [Board.aboveOf_go_step (hread.trans ht) hcon] at hy
                rcases ih (Sum.inr d) (d :: acc) y (by omega) hy with h | h | h
                · exact Or.inl (by rw [Board.aboveOf_go_step ht hcon]; exact h)
                · exact Or.inr (Or.inl h)
                · exact Or.inr (Or.inr h)
  rw [Board.aboveOf_eq] at hx
  rcases main 52 (Sum.inr c₀) [] x (Nat.le_refl 52) hx with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- **The exchange walk-bound** (the user's session-7 correction made
formal): the walk in the exchanged board from any card grows by at most
the two cargos' own stacks — everything else was already collected by
the original walk. -/
theorem Board.aboveOf_exchangeTwin_bound {bd : Board} {t z z' c x : Card}
    (h₀ : bd.topOf (Sum.inr t) = some z)
    (h₀' : bd.topOf (Sum.inr t.flipSuit) = some z')
    (hne : z ≠ t ∧ z ≠ t.flipSuit ∧ z' ≠ t ∧ z' ≠ t.flipSuit)
    (hnbz : t ∉ bd.aboveOf z ∧ t.flipSuit ∉ bd.aboveOf z)
    (hnbz' : t ∉ bd.aboveOf z' ∧ t.flipSuit ∉ bd.aboveOf z')
    (hx : x ∈ (bd.exchangeTwin t).aboveOf c) :
    x ∈ bd.aboveOf c ∨ x = z ∨ x = z' ∨ x ∈ bd.aboveOf z ∨ x ∈ bd.aboveOf z' := by
  have hsw : Base.swapTwin t (Sum.inr t.flipSuit) = Sum.inr t := by
    show Sum.inr (Card.swapTwin t t.flipSuit) = Sum.inr t
    rw [Card.swapTwin_self_right]
  have hsw' : Base.swapTwin t (Sum.inr t) = Sum.inr t.flipSuit := by
    show Sum.inr (Card.swapTwin t t) = Sum.inr t.flipSuit
    rw [Card.swapTwin_self_left]
  have hxt : (bd.exchangeTwin t).topOf (Sum.inr t) = some z' := by
    rw [Board.exchangeTwin_topOf, hsw']; exact h₀'
  have hxt' : (bd.exchangeTwin t).topOf (Sum.inr t.flipSuit) = some z := by
    rw [Board.exchangeTwin_topOf, hsw]; exact h₀
  have hagree : ∀ (b₁ : Base), b₁ ≠ Sum.inr t → b₁ ≠ Sum.inr t.flipSuit →
      (bd.exchangeTwin t).topOf b₁ = bd.topOf b₁ := by
    intro b₁ hb hb'
    rw [Board.exchangeTwin_topOf, Base.swapTwin_eq_self hb hb']
  have hagreeC : ∀ (w : Card), w ≠ t → w ≠ t.flipSuit →
      bd.topOf (Sum.inr w) = (bd.exchangeTwin t).topOf (Sum.inr w) := by
    intro w hw₁ hw₂
    rw [Board.exchangeTwin_topOf,
      Base.swapTwin_eq_self (fun h => hw₁ (Sum.inr.inj h))
        (fun h => hw₂ (Sum.inr.inj h))]
  have hz : (bd.exchangeTwin t).aboveOf z = bd.aboveOf z :=
    Board.aboveOf_congr_off hagreeC
      (fun w hw => ⟨fun heq => hnbz.1 (heq ▸ hw), fun heq => hnbz.2 (heq ▸ hw)⟩)
      ⟨hne.1, hne.2.1⟩
  have hz' : (bd.exchangeTwin t).aboveOf z' = bd.aboveOf z' :=
    Board.aboveOf_congr_off hagreeC
      (fun w hw => ⟨fun heq => hnbz'.1 (heq ▸ hw), fun heq => hnbz'.2 (heq ▸ hw)⟩)
      ⟨hne.2.2.1, hne.2.2.2⟩
  have main : ∀ (n : Nat) (b₀ : Base) (acc : List Card) (y : Card), n ≤ 52 →
      y ∈ Board.aboveOf.go (bd.exchangeTwin t) n b₀ acc →
      y ∈ Board.aboveOf.go bd n b₀ acc ∨ y = z ∨ y = z' ∨
        y ∈ bd.aboveOf z ∨ y ∈ bd.aboveOf z' := by
    intro n
    induction n with
    | zero => intro b₀ acc y _ hy; exact Or.inl hy
    | succ n ih =>
        intro b₀ acc y hn hy
        by_cases hbt : b₀ = Sum.inr t
        · rw [hbt] at hy
          by_cases hcon : acc.contains z' = true
          · rw [Board.aboveOf_go_stop hxt hcon] at hy
            exact Or.inl (Board.aboveOf_go_mem bd (n + 1) b₀ acc y hy)
          · rw [Board.aboveOf_go_step hxt hcon] at hy
            rcases Board.aboveOf_go_seeded_bound n z' (z' :: acc) y (by omega) hy with h | h
            · rcases List.mem_cons.mp h with heq | h'
              · exact Or.inr (Or.inr (Or.inl heq))
              · exact Or.inl (Board.aboveOf_go_mem bd (n + 1) b₀ acc y h')
            · rw [hz'] at h
              exact Or.inr (Or.inr (Or.inr (Or.inr h)))
        · by_cases hbt' : b₀ = Sum.inr t.flipSuit
          · rw [hbt'] at hy
            by_cases hcon : acc.contains z = true
            · rw [Board.aboveOf_go_stop hxt' hcon] at hy
              exact Or.inl (Board.aboveOf_go_mem bd (n + 1) b₀ acc y hy)
            · rw [Board.aboveOf_go_step hxt' hcon] at hy
              rcases Board.aboveOf_go_seeded_bound n z (z :: acc) y (by omega) hy with h | h
              · rcases List.mem_cons.mp h with heq | h'
                · exact Or.inr (Or.inl heq)
                · exact Or.inl (Board.aboveOf_go_mem bd (n + 1) b₀ acc y h')
              · rw [hz] at h
                exact Or.inr (Or.inr (Or.inr (Or.inl h)))
          · have hread : (bd.exchangeTwin t).topOf b₀ = bd.topOf b₀ := hagree b₀ hbt hbt'
            cases ht : bd.topOf b₀ with
            | none =>
                rw [Board.aboveOf_go_topOf_none (hread.trans ht)] at hy
                exact Or.inl (Board.aboveOf_go_mem bd (n + 1) b₀ acc y hy)
            | some d =>
                by_cases hcon : acc.contains d = true
                · rw [Board.aboveOf_go_stop (hread.trans ht) hcon] at hy
                  exact Or.inl (Board.aboveOf_go_mem bd (n + 1) b₀ acc y hy)
                · rw [Board.aboveOf_go_step (hread.trans ht) hcon] at hy
                  rcases ih (Sum.inr d) (d :: acc) y (by omega) hy with h | h | h | h | h
                  · exact Or.inl (by rw [Board.aboveOf_go_step ht hcon]; exact h)
                  · exact Or.inr (Or.inl h)
                  · exact Or.inr (Or.inr (Or.inl h))
                  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
                  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  rw [Board.aboveOf_eq] at hx
  rcases main 52 (Sum.inr c) [] x (Nat.le_refl 52) hx with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- **The off-cargo self-landing transfer** (the step lemma v2's guard):
a card off the original run and off both cargos' stacks stays off the
exchanged run — the user's session-7 correction, formal. -/
theorem Board.selfLanding_exchangeTwin_of_off_cargo {bd : Board} {t z z' c d : Card}
    (h₀ : bd.topOf (Sum.inr t) = some z)
    (h₀' : bd.topOf (Sum.inr t.flipSuit) = some z')
    (hne : z ≠ t ∧ z ≠ t.flipSuit ∧ z' ≠ t ∧ z' ≠ t.flipSuit)
    (hnbz : t ∉ bd.aboveOf z ∧ t.flipSuit ∉ bd.aboveOf z)
    (hnbz' : t ∉ bd.aboveOf z' ∧ t.flipSuit ∉ bd.aboveOf z')
    (hd : d ≠ z ∧ d ≠ z' ∧ d ∉ bd.aboveOf z ∧ d ∉ bd.aboveOf z')
    (hguard : d ∉ bd.aboveOf c) :
    d ∉ (bd.exchangeTwin t).aboveOf c := by
  intro hmem
  rcases Board.aboveOf_exchangeTwin_bound h₀ h₀' hne hnbz hnbz' hmem with h | h | h | h | h
  · exact hguard h
  · exact hd.1 h
  · exact hd.2.1 h
  · exact hd.2.2.1 h
  · exact hd.2.2.2 h

/-! ### The clean-move mirror steps (the prefix induction's mechanics)

The non-board-writing moves mirror verbatim: the guards read only the
stock/heights (inherited across the exchange), and the successor
relation `b₁ = a₁.exchangeTwinCargo t` is a field-for-field identity.
The board-writing kinds (reveal/deckPile/stackPile/pilePile) ride the
`exchangeTwin_attach_ne`/`exchangeTwin_detach_ne` congruences — their
step lemmas are the remaining mechanical work; the pilePile kind
additionally needs the walk congruence (`aboveOf_congr_off`) for the
self-landing guard, i.e. the twin-avoidance of the moved run's root
(the merge case is the row's open gap). -/

/-- `draw` mirrors: the stock is inherited across the exchange. -/
theorem State.exchangeTwinCargo_step_draw {st a₁ : State} {t : Card}
    (hstep : st.apply Move.draw = some a₁) :
    (st.exchangeTwinCargo t).apply Move.draw = some (a₁.exchangeTwinCargo t) := by
  rw [apply_draw_iff] at hstep ⊢
  rw [hstep, State.exchangeTwinCargo_stock, State.exchangeTwinCargo_drawStep]
  rfl

/-- `deckStack` mirrors: the waste top, the rung, and the update are all
frame-inherited across the exchange. -/
theorem State.exchangeTwinCargo_step_deckStack {st a₁ : State} {t c : Card}
    (hstep : st.apply (Move.deckStack c) = some a₁) :
    (st.exchangeTwinCargo t).apply (Move.deckStack c) = some (a₁.exchangeTwinCargo t) := by
  rw [apply_deckStack_iff] at hstep ⊢
  obtain ⟨hprev, hrk, hst⟩ := hstep
  refine ⟨?_, ?_, ?_⟩
  · rw [State.exchangeTwinCargo_stock]
    exact hprev
  · rw [State.exchangeTwinCargo_heights]
    exact hrk
  · rw [hst, State.exchangeTwinCargo_stock, State.exchangeTwinCargo_heights]
    rfl

/-- Visibility is exchange-invariant: the seat swap preserves the
isSome-ness of every card's base search. -/
theorem State.isVis_exchangeTwin (st : State) (t : Card) (c : Card) :
    (st.exchangeTwinCargo t).isVis c = st.isVis c := by
  show ((st.exchangeTwinCargo t).board.bottomOf c).isSome = (st.board.bottomOf c).isSome
  rw [State.exchangeTwinCargo_board, Board.bottomOf_exchangeTwin]
  cases hb : st.board.bottomOf c with
  | none => rfl
  | some β => rfl

/-- The `canPlace` transfer across the exchange, for landing targets off
the twin pair (the seat's value and the base card's visibility are
inherited). -/
theorem State.canPlace_exchangeTwin {st : State} {t c : Card} {b : Base}
    (hbt : b ≠ Sum.inr t) (hbt' : b ≠ Sum.inr t.flipSuit) :
    (st.exchangeTwinCargo t).canPlace c b = st.canPlace c b := by
  have h1 : (st.exchangeTwinCargo t).board.topOf b = st.board.topOf b := by
    rw [State.exchangeTwinCargo_board, Board.exchangeTwin_topOf,
      Base.swapTwin_eq_self hbt hbt']
  cases b with
  | inl a => rfl
  | inr d =>
      simp only [State.canPlace]
      rw [h1, State.isVis_exchangeTwin]

/-- `deckPile` mirrors for landing targets off the twin pair (targets on
the twin seats are excluded from the source play by the
occupied-twin argument). -/
theorem State.exchangeTwinCargo_step_deckPile {st a₁ : State} {t z z' c : Card} {b : Base}
    (h₀ : st.board.bottomOf z = some (Sum.inr t))
    (h₀' : st.board.bottomOf z' = some (Sum.inr t.flipSuit))
    (hstep : st.apply (Move.deckPile c b) = some a₁) :
    (st.exchangeTwinCargo t).apply (Move.deckPile c b) = some (a₁.exchangeTwinCargo t) := by
  have hztop : st.board.topOf (Sum.inr t) = some z := (Board.bottomOf_eq _ _ _).mp h₀
  have hztop' : st.board.topOf (Sum.inr t.flipSuit) = some z' := (Board.bottomOf_eq _ _ _).mp h₀'
  rw [apply_deckPile_iff] at hstep ⊢
  obtain ⟨hprev, hcp, bd, hatt, hst⟩ := hstep
  have hbt : b ≠ Sum.inr t := by
    intro h
    rw [h, State.canPlace, hztop] at hcp
    simp at hcp
  have hbt' : b ≠ Sum.inr t.flipSuit := by
    intro h
    rw [h, State.canPlace, hztop'] at hcp
    simp at hcp
  refine ⟨?_, ?_, bd.exchangeTwin t, ?_, ?_⟩
  · rw [State.exchangeTwinCargo_stock]
    exact hprev
  · rw [State.canPlace_exchangeTwin hbt hbt']
    exact hcp
  · rw [State.exchangeTwinCargo_board]
    exact Board.exchangeTwin_attach_ne _ _ hbt hbt' hatt
  · rw [hst, State.exchangeTwinCargo_stock]
    rfl

/-- `stackPile` mirrors for landing targets off the twin pair (the
worry-back's un-stack rung is height-inherited). -/
theorem State.exchangeTwinCargo_step_stackPile {st a₁ : State} {t z z' c : Card} {b : Base}
    (h₀ : st.board.bottomOf z = some (Sum.inr t))
    (h₀' : st.board.bottomOf z' = some (Sum.inr t.flipSuit))
    (hstep : st.apply (Move.stackPile c b) = some a₁) :
    (st.exchangeTwinCargo t).apply (Move.stackPile c b) = some (a₁.exchangeTwinCargo t) := by
  have hztop : st.board.topOf (Sum.inr t) = some z := (Board.bottomOf_eq _ _ _).mp h₀
  have hztop' : st.board.topOf (Sum.inr t.flipSuit) = some z' := (Board.bottomOf_eq _ _ _).mp h₀'
  rw [apply_stackPile_iff] at hstep ⊢
  obtain ⟨hrk, hcp, bd, hatt, hst⟩ := hstep
  have hbt : b ≠ Sum.inr t := by
    intro h
    rw [h, State.canPlace, hztop] at hcp
    simp at hcp
  have hbt' : b ≠ Sum.inr t.flipSuit := by
    intro h
    rw [h, State.canPlace, hztop'] at hcp
    simp at hcp
  refine ⟨?_, ?_, bd.exchangeTwin t, ?_, ?_⟩
  · rw [State.exchangeTwinCargo_heights]
    exact hrk
  · rw [State.canPlace_exchangeTwin hbt hbt']
    exact hcp
  · rw [State.exchangeTwinCargo_board]
    exact Board.exchangeTwin_attach_ne _ _ hbt hbt' hatt
  · rw [hst, State.exchangeTwinCargo_heights]
    rfl

/-- `reveal` mirrors: the trigger's own seat, the revealed card, the
pile/hiddenBase reads (deal+depths-inherited), and the attach base are
all off the twin pair at any FIRING reveal — triggers on the twin seats
are excluded (the seats are occupied), and reveals whose revealed card
is a twin cannot fire (the attach needs the revealed card unplaced, but
the twins stay placed). -/
theorem State.exchangeTwinCargo_step_reveal {st a₁ : State} {t z z' c : Card}
    (hvis : st.isVis t = true) (hvis' : st.isVis t.flipSuit = true)
    (h₀ : st.board.bottomOf z = some (Sum.inr t))
    (h₀' : st.board.bottomOf z' = some (Sum.inr t.flipSuit))
    (hstep : st.apply (Move.reveal c) = some a₁) :
    (st.exchangeTwinCargo t).apply (Move.reveal c) = some (a₁.exchangeTwinCargo t) := by
  have hztop : st.board.topOf (Sum.inr t) = some z := (Board.bottomOf_eq _ _ _).mp h₀
  have hztop' : st.board.topOf (Sum.inr t.flipSuit) = some z' := (Board.bottomOf_eq _ _ _).mp h₀'
  rw [apply_reveal_iff] at hstep ⊢
  obtain ⟨htop, r, a, bd, hbot, hpile, hatt, hst⟩ := hstep
  have hct : c ≠ t := by
    intro h
    rw [h, hztop] at htop
    simp at htop
  have hct' : c ≠ t.flipSuit := by
    intro h
    rw [h, hztop'] at htop
    simp at htop
  -- the revealed card r is off the twin pair (else the attach would
  -- seat a placed twin)
  have hrt : r ≠ t ∧ r ≠ t.flipSuit := by
    obtain ⟨-, hgunplaced⟩ := (Board.attach_eq_some_iff _ _ _).mp (by
      intro h
      rw [hatt] at h
      simp at h)
    refine ⟨?_, ?_⟩
    · intro h
      rw [h] at hgunplaced
      rw [State.isVis, hgunplaced] at hvis
      simp at hvis
    · intro h
      rw [h] at hgunplaced
      rw [State.isVis, hgunplaced] at hvis'
      simp at hvis'
  -- the attach base is off the twin pair (the twin seats are occupied)
  obtain ⟨hgb, -⟩ := (Board.attach_eq_some_iff _ _ _).mp (by
    intro h
    rw [hatt] at h
    simp at h)
  have hgbt : st.hiddenBase a ≠ Sum.inr t := by
    intro h
    rw [h, hztop] at hgb
    simp at hgb
  have hgbt' : st.hiddenBase a ≠ Sum.inr t.flipSuit := by
    intro h
    rw [h, hztop'] at hgb
    simp at hgb
  -- the B-side guards
  refine ⟨?_, r, a, bd.exchangeTwin t, ?_, ?_, ?_, ?_⟩
  · rw [State.exchangeTwinCargo_board, Board.exchangeTwin_topOf,
      Base.swapTwin_eq_self (fun h => hct (Sum.inr.inj h))
        (fun h => hct' (Sum.inr.inj h))]
    exact htop
  · rw [State.exchangeTwinCargo_board, Board.bottomOf_exchangeTwin, hbot]
    show some (Base.swapTwin t (Sum.inr r)) = _
    rw [Base.swapTwin_eq_self (fun h => hrt.1 (Sum.inr.inj h))
      (fun h => hrt.2 (Sum.inr.inj h))]
  · rw [Frame.pileOfTopHidden_congr (State.exchangeTwinCargo_deal st t)
      (State.exchangeTwinCargo_depths st t) r]
    exact hpile
  · rw [show (st.exchangeTwinCargo t).hiddenBase a = st.hiddenBase a from
      Frame.hiddenBase_congr (State.exchangeTwinCargo_deal st t)
        (State.exchangeTwinCargo_depths st t) a,
      State.exchangeTwinCargo_board]
    exact Board.exchangeTwin_attach_ne _ _ hgbt hgbt' hatt
  · rw [hst, State.exchangeTwinCargo_depths]
    rfl

/-- **The clean-run `pilePile` mirror step**: when the moved run's root
is off the twin pair and its walk avoids the twins (the run contains
neither `t` nor `t'`), the SAME move is legal in the exchanged state and
the successors stay exchanged — `aboveOf_congr_off` carries the
self-landing guard, the detach/attach congruences carry the board.
This is the mirror step for the only move kind with a divergence: the
MERGE (the root's walk reaching a twin, landing on the other cargo's
stack) is the [H] row's open gap. -/
theorem State.exchangeTwinCargo_step_pilePile {st a₁ : State} {z z' t c : Card} {b : Base}
    (h₀ : st.board.bottomOf z = some (Sum.inr t))
    (h₀' : st.board.bottomOf z' = some (Sum.inr t.flipSuit))
    (hc : c ≠ z ∧ c ≠ z')
    (hct : c ≠ t ∧ c ≠ t.flipSuit)
    (hclean : t ∉ st.board.aboveOf c ∧ t.flipSuit ∉ st.board.aboveOf c)
    (hstep : st.apply (Move.pilePile c b) = some a₁) :
    (st.exchangeTwinCargo t).apply (Move.pilePile c b) = some (a₁.exchangeTwinCargo t) := by
  have hztop : st.board.topOf (Sum.inr t) = some z := (Board.bottomOf_eq _ _ _).mp h₀
  have hztop' : st.board.topOf (Sum.inr t.flipSuit) = some z' := (Board.bottomOf_eq _ _ _).mp h₀'
  rw [apply_pilePile_iff] at hstep
  obtain ⟨β, hβ, hβb, hcmr, bd, hatt, ha₁⟩ := hstep
  simp only [State.canMoveRun] at hcmr
  obtain ⟨hbcp, hself⟩ := Bool.and_eq_true_iff.mp hcmr
  -- the moved root's base is off the twin pair (else it would be a cargo)
  have hβt : β ≠ Sum.inr t := by
    intro h
    rw [h] at hβ
    exact hc.1
      (Option.some.inj (hztop.symm.trans ((Board.bottomOf_eq st.board c (Sum.inr t)).mp hβ))).symm
  have hβt' : β ≠ Sum.inr t.flipSuit := by
    intro h
    rw [h] at hβ
    exact hc.2
      (Option.some.inj (hztop'.symm.trans
        ((Board.bottomOf_eq st.board c (Sum.inr t.flipSuit)).mp hβ))).symm
  -- the landing target is off the twin pair (occupied in the source)
  have hbt : b ≠ Sum.inr t := by
    intro h
    rw [h, State.canPlace, hztop] at hbcp
    simp at hbcp
  have hbt' : b ≠ Sum.inr t.flipSuit := by
    intro h
    rw [h, State.canPlace, hztop'] at hbcp
    simp at hbcp
  -- the walk congruence: the self-landing guard transfers verbatim
  have habove : (st.exchangeTwinCargo t).board.aboveOf c = st.board.aboveOf c := by
    apply Board.aboveOf_congr_off
    · intro x hx₁ hx₂
      rw [State.exchangeTwinCargo_board, Board.exchangeTwin_topOf,
        Base.swapTwin_eq_self (fun h => hx₁ (Sum.inr.inj h))
          (fun h => hx₂ (Sum.inr.inj h))]
    · intro x hx
      exact ⟨fun h => hclean.1 (h ▸ hx), fun h => hclean.2 (h ▸ hx)⟩
    · exact hct
  -- the B-side guards
  have hβE : (st.exchangeTwinCargo t).board.bottomOf c = some β := by
    rw [State.exchangeTwinCargo_board, Board.bottomOf_exchangeTwin, hβ]
    show some (β.swapTwin t) = some β
    exact congrArg some (Base.swapTwin_eq_self hβt hβt')
  have hbcpE : (st.exchangeTwinCargo t).canPlace c b = true := by
    have h1 : (st.exchangeTwinCargo t).board.topOf b = st.board.topOf b := by
      rw [State.exchangeTwinCargo_board, Board.exchangeTwin_topOf,
        Base.swapTwin_eq_self hbt hbt']
    cases b with
    | inl a =>
        rw [State.canPlace]
        exact hbcp
    | inr d =>
        simp only [State.canPlace] at hbcp ⊢
        rw [h1, State.isVis_exchangeTwin]
        exact hbcp
  have hcmrE : (st.exchangeTwinCargo t).canMoveRun c b = true := by
    simp only [State.canMoveRun]
    rw [hbcpE]
    cases b with
    | inl a => rfl
    | inr d =>
        rw [habove]
        exact hself
  -- the B-side board composite
  have hattE : ((st.exchangeTwinCargo t).board.detach β).attach b c
      = some (bd.exchangeTwin t) := by
    rw [State.exchangeTwinCargo_board, Board.exchangeTwin_detach_ne _ _ hβt hβt']
    exact Board.exchangeTwin_attach_ne _ _ hbt hbt' hatt
  -- the assembly
  rw [apply_pilePile_iff]
  refine ⟨β, hβE, hβb, hcmrE, bd.exchangeTwin t, hattE, ?_⟩
  rw [ha₁]
  rfl

/-! ## The rows -/

/-- **The both-cargo exchange**: with both twins carrying a legal-seated
cargo (`hfit`/`hfit'` — the corner's repair premises: without them the
bridge's transfer dies at `canSitOn`, the deal being free to stack
non-fitting pairs), the exchanged state is solvability-equivalent — the
exchange need not be executable.  The no-braid premises (`hnb`, `hnb'`)
keep the exchanged board acyclic: a twin inside a cargo's run would seat
a stack on its own member after the swap.

TODO(proof) **[H]**: the scheduling argument — **the mechanics are
COMPLETE** (2026-09-14, sessions 3-5).  Base case: the freedom-first
bridge (`solvable_of_exchange_pileStack`; the first freedom move is
always a `pileStack` — pre-freedom `pilePile z _` is impossible by the
seat lock).  Step mechanics, all six non-freedom move kinds:
`exchangeTwinCargo_step_{draw,deckStack,deckPile,stackPile,reveal}`
(the single-attach kinds: the `canPlace` transfer
`State.canPlace_exchangeTwin` + the attach congruence; the reveal's
trigger/revealed-card/hiddenBase off-twin derivations) and
`exchangeTwinCargo_step_pilePile` (the clean-run kind: the walk
congruence carries the self-landing guard).  **Premise-transfer
substrate (session 6)**: `Board.aboveOf_sub_detach` (the detach-shrink)
LANDED; the attach-growth lemma and the WF derivations remain.  **THE
WF REPAIR (session 6 finding)**: the hnb transfer through the
attach-moves needs the moved card to carry no stack — at WF this is
board_edges (the deal-adjacent disjunct's own topHidden-or-seated side
condition kills any edge over a stock, foundationed, or non-boundary
base); without WF a phantom unplaced card can formally support a stack
carrying `t` into a cargo run.  The pilePile case needs no WF (the
self-landing guard excludes runs containing `t` from landing on the
cargo's own stack); the reveal case needs only the trigger's bareness.
**Remaining**: the WF stack-free derivations, the h₀/hvis transfers,
the step-lemma v2 wiring (the pilePile step re-based on
`Board.selfLanding_exchangeTwin_of_off_cargo` — the t-passing runs with
targets off the cargo stacks), and the assembly.  **The open gap**: the MERGE —
a `pilePile` whose root's walk passes a twin, landing on the other
cargo's stack — which breaks the mirror (self-landing in the exchanged
state) AND the premise transfer (it creates the braid `t ∈ aboveOf z'`);
the B&G redirect is `canSitOn`-gated (unrelated stack-tops), and the
bare-cargo redirect degenerates to the `z ↔ z'` conjugation, which dies
at suit-reading moves (per-suit rungs — TwinSwapWitness's root cause).
Route: piecewise bookkeeping or play normalization ("winning plays
avoid cargo-top merges"); the gate's witness hunt (the corner AND the
merge shape) runs first.  Premise arithmetic: `hfit`/`hfit'` force
`z' = z.flipSuit` — two twin pairs crossed; `canSitOn_hosts_are_twins`
is the seat lock.

**REPAIRED 2026-09-14 (session 7) — `+hwf`**: the premiseless form is
REFUTED by a witness (Temp/opencode/w15merge.lean, #eval-verified,
exit 0): a crafted non-WF state (empty deal, heights past visible
cards) satisfying every premise where the 3-move win goes through the
MERGE (`pilePile ♥10 (inr ♣J)` — c's t-passing run onto z'), while the
exchanged state is FROZEN (its reachable space is two states, the
second with zero legal moves — exhaustively dead at every depth; the
merge is self-landing there, and every dodge is blocked: the strays
sit at foundation-passed ranks, the anchors are all occupied, the
mirror landing is blocked by a crafted non-fitting tenant).  The repair
`hwf : st.WF` kills the witness via founds_gone/board_edges — exactly
the session-6 phantom-stack finding realized.  Note the repair is
symmetric (the exchange preserves WF: the swapped edges are
legal-seated by twin-blindness) and non-vacuous at every engine state.
The WF-side merge remains the sole open gap. -/
theorem State.solvable_cargoTwin_exchange {st : State} {z z' t : Card}
    (hwf : st.WF)
    (hvis : st.isVis t = true) (hvis' : st.isVis t.flipSuit = true)
    (h₀ : st.board.bottomOf z = some (Sum.inr t))
    (h₀' : st.board.bottomOf z' = some (Sum.inr t.flipSuit))
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.flipSuit = true)
    (hnb : t ∉ st.board.aboveOf z ∧ t.flipSuit ∉ st.board.aboveOf z)
    (hnb' : t ∉ st.board.aboveOf z' ∧ t.flipSuit ∉ st.board.aboveOf z') :
    (st.exchangeTwinCargo t).solvableFrom ↔ st.solvableFrom := sorry

/-- **The bare-twin companion (PROVEN)**: the one-bare-twin exchange
preserves solvability forward, with NO executability or zone premise.
Wave 14's transfer needs the twin visible; the backward realization
above needs nothing but the bare seat — so the phantom-twin shapes (the
twin stocked, buried, or foundationed) come for free: the exchanged
state is one move away from the original (`exchangeTwinCargo_pilePile_back`),
and the original's winning play replays through it.  The statement is
strictly stronger than scaffolded (the planned `hzone` case split and its
`hwf` were dropped — the proof never consults the twin card).

The reverse (`stx.solvable → st.solvable`) holds when the twin is
visible (`pilePile_exchangeTwinCargo_fwd` + `solvable_cargoTwin`'s
pattern); at phantom twins it stays the open corner — the FARM row's
gate note. -/
theorem State.solvable_cargoTwin_exchange_bare {st : State} {z t : Card}
    (hvis : st.isVis t = true)
    (h₀ : st.board.bottomOf z = some (Sum.inr t))
    (hbare : st.board.topOf (Sum.inr t.flipSuit) = none)
    (hfit : canSitOn z t = true)
    (hnb : t ∉ st.board.aboveOf z ∧ t.flipSuit ∉ st.board.aboveOf z)
    (hsol : st.solvableFrom) :
    (st.exchangeTwinCargo t).solvableFrom := by
  obtain ⟨π, w, hrun, hwin⟩ := hsol
  have hback : (st.exchangeTwinCargo t).apply (Move.pilePile z (Sum.inr t)) = some st :=
    State.exchangeTwinCargo_pilePile_back hvis h₀ hbare hfit hnb
  refine ⟨Move.pilePile z (Sum.inr t) :: π, w, ?_, hwin⟩
  simp only [State.run, hback]
  exact hrun
