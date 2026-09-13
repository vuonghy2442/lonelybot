import Klondike.Dominance

/-!
# The local twin swap — the representation-canonicalization theorem

`Card.swapTwin t` exchanges just the pair `t`, `t.flipSuit` in place
(unlike the global relabeling of Klondike/Relabel.lean, which swaps a
whole suit pair *everywhere*): every occurrence of the pair in the
deal, the hidden slices, the board matching and the stock is exchanged;
heights, depths, cursor and draw step stay put.  The claim this file
organizes: **with both twins on the tableau (and WF), the swap
preserves solvability** (`State.solvable_swapTwin`) — the engine's
representation never needs to know which twin of an ambiguous pair
occupies a seat.

## Status of the theory (2026-09-13, corrected same-day)

*Proven, unconditional* (the kit — Basic.lean/Board.lean):
`Card.swapTwin` is an involution, injective, twin-blind to the tableau
rules; `swapTwin_of_ne`: exactly the two cards move; the cargo-transfer
fact `canSitOn_swapTwin_right/_left`; the `swapFull`/`swapColorOf`
family; `Board.mapByWith` (the generic involution conjugation) with
`mapByTwin`/`mapByFull`; and the equal-heights license source
`State.redundantTwins_heights_eq` (for the §5.5 corner).

*Refuted* (witness: `witnesses/TwinSwapWitness.lean`, `by decide`):
the naive apply-level conjugation of the local swap is **false** — the
local pin is not an automorphism.  The correct conjugation is *mixed*
(orchestrated after two failed designs, recorded here so nobody
re-tries them): states map by `State.swapFull t` (contents:
`Card.swapFull t` — the color's suit swap with the pair pinned;
heights: permuted by `Suit.swapColorOf t`), moves map by the plain
suit relabel `Move.relabel (Relabel.ofColorTwin t)`.  Under the
tableau license the twins never occur in the stock, hidden slices, or
foundation prefix (via WF + `isVis`), every guard's equality probe
threads back through `π ∘ R = swapTwin` consistently, and the
foundation guards translate *unconditionally* (the relabeled move
probes the permuted counter of its own suit).

*The sandwich*: `solvable_swapTwin` follows from
`solvable_relabel` (proven) + the bridge `(st.swapTwin t).relabelBy
(Relabel.ofColorTwin t) = st.swapFull t` + `solvable_swapFull`.

One caveat recorded for the run-level row: the conjugation's license
can die mid-play (a twin may get stacked), so the play-level induction
carries the "twins visible-or-symmetrically-gone" invariant — flagged
in `solvable_swapFull`'s route.
-/

/-- The local twin swap on moves: card arguments and card bases are
re-named. -/
def Move.swapTwin (t : Card) : Move → Move
  | .draw => .draw
  | .reveal c => .reveal (Card.swapTwin t c)
  | .deckPile c b => .deckPile (Card.swapTwin t c) (b.swapTwin t)
  | .deckStack c => .deckStack (Card.swapTwin t c)
  | .pileStack c => .pileStack (Card.swapTwin t c)
  | .stackPile c b => .stackPile (Card.swapTwin t c) (b.swapTwin t)
  | .pilePile c b => .pilePile (Card.swapTwin t c) (b.swapTwin t)

/-- The local twin swap on states: every *occurrence* of the pair is
exchanged (deal piles and stock — so the hidden slices follow — the
board matching, and the cycle), while the heights function, depths,
cursor, and draw step stay put.  Not an automorphism (see the header's
finding and `witnesses/TwinSwapWitness.lean`): `heights` stays fixed
because suits are *shared* with non-swapped cards. -/
def State.swapTwin (t : Card) (st : State) : State where
  deal := { piles := fun a => (st.deal.piles a).map (Card.swapTwin t),
            stock := st.deal.stock.map (Card.swapTwin t) }
  board := st.board.mapByTwin t
  heights := st.heights
  depths := st.depths
  stock := { cards := st.stock.cards.map (Card.swapTwin t), cursor := st.stock.cursor }
  drawStep := st.drawStep

/-- A redundant stack has its suit's height at exactly the card's rank
(the pileStack guard). -/
theorem State.heights_eq_of_redundantStack {st : State} {c : Card}
    (h : st.isRedundantStack c = true) : st.heights c.suit = c.rank.toIdx := by
  simp only [State.isRedundantStack, Bool.and_eq_true] at h
  obtain ⟨hleg, -⟩ := h
  simp only [State.legal] at hleg
  obtain ⟨st', hst'⟩ := Option.isSome_iff_exists.mp hleg
  rw [apply_pileStack_iff] at hst'
  obtain ⟨-, -, -, hrk, -⟩ := hst'
  exact hrk.symm

/-- Where the equal-heights license comes from in the §5.5 corner:
both twins redundant implies both heights equal the rank. -/
theorem State.redundantTwins_heights_eq {st : State} {t : Card}
    (h₁ : st.isRedundantStack t = true) (h₂ : st.isRedundantStack t.flipSuit = true) :
    st.heights t.suit = st.heights t.flipSuit.suit := by
  rw [State.heights_eq_of_redundantStack h₁, State.heights_eq_of_redundantStack h₂,
    Card.flipSuit_rank]

/-! ### Visibility along a play: every tableau card is stacked in a win

The machinery behind "the game is solvable, so you can get the card to
the foundation": a tableau card's visibility is anti-monotone along
plays, and the unique move that un-sees a card is its own `pileStack`
(the other moves only ever *add* to the visible image). -/

/-- One step: only `pileStack x` can make `x` leave the tableau (the
other moves only ever *add* to the visible image). -/
theorem State.isVis_antimono {st st' : State} {m : Move} {x : Card}
    (h : st.apply m = some st') (hvis : st.isVis x = true) (hne : m ≠ Move.pileStack x) :
    st'.isVis x = true := by
  obtain ⟨b₀, hb₀⟩ := Option.isSome_iff_exists.mp hvis
  cases m with
  | draw =>
    rw [apply_draw_iff] at h
    rw [h]
    show (st.board.bottomOf x).isSome = true
    exact Option.isSome_iff_exists.mpr ⟨b₀, hb₀⟩
  | reveal c =>
    rw [apply_reveal_iff] at h
    obtain ⟨-, r, a, bd, -, -, hatt, hst'⟩ := h
    rw [hst']
    show (bd.bottomOf x).isSome = true
    have hds : (st.board.bottomOf x).isSome = true := Option.isSome_iff_exists.mpr ⟨b₀, hb₀⟩
    exact bottomOf_isSome_attach hatt hds
  | deckPile c b =>
    rw [apply_deckPile_iff] at h
    obtain ⟨-, -, bd, hatt, hst'⟩ := h
    rw [hst']
    show (bd.bottomOf x).isSome = true
    have hds : (st.board.bottomOf x).isSome = true := Option.isSome_iff_exists.mpr ⟨b₀, hb₀⟩
    exact bottomOf_isSome_attach hatt hds
  | deckStack c =>
    rw [apply_deckStack_iff] at h
    obtain ⟨-, -, hst'⟩ := h
    rw [hst']
    show (st.board.bottomOf x).isSome = true
    exact Option.isSome_iff_exists.mpr ⟨b₀, hb₀⟩
  | pileStack c =>
    rw [apply_pileStack_iff] at h
    obtain ⟨-, b, hbot, -, hst'⟩ := h
    rw [hst']
    show ((st.board.detach b).bottomOf x).isSome = true
    by_cases hxc : x = c
    · subst hxc; exact absurd rfl hne
    · have htop : st.board.topOf b = some c := (Board.bottomOf_eq st.board c b).mp hbot
      rw [bottomOf_detach_ne htop hxc]
      exact Option.isSome_iff_exists.mpr ⟨b₀, hb₀⟩
  | stackPile c b =>
    rw [apply_stackPile_iff] at h
    obtain ⟨-, -, bd, hatt, hst'⟩ := h
    rw [hst']
    show (bd.bottomOf x).isSome = true
    have hds : (st.board.bottomOf x).isSome = true := Option.isSome_iff_exists.mpr ⟨b₀, hb₀⟩
    exact bottomOf_isSome_attach hatt hds
  | pilePile c b =>
    rw [apply_pilePile_iff] at h
    obtain ⟨b₀', hbot, -, -, bd, hatt, hst'⟩ := h
    rw [hst']
    show (bd.bottomOf x).isSome = true
    by_cases hxc : x = c
    · rw [hxc]
      exact Option.isSome_iff_exists.mpr ⟨b,
        (Board.bottomOf_eq bd c b).mpr (Board.attach_topOf _ _ _ hatt)⟩
    · have htop : st.board.topOf b₀' = some c := (Board.bottomOf_eq st.board c b₀').mp hbot
      have hds : ((st.board.detach b₀').bottomOf x).isSome = true := by
        rw [bottomOf_detach_ne htop hxc]
        exact Option.isSome_iff_exists.mpr ⟨b₀, hb₀⟩
      exact bottomOf_isSome_attach hatt hds

/-- The win-induction: in a winning play from a WF state, every
tableau-visible card is `pileStack`ed somewhere along the play — its
only route off the tableau, and a win puts every card on a foundation. -/
theorem State.pileStack_mem_of_win {st w : State} {play : List Move} {c : Card}
    (hwf : st.WF) (hrun : st.run play = some w) (hwin : w.isWin = true)
    (hvis : st.isVis c = true) : Move.pileStack c ∈ play := by
  induction play generalizing st with
  | nil =>
    simp only [State.run] at hrun
    have hsw : st = w := Option.some.inj hrun
    subst hsw
    have h13 : st.heights c.suit = 13 := by
      unfold State.isWin at hwin
      rw [List.all_eq_true] at hwin
      exact of_decide_eq_true (hwin c.suit (Suit.mem_all _))
    have hlt : c.rank.toIdx < st.heights c.suit := by rw [h13]; exact Rank.toIdx_lt _
    rw [(hwf.founds_gone c hlt).1] at hvis
    simp at hvis
  | cons m ms ih =>
    simp only [State.run] at hrun
    cases hma : st.apply m with
    | none => rw [hma] at hrun; simp at hrun
    | some st₁ =>
      rw [hma] at hrun
      by_cases hmeq : m = Move.pileStack c
      · subst hmeq; exact List.mem_cons_self
      · have hvis₁ : st₁.isVis c = true := State.isVis_antimono hma hvis hmeq
        have hwf₁ : st₁.WF := apply_wf hwf m st₁ hma
        exact List.mem_cons.mpr (Or.inr (ih hwf₁ hrun hvis₁))

/-- Right before its `pileStack`, the card is necessarily on the
tableau (the move's own `bottomOf` guard). -/
theorem State.isVis_of_apply_pileStack {st st' : State} {c : Card}
    (h : st.apply (Move.pileStack c) = some st') : st.isVis c = true := by
  rw [apply_pileStack_iff] at h
  obtain ⟨-, b, hbot, -, -⟩ := h
  exact Option.isSome_iff_exists.mpr ⟨b, hbot⟩

/-- Right before its `pileStack`, the card is bare — nothing sits on
it (the move's own `topOf` guard).  "Free", in engine vocabulary. -/
theorem State.topOf_none_of_apply_pileStack {st st' : State} {c : Card}
    (h : st.apply (Move.pileStack c) = some st') : st.board.topOf (Sum.inr c) = none := by
  rw [apply_pileStack_iff] at h
  exact h.1

/-- **The twin stack-exchange pivot** (the strategy-transposition
theorem): when a state admits stacking BOTH twins (their guards read
`heights t.suit = rank = heights t.flipSuit.suit` — so the equal
counters needed for the exchange are *automatic* here), stacking one
or the other gives equi-solvable successors.  This is the pivot of the
play-editing argument for `solvable_swapTwin`: at the moment a winning
line stacks a twin, the twin is bare (`topOf_none_of_apply_pileStack`)
and on the tableau (`isVis_of_apply_pileStack`), and if the other twin
is likewise stackable-bare, the line may stack either.

TODO(proof) [H]: the successors differ by the suit-counter assignment
(`t.suit +1` vs `t.flipSuit.suit +1`) and the seat left behind — relate
them through `State.swapFull` + `solvable_relabel`, or prove the direct
simulation; either route needs the play's continuation transport, so
expect this to share the crux family's machinery.  Probe first per the
refute-first discipline (the guard analysis says it holds; a corpus
check would confirm before the [H] investment). -/
theorem State.solvable_pileStack_twin_iff {st : State} {t : Card} {st₁ st₂ : State}
    (hwf : st.WF)
    (h₁ : st.apply (Move.pileStack t) = some st₁)
    (h₂ : st.apply (Move.pileStack t.flipSuit) = some st₂) :
    st₁.solvableFrom ↔ st₂.solvableFrom := sorry

/-! ### The supermove layer (`superStack`)

The suit-symmetric stack move — the same packaging pattern as
`drawCommit` folding the jump+placement (Macro.lean): `superStack t`
stacks the pair member that's stackable, canonical priority to `t`.
Soundness is by construction (the successor is a physical successor);
sufficiency — you never need the non-canonical member — is the pivot
theorem above, dressed as a move-set equivalence.  The pilePile
transposition arm ("if the stackable twin isn't in position, transpose
first") is the follow-up: it needs a free-base parameter and its own
reachability analysis. -/

/-- The canonical member of a twin pair: the pair-`false` suit (hearts
over diamonds, spades over clubs — `Suit.all`'s order). -/
def Card.canonicalOfPair (t : Card) : Card := if t.suit.pair then t.flipSuit else t

/-- The super-stack: pileStack the canonical member if it goes,
otherwise the other twin.  (If-cased rather than `<|>`: the branches'
conditions surface under `split`/`by_cases` without extra lemmas.) -/
def State.applySuperStack (st : State) (t : Card) : Option State :=
  if (st.apply (Move.pileStack (Card.canonicalOfPair t))).isSome then
    st.apply (Move.pileStack (Card.canonicalOfPair t))
  else st.apply (Move.pileStack (Card.canonicalOfPair t).flipSuit)

/-- The super-stack fires exactly when some twin can pileStack. -/
theorem State.isSome_applySuperStack (st : State) (t : Card) :
    (st.applySuperStack t).isSome = true ↔
      st.legal (Move.pileStack (Card.canonicalOfPair t)) = true ∨
        st.legal (Move.pileStack (Card.canonicalOfPair t).flipSuit) = true := by
  unfold State.applySuperStack
  by_cases h₁ : (st.apply (Move.pileStack t.canonicalOfPair)).isSome = true
  · rw [if_pos h₁]
    exact iff_of_true h₁ (Or.inl h₁)
  · rw [if_neg h₁]
    constructor
    · intro h
      exact Or.inr h
    · intro h
      rcases h with h | h
      · exact absurd h h₁
      · exact h

/-- The super-stack's successor is a physical successor — soundness by
construction (the folded move resolves to an ordinary `pileStack`). -/
theorem State.applySuperStack_sound {st st' : State} {t : Card}
    (h : st.applySuperStack t = some st') :
    ∃ m, st.apply m = some st' ∧
      (m = Move.pileStack (Card.canonicalOfPair t) ∨
        m = Move.pileStack (Card.canonicalOfPair t).flipSuit) := by
  unfold State.applySuperStack at h
  by_cases h₁ : (st.apply (Move.pileStack t.canonicalOfPair)).isSome = true
  · rw [if_pos h₁] at h
    exact ⟨_, h, Or.inl rfl⟩
  · rw [if_neg h₁] at h
    exact ⟨_, h, Or.inr rfl⟩

/-- **Super-stack sufficiency** (the completeness of the suit-symmetric
move set): you never need to pick "the right twin" — every win has a
twin-canonical line.  The canonical member is the pair-`false` one;
"canonical move" at a play position means: not stacking the
pair-`true` twin while its pair-`false` mate is ALSO stackable there.

TODO(proof) [H]: the pivot (`solvable_pileStack_twin_iff`) underlies
the exchange step — a non-canonical stack under simultaneous legality
has an equi-solvable successor by the canonical one; then a
well-founded descent on `cascadeMeasure` turns every win into a
canonical win (pair the pivot with the measure progress of the stack
moves — `cascade_escape_progress`'s sibling reasoning; draws and
autonomous play need care: the descent is over the *positions of the
first non-canonical stack* in the trace).  Probe-first per discipline. -/
theorem State.solvable_iff_canonicalStack {st : State}
    (hwf : st.WF) :
    st.solvableFrom ↔ ∃ play w, st.run play = some w ∧ w.isWin = true ∧
      ∀ (pre : List Move) (c : Card) (rest : List Move) (st₁ st₂ : State),
        play = pre ++ Move.pileStack c :: rest →
        st.run pre = some st₁ →
        st₁.apply (Move.pileStack c) = some st₂ →
        c.suit.pair = true →
        st₁.legal (Move.pileStack c.flipSuit) = true →
        False := sorry

/-! ### The mixed conjugation machinery (Φ state map + relabeled moves) -/

/-- The color-suit-swap relabeling of `t`'s color (the move-level half
of the mixed conjugation): flips the pair bit on suits of `t`'s color,
fixed elsewhere. -/
def Relabel.ofColorTwin (t : Card) : Relabel where
  suit := Suit.swapColorOf t
  suitInv := Suit.swapColorOf t
  left_inv := fun s => Suit.swapColorOf_swapColorOf t s
  right_inv := fun s => Suit.swapColorOf_swapColorOf t s
  coherent := by
    intro s s'
    rw [Suit.swapColorOf_color, Suit.swapColorOf_color]

/-- The Φ state map: contents swapped by `Card.swapFull t` (the color's
suit swap with the pair pinned), heights permuted by the color's suit
swap, the rest fixed. -/
def State.swapFull (t : Card) (st : State) : State where
  deal := { piles := fun a => (st.deal.piles a).map (Card.swapFull t),
            stock := st.deal.stock.map (Card.swapFull t) }
  board := st.board.mapByFull t
  heights := fun s => st.heights (Suit.swapColorOf t s)
  depths := st.depths
  stock := { cards := st.stock.cards.map (Card.swapFull t), cursor := st.stock.cursor }
  drawStep := st.drawStep

/-- The suit permutation backing `swapFull`'s heights: flip the pair
bit on `t`'s color, fix the other color.  An involution. -/
theorem State.swapFull_heights_relabel (st : State) (t c : Card) :
    (st.swapFull t).heights ((Relabel.ofColorTwin t).card c).suit = st.heights c.suit := by
  show st.heights (Suit.swapColorOf t (Suit.swapColorOf t c.suit)) = st.heights c.suit
  rw [Suit.swapColorOf_swapColorOf]

/-- Outside the pinned pair, the full swap and the color-swap relabel
agree on cards. -/
theorem Card.swapFull_eq_ofColorTwin_card_of_not_pair {t x : Card}
    (hp : ¬ (x = t ∨ x = t.flipSuit)) :
    Card.swapFull t x = (Relabel.ofColorTwin t).card x := by
  by_cases hc : x.suit.color = t.suit.color
  · rw [Card.swapFull_of_not_pair hp hc]
    show x.flipSuit = ⟨Suit.swapColorOf t x.suit, x.rank⟩
    have hs : x.flipSuit = ⟨x.suit.flipPair, x.rank⟩ := rfl
    rw [hs, Suit.swapColorOf]
    rw [if_pos hc]
  · rw [Card.swapFull_of_color_ne hc]
    show x = ⟨Suit.swapColorOf t x.suit, x.rank⟩
    rw [Suit.swapColorOf_of_color_ne hc]

/-! **The mixed conjugation** (the corrected form after the naive
versions' refutation): applying the suit-relabeled move to the
Φ-swapped state is applying the move and Φ-swapping the result.
License: WF + both twins on the tableau (so no equality probe — stock
`prev`, hidden boundary, or the foundation prefix — can meet a twin
outside the board).

## The third failure mode (recorded so it is not re-attempted)

Even the mixed conjugation is false AS AN EQUALITY at the twin-covering
arms: the move-naming map must pick a card for a cover target, so when
exactly one twin is bare the legality of covering disagrees across the
map (and even when both succeed, the cargo lands on different seats).
Seat and counter being *the same suit* is the irreducible conflict —
pinning fixes counters but breaks covers, relabeling fixes covers but
crosses counters at bumps, and the composite of the two breaks thirds.
What survives: **the pair-avoiding conjugation** below (true — every
probe of an avoiding move threads back through `π ∘ R = swapTwin`), and
the twin-touching steps are delegated to the pivot.  This is also the
documented reason `solvable_swapTwin` is solvability-level. -/

/-- A move *avoids* the pair: it never names `t`/`t.flipSuit` as its
card argument and never covers onto their base `inr`s. -/
def Move.avoidsPair (t : Card) : Move → Bool
  | .draw => true
  | .reveal c => !(c == t || c == t.flipSuit)
  | .deckPile c b | .stackPile c b | .pilePile c b =>
      !(c == t || c == t.flipSuit) &&
        match b with
        | Sum.inl _ => true
        | Sum.inr d => !(d == t || d == t.flipSuit)
  | .deckStack c | .pileStack c => !(c == t || c == t.flipSuit)

/-- **The pair-avoiding conjugation**: for moves that never touch the
pair, the Φ-state map precisely interchanges the game's semantics.
License: WF + both twins visible (so no equality probe can meet a twin
in the stock, the hidden slices, or the foundation prefix — the regions
where the pair would break the threading).

TODO(proof) [M]: the 7-arm guard translation, mirroring `apply_relabel`'s
pattern.  Kit: `mapByFull_topOf` (rfl), `mapByFull_bottomOf` (via
`Board.bottomOf_eq`'s roundtrips — order-free), `mapByFull_attach`/
`_detach`/`_aboveOf` (via `Board.ext_topOf` + fuel induction), the
State transfers `swapFull_isVis`/`_canPlace`/`_hidden`/`_topHidden`/
`_pileOfTopHidden`/`_prev`, `swapFull_heights_relabel` (done above),
`Card.swapFull t (R.card ·) = swapTwin t ·` on cards (the probe
threading), and the license bridges (twins excluded from stock/hidden
by the WF conjuncts at `hvis`/`hvis'`).  Hypothesis `hm` does the
arm-level case elimination. -/
theorem State.apply_swapFull_of_avoids {st : State} {t : Card}
    (hwf : st.WF) (hvis : st.isVis t = true) (hvis' : st.isVis t.flipSuit = true)
    {m : Move} (hm : m.avoidsPair t = true) :
    (st.swapFull t).apply (m.relabel (Relabel.ofColorTwin t))
      = (st.apply m).map (State.swapFull t) := sorry

/-! ### The twin bisimulation (strategy rewriting package)

The two-level relation that makes the strategy-modification proof
mechanical: `y` is `x`'s local swap (level 0) or the color-relabel of
it (level 1).  Each level covers the other's weak guard: level 0's
heights are untouched (tableau arms file verbatim) while level 1's
counters cross (foundation arms stay honest at twists); the level is
chosen per move at the pivot.  The side conditions keep the pair out
of the regions where equality probes would meet it (the stock's `prev`
and the hidden slices), so the only twins a probe can see are the two
on the tableau.

The crown (`solvable_swapTwin`, above) is assembled from the step + run
rows below; per the farm protocol the crown cites the sorried rows and
warns until they land. -/

/-- The twin bisimulation: the two levels, plus the probe-region
exclusions (both sides, for symmetry). -/
def State.SimTwin (t : Card) (x y : State) : Prop :=
  (y = x.swapTwin t ∨ y = (x.swapTwin t).relabelBy (Relabel.ofColorTwin t)) ∧
    (∀ c, c ∈ x.stock.cards ∨ c ∈ y.stock.cards → c ≠ t ∧ c ≠ t.flipSuit) ∧
      ∀ a c, c ∈ x.hidden a ∨ c ∈ y.hidden a → c ≠ t ∧ c ≠ t.flipSuit

/-- The pair never in the stock: WF + visible gives it for free. -/
theorem State.twin_notMem_stock_of_vis {st : State} (hwf : st.WF) {t : Card}
    (hvis : st.isVis t = true) : t ∉ st.stock.cards :=
  fun hmem => Cycle.posOf_mem hmem (hwf.vis_off_cycle t hvis)

/-- The pair never in the hidden slices, WF-free (the `vis_not_hidden`
conjunct speaks directly). -/
theorem State.twin_notHidden_of_vis {st : State} (hwf : st.WF) {t : Card}
    (hvis : st.isVis t = true) (a : Anchor) : t ∉ st.hidden a :=
  hwf.vis_not_hidden t hvis a

/-- The swapped state's hidden slices are the card-mapped slices. -/
theorem State.swapTwin_hidden (st : State) (t : Card) (a : Anchor) :
    (st.swapTwin t).hidden a = (st.hidden a).map (Card.swapTwin t) := by
  show ((st.deal.piles a).map (Card.swapTwin t)).take (st.depths a)
      = ((st.deal.piles a).take (st.depths a)).map (Card.swapTwin t)
  rw [List.map_take]

/-- The involution's membership map on a list: the mapped list stays
twin-free when the original is. -/
theorem twin_notMem_map {t c : Card} {l : List Card}
    (h₁ : t ∉ l) (h₂ : t.flipSuit ∉ l)
    (hmem : c ∈ l.map (Card.swapTwin t)) : c ≠ t ∧ c ≠ t.flipSuit := by
  obtain ⟨c₀, hmem₀, hswap⟩ := List.mem_map.mp hmem
  have hc₀ : c₀ ≠ t ∧ c₀ ≠ t.flipSuit := ⟨fun h => h₁ (h ▸ hmem₀), fun h => h₂ (h ▸ hmem₀)⟩
  constructor
  · intro hcon
    have : c₀ = t.flipSuit := by
      rw [hcon] at hswap
      have h' := congrArg (Card.swapTwin t) hswap
      rwa [Card.swapTwin_swapTwin, Card.swapTwin_self_left] at h'
    exact hc₀.2 this
  · intro hcon
    have : c₀ = t := by
      rw [hcon] at hswap
      have h' := congrArg (Card.swapTwin t) hswap
      rwa [Card.swapTwin_swapTwin, Card.swapTwin_self_right] at h'
    exact hc₀.1 this

/-- The stock side of the instance conditions. -/
theorem State.twin_stock_free {st : State} {t : Card}
    (hwf : st.WF) (hvis : st.isVis t = true) (hvis' : st.isVis t.flipSuit = true) :
    ∀ c, c ∈ st.stock.cards ∨ c ∈ (st.swapTwin t).stock.cards → c ≠ t ∧ c ≠ t.flipSuit := by
  intro c hc
  have h₁ := State.twin_notMem_stock_of_vis hwf hvis
  have h₂ := State.twin_notMem_stock_of_vis hwf hvis'
  rcases hc with hc | hc
  · exact ⟨fun h => h₁ (h ▸ hc), fun h => h₂ (h ▸ hc)⟩
  · have hmem : c ∈ st.stock.cards.map (Card.swapTwin t) := hc
    exact twin_notMem_map h₁ h₂ hmem

/-- The hidden side of the instance conditions. -/
theorem State.twin_hidden_free {st : State} {t : Card}
    (hwf : st.WF) (hvis : st.isVis t = true) (hvis' : st.isVis t.flipSuit = true) :
    ∀ a c, c ∈ st.hidden a ∨ c ∈ (st.swapTwin t).hidden a → c ≠ t ∧ c ≠ t.flipSuit := by
  intro a c hc
  have h₁ := State.twin_notHidden_of_vis hwf hvis a
  have h₂ := State.twin_notHidden_of_vis hwf hvis' a
  rcases hc with hc | hc
  · exact ⟨fun h => h₁ (h ▸ hc), fun h => h₂ (h ▸ hc)⟩
  · rw [State.swapTwin_hidden] at hc
    exact twin_notMem_map h₁ h₂ hc

/-- The state-level involution: exchanging the pair twice is the
identity.  TODO(proof) [M]: `state_ext` (Relabel.lean) over the six
fields; boards by `Board.ext_topOf` + funext + the pointwise
involutions (`swapTwin_swapTwin`, `Base.swapTwin_swapTwin`,
`Option.map_map`); the deal/stock by `List.map_map` + the pointwise
involution. -/
theorem State.swapTwin_swapTwin (t : Card) (st : State) :
    (st.swapTwin t).swapTwin t = st := sorry

/-- The step: from a simulated pair, any legal move has a translated
legal move, landing at a simulated successor.  TODO(proof) [H]: case
split on the level (`h.1`) and on the move; the avoiding moves do the
verbatim work of `apply_swapFull_of_avoids`; cover/reveal/stack moves
naming the pair pick level 1 (the counters cross: `_heights_relabel`);
the twin-stack pivot arms need the guards' equal counters —
`solvable_pileStack_twin_iff`'s local content — the pair guards are
the only spots needing the bares.  Side conditions propagate:
stocks shrink, hidden slices shrink. -/
theorem State.simTwin_step {t : Card} {x y : State} (h : State.SimTwin t x y)
    {m : Move} {x' : State} (hstep : x.apply m = some x') :
    ∃ m' : Move, ∃ y' : State, y.apply m' = some y' ∧ State.SimTwin t x' y' := sorry

/-- The run lift: a winning play of `x` transports to a winning play of
the simulated `y` (the win is read off `isWin` invariance along the
levels).  TODO(proof) [M]: induction on the play with `simTwin_step`
per move; nil is the `isWin` reading. -/
theorem State.simTwin_runWin {t : Card} {x y : State} (h : State.SimTwin t x y)
    {play : List Move} {w : State} (hrun : x.run play = some w) (hwin : w.isWin = true) :
    ∃ play' : List Move, ∃ w' : State, y.run play' = some w' ∧ w'.isWin = true := sorry

/-- The level-0 instance (the swap itself), at a licensed state. -/
theorem State.SimTwin.refl_right {st : State} {t : Card}
    (hwf : st.WF) (hvis : st.isVis t = true) (hvis' : st.isVis t.flipSuit = true) :
    State.SimTwin t st (st.swapTwin t) :=
  ⟨Or.inl rfl, State.twin_stock_free hwf hvis hvis', State.twin_hidden_free hwf hvis hvis'⟩

/-- The flipped instance: the original state seen from the swapped
side, level 0 (via the state involution). -/
theorem State.SimTwin.refl_left {st : State} {t : Card}
    (hwf : st.WF) (hvis : st.isVis t = true) (hvis' : st.isVis t.flipSuit = true) :
    State.SimTwin t (st.swapTwin t) st := by
  have hf := State.twin_stock_free hwf hvis hvis'
  have hg := State.twin_hidden_free hwf hvis hvis'
  refine ⟨Or.inl (State.swapTwin_swapTwin t st).symm, fun c hc => ?_, fun a c hc => ?_⟩
  · rcases hc with hc | hc
    · exact hf c (Or.inr hc)
    · exact hf c (Or.inl hc)
  · rcases hc with hc | hc
    · exact hg a c (Or.inr hc)
    · exact hg a c (Or.inl hc)

/-- The crown, strategy-rewritten: the win direction ↦ uses the
simulation centered at `st`; ↤ centers it at the swapped state.
Both directions cite the sorried `simTwin_step`/`simTwin_runWin` and
`swapTwin_swapTwin`; the side conditions come from WF + the twins'
visibility (refl_right/refl_left above, proven). -/
theorem State.solvable_swapTwin {st : State} {t : Card}
    (hwf : st.WF) (hvis : st.isVis t = true) (hvis' : st.isVis t.flipSuit = true) :
    (st.swapTwin t).solvableFrom ↔ st.solvableFrom := by
  constructor
  · rintro ⟨play, w, hrun, hwin⟩
    obtain ⟨play', w', hrun', hwin'⟩ :=
      State.simTwin_runWin (State.SimTwin.refl_left hwf hvis hvis') hrun hwin
    exact ⟨play', w', hrun', hwin'⟩
  · rintro ⟨play, w, hrun, hwin⟩
    obtain ⟨play', w', hrun', hwin'⟩ :=
      State.simTwin_runWin (State.SimTwin.refl_right hwf hvis hvis') hrun hwin
    exact ⟨play', w', hrun', hwin'⟩

/-- **Covering either twin is worth the same**: parking `x` on `t` or
on `t.flipSuit` — in the SAME state — never commits to "the wrong
twin": the successors are equi-solvable.  Routes through the same
machinery (the successors differ exactly in one pair of seats).
Dominance's `twinPair_placement_equi` is the `deckPile` instance and
merges here.

TODO(proof) [M]: after the conjugation lands; one `swapTwin`-relating
equation between the successors + the solvability transport. -/
theorem State.solvable_cover_twin_iff {st : State} {t x : Card} {st₁ st₂ : State}
    (hwf : st.WF) (hvis : st.isVis t = true) (hvis' : st.isVis t.flipSuit = true)
    (h₁ : st.apply (Move.pilePile x (Sum.inr t)) = some st₁)
    (h₂ : st.apply (Move.pilePile x (Sum.inr t.flipSuit)) = some st₂) :
    st₁.solvableFrom ↔ st₂.solvableFrom := sorry

/-- WF survives the local swap (for downstream consumers that carry
`hwf`): the deal maps stay duplicate-free (`swapTwin_inj` on maps), the
board edges re-read through `mapByTwin`, the stock's noDup + membership
follow by the map; heights untouched so the height conjuncts transfer
pointwise.

TODO(proof) [M]: conjunct-wise; the `board_edges` deal-adjacency clause
translates because the deal's piles were swapped too. -/
theorem State.swapTwin_wf {st : State} {t : Card} (hwf : st.WF) :
    (st.swapTwin t).WF := sorry
