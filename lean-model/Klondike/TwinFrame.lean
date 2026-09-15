import Klondike.TwinQuotient

/-!
# The twin replay — the growing correspondence (L1/O3, part ii)

The re-scoped interleaving lemma's substrate.  The climb-out consumer
(`exchange_merge_ply_root`, route step 2a) hands the mirror a state
that is the SOURCE with the board twin-swapped at the cargo `z` — the
board-only correspondence `M.board = ρ(S.board)` at `ρ = τ_z`, every
other field equal.  The source then replays its winning play; the
mirror must TRANSLATE it.  The provable half of that translation is
this file's kit:

* **§1 Twin maps** (`Card.IsTwinMap`): the correspondence's group —
  the partial products of twin transpositions.  On each color-rank
  class such a map is the identity or the twin flip, so it is an
  involution preserving every card's rank and color, it commutes with
  every other twin map, and composing one with a twin transposition
  `τ_q` is again one — the GROWTH operation
  `ρ' = τ_{ρ q} ∘ ρ` of the interleaving window.
* **§2 The board kit** (`Board.mapByRho`): the conjugation of a
  matching by a twin map — the `mapByTwin` construction at a general
  partial pair-flip, with the composition law
  (`mapByRho ρ ∘ mapByRho υ = mapByRho (ρ ∘ υ)`: the group action),
  the `topOf`/`bottomOf`/`attach`/`detach`/`aboveOf` transfer kit,
  and the state-level guard transfers (`isVis`, `canPlace`,
  `canMoveRun` — all board-and-rank/color reads, all twin-blind).
* **§3 The correspondence** (`State.TwinCorr`): the mirror game M
  tracked against the source S through a growing ρ — the board the
  ρ-relabel, the deal/stock/depths/drawStep identical, the off-suit
  heights equal, and the twin-suit stacked-set invariant
  (`M's stacked = ρ(S's stacked)`, stated per card:
  `M.heights (ρ c).suit > c.rank.toIdx ↔ S.heights c.suit > c.rank.toIdx`
  — the ladder-prefix rung arithmetic is exactly this per-card form).
* **§4 The clean step** (`State.TwinCorr.apply_clean`): the
  generalization of `apply_swapTwinBoard_clean` from the single
  transposition `τ_z` to an arbitrary twin map ρ — every height-blind
  move (draw/reveal/deckPile/pilePile, any cards) and every
  foundation move of an off-suit card translates, correspondence
  preserved.  The reveal case rides the hidden slices' ρ-freeness, the
  deckPile case the stock's (the `hhid`/`hstock` premises — at the ply
  result they are WF-consequences: z/z' seated).
* **§5 The on-suit steps**: the twin-suit foundation moves, the
  window's exact content.  The VERBATIM stacking (the rung aligned:
  `M.heights (ρ q).suit = q.rank.toIdx`), the GROWTH (the rung
  misaligned: the mirror stacks the FLIP `flip (ρ q)`, the
  correspondence grows to `τ_{ρ q} ∘ ρ` — the legality is DERIVED from
  the stacked-set invariant alone: the misalignment forces the flip's
  rung exact, no balance or prefix side-conditions), and the WORRY-BACK
  (translated through the correspondence when the twin rungs are
  within one — the no-skew premise `hskew`).
* **§6 The crossed-set frame** (`State.TwinCorrX` + the step family):
  the weakened correspondence for the growth's aftermath.  The
  frame carries the twin core, the stranded-card list `X` (the
  ρ-images of the source's stacked cards, still seated in the mirror
  at their old seats), and the board correspondence with per-clause
  escapes at exactly those cards: the card-SET conjugation is global
  (`vis_iff` — a crossing swaps within a twin pair, so the ρ-images of
  the two boards' seated cards coincide), the seat conjugation holds
  away from the partners and the stranded seats
  (`top_some`/`top_none`), each crossing's wanted seat is free
  (`top_wanted`), and the run walks conjugate on the stranded columns
  and stay inside the image walk elsewhere (`above_strand`,
  `above_sub`).  The full correspondence embeds at `X = []`
  (`State.TwinCorr.toTwinCorrX`).  **The step family**:
  the GROWTH PACKAGING (`State.TwinCorr.apply_pileStack_grow_X`, with
  the corner-freedom premises — the moved pair not deal-adjacent to
  itself) enters the frame with the single stranded card `ρ q`; the
  CATCH-UP DRAIN (`State.TwinCorrX.apply_pileStack_catchup`, with the
  alignment `State.TwinCore.rung_of_skew`) resolves a crossing: when
  the source stacks the partner, the mirror stacks the stranded card —
  the rung is DERIVED, the bareness rides the stranded-rider field,
  and the frame is restored at the filtered list; the VERBATIM
  on-suit stacking (`apply_pileStack_onsuit`, the rung aligned, the
  card not stranded, the card-seat bareness premise); the clean
  steps `apply_draw` / `apply_deckStack_off` / `apply_pileStack_off`
  (the no-attach kinds — no board reads, or the detach at the proper
  seat with the card-seat shape condition); and the ATTACH FAMILY with
  its L1/L2 landing premises — `apply_deckPile` (the stock card drawn
  onto a free base: the fixed point `ρ q = q` from the stock premise,
  the column over the moved card empty via
  `State.WF.no_topOf_of_stock`) and `apply_stackPile_off` (the
  off-suit worry-back: the same card returned at the ρ-image base,
  the column over it empty via `State.WF.no_topOf_of_found`).  Both
  carry the landing's shape premises — `hfree` (no strand at the
  mirror's landing seat), `hbare2` (no strand rides on the moved
  card), `hwalk` (no strand walk reads the landing seat), and `hL2`
  (the landing base's card-coordinate synchronized out of the
  strands' columns) — each a genuine run-level invariant the assembly
  must supply.  `apply_reveal_X` lands the reveal in the frame: the
  boundary card is deal-determined and hidden cards are `ρ`-fixed
  (`hhid`), so the mirror turns the SAME boundary at the SAME
  `hiddenBase`, the cover conjugates (`hcX`), and the hiddenness of
  the under-card makes every walk-condition (the strands never read
  the landing seat, the extension stays out of the strands' columns)
  DERIVABLE rather than premised — only the landing-seat and
  cover-column shape premises (`hfree`, `hcov`) remain.  Its walk
  work runs on two new kit lemmas: `Board.mem_aboveOf_extend` (a walk
  member's seat-top joins the walk — the fuel-margin induction) and
  `Board.mem_aboveOf_attach_two` (the two-step attach decomposition
  for a landing whose column is short).  `apply_stackPile_onsuit`
  lands the on-suit worry-back in the frame (the rung-aligned premise
  `halign : M.heights (ρ c).suit = c.rank.toIdx + 1`, supplied
  upstream by `State.TwinCore.stackPile_rung` from the no-skew
  condition): the mirror plays `stackPile (ρ c) (relabel ρ b)` with
  the same L1/L2 landing family, the rungs dropping in tandem through
  `State.stacked_drop_aux`.

  **The two residuals.**  (1) `apply_pilePile_X` (the detach+attach
  run move): the L1/L2 family is needed at BOTH the vacated base
  (`hL2₀`/`hwalk₀`) and the landing base, the self-landing guard
  transfers through `above_sub` + hL2, and the vacated-seat reads
  conjugate (`ρ d₀ ∈ c' :: M.walk ↔ d₀ ∈ ρ c' :: S.walk`) via
  `above_strand`.  The seeded-walk monotonicity kit is NOW LANDED:
  `Board.aboveOf_go_pair` (the seeded walk stays inside the seed and
  the plain walk from the same seat — the sub-seed's stops are a
  subset of the seed's, so the two collect the same cards while both
  run), `Board.aboveOf_go_mono_one`/`_fuel_add`/`_sat` (the fuel
  monotonicity and the 52-saturation), and
  `Board.mem_aboveOf_attach_run` (the run-column attach
  decomposition: a successor walk member is old, the new card, or in
  the new card's own walk — NO self-guard needed, the subsumption
  handles the continuation into the run), plus the two
  walk-structure lemmas the pilePile chains need:
  `Board.aboveOf_go_pred` (every walk member was read off a walk
  member's seat — the downward step of the run-chain) and
  `Board.aboveOf_go_detach_split` (the detach-split: every member of
  the original walk survives into the detached walk or lies in the
  run above the vacated top).  What REMAINS for pilePile's
  `above_sub` is: the walk-through (the transitivity — `e ∈
  walk(w) ∧ w ∈ walk(z) → e ∈ walk(z)`), the chain-inductions (the
  run's images are only reachable through the vacated cell, in both
  the detached and the composite mirror), the reader-forcing, and
  the reader-transfer premise `hread` (the S-side d'-readers' walks
  never read the vacated seat) — plus the acyclicity fact for the
  head-corners.  The run-shape premises
  (the vacated and landing coordinates not in the run:
  `d ∉ c :: S.aboveOf c`) are forest-facts, true on every WF board
  reachable from a real deal but not derivable from the frame alone.
  (2) The on-suit deckStack (Residual 2) — DECIDED BY PROBE
  (`Temp/opencode/rhoreplay2.lean` §4) and LANDED for the non-pair
  case: `apply_deckStack_onsuit` (`hqρ : ρ q = q`, the pinning
  premise `hpinn : M.heights q.suit = q.rank.toIdx` — the rungs
  pinned equal by the stacked-set iff, so the misaligned case cannot
  occur under a fixed `ρ`), the same-card response with the
  same-suit double-bump, the pair-card cross-term saved by
  rank-separation.  The PAIR card (`q ∈ {z, flip z}`) has NO in-kind
  response (the mirror's stacking `q` bumps `q.suit` while the image
  `ρ q = flip q` needs the other twin suit), and the probe confirms
  the deckPile-parking fires at a free base-compatible seat but it
  breaks the frame's `vis_iff` without a growth — so the response is
  run-level (parking-with-twin-swap or deferral-with-debt); the
  window for plays avoiding on-suit deckStacks of PAIR cards is the
  honest fallback.  The run-level assembly
  (`State.solvable_of_twinCorr_window`) is gated on both.
* **§7 The window assembly** (`State.solvable_of_twinCorr_clean`):
  the no-twin-foundation window — if the source's winning play never
  makes a twin-suit foundation move, the mirror replays the translated
  play and wins (the heights track throughout, `isWin` transfers).
  With the growth steps of §5 this covers the climb-out's clean core;
  the residue — the mid-episode BOARD CROSSING at a growth (see
  `State.TwinCorr.apply_pileStack_grow`'s conclusion) and the
  deckStack-at-a-misaligned-rung corner — is the open part of the
  interleaving lemma, reported in the route notes.  §6's frame and its
  catch-up drain are that residue's substrate: the growth introduces
  the crossing and the catch-up removes it; the remaining content is
  the growth's own entry into the frame (the growth conclusion
  repackaged at the four excluded seats) and the run-level scheduling
  that interleaves them with the clean moves, the worry-backs, and the
  twin-suit deckStacks (the stock is shared, so a lagged rung needs
  the deckPile-parking response or a deferral).

The probe (`Temp/opencode/rhoreplay2.lean`) validates the dynamics on
the w15wfmerge miniature: the growth-rule mirror (TWO growths, at ♠Q
and ♠K) and the mid-episode worry-back both win from the board-only
swapped state, and the crossed seats are exhibited directly.
-/

/-! ## §1. Twin maps — the correspondence's group -/

/-- The twin flip's suit component. -/
theorem Card.flipSuit_suit (c : Card) : c.flipSuit.suit = c.suit.flipPair := rfl

/-- A TWIN MAP: a partial product of twin transpositions.  On each
color-rank class `{c, c.flipSuit}` the map is the identity or the twin
flip (the first conjunct, per card); in particular it is an involution
(the second conjunct), hence a bijection preserving every card's rank
and color, commuting with every other twin map — the
elementary-abelian-2 structure of the pair group. -/
def Card.IsTwinMap (ρ : Card → Card) : Prop :=
  (∀ c, ρ c = c ∨ ρ c = c.flipSuit) ∧ (∀ c, ρ (ρ c) = c)

theorem Card.IsTwinMap.pair {ρ : Card → Card} (h : Card.IsTwinMap ρ) (c : Card) :
    ρ c = c ∨ ρ c = c.flipSuit := h.1 c

theorem Card.IsTwinMap.invol {ρ : Card → Card} (h : Card.IsTwinMap ρ) (c : Card) :
    ρ (ρ c) = c := h.2 c

/-- An involution is injective. -/
theorem Card.IsTwinMap.inj {ρ : Card → Card} (h : Card.IsTwinMap ρ) :
    Function.Injective ρ := by
  intro a b hab
  have hcon := congrArg ρ hab
  rw [h.invol a, h.invol b] at hcon
  exact hcon

/-- Twin maps preserve the rank. -/
theorem Card.IsTwinMap.rank {ρ : Card → Card} (h : Card.IsTwinMap ρ) (c : Card) :
    (ρ c).rank = c.rank := by
  rcases h.pair c with hc | hc <;> rw [hc] <;> rfl

/-- Twin maps preserve the color (definitionally, per conjunct). -/
theorem Card.IsTwinMap.color {ρ : Card → Card} (h : Card.IsTwinMap ρ) (c : Card) :
    (ρ c).suit.color = c.suit.color := by
  rcases h.pair c with hc | hc <;> rw [hc] <;> rfl

/-- Twin maps commute with the twin flip: `ρ(flip c) = flip(ρ c)`
(the class structure — the pair-flip is uniform on the class). -/
theorem Card.IsTwinMap.flip_comm {ρ : Card → Card} (h : Card.IsTwinMap ρ) (c : Card) :
    ρ c.flipSuit = (ρ c).flipSuit := by
  rcases h.pair c with hc | hc
  · rcases h.pair c.flipSuit with hf | hf
    · rw [hc, hf]
    · exfalso
      have h1 : ρ c = ρ c.flipSuit := by rw [hc, hf, Card.flipSuit_flipSuit]
      exact Card.flipSuit_ne c (h.inj h1).symm
  · have h1 : ρ c.flipSuit = c := by
      have h2 := h.invol c
      rw [hc] at h2
      exact h2
    rw [h1, hc, Card.flipSuit_flipSuit]

/-- The identity is a twin map. -/
theorem Card.IsTwinMap.id : Card.IsTwinMap id :=
  ⟨fun _ => Or.inl rfl, fun _ => rfl⟩

/-- A twin transposition is a twin map. -/
theorem Card.IsTwinMap.swapTwin (t : Card) : Card.IsTwinMap (Card.swapTwin t) :=
  ⟨fun c => by
      by_cases h1 : c = t
      · exact Or.inr (by rw [h1]; exact Card.swapTwin_self_left t)
      · by_cases h2 : c = t.flipSuit
        · exact Or.inr (by rw [h2, Card.swapTwin_self_right t, Card.flipSuit_flipSuit])
        · exact Or.inl (Card.swapTwin_of_ne h1 h2),
    fun c => Card.swapTwin_swapTwin t c⟩

/-- **Twin maps commute** (two partial pair-flips act on disjoint
class-coordinates). -/
theorem Card.IsTwinMap.comm {ρ υ : Card → Card} (hρ : Card.IsTwinMap ρ)
    (hυ : Card.IsTwinMap υ) : ∀ x, ρ (υ x) = υ (ρ x) := by
  intro x
  rcases hυ.pair x with hu | hu
  · rw [hu]
    rcases hρ.pair x with hr | hr
    · rw [hr]; exact hu.symm
    · rw [hr, hυ.flip_comm x, hu]
  · rw [hu, hρ.flip_comm x]
    rcases hρ.pair x with hr | hr
    · rw [hr]; exact hu.symm
    · rw [hr, Card.flipSuit_flipSuit, ← hu, hυ.invol x]

/-- **The group is closed under composition**: `ρ ∘ υ` is a twin map. -/
theorem Card.IsTwinMap.comp {ρ υ : Card → Card} (hρ : Card.IsTwinMap ρ)
    (hυ : Card.IsTwinMap υ) : Card.IsTwinMap (ρ ∘ υ) := by
  refine ⟨fun c => ?_, fun c => ?_⟩
  · show ρ (υ c) = c ∨ ρ (υ c) = c.flipSuit
    rcases hυ.pair c with hu | hu
    · rcases hρ.pair c with hr | hr
      · exact Or.inl (by rw [hu, hr])
      · exact Or.inr (by rw [hu, hr])
    · rw [hu, hρ.flip_comm c]
      rcases hρ.pair c with hr | hr <;> rw [hr] <;> simp
  · show ρ (υ (ρ (υ c))) = c
    have hc := hρ.comm hυ (υ c)
    rw [show υ (ρ (υ c)) = ρ (υ (υ c)) from hc.symm, hυ.invol c, hρ.invol c]

/-- **The growth composition**: a twin map composed with a twin
transposition is a twin map (`ρ' = τ_q ∘ ρ` in the window). -/
theorem Card.IsTwinMap.comp_swapTwin {ρ : Card → Card} (hρ : Card.IsTwinMap ρ) (q : Card) :
    Card.IsTwinMap (Card.swapTwin q ∘ ρ) :=
  (Card.IsTwinMap.swapTwin q).comp hρ

/-- A twin transposition's representative is immaterial on a twin
map's image: `τ_{ρ q} = τ_q` (the PAIR, not the card). -/
theorem Card.swapTwin_pair_congr {ρ : Card → Card} (hρ : Card.IsTwinMap ρ) (q : Card) :
    Card.swapTwin (ρ q) = Card.swapTwin q := by
  rcases hρ.pair q with h | h
  · rw [h]
  · funext x
    rw [h]
    exact Card.swapTwin_flipSuit q x

/-- The off-suit closure of the growth: if ρ fixes every off-suit
card, so does `τ_q ∘ ρ` for an on-suit q. -/
theorem Card.IsTwinMap.fixes_off_comp_swapTwin {ρ : Card → Card} {σ : Suit}
    (hfix : ∀ c, c.suit ≠ σ → c.suit ≠ σ.flipPair → ρ c = c)
    {q : Card} (honq : q.suit = σ ∨ q.suit = σ.flipPair)
    (c : Card) (h1 : c.suit ≠ σ) (h2 : c.suit ≠ σ.flipPair) :
    (Card.swapTwin q ∘ ρ) c = c := by
  have hcρ : ρ c = c := hfix c h1 h2
  have hqfs : q.flipSuit.suit = σ ∨ q.flipSuit.suit = σ.flipPair := by
    show q.suit.flipPair = σ ∨ q.suit.flipPair = σ.flipPair
    rcases honq with hs | hs
    · rw [hs]; exact Or.inr rfl
    · rw [hs]; exact Or.inl (Suit.flipPair_flipPair σ)
  have hqc : c ≠ q := by
    intro hcon; subst hcon
    rcases honq with hs | hs
    · exact h1 hs
    · exact h2 hs
  have hqc' : c ≠ q.flipSuit := by
    intro hcon; subst hcon
    rcases hqfs with hs | hs
    · exact h1 hs
    · exact h2 hs
  show Card.swapTwin q (ρ c) = c
  rw [hcρ, Card.swapTwin_of_ne hqc hqc']

/-- A twin map's image of an on-suit card is on-suit (the pair of
twin suits is ρ-stable). -/
theorem Card.IsTwinMap.suit_mem {ρ : Card → Card} {σ : Suit} (hρ : Card.IsTwinMap ρ)
    {c : Card} (hon : c.suit = σ ∨ c.suit = σ.flipPair) :
    (ρ c).suit = σ ∨ (ρ c).suit = σ.flipPair := by
  rcases hρ.pair c with h | h
  · rw [h]; exact hon
  · rw [h, Card.flipSuit_suit]
    rcases hon with hs | hs
    · rw [hs]; exact Or.inr rfl
    · rw [hs]; exact Or.inl (Suit.flipPair_flipPair σ)

/-- The two-suit trichotomy: an on-suit suit other than σ is σ'. -/
theorem Card.suit_mem_two {σ : Suit} {s : Suit} (h : s = σ ∨ s = σ.flipPair) (hne : s ≠ σ) :
    s = σ.flipPair := by
  rcases h with h1 | h1
  · exact absurd h1 hne
  · exact h1

/-- Two on-suit cards of the same rank are the pair: each rank has
exactly one card per twin suit. -/
theorem Card.eq_or_flip_of_onSuit {σ : Suit} {x q : Card}
    (hx : x.suit = σ ∨ x.suit = σ.flipPair)
    (hq : q.suit = σ ∨ q.suit = σ.flipPair)
    (hr : x.rank = q.rank) :
    x = q ∨ x = q.flipSuit := by
  rcases hx with hx | hx <;> rcases hq with hq | hq
  · exact Or.inl (by rw [Card.mk.injEq]; exact ⟨hx.trans hq.symm, hr⟩)
  · exact Or.inr (by
      rw [Card.mk.injEq]
      refine ⟨by rw [Card.flipSuit_suit, hq, hx, Suit.flipPair_flipPair], ?_⟩
      rw [Card.flipSuit_rank]; exact hr)
  · exact Or.inr (by
      rw [Card.mk.injEq]
      refine ⟨by rw [Card.flipSuit_suit, hq, hx], ?_⟩
      rw [Card.flipSuit_rank]; exact hr)
  · exact Or.inl (by rw [Card.mk.injEq]; exact ⟨hx.trans hq.symm, hr⟩)

/-- Every rank index below 13 is a rank's (the rung arithmetic's
boundary cards). -/
theorem Rank.exists_toIdx : ∀ (n : Nat), n < 13 → ∃ r : Rank, r.toIdx = n
  | 0, _ => ⟨.ace, rfl⟩
  | 1, _ => ⟨.two, rfl⟩
  | 2, _ => ⟨.three, rfl⟩
  | 3, _ => ⟨.four, rfl⟩
  | 4, _ => ⟨.five, rfl⟩
  | 5, _ => ⟨.six, rfl⟩
  | 6, _ => ⟨.seven, rfl⟩
  | 7, _ => ⟨.eight, rfl⟩
  | 8, _ => ⟨.nine, rfl⟩
  | 9, _ => ⟨.ten, rfl⟩
  | 10, _ => ⟨.jack, rfl⟩
  | 11, _ => ⟨.queen, rfl⟩
  | 12, _ => ⟨.king, rfl⟩
  | n + 13, h => absurd h (by omega)

/-! ## §2. The base/board kit — the ρ-conjugation -/

/-- The base-level relabeling induced by a card relabeling `ρ`
(anchors fixed, card-seats relabeled). -/
def Base.relabel (ρ : Card → Card) : Base → Base := Sum.map id ρ

theorem Base.relabel_inr (ρ : Card → Card) (c : Card) :
    Base.relabel ρ (Sum.inr c) = Sum.inr (ρ c) := rfl

theorem Base.relabel_invol {ρ : Card → Card} (hρ : Card.IsTwinMap ρ) (b : Base) :
    Base.relabel ρ (Base.relabel ρ b) = b := by
  cases b with
  | inl a => rfl
  | inr c => show Sum.inr (ρ (ρ c)) = _; rw [hρ.invol c]

theorem Base.relabel_inj {ρ : Card → Card} (hρ : Card.IsTwinMap ρ) {b₁ b₂ : Base}
    (h : Base.relabel ρ b₁ = Base.relabel ρ b₂) : b₁ = b₂ := by
  have hcon := congrArg (Base.relabel ρ) h
  rw [Base.relabel_invol hρ b₁, Base.relabel_invol hρ b₂] at hcon
  exact hcon

theorem Base.relabel_comp (ρ υ : Card → Card) (b : Base) :
    Base.relabel (ρ ∘ υ) b = Base.relabel ρ (Base.relabel υ b) := by
  cases b <;> rfl

theorem Base.relabel_swapTwin (t : Card) (b : Base) :
    Base.relabel (Card.swapTwin t) b = Base.swapTwin t b := rfl

/-- **The twin-map conjugation of a board**: every seated card and
every card-seat relabeled by `ρ` — the `mapByTwin` construction at a
general partial pair-flip.  The matching law holds because a twin map
is an involution. -/
def Board.mapByRho {ρ : Card → Card} (hρ : Card.IsTwinMap ρ) (bd : Board) : Board where
  topOf := fun b => (bd.topOf (Base.relabel ρ b)).map ρ
  inj := by
    intro b₁ b₂ c h₁ h₂
    obtain ⟨x, hx, hx'⟩ := Option.map_eq_some_iff.mp h₁
    obtain ⟨y, hy, hy'⟩ := Option.map_eq_some_iff.mp h₂
    have hxy : x = y := hρ.inj (hx'.trans hy'.symm)
    subst hxy
    exact Base.relabel_inj hρ (bd.inj _ _ _ hx hy)

theorem Board.mapByRho_topOf {ρ : Card → Card} (hρ : Card.IsTwinMap ρ) (bd : Board)
    (b : Base) :
    (Board.mapByRho hρ bd).topOf b = (bd.topOf (Base.relabel ρ b)).map ρ := rfl

theorem Board.mapByRho_topOf_relabel {ρ : Card → Card} (hρ : Card.IsTwinMap ρ) (bd : Board)
    (b : Base) :
    (Board.mapByRho hρ bd).topOf (Base.relabel ρ b) = (bd.topOf b).map ρ := by
  rw [Board.mapByRho_topOf, Base.relabel_invol hρ b]

theorem Board.mapByRho_topOf_inl {ρ : Card → Card} (hρ : Card.IsTwinMap ρ) (bd : Board)
    (a : Anchor) :
    (Board.mapByRho hρ bd).topOf (Sum.inl a) = (bd.topOf (Sum.inl a)).map ρ := by
  rw [Board.mapByRho_topOf]; rfl

theorem Board.mapByRho_topOf_inr {ρ : Card → Card} (hρ : Card.IsTwinMap ρ) (bd : Board)
    (c : Card) :
    (Board.mapByRho hρ bd).topOf (Sum.inr (ρ c)) = (bd.topOf (Sum.inr c)).map ρ := by
  rw [Board.mapByRho_topOf]
  show (bd.topOf (Sum.inr (ρ (ρ c)))).map ρ = _
  rw [hρ.invol c]

/-- The local twin swap IS the twin-map conjugation at `τ_t`. -/
theorem Board.mapByTwin_eq_mapByRho (t : Card) (bd : Board) :
    bd.mapByTwin t = Board.mapByRho (Card.IsTwinMap.swapTwin t) bd := by
  apply Board.ext_topOf
  funext b
  rfl

/-- **The group action**: conjugating by ρ then υ is conjugating by
`υ ∘ ρ` (twin maps commute, so the order is immaterial). -/
theorem Board.mapByRho_comp {ρ υ : Card → Card} (hρ : Card.IsTwinMap ρ)
    (hυ : Card.IsTwinMap υ) (bd : Board) :
    Board.mapByRho hρ (Board.mapByRho hυ bd) = Board.mapByRho (hρ.comp hυ) bd := by
  apply Board.ext_topOf
  funext b
  have hcomm : υ ∘ ρ = ρ ∘ υ := funext (fun x => (hρ.comm hυ x).symm)
  show ((Board.mapByRho hυ bd).topOf (Base.relabel ρ b)).map ρ
    = (bd.topOf (Base.relabel (ρ ∘ υ) b)).map (ρ ∘ υ)
  rw [Board.mapByRho_topOf, ← Base.relabel_comp, hcomm, Option.map_map]

theorem Board.mapByRho_bottomOf {ρ : Card → Card} (hρ : Card.IsTwinMap ρ) (bd : Board)
    (c : Card) :
    (Board.mapByRho hρ bd).bottomOf (ρ c) = (bd.bottomOf c).map (Base.relabel ρ) := by
  cases hb : bd.bottomOf c with
  | none =>
      refine (Board.bottomOf_eq_none _ _).mpr (fun b' hb' => ?_)
      rw [Board.mapByRho_topOf] at hb'
      obtain ⟨x, hx, hx'⟩ := Option.map_eq_some_iff.mp hb'
      have hxc : x = c := hρ.inj hx'
      rw [hxc] at hx
      exact (Board.bottomOf_eq_none bd c).mp hb _ hx
  | some b =>
      show (Board.mapByRho hρ bd).bottomOf (ρ c) = some (Base.relabel ρ b)
      refine (Board.bottomOf_eq _ _ _).mpr ?_
      rw [Board.mapByRho_topOf_relabel, (Board.bottomOf_eq bd c b).mp hb, Option.map_some]

theorem Board.mapByRho_attach {ρ : Card → Card} (hρ : Card.IsTwinMap ρ) {bd : Board}
    {b : Base} {c : Card} {bd' : Board} (h : bd.attach b c = some bd') :
    (Board.mapByRho hρ bd).attach (Base.relabel ρ b) (ρ c)
      = some (Board.mapByRho hρ bd') := by
  have hne : bd.attach b c ≠ none := by rw [h]; simp
  obtain ⟨htop, hbot⟩ := (Board.attach_eq_some_iff bd b c).mp hne
  have htopR : (Board.mapByRho hρ bd).topOf (Base.relabel ρ b) = none := by
    rw [Board.mapByRho_topOf_relabel, htop]; rfl
  have hbotR : (Board.mapByRho hρ bd).bottomOf (ρ c) = none := by
    rw [Board.mapByRho_bottomOf, hbot]; rfl
  have hneR : (Board.mapByRho hρ bd).attach (Base.relabel ρ b) (ρ c) ≠ none :=
    Board.attach_eq_some_iff _ _ _ |>.mpr ⟨htopR, hbotR⟩
  cases hR : (Board.mapByRho hρ bd).attach (Base.relabel ρ b) (ρ c) with
  | none => rw [hR] at hneR; simp at hneR
  | some bdR =>
      rw [Option.some.injEq]
      refine Board.ext_topOf (funext (fun b'' => ?_))
      by_cases hbb : b'' = Base.relabel ρ b
      · rw [hbb, Board.attach_topOf _ _ _ hR, Board.mapByRho_topOf_relabel,
          Board.attach_topOf _ _ _ h, Option.map_some]
      · rw [Board.attach_topOf_ne _ _ _ hR hbb, Board.mapByRho_topOf]
        have hcb : Base.relabel ρ b'' ≠ b := fun hcon => hbb (by
          have hc2 := Base.relabel_invol hρ b''
          rw [hcon] at hc2
          exact hc2.symm)
        rw [Board.mapByRho_topOf, Board.attach_topOf_ne _ _ _ h hcb]

theorem Board.mapByRho_detach {ρ : Card → Card} (hρ : Card.IsTwinMap ρ) (bd : Board)
    (b : Base) :
    (Board.mapByRho hρ bd).detach (Base.relabel ρ b) = (bd.detach b).mapByRho hρ := by
  apply Board.ext_topOf
  funext b''
  by_cases hbb : b'' = Base.relabel ρ b
  · rw [hbb]
    show (if Base.relabel ρ b = Base.relabel ρ b then none
        else (Board.mapByRho hρ bd).topOf (Base.relabel ρ b))
      = ((bd.detach b).mapByRho hρ).topOf (Base.relabel ρ b)
    rw [if_pos rfl, Board.mapByRho_topOf_relabel, Board.detach_topOf]
    rfl
  · show (if b'' = Base.relabel ρ b then none else (Board.mapByRho hρ bd).topOf b'')
      = ((bd.detach b).mapByRho hρ).topOf b''
    have hcb : Base.relabel ρ b'' ≠ b := fun hcon => hbb (by
      have hc2 := Base.relabel_invol hρ b''
      rw [hcon] at hc2
      exact hc2.symm)
    rw [if_neg hbb, Board.mapByRho_topOf, Board.mapByRho_topOf,
      Board.detach_topOf_ne _ _ _ hcb]

theorem beq_twinMap {ρ : Card → Card} (hρ : Card.IsTwinMap ρ) (x y : Card) :
    ((ρ x == ρ y) : Bool) = (x == y) := by
  by_cases hxy : x = y
  · rw [hxy]
    rw [show ((ρ y == ρ y) : Bool) = true from decide_eq_true rfl,
        show ((y == y) : Bool) = true from decide_eq_true rfl]
  · have h1 : (ρ x == ρ y) = false := by
      cases hb : (ρ x == ρ y) with
      | true => exact absurd (hρ.inj (of_decide_eq_true hb)) hxy
      | false => rfl
    have h2 : (x == y) = false := by
      cases hb : (x == y) with
      | true => exact absurd (of_decide_eq_true hb) hxy
      | false => rfl
    rw [h1, h2]

theorem contains_twinMap {ρ : Card → Card} (hρ : Card.IsTwinMap ρ) :
    ∀ (l : List Card) (x : Card),
    (l.map ρ).contains (ρ x) = l.contains x := by
  intro l
  induction l with
  | nil => intro x; rfl
  | cons a tl ih =>
      intro x
      show ((ρ x == ρ a) || (tl.map ρ).contains (ρ x)) = (x == a || tl.contains x)
      rw [ih x, beq_twinMap hρ x a]

theorem Board.mapByRho_aboveOf_go {ρ : Card → Card} (hρ : Card.IsTwinMap ρ) (bd : Board) :
    ∀ (fuel : Nat) (b : Base) (acc : List Card),
    Board.aboveOf.go (Board.mapByRho hρ bd) fuel (Base.relabel ρ b) (acc.map ρ)
      = (Board.aboveOf.go bd fuel b acc).map ρ := by
  intro fuel
  induction fuel with
  | zero => intro b acc; rfl
  | succ n ih =>
      intro b acc
      rw [Board.aboveOf_go_succ, Board.aboveOf_go_succ, Board.mapByRho_topOf_relabel]
      cases hb : bd.topOf b with
      | none => rfl
      | some x =>
          show (if (acc.map ρ).contains (ρ x) then acc.map ρ
                else Board.aboveOf.go (Board.mapByRho hρ bd) n (Sum.inr (ρ x))
                  (ρ x :: acc.map ρ))
            = (if acc.contains x then acc
               else Board.aboveOf.go bd n (Sum.inr x) (x :: acc)).map ρ
          rw [contains_twinMap hρ acc x]
          by_cases hac : acc.contains x = true
          · rw [if_pos hac, if_pos hac]
          · rw [if_neg hac, if_neg hac]
            exact ih (Sum.inr x) (x :: acc)

theorem Board.mapByRho_aboveOf {ρ : Card → Card} (hρ : Card.IsTwinMap ρ) (bd : Board)
    (c : Card) :
    (Board.mapByRho hρ bd).aboveOf (ρ c) = (bd.aboveOf c).map ρ :=
  Board.mapByRho_aboveOf_go hρ bd 52 (Sum.inr c) []

/-! ### The state-level guard transfers (all reads are twin-blind) -/

theorem canSitOn_twinMap {ρ : Card → Card} (hρ : Card.IsTwinMap ρ) (c d : Card) :
    canSitOn (ρ c) (ρ d) = canSitOn c d := by
  have h1 : (ρ c).rank.toIdx + 1 = (ρ d).rank.toIdx
      ↔ c.rank.toIdx + 1 = d.rank.toIdx := by
    rw [Card.IsTwinMap.rank hρ c, Card.IsTwinMap.rank hρ d]
  have h2 : (ρ c).suit.color ≠ (ρ d).suit.color ↔ c.suit.color ≠ d.suit.color := by
    rw [Card.IsTwinMap.color hρ c, Card.IsTwinMap.color hρ d]
  simp [canSitOn, h1, h2]

theorem State.isVis_relabel {ρ : Card → Card} {S M : State} (hρ : Card.IsTwinMap ρ)
    (hb : M.board = Board.mapByRho hρ S.board) (c : Card) :
    M.isVis (ρ c) = S.isVis c := by
  simp only [State.isVis, hb, Board.mapByRho_bottomOf]
  cases S.board.bottomOf c with
  | none => rfl
  | some b => rfl

theorem State.canPlace_relabel {ρ : Card → Card} {S M : State} (hρ : Card.IsTwinMap ρ)
    (hb : M.board = Board.mapByRho hρ S.board) (c : Card) (b : Base) :
    M.canPlace (ρ c) (Base.relabel ρ b) = S.canPlace c b := by
  cases b with
  | inl a =>
      show (decide (M.board.topOf (Base.relabel ρ (Sum.inl a)) = none)
        && decide ((ρ c).rank = Rank.king))
        = (decide (S.board.topOf (Sum.inl a) = none) && decide (c.rank = Rank.king))
      rw [show Base.relabel ρ (Sum.inl a) = Sum.inl a from rfl, hb,
        Board.mapByRho_topOf_inl, Card.IsTwinMap.rank hρ c]
      cases S.board.topOf (Sum.inl a) with
      | none => rfl
      | some x => rfl
  | inr d =>
      show (decide (M.board.topOf (Base.relabel ρ (Sum.inr d)) = none)
        && (M.isVis (ρ d) && canSitOn (ρ c) (ρ d)))
        = (decide (S.board.topOf (Sum.inr d) = none) && (S.isVis d && canSitOn c d))
      rw [show Base.relabel ρ (Sum.inr d) = Sum.inr (ρ d) from rfl, hb,
        Board.mapByRho_topOf_inr, State.isVis_relabel hρ hb, canSitOn_twinMap hρ c d]
      cases S.board.topOf (Sum.inr d) with
      | none => rfl
      | some x => rfl

theorem State.canMoveRun_relabel {ρ : Card → Card} {S M : State} (hρ : Card.IsTwinMap ρ)
    (hb : M.board = Board.mapByRho hρ S.board) (c : Card) (b : Base) :
    M.canMoveRun (ρ c) (Base.relabel ρ b) = S.canMoveRun c b := by
  cases b with
  | inl a =>
      show (M.canPlace (ρ c) (Base.relabel ρ (Sum.inl a)) && true)
        = (S.canPlace c (Sum.inl a) && true)
      rw [State.canPlace_relabel hρ hb c (Sum.inl a)]
  | inr d =>
      show (M.canPlace (ρ c) (Base.relabel ρ (Sum.inr d))
        && !((M.board).aboveOf (ρ c)).contains (ρ d))
        = (S.canPlace c (Sum.inr d) && !(S.board.aboveOf c).contains d)
      rw [hb, State.canPlace_relabel hρ hb c (Sum.inr d), Board.mapByRho_aboveOf,
        contains_twinMap hρ]

/-! ## §3. The correspondence — the growing ρ

The mirror game M tracked against the source S.  The core relation
(`State.TwinCore`) carries every field except the board; the full
correspondence (`State.TwinCorr`) adds the board conjugation.  The
stacked-set invariant is stated PER CARD — `ρ c` is stacked in M
exactly when `c` is stacked in S — which, because a state's stacked
cards of a suit are exactly the ranks below its height, IS the full
ladder-prefix rung arithmetic (the image of a ladder prefix under a
boundary twin transposition is a ladder prefix, per-card). -/

/-- The fields-and-heights half of the correspondence: the mirror's
deal/stock/depths/drawStep are the source's, the off-suit heights
agree, and the twin-suit stacked sets correspond through ρ. -/
structure State.TwinCore (ρ : Card → Card) (σ : Suit) (S M : State) : Prop where
  /-- ρ is a partial product of twin transpositions. -/
  isTwinMap : Card.IsTwinMap ρ
  /-- ρ fixes every off-suit card (the growth happens on the twin suits). -/
  fixes_off : ∀ c, c.suit ≠ σ → c.suit ≠ σ.flipPair → ρ c = c
  /-- the deals coincide (the board-only correspondence). -/
  deal_eq : M.deal = S.deal
  /-- the reveal boundaries coincide. -/
  depths_eq : M.depths = S.depths
  /-- the stock cycles coincide. -/
  stock_eq : M.stock = S.stock
  /-- the draw steps coincide. -/
  step_eq : M.drawStep = S.drawStep
  /-- the off-suit foundation heights agree. -/
  heights_off : ∀ s, s ≠ σ → s ≠ σ.flipPair → M.heights s = S.heights s
  /-- **the stacked-set invariant**: for a twin-suit card `c`, the card
  `ρ c` sits below M's rung of its suit exactly when `c` sits below
  S's rung — M's twin-suit stacked set is the ρ-image of S's. -/
  stacked_iff : ∀ c, c.suit = σ ∨ c.suit = σ.flipPair →
    (M.heights (ρ c).suit > (ρ c).rank.toIdx ↔ S.heights c.suit > c.rank.toIdx)

/-- **The twin correspondence**: the core plus the board conjugation —
M's board is the ρ-relabel of S's (pointwise on `topOf`). -/
structure State.TwinCorr (ρ : Card → Card) (σ : Suit) (S M : State)
    extends State.TwinCore ρ σ S M where
  /-- the board is the ρ-relabel, pointwise. -/
  board_eq : ∀ b, M.board.topOf b = (S.board.topOf (Base.relabel ρ b)).map ρ

namespace State.TwinCore

/-- The correspondence is symmetric in the two games (ρ is its own
inverse; the stacked-set invariant read at `ρ c` is its own dual). -/
theorem symm {ρ σ S M} (h : State.TwinCore ρ σ S M) : State.TwinCore ρ σ M S where
  isTwinMap := h.isTwinMap
  fixes_off := h.fixes_off
  deal_eq := h.deal_eq.symm
  depths_eq := h.depths_eq.symm
  stock_eq := h.stock_eq.symm
  step_eq := h.step_eq.symm
  heights_off := fun s h1 h2 => (h.heights_off s h1 h2).symm
  stacked_iff := fun c hon => by
    have honρ : (ρ c).suit = σ ∨ (ρ c).suit = σ.flipPair := h.isTwinMap.suit_mem hon
    have key := h.stacked_iff (ρ c) honρ
    rw [h.isTwinMap.invol c] at key
    exact key.symm

end State.TwinCore

namespace State.TwinCorr

/-- The full correspondence is symmetric (the board conjugation read
through the involution). -/
theorem symm {ρ σ S M} (h : State.TwinCorr ρ σ S M) : State.TwinCorr ρ σ M S where
  isTwinMap := h.isTwinMap
  fixes_off := h.fixes_off
  deal_eq := h.deal_eq.symm
  depths_eq := h.depths_eq.symm
  stock_eq := h.stock_eq.symm
  step_eq := h.step_eq.symm
  heights_off := fun s h1 h2 => (h.heights_off s h1 h2).symm
  stacked_iff := h.toTwinCore.symm.stacked_iff
  board_eq := fun b => by
    have hb := h.board_eq (Base.relabel ρ b)
    rw [Base.relabel_invol h.isTwinMap b] at hb
    cases hval : S.board.topOf b with
    | none => rw [hval] at hb; rw [hb]; rfl
    | some x =>
        have hinv : ρ (ρ x) = x := h.isTwinMap.invol x
        rw [hval] at hb
        rw [hb, Option.map_map]
        have hcomp : ρ ∘ ρ = id := funext (fun y => h.isTwinMap.invol y)
        rw [hcomp]
        rfl

/-- The board clause packaged as a board equality (the conjugate). -/
theorem board_mapByRho {ρ σ S M} (h : State.TwinCorr ρ σ S M) :
    M.board = Board.mapByRho h.isTwinMap S.board := by
  apply Board.ext_topOf
  funext b
  rw [Board.mapByRho_topOf]
  exact h.board_eq b

/-- The core underneath. -/
theorem core {ρ σ S M} (h : State.TwinCorr ρ σ S M) : State.TwinCore ρ σ S M :=
  h.toTwinCore

end State.TwinCorr

/-! ## §4. The move translation -/

/-- A move the correspondence translates WITHOUT GROWTH: the
height-blind kinds (any cards — draw/reveal/deckPile/pilePile never
read heights), or a foundation move of an off-suit card (its guard
reads its own suit's height, where the two games agree). -/
def Move.twinClean (σ : Suit) : Move → Bool
  | .draw | .reveal _ | .deckPile _ _ | .pilePile _ _ => true
  | .deckStack c | .pileStack c | .stackPile c _ =>
      decide (c.suit ≠ σ ∧ c.suit ≠ σ.flipPair)

/-- The ρ-translation of a move: every card argument and every
card-seat relabeled through ρ (the `Move.swapTwin` construction at a
general twin map). -/
def Move.relabelTwin (ρ : Card → Card) : Move → Move
  | .draw => .draw
  | .reveal c => .reveal (ρ c)
  | .deckPile c b => .deckPile (ρ c) (Base.relabel ρ b)
  | .deckStack c => .deckStack (ρ c)
  | .pileStack c => .pileStack (ρ c)
  | .stackPile c b => .stackPile (ρ c) (Base.relabel ρ b)
  | .pilePile c b => .pilePile (ρ c) (Base.relabel ρ b)

theorem Move.relabelTwin_swapTwin (t : Card) (m : Move) :
    Move.relabelTwin (Card.swapTwin t) m = Move.swapTwin t m := by
  cases m <;> rfl

theorem Move.relabelTwin_relabelTwin {ρ : Card → Card} (hρ : Card.IsTwinMap ρ) (m : Move) :
    Move.relabelTwin ρ (Move.relabelTwin ρ m) = m := by
  cases m with
  | draw => rfl
  | reveal c => show Move.reveal (ρ (ρ c)) = _; rw [hρ.invol c]
  | deckPile c b =>
      show Move.deckPile (ρ (ρ c)) (Base.relabel ρ (Base.relabel ρ b)) = _
      rw [hρ.invol c, Base.relabel_invol hρ b]
  | deckStack c => show Move.deckStack (ρ (ρ c)) = _; rw [hρ.invol c]
  | pileStack c => show Move.pileStack (ρ (ρ c)) = _; rw [hρ.invol c]
  | stackPile c b =>
      show Move.stackPile (ρ (ρ c)) (Base.relabel ρ (Base.relabel ρ b)) = _
      rw [hρ.invol c, Base.relabel_invol hρ b]
  | pilePile c b =>
      show Move.pilePile (ρ (ρ c)) (Base.relabel ρ (Base.relabel ρ b)) = _
      rw [hρ.invol c, Base.relabel_invol hρ b]

/-- The translation preserves the clean-move predicate (an off-suit
card fixed by ρ stays off-suit). -/
theorem Move.twinClean_relabelTwin {ρ : Card → Card} {σ : Suit}
    (hfix : ∀ c, c.suit ≠ σ → c.suit ≠ σ.flipPair → ρ c = c)
    {m : Move} (hc : Move.twinClean σ m = true) :
    Move.twinClean σ (Move.relabelTwin ρ m) = true := by
  cases m with
  | draw | reveal _ | deckPile _ _ | pilePile _ _ => rfl
  | deckStack c =>
      obtain ⟨h1, h2⟩ := by simpa [Move.twinClean] using hc
      show decide ((ρ c).suit ≠ σ ∧ (ρ c).suit ≠ σ.flipPair) = true
      rw [hfix c h1 h2]
      exact hc
  | pileStack c =>
      obtain ⟨h1, h2⟩ := by simpa [Move.twinClean] using hc
      show decide ((ρ c).suit ≠ σ ∧ (ρ c).suit ≠ σ.flipPair) = true
      rw [hfix c h1 h2]
      exact hc
  | stackPile c b =>
      obtain ⟨h1, h2⟩ := by simpa [Move.twinClean] using hc
      show decide ((ρ c).suit ≠ σ ∧ (ρ c).suit ≠ σ.flipPair) = true
      rw [hfix c h1 h2]
      exact hc

/-- Along a clean move, the twin suits' heights never move (the
window's twin rungs are frozen by the clean part of the play). -/
theorem Move.twinClean_heights {σ : Suit} {S R : State} {m : Move}
    (hc : Move.twinClean σ m = true) (hS : S.apply m = some R) :
    R.heights σ = S.heights σ ∧ R.heights σ.flipPair = S.heights σ.flipPair := by
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
  | pilePile c b =>
      rw [apply_pilePile_iff] at hS
      obtain ⟨-, -, -, -, -, -, rfl⟩ := hS
      exact ⟨rfl, rfl⟩
  | deckStack c =>
      obtain ⟨h1, h2⟩ := by simpa [Move.twinClean] using hc
      rw [apply_deckStack_iff] at hS
      obtain ⟨-, -, rfl⟩ := hS
      constructor
      · show (if σ = c.suit then S.heights σ + 1 else S.heights σ) = S.heights σ
        rw [if_neg (fun hcon => h1 hcon.symm)]
      · show (if σ.flipPair = c.suit then S.heights σ.flipPair + 1 else S.heights σ.flipPair)
          = S.heights σ.flipPair
        rw [if_neg (fun hcon => h2 hcon.symm)]
  | pileStack c =>
      obtain ⟨h1, h2⟩ := by simpa [Move.twinClean] using hc
      rw [apply_pileStack_iff] at hS
      obtain ⟨-, -, -, -, rfl⟩ := hS
      constructor
      · show (if σ = c.suit then S.heights σ + 1 else S.heights σ) = S.heights σ
        rw [if_neg (fun hcon => h1 hcon.symm)]
      · show (if σ.flipPair = c.suit then S.heights σ.flipPair + 1 else S.heights σ.flipPair)
          = S.heights σ.flipPair
        rw [if_neg (fun hcon => h2 hcon.symm)]
  | stackPile c b =>
      obtain ⟨h1, h2⟩ := by simpa [Move.twinClean] using hc
      rw [apply_stackPile_iff] at hS
      obtain ⟨-, -, -, -, rfl⟩ := hS
      constructor
      · show (if σ = c.suit then S.heights σ - 1 else S.heights σ) = S.heights σ
        rw [if_neg (fun hcon => h1 hcon.symm)]
      · show (if σ.flipPair = c.suit then S.heights σ.flipPair - 1 else S.heights σ.flipPair)
          = S.heights σ.flipPair
        rw [if_neg (fun hcon => h2 hcon.symm)]

/-! ### The shrink lemmas (the `hhid`/`hstock` premises' maintenance) -/

/-- No move ever increases a pile's hidden slice (only `reveal`
shrinks one). -/
theorem State.depths_le_apply {S R : State} {m : Move} (hS : S.apply m = some R) :
    ∀ a, R.depths a ≤ S.depths a := by
  cases m with
  | draw =>
      rw [apply_draw_iff] at hS
      obtain rfl := hS
      intro a; exact Nat.le_refl _
  | reveal c =>
      rw [apply_reveal_iff] at hS
      obtain ⟨-, r, a, bd, -, -, -, rfl⟩ := hS
      intro a'
      by_cases haa : a' = a
      · rw [haa]
        show (if a = a then S.depths a - 1 else S.depths a) ≤ _
        rw [if_pos rfl]
        exact Nat.sub_le _ _
      · show (if a' = a then S.depths a - 1 else S.depths a') ≤ S.depths a'
        rw [if_neg haa]
        exact Nat.le_refl _
  | deckPile c b =>
      rw [apply_deckPile_iff] at hS
      obtain ⟨-, -, -, -, rfl⟩ := hS
      intro a; exact Nat.le_refl _
  | deckStack c =>
      rw [apply_deckStack_iff] at hS
      obtain ⟨-, -, rfl⟩ := hS
      intro a; exact Nat.le_refl _
  | pileStack c =>
      rw [apply_pileStack_iff] at hS
      obtain ⟨-, -, -, -, rfl⟩ := hS
      intro a; exact Nat.le_refl _
  | stackPile c b =>
      rw [apply_stackPile_iff] at hS
      obtain ⟨-, -, -, -, rfl⟩ := hS
      intro a; exact Nat.le_refl _
  | pilePile c b =>
      rw [apply_pilePile_iff] at hS
      obtain ⟨-, -, -, -, -, -, rfl⟩ := hS
      intro a; exact Nat.le_refl _

/-- The hidden slices shrink along any move (the ρ-freeness premise
on them is maintained). -/
theorem State.hidden_sub_apply {S R : State} {m : Move} (hS : S.apply m = some R) :
    ∀ a, ∀ c ∈ R.hidden a, c ∈ S.hidden a := by
  have hdeal : R.deal = S.deal := by
    cases m with
    | draw => rw [apply_draw_iff] at hS; obtain rfl := hS; rfl
    | reveal c =>
        rw [apply_reveal_iff] at hS
        obtain ⟨-, -, -, -, -, -, -, rfl⟩ := hS; rfl
    | deckPile c b =>
        rw [apply_deckPile_iff] at hS
        obtain ⟨-, -, -, -, rfl⟩ := hS; rfl
    | deckStack c =>
        rw [apply_deckStack_iff] at hS
        obtain ⟨-, -, rfl⟩ := hS; rfl
    | pileStack c =>
        rw [apply_pileStack_iff] at hS
        obtain ⟨-, -, -, -, rfl⟩ := hS; rfl
    | stackPile c b =>
        rw [apply_stackPile_iff] at hS
        obtain ⟨-, -, -, -, rfl⟩ := hS; rfl
    | pilePile c b =>
        rw [apply_pilePile_iff] at hS
        obtain ⟨-, -, -, -, -, -, rfl⟩ := hS; rfl
  intro a c hc
  show c ∈ (S.deal.piles a).take (S.depths a)
  have hc' : c ∈ (S.deal.piles a).take (R.depths a) := by
    rw [← hdeal]
    exact hc
  exact take_mono (State.depths_le_apply hS a) hc'

/-- The stock only loses cards along any move (the ρ-freeness
premise on it is maintained). -/
theorem State.stock_cards_sub_apply {S R : State} {m : Move} (hS : S.apply m = some R) :
    ∀ c ∈ R.stock.cards, c ∈ S.stock.cards := by
  cases m with
  | draw =>
      rw [apply_draw_iff] at hS
      obtain rfl := hS
      intro c hc
      rw [Cycle.dealOnce_cards] at hc
      exact hc
  | reveal c =>
      rw [apply_reveal_iff] at hS
      obtain ⟨-, -, -, -, -, -, -, rfl⟩ := hS
      intro c hc; exact hc
  | deckPile c b =>
      rw [apply_deckPile_iff] at hS
      obtain ⟨-, -, -, -, rfl⟩ := hS
      intro c hc
      exact Cycle.mem_removeIdx S.stock.cards _ hc
  | deckStack c =>
      rw [apply_deckStack_iff] at hS
      obtain ⟨-, -, rfl⟩ := hS
      intro c hc
      exact Cycle.mem_removeIdx S.stock.cards _ hc
  | pileStack c =>
      rw [apply_pileStack_iff] at hS
      obtain ⟨-, -, -, -, rfl⟩ := hS
      intro c hc; exact hc
  | stackPile c b =>
      rw [apply_stackPile_iff] at hS
      obtain ⟨-, -, -, -, rfl⟩ := hS
      intro c hc; exact hc
  | pilePile c b =>
      rw [apply_pilePile_iff] at hS
      obtain ⟨-, -, -, -, -, -, rfl⟩ := hS
      intro c hc; exact hc

/-! ## §5. The clean step

`apply_swapTwinBoard_clean` generalized from the single twin
transposition `τ_z` to an arbitrary twin map ρ.  The height-blind
kinds translate with their cards and seats relabeled — the reveal case
rides the hidden slices' ρ-freeness (the boundary lookups only ever
produce hidden-slice cards, and a card fixed by ρ relabels the deal
read to itself), the deckPile case the stock's (the moved card is a
stock card, fixed); the off-suit foundation moves translate with their
guards agreeing on the off-suit heights.  The correspondence is
preserved verbatim (no growth: clean moves never touch the twin-suit
rungs). -/

/-- **The clean step**: a clean move's ρ-translation fires in the
mirror and preserves the correspondence. -/
theorem State.TwinCorr.apply_clean {ρ σ S M R m}
    (h : State.TwinCorr ρ σ S M)
    (hhid : ∀ a, ∀ c ∈ S.hidden a, ρ c = c)
    (hstock : ∀ c ∈ S.stock.cards, ρ c = c)
    (hclean : Move.twinClean σ m = true)
    (hS : S.apply m = some R) :
    ∃ N, M.apply (Move.relabelTwin ρ m) = some N ∧ State.TwinCorr ρ σ R N := by
  cases m with
  | draw =>
      rw [apply_draw_iff] at hS
      obtain rfl := hS
      refine ⟨{M with stock := M.stock.dealOnce M.drawStep},
        apply_draw_iff.mpr rfl, ?_⟩
      refine ⟨⟨h.isTwinMap, h.fixes_off, h.deal_eq, h.depths_eq, ?_, h.step_eq,
        h.heights_off, h.stacked_iff⟩, h.board_eq⟩
      show M.stock.dealOnce M.drawStep = S.stock.dealOnce S.drawStep
      rw [h.stock_eq, h.step_eq]
  | reveal c =>
      rw [apply_reveal_iff] at hS
      obtain ⟨htop, r, a, bd, hbot, hp, hatt, rfl⟩ := hS
      have hrhid : r ∈ S.hidden a := State.mem_hidden_of_pileOfTopHidden hp
      have hrr : ρ r = r := hhid a r hrhid
      have hhbM : M.hiddenBase a = S.hiddenBase a :=
        Frame.hiddenBase_congr h.deal_eq h.depths_eq a
      have htopM : M.board.topOf (Sum.inr (ρ c)) = none := by
        have hseat : Base.relabel ρ (Sum.inr (ρ c)) = Sum.inr c := by
          show Sum.inr (ρ (ρ c)) = _
          rw [h.isTwinMap.invol c]
        rw [h.board_eq, hseat, htop]
        rfl
      have hbotM : M.board.bottomOf (ρ c) = some (Sum.inr r) := by
        rw [h.board_mapByRho, Board.mapByRho_bottomOf, hbot, Option.map_some]
        show some (Sum.inr (ρ r)) = _
        rw [hrr]
      have hpM : M.pileOfTopHidden r = some a :=
        (Frame.pileOfTopHidden_congr h.deal_eq h.depths_eq r).trans hp
      have hHBfix : Base.relabel ρ (S.hiddenBase a) = S.hiddenBase a := by
        cases hHB : S.hiddenBase a with
        | inl a' => rfl
        | inr d =>
            have hdr : ρ d = d := hhid a d (State.mem_hidden_of_hiddenBase hHB)
            show Sum.inr (ρ d) = Sum.inr d
            rw [hdr]
      have hattM : M.board.attach (S.hiddenBase a) r
          = some (Board.mapByRho h.isTwinMap bd) := by
        rw [h.board_mapByRho, ← hHBfix, ← hrr]
        exact Board.mapByRho_attach h.isTwinMap hatt
      refine ⟨{M with
          board := Board.mapByRho h.isTwinMap bd,
          depths := fun a' => if a' = a then M.depths a - 1 else M.depths a'},
        apply_reveal_iff.mpr ⟨htopM, r, a, Board.mapByRho h.isTwinMap bd, hbotM, hpM,
          by rw [hhbM]; exact hattM, rfl⟩, ?_⟩
      refine ⟨⟨h.isTwinMap, h.fixes_off, h.deal_eq, ?_, h.stock_eq, h.step_eq,
        h.heights_off, h.stacked_iff⟩, ?_⟩
      · funext a'
        by_cases ha' : a' = a
        · rw [ha']
          show (if a = a then M.depths a - 1 else M.depths a)
            = (if a = a then S.depths a - 1 else S.depths a)
          rw [if_pos rfl, if_pos rfl]
          show M.depths a - 1 = S.depths a - 1
          rw [congrFun h.depths_eq a]
        · show (if a' = a then M.depths a - 1 else M.depths a')
            = (if a' = a then S.depths a - 1 else S.depths a')
          rw [if_neg ha', if_neg ha']
          show M.depths a' = S.depths a'
          rw [congrFun h.depths_eq a']
      · intro b'
        show (Board.mapByRho h.isTwinMap bd).topOf b' = (bd.topOf (Base.relabel ρ b')).map ρ
        exact Board.mapByRho_topOf h.isTwinMap bd b'
  | deckPile c b =>
      rw [apply_deckPile_iff] at hS
      obtain ⟨hprev, hcp, bd, hatt, rfl⟩ := hS
      have hmem : c ∈ S.stock.cards := by
        simp only [Cycle.prev] at hprev
        split at hprev
        · exact absurd hprev (by simp)
        · exact List.mem_iff_getElem?.mpr ⟨S.stock.cursor - 1, hprev⟩
      have hrc : ρ c = c := hstock c hmem
      have hprevM : M.stock.prev = some c := by rw [h.stock_eq]; exact hprev
      have hcpM : M.canPlace c (Base.relabel ρ b) = true := by
        have hcpR := State.canPlace_relabel h.isTwinMap h.board_mapByRho c b
        rw [hrc] at hcpR
        exact hcpR.trans hcp
      have hattM : M.board.attach (Base.relabel ρ b) c
          = some (Board.mapByRho h.isTwinMap bd) := by
        rw [h.board_mapByRho, ← hrc]
        exact Board.mapByRho_attach h.isTwinMap hatt
      refine ⟨{M with
          board := Board.mapByRho h.isTwinMap bd,
          stock := M.stock.removeAt (M.stock.cursor - 1)},
        ?_, ?_⟩
      · show M.apply (Move.deckPile (ρ c) (Base.relabel ρ b)) = some _
        rw [hrc]
        exact apply_deckPile_iff.mpr ⟨hprevM, hcpM, Board.mapByRho h.isTwinMap bd, hattM, rfl⟩
      · refine ⟨⟨h.isTwinMap, h.fixes_off, h.deal_eq, h.depths_eq, ?_, h.step_eq,
          h.heights_off, h.stacked_iff⟩, ?_⟩
        · show M.stock.removeAt (M.stock.cursor - 1) = S.stock.removeAt (S.stock.cursor - 1)
          rw [h.stock_eq]
        · intro b'
          show (Board.mapByRho h.isTwinMap bd).topOf b' = (bd.topOf (Base.relabel ρ b')).map ρ
          exact Board.mapByRho_topOf h.isTwinMap bd b'
  | deckStack c =>
      obtain ⟨h1, h2⟩ := by simpa [Move.twinClean] using hclean
      have hrc : ρ c = c := h.fixes_off c h1 h2
      rw [apply_deckStack_iff] at hS
      obtain ⟨hprev, hrk, rfl⟩ := hS
      have hprevM : M.stock.prev = some c := by rw [h.stock_eq]; exact hprev
      have hrkM : c.rank.toIdx = M.heights c.suit := by
        rw [h.heights_off c.suit h1 h2]
        exact hrk
      refine ⟨{M with
          stock := M.stock.removeAt (M.stock.cursor - 1),
          heights := fun s => if s = c.suit then M.heights s + 1 else M.heights s},
        ?_, ?_⟩
      · show M.apply (Move.deckStack (ρ c)) = some _
        rw [hrc]
        exact apply_deckStack_iff.mpr ⟨hprevM, hrkM, rfl⟩
      · refine ⟨⟨h.isTwinMap, h.fixes_off, h.deal_eq, h.depths_eq, ?_, h.step_eq,
          ?_, ?_⟩, h.board_eq⟩
        · show M.stock.removeAt (M.stock.cursor - 1) = S.stock.removeAt (S.stock.cursor - 1)
          rw [h.stock_eq]
        · intro s hs1 hs2
          show (if s = c.suit then M.heights s + 1 else M.heights s)
            = (if s = c.suit then S.heights s + 1 else S.heights s)
          by_cases hsc : s = c.suit
          · simp only [if_pos hsc]
            rw [h.heights_off s hs1 hs2]
          · simp only [if_neg hsc]
            exact h.heights_off s hs1 hs2
        · intro c' hon
          have honρ : (ρ c').suit = σ ∨ (ρ c').suit = σ.flipPair :=
            h.isTwinMap.suit_mem hon
          have hne : (ρ c').suit ≠ c.suit := by
            rcases honρ with hs | hs
            · intro hcon; rw [hcon] at hs; exact h1 hs
            · intro hcon; rw [hcon] at hs; exact h2 hs
          have hne' : c'.suit ≠ c.suit := by
            rcases hon with hs | hs
            · intro hcon; rw [hcon] at hs; exact h1 hs
            · intro hcon; rw [hcon] at hs; exact h2 hs
          show (if (ρ c').suit = c.suit then M.heights (ρ c').suit + 1
              else M.heights (ρ c').suit) > (ρ c').rank.toIdx
            ↔ (if c'.suit = c.suit then S.heights c'.suit + 1 else S.heights c'.suit)
              > c'.rank.toIdx
          rw [if_neg hne, if_neg hne']
          exact h.stacked_iff c' hon
  | pileStack c =>
      obtain ⟨h1, h2⟩ := by simpa [Move.twinClean] using hclean
      have hrc : ρ c = c := h.fixes_off c h1 h2
      rw [apply_pileStack_iff] at hS
      obtain ⟨htop, b, hbot, hrk, rfl⟩ := hS
      have htopM : M.board.topOf (Sum.inr c) = none := by
        rw [h.board_eq]
        show (S.board.topOf (Sum.inr (ρ c))).map ρ = none
        rw [hrc, htop]
        rfl
      have hbotM : M.board.bottomOf c = some (Base.relabel ρ b) := by
        have hmb := Board.mapByRho_bottomOf h.isTwinMap S.board c
        rw [← h.board_mapByRho, hrc, hbot, Option.map_some] at hmb
        exact hmb
      have hrkM : c.rank.toIdx = M.heights c.suit := by
        rw [h.heights_off c.suit h1 h2]
        exact hrk
      refine ⟨{M with
          board := M.board.detach (Base.relabel ρ b),
          heights := fun s => if s = c.suit then M.heights s + 1 else M.heights s},
        ?_, ?_⟩
      · show M.apply (Move.pileStack (ρ c)) = some _
        rw [hrc]
        exact apply_pileStack_iff.mpr ⟨htopM, Base.relabel ρ b, hbotM, hrkM, rfl⟩
      · refine ⟨⟨h.isTwinMap, h.fixes_off, h.deal_eq, h.depths_eq, h.stock_eq, h.step_eq,
          ?_, ?_⟩, ?_⟩
        · intro s hs1 hs2
          show (if s = c.suit then M.heights s + 1 else M.heights s)
            = (if s = c.suit then S.heights s + 1 else S.heights s)
          by_cases hsc : s = c.suit
          · simp only [if_pos hsc]
            rw [h.heights_off s hs1 hs2]
          · simp only [if_neg hsc]
            exact h.heights_off s hs1 hs2
        · intro c' hon
          have honρ : (ρ c').suit = σ ∨ (ρ c').suit = σ.flipPair :=
            h.isTwinMap.suit_mem hon
          have hne : (ρ c').suit ≠ c.suit := by
            rcases honρ with hs | hs
            · intro hcon; rw [hcon] at hs; exact h1 hs
            · intro hcon; rw [hcon] at hs; exact h2 hs
          have hne' : c'.suit ≠ c.suit := by
            rcases hon with hs | hs
            · intro hcon; rw [hcon] at hs; exact h1 hs
            · intro hcon; rw [hcon] at hs; exact h2 hs
          show (if (ρ c').suit = c.suit then M.heights (ρ c').suit + 1
              else M.heights (ρ c').suit) > (ρ c').rank.toIdx
            ↔ (if c'.suit = c.suit then S.heights c'.suit + 1 else S.heights c'.suit)
              > c'.rank.toIdx
          rw [if_neg hne, if_neg hne']
          exact h.stacked_iff c' hon
        · intro b'
          show (M.board.detach (Base.relabel ρ b)).topOf b'
            = ((S.board.detach b).topOf (Base.relabel ρ b')).map ρ
          rw [h.board_mapByRho, Board.mapByRho_detach]
          exact Board.mapByRho_topOf h.isTwinMap (S.board.detach b) b'
  | stackPile c b =>
      obtain ⟨h1, h2⟩ := by simpa [Move.twinClean] using hclean
      have hrc : ρ c = c := h.fixes_off c h1 h2
      rw [apply_stackPile_iff] at hS
      obtain ⟨hrk, hcp, bd, hatt, rfl⟩ := hS
      have hrkM : c.rank.toIdx + 1 = M.heights c.suit := by
        rw [h.heights_off c.suit h1 h2]
        exact hrk
      have hcpM : M.canPlace c (Base.relabel ρ b) = true := by
        have hcpR := State.canPlace_relabel h.isTwinMap h.board_mapByRho c b
        rw [hrc] at hcpR
        exact hcpR.trans hcp
      have hattM : M.board.attach (Base.relabel ρ b) c
          = some (Board.mapByRho h.isTwinMap bd) := by
        rw [h.board_mapByRho, ← hrc]
        exact Board.mapByRho_attach h.isTwinMap hatt
      refine ⟨{M with
          board := Board.mapByRho h.isTwinMap bd,
          heights := fun s => if s = c.suit then M.heights s - 1 else M.heights s},
        ?_, ?_⟩
      · show M.apply (Move.stackPile (ρ c) (Base.relabel ρ b)) = some _
        rw [hrc]
        exact apply_stackPile_iff.mpr ⟨hrkM, hcpM, Board.mapByRho h.isTwinMap bd, hattM, rfl⟩
      · refine ⟨⟨h.isTwinMap, h.fixes_off, h.deal_eq, h.depths_eq, h.stock_eq, h.step_eq,
          ?_, ?_⟩, ?_⟩
        · intro s hs1 hs2
          show (if s = c.suit then M.heights s - 1 else M.heights s)
            = (if s = c.suit then S.heights s - 1 else S.heights s)
          by_cases hsc : s = c.suit
          · simp only [if_pos hsc]
            rw [h.heights_off s hs1 hs2]
          · simp only [if_neg hsc]
            exact h.heights_off s hs1 hs2
        · intro c' hon
          have honρ : (ρ c').suit = σ ∨ (ρ c').suit = σ.flipPair :=
            h.isTwinMap.suit_mem hon
          have hne : (ρ c').suit ≠ c.suit := by
            rcases honρ with hs | hs
            · intro hcon; rw [hcon] at hs; exact h1 hs
            · intro hcon; rw [hcon] at hs; exact h2 hs
          have hne' : c'.suit ≠ c.suit := by
            rcases hon with hs | hs
            · intro hcon; rw [hcon] at hs; exact h1 hs
            · intro hcon; rw [hcon] at hs; exact h2 hs
          show (if (ρ c').suit = c.suit then M.heights (ρ c').suit - 1
              else M.heights (ρ c').suit) > (ρ c').rank.toIdx
            ↔ (if c'.suit = c.suit then S.heights c'.suit - 1 else S.heights c'.suit)
              > c'.rank.toIdx
          rw [if_neg hne, if_neg hne']
          exact h.stacked_iff c' hon
        · intro b'
          show (Board.mapByRho h.isTwinMap bd).topOf b' = (bd.topOf (Base.relabel ρ b')).map ρ
          exact Board.mapByRho_topOf h.isTwinMap bd b'
  | pilePile c b =>
      rw [apply_pilePile_iff] at hS
      obtain ⟨b₀, hbot, hne, hcmr, bd, hatt, rfl⟩ := hS
      have hbotM : M.board.bottomOf (ρ c) = some (Base.relabel ρ b₀) := by
        rw [h.board_mapByRho, Board.mapByRho_bottomOf, hbot, Option.map_some]
      have hneM : Base.relabel ρ b₀ ≠ Base.relabel ρ b := by
        intro hcon
        exact hne (Base.relabel_inj h.isTwinMap hcon)
      have hcmrM : M.canMoveRun (ρ c) (Base.relabel ρ b) = true := by
        rw [State.canMoveRun_relabel h.isTwinMap h.board_mapByRho c b]
        exact hcmr
      have hattM : (M.board.detach (Base.relabel ρ b₀)).attach (Base.relabel ρ b) (ρ c)
          = some (Board.mapByRho h.isTwinMap bd) := by
        rw [h.board_mapByRho, Board.mapByRho_detach]
        exact Board.mapByRho_attach h.isTwinMap hatt
      refine ⟨{M with board := Board.mapByRho h.isTwinMap bd},
        ?_, ?_⟩
      · show M.apply (Move.pilePile (ρ c) (Base.relabel ρ b)) = some _
        exact apply_pilePile_iff.mpr ⟨Base.relabel ρ b₀, hbotM, hneM, hcmrM,
          Board.mapByRho h.isTwinMap bd, hattM, rfl⟩
      · refine ⟨⟨h.isTwinMap, h.fixes_off, h.deal_eq, h.depths_eq, h.stock_eq, h.step_eq,
          h.heights_off, h.stacked_iff⟩, ?_⟩
        intro b'
        show (Board.mapByRho h.isTwinMap bd).topOf b' = (bd.topOf (Base.relabel ρ b')).map ρ
        exact Board.mapByRho_topOf h.isTwinMap bd b'

/-! ### The rung arithmetic of an on-suit foundation move

Two auxiliary computations, stated over plain height functions so
both the verbatim stacking and the growth reuse them: the BUMP (the
two games each stack one card — the source `q`, the mirror `w = ρn q`
under the NEW correspondence ρn, the two rungs equal) and the DROP
(the worry-back — both games return one card, the rungs equal).  The
excluded middle card is the moved pair itself (`x = q` / `x = flip q`
or `x = c` / `x = flip c`), handled inline by the callers. -/

/-- Same suit and rank is the same card. -/
theorem Card.eq_of_suit_rank {x q : Card} (hs : x.suit = q.suit)
    (hr : x.rank = q.rank) : x = q := by
  cases x with
  | mk xs xr =>
      cases q with
      | mk qs qr =>
          rw [Card.mk.injEq]
          exact ⟨hs, hr⟩

/-- Two on-suit cards of the same rank are the pair (each rank has
exactly one card per twin suit). -/
theorem Card.eq_or_flip_of_onSuit_rank {σ : Suit} {x q : Card}
    (hx : x.suit = σ ∨ x.suit = σ.flipPair)
    (hq : q.suit = σ ∨ q.suit = σ.flipPair)
    (hcon : x.rank.toIdx = q.rank.toIdx) :
    x = q ∨ x = Card.flipSuit q :=
  Card.eq_or_flip_of_onSuit hx hq (Rank.toIdx_inj hcon)

/-- **The bump**: after the source bumps `q`'s suit and the mirror
bumps `w`'s suit (`w = ρn q`, the rungs equal), the stacked-set
invariant carries from ρ to ρn. -/
theorem State.stacked_bump_aux {σ : Suit} {hS hM hS' hM' : Suit → Nat}
    {ρ ρn : Card → Card} {q w : Card}
    (hρ : Card.IsTwinMap ρ) (_hρn : Card.IsTwinMap ρn)
    (honq : q.suit = σ ∨ q.suit = σ.flipPair)
    (_hqw : ρn q = w)
    (hagree : ∀ x, x ≠ q → x ≠ Card.flipSuit q → ρn x = ρ x)
    (hold : ∀ x, x.suit = σ ∨ x.suit = σ.flipPair →
      (hM (ρ x).suit > (ρ x).rank.toIdx ↔ hS x.suit > x.rank.toIdx))
    (hq : hS q.suit = q.rank.toIdx)
    (hw : hM w.suit = q.rank.toIdx)
    (hSb : ∀ s, hS' s = if s = q.suit then hS s + 1 else hS s)
    (hMb : ∀ s, hM' s = if s = w.suit then hM s + 1 else hM s) :
    ∀ x, x ≠ q → x ≠ Card.flipSuit q → (x.suit = σ ∨ x.suit = σ.flipPair) →
      (hM' (ρn x).suit > (ρn x).rank.toIdx ↔ hS' x.suit > x.rank.toIdx) := by
  intro x hxq hxq' hon
  have hrx : ρn x = ρ x := hagree x hxq hxq'
  have hrank : (ρ x).rank.toIdx = x.rank.toIdx := by
    rw [Card.IsTwinMap.rank hρ x]
  have holdx := hold x hon
  rw [hrank] at holdx
  rw [hrx, hrank, hMb (ρ x).suit, hSb x.suit]
  by_cases h1 : x.suit = q.suit
  · by_cases h2 : (ρ x).suit = w.suit
    · rw [if_pos h2, if_pos h1, h2, h1, hw, hq]
    · rw [if_neg h2, if_pos h1, h1, hq]
      have hkx : x.rank.toIdx ≠ q.rank.toIdx := by
        intro hcon
        exact hxq (Card.eq_of_suit_rank h1 (Rank.toIdx_inj hcon))
      constructor
      · intro hlt
        have h1' := holdx.mp hlt
        rw [h1, hq] at h1'
        omega
      · intro hlt
        have h1' : hS x.suit > x.rank.toIdx := by
          rw [h1, hq]
          omega
        exact holdx.mpr h1'
  · by_cases h2 : (ρ x).suit = w.suit
    · rw [if_pos h2, if_neg h1, h2, hw]
      have hkx : x.rank.toIdx ≠ q.rank.toIdx := by
        intro hcon
        rcases Card.eq_or_flip_of_onSuit_rank hon honq hcon with hc | hc
        · exact hxq hc
        · exact hxq' hc
      constructor
      · intro hlt
        have hMside : hM (ρ x).suit > x.rank.toIdx := by rw [h2, hw]; omega
        exact holdx.mp hMside
      · intro hlt
        have hMside := holdx.mpr hlt
        rw [h2, hw] at hMside
        omega
    · rw [if_neg h2, if_neg h1]
      exact holdx

/-- **The drop**: after the source's worry-back of `c` and the
mirror's of `ρ c` (the rungs equal), the stacked-set invariant is
preserved. -/
theorem State.stacked_drop_aux {σ : Suit} {hS hM hS' hM' : Suit → Nat}
    {ρ : Card → Card} {c : Card}
    (hρ : Card.IsTwinMap ρ)
    (hon : c.suit = σ ∨ c.suit = σ.flipPair)
    (hold : ∀ x, x.suit = σ ∨ x.suit = σ.flipPair →
      (hM (ρ x).suit > (ρ x).rank.toIdx ↔ hS x.suit > x.rank.toIdx))
    (hSg : hS c.suit = c.rank.toIdx + 1)
    (hMg : hM (ρ c).suit = c.rank.toIdx + 1)
    (hSd : ∀ s, hS' s = if s = c.suit then hS s - 1 else hS s)
    (hMd : ∀ s, hM' s = if s = (ρ c).suit then hM s - 1 else hM s) :
    ∀ x, x ≠ c → x ≠ Card.flipSuit c → (x.suit = σ ∨ x.suit = σ.flipPair) →
      (hM' (ρ x).suit > (ρ x).rank.toIdx ↔ hS' x.suit > x.rank.toIdx) := by
  intro x hxc hxfc hon'
  have holdx := hold x hon'
  have hrk : (ρ x).rank.toIdx = x.rank.toIdx := by
    rw [Card.IsTwinMap.rank hρ x]
  rw [hrk] at holdx
  rw [hMd (ρ x).suit, hSd x.suit, hrk]
  by_cases h1 : x.suit = c.suit
  · by_cases h2 : (ρ x).suit = (ρ c).suit
    · rw [if_pos h2, if_pos h1, h2, h1, hMg, hSg]
    · rw [if_neg h2, if_pos h1, h1, hSg]
      have hkx : x.rank.toIdx ≠ c.rank.toIdx := by
        intro hcon
        exact hxc (Card.eq_of_suit_rank h1 (Rank.toIdx_inj hcon))
      constructor
      · intro hlt
        have h1' := holdx.mp hlt
        rw [h1, hSg] at h1'
        omega
      · intro hlt
        have h1' : hS x.suit > x.rank.toIdx := by
          rw [h1, hSg]
          omega
        exact holdx.mpr h1'
  · by_cases h2 : (ρ x).suit = (ρ c).suit
    · rw [if_pos h2, if_neg h1, h2, hMg]
      have hkx : x.rank.toIdx ≠ c.rank.toIdx := by
        intro hcon
        rcases Card.eq_or_flip_of_onSuit_rank hon' hon hcon with hc | hc
        · exact hxc hc
        · exact hxfc hc
      constructor
      · intro hlt
        have hMside : hM (ρ x).suit > x.rank.toIdx := by rw [h2, hMg]; omega
        exact holdx.mp hMside
      · intro hlt
        have hMside := holdx.mpr hlt
        rw [h2, hMg] at hMside
        omega
    · rw [if_neg h2, if_neg h1]
      exact holdx

/-! ### The on-suit foundation steps -/

/-- The twin-suit trichotomy: any on-suit suit is the card's or its
twin's. -/
theorem Suit.two_cases {σ : Suit} {c : Card} {s : Suit}
    (hon : c.suit = σ ∨ c.suit = σ.flipPair)
    (hx : s = σ ∨ s = σ.flipPair) :
    s = c.suit ∨ s = (Card.flipSuit c).suit := by
  rcases hon with hs | hs
  · rcases hx with hs' | hs'
    · exact Or.inl (hs'.trans hs.symm)
    · exact Or.inr (by rw [Card.flipSuit_suit, hs]; exact hs')
  · rcases hx with hs' | hs'
    · exact Or.inr (by rw [Card.flipSuit_suit, hs, Suit.flipPair_flipPair]; exact hs')
    · exact Or.inl (hs'.trans hs.symm)

/-- **The on-suit stacking, verbatim**: when the mirror's rung of
`ρ q`'s suit is exactly `q`'s rank (the rung ALIGNED), the mirror
stacks `ρ q` itself and the full correspondence is preserved — no
growth. -/
theorem State.TwinCorr.apply_pileStack_onsuit {ρ σ S M R q}
    (h : State.TwinCorr ρ σ S M)
    (hon : q.suit = σ ∨ q.suit = σ.flipPair)
    (hS : S.apply (Move.pileStack q) = some R)
    (halign : M.heights (ρ q).suit = q.rank.toIdx) :
    ∃ N, M.apply (Move.pileStack (ρ q)) = some N ∧ State.TwinCorr ρ σ R N := by
  rw [apply_pileStack_iff] at hS
  obtain ⟨htop, b, hbot, hrk, rfl⟩ := hS
  have htopM : M.board.topOf (Sum.inr (ρ q)) = none := by
    have hseat : Base.relabel ρ (Sum.inr (ρ q)) = Sum.inr q := by
      show Sum.inr (ρ (ρ q)) = _
      rw [h.isTwinMap.invol q]
    rw [h.board_eq, hseat, htop]
    rfl
  have hbotM : M.board.bottomOf (ρ q) = some (Base.relabel ρ b) := by
    rw [h.board_mapByRho, Board.mapByRho_bottomOf, hbot, Option.map_some]
  have hrkM : (ρ q).rank.toIdx = M.heights (ρ q).suit := by
    rw [Card.IsTwinMap.rank h.isTwinMap q, halign]
  refine ⟨{M with
      board := M.board.detach (Base.relabel ρ b),
      heights := fun s => if s = (ρ q).suit then M.heights s + 1 else M.heights s},
    apply_pileStack_iff.mpr ⟨htopM, Base.relabel ρ b, hbotM, hrkM, rfl⟩, ?_⟩
  refine ⟨⟨h.isTwinMap, h.fixes_off, h.deal_eq, h.depths_eq, h.stock_eq, h.step_eq,
    ?_, ?_⟩, ?_⟩
  · intro s hs1 hs2
    have honρ : (ρ q).suit = σ ∨ (ρ q).suit = σ.flipPair := h.isTwinMap.suit_mem hon
    have hne1 : s ≠ (ρ q).suit := by
      rcases honρ with hs | hs
      · intro hcon; exact hs1 (hcon.trans hs)
      · intro hcon; exact hs2 (hcon.trans hs)
    have hne2 : s ≠ q.suit := by
      rcases hon with hs | hs
      · intro hcon; exact hs1 (hcon.trans hs)
      · intro hcon; exact hs2 (hcon.trans hs)
    show (if s = (ρ q).suit then M.heights s + 1 else M.heights s)
      = (if s = q.suit then S.heights s + 1 else S.heights s)
    rw [if_neg hne1, if_neg hne2]
    exact h.heights_off s hs1 hs2
  · intro c' hon'
    by_cases hcq : c' = q
    · rw [hcq]
      constructor
      · intro _
        show (if q.suit = q.suit then S.heights q.suit + 1 else S.heights q.suit)
          > q.rank.toIdx
        rw [if_pos rfl, ← hrk]
        omega
      · intro _
        show (if (ρ q).suit = (ρ q).suit then M.heights (ρ q).suit + 1
            else M.heights (ρ q).suit) > (ρ q).rank.toIdx
        rw [if_pos rfl, Card.IsTwinMap.rank h.isTwinMap q, halign]
        omega
    · by_cases hcq' : c' = Card.flipSuit q
      · rw [hcq']
        have hfs : q.flipSuit.suit ≠ q.suit := by
          show q.suit.flipPair ≠ q.suit
          exact Suit.flipPair_ne q.suit
        have hfsρ : (ρ q.flipSuit).suit ≠ (ρ q).suit := by
          rw [h.isTwinMap.flip_comm q, Card.flipSuit_suit]
          exact Suit.flipPair_ne (ρ q).suit
        have honf : q.flipSuit.suit = σ ∨ q.flipSuit.suit = σ.flipPair := by
          show q.suit.flipPair = σ ∨ q.suit.flipPair = σ.flipPair
          rcases hon with hs | hs
          · rw [hs]; exact Or.inr rfl
          · rw [hs]; exact Or.inl (Suit.flipPair_flipPair σ)
        show (if (ρ q.flipSuit).suit = (ρ q).suit then M.heights (ρ q.flipSuit).suit + 1
            else M.heights (ρ q.flipSuit).suit) > (ρ q.flipSuit).rank.toIdx
          ↔ (if q.flipSuit.suit = q.suit then S.heights q.flipSuit.suit + 1
            else S.heights q.flipSuit.suit) > q.flipSuit.rank.toIdx
        rw [if_neg hfsρ, if_neg hfs, Card.flipSuit_rank q]
        exact h.stacked_iff q.flipSuit honf
      · exact State.stacked_bump_aux
          (hS := S.heights) (hM := M.heights)
          (hS' := fun s => if s = q.suit then S.heights s + 1 else S.heights s)
          (hM' := fun s => if s = (ρ q).suit then M.heights s + 1 else M.heights s)
          (ρ := ρ) (ρn := ρ) (q := q) (w := ρ q)
          h.isTwinMap h.isTwinMap hon rfl (fun _ _ _ => rfl) h.stacked_iff
          hrk.symm halign (fun _ => rfl) (fun _ => rfl) c' hcq hcq' hon'
  · intro b'
    show (M.board.detach (Base.relabel ρ b)).topOf b'
      = ((S.board.detach b).topOf (Base.relabel ρ b')).map ρ
    rw [h.board_mapByRho, Board.mapByRho_detach]
    exact Board.mapByRho_topOf h.isTwinMap (S.board.detach b) b'

/-- **The worry-back rung derivation**: under the no-skew premise (the
source's other twin suit at most `c`'s rung) and the mirror's height
bound, the mirror's rung of `ρ c`'s suit is exactly `c`'s rung — the
rank-above card, translated through the invariant, is stacked in
neither twin suit.  (The king corner — no rank-above card — is cut by
the height bound; at a WF mirror it is free.) -/
theorem State.TwinCore.stackPile_rung {ρ σ S M c}
    (h : State.TwinCore ρ σ S M)
    (hon : c.suit = σ ∨ c.suit = σ.flipPair)
    (hSg : S.heights c.suit = c.rank.toIdx + 1)
    (hskew : S.heights (Card.flipSuit c).suit ≤ c.rank.toIdx + 1)
    (hMle : M.heights (ρ c).suit ≤ 13) :
    M.heights (ρ c).suit = c.rank.toIdx + 1 := by
  have hgt : M.heights (ρ c).suit > c.rank.toIdx := by
    have h1 := (h.stacked_iff c hon).mpr (by omega)
    rw [Card.IsTwinMap.rank h.isTwinMap c] at h1
    exact h1
  have hle : M.heights (ρ c).suit ≤ c.rank.toIdx + 1 := by
    by_cases hc : M.heights (ρ c).suit ≤ c.rank.toIdx + 1
    · exact hc
    · exfalso
      have hge2 : M.heights (ρ c).suit > c.rank.toIdx + 1 := by omega
      have hk12 : c.rank.toIdx + 1 < 13 := by omega
      obtain ⟨m, hm⟩ := Rank.exists_toIdx (c.rank.toIdx + 1) hk12
      have hdon : (Card.mk (ρ c).suit m).suit = σ ∨ (Card.mk (ρ c).suit m).suit = σ.flipPair := by
        show (ρ c).suit = σ ∨ (ρ c).suit = σ.flipPair
        exact h.isTwinMap.suit_mem hon
      have hkeyd := h.stacked_iff (ρ (Card.mk (ρ c).suit m)) (h.isTwinMap.suit_mem hdon)
      rw [h.isTwinMap.invol (Card.mk (ρ c).suit m),
        Card.IsTwinMap.rank h.isTwinMap (Card.mk (ρ c).suit m), hm] at hkeyd
      have hSside : S.heights (ρ (Card.mk (ρ c).suit m)).suit
          > c.rank.toIdx + 1 := hkeyd.mp hge2
      -- the rank-above card's ρ-image is stacked in S at some twin suit — both capped
      rcases h.isTwinMap.pair (Card.mk (ρ c).suit m) with hc | hc
      · have hSside' : S.heights (ρ c).suit > c.rank.toIdx + 1 := by
          rw [hc] at hSside
          exact hSside
        rcases Suit.two_cases hon (h.isTwinMap.suit_mem hon) with hs | hs
        · rw [hs, hSg] at hSside'
          omega
        · rw [hs] at hSside'
          omega
      · have hSside' : S.heights (ρ c).suit.flipPair > c.rank.toIdx + 1 := by
          rw [hc, Card.flipSuit_suit] at hSside
          exact hSside
        rcases Suit.two_cases hon (by
          show (ρ c).suit.flipPair = σ ∨ (ρ c).suit.flipPair = σ.flipPair
          rcases h.isTwinMap.suit_mem hon with hs | hs
          · rw [hs]; exact Or.inr rfl
          · rw [hs]; exact Or.inl (Suit.flipPair_flipPair σ)) with hs | hs
        · rw [hs, hSg] at hSside'
          omega
        · rw [hs] at hSside'
          omega
  omega

/-- **The worry-back step**: a twin-suit foundation card's worry-back
translates through the correspondence — the mirror plays
`stackPile (ρ c) (relabel ρ b)` — when the mirror's rung of `ρ c`'s
suit is exactly `c`'s rung (the aligned premise; `stackPile_rung`
derives it from the no-skew condition).  The full correspondence is
preserved (no growth: the correspondence maps the worried-back card
consistently). -/
theorem State.TwinCorr.apply_stackPile_onsuit {ρ σ S M R c b}
    (h : State.TwinCorr ρ σ S M)
    (hon : c.suit = σ ∨ c.suit = σ.flipPair)
    (hS : S.apply (Move.stackPile c b) = some R)
    (halign : M.heights (ρ c).suit = c.rank.toIdx + 1) :
    ∃ N, M.apply (Move.stackPile (ρ c) (Base.relabel ρ b)) = some N ∧
      State.TwinCorr ρ σ R N := by
  rw [apply_stackPile_iff] at hS
  obtain ⟨hrk, hcp, bd, hatt, rfl⟩ := hS
  have hrkM : (ρ c).rank.toIdx + 1 = M.heights (ρ c).suit := by
    rw [Card.IsTwinMap.rank h.isTwinMap c, halign]
  have hcpM : M.canPlace (ρ c) (Base.relabel ρ b) = true := by
    rw [State.canPlace_relabel h.isTwinMap h.board_mapByRho c b]
    exact hcp
  have hattM : M.board.attach (Base.relabel ρ b) (ρ c)
      = some (Board.mapByRho h.isTwinMap bd) := by
    rw [h.board_mapByRho]
    exact Board.mapByRho_attach h.isTwinMap hatt
  refine ⟨{M with
      board := Board.mapByRho h.isTwinMap bd,
      heights := fun s => if s = (ρ c).suit then M.heights s - 1 else M.heights s},
    apply_stackPile_iff.mpr ⟨hrkM, hcpM, Board.mapByRho h.isTwinMap bd, hattM, rfl⟩, ?_⟩
  refine ⟨⟨h.isTwinMap, h.fixes_off, h.deal_eq, h.depths_eq, h.stock_eq, h.step_eq,
    ?_, ?_⟩, ?_⟩
  · intro s hs1 hs2
    have honρ : (ρ c).suit = σ ∨ (ρ c).suit = σ.flipPair := h.isTwinMap.suit_mem hon
    have hne1 : s ≠ (ρ c).suit := by
      rcases honρ with hs | hs
      · intro hcon; exact hs1 (hcon.trans hs)
      · intro hcon; exact hs2 (hcon.trans hs)
    have hne2 : s ≠ c.suit := by
      rcases hon with hs | hs
      · intro hcon; exact hs1 (hcon.trans hs)
      · intro hcon; exact hs2 (hcon.trans hs)
    show (if s = (ρ c).suit then M.heights s - 1 else M.heights s)
      = (if s = c.suit then S.heights s - 1 else S.heights s)
    rw [if_neg hne1, if_neg hne2]
    exact h.heights_off s hs1 hs2
  · intro c' hon'
    have hfc : (Card.flipSuit c).suit ≠ c.suit := by
      show c.suit.flipPair ≠ c.suit
      exact Suit.flipPair_ne c.suit
    have hfcρ : (ρ (Card.flipSuit c)).suit ≠ (ρ c).suit := by
      rw [h.isTwinMap.flip_comm c, Card.flipSuit_suit]
      exact Suit.flipPair_ne (ρ c).suit
    have honf : (Card.flipSuit c).suit = σ ∨ (Card.flipSuit c).suit = σ.flipPair := by
      show c.suit.flipPair = σ ∨ c.suit.flipPair = σ.flipPair
      rcases hon with hs | hs
      · rw [hs]; exact Or.inr rfl
      · rw [hs]; exact Or.inl (Suit.flipPair_flipPair σ)
    by_cases hcc : c' = c
    · rw [hcc]
      show (if (ρ c).suit = (ρ c).suit then M.heights (ρ c).suit - 1
          else M.heights (ρ c).suit) > (ρ c).rank.toIdx
        ↔ (if c.suit = c.suit then S.heights c.suit - 1 else S.heights c.suit)
          > c.rank.toIdx
      rw [if_pos rfl, if_pos rfl, Card.IsTwinMap.rank h.isTwinMap c, halign]
      constructor <;> intro hlt <;> omega
    · by_cases hcc' : c' = Card.flipSuit c
      · rw [hcc']
        show (if (ρ (Card.flipSuit c)).suit = (ρ c).suit
              then M.heights (ρ (Card.flipSuit c)).suit - 1
              else M.heights (ρ (Card.flipSuit c)).suit) > (ρ (Card.flipSuit c)).rank.toIdx
          ↔ (if (Card.flipSuit c).suit = c.suit then S.heights (Card.flipSuit c).suit - 1
            else S.heights (Card.flipSuit c).suit) > (Card.flipSuit c).rank.toIdx
        rw [if_neg hfcρ, if_neg hfc, Card.flipSuit_rank c]
        exact h.stacked_iff (Card.flipSuit c) honf
      · exact State.stacked_drop_aux
          (hS := S.heights) (hM := M.heights)
          (hS' := fun s => if s = c.suit then S.heights s - 1 else S.heights s)
          (hM' := fun s => if s = (ρ c).suit then M.heights s - 1 else M.heights s)
          (ρ := ρ) (c := c)
          h.isTwinMap hon h.stacked_iff hrk.symm halign (fun _ => rfl) (fun _ => rfl)
          c' hcc hcc' hon'
  · intro b'
    show (Board.mapByRho h.isTwinMap bd).topOf b' = (bd.topOf (Base.relabel ρ b')).map ρ
    exact Board.mapByRho_topOf h.isTwinMap bd b'

/-- The invariant read through the involution: the card `x`'s own
stackedness in M (at `x`'s suit, below `x`'s rank) against S's height
at `ρ x`'s suit — the boundary-card reads of the growth's rung
arithmetic. -/
theorem State.TwinCore.stacked_self {ρ σ S M} (h : State.TwinCore ρ σ S M)
    (x : Card) (hx : x.suit = σ ∨ x.suit = σ.flipPair) :
    (M.heights x.suit > x.rank.toIdx ↔ S.heights (ρ x).suit > x.rank.toIdx) := by
  have h0 := h.stacked_iff (ρ x) (h.isTwinMap.suit_mem hx)
  rw [h.isTwinMap.invol x, Card.IsTwinMap.rank h.isTwinMap x] at h0
  exact h0

/-- **The growth step**: at the source's twin-suit stacking of `q`,
when the mirror's rung of `ρ q`'s suit is NOT `q`'s rank (the
misalignment), the mirror stacks the FLIP `flip (ρ q)` and the
correspondence GROWS to `τ_{ρ q} ∘ ρ`.  The flip's legality is
DERIVED — no balance or prefix side-conditions: the stacked-set
invariant forces the source's other twin suit below the rank (the
flip is not buried), and the mirror's own rung of the flip is exact.

The conclusion is a TWINCORE, not the full correspondence: the growth
CROSSES the two boards at the moved pair's seats — the source keeps
`flip q` seated at `bq'` while the mirror keeps `ρ q` seated at
`ρ bq` — so the pointwise board conjugation holds only OUTSIDE the
crossed seats (the excluded set also covers the seats sitting on the
pair, where the ρ/ρ' relabels differ).  Resolving the crossing —
re-homing the stranded card, or the rung-sorted catch-up scheduling —
is the interleaving window's remaining content. -/
theorem State.TwinCorr.apply_pileStack_grow {ρ σ S M R q bq bq'}
    (h : State.TwinCorr ρ σ S M)
    (hon : q.suit = σ ∨ q.suit = σ.flipPair)
    (hS : S.apply (Move.pileStack q) = some R)
    (hbq : S.board.bottomOf q = some bq)
    (hbq' : S.board.bottomOf (Card.flipSuit q) = some bq')
    (hflip : S.board.topOf (Sum.inr (Card.flipSuit q)) = none)
    (hmis : M.heights (ρ q).suit ≠ q.rank.toIdx) :
    ∃ N, M.apply (Move.pileStack (Card.flipSuit (ρ q))) = some N ∧
      State.TwinCore (Card.swapTwin (ρ q) ∘ ρ) σ R N ∧
      (∀ β, Base.relabel ρ β ≠ bq → Base.relabel ρ β ≠ bq' →
        Base.relabel ρ β ≠ Sum.inr q → Base.relabel ρ β ≠ Sum.inr (Card.flipSuit q) →
        N.board.topOf β
          = Option.map (Card.swapTwin (ρ q) ∘ ρ)
              (R.board.topOf (Base.relabel (Card.swapTwin (ρ q) ∘ ρ) β))) ∧
      N.board.topOf (Base.relabel ρ bq) = some (ρ q) ∧
      N.board.topOf (Base.relabel ρ bq') = none := by
  rw [apply_pileStack_iff] at hS
  obtain ⟨htop, b, hbot, hrk, rfl⟩ := hS
  have hbqeq : bq = b := by
    have h1 : S.board.topOf b = some q := (Board.bottomOf_eq S.board q b).mp hbot
    have h2 : S.board.topOf bq = some q := (Board.bottomOf_eq S.board q bq).mp hbq
    exact (S.board.inj b bq q h1 h2).symm
  subst hbqeq
  -- the normalized invariant
  have key : ∀ x : Card, x.suit = σ ∨ x.suit = σ.flipPair →
      (M.heights (ρ x).suit > x.rank.toIdx ↔ S.heights x.suit > x.rank.toIdx) := by
    intro x hx
    have h0 := h.stacked_iff x hx
    rw [Card.IsTwinMap.rank h.isTwinMap x] at h0
    exact h0
  have honu : (ρ q).suit = σ ∨ (ρ q).suit = σ.flipPair := h.isTwinMap.suit_mem hon
  have honf : (Card.flipSuit q).suit = σ ∨ (Card.flipSuit q).suit = σ.flipPair := by
    show q.suit.flipPair = σ ∨ q.suit.flipPair = σ.flipPair
    rcases hon with hs | hs
    · rw [hs]; exact Or.inr rfl
    · rw [hs]; exact Or.inl (Suit.flipPair_flipPair σ)
  have hvρ : Card.flipSuit (ρ q) = ρ (Card.flipSuit q) := (h.isTwinMap.flip_comm q).symm
  have hF1 : ¬(M.heights (ρ q).suit > q.rank.toIdx) := by
    intro hgt
    have h1 := (key q hon).mp hgt
    rw [← hrk] at h1
    exact Nat.lt_irrefl _ h1
  have hslt : M.heights (ρ q).suit < q.rank.toIdx := by omega
  have hk12 : q.rank.toIdx < 13 := Rank.toIdx_lt q.rank
  obtain ⟨m, hm⟩ := Rank.exists_toIdx (q.rank.toIdx - 1) (by omega)
  -- the boundary card read at ρ q's suit (the rank-(k−1) card)
  have hB : M.heights (ρ q).suit > q.rank.toIdx - 1
      ↔ S.heights (ρ (Card.mk (ρ q).suit m)).suit > q.rank.toIdx - 1 := by
    have h0 := h.toTwinCore.stacked_self (Card.mk (ρ q).suit m)
      (by show (ρ q).suit = σ ∨ (ρ q).suit = σ.flipPair; exact honu)
    rw [show (Card.mk (ρ q).suit m).suit = (ρ q).suit from rfl, hm] at h0
    exact h0
  have hnotw : ¬(M.heights (ρ q).suit > q.rank.toIdx - 1) := by clear hB; omega
  -- the source's other twin rung is below the rank (the flip is not buried)
  have hUP : S.heights (Card.flipSuit q).suit ≤ q.rank.toIdx - 1 := by
    rcases Suit.two_cases hon honu with hu | hu
    · rcases h.isTwinMap.pair (Card.mk (ρ q).suit m) with hc | hc
      · exfalso
        rw [hc] at hB
        rw [show (Card.mk (ρ q).suit m).suit = (ρ q).suit from rfl] at hB
        have h1 : ¬(S.heights (ρ q).suit > q.rank.toIdx - 1) := fun hg =>
          hnotw (hB.mpr hg)
        rw [hu, hrk] at h1
        omega
      · rw [hc] at hB
        rw [show (Card.flipSuit (Card.mk (ρ q).suit m)).suit = (ρ q).suit.flipPair from rfl] at hB
        have h1 : ¬(S.heights (ρ q).suit.flipPair > q.rank.toIdx - 1) := fun hg =>
          hnotw (hB.mpr hg)
        show S.heights q.suit.flipPair ≤ q.rank.toIdx - 1
        rw [hu] at h1
        omega
    · rcases h.isTwinMap.pair (Card.mk (ρ q).suit m) with hc | hc
      · rw [hc] at hB
        rw [show (Card.mk (ρ q).suit m).suit = (ρ q).suit from rfl] at hB
        have h1 : ¬(S.heights (ρ q).suit > q.rank.toIdx - 1) := fun hg =>
          hnotw (hB.mpr hg)
        rw [hu] at h1
        omega
      · exfalso
        rw [hc] at hB
        rw [show (Card.flipSuit (Card.mk (ρ q).suit m)).suit = (ρ q).suit.flipPair from rfl] at hB
        have h1 : ¬(S.heights (ρ q).suit.flipPair > q.rank.toIdx - 1) := fun hg =>
          hnotw (hB.mpr hg)
        rw [hu, Card.flipSuit_suit, Suit.flipPair_flipPair, hrk] at h1
        omega
  -- the flip's rung is exact
  have hB2 : M.heights (Card.flipSuit (ρ q)).suit > q.rank.toIdx
      ↔ S.heights (Card.flipSuit q).suit > q.rank.toIdx := by
    have h0 := h.stacked_iff (Card.flipSuit q) honf
    rw [← hvρ, Card.flipSuit_rank (ρ q), Card.IsTwinMap.rank h.isTwinMap q,
      Card.flipSuit_rank q] at h0
    exact h0
  have hgoal : M.heights (Card.flipSuit (ρ q)).suit = q.rank.toIdx := by
    -- the boundary card read at the flip's suit (the rank-(k−1) card, ρ-flipped)
    have hB3 : M.heights (Card.flipSuit (ρ q)).suit > q.rank.toIdx - 1
        ↔ S.heights (ρ (Card.flipSuit (Card.mk (ρ q).suit m))).suit
          > q.rank.toIdx - 1 := by
      have h0 := h.toTwinCore.stacked_self (Card.flipSuit (Card.mk (ρ q).suit m))
        (by show (ρ q).suit.flipPair = σ ∨ (ρ q).suit.flipPair = σ.flipPair
            rcases honu with hs | hs
            · rw [hs]; exact Or.inr rfl
            · rw [hs]; exact Or.inl (Suit.flipPair_flipPair σ))
      rw [show (Card.flipSuit (Card.mk (ρ q).suit m)).suit = (ρ q).suit.flipPair from rfl,
        show (ρ q).suit.flipPair = (Card.flipSuit (ρ q)).suit from rfl,
        show (Card.flipSuit (Card.mk (ρ q).suit m)).rank.toIdx = m.toIdx from rfl,
        hm] at h0
      exact h0
    rcases Suit.two_cases hon honu with hu | hu
    · rcases h.isTwinMap.pair (Card.mk (ρ q).suit m) with hc | hc
      · exfalso
        rw [hc] at hB
        rw [show (Card.mk (ρ q).suit m).suit = (ρ q).suit from rfl] at hB
        have h1 : ¬(S.heights (ρ q).suit > q.rank.toIdx - 1) := fun hg =>
          hnotw (hB.mpr hg)
        rw [hu, hrk] at h1
        clear hB hB2 hB3; omega
      · -- ρ q's suit = q's suit, boundary flipped: constructive
        rw [h.isTwinMap.flip_comm (Card.mk (ρ q).suit m), hc,
          Card.flipSuit_flipSuit (Card.mk (ρ q).suit m),
          show (Card.mk (ρ q).suit m).suit = (ρ q).suit from rfl] at hB3
        have hleM : ¬(M.heights (Card.flipSuit (ρ q)).suit > q.rank.toIdx) := by
          intro hg
          have h2 := hB2.mp hg
          clear hB hB2 hB3; omega
        have hgeM : M.heights (Card.flipSuit (ρ q)).suit > q.rank.toIdx - 1 := by
          have hSside : S.heights (ρ q).suit > q.rank.toIdx - 1 := by
            rw [hu, hrk]
            clear hB hB2 hB3; omega
          exact hB3.mpr hSside
        clear hB hB2 hB3; omega
    · rcases h.isTwinMap.pair (Card.mk (ρ q).suit m) with hc | hc
      · -- ρ q's suit = the flip's, boundary unflipped: constructive
        rw [h.isTwinMap.flip_comm (Card.mk (ρ q).suit m), hc,
          show (Card.flipSuit (Card.mk (ρ q).suit m)).suit = (ρ q).suit.flipPair from rfl] at hB3
        have hleM : ¬(M.heights (Card.flipSuit (ρ q)).suit > q.rank.toIdx) := by
          intro hg
          have h2 := hB2.mp hg
          clear hB hB2 hB3; omega
        have hgeM : M.heights (Card.flipSuit (ρ q)).suit > q.rank.toIdx - 1 := by
          have hSside : S.heights (ρ q).suit.flipPair > q.rank.toIdx - 1 := by
            rw [hu, Card.flipSuit_suit, Suit.flipPair_flipPair, hrk]
            clear hB hB2 hB3; omega
          exact hB3.mpr hSside
        clear hB hB2 hB3; omega
      · exfalso
        rw [hc] at hB
        rw [show (Card.flipSuit (Card.mk (ρ q).suit m)).suit = (ρ q).suit.flipPair from rfl] at hB
        have h1 : ¬(S.heights (ρ q).suit.flipPair > q.rank.toIdx - 1) := fun hg =>
          hnotw (hB.mpr hg)
        rw [hu, Card.flipSuit_suit, Suit.flipPair_flipPair, hrk] at h1
        omega
  -- the mirror's firing
  have htopM : M.board.topOf (Sum.inr (Card.flipSuit (ρ q))) = none := by
    rw [h.board_eq]
    show (S.board.topOf (Sum.inr (ρ (Card.flipSuit (ρ q))))).map ρ = none
    rw [hvρ, h.isTwinMap.invol (Card.flipSuit q), hflip]
    rfl
  have hbotM : M.board.bottomOf (Card.flipSuit (ρ q))
      = some (Base.relabel ρ bq') := by
    rw [h.board_mapByRho, hvρ, Board.mapByRho_bottomOf, hbq', Option.map_some]
  have hrkM : (Card.flipSuit (ρ q)).rank.toIdx
      = M.heights (Card.flipSuit (ρ q)).suit := by
    rw [Card.flipSuit_rank (ρ q), Card.IsTwinMap.rank h.isTwinMap q, hgoal]
  have hbqne : bq ≠ bq' := by
    intro hcon
    have h1 : S.board.topOf bq = some q := (Board.bottomOf_eq S.board q bq).mp hbq
    have h2 : S.board.topOf bq' = some (Card.flipSuit q) :=
      (Board.bottomOf_eq S.board (Card.flipSuit q) bq').mp hbq'
    rw [hcon] at h1
    exact Card.flipSuit_ne q (Option.some.inj (h2.symm.trans h1))
  refine ⟨{M with
      board := M.board.detach (Base.relabel ρ bq'),
      heights := fun s => if s = (Card.flipSuit (ρ q)).suit
        then M.heights s + 1 else M.heights s},
    apply_pileStack_iff.mpr ⟨htopM, Base.relabel ρ bq', hbotM, hrkM, rfl⟩,
    ?_, ?_, ?_, ?_⟩
  · -- the grown core
    refine ⟨?_, ?_, h.deal_eq, h.depths_eq, h.stock_eq, h.step_eq, ?_, ?_⟩
    · rw [Card.swapTwin_pair_congr h.isTwinMap q]
      exact h.isTwinMap.comp_swapTwin q
    · intro c h1 h2
      rw [Card.swapTwin_pair_congr h.isTwinMap q]
      exact Card.IsTwinMap.fixes_off_comp_swapTwin h.fixes_off hon c h1 h2
    · intro s hs1 hs2
      have honv : (Card.flipSuit (ρ q)).suit = σ ∨ (Card.flipSuit (ρ q)).suit = σ.flipPair := by
        rw [Card.flipSuit_suit]
        rcases honu with hs | hs
        · rw [hs]; exact Or.inr rfl
        · rw [hs]; exact Or.inl (Suit.flipPair_flipPair σ)
      have hne1 : s ≠ (Card.flipSuit (ρ q)).suit := by
        rcases honv with hs | hs
        · intro hcon; exact hs1 (hcon.trans hs)
        · intro hcon; exact hs2 (hcon.trans hs)
      have hne2 : s ≠ q.suit := by
        rcases hon with hs | hs
        · intro hcon; exact hs1 (hcon.trans hs)
        · intro hcon; exact hs2 (hcon.trans hs)
      show (if s = (Card.flipSuit (ρ q)).suit then M.heights s + 1 else M.heights s)
        = (if s = q.suit then S.heights s + 1 else S.heights s)
      rw [if_neg hne1, if_neg hne2]
      exact h.heights_off s hs1 hs2
    · intro c' hon'
      have hρq : (Card.swapTwin (ρ q) ∘ ρ) q = Card.flipSuit (ρ q) := by
        show Card.swapTwin (ρ q) (ρ q) = Card.flipSuit (ρ q)
        rw [Card.swapTwin_self_left (ρ q)]
      have hρn' : Card.IsTwinMap (Card.swapTwin (ρ q) ∘ ρ) := by
        rw [Card.swapTwin_pair_congr h.isTwinMap q]
        exact h.isTwinMap.comp_swapTwin q
      by_cases hcq : c' = q
      · rw [hcq]
        rw [hρq]
        constructor
        · intro _
          show (if q.suit = q.suit then S.heights q.suit + 1 else S.heights q.suit)
            > q.rank.toIdx
          rw [if_pos rfl, ← hrk]
          clear hB hB2; omega
        · intro _
          show (if (Card.flipSuit (ρ q)).suit = (Card.flipSuit (ρ q)).suit
              then M.heights (Card.flipSuit (ρ q)).suit + 1
              else M.heights (Card.flipSuit (ρ q)).suit) > (Card.flipSuit (ρ q)).rank.toIdx
          rw [if_pos rfl, Card.flipSuit_rank (ρ q), Card.IsTwinMap.rank h.isTwinMap q, hgoal]
          clear hB hB2; omega
      · by_cases hcq' : c' = Card.flipSuit q
        · rw [hcq']
          have hρq' : (Card.swapTwin (ρ q) ∘ ρ) (Card.flipSuit q) = ρ q := by
            show Card.swapTwin (ρ q) (ρ (Card.flipSuit q)) = ρ q
            rw [← hvρ, Card.swapTwin_self_right (ρ q)]
          rw [hρq']
          have hnv : (ρ q).suit ≠ (Card.flipSuit (ρ q)).suit := by
            rw [Card.flipSuit_suit]
            exact (Suit.flipPair_ne (ρ q).suit).symm
          have hqf : (Card.flipSuit q).suit ≠ q.suit := by
            show q.suit.flipPair ≠ q.suit
            exact Suit.flipPair_ne q.suit
          show (if (ρ q).suit = (Card.flipSuit (ρ q)).suit
              then M.heights (ρ q).suit + 1 else M.heights (ρ q).suit) > (ρ q).rank.toIdx
            ↔ (if (Card.flipSuit q).suit = q.suit then S.heights (Card.flipSuit q).suit + 1
              else S.heights (Card.flipSuit q).suit) > (Card.flipSuit q).rank.toIdx
          rw [if_neg hnv, if_neg hqf, Card.IsTwinMap.rank h.isTwinMap q, Card.flipSuit_rank q]
          constructor
          · intro hlt
            exact absurd hlt hF1
          · intro hlt
            clear hB hB2; omega
        · have hagree : ∀ x, x ≠ q → x ≠ Card.flipSuit q →
              (Card.swapTwin (ρ q) ∘ ρ) x = ρ x := by
            intro x hxq hxq'
            have h1 : ρ x ≠ ρ q := fun hcon => hxq (h.isTwinMap.inj hcon)
            have h2 : ρ x ≠ Card.flipSuit (ρ q) := by
              rw [hvρ]
              exact fun hcon => hxq' (h.isTwinMap.inj hcon)
            show Card.swapTwin (ρ q) (ρ x) = ρ x
            rw [Card.swapTwin_of_ne h1 h2]
          exact State.stacked_bump_aux
            (hS := S.heights) (hM := M.heights)
            (hS' := fun s => if s = q.suit then S.heights s + 1 else S.heights s)
            (hM' := fun s => if s = (Card.flipSuit (ρ q)).suit
              then M.heights s + 1 else M.heights s)
            (ρ := ρ) (ρn := Card.swapTwin (ρ q) ∘ ρ) (q := q) (w := Card.flipSuit (ρ q))
            h.isTwinMap hρn' hon hρq hagree h.stacked_iff hrk.symm hgoal
            (fun _ => rfl) (fun _ => rfl) c' hcq hcq' hon'
  · -- the board outside the crossed seats
    intro β hγ1 hγ2 hγ3 hγ4
    have hN : (M.board.detach (Base.relabel ρ bq')).topOf β
        = (S.board.topOf (Base.relabel ρ β)).map ρ := by
      show (if β = Base.relabel ρ bq' then none else M.board.topOf β) = _
      rw [if_neg (fun hcon => hγ2 (by
        rw [hcon, Base.relabel_invol h.isTwinMap bq']))]
      exact h.board_eq β
    have hfixγ : Base.relabel (Card.swapTwin (ρ q) ∘ ρ) β = Base.relabel ρ β := by
      rw [Base.relabel_comp]
      cases hγ : Base.relabel ρ β with
      | inl a => rfl
      | inr d =>
          have hdq : d ≠ q := fun hcon => hγ3 (by rw [hγ, hcon])
          have hdq' : d ≠ Card.flipSuit q := fun hcon => hγ4 (by rw [hγ, hcon])
          have hd1 : d ≠ ρ q := by
            rcases h.isTwinMap.pair q with hc | hc
            · rw [hc]; exact hdq
            · rw [hc]; exact hdq'
          have hd2 : d ≠ Card.flipSuit (ρ q) := by
            rw [hvρ]
            rcases h.isTwinMap.pair (Card.flipSuit q) with hc | hc
            · rw [hc]; exact hdq'
            · rw [hc, Card.flipSuit_flipSuit q]; exact hdq
          show Sum.inr (Card.swapTwin (ρ q) d) = Sum.inr d
          rw [Card.swapTwin_of_ne hd1 hd2]
    have hR : (S.board.detach bq).topOf (Base.relabel ρ β)
        = S.board.topOf (Base.relabel ρ β) := by
      show (if Base.relabel ρ β = bq then none else S.board.topOf (Base.relabel ρ β)) = _
      rw [if_neg hγ1]
    rw [hN, hfixγ, hR]
    cases hval : S.board.topOf (Base.relabel ρ β) with
    | none => rfl
    | some x =>
        have hxq : x ≠ q := by
          intro hcon
          apply hγ1
          have h1 : S.board.topOf (Base.relabel ρ β) = some q := by rw [hval, hcon]
          have h2 : S.board.topOf bq = some q := (Board.bottomOf_eq S.board q bq).mp hbq
          exact S.board.inj (Base.relabel ρ β) bq q h1 h2
        have hxq' : x ≠ Card.flipSuit q := by
          intro hcon
          apply hγ2
          have h1 : S.board.topOf (Base.relabel ρ β) = some (Card.flipSuit q) := by
            rw [hval, hcon]
          have h2 : S.board.topOf bq' = some (Card.flipSuit q) :=
            (Board.bottomOf_eq S.board (Card.flipSuit q) bq').mp hbq'
          exact S.board.inj (Base.relabel ρ β) bq' (Card.flipSuit q) h1 h2
        have hxr : ρ x = (Card.swapTwin (ρ q) ∘ ρ) x := by
          have h1 : ρ x ≠ ρ q := fun hcon => hxq (h.isTwinMap.inj hcon)
          have h2 : ρ x ≠ Card.flipSuit (ρ q) := by
            rw [hvρ]
            exact fun hcon => hxq' (h.isTwinMap.inj hcon)
          show ρ x = Card.swapTwin (ρ q) (ρ x)
          rw [Card.swapTwin_of_ne h1 h2]
        rw [Option.map_some, Option.map_some, hxr]
  · -- the stranded card at the crossed seat
    show (if Base.relabel ρ bq = Base.relabel ρ bq' then none
        else M.board.topOf (Base.relabel ρ bq)) = some (ρ q)
    rw [if_neg (fun hcon => hbqne (Base.relabel_inj h.isTwinMap hcon))]
    rw [h.board_eq, Base.relabel_invol h.isTwinMap bq,
      (Board.bottomOf_eq S.board q bq).mp hbq, Option.map_some]
  · -- the detached seat
    show (if Base.relabel ρ bq' = Base.relabel ρ bq' then none
        else M.board.topOf (Base.relabel ρ bq')) = none
    rw [if_pos rfl]

/-! ## §6. The crossed-set frame — the weakened correspondence

The growth's conclusion (§5) hands over a state that satisfies the
core and the board conjugation only OUTSIDE the crossed seats, with
the stranded `ρ q` still seated at its old seat and the partner's
seat-image vacated.  The frame below collects what survives: the
board's CARD SET still conjugates globally (a crossing swaps the two
members of a twin pair between the games, and each board holds one
member, so the ρ-images coincide — `vis_iff`), the seat conjugation
survives away from the stranded cards and the partners
(`top_some`/`top_none`/`top_wanted`), and the run walks conjugate on
the stranded columns and stay inside the image walk elsewhere
(`above_strand`/`above_sub`).  The crossed cards drain when they
stack in both games — the catch-up lemma of this section. -/

/-- A `none` cell ends the walk at the accumulator, at every fuel. -/
theorem Board.aboveOf_go_none {bd : Board} {b : Base} (h : bd.topOf b = none) :
    ∀ (n : Nat) (acc : List Card), Board.aboveOf.go bd n b acc = acc := by
  intro n
  cases n with
  | zero => intro acc; rfl
  | succ m => intro acc; rw [Board.aboveOf_go_succ, h]

/-- Detaching a bare top only removes that card from every run: the
walk on the detached board is the walk on the original with the
detached card filtered out.  The walk probes the detached seat only
after passing through the card under it — and the detached card is
bare, so that probe is the walk's last step; everything before it the
two walks share (the accumulator is carried free of the detached
card, so the contains-guards coincide). -/
theorem Board.aboveOf_go_detach {bd : Board} {b : Base} {e : Card}
    (hb : bd.topOf b = some e) (hbare : bd.topOf (Sum.inr e) = none) :
    ∀ (n : Nat) (b' : Base) (acc : List Card), ¬ acc.contains e = true →
      Board.aboveOf.go (bd.detach b) n b' acc =
        (Board.aboveOf.go bd n b' acc).filter (fun c => c != e) := by
  have hself : ∀ acc : List Card, ¬ acc.contains e = true →
      acc = acc.filter (fun c => c != e) := by
    intro acc hacc
    exact (List.filter_eq_self.mpr (fun x hx =>
      bne_iff_ne.mpr (fun hcon =>
        hacc (List.contains_iff_mem.mpr (by rw [← hcon]; exact hx))))).symm
  intro n
  induction n with
  | zero =>
      intro b' acc hacc
      exact hself acc hacc
  | succ n ih =>
      intro b' acc hacc
      rw [Board.aboveOf_go_succ, Board.aboveOf_go_succ]
      cases hb' : bd.topOf b' with
      | none =>
          have hbb' : b' ≠ b := fun hcon => by
            subst hcon
            rw [hb'] at hb
            exact absurd hb (by simp)
          have hd' : (bd.detach b).topOf b' = none := by
            rw [Board.detach_topOf_ne bd b b' hbb']; exact hb'
          simp only [hd']
          exact hself acc hacc
      | some c' =>
          by_cases hbb' : b' = b
          · rw [hbb'] at hb' ⊢
            have hce : e = c' := Option.some.inj (hb.symm.trans hb')
            simp only [Board.detach_topOf, ← hce]
            rw [if_neg hacc, Board.aboveOf_go_none hbare n (e :: acc),
              List.filter_cons_of_neg (by simp)]
            exact hself acc hacc
          · have hd' : (bd.detach b).topOf b' = some c' := by
              rw [Board.detach_topOf_ne bd b b' hbb']; exact hb'
            simp only [hd']
            by_cases hcon : acc.contains c' = true
            · rw [if_pos hcon, if_pos hcon]
              exact hself acc hacc
            · rw [if_neg hcon, if_neg hcon]
              refine ih (Sum.inr c') (c' :: acc) (fun hc => ?_)
              have hmem : e ∈ c' :: acc := List.contains_iff_mem.mp hc
              rcases List.mem_cons.mp hmem with rfl | hmem'
              · exact absurd (bd.inj b b' e hb hb') (fun hcon => hbb' hcon.symm)
              · exact hacc (List.contains_iff_mem.mpr hmem')

/-- The `aboveOf`-level form: a bare top's detach filters its own card
out of every run. -/
theorem Board.aboveOf_detach_filter {bd : Board} {b : Base} {e : Card}
    (hb : bd.topOf b = some e) (hbare : bd.topOf (Sum.inr e) = none) (c : Card) :
    (bd.detach b).aboveOf c = (bd.aboveOf c).filter (fun c => c != e) :=
  Board.aboveOf_go_detach hb hbare 52 (Sum.inr c) [] (by simp)

/-- Detaching preserves every other card's seat (the round trip
through the untouched cells). -/
theorem Board.bottomOf_detach_ne {bd : Board} {b : Base} {c : Card} {b' : Base}
    (h : bd.bottomOf c = some b') (hnb : b' ≠ b) :
    (bd.detach b).bottomOf c = some b' := by
  have h1 : bd.topOf b' = some c := (Board.bottomOf_eq bd c b').mp h
  refine (Board.bottomOf_eq _ _ _).mpr ?_
  rw [Board.detach_topOf_ne bd b b' hnb]
  exact h1

/-- Detaching seats no new card (the search over untouched cells). -/
theorem Board.bottomOf_detach_of_none {bd : Board} {b : Base} {c : Card}
    (h : bd.bottomOf c = none) : (bd.detach b).bottomOf c = none := by
  refine (Board.bottomOf_eq_none _ c).mpr (fun b' hb' => ?_)
  by_cases hbb : b' = b
  · subst hbb
    rw [Board.detach_topOf] at hb'
    exact absurd hb' (by simp)
  · rw [Board.detach_topOf_ne _ _ _ hbb] at hb'
    exact (Board.bottomOf_eq_none bd c).mp h b' hb'

/-- Detaching a seat preserves every other card's seated/unseated
status (the card at the detached seat is the only one unseated — the
frame's card-set transfer under a board update). -/
theorem Board.isVis_detach_eq {bd : Board} {b : Base} {e c : Card}
    (hb : bd.topOf b = some e) (hc : c ≠ e) :
    ((bd.detach b).bottomOf c).isSome = (bd.bottomOf c).isSome := by
  cases hbd : bd.bottomOf c with
  | none => rw [Board.bottomOf_detach_of_none hbd]
  | some b' =>
      have hb' : b' ≠ b := by
        intro hcon
        subst hcon
        have h1 : bd.topOf b' = some c := (Board.bottomOf_eq _ _ _).mp hbd
        exact hc (Option.some.inj (h1.symm.trans hb))
      rw [Board.bottomOf_detach_ne hbd hb']

/-- A twin transposition's action is one of the three trivial
possibilities (the frame's pair-membership bookkeeping). -/
theorem Card.swapTwin_cases (t c : Card) :
    Card.swapTwin t c = t ∨ Card.swapTwin t c = t.flipSuit ∨ Card.swapTwin t c = c := by
  by_cases h1 : c = t
  · right; left; rw [h1, Card.swapTwin_self_left]
  · by_cases h2 : c = t.flipSuit
    · left; rw [h2, Card.swapTwin_self_right]
    · right; right; exact Card.swapTwin_of_ne h1 h2

/-! ### The attach/walk kit (the frame's attach-family substrate)

The duals of the detach kit (§6's helpers): an attachment seats exactly
one card at one seat, and the run walks extend or pass through the new
edge.  `isVis_attach_eq` — the card-set transfer under a board update;
`aboveOf_attach_sup` — reachability is monotone under an attach (the
S-side walk survives into the successor); `mem_aboveOf_attach_new` —
the new card joins every walk that reaches its seat's card (the
SYNCHRONIZED extension: the walk in the successor passes through the
newly seated card when the old walk stopped at its seat);
`mem_aboveOf_attach_cases` — with an empty column over the new card,
every successor walk member is old or the new card itself (the
above_sub case analysis). -/

/-- Attaching a seat preserves every other card's seated status (the
only newly seated card is the attached one, and only at a previously
empty seat). -/
theorem Board.isVis_attach_eq {bd : Board} {b : Base} {c x : Card} {bd' : Board}
    (hatt : bd.attach b c = some bd') (hfree : bd.topOf b = none) (hx : x ≠ c) :
    (bd'.bottomOf x).isSome = (bd.bottomOf x).isSome := by
  cases hbd : bd.bottomOf x with
  | none =>
      have h1 : bd'.bottomOf x = none :=
        (Board.bottomOf_eq_none bd' x).mpr (fun b'' hb'' => by
          by_cases hbb : b'' = b
          · rw [hbb] at hb''
            exact hx (Option.some.inj
              ((Board.attach_topOf _ _ _ hatt).symm.trans hb'')).symm
          · rw [Board.attach_topOf_ne _ _ _ hatt hbb] at hb''
            exact (Board.bottomOf_eq_none bd x).mp hbd b'' hb'')
      rw [h1]
  | some β' =>
      have hβ' : β' ≠ b := by
        intro hcon
        have h1 : bd.topOf β' = some x := (Board.bottomOf_eq bd x β').mp hbd
        rw [hcon, hfree] at h1
        exact absurd h1 (by simp)
      have h1 : bd'.topOf β' = some x := by
        rw [Board.attach_topOf_ne _ _ _ hatt hβ']
        exact (Board.bottomOf_eq bd x β').mp hbd
      have h2 : bd'.bottomOf x = some β' := (Board.bottomOf_eq bd' x β').mpr h1
      rw [h2]

/-- Reachability is monotone under an attach: every old run member
survives (the walk follows the same reads; the new edge only extends). -/
theorem Board.aboveOf_go_attach_sup {bd : Board} {b : Base} {c : Card} {bd' : Board}
    (hatt : bd.attach b c = some bd') :
    ∀ (n : Nat) (b₀ : Base) (acc : List Card) (d : Card),
      d ∈ Board.aboveOf.go bd n b₀ acc → d ∈ Board.aboveOf.go bd' n b₀ acc := by
  have hfree : bd.topOf b = none := ((Board.attach_eq_some_iff _ _ _).mp (by rw [hatt]; simp)).1
  intro n
  induction n with
  | zero => intro b₀ acc d hd; exact hd
  | succ m ih =>
      intro b₀ acc d hd
      by_cases hbb : b₀ = b
      · rw [hbb] at hd ⊢
        rw [Board.aboveOf_go_topOf_none hfree] at hd
        by_cases hc : acc.contains c = true
        · rw [Board.aboveOf_go_stop (Board.attach_topOf _ _ _ hatt) hc]
          exact hd
        · rw [Board.aboveOf_go_step (Board.attach_topOf _ _ _ hatt) hc]
          exact Board.aboveOf_go_mono _ _ _ (List.mem_cons_of_mem _ hd)
      · have hne : bd'.topOf b₀ = bd.topOf b₀ := Board.attach_topOf_ne _ _ _ hatt hbb
        cases hb : bd.topOf b₀ with
        | none =>
            rw [hb] at hne
            rw [Board.aboveOf_go_topOf_none hne]
            rw [Board.aboveOf_go_topOf_none hb] at hd
            exact hd
        | some y =>
            rw [hb] at hne
            by_cases hcon : acc.contains y = true
            · rw [Board.aboveOf_go_stop hne hcon]
              rw [Board.aboveOf_go_stop hb hcon] at hd
              exact hd
            · rw [Board.aboveOf_go_step hne hcon]
              rw [Board.aboveOf_go_step hb hcon] at hd
              exact ih (Sum.inr y) (y :: acc) d hd

theorem Board.aboveOf_attach_sup {bd : Board} {b : Base} {c c₀ d : Card} {bd' : Board}
    (hatt : bd.attach b c = some bd') (hd : d ∈ bd.aboveOf c₀) : d ∈ bd'.aboveOf c₀ :=
  Board.aboveOf_go_attach_sup hatt 52 (Sum.inr c₀) [] d hd

/-- **The synchronized extension**: the newly seated card joins every
walk that reaches its seat's card — the old walk stopped at the
now-filled seat, the new walk passes through the new card (the
frame's `above_sub` case analysis: the new card's column is empty,
so the extension is exactly the new card). -/
theorem Board.aboveOf_go_attach_new {bd : Board} {d q : Card} {bd' : Board}
    (hatt : bd.attach (Sum.inr d) q = some bd') (hstop : bd.topOf (Sum.inr d) = none) :
    ∀ (n : Nat) (c₀ : Card) (acc : List Card),
      d ∈ Board.aboveOf.go bd n (Sum.inr c₀) acc → d ∉ acc →
        q ∈ Board.aboveOf.go bd' (n + 1) (Sum.inr c₀) acc := by
  intro n
  induction n with
  | zero => intro c₀ acc hd hna; exact absurd hd hna
  | succ m ih =>
      intro c₀ acc hd hna
      by_cases hc0 : c₀ = d
      · subst hc0
        rw [Board.aboveOf_go_topOf_none hstop] at hd
        exact absurd hd hna
      · have hne : bd'.topOf (Sum.inr c₀) = bd.topOf (Sum.inr c₀) := by
          refine Board.attach_topOf_ne _ _ _ hatt ?_
          show Sum.inr c₀ ≠ Sum.inr d
          exact fun hcon => hc0 (Sum.inr.inj hcon)
        cases hb : bd.topOf (Sum.inr c₀) with
        | none =>
            rw [hb] at hne
            rw [Board.aboveOf_go_topOf_none hb] at hd
            exact absurd hd hna
        | some y =>
            rw [hb] at hne
            by_cases hcon : acc.contains y = true
            · rw [Board.aboveOf_go_stop hb hcon] at hd
              exact absurd hd hna
            · rw [Board.aboveOf_go_step hb hcon] at hd
              rw [Board.aboveOf_go_step hne hcon]
              by_cases hy : y = d
              · rw [hy]
                by_cases hcon2 : (d :: acc).contains q = true
                · rw [Board.aboveOf_go_stop (Board.attach_topOf _ _ _ hatt) hcon2]
                  exact List.contains_iff_mem.mp hcon2
                · rw [Board.aboveOf_go_step (Board.attach_topOf _ _ _ hatt) hcon2]
                  exact Board.aboveOf_go_mono _ _ _ (List.mem_cons_self)
              · refine ih y (y :: acc) hd (fun hcon2 => ?_)
                rcases List.mem_cons.mp hcon2 with hcon2 | hcon2
                · exact hy hcon2.symm
                · exact hna hcon2

theorem Board.mem_aboveOf_attach_new {bd : Board} {d q c₀ : Card} {bd' : Board}
    (hatt : bd.attach (Sum.inr d) q = some bd') (hstop : bd.topOf (Sum.inr d) = none)
    (hd : d ∈ c₀ :: bd.aboveOf c₀) : q ∈ bd'.aboveOf c₀ := by
  rcases List.mem_cons.mp hd with rfl | hd
  · exact Board.mem_aboveOf_of_topOf (Board.attach_topOf _ _ _ hatt)
  · have h1 := Board.aboveOf_go_attach_new hatt hstop 52 c₀ [] hd (by simp)
    rw [← Board.aboveOf_eq_go (n := 53) (by omega)] at h1
    exact h1

/-- With an empty column over the new card, every successor walk
member is an old member or the new card itself. -/
theorem Board.aboveOf_go_attach_cases {bd : Board} {b : Base} {q : Card} {bd' : Board}
    (hatt : bd.attach b q = some bd') (_hfree : bd.topOf b = none)
    (hcol : bd'.topOf (Sum.inr q) = none) :
    ∀ (n : Nat) (c₀ : Card) (acc : List Card) (d : Card),
      d ∈ Board.aboveOf.go bd' n (Sum.inr c₀) acc →
        d ∈ acc ∨ d = q ∨ d ∈ Board.aboveOf.go bd n (Sum.inr c₀) acc := by
  intro n
  induction n with
  | zero => intro c₀ acc d hd; exact Or.inl hd
  | succ m ih =>
      intro c₀ acc d hd
      by_cases hbb : Sum.inr c₀ = b
      · rw [hbb] at hd ⊢
        by_cases hc : acc.contains q = true
        · rw [Board.aboveOf_go_stop (Board.attach_topOf _ _ _ hatt) hc] at hd
          exact Or.inl hd
        · rw [Board.aboveOf_go_step (Board.attach_topOf _ _ _ hatt) hc] at hd
          cases hm : m with
          | zero =>
              rw [hm] at hd
              rcases List.mem_cons.mp (hd : d ∈ q :: acc) with hq | hd
              · exact Or.inr (Or.inl hq)
              · exact Or.inl hd
          | succ m' =>
              rw [hm] at hd
              rw [Board.aboveOf_go_topOf_none hcol] at hd
              rcases List.mem_cons.mp hd with hq | hd
              · exact Or.inr (Or.inl hq)
              · exact Or.inl hd
      · have hne : bd'.topOf (Sum.inr c₀) = bd.topOf (Sum.inr c₀) :=
          Board.attach_topOf_ne _ _ _ hatt hbb
        cases hb : bd.topOf (Sum.inr c₀) with
        | none =>
            rw [hb] at hne
            rw [Board.aboveOf_go_topOf_none hne] at hd
            rw [Board.aboveOf_go_topOf_none hb]
            exact Or.inl hd
        | some y =>
            rw [hb] at hne
            by_cases hcon : acc.contains y = true
            · rw [Board.aboveOf_go_stop hne hcon] at hd
              rw [Board.aboveOf_go_stop hb hcon]
              exact Or.inl hd
            · rw [Board.aboveOf_go_step hne hcon] at hd
              rw [Board.aboveOf_go_step hb hcon]
              rcases ih y (y :: acc) d hd with h1 | h1 | h1
              · rcases List.mem_cons.mp h1 with h1 | h1
                · refine Or.inr (Or.inr ?_)
                  rw [h1]
                  exact Board.aboveOf_go_mono _ _ _ (List.mem_cons_self)
                · exact Or.inl h1
              · exact Or.inr (Or.inl h1)
              · exact Or.inr (Or.inr h1)

theorem Board.mem_aboveOf_attach_cases {bd : Board} {b : Base} {q c₀ d : Card} {bd' : Board}
    (hatt : bd.attach b q = some bd') (hfree : bd.topOf b = none)
    (hcol : bd'.topOf (Sum.inr q) = none) (hd : d ∈ bd'.aboveOf c₀) :
    d ∈ bd.aboveOf c₀ ∨ d = q := by
  rcases Board.aboveOf_go_attach_cases hatt hfree hcol 52 c₀ [] d hd with h1 | h1 | h1
  · exact absurd h1 (by simp)
  · exact Or.inr h1
  · rw [Board.aboveOf_eq_go (n := 52) (by omega)]
    exact Or.inl h1

/-- **The walk extends through its members**: a card the walk collects
opens the very next read (its own seat), so the seat's top joins the
walk one fuel unit later — the collected card cannot be in the seeded
accumulator, and the match on the seat closes the induction. -/
theorem Board.aboveOf_go_extend {bd : Board} :
    ∀ (n : Nat) (b : Base) (acc : List Card) (z w : Card),
      z ∈ Board.aboveOf.go bd n b acc → ¬ acc.contains z →
        bd.topOf (Sum.inr z) = some w →
          w ∈ Board.aboveOf.go bd (n + 1) b acc := by
  intro n
  induction n with
  | zero =>
      intro b acc z w hz hnc _
      have hz' : z ∈ acc := hz
      exact absurd ((List.contains_iff_mem).mpr hz') hnc
  | succ n ih =>
      intro b acc z w hz hnc hw
      cases ht : bd.topOf b with
      | none =>
          rw [Board.aboveOf_go_topOf_none ht] at hz
          exact absurd ((List.contains_iff_mem).mpr hz) hnc
      | some c' =>
          by_cases hcc : acc.contains c' = true
          · rw [Board.aboveOf_go_stop ht hcc] at hz
            exact absurd ((List.contains_iff_mem).mpr hz) hnc
          · rw [Board.aboveOf_go_step ht hcc] at hz
            rw [Board.aboveOf_go_step ht hcc]
            by_cases hcz : c' = z
            · rw [hcz]
              by_cases hcw : (z :: acc).contains w = true
              · rw [Board.aboveOf_go_stop hw hcw]
                exact (List.contains_iff_mem).mp hcw
              · rw [Board.aboveOf_go_step hw hcw]
                exact Board.aboveOf_go_mem bd n (Sum.inr w) (w :: z :: acc) w (by simp)
            · refine ih (Sum.inr c') (c' :: acc) z w hz ?_ hw
              intro hcon
              rcases List.mem_cons.mp ((List.contains_iff_mem).mp hcon) with h1 | hmem
              · exact hcz h1.symm
              · exact hnc ((List.contains_iff_mem).mpr hmem)

/-- The walk-level form: a walk member's seat-top joins the walk (the
root case is the direct read; the member case goes through the
fuel-margin lemma, folded back by the 52-saturation). -/
theorem Board.mem_aboveOf_extend {bd : Board} {c₀ z w : Card}
    (hz : z ∈ c₀ :: bd.aboveOf c₀) (hw : bd.topOf (Sum.inr z) = some w) :
    w ∈ c₀ :: bd.aboveOf c₀ := by
  rcases List.mem_cons.mp hz with rfl | hz'
  · exact List.mem_cons_of_mem _ (Board.mem_aboveOf_of_topOf hw)
  · have h1 : z ∈ Board.aboveOf.go bd 52 (Sum.inr c₀) [] := hz'
    have h2 := Board.aboveOf_go_extend 52 (Sum.inr c₀) [] z w h1 (by simp) hw
    rw [← Board.aboveOf_eq_go (n := 53) (by omega)] at h2
    exact List.mem_cons_of_mem _ h2

/-- **The two-step attach decomposition**: attaching `r` at `d`'s seat
(with `r`'s column exactly `w` and `w`'s column empty) changes every
walk only through the two new cards — a successor walk member is an
old member, `r`, or `w` (the empty column after `w` makes the fuel
bookkeeping moot). -/
theorem Board.aboveOf_go_attach_two {bd : Board} {d r w : Card} {bd' : Board}
    (hatt : bd.attach (Sum.inr d) r = some bd') (hfree : bd.topOf (Sum.inr d) = none)
    (hw1 : bd'.topOf (Sum.inr r) = some w) (hw2 : bd'.topOf (Sum.inr w) = none) :
    ∀ (n : Nat) (c₀ : Card) (acc : List Card) (y : Card),
      y ∈ Board.aboveOf.go bd' n (Sum.inr c₀) acc →
        y ∈ Board.aboveOf.go bd n (Sum.inr c₀) acc ∨ y = r ∨ y = w := by
  intro n
  induction n with
  | zero => intro c₀ acc y hy; exact Or.inl hy
  | succ m ih =>
      intro c₀ acc y hy
      by_cases hcd : c₀ = d
      · have hrd : bd'.topOf (Sum.inr c₀) = some r := by
          rw [hcd]; exact Board.attach_topOf _ _ _ hatt
        have hmd : bd.topOf (Sum.inr c₀) = none := by rw [hcd]; exact hfree
        rw [Board.aboveOf_go_topOf_none hmd]
        by_cases hcr : acc.contains r = true
        · rw [Board.aboveOf_go_stop hrd hcr] at hy
          exact Or.inl hy
        · rw [Board.aboveOf_go_step hrd hcr] at hy
          cases hm : m with
          | zero =>
              rw [hm] at hy
              have hy' : y ∈ r :: acc := hy
              rcases List.mem_cons.mp hy' with h1 | h1
              · exact Or.inr (Or.inl h1)
              · exact Or.inl h1
          | succ m' =>
              rw [hm] at hy
              by_cases hcw : (r :: acc).contains w = true
              · rw [Board.aboveOf_go_stop hw1 hcw] at hy
                have hy' : y ∈ r :: acc := hy
                rcases List.mem_cons.mp hy' with h1 | h1
                · exact Or.inr (Or.inl h1)
                · exact Or.inl h1
              · rw [Board.aboveOf_go_step hw1 hcw] at hy
                cases hm' : m' with
                | zero =>
                    rw [hm'] at hy
                    have hy' : y ∈ w :: r :: acc := hy
                    rcases List.mem_cons.mp hy' with h1 | h1
                    · exact Or.inr (Or.inr h1)
                    · rcases List.mem_cons.mp h1 with h2 | h2
                      · exact Or.inr (Or.inl h2)
                      · exact Or.inl h2
                | succ m'' =>
                    rw [hm'] at hy
                    rw [Board.aboveOf_go_topOf_none hw2] at hy
                    have hy' : y ∈ w :: r :: acc := hy
                    rcases List.mem_cons.mp hy' with h1 | h1
                    · exact Or.inr (Or.inr h1)
                    · rcases List.mem_cons.mp h1 with h2 | h2
                      · exact Or.inr (Or.inl h2)
                      · exact Or.inl h2
      · have hne : bd'.topOf (Sum.inr c₀) = bd.topOf (Sum.inr c₀) :=
          Board.attach_topOf_ne _ _ _ hatt (fun hcon => hcd (Sum.inr.inj hcon))
        cases hb : bd.topOf (Sum.inr c₀) with
        | none =>
            rw [hb] at hne
            rw [Board.aboveOf_go_topOf_none hne] at hy
            rw [Board.aboveOf_go_topOf_none hb]
            exact Or.inl hy
        | some c' =>
            rw [hb] at hne
            by_cases hcon : acc.contains c' = true
            · rw [Board.aboveOf_go_stop hne hcon] at hy
              rw [Board.aboveOf_go_stop hb hcon]
              exact Or.inl hy
            · rw [Board.aboveOf_go_step hne hcon] at hy
              rw [Board.aboveOf_go_step hb hcon]
              exact ih c' (c' :: acc) y hy

/-- The walk-level form of the two-step attach decomposition. -/
theorem Board.mem_aboveOf_attach_two {bd : Board} {d r w c₀ y : Card} {bd' : Board}
    (hatt : bd.attach (Sum.inr d) r = some bd') (hfree : bd.topOf (Sum.inr d) = none)
    (hw1 : bd'.topOf (Sum.inr r) = some w) (hw2 : bd'.topOf (Sum.inr w) = none)
    (hy : y ∈ bd'.aboveOf c₀) : y ∈ bd.aboveOf c₀ ∨ y = r ∨ y = w := by
  rcases Board.aboveOf_go_attach_two hatt hfree hw1 hw2 52 c₀ [] y hy with h1 | h1 | h1
  · rw [Board.aboveOf_eq_go (n := 52) (by omega)]
    exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)

/-- One more fuel unit only extends the walk: the read either stops
(the result is the accumulator, which the shorter walk already
returned) or continues (both walks step together). -/
theorem Board.aboveOf_go_mono_one {bd : Board} :
    ∀ (n : Nat) (b₀ : Base) (acc : List Card) (d : Card),
      d ∈ Board.aboveOf.go bd n b₀ acc →
        d ∈ Board.aboveOf.go bd (n + 1) b₀ acc := by
  intro n
  induction n with
  | zero =>
      intro b₀ acc d hd
      cases ht : bd.topOf b₀ with
      | none => rw [Board.aboveOf_go_topOf_none ht]; exact hd
      | some c' =>
          by_cases hc : acc.contains c' = true
          · rw [Board.aboveOf_go_stop ht hc]; exact hd
          · rw [Board.aboveOf_go_step ht hc]
            exact List.mem_cons_of_mem _ hd
  | succ m ih =>
      intro b₀ acc d hd
      cases ht : bd.topOf b₀ with
      | none =>
          rw [Board.aboveOf_go_topOf_none ht] at hd ⊢
          exact hd
      | some c' =>
          by_cases hc : acc.contains c' = true
          · rw [Board.aboveOf_go_stop ht hc] at hd ⊢
            exact hd
          · rw [Board.aboveOf_go_step ht hc] at hd
            rw [Board.aboveOf_go_step ht hc]
            exact ih (Sum.inr c') (c' :: acc) d hd

/-- The fuel additivity: any amount of extra fuel only extends. -/
theorem Board.aboveOf_go_fuel_add {bd : Board} :
    ∀ (k m : Nat) (b₀ : Base) (acc : List Card) (d : Card),
      d ∈ Board.aboveOf.go bd m b₀ acc →
        d ∈ Board.aboveOf.go bd (m + k) b₀ acc := by
  intro k
  induction k with
  | zero =>
      intro m b₀ acc d hd
      rw [Nat.add_zero]
      exact hd
  | succ k ih =>
      intro m b₀ acc d hd
      have h1 := ih m b₀ acc d hd
      have h2 := Board.aboveOf_go_mono_one (m + k) b₀ acc d h1
      rw [show m + (k + 1) = (m + k) + 1 from rfl]
      exact h2

/-- **The seeded walk stays inside the seed and the plain walk**: a
walk with a pre-collected accumulator `σ` collects nothing outside
`σ` and what the walk from the same seat with the sub-seed `π`
collects.  The sub-seed's stops are a subset of the seed's (every
`π`-member is a `σ`-member), so the seeded walk stops first, and the
two walks collect the same cards while both run — the seeded walk's
fresh cards are all read by the plain one. -/
theorem Board.aboveOf_go_pair {bd : Board} :
    ∀ (n : Nat) (b₀ : Base) (σ π : List Card) (d : Card),
      (∀ z ∈ π, z ∈ σ) →
        d ∈ Board.aboveOf.go bd n b₀ σ →
          d ∈ σ ∨ d ∈ Board.aboveOf.go bd n b₀ π := by
  intro n
  induction n with
  | zero => intro b₀ σ π d _ hd; exact Or.inl hd
  | succ m ih =>
      intro b₀ σ π d hsub hd
      cases ht : bd.topOf b₀ with
      | none =>
          rw [Board.aboveOf_go_topOf_none ht] at hd
          exact Or.inl hd
      | some c' =>
          by_cases hcs : σ.contains c' = true
          · rw [Board.aboveOf_go_stop ht hcs] at hd
            exact Or.inl hd
          · rw [Board.aboveOf_go_step ht hcs] at hd
            have hcp : π.contains c' ≠ true := by
              intro hcp'
              exact hcs (List.contains_iff_mem.mpr (hsub c' (List.contains_iff_mem.mp hcp')))
            rw [Board.aboveOf_go_step ht hcp]
            have hsub' : ∀ z ∈ c' :: π, z ∈ c' :: σ := by
              intro z hz
              rcases List.mem_cons.mp hz with rfl | hz'
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ (hsub z hz')
            rcases ih (Sum.inr c') (c' :: σ) (c' :: π) d hsub' hd with h1 | h1
            · rcases List.mem_cons.mp h1 with h1a | h1
              · rw [h1a]
                exact Or.inr (Board.aboveOf_go_mem bd m (Sum.inr c') (c' :: π) c' (by simp))
              · exact Or.inl h1
            · exact Or.inr h1

/-- The walk-level seed subsumption: the seeded walk stays inside
the seed and the plain walk from the same seat. -/
theorem Board.aboveOf_go_acc_sub {bd : Board} {b₀ : Base} {σ : List Card} {d : Card}
    {n : Nat} (hd : d ∈ Board.aboveOf.go bd n b₀ σ) :
    d ∈ σ ∨ d ∈ Board.aboveOf.go bd n b₀ [] :=
  Board.aboveOf_go_pair n b₀ σ [] d (by intro z hz; exact absurd hz (by simp)) hd

/-- Any fuel's plain walk is inside the canonical walk (the
saturation at 52 for the longer fuels, the fuel additivity below). -/
theorem Board.aboveOf_go_sat {bd : Board} {q : Card} {m : Nat} {d : Card}
    (hd : d ∈ Board.aboveOf.go bd m (Sum.inr q) []) :
    d ∈ bd.aboveOf q := by
  by_cases hm : m ≤ 52
  · obtain ⟨k, hk⟩ := Nat.le.dest hm
    have h2 := Board.aboveOf_go_fuel_add k m (Sum.inr q) ([] : List Card) d hd
    rw [hk] at h2
    rw [← Board.aboveOf_eq_go (n := 52) (by omega)] at h2
    exact h2
  · rw [← Board.aboveOf_eq_go (n := m) (by omega)] at hd
    exact hd

/-- **The run-column attach decomposition**: attaching `q` at a free
seat changes every walk only through the new card and its own
column — a successor walk member is an accumulator member, `q`
itself, in `q`'s own walk, or an old member.  The seeded-walk
subsumption handles the continuation into the run (`q`'s column),
so no self-guard is needed. -/
theorem Board.aboveOf_go_attach_run {bd : Board} {b : Base} {q : Card} {bd' : Board}
    (hatt : bd.attach b q = some bd') (_hfree : bd.topOf b = none) :
    ∀ (n : Nat) (c₀ : Card) (acc : List Card) (d : Card),
      d ∈ Board.aboveOf.go bd' n (Sum.inr c₀) acc →
        d ∈ acc ∨ d = q ∨ d ∈ bd'.aboveOf q ∨
          d ∈ Board.aboveOf.go bd n (Sum.inr c₀) acc := by
  intro n
  induction n with
  | zero => intro c₀ acc d hd; exact Or.inl hd
  | succ m ih =>
      intro c₀ acc d hd
      by_cases hcb : Sum.inr c₀ = b
      · have hrd : bd'.topOf b = some q := Board.attach_topOf _ _ _ hatt
        rw [hcb] at hd
        by_cases hcq : acc.contains q = true
        · rw [Board.aboveOf_go_stop hrd hcq] at hd
          exact Or.inl hd
        · rw [Board.aboveOf_go_step hrd hcq] at hd
          rcases Board.aboveOf_go_acc_sub hd with h1 | h1
          · rcases List.mem_cons.mp h1 with rfl | h1
            · exact Or.inr (Or.inl rfl)
            · exact Or.inl h1
          · exact Or.inr (Or.inr (Or.inl (Board.aboveOf_go_sat h1)))
      · have hne : bd'.topOf (Sum.inr c₀) = bd.topOf (Sum.inr c₀) :=
          Board.attach_topOf_ne _ _ _ hatt hcb
        cases ht : bd.topOf (Sum.inr c₀) with
        | none =>
            rw [ht] at hne
            rw [Board.aboveOf_go_topOf_none hne] at hd
            exact Or.inl hd
        | some c' =>
            rw [ht] at hne
            by_cases hcon : acc.contains c' = true
            · rw [Board.aboveOf_go_stop hne hcon] at hd
              exact Or.inl hd
            · rw [Board.aboveOf_go_step hne hcon] at hd
              rw [Board.aboveOf_go_step ht hcon]
              rcases ih c' (c' :: acc) d hd with h1 | h1 | h1 | h1
              · rcases List.mem_cons.mp h1 with h1a | h1
                · rw [h1a]
                  exact Or.inr (Or.inr (Or.inr
                    (Board.aboveOf_go_mem bd m (Sum.inr c') (c' :: acc) c' (by simp))))
                · exact Or.inl h1
              · exact Or.inr (Or.inl h1)
              · exact Or.inr (Or.inr (Or.inl h1))
              · exact Or.inr (Or.inr (Or.inr h1))

/-- The walk-level form of the run-column attach decomposition. -/
theorem Board.mem_aboveOf_attach_run {bd : Board} {b : Base} {q c₀ d : Card} {bd' : Board}
    (hatt : bd.attach b q = some bd') (hfree : bd.topOf b = none)
    (hd : d ∈ bd'.aboveOf c₀) :
    d ∈ bd.aboveOf c₀ ∨ d = q ∨ d ∈ bd'.aboveOf q := by
  rcases Board.aboveOf_go_attach_run hatt hfree 52 c₀ [] d hd with h1 | h1 | h1 | h1
  · exact absurd h1 (by simp)
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)
  · rw [Board.aboveOf_eq_go (n := 52) (by omega)]
    exact Or.inl h1

/-- **The predecessor read**: every walk member was read off a walk
member's seat — the walk from `z` collects `w` only by reading the
seat of some card already on the walk (or `z` itself).  This is the
downward step of the run-chain argument (the run's images are only
reachable through the vacated cell). -/
theorem Board.aboveOf_go_pred {bd : Board} :
    ∀ (n : Nat) (z : Card) (acc : List Card) (w : Card),
      w ∈ Board.aboveOf.go bd n (Sum.inr z) acc →
        w ∈ acc ∨ ∃ pred : Card,
          pred ∈ z :: Board.aboveOf.go bd n (Sum.inr z) acc ∧
            bd.topOf (Sum.inr pred) = some w := by
  intro n
  induction n with
  | zero => intro z acc w hd; exact Or.inl hd
  | succ m ih =>
      intro z acc w hd
      cases ht : bd.topOf (Sum.inr z) with
      | none =>
          rw [Board.aboveOf_go_topOf_none ht] at hd
          exact Or.inl hd
      | some c' =>
          by_cases hcon : acc.contains c' = true
          · rw [Board.aboveOf_go_stop ht hcon] at hd
            exact Or.inl hd
          · rw [Board.aboveOf_go_step ht hcon] at hd ⊢
            rcases ih c' (c' :: acc) w hd with h1 | ⟨pred, hmem, htop⟩
            · rcases List.mem_cons.mp h1 with h1a | h1
              · rw [h1a]
                exact Or.inr ⟨z, List.mem_cons_self, ht⟩
              · exact Or.inl h1
            · refine Or.inr ⟨pred, List.mem_cons_of_mem _ ?_, htop⟩
              rcases List.mem_cons.mp hmem with h2a | hmem'
              · rw [h2a]
                exact Board.aboveOf_go_mem bd m (Sum.inr c') (c' :: acc) c' (by simp)
              · exact hmem'

/-- **The detach-split**: detaching at a bare top `c`'s seat truncates
every walk at the vacated seat — every member of the original walk
survives into the detached walk or lies in the run above `c` (the
continuation past the vacated seat is the seeded walk from `c`, which
the subsumption and saturation fold into the run). -/
theorem Board.aboveOf_go_detach_split {bd : Board} {b₀ : Base} {c : Card}
    (hstop : bd.topOf b₀ = some c) :
    ∀ (n : Nat) (z : Card) (acc : List Card) (e : Card),
      e ∈ Board.aboveOf.go bd n (Sum.inr z) acc →
        e ∈ acc ∨ e ∈ Board.aboveOf.go (bd.detach b₀) n (Sum.inr z) acc ∨
          e ∈ c :: bd.aboveOf c := by
  intro n
  induction n with
  | zero => intro z acc e hd; exact Or.inl hd
  | succ m ih =>
      intro z acc e hd
      by_cases hcb : Sum.inr z = b₀
      · rw [hcb] at hd
        by_cases hcc : acc.contains c = true
        · rw [Board.aboveOf_go_stop hstop hcc] at hd
          exact Or.inl hd
        · rw [Board.aboveOf_go_step hstop hcc] at hd
          rcases Board.aboveOf_go_acc_sub hd with h1 | h1
          · rcases List.mem_cons.mp h1 with rfl | h1
            · exact Or.inr (Or.inr List.mem_cons_self)
            · exact Or.inl h1
          · exact Or.inr (Or.inr (List.mem_cons_of_mem _ (Board.aboveOf_go_sat h1)))
      · have hne : (bd.detach b₀).topOf (Sum.inr z) = bd.topOf (Sum.inr z) :=
          Board.detach_topOf_ne bd b₀ (Sum.inr z) hcb
        cases ht : bd.topOf (Sum.inr z) with
        | none =>
            rw [Board.aboveOf_go_topOf_none ht] at hd
            exact Or.inl hd
        | some c' =>
            rw [ht] at hne
            by_cases hcon : acc.contains c' = true
            · rw [Board.aboveOf_go_stop ht hcon] at hd
              exact Or.inl hd
            · rw [Board.aboveOf_go_step ht hcon] at hd
              rw [Board.aboveOf_go_step hne hcon]
              rcases ih c' (c' :: acc) e hd with h1 | h1 | h1
              · rcases List.mem_cons.mp h1 with h1a | h1
                · rw [h1a]
                  exact Or.inr (Or.inl
                    (Board.aboveOf_go_mem (bd.detach b₀) m (Sum.inr c') (c' :: acc) c'
                      (by simp)))
                · exact Or.inl h1
              · exact Or.inr (Or.inl h1)
              · exact Or.inr (Or.inr h1)

/-- A relabeling commutes with filtering off its own moved card: the
image of the filter is the filter of the image at the moved card's
image (the relabeling is injective). -/
theorem map_filter_ne {ρ : Card → Card} (hinj : Function.Injective ρ)
    (l : List Card) (x : Card) :
    (l.filter (fun c => c != x)).map ρ = (l.map ρ).filter (fun c => c != ρ x) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      by_cases hax : a = x
      · subst hax
        have hn : ¬ ((fun c => c != a) a = true) := by
          show ¬ ((a != a) = true); simp
        have hn2 : ¬ ((fun c => c != ρ a) (ρ a) = true) := by
          show ¬ ((ρ a != ρ a) = true); simp
        rw [List.filter_cons_of_neg (p := fun c => c != a) hn, List.map_cons,
          List.filter_cons_of_neg (p := fun c => c != ρ a) hn2]
        exact ih
      · have hne : a ≠ x := hax
        have hp : ((fun c => c != x) a = true) := by
          show ((a != x) = true); exact bne_iff_ne.mpr hne
        have hp2 : ((fun c => c != ρ x) (ρ a) = true) := by
          show ((ρ a != ρ x) = true)
          exact bne_iff_ne.mpr (fun hcon => hne (hinj hcon))
        rw [List.filter_cons_of_pos (p := fun c => c != x) hp, List.map_cons, List.map_cons,
          List.filter_cons_of_pos (p := fun c => c != ρ x) hp2]
        exact congrArg (List.cons (ρ a)) ih

/-- **The catch-up alignment**: when the source is about to stack the
on-suit card `q` at its exact rung and the OTHER twin rung is at or
above the rank, the mirror's rung of `ρ q`'s suit is exactly the rank.
The upper bound is the stacked-iff read at `q` (unstacked at its own
rung in S, so its image is unstacked in M); the lower bound is the
boundary-card read at the rank below — its ρ-preimage is stacked in S
at ONE of the two twin suits, both at or above the rank, so the
boundary card is stacked in M. -/
theorem State.TwinCore.rung_of_skew {ρ σ S M q}
    (h : State.TwinCore ρ σ S M)
    (hon : q.suit = σ ∨ q.suit = σ.flipPair)
    (hq : S.heights q.suit = q.rank.toIdx)
    (hskew : q.rank.toIdx ≤ S.heights (Card.flipSuit q).suit) :
    M.heights (ρ q).suit = q.rank.toIdx := by
  have key := h.stacked_iff q hon
  rw [Card.IsTwinMap.rank h.isTwinMap q] at key
  have hle : ¬ (M.heights (ρ q).suit > q.rank.toIdx) := by
    intro hgt
    have h1 := key.mp hgt
    rw [← hq] at h1
    exact Nat.lt_irrefl _ h1
  clear key
  have hboth : ∀ t : Suit, t = σ ∨ t = σ.flipPair → S.heights t ≥ q.rank.toIdx := by
    intro t ht
    rcases Suit.two_cases hon ht with hc | hc
    · rw [hc, hq]
      exact Nat.le_refl _
    · rw [hc]; exact hskew
  by_cases hk : q.rank.toIdx = 0
  · have h1 : M.heights (ρ q).suit ≤ 0 := by omega
    omega
  · have hk13 : q.rank.toIdx < 13 := Rank.toIdx_lt q.rank
    have hge : ¬ (M.heights (ρ q).suit ≤ q.rank.toIdx - 1) := by
      intro hle'
      obtain ⟨m, hm⟩ := Rank.exists_toIdx (q.rank.toIdx - 1) (by omega)
      have honw : (Card.mk (ρ q).suit m).suit = σ ∨ (Card.mk (ρ q).suit m).suit = σ.flipPair := by
        show (ρ q).suit = σ ∨ (ρ q).suit = σ.flipPair
        exact h.isTwinMap.suit_mem hon
      have honw' : (ρ (Card.mk (ρ q).suit m)).suit = σ ∨
          (ρ (Card.mk (ρ q).suit m)).suit = σ.flipPair :=
        h.isTwinMap.suit_mem honw
      have hS := hboth _ honw'
      have hRHS : S.heights (ρ (Card.mk (ρ q).suit m)).suit > q.rank.toIdx - 1 := by omega
      have keyw := h.stacked_self (Card.mk (ρ q).suit m) honw
      rw [show (Card.mk (ρ q).suit m).rank.toIdx = m.toIdx from rfl, hm] at keyw
      have hfalse := keyw.mpr hRHS
      rw [show (Card.mk (ρ q).suit m).suit = (ρ q).suit from rfl] at hfalse
      clear keyw
      omega
    omega

/-- The CROSS-CORRESPONDENCE: the twin core plus the stranded-card
bookkeeping.  After a growth the mirror's board differs from the
ρ-conjugation of the source's at the crossed pair's two seats: the
STRANDED card `x` (the ρ-image of the source's just-stacked card,
still seated in the mirror at its old seat) and the WANTED seat (the
ρ-image of the partner's seat, empty in the mirror — `top_wanted`).
The frame collects the stranded cards into the list `X` and states
the board correspondence with per-clause escapes at exactly those
cards:

* `vis_iff` — the card-set correspondence is GLOBAL: a crossing swaps
  the two members of a twin pair between the games, and each board
  holds one member, so the ρ-images of the seated cards coincide;
* `top_some` — the seat conjugation at every base whose source card
  is not a PARTNER (`c ∉ X.map ρ`, the escape);
* `top_none` — the free-side conjugation away from the stranded cards'
  own seats (the escape);
* `above_strand` — the riders on a stranded card are the images of
  the riders on its partner;
* `above_sub` — every mirror walk stays inside the image walk or
  inside a stranded card's column (the guard-transfer direction). -/
structure State.TwinCorrX (ρ : Card → Card) (σ : Suit) (S M : State) (X : List Card) : Prop where
  /-- the fields-and-heights half, verbatim. -/
  core : State.TwinCore ρ σ S M
  /-- the stranded cards sit on the mirror's board. -/
  strand_vis : ∀ x ∈ X, M.isVis x = true
  /-- the card-set correspondence is global. -/
  vis_iff : ∀ c, M.isVis c = S.isVis (ρ c)
  /-- the seat conjugation, occupied side: away from the partners. -/
  top_some : ∀ b c, S.board.topOf b = some c → c ∉ X.map ρ →
    M.board.topOf (Base.relabel ρ b) = some (ρ c)
  /-- the seat conjugation, free side: away from the stranded seats. -/
  top_none : ∀ b, S.board.topOf b = none →
    (∀ x ∈ X, M.board.bottomOf x ≠ some (Base.relabel ρ b)) →
    M.board.topOf (Base.relabel ρ b) = none
  /-- each crossing's wanted seat is free in the mirror. -/
  top_wanted : ∀ x ∈ X, ∀ b', S.board.bottomOf (ρ x) = some b' →
    M.board.topOf (Base.relabel ρ b') = none
  /-- the riders on a stranded card are the images of the riders on its partner. -/
  above_strand : ∀ x ∈ X, M.board.aboveOf x = (S.board.aboveOf (ρ x)).map ρ
  /-- every mirror walk stays inside the image walk, inside a stranded
  card, or inside a stranded card's column (the guard-transfer
  direction; the middle disjunct: a growth leaves its stranded card
  seated mid-run, where the image walk cannot see it). -/
  above_sub : ∀ c d, d ∈ M.board.aboveOf c →
    d ∈ (S.board.aboveOf (ρ c)).map ρ ∨ d ∈ X ∨ ∃ x ∈ X, d ∈ M.board.aboveOf x

namespace State.TwinCorr

/-- The full correspondence is the empty-crossing frame (every escape
is vacuous). -/
theorem toTwinCorrX {ρ σ S M} (h : State.TwinCorr ρ σ S M) :
    State.TwinCorrX ρ σ S M [] where
  core := h.toTwinCore
  strand_vis := fun x hx => absurd hx (by simp)
  vis_iff := by
    intro c
    have h1 := State.isVis_relabel h.isTwinMap h.board_mapByRho (ρ c)
    rw [h.isTwinMap.invol c] at h1
    exact h1
  top_some := by
    intro b c hb _
    have h1 := h.board_eq (Base.relabel ρ b)
    rw [Base.relabel_invol h.isTwinMap b] at h1
    rw [h1, hb, Option.map_some]
  top_none := by
    intro b hb _
    have h1 := h.board_eq (Base.relabel ρ b)
    rw [Base.relabel_invol h.isTwinMap b] at h1
    rw [h1, hb]
    rfl
  top_wanted := fun x hx _ => absurd hx (by simp)
  above_strand := fun x hx => absurd hx (by simp)
  above_sub := by
    intro c d hd
    left
    have h1 := Board.mapByRho_aboveOf h.isTwinMap S.board (ρ c)
    rw [h.isTwinMap.invol c, ← h.board_mapByRho] at h1
    rw [h1] at hd
    exact hd

end State.TwinCorr

/-- Every walk member is seated: the walk only collects cards read off
some seat, and the matching's round trip seats them. -/
theorem Board.aboveOf_go_seated {bd : Board} :
    ∀ (n : Nat) (b : Base) (acc : List Card),
      (∀ z ∈ acc, ∃ b₀, bd.topOf b₀ = some z) →
      ∀ d ∈ Board.aboveOf.go bd n b acc, ∃ b₀, bd.topOf b₀ = some d := by
  intro n
  induction n with
  | zero => intro b acc hacc d hd; exact hacc d hd
  | succ m ih =>
      intro b acc hacc d hd
      rw [Board.aboveOf_go_succ] at hd
      cases ht : bd.topOf b with
      | none => rw [ht] at hd; exact hacc d hd
      | some c' =>
          rw [ht] at hd
          have hd' : d ∈ (if acc.contains c' = true then acc
            else aboveOf.go bd m (Sum.inr c') (c' :: acc)) := hd
          by_cases hcon : acc.contains c' = true
          · rw [if_pos hcon] at hd'; exact hacc d hd'
          · rw [if_neg hcon] at hd'
            refine ih (Sum.inr c') (c' :: acc) ?_ d hd'
            intro z hz
            rcases List.mem_cons.mp hz with rfl | hz'
            · exact ⟨b, ht⟩
            · exact hacc z hz'

/-- The `aboveOf`-level form: every run member is seated. -/
theorem Board.mem_aboveOf_seated {bd : Board} {c d : Card}
    (h : d ∈ bd.aboveOf c) : ∃ b₀, bd.topOf b₀ = some d :=
  Board.aboveOf_go_seated 52 (Sum.inr c) [] (by simp) d h

namespace State.TwinCorrX

/-- **The catch-up drain** (the crossing's resolution): when the source
stacks the PARTNER of a crossed pair — the on-board twin `q` of the
mirror's stranded card `ρ q` — the mirror stacks the stranded card
itself, and the crossing DRAINS.  The rung is DERIVED (the catch-up
alignment `TwinCore.rung_of_skew`: the partner's own rung is exact and
the other twin rung at or above the rank); the bareness of the
stranded card rides the stranded-rider field (its riders are the
images of the partner's riders, and the partner is bare by the source
guard); and the frame is restored at the filtered list — the two
vacated seats, each side of the crossing, are exactly the seats the
correspondence wants empty, so both the wanted seat and the stranded
seat read `none` afterwards. -/
theorem apply_pileStack_catchup {ρ σ S M X R q}
    (h : State.TwinCorrX ρ σ S M X)
    (hon : q.suit = σ ∨ q.suit = σ.flipPair)
    (hX : ρ q ∈ X)
    (hS : S.apply (Move.pileStack q) = some R)
    (hskew : q.rank.toIdx ≤ S.heights (Card.flipSuit q).suit) :
    ∃ N, M.apply (Move.pileStack (ρ q)) = some N ∧
      State.TwinCorrX ρ σ R N (X.filter (fun c => c != ρ q)) := by
  obtain ⟨htop, bq, hbot, hrk, rfl⟩ := apply_pileStack_iff.mp hS
  have hrung : M.heights (ρ q).suit = q.rank.toIdx :=
    h.core.rung_of_skew hon hrk.symm hskew
  have htopS : S.board.topOf bq = some q := (Board.bottomOf_eq S.board q bq).mp hbot
  have hinvolq : ρ (ρ q) = q := h.core.isTwinMap.invol q
  have honρ : (ρ q).suit = σ ∨ (ρ q).suit = σ.flipPair :=
    h.core.isTwinMap.suit_mem hon
  -- the stranded card is bare: its riders are the images of the partner's
  have hbareM : M.board.topOf (Sum.inr (ρ q)) = none := by
    have h1 : M.board.aboveOf (ρ q) = (S.board.aboveOf (ρ (ρ q))).map ρ :=
      h.above_strand (ρ q) hX
    rw [hinvolq, Board.aboveOf_step_none htop] at h1
    cases hval : M.board.topOf (Sum.inr (ρ q)) with
    | none => rfl
    | some e =>
        have hmem : e ∈ M.board.aboveOf (ρ q) := Board.mem_aboveOf_of_topOf hval
        rw [h1] at hmem
        exact absurd hmem (by simp)
  -- the stranded card's seat in the mirror
  have hβ : ∃ β, M.board.bottomOf (ρ q) = some β := by
    have h1 := h.strand_vis (ρ q) hX
    rw [State.isVis] at h1
    cases hb : M.board.bottomOf (ρ q) with
    | none => rw [hb] at h1; exact absurd h1 (by simp)
    | some β => exact ⟨β, rfl⟩
  obtain ⟨β, hbβ⟩ := hβ
  have htopβ : M.board.topOf β = some (ρ q) := (Board.bottomOf_eq _ _ _).mp hbβ
  -- the mirror's firing
  have hrkM : (ρ q).rank.toIdx = M.heights (ρ q).suit := by
    rw [Card.IsTwinMap.rank h.core.isTwinMap q, hrung]
  refine ⟨{M with
      board := M.board.detach β,
      heights := fun s => if s = (ρ q).suit then M.heights s + 1 else M.heights s},
    apply_pileStack_iff.mpr ⟨hbareM, β, hbβ, hrkM, rfl⟩, ?_⟩
  -- the seat bookkeeping
  have hRtop : ∀ b : Base, b ≠ bq → (S.board.detach bq).topOf b = S.board.topOf b :=
    fun b hbq => Board.detach_topOf_ne S.board bq b hbq
  have hNtop : ∀ b : Base, b ≠ β →
      (M.board.detach β).topOf b = M.board.topOf b :=
    fun b hb => Board.detach_topOf_ne M.board β b hb
  have hseatM : ∀ c : Card, c ≠ ρ q →
      ((M.board.detach β).bottomOf c).isSome = (M.board.bottomOf c).isSome := by
    intro c hcq
    cases hb : M.board.bottomOf c with
    | none =>
        rw [Board.bottomOf_detach_of_none hb]
    | some β' =>
        have hβ' : β' ≠ β := by
          intro hcon
          subst hcon
          have h1 : M.board.topOf β' = some c := (Board.bottomOf_eq _ _ _).mp hb
          exact absurd (Option.some.inj (h1.symm.trans htopβ)) hcq
        rw [Board.bottomOf_detach_ne hb hβ']
  have hseatS : ∀ c : Card, c ≠ q →
      ((S.board.detach bq).bottomOf c).isSome = (S.board.bottomOf c).isSome := by
    intro c hcq
    cases hb : S.board.bottomOf c with
    | none =>
        rw [Board.bottomOf_detach_of_none hb]
    | some b' =>
        have hb' : b' ≠ bq := by
          intro hcon
          subst hcon
          have h1 : S.board.topOf b' = some c := (Board.bottomOf_eq _ _ _).mp hb
          exact absurd (Option.some.inj (h1.symm.trans htopS)) hcq
        rw [Board.bottomOf_detach_ne hb hb']
  refine ⟨⟨h.core.isTwinMap, h.core.fixes_off, h.core.deal_eq, h.core.depths_eq,
    h.core.stock_eq, h.core.step_eq, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs1 hs2
    have h1 : s ≠ (ρ q).suit := by
      rcases honρ with hs | hs
      · intro hcon; exact hs1 (hcon ▸ hs)
      · intro hcon; exact hs2 (hcon ▸ hs)
    have h2 : s ≠ q.suit := by
      rcases hon with hs | hs
      · intro hcon; exact hs1 (hcon ▸ hs)
      · intro hcon; exact hs2 (hcon ▸ hs)
    show (if s = (ρ q).suit then M.heights s + 1 else M.heights s)
      = (if s = q.suit then S.heights s + 1 else S.heights s)
    rw [if_neg h1, if_neg h2]
    exact h.core.heights_off s hs1 hs2
  · intro c' hon'
    by_cases hcq : c' = q
    · rw [hcq]
      constructor
      · intro _
        show (if q.suit = q.suit then S.heights q.suit + 1 else S.heights q.suit)
          > q.rank.toIdx
        rw [if_pos rfl]
        omega
      · intro _
        show (if (ρ q).suit = (ρ q).suit then M.heights (ρ q).suit + 1
            else M.heights (ρ q).suit) > (ρ q).rank.toIdx
        rw [if_pos rfl, Card.IsTwinMap.rank h.core.isTwinMap q, hrung]
        omega
    · by_cases hcq' : c' = Card.flipSuit q
      · rw [hcq']
        have hfs : (Card.flipSuit q).suit ≠ q.suit := by
          show q.suit.flipPair ≠ q.suit
          exact Suit.flipPair_ne q.suit
        have hfsρ : (ρ (Card.flipSuit q)).suit ≠ (ρ q).suit := by
          rw [h.core.isTwinMap.flip_comm q, Card.flipSuit_suit]
          exact Suit.flipPair_ne (ρ q).suit
        have honf : (Card.flipSuit q).suit = σ ∨ (Card.flipSuit q).suit = σ.flipPair := by
          show q.suit.flipPair = σ ∨ q.suit.flipPair = σ.flipPair
          rcases hon with hs | hs
          · rw [hs]; exact Or.inr rfl
          · rw [hs]; exact Or.inl (Suit.flipPair_flipPair σ)
        show (if (ρ (Card.flipSuit q)).suit = (ρ q).suit
            then M.heights (ρ (Card.flipSuit q)).suit + 1
            else M.heights (ρ (Card.flipSuit q)).suit) > (ρ (Card.flipSuit q)).rank.toIdx
          ↔ (if (Card.flipSuit q).suit = q.suit then S.heights (Card.flipSuit q).suit + 1
            else S.heights (Card.flipSuit q).suit) > (Card.flipSuit q).rank.toIdx
        rw [if_neg hfsρ, if_neg hfs, Card.flipSuit_rank q]
        exact h.core.stacked_iff (Card.flipSuit q) honf
      · exact State.stacked_bump_aux
          (hS := S.heights) (hM := M.heights)
          (hS' := fun s => if s = q.suit then S.heights s + 1 else S.heights s)
          (hM' := fun s => if s = (ρ q).suit then M.heights s + 1 else M.heights s)
          (ρ := ρ) (ρn := ρ) (q := q) (w := ρ q)
          h.core.isTwinMap h.core.isTwinMap hon rfl (fun _ _ _ => rfl) h.core.stacked_iff
          hrk.symm hrung (fun _ => rfl) (fun _ => rfl) c' hcq hcq' hon'
  · intro x hx
    obtain ⟨hxX, hxne⟩ := List.mem_filter.mp hx
    have hxq : x ≠ ρ q := bne_iff_ne.mp hxne
    have h1 := h.strand_vis x hxX
    rw [State.isVis] at h1
    show ((M.board.detach β).bottomOf x).isSome = true
    cases hb : M.board.bottomOf x with
    | none => rw [hb] at h1; exact absurd h1 (by simp)
    | some β' =>
        have hβ' : β' ≠ β := by
          intro hcon
          subst hcon
          have h2 : M.board.topOf β' = some x := (Board.bottomOf_eq _ _ _).mp hb
          exact absurd (Option.some.inj (h2.symm.trans htopβ)) hxq
        rw [Board.bottomOf_detach_ne hb hβ']
        rfl
  · intro c
    show ((M.board.detach β).bottomOf c).isSome = ((S.board.detach bq).bottomOf (ρ c)).isSome
    by_cases hc : c = ρ q
    · subst hc
      rw [hinvolq, Board.bottomOf_detach_self htopβ, Board.bottomOf_detach_self htopS]
    · have hcq : ρ c ≠ q := fun hcon => hc (by
        have h2 : c = ρ (ρ c) := (h.core.isTwinMap.invol c).symm
        rw [hcon] at h2
        exact h2)
      rw [hseatM c hc, hseatS (ρ c) hcq]
      exact h.vis_iff c
  · intro b c hb hc
    have hbq : b ≠ bq := by
      intro hcon
      subst hcon
      rw [Board.detach_topOf] at hb
      exact absurd hb (by simp)
    have hcq : c ≠ q := by
      intro hcon
      have h1 : S.board.topOf b = some q := by
        rw [← hRtop b hbq, ← hcon]; exact hb
      exact hbq (S.board.inj b bq q h1 htopS)
    have hcX : c ∉ X.map ρ := by
      intro hmem
      obtain ⟨x, hxX, hx⟩ := List.mem_map.mp hmem
      by_cases hxq : x = ρ q
      · exact hcq (by rw [← hx, hxq, hinvolq])
      · exact hc (List.mem_map.mpr ⟨x, List.mem_filter.mpr ⟨hxX, bne_iff_ne.mpr hxq⟩, hx⟩)
    have hSb : S.board.topOf b = some c := by
      rw [← hRtop b hbq]; exact hb
    have hpre := h.top_some b c hSb hcX
    have hbβ : Base.relabel ρ b ≠ β := by
      intro hcon
      rw [hcon] at hpre
      exact absurd (h.core.isTwinMap.inj (Option.some.inj (hpre.symm.trans htopβ))) hcq
    rw [hNtop _ hbβ]
    exact hpre
  · intro b hb hno
    by_cases hbq : b = bq
    · rw [hbq]
      have hwant := h.top_wanted (ρ q) hX bq (by rw [hinvolq]; exact hbot)
      have hbβ : Base.relabel ρ bq ≠ β := by
        intro hcon
        rw [hcon, htopβ] at hwant
        exact absurd hwant (by simp)
      rw [hNtop _ hbβ]
      exact hwant
    · have hSb : S.board.topOf b = none := by
        rw [← hRtop b hbq]; exact hb
      by_cases hesc : ∃ x ∈ X, M.board.bottomOf x = some (Base.relabel ρ b)
      · obtain ⟨x, hxX, hbx⟩ := hesc
        by_cases hxq : x = ρ q
        · subst hxq
          have hseat : Base.relabel ρ b = β :=
            M.board.inj (Base.relabel ρ b) β (ρ q)
              ((Board.bottomOf_eq _ _ _).mp hbx) ((Board.bottomOf_eq _ _ _).mp hbβ)
          subst hseat
          exact Board.detach_topOf _ _
        · have hβ' : Base.relabel ρ b ≠ β := by
            intro hcon
            have h1 : M.board.topOf (Base.relabel ρ b) = some x :=
              (Board.bottomOf_eq _ _ _).mp hbx
            rw [hcon] at h1
            exact absurd (Option.some.inj (h1.symm.trans htopβ)) hxq
          exact absurd (Board.bottomOf_detach_ne hbx hβ')
            (hno x (List.mem_filter.mpr ⟨hxX, bne_iff_ne.mpr hxq⟩))
      · have hall : ∀ x ∈ X, M.board.bottomOf x ≠ some (Base.relabel ρ b) :=
          fun x hxX hbx => hesc ⟨x, hxX, hbx⟩
        have hbβ : Base.relabel ρ b ≠ β := by
          intro hcon
          exact hall (ρ q) hX (by rw [hcon]; exact hbβ)
        rw [hNtop _ hbβ]
        exact h.top_none b hSb hall
  · intro x hx b' hb'
    obtain ⟨hxX, hxne⟩ := List.mem_filter.mp hx
    have hxq : x ≠ ρ q := bne_iff_ne.mp hxne
    have hcq : ρ x ≠ q := fun hcon => hxq (by
      have h2 : x = ρ (ρ x) := (h.core.isTwinMap.invol x).symm
      rw [hcon] at h2
      exact h2)
    have hb'q : b' ≠ bq := by
      intro hcon
      subst hcon
      have h2 : (S.board.detach b').topOf b' = some (ρ x) := (Board.bottomOf_eq _ _ _).mp hb'
      rw [Board.detach_topOf] at h2
      exact absurd h2 (by simp)
    have hSseat : S.board.bottomOf (ρ x) = some b' := by
      have h1 : (S.board.detach bq).topOf b' = some (ρ x) := (Board.bottomOf_eq _ _ _).mp hb'
      rw [hRtop b' hb'q] at h1
      exact (Board.bottomOf_eq _ _ _).mpr h1
    have hpre := h.top_wanted x hxX b' hSseat
    have hbβ : Base.relabel ρ b' ≠ β := by
      intro hcon
      rw [hcon, htopβ] at hpre
      exact absurd hpre (by simp)
    rw [hNtop _ hbβ]
    exact hpre
  · intro x hx
    obtain ⟨hxX, hxne⟩ := List.mem_filter.mp hx
    rw [Board.aboveOf_detach_filter htopβ hbareM,
      h.above_strand x hxX,
      ← map_filter_ne (l := S.board.aboveOf (ρ x)) (x := q) h.core.isTwinMap.inj,
      ← Board.aboveOf_detach_filter htopS htop]
  · intro c d hd
    have hsub : d ∈ M.board.aboveOf c :=
      Board.aboveOf_sub (bd' := M.board.detach β) (bd := M.board) (fun b => by
        by_cases hbb : b = β
        · subst hbb; rw [Board.detach_topOf]; exact Or.inl rfl
        · rw [hNtop b hbb]; exact Or.inr rfl) d hd
    have hdne : d ≠ ρ q := by
      intro hcon
      subst hcon
      obtain ⟨b₀, hb₀⟩ := Board.mem_aboveOf_seated hd
      by_cases hbb : b₀ = β
      · subst hbb
        rw [Board.detach_topOf] at hb₀
        exact absurd hb₀ (by simp)
      · rw [hNtop b₀ hbb] at hb₀
        exact absurd (M.board.inj b₀ β (ρ q) hb₀ htopβ) hbb
    rcases h.above_sub c d hsub with hm | hdX | ⟨x, hxX, hx⟩
    · left
      obtain ⟨y, hymem, hyy⟩ := List.mem_map.mp hm
      have hyq : y ≠ q := fun hcon => hdne (by rw [← hyy, hcon])
      show d ∈ ((S.board.detach bq).aboveOf (ρ c)).map ρ
      rw [Board.aboveOf_detach_filter htopS htop]
      exact List.mem_map.mpr ⟨y, List.mem_filter.mpr ⟨hymem, bne_iff_ne.mpr hyq⟩, hyy⟩
    · refine Or.inr (Or.inl ?_)
      show d ∈ List.filter (fun c => c != ρ q) X
      exact List.mem_filter.mpr ⟨hdX, bne_iff_ne.mpr hdne⟩
    · have hxq : x ≠ ρ q := by
        intro hcon
        subst hcon
        rw [h.above_strand (ρ q) hX, h.core.isTwinMap.invol q,
          Board.aboveOf_step_none htop] at hx
        exact absurd hx (by simp)
      refine Or.inr (Or.inr ⟨x, List.mem_filter.mpr ⟨hxX, bne_iff_ne.mpr hxq⟩, ?_⟩)
      rw [Board.aboveOf_detach_filter htopβ hbareM]
      exact List.mem_filter.mpr ⟨hx, bne_iff_ne.mpr hdne⟩
end State.TwinCorrX

/-- **The growth's frame packaging** (Residual 1's entry point): a
misaligned on-suit stacking whose twin is visible and bare grows the
correspondence to `ρ' = τ_{ρ q} ∘ ρ` AND enters the crossed-set frame
with the single stranded card `ρ q` — the growth lemma's conclusion
(the core at the grown map, the board conjugation away from the four
crossed seats, the stranded card at its old seat-image, the vacated
twin-seat) repackaged as the frame's clauses.

The corner-freedom premises (`hcbq`, `hcbq'`): the moved pair is not
deal-adjacent to itself — neither `q` nor its twin sits directly on
the other's base — so the four excluded seats are exactly the two
crossed base-seats and the two bare card-seats, and every clause's
escape is one of them. -/
theorem State.TwinCorr.apply_pileStack_grow_X {ρ σ S M R q bq bq' ρ'}
    (h : State.TwinCorr ρ σ S M)
    (hon : q.suit = σ ∨ q.suit = σ.flipPair)
    (hS : S.apply (Move.pileStack q) = some R)
    (hbq : S.board.bottomOf q = some bq)
    (hbq' : S.board.bottomOf (Card.flipSuit q) = some bq')
    (hflip : S.board.topOf (Sum.inr (Card.flipSuit q)) = none)
    (hmis : M.heights (ρ q).suit ≠ q.rank.toIdx)
    (hcbq : bq ≠ Sum.inr q ∧ bq ≠ Sum.inr (Card.flipSuit q))
    (hcbq' : bq' ≠ Sum.inr q ∧ bq' ≠ Sum.inr (Card.flipSuit q))
    (hcomp : ρ' = Card.swapTwin (ρ q) ∘ ρ) :
    ∃ N, M.apply (Move.pileStack (Card.flipSuit (ρ q))) = some N ∧
      State.TwinCorrX ρ' σ R N [ρ q] := by
  obtain ⟨N, hfire, hcore', hboard, hstrand, hvacant⟩ :=
    State.TwinCorr.apply_pileStack_grow h hon hS hbq hbq' hflip hmis
  refine ⟨N, hfire, ?_⟩
  rw [← hcomp] at hcore' hboard
  -- ===== the pair identities =====
  have hq : ρ q = q ∨ ρ q = Card.flipSuit q := h.core.isTwinMap.pair q
  have hfl : Card.flipSuit (ρ q) = q ∨ Card.flipSuit (ρ q) = Card.flipSuit q := by
    rcases hq with hq0 | hq0
    · exact Or.inr (by rw [hq0])
    · exact Or.inl (by rw [hq0, Card.flipSuit_flipSuit q])
  have hρ'q : ρ' q = Card.flipSuit (ρ q) := by
    rw [hcomp]
    show Card.swapTwin (ρ q) (ρ q) = Card.flipSuit (ρ q)
    exact Card.swapTwin_self_left _
  have hρ'q' : ρ' (Card.flipSuit q) = ρ q := by
    rw [hcomp]
    show Card.swapTwin (ρ q) (ρ (Card.flipSuit q)) = ρ q
    rw [h.core.isTwinMap.flip_comm q, Card.swapTwin_self_right]
  have hρ'pq : ρ' (ρ q) = Card.flipSuit q := by
    rw [hcomp]
    show Card.swapTwin (ρ q) (ρ (ρ q)) = Card.flipSuit q
    rw [h.core.isTwinMap.invol q]
    rcases hq with hq0 | hq0
    · rw [hq0, Card.swapTwin_self_left]
    · rw [hq0]
      have h1 : q = Card.flipSuit (Card.flipSuit q) := (Card.flipSuit_flipSuit q).symm
      have h2 : Card.swapTwin (Card.flipSuit q) q = Card.flipSuit q := by
        unfold Card.swapTwin
        rw [if_neg (fun hcon => Card.flipSuit_ne q hcon.symm), if_pos h1]
      rw [h2]
  have hρ'fix : ∀ c, c ≠ q → c ≠ Card.flipSuit q → ρ' c = ρ c := by
    intro c h1 h2
    rw [hcomp]
    show Card.swapTwin (ρ q) (ρ c) = ρ c
    refine Card.swapTwin_of_ne ?_ ?_
    · exact fun hcon => h1 (h.core.isTwinMap.inj hcon)
    · rw [← h.core.isTwinMap.flip_comm q]
      exact fun hcon => h2 (h.core.isTwinMap.inj hcon)
  have hneR : ∀ c, c ≠ q → c ≠ Card.flipSuit q → ρ c ≠ q := by
    intro c h1 h2 hcon
    have h3 : c = ρ q := by
      rw [← h.core.isTwinMap.invol c, hcon]
    rcases hq with hq0 | hq0
    · exact h1 (h3.trans hq0)
    · exact h2 (h3.trans hq0)
  have hneF : ∀ c, c ≠ q → c ≠ Card.flipSuit q → c ≠ Card.flipSuit (ρ q) := by
    intro c h1 h2 hcon
    rcases hfl with hf0 | hf0
    · exact h1 (hcon.trans hf0)
    · exact h2 (hcon.trans hf0)
  -- ===== the function identities =====
  have hrr : ∀ b : Base, Base.relabel ρ (Base.relabel ρ' b) = Base.swapTwin (ρ q) b := by
    intro b
    have h1 : ρ ∘ ρ' = Card.swapTwin (ρ q) := by
      rw [hcomp]
      funext c
      show ρ (Card.swapTwin (ρ q) (ρ c)) = Card.swapTwin (ρ q) c
      rw [h.core.isTwinMap.comm (Card.IsTwinMap.swapTwin (ρ q)) (ρ c),
        h.core.isTwinMap.invol c]
    rw [← Base.relabel_comp, h1, Base.relabel_swapTwin]
  have hrr2 : ∀ b : Base, Base.relabel ρ' (Base.relabel ρ b) = Base.swapTwin (ρ q) b := by
    intro b
    have h1 : ρ' ∘ ρ = Card.swapTwin (ρ q) := by
      rw [hcomp]
      funext c
      show Card.swapTwin (ρ q) (ρ (ρ c)) = Card.swapTwin (ρ q) c
      rw [h.core.isTwinMap.invol c]
    rw [← Base.relabel_comp, h1, Base.relabel_swapTwin]
  -- ===== the seat facts =====
  have htopS : S.board.topOf bq = some q := (Board.bottomOf_eq S.board q bq).mp hbq
  have htopS' : S.board.topOf bq' = some (Card.flipSuit q) :=
    (Board.bottomOf_eq S.board (Card.flipSuit q) bq').mp hbq'
  have htop : S.board.topOf (Sum.inr q) = none := (apply_pileStack_iff.mp hS).1
  have hbqne : bq ≠ bq' := by
    intro hcon
    rw [hcon] at htopS
    exact Card.flipSuit_ne q (Option.some.inj (htopS.symm.trans htopS')).symm
  obtain ⟨-, b₀, hbot₀, -, hRdef⟩ := apply_pileStack_iff.mp hS
  have hb₀ : b₀ = bq :=
    S.board.inj b₀ bq q ((Board.bottomOf_eq S.board q b₀).mp hbot₀) htopS
  have hRb : R.board = S.board.detach bq := by rw [hRdef, hb₀]
  obtain ⟨-, βN, hbotN, -, hNdef⟩ := apply_pileStack_iff.mp hfire
  have hβN : βN = Base.relabel ρ bq' := by
    have h1 : M.board.bottomOf (Card.flipSuit (ρ q)) = some (Base.relabel ρ bq') := by
      rw [h.board_mapByRho, ← h.core.isTwinMap.flip_comm q, Board.mapByRho_bottomOf,
        hbq', Option.map_some]
    exact Option.some.inj (hbotN.symm.trans h1)
  have hNb : N.board = M.board.detach (Base.relabel ρ bq') := by rw [hNdef, hβN]
  -- ===== the corner facts (the moved pair is not deal-adjacent to itself) =====
  have hbqρ : bq ≠ Sum.inr (ρ q) ∧ bq ≠ Sum.inr (Card.flipSuit (ρ q)) := by
    rcases hq with hq0 | hq0
    · rw [hq0]; exact ⟨hcbq.1, hcbq.2⟩
    · rw [hq0]
      refine ⟨hcbq.2, ?_⟩
      rw [Card.flipSuit_flipSuit q]
      exact hcbq.1
  have hbq'ρ : bq' ≠ Sum.inr (ρ q) ∧ bq' ≠ Sum.inr (Card.flipSuit (ρ q)) := by
    rcases hq with hq0 | hq0
    · rw [hq0]; exact ⟨hcbq'.1, hcbq'.2⟩
    · rw [hq0]
      refine ⟨hcbq'.2, ?_⟩
      rw [Card.flipSuit_flipSuit q]
      exact hcbq'.1
  have hbqfix : Base.swapTwin (ρ q) bq = bq :=
    Base.swapTwin_eq_self hbqρ.1 hbqρ.2
  have hbq'fix : Base.swapTwin (ρ q) bq' = bq' :=
    Base.swapTwin_eq_self hbq'ρ.1 hbq'ρ.2
  have hseatin : ∀ b' : Base, ∀ d : Card, Base.relabel ρ b' = Sum.inr d → b' = Sum.inr (ρ d) := by
    intro b' d hcon
    have h2 := congrArg (Base.relabel ρ) hcon
    rw [Base.relabel_invol h.core.isTwinMap b'] at h2
    exact h2
  have hmemsq : Card.swapTwin (ρ q) q = q ∨ Card.swapTwin (ρ q) q = Card.flipSuit q := by
    rcases Card.swapTwin_cases (ρ q) q with hc | hc | hc
    · rcases hq with hq0 | hq0
      · rw [hc, hq0]; exact Or.inl rfl
      · rw [hc, hq0]; exact Or.inr rfl
    · rcases hfl with hf0 | hf0
      · rw [hc, hf0]; exact Or.inl rfl
      · rw [hc, hf0]; exact Or.inr rfl
    · exact Or.inl hc
  have hmemsq' : Card.swapTwin (ρ q) (Card.flipSuit q) = q ∨
      Card.swapTwin (ρ q) (Card.flipSuit q) = Card.flipSuit q := by
    rcases Card.swapTwin_cases (ρ q) (Card.flipSuit q) with hc | hc | hc
    · rcases hq with hq0 | hq0
      · rw [hc, hq0]; exact Or.inl rfl
      · rw [hc, hq0]; exact Or.inr rfl
    · rcases hfl with hf0 | hf0
      · rw [hc, hf0]; exact Or.inl rfl
      · rw [hc, hf0]; exact Or.inr rfl
    · exact Or.inr hc
  -- ===== the bare card-seats stay bare =====
  have hnnR : ∀ y, y = q ∨ y = Card.flipSuit q → R.board.topOf (Sum.inr y) = none := by
    intro y hy
    rcases hy with rfl | rfl
    · rw [hRb, Board.detach_topOf_ne _ _ _ (Ne.symm hcbq.1)]
      exact htop
    · rw [hRb, Board.detach_topOf_ne _ _ _ (Ne.symm hcbq.2)]
      exact hflip
  have hnnN : ∀ y, y = q ∨ y = Card.flipSuit q → N.board.topOf (Sum.inr y) = none := by
    intro y hy
    have hc1 : Sum.inr y ≠ Base.relabel ρ bq' := by
      intro hcon
      have h2 := hseatin _ _ hcon.symm
      rcases hy with rfl | rfl
      · exact hbq'ρ.1 h2
      · rw [h.core.isTwinMap.flip_comm q] at h2
        exact hbq'ρ.2 h2
    rw [hNb, Board.detach_topOf_ne _ _ _ hc1, h.board_eq]
    show (S.board.topOf (Base.relabel ρ (Sum.inr y))).map ρ = none
    rw [Base.relabel_inr]
    rcases hy with rfl | rfl
    · rcases hq with hq0 | hq0
      · rw [hq0, htop]; rfl
      · rw [hq0, hflip]; rfl
    · rw [h.core.isTwinMap.flip_comm q]
      rcases hfl with hf0 | hf0
      · rw [hf0, htop]; rfl
      · rw [hf0, hflip]; rfl
  -- ===== the seatedness transfers =====
  have hRunseat : R.board.bottomOf q = none := by
    rw [hRb]
    exact Board.bottomOf_detach_self htopS
  have hMunseat : M.board.topOf (Base.relabel ρ bq') = some (Card.flipSuit (ρ q)) := by
    have h1 : M.board.bottomOf (Card.flipSuit (ρ q)) = some (Base.relabel ρ bq') :=
      hbotN.trans (congrArg some hβN)
    exact (Board.bottomOf_eq M.board (Card.flipSuit (ρ q)) (Base.relabel ρ bq')).mp h1
  have hVisN : ∀ c, c ≠ Card.flipSuit (ρ q) → N.isVis c = M.isVis c := by
    intro c hc
    show (N.board.bottomOf c).isSome = (M.board.bottomOf c).isSome
    rw [hNb]
    exact Board.isVis_detach_eq hMunseat hc
  have hVisR : ∀ c, c ≠ q → R.isVis c = S.isVis c := by
    intro c hc
    show (R.board.bottomOf c).isSome = (S.board.bottomOf c).isSome
    rw [hRb]
    exact Board.isVis_detach_eq htopS hc
  have hvisM : ∀ c, M.isVis c = S.isVis (ρ c) := h.toTwinCorrX.vis_iff
  have hVisS : S.isVis q = true := by
    show (S.board.bottomOf q).isSome = true
    rw [hbq]
    rfl
  have hVisS' : S.isVis (Card.flipSuit q) = true := by
    show (S.board.bottomOf (Card.flipSuit q)).isSome = true
    rw [hbq']
    rfl
  have hwalkM : ∀ c, M.board.aboveOf c = (S.board.aboveOf (ρ c)).map ρ := by
    intro c
    have h1 := Board.mapByRho_aboveOf h.core.isTwinMap S.board (ρ c)
    rw [h.core.isTwinMap.invol c, ← h.board_mapByRho] at h1
    exact h1
  -- ===== the frame's fields =====
  refine ⟨hcore', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain rfl := List.mem_singleton.mp hx
    show (N.board.bottomOf (ρ q)).isSome = true
    rw [(Board.bottomOf_eq N.board (ρ q) (Base.relabel ρ bq)).mpr hstrand]
    rfl
  · intro c
    rcases hq with hq0 | hq0
    · -- ALIGNED (ρ q = q): the mirror stacked q'; ρ' swaps the pair
      have hρ'q2 : ρ' q = Card.flipSuit q := by rw [hρ'q, hq0]
      have hρ'q'2 : ρ' (Card.flipSuit q) = q := by rw [hρ'q', hq0]
      have hflρ : Card.flipSuit (ρ q) = Card.flipSuit q := by rw [hq0]
      have hNq' : N.board.bottomOf (Card.flipSuit q) = none := by
        rw [show Card.flipSuit q = Card.flipSuit (ρ q) from hflρ.symm, hNb]
        exact Board.bottomOf_detach_self hMunseat
      by_cases hcq : c = q
      · rw [hcq, hρ'q2, hVisN q (by rw [hflρ]; exact Ne.symm (Card.flipSuit_ne q)), hvisM q, hq0,
          hVisR (Card.flipSuit q) (Card.flipSuit_ne q), hVisS, hVisS']
      · by_cases hcq' : c = Card.flipSuit q
        · rw [hcq', hρ'q'2]
          show (N.board.bottomOf (Card.flipSuit q)).isSome = (R.board.bottomOf q).isSome
          rw [hNq', hRunseat]
        · rw [hρ'fix c hcq hcq', hVisN c (hneF c hcq hcq'), hvisM c,
            hVisR (ρ c) (hneR c hcq hcq')]
    · -- SWAPPED (ρ q = q'): the mirror stacked q itself; ρ' fixes the pair
      have hρ'q2 : ρ' q = q := by rw [hρ'q, hq0, Card.flipSuit_flipSuit q]
      have hρ'q'2 : ρ' (Card.flipSuit q) = Card.flipSuit q := by rw [hρ'q', hq0]
      have hflρ : Card.flipSuit (ρ q) = q := by rw [hq0, Card.flipSuit_flipSuit q]
      have hNq : N.board.bottomOf q = none := by
        rw [show q = Card.flipSuit (ρ q) from hflρ.symm, hNb]
        exact Board.bottomOf_detach_self hMunseat
      by_cases hcq : c = q
      · rw [hcq, hρ'q2]
        show (N.board.bottomOf q).isSome = (R.board.bottomOf q).isSome
        rw [hNq, hRunseat]
      · by_cases hcq' : c = Card.flipSuit q
        · rw [hcq', hρ'q'2, hVisN (Card.flipSuit q) (by rw [hflρ]; exact Card.flipSuit_ne q),
            hvisM (Card.flipSuit q), h.core.isTwinMap.flip_comm q, hflρ,
            hVisR (Card.flipSuit q) (Card.flipSuit_ne q), hVisS, hVisS']
        · rw [hρ'fix c hcq hcq', hVisN c (hneF c hcq hcq'), hvisM c,
            hVisR (ρ c) (hneR c hcq hcq')]
  · intro b c hb hc
    have hcq : c ≠ Card.flipSuit q := by
      intro hcon
      refine hc ?_
      show c ∈ [ρ' (ρ q)]
      rw [hρ'pq, hcon]
      exact List.mem_singleton_self _
    have hbq0 : b ≠ bq := by
      intro hcon
      rw [hcon] at hb
      rw [hRb, Board.detach_topOf] at hb
      exact absurd hb (by simp)
    have hE1 : Base.swapTwin (ρ q) b ≠ bq := by
      intro hcon
      have h2 := congrArg (Base.swapTwin (ρ q)) hcon
      rw [Base.swapTwin_swapTwin, hbqfix] at h2
      exact hbq0 h2
    have hE2 : Base.swapTwin (ρ q) b ≠ bq' := by
      intro hcon
      have h2 := congrArg (Base.swapTwin (ρ q)) hcon
      rw [Base.swapTwin_swapTwin, hbq'fix] at h2
      rw [h2] at hb
      rw [hRb, Board.detach_topOf_ne _ _ _ (Ne.symm hbqne), htopS'] at hb
      exact hcq (Option.some.inj hb).symm
    have hE3 : Base.swapTwin (ρ q) b ≠ Sum.inr q := by
      intro hcon
      have h2 := congrArg (Base.swapTwin (ρ q)) hcon
      rw [Base.swapTwin_swapTwin] at h2
      rw [h2, show Base.swapTwin (ρ q) (Sum.inr q) = Sum.inr (Card.swapTwin (ρ q) q) from rfl] at hb
      rcases hmemsq with hm | hm
      · rw [hm, hnnR q (Or.inl rfl)] at hb
        exact absurd hb (by simp)
      · rw [hm, hnnR (Card.flipSuit q) (Or.inr rfl)] at hb
        exact absurd hb (by simp)
    have hE4 : Base.swapTwin (ρ q) b ≠ Sum.inr (Card.flipSuit q) := by
      intro hcon
      have h2 := congrArg (Base.swapTwin (ρ q)) hcon
      rw [Base.swapTwin_swapTwin] at h2
      rw [h2, show Base.swapTwin (ρ q) (Sum.inr (Card.flipSuit q))
          = Sum.inr (Card.swapTwin (ρ q) (Card.flipSuit q)) from rfl] at hb
      rcases hmemsq' with hm | hm
      · rw [hm, hnnR q (Or.inl rfl)] at hb
        exact absurd hb (by simp)
      · rw [hm, hnnR (Card.flipSuit q) (Or.inr rfl)] at hb
        exact absurd hb (by simp)
    have hcl := hboard (Base.relabel ρ' b)
      (by rw [hrr]; exact hE1) (by rw [hrr]; exact hE2)
      (by rw [hrr]; exact hE3) (by rw [hrr]; exact hE4)
    rw [Base.relabel_invol hcore'.isTwinMap b, hb, Option.map_some] at hcl
    exact hcl
  · intro b hb hno
    have h5 : Base.relabel ρ' bq = Base.relabel ρ bq := by
      have h4 : Base.relabel ρ' (Base.relabel ρ' bq) = Base.relabel ρ' (Base.relabel ρ bq) := by
        rw [Base.relabel_invol hcore'.isTwinMap bq, hrr2 bq, hbqfix]
      exact Base.relabel_inj hcore'.isTwinMap h4
    have hbq0 : b ≠ bq := by
      intro hcon
      rw [hcon] at hno
      exact absurd (by
        show N.board.bottomOf (ρ q) = some (Base.relabel ρ' bq)
        rw [(Board.bottomOf_eq N.board (ρ q) (Base.relabel ρ bq)).mpr hstrand, h5])
        (hno (ρ q) (List.mem_singleton_self _))
    by_cases hE3 : Base.swapTwin (ρ q) b = Sum.inr q
    · have h2 := congrArg (Base.swapTwin (ρ q)) hE3
      rw [Base.swapTwin_swapTwin] at h2
      rw [h2]
      show N.board.topOf (Sum.inr (ρ' (Card.swapTwin (ρ q) q))) = none
      rcases hmemsq with hm | hm
      · rw [hm]
        exact hnnN (ρ' q) (by rw [hρ'q]; exact hfl)
      · rw [hm]
        exact hnnN (ρ' (Card.flipSuit q)) (by rw [hρ'q']; exact hq)
    by_cases hE4 : Base.swapTwin (ρ q) b = Sum.inr (Card.flipSuit q)
    · have h2 := congrArg (Base.swapTwin (ρ q)) hE4
      rw [Base.swapTwin_swapTwin] at h2
      rw [h2]
      show N.board.topOf (Sum.inr (ρ' (Card.swapTwin (ρ q) (Card.flipSuit q)))) = none
      rcases hmemsq' with hm | hm
      · rw [hm]
        exact hnnN (ρ' q) (by rw [hρ'q]; exact hfl)
      · rw [hm]
        exact hnnN (ρ' (Card.flipSuit q)) (by rw [hρ'q']; exact hq)
    have hE1 : Base.swapTwin (ρ q) b ≠ bq := by
      intro hcon
      have h2 := congrArg (Base.swapTwin (ρ q)) hcon
      rw [Base.swapTwin_swapTwin, hbqfix] at h2
      exact hbq0 h2
    have hE2 : Base.swapTwin (ρ q) b ≠ bq' := by
      intro hcon
      have h2 := congrArg (Base.swapTwin (ρ q)) hcon
      rw [Base.swapTwin_swapTwin, hbq'fix] at h2
      rw [h2] at hb
      rw [hRb, Board.detach_topOf_ne _ _ _ (Ne.symm hbqne), htopS'] at hb
      exact absurd hb (by simp)
    have hcl := hboard (Base.relabel ρ' b)
      (by rw [hrr]; exact hE1) (by rw [hrr]; exact hE2)
      (by rw [hrr]; exact hE3) (by rw [hrr]; exact hE4)
    rw [Base.relabel_invol hcore'.isTwinMap b, hb] at hcl
    exact hcl
  · intro x hx b' hb'
    obtain rfl := List.mem_singleton.mp hx
    rw [hρ'pq] at hb'
    have h1 : R.board.topOf b' = some (Card.flipSuit q) := (Board.bottomOf_eq _ _ _).mp hb'
    have h2 : R.board.topOf bq' = some (Card.flipSuit q) := by
      rw [hRb, Board.detach_topOf_ne _ _ _ (Ne.symm hbqne)]
      exact htopS'
    have hb'eq : b' = bq' := R.board.inj b' bq' (Card.flipSuit q) h1 h2
    have h5' : Base.relabel ρ' bq' = Base.relabel ρ bq' := by
      have h4 : Base.relabel ρ' (Base.relabel ρ' bq') = Base.relabel ρ' (Base.relabel ρ bq') := by
        rw [Base.relabel_invol hcore'.isTwinMap bq', hrr2 bq', hbq'fix]
      exact Base.relabel_inj hcore'.isTwinMap h4
    rw [hb'eq, h5']
    exact hvacant
  · intro x hx
    obtain rfl := List.mem_singleton.mp hx
    have hb1 : N.board.topOf (Sum.inr (ρ q)) = none := by
      rw [show ρ q = ρ' (Card.flipSuit q) from by rw [hρ'q']]
      exact hnnN (ρ' (Card.flipSuit q)) (by rw [hρ'q']; exact hq)
    rw [Board.aboveOf_step_none hb1, hρ'pq,
      Board.aboveOf_step_none (hnnR (Card.flipSuit q) (Or.inr rfl))]
    rfl
  · intro c d hd
    by_cases hcq : c = q
    · rw [hcq] at hd
      rw [Board.aboveOf_step_none (hnnN q (Or.inl rfl))] at hd
      exact absurd hd (by simp)
    by_cases hcq' : c = Card.flipSuit q
    · rw [hcq'] at hd
      rw [Board.aboveOf_step_none (hnnN (Card.flipSuit q) (Or.inr rfl))] at hd
      exact absurd hd (by simp)
    have hsub : d ∈ M.board.aboveOf c := by
      refine Board.aboveOf_sub (bd' := N.board) (bd := M.board) ?_ d hd
      intro b''
      by_cases hbb : b'' = Base.relabel ρ bq'
      · rw [hbb]
        exact Or.inl hvacant
      · rw [hNb]
        exact Or.inr (Board.detach_topOf_ne _ _ _ hbb)
    have hdM : d ∈ List.map ρ (S.board.aboveOf (ρ c)) := by
      rw [← hwalkM c]
      exact hsub
    obtain ⟨y, hymem, hyy⟩ := List.mem_map.mp hdM
    by_cases hy : y = q
    · right; left
      rw [← hyy, hy]
      exact List.mem_singleton_self _
    by_cases hy' : y = Card.flipSuit q
    · exfalso
      obtain ⟨b₀, hb₀⟩ := Board.mem_aboveOf_seated hd
      rw [← hyy, hy', h.core.isTwinMap.flip_comm q] at hb₀
      have hnone : N.board.bottomOf (Card.flipSuit (ρ q)) = none := by
        rw [hNb]
        exact Board.bottomOf_detach_self hMunseat
      rw [(Board.bottomOf_eq _ _ _).mpr hb₀] at hnone
      exact absurd hnone (by simp)
    · left
      have hyf : ρ' y = ρ y := hρ'fix y hy hy'
      have hyR : y ∈ R.board.aboveOf (ρ c) := by
        rw [hRb, Board.aboveOf_detach_filter htopS htop (ρ c)]
        exact List.mem_filter.mpr ⟨hymem, bne_iff_ne.mpr hy⟩
      rw [hρ'fix c hcq hcq', ← hyy, ← hyf]
      exact List.mem_map.mpr ⟨y, hyR, rfl⟩

/-- **The verbatim on-suit stacking in the frame** (the rung ALIGNED,
the card not stranded): the mirror stacks `ρ q` itself at its proper
seat, the correspondence and the crossing list both unchanged.  The
alignment premise is the rung arithmetic (`rung_of_skew` derives it
when the other twin rung is at or above the rank — the catch-up's
regime); the bareness premise is the card-seat shape condition (no
stranded card rides on `ρ q` — the frame's `top_none` at the card
seat, the L1 family). -/
theorem State.TwinCorrX.apply_pileStack_onsuit {ρ σ S M X R q}
    (h : State.TwinCorrX ρ σ S M X)
    (hon : q.suit = σ ∨ q.suit = σ.flipPair)
    (hS : S.apply (Move.pileStack q) = some R)
    (halign : M.heights (ρ q).suit = q.rank.toIdx)
    (hX : ρ q ∉ X)
    (hbare : ∀ x ∈ X, M.board.bottomOf x ≠ some (Sum.inr (ρ q))) :
    ∃ N, M.apply (Move.pileStack (ρ q)) = some N ∧ State.TwinCorrX ρ σ R N X := by
  obtain ⟨htop, bq, hbot, hrk, rfl⟩ := apply_pileStack_iff.mp hS
  have htopS : S.board.topOf bq = some q := (Board.bottomOf_eq S.board q bq).mp hbot
  -- ρ q sits at its PROPER seat (the correspondence's image of q's seat)
  have hqX : q ∉ X.map ρ := by
    intro hmem
    obtain ⟨x, hxX, hx⟩ := List.mem_map.mp hmem
    refine hX ?_
    have h2 : ρ q = x := (congrArg ρ hx.symm).trans (h.core.isTwinMap.invol x)
    rw [h2]
    exact hxX
  have hseat : M.board.topOf (Base.relabel ρ bq) = some (ρ q) :=
    h.top_some bq q htopS hqX
  have hbotM : M.board.bottomOf (ρ q) = some (Base.relabel ρ bq) :=
    (Board.bottomOf_eq M.board (ρ q) (Base.relabel ρ bq)).mpr hseat
  -- the mirror's firing guard (the card-seat transfer, the L1 premise)
  have hbareM : M.board.topOf (Sum.inr (ρ q)) = none := by
    have h1 := h.top_none (Sum.inr q) htop (fun x hxX hcon => hbare x hxX (by
      rw [Base.relabel_inr] at hcon
      exact hcon))
    rw [Base.relabel_inr ρ q] at h1
    exact h1
  have hrkM : (ρ q).rank.toIdx = M.heights (ρ q).suit := by
    rw [Card.IsTwinMap.rank h.core.isTwinMap q, halign]
  refine ⟨{M with
      board := M.board.detach (Base.relabel ρ bq),
      heights := fun s => if s = (ρ q).suit then M.heights s + 1 else M.heights s},
    apply_pileStack_iff.mpr ⟨hbareM, Base.relabel ρ bq, hbotM, hrkM, rfl⟩, ?_⟩
  -- the seat bookkeeping
  have hRtop : ∀ b : Base, b ≠ bq → (S.board.detach bq).topOf b = S.board.topOf b :=
    fun b hbq => Board.detach_topOf_ne S.board bq b hbq
  have hNtop : ∀ b : Base, b ≠ Base.relabel ρ bq →
      (M.board.detach (Base.relabel ρ bq)).topOf b = M.board.topOf b :=
    fun b hb => Board.detach_topOf_ne M.board _ b hb
  have hseatM : ∀ c : Card, c ≠ ρ q →
      ((M.board.detach (Base.relabel ρ bq)).bottomOf c).isSome = (M.board.bottomOf c).isSome := by
    intro c hcq
    cases hb : M.board.bottomOf c with
    | none => rw [Board.bottomOf_detach_of_none hb]
    | some β' =>
        have hβ' : β' ≠ Base.relabel ρ bq := by
          intro hcon
          subst hcon
          exact hcq (Option.some.inj
            (((Board.bottomOf_eq _ _ _).mp hb).symm.trans hseat))
        rw [Board.bottomOf_detach_ne hb hβ']
  have hseatS : ∀ c : Card, c ≠ q →
      ((S.board.detach bq).bottomOf c).isSome = (S.board.bottomOf c).isSome := by
    intro c hcq
    cases hb : S.board.bottomOf c with
    | none => rw [Board.bottomOf_detach_of_none hb]
    | some b' =>
        have hb' : b' ≠ bq := by
          intro hcon
          subst hcon
          exact hcq (Option.some.inj
            (((Board.bottomOf_eq _ _ _).mp hb).symm.trans htopS))
        rw [Board.bottomOf_detach_ne hb hb']
  -- the strands' seats survive (only ρ q is unseated, and it is not stranded)
  have hstrandseat : ∀ x ∈ X, M.board.bottomOf x ≠ some (Base.relabel ρ bq) := by
    intro x hxX hcon
    have h1 : M.board.topOf (Base.relabel ρ bq) = some x := (Board.bottomOf_eq _ _ _).mp hcon
    have h2 : x = ρ q := Option.some.inj (h1.symm.trans hseat)
    exact absurd (h2 ▸ hxX) hX
  have honρ : (ρ q).suit = σ ∨ (ρ q).suit = σ.flipPair := h.core.isTwinMap.suit_mem hon
  refine ⟨⟨h.core.isTwinMap, h.core.fixes_off, h.core.deal_eq, h.core.depths_eq,
    h.core.stock_eq, h.core.step_eq, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs1 hs2
    have h1 : s ≠ (ρ q).suit := by
      rcases honρ with hs | hs
      · intro hcon; exact hs1 (hcon ▸ hs)
      · intro hcon; exact hs2 (hcon ▸ hs)
    have h2 : s ≠ q.suit := by
      rcases hon with hs | hs
      · intro hcon; exact hs1 (hcon ▸ hs)
      · intro hcon; exact hs2 (hcon ▸ hs)
    show (if s = (ρ q).suit then M.heights s + 1 else M.heights s)
      = (if s = q.suit then S.heights s + 1 else S.heights s)
    rw [if_neg h1, if_neg h2]
    exact h.core.heights_off s hs1 hs2
  · intro c' hon'
    by_cases hcq : c' = q
    · rw [hcq]
      constructor
      · intro _
        show (if q.suit = q.suit then S.heights q.suit + 1 else S.heights q.suit)
          > q.rank.toIdx
        rw [if_pos rfl]
        omega
      · intro _
        show (if (ρ q).suit = (ρ q).suit then M.heights (ρ q).suit + 1
            else M.heights (ρ q).suit) > (ρ q).rank.toIdx
        rw [if_pos rfl, Card.IsTwinMap.rank h.core.isTwinMap q, halign]
        omega
    · by_cases hcq' : c' = Card.flipSuit q
      · rw [hcq']
        have hfs : (Card.flipSuit q).suit ≠ q.suit := by
          show q.suit.flipPair ≠ q.suit
          exact Suit.flipPair_ne q.suit
        have hfsρ : (ρ (Card.flipSuit q)).suit ≠ (ρ q).suit := by
          rw [h.core.isTwinMap.flip_comm q, Card.flipSuit_suit]
          exact Suit.flipPair_ne (ρ q).suit
        have honf : (Card.flipSuit q).suit = σ ∨ (Card.flipSuit q).suit = σ.flipPair := by
          show q.suit.flipPair = σ ∨ q.suit.flipPair = σ.flipPair
          rcases hon with hs | hs
          · rw [hs]; exact Or.inr rfl
          · rw [hs]; exact Or.inl (Suit.flipPair_flipPair σ)
        show (if (ρ (Card.flipSuit q)).suit = (ρ q).suit
            then M.heights (ρ (Card.flipSuit q)).suit + 1
            else M.heights (ρ (Card.flipSuit q)).suit) > (ρ (Card.flipSuit q)).rank.toIdx
          ↔ (if (Card.flipSuit q).suit = q.suit then S.heights (Card.flipSuit q).suit + 1
            else S.heights (Card.flipSuit q).suit) > (Card.flipSuit q).rank.toIdx
        rw [if_neg hfsρ, if_neg hfs, Card.flipSuit_rank q]
        exact h.core.stacked_iff (Card.flipSuit q) honf
      · exact State.stacked_bump_aux
          (hS := S.heights) (hM := M.heights)
          (hS' := fun s => if s = q.suit then S.heights s + 1 else S.heights s)
          (hM' := fun s => if s = (ρ q).suit then M.heights s + 1 else M.heights s)
          (ρ := ρ) (ρn := ρ) (q := q) (w := ρ q)
          h.core.isTwinMap h.core.isTwinMap hon rfl (fun _ _ _ => rfl) h.core.stacked_iff
          hrk.symm halign (fun _ => rfl) (fun _ => rfl) c' hcq hcq' hon'
  · intro x hx
    have h1 := h.strand_vis x hx
    rw [State.isVis] at h1
    show ((M.board.detach (Base.relabel ρ bq)).bottomOf x).isSome = true
    cases hb : M.board.bottomOf x with
    | none => rw [hb] at h1; exact absurd h1 (by simp)
    | some β' =>
        have hβ' : β' ≠ Base.relabel ρ bq := by
          intro hcon
          rw [hcon] at hb
          exact hstrandseat x hx hb
        rw [Board.bottomOf_detach_ne hb hβ']
        rfl
  · intro c
    by_cases hc : c = ρ q
    · rw [hc]
      show ((M.board.detach (Base.relabel ρ bq)).bottomOf (ρ q)).isSome
          = ((S.board.detach bq).bottomOf (ρ (ρ q))).isSome
      rw [Board.bottomOf_detach_self hseat, h.core.isTwinMap.invol q,
        Board.bottomOf_detach_self htopS]
    · have hc' : ρ c ≠ q := by
        intro hcon
        exact hc (by rw [← hcon]; exact (h.core.isTwinMap.invol c).symm)
      by_cases hcq : c = q
      · rw [hcq]
        by_cases hqρ : q = ρ q
        · rw [hqρ]
          show ((M.board.detach (Base.relabel ρ bq)).bottomOf (ρ q)).isSome
            = ((S.board.detach bq).bottomOf (ρ (ρ q))).isSome
          rw [Board.bottomOf_detach_self hseat, h.core.isTwinMap.invol q,
            Board.bottomOf_detach_self htopS]
        · show ((M.board.detach (Base.relabel ρ bq)).bottomOf q).isSome
            = ((S.board.detach bq).bottomOf (ρ q)).isSome
          rw [hseatM q hqρ, hseatS (ρ q) (fun hcon => hqρ hcon.symm)]
          exact h.vis_iff q
      · show ((M.board.detach (Base.relabel ρ bq)).bottomOf c).isSome
          = ((S.board.detach bq).bottomOf (ρ c)).isSome
        rw [hseatM c hc, hseatS (ρ c) hc']
        exact h.vis_iff c
  · intro b c hb hc
    have hbq : b ≠ bq := by
      intro hcon
      rw [hcon] at hb
      rw [Board.detach_topOf] at hb
      exact absurd hb (by simp)
    have hSb : S.board.topOf b = some c := by rw [← hRtop b hbq]; exact hb
    have hpre := h.top_some b c hSb hc
    have hbβ : Base.relabel ρ b ≠ Base.relabel ρ bq := by
      intro hcon
      exact hbq (Base.relabel_inj h.core.isTwinMap hcon)
    rw [hNtop _ hbβ]
    exact hpre
  · intro b hb hno
    by_cases hbq : b = bq
    · rw [hbq]
      exact Board.detach_topOf _ _
    · have hSb : S.board.topOf b = none := by rw [← hRtop b hbq]; exact hb
      have hall : ∀ x ∈ X, M.board.bottomOf x ≠ some (Base.relabel ρ b) := by
        intro x hxX hbx
        have h1 : (M.board.detach (Base.relabel ρ bq)).bottomOf x = some (Base.relabel ρ b) := by
          cases hb2 : M.board.bottomOf x with
          | none =>
              rw [Board.bottomOf_detach_of_none hb2]
              rw [hb2] at hbx
              exact hbx
          | some β' =>
              have hβ' : β' ≠ Base.relabel ρ bq := by
                intro hcon
                rw [hcon] at hb2
                exact hstrandseat x hxX hb2
              rw [Board.bottomOf_detach_ne hb2 hβ']
              exact hb2.symm.trans hbx
        exact hno x hxX h1
      have hpre := h.top_none b hSb hall
      have hbβ : Base.relabel ρ b ≠ Base.relabel ρ bq :=
        fun hcon => hbq (Base.relabel_inj h.core.isTwinMap hcon)
      rw [hNtop _ hbβ]
      exact hpre
  · intro x hx b' hb'
    have hρx : ρ x ≠ q := by
      intro hcon
      exact hX (by rw [← hcon, h.core.isTwinMap.invol x]; exact hx)
    have hb'q : b' ≠ bq := by
      intro hcon
      rw [hcon] at hb'
      have h1 : (S.board.detach bq).topOf bq = some (ρ x) := (Board.bottomOf_eq _ _ _).mp hb'
      rw [Board.detach_topOf] at h1
      exact absurd h1 (by simp)
    have hSseat : S.board.bottomOf (ρ x) = some b' := by
      have h1 : (S.board.detach bq).topOf b' = some (ρ x) := (Board.bottomOf_eq _ _ _).mp hb'
      rw [hRtop b' hb'q] at h1
      exact (Board.bottomOf_eq _ _ _).mpr h1
    have hpre := h.top_wanted x hx b' hSseat
    have hbβ : Base.relabel ρ b' ≠ Base.relabel ρ bq := by
      intro hcon
      exact hb'q (Base.relabel_inj h.core.isTwinMap hcon)
    rw [hNtop _ hbβ]
    exact hpre
  · intro x hx
    rw [Board.aboveOf_detach_filter hseat hbareM, h.above_strand x hx,
      ← map_filter_ne (l := S.board.aboveOf (ρ x)) (x := q) h.core.isTwinMap.inj,
      ← Board.aboveOf_detach_filter htopS htop]
  · intro c d hd
    have hsub : d ∈ M.board.aboveOf c :=
      Board.aboveOf_sub (bd' := M.board.detach (Base.relabel ρ bq)) (bd := M.board) (fun b => by
        by_cases hbb : b = Base.relabel ρ bq
        · rw [hbb]
          exact Or.inl (Board.detach_topOf _ _)
        · rw [hNtop b hbb]
          exact Or.inr rfl) d hd
    have hdne : d ≠ ρ q := by
      intro hcon
      subst hcon
      obtain ⟨b₀, hb₀⟩ := Board.mem_aboveOf_seated hd
      have h1 : (M.board.detach (Base.relabel ρ bq)).bottomOf (ρ q) = none :=
        Board.bottomOf_detach_self hseat
      rw [(Board.bottomOf_eq _ _ _).mpr hb₀] at h1
      exact absurd h1 (by simp)
    rcases h.above_sub c d hsub with hm | hdX | ⟨x, hxX, hx⟩
    · left
      obtain ⟨y, hymem, hyy⟩ := List.mem_map.mp hm
      have hyq : y ≠ q := fun hcon => hdne (by rw [← hyy, hcon])
      show d ∈ ((S.board.detach bq).aboveOf (ρ c)).map ρ
      rw [Board.aboveOf_detach_filter htopS htop]
      exact List.mem_map.mpr ⟨y, List.mem_filter.mpr ⟨hymem, bne_iff_ne.mpr hyq⟩, hyy⟩
    · exact Or.inr (Or.inl hdX)
    · refine Or.inr (Or.inr ⟨x, hxX, ?_⟩)
      rw [Board.aboveOf_detach_filter hseat hbareM]
      exact List.mem_filter.mpr ⟨hx, bne_iff_ne.mpr hdne⟩

/-- A member of both halves of a no-duplicate append is a
contradiction. -/
theorem NoDupP_append_mem {l1 l2 : List Card} {a : Card}
    (h : NoDupP (l1 ++ l2)) (h1 : a ∈ l1) (h2 : a ∈ l2) : False := by
  induction l1 with
  | nil => cases h1
  | cons b t ih =>
      rcases List.mem_cons.mp h1 with rfl | hm
      · exact h.1 (List.mem_append_right t h2)
      · exact ih h.2 hm

/-- **The stock and the piles are disjoint** (the deal's no-duplicate
clause, via the stock-cycle sublist: a stock card appears in no pile). -/
theorem State.WF.stock_not_in_piles {S : State} (hwf : S.WF) {q : Card}
    (hq : q ∈ S.stock.cards) : ∀ a, q ∉ S.deal.piles a := by
  intro a hcon
  exact NoDupP_append_mem (noDupCards_NoDupP hwf.deal_wf.2.2)
    (List.mem_flatMap.mpr ⟨a, Anchor.mem_all a, hcon⟩) (hwf.stock_wf.2 q hq)

/-- A member is found: `posOf` of a cycle member is not `none`
(the findFirstIdx of a present card). -/
theorem Cycle.posOf_of_mem {c : Card} {cy : Cycle Card} (h : c ∈ cy.cards) :
    cy.posOf c ≠ none := by
  have key : ∀ (l : List Card), c ∈ l →
      Cycle.findFirstIdx (fun c' => decide (c' = c)) l ≠ none := by
    intro l
    induction l with
    | nil => intro hm; cases hm
    | cons a' t ih =>
        intro hm
        by_cases hpp : a' = c
        · intro hcon
          have h1 : Cycle.findFirstIdx (fun c' => decide (c' = c)) (a' :: t) = some 0 := by
            show (if decide (a' = c) then some 0
              else (Cycle.findFirstIdx (fun c' => decide (c' = c)) t).map Nat.succ) = some 0
            rw [if_pos (by rw [hpp]; simp)]
          rw [h1] at hcon; exact absurd hcon (by simp)
        · have hd : ¬(decide (a' = c) = true) :=
            fun hcon => hpp (of_decide_eq_true hcon)
          show (if decide (a' = c) then some 0
              else (Cycle.findFirstIdx (fun c' => decide (c' = c)) t).map Nat.succ) ≠ none
          rw [if_neg hd]
          rcases List.mem_cons.mp hm with hq | hm'
          · exact absurd hq.symm hpp
          · cases hval : Cycle.findFirstIdx (fun c' => decide (c' = c)) t with
            | none => exact (ih hm' hval).elim
            | some i => simp
  show Cycle.findFirstIdx (fun c' => decide (c' = c)) cy.cards ≠ none
  exact key cy.cards h

/-- **No edges onto a stock card**: a card in the stock carries
nothing (the WF board-edge condition — the base `inr q` needs q
seated or deal-adjacent-with-hidden-boundary, both excluded: a stock
card is neither visible nor in any pile). -/
theorem State.WF.no_topOf_of_stock {S : State} (hwf : S.WF) {q : Card}
    (hq : q ∈ S.stock.cards) : S.board.topOf (Sum.inr q) = none := by
  have hvis : S.isVis q = false := by
    have h3 := hwf.vis_off_cycle q
    cases h4 : S.isVis q with
    | false => rfl
    | true =>
        have h5 : S.stock.posOf q = none := h3 h4
        exact absurd h5 (Cycle.posOf_of_mem hq)
  cases hval : S.board.topOf (Sum.inr q) with
  | none => rfl
  | some e =>
      obtain ⟨-, hbase⟩ := hwf.board_edges (Sum.inr q) e hval
      rcases hbase with ⟨a, t, rest, hpile, halt⟩ | ⟨hbot, -⟩
      · rcases halt with ⟨a', htop⟩ | hbot
        · refine absurd ?_ (hwf.stock_not_in_piles hq a')
          have h1 : q ∈ S.hidden a' := mem_of_getLast (by
            show (S.hidden a').getLast? = some q
            exact htop)
          exact List.mem_of_mem_take h1
        · exact absurd (show S.isVis q = true from hbot) (by rw [hvis]; simp)
      · exact absurd (show S.isVis q = true from hbot) (by rw [hvis]; simp)

/-- **The deckPile step in the frame**: the source draws the stock
card `q` onto a free base `b`, and the mirror plays the same card onto
the `ρ`-image of the base (the fixed point `ρ q = q` from the stock
premise `hstock` makes the card itself carry across).  The successor
frame keeps the strand set `X` unchanged — no strand sits at the
landing seat, none rides on the moved card, no strand walk reads the
landing seat, and the landing base's card-coordinate is synchronized
out of the strands' columns.

The shape premises (the L1/L2 family, each a genuine run-level
invariant the assembly must supply): `hfree` — no strand sits at the
mirror's landing seat; `hbare2` — no strand rides on the moved card
(the mirror's column over it stays empty — the WF-derived
no-edges-onto-stock-cards read through the frame); `hwalk` — no walk
from a strand reads the mirror's landing seat; `hL2` — the landing
base's card-coordinate has its ρ-image not a strand and itself in no
partner's column (the extension synchronization for `above_sub`). -/
theorem State.TwinCorrX.apply_deckPile {ρ σ S M X R q b}
    (h : State.TwinCorrX ρ σ S M X)
    (hwf : S.WF)
    (hstock : ∀ c ∈ S.stock.cards, ρ c = c)
    (hS : S.apply (Move.deckPile q b) = some R)
    (hfree : ∀ x ∈ X, M.board.bottomOf x ≠ some (Base.relabel ρ b))
    (hbare2 : ∀ x ∈ X, M.board.bottomOf x ≠ some (Sum.inr q))
    (hwalk : ∀ x ∈ X, ∀ y ∈ x :: M.board.aboveOf x, Base.relabel ρ b ≠ Sum.inr y)
    (hL2 : ∀ d : Card, b = Sum.inr d →
      (ρ d ∉ X ∧ ∀ x ∈ X, d ∉ S.board.aboveOf (ρ x))) :
    ∃ N, M.apply (Move.deckPile q (Base.relabel ρ b)) = some N ∧
      State.TwinCorrX ρ σ R N X := by
  rw [apply_deckPile_iff] at hS
  obtain ⟨hprev, hcp, bd, hatt, rfl⟩ := hS
  -- the moved card is a stock card, fixed by ρ
  have hmem : q ∈ S.stock.cards := by
    simp only [Cycle.prev] at hprev
    split at hprev
    · exact absurd hprev (by simp)
    · exact List.mem_iff_getElem?.mpr ⟨S.stock.cursor - 1, hprev⟩
  have hqρ : ρ q = q := hstock q hmem
  have hbq : S.board.topOf b = none := by
    cases b with
    | inl a => exact (canPlace_inl_iff.mp hcp).1
    | inr d => exact (canPlace_inr_iff.mp hcp).1
  -- the mirror's guard pieces
  have hfree' : M.board.topOf (Base.relabel ρ b) = none := h.top_none b hbq hfree
  have hqX : q ∉ X := by
    intro hcon
    have h1 : M.isVis q = true := h.strand_vis q hcon
    rw [h.vis_iff q, hqρ] at h1
    have h2 : S.stock.posOf q = none := hwf.vis_off_cycle q h1
    exact absurd h2 (Cycle.posOf_of_mem hmem)
  have hbotqM : M.board.bottomOf q = none := by
    have h2 : S.isVis q = false := by
      have h3 := hwf.vis_off_cycle q
      cases h4 : S.isVis q with
      | false => rfl
      | true =>
          have h5 : S.stock.posOf q = none := h3 h4
          exact absurd h5 (Cycle.posOf_of_mem hmem)
    have h1 : M.isVis q = false := by rw [h.vis_iff q, hqρ, h2]
    have h1' : (M.board.bottomOf q).isSome = false := h1
    cases hb : M.board.bottomOf q with
    | none => rfl
    | some β' =>
        rw [hb] at h1'
        exact absurd h1' (by simp)
  -- the mirror's canPlace
  have hcpM : M.canPlace q (Base.relabel ρ b) = true := by
    cases b with
    | inl a =>
        rw [show Base.relabel ρ (Sum.inl a) = Sum.inl a from rfl]
        refine canPlace_inl_iff.mpr ⟨hfree', ?_⟩
        have h1 := canPlace_inl_iff.mp hcp
        exact h1.2
    | inr d =>
        rw [show Base.relabel ρ (Sum.inr d) = Sum.inr (ρ d) from rfl]
        have h1 := canPlace_inr_iff.mp hcp
        refine canPlace_inr_iff.mpr ⟨hfree', ?_, ?_⟩
        · rw [h.vis_iff (ρ d), h.core.isTwinMap.invol d]
          exact h1.2.1
        · have hc := canSitOn_twinMap h.core.isTwinMap q d
          rw [hqρ] at hc
          rw [hc]
          exact h1.2.2
  -- the source's invisibility facts for the moved card
  have hvis : S.isVis q = false := by
    have h3 := hwf.vis_off_cycle q
    cases h4 : S.isVis q with
    | false => rfl
    | true =>
        have h5 : S.stock.posOf q = none := h3 h4
        exact absurd h5 (Cycle.posOf_of_mem hmem)
  -- the column over the moved card is empty in the mirror
  have hcolM : M.board.topOf (Sum.inr q) = none := by
    have h1 : S.board.topOf (Sum.inr q) = none := hwf.no_topOf_of_stock hmem
    have h2 := h.top_none (Sum.inr q) h1 (fun x hxX hcon => hbare2 x hxX (by
      rw [Base.relabel_inr, hqρ] at hcon
      exact hcon))
    rw [Base.relabel_inr, hqρ] at h2
    exact h2
  -- the mirror's firing
  obtain ⟨bd', hattM⟩ : ∃ bd', M.board.attach (Base.relabel ρ b) q = some bd' := by
    have hne : M.board.attach (Base.relabel ρ b) q ≠ none :=
      (Board.attach_eq_some_iff _ _ _).mpr ⟨hfree', hbotqM⟩
    cases hatt2 : M.board.attach (Base.relabel ρ b) q with
    | none => exact absurd hatt2 hne
    | some bd'' => exact ⟨bd'', rfl⟩
  have hcolq : bd'.topOf (Sum.inr q) = none := by
    have h1 : Sum.inr q ≠ Base.relabel ρ b := by
      intro hcon
      have h2 := congrArg (Base.relabel ρ) hcon.symm
      rw [Base.relabel_invol h.core.isTwinMap b, Base.relabel_inr, hqρ] at h2
      rw [h2] at hcp
      have h3 : S.isVis q = true := (canPlace_inr_iff.mp hcp).2.1
      exact absurd h3 (by rw [hvis]; simp)
    rw [Board.attach_topOf_ne _ _ _ hattM h1]
    exact hcolM
  refine ⟨{M with
      board := bd',
      stock := M.stock.removeAt (M.stock.cursor - 1)},
    apply_deckPile_iff.mpr ⟨by rw [h.core.stock_eq]; exact hprev, hcpM, bd', hattM, rfl⟩, ?_⟩
  -- the successor's topOf kits
  have htopR : bd.topOf b = some q := Board.attach_topOf _ _ _ hatt
  have htopN : bd'.topOf (Base.relabel ρ b) = some q := Board.attach_topOf _ _ _ hattM
  have hRne : ∀ b' : Base, b' ≠ b → bd.topOf b' = S.board.topOf b' :=
    fun b' hb' => Board.attach_topOf_ne _ _ _ hatt hb'
  have hNne : ∀ b' : Base, b' ≠ Base.relabel ρ b → bd'.topOf b' = M.board.topOf b' :=
    fun b' hb' => Board.attach_topOf_ne _ _ _ hattM hb'
  have hrelabel : ∀ b₁ b₂ : Base, Base.relabel ρ b₁ = Base.relabel ρ b₂ → b₁ = b₂ :=
    fun _ _ hcon => Base.relabel_inj h.core.isTwinMap hcon
  refine ⟨⟨h.core.isTwinMap, h.core.fixes_off, h.core.deal_eq, h.core.depths_eq, ?_,
    h.core.step_eq, h.core.heights_off, h.core.stacked_iff⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show M.stock.removeAt (M.stock.cursor - 1) = S.stock.removeAt (S.stock.cursor - 1)
    rw [h.core.stock_eq]
  · -- strand_vis
    intro x hx
    have h1 : (bd'.bottomOf x).isSome = (M.board.bottomOf x).isSome :=
      Board.isVis_attach_eq hattM hfree' (fun hcon => hqX (by rw [← hcon]; exact hx))
    show (bd'.bottomOf x).isSome = true
    rw [h1]
    exact h.strand_vis x hx
  · -- vis_iff
    intro c
    by_cases hcq : c = q
    · rw [hcq]
      show (bd'.bottomOf q).isSome = (bd.bottomOf (ρ q)).isSome
      rw [hqρ, (Board.bottomOf_eq bd' q (Base.relabel ρ b)).mpr htopN,
        (Board.bottomOf_eq bd q b).mpr htopR]
      rfl
    · have h1 : (bd'.bottomOf c).isSome = (M.board.bottomOf c).isSome :=
        Board.isVis_attach_eq hattM hfree' hcq
      have hρc : ρ c ≠ q := by
        intro hcon
        have h2 : c = ρ (ρ c) := (h.core.isTwinMap.invol c).symm
        rw [hcon, hqρ] at h2
        exact hcq h2
      have h2 : (bd.bottomOf (ρ c)).isSome = (S.board.bottomOf (ρ c)).isSome :=
        Board.isVis_attach_eq hatt hbq hρc
      show (bd'.bottomOf c).isSome = (bd.bottomOf (ρ c)).isSome
      rw [h1, h2]
      exact h.vis_iff c
  · -- top_some
    intro b' c' hb' hc'
    by_cases hbb : b' = b
    · rw [hbb] at hb' ⊢
      have hc'q : c' = q := Option.some.inj ((show bd.topOf b = some c' from hb').symm.trans htopR)
      rw [hc'q]
      show bd'.topOf (Base.relabel ρ b) = some (ρ q)
      rw [hqρ]
      exact htopN
    · have hb'2 : S.board.topOf b' = some c' := by
        rw [← hRne b' hbb]
        exact hb'
      show bd'.topOf (Base.relabel ρ b') = some (ρ c')
      rw [hNne (Base.relabel ρ b') (fun hcon => hbb (hrelabel _ _ hcon))]
      exact h.top_some b' c' hb'2 hc'
  · -- top_none
    intro b' hb' hnb
    by_cases hbb : b' = b
    · rw [hbb] at hb'
      exact absurd (show bd.topOf b = none from hb') (by rw [htopR]; simp)
    · have hb'2 : S.board.topOf b' = none := by
        rw [← hRne b' hbb]
        exact hb'
      have hnb2 : ∀ x ∈ X, M.board.bottomOf x ≠ some (Base.relabel ρ b') := by
        intro x hx hcon
        refine hnb x hx ?_
        rw [Board.bottomOf_eq M.board x (Base.relabel ρ b')] at hcon
        exact (Board.bottomOf_eq bd' x (Base.relabel ρ b')).mpr (by
          rw [hNne (Base.relabel ρ b') (fun hc => hbb (hrelabel _ _ hc))]
          exact hcon)
      show bd'.topOf (Base.relabel ρ b') = none
      rw [hNne (Base.relabel ρ b') (fun hc => hbb (hrelabel _ _ hc))]
      exact h.top_none b' hb'2 hnb2
  · -- top_wanted
    intro x hx b' hb'
    by_cases hbb : b' = b
    · rw [hbb] at hb'
      have h1 : bd.topOf b = some (ρ x) :=
        (Board.bottomOf_eq bd (ρ x) b).mp (show bd.bottomOf (ρ x) = some b from hb')
      have h2 : ρ x = q := Option.some.inj (h1.symm.trans htopR)
      have h3 : x = q := by
        have h4 : x = ρ (ρ x) := (h.core.isTwinMap.invol x).symm
        rw [h2, hqρ] at h4
        exact h4
      exact absurd (by rw [← h3]; exact hx) hqX
    · have hb'2 : S.board.bottomOf (ρ x) = some b' := by
        rw [Board.bottomOf_eq S.board (ρ x) b', ← hRne b' hbb]
        exact (Board.bottomOf_eq bd (ρ x) b').mp (show bd.bottomOf (ρ x) = some b' from hb')
      show bd'.topOf (Base.relabel ρ b') = none
      rw [hNne (Base.relabel ρ b') (fun hc => hbb (hrelabel _ _ hc))]
      exact h.top_wanted x hx b' hb'2
  · -- above_strand
    intro x hx
    have h1 : bd'.aboveOf x = M.board.aboveOf x := by
      refine Board.aboveOf_congr ?_
      intro y hy
      exact (Board.attach_topOf_ne _ _ _ hattM (Ne.symm (hwalk x hx y hy))).symm
    have hSread : ∀ y ∈ ρ x :: S.board.aboveOf (ρ x), b ≠ Sum.inr y := by
      intro y hy hcon
      obtain ⟨h2, h3⟩ := hL2 y hcon
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact h2 (by rw [h.core.isTwinMap.invol x]; exact hx)
      · exact h3 x hx hy'
    have h2 : bd.aboveOf (ρ x) = S.board.aboveOf (ρ x) := by
      refine Board.aboveOf_congr ?_
      intro y hy
      exact (Board.attach_topOf_ne _ _ _ hatt (Ne.symm (hSread y hy))).symm
    show bd'.aboveOf x = (bd.aboveOf (ρ x)).map ρ
    rw [h1, h2]
    exact h.above_strand x hx
  · -- above_sub
    intro c y hy
    rcases Board.mem_aboveOf_attach_cases hattM hfree' hcolq (show y ∈ bd'.aboveOf c from hy)
      with h1 | h1
    · rcases h.above_sub c y h1 with h2 | h2 | ⟨x, hxX, h2⟩
      · obtain ⟨e, he, hey⟩ := List.mem_map.mp h2
        exact Or.inl (List.mem_map.mpr ⟨e, Board.aboveOf_attach_sup hatt he, hey⟩)
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ⟨x, hxX, Board.aboveOf_attach_sup hattM h2⟩)
    · rw [h1] at hy ⊢
      cases b with
      | inl a =>
          -- the landing seats are anchor seats: no walk ever reads them
          have hcongr : bd'.aboveOf c = M.board.aboveOf c := by
            refine Board.aboveOf_congr ?_
            intro y hy
            refine (Board.attach_topOf_ne _ _ _ hattM ?_).symm
            intro hcon
            rw [show Base.relabel ρ (Sum.inl a) = Sum.inl a from rfl] at hcon
            exact absurd hcon (by simp)
          have hy2 : q ∈ M.board.aboveOf c := by rw [← hcongr]; exact hy
          obtain ⟨b₀, hb₀⟩ := Board.mem_aboveOf_seated hy2
          exact absurd ((Board.bottomOf_eq M.board q b₀).mpr hb₀) (by rw [hbotqM]; simp)
      | inr d =>
          by_cases hSreach : d ∈ ρ c :: S.board.aboveOf (ρ c)
          · have hjoin : q ∈ bd.aboveOf (ρ c) :=
              Board.mem_aboveOf_attach_new hatt hbq hSreach
            exact Or.inl (List.mem_map.mpr ⟨q, hjoin, hqρ⟩)
          · by_cases hMread : ρ d ∈ c :: M.board.aboveOf c
            · rcases List.mem_cons.mp hMread with hzc | hzmem'
              · exact absurd (show d ∈ ρ c :: S.board.aboveOf (ρ c) from by
                  rw [show ρ c = d from by rw [← hzc, h.core.isTwinMap.invol d]]
                  exact List.mem_cons_self) hSreach
              · rcases h.above_sub c (ρ d) hzmem' with h2 | h2 | ⟨x, hxX, h2⟩
                · obtain ⟨e, he, hze⟩ := List.mem_map.mp h2
                  exact absurd (show d ∈ ρ c :: S.board.aboveOf (ρ c) from by
                    rw [show d = e from h.core.isTwinMap.inj hze.symm]
                    exact List.mem_cons_of_mem _ he) hSreach
                · exact absurd h2 (hL2 d rfl).1
                · exact Or.inr (Or.inr ⟨x, hxX, Board.mem_aboveOf_attach_new hattM hfree'
                    (List.mem_cons_of_mem _ h2)⟩)
            · have hcongr : bd'.aboveOf c = M.board.aboveOf c := by
                refine Board.aboveOf_congr ?_
                intro y hy
                refine (Board.attach_topOf_ne _ _ _ hattM ?_).symm
                intro hcon
                rw [show Base.relabel ρ (Sum.inr d) = Sum.inr (ρ d) from rfl] at hcon
                exact hMread (by rw [← Sum.inr.inj hcon]; exact hy)
              have hy2 : q ∈ M.board.aboveOf c := by rw [← hcongr]; exact hy
              obtain ⟨b₀, hb₀⟩ := Board.mem_aboveOf_seated hy2
              exact absurd ((Board.bottomOf_eq M.board q b₀).mpr hb₀) (by rw [hbotqM]; simp)

/-- **No edges onto a foundation card**: a card below its suit's rung
carries nothing (the `founds_gone` side fact: it is neither seated on
the board nor deal-adjacent with a live boundary). -/
theorem State.WF.no_topOf_of_found {S : State} (hwf : S.WF) {c : Card}
    (hlt : c.rank.toIdx < S.heights c.suit) : S.board.topOf (Sum.inr c) = none := by
  obtain ⟨hvis, -, hhid⟩ := hwf.founds_gone c hlt
  have hiv : (S.board.bottomOf c).isSome = false := hvis
  cases hval : S.board.topOf (Sum.inr c) with
  | none => rfl
  | some y =>
      obtain ⟨-, hbase⟩ := hwf.board_edges (Sum.inr c) y hval
      rcases hbase with ⟨a, t, rest, hpile, halt⟩ | ⟨hbd, -⟩
      · rcases halt with ⟨a', htop⟩ | hbd
        · exact absurd (mem_of_getLast (by
            show (S.hidden a').getLast? = some c
            exact htop)) (hhid a')
        · rw [hiv] at hbd; exact Bool.noConfusion hbd
      · rw [hiv] at hbd; exact Bool.noConfusion hbd

/-- **The off-suit worry-back in the frame**: the source returns the
off-suit foundation card `c` to the base `b`, and the mirror returns
the SAME card (`ρ` fixes it) to the `ρ`-image of the base — the rung
drops on both sides through the core's off-suit height agreement.  The
shape premises are the L1/L2 family of the landing (as in
`apply_deckPile`): `hfree` — no strand sits at the mirror's landing
seat; `hbare2` — no strand rides on the returned card; `hwalk` — no
strand walk reads the mirror's landing seat; `hL2` — the landing
base's card-coordinate is synchronized out of the strands' columns. -/
theorem State.TwinCorrX.apply_stackPile_off {ρ σ S M X R c b}
    (h : State.TwinCorrX ρ σ S M X)
    (hwf : S.WF)
    (hoff : c.suit ≠ σ ∧ c.suit ≠ σ.flipPair)
    (hS : S.apply (Move.stackPile c b) = some R)
    (hfree : ∀ x ∈ X, M.board.bottomOf x ≠ some (Base.relabel ρ b))
    (hbare2 : ∀ x ∈ X, M.board.bottomOf x ≠ some (Sum.inr c))
    (hwalk : ∀ x ∈ X, ∀ y ∈ x :: M.board.aboveOf x, Base.relabel ρ b ≠ Sum.inr y)
    (hL2 : ∀ d : Card, b = Sum.inr d →
      (ρ d ∉ X ∧ ∀ x ∈ X, d ∉ S.board.aboveOf (ρ x))) :
    ∃ N, M.apply (Move.stackPile c (Base.relabel ρ b)) = some N ∧
      State.TwinCorrX ρ σ R N X := by
  rw [apply_stackPile_iff] at hS
  obtain ⟨hrk, hcp, bd, hatt, rfl⟩ := hS
  have hlt : c.rank.toIdx < S.heights c.suit := by omega
  have hcρ : ρ c = c := h.core.fixes_off c hoff.1 hoff.2
  have hvis : S.isVis c = false := (hwf.founds_gone c hlt).1
  have hcX : c ∉ X := by
    intro hcon
    have h1 : M.isVis c = true := h.strand_vis c hcon
    rw [h.vis_iff c, hcρ] at h1
    exact absurd h1 (by rw [hvis]; simp)
  have hbq : S.board.topOf b = none := by
    cases b with
    | inl a => exact (canPlace_inl_iff.mp hcp).1
    | inr d => exact (canPlace_inr_iff.mp hcp).1
  have hfree' : M.board.topOf (Base.relabel ρ b) = none := h.top_none b hbq hfree
  have hbotcM : M.board.bottomOf c = none := by
    have h1 : M.isVis c = false := by rw [h.vis_iff c, hcρ, hvis]
    have h1' : (M.board.bottomOf c).isSome = false := h1
    cases hb : M.board.bottomOf c with
    | none => rfl
    | some β' =>
        rw [hb] at h1'
        exact absurd h1' (by simp)
  have hcpM : M.canPlace c (Base.relabel ρ b) = true := by
    cases b with
    | inl a =>
        rw [show Base.relabel ρ (Sum.inl a) = Sum.inl a from rfl]
        refine canPlace_inl_iff.mpr ⟨hfree', ?_⟩
        exact (canPlace_inl_iff.mp hcp).2
    | inr d =>
        rw [show Base.relabel ρ (Sum.inr d) = Sum.inr (ρ d) from rfl]
        have h1 := canPlace_inr_iff.mp hcp
        refine canPlace_inr_iff.mpr ⟨hfree', ?_, ?_⟩
        · rw [h.vis_iff (ρ d), h.core.isTwinMap.invol d]
          exact h1.2.1
        · have hc2 := canSitOn_twinMap h.core.isTwinMap c d
          rw [hcρ] at hc2
          rw [hc2]
          exact h1.2.2
  have hrkM : c.rank.toIdx + 1 = M.heights c.suit := by
    rw [h.core.heights_off c.suit hoff.1 hoff.2]
    exact hrk
  -- the column over the returned card is empty in the mirror
  have hcolM : M.board.topOf (Sum.inr c) = none := by
    have h1 : S.board.topOf (Sum.inr c) = none := hwf.no_topOf_of_found hlt
    have h2 := h.top_none (Sum.inr c) h1 (fun x hxX hcon => hbare2 x hxX (by
      rw [Base.relabel_inr, hcρ] at hcon
      exact hcon))
    rw [Base.relabel_inr, hcρ] at h2
    exact h2
  -- the mirror's firing
  obtain ⟨bd', hattM⟩ : ∃ bd', M.board.attach (Base.relabel ρ b) c = some bd' := by
    have hne : M.board.attach (Base.relabel ρ b) c ≠ none :=
      (Board.attach_eq_some_iff _ _ _).mpr ⟨hfree', hbotcM⟩
    cases hatt2 : M.board.attach (Base.relabel ρ b) c with
    | none => exact absurd hatt2 hne
    | some bd'' => exact ⟨bd'', rfl⟩
  have hcolc : bd'.topOf (Sum.inr c) = none := by
    have h1 : Sum.inr c ≠ Base.relabel ρ b := by
      intro hcon
      have h2 := congrArg (Base.relabel ρ) hcon.symm
      rw [Base.relabel_invol h.core.isTwinMap b, Base.relabel_inr, hcρ] at h2
      rw [h2] at hcp
      have h3 : S.isVis c = true := (canPlace_inr_iff.mp hcp).2.1
      exact absurd h3 (by rw [hvis]; simp)
    rw [Board.attach_topOf_ne _ _ _ hattM h1]
    exact hcolM
  refine ⟨{M with
      board := bd',
      heights := fun s => if s = c.suit then M.heights s - 1 else M.heights s},
    apply_stackPile_iff.mpr ⟨hrkM, hcpM, bd', hattM, rfl⟩, ?_⟩
  -- the successor's topOf kits
  have htopR : bd.topOf b = some c := Board.attach_topOf _ _ _ hatt
  have htopN : bd'.topOf (Base.relabel ρ b) = some c := Board.attach_topOf _ _ _ hattM
  have hRne : ∀ b' : Base, b' ≠ b → bd.topOf b' = S.board.topOf b' :=
    fun b' hb' => Board.attach_topOf_ne _ _ _ hatt hb'
  have hNne : ∀ b' : Base, b' ≠ Base.relabel ρ b → bd'.topOf b' = M.board.topOf b' :=
    fun b' hb' => Board.attach_topOf_ne _ _ _ hattM hb'
  have hrelabel : ∀ b₁ b₂ : Base, Base.relabel ρ b₁ = Base.relabel ρ b₂ → b₁ = b₂ :=
    fun _ _ hcon => Base.relabel_inj h.core.isTwinMap hcon
  refine ⟨⟨h.core.isTwinMap, h.core.fixes_off, h.core.deal_eq, h.core.depths_eq,
    h.core.stock_eq, h.core.step_eq, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- heights_off
    intro s hs1 hs2
    show (if s = c.suit then M.heights s - 1 else M.heights s)
      = (if s = c.suit then S.heights s - 1 else S.heights s)
    by_cases hsc : s = c.suit
    · rw [if_pos hsc, if_pos hsc, h.core.heights_off s hs1 hs2]
    · rw [if_neg hsc, if_neg hsc]
      exact h.core.heights_off s hs1 hs2
  · -- stacked_iff
    intro c' hon'
    have honρ : (ρ c').suit ≠ c.suit := by
      intro hcon
      rcases h.core.isTwinMap.suit_mem hon' with hs | hs
      · rw [hs] at hcon; exact hoff.1 hcon.symm
      · rw [hs] at hcon; exact hoff.2 hcon.symm
    have hcs : c'.suit ≠ c.suit := by
      intro hcon
      rcases hon' with hs | hs
      · rw [hs] at hcon; exact hoff.1 hcon.symm
      · rw [hs] at hcon; exact hoff.2 hcon.symm
    show (if (ρ c').suit = c.suit then M.heights (ρ c').suit - 1 else M.heights (ρ c').suit)
        > (ρ c').rank.toIdx
      ↔ (if c'.suit = c.suit then S.heights c'.suit - 1 else S.heights c'.suit) > c'.rank.toIdx
    rw [if_neg honρ, if_neg hcs]
    exact h.core.stacked_iff c' hon'
  · -- strand_vis
    intro x hx
    have h1 : (bd'.bottomOf x).isSome = (M.board.bottomOf x).isSome :=
      Board.isVis_attach_eq hattM hfree' (fun hcon => hcX (by rw [← hcon]; exact hx))
    show (bd'.bottomOf x).isSome = true
    rw [h1]
    exact h.strand_vis x hx
  · -- vis_iff
    intro c₂
    by_cases hcq : c₂ = c
    · rw [hcq]
      show (bd'.bottomOf c).isSome = (bd.bottomOf (ρ c)).isSome
      rw [hcρ, (Board.bottomOf_eq bd' c (Base.relabel ρ b)).mpr htopN,
        (Board.bottomOf_eq bd c b).mpr htopR]
      rfl
    · have h1 : (bd'.bottomOf c₂).isSome = (M.board.bottomOf c₂).isSome :=
        Board.isVis_attach_eq hattM hfree' hcq
      have hρc : ρ c₂ ≠ c := by
        intro hcon
        have h2 : c₂ = ρ (ρ c₂) := (h.core.isTwinMap.invol c₂).symm
        rw [hcon, hcρ] at h2
        exact hcq h2
      have h2 : (bd.bottomOf (ρ c₂)).isSome = (S.board.bottomOf (ρ c₂)).isSome :=
        Board.isVis_attach_eq hatt hbq hρc
      show (bd'.bottomOf c₂).isSome = (bd.bottomOf (ρ c₂)).isSome
      rw [h1, h2]
      exact h.vis_iff c₂
  · -- top_some
    intro b' c' hb' hc'
    by_cases hbb : b' = b
    · rw [hbb] at hb' ⊢
      have hc'c : c' = c := Option.some.inj ((show bd.topOf b = some c' from hb').symm.trans htopR)
      rw [hc'c]
      show bd'.topOf (Base.relabel ρ b) = some (ρ c)
      rw [hcρ]
      exact htopN
    · have hb'2 : S.board.topOf b' = some c' := by
        rw [← hRne b' hbb]
        exact hb'
      show bd'.topOf (Base.relabel ρ b') = some (ρ c')
      rw [hNne (Base.relabel ρ b') (fun hcon => hbb (hrelabel _ _ hcon))]
      exact h.top_some b' c' hb'2 hc'
  · -- top_none
    intro b' hb' hnb
    by_cases hbb : b' = b
    · rw [hbb] at hb'
      exact absurd (show bd.topOf b = none from hb') (by rw [htopR]; simp)
    · have hb'2 : S.board.topOf b' = none := by
        rw [← hRne b' hbb]
        exact hb'
      have hnb2 : ∀ x ∈ X, M.board.bottomOf x ≠ some (Base.relabel ρ b') := by
        intro x hx hcon
        refine hnb x hx ?_
        rw [Board.bottomOf_eq M.board x (Base.relabel ρ b')] at hcon
        exact (Board.bottomOf_eq bd' x (Base.relabel ρ b')).mpr (by
          rw [hNne (Base.relabel ρ b') (fun hc => hbb (hrelabel _ _ hc))]
          exact hcon)
      show bd'.topOf (Base.relabel ρ b') = none
      rw [hNne (Base.relabel ρ b') (fun hc => hbb (hrelabel _ _ hc))]
      exact h.top_none b' hb'2 hnb2
  · -- top_wanted
    intro x hx b' hb'
    by_cases hbb : b' = b
    · rw [hbb] at hb'
      have h1 : bd.topOf b = some (ρ x) :=
        (Board.bottomOf_eq bd (ρ x) b).mp (show bd.bottomOf (ρ x) = some b from hb')
      have h2 : ρ x = c := Option.some.inj (h1.symm.trans htopR)
      have h3 : x = c := by
        have h4 : x = ρ (ρ x) := (h.core.isTwinMap.invol x).symm
        rw [h2, hcρ] at h4
        exact h4
      exact absurd (by rw [← h3]; exact hx) hcX
    · have hb'2 : S.board.bottomOf (ρ x) = some b' := by
        rw [Board.bottomOf_eq S.board (ρ x) b', ← hRne b' hbb]
        exact (Board.bottomOf_eq bd (ρ x) b').mp (show bd.bottomOf (ρ x) = some b' from hb')
      show bd'.topOf (Base.relabel ρ b') = none
      rw [hNne (Base.relabel ρ b') (fun hc => hbb (hrelabel _ _ hc))]
      exact h.top_wanted x hx b' hb'2
  · -- above_strand
    intro x hx
    have h1 : bd'.aboveOf x = M.board.aboveOf x := by
      refine Board.aboveOf_congr ?_
      intro y hy
      exact (Board.attach_topOf_ne _ _ _ hattM (Ne.symm (hwalk x hx y hy))).symm
    have hSread : ∀ y ∈ ρ x :: S.board.aboveOf (ρ x), b ≠ Sum.inr y := by
      intro y hy hcon
      obtain ⟨h2, h3⟩ := hL2 y hcon
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact h2 (by rw [h.core.isTwinMap.invol x]; exact hx)
      · exact h3 x hx hy'
    have h2 : bd.aboveOf (ρ x) = S.board.aboveOf (ρ x) := by
      refine Board.aboveOf_congr ?_
      intro y hy
      exact (Board.attach_topOf_ne _ _ _ hatt (Ne.symm (hSread y hy))).symm
    show bd'.aboveOf x = (bd.aboveOf (ρ x)).map ρ
    rw [h1, h2]
    exact h.above_strand x hx
  · -- above_sub
    intro c₂ y hy
    rcases Board.mem_aboveOf_attach_cases hattM hfree' hcolc (show y ∈ bd'.aboveOf c₂ from hy)
      with h1 | h1
    · rcases h.above_sub c₂ y h1 with h2 | h2 | ⟨x, hxX, h2⟩
      · obtain ⟨e, he, hey⟩ := List.mem_map.mp h2
        exact Or.inl (List.mem_map.mpr ⟨e, Board.aboveOf_attach_sup hatt he, hey⟩)
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ⟨x, hxX, Board.aboveOf_attach_sup hattM h2⟩)
    · rw [h1] at hy ⊢
      cases b with
      | inl a =>
          -- the landing seats are anchor seats: no walk ever reads them
          have hcongr : bd'.aboveOf c₂ = M.board.aboveOf c₂ := by
            refine Board.aboveOf_congr ?_
            intro y hy
            refine (Board.attach_topOf_ne _ _ _ hattM ?_).symm
            intro hcon
            rw [show Base.relabel ρ (Sum.inl a) = Sum.inl a from rfl] at hcon
            exact absurd hcon (by simp)
          have hy2 : c ∈ M.board.aboveOf c₂ := by rw [← hcongr]; exact hy
          obtain ⟨b₀, hb₀⟩ := Board.mem_aboveOf_seated hy2
          exact absurd ((Board.bottomOf_eq M.board c b₀).mpr hb₀) (by rw [hbotcM]; simp)
      | inr d =>
          by_cases hSreach : d ∈ ρ c₂ :: S.board.aboveOf (ρ c₂)
          · have hjoin : c ∈ bd.aboveOf (ρ c₂) :=
              Board.mem_aboveOf_attach_new hatt hbq hSreach
            exact Or.inl (List.mem_map.mpr ⟨c, hjoin, hcρ⟩)
          · by_cases hMread : ρ d ∈ c₂ :: M.board.aboveOf c₂
            · rcases List.mem_cons.mp hMread with hzc | hzmem'
              · exact absurd (show d ∈ ρ c₂ :: S.board.aboveOf (ρ c₂) from by
                  rw [show ρ c₂ = d from by rw [← hzc, h.core.isTwinMap.invol d]]
                  exact List.mem_cons_self) hSreach
              · rcases h.above_sub c₂ (ρ d) hzmem' with h2 | h2 | ⟨x, hxX, h2⟩
                · obtain ⟨e, he, hze⟩ := List.mem_map.mp h2
                  exact absurd (show d ∈ ρ c₂ :: S.board.aboveOf (ρ c₂) from by
                    rw [show d = e from h.core.isTwinMap.inj hze.symm]
                    exact List.mem_cons_of_mem _ he) hSreach
                · exact absurd h2 (hL2 d rfl).1
                · exact Or.inr (Or.inr ⟨x, hxX, Board.mem_aboveOf_attach_new hattM hfree'
                    (List.mem_cons_of_mem _ h2)⟩)
            · have hcongr : bd'.aboveOf c₂ = M.board.aboveOf c₂ := by
                refine Board.aboveOf_congr ?_
                intro y hy
                refine (Board.attach_topOf_ne _ _ _ hattM ?_).symm
                intro hcon
                rw [show Base.relabel ρ (Sum.inr d) = Sum.inr (ρ d) from rfl] at hcon
                exact hMread (by rw [← Sum.inr.inj hcon]; exact hy)
              have hy2 : c ∈ M.board.aboveOf c₂ := by rw [← hcongr]; exact hy
              obtain ⟨b₀, hb₀⟩ := Board.mem_aboveOf_seated hy2
              exact absurd ((Board.bottomOf_eq M.board c b₀).mpr hb₀) (by rw [hbotcM]; simp)

/-- **The reveal step in the frame**: the boundary card is
deal-determined and every hidden card is `ρ`-fixed (`hhid`), so the
mirror turns the same boundary `r` at the same `hiddenBase` — the
cover conjugates (`hcX`), and the hiddenness of the under-card makes
every walk-condition (the strands never read the landing seat, the
extension stays out of the strands' columns) DERIVABLE rather than
premised.  The two genuine shape premises: no strand sits at the
mirror's landing seat (`hfree`), and none rides the mirror's cover
(`hcov`). -/
theorem State.TwinCorrX.apply_reveal_X {ρ σ S M X R c r a}
    (h : State.TwinCorrX ρ σ S M X)
    (hwf : S.WF)
    (hhid : ∀ a', ∀ c' ∈ S.hidden a', ρ c' = c')
    (hcX : c ∉ X.map ρ)
    (hS : S.apply (Move.reveal c) = some R)
    (hbot : S.board.bottomOf c = some (Sum.inr r))
    (hp : S.pileOfTopHidden r = some a)
    (hcov : ∀ x ∈ X, M.board.bottomOf x ≠ some (Sum.inr (ρ c)))
    (hfree : ∀ x ∈ X, M.board.bottomOf x ≠ some (S.hiddenBase a)) :
    ∃ N, M.apply (Move.reveal (ρ c)) = some N ∧ State.TwinCorrX ρ σ R N X := by
  rw [apply_reveal_iff] at hS
  obtain ⟨htop, r', a', bd, hbot', hp', hatt, rfl⟩ := hS
  have hrr' : r' = r := Sum.inr.inj (Option.some.inj (hbot'.symm.trans hbot))
  rw [hrr'] at hp' hatt
  have haa' : a' = a := Option.some.inj (hp'.symm.trans hp)
  rw [haa'] at hatt hp' ⊢
  -- the boundary facts: hidden, ρ-fixed, invisible both sides
  have hrhid : r ∈ S.hidden a := State.mem_hidden_of_pileOfTopHidden hp
  have hrr : ρ r = r := hhid a r hrhid
  have hvir : S.isVis r = false := by
    have h1 := hwf.vis_not_hidden r
    cases h2 : S.isVis r with
    | false => rfl
    | true => exact (h1 h2 a hrhid).elim
  have hbotrM : M.board.bottomOf r = none := by
    have h1 : M.isVis r = false := by rw [h.vis_iff r, hrr, hvir]
    have h1' : (M.board.bottomOf r).isSome = false := h1
    cases hb : M.board.bottomOf r with
    | none => rfl
    | some β' =>
        rw [hb] at h1'
        exact absurd h1' (by simp)
  have hrX : r ∉ X := by
    intro hcon
    have h1 : M.isVis r = true := h.strand_vis r hcon
    rw [h.vis_iff r, hrr] at h1
    exact absurd h1 (by rw [hvir]; simp)
  -- the landing seat is ρ-fixed
  have hHBfix : Base.relabel ρ (S.hiddenBase a) = S.hiddenBase a := by
    cases hHB : S.hiddenBase a with
    | inl a' => rfl
    | inr d =>
        have hdr : ρ d = d := hhid a d (State.mem_hidden_of_hiddenBase hHB)
        show Sum.inr (ρ d) = Sum.inr d
        rw [hdr]
  -- the mirror's guard pieces
  have hbotc : S.board.topOf (Sum.inr r) = some c :=
    (Board.bottomOf_eq S.board c (Sum.inr r)).mp hbot
  have hcovM : M.board.topOf (Sum.inr r) = some (ρ c) := by
    have h1 := h.top_some (Sum.inr r) c hbotc hcX
    rw [show Base.relabel ρ (Sum.inr r) = Sum.inr (ρ r) from rfl, hrr] at h1
    exact h1
  have hbotM : M.board.bottomOf (ρ c) = some (Sum.inr r) :=
    (Board.bottomOf_eq M.board (ρ c) (Sum.inr r)).mpr hcovM
  have htopM : M.board.topOf (Sum.inr (ρ c)) = none := by
    have h1 := h.top_none (Sum.inr c) htop (fun x hxX hcon => hcov x hxX (by
      rw [show Base.relabel ρ (Sum.inr c) = Sum.inr (ρ c) from rfl] at hcon
      exact hcon))
    rw [show Base.relabel ρ (Sum.inr c) = Sum.inr (ρ c) from rfl] at h1
    exact h1
  have hpM : M.pileOfTopHidden r = some a :=
    (Frame.pileOfTopHidden_congr h.core.deal_eq h.core.depths_eq r).trans hp
  have hfreeS : S.board.topOf (S.hiddenBase a) = none :=
    ((Board.attach_eq_some_iff S.board (S.hiddenBase a) r).mp (by rw [hatt]; simp)).1
  have hfreeM : M.board.topOf (S.hiddenBase a) = none := by
    have h1 := h.top_none (S.hiddenBase a) hfreeS (fun x hxX hcon => hfree x hxX (by
      rw [hHBfix] at hcon
      exact hcon))
    rw [hHBfix] at h1
    exact h1
  -- the hidden under-card facts (whenever the landing seat is a card seat)
  have hdF : ∀ d : Card, S.hiddenBase a = Sum.inr d →
      (ρ d = d ∧ M.isVis d = false ∧ S.isVis d = false ∧ d ≠ r ∧ d ≠ ρ c) := by
    intro d hHB
    have hd : d ∈ S.hidden a := State.mem_hidden_of_hiddenBase hHB
    have hdr : ρ d = d := hhid a d hd
    have hvS : S.isVis d = false := by
      have h1 := hwf.vis_not_hidden d
      cases h2 : S.isVis d with
      | false => rfl
      | true => exact (h1 h2 a hd).elim
    have hvM : M.isVis d = false := by rw [h.vis_iff d, hdr, hvS]
    have hne1 : d ≠ r := by
      intro hcon
      rw [hHB] at hfreeS
      rw [← hcon] at hbotc
      exact absurd (hbotc.symm.trans hfreeS) (by simp)
    have hne2 : d ≠ ρ c := by
      intro hcon
      have h1 : S.isVis c = true := by
        show (S.board.bottomOf c).isSome = true
        rw [hbot]
        rfl
      have h2 : M.isVis (ρ c) = true := by rw [h.vis_iff (ρ c), h.core.isTwinMap.invol c, h1]
      rw [← hcon] at h2
      exact absurd h2 (by rw [hvM]; simp)
    exact ⟨hdr, hvM, hvS, hne1, hne2⟩
  -- the successor's seat kits
  have htopR : bd.topOf (S.hiddenBase a) = some r := Board.attach_topOf _ _ _ hatt
  obtain ⟨bd', hattM⟩ : ∃ bd', M.board.attach (S.hiddenBase a) r = some bd' := by
    have hne : M.board.attach (S.hiddenBase a) r ≠ none :=
      (Board.attach_eq_some_iff _ _ _).mpr ⟨hfreeM, hbotrM⟩
    cases hatt2 : M.board.attach (S.hiddenBase a) r with
    | none => exact absurd hatt2 hne
    | some bd'' => exact ⟨bd'', rfl⟩
  have htopN : bd'.topOf (S.hiddenBase a) = some r := Board.attach_topOf _ _ _ hattM
  have hRne : ∀ b' : Base, b' ≠ S.hiddenBase a → bd.topOf b' = S.board.topOf b' :=
    fun b' hb' => Board.attach_topOf_ne _ _ _ hatt hb'
  have hNne : ∀ b' : Base, b' ≠ S.hiddenBase a → bd'.topOf b' = M.board.topOf b' :=
    fun b' hb' => Board.attach_topOf_ne _ _ _ hattM hb'
  have hrelabel : ∀ b₁ b₂ : Base, Base.relabel ρ b₁ = Base.relabel ρ b₂ → b₁ = b₂ :=
    fun _ _ hcon => Base.relabel_inj h.core.isTwinMap hcon
  have hrvis : M.isVis r = false := by rw [h.vis_iff r, hrr, hvir]
  have hcovvis : M.isVis (ρ c) = true := by
    have h1 : S.isVis c = true := by
      show (S.board.bottomOf c).isSome = true
      rw [hbot]
      rfl
    rw [h.vis_iff (ρ c), h.core.isTwinMap.invol c, h1]
  refine ⟨{M with
      board := bd',
      depths := fun a' => if a' = a then M.depths a - 1 else M.depths a'},
    apply_reveal_iff.mpr ⟨htopM, r, a, bd', hbotM, hpM,
      by rw [Frame.hiddenBase_congr h.core.deal_eq h.core.depths_eq a]; exact hattM, rfl⟩, ?_⟩
  refine ⟨⟨h.core.isTwinMap, h.core.fixes_off, h.core.deal_eq, ?_, h.core.stock_eq,
    h.core.step_eq, h.core.heights_off, h.core.stacked_iff⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- depths_eq
    funext a'
    by_cases ha' : a' = a
    · rw [ha']
      show (if a = a then M.depths a - 1 else M.depths a)
        = (if a = a then S.depths a - 1 else S.depths a)
      rw [if_pos rfl, if_pos rfl]
      show M.depths a - 1 = S.depths a - 1
      rw [congrFun h.core.depths_eq a]
    · show (if a' = a then M.depths a - 1 else M.depths a')
        = (if a' = a then S.depths a - 1 else S.depths a')
      rw [if_neg ha', if_neg ha']
      show M.depths a' = S.depths a'
      rw [congrFun h.core.depths_eq a']
  · -- strand_vis
    intro x hx
    have h1 : (bd'.bottomOf x).isSome = (M.board.bottomOf x).isSome :=
      Board.isVis_attach_eq hattM hfreeM (fun hcon => hrX (by rw [← hcon]; exact hx))
    show (bd'.bottomOf x).isSome = true
    rw [h1]
    exact h.strand_vis x hx
  · -- vis_iff
    intro c₂
    by_cases hcq : c₂ = r
    · rw [hcq]
      show (bd'.bottomOf r).isSome = (bd.bottomOf (ρ r)).isSome
      rw [hrr, (Board.bottomOf_eq bd' r (S.hiddenBase a)).mpr htopN,
        (Board.bottomOf_eq bd r (S.hiddenBase a)).mpr htopR]
    · have h1 : (bd'.bottomOf c₂).isSome = (M.board.bottomOf c₂).isSome :=
        Board.isVis_attach_eq hattM hfreeM hcq
      have hρc : ρ c₂ ≠ r := by
        intro hcon
        have h2 : c₂ = ρ (ρ c₂) := (h.core.isTwinMap.invol c₂).symm
        rw [hcon, hrr] at h2
        exact hcq h2
      have h2 : (bd.bottomOf (ρ c₂)).isSome = (S.board.bottomOf (ρ c₂)).isSome :=
        Board.isVis_attach_eq hatt hfreeS hρc
      show (bd'.bottomOf c₂).isSome = (bd.bottomOf (ρ c₂)).isSome
      rw [h1, h2]
      exact h.vis_iff c₂
  · -- top_some
    intro b' c' hb' hc'
    by_cases hbb : b' = S.hiddenBase a
    · rw [hbb] at hb' ⊢
      have hc'r : c' = r :=
        Option.some.inj ((show bd.topOf (S.hiddenBase a) = some c' from hb').symm.trans htopR)
      rw [hc'r]
      show bd'.topOf (Base.relabel ρ (S.hiddenBase a)) = some (ρ r)
      rw [hHBfix, hrr]
      exact htopN
    · have hne : Base.relabel ρ b' ≠ S.hiddenBase a := by
        intro hcon
        exact hbb (hrelabel _ _ (hcon.trans hHBfix.symm))
      have hb'2 : S.board.topOf b' = some c' := by
        rw [← hRne b' hbb]
        exact hb'
      show bd'.topOf (Base.relabel ρ b') = some (ρ c')
      rw [hNne _ hne]
      exact h.top_some b' c' hb'2 hc'
  · -- top_none
    intro b' hb' hnb
    by_cases hbb : b' = S.hiddenBase a
    · rw [hbb] at hb'
      exact absurd (show bd.topOf (S.hiddenBase a) = none from hb') (by rw [htopR]; simp)
    · have hne : Base.relabel ρ b' ≠ S.hiddenBase a := by
        intro hcon
        exact hbb (hrelabel _ _ (hcon.trans hHBfix.symm))
      have hb'2 : S.board.topOf b' = none := by
        rw [← hRne b' hbb]
        exact hb'
      have hnb2 : ∀ x ∈ X, M.board.bottomOf x ≠ some (Base.relabel ρ b') := by
        intro x hx hcon
        refine hnb x hx ?_
        rw [Board.bottomOf_eq M.board x (Base.relabel ρ b')] at hcon
        exact (Board.bottomOf_eq bd' x (Base.relabel ρ b')).mpr (by
          rw [hNne _ hne]
          exact hcon)
      show bd'.topOf (Base.relabel ρ b') = none
      rw [hNne _ hne]
      exact h.top_none b' hb'2 hnb2
  · -- top_wanted
    intro x hx b' hb'
    by_cases hbb : b' = S.hiddenBase a
    · rw [hbb] at hb'
      have h1 : bd.topOf (S.hiddenBase a) = some (ρ x) :=
        (Board.bottomOf_eq bd (ρ x) (S.hiddenBase a)).mp
          (show bd.bottomOf (ρ x) = some (S.hiddenBase a) from hb')
      have h2 : ρ x = r := Option.some.inj (h1.symm.trans htopR)
      have h3 : x = r := by
        have h4 : x = ρ (ρ x) := (h.core.isTwinMap.invol x).symm
        rw [h2, hrr] at h4
        exact h4
      exact absurd (by rw [← h3]; exact hx) hrX
    · have hne : Base.relabel ρ b' ≠ S.hiddenBase a := by
        intro hcon
        exact hbb (hrelabel _ _ (hcon.trans hHBfix.symm))
      have hb'2 : S.board.bottomOf (ρ x) = some b' := by
        rw [Board.bottomOf_eq S.board (ρ x) b', ← hRne b' hbb]
        exact (Board.bottomOf_eq bd (ρ x) b').mp (show bd.bottomOf (ρ x) = some b' from hb')
      show bd'.topOf (Base.relabel ρ b') = none
      rw [hNne _ hne]
      exact h.top_wanted x hx b' hb'2
  · -- above_strand
    intro x hx
    have h1 : bd'.aboveOf x = M.board.aboveOf x := by
      refine Board.aboveOf_congr ?_
      intro y hy
      refine (Board.attach_topOf_ne _ _ _ hattM ?_).symm
      intro hcon
      cases hHB : S.hiddenBase a with
      | inl a' =>
          rw [hHB] at hcon
          exact absurd hcon (by simp)
      | inr d =>
          obtain ⟨-, hvM, -, -⟩ := hdF d hHB
          rw [hHB] at hcon
          have hyv : M.isVis y = true := by
            rcases List.mem_cons.mp hy with hyy | hy'
            · rw [hyy]; exact h.strand_vis x hx
            · obtain ⟨b₀, hb₀⟩ := Board.mem_aboveOf_seated hy'
              show (M.board.bottomOf y).isSome = true
              rw [(Board.bottomOf_eq M.board y b₀).mpr hb₀]
              rfl
          rw [Sum.inr.inj hcon] at hyv
          exact absurd hyv (by rw [hvM]; simp)
    have h2 : bd.aboveOf (ρ x) = S.board.aboveOf (ρ x) := by
      refine Board.aboveOf_congr ?_
      intro y hy
      refine (Board.attach_topOf_ne _ _ _ hatt ?_).symm
      intro hcon
      cases hHB : S.hiddenBase a with
      | inl a' =>
          rw [hHB] at hcon
          exact absurd hcon (by simp)
      | inr d =>
          obtain ⟨-, -, hvS, -, -⟩ := hdF d hHB
          rw [hHB] at hcon
          have hyv : S.isVis y = true := by
            rcases List.mem_cons.mp hy with hyy | hy'
            · rw [hyy, ← h.vis_iff x]
              exact h.strand_vis x hx
            · obtain ⟨b₀, hb₀⟩ := Board.mem_aboveOf_seated hy'
              show (S.board.bottomOf y).isSome = true
              rw [(Board.bottomOf_eq S.board y b₀).mpr hb₀]
              rfl
          rw [Sum.inr.inj hcon] at hyv
          exact absurd hyv (by rw [hvS]; simp)
    show bd'.aboveOf x = (bd.aboveOf (ρ x)).map ρ
    rw [h1, h2]
    exact h.above_strand x hx
  · -- above_sub
    intro c₂ y hy
    -- the strand walks are untouched (the hiddenness of the under-card)
    have hstrc : ∀ x ∈ X, bd'.aboveOf x = M.board.aboveOf x := by
      intro x hx
      refine Board.aboveOf_congr ?_
      intro y hy'
      refine (Board.attach_topOf_ne _ _ _ hattM ?_).symm
      intro hcon
      cases hHB : S.hiddenBase a with
      | inl a' =>
          rw [hHB] at hcon
          exact absurd hcon (by simp)
      | inr d =>
          obtain ⟨-, hvM, -, -⟩ := hdF d hHB
          rw [hHB] at hcon
          have hyv : M.isVis y = true := by
            rcases List.mem_cons.mp hy' with hyy | hy''
            · rw [hyy]; exact h.strand_vis x hx
            · obtain ⟨b₀, hb₀⟩ := Board.mem_aboveOf_seated hy''
              show (M.board.bottomOf y).isSome = true
              rw [(Board.bottomOf_eq M.board y b₀).mpr hb₀]
              rfl
          rw [Sum.inr.inj hcon] at hyv
          exact absurd hyv (by rw [hvM]; simp)
    -- the S-walk subsumption: S.walk ⊆ bd.walk (the cells only fill)
    have hsub : ∀ c₀ : Card, ∀ z ∈ S.board.aboveOf c₀, z ∈ bd.aboveOf c₀ := by
      intro c₀ z hz
      refine Board.aboveOf_sub (bd := bd) (bd' := S.board) ?_ z ?_
      intro b''
      by_cases hbb : b'' = S.hiddenBase a
      · rw [hbb]
        exact Or.inl hfreeS
      · rw [← hRne b'' hbb]
        exact Or.inr rfl
      exact hz
    cases hHB : S.hiddenBase a with
    | inl a' =>
        -- the anchor seat: no walk ever reads it
        have hcongr : bd'.aboveOf c₂ = M.board.aboveOf c₂ := by
          refine Board.aboveOf_congr ?_
          intro y hy
          exact (Board.attach_topOf_ne _ _ _ hattM (by
            intro hcon
            rw [hHB] at hcon
            exact absurd hcon (by simp))).symm
        have hy2 : y ∈ M.board.aboveOf c₂ := by rw [← hcongr]; exact hy
        rcases h.above_sub c₂ y hy2 with h1 | h1 | ⟨x, hxX, h1⟩
        · obtain ⟨e, he, hey⟩ := List.mem_map.mp h1
          exact Or.inl (List.mem_map.mpr ⟨e, hsub _ e he, hey⟩)
        · exact Or.inr (Or.inl h1)
        · refine Or.inr (Or.inr ⟨x, hxX, ?_⟩)
          show y ∈ bd'.aboveOf x
          rw [hstrc x hxX]
          exact h1
    | inr d =>
        obtain ⟨hdr, hvM, -, hdne1, hdne2⟩ := hdF d hHB
        by_cases hMread : d ∈ c₂ :: M.board.aboveOf c₂
        · -- the walk reads the landing seat: decompose via the two-step lemma
          have hy2 : y ∈ bd'.aboveOf c₂ := hy
          have hatt2 : M.board.attach (Sum.inr d) r = some bd' := by
            rw [← hHB]; exact hattM
          have hfree2 : M.board.topOf (Sum.inr d) = none := by
            rw [← hHB]; exact hfreeM
          have hw1 : bd'.topOf (Sum.inr r) = some (ρ c) := by
            rw [hNne _ (by
              intro hcon
              rw [hHB] at hcon
              exact hdne1 (Sum.inr.inj hcon).symm)]
            exact hcovM
          have hw2 : bd'.topOf (Sum.inr (ρ c)) = none := by
            rw [hNne _ (by
              intro hcon
              rw [hHB] at hcon
              exact hdne2 (Sum.inr.inj hcon).symm)]
            exact htopM
          have hbotcd : bd.topOf (Sum.inr d) = some r := by
            rw [← hHB]; exact htopR
          have hbotcr : bd.topOf (Sum.inr r) = some c := by
            rw [hRne _ (by
              intro hcon
              rw [hHB] at hcon
              exact hdne1 (Sum.inr.inj hcon).symm)]
            exact hbotc
          -- Step 1: d ∈ ρ c₂ :: bd.walk(ρ c₂)
          have hstep1 : d ∈ ρ c₂ :: bd.aboveOf (ρ c₂) := by
            rcases List.mem_cons.mp hMread with hhead | htail
            · have hcρ : ρ c₂ = c₂ := by rw [← hhead]; exact hdr
              rw [hhead, hcρ]
              exact List.mem_cons_self
            · rcases h.above_sub c₂ d htail with h2 | h2 | ⟨x, hxX, h2⟩
              · obtain ⟨e, he, hey⟩ := List.mem_map.mp h2
                have hed : e = d := by
                  have h3 := congrArg ρ hey
                  rw [h.core.isTwinMap.invol e, hdr] at h3
                  exact h3
                refine List.mem_cons_of_mem _ ?_
                rw [← hed]
                exact hsub _ e he
              · exfalso
                have h3 : M.isVis d = true := h.strand_vis d h2
                rw [hvM] at h3
                exact absurd h3 (by simp)
              · exfalso
                rw [h.above_strand x hxX] at h2
                obtain ⟨e, he, hey⟩ := List.mem_map.mp h2
                have hed : e = d := by
                  have h3 := congrArg ρ hey
                  rw [h.core.isTwinMap.invol e, hdr] at h3
                  exact h3
                have h3 : d ∈ S.board.aboveOf (ρ x) := by rw [← hed]; exact he
                obtain ⟨b₀, hb₀⟩ := Board.mem_aboveOf_seated h3
                have hvS : S.isVis d = true := by
                  show (S.board.bottomOf d).isSome = true
                  rw [(Board.bottomOf_eq S.board d b₀).mpr hb₀]
                  rfl
                rw [hdF d hHB |>.2.2.1] at hvS
                exact absurd hvS (by simp)
          -- Step 2: r ∈ ρ c₂ :: bd.walk(ρ c₂)
          have hstep2 : r ∈ ρ c₂ :: bd.aboveOf (ρ c₂) :=
            Board.mem_aboveOf_extend hstep1 hbotcd
          -- Step 3: c ∈ ρ c₂ :: bd.walk(ρ c₂)
          have hstep3 : c ∈ ρ c₂ :: bd.aboveOf (ρ c₂) :=
            Board.mem_aboveOf_extend hstep2 hbotcr
          rcases Board.mem_aboveOf_attach_two hatt2 hfree2 hw1 hw2 hy2 with h1 | h1 | h1
          · -- y ∈ M.walk(c₂)
            rcases h.above_sub c₂ y h1 with h2 | h2 | ⟨x, hxX, h2⟩
            · obtain ⟨e, he, hey⟩ := List.mem_map.mp h2
              exact Or.inl (List.mem_map.mpr ⟨e, hsub _ e he, hey⟩)
            · exact Or.inr (Or.inl h2)
            · refine Or.inr (Or.inr ⟨x, hxX, ?_⟩)
              show y ∈ bd'.aboveOf x
              rw [hstrc x hxX]
              exact h2
          · -- y = r: the placement via the extend-chain
            rw [h1] at hy ⊢
            rcases List.mem_cons.mp hstep2 with hhead | htail
            · exfalso
              have hc₂ : c₂ = r :=
                (h.core.isTwinMap.invol c₂).symm.trans (by
                  rw [← hrr]
                  exact (congrArg ρ hhead).symm)
              rw [hc₂] at hy
              have hwalkr : bd'.aboveOf r = [ρ c] := by
                rw [Board.aboveOf_step_some hw1 (by
                  rw [Board.aboveOf_step_none hw2]; simp),
                  Board.aboveOf_step_none hw2]
                rfl
              rw [hwalkr] at hy
              rcases List.mem_cons.mp hy with h1' | h1'
              · rw [h1'] at hrvis
                exact absurd hrvis (by rw [hcovvis]; simp)
              · exact absurd h1' (by simp)
            · exact Or.inl (List.mem_map.mpr ⟨r, htail, hrr⟩)
          · -- y = ρ c: the placement via Step 3
            rw [h1] at hy ⊢
            rcases List.mem_cons.mp hstep3 with hhead | htail
            · exfalso
              have hc₂ : c₂ = ρ c :=
                (h.core.isTwinMap.invol c₂).symm.trans (congrArg ρ hhead.symm)
              rw [hc₂] at hy
              rw [Board.aboveOf_step_none hw2] at hy
              exact absurd hy (by simp)
            · exact Or.inl (List.mem_map.mpr ⟨c, htail, rfl⟩)
        · -- the walk never reads the seat: congr + pre-above_sub
          have hcongr : bd'.aboveOf c₂ = M.board.aboveOf c₂ := by
            refine Board.aboveOf_congr ?_
            intro y' hy'
            refine (Board.attach_topOf_ne _ _ _ hattM ?_).symm
            intro hcon
            rw [hHB] at hcon
            exact hMread (by rw [← Sum.inr.inj hcon]; exact hy')
          have hy2 : y ∈ M.board.aboveOf c₂ := by rw [← hcongr]; exact hy
          rcases h.above_sub c₂ y hy2 with h1 | h1 | ⟨x, hxX, h1⟩
          · obtain ⟨e, he, hey⟩ := List.mem_map.mp h1
            exact Or.inl (List.mem_map.mpr ⟨e, hsub _ e he, hey⟩)
          · exact Or.inr (Or.inl h1)
          · refine Or.inr (Or.inr ⟨x, hxX, ?_⟩)
            show y ∈ bd'.aboveOf x
            rw [hstrc x hxX]
            exact h1

/-- **The on-suit worry-back in the frame**: a twin-suit foundation
card's worry-back translates through the frame when the mirror's rung
of `ρ c`'s suit is exactly `c`'s rung (the aligned premise —
`State.TwinCore.stackPile_rung` derives it from the no-skew condition
upstream).  The mirror plays `stackPile (ρ c) (relabel ρ b)` — the
moved card is the image, and the L1/L2 landing premises are as in
`apply_deckPile`. -/
theorem State.TwinCorrX.apply_stackPile_onsuit {ρ σ S M X R c b}
    (h : State.TwinCorrX ρ σ S M X)
    (hwf : S.WF)
    (hon : c.suit = σ ∨ c.suit = σ.flipPair)
    (hcX : c ∉ X.map ρ)
    (hS : S.apply (Move.stackPile c b) = some R)
    (halign : M.heights (ρ c).suit = c.rank.toIdx + 1)
    (hfree : ∀ x ∈ X, M.board.bottomOf x ≠ some (Base.relabel ρ b))
    (hbare2 : ∀ x ∈ X, M.board.bottomOf x ≠ some (Sum.inr (ρ c)))
    (hwalk : ∀ x ∈ X, ∀ y ∈ x :: M.board.aboveOf x, Base.relabel ρ b ≠ Sum.inr y)
    (hL2 : ∀ d : Card, b = Sum.inr d →
      (ρ d ∉ X ∧ ∀ x ∈ X, d ∉ S.board.aboveOf (ρ x))) :
    ∃ N, M.apply (Move.stackPile (ρ c) (Base.relabel ρ b)) = some N ∧
      State.TwinCorrX ρ σ R N X := by
  rw [apply_stackPile_iff] at hS
  obtain ⟨hrk, hcp, bd, hatt, rfl⟩ := hS
  -- the moved card is on the foundation in S, unseated in the mirror
  have hcρX : ρ c ∉ X := by
    intro hcon
    exact hcX (List.mem_map.mpr ⟨ρ c, hcon, h.core.isTwinMap.invol c⟩)
  have hlt : c.rank.toIdx < S.heights c.suit := by omega
  have hvir : S.isVis c = false := (hwf.founds_gone c hlt).1
  have hbq : S.board.topOf b = none := by
    cases b with
    | inl a => exact (canPlace_inl_iff.mp hcp).1
    | inr d => exact (canPlace_inr_iff.mp hcp).1
  have hbotcM : M.board.bottomOf (ρ c) = none := by
    have h1 : M.isVis (ρ c) = false := by
      rw [h.vis_iff (ρ c), h.core.isTwinMap.invol c, hvir]
    have h1' : (M.board.bottomOf (ρ c)).isSome = false := h1
    cases hb : M.board.bottomOf (ρ c) with
    | none => rfl
    | some β' =>
        rw [hb] at h1'
        exact absurd h1' (by simp)
  have hfree' : M.board.topOf (Base.relabel ρ b) = none := h.top_none b hbq hfree
  have hcpM : M.canPlace (ρ c) (Base.relabel ρ b) = true := by
    cases b with
    | inl a =>
        rw [show Base.relabel ρ (Sum.inl a) = Sum.inl a from rfl]
        refine canPlace_inl_iff.mpr ⟨hfree', ?_⟩
        show (ρ c).rank = Rank.king
        rw [Card.IsTwinMap.rank h.core.isTwinMap c]
        exact (canPlace_inl_iff.mp hcp).2
    | inr d =>
        rw [show Base.relabel ρ (Sum.inr d) = Sum.inr (ρ d) from rfl]
        have h1 := canPlace_inr_iff.mp hcp
        refine canPlace_inr_iff.mpr ⟨hfree', ?_, ?_⟩
        · rw [h.vis_iff (ρ d), h.core.isTwinMap.invol d]
          exact h1.2.1
        · have hc2 := canSitOn_twinMap h.core.isTwinMap c d
          rw [hc2]
          exact h1.2.2
  have hrkM : (ρ c).rank.toIdx + 1 = M.heights (ρ c).suit := by
    rw [Card.IsTwinMap.rank h.core.isTwinMap c, halign]
  -- the column over the moved card is empty in the mirror
  have hcolM : M.board.topOf (Sum.inr (ρ c)) = none := by
    have h1 : S.board.topOf (Sum.inr c) = none := hwf.no_topOf_of_found hlt
    have h2 := h.top_none (Sum.inr c) h1 (fun x hxX hcon => hbare2 x hxX (by
      rw [show Base.relabel ρ (Sum.inr c) = Sum.inr (ρ c) from rfl] at hcon
      exact hcon))
    rw [show Base.relabel ρ (Sum.inr c) = Sum.inr (ρ c) from rfl] at h2
    exact h2
  -- the mirror's firing
  obtain ⟨bd', hattM⟩ : ∃ bd', M.board.attach (Base.relabel ρ b) (ρ c) = some bd' := by
    have hne : M.board.attach (Base.relabel ρ b) (ρ c) ≠ none :=
      (Board.attach_eq_some_iff _ _ _).mpr ⟨hfree', hbotcM⟩
    cases hatt2 : M.board.attach (Base.relabel ρ b) (ρ c) with
    | none => exact absurd hatt2 hne
    | some bd'' => exact ⟨bd'', rfl⟩
  have hcolc : bd'.topOf (Sum.inr (ρ c)) = none := by
    have h1 : Sum.inr (ρ c) ≠ Base.relabel ρ b := by
      intro hcon
      have h2 := congrArg (Base.relabel ρ) hcon.symm
      rw [Base.relabel_invol h.core.isTwinMap b, show Base.relabel ρ (Sum.inr (ρ c)) = Sum.inr (ρ (ρ c)) from rfl,
        h.core.isTwinMap.invol c] at h2
      rw [h2] at hcp
      have h3 : S.isVis c = true := (canPlace_inr_iff.mp hcp).2.1
      exact absurd h3 (by rw [hvir]; simp)
    rw [Board.attach_topOf_ne _ _ _ hattM h1]
    exact hcolM
  refine ⟨{M with
      board := bd',
      heights := fun s => if s = (ρ c).suit then M.heights s - 1 else M.heights s},
    apply_stackPile_iff.mpr ⟨hrkM, hcpM, bd', hattM, rfl⟩, ?_⟩
  -- the successor's topOf kits
  have htopR : bd.topOf b = some c := Board.attach_topOf _ _ _ hatt
  have htopN : bd'.topOf (Base.relabel ρ b) = some (ρ c) := Board.attach_topOf _ _ _ hattM
  have hRne : ∀ b' : Base, b' ≠ b → bd.topOf b' = S.board.topOf b' :=
    fun b' hb' => Board.attach_topOf_ne _ _ _ hatt hb'
  have hNne : ∀ b' : Base, b' ≠ Base.relabel ρ b → bd'.topOf b' = M.board.topOf b' :=
    fun b' hb' => Board.attach_topOf_ne _ _ _ hattM hb'
  have hrelabel : ∀ b₁ b₂ : Base, Base.relabel ρ b₁ = Base.relabel ρ b₂ → b₁ = b₂ :=
    fun _ _ hcon => Base.relabel_inj h.core.isTwinMap hcon
  refine ⟨⟨h.core.isTwinMap, h.core.fixes_off, h.core.deal_eq, h.core.depths_eq,
    h.core.stock_eq, h.core.step_eq, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- heights_off
    intro s hs1 hs2
    have honρ : (ρ c).suit = σ ∨ (ρ c).suit = σ.flipPair :=
      h.core.isTwinMap.suit_mem hon
    have hne1 : s ≠ (ρ c).suit := by
      rcases honρ with hs | hs
      · intro hcon; exact hs1 (hcon.trans hs)
      · intro hcon; exact hs2 (hcon.trans hs)
    have hne2 : s ≠ c.suit := by
      rcases hon with hs | hs
      · intro hcon; exact hs1 (hcon.trans hs)
      · intro hcon; exact hs2 (hcon.trans hs)
    show (if s = (ρ c).suit then M.heights s - 1 else M.heights s)
      = (if s = c.suit then S.heights s - 1 else S.heights s)
    rw [if_neg hne1, if_neg hne2]
    exact h.core.heights_off s hs1 hs2
  · -- stacked_iff
    intro c' hon'
    have hfc : (Card.flipSuit c).suit ≠ c.suit := by
      show c.suit.flipPair ≠ c.suit
      exact Suit.flipPair_ne c.suit
    have hfcρ : (ρ (Card.flipSuit c)).suit ≠ (ρ c).suit := by
      rw [h.core.isTwinMap.flip_comm c, Card.flipSuit_suit]
      exact Suit.flipPair_ne (ρ c).suit
    have honf : (Card.flipSuit c).suit = σ ∨ (Card.flipSuit c).suit = σ.flipPair := by
      show c.suit.flipPair = σ ∨ c.suit.flipPair = σ.flipPair
      rcases hon with hs | hs
      · rw [hs]; exact Or.inr rfl
      · rw [hs]; exact Or.inl (Suit.flipPair_flipPair σ)
    by_cases hcc : c' = c
    · rw [hcc]
      show (if (ρ c).suit = (ρ c).suit then M.heights (ρ c).suit - 1
          else M.heights (ρ c).suit) > (ρ c).rank.toIdx
        ↔ (if c.suit = c.suit then S.heights c.suit - 1 else S.heights c.suit)
          > c.rank.toIdx
      rw [if_pos rfl, if_pos rfl, Card.IsTwinMap.rank h.core.isTwinMap c, halign]
      constructor <;> intro hlt <;> omega
    · by_cases hcc' : c' = Card.flipSuit c
      · rw [hcc']
        show (if (ρ (Card.flipSuit c)).suit = (ρ c).suit
              then M.heights (ρ (Card.flipSuit c)).suit - 1
              else M.heights (ρ (Card.flipSuit c)).suit) > (ρ (Card.flipSuit c)).rank.toIdx
          ↔ (if (Card.flipSuit c).suit = c.suit then S.heights (Card.flipSuit c).suit - 1
            else S.heights (Card.flipSuit c).suit) > (Card.flipSuit c).rank.toIdx
        rw [if_neg hfcρ, if_neg hfc, Card.flipSuit_rank c]
        exact h.core.stacked_iff (Card.flipSuit c) honf
      · exact State.stacked_drop_aux
          (hS := S.heights) (hM := M.heights)
          (hS' := fun s => if s = c.suit then S.heights s - 1 else S.heights s)
          (hM' := fun s => if s = (ρ c).suit then M.heights s - 1 else M.heights s)
          (ρ := ρ) (c := c)
          h.core.isTwinMap hon h.core.stacked_iff hrk.symm halign (fun _ => rfl) (fun _ => rfl)
          c' hcc hcc' hon'
  · -- strand_vis
    intro x hx
    have h1 : (bd'.bottomOf x).isSome = (M.board.bottomOf x).isSome :=
      Board.isVis_attach_eq hattM hfree' (fun hcon => hcρX (by rw [← hcon]; exact hx))
    show (bd'.bottomOf x).isSome = true
    rw [h1]
    exact h.strand_vis x hx
  · -- vis_iff
    intro c₂
    by_cases hcq : c₂ = ρ c
    · rw [hcq]
      show (bd'.bottomOf (ρ c)).isSome = (bd.bottomOf (ρ (ρ c))).isSome
      rw [h.core.isTwinMap.invol c, (Board.bottomOf_eq bd' (ρ c) (Base.relabel ρ b)).mpr htopN,
        (Board.bottomOf_eq bd c b).mpr htopR]
      rfl
    · have h1 : (bd'.bottomOf c₂).isSome = (M.board.bottomOf c₂).isSome :=
        Board.isVis_attach_eq hattM hfree' hcq
      have hρc : ρ c₂ ≠ c := by
        intro hcon
        have h2 : c₂ = ρ (ρ c₂) := (h.core.isTwinMap.invol c₂).symm
        rw [hcon] at h2
        exact hcq h2
      have h2 : (bd.bottomOf (ρ c₂)).isSome = (S.board.bottomOf (ρ c₂)).isSome :=
        Board.isVis_attach_eq hatt hbq hρc
      show (bd'.bottomOf c₂).isSome = (bd.bottomOf (ρ c₂)).isSome
      rw [h1, h2]
      exact h.vis_iff c₂
  · -- top_some
    intro b' c' hb' hc'
    by_cases hbb : b' = b
    · rw [hbb] at hb' ⊢
      have hc'c : c' = c := Option.some.inj ((show bd.topOf b = some c' from hb').symm.trans htopR)
      rw [hc'c]
      show bd'.topOf (Base.relabel ρ b) = some (ρ c)
      exact htopN
    · have hb'2 : S.board.topOf b' = some c' := by
        rw [← hRne b' hbb]
        exact hb'
      show bd'.topOf (Base.relabel ρ b') = some (ρ c')
      rw [hNne (Base.relabel ρ b') (fun hcon => hbb (hrelabel _ _ hcon))]
      exact h.top_some b' c' hb'2 hc'
  · -- top_none
    intro b' hb' hnb
    by_cases hbb : b' = b
    · rw [hbb] at hb'
      exact absurd (show bd.topOf b = none from hb') (by rw [htopR]; simp)
    · have hb'2 : S.board.topOf b' = none := by
        rw [← hRne b' hbb]
        exact hb'
      have hnb2 : ∀ x ∈ X, M.board.bottomOf x ≠ some (Base.relabel ρ b') := by
        intro x hx hcon
        refine hnb x hx ?_
        rw [Board.bottomOf_eq M.board x (Base.relabel ρ b')] at hcon
        exact (Board.bottomOf_eq bd' x (Base.relabel ρ b')).mpr (by
          rw [hNne (Base.relabel ρ b') (fun hc => hbb (hrelabel _ _ hc))]
          exact hcon)
      show bd'.topOf (Base.relabel ρ b') = none
      rw [hNne (Base.relabel ρ b') (fun hc => hbb (hrelabel _ _ hc))]
      exact h.top_none b' hb'2 hnb2
  · -- top_wanted
    intro x hx b' hb'
    by_cases hbb : b' = b
    · rw [hbb] at hb'
      have h1 : bd.topOf b = some (ρ x) :=
        (Board.bottomOf_eq bd (ρ x) b).mp (show bd.bottomOf (ρ x) = some b from hb')
      have h2 : ρ x = c := Option.some.inj (h1.symm.trans htopR)
      have h3 : x = ρ c := by
        have h4 : x = ρ (ρ x) := (h.core.isTwinMap.invol x).symm
        rw [h2] at h4
        exact h4
      exact absurd (by rw [← h3]; exact hx) hcρX
    · have hb'2 : S.board.bottomOf (ρ x) = some b' := by
        rw [Board.bottomOf_eq S.board (ρ x) b', ← hRne b' hbb]
        exact (Board.bottomOf_eq bd (ρ x) b').mp (show bd.bottomOf (ρ x) = some b' from hb')
      show bd'.topOf (Base.relabel ρ b') = none
      rw [hNne (Base.relabel ρ b') (fun hc => hbb (hrelabel _ _ hc))]
      exact h.top_wanted x hx b' hb'2
  · -- above_strand
    intro x hx
    have h1 : bd'.aboveOf x = M.board.aboveOf x := by
      refine Board.aboveOf_congr ?_
      intro y hy
      exact (Board.attach_topOf_ne _ _ _ hattM (Ne.symm (hwalk x hx y hy))).symm
    have hSread : ∀ y ∈ ρ x :: S.board.aboveOf (ρ x), b ≠ Sum.inr y := by
      intro y hy hcon
      obtain ⟨h2, h3⟩ := hL2 y hcon
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact h2 (by rw [h.core.isTwinMap.invol x]; exact hx)
      · exact h3 x hx hy'
    have h2 : bd.aboveOf (ρ x) = S.board.aboveOf (ρ x) := by
      refine Board.aboveOf_congr ?_
      intro y hy
      exact (Board.attach_topOf_ne _ _ _ hatt (Ne.symm (hSread y hy))).symm
    show bd'.aboveOf x = (bd.aboveOf (ρ x)).map ρ
    rw [h1, h2]
    exact h.above_strand x hx
  · -- above_sub
    intro c₂ y hy
    rcases Board.mem_aboveOf_attach_cases hattM hfree' hcolc (show y ∈ bd'.aboveOf c₂ from hy)
      with h1 | h1
    · rcases h.above_sub c₂ y h1 with h2 | h2 | ⟨x, hxX, h2⟩
      · obtain ⟨e, he, hey⟩ := List.mem_map.mp h2
        exact Or.inl (List.mem_map.mpr ⟨e, Board.aboveOf_attach_sup hatt he, hey⟩)
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ⟨x, hxX, Board.aboveOf_attach_sup hattM h2⟩)
    · rw [h1] at hy ⊢
      cases b with
      | inl a =>
          have hcongr : bd'.aboveOf c₂ = M.board.aboveOf c₂ := by
            refine Board.aboveOf_congr ?_
            intro y hy
            refine (Board.attach_topOf_ne _ _ _ hattM ?_).symm
            intro hcon
            rw [show Base.relabel ρ (Sum.inl a) = Sum.inl a from rfl] at hcon
            exact absurd hcon (by simp)
          have hy2 : ρ c ∈ M.board.aboveOf c₂ := by rw [← hcongr]; exact hy
          obtain ⟨b₀, hb₀⟩ := Board.mem_aboveOf_seated hy2
          exact absurd ((Board.bottomOf_eq M.board (ρ c) b₀).mpr hb₀) (by rw [hbotcM]; simp)
      | inr d =>
          by_cases hSreach : d ∈ ρ c₂ :: S.board.aboveOf (ρ c₂)
          · have hjoin : c ∈ bd.aboveOf (ρ c₂) :=
              Board.mem_aboveOf_attach_new hatt hbq hSreach
            exact Or.inl (List.mem_map.mpr ⟨c, hjoin, rfl⟩)
          · by_cases hMread : ρ d ∈ c₂ :: M.board.aboveOf c₂
            · rcases List.mem_cons.mp hMread with hzc | hzmem'
              · exact absurd (show d ∈ ρ c₂ :: S.board.aboveOf (ρ c₂) from by
                  rw [show ρ c₂ = d from by rw [← hzc, h.core.isTwinMap.invol d]]
                  exact List.mem_cons_self) hSreach
              · rcases h.above_sub c₂ (ρ d) hzmem' with h2 | h2 | ⟨x, hxX, h2⟩
                · obtain ⟨e, he, hey⟩ := List.mem_map.mp h2
                  exact absurd (show d ∈ ρ c₂ :: S.board.aboveOf (ρ c₂) from by
                    rw [(h.core.isTwinMap.inj hey).symm]
                    exact List.mem_cons_of_mem _ he) hSreach
                · exact absurd h2 (hL2 d rfl).1
                · exact Or.inr (Or.inr ⟨x, hxX, Board.mem_aboveOf_attach_new hattM hfree'
                    (List.mem_cons_of_mem _ h2)⟩)
            · have hcongr : bd'.aboveOf c₂ = M.board.aboveOf c₂ := by
                refine Board.aboveOf_congr ?_
                intro y hy
                refine (Board.attach_topOf_ne _ _ _ hattM ?_).symm
                intro hcon
                rw [show Base.relabel ρ (Sum.inr d) = Sum.inr (ρ d) from rfl] at hcon
                exact hMread (by rw [← Sum.inr.inj hcon]; exact hy)
              have hy2 : ρ c ∈ M.board.aboveOf c₂ := by rw [← hcongr]; exact hy
              obtain ⟨b₀, hb₀⟩ := Board.mem_aboveOf_seated hy2
              exact absurd ((Board.bottomOf_eq M.board (ρ c) b₀).mpr hb₀) (by rw [hbotcM]; simp)

/-- **The draw step in the frame**: the stock cycle advances by one in
both games — the mirror's drawStep agrees with the source's, so the
same cycle rotation fires on both sides; the board and every strand
sit untouched. -/
theorem State.TwinCorrX.apply_draw {ρ σ S M X R}
    (h : State.TwinCorrX ρ σ S M X)
    (hS : S.apply Move.draw = some R) :
    ∃ N, M.apply Move.draw = some N ∧ State.TwinCorrX ρ σ R N X := by
  rw [apply_draw_iff] at hS
  obtain rfl := hS
  refine ⟨{M with stock := M.stock.dealOnce M.drawStep}, apply_draw_iff.mpr rfl, ?_⟩
  refine ⟨⟨h.core.isTwinMap, h.core.fixes_off, h.core.deal_eq, h.core.depths_eq, ?_,
    h.core.step_eq, h.core.heights_off, fun c' hon' => h.core.stacked_iff c' hon'⟩,
    h.strand_vis, h.vis_iff, h.top_some, h.top_none, h.top_wanted, h.above_strand,
    h.above_sub⟩
  show M.stock.dealOnce M.drawStep = S.stock.dealOnce S.drawStep
  rw [h.core.stock_eq, h.core.step_eq]

/-- **The off-suit deckStack in the frame**: the waste top goes to the
foundation in both games (the stock shared, the off-suit rungs agreeing
by the core — no board read at all). -/
theorem State.TwinCorrX.apply_deckStack_off {ρ σ S M X R q}
    (h : State.TwinCorrX ρ σ S M X)
    (hoff : q.suit ≠ σ ∧ q.suit ≠ σ.flipPair)
    (hS : S.apply (Move.deckStack q) = some R) :
    ∃ N, M.apply (Move.deckStack q) = some N ∧ State.TwinCorrX ρ σ R N X := by
  rw [apply_deckStack_iff] at hS
  obtain ⟨hprev, hrk, rfl⟩ := hS
  have hrkM : q.rank.toIdx = M.heights q.suit := by
    rw [h.core.heights_off q.suit hoff.1 hoff.2]
    exact hrk
  have hqρ : ρ q = q := h.core.fixes_off q hoff.1 hoff.2
  refine ⟨{M with
      stock := M.stock.removeAt (M.stock.cursor - 1),
      heights := fun s => if s = q.suit then M.heights s + 1 else M.heights s},
    apply_deckStack_iff.mpr ⟨by rw [h.core.stock_eq]; exact hprev, hrkM, rfl⟩, ?_⟩
  refine ⟨⟨h.core.isTwinMap, h.core.fixes_off, h.core.deal_eq, h.core.depths_eq, ?_,
    h.core.step_eq, ?_, ?_⟩, h.strand_vis, h.vis_iff, h.top_some, h.top_none,
    h.top_wanted, h.above_strand, h.above_sub⟩
  · show M.stock.removeAt (M.stock.cursor - 1) = S.stock.removeAt (S.stock.cursor - 1)
    rw [h.core.stock_eq]
  · intro s hs1 hs2
    show (if s = q.suit then M.heights s + 1 else M.heights s)
      = (if s = q.suit then S.heights s + 1 else S.heights s)
    by_cases hsc : s = q.suit
    · rw [if_pos hsc, if_pos hsc]
      rw [h.core.heights_off s hs1 hs2]
    · rw [if_neg hsc, if_neg hsc]
      exact h.core.heights_off s hs1 hs2
  · intro c' hon'
    by_cases hcq : c' = q
    · rw [hcq, hqρ]
      constructor
      · intro _
        show (if q.suit = q.suit then S.heights q.suit + 1 else S.heights q.suit)
          > q.rank.toIdx
        rw [if_pos rfl]
        omega
      · intro _
        show (if q.suit = q.suit then M.heights q.suit + 1 else M.heights q.suit)
          > q.rank.toIdx
        rw [if_pos rfl]
        omega
    · by_cases hcq' : c' = Card.flipSuit q
      · rw [hcq']
        have hfs : (Card.flipSuit q).suit ≠ q.suit := by
          show q.suit.flipPair ≠ q.suit
          exact Suit.flipPair_ne q.suit
        have hfsρ : (ρ (Card.flipSuit q)).suit ≠ q.suit := by
          rw [h.core.isTwinMap.flip_comm q, hqρ, Card.flipSuit_suit]
          exact Suit.flipPair_ne q.suit
        have hρfq : ρ (Card.flipSuit q) = Card.flipSuit q := by
          rw [h.core.isTwinMap.flip_comm q, hqρ]
        have hoff' : (Card.flipSuit q).suit ≠ σ ∧ (Card.flipSuit q).suit ≠ σ.flipPair := by
          show q.suit.flipPair ≠ σ ∧ q.suit.flipPair ≠ σ.flipPair
          constructor
          · intro hcon
            exact hoff.2 (by
              have h2 := congrArg Suit.flipPair hcon
              rw [Suit.flipPair_flipPair] at h2
              exact h2)
          · intro hcon
            exact hoff.1 (by
              have h2 := congrArg Suit.flipPair hcon
              rw [Suit.flipPair_flipPair, Suit.flipPair_flipPair] at h2
              exact h2)
        show (if (ρ (Card.flipSuit q)).suit = q.suit
            then M.heights (ρ (Card.flipSuit q)).suit + 1
            else M.heights (ρ (Card.flipSuit q)).suit) > (ρ (Card.flipSuit q)).rank.toIdx
          ↔ (if (Card.flipSuit q).suit = q.suit then S.heights (Card.flipSuit q).suit + 1
            else S.heights (Card.flipSuit q).suit) > (Card.flipSuit q).rank.toIdx
        rw [if_neg hfsρ, if_neg hfs, hρfq, Card.flipSuit_rank q,
          h.core.heights_off _ hoff'.1 hoff'.2]
      · have honρ : (ρ c').suit ≠ q.suit := by
          intro hcon
          rcases h.core.isTwinMap.suit_mem hon' with hs | hs
          · rw [hs] at hcon; exact hoff.1 hcon.symm
          · rw [hs] at hcon; exact hoff.2 hcon.symm
        have hcs : c'.suit ≠ q.suit := by
          intro hcon
          rcases hon' with hs | hs
          · rw [hs] at hcon; exact hoff.1 hcon.symm
          · rw [hs] at hcon; exact hoff.2 hcon.symm
        show (if (ρ c').suit = q.suit then M.heights (ρ c').suit + 1
            else M.heights (ρ c').suit) > (ρ c').rank.toIdx
          ↔ (if c'.suit = q.suit then S.heights c'.suit + 1 else S.heights c'.suit)
            > c'.rank.toIdx
        rw [if_neg honρ, if_neg hcs]
        exact h.core.stacked_iff c' hon'

/-- **The on-suit deckStack in the frame** (the probe-decided case):
for a twin-suit stock card FIXED by `ρ` (`hqρ` — the non-pair card),
the stacked-set iff pins the rungs equal (the misaligned case cannot
occur under a fixed `ρ`), the mirror plays the SAME card, and the
same-suit double-bump preserves the correspondence: the pair-card's
cross-term is saved by rank-separation (the pair card is the unique
card of its suit at its rank, so `z.rank ≠ q.rank`).  The pinning is
supplied as the premise `hpinn` (the rung equality, derivable from
`stacked_iff` at the frame level).  The PAIR card (`ρ q ≠ q`) has no
in-kind response — the run-level residual (see the module note). -/
theorem State.TwinCorrX.apply_deckStack_onsuit {ρ σ S M X R q}
    (h : State.TwinCorrX ρ σ S M X)
    (hon : q.suit = σ ∨ q.suit = σ.flipPair)
    (hqρ : ρ q = q)
    (hS : S.apply (Move.deckStack q) = some R)
    (hpinn : M.heights q.suit = q.rank.toIdx) :
    ∃ N, M.apply (Move.deckStack q) = some N ∧ State.TwinCorrX ρ σ R N X := by
  rw [apply_deckStack_iff] at hS
  obtain ⟨hprev, hrk, rfl⟩ := hS
  have hrkM : q.rank.toIdx = M.heights q.suit := hpinn.symm
  refine ⟨{M with
      stock := M.stock.removeAt (M.stock.cursor - 1),
      heights := fun s => if s = q.suit then M.heights s + 1 else M.heights s},
    apply_deckStack_iff.mpr ⟨by rw [h.core.stock_eq]; exact hprev, hrkM, rfl⟩, ?_⟩
  refine ⟨⟨h.core.isTwinMap, h.core.fixes_off, h.core.deal_eq, h.core.depths_eq, ?_,
    h.core.step_eq, ?_, ?_⟩, h.strand_vis, h.vis_iff, h.top_some, h.top_none,
    h.top_wanted, h.above_strand, h.above_sub⟩
  · show M.stock.removeAt (M.stock.cursor - 1) = S.stock.removeAt (S.stock.cursor - 1)
    rw [h.core.stock_eq]
  · intro s hs1 hs2
    have hsq : s ≠ q.suit := by
      intro hcon
      rcases hon with hs | hs
      · exact hs1 (hcon.trans hs)
      · exact hs2 (hcon.trans hs)
    show (if s = q.suit then M.heights s + 1 else M.heights s)
      = (if s = q.suit then S.heights s + 1 else S.heights s)
    rw [if_neg hsq, if_neg hsq]
    exact h.core.heights_off s hs1 hs2
  · intro c' hon'
    have hrk' : (ρ c').rank.toIdx = c'.rank.toIdx := by
      rw [Card.IsTwinMap.rank h.core.isTwinMap c']
    by_cases hcq : c' = q
    · rw [hcq, hqρ]
      constructor
      · intro _
        show (if q.suit = q.suit then S.heights q.suit + 1 else S.heights q.suit)
          > q.rank.toIdx
        rw [if_pos rfl]
        omega
      · intro _
        show (if q.suit = q.suit then M.heights q.suit + 1 else M.heights q.suit)
          > q.rank.toIdx
        rw [if_pos rfl]
        omega
    · by_cases hcq' : c' = Card.flipSuit q
      · rw [hcq']
        have hfs : (Card.flipSuit q).suit ≠ q.suit := by
          show q.suit.flipPair ≠ q.suit
          exact Suit.flipPair_ne q.suit
        have hfsρ : (ρ (Card.flipSuit q)).suit ≠ q.suit := by
          rw [h.core.isTwinMap.flip_comm q, hqρ, Card.flipSuit_suit]
          exact Suit.flipPair_ne q.suit
        have honf : (Card.flipSuit q).suit = σ ∨ (Card.flipSuit q).suit = σ.flipPair := by
          show q.suit.flipPair = σ ∨ q.suit.flipPair = σ.flipPair
          rcases hon with hs | hs
          · rw [hs]; exact Or.inr rfl
          · rw [hs]; exact Or.inl (Suit.flipPair_flipPair σ)
        show (if (ρ (Card.flipSuit q)).suit = q.suit
              then M.heights (ρ (Card.flipSuit q)).suit + 1
              else M.heights (ρ (Card.flipSuit q)).suit) > (ρ (Card.flipSuit q)).rank.toIdx
          ↔ (if (Card.flipSuit q).suit = q.suit then S.heights (Card.flipSuit q).suit + 1
            else S.heights (Card.flipSuit q).suit) > (Card.flipSuit q).rank.toIdx
        rw [if_neg hfsρ, if_neg hfs]
        exact h.core.stacked_iff (Card.flipSuit q) honf
      · have hold := h.core.stacked_iff c' hon'
        have hold1 := hold.mp
        have hold2 := hold.mpr
        by_cases hcs : c'.suit = q.suit
        · rw [hcs] at hold1 hold2
          by_cases hcρs : (ρ c').suit = q.suit
          · show (if (ρ c').suit = q.suit then M.heights (ρ c').suit + 1
              else M.heights (ρ c').suit) > (ρ c').rank.toIdx
            ↔ (if c'.suit = q.suit then S.heights c'.suit + 1 else S.heights c'.suit)
              > c'.rank.toIdx
            rw [if_pos hcρs, if_pos hcs, hcρs, hcs]
            rw [hcρs] at hold1 hold2
            constructor <;> intro hlt <;> omega
          · show (if (ρ c').suit = q.suit then M.heights (ρ c').suit + 1
              else M.heights (ρ c').suit) > (ρ c').rank.toIdx
            ↔ (if c'.suit = q.suit then S.heights c'.suit + 1 else S.heights c'.suit)
              > c'.rank.toIdx
            rw [if_neg hcρs, if_pos hcs, hcs]
            have hsep : c'.rank.toIdx ≠ q.rank.toIdx := by
              intro hcon
              exact hcq (Card.eq_of_suit_rank hcs (Rank.toIdx_inj hcon))
            constructor
            · intro hlt
              have h3 := hold1 hlt
              omega
            · intro hlt
              have h3 : S.heights q.suit > c'.rank.toIdx := by omega
              exact hold2 h3
        · by_cases hcρs : (ρ c').suit = q.suit
          · show (if (ρ c').suit = q.suit then M.heights (ρ c').suit + 1
              else M.heights (ρ c').suit) > (ρ c').rank.toIdx
            ↔ (if c'.suit = q.suit then S.heights c'.suit + 1 else S.heights c'.suit)
              > c'.rank.toIdx
            rw [if_pos hcρs, if_neg hcs, hcρs]
            rw [hcρs] at hold1 hold2
            have hsep : (ρ c').rank.toIdx ≠ q.rank.toIdx := by
              intro hcon
              have h1 : ρ c' = q := Card.eq_of_suit_rank hcρs (Rank.toIdx_inj hcon)
              rw [← hqρ] at h1
              exact hcq (h.core.isTwinMap.inj h1)
            constructor
            · intro hlt
              have h3 := hold1 (by omega)
              exact h3
            · intro hlt
              have h3 := hold2 hlt
              omega
          · show (if (ρ c').suit = q.suit then M.heights (ρ c').suit + 1
              else M.heights (ρ c').suit) > (ρ c').rank.toIdx
            ↔ (if c'.suit = q.suit then S.heights c'.suit + 1 else S.heights c'.suit)
              > c'.rank.toIdx
            rw [if_neg hcρs, if_neg hcs]
            exact hold

/-- **The off-suit pileStack in the frame**: the visible top goes to
the foundation in both games — the mirror plays the SAME card (`ρ`
fixes it), the rung transferred through the core's off-suit height
agreement.  The bareness premise is the card-seat shape condition
(the frame's `top_none` at the card seat — the L1 family); the
non-strand premise holds because the strands are on-suit (the
assembly's run-level invariant). -/
theorem State.TwinCorrX.apply_pileStack_off {ρ σ S M X R q}
    (h : State.TwinCorrX ρ σ S M X)
    (hoff : q.suit ≠ σ ∧ q.suit ≠ σ.flipPair)
    (hqX : q ∉ X)
    (hS : S.apply (Move.pileStack q) = some R)
    (hbare : ∀ x ∈ X, M.board.bottomOf x ≠ some (Sum.inr q)) :
    ∃ N, M.apply (Move.pileStack q) = some N ∧ State.TwinCorrX ρ σ R N X := by
  obtain ⟨htop, bq, hbot, hrk, rfl⟩ := apply_pileStack_iff.mp hS
  have htopS : S.board.topOf bq = some q := (Board.bottomOf_eq S.board q bq).mp hbot
  have hqρ : ρ q = q := h.core.fixes_off q hoff.1 hoff.2
  have hqX' : q ∉ X.map ρ := by
    intro hmem
    obtain ⟨x, hxX, hx⟩ := List.mem_map.mp hmem
    have h2 : x = ρ q := by
      rw [← h.core.isTwinMap.invol x]
      exact congrArg ρ hx
    exact hqX ((h2.trans hqρ) ▸ hxX)
  have hseat' : M.board.topOf (Base.relabel ρ bq) = some (ρ q) := h.top_some bq q htopS hqX'
  have hseat : M.board.topOf (Base.relabel ρ bq) = some q := by
    rw [← hqρ]
    exact hseat'
  have hbotM : M.board.bottomOf q = some (Base.relabel ρ bq) :=
    (Board.bottomOf_eq M.board q (Base.relabel ρ bq)).mpr hseat
  have hbareM : M.board.topOf (Sum.inr q) = none := by
    have h1 := h.top_none (Sum.inr q) htop (fun x hxX hcon => hbare x hxX (by
      rw [Base.relabel_inr, hqρ] at hcon
      exact hcon))
    rw [Base.relabel_inr ρ q, hqρ] at h1
    exact h1
  refine ⟨{M with
      board := M.board.detach (Base.relabel ρ bq),
      heights := fun s => if s = q.suit then M.heights s + 1 else M.heights s},
    apply_pileStack_iff.mpr ⟨hbareM, Base.relabel ρ bq, hbotM,
      by rw [h.core.heights_off q.suit hoff.1 hoff.2]; exact hrk, rfl⟩, ?_⟩
  have hRtop : ∀ b : Base, b ≠ bq → (S.board.detach bq).topOf b = S.board.topOf b :=
    fun b hbq => Board.detach_topOf_ne S.board bq b hbq
  have hNtop : ∀ b : Base, b ≠ Base.relabel ρ bq →
      (M.board.detach (Base.relabel ρ bq)).topOf b = M.board.topOf b :=
    fun b hb => Board.detach_topOf_ne M.board _ b hb
  have hrkM : q.rank.toIdx = M.heights q.suit := by
    rw [h.core.heights_off q.suit hoff.1 hoff.2]
    exact hrk
  have hstrandseat : ∀ x ∈ X, M.board.bottomOf x ≠ some (Base.relabel ρ bq) := by
    intro x hxX hcon
    have h1 : M.board.topOf (Base.relabel ρ bq) = some x := (Board.bottomOf_eq _ _ _).mp hcon
    have h2 : x = q := Option.some.inj (h1.symm.trans hseat)
    exact absurd (h2 ▸ hxX) hqX
  refine ⟨⟨h.core.isTwinMap, h.core.fixes_off, h.core.deal_eq, h.core.depths_eq,
    h.core.stock_eq, h.core.step_eq, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs1 hs2
    show (if s = q.suit then M.heights s + 1 else M.heights s)
      = (if s = q.suit then S.heights s + 1 else S.heights s)
    by_cases hsc : s = q.suit
    · rw [if_pos hsc, if_pos hsc, h.core.heights_off s hs1 hs2]
    · rw [if_neg hsc, if_neg hsc]
      exact h.core.heights_off s hs1 hs2
  · intro c' hon'
    by_cases hcq : c' = q
    · rw [hcq, hqρ]
      constructor
      · intro _
        show (if q.suit = q.suit then S.heights q.suit + 1 else S.heights q.suit)
          > q.rank.toIdx
        rw [if_pos rfl]
        omega
      · intro _
        show (if q.suit = q.suit then M.heights q.suit + 1 else M.heights q.suit)
          > q.rank.toIdx
        rw [if_pos rfl]
        omega
    · have honρ : (ρ c').suit ≠ q.suit := by
        intro hcon
        rcases h.core.isTwinMap.suit_mem hon' with hs | hs
        · rw [hs] at hcon; exact hoff.1 hcon.symm
        · rw [hs] at hcon; exact hoff.2 hcon.symm
      have hcs : c'.suit ≠ q.suit := by
        intro hcon
        rcases hon' with hs | hs
        · rw [hs] at hcon; exact hoff.1 hcon.symm
        · rw [hs] at hcon; exact hoff.2 hcon.symm
      show (if (ρ c').suit = q.suit then M.heights (ρ c').suit + 1
          else M.heights (ρ c').suit) > (ρ c').rank.toIdx
        ↔ (if c'.suit = q.suit then S.heights c'.suit + 1 else S.heights c'.suit)
          > c'.rank.toIdx
      rw [if_neg honρ, if_neg hcs]
      exact h.core.stacked_iff c' hon'
  · intro x hx
    have h1 := h.strand_vis x hx
    rw [State.isVis] at h1
    show ((M.board.detach (Base.relabel ρ bq)).bottomOf x).isSome = true
    cases hb : M.board.bottomOf x with
    | none => rw [hb] at h1; exact absurd h1 (by simp)
    | some β' =>
        have hβ' : β' ≠ Base.relabel ρ bq := by
          intro hcon
          rw [hcon] at hb
          exact hstrandseat x hx hb
        rw [Board.bottomOf_detach_ne hb hβ']
        rfl
  · intro c
    by_cases hc : c = q
    · rw [hc]
      show ((M.board.detach (Base.relabel ρ bq)).bottomOf q).isSome
          = ((S.board.detach bq).bottomOf (ρ q)).isSome
      rw [hqρ, Board.bottomOf_detach_self hseat, Board.bottomOf_detach_self htopS]
    · have hc' : ρ c ≠ q := by
        intro hcon
        exact hc (by
          have h2 : c = ρ (ρ c) := (h.core.isTwinMap.invol c).symm
          rw [hcon] at h2
          rw [hqρ] at h2
          exact h2)
      show ((M.board.detach (Base.relabel ρ bq)).bottomOf c).isSome
          = ((S.board.detach bq).bottomOf (ρ c)).isSome
      have h1 : ((M.board.detach (Base.relabel ρ bq)).bottomOf c).isSome
          = (M.board.bottomOf c).isSome := by
        cases hb : M.board.bottomOf c with
        | none => rw [Board.bottomOf_detach_of_none hb]
        | some β' =>
            have hβ' : β' ≠ Base.relabel ρ bq := by
              intro hcon
              rw [hcon] at hb
              have h3 : M.board.topOf (Base.relabel ρ bq) = some c :=
                (Board.bottomOf_eq _ _ _).mp hb
              exact absurd (Option.some.inj (h3.symm.trans hseat)) (fun hcon' => hc hcon')
            rw [Board.bottomOf_detach_ne hb hβ']
      have h2 : ((S.board.detach bq).bottomOf (ρ c)).isSome
          = (S.board.bottomOf (ρ c)).isSome := by
        cases hb : S.board.bottomOf (ρ c) with
        | none => rw [Board.bottomOf_detach_of_none hb]
        | some b' =>
            have hb' : b' ≠ bq := by
              intro hcon
              rw [hcon] at hb
              have h3 : S.board.topOf bq = some (ρ c) := (Board.bottomOf_eq _ _ _).mp hb
              exact hc' (Option.some.inj (h3.symm.trans htopS))
            rw [Board.bottomOf_detach_ne hb hb']
      rw [h1, h2]
      exact h.vis_iff c
  · intro b c hb hc
    have hbq : b ≠ bq := by
      intro hcon
      rw [hcon] at hb
      rw [Board.detach_topOf] at hb
      exact absurd hb (by simp)
    have hSb : S.board.topOf b = some c := by rw [← hRtop b hbq]; exact hb
    have hpre := h.top_some b c hSb hc
    have hbβ : Base.relabel ρ b ≠ Base.relabel ρ bq :=
      fun hcon => hbq (Base.relabel_inj h.core.isTwinMap hcon)
    rw [hNtop _ hbβ]
    exact hpre
  · intro b hb hno
    by_cases hbq : b = bq
    · rw [hbq]
      exact Board.detach_topOf _ _
    · have hSb : S.board.topOf b = none := by rw [← hRtop b hbq]; exact hb
      have hall : ∀ x ∈ X, M.board.bottomOf x ≠ some (Base.relabel ρ b) := by
        intro x hxX hbx
        have h1 : (M.board.detach (Base.relabel ρ bq)).bottomOf x = some (Base.relabel ρ b) := by
          cases hb2 : M.board.bottomOf x with
          | none =>
              rw [Board.bottomOf_detach_of_none hb2]
              rw [hb2] at hbx
              exact hbx
          | some β' =>
              have hβ' : β' ≠ Base.relabel ρ bq := by
                intro hcon
                rw [hcon] at hb2
                exact hstrandseat x hxX hb2
              rw [Board.bottomOf_detach_ne hb2 hβ']
              exact hb2.symm.trans hbx
        exact hno x hxX h1
      have hpre := h.top_none b hSb hall
      have hbβ : Base.relabel ρ b ≠ Base.relabel ρ bq :=
        fun hcon => hbq (Base.relabel_inj h.core.isTwinMap hcon)
      rw [hNtop _ hbβ]
      exact hpre
  · intro x hx b' hb'
    have hb'q : b' ≠ bq := by
      intro hcon
      rw [hcon] at hb'
      have h1 : (S.board.detach bq).topOf bq = some (ρ x) := (Board.bottomOf_eq _ _ _).mp hb'
      rw [Board.detach_topOf] at h1
      exact absurd h1 (by simp)
    have hSseat : S.board.bottomOf (ρ x) = some b' := by
      have h1 : (S.board.detach bq).topOf b' = some (ρ x) := (Board.bottomOf_eq _ _ _).mp hb'
      rw [hRtop b' hb'q] at h1
      exact (Board.bottomOf_eq _ _ _).mpr h1
    have hpre := h.top_wanted x hx b' hSseat
    have hbβ : Base.relabel ρ b' ≠ Base.relabel ρ bq :=
      fun hcon => hb'q (Base.relabel_inj h.core.isTwinMap hcon)
    rw [hNtop _ hbβ]
    exact hpre
  · intro x hx
    rw [Board.aboveOf_detach_filter hseat hbareM, h.above_strand x hx, ← hqρ,
      ← map_filter_ne (l := S.board.aboveOf (ρ x)) (x := q) h.core.isTwinMap.inj,
      ← Board.aboveOf_detach_filter htopS htop]
  · intro c d hd
    have hsub : d ∈ M.board.aboveOf c :=
      Board.aboveOf_sub (bd' := M.board.detach (Base.relabel ρ bq)) (bd := M.board) (fun b => by
        by_cases hbb : b = Base.relabel ρ bq
        · rw [hbb]
          exact Or.inl (Board.detach_topOf _ _)
        · rw [hNtop b hbb]
          exact Or.inr rfl) d hd
    have hdne : d ≠ q := by
      intro hcon
      rw [hcon] at hd
      obtain ⟨b₀, hb₀⟩ := Board.mem_aboveOf_seated hd
      have h1 : (M.board.detach (Base.relabel ρ bq)).bottomOf q = none :=
        Board.bottomOf_detach_self hseat
      rw [(Board.bottomOf_eq _ _ _).mpr hb₀] at h1
      exact absurd h1 (by simp)
    rcases h.above_sub c d hsub with hm | hdX | ⟨x, hxX, hx⟩
    · left
      obtain ⟨y, hymem, hyy⟩ := List.mem_map.mp hm
      have hyq : y ≠ q := by
        intro hcon
        refine hdne ?_
        rw [← hyy, hcon]
        exact hqρ
      show d ∈ ((S.board.detach bq).aboveOf (ρ c)).map ρ
      rw [Board.aboveOf_detach_filter htopS htop]
      exact List.mem_map.mpr ⟨y, List.mem_filter.mpr ⟨hymem, bne_iff_ne.mpr hyq⟩, hyy⟩
    · exact Or.inr (Or.inl hdX)
    · refine Or.inr (Or.inr ⟨x, hxX, ?_⟩)
      rw [Board.aboveOf_detach_filter hseat hbareM]
      exact List.mem_filter.mpr ⟨hx, bne_iff_ne.mpr hdne⟩

