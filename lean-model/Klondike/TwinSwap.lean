import Klondike.Dominance

/-!
# The twin pair at the play level — visibility, stacking, cargo

This file holds two proven theories.

**Visibility along a play** (§1): a tableau card's visibility is
anti-monotone under every move except its own `pileStack`
(`isVis_antimono`), every tableau card is stacked along a winning play
(`pileStack_mem_of_win`), and right before that stack the card is
visible and bare (`isVis_of_apply_pileStack`, `topOf_none_of_apply_pileStack`).
These are the "assume the game is solvable, hence you can get the card
to the foundation exactly when needed" facts, made into lemmas.

**The twin cargo transfer** (§2): the locking subtlety that killed the
seat-swap line (the twin's seat governs a hidden boundary's reveal —
swapping the seats moves the reveals, which is wrong) dissolves at the
cargo level: transfer only what sits ABOVE the twins.  There, physics is
one `pilePile` each way, and mutual reachability gives the equivalence.
Both directions are proven from the roundtrip.

Abandoned along the way (recorded in FARM.md's wave-14 note and its
witnesses): the seat-level automorphism and the apply-level conjugation.
`Move.swapTwin`/`State.swapTwin` stay as the substrate for
`witnesses/TwinSwapWitness.lean` (the legality-flip record).

Subsidiary facts proven here and used outside: `redundantTwins_heights_eq`
(the §5.5 redundant pair forces equal heights — feeds the Dominance
row's repair).
-/

/-- The local twin swap on moves: card arguments and card bases are
re-named.  Kept for the witness/regression layer. -/
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
cursor, and draw step stay put.  Not an automorphism (the legality-flip
is machine-checked in `witnesses/TwinSwapWitness.lean`): `heights`
stays fixed because suits are *shared* with non-swapped cards. -/
def State.swapTwin (t : Card) (st : State) : State where
  deal := { piles := fun a => (st.deal.piles a).map (Card.swapTwin t),
            stock := st.deal.stock.map (Card.swapTwin t) }
  board := st.board.mapByTwin t
  heights := st.heights
  depths := st.depths
  stock := { cards := st.stock.cards.map (Card.swapTwin t), cursor := st.stock.cursor }
  drawStep := st.drawStep

/-- The state-level involution: exchanging the pair twice is the
identity. -/
theorem State.swapTwin_swapTwin (t : Card) (st : State) :
    (st.swapTwin t).swapTwin t = st := by
  have mapTwin_id : ∀ l : List Card,
      (l.map (Card.swapTwin t)).map (Card.swapTwin t) = l := by
    intro l
    induction l with
    | nil => rfl
    | cons x xs ih =>
        simp only [List.map_cons, List.cons.injEq]
        exact ⟨Card.swapTwin_swapTwin t x, ih⟩
  obtain ⟨d0, b0, h0, dp0, s0, ds0⟩ := st
  apply state_ext
  · -- deal: two mapped layers cancel pointwise
    cases d0 with
    | mk piles stock =>
      show ({ piles := fun a => ((piles a).map (Card.swapTwin t)).map (Card.swapTwin t),
              stock := (stock.map (Card.swapTwin t)).map (Card.swapTwin t) } : Deal) = _
      have hp : (fun a => ((piles a).map (Card.swapTwin t)).map (Card.swapTwin t)) = piles := by
        funext a
        exact mapTwin_id (piles a)
      rw [hp, mapTwin_id]
  · apply Board.ext_topOf
    funext b
    simp [State.swapTwin, Board.mapByTwin]
    rw [show (t.swapTwin ∘ t.swapTwin) = id from funext (fun x => Card.swapTwin_swapTwin t x)]
    cases b0.topOf b <;> rfl
  · rfl
  · rfl
  · cases s0 with
    | mk cards cursor =>
      show ({ cards := ((cards.map (Card.swapTwin t)).map (Card.swapTwin t)),
                cursor := cursor } : Cycle Card) = _
      rw [mapTwin_id]
  · rfl

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

/-! ## §1. Visibility along a play: every tableau card is stacked in a win

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

/-! ## §2. The twin cargo transfer

The strategy content, the exact form it takes in this engine: re-seat
the run sitting on twin `t` onto `t.flipSuit`'s base by one `pilePile`,
return by another — `pilePile_roundtrip` proves the state is back
verbatim, so the two states are mutually reachable and equisolvable
(`solvable_iff_mutuallyReaches`, Progress.lean).  The remaining work is
the return move's legality, which is the farm's
`pilePile_return_legal` row; visible-twin licensure makes it go
through (details in its docstring). -/

/-- **The twin cargo-transfer equivalence, in its honest form**: when
the transfer's return move is legal, both transfers preserve
solvability. -/
theorem State.solvable_cargoTwin_transfer {st : State} {z t : Card} {st₁ : State}
    (h₀ : st.board.bottomOf z = some (Sum.inr t))
    (h₁ : st.apply (Move.pilePile z (Sum.inr t.flipSuit)) = some st₁)
    (hret : ∃ st₂, st₁.apply (Move.pilePile z (Sum.inr t)) = some st₂) :
    st₁.solvableFrom ↔ st.solvableFrom := by
  obtain ⟨st₂, hret⟩ := hret
  have h₂eq : st₂ = st := pilePile_roundtrip h₀ h₁ hret
  have hgo : st.run [Move.pilePile z (Sum.inr t.flipSuit)] = some st₁ := by
    simp only [State.run]
    cases hc : st.apply (Move.pilePile z (Sum.inr t.flipSuit)) with
    | none => rw [hc] at h₁; simp at h₁
    | some st' =>
      obtain rfl : st' = st₁ := Option.some.inj (hc.symm.trans h₁)
      rfl
  have hback : st₁.run [Move.pilePile z (Sum.inr t)] = some st₂ := by
    simp only [State.run]
    cases hc : st₁.apply (Move.pilePile z (Sum.inr t)) with
    | none => rw [hc] at hret; simp at hret
    | some st' =>
      obtain rfl : st' = st₂ := Option.some.inj (hc.symm.trans hret)
      rfl
  apply solvable_iff_mutuallyReaches
  · exact ⟨_, h₂eq ▸ hback⟩
  · exact ⟨_, hgo⟩

/-- The return legality module: the return `pilePile` of the transfer
goes through whenever the twins are both bare-visible — its premises
(`topOf` none at the origin base, `isVis` of the twin, `canSitOn` by
the body's hypotheses, run self-landing at an unchanged run) are
maintained by the transfer's own attachment/detachment machinery.

TODO(proof) [M]: invert the transfer iff for the return guards; the
run structure is untouched because the twins aren't in `z`'s run
(`pileOfTopHidden`-freeness licensed the case, derivable from WF; an
`aboveOf` reseat-invariance lemma makes it mechanical). -/
theorem State.pilePile_return_legal {st : State} {z t : Card} {st₁ : State}
    (hwf : st.WF) (hvis : st.isVis t = true) (hvis' : st.isVis t.flipSuit = true)
    (h₀ : st.board.bottomOf z = some (Sum.inr t))
    (h₁ : st.apply (Move.pilePile z (Sum.inr t.flipSuit)) = some st₁) :
    ∃ st₂, st₁.apply (Move.pilePile z (Sum.inr t)) = some st₂ := sorry
