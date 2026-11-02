/-
  Orig2/ForkSeatTwinNoGo.lean  (scratch card; READ-ONLY on Orig2/)

  THE TWIN-BRACKET PREPARED SEAT IS IMPOSSIBLE FOR A NON-KING SEAT-MATE.

  Context.  `ForkFace1.cover_is_twin` says: in the `¬ Pullable B d (inr z)`
  face of a cross-suit corridor (the vision the brief calls the
  "prepared-seat" face), if `z` is face-up at the raise's image `B`, then the
  card `x` sitting directly on `z` is exactly `d.twin`.

  `ForkOffWindow.prepared_seat_single_slide_is_twin_exchange` then explains
  that slide as the twin exchange `slide d.twin : z -> z.twin` (a legal
  two-move seat relay), and the brief's shape is
      raise c ; slide d.twin ; pull d
  with `SeatMate c d`.

  This card proves that the two hypotheses CANNOT coexist when `c` is not a
  king: a non-king seat-mate of `c` with `c.suit ≠ d.suit` is `d = c.twin`,
  hence the cover `x = d.twin` is `c` itself — but `c` was just raised, so it
  is on the FOUNDATION at `B`, and `WF` forbids a card from being both founded
  and in a pile.  So no `ShufflePlayW` window can realise the twin bracket in
  the `inr` face: with `SeatMate` the prepared-seat face collapses to the
  KING / `inl` variant.

  Consequences for the search (see Temp/Search_Report.md):
  * the literal pattern `raise c ; slide d.twin ; pull d` with `SeatMate c d`
    is impossible in ANY witness play, saturated or not (for a king `d` the
    pull must be `inl`, so there is no `z` to slide off);
  * the exhaustive/random searches report 0 hits for that pattern, and the
    counterexample of Search_Report.md necessarily uses a NON-seat-mate pair.

  Battery at the tail; expected `[propext]` / `[propext, Quot.sound]`, no
  `sorryAx`, no `Classical.choice`, no `Lean.ofReduceBool`.
-/
import Orig2.ForkOffWindow

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace CrossSuitTwinNoGo

open CrossSuitF1

/-- **THE PREPARED-SEAT TWIN COVER IS THE FOUNDED CARD.**  In the
`¬ Pullable B d (inr z)` face with `SeatMate c d`, `c` not a king and
`c.suit ≠ d.suit`, the cover of `z` is `c` itself. -/
theorem cover_eq_raised_of_seatMate
    {A B P C0 : State} {γ : List Move} {c d z : Card}
    (hAwf : A.WF)
    (hstepR : State.step A (Move.tabToFound c) = some B)
    (hγ : ShufflePlayW B γ P) (hfree : Canon.FreeOnly γ)
    (hfire : State.step P (Move.foundToTab d (Sum.inr z)) = some C0)
    (hB : ¬ PullKit.Pullable B d (Sum.inr z))
    (hface : ∃ a0 : Anchor, z ∈ (B.piles a0).faceUp)
    (hsm : SeatMate c d) (hk : c.rank ≠ Rank.king) (hsu : c.suit ≠ d.suit) :
    ∃ (front rest : List Card) (a0 : Anchor),
      (B.piles a0).faceUp = front ++ z :: c :: rest := by
  have hBwf : B.WF := step_wf hAwf hstepR
  obtain ⟨x, front, rest, a0, hsplit, hx⟩ :=
    cover_is_twin hBwf hγ hfree hfire hB hface
  -- a non-king seat-mate with a different suit is the twin
  have hd : d = c.twin := by
    rcases hsm with ⟨hck, -⟩ | ⟨-, hd | hd⟩
    · exact absurd hck hk
    · rw [hd] at hsu; exact absurd rfl hsu
    · exact hd
  have hx' : x = c := by rw [hx, hd, card_twin_twin]
  exact ⟨front, rest, a0, by rw [hsplit, hx']⟩

/-- **THE PREPARED-SEAT TWIN BRACKET IS IMPOSSIBLE FOR A NON-KING SEAT-MATE.**
The corridor shape of `Blocks.NoSeatMateCrossSuit` cannot have `¬ Pullable` at
the raise's image when the two cards are non-king seat-mates: `c` would have to
be both founded (it was raised) and inside the run of `z`. -/
theorem no_twin_prepared_seat
    {A B P C0 : State} {γ : List Move} {c d z : Card}
    (hAwf : A.WF)
    (hstepR : State.step A (Move.tabToFound c) = some B)
    (hγ : ShufflePlayW B γ P) (hfree : Canon.FreeOnly γ)
    (hfire : State.step P (Move.foundToTab d (Sum.inr z)) = some C0)
    (hB : ¬ PullKit.Pullable B d (Sum.inr z))
    (hface : ∃ a0 : Anchor, z ∈ (B.piles a0).faceUp)
    (hsm : SeatMate c d) (hk : c.rank ≠ Rank.king) (hsu : c.suit ≠ d.suit) :
    False := by
  obtain ⟨front, rest, a0, hsplit⟩ :=
    cover_eq_raised_of_seatMate hAwf hstepR hγ hfree hfire hB hface hsm hk hsu
  have hBwf : B.WF := step_wf hAwf hstepR
  -- `c` sits in pile `a0`'s face-up run at `B`
  have hcpile : c ∈ pileZone B a0 := by
    show c ∈ (B.piles a0).hidden ++ (B.piles a0).faceUp
    rw [hsplit]
    exact List.mem_append.mpr
      (Or.inr (List.mem_append.mpr
        (Or.inr (List.mem_cons_of_mem z (List.mem_cons_self ..)))))
  -- and `c` is founded at `B`
  obtain ⟨_, _, _, hsB⟩ := step_tabToFound_inv hstepR
  have hcfound : c ∈ B.found c.suit := by
    have hfound : B.found c.suit = A.found c.suit ++ [c] :=
      (tabToFound_found_trio hsB).1
    rw [hfound]
    exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
  exact wf_pile_found_ne hBwf hcpile hcfound

/-- **THE TWIN EXCHANGE WINDOW IS NOT A SEAT-MATE CORRIDOR (SHAPE FORM).**  At
the `TwinExchangeWindow` shape the window's slide moves `p` out of pile `a`;
if the corridor's raised card `c` is the non-king seat-mate of the pulled card
`d`, then `p = d.twin = c`, so the slide would have to move the already-founded
card `c`.  We record the resulting identity `p = c` — it is incompatible with
`c` being founded at the window's start, which is the corridor hypothesis. -/
theorem twinExchange_cover_eq_seatMate
    {B C Pv : State} {a : Anchor} {front rest : List Card} {p z d c : Card}
    (hW : OffWindow.TwinExchangeWindow B C Pv a front rest p z d)
    (hp : p = d.twin)
    (hsm : SeatMate c d) (hk : c.rank ≠ Rank.king) (hsu : c.suit ≠ d.suit) :
    p = c := by
  have hd : d = c.twin := by
    rcases hsm with ⟨hck, -⟩ | ⟨-, hd | hd⟩
    · exact absurd hck hk
    · rw [hd] at hsu; exact absurd rfl hsu
    · exact hd
  rw [hp, hd, card_twin_twin]

end CrossSuitTwinNoGo

#print axioms CrossSuitTwinNoGo.cover_eq_raised_of_seatMate
#print axioms CrossSuitTwinNoGo.no_twin_prepared_seat
#print axioms CrossSuitTwinNoGo.twinExchange_cover_eq_seatMate
