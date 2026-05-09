/-
Klondike.Move — Move types, legality, and state transitions.

This file defines the five move types in the optimized Klondike solver
and the state transition function. The moves correspond exactly to the
`Move` enum in src/moves.rs:

1. DeckStack  — Move a card from the stock to the foundation
2. PileStack  — Move a card from a tableau pile to the foundation
3. DeckPile   — Move a card from the stock to a tableau pile
4. StackPile  — Move a card from the foundation to a tableau pile
5. Reveal     — Move a top tableau card to another pile, revealing a hidden card

A key property: Reveal may also implicitly reveal the hidden card
underneath the moved card's source pile. This is captured by the
`ExtraInfo` type (corresponding to the Rust branch's new `ExtraInfo`).

We also define the concept of a "reverse move" — whether a move can
be undone by another legal move. This is central to the CyclePruner.
-/

namespace Klondike

open Basic

/-- Extra information about side effects of a move. -/
inductive ExtraInfo where
  | none        : ExtraInfo
  | revealEmpty : ExtraInfo  -- Reveal left an empty pile (no hidden card)
  | revealCard  : Card → ExtraInfo  -- Reveal uncovered a specific hidden card
  deriving DecidableEq, Repr

/-- The five move types in the optimized solver representation. -/
inductive Move where
  | deckStack : Card → Move
  | pileStack : Card → Move
  | deckPile  : Card → Move
  | stackPile : Card → Move
  | reveal    : Card → Move
  deriving DecidableEq, Repr

namespace Move

/-- Get the card involved in a move. -/
def card : Move → Card
  | deckStack c | pileStack c | deckPile c | stackPile c | reveal c => c

end Move

namespace GameState

/-- Remove the top card from a pile and optionally reveal the hidden card beneath. -/
def removeTopCard (p : TableauPile) : Option (Card × TableauPile × ExtraInfo) :=
  match p with
  | ⟨h, c :: rest⟩ =>
    let newPile :=
      match h with
      | []       => ⟨[], rest⟩
      | d :: dh  => ⟨dh, d :: rest⟩
    let extra :=
      match h with
      | []      => ExtraInfo.revealEmpty
      | d :: _  => ExtraInfo.revealCard d
    some (c, newPile, extra)
  | ⟨_, []⟩ => none

/-- Add a card to the top of a pile's visible cards. -/
def addCardToPile (p : TableauPile) (c : Card) : TableauPile :=
  ⟨p.hidden, c :: p.visible⟩

/-- Increment foundation for a suit. -/
def pushFoundation (f : Foundation) (suit : Suit) : Foundation :=
  fun s => if s = suit then f s + 1 else f s

/-- Decrement foundation for a suit. -/
def popFoundation (f : Foundation) (suit : Suit) : Foundation :=
  fun s => if s = suit then f s - 1 else f s

/--
Execute a move on the game state, returning the new state and extra info.
Returns `none` if the move is illegal.

This corresponds to `Solitaire::do_move` in the Rust code.
-/
def doMove (s : GameState) : Move → Option (GameState × ExtraInfo)
  | Move.deckStack c => do
    guard (s.canMoveToFoundation c)
    guard (s.deck.waste.head? = some c)
    let newDeck := { s.deck with waste := s.deck.waste.tail! }
    let newFoundation := s.pushFoundation c.suit
    some ({ s with foundation := newFoundation, deck := newDeck }, ExtraInfo.none)

  | Move.pileStack c => do
    guard (s.canMoveToFoundation c)
    let some pileIdx := s.findCardPile c | none
    let pile := s.piles pileIdx
    let some (c', newPile, extra) := removeTopCard pile | none
    guard (c' = c)
    let newFoundation := s.pushFoundation c.suit
    let newPiles := fun i => if i = pileIdx then newPile else s.piles i
    some ({ s with foundation := newFoundation, piles := newPiles }, extra)

  | Move.deckPile c => do
    guard (s.deck.waste.head? = some c)
    let some targetIdx := List.finFind? 7 (s.canMoveToPile · c) | none
    let newDeck := { s.deck with waste := s.deck.waste.tail! }
    let targetPile := s.piles targetIdx
    let newPile := addCardToPile targetPile c
    let newPiles := fun i => if i = targetIdx then newPile else s.piles i
    some ({ s with deck := newDeck, piles := newPiles }, ExtraInfo.none)

  | Move.stackPile c => do
    guard (s.foundation c.suit > 0)
    guard (s.foundationRank c.suit = some c.rank)
    let some targetIdx := List.finFind? 7 (s.canMoveToPile · c) | none
    let newFoundation := s.popFoundation c.suit
    let targetPile := s.piles targetIdx
    let newPile := addCardToPile targetPile c
    let newPiles := fun i => if i = targetIdx then newPile else s.piles i
    some ({ s with foundation := newFoundation, piles := newPiles }, ExtraInfo.none)

  | Move.reveal c => do
    let some pileIdx := s.findCardPile c | none
    guard (s.isLockedCard c)
    let some targetIdx := List.finFind? 7 fun i =>
      i ≠ pileIdx && s.canMoveToPile i c
    | none
    let pile := s.piles pileIdx
    let some (c', newSourcePile, extra) := removeTopCard pile | none
    guard (c' = c)
    let targetPile := s.piles targetIdx
    let newTargetPile := addCardToPile targetPile c
    let newPiles := fun i =>
      if i = pileIdx then newSourcePile
      else if i = targetIdx then newTargetPile
      else s.piles i
    some ({ s with piles := newPiles }, extra)

/--
Compute the reverse move: if move m is applied, can it be undone by
a legal move in the resulting state?

This corresponds to `Solitaire::reverse_move` in the Rust code.
A move is reversible unless it's a PileStack that reveals a hidden card
(that can't go back because the card above it on the pile is now different).

Key cases:
- DeckStack: not reversible (stock doesn't accept returns)
- PileStack: reversible iff the card was NOT locked (no hidden card revealed)
- DeckPile: not reversible (stock doesn't accept returns)
- StackPile: always reversible (can move back from pile to foundation)
- Reveal: reversible iff the source pile isn't empty after move
          (i.e., there's still a card to move back to)
-/
def reverseMove (s : GameState) : Move → Option Move
  | Move.pileStack c =>
    if s.isLockedCard c then none
    else some (Move.stackPile c)
  | Move.stackPile _ => some (Move.pileStack _) -- approximate: the reverse exists
  | Move.reveal c =>
    let some pileIdx := s.findCardPile c | none
    match s.piles pileIdx with
    | ⟨_ :: more, _⟩ => if more.isEmpty then none else some (Move.reveal c)
    | _ => none
  | _ => none

/--
A move is "irreversible" if it has no reverse in the resulting state.
Irreversible moves are the key decision points in the search.
-/
def isIrreversible (s : GameState) (m : Move) : Bool :=
  (reverseMove s m).isNone

end GameState

end Klondike
