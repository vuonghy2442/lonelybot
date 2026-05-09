import Klondike.State

namespace Klondike

def legalMoves (s : Solitaire) : MoveMask := sorry

def moveInMask (mv : Move) (mask : MoveMask) : Prop :=
  match mv with
  | .pileStack c => (mask.pileStack &&& Card.mask c) ≠ 0
  | .deckStack c => (mask.deckStack &&& Card.mask c) ≠ 0
  | .stackPile c => (mask.stackPile &&& Card.mask c) ≠ 0
  | .deckPile c => (mask.deckPile &&& Card.mask c) ≠ 0
  | .reveal c => (mask.reveal &&& Card.mask c) ≠ 0

inductive Solvable : Solitaire → Prop where
  | win (s : Solitaire) (h : Solitaire.isWin s = true) : Solvable s
  | step (s : Solitaire) (mv : Move) (h : moveInMask mv (legalMoves s))
      (s' : Solitaire) (h2 : (s.doMove mv).2.2 = s') : Solvable s' → Solvable s

theorem gen_moves_sound (s : Solitaire) (mv : Move)
    (h : moveInMask mv (Solitaire.genMoves true s)) :
    moveInMask mv (legalMoves s) := sorry

theorem gen_moves_complete (s : Solitaire) (mv : Move)
    (h : moveInMask mv (legalMoves s)) :
    moveInMask mv (Solitaire.genMoves true s) := sorry

end Klondike
