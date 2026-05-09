import Klondike.Spec.Basic
import Klondike.Spec.GameState
import Klondike.Spec.Move

namespace Klondike.Spec

inductive reaches : GameState → List Move → GameState → Prop where
  | nil : reaches s [] s
  | cons (m : Move) (h : GameState.applyMove s m = some s') : reaches s' ms s'' → reaches s (m :: ms) s''

inductive Solvable : GameState → Prop where
  | win : GameState.isWin s → Solvable s
  | step (m : Move) (h : GameState.applyMove s m = some s') : Solvable s' → Solvable s

def Dominates (s : GameState) (m m' : Move) : Prop :=
  ∀ s', GameState.applyMove s m = some s' →
    GameState.applyMove s m' = some s' → False

end Klondike.Spec
