import Klondike.Spec.Basic

namespace Klondike.Spec

inductive ExtraInfo where
  | none | revealEmpty | revealCard : Card → ExtraInfo
  deriving DecidableEq, Repr

inductive Move where
  | deckStack : Card → Move
  | pileStack : Card → Move
  | deckPile  : Card → Move
  | stackPile : Card → Move
  | reveal    : Card → Move
  deriving DecidableEq, Repr

namespace Move
def card : Move → Card
  | .deckStack c | .pileStack c | .deckPile c | .stackPile c | .reveal c => c
end Move

end Klondike.Spec
