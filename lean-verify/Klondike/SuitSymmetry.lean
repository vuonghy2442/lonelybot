import Klondike.State

namespace Klondike

theorem swapSuit_preserves_goesOnTopOf (c c' : Card)
    (h : Card.goesOnTopOf c c') :
    Card.goesOnTopOf c.swapSuit c'.swapSuit := by sorry

end Klondike
