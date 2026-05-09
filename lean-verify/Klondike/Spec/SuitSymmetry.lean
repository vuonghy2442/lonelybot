import Klondike.Spec.Basic

namespace Klondike.Spec

def rankColorSwap (r : Rank) (C : Color) (c : Card) : Card :=
  if c.rank = r ∧ c.suit.color = C then { c with suit := c.suit.swapSuit } else c

theorem rankColorSwap_preserves_rank (r : Rank) (C : Color) (c : Card) :
    (rankColorSwap r C c).rank = c.rank := by
  unfold rankColorSwap; split <;> rfl

theorem rankColorSwap_preserves_color (r : Rank) (C : Color) (c : Card) :
    (rankColorSwap r C c).suit.color = c.suit.color := by
  unfold rankColorSwap; split <;> simp [Suit.swapSuit_same_color]

theorem rankColorSwap_involution (r : Rank) (C : Color) (c : Card) :
    rankColorSwap r C (rankColorSwap r C c) = c := by
  sorry

theorem rankColorSwap_preserves_goesOnTopOf (r : Rank) (C : Color)
    {c c' : Card} (h : c.goesOnTopOf c') :
    (rankColorSwap r C c).goesOnTopOf (rankColorSwap r C c') := by
  sorry

end Klondike.Spec
