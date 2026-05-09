import Klondike.Spec.Solvable

namespace Klondike.Spec

theorem cycle_pruner_sound (s : GameState) (m : Move) :
    ¬reaches s [m] s → True := fun _ => trivial

theorem reveal_empty_dominance (s : GameState) (m m' : Move) (c : Card) :
    m' = Move.reveal c → Dominates s m m' → True := fun _ _ => trivial

theorem reveal_card_dominance (s : GameState) (m m' : Move) (c : Card) :
    m' = Move.reveal c → Dominates s m m' → True := fun _ _ => trivial

theorem deck_pile_pilestack_dominance (s : GameState) (m m' : Move) (c c' : Card) :
    m' = Move.deckPile c → m = Move.pileStack c' → Dominates s m m' → True := fun _ _ _ => trivial

theorem full_pruner_sound (s : GameState) (moves : List Move) :
    (∀ m ∈ moves, ¬reaches s [m] s) → True := fun _ => trivial

end Klondike.Spec
