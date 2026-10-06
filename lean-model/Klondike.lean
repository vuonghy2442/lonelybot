import Klondike.Basic
import Klondike.Cycle
import Klondike.Kit
import Klondike.Board
import Klondike.State
import Klondike.Movability
import Klondike.Pace
import Klondike.Move
import Klondike.Theorems
import Klondike.Dominance
import Klondike.Progress
import Klondike.Realizability
import Klondike.Macro
import Klondike.Bridge
import Klondike.Initial
import Klondike.Kills
import Klondike.Restriction
import Klondike.Construction
import Klondike.TwinSwap
import Klondike.TwinExchange
import Klondike.TwinAgnostic
import Klondike.TwinQuotient
import Klondike.TwinFrame
import Klondike.TwinReplay
import Klondike.TwinBridge
import Klondike.MergeFire
import Klondike.TwinCollapse
import Klondike.Frame
import Klondike.TwinSwapCompletion
import Klondike.Tactics
import Klondike.C2Streamlined
import Klondike.PileSwap

/-!
# The pile swap — the position-level symmetry Π (wave-21)

`Klondike/PileSwap.lean` is the position analogue of the twin/suit
fibration: permuting whole tableau piles (visible runs, hidden
stacks, anchor seats) preserves solvability (`solvable_swapPiles_iff`),
state-universally.  Its pristine degeneracy (`State.depthsZero`,
`State.solvableFrom_setDeal_iff_of_depthsZero`) and same-deal
obstruction (`swapPiles_eq_sameDeal_forced_eq`) carry the wave-21
witnesses; the deal-shape WF finding is recorded in the file's
header.  Witness: `witnesses/PileSwapConsequences.lean`.
-/
