import Orig.Basic
import Orig.State
import Orig.Play

/-!
# Orig2.Model — THE SEAM

The rebuild library's only sanctioned import surface (the
`Orig2.lean` root charter's seam policy): the GAME-MODEL FOUNDATION
— the board, the cards, the piles, the moves, the step relation,
the run algebra (`Orig.Play`) — everything beneath the
class-grade content, certified and shared with the frozen `Orig`
tier.  The reversibility carrier was seam-carried from `Orig.Fate`
until the 2026-10-17 review: it is now registry-owned
(`Orig2/Vocab.lean` §1.5, ported verbatim from `Orig/Fate.lean:92`),
so the seam is exactly the certified game core.

Everything above this file (the class notion, witness journeys,
detection, censuses, the programs) is defined FRESH inside `Orig2`
to the owner-approved intent lines (see the root charter's
registry).  The frozen `Orig` macro tier imports only via
explicitly recorded override entries in the root — none yet.

House compliance: additive file below the certified foundation;
no fresh heads here (a pure seam), so no battery section; zero
`sorry`; zero `Classical.choice`.
-/
