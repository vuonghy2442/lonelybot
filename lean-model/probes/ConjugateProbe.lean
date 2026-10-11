import Orig.Canonical

/-! # The conjugation probe — the corrected composite's anatomy, witnessed

Probe-first battery for the `Orig/ConjugateProof.lean` card (the
corrected `conjugateForkState` composite at macro-game 07247ec).  Four
concrete boards settle every handwavy seat-package claim before any
proof is written; every gate is a `#eval` reading the game layer's own
decidable guards (`State.step`, `canRaiseB`, `Card.universe`):

* **(A) THE CANONICAL SWAP** — both twins seated (the V3 seat
  packages): the raise–slide–pull composite fires exactly at the
  docstring bases, and the ENDPOINT'S ONLY RAISER IS THE ORIGINAL
  WITNESS x (NOT x.twin — the banked `conjugate_endpoint_witness`
  row's behavior, here witnessed at the corrected composite): Q♠
  raises at w, Q♣ stays covered.  For contrast: the §3 one-leg slide
  of the cover J♦ off Q♣ onto Q♠ DOES flip the license to Q♣ — the
  mate is the slide, never the conjugate.
* **(B) THE (Q,J) CORNER** — x.twin BARE-BOTTOM non-king (the seat
  package's failure shape): the composite still FIRES (x lands on the
  exposed second (x+1) elsewhere — the rank packing leaves nothing
  else), but the endpoint carries TWO raisers (both twins
  exposed-with-seats) — NOT a forkState.  The seat package is exactly
  what the conjugation theorem must carry as its premise.
* **(C) THE FLOATING-COVERED FIRING** — x.twin covered but
  UNSEATED (bottom of its face-up run, empty hidden, non-king): the
  composite fires with a DISPLACED bb (x lands on the exposed second
  (x+1) at a third pile, since x.twin's emptied pile holds no base),
  and the endpoint is STILL a forkState-shaped board with the original
  witness live.  This refutes the literal necessity reading of the
  user iff ("fires ⟹ both twins seated") — the honest forward is the
  (Q,J)-corner row: an UNSEATED EXPOSED non-king twin can never land a
  forkState endpoint.
* **(D) THE KING CHANNEL** — the pair at rank 12, x a bare king and
  x.twin a covered king at the bottom of a hidden-less pile: the
  composite fires through the empty-anchor letters both ways
  (`ba = Sum.inl p0`, `bb = Sum.inl p1`), and the endpoint witnesses
  x again.

Rank arithmetic everywhere: `toIdx` is ace = 0 (Basic.lean), twins
share rank and COLOR (spade↔club, heart↔diamond), `canSitOn` is
rank+1 and color-differ, and the (x+1) cards of x's opposite color
are EXACTLY TWO — the packing the conjugate's forced-base claims ride.
-/

/-- The card shorthand. -/
def c_ (s : Suit) (r : Rank) : Card := Card.mk s r

/-- The pile shorthand. -/
def P (h f : List Card) : Pile := ⟨h, f⟩

/-- The leftover stock after a used-prefix board (conservation leg of
the probe's honesty: the used cards counted once, the rest stocked). -/
def restOf (used : List Card) : List Card :=
  Card.universe.filter (fun c => !(used.contains c))

/-- The used cards are pairwise distinct and together with the
stocked rest they account for all 52. -/
def censusOK (used : List Card) : Bool :=
  used.all (fun c => used.count c == 1) &&
  used.length + (restOf used).length == 52

/-- The full-universe raiser census: exactly the listed cards raise. -/
def raisers (st : State) : List Card :=
  Card.universe.filter (fun c => canRaiseB st c)

/-- The only-raiser gate: the census is exactly the singleton [x]. -/
def onlyRaiser (st : State) (x : Card) : Bool := raisers st == [x]

/-- The built state from founds, piles (the stocked rest implied). -/
def mkSt (found : Suit → List Card) (piles : Anchor → Pile)
    (used : List Card) : State :=
  ⟨found, piles, restOf used, [], 1⟩

/-! ## (A) The canonical swap: both twins seated -/

/-- The pair: Q♠ over K♥ at p0; Q♣ over K♦ covered by J♦ at p1;
the black suits' rungs pinned at 11 (Q next-up both), red rungs at 0. -/
def QA : Card := c_ .spade .queen
def QAc : Card := c_ .club .queen
def KH : Card := c_ .heart .king
def KD : Card := c_ .diamond .king
def JD : Card := c_ .diamond .jack
def JH : Card := c_ .heart .jack

def foundA : Suit → List Card
  | .spade => Suit.spade.upCards.take 11
  | .club => Suit.club.upCards.take 11
  | _ => []

def pilesA : Anchor → Pile
  | .p0 => P [] [KH, QA]
  | .p1 => P [] [KD, QAc, JD]
  | _ => P [] []

def usedA : List Card :=
  foundA .spade ++ foundA .club ++
  (pilesA .p0).faceUp ++ (pilesA .p1).faceUp

def stA : State := mkSt foundA pilesA usedA

#eval censusOK usedA                                          -- true — 27 used, 25 stocked
#eval onlyRaiser stA QA                                      -- true — st is the forkState shape, witness x = Q♠
#eval canRaiseB stA QAc                                      -- false — the twin is covered, not a pile top

/-- The composite, step by step: raise x, slide x.twin's run onto x's
exposed base z₀ = K♥, pull x back onto x.twin's exposed base
z₁ = K♦. -/
def st1A : State := ((State.step stA (Move.tabToFound QA)).getD stA)
def st2A : State := ((State.step st1A (Move.tabToTab QAc (Sum.inr KH))).getD st1A)
def stwA : State := ((State.step st2A (Move.foundToTab QA (Sum.inr KD))).getD st2A)

#eval (State.step stA (Move.tabToFound QA)).isSome             -- true
#eval st1A.piles Anchor.p0 == P [] [KH]                          -- true — the vacated seat exposes z₀
#eval (st1A.found Suit.spade).length == 12                      -- true — rung +1
#eval st2A.piles Anchor.p0 == P [] [KH, QAc, JD]                 -- true — the whole segment rode
#eval st2A.piles Anchor.p1 == P [] [KD]                         -- true — z₁ exposed
#eval (State.step st2A (Move.foundToTab QA (Sum.inr KD))).isSome -- true
#eval stwA.piles Anchor.p0 == P [] [KH, QAc, JD]                 -- true
#eval stwA.piles Anchor.p1 == P [] [KD, QA]                     -- true — the seats swapped
#eval (stwA.found Suit.spade).length == 11                      -- true — net-flat
#eval onlyRaiser stwA QA                                       -- TRUE HEADLINE — w is a forkState, witness STILL x (NOT x.twin)
#eval canRaiseB stwA QAc                                       -- false — the twin arrived covered at x's old seat

/-- The §3 mate contrast: one direct slide of the cover J♦ onto Q♠
flips the license to x.twin — the mate is the slide, never the
conjugate. -/
def mateA : State := ((State.step stA (Move.tabToTab JD (Sum.inr QA))).getD stA)
#eval (State.step stA (Move.tabToTab JD (Sum.inr QA))).isSome   -- true
#eval onlyRaiser mateA QAc                                     -- true — the SLIDE lands the x.twin-witness mate

/-! ## (B) The (Q,J) corner: the unseated bare-bottom twin -/

/-- Q♣ bare-bottom at p1 (no under-seat, non-king — the V3 falsifier
shape); the second red king K♦ floats exposed at p2 to receive the
pulled-back x. -/
def pilesB : Anchor → Pile
  | .p0 => P [] [KH, QA]
  | .p1 => P [] [QAc]
  | .p2 => P [] [KD]
  | _ => P [] []

def usedB : List Card :=
  foundA .spade ++ foundA .club ++
  (pilesB .p0).faceUp ++ (pilesB .p1).faceUp ++ (pilesB .p2).faceUp

def stB : State := mkSt foundA pilesB usedB

#eval censusOK usedB                                           -- true
#eval onlyRaiser stB QA                                        -- true — forkState shape; the seat is Q♣'s only failure
#eval canRaiseB stB QAc                                        -- false — the (Q,J) corner: next-up, bare, non-king

def st1B : State := ((State.step stB (Move.tabToFound QA)).getD stB)
def st2B : State := ((State.step st1B (Move.tabToTab QAc (Sum.inr KH))).getD st1B)
def stwB : State := ((State.step st2B (Move.foundToTab QA (Sum.inr KD))).getD st2B)

#eval (State.step stB (Move.tabToFound QA)).isSome               -- true — step 1 fires
#eval (State.step st1B (Move.tabToTab QAc (Sum.inr KH))).isSome -- true — step 2 fires (the bare twin rides alone)
#eval st2B.piles Anchor.p0 == P [] [KH, QAc]                    -- true
#eval st2B.piles Anchor.p1 == P [] []                          -- true — the corner pile is emptied, no flip (hidden was [])
#eval (State.step st2B (Move.foundToTab QA (Sum.inr KD))).isSome -- true — step 3 fires: DISPLACED onto K♦ at p2
#eval stwB.piles Anchor.p2 == P [] [KD, QA]                     -- true
#eval raisers stwB == [QA, QAc]                                 -- true — TWO raisers: the endpoint is NOT a forkState

/-! ## (C) The floating-covered firing: covered but UNSEATED twin -/

/-- Q♣ covered by J♥ but at the BOTTOM of its face-up run with empty
hidden (under-seat fails, non-king): the composite fires with bb
DISPLACED (x lands on the exposed second (x+1) K♦ at p2 — x.twin's
emptied pile holds no base), and the endpoint still witnesses x. -/
def pilesC : Anchor → Pile
  | .p0 => P [] [KH, QA]
  | .p1 => P [] [QAc, JH]
  | .p2 => P [] [KD]
  | _ => P [] []

def usedC : List Card :=
  foundA .spade ++ foundA .club ++
  (pilesC .p0).faceUp ++ (pilesC .p1).faceUp ++ (pilesC .p2).faceUp

def stC : State := mkSt foundA pilesC usedC

#eval censusOK usedC                                           -- true
#eval onlyRaiser stC QA                                        -- true — forkState shape; the twin is covered, seat or not

def st1C : State := ((State.step stC (Move.tabToFound QA)).getD stC)
def st2C : State := ((State.step st1C (Move.tabToTab QAc (Sum.inr KH))).getD st1C)
def stwC : State := ((State.step st2C (Move.foundToTab QA (Sum.inr KD))).getD st2C)

#eval (State.step st1C (Move.tabToTab QAc (Sum.inr KH))).isSome  -- true — the covered unseated twin still rides
#eval st2C.piles Anchor.p0 == P [] [KH, QAc, JH]                -- true
#eval st2C.piles Anchor.p1 == P [] []                          -- true — emptied (no flip: hidden was [])
#eval (State.step st2C (Move.foundToTab QA (Sum.inr KD))).isSome -- true — the DISPLACED landing (K♦ at p2)
#eval stwC.piles Anchor.p1 == P [] []                          -- true — the emptied pile never refilled
#eval stwC.piles Anchor.p2 == P [] [KD, QA]                     -- true
#eval onlyRaiser stwC QA                                       -- true — the endpoint IS forkState-shaped: the literal
                                                               -- "fires ⟹ both seated" necessity is REFUTED (seatless twin)

/-! ## (D) The king channel: the pair at rank 12 -/

/-- x = K♠ a bare king (kings cannot sit on anything — the king
channel is forced); x.twin = K♣ covered at the bottom of a
hidden-less pile.  The composite fires through the empty-anchor
letters both ways. -/
def KS : Card := c_ .spade .king
def KC : Card := c_ .club .king

def foundD : Suit → List Card
  | .spade => Suit.spade.upCards.take 12
  | .club => Suit.club.upCards.take 12
  | _ => []

def pilesD : Anchor → Pile
  | .p0 => P [] [KS]
  | .p1 => P [] [KC, JH]
  | _ => P [] []

def usedD : List Card :=
  foundD .spade ++ foundD .club ++
  (pilesD .p0).faceUp ++ (pilesD .p1).faceUp

def stD : State := mkSt foundD pilesD usedD

#eval censusOK usedD                                           -- true
#eval onlyRaiser stD KS                                        -- true — the bare king raises; the covered king does not

def st1D : State := ((State.step stD (Move.tabToFound KS)).getD stD)
def st2D : State := ((State.step st1D (Move.tabToTab KC (Sum.inl Anchor.p0))).getD st1D)
def stwD : State := ((State.step st2D (Move.foundToTab KS (Sum.inl Anchor.p1))).getD st2D)

#eval st1D.piles Anchor.p0 == P [] []                          -- true — the king's raise vacates to the empty pile
#eval (State.step st1D (Move.tabToTab KC (Sum.inl Anchor.p0))).isSome -- true — the covered king vacates onto x's emptied seat
#eval st2D.piles Anchor.p0 == P [] [KC, JH]                    -- true
#eval st2D.piles Anchor.p1 == P [] []                          -- true — emptied (no flip: hidden was [])
#eval (State.step st2D (Move.foundToTab KS (Sum.inl Anchor.p1))).isSome -- true — the bare king lands on the twin's emptied pile
#eval stwD.piles Anchor.p0 == P [] [KC, JH]                     -- true
#eval stwD.piles Anchor.p1 == P [] [KS]                        -- true — the anchors swapped
#eval (stwD.found Suit.spade).length == 12                      -- true — net-flat
#eval onlyRaiser stwD KS                                        -- true — the endpoint witnesses x again
