import Klondike.Card
import Klondike.Bitmask
import Klondike.Stack
import Klondike.Deck
import Klondike.Hidden
import Klondike.Moves

namespace Klondike

inductive ExtraInfo where
  | none : ExtraInfo
  | revealEmpty : ExtraInfo
  | revealCard : Card → ExtraInfo
  deriving DecidableEq, Repr

structure Solitaire where
  hidden : Hidden
  finalStack : Stack
  deck : Deck
  visibleMask : Nat
  deriving DecidableEq, Repr

abbrev UndoInfo := Nat

namespace Solitaire

def getVisibleMask (s : Solitaire) : Nat := s.visibleMask
def getLockedMask (s : Solitaire) : Nat := Hidden.getLockedMask s.hidden
def getExtendedTopMask (s : Solitaire) : Nat := s.visibleMask &&& (s.getLockedMask ||| KING_MASK)

def getBottomMask (s : Solitaire) : Nat :=
  let vis := s.getVisibleMask
  let free := vis &&& Nat.complement64 s.getLockedMask
  bottomMask vis free

def isWin (s : Solitaire) : Bool := Stack.isFull s.finalStack

private def getDeckMask (s : Solitaire) (domStackable : Nat) : Nat × Bool :=
  if s.deck.isEmpty then (0, false)
  else
    let mask := s.deck.computeMask false
    let maskDom := mask &&& domStackable
    if maskDom ≠ 0 then
      let lowest := maskDom &&& (0 - maskDom)
      if lowest = mask then (mask, true) else (lowest, true)
    else
      (mask, false)

def genMoves (dominance : Bool) (s : Solitaire) : MoveMask :=
  let vis := s.getVisibleMask
  let locked := s.getLockedMask
  let bm := s.getBottomMask
  let sm := s.finalStack.mask
  let domSm := if dominance then s.finalStack.dominanceMask else 0

  let pileStack := bm &&& vis &&& sm
  let pileStackDom := pileStack &&& domSm

  if pileStackDom ≠ 0 then
    ⟨(0 - pileStackDom) &&& pileStackDom, 0, 0, 0, 0⟩
  else
    let redundantStack := pileStack &&& Nat.complement64 locked
    let leastStack := redundantStack &&& (0 - redundantStack)

    if dominance && Nat.popCount redundantStack ≥ 3 then
      ⟨leastStack, 0, 0, 0, 0⟩
    else
      let (deckMask, dom) := s.getDeckMask (domSm &&& sm)
      if dom then
        ⟨0, deckMask, 0, 0, 0⟩
      else
        let freePile := Nat.popCount s.getExtendedTopMask < N_PILES
        let kingMask := if freePile then KING_MASK else 0
        let freeSlot := (bm >>> 4) ||| kingMask

        let stackPile := swapPair (sm >>> 4) &&& freeSlot &&& Nat.complement64 domSm
        let deckStack := deckMask &&& sm

        let pairedStack := pileStack &&& (pileStack >>> 1) &&& ALT_MASK

        let (stackPile, pileStack, deckStack, freeSlot) :=
          if !dominance || leastStack = 0 then
            (stackPile, pileStack, deckStack, freeSlot)
          else if pairedStack > 0 then
            let rm := pairedStack * 3
            (0, rm, 0, rm >>> 4)
          else
            let least := leastStack ||| (leastStack >>> 1)
            let least := (least &&& ALT_MASK) * 3
            let extra := redundantStack ||| (vis &&& sm &&& (least <<< 4))
            let s0 := extra &&& SUIT_MASK[0]! = 0
            let s1 := extra &&& SUIT_MASK[1]! = 0
            let s2 := extra &&& SUIT_MASK[2]! = 0
            let s3 := extra &&& SUIT_MASK[3]! = 0

            if (s0 || s1) && (s2 || s3) then
              let potStack := Nat.complement64 locked &&& vis &&& sm
              let potStack := potStack ||| (potStack >>> 1)
              let stackRank := (least >>> 2) &&& RANK_MASK
              let tripleStackable := (potStack &&& stackRank) * 3

              let suitFilter :=
                (if s0 then SUIT_MASK[1]! else 0)
                ||| (if s1 then SUIT_MASK[0]! else 0)
                ||| (if s2 then SUIT_MASK[3]! else 0)
                ||| (if s3 then SUIT_MASK[2]! else 0)

              let newStackPile := stackPile &&& suitFilter &&& (leastStack - 1) &&& Nat.complement64 tripleStackable
              let newFreeSlot := if (least <<< 2) &&& redundantStack > 0 then 0 else least >>> 4
              (newStackPile, leastStack, 0, newFreeSlot)
            else
              (0, leastStack, 0, 0)

        let deckPile := deckMask &&& freeSlot &&& Nat.complement64 (domSm &&& sm)
        let reveal := vis &&& locked &&& freeSlot &&& Nat.complement64 (Hidden.getFirstLayerMask s.hidden &&& KING_MASK)

        ⟨pileStack, deckStack, stackPile, deckPile, reveal⟩

def reverseMove (s : Solitaire) (m : Move) : Option Move :=
  match m with
  | .pileStack c => if s.getLockedMask &&& Card.mask c = 0 then some (Move.stackPile c) else none
  | .stackPile c => some (Move.pileStack c)
  | _ => none

private def makeReveal (s : Solitaire) (c : Card) : ExtraInfo × Solitaire :=
  let (newHidden, revealed) := s.hidden.popCard c
  match revealed with
  | some rc => (ExtraInfo.revealCard rc, { s with hidden := newHidden, visibleMask := s.visibleMask ||| Card.mask rc })
  | none => (ExtraInfo.revealEmpty, { s with hidden := newHidden })

private def unmakeReveal (s : Solitaire) (c : Card) (revealed : Option Card) : Solitaire :=
  let newHidden := s.hidden.unpopCard c revealed
  match revealed with
  | some rc => { s with hidden := newHidden, visibleMask := s.visibleMask &&& Nat.complement64 (Card.mask rc) }
  | none => { s with hidden := newHidden }

private def makeStackFromPile (s : Solitaire) (c : Card) : UndoInfo × ExtraInfo × Solitaire :=
  let mask := Card.mask c
  let newStack := s.finalStack.push c.suit.val
  let locked := s.getLockedMask &&& mask ≠ 0
  let newVis := s.visibleMask ^^^ mask
  let (extra, s2) :=
    if locked then
      let (ei, s') := makeReveal { s with finalStack := newStack, visibleMask := newVis } c
      (ei, s')
    else
      (ExtraInfo.none, { s with finalStack := newStack, visibleMask := newVis })
  (if locked then 1 else 0, extra, s2)

private def unmakeStackFromPile (s : Solitaire) (c : Card) (undo : UndoInfo) : Solitaire :=
  let mask := Card.mask c
  let newStack := s.finalStack.pop c.suit.val
  let newVis := s.visibleMask ||| mask
  let s' := { s with finalStack := newStack, visibleMask := newVis }
  if undo > 0 then
    let revealed : Option Card := none
    unmakeReveal s' c revealed
  else s'

private def makeStackFromDeck (s : Solitaire) (c : Card) : UndoInfo × ExtraInfo × Solitaire :=
  let newStack := s.finalStack.push c.suit.val
  let oldOffset := s.deck.getOffset
  let newDeck := { s.deck with drawCur := oldOffset + 1 }
  (oldOffset, ExtraInfo.none, { s with finalStack := newStack, deck := newDeck })

private def unmakeStackFromDeck (s : Solitaire) (c : Card) (undo : UndoInfo) : Solitaire :=
  let newStack := s.finalStack.pop c.suit.val
  let newDeck := { s.deck with drawCur := undo }
  { s with finalStack := newStack, deck := newDeck }

private def makePileFromStack (s : Solitaire) (c : Card) : UndoInfo × ExtraInfo × Solitaire :=
  let mask := Card.mask c
  let newVis := s.visibleMask ||| mask
  let newStack := s.finalStack.pop c.suit.val
  (0, ExtraInfo.none, { s with finalStack := newStack, visibleMask := newVis })

private def unmakePileFromStack (s : Solitaire) (c : Card) (undo : UndoInfo) : Solitaire :=
  let mask := Card.mask c
  let newVis := s.visibleMask &&& Nat.complement64 mask
  let newStack := s.finalStack.push c.suit.val
  { s with finalStack := newStack, visibleMask := newVis }

private def makePileFromDeck (s : Solitaire) (c : Card) : UndoInfo × ExtraInfo × Solitaire :=
  let mask := Card.mask c
  let newVis := s.visibleMask ||| mask
  let oldOffset := s.deck.getOffset
  let newDeck := { s.deck with drawCur := oldOffset + 1 }
  (oldOffset, ExtraInfo.none, { s with deck := newDeck, visibleMask := newVis })

private def unmakePileFromDeck (s : Solitaire) (c : Card) (undo : UndoInfo) : Solitaire :=
  let mask := Card.mask c
  let newVis := s.visibleMask &&& Nat.complement64 mask
  let newDeck := { s.deck with drawCur := undo }
  { s with deck := newDeck, visibleMask := newVis }

def doMove (s : Solitaire) (m : Move) : Option Move × (UndoInfo × ExtraInfo) × Solitaire :=
  let rev := reverseMove s m
  match m with
  | .deckStack c =>
    let (undo, extra, s') := makeStackFromDeck s c
    (rev, (undo, extra), s')
  | .pileStack c =>
    let (undo, extra, s') := makeStackFromPile s c
    (rev, (undo, extra), s')
  | .deckPile c =>
    let (undo, extra, s') := makePileFromDeck s c
    (rev, (undo, extra), s')
  | .stackPile c =>
    let (undo, extra, s') := makePileFromStack s c
    (rev, (undo, extra), s')
  | .reveal c =>
    let (extra, s') := makeReveal s c
    (rev, (0, extra), s')

def undoMove (s : Solitaire) (m : Move) (undo : UndoInfo) (extra : ExtraInfo) : Solitaire :=
  match m with
  | .deckStack c => unmakeStackFromDeck s c undo
  | .pileStack c => unmakeStackFromPile s c undo
  | .deckPile c => unmakePileFromDeck s c undo
  | .stackPile c => unmakePileFromStack s c undo
  | .reveal c =>
    match extra with
    | ExtraInfo.revealCard rc => unmakeReveal s c (some rc)
    | _ => unmakeReveal s c none

def encode (s : Solitaire) : Nat :=
  Stack.encode s.finalStack
  ||| (Hidden.encode s.hidden <<< 16)
  ||| (Deck.encode s.deck <<< 32)

def decode (n : Nat) : Solitaire :=
  ⟨Hidden.decode ((n >>> 16) &&& 0xFFFF),
   Stack.decode (n &&& 0xFFFF),
   Deck.decode (n >>> 32),
   0⟩

end Solitaire

end Klondike
