import Klondike.State

open Klondike
open Klondike.Solitaire

def seed5Cards : Array Nat :=
  #[9,40,34,25,35,51,19,32,20,50,10,13,27,
    47,15,14,48,1,16,17,41,38,18,36,4,7,
    3,23,12,45,24,11,37,33,30,43,31,2,26,
    6,44,39,22,0,42,21,46,49,5,28,8,29]

def card5 : Klondike.Card := ⟨⟨5, by decide⟩⟩
def card31 : Klondike.Card := ⟨⟨31, by decide⟩⟩

private def verifyEdge (g : Klondike.Solitaire) (m : Klondike.Move) (expectedEnc : Nat) : Bool :=
  let (_, (undo, extra), s) := g.doMove m
  let encOk := s.encode == expectedEnc
  let sUndo := s.undoMove m undo extra
  let undoOk := sUndo.encode == g.encode
  encOk && undoOk

def main : List String → IO UInt32 := fun _ => do
  let g : Klondike.Solitaire := Klondike.Solitaire.new seed5Cards 3
  let enc := g.encode
  let encOk : Bool := enc == 1801439849295577088
  let visOk : Bool := g.visibleMask == 3379915932074496
  let lockedOk : Bool := g.hidden.lockedMask == 3803610330687130
  let flmOk : Bool := g.hidden.firstLayerMask == 1374423631360
  let stackOk : Bool := g.finalStack.val == 0
  let deckEncOk : Bool := g.deck.encode == 419430399
  let movesNoDom := g.genMoves false
  let psOk : Bool := movesNoDom.pileStack == 0
  let dsOk : Bool := movesNoDom.deckStack == 0
  let spOk : Bool := movesNoDom.stackPile == 0
  let dpOk : Bool := movesNoDom.deckPile == 2147483680
  let rOk : Bool := movesNoDom.reveal == 0
  let movesDom := g.genMoves true
  let domSame : Bool := movesDom == movesNoDom
  let e0 := verifyEdge g (Klondike.Move.deckPile card5) 1508705873516494848
  let e1 := verifyEdge g (Klondike.Move.deckPile card31) 648517245177102336
  let (_, (_, _), s0) := g.doMove (Klondike.Move.deckPile card5)
  let s0moves := s0.genMoves true
  let s0dpOk : Bool := s0moves.deckPile == 2147483648 && s0moves.pileStack == 0
  let s0otherOk := s0moves.deckStack == 0 && s0moves.stackPile == 0 && s0moves.reveal == 0
  let allOk := encOk && visOk && lockedOk && flmOk && stackOk && deckEncOk
    && psOk && dsOk && spOk && dpOk && rOk && domSame && e0 && e1
    && s0dpOk && s0otherOk
  IO.println s!"=== Initial State ==="
  IO.println s!"encode={enc} ok={encOk}"
  IO.println s!"visibleMask={g.visibleMask} ok={visOk}"
  IO.println s!"lockedMask={g.hidden.lockedMask} ok={lockedOk}"
  IO.println s!"firstLayerMask={g.hidden.firstLayerMask} ok={flmOk}"
  IO.println s!"stack={g.finalStack.val} ok={stackOk}"
  IO.println s!"deckEncode={g.deck.encode} ok={deckEncOk}"
  IO.println s!"=== genMoves ==="
  IO.println s!"pileStack={movesNoDom.pileStack} ok={psOk}"
  IO.println s!"deckStack={movesNoDom.deckStack} ok={dsOk}"
  IO.println s!"stackPile={movesNoDom.stackPile} ok={spOk}"
  IO.println s!"deckPile={movesNoDom.deckPile} ok={dpOk}"
  IO.println s!"reveal={movesNoDom.reveal} ok={rOk}"
  IO.println s!"domSame={domSame}"
  IO.println s!"=== doMove/undoMove ==="
  IO.println s!"edge0_ok={e0}"
  IO.println s!"edge1_ok={e1}"
  IO.println s!"=== State after DeckPile(5) ==="
  IO.println s!"deckPile={s0moves.deckPile} ok={s0dpOk}"
  IO.println s!"other_ok={s0otherOk}"
  IO.println s!"ALL_OK={allOk}"
  if allOk then pure 0 else pure 1
