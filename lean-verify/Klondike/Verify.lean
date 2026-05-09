import Klondike.State

namespace Klondike

open Solitaire

private def seed5Cards : Array Nat :=
  #[9,40,34,25,35,51,19,32,20,50,10,13,27,
    47,15,14,48,1,16,17,41,38,18,36,4,7,
    3,23,12,45,24,11,37,33,30,43,31,2,26,
    6,44,39,22,0,42,21,46,49,5,28,8,29]

private def seed5Game : Solitaire := Solitaire.new seed5Cards 3

private def card5 : Card := ⟨⟨5, by decide⟩⟩
private def card31 : Card := ⟨⟨31, by decide⟩⟩

def verifySeed5 : String := Id.run do
  let g := seed5Game
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
  let (rev0, (undo0, extra0), s0) := g.doMove (Move.deckPile card5)
  let enc0Ok : Bool := s0.encode == 1508705873516494848
  let s0undo := s0.undoMove (Move.deckPile card5) undo0 extra0
  let undo0Ok : Bool := s0undo.encode == g.encode
  let (rev1, (undo1, extra1), s1) := g.doMove (Move.deckPile card31)
  let enc1Ok : Bool := s1.encode == 648517245177102336
  let s1undo := s1.undoMove (Move.deckPile card31) undo1 extra1
  let undo1Ok : Bool := s1undo.encode == g.encode
  let allOk := encOk && visOk && lockedOk && flmOk && stackOk && deckEncOk
    && psOk && dsOk && spOk && dpOk && rOk && domSame
    && enc0Ok && undo0Ok && enc1Ok && undo1Ok
  let results :=
    [s!"encode={enc} ok={encOk}",
     s!"visibleMask={g.visibleMask} ok={visOk}",
     s!"lockedMask={g.hidden.lockedMask} ok={lockedOk}",
     s!"firstLayerMask={g.hidden.firstLayerMask} ok={flmOk}",
     s!"stack={g.finalStack.val} ok={stackOk}",
     s!"deckEncode={g.deck.encode} ok={deckEncOk}",
     s!"pileStack={movesNoDom.pileStack} ok={psOk}",
     s!"deckStack={movesNoDom.deckStack} ok={dsOk}",
     s!"stackPile={movesNoDom.stackPile} ok={spOk}",
     s!"deckPile={movesNoDom.deckPile} ok={dpOk}",
     s!"reveal={movesNoDom.reveal} ok={rOk}",
     s!"domSame={domSame}",
     s!"doMove(DeckPile 5) enc={s0.encode} ok={enc0Ok}",
     s!"undoMove(DeckPile 5) enc={s0undo.encode} ok={undo0Ok}",
     s!"doMove(DeckPile 31) enc={s1.encode} ok={enc1Ok}",
     s!"undoMove(DeckPile 31) enc={s1undo.encode} ok={undo1Ok}",
     s!"ALL_OK={allOk}"]
  pure (String.intercalate "\n" results)

end Klondike
