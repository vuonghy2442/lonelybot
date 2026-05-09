/-
Klondike.State — Core Solitaire game state with gen_moves, matching src/state.rs.

This is the central module. The Solitaire struct uses bitmask operations
for extremely fast move generation. We reimplement gen_moves in Lean
and prove it generates exactly the legal moves.

The key function is gen_moves(dominance): computes all legal moves
using bitwise operations on visible_mask, locked_mask, stack masks,
and deck masks. With dominance=true, it applies pruning rules.
-/

namespace Klondike

/--
Extra information about move side effects.
Matches `ExtraInfo` in the more_dominances branch of src/state.rs.
-/
inductive ExtraInfo where
  | none        : ExtraInfo
  | revealEmpty : ExtraInfo
  | revealCard  : Card → ExtraInfo
  deriving DecidableEq, Repr

/--
The core Solitaire game state, matching `Solitaire` in src/state.rs.

Fields:
- hidden: Hidden card management
- final_stack: Foundation (Stack = compact u16)
- deck: Stock/waste deck
- visible_mask: Bitmask of all face-up cards in tableau (u64)
-/
structure Solitaire where
  hidden      : Hidden
  finalStack  : Stack
  deck        : Deck
  visibleMask : Nat  -- u64 bitmask
  deriving DecidableEq, Repr

namespace Solitaire

/-- The type of undo information. -/
abbrev UndoInfo := Nat

/--
Create a new game from a card deck and draw step.
Matches `Solitaire::new()` in src/state.rs:41-65.
-/
def new (cards : Array Card) (drawStep : Nat) : Solitaire :=
  let hiddenPiles := cards.take N_PILE_CARDS
  let mut visibleMask := 0
  for i in [0:N_PILES] do
    let pos := (i + 2) * (i + 1) / 2 - 1
    if pos < hiddenPiles.size then
      visibleMask := visibleMask ||| (1 <<< hiddenPiles[pos]!.val)
  {
    hidden := Hidden.new hiddenPiles
    finalStack := Stack.empty
    deck := ⟨cards.drop N_PILE_CARDS, 0, drawStep⟩
    visibleMask := visibleMask
  }

/-- Get the visible mask. -/
def getVisibleMask (s : Solitaire) : Nat := s.visibleMask

/-- Get the locked mask (all hidden cards). -/
def getLockedMask (s : Solitaire) : Nat := s.hidden.getLockedMask

/-- Get the extended top mask (top cards + kings). -/
def getExtendedTopMask (s : Solitaire) : Nat :=
  s.visibleMask &&& (s.getLockedMask ||| KING_MASK)

/--
Compute the "bottom mask" — cards that can receive another card on top.
Matches `get_bottom_mask()` in src/state.rs:107-124.

A card is a "bottom" if another card can be placed on top of it.
The formula uses XOR and OR operations on the visible mask and
the free (non-locked) mask to identify valid receiving positions.
-/
def getBottomMask (s : Solitaire) : Nat :=
  let vis := s.getVisibleMask
  let free := vis &&& ~~~ s.getLockedMask
  let xorFree := free ^^^ (free >>> 1)
  let xorVis := vis ^^^ (vis >>> 1)
  let xorAll := xorVis ^^^ (xorFree <<< 4)
  let orFree := free ||| (free >>> 1)
  let orVis := vis ||| (vis >>> 1)
  let bm := ((xorAll ||| ~~~(orFree <<< 4)) &&& orVis &&& ALT_MASK) * 3
  bm

/--
Compute the deck mask: which cards are accessible from the stock.
Matches `get_deck_mask()` in src/state.rs:127-148.

Returns (mask, is_dominant).
-/
def getDeckMask (s : Solitaire) (domStackable : Nat) : Nat × Bool :=
  if s.deck.drawStep = 1 then
    let mask := s.deck.computeMask false
    let maskDom := mask &&& domStackable
    if maskDom > 0 then
      (maskDom &&& (0 - maskDom), true)  -- lowest bit of maskDom
    else
      (mask, false)
  else
    match s.deck.peekLast with
    | some lastCard =>
      let filter := domStackable &&& Card.mask lastCard > 0
      if filter && s.deck.isPure then
        (Card.mask lastCard, true)
      else
        (s.deck.computeMask filter, false)
    | none => (0, false)

/--
THE CORE FUNCTION: Generate all legal moves.
Matches `gen_moves::<DOMINANCE>()` in src/state.rs:152-294.

With DOMINANCE = false: generates all legal moves (no pruning).
With DOMINANCE = true: applies suit symmetry and dominance pruning.

Returns a MoveMask where each set bit represents a legal move.
-/
def genMoves (dominance : Bool) (s : Solitaire) : MoveMask :=
  let vis := s.getVisibleMask
  let locked := s.getLockedMask
  let bm := s.getBottomMask
  let sm := Stack.mask s.finalStack
  let domSm := if dominance then Stack.dominanceMask s.finalStack else 0

  -- PileStack: visible + stackable + bottom cards
  let pileStackAll := bm &&& vis &&& sm
  let pileStackDom := pileStackAll &&& domSm

  -- Early return for dominance mask auto-stack
  if dominance && pileStackDom ≠ 0 then
    { pileStack := pileStackDom &&& (0 - pileStackDom)  -- lowest bit
      deckStack := 0, stackPile := 0, deckPile := 0, reveal := 0 }
  else
    let redundantStack := pileStackAll &&& ~~~ locked
    let leastStack := redundantStack &&& (0 - redundantStack)  -- lowest bit

    -- If 3+ redundant stackable cards, only keep the lowest
    if dominance && redundantStack.popCount ≥ 3 then
      { pileStack := leastStack
        deckStack := 0, stackPile := 0, deckPile := 0, reveal := 0 }
    else
      -- Compute deck mask
      let (deckMask, dom) := s.getDeckMask (domSm &&& sm)
      if dom then
        { deckStack := deckMask
          pileStack := 0, stackPile := 0, deckPile := 0, reveal := 0 }
      else
        -- Free slots: where can cards be placed
        let freePile := s.getExtendedTopMask.popCount < N_PILES
        let kingMask := if freePile then KING_MASK else 0
        let freeSlot := (bm >>> 4) ||| kingMask

        -- StackPile: from foundation to tableau
        let stackPileAll := swapPair (sm >>> 4) &&& freeSlot &&& ~~~ domSm

        -- DeckStack: from stock to foundation
        let deckStackAll := deckMask &&& sm

        -- Paired stack: both same-color cards stackable at same rank
        let pairedStack := pileStackAll &&& (pileStackAll >>> 1) &&& ALT_MASK

        -- Apply dominance rules for paired/non-paired cases
        let (stackPile, pileStack, deckStack, freeSlot) :=
          if !dominance || leastStack = 0 then
            (stackPileAll, pileStackAll, deckStackAll, freeSlot)
          else if pairedStack > 0 then
            let rm := pairedStack * 3
            (0, rm, 0, rm >>> 4)
          else
            let least := (leastStack ||| (leastStack >>> 1)) &&& ALT_MASK
            let least := least * 3
            let extra := redundantStack ||| (vis &&& sm &&& (least <<< 4))
            let suitUnstack := (Array.ofFn fun i => extra &&& SUIT_MASK ⟨i, by omega⟩ = 0)

            if (suitUnstack[0]! || suitUnstack[1]!) && (suitUnstack[2]! || suitUnstack[3]!) then
              let potStack := (~~~ locked) &&& vis &&& sm
              let potStack := potStack ||| (potStack >>> 1)
              let stackRank := (least >>> 2) &&& RANK_MASK
              let tripleStackable := (potStack &&& stackRank) * 3

              let suitFilter :=
                (if suitUnstack[0]! then SUIT_MASK ⟨1, by omega⟩ else 0)
                ||| (if suitUnstack[1]! then SUIT_MASK ⟨0, by omega⟩ else 0)
                ||| (if suitUnstack[2]! then SUIT_MASK ⟨3, by omega⟩ else 0)
                ||| (if suitUnstack[3]! then SUIT_MASK ⟨2, by omega⟩ else 0)

              (stackPileAll &&& suitFilter &&& (leastStack - 1) &&& ~~~ tripleStackable,
               leastStack,
               0,
               if (least <<< 2) &&& redundantStack > 0 then 0 else least >>> 4)
            else
              (0, leastStack, 0, 0)

        -- DeckPile: from stock to tableau
        let deckPile := deckMask &&& freeSlot &&& ~~~ (domSm &&& sm)

        -- Reveal: move top card to another pile, revealing hidden card
        let reveal := vis &&& locked &&& freeSlot &&& ~~~ (s.hidden.getFirstLayerMask &&& KING_MASK)

        { pileStack, deckStack, stackPile, deckPile, reveal }

/--
Execute a move, returning the new state, reverse move, and undo info.
Matches `Solitaire::do_move()` in src/state.rs.

Returns: (reverse_move, (undo_info, extra_info))
-/
def doMove (s : Solitaire) (m : Move) : Option Move × (UndoInfo × ExtraInfo) × Solitaire :=
  (none, (0, ExtraInfo.none), s)  -- TODO: implement fully

/--
Undo a move.
Matches `Solitaire::undo_move()` in src/state.rs.
-/
def undoMove (s : Solitaire) (m : Move) (undo : UndoInfo) : Solitaire :=
  s  -- TODO: implement

/--
Compute the reverse move: can this move be undone by a legal move?
Matches `Solitaire::reverse_move()` in src/state.rs:297-316.
-/
def reverseMove (s : Solitaire) (m : Move) : Option Move :=
  match m with
  | Move.pileStack c =>
    if s.getLockedMask &&& Card.mask c = 0 then
      some (Move.stackPile c)
    else none
  | Move.stackPile _ => some (Move.pileStack Card.default)  -- approximate
  | _ => none

/-- Whether the game is won. -/
def isWin (s : Solitaire) : Bool :=
  s.finalStack.isFull

/-- Encode the state as a compact u64 for transposition table.
    Matches `Solitaire::encode()` in src/state.rs:444-451.
    Format: 16 bits stack + 16 bits hidden + 29 bits deck = 61 bits. -/
def encode (s : Solitaire) : Nat :=
  Stack.encode s.finalStack
  ||| (Hidden.encode s.hidden <<< 16)
  ||| (Deck.encode s.deck <<< 32)

/-- Decode a state from compact u64. -/
def decode (n : Nat) : Solitaire :=
  ⟨Hidden.decode ((n >>> 16) &&& 0xFFFF),
   Stack.decode (n &&& 0xFFFF),
   Deck.decode ((n >>> 32)),
   0⟩

end Solitaire

end Klondike
