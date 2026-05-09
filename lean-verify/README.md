# Klondike Solver Verification (Lean 4)

Formal verification of the lonelybot Klondike Solitaire solver by reimplementing the core engine in Lean and proving it correct, then cross-validating against the Rust implementation.

## Strategy

1. **Verified reference implementation** — Reimplement the core data structures and `gen_moves` in Lean, matching the Rust code structure
2. **Prove correctness** — Show `gen_moves(false)` generates exactly the legal moves, and `gen_moves(true)` only removes dominated moves
3. **Cross-validate** — Compare encoded states visited by the Lean and Rust solvers on the same seeds to confirm equivalence

## Project Structure

### Implementation Layer (mirrors Rust code)

| File | Rust equivalent | Status |
|------|----------------|--------|
| `Card.lean` | `src/card.rs` | Card with XOR encoding, bitmask, swapSuit/swapColor |
| `Bitmask.lean` | `src/state.rs` (helpers) | swap_pair, bottom_mask computations |
| `Stack.lean` | `src/stack.rs` | Foundation stack, mask, dominance_mask, encode |
| `Deck.lean` | `src/deck.rs` | Stock/waste, compute_mask, encode |
| `Hidden.lean` | `src/hidden.rs` | Face-down cards, first_layer_mask, encode |
| `Moves.lean` | `src/moves.rs` | Move enum, MoveMask with filter/combine |
| `State.lean` | `src/state.rs` | Solitaire struct, gen_moves, do_move, encode |
| `MoveGenCorrect.lean` | — | **Core correctness theorems** |
| `Encode.lean` | — | 61-bit state encoding + cross-validation |
| `SuitSymmetry.lean` | — | Rank-color swap invariance theorem |

### Specification Layer (abstract game rules)

| File | Purpose |
|------|---------|
| `Spec/Basic.lean` | Abstract Card, Suit, Rank, Color, goesOnTopOf |
| `Spec/GameState.lean` | Abstract game state with pile lists |
| `Spec/Move.lean` | Abstract move with doMove/reverseMove |
| `Spec/Solvable.lean` | Solvability predicate, pruning soundness |
| `Spec/Dominance.lean` | Per-rule pruning correctness |

## Key Theorems

### 1. Move Generation Correctness
```
gen_moves(false) = legal_moves    (exactness)
gen_moves(true) ⊆ legal_moves    (soundness)
```

### 2. Suit Symmetry
```
For rank r, color C, if f(suit₀) ≤ r ∧ f(suit₁) ≤ r:
  Solvable(s) ⟺ Solvable(swap(s, r, C))
```

### 3. Dominance Preserves Solvability
```
For every pruned move m, ∃ non-pruned move m' that dominates m
```

## Cross-Validation with Rust

The 61-bit state encoding (`Solitaire.encode()`) is identical in both Lean and Rust. To cross-validate:

1. Run the Rust solver with a trace mode, outputting `(encode, move)` pairs
2. Run the Lean implementation on the same seed
3. Compare visited states: `traceStates(rust_trace) = traceStates(lean_trace)`

## Getting Started

```sh
cd lean-verify
lake exe cache get
lake build
```

## Current Status

Core data structures implemented. `sorry` placeholders remain in:
- `gen_moves` implementation (the core bitmask logic is laid out but needs completion)
- `do_move` / `undo_move` state transitions
- Correctness proofs (depend on completed implementations)
- Suit symmetry proof (depends on bit-level lemmas)
