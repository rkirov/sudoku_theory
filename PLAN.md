# Sudoku Theory: Lean 4 + Verso Literate Programming

## Goal

Formalize the theory of Sudoku puzzles in Lean 4, using Verso-compatible literate programming so the `.lean` files render as a navigable documentation website.

## Design Decisions

### Board Representation
- **Parameterized by block dimensions `m × n`**: Blocks are `m` rows by `n` columns, making the full board `(m*n) × (m*n)` with values from `Fin (m*n)`. Standard 9×9 sudoku is `m=n=3`; popular 6×6 puzzles use `m=3, n=2` (3-row × 2-column blocks).
- **Function-based**: `Board m n := Fin (m*n) → Fin (m*n) → Fin (m*n)` (same pattern as mathlib's `Matrix`).

### Validity
- **`Function.Injective`** as the core predicate: injectivity on finite types equals bijectivity (pigeonhole principle from mathlib), so "all distinct" and "each value exactly once" are equivalent for free. Richer mathlib lemma support than the `Finset.image` alternative.
- **`Finset` characterization as equivalent lemma**: e.g. `RowValid b i ↔ Finset.univ.image (b i) = Finset.univ` — provided for convenience, not used as the definition.
- **`[NeZero m] [NeZero n]`** typeclass constraints for block definitions (need `m, n > 0` for division).

### Verso Integration
- Use **literate module docs** approach (not textbook template).
- Set `doc.verso = true` in lakefile options.
- `/-! ... -/` module docs for narrative prose; `/-- ... -/` for definition docs.
- Build docs with `lake build :literateHtml`.

## Project Structure

```
sudoku_theory/
├── lakefile.toml            # mathlib + verso deps, doc.verso = true
├── lean-toolchain           # Lean version (matching Verso)
├── literate.toml            # Verso site configuration
├── SudokuTheory.lean        # Root module + project introduction
└── SudokuTheory/
    ├── Defs.lean            # Re-exports Board + Valid + Puzzle
    ├── Defs/
    │   ├── Board.lean       # Board type, row/col/block region definitions
    │   ├── Valid.lean       # RowValid, ColValid, BlockValid, ValidSudoku
    │   └── Puzzle.lean      # Partial boards (puzzles), solutions, solution count
    └── LatinSquare.lean     # (deferred) Latin square definition + connection
```

## Module Contents

### `SudokuTheory/Defs/Board.lean`
- `Board m n` — type alias for `Fin (m*n) → Fin (m*n) → Fin (m*n)`
- `row i` — finset of cells in row `i`
- `col j` — finset of cells in column `j`
- `block m n bi bj` — finset of cells in block `(bi, bj)` where `bi : Fin n`, `bj : Fin m` (blocks are `m` rows × `n` cols, so there are `n` block-rows and `m` block-columns)

### `SudokuTheory/Defs/Valid.lean`
- `RowValid b i` — `Function.Injective (b i)`
- `ColValid b j` — `Function.Injective (fun i => b i j)`
- `BlockValid m n b bi bj` — injectivity on block cells
- `ValidSudoku b` — `Prop` combining all three (conjunction, not structure)

### `SudokuTheory/Defs/Puzzle.lean`
- `Puzzle m n` — partial board: `Fin (m*n) → Fin (m*n) → Option (Fin (m*n))` (cells are either filled or empty)
- `IsSolution (p : Puzzle m n) (b : Board m n)` — `b` is a valid solution to `p`: `ValidSudoku b` and `b` agrees with `p` on all filled cells
- `HasUniqueSolution p` — exactly one solution: `∃! b, IsSolution p b`
- `HasNoSolution p` — no solution: `¬ ∃ b, IsSolution p b`
- `HasMultipleSolutions p` — more than one: `∃ b₁ b₂, IsSolution p b₁ ∧ IsSolution p b₂ ∧ b₁ ≠ b₂`
- `WellPosed p` — synonym for `HasUniqueSolution` (a well-posed puzzle has exactly one solution)
- `Possible (p : Puzzle m n) (i j : Fin (m*n))` — `Finset (Fin (m*n))`: values for empty cell `(i,j)` that don't violate any constraint (not already in same row, column, or block among filled cells). Only meaningful when `p i j = none`.
- **Hard puzzle conjecture** (general): `∀ m n, ∃ p : Puzzle m n, WellPosed p ∧ ∀ i j, p i j = none → (Possible p i j).card > 1` — for every dimension there exists a puzzle with unique solution but no naked singles. May be hard to prove in general.
- **Hard puzzle examples** (concrete, provable): exhibit specific hard puzzles for `2×2`, `2×3`, and `3×3` with proofs by `decide` or explicit construction.

### `SudokuTheory/Properties.lean`
- `relabel_valid`: if `σ : Fin (m*n) ≃ Fin (m*n)` is a permutation and `ValidSudoku b`, then `ValidSudoku (σ ∘ b · ·)` — relabeling values preserves validity
- `relabel_puzzle`: analogous for puzzles — applying `σ` to all filled cells preserves solution count (unique stays unique, etc.)
- `relabel_possible`: `Possible` sets transform covariantly under relabeling

### `SudokuTheory/Strategies.lean`
- **Hidden subset theorem** (generalizes naked/hidden singles, pairs, triples, etc.): In any region (row/col/box), given a subset `S ⊆ Fin (m*n)` of size `k`, if exactly `k` cells in that region have a possible value in `S`, then:
  1. Those `k` cells can only contain values from `S` (all other possibilities can be eliminated)
  2. It's impossible for fewer than `k` cells to have possibilities intersecting `S` (contradiction with pigeonhole — `k` values need `k` cells)
- This single theorem unifies: naked single (`k=1`), naked pair (`k=2`), naked triple (`k=3`), and their hidden duals
- **Deadly pattern / uniqueness forcing**: A *deadly pattern* is a set of cells where a value permutation yields another valid completion. If a puzzle is well-posed (`WellPosed p`), no deadly pattern can exist. Specific case: **Unique Rectangle** — 4 cells at the intersection of 2 rows and 2 columns spanning 2 boxes; if three have possibilities `{a,b}` and one has `{a,b,c,...}`, then `c` (or other extra candidates) must be the value in that cell, because `{a,b}` in all four would allow an `a↔b` swap giving a second solution. Generalization TBD — formalizing arbitrary deadly patterns may require defining a notion of "partial permutation that preserves all region constraints."

## Implementation Order

1. **Scaffold + Verso setup**: lakefile.toml, lean-toolchain, literate.toml, minimal SudokuTheory.lean
2. `lake build` to verify setup, `lake build :literateHtml` to test Verso
3. Push to GitHub, set up GitHub Pages for Verso docs
4. Board.lean + Valid.lean — core definitions
5. Puzzle.lean — partial boards, solutions, Possible, hard puzzle examples
6. Properties.lean — relabeling
7. Strategies.lean — hidden subset, uniqueness forcing

## Deferred (future iterations)
- **Latin squares**: `LatinSquare` definition, `ValidSudoku.toLatinSquare` theorem
- **More properties**: transpose, row/column permutations within bands, band permutations
- **Strategies**: naked single, hidden single as formal lemmas
- **Counting**: number of valid boards for small `m`, `n`
- **Concrete examples**: 9×9 puzzles with `#eval`
- **Symmetry group**: permutations that preserve sudoku validity

## Dependencies
- **mathlib4** — Finset, Fintype, Function.Injective, Fin arithmetic
- **verso** — literate programming documentation generation
