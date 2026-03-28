import SudokuTheory.Defs

/-!
# Sudoku Formal Math Theory

A formal treatment of Sudoku puzzles in Lean 4.

Sudoku is a well-known logic puzzle, typically presented as follows:

![A typical 9×9 Sudoku puzzle](images/sudoku-example.png)

The rules are straightforward:
- Fill each cell with a digit from 1 to 9.
- Every row contains each digit exactly once.
- Every column contains each digit exactly once.
- Every 3×3 block contains each digit exactly once.
- The puzzle has a unique solution satisfying all constraints.

This library generalizes the grid size and block dimensions. A Sudoku board has
size {lit}`m * n × m * n`, partitioned into rectangular blocks of {lit}`m` rows
and {lit}`n` columns. Each cell takes a value in {lit}`Fin (m * n)` (Lean's
way of describing finite sets from {lit}`0` to {lit}`m * n - 1`), and every
row, column, and block must contain each value exactly once.

Standard 9×9 Sudoku corresponds to {lit}`m = n = 3`. The common 6×6 variant
uses {lit}`m = 3, n = 2` (blocks of 3 rows × 2 columns).

For background on Sudoku, see the [Wikipedia article](https://en.wikipedia.org/wiki/Sudoku).

The modules below are written with Verso, Lean 4's literate programming tool,
so each one doubles as a readable document. They are best read in order.

## Modules

- `SudokuTheory.Defs.Board` — board representation and regions
- `SudokuTheory.Defs.Valid` — validity predicates
- `SudokuTheory.Defs.Puzzle` — partial boards, solutions, and difficulty
-/
