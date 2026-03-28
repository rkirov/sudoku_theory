/-!
# Sudoku Theory

A formal theory of Sudoku puzzles in Lean 4.

Sudoku is played on a grid of size {lit}`m * n × m * n`, divided into
rectangular blocks of {lit}`m` rows and {lit}`n` columns. The goal is to fill
every cell with a value from {lit}`Fin (m * n)` so that each row, column,
and block contains every value exactly once.

Standard 9×9 Sudoku uses {lit}`m = n = 3`. The popular 6×6 variant uses
{lit}`m = 3, n = 2` (blocks of 3 rows × 2 columns).

## Modules

- `SudokuTheory.Defs.Board` — board representation and regions
- `SudokuTheory.Defs.Valid` — validity predicates
- `SudokuTheory.Defs.Puzzle` — partial boards, solutions, and difficulty
-/
