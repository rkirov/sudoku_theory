/-!
# Sudoku Theory

A formal theory of Sudoku puzzles in Lean 4.

Sudoku is a popular logic puzzle that usually looks like this:

![A typical 9×9 Sudoku puzzle](images/sudoku-example.png)

The rules are simple:
- Each cell must contain a value from 1 to 9.
- Each row must contain each value from 1 to 9 exactly once.
- Each column must contain each value from 1 to 9 exactly once.
- Each of the nine 3×3 blocks must contain each value from 1 to 9 exactly once.
- There is a unique solution that satisfies all these constraints.

To formalize Sudoku, we generalize the grid size and block dimensions. In our theory,
Sudoku is played on a grid of size {lit}`m * n × m * n`, divided into
rectangular blocks of {lit}`m` rows and {lit}`n` columns. The goal is to fill
every cell with a value from {lit}`Fin (m * n)` so that each row, column,
and block contains every value exactly once.

Standard 9×9 Sudoku uses {lit}`m = n = 3`. A popular 6×6 variant uses
{lit}`m = 3, n = 2` (blocks of 3 rows × 2 columns).

To read more about Sudoku, see the [Wikipedia article](https://en.wikipedia.org/wiki/Sudoku).

This theory is organized into the following modules. They are
written using Verso (lean4's literate coding tool), so you can read them as standalone documents.

Read them in order, to learn more about the theory and how to use it.

## Modules

- `SudokuTheory.Defs.Board` — board representation and regions
- `SudokuTheory.Defs.Valid` — validity predicates
- `SudokuTheory.Defs.Puzzle` — partial boards, solutions, and difficulty
-/
