/-!
# Sudoku Boards

A Sudoku board of order {lit}`m × n` is a grid of {lit}`(m * n) × (m * n)` cells,
divided into rectangular blocks of {lit}`m` rows and {lit}`n` columns.

For example, the first block contains the intersection of the first {lit}`m` rows and first {lit}`n` columns,
 the second block contains the intersection of the first {lit}`m` rows and second {lit}`n` columns, and so on.

Each cell contains a value from {lit}`Fin (m * n)`.

We represent a board as a function from row and column indices to values.

## Regions

Every cell belongs to exactly three *regions*: its row, its column, and its block.
The validity constraints require each region to contain every value exactly once.

For an order {lit}`m × n` board:
- There are {lit}`m * n` rows and {lit}`m * n` columns.
- There are {lit}`n` block-rows (horizontal bands of {lit}`m` rows each) and
  {lit}`m` block-columns (vertical bands of {lit}`n` columns each),
  giving {lit}`m * n` blocks total.
- Each block spans {lit}`m` consecutive rows and {lit}`n` consecutive columns.
-/

/-- A completed Sudoku board of order {lit}`m × n`: an {lit}`(m * n) × (m * n)` grid
where every cell is filled with a value in {lit}`Fin (m * n)`.
-/
abbrev SudokuTheory.Board (m n : Nat) := Fin (m * n) → Fin (m * n) → Fin (m * n)

namespace SudokuTheory

variable {m n : Nat}

/-- A cell is a position on the board, identified by a row–column pair. -/
abbrev Cell (m n : Nat) := Fin (m * n) × Fin (m * n)

/-!
## Same-Region Predicates

Rather than building explicit sets of cell coordinates, we define when
two cells share a region. These predicates are used in the validity
and puzzle definitions.
-/

/-- Two cells are in the same row when they share a row index. -/
def sameRow (c₁ c₂ : Cell m n) : Prop := c₁.1 = c₂.1

/-- Two cells are in the same column when they share a column index. -/
def sameCol (c₁ c₂ : Cell m n) : Prop := c₁.2 = c₂.2

/-- Two cells are in the same block of an order {lit}`m × n` board.
Cell {lit}`(i, j)` belongs to block {lit}`(i / m, j / n)`. -/
def sameBlock (m n : Nat) [NeZero m] [NeZero n]
    (c₁ c₂ : Cell m n) : Prop :=
  c₁.1.val / m = c₂.1.val / m ∧ c₁.2.val / n = c₂.2.val / n

/-- Two cells share a region (row, column, or block), thus constraining
each other's possible values. -/
def sameRegion (m n : Nat) [NeZero m] [NeZero n]
    (c₁ c₂ : Cell m n) : Prop :=
  sameRow c₁ c₂ ∨ sameCol c₁ c₂ ∨ sameBlock m n c₁ c₂

end SudokuTheory
