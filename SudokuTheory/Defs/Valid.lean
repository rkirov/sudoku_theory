import SudokuTheory.Defs.Board

/-!
# Valid Sudoku

A completed board is *valid* when every row, every column, and every block
contains each value exactly once. We formalize "each value exactly once"
as {name}`Function.Injective` — injectivity on a function between finite types
of equal cardinality is equivalent to bijectivity (by pigeonhole)
and thus the function is a permutation of the values in that region.

## Definitions

We define three predicates — row validity, column validity, and block
validity — then combine them into a single {lit}`ValidBoard` predicate.
-/

namespace SudokuTheory

variable {m n : Nat}

/-- Row {lit}`i` of board {lit}`b` is valid: all values in that row are distinct. -/
def RowValid (b : Board m n) (i : Fin (m * n)) : Prop :=
  Function.Injective (b i)

/-- Column {lit}`j` of board {lit}`b` is valid: all values in that column are distinct. -/
def ColValid (b : Board m n) (j : Fin (m * n)) : Prop :=
  Function.Injective (fun i => b i j)

/-- Block {lit}`(bi, bj)` of an order {lit}`m × n` board is valid: all values
in that block are distinct (see {name}`SudokuTheory.Board` for the block indexing scheme). -/
-- To index into a board of size `m * n`, we need proofs that
-- block-relative coordinates stay within bounds.
private theorem block_row_bound {bi : Fin n} {di : Fin m} :
    bi.val * m + di.val < m * n := by
  calc bi.val * m + di.val
      < bi.val * m + m := Nat.add_lt_add_left di.isLt _
    _ = (bi.val + 1) * m := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ n * m := Nat.mul_le_mul_right m (by omega)
    _ = m * n := Nat.mul_comm n m

private theorem block_col_bound {bj : Fin m} {dj : Fin n} :
    bj.val * n + dj.val < m * n := by
  calc bj.val * n + dj.val
      < bj.val * n + n := Nat.add_lt_add_left dj.isLt _
    _ = (bj.val + 1) * n := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ m * n := Nat.mul_le_mul_right n (by omega)

def BlockValid (m n : Nat) [NeZero m] [NeZero n]
    (b : Board m n) (bi : Fin n) (bj : Fin m) : Prop :=
  Function.Injective (fun (p : Fin m × Fin n) =>
    b ⟨bi.val * m + p.1.val, block_row_bound⟩
      ⟨bj.val * n + p.2.val, block_col_bound⟩)

/-!
## Combined Validity

A board is a valid Sudoku when all rows, columns, and blocks are valid.
-/

/-- A completed board is a valid Sudoku of order {lit}`m × n`. -/
def ValidBoard (m n : Nat) [NeZero m] [NeZero n] (b : Board m n) : Prop :=
  (∀ i, RowValid b i) ∧
  (∀ j, ColValid b j) ∧
  (∀ bi bj, BlockValid m n b bi bj)

end SudokuTheory
