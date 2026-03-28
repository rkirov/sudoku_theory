import SudokuTheory.Defs.Valid

/-!
# Puzzles and Solutions

A *puzzle* is a partially filled board: some cells have given values,
others are empty. A *solution* to a puzzle is a valid completed board
that agrees with all the given cells.

We classify puzzles by their solution count:
- *well-posed*: exactly one solution (the standard for published puzzles)
- *unsolvable*: no solution exists
- *ambiguous*: multiple solutions exist

## Possible Values

For each empty cell, the set of *possible* values consists of those
not yet ruled out by the givens in the same row, column, or block.
A puzzle where no empty cell has a singleton possible set (yet still
has a unique solution) is considered *hard* — it cannot be advanced
by the naked-single strategy alone.
-/

namespace SudokuTheory

variable {m n : Nat}

/-- A puzzle of order {lit}`m × n`: a partially filled board where
{lit}`none` represents an empty cell and {lit}`some v` a given value. -/
abbrev Puzzle (m n : Nat) := Fin (m * n) → Fin (m * n) → Option (Fin (m * n))

/-- Board {lit}`b` agrees with puzzle {lit}`p` on every given cell. -/
def Agrees (p : Puzzle m n) (b : Board m n) : Prop :=
  ∀ i j v, p i j = some v → b i j = v

/-- Board {lit}`b` is a solution to puzzle {lit}`p`: it is a valid completed board
that agrees with all givens. -/
def IsSolution [NeZero m] [NeZero n] (p : Puzzle m n) (b : Board m n) : Prop :=
  ValidBoard m n b ∧ Agrees p b

/-!
## Solution Classification
-/

/-- A puzzle has a unique solution (well-posed). -/
def WellPosed [NeZero m] [NeZero n] (p : Puzzle m n) : Prop :=
  ∃ b, IsSolution p b ∧ ∀ b', IsSolution p b' → b' = b

/-- A puzzle has no solution. -/
def Unsolvable [NeZero m] [NeZero n] (p : Puzzle m n) : Prop :=
  ¬∃ b, IsSolution p b

/-- A puzzle has more than one solution. -/
def Ambiguous [NeZero m] [NeZero n] (p : Puzzle m n) : Prop :=
  ∃ b₁ b₂, IsSolution p b₁ ∧ IsSolution p b₂ ∧ b₁ ≠ b₂

/-!
## Possible Values

A value is *possible* for an empty cell if placing it there would not
immediately conflict with any given in the same row, column, or block.
-/

/-- Value {lit}`v` conflicts with a given in the same row as cell {lit}`(i, j)`. -/
def RowConflict (p : Puzzle m n) (i j : Fin (m * n)) (v : Fin (m * n)) : Prop :=
  ∃ j', j' ≠ j ∧ p i j' = some v

/-- Value {lit}`v` conflicts with a given in the same column as cell {lit}`(i, j)`. -/
def ColConflict (p : Puzzle m n) (i j : Fin (m * n)) (v : Fin (m * n)) : Prop :=
  ∃ i', i' ≠ i ∧ p i' j = some v

/-- Value {lit}`v` conflicts with a given in the same block as cell {lit}`(i, j)`. -/
def BlockConflict (m n : Nat) [NeZero m] [NeZero n]
    (p : Puzzle m n) (i j : Fin (m * n)) (v : Fin (m * n)) : Prop :=
  ∃ i' j', (i', j') ≠ (i, j) ∧
    i'.val / m = i.val / m ∧ j'.val / n = j.val / n ∧
    p i' j' = some v

/-- Value {lit}`v` is *possible* for cell {lit}`(i, j)`: it does not conflict
with any given in the same row, column, or block. -/
def IsPossible (m n : Nat) [NeZero m] [NeZero n]
    (p : Puzzle m n) (i j : Fin (m * n)) (v : Fin (m * n)) : Prop :=
  ¬RowConflict p i j v ∧ ¬ColConflict p i j v ∧ ¬BlockConflict m n p i j v

/-!
## Hard Puzzles

A well-posed puzzle is *hard* (with respect to naked singles) if every
empty cell has at least two possible values. Such puzzles cannot be
solved by the most basic elimination strategy.
-/

/-- A well-posed puzzle where no empty cell has a unique possible value. -/
def HardPuzzle (m n : Nat) [NeZero m] [NeZero n] (p : Puzzle m n) : Prop :=
  WellPosed p ∧
  ∀ i j, p i j = none →
    ∀ v, IsPossible m n p i j v →
      ∃ w, w ≠ v ∧ IsPossible m n p i j w

end SudokuTheory
