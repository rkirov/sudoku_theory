import SudokuTheory.Defs.Valid
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod

/-!
# Puzzles and Solutions

A *puzzle* is a partially filled board: some cells have given values,
others are empty. A *solution* to a puzzle is a valid (completed) board
that agrees with all the given cells.

Note that in this formalization, filling in a cell produces a new puzzle
with one fewer empty cell. Solving a Sudoku is thus a sequence of puzzles,
each strictly closer to the final board. There is no mutable state — each
step is a fresh, more constrained puzzle.

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
  ∃! b, IsSolution p b

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

All definitions below are {lit}`Prop`-valued with {lit}`Decidable` instances,
so they work both for formal proofs and for computation via
{lit}`native_decide`.
-/

/-- Value {lit}`v` conflicts with a given in the same row as cell {lit}`c`. -/
def RowConflict (p : Puzzle m n) (c : Cell m n) (v : Fin (m * n)) : Prop :=
  ∃ j', j' ≠ c.2 ∧ p c.1 j' = some v

/-- Value {lit}`v` conflicts with a given in the same column as cell {lit}`c`. -/
def ColConflict (p : Puzzle m n) (c : Cell m n) (v : Fin (m * n)) : Prop :=
  ∃ i', i' ≠ c.1 ∧ p i' c.2 = some v

/-- Value {lit}`v` conflicts with a given in the same block as cell {lit}`c`. -/
def BlockConflict (m n : Nat) [NeZero m] [NeZero n]
    (p : Puzzle m n) (c : Cell m n) (v : Fin (m * n)) : Prop :=
  ∃ c' : Cell m n, c' ≠ c ∧
    c'.1.val / m = c.1.val / m ∧ c'.2.val / n = c.2.val / n ∧
    p c'.1 c'.2 = some v

/-- Value {lit}`v` is *possible* for cell {lit}`c`: it does not conflict
with any given in the same row, column, or block. -/
def IsPossible (m n : Nat) [NeZero m] [NeZero n]
    (p : Puzzle m n) (c : Cell m n) (v : Fin (m * n)) : Prop :=
  ¬RowConflict p c v ∧ ¬ColConflict p c v ∧ ¬BlockConflict m n p c v

/-!
### Decidability

Each conflict predicate quantifies over a finite type, making it
decidable via {name}`Fintype.decidableExistsFintype`.
-/

instance (p : Puzzle m n) (c : Cell m n) (v : Fin (m * n)) :
    Decidable (RowConflict p c v) := Fintype.decidableExistsFintype

instance (p : Puzzle m n) (c : Cell m n) (v : Fin (m * n)) :
    Decidable (ColConflict p c v) := Fintype.decidableExistsFintype

instance [NeZero m] [NeZero n] (p : Puzzle m n) (c : Cell m n) (v : Fin (m * n)) :
    Decidable (BlockConflict m n p c v) := Fintype.decidableExistsFintype

instance [NeZero m] [NeZero n] (p : Puzzle m n) (c : Cell m n) (v : Fin (m * n)) :
    Decidable (IsPossible m n p c v) := instDecidableAnd

/-- The finite set of possible values for cell {lit}`c`: all values in
{lit}`Fin (m * n)` that do not conflict with any given in the same row,
column, or block. -/
def possibleSet (m n : Nat) [NeZero m] [NeZero n]
    (p : Puzzle m n) (c : Cell m n) : Finset (Fin (m * n)) :=
  Finset.univ.filter (IsPossible m n p c ·)

/-!
## Hard Puzzles

A well-posed puzzle is *hard* (with respect to naked singles) if it has
at least one empty cell, and the possible set of every empty cell has
cardinality at least 2. Such puzzles cannot be solved by the most basic
elimination strategy.

We require at least one empty cell to exclude the trivial case of a
fully filled board, which would satisfy the cardinality condition
vacuously.
-/

/-- A well-posed puzzle with at least one empty cell where every empty
cell has at least two possible values. -/
def HardPuzzle (m n : Nat) [NeZero m] [NeZero n] (p : Puzzle m n) : Prop :=
  WellPosed p ∧
  (∃ c : Cell m n, p c.1 c.2 = none) ∧
  ∀ c : Cell m n, p c.1 c.2 = none →
    2 ≤ (possibleSet m n p c).card

end SudokuTheory
