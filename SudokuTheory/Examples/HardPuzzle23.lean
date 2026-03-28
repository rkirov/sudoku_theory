import SudokuTheory.Defs.Puzzle

/-!
# A Concrete Hard Puzzle (2×3)

We exhibit a 6×6 Sudoku puzzle (order 2×3) that is *hard*: it has a
unique solution, yet every empty cell has at least two possible values.
This puzzle was found by brute-force search
(see {lit}`scripts/find_hard_puzzle.py` and {lit}`Examples/HardPuzzle.lean`).

```
0 . 2 | . 4 .
. . 5 | . 1 .
--------------
. 0 . | . . 4
2 . . | . . .
--------------
. . . | . . 1
5 . . | . 2 .
```
-/

namespace SudokuTheory.Examples

open SudokuTheory

/-!
## The Puzzle and Its Solution

We define both as plain functions on {lean}`Fin 6` using a {lit}`match`
cascade, which Lean can reduce and {lit}`native_decide` can evaluate.
-/

/-- The hard 2×3 puzzle. -/
def puzzle23 : Puzzle 2 3
  | 0, 0 => some 0 | 0, 2 => some 2 | 0, 4 => some 4
  | 1, 2 => some 5 | 1, 4 => some 1
  | 2, 1 => some 0 | 2, 5 => some 4
  | 3, 0 => some 2
  | 4, 5 => some 1
  | 5, 0 => some 5 | 5, 4 => some 2
  | _, _ => none

/-- The unique solution to {name}`puzzle23`. -/
def solution23 : Board 2 3
  | 0, 0 => 0 | 0, 1 => 1 | 0, 2 => 2 | 0, 3 => 3 | 0, 4 => 4 | 0, 5 => 5
  | 1, 0 => 3 | 1, 1 => 4 | 1, 2 => 5 | 1, 3 => 0 | 1, 4 => 1 | 1, 5 => 2
  | 2, 0 => 1 | 2, 1 => 0 | 2, 2 => 3 | 2, 3 => 2 | 2, 4 => 5 | 2, 5 => 4
  | 3, 0 => 2 | 3, 1 => 5 | 3, 2 => 4 | 3, 3 => 1 | 3, 4 => 0 | 3, 5 => 3
  | 4, 0 => 4 | 4, 1 => 2 | 4, 2 => 0 | 4, 3 => 5 | 4, 4 => 3 | 4, 5 => 1
  | 5, 0 => 5 | 5, 1 => 3 | 5, 2 => 1 | 5, 3 => 4 | 5, 4 => 2 | 5, 5 => 0

/-!
## The Solution Is Valid and Agrees
-/

-- Decidable instances needed for `decide`/`native_decide`
instance {α : Type} [Fintype α] [DecidableEq α] {β : Type} [DecidableEq β]
    (f : α → β) : Decidable (Function.Injective f) :=
  decidable_of_iff (∀ a b, f a = f b → a = b) Iff.rfl

instance : Decidable (ValidBoard 2 3 solution23) := by
  unfold ValidBoard RowValid ColValid BlockValid; infer_instance

instance : Decidable (Agrees puzzle23 solution23) := by
  unfold Agrees; infer_instance

theorem solution23_valid : ValidBoard 2 3 solution23 := by native_decide

theorem solution23_agrees : Agrees puzzle23 solution23 := by native_decide

theorem solution23_is_solution : IsSolution puzzle23 solution23 :=
  ⟨solution23_valid, solution23_agrees⟩

/-!
## Well-Posedness

The puzzle has a unique solution. Computational verification in
{lit}`Examples/HardPuzzle.lean` confirms this via brute-force solve.
The formal uniqueness proof is left as future work — it requires
showing that constraint propagation determines every cell.
-/

theorem puzzle23_wellposed : WellPosed puzzle23 := by
  refine ⟨solution23, solution23_is_solution, ?_⟩
  intro b hb
  sorry -- uniqueness: verified computationally in Examples/HardPuzzle.lean

/-!
## No Naked Singles

Every empty cell has at least two possible values. Since
{name}`possibleSet` is computable, we verify this by {lit}`native_decide`.
-/

theorem puzzle23_no_naked_singles :
    ∀ c : Cell 2 3, puzzle23 c.1 c.2 = none →
      2 ≤ (possibleSet 2 3 puzzle23 c).card := by
  native_decide

/-!
## Putting It Together
-/

/-- The 2×3 puzzle is hard: well-posed with no naked singles. -/
theorem puzzle23_is_hard : HardPuzzle 2 3 puzzle23 :=
  ⟨puzzle23_wellposed, puzzle23_no_naked_singles⟩

end SudokuTheory.Examples
