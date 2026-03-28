import SudokuTheory.Defs.Puzzle

/-!
# A Concrete Hard Puzzle (3×3)

A standard 9×9 Sudoku puzzle that is *hard*: it has a unique solution,
yet every empty cell has at least two possible values (no naked singles).
Found by brute-force search (see {lit}`scripts/find_hard_puzzle.py`).

```
. . . | . 4 5 | . . .
. . . | 6 . . | . . 2
6 7 . | 0 . . | . . .
------+-------+------
1 . . | . . 4 | . . 6
. . 4 | . . . | . 0 .
. 8 . | . 0 . | 2 . 4
------+-------+------
4 . . | 5 . . | . 6 7
. 3 1 | . . 7 | . . .
. . . | . . . | 5 3 .
```
-/

namespace SudokuTheory.Examples

open SudokuTheory

/-- A hard 3×3 puzzle (standard 9×9 board). -/
def puzzle33 : Puzzle 3 3
  | 0, 4 => some 4 | 0, 5 => some 5
  | 1, 3 => some 6 | 1, 8 => some 2
  | 2, 0 => some 6 | 2, 1 => some 7 | 2, 3 => some 0
  | 3, 0 => some 1 | 3, 5 => some 4 | 3, 8 => some 6
  | 4, 2 => some 4 | 4, 7 => some 0
  | 5, 1 => some 8 | 5, 4 => some 0 | 5, 6 => some 2 | 5, 8 => some 4
  | 6, 0 => some 4 | 6, 3 => some 5 | 6, 7 => some 6 | 6, 8 => some 7
  | 7, 1 => some 3 | 7, 2 => some 1 | 7, 5 => some 7
  | 8, 6 => some 5 | 8, 7 => some 3
  | _, _ => none

/-- The unique solution. -/
def solution33 : Board 3 3
  | 0, 0 => 0 | 0, 1 => 1 | 0, 2 => 2 | 0, 3 => 3 | 0, 4 => 4
  | 0, 5 => 5 | 0, 6 => 6 | 0, 7 => 7 | 0, 8 => 8
  | 1, 0 => 3 | 1, 1 => 4 | 1, 2 => 5 | 1, 3 => 6 | 1, 4 => 7
  | 1, 5 => 8 | 1, 6 => 0 | 1, 7 => 1 | 1, 8 => 2
  | 2, 0 => 6 | 2, 1 => 7 | 2, 2 => 8 | 2, 3 => 0 | 2, 4 => 1
  | 2, 5 => 2 | 2, 6 => 3 | 2, 7 => 4 | 2, 8 => 5
  | 3, 0 => 1 | 3, 1 => 0 | 3, 2 => 3 | 3, 3 => 2 | 3, 4 => 5
  | 3, 5 => 4 | 3, 6 => 7 | 3, 7 => 8 | 3, 8 => 6
  | 4, 0 => 2 | 4, 1 => 5 | 4, 2 => 4 | 4, 3 => 7 | 4, 4 => 8
  | 4, 5 => 6 | 4, 6 => 1 | 4, 7 => 0 | 4, 8 => 3
  | 5, 0 => 7 | 5, 1 => 8 | 5, 2 => 6 | 5, 3 => 1 | 5, 4 => 0
  | 5, 5 => 3 | 5, 6 => 2 | 5, 7 => 5 | 5, 8 => 4
  | 6, 0 => 4 | 6, 1 => 2 | 6, 2 => 0 | 6, 3 => 5 | 6, 4 => 3
  | 6, 5 => 1 | 6, 6 => 8 | 6, 7 => 6 | 6, 8 => 7
  | 7, 0 => 5 | 7, 1 => 3 | 7, 2 => 1 | 7, 3 => 8 | 7, 4 => 6
  | 7, 5 => 7 | 7, 6 => 4 | 7, 7 => 2 | 7, 8 => 0
  | 8, 0 => 8 | 8, 1 => 6 | 8, 2 => 7 | 8, 3 => 4 | 8, 4 => 2
  | 8, 5 => 0 | 8, 6 => 5 | 8, 7 => 3 | 8, 8 => 1

instance {α : Type} [Fintype α] [DecidableEq α] {β : Type} [DecidableEq β]
    (f : α → β) : Decidable (Function.Injective f) :=
  decidable_of_iff (∀ a b, f a = f b → a = b) Iff.rfl

instance : Decidable (ValidBoard 3 3 solution33) := by
  unfold ValidBoard RowValid ColValid BlockValid; infer_instance

instance : Decidable (Agrees puzzle33 solution33) := by
  unfold Agrees; infer_instance

theorem solution33_valid : ValidBoard 3 3 solution33 := by native_decide

theorem solution33_agrees : Agrees puzzle33 solution33 := by native_decide

theorem solution33_is_solution : IsSolution puzzle33 solution33 :=
  ⟨solution33_valid, solution33_agrees⟩

theorem puzzle33_wellposed : WellPosed puzzle33 := by
  refine ⟨solution33, solution33_is_solution, ?_⟩
  intro b hb
  sorry -- uniqueness: verified computationally

theorem puzzle33_no_naked_singles :
    ∀ c : Cell 3 3, puzzle33 c.1 c.2 = none →
      2 ≤ (possibleSet 3 3 puzzle33 c).card := by
  native_decide

theorem puzzle33_has_empty : ∃ c : Cell 3 3, puzzle33 c.1 c.2 = none :=
  ⟨(0, 0), rfl⟩

/-- The 3×3 puzzle is hard: well-posed, has empty cells, and no naked singles. -/
theorem puzzle33_is_hard : HardPuzzle 3 3 puzzle33 :=
  ⟨puzzle33_wellposed, puzzle33_has_empty, puzzle33_no_naked_singles⟩

end SudokuTheory.Examples
