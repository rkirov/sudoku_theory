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

The puzzle has a unique solution. Existence is proved above;
uniqueness is verified computationally in {lit}`Examples/HardPuzzle.lean`
but not yet proved formally.

**Why {lit}`decide` can't close this:** the uniqueness goal
{lit}`∀ b : Board 2 3, IsSolution p b → b = solution` quantifies over
{lit}`Board 2 3 = Fin 6 → Fin 6 → Fin 6`, a type with 6³⁶ ≈ 10²⁸
elements. Lean's {lit}`Decidable` instance for {lit}`∀` over a {lit}`Fintype`
enumerates every element — no pruning. By contrast, the backtracking
solver in {lit}`HardPuzzle.lean` uses constraint propagation and explores
only a few hundred partial boards.

Possible approaches to close this {lit}`sorry`:
1. Formalize a constraint-propagation solver in Lean and prove it sound
   and complete, then run it on this puzzle.
2. Use a proof-by-reflection tactic that executes the smart search
   inside the kernel.
3. Prove uniqueness manually by chaining cell-by-cell deductions
   (each cell is forced by pairs, triples, or other strategies even
   though no naked single exists).
-/

theorem puzzle23_wellposed : WellPosed puzzle23 := by
  refine ⟨solution23, solution23_is_solution, ?_⟩
  intro b hb
  sorry

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
