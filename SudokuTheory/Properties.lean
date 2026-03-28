import SudokuTheory.Defs.Puzzle

/-!
# Relabeling

A *relabeling* is a permutation {lit}`σ : Equiv.Perm (Fin (m * n))` applied
to every cell value. Since the validity constraints only require each
region to contain *distinct* values, permuting which symbol goes where
preserves validity. The same applies to puzzles: relabeling all givens
by {lit}`σ` preserves the solution count.

## Relabeling a Board

Given a board {lit}`b` and a permutation {lit}`σ`, the relabeled board
maps each cell {lit}`(i, j)` to {lit}`σ (b i j)`.
-/

namespace SudokuTheory

variable {m n : Nat}

/-- Apply a value permutation to every cell of a board. -/
def Board.relabel (σ : Equiv.Perm (Fin (m * n))) (b : Board m n) : Board m n :=
  fun i j => σ (b i j)

/-- Relabeling preserves row validity: if row {lit}`i` has distinct values,
so does the relabeled row, because {lit}`σ` is injective. -/
theorem RowValid.relabel {b : Board m n} {i : Fin (m * n)}
    (h : RowValid b i) (σ : Equiv.Perm (Fin (m * n))) :
    RowValid (b.relabel σ) i :=
  σ.injective.comp h

/-- Relabeling preserves column validity. -/
theorem ColValid.relabel {b : Board m n} {j : Fin (m * n)}
    (h : ColValid b j) (σ : Equiv.Perm (Fin (m * n))) :
    ColValid (b.relabel σ) j :=
  σ.injective.comp h

/-- Relabeling preserves block validity. -/
theorem BlockValid.relabel [NeZero m] [NeZero n]
    {b : Board m n} {bi : Fin n} {bj : Fin m}
    (h : BlockValid m n b bi bj) (σ : Equiv.Perm (Fin (m * n))) :
    BlockValid m n (b.relabel σ) bi bj :=
  σ.injective.comp h

/-- Relabeling values preserves board validity. -/
theorem ValidBoard.relabel [NeZero m] [NeZero n]
    {b : Board m n} (h : ValidBoard m n b) (σ : Equiv.Perm (Fin (m * n))) :
    ValidBoard m n (b.relabel σ) :=
  ⟨fun i => (h.1 i).relabel σ,
   fun j => (h.2.1 j).relabel σ,
   fun bi bj => (h.2.2 bi bj).relabel σ⟩

/-!
# Relabeling a Puzzle

Applying {lit}`σ` to every given value in a puzzle preserves the
relationship between puzzles and solutions: {lit}`b` solves {lit}`p`
if and only if {lit}`σ ∘ b` solves the relabeled puzzle.
-/

/-- Apply a value permutation to every given in a puzzle. -/
def Puzzle.relabel (σ : Equiv.Perm (Fin (m * n))) (p : Puzzle m n) : Puzzle m n :=
  fun i j => (p i j).map σ

/-- If {lit}`b` agrees with {lit}`p`, then {lit}`σ ∘ b` agrees with
the relabeled puzzle. -/
theorem Agrees.relabel {p : Puzzle m n} {b : Board m n}
    (h : Agrees p b) (σ : Equiv.Perm (Fin (m * n))) :
    Agrees (p.relabel σ) (b.relabel σ) := by
  intro i j v hpij
  simp [Puzzle.relabel, Board.relabel] at hpij ⊢
  cases hv : p i j with
  | none => simp [hv] at hpij
  | some w =>
    simp [hv] at hpij
    rw [h i j w hv, hpij]

/-- Relabeling preserves the solution relationship. -/
theorem IsSolution.relabel [NeZero m] [NeZero n]
    {p : Puzzle m n} {b : Board m n}
    (h : IsSolution p b) (σ : Equiv.Perm (Fin (m * n))) :
    IsSolution (p.relabel σ) (b.relabel σ) :=
  ⟨h.1.relabel σ, h.2.relabel σ⟩

end SudokuTheory
