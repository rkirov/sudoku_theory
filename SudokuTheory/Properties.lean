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

/-!
# Row Permutations

Permuting the rows of a board by {lit}`σ : Equiv.Perm (Fin (m * n))`
always preserves row and column validity — each row still contains
the same values, and each column is just a rearrangement of what it was.

However, an arbitrary row permutation does **not** preserve block
validity. Blocks are only preserved when the permutation *respects
bands*: it maps each horizontal band (a group of {lit}`m` consecutive
rows sharing the same block-row index) to some band.

Formally, {lit}`σ` respects bands when
{lit}`∀ i₁ i₂, i₁.val / m = i₂.val / m → (σ i₁).val / m = (σ i₂).val / m`.
This includes two important special cases:
- **Within-band permutations**: {lit}`σ` fixes each band
  ({lit}`(σ i).val / m = i.val / m` for all {lit}`i`).
- **Band permutations**: {lit}`σ` permutes entire bands as blocks
  (every row in band {lit}`k` maps to some band {lit}`σ'(k)`).

The set of all band-respecting row permutations forms the *wreath
product* {lit}`Sym(Fin m) ≀ Sym(Fin n)`, and analogously for columns.
-/

/-- Permute the rows of a board. -/
def Board.permuteRows (σ : Equiv.Perm (Fin (m * n))) (b : Board m n) : Board m n :=
  fun i j => b (σ i) j

/-- Row permutation preserves row validity: row {lit}`i` of the permuted
board is row {lit}`σ i` of the original, which has the same values. -/
theorem RowValid.permuteRows {b : Board m n} {i : Fin (m * n)}
    (σ : Equiv.Perm (Fin (m * n))) (h : RowValid b (σ i)) :
    RowValid (b.permuteRows σ) i :=
  h

/-- Row permutation preserves column validity: each column is a
rearrangement of the original column. -/
theorem ColValid.permuteRows {b : Board m n} {j : Fin (m * n)}
    (h : ColValid b j) (σ : Equiv.Perm (Fin (m * n))) :
    ColValid (b.permuteRows σ) j :=
  h.comp σ.injective

/-- A row permutation *respects bands* if rows in the same band are
mapped to rows in the same band. -/
def RespectsBands (m : Nat) [NeZero m] (σ : Equiv.Perm (Fin (m * n))) : Prop :=
  ∀ i₁ i₂ : Fin (m * n), i₁.val / m = i₂.val / m → (σ i₁).val / m = (σ i₂).val / m

/-- A band-respecting row permutation preserves block validity. -/
theorem BlockValid.permuteRows [NeZero m] [NeZero n]
    {b : Board m n} {bi : Fin n} {bj : Fin m}
    (h : BlockValid m n b bi bj)
    (σ : Equiv.Perm (Fin (m * n)))
    (hσ : RespectsBands m σ) :
    ∃ bi' : Fin n, BlockValid m n (b.permuteRows σ) bi' bj := by
  sorry -- the target block-row is determined by σ's action on the band

/-!
# Column Permutations

Column permutations are entirely analogous to row permutations.
-/

/-- Permute the columns of a board. -/
def Board.permuteCols (σ : Equiv.Perm (Fin (m * n))) (b : Board m n) : Board m n :=
  fun i j => b i (σ j)

/-- Column permutation preserves row validity. -/
theorem RowValid.permuteCols {b : Board m n} {i : Fin (m * n)}
    (h : RowValid b i) (σ : Equiv.Perm (Fin (m * n))) :
    RowValid (b.permuteCols σ) i :=
  h.comp σ.injective

/-- Column permutation preserves column validity. -/
theorem ColValid.permuteCols {b : Board m n} {j : Fin (m * n)}
    (σ : Equiv.Perm (Fin (m * n))) (h : ColValid b (σ j)) :
    ColValid (b.permuteCols σ) j :=
  h

/-- A column permutation *respects stacks* if columns in the same stack
(vertical band of {lit}`n` columns) are mapped to columns in the same stack. -/
def RespectsStacks (n : Nat) [NeZero n] (σ : Equiv.Perm (Fin (m * n))) : Prop :=
  ∀ j₁ j₂ : Fin (m * n), j₁.val / n = j₂.val / n → (σ j₁).val / n = (σ j₂).val / n

end SudokuTheory
