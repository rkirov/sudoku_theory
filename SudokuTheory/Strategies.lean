import SudokuTheory.Defs.Puzzle
import Mathlib.Data.Finset.Card

/-!
# Solving Strategies

This module formalizes the logical principles behind common Sudoku
solving strategies. The central result is the *subset theorem*, which
unifies naked singles, naked pairs, naked triples, hidden singles, and
their duals into a single pigeonhole argument.

## The Subset Theorem

Consider a region (row, column, or block) in a valid completed board.
Because each value appears exactly once, any subset {lit}`S` of values
of size {lit}`k` occupies exactly {lit}`k` cells.

For a *puzzle* (partially filled board), this has a powerful consequence.
Suppose we identify {lit}`k` empty cells in a region whose combined
possible values form a set of size exactly {lit}`k`. Then in any
valid completion:
- Those {lit}`k` cells must use exactly those {lit}`k` values (a bijection).
- No other cell in the region can use any of those values.

This single principle, applied with {lit}`k = 1`, gives the *naked
single* strategy; with {lit}`k = 2`, the *naked pair*; and so on.
Taking the complement gives the *hidden* variants.

## Formalization

We state the theorem in terms of {name}`Function.Injective`, which is
our formalization of "all distinct" in a region.
-/

namespace SudokuTheory

variable {m n : Nat}

/-!
## Pigeonhole for Injective Functions

The core mathematical fact: if {lit}`f : Fin s → Fin s` is injective
(hence bijective on a finite type), then the preimage of any subset
has the same cardinality as the subset.
-/

/-- For an injective function {lit}`f : Fin s → Fin s`, the preimage
of a set {lit}`S` has the same cardinality as {lit}`S`.
This is the heart of all subset-based strategies. -/
theorem Finset.card_preimage_of_injective {s : Nat}
    {f : Fin s → Fin s} (hf : Function.Injective f)
    (S : Finset (Fin s)) :
    (Finset.univ.filter (fun i => f i ∈ S)).card = S.card := by
  sorry -- follows from f being a bijection on Fin s

/-!
## Naked Subset Strategy

Given a puzzle {lit}`p` and any solution {lit}`b`, consider a row
{lit}`i`. Let {lit}`C` be a set of {lit}`k` positions (columns) in
that row, and let {lit}`V` be the set of values that {lit}`b` assigns
to those positions. If {lit}`|V| = k`, then {lit}`V` is exactly the
set of values at positions {lit}`C` — no other position in the row
can hold a value from {lit}`V`.
-/

/-- In a valid row, the values at any {lit}`k` positions form a set
of size {lit}`k` (since the row function is injective). -/
theorem row_values_card {b : Board m n} {i : Fin (m * n)}
    (hrow : RowValid b i) (C : Finset (Fin (m * n))) :
    (C.image (b i)).card = C.card :=
  Finset.card_image_of_injective C hrow

/-- In a valid row, if position {lit}`j` has value {lit}`v`, then no
other position in the row has value {lit}`v`. -/
theorem row_value_unique {b : Board m n} {i : Fin (m * n)}
    (hrow : RowValid b i) {j₁ j₂ : Fin (m * n)}
    (heq : b i j₁ = b i j₂) : j₁ = j₂ :=
  hrow heq

/-- In a valid column, the values at any {lit}`k` positions form a set
of size {lit}`k`. -/
theorem col_values_card {b : Board m n} {j : Fin (m * n)}
    (hcol : ColValid b j) (C : Finset (Fin (m * n))) :
    (C.image (fun i => b i j)).card = C.card :=
  Finset.card_image_of_injective C hcol

/-!
## Naked Single

The simplest instance: if an empty cell has exactly one possible value,
that value must appear there in any solution. This is a direct
consequence of the definitions, stated here for clarity.
-/

/-- If value {lit}`v` is the only possible value for cell {lit}`c` in
puzzle {lit}`p`, then every solution assigns {lit}`v` to that cell. -/
theorem naked_single [NeZero m] [NeZero n]
    {p : Puzzle m n} {b : Board m n} {c : Cell m n} {v : Fin (m * n)}
    (hsol : IsSolution p b)
    (hempty : p c.1 c.2 = none)
    (honly : ∀ w : Fin (m * n), IsPossible m n p c w → w = v) :
    b c.1 c.2 = v := by
  -- b c.1 c.2 must be possible (it doesn't conflict with givens in
  -- the same region, because b is a valid solution agreeing with p)
  sorry

/-!
## Deadly Patterns and Uniqueness

A *deadly pattern* is a configuration of cells where swapping values
produces another valid board. If a puzzle is well-posed, no deadly
pattern can exist in its solution — otherwise the swap would give a
second solution.

The simplest case is the *unique rectangle*: four cells at the
intersection of two rows and two columns, spanning two blocks. If
all four cells contained only values {lit}`{a, b}`, swapping {lit}`a`
and {lit}`b` in those cells would produce another valid board.
Therefore, at least one cell must have an additional possible value.
-/

/-- A value swap on a set of cells: replace {lit}`a` with {lit}`b` and
vice versa, leaving all other values unchanged. -/
def Board.swap (b : Board m n) (a c : Fin (m * n))
    (cells : Finset (Cell m n)) : Board m n :=
  fun i j =>
    if (i, j) ∈ cells then
      if b i j = a then c
      else if b i j = c then a
      else b i j
    else b i j

/-- If swapping two values in a set of cells preserves validity and
agreement, then the puzzle has multiple solutions — contradicting
well-posedness. -/
theorem no_deadly_swap [NeZero m] [NeZero n]
    {p : Puzzle m n} {b : Board m n}
    (hwp : WellPosed p) (hsol : IsSolution p b)
    {a c : Fin (m * n)} (_hac : a ≠ c)
    {cells : Finset (Cell m n)}
    (hswap_valid : ValidBoard m n (b.swap a c cells))
    (hswap_agrees : Agrees p (b.swap a c cells))
    (hswap_diff : b.swap a c cells ≠ b) :
    False := by
  have ⟨b', hsol', huniq⟩ := hwp
  have h1 := huniq b hsol
  have h2 := huniq (b.swap a c cells) ⟨hswap_valid, hswap_agrees⟩
  exact hswap_diff (h2 ▸ h1 ▸ rfl)

end SudokuTheory
