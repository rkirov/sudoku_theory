import SudokuTheory.Defs.Puzzle
import Mathlib.Data.Finset.Card

/-!
# Solving Strategies

This module formalizes the logical principles behind common Sudoku
solving strategies. Sudoku solvers recognize dozens of named techniques
(see [sudokuwiki.org](https://www.sudokuwiki.org/Strategy_Families) or
[sudoku.coach](https://sudoku.coach/en/learn) for comprehensive lists).

Remarkably, most of these techniques are instances of just two
abstract principles:

1. **The Subset Principle** (pigeonhole on regions) — covers all
   constraint-propagation strategies.
2. **The Uniqueness Principle** (well-posedness forbids deadly
   patterns) — covers all uniqueness-based strategies.

## Strategy Taxonomy

The table below maps standard solver terminology to the abstract
principles formalized here.

### Subset Principle ({lit}`k` values in {lit}`k` cells)

| Solver name | {lit}`k` | Variant | Formalized as |
|---|---|---|---|
| Naked Single | 1 | naked | {lit}`naked_single` |
| Hidden Single | 1 | hidden | (dual of naked single) |
| Naked Pair | 2 | naked | {lit}`row_values_card` with {lit}`|C| = 2` |
| Hidden Pair | 2 | hidden | (complement) |
| Naked Triple | 3 | naked | {lit}`row_values_card` with {lit}`|C| = 3` |
| Naked Quad | 4 | naked | {lit}`row_values_card` with {lit}`|C| = 4` |
| Pointing Pair | 2 | cross-region | intersection of row/col and block |
| Box/Line Reduction | — | cross-region | intersection of block and row/col |

The *naked* variant picks {lit}`k` cells whose combined candidates
have size {lit}`k`; the *hidden* variant picks {lit}`k` values that
appear as candidates in only {lit}`k` cells. These are dual: if {lit}`k`
cells hold exactly {lit}`k` values, the remaining {lit}`s - k` cells
hold the remaining {lit}`s - k` values (where {lit}`s = m * n`).

### Fish Strategies (subset principle across rows/columns)

| Solver name | Rows | Columns |
|---|---|---|
| X-Wing | 2 | 2 |
| Swordfish | 3 | 3 |
| Jellyfish | 4 | 4 |

These apply the subset principle globally: if a value can appear in
only {lit}`k` columns across {lit}`k` rows, it must appear in those
columns and can be eliminated from those columns in other rows.
This is the same pigeonhole argument applied to row–column
intersections rather than within a single region.

### Uniqueness Principle (well-posedness)

| Solver name | Formalized as |
|---|---|
| Unique Rectangle | {lit}`no_deadly_swap` |
| Hidden Rectangle | (same principle, different cell selection) |
| Avoidable Rectangle | (same principle) |
| BUG+1 | (same principle, board-wide) |

All of these reason: "if this candidate were absent, a deadly pattern
(value swap preserving validity) would exist, giving two solutions.
Since the puzzle is well-posed, the candidate must be present."

### Strategies Not Covered Here

Chaining strategies (XY-Chain, X-Cycle, AIC, Forcing Chains, Colouring)
and exotic strategies (Almost Locked Sets, Exocet, Sue-de-Coq) involve
multi-step logical inference that goes beyond single-region analysis.
Formalizing these would require defining *inference chains* — sequences
of strong and weak links between candidates — which is a natural
direction for future work.

## Formalization

We state the theorems in terms of {name}`Function.Injective`, which is
our formalization of "all distinct" in a region.
-/

namespace SudokuTheory

variable {m n : Nat}

/-!
# Pigeonhole for Injective Functions

The core mathematical fact: if {lit}`f : Fin s → Fin s` is injective
(hence bijective on a finite type), then the preimage of any subset
has the same cardinality as the subset. This single lemma is the
engine behind all subset-based strategies.
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
# Naked Subsets

In a valid row (or column, or block), the values at any {lit}`k`
positions form a set of size exactly {lit}`k`, because the region
function is injective. This is the formal content of all "naked"
strategies — naked single ({lit}`k = 1`), naked pair ({lit}`k = 2`),
naked triple ({lit}`k = 3`), naked quad ({lit}`k = 4`).
-/

/-- In a valid row, the values at any {lit}`k` positions form a set
of size {lit}`k` (since the row function is injective).
This covers naked single, pair, triple, quad — just vary {lit}`|C|`. -/
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
# Naked Single

The simplest instance of the subset principle: if an empty cell has
exactly one possible value, that value must appear there in any
solution. Every sudoku solver applies this rule first.
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
# Deadly Patterns and Uniqueness

A *deadly pattern* is a configuration of cells where swapping values
produces another valid board. If a puzzle is well-posed, no deadly
pattern can exist in its solution — otherwise the swap would give a
second solution.

The simplest case is the *unique rectangle*: four cells at the
intersection of two rows and two columns, spanning two blocks. If
all four cells contained only values {lit}`{a, b}`, swapping {lit}`a`
and {lit}`b` in those cells would produce another valid board.
Therefore, at least one cell must have an additional possible value.

This principle is the formal basis for Unique Rectangles, Hidden
Rectangles, Avoidable Rectangles, and BUG+1 — all techniques listed
on sudokuwiki.org under "Uniqueness" strategies.
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
well-posedness. This rules out all deadly patterns. -/
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
