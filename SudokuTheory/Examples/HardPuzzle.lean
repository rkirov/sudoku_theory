/-!
# Hard Puzzle Search

A *hard puzzle* (with respect to naked singles) is a well-posed puzzle
where every empty cell has at least two possible values — no cell can
be filled by simple elimination alone.

This module provides a brute-force solver and hard-puzzle checker,
then exhibits a concrete 2×3 (6×6) hard puzzle found by search.

This is a computational script — no correctness proofs are attempted here.
The results are used as witnesses in formal proofs in {lit}`Puzzle.lean`.
-/

/-!
## Solver

We work with flat arrays for efficient {lit}`#eval` computation.
All array accesses use bounds-unchecked {lit}`getD`/{lit}`setD` for simplicity.
-/

/-- A cell is either filled ({lit}`some v`) or empty ({lit}`none`). -/
abbrev Grid (s : Nat) := Array (Option (Fin s))

private def Grid.at (g : Grid s) (i j : Nat) : Option (Fin s) :=
  g.getD (i * s + j) none

private def Grid.place (g : Grid s) (i j : Nat) (v : Option (Fin s)) : Grid s :=
  g.setIfInBounds (i * s + j) v

/-- Check if value {lit}`v` can be placed at {lit}`(i, j)` without conflict. -/
def canPlace (m n : Nat) (g : Grid (m * n)) (i j : Nat) (v : Fin (m * n)) : Bool :=
  let s := m * n
  -- Row check
  let rowOk := (List.range s).all fun jj =>
    match g.at i jj with
    | some w => jj == j || w != v
    | none => true
  -- Col check
  let colOk := (List.range s).all fun ii =>
    match g.at ii j with
    | some w => ii == i || w != v
    | none => true
  -- Block check (blocks are m rows × n cols)
  let bi := i / m
  let bj := j / n
  let blockOk := (List.range m).all fun di =>
    (List.range n).all fun dj =>
      let ii := bi * m + di
      let jj := bj * n + dj
      match g.at ii jj with
      | some w => (ii == i && jj == j) || w != v
      | none => true
  rowOk && colOk && blockOk

/-- Count of possible values for cell {lit}`(i, j)`. -/
def possibleCount (m n : Nat) (g : Grid (m * n)) (i j : Nat) : Nat :=
  (List.finRange (m * n)).countP fun v => canPlace m n g i j v

/-- Find the first empty cell. -/
def findEmpty (s : Nat) (g : Grid s) : Option (Nat × Nat) :=
  match g.findIdx? (· == none) with
  | some k => if k < s * s then some (k / s, k % s) else none
  | none => none

/-- Solve a puzzle, returning up to {lit}`maxSols` solutions. -/
partial def solvePuzzle (m n : Nat) (g : Grid (m * n)) (maxSols : Nat) :
    List (Grid (m * n)) :=
  match findEmpty (m * n) g with
  | none => [g]
  | some (i, j) =>
    (List.finRange (m * n)).foldl (fun acc v =>
      if acc.length >= maxSols then acc
      else if canPlace m n g i j v then
        acc ++ solvePuzzle m n (g.place i j (some v)) maxSols
      else acc
    ) []

/-- Check if a puzzle is hard: unique solution and no naked singles. -/
def checkHard (m n : Nat) (g : Grid (m * n)) : Bool :=
  let s := m * n
  let sols := solvePuzzle m n g 2
  if sols.length != 1 then false
  else
    (List.range s).all fun i =>
      (List.range s).all fun j =>
        match g.at i j with
        | some _ => true
        | none => possibleCount m n g i j >= 2

/-!
## Concrete 2×3 Hard Puzzle

The following 6×6 puzzle was found by brute-force search (see
{lit}`scripts/find_hard_puzzle.py`). It has a unique solution, but
every empty cell has at least 2 possible values.

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

private abbrev F (k : Nat) (h : k < 6 := by omega) : Option (Fin 6) := some ⟨k, h⟩
private abbrev E : Option (Fin 6) := none

private def puzzle23 : Grid 6 :=
  #[ F 0, E,   F 2, E,   F 4, E,
     E,   E,   F 5, E,   F 1, E,
     E,   F 0, E,   E,   E,   F 4,
     F 2, E,   E,   E,   E,   E,
     E,   E,   E,   E,   E,   F 1,
     F 5, E,   E,   E,   F 2, E ]

#eval checkHard 2 3 puzzle23  -- true

#eval
  let sols := solvePuzzle 2 3 puzzle23 2
  s!"Solutions: {sols.length}"  -- "Solutions: 1"

/-!
The unique solution:
```
0 1 2 | 3 4 5
3 4 5 | 0 1 2
--------------
1 0 3 | 2 5 4
2 5 4 | 1 0 3
--------------
4 2 0 | 5 3 1
5 3 1 | 4 2 0
```
-/
