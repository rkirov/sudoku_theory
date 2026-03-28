"""Find a hard puzzle: well-posed (unique solution) but no naked singles."""

from itertools import product
import sys

def is_valid_board(board, m, n):
    s = m * n
    # Check rows
    for i in range(s):
        if len(set(board[i])) != s:
            return False
    # Check cols
    for j in range(s):
        if len(set(board[i][j] for i in range(s))) != s:
            return False
    # Check blocks
    for bi in range(n):
        for bj in range(m):
            vals = []
            for di in range(m):
                for dj in range(n):
                    vals.append(board[bi*m+di][bj*n+dj])
            if len(set(vals)) != s:
                return False
    return True

def solve(puzzle, m, n, solutions, max_solutions=2):
    """Find all solutions (up to max_solutions)."""
    s = m * n
    # Find first empty cell
    for i in range(s):
        for j in range(s):
            if puzzle[i][j] is None:
                # Try each value
                for v in range(s):
                    if can_place(puzzle, m, n, i, j, v):
                        puzzle[i][j] = v
                        solve(puzzle, m, n, solutions, max_solutions)
                        puzzle[i][j] = None
                        if len(solutions) >= max_solutions:
                            return
                return
    # No empty cell - found a solution
    solutions.append([row[:] for row in puzzle])

def can_place(puzzle, m, n, i, j, v):
    s = m * n
    # Row
    for jj in range(s):
        if puzzle[i][jj] == v:
            return False
    # Col
    for ii in range(s):
        if puzzle[ii][j] == v:
            return False
    # Block
    bi, bj = i // m, j // n
    for di in range(m):
        for dj in range(n):
            if puzzle[bi*m+di][bj*n+dj] == v:
                return False
    return True

def possible_values(puzzle, m, n, i, j):
    s = m * n
    return {v for v in range(s) if can_place(puzzle, m, n, i, j, v)}

def is_hard(puzzle, m, n):
    """No empty cell has exactly one possible value."""
    s = m * n
    for i in range(s):
        for j in range(s):
            if puzzle[i][j] is None:
                poss = possible_values(puzzle, m, n, i, j)
                if len(poss) <= 1:
                    return False
    return True

def has_empty(puzzle, m, n):
    s = m * n
    return any(puzzle[i][j] is None for i in range(s) for j in range(s))

def find_hard_puzzle(m, n):
    """Generate all valid boards, then try removing cells."""
    s = m * n

    # Start from a valid board and try removing cells
    # First, generate a valid board by solving empty grid
    empty = [[None]*s for _ in range(s)]
    solutions = []
    solve(empty, m, n, solutions, max_solutions=1)
    if not solutions:
        print(f"No valid {s}x{s} board exists")
        return

    board = solutions[0]
    print(f"Starting from valid board:")
    print_board(board, m, n)

    # Try all subsets of cells to remove (start small)
    cells = [(i,j) for i in range(s) for j in range(s)]

    # Try removing cells greedily, checking hardness
    from random import shuffle, seed

    for trial in range(1000):
        seed(trial)
        order = cells[:]
        shuffle(order)

        puzzle = [row[:] for row in board]
        for i, j in order:
            puzzle[i][j] = None
            # Check still unique
            sols = []
            solve([row[:] for row in puzzle], m, n, sols, max_solutions=2)
            if len(sols) != 1:
                puzzle[i][j] = board[i][j]  # put back

        if has_empty(puzzle, m, n) and is_hard(puzzle, m, n):
            # Check unique
            sols = []
            solve([row[:] for row in puzzle], m, n, sols, max_solutions=2)
            if len(sols) == 1:
                empty_count = sum(1 for i in range(s) for j in range(s) if puzzle[i][j] is None)
                print(f"\nFound hard puzzle (trial {trial}, {empty_count} empty cells):")
                print_board(puzzle, m, n)
                print("\nPossible values per empty cell:")
                for i in range(s):
                    for j in range(s):
                        if puzzle[i][j] is None:
                            poss = possible_values(puzzle, m, n, i, j)
                            print(f"  ({i},{j}): {poss}")
                return puzzle

    print("No hard puzzle found in 1000 trials")
    return None

def print_board(board, m, n):
    s = m * n
    for i in range(s):
        if i > 0 and i % m == 0:
            print("-" * (s * 2 + n - 1))
        row = ""
        for j in range(s):
            if j > 0 and j % n == 0:
                row += "| "
            cell = board[i][j]
            row += (str(cell) if cell is not None else ".") + " "
        print(row)

if __name__ == "__main__":
    m, n = int(sys.argv[1]), int(sys.argv[2])
    print(f"Searching for hard {m}x{n} puzzle ({m*n}x{m*n} board)...")
    find_hard_puzzle(m, n)
