"""Analyze the pattern of given cells in minimal hard puzzles."""

from find_hard_puzzle import solve, possible_values, is_hard
from random import shuffle, seed
import sys


def find_minimal_hard(board, m, n, num_trials=500):
    s = m * n
    cells = [(i, j) for i in range(s) for j in range(s)]
    best = None
    best_empty = s * s + 1
    for trial in range(num_trials):
        seed(trial)
        order = cells[:]
        shuffle(order)
        puzzle = [row[:] for row in board]
        for i, j in order:
            old = puzzle[i][j]
            puzzle[i][j] = None
            sols = []
            solve([row[:] for row in puzzle], m, n, sols, max_solutions=2)
            if len(sols) != 1:
                puzzle[i][j] = old
        if is_hard(puzzle, m, n):
            empty_count = sum(1 for i in range(s) for j in range(s) if puzzle[i][j] is None)
            if 0 < empty_count < best_empty:
                best_empty = empty_count
                best = [row[:] for row in puzzle]
    return best, best_empty


def main():
    m, n = int(sys.argv[1]), int(sys.argv[2])
    s = m * n
    empty = [[None]*s for _ in range(s)]
    boards = []
    solve(empty, m, n, boards, max_solutions=20)

    print(f"=== Given cell patterns for {m}x{n} ({s}x{s}) ===\n")

    for idx, board in enumerate(boards[:10]):
        best, best_empty = find_minimal_hard(board, m, n, num_trials=500)
        if not best:
            continue

        given_count = s * s - best_empty
        print(f"Board {idx+1}: {given_count} givens, {best_empty} empty")

        # Givens per row
        row_counts = [sum(1 for j in range(s) if best[i][j] is not None) for i in range(s)]
        # Givens per col
        col_counts = [sum(1 for i in range(s) if best[i][j] is not None) for j in range(s)]
        # Givens per block
        block_counts = {}
        for bi in range(s // m):
            for bj in range(s // n):
                c = sum(1 for di in range(m) for dj in range(n) if best[bi*m+di][bj*n+dj] is not None)
                block_counts[(bi, bj)] = c

        print(f"  Givens per row: {row_counts}")
        print(f"  Givens per col: {col_counts}")
        print(f"  Givens per block: {dict(block_counts)}")

        # Show given pattern as grid of G/.
        for i in range(s):
            row = ""
            for j in range(s):
                if j > 0 and j % n == 0:
                    row += "| "
                row += ("G " if best[i][j] is not None else ". ")
            print(f"  {row}")
        print()


if __name__ == "__main__":
    main()
