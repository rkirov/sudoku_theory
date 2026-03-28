"""Analyze structure of hard puzzles to find generalizable constructions.

Focus on minimal hard puzzles (fewest empty cells) since those
reveal the essential structure needed.
"""

from find_hard_puzzle import solve, can_place, possible_values, is_hard, print_board
from collections import defaultdict
from random import shuffle, seed
import sys


def find_minimal_hard(board, m, n, num_trials=200):
    """Find hard puzzles with minimum empty cells."""
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


def find_hard_with_few_empty(board, m, n, target_empty):
    """Try to find hard puzzles with exactly target_empty empty cells."""
    s = m * n
    cells = [(i, j) for i in range(s) for j in range(s)]
    results = []

    from itertools import combinations
    for to_remove in combinations(cells, target_empty):
        puzzle = [row[:] for row in board]
        for i, j in to_remove:
            puzzle[i][j] = None

        # Quick check: any empty cell with 0 or 1 possible?
        has_single = False
        for i, j in to_remove:
            poss = possible_values(puzzle, m, n, i, j)
            if len(poss) <= 1:
                has_single = True
                break
        if has_single:
            continue

        # Check uniqueness
        sols = []
        solve([row[:] for row in puzzle], m, n, sols, max_solutions=2)
        if len(sols) == 1:
            results.append(puzzle)

    return results


def main():
    m, n = int(sys.argv[1]), int(sys.argv[2])
    s = m * n
    print(f"=== Analyzing hard puzzle structure: {m}x{n} ({s}x{s} board) ===\n")

    # Use first few valid boards
    empty = [[None]*s for _ in range(s)]
    boards = []
    solve(empty, m, n, boards, max_solutions=20)

    # Find minimum empty cells needed
    print("Finding minimal hard puzzles...\n")
    for idx, board in enumerate(boards[:10]):
        print(f"Board {idx+1}:")
        print_board(board, m, n)

        best, best_empty = find_minimal_hard(board, m, n, num_trials=500)
        if best:
            print(f"\nMinimal hard puzzle ({best_empty} empty cells):")
            print_board(best, m, n)
            for i in range(s):
                for j in range(s):
                    if best[i][j] is None:
                        poss = possible_values(best, m, n, i, j)
                        bi, bj = i // m, j // n
                        print(f"  ({i},{j}) block=({bi},{bj}) possible={poss} answer={board[i][j]}")
        else:
            print("  No hard puzzle found")
        print()

    # Try to find hard puzzles with exactly 2 empty cells
    print(f"\n=== Exhaustive search for hard puzzles with 2 empty cells ===")
    for idx, board in enumerate(boards[:5]):
        results = find_hard_with_few_empty(board, m, n, 2)
        if results:
            print(f"\nBoard {idx+1}: {len(results)} hard puzzles with 2 empty cells")
            for puzzle in results[:3]:
                print()
                print_board(puzzle, m, n)
                for i in range(s):
                    for j in range(s):
                        if puzzle[i][j] is None:
                            poss = possible_values(puzzle, m, n, i, j)
                            print(f"  ({i},{j}) possible={poss} answer={board[i][j]}")
        else:
            print(f"Board {idx+1}: no hard puzzles with 2 empty cells")

    # Try 3 empty cells if 2 didn't work
    print(f"\n=== Exhaustive search for hard puzzles with 3 empty cells ===")
    for idx, board in enumerate(boards[:3]):
        results = find_hard_with_few_empty(board, m, n, 3)
        if results:
            print(f"\nBoard {idx+1}: {len(results)} hard puzzles with 3 empty cells")
            for puzzle in results[:5]:
                print()
                print_board(puzzle, m, n)
                for i in range(s):
                    for j in range(s):
                        if puzzle[i][j] is None:
                            poss = possible_values(puzzle, m, n, i, j)
                            bi, bj = i // m, j // n
                            print(f"  ({i},{j}) block=({bi},{bj}) possible={poss} answer={board[i][j]}")
        else:
            print(f"Board {idx+1}: no hard puzzles with 3 empty cells")


if __name__ == "__main__":
    main()
