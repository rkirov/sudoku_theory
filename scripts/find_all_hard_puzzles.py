"""Find ALL hard puzzles for small boards and analyze patterns."""

from itertools import product
from find_hard_puzzle import (
    is_valid_board, solve, can_place, possible_values, is_hard, print_board
)
import sys
from collections import defaultdict


def generate_all_valid_boards(m, n):
    """Generate all valid completed boards by solving empty grid."""
    s = m * n
    empty = [[None]*s for _ in range(s)]
    solutions = []
    solve(empty, m, n, solutions, max_solutions=10000)
    return solutions


def find_all_hard_puzzles_from_board(board, m, n, min_empty=1):
    """Find all maximal hard puzzles from a given board.

    Strategy: start from full board, greedily remove cells in all possible
    orders, keeping only those that remain hard and well-posed.
    We use BFS over removal sets.
    """
    s = m * n
    cells = [(i, j) for i in range(s) for j in range(s)]
    hard_puzzles = []

    # BFS: start from puzzles with few removals
    from collections import deque

    # Try all single removals first, then pairs, etc.
    # But this is exponential. Let's be smarter:
    # enumerate subsets of cells to remove, check hardness + uniqueness

    # For small boards, enumerate all subsets up to a reasonable size
    from itertools import combinations

    max_removals = s * s  # try all
    seen = set()

    for num_remove in range(min_empty, min(max_removals + 1, s * s)):
        found_any = False
        for to_remove in combinations(cells, num_remove):
            puzzle = [row[:] for row in board]
            for i, j in to_remove:
                puzzle[i][j] = None

            # Check uniqueness
            sols = []
            solve([row[:] for row in puzzle], m, n, sols, max_solutions=2)
            if len(sols) != 1:
                continue

            # Check hardness
            if is_hard(puzzle, m, n):
                # Convert to hashable form
                key = tuple(tuple(row) for row in puzzle)
                if key not in seen:
                    seen.add(key)
                    hard_puzzles.append((puzzle, num_remove))
                    found_any = True

        if found_any:
            print(f"  Found {len([p for p, k in hard_puzzles if k == num_remove])} "
                  f"hard puzzles with {num_remove} empty cells")

    return hard_puzzles


def analyze_puzzle(puzzle, board, m, n):
    """Analyze the structure of a hard puzzle."""
    s = m * n
    empty_cells = []
    for i in range(s):
        for j in range(s):
            if puzzle[i][j] is None:
                poss = possible_values(puzzle, m, n, i, j)
                empty_cells.append(((i, j), poss, board[i][j]))

    return empty_cells


def main():
    m, n = int(sys.argv[1]), int(sys.argv[2])
    s = m * n
    print(f"=== Finding all hard puzzles for {m}x{n} ({s}x{s} board) ===\n")

    boards = generate_all_valid_boards(m, n)
    print(f"Found {len(boards)} valid completed boards\n")

    all_hard = []
    for idx, board in enumerate(boards):
        print(f"Board {idx + 1}/{len(boards)}:")
        print_board(board, m, n)
        hard = find_all_hard_puzzles_from_board(board, m, n)
        if hard:
            all_hard.extend([(board, puzzle, num_remove) for puzzle, num_remove in hard])
        print()

    print(f"\n=== SUMMARY ===")
    print(f"Total hard puzzles found: {len(all_hard)}")

    if all_hard:
        # Group by number of empty cells
        by_empty = defaultdict(list)
        for board, puzzle, num_remove in all_hard:
            by_empty[num_remove].append((board, puzzle))

        for k in sorted(by_empty.keys()):
            print(f"\n--- {k} empty cells: {len(by_empty[k])} puzzles ---")
            for board, puzzle in by_empty[k][:5]:  # show first 5
                print()
                print_board(puzzle, m, n)
                analysis = analyze_puzzle(puzzle, board, m, n)
                for (i, j), poss, actual in analysis:
                    print(f"  ({i},{j}): possible={poss}, answer={actual}")


if __name__ == "__main__":
    main()
