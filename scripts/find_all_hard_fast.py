"""Fast search for hard puzzles using greedy removal + symmetry."""

from find_hard_puzzle import solve, can_place, possible_values, is_hard, print_board
from collections import defaultdict
from random import shuffle, seed, sample
import sys


def find_hard_from_board(board, m, n, num_trials=500):
    """Find hard puzzles by greedy random removal from a board."""
    s = m * n
    cells = [(i, j) for i in range(s) for j in range(s)]
    results = set()

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
                puzzle[i][j] = old  # put back

        if is_hard(puzzle, m, n):
            empty_count = sum(1 for i in range(s) for j in range(s) if puzzle[i][j] is None)
            if empty_count > 0:
                key = tuple(tuple(row) for row in puzzle)
                results.add(key)

    return results


def board_to_str(board, m, n):
    s = m * n
    lines = []
    for i in range(s):
        row = ""
        for j in range(s):
            v = board[i][j]
            row += ("." if v is None else str(v))
        lines.append(row)
    return "\n".join(lines)


def analyze_empty_pattern(puzzle, board, m, n):
    """Return info about the empty cell pattern."""
    s = m * n
    empty = []
    for i in range(s):
        for j in range(s):
            if puzzle[i][j] is None:
                poss = possible_values(puzzle, m, n, i, j)
                empty.append({
                    "pos": (i, j),
                    "block": (i // m, j // n),
                    "possible": poss,
                    "answer": board[i][j],
                    "num_possible": len(poss)
                })
    return empty


def main():
    m, n = int(sys.argv[1]), int(sys.argv[2])
    s = m * n
    print(f"=== Searching for hard puzzles: {m}x{n} ({s}x{s} board) ===\n")

    # Generate all valid boards
    empty = [[None]*s for _ in range(s)]
    boards = []
    solve(empty, m, n, boards, max_solutions=10000)
    print(f"Valid completed boards: {len(boards)}\n")

    all_hard = {}
    for idx, board in enumerate(boards):
        results = find_hard_from_board(board, m, n, num_trials=200)
        for key in results:
            if key not in all_hard:
                all_hard[key] = board
        if results:
            print(f"Board {idx+1}: found {len(results)} hard puzzles")

    print(f"\n=== RESULTS ===")
    print(f"Total unique hard puzzles: {len(all_hard)}\n")

    if not all_hard:
        print("No hard puzzles exist!")
        return

    # Analyze patterns
    by_empty_count = defaultdict(list)
    for key, board in all_hard.items():
        puzzle = [list(row) for row in key]
        empty_count = sum(1 for row in puzzle for v in row if v is None)
        by_empty_count[empty_count].append((puzzle, board))

    for count in sorted(by_empty_count.keys()):
        puzzles = by_empty_count[count]
        print(f"--- {count} empty cells: {len(puzzles)} puzzles ---")

        for puzzle, board in puzzles[:3]:
            print()
            print_board(puzzle, m, n)
            analysis = analyze_empty_pattern(puzzle, board, m, n)
            # Show which blocks have empty cells
            blocks_with_empty = set(e["block"] for e in analysis)
            print(f"  Empty cells in blocks: {blocks_with_empty}")
            for e in analysis:
                print(f"  ({e['pos'][0]},{e['pos'][1]}): "
                      f"block={e['block']}, possible={e['possible']}, "
                      f"answer={e['answer']}")
            # Show possibility distribution
            poss_counts = [e["num_possible"] for e in analysis]
            print(f"  Possibility distribution: {sorted(poss_counts)}")
        print()


if __name__ == "__main__":
    main()
