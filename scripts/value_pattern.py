"""Check if hard puzzles have patterns in which values appear as givens."""

from find_hard_puzzle import solve, possible_values, is_hard
from random import shuffle, seed
from collections import Counter
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

    print(f"=== Value distribution in givens for {m}x{n} ===\n")

    for idx, board in enumerate(boards[:10]):
        best, best_empty = find_minimal_hard(board, m, n, num_trials=500)
        if not best:
            continue

        given_values = Counter()
        for i in range(s):
            for j in range(s):
                if best[i][j] is not None:
                    given_values[best[i][j]] += 1

        print(f"Board {idx+1}: givens by value: {dict(sorted(given_values.items()))}")

        # Check: do empty cells form pairs/triples with same possibilities?
        poss_groups = {}
        for i in range(s):
            for j in range(s):
                if best[i][j] is None:
                    poss = frozenset(possible_values(best, m, n, i, j))
                    if poss not in poss_groups:
                        poss_groups[poss] = []
                    poss_groups[poss].append((i, j))

        print(f"  Empty cells grouped by possible values:")
        for poss, cells in sorted(poss_groups.items(), key=lambda x: (len(x[0]), x[0])):
            print(f"    {set(poss)}: {cells}")
        print()


if __name__ == "__main__":
    main()
