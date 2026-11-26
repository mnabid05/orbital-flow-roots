"""Check the orbital flow examples by exhaustive enumeration on small multigraphs."""

from fractions import Fraction
from itertools import product
from math import prod


def flows(vertex_count, edges, moduli):
    """Enumerate nonzero currents balanced at each vertex, coordinate by coordinate."""
    elements = product(*(range(n) for n in moduli))
    nonzero = [element for element in elements if any(element)]
    for currents in product(nonzero, repeat=len(edges)):
        balances = [[0] * len(moduli) for _ in range(vertex_count)]
        for (tail, head), current in zip(edges, currents):
            for i, value in enumerate(current):
                balances[tail][i] -= value
                balances[head][i] += value
        if all(value % modulus == 0 for row in balances for value, modulus in zip(row, moduli)):
            yield currents


def doubled_stages(loops, stages):
    edges = [(0, 0)] * loops + [(stages, 0)]
    for j in range(stages):
        edges.extend([(j, j + 1)] * 2)
    return stages + 1, edges


def ladder(rungs):
    start, end = 0, 1
    edges = [(end, start)]
    for rail in range(2):
        path = [start] + [2 + 2 * j + rail for j in range(rungs)] + [end]
        edges.extend(zip(path, path[1:]))
    edges.extend((2 + 2 * j, 3 + 2 * j) for j in range(rungs))
    return 2 + 2 * rungs, edges


def bundle_cycle(stages, width):
    edges = [(j, (j + 1) % stages) for j in range(stages) for _ in range(width)]
    return stages, edges


def bundle_count(q, stages, width):
    sign = (-1) ** width
    zero_total = Fraction((q - 1) ** width + (q - 1) * sign, q)
    nonzero_total = Fraction((q - 1) ** width - sign, q)
    return zero_total**stages + (q - 1) * nonzero_total**stages


def check_count(graph, moduli, expected, case):
    observed = sum(1 for _ in flows(*graph, moduli))
    if observed != expected:
        raise AssertionError(f"{case}, group {moduli}: counted {observed}, expected {expected}")


def check_swap(graph, moduli):
    """Identify the two vertex-zero roots, then exchange matching edge indices."""
    vertices, edges = graph
    second = [0] + list(range(vertices, 2 * vertices - 1))
    joined_edges = edges + [(second[u], second[v]) for u, v in edges]
    all_flows = set(flows(2 * vertices - 1, joined_edges, moduli))
    representatives = set()
    cut = len(edges)
    for current in all_flows:
        swapped = current[cut:] + current[:cut]
        if swapped not in all_flows:
            raise AssertionError(f"swap failed to preserve a flow over {moduli}")
        representatives.add(min(current, swapped))
    n = sum(1 for _ in flows(*graph, moduli))
    if len(all_flows) != n * n or len(representatives) != n * (n + 1) // 2:
        raise AssertionError(f"incorrect copy or orbit count over {moduli}, base count {n}")


def main():
    for moduli in [(2,), (3,), (4,), (2, 2)]:
        q = prod(moduli)
        for loops, stages in product(range(2), range(3)):
            check_count(doubled_stages(loops, stages), moduli,
                        (q - 1) ** (loops + 1) * (q - 2) ** stages, ("stages", loops, stages))
        for rungs in range(3):
            check_count(ladder(rungs), moduli,
                        (q - 1) * (q - 2) * (q - 3) ** rungs, ("ladder", rungs))
        for stages, width in product(range(1, 4), range(4)):
            check_count(bundle_cycle(stages, width), moduli,
                        bundle_count(q, stages, width), ("bundle cycle", stages, width))
        check_swap(doubled_stages(0, 0), moduli)
        check_swap(ladder(0), moduli)

    left, right = Fraction(534, 1000), Fraction(535, 1000)

    def shifted_flow(x):
        return (x - 1) * (x - 2) ** 2 + 1

    if not shifted_flow(left) < 0 < shifted_flow(right):
        raise AssertionError("the rational endpoints do not bracket the root")
    print("Verified 84 flow counts, 8 copy swaps, and the exact root bracket (0.534, 0.535).")


if __name__ == "__main__":
    main()
