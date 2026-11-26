# Orbital flow roots are dense

In 2008, Peter Cameron asked whether every open interval in $[0,1]$ contains a real orbital flow root. The answer is yes. We also prove that every open disk in the complex plane contains an orbital flow root. In both theorems, the graphs are finite, simple and connected, and the specified symmetry group always has order two. [Cameron’s Problem 72(2)](https://cameroncounts.github.io/web/QM/oldprob.html) · [Written proof](notes/orbital-flow-roots.md)

| Result | Lean theorem |
| --- | --- |
| A real root strictly between any $0\leq a<b\leq 1$ | [`root_in_every_interval`](Conjectures/OrbitalFlowTheorem.lean#L108) |
| A complex root arbitrarily close to any point of the plane | [`dense_fixed_swap_roots`](Conjectures/OrbitalFlowPlaneTheorem.lean#L72) |

## How the symmetry produces a root

Suppose a graph admits $F(q)$ nowhere-zero flows over a finite abelian group of order $q$. Glue two copies of the graph at a single vertex and let the symmetry exchange them. A flow on the joined graph is a pair of flows. Counting pairs up to exchange gives the orbital polynomial $F(q)(F(q)+1)/2$. Wherever $F(x)=-1$, the orbital polynomial vanishes. [Counting flows up to symmetry](notes/orbital-flow-roots.md#one-symmetry-and-one-extra-factor)

For the real theorem we construct graphs with $F(x)=(x-1)^m(x-2)^k$. Choosing the exponents puts a solution of $F(x)=-1$ in any prescribed interval. For example, $m=1$ and $k=2$ give a root strictly between $0.534$ and $0.535$. The complex theorem uses two further graph families. Lean checks the density statements and the connection to actual flow-orbit counts. The written argument also shows how to draw the graphs in the plane. [Real and complex constructions](notes/orbital-flow-roots.md)

## Reproduce the verification

With Elan installed, run the following commands from the repository root. The project pins Lean and mathlib to version 4.19.0.

```sh
sed -n 's/^import \(Mathlib[.].*\)$/\1/p' Conjectures/*.lean | sort -u | xargs lake exe cache get
lake build
lake env lean Audit.lean
python3 scripts/verify_orbital_flow_roots.py
```

The audit prints the axioms used by both density theorems. The independent Python check enumerates small flows and verifies the displayed root bracket using rational arithmetic. The full Lean proofs and the written argument were extracted from the [original proof collection](https://github.com/mnabid05/lean-conjecture-studies/tree/30abad7889c4c8f144f2f01318d581ef3bbfaa64).
