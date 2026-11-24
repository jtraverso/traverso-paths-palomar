# Supporting lines on a Newton slope path

This Lean project formalizes a path argument extracted from the proof of Lau–Nicole–Vasiu, Proposition 5.12. The vertices are the ordered Newton slopes. Each vertex carries its reference interval and the extreme contacts of a supporting line of the coefficient valuations. The local argument propagates an interval bound to the right. A crossing into a line above the reference, or the last endpoint of the Newton polygon, rules out any line that remains below the reference.

`Challenge.lean` contains the three statements selected for Comparator. `Solution.lean` constructs the contact intervals, proves the propagation and lattice inclusion, and applies the estimate in `TraversoSlopeGraph.lean` to obtain the exponent `floor(2cd/(c+d))`. The cyclic-coordinate model explicitly supplies integral-coordinate membership and the short-interval no-cancellation criterion of Lemma 5.16. The final statement bounds transported endomorphism blocks in that model. Constructing the model for Dieudonné modules and identifying an isomorphism number for a group are separate algebraic inputs. [Lau–Nicole–Vasiu, §§5.3 and 8.1](https://arxiv.org/html/0912.0506)

## Transfer to the double-hexagon certificate

`DoubleHexagonTransfer.lean` examines the double hexagon from Paper II on typed triangle absorption. A state records an integer edge vector. Adding or subtracting a physical triangle is one step, and a coefficient of magnitude `k` costs `k` steps. Give the 12 rim edges weight `2`, the three central edges weight `−1`, and every other edge weight `0`. The target has potential `24`. A legal signed triangle step changes the potential by at most `3` in absolute value. A step touching a vertex outside the nine roots changes it by at most `2`, because it has at most one root edge.

With signed weight `W` and auxiliary weight `A`, summing along the path gives `24 + A ≤ 3W`. The certified input from Paper II takes the six ear triangles with coefficient `+1` and the central triangle with coefficient `−2`. Its weight is `8`, so the bound is attained. Equality forces `A = 0` for any weight-eight certificate. This applies to every physical extension inducing the same graph on the nine roots. The proof certifies signed weight, which is the input cost in the absorber construction of Paper II. [Pinned source certificate](https://github.com/jtraverso/typed-triangle-absorption/blob/673c6d4118b5679783bafa7606fd2c611161a254/PartitionedTriangleAbsorption/SignedCertificate/DoubleHexagon.lean)

## Reproduce

Run the commands below in the pinned Lean toolchain. Standard Comparator uses Bubblewrap on Linux.

```sh
lake exe cache get
lake build
lake comparator
```

The repository includes the pinned Lake manifest and `formalization.yaml`. The double-hexagon transfer is built as a separate module and the three selected comparison declarations concern the Newton slope path and cyclic-coordinate model. [Palomar submission requirements](https://palomar-registry.org/how-to-submit)

Local preflight on Lean 4.35.0-rc3 built all three targets. Comparator ran on the local Windows sources with its Linux sandbox disabled and accepted the three statements. A separate NanoDa replay of the solution export checked 7,639 declarations with no typechecker errors. NanoDa reported one pretty-printer diagnostic while displaying axioms. The metadata passed the public `formalization.yaml` JSON schema.
