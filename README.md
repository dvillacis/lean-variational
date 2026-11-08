# VariationalAnalysis

Variational analysis and generalized differentiation for Lean 4 / Mathlib (v4.33.1), following

- B. S. Mordukhovich, *Variational Analysis and Applications*, Springer Monographs in
  Mathematics, 2018 ([doi:10.1007/978-3-319-92775-6](https://doi.org/10.1007/978-3-319-92775-6)),
  cited as [Mordukhovich 2018];
- C. Clason and T. Valkonen, *Introduction to Nonsmooth Analysis and Optimization*,
  [arXiv:2001.00216](https://arxiv.org/abs/2001.00216) (v7), cited as [Clason–Valkonen].

It builds on [`ConvexAnalysis`](https://github.com/dvillacis/lean-convex) (convex analysis,
subgradients and the port of OptLib), pinned in `lakefile.toml`.

## Contents

| Area | File | Contents |
|---|---|---|
| Set-valued maps | `SetValued/OuterLimit` | Painlevé–Kuratowski outer and inner limits (M (1.1), (1.20)); `funNhds φ x₀` for `x →φ x₀`; diagonal arguments; closedness |
| Regular normals | `Normal/Regular` | `regularNormalCone`, `epsNormalCone` (M (1.5), (1.6)); closed convex cone; trivial at interior points; convex sets (M Prop. 1.7, (1.8)); smooth variational description (M Thm. 1.10(i)) |
| Smooth supports | `Analysis/ConvexMajorant`, `Subdifferential/SmoothSupport` | `C¹` convex majorants of vanishing moduli; concave `C¹` supports of regular normals and subgradients (M Thm. 1.10(ii), Thm. 1.27) |
| Limiting normals | `Normal/Limiting` | `normalCone` (M (1.7), CV (18.3)); closed cone; robustness (M Prop. 1.3); convex sets (M Prop. 1.7, (1.9)); trivial at interior points |
| Projections | `Normal/Projection` | Euclidean projector (M (1.3)); `projNormalCone` (M Def. 1.1); M Thm. 1.6: both representations in (1.7); boundary points (M Prop. 1.2), in inner product spaces |
| Transport | `Normal/Transport` | normals pull back along linear isomorphisms; M Thm. 1.6 (`ω`-representation) and Prop. 1.2 in every finite-dimensional normed space |
| Products | `Normal/Product` | normals to products (M Prop. 1.4); locality of normal cones |
| Tangents | `Tangent/Contingent` | `contingentCone` (M Def. 1.8, (1.11)); tangential preduality `N̂ = T*` (M Prop. 1.9) |
| Regular subgradients | `Subdifferential/Regular` | `regularSubdiff`, `epsSubdiff` (M (1.33), (1.34)); Fermat rule; `∂̂f = {f'}` for differentiable `f`; sum rule with a differentiable function (M Prop. 1.30(ii)); indicator functions; epigraphical description (M Thm. 1.26, Prop. 1.17, Ex. 1.62); convex functions (M Prop. 1.25) |
| Basic subgradients | `Subdifferential/Limiting` | `subdiff`, `singularSubdiff` (M Def. 1.18); normals to epigraphs (M Prop. 1.17); limiting representations (M Thm. 1.28, (1.37); (1.38) `⊇`); robustness (M Prop. 1.20); Fermat rule; `C¹` functions (M Cor. 1.24); sum rule with a `C¹` function (M Prop. 1.30(ii)); indicator functions (M Prop. 1.19); convex functions (M Prop. 1.25) |
| Lipschitz functions | `Subdifferential/Lipschitz` | locality of subdifferentials; M Thm. 1.22 ("only if": `∂^∞f = {0}`, `∂f ≠ ∅`, `‖v‖ ≤ L`); Lipschitzian additions (M Prop. 1.29) |
| Comparison with `ConvexAnalysis` | `Subdifferential/Bridge` | `SubderivAt`, OptLib's `f_subdifferential` and `subdifferential` correspond to `subdiff` and `regularSubdiff` under the Riesz map |
| Coderivatives | `Coderivative/Basic` | `coderiv`, `regularCoderiv` (M Def. 1.11, (1.16), (1.17)); smooth mappings (M Prop. 1.12); convex-graph mappings (M Prop. 1.13); extremal property of convex-valued mappings (M Thm. 1.15) |
| Subgradients and coderivatives | `Subdifferential/Coderivative` | `∂f = D*f(1)`, `∂^∞f ⊆ D*f(0)` (M Thm. 1.23); coderivative scalarization (M Thm. 1.32) |
| Distance function | `Subdifferential/Distance`, `Subdifferential/DistanceEuclidean`, `Subdifferential/RightSided` | subgradients of `dist(·; Ω)` at in-set and out-of-set points (M Thm. 1.33, Lemma 1.34); right-sided subdifferential (M Def. 1.36, Prop. 1.37(i)); normals to enlargements (M Thm. 1.38) |
| Set-valued vocabulary | `SetValued/Basic` | domain, inverse, inner semicontinuity, local boundedness; normal, graphical, lower and epigraphical regularity |
| Variational principles | `Principle/Variational`, `Principle/AlmostStationary` | general variational principle, Ekeland's principle, almost stationary points, fixed points (M Thm. 2.12–Prop. 2.15); density of `dom ∂̂φ` (M Ex. 2.25) |
| Extremal principle | `Extremal/Basic` | local extremality, separation, basic and approximate extremal principles (M Def. 2.1–Cor. 2.5) |
| Intersection rule | `Normal/Intersection` | normals to intersections and sums of sets (M Thm. 2.16–Cor. 2.18) |
| Sum rules | `Subdifferential/SumRule`, `Subdifferential/EpigraphClosed`, `Subdifferential/StrictSum` | subdifferential sum rules (M Thm. 2.19–Cor. 2.21); sum rule with a strictly differentiable function and M Thm. 4.5(ii) |
| Smooth changes of variables | `Normal/Diffeomorphism`, `Coderivative/Smooth`, `Subdifferential/SmoothChain` | normals to preimages under `C¹` maps with surjective derivative (M Ex. 1.54); coderivative sum rule (3.24) and full-rank chain rule (M Thm. 3.11(iii)); subdifferential chain rule (M Ex. 1.72) |
| Well-posedness | `WellPosedness/Basic`, `WellPosedness/Coderivative`, `WellPosedness/Criterion`, `WellPosedness/Corollaries` | covering, metric regularity, Lipschitz-like property and their equivalence (M Def. 3.1, Thm. 3.2); coderivative criteria with exact bounds (M Thm. 3.3, Cor. 3.5–3.8) |
| Coderivative calculus | `Coderivative/SumRule`, `Coderivative/ChainRule`, `Coderivative/BinaryOperation`, `Coderivative/Implicit` | sum and chain rules, normals to inverse images, binary operations (M Thm. 3.9–Cor. 3.15); implicit multifunctions ([Mordukhovich 2006, Cor. 4.34]) |
| Parametric variational systems | `Coderivative/Variational`, `Coderivative/SecondOrder`, `Coderivative/CompositeField`, `WellPosedness/Variational`, `WellPosedness/Failure` | coderivatives of PVS, second-order subdifferential (M Prop. 3.16–3.19); metric regularity of PVS and its failure (M Thm. 3.20–3.31) |
| Monotone and prox-regular functions | `WellPosedness/Monotone`, `WellPosedness/Gateaux`, `WellPosedness/ProxRegular`, `WellPosedness/MaximalMonotone` | local, global and maximal monotonicity; Lipschitz-like monotone operators (M Prop. 3.24); amenable and prox-regular functions (M Def. 3.23, 3.27, Lemma 3.28); maximal monotonicity of convex subdifferentials |
| Marginal functions and compositions | `Subdifferential/Marginal`, `Subdifferential/MarginalLipschitz`, `Subdifferential/InfConvolution`, `Subdifferential/ChainRule`, `Subdifferential/ProductRule`, `Subdifferential/MinMax` | M Thm. 4.1–Thm. 4.10 |
| Mean value theorems | `Subdifferential/MeanValue`, `Subdifferential/MeanValueIneq`, `Subdifferential/SymmetricMeanValue`, `Subdifferential/Characterizations`, `Subdifferential/MonotoneConvex` | approximate and symmetric mean value theorems; characterizations of Lipschitz continuity (completing M Thm. 1.22), constancy, strict differentiability, monotonicity and convexity (M Thm. 4.11–4.19) |
| Geometric constraints | `Optimality/GeometricConstraints` | upper and lower subdifferential optimality conditions for `min φ` over `Ω` and over `Ω₁ ∩ ⋯ ∩ Ωₛ`; DC problems (M Thm. 6.1–Prop. 6.4) |
| Nondifferentiable programming | `Optimality/Programming` | Fritz John conditions via normals to epigraphs and graphs, via separate and symmetric subgradients, condensed Lagrangian conditions, abstract maximum principle, upper subdifferential conditions (M Thm. 6.5–Thm. 6.12) |

M = [Mordukhovich 2018], CV = [Clason–Valkonen]. `ROADMAP.md` lists every statement of
[Mordukhovich 2018, Ch. 1–6] with its Lean name or status, and the corresponding results of
[Clason–Valkonen]. All numbered results of Ch. 1, 3 and 4 are formalized, and those of Ch. 2
except Cor. 2.4, the bound `‖x̄ − x₀‖ ≤ λ` in Thm. 2.14, the epi-regular part of Thm. 2.19 and
the countable extremal principles of Sect. 2.2. All numbered theorems, propositions and
corollaries of Sect. 6.1 are formalized. In Ch. 1, the inclusion `⊆` in (1.38) and
Prop. 1.37(ii) remain; the worked examples are not formalized. `ROADMAP.md` also records the
places where a statement of the book had to be corrected (Thm. 2.12, 2.14, 3.14, 3.25, 4.1,
Cor. 4.8, Thm. 4.18).

## Conventions

- **Normals and subgradients are dual elements.** Normals to `Ω ⊆ E` and subgradients of
  `φ : E → EReal` are elements of `StrongDual ℝ E = E →L[ℝ] ℝ`. On products, `(u, v)` is written
  `u.coprod v`. This makes graphs and epigraphs (in `E × F`, `E × ℝ`) work without an inner
  product, and Fréchet derivatives are already dual elements. In a Hilbert space, vectors are
  identified with dual elements through `InnerProductSpace.toDual`, as in `Normal/Projection` and
  `Subdifferential/Bridge`.
- **Setting.** Regular (Fréchet) constructions and the Fermat rules hold in any real normed
  space. Limiting constructions use the norm topology of the dual. This is the limiting normal
  cone of the literature in finite dimensions, where the book works; in infinite dimensions the
  literature uses weak-* limits. Results that need compactness or projections assume
  `[FiniteDimensional ℝ E]`; they are proved in Euclidean space and transported through
  `toEuclidean` (`Normal/Transport`).
- **Limiting normal cone.** `normalCone Ω x₀` is defined as `Lim sup_{x →Ω x₀} N̂(x; Ω)`, the
  first representation of [Mordukhovich 2018, Thm. 1.6] and the definition of
  [Clason–Valkonen, (18.3)]. The projection-based Def. 1.1 of [Mordukhovich 2018] is
  `projNormalCone`, and Thm. 1.6 (`toDual_projNormalCone`) shows the two agree for locally closed
  sets in finite dimensions.
- **Extended-real functions.** Functions are `E → EReal`. A subdifferential at `x₀` is empty
  unless `φ x₀` is finite. The epigraph is `Function.Epi φ univ` and the indicator function is
  `Set.convex_indicator` (both from `ConvexAnalysis`). The `lim inf`/`lim sup` conditions of the
  book are unfolded into "for every `ε > 0`, eventually …" form.
- Cones are empty at points outside the set, following [Rockafellar–Wets 1998].

## Build

```
lake exe cache get && lake build
```

## Status

All 58 files compile against Mathlib v4.33.1 with no `sorry`.
`lake env lean scripts/AuditAxioms.lean` checks that no declaration depends on an axiom beyond
`propext`, `Classical.choice`, `Quot.sound` (1107 declarations checked).
