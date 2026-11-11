# VariationalAnalysis

Variational analysis and generalized differentiation for Lean 4 / Mathlib (v4.33.1), following

- B. S. Mordukhovich, *Variational Analysis and Applications*, Springer Monographs in
  Mathematics, 2018 ([doi:10.1007/978-3-319-92775-6](https://doi.org/10.1007/978-3-319-92775-6)),
  cited as [Mordukhovich 2018];
- C. Clason and T. Valkonen, *Introduction to Nonsmooth Analysis and Optimization*,
  [arXiv:2001.00216](https://arxiv.org/abs/2001.00216) (v7), cited as [Clason–Valkonen].

The generalized gradient follows Ch. 7 of B. S. Mordukhovich and N. M. Nam, *Convex Analysis and
Beyond, Vol. I: Basic Theory*, Springer, 2022, cited as [Mordukhovich–Nam 2022].
Second-order subdifferentials, prox-regularity, Moreau envelopes and subgradient graphical
derivatives follow Ch. 1 of B. S. Mordukhovich, *Second-Order Variational Analysis in
Optimization, Variational Stability, and Control*, Springer, 2024, cited as [Mordukhovich 2024];
Motzkin's theorem of the alternative follows its Lemma 3.1.

The theory of SCD (subspace containing derivative) mappings follows H. Gfrerer and J. V. Outrata,
*On (local) analysis of multifunctions via subspaces contained in graphs of generalized
derivatives*, J. Math. Anal. Appl., 2022 ([arXiv:2106.00519](https://arxiv.org/abs/2106.00519)),
cited as [Gfrerer–Outrata 2022], together with the product rule of H. Gfrerer, M. Mandlmayr,
J. V. Outrata and J. Valdman, *On the SCD semismooth\* Newton method for generalized equations
with application to a class of static contact problems with Coulomb friction*, Comput. Optim.
Appl. 86 (2023), 1159–1191 ([doi:10.1007/s10589-022-00429-0](https://doi.org/10.1007/s10589-022-00429-0)),
cited as [Gfrerer–Mandlmayr–Outrata–Valdman 2023], and Sect. 2.5 of H. Gfrerer and J. V. Outrata,
*On the role of semismoothness in nonsmooth numerical analysis: Theory*
([arXiv:2405.14637](https://arxiv.org/abs/2405.14637)), cited as [Gfrerer–Outrata 2024].

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
| Clarke generalized gradient | `Subdifferential/Clarke` | generalized directional derivative and generalized gradient ([Mordukhovich–Nam 2022, Def. 7.1, 7.21]); `∂f ⊆ ∂̄f`, `∂̄f = co ∂f` in finite dimensions (Thm. 7.69, M (1.83), CV Thm. 16.10); full duality, compactness, symmetry, Fermat's rule, smooth and convex cases, sum and scalar rules, composition with the projection `E × F → E` |
| SCD mappings | `SCD/Grassmannian`, `SCD/Adjoint`, `SCD/Basic`, `SCD/SingleValued`, `SCD/Calculus`, `SCD/GraphLipschitz`, `SCD/Derivable`, `SCD/Product`, `SCD/Monotone`, `SCD/Minty`, `SCD/LocalMonotone` | metric and compactness of the space of subspaces, adjoint subspaces; graphical smoothness, SC derivatives `𝒮F`, `𝒮*F`, SCD property ([Gfrerer–Outrata 2022, Sect. 3]); Lipschitz maps via Rademacher, `C¹` changes of variables, `F + h`, graphically Lipschitzian and (hypo)monotone maps, Minty's theorem, convex subdifferentials; product rule ([Gfrerer–Mandlmayr–Outrata–Valdman 2023, Prop. 3.5]) |
| SCD regularity and Newton's method | `SCD/Regularity`, `SCD/Semismooth`, `SCD/SemismoothPrimal`, `SCD/Subregularity`, `SCD/SemismoothSubregularity` | SCD regularity and `scdreg`; SCD semismooth\* maps and local superlinear convergence of the SCD semismooth\* Newton method; strong metric subregularity via `T♯` ([Gfrerer–Outrata 2022, Sect. 4–6], [Gfrerer–Outrata 2024, Sect. 2.5]) |
| Second-order subdifferentials | `SecondOrder/Basic` | combined and partial second-order subdifferentials (M24 Def. 1.46, 1.52); `C²` and `C^{1,1}` functions, sum rules (M24 Prop. 1.47–1.54); regular coderivative sum rule |
| Prox-regularity | `SecondOrder/ProxRegular` | proximal subgradients, `φ`-attentive localizations, hypomonotonicity; prox-regularity via hypomonotone localizations (M24 Thm. 1.65) |
| Moreau envelopes | `SecondOrder/Moreau` | Moreau envelopes and proximal mappings (M24 Def. 1.66–1.67, Lemma 1.68–1.69); single-valued Lipschitz proximal mappings and `C^{1,1}` envelopes of prox-regular functions (M24 Thm. 1.70–1.71); `∂φ` graphically Lipschitzian and SCD (M24 Cor. 1.72, [Gfrerer–Outrata 2022, Prop. 3.26]) |
| Subgradient graphical derivatives | `SecondOrder/GraphicalDerivative` | graphical derivative and its sum rule; subgradient graphical derivatives (M24 Def. 1.73), `C²` case and sum rules (M24 Prop. 1.74, 1.76); local convexification of `C^{1,1}` functions (M24 Lemma 1.82) |
| Epi-convergence | `SecondOrder/EpiConvergence` | set convergence, epi-convergence and epi-differentiability (M24 Def. 1.78–1.80); proximal normals and their approximation under set convergence (M24 Lemma 1.81); proto-differentiability (M24 Def. 1.85) |
| `C^{1,1}` functions | `SecondOrder/C11` | directional differentiability (M24 Def. 1.77); `∂²_D φ(x̄)(u) ⊆ ∂²φ(x̄)(u)` for `C^{1,1}` functions with directionally differentiable gradient (M24 Thm. 1.84) |
| Proto-differentiability | `SecondOrder/ProtoDiff` | graphical derivatives and coderivatives under shears (M24 (1.118)); derivable Lipschitz graphs are directionally differentiable; `∂²_D φ ⊆ ∂²φ` for continuously prox-regular functions with proto-differentiable `∂φ` (M24 Thm. 1.86) |
| Second subderivatives | `SecondOrder/SecondSubderiv` | subderivatives (M24 Def. 1.43); second subderivatives, twice epi- and semidifferentiability (M24 Def. 1.88–1.89); twice differentiable and convex functions (M24 Prop. 1.90, 1.93); quotients under subdifferentiation and Moreau envelopes (M24 Lemma 1.94); semiderivatives of set-valued mappings (M24 Def. 1.100) |
| Cyclic monotonicity | `SecondOrder/CyclicMonotone` | resolvents of monotone operators (M24 Lemma 1.95); cyclically monotone mappings and Rockafellar's theorem, with uniqueness up to a constant (M24 Def. 1.96, Lemma 1.97) |
| Theorems of the alternative | `Analysis/Motzkin` | Motzkin's theorem of the alternative in finite dimensions ([Mordukhovich 2024, Lemma 3.1]) |
| Geometric constraints | `Optimality/GeometricConstraints` | upper and lower subdifferential optimality conditions for `min φ` over `Ω` and over `Ω₁ ∩ ⋯ ∩ Ωₛ`; DC problems (M Thm. 6.1–Prop. 6.4) |
| Nondifferentiable programming | `Optimality/Programming` | Fritz John conditions via normals to epigraphs and graphs, via separate and symmetric subgradients, condensed Lagrangian conditions, abstract maximum principle, upper subdifferential conditions (M Thm. 6.5–Thm. 6.12) |
| Bilevel programming | `Optimality/Bilevel`, `Optimality/BilevelSmooth`, `Subdifferential/NegConvexHull` | value function reformulation, partial calmness, weak sharp minima (M Prop. 6.13–6.18); difference rule (M Lemma 6.22); value function subgradients; optimality conditions for smooth bilevel programs (M Thm. 6.21, 6.23); `∂(-f) ⊆ -co ∂f` for Lipschitz `f` |

M = [Mordukhovich 2018], M24 = [Mordukhovich 2024], CV = [Clason–Valkonen]. `ROADMAP.md` lists every statement of
[Mordukhovich 2018, Ch. 1–6] with its Lean name or status, and the corresponding results of
[Clason–Valkonen]. All numbered results of Ch. 1, 3 and 4 are formalized, and those of Ch. 2
except Cor. 2.4, the bound `‖x̄ − x₀‖ ≤ λ` in Thm. 2.14, the epi-regular part of Thm. 2.19 and
the countable extremal principles of Sect. 2.2. All numbered theorems, propositions and
corollaries of Sect. 6.1–6.2 are formalized, and those of Sect. 6.3 except the Lipschitzian
Thm. 6.25–6.26. In Ch. 1, the inclusion `⊆` in (1.38) and
Prop. 1.37(ii) remain; the worked examples are not formalized. `ROADMAP.md` also records the
places where a statement of the book had to be corrected (Thm. 2.12, 2.14, 3.14, 3.25, 4.1,
Cor. 4.8, Thm. 4.18, Prop. 6.13, Thm. 6.21).

For [Mordukhovich 2024, Ch. 1], `ROADMAP.md` lists the statements of Sect. 1.2–1.4 with their Lean
names or status. Formalized: the second-order subdifferentials of Sect. 1.2, Thm. 1.65, the
Moreau envelope results Lemma 1.68–Cor. 1.72, Def. 1.73–Lemma 1.81, Thm. 1.84 (with a proof
that avoids Lemma 1.81), Def. 1.85–Thm. 1.86, and in Sect. 1.5 Def. 1.88–Prop. 1.90,
Prop. 1.93–Lemma 1.97 and Def. 1.100. Thm. 1.70–1.71
assume prox-boundedness, which the book omits (a correction). Cor. 1.87, Thm. 1.91 and Thm. 1.98
with its corollaries remain.

For SCD mappings, `ROADMAP.md` lists the results of [Gfrerer–Outrata 2022, Sect. 3–6] and their
Lean names. Everything there is formalized except the symmetric representation of
`𝒮∂q` for prox-regular `q` (Prop. 3.26, whose SCD part follows from [Mordukhovich 2024, Cor. 1.72])
and Cor. 3.27,
quadratic bundles (3.30–3.34), the adjoint formulas (21) and (24b) for a general change of
variables, and the worked examples. Minty's theorem is proved (`SCD/Minty`, via the Fitzpatrick
function), so maximally monotone mappings are SCD; Prop. 3.22–Cor. 3.24 are proved for the
local notions of Def. 3.20 (`SCD/LocalMonotone`), through a maximally monotone extension
(Zorn's lemma). Sect. 7 (strong
metric regularity, tilt stability) is not started.

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
- **SCD mappings.** `F : E → Set E` on a finite-dimensional real inner product space `E`; subspaces
  of `E × E` are `Submodule ℝ (E × E)`, compared through orthogonal projections in the Euclidean
  model of `E × E`. `E × E` keeps the sup norm, so estimates are stated with norms on `E`. The
  adjoint subspace is the orthogonal complement for `ω((u, v), (y*, x*)) = ⟪v, y*⟫ - ⟪u, x*⟫`, and
  `𝒮*F` is defined as `{L* | L ∈ 𝒮F}` ([Gfrerer–Outrata 2022, Remark 3.5]).

## Build

```
lake exe cache get && lake build
```

## Status

All 89 files compile against Mathlib v4.33.1 with no `sorry`.
`lake env lean scripts/AuditAxioms.lean` checks that no declaration depends on an axiom beyond
`propext`, `Classical.choice`, `Quot.sound` (2109 declarations checked).
