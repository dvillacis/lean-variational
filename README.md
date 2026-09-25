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

M = [Mordukhovich 2018], CV = [Clason–Valkonen]. `ROADMAP.md` lists every statement of
[Mordukhovich 2018, Ch. 1–6] with its Lean name or status, and the corresponding results of
[Clason–Valkonen]. All numbered results of Ch. 1 are formalized except the converse of Thm. 1.22
(which the book derives from Ch. 3–4), the inclusion `⊆` in (1.38) and Prop. 1.37(ii); the
worked examples are not.

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

All 20 files compile against Mathlib v4.33.1 with no `sorry`.
`lake env lean scripts/AuditAxioms.lean` checks that no declaration depends on an axiom beyond
`propext`, `Classical.choice`, `Quot.sound` (271 declarations checked).
