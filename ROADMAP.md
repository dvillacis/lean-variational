# Roadmap

Statements of [Mordukhovich 2018, Ch. 1–6], numbered as in its *List of Statements*, with their
status in this library. Chapters 1–6 of the book are set in finite-dimensional spaces. Ch. 7–10
(semi-infinite programs, set optimization, economics) are out of scope for now.

Legend: ✓ formalized (no `sorry`), ◐ partially formalized (what is missing is stated),
☐ not started. CV = [Clason–Valkonen].

## Chapter 1. Constructions of generalized differentiation

| # | Statement | Status | Lean | CV |
|---|---|---|---|---|
| (1.1) | Painlevé–Kuratowski outer limit | ✓ | `outerLimit` | §6.1 |
| (1.3) | Euclidean projector | ✓ | `euclideanProj` | |
| 1.1 | Def: basic normals (via projections) | ✓ | `projNormalCone`; equal to `normalCone` by Thm 1.6 | |
| 1.2 | Normal cone characterization of boundary points | ✓ | `exists_ne_zero_mem_normalCone_iff` | |
| 1.3 | Robustness of basic normals | ✓ | `normalCone_eq_outerLimit_normalCone` | Cor 18.9 |
| 1.4 | Normals to products of sets | ☐ | | |
| 1.5 | Ex: nonconvexity of the basic normal cone | ☐ | | Ex 18.1 |
| (1.5), (1.6) | Regular normals and `ω`-normals | ✓ | `regularNormalCone`, `epsNormalCone` | (18.2), (18.7) |
| 1.6 | Equivalent descriptions of basic normals | ✓ | `toDual_projNormalCone`, `normalCone_eq_outerLimit_epsNormalCone` (Step 1: `toDual_sub_mem_regularNormalCone`) | Thm 18.2 |
| 1.7 | Normals to convex sets | ✓ | `mem_epsNormalCone_of_convex`, `mem_regularNormalCone_of_convex`, `normalCone_eq_regularNormalCone_of_convex`, `mem_normalCone_of_convex` | Lemma 18.6 |
| 1.8 | Def: contingent cone | ✓ | `contingentCone` (by its sequential representation; (1.11) as a theorem and the link to Mathlib's `posTangentConeAt` are ☐) | (18.1) |
| 1.9 | Duality between prenormal and contingent cones | ✓ | `regularNormalCone_eq_polar_contingentCone` (inclusion in any normed space: `regularNormalCone_subset_polar_contingentCone`) | Lemma 18.10 |
| 1.10 | Smooth variational description of regular normals | ◐ | (i): `mem_regularNormalCone_iff_exists_localMax`; (ii) ☐ | |
| 1.11 | Def: basic coderivative | ✓ | `coderiv`; regular coderivative (1.16): `regularCoderiv`; limiting representation (1.17) ☐ | §20.1 |
| 1.12 | Coderivatives of smooth mappings | ✓ | `coderiv_of_hasFDerivAt_of_continuousAt`, `regularCoderiv_of_hasFDerivAt` | Thm 20.14 |
| 1.13 | Coderivatives of convex-graph mappings | ☐ | | |
| 1.14 | Ex: coderivative calculations | ☐ | | §20.3 |
| 1.15, 1.16 | Extremal property of convex-valued mappings | ☐ | | |
| 1.17 | Basic normals to epigraphs | ◐ | sign `ℓ (0, 1) ≤ 0`: `apply_zero_one_nonpos_of_mem_normalCone_epi`; the representation through `D`, `D^∞` ☐ | |
| 1.18 | Def: basic and singular subdifferentials | ✓ | `subdiff`, `singularSubdiff` | (16.5) |
| 1.19 | Subgradients of indicator functions | ◐ | `∂δ_Ω = N`: `subdiff_convex_indicator`; `∂^∞δ_Ω = N` ☐ | |
| 1.20 | Robustness of basic and singular subdifferentials | ☐ | | |
| 1.21 | Ex: subgradients of simple functions on ℝ | ☐ | | Ex 16.5, 16.7 |
| 1.22 | Subdifferentials of locally Lipschitzian functions | ☐ | | |
| 1.23 | Subdifferentials from coderivatives | ☐ | | |
| 1.24 | Subgradients of smooth functions | ✓ | `subdiff_of_hasFDerivAt_of_continuousAt` | Thm 16.9 |
| (1.33), (1.34) | Regular subgradients and `ω`-subgradients | ✓ | `regularSubdiff`, `epsSubdiff`; `∂̂f = {f'}`: `regularSubdiff_of_hasFDerivAt` | (16.2), Thm 16.4 |
| 1.25 | Subgradients of convex functions | ◐ | `ω = 0`: `mem_regularSubdiff_of_convex`, `subdiff_eq_regularSubdiff_of_convex`, `mem_subdiff_of_convex`; `ω > 0` and `∂^∞φ = N(·; dom φ)` ☐ | Thm 16.3, 16.8 |
| 1.26 | Geometric descriptions of regular subgradients | ◐ | first inclusion (`ω ≥ 0`): `coprod_mem_epsNormalCone_of_mem_epsSubdiff`; (1.36): `mem_regularSubdiff_iff_coprod_mem`; converse for `0 < ω < 1` ☐ | |
| 1.27 | Smooth variational descriptions of regular subgradients | ☐ | | |
| 1.28 | Limiting representations of basic and singular subgradients | ◐ | first representation in (1.37): `subdiff_eq_outerLimit`; `ω`-representation and (1.38) ☐ | (16.5) |
| 1.29 | Singular subgradients under Lipschitzian additions | ☐ | | |
| 1.30 | Elementary rules | ◐ | (i): `zero_mem_regularSubdiff_of_isLocalMin`, `zero_mem_subdiff_of_isLocalMin`; (ii) regular: `mem_regularSubdiff_add_iff`; (ii) basic ☐ | Thm 16.2, Cor 16.6, Thm 16.13, Cor 25.27 |
| 1.31 | Ex: subdifferentials of Lipschitzian functions | ☐ | | Ex 16.11 |
| 1.32 | Coderivative scalarization | ☐ | | |
| 1.33–1.38 | Subgradients of the distance function; right-sided subdifferential | ☐ | | |
| Ex 1.62 | Slanted regular normals to epigraphs | ✓ | `eq_of_mem_regularNormalCone_epi` | |

Also formalized, with no numbered statement in the book: `regularNormalCone` and `normalCone` are
closed cones (CV Thm 18.8) and trivial at interior points; `N̂ ⊆ N` (CV Thm 18.5(ii));
`N̂(x; Ω) = ∂̂δ_Ω(x)` (CV Cor 18.7): `regularSubdiff_convex_indicator`; `∂̂ ⊆ ∂`:
`regularSubdiff_subset_subdiff`.

## Chapter 2. Fundamental principles of variational analysis

| # | Statement | Status | Notes |
|---|---|---|---|
| 2.1, 2.2 | Local extremality of sets; extremality and separation | ☐ | |
| 2.3 | Basic extremal principle | ☐ | central result; proof by smooth penalization and Thm 1.6 |
| 2.4, 2.5 | Convex sets; approximate extremal principle | ☐ | |
| 2.6–2.11 | Conic and contingent extremal principles | ☐ | |
| 2.12, 2.13 | General variational principle; Ekeland's variational principle | ☐ | not in Mathlib; CV Thm 17.13 |
| 2.14, 2.15 | Suboptimality; fixed points | ☐ | |
| 2.16–2.18 | Basic intersection rule; normals to intersections and sums | ☐ | |
| 2.19–2.21 | Subdifferential sum rules | ☐ | |

## Chapter 3. Well-posedness and coderivative calculus

| # | Statement | Status | Notes |
|---|---|---|---|
| 3.1, 3.2 | Lipschitz-like (Aubin) property, metric regularity, covering; their equivalence | ☐ | CV Thm 27.3, Cor 27.5 |
| 3.3–3.8 | Coderivative criteria (Mordukhovich criterion) | ☐ | CV Cor 27.16, 27.18 |
| 3.9–3.15 | Coderivative sum, chain and product rules | ☐ | CV Ch 25 |
| 3.16–3.22 | Parametric variational systems | ☐ | |
| 3.17 | Def: second-order subdifferential | ☐ | |
| 3.23–3.31 | Amenable and prox-regular functions; failure of metric regularity | ☐ | |

## Chapter 4. First-order subdifferential calculus

| # | Statement | Status | Notes |
|---|---|---|---|
| 4.1–4.4 | Marginal functions; infimal convolutions | ☐ | |
| 4.5–4.8 | Chain, product and quotient rules | ☐ | CV Cor 25.29–25.31 |
| 4.9, 4.10 | Minimum and maximum functions | ☐ | |
| 4.11–4.14 | Mean value theorems | ☐ | |
| 4.15–4.19 | Characterizations of Lipschitz continuity, strict differentiability, monotonicity, convexity | ☐ | Mathlib has Rademacher's theorem (CV Thm 13.25) |

## Chapter 5. Coderivatives of maximal monotone operators

| # | Statement | Status |
|---|---|---|
| 5.1–5.9 | Hypomonotonicity; coderivative criteria for global maximal monotonicity | ☐ |
| 5.10–5.17 | Strong local maximal monotonicity; strong metric regularity | ☐ |

## Chapter 6. Nondifferentiable and bilevel optimization

| # | Statement | Status |
|---|---|---|
| 6.1–6.12 | Lower and upper subdifferential optimality conditions; nondifferentiable programming | ☐ |
| 6.13–6.20 | Bilevel programs: value function approach, partial calmness, weak sharp minima | ☐ |
| 6.21–6.27 | Optimality conditions for smooth and Lipschitzian bilevel programs | ☐ |

## Clason–Valkonen topics outside [Mordukhovich 2018, Ch. 1–6]

| CV | Topic | Status |
|---|---|---|
| Ch 13 | Clarke subdifferential: Fermat principle (Thm 13.4), `C¹` (Thm 13.5), convex (Thm 13.8), calculus (Thm 13.20, 13.23), finite-dimensional characterization (Thm 13.26) | ☐ |
| Thm 16.10 | `∂_C F = cl co ∂_M F` for locally Lipschitz `F` | ☐ |
| Ch 17 | `ε`-subdifferentials; fuzzy Fermat principle (Lemma 17.9) | ☐ |
| (18.4) | Clarke tangent cone; `T̂_C(x) = N_C(x)°` (Thm 18.15); normal regularity (Thm 18.24) | ☐ |
| Ch 20 | Graphical derivatives; `D̂*F = (DF)°+` (Cor 20.9) | ☐ |
| Ch 26 | Second-order optimality conditions | ☐ |
| Ch 28 | Stability; metric subregularity of convex subdifferentials (Thm 28.8) | ☐ |

## Suggested order of work

1. Finish Ch. 1: products (Prop 1.4), robustness of subdifferentials (Prop 1.20), the
   `ω`-representation in Thm 1.28 (transport Thm 1.6 to `E × ℝ` through a Euclidean norm),
   singular subgradients (Props 1.19, 1.25, 1.29), and the Lipschitz case (Thm 1.22, which gives
   `∂^∞φ = {0}`).
2. Ekeland's variational principle (Cor 2.13), then the extremal principle (Thm 2.3) and its
   consequences: intersection rule (Thm 2.16) and sum rules (Thm 2.19).
3. Well-posedness (Ch. 3): the Mordukhovich criterion for the Lipschitz-like property and
   metric regularity (Thm 3.3), and coderivative calculus.
4. Ch. 4 calculus rules, then the bilevel optimality conditions of Ch. 6.
