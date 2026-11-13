# Roadmap

Statements of [Mordukhovich 2018, Ch. 1–6], numbered as in its *List of Statements*, with their
status in this library. Chapters 1–6 of the book are set in finite-dimensional spaces. Ch. 7–10
(semi-infinite programs, set optimization, economics) are out of scope for now.

Legend: ✓ formalized (no `sorry`), ◐ partially formalized (what is missing is stated),
☐ not started. CV = [Clason–Valkonen].

## Chapter 1. Constructions of generalized differentiation

All numbered theorems, propositions, corollaries, lemmas and definitions of Ch. 1 are formalized,
except the two items marked ◐ below. The worked examples (1.5, 1.14, 1.16, 1.21, 1.31, 1.35) and
the exercises (1.39–1.87, except 1.62) are not.

| # | Statement | Status | Lean | CV |
|---|---|---|---|---|
| (1.1) | Painlevé–Kuratowski outer limit | ✓ | `outerLimit` | §6.1 |
| (1.3) | Euclidean projector | ✓ | `euclideanProj` | |
| 1.1 | Def: basic normals (via projections) | ✓ | `projNormalCone`; equal to `normalCone` by Thm 1.6 | |
| 1.2 | Normal cone characterization of boundary points | ✓ | `exists_ne_zero_mem_normalCone_iff` (finite-dimensional normed spaces; Hilbert version `_inner`) | |
| 1.3 | Robustness of basic normals | ✓ | `normalCone_eq_outerLimit_normalCone` | Cor 18.9 |
| 1.4 | Normals to products of sets | ✓ | `coprod_mem_normalCone_prod_iff`, `mem_normalCone_prod_iff`; regular normals: `coprod_mem_regularNormalCone_prod_iff` | |
| 1.5 | Ex: nonconvexity of the basic normal cone | ☐ | | Ex 18.1 |
| (1.5), (1.6) | Regular normals and `ω`-normals | ✓ | `regularNormalCone`, `epsNormalCone` | (18.2), (18.7) |
| 1.6 | Equivalent descriptions of basic normals | ✓ | `toDual_projNormalCone`; `ω`-representation: `normalCone_eq_outerLimit_epsNormalCone` (finite-dimensional normed spaces, via `toEuclidean`; Hilbert version `_inner`); Step 1: `toDual_sub_mem_regularNormalCone` | Thm 18.2 |
| 1.7 | Normals to convex sets | ✓ | `mem_epsNormalCone_of_convex`, `mem_regularNormalCone_of_convex`, `normalCone_eq_regularNormalCone_of_convex`, `mem_normalCone_of_convex` | Lemma 18.6 |
| 1.8 | Def: contingent cone | ✓ | `contingentCone` (sequential representation); (1.11): `contingentCone_eq_outerLimit` | (18.1) |
| 1.9 | Duality between prenormal and contingent cones | ✓ | `regularNormalCone_eq_polar_contingentCone` (inclusion in any normed space: `regularNormalCone_subset_polar_contingentCone`) | Lemma 18.10 |
| 1.10 | Smooth variational description of regular normals | ✓ | (i): `mem_regularNormalCone_iff_exists_localMax`; (ii): `mem_regularNormalCone_iff_exists_concave` (inner product spaces; the `C¹` convex majorant is built by integration, `convexMajorant`) | |
| 1.11 | Def: basic coderivative | ✓ | `coderiv`; (1.16): `regularCoderiv`; (1.17): `coderiv_eq_outerLimit` | §20.1 |
| 1.12 | Coderivatives of smooth mappings | ✓ | `coderiv_of_hasFDerivAt_of_continuousAt`, `regularCoderiv_of_hasFDerivAt` | Thm 20.14 |
| 1.13 | Coderivatives of convex-graph mappings | ✓ | `coderiv_eq_regularCoderiv_of_convex`, `mem_coderiv_of_convex` | |
| 1.14 | Ex: coderivative calculations | ☐ | | §20.3 |
| 1.15 | Extremal property of convex-valued mappings | ✓ | `apply_le_of_mem_coderiv`; inner limit (1.20): `innerLimit` | |
| 1.16 | Ex: assumptions of Thm 1.15 are essential | ☐ | | |
| 1.17 | Basic normals to epigraphs | ✓ | `mem_normalCone_epi_iff`, `apply_zero_one_nonpos_of_mem_normalCone_epi` | |
| 1.18 | Def: basic and singular subdifferentials | ✓ | `subdiff`, `singularSubdiff` | (16.5) |
| 1.19 | Subgradients of indicator functions | ✓ | `subdiff_convex_indicator`, `singularSubdiff_convex_indicator` | |
| 1.20 | Robustness of basic and singular subdifferentials | ✓ | `subdiff_eq_outerLimit_subdiff`, `singularSubdiff_eq_outerLimit_singularSubdiff` | |
| 1.21 | Ex: subgradients of simple functions on ℝ | ☐ | | Ex 16.5, 16.7 |
| 1.22 | Subdifferentials of locally Lipschitzian functions | ✓ | "only if": `singularSubdiff_eq_zero_of_lipschitz`, `subdiff_nonempty_of_lipschitz`, (1.27): `norm_le_of_mem_subdiff_of_lipschitz`, (1.28): `norm_comp_inl_le_of_mem_normalCone_epi`; "if" (via Thm 4.15): `exists_lipschitzOnWith_of_singularSubdiff`; both: `exists_lipschitzOnWith_iff_singularSubdiff_eq_zero` | |
| 1.23 | Subdifferentials from coderivatives | ✓ | (1.30): `subdiff_eq_coderiv_one` (`⊆` for every real-valued `f`: `subdiff_subset_coderiv_one`); (1.31): `singularSubdiff_subset_coderiv_zero` | |
| 1.24 | Subgradients of smooth functions | ✓ | `subdiff_of_hasFDerivAt_of_continuousAt` | Thm 16.9 |
| (1.33), (1.34) | Regular subgradients and `ω`-subgradients | ✓ | `regularSubdiff`, `epsSubdiff`; `∂̂f = {f'}`: `regularSubdiff_of_hasFDerivAt` | (16.2), Thm 16.4 |
| 1.25 | Subgradients of convex functions | ✓ | `mem_epsSubdiff_of_convex`, `mem_regularSubdiff_of_convex`, `subdiff_eq_regularSubdiff_of_convex`, `mem_subdiff_of_convex`, `singularSubdiff_eq_normalCone_dom_of_convex` | Thm 16.3, 16.8 |
| 1.26 | Geometric descriptions of regular subgradients | ✓ | `coprod_mem_epsNormalCone_of_mem_epsSubdiff`, `mem_epsSubdiff_of_coprod_mem_epsNormalCone`, (1.36): `mem_regularSubdiff_iff_coprod_mem` | |
| 1.27 | Smooth variational descriptions of regular subgradients | ✓ | first part: `mem_regularSubdiff_iff_exists_support`; second part: `exists_concave_support_of_mem_regularSubdiff` (inner product spaces) | |
| 1.28 | Limiting representations of basic and singular subgradients | ◐ | (1.37): `subdiff_eq_outerLimit`, `subdiff_eq_outerLimit_epsSubdiff`; (1.38) `⊇`: `outerLimit_smul_regularSubdiff_subset_singularSubdiff`; (1.38) `⊆` ☐ (the book omits this proof and cites [Rockafellar–Wets, Thm 8.9]) | (16.5) |
| 1.29 | Singular subgradients under Lipschitzian additions | ✓ | `singularSubdiff_add_of_lipschitz` | |
| 1.30 | Elementary rules | ✓ | (i): `zero_mem_regularSubdiff_of_isLocalMin`, `zero_mem_subdiff_of_isLocalMin`; (ii): `mem_regularSubdiff_add_iff`, `mem_subdiff_add_iff` | Thm 16.2, Cor 16.6, Thm 16.13, Cor 25.27 |
| 1.31 | Ex: subdifferentials of Lipschitzian functions | ☐ | | Ex 16.11 |
| 1.32 | Coderivative scalarization | ✓ | `subdiff_comp_subset_coderiv` (`f` continuous at `x₀`), `subdiff_comp_eq_coderiv` (`f` Lipschitz, finite dimensions) | |
| 1.33 | Subdifferentiation of the distance function | ✓ | `distFun`; (i): `regularSubdiff_distFun_of_mem` (any normed space), `subdiff_distFun_of_mem` (closed `Ω`, finite dimensions); Step 2: `mem_regularNormalCone_of_mem_regularSubdiff_distFun`; (ii): `regularSubdiff_distFun_of_proj_eq`, `regularSubdiff_distFun_eq_empty`, `regularSubdiff_distFun_subset`, `subdiff_distFun_of_notMem` (Euclidean, closed `Ω`) | |
| 1.34 | Regular subgradients of the distance function via enlargements | ✓ | `regularSubdiff_distFun_eq_of_pos`; (1.49): `enlargement`; (1.51): `infDist_enlargement` | |
| 1.35 | Ex: basic subgradients vs. normals to enlargements | ☐ | | |
| 1.36 | Def: right-sided subdifferential | ✓ | `rightSubdiff`; `regularSubdiff_subset_rightSubdiff`, `rightSubdiff_subset_subdiff` | |
| 1.37 | Properties of the right-sided subdifferential | ◐ | (i): `rightSubdiff_eq_subdiff_of_isLocalMin`, `zero_mem_rightSubdiff_of_isLocalMin`; (ii) ☐: the book's proof only says to proceed as for (1.37), and that argument does not keep the constraint `φ x ≥ φ x₀` | |
| 1.38 | Right-sided subgradients of the distance function | ✓ | (1.55): `rightSubdiff_distFun_subset` (unit normals); (1.56): `mem_normalCone_enlargement_iff` (finite dimensions) | |
| Ex 1.62 | Slanted regular normals to epigraphs | ✓ | `eq_of_mem_regularNormalCone_epi` | |

Also formalized, with no numbered statement in the book: `regularNormalCone` and `normalCone` are
closed cones (CV Thm 18.8) and trivial at interior points; `N̂ ⊆ N` (CV Thm 18.5(ii)); regular
normals are antitone in the set (Ex 1.39(iii), `regularNormalCone_anti`);
`N̂(x; Ω) = ∂̂δ_Ω(x)` (CV Cor 18.7): `regularSubdiff_convex_indicator`; `∂̂ ⊆ ∂`:
`regularSubdiff_subset_subdiff`; normal cones and subdifferentials only depend on the data near
the point (`normalCone_congr`, `regularSubdiff_congr`, `subdiff_congr`, `singularSubdiff_congr`);
normals pull back along linear isomorphisms (`mem_normalCone_image_iff`).

## Chapter 2. Fundamental principles of variational analysis

Sections 2.1, 2.3 and 2.4 are formalized. The countable extremal principles of Section 2.2
(Def 2.6 – Thm 2.11) and the worked examples are not.

| # | Statement | Status | Lean | CV |
|---|---|---|---|---|
| 2.1 | Def: local extremality of finitely many sets | ✓ | `IsLocallyExtremal`; two sets: `isLocallyExtremal_pair_iff`; `U = ℝⁿ`: `IsLocallyExtremal.exists_global` | |
| 2.2 | Extremality and separation | ✓ | `AreSeparated`; (i): `AreSeparated.isLocallyExtremal`; (ii): `AreSeparated.of_isLocallyExtremal` (locally closed convex sets); (iii): `areSeparated_iff_forall_isLocallyExtremal` | |
| 2.3 | Basic extremal principle | ✓ | `IsLocallyExtremal.exists_mem_normalCone` (finite-dimensional normed spaces; norm-free form `_ne_zero`, Hilbert version `_inner`); (2.9): `IsLocallyExtremal.exists_mem_normalCone_pair`; Prop 1.2 recovered: `exists_mem_normalCone_norm_eq_one_of_mem_frontier` | |
| 2.4 | Extremality of convex sets via relative interiors | ☐ | needs proper separation under relative interiors [Rockafellar, Thm 11.3], not in Mathlib | |
| 2.5 | Approximate extremal principle | ✓ | `IsLocallyExtremal.exists_approx` | |
| 2.6–2.11 | Conic and contingent extremal principles for countable systems | ☐ | | |
| 2.12 | General variational principle | ✓ | `exists_forall_add_le_add`, `general_variational_principle`; (2.21): `general_variational_principle_subadditive` (the strict inequality needs a suitable choice of the minimizer, `exists_lex_minimizer`; it fails for some minimizers) | |
| 2.13 | Ekeland's variational principle | ✓ | `ekeland_variational_principle`; (2.24): `norm_le_of_hasFDerivAt_of_forall_le_add_norm` | Thm 2.17 |
| 2.14 | Subdifferential almost stationary conditions | ◐ | upper part: `ekeland_almost_stationary` (as stated); lower part: `exists_mem_regularSubdiff_almost_stationary` with `‖x̄ − x₀‖ < λ + η` for every `η > 0` (inner product spaces); the book's proof only gives `2λ` (`exists_mem_regularSubdiff_norm_sub_lt_two_mul`), and `≤ λ` is not proved | |
| 2.15 | Fixed points | ✓ | `exists_fixedPoint_of_variational`, `exists_mem_self_of_variational`, `exists_eq_singleton_of_variational` (with `θ` subadditive, which the book's proof uses) | |
| Ex 2.25(iii) | Density of `dom ∂̂φ` | ✓ | `exists_mem_ball_regularSubdiff_nonempty`, `exists_seq_tendsto_regularSubdiff_nonempty`, `frequently_funNhds_regularSubdiff_nonempty` | |
| 2.16 | Basic intersection rule | ✓ | `normalCone_inter_subset`; equality and regularity: `normalCone_inter_eq`; `N̂ + N̂ ⊆ N̂(∩)`: `regularNormalCone_add_subset_inter` | |
| 2.17 | Normals to finite intersections | ✓ | `normalCone_iInter_subset`, `normalCone_iInter_eq`, `normalCone_biInter_subset` | |
| 2.18 | Normals to sums of sets | ✓ | `normalCone_add_subset` | |
| 2.19 | Subdifferential sum rules | ◐ | (2.35): `subdiff_add_subset`; (2.36): `singularSubdiff_add_subset`; lower-regular equality: `subdiff_add_eq`; `∂̂ + ∂̂ ⊆ ∂̂(+)`: `regularSubdiff_add_subset`; equality in (2.36) and the epi-regular statement ☐ (the book says "similarly"; the argument needs metric regularity of the constraint system) | |
| 2.20 | Semi-Lipschitzian sum rule | ✓ | `subdiff_add_subset_of_lipschitz`, `subdiff_lipschitz_add_subset`; `exists_mem_subdiff_norm_le_of_isLocalMin_add` | |
| 2.21 | Sums of finitely many functions | ✓ | `subdiff_sum_subset`, `singularSubdiff_sum_subset`, `subdiff_sum_eq` (epi-regular part as in Thm 2.19) | |

## Chapter 3. Well-posedness and coderivative calculus

All numbered statements are formalized; "max/min attained" in some exact-bound formulas is stated
as sup/inf. Sets and graphs are locally closed around the reference points (explicit hypotheses),
spaces are finite-dimensional for coderivative results; Def 3.1 and Thm 3.2 hold in metric spaces.

| # | Statement | Status | Lean | CV |
|---|---|---|---|---|
| 3.1 | Def: covering, metric regularity, Lipschitz-like property; exact bounds | ✓ | `HasCoveringWith`, `MetricallyRegularWith`, `LipschitzLikeWith`, `…At`; `covBound`, `regBound`, `lipBound` (in `ℝ≥0∞`; distances to `∅` via `infEDist`) | (27.1) |
| 3.2 | Equivalences between well-posedness properties | ✓ | (i): `hasCoveringAt_iff_metricallyRegularAt`, `covBound_eq_inv_regBound` (needs `Nontrivial E`; false for `E = {0}`); (ii): `lipschitzLikeAt_iff_metricallyRegularAt_invMap`, `lipBound_eq_regBound_invMap`; Step 1: `metricallyRegularWith_of_infEDist_le` | Thm 27.3 |
| (1.14) | Norm of positively homogeneous maps | ✓ | `posHomNorm`, `posHomLowerNorm`, `coderivKer`; inverse coderivative `mem_coderiv_invMap_iff` | |
| 3.3 | Coderivative criteria (Mordukhovich criterion) | ✓ | (i): `hasCoveringAt_iff_coderivKer_eq`, `covBound_eq_posHomLowerNorm`; (ii): `metricallyRegularAt_iff_coderivKer_eq`, `metricallyRegularAt_iff_forall_zero_mem_coderiv`, `regBound_eq_posHomNorm_invMap_coderiv`; (iii): `lipschitzLikeAt_iff_coderiv_zero_eq`, `lipBound_eq_posHomNorm_coderiv`; Step 1: `posHomNorm_coderiv_le_lipBound` (any normed spaces); Step 2 via Thm 2.12 and Cor 2.20 (`metricallyRegularWith_of_forall_mul_norm_le`) | Lemma 27.11, Cor 27.12 |
| 3.5 | Local Lipschitz continuity of locally bounded mappings | ✓ | `LocallyLipschitzAt`, `locallyLipschitzAt_iff_forall_coderiv_zero_eq`, `lipBoundAt_eq_iSup_posHomNorm_coderiv` | |
| 3.6 | Convex-graph mappings | ✓ | `metricallyRegularAt_iff_mem_interior_of_convex`, `hasCoveringAt_iff_mem_interior_of_convex`, `regBound_eq_of_convex`, `covBound_eq_of_convex` | |
| 3.7 | Locally Lipschitz single-valued mappings | ✓ | `metricallyRegularAt_iff_of_lipschitz`, `regBound_eq_of_lipschitz`, `covBound_eq_of_lipschitz` | |
| 3.8 | Smooth mappings | ✓ | `metricallyRegularAt_iff_surjective`, `regBound_eq_of_hasFDerivAt`, `covBound_eq_of_hasFDerivAt`, `covBound_eq_inv_norm_symm` (via Thm 3.3, not Lyusternik–Graves) | |
| 3.9 | Coderivative sum rules | ✓ | (i): `coderiv_add_subset`; (3.24): `coderiv_add`, `coderiv_add'` (no assumptions); (ii): `coderiv_add_subset_iUnion` (closed graphs) | Thm 25.15 |
| 3.10 | Sum rules for Lipschitz-like mappings | ✓ | `coderiv_add_subset_of_lipschitzLike`, `coderiv_add_subset_iUnion_of_lipschitzLike` | |
| 3.11 | Coderivative chain rules | ✓ | (i): `coderiv_setComp_subset`; (ii): `coderiv_setComp_subset_iUnion`; (iii) full rank: `coderiv_comp_of_surjective`; (iii) graphical regularity: `coderiv_comp_eq_of_graphicallyRegularAt`, `graphicallyRegularAt_comp`; (3.31): `coprod_zero_mem_coderiv_chainGraphMap_iff` | Thm 25.16, 25.18 |
| 3.12 | Chain rules for Lipschitz-like / metrically regular mappings | ✓ | `coderiv_setComp_subset_of_lipschitzLike_or_metricallyRegular`, `…_iUnion_…` | |
| 3.13 | Normals to inverse images | ✓ | `normalCone_preimage_setValued_subset`, `…_of_metricallyRegular`; equality: `normalCone_preimage_eq_of_normallyRegularAt`, `normalCone_preimage_of_surjective_of_finiteDimensional` (Ex 1.54); `Θ = {z̄}`: `normalCone_invMap_subset`, `normalCone_invMap_eq` | |
| 3.14 | Compositions with binary operations | ✓ | `coderiv_binaryComp_subset` (adds the qualification condition (3.22), without which the statement fails) | |
| 3.15 | Coderivatives of inner products | ✓ | `coderiv_innerComp_subset` | |
| 3.16 | Coderivatives of general PVS | ✓ | `pvsSolutionMap`, `coderiv_pvsSolutionMap` (3.38), `coderivKer_pvsSolutionMap` (3.39); regular version `regularCoderiv_pvsSolutionMap` | |
| 3.17 | Def: second-order subdifferential | ✓ | `secondOrderSubdiff`; (3.43): `secondOrderSubdiff_of_hasFDerivAt` | |
| 3.18 | PVS with composite potentials | ✓ | `coderiv_pvsSolutionMap_compositePotential`, `coderivKer_…`; (3.47) (Ex 3.78(i)): `secondOrderSubdiff_comp_of_surjective`; first-order chain rule (Ex 1.72): `subdiff_comp_of_surjective` | |
| 3.19 | PVS with composite fields | ✓ | (i): `coderiv_pvsSolutionMap_compositeField`, `coderivKer_…`; (ii): `coderiv_pvsSolutionMap_compositeField_subset`, `coderivKer_…_subset` | |
| 3.20 | Metric regularity of general PVS | ✓ | `metricallyRegularAt_pvsSolutionMap_iff`, `…_iff_lipschitzLikeAt`, `regBound_pvsSolutionMap` | |
| 3.21 | Subdifferential PVS with composite potentials | ✓ | `metricallyRegularAt_pvsSolutionMap_compositePotential_iff` | |
| 3.22 | Subdifferential PVS with composite fields | ✓ | `metricallyRegularAt_pvsSolutionMap_compositeField_iff` | |
| 3.23 | Def: amenable, strongly amenable functions | ✓ | `AmenableAt`, `StronglyAmenableAt` | |
| 3.24 | Single-valuedness of Lipschitz-like monotone operators | ✓ | `LipschitzLikeAt.singleValuedAround` (also for hypomonotone operators, with a Lipschitz localization) | |
| 3.25 | Failure of metric regularity for PVS with monotone fields | ✓ | `not_metricallyRegularAt_pvsSolutionMap_of_locallyMonotoneAt` (corrected: the book's hypothesis "no neighborhood of `ȳ` where `Q` is single-valued" must be "`Q` not single-valued around `(ȳ, z̄)`"; counterexample `Q y = {0, 1}`, `f(x, y) = x`); book wording for convex-valued `Q`: `not_metricallyRegularAt_pvsSolutionMap_of_convex_values` | |
| 3.26 | Subdifferential PVS with convex potentials | ✓ | `not_metricallyRegularAt_pvsSolutionMap_subdiff_of_convex` (closed graph of `∂φ` proved: `isClosed_graph_subdiff_of_convex`) | |
| 3.29 | Subdifferential PVS with prox-regular potentials | ✓ | `not_metricallyRegularAt_pvsSolutionMap_compositePotential_of_proxRegular` | |
| 3.30 | Composite potentials with convex outer function | ✓ | `not_metricallyRegularAt_pvsSolutionMap_compositePotential_of_convex` | |
| 3.31 | Composite fields with prox-regular functions | ✓ | `not_metricallyRegularAt_pvsSolutionMap_compositeField_of_proxRegular` | |
| 3.27 | Def: prox-regularity, subdifferential continuity | ✓ | `ProxRegularFor`, `ProxRegularAt`, `SubdiffContinuousFor`, `ContinuouslyProxRegularFor` | |
| 3.28 | Continuously prox-regular functions with Lipschitz-like subdifferentials are `C^{1,1}` | ✓ | `ContinuouslyProxRegularFor.exists_C11` | |
| Ex 1.54 | Normals to inverse images under smooth maps | ✓ | `normalCone_preimage_of_surjective`, `regularNormalCone_preimage_of_surjective` (and finite-dimensional forms) | |
| Ex 1.59 | Indicator mappings | ✓ | `indicatorMap`, `coderiv_indicatorMap` | |
| M2006 Cor 4.34 | Coderivatives of implicit multifunctions | ✓ | `coderiv_implicit_subset`, `coderiv_implicit_eq` (graphical regularity), single-valued forms `coderiv_implicit_singleton_subset_of_eventually`, …; smooth case `coderiv_implicit_smooth_eq` | |

Also: global and maximal monotonicity (`GloballyMonotone`, `GloballyMaximalMonotone`), maximal
monotonicity of convex subdifferentials (`globallyMaximalMonotone_subdiff_of_convex`), Gâteaux
derivatives and `∂φ(x) = {v}` ⇔ differentiability for convex `φ`
(`subdiff_eq_singleton_iff_hasFDerivAt`, Ex 3.90(iv)).

## Chapter 4. First-order subdifferential calculus

All numbered statements are formalized. Functions are `E → EReal`, l.s.c. (or with locally
closed epigraph) around the reference points, spaces finite-dimensional. Every basic-subgradient
result below has its singular counterpart (`singular…`).

| # | Statement | Status | Lean | CV |
|---|---|---|---|---|
| (4.1), (4.2) | Marginal function, argminimum map | ✓ | `marginal`, `argminMap` | |
| 4.1 | Basic and singular subgradients of marginal functions | ✓ | (i): `subdiff_marginal_subset`, `singularSubdiff_marginal_subset` (under μ-inner semicontinuity; (4.5) additionally needs `μ` l.s.c. at `x̄`, counterexample in `Marginal.lean`); with the book's inner semicontinuity: `subdiff_marginal_subset_of_innerSemicontinuousAt` (adds attainment of the infimum near `x̄`, which the proof uses); (ii): `subdiff_marginal_subset_of_locallyBoundedAt` | |
| 4.2 | Marginal functions with Lipschitzian and metrically regular data | ✓ | `marginal_subset_of_lipschitz`, `marginal_subset_of_metricallyRegularAt` | |
| 4.3 | Local Lipschitz continuity of marginal functions | ✓ | `exists_lipschitzOnWith_marginal_of_lipschitzLikeAt`, `…_of_locallyBoundedAt` | |
| 4.4 | Infimal convolutions | ✓ | `subdiff_infConv_subset`, `infConv_subset_of_innerSemicontinuousAt`, `infConv_subset_of_locallyBoundedAt` | |
| 4.5 | General compositions `φ(x, g x)` | ✓ | (i): `subdiff_generalComp_subset` (4.10), `singularSubdiff_generalComp_subset` (4.11), equalities `generalComp_eq_of_hasFDerivAt`, `generalComp_eq_of_lowerRegularAt`; (ii): `subdiff_comp_strict_eq` (4.12), with coderivatives `subdiff_comp_strict_eq_coderiv` | |
| 4.6 | Chain rules | ✓ | `subdiff_comp_lipschitz_subset`, `singularSubdiff_comp_lipschitz_subset`; full rank (Ex 1.72): `subdiff_comp_of_surjective` | Cor 25.29 |
| 4.7 | Product rules | ✓ | `subdiff_mul_eq`, `subdiff_mul_subset`, `subdiff_mul_eq_add` | Cor 25.31 |
| 4.8 | Quotient rules | ✓ | `subdiff_div_eq`, `subdiff_div_subset`, `subdiff_div_eq_add` (the book's second formula has a sign error: `− ∂(φ₁(x̄)φ₂)` must be `+ ∂(−φ₁(x̄)φ₂)`; counterexample `f₁ = 1`, `f₂ = 1 − |x|`) | |
| 4.9 | Minimum functions | ✓ | `subdiff_iInf_subset` | |
| 4.10 | Maximum functions | ✓ | (i): `subdiff_iSup_subset`, equality `iSup_eq_of_epiRegularAt`; (ii): `subdiff_iSup_lipschitz_subset`, `iSup_lipschitz_eq_of_lowerRegularAt` | |
| (1.74)–(1.76), (4.18) | Upper and symmetric subdifferentials | ✓ | `upperRegularSubdiff`, `upperSubdiff`, `symmSubdiff`, `symmSingularSubdiff` | |
| 4.11 | Symmetric mean value theorem for continuous functions | ✓ | `symmetric_mean_value` | |
| 4.12 | Symmetric mean value theorem for Lipschitzian functions | ✓ | `symmetric_mean_value_of_lipschitz`, (4.21): `mean_value_of_lipschitz_of_lowerRegular` | |
| 4.13 | Approximate mean value theorem | ✓ | `approx_mean_value`, `exists_isMinOn_approx_mean_value` | |
| 4.14 | Mean value inequalities | ✓ | (i): `mean_value_ineq` (including `φ(b) = ∞`; the book's argument there needed a diagonal repair), (4.25): `abs_sub_le_norm_mul_of_forall_norm_le`; (ii): `exists_mem_subdiff_mean_value_of_lipschitz`, `abs_sub_le_norm_mul_of_lipschitz` | |
| 4.15 | Subdifferential characterizations of local Lipschitz continuity | ✓ | `lipschitz_tfae`; singular criterion: `exists_lipschitzOnWith_of_singularSubdiff`, `exists_lipschitzOnWith_iff_singularSubdiff_eq_zero` | |
| 4.16 | Constancy | ✓ | `eventually_eq_iff_regularSubdiff_subset_zero`, `forall_eq_iff_regularSubdiff_subset_zero` | |
| 4.17 | Strict differentiability | ✓ | `strictDifferentiability_tfae` | |
| 4.18 | Monotonicity | ✓ | `antitone_iff_regularSubdiff_subset_polar` (needs `U` convex; false otherwise, counterexample in `MonotoneConvex.lean`) | |
| 4.19 | Subdifferential monotonicity and convexity | ✓ | `convex_epi_of_monotone_regularSubdiff`, `convex_epi_of_monotone_subdiff` | |
| M2006 Prop 1.107(ii) | Sum rule with a strictly differentiable function | ✓ | `mem_subdiff_add_strict_iff` | Thm 16.13 |

## Chapter 5. Coderivatives of maximal monotone operators

| # | Statement | Status |
|---|---|---|
| 5.1–5.9 | Hypomonotonicity; coderivative criteria for global maximal monotonicity | ☐ |
| 5.10–5.17 | Strong local maximal monotonicity; strong metric regularity | ☐ |

## Chapter 6. Nondifferentiable and bilevel optimization

Sect. 6.1 is formalized in `Optimality/GeometricConstraints` (problems (6.1), (6.9)) and
`Optimality/Programming` (problem (6.11)). In (6.11) the functional data are indexed by one
finite type `K`: `φ : K → E → ℝ` (or `EReal` in Thm 6.5(i)), a cost index `k₀`, and a set
`Q ∌ k₀` of equality indices; the feasible set is `feasibleSet Q k₀ Ω φ` and the Lagrangian
`lagrangian φ λ = ∑ₖ λₖ φₖ`. "Lipschitz data" means all `φₖ` are `L`-Lipschitz on a common
neighborhood of `x₀`.

Sect. 6.2 is formalized in `Optimality/Bilevel` and the smooth part of Sect. 6.3 in
`Optimality/BilevelSmooth` (with `Subdifferential/NegConvexHull`). The bilevel data are
`f φ : E × F → ℝ`, `g : ι → E × F → ℝ` and `Ω : Set E` (`Ω = {x ∣ hⱼ(x) ≤ 0}` in Thm 6.21);
`lowerFeasible`, `lowerValue`, `lowerSolution` are `G`, `μ`, `S` of (6.29), (6.33), (6.30), and
`valueFeasible` is the feasible set of (6.34). Lower- and upper-level regularity (6.52)–(6.53)
are `LowerLevelRegular`, `UpperLevelRegular`.

| # | Statement | Status | Lean | Notes |
|---|---|---|---|---|
| 6.1 | Optimality conditions with a single geometric constraint | ✓ | (i): `neg_upperRegularSubdiff_subset_regularNormalCone`, `neg_upperRegularSubdiff_subset_normalCone`; (ii): `zero_mem_subdiff_add_normalCone_of_isLocalMinOn`, `exists_mem_subdiff_neg_mem_normalCone_of_isLocalMinOn` | (ii) assumes `φ ≠ ⊥` near `x₀` (in `EReal`, `⊥ + ⊤ = ⊥`) |
| 6.2 | Upper vs. lower subdifferential conditions | ◐ | (i): `neg_mem_regularNormalCone_of_hasFDerivAt`, `mem_upperRegularSubdiff_of_hasFDerivAt` | (ii)–(iv) are discussion and examples |
| 6.3 | DC optimization problems | ✓ | `isLocalMin_sub_iff_isLocalMinOn_epi`, `neg_upperRegularSubdiff_subset_normalCone_epi_iff`, `subdiff_subset_subdiff_of_isLocalMin_sub` | `φ₂ : E → ℝ` convex (so `∞ - ∞` never occurs); the equivalence uses continuity of `φ₂` at `x₀` and no convexity of `φ₁` |
| 6.4 | Optimality conditions with many geometric constraints | ✓ | (i): `neg_upperRegularSubdiff_subset_sum_normalCone`; (ii): `zero_mem_subdiff_add_sum_normalCone_of_isLocalMinOn` | |
| 6.5 | Lower subdifferential conditions via separate constraints | ✓ | (i): `exists_mem_normalCone_epi_graph`; (ii): `exists_multipliers_zero_mem_sum_separateSubdiff` | (i): `EReal` data, cost and inequality data l.s.c. around `x₀`, equality data continuous around `x₀`; (ii) is derived from Thm 6.10 and the sum rule |
| 6.6 | Equality constraints via symmetric subgradients | ✓ | `exists_multipliers_zero_mem_sum_symmSeparateSubdiff`, `symmSeparateSubdiff_of_mem` | |
| 6.7–6.9 | Examples | ☐ | | worked examples |
| 6.10 | Condensed lower subdifferential conditions | ✓ | `exists_multipliers_zero_mem_subdiff_lagrangian`, `exists_multipliers_zero_mem_subdiff_lagrangian_add_normalCone` | the book's appeal to "Thm 1.32 and its proof" is replaced by `mem_regularSubdiff_of_mem_regularNormalCone` and `mem_subdiff_of_mem_normalCone_constraintGraph` (normals to `ℰ`) |
| 6.11 | Abstract maximum principle | ✓ | `exists_multipliers_abstract_maximum_principle` | |
| 6.12 | Upper subdifferential conditions in nondifferentiable programming | ✓ | `exists_multipliers_upperRegularSubdiff`; `C¹` upper supports: `exists_contDiff_upper_support` | inner product spaces (where Thm 1.27(ii) is available) |
| 6.13 | Local solutions of optimistic and value function reformulations | ✓ | (i): `isLocalMinOn_valueFeasible_of_isLocalMinOn_optimisticValue`; (ii): `isLocalMinOn_optimisticValue_of_isLocalMinOn_valueFeasible` | `S̃(x) = {y ∈ S(x) ∣ f(x, y) = f_opt(x)}`: the book's `S̃ ⊆ S` can fail for its definition via (6.35); (ii) assumes the infimum in `f_opt` is attained near `x̄` |
| 6.14 | Partial calmness | ✓ | `PartiallyCalmWith`, `PartiallyCalm` | the perturbed constraint is written `μ(x) = φ(x, y) + ϑ` |
| 6.15 | Penalization via partial calmness | ✓ | `isLocalMinOn_penalizedObjective`, `partiallyCalmWith_of_isLocalMinOn_penalizedObjective` | the objective `penalizedObjective` of (6.40) is `+∞` where `μ = -∞` |
| 6.16 | Local weak sharp minima | ✓ | `IsLocalWeakSharpMin` | |
| 6.17 | Partial calmness from uniform weak sharp minima | ✓ | `partiallyCalm_of_uniform_weakSharp` | `S(x) ≠ ∅` near `x̄` (the book's standing assumption) is explicit; `κ = 2(ℓ + 1)/α` |
| 6.18 | Weak sharp minima from KKT and the kernel condition (6.46) | ✓ | `exists_weakSharp_of_kkt`, `isLocalWeakSharpMin_of_kkt` | local optimality of `z̄` is not needed |
| 6.19–6.20 | Examples | ☐ | | worked examples |
| 6.21 | Optimality conditions for smooth bilevel programs, I | ✓ | `exists_multipliers_smooth_bilevel_upper`; value function: `subdiff_lowerValue_subset`, `singularSubdiff_lowerValue_eq_zero`, `exists_lipschitzOnWith_lowerValue`; normals to `C¹` inequality systems: `normalCone_le_zero_subset`; `∂(-μ) ⊆ -co ∂μ`: `neg_mem_convexHull_subdiff_of_mem_subdiff_neg` | lower semicontinuity of `μ` around `x̄` is assumed (the book's "easy to see" only gives it at `x̄`); `S(x) ≠ ∅` near `x̄` is explicit; local optimality enters only through partial calmness at a feasible point |
| 6.22 | Difference rule for regular subgradients | ✓ | `add_mem_regularSubdiff_of_mem_regularSubdiff_sub`, `regularSubdiff_sub_subset`, `regularSubdiff_subset_of_isLocalMin_sub`; increment version: `regularSubdiff_subset_of_eventually_le` | |
| 6.23 | Optimality conditions for smooth bilevel programs, II | ✓ | `exists_multipliers_smooth_bilevel_regular` | uses the increment inequality from (6.40) directly instead of (6.63)–(6.64), so `G(x) ≠ ∅` near `x̄` is not needed |
| 6.24 | Example | ☐ | | worked example |
| 6.25–6.26 | Optimality conditions for Lipschitzian bilevel programs | ☐ | | the book leaves the proofs to Exercise 6.43; they need normals to Lipschitzian inequality systems (Thm 6.10-type qualification for `gph G`) and the Lipschitzian version of `subdiff_lowerValue_subset` |
| 6.27 | Remark: inner semicompactness | ☐ | | discussion |

## Clason–Valkonen topics outside [Mordukhovich 2018, Ch. 1–6]

| CV | Topic | Status |
|---|---|---|
| Ch 13 | Clarke subdifferential: Fermat principle (Thm 13.4), `C¹` (Thm 13.5), convex (Thm 13.8), calculus (Thm 13.20, 13.23), finite-dimensional characterization (Thm 13.26) | ◐ (finite dimensions: Fermat, `C¹`, convex, sum and scalar rules in `Subdifferential/Clarke`, see below; chain rules and the Rademacher characterization not yet) |
| Thm 16.10 | `∂_C F = cl co ∂_M F` for locally Lipschitz `F` | ✓ (finite dimensions) `clarkeSubdiff_eq_convexHull` |
| Ch 17 | `ε`-subdifferentials; fuzzy Fermat principle (Lemma 17.9) | ☐ |
| (18.4) | Clarke tangent cone; `T̂_C(x) = N_C(x)°` (Thm 18.15); normal regularity (Thm 18.24) | ☐ |
| Ch 20 | Graphical derivatives; `D̂*F = (DF)°+` (Cor 20.9) | ☐ |
| Ch 26 | Second-order optimality conditions | ☐ |
| Ch 28 | Stability; metric subregularity of convex subdifferentials (Thm 28.8) | ☐ |

## [Mordukhovich–Nam 2022], Ch. 7: the generalized gradient

| # | Statement | Status | Lean | Notes |
|---|---|---|---|---|
| Def 7.1(a) | generalized directional derivative `f°(x̄; v)` | ✓ | `clarkeDeriv` | `EReal`-valued upper limit, defined for every `f` |
| Def 7.21(a) | generalized gradient `∂̄f(x̄)` | ✓ | `clarkeSubdiff`, `mem_clarkeSubdiff_iff` | |
| Prop 7.8 | `\|f°(x̄; v)\| ≤ ℓ ‖v‖`, positive homogeneity | ✓ | `clarkeDeriv_le_mul_norm`, `neg_mul_norm_le_clarkeDeriv`, `clarkeDeriv_smul` | finite dimensions |
| Thm 7.10 | `f°(x̄; ·)` subadditive | ✓ | `clarkeDeriv_add_le` | finite dimensions |
| Prop 7.11 | `(-f)°(x̄; v) = f°(x̄; -v)` | ✓ | `clarkeDeriv_neg` | normed spaces |
| Thm 7.24 | `∂̄f(x̄)` nonempty, convex, compact, `‖x*‖ ≤ ℓ` | ✓ | `clarkeSubdiff_nonempty`, `convex_clarkeSubdiff`, `isClosed_clarkeSubdiff`, `isCompact_clarkeSubdiff`, `norm_le_of_mem_clarkeSubdiff` | convexity and closedness in normed spaces, the rest in finite dimensions; the closed-graph part (7.37) not yet |
| Thm 7.31 | full duality `f°(x̄; v) = max {⟨x*, v⟩ \| x* ∈ ∂̄f(x̄)}` | ✓ | `clarkeDeriv_eq_iSup_clarkeSubdiff`, `exists_mem_clarkeSubdiff_eq` | finite dimensions, via Thm 7.69 instead of Hahn–Banach |
| Prop 7.5 | `C¹` (strictly differentiable) functions | ✓ | `clarkeSubdiff_eq_singleton_of_hasStrictFDerivAt` | finite dimensions |
| after Def 7.21, Prop 7.4 | convex functions | ✓ | `clarkeSubdiff_eq_of_convexOn` | finite dimensions |
| Thm 7.32 | sum rule (7.44) | ◐ | `clarkeSubdiff_add_subset`, `clarkeSubdiff_add_eq_of_hasStrictFDerivAt` | the inclusion, and equality when one term is strictly differentiable; equality under directional regularity not yet |
| (7.54) | `∂̄(αf)(x̄) = α ∂̄f(x̄)` | ✓ | `clarkeSubdiff_neg`, `clarkeSubdiff_const_mul` | |
| — | Fermat's rule at local minima and maxima | ✓ | `zero_mem_clarkeSubdiff_of_isLocalMin`, `zero_mem_clarkeSubdiff_of_isLocalMax` | |
| Ex 7.148 | `∂f(x̄) ⊆ ∂̄f(x̄)` | ✓ | `subdiff_subset_clarkeSubdiff`, `regularSubdiff_subset_clarkeSubdiff`, `subdiff_neg_subset_neg_clarkeSubdiff` | normed spaces |
| Thm 7.69 | `∂̄f(x̄) = co ∂f(x̄)` in `ℝⁿ` (7.89); `f°(x̄; v) = sup {⟨x*, v⟩ \| x* ∈ ∂f(x̄)}` (7.91) | ✓ | `clarkeSubdiff_eq_convexHull`, `clarkeDeriv_eq_iSup`, `exists_mem_subdiff_eq_clarkeDeriv` | proof via the mean value inequality (M Cor. 4.14(ii)) and robustness of `∂f` (`eventually_forall_mem_subdiff_apply_le`); the weak* closure version in Asplund spaces is out of scope |
| Def 7.1(b), 7.21(b), Prop 7.2–7.3 | contingent derivative and subdifferential, directional regularity | ☐ | | |
| Thm 7.33–7.36 | chain rules, maxima | ◐ | `clarkeDeriv_comp_fst`, `clarkeSubdiff_comp_fst`, `clarkeSubdiff_sub_comp_fst` | only composition with the projection `E × F → E`; the general chain rules and maxima not yet |
| Sect. 7.4–7.6 | Lebourg mean value theorem, strict differentiability, Rademacher representation | ☐ | | |

## [Mordukhovich 2024], Ch. 1: basic concepts of second-order analysis

M24 = [Mordukhovich 2024]. Statements are numbered as in the body of the book; from 1.68 on, the
numbers in its *List of Statements* differ from those in the text (e.g. the list calls Def 1.73
"1.74"). The book works in Banach, Asplund or Hilbert spaces; here everything is finite
dimensional, and Sect. 1.3.3 uses real inner product spaces. Worked examples (1.48, 1.49, 1.55,
1.75, …) are not formalized. Files: `SecondOrder/Basic`, `SecondOrder/ProxRegular`,
`SecondOrder/Moreau`, `SecondOrder/GraphicalDerivative`.

| # | Statement | Status | Lean | Notes |
|---|---|---|---|---|
| Def 1.46(i)–(ii) | basic second-order subdifferential `∂²φ(x̄, v̄)` | ✓ | `secondOrderSubdiff` (`Coderivative/SecondOrder`) | normal and mixed versions agree in finite dimensions |
| Def 1.46(iii) | combined second-order subdifferential `∂̆²φ` (1.62) | ✓ | `combinedSecondOrderSubdiff`, `combinedSecondOrderSubdiff_subset_secondOrderSubdiff` | |
| Prop 1.47 | `C²` functions: `∂̆²φ(x̄)(u) = ∂²φ(x̄)(u) = {∇²φ(x̄)u}` | ✓ | `combinedSecondOrderSubdiff_of_hasFDerivAt`, `secondOrderSubdiff_of_hasFDerivAt` | the combined part only needs `∇φ` differentiable at `x̄` |
| Prop 1.50 | `C^{1,1}` functions: `∂̆²φ(x̄)(u) = ∂̂⟨u, ∇φ⟩(x̄)`, `∂²φ(x̄)(u) = ∂⟨u, ∇φ⟩(x̄)` | ✓ | `combinedSecondOrderSubdiff_of_lipschitz`, `secondOrderSubdiff_of_lipschitz` | via `regularCoderiv_eq_regularSubdiff_comp` (M24 Thm 1.34) |
| Prop 1.51 | second-order sum rules (1.64), (1.65) | ✓ | `secondOrderSubdiff_add`, `combinedSecondOrderSubdiff_add` | (1.64) assumes `∇φ₁` strictly differentiable around `x̄` with derivative continuous at `x̄` (book: strictly differentiable at `x̄`); (1.65) as in the book |
| Def 1.52 | partial second-order subdifferentials (1.66)–(1.68) | ✓ | `partialSubdiff`, `partialSecondOrderSubdiff`, `combinedPartialSecondOrderSubdiff` | values in `(E × F)*` |
| Prop 1.53 | partial second-order subdifferentials of `C²` functions | ✓ | `partialSecondOrderSubdiff_of_hasFDerivAt`, `combinedPartialSecondOrderSubdiff_of_hasFDerivAt` | |
| Prop 1.54 | partial sum rules (1.69), (1.70) | ✓ | `partialSecondOrderSubdiff_add`, `combinedPartialSecondOrderSubdiff_add` | same change of hypotheses as Prop 1.51 |
| Def 1.56, 1.57 | prox-regularity, subdifferential continuity | ✓ | `ProxRegularFor`, `SubdiffContinuousFor`, `ContinuouslyProxRegularFor` (`WellPosedness/ProxRegular`) | M Def 3.27; the library asks for `φ(x) ≤ φ(x̄) + ε` where the book asks for `\|φ(x) − φ(x̄)\| ≤ ε` |
| Prop 1.58 | convex functions are continuously prox-regular | ✓ | `continuouslyProxRegularFor_of_convex` | |
| Def 1.59 | piecewise linear-quadratic and piecewise linear functions | ✓ | `IsPolyhedral`, `IsPLQ`, `IsPiecewiseLinear`, `IsPiecewiseLinear.isPLQ` (`SecondOrder/PLQ`) | any normed space; polyhedral = finite intersection of closed half-spaces; `A` as a symmetric continuous bilinear form |
| Def 1.60 | amenable compositions | ◐ | `AmenableAt`, `StronglyAmenableAt`, `AmenableAtOfClass` | M Def 3.23; strictly and fully amenable functions not yet |
| Thm 1.61 | strictly amenable functions are continuously prox-regular | ◐ | `continuouslyProxRegularFor_of_C11` | only `C^{1,1}` functions |
| (1.80) | proximal subdifferential `∂_P φ` | ✓ | `proxSubdiff`, `proxSubdiff_subset_regularSubdiff`, `proxSubdiff_subset_subdiff` | |
| Def 1.62 | `φ`-attentive `ε`-localization (1.76) | ✓ | `attentiveLocalization` | |
| Def 1.63 | local monotonicity, hypomonotonicity | ✓ | `LocallyMonotoneAt`, `LocallyHypomonotoneAt` (`WellPosedness/Monotone`), `IsHypomonotoneOn`, `globallyMonotone_iff_isHypomonotoneOn` | |
| Lemma 1.64 | parameter interplay for quadratic perturbations | ◐ | inside `ProxRegularFor.of_isHypomonotoneOn` | used inline, with other constants (`r ≥ ρ + 4α + 8`); not stated separately |
| Thm 1.65 | prox-regularity via hypomonotonicity of attentive localizations | ✓ | `ProxRegularFor.mem_proxSubdiff`, `ProxRegularFor.isHypomonotoneOn_attentiveLocalization`, `ProxRegularFor.of_isHypomonotoneOn`, `proxRegularFor_iff_isHypomonotoneOn`, `proxRegularFor_iff_isHypomonotoneOn_subdiff`, `proxRegularFor_iff_locallyHypomonotoneAt` | finite-dimensional inner product spaces; (ii) ⇒ (i) needs only the basic localization, by the argument of Ex 1.121 instead of Ekeland's principle and the fuzzy sum rule |
| Def 1.66, 1.67 | Moreau envelope, proximal mapping and their local versions (1.85)–(1.88) | ✓ | `proxObjective`, `moreauEnvelope`, `localMoreauEnvelope`, `proximalMap`, `localProximalMap` | |
| Lemma 1.68 | estimates for Moreau envelopes | ✓ | `norm_le_of_proxObjective_le`, `mem_closedBall_of_proxObjective_le`, `moreauEnvelope_eq_localMoreauEnvelope`, `proximalMap_eq_localProximalMap`, `coe_le_moreauEnvelope_of_quadratic` | `φ(x) ≥ −(r̄/2)‖x‖²` for all `x` in place of the strict (1.89); (1.91) for every radius `ε ≥ 2μγ + √(2λμρ)` |
| Lemma 1.69 | `(I + λT)⁻¹` single-valued and Lipschitz for hypomonotone `T` | ✓ | `IsHypomonotoneOn.norm_sub_le` | constant `(1 − λρ)⁻¹` |
| Thm 1.70 | proximal mappings of prox-regular functions | ✓ | `ProxRegularFor.exists_proximalMap` | **corrected**: the book assumes `φ` l.s.c. and minorized by a quadratic *around* `x̄`, but `P_λφ` is a global argmin and is empty when `φ` is unbounded below far away; we assume prox-boundedness `φ(x) ≥ a − b‖x − x̄‖²` for all `x` (and global l.s.c. for simplicity). `P_λφ` is `2`-Lipschitz on `U_λ` and equals `(I + λT_ε)⁻¹` there |
| Thm 1.71 | `e_λφ` is `C^{1,1}` with `∇e_λφ = λ⁻¹(I − P_λφ)` (1.94) | ✓ | `ProxRegularFor.exists_moreauEnvelope` | hypotheses as in Thm 1.70; the gradient is `3/λ`-Lipschitz |
| Cor 1.72 | `∂φ` graphically Lipschitzian of dimension `n` | ✓ | `ContinuouslyProxRegularFor.graphicallyLipschitzianAt` | `GraphicallyLipschitzianAt` (GO Def 3.16) for `subdiffMap φ`, transformation `(x, v) ↦ (x + λv, v)`; proof via Thm 1.70 for `φ` plus the indicator of a small closed ball |
| Def 1.73 | subgradient graphical derivatives (1.96), (1.97) | ✓ | `graphDeriv`, `subgradGraphDeriv`, `regularSubgradGraphDeriv`, `regularSubgradGraphDeriv_subset` | graphical derivative (1.39) via `contingentCone`; sum rule (1.41) is `graphDeriv_add` |
| Prop 1.74 | `C²` functions (1.98) | ✓ | `subgradGraphDeriv_of_hasFDerivAt`, `regularSubgradGraphDeriv_of_hasFDerivAt`, `secondOrderSubdiff_eq_subgradGraphDeriv` | |
| Prop 1.76 | sum rules (1.100) | ✓ | `subgradGraphDeriv_add`, `regularSubgradGraphDeriv_add` | the result is `f'' u`, so no symmetry of `∇²φ₁(x̄)` is needed |
| Def 1.77 | directional differentiability (1.101) | ✓ | `HasDirDerivAt`, `DirDifferentiableAt`, `HasFDerivAt.hasDirDerivAt` (`SecondOrder/C11`) | any normed spaces; no Lipschitz hypothesis in the definition |
| Def 1.78 | set convergence (1.102)–(1.104) | ✓ | `IsSetLimit`, `mem_outerLimit_atTop_iff`, `mem_innerLimit_atTop_iff`, `innerLimit_subset_outerLimit_atTop` (`SecondOrder/EpiConvergence`) | along any filter, via `outerLimit`, `innerLimit`; nonemptiness is not part of the definition |
| Def 1.79 | epi-convergence | ✓ | `EpiTendsto`, `EpiTendsto.epi_eq` | |
| Def 1.80 | epi-differentiability | ✓ | `diffQuot`, `EpiDifferentiableAt` | quotients (1.56) in `EReal` |
| (1.105), Lemma 1.81 | proximal normal cone; proximal-normal approximation under set convergence | ✓ | `proxNormalCone`, `proxNormalCone_subset_regularNormalCone`, `toDual_smul_sub_mem_proxNormalCone`, `exists_tendsto_proj_of_isSetLimit`, `exists_tendsto_proxNormalCone` | closed nonempty sets in finite-dimensional inner product spaces; `γ ≥ 0` in (1.105) |
| Lemma 1.82 | local convexification of `C^{1,1}` functions (1.108), (1.109) | ◐ | `convexOn_add_sq_of_lipschitzOnWith`, `convexOn_closedBall_add_sq`, `subgradGraphDeriv_add_sq`, `convexOn_of_monotone_fderiv` | (1.108) and the graphical-derivative half of (1.109); the `∂²` half of (1.109) is not stated |
| Lemma 1.83 | Rademacher's theorem | ✓ | Mathlib: `LipschitzWith.ae_differentiableAt`, `LipschitzOnWith.ae_differentiableWithinAt_of_mem` | |
| Thm 1.84 | `∂²_D φ(x̄)(u) ⊆ ∂²φ(x̄)(u)` for `C^{1,1}` functions with directionally differentiable gradient (1.111) | ✓ | `subgradGraphDeriv_subset_secondOrderSubdiff`, `graphDeriv_subset_of_hasDirDerivAt`, `dirDeriv_mem_subdiff` | finite-dimensional inner product spaces; different proof: `∂²_D φ(x̄)(u) ⊆ {(∇φ)'(x̄; u)}`, and `(∇φ)'(x̄; ·)` is a gradient (limit of blow-ups), symmetric and Euler-homogeneous at its points of differentiability (Rademacher), whose gradients are approximated by regular subgradients of the blow-ups; no Lemma 1.81 |
| Def 1.85 | proto-differentiability | ✓ | `ProtoDifferentiableAt`, `protoDifferentiableAt_invMap_iff` | via geometric derivability (Def 1.9) of the graph |
| Thm 1.86 | `∂²_D φ(x̄\|v̄)(u) ⊆ ∂²φ(x̄\|v̄)(u)` for continuously prox-regular `φ` with proto-differentiable `∂φ` (1.116) | ✓ | `ContinuouslyProxRegularFor.subgradGraphDeriv_subset_secondOrderSubdiff`, `coderiv_shear_iff`, `graphDeriv_shear_iff`, `ProtoDifferentiableAt.of_shear`, `dirDifferentiableAt_of_geometricallyDerivableAt`, `ContinuouslyProxRegularFor.exists_local_moreau` (`SecondOrder/ProtoDiff`) | finite-dimensional inner product spaces; (1.118) for a general shear `(x, y) ↦ (x + By, y)`; no prox-boundedness needed (localization as in Cor 1.72) |
| Cor 1.87 | fully amenable functions | ☐ | | needs Thm 1.61 for fully amenable functions and Ex 1.139(ii) |
| Def 1.43 | subderivative `dφ(x̄)` (1.56)–(1.57) | ✓ | `diffQuot`, `subderiv`, `subderiv_of_hasFDerivAt` (`SecondOrder/SecondSubderiv`) | Sect. 1.1 preliminary needed for Sect. 1.5; semidifferentiability is used inside `TwiceSemidifferentiableAt` |
| Def 1.88 | second subderivatives `d²φ(x̄, v)`, `d²φ(x̄)` (1.119)–(1.122) | ✓ | `secondDiffQuot`, `secondDiffQuot'`, `secondSubderiv`, `secondSubderiv'`, `secondDiffQuot'_eq` | |
| Def 1.89 | twice epi-differentiability, twice semidifferentiability | ✓ | `TwiceEpiDifferentiableAt`, `TwiceSemidifferentiableAt` | (ii) asks for a finite first-order limit |
| Prop 1.90 | twice differentiable functions | ✓ | `secondSubderiv_of_hasFDerivAt`, `secondSubderiv'_of_hasFDerivAt`, `twiceEpiDifferentiableAt_of_hasFDerivAt`, `tendsto_secondDiffQuot_dir_of_hasFDerivAt`, `abs_taylor_two_le` | twice Fréchet differentiable at `x̄` (gradient near `x̄`, differentiable at `x̄`); any normed space |
| (1.125), Thm 1.91 | critical cone; second subderivatives of piecewise linear-quadratic convex functions (1.126)–(1.128) | ✓ | `criticalCone`; `LocalPLQ`, `IsPolyhedral.exists_cone`, `IsPLQ.exists_localPLQ`, `LocalPLQ.subderiv_of_mem`, `LocalPLQ.secondSubderiv'_of_mem`, `LocalPLQ.mem_criticalCone_iff`; `IsPLQ.twiceEpiDifferentiableAt`, `IsPLQ.exists_eq_add_subderiv_add`, `IsPLQ.tendsto_secondDiffQuot'`, `IsPLQ.secondSubderiv'_nonneg`, `IsPLQ.isPLQ_secondSubderiv'`, `IsPLQ.tendsto_secondDiffQuot`, `IsPLQ.secondSubderiv_eq`, `IsPLQ.convex_epi_secondSubderiv`, `IsPLQ.isPLQ_secondSubderiv`, `IsPLQ.exists_criticalCone_eq` (`SecondOrder/PLQ`) | any normed space; via a local linear-quadratic model on polyhedral cones; (1.126), the limit in (1.127) and the structure of `d²φ(x̄)` need no convexity; `K_φ(x̄, v)` as a finite union of polyhedral cones (its polyhedrality as a convex set not yet); the second directional derivative `φ''(x̄; w)` of (1.127) is not defined |
| Prop 1.93 | second subderivatives of convex functions | ✓ | `secondSubderiv_nonneg_of_convex`, `convex_epi_secondSubderiv`, `secondDiffQuot_combo_le` | the convexity part only uses convexity of `φ` and finiteness of `φ(x̄)` |
| Lemma 1.94 | subdifferentials and Moreau envelopes of second-order quotients (1.130), (1.131) | ✓ | `subdiff_half_secondDiffQuot`, `mem_subdiff_coe_mul_iff`, `moreauEnvelope_scale`, `proximalMap_scale`, `moreauEnvelope_half_secondDiffQuot`, `proximalMap_half_secondDiffQuot` | (1.130) in finite dimensions; (1.131) stated for `w ↦ t⁻²φ(tw)` and then for `Δ²_tφ(0, 0)/2` |
| Lemma 1.95 | resolvents of monotone operators | ✓ | `resolventMap`, `isMaximalMonotoneOp_iff_resolventMap`, `IsMaximalMonotoneOp.resolventMap_nonempty` (`SCD/Minty`), `IsMonotoneOp.isMonotoneOp_resolventMap`, `IsMonotoneOp.norm_sub_le_of_mem_resolventMap`, `IsMonotoneOp.isMaximalMonotoneOp_of_resolventMap`, `IsMonotoneOp.exists_resolventMap_eq_singleton`, `isMaximalMonotoneOp_of_continuous` (`SecondOrder/CyclicMonotone`) | finite dimensions; full domain via Minty's theorem (`SCD/Minty`) |
| Def 1.96, Lemma 1.97 | cyclical monotonicity; maximal cyclically monotone = convex subdifferential, unique up to a constant | ✓ | `CyclicallyMonotone`, `MaximalCyclicallyMonotone`, `cyclicallyMonotone_subdiff_of_convex`, `rockafellarFun`, `mem_subdiff_rockafellarFun`, `maximalCyclicallyMonotone_iff`, `exists_eq_add_const_of_subdiff_eq`, `exists_mem_dom_subdiff_near` | finite dimensions; uniqueness via Moreau envelopes; maximality of `∂φ` via `globallyMaximalMonotone_subdiff_of_convex` for all proper l.s.c. convex `φ` |
| Thm 1.98, Cor 1.99, Cor 1.101 | twice epi-differentiability ⇔ proto-differentiability for prox-regular functions; fully amenable functions; proximal mappings | ◐ | `twiceEpiDifferentiableAt_iff_epiTendsto`, `EpiTendsto.coe_mul`, `TwiceEpiDifferentiableAt.epiTendsto_half`, `TwiceEpiDifferentiableAt.mem_proximalMap_of_tendsto`, `TwiceEpiDifferentiableAt.tendsto_inv_smul_of_mem_proximalMap`, `TwiceEpiDifferentiableAt.exists_proximalMap_half_secondSubderiv_eq_singleton`, `TwiceEpiDifferentiableAt.exists_tendsto_inv_smul_proximalMap`, `ProxRegularFor.exists_proxObjective_growth`, `ProxRegularFor.exists_tendsto_inv_smul_proximalMap`, `shiftTilt`, `mem_proximalMap_shiftTilt_iff`, `ProxRegularFor.exists_tendsto_inv_smul_sub_proximalMap` (`SecondOrder/TwiceEpiProx`), `geometricallyDerivableAt_graph_of_tendsto`, `ContinuouslyProxRegularFor.eventually_mem_subdiff_iff`, `ContinuouslyProxRegularFor.protoDifferentiableAt_subdiff` (`SecondOrder/TwiceEpiProto`), `tendsto_second_quot_of_hasDirDerivAt`, `ContinuouslyProxRegularFor.exists_dirDifferentiableAt_proximalMap`, `ContinuouslyProxRegularFor.exists_tendsto_moreauEnvelope_second_quot` (`SecondOrder/EnvelopeExpansion`), `twiceEpiDifferentiableAt_zero_of_moreauEnvelope`, `ContinuouslyProxRegularFor.twiceEpiDifferentiableAt_of_protoDifferentiableAt`, `ContinuouslyProxRegularFor.twiceEpiDifferentiableAt_iff_protoDifferentiableAt` (`SecondOrder/ProtoTwiceEpi`), `ContinuouslyProxRegularFor.exists_twiceEpiDifferentiableAt_iff_proximalMap`, `ContinuouslyProxRegularFor.exists_isSemiderivative_proximalMap` (`SecondOrder/ProxSemidiff`), `moreauEnvelope_half_secondDiffQuot_shift`, `ProxRegularFor.exists_twiceEpiDifferentiableAt_moreauEnvelope` (`SecondOrder/EnvelopeTwiceEpi`) | the equivalence of Thm 1.98 is done: for `φ` continuously prox-regular at `x̄` for `v̄`, `φ` is twice epi-differentiable at `x̄` for `v̄` iff `∂φ` is proto-differentiable at `(x̄, v̄)` (no global assumptions). Of Cor 1.101, for `φ` l.s.c., prox-bounded and continuously prox-regular at `x̄` for `v̄` (any `v̄`, not only `0`) and small `λ`: twice epi-differentiability of `φ` ⇔ (b) proto-differentiability of `P_λφ` at `(x̄ + λv̄, x̄)` ⇔ (c) semidifferentiability of `P_λφ` (Def 1.100), and under these the semiderivative is `P_λ(d²φ(x̄, v̄)/2)`, a single-valued mapping; proto-differentiability of `∂φ` also gives the second-order expansion of `e_λφ` at `x̄ + λv̄`. Part (a), one implication: if `φ` is l.s.c., prox-bounded, prox-regular and twice epi-differentiable at `x̄` for `v̄`, then `e_λφ` is twice epi-differentiable at `x̄ + λv̄` for `v̄` and `d²(e_λφ)/2 = e_λ(d²φ/2)` (first formula). Still open: formula (1.135) `D(∂φ) = ∂(d²φ/2)`; the converse implication of part (a) (needs continuous prox-regularity of `e_λφ` near `x̄ + λv̄`, a `C^{1,1}` function); Cor 1.99 needs Ex 1.139(ii) |
| Def 1.100 | semidifferentiability of set-valued mappings (1.138) | ✓ | `IsSemiderivative`, `SemidifferentiableAt'` | |
| Ex 1.133 | analytic description of epi-convergence | ✓ | `epiTendsto_atTop_iff`, `epiTendsto_iff`, `outerLimit_epi_subset_iff`, `epi_subset_innerLimit_iff`, `isSetLimit_iff_subset` (`SecondOrder/EpiAnalytic`) | also along a countably generated filter, with the lower limit along `l ×ˢ 𝓝 x`; points with `φ₀(x) = -∞` by a diagonal sequence |
| Ex 1.134 | convexity under set and epi-convergence | ◐ | `convex_innerLimit`, `EpiTendsto.convex_epi` | (i), (iii); the counterexample of (ii) not formalized |
| Ex 1.135 | epi-convergence via Moreau envelopes | ✓ | `EpiTendsto.tendsto_moreauEnvelope`, `EpiTendsto.tendsto_moreauEnvelope_apply`, `epiTendsto_of_tendsto_moreauEnvelope`, `tendsto_moreauEnvelope_of_seq`; `EpiTendsto.outerLimit_graph_proximalMap_subset`, `EpiTendsto.tendsto_of_mem_proximalMap` (`SecondOrder/EpiAnalytic`) | (i): the direct part gives continuous convergence (in `EReal`, proper spaces; for a common minorant `-(r/2)‖·‖²` and `λr < 1`, so every `λ > 0` for nonnegative functions), the converse needs the common minorant `-(r/2)‖·‖²` (eventually along the filter), `φ₀` l.s.c. and pointwise convergence for small `λ`; properness not needed. (ii), (iii): for proximal points `p ∈ P_λφ(u)` instead of gradients `λ⁻¹(u - p)` of envelopes (which need not exist without convexity); convergence when `P_λφ₀(u)` has at most one point |
| Ex 1.136 | `e_λφ(u) ↑ φ(u)` as `λ ↓ 0` | ✓ | `tendsto_moreauEnvelope_nhdsGT_zero`, `moreauEnvelope_anti` | `φ ≥ 0` l.s.c. at `u`; any normed space; `tendsto_moreauEnvelope_nhdsGT_zero_of_ge` for `φ ≥ -(r/2)‖·‖²` |
| Ex 1.139 | properties of proto-differentiable mappings | ◐ | `protoDifferentiableAt_iff_isSetLimit`, `geometricallyDerivableAt_iff_isSetLimit` | (iii) only; (i) graphical regularity and (ii) fully amenable functions not yet |

## SCD mappings [Gfrerer–Outrata 2022]

Setting: `E` a finite-dimensional real inner product space, `F : E → Set E`, subspaces of
`E × E` as `Submodule ℝ (E × E)`. GO = [Gfrerer–Outrata 2022], GMOV = [Gfrerer–Mandlmayr–Outrata–Valdman 2023],
GO24 = [Gfrerer–Outrata 2024].
`E × E` carries the sup norm in Lean; estimates are stated with norms on `E`, and the constant of
GO Prop 5.3 is `max 1 ‖C_L‖` instead of `√(n(1+‖C_L‖²))`.

| # | Statement | Status | Lean | Notes |
|---|---|---|---|---|
| GO Sect. 3, (8) | metric `d(L₁, L₂) = ‖P₁ − P₂‖` on subspaces | ✓ | `grassProj`, `grassDist`, `GrassTendsto`, `grassDist_triangle`, `grassTendsto_iff` (`SCD/Grassmannian`) | projections computed in the Euclidean model `toEuclidean` |
| GO Lemma 3.1 | compactness; inner/outer limits; limits keep the dimension | ✓ | `exists_grassTendsto_subseq`, `GrassTendsto.exists_tendsto`, `GrassTendsto.outerLimit_subset`, `grassTendsto_of_outerLimit_subset`, `GrassTendsto.finrank_eq` | |
| GO (15), p. 10 | adjoint subspace `L*`; `(L*)* = L`; `dim L* = 2n − dim L`; continuity of `L ↦ L*` | ✓ | `adjointSubspace`, `mem_adjointSubspace_iff`, `adjointSubspace_adjointSubspace`, `finrank_adjointSubspace`, `GrassTendsto.adjointSubspace` (`SCD/Adjoint`) | the isometry property is replaced by continuity |
| GO Lemma 3.11 proof | `(gph A)* = gph Aᵀ` | ✓ | `adjointSubspace_graph` | |
| GO Def 3.3 | `O_F`, `𝒮F`, SCD property at/around, SCD mapping | ✓ | `GraphicallySmoothAt`, `tangentSubspace`, `scDeriv`, `HasSCDPropertyAt`, `HasSCDPropertyAround`, `IsSCDMapping` (`SCD/Basic`) | |
| GO Remark 3.4 | `gph D̂*F = T*` on `O_F` | ✓ | `GraphicallySmoothAt.mem_adjoint_tangentSubspace_iff`, `GraphicallySmoothAt.mem_regularCoderiv_iff` | |
| GO Remark 3.5 | `𝒮*F = {L* \| L ∈ 𝒮F}` | ✓ | `scCoderiv` (definition), `mem_scCoderiv_iff` | the limit description of the paper is a theorem |
| GO Lemma 3.6 | SCD property at `p` iff `p ∈ cl O_F` | ✓ | `hasSCDPropertyAt_iff_mem_closure` | |
| GO Lemma 3.7 | `⋃ 𝒮*F ⊆ gph D*F` | ✓ | `toDual_mem_coderiv_of_mem_scCoderiv` | |
| GO Def 3.8, Lemma 3.10 | `T♯`, `D♯F`; `⋃ 𝒮F ⊆ gph D♯F` | ✓ | `sharpTangentCone`, `sharpDeriv`, `mem_sharpTangentCone_of_mem_scDeriv` | |
| GO Lemma 3.2 | tangent cone of a graph at differentiability points; calm + graphically smooth ⇒ differentiable | ✓ | `contingentCone_graph_of_hasFDerivAt`, `graphicallySmoothAt_of_hasFDerivAt`, `differentiableAt_of_graphicallySmoothAt`, `graphicallySmoothAt_iff_differentiableAt` (`SCD/SingleValued`) | calmness as a hypothesis |
| GO Lemma 3.11 | `𝒮f(x) ⊇ {gph A \| A ∈ ∂_B f(x)}`, equality and SCD for Lipschitz `f` | ✓ | `bSubdiff`, `grassTendsto_graph`, `graph_mem_scDeriv_of_mem_bSubdiff`, `graph_adjoint_mem_scCoderiv_of_mem_bSubdiff`, `mem_scDeriv_iff_of_lipschitzOnWith`, `mem_scCoderiv_iff_of_lipschitzOnWith` | |
| GO Remark 3.12 | Lipschitz maps are SCD (Rademacher) | ✓ | `mem_closure_differentiableAt`, `hasSCDPropertyAround_of_lipschitzOnWith`, `LipschitzWith.isSCDMapping`, `Differentiable.isSCDMapping` | |
| GO Lemma 3.13 | robustness `𝒮F(p) = Lim sup 𝒮F(q)` | ✓ | `mem_scDeriv_of_tendsto`, `mem_scDeriv_iff_exists_seq`, `mem_scCoderiv_of_tendsto`, `hasSCDPropertyAt_of_tendsto` | |
| GO Prop 3.14 | `C¹` change of variables, (20) | ✓ | `scDeriv_preimage`, `scDeriv_eq_image_symm`, `hasSCDPropertyAt_iff_of_preimage`, `scDeriv_image_linear` (`SCD/Calculus`); local form `scDeriv_preimage_of_inter_eq` (`SCD/GraphLipschitz`) | the adjoint formula (21) for general `Φ` is not yet stated |
| GO Prop 3.15 | `F + h`, (22), (23) | ✓ | `scDeriv_add`, `scDeriv_add_of_contDiffAt`, `hasSCDPropertyAt_add_iff`, `scCoderiv_add` | |
| GO Def 3.16, Remark 3.18 | graphically Lipschitzian mappings; smooth points | ✓ | `IsGraphLipschitzTransform`, `GraphicallyLipschitzianAt`, `IsGraphLipschitzTransform.graphicallySmoothAt_iff` (`SCD/GraphLipschitz`) | dimension `n`; invertible `∇Φ` on `W` instead of `C¹` inverse |
| GO Prop 3.17 | graphically Lipschitzian ⇒ SCD around, (24a) | ◐ | `IsGraphLipschitzTransform.scDeriv_eq`, `.mem_scDeriv_iff`, `.mem_scCoderiv_iff`, `GraphicallyLipschitzianAt.hasSCDPropertyAround` | (24b) as adjoints of (24a), not in the explicit `S_n ∇Φᵀ S_nᵀ` form |
| GO Cor 3.19 | `F⁻¹` with Lipschitz localization plus `C¹` `h`, (25) | ✓ | `HasLipschitzInvLocalization`, `graphicallyLipschitzianAt_of_add`, `mem_scDeriv_iff_of_add`, `hasSCDPropertyAround_of_add` | |
| GMOV Lemma 3.7 | graphically Lipschitzian maps: `gph F` geometrically derivable on `O_F`, tangent subspaces of dimension `n`, near the point | ✓ | `IsGraphLipschitzTransform.finrank_eq_of_coe_eq_contingentCone`, `IsGraphLipschitzTransform.geometricallyDerivableAt`, `GraphicallyLipschitzianAt.exists_nhds_derivable_finrank` (`SCD/Derivable`) | via `geometricallyDerivableAt_graph_of_hasFDerivAt` (cf. [Rockafellar–Wets, Prop. 8.41]) and transfer along `Φ` |
| GMOV Lemma 3.4, Prop 3.5 | product rule (3.6)–(3.10), with equality | ✓ | `contingentCone_prod_eq`, `graphicallySmoothAt_prodMap_iff`, `prodSubspace_mem_scDeriv`, `prodSubspace_mem_scCoderiv`, `IsSCDMapping.prodMap`, `scDeriv_prodMap`, `scCoderiv_prodMap` (`SCD/Product`) | two factors, on `WithLp 2 (E₁ × E₂)`; `GeometricallyDerivableAt` follows GMOV Def 2.1 |
| GO Def 3.21 | firmly nonexpansive maps and matrices; derivatives and `∂_B` elements of firm maps are firm | ✓ | `IsFirmlyNonexpansive`, `IsFirmlyNonexpansiveOp`, `isFirmlyNonexpansiveOp_of_mem_bSubdiff` (`SCD/Monotone`) | |
| GO p. 15 | Minty parametrization `Φ(x, y) = (x + y, x)`; resolvent of a monotone map is firmly nonexpansive | ✓ | `mintyMap`, `mintySubspace`, `adjointSubspace_mintySubspace`, `resolvent`, `IsMonotoneOp.isFirmlyNonexpansive_resolvent`, `IsMonotoneOp.graph_eq_image_resolvent` | |
| GO Def 3.20, Prop 3.22 | (locally) maximally monotone maps are SCD; `L = rge(B, I − B)`, `L* = rge(Bᵀ, I − Bᵀ)` with `B` firm | ✓ | `IsMonotoneOp.isSCDMapping`, `IsMonotoneOp.mem_scDeriv_iff`, `IsMonotoneOp.mem_scCoderiv_iff`, `IsMonotoneOp.exists_firm_of_mem_scDeriv` (`SCD/Monotone`), `IsMaximalMonotoneOp.isSCDMapping` (`SCD/Minty`), `IsMaximalMonotoneOn`, `IsLocallyMaximalMonotoneAt`, `IsMonotoneOp.exists_isMaximalMonotoneOp_ge`, `IsMaximalMonotoneOn.exists_isMaximalMonotoneOp`, `IsLocallyMaximalMonotoneAt.scd` (`SCD/LocalMonotone`) | Def. 3.20 as in the paper (without `p ∈ gph F`); maximally monotone extension by Zorn's lemma [Rockafellar–Wets, Prop. 12.6], then Minty's theorem; the graphically Lipschitzian statement with `Φ(x, y) = (x + y, x)` is not stated separately |
| GO Cor 3.23, 3.24 | locally maximally hypomonotone maps; density version | ✓ | `IsLocallyMaximalHypomonotoneAt`, `IsLocallyMaximalHypomonotoneAt.scd`, `isSCDMapping_of_dense` (`SCD/LocalMonotone`) | |
| GO Cor 3.28 | `∂φ` of a proper lsc convex `φ` is SCD; `L = rge(B, I − B)`, `B` symmetric psd, `‖B‖ ≤ 1`, `L* = L` | ✓ | `subdiffMap`, `isSCDMapping_subdiffMap`, `exists_symm_of_mem_scDeriv_subdiffMap`, `adjointSubspace_eq_of_mem_scDeriv_subdiffMap`, `scCoderiv_subdiffMap` | `rge(I + ∂φ) = E` via the proximal point; symmetry via the Moreau envelope (`hasFDerivAt_moreauEnv`); also [Gfrerer–Outrata 2022b, Thm 3.6] |
| GMOV Prop 3.5 + Lemma 3.7 | products with a graphically Lipschitzian factor: SCD, with equality in (3.8)–(3.10) | ✓ | `IsSCDMapping.prodMap_of_graphicallyLipschitzian_left`, `scDeriv_prodMap_of_graphicallyLipschitzian_left`, `scCoderiv_prodMap_of_graphicallyLipschitzian_left` (and `_right`), `LipschitzWith.graphicallyLipschitzianAt` | |
| GO Def 4.1, Prop 4.2, Remark 4.3, (32)–(34) | regular subspaces, `C_L`, `L* = rge(C_Lᵀ, I)`, SCD regularity, `scdreg` | ✓ | `IsRegularSubspace`, `rgeSubspace`, `regularSubspaceOp`, `IsRegularSubspace.eq_rgeSubspace`, `IsRegularSubspace.adjointSubspace_eq`, `IsRegularSubspace.norm_fst_le`, `IsRegularSubspace.subspaceBound_eq`, `IsSCDRegularAround`, `scdreg` (`SCD/Regularity`) | `scdreg` in `ℝ≥0∞` |
| GO Lemma 4.5 | SCD regularity and `scdreg` through `𝒮F` | ✓ | `isSCDRegularAround_iff_scDeriv`, `IsSCDRegularAround.scdreg_eq_iSup_scDeriv` | |
| GO Lemma 4.7 | `scdreg < ∞` | ✓ | `IsSCDRegularAround.scdreg_lt_top` | |
| GO Prop 4.8 | robustness of SCD regularity and of the modulus | ✓ | `eventually_forall_norm_lt_of_scdreg_lt`, `eventually_isRegularSubspace_and_norm_le`, `IsSCDRegularAround.eventually` | |
| GO Def 5.1 | SCD semismooth* | ✓ | `IsSCDSemismoothStarAt`, `IsSCDSemismoothStarAround`, `isSCDSemismoothStarAt_iff` (`SCD/Semismooth`) | |
| GO Prop 5.3 | `‖x − C_Lᵀ(y − ȳ) − x̄‖ ≤ ε c ‖(x, y) − (x̄, ȳ)‖` | ✓ | `norm_sub_adjoint_le_of_forall`, `IsSCDSemismoothStarAt.eventually_norm_le` | `c = max 1 ‖C_L‖` |
| GO Alg. 1, Thm 5.4 | SCD semismooth* Newton method, local superlinear convergence | ✓ | `newtonApproxSet`, `newtonStep`, `IsSCDNewtonSeq`, `SCDNewtonConverges`, `IsSCDSemismoothStarAt.scdNewton_converges` | |
| GO Prop 5.5, Cor 5.6 | approximation step; convergence under SCD regularity | ✓ | `IsSCDRegularAround.eventually_newtonApproxSet`, `IsSCDSemismoothStarAt.scdNewton_converges_of_isSCDRegularAround` | |
| GO Def 2.5, 2.8, Thm 2.7(i) | strong metric subregularity at/around; Levy–Rockafellar criterion and modulus | ✓ | `StronglyMetricallySubregularWith`, `StronglyMetricallySubregularAround`, `subregBound`, `lsubregBound`, `stronglyMetricallySubregularAt_iff`, `subregBound_eq_coneBound` (`SCD/Subregularity`) | distances via `infEDist` |
| GO Thm 6.1 | strong metric subregularity around iff `(u, 0) ∈ gph D♯F ⇒ u = 0`, (43) | ✓ | `stronglyMetricallySubregularAround_iff`, `stronglyMetricallySubregularAround_iff_sharpDeriv`, `lsubregBound_eq_coneBound` | no closedness of `gph F` needed |
| GO Thm 6.2 | SCD regular + SCD semismooth* ⇒ strongly metrically subregular, `subreg ≤ scdreg` | ✓ | `IsSCDSemismoothStarAt.stronglyMetricallySubregularWith`, `IsSCDSemismoothStarAt.subregBound_le`, `IsSCDRegularAround.eventually_stronglyMetricallySubregularWith` (`SCD/SemismoothSubregularity`) | |
| GO remark after Thm 6.1 | `scdreg ≤ l-subreg` | ✓ | `StronglyMetricallySubregularAround.isSCDRegularAround`, `IsSCDRegularAround.scdreg_le_lsubregBound` | needs the SCD property around |
| GO Cor 6.4 | under SCD semismooth* around: equivalence, `l-subreg = scdreg` | ✓ | `IsSCDSemismoothStarAround.stronglyMetricallySubregularAround_iff`, `IsSCDSemismoothStarAround.lsubregBound_eq` | |
| GO24 Def 2.9, 2.10, 2.11 | semismooth* (w.r.t. `D*F`, w.r.t. a cone-valued `Γ`); SCD-ss* as an instance | ✓ | `IsSemismoothStarWrtAt`, `coderivGraph`, `IsSemismoothStarAt`, `scCoderivUnion`, `isSCDSemismoothStarAt_iff_wrt` (`SCD/SemismoothPrimal`) | |
| GO24 p. 11 | semismooth* + SCD property around ⇒ SCD semismooth* | ✓ | `IsSemismoothStarAt.isSCDSemismoothStarAt` | via GO Lemma 3.7 |
| GO24 Prop 2.12 | primal characterization `dist((x − x̄, y − ȳ), L) = o(‖(x, y) − (x̄, ȳ)‖)` | ✓ | `isSCDSemismoothStarAt_iff_infDist` | distance to the primal `L ∈ 𝒮F(x, y)` (the paper writes `𝒮*F`) |
| GO Prop 3.26 | `∂q` of a continuously prox-regular `q`: graphically Lipschitzian, SCD; `𝒮*∂q = 𝒮∂q`, `L = L* = rge(B, λ⁻¹(I − B))` with `B` symmetric psd | ◐ | `ContinuouslyProxRegularFor.graphicallyLipschitzianAt`, `ContinuouslyProxRegularFor.hasSCDPropertyAround` (`SecondOrder/Moreau`), `proxSubspace`, `adjointSubspace_proxSubspace`, `ContinuouslyProxRegularFor.scd_symm` (`SCD/ProxRegular`), `inner_nonneg_of_mem_proximalMap`, `ContinuouslyProxRegularFor.exists_local_moreau` | from M24 Cor 1.72, with transformation `(x, x*) ↦ (x + λx*, x*)` and the gradient of a local Moreau envelope; symmetry from Hessians, `B ⪰ 0` from the monotonicity of proximal mappings; local maximal hypomonotonicity (Def. 3.20) of `∂q` not yet |
| GO Cor 3.27 | `∂q` is SCD if `q` is continuously prox-regular on a dense subset of `gph ∂q` | ✓ | `isSCDMapping_subdiffMap_of_dense` (`SCD/ProxRegular`) | no lower semicontinuity needed |
| GO 3.30–3.34 | quadratic bundles | ☐ | | |
| GO Sect. 7 | strong metric regularity, Clarke-type inverse function theorem, tilt stability | ☐ | | needs [Rockafellar–Wets, Thm 9.62] |
| GO Examples 3.29, 4.6, 6.5 | worked examples | ☐ | | |
| Minty's theorem | maximal monotone ⇔ monotone with `rge(I + F) = E` | ✓ | `IsMaximalMonotoneOp.exists_sub_mem`, `isMaximalMonotoneOp_iff`, `fitzpatrick`, `IsMaximalMonotoneOp.inner_le_fitzpatrick` (`SCD/Minty`) | finite dimensions; proof via the Fitzpatrick function and a coercive minimization |

## Auxiliary results

| # | Statement | Status | Lean | Notes |
|---|---|---|---|---|
| [Mordukhovich 2024, Lemma 3.1] | Motzkin's theorem of the alternative | ✓ | `exists_multipliers_of_not_exists_direction` (`Analysis/Motzkin`) | finite dimensions, with equality constraints `⟨ξₖ, d⟩ = 0`; via separation |
| Farkas' lemma | `c = ∑ μᵢ aᵢ` with `μ ≥ 0` if `⟨aᵢ, v⟩ ≥ 0 ∀ i ⇒ ⟨c, v⟩ ≥ 0`; closedness of finitely generated cones; conic Carathéodory | ✓ | `exists_nonneg_eq_sum_of_forall_nonneg`, `isClosed_nonnegSpan`, `exists_nonneg_linearIndependent_sum_eq` (`Analysis/Farkas`) | finite dimensions; Mathlib has the separation form for closed cones but not closedness of finitely generated cones; moved from `lean-bilevel` |

## Suggested order of work

SCD mappings: the adjoint formulas (21), (24b) for a general `Φ`; local maximal
hypomonotonicity of `∂q` in Prop. 3.26; quadratic bundles (3.30–3.34); Sect. 7, after
[Rockafellar–Wets, Thm 9.62].

Second-order analysis ([Mordukhovich 2024, Ch. 1]): formula (1.135) of Thm 1.98 and the converse implication of part (a) of
Cor 1.101 (continuing `SecondOrder/EnvelopeTwiceEpi`); Cor 1.87 and Cor 1.99 (need Thm 1.61 for fully
amenable functions and Ex 1.139(ii)).

Variational analysis:

1. The Lipschitzian bilevel results Thm 6.25–6.26 (normals to Lipschitzian inequality systems,
   then the Lipschitzian analogue of `subdiff_lowerValue_subset`).
2. Ch. 5 (maximal monotone operators): hypomonotonicity and monotonicity notions exist already
   (`WellPosedness/Monotone.lean`).
3. Remaining gaps: Cor 2.4 (relative interiors), Thm 2.14 with `‖x̄ − x₀‖ ≤ λ`, the
   epi-regular part of Thm 2.19, the countable extremal principles (Sect. 2.2), (1.38) `⊆`,
   Prop 1.37(ii), the worked examples.
