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
| 6.13–6.20 | Bilevel programs: value function approach, partial calmness, weak sharp minima | ☐ | | |
| 6.21–6.27 | Optimality conditions for smooth and Lipschitzian bilevel programs | ☐ | | |

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

1. The bilevel optimality conditions of Ch. 6 (value function approach, Sect. 6.2–6.3), which
   build on Sect. 6.1, Thm 4.1 and the Ch. 3 criteria.
2. Ch. 5 (maximal monotone operators): hypomonotonicity and monotonicity notions exist already
   (`WellPosedness/Monotone.lean`).
3. Remaining gaps: Cor 2.4 (relative interiors), Thm 2.14 with `‖x̄ − x₀‖ ≤ λ`, the
   epi-regular part of Thm 2.19, the countable extremal principles (Sect. 2.2), (1.38) `⊆`,
   Prop 1.37(ii), the worked examples.
