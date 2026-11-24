# Errata and remarks on the sources

Places where the formalized statement differs from the printed one, or where a printed proof
needed a repair. Each entry names the Lean declaration that holds the corrected statement;
`ROADMAP.md` has the full list of statements. The counterexamples are described in the module
or declaration docstrings of the files named; they are not themselves formalized.

## [Mordukhovich 2018]

B. S. Mordukhovich, *Variational Analysis and Applications*, Springer, 2018.

### Statements that need a change

| Statement | Remark | Lean |
|---|---|---|
| Thm. 2.12, (2.21) | The strict inequality holds for a suitable choice of the minimizer; it fails for some minimizers. | `general_variational_principle_subadditive`, `exists_lex_minimizer` |
| Thm. 3.2(i) | The relation between the covering and regularity bounds needs `E ≠ {0}`; it is false for `E = {0}`. | `covBound_eq_inv_regBound` |
| Thm. 3.14 | The statement fails without the qualification condition (3.22), which is added. | `coderiv_binaryComp_subset` |
| Thm. 3.25 | The hypothesis "no neighborhood of `ȳ` where `Q` is single-valued" must be "`Q` is not single-valued around `(ȳ, z̄)`". Counterexample: `Q y = {0, 1}`, `f(x, y) = x`. | `not_metricallyRegularAt_pvsSolutionMap_of_locallyMonotoneAt` |
| Thm. 4.1(i) | Under μ-inner semicontinuity, (4.5) also needs `μ` lower semicontinuous at `x̄` (counterexample in `Subdifferential/Marginal`). With the book's inner semicontinuity, the proof uses that the infimum is attained near `x̄`. | `singularSubdiff_marginal_subset`, `subdiff_marginal_subset_of_innerSemicontinuousAt` |
| Cor. 4.8 | Sign error in the second quotient formula: `− ∂(φ₁(x̄)φ₂)` must be `+ ∂(−φ₁(x̄)φ₂)`. Counterexample: `f₁ = 1`, `f₂ = 1 − |x|`. | `subdiff_div_eq_add` |
| Thm. 4.18 | Needs `U` convex; false otherwise (counterexample in `Subdifferential/MonotoneConvex`). | `antitone_iff_regularSubdiff_subset_polar` |
| Prop. 6.13 | The inclusion `S̃ ⊆ S` can fail for the definition of `S̃` via (6.35); we use `S̃(x) = {y ∈ S(x) ∣ f(x, y) = f_opt(x)}`. Part (ii) assumes that the infimum in `f_opt` is attained near `x̄`. | `isLocalMinOn_valueFeasible_of_isLocalMinOn_optimisticValue`, `isLocalMinOn_optimisticValue_of_isLocalMinOn_valueFeasible` |

### Hypotheses used by the proof and made explicit

| Statement | Remark | Lean |
|---|---|---|
| Prop. 2.15 | The proof uses that `θ` is subadditive. | `exists_fixedPoint_of_variational` |
| Prop. 6.17 | `S(x) ≠ ∅` near `x̄`, the book's standing assumption, is a hypothesis. | `partiallyCalm_of_uniform_weakSharp` |
| Thm. 6.21 | Lower semicontinuity of `μ` around `x̄` is assumed; the argument given as "easy to see" only yields it at `x̄`. `S(x) ≠ ∅` near `x̄` is a hypothesis. | `exists_multipliers_smooth_bilevel_upper` |

### Proofs

| Statement | Remark | Lean |
|---|---|---|
| Prop. 1.37(ii) | Not formalized. The proof says to proceed as for (1.37), and that argument does not keep the constraint `φ x ≥ φ x₀`. | |
| Thm. 2.14 | The printed proof of the lower part gives `‖x̄ − x₀‖ < 2λ`. We prove `‖x̄ − x₀‖ < λ + η` for every `η > 0` in inner product spaces; the stated bound `≤ λ` is not proved. | `exists_mem_regularSubdiff_norm_sub_lt_two_mul`, `exists_mem_regularSubdiff_almost_stationary` |
| Thm. 4.14(i) | For `φ(b) = ∞`, the argument needed a diagonal repair. | `mean_value_ineq` |
| Thm. 6.10 | The appeal to "Thm. 1.32 and its proof" is replaced by a direct argument on normals to the constraint graph. | `mem_regularSubdiff_of_mem_regularNormalCone`, `mem_subdiff_of_mem_normalCone_constraintGraph` |

## [Mordukhovich 2024]

B. S. Mordukhovich, *Second-Order Variational Analysis in Optimization, Variational Stability,
and Control*, Springer, 2024.

| Statement | Remark | Lean |
|---|---|---|
| Thm. 1.70, 1.71 | The book assumes `φ` lower semicontinuous and minorized by a quadratic *around* `x̄`. But `P_λφ` is a global argmin, and it is empty when `φ` is unbounded below far away. We assume prox-boundedness, `φ(x) ≥ a − b‖x − x̄‖²` for all `x` (and global lower semicontinuity, for simplicity). | `ProxRegularFor.exists_proximalMap`, `ProxRegularFor.exists_moreauEnvelope` |

## [Gfrerer–Outrata 2024]

H. Gfrerer and J. V. Outrata, *On the role of semismoothness in nonsmooth numerical analysis:
Theory*, arXiv:2405.14637.

| Statement | Remark | Lean |
|---|---|---|
| Prop. 2.12 | The distance is to the primal subspace `L ∈ 𝒮F(x, y)`; the paper writes `𝒮*F`. | `isSCDSemismoothStarAt_iff_infDist` |
