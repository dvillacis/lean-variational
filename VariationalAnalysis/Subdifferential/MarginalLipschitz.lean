/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis.Subdifferential.Characterizations
import VariationalAnalysis.Subdifferential.Marginal

/-!
# Local Lipschitz continuity of marginal functions

[Mordukhovich 2018, Cor. 4.3]: a marginal function `μ(x) = inf {φ(x, y) | y ∈ G x}` with a
Lipschitzian cost and a Lipschitz-like constraint mapping is locally Lipschitz, provided it is
lower semicontinuous around the point. The proof combines the reduction
`∂^∞μ(x₀) = {0}` (`singularSubdiff_marginal_eq_zero_of_lipschitzLikeAt`,
`singularSubdiff_marginal_eq_zero_of_locallyBoundedAt`, from Thm. 4.1 and Thm. 3.3) with the "if"
part of Thm. 1.22 (`exists_lipschitzOnWith_of_singularSubdiff`).

## Main results

* `exists_lipschitzOnWith_marginal_of_lipschitzLikeAt`: Cor. 4.3(i) of [Mordukhovich 2018].
* `exists_lipschitzOnWith_marginal_of_locallyBoundedAt`: Cor. 4.3(ii) of [Mordukhovich 2018].

As in `VariationalAnalysis.Subdifferential.Marginal`, the inner semicontinuity of the argminimum
mapping (part (i)) and its local boundedness (part (ii)) come with the attainment of the infimum
near `x₀` wherever `μ < ⊤`, which the book's proof uses implicitly.
-/

open Filter Topology Set Metric
open scoped NNReal

namespace VariationalAnalysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {G : E → Set F} {x₀ : E} {y₀ : F} {r : ℝ}

/-- Cor. 4.3(i) of [Mordukhovich 2018] (local Lipschitz continuity of marginal functions): let the
argminimum mapping (4.2) be inner semicontinuous at `(x₀, y₀)` (the infimum in (4.1) being
attained near `x₀` wherever `μ < ⊤`), the cost `f` be Lipschitz around `(x₀, y₀)`, `gph G` be
locally closed around `(x₀, y₀)` and `G` be Lipschitz-like around `(x₀, y₀)`. If `μ` is finite at
`x₀` and l.s.c. around `x₀`, then `μ` is Lipschitz continuous around `x₀`: it agrees near `x₀`
with a real function Lipschitz on a neighborhood of `x₀`. -/
theorem exists_lipschitzOnWith_marginal_of_lipschitzLikeAt {f : E × F → ℝ} {U : Set (E × F)}
    {L : ℝ≥0} (hU : U ∈ 𝓝 (x₀, y₀)) (hL : LipschitzOnWith L f U)
    (hr : marginal (fun p ↦ (f p : EReal)) G x₀ = r)
    (hy₀ : y₀ ∈ argminMap (fun p ↦ (f p : EReal)) G x₀)
    (hisc : InnerSemicontinuousAt (argminMap (fun p ↦ (f p : EReal)) G) x₀ y₀)
    (hatt : ∀ᶠ x in 𝓝 x₀, marginal (fun p ↦ (f p : EReal)) G x ≠ ⊤ →
      (argminMap (fun p ↦ (f p : EReal)) G x).Nonempty)
    (hG : ∃ ρ > 0, IsClosed (graph G ∩ closedBall (x₀, y₀) ρ))
    (hlip : LipschitzLikeAt G x₀ y₀)
    (hlsc : ∀ᶠ x in 𝓝 x₀, LowerSemicontinuousAt (marginal (fun p ↦ (f p : EReal)) G) x) :
    ∃ V ∈ 𝓝 x₀, ∃ K : ℝ≥0, ∃ μ : E → ℝ,
      (∀ x ∈ V, marginal (fun p ↦ (f p : EReal)) G x = μ x) ∧ LipschitzOnWith K μ V := by
  have h0 := singularSubdiff_marginal_eq_zero_of_lipschitzLikeAt hU hL hr hy₀ hisc hatt hG hlip
  exact exists_lipschitzOnWith_of_singularSubdiff hr hlsc fun v hv ↦ by rwa [h0] at hv

/-- Cor. 4.3(ii) of [Mordukhovich 2018]: let the argminimum mapping (4.2) be locally bounded
around `x₀` (the infimum in (4.1) being attained near `x₀` wherever `μ < ⊤`), `gph G` be closed,
the real-valued cost `f` be l.s.c. around every `(x₀, y)`, `y ∈ G x₀`, and, for every
`y ∈ M(x₀)`, let `f` be Lipschitz around `(x₀, y)` and `G` Lipschitz-like around `(x₀, y)`. If
`μ` is finite at `x₀` and l.s.c. around `x₀`, then `μ` is Lipschitz continuous around `x₀`. -/
theorem exists_lipschitzOnWith_marginal_of_locallyBoundedAt {f : E × F → ℝ}
    (hr : marginal (fun p ↦ (f p : EReal)) G x₀ = r)
    (hlb : LocallyBoundedAt (argminMap (fun p ↦ (f p : EReal)) G) x₀)
    (hatt : ∀ᶠ x in 𝓝 x₀, marginal (fun p ↦ (f p : EReal)) G x ≠ ⊤ →
      (argminMap (fun p ↦ (f p : EReal)) G x).Nonempty)
    (hG : IsClosed (graph G))
    (hφ : ∀ y ∈ G x₀, ∃ U ∈ 𝓝 (x₀, y), LowerSemicontinuousOn (fun p ↦ (f p : EReal)) U)
    (hL : ∀ y ∈ argminMap (fun p ↦ (f p : EReal)) G x₀,
      ∃ U ∈ 𝓝 (x₀, y), ∃ L : ℝ≥0, LipschitzOnWith L f U)
    (hlip : ∀ y ∈ argminMap (fun p ↦ (f p : EReal)) G x₀, LipschitzLikeAt G x₀ y)
    (hlsc : ∀ᶠ x in 𝓝 x₀, LowerSemicontinuousAt (marginal (fun p ↦ (f p : EReal)) G) x) :
    ∃ V ∈ 𝓝 x₀, ∃ K : ℝ≥0, ∃ μ : E → ℝ,
      (∀ x ∈ V, marginal (fun p ↦ (f p : EReal)) G x = μ x) ∧ LipschitzOnWith K μ V := by
  have h0 := singularSubdiff_marginal_eq_zero_of_locallyBoundedAt hr hlb hatt hG hφ hL hlip
  exact exists_lipschitzOnWith_of_singularSubdiff hr hlsc fun v hv ↦ by rwa [h0] at hv

end VariationalAnalysis
