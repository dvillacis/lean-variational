/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis.Coderivative.ChainRule
import VariationalAnalysis.Coderivative.Variational

/-!
# Subdifferential variational systems with composite fields: the qualification case

For the subdifferential parametric variational system with composite field (3.48) of
[Mordukhovich 2018],

  `S(x) = {y | 0 ∈ f(x, y) + ∂θ(g y)}`,

with `f : E × F → W*` of class `C¹` and `∇ₓf(x̄, ȳ)` surjective, and `g : F → W` of class `C¹`,
Prop. 3.19(i) (full rank of `∇g(ȳ)`; `coderiv_pvsSolutionMap_compositeField` in
`Coderivative/Variational`) computes `D*S(x̄, ȳ)` exactly. Prop. 3.19(ii) replaces the full rank
of `∇g(ȳ)` by the qualification condition (3.51)

  `∂²θ(w̄, q̄)(0) ∩ ker ∇g(ȳ)* = {0}`,  `w̄ = g ȳ`, `q̄ = -f(x̄, ȳ)`,

and the closedness of `gph ∂θ` around `(w̄, q̄)`, and gives the inclusions `⊆` in (3.49) and
(3.50). As in the book, the proof combines Prop. 3.16 with the chain rule Thm. 3.11(i) for the
composition `∂θ ∘ g` (`coderiv_comp_subset`), where the qualification condition (3.26) becomes
(3.51).

Directions in `W**` are written as `u : W` through `NormedSpace.inclusionInDoubleDual`, as in
`Coderivative/SecondOrder`.

## Main results

* `coderiv_pvsSolutionMap_compositeField_subset`: Prop. 3.19(ii), inclusion in (3.49).
* `coderivKer_pvsSolutionMap_compositeField_subset`: Prop. 3.19(ii), inclusion in (3.50).
-/

open Filter Topology Set Metric ContinuousLinearMap
open scoped Pointwise

namespace VariationalAnalysis

variable {E F W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ F] [FiniteDimensional ℝ W] {x₀ : E} {y₀ : F}

/-- The coderivative of the field `Q = ∂θ ∘ g` under (3.51) [Mordukhovich 2018, proof of
Prop. 3.19(ii)]: `D*(∂θ ∘ g)(ȳ, q̄)(z*) ⊆ ∇g(ȳ)* D*∂θ(w̄, q̄)(z*)`. -/
theorem coderiv_subdiff_comp_subset {θ : W → EReal} {g : F → W} {Dg : F → F →L[ℝ] W}
    {q₀ : StrongDual ℝ W} (hg : ∀ᶠ y in 𝓝 y₀, HasStrictFDerivAt g (Dg y) y)
    (hDg : ContinuousAt Dg y₀)
    (hloc : ∃ r > 0, IsClosed (graph (subdiff θ) ∩ closedBall (g y₀, q₀) r))
    (hqc : ∀ m ∈ secondOrderSubdiff θ (g y₀) q₀ 0, m.comp (Dg y₀) = 0 → m = 0)
    (z' : StrongDual ℝ (StrongDual ℝ W)) :
    coderiv (fun y ↦ subdiff θ (g y)) y₀ q₀ z' ⊆
      (fun m ↦ m.comp (Dg y₀)) '' coderiv (subdiff θ) (g y₀) q₀ z' :=
  coderiv_comp_subset hg hDg hloc (fun m hm ↦ hqc m (by
    rwa [secondOrderSubdiff, map_zero])) z'

/-- Prop. 3.19(ii) of [Mordukhovich 2018], inclusion `⊆` in (3.49): let
`S(x) = {y | 0 ∈ f(x, y) + ∂θ(g y)}` with `f : E × F → W*` of class `C¹` around `(x̄, ȳ)`,
`∇ₓf(x̄, ȳ)` surjective, `g : F → W` of class `C¹` around `ȳ`, `gph ∂θ` locally closed around
`(w̄, q̄)` (`w̄ = g ȳ`, `q̄ = -f(x̄, ȳ)`), and the qualification condition (3.51)
`∂²θ(w̄, q̄)(0) ∩ ker ∇g(ȳ)* = {0}`. Then

  `D*S(x̄, ȳ)(y*) ⊆ {x* | ∃ u, x* = ∇ₓf(x̄, ȳ)* u, -y* ∈ ∇ᵧf(x̄, ȳ)* u + ∇g(ȳ)* ∂²θ(w̄, q̄)(u)}`,

with `u ∈ W ≅ W**`. -/
theorem coderiv_pvsSolutionMap_compositeField_subset {f : E × F → StrongDual ℝ W}
    {Df : E × F → E × F →L[ℝ] StrongDual ℝ W} {θ : W → EReal} {g : F → W}
    {Dg : F → F →L[ℝ] W} (hf : ∀ᶠ p in 𝓝 (x₀, y₀), HasStrictFDerivAt f (Df p) p)
    (hDf : ContinuousAt Df (x₀, y₀)) (hsurj : Function.Surjective ((Df (x₀, y₀)).comp (inl ℝ E F)))
    (hg : ∀ᶠ y in 𝓝 y₀, HasStrictFDerivAt g (Dg y) y) (hDg : ContinuousAt Dg y₀)
    (hloc : ∃ r > 0, IsClosed (graph (subdiff θ) ∩ closedBall (g y₀, -f (x₀, y₀)) r))
    (hqc : ∀ m ∈ secondOrderSubdiff θ (g y₀) (-f (x₀, y₀)) 0, m.comp (Dg y₀) = 0 → m = 0)
    (y' : StrongDual ℝ F) :
    coderiv (pvsSolutionMap f fun y ↦ subdiff θ (g y)) x₀ y₀ y' ⊆
      {x' | ∃ u : W,
        x' = (NormedSpace.inclusionInDoubleDual ℝ W u).comp ((Df (x₀, y₀)).comp (inl ℝ E F)) ∧
        -y' ∈ (fun m : StrongDual ℝ W ↦
            (NormedSpace.inclusionInDoubleDual ℝ W u).comp ((Df (x₀, y₀)).comp (inr ℝ E F)) +
              m.comp (Dg y₀)) '' secondOrderSubdiff θ (g y₀) (-f (x₀, y₀)) u} := by
  rw [coderiv_pvsSolutionMap hf hDf hsurj]
  rintro x' ⟨z', hx', w, hw, hwy⟩
  obtain ⟨u, rfl⟩ := inclusionInDoubleDual_surjective z'
  obtain ⟨m, hm, rfl⟩ := coderiv_subdiff_comp_subset hg hDg hloc hqc _ hw
  exact ⟨u, hx', m, hm, hwy⟩

/-- Prop. 3.19(ii) of [Mordukhovich 2018], inclusion `⊆` in (3.50): under the assumptions of
`coderiv_pvsSolutionMap_compositeField_subset`, `ker D*S(x̄, ȳ) ⊆ -∇g(ȳ)* ∂²θ(w̄, q̄)(0)`. -/
theorem coderivKer_pvsSolutionMap_compositeField_subset {f : E × F → StrongDual ℝ W}
    {Df : E × F → E × F →L[ℝ] StrongDual ℝ W} {θ : W → EReal} {g : F → W}
    {Dg : F → F →L[ℝ] W} (hf : ∀ᶠ p in 𝓝 (x₀, y₀), HasStrictFDerivAt f (Df p) p)
    (hDf : ContinuousAt Df (x₀, y₀)) (hsurj : Function.Surjective ((Df (x₀, y₀)).comp (inl ℝ E F)))
    (hg : ∀ᶠ y in 𝓝 y₀, HasStrictFDerivAt g (Dg y) y) (hDg : ContinuousAt Dg y₀)
    (hloc : ∃ r > 0, IsClosed (graph (subdiff θ) ∩ closedBall (g y₀, -f (x₀, y₀)) r))
    (hqc : ∀ m ∈ secondOrderSubdiff θ (g y₀) (-f (x₀, y₀)) 0, m.comp (Dg y₀) = 0 → m = 0) :
    coderivKer (pvsSolutionMap f fun y ↦ subdiff θ (g y)) x₀ y₀ ⊆
      -((fun m : StrongDual ℝ W ↦ m.comp (Dg y₀)) ''
        secondOrderSubdiff θ (g y₀) (-f (x₀, y₀)) 0) := by
  rw [coderivKer_pvsSolutionMap hf hDf hsurj]
  intro y' hy'
  rw [Set.mem_neg] at hy' ⊢
  have h := coderiv_subdiff_comp_subset hg hDg hloc hqc 0 hy'
  rwa [secondOrderSubdiff, map_zero]

end VariationalAnalysis
