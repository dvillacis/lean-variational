/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis.Coderivative.SecondOrder
import VariationalAnalysis.Subdifferential.Coderivative
import VariationalAnalysis.Normal.Diffeomorphism

/-!
# Second-order subdifferentials: definitions and elementary properties

This file follows [Mordukhovich 2024, Sect. 1.2] (B. S. Mordukhovich, *Second-Order Variational
Analysis in Optimization, Variational Stability, and Control*, Springer, 2024).

The basic second-order subdifferential `∂²φ(x̄, v̄)(u) = (D*∂φ)(x̄, v̄)(u)` is
`secondOrderSubdiff` (`Coderivative/SecondOrder`), with the direction `u : E` fed to the
coderivative through `E → E**`. In finite dimensions the normal and the mixed coderivatives
agree, so [Mordukhovich 2024, Def. 1.46(i)–(ii)] is `secondOrderSubdiff`. Here we add the
combined second-order subdifferential `∂̆²φ(x̄, v̄)(u) = (D̂*∂φ)(x̄, v̄)(u)` of Def. 1.46(iii) and
the partial second-order subdifferentials of Def. 1.52.

## Main declarations

* `combinedSecondOrderSubdiff`: [Mordukhovich 2024, Def. 1.46(iii), (1.62)].
* `partialSubdiff`, `partialSecondOrderSubdiff`, `combinedPartialSecondOrderSubdiff`:
  [Mordukhovich 2024, (1.66), Def. 1.52, (1.67)–(1.68)].

## Main results

* `combinedSecondOrderSubdiff_of_hasFDerivAt`: [Mordukhovich 2024, Prop. 1.47], combined part:
  for `φ` of class `C¹` around `x̄` with `∇φ` differentiable at `x̄`,
  `∂̆²φ(x̄)(u) = {∇²φ(x̄) u}`. The basic part is `secondOrderSubdiff_of_hasFDerivAt`.
* `regularCoderiv_eq_regularSubdiff_comp`: the regular coderivative of a Lipschitz map is the
  regular subdifferential of its scalarization [Mordukhovich 2024, Thm. 1.34].
* `combinedSecondOrderSubdiff_of_lipschitz`, `secondOrderSubdiff_of_lipschitz`:
  [Mordukhovich 2024, Prop. 1.50] (second-order subdifferentials of `C^{1,1}` functions):
  `∂̆²φ(x̄)(u) = ∂̂⟨u, ∇φ⟩(x̄)` and `∂²φ(x̄)(u) = ∂⟨u, ∇φ⟩(x̄)`.
* `mem_regularCoderiv_add_iff`, `regularCoderiv_add`: the regular coderivative sum rule with a
  summand differentiable at the point [Mordukhovich 2024, Thm. 1.15(i)].
* `secondOrderSubdiff_add`, `combinedSecondOrderSubdiff_add`: [Mordukhovich 2024, Prop. 1.51]
  (equality sum rules (1.64), (1.65)).
* `partialSecondOrderSubdiff_of_hasFDerivAt`, `combinedPartialSecondOrderSubdiff_of_hasFDerivAt`:
  [Mordukhovich 2024, Prop. 1.53].
* `partialSecondOrderSubdiff_add`, `combinedPartialSecondOrderSubdiff_add`:
  [Mordukhovich 2024, Prop. 1.54] (partial sum rules (1.69), (1.70)).

## Hypotheses

The book's Prop. 1.51(i) and 1.54(i) assume that `∇φ₁` is strictly differentiable at `x̄`. We
use the coderivative sum rule (3.24) of [Mordukhovich 2018], which asks for `∇φ₁` strictly
differentiable around `x̄` with derivative continuous at `x̄` (e.g. `φ₁ ∈ C²`). The combined
versions only need `∇φ₁` Fréchet differentiable at `x̄`, as in the book. The smooth summand is
written on the right, `φ + f`, as in `mem_subdiff_add_iff`. Partial subgradients of
`φ : E × F → EReal` are elements of `E*`, and partial second-order subdifferentials take values
in `(E × F)*`, where the book writes pairs `(x*, y*) ∈ X* × Y*`.
-/

open Filter Topology Set ContinuousLinearMap
open scoped NNReal

namespace VariationalAnalysis

section Congr

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Regular coderivatives only depend on the mapping near the point. -/
theorem regularCoderiv_congr {S T : E → Set F} {x₀ : E} (h : ∀ᶠ x in 𝓝 x₀, S x = T x) (y₀ : F)
    (v : StrongDual ℝ F) : regularCoderiv S x₀ y₀ v = regularCoderiv T x₀ y₀ v := by
  have hg : graph S =ᶠ[𝓝 (x₀, y₀)] graph T := by
    filter_upwards [(continuous_fst.tendsto (x₀, y₀)).eventually h] with p hp
    change (p.2 ∈ S p.1) = (p.2 ∈ T p.1)
    rw [hp]
  simp only [regularCoderiv, regularNormalCone_congr hg]

end Congr

section Combined

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- [Mordukhovich 2024, Def. 1.46(iii), (1.62)] (combined second-order subdifferential): for
`v₀ ∈ ∂φ(x₀)`, `∂̆²φ(x₀, v₀)(u) = (D̂*∂φ)(x₀, v₀)(u)`, the regular coderivative of the basic
subgradient mapping. As for `secondOrderSubdiff`, `u : E` enters through `E → E**`. -/
def combinedSecondOrderSubdiff (φ : E → EReal) (x₀ : E) (v₀ : StrongDual ℝ E) (u : E) :
    Set (StrongDual ℝ E) :=
  regularCoderiv (subdiff φ) x₀ v₀ (NormedSpace.inclusionInDoubleDual ℝ E u)

/-- The combined second-order subdifferential is contained in the second-order subdifferential:
`∂̆²φ(x₀, v₀)(u) ⊆ ∂²φ(x₀, v₀)(u)`, since `D̂*∂φ ⊆ D*∂φ`. -/
theorem combinedSecondOrderSubdiff_subset_secondOrderSubdiff {φ : E → EReal} {x₀ u : E}
    {v₀ : StrongDual ℝ E} :
    combinedSecondOrderSubdiff φ x₀ v₀ u ⊆ secondOrderSubdiff φ x₀ v₀ u :=
  regularCoderiv_subset_coderiv

/-- `∂φ(x) = {φ'(x)}` near `x₀` for `φ` of class `C¹` around `x₀`. -/
theorem eventually_subdiff_eq_singleton {φ : E → ℝ} {φ' : E → StrongDual ℝ E} {x₀ : E}
    (hφ : ∀ᶠ x in 𝓝 x₀, HasFDerivAt φ (φ' x) x) (hc : ∀ᶠ x in 𝓝 x₀, ContinuousAt φ' x) :
    ∀ᶠ x in 𝓝 x₀, subdiff (fun x ↦ (φ x : EReal)) x = {φ' x} := by
  filter_upwards [hφ.eventually_nhds, hc] with x hx hcx
  exact subdiff_of_hasFDerivAt_of_continuousAt hx hcx

/-- [Mordukhovich 2024, Prop. 1.47], combined part: if `φ` is of class `C¹` around `x₀` and its
gradient `φ'` is differentiable at `x₀` with derivative `φ''`, then
`∂̆²φ(x₀)(u) = {∇²φ(x₀) u}`. (The coderivative gives `∇²φ(x₀)* u`, which is `∇²φ(x₀) u` by the
symmetry of the second derivative.) -/
theorem combinedSecondOrderSubdiff_of_hasFDerivAt {φ : E → ℝ} {φ' : E → StrongDual ℝ E}
    {φ'' : E →L[ℝ] StrongDual ℝ E} {x₀ : E} (hφ : ∀ᶠ x in 𝓝 x₀, HasFDerivAt φ (φ' x) x)
    (hc : ∀ᶠ x in 𝓝 x₀, ContinuousAt φ' x) (hφ' : HasFDerivAt φ' φ'' x₀) (u : E) :
    combinedSecondOrderSubdiff (fun x ↦ (φ x : EReal)) x₀ (φ' x₀) u = {φ'' u} := by
  rw [combinedSecondOrderSubdiff, regularCoderiv_congr (eventually_subdiff_eq_singleton hφ hc),
    regularCoderiv_of_hasFDerivAt hφ']
  congr 1
  ext h
  simp only [comp_apply, NormedSpace.dual_def]
  exact second_derivative_symmetric_of_eventually hφ hφ' h u

end Combined

section Scalarization

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The regular part of the coderivative scalarization [Mordukhovich 2024, Thm. 1.34]: for `f`
Lipschitz around `x₀`, `D̂*f(x₀)(v) = ∂̂⟨v, f⟩(x₀)`. -/
theorem regularCoderiv_eq_regularSubdiff_comp {f : E → F} {x₀ : E} {U : Set E} {L : ℝ≥0}
    (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U) (v : StrongDual ℝ F) :
    regularCoderiv (fun x ↦ ({f x} : Set F)) x₀ (f x₀) v =
      regularSubdiff (fun x ↦ ((v (f x) : ℝ) : EReal)) x₀ := by
  ext u
  constructor
  · intro hu
    have h := mem_epsSubdiff_comp_of_mem_regularNormalCone_graph hU hL hu v
    have h1 : (u.coprod (-v)).comp (ContinuousLinearMap.inl ℝ E F) = u := by ext; simp
    have h2 : -(u.coprod (-v)).comp (ContinuousLinearMap.inr ℝ E F) - v = 0 := by ext; simp
    rwa [h1, h2, norm_zero, mul_zero, epsSubdiff_zero] at h
  · intro hu
    exact coprod_mem_regularNormalCone_graph_of_mem_regularSubdiff hu

end Scalarization

section C11

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `C^{1,1}` data: `φ` is differentiable on a neighborhood `U` of `x₀`, with gradient `φ'`
Lipschitz on `U`. Then `∂φ(x) = {φ'(x)}` near `x₀`. -/
theorem eventually_subdiff_eq_singleton_of_lipschitz {φ : E → ℝ} {φ' : E → StrongDual ℝ E}
    {x₀ : E} {U : Set E} {L : ℝ≥0} (hU : U ∈ 𝓝 x₀) (hφ : ∀ x ∈ U, HasFDerivAt φ (φ' x) x)
    (hL : LipschitzOnWith L φ' U) :
    ∀ᶠ x in 𝓝 x₀, subdiff (fun x ↦ (φ x : EReal)) x = {φ' x} := by
  have hU' : ∀ᶠ x in 𝓝 x₀, U ∈ 𝓝 x := eventually_eventually_nhds.2 hU
  refine eventually_subdiff_eq_singleton ?_ ?_
  · filter_upwards [hU] with x hx using hφ x hx
  · filter_upwards [hU'] with x hx using hL.continuousOn.continuousAt hx

/-- [Mordukhovich 2024, Prop. 1.50], combined part (second-order subdifferentials of `C^{1,1}`
functions): if `φ` is differentiable on a neighborhood `U` of `x₀` with gradient `φ'` Lipschitz
on `U`, then `∂̆²φ(x₀)(u) = ∂̂⟨u, ∇φ⟩(x₀)`. -/
theorem combinedSecondOrderSubdiff_of_lipschitz {φ : E → ℝ} {φ' : E → StrongDual ℝ E} {x₀ : E}
    {U : Set E} {L : ℝ≥0} (hU : U ∈ 𝓝 x₀) (hφ : ∀ x ∈ U, HasFDerivAt φ (φ' x) x)
    (hL : LipschitzOnWith L φ' U) (u : E) :
    combinedSecondOrderSubdiff (fun x ↦ (φ x : EReal)) x₀ (φ' x₀) u =
      regularSubdiff (fun x ↦ ((φ' x u : ℝ) : EReal)) x₀ := by
  rw [combinedSecondOrderSubdiff,
    regularCoderiv_congr (eventually_subdiff_eq_singleton_of_lipschitz hU hφ hL),
    regularCoderiv_eq_regularSubdiff_comp hU hL]
  rfl

/-- [Mordukhovich 2024, Prop. 1.50], basic part (second-order subdifferentials of `C^{1,1}`
functions, finite dimensions): `∂²φ(x₀)(u) = ∂⟨u, ∇φ⟩(x₀)`. -/
theorem secondOrderSubdiff_of_lipschitz [FiniteDimensional ℝ E] {φ : E → ℝ}
    {φ' : E → StrongDual ℝ E} {x₀ : E} {U : Set E} {L : ℝ≥0} (hU : U ∈ 𝓝 x₀)
    (hφ : ∀ x ∈ U, HasFDerivAt φ (φ' x) x) (hL : LipschitzOnWith L φ' U) (u : E) :
    secondOrderSubdiff (fun x ↦ (φ x : EReal)) x₀ (φ' x₀) u =
      subdiff (fun x ↦ ((φ' x u : ℝ) : EReal)) x₀ := by
  rw [secondOrderSubdiff, coderiv_congr (eventually_subdiff_eq_singleton_of_lipschitz hU hφ hL),
    ← subdiff_comp_eq_coderiv hU hL]
  rfl

end C11

section RegularSum

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The regular coderivative sum rule with a summand differentiable at the point
[Mordukhovich 2024, Thm. 1.15(i)], pointwise form: if `F₁` is Fréchet differentiable at `x₀`
with derivative `A`, then `m ∈ D̂*(F₁ + F₂)(x₀, F₁ x₀ + y₀)(y*)` iff
`m - y* ∘ A ∈ D̂*F₂(x₀, y₀)(y*)`. -/
theorem mem_regularCoderiv_add_iff {F₁ : E → F} {A : E →L[ℝ] F} {F₂ : E → Set F} {x₀ : E}
    {y₀ : F} (hF : HasFDerivAt F₁ A x₀) {y' : StrongDual ℝ F} {m : StrongDual ℝ E} :
    m ∈ regularCoderiv (fun x ↦ (fun y ↦ F₁ x + y) '' F₂ x) x₀ (F₁ x₀ + y₀) y' ↔
      m - y'.comp A ∈ regularCoderiv F₂ x₀ y₀ y' := by
  set Ψ : E × F → E × F := fun p ↦ (p.1, F₁ p.1 + p.2)
  set Θ : E × F → E × F := fun p ↦ (p.1, p.2 - F₁ p.1)
  set DΨ : E × F →L[ℝ] E × F := (fst ℝ E F).prod (A.comp (fst ℝ E F) + snd ℝ E F)
  set DΘ : E × F →L[ℝ] E × F := (fst ℝ E F).prod (snd ℝ E F - A.comp (fst ℝ E F))
  have hΨ : HasFDerivAt Ψ DΨ (x₀, y₀) :=
    hasFDerivAt_fst.prodMk ((hF.comp (x₀, y₀) hasFDerivAt_fst).add hasFDerivAt_snd)
  have hΘ : HasFDerivAt Θ DΘ (x₀, F₁ x₀ + y₀) :=
    hasFDerivAt_fst.prodMk (hasFDerivAt_snd.sub (hF.comp (x₀, F₁ x₀ + y₀) hasFDerivAt_fst))
  have hΨx : Ψ (x₀, y₀) = (x₀, F₁ x₀ + y₀) := rfl
  have hΘx : Θ (x₀, F₁ x₀ + y₀) = (x₀, y₀) := by simp [Θ]
  have hΨmaps : ∀ p ∈ graph F₂, Ψ p ∈ graph fun x ↦ (fun y ↦ F₁ x + y) '' F₂ x :=
    fun p hp ↦ ⟨p.2, hp, rfl⟩
  have hΘmaps : ∀ p ∈ graph (fun x ↦ (fun y ↦ F₁ x + y) '' F₂ x), Θ p ∈ graph F₂ := by
    rintro ⟨x, y⟩ ⟨z, hz, hzy⟩
    simp only at hz hzy
    change y - F₁ x ∈ F₂ x
    rw [← hzy, add_sub_cancel_left]
    exact hz
  constructor
  · intro h
    have hy₀ : (x₀, y₀) ∈ graph F₂ := by simpa [hΘx] using hΘmaps _ h.1
    have := comp_mem_regularNormalCone_of_hasFDerivAt hΨ hy₀
      (eventually_nhdsWithin_of_forall hΨmaps)
      (show m.coprod (-y') ∈ regularNormalCone _ (Ψ (x₀, y₀)) from h)
    have heq : (m.coprod (-y')).comp DΨ = (m - y'.comp A).coprod (-y') := by
      ext <;> simp [DΨ, sub_eq_add_neg]
    rw [regularCoderiv, mem_ofPred_eq, ← heq]
    exact this
  · intro h
    have hy₀ : ((x₀, F₁ x₀ + y₀) : E × F) ∈ graph fun x ↦ (fun y ↦ F₁ x + y) '' F₂ x :=
      hΨmaps _ h.1
    have := comp_mem_regularNormalCone_of_hasFDerivAt hΘ hy₀
      (eventually_nhdsWithin_of_forall hΘmaps) (by rw [hΘx]; exact h)
    have heq : ((m - y'.comp A).coprod (-y')).comp DΘ = m.coprod (-y') := by
      ext <;> simp [DΘ]
    rw [heq] at this
    exact this

/-- The regular coderivative sum rule with a summand differentiable at the point
[Mordukhovich 2024, Thm. 1.15(i)]:
`D̂*(F₁ + F₂)(x₀, y₀)(y*) = ∇F₁(x₀)* y* + D̂*F₂(x₀, y₀ - F₁ x₀)(y*)`. -/
theorem regularCoderiv_add {F₁ : E → F} {A : E →L[ℝ] F} {F₂ : E → Set F} {x₀ : E} {y₀ : F}
    (hF : HasFDerivAt F₁ A x₀) (y' : StrongDual ℝ F) :
    regularCoderiv (fun x ↦ (fun y ↦ F₁ x + y) '' F₂ x) x₀ y₀ y' =
      (fun u ↦ y'.comp A + u) '' regularCoderiv F₂ x₀ (y₀ - F₁ x₀) y' := by
  ext m
  have h := mem_regularCoderiv_add_iff (F₂ := F₂) (y₀ := y₀ - F₁ x₀) hF (y' := y') (m := m)
  rw [add_sub_cancel] at h
  rw [h]
  constructor
  · intro h'; exact ⟨_, h', by abel_nf⟩
  · rintro ⟨u, hu, rfl⟩; simpa using hu

end RegularSum

section SumRule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The first-order sum rule near `x₀`: for `f` of class `C¹` around `x₀`,
`∂(φ + f)(x) = ∇f(x) + ∂φ(x)` for all `x` near `x₀` [Mordukhovich 2018, Prop. 1.30(ii)]. -/
theorem eventually_subdiff_add_eq {φ : E → EReal} {f : E → ℝ} {f' : E → StrongDual ℝ E}
    {x₀ : E} (hf : ∀ᶠ x in 𝓝 x₀, HasFDerivAt f (f' x) x)
    (hc : ∀ᶠ x in 𝓝 x₀, ContinuousAt f' x) :
    ∀ᶠ x in 𝓝 x₀, subdiff (fun x ↦ φ x + f x) x = (fun y ↦ f' x + y) '' subdiff φ x := by
  filter_upwards [hf.eventually_nhds, hc] with x hx hcx
  ext v
  rw [mem_subdiff_add_iff hx hcx]
  constructor
  · intro h; exact ⟨_, h, by abel_nf⟩
  · rintro ⟨w, hw, rfl⟩; simpa using hw

/-- [Mordukhovich 2024, Prop. 1.51(i), (1.64)] (equality sum rule for second-order
subdifferentials): if `f` is differentiable around `x₀` with gradient `f'` strictly
differentiable around `x₀` and `f''` continuous at `x₀` (e.g. `f ∈ C²`), then
`∂²(φ + f)(x₀, v₀)(u) = ∇²f(x₀) u + ∂²φ(x₀, v₀ - ∇f(x₀))(u)`. -/
theorem secondOrderSubdiff_add [CompleteSpace E] {φ : E → EReal} {f : E → ℝ}
    {f' : E → StrongDual ℝ E} {f'' : E → E →L[ℝ] StrongDual ℝ E} {x₀ : E}
    (hf : ∀ᶠ x in 𝓝 x₀, HasFDerivAt f (f' x) x)
    (hf' : ∀ᶠ x in 𝓝 x₀, HasStrictFDerivAt f' (f'' x) x) (hc : ContinuousAt f'' x₀)
    (v₀ : StrongDual ℝ E) (u : E) :
    secondOrderSubdiff (fun x ↦ φ x + f x) x₀ v₀ u =
      (fun m ↦ f'' x₀ u + m) '' secondOrderSubdiff φ x₀ (v₀ - f' x₀) u := by
  have hsub := eventually_subdiff_add_eq (φ := φ) hf (hf'.mono fun x hx ↦ hx.continuousAt)
  rw [secondOrderSubdiff, coderiv_congr hsub, coderiv_add' hf' hc]
  have hsymm : (NormedSpace.inclusionInDoubleDual ℝ E u).comp (f'' x₀) = f'' x₀ u := by
    ext h
    simp only [comp_apply, NormedSpace.dual_def]
    exact second_derivative_symmetric_of_eventually hf hf'.self_of_nhds.hasFDerivAt h u
  rw [hsymm]
  rfl

/-- [Mordukhovich 2024, Prop. 1.51(ii), (1.65)] (equality sum rule for combined second-order
subdifferentials): if `f` is of class `C¹` around `x₀` and its gradient is Fréchet
differentiable at `x₀`, then `∂̆²(φ + f)(x₀, v₀)(u) = ∇²f(x₀) u + ∂̆²φ(x₀, v₀ - ∇f(x₀))(u)`. -/
theorem combinedSecondOrderSubdiff_add {φ : E → EReal} {f : E → ℝ} {f' : E → StrongDual ℝ E}
    {f'' : E →L[ℝ] StrongDual ℝ E} {x₀ : E} (hf : ∀ᶠ x in 𝓝 x₀, HasFDerivAt f (f' x) x)
    (hc : ∀ᶠ x in 𝓝 x₀, ContinuousAt f' x) (hf' : HasFDerivAt f' f'' x₀)
    (v₀ : StrongDual ℝ E) (u : E) :
    combinedSecondOrderSubdiff (fun x ↦ φ x + f x) x₀ v₀ u =
      (fun m ↦ f'' u + m) '' combinedSecondOrderSubdiff φ x₀ (v₀ - f' x₀) u := by
  rw [combinedSecondOrderSubdiff, regularCoderiv_congr (eventually_subdiff_add_eq hf hc),
    regularCoderiv_add hf']
  have hsymm : (NormedSpace.inclusionInDoubleDual ℝ E u).comp f'' = f'' u := by
    ext h
    simp only [comp_apply, NormedSpace.dual_def]
    exact second_derivative_symmetric_of_eventually hf hf' h u
  rw [hsymm]
  rfl

end SumRule

section Partial

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- [Mordukhovich 2024, (1.66)] (partial subgradient mapping): `∂ₓφ(x, y) = ∂φ(·, y)(x)`. -/
def partialSubdiff (φ : E × F → EReal) (p : E × F) : Set (StrongDual ℝ E) :=
  subdiff (fun x ↦ φ (x, p.2)) p.1

/-- [Mordukhovich 2024, Def. 1.52, (1.67)] (partial second-order subdifferential): for
`v₀ ∈ ∂ₓφ(x₀, y₀)`, `∂²ₓφ(x₀, y₀, v₀)(u) = (D*∂ₓφ)(x₀, y₀, v₀)(u)`, the coderivative of the
partial subgradient mapping `∂ₓφ : E × F ⇉ E*` in both variables. -/
def partialSecondOrderSubdiff (φ : E × F → EReal) (p₀ : E × F) (v₀ : StrongDual ℝ E) (u : E) :
    Set (StrongDual ℝ (E × F)) :=
  coderiv (partialSubdiff φ) p₀ v₀ (NormedSpace.inclusionInDoubleDual ℝ E u)

/-- [Mordukhovich 2024, Def. 1.52, (1.68)] (combined partial second-order subdifferential):
`∂̆²ₓφ(x₀, y₀, v₀)(u) = (D̂*∂ₓφ)(x₀, y₀, v₀)(u)`. -/
def combinedPartialSecondOrderSubdiff (φ : E × F → EReal) (p₀ : E × F) (v₀ : StrongDual ℝ E)
    (u : E) : Set (StrongDual ℝ (E × F)) :=
  regularCoderiv (partialSubdiff φ) p₀ v₀ (NormedSpace.inclusionInDoubleDual ℝ E u)

omit [NormedSpace ℝ F] in
/-- If `φ` has partial gradient `g p` in `x` at every `p` near `p₀`, with `g` continuous near
`p₀`, then `∂ₓφ(p) = {g p}` near `p₀`. -/
theorem eventually_partialSubdiff_eq_singleton {φ : E × F → ℝ} {g : E × F → StrongDual ℝ E}
    {p₀ : E × F} (hφ : ∀ᶠ p in 𝓝 p₀, HasFDerivAt (fun x ↦ φ (x, p.2)) (g p) p.1)
    (hc : ∀ᶠ p in 𝓝 p₀, ContinuousAt g p) :
    ∀ᶠ p in 𝓝 p₀, partialSubdiff (fun p ↦ (φ p : EReal)) p = {g p} := by
  filter_upwards [hφ.eventually_nhds, hc] with p hp hcp
  have hcont : Continuous fun x : E ↦ ((x, p.2) : E × F) := continuous_id.prodMk continuous_const
  have h1 : ∀ᶠ x in 𝓝 p.1, HasFDerivAt (fun x' ↦ φ (x', p.2)) (g (x, p.2)) x := by
    have := (hcont.tendsto p.1).eventually hp
    exact this
  have h2 : ContinuousAt (fun x ↦ g (x, p.2)) p.1 := hcp.comp hcont.continuousAt
  exact subdiff_of_hasFDerivAt_of_continuousAt h1 h2

/-- [Mordukhovich 2024, Prop. 1.53], basic part (partial second-order subdifferentials of `C²`
functions): if `φ` has partial gradient `g p` in `x` for `p` near `p₀`, and `g` is
differentiable around `p₀` with derivative `g'` continuous at `p₀`, then
`∂²ₓφ(p₀)(u) = {⟨u, ∇g(p₀)·⟩}`, i.e. `(h, k) ↦ ∇²ₓₓφ(p₀)(h, u) + ∇²ₓᵧφ(p₀)(k, u)`; the book
writes this as `(∇²ₓₓφ(p₀)* u, ∇²ₓᵧφ(p₀)* u)`. -/
theorem partialSecondOrderSubdiff_of_hasFDerivAt {φ : E × F → ℝ} {g : E × F → StrongDual ℝ E}
    {g' : E × F → E × F →L[ℝ] StrongDual ℝ E} {p₀ : E × F}
    (hφ : ∀ᶠ p in 𝓝 p₀, HasFDerivAt (fun x ↦ φ (x, p.2)) (g p) p.1)
    (hg : ∀ᶠ p in 𝓝 p₀, HasFDerivAt g (g' p) p) (hc : ContinuousAt g' p₀) (u : E) :
    partialSecondOrderSubdiff (fun p ↦ (φ p : EReal)) p₀ (g p₀) u =
      {(NormedSpace.inclusionInDoubleDual ℝ E u).comp (g' p₀)} := by
  rw [partialSecondOrderSubdiff,
    coderiv_congr (eventually_partialSubdiff_eq_singleton hφ (hg.mono fun p hp ↦ hp.continuousAt)),
    coderiv_of_hasFDerivAt_of_continuousAt hg hc]

/-- [Mordukhovich 2024, Prop. 1.53], combined part: under Fréchet differentiability of the
partial gradient `g` at `p₀` (and continuity near `p₀`),
`∂̆²ₓφ(p₀)(u) = {⟨u, ∇g(p₀)·⟩}`. -/
theorem combinedPartialSecondOrderSubdiff_of_hasFDerivAt {φ : E × F → ℝ}
    {g : E × F → StrongDual ℝ E} {g' : E × F →L[ℝ] StrongDual ℝ E} {p₀ : E × F}
    (hφ : ∀ᶠ p in 𝓝 p₀, HasFDerivAt (fun x ↦ φ (x, p.2)) (g p) p.1)
    (hc : ∀ᶠ p in 𝓝 p₀, ContinuousAt g p) (hg : HasFDerivAt g g' p₀) (u : E) :
    combinedPartialSecondOrderSubdiff (fun p ↦ (φ p : EReal)) p₀ (g p₀) u =
      {(NormedSpace.inclusionInDoubleDual ℝ E u).comp g'} := by
  rw [combinedPartialSecondOrderSubdiff,
    regularCoderiv_congr (eventually_partialSubdiff_eq_singleton hφ hc),
    regularCoderiv_of_hasFDerivAt hg]

/-- The partial first-order sum rule near `p₀`: for `f` of class `C¹` around `p₀`,
`∂ₓ(φ + f)(p) = ∇ₓf(p) + ∂ₓφ(p)` for `p` near `p₀`. -/
theorem eventually_partialSubdiff_add_eq {φ : E × F → EReal} {f : E × F → ℝ}
    {f' : E × F → StrongDual ℝ (E × F)} {p₀ : E × F}
    (hf : ∀ᶠ p in 𝓝 p₀, HasFDerivAt f (f' p) p) (hc : ∀ᶠ p in 𝓝 p₀, ContinuousAt f' p) :
    ∀ᶠ p in 𝓝 p₀, partialSubdiff (fun p ↦ φ p + f p) p =
      (fun y ↦ (f' p).comp (inl ℝ E F) + y) '' partialSubdiff φ p := by
  filter_upwards [hf.eventually_nhds, hc.eventually_nhds] with p hp hcp
  have hcont : Continuous fun x : E ↦ ((x, p.2) : E × F) := continuous_id.prodMk continuous_const
  have h1 : ∀ᶠ x in 𝓝 p.1, HasFDerivAt (fun x' ↦ f (x', p.2)) ((f' (x, p.2)).comp (inl ℝ E F))
      x := by
    filter_upwards [(hcont.tendsto p.1).eventually hp] with x hx
    have hin : HasFDerivAt (fun x' : E ↦ ((x', p.2) : E × F)) (inl ℝ E F) x :=
      (hasFDerivAt_id x).prodMk (hasFDerivAt_const _ _)
    exact hx.comp x hin
  have h2 : ContinuousAt (fun x ↦ (f' (x, p.2)).comp (inl ℝ E F)) p.1 :=
    ((hcp.self_of_nhds).comp hcont.continuousAt).clm_comp continuousAt_const
  ext v
  simp only [partialSubdiff]
  rw [mem_subdiff_add_iff (φ := fun x ↦ φ (x, p.2)) h1 h2]
  constructor
  · intro h; exact ⟨_, h, by abel_nf⟩
  · rintro ⟨w, hw, rfl⟩; simpa using hw

/-- The derivative of the partial gradient `p ↦ ∇f(p) ∘ inl`. -/
theorem hasStrictFDerivAt_comp_inl {f' : E × F → StrongDual ℝ (E × F)}
    {f'' : E × F →L[ℝ] StrongDual ℝ (E × F)} {p : E × F} (h : HasStrictFDerivAt f' f'' p) :
    HasStrictFDerivAt (fun p ↦ (f' p).comp (inl ℝ E F))
      ((compL ℝ E (E × F) ℝ).flip (inl ℝ E F) ∘L f'') p :=
  ((compL ℝ E (E × F) ℝ).flip (inl ℝ E F)).hasStrictFDerivAt.comp p h

/-- Fréchet version of `hasStrictFDerivAt_comp_inl`: if `f'` has derivative `f''` at `p`, then the
partial gradient `p ↦ f'(p) ∘ inl` has derivative `w ↦ f''(w) ∘ inl` at `p`. -/
theorem hasFDerivAt_comp_inl {f' : E × F → StrongDual ℝ (E × F)}
    {f'' : E × F →L[ℝ] StrongDual ℝ (E × F)} {p : E × F} (h : HasFDerivAt f' f'' p) :
    HasFDerivAt (fun p ↦ (f' p).comp (inl ℝ E F))
      ((compL ℝ E (E × F) ℝ).flip (inl ℝ E F) ∘L f'') p :=
  ((compL ℝ E (E × F) ℝ).flip (inl ℝ E F)).hasFDerivAt.comp p h

/-- [Mordukhovich 2024, Prop. 1.54(i), (1.69)] (partial second-order sum rule with a smooth
addition): if `f` is differentiable around `p₀` with gradient `f'` strictly differentiable
around `p₀` and `f''` continuous at `p₀`, then
`∂²ₓ(φ + f)(p₀, v₀)(u) = ∇²f(p₀)(u, 0) + ∂²ₓφ(p₀, v₀ - ∇ₓf(p₀))(u)`. The first term is
`(∇²ₓₓf(p₀)* u, ∇²ₓᵧf(p₀)* u)` in the book's notation. -/
theorem partialSecondOrderSubdiff_add [CompleteSpace E] [CompleteSpace F] {φ : E × F → EReal}
    {f : E × F → ℝ} {f' : E × F → StrongDual ℝ (E × F)}
    {f'' : E × F → E × F →L[ℝ] StrongDual ℝ (E × F)} {p₀ : E × F}
    (hf : ∀ᶠ p in 𝓝 p₀, HasFDerivAt f (f' p) p)
    (hf' : ∀ᶠ p in 𝓝 p₀, HasStrictFDerivAt f' (f'' p) p) (hc : ContinuousAt f'' p₀)
    (v₀ : StrongDual ℝ E) (u : E) :
    partialSecondOrderSubdiff (fun p ↦ φ p + f p) p₀ v₀ u =
      (fun m ↦ f'' p₀ (u, 0) + m) ''
        partialSecondOrderSubdiff φ p₀ (v₀ - (f' p₀).comp (inl ℝ E F)) u := by
  have hsub := eventually_partialSubdiff_add_eq (φ := φ) hf
    (hf'.mono fun p hp ↦ hp.continuousAt)
  have hD : ∀ᶠ p in 𝓝 p₀, HasStrictFDerivAt (fun p ↦ (f' p).comp (inl ℝ E F))
      ((compL ℝ E (E × F) ℝ).flip (inl ℝ E F) ∘L f'' p) p :=
    hf'.mono fun p hp ↦ hasStrictFDerivAt_comp_inl hp
  have hDc : ContinuousAt (fun p ↦ (compL ℝ E (E × F) ℝ).flip (inl ℝ E F) ∘L f'' p) p₀ :=
    continuousAt_const.clm_comp hc
  rw [partialSecondOrderSubdiff, coderiv_congr hsub, coderiv_add' hD hDc]
  have hsymm : (NormedSpace.inclusionInDoubleDual ℝ E u).comp
      ((compL ℝ E (E × F) ℝ).flip (inl ℝ E F) ∘L f'' p₀) = f'' p₀ (u, 0) := by
    ext h
    · simp only [comp_apply, NormedSpace.dual_def, flip_apply, compL_apply, inl_apply]
      exact second_derivative_symmetric_of_eventually hf hf'.self_of_nhds.hasFDerivAt _ _
    · simp only [comp_apply, NormedSpace.dual_def, flip_apply, compL_apply, inl_apply]
      exact second_derivative_symmetric_of_eventually hf hf'.self_of_nhds.hasFDerivAt _ _
  rw [hsymm]
  rfl

/-- [Mordukhovich 2024, Prop. 1.54(ii), (1.70)] (combined partial second-order sum rule): if `f`
is of class `C¹` around `p₀` and its gradient is Fréchet differentiable at `p₀`, then
`∂̆²ₓ(φ + f)(p₀, v₀)(u) = ∇²f(p₀)(u, 0) + ∂̆²ₓφ(p₀, v₀ - ∇ₓf(p₀))(u)`. -/
theorem combinedPartialSecondOrderSubdiff_add {φ : E × F → EReal} {f : E × F → ℝ}
    {f' : E × F → StrongDual ℝ (E × F)} {f'' : E × F →L[ℝ] StrongDual ℝ (E × F)} {p₀ : E × F}
    (hf : ∀ᶠ p in 𝓝 p₀, HasFDerivAt f (f' p) p) (hc : ∀ᶠ p in 𝓝 p₀, ContinuousAt f' p)
    (hf' : HasFDerivAt f' f'' p₀) (v₀ : StrongDual ℝ E) (u : E) :
    combinedPartialSecondOrderSubdiff (fun p ↦ φ p + f p) p₀ v₀ u =
      (fun m ↦ f'' (u, 0) + m) ''
        combinedPartialSecondOrderSubdiff φ p₀ (v₀ - (f' p₀).comp (inl ℝ E F)) u := by
  rw [combinedPartialSecondOrderSubdiff,
    regularCoderiv_congr (eventually_partialSubdiff_add_eq hf hc),
    regularCoderiv_add (hasFDerivAt_comp_inl hf')]
  have hsymm : (NormedSpace.inclusionInDoubleDual ℝ E u).comp
      ((compL ℝ E (E × F) ℝ).flip (inl ℝ E F) ∘L f'') = f'' (u, 0) := by
    ext h
    · simp only [comp_apply, NormedSpace.dual_def, flip_apply, compL_apply, inl_apply]
      exact second_derivative_symmetric_of_eventually hf hf' _ _
    · simp only [comp_apply, NormedSpace.dual_def, flip_apply, compL_apply, inl_apply]
      exact second_derivative_symmetric_of_eventually hf hf' _ _
  rw [hsymm]
  rfl

end Partial

end VariationalAnalysis
