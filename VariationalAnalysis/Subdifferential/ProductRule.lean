/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import VariationalAnalysis.Subdifferential.StrictSum
import VariationalAnalysis.Subdifferential.SumRule

/-!
# Product and quotient rules

Cor. 4.7 and Cor. 4.8 of [Mordukhovich 2018]: subgradients of `f₁ f₂` and `f₁ / f₂` for real
functions `f₁, f₂` Lipschitz around `x₀`. As in the book, the first formulas come from
Thm. 4.5(ii) (`subdiff_comp_strict_eq`) applied to `φ(y₁, y₂) = y₁ y₂` and `φ(y₁, y₂) = y₁ / y₂`
with `g = (f₁, f₂)`, and the second ones from the sum rules Cor. 2.20 and Thm. 2.19. The lower
regularity of the product and the quotient uses the regular counterpart of (4.12)
(`mem_regularSubdiff_comp_strict_iff`).

## Main results

* `subdiff_const_mul`, `regularSubdiff_const_mul`, `LowerRegularAt.const_mul`: `∂(t f) = t ∂f`
  for `t > 0`.
* `mem_regularSubdiff_comp_strict_iff`, `lowerRegularAt_comp_strict`: regular subgradients and
  lower regularity in Thm. 4.5(ii) of [Mordukhovich 2018].
* `subdiff_mul_eq`, `subdiff_mul_subset`, `subdiff_mul_eq_add`: Cor. 4.7 (product rules).
* `subdiff_div_eq`, `subdiff_div_subset`, `subdiff_div_eq_add`: Cor. 4.8 (quotient rules). The
  book's second quotient rule has `∂(f₂(x₀) f₁)(x₀) - ∂(f₁(x₀) f₂)(x₀)` in the numerator; the
  correct set is `∂(f₂(x₀) f₁)(x₀) + ∂(-f₁(x₀) f₂)(x₀)` (for `f₁ = 1`, `f₂ = 1 - |x|`,
  `x₀ = 0`, the book's right-hand side is `{-1, 1}` while `∂(f₁ / f₂)(0) = [-1, 1]`).
-/

open Filter Topology Set Metric
open scoped Pointwise NNReal

namespace VariationalAnalysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

section Scaling

variable {f : E → ℝ} {x₀ : E} {t : ℝ}

/-- `v ∈ ∂̂f(x₀)` implies `t v ∈ ∂̂(t f)(x₀)` for `t > 0`. -/
theorem smul_mem_regularSubdiff_const_mul (ht : 0 < t) {v : StrongDual ℝ E}
    (hv : v ∈ regularSubdiff (fun x ↦ (f x : EReal)) x₀) :
    t • v ∈ regularSubdiff (fun x ↦ ((t * f x : ℝ) : EReal)) x₀ := by
  rw [mem_regularSubdiff_coe] at hv ⊢
  intro ε hε
  filter_upwards [hv (ε / t) (div_pos hε ht)] with x hx
  have := mul_le_mul_of_nonneg_left hx ht.le
  simp only [smul_apply, smul_eq_mul]
  have e : t * (f x₀ + v (x - x₀) - ε / t * ‖x - x₀‖) =
      t * f x₀ + t * v (x - x₀) - ε * ‖x - x₀‖ := by field_simp
  linarith

/-- `∂̂(t f)(x₀) = t ∂̂f(x₀)` for `t > 0`. -/
theorem regularSubdiff_const_mul (ht : 0 < t) :
    regularSubdiff (fun x ↦ ((t * f x : ℝ) : EReal)) x₀ =
      t • regularSubdiff (fun x ↦ (f x : EReal)) x₀ := by
  refine subset_antisymm (fun v hv ↦ ⟨t⁻¹ • v, ?_, by simp [smul_smul, ht.ne']⟩) ?_
  · rintro _ ⟨v, hv, rfl⟩
    exact smul_mem_regularSubdiff_const_mul ht hv
  · have := smul_mem_regularSubdiff_const_mul (inv_pos.2 ht) hv
    simpa [← mul_assoc, inv_mul_cancel₀ ht.ne'] using this

/-- `v ∈ ∂f(x₀)` implies `t v ∈ ∂(t f)(x₀)` for `t > 0`. -/
theorem smul_mem_subdiff_const_mul (ht : 0 < t) {v : StrongDual ℝ E}
    (hv : v ∈ subdiff (fun x ↦ (f x : EReal)) x₀) :
    t • v ∈ subdiff (fun x ↦ ((t * f x : ℝ) : EReal)) x₀ := by
  rw [subdiff_eq_outerLimit (φ := fun x ↦ (f x : EReal)) (r := f x₀) rfl] at hv
  rw [subdiff_eq_outerLimit (φ := fun x ↦ ((t * f x : ℝ) : EReal)) (r := t * f x₀) rfl]
  obtain ⟨a, w, ha, hw, hmem⟩ := hv
  obtain ⟨ha1, ha2⟩ := tendsto_funNhds_iff.1 ha
  refine ⟨a, fun k ↦ t • w k, tendsto_funNhds_iff.2 ⟨ha1, ?_⟩, hw.const_smul t,
    fun k ↦ smul_mem_regularSubdiff_const_mul ht (hmem k)⟩
  exact EReal.tendsto_coe.2 ((EReal.tendsto_coe.1 ha2).const_mul t)

/-- `∂(t f)(x₀) = t ∂f(x₀)` for `t > 0`. -/
theorem subdiff_const_mul (ht : 0 < t) :
    subdiff (fun x ↦ ((t * f x : ℝ) : EReal)) x₀ = t • subdiff (fun x ↦ (f x : EReal)) x₀ := by
  refine subset_antisymm (fun v hv ↦ ⟨t⁻¹ • v, ?_, by simp [smul_smul, ht.ne']⟩) ?_
  · rintro _ ⟨v, hv, rfl⟩
    exact smul_mem_subdiff_const_mul ht hv
  · have := smul_mem_subdiff_const_mul (inv_pos.2 ht) hv
    simpa [← mul_assoc, inv_mul_cancel₀ ht.ne'] using this

/-- Lower regularity is preserved by multiplication with `t > 0`. -/
theorem LowerRegularAt.const_mul (ht : 0 < t) (h : LowerRegularAt (fun x ↦ (f x : EReal)) x₀) :
    LowerRegularAt (fun x ↦ ((t * f x : ℝ) : EReal)) x₀ := by
  unfold LowerRegularAt at h ⊢
  rw [subdiff_const_mul ht, regularSubdiff_const_mul ht, h]

end Scaling

section Lipschitz

omit [NormedSpace ℝ E] in
/-- `x ↦ a f(x)` is `|a| K`-Lipschitz on `U` if `f` is `K`-Lipschitz on `U`. -/
theorem lipschitzOnWith_const_mul {f : E → ℝ} {U : Set E} {K : ℝ≥0} (hf : LipschitzOnWith K f U)
    (a : ℝ) : LipschitzOnWith (‖a‖₊ * K) (fun x ↦ a * f x) U := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  rw [Real.dist_eq, ← mul_sub, abs_mul, ← Real.dist_eq]
  have := hf.dist_le_mul x hx y hy
  push_cast
  rw [mul_assoc, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left this (abs_nonneg a)

end Lipschitz

section StrictChain

open ContinuousLinearMap in
/-- Regular subgradients in Thm. 4.5(ii) of [Mordukhovich 2018]: for `g` Lipschitz around `x₀`
and `φ : E × F → ℝ` strictly differentiable at `(x₀, g x₀)`,
`∂̂(φ ∘ (I, g))(x₀) = ∇ₓφ(x₀, g x₀) + ∂̂⟨∇ᵧφ(x₀, g x₀), g⟩(x₀)`. -/
theorem mem_regularSubdiff_comp_strict_iff {g : E → F} {U : Set E} {x₀ : E} (hU : U ∈ 𝓝 x₀)
    {K : ℝ≥0} (hg : LipschitzOnWith K g U) {φ : E × F → ℝ} {φ' : StrongDual ℝ (E × F)}
    (hφ : HasStrictFDerivAt φ φ' (x₀, g x₀)) {v : StrongDual ℝ E} :
    v ∈ regularSubdiff (fun x ↦ ((φ (x, g x) : ℝ) : EReal)) x₀ ↔
      v - φ'.comp (inl ℝ E F) ∈
        regularSubdiff (fun x ↦ ((φ'.comp (inr ℝ E F) (g x) : ℝ) : EReal)) x₀ := by
  have h := mem_regularSubdiff_add_iff (v := v)
    (φ := fun x ↦ ((φ'.comp (inr ℝ E F) (g x) : ℝ) : EReal))
    (hasStrictFDerivAt_comp_sub_comp_inr hU hg hφ).hasFDerivAt
  have hfun : (fun x ↦ ((φ'.comp (inr ℝ E F) (g x) : ℝ) : EReal) +
      ((φ (x, g x) - φ'.comp (inr ℝ E F) (g x) : ℝ) : EReal)) =
      fun x ↦ ((φ (x, g x) : ℝ) : EReal) := by
    funext x; rw [← EReal.coe_add]; congr 1; ring
  rwa [hfun] at h

open ContinuousLinearMap in
/-- Lower regularity in Thm. 4.5(ii) of [Mordukhovich 2018]: under the assumptions of
`mem_regularSubdiff_comp_strict_iff`, if `⟨∇ᵧφ(x₀, g x₀), g⟩` is lower regular at `x₀`, then so is
`φ ∘ (I, g)` (finite dimensions). -/
theorem lowerRegularAt_comp_strict [FiniteDimensional ℝ E] {g : E → F} {U : Set E} {x₀ : E}
    (hU : U ∈ 𝓝 x₀) {K : ℝ≥0} (hg : LipschitzOnWith K g U) {φ : E × F → ℝ}
    {φ' : StrongDual ℝ (E × F)} (hφ : HasStrictFDerivAt φ φ' (x₀, g x₀))
    (hreg : LowerRegularAt (fun x ↦ ((φ'.comp (inr ℝ E F) (g x) : ℝ) : EReal)) x₀) :
    LowerRegularAt (fun x ↦ ((φ (x, g x) : ℝ) : EReal)) x₀ := by
  refine subset_antisymm (fun v hv ↦ ?_) regularSubdiff_subset_subdiff
  rw [mem_subdiff_comp_strict_iff hU hg hφ, hreg] at hv
  exact (mem_regularSubdiff_comp_strict_iff hU hg hφ).2 hv

end StrictChain

section Product

variable [FiniteDimensional ℝ E]
variable {f₁ f₂ : E → ℝ} {x₀ : E} {U₁ U₂ : Set E} {K₁ K₂ : ℝ≥0}

open ContinuousLinearMap in
omit [FiniteDimensional ℝ E] in
/-- The strict derivative of `(x, (y₁, y₂)) ↦ y₁ y₂` at `(x₀, (a, b))`. -/
theorem hasStrictFDerivAt_mul_snd (a b : ℝ) :
    HasStrictFDerivAt (fun p : E × (ℝ × ℝ) ↦ p.2.1 * p.2.2)
      (a • (snd ℝ ℝ ℝ).comp (snd ℝ E (ℝ × ℝ)) + b • (fst ℝ ℝ ℝ).comp (snd ℝ E (ℝ × ℝ)))
      (x₀, (a, b)) := by
  have h1 : HasStrictFDerivAt (fun p : E × (ℝ × ℝ) ↦ p.2.1)
      ((fst ℝ ℝ ℝ).comp (snd ℝ E (ℝ × ℝ))) (x₀, (a, b)) :=
    ((fst ℝ ℝ ℝ).comp (snd ℝ E (ℝ × ℝ))).hasStrictFDerivAt
  have h2 : HasStrictFDerivAt (fun p : E × (ℝ × ℝ) ↦ p.2.2)
      ((snd ℝ ℝ ℝ).comp (snd ℝ E (ℝ × ℝ))) (x₀, (a, b)) :=
    ((snd ℝ ℝ ℝ).comp (snd ℝ E (ℝ × ℝ))).hasStrictFDerivAt
  exact h1.mul h2

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- `(f₁, f₂)` is Lipschitz on `U₁ ∩ U₂`. -/
theorem lipschitzOnWith_prodMk (hL₁ : LipschitzOnWith K₁ f₁ U₁) (hL₂ : LipschitzOnWith K₂ f₂ U₂) :
    LipschitzOnWith (max K₁ K₂) (fun x ↦ (f₁ x, f₂ x)) (U₁ ∩ U₂) :=
  (hL₁.mono inter_subset_left).prodMk (hL₂.mono inter_subset_right)

open ContinuousLinearMap in
/-- Cor. 4.7 of [Mordukhovich 2018] (product rule), first formula: for `f₁, f₂` Lipschitz around
`x₀`, `∂(f₁ f₂)(x₀) = ∂(f₂(x₀) f₁ + f₁(x₀) f₂)(x₀)` (from Thm. 4.5(ii)). -/
theorem subdiff_mul_eq (hU₁ : U₁ ∈ 𝓝 x₀) (hL₁ : LipschitzOnWith K₁ f₁ U₁) (hU₂ : U₂ ∈ 𝓝 x₀)
    (hL₂ : LipschitzOnWith K₂ f₂ U₂) :
    subdiff (fun x ↦ ((f₁ x * f₂ x : ℝ) : EReal)) x₀ =
      subdiff (fun x ↦ ((f₂ x₀ * f₁ x + f₁ x₀ * f₂ x : ℝ) : EReal)) x₀ := by
  have h := subdiff_comp_strict_eq (g := fun x ↦ (f₁ x, f₂ x)) (inter_mem hU₁ hU₂)
    (lipschitzOnWith_prodMk hL₁ hL₂) (hasStrictFDerivAt_mul_snd (x₀ := x₀) (f₁ x₀) (f₂ x₀))
  refine h.trans ?_
  have h0 : (f₁ x₀ • (snd ℝ ℝ ℝ).comp (snd ℝ E (ℝ × ℝ)) +
      f₂ x₀ • (fst ℝ ℝ ℝ).comp (snd ℝ E (ℝ × ℝ))).comp (inl ℝ E (ℝ × ℝ)) = 0 := by
    ext; simp
  rw [h0]
  simp only [zero_add, image_id']
  congr 1
  funext x
  simp only [EReal.coe_eq_coe_iff]
  simp
  ring

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem locallyClosed_epi_const_mul (hU₁ : U₁ ∈ 𝓝 x₀) (hL₁ : LipschitzOnWith K₁ f₁ U₁) (c r : ℝ) :
    ∃ ρ > 0, IsClosed ((fun x ↦ ((c * f₁ x : ℝ) : EReal)).Epi univ ∩
      closedBall ((x₀, r) : E × ℝ) ρ) :=
  locallyClosed_epi_of_continuousOn hU₁ (lipschitzOnWith_const_mul hL₁ c).continuousOn r

omit [FiniteDimensional ℝ E] in
theorem singularSubdiff_const_mul_eq_zero (hU₁ : U₁ ∈ 𝓝 x₀) (hL₁ : LipschitzOnWith K₁ f₁ U₁)
    (c : ℝ) : singularSubdiff (fun x ↦ ((c * f₁ x : ℝ) : EReal)) x₀ = {0} :=
  singularSubdiff_eq_zero_of_lipschitz hU₁ (lipschitzOnWith_const_mul hL₁ c)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem coe_add_fun (c₁ c₂ : ℝ) :
    (fun x ↦ ((c₁ * f₁ x + c₂ * f₂ x : ℝ) : EReal)) =
      fun x ↦ ((c₁ * f₁ x : ℝ) : EReal) + ((c₂ * f₂ x : ℝ) : EReal) :=
  funext fun _ ↦ EReal.coe_add _ _

/-- Cor. 4.7 of [Mordukhovich 2018] (product rule), second formula: for `f₁, f₂` Lipschitz around
`x₀`, `∂(f₁ f₂)(x₀) ⊆ ∂(f₂(x₀) f₁)(x₀) + ∂(f₁(x₀) f₂)(x₀)` (Cor. 2.20). -/
theorem subdiff_mul_subset (hU₁ : U₁ ∈ 𝓝 x₀) (hL₁ : LipschitzOnWith K₁ f₁ U₁) (hU₂ : U₂ ∈ 𝓝 x₀)
    (hL₂ : LipschitzOnWith K₂ f₂ U₂) :
    subdiff (fun x ↦ ((f₁ x * f₂ x : ℝ) : EReal)) x₀ ⊆
      subdiff (fun x ↦ ((f₂ x₀ * f₁ x : ℝ) : EReal)) x₀ +
        subdiff (fun x ↦ ((f₁ x₀ * f₂ x : ℝ) : EReal)) x₀ := by
  rw [subdiff_mul_eq hU₁ hL₁ hU₂ hL₂, coe_add_fun]
  exact subdiff_add_subset_of_lipschitz (φ := fun x ↦ ((f₂ x₀ * f₁ x : ℝ) : EReal))
    (f := fun x ↦ f₁ x₀ * f₂ x) rfl (locallyClosed_epi_const_mul hU₁ hL₁ _ _) hU₂
    (lipschitzOnWith_const_mul hL₂ _)

open ContinuousLinearMap in
/-- Cor. 4.7 of [Mordukhovich 2018] (product rule), equality statement: if moreover
`f₂(x₀) f₁` and `f₁(x₀) f₂` are lower regular at `x₀`, then
`∂(f₁ f₂)(x₀) = ∂(f₂(x₀) f₁)(x₀) + ∂(f₁(x₀) f₂)(x₀)` and `f₁ f₂` is lower regular at `x₀`
(Thm. 2.19 and Thm. 4.5(ii)). -/
theorem subdiff_mul_eq_add (hU₁ : U₁ ∈ 𝓝 x₀) (hL₁ : LipschitzOnWith K₁ f₁ U₁)
    (hU₂ : U₂ ∈ 𝓝 x₀) (hL₂ : LipschitzOnWith K₂ f₂ U₂)
    (hreg₁ : LowerRegularAt (fun x ↦ ((f₂ x₀ * f₁ x : ℝ) : EReal)) x₀)
    (hreg₂ : LowerRegularAt (fun x ↦ ((f₁ x₀ * f₂ x : ℝ) : EReal)) x₀) :
    subdiff (fun x ↦ ((f₁ x * f₂ x : ℝ) : EReal)) x₀ =
        subdiff (fun x ↦ ((f₂ x₀ * f₁ x : ℝ) : EReal)) x₀ +
          subdiff (fun x ↦ ((f₁ x₀ * f₂ x : ℝ) : EReal)) x₀ ∧
      LowerRegularAt (fun x ↦ ((f₁ x * f₂ x : ℝ) : EReal)) x₀ := by
  obtain ⟨heq, hreg⟩ := subdiff_add_eq (φ₁ := fun x ↦ ((f₂ x₀ * f₁ x : ℝ) : EReal))
    (φ₂ := fun x ↦ ((f₁ x₀ * f₂ x : ℝ) : EReal)) rfl rfl
    (locallyClosed_epi_const_mul hU₁ hL₁ _ _) (locallyClosed_epi_const_mul hU₂ hL₂ _ _)
    (fun v hv _ ↦ by rwa [singularSubdiff_const_mul_eq_zero hU₁ hL₁] at hv) hreg₁ hreg₂
  refine ⟨by rw [subdiff_mul_eq hU₁ hL₁ hU₂ hL₂, coe_add_fun]; exact heq, ?_⟩
  refine lowerRegularAt_comp_strict (g := fun x ↦ (f₁ x, f₂ x)) (inter_mem hU₁ hU₂)
    (lipschitzOnWith_prodMk hL₁ hL₂) (hasStrictFDerivAt_mul_snd (x₀ := x₀) (f₁ x₀) (f₂ x₀)) ?_
  convert hreg using 2 with x
  rw [← EReal.coe_add, EReal.coe_eq_coe_iff]
  simp
  ring

open ContinuousLinearMap in
omit [FiniteDimensional ℝ E] in
/-- The strict derivative of `(x, (y₁, y₂)) ↦ y₁ / y₂` at `(x₀, (a, b))`, `b ≠ 0`. -/
theorem hasStrictFDerivAt_div_snd (a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    HasStrictFDerivAt (fun p : E × (ℝ × ℝ) ↦ p.2.1 * (p.2.2)⁻¹)
      (a • (toSpanSingleton ℝ (-(b ^ 2)⁻¹)).comp ((snd ℝ ℝ ℝ).comp (snd ℝ E (ℝ × ℝ))) +
        b⁻¹ • (fst ℝ ℝ ℝ).comp (snd ℝ E (ℝ × ℝ))) (x₀, (a, b)) := by
  have h1 : HasStrictFDerivAt (fun p : E × (ℝ × ℝ) ↦ p.2.1)
      ((fst ℝ ℝ ℝ).comp (snd ℝ E (ℝ × ℝ))) (x₀, (a, b)) :=
    ((fst ℝ ℝ ℝ).comp (snd ℝ E (ℝ × ℝ))).hasStrictFDerivAt
  have h2 : HasStrictFDerivAt (fun p : E × (ℝ × ℝ) ↦ p.2.2)
      ((snd ℝ ℝ ℝ).comp (snd ℝ E (ℝ × ℝ))) (x₀, (a, b)) :=
    ((snd ℝ ℝ ℝ).comp (snd ℝ E (ℝ × ℝ))).hasStrictFDerivAt
  have h3 : HasStrictFDerivAt (fun p : E × (ℝ × ℝ) ↦ (p.2.2)⁻¹)
      ((toSpanSingleton ℝ (-(b ^ 2)⁻¹)).comp ((snd ℝ ℝ ℝ).comp (snd ℝ E (ℝ × ℝ))))
      (x₀, (a, b)) :=
    (hasStrictFDerivAt_inv (𝕜 := ℝ) hb).comp (x₀, (a, b)) h2
  exact h1.mul h3

open ContinuousLinearMap in
/-- Cor. 4.8 of [Mordukhovich 2018] (quotient rule), first formula: for `f₁, f₂` Lipschitz around
`x₀` with `f₂(x₀) ≠ 0`,
`∂(f₁ / f₂)(x₀) = ∂(f₂(x₀) f₁ - f₁(x₀) f₂)(x₀) / f₂(x₀)²`. -/
theorem subdiff_div_eq (hU₁ : U₁ ∈ 𝓝 x₀) (hL₁ : LipschitzOnWith K₁ f₁ U₁) (hU₂ : U₂ ∈ 𝓝 x₀)
    (hL₂ : LipschitzOnWith K₂ f₂ U₂) (hb : f₂ x₀ ≠ 0) :
    subdiff (fun x ↦ ((f₁ x / f₂ x : ℝ) : EReal)) x₀ =
      (f₂ x₀ ^ 2)⁻¹ • subdiff (fun x ↦ ((f₂ x₀ * f₁ x + (-f₁ x₀) * f₂ x : ℝ) : EReal)) x₀ := by
  have h := subdiff_comp_strict_eq (g := fun x ↦ (f₁ x, f₂ x)) (inter_mem hU₁ hU₂)
    (lipschitzOnWith_prodMk hL₁ hL₂) (hasStrictFDerivAt_div_snd (x₀ := x₀) (f₁ x₀) hb)
  simp only [← div_eq_mul_inv] at h
  rw [h, ← subdiff_const_mul (inv_pos.2 (by positivity))]
  have h0 : (f₁ x₀ • (toSpanSingleton ℝ (-(f₂ x₀ ^ 2)⁻¹)).comp
      ((snd ℝ ℝ ℝ).comp (snd ℝ E (ℝ × ℝ))) +
      (f₂ x₀)⁻¹ • (fst ℝ ℝ ℝ).comp (snd ℝ E (ℝ × ℝ))).comp (inl ℝ E (ℝ × ℝ)) = 0 := by
    ext; simp
  rw [h0]
  simp only [zero_add, image_id']
  congr 1
  funext x
  simp only [EReal.coe_eq_coe_iff]
  simp
  field_simp
  ring

/-- Cor. 4.8 of [Mordukhovich 2018] (quotient rule), second formula: for `f₁, f₂` Lipschitz
around `x₀` with `f₂(x₀) ≠ 0`,
`∂(f₁ / f₂)(x₀) ⊆ [∂(f₂(x₀) f₁)(x₀) + ∂(-f₁(x₀) f₂)(x₀)] / f₂(x₀)²`. The book writes the second
summand as `-∂(f₁(x₀) f₂)(x₀)`; since `∂(-h) ≠ -∂h` in general, the correct term is
`∂(-f₁(x₀) f₂)(x₀)` (as in the book's regularity condition). -/
theorem subdiff_div_subset (hU₁ : U₁ ∈ 𝓝 x₀) (hL₁ : LipschitzOnWith K₁ f₁ U₁) (hU₂ : U₂ ∈ 𝓝 x₀)
    (hL₂ : LipschitzOnWith K₂ f₂ U₂) (hb : f₂ x₀ ≠ 0) :
    subdiff (fun x ↦ ((f₁ x / f₂ x : ℝ) : EReal)) x₀ ⊆
      (f₂ x₀ ^ 2)⁻¹ • (subdiff (fun x ↦ ((f₂ x₀ * f₁ x : ℝ) : EReal)) x₀ +
        subdiff (fun x ↦ ((-f₁ x₀ * f₂ x : ℝ) : EReal)) x₀) := by
  rw [subdiff_div_eq hU₁ hL₁ hU₂ hL₂ hb, coe_add_fun]
  exact Set.smul_set_mono (subdiff_add_subset_of_lipschitz
    (φ := fun x ↦ ((f₂ x₀ * f₁ x : ℝ) : EReal)) (f := fun x ↦ -f₁ x₀ * f₂ x) rfl
    (locallyClosed_epi_const_mul hU₁ hL₁ _ _) hU₂ (lipschitzOnWith_const_mul hL₂ _))

open ContinuousLinearMap in
/-- Cor. 4.8 of [Mordukhovich 2018] (quotient rule), equality statement: if moreover
`f₂(x₀) f₁` and `-f₁(x₀) f₂` are lower regular at `x₀`, then
`∂(f₁ / f₂)(x₀) = [∂(f₂(x₀) f₁)(x₀) + ∂(-f₁(x₀) f₂)(x₀)] / f₂(x₀)²` and `f₁ / f₂` is lower
regular at `x₀`. -/
theorem subdiff_div_eq_add (hU₁ : U₁ ∈ 𝓝 x₀) (hL₁ : LipschitzOnWith K₁ f₁ U₁)
    (hU₂ : U₂ ∈ 𝓝 x₀) (hL₂ : LipschitzOnWith K₂ f₂ U₂) (hb : f₂ x₀ ≠ 0)
    (hreg₁ : LowerRegularAt (fun x ↦ ((f₂ x₀ * f₁ x : ℝ) : EReal)) x₀)
    (hreg₂ : LowerRegularAt (fun x ↦ ((-f₁ x₀ * f₂ x : ℝ) : EReal)) x₀) :
    subdiff (fun x ↦ ((f₁ x / f₂ x : ℝ) : EReal)) x₀ =
        (f₂ x₀ ^ 2)⁻¹ • (subdiff (fun x ↦ ((f₂ x₀ * f₁ x : ℝ) : EReal)) x₀ +
          subdiff (fun x ↦ ((-f₁ x₀ * f₂ x : ℝ) : EReal)) x₀) ∧
      LowerRegularAt (fun x ↦ ((f₁ x / f₂ x : ℝ) : EReal)) x₀ := by
  obtain ⟨heq, hreg⟩ := subdiff_add_eq (φ₁ := fun x ↦ ((f₂ x₀ * f₁ x : ℝ) : EReal))
    (φ₂ := fun x ↦ ((-f₁ x₀ * f₂ x : ℝ) : EReal)) rfl rfl
    (locallyClosed_epi_const_mul hU₁ hL₁ _ _) (locallyClosed_epi_const_mul hU₂ hL₂ _ _)
    (fun v hv _ ↦ by rwa [singularSubdiff_const_mul_eq_zero hU₁ hL₁] at hv) hreg₁ hreg₂
  refine ⟨by rw [subdiff_div_eq hU₁ hL₁ hU₂ hL₂ hb, coe_add_fun, heq], ?_⟩
  rw [← coe_add_fun] at hreg
  have hreg' := hreg.const_mul (t := (f₂ x₀ ^ 2)⁻¹) (inv_pos.2 (by positivity))
  simp only [div_eq_mul_inv]
  refine lowerRegularAt_comp_strict (g := fun x ↦ (f₁ x, f₂ x)) (inter_mem hU₁ hU₂)
    (lipschitzOnWith_prodMk hL₁ hL₂) (hasStrictFDerivAt_div_snd (x₀ := x₀) (f₁ x₀) hb) ?_
  convert hreg' using 2 with x
  rw [EReal.coe_eq_coe_iff]
  simp
  field_simp
  ring

end Product

end VariationalAnalysis
