/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Auxiliary lemmas

Small facts used throughout the library: passing to the limit in `vₖ xₖ` for dual vectors,
"`a ≤ b + ε c` for all `ε > 0`" arguments, and directional limits along rays `x₀ + t • d`.
-/

open Filter Topology Set

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If `vₖ → v` in the dual and `xₖ → x`, then `vₖ xₖ → v x`. -/
theorem tendsto_dual_apply {α : Type*} {l : Filter α} {v : α → StrongDual ℝ E}
    {v₀ : StrongDual ℝ E} {x : α → E} {x₀ : E} (hv : Tendsto v l (𝓝 v₀))
    (hx : Tendsto x l (𝓝 x₀)) : Tendsto (fun k ↦ v k (x k)) l (𝓝 (v₀ x₀)) :=
  ((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := ℝ)).continuous.tendsto (v₀, x₀)).comp
    (hv.prodMk_nhds hx)

/-- If `a ≤ b + ε * c` for every `ε > 0`, then `a ≤ b`. -/
theorem le_of_forall_pos_le_add_mul {a b c : ℝ} (h : ∀ ε > 0, a ≤ b + ε * c) : a ≤ b := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  rcases le_or_gt c 0 with hc | hc
  · exact (h 1 one_pos).trans (by nlinarith)
  · have := h (ε / c) (div_pos hε hc)
    rwa [div_mul_cancel₀ _ hc.ne'] at this

/-- Directional limits. If `v (x - x₀) ≤ c ‖x - x₀‖` for `x` near `x₀` in `Ω`, and the ray
`x₀ + t • d` stays in `Ω` for small `t > 0`, then `v d ≤ c ‖d‖`. -/
theorem le_of_eventually_ray {Ω : Set E} {x₀ d : E} {v : StrongDual ℝ E} {c : ℝ}
    (hv : ∀ᶠ x in 𝓝[Ω] x₀, v (x - x₀) ≤ c * ‖x - x₀‖)
    (hray : ∀ᶠ t in 𝓝[>] (0 : ℝ), x₀ + t • d ∈ Ω) : v d ≤ c * ‖d‖ := by
  have hT : Tendsto (fun t : ℝ ↦ x₀ + t • d) (𝓝[>] 0) (𝓝[Ω] x₀) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hray⟩
    have : Tendsto (fun t : ℝ ↦ x₀ + t • d) (𝓝 0) (𝓝 (x₀ + (0 : ℝ) • d)) :=
      ((continuous_id.smul continuous_const).const_add x₀).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  obtain ⟨t, ht, ht0⟩ := ((hT.eventually hv).and self_mem_nhdsWithin).exists
  simp only [add_sub_cancel_left, map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (show (0 : ℝ) < t from ht0)] at ht
  nlinarith [mul_comm c t]

section Product

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `(v, c) ↦ v.coprod c` is continuous: dual elements on `E × F` depend continuously on their
two components. -/
theorem tendsto_coprod {α : Type*} {l : Filter α} {v : α → StrongDual ℝ E}
    {c : α → StrongDual ℝ F} {v₀ : StrongDual ℝ E} {c₀ : StrongDual ℝ F}
    (hv : Tendsto v l (𝓝 v₀)) (hc : Tendsto c l (𝓝 c₀)) :
    Tendsto (fun k ↦ (v k).coprod (c k)) l (𝓝 (v₀.coprod c₀)) :=
  ((ContinuousLinearMap.coprodEquivL (S := ℝ)).continuous.tendsto (v₀, c₀)).comp
    (hv.prodMk_nhds hc)

/-- `ℓ ↦ ℓ ∘ inl` is continuous. -/
theorem tendsto_comp_inl {α : Type*} {l : Filter α} {ℓ : α → StrongDual ℝ (E × F)}
    {ℓ₀ : StrongDual ℝ (E × F)} (h : Tendsto ℓ l (𝓝 ℓ₀)) :
    Tendsto (fun k ↦ (ℓ k).comp (ContinuousLinearMap.inl ℝ E F)) l
      (𝓝 (ℓ₀.comp (ContinuousLinearMap.inl ℝ E F))) :=
  (((ContinuousLinearMap.inl ℝ E F).precomp ℝ).continuous.tendsto ℓ₀).comp h

/-- `ℓ ↦ ℓ ∘ inr` is continuous. -/
theorem tendsto_comp_inr {α : Type*} {l : Filter α} {ℓ : α → StrongDual ℝ (E × F)}
    {ℓ₀ : StrongDual ℝ (E × F)} (h : Tendsto ℓ l (𝓝 ℓ₀)) :
    Tendsto (fun k ↦ (ℓ k).comp (ContinuousLinearMap.inr ℝ E F)) l
      (𝓝 (ℓ₀.comp (ContinuousLinearMap.inr ℝ E F))) :=
  (((ContinuousLinearMap.inr ℝ E F).precomp ℝ).continuous.tendsto ℓ₀).comp h

/-- `(v, A) ↦ v ∘ A` is continuous. -/
theorem tendsto_dual_comp {α : Type*} {l : Filter α} {v : α → StrongDual ℝ F}
    {A : α → E →L[ℝ] F} {v₀ : StrongDual ℝ F} {A₀ : E →L[ℝ] F} (hv : Tendsto v l (𝓝 v₀))
    (hA : Tendsto A l (𝓝 A₀)) : Tendsto (fun k ↦ (v k).comp (A k)) l (𝓝 (v₀.comp A₀)) :=
  ((isBoundedBilinearMap_comp (𝕜 := ℝ) (E := E) (F := F) (G := ℝ)).continuous.tendsto
    (v₀, A₀)).comp (hv.prodMk_nhds hA)

/-- A dual element `ℓ` on `E × ℝ` with `ℓ (0, 1) = -1` is `(ℓ ∘ inl, -1)`. -/
theorem eq_coprod_neg_one (ℓ : StrongDual ℝ (E × ℝ)) (h : ℓ (0, 1) = -1) :
    ℓ = (ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ)).coprod (-1) := by
  conv_lhs => rw [← ContinuousLinearMap.coprod_comp_inl_inr ℓ]
  congr 1
  ext
  simp [h]

/-- A dual element `ℓ` on `E × ℝ` with `ℓ (0, 1) = 0` is `(ℓ ∘ inl, 0)`. -/
theorem eq_coprod_zero (ℓ : StrongDual ℝ (E × ℝ)) (h : ℓ (0, 1) = 0) :
    ℓ = (ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ)).coprod 0 := by
  conv_lhs => rw [← ContinuousLinearMap.coprod_comp_inl_inr ℓ]
  congr 1
  ext
  simp [h]

end Product

end VariationalAnalysis
