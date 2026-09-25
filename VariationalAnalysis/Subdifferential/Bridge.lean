/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import ConvexAnalysis.Convex.Subgradient
import ConvexAnalysis.Differential.Subdifferential
import VariationalAnalysis.Subdifferential.Limiting

/-!
# Comparison with the subdifferentials of `ConvexAnalysis`

`ConvexAnalysis` (the port of OptLib) works with real-valued functions on real inner product
spaces and represents subgradients as vectors. In a Hilbert space `H` the Riesz map
`InnerProductSpace.toDual ℝ H` identifies them with the dual elements used here:

* `toDual_image_subderivAt`: for convex `f`, `SubderivAt f x` (subgradients of convex analysis)
  corresponds to the basic subdifferential `∂f(x)` [Mordukhovich 2018, Prop. 1.25].
* `toDual_image_f_subdifferential`: OptLib's Fréchet subdifferential `f_subdifferential f x` is
  the regular subdifferential `∂̂f(x)` [Mordukhovich 2018, (1.33)].
* `toDual_image_subdifferential`: OptLib's limiting subdifferential `subdifferential f x` is the
  basic subdifferential `∂f(x)`; this is Thm. 1.28 of [Mordukhovich 2018].
-/

open Filter Topology Set InnerProductSpace

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The epigraph of a real-valued convex function is convex. -/
theorem convex_epi_of_convexOn {f : E → ℝ} (hf : ConvexOn ℝ univ f) :
    Convex ℝ ((fun x ↦ (f x : EReal)).Epi univ) := by
  rintro ⟨x, α⟩ ⟨-, hx⟩ ⟨y, β⟩ ⟨-, hy⟩ a b ha hb hab
  refine ⟨mem_univ _, ?_⟩
  rw [EReal.coe_le_coe_iff] at hx hy
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, EReal.coe_le_coe_iff]
  calc f (a • x + b • y) ≤ a * f x + b * f y := by
        simpa using hf.2 (mem_univ x) (mem_univ y) ha hb hab
    _ ≤ a * α + b * β := by gcongr

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "⟪" a ", " b "⟫" => @inner ℝ _ _ a b

/-- Subgradients of a convex function in the sense of `ConvexAnalysis` are its basic
subgradients [Mordukhovich 2018, Prop. 1.25]. -/
theorem toDual_image_subderivAt {f : H → ℝ} (hf : ConvexOn ℝ univ f) (x₀ : H) :
    toDual ℝ H '' SubderivAt f x₀ = subdiff (fun x ↦ (f x : EReal)) x₀ := by
  ext v
  rw [mem_subdiff_of_convex (convex_epi_of_convexOn hf) (r := f x₀) rfl]
  simp only [EReal.coe_le_coe_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩ x
    rw [toDual_apply_apply]
    have := hg x
    linarith
  · intro h
    refine ⟨(toDual ℝ H).symm v, fun x ↦ ?_, by simp⟩
    rw [toDual_symm_apply]
    linarith [h x]

/-- OptLib's Fréchet subdifferential is the regular subdifferential
[Mordukhovich 2018, (1.33)]. -/
theorem toDual_image_f_subdifferential (f : H → ℝ) (x₀ : H) :
    toDual ℝ H '' f_subdifferential f x₀ = regularSubdiff (fun x ↦ (f x : EReal)) x₀ := by
  ext v
  rw [mem_regularSubdiff_coe]
  constructor
  · rintro ⟨g, hg, rfl⟩ ε hε
    filter_upwards [has_f_subdiff_iff.1 hg ε hε] with x hx
    rw [toDual_apply_apply]
    linarith
  · intro h
    refine ⟨(toDual ℝ H).symm v, has_f_subdiff_iff.2 fun ε hε ↦ ?_, by simp⟩
    filter_upwards [h ε hε] with x hx
    rw [toDual_symm_apply]
    linarith

/-- OptLib's limiting subdifferential is the basic subdifferential; this is the limiting
representation of [Mordukhovich 2018, Thm. 1.28]. -/
theorem toDual_image_subdifferential (f : H → ℝ) (x₀ : H) :
    toDual ℝ H '' subdifferential f x₀ = subdiff (fun x ↦ (f x : EReal)) x₀ := by
  rw [subdiff_eq_outerLimit (φ := fun x ↦ (f x : EReal)) (r := f x₀) rfl]
  ext v
  simp only [mem_image, subdifferential, mem_ofPred_eq, mem_outerLimit, tendsto_funNhds_iff,
    EReal.tendsto_coe]
  constructor
  · rintro ⟨g, ⟨u, hu, hfu, w, hw⟩, rfl⟩
    have hwlim : Tendsto w atTop (𝓝 g) := (hw 0).2
    refine ⟨u, fun k ↦ toDual ℝ H (w k), ⟨hu, hfu⟩,
      ((toDual ℝ H).continuous.tendsto g).comp hwlim, fun k ↦ ?_⟩
    rw [← toDual_image_f_subdifferential]
    exact mem_image_of_mem _ (hw k).1
  · rintro ⟨u, w, ⟨hu, hfu⟩, hw, hmem⟩
    refine ⟨(toDual ℝ H).symm v, ⟨u, hu, hfu, fun k ↦ (toDual ℝ H).symm (w k), fun k ↦
      ⟨?_, ((toDual ℝ H).symm.continuous.tendsto v).comp hw⟩⟩, by simp⟩
    have := hmem k
    rw [← toDual_image_f_subdifferential] at this
    obtain ⟨g, hg, hgw⟩ := this
    simpa [← hgw] using hg

end VariationalAnalysis
