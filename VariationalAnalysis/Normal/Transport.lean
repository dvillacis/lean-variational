/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import VariationalAnalysis.Normal.Projection

/-!
# Normals under linear isomorphisms; finite-dimensional normed spaces

Normal cones pull back along continuous linear isomorphisms `A : E ≃L[ℝ] F`: `v` is a normal to
`A '' Ω` at `A x₀` iff `v ∘ A` is a normal to `Ω` at `x₀`, while `ω`-normals pick up the factor
`‖A‖`. Through `toEuclidean`, this transfers the results of `VariationalAnalysis.Normal.Projection`
from Euclidean spaces to every finite-dimensional real normed space, e.g. to `E × ℝ` with its
product norm, where epigraphs live.

## Main results

* `comp_mem_epsNormalCone_of_mem_image`, `mem_normalCone_image_iff`: pullback of normals.
* `normalCone_eq_outerLimit_epsNormalCone`: Thm. 1.6, second representation in (1.7), of
  [Mordukhovich 2018] in finite-dimensional normed spaces.
* `exists_ne_zero_mem_normalCone_iff`: Prop. 1.2 of [Mordukhovich 2018] in finite-dimensional
  normed spaces.
-/

open Filter Topology Set Metric

namespace VariationalAnalysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {Ω : Set E} {x₀ : E}

section Pullback

variable (A : E ≃L[ℝ] F)

theorem tendsto_image_nhdsWithin : Tendsto A (𝓝[Ω] x₀) (𝓝[A '' Ω] (A x₀)) :=
  tendsto_nhdsWithin_iff.2 ⟨(A.continuous.tendsto x₀).mono_left nhdsWithin_le_nhds,
    eventually_nhdsWithin_of_forall fun _ hx ↦ mem_image_of_mem _ hx⟩

/-- `ω`-normals pull back along a linear isomorphism, with the enlargement scaled by `‖A‖`. -/
theorem comp_mem_epsNormalCone_of_mem_image {v : StrongDual ℝ F} {ω : ℝ} (hω : 0 ≤ ω)
    (hv : v ∈ epsNormalCone ω (A '' Ω) (A x₀)) :
    v.comp (A : E →L[ℝ] F) ∈ epsNormalCone (ω * ‖(A : E →L[ℝ] F)‖) Ω x₀ := by
  refine ⟨A.injective.mem_set_image.1 hv.1, fun ε hε ↦ ?_⟩
  set c := ‖(A : E →L[ℝ] F)‖
  have hc : 0 ≤ c := norm_nonneg _
  have hδ : 0 < ε / (c + 1) := div_pos hε (by positivity)
  filter_upwards [(tendsto_image_nhdsWithin A).eventually (hv.2 _ hδ)] with x hx
  have hA : ‖A x - A x₀‖ ≤ c * ‖x - x₀‖ := by
    rw [← map_sub]; exact (A : E →L[ℝ] F).le_opNorm _
  have hfrac : ε / (c + 1) * c ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
  calc (v.comp (A : E →L[ℝ] F)) (x - x₀) = v (A x - A x₀) := by simp [map_sub]
    _ ≤ (ω + ε / (c + 1)) * ‖A x - A x₀‖ := hx
    _ ≤ (ω + ε / (c + 1)) * (c * ‖x - x₀‖) := by gcongr
    _ ≤ (ω * c + ε) * ‖x - x₀‖ := by
        rw [← mul_assoc, add_mul]; gcongr

/-- Regular normals pull back along a linear isomorphism. -/
theorem comp_mem_regularNormalCone_of_mem_image {v : StrongDual ℝ F}
    (hv : v ∈ regularNormalCone (A '' Ω) (A x₀)) :
    v.comp (A : E →L[ℝ] F) ∈ regularNormalCone Ω x₀ := by
  have := comp_mem_epsNormalCone_of_mem_image A le_rfl (by rwa [epsNormalCone_zero])
  rwa [zero_mul, epsNormalCone_zero] at this

/-- Limiting normals pull back along a linear isomorphism. -/
theorem comp_mem_normalCone_of_mem_image {v : StrongDual ℝ F}
    (hv : v ∈ normalCone (A '' Ω) (A x₀)) : v.comp (A : E →L[ℝ] F) ∈ normalCone Ω x₀ := by
  obtain ⟨hx, a, w, ha, hw, hmem⟩ := hv
  have ha' := tendsto_nhdsWithin_iff.1 ha
  refine ⟨A.injective.mem_set_image.1 hx, fun k ↦ A.symm (a k),
    fun k ↦ (w k).comp (A : E →L[ℝ] F), tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩,
    tendsto_dual_comp hw tendsto_const_nhds, fun k ↦ ?_⟩
  · simpa [Function.comp_def] using (A.symm.continuous.tendsto _).comp ha'.1
  · filter_upwards [ha'.2] with k hk
    obtain ⟨y, hy, hyk⟩ := hk
    simpa [← hyk] using hy
  · have := hmem k
    rw [← A.apply_symm_apply (a k)] at this
    exact comp_mem_regularNormalCone_of_mem_image A this

/-- `v` is a limiting normal to `A '' Ω` at `A x₀` iff `v ∘ A` is a limiting normal to `Ω` at
`x₀`. -/
theorem mem_normalCone_image_iff {v : StrongDual ℝ F} :
    v ∈ normalCone (A '' Ω) (A x₀) ↔ v.comp (A : E →L[ℝ] F) ∈ normalCone Ω x₀ := by
  refine ⟨comp_mem_normalCone_of_mem_image A, fun h ↦ ?_⟩
  rw [← A.symm_image_image Ω, ← A.symm_apply_apply x₀] at h
  have := comp_mem_normalCone_of_mem_image A.symm h
  have hv : (v.comp (A : E →L[ℝ] F)).comp (A.symm : F →L[ℝ] E) = v := by ext; simp
  rwa [hv] at this

/-- Local closedness is preserved by linear isomorphisms. -/
theorem locallyClosed_image (h : ∃ r > 0, IsClosed (Ω ∩ closedBall x₀ r)) :
    ∃ r > 0, IsClosed (A '' Ω ∩ closedBall (A x₀) r) := by
  obtain ⟨r, hr, hcl⟩ := h
  set c := ‖(A.symm : F →L[ℝ] E)‖
  refine ⟨r / (c + 1), by positivity, ?_⟩
  have heq : A '' Ω ∩ closedBall (A x₀) (r / (c + 1)) =
      A '' (Ω ∩ closedBall x₀ r) ∩ closedBall (A x₀) (r / (c + 1)) := by
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hy⟩
      refine ⟨⟨x, ⟨hx, ?_⟩, rfl⟩, hy⟩
      rw [mem_closedBall, dist_eq_norm] at hy ⊢
      have h1 : ‖x - x₀‖ ≤ c * ‖A x - A x₀‖ := by
        have := (A.symm : F →L[ℝ] E).le_opNorm (A x - A x₀)
        simpa [← map_sub] using this
      have h2 : c * (r / (c + 1)) ≤ r := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
      calc ‖x - x₀‖ ≤ c * ‖A x - A x₀‖ := h1
        _ ≤ c * (r / (c + 1)) := by gcongr
        _ ≤ r := h2
    · rintro ⟨⟨x, ⟨hx, -⟩, rfl⟩, hy⟩
      exact ⟨mem_image_of_mem _ hx, hy⟩
  rw [heq]
  exact (A.toHomeomorph.isClosedMap _ hcl).inter isClosed_closedBall

end Pullback

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- Thm. 1.6 of [Mordukhovich 2018], second representation in (1.7), in a finite-dimensional
normed space: for `Ω` locally closed around `x₀ ∈ Ω`,
`N(x₀; Ω) = Lim sup_{x →Ω x₀, ω ↓ 0} N̂_ω(x; Ω)`. -/
theorem normalCone_eq_outerLimit_epsNormalCone (hx₀ : x₀ ∈ Ω)
    (hloc : ∃ r > 0, IsClosed (Ω ∩ closedBall x₀ r)) :
    normalCone Ω x₀ =
      outerLimit (𝓝[Ω] x₀ ×ˢ 𝓝[≥] (0 : ℝ)) (fun p ↦ epsNormalCone p.2 Ω p.1) := by
  refine subset_antisymm (fun v hv ↦ ?_) (fun v hv ↦ ?_)
  · obtain ⟨-, a, w, ha, hw, hmem⟩ := hv
    refine ⟨fun k ↦ (a k, 0), w, ha.prodMk (tendsto_nhdsWithin_iff.2
      ⟨tendsto_const_nhds, Eventually.of_forall fun _ ↦ mem_Ici.2 le_rfl⟩), hw, fun k ↦ ?_⟩
    simpa [epsNormalCone_zero] using hmem k
  set G := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  set A : E ≃L[ℝ] G := toEuclidean
  set c := ‖(A.symm : G →L[ℝ] E)‖
  obtain ⟨p, w, hp, hw, hmem⟩ := hv
  have hpa₀ : Tendsto (fun k ↦ (p k).1) atTop (𝓝[Ω] x₀) := tendsto_fst.comp hp
  have hpω₀ : Tendsto (fun k ↦ (p k).2) atTop (𝓝[≥] (0 : ℝ)) := tendsto_snd.comp hp
  have hpa := tendsto_nhdsWithin_iff.1 hpa₀
  have hpω := tendsto_nhdsWithin_iff.1 hpω₀
  have hN : v.comp (A.symm : G →L[ℝ] E) ∈ normalCone (A '' Ω) (A x₀) := by
    rw [normalCone_eq_outerLimit_epsNormalCone_inner (mem_image_of_mem _ hx₀)
      (locallyClosed_image A hloc)]
    refine mem_outerLimit_of_eventually (fun k ↦ (A (p k).1, (p k).2 * c))
      (fun k ↦ (w k).comp (A.symm : G →L[ℝ] E)) ?_ (tendsto_dual_comp hw tendsto_const_nhds) ?_
    · have h1 : Tendsto (fun k ↦ A (p k).1) atTop (𝓝[A '' Ω] (A x₀)) :=
        tendsto_nhdsWithin_iff.2 ⟨(A.continuous.tendsto _).comp hpa.1,
          hpa.2.mono fun k hk ↦ mem_image_of_mem _ hk⟩
      have h2 : Tendsto (fun k ↦ (p k).2 * c) atTop (𝓝[≥] (0 : ℝ)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, hpω.2.mono fun k hk ↦ ?_⟩
        · simpa using hpω.1.mul_const c
        · exact mul_nonneg hk (norm_nonneg _)
      exact h1.prodMk h2
    · filter_upwards [hpω.2] with k hk
      have h := hmem k
      simp only at h
      rw [← A.symm_image_image Ω, ← A.symm_apply_apply (p k).1] at h
      exact comp_mem_epsNormalCone_of_mem_image A.symm hk h
  have := (mem_normalCone_image_iff A).1 hN
  have hv : (v.comp (A.symm : G →L[ℝ] E)).comp (A : E →L[ℝ] G) = v := by ext; simp
  rwa [hv] at this

/-- Prop. 1.2 of [Mordukhovich 2018] in a finite-dimensional normed space: for `Ω` locally
closed around `x₀ ∈ Ω`, `x₀` is a boundary point of `Ω` iff `N(x₀; Ω) ≠ {0}`. -/
theorem exists_ne_zero_mem_normalCone_iff (hx₀ : x₀ ∈ Ω)
    (hloc : ∃ r > 0, IsClosed (Ω ∩ closedBall x₀ r)) :
    (∃ v ∈ normalCone Ω x₀, v ≠ 0) ↔ x₀ ∈ frontier Ω := by
  constructor
  · rintro ⟨v, hv, hv0⟩
    rw [frontier, Set.mem_sdiff, and_iff_right (subset_closure hx₀)]
    intro hint
    rw [normalCone_of_mem_interior hint] at hv
    exact hv0 hv
  · intro hfr
    set G := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
    set A : E ≃L[ℝ] G := toEuclidean
    have hfr' : A x₀ ∈ frontier (A '' Ω) := by
      have h := A.toHomeomorph.image_frontier Ω
      change A '' frontier Ω = frontier (A '' Ω) at h
      rw [← h]; exact mem_image_of_mem _ hfr
    obtain ⟨w, hw, hw0⟩ := (exists_ne_zero_mem_normalCone_iff_inner (mem_image_of_mem _ hx₀)
      (locallyClosed_image A hloc)).2 hfr'
    refine ⟨w.comp (A : E →L[ℝ] G), (mem_normalCone_image_iff A).1 hw, fun h ↦ hw0 ?_⟩
    have : (w.comp (A : E →L[ℝ] G)).comp (A.symm : G →L[ℝ] E) = w := by ext; simp
    rw [← this, h, ContinuousLinearMap.zero_comp]

end FiniteDimensional

end VariationalAnalysis
