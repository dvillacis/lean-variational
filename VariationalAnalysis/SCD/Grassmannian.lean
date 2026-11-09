/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Trace
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import VariationalAnalysis.SetValued.OuterLimit

/-!
# Convergence of subspaces: the Grassmannian metric

[Gfrerer–Outrata 2022] equip the set `𝓛ₙ` of `n`-dimensional subspaces of `ℝ²ⁿ` with the metric
`d(L₁, L₂) = ‖P₁ - P₂‖`, where `Pᵢ` is the orthogonal projection onto `Lᵢ` (Section 3). We do the
same for the subspaces of a finite-dimensional real normed space `V`, computing the projections in
the Euclidean model `toEuclidean : V ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ V))`.

## Main declarations

* `grassProj L`: the orthogonal projection onto the image of `L` in the Euclidean model.
* `grassDist L₁ L₂ = ‖grassProj L₁ - grassProj L₂‖`, and `GrassTendsto L L₀` for `d(Lₖ, L₀) → 0`.

## Main results

* `GrassTendsto.mem_of_tendsto`, `GrassTendsto.exists_tendsto`: convergence of subspaces implies
  Painlevé–Kuratowski convergence (`Lim sup Lₖ ⊆ L₀ ⊆ Lim inf Lₖ`).
* `exists_grassTendsto_subseq`: the set of subspaces of a fixed dimension is sequentially compact
  [Gfrerer–Outrata 2022, Lemma 3.1(iv)].
* `grassTendsto_of_outerLimit_subset`: for subspaces of a fixed dimension, `Lim sup Lₖ ⊆ L₀`
  already implies `d(Lₖ, L₀) → 0`; in particular Painlevé–Kuratowski convergence and convergence
  in the metric agree [Gfrerer–Outrata 2022, Lemma 3.1(v)].
-/

open Filter Topology Set Module

namespace VariationalAnalysis

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The Euclidean model of `V`. -/
local notation "𝕎" => EuclideanSpace ℝ (Fin (finrank ℝ V))

/-- The image of a subspace `L ≤ V` in the Euclidean model of `V`. -/
noncomputable def euclideanImage (L : Submodule ℝ V) : Submodule ℝ 𝕎 :=
  L.map ((toEuclidean : V ≃L[ℝ] 𝕎) : V →ₗ[ℝ] 𝕎)

/-- The orthogonal projection onto the image of `L` in the Euclidean model of `V`. -/
noncomputable def grassProj (L : Submodule ℝ V) : 𝕎 →L[ℝ] 𝕎 :=
  (euclideanImage L).starProjection

/-- The Grassmannian distance `d(L₁, L₂) = ‖P₁ - P₂‖` between two subspaces
[Gfrerer–Outrata 2022, Section 3]. -/
noncomputable def grassDist (L₁ L₂ : Submodule ℝ V) : ℝ := ‖grassProj L₁ - grassProj L₂‖

/-- `Lₖ → L₀` in the Grassmannian metric. -/
def GrassTendsto (L : ℕ → Submodule ℝ V) (L₀ : Submodule ℝ V) : Prop :=
  Tendsto (fun k ↦ grassProj (L k)) atTop (𝓝 (grassProj L₀))

/-- If `Pₖ → P₀` in operator norm and `xₖ → x₀`, then `Pₖ xₖ → P₀ x₀`. -/
theorem tendsto_clm_apply {α E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {l : Filter α} {P : α → E →L[ℝ] F}
    {P₀ : E →L[ℝ] F} {x : α → E} {x₀ : E} (hP : Tendsto P l (𝓝 P₀)) (hx : Tendsto x l (𝓝 x₀)) :
    Tendsto (fun k ↦ P k (x k)) l (𝓝 (P₀ x₀)) :=
  ((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := F)).continuous.tendsto (P₀, x₀)).comp
    (hP.prodMk_nhds hx)

section Basic

variable {L L₀ L₁ L₂ L₃ : Submodule ℝ V}

theorem mem_euclideanImage_iff {w : 𝕎} :
    w ∈ euclideanImage L ↔ ∃ x ∈ L, toEuclidean x = w := by
  rw [euclideanImage, Submodule.mem_map]
  rfl

theorem toEuclidean_mem_euclideanImage_iff {x : V} :
    toEuclidean x ∈ euclideanImage L ↔ x ∈ L := by
  rw [mem_euclideanImage_iff]
  exact ⟨fun ⟨y, hy, h⟩ ↦ toEuclidean.injective h ▸ hy, fun h ↦ ⟨x, h, rfl⟩⟩

theorem finrank_euclideanImage (L : Submodule ℝ V) :
    finrank ℝ (euclideanImage L) = finrank ℝ L :=
  LinearEquiv.finrank_map_eq (toEuclidean : V ≃L[ℝ] 𝕎).toLinearEquiv L

theorem euclideanImage_injective : Function.Injective (euclideanImage (V := V)) :=
  Submodule.map_injective_of_injective (toEuclidean : V ≃L[ℝ] 𝕎).injective

theorem grassProj_apply_mem (L : Submodule ℝ V) (w : 𝕎) : grassProj L w ∈ euclideanImage L :=
  Submodule.starProjection_apply_mem _ w

theorem grassProj_eq_self_iff {w : 𝕎} : grassProj L w = w ↔ w ∈ euclideanImage L :=
  Submodule.starProjection_eq_self_iff

theorem grassProj_toEuclidean_of_mem {x : V} (hx : x ∈ L) :
    grassProj L (toEuclidean x) = toEuclidean x :=
  grassProj_eq_self_iff.2 (toEuclidean_mem_euclideanImage_iff.2 hx)

theorem range_grassProj (L : Submodule ℝ V) :
    LinearMap.range (grassProj L : 𝕎 →ₗ[ℝ] 𝕎) = euclideanImage L :=
  Submodule.range_starProjection _

theorem norm_grassProj_le (L : Submodule ℝ V) : ‖grassProj L‖ ≤ 1 :=
  Submodule.starProjection_norm_le _

theorem grassProj_injective : Function.Injective (grassProj (V := V)) := fun L₁ L₂ h ↦
  euclideanImage_injective (by rw [← range_grassProj, ← range_grassProj, h])

theorem grassDist_comm (L₁ L₂ : Submodule ℝ V) : grassDist L₁ L₂ = grassDist L₂ L₁ :=
  norm_sub_rev _ _

theorem grassDist_nonneg (L₁ L₂ : Submodule ℝ V) : 0 ≤ grassDist L₁ L₂ := norm_nonneg _

theorem grassDist_self (L : Submodule ℝ V) : grassDist L L = 0 := by simp [grassDist]

theorem grassDist_triangle (L₁ L₂ L₃ : Submodule ℝ V) :
    grassDist L₁ L₃ ≤ grassDist L₁ L₂ + grassDist L₂ L₃ :=
  norm_sub_le_norm_sub_add_norm_sub _ _ _

theorem grassDist_eq_zero_iff : grassDist L₁ L₂ = 0 ↔ L₁ = L₂ := by
  rw [grassDist, norm_sub_eq_zero_iff]
  exact ⟨fun h ↦ grassProj_injective h, fun h ↦ h ▸ rfl⟩

theorem grassTendsto_iff {L : ℕ → Submodule ℝ V} :
    GrassTendsto L L₀ ↔ Tendsto (fun k ↦ grassDist (L k) L₀) atTop (𝓝 0) :=
  tendsto_iff_norm_sub_tendsto_zero

theorem grassTendsto_const (L₀ : Submodule ℝ V) : GrassTendsto (fun _ ↦ L₀) L₀ :=
  tendsto_const_nhds

theorem GrassTendsto.comp {L : ℕ → Submodule ℝ V} (h : GrassTendsto L L₀) {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop) : GrassTendsto (L ∘ φ) L₀ :=
  Filter.Tendsto.comp h hφ

/-- Limits in the Grassmannian metric are unique. -/
theorem GrassTendsto.unique {L : ℕ → Submodule ℝ V} (h₁ : GrassTendsto L L₁)
    (h₂ : GrassTendsto L L₂) : L₁ = L₂ :=
  grassProj_injective (tendsto_nhds_unique h₁ h₂)

/-- If `d(Lₖ, Mₖ) → 0` and `Mₖ → L₀`, then `Lₖ → L₀`. -/
theorem GrassTendsto.of_grassDist_tendsto {L M : ℕ → Submodule ℝ V} (hM : GrassTendsto M L₀)
    (h : Tendsto (fun k ↦ grassDist (L k) (M k)) atTop (𝓝 0)) : GrassTendsto L L₀ := by
  rw [grassTendsto_iff] at hM ⊢
  refine squeeze_zero (fun k ↦ grassDist_nonneg _ _) (fun k ↦ grassDist_triangle _ (M k) _)
    (by simpa using h.add hM)

end Basic

section Convergence

variable {L : ℕ → Submodule ℝ V} {L₀ : Submodule ℝ V}

/-- `Lim sup Lₖ ⊆ L₀`: if `wₖ ∈ Lₖ` and `wₖ → w₀`, then `w₀ ∈ L₀`. -/
theorem GrassTendsto.mem_of_tendsto (h : GrassTendsto L L₀) {w : ℕ → V} {w₀ : V}
    (hw : ∀ k, w k ∈ L k) (hlim : Tendsto w atTop (𝓝 w₀)) : w₀ ∈ L₀ := by
  have he : Tendsto (fun k ↦ toEuclidean (w k)) atTop (𝓝 (toEuclidean w₀)) :=
    (toEuclidean.continuous.tendsto _).comp hlim
  have h1 : Tendsto (fun k ↦ grassProj (L k) (toEuclidean (w k))) atTop
      (𝓝 (grassProj L₀ (toEuclidean w₀))) := tendsto_clm_apply h he
  have h2 : Tendsto (fun k ↦ grassProj (L k) (toEuclidean (w k))) atTop
      (𝓝 (toEuclidean w₀)) :=
    he.congr fun k ↦ (grassProj_toEuclidean_of_mem (hw k)).symm
  exact toEuclidean_mem_euclideanImage_iff.1
    (grassProj_eq_self_iff.1 (tendsto_nhds_unique h1 h2))

/-- `Lim sup Lₖ ⊆ L₀`, with an arbitrary index sequence `aₖ → ∞`. -/
theorem GrassTendsto.outerLimit_subset (h : GrassTendsto L L₀) :
    outerLimit atTop (fun k ↦ (L k : Set V)) ⊆ L₀ := by
  rintro w₀ ⟨a, w, ha, hw, hmem⟩
  exact (h.comp ha).mem_of_tendsto hmem hw

/-- `L₀ ⊆ Lim inf Lₖ`: every `w₀ ∈ L₀` is the limit of some `wₖ ∈ Lₖ`. -/
theorem GrassTendsto.exists_tendsto (h : GrassTendsto L L₀) {w₀ : V} (hw₀ : w₀ ∈ L₀) :
    ∃ w : ℕ → V, (∀ k, w k ∈ L k) ∧ Tendsto w atTop (𝓝 w₀) := by
  refine ⟨fun k ↦ toEuclidean.symm (grassProj (L k) (toEuclidean w₀)), fun k ↦ ?_, ?_⟩
  · obtain ⟨x, hx, hxe⟩ := mem_euclideanImage_iff.1 (grassProj_apply_mem (L k) (toEuclidean w₀))
    show toEuclidean.symm (grassProj (L k) (toEuclidean w₀)) ∈ L k
    rw [← hxe]
    simpa using hx
  · have h1 : Tendsto (fun k ↦ grassProj (L k) (toEuclidean w₀)) atTop
        (𝓝 (grassProj L₀ (toEuclidean w₀))) := tendsto_clm_apply h tendsto_const_nhds
    rw [grassProj_toEuclidean_of_mem hw₀] at h1
    have := (toEuclidean.symm.continuous.tendsto _).comp h1
    rwa [ContinuousLinearEquiv.symm_apply_apply] at this

/-- The trace of the projection onto `euclideanImage L` is `finrank L`. -/
theorem trace_grassProj (L : Submodule ℝ V) :
    LinearMap.trace ℝ 𝕎 (grassProj L : 𝕎 →ₗ[ℝ] 𝕎) = finrank ℝ L := by
  have hidem : IsIdempotentElem (grassProj L : 𝕎 →ₗ[ℝ] 𝕎) :=
    ContinuousLinearMap.IsIdempotentElem.toLinearMap (Submodule.isIdempotentElem_starProjection _)
  have hproj := LinearMap.IsIdempotentElem.isProj_range _ hidem
  rw [hproj.trace, range_grassProj, finrank_euclideanImage]

omit [FiniteDimensional ℝ V] in
/-- The trace, as a continuous linear functional on `𝕎 →L[ℝ] 𝕎`. -/
theorem continuous_trace_coe :
    Continuous fun P : 𝕎 →L[ℝ] 𝕎 ↦ LinearMap.trace ℝ 𝕎 (P : 𝕎 →ₗ[ℝ] 𝕎) :=
  LinearMap.continuous_of_finiteDimensional
    ((LinearMap.trace ℝ 𝕎).comp (ContinuousLinearMap.coeLM ℝ))

/-- Lemma 3.1(iv) of [Gfrerer–Outrata 2022]: the subspaces of dimension `n` form a sequentially
compact set in the Grassmannian metric. -/
theorem exists_grassTendsto_subseq (L : ℕ → Submodule ℝ V) {n : ℕ}
    (hL : ∀ k, finrank ℝ (L k) = n) :
    ∃ L₀ : Submodule ℝ V, finrank ℝ L₀ = n ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ GrassTendsto (L ∘ φ) L₀ := by
  -- the projections lie in the compact unit ball of `𝕎 →L[ℝ] 𝕎`
  have hball : ∀ k, grassProj (L k) ∈ Metric.closedBall (0 : 𝕎 →L[ℝ] 𝕎) 1 := fun k ↦ by
    simpa using norm_grassProj_le (L k)
  obtain ⟨P, -, φ, hφ, hP⟩ := (isCompact_closedBall (0 : 𝕎 →L[ℝ] 𝕎) 1).tendsto_subseq hball
  -- the limit `P` is an orthogonal projection
  have hidem : IsIdempotentElem P := by
    have h1 : Tendsto (fun k ↦ grassProj (L (φ k)) * grassProj (L (φ k))) atTop (𝓝 (P * P)) :=
      hP.mul hP
    have h2 : Tendsto (fun k ↦ grassProj (L (φ k)) * grassProj (L (φ k))) atTop (𝓝 P) :=
      hP.congr fun k ↦ (Submodule.isIdempotentElem_starProjection _).eq.symm
    exact tendsto_nhds_unique h1 h2
  have hsa : IsSelfAdjoint P := by
    have h1 : Tendsto (fun k ↦ star (grassProj (L (φ k)))) atTop (𝓝 (star P)) := by
      simp only [ContinuousLinearMap.star_eq_adjoint]
      exact (ContinuousLinearMap.adjoint.continuous.tendsto P).comp hP
    have h2 : Tendsto (fun k ↦ star (grassProj (L (φ k)))) atTop (𝓝 P) :=
      hP.congr fun k ↦ (isSelfAdjoint_starProjection _).star_eq.symm
    exact tendsto_nhds_unique h1 h2
  obtain ⟨hK, hPK⟩ := isStarProjection_iff_eq_starProjection_range.1 ⟨hidem, hsa⟩
  set K : Submodule ℝ 𝕎 := LinearMap.range (P : 𝕎 →ₗ[ℝ] 𝕎)
  -- the subspace `L₀ := e⁻¹ K` has Euclidean image `K`
  set L₀ : Submodule ℝ V := K.comap ((toEuclidean : V ≃L[ℝ] 𝕎) : V →ₗ[ℝ] 𝕎)
  have himage : euclideanImage L₀ = K :=
    Submodule.map_comap_eq_of_surjective (toEuclidean : V ≃L[ℝ] 𝕎).surjective K
  have hproj : grassProj L₀ = P := by
    rw [grassProj]
    convert hPK.symm
  refine ⟨L₀, ?_, φ, hφ, ?_⟩
  · -- the dimension is preserved by the trace
    have htr : Tendsto (fun k ↦ LinearMap.trace ℝ 𝕎 (grassProj (L (φ k)) : 𝕎 →ₗ[ℝ] 𝕎)) atTop
        (𝓝 (LinearMap.trace ℝ 𝕎 (P : 𝕎 →ₗ[ℝ] 𝕎))) :=
      (continuous_trace_coe.tendsto P).comp hP
    have hconst : ∀ k, LinearMap.trace ℝ 𝕎 (grassProj (L (φ k)) : 𝕎 →ₗ[ℝ] 𝕎) = n := fun k ↦ by
      rw [trace_grassProj, hL]
    rw [tendsto_congr hconst] at htr
    have h1 : LinearMap.trace ℝ 𝕎 (P : 𝕎 →ₗ[ℝ] 𝕎) = n := tendsto_nhds_unique htr tendsto_const_nhds
    rw [← hproj, trace_grassProj] at h1
    exact_mod_cast h1
  · rw [GrassTendsto, hproj]
    exact hP

/-- Lemma 3.1(v) of [Gfrerer–Outrata 2022], the useful direction: if all `Lₖ` and `L₀` have the
same dimension `n` and `Lim sup Lₖ ⊆ L₀`, then `Lₖ → L₀` in the Grassmannian metric. Together
with `GrassTendsto.outerLimit_subset` and `GrassTendsto.exists_tendsto`, convergence in the
metric and Painlevé–Kuratowski convergence agree for subspaces of a fixed dimension. -/
theorem grassTendsto_of_outerLimit_subset {n : ℕ} (hL : ∀ k, finrank ℝ (L k) = n)
    (hL₀ : finrank ℝ L₀ = n) (h : outerLimit atTop (fun k ↦ (L k : Set V)) ⊆ L₀) :
    GrassTendsto L L₀ := by
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  obtain ⟨M, hM, φ, hφ, hconv⟩ := exists_grassTendsto_subseq (L ∘ ns) fun k ↦ hL (ns k)
  refine ⟨φ, ?_⟩
  have hle : M ≤ L₀ := fun w₀ hw₀ ↦ by
    obtain ⟨w, hw, hlim⟩ := hconv.exists_tendsto hw₀
    exact h ⟨ns ∘ φ, w, hns.comp hφ.tendsto_atTop, hlim, hw⟩
  have hMeq : M = L₀ := Submodule.eq_of_le_of_finrank_eq hle (hM.trans hL₀.symm)
  rw [← hMeq]
  exact hconv

/-- Limits of `n`-dimensional subspaces are `n`-dimensional. -/
theorem GrassTendsto.finrank_eq {n : ℕ} (h : GrassTendsto L L₀) (hL : ∀ k, finrank ℝ (L k) = n) :
    finrank ℝ L₀ = n := by
  have h1 := (continuous_trace_coe.tendsto _).comp h
  simp only [Function.comp_def, trace_grassProj, hL] at h1
  exact_mod_cast (tendsto_nhds_unique tendsto_const_nhds h1).symm

end Convergence

end VariationalAnalysis
