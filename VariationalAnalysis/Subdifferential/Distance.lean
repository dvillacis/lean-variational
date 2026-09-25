/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import Mathlib.Topology.MetricSpace.HausdorffDistance
import VariationalAnalysis.Subdifferential.Lipschitz

/-!
# Subgradients of the distance function

For a set `Ω` in a real normed space `E`, the distance function `d_Ω(x) = dist(x; Ω)` is
`distFun Ω`, viewed as an `EReal`-valued function.

## Main results

* `regularSubdiff_distFun_of_mem`, `subdiff_distFun_of_mem`: Thm. 1.33(i) of
  [Mordukhovich 2018]: at `x₀ ∈ Ω`, `∂̂d_Ω(x₀) = N̂(x₀; Ω) ∩ 𝔹` and `∂d_Ω(x₀) = N(x₀; Ω) ∩ 𝔹`
  (the latter for closed `Ω` in finite dimensions).
* `mem_regularNormalCone_of_mem_regularSubdiff_distFun`: [Mordukhovich 2018, Thm. 1.33,
  Step 2]: regular subgradients of `d_Ω` at `x₀` are regular normals at any nearest point.
-/

open Filter Topology Set Metric
open scoped NNReal

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : Set E} {x₀ : E} {v : StrongDual ℝ E}

/-- The distance function `d_Ω(x) = dist(x; Ω)` [Mordukhovich 2018, (1.2)], as an `EReal`-valued
function. -/
noncomputable def distFun (Ω : Set E) (x : E) : EReal := (infDist x Ω : ℝ)

/-- Basic subgradients of `d_Ω` have norm at most `1`. -/
theorem norm_le_one_of_mem_subdiff_distFun (hv : v ∈ subdiff (distFun Ω) x₀) : ‖v‖ ≤ 1 := by
  have := norm_le_of_mem_subdiff_of_lipschitz (f := fun x ↦ infDist x Ω) (U := univ)
    (L := 1) univ_mem ((lipschitz_infDist_pt (s := Ω)).lipschitzOnWith) hv
  simpa using this

/-- Regular subgradients of `d_Ω` have norm at most `1`. -/
theorem norm_le_one_of_mem_regularSubdiff_distFun (hv : v ∈ regularSubdiff (distFun Ω) x₀) :
    ‖v‖ ≤ 1 :=
  norm_le_one_of_mem_subdiff_distFun (regularSubdiff_subset_subdiff hv)

omit [NormedSpace ℝ E] in
theorem distFun_of_mem {x : E} (hx : x ∈ Ω) : distFun Ω x = ((0 : ℝ) : EReal) := by
  simp [distFun, infDist_zero_of_mem hx]

/-- Thm. 1.33(i) of [Mordukhovich 2018], regular subgradients: at `x₀ ∈ Ω`,
`∂̂d_Ω(x₀) = N̂(x₀; Ω) ∩ 𝔹`. -/
theorem regularSubdiff_distFun_of_mem (hx : x₀ ∈ Ω) :
    regularSubdiff (distFun Ω) x₀ = regularNormalCone Ω x₀ ∩ closedBall 0 1 := by
  ext v
  rw [mem_regularSubdiff_iff (distFun_of_mem hx)]
  constructor
  · intro hv
    refine ⟨⟨hx, fun ε hε ↦ ?_⟩, ?_⟩
    · filter_upwards [nhdsWithin_le_nhds (hv ε hε), self_mem_nhdsWithin] with x h1 h2
      rw [distFun_of_mem h2, EReal.coe_le_coe_iff] at h1
      linarith
    · rw [mem_closedBall, dist_zero_right]
      exact norm_le_one_of_mem_regularSubdiff_distFun ⟨0, distFun_of_mem hx, hv⟩
  · rintro ⟨hN, hB⟩ ε hε
    rw [mem_closedBall, dist_zero_right] at hB
    set δ := min (ε / 4) 1
    have hδ : 0 < δ := lt_min (by positivity) one_pos
    have hδ1 : δ ≤ ε / 4 := min_le_left _ _
    have hδ2 : δ ≤ 1 := min_le_right _ _
    obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhdsWithin_iff.1 (hN.2 δ hδ)
    filter_upwards [ball_mem_nhds x₀ (show 0 < ρ / 4 by positivity)] with x hxρ
    rw [mem_ball, dist_eq_norm] at hxρ
    simp only [distFun, EReal.coe_le_coe_iff, zero_add]
    have hdx : infDist x Ω ≤ ‖x - x₀‖ := by
      rw [← dist_eq_norm]; exact infDist_le_dist_of_mem hx
    rcases (norm_nonneg (x - x₀)).eq_or_lt with h0 | h0
    · rw [← h0, norm_eq_zero.1 h0.symm]
      simp [infDist_nonneg]
    obtain ⟨u, hu, hxu⟩ := (infDist_lt_iff ⟨x₀, hx⟩).1
      (show infDist x Ω < infDist x Ω + δ * ‖x - x₀‖ by nlinarith)
    rw [dist_eq_norm] at hxu
    have hux : ‖u - x₀‖ ≤ (2 + δ) * ‖x - x₀‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub u x x₀
      rw [norm_sub_rev u x] at this
      nlinarith
    have huρ : u ∈ ball x₀ ρ := by
      rw [mem_ball, dist_eq_norm]; nlinarith
    have hNu : v (u - x₀) ≤ δ * ‖u - x₀‖ := hball ⟨huρ, hu⟩
    have hvxu : v (x - u) ≤ ‖x - u‖ := by
      calc v (x - u) ≤ ‖v‖ * ‖x - u‖ := (le_abs_self _).trans (v.le_opNorm _)
        _ ≤ 1 * ‖x - u‖ := by gcongr
        _ = ‖x - u‖ := one_mul _
    have hsplit : v (x - x₀) = v (x - u) + v (u - x₀) := by
      rw [← map_add]; congr 1; abel
    have k1 := mul_le_mul_of_nonneg_left hux hδ.le
    have k2 : δ * ((2 + δ) * ‖x - x₀‖) ≤ 3 * δ * ‖x - x₀‖ := by
      have : δ * ‖x - x₀‖ * δ ≤ δ * ‖x - x₀‖ * 1 :=
        mul_le_mul_of_nonneg_left hδ2 (mul_nonneg hδ.le h0.le)
      nlinarith
    have k3 : 4 * δ * ‖x - x₀‖ ≤ ε * ‖x - x₀‖ := by nlinarith
    linarith

/-- [Mordukhovich 2018, Thm. 1.33, Step 2]: if `w ∈ Ω` is a nearest point to `x₀`, every regular
subgradient of `d_Ω` at `x₀` is a regular normal to `Ω` at `w` of norm at most `1`. -/
theorem mem_regularNormalCone_of_mem_regularSubdiff_distFun {w : E} (hw : w ∈ Ω)
    (hdw : ‖x₀ - w‖ = infDist x₀ Ω) (hv : v ∈ regularSubdiff (distFun Ω) x₀) :
    v ∈ regularNormalCone Ω w ∩ closedBall 0 1 := by
  refine ⟨⟨hw, fun ε hε ↦ ?_⟩, ?_⟩
  · rw [mem_regularSubdiff_iff (φ := distFun Ω) (r := infDist x₀ Ω) rfl] at hv
    have hT : Tendsto (fun u ↦ u - w + x₀) (𝓝 w) (𝓝 x₀) := by
      have : Tendsto (fun u ↦ u - w + x₀) (𝓝 w) (𝓝 (w - w + x₀)) :=
        ((continuous_id.sub continuous_const).add continuous_const).tendsto w
      simpa using this
    filter_upwards [nhdsWithin_le_nhds (hT.eventually (hv ε hε)), self_mem_nhdsWithin]
      with u h1 hu
    have hd : infDist (u - w + x₀) Ω ≤ infDist x₀ Ω := by
      rw [← hdw]
      calc infDist (u - w + x₀) Ω ≤ dist (u - w + x₀) u := infDist_le_dist_of_mem hu
        _ = ‖x₀ - w‖ := by rw [dist_eq_norm]; congr 1; abel
    simp only [distFun, EReal.coe_le_coe_iff] at h1
    have : u - w + x₀ - x₀ = u - w := by abel
    rw [this] at h1
    linarith
  · rw [mem_closedBall, dist_zero_right]
    exact norm_le_one_of_mem_regularSubdiff_distFun hv

/-- Thm. 1.33(i) of [Mordukhovich 2018], basic subgradients: at `x₀ ∈ Ω`, for `Ω` closed in finite
dimensions, `∂d_Ω(x₀) = N(x₀; Ω) ∩ 𝔹`. -/
theorem subdiff_distFun_of_mem [FiniteDimensional ℝ E] (hΩ : IsClosed Ω) (hx : x₀ ∈ Ω) :
    subdiff (distFun Ω) x₀ = normalCone Ω x₀ ∩ closedBall 0 1 := by
  rw [subdiff_eq_outerLimit (distFun_of_mem hx)]
  ext v
  constructor
  · rintro ⟨a, u, ha, hu, hmem⟩
    obtain ⟨ha1, ha2⟩ := tendsto_funNhds_iff.1 ha
    have hproj : ∀ k, ∃ w ∈ Ω, infDist (a k) Ω = dist (a k) w :=
      fun k ↦ hΩ.exists_infDist_eq_dist ⟨x₀, hx⟩ (a k)
    choose w hw hdw using hproj
    have hwlim : Tendsto w atTop (𝓝 x₀) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h2 := (tendsto_iff_norm_sub_tendsto_zero.1 ha1).const_mul 2
      rw [mul_zero] at h2
      refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ ?_) h2
      have h1 : infDist (a k) Ω ≤ ‖a k - x₀‖ := by
        rw [← dist_eq_norm]; exact infDist_le_dist_of_mem hx
      have h3 := norm_sub_le_norm_sub_add_norm_sub (w k) (a k) x₀
      have h4 : ‖w k - a k‖ = infDist (a k) Ω := by rw [hdw k, dist_eq_norm, norm_sub_rev]
      linarith
    have hmem' : ∀ k, u k ∈ regularNormalCone Ω (w k) ∩ closedBall 0 1 := fun k ↦
      mem_regularNormalCone_of_mem_regularSubdiff_distFun (hw k)
        (by rw [← dist_eq_norm, ← hdw k]) (hmem k)
    refine ⟨⟨hx, w, u, tendsto_nhdsWithin_iff.2 ⟨hwlim, Eventually.of_forall hw⟩, hu,
      fun k ↦ (hmem' k).1⟩, ?_⟩
    exact isClosed_closedBall.mem_of_tendsto hu (Eventually.of_forall fun k ↦ (hmem' k).2)
  · rintro ⟨⟨-, a, u, ha, hu, hmem⟩, hB⟩
    rw [mem_closedBall, dist_zero_right] at hB
    have ha' := tendsto_nhdsWithin_iff.1 ha
    refine mem_outerLimit_of_eventually a (fun k ↦ (max ‖u k‖ 1)⁻¹ • u k)
      (tendsto_funNhds_iff.2 ⟨ha'.1, ?_⟩) ?_ ?_
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [ha'.2] with k hk
      rw [distFun_of_mem hk, distFun_of_mem hx]
    · have h1 : Tendsto (fun k ↦ (max ‖u k‖ 1)⁻¹) atTop (𝓝 (max ‖v‖ 1)⁻¹) :=
        (((continuous_norm.tendsto v).comp hu).max tendsto_const_nhds).inv₀ (by positivity)
      have := h1.smul hu
      rwa [max_eq_right hB, inv_one, one_smul] at this
    · filter_upwards [ha'.2] with k hk
      rw [regularSubdiff_distFun_of_mem hk]
      refine ⟨smul_mem_regularNormalCone (hmem k) (by positivity), ?_⟩
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity),
        inv_mul_le_iff₀ (by positivity), mul_one]
      exact le_max_left _ _

end VariationalAnalysis
