/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import VariationalAnalysis.Normal.Regular

/-!
# The contingent cone and tangential preduality

The contingent (Bouligand) cone [Mordukhovich 2018, Def. 1.8], [Clason–Valkonen, (18.1)]
`T(x₀; Ω) = Lim sup_{t ↓ 0} (Ω - x₀) / t` consists of the vectors `w` for which there are
`xₖ ∈ Ω` with `xₖ → x₀` and `αₖ ≥ 0` with `αₖ (xₖ - x₀) → w`. We define it by this sequential
representation, which [Mordukhovich 2018, p. 8] states right after (1.11).

## Main results

* `regularNormalCone_subset_polar_contingentCone`: `N̂(x₀; Ω) ⊆ T(x₀; Ω)*` in any normed space
  [Clason–Valkonen, Lemma 18.10(i)].
* `regularNormalCone_eq_polar_contingentCone`: Prop. 1.9 of [Mordukhovich 2018]: in finite
  dimensions `N̂(x₀; Ω) = T(x₀; Ω)*` (Lemma 18.10(ii) of [Clason–Valkonen], where the weak and
  strong contingent cones agree).
-/

open Filter Topology Set

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : Set E} {x₀ w : E} {v : StrongDual ℝ E}

/-- The contingent cone to `Ω` at `x₀` [Mordukhovich 2018, Def. 1.8]: the limits of
`αₖ (xₖ - x₀)` with `Ω ∋ xₖ → x₀` and `αₖ ≥ 0`. Empty if `x₀ ∉ Ω`. -/
def contingentCone (Ω : Set E) (x₀ : E) : Set E :=
  {w | x₀ ∈ Ω ∧ ∃ x : ℕ → E, ∃ α : ℕ → ℝ, (∀ k, x k ∈ Ω ∧ 0 ≤ α k) ∧
    Tendsto x atTop (𝓝 x₀) ∧ Tendsto (fun k ↦ α k • (x k - x₀)) atTop (𝓝 w)}

theorem zero_mem_contingentCone (hx : x₀ ∈ Ω) : (0 : E) ∈ contingentCone Ω x₀ :=
  ⟨hx, fun _ ↦ x₀, fun _ ↦ 0, fun _ ↦ ⟨hx, le_rfl⟩, tendsto_const_nhds, by simp⟩

theorem smul_mem_contingentCone (hw : w ∈ contingentCone Ω x₀) {t : ℝ} (ht : 0 ≤ t) :
    t • w ∈ contingentCone Ω x₀ := by
  obtain ⟨hx, x, α, hxα, hxlim, hlim⟩ := hw
  refine ⟨hx, x, fun k ↦ t * α k, fun k ↦ ⟨(hxα k).1, mul_nonneg ht (hxα k).2⟩, hxlim, ?_⟩
  simpa [mul_smul] using hlim.const_smul t

/-- `N̂(x₀; Ω) ⊆ T(x₀; Ω)*` in every normed space [Mordukhovich 2018, Prop. 1.9, first part of
the proof]. -/
theorem regularNormalCone_subset_polar_contingentCone (hv : v ∈ regularNormalCone Ω x₀) :
    ∀ w ∈ contingentCone Ω x₀, v w ≤ 0 := by
  rintro w ⟨-, x, α, hxα, hxlim, hlim⟩
  have hxΩ : Tendsto x atTop (𝓝[Ω] x₀) :=
    tendsto_nhdsWithin_iff.2 ⟨hxlim, Eventually.of_forall fun k ↦ (hxα k).1⟩
  refine le_of_forall_pos_le_add_mul (c := ‖w‖) fun ε hε ↦ ?_
  have hle : ∀ᶠ k in atTop, v (α k • (x k - x₀)) ≤ ε * ‖α k • (x k - x₀)‖ := by
    filter_upwards [hxΩ.eventually (hv.2 ε hε)] with k hk
    rw [map_smul, smul_eq_mul, norm_smul, Real.norm_of_nonneg (hxα k).2]
    nlinarith [(hxα k).2]
  have := le_of_tendsto_of_tendsto ((v.continuous.tendsto w).comp hlim)
    ((continuous_norm.tendsto w).comp hlim |>.const_mul ε) hle
  simpa using this

/-- Prop. 1.9 of [Mordukhovich 2018] (tangential preduality): in finite dimensions the regular
normal cone is the polar of the contingent cone, `N̂(x₀; Ω) = T*(x₀; Ω)`. -/
theorem regularNormalCone_eq_polar_contingentCone [FiniteDimensional ℝ E] (hx : x₀ ∈ Ω) :
    regularNormalCone Ω x₀ = {v | ∀ w ∈ contingentCone Ω x₀, v w ≤ 0} := by
  refine subset_antisymm (fun v hv ↦ regularNormalCone_subset_polar_contingentCone hv)
    fun v hv ↦ ⟨hx, fun ε hε ↦ ?_⟩
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨x, hxlim, hxv⟩ := exists_seq_forall_of_frequently hcon
  simp only [not_le] at hxv
  have hxΩ := (tendsto_nhdsWithin_iff.1 hxlim)
  have hne : ∀ k, x k - x₀ ≠ 0 := fun k h ↦ by
    have := hxv k; rw [h] at this; simp at this
  set u : ℕ → E := fun k ↦ ‖x k - x₀‖⁻¹ • (x k - x₀) with hu
  have hus : ∀ k, u k ∈ Metric.sphere (0 : E) 1 := fun k ↦ by
    simp [hu, norm_smul, hne k]
  obtain ⟨w, hw, φ, hφ, hlim⟩ := (isCompact_sphere (0 : E) 1).tendsto_subseq hus
  have hwT : w ∈ contingentCone Ω x₀ := by
    obtain ⟨N, hN⟩ := eventually_atTop.1 hxΩ.2
    refine ⟨hx, fun k ↦ x (φ (k + N)), fun k ↦ ‖x (φ (k + N)) - x₀‖⁻¹, fun k ↦
      ⟨hN _ ((Nat.le_add_left N k).trans (hφ.id_le _)), inv_nonneg.2 (norm_nonneg _)⟩,
      ?_, ?_⟩
    · exact hxΩ.1.comp (hφ.tendsto_atTop.comp (tendsto_add_atTop_nat N))
    · exact (tendsto_add_atTop_iff_nat N).2 hlim
  have hvw : ε ≤ v w := by
    refine ge_of_tendsto ((v.continuous.tendsto w).comp hlim) (Eventually.of_forall fun k ↦ ?_)
    have h1 := hxv (φ k)
    have h2 : 0 < ‖x (φ k) - x₀‖ := norm_pos_iff.2 (hne _)
    simp only [Function.comp_apply, hu, map_smul, smul_eq_mul]
    rw [le_inv_mul_iff₀ h2]
    linarith [mul_comm ε ‖x (φ k) - x₀‖]
  linarith [hv w hwT]

end VariationalAnalysis
