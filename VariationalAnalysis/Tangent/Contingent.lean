/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import VariationalAnalysis.Normal.Regular
import VariationalAnalysis.SetValued.OuterLimit

/-!
# The contingent cone and tangential preduality

The contingent (Bouligand) cone [Mordukhovich 2018, Def. 1.8], [Clason–Valkonen, (18.1)]
`T(x₀; Ω) = Lim sup_{t ↓ 0} (Ω - x₀) / t` consists of the vectors `w` for which there are
`xₖ ∈ Ω` with `xₖ → x₀` and `αₖ ≥ 0` with `αₖ (xₖ - x₀) → w`. We define it by this sequential
representation, which [Mordukhovich 2018, p. 8] states right after (1.11).

## Main results

* `contingentCone_eq_outerLimit`: (1.11) of [Mordukhovich 2018]:
  `T(x₀; Ω) = Lim sup_{t ↓ 0} (Ω - x₀) / t`.
* `regularNormalCone_subset_polar_contingentCone`: `N̂(x₀; Ω) ⊆ T(x₀; Ω)*` in any normed space
  [Clason–Valkonen, Lemma 18.10(i)].
* `regularNormalCone_eq_polar_contingentCone`: Prop. 1.9 of [Mordukhovich 2018]: in finite
  dimensions `N̂(x₀; Ω) = T(x₀; Ω)*` (Lemma 18.10(ii) of [Clason–Valkonen], where the weak and
  strong contingent cones agree).
-/

open Filter Topology Set
open scoped Pointwise

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

/-- It suffices that `xₖ ∈ Ω` and `αₖ ≥ 0` hold for all large `k`. -/
theorem mem_contingentCone_of_eventually (hx : x₀ ∈ Ω) (x : ℕ → E) (α : ℕ → ℝ)
    (h : ∀ᶠ k in atTop, x k ∈ Ω ∧ 0 ≤ α k) (hx₀ : Tendsto x atTop (𝓝 x₀))
    (hw : Tendsto (fun k ↦ α k • (x k - x₀)) atTop (𝓝 w)) : w ∈ contingentCone Ω x₀ := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  exact ⟨hx, fun k ↦ x (k + N), fun k ↦ α (k + N), fun k ↦ hN _ (Nat.le_add_left N k),
    (tendsto_add_atTop_iff_nat N).2 hx₀, (tendsto_add_atTop_iff_nat N).2 hw⟩

/-- (1.11) of [Mordukhovich 2018]: the contingent cone is the outer limit
`T(x₀; Ω) = Lim sup_{t ↓ 0} (Ω - x₀) / t`. -/
theorem contingentCone_eq_outerLimit (hx : x₀ ∈ Ω) :
    contingentCone Ω x₀ = outerLimit (𝓝[>] (0 : ℝ)) (fun t ↦ t⁻¹ • ((· - x₀) '' Ω)) := by
  ext w
  constructor
  · rintro ⟨-, x, α, hxα, hxlim, hlim⟩
    by_cases hw0 : w = 0
    · subst hw0
      refine ⟨fun k ↦ 1 / ((k : ℝ) + 1), fun _ ↦ 0, ?_, tendsto_const_nhds, fun k ↦ ?_⟩
      · exact tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
          Eventually.of_forall fun k ↦ mem_Ioi.2 Nat.one_div_pos_of_nat⟩
      · exact ⟨0, ⟨x₀, hx, sub_self x₀⟩, smul_zero _⟩
    -- `αₖ → ∞`, since `αₖ (xₖ - x₀) → w ≠ 0` while `xₖ → x₀`
    have hnw : 0 < ‖w‖ := norm_pos_iff.2 hw0
    have hev : ∀ᶠ k in atTop, ‖w‖ / 2 < ‖α k • (x k - x₀)‖ :=
      ((continuous_norm.tendsto w).comp hlim).eventually (lt_mem_nhds (by linarith))
    have hd : Tendsto (fun k ↦ ‖x k - x₀‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 hxlim
    have hpos : ∀ᶠ k in atTop, 0 < α k ∧ 0 < ‖x k - x₀‖ := hev.mono fun k hk ↦ by
      have h0 : 0 < ‖α k • (x k - x₀)‖ := by linarith
      rw [norm_smul, Real.norm_of_nonneg (hxα k).2] at h0 hk
      exact ⟨pos_of_mul_pos_left h0 (norm_nonneg _), pos_of_mul_pos_right h0 (hxα k).2⟩
    have hd' : Tendsto (fun k ↦ ‖x k - x₀‖) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨hd, hpos.mono fun k hk ↦ hk.2⟩
    have hinv : Tendsto (fun k ↦ ‖w‖ / 2 * ‖x k - x₀‖⁻¹) atTop atTop :=
      (tendsto_inv_nhdsGT_zero.comp hd').const_mul_atTop (by linarith)
    have hαtop : Tendsto α atTop atTop := by
      refine tendsto_atTop_mono' atTop ?_ hinv
      filter_upwards [hev, hpos] with k hk hk'
      rw [norm_smul, Real.norm_of_nonneg (hxα k).2] at hk
      rw [← div_eq_mul_inv, div_le_iff₀ hk'.2]
      linarith
    refine mem_outerLimit_of_eventually (fun k ↦ (α k)⁻¹) (fun k ↦ α k • (x k - x₀))
      (tendsto_inv_atTop_nhdsGT_zero.comp hαtop) hlim ?_
    filter_upwards [hpos] with k hk
    simp only [inv_inv]
    exact ⟨x k - x₀, ⟨x k, (hxα k).1, rfl⟩, rfl⟩
  · rintro ⟨t, v, ht, hv, hmem⟩
    choose y hy hyv using fun k ↦ hmem k
    choose z hz hzy using hy
    simp only at hyv hzy
    have ht' := tendsto_nhdsWithin_iff.1 ht
    refine mem_contingentCone_of_eventually hx z (fun k ↦ (t k)⁻¹) ?_ ?_ ?_
    · filter_upwards [ht'.2] with k hk
      exact ⟨hz k, inv_nonneg.2 (le_of_lt hk)⟩
    · -- `zₖ - x₀ = tₖ vₖ → 0`
      have hzv : ∀ᶠ k in atTop, z k - x₀ = t k • v k := by
        filter_upwards [ht'.2] with k hk
        rw [← hyv k, ← hzy k, smul_smul, mul_inv_cancel₀ (ne_of_gt hk), one_smul]
      have : Tendsto (fun k ↦ t k • v k) atTop (𝓝 ((0 : ℝ) • w)) := ht'.1.smul hv
      rw [zero_smul] at this
      have h2 : Tendsto (fun k ↦ z k - x₀) atTop (𝓝 0) :=
        this.congr' (hzv.mono fun k hk ↦ hk.symm)
      simpa using h2.add_const x₀
    · refine hv.congr' (Eventually.of_forall fun k ↦ ?_)
      simp only
      rw [← hyv k, ← hzy k]

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
