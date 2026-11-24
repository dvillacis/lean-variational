/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import ConvexAnalysis.Convex.Radial
import VariationalAnalysis.Analysis.ConvexMajorant
import VariationalAnalysis.Subdifferential.Regular

/-!
# Smooth concave supports of regular normals and subgradients

In a real inner product space `H`:

* `mem_regularNormalCone_iff_exists_concave`: Thm. 1.10(ii) of [Mordukhovich 2018]:
  `v ∈ N̂(x₀; Ω)` iff there is a concave `C¹` function `ψ` with `∇ψ(x₀) = v` attaining its
  maximum over `Ω` uniquely at `x₀`.
* `exists_concave_support_of_mem_regularSubdiff`: Thm. 1.27 of [Mordukhovich 2018], second part:
  if `φ` is bounded below and `v ∈ ∂̂φ(x₀)`, there is a concave `C¹` function `ψ` with
  `∇ψ(x₀) = v`, `ψ x₀ = φ x₀`, and `ψ < φ` away from `x₀`.

The construction: a modulus `η` measuring the failure of the linear minorant is majorized by
the convex `C¹` function `τ = convexMajorant η`, and `ψ = ⟨v, · - x₀⟩ - τ(‖· - x₀‖)` (plus a
constant).
-/

open Filter Topology Set InnerProductSpace

namespace VariationalAnalysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {x₀ : H}

section SupModulus

variable {S : Set H} {q : H → ℝ}

/-- The modulus `η(t) = max(0, sup {q x | x ∈ S, 0 < ‖x - x₀‖ ≤ t})`. -/
noncomputable def supModulus (S : Set H) (x₀ : H) (q : H → ℝ) (t : ℝ) : ℝ :=
  sSup (insert 0 (q '' {x | x ∈ S ∧ x ≠ x₀ ∧ ‖x - x₀‖ ≤ t}))

variable (hB : ∃ B, ∀ x ∈ S, x ≠ x₀ → q x ≤ B)
include hB

omit [InnerProductSpace ℝ H] in
theorem bddAbove_supModulus (t : ℝ) :
    BddAbove (insert 0 (q '' {x | x ∈ S ∧ x ≠ x₀ ∧ ‖x - x₀‖ ≤ t})) := by
  obtain ⟨B, hB⟩ := hB
  refine ⟨max B 0, ?_⟩
  rintro _ (rfl | ⟨x, ⟨hx, hx0, -⟩, rfl⟩)
  · exact le_max_right _ _
  · exact (hB x hx hx0).trans (le_max_left _ _)

omit [InnerProductSpace ℝ H] in
theorem supModulus_nonneg (t : ℝ) : 0 ≤ supModulus S x₀ q t :=
  le_csSup (bddAbove_supModulus hB t) (mem_insert _ _)

omit [InnerProductSpace ℝ H] in
theorem monotone_supModulus : Monotone (supModulus S x₀ q) := fun _ _ hst ↦
  csSup_le_csSup (bddAbove_supModulus hB _) (insert_nonempty _ _)
    (insert_subset_insert (image_mono fun _ ⟨hx, hx0, hxt⟩ ↦ ⟨hx, hx0, hxt.trans hst⟩))

omit [InnerProductSpace ℝ H] hB in
theorem supModulus_of_nonpos {t : ℝ} (ht : t ≤ 0) : supModulus S x₀ q t = 0 := by
  have : {x | x ∈ S ∧ x ≠ x₀ ∧ ‖x - x₀‖ ≤ t} = ∅ := by
    ext x
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    intro _ hx0 hxt
    exact hx0 (sub_eq_zero.1 (norm_le_zero_iff.1 (hxt.trans ht)))
  simp [supModulus, this]

omit [InnerProductSpace ℝ H] in
theorem le_supModulus {x : H} (hx : x ∈ S) (hx0 : x ≠ x₀) :
    q x ≤ supModulus S x₀ q ‖x - x₀‖ :=
  le_csSup (bddAbove_supModulus hB _) (mem_insert_of_mem _ ⟨x, ⟨hx, hx0, le_rfl⟩, rfl⟩)

omit [InnerProductSpace ℝ H] in
theorem tendsto_supModulus (hvan : ∀ ε > 0, ∃ δ > 0, ∀ x ∈ S, x ≠ x₀ → ‖x - x₀‖ < δ → q x ≤ ε) :
    Tendsto (supModulus S x₀ q) (𝓝[≥] 0) (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha ↦ Eventually.of_forall fun t ↦ lt_of_lt_of_le ha (supModulus_nonneg hB t),
    fun a ha ↦ ?_⟩
  obtain ⟨δ, hδ, hq⟩ := hvan (a / 2) (half_pos ha)
  filter_upwards [nhdsWithin_le_nhds (gt_mem_nhds hδ)] with t ht
  refine lt_of_le_of_lt (csSup_le (insert_nonempty _ _) ?_) (half_lt_self ha)
  rintro _ (rfl | ⟨x, ⟨hx, hx0, hxt⟩, rfl⟩)
  · exact (half_pos ha).le
  · exact hq x hx hx0 (lt_of_le_of_lt hxt ht)

end SupModulus

section Radial

variable {η : ℝ → ℝ} (hmono : Monotone η) (h0 : ∀ t, 0 ≤ η t) (hneg : ∀ t ≤ 0, η t = 0)
  (hlim : Tendsto η (𝓝[≥] 0) (𝓝 0))
include hmono h0 hneg hlim

/-- The derivative of `x ↦ τ(‖x - x₀‖)`. -/
noncomputable def radialDeriv (η : ℝ → ℝ) (x₀ x : H) : StrongDual ℝ H :=
  convexMajorantDeriv η ‖x - x₀‖ • (‖x - x₀‖⁻¹ • innerSL ℝ (x - x₀))

theorem hasFDerivAt_radial (x : H) :
    HasFDerivAt (fun y ↦ convexMajorant η ‖y - x₀‖) (radialDeriv η x₀ x) x := by
  have hd := hasDerivAt_convexMajorant hmono h0 hneg hlim
  by_cases hx : x = x₀
  · subst hx
    have hz : radialDeriv η x x = 0 := by
      simp [radialDeriv, convexMajorantDeriv_zero hneg]
    rw [hz]
    have h1 := (hd 0).isLittleO
    rw [convexMajorantDeriv_zero hneg, convexMajorant_zero] at h1
    have hT : Tendsto (fun y ↦ ‖y - x‖) (𝓝 x) (𝓝 0) := by
      have : Tendsto (fun y : H ↦ ‖y - x‖) (𝓝 x) (𝓝 ‖x - x‖) :=
        (continuous_id.sub (continuous_const : Continuous fun _ : H ↦ x)).norm.tendsto x
      simpa using this
    have h2 := h1.comp_tendsto hT
    refine HasFDerivAt.of_isLittleO ?_
    simp only [Function.comp_def, smul_zero, sub_zero, sub_self, norm_zero,
      convexMajorant_zero, zero_apply] at h2 ⊢
    exact Asymptotics.isLittleO_norm_right.1 h2
  · have hne : x - x₀ ≠ 0 := sub_ne_zero.2 hx
    have hn := (hasFDerivAt_norm_of_ne_zero hne).comp x ((hasFDerivAt_id x).sub_const x₀)
    have := (hd ‖x - x₀‖).comp_hasFDerivAt x hn
    refine this.congr_fderiv ?_
    simp [radialDeriv]

theorem continuous_radialDeriv : Continuous (radialDeriv η x₀) := by
  have hc := continuous_convexMajorantDeriv hmono h0 hneg hlim
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = x₀
  · subst hx
    rw [ContinuousAt,
      show radialDeriv η x x = 0 by simp [radialDeriv, convexMajorantDeriv_zero hneg]]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hT : Tendsto (fun y ↦ |convexMajorantDeriv η ‖y - x‖|) (𝓝 x) (𝓝 0) := by
      have : Tendsto (fun y ↦ |convexMajorantDeriv η ‖y - x‖|) (𝓝 x)
          (𝓝 |convexMajorantDeriv η ‖x - x‖|) :=
        ((continuous_abs.comp hc).comp (continuous_id.sub continuous_const).norm).tendsto x
      simpa [convexMajorantDeriv_zero hneg] using this
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun y ↦ ?_) hT
    rw [radialDeriv, norm_smul, norm_smul, innerSL_apply_norm, Real.norm_eq_abs, norm_inv,
      norm_norm]
    rcases (norm_nonneg (y - x)).eq_or_lt with h | h
    · rw [← h]; simp
    · rw [inv_mul_cancel₀ h.ne', mul_one]
  · have hne : ‖x - x₀‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hx)
    unfold radialDeriv
    exact ((hc.comp (continuous_id.sub continuous_const).norm).continuousAt).smul
      ((((continuous_id.sub continuous_const).norm.continuousAt).inv₀ hne).smul
        ((innerSL ℝ).continuous.comp (continuous_id.sub continuous_const)).continuousAt)

theorem contDiff_radial : ContDiff ℝ 1 (fun y : H ↦ convexMajorant η ‖y - x₀‖) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x ↦ (hasFDerivAt_radial hmono h0 hneg hlim x).differentiableAt, ?_⟩
  have : fderiv ℝ (fun y : H ↦ convexMajorant η ‖y - x₀‖) = radialDeriv η x₀ :=
    funext fun x ↦ (hasFDerivAt_radial hmono h0 hneg hlim x).fderiv
  rw [this]
  exact continuous_radialDeriv hmono h0 hneg hlim

theorem convexOn_radial : ConvexOn ℝ univ (fun y : H ↦ convexMajorant η ‖y - x₀‖) := by
  have := (radial_convexOn (E := H) (convexOn_convexMajorant hmono h0 hneg hlim)
    (monotoneOn_convexMajorant hmono h0 hneg hlim)).translate_right (-x₀)
  simpa [Function.comp_def, neg_add_eq_sub] using this

end Radial

/-- Affine functions are concave. -/
theorem concaveOn_affine (v : StrongDual ℝ H) (c : ℝ) : ConcaveOn ℝ univ (fun x ↦ v x + c) := by
  refine ⟨convex_univ, fun x _ y _ a b _ _ hab ↦ ?_⟩
  simp only [smul_eq_mul, map_add, map_smul]
  have : c = a * c + b * c := by rw [← add_mul, hab, one_mul]
  linarith

/-- Thm. 1.10(ii) of [Mordukhovich 2018] (smooth variational description of regular normals):
`v ∈ N̂(x₀; Ω)` iff there is a concave `C¹` function `ψ` with `∇ψ(x₀) = v` attaining its maximum
relative to `Ω` uniquely at `x₀`. -/
theorem mem_regularNormalCone_iff_exists_concave {Ω : Set H} {v : StrongDual ℝ H}
    (hx : x₀ ∈ Ω) :
    v ∈ regularNormalCone Ω x₀ ↔ ∃ ψ : H → ℝ, ContDiff ℝ 1 ψ ∧ ConcaveOn ℝ univ ψ ∧
      HasFDerivAt ψ v x₀ ∧ ∀ x ∈ Ω, x ≠ x₀ → ψ x < ψ x₀ := by
  constructor
  · intro hv
    set q : H → ℝ := fun x ↦ v (x - x₀) / ‖x - x₀‖
    have hB : ∃ B, ∀ x ∈ Ω, x ≠ x₀ → q x ≤ B := ⟨‖v‖, fun x _ hx0 ↦ by
      have hpos : 0 < ‖x - x₀‖ := norm_pos_iff.2 (sub_ne_zero.2 hx0)
      rw [div_le_iff₀ hpos]
      exact (le_abs_self _).trans (v.le_opNorm _)⟩
    have hvan : ∀ ε > 0, ∃ δ > 0, ∀ x ∈ Ω, x ≠ x₀ → ‖x - x₀‖ < δ → q x ≤ ε := by
      intro ε hε
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 (hv.2 ε hε)
      refine ⟨δ, hδ, fun x hxΩ hx0 hxδ ↦ ?_⟩
      have hpos : 0 < ‖x - x₀‖ := norm_pos_iff.2 (sub_ne_zero.2 hx0)
      rw [div_le_iff₀ hpos]
      exact hball ⟨by rwa [Metric.mem_ball, dist_eq_norm], hxΩ⟩
    set η := supModulus Ω x₀ q
    have hmono := monotone_supModulus hB
    have h0 := supModulus_nonneg hB
    have hneg : ∀ t ≤ 0, η t = 0 := fun t ht ↦ supModulus_of_nonpos ht
    have hlim := tendsto_supModulus hB hvan
    refine ⟨fun x ↦ v (x - x₀) - convexMajorant η ‖x - x₀‖, ?_, ?_, ?_, ?_⟩
    · exact ((v.contDiff.comp (contDiff_id.sub contDiff_const)).sub
        (contDiff_radial hmono h0 hneg hlim))
    · have hlin : ConcaveOn ℝ univ (fun x ↦ v (x - x₀)) :=
        (concaveOn_affine v (-v x₀)).congr fun x _ ↦ by simp [sub_eq_add_neg]
      exact hlin.sub (convexOn_radial hmono h0 hneg hlim)
    · have h1 := (v.hasFDerivAt.comp x₀ ((hasFDerivAt_id x₀).sub_const x₀)).sub
        (hasFDerivAt_radial (x₀ := x₀) hmono h0 hneg hlim x₀)
      have h2 : v.comp (ContinuousLinearMap.id ℝ H) - radialDeriv η x₀ x₀ = v := by
        simp [radialDeriv, convexMajorantDeriv_zero hneg]
      rw [h2] at h1
      exact h1
    · intro x hxΩ hx0
      have hpos : 0 < ‖x - x₀‖ := norm_pos_iff.2 (sub_ne_zero.2 hx0)
      have h1 := le_supModulus hB hxΩ hx0
      have h2 := mul_lt_convexMajorant hmono h0 hneg hlim hpos
      simp only [q] at h1
      rw [div_le_iff₀ hpos] at h1
      simp only [sub_self, map_zero, norm_zero, convexMajorant_zero]
      nlinarith
  · rintro ⟨ψ, -, -, hψ, hmax⟩
    rw [mem_regularNormalCone_iff_exists_localMax hx]
    refine ⟨ψ, hψ, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hxΩ
    by_cases hx0 : x = x₀
    · rw [hx0]
    · exact (hmax x hxΩ hx0).le

/-- Thm. 1.27 of [Mordukhovich 2018], second part: if `φ` is bounded below and `v ∈ ∂̂φ(x₀)`,
there is a concave `C¹` function `ψ` with `ψ x₀ = φ x₀` and `∇ψ(x₀) = v` such that `ψ - φ`
attains its global maximum `0` uniquely at `x₀`. -/
theorem exists_concave_support_of_mem_regularSubdiff {φ : H → EReal} {v : StrongDual ℝ H}
    {r : ℝ} (hr : φ x₀ = r) (hbdd : ∃ m : ℝ, ∀ x, (m : EReal) ≤ φ x)
    (hv : v ∈ regularSubdiff φ x₀) :
    ∃ ψ : H → ℝ, ContDiff ℝ 1 ψ ∧ ConcaveOn ℝ univ ψ ∧ HasFDerivAt ψ v x₀ ∧ ψ x₀ = r ∧
      ∀ x ≠ x₀, (ψ x : EReal) < φ x := by
  obtain ⟨m, hm⟩ := hbdd
  rw [mem_regularSubdiff_iff hr] at hv
  set S : Set H := {x | φ x ≠ ⊤}
  set q : H → ℝ := fun x ↦ (r - (φ x).toReal + v (x - x₀)) / ‖x - x₀‖
  have hfin : ∀ x ∈ S, φ x = ((φ x).toReal : EReal) := fun x hx ↦
    (EReal.coe_toReal hx (ne_bot_of_le_ne_bot (EReal.coe_ne_bot m) (hm x))).symm
  have hvan : ∀ ε > 0, ∃ δ > 0, ∀ x ∈ S, x ≠ x₀ → ‖x - x₀‖ < δ → q x ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hv ε hε)
    refine ⟨δ, hδ, fun x hxS hx0 hxδ ↦ ?_⟩
    have hpos : 0 < ‖x - x₀‖ := norm_pos_iff.2 (sub_ne_zero.2 hx0)
    have h1 := hball (by rwa [dist_eq_norm])
    rw [hfin x hxS, EReal.coe_le_coe_iff] at h1
    simp only [q]
    rw [div_le_iff₀ hpos]
    linarith
  have hB : ∃ B, ∀ x ∈ S, x ≠ x₀ → q x ≤ B := by
    obtain ⟨δ, hδ, hq⟩ := hvan 1 one_pos
    refine ⟨max 1 ((|r - m|) / δ + ‖v‖), fun x hxS hx0 ↦ ?_⟩
    by_cases hxδ : ‖x - x₀‖ < δ
    · exact (hq x hxS hx0 hxδ).trans (le_max_left _ _)
    · refine le_trans ?_ (le_max_right _ _)
      rw [not_lt] at hxδ
      have hpos : 0 < ‖x - x₀‖ := lt_of_lt_of_le hδ hxδ
      have hmx : m ≤ (φ x).toReal := by
        have := hm x; rw [hfin x hxS, EReal.coe_le_coe_iff] at this; exact this
      simp only [q]
      rw [div_le_iff₀ hpos, add_mul]
      have h1 : v (x - x₀) ≤ ‖v‖ * ‖x - x₀‖ := (le_abs_self _).trans (v.le_opNorm _)
      have h2 : r - (φ x).toReal ≤ |r - m| / δ * ‖x - x₀‖ := by
        have h3 : r - (φ x).toReal ≤ |r - m| := (by linarith : r - (φ x).toReal ≤ r - m).trans
          (le_abs_self _)
        have h4 : |r - m| ≤ |r - m| / δ * ‖x - x₀‖ := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
          exact mul_le_mul_of_nonneg_left hxδ (abs_nonneg _)
        linarith
      linarith
  set η := supModulus S x₀ q
  have hmono := monotone_supModulus hB
  have h0 := supModulus_nonneg hB
  have hneg : ∀ t ≤ 0, η t = 0 := fun t ht ↦ supModulus_of_nonpos ht
  have hlim := tendsto_supModulus hB hvan
  refine ⟨fun x ↦ r + v (x - x₀) - convexMajorant η ‖x - x₀‖, ?_, ?_, ?_, ?_, ?_⟩
  · exact (contDiff_const.add (v.contDiff.comp (contDiff_id.sub contDiff_const))).sub
      (contDiff_radial hmono h0 hneg hlim)
  · have hlin : ConcaveOn ℝ univ (fun x ↦ r + v (x - x₀)) :=
      (concaveOn_affine v (r - v x₀)).congr fun x _ ↦ by simp only [map_sub]; ring
    exact hlin.sub (convexOn_radial hmono h0 hneg hlim)
  · have h1 := ((v.hasFDerivAt.comp x₀ ((hasFDerivAt_id x₀).sub_const x₀)).const_add r).sub
      (hasFDerivAt_radial (x₀ := x₀) hmono h0 hneg hlim x₀)
    have h2 : v.comp (ContinuousLinearMap.id ℝ H) - radialDeriv η x₀ x₀ = v := by
      simp [radialDeriv, convexMajorantDeriv_zero hneg]
    rw [h2] at h1
    exact h1
  · simp [convexMajorant_zero]
  · intro x hx0
    by_cases hxS : x ∈ S
    · have hpos : 0 < ‖x - x₀‖ := norm_pos_iff.2 (sub_ne_zero.2 hx0)
      have h1 := le_supModulus hB hxS hx0
      have h2 := mul_lt_convexMajorant hmono h0 hneg hlim hpos
      simp only [q] at h1
      rw [div_le_iff₀ hpos] at h1
      rw [hfin x hxS, EReal.coe_lt_coe_iff]
      nlinarith
    · have : φ x = ⊤ := not_not.1 hxS
      rw [this]
      exact EReal.coe_lt_top _

end VariationalAnalysis
