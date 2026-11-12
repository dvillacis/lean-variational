/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis.SecondOrder.TwiceEpiProto

/-!
# Second-order expansion of Moreau envelopes under proto-differentiability

This file contains the first part of the proof of the converse implication of
[Mordukhovich 2024, Thm. 1.98]: if `φ` is continuously prox-regular at `x̄` for `v̄` and `∂φ` is
proto-differentiable at `(x̄, v̄)`, then the proximal mapping `P_λφ` is directionally
differentiable at `x̄ + λv̄` and the Moreau envelope `e_λφ` has a second-order expansion there.

## Main results

* `tendsto_second_quot_of_hasDirDerivAt`: if `e` is differentiable around `ū` with a Lipschitz
  gradient `f` that is directionally differentiable at `ū` with derivative `G`, then
  `(e(ū + tw') - e(ū) - t⟨f(ū), w'⟩)/t² → ⟨G(w), w⟩/2` as `t ↓ 0`, `w' → w`.
* `ContinuouslyProxRegularFor.exists_dirDifferentiableAt_proximalMap`: for `φ` l.s.c.,
  prox-bounded and continuously prox-regular with `∂φ` proto-differentiable, and small `λ`,
  `P_λφ` is directionally differentiable at `x̄ + λv̄`.
* `ContinuouslyProxRegularFor.exists_tendsto_moreauEnvelope_second_quot`: under the same
  assumptions, `(e_λφ(ū + tw') - e_λφ(ū) - t⟨g, w'⟩)/t² → (‖w‖² - ⟨DP_λφ(w), w⟩)/(2λ)`
  with `ū = x̄ + λg`.
-/

open Filter Topology Set Metric InnerProductSpace
open scoped NNReal RealInnerProductSpace

namespace VariationalAnalysis

section Expansion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Second-order expansion of a `C^{1,1}` function with directionally differentiable
gradient.** If `e` is differentiable on `B(ū, δ)` with gradient `f`, `f` is Lipschitz there and
directionally differentiable at `ū` with derivative `G`, then
`(e(ū + t_k w_k) - e(ū) - t_k⟨f(ū), w_k⟩)/t_k² → ⟨G(w), w⟩/2` for `t_k ↓ 0`, `w_k → w`. -/
theorem tendsto_second_quot_of_hasDirDerivAt {e : E → ℝ} {f G : E → E} {ū : E} {δ : ℝ}
    {K : ℝ≥0} (hδ : 0 < δ) (he : ∀ u ∈ ball ū δ, HasFDerivAt e (toDual ℝ E (f u)) u)
    (hL : LipschitzOnWith K f (ball ū δ)) (hG : ∀ w, HasDirDerivAt f ū w (G w))
    {t : ℕ → ℝ} (ht : Tendsto t atTop (𝓝[>] 0)) {w : ℕ → E} {w₀ : E}
    (hw : Tendsto w atTop (𝓝 w₀)) :
    Tendsto (fun k ↦ ((t k) ^ 2)⁻¹ * (e (ū + t k • w k) - e ū - t k * ⟪f ū, w k⟫_ℝ)) atTop
      (𝓝 (⟪G w₀, w₀⟫_ℝ / 2)) := by
  have hū : ū ∈ ball ū δ := mem_ball_self hδ
  -- the function minus its linearization
  obtain ⟨h, hh_def⟩ : ∃ h : E → ℝ, h = fun u ↦ e u - e ū - toDual ℝ E (f ū) (u - ū) :=
    ⟨_, rfl⟩
  have hval : ∀ u, h u = e u - e ū - ⟪f ū, u - ū⟫_ℝ := fun u ↦ by
    simp only [hh_def, toDual_apply_apply]
  have hh0 : h ū = 0 := by rw [hval]; simp
  have hh : ∀ u ∈ ball ū δ, HasFDerivAt h (toDual ℝ E (f u - f ū)) u := fun u hu ↦ by
    have h1 : HasFDerivAt (fun u ↦ toDual ℝ E (f ū) (u - ū)) (toDual ℝ E (f ū)) u :=
      ((toDual ℝ E (f ū)).hasFDerivAt.comp u ((hasFDerivAt_id u).sub_const ū)).congr_fderiv
        (ContinuousLinearMap.comp_id _)
    rw [hh_def, map_sub]
    exact ((he u hu).sub_const (e ū)).sub h1
  have hbound : ∀ u ∈ ball ū δ, ‖toDual ℝ E (f u - f ū)‖ ≤ K * ‖u - ū‖ := fun u hu ↦ by
    rw [LinearIsometryEquiv.norm_map, ← dist_eq_norm, ← dist_eq_norm]
    exact hL.dist_le_mul u hu ū hū
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ⟪G w₀, w₀⟫_ℝ := ⟨_, rfl⟩
  -- the expansion along the fixed direction `w₀`
  have hA : Tendsto (fun s : ℝ ↦ (s ^ 2)⁻¹ * h (ū + s • w₀)) (𝓝[>] 0) (𝓝 (c / 2)) := by
    have hin : Tendsto (fun s : ℝ ↦ ⟪s⁻¹ • (f (ū + s • w₀) - f ū), w₀⟫_ℝ) (𝓝[>] 0) (𝓝 c) := by
      rw [hc]; exact (hG w₀).inner tendsto_const_nhds
    rw [Metric.tendsto_nhdsWithin_nhds] at hin ⊢
    intro ε hε
    obtain ⟨η, hη, Hη⟩ := hin (ε / 2) (half_pos hε)
    refine ⟨min η (δ / (‖w₀‖ + 1)), lt_min hη (by positivity), fun τ hτ hτη ↦ ?_⟩
    have hτ0 : (0 : ℝ) < τ := hτ
    rw [Real.dist_eq, sub_zero, abs_of_pos hτ0] at hτη
    have hτδ : τ * (‖w₀‖ + 1) < δ := by
      have := hτη.trans_le (min_le_right _ _)
      rwa [lt_div_iff₀ (by positivity)] at this
    have hmem : ∀ s ∈ Icc (0 : ℝ) τ, ū + s • w₀ ∈ ball ū δ := fun s hs ↦ by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.1]
      nlinarith [norm_nonneg w₀, hs.2, mul_le_mul_of_nonneg_right hs.2 (norm_nonneg w₀)]
    have hd : ∀ s ∈ Icc (0 : ℝ) τ, HasDerivAt (fun s ↦ h (ū + s • w₀) - c / 2 * s ^ 2)
        (⟪f (ū + s • w₀) - f ū, w₀⟫_ℝ - c * s) s := fun s hs ↦ by
      have h1 := (hh _ (hmem s hs)).comp_hasDerivAt s
        (((hasDerivAt_id s).smul_const w₀).const_add ū)
      have h2 := (hasDerivAt_pow 2 s).const_mul (c / 2)
      refine (h1.sub h2).congr_deriv ?_
      simp only [toDual_apply_apply, one_smul]
      norm_num
      ring
    have hbd : ∀ s ∈ Icc (0 : ℝ) τ, ‖⟪f (ū + s • w₀) - f ū, w₀⟫_ℝ - c * s‖ ≤ ε / 2 * τ := by
      intro s hs
      rcases hs.1.eq_or_lt with h0 | h0
      · rw [← h0]
        simp only [zero_smul, add_zero, sub_self, inner_zero_left, mul_zero, norm_zero]
        positivity
      · have := Hη h0 (by
          rw [Real.dist_eq, sub_zero, abs_of_pos h0]
          exact (hs.2.trans_lt hτη).trans_le (min_le_left _ _))
        rw [Real.dist_eq, real_inner_smul_left] at this
        have e1 : ⟪f (ū + s • w₀) - f ū, w₀⟫_ℝ - c * s =
            s * (s⁻¹ * ⟪f (ū + s • w₀) - f ū, w₀⟫_ℝ - c) := by
          field_simp
        rw [e1, Real.norm_eq_abs, abs_mul, abs_of_pos h0, mul_comm (ε / 2)]
        exact mul_le_mul hs.2 this.le (abs_nonneg _) hτ0.le
    have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s hs ↦ (hd s hs).hasDerivWithinAt) hbd (convex_Icc 0 τ)
      (left_mem_Icc.2 hτ0.le) (right_mem_Icc.2 hτ0.le)
    simp only [zero_smul, add_zero, hh0, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, Real.norm_eq_abs, abs_of_pos hτ0] at key
    rw [Real.dist_eq]
    have e2 : (τ ^ 2)⁻¹ * h (ū + τ • w₀) - c / 2 =
        (τ ^ 2)⁻¹ * (h (ū + τ • w₀) - c / 2 * τ ^ 2) := by
      field_simp
    rw [e2, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (τ ^ 2)⁻¹)]
    calc (τ ^ 2)⁻¹ * |h (ū + τ • w₀) - c / 2 * τ ^ 2| ≤ (τ ^ 2)⁻¹ * (ε / 2 * τ * τ) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = ε / 2 := by field_simp
      _ < ε := half_lt_self hε
  -- the dependence on the direction
  have hpos : ∀ᶠ k in atTop, 0 < t k := (tendsto_nhdsWithin_iff.1 ht).2
  have ht0 : Tendsto t atTop (𝓝 0) := tendsto_nhds_of_tendsto_nhdsWithin ht
  have hwb : ∀ᶠ k in atTop, ‖w k‖ ≤ ‖w₀‖ + 1 :=
    hw.norm.eventually (ge_mem_nhds (lt_add_one _))
  have htδ : ∀ᶠ k in atTop, t k * (‖w₀‖ + 1) < δ := by
    have := ht0.mul_const (‖w₀‖ + 1)
    rw [zero_mul] at this
    exact this.eventually (gt_mem_nhds hδ)
  have hB : Tendsto (fun k ↦ ((t k) ^ 2)⁻¹ * h (ū + t k • w k) -
      ((t k) ^ 2)⁻¹ * h (ū + t k • w₀)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun k ↦ (K : ℝ) * (‖w₀‖ + 1) * ‖w k - w₀‖) atTop (𝓝 0) := by
      have := ((hw.sub_const w₀).norm).const_mul ((K : ℝ) * (‖w₀‖ + 1))
      simpa using this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hpos, hwb, htδ] with k hk hkw hkδ
    have hsub : closedBall ū (t k * (‖w₀‖ + 1)) ⊆ ball ū δ := closedBall_subset_ball hkδ
    have hin : ∀ z : E, ‖z‖ ≤ ‖w₀‖ + 1 → ū + t k • z ∈ closedBall ū (t k * (‖w₀‖ + 1)) :=
      fun z hz ↦ by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_of_nonneg hk.le]
        exact mul_le_mul_of_nonneg_left hz hk.le
    have key := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (s := closedBall ū (t k * (‖w₀‖ + 1))) (C := K * (t k * (‖w₀‖ + 1)))
      (fun u hu ↦ (hh u (hsub hu)).hasFDerivWithinAt)
      (fun u hu ↦ (hbound u (hsub hu)).trans (mul_le_mul_of_nonneg_left
        (by rw [← dist_eq_norm]; exact mem_closedBall.1 hu) K.coe_nonneg))
      (convex_closedBall _ _) (hin w₀ (by linarith)) (hin (w k) hkw)
    rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg hk.le] at key
    rw [← mul_sub, norm_mul, norm_inv, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ t k ^ 2)]
    calc ((t k) ^ 2)⁻¹ * ‖h (ū + t k • w k) - h (ū + t k • w₀)‖
        ≤ ((t k) ^ 2)⁻¹ * (K * (t k * (‖w₀‖ + 1)) * (t k * ‖w k - w₀‖)) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = K * (‖w₀‖ + 1) * ‖w k - w₀‖ := by field_simp
  have := (hA.comp ht).add hB
  rw [add_zero, hc] at this
  refine this.congr fun k ↦ ?_
  simp only [Function.comp_apply, add_sub_cancel]
  rw [hval, add_sub_cancel_left, real_inner_smul_right]

end Expansion

section Prox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {φ : E → EReal} {x₀ : E}

/-- If `φ` is l.s.c., prox-bounded and continuously prox-regular at `x̄` for `v̄ = ⟨g, ·⟩` and
`∂φ` is proto-differentiable at `(x̄, v̄)`, then for all small `λ > 0` the proximal mapping `P_λφ`
is single-valued and Lipschitz around `x̄ + λg` and directionally differentiable at `x̄ + λg`. -/
theorem ContinuouslyProxRegularFor.exists_dirDifferentiableAt_proximalMap {g : E}
    (hφ : ContinuouslyProxRegularFor φ x₀ (toDual ℝ E g))
    (hproto : ProtoDifferentiableAt (subdiff φ) x₀ (toDual ℝ E g))
    (hlsc : ∀ x, LowerSemicontinuousAt φ x)
    (hbd : ∃ a b : ℝ, ∀ x, ((a - b * ‖x - x₀‖ ^ 2 : ℝ) : EReal) ≤ φ x) :
    ∃ l₀ > (0 : ℝ), ∀ l, 0 < l → l < l₀ → ∃ δ > (0 : ℝ), ∃ p : E → E,
      p (x₀ + l • g) = x₀ ∧
      (∀ u ∈ ball (x₀ + l • g) δ, proximalMap φ l u = {p u}) ∧
      LipschitzOnWith 2 p (ball (x₀ + l • g) δ) ∧ DirDifferentiableAt p (x₀ + l • g) := by
  obtain ⟨l₀, hl₀, H⟩ := hφ.eventually_mem_subdiff_iff hlsc hbd
  refine ⟨l₀, hl₀, fun l hl hll ↦ ?_⟩
  obtain ⟨δ, hδ, p, hp0, hpU, hLip, hgraph⟩ := H l hl hll
  refine ⟨δ, hδ, p, hp0, hpU, hLip, ?_⟩
  have hd : GeometricallyDerivableAt (graph fun u ↦ ({p u} : Set E))
      (x₀ + l • g, p (x₀ + l • g)) := by
    rw [hp0]
    exact (protoDifferentiableAt_iff_geometricallyDerivableAt_graph hl.ne' hp0 hgraph).1 hproto
  exact dirDifferentiableAt_of_geometricallyDerivableAt (ball_mem_nhds _ hδ) hLip hd

/-- **Second-order expansion of the Moreau envelope.** If `φ` is l.s.c., prox-bounded and
continuously prox-regular at `x̄` for `v̄ = ⟨g, ·⟩` and `∂φ` is proto-differentiable at
`(x̄, v̄)`, then for all small `λ > 0` the proximal mapping `P_λφ = p` is directionally
differentiable at `ū = x̄ + λg`, with derivative `D` say, and
`(e_λφ(ū + t_k w_k) - e_λφ(ū) - t_k⟨g, w_k⟩)/t_k² → (‖w‖² - ⟨D(w), w⟩)/(2λ)` for `t_k ↓ 0`,
`w_k → w`. -/
theorem ContinuouslyProxRegularFor.exists_tendsto_moreauEnvelope_second_quot {g : E}
    (hφ : ContinuouslyProxRegularFor φ x₀ (toDual ℝ E g))
    (hproto : ProtoDifferentiableAt (subdiff φ) x₀ (toDual ℝ E g))
    (hlsc : ∀ x, LowerSemicontinuousAt φ x)
    (hbd : ∃ a b : ℝ, ∀ x, ((a - b * ‖x - x₀‖ ^ 2 : ℝ) : EReal) ≤ φ x) :
    ∃ l₀ > (0 : ℝ), ∀ l, 0 < l → l < l₀ → ∃ δ > (0 : ℝ), ∃ p D : E → E,
      p (x₀ + l • g) = x₀ ∧
      (∀ u ∈ ball (x₀ + l • g) δ, proximalMap φ l u = {p u}) ∧
      (∀ u ∈ ball (x₀ + l • g) δ,
        (((moreauEnvelope φ l u).toReal : ℝ) : EReal) = moreauEnvelope φ l u) ∧
      (∀ w, HasDirDerivAt p (x₀ + l • g) w (D w)) ∧
      ∀ t : ℕ → ℝ, Tendsto t atTop (𝓝[>] 0) → ∀ (w : ℕ → E) (w₀ : E),
        Tendsto w atTop (𝓝 w₀) →
        Tendsto (fun k ↦ ((t k) ^ 2)⁻¹ * ((moreauEnvelope φ l (x₀ + l • g + t k • w k)).toReal -
          (moreauEnvelope φ l (x₀ + l • g)).toReal - t k * ⟪g, w k⟫_ℝ)) atTop
          (𝓝 ((2 * l)⁻¹ * (‖w₀‖ ^ 2 - ⟪D w₀, w₀⟫_ℝ))) := by
  obtain ⟨l₁, hl₁, H1⟩ := hφ.exists_dirDifferentiableAt_proximalMap hproto hlsc hbd
  obtain ⟨l₂, hl₂, H2⟩ := hφ.1.exists_moreauEnvelope hlsc hbd
  refine ⟨min l₁ l₂, lt_min hl₁ hl₂, fun l hl hll ↦ ?_⟩
  obtain ⟨δ₁, hδ₁, p, hp0, hpU, -, hdir⟩ := H1 l hl (hll.trans_le (min_le_left _ _))
  obtain ⟨δ₂, hδ₂, p₂, hpU₂, hfin, hder, hLip⟩ := H2 l hl (hll.trans_le (min_le_right _ _))
  choose D hD using hdir
  have hsub₁ : ball (x₀ + l • g) (min δ₁ δ₂) ⊆ ball (x₀ + l • g) δ₁ :=
    ball_subset_ball (min_le_left _ _)
  have hsub₂ : ball (x₀ + l • g) (min δ₁ δ₂) ⊆ ball (x₀ + l • g) δ₂ :=
    ball_subset_ball (min_le_right _ _)
  have hpp : ∀ u ∈ ball (x₀ + l • g) (min δ₁ δ₂), p₂ u = p u := fun u hu ↦
    Set.singleton_eq_singleton_iff.1 ((hpU₂ u (hsub₂ hu)).symm.trans (hpU u (hsub₁ hu)))
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, p, D, hp0, fun u hu ↦ hpU u (hsub₁ hu),
    fun u hu ↦ hfin u (hsub₂ hu), hD, fun t ht w w₀ hw ↦ ?_⟩
  obtain ⟨f, hf⟩ : ∃ f : E → E, f = fun u ↦ l⁻¹ • (u - p u) := ⟨_, rfl⟩
  have hfū : f (x₀ + l • g) = g := by
    rw [hf]
    simp only [hp0, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hl.ne', one_smul]
  have he : ∀ u ∈ ball (x₀ + l • g) (min δ₁ δ₂),
      HasFDerivAt (fun u ↦ (moreauEnvelope φ l u).toReal) (toDual ℝ E (f u)) u := fun u hu ↦ by
    have := hder u (hsub₂ hu)
    rw [hpp u hu] at this
    rw [hf]
    exact this
  have hfL : LipschitzOnWith (Real.toNNReal (3 / l)) f (ball (x₀ + l • g) (min δ₁ δ₂)) := by
    refine LipschitzOnWith.of_dist_le_mul fun u₁ hu₁ u₂ hu₂ ↦ ?_
    have := hLip.dist_le_mul u₁ (hsub₂ hu₁) u₂ (hsub₂ hu₂)
    rw [hpp u₁ hu₁, hpp u₂ hu₂] at this
    rw [hf]
    exact this
  have hG : ∀ z, HasDirDerivAt f (x₀ + l • g) z (l⁻¹ • (z - D z)) := fun z ↦ by
    have h1 : Tendsto (fun s : ℝ ↦ l⁻¹ • (z - s⁻¹ • (p (x₀ + l • g + s • z) - p (x₀ + l • g))))
        (𝓝[>] 0) (𝓝 (l⁻¹ • (z - D z))) := (tendsto_const_nhds.sub (hD z)).const_smul l⁻¹
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : (s : ℝ) ≠ 0 := (show (0 : ℝ) < s from hs).ne'
    simp only [hf]
    have e1 : x₀ + l • g + s • z - p (x₀ + l • g + s • z) - (x₀ + l • g - p (x₀ + l • g)) =
        s • z - (p (x₀ + l • g + s • z) - p (x₀ + l • g)) := by abel
    rw [← smul_sub, e1, smul_comm s⁻¹ l⁻¹, smul_sub s⁻¹ (s • z), smul_smul,
      inv_mul_cancel₀ hs0, one_smul]
  have := tendsto_second_quot_of_hasDirDerivAt (lt_min hδ₁ hδ₂) he hfL hG ht hw
  rw [hfū] at this
  have hlim : ⟪l⁻¹ • (w₀ - D w₀), w₀⟫_ℝ / 2 = (2 * l)⁻¹ * (‖w₀‖ ^ 2 - ⟪D w₀, w₀⟫_ℝ) := by
    rw [real_inner_smul_left, inner_sub_left, real_inner_self_eq_norm_sq, mul_inv]
    ring
  rwa [hlim] at this

end Prox

end VariationalAnalysis
