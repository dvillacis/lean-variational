/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis.SecondOrder.ProxSemidiff

/-!
# Twice epi-differentiability of Moreau envelopes

This file proves one implication of part (a) of [Mordukhovich 2024, Cor. 1.101] and its first
formula: if `φ` is l.s.c., prox-bounded, prox-regular and twice epi-differentiable at `x̄` for
`v̄`, then for all small `λ > 0` the Moreau envelope `e_λφ` is twice epi-differentiable at
`x̄ + λv̄` for `v̄`, and `d²(e_λφ)(x̄ + λv̄, v̄)/2 = e_λ(d²φ(x̄, v̄)/2)`.

## Main results

* `moreauEnvelope_shiftTilt`: the Moreau envelope of the shifted and tilted function.
* `moreauEnvelope_half_secondDiffQuot_shift`: [Mordukhovich 2024, Lemma 1.94, (1.131)] at a
  general point, `e_λ(Δ²_tφ(x̄, v̄)/2) = Δ²_t(e_λφ)(x̄ + λv̄, v̄)/2`.
* `twiceEpiDifferentiableAt_of_tendsto_secondDiffQuot`: continuous convergence of the
  second-order difference quotients gives twice epi-differentiability.
* `ProxRegularFor.exists_twiceEpiDifferentiableAt_moreauEnvelope`:
  [Mordukhovich 2024, Cor. 1.101], twice epi-differentiability of `e_λφ` and the first formula.
-/

open Filter Topology Set Metric InnerProductSpace
open scoped NNReal RealInnerProductSpace

namespace VariationalAnalysis

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If the second-order difference quotients `Δ²_tψ(x, v)(w')` converge to `c(w)` as `t ↓ 0`,
`w' → w`, for every `w`, then `ψ` is twice epi-differentiable at `x` for `v` and
`d²ψ(x, v) = c`. -/
theorem twiceEpiDifferentiableAt_of_tendsto_secondDiffQuot {ψ : E → EReal} {x : E}
    {v : StrongDual ℝ E} {c : E → EReal} (hfin : ∃ r : ℝ, ψ x = r)
    (h : ∀ w, Tendsto (fun q : ℝ × E ↦ secondDiffQuot ψ x v q.1 q.2) (𝓝[>] 0 ×ˢ 𝓝 w)
      (𝓝 (c w))) :
    TwiceEpiDifferentiableAt ψ x v ∧ ∀ w, secondSubderiv ψ x v w = c w := by
  have hsub : ∀ w, secondSubderiv ψ x v w = c w := fun w ↦ (h w).liminf_eq
  refine ⟨⟨hfin, fun t ht w ↦ ⟨fun wk hwk ↦ ?_, ⟨fun _ ↦ w, tendsto_const_nhds, ?_⟩⟩⟩, hsub⟩
  · rw [hsub]
    have hc := (h w).comp (ht.prodMk hwk)
    simp only [Function.comp_def] at hc
    exact hc.liminf_eq.ge
  · rw [hsub]
    have hc := (h w).comp (ht.prodMk (tendsto_const_nhds (x := w)))
    simp only [Function.comp_def] at hc
    exact hc.limsup_eq.le

end General

section Prox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {φ : E → EReal} {x₀ : E}

omit [FiniteDimensional ℝ E] in
/-- The Moreau envelope of the shifted and tilted function:
`e_λ(φ(x̄ + ·) - φ(x̄) - ⟨g, ·⟩)(u) = e_λφ(x̄ + λg + u) - φ(x̄) - ⟨g, u⟩ - (λ/2)‖g‖²`. -/
theorem moreauEnvelope_shiftTilt (φ : E → EReal) (x₀ g : E) {l : ℝ} (hl : l ≠ 0) (u : E) :
    moreauEnvelope (shiftTilt φ x₀ g) l u = moreauEnvelope φ l (x₀ + l • g + u) +
      ((-((φ x₀).toReal + ⟪g, u⟫_ℝ + l / 2 * ‖g‖ ^ 2) : ℝ) : EReal) := by
  have hcomm : x₀ + u + l • g = x₀ + l • g + u := by abel
  show (⨅ x, proxObjective (shiftTilt φ x₀ g) l u x) =
    (⨅ y, proxObjective φ l (x₀ + l • g + u) y) + _
  simp only [proxObjective_shiftTilt φ x₀ g hl, hcomm]
  rw [iInf_add_coe]
  congr 1
  exact (show Function.Surjective fun x : E ↦ x₀ + x from
    fun y ↦ ⟨y - x₀, add_sub_cancel _ _⟩).iInf_comp
      (fun y ↦ proxObjective φ l (x₀ + l • g + u) y)

/-- [Mordukhovich 2024, Lemma 1.94, (1.131)], first formula at a general point: if `φ(x̄)` is
finite and `e_λφ(x̄ + λg) = φ(x̄) + (λ/2)‖g‖²` (e.g. `x̄ ∈ P_λφ(x̄ + λg)`), then
`e_λ(Δ²_tφ(x̄, v̄)/2) = Δ²_t(e_λφ)(x̄ + λg, v̄)/2` for `v̄ = ⟨g, ·⟩`. -/
theorem moreauEnvelope_half_secondDiffQuot_shift {g : E} {r₀ l t : ℝ} (hr₀ : φ x₀ = r₀)
    (hl : l ≠ 0)
    (he : moreauEnvelope φ l (x₀ + l • g) = ((r₀ + l / 2 * ‖g‖ ^ 2 : ℝ) : EReal))
    (ht : 0 < t) (w : E) :
    moreauEnvelope (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondDiffQuot φ x₀ (toDual ℝ E g) t w)
      l w = ((1 / 2 : ℝ) : EReal) *
        secondDiffQuot (moreauEnvelope φ l) (x₀ + l • g) (toDual ℝ E g) t w := by
  have hq : (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondDiffQuot φ x₀ (toDual ℝ E g) t w) =
      fun w ↦ ((t⁻¹ ^ 2 : ℝ) : EReal) * shiftTilt φ x₀ g (t • w) := by
    funext w
    rw [← secondDiffQuot_shiftTilt hr₀, half_secondDiffQuot_zero (shiftTilt_zero hr₀) ht.ne']
  rw [hq, moreauEnvelope_scale _ ht, moreauEnvelope_shiftTilt φ x₀ g hl, secondDiffQuot, he,
    hr₀, EReal.toReal_coe, toDual_apply_apply, ← mul_assoc, ← EReal.coe_mul, sub_eq_add_neg,
    sub_eq_add_neg, ← EReal.coe_neg, ← EReal.coe_neg]
  have h1 : t⁻¹ ^ 2 = 1 / 2 * (2 / t ^ 2) := by field_simp
  have h2 : -(r₀ + ⟪g, t • w⟫_ℝ + l / 2 * ‖g‖ ^ 2) =
      -(r₀ + l / 2 * ‖g‖ ^ 2) + -(t * ⟪g, w⟫_ℝ) := by
    rw [real_inner_smul_right]; ring
  rw [h1, h2, EReal.coe_add, ← add_assoc]

/-- **Twice epi-differentiability of Moreau envelopes** [Mordukhovich 2024, Cor. 1.101]: let
`φ` be l.s.c., prox-bounded, prox-regular and twice epi-differentiable at `x̄` for
`v̄ = ⟨g, ·⟩`. Then for all small `λ > 0` the Moreau envelope `e_λφ` is twice epi-differentiable
at `x̄ + λg` for `v̄`, and `d²(e_λφ)(x̄ + λg, v̄)/2 = e_λ(d²φ(x̄, v̄)/2)`. -/
theorem ProxRegularFor.exists_twiceEpiDifferentiableAt_moreauEnvelope {g : E}
    (hφ : ProxRegularFor φ x₀ (toDual ℝ E g))
    (H : TwiceEpiDifferentiableAt φ x₀ (toDual ℝ E g))
    (hlsc : ∀ x, LowerSemicontinuousAt φ x)
    (hbd : ∃ a b : ℝ, ∀ x, ((a - b * ‖x - x₀‖ ^ 2 : ℝ) : EReal) ≤ φ x) :
    ∃ l₀ > (0 : ℝ), ∀ l, 0 < l → l < l₀ →
      TwiceEpiDifferentiableAt (moreauEnvelope φ l) (x₀ + l • g) (toDual ℝ E g) ∧
      ∀ w, ((1 / 2 : ℝ) : EReal) *
          secondSubderiv (moreauEnvelope φ l) (x₀ + l • g) (toDual ℝ E g) w =
        moreauEnvelope (fun w ↦ ((1 / 2 : ℝ) : EReal) *
          secondSubderiv φ x₀ (toDual ℝ E g) w) l w := by
  obtain ⟨r₀, hr₀, -⟩ := hφ.1
  obtain ⟨R, hR, hmin⟩ := exists_shiftTilt_ge hφ.mem_proxSubdiff hbd
  obtain ⟨ε, -, l₁, hl₁, H1⟩ := hφ.exists_proximalMap hlsc hbd
  refine ⟨min l₁ (1 / (R + 1)), lt_min hl₁ (by positivity), fun l hl hll ↦ ?_⟩
  have hlR : l * R < 1 := by
    have h1 : l < 1 / (R + 1) := hll.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith
  obtain ⟨δ, hδ, p, hp0, hpU, -, -, -⟩ := H1 l hl (hll.trans_le (min_le_left _ _))
  -- the value of the envelope at `x̄ + λg`
  have he : moreauEnvelope φ l (x₀ + l • g) = ((r₀ + l / 2 * ‖g‖ ^ 2 : ℝ) : EReal) := by
    have hmem : x₀ ∈ proximalMap φ l (x₀ + l • g) := by
      rw [hpU _ (mem_ball_self hδ), hp0]; exact mem_singleton _
    rw [moreauEnvelope_eq_of_mem_proximalMap hmem]
    show φ x₀ + (((2 * l)⁻¹ * ‖x₀ - (x₀ + l • g)‖ ^ 2 : ℝ) : EReal) = _
    have h1 : x₀ - (x₀ + l • g) = -(l • g) := by abel
    rw [hr₀, ← EReal.coe_add, h1, norm_neg, norm_smul, Real.norm_of_nonneg hl.le]
    congr 2
    field_simp
  obtain ⟨f, hf⟩ : ∃ f : ℝ → E → EReal,
      f = fun t w ↦ ((1 / 2 : ℝ) : EReal) * secondDiffQuot φ x₀ (toDual ℝ E g) t w := ⟨_, rfl⟩
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀ : E → EReal,
      φ₀ = fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderiv φ x₀ (toDual ℝ E g) w := ⟨_, rfl⟩
  have hepi : EpiTendsto (𝓝[>] (0 : ℝ)) f φ₀ := by
    rw [hf, hφ₀]
    exact (twiceEpiDifferentiableAt_iff_epiTendsto.1 H).2.coe_mul (by norm_num)
  have hfmin : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ w : E, ((-(R / 2) * ‖w‖ ^ 2 : ℝ) : EReal) ≤ f t w := by
    filter_upwards [self_mem_nhdsWithin] with t ht w
    rw [hf]
    show _ ≤ ((1 / 2 : ℝ) : EReal) * secondDiffQuot φ x₀ (toDual ℝ E g) t w
    rw [← secondDiffQuot_shiftTilt hr₀]
    exact half_secondDiffQuot_ge (shiftTilt_zero hr₀) hmin ht w
  have htwo : ∀ a : EReal, ((2 : ℝ) : EReal) * (((1 / 2 : ℝ) : EReal) * a) = a := fun a ↦ by
    rw [← mul_assoc, ← EReal.coe_mul]
    norm_num
  have hhalf : ∀ a : EReal, ((1 / 2 : ℝ) : EReal) * (((2 : ℝ) : EReal) * a) = a := fun a ↦ by
    rw [← mul_assoc, ← EReal.coe_mul]
    norm_num
  have hlim : ∀ w, Tendsto (fun q : ℝ × E ↦
      secondDiffQuot (moreauEnvelope φ l) (x₀ + l • g) (toDual ℝ E g) q.1 q.2)
      (𝓝[>] 0 ×ˢ 𝓝 w) (𝓝 (((2 : ℝ) : EReal) * moreauEnvelope φ₀ l w)) := by
    intro w
    have h1 := hepi.tendsto_moreauEnvelope hl hR hlR hfmin w
    have h2 := ((coeMulOrderIso 2 two_pos).continuous.tendsto _).comp h1
    refine h2.congr' ?_
    filter_upwards [(tendsto_fst (f := 𝓝[>] (0 : ℝ)) (g := 𝓝 w)).eventually
      self_mem_nhdsWithin] with q hq
    have hq0 : 0 < q.1 := hq
    show ((2 : ℝ) : EReal) * moreauEnvelope (f q.1) l q.2 = _
    rw [hf]
    show ((2 : ℝ) : EReal) * moreauEnvelope
      (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondDiffQuot φ x₀ (toDual ℝ E g) q.1 w) l q.2 = _
    rw [moreauEnvelope_half_secondDiffQuot_shift hr₀ hl.ne' he hq0, htwo]
  obtain ⟨hT, hsub⟩ := twiceEpiDifferentiableAt_of_tendsto_secondDiffQuot ⟨_, he⟩ hlim
  refine ⟨hT, fun w ↦ ?_⟩
  rw [hsub, hhalf, hφ₀]

end Prox

end VariationalAnalysis
