/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis.SecondOrder.ProxSemidiff

/-!
# Twice epi-differentiability of Moreau envelopes

This file proves part (a) of [Mordukhovich 2024, Cor. 1.101] and its first formula: for `φ`
l.s.c., prox-bounded and continuously prox-regular at `x̄` for `v̄`, and small `λ`, `φ` is twice
epi-differentiable at `x̄` for `v̄` iff `e_λφ` is twice epi-differentiable at `x̄ + λv̄`. Moreover,
if `φ` is l.s.c., prox-bounded, prox-regular and twice epi-differentiable at `x̄` for
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
* `continuouslyProxRegularFor_of_lipschitz_gradient`: a function with Lipschitz gradient around
  a point is continuously prox-regular there.
* `ContinuouslyProxRegularFor.exists_twiceEpiDifferentiableAt_iff_moreauEnvelope`:
  [Mordukhovich 2024, Cor. 1.101], the equivalence with (a).
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

/-! ### The converse implication -/

omit [FiniteDimensional ℝ E] in
/-- A function that agrees near `ū` with a differentiable function with Lipschitz gradient `f`
is continuously prox-regular at `ū` for `⟨f(ū), ·⟩`, and `∂ψ(u) = {⟨f(u), ·⟩}` near `ū`. -/
theorem continuouslyProxRegularFor_of_lipschitz_gradient [CompleteSpace E] {ψ : E → EReal}
    {e : E → ℝ} {f : E → E} {ū : E} {δ : ℝ} {K : ℝ≥0} (hδ : 0 < δ)
    (hψ : ∀ u ∈ ball ū δ, ψ u = e u)
    (he : ∀ u ∈ ball ū δ, HasFDerivAt e (toDual ℝ E (f u)) u)
    (hL : LipschitzOnWith K f (ball ū δ)) :
    ContinuouslyProxRegularFor ψ ū (toDual ℝ E (f ū)) ∧
      ∀ᶠ u in 𝓝 ū, subdiff ψ u = {toDual ℝ E (f u)} := by
  have hφ'L : LipschitzOnWith (1 * K) (fun u ↦ toDual ℝ E (f u)) (ball ū δ) :=
    (toDual ℝ E).lipschitz.comp_lipschitzOnWith hL
  have hsub : ∀ᶠ u in 𝓝 ū, subdiff ψ u = {toDual ℝ E (f u)} := by
    filter_upwards [eventually_subdiff_eq_singleton_of_lipschitz (ball_mem_nhds ū hδ) he hφ'L,
      ball_mem_nhds ū hδ] with u h1 hu
    rw [← h1]
    exact subdiff_congr (eventually_of_mem (isOpen_ball.mem_nhds hu) hψ)
  refine ⟨?_, hsub⟩
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.eventually_nhds_iff.1 hsub
  have hcont : ∀ u ∈ ball ū δ, ContinuousAt ψ u := fun u hu ↦
    ((continuous_coe_real_ereal.continuousAt).comp (he u hu).continuousAt).congr
      (eventually_of_mem (isOpen_ball.mem_nhds hu) fun z hz ↦ (hψ z hz).symm)
  have hv₀ : toDual ℝ E (f ū) ∈ subdiff ψ ū := by
    rw [hsub.self_of_nhds]; exact mem_singleton _
  have hε : 0 < min ρ δ / 2 := half_pos (lt_min hρ hδ)
  have hερ : min ρ δ / 2 < ρ := (half_lt_self (lt_min hρ hδ)).trans_le (min_le_left _ _)
  have hεδ : min ρ δ / 2 < δ := (half_lt_self (lt_min hρ hδ)).trans_le (min_le_right _ _)
  refine ⟨⟨hv₀, ?_, min ρ δ / 2, hε, 2 * K, by positivity, fun x u v hv r hr _ hu hx _ ↦ ?_⟩,
    hv₀, fun x v hx _ _ ↦ (hcont ū (mem_ball_self hδ)).tendsto.comp hx⟩
  · filter_upwards [ball_mem_nhds ū hδ] with x hx using (hcont x hx).lowerSemicontinuousAt
  · have hxρ : dist x ū < ρ := by rw [dist_eq_norm]; exact hx.trans_lt hερ
    have hxδ : x ∈ ball ū δ := by rw [mem_ball, dist_eq_norm]; exact hx.trans_lt hεδ
    have huδ : u ∈ ball ū δ := by rw [mem_ball, dist_eq_norm]; exact hu.trans_lt hεδ
    rw [hρsub hxρ, mem_singleton_iff] at hv
    have hrx : e x = r := by
      rw [hψ x hxδ] at hr
      exact_mod_cast hr
    rw [hψ u huδ, EReal.coe_le_coe_iff, hv, ← hrx]
    -- the descent lemma along the segment from `x` to `u`
    have hconv : Convex ℝ (closedBall x ‖u - x‖ ∩ ball ū δ) :=
      (convex_closedBall _ _).inter (convex_ball _ _)
    have hh : ∀ z ∈ closedBall x ‖u - x‖ ∩ ball ū δ,
        HasFDerivWithinAt (fun z ↦ e z - toDual ℝ E (f x) (z - x))
          (toDual ℝ E (f z) - toDual ℝ E (f x)) (closedBall x ‖u - x‖ ∩ ball ū δ) z :=
      fun z hz ↦ ((he z hz.2).sub
        (((toDual ℝ E (f x)).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const x)).congr_fderiv
          (ContinuousLinearMap.comp_id _))).hasFDerivWithinAt
    have hbound : ∀ z ∈ closedBall x ‖u - x‖ ∩ ball ū δ,
        ‖toDual ℝ E (f z) - toDual ℝ E (f x)‖ ≤ K * ‖u - x‖ := fun z hz ↦ by
      rw [← map_sub, LinearIsometryEquiv.norm_map, ← dist_eq_norm]
      exact (hL.dist_le_mul z hz.2 x hxδ).trans
        (mul_le_mul_of_nonneg_left (mem_closedBall.1 hz.1) K.coe_nonneg)
    have key := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hh hbound hconv
      (show x ∈ closedBall x ‖u - x‖ ∩ ball ū δ from
        ⟨mem_closedBall_self (norm_nonneg _), hxδ⟩)
      (show u ∈ closedBall x ‖u - x‖ ∩ ball ū δ from
        ⟨by rw [mem_closedBall, dist_eq_norm], huδ⟩)
    simp only [sub_self, map_zero, sub_zero, Real.norm_eq_abs] at key
    have h1 := (abs_le.1 key).1
    have h2 : 2 * (K : ℝ) / 2 * ‖u - x‖ ^ 2 = K * ‖u - x‖ * ‖u - x‖ := by ring
    linarith

/-- [Mordukhovich 2024, Cor. 1.101], part (a), the converse implication: let `φ` be l.s.c.,
prox-bounded and continuously prox-regular at `x̄` for `v̄ = ⟨g, ·⟩`. For all small `λ > 0`, if
`e_λφ` is twice epi-differentiable at `x̄ + λg` for `v̄`, then `φ` is twice epi-differentiable at
`x̄` for `v̄`. -/
theorem ContinuouslyProxRegularFor.exists_twiceEpiDifferentiableAt_of_moreauEnvelope {g : E}
    (hφ : ContinuouslyProxRegularFor φ x₀ (toDual ℝ E g))
    (hlsc : ∀ x, LowerSemicontinuousAt φ x)
    (hbd : ∃ a b : ℝ, ∀ x, ((a - b * ‖x - x₀‖ ^ 2 : ℝ) : EReal) ≤ φ x) :
    ∃ l₀ > (0 : ℝ), ∀ l, 0 < l → l < l₀ →
      TwiceEpiDifferentiableAt (moreauEnvelope φ l) (x₀ + l • g) (toDual ℝ E g) →
      TwiceEpiDifferentiableAt φ x₀ (toDual ℝ E g) := by
  obtain ⟨l₁, hl₁, H1⟩ := hφ.eventually_mem_subdiff_iff hlsc hbd
  obtain ⟨l₂, hl₂, H2⟩ := hφ.1.exists_moreauEnvelope hlsc hbd
  obtain ⟨l₃, hl₃, H3⟩ := hφ.exists_twiceEpiDifferentiableAt_iff_proximalMap hlsc hbd
  refine ⟨min (min l₁ l₂) l₃, lt_min (lt_min hl₁ hl₂) hl₃, fun l hl hll HT ↦ ?_⟩
  have hll₁ : l < l₁ := hll.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hll₂ : l < l₂ := hll.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hll₃ : l < l₃ := hll.trans_le (min_le_right _ _)
  obtain ⟨δ₁, hδ₁, p, hp0, hpU, -, -⟩ := H1 l hl hll₁
  obtain ⟨δ₂, hδ₂, p₂, hpU₂, hfin, hder, hLip⟩ := H2 l hl hll₂
  have hδ : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have hsub₁ : ball (x₀ + l • g) (min δ₁ δ₂) ⊆ ball (x₀ + l • g) δ₁ :=
    ball_subset_ball (min_le_left _ _)
  have hsub₂ : ball (x₀ + l • g) (min δ₁ δ₂) ⊆ ball (x₀ + l • g) δ₂ :=
    ball_subset_ball (min_le_right _ _)
  have hball := ball_mem_nhds (x₀ + l • g) hδ
  have hpp : ∀ u ∈ ball (x₀ + l • g) (min δ₁ δ₂), p₂ u = p u := fun u hu ↦
    Set.singleton_eq_singleton_iff.1 ((hpU₂ u (hsub₂ hu)).symm.trans (hpU u (hsub₁ hu)))
  obtain ⟨f, hf⟩ : ∃ f : E → E, f = fun u ↦ l⁻¹ • (u - p u) := ⟨_, rfl⟩
  have hfu : ∀ u, f u = l⁻¹ • (u - p u) := fun u ↦ by rw [hf]
  have hfū : f (x₀ + l • g) = g := by
    rw [hfu, hp0, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hl.ne', one_smul]
  have he : ∀ u ∈ ball (x₀ + l • g) (min δ₁ δ₂),
      HasFDerivAt (fun u ↦ (moreauEnvelope φ l u).toReal) (toDual ℝ E (f u)) u := fun u hu ↦ by
    have := hder u (hsub₂ hu)
    rw [hpp u hu] at this
    rw [hfu]
    exact this
  have hfL : LipschitzOnWith (Real.toNNReal (3 / l)) f (ball (x₀ + l • g) (min δ₁ δ₂)) := by
    refine LipschitzOnWith.of_dist_le_mul fun u₁ hu₁ u₂ hu₂ ↦ ?_
    have := hLip.dist_le_mul u₁ (hsub₂ hu₁) u₂ (hsub₂ hu₂)
    rw [hpp u₁ hu₁, hpp u₂ hu₂] at this
    rw [hfu, hfu]
    exact this
  -- the envelope is continuously prox-regular, so Thm. 1.98 applies to it
  obtain ⟨hcpr, hsub⟩ := continuouslyProxRegularFor_of_lipschitz_gradient hδ
    (fun u hu ↦ (hfin u (hsub₂ hu)).symm) he hfL
  rw [hfū] at hcpr
  have hproto := hcpr.twiceEpiDifferentiableAt_iff_protoDifferentiableAt.1 HT
  have hG1 : GeometricallyDerivableAt
      (graph fun u ↦ ({toDual ℝ E (f u)} : Set (StrongDual ℝ E)))
      (x₀ + l • g, toDual ℝ E g) := by
    refine GeometricallyDerivableAt.congr hproto (eventuallyEq_set.2 ?_)
      (show toDual ℝ E g ∈ ({toDual ℝ E (f (x₀ + l • g))} : Set (StrongDual ℝ E)) by
        rw [hfū]; exact mem_singleton _)
    filter_upwards [(continuous_fst.tendsto (x₀ + l • g, toDual ℝ E g)).eventually hsub]
      with q hq
    show q.2 ∈ subdiff (moreauEnvelope φ l) q.1 ↔
      q.2 ∈ ({toDual ℝ E (f q.1)} : Set (StrongDual ℝ E))
    rw [hq]
  -- the linear isomorphism `(u, x) ↦ (u, λ⁻¹(u - x))` between the graphs of `P_λφ` and `∇e_λφ`
  let Ψ : (E × E) ≃L[ℝ] (E × StrongDual ℝ E) := ContinuousLinearEquiv.equivOfInverse
    { toFun := fun q ↦ (q.1, toDual ℝ E (l⁻¹ • (q.1 - q.2)))
      map_add' := fun a b ↦ Prod.ext (by simp) (by simp [smul_sub, smul_add]; abel)
      map_smul' := fun c a ↦ Prod.ext (by simp) (by simp [smul_sub, smul_comm l⁻¹ c])
      cont := continuous_fst.prodMk ((toDual ℝ E).continuous.comp
        ((continuous_fst.sub continuous_snd).const_smul l⁻¹)) }
    { toFun := fun q ↦ (q.1, q.1 - l • (toDual ℝ E).symm q.2)
      map_add' := fun a b ↦ Prod.ext (by simp) (by simp [smul_add]; abel)
      map_smul' := fun c a ↦ Prod.ext (by simp) (by simp [smul_sub, smul_comm l c])
      cont := continuous_fst.prodMk (continuous_fst.sub
        (((toDual ℝ E).symm.continuous.comp continuous_snd).const_smul l)) }
    (fun q ↦ Prod.ext rfl (by
      show q.1 - l • (toDual ℝ E).symm (toDual ℝ E (l⁻¹ • (q.1 - q.2))) = q.2
      rw [LinearIsometryEquiv.symm_apply_apply, smul_smul, mul_inv_cancel₀ hl.ne', one_smul,
        sub_sub_cancel]))
    (fun q ↦ Prod.ext rfl (by
      show toDual ℝ E (l⁻¹ • (q.1 - (q.1 - l • (toDual ℝ E).symm q.2))) = q.2
      rw [sub_sub_cancel, smul_smul, inv_mul_cancel₀ hl.ne', one_smul,
        LinearIsometryEquiv.apply_symm_apply]))
  have hΨ : ∀ q : E × E, Ψ q = (q.1, toDual ℝ E (l⁻¹ • (q.1 - q.2))) := fun q ↦ rfl
  have hΨ0 : Ψ (x₀ + l • g, x₀) = (x₀ + l • g, toDual ℝ E g) := by
    rw [hΨ]
    simp only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hl.ne', one_smul]
  have hG2 : GeometricallyDerivableAt (graph fun u ↦ ({p u} : Set E)) (x₀ + l • g, x₀) := by
    refine GeometricallyDerivableAt.of_inter_eq_preimage (Φ := Ψ) (e := Ψ)
      (by rw [hΨ0]; exact hG1) univ_mem ?_ Ψ.hasStrictFDerivAt
      (show x₀ ∈ ({p (x₀ + l • g)} : Set E) by rw [hp0]; exact mem_singleton _)
    ext q
    simp only [inter_univ]
    show q.2 ∈ ({p q.1} : Set E) ↔
      toDual ℝ E (l⁻¹ • (q.1 - q.2)) ∈ ({toDual ℝ E (f q.1)} : Set (StrongDual ℝ E))
    rw [mem_singleton_iff, mem_singleton_iff, (toDual ℝ E).injective.eq_iff, hfu]
    exact ⟨fun h ↦ by rw [h], fun h ↦
      sub_right_injective (smul_right_injective E (inv_ne_zero hl.ne') h)⟩
  -- back to the proximal mapping and to `φ`
  have hEq : graph (fun u ↦ ({p u} : Set E)) =ᶠ[𝓝 (x₀ + l • g, x₀)]
      graph (proximalMap φ l) := by
    refine eventuallyEq_set.2 ?_
    filter_upwards [(continuous_fst.tendsto (x₀ + l • g, x₀)).eventually
      (ball_mem_nhds (x₀ + l • g) hδ₁)] with q hq
    show q.2 ∈ ({p q.1} : Set E) ↔ q.2 ∈ proximalMap φ l q.1
    rw [hpU _ hq]
  have hmemP : x₀ ∈ proximalMap φ l (x₀ + l • g) := by
    rw [hpU _ (mem_ball_self hδ₁), hp0]; exact mem_singleton _
  exact (H3 l hl hll₃).1.2 (GeometricallyDerivableAt.congr hG2 hEq hmemP)

/-- **Twice epi-differentiability of Moreau envelopes** [Mordukhovich 2024, Cor. 1.101], part
(a): let `φ` be l.s.c., prox-bounded and continuously prox-regular at `x̄` for `v̄ = ⟨g, ·⟩`.
Then for all small `λ > 0`, `φ` is twice epi-differentiable at `x̄` for `v̄` iff `e_λφ` is twice
epi-differentiable at `x̄ + λg` for `v̄`. -/
theorem ContinuouslyProxRegularFor.exists_twiceEpiDifferentiableAt_iff_moreauEnvelope {g : E}
    (hφ : ContinuouslyProxRegularFor φ x₀ (toDual ℝ E g))
    (hlsc : ∀ x, LowerSemicontinuousAt φ x)
    (hbd : ∃ a b : ℝ, ∀ x, ((a - b * ‖x - x₀‖ ^ 2 : ℝ) : EReal) ≤ φ x) :
    ∃ l₀ > (0 : ℝ), ∀ l, 0 < l → l < l₀ →
      (TwiceEpiDifferentiableAt φ x₀ (toDual ℝ E g) ↔
        TwiceEpiDifferentiableAt (moreauEnvelope φ l) (x₀ + l • g) (toDual ℝ E g)) := by
  obtain ⟨l₁, hl₁, H1⟩ := hφ.exists_twiceEpiDifferentiableAt_of_moreauEnvelope hlsc hbd
  by_cases H : TwiceEpiDifferentiableAt φ x₀ (toDual ℝ E g)
  · obtain ⟨l₂, hl₂, H2⟩ := hφ.1.exists_twiceEpiDifferentiableAt_moreauEnvelope H hlsc hbd
    exact ⟨min l₁ l₂, lt_min hl₁ hl₂, fun l hl hll ↦
      ⟨fun _ ↦ (H2 l hl (hll.trans_le (min_le_right _ _))).1,
        H1 l hl (hll.trans_le (min_le_left _ _))⟩⟩
  · exact ⟨l₁, hl₁, fun l hl hll ↦ ⟨fun h ↦ absurd h H, H1 l hl hll⟩⟩

end Prox

end VariationalAnalysis
