/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import VariationalAnalysis.SecondOrder.EpiConvergence
import VariationalAnalysis.SecondOrder.Moreau
import VariationalAnalysis.Subdifferential.SmoothChain

/-!
# Second subderivatives

This file follows [Mordukhovich 2024, Sect. 1.5.1 and Lemma 1.94] (body numbering): the
subderivative (Def. 1.43), second-order difference quotients, second subderivatives and twice
epi-differentiability, together with their basic properties.

## Main declarations

* `subderiv φ x₀`: the subderivative `dφ(x̄)` [Mordukhovich 2024, Def. 1.43, (1.57)].
* `secondDiffQuot φ x₀ v t`, `secondDiffQuot' φ x₀ t`: the second-order difference quotients
  (1.120) and (1.119).
* `secondSubderiv φ x₀ v`, `secondSubderiv' φ x₀`: the second subderivatives `d²φ(x̄, v)` and
  `d²φ(x̄)` [Mordukhovich 2024, Def. 1.88].
* `TwiceEpiDifferentiableAt`, `TwiceSemidifferentiableAt`: [Mordukhovich 2024, Def. 1.89].
* `criticalCone φ x₀ v`: the critical cone (1.125).
* `IsSemiderivative`, `SemidifferentiableAt'`: semiderivatives of set-valued mappings
  [Mordukhovich 2024, Def. 1.100].

## Main results

* `subderiv_of_hasFDerivAt`: `dφ(x̄)(w) = ⟨∇φ(x̄), w⟩` for differentiable `φ`.
* `abs_taylor_two_le`: the second-order Taylor expansion of a twice differentiable function.
* `secondSubderiv_of_hasFDerivAt`, `secondSubderiv'_of_hasFDerivAt`,
  `twiceEpiDifferentiableAt_of_hasFDerivAt`, `tendsto_secondDiffQuot_dir_of_hasFDerivAt`:
  [Mordukhovich 2024, Prop. 1.90].
* `secondSubderiv_nonneg_of_convex`, `convex_epi_secondSubderiv`:
  [Mordukhovich 2024, Prop. 1.93].
* `subdiff_half_secondDiffQuot`: [Mordukhovich 2024, Lemma 1.94, (1.130)], via
  `mem_subdiff_coe_mul_iff` (`∂(cθ) = c∂θ` for `c > 0`).
* `moreauEnvelope_scale`, `proximalMap_scale`, `moreauEnvelope_half_secondDiffQuot`,
  `proximalMap_half_secondDiffQuot`: [Mordukhovich 2024, Lemma 1.94, (1.131)].
-/

open Filter Topology Set Metric
open scoped NNReal Pointwise

namespace VariationalAnalysis

section Defs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The subderivative `dφ(x̄)(w) = liminf_{t ↓ 0, u → w} Δ_tφ(x̄)(u)`
[Mordukhovich 2024, Def. 1.43, (1.57)]. -/
noncomputable def subderiv (φ : E → EReal) (x₀ w : E) : EReal :=
  liminf (fun p : ℝ × E ↦ diffQuot φ x₀ p.1 p.2) (𝓝[>] 0 ×ˢ 𝓝 w)

/-- The second-order difference quotient
`Δ²_tφ(x̄, v)(w) = (φ(x̄ + tw) - φ(x̄) - t⟨v, w⟩) / (t²/2)` [Mordukhovich 2024, (1.120)]. -/
noncomputable def secondDiffQuot (φ : E → EReal) (x₀ : E) (v : StrongDual ℝ E) (t : ℝ) (w : E) :
    EReal :=
  ((2 / t ^ 2 : ℝ) : EReal) * (φ (x₀ + t • w) - φ x₀ - ((t * v w : ℝ) : EReal))

open Classical in
/-- The second-order difference quotient
`Δ²_tφ(x̄)(w) = (φ(x̄ + tw) - φ(x̄) - t dφ(x̄)(w)) / (t²/2)`, with the value `∞` when
`φ(x̄ + tw) = dφ(x̄)(w) = ±∞` [Mordukhovich 2024, (1.119)]. -/
noncomputable def secondDiffQuot' (φ : E → EReal) (x₀ : E) (t : ℝ) (w : E) : EReal :=
  if (φ (x₀ + t • w) = ⊤ ∧ subderiv φ x₀ w = ⊤) ∨ (φ (x₀ + t • w) = ⊥ ∧ subderiv φ x₀ w = ⊥)
  then ⊤
  else ((2 / t ^ 2 : ℝ) : EReal) * (φ (x₀ + t • w) - φ x₀ - (t : EReal) * subderiv φ x₀ w)

/-- The second subderivative `d²φ(x̄, v)(w) = liminf_{t ↓ 0, u → w} Δ²_tφ(x̄, v)(u)`
[Mordukhovich 2024, Def. 1.88, (1.121)]. -/
noncomputable def secondSubderiv (φ : E → EReal) (x₀ : E) (v : StrongDual ℝ E) (w : E) : EReal :=
  liminf (fun p : ℝ × E ↦ secondDiffQuot φ x₀ v p.1 p.2) (𝓝[>] 0 ×ˢ 𝓝 w)

/-- The `v`-independent second subderivative `d²φ(x̄)(w) = liminf_{t ↓ 0, u → w} Δ²_tφ(x̄)(u)`
[Mordukhovich 2024, Def. 1.88, (1.122)]. -/
noncomputable def secondSubderiv' (φ : E → EReal) (x₀ w : E) : EReal :=
  liminf (fun p : ℝ × E ↦ secondDiffQuot' φ x₀ p.1 p.2) (𝓝[>] 0 ×ˢ 𝓝 w)

/-- The critical cone `K_φ(x̄, v) = {w | dφ(x̄)(w) = ⟨v, w⟩}` [Mordukhovich 2024, (1.125)]. -/
def criticalCone (φ : E → EReal) (x₀ : E) (v : StrongDual ℝ E) : Set E :=
  {w | subderiv φ x₀ w = (v w : EReal)}

/-- `φ` is twice epi-differentiable at `x̄` for `v` [Mordukhovich 2024, Def. 1.89(i)]: `φ(x̄)` is
finite and, for every `t_k ↓ 0` and `w`, `d²φ(x̄, v)(w) ≤ liminf Δ²_{t_k}φ(x̄, v)(w_k)` for every
`w_k → w` and `d²φ(x̄, v)(w) ≥ limsup Δ²_{t_k}φ(x̄, v)(w_k)` for some `w_k → w`. -/
def TwiceEpiDifferentiableAt (φ : E → EReal) (x₀ : E) (v : StrongDual ℝ E) : Prop :=
  (∃ r : ℝ, φ x₀ = r) ∧ ∀ t : ℕ → ℝ, Tendsto t atTop (𝓝[>] 0) → ∀ w,
    (∀ wk : ℕ → E, Tendsto wk atTop (𝓝 w) →
      secondSubderiv φ x₀ v w ≤ liminf (fun k ↦ secondDiffQuot φ x₀ v (t k) (wk k)) atTop) ∧
    ∃ wk : ℕ → E, Tendsto wk atTop (𝓝 w) ∧
      limsup (fun k ↦ secondDiffQuot φ x₀ v (t k) (wk k)) atTop ≤ secondSubderiv φ x₀ v w

/-- `φ : E → ℝ` is twice semidifferentiable at `x̄` [Mordukhovich 2024, Def. 1.89(ii)]: the
difference quotients converge to a finite limit `dφ(x̄)(w)` as `t ↓ 0`, `u → w`, and
`φ(x) = φ(x̄) + dφ(x̄)(x - x̄) + ψ(x - x̄)/2 + o(‖x - x̄‖²)` for a continuous `ψ` positively
homogeneous of degree `2`. (A twice semidifferentiable function has a finite subderivative, so
we ask for a finite limit.) -/
def TwiceSemidifferentiableAt (φ : E → ℝ) (x₀ : E) : Prop :=
  ∃ d : E → ℝ, (∀ w, Tendsto (fun p : ℝ × E ↦ diffQuot (fun x ↦ (φ x : EReal)) x₀ p.1 p.2)
      (𝓝[>] 0 ×ˢ 𝓝 w) (𝓝 (d w))) ∧
    ∃ ψ : E → ℝ, Continuous ψ ∧ (∀ s : ℝ, 0 < s → ∀ x, ψ (s • x) = s ^ 2 * ψ x) ∧
      (fun x ↦ φ x - φ x₀ - d (x - x₀) - ψ (x - x₀) / 2) =o[𝓝 x₀] fun x ↦ ‖x - x₀‖ ^ 2

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `D` is the semiderivative of `F` at `x̄` for `ȳ` and `w̄`: the sets `(F(x̄ + tw) - ȳ)/t`
converge to `D` as `t ↓ 0`, `w → w̄` [Mordukhovich 2024, Def. 1.100, (1.138)]. -/
def IsSemiderivative (S : E → Set F) (x₀ : E) (y₀ : F) (w₀ : E) (D : Set F) : Prop :=
  IsSetLimit (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w₀)
    (fun p : ℝ × E ↦ (fun y ↦ (p.1)⁻¹ • (y - y₀)) '' S (x₀ + p.1 • p.2)) D

/-- `S` is semidifferentiable at `x̄` for `ȳ` if the semiderivative exists in every direction
[Mordukhovich 2024, Def. 1.100]. -/
def SemidifferentiableAt' (S : E → Set F) (x₀ : E) (y₀ : F) : Prop :=
  ∀ w₀, ∃ D, IsSemiderivative S x₀ y₀ w₀ D

end Defs

/-! ### Real-valued functions -/

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem diffQuot_coe (φ : E → ℝ) (x₀ : E) (t : ℝ) (w : E) :
    diffQuot (fun x ↦ (φ x : EReal)) x₀ t w = ((t⁻¹ * (φ (x₀ + t • w) - φ x₀) : ℝ) : EReal) := by
  simp only [diffQuot]
  rw [← EReal.coe_sub, ← EReal.coe_mul]

theorem secondDiffQuot_coe (φ : E → ℝ) (x₀ : E) (v : StrongDual ℝ E) (t : ℝ) (w : E) :
    secondDiffQuot (fun x ↦ (φ x : EReal)) x₀ v t w =
      ((2 / t ^ 2 * (φ (x₀ + t • w) - φ x₀ - t * v w) : ℝ) : EReal) := by
  simp only [secondDiffQuot]
  rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_mul]

theorem tendsto_smul_nhdsGT_prod (w : E) :
    Tendsto (fun p : ℝ × E ↦ p.1 • p.2) (𝓝[>] 0 ×ˢ 𝓝 w) (𝓝 0) := by
  have h : Tendsto (fun p : ℝ × E ↦ p.1 • p.2) (𝓝 ((0 : ℝ), w)) (𝓝 ((0 : ℝ) • w)) :=
    (continuous_fst.smul continuous_snd).tendsto _
  rw [zero_smul, nhds_prod_eq] at h
  exact h.mono_left (prod_mono nhdsWithin_le_nhds le_rfl)

omit [NormedSpace ℝ E] in
theorem eventually_pos_nhdsGT_prod (w : E) : ∀ᶠ p : ℝ × E in 𝓝[>] 0 ×ˢ 𝓝 w, 0 < p.1 :=
  (eventually_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0)).prod_inl _

/-- The subderivative of a function differentiable at `x̄` is its derivative. -/
theorem tendsto_diffQuot_of_hasFDerivAt {φ : E → ℝ} {φ' : StrongDual ℝ E} {x₀ : E}
    (hφ : HasFDerivAt φ φ' x₀) (w : E) :
    Tendsto (fun p : ℝ × E ↦ diffQuot (fun x ↦ (φ x : EReal)) x₀ p.1 p.2) (𝓝[>] 0 ×ˢ 𝓝 w)
      (𝓝 (φ' w : EReal)) := by
  simp only [diffQuot_coe]
  refine (continuous_coe_real_ereal.tendsto _).comp ?_
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η, hη⟩ : ∃ η, η = ε / (2 * (‖w‖ + 1)) := ⟨_, rfl⟩
  have hηpos : 0 < η := by rw [hη]; positivity
  have hlo := (tendsto_smul_nhdsGT_prod w).eventually
    ((hasFDerivAt_iff_isLittleO_nhds_zero.1 hφ).def hηpos)
  have hlin : Tendsto (fun p : ℝ × E ↦ φ' p.2) (𝓝[>] 0 ×ˢ 𝓝 w) (𝓝 (φ' w)) :=
    ((φ'.continuous.tendsto w).comp tendsto_snd)
  have hnorm : ∀ᶠ p : ℝ × E in 𝓝[>] 0 ×ˢ 𝓝 w, ‖p.2‖ < ‖w‖ + 1 :=
    tendsto_snd.eventually ((continuous_norm.tendsto w).eventually (gt_mem_nhds (by linarith)))
  filter_upwards [hlo, Metric.tendsto_nhds.1 hlin (ε / 2) (half_pos hε),
    eventually_pos_nhdsGT_prod w, hnorm] with p h1 h2 ht hn
  obtain ⟨t, u⟩ := p
  simp only at h1 h2 ht hn
  rw [Real.dist_eq] at h2 ⊢
  simp only [map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at h1
  have e : t⁻¹ * (φ (x₀ + t • u) - φ x₀) - φ' w =
      t⁻¹ * (φ (x₀ + t • u) - φ x₀ - t * φ' u) + (φ' u - φ' w) := by
    field_simp; ring
  rw [e]
  have h3 : |t⁻¹ * (φ (x₀ + t • u) - φ x₀ - t * φ' u)| ≤ η * ‖u‖ := by
    rw [abs_mul, abs_of_pos (inv_pos.2 ht)]
    calc t⁻¹ * |φ (x₀ + t • u) - φ x₀ - t * φ' u| ≤ t⁻¹ * (η * (t * ‖u‖)) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 ht.le)
      _ = η * ‖u‖ := by field_simp
  have h4 : η * ‖u‖ ≤ ε / 2 := by
    calc η * ‖u‖ ≤ η * (‖w‖ + 1) := mul_le_mul_of_nonneg_left hn.le hηpos.le
      _ = ε / 2 := by rw [hη]; field_simp
  calc |t⁻¹ * (φ (x₀ + t • u) - φ x₀ - t * φ' u) + (φ' u - φ' w)|
      ≤ |t⁻¹ * (φ (x₀ + t • u) - φ x₀ - t * φ' u)| + |φ' u - φ' w| := abs_add_le _ _
    _ < ε := by linarith

/-- `dφ(x̄)(w) = ⟨∇φ(x̄), w⟩` for a function differentiable at `x̄`
[Mordukhovich 2024, p. 34]. -/
theorem subderiv_of_hasFDerivAt {φ : E → ℝ} {φ' : StrongDual ℝ E} {x₀ : E}
    (hφ : HasFDerivAt φ φ' x₀) (w : E) :
    subderiv (fun x ↦ (φ x : EReal)) x₀ w = φ' w :=
  (tendsto_diffQuot_of_hasFDerivAt hφ w).liminf_eq

/-- If `dφ(x̄)(w) = ⟨v, w⟩` for all `w`, the two second-order difference quotients agree. -/
theorem secondDiffQuot'_eq {φ : E → EReal} {x₀ : E} {v : StrongDual ℝ E}
    (h : ∀ w, subderiv φ x₀ w = (v w : EReal)) (t : ℝ) (w : E) :
    secondDiffQuot' φ x₀ t w = secondDiffQuot φ x₀ v t w := by
  rw [secondDiffQuot', h w, if_neg (by simp), ← EReal.coe_mul, secondDiffQuot]

end Real

/-! ### Twice differentiable functions -/

section Twice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {φ : E → ℝ} {φ' : E → StrongDual ℝ E} {φ'' : E →L[ℝ] StrongDual ℝ E} {x₀ : E}

/-- The second-order Taylor expansion
`φ(x̄ + h) = φ(x̄) + ⟨∇φ(x̄), h⟩ + ⟨∇²φ(x̄)h, h⟩/2 + o(‖h‖²)` of a function twice differentiable
at `x̄`. -/
theorem abs_taylor_two_le (hφ : ∀ᶠ x in 𝓝 x₀, HasFDerivAt φ (φ' x) x)
    (hφ' : HasFDerivAt φ' φ'' x₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in 𝓝 (0 : E), |φ (x₀ + h) - φ x₀ - φ' x₀ h - φ'' h h / 2| ≤ ε * ‖h‖ ^ 2 := by
  have hsymm : ∀ v w, φ'' v w = φ'' w v := second_derivative_symmetric_of_eventually hφ hφ'
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 (hφ.and (hφ'.isLittleO.def hε))
  rw [Metric.eventually_nhds_iff]
  refine ⟨ρ, hρ, fun h hh ↦ ?_⟩
  rw [dist_zero_right] at hh
  let g : E → ℝ := fun y ↦ φ (x₀ + y) - φ x₀ - φ' x₀ y - (1 / 2) * φ'' y y
  have hmem : ∀ y ∈ closedBall (0 : E) ‖h‖, dist (x₀ + y) x₀ < ρ := by
    intro y hy
    rw [mem_closedBall, dist_zero_right] at hy
    rw [dist_eq_norm, add_sub_cancel_left]; linarith
  have hderiv : ∀ y ∈ closedBall (0 : E) ‖h‖,
      HasFDerivWithinAt g (φ' (x₀ + y) - φ' x₀ - φ'' y) (closedBall (0 : E) ‖h‖) y := by
    intro y hy
    have h1 := ((hball (hmem y hy)).1).comp y ((hasFDerivAt_id y).const_add x₀)
    have h3 : HasFDerivAt (fun y ↦ φ'' y y)
        ((φ'' y).comp (ContinuousLinearMap.id ℝ E) + φ''.flip y) y :=
      φ''.hasFDerivAt.clm_apply (hasFDerivAt_id y)
    refine ((((h1.sub_const (φ x₀)).sub (φ' x₀).hasFDerivAt).sub
      (h3.const_mul (1 / 2))).congr_fderiv ?_).hasFDerivWithinAt
    ext d
    simp [hsymm d y]
    ring
  have hbound : ∀ y ∈ closedBall (0 : E) ‖h‖, ‖φ' (x₀ + y) - φ' x₀ - φ'' y‖ ≤ ε * ‖h‖ := by
    intro y hy
    have := (hball (hmem y hy)).2
    rw [add_sub_cancel_left] at this
    rw [mem_closedBall, dist_zero_right] at hy
    exact this.trans (mul_le_mul_of_nonneg_left hy hε.le)
  have hmv := (convex_closedBall (0 : E) ‖h‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hderiv hbound (mem_closedBall_self (norm_nonneg h))
    (mem_closedBall.2 (by rw [dist_zero_right]))
  simp only [g, add_zero, map_zero, sub_self, mul_zero, sub_zero, Real.norm_eq_abs] at hmv
  calc |φ (x₀ + h) - φ x₀ - φ' x₀ h - φ'' h h / 2|
      = |φ (x₀ + h) - φ x₀ - φ' x₀ h - 1 / 2 * φ'' h h| := by ring_nf
    _ ≤ ε * ‖h‖ * ‖h‖ := hmv
    _ = ε * ‖h‖ ^ 2 := by ring

/-- The second-order difference quotients of a twice differentiable function converge to the
Hessian quadratic form. -/
theorem tendsto_secondDiffQuot_of_hasFDerivAt (hφ : ∀ᶠ x in 𝓝 x₀, HasFDerivAt φ (φ' x) x)
    (hφ' : HasFDerivAt φ' φ'' x₀) (w : E) :
    Tendsto (fun p : ℝ × E ↦ secondDiffQuot (fun x ↦ (φ x : EReal)) x₀ (φ' x₀) p.1 p.2)
      (𝓝[>] 0 ×ˢ 𝓝 w) (𝓝 (φ'' w w : EReal)) := by
  simp only [secondDiffQuot_coe]
  refine (continuous_coe_real_ereal.tendsto _).comp ?_
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η, hη⟩ : ∃ η, η = ε / (4 * (‖w‖ + 1) ^ 2) := ⟨_, rfl⟩
  have hηpos : 0 < η := by rw [hη]; positivity
  have hT := (tendsto_smul_nhdsGT_prod w).eventually (abs_taylor_two_le hφ hφ' hηpos)
  have hq : Tendsto (fun p : ℝ × E ↦ φ'' p.2 p.2) (𝓝[>] 0 ×ˢ 𝓝 w) (𝓝 (φ'' w w)) := by
    have : Continuous fun u : E ↦ φ'' u u := by fun_prop
    exact (this.tendsto w).comp tendsto_snd
  have hnorm : ∀ᶠ p : ℝ × E in 𝓝[>] 0 ×ˢ 𝓝 w, ‖p.2‖ < ‖w‖ + 1 :=
    tendsto_snd.eventually ((continuous_norm.tendsto w).eventually (gt_mem_nhds (by linarith)))
  filter_upwards [hT, Metric.tendsto_nhds.1 hq (ε / 2) (half_pos hε),
    eventually_pos_nhdsGT_prod w, hnorm] with p h1 h2 ht hn
  obtain ⟨t, u⟩ := p
  simp only at h1 h2 ht hn
  rw [Real.dist_eq] at h2 ⊢
  simp only [map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at h1
  rw [show (t • φ'' u) u = t * φ'' u u by simp] at h1
  dsimp only
  have e : 2 / t ^ 2 * (φ (x₀ + t • u) - φ x₀ - t * φ' x₀ u) - φ'' w w =
      2 / t ^ 2 * (φ (x₀ + t • u) - φ x₀ - t * φ' x₀ u - t * (t * φ'' u u) / 2) +
        (φ'' u u - φ'' w w) := by
    field_simp; ring
  rw [e]
  have h3 : |2 / t ^ 2 * (φ (x₀ + t • u) - φ x₀ - t * φ' x₀ u - t * (t * φ'' u u) / 2)| ≤
      2 * η * ‖u‖ ^ 2 := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / t ^ 2)]
    calc 2 / t ^ 2 * |φ (x₀ + t • u) - φ x₀ - t * φ' x₀ u - t * (t * φ'' u u) / 2|
        ≤ 2 / t ^ 2 * (η * (t * ‖u‖) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 * η * ‖u‖ ^ 2 := by field_simp
  have h4 : 2 * η * ‖u‖ ^ 2 ≤ ε / 2 := by
    have : ‖u‖ ^ 2 ≤ (‖w‖ + 1) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn.le 2
    calc 2 * η * ‖u‖ ^ 2 ≤ 2 * η * (‖w‖ + 1) ^ 2 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = ε / 2 := by rw [hη]; field_simp; ring
  calc |2 / t ^ 2 * (φ (x₀ + t • u) - φ x₀ - t * φ' x₀ u - t * (t * φ'' u u) / 2) +
        (φ'' u u - φ'' w w)|
      ≤ |2 / t ^ 2 * (φ (x₀ + t • u) - φ x₀ - t * φ' x₀ u - t * (t * φ'' u u) / 2)| +
        |φ'' u u - φ'' w w| := abs_add_le _ _
    _ < ε := by linarith

/-- [Mordukhovich 2024, Prop. 1.90]: `d²φ(x̄, ∇φ(x̄))(w) = ⟨∇²φ(x̄)w, w⟩`. -/
theorem secondSubderiv_of_hasFDerivAt (hφ : ∀ᶠ x in 𝓝 x₀, HasFDerivAt φ (φ' x) x)
    (hφ' : HasFDerivAt φ' φ'' x₀) (w : E) :
    secondSubderiv (fun x ↦ (φ x : EReal)) x₀ (φ' x₀) w = φ'' w w :=
  (tendsto_secondDiffQuot_of_hasFDerivAt hφ hφ' w).liminf_eq

/-- [Mordukhovich 2024, Prop. 1.90]: `d²φ(x̄)(w) = ⟨∇²φ(x̄)w, w⟩`. -/
theorem secondSubderiv'_of_hasFDerivAt (hφ : ∀ᶠ x in 𝓝 x₀, HasFDerivAt φ (φ' x) x)
    (hφ' : HasFDerivAt φ' φ'' x₀) (w : E) :
    secondSubderiv' (fun x ↦ (φ x : EReal)) x₀ w = φ'' w w := by
  have h := secondDiffQuot'_eq (subderiv_of_hasFDerivAt hφ.self_of_nhds)
  simp only [secondSubderiv', h]
  exact secondSubderiv_of_hasFDerivAt hφ hφ' w

/-- [Mordukhovich 2024, Prop. 1.90]: a twice differentiable function is twice epi-differentiable
at `x̄` for `∇φ(x̄)`. -/
theorem twiceEpiDifferentiableAt_of_hasFDerivAt (hφ : ∀ᶠ x in 𝓝 x₀, HasFDerivAt φ (φ' x) x)
    (hφ' : HasFDerivAt φ' φ'' x₀) :
    TwiceEpiDifferentiableAt (fun x ↦ (φ x : EReal)) x₀ (φ' x₀) := by
  refine ⟨⟨φ x₀, rfl⟩, fun t ht w ↦ ⟨fun wk hwk ↦ ?_, ⟨fun _ ↦ w, tendsto_const_nhds, ?_⟩⟩⟩
  · rw [secondSubderiv_of_hasFDerivAt hφ hφ' w]
    have hc := (tendsto_secondDiffQuot_of_hasFDerivAt hφ hφ' w).comp (ht.prodMk hwk)
    simp only [Function.comp_def] at hc
    exact hc.liminf_eq.ge
  · rw [secondSubderiv_of_hasFDerivAt hφ hφ' w]
    have hc := (tendsto_secondDiffQuot_of_hasFDerivAt hφ hφ' w).comp
      (ht.prodMk (tendsto_const_nhds (x := w)))
    simp only [Function.comp_def] at hc
    exact hc.limsup_eq.le

/-- [Mordukhovich 2024, Prop. 1.90, (1.124)]: the one-sided second directional derivative of a
twice differentiable function is `φ''(x̄; w) = ⟨∇²φ(x̄)w, w⟩`. -/
theorem tendsto_secondDiffQuot_dir_of_hasFDerivAt (hφ : ∀ᶠ x in 𝓝 x₀, HasFDerivAt φ (φ' x) x)
    (hφ' : HasFDerivAt φ' φ'' x₀) (w : E) :
    Tendsto (fun t ↦ secondDiffQuot (fun x ↦ (φ x : EReal)) x₀ (φ' x₀) t w) (𝓝[>] 0)
      (𝓝 (φ'' w w : EReal)) := by
  have h : Tendsto (fun t : ℝ ↦ (t, w)) (𝓝[>] 0) (𝓝[>] 0 ×ˢ 𝓝 w) :=
    tendsto_id.prodMk tendsto_const_nhds
  have h2 := (tendsto_secondDiffQuot_of_hasFDerivAt hφ hφ' w).comp h
  simp only [Function.comp_def] at h2
  exact h2

end Twice

/-! ### Convex functions -/

section Convex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {φ : E → EReal} {x₀ : E} {v : StrongDual ℝ E} {r : ℝ}

theorem secondDiffQuot_nonneg (hr : φ x₀ = r) {t : ℝ} {w : E}
    (h : ((r + v (t • w) : ℝ) : EReal) ≤ φ (x₀ + t • w)) :
    0 ≤ secondDiffQuot φ x₀ v t w := by
  rw [secondDiffQuot, hr]
  refine le_trans (le_of_eq (mul_zero _).symm)
    (PosMulMono.mul_le_mul_of_nonneg_left (EReal.coe_nonneg.2 (by positivity)) ?_)
  by_cases htop : φ (x₀ + t • w) = ⊤
  · rw [htop, EReal.top_sub_coe, EReal.top_sub_coe]; exact le_top
  have hbot : φ (x₀ + t • w) ≠ ⊥ := fun hb ↦ by
    rw [hb] at h; exact absurd h (not_le.2 (EReal.bot_lt_coe _))
  rw [← EReal.coe_toReal htop hbot] at h ⊢
  rw [EReal.coe_le_coe_iff, map_smul, smul_eq_mul] at h
  rw [← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_nonneg]
  linarith

/-- [Mordukhovich 2024, Prop. 1.93, (1.129)]: for a convex function and `v ∈ ∂φ(x̄)`,
`d²φ(x̄, v)(w) ≥ 0`. -/
theorem secondSubderiv_nonneg_of_convex (hconv : Convex ℝ (φ.Epi univ)) (hr : φ x₀ = r)
    (hv : v ∈ subdiff φ x₀) (w : E) : 0 ≤ secondSubderiv φ x₀ v w := by
  rw [mem_subdiff_of_convex hconv hr] at hv
  refine le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall fun p ↦ ?_)
  exact secondDiffQuot_nonneg hr (by simpa using hv (x₀ + p.1 • p.2))

theorem secondDiffQuot_le_coe_iff (hr : φ x₀ = r) {t : ℝ} (ht : 0 < t) {u : E} {β : ℝ} :
    secondDiffQuot φ x₀ v t u ≤ β ↔
      φ (x₀ + t • u) ≤ ((r + t * v u + t ^ 2 / 2 * β : ℝ) : EReal) := by
  have hc : (0 : ℝ) < 2 / t ^ 2 := by positivity
  rw [secondDiffQuot, hr]
  by_cases htop : φ (x₀ + t • u) = ⊤
  · rw [htop, EReal.top_sub_coe, EReal.top_sub_coe, EReal.coe_mul_top_of_pos hc]
    exact iff_of_false (fun h ↦ EReal.coe_ne_top _ (top_le_iff.1 h))
      (fun h ↦ EReal.coe_ne_top _ (top_le_iff.1 h))
  by_cases hbot : φ (x₀ + t • u) = ⊥
  · rw [hbot, EReal.bot_sub, EReal.bot_sub, EReal.coe_mul_bot_of_pos hc]
    simp
  rw [← EReal.coe_toReal htop hbot, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_mul,
    EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
  set s := (φ (x₀ + t • u)).toReal
  constructor
  · intro h
    have h' := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ t ^ 2 / 2)
    have e : t ^ 2 / 2 * (2 / t ^ 2 * (s - r - t * v u)) = s - r - t * v u := by field_simp
    linarith
  · intro h
    have h' : s - r - t * v u ≤ t ^ 2 / 2 * β := by linarith
    have := mul_le_mul_of_nonneg_left h' hc.le
    have e : 2 / t ^ 2 * (t ^ 2 / 2 * β) = β := by field_simp
    linarith

/-- Second-order difference quotients of a convex function are convex. -/
theorem secondDiffQuot_combo_le (hconv : Convex ℝ (φ.Epi univ)) (hr : φ x₀ = r) {t : ℝ}
    (ht : 0 < t) {u₁ u₂ : E} {β₁ β₂ a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (h₁ : secondDiffQuot φ x₀ v t u₁ ≤ β₁) (h₂ : secondDiffQuot φ x₀ v t u₂ ≤ β₂) :
    secondDiffQuot φ x₀ v t (a • u₁ + b • u₂) ≤ ((a * β₁ + b * β₂ : ℝ) : EReal) := by
  rw [secondDiffQuot_le_coe_iff hr ht] at h₁ h₂ ⊢
  obtain ⟨-, h⟩ := hconv (x := (x₀ + t • u₁, r + t * v u₁ + t ^ 2 / 2 * β₁))
    (y := (x₀ + t • u₂, r + t * v u₂ + t ^ 2 / 2 * β₂)) ⟨mem_univ _, h₁⟩ ⟨mem_univ _, h₂⟩
    ha hb hab
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at h
  obtain rfl : b = 1 - a := by linarith
  convert h using 2
  · module
  · simp only [map_add, map_smul, smul_eq_mul]
    ring

/-- [Mordukhovich 2024, Prop. 1.93], second part: if a convex function is twice
epi-differentiable at `x̄` for `v`, then `d²φ(x̄, v)` is convex. (Only the convexity of `φ` and the
finiteness of `φ(x̄)` are used.) -/
theorem convex_epi_secondSubderiv (hconv : Convex ℝ (φ.Epi univ))
    (h : TwiceEpiDifferentiableAt φ x₀ v) : Convex ℝ ((secondSubderiv φ x₀ v).Epi univ) := by
  obtain ⟨⟨r, hr⟩, h⟩ := h
  rintro ⟨w₁, α₁⟩ ⟨-, hw₁⟩ ⟨w₂, α₂⟩ ⟨-, hw₂⟩ a b ha hb hab
  refine ⟨mem_univ _, ?_⟩
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hw₁ hw₂ ⊢
  set t : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have ht : Tendsto t atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun k ↦ show (0 : ℝ) < t k from Nat.one_div_pos_of_nat⟩
  obtain ⟨wk₁, hwk₁, hls₁⟩ := (h t ht w₁).2
  obtain ⟨wk₂, hwk₂, hls₂⟩ := (h t ht w₂).2
  have hlim := (h t ht (a • w₁ + b • w₂)).1 (fun k ↦ a • wk₁ k + b • wk₂ k)
    ((hwk₁.const_smul a).add (hwk₂.const_smul b))
  -- `d²φ(x̄, v)(a w₁ + b w₂) ≤ a α₁ + b α₂ + ε` for every `ε > 0`
  have hε : ∀ ε > 0, secondSubderiv φ x₀ v (a • w₁ + b • w₂) ≤
      ((a * α₁ + b * α₂ + ε : ℝ) : EReal) := by
    intro ε hε
    have e₁ : ∀ᶠ k in atTop, secondDiffQuot φ x₀ v (t k) (wk₁ k) < ((α₁ + ε : ℝ) : EReal) :=
      eventually_lt_of_limsup_lt (hls₁.trans_lt (hw₁.trans_lt (by
        rw [EReal.coe_lt_coe_iff]; linarith)))
    have e₂ : ∀ᶠ k in atTop, secondDiffQuot φ x₀ v (t k) (wk₂ k) < ((α₂ + ε : ℝ) : EReal) :=
      eventually_lt_of_limsup_lt (hls₂.trans_lt (hw₂.trans_lt (by
        rw [EReal.coe_lt_coe_iff]; linarith)))
    refine hlim.trans (le_trans liminf_le_limsup (limsup_le_of_le (by isBoundedDefault) ?_))
    filter_upwards [e₁, e₂] with k hk₁ hk₂
    have := secondDiffQuot_combo_le hconv hr (show (0 : ℝ) < t k from Nat.one_div_pos_of_nat)
      ha hb hab hk₁.le hk₂.le
    refine this.trans (le_of_eq ?_)
    congr 1
    linear_combination ε * hab
  refine ge_of_tendsto (f := fun ε : ℝ ↦ ((a * α₁ + b * α₂ + ε : ℝ) : EReal)) (x := 𝓝[>] 0) ?_
    (eventually_nhdsWithin_of_forall fun ε hε' ↦ hε ε hε')
  have : Tendsto (fun ε : ℝ ↦ ((a * α₁ + b * α₂ + ε : ℝ) : EReal)) (𝓝 0)
      (𝓝 ((a * α₁ + b * α₂ + 0 : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.comp (continuous_const.add continuous_id)).tendsto 0
  simpa using this.mono_left nhdsWithin_le_nhds

end Convex

/-! ### Lemma 1.94 -/

section Scaling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem coe_mul_le_coe_mul_iff {c : ℝ} (hc : 0 < c) {a b : EReal} :
    (c : EReal) * a ≤ c * b ↔ a ≤ b := by
  refine ⟨fun h ↦ ?_, fun h ↦ PosMulMono.mul_le_mul_of_nonneg_left (EReal.coe_nonneg.2 hc.le) h⟩
  have h' := PosMulMono.mul_le_mul_of_nonneg_left (EReal.coe_nonneg.2 (inv_pos.2 hc).le) h
  rwa [← mul_assoc, ← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hc.ne', EReal.coe_one,
    one_mul, one_mul] at h'

theorem coe_mul_iInf_of_pos {ι : Sort*} {c : ℝ} (hc : 0 < c) (f : ι → EReal) :
    (c : EReal) * ⨅ i, f i = ⨅ i, (c : EReal) * f i := by
  have hinv : ∀ a : EReal, (c : EReal) * (((c⁻¹ : ℝ) : EReal) * a) = a := fun a ↦ by
    rw [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hc.ne', EReal.coe_one, one_mul]
  refine le_antisymm (le_iInf fun i ↦ (coe_mul_le_coe_mul_iff hc).2 (iInf_le _ i)) ?_
  have : ((c⁻¹ : ℝ) : EReal) * ⨅ i, (c : EReal) * f i ≤ ⨅ i, f i := by
    refine le_iInf fun i ↦ (coe_mul_le_coe_mul_iff hc).1 ?_
    rw [hinv]
    exact iInf_le _ i
  calc ⨅ i, (c : EReal) * f i = c * (((c⁻¹ : ℝ) : EReal) * ⨅ i, (c : EReal) * f i) :=
        (hinv _).symm
    _ ≤ c * ⨅ i, f i := (coe_mul_le_coe_mul_iff hc).2 this

variable {φ : E → EReal} {t l : ℝ}

theorem proxObjective_scale (φ : E → EReal) (ht : 0 < t) (l : ℝ) (u w : E) :
    proxObjective (fun w ↦ ((t⁻¹ ^ 2 : ℝ) : EReal) * φ (t • w)) l u w =
      ((t⁻¹ ^ 2 : ℝ) : EReal) * proxObjective φ l (t • u) (t • w) := by
  simp only [proxObjective]
  rw [EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.2 (by positivity))
    (EReal.coe_ne_top _), ← EReal.coe_mul, ← smul_sub, norm_smul, Real.norm_of_nonneg ht.le]
  congr 2
  field_simp

theorem smul_surjective_of_ne_zero (ht : t ≠ 0) : Function.Surjective fun w : E ↦ t • w :=
  fun z ↦ ⟨t⁻¹ • z, by simp [smul_smul, ht]⟩

/-- [Mordukhovich 2024, Lemma 1.94, (1.131)], general form: the Moreau envelope of
`w ↦ t⁻²φ(tw)` is `u ↦ t⁻² e_λφ(tu)`. -/
theorem moreauEnvelope_scale (φ : E → EReal) (ht : 0 < t) (l : ℝ) (u : E) :
    moreauEnvelope (fun w ↦ ((t⁻¹ ^ 2 : ℝ) : EReal) * φ (t • w)) l u =
      ((t⁻¹ ^ 2 : ℝ) : EReal) * moreauEnvelope φ l (t • u) := by
  simp only [moreauEnvelope, proxObjective_scale φ ht]
  rw [coe_mul_iInf_of_pos (by positivity)]
  exact (smul_surjective_of_ne_zero ht.ne').iInf_comp
    (fun z ↦ ((t⁻¹ ^ 2 : ℝ) : EReal) * proxObjective φ l (t • u) z)

/-- [Mordukhovich 2024, Lemma 1.94, (1.131)], general form: `x ∈ P_λ(t⁻²φ(t·))(u)` iff
`tx ∈ P_λφ(tu)`. -/
theorem mem_proximalMap_scale_iff (φ : E → EReal) (ht : 0 < t) (l : ℝ) {u x : E} :
    x ∈ proximalMap (fun w ↦ ((t⁻¹ ^ 2 : ℝ) : EReal) * φ (t • w)) l u ↔
      t • x ∈ proximalMap φ l (t • u) := by
  simp only [proximalMap, Set.mem_ofPred_eq, proxObjective_scale φ ht,
    coe_mul_le_coe_mul_iff (show (0 : ℝ) < t⁻¹ ^ 2 by positivity)]
  refine ⟨fun h z ↦ ?_, fun h y ↦ h (t • y)⟩
  have := h (t⁻¹ • z)
  rwa [smul_smul, mul_inv_cancel₀ ht.ne', one_smul] at this

theorem proximalMap_scale (φ : E → EReal) (ht : 0 < t) (l : ℝ) (u : E) :
    proximalMap (fun w ↦ ((t⁻¹ ^ 2 : ℝ) : EReal) * φ (t • w)) l u =
      t⁻¹ • proximalMap φ l (t • u) := by
  ext x
  rw [mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero ht.ne'), inv_inv,
    mem_proximalMap_scale_iff φ ht]

/-- For `φ(0) = 0`, `Δ²_tφ(0, 0)(w)/2 = t⁻²φ(tw)`. -/
theorem half_secondDiffQuot_zero (h0 : φ 0 = 0) (ht : t ≠ 0) (w : E) :
    ((1 / 2 : ℝ) : EReal) * secondDiffQuot φ 0 0 t w = ((t⁻¹ ^ 2 : ℝ) : EReal) * φ (t • w) := by
  have hz : ((t * (0 : StrongDual ℝ E) w : ℝ) : EReal) = 0 := by simp
  simp only [secondDiffQuot, zero_add, h0, hz, sub_zero]
  rw [← mul_assoc, ← EReal.coe_mul]
  congr 2
  field_simp

/-- [Mordukhovich 2024, Lemma 1.94, (1.131)], first formula: if `φ(0) = 0` and `e_λφ(0) = 0`
(e.g. `0` minimizes `φ`), then `e_λ(Δ²_tφ(0, 0)/2) = Δ²_t(e_λφ)(0, 0)/2`. -/
theorem moreauEnvelope_half_secondDiffQuot (h0 : φ 0 = 0) (he : moreauEnvelope φ l 0 = 0)
    (ht : 0 < t) (u : E) :
    moreauEnvelope (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondDiffQuot φ 0 0 t w) l u =
      ((1 / 2 : ℝ) : EReal) * secondDiffQuot (moreauEnvelope φ l) 0 0 t u := by
  simp only [half_secondDiffQuot_zero h0 ht.ne', half_secondDiffQuot_zero he ht.ne']
  exact moreauEnvelope_scale φ ht l u

/-- [Mordukhovich 2024, Lemma 1.94, (1.131)], second formula: if `φ(0) = 0`, then
`P_λ(Δ²_tφ(0, 0)/2)(u) = t⁻¹ P_λφ(tu)`, which is `(Δ_t P_λφ)(0, 0)(u)` when `P_λφ(0) = {0}`. -/
theorem proximalMap_half_secondDiffQuot (h0 : φ 0 = 0) (ht : 0 < t) (u : E) :
    proximalMap (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondDiffQuot φ 0 0 t w) l u =
      t⁻¹ • proximalMap φ l (t • u) := by
  simp only [half_secondDiffQuot_zero h0 ht.ne']
  exact proximalMap_scale φ ht l u

/-! #### Subdifferentials of scaled functions -/

/-- The linear isomorphism `(x, α) ↦ (x, cα)` of `E × ℝ`. -/
noncomputable def scaleSnd (c : ℝ) (hc : c ≠ 0) : (E × ℝ) ≃L[ℝ] (E × ℝ) :=
  ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.fst ℝ E ℝ).prod (c • ContinuousLinearMap.snd ℝ E ℝ))
    ((ContinuousLinearMap.fst ℝ E ℝ).prod (c⁻¹ • ContinuousLinearMap.snd ℝ E ℝ))
    (fun p ↦ Prod.ext rfl (by simp [inv_mul_cancel_left₀ hc]))
    (fun p ↦ Prod.ext rfl (by simp [mul_inv_cancel_left₀ hc]))

theorem scaleSnd_apply (c : ℝ) (hc : c ≠ 0) (p : E × ℝ) :
    scaleSnd c hc p = (p.1, c * p.2) := rfl

theorem epi_coe_mul {θ : E → EReal} {c : ℝ} (hc : 0 < c) :
    (fun x ↦ (c : EReal) * θ x).Epi univ = scaleSnd c hc.ne' '' θ.Epi univ := by
  ext ⟨x, α⟩
  simp only [Function.Epi, Set.mem_ofPred_eq, mem_univ, true_and, mem_image]
  constructor
  · intro h
    refine ⟨(x, c⁻¹ * α), ?_, by
      rw [scaleSnd_apply, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]⟩
    rw [← coe_mul_le_coe_mul_iff hc, ← EReal.coe_mul, ← mul_assoc, mul_inv_cancel₀ hc.ne',
      one_mul]
    exact h
  · rintro ⟨⟨y, β⟩, h, hp⟩
    rw [scaleSnd_apply, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    rw [EReal.coe_mul]
    exact (coe_mul_le_coe_mul_iff hc).2 h

/-- Limiting subdifferentials of positive multiples: `∂(cθ)(x) = c ∂θ(x)`. -/
theorem mem_subdiff_coe_mul_iff {θ : E → EReal} {c : ℝ} (hc : 0 < c) {x₀ : E}
    {y : StrongDual ℝ E} :
    y ∈ subdiff (fun x ↦ (c : EReal) * θ x) x₀ ↔ c⁻¹ • y ∈ subdiff θ x₀ := by
  set L := scaleSnd (E := E) c hc.ne'
  have hcomp : ∀ z : StrongDual ℝ E,
      (z.coprod (-1)).comp (L : E × ℝ →L[ℝ] E × ℝ) = c • ((c⁻¹ • z).coprod (-1)) := by
    intro z
    refine ContinuousLinearMap.ext fun p ↦ ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, scaleSnd_apply]
    simp
    field_simp
  by_cases hfin : ∃ r : ℝ, θ x₀ = r
  · obtain ⟨r, hr⟩ := hfin
    have hr' : (fun x ↦ (c : EReal) * θ x) x₀ = ((c * r : ℝ) : EReal) := by
      simp only [hr, EReal.coe_mul]
    have hL : L (x₀, r) = (x₀, c * r) := scaleSnd_apply _ _ _
    rw [mem_subdiff_iff (φ := fun x ↦ (c : EReal) * θ x) hr', mem_subdiff_iff hr, epi_coe_mul hc,
      ← hL, mem_normalCone_image_iff L, hcomp]
    refine ⟨fun h ↦ ?_, fun h ↦ smul_mem_normalCone h hc.le⟩
    have := smul_mem_normalCone h (inv_pos.2 hc).le
    rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at this
  · push Not at hfin
    have h1 : y ∉ subdiff (fun x ↦ (c : EReal) * θ x) x₀ := by
      rintro ⟨s, hs, -⟩
      apply hfin (c⁻¹ * s)
      have := congrArg (fun a ↦ ((c⁻¹ : ℝ) : EReal) * a) hs
      simp only at this
      rwa [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hc.ne', EReal.coe_one, one_mul,
        ← EReal.coe_mul] at this
    have h2 : c⁻¹ • y ∉ subdiff θ x₀ := fun ⟨s, hs, _⟩ ↦ hfin s hs
    exact iff_of_false h1 h2

end Scaling

section Quotient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- [Mordukhovich 2024, Lemma 1.94, (1.130)]: subdifferentials of second-order difference
quotients are difference quotients of the subdifferential,
`∂(Δ²_tφ(x̄, v̄)/2)(w) = (∂φ(x̄ + tw) - v̄)/t`. -/
theorem subdiff_half_secondDiffQuot {φ : E → EReal} {x₀ : E} {v : StrongDual ℝ E} {r : ℝ}
    (hr : φ x₀ = r) {t : ℝ} (ht : 0 < t) (w : E) :
    subdiff (fun u ↦ ((1 / 2 : ℝ) : EReal) * secondDiffQuot φ x₀ v t u) w =
      (fun z ↦ t⁻¹ • (z - v)) '' subdiff φ (x₀ + t • w) := by
  -- rewrite the quotient as `t⁻² (φ ∘ g + f)` with `g u = x₀ + tu`, `f u = -r - t⟨v, u⟩`
  have hfun : (fun u ↦ ((1 / 2 : ℝ) : EReal) * secondDiffQuot φ x₀ v t u) =
      fun u ↦ ((t⁻¹ ^ 2 : ℝ) : EReal) * (φ (x₀ + t • u) + ((-r - t * v u : ℝ) : EReal)) := by
    funext u
    simp only [secondDiffQuot, hr]
    rw [← mul_assoc, ← EReal.coe_mul, sub_eq_add_neg, sub_eq_add_neg, add_assoc,
      ← EReal.coe_neg, ← EReal.coe_neg, ← EReal.coe_add]
    congr 2
    field_simp
  have hc : (0 : ℝ) < t⁻¹ ^ 2 := by positivity
  -- the chain rule for `g`
  have hg : subdiff (fun u ↦ φ (x₀ + t • u)) w =
      (fun z : StrongDual ℝ E ↦ z.comp (t • ContinuousLinearMap.id ℝ E)) ''
        subdiff φ (x₀ + t • w) :=
    subdiff_comp_of_surjective (D := fun _ ↦ t • ContinuousLinearMap.id ℝ E)
      (Eventually.of_forall fun y ↦ ((hasStrictFDerivAt_id y).const_smul t).const_add x₀)
      continuousAt_const (fun z ↦ ⟨t⁻¹ • z, by simp [smul_smul, ht.ne']⟩)
  -- the sum rule for `f`
  have hf : ∀ᶠ u in 𝓝 w, HasFDerivAt (fun u ↦ -r - t * v u) (-(t • v)) u :=
    Eventually.of_forall fun u ↦ by
      simpa using ((v.hasFDerivAt (x := u)).const_mul t).const_sub (-r)
  ext y
  rw [hfun, mem_subdiff_coe_mul_iff hc, mem_subdiff_add_iff hf continuousAt_const, hg]
  simp only [mem_image, sub_neg_eq_add]
  constructor
  · rintro ⟨z, hz, hzy⟩
    refine ⟨z, hz, ?_⟩
    ext d
    have h1 := congrArg (fun f : StrongDual ℝ E ↦ f d) hzy
    simp only [ContinuousLinearMap.comp_smulₛₗ, RingHom.id_apply, ContinuousLinearMap.comp_id,
      smul_apply, smul_eq_mul, inv_pow, inv_inv, add_apply] at h1
    simp only [smul_apply, sub_apply, smul_eq_mul]
    have h2 : z d - v d = t * y d :=
      mul_left_cancel₀ ht.ne' (by linear_combination h1)
    rw [h2, ← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul]
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z, hz, ?_⟩
    ext d
    simp [smul_smul]
    field_simp
    ring

end Quotient

end VariationalAnalysis
