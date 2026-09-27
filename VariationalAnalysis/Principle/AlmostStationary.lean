/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.SpecialFunctions.Sqrt
import VariationalAnalysis.Principle.Variational
import VariationalAnalysis.SetValued.OuterLimit

/-!
# Subdifferential almost stationary conditions; density of regular subgradients

Applications of the general variational principle (Thm. 2.12 of [Mordukhovich 2018]) with a
differentiable perturbation `θ`: suboptimal points `x₀` of a l.s.c. function `φ` are close to
points `x̄` with a small regular subgradient [Mordukhovich 2018, Thm. 2.14], and points where
`∂̂φ` is nonempty are dense in the graph of `φ` [Mordukhovich 2018, Exercise 2.25(iii)].

## Main results

* `exists_mem_regularSubdiff_of_hasFDerivAt`: Thm. 2.14 of [Mordukhovich 2018] for a general
  differentiable perturbation `θ`: `-(ε/λ) ∇θ(x̄ - x₀)` is a regular subgradient of `φ` at `x̄`,
  and the only upper regular subgradient there.
* `exists_mem_regularSubdiff_almost_stationary`,
  `exists_mem_regularSubdiff_norm_sub_lt_two_mul`: Thm. 2.14 of [Mordukhovich 2018]
  (subdifferential almost stationary conditions), in finite-dimensional inner product spaces.
  The upper part in finite-dimensional normed spaces is `ekeland_almost_stationary`.
* `exists_mem_ball_regularSubdiff_nonempty`, `exists_seq_tendsto_regularSubdiff_nonempty`,
  `frequently_funNhds_regularSubdiff_nonempty`: Exercise 2.25(iii) of [Mordukhovich 2018]
  (density of regular subgradients) in finite-dimensional normed spaces, for functions that are
  l.s.c. around the point.

## Remark on Thm. 2.14 of the book

The book states the first part with `‖x̄ - x₀‖ ≤ λ` and `‖v‖ ≤ ε/λ`, but its proof uses
`θ = ‖·‖² / (4λ)`, for which Thm. 2.12 only gives `θ(x̄ - x₀) ≤ λ`, i.e. `‖x̄ - x₀‖ ≤ 2λ`. No
rescaling of a quadratic perturbation `c ‖· - x₀‖²` gives both bounds: the minimizer only obeys
`c ‖x̄ - x₀‖² ≤ ε`, and `‖v‖ = 2c ‖x̄ - x₀‖`, so `‖x̄ - x₀‖ ≤ λ` forces `c ≥ ε/λ²` while
`‖v‖ ≤ ε/λ` forces `c ≤ ε/(4λ²)`. With the smoothed norm `θ = √(‖·‖² + η²) - η` one gets
`‖x̄ - x₀‖ < λ + η` and `‖v‖ < ε/λ` for every `η > 0`
(`exists_mem_regularSubdiff_almost_stationary`), which is the book's statement up to an
arbitrarily small enlargement of the radius; the book's proof gives the case `η = λ`
(`exists_mem_regularSubdiff_norm_sub_lt_two_mul`). Moreover, both parts of the theorem hold at
the same point `x̄`: there, every upper regular subgradient coincides with `v`.
-/

open Filter Topology Set Metric

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {φ : E → EReal} {θ : E → ℝ} {x₀ : E} {ε ρ : ℝ}

/-- A regular subgradient and an upper regular subgradient at the same point coincide: if
`u ∈ ∂̂φ(z)` and `w ∈ ∂̂⁺φ(z) = -∂̂(-φ)(z)`, then `u = w`. -/
theorem eq_of_mem_regularSubdiff_of_neg_mem {z : E} {u w : StrongDual ℝ E}
    (hu : u ∈ regularSubdiff φ z) (hw : -w ∈ regularSubdiff (fun x ↦ -φ x) z) : u = w := by
  obtain ⟨r, hr, hu⟩ := hu
  obtain ⟨s, hs, hw⟩ := hw
  have hsr : s = -r := by
    have : -φ z = s := hs
    rw [hr, ← EReal.coe_neg, EReal.coe_eq_coe_iff] at this
    exact this.symm
  have h0 : ‖u - w‖ ≤ 0 := by
    refine norm_le_of_forall_eventually_le (z := z) le_rfl fun δ hδ ↦ ?_
    filter_upwards [hu (δ / 2) (half_pos hδ), hw (δ / 2) (half_pos hδ)] with x h1 h2
    have h2' : -φ x ≥ _ := h2
    rw [ge_iff_le, EReal.le_neg] at h2'
    have := EReal.coe_le_coe_iff.1 (h1.trans (h2'.trans_eq (EReal.coe_neg _).symm))
    simp only [neg_apply, sub_apply] at this ⊢
    rw [hsr] at this
    linarith
  rw [← sub_eq_zero]
  exact norm_le_zero_iff.1 h0

/-- Thm. 2.14 of [Mordukhovich 2018] (subdifferential almost stationary conditions), for a
general differentiable perturbation: under the assumptions of Thm. 2.12, with `θ` differentiable
(`∇θ = θ'`), nonnegative and `θ 0 = 0`, there is `x̄` (here `z`) with `θ(x̄ - x₀) ≤ λ` (here
`ρ`), `φ x̄ ≤ φ x₀`, `v = -(ε/λ) ∇θ(x̄ - x₀) ∈ ∂̂φ(x̄)`, and every `w ∈ ∂̂⁺φ(x̄) = -∂̂(-φ)(x̄)`
equals `v`. The book's proof takes `θ = ‖·‖²/(4λ)`. -/
theorem exists_mem_regularSubdiff_of_hasFDerivAt (hφ : LowerSemicontinuous φ)
    (hbdd : ∃ m : ℝ, ∀ x, (m : EReal) ≤ φ x) {θ' : E → StrongDual ℝ E}
    (hθd : ∀ y, HasFDerivAt θ (θ' y) y) (hθnn : ∀ x, 0 ≤ θ x) (hθ0 : θ 0 = 0)
    (hθc : Tendsto θ (cocompact E) atTop) (hε : 0 < ε) (hρ : 0 < ρ) (hx₀ : φ x₀ ≠ ⊤)
    (hsub : φ x₀ ≤ (⨅ x, φ x) + ε) :
    ∃ z, θ (z - x₀) ≤ ρ ∧ φ z ≤ φ x₀ ∧ -((ε / ρ) • θ' (z - x₀)) ∈ regularSubdiff φ z ∧
      ∀ w, -w ∈ regularSubdiff (fun x ↦ -φ x) z → w = -((ε / ρ) • θ' (z - x₀)) := by
  have hθ : LowerSemicontinuous θ :=
    (continuous_iff_continuousAt.2 fun y ↦ (hθd y).continuousAt).lowerSemicontinuous
  obtain ⟨z, h1, hle, hθz⟩ := general_variational_principle hφ hbdd hθ hθnn hθ0 hθc hε hρ hx₀ hsub
  obtain ⟨m, hm⟩ := hbdd
  obtain ⟨b, hb⟩ := exists_coe_eq_of_ne_top (hm z) (ne_top_of_le_ne_top hx₀ hle)
  have hg : HasFDerivAt (fun x ↦ ε / ρ * θ (x - x₀)) ((ε / ρ) • θ' (z - x₀)) z := by
    have := ((hθd (z - x₀)).comp z ((hasFDerivAt_id z).sub_const x₀)).const_mul (ε / ρ)
    simpa using this
  have hmin : IsLocalMin (fun x ↦ φ x + ((ε / ρ * θ (x - x₀) : ℝ) : EReal)) z :=
    Eventually.of_forall h1
  have h0 := zero_mem_regularSubdiff_of_isLocalMin hmin (r := b + ε / ρ * θ (z - x₀))
    (by rw [hb, EReal.coe_add])
  rw [mem_regularSubdiff_add_iff hg, zero_sub] at h0
  exact ⟨z, hθz, hle, h0, fun w hw ↦ (eq_of_mem_regularSubdiff_of_neg_mem h0 hw).symm⟩

section InnerProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The smoothed norm `y ↦ √(‖y‖² + η²) - η` is differentiable with gradient
`y / √(‖y‖² + η²)`. -/
theorem hasFDerivAt_sqrt_norm_sq_add_sq_sub {η : ℝ} (hη : 0 < η) (y : H) :
    HasFDerivAt (fun y : H ↦ √(‖y‖ ^ 2 + η ^ 2) - η)
      ((√(‖y‖ ^ 2 + η ^ 2))⁻¹ • innerSL ℝ y) y := by
  have h1 : HasFDerivAt (fun y : H ↦ ‖y‖ ^ 2 + η ^ 2) (2 • innerSL ℝ y) y := by
    simpa using ((hasFDerivAt_id y).norm_sq).add_const (η ^ 2)
  have hpos : 0 < √(‖y‖ ^ 2 + η ^ 2) := Real.sqrt_pos.2 (by positivity)
  refine ((h1.sqrt (by positivity)).sub_const η).congr_fderiv ?_
  ext h
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul,
    Nat.cast_ofNat]
  field_simp

variable [FiniteDimensional ℝ H] {φ : H → EReal} {x₀ : H}

/-- Thm. 2.14 of [Mordukhovich 2018] (subdifferential almost stationary conditions), in a
finite-dimensional inner product space: for `φ` l.s.c., bounded below, finite at `x₀` with
`φ x₀ ≤ inf φ + ε`, all `λ > 0` (here `ρ`) and `η > 0`, there are `x̄` (here `z`) and
`v ∈ ∂̂φ(x̄)` with `‖x̄ - x₀‖ < λ + η`, `φ x̄ ≤ φ x₀` and `‖v‖ < ε/λ`; moreover every upper
regular subgradient `w ∈ ∂̂⁺φ(x̄) = -∂̂(-φ)(x̄)` equals `v`, so `‖w‖ < ε/λ`. The book states
`‖x̄ - x₀‖ ≤ λ`, which its proof does not give (see the module docstring); the perturbation used
here is `θ = √(‖·‖² + η²) - η`. -/
theorem exists_mem_regularSubdiff_almost_stationary (hφ : LowerSemicontinuous φ)
    (hbdd : ∃ m : ℝ, ∀ x, (m : EReal) ≤ φ x) (hε : 0 < ε) (hρ : 0 < ρ) (hx₀ : φ x₀ ≠ ⊤)
    (hsub : φ x₀ ≤ (⨅ x, φ x) + ε) {η : ℝ} (hη : 0 < η) :
    ∃ z v, v ∈ regularSubdiff φ z ∧ ‖z - x₀‖ < ρ + η ∧ φ z ≤ φ x₀ ∧ ‖v‖ < ε / ρ ∧
      ∀ w, -w ∈ regularSubdiff (fun x ↦ -φ x) z → w = v := by
  have hle : ∀ y : H, ‖y‖ ≤ √(‖y‖ ^ 2 + η ^ 2) := fun y ↦
    (Real.le_sqrt (norm_nonneg _) (by positivity)).2 (by nlinarith)
  have hlt : ∀ y : H, ‖y‖ < √(‖y‖ ^ 2 + η ^ 2) := fun y ↦
    (Real.lt_sqrt (norm_nonneg _)).2 (by nlinarith)
  have hθnn : ∀ y : H, 0 ≤ √(‖y‖ ^ 2 + η ^ 2) - η := fun y ↦ by
    have : η ≤ √(‖y‖ ^ 2 + η ^ 2) :=
      (Real.le_sqrt hη.le (by positivity)).2 (by nlinarith [sq_nonneg ‖y‖])
    linarith
  have hθ0 : √(‖(0 : H)‖ ^ 2 + η ^ 2) - η = 0 := by
    simp [Real.sqrt_sq hη.le]
  have hθc : Tendsto (fun y : H ↦ √(‖y‖ ^ 2 + η ^ 2) - η) (cocompact H) atTop :=
    tendsto_atTop_mono (fun y ↦ by linarith [hle y])
      (tendsto_atTop_add_const_right _ (-η) tendsto_norm_cocompact_atTop)
  obtain ⟨z, hθz, hφz, hv, hw⟩ := exists_mem_regularSubdiff_of_hasFDerivAt hφ hbdd
    (hasFDerivAt_sqrt_norm_sq_add_sq_sub hη) hθnn hθ0 hθc hε hρ hx₀ hsub
  refine ⟨z, _, hv, by linarith [hlt (z - x₀)], hφz, ?_, hw⟩
  set y := z - x₀
  have hpos : 0 < √(‖y‖ ^ 2 + η ^ 2) := (norm_nonneg y).trans_lt (hlt y)
  rw [norm_neg, norm_smul, norm_smul, innerSL_apply_norm, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (div_pos hε hρ), abs_of_pos (inv_pos.2 hpos)]
  have : (√(‖y‖ ^ 2 + η ^ 2))⁻¹ * ‖y‖ < 1 := by
    rw [inv_mul_lt_iff₀ hpos, mul_one]; exact hlt y
  nlinarith [div_pos hε hρ]

/-- Thm. 2.14 of [Mordukhovich 2018] (subdifferential almost stationary conditions), in the form
given by the book's proof: there are `x̄` (here `z`) and `v ∈ ∂̂φ(x̄)` with `‖x̄ - x₀‖ < 2λ` (here
`ρ`), `φ x̄ ≤ φ x₀`, `‖v‖ ≤ ε/λ`, and `‖w‖ ≤ ε/λ` for every `w ∈ ∂̂⁺φ(x̄)`. -/
theorem exists_mem_regularSubdiff_norm_sub_lt_two_mul (hφ : LowerSemicontinuous φ)
    (hbdd : ∃ m : ℝ, ∀ x, (m : EReal) ≤ φ x) (hε : 0 < ε) (hρ : 0 < ρ) (hx₀ : φ x₀ ≠ ⊤)
    (hsub : φ x₀ ≤ (⨅ x, φ x) + ε) :
    ∃ z, ∃ v ∈ regularSubdiff φ z, ‖z - x₀‖ < 2 * ρ ∧ φ z ≤ φ x₀ ∧ ‖v‖ ≤ ε / ρ ∧
      ∀ w, -w ∈ regularSubdiff (fun x ↦ -φ x) z → ‖w‖ ≤ ε / ρ := by
  obtain ⟨z, v, hv, hz, hφz, hnorm, hw⟩ :=
    exists_mem_regularSubdiff_almost_stationary hφ hbdd hε hρ hx₀ hsub hρ
  exact ⟨z, v, hv, by linarith, hφz, hnorm.le, fun w hw' ↦ hw w hw' ▸ hnorm.le⟩

end InnerProduct

section Density

variable [FiniteDimensional ℝ E]

/-- Exercise 2.25(iii) of [Mordukhovich 2018] (density of regular subgradients), local form: if
`φ` is l.s.c. around `x₀` and finite at `x₀`, then every ball around `x₀` contains a point `x`
with `φ x ≤ φ x₀` and `∂̂φ(x) ≠ ∅`. The proof applies Thm. 2.14 (with the differentiable
perturbation `‖toEuclidean ·‖²`) to `φ` restricted to a small closed ball, which is bounded
below by lower semicontinuity. -/
theorem exists_mem_ball_regularSubdiff_nonempty {a : ℝ} (hx : φ x₀ = a)
    (hlsc : ∀ᶠ x in 𝓝 x₀, LowerSemicontinuousAt φ x) {s : ℝ} (hs : 0 < s) :
    ∃ x ∈ ball x₀ s, φ x ≤ φ x₀ ∧ (regularSubdiff φ x).Nonempty := by
  classical
  have hlow : ∀ᶠ x in 𝓝 x₀, ((a - 1 : ℝ) : EReal) < φ x :=
    (hlsc.self_of_nhds : LowerSemicontinuousAt φ x₀) _
      (show ((a - 1 : ℝ) : EReal) < φ x₀ by rw [hx]; exact EReal.coe_lt_coe_iff.2 (by linarith))
  obtain ⟨R, hR, hP⟩ := Metric.eventually_nhds_iff_ball.1 (hlsc.and hlow)
  set B := closedBall x₀ (R / 2)
  have hBR : B ⊆ ball x₀ R := closedBall_subset_ball (half_lt_self hR)
  set ψ : E → EReal := fun x ↦ if x ∈ B then φ x else ⊤ with hψ_def
  have hψge : ∀ x, φ x ≤ ψ x := fun x ↦ by
    by_cases h : x ∈ B <;> simp [ψ, h]
  have hψlsc : LowerSemicontinuous ψ := by
    intro x y hy
    by_cases h : x ∈ B
    · have hyφ : y < φ x := by simpa [ψ, h] using hy
      exact ((hP x (hBR h)).1 y hyφ).mono fun x' hx' ↦ hx'.trans_le (hψge x')
    · have hy' : y < ⊤ := by simpa [ψ, h] using hy
      filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds h] with x' hx'
      simpa [ψ, show x' ∉ B from hx'] using hy'
  have hψm : ∀ x, ((a - 1 : ℝ) : EReal) ≤ ψ x := fun x ↦ by
    by_cases h : x ∈ B
    · simpa [ψ, h] using ((hP x (hBR h)).2).le
    · simp [ψ, h]
  have hψ0 : ψ x₀ = a := by simp [ψ, B, (half_pos hR).le, hx]
  have hsub : ψ x₀ ≤ (⨅ x, ψ x) + ((1 : ℝ) : EReal) := by
    rw [hψ0]
    calc (a : EReal) = ((a - 1 : ℝ) : EReal) + ((1 : ℝ) : EReal) := by
          rw [← EReal.coe_add, sub_add_cancel]
      _ ≤ (⨅ x, ψ x) + ((1 : ℝ) : EReal) := add_le_add_left (le_iInf hψm) _
  -- the differentiable perturbation `θ = ‖e ·‖²`, `e = toEuclidean`
  set e := (toEuclidean : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
  set C := ‖(e.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E)‖
  have hC : 0 ≤ C := norm_nonneg _
  have hθc : Tendsto (fun y ↦ ‖e y‖ ^ 2) (cocompact E) atTop :=
    (tendsto_pow_atTop two_ne_zero).comp
      (tendsto_norm_cocompact_atTop.comp e.toHomeomorph.map_cocompact.le)
  set s' := min s (R / 2)
  have hs' : 0 < s' := lt_min hs (half_pos hR)
  obtain ⟨z, hθz, hψz, hv, -⟩ := exists_mem_regularSubdiff_of_hasFDerivAt (φ := ψ) (x₀ := x₀)
    (ε := 1) (ρ := (s' / (C + 1)) ^ 2) hψlsc ⟨a - 1, hψm⟩
    (fun y ↦ e.hasFDerivAt.norm_sq) (fun _ ↦ sq_nonneg _) (by simp) hθc one_pos
    (by positivity) (by rw [hψ0]; exact EReal.coe_ne_top a) hsub
  have hdist : ‖z - x₀‖ < s' := by
    have h1 : ‖e (z - x₀)‖ ≤ s' / (C + 1) :=
      (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hθz
    have h2 : ‖z - x₀‖ ≤ C * ‖e (z - x₀)‖ := by
      calc ‖z - x₀‖ = ‖e.symm (e (z - x₀))‖ := by rw [e.symm_apply_apply]
        _ ≤ C * ‖e (z - x₀)‖ :=
          (e.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E).le_opNorm _
    have h3 : C * (s' / (C + 1)) < s' := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
    nlinarith
  have hzB : z ∈ ball x₀ (R / 2) := mem_ball_iff_norm.2 (hdist.trans_le (min_le_right _ _))
  have hψφ : ψ =ᶠ[𝓝 z] φ := Filter.eventually_of_mem (isOpen_ball.mem_nhds hzB) fun x hx ↦
    if_pos (ball_subset_closedBall hx)
  refine ⟨z, mem_ball_iff_norm.2 (hdist.trans_le (min_le_left _ _)), ?_,
    ⟨_, regularSubdiff_congr hψφ ▸ hv⟩⟩
  rw [← hψφ.self_of_nhds]
  exact hψz.trans_eq (hψ0.trans hx.symm)

/-- Exercise 2.25(iii) of [Mordukhovich 2018] (density of regular subgradients): if `φ` is
l.s.c. around `x₀` and finite at `x₀`, there are `xₖ → x₀` with `φ xₖ → φ x₀`,
`φ xₖ ≤ φ x₀` and `∂̂φ(xₖ) ≠ ∅`. -/
theorem exists_seq_tendsto_regularSubdiff_nonempty {a : ℝ} (hx : φ x₀ = a)
    (hlsc : ∀ᶠ x in 𝓝 x₀, LowerSemicontinuousAt φ x) :
    ∃ x : ℕ → E, Tendsto x atTop (𝓝 x₀) ∧ Tendsto (fun k ↦ φ (x k)) atTop (𝓝 (φ x₀)) ∧
      ∀ k, φ (x k) ≤ φ x₀ ∧ (regularSubdiff φ (x k)).Nonempty := by
  choose x hxb hx using fun k : ℕ ↦
    exists_mem_ball_regularSubdiff_nonempty hx hlsc (s := 1 / (k + 1)) Nat.one_div_pos_of_nat
  have hxt : Tendsto x atTop (𝓝 x₀) := by
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ ↦ dist_nonneg)
      (fun k ↦ (mem_ball.1 (hxb k)).le) tendsto_one_div_add_atTop_nhds_zero_nat)
  refine ⟨x, hxt, tendsto_order.2 ⟨fun b hb ↦ ?_, fun b hb ↦
    Eventually.of_forall fun k ↦ (hx k).1.trans_lt hb⟩, hx⟩
  exact hxt.eventually (hlsc.self_of_nhds b hb)

/-- Exercise 2.25(iii) of [Mordukhovich 2018] (density of regular subgradients), filter form:
if `φ` is l.s.c. around `x₀` and finite at `x₀`, then `∂̂φ(x) ≠ ∅` for `x` frequently along
`x →φ x₀`. -/
theorem frequently_funNhds_regularSubdiff_nonempty {a : ℝ} (hx : φ x₀ = a)
    (hlsc : ∀ᶠ x in 𝓝 x₀, LowerSemicontinuousAt φ x) :
    ∃ᶠ x in funNhds φ x₀, (regularSubdiff φ x).Nonempty := by
  obtain ⟨x, hxt, hφx, hx⟩ := exists_seq_tendsto_regularSubdiff_nonempty hx hlsc
  exact (tendsto_funNhds_iff.2 ⟨hxt, hφx⟩).frequently
    (Frequently.of_forall fun k ↦ (hx k).2)

/-- Exercise 2.25(iii) of [Mordukhovich 2018]: a point where `φ` is finite and l.s.c. around
lies in the closure of the domain of `∂̂φ`. -/
theorem mem_closure_regularSubdiff_nonempty {a : ℝ} (hx : φ x₀ = a)
    (hlsc : ∀ᶠ x in 𝓝 x₀, LowerSemicontinuousAt φ x) :
    x₀ ∈ closure {x | (regularSubdiff φ x).Nonempty} := by
  obtain ⟨x, hxt, -, hx⟩ := exists_seq_tendsto_regularSubdiff_nonempty hx hlsc
  exact mem_closure_of_tendsto hxt (Eventually.of_forall fun k ↦ (hx k).2)

end Density

end VariationalAnalysis
