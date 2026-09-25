/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# `C¹` convex majorants of vanishing moduli

Let `η : ℝ → ℝ` be nondecreasing, nonnegative, zero on `(-∞, 0]` and continuous at `0` from
the right. We construct a function `τ` of class `C¹` on `ℝ`, convex and nondecreasing on
`[0, ∞)`, with `τ 0 = τ' 0 = 0` and `t η(t) < τ(t)` for `t > 0`. This replaces Steps 1–2 in the
proof of [Mordukhovich 2018, Thm. 1.10] (there by piecewise-linear interpolation) with an
integral construction:

  `g(s) = ∫₁² η(s w) dw`,  `τ(t) = ∫₀^{2t} g + t²`.
-/

open Filter Topology Set intervalIntegral MeasureTheory

namespace VariationalAnalysis

variable {η : ℝ → ℝ}

/-- The averaged modulus `g(s) = ∫₁² η(s w) dw`. -/
noncomputable def avgModulus (η : ℝ → ℝ) (s : ℝ) : ℝ := ∫ w in (1 : ℝ)..2, η (s * w)

/-- The convex majorant `τ(t) = ∫₀^{2t} g + t²`. -/
noncomputable def convexMajorant (η : ℝ → ℝ) (t : ℝ) : ℝ :=
  (∫ s in (0 : ℝ)..2 * t, avgModulus η s) + t ^ 2

/-- The derivative `τ'(t) = 2 g(2t) + 2t`. -/
noncomputable def convexMajorantDeriv (η : ℝ → ℝ) (t : ℝ) : ℝ :=
  2 * avgModulus η (2 * t) + 2 * t

section

variable (hmono : Monotone η) (h0 : ∀ t, 0 ≤ η t) (hneg : ∀ t ≤ 0, η t = 0)
include hmono

theorem intervalIntegrable_comp_mul {s : ℝ} (hs : 0 ≤ s) (a b : ℝ) :
    IntervalIntegrable (fun w ↦ η (s * w)) volume a b :=
  (hmono.comp (monotone_mul_left_of_nonneg hs)).intervalIntegrable

theorem avgModulus_monotoneOn : MonotoneOn (avgModulus η) (Ici 0) := by
  intro s hs s' hs' hss'
  exact integral_mono_on (by norm_num) (intervalIntegrable_comp_mul hmono hs _ _)
    (intervalIntegrable_comp_mul hmono hs' _ _) fun w hw ↦
      hmono (mul_le_mul_of_nonneg_right hss' (by linarith [hw.1]))

theorem le_avgModulus {s : ℝ} (hs : 0 ≤ s) : η s ≤ avgModulus η s := by
  have h : ∫ _ in (1 : ℝ)..2, η s = η s := by simp; norm_num
  rw [← h]
  exact integral_mono_on (by norm_num) (by simp) (intervalIntegrable_comp_mul hmono hs _ _)
    fun w hw ↦ hmono (le_mul_of_one_le_right hs hw.1)

theorem avgModulus_le {s : ℝ} (hs : 0 ≤ s) : avgModulus η s ≤ η (2 * s) := by
  have h : ∫ _ in (1 : ℝ)..2, η (2 * s) = η (2 * s) := by simp; norm_num
  rw [← h]
  exact integral_mono_on (by norm_num) (intervalIntegrable_comp_mul hmono hs _ _) (by simp)
    fun w hw ↦ hmono (by nlinarith [hw.2])

omit hmono in
include h0 in
theorem avgModulus_nonneg (s : ℝ) : 0 ≤ avgModulus η s :=
  integral_nonneg (by norm_num) fun w _ ↦ h0 _

omit hmono in
include hneg in
theorem avgModulus_of_nonpos {s : ℝ} (hs : s ≤ 0) : avgModulus η s = 0 := by
  unfold avgModulus
  rw [integral_congr (g := fun _ ↦ (0 : ℝ)) fun w hw ↦ ?_]
  · simp
  · rw [uIcc_of_le (by norm_num)] at hw
    exact hneg _ (mul_nonpos_of_nonpos_of_nonneg hs (by linarith [hw.1]))

include h0 hneg in
theorem continuous_avgModulus (hlim : Tendsto η (𝓝[≥] 0) (𝓝 0)) :
    Continuous (avgModulus η) := by
  rw [continuous_iff_continuousAt]
  intro s
  rcases lt_trichotomy s 0 with hs | rfl | hs
  · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [gt_mem_nhds hs] with s' hs'
    exact (avgModulus_of_nonpos hneg hs'.le).symm
  · have h2 : Tendsto (fun s' : ℝ ↦ η (2 * |s'|)) (𝓝 0) (𝓝 0) := by
      refine hlim.comp (tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun s' ↦ ?_⟩)
      · have : Tendsto (fun s' : ℝ ↦ 2 * |s'|) (𝓝 0) (𝓝 (2 * |0|)) :=
          (continuous_const.mul continuous_abs).tendsto 0
        simpa using this
      · exact mem_Ici.2 (by positivity)
    rw [ContinuousAt, avgModulus_of_nonpos hneg le_rfl]
    refine squeeze_zero (fun s' ↦ avgModulus_nonneg h0 s') (fun s' ↦ ?_) h2
    rcases le_total 0 s' with h | h
    · rw [abs_of_nonneg h]; exact avgModulus_le hmono h
    · rw [avgModulus_of_nonpos hneg h]; exact h0 _
  · set G : ℝ → ℝ := fun t ↦ ∫ x in (0 : ℝ)..t, η x
    have hG : Continuous G := continuous_primitive (fun a b ↦ hmono.intervalIntegrable) 0
    have hform : ∀ s' ≠ 0, avgModulus η s' = s'⁻¹ * (G (s' * 2) - G (s' * 1)) := by
      intro s' hs'
      unfold avgModulus
      rw [integral_comp_mul_left (fun x ↦ η x) hs', smul_eq_mul,
        integral_interval_sub_left hmono.intervalIntegrable hmono.intervalIntegrable]
    have hc : ContinuousAt (fun s' ↦ s'⁻¹ * (G (s' * 2) - G (s' * 1))) s :=
      (continuousAt_inv₀ hs.ne').mul ((hG.comp (continuous_id.mul continuous_const)).sub
        (hG.comp (continuous_id.mul continuous_const))).continuousAt
    refine hc.congr ?_
    filter_upwards [lt_mem_nhds hs] with s' hs'
    exact (hform s' hs'.ne').symm

variable (hlim : Tendsto η (𝓝[≥] 0) (𝓝 0))
include h0 hneg hlim

theorem hasDerivAt_convexMajorant (t : ℝ) :
    HasDerivAt (convexMajorant η) (convexMajorantDeriv η t) t := by
  have hg := continuous_avgModulus hmono h0 hneg hlim
  have h1 := (hg.integral_hasStrictDerivAt 0 (2 * t)).hasDerivAt.comp t
    ((hasDerivAt_id t).const_mul 2)
  have h2 := hasDerivAt_pow 2 t
  have heq : convexMajorantDeriv η t = avgModulus η (2 * t) * (2 * 1) + ↑(2 : ℕ) * t ^ (2 - 1) := by
    simp only [convexMajorantDeriv]; push_cast; ring
  rw [heq]
  exact h1.add h2

theorem continuous_convexMajorantDeriv : Continuous (convexMajorantDeriv η) :=
  (continuous_const.mul ((continuous_avgModulus hmono h0 hneg hlim).comp
    (continuous_const.mul continuous_id))).add (continuous_const.mul continuous_id)

omit hmono h0 hlim in
theorem convexMajorantDeriv_zero : convexMajorantDeriv η 0 = 0 := by
  simp [convexMajorantDeriv, avgModulus_of_nonpos hneg le_rfl]

omit hmono h0 hneg hlim in
theorem convexMajorant_zero : convexMajorant η 0 = 0 := by simp [convexMajorant]

theorem convexOn_convexMajorant : ConvexOn ℝ (Ici 0) (convexMajorant η) := by
  have hd := hasDerivAt_convexMajorant hmono h0 hneg hlim
  refine MonotoneOn.convexOn_of_deriv (convex_Ici 0)
    (fun t _ ↦ (hd t).continuousAt.continuousWithinAt)
    (fun t _ ↦ (hd t).differentiableAt.differentiableWithinAt) ?_
  intro s hs s' hs' hss'
  rw [interior_Ici, mem_Ioi] at hs hs'
  rw [(hd s).deriv, (hd s').deriv]
  unfold convexMajorantDeriv
  have := avgModulus_monotoneOn hmono (mem_Ici.2 (by linarith : (0 : ℝ) ≤ 2 * s))
    (mem_Ici.2 (by linarith : (0 : ℝ) ≤ 2 * s')) (by linarith)
  linarith

theorem monotoneOn_convexMajorant : MonotoneOn (convexMajorant η) (Ici 0) := by
  have hd := hasDerivAt_convexMajorant hmono h0 hneg hlim
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (fun t _ ↦ (hd t).continuousAt.continuousWithinAt)
    (fun t _ ↦ (hd t).differentiableAt.differentiableWithinAt) fun t ht ↦ ?_
  rw [interior_Ici, mem_Ioi] at ht
  rw [(hd t).deriv]
  unfold convexMajorantDeriv
  have := avgModulus_nonneg h0 (2 * t)
  linarith

theorem mul_lt_convexMajorant {t : ℝ} (ht : 0 < t) : t * η t < convexMajorant η t := by
  have hg := continuous_avgModulus hmono h0 hneg hlim
  have hint : ∀ a b, IntervalIntegrable (avgModulus η) volume a b :=
    fun a b ↦ hg.intervalIntegrable a b
  have h1 : (∫ s in (0 : ℝ)..2 * t, avgModulus η s) =
      (∫ s in (0 : ℝ)..t, avgModulus η s) + ∫ s in t..2 * t, avgModulus η s :=
    (integral_add_adjacent_intervals (hint _ _) (hint _ _)).symm
  have h2 : 0 ≤ ∫ s in (0 : ℝ)..t, avgModulus η s :=
    integral_nonneg ht.le fun s _ ↦ avgModulus_nonneg h0 s
  have h3 : ∫ s in t..2 * t, avgModulus η t ≤ ∫ s in t..2 * t, avgModulus η s :=
    integral_mono_on (by linarith) (by simp) (hint _ _) fun s hs ↦
      avgModulus_monotoneOn hmono (mem_Ici.2 ht.le) (mem_Ici.2 (by linarith [hs.1])) hs.1
  have h4 : ∫ s in t..2 * t, avgModulus η t = t * avgModulus η t := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have h5 := le_avgModulus hmono ht.le
  unfold convexMajorant
  nlinarith

end

end VariationalAnalysis
