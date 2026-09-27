/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import Mathlib.Topology.Order.Rolle
import VariationalAnalysis.Subdifferential.ChainRule
import VariationalAnalysis.Subdifferential.Characterizations

/-!
# Symmetric subdifferential mean value theorem

The upper and symmetric subdifferentials of [Mordukhovich 2018, Exercises 1.75, 1.76],

  `∂⁺φ(x̄) = -∂(-φ)(x̄)`, `∂^{∞,+}φ(x̄) = -∂^∞(-φ)(x̄)`   (1.74),
  `∂⁰φ(x̄) = ∂φ(x̄) ∪ ∂⁺φ(x̄)`, `∂^{∞,0}φ(x̄) = ∂^∞φ(x̄) ∪ ∂^{∞,+}φ(x̄)`   (1.75), (4.18),
  `∂̂⁺φ(x̄) = -∂̂(-φ)(x̄)`   (1.76),

and the mean value theorems of [Mordukhovich 2018, Section 4.4.1] for continuous and Lipschitz
functions.

## Main results

* `upperRegularSubdiff`, `upperSubdiff`, `upperSingularSubdiff`, `symmSubdiff`,
  `symmSingularSubdiff`: (1.74)–(1.76), (4.18) of [Mordukhovich 2018].
* `exists_mem_subdiff_of_mem_subdiff_comp_line`: Cor. 4.6 of [Mordukhovich 2018] (chain rule,
  `subdiff_comp_lipschitz_subset`) for the affine inner map `t ↦ a + t (b - a)` from `ℝ` to `E`.
* `exists_mem_regularSubdiff_line`: (4.20) of [Mordukhovich 2018] (proof of Thm. 4.11).
* `symmetric_mean_value`: Thm. 4.11 of [Mordukhovich 2018] (symmetric subdifferential mean
  value theorem for continuous functions), (4.19).
* `symmetric_mean_value_of_lipschitz`, `mean_value_of_lipschitz_of_lowerRegular`: Cor. 4.12 of
  [Mordukhovich 2018], (4.19) and (4.21).

## Remarks on the book

* For (4.21) the book derives the lower regularity of `φ ∘ g` from Thm. 4.5(i). Here a local
  maximum of the auxiliary function gives an upper regular subgradient `φ(b) - φ(a)` of `φ ∘ g`,
  and the pullback `⟨v, b - a⟩ ∈ ∂̂(φ ∘ g)(θ)` of some `v ∈ ∂̂φ(c) = ∂φ(c) ≠ ∅`
  (`regularSubdiff_comp_line`) coincides with it (Exercise 1.76).
-/

open Filter Topology Set Metric
open scoped Pointwise NNReal

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Definitions

/-- The upper regular subdifferential `∂̂⁺φ(x₀) = -∂̂(-φ)(x₀)` [Mordukhovich 2018, (1.76)]. -/
def upperRegularSubdiff (φ : E → EReal) (x₀ : E) : Set (StrongDual ℝ E) :=
  -regularSubdiff (fun x ↦ -φ x) x₀

/-- The upper subdifferential `∂⁺φ(x₀) = -∂(-φ)(x₀)` [Mordukhovich 2018, (1.74)]. -/
def upperSubdiff (φ : E → EReal) (x₀ : E) : Set (StrongDual ℝ E) :=
  -subdiff (fun x ↦ -φ x) x₀

/-- The upper singular subdifferential `∂^{∞,+}φ(x₀) = -∂^∞(-φ)(x₀)`
[Mordukhovich 2018, (1.74)]. -/
def upperSingularSubdiff (φ : E → EReal) (x₀ : E) : Set (StrongDual ℝ E) :=
  -singularSubdiff (fun x ↦ -φ x) x₀

/-- The symmetric subdifferential `∂⁰φ(x₀) = ∂φ(x₀) ∪ ∂⁺φ(x₀)` [Mordukhovich 2018, (1.75),
(4.18)]. -/
def symmSubdiff (φ : E → EReal) (x₀ : E) : Set (StrongDual ℝ E) :=
  subdiff φ x₀ ∪ upperSubdiff φ x₀

/-- The symmetric singular subdifferential `∂^{∞,0}φ(x₀) = ∂^∞φ(x₀) ∪ ∂^{∞,+}φ(x₀)`
[Mordukhovich 2018, (1.75)]. -/
def symmSingularSubdiff (φ : E → EReal) (x₀ : E) : Set (StrongDual ℝ E) :=
  singularSubdiff φ x₀ ∪ upperSingularSubdiff φ x₀

variable {φ : E → EReal} {x₀ : E} {v : StrongDual ℝ E}

/-- `v ∈ ∂⁺φ(x₀)` iff `-v ∈ ∂(-φ)(x₀)`. -/
theorem mem_upperSubdiff_iff : v ∈ upperSubdiff φ x₀ ↔ -v ∈ subdiff (fun x ↦ -φ x) x₀ :=
  Set.mem_neg

/-- `v ∈ ∂^{∞,+}φ(x₀)` iff `-v ∈ ∂^∞(-φ)(x₀)`. -/
theorem mem_upperSingularSubdiff_iff :
    v ∈ upperSingularSubdiff φ x₀ ↔ -v ∈ singularSubdiff (fun x ↦ -φ x) x₀ :=
  Set.mem_neg

/-- `v ∈ ∂̂⁺φ(x₀)` iff `-v ∈ ∂̂(-φ)(x₀)`. -/
theorem mem_upperRegularSubdiff_iff :
    v ∈ upperRegularSubdiff φ x₀ ↔ -v ∈ regularSubdiff (fun x ↦ -φ x) x₀ :=
  Set.mem_neg

/-- Exercise 1.76 of [Mordukhovich 2018]: a regular subgradient and an upper regular subgradient
at the same point coincide. -/
theorem eq_of_mem_regularSubdiff_of_mem_upperRegularSubdiff {u w : StrongDual ℝ E}
    (hu : u ∈ regularSubdiff φ x₀) (hw : w ∈ upperRegularSubdiff φ x₀) : u = w :=
  eq_of_mem_regularSubdiff_of_neg_mem hu (mem_upperRegularSubdiff_iff.1 hw)

end Definitions

section Line

variable {a b : E}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- `-f` as an extended-real-valued function. -/
theorem coe_neg_fun (f : E → ℝ) :
    (fun y ↦ -((f y : ℝ) : EReal)) = fun y ↦ (((-f) y : ℝ) : EReal) := by
  funext y; simp

/-- `t ↦ ⟨v, a + t (b - a)⟩` has derivative `⟨v, b - a⟩`. -/
theorem hasFDerivAt_dual_line (v : StrongDual ℝ E) (t : ℝ) :
    HasFDerivAt (fun t : ℝ ↦ v (a + t • (b - a)))
      (ContinuousLinearMap.toSpanSingleton ℝ (v (b - a))) t := by
  have h : HasDerivAt (fun t : ℝ ↦ v a + t * v (b - a)) (v (b - a)) t := by
    simpa using ((hasDerivAt_id t).mul_const (v (b - a))).const_add (v a)
  refine h.hasFDerivAt.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ ?_)
  simp [map_add, map_smul]

/-- `∂⟨v, g⟩(t) = {⟨v, b - a⟩}` for the affine map `g(t) = a + t (b - a)`. -/
theorem subdiff_dual_line (v : StrongDual ℝ E) (t : ℝ) :
    subdiff (fun t : ℝ ↦ ((v (a + t • (b - a)) : ℝ) : EReal)) t =
      {ContinuousLinearMap.toSpanSingleton ℝ (v (b - a))} :=
  subdiff_of_hasFDerivAt_of_continuousAt
    (f' := fun _ ↦ ContinuousLinearMap.toSpanSingleton ℝ (v (b - a)))
    (Eventually.of_forall fun s ↦ hasFDerivAt_dual_line v s) continuousAt_const

omit [NormedSpace ℝ E] in
/-- The derivative `t ↦ t c` evaluated at `1`. -/
theorem toSpanSingleton_apply_one (c : ℝ) : ContinuousLinearMap.toSpanSingleton ℝ c 1 = c := by
  simp

/-- The affine map `t ↦ a + t (b - a)` is Lipschitz. -/
theorem lipschitzWith_line : LipschitzWith ‖b - a‖₊ (fun t : ℝ ↦ a + t • (b - a)) :=
  LipschitzWith.of_dist_le_mul fun s t ↦ by
    rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul,
      coe_nnnorm, mul_comm]

/-- Regular subgradients pull back along the affine map `g(t) = a + t (b - a)`: if
`v ∈ ∂̂ψ(g θ)`, then `⟨v, b - a⟩ ∈ ∂̂(ψ ∘ g)(θ)`. -/
theorem regularSubdiff_comp_line {ψ : E → EReal} {θ : ℝ} {v : StrongDual ℝ E}
    (hv : v ∈ regularSubdiff ψ (a + θ • (b - a))) :
    ContinuousLinearMap.toSpanSingleton ℝ (v (b - a)) ∈
      regularSubdiff (fun t ↦ ψ (a + t • (b - a))) θ := by
  obtain ⟨r, hr, hv⟩ := hv
  refine ⟨r, hr, fun ε hε ↦ ?_⟩
  have hε' : 0 < ε / (‖b - a‖ + 1) := by positivity
  have hg : Tendsto (fun t : ℝ ↦ a + t • (b - a)) (𝓝 θ) (𝓝 (a + θ • (b - a))) :=
    (continuous_const.add (continuous_id.smul continuous_const)).tendsto θ
  filter_upwards [hg.eventually (hv _ hε')] with t ht
  refine le_trans (EReal.coe_le_coe_iff.2 ?_) ht
  rw [add_sub_add_left_eq_sub, ← sub_smul, map_smul, smul_eq_mul, norm_smul,
    Real.norm_eq_abs]
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  have h1 : ε / (‖b - a‖ + 1) * (|t - θ| * ‖b - a‖) ≤ ε * |t - θ| := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [abs_nonneg (t - θ), norm_nonneg (b - a), mul_nonneg hε.le (abs_nonneg (t - θ))]
  linarith

variable [FiniteDimensional ℝ E]

/-- Cor. 4.6 of [Mordukhovich 2018] for the affine inner map `g(t) = a + t (b - a)` from `ℝ` to
`E`: if `ψ` is finite at `g θ` with epigraph locally closed there, and
`∂^∞ψ(g θ) ∩ (b - a)^⊥ = {0}`, then every `s ∈ ∂(ψ ∘ g)(θ)` is `s = ⟨v, b - a⟩` for some
`v ∈ ∂ψ(g θ)`. -/
theorem exists_mem_subdiff_of_mem_subdiff_comp_line {ψ : E → EReal} {θ r : ℝ}
    (hr : ψ (a + θ • (b - a)) = r)
    (hψ : ∃ ρ > 0, IsClosed (ψ.Epi univ ∩ closedBall ((a + θ • (b - a), r) : E × ℝ) ρ))
    (hqc : ∀ v ∈ singularSubdiff ψ (a + θ • (b - a)), v (b - a) = 0 → v = 0)
    {s : StrongDual ℝ ℝ} (hs : s ∈ subdiff (fun t ↦ ψ (a + t • (b - a))) θ) :
    ∃ v ∈ subdiff ψ (a + θ • (b - a)), s 1 = v (b - a) := by
  have h := subdiff_comp_lipschitz_subset (g := fun t : ℝ ↦ a + t • (b - a)) (x₀ := θ)
    (U := univ) univ_mem lipschitzWith_line.lipschitzOnWith hr hψ (fun v hv h0 ↦ by
      rw [subdiff_dual_line, mem_singleton_iff] at h0
      have := congrArg (fun ℓ : StrongDual ℝ ℝ ↦ ℓ 1) h0
      simp only [zero_apply, toSpanSingleton_apply_one] at this
      exact hqc v hv this.symm) hs
  obtain ⟨v, hv, hsv⟩ := mem_iUnion₂.1 h
  rw [subdiff_dual_line, mem_singleton_iff] at hsv
  exact ⟨v, hv, by rw [hsv, toSpanSingleton_apply_one]⟩

end Line

section MeanValue

variable [FiniteDimensional ℝ E] {a b : E} {f : E → ℝ} {U : Set E}

omit [FiniteDimensional ℝ E] in
/-- The first step of the proof of Thm. 4.11 of [Mordukhovich 2018], (4.20): if `f` is continuous
on a set `U ⊇ [a, b]`, there is `θ ∈ (0, 1)` such that `f(b) - f(a)` is a regular
subgradient or an upper regular subgradient of `t ↦ f(a + t (b - a))` at `θ` (Rolle's theorem
for `t ↦ f(a + t (b - a)) + t (f(a) - f(b))`, the Fermat rule, and the sum rule with a smooth
function). -/
theorem exists_mem_regularSubdiff_line (hsub : segment ℝ a b ⊆ U) (hf : ContinuousOn f U) :
    ∃ θ ∈ Ioo (0 : ℝ) 1,
      ContinuousLinearMap.toSpanSingleton ℝ (f b - f a) ∈
          regularSubdiff (fun t ↦ ((f (a + t • (b - a)) : ℝ) : EReal)) θ ∨
        ContinuousLinearMap.toSpanSingleton ℝ (f b - f a) ∈
          upperRegularSubdiff (fun t ↦ ((f (a + t • (b - a)) : ℝ) : EReal)) θ := by
  set h : ℝ → ℝ := fun t ↦ f (a + t • (b - a)) + t * (f a - f b) with hh
  have hcont : ContinuousOn h (Icc 0 1) := by
    refine (hf.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
      fun t ht ↦ hsub (add_smul_sub_mem_segment ht.1 ht.2)).add ?_
    exact (continuous_id.mul continuous_const).continuousOn
  have hends : h 0 = h 1 := by
    simp only [hh, zero_smul, add_zero, zero_mul, one_smul, add_sub_cancel, one_mul]
  obtain ⟨θ, hθ, hext⟩ := exists_isLocalExtr_Ioo zero_lt_one hcont hends
  refine ⟨θ, hθ, ?_⟩
  have hder : ∀ c : ℝ, HasFDerivAt (fun t : ℝ ↦ t * c) (ContinuousLinearMap.toSpanSingleton ℝ c)
      θ := fun c ↦ by simpa using ((hasDerivAt_id θ).mul_const c).hasFDerivAt
  rcases hext with hmin | hmax
  · left
    have hmin' : IsLocalMin (fun t ↦ ((f (a + t • (b - a)) : ℝ) : EReal) +
        ((t * (f a - f b) : ℝ) : EReal)) θ :=
      Filter.Eventually.mono hmin fun t ht ↦ by
        simp only
        rw [← EReal.coe_add, ← EReal.coe_add]; exact EReal.coe_le_coe_iff.2 ht
    have h0 := zero_mem_regularSubdiff_of_isLocalMin hmin' (r := h θ)
      (by simp only [hh, EReal.coe_add])
    have := (mem_regularSubdiff_add_iff (hder (f a - f b))).1 h0
    convert this using 1
    ext; simp
  · right
    rw [mem_upperRegularSubdiff_iff]
    have hmin' : IsLocalMin (fun t ↦ -((f (a + t • (b - a)) : ℝ) : EReal) +
        ((t * (f b - f a) : ℝ) : EReal)) θ :=
      Filter.Eventually.mono hmax fun t ht ↦ by
        simp only
        rw [← EReal.coe_neg, ← EReal.coe_neg, ← EReal.coe_add, ← EReal.coe_add]
        refine EReal.coe_le_coe_iff.2 ?_
        simp only [hh] at ht
        linarith
    have h0 := zero_mem_regularSubdiff_of_isLocalMin hmin' (r := -h θ)
      (by simp only [hh, ← EReal.coe_neg, ← EReal.coe_add]; congr 1; ring)
    have := (mem_regularSubdiff_add_iff (hder (f b - f a))).1 h0
    rwa [zero_sub] at this

/-- Thm. 4.11 of [Mordukhovich 2018] (symmetric subdifferential mean value theorem for continuous
functions): let `f` be continuous on an open set `U ⊇ [a, b]` and assume the qualification
condition `∂^{∞,0}f(x) ∩ (b - a)^⊥ = {0}` for every `x ∈ (a, b)`. Then
`f(b) - f(a) ∈ ⟨∂⁰f(c), b - a⟩` for some `c ∈ (a, b)` (4.19). Here `∂⁰` and `∂^{∞,0}` are the
symmetric subdifferentials (1.75). The chain rule of Cor. 4.6 is applied to the affine map
`t ↦ a + t (b - a)` (`exists_mem_subdiff_of_mem_subdiff_comp_line`). -/
theorem symmetric_mean_value (hU : IsOpen U) (hsub : segment ℝ a b ⊆ U) (hf : ContinuousOn f U)
    (hqc : ∀ x ∈ openSegment ℝ a b, ∀ v ∈ symmSingularSubdiff (fun y ↦ (f y : EReal)) x,
      v (b - a) = 0 → v = 0) :
    ∃ c ∈ openSegment ℝ a b, ∃ v ∈ symmSubdiff (fun y ↦ (f y : EReal)) c,
      f b - f a = v (b - a) := by
  rcases eq_or_ne a b with rfl | hab
  · -- `(a, a) = {a}`: the qualification condition gives `∂^∞f(a) = {0}` (Thm. 1.22)
    have haU : U ∈ 𝓝 a := hU.mem_nhds (hsub (left_mem_segment ℝ a a))
    have hmem : a ∈ openSegment ℝ a a := by rw [openSegment_same]; exact mem_singleton a
    obtain ⟨V, hV, L, g, hg, hL⟩ := exists_lipschitzOnWith_of_singularSubdiff
      (φ := fun y ↦ (f y : EReal)) rfl
      (eventually_of_mem haU fun y hy ↦ (continuous_coe_real_ereal.continuousAt.comp
        (hf.continuousAt (hU.mem_nhds hy))).lowerSemicontinuousAt)
      fun v hv ↦ hqc a hmem v (Or.inl hv) (by rw [sub_self, map_zero])
    obtain ⟨v, hv⟩ := (subdiff_nonempty_and_norm_le_of_eqOn_lipschitz hV hg hL).1
    exact ⟨a, hmem, v, Or.inl hv, by rw [sub_self, sub_self, map_zero]⟩
  obtain ⟨θ, hθ, hcase⟩ := exists_mem_regularSubdiff_line hsub hf
  set c := a + θ • (b - a) with hcdef
  have hc : c ∈ openSegment ℝ a b := by rw [openSegment_eq_image']; exact ⟨θ, hθ, rfl⟩
  have hcU : U ∈ 𝓝 c := hU.mem_nhds (hsub (openSegment_subset_segment ℝ a b hc))
  rcases hcase with hmin | hmax
  · obtain ⟨v, hv, hsv⟩ := exists_mem_subdiff_of_mem_subdiff_comp_line (ψ := fun y ↦ (f y : EReal))
      (θ := θ) (r := f c) rfl (locallyClosed_epi_of_continuousOn hcU hf (f c))
      (fun v hv h0 ↦ hqc c hc v (Or.inl hv) h0) (regularSubdiff_subset_subdiff hmin)
    rw [toSpanSingleton_apply_one] at hsv
    exact ⟨c, hc, v, Or.inl hv, hsv⟩
  · rw [mem_upperRegularSubdiff_iff] at hmax
    have hloc := locallyClosed_epi_of_continuousOn hcU hf.neg (-f c)
    rw [← coe_neg_fun] at hloc
    obtain ⟨v, hv, hsv⟩ := exists_mem_subdiff_of_mem_subdiff_comp_line
      (ψ := fun y ↦ -((f y : ℝ) : EReal)) (θ := θ) (r := -f c) (by simp [hcdef]) hloc
      (fun v hv h0 ↦ by
        have := hqc c hc (-v) (Or.inr (by rw [mem_upperSingularSubdiff_iff, neg_neg]; exact hv))
          (by rw [neg_apply, h0, neg_zero])
        rwa [neg_eq_zero] at this)
      (regularSubdiff_subset_subdiff hmax)
    rw [neg_apply, toSpanSingleton_apply_one] at hsv
    refine ⟨c, hc, -v, Or.inr (by rw [mem_upperSubdiff_iff, neg_neg]; exact hv), ?_⟩
    rw [neg_apply]
    linarith

/-- Cor. 4.12 of [Mordukhovich 2018] (symmetric subdifferential mean value theorem for Lipschitz
functions), first part: if `f` is Lipschitz on an open set `U ⊇ [a, b]`, then (4.19) holds: the
qualification condition of Thm. 4.11 is automatic by Thm. 1.22. -/
theorem symmetric_mean_value_of_lipschitz {L : ℝ≥0} (hU : IsOpen U) (hsub : segment ℝ a b ⊆ U)
    (hL : LipschitzOnWith L f U) :
    ∃ c ∈ openSegment ℝ a b, ∃ v ∈ symmSubdiff (fun y ↦ (f y : EReal)) c,
      f b - f a = v (b - a) := by
  refine symmetric_mean_value hU hsub hL.continuousOn fun x hx v hv _ ↦ ?_
  have hxU : U ∈ 𝓝 x := hU.mem_nhds (hsub (openSegment_subset_segment ℝ a b hx))
  rcases hv with hv | hv
  · rwa [singularSubdiff_eq_zero_of_lipschitz hxU hL] at hv
  · rw [mem_upperSingularSubdiff_iff, coe_neg_fun,
      singularSubdiff_eq_zero_of_lipschitz hxU hL.neg, mem_singleton_iff, neg_eq_zero] at hv
    exact hv

/-- Cor. 4.12 of [Mordukhovich 2018], second part, (4.21): if `f` is Lipschitz on an open set
`U ⊇ [a, b]` and lower regular (`∂f(x) = ∂̂f(x)`) at every `x ∈ (a, b)`, then
`f(b) - f(a) ∈ ⟨∂f(c), b - a⟩` for some `c ∈ (a, b)`. At a local maximum of the auxiliary
function, lower regularity and Thm. 1.22 give a regular subgradient `v ∈ ∂̂f(c)`, and
`⟨v, b - a⟩ ∈ ∂̂(f ∘ g)(θ)` coincides with the upper regular subgradient `f(b) - f(a)`
(Exercise 1.76); this replaces the book's appeal to Thm. 4.5(i). -/
theorem mean_value_of_lipschitz_of_lowerRegular {L : ℝ≥0} (hU : IsOpen U)
    (hsub : segment ℝ a b ⊆ U) (hL : LipschitzOnWith L f U)
    (hreg : ∀ x ∈ openSegment ℝ a b, LowerRegularAt (fun y ↦ (f y : EReal)) x) :
    ∃ c ∈ openSegment ℝ a b, ∃ v ∈ subdiff (fun y ↦ (f y : EReal)) c, f b - f a = v (b - a) := by
  rcases eq_or_ne a b with rfl | hab
  · have hmem : a ∈ openSegment ℝ a a := by rw [openSegment_same]; exact mem_singleton a
    obtain ⟨v, hv⟩ := subdiff_nonempty_of_lipschitz
      (hU.mem_nhds (hsub (left_mem_segment ℝ a a))) hL
    exact ⟨a, hmem, v, hv, by rw [sub_self, sub_self, map_zero]⟩
  obtain ⟨θ, hθ, hcase⟩ := exists_mem_regularSubdiff_line hsub hL.continuousOn
  set c := a + θ • (b - a) with hcdef
  have hc : c ∈ openSegment ℝ a b := by rw [openSegment_eq_image']; exact ⟨θ, hθ, rfl⟩
  have hcU : U ∈ 𝓝 c := hU.mem_nhds (hsub (openSegment_subset_segment ℝ a b hc))
  rcases hcase with hmin | hmax
  · obtain ⟨v, hv, hsv⟩ := exists_mem_subdiff_of_mem_subdiff_comp_line (ψ := fun y ↦ (f y : EReal))
      (θ := θ) (r := f c) rfl (locallyClosed_epi_of_continuousOn hcU hL.continuousOn (f c))
      (fun v hv _ ↦ by rwa [singularSubdiff_eq_zero_of_lipschitz hcU hL] at hv)
      (regularSubdiff_subset_subdiff hmin)
    rw [toSpanSingleton_apply_one] at hsv
    exact ⟨c, hc, v, hv, hsv⟩
  · obtain ⟨v, hv⟩ := subdiff_nonempty_of_lipschitz hcU hL
    have hv' : v ∈ regularSubdiff (fun y ↦ (f y : EReal)) c := by
      rw [← hreg c hc]; exact hv
    have heq := eq_of_mem_regularSubdiff_of_mem_upperRegularSubdiff
      (regularSubdiff_comp_line (ψ := fun y ↦ (f y : EReal)) hv') hmax
    have := congrArg (fun ℓ : StrongDual ℝ ℝ ↦ ℓ 1) heq
    simp only [toSpanSingleton_apply_one] at this
    exact ⟨c, hc, v, hv, this.symm⟩

end MeanValue

end VariationalAnalysis
