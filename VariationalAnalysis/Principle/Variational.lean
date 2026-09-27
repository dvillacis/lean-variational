/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import VariationalAnalysis.Subdifferential.Regular

/-!
# Variational principles

The general variational principle in finite dimensions and Ekeland's variational principle
[Mordukhovich 2018, Section 2.3.1], and their applications to fixed points
[Mordukhovich 2018, Section 2.3.2].

Throughout, `φ : E → EReal` is lower semicontinuous and bounded below (`∃ m : ℝ, ∀ x, m ≤ φ x`),
`x₀` is a point where `φ` is finite, and `θ : E → ℝ` is a lower semicontinuous perturbation with
`θ x → ∞` as `‖x‖ → ∞`, written `Tendsto θ (cocompact E) atTop`. In a finite-dimensional space
this is exactly the growth condition of the book; since the only use of finite dimensions is the
compactness of the sublevel sets of `θ`, which this hypothesis encodes, the general principle is
stated in any real normed space. The book's parameters `ε, λ > 0` are `ε, ρ > 0` here (`λ` is a
keyword), and the suboptimality `φ x₀ ≤ inf φ + ε` is `φ x₀ ≤ (⨅ x, φ x) + ε`.
Inequalities such as (2.20) are written with the real perturbations coerced to `EReal` and added
on both sides, which avoids subtracting infinite values.

## Main results

* `exists_forall_add_le_add`, `general_variational_principle`,
  `general_variational_principle_subadditive`: Thm. 2.12 of [Mordukhovich 2018] (general
  variational principle), (2.20)–(2.21).
* `ekeland_variational_principle`: Cor. 2.13 of [Mordukhovich 2018] (Ekeland's variational
  principle), [Clason–Valkonen, Thm. 2.17] in finite dimensions.
* `norm_le_of_forall_le_add_norm`, `norm_le_of_hasFDerivAt_of_forall_le_add_norm`: the almost
  stationarity condition (2.24) of [Mordukhovich 2018], for upper regular subgradients
  `v ∈ ∂̂⁺φ(x̄) = -∂̂(-φ)(x̄)` and for derivatives, in any normed space.
* `ekeland_almost_stationary`: Cor. 2.13 with (2.24), and the second (upper) part of Thm. 2.14 of
  [Mordukhovich 2018] with the book's bound `‖x̄ - x₀‖ ≤ λ`.
* `exists_fixedPoint_of_variational`, `exists_mem_self_of_variational`,
  `exists_eq_singleton_of_variational`: Prop. 2.15 of [Mordukhovich 2018] (fixed points).

The first part of Thm. 2.14 and Exercise 2.25(iii) are in
`VariationalAnalysis.Principle.AlmostStationary`.

## Remarks on the book

* In Thm. 2.12, the strict form of (2.21) does not follow from (2.21) for an arbitrary minimizer
  `x̄` of (2.22), as the book claims: for `φ = max (-|·|) (-1)` on `ℝ`, `θ = |·|`, `ε = λ = 1`,
  `x₀ = 0`, every point of `[-1, 1]` minimizes (2.22) and `x̄ = 0` gives equality in (2.21) for
  all `x ∈ [-1, 1]`. The statement is true for a minimizer of `φ` over the (compact) set of
  minimizers of (2.22); this is the `x̄` constructed here.
* Prop. 2.15 uses (2.21), hence needs `θ` subadditive; this hypothesis, missing from the book's
  statement, is added.
-/

open Filter Topology Set Metric

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {φ : E → EReal} {θ : E → ℝ} {x₀ : E} {ε ρ c : ℝ}

section Auxiliary

/-- An extended real that is bounded below by a real number and is not `⊤` is a real number. -/
theorem exists_coe_eq_of_ne_top {m : ℝ} {y : EReal} (hm : (m : EReal) ≤ y) (ht : y ≠ ⊤) :
    ∃ b : ℝ, y = b :=
  ⟨y.toReal, (EReal.coe_toReal ht (ne_bot_of_le_ne_bot (EReal.coe_ne_bot m) hm)).symm⟩

/-- Moving real perturbations across an `EReal` inequality: if `y + r ≤ z + s` and
`s ≤ r + t`, then `y ≤ z + t`. -/
theorem le_add_coe_of_add_coe_le_add_coe {y z : EReal} {r s t : ℝ}
    (h : y + r ≤ z + s) (hst : s ≤ r + t) : y ≤ z + t := by
  induction y with
  | bot => exact bot_le
  | top =>
    have hz : z = ⊤ := by
      by_contra hz
      have : z + s ≠ ⊤ := EReal.add_ne_top hz (EReal.coe_ne_top s)
      exact this (top_le_iff.1 (by simpa using h))
    simp [hz]
  | coe y =>
    rw [← EReal.coe_add, coe_le_add_coe_iff] at h
    rw [coe_le_add_coe_iff]
    exact le_trans (EReal.coe_le_coe_iff.2 (by linarith)) h

omit [NormedSpace ℝ E] in
/-- The perturbed function `φ + c θ(· - x₀)` of (2.22) is lower semicontinuous. -/
theorem lowerSemicontinuous_add_perturbation (hφ : LowerSemicontinuous φ)
    (hθ : LowerSemicontinuous θ) (hc : 0 ≤ c) (x₀ : E) :
    LowerSemicontinuous fun x ↦ φ x + ((c * θ (x - x₀) : ℝ) : EReal) := by
  have h1 : LowerSemicontinuous fun x ↦ ((c * θ (x - x₀) : ℝ) : EReal) :=
    Continuous.comp_lowerSemicontinuous (g := fun t : ℝ ↦ ((c * t : ℝ) : EReal))
      (continuous_coe_real_ereal.comp (continuous_const.mul continuous_id))
      (hθ.comp (continuous_id.sub continuous_const))
      (fun s t hst ↦ EReal.coe_le_coe_iff.2 (mul_le_mul_of_nonneg_left hst hc))
  exact hφ.add' h1 fun x ↦
    EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The suboptimality condition `φ x₀ ≤ inf φ + ε` gives `φ x₀ ≤ φ x + ε` for every `x`. -/
theorem le_add_of_le_iInf_add (hsub : φ x₀ ≤ (⨅ x, φ x) + ε) (x : E) : φ x₀ ≤ φ x + ε :=
  hsub.trans (add_le_add_left (iInf_le _ x) _)

omit [NormedSpace ℝ E] in
/-- Weierstrass step in the proof of Thm. 2.12 of [Mordukhovich 2018]: the perturbed function
`ψ = φ + c θ(· - x₀)` of (2.22) attains its minimum, and a minimizer `x̄` can be chosen to
minimize `φ` among all minimizers of `ψ`. -/
theorem exists_lex_minimizer (hφ : LowerSemicontinuous φ)
    (hbdd : ∃ m : ℝ, ∀ x, (m : EReal) ≤ φ x) (hθ : LowerSemicontinuous θ)
    (hθc : Tendsto θ (cocompact E) atTop) (hc : 0 < c) (hx₀ : φ x₀ ≠ ⊤) :
    ∃ z, (∀ x, φ z + ((c * θ (z - x₀) : ℝ) : EReal) ≤ φ x + ((c * θ (x - x₀) : ℝ) : EReal)) ∧
      ∀ x, φ x + ((c * θ (x - x₀) : ℝ) : EReal) ≤ φ z + ((c * θ (z - x₀) : ℝ) : EReal) →
        φ z ≤ φ x := by
  obtain ⟨m, hm⟩ := hbdd
  obtain ⟨a, ha⟩ := exists_coe_eq_of_ne_top (hm x₀) hx₀
  set ψ : E → EReal := fun x ↦ φ x + ((c * θ (x - x₀) : ℝ) : EReal) with hψ_def
  have hψ : LowerSemicontinuous ψ := lowerSemicontinuous_add_perturbation hφ hθ hc.le x₀
  set M : ℝ := (a + c * θ 0 - m) / c with hM
  obtain ⟨t, ht, htM⟩ := mem_cocompact.1 (hθc.eventually (eventually_gt_atTop M))
  set K : Set E := insert x₀ ((fun y ↦ y + x₀) '' t)
  have hK : IsCompact K := (ht.image (continuous_id.add continuous_const)).insert x₀
  have hout : ∀ x ∉ K, ψ x₀ < ψ x := by
    intro x hx
    have hxt : x - x₀ ∉ t := fun h ↦ hx (mem_insert_of_mem _ ⟨x - x₀, h, sub_add_cancel x x₀⟩)
    have hθx : M < θ (x - x₀) := htM hxt
    have h1 : ψ x₀ = ((a + c * θ 0 : ℝ) : EReal) := by simp [ψ, ha]
    have h2 : ((m + c * θ (x - x₀) : ℝ) : EReal) ≤ ψ x := by
      rw [EReal.coe_add]; exact add_le_add_left (hm x) _
    rw [h1]
    refine lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 ?_) h2
    have hcM : c * M = a + c * θ 0 - m := by rw [hM]; field_simp
    nlinarith [mul_lt_mul_of_pos_left hθx hc]
  obtain ⟨x₁, -, hx₁⟩ := (hψ.lowerSemicontinuousOn K).exists_isMinOn ⟨x₀, mem_insert _ _⟩ hK
  have hmin₁ : ∀ x, ψ x₁ ≤ ψ x := fun x ↦ by
    by_cases hx : x ∈ K
    · exact hx₁ hx
    · exact (hx₁ (mem_insert _ _)).trans (hout x hx).le
  set S := ψ ⁻¹' Iic (ψ x₁)
  have hSK : S ⊆ K := fun x hx ↦ by
    by_contra h
    exact absurd ((hx₁ (mem_insert _ _)).trans_lt (hout x h)) (not_lt.2 hx)
  have hS : IsCompact S := hK.of_isClosed_subset (hψ.isClosed_preimage _) hSK
  obtain ⟨z, hzS, hz⟩ :=
    (hφ.lowerSemicontinuousOn S).exists_isMinOn ⟨x₁, show ψ x₁ ≤ ψ x₁ from le_rfl⟩ hS
  have hzS' : ψ z ≤ ψ x₁ := hzS
  exact ⟨z, fun x ↦ hzS'.trans (hmin₁ x),
    fun x hx ↦ hz (show ψ x ≤ ψ x₁ from hx.trans hzS')⟩

omit [NormedSpace ℝ E] in
/-- The estimates of Thm. 2.12 of [Mordukhovich 2018] for `θ 0 = 0`, from (2.20) at `x = x₀` and
the suboptimality of `x₀`. -/
theorem le_and_le_of_forall_add_le_add {m : ℝ} {z : E} (hm : ∀ x, (m : EReal) ≤ φ x)
    (hθnn : ∀ x, 0 ≤ θ x) (hθ0 : θ 0 = 0) (hε : 0 < ε) (hρ : 0 < ρ) (hx₀ : φ x₀ ≠ ⊤)
    (hsub : φ x₀ ≤ (⨅ x, φ x) + ε)
    (h : ∀ x, φ z + ((ε / ρ * θ (z - x₀) : ℝ) : EReal) ≤ φ x + ((ε / ρ * θ (x - x₀) : ℝ) : EReal)) :
    φ z ≤ φ x₀ ∧ θ (z - x₀) ≤ ρ := by
  have hr : 0 ≤ ε / ρ * θ (z - x₀) := mul_nonneg (div_pos hε hρ).le (hθnn _)
  have h0 : φ z + ((ε / ρ * θ (z - x₀) : ℝ) : EReal) ≤ φ x₀ := by
    have := h x₀
    rwa [sub_self, hθ0, mul_zero, EReal.coe_zero, add_zero] at this
  have hle : φ z ≤ φ x₀ := by
    have := le_add_coe_of_add_coe_le_add_coe (y := φ z) (z := φ x₀) (s := 0) (t := 0)
      (by rwa [EReal.coe_zero, add_zero]) (by linarith : (0 : ℝ) ≤ ε / ρ * θ (z - x₀) + 0)
    rwa [EReal.coe_zero, add_zero] at this
  refine ⟨hle, ?_⟩
  obtain ⟨b, hb⟩ := exists_coe_eq_of_ne_top (hm z) (ne_top_of_le_ne_top hx₀ hle)
  have h1 := h0.trans (le_add_of_le_iInf_add hsub z)
  rw [hb, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
  have h2 : ε / ρ * θ (z - x₀) * ρ ≤ ε * ρ := by nlinarith
  rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hρ.ne'] at h2
  exact le_of_mul_le_mul_left h2 hε

omit [NormedSpace ℝ E] in
/-- Strict inequality in (2.21) for the minimizer built in `exists_lex_minimizer`. -/
theorem lt_add_of_lex_minimizer {m : ℝ} {z : E} (hm : ∀ x, (m : EReal) ≤ φ x) (hc : 0 < c)
    (hθnn : ∀ x, 0 ≤ θ x) (hθadd : ∀ x y, θ (x + y) ≤ θ x + θ y) (hθz : ∀ x, θ x = 0 → x = 0)
    (hz : φ z ≠ ⊤)
    (h2 : ∀ x, φ x + ((c * θ (x - x₀) : ℝ) : EReal) ≤ φ z + ((c * θ (z - x₀) : ℝ) : EReal) →
      φ z ≤ φ x) {x : E} (hx : x ≠ z) :
    φ z < φ x + ((c * θ (x - z) : ℝ) : EReal) := by
  obtain ⟨b, hb⟩ := exists_coe_eq_of_ne_top (hm z) hz
  have hθpos : 0 < θ (x - z) :=
    lt_of_le_of_ne (hθnn _) fun h ↦ hx (sub_eq_zero.1 (hθz _ h.symm))
  have hsub : θ (x - x₀) ≤ θ (x - z) + θ (z - x₀) := by
    simpa using hθadd (x - z) (z - x₀)
  induction hφx : φ x with
  | bot => exact absurd (hφx ▸ hm x) (by simp)
  | top => rw [hb, EReal.top_add_coe]; exact EReal.coe_lt_top b
  | coe a =>
    rw [hb, ← EReal.coe_add, EReal.coe_lt_coe_iff]
    by_cases hle : a + c * θ (x - x₀) ≤ b + c * θ (z - x₀)
    · have := h2 x (by rw [hφx, hb, ← EReal.coe_add, ← EReal.coe_add]; exact_mod_cast hle)
      rw [hφx, hb, EReal.coe_le_coe_iff] at this
      nlinarith
    · nlinarith

end Auxiliary

section General

omit [NormedSpace ℝ E] in
/-- Thm. 2.12 of [Mordukhovich 2018] (general variational principle), (2.20): for `φ` l.s.c.
and bounded below, finite at `x₀`, and `θ` l.s.c. with `θ x → ∞` as `‖x‖ → ∞`, for all
`ε, λ > 0` (here `ρ`) there is `x̄` (here `z`) with
`φ x̄ + (ε/λ) θ(x̄ - x₀) ≤ φ x + (ε/λ) θ(x - x₀)` for all `x`, i.e. `x̄` minimizes (2.22). -/
theorem exists_forall_add_le_add (hφ : LowerSemicontinuous φ)
    (hbdd : ∃ m : ℝ, ∀ x, (m : EReal) ≤ φ x) (hθ : LowerSemicontinuous θ)
    (hθc : Tendsto θ (cocompact E) atTop) (hε : 0 < ε) (hρ : 0 < ρ) (hx₀ : φ x₀ ≠ ⊤) :
    ∃ z, ∀ x, φ z + ((ε / ρ * θ (z - x₀) : ℝ) : EReal) ≤
      φ x + ((ε / ρ * θ (x - x₀) : ℝ) : EReal) :=
  (exists_lex_minimizer hφ hbdd hθ hθc (div_pos hε hρ) hx₀).imp fun _ h ↦ h.1

omit [NormedSpace ℝ E] in
/-- Thm. 2.12 of [Mordukhovich 2018] (general variational principle), with the estimates for
`θ(0) = 0`: if `θ ≥ 0`, `θ 0 = 0` and `φ x₀ ≤ inf φ + ε`, there is `x̄` (here `z`) satisfying
(2.20) with `φ x̄ ≤ φ x₀` and `θ(x̄ - x₀) ≤ λ` (here `ρ`). -/
theorem general_variational_principle (hφ : LowerSemicontinuous φ)
    (hbdd : ∃ m : ℝ, ∀ x, (m : EReal) ≤ φ x) (hθ : LowerSemicontinuous θ)
    (hθnn : ∀ x, 0 ≤ θ x) (hθ0 : θ 0 = 0) (hθc : Tendsto θ (cocompact E) atTop) (hε : 0 < ε)
    (hρ : 0 < ρ) (hx₀ : φ x₀ ≠ ⊤) (hsub : φ x₀ ≤ (⨅ x, φ x) + ε) :
    ∃ z, (∀ x, φ z + ((ε / ρ * θ (z - x₀) : ℝ) : EReal) ≤
      φ x + ((ε / ρ * θ (x - x₀) : ℝ) : EReal)) ∧ φ z ≤ φ x₀ ∧ θ (z - x₀) ≤ ρ := by
  obtain ⟨z, hz⟩ := exists_forall_add_le_add hφ hbdd hθ hθc hε hρ hx₀
  obtain ⟨m, hm⟩ := hbdd
  exact ⟨z, hz, le_and_le_of_forall_add_le_add hm hθnn hθ0 hε hρ hx₀ hsub hz⟩

omit [NormedSpace ℝ E] in
/-- Thm. 2.12 of [Mordukhovich 2018] (general variational principle), complete statement: if
moreover `θ` is subadditive, then `x̄` (here `z`) also satisfies (2.21),
`φ x̄ ≤ φ x + (ε/λ) θ(x - x̄)` for all `x`, with strict inequality for `x ≠ x̄` when `0` is the
only zero of `θ`. The strict inequality needs a suitable choice of the minimizer `x̄` of (2.22)
(see the module docstring). -/
theorem general_variational_principle_subadditive (hφ : LowerSemicontinuous φ)
    (hbdd : ∃ m : ℝ, ∀ x, (m : EReal) ≤ φ x) (hθ : LowerSemicontinuous θ)
    (hθnn : ∀ x, 0 ≤ θ x) (hθ0 : θ 0 = 0) (hθadd : ∀ x y, θ (x + y) ≤ θ x + θ y)
    (hθc : Tendsto θ (cocompact E) atTop) (hε : 0 < ε) (hρ : 0 < ρ) (hx₀ : φ x₀ ≠ ⊤)
    (hsub : φ x₀ ≤ (⨅ x, φ x) + ε) :
    ∃ z, (∀ x, φ z + ((ε / ρ * θ (z - x₀) : ℝ) : EReal) ≤
      φ x + ((ε / ρ * θ (x - x₀) : ℝ) : EReal)) ∧ φ z ≤ φ x₀ ∧ θ (z - x₀) ≤ ρ ∧
      (∀ x, φ z ≤ φ x + ((ε / ρ * θ (x - z) : ℝ) : EReal)) ∧
      ((∀ x, θ x = 0 → x = 0) → ∀ x ≠ z, φ z < φ x + ((ε / ρ * θ (x - z) : ℝ) : EReal)) := by
  have hc : 0 < ε / ρ := div_pos hε hρ
  obtain ⟨z, h1, h2⟩ := exists_lex_minimizer hφ hbdd hθ hθc hc hx₀
  obtain ⟨m, hm⟩ := hbdd
  obtain ⟨hle, hθz⟩ := le_and_le_of_forall_add_le_add hm hθnn hθ0 hε hρ hx₀ hsub h1
  refine ⟨z, h1, hle, hθz, fun x ↦ le_add_coe_of_add_coe_le_add_coe (h1 x) ?_,
    fun h0 x hx ↦ lt_add_of_lex_minimizer hm hc hθnn hθadd h0 (ne_top_of_le_ne_top hx₀ hle)
      h2 hx⟩
  have := hθadd (x - z) (z - x₀)
  rw [sub_add_sub_cancel] at this
  nlinarith

end General

section Ekeland

/-- If `v (x - z) ≤ (c + δ) ‖x - z‖` for `x` near `z`, for every `δ > 0`, then `‖v‖ ≤ c`. -/
theorem norm_le_of_forall_eventually_le {z : E} {v : StrongDual ℝ E} (hc : 0 ≤ c)
    (h : ∀ δ > 0, ∀ᶠ x in 𝓝 z, v (x - z) ≤ (c + δ) * ‖x - z‖) : ‖v‖ ≤ c := by
  have hdir : ∀ d, v d ≤ c * ‖d‖ := fun d ↦ le_of_forall_pos_le_add_mul (c := ‖d‖) fun δ hδ ↦ by
    have := le_of_eventually_ray (Ω := univ) (d := d) (by rw [nhdsWithin_univ]; exact h δ hδ)
      (Eventually.of_forall fun _ ↦ mem_univ _)
    linarith [add_mul c δ ‖d‖]
  refine v.opNorm_le_bound hc fun d ↦ ?_
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have := hdir (-d)
    rw [map_neg, norm_neg] at this
    linarith
  · exact hdir d

/-- The upper estimate behind (2.24) and the second part of Thm. 2.14 of [Mordukhovich 2018]: if
`φ z ≤ φ x + c ‖x - z‖` for `x` near `z` and `v ∈ ∂̂⁺φ(z) = -∂̂(-φ)(z)` is an upper regular
subgradient, then `‖v‖ ≤ c`. (The book argues through the smooth variational description of
Thm. 1.27; here the definition is used directly.) -/
theorem norm_le_of_forall_le_add_norm {z : E} {v : StrongDual ℝ E} (hc : 0 ≤ c)
    (hmin : ∀ᶠ x in 𝓝 z, φ z ≤ φ x + ((c * ‖x - z‖ : ℝ) : EReal))
    (hv : -v ∈ regularSubdiff (fun x ↦ -φ x) z) : ‖v‖ ≤ c := by
  obtain ⟨s, hs, hv⟩ := hv
  have hφz : φ z = ((-s : ℝ) : EReal) := by
    rw [EReal.coe_neg, ← hs, neg_neg]
  rw [← norm_neg]
  refine norm_le_of_forall_eventually_le (z := z) hc fun δ hδ ↦ ?_
  filter_upwards [hmin, hv δ hδ] with x h1 h2
  rw [EReal.le_neg] at h2
  rw [hφz, coe_le_add_coe_iff] at h1
  have := EReal.coe_le_coe_iff.1 (h1.trans (h2.trans_eq (EReal.coe_neg _).symm))
  simp only [neg_apply] at this ⊢
  nlinarith

/-- The almost stationarity condition (2.24) of [Mordukhovich 2018]: if
`φ z ≤ φ x + c ‖x - z‖` for `x` near `z` (as for the point of Ekeland's variational principle,
with `c = ε/λ`) and `φ` agrees near `z` with a function `f` differentiable at `z`, then
`‖∇f(z)‖ ≤ c`. -/
theorem norm_le_of_hasFDerivAt_of_forall_le_add_norm {z : E} {f : E → ℝ}
    {f' : StrongDual ℝ E} (hf : HasFDerivAt f f' z) (hφf : ∀ᶠ x in 𝓝 z, φ x = f x)
    (hc : 0 ≤ c) (hmin : ∀ᶠ x in 𝓝 z, φ z ≤ φ x + ((c * ‖x - z‖ : ℝ) : EReal)) : ‖f'‖ ≤ c := by
  refine norm_le_of_forall_le_add_norm hc hmin ?_
  have h : (fun x ↦ -φ x) =ᶠ[𝓝 z] fun x ↦ ((-f x : ℝ) : EReal) :=
    hφf.mono fun x hx ↦ show -φ x = ((-f x : ℝ) : EReal) by rw [hx, EReal.coe_neg]
  have h2 : regularSubdiff (fun x ↦ ((-f x : ℝ) : EReal)) z = {-f'} :=
    regularSubdiff_of_hasFDerivAt hf.neg
  rw [regularSubdiff_congr h, h2]
  rfl

variable [FiniteDimensional ℝ E]

/-- Cor. 2.13 of [Mordukhovich 2018] (Ekeland's variational principle), [Clason–Valkonen,
Thm. 2.17] in finite dimensions: for `φ` l.s.c., bounded below, finite at `x₀` with
`φ x₀ ≤ inf φ + ε`, and every `λ > 0` (here `ρ`), there is `x̄` (here `z`) with
`‖x̄ - x₀‖ ≤ λ`, `φ x̄ ≤ φ x₀` and (2.23): `φ x̄ < φ x + (ε/λ) ‖x - x̄‖` for `x ≠ x̄`. -/
theorem ekeland_variational_principle (hφ : LowerSemicontinuous φ)
    (hbdd : ∃ m : ℝ, ∀ x, (m : EReal) ≤ φ x) (hε : 0 < ε) (hρ : 0 < ρ) (hx₀ : φ x₀ ≠ ⊤)
    (hsub : φ x₀ ≤ (⨅ x, φ x) + ε) :
    ∃ z, ‖z - x₀‖ ≤ ρ ∧ φ z ≤ φ x₀ ∧
      ∀ x ≠ z, φ z < φ x + ((ε / ρ * ‖x - z‖ : ℝ) : EReal) := by
  obtain ⟨z, -, hle, hθ, -, hstrict⟩ := general_variational_principle_subadditive
    (θ := fun x ↦ ‖x‖) hφ hbdd continuous_norm.lowerSemicontinuous (fun _ ↦ norm_nonneg _)
    norm_zero norm_add_le tendsto_norm_cocompact_atTop hε hρ hx₀ hsub
  exact ⟨z, hθ, hle, hstrict fun x hx ↦ norm_eq_zero.1 hx⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The strict inequality (2.23) at `x ≠ z` gives the non-strict one at every `x`. -/
theorem forall_le_add_norm_of_forall_ne {z : E}
    (h : ∀ x ≠ z, φ z < φ x + ((c * ‖x - z‖ : ℝ) : EReal)) (x : E) :
    φ z ≤ φ x + ((c * ‖x - z‖ : ℝ) : EReal) := by
  rcases eq_or_ne x z with rfl | hx
  · simp
  · exact (h x hx).le

/-- Thm. 2.14 of [Mordukhovich 2018] (subdifferential almost stationary conditions), upper
part, together with (2.24): the point `x̄` (here `z`) of Ekeland's variational principle satisfies
`‖x̄ - x₀‖ ≤ λ` (here `ρ`), `φ x̄ ≤ φ x₀`, `‖v‖ ≤ ε/λ` for every upper regular subgradient
`v ∈ ∂̂⁺φ(x̄) = -∂̂(-φ)(x̄)`, and `‖∇f(x̄)‖ ≤ ε/λ` whenever `φ` agrees near `x̄` with a function `f`
differentiable at `x̄`. -/
theorem ekeland_almost_stationary (hφ : LowerSemicontinuous φ)
    (hbdd : ∃ m : ℝ, ∀ x, (m : EReal) ≤ φ x) (hε : 0 < ε) (hρ : 0 < ρ) (hx₀ : φ x₀ ≠ ⊤)
    (hsub : φ x₀ ≤ (⨅ x, φ x) + ε) :
    ∃ z, ‖z - x₀‖ ≤ ρ ∧ φ z ≤ φ x₀ ∧
      (∀ x ≠ z, φ z < φ x + ((ε / ρ * ‖x - z‖ : ℝ) : EReal)) ∧
      (∀ v, -v ∈ regularSubdiff (fun x ↦ -φ x) z → ‖v‖ ≤ ε / ρ) ∧
      ∀ (f : E → ℝ) (f' : StrongDual ℝ E), HasFDerivAt f f' z → (∀ᶠ x in 𝓝 z, φ x = f x) →
        ‖f'‖ ≤ ε / ρ := by
  obtain ⟨z, hz, hle, hstrict⟩ := ekeland_variational_principle hφ hbdd hε hρ hx₀ hsub
  have hmin := Eventually.of_forall (f := 𝓝 z) (forall_le_add_norm_of_forall_ne hstrict)
  have hc : 0 ≤ ε / ρ := (div_pos hε hρ).le
  exact ⟨z, hz, hle, hstrict, fun v hv ↦ norm_le_of_forall_le_add_norm hc hmin hv,
    fun f f' hf hφf ↦ norm_le_of_hasFDerivAt_of_forall_le_add_norm hf hφf hc hmin⟩

end Ekeland

section FixedPoint

omit [NormedSpace ℝ E] in
/-- (2.21) for a minimizer of (2.22) with a general coefficient `c > 0` in place of `ε/λ`, as
used in the proof of Prop. 2.15 of [Mordukhovich 2018]. -/
theorem exists_forall_le_add_of_subadditive (hφ : LowerSemicontinuous φ)
    (hbdd : ∃ m : ℝ, ∀ x, (m : EReal) ≤ φ x) (hθ : LowerSemicontinuous θ)
    (hθadd : ∀ x y, θ (x + y) ≤ θ x + θ y) (hθc : Tendsto θ (cocompact E) atTop) (hc : 0 < c)
    (hx₀ : φ x₀ ≠ ⊤) : ∃ z, φ z ≠ ⊤ ∧ ∀ x, φ z ≤ φ x + ((c * θ (x - z) : ℝ) : EReal) := by
  obtain ⟨z, h1, -⟩ := exists_lex_minimizer hφ hbdd hθ hθc hc hx₀
  refine ⟨z, fun h ↦ ?_, fun x ↦ le_add_coe_of_add_coe_le_add_coe (h1 x) ?_⟩
  · have := h1 x₀
    rw [h, EReal.top_add_coe, top_le_iff] at this
    exact EReal.add_ne_top hx₀ (EReal.coe_ne_top _) this
  · have := hθadd (x - z) (z - x₀)
    rw [sub_add_sub_cancel] at this
    nlinarith

omit [NormedSpace ℝ E] in
/-- The key step of Prop. 2.15 of [Mordukhovich 2018]: (2.21) with `ε/λ = 1/2` and (2.25) at the
same pair `(x̄, ȳ)` (here `(z, y)`) force `θ(ȳ - x̄) = 0`. -/
theorem eq_zero_of_le_add_half {m : ℝ} {y z : E} (hm : ∀ x, (m : EReal) ≤ φ x)
    (hθnn : ∀ x, 0 ≤ θ x) (hz : φ z ≠ ⊤)
    (h21 : φ z ≤ φ y + ((1 / 2 * θ (y - z) : ℝ) : EReal))
    (hy : φ y + (θ (y - z) : EReal) ≤ φ z) : θ (y - z) = 0 := by
  have hyt : φ y ≠ ⊤ := fun h ↦ hz (top_le_iff.1 (by rwa [h, EReal.top_add_coe] at hy))
  obtain ⟨a, ha⟩ := exists_coe_eq_of_ne_top (hm y) hyt
  obtain ⟨b, hb⟩ := exists_coe_eq_of_ne_top (hm z) hz
  rw [ha, hb, ← EReal.coe_add, EReal.coe_le_coe_iff] at h21 hy
  linarith [hθnn (y - z)]

omit [NormedSpace ℝ E] in
/-- Prop. 2.15 of [Mordukhovich 2018] (fixed points), first part: let `φ` be l.s.c., bounded
below and not identically `∞`, and `θ ≥ 0` l.s.c., subadditive, with `θ x → ∞` as `‖x‖ → ∞`.
If `F : E ⇉ E` satisfies (2.25), i.e. for every `x` there is `y ∈ F x` with
`θ(y - x) ≤ φ x - φ y` (written `φ y + θ(y - x) ≤ φ x`), then there are `x̄` (here `z`) and
`ȳ ∈ F x̄` with `θ(ȳ - x̄) = 0`. The subadditivity of `θ`, used in the book's proof through
(2.21), is not listed in the book's statement. -/
theorem exists_fixedPoint_of_variational (F : E → Set E) (hφ : LowerSemicontinuous φ)
    (hbdd : ∃ m : ℝ, ∀ x, (m : EReal) ≤ φ x) (hφne : ∃ x₀, φ x₀ ≠ ⊤)
    (hθ : LowerSemicontinuous θ) (hθnn : ∀ x, 0 ≤ θ x) (hθadd : ∀ x y, θ (x + y) ≤ θ x + θ y)
    (hθc : Tendsto θ (cocompact E) atTop)
    (hF : ∀ x, ∃ y ∈ F x, φ y + (θ (y - x) : EReal) ≤ φ x) :
    ∃ z, ∃ y ∈ F z, θ (y - z) = 0 := by
  obtain ⟨x₀, hx₀⟩ := hφne
  obtain ⟨z, hz, h21⟩ :=
    exists_forall_le_add_of_subadditive hφ hbdd hθ hθadd hθc one_half_pos hx₀
  obtain ⟨m, hm⟩ := hbdd
  obtain ⟨y, hyF, hy⟩ := hF z
  exact ⟨z, y, hyF, eq_zero_of_le_add_half hm hθnn hz (h21 y) hy⟩

omit [NormedSpace ℝ E] in
/-- Prop. 2.15 of [Mordukhovich 2018] (fixed points): if moreover `0` is the only zero of `θ`,
then `F` has a fixed point `x̄ ∈ F x̄`. -/
theorem exists_mem_self_of_variational (F : E → Set E) (hφ : LowerSemicontinuous φ)
    (hbdd : ∃ m : ℝ, ∀ x, (m : EReal) ≤ φ x) (hφne : ∃ x₀, φ x₀ ≠ ⊤)
    (hθ : LowerSemicontinuous θ) (hθnn : ∀ x, 0 ≤ θ x) (hθadd : ∀ x y, θ (x + y) ≤ θ x + θ y)
    (hθz : ∀ x, θ x = 0 → x = 0) (hθc : Tendsto θ (cocompact E) atTop)
    (hF : ∀ x, ∃ y ∈ F x, φ y + (θ (y - x) : EReal) ≤ φ x) : ∃ z, z ∈ F z := by
  obtain ⟨z, y, hyF, hy⟩ :=
    exists_fixedPoint_of_variational F hφ hbdd hφne hθ hθnn hθadd hθc hF
  rw [sub_eq_zero.1 (hθz _ hy)] at hyF
  exact ⟨z, hyF⟩

omit [NormedSpace ℝ E] in
/-- Prop. 2.15 of [Mordukhovich 2018] (fixed points), last part: if `F` has nonempty values,
`0` is the only zero of `θ`, and (2.25) holds for all `y ∈ F x`, then `F x̄ = {x̄}` for some
`x̄` (here `z`). -/
theorem exists_eq_singleton_of_variational (F : E → Set E) (hφ : LowerSemicontinuous φ)
    (hbdd : ∃ m : ℝ, ∀ x, (m : EReal) ≤ φ x) (hφne : ∃ x₀, φ x₀ ≠ ⊤)
    (hθ : LowerSemicontinuous θ) (hθnn : ∀ x, 0 ≤ θ x) (hθadd : ∀ x y, θ (x + y) ≤ θ x + θ y)
    (hθz : ∀ x, θ x = 0 → x = 0) (hθc : Tendsto θ (cocompact E) atTop)
    (hFne : ∀ x, (F x).Nonempty) (hF : ∀ x, ∀ y ∈ F x, φ y + (θ (y - x) : EReal) ≤ φ x) :
    ∃ z, F z = {z} := by
  obtain ⟨x₀, hx₀⟩ := hφne
  obtain ⟨z, hz, h21⟩ :=
    exists_forall_le_add_of_subadditive hφ hbdd hθ hθadd hθc one_half_pos hx₀
  obtain ⟨m, hm⟩ := hbdd
  have hmem : ∀ y ∈ F z, y = z := fun y hy ↦
    sub_eq_zero.1 (hθz _ (eq_zero_of_le_add_half hm hθnn hz (h21 y) (hF z y hy)))
  refine ⟨z, (Set.eq_singleton_iff_nonempty_unique_mem.2 ⟨hFne z, hmem⟩)⟩

end FixedPoint

end VariationalAnalysis
