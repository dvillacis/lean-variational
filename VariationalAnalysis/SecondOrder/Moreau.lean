/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import VariationalAnalysis.SecondOrder.ProxRegular
import VariationalAnalysis.SCD.Monotone
import VariationalAnalysis.SCD.GraphLipschitz

/-!
# Moreau envelopes and proximal mappings of prox-regular functions

Following [Mordukhovich 2024, Sect. 1.3.3] (body numbering), we define the Moreau envelope and
the proximal mapping of an extended-real-valued function and prove that, for a function
prox-regular at `x̄` for `v̄`, the proximal mapping is single-valued and Lipschitz around
`x̄ + λv̄` and the Moreau envelope is of class `C^{1,1}` there.

## Main declarations

* `proxObjective φ λ u x = φ(x) + ‖x - u‖² / (2λ)`.
* `moreauEnvelope φ λ`, `localMoreauEnvelope φ λ x₀ ε`: (1.85), (1.86).
* `proximalMap φ λ`, `localProximalMap φ λ x₀ ε`: (1.87), (1.88).

## Main results

* `norm_le_of_proxObjective_le`, `moreauEnvelope_eq_localMoreauEnvelope`,
  `proximalMap_eq_localProximalMap`: Lemma 1.68, (1.90) and (1.91).
* `IsHypomonotoneOn.norm_sub_le`: Lemma 1.69, the resolvent `(I + λT)⁻¹` of a
  `ρ`-hypomonotone mapping is single-valued and Lipschitz with constant `(1 - λρ)⁻¹`.
* `ProxRegularFor.exists_proximalMap`: Thm. 1.70.
* `ProxRegularFor.exists_moreauEnvelope`: Thm. 1.71, (1.94).
* `ContinuouslyProxRegularFor.graphicallyLipschitzianAt`: Cor. 1.72.
* `ContinuouslyProxRegularFor.hasSCDPropertyAround`: the SCD part of
  [Gfrerer–Outrata 2022, Prop. 3.26].

## Implementation notes

* Everything is stated in finite-dimensional real inner product spaces; subgradients are dual
  vectors, so the subgradient `v̄` is written `toDual ℝ E g` with `g ∈ E`.
* In Thms. 1.70 and 1.71 the book assumes `φ` l.s.c. around `x̄` and "minorized by a quadratic
  function around `x̄`". The global proximal mapping needs global information, so we assume `φ`
  l.s.c. everywhere and prox-bounded: `φ(x) ≥ a - b‖x - x̄‖²` for all `x`. Cor. 1.72 is local and
  is derived by applying Thm. 1.70 to `φ` plus the indicator function of a small closed ball.
* We use `l` for the parameter `λ`, a reserved word in Lean.
-/

namespace VariationalAnalysis

open Filter Topology Set Metric ContinuousLinearMap InnerProductSpace Asymptotics
open scoped NNReal RealInnerProductSpace

section Defs

variable {E : Type*} [NormedAddCommGroup E] (φ : E → EReal) (l : ℝ)

/-- The proximal objective `x ↦ φ(x) + ‖x - u‖² / (2λ)` of [Mordukhovich 2024, (1.85)]. -/
noncomputable def proxObjective (u x : E) : EReal :=
  φ x + (((2 * l)⁻¹ * ‖x - u‖ ^ 2 : ℝ) : EReal)

/-- The Moreau envelope `e_λφ(u) = inf_x {φ(x) + ‖x - u‖² / (2λ)}`
[Mordukhovich 2024, Def. 1.66, (1.85)]. -/
noncomputable def moreauEnvelope (u : E) : EReal :=
  ⨅ x, proxObjective φ l u x

/-- The local Moreau envelope `e_{λ,ε}φ(u) = inf_{‖x - x̄‖ ≤ ε} {φ(x) + ‖x - u‖² / (2λ)}`
[Mordukhovich 2024, (1.86)]. -/
noncomputable def localMoreauEnvelope (x₀ : E) (ε : ℝ) (u : E) : EReal :=
  ⨅ x ∈ closedBall x₀ ε, proxObjective φ l u x

/-- The proximal mapping `P_λφ(u) = argmin_x {φ(x) + ‖x - u‖² / (2λ)}`
[Mordukhovich 2024, Def. 1.67, (1.87)]. -/
def proximalMap (u : E) : Set E :=
  {x | ∀ y, proxObjective φ l u x ≤ proxObjective φ l u y}

/-- The local proximal mapping [Mordukhovich 2024, (1.88)]. -/
def localProximalMap (x₀ : E) (ε : ℝ) (u : E) : Set E :=
  {x | x ∈ closedBall x₀ ε ∧ ∀ y ∈ closedBall x₀ ε, proxObjective φ l u x ≤ proxObjective φ l u y}

variable {φ l}

theorem moreauEnvelope_le (u x : E) : moreauEnvelope φ l u ≤ proxObjective φ l u x :=
  iInf_le _ x

theorem moreauEnvelope_le_self (u : E) : moreauEnvelope φ l u ≤ φ u := by
  simpa [proxObjective] using moreauEnvelope_le (φ := φ) (l := l) u u

theorem moreauEnvelope_eq_of_mem_proximalMap {u x : E} (hx : x ∈ proximalMap φ l u) :
    moreauEnvelope φ l u = proxObjective φ l u x :=
  le_antisymm (moreauEnvelope_le u x) (le_iInf hx)

theorem moreauEnvelope_le_localMoreauEnvelope (x₀ : E) (ε : ℝ) (u : E) :
    moreauEnvelope φ l u ≤ localMoreauEnvelope φ l x₀ ε u :=
  le_iInf₂ fun x _ ↦ moreauEnvelope_le u x

/-- An extended real `a ≠ ⊥` with `a + A ≤ B` (`A, B` real) is real. -/
theorem exists_real_of_add_coe_le {a : EReal} {A B : ℝ} (h : a + A ≤ B) (hb : a ≠ ⊥) :
    ∃ s : ℝ, a = s ∧ s + A ≤ B := by
  induction a using EReal.rec with
  | bot => exact absurd rfl hb
  | top => exact absurd h (by simp)
  | coe s => exact ⟨s, rfl, by exact_mod_cast h⟩

end Defs

/-- `t² ≤ bt + c` with `b, c ≥ 0` implies `t ≤ b + √c`. -/
theorem le_add_sqrt_of_sq_le {t b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (h : t ^ 2 ≤ b * t + c) :
    t ≤ b + √c := by
  by_contra hlt
  push Not at hlt
  have hs : √c * √c = c := Real.mul_self_sqrt hc
  have hsn := Real.sqrt_nonneg c
  have ht : 0 < t := by linarith
  have h1 : √c * √c ≤ t * √c := mul_le_mul_of_nonneg_right (by linarith) hsn
  have h2 : t * √c < t * (t - b) := mul_lt_mul_of_pos_left (by linarith) ht
  nlinarith

/-- `∀ᶠ t in 𝓝 0, t * k < M` for `M > 0`. -/
theorem eventually_mul_lt (k : ℝ) {M : ℝ} (hM : 0 < M) : ∀ᶠ t in 𝓝 (0 : ℝ), t * k < M := by
  have : Tendsto (fun t : ℝ ↦ t * k) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).mul_const k
  exact this.eventually (gt_mem_nhds hM)

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {φ : E → EReal} {l : ℝ} {x₀ : E}

omit [CompleteSpace E] in
/-- [Mordukhovich 2024, Lemma 1.68, (1.90)]: if `φ(0) = 0` and `φ(x) ≥ -(r/2)‖x‖²`, then for
`λ ∈ (0, 1/r)`, `μ = (1 - λr)⁻¹` and `ρ > 0`, every `ρ`-minimizer `x` of the proximal objective
satisfies `‖x‖ ≤ 2μ‖u‖ + √(2λμρ)`. -/
theorem norm_le_of_proxObjective_le {r : ℝ} (hl : 0 < l) (hlr : l * r < 1) (hφ0 : φ 0 = 0)
    (hφ : ∀ x, ((-(r / 2) * ‖x‖ ^ 2 : ℝ) : EReal) ≤ φ x) {ρ : ℝ} (hρ : 0 < ρ) {x u : E}
    (hx : proxObjective φ l u x ≤ moreauEnvelope φ l u + ρ) :
    ‖x‖ ≤ 2 * (1 - l * r)⁻¹ * ‖u‖ + √(2 * l * (1 - l * r)⁻¹ * ρ) := by
  have he : moreauEnvelope φ l u ≤ (((2 * l)⁻¹ * ‖u‖ ^ 2 : ℝ) : EReal) := by
    have := moreauEnvelope_le (φ := φ) (l := l) u 0
    simpa [proxObjective, hφ0, norm_neg] using this
  have hx' : φ x + (((2 * l)⁻¹ * ‖x - u‖ ^ 2 : ℝ) : EReal) ≤
      (((2 * l)⁻¹ * ‖u‖ ^ 2 + ρ : ℝ) : EReal) := by
    rw [EReal.coe_add]
    exact hx.trans (add_le_add_left he _)
  obtain ⟨s, hs, hsA⟩ := exists_real_of_add_coe_le hx'
    (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hφ x))
  have hsr : -(r / 2) * ‖x‖ ^ 2 ≤ s := by have := hφ x; rwa [hs, EReal.coe_le_coe_iff] at this
  have h2lk : 2 * l * (2 * l)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hsA (by positivity : (0 : ℝ) ≤ 2 * l)
  rw [mul_add, mul_add, ← mul_assoc, ← mul_assoc, h2lk, one_mul, one_mul,
    norm_sub_sq_real] at hmul
  have hin := real_inner_le_norm x u
  have hmr : 2 * l * (-(r / 2) * ‖x‖ ^ 2) ≤ 2 * l * s :=
    mul_le_mul_of_nonneg_left hsr (by positivity)
  set μ := (1 - l * r)⁻¹ with hμ
  have hμpos : 0 < μ := inv_pos.2 (by linarith)
  have hμ1 : μ * (1 - l * r) = 1 := inv_mul_cancel₀ (by linarith)
  -- `(1 - λr)‖x‖² ≤ 2‖x‖‖u‖ + 2λρ`
  have key : (1 - l * r) * ‖x‖ ^ 2 ≤ 2 * ‖u‖ * ‖x‖ + 2 * l * ρ := by linarith
  have key' := mul_le_mul_of_nonneg_left key hμpos.le
  rw [← mul_assoc, hμ1, one_mul] at key'
  refine le_add_sqrt_of_sq_le (by positivity) (by positivity) ?_
  linarith

omit [CompleteSpace E] in
/-- Under the quadratic minorization of [Mordukhovich 2024, Lemma 1.68] the Moreau envelope is
bounded below: `e_λφ(u) ≥ (2λ)⁻¹(‖u‖² - (1 - λr)⁻¹‖u‖²)`. -/
theorem coe_le_moreauEnvelope_of_quadratic {r : ℝ} (hl : 0 < l) (hlr : l * r < 1)
    (hφ : ∀ x, ((-(r / 2) * ‖x‖ ^ 2 : ℝ) : EReal) ≤ φ x) (u : E) :
    (((2 * l)⁻¹ * (‖u‖ ^ 2 - (1 - l * r)⁻¹ * ‖u‖ ^ 2) : ℝ) : EReal) ≤ moreauEnvelope φ l u := by
  refine le_iInf fun x ↦ le_trans ?_ (add_le_add (hφ x) le_rfl)
  rw [← EReal.coe_add, EReal.coe_le_coe_iff, norm_sub_sq_real]
  set a := 1 - l * r with ha_def
  have ha : 0 < a := by linarith
  have hin := real_inner_le_norm x u
  have e1 : a⁻¹ * (a * ‖x‖ - ‖u‖) ^ 2 = a * ‖x‖ ^ 2 - 2 * ‖x‖ * ‖u‖ + a⁻¹ * ‖u‖ ^ 2 := by
    field_simp
    ring
  have e2 := mul_nonneg (inv_nonneg.2 ha.le) (sq_nonneg (a * ‖x‖ - ‖u‖))
  have key : ‖u‖ ^ 2 - a⁻¹ * ‖u‖ ^ 2 ≤ a * ‖x‖ ^ 2 - 2 * ⟪x, u⟫ + ‖u‖ ^ 2 := by linarith
  have e3 : -(r / 2) * ‖x‖ ^ 2 + (2 * l)⁻¹ * (‖x‖ ^ 2 - 2 * ⟪x, u⟫ + ‖u‖ ^ 2) =
      (2 * l)⁻¹ * (a * ‖x‖ ^ 2 - 2 * ⟪x, u⟫ + ‖u‖ ^ 2) := by
    rw [ha_def]
    field_simp
    ring
  rw [e3]
  exact mul_le_mul_of_nonneg_left key (by positivity)

omit [CompleteSpace E] in
/-- [Mordukhovich 2024, Lemma 1.68], (1.90) for `‖u‖ ≤ γ`: `ρ`-minimizers of the proximal
objective lie in the ball of radius `ε ≥ 2μγ + √(2λμρ)`. -/
theorem mem_closedBall_of_proxObjective_le {r : ℝ} (hl : 0 < l) (hlr : l * r < 1) (hφ0 : φ 0 = 0)
    (hφ : ∀ x, ((-(r / 2) * ‖x‖ ^ 2 : ℝ) : EReal) ≤ φ x) {ρ γ ε : ℝ} (hρ : 0 < ρ)
    (hε : 2 * (1 - l * r)⁻¹ * γ + √(2 * l * (1 - l * r)⁻¹ * ρ) ≤ ε) {x u : E} (hu : ‖u‖ ≤ γ)
    (hx : proxObjective φ l u x ≤ moreauEnvelope φ l u + ρ) : x ∈ closedBall (0 : E) ε := by
  rw [mem_closedBall, dist_zero_right]
  have hμ : 0 ≤ 2 * (1 - l * r)⁻¹ := mul_nonneg zero_le_two (inv_nonneg.2 (by linarith))
  have := mul_le_mul_of_nonneg_left hu hμ
  linarith [norm_le_of_proxObjective_le hl hlr hφ0 hφ hρ hx]

omit [CompleteSpace E] in
/-- [Mordukhovich 2024, Lemma 1.68, (1.91)]: for `‖u‖ ≤ γ` the global Moreau envelope agrees
with the local one on the ball of radius `ε ≥ 2μγ + √(2λμρ)`, `μ = (1 - λr)⁻¹`. -/
theorem moreauEnvelope_eq_localMoreauEnvelope {r : ℝ} (hl : 0 < l) (hlr : l * r < 1)
    (hφ0 : φ 0 = 0) (hφ : ∀ x, ((-(r / 2) * ‖x‖ ^ 2 : ℝ) : EReal) ≤ φ x) {ρ γ ε : ℝ}
    (hρ : 0 < ρ) (hε : 2 * (1 - l * r)⁻¹ * γ + √(2 * l * (1 - l * r)⁻¹ * ρ) ≤ ε) {u : E}
    (hu : ‖u‖ ≤ γ) : moreauEnvelope φ l u = localMoreauEnvelope φ l 0 ε u := by
  refine le_antisymm (moreauEnvelope_le_localMoreauEnvelope _ _ _) ?_
  obtain ⟨m, hm⟩ : ∃ m : ℝ, moreauEnvelope φ l u = m := by
    have hlo := coe_le_moreauEnvelope_of_quadratic hl hlr hφ u
    have hhi : moreauEnvelope φ l u ≤ (((2 * l)⁻¹ * ‖u‖ ^ 2 : ℝ) : EReal) := by
      simpa [proxObjective, hφ0, norm_neg] using moreauEnvelope_le (φ := φ) (l := l) u 0
    exact ⟨_, (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) hhi)
      (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlo)).symm⟩
  refine le_of_forall_gt_imp_ge_of_dense fun β hβ ↦ ?_
  have hlt : moreauEnvelope φ l u < min β ((m + ρ : ℝ) : EReal) := by
    rw [hm] at hβ ⊢
    exact lt_min hβ (EReal.coe_lt_coe_iff.2 (by linarith))
  obtain ⟨x, hx⟩ := iInf_lt_iff.1 hlt
  have hxb : x ∈ closedBall (0 : E) ε := mem_closedBall_of_proxObjective_le hl hlr hφ0 hφ hρ hε hu
    (by rw [hm, ← EReal.coe_add]; exact (hx.trans_le (min_le_right _ _)).le)
  have := iInf₂_le (f := fun x (_ : x ∈ closedBall (0 : E) ε) ↦ proxObjective φ l u x) x hxb
  exact this.trans (hx.trans_le (min_le_left _ _)).le

omit [CompleteSpace E] in
/-- [Mordukhovich 2024, Lemma 1.68, (1.91)]: for `‖u‖ ≤ γ` the global proximal mapping agrees
with the local one on the ball of radius `ε ≥ 2μγ + √(2λμρ)`. -/
theorem proximalMap_eq_localProximalMap {r : ℝ} (hl : 0 < l) (hlr : l * r < 1)
    (hφ0 : φ 0 = 0) (hφ : ∀ x, ((-(r / 2) * ‖x‖ ^ 2 : ℝ) : EReal) ≤ φ x) {ρ γ ε : ℝ}
    (hρ : 0 < ρ) (hε : 2 * (1 - l * r)⁻¹ * γ + √(2 * l * (1 - l * r)⁻¹ * ρ) ≤ ε) {u : E}
    (hu : ‖u‖ ≤ γ) : proximalMap φ l u = localProximalMap φ l 0 ε u := by
  ext x
  constructor
  · intro hx
    refine ⟨mem_closedBall_of_proxObjective_le hl hlr hφ0 hφ hρ hε hu ?_, fun y _ ↦ hx y⟩
    rw [moreauEnvelope_eq_of_mem_proximalMap hx]
    exact le_add_of_nonneg_right (EReal.coe_nonneg.2 hρ.le)
  · rintro ⟨-, hmin⟩ y
    have h1 : proxObjective φ l u x ≤ localMoreauEnvelope φ l 0 ε u := le_iInf₂ hmin
    rw [← moreauEnvelope_eq_localMoreauEnvelope hl hlr hφ0 hφ hρ hε hu] at h1
    exact h1.trans (moreauEnvelope_le u y)

/-- [Mordukhovich 2024, Lemma 1.69] (finite-dimensional form): if `T` is `ρ`-hypomonotone on
`U` and `λρ < 1`, then `(I + λT)⁻¹` is single-valued and Lipschitz with constant `(1 - λρ)⁻¹`
on `U`: `x ∈ (I + λT)⁻¹(u)` means `λ⁻¹(u - x) ∈ T(x)`. -/
theorem IsHypomonotoneOn.norm_sub_le {ρ : ℝ} {T : E → Set (StrongDual ℝ E)} {U : Set E}
    (hT : IsHypomonotoneOn ρ T U) (hl : 0 < l) (hlρ : l * ρ < 1) {x₁ x₂ u₁ u₂ : E}
    (hx₁ : x₁ ∈ U) (hx₂ : x₂ ∈ U) (h₁ : toDual ℝ E (l⁻¹ • (u₁ - x₁)) ∈ T x₁)
    (h₂ : toDual ℝ E (l⁻¹ • (u₂ - x₂)) ∈ T x₂) :
    ‖x₁ - x₂‖ ≤ (1 - l * ρ)⁻¹ * ‖u₁ - u₂‖ := by
  have h := hT x₁ hx₁ x₂ hx₂ _ h₁ _ h₂
  rw [← map_sub, ← smul_sub, show (u₁ - x₁) - (u₂ - x₂) = (u₁ - u₂) - (x₁ - x₂) by abel,
    toDual_apply_apply, real_inner_smul_left, inner_sub_left, real_inner_self_eq_norm_sq] at h
  have hP := real_inner_le_norm (u₁ - u₂) (x₁ - x₂)
  have hl1 : l * l⁻¹ = 1 := mul_inv_cancel₀ hl.ne'
  have hm := mul_le_mul_of_nonneg_left h hl.le
  rw [← mul_assoc, hl1, one_mul] at hm
  have key : (1 - l * ρ) * ‖x₁ - x₂‖ ^ 2 ≤ ‖u₁ - u₂‖ * ‖x₁ - x₂‖ := by linarith
  rw [inv_mul_eq_div, le_div_iff₀ (by linarith)]
  rcases (norm_nonneg (x₁ - x₂)).eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]; positivity
  · refine le_of_mul_le_mul_right ?_ hpos
    linarith

/-- The Fermat rule for the proximal objective: a proximal point `x ∈ P_λφ(u)` satisfies
`λ⁻¹(u - x) ∈ ∂̂φ(x)` [Mordukhovich 2024, proof of Thm. 1.70]. -/
theorem toDual_mem_regularSubdiff_of_mem_proximalMap {u x : E} {s : ℝ} (hs : φ x = s)
    (hx : x ∈ proximalMap φ l u) : toDual ℝ E (l⁻¹ • (u - x)) ∈ regularSubdiff φ x := by
  have hmin : IsLocalMin (fun z ↦ φ z + (((2 * l)⁻¹ * ‖z - u‖ ^ 2 : ℝ) : EReal)) x :=
    Filter.Eventually.of_forall hx
  have h0 := zero_mem_regularSubdiff_of_isLocalMin hmin
    (r := s + (2 * l)⁻¹ * ‖x - u‖ ^ 2) (by rw [hs, EReal.coe_add])
  have hd : HasFDerivAt (fun z ↦ (2 * l)⁻¹ * ‖z - u‖ ^ 2) (l⁻¹ • innerSL ℝ (x - u)) x := by
    have := hasFDerivAt_quadPerturb (0 : StrongDual ℝ E) l⁻¹ u x
    simp only [zero_apply, neg_zero, zero_add] at this
    convert this using 1
    funext z
    ring
  have := (mem_regularSubdiff_add_iff hd).1 h0
  convert this using 1
  ext y
  simp only [toDual_apply_apply, real_inner_smul_left, inner_sub_left, zero_sub, neg_apply,
    smul_apply, innerSL_apply_apply, smul_eq_mul]
  ring

omit [CompleteSpace E] in
/-- Proximal mappings are monotone: for `xᵢ ∈ P_λφ(uᵢ)` with `φ(xᵢ)` finite,
`⟨x₁ - x₂, u₁ - u₂⟩ ≥ 0`. No convexity or prox-regularity is needed
(cf. [Gfrerer–Outrata 2022, proof of Prop. 3.26]). -/
theorem inner_nonneg_of_mem_proximalMap (hl : 0 < l) {u₁ u₂ x₁ x₂ : E} {s₁ s₂ : ℝ}
    (hs₁ : φ x₁ = s₁) (hs₂ : φ x₂ = s₂) (hx₁ : x₁ ∈ proximalMap φ l u₁)
    (hx₂ : x₂ ∈ proximalMap φ l u₂) : 0 ≤ ⟪x₁ - x₂, u₁ - u₂⟫_ℝ := by
  have h₁ := hx₁ x₂
  have h₂ := hx₂ x₁
  simp only [proxObjective, hs₁, hs₂, ← EReal.coe_add, EReal.coe_le_coe_iff] at h₁ h₂
  have hc : 0 < (2 * l)⁻¹ := by positivity
  have key : ‖x₁ - u₁‖ ^ 2 + ‖x₂ - u₂‖ ^ 2 ≤ ‖x₂ - u₁‖ ^ 2 + ‖x₁ - u₂‖ ^ 2 := by
    refine le_of_mul_le_mul_left ?_ hc
    rw [mul_add, mul_add]
    linarith
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real] at key
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  linarith

end Inner

section Local

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {φ : E → EReal} {x₀ : E} {v₀ : StrongDual ℝ E}

/-- Prox-regularity is a local property: it only depends on `φ` near `x₀`. -/
theorem ProxRegularFor.congr {ψ : E → EReal} {ρ : ℝ} (h : ProxRegularFor φ x₀ v₀) (hρ : 0 < ρ)
    (hψ : ∀ x ∈ ball x₀ ρ, ψ x = φ x) : ProxRegularFor ψ x₀ v₀ := by
  have hS : ∀ x ∈ ball x₀ ρ, subdiff ψ x = subdiff φ x := fun x hx ↦
    subdiff_congr (eventually_of_mem (isOpen_ball.mem_nhds hx) hψ)
  have h0 := mem_ball_self (x := x₀) hρ
  obtain ⟨hv₀, hlsc, ε, hε, η, hη, H⟩ := h
  refine ⟨hS x₀ h0 ▸ hv₀, ?_, min ε (ρ / 2), lt_min hε (half_pos hρ), η, hη, ?_⟩
  · filter_upwards [hlsc, isOpen_ball.mem_nhds h0] with x hx hxb c hc
    rw [hψ x hxb] at hc
    filter_upwards [hx c hc, isOpen_ball.mem_nhds hxb] with z hz hzb
    rwa [hψ z hzb]
  · intro x u v hv r hr hvv hu hx hxf
    have hb : ∀ y : E, ‖y - x₀‖ ≤ min ε (ρ / 2) → y ∈ ball x₀ ρ := fun y hy ↦ by
      rw [mem_ball, dist_eq_norm]; linarith [min_le_right ε (ρ / 2)]
    rw [hS x (hb x hx)] at hv
    rw [hψ x (hb x hx)] at hr hxf
    rw [hψ x₀ h0] at hxf
    rw [hψ u (hb u hu)]
    have hm := min_le_left ε (ρ / 2)
    exact H x u v hv r hr (hvv.trans hm) (hu.trans hm) (hx.trans hm)
      (hxf.trans (add_le_add_right (EReal.coe_le_coe_iff.2 hm) _))

end Local

/-- An extended real strictly between two reals is real. -/
theorem exists_real_of_mem_Ioo {z : EReal} {a b : ℝ} (h : z ∈ Ioo (a : EReal) b) :
    ∃ s : ℝ, z = s ∧ a < s ∧ s < b := by
  induction z using EReal.rec with
  | bot => exact absurd h.1 not_lt_bot
  | top => exact absurd h.2 not_top_lt
  | coe s => exact ⟨s, rfl, by exact_mod_cast h.1, by exact_mod_cast h.2⟩

section Main

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {φ : E → EReal} {x₀ : E}

/-- [Mordukhovich 2024, Thm. 1.70] (proximal mappings of prox-regular functions): let `φ` be
l.s.c., prox-bounded (`φ(x) ≥ a - b‖x - x̄‖²`) and prox-regular at `x̄` for `v̄ = ⟨g, ·⟩`. Then
there are `ε, λ̄ > 0` such that for each `λ ∈ (0, λ̄)` the proximal mapping `P_λφ` is single-valued
and `2`-Lipschitz on a ball `U_λ` around `x̄ + λg`, with `P_λφ(x̄ + λg) = x̄`, and it coincides
there with `(I + λT_ε)⁻¹`, where `T_ε` is the `φ`-attentive `ε`-localization of `∂φ` around
`(x̄, v̄)`. -/
theorem ProxRegularFor.exists_proximalMap {g : E} (hφ : ProxRegularFor φ x₀ (toDual ℝ E g))
    (hlsc : ∀ x, LowerSemicontinuousAt φ x)
    (hbd : ∃ a b : ℝ, ∀ x, ((a - b * ‖x - x₀‖ ^ 2 : ℝ) : EReal) ≤ φ x) :
    ∃ ε > (0 : ℝ), ∃ l₀ > (0 : ℝ), ∀ l, 0 < l → l < l₀ → ∃ δ > (0 : ℝ), ∃ p : E → E,
      p (x₀ + l • g) = x₀ ∧
      (∀ u ∈ ball (x₀ + l • g) δ, proximalMap φ l u = {p u}) ∧
      LipschitzOnWith 2 p (ball (x₀ + l • g) δ) ∧
      (∀ u ∈ ball (x₀ + l • g) δ, toDual ℝ E (l⁻¹ • (u - p u)) ∈
        attentiveLocalization (subdiff φ) φ x₀ (toDual ℝ E g) ε (p u)) ∧
      (∀ u ∈ ball (x₀ + l • g) δ, ∀ x, toDual ℝ E (l⁻¹ • (u - x)) ∈
        attentiveLocalization (subdiff φ) φ x₀ (toDual ℝ E g) ε x → x = p u) := by
  obtain ⟨r₀, hr₀, -⟩ := hφ.1
  obtain ⟨r₀', hr₀', ε₀, hε₀, α, hα, Hprox⟩ := hφ.mem_proxSubdiff
  have hrr : r₀' = r₀ := by rw [hr₀] at hr₀'; exact_mod_cast hr₀'.symm
  rw [hrr] at Hprox
  obtain ⟨ε, hε, η, hη, hT⟩ := hφ.isHypomonotoneOn_attentiveLocalization
  obtain ⟨a, b, hab⟩ := hbd
  obtain ⟨B, hB, hbB⟩ : ∃ B : ℝ, 0 ≤ B ∧ b ≤ B := ⟨max b 0, le_max_right _ _, le_max_left _ _⟩
  have hlow : ∀ x, ((a - B * ‖x - x₀‖ ^ 2 : ℝ) : EReal) ≤ φ x := fun x ↦ by
    refine le_trans (EReal.coe_le_coe_iff.2 ?_) (hab x)
    linarith [mul_le_mul_of_nonneg_right hbB (sq_nonneg ‖x - x₀‖)]
  have hra : a ≤ r₀ := by
    have := hlow x₀
    rw [hr₀, EReal.coe_le_coe_iff] at this
    simpa using this
  have hng := norm_nonneg g
  -- the admissible parameters
  have hev : ∀ᶠ l in 𝓝 (0 : ℝ), l < 1 ∧ l * (4 * B + 1) < 1 ∧ l * (2 * α + 1) < 1 ∧
      l * (2 * η + 1) < 1 ∧ l * (8 * (‖g‖ + 1)) < ε₀ ∧ l * (8 * (r₀ - a + 1)) < ε₀ ^ 2 ∧
      l * (‖g‖ + α + 1) < ε :=
    (gt_mem_nhds one_pos).and ((eventually_mul_lt _ one_pos).and ((eventually_mul_lt _ one_pos).and
      ((eventually_mul_lt _ one_pos).and ((eventually_mul_lt _ hε₀).and
      ((eventually_mul_lt _ (pow_pos hε₀ 2)).and (eventually_mul_lt _ hε))))))
  obtain ⟨l₀, hl₀, H⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε, hε, l₀, hl₀, fun l hl hll₀ ↦ ?_⟩
  obtain ⟨hl1, hlB, hlα, hlη, hlc, hlr, hlε⟩ :=
    H (by rw [Real.dist_eq, sub_zero, abs_of_pos hl]; exact hll₀)
  have hlB' : l * B ≤ 1 / 4 := by linarith
  have hlα' : l * α ≤ 1 / 2 := by linarith
  have hlη' : l * η ≤ 1 / 2 := by linarith
  have hlr' : 8 * (l * (r₀ - a)) < ε₀ ^ 2 := by linarith
  have hlg0 : 0 ≤ l * ‖g‖ := mul_nonneg hl.le hng
  obtain ⟨m, hm, hm1, hmε⟩ : ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ m ≤ ε :=
    ⟨min 1 ε, lt_min one_pos hε, min_le_left _ _, min_le_right _ _⟩
  set δ := l * m / 10 with hδ_def
  have hδ : 0 < δ := by positivity
  have hlm : l * m ≤ l := mul_le_of_le_one_right hl.le hm1
  have hlmε : l * m ≤ l * ε := mul_le_mul_of_nonneg_left hmε hl.le
  have hδl : δ ≤ l / 10 := by rw [hδ_def]; linarith
  have hlm' : l * m ≤ m := mul_le_of_le_one_left hm.le hl1.le
  have h4δ : 4 * δ < ε₀ := by linarith
  refine ⟨δ, hδ, ?_⟩
  have h2lk : 2 * l * (2 * l)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  have hll : l⁻¹ * l = 1 := inv_mul_cancel₀ hl.ne'
  set v₀ := toDual ℝ E g with hv₀
  -- the main estimate: points with a smaller objective value than `x₀` are close to `x₀`
  have claim : ∀ u ∈ ball (x₀ + l • g) δ, ∀ x,
      proxObjective φ l u x ≤ proxObjective φ l u x₀ → ∃ s : ℝ, φ x = s ∧
        ‖x - x₀‖ ≤ 4 * ‖u - (x₀ + l • g)‖ ∧ |s - r₀| < ε ∧
        ‖toDual ℝ E (l⁻¹ • (u - x)) - v₀‖ < ε := by
    intro u hu x hle
    rw [mem_ball, dist_eq_norm] at hu
    set d := u - (x₀ + l • g) with hd_def
    set w := x - x₀ with hw_def
    have hdn := norm_nonneg d
    have hwn := norm_nonneg w
    have he : u - x₀ = l • g + d := by rw [hd_def]; abel
    have hxu : x - u = w - (u - x₀) := by rw [hw_def]; abel
    have hle' : φ x + (((2 * l)⁻¹ * ‖x - u‖ ^ 2 : ℝ) : EReal) ≤
        ((r₀ + (2 * l)⁻¹ * ‖x₀ - u‖ ^ 2 : ℝ) : EReal) := by
      have := hle; rwa [proxObjective, proxObjective, hr₀, ← EReal.coe_add] at this
    obtain ⟨s, hs, hsA⟩ := exists_real_of_add_coe_le hle'
      (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hlow x))
    have hmul := mul_le_mul_of_nonneg_left hsA (by positivity : (0 : ℝ) ≤ 2 * l)
    rw [mul_add, mul_add, ← mul_assoc, ← mul_assoc, h2lk, one_mul, one_mul, hxu,
      norm_sub_sq_real, norm_sub_rev x₀ u, he, inner_add_right, real_inner_smul_right] at hmul
    -- `hmul : 2λs + ‖w‖² - 2(λ⟨w, g⟩ + ⟨w, d⟩) + ‖e‖² ≤ 2λr₀ + ‖e‖²`
    have hg1 := abs_le.1 ((abs_real_inner_le_norm w g))
    have hd1 := abs_le.1 ((abs_real_inner_le_norm w d))
    have hlg : l * ⟪w, g⟫_ℝ ≤ l * (‖w‖ * ‖g‖) := mul_le_mul_of_nonneg_left hg1.2 hl.le
    have hlg' : -(l * (‖w‖ * ‖g‖)) ≤ l * ⟪w, g⟫_ℝ := by
      linarith [mul_le_mul_of_nonneg_left hg1.1 hl.le]
    have hwd : ‖w‖ * ‖d‖ ≤ ‖w‖ * δ := mul_le_mul_of_nonneg_left hu.le hwn
    have hwδ : ‖w‖ * δ ≤ ‖w‖ * l := mul_le_mul_of_nonneg_left (by linarith) hwn
    -- the far case is impossible
    have hwε : ‖w‖ ≤ ε₀ := by
      by_contra hgt
      push Not at hgt
      have hsa : a - B * ‖w‖ ^ 2 ≤ s := by
        have := hlow x; rwa [hs, EReal.coe_le_coe_iff] at this
      have F1 := mul_le_mul_of_nonneg_left hsa (by positivity : (0 : ℝ) ≤ 2 * l)
      have F2 : l * B * ‖w‖ ^ 2 ≤ 1 / 4 * ‖w‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hlB' (sq_nonneg _)
      have F5 : 2 * l * (‖g‖ + 1) * ‖w‖ ≤ ‖w‖ / 4 * ‖w‖ :=
        mul_le_mul_of_nonneg_right (by linarith) hwn
      have F6 : ε₀ ^ 2 < ‖w‖ ^ 2 := pow_lt_pow_left₀ hgt hε₀.le two_ne_zero
      linarith [hd1.2]
    -- the near case
    have hsH : r₀ + v₀ w - α / 2 * ‖w‖ ^ 2 ≤ s := by
      have := Hprox x hwε; rwa [hs, EReal.coe_le_coe_iff] at this
    rw [hv₀, toDual_apply_apply, real_inner_comm] at hsH
    have G1 := mul_le_mul_of_nonneg_left hsH (by positivity : (0 : ℝ) ≤ 2 * l)
    have G2 : l * α * ‖w‖ ^ 2 ≤ 1 / 2 * ‖w‖ ^ 2 := mul_le_mul_of_nonneg_right hlα' (sq_nonneg _)
    have ht4 : ‖w‖ ≤ 4 * ‖d‖ := by
      rcases hwn.eq_or_lt with h0 | hpos
      · rw [← h0]; positivity
      · refine le_of_mul_le_mul_left ?_ hpos
        linarith [hd1.2]
    have hwl : ‖w‖ ≤ l / 2 := by linarith
    have hw1 : ‖w‖ ≤ 1 := by linarith
    refine ⟨s, hs, ht4, ?_, ?_⟩
    · -- the function values
      have hup : 2 * l * (s - r₀) ≤ 2 * l * (‖w‖ * (‖g‖ + 1)) := by
        linarith [hd1.2, sq_nonneg ‖w‖]
      have hup' := le_of_mul_le_mul_left hup (by positivity)
      have e1 : ‖w‖ * (‖g‖ + 1) ≤ l * (‖g‖ + 1) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have e2 : ‖w‖ * ‖g‖ ≤ l * ‖g‖ := mul_le_mul_of_nonneg_right (by linarith) hng
      have e3 : α * ‖w‖ ^ 2 ≤ α * l := by
        refine mul_le_mul_of_nonneg_left ?_ hα
        have := mul_le_mul hw1 hwl hwn zero_le_one
        linarith
      have e4 : 0 ≤ l * α := mul_nonneg hl.le hα
      rw [abs_lt]
      constructor <;> linarith [hg1.1]
    · -- the subgradient
      have hux : u - x = l • g + (d - w) := by rw [hd_def, hw_def]; abel
      rw [hv₀, ← map_sub, LinearIsometryEquiv.norm_map, hux, smul_add, smul_smul, hll, one_smul,
        add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hl.le),
        inv_mul_lt_iff₀ hl]
      calc ‖d - w‖ ≤ ‖d‖ + ‖w‖ := norm_sub_le _ _
        _ < l * ε := by linarith [mul_pos hl hε]
  -- every proximal point lies in the localization
  have hloc : ∀ u ∈ ball (x₀ + l • g) δ, ∀ x ∈ proximalMap φ l u,
      toDual ℝ E (l⁻¹ • (u - x)) ∈ attentiveLocalization (subdiff φ) φ x₀ v₀ ε x := by
    intro u hu x hx
    obtain ⟨s, hs, hx4, hsε, hvε⟩ := claim u hu x (hx x₀)
    have hu' := hu
    rw [mem_ball, dist_eq_norm] at hu'
    refine ⟨regularSubdiff_subset_subdiff (toDual_mem_regularSubdiff_of_mem_proximalMap hs hx),
      by linarith, hvε, s, hs, by rwa [hr₀, EReal.toReal_coe]⟩
  -- existence of proximal points
  have hex : ∀ u ∈ ball (x₀ + l • g) δ, ∃ x, x ∈ proximalMap φ l u := by
    intro u hu
    have hu' := hu
    rw [mem_ball, dist_eq_norm] at hu'
    have hψlsc : LowerSemicontinuousOn (proxObjective φ l u) (closedBall x₀ ε₀) := fun y _ ↦
      (LowerSemicontinuousAt.add' (hlsc y)
        (continuous_coe_real_ereal.comp (by fun_prop :
          Continuous fun z : E ↦ (2 * l)⁻¹ * ‖z - u‖ ^ 2)).continuousAt.lowerSemicontinuousAt
        (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _))
          (Or.inr (EReal.coe_ne_top _)))).lowerSemicontinuousWithinAt _
    obtain ⟨xb, hxbK, hxbmin⟩ := hψlsc.exists_isMinOn (nonempty_closedBall.2 hε₀.le)
      (isCompact_closedBall x₀ ε₀)
    have hx₀K : x₀ ∈ closedBall x₀ ε₀ := mem_closedBall_self hε₀.le
    refine ⟨xb, fun y ↦ ?_⟩
    by_cases hy : y ∈ closedBall x₀ ε₀
    · exact hxbmin hy
    by_cases hyle : proxObjective φ l u y ≤ proxObjective φ l u x₀
    · obtain ⟨-, -, hy4, -⟩ := claim u hu y hyle
      exact absurd (by rw [mem_closedBall, dist_eq_norm]; linarith) hy
    · exact (hxbmin hx₀K).trans (not_le.1 hyle).le
  choose! p hp using hex
  have hmono : ∀ u₁ u₂ x₁ x₂, toDual ℝ E (l⁻¹ • (u₁ - x₁)) ∈
      attentiveLocalization (subdiff φ) φ x₀ v₀ ε x₁ → toDual ℝ E (l⁻¹ • (u₂ - x₂)) ∈
      attentiveLocalization (subdiff φ) φ x₀ v₀ ε x₂ → ‖x₁ - x₂‖ ≤ 2 * ‖u₁ - u₂‖ := by
    intro u₁ u₂ x₁ x₂ h₁ h₂
    have hinv : (1 - l * η)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    exact (hT.norm_sub_le hl (by linarith) trivial trivial h₁ h₂).trans
      (mul_le_mul_of_nonneg_right hinv (norm_nonneg _))
  have huniq : ∀ u ∈ ball (x₀ + l • g) δ, ∀ x, toDual ℝ E (l⁻¹ • (u - x)) ∈
      attentiveLocalization (subdiff φ) φ x₀ v₀ ε x → x = p u := by
    intro u hu x hx
    have := hmono u u x (p u) hx (hloc u hu _ (hp u hu))
    rw [sub_self, norm_zero, mul_zero] at this
    exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
  have hcenter : x₀ + l • g ∈ ball (x₀ + l • g) δ := mem_ball_self hδ
  refine ⟨p, ?_, fun u hu ↦ ?_, ?_, fun u hu ↦ hloc u hu _ (hp u hu), huniq⟩
  · refine (huniq _ hcenter x₀ ?_).symm
    rw [add_sub_cancel_left, smul_smul, hll, one_smul]
    refine ⟨hφ.1, by simpa using hε, by simp [hv₀, hε], r₀, hr₀, by simpa [hr₀] using hε⟩
  · ext x
    exact ⟨fun hx ↦ huniq u hu x (hloc u hu x hx), fun hx ↦ hx ▸ hp u hu⟩
  · refine LipschitzOnWith.of_dist_le_mul fun u₁ hu₁ u₂ hu₂ ↦ ?_
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_ofNat]
    exact hmono u₁ u₂ _ _ (hloc u₁ hu₁ _ (hp u₁ hu₁)) (hloc u₂ hu₂ _ (hp u₂ hu₂))

/-- [Mordukhovich 2024, Thm. 1.71, (1.94)] (Moreau envelopes of prox-regular functions): under
the assumptions of Thm. 1.70, for each small `λ > 0` the Moreau envelope `e_λφ` is finite and of
class `C^{1,1}` on a ball `U_λ` around `x̄ + λg`, with `∇e_λφ = λ⁻¹(I - P_λφ)`. -/
theorem ProxRegularFor.exists_moreauEnvelope {g : E} (hφ : ProxRegularFor φ x₀ (toDual ℝ E g))
    (hlsc : ∀ x, LowerSemicontinuousAt φ x)
    (hbd : ∃ a b : ℝ, ∀ x, ((a - b * ‖x - x₀‖ ^ 2 : ℝ) : EReal) ≤ φ x) :
    ∃ l₀ > (0 : ℝ), ∀ l, 0 < l → l < l₀ → ∃ δ > (0 : ℝ), ∃ p : E → E,
      (∀ u ∈ ball (x₀ + l • g) δ, proximalMap φ l u = {p u}) ∧
      (∀ u ∈ ball (x₀ + l • g) δ,
        (((moreauEnvelope φ l u).toReal : ℝ) : EReal) = moreauEnvelope φ l u) ∧
      (∀ u ∈ ball (x₀ + l • g) δ, HasFDerivAt (fun u ↦ (moreauEnvelope φ l u).toReal)
        (toDual ℝ E (l⁻¹ • (u - p u))) u) ∧
      LipschitzOnWith (Real.toNNReal (3 / l)) (fun u ↦ l⁻¹ • (u - p u))
        (ball (x₀ + l • g) δ) := by
  obtain ⟨ε, -, l₀, hl₀, H⟩ := hφ.exists_proximalMap hlsc hbd
  refine ⟨l₀, hl₀, fun l hl hll₀ ↦ ?_⟩
  obtain ⟨δ, hδ, p, -, hpU, hLip, hloc, -⟩ := H l hl hll₀
  refine ⟨δ, hδ, p, hpU, ?_⟩
  set U := ball (x₀ + l • g) δ with hU
  have hpmem : ∀ u ∈ U, p u ∈ proximalMap φ l u := fun u hu ↦ by rw [hpU u hu]; rfl
  have hfin : ∀ u ∈ U, φ (p u) = ((φ (p u)).toReal : EReal) := fun u hu ↦ by
    obtain ⟨-, -, -, s, hs, -⟩ := hloc u hu
    rw [hs, EReal.toReal_coe]
  set k := (2 * l)⁻¹ with hk
  have hkpos : 0 < k := by positivity
  have henv : ∀ u ∈ U,
      moreauEnvelope φ l u = (((φ (p u)).toReal + k * ‖p u - u‖ ^ 2 : ℝ) : EReal) :=
    fun u hu ↦ by
      rw [moreauEnvelope_eq_of_mem_proximalMap (hpmem u hu), proxObjective, EReal.coe_add,
        ← hfin u hu]
  have henv' : ∀ u ∈ U, (moreauEnvelope φ l u).toReal = (φ (p u)).toReal + k * ‖p u - u‖ ^ 2 :=
    fun u hu ↦ by rw [henv u hu, EReal.toReal_coe]
  -- global minimality of the proximal points
  have hmin : ∀ u ∈ U, ∀ y ∈ U,
      (moreauEnvelope φ l u).toReal ≤ (φ (p y)).toReal + k * ‖p y - u‖ ^ 2 := by
    intro u hu y hy
    have := hpmem u hu (p y)
    rw [proxObjective, proxObjective, hfin u hu, hfin y hy, ← EReal.coe_add, ← EReal.coe_add,
      EReal.coe_le_coe_iff] at this
    rw [henv' u hu]
    exact this
  refine ⟨fun u hu ↦ by rw [henv u hu, EReal.toReal_coe], fun u hu ↦ ?_, ?_⟩
  · rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    refine IsBigO.trans_isLittleO (g := fun h : E ↦ ‖h‖ ^ 2) ?_ (isLittleO_norm_pow_id one_lt_two)
    refine IsBigO.of_bound (4 * k) ?_
    have hev : ∀ᶠ h in 𝓝 (0 : E), u + h ∈ U :=
      ((continuous_const_add u).tendsto' 0 u (add_zero u)).eventually (isOpen_ball.mem_nhds hu)
    filter_upwards [hev] with h hh
    rw [Real.norm_eq_abs, norm_pow, norm_norm, abs_le]
    have hup := hmin (u + h) hh u hu
    have hlo := hmin u hu (u + h) hh
    rw [henv' (u + h) hh] at hup
    rw [henv' u hu] at hlo
    rw [henv' (u + h) hh, henv' u hu]
    set x := p u
    set x' := p (u + h)
    have hxx : ‖x' - x‖ ≤ 2 * ‖h‖ := by
      have := hLip.dist_le_mul (u + h) hh u hu
      rwa [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, NNReal.coe_ofNat] at this
    have hin := real_inner_le_norm (x' - x) h
    have hin' : k * ⟪x' - x, h⟫_ℝ ≤ k * (2 * ‖h‖ ^ 2) := by
      refine mul_le_mul_of_nonneg_left (hin.trans ?_) hkpos.le
      nlinarith [norm_nonneg h]
    have e1 : x - (u + h) = (x - u) - h := by abel
    have e2 : x' - u = (x' - (u + h)) + h := by abel
    have e3 : ⟪x' - (u + h), h⟫_ℝ = ⟪x - u, h⟫_ℝ + ⟪x' - x, h⟫_ℝ - ‖h‖ ^ 2 := by
      rw [show x' - (u + h) = (x - u) + (x' - x) - h by abel, inner_sub_left, inner_add_left,
        real_inner_self_eq_norm_sq]
    have e4 : toDual ℝ E (l⁻¹ • (u - x)) h = -(2 * k * ⟪x - u, h⟫_ℝ) := by
      rw [toDual_apply_apply, real_inner_smul_left, ← neg_sub, inner_neg_left, hk, mul_inv,
        ← mul_assoc, mul_inv_cancel₀ (two_ne_zero' ℝ), one_mul, mul_neg]
    rw [e1, norm_sub_sq_real (x - u) h] at hup
    rw [e2, norm_add_sq_real (x' - (u + h)) h, e3] at hlo
    rw [e4]
    have hkh := mul_nonneg hkpos.le (sq_nonneg ‖h‖)
    constructor <;> linarith
  · refine LipschitzOnWith.of_dist_le_mul fun u₁ hu₁ u₂ hu₂ ↦ ?_
    have := hLip.dist_le_mul u₁ hu₁ u₂ hu₂
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_ofNat] at this
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity), ← smul_sub,
      norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hl.le),
      show u₁ - p u₁ - (u₂ - p u₂) = (u₁ - u₂) - (p u₁ - p u₂) by abel, div_eq_mul_inv,
      mul_comm 3, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hl.le)
    linarith [norm_sub_le (u₁ - u₂) (p u₁ - p u₂)]

/-- [Mordukhovich 2024, Cor. 1.72]: if `φ` is continuously prox-regular at `x̄` for
`v̄ = ⟨g, ·⟩`, then the subgradient mapping `∂φ` is graphically Lipschitzian of dimension
`n = dim E` around `(x̄, v̄)`. The transformation is `(x, v) ↦ (x + λv, v)` and the Lipschitz
mapping is `λ⁻¹(I - P_λφ̃)`, where `φ̃` is `φ` plus the indicator function of a small closed
ball. -/
theorem ContinuouslyProxRegularFor.graphicallyLipschitzianAt {g : E}
    (hφ : ContinuouslyProxRegularFor φ x₀ (toDual ℝ E g)) :
    GraphicallyLipschitzianAt (subdiffMap φ) (x₀, g) := by
  classical
  obtain ⟨hpr, hsc⟩ := hφ
  set v₀ := toDual ℝ E g with hv₀
  obtain ⟨r₀, hr₀, -⟩ := hpr.1
  obtain ⟨δl, hδl, Hlsc⟩ := Metric.eventually_nhds_iff.1 hpr.2.1
  obtain ⟨r₀', hr₀', ε₀, hε₀, α, hα, Hprox⟩ := hpr.mem_proxSubdiff
  have hrr : r₀' = r₀ := by rw [hr₀] at hr₀'; exact_mod_cast hr₀'.symm
  rw [hrr] at Hprox
  obtain ⟨ρ, hρ, hρl, hρ0⟩ : ∃ ρ > (0 : ℝ), ρ < δl ∧ ρ ≤ ε₀ :=
    ⟨min (δl / 2) ε₀, lt_min (half_pos hδl) hε₀,
      (min_le_left _ _).trans_lt (half_lt_self hδl), min_le_right _ _⟩
  -- the localized function `φ + δ_{B̄(x̄, ρ)}`
  set ψ : E → EReal := fun x ↦ if x ∈ closedBall x₀ ρ then φ x else ⊤ with hψ_def
  have hψeq : ∀ x ∈ closedBall x₀ ρ, ψ x = φ x := fun x hx ↦ if_pos hx
  have hψtop : ∀ x ∉ closedBall x₀ ρ, ψ x = ⊤ := fun x hx ↦ if_neg hx
  have hψball : ∀ x ∈ ball x₀ ρ, ψ x = φ x := fun x hx ↦ hψeq x (ball_subset_closedBall hx)
  have hψS : ∀ x ∈ ball x₀ ρ, subdiff ψ x = subdiff φ x := fun x hx ↦
    subdiff_congr (eventually_of_mem (isOpen_ball.mem_nhds hx) hψball)
  have hψpr : ProxRegularFor ψ x₀ v₀ := hpr.congr hρ hψball
  have hψlsc : ∀ x, LowerSemicontinuousAt ψ x := by
    intro y c hc
    by_cases hy : y ∈ closedBall x₀ ρ
    · rw [hψeq y hy] at hc
      have hyl : dist y x₀ < δl := (mem_closedBall.1 hy).trans_lt hρl
      filter_upwards [Hlsc hyl c hc] with z hz
      by_cases hz' : z ∈ closedBall x₀ ρ
      · rwa [hψeq z hz']
      · rw [hψtop z hz']; exact hz.trans_le le_top
    · rw [hψtop y hy] at hc
      filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hy] with z hz
      rw [hψtop z hz]; exact hc
  have hψbd : ∃ a b : ℝ, ∀ x, ((a - b * ‖x - x₀‖ ^ 2 : ℝ) : EReal) ≤ ψ x := by
    refine ⟨r₀ - ‖g‖ * ρ - α / 2 * ρ ^ 2, 0, fun x ↦ ?_⟩
    by_cases hx : x ∈ closedBall x₀ ρ
    · rw [hψeq x hx]
      have hxn : ‖x - x₀‖ ≤ ρ := by rw [← dist_eq_norm]; exact mem_closedBall.1 hx
      refine le_trans (EReal.coe_le_coe_iff.2 ?_) (Hprox x (hxn.trans hρ0))
      rw [hv₀, toDual_apply_apply]
      have h1 := abs_le.1 (abs_real_inner_le_norm g (x - x₀))
      have h2 : ‖g‖ * ‖x - x₀‖ ≤ ‖g‖ * ρ := mul_le_mul_of_nonneg_left hxn (norm_nonneg g)
      have h3 : ‖x - x₀‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxn 2
      have h4 := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ α / 2)
      linarith [h1.1]
    · rw [hψtop x hx]; exact le_top
  -- the proximal mapping of `ψ`
  obtain ⟨ε, hε, l₀, hl₀, H⟩ := hψpr.exists_proximalMap hψlsc hψbd
  set l := l₀ / 2 with hl_def
  have hl : 0 < l := half_pos hl₀
  obtain ⟨δ, hδ, p, hp0, -, hLip, hloc, huniq⟩ := H l hl (half_lt_self hl₀)
  -- subdifferential continuity
  obtain ⟨r₁, hr₁, hcont⟩ : ∃ r₁ > (0 : ℝ), ∀ x (v : StrongDual ℝ E), ‖x - x₀‖ < r₁ →
      ‖v - v₀‖ < r₁ → v ∈ subdiff φ x → ∃ s : ℝ, φ x = s ∧ |s - r₀| < ε := by
    have ht := hsc.tendsto
    rw [hr₀] at ht
    have hI : Ioo ((r₀ - ε : ℝ) : EReal) ((r₀ + ε : ℝ) : EReal) ∈ 𝓝 ((r₀ : ℝ) : EReal) :=
      Ioo_mem_nhds (EReal.coe_lt_coe_iff.2 (by linarith)) (EReal.coe_lt_coe_iff.2 (by linarith))
    obtain ⟨O, hO, hO0, hOs⟩ := mem_nhdsWithin.1 (ht hI)
    obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.1 hO _ hO0
    refine ⟨r₁, hr₁, fun x v hx hv hvx ↦ ?_⟩
    have hmem : (x, v) ∈ O := hball (by
      rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm]; exact ⟨hx, hv⟩)
    obtain ⟨s, hs, hs1, hs2⟩ := exists_real_of_mem_Ioo (hOs ⟨hmem, hvx⟩)
    exact ⟨s, hs, abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩⟩
  -- the radii
  obtain ⟨τ, hτ, hτr, hτε, hτρ⟩ : ∃ τ > (0 : ℝ), τ ≤ r₁ ∧ τ ≤ ε ∧ τ < ρ :=
    ⟨min (min r₁ ε) (ρ / 2), lt_min (lt_min hr₁ hε) (half_pos hρ),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans_lt (half_lt_self hρ)⟩
  obtain ⟨δ', hδ', hδ'δ, hδ'τ, hδ'τl⟩ : ∃ δ' > (0 : ℝ), δ' ≤ δ ∧ 4 * δ' ≤ τ ∧ 4 * δ' ≤ τ * l := by
    refine ⟨min δ (min (τ / 4) (τ * l / 4)), lt_min hδ (lt_min (by positivity) (by positivity)),
      min_le_left _ _, ?_, ?_⟩
    · have := (min_le_right δ _).trans (min_le_left (τ / 4) (τ * l / 4)); linarith
    · have := (min_le_right δ _).trans (min_le_right (τ / 4) (τ * l / 4)); linarith
  -- the transformation `(x, v) ↦ (x + λv, v)`
  set A : (E × E) →L[ℝ] (E × E) :=
    (ContinuousLinearMap.fst ℝ E E + l • ContinuousLinearMap.snd ℝ E E).prod
      (ContinuousLinearMap.snd ℝ E E) with hA_def
  set A' : (E × E) →L[ℝ] (E × E) :=
    (ContinuousLinearMap.fst ℝ E E - l • ContinuousLinearMap.snd ℝ E E).prod
      (ContinuousLinearMap.snd ℝ E E) with hA'_def
  have hA : ∀ q : E × E, A q = (q.1 + l • q.2, q.2) := fun q ↦ rfl
  have hA' : ∀ q : E × E, A' q = (q.1 - l • q.2, q.2) := fun q ↦ rfl
  have hleft : Function.LeftInverse A' A := fun q ↦ by rw [hA, hA']; simp
  have hright : Function.RightInverse A' A := fun q ↦ by rw [hA', hA]; simp
  set f : E → E := fun u ↦ l⁻¹ • (u - p u) with hf
  set U := ball (x₀ + l • g) δ' with hU
  set W : Set (E × E) := {q | dist q.1 x₀ < τ ∧ dist q.2 g < τ ∧
    dist (q.1 + l • q.2) (x₀ + l • g) < δ'} with hW
  have hc : x₀ + l • g ∈ ball (x₀ + l • g) δ := mem_ball_self hδ
  have hdual : ∀ y : E, ‖toDual ℝ E y - v₀‖ = dist y g := fun y ↦ by
    rw [hv₀, ← map_sub, LinearIsometryEquiv.norm_map, dist_eq_norm]
  refine ⟨mem_subdiffMap_iff.2 hpr.1, W, A, fun _ ↦ A, U, f, Real.toNNReal (3 / l),
    ⟨by simpa using hτ, by simpa using hτ, by simpa using hδ'⟩, ?_⟩
  refine
    { isOpen_W := ?_
      isOpen_U := isOpen_ball
      hasStrictFDerivAt := fun _ _ ↦ A.hasStrictFDerivAt
      continuousOn := continuousOn_const
      exists_equiv := fun _ _ ↦ ⟨ContinuousLinearEquiv.equivOfInverse A A' hleft hright, rfl⟩
      injOn := fun q₁ _ q₂ _ h ↦ by rw [← hleft q₁, ← hleft q₂, h]
      lipschitzOnWith := ?_
      image_eq := ?_ }
  · have c1 : Continuous fun q : E × E ↦ dist q.1 x₀ := by fun_prop
    have c2 : Continuous fun q : E × E ↦ dist q.2 g := by fun_prop
    have c3 : Continuous fun q : E × E ↦ dist (q.1 + l • q.2) (x₀ + l • g) := by fun_prop
    exact (isOpen_lt c1 continuous_const).inter
      ((isOpen_lt c2 continuous_const).inter (isOpen_lt c3 continuous_const))
  · refine LipschitzOnWith.of_dist_le_mul fun u₁ hu₁ u₂ hu₂ ↦ ?_
    have := hLip.dist_le_mul u₁ (ball_subset_ball hδ'δ hu₁) u₂ (ball_subset_ball hδ'δ hu₂)
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_ofNat] at this
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity), hf, ← smul_sub,
      norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hl.le),
      show u₁ - p u₁ - (u₂ - p u₂) = (u₁ - u₂) - (p u₁ - p u₂) by abel, div_eq_mul_inv,
      mul_comm 3, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hl.le)
    linarith [norm_sub_le (u₁ - u₂) (p u₁ - p u₂)]
  · apply Set.ext
    rintro ⟨u, y⟩
    constructor
    · rintro ⟨⟨x, y'⟩, ⟨hgr, hx1, hx2, hx3⟩, hAq⟩
      rw [hA, Prod.mk.injEq] at hAq
      obtain ⟨rfl, rfl⟩ := hAq
      have hx1' : dist x x₀ < τ := hx1
      have hx2' : dist y' g < τ := hx2
      have hx3' : dist (x + l • y') (x₀ + l • g) < δ' := hx3
      have hgr' : toDual ℝ E y' ∈ subdiff φ x := mem_subdiffMap_iff.1 hgr
      have hxρ : x ∈ ball x₀ ρ := by rw [mem_ball]; linarith
      have hu : x + l • y' ∈ ball (x₀ + l • g) δ := ball_subset_ball hδ'δ hx3'
      have hxe : x = p (x + l • y') := by
        refine huniq _ hu x ?_
        rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hl.ne', one_smul]
        obtain ⟨s, hs, hsr⟩ := hcont x (toDual ℝ E y') (by rw [← dist_eq_norm]; linarith)
          (by rw [hdual]; linarith) hgr'
        refine ⟨by rwa [hψS x hxρ], by rw [← dist_eq_norm]; linarith, by rw [hdual]; linarith,
          s, by rw [hψball x hxρ, hs], ?_⟩
        rwa [hψball x₀ (mem_ball_self hρ), hr₀, EReal.toReal_coe]
      refine ⟨?_, hx3', mem_univ _⟩
      change y' ∈ ({f (x + l • y')} : Set E)
      rw [mem_singleton_iff, hf]
      dsimp only
      rw [← hxe, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hl.ne', one_smul]
    · rintro ⟨hy, hu, -⟩
      have hy' : y = f u := hy
      subst hy'
      have hu' : dist u (x₀ + l • g) < δ' := hu
      have huδ : u ∈ ball (x₀ + l • g) δ := ball_subset_ball hδ'δ hu
      have hpu : ‖p u - x₀‖ ≤ 2 * ‖u - (x₀ + l • g)‖ := by
        have := hLip.dist_le_mul u huδ (x₀ + l • g) hc
        rwa [dist_eq_norm, dist_eq_norm, hp0, NNReal.coe_ofNat] at this
      rw [dist_eq_norm] at hu'
      have hpuτ : ‖p u - x₀‖ < τ := by linarith
      have hpuρ : p u ∈ ball x₀ ρ := by rw [mem_ball, dist_eq_norm]; linarith
      have hfu : f u = l⁻¹ • ((u - (x₀ + l • g)) - (p u - x₀)) + g := by
        rw [show (u - (x₀ + l • g)) - (p u - x₀) = (u - p u) - l • g by abel, smul_sub (l⁻¹),
          smul_smul, inv_mul_cancel₀ hl.ne', one_smul, sub_add_cancel]
      have hpf : p u + l • f u = u := by
        rw [hf]; dsimp only
        rw [smul_smul, mul_inv_cancel₀ hl.ne', one_smul, add_sub_cancel]
      refine ⟨(p u, f u), ⟨mem_subdiffMap_iff.2 ?_, ?_, ?_, ?_⟩, ?_⟩
      · have := (hloc u huδ).1
        rwa [hψS (p u) hpuρ] at this
      · change dist (p u) x₀ < τ
        rwa [dist_eq_norm]
      · change dist (f u) g < τ
        rw [dist_eq_norm, hfu, add_sub_cancel_right, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.2 hl.le), inv_mul_lt_iff₀ hl]
        calc ‖(u - (x₀ + l • g)) - (p u - x₀)‖ ≤ ‖u - (x₀ + l • g)‖ + ‖p u - x₀‖ :=
              norm_sub_le _ _
          _ < l * τ := by linarith
      · change dist (p u + l • f u) (x₀ + l • g) < δ'
        rw [hpf, dist_eq_norm]; exact hu'
      · rw [hA]; dsimp only; rw [hpf]

/-- [Gfrerer–Outrata 2022, Prop. 3.26], SCD part: the subgradient mapping of a function
prox-regular and subdifferentially continuous at `x̄` for `v̄ = ⟨g, ·⟩` has the SCD property
around `(x̄, g)`. -/
theorem ContinuouslyProxRegularFor.hasSCDPropertyAround {g : E}
    (hφ : ContinuouslyProxRegularFor φ x₀ (toDual ℝ E g)) :
    HasSCDPropertyAround (subdiffMap φ) (x₀, g) :=
  hφ.graphicallyLipschitzianAt.hasSCDPropertyAround

end Main

end VariationalAnalysis
