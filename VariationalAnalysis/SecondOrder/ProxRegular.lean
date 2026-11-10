/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import VariationalAnalysis.WellPosedness.ProxRegular

/-!
# Prox-regularity and hypomonotonicity

This file follows [Mordukhovich 2024, Subsect. 1.3.2]: prox-regularity of `φ` at `x̄` for
`v̄ ∈ ∂φ(x̄)` is characterized by the proximal subgradient condition `v̄ ∈ ∂_P φ(x̄)` together
with the hypomonotonicity of a `φ`-attentive localization of `∂φ` around `(x̄, v̄)`.

Prox-regularity is `ProxRegularFor` (Def. 3.27 of [Mordukhovich 2018]); it agrees with
[Mordukhovich 2024, Def. 1.56] up to the bookkeeping of the constants (the library asks for
`φ(x) ≤ φ(x̄) + ε` where the book asks for `|φ(x) - φ(x̄)| ≤ ε`, which is equivalent under lower
semicontinuity).

## Main declarations

* `proxSubdiff φ x₀`: the proximal subdifferential [Mordukhovich 2024, (1.80)].
* `attentiveLocalization T φ x₀ v₀ ε`: the `φ`-attentive `ε`-localization of a subgradient
  mapping `T` around `(x₀, v₀)` [Mordukhovich 2024, Def. 1.62, (1.76)]; it is applied to
  `T = ∂φ` and `T = ∂̂φ`.
* `IsHypomonotoneOn ρ T U`: `ρ`-hypomonotonicity on `U` [Mordukhovich 2024, Def. 1.63(ii)];
  global monotonicity is `GloballyMonotone` (`globallyMonotone_iff_isHypomonotoneOn`).

## Main results

* `proxSubdiff_subset_regularSubdiff`: `∂_P φ(x̄) ⊆ ∂̂φ(x̄)`.
* `ProxRegularFor.isHypomonotoneOn_attentiveLocalization`, `ProxRegularFor.mem_proxSubdiff`:
  [Mordukhovich 2024, Thm. 1.65], (i) ⇒ (ii).
* `ProxRegularFor.of_isHypomonotoneOn`: [Mordukhovich 2024, Thm. 1.65], (ii) ⇒ (i), in finite
  dimensional inner product spaces, from the hypomonotonicity of the localization of `∂φ`
  alone.
* `proxRegularFor_iff_isHypomonotoneOn`: [Mordukhovich 2024, Thm. 1.65], the book's form (both
  localizations).
* `proxRegularFor_iff_isHypomonotoneOn_subdiff`: the same with the basic localization only.
* `proxRegularFor_iff_locallyHypomonotoneAt`: [Mordukhovich 2024, Thm. 1.65], last statement:
  under subdifferential continuity, the ordinary localization of `∂φ` can be used.

## Proof of (ii) ⇒ (i)

The book argues in Asplund spaces with Ekeland's principle and the fuzzy sum rule; in finite
dimensions the minimizer exists, which gives the simplified argument of
[Mordukhovich 2024, Exercise 1.121]. Fix `(u, u*)` in the localization and let
`ψ(z) = φ(z) - ⟨u*, z⟩ + (r/2)‖z - u‖²` with `r` larger than the hypomonotonicity modulus and
`4α + 8`, where `α` is the proximal modulus of `v̄`. A minimizer `z̄` of `ψ` over a small closed
ball around `x̄` lies in the open ball (Lemma 1.64), so the Fermat rule gives
`w* = u* - r⟨z̄ - u, ·⟩ ∈ ∂φ(z̄)`, and `(z̄, w*)` lies in the localization. Hypomonotonicity
yields `(r - ρ)‖z̄ - u‖² ≤ 0`, i.e. `z̄ = u`, and `ψ(u) ≤ ψ(z)` is the prox-regularity inequality.
-/

open Filter Topology Set Metric ContinuousLinearMap
open scoped NNReal RealInnerProductSpace

namespace VariationalAnalysis

section Defs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {φ : E → EReal} {x₀ : E} {v₀ : StrongDual ℝ E}

/-- [Mordukhovich 2024, (1.80)] (proximal subdifferential): `v ∈ ∂_P φ(x₀)` if `φ(x₀)` is
finite and `φ(x) ≥ φ(x₀) + ⟨v, x - x₀⟩ - (ρ/2)‖x - x₀‖²` for `‖x - x₀‖ ≤ ε`, for some
`ε > 0` and `ρ ≥ 0`. -/
def proxSubdiff (φ : E → EReal) (x₀ : E) : Set (StrongDual ℝ E) :=
  {v | ∃ r : ℝ, φ x₀ = r ∧ ∃ ε > (0 : ℝ), ∃ ρ ≥ (0 : ℝ), ∀ x, ‖x - x₀‖ ≤ ε →
    ((r + v (x - x₀) - ρ / 2 * ‖x - x₀‖ ^ 2 : ℝ) : EReal) ≤ φ x}

/-- Proximal subgradients are regular subgradients: `∂_P φ(x₀) ⊆ ∂̂φ(x₀)`. -/
theorem proxSubdiff_subset_regularSubdiff : proxSubdiff φ x₀ ⊆ regularSubdiff φ x₀ := by
  rintro v ⟨r, hr, ε, hε, ρ, hρ, H⟩
  refine ⟨r, hr, fun ε' hε' ↦ ?_⟩
  have hδ : 0 < min ε (2 * ε' / (ρ + 1)) := lt_min hε (by positivity)
  filter_upwards [ball_mem_nhds x₀ hδ] with x hx
  rw [mem_ball, dist_eq_norm] at hx
  have h1 : ‖x - x₀‖ ≤ ε := hx.le.trans (min_le_left _ _)
  have h2 : ‖x - x₀‖ ≤ 2 * ε' / (ρ + 1) := hx.le.trans (min_le_right _ _)
  refine le_trans (EReal.coe_le_coe_iff.2 ?_) (H x h1)
  have hn := norm_nonneg (x - x₀)
  have h3 : (ρ + 1) * ‖x - x₀‖ ≤ 2 * ε' := by
    rwa [le_div_iff₀ (by positivity), mul_comm] at h2
  nlinarith

/-- Proximal subgradients are basic subgradients. -/
theorem proxSubdiff_subset_subdiff : proxSubdiff φ x₀ ⊆ subdiff φ x₀ :=
  proxSubdiff_subset_regularSubdiff.trans regularSubdiff_subset_subdiff

/-- [Mordukhovich 2024, Def. 1.62, (1.76)] (`φ`-attentive `ε`-localization of a subgradient
mapping `T`, e.g. `T = ∂φ` or `T = ∂̂φ`, around `(x₀, v₀)`): its graph consists of the
`(x, v) ∈ gph T` with `‖x - x₀‖ < ε`, `‖v - v₀‖ < ε` and `|φ(x) - φ(x₀)| < ε`. -/
def attentiveLocalization (T : E → Set (StrongDual ℝ E)) (φ : E → EReal) (x₀ : E)
    (v₀ : StrongDual ℝ E) (ε : ℝ) (x : E) : Set (StrongDual ℝ E) :=
  {v | v ∈ T x ∧ ‖x - x₀‖ < ε ∧ ‖v - v₀‖ < ε ∧ ∃ r : ℝ, φ x = r ∧ |r - (φ x₀).toReal| < ε}

/-- [Mordukhovich 2024, Def. 1.63(ii), (1.78)]: `T : E ⇉ E*` is hypomonotone on `U` with
modulus `ρ` if `⟨v₁ - v₂, x₁ - x₂⟩ ≥ -ρ ‖x₁ - x₂‖²` for `(xᵢ, vᵢ) ∈ gph T`, `xᵢ ∈ U`. -/
def IsHypomonotoneOn (ρ : ℝ) (T : E → Set (StrongDual ℝ E)) (U : Set E) : Prop :=
  ∀ x₁ ∈ U, ∀ x₂ ∈ U, ∀ v₁ ∈ T x₁, ∀ v₂ ∈ T x₂, -(ρ * ‖x₁ - x₂‖ ^ 2) ≤ (v₁ - v₂) (x₁ - x₂)

/-- [Mordukhovich 2024, Def. 1.63(i)]: global monotonicity is `0`-hypomonotonicity on `E`. -/
theorem globallyMonotone_iff_isHypomonotoneOn {T : E → Set (StrongDual ℝ E)} :
    GloballyMonotone T ↔ IsHypomonotoneOn 0 T univ := by
  simp [GloballyMonotone, IsHypomonotoneOn]

theorem IsHypomonotoneOn.mono {ρ : ℝ} {T T' : E → Set (StrongDual ℝ E)} {U U' : Set E}
    (h : IsHypomonotoneOn ρ T U) (hT : ∀ x, T' x ⊆ T x) (hU : U' ⊆ U) :
    IsHypomonotoneOn ρ T' U' :=
  fun x₁ hx₁ x₂ hx₂ v₁ hv₁ v₂ hv₂ ↦ h x₁ (hU hx₁) x₂ (hU hx₂) v₁ (hT _ hv₁) v₂ (hT _ hv₂)

theorem IsHypomonotoneOn.mono_modulus {ρ ρ' : ℝ} {T : E → Set (StrongDual ℝ E)} {U : Set E}
    (h : IsHypomonotoneOn ρ T U) (hρ : ρ ≤ ρ') : IsHypomonotoneOn ρ' T U := by
  intro x₁ hx₁ x₂ hx₂ v₁ hv₁ v₂ hv₂
  have := h x₁ hx₁ x₂ hx₂ v₁ hv₁ v₂ hv₂
  nlinarith [sq_nonneg ‖x₁ - x₂‖]

theorem attentiveLocalization_subset {T T' : E → Set (StrongDual ℝ E)} (hT : ∀ x, T x ⊆ T' x)
    {ε : ℝ} (x : E) :
    attentiveLocalization T φ x₀ v₀ ε x ⊆ attentiveLocalization T' φ x₀ v₀ ε x :=
  fun _ ⟨hv, h⟩ ↦ ⟨hT x hv, h⟩

/-- `|⟨v, x⟩| ≤ ‖v‖ ‖x‖`, split into two inequalities. -/
theorem dual_bound (v : StrongDual ℝ E) (x : E) : -(‖v‖ * ‖x‖) ≤ v x ∧ v x ≤ ‖v‖ * ‖x‖ := by
  have := v.le_opNorm x
  rw [Real.norm_eq_abs] at this
  exact abs_le.1 this

end Defs

section Forward

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {φ : E → EReal} {x₀ : E} {v₀ : StrongDual ℝ E}

/-- [Mordukhovich 2024, Thm. 1.65], (i) ⇒ (ii), first part: a prox-regular subgradient is a
proximal subgradient. -/
theorem ProxRegularFor.mem_proxSubdiff (h : ProxRegularFor φ x₀ v₀) : v₀ ∈ proxSubdiff φ x₀ := by
  obtain ⟨hv₀, -, ε, hε, η, hη, H⟩ := h
  have ⟨r₀, hr₀, _⟩ := hv₀
  refine ⟨r₀, hr₀, ε, hε, η, hη, fun x hx ↦ ?_⟩
  have := H x₀ x v₀ hv₀ r₀ hr₀ (by simp [hε.le]) hx
    (by simp [hε.le]) (le_add_of_nonneg_right (EReal.coe_nonneg.2 hε.le))
  simpa using this

/-- The hypomonotonicity estimate behind prox-regularity [Mordukhovich 2024, proof of
Thm. 1.65]: for `(xᵢ, vᵢ)` in the prox-regularity neighborhood,
`⟨v₁ - v₂, x₁ - x₂⟩ ≥ -η ‖x₁ - x₂‖²`. -/
theorem ProxRegularFor.exists_hypomonotone (h : ProxRegularFor φ x₀ v₀) :
    ∃ ε > (0 : ℝ), ∃ η ≥ (0 : ℝ), ∀ x₁ x₂ : E, ∀ v₁ ∈ subdiff φ x₁, ∀ v₂ ∈ subdiff φ x₂,
      ∀ r₁ r₂ : ℝ, φ x₁ = r₁ → φ x₂ = r₂ → ‖v₁ - v₀‖ ≤ ε → ‖v₂ - v₀‖ ≤ ε →
        ‖x₁ - x₀‖ ≤ ε → ‖x₂ - x₀‖ ≤ ε → φ x₁ ≤ φ x₀ + ε → φ x₂ ≤ φ x₀ + ε →
          -(η * ‖x₁ - x₂‖ ^ 2) ≤ (v₁ - v₂) (x₁ - x₂) := by
  obtain ⟨-, -, ε, hε, η, hη, H⟩ := h
  refine ⟨ε, hε, η, hη, fun x₁ x₂ v₁ hv₁ v₂ hv₂ r₁ r₂ hr₁ hr₂ hv₁' hv₂' hx₁ hx₂ hf₁ hf₂ ↦ ?_⟩
  have h1 := H x₁ x₂ v₁ hv₁ r₁ hr₁ hv₁' hx₂ hx₁ hf₁
  have h2 := H x₂ x₁ v₂ hv₂ r₂ hr₂ hv₂' hx₁ hx₂ hf₂
  rw [hr₂, EReal.coe_le_coe_iff] at h1
  rw [hr₁, EReal.coe_le_coe_iff] at h2
  have e1 : v₁ (x₂ - x₁) = -v₁ (x₁ - x₂) := by rw [← map_neg, neg_sub]
  rw [norm_sub_rev x₂ x₁] at h1
  simp only [sub_apply]
  linarith

/-- [Mordukhovich 2024, Thm. 1.65], (i) ⇒ (ii), second part: for a function prox-regular at `x₀`
for `v₀`, some `φ`-attentive localization of `∂φ` around `(x₀, v₀)` is hypomonotone. -/
theorem ProxRegularFor.isHypomonotoneOn_attentiveLocalization (h : ProxRegularFor φ x₀ v₀) :
    ∃ ε > (0 : ℝ), ∃ ρ > (0 : ℝ),
      IsHypomonotoneOn ρ (attentiveLocalization (subdiff φ) φ x₀ v₀ ε) univ := by
  obtain ⟨r₀, hr₀, -⟩ := h.1
  obtain ⟨ε, hε, η, hη, H⟩ := h.exists_hypomonotone
  refine ⟨ε, hε, η + 1, by linarith, fun x₁ _ x₂ _ v₁ hv₁ v₂ hv₂ ↦ ?_⟩
  obtain ⟨hv₁, hx₁, hv₁', s₁, hs₁, hs₁'⟩ := hv₁
  obtain ⟨hv₂, hx₂, hv₂', s₂, hs₂, hs₂'⟩ := hv₂
  rw [hr₀, EReal.toReal_coe] at hs₁' hs₂'
  have hf : ∀ s : ℝ, |s - r₀| < ε → (s : EReal) ≤ φ x₀ + ε := fun s hs ↦ by
    rw [hr₀, ← EReal.coe_add, EReal.coe_le_coe_iff]
    linarith [le_abs_self (s - r₀)]
  have := H x₁ x₂ v₁ hv₁ v₂ hv₂ s₁ s₂ hs₁ hs₂ hv₁'.le hv₂'.le hx₁.le hx₂.le (hs₁ ▸ hf s₁ hs₁')
    (hs₂ ▸ hf s₂ hs₂')
  nlinarith [sq_nonneg ‖x₁ - x₂‖]

end Forward

section Backward

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {φ : E → EReal} {x₀ : E} {v₀ : StrongDual ℝ E}

omit [FiniteDimensional ℝ E] in
/-- The derivative of the quadratic perturbation `z ↦ -⟨w, z⟩ + (r/2)‖z - u‖²` in the proof
of [Mordukhovich 2024, Thm. 1.65]. -/
theorem hasFDerivAt_quadPerturb (w : StrongDual ℝ E) (r : ℝ) (u z : E) :
    HasFDerivAt (fun z ↦ -w z + r / 2 * ‖z - u‖ ^ 2) (-w + r • innerSL ℝ (z - u)) z := by
  have h1 : HasFDerivAt (fun z ↦ ‖z - u‖ ^ 2)
      (2 • (innerSL ℝ (z - u)).comp (ContinuousLinearMap.id ℝ E)) z :=
    ((hasFDerivAt_id z).sub_const u).norm_sq
  refine (w.hasFDerivAt.neg.add (h1.const_mul (r / 2))).congr_fderiv ?_
  ext y
  simp only [add_apply, neg_apply,
    smul_apply, comp_apply, id_apply,
    innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

/-- [Mordukhovich 2024, Thm. 1.65], (ii) ⇒ (i), in finite-dimensional inner product spaces: if
`v₀ ∈ ∂_P φ(x₀)`, `φ` is l.s.c. around `x₀` and some `φ`-attentive localization of `∂φ` around
`(x₀, v₀)` is hypomonotone, then `φ` is prox-regular at `x₀` for `v₀`. -/
theorem ProxRegularFor.of_isHypomonotoneOn (hlsc : ∀ᶠ x in 𝓝 x₀, LowerSemicontinuousAt φ x)
    (hP : v₀ ∈ proxSubdiff φ x₀) {ε' ρ' : ℝ} (hε' : 0 < ε')
    (hT : IsHypomonotoneOn ρ' (attentiveLocalization (subdiff φ) φ x₀ v₀ ε') univ) :
    ProxRegularFor φ x₀ v₀ := by
  obtain ⟨r₀, hr₀, ε₀, hε₀, α, hα, Hprox⟩ := hP
  have hv₀ : v₀ ∈ subdiff φ x₀ := proxSubdiff_subset_subdiff ⟨r₀, hr₀, ε₀, hε₀, α, hα, Hprox⟩
  obtain ⟨δl, hδl, Hlsc⟩ := Metric.eventually_nhds_iff.1 hlsc
  obtain ⟨a, ha_def⟩ : ∃ a, a = ‖v₀‖ := ⟨_, rfl⟩
  have ha : 0 ≤ a := ha_def ▸ norm_nonneg _
  obtain ⟨ρ, hρ, hT'⟩ : ∃ ρ ≥ (0 : ℝ),
      IsHypomonotoneOn ρ (attentiveLocalization (subdiff φ) φ x₀ v₀ ε') univ :=
    ⟨max ρ' 0, le_max_right _ _, hT.mono_modulus (le_max_left _ _)⟩
  -- the constants
  obtain ⟨r, hr_def⟩ : ∃ r, r = ρ + 4 * α + 8 := ⟨_, rfl⟩
  have hr : 0 < r := by rw [hr_def]; positivity
  obtain ⟨K, hK_def⟩ : ∃ K, K = 3 + 2 * a + α + 2 * r := ⟨_, rfl⟩
  have hK : 0 < K := by rw [hK_def]; positivity
  obtain ⟨R, hR, hRδl, hRε₀, hR1, hRK⟩ : ∃ R > (0 : ℝ), R < δl ∧ R ≤ ε₀ ∧ R ≤ 1 ∧
      R * K ≤ ε' / 2 := by
    refine ⟨min (min (δl / 2) ε₀) (min 1 (ε' / (2 * K))),
      lt_min (lt_min (half_pos hδl) hε₀) (lt_min one_pos (by positivity)),
      (min_le_left _ _).trans_lt ((min_le_left _ _).trans_lt (half_lt_self hδl)),
      (min_le_left _ _).trans (min_le_right _ _), (min_le_right _ _).trans (min_le_left _ _), ?_⟩
    have : min (min (δl / 2) ε₀) (min 1 (ε' / (2 * K))) ≤ ε' / (2 * K) :=
      (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  obtain ⟨δ, hδ, hδR, hδ3⟩ : ∃ δ > (0 : ℝ), δ ≤ R / 2 ∧ δ * (3 + a) ≤ R ^ 2 / 2 := by
    refine ⟨min (R / 2) (R ^ 2 / (2 * (3 + a))), lt_min (half_pos hR) (by positivity),
      min_le_left _ _, ?_⟩
    have : min (R / 2) (R ^ 2 / (2 * (3 + a))) ≤ R ^ 2 / (2 * (3 + a)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hKa : 3 + 2 * a + α + 2 * r ≤ K := hK_def.ge
  have hRε' : R < ε' := by
    have : R ≤ R * K := le_mul_of_one_le_right hR.le (by linarith)
    linarith
  -- the lower bound from the proximal subgradient
  have Hlow : ∀ z, ‖z - x₀‖ ≤ ε₀ →
      ((r₀ + v₀ (z - x₀) - α / 2 * ‖z - x₀‖ ^ 2 : ℝ) : EReal) ≤ φ z ∧ φ z ≠ ⊥ := fun z hz ↦ by
    have h := Hprox z hz
    refine ⟨h, fun hb ↦ ?_⟩
    rw [hb] at h
    exact EReal.coe_ne_bot _ (le_bot_iff.1 h)
  refine ⟨hv₀, hlsc, δ, hδ, r, hr.le, ?_⟩
  intro u z us hus t ht hus' hz hu hfu
  rw [hr₀, ← EReal.coe_add, ht, EReal.coe_le_coe_iff] at hfu
  have hδ1 : δ ≤ 1 := by linarith
  -- `t = φ u` is close to `r₀`
  have hu₀ : ‖u - x₀‖ ≤ ε₀ := by linarith
  have hv₀u := dual_bound v₀ (u - x₀)
  rw [← ha_def] at hv₀u
  have hau : a * ‖u - x₀‖ ≤ a * δ := mul_le_mul_of_nonneg_left hu ha
  have htlow : r₀ - a * δ - α * δ ≤ t := by
    have h := (Hlow u hu₀).1
    rw [ht, EReal.coe_le_coe_iff] at h
    have h3 : ‖u - x₀‖ ^ 2 ≤ δ := by
      rw [sq]
      calc ‖u - x₀‖ * ‖u - x₀‖ ≤ δ * 1 := mul_le_mul hu (by linarith) (norm_nonneg _) hδ.le
        _ = δ := mul_one δ
    have h4 := mul_le_mul_of_nonneg_left h3 (show 0 ≤ α / 2 by linarith)
    linarith [hv₀u.1, mul_nonneg hα hδ.le]
  -- the auxiliary function and its minimizer over the closed ball
  obtain ⟨h, h_def⟩ : ∃ h : E → ℝ, h = fun z ↦ -us z + r / 2 * ‖z - u‖ ^ 2 := ⟨_, rfl⟩
  have hhc : Continuous h := by rw [h_def]; fun_prop
  have hhu : h u = -us u := by rw [h_def]; simp
  have hhdiff : ∀ y, h y - h u = -us (y - u) + r / 2 * ‖y - u‖ ^ 2 := fun y ↦ by
    rw [h_def]; simp only [map_sub, sub_self, norm_zero]; ring
  obtain ⟨ψ, hψ_def⟩ : ∃ ψ : E → EReal, ψ = fun z ↦ φ z + (h z : EReal) := ⟨_, rfl⟩
  have hψ : ∀ y, ψ y = φ y + (h y : EReal) := fun y ↦ by rw [hψ_def]
  have hψlsc : LowerSemicontinuousOn ψ (closedBall x₀ R) := by
    intro y hy
    have hy' : dist y x₀ < δl := (mem_closedBall.1 hy).trans_lt hRδl
    rw [hψ_def]
    exact (LowerSemicontinuousAt.add' (Hlsc hy')
      (continuous_coe_real_ereal.comp hhc).continuousAt.lowerSemicontinuousAt
      (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _))
        (Or.inr (EReal.coe_ne_top _)))).lowerSemicontinuousWithinAt _
  obtain ⟨zb, hzbK, hzbmin⟩ := hψlsc.exists_isMinOn (nonempty_closedBall.2 hR.le)
    (isCompact_closedBall x₀ R)
  have hzbK' : ‖zb - x₀‖ ≤ R := by rw [← dist_eq_norm]; exact mem_closedBall.1 hzbK
  have huK : u ∈ closedBall x₀ R := by
    rw [mem_closedBall, dist_eq_norm]; linarith
  have hψu : ψ u = ((t + h u : ℝ) : EReal) := by rw [hψ, ht, EReal.coe_add]
  have hle0 : ψ zb ≤ ((t + h u : ℝ) : EReal) := hψu ▸ hzbmin huK
  rw [hψ] at hle0
  -- `φ zb` is finite
  obtain ⟨s, hs⟩ : ∃ s : ℝ, φ zb = s := by
    have hbot := (Hlow zb (hzbK'.trans hRε₀)).2
    induction hφ : φ zb with
    | bot => exact absurd hφ hbot
    | top =>
      rw [hφ, EReal.top_add_coe] at hle0
      exact absurd (top_le_iff.1 hle0) (EReal.coe_ne_top _)
    | coe s => exact ⟨s, rfl⟩
  have hM : s + h zb ≤ t + h u := by
    rwa [hs, ← EReal.coe_add, EReal.coe_le_coe_iff] at hle0
  have hL : r₀ + v₀ (zb - x₀) - α / 2 * ‖zb - x₀‖ ^ 2 ≤ s := by
    have := (Hlow zb (hzbK'.trans hRε₀)).1
    rwa [hs, EReal.coe_le_coe_iff] at this
  -- basic estimates
  have hus_norm : ‖us‖ ≤ a + δ := by
    calc ‖us‖ = ‖v₀ + (us - v₀)‖ := by rw [add_sub_cancel]
      _ ≤ ‖v₀‖ + ‖us - v₀‖ := norm_add_le _ _
      _ ≤ a + δ := by rw [← ha_def]; linarith
  have hzu : ‖zb - u‖ ≤ 2 * R := by
    calc ‖zb - u‖ = ‖(zb - x₀) - (u - x₀)‖ := by rw [sub_sub_sub_cancel_right]
      _ ≤ ‖zb - x₀‖ + ‖u - x₀‖ := norm_sub_le _ _
      _ ≤ 2 * R := by linarith
  have hzu0 := norm_nonneg (zb - u)
  have e4 := hhdiff zb
  have hus_zu := dual_bound us (zb - u)
  have hd_zu := dual_bound (us - v₀) (zb - u)
  have hdzu : ‖us - v₀‖ * ‖zb - u‖ ≤ δ * ‖zb - u‖ := mul_le_mul_of_nonneg_right hus' hzu0
  -- the key inequality (*) of the proof
  have hkey : r / 2 * ‖zb - u‖ ^ 2 - δ * ‖zb - u‖ - α / 2 * ‖zb - x₀‖ ^ 2 ≤ δ + a * δ := by
    have e1 : v₀ (zb - x₀) - us (zb - u) = v₀ (u - x₀) - (us - v₀) (zb - u) := by
      simp only [sub_apply, map_sub]; ring
    linarith [hv₀u.1, hd_zu.2]
  -- `zb` lies in the open ball
  have hzb_lt : ‖zb - x₀‖ < R := by
    by_contra hge
    push Not at hge
    have hzb_eq : ‖zb - x₀‖ = R := le_antisymm hzbK' hge
    have hzu' : R / 2 ≤ ‖zb - u‖ := by
      have : ‖zb - x₀‖ ≤ ‖zb - u‖ + ‖u - x₀‖ := by
        calc ‖zb - x₀‖ = ‖(zb - u) + (u - x₀)‖ := by rw [sub_add_sub_cancel]
          _ ≤ _ := norm_add_le _ _
      linarith
    have h1 : r / 2 * (R / 2) ^ 2 ≤ r / 2 * ‖zb - u‖ ^ 2 := by gcongr
    have h2 : δ * ‖zb - u‖ ≤ δ * (2 * R) := by gcongr
    rw [hzb_eq] at hkey
    have h3 : r / 2 * (R / 2) ^ 2 = (ρ / 8 + α / 2 + 1) * R ^ 2 := by rw [hr_def]; ring
    have h4 : 0 ≤ ρ / 8 * R ^ 2 := by positivity
    have h5 : δ * R ≤ δ := mul_le_of_le_one_right hδ.le hR1
    linarith
  -- Fermat rule
  have hKnhds : closedBall x₀ R ∈ 𝓝 zb := by
    refine mem_of_superset (isOpen_ball.mem_nhds ?_) ball_subset_closedBall
    rw [mem_ball, dist_eq_norm]; exact hzb_lt
  have hmin : IsLocalMin ψ zb := hzbmin.isLocalMin hKnhds
  obtain ⟨ws, hws_def⟩ : ∃ ws : StrongDual ℝ E, ws = us - r • innerSL ℝ (zb - u) := ⟨_, rfl⟩
  have hws : ws ∈ subdiff φ zb := by
    have h0 := zero_mem_regularSubdiff_of_isLocalMin hmin (r := s + h zb)
      (by rw [hψ, hs, EReal.coe_add])
    rw [hψ_def] at h0
    have hd : HasFDerivAt h (-us + r • innerSL ℝ (zb - u)) zb := by
      rw [h_def]; exact hasFDerivAt_quadPerturb us r u zb
    rw [mem_regularSubdiff_add_iff hd] at h0
    have : (0 : StrongDual ℝ E) - (-us + r • innerSL ℝ (zb - u)) = ws := by
      rw [hws_def]; abel
    rw [this] at h0
    exact regularSubdiff_subset_subdiff h0
  -- both points lie in the localization
  have hloc_u : us ∈ attentiveLocalization (subdiff φ) φ x₀ v₀ ε' u := by
    have hprod : (1 + a + α) * δ ≤ K * R :=
      mul_le_mul (by linarith) (by linarith) hδ.le hK.le
    refine ⟨hus, by linarith, by linarith, t, ht, ?_⟩
    rw [hr₀, EReal.toReal_coe, abs_lt]
    constructor <;> linarith
  have hws_v : ‖ws - v₀‖ ≤ δ + r * (2 * R) := by
    calc ‖ws - v₀‖ = ‖(us - v₀) - r • innerSL ℝ (zb - u)‖ := by rw [hws_def]; abel_nf
      _ ≤ ‖us - v₀‖ + ‖r • innerSL ℝ (zb - u)‖ := norm_sub_le _ _
      _ = ‖us - v₀‖ + r * ‖zb - u‖ := by
          rw [norm_smul, innerSL_apply_norm, Real.norm_of_nonneg hr.le]
      _ ≤ δ + r * (2 * R) := by gcongr
  have hsup : s ≤ r₀ + δ + (a + δ) * (2 * R) := by
    have e5 : us (zb - u) ≤ (a + δ) * (2 * R) := by
      calc us (zb - u) ≤ ‖us‖ * ‖zb - u‖ := hus_zu.2
        _ ≤ (a + δ) * (2 * R) := by gcongr
    have : 0 ≤ r / 2 * ‖zb - u‖ ^ 2 := by positivity
    linarith
  have hsinf : r₀ - a * R - α * R ≤ s := by
    have hv₀z := dual_bound v₀ (zb - x₀)
    rw [← ha_def] at hv₀z
    have e1 : a * ‖zb - x₀‖ ≤ a * R := mul_le_mul_of_nonneg_left hzbK' ha
    have e2 : ‖zb - x₀‖ ^ 2 ≤ R := by
      rw [sq]
      calc ‖zb - x₀‖ * ‖zb - x₀‖ ≤ R * 1 := mul_le_mul hzbK' (by linarith) (norm_nonneg _) hR.le
        _ = R := mul_one R
    have e3 := mul_le_mul_of_nonneg_left e2 (show 0 ≤ α / 2 by linarith)
    linarith [hv₀z.1, mul_nonneg hα hR.le]
  have hloc_z : ws ∈ attentiveLocalization (subdiff φ) φ x₀ v₀ ε' zb := by
    have hRK' : (1 + 2 * r) * R ≤ K * R := mul_le_mul_of_nonneg_right (by linarith) hR.le
    have hδR' : δ * R ≤ R := mul_le_of_le_one_left hR.le hδ1
    have h2 : (3 + 2 * a) * R ≤ K * R := mul_le_mul_of_nonneg_right (by linarith) hR.le
    have h3 : (a + α) * R ≤ K * R := mul_le_mul_of_nonneg_right (by linarith) hR.le
    refine ⟨hws, by linarith, by linarith, s, hs, ?_⟩
    rw [hr₀, EReal.toReal_coe, abs_lt]
    constructor <;> linarith
  -- hypomonotonicity forces `zb = u`
  have hmono := hT' zb trivial u trivial ws hloc_z us hloc_u
  have hcalc : (ws - us) (zb - u) = -(r * ‖zb - u‖ ^ 2) := by
    rw [hws_def, sub_sub_cancel_left, neg_apply, smul_apply, innerSL_apply_apply,
      real_inner_self_eq_norm_sq, smul_eq_mul]
  rw [hcalc] at hmono
  have hzb_u : zb = u := by
    have hrρ : 0 < r - ρ := by rw [hr_def]; linarith
    have h1 : (r - ρ) * ‖zb - u‖ ^ 2 ≤ 0 := by linarith
    have h2 : ‖zb - u‖ ^ 2 ≤ 0 := by
      by_contra hpos
      push Not at hpos
      have := mul_pos hrρ hpos
      linarith
    have : ‖zb - u‖ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1
      (le_antisymm h2 (sq_nonneg _))
    rwa [norm_eq_zero, sub_eq_zero] at this
  -- conclusion: `ψ u ≤ ψ z`
  subst hzb_u
  have hzK : z ∈ closedBall x₀ R := by
    rw [mem_closedBall, dist_eq_norm]; linarith
  have hle : ψ zb ≤ ψ z := hzbmin hzK
  rw [hψu, hψ, coe_le_add_coe_iff] at hle
  refine le_trans (EReal.coe_le_coe_iff.2 (le_of_eq ?_)) hle
  have := hhdiff z
  rw [hhu] at this ⊢
  simp only [map_sub] at this ⊢
  linarith

/-- [Mordukhovich 2024, Thm. 1.65] with the basic localization only (finite-dimensional inner
product spaces): `φ` (l.s.c. around `x₀`) is prox-regular at `x₀` for `v₀` iff
`v₀ ∈ ∂_P φ(x₀)` and some `φ`-attentive localization of `∂φ` around `(x₀, v₀)` is
hypomonotone. -/
theorem proxRegularFor_iff_isHypomonotoneOn_subdiff
    (hlsc : ∀ᶠ x in 𝓝 x₀, LowerSemicontinuousAt φ x) :
    ProxRegularFor φ x₀ v₀ ↔ v₀ ∈ proxSubdiff φ x₀ ∧ ∃ ε > (0 : ℝ), ∃ ρ > (0 : ℝ),
      IsHypomonotoneOn ρ (attentiveLocalization (subdiff φ) φ x₀ v₀ ε) univ := by
  refine ⟨fun h ↦ ⟨h.mem_proxSubdiff, h.isHypomonotoneOn_attentiveLocalization⟩, ?_⟩
  rintro ⟨hP, ε, hε, ρ, -, hT⟩
  exact ProxRegularFor.of_isHypomonotoneOn hlsc hP hε hT

/-- [Mordukhovich 2024, Thm. 1.65] (subdifferential characterization of prox-regularity via
hypomonotonicity), finite-dimensional inner product spaces: for `φ` l.s.c. around `x₀`,
`φ` is prox-regular at `x₀` for `v₀` iff `v₀ ∈ ∂_P φ(x₀)` and, for some
`ε, ρ > 0`, both `φ`-attentive `ε`-localizations of `∂φ` and of `∂̂φ` around `(x₀, v₀)` are
`ρ`-hypomonotone. -/
theorem proxRegularFor_iff_isHypomonotoneOn (hlsc : ∀ᶠ x in 𝓝 x₀, LowerSemicontinuousAt φ x) :
    ProxRegularFor φ x₀ v₀ ↔ v₀ ∈ proxSubdiff φ x₀ ∧ ∃ ε > (0 : ℝ), ∃ ρ > (0 : ℝ),
      IsHypomonotoneOn ρ (attentiveLocalization (subdiff φ) φ x₀ v₀ ε) univ ∧
        IsHypomonotoneOn ρ (attentiveLocalization (regularSubdiff φ) φ x₀ v₀ ε) univ := by
  rw [proxRegularFor_iff_isHypomonotoneOn_subdiff hlsc]
  refine and_congr_right fun _ ↦ ⟨fun ⟨ε, hε, ρ, hρ, hT⟩ ↦ ⟨ε, hε, ρ, hρ, hT, ?_⟩,
    fun ⟨ε, hε, ρ, hρ, hT, _⟩ ↦ ⟨ε, hε, ρ, hρ, hT⟩⟩
  exact hT.mono (attentiveLocalization_subset fun _ ↦ regularSubdiff_subset_subdiff)
    subset_rfl

/-- [Mordukhovich 2024, Thm. 1.65], last statement (finite-dimensional inner product spaces):
for `φ` l.s.c. around `x₀` and subdifferentially continuous at `x₀` for `v₀`, prox-regularity
at `x₀` for `v₀` is equivalent to `v₀ ∈ ∂_P φ(x₀)` together with the local hypomonotonicity of
the ordinary localization of `∂φ` around `(x₀, v₀)`. The implication `⇐` does not need
subdifferential continuity. -/
theorem proxRegularFor_iff_locallyHypomonotoneAt
    (hlsc : ∀ᶠ x in 𝓝 x₀, LowerSemicontinuousAt φ x) (hc : SubdiffContinuousFor φ x₀ v₀) :
    ProxRegularFor φ x₀ v₀ ↔
      v₀ ∈ proxSubdiff φ x₀ ∧ LocallyHypomonotoneAt (subdiff φ) x₀ v₀ := by
  refine ⟨fun h ↦ ⟨h.mem_proxSubdiff, ContinuouslyProxRegularFor.locallyHypomonotoneAt ⟨h, hc⟩⟩,
    fun ⟨hP, hT⟩ ↦ ?_⟩
  obtain ⟨ρ, hρ, U, hU, V, hV, H⟩ := hT
  obtain ⟨ε₁, hε₁, hU'⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨ε₂, hε₂, hV'⟩ := Metric.mem_nhds_iff.1 hV
  refine ProxRegularFor.of_isHypomonotoneOn hlsc hP (lt_min hε₁ hε₂) (ρ' := ρ) ?_
  rintro x₁ - x₂ - v₁ ⟨hv₁, hx₁, hv₁', -⟩ v₂ ⟨hv₂, hx₂, hv₂', -⟩
  have hU₁ : x₁ ∈ U := hU' (by rw [mem_ball, dist_eq_norm]; exact hx₁.trans_le (min_le_left _ _))
  have hU₂ : x₂ ∈ U := hU' (by rw [mem_ball, dist_eq_norm]; exact hx₂.trans_le (min_le_left _ _))
  have hV₁ : v₁ ∈ V :=
    hV' (by rw [mem_ball, dist_eq_norm]; exact hv₁'.trans_le (min_le_right _ _))
  have hV₂ : v₂ ∈ V :=
    hV' (by rw [mem_ball, dist_eq_norm]; exact hv₂'.trans_le (min_le_right _ _))
  exact H x₁ hU₁ x₂ hU₂ v₁ ⟨hv₁, hV₁⟩ v₂ ⟨hv₂, hV₂⟩

end Backward

end VariationalAnalysis
