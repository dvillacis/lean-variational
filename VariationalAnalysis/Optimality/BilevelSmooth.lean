/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import VariationalAnalysis.Optimality.Bilevel
import VariationalAnalysis.Optimality.Programming
import VariationalAnalysis.Subdifferential.NegConvexHull
import VariationalAnalysis.Normal.Diffeomorphism

/-!
# Bilevel programs with smooth data

Sect. 6.3 of [Mordukhovich 2018]: necessary optimality conditions for optimistic bilevel programs
via the value function approach, partial calmness and the subdifferentiation of the lower-level
value function `μ`.

The data are as in `VariationalAnalysis.Optimality.Bilevel`; the upper-level constraint set is
`Ω = {x | hⱼ(x) ≤ 0, j ∈ J}` (6.50). "Smooth" means `C¹` around the reference point, and
partial derivatives are written `∇ₓf(x̄, ȳ) = ∇f(x̄, ȳ) ∘ inl`, `∇_y f(x̄, ȳ) = ∇f(x̄, ȳ) ∘ inr`.

## Main results

* `normalCone_le_zero_subset`: normals to sets given by `C¹` inequalities under positive linear
  independence of the active gradients [Mordukhovich 2018, Exercise 2.51(ii)].
* `subdiff_lowerValue_subset`, `exists_lipschitzOnWith_lowerValue`: basic subgradients and
  Lipschitz continuity of the value function `μ` of a smooth lower-level problem (Thm. 4.1 with
  (6.29)), as in the proof of Thm. 6.21.
* `add_mem_regularSubdiff_of_mem_regularSubdiff_sub`, `regularSubdiff_sub_subset`,
  `regularSubdiff_subset_of_isLocalMin_sub`: Lemma 6.22 (difference rule for regular
  subgradients).
* `exists_multipliers_smooth_bilevel_upper`: Thm. 6.21 (optimality conditions for smooth bilevel
  programs, I).
* `exists_multipliers_smooth_bilevel_regular`: Thm. 6.23 (optimality conditions for smooth bilevel
  programs, II).

## Remarks on the book

* Lower-level regularity (6.52) and upper-level regularity (6.53) are stated for multipliers
  vanishing on the inactive constraints (`LowerLevelRegular`, `UpperLevelRegular`).
* Thm. 6.21: the book's proof asserts that `μ` is "easy to see" l.s.c. around `x̄`; inner
  semicontinuity of `S` at `(x̄, ȳ)` only gives lower semicontinuity at `x̄`
  (`lowerSemicontinuousAt_marginal_of_innerSemicontinuousAt`), so lower semicontinuity of `μ`
  around `x̄` is assumed (as in Cor. 4.3, `exists_lipschitzOnWith_marginal_of_lipschitzLikeAt`). The
  standing assumption `S(x) ≠ ∅` near `x̄` is explicit. Local optimality in (6.31) enters the
  book's proof only through Prop. 6.13(i), i.e. local optimality in (6.34), which already follows
  from partial calmness at a feasible point; we assume `ȳ ∈ S(x̄)`, `x̄ ∈ Ω` and partial calmness.
  The inclusion `∂(-μ)(x̄) ⊆ -co ∂μ(x̄)`, which the book takes from (1.79) and (1.83), is
  `neg_mem_convexHull_subdiff_of_mem_subdiff_neg`.
* Thm. 6.23: the book uses (6.63) for the difference function (6.64); the penalized problem
  (6.40) gives directly the increment inequality behind (6.63)
  (`regularSubdiff_subset_of_eventually_le`), which avoids assuming `G(x) ≠ ∅` near `x̄`.
-/

open Filter Topology Set Metric ContinuousLinearMap
open scoped NNReal Pointwise

namespace VariationalAnalysis

/-! ### `C¹` functions -/

section Smooth

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {f : X → ℝ} {x : X}

theorem eventually_hasFDerivAt_of_contDiffAt (h : ContDiffAt ℝ 1 f x) :
    ∀ᶠ y in 𝓝 x, HasFDerivAt f (fderiv ℝ f y) y :=
  (h.eventually (by simp)).mono fun _ hy ↦ (hy.differentiableAt one_ne_zero).hasFDerivAt

theorem eventually_hasStrictFDerivAt_of_contDiffAt (h : ContDiffAt ℝ 1 f x) :
    ∀ᶠ y in 𝓝 x, HasStrictFDerivAt f (fderiv ℝ f y) y :=
  (h.eventually (by simp)).mono fun _ hy ↦ hy.hasStrictFDerivAt one_ne_zero

theorem continuousAt_fderiv_of_contDiffAt (h : ContDiffAt ℝ 1 f x) :
    ContinuousAt (fderiv ℝ f) x :=
  (h.fderiv_right (m := 0) (by norm_num)).continuousAt

theorem exists_continuousOn_of_contDiffAt (h : ContDiffAt ℝ 1 f x) :
    ∃ U ∈ 𝓝 x, ContinuousOn f U :=
  ⟨_, h.eventually (by simp), fun y hy ↦
    (show ContDiffAt ℝ 1 f y from hy).continuousAt.continuousWithinAt⟩

theorem subdiff_of_contDiffAt (h : ContDiffAt ℝ 1 f x) :
    subdiff (fun y ↦ (f y : EReal)) x = {fderiv ℝ f x} :=
  subdiff_of_hasFDerivAt_of_continuousAt (eventually_hasFDerivAt_of_contDiffAt h)
    (continuousAt_fderiv_of_contDiffAt h)

omit [NormedSpace ℝ X] in
/-- Finitely many functions Lipschitz around `x` are Lipschitz with a common constant on a common
neighborhood. -/
theorem exists_common_lipschitzOnWith {K : Type*} [Finite K] {Φ : K → X → ℝ}
    (h : ∀ k, ∃ L : ℝ≥0, ∃ U ∈ 𝓝 x, LipschitzOnWith L (Φ k) U) :
    ∃ U ∈ 𝓝 x, ∃ L : ℝ≥0, ∀ k, LipschitzOnWith L (Φ k) U := by
  classical
  have := Fintype.ofFinite K
  choose L U hU hL using h
  refine ⟨⋂ k, U k, iInter_mem.2 hU, Finset.univ.sup L, fun k ↦ ?_⟩
  exact ((hL k).mono (iInter_subset _ k)).weaken (Finset.le_sup (Finset.mem_univ k))

omit [NormedSpace ℝ X] in
/-- The set `{w | gᵢ(w) ≤ 0 for all i}` is locally closed around `w₀` if the `gᵢ` are continuous
around `w₀`. -/
theorem locallyClosed_le_zero {ι : Type*} [Finite ι] {g : ι → X → ℝ}
    (hg : ∀ i, ∃ U ∈ 𝓝 x, ContinuousOn (g i) U) :
    ∃ ρ > 0, IsClosed ({w | ∀ i, g i w ≤ 0} ∩ closedBall x ρ) := by
  choose U hU hc using hg
  obtain ⟨ρ, hρ, hsub⟩ := nhds_basis_closedBall.mem_iff.1 (iInter_mem.2 hU)
  refine ⟨ρ, hρ, ?_⟩
  have heq : {w | ∀ i, g i w ≤ 0} ∩ closedBall x ρ =
      closedBall x ρ ∩ ⋂ i, (closedBall x ρ ∩ g i ⁻¹' Iic 0) := by
    ext w
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iInter, mem_preimage, mem_Iic]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, fun i ↦ ⟨h2, h1 i⟩⟩
    · rintro ⟨h1, h2⟩; exact ⟨fun i ↦ (h2 i).2, h1⟩
  rw [heq]
  exact isClosed_closedBall.inter (isClosed_iInter fun i ↦
    ((hc i).mono (hsub.trans (iInter_subset _ i))).preimage_isClosed_of_isClosed
      isClosed_closedBall isClosed_Iic)

end Smooth

/-! ### Normals to sets given by smooth inequalities -/

section Inequalities

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

omit [FiniteDimensional ℝ W] in
/-- A nonzero functional on `W` is onto `ℝ`. -/
theorem surjective_of_ne_zero {v : StrongDual ℝ W} (hv : v ≠ 0) : Function.Surjective v := by
  obtain ⟨w, hw⟩ : ∃ w, v w ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (ContinuousLinearMap.ext h)
  exact fun t ↦ ⟨(t / v w) • w, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hw]⟩

/-- Normals to a single `C¹` inequality `{g ≤ 0}` at `w₀`: `N(w₀; {g ≤ 0}) ⊆ {c ∇g(w₀) | c ≥ 0,
c g(w₀) = 0}` provided `∇g(w₀) ≠ 0` when the constraint is active. -/
theorem normalCone_le_zero_single_subset {g : W → ℝ} {w₀ : W} (hg : ContDiffAt ℝ 1 g w₀)
    (hfeas : g w₀ ≤ 0) (hne : g w₀ = 0 → fderiv ℝ g w₀ ≠ 0) :
    normalCone (g ⁻¹' Iic 0) w₀ ⊆
      {v | ∃ c : ℝ, 0 ≤ c ∧ c * g w₀ = 0 ∧ v = c • fderiv ℝ g w₀} := by
  intro v hv
  rcases hfeas.lt_or_eq with hlt | heq
  · have hint : w₀ ∈ interior (g ⁻¹' Iic 0) := by
      rw [mem_interior_iff_mem_nhds]
      filter_upwards [hg.continuousAt.eventually (Iio_mem_nhds hlt)] with w hw
      exact le_of_lt hw
    rw [normalCone_of_mem_interior hint] at hv
    exact ⟨0, le_rfl, by simp, by simpa using hv⟩
  · rw [normalCone_preimage_of_surjective_of_finiteDimensional
      (eventually_hasStrictFDerivAt_of_contDiffAt hg) (continuousAt_fderiv_of_contDiffAt hg)
      (surjective_of_ne_zero (hne heq)), heq] at hv
    obtain ⟨m, hm, rfl⟩ := hv
    rw [mem_normalCone_of_convex (convex_Iic (0 : ℝ)) (mem_Iic.2 le_rfl)] at hm
    have h1 : 0 ≤ m 1 := by
      have := hm (-1) (by norm_num)
      simp only [sub_zero, map_neg] at this
      linarith
    have hm1 : ∀ t : ℝ, m t = t * m 1 := fun t ↦ by
      rw [← smul_eq_mul t (m 1), ← map_smul, smul_eq_mul, mul_one]
    refine ⟨m 1, h1, by rw [heq, mul_zero], ?_⟩
    ext w
    simp only [coe_comp, Function.comp_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [hm1]; ring

/-- [Mordukhovich 2018, Exercise 2.51(ii)]: normals to `{w | gᵢ(w) ≤ 0 for all i}` for `C¹`
functions `gᵢ` whose active gradients at `w₀` are positively linearly independent:
`N(w₀) ⊆ {∑ λᵢ ∇gᵢ(w₀) | λᵢ ≥ 0, λᵢ gᵢ(w₀) = 0}`. -/
theorem normalCone_le_zero_subset {ι : Type*} [Fintype ι] {g : ι → W → ℝ} {w₀ : W}
    (hg : ∀ i, ContDiffAt ℝ 1 (g i) w₀) (hfeas : ∀ i, g i w₀ ≤ 0)
    (hreg : ∀ lam : ι → ℝ, (∀ i, 0 ≤ lam i) → (∀ i, g i w₀ < 0 → lam i = 0) →
      ∑ i, lam i • fderiv ℝ (g i) w₀ = 0 → lam = 0) :
    normalCone {w | ∀ i, g i w ≤ 0} w₀ ⊆
      {v | ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧ (∀ i, lam i * g i w₀ = 0) ∧
        v = ∑ i, lam i • fderiv ℝ (g i) w₀} := by
  classical
  have hne : ∀ i, g i w₀ = 0 → fderiv ℝ (g i) w₀ ≠ 0 := by
    intro i hi h0
    have := hreg (Pi.single i 1) (fun j ↦ by by_cases hj : j = i <;> simp [hj])
      (fun j hj ↦ by
        have : j ≠ i := fun h ↦ by rw [h, hi] at hj; exact lt_irrefl _ hj
        simp [this])
      (by simp [Pi.single_apply, h0])
    simpa using congrFun this i
  have hsingle := fun i ↦ normalCone_le_zero_single_subset (hg i) (hfeas i) (hne i)
  have hset : {w | ∀ i, g i w ≤ 0} = ⋂ i, g i ⁻¹' Iic 0 := by ext; simp
  intro v hv
  rw [hset] at hv
  have hloc : ∀ i, ∃ r > 0, IsClosed (g i ⁻¹' Iic 0 ∩ closedBall w₀ r) := fun i ↦ by
    obtain ⟨ρ, hρ, hc⟩ := locallyClosed_le_zero (ι := Unit) (g := fun _ ↦ g i)
      (fun _ ↦ exists_continuousOn_of_contDiffAt (hg i))
    exact ⟨ρ, hρ, by convert hc using 2; ext; simp⟩
  have hqc : ∀ u : ι → StrongDual ℝ W, (∀ i, u i ∈ normalCone (g i ⁻¹' Iic 0) w₀) →
      ∑ i, u i = 0 → ∀ i, u i = 0 := by
    intro u hu hsum
    choose c hc0 hcs hcu using fun i ↦ hsingle i (hu i)
    have hc : c = 0 := hreg c hc0
      (fun i hi ↦ (mul_eq_zero.1 (hcs i)).resolve_right hi.ne)
      (by rw [← hsum]; exact Finset.sum_congr rfl fun i _ ↦ (hcu i).symm)
    intro i
    rw [hcu i, hc, Pi.zero_apply, zero_smul]
  obtain ⟨u, hu, rfl⟩ := (Set.mem_fintype_sum _ _).1 (normalCone_iInter_subset hloc hqc hv)
  choose c hc0 hcs hcu using fun i ↦ hsingle i (hu i)
  exact ⟨c, hc0, hcs, Finset.sum_congr rfl fun i _ ↦ hcu i⟩

end Inequalities

/-! ### Lemma 6.22: difference rule for regular subgradients -/

section DifferenceRule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {φ₁ φ₂ : E → EReal} {x₀ : E}
  {r₁ r₂ : ℝ}

/-- The increment form of (6.63) of [Mordukhovich 2018]: if `φ₂(x) - φ₂(x̄) ≤ φ₁(x) - φ₁(x̄)` near
`x̄` (written `φ₂(x) + φ₁(x̄) ≤ φ₁(x) + φ₂(x̄)`), then `∂̂φ₂(x̄) ⊆ ∂̂φ₁(x̄)`. -/
theorem regularSubdiff_subset_of_eventually_le (hr₁ : φ₁ x₀ = r₁) (hr₂ : φ₂ x₀ = r₂)
    (h : ∀ᶠ x in 𝓝 x₀, φ₂ x + r₁ ≤ φ₁ x + r₂) : regularSubdiff φ₂ x₀ ⊆ regularSubdiff φ₁ x₀ := by
  intro v hv
  rw [mem_regularSubdiff_iff hr₂] at hv
  rw [mem_regularSubdiff_iff hr₁]
  intro ε hε
  filter_upwards [hv ε hε, h] with x hx hxh
  induction hφ₁ : φ₁ x with
  | top => exact le_top
  | bot =>
    rw [hφ₁, EReal.bot_add, le_bot_iff] at hxh
    have : φ₂ x = ⊥ := by
      by_contra hne
      exact EReal.add_ne_bot_iff.2 ⟨hne, EReal.coe_ne_bot _⟩ hxh
    rw [this, le_bot_iff] at hx
    exact absurd hx (EReal.coe_ne_bot _)
  | coe c =>
    rw [hφ₁, ← EReal.coe_add] at hxh
    induction hφ₂ : φ₂ x with
    | top =>
      rw [hφ₂, EReal.top_add_coe] at hxh; exact absurd (top_le_iff.1 hxh) (EReal.coe_ne_top _)
    | bot => rw [hφ₂, le_bot_iff] at hx; exact absurd hx (EReal.coe_ne_bot _)
    | coe b =>
      rw [hφ₂, ← EReal.coe_add, EReal.coe_le_coe_iff] at hxh
      rw [hφ₂, EReal.coe_le_coe_iff] at hx
      rw [EReal.coe_le_coe_iff]
      linarith

/-- Lemma 6.22 of [Mordukhovich 2018], first inclusion in (6.62): if `φ₂` is finite at `x̄`
(the book also assumes `φ₁` finite at `x̄`), then `u + v ∈ ∂̂φ₁(x̄)` for all `u ∈ ∂̂(φ₁ - φ₂)(x̄)` and `v ∈ ∂̂φ₂(x̄)`. -/
theorem add_mem_regularSubdiff_of_mem_regularSubdiff_sub (hr₂ : φ₂ x₀ = r₂)
    {u v : StrongDual ℝ E} (hu : u ∈ regularSubdiff (fun x ↦ φ₁ x - φ₂ x) x₀)
    (hv : v ∈ regularSubdiff φ₂ x₀) : u + v ∈ regularSubdiff φ₁ x₀ := by
  obtain ⟨ψ, hψ, hψ₀, hψle⟩ := (mem_regularSubdiff_iff_exists_support hr₂).1 hv
  have hle : ∀ᶠ x in 𝓝 x₀, φ₁ x - φ₂ x ≤ φ₁ x + ((-ψ x : ℝ) : EReal) := by
    filter_upwards [hψle] with x hx
    rw [EReal.coe_neg, ← sub_eq_add_neg]
    exact EReal.sub_le_sub le_rfl hx
  have heq : φ₁ x₀ - φ₂ x₀ = φ₁ x₀ + ((-ψ x₀ : ℝ) : EReal) := by
    rw [hr₂, hψ₀, EReal.coe_neg, ← sub_eq_add_neg]
  have hu' := regularSubdiff_subset_of_le hle heq hu
  have := (mem_regularSubdiff_add_iff (φ := φ₁) (f := fun x ↦ -ψ x) hψ.neg).1 hu'
  simpa [sub_neg_eq_add] using this

/-- Lemma 6.22 of [Mordukhovich 2018], (6.62): if `φ₂` is finite at `x̄` and
`∂̂φ₂(x̄) ≠ ∅`, then `∂̂(φ₁ - φ₂)(x̄) ⊆ ∂̂φ₁(x̄) - ∂̂φ₂(x̄)`. -/
theorem regularSubdiff_sub_subset (hr₂ : φ₂ x₀ = r₂)
    (hne : (regularSubdiff φ₂ x₀).Nonempty) :
    regularSubdiff (fun x ↦ φ₁ x - φ₂ x) x₀ ⊆ regularSubdiff φ₁ x₀ - regularSubdiff φ₂ x₀ := by
  obtain ⟨v, hv⟩ := hne
  exact fun u hu ↦
    ⟨u + v, add_mem_regularSubdiff_of_mem_regularSubdiff_sub hr₂ hu hv, v, hv, by simp⟩

/-- Lemma 6.22 of [Mordukhovich 2018], (6.63): a local minimizer `x̄` of `φ₁ - φ₂`, with `φ₁`,
`φ₂` finite at `x̄`, satisfies `∂̂φ₂(x̄) ⊆ ∂̂φ₁(x̄)`. -/
theorem regularSubdiff_subset_of_isLocalMin_sub (hr₁ : φ₁ x₀ = r₁) (hr₂ : φ₂ x₀ = r₂)
    (hmin : IsLocalMin (fun x ↦ φ₁ x - φ₂ x) x₀) : regularSubdiff φ₂ x₀ ⊆ regularSubdiff φ₁ x₀ :=
  fun v hv ↦ by
    have h0 := zero_mem_regularSubdiff_of_isLocalMin hmin
      (show φ₁ x₀ - φ₂ x₀ = ((r₁ - r₂ : ℝ) : EReal) by rw [hr₁, hr₂, EReal.coe_sub])
    simpa using add_mem_regularSubdiff_of_mem_regularSubdiff_sub hr₂ h0 hv

end DifferenceRule

/-! ### Smooth bilevel programs -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {ι J : Type*}

variable (g : ι → E × F → ℝ) in
/-- Lower-level regularity (6.52) of [Mordukhovich 2018] at `(x̄, ȳ)`: the partial gradients
`∇_y gᵢ(x̄, ȳ)` of the active constraints are positively linearly independent. -/
def LowerLevelRegular [Fintype ι] (x₀ : E) (y₀ : F) : Prop :=
  ∀ lam : ι → ℝ, (∀ i, 0 ≤ lam i) → (∀ i, g i (x₀, y₀) < 0 → lam i = 0) →
    ∑ i, lam i • (fderiv ℝ (g i) (x₀, y₀)).comp (inr ℝ E F) = 0 → lam = 0

variable (h : J → E → ℝ) in
/-- Upper-level regularity (6.53) of [Mordukhovich 2018] at `x̄`: the gradients `∇hⱼ(x̄)` of the
active upper-level constraints are positively linearly independent. -/
def UpperLevelRegular [Fintype J] (x₀ : E) : Prop :=
  ∀ lam : J → ℝ, (∀ j, 0 ≤ lam j) → (∀ j, h j x₀ < 0 → lam j = 0) →
    ∑ j, lam j • fderiv ℝ (h j) x₀ = 0 → lam = 0

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [Fintype ι] [Fintype J]
  {f φ : E × F → ℝ} {g : ι → E × F → ℝ} {h : J → E → ℝ} {x₀ : E} {y₀ : F}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [Fintype ι] [Fintype J] in
theorem graph_lowerFeasible : graph (lowerFeasible g) = {p : E × F | ∀ i, g i p ≤ 0} := rfl

/-- Normals to the graph of the lower-level constraint map `G` (6.29) under lower-level
regularity [Mordukhovich 2018, Exercise 2.51(ii)]. -/
theorem normalCone_graph_lowerFeasible_subset (hg : ∀ i, ContDiffAt ℝ 1 (g i) (x₀, y₀))
    (hfeas : y₀ ∈ lowerFeasible g x₀) (hreg : LowerLevelRegular g x₀ y₀) :
    normalCone (graph (lowerFeasible g)) (x₀, y₀) ⊆
      {v | ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧ (∀ i, lam i * g i (x₀, y₀) = 0) ∧
        v = ∑ i, lam i • fderiv ℝ (g i) (x₀, y₀)} := by
  rw [graph_lowerFeasible]
  refine normalCone_le_zero_subset hg hfeas fun lam h0 hin hsum ↦ hreg lam h0 hin ?_
  ext y
  have := congrArg (fun T : StrongDual ℝ (E × F) ↦ T (0, y)) hsum
  simpa using this

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem locallyClosed_graph_lowerFeasible (hg : ∀ i, ContDiffAt ℝ 1 (g i) (x₀, y₀)) :
    ∃ ρ > 0, IsClosed (graph (lowerFeasible g) ∩ closedBall (x₀, y₀) ρ) :=
  locallyClosed_le_zero fun i ↦ exists_continuousOn_of_contDiffAt (hg i)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The set of vectors `B₀ + ∑ λᵢ Bᵢ` with multipliers `λᵢ ≥ 0`, `λᵢ cᵢ = 0` and
`A₀ + ∑ λᵢ Aᵢ = 0` is convex. -/
theorem convex_multiplierSet {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] [TopologicalSpace V] [TopologicalSpace W] {c : ι → ℝ}
    {A₀ : V →L[ℝ] ℝ} {A : ι → V →L[ℝ] ℝ} {B₀ : W →L[ℝ] ℝ} {B : ι → W →L[ℝ] ℝ} :
    Convex ℝ {u : W →L[ℝ] ℝ | ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧ (∀ i, lam i * c i = 0) ∧
      A₀ + ∑ i, lam i • A i = 0 ∧ u = B₀ + ∑ i, lam i • B i} := by
  rintro _ ⟨l₁, h1, c1, y1, rfl⟩ _ ⟨l₂, h2, c2, y2, rfl⟩ a b ha hb hab
  refine ⟨a • l₁ + b • l₂, fun i ↦ ?_, fun i ↦ ?_, ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (h1 i)) (mul_nonneg hb (h2 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [add_mul, mul_assoc, mul_assoc, c1 i, c2 i, mul_zero, mul_zero, add_zero]
  · ext v
    have e1 := congrArg (fun T : V →L[ℝ] ℝ ↦ T v) y1
    have e2 := congrArg (fun T : V →L[ℝ] ℝ ↦ T v) y2
    simp only [add_apply, sum_apply, smul_apply, smul_eq_mul, zero_apply, Pi.add_apply,
      Pi.smul_apply] at e1 e2 ⊢
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    linear_combination a * e1 + b * e2 - A₀ v * hab
  · ext v
    simp only [add_apply, sum_apply, smul_apply, smul_eq_mul, Pi.add_apply, Pi.smul_apply]
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    linear_combination (B₀ v) * hab

/-- Basic subgradients of the value function `μ` (6.33) of a smooth lower-level problem with
constraints (6.29) [Mordukhovich 2018, Thm. 4.1(i), (4.4), and Exercise 2.51(ii), as in the proof
of Thm. 6.21]: if `ȳ ∈ S(x̄)`, `S` is inner semicontinuous at `(x̄, ȳ)` and nonempty-valued near
`x̄`, and `(x̄, ȳ)` is lower-level regular, then every `u ∈ ∂μ(x̄)` is
`u = ∇ₓφ(x̄, ȳ) + ∑ λᵢ ∇ₓgᵢ(x̄, ȳ)` with `λᵢ ≥ 0`, `λᵢ gᵢ(x̄, ȳ) = 0` and
`∇_yφ(x̄, ȳ) + ∑ λᵢ ∇_y gᵢ(x̄, ȳ) = 0`. -/
theorem subdiff_lowerValue_subset (hy₀ : y₀ ∈ lowerSolution φ g x₀)
    (hφ : ContDiffAt ℝ 1 φ (x₀, y₀)) (hg : ∀ i, ContDiffAt ℝ 1 (g i) (x₀, y₀))
    (hreg : LowerLevelRegular g x₀ y₀) (hisc : InnerSemicontinuousAt (lowerSolution φ g) x₀ y₀)
    (hne : ∀ᶠ x in 𝓝 x₀, (lowerSolution φ g x).Nonempty) :
    subdiff (lowerValue φ g) x₀ ⊆ {u | ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧
      (∀ i, lam i * g i (x₀, y₀) = 0) ∧
      (fderiv ℝ φ (x₀, y₀)).comp (inr ℝ E F) +
        ∑ i, lam i • (fderiv ℝ (g i) (x₀, y₀)).comp (inr ℝ E F) = 0 ∧
      u = (fderiv ℝ φ (x₀, y₀)).comp (inl ℝ E F) +
        ∑ i, lam i • (fderiv ℝ (g i) (x₀, y₀)).comp (inl ℝ E F)} := by
  obtain ⟨U, hU, hc⟩ := exists_continuousOn_of_contDiffAt hφ
  obtain ⟨K, V, hV, hK⟩ := hφ.exists_lipschitzOnWith
  intro u hu
  obtain ⟨a, b, hab, hcod⟩ := subdiff_marginal_subset_of_innerSemicontinuousAt
    (lowerValue_eq_of_mem_lowerSolution hy₀) hy₀ hisc (hne.mono fun _ hx _ ↦ hx)
    (locallyClosed_epi_of_continuousOn hU hc _) (locallyClosed_graph_lowerFeasible hg)
    (fun w hw _ ↦ by rwa [singularSubdiff_eq_zero_of_lipschitz hV hK] at hw) hu
  rw [subdiff_of_contDiffAt hφ, mem_singleton_iff] at hab
  obtain ⟨lam, hlam, hcs, heq⟩ := normalCone_graph_lowerFeasible_subset hg hy₀.1 hreg hcod
  refine ⟨lam, hlam, hcs, ?_, ?_⟩
  · ext y
    have h1 := congrArg (fun T : StrongDual ℝ (E × F) ↦ T (0, y)) heq
    have h2 := congrArg (fun T : StrongDual ℝ (E × F) ↦ T (0, y)) hab
    simp at h1 h2 ⊢
    linarith
  · ext x
    have h1 := congrArg (fun T : StrongDual ℝ (E × F) ↦ T (x, 0)) heq
    have h2 := congrArg (fun T : StrongDual ℝ (E × F) ↦ T (x, 0)) hab
    simp at h1 h2 ⊢
    linarith

/-- Under the assumptions of `subdiff_lowerValue_subset`, `∂^∞μ(x̄) = {0}` [Mordukhovich 2018,
(6.60), proof of Thm. 6.21]. -/
theorem singularSubdiff_lowerValue_eq_zero (hy₀ : y₀ ∈ lowerSolution φ g x₀)
    (hφ : ContDiffAt ℝ 1 φ (x₀, y₀)) (hg : ∀ i, ContDiffAt ℝ 1 (g i) (x₀, y₀))
    (hreg : LowerLevelRegular g x₀ y₀) (hisc : InnerSemicontinuousAt (lowerSolution φ g) x₀ y₀)
    (hne : ∀ᶠ x in 𝓝 x₀, (lowerSolution φ g x).Nonempty) :
    ∀ u ∈ singularSubdiff (lowerValue φ g) x₀, u = 0 := by
  obtain ⟨U, hU, hc⟩ := exists_continuousOn_of_contDiffAt hφ
  obtain ⟨K, V, hV, hK⟩ := hφ.exists_lipschitzOnWith
  intro u hu
  obtain ⟨a, b, hab, hcod⟩ := singularSubdiff_marginal_subset_of_innerSemicontinuousAt
    (lowerValue_eq_of_mem_lowerSolution hy₀) hy₀ hisc (hne.mono fun _ hx _ ↦ hx)
    (locallyClosed_epi_of_continuousOn hU hc _) (locallyClosed_graph_lowerFeasible hg)
    (fun w hw _ ↦ by rwa [singularSubdiff_eq_zero_of_lipschitz hV hK] at hw) hu
  rw [singularSubdiff_eq_zero_of_lipschitz hV hK, mem_singleton_iff] at hab
  obtain ⟨lam, hlam, hcs, heq⟩ := normalCone_graph_lowerFeasible_subset hg hy₀.1 hreg hcod
  have hb : b = 0 := by
    ext y; have := congrArg (fun T : StrongDual ℝ (E × F) ↦ T (0, y)) hab; simpa using this
  have ha : a = 0 := by
    ext x; have := congrArg (fun T : StrongDual ℝ (E × F) ↦ T (x, 0)) hab; simpa using this
  have hl : lam = 0 := hreg lam hlam (fun i hi ↦ (mul_eq_zero.1 (hcs i)).resolve_right hi.ne) (by
    ext y
    have := congrArg (fun T : StrongDual ℝ (E × F) ↦ T (0, y)) heq
    simp [hb] at this ⊢
    linarith)
  ext x
  have := congrArg (fun T : StrongDual ℝ (E × F) ↦ T (x, 0)) heq
  simpa [ha, hb, hl] using this

/-- Lipschitz continuity of the value function `μ` (6.33) of a smooth lower-level problem
[Mordukhovich 2018, proof of Thm. 6.21]: under the assumptions of `subdiff_lowerValue_subset`, if
`μ` is l.s.c. around `x̄`, then `μ` agrees near `x̄` with a real function Lipschitz around `x̄`
(Thm. 1.22). -/
theorem exists_lipschitzOnWith_lowerValue (hy₀ : y₀ ∈ lowerSolution φ g x₀)
    (hφ : ContDiffAt ℝ 1 φ (x₀, y₀)) (hg : ∀ i, ContDiffAt ℝ 1 (g i) (x₀, y₀))
    (hreg : LowerLevelRegular g x₀ y₀) (hisc : InnerSemicontinuousAt (lowerSolution φ g) x₀ y₀)
    (hne : ∀ᶠ x in 𝓝 x₀, (lowerSolution φ g x).Nonempty)
    (hlsc : ∀ᶠ x in 𝓝 x₀, LowerSemicontinuousAt (lowerValue φ g) x) :
    ∃ U ∈ 𝓝 x₀, ∃ L : ℝ≥0, ∃ μ : E → ℝ, (∀ x ∈ U, lowerValue φ g x = μ x) ∧
      LipschitzOnWith L μ U :=
  exists_lipschitzOnWith_of_singularSubdiff (lowerValue_eq_of_mem_lowerSolution hy₀) hlsc
    (singularSubdiff_lowerValue_eq_zero hy₀ hφ hg hreg hisc hne)

/-- Thm. 6.23 of [Mordukhovich 2018] (optimality conditions for smooth bilevel programs, II): let
`ȳ ∈ S(x̄)`, let (6.34) with `Ω = ℝⁿ` be partially calm at `(x̄, ȳ)`, let `f`, `φ`, `gᵢ` be `C¹`
around `(x̄, ȳ)`, `(x̄, ȳ)` lower-level regular, and `∂̂μ(x̄) ≠ ∅`. Then there are multipliers `νᵢ`
and `βᵢ ≥ 0` with `νᵢ gᵢ(x̄, ȳ) = βᵢ gᵢ(x̄, ȳ) = 0`,
`∇f(x̄, ȳ) + ∑ νᵢ ∇gᵢ(x̄, ȳ) = 0` and `∇_yφ(x̄, ȳ) + ∑ βᵢ ∇_y gᵢ(x̄, ȳ) = 0`. -/
theorem exists_multipliers_smooth_bilevel_regular (hy₀ : y₀ ∈ lowerSolution φ g x₀)
    (hcalm : PartiallyCalm f φ g univ x₀ y₀) (hf : ContDiffAt ℝ 1 f (x₀, y₀))
    (hφ : ContDiffAt ℝ 1 φ (x₀, y₀)) (hg : ∀ i, ContDiffAt ℝ 1 (g i) (x₀, y₀))
    (hreg : LowerLevelRegular g x₀ y₀) (hμ : (regularSubdiff (lowerValue φ g) x₀).Nonempty) :
    ∃ ν β : ι → ℝ, (∀ i, 0 ≤ β i) ∧ (∀ i, β i * g i (x₀, y₀) = 0) ∧
      (∀ i, ν i * g i (x₀, y₀) = 0) ∧
      fderiv ℝ f (x₀, y₀) + ∑ i, ν i • fderiv ℝ (g i) (x₀, y₀) = 0 ∧
      (fderiv ℝ φ (x₀, y₀)).comp (inr ℝ E F) +
        ∑ i, β i • (fderiv ℝ (g i) (x₀, y₀)).comp (inr ℝ E F) = 0 := by
  set p₀ : E × F := (x₀, y₀)
  have hp₀F : p₀ ∈ valueFeasible φ g univ := mem_valueFeasible_iff.2 ⟨mem_univ _, hy₀⟩
  have hp₀G : p₀ ∈ graph (lowerFeasible g) := hy₀.1
  have hr : lowerValue φ g x₀ = φ p₀ := lowerValue_eq_of_mem_lowerSolution hy₀
  obtain ⟨κ, hκ, hcalmκ⟩ := hcalm
  have hmin := eventually_nhdsWithin_iff.1
    (isLocalMinOn_penalizedObjective hκ hcalmκ hf.continuousAt hp₀F)
  obtain ⟨u, hu⟩ := hμ
  -- `(u, 0)` is a regular subgradient of `μ ∘ fst`
  have huM : u.comp (fst ℝ E F) ∈ regularSubdiff (fun p : E × F ↦ lowerValue φ g p.1) p₀ := by
    rw [regularSubdiff_comp_of_surjective (g := Prod.fst) hasStrictFDerivAt_fst
      (fun x ↦ ⟨(x, 0), rfl⟩)]
    exact ⟨u, hu, rfl⟩
  -- (6.65), via the penalized problem (6.40)
  have h1 : u.comp (fst ℝ E F) ∈ regularSubdiff (fun p ↦
      (graph (lowerFeasible g)).convex_indicator p + ((κ⁻¹ * f p + φ p : ℝ) : EReal)) p₀ := by
    refine regularSubdiff_subset_of_eventually_le (φ₂ := fun p : E × F ↦ lowerValue φ g p.1)
      (r₁ := κ⁻¹ * f p₀ + φ p₀) (r₂ := φ p₀) ?_ hr ?_ huM
    · rw [convex_indicator_of_mem hp₀G, ← EReal.coe_add, zero_add]
    · filter_upwards [hmin] with p hp
      by_cases hpG : p ∈ graph (lowerFeasible g)
      · have hpen := hp ⟨mem_univ _, hpG⟩
        rw [penalizedObjective_of_mem_valueFeasible hp₀F] at hpen
        rw [convex_indicator_of_mem hpG, ← EReal.coe_add, zero_add, ← EReal.coe_add]
        induction hμp : lowerValue φ g p.1 with
        | bot => rw [EReal.bot_add]; exact bot_le
        | top => exact absurd hμp (lowerValue_ne_top hpG)
        | coe c =>
          rw [penalizedObjective_of_eq hμp, EReal.coe_le_coe_iff] at hpen
          rw [← EReal.coe_add, EReal.coe_le_coe_iff]
          have hkey : κ⁻¹ * f p + φ p + φ p₀ - (c + (κ⁻¹ * f p₀ + φ p₀)) =
              κ⁻¹ * (f p + κ * φ p - κ * c - f p₀) := by field_simp; ring
          nlinarith [mul_nonneg (inv_nonneg.2 hκ.le) (sub_nonneg.2 hpen)]
      · rw [convex_indicator_of_notMem hpG, EReal.top_add_coe, EReal.top_add_coe]
        exact le_top
  -- (6.66)
  have h2 : u.comp (fst ℝ E F) ∈ regularSubdiff (fun p ↦
      (graph (lowerFeasible g)).convex_indicator p + (φ p : EReal)) p₀ := by
    refine regularSubdiff_subset_of_eventually_le (φ₂ := fun p : E × F ↦ lowerValue φ g p.1)
      (r₁ := φ p₀) (r₂ := φ p₀) ?_ hr ?_ huM
    · rw [convex_indicator_of_mem hp₀G, ← EReal.coe_add, zero_add]
    · filter_upwards with p
      by_cases hpG : p ∈ graph (lowerFeasible g)
      · rw [convex_indicator_of_mem hpG, ← EReal.coe_add, zero_add]
        exact add_le_add_left (lowerValue_le hpG) _
      · rw [convex_indicator_of_notMem hpG, EReal.top_add_coe, EReal.top_add_coe]
        exact le_top
  -- passing to basic subgradients and normals to `gph G`
  have hD : ∀ᶠ p in 𝓝 p₀, HasFDerivAt (fun p ↦ κ⁻¹ * f p + φ p)
      (κ⁻¹ • fderiv ℝ f p + fderiv ℝ φ p) p := by
    filter_upwards [eventually_hasFDerivAt_of_contDiffAt hf,
      eventually_hasFDerivAt_of_contDiffAt hφ] with p hf' hφ'
    exact (hf'.const_mul κ⁻¹).add hφ'
  have hDc : ContinuousAt (fun p ↦ κ⁻¹ • fderiv ℝ f p + fderiv ℝ φ p) p₀ :=
    ((continuousAt_fderiv_of_contDiffAt hf).const_smul κ⁻¹).add
      (continuousAt_fderiv_of_contDiffAt hφ)
  have n1 := (mem_subdiff_add_iff (φ := (graph (lowerFeasible g)).convex_indicator) hD hDc).1
    (regularSubdiff_subset_subdiff h1)
  have n2 := (mem_subdiff_add_iff (φ := (graph (lowerFeasible g)).convex_indicator)
    (eventually_hasFDerivAt_of_contDiffAt hφ) (continuousAt_fderiv_of_contDiffAt hφ)).1
    (regularSubdiff_subset_subdiff h2)
  rw [subdiff_convex_indicator] at n1 n2
  obtain ⟨β', -, hβ'cs, hβ'⟩ := normalCone_graph_lowerFeasible_subset hg hy₀.1 hreg n1
  obtain ⟨lam, hlam0, hlamcs, hlam⟩ := normalCone_graph_lowerFeasible_subset hg hy₀.1 hreg n2
  refine ⟨fun i ↦ κ * (β' i - lam i), lam, hlam0, hlamcs, fun i ↦ by
    rw [mul_assoc, sub_mul, hβ'cs i, hlamcs i, sub_zero, mul_zero], ?_, ?_⟩
  · refine ContinuousLinearMap.ext fun p ↦ ?_
    have e1 := congrArg (fun T : StrongDual ℝ (E × F) ↦ T p) hβ'
    have e2 := congrArg (fun T : StrongDual ℝ (E × F) ↦ T p) hlam
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul, sum_apply, coe_comp,
      Function.comp_apply, coe_fst'] at e1 e2
    simp only [add_apply, sum_apply, smul_apply, smul_eq_mul, zero_apply]
    have hsum : ∑ i, κ * (β' i - lam i) * fderiv ℝ (g i) p₀ p =
        κ * ∑ i, β' i * fderiv ℝ (g i) p₀ p - κ * ∑ i, lam i * fderiv ℝ (g i) p₀ p := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hsum, ← e1, ← e2]
    field_simp
    ring
  · ext y
    have e2 := congrArg (fun T : StrongDual ℝ (E × F) ↦ T (0, y)) hlam
    simp at e2 ⊢
    linarith

/-- Thm. 6.21 of [Mordukhovich 2018] (optimality conditions for smooth bilevel programs, I): let
`ȳ ∈ S(x̄)`, `x̄ ∈ Ω = {x | hⱼ(x) ≤ 0}` (6.50), let (6.34) be partially calm at `(x̄, ȳ)`, let
`f`, `φ`, `gᵢ` be `C¹` around `(x̄, ȳ)` and `hⱼ` around `x̄`, let `(x̄, ȳ)` be lower-level regular
and `x̄` upper-level regular, let `S` be inner semicontinuous at `(x̄, ȳ)` and nonempty-valued near
`x̄`, and let `μ` be l.s.c. around `x̄`. Then there are `κ > 0`, `λ, β ∈ ℝ^ι` and `α ∈ ℝ^J`
satisfying (6.54)–(6.59). -/
theorem exists_multipliers_smooth_bilevel_upper (hy₀ : y₀ ∈ lowerSolution φ g x₀)
    (hh₀ : ∀ j, h j x₀ ≤ 0) (hcalm : PartiallyCalm f φ g {x | ∀ j, h j x ≤ 0} x₀ y₀)
    (hf : ContDiffAt ℝ 1 f (x₀, y₀)) (hφ : ContDiffAt ℝ 1 φ (x₀, y₀))
    (hg : ∀ i, ContDiffAt ℝ 1 (g i) (x₀, y₀)) (hh : ∀ j, ContDiffAt ℝ 1 (h j) x₀)
    (hll : LowerLevelRegular g x₀ y₀) (hul : UpperLevelRegular h x₀)
    (hisc : InnerSemicontinuousAt (lowerSolution φ g) x₀ y₀)
    (hne : ∀ᶠ x in 𝓝 x₀, (lowerSolution φ g x).Nonempty)
    (hlsc : ∀ᶠ x in 𝓝 x₀, LowerSemicontinuousAt (lowerValue φ g) x) :
    ∃ κ > 0, ∃ lam β : ι → ℝ, ∃ α : J → ℝ,
      (fderiv ℝ f (x₀, y₀)).comp (inl ℝ E F) +
          ∑ i, (β i - κ * lam i) • (fderiv ℝ (g i) (x₀, y₀)).comp (inl ℝ E F) +
          ∑ j, α j • fderiv ℝ (h j) x₀ = 0 ∧
        (fderiv ℝ f (x₀, y₀)).comp (inr ℝ E F) + κ • (fderiv ℝ φ (x₀, y₀)).comp (inr ℝ E F) +
          ∑ i, β i • (fderiv ℝ (g i) (x₀, y₀)).comp (inr ℝ E F) = 0 ∧
        (fderiv ℝ φ (x₀, y₀)).comp (inr ℝ E F) +
          ∑ i, lam i • (fderiv ℝ (g i) (x₀, y₀)).comp (inr ℝ E F) = 0 ∧
        (∀ i, 0 ≤ lam i ∧ lam i * g i (x₀, y₀) = 0) ∧
        (∀ i, 0 ≤ β i ∧ β i * g i (x₀, y₀) = 0) ∧ (∀ j, 0 ≤ α j ∧ α j * h j x₀ = 0) := by
  classical
  set p₀ : E × F := (x₀, y₀)
  set Ω : Set E := {x | ∀ j, h j x ≤ 0}
  have hp₀F : p₀ ∈ valueFeasible φ g Ω := mem_valueFeasible_iff.2 ⟨hh₀, hy₀⟩
  obtain ⟨κ, hκ, hcalmκ⟩ := hcalm
  have hpen := isLocalMinOn_penalizedObjective hκ hcalmκ hf.continuousAt hp₀F
  -- `μ` is Lipschitz around `x̄`
  obtain ⟨U, hU, Lμ, μ', hμeq, hμL⟩ :=
    exists_lipschitzOnWith_lowerValue hy₀ hφ hg hll hisc hne hlsc
  have hμ₀ : μ' x₀ = φ p₀ := by
    have := hμeq x₀ (mem_of_mem_nhds hU)
    rw [lowerValue_eq_of_mem_lowerSolution hy₀] at this
    exact (EReal.coe_eq_coe_iff.1 this).symm
  have hUp : Prod.fst ⁻¹' U ∈ 𝓝 p₀ := (continuous_fst.tendsto p₀) hU
  -- the penalized problem (6.51) as a problem (6.11) with data indexed by `Option (ι ⊕ J)`
  let Φ : Option (ι ⊕ J) → E × F → ℝ := fun k ↦
    k.elim (fun p ↦ f p + κ * φ p - κ * μ' p.1) (Sum.elim g fun j p ↦ h j p.1)
  have hfeas : feasibleSet ∅ none univ Φ = {p : E × F | p.1 ∈ Ω ∧ p.2 ∈ lowerFeasible g p.1} := by
    ext p
    simp only [feasibleSet, mem_ofPred_eq, mem_univ, true_and, mem_empty_iff_false,
      not_false_eq_true, forall_const, IsEmpty.forall_iff, and_true]
    constructor
    · intro hk
      exact ⟨fun j ↦ hk (some (Sum.inr j)) (Option.some_ne_none _),
        fun i ↦ hk (some (Sum.inl i)) (Option.some_ne_none _)⟩
    · rintro ⟨hΩ, hG⟩ k hk
      rcases k with _ | i | j
      · exact absurd rfl hk
      · exact hG i
      · exact hΩ j
  have hmin : IsLocalMinOn (Φ none) (feasibleSet ∅ none univ Φ) p₀ := by
    rw [hfeas]
    filter_upwards [hpen, nhdsWithin_le_nhds hUp] with p hp hpU
    rw [penalizedObjective_of_mem_valueFeasible hp₀F, penalizedObjective_of_eq (hμeq p.1 hpU),
      EReal.coe_le_coe_iff] at hp
    show f p₀ + κ * φ p₀ - κ * μ' p₀.1 ≤ f p + κ * φ p - κ * μ' p.1
    rw [show p₀.1 = x₀ from rfl, hμ₀]
    linarith
  -- common Lipschitz data
  have hfst : ∀ (K : ℝ≥0) (V : Set E) (ψ : E → ℝ), LipschitzOnWith K ψ V →
      LipschitzOnWith (K * 1) (fun p : E × F ↦ ψ p.1) (Prod.fst ⁻¹' V) := fun K V ψ hψ ↦
    hψ.comp LipschitzWith.prod_fst.lipschitzOnWith fun _ hp ↦ hp
  have hLip : ∀ k, ∃ L : ℝ≥0, ∃ V ∈ 𝓝 p₀, LipschitzOnWith L (Φ k) V := by
    rintro (_ | i | j)
    · obtain ⟨K₁, V₁, hV₁, hL₁⟩ := hf.exists_lipschitzOnWith
      obtain ⟨K₂, V₂, hV₂, hL₂⟩ := hφ.exists_lipschitzOnWith
      set V := V₁ ∩ V₂ ∩ Prod.fst ⁻¹' U
      have hV : V ∈ 𝓝 p₀ := inter_mem (inter_mem hV₁ hV₂) hUp
      exact ⟨_, V, hV, ((hL₁.mono fun _ hp ↦ hp.1.1).add
        (lipschitzOnWith_const_mul (hL₂.mono fun _ hp ↦ hp.1.2) κ)).sub
        (lipschitzOnWith_const_mul ((hfst _ _ _ hμL).mono fun _ hp ↦ hp.2) κ)⟩
    · obtain ⟨K, V, hV, hL⟩ := (hg i).exists_lipschitzOnWith
      exact ⟨K, V, hV, hL⟩
    · obtain ⟨K, V, hV, hL⟩ := (hh j).exists_lipschitzOnWith
      exact ⟨_, _, (continuous_fst.tendsto p₀) hV, hfst _ _ _ hL⟩
  obtain ⟨V, hV, L, hL⟩ := exists_common_lipschitzOnWith hLip
  -- Thm. 6.10
  obtain ⟨lam, hlam0, hnn, hcs, h0⟩ := exists_multipliers_zero_mem_subdiff_lagrangian
    (Q := (∅ : Set (Option (ι ⊕ J)))) (k₀ := none) (Ω := univ) (φ := Φ) (notMem_empty _)
    (by rw [hfeas]; exact ⟨hh₀, hy₀.1⟩) hmin hV hL ⟨1, one_pos, by simpa using isClosed_closedBall⟩
  set l₀ := lam none
  set b : ι → ℝ := fun i ↦ lam (some (Sum.inl i))
  set a : J → ℝ := fun j ↦ lam (some (Sum.inr j))
  have hb0 : ∀ i, 0 ≤ b i := fun i ↦ hnn _ (notMem_empty _)
  have ha0 : ∀ j, 0 ≤ a j := fun j ↦ hnn _ (notMem_empty _)
  have hbcs : ∀ i, b i * g i p₀ = 0 := fun i ↦
    hcs (some (Sum.inl i)) (Option.some_ne_none _) (notMem_empty _)
  have hacs : ∀ j, a j * h j x₀ = 0 := fun j ↦
    hcs (some (Sum.inr j)) (Option.some_ne_none _) (notMem_empty _)
  -- the smooth part of the Lagrangian
  set Ψ : E × F → ℝ := fun p ↦ l₀ * (f p + κ * φ p) + ∑ i, b i * g i p + ∑ j, a j * h j p.1
  set Ψ' : E × F → StrongDual ℝ (E × F) := fun p ↦
    l₀ • (fderiv ℝ f p + κ • fderiv ℝ φ p) + ∑ i, b i • fderiv ℝ (g i) p +
      ∑ j, a j • (fderiv ℝ (h j) p.1).comp (fst ℝ E F)
  have hΨ : ∀ᶠ p in 𝓝 p₀, HasFDerivAt Ψ (Ψ' p) p := by
    filter_upwards [eventually_hasFDerivAt_of_contDiffAt hf,
      eventually_hasFDerivAt_of_contDiffAt hφ,
      eventually_all.2 fun i ↦ eventually_hasFDerivAt_of_contDiffAt (hg i),
      (continuous_fst.tendsto p₀).eventually
        (eventually_all.2 fun j ↦ eventually_hasFDerivAt_of_contDiffAt (hh j))] with p h1 h2 h3 h4
    exact ((((h1.add (h2.const_mul κ)).const_mul l₀).add
      (HasFDerivAt.sum (u := Finset.univ) fun i _ ↦ (h3 i).const_mul (b i))).add
      (HasFDerivAt.sum (u := Finset.univ) fun j _ ↦
        ((h4 j).comp p hasFDerivAt_fst).const_mul (a j))).congr_of_eventuallyEq
      (Eventually.of_forall fun q ↦ by simp [Ψ, Finset.sum_apply])
  have hΨc : ContinuousAt Ψ' p₀ :=
    ((((continuousAt_fderiv_of_contDiffAt hf).add
      ((continuousAt_fderiv_of_contDiffAt hφ).const_smul κ)).const_smul l₀).add
      (tendsto_finsetSum _ fun i _ ↦
        (continuousAt_fderiv_of_contDiffAt (hg i)).const_smul (b i))).add
      (tendsto_finsetSum _ fun j _ ↦
        (((continuousAt_fderiv_of_contDiffAt (hh j)).comp continuous_fst.continuousAt).clm_comp
          continuousAt_const).const_smul (a j))
  set c := l₀ * κ
  have hsub : (0 : StrongDual ℝ (E × F)) - Ψ' p₀ ∈
      subdiff (fun p ↦ ((c * -μ' p.1 : ℝ) : EReal)) p₀ := by
    refine (mem_subdiff_add_iff hΨ hΨc).1 ?_
    have hfun : (fun p ↦ (lagrangian Φ lam p : EReal) + univ.convex_indicator p) =
        fun p ↦ ((c * -μ' p.1 : ℝ) : EReal) + (Ψ p : EReal) := by
      funext p
      rw [convex_indicator_of_mem (mem_univ p), ← EReal.coe_add, ← EReal.coe_add]
      congr 1
      simp only [lagrangian, Fintype.sum_option, Fintype.sum_sum_type, Φ, Option.elim,
        Sum.elim_inl, Sum.elim_inr, Ψ, c, l₀, b, a]
      ring
    rw [← hfun]
    exact h0
  have hl₀ : 0 ≤ l₀ := hnn none (notMem_empty _)
  rcases hl₀.lt_or_eq with hl₀pos | hl₀0
  swap
  · -- `λ₀ = 0` contradicts the regularity conditions
    exfalso
    have hc0 : c = 0 := by simp [c, ← hl₀0]
    have hconst : subdiff (fun p : E × F ↦ ((c * -μ' p.1 : ℝ) : EReal)) p₀ = {0} := by
      simp only [hc0, zero_mul]
      exact subdiff_of_hasFDerivAt_of_continuousAt (f := fun _ ↦ 0) (f' := fun _ ↦ 0)
        (Eventually.of_forall fun p ↦ hasFDerivAt_const 0 p) continuousAt_const
    rw [hconst, mem_singleton_iff, zero_sub, neg_eq_zero] at hsub
    have hb : b = 0 := hll b hb0 (fun i hi ↦ (mul_eq_zero.1 (hbcs i)).resolve_right hi.ne) (by
      ext y
      have := congrArg (fun T : StrongDual ℝ (E × F) ↦ T (0, y)) hsub
      simpa [Ψ', ← hl₀0] using this)
    have ha : a = 0 := hul a ha0 (fun j hj ↦ (mul_eq_zero.1 (hacs j)).resolve_right hj.ne) (by
      ext x
      have := congrArg (fun T : StrongDual ℝ (E × F) ↦ T (x, 0)) hsub
      simpa [Ψ', ← hl₀0, hb] using this)
    apply hlam0
    funext k
    rcases k with _ | i | j
    · exact hl₀0.symm
    · exact congrFun hb i
    · exact congrFun ha j
  -- `λ₀ > 0`: the subgradient of `-μ`
  have hc : 0 < c := mul_pos hl₀pos hκ
  have hcm := subdiff_const_mul (f := fun p : E × F ↦ -μ' p.1) (x₀ := p₀) hc
  have hcf := subdiff_comp_fst (fun x ↦ ((-μ' x : ℝ) : EReal)) p₀
  rw [hcm, hcf] at hsub
  obtain ⟨_, ⟨w, hw, rfl⟩, hweq⟩ := hsub
  have hwco := neg_mem_convexHull_subdiff_of_mem_subdiff_neg hU hμL hw
  rw [subdiff_congr (eventually_of_mem hU fun x hx ↦ (hμeq x hx).symm)] at hwco
  obtain ⟨μl, hμl0, hμlcs, hμly, hμlx⟩ := convexHull_min
    (subdiff_lowerValue_subset hy₀ hφ hg hll hisc hne) convex_multiplierSet hwco
  -- normalization by `λ₀`
  refine ⟨κ, hκ, μl, fun i ↦ l₀⁻¹ * b i, fun j ↦ l₀⁻¹ * a j, ?_, ?_, hμly,
    fun i ↦ ⟨hμl0 i, hμlcs i⟩,
    fun i ↦ ⟨mul_nonneg (inv_nonneg.2 hl₀) (hb0 i), by rw [mul_assoc, hbcs i, mul_zero]⟩,
    fun j ↦ ⟨mul_nonneg (inv_nonneg.2 hl₀) (ha0 j), by rw [mul_assoc, hacs j, mul_zero]⟩⟩
  · ext x
    have e := congrArg (fun T : StrongDual ℝ (E × F) ↦ T (x, 0)) hweq
    have ex := congrArg (fun T : StrongDual ℝ E ↦ T x) hμlx
    simp only [Ψ', smul_apply, smul_eq_mul, coe_comp, Function.comp_apply, coe_fst', add_apply,
      sum_apply, zero_sub, neg_apply, inl_apply] at e ex
    simp only [add_apply, sum_apply, smul_apply, smul_eq_mul, coe_comp, Function.comp_apply,
      inl_apply, zero_apply]
    simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    field_simp
    simp only [c] at e
    linear_combination e + l₀ * κ * ex
  · ext y
    have e := congrArg (fun T : StrongDual ℝ (E × F) ↦ T (0, y)) hweq
    simp only [Ψ', smul_apply, smul_eq_mul, coe_comp, Function.comp_apply, coe_fst', add_apply,
      sum_apply, zero_sub, neg_apply, map_zero, mul_zero, Finset.sum_const_zero,
      add_zero] at e
    simp only [add_apply, sum_apply, smul_apply, smul_eq_mul, coe_comp, Function.comp_apply,
      inr_apply, zero_apply]
    simp only [mul_assoc, ← Finset.mul_sum]
    field_simp
    linear_combination e

end VariationalAnalysis
