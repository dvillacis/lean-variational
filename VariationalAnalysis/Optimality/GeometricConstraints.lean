/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Analysis.Convex.Continuous
import VariationalAnalysis.Subdifferential.SumRule
import VariationalAnalysis.Subdifferential.SymmetricMeanValue
import VariationalAnalysis.Normal.Intersection
import VariationalAnalysis.Subdifferential.Bridge
import VariationalAnalysis.Subdifferential.SmoothChain

/-!
# Optimality conditions under geometric constraints

Necessary optimality conditions for local minimizers of

  `minimize φ(x) subject to x ∈ Ω`                                  [Mordukhovich 2018, (6.1)]

and of its version (6.9) with finitely many constraint sets `Ω₁, …, Ωₛ`, following
[Mordukhovich 2018, Sect. 6.1.1].

A local minimizer of (6.1) is a point `x₀ ∈ Ω` with `IsLocalMinOn φ Ω x₀` at which `φ` is finite.

## Main results

* `neg_upperRegularSubdiff_subset_regularNormalCone`,
  `neg_upperRegularSubdiff_subset_normalCone`: Thm. 6.1(i) of [Mordukhovich 2018], the upper
  subdifferential conditions (6.3) `-∂̂⁺φ(x₀) ⊆ N̂(x₀; Ω)` and `-∂̂⁺φ(x₀) ⊆ N(x₀; Ω)`.
* `zero_mem_subdiff_add_normalCone_of_isLocalMinOn`: Thm. 6.1(ii) of [Mordukhovich 2018], the
  lower subdifferential condition (6.5) `0 ∈ ∂φ(x₀) + N(x₀; Ω)` under the qualification
  condition (6.4).
* `neg_mem_regularNormalCone_of_hasFDerivAt`: Remark 6.2(i) of [Mordukhovich 2018], the
  differentiable case `-∇φ(x₀) ∈ N̂(x₀; Ω)`.
* `neg_upperRegularSubdiff_subset_sum_normalCone`,
  `zero_mem_subdiff_add_sum_normalCone_of_isLocalMinOn`: Prop. 6.4 of [Mordukhovich 2018],
  the upper and lower subdifferential conditions for finitely many geometric constraints.

## Implementation notes

The book takes `φ : ℝⁿ → (-∞, ∞]`. Here `φ : E → EReal`, and for the lower subdifferential
condition we assume `φ ≠ ⊥` near `x₀`: in `EReal`, `⊥ + ⊤ = ⊥`, so otherwise `φ + δ_Ω` need not
have a local minimum at `x₀`. The book's standing assumptions (`φ` l.s.c. around `x₀`, `Ω`
locally closed around `x₀`) enter as local closedness of `epi φ` and of `Ω`.
-/

open Filter Topology Set Metric
open scoped Pointwise

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {φ : E → EReal} {Ω : Set E} {x₀ : E} {r : ℝ}

section Upper

/-- `-∂̂⁺φ(x₀) = ∂̂(-φ)(x₀)`. -/
theorem neg_upperRegularSubdiff :
    -upperRegularSubdiff φ x₀ = regularSubdiff (fun x ↦ -φ x) x₀ := by
  rw [upperRegularSubdiff, neg_neg]

/-- Thm. 6.1(i) of [Mordukhovich 2018], first inclusion in (6.3): at a local minimizer `x₀` of
`φ` over `Ω`, `-∂̂⁺φ(x₀) ⊆ N̂(x₀; Ω)`. No semicontinuity is needed. -/
theorem neg_upperRegularSubdiff_subset_regularNormalCone (hmin : IsLocalMinOn φ Ω x₀)
    (hx : x₀ ∈ Ω) (hr : φ x₀ = r) :
    -upperRegularSubdiff φ x₀ ⊆ regularNormalCone Ω x₀ := by
  intro w hw
  rw [neg_upperRegularSubdiff] at hw
  -- a function `ψ ≤ -φ` near `x₀`, differentiable at `x₀` with `∇ψ(x₀) = w` (Thm. 1.27)
  obtain ⟨ψ, hψ, hψ0, hle⟩ :=
    (mem_regularSubdiff_iff_exists_support (φ := fun x ↦ -φ x) (r := -r)
      (by simp [hr])).1 hw
  -- `x₀` maximizes `ψ` over `Ω` near `x₀`
  have hmax : ∀ᶠ x in 𝓝[Ω] x₀, ψ x ≤ ψ x₀ := by
    filter_upwards [hmin, nhdsWithin_le_nhds hle] with x hx1 hx2
    rw [hψ0, ← EReal.coe_le_coe_iff]
    refine hx2.trans ?_
    rw [EReal.coe_neg, ← hr]
    exact EReal.neg_le_neg_iff.2 hx1
  refine ⟨hx, fun ε hε ↦ ?_⟩
  filter_upwards [hmax, nhdsWithin_le_nhds (hψ.isLittleO.def hε)] with x h1 h2
  rw [Real.norm_eq_abs, abs_le] at h2
  linarith [h2.1]

/-- Thm. 6.1(i) of [Mordukhovich 2018], second inclusion in (6.3): at a local minimizer `x₀` of
`φ` over `Ω`, `-∂̂⁺φ(x₀) ⊆ N(x₀; Ω)`. -/
theorem neg_upperRegularSubdiff_subset_normalCone (hmin : IsLocalMinOn φ Ω x₀)
    (hx : x₀ ∈ Ω) (hr : φ x₀ = r) :
    -upperRegularSubdiff φ x₀ ⊆ normalCone Ω x₀ :=
  (neg_upperRegularSubdiff_subset_regularNormalCone hmin hx hr).trans
    regularNormalCone_subset_normalCone

/-- The derivative of a differentiable function is an upper regular subgradient. -/
theorem mem_upperRegularSubdiff_of_hasFDerivAt {f : E → ℝ} {f' : StrongDual ℝ E}
    (hf : HasFDerivAt f f' x₀) : f' ∈ upperRegularSubdiff (fun x ↦ (f x : EReal)) x₀ := by
  rw [mem_upperRegularSubdiff_iff, show (fun x ↦ -((f x : ℝ) : EReal)) =
    fun x ↦ (((-f) x : ℝ) : EReal) from funext fun x ↦ by simp,
    regularSubdiff_of_hasFDerivAt hf.neg]
  rfl

/-- Remark 6.2(i) of [Mordukhovich 2018]: if `f` is differentiable at a local minimizer `x₀` of
`f` over `Ω`, then `-∇f(x₀) ∈ N̂(x₀; Ω)`. -/
theorem neg_mem_regularNormalCone_of_hasFDerivAt {f : E → ℝ} {f' : StrongDual ℝ E}
    (hf : HasFDerivAt f f' x₀) (hmin : IsLocalMinOn f Ω x₀) (hx : x₀ ∈ Ω) :
    -f' ∈ regularNormalCone Ω x₀ := by
  refine neg_upperRegularSubdiff_subset_regularNormalCone (φ := fun x ↦ (f x : EReal))
    (r := f x₀) ?_ hx rfl (Set.neg_mem_neg.2 (mem_upperRegularSubdiff_of_hasFDerivAt hf))
  filter_upwards [hmin] with x hx
  exact EReal.coe_le_coe_iff.2 hx

end Upper

section Lower

omit [NormedSpace ℝ E] in
/-- At a local minimizer of `φ` over `Ω` where `φ ≠ ⊥` nearby, `φ + δ_Ω` has an unconstrained
local minimum. -/
theorem isLocalMin_add_convex_indicator (hmin : IsLocalMinOn φ Ω x₀) (hx : x₀ ∈ Ω)
    (hbot : ∀ᶠ x in 𝓝 x₀, φ x ≠ ⊥) :
    IsLocalMin (fun x ↦ φ x + Ω.convex_indicator x) x₀ := by
  have hmin' := eventually_nhdsWithin_iff.1 hmin
  filter_upwards [hmin', hbot] with x h1 h2
  simp only [convex_indicator_of_mem hx, EReal.coe_zero, add_zero]
  by_cases hxΩ : x ∈ Ω
  · simpa [convex_indicator_of_mem hxΩ] using h1 hxΩ
  · rw [convex_indicator_of_notMem hxΩ, EReal.add_top_of_ne_bot h2]
    exact le_top

variable [FiniteDimensional ℝ E]

/-- Thm. 6.1(ii) of [Mordukhovich 2018], (6.5): let `x₀` be a local minimizer of `φ` over `Ω`,
with `epi φ` locally closed around `(x₀, φ x₀)` (e.g. `φ` l.s.c. around `x₀`), `Ω` locally closed
around `x₀` and `φ ≠ ⊥` near `x₀`. Under the qualification condition (6.4)
`∂^∞φ(x₀) ∩ (-N(x₀; Ω)) = {0}`, we have `0 ∈ ∂φ(x₀) + N(x₀; Ω)`. -/
theorem zero_mem_subdiff_add_normalCone_of_isLocalMinOn (hmin : IsLocalMinOn φ Ω x₀)
    (hx : x₀ ∈ Ω) (hr : φ x₀ = r) (hbot : ∀ᶠ x in 𝓝 x₀, φ x ≠ ⊥)
    (hlocφ : ∃ ρ > 0, IsClosed (φ.Epi univ ∩ closedBall ((x₀, r) : E × ℝ) ρ))
    (hlocΩ : ∃ ρ > 0, IsClosed (Ω ∩ closedBall x₀ ρ))
    (hqc : ∀ v ∈ singularSubdiff φ x₀, -v ∈ normalCone Ω x₀ → v = 0) :
    (0 : StrongDual ℝ E) ∈ subdiff φ x₀ + normalCone Ω x₀ := by
  have hδ : Ω.convex_indicator x₀ = ((0 : ℝ) : EReal) := convex_indicator_of_mem hx
  have h0 := zero_mem_subdiff_of_isLocalMin (isLocalMin_add_convex_indicator hmin hx hbot)
    (add_apply_eq_coe hr hδ)
  have hsum := subdiff_add_subset hr hδ hlocφ (locallyClosed_epi_convex_indicator hlocΩ)
    (by rwa [singularSubdiff_convex_indicator]) h0
  rwa [subdiff_convex_indicator] at hsum

/-- Thm. 6.1(ii) of [Mordukhovich 2018], (6.5), first form: `∂φ(x₀) ∩ (-N(x₀; Ω)) ≠ ∅`. -/
theorem exists_mem_subdiff_neg_mem_normalCone_of_isLocalMinOn (hmin : IsLocalMinOn φ Ω x₀)
    (hx : x₀ ∈ Ω) (hr : φ x₀ = r) (hbot : ∀ᶠ x in 𝓝 x₀, φ x ≠ ⊥)
    (hlocφ : ∃ ρ > 0, IsClosed (φ.Epi univ ∩ closedBall ((x₀, r) : E × ℝ) ρ))
    (hlocΩ : ∃ ρ > 0, IsClosed (Ω ∩ closedBall x₀ ρ))
    (hqc : ∀ v ∈ singularSubdiff φ x₀, -v ∈ normalCone Ω x₀ → v = 0) :
    ∃ v ∈ subdiff φ x₀, -v ∈ normalCone Ω x₀ := by
  obtain ⟨v, hv, w, hw, hvw⟩ :=
    zero_mem_subdiff_add_normalCone_of_isLocalMinOn hmin hx hr hbot hlocφ hlocΩ hqc
  exact ⟨v, hv, by rwa [neg_eq_of_add_eq_zero_right hvw]⟩

end Lower

section Many

/-! ### Finitely many geometric constraints -/

variable {ι : Type*} [Fintype ι] {Ω : ι → Set E}

omit [NormedSpace ℝ E] [Fintype ι] in
theorem locallyClosed_iInter [Finite ι] (hloc : ∀ i, ∃ ρ > 0, IsClosed (Ω i ∩ closedBall x₀ ρ)) :
    ∃ ρ > 0, IsClosed ((⋂ i, Ω i) ∩ closedBall x₀ ρ) := by
  have := Fintype.ofFinite ι
  simpa using locallyClosed_biInter (Ω := Ω) (x₀ := x₀) Finset.univ fun i _ ↦ hloc i

variable [FiniteDimensional ℝ E]

/-- Prop. 6.4(i) of [Mordukhovich 2018]: let `x₀` be a local minimizer of `φ` over `⋂ᵢ Ωᵢ` with
the sets `Ωᵢ` locally closed around `x₀`. Under the constraint qualification (6.10), we have the
upper subdifferential inclusion `-∂̂⁺φ(x₀) ⊆ N(x₀; Ω₁) + ⋯ + N(x₀; Ωₛ)`. -/
theorem neg_upperRegularSubdiff_subset_sum_normalCone (hmin : IsLocalMinOn φ (⋂ i, Ω i) x₀)
    (hx : x₀ ∈ ⋂ i, Ω i) (hr : φ x₀ = r)
    (hloc : ∀ i, ∃ ρ > 0, IsClosed (Ω i ∩ closedBall x₀ ρ))
    (hqc : ∀ v : ι → StrongDual ℝ E, (∀ i, v i ∈ normalCone (Ω i) x₀) → ∑ i, v i = 0 →
      ∀ i, v i = 0) :
    -upperRegularSubdiff φ x₀ ⊆ ∑ i, normalCone (Ω i) x₀ :=
  (neg_upperRegularSubdiff_subset_normalCone hmin hx hr).trans (normalCone_iInter_subset hloc hqc)

/-- Prop. 6.4(ii) of [Mordukhovich 2018]: let `x₀` be a local minimizer of `φ` over `⋂ᵢ Ωᵢ`,
with `epi φ` locally closed around `(x₀, φ x₀)`, the sets `Ωᵢ` locally closed around `x₀` and
`φ ≠ ⊥` near `x₀`. Under the qualification condition
`[v + ∑ᵢ vᵢ = 0, v ∈ ∂^∞φ(x₀), vᵢ ∈ N(x₀; Ωᵢ)] ⟹ v = vᵢ = 0`, we have
`0 ∈ ∂φ(x₀) + N(x₀; Ω₁) + ⋯ + N(x₀; Ωₛ)`. -/
theorem zero_mem_subdiff_add_sum_normalCone_of_isLocalMinOn
    (hmin : IsLocalMinOn φ (⋂ i, Ω i) x₀) (hx : x₀ ∈ ⋂ i, Ω i) (hr : φ x₀ = r)
    (hbot : ∀ᶠ x in 𝓝 x₀, φ x ≠ ⊥)
    (hlocφ : ∃ ρ > 0, IsClosed (φ.Epi univ ∩ closedBall ((x₀, r) : E × ℝ) ρ))
    (hloc : ∀ i, ∃ ρ > 0, IsClosed (Ω i ∩ closedBall x₀ ρ))
    (hqc : ∀ v ∈ singularSubdiff φ x₀, ∀ w : ι → StrongDual ℝ E,
      (∀ i, w i ∈ normalCone (Ω i) x₀) → v + ∑ i, w i = 0 → v = 0 ∧ ∀ i, w i = 0) :
    (0 : StrongDual ℝ E) ∈ subdiff φ x₀ + ∑ i, normalCone (Ω i) x₀ := by
  -- the qualification condition implies (6.10)
  have hqc' : ∀ w : ι → StrongDual ℝ E, (∀ i, w i ∈ normalCone (Ω i) x₀) → ∑ i, w i = 0 →
      ∀ i, w i = 0 := fun w hw hs ↦
    (hqc 0 (zero_mem_singularSubdiff hr) w hw (by rw [hs, add_zero])).2
  have hinter := normalCone_iInter_subset hloc hqc'
  -- the qualification condition (6.4) for `⋂ᵢ Ωᵢ`
  have hqc₁ : ∀ v ∈ singularSubdiff φ x₀, -v ∈ normalCone (⋂ i, Ω i) x₀ → v = 0 := by
    intro v hv hv'
    obtain ⟨w, hw, hws⟩ := (Set.mem_finsetSum _ _ _).1 (hinter hv')
    exact (hqc v hv w (fun i ↦ hw (Finset.mem_univ i)) (by rw [hws, add_neg_cancel])).1
  exact Set.add_subset_add_left hinter
    (zero_mem_subdiff_add_normalCone_of_isLocalMinOn hmin hx hr hbot hlocφ
      (locallyClosed_iInter hloc) hqc₁)

end Many

section DC

/-! ### Difference-of-convex problems -/

variable {φ₁ : E → EReal} {φ₂ : E → ℝ}

omit [NormedSpace ℝ E] in
/-- Prop. 6.3 of [Mordukhovich 2018], first part: `x₀` is a local minimizer of `φ₁ - φ₂` (6.6) iff
`(x₀, φ₁ x₀)` is a local minimizer of the concave function `ψ(x, α) = α - φ₂(x)` over `epi φ₁`
(6.7). Here `φ₂` is real-valued and continuous at `x₀`, which is the case for every convex
`φ₂ : E → ℝ` in finite dimensions; no convexity of `φ₁` is needed. -/
theorem isLocalMin_sub_iff_isLocalMinOn_epi (hr : φ₁ x₀ = r) (hφ₂ : ContinuousAt φ₂ x₀) :
    IsLocalMin (fun x ↦ φ₁ x - φ₂ x) x₀ ↔
      IsLocalMinOn (fun p : E × ℝ ↦ p.2 - φ₂ p.1) (φ₁.Epi univ) (x₀, r) := by
  constructor
  · intro hmin
    have hfst : Tendsto Prod.fst (𝓝[φ₁.Epi univ] ((x₀, r) : E × ℝ)) (𝓝 x₀) :=
      (continuous_fst.tendsto _).mono_left nhdsWithin_le_nhds
    filter_upwards [hfst.eventually hmin, self_mem_nhdsWithin] with p hp hpE
    obtain ⟨x, α⟩ := p
    have hle : φ₁ x ≤ α := hpE.2
    simp only [hr] at hp ⊢
    induction h : φ₁ x with
    | bot =>
      rw [h, EReal.bot_sub, ← EReal.coe_sub] at hp
      exact absurd (le_bot_iff.1 hp) (EReal.coe_ne_bot _)
    | top => rw [h] at hle; simp at hle
    | coe a =>
      rw [h, ← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff] at hp
      rw [h, EReal.coe_le_coe_iff] at hle
      linarith
  · intro hmin
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hmin)
    obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.1 hφ₂ (δ / 2) (half_pos hδ)
    filter_upwards [Metric.ball_mem_nhds x₀ (lt_min hδ hη)] with x hx
    rw [mem_ball, lt_min_iff] at hx
    simp only [hr]
    by_contra hlt
    rw [not_le] at hlt
    -- `φ₁ x < β` for the real number `β = r - φ₂ x₀ + φ₂ x`
    set β := r - φ₂ x₀ + φ₂ x with hβ
    have hlt' : φ₁ x < β := by
      induction h : φ₁ x with
      | bot => exact EReal.bot_lt_coe β
      | top => rw [h] at hlt; simp at hlt
      | coe a =>
        rw [h, ← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_lt_coe_iff] at hlt
        rw [EReal.coe_lt_coe_iff]; linarith
    obtain ⟨a, ha₁, ha₂⟩ := EReal.lt_iff_exists_real_btwn.1 hlt'
    rw [EReal.coe_lt_coe_iff] at ha₂
    set α := max a (β - δ / 4)
    have hd := hcont hx.2
    rw [Real.dist_eq, abs_lt] at hd
    have hα : |α - r| < δ := by
      rw [abs_lt]
      constructor
      · have := le_max_right a (β - δ / 4); linarith
      · have := max_lt ha₂ (show β - δ / 4 < β by linarith); linarith
    have hmem : ((x, α) : E × ℝ) ∈ φ₁.Epi univ :=
      ⟨mem_univ _, ha₁.le.trans (EReal.coe_le_coe_iff.2 (le_max_left _ _))⟩
    have hdist : dist ((x, α) : E × ℝ) (x₀, r) < δ := by
      rw [Prod.dist_eq, max_lt_iff, Real.dist_eq]; exact ⟨hx.1, hα⟩
    have := hball hdist hmem
    have := max_lt ha₂ (show β - δ / 4 < β by linarith)
    simp only at *
    linarith

variable [FiniteDimensional ℝ E]

/-- Regular subgradients of `(x, α) ↦ f(x) - α`: they are the functionals `(v, -1)` with
`v ∈ ∂̂f(x)`. -/
theorem regularSubdiff_sub_snd {f : E → ℝ} (p : E × ℝ) :
    regularSubdiff (fun q : E × ℝ ↦ ((f q.1 - q.2 : ℝ) : EReal)) p =
      (fun v : StrongDual ℝ E ↦ v.coprod (-1)) '' regularSubdiff (fun x ↦ (f x : EReal)) p.1 := by
  have hfun : (fun q : E × ℝ ↦ ((f q.1 - q.2 : ℝ) : EReal)) =
      fun q ↦ (f q.1 : EReal) + ((-q.2 : ℝ) : EReal) := by
    funext q; rw [sub_eq_add_neg, EReal.coe_add]
  have hd : HasFDerivAt (fun q : E × ℝ ↦ -q.2) (-ContinuousLinearMap.snd ℝ E ℝ) p :=
    hasFDerivAt_snd.neg
  have hcomp := regularSubdiff_comp_of_surjective (ψ := fun x ↦ (f x : EReal)) (g := Prod.fst)
    (y₀ := p) hasStrictFDerivAt_fst (fun x ↦ ⟨(x, 0), rfl⟩)
  ext ℓ
  rw [hfun, mem_regularSubdiff_add_iff hd, sub_neg_eq_add, hcomp]
  simp only [mem_image]
  refine exists_congr fun v ↦ and_congr_right fun _ ↦ ?_
  constructor
  · intro h
    rw [eq_sub_of_add_eq h.symm]
    ext <;> simp
  · rintro rfl
    ext <;> simp

/-- Prop. 6.3 of [Mordukhovich 2018], second part: for the problem (6.7), the second upper
subdifferential condition (6.3), i.e. (6.8), is equivalent to `∂̂φ₂(x₀) ⊆ ∂φ₁(x₀)`. -/
theorem neg_upperRegularSubdiff_subset_normalCone_epi_iff (hr : φ₁ x₀ = r) :
    -upperRegularSubdiff (fun p : E × ℝ ↦ ((p.2 - φ₂ p.1 : ℝ) : EReal)) (x₀, r) ⊆
        normalCone (φ₁.Epi univ) (x₀, r) ↔
      regularSubdiff (fun x ↦ (φ₂ x : EReal)) x₀ ⊆ subdiff φ₁ x₀ := by
  have h : -upperRegularSubdiff (fun p : E × ℝ ↦ ((p.2 - φ₂ p.1 : ℝ) : EReal)) (x₀, r) =
      (fun v : StrongDual ℝ E ↦ v.coprod (-1)) '' regularSubdiff (fun x ↦ (φ₂ x : EReal)) x₀ := by
    rw [neg_upperRegularSubdiff, ← regularSubdiff_sub_snd (x₀, r)]
    congr 1
    funext q
    rw [← EReal.coe_neg, neg_sub]
  rw [h, image_subset_iff]
  exact forall₂_congr fun v _ ↦ (mem_subdiff_iff hr).symm

/-- Prop. 6.3 of [Mordukhovich 2018] (DC optimization problems): if `x₀` is a local minimizer of
`φ₁ - φ₂` with `φ₁ x₀` finite and `φ₂ : E → ℝ` convex, then `∂φ₂(x₀) ⊆ ∂φ₁(x₀)`. For convex
`φ₁` both sides are subdifferentials of convex analysis (`mem_subdiff_of_convex`). -/
theorem subdiff_subset_subdiff_of_isLocalMin_sub (hr : φ₁ x₀ = r)
    (hφ₂ : ConvexOn ℝ univ φ₂) (hmin : IsLocalMin (fun x ↦ φ₁ x - φ₂ x) x₀) :
    subdiff (fun x ↦ (φ₂ x : EReal)) x₀ ⊆ subdiff φ₁ x₀ := by
  have hcont : ContinuousAt φ₂ x₀ :=
    (hφ₂.continuousOn isOpen_univ).continuousAt univ_mem
  have hmin' := (isLocalMin_sub_iff_isLocalMinOn_epi hr hcont).1 hmin
  have hminE : IsLocalMinOn (fun p : E × ℝ ↦ ((p.2 - φ₂ p.1 : ℝ) : EReal)) (φ₁.Epi univ)
      (x₀, r) := by
    filter_upwards [hmin'] with p hp
    exact EReal.coe_le_coe_iff.2 hp
  have hx : ((x₀, r) : E × ℝ) ∈ φ₁.Epi univ := ⟨mem_univ _, hr.le⟩
  rw [subdiff_eq_regularSubdiff_of_convex (convex_epi_of_convexOn hφ₂),
    ← neg_upperRegularSubdiff_subset_normalCone_epi_iff hr]
  exact neg_upperRegularSubdiff_subset_normalCone hminE hx rfl

end DC

end VariationalAnalysis
