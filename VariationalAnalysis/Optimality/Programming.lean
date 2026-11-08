/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import VariationalAnalysis.Optimality.GeometricConstraints
import VariationalAnalysis.Subdifferential.ProductRule
import VariationalAnalysis.Extremal.Basic
import VariationalAnalysis.Normal.Product
import VariationalAnalysis.Subdifferential.SmoothSupport
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Nondifferentiable programming

Necessary optimality conditions for the problem of nondifferentiable programming
[Mordukhovich 2018, (6.11)]

  `minimize φ₀(x)` subject to `φᵢ(x) ≤ 0` (`i = 1, …, m`), `φᵢ(x) = 0` (`i = m+1, …, m+r`),
  `x ∈ Ω`,

following [Mordukhovich 2018, Sect. 6.1.2–6.1.3].

## Setting

All functional data are indexed by one finite type `K`: `φ : K → E → ℝ`, a cost index `k₀ : K`,
and a set `Q ⊆ K` of equality indices with `k₀ ∉ Q`. The remaining indices `k ∉ Q`, `k ≠ k₀`, are
inequality constraints. The Lagrangian with multipliers `λ : K → ℝ` is `∑ₖ λₖ φₖ`.

## Main results

* `exists_mem_normalCone_epi_graph`: Thm. 6.5(i) of [Mordukhovich 2018], Fritz John conditions
  via normals to the epigraphs and graphs of the separate data (l.s.c. `EReal` data).
* `exists_multipliers_zero_mem_sum_separateSubdiff`: Thm. 6.5(ii), via separate subgradients of
  Lipschitz data.
* `exists_multipliers_zero_mem_sum_symmSeparateSubdiff`: Cor. 6.6, via symmetric subgradients for
  the equality constraints.
* `exists_multipliers_zero_mem_subdiff_lagrangian`,
  `exists_multipliers_zero_mem_subdiff_lagrangian_add_normalCone`: Thm. 6.10 (condensed lower
  subdifferential optimality conditions), both inclusions in (6.23).
* `exists_multipliers_abstract_maximum_principle`: Cor. 6.11 (abstract maximum principle).
* `exists_multipliers_upperRegularSubdiff`: Thm. 6.12 (upper subdifferential optimality
  conditions), in inner product spaces.

## Proof strategy

For Thm. 6.10, as in the book, the multipliers come from the extremal principle applied to the set
`ℰ = {(x, α) | x ∈ Ω, φₖ(x) ≤ αₖ (k ∉ Q), φₖ(x) = αₖ (k ∈ Q)}` and a ball times a point. The
book then invokes "the scalarization formula of Thm. 1.32 and its proof" to turn the normal
`(0, -λ) ∈ N(ℰ)` into `0 ∈ ∂(∑ₖ λₖ φₖ + δ_Ω)`. Here this step is proved directly: a regular normal
`(u, -λ)` to `ℰ` gives `u ∈ ∂̂(∑ₖ λₖ φₖ + δ_Ω)` (`mem_regularSubdiff_of_mem_regularNormalCone`), and
the passage to the limit absorbs the change of multipliers into `ω`-subgradients
(Thm. 1.28, `subdiff_eq_outerLimit_epsSubdiff`).
-/

open Filter Topology Set Metric
open scoped Pointwise NNReal

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {K : Type*} [Fintype K] [DecidableEq K]

section ConstraintGraph

variable (φ : K → E → ℝ) (Q : Set K) (Ω : Set E)

/-- The set `ℰ(φ₀, …, φ_{m+r}, Ω)` of [Mordukhovich 2018, proof of Thm. 6.10]. -/
def constraintGraph : Set (E × (K → ℝ)) :=
  {p | p.1 ∈ Ω ∧ (∀ k ∉ Q, φ k p.1 ≤ p.2 k) ∧ ∀ k ∈ Q, φ k p.1 = p.2 k}

/-- The multipliers `λₖ = -ℓ(0, eₖ)` of a functional `ℓ` on `E × ℝ^K`, so that
`ℓ = (ℓ ∘ inl, -λ)`. -/
def multipliers (ℓ : StrongDual ℝ (E × (K → ℝ))) (k : K) : ℝ :=
  -ℓ (0, Pi.single k 1)

/-- The Lagrangian `∑ₖ λₖ φₖ`. -/
def lagrangian (lam : K → ℝ) (x : E) : ℝ :=
  ∑ k, lam k * φ k x

variable {φ Q Ω}

theorem apply_zero_pi (ℓ : StrongDual ℝ (E × (K → ℝ))) (β : K → ℝ) :
    ℓ (0, β) = -∑ k, multipliers ℓ k * β k := by
  have h : ((0 : E), β) = ∑ k, β k • ((0 : E), (Pi.single k (1 : ℝ) : K → ℝ)) := by
    ext j
    · simp [Prod.fst_sum]
    · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  rw [h, map_sum]
  simp only [map_smul, smul_eq_mul, multipliers]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

theorem apply_prod (ℓ : StrongDual ℝ (E × (K → ℝ))) (a : E) (β : K → ℝ) :
    ℓ (a, β) = ℓ.comp (ContinuousLinearMap.inl ℝ E (K → ℝ)) a - ∑ k, multipliers ℓ k * β k := by
  have : ((a, β) : E × (K → ℝ)) = (a, 0) + (0, β) := by simp
  rw [this, map_add, apply_zero_pi, sub_eq_add_neg]
  rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq K] in
theorem lagrangian_sub (lam : K → ℝ) (x y : E) :
    lagrangian φ lam y - lagrangian φ lam x = ∑ k, lam k * (φ k y - φ k x) := by
  simp only [lagrangian, ← Finset.sum_sub_distrib, mul_sub]

omit [NormedSpace ℝ E] [DecidableEq K] in
/-- A finite combination of Lipschitz functions is Lipschitz. -/
theorem lipschitzOnWith_lagrangian {U : Set E} {L : ℝ≥0}
    (hL : ∀ k, LipschitzOnWith L (φ k) U) (lam : K → ℝ) :
    LipschitzOnWith (∑ k, ‖lam k‖₊ * L) (lagrangian φ lam) U := by
  classical
  unfold lagrangian
  induction (Finset.univ : Finset K) using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (lipschitzOnWith_const_mul (hL j) (lam j)).add ih

/-- A direction `d` along which `p + t d ∈ Ω` for all small `t > 0` is polar to the regular
normals: `ℓ d ≤ 0` for `ℓ ∈ N̂(p; Ω)`. -/
theorem apply_nonpos_of_mem_regularNormalCone {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {S : Set F} {p d : F} {ℓ : StrongDual ℝ F}
    (hℓ : ℓ ∈ regularNormalCone S p) (hd : ∀ᶠ t in 𝓝[>] (0 : ℝ), p + t • d ∈ S) : ℓ d ≤ 0 := by
  by_contra hpos
  rw [not_le] at hpos
  set ε := ℓ d / (2 * (‖d‖ + 1))
  have hε : 0 < ε := by positivity
  have hT : Tendsto (fun t : ℝ ↦ p + t • d) (𝓝[>] 0) (𝓝[S] p) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hd⟩
    have : Tendsto (fun t : ℝ ↦ p + t • d) (𝓝 0) (𝓝 (p + (0 : ℝ) • d)) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  obtain ⟨t, ht, htpos⟩ := ((hT.eventually (hℓ.2 ε hε)).and self_mem_nhdsWithin).exists
  have htpos' : 0 < t := htpos
  simp only [add_sub_cancel_left, map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs,
    abs_of_pos htpos'] at ht
  have h1 : ℓ d ≤ ε * ‖d‖ :=
    (mul_le_mul_iff_of_pos_left htpos').1 (by linarith : t * ℓ d ≤ t * (ε * ‖d‖))
  have h2 : ε * ‖d‖ < ℓ d := by
    have hd0 : 0 ≤ ‖d‖ := norm_nonneg d
    have : ε * ‖d‖ ≤ ℓ d / 2 := by
      simp only [ε]
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
      nlinarith
    linarith
  linarith

omit [Fintype K] in
/-- Moving the `k`-th level `α_k` of a point of `ℰ` up by `t ≥ 0` stays in `ℰ` for `k ∉ Q`. -/
theorem add_smul_single_mem_constraintGraph {p : E × (K → ℝ)} (hp : p ∈ constraintGraph φ Q Ω)
    {k : K} (hk : k ∉ Q) {t : ℝ} (ht : 0 ≤ t) :
    p + t • ((0 : E), (Pi.single k 1 : K → ℝ)) ∈ constraintGraph φ Q Ω := by
  refine ⟨by simpa using hp.1, fun j hj ↦ ?_, fun j hj ↦ ?_⟩
  · have h1 := hp.2.1 j hj
    have h2 : 0 ≤ t * (Pi.single k (1 : ℝ) : K → ℝ) j := by
      rw [Pi.single_apply]; split_ifs <;> simp [ht]
    simp only [Prod.fst_add, Prod.smul_fst, smul_zero, add_zero, Prod.snd_add, Prod.smul_snd,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  · have hjk : j ≠ k := fun h ↦ hk (h ▸ hj)
    simpa [Pi.single_apply, hjk] using hp.2.2 j hj

omit [Fintype K] in
/-- Moving the `k`-th level of a point of `ℰ` down by `t` stays in `ℰ` while `t ≤ α_k - φ_k(x)`. -/
theorem sub_smul_single_mem_constraintGraph {p : E × (K → ℝ)} (hp : p ∈ constraintGraph φ Q Ω)
    {k : K} (hk : k ∉ Q) {t : ℝ} (ht : t ≤ p.2 k - φ k p.1) :
    p + t • ((0 : E), -(Pi.single k 1 : K → ℝ)) ∈ constraintGraph φ Q Ω := by
  refine ⟨by simpa using hp.1, fun j hj ↦ ?_, fun j hj ↦ ?_⟩
  · have h1 := hp.2.1 j hj
    simp only [Prod.fst_add, Prod.smul_fst, smul_zero, add_zero, Prod.snd_add, Prod.smul_snd,
      Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Pi.single_apply]
    split_ifs with hjk
    · subst hjk; linarith
    · simpa using h1
  · have hjk : j ≠ k := fun h ↦ hk (h ▸ hj)
    simpa [Pi.single_apply, hjk] using hp.2.2 j hj

/-- Regular normals to `ℰ` have nonnegative inequality multipliers. -/
theorem multipliers_nonneg_of_mem_regularNormalCone {p : E × (K → ℝ)}
    (hp : p ∈ constraintGraph φ Q Ω) {ℓ : StrongDual ℝ (E × (K → ℝ))}
    (hℓ : ℓ ∈ regularNormalCone (constraintGraph φ Q Ω) p) {k : K} (hk : k ∉ Q) :
    0 ≤ multipliers ℓ k := by
  have := apply_nonpos_of_mem_regularNormalCone hℓ
    (eventually_nhdsWithin_of_forall fun t ht ↦
      add_smul_single_mem_constraintGraph hp hk (le_of_lt ht))
  simp only [multipliers]; linarith

/-- Regular normals to `ℰ` vanish on inactive inequality levels: if `φ_k(x) < α_k`, then
`λ_k = 0`. -/
theorem multipliers_eq_zero_of_mem_regularNormalCone {p : E × (K → ℝ)}
    (hp : p ∈ constraintGraph φ Q Ω) {ℓ : StrongDual ℝ (E × (K → ℝ))}
    (hℓ : ℓ ∈ regularNormalCone (constraintGraph φ Q Ω) p) {k : K} (hk : k ∉ Q)
    (hlt : φ k p.1 < p.2 k) : multipliers ℓ k = 0 := by
  have h1 := multipliers_nonneg_of_mem_regularNormalCone hp hℓ hk
  have h2 := apply_nonpos_of_mem_regularNormalCone hℓ (d := ((0 : E), -(Pi.single k 1 : K → ℝ)))
    (by
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (sub_pos.2 hlt))] with t ht
      exact sub_smul_single_mem_constraintGraph hp hk (le_of_lt ht))
  have : ((0 : E), -(Pi.single k 1 : K → ℝ)) = -((0 : E), (Pi.single k 1 : K → ℝ)) := by simp
  rw [this, map_neg] at h2
  simp only [multipliers] at h1 ⊢
  linarith

/-- The key step in the proof of Thm. 6.10 of [Mordukhovich 2018]: if the data `φₖ` are
Lipschitz around `x = p.1` and `ℓ = (u, -λ)` is a regular normal to `ℰ` at `p`, then
`u ∈ ∂̂(∑ₖ λₖ φₖ + δ_Ω)(x)`. -/
theorem mem_regularSubdiff_of_mem_regularNormalCone {U : Set E} {L : ℝ≥0} {p : E × (K → ℝ)}
    (hU : U ∈ 𝓝 p.1) (hL : ∀ k, LipschitzOnWith L (φ k) U)
    (hp : p ∈ constraintGraph φ Q Ω) {ℓ : StrongDual ℝ (E × (K → ℝ))}
    (hℓ : ℓ ∈ regularNormalCone (constraintGraph φ Q Ω) p) :
    ℓ.comp (ContinuousLinearMap.inl ℝ E (K → ℝ)) ∈
      regularSubdiff (fun y ↦ (lagrangian φ (multipliers ℓ) y : EReal) + Ω.convex_indicator y)
        p.1 := by
  obtain ⟨x, α⟩ := p
  simp only at hU hp ⊢
  set lam := multipliers ℓ
  set u := ℓ.comp (ContinuousLinearMap.inl ℝ E (K → ℝ))
  have hr : (lagrangian φ lam x : EReal) + Ω.convex_indicator x = (lagrangian φ lam x : ℝ) := by
    simp [convex_indicator_of_mem hp.1]
  rw [mem_regularSubdiff_iff (φ := fun y ↦ (lagrangian φ lam y : EReal) + Ω.convex_indicator y)
    hr]
  intro ε hε
  set C : ℝ := 1 + L
  have hC : 0 < C := by positivity
  -- the lift `y ↦ (y, α + Φ(y) - Φ(x))` of `Ω` into `ℰ`
  set q : E → E × (K → ℝ) := fun y ↦ (y, fun k ↦ α k + φ k y - φ k x)
  have hq_mem : ∀ y ∈ Ω, q y ∈ constraintGraph φ Q Ω := fun y hy ↦
    ⟨hy, fun k hk ↦ by have := hp.2.1 k hk; simp only [q]; linarith,
      fun k hk ↦ by have := hp.2.2 k hk; simp only [q]; linarith⟩
  have hq_x : q x = (x, α) := by simp [q]
  have hq_cont : ContinuousAt q x :=
    continuousAt_id.prodMk (continuousAt_pi.2 fun k ↦
      continuousAt_const.add ((hL k).continuousOn.continuousAt hU) |>.sub continuousAt_const)
  have hq_sub : ∀ y, q y - (x, α) = (y - x, fun k ↦ φ k y - φ k x) := fun y ↦ by
    ext k <;> simp [q]; ring
  have hq_norm : ∀ y ∈ U, ‖q y - (x, α)‖ ≤ C * ‖y - x‖ := fun y hy ↦ by
    rw [hq_sub, Prod.norm_def, max_le_iff]
    have hx : x ∈ U := mem_of_mem_nhds hU
    refine ⟨by simp only [C]; nlinarith [mul_nonneg L.coe_nonneg (norm_nonneg (y - x))], ?_⟩
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k ↦ ?_
    have := (hL k).dist_le_mul y hy x hx
    rw [Real.dist_eq, dist_eq_norm] at this
    rw [Real.norm_eq_abs]
    simp only [C]; nlinarith [norm_nonneg (y - x)]
  have hT : Tendsto q (𝓝[Ω] x) (𝓝[constraintGraph φ Q Ω] (x, α)) :=
    tendsto_nhdsWithin_iff.2 ⟨(hq_x ▸ hq_cont.tendsto).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall hq_mem⟩
  have hev := eventually_nhdsWithin_iff.1 (hT.eventually (hℓ.2 (ε / C) (div_pos hε hC)))
  filter_upwards [hev, hU] with y hy hyU
  by_cases hyΩ : y ∈ Ω
  · rw [convex_indicator_of_mem hyΩ, ← EReal.coe_add, add_zero, EReal.coe_le_coe_iff]
    have h1 := hy hyΩ
    rw [hq_sub, apply_prod] at h1
    have h2 := mul_le_mul_of_nonneg_left (hq_norm y hyU) (div_pos hε hC).le
    rw [hq_sub] at h2
    have h3 : ε / C * (C * ‖y - x‖) = ε * ‖y - x‖ := by field_simp
    have h4 := lagrangian_sub (φ := φ) lam x y
    linarith
  · rw [convex_indicator_of_notMem hyΩ, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
    exact le_top

omit [Fintype K] [DecidableEq K] in
/-- If `v` is a regular subgradient of `f + h + δ_Ω` at `x` and `h` is `M`-Lipschitz around `x`,
then `v` is an `M`-subgradient of `f + δ_Ω` at `x`. -/
theorem mem_epsSubdiff_of_mem_regularSubdiff_add {f h : E → ℝ} {U : Set E} {M : ℝ≥0} {x : E}
    {v : StrongDual ℝ E} (hU : U ∈ 𝓝 x) (hh : LipschitzOnWith M h U)
    (hv : v ∈ regularSubdiff (fun y ↦ ((f y + h y : ℝ) : EReal) + Ω.convex_indicator y) x) :
    v ∈ epsSubdiff M (fun y ↦ (f y : EReal) + Ω.convex_indicator y) x := by
  obtain ⟨s, hs, hv⟩ := hv
  beta_reduce at hs hv
  have hx : x ∈ Ω := by
    by_contra hx
    rw [convex_indicator_of_notMem hx, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)] at hs
    exact EReal.coe_ne_top s hs.symm
  rw [convex_indicator_of_mem hx, ← EReal.coe_add, add_zero, EReal.coe_eq_coe_iff] at hs
  refine ⟨f x, by simp [convex_indicator_of_mem hx], fun ε hε ↦ ?_⟩
  have hxU : x ∈ U := mem_of_mem_nhds hU
  filter_upwards [hv ε hε, hU] with y hy hyU
  by_cases hyΩ : y ∈ Ω
  · rw [convex_indicator_of_mem hyΩ, ← EReal.coe_add, add_zero, EReal.coe_le_coe_iff] at hy ⊢
    have hL := hh.dist_le_mul y hyU x hxU
    rw [Real.dist_eq, dist_eq_norm, abs_le] at hL
    rw [← hs] at hy
    nlinarith [hL.1]
  · rw [convex_indicator_of_notMem hyΩ, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
    exact le_top

omit [NormedSpace ℝ E] [Fintype K] [DecidableEq K] in
/-- The epigraph of `f + δ_Ω` is locally closed if `f` is continuous around `x₀` and `Ω` is
locally closed around `x₀`. -/
theorem locallyClosed_epi_add_convex_indicator {f : E → ℝ} {U : Set E} {x₀ : E}
    (hU : U ∈ 𝓝 x₀) (hf : ContinuousOn f U) (hΩ : ∃ ρ > 0, IsClosed (Ω ∩ closedBall x₀ ρ))
    (α : ℝ) :
    ∃ ρ > 0, IsClosed ((fun x ↦ (f x : EReal) + Ω.convex_indicator x).Epi univ ∩
      closedBall ((x₀, α) : E × ℝ) ρ) := by
  have h : (fun x ↦ (f x : EReal) + Ω.convex_indicator x).Epi univ =
      (fun x ↦ (f x : EReal)).Epi univ ∩ Ω ×ˢ univ := by
    ext ⟨x, a⟩
    by_cases hx : x ∈ Ω
    · simp [Function.Epi, convex_indicator_of_mem hx, hx]
    · simp [Function.Epi, convex_indicator_of_notMem hx, hx,
        EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
  rw [h]
  exact locallyClosed_inter (locallyClosed_epi_of_continuousOn hU hf α)
    (locallyClosed_prod hΩ ⟨1, one_pos, isClosed_univ.inter isClosed_closedBall⟩)

theorem tendsto_multipliers {w : ℕ → StrongDual ℝ (E × (K → ℝ))} {ℓ : StrongDual ℝ (E × (K → ℝ))}
    (hw : Tendsto w atTop (𝓝 ℓ)) (k : K) :
    Tendsto (fun n ↦ multipliers (w n) k) atTop (𝓝 (multipliers ℓ k)) :=
  (((ContinuousLinearMap.apply ℝ ℝ ((0 : E), (Pi.single k 1 : K → ℝ))).continuous.tendsto ℓ).comp
    hw).neg

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq K] in
theorem lagrangian_add (lam μ : K → ℝ) (y : E) :
    lagrangian φ (lam + μ) y = lagrangian φ lam y + lagrangian φ μ y := by
  simp only [lagrangian, Pi.add_apply, add_mul, Finset.sum_add_distrib]

variable [FiniteDimensional ℝ E]

/-- Limiting normals to `ℰ`: if the data `φₖ` are Lipschitz around `x = p.1`, `Ω` is locally
closed around `x`, and `ℓ = (u, -λ) ∈ N(p; ℰ)`, then `λₖ ≥ 0` for `k ∉ Q`, `λₖ = 0` for inactive
levels `φₖ(x) < αₖ`, and `u ∈ ∂(∑ₖ λₖ φₖ + δ_Ω)(x)`. -/
theorem mem_subdiff_of_mem_normalCone_constraintGraph {U : Set E} {L : ℝ≥0} {p : E × (K → ℝ)}
    (hU : U ∈ 𝓝 p.1) (hL : ∀ k, LipschitzOnWith L (φ k) U)
    (hΩ : ∃ ρ > 0, IsClosed (Ω ∩ closedBall p.1 ρ)) {ℓ : StrongDual ℝ (E × (K → ℝ))}
    (hℓ : ℓ ∈ normalCone (constraintGraph φ Q Ω) p) :
    (∀ k ∉ Q, 0 ≤ multipliers ℓ k) ∧ (∀ k ∉ Q, φ k p.1 < p.2 k → multipliers ℓ k = 0) ∧
      ℓ.comp (ContinuousLinearMap.inl ℝ E (K → ℝ)) ∈
        subdiff (fun y ↦ (lagrangian φ (multipliers ℓ) y : EReal) + Ω.convex_indicator y) p.1 := by
  obtain ⟨hp, a, w, ha, hw, hmem⟩ := hℓ
  have ha1 : Tendsto a atTop (𝓝 p) := (tendsto_nhdsWithin_iff.1 ha).1
  have ha2 : ∀ᶠ n in atTop, a n ∈ constraintGraph φ Q Ω := (tendsto_nhdsWithin_iff.1 ha).2
  have hlam := tendsto_multipliers hw
  have hfst : Tendsto (fun n ↦ (a n).1) atTop (𝓝 p.1) := (continuous_fst.tendsto p).comp ha1
  refine ⟨fun k hk ↦ ge_of_tendsto (hlam k)
    (ha2.mono fun n hn ↦ multipliers_nonneg_of_mem_regularNormalCone hn (hmem n) hk),
    fun k hk hlt ↦ ?_, ?_⟩
  · have hc : Tendsto (fun n ↦ (a n).2 k - φ k (a n).1) atTop (𝓝 (p.2 k - φ k p.1)) :=
      (((continuous_apply k).tendsto _).comp ((continuous_snd.tendsto p).comp ha1)).sub
        ((((hL k).continuousOn.continuousAt hU).tendsto).comp hfst)
    refine tendsto_nhds_unique (hlam k) (tendsto_const_nhds.congr' ?_)
    filter_upwards [hc.eventually (lt_mem_nhds (sub_pos.2 hlt)), ha2] with n hn hn2
    exact (multipliers_eq_zero_of_mem_regularNormalCone hn2 (hmem n) hk (by linarith)).symm
  set lam := multipliers ℓ
  set F := fun y ↦ (lagrangian φ lam y : EReal) + Ω.convex_indicator y
  have hF : F p.1 = (lagrangian φ lam p.1 : ℝ) := by simp [F, convex_indicator_of_mem hp.1]
  have hLip := lipschitzOnWith_lagrangian hL lam
  have hint : ∀ᶠ n in atTop, U ∈ 𝓝 (a n).1 := by
    filter_upwards [hfst.eventually (interior_mem_nhds.2 hU)] with n hn
    exact mem_interior_iff_mem_nhds.1 hn
  set M : ℕ → ℝ≥0 := fun n ↦ ∑ k, ‖(multipliers (w n) - lam) k‖₊ * L
  have hM : Tendsto (fun n ↦ (M n : ℝ)) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset K) fun k _ ↦
      (((hlam k).sub_const (lam k)).norm.mul_const (L : ℝ))
    simpa [M] using this
  rw [subdiff_eq_outerLimit_epsSubdiff hF
    (locallyClosed_epi_add_convex_indicator hU hLip.continuousOn hΩ _)]
  refine mem_outerLimit_of_eventually (fun n ↦ ((a n).1, (M n : ℝ)))
    (fun n ↦ (w n).comp (ContinuousLinearMap.inl ℝ E (K → ℝ))) ?_ ?_ ?_
  · refine Tendsto.prodMk (tendsto_funNhds_iff.2 ⟨hfst, ?_⟩)
      (tendsto_nhdsWithin_iff.2 ⟨hM, Eventually.of_forall fun n ↦ (M n).coe_nonneg⟩)
    rw [hF]
    refine (EReal.tendsto_coe.2 (((hLip.continuousOn.continuousAt hU).tendsto).comp hfst)).congr' ?_
    filter_upwards [ha2] with n hn
    simp [F, convex_indicator_of_mem hn.1]
  · exact (((ContinuousLinearMap.compL ℝ E (E × (K → ℝ)) ℝ).flip
      (ContinuousLinearMap.inl ℝ E (K → ℝ))).continuous.tendsto ℓ).comp hw
  · filter_upwards [ha2, hint] with n hn hnU
    have hA := mem_regularSubdiff_of_mem_regularNormalCone hnU hL hn (hmem n)
    have hsplit : multipliers (w n) = lam + (multipliers (w n) - lam) := by abel
    rw [hsplit] at hA
    simp only [lagrangian_add] at hA
    exact mem_epsSubdiff_of_mem_regularSubdiff_add hnU (lipschitzOnWith_lagrangian hL _) hA

end ConstraintGraph

section Condensed

variable {φ : K → E → ℝ} {Q : Set K} {k₀ : K} {Ω : Set E} {x₀ : E}

variable (Q k₀ Ω) in
/-- The feasible set of the problem of nondifferentiable programming (6.11): `x ∈ Ω`,
`φₖ(x) ≤ 0` for the inequality indices `k ∉ Q`, `k ≠ k₀`, and `φₖ(x) = 0` for `k ∈ Q`. The data
take values in `ℝ` or in `EReal`. -/
def feasibleSet {β : Type*} [Zero β] [LE β] (φ : K → E → β) : Set E :=
  {x | x ∈ Ω ∧ (∀ k, k ≠ k₀ → k ∉ Q → φ k x ≤ 0) ∧ ∀ k ∈ Q, φ k x = 0}

omit [NormedSpace ℝ E] [DecidableEq K] in
/-- `ℰ` is locally closed around any of its points if `Ω` is locally closed and the `φₖ` are
continuous around the base point. -/
theorem locallyClosed_constraintGraph {U : Set E} {p : E × (K → ℝ)} (hU : U ∈ 𝓝 p.1)
    (hc : ∀ k, ContinuousOn (φ k) U) (hΩ : ∃ ρ > 0, IsClosed (Ω ∩ closedBall p.1 ρ)) :
    ∃ ρ > 0, IsClosed (constraintGraph φ Q Ω ∩ closedBall p ρ) := by
  obtain ⟨ρ₁, hρ₁, hc₁⟩ := hΩ
  obtain ⟨ρ₂, hρ₂, hsub⟩ := nhds_basis_closedBall.mem_iff.1 hU
  set ρ := min ρ₁ ρ₂
  have hρ : 0 < ρ := lt_min hρ₁ hρ₂
  have hfst : ∀ {z : E × (K → ℝ)}, z ∈ closedBall p ρ → z.1 ∈ closedBall p.1 ρ := by
    intro z hz
    rw [mem_closedBall] at hz ⊢
    exact (by rw [Prod.dist_eq]; exact le_max_left _ _ : dist z.1 p.1 ≤ dist z p).trans hz
  set S := ((Ω ∩ closedBall p.1 ρ) ×ˢ (univ : Set (K → ℝ))) ∩ closedBall p ρ
  have hS : IsClosed S :=
    ((isClosed_inter_closedBall_of_le hc₁ (min_le_left _ _)).prod isClosed_univ).inter
      isClosed_closedBall
  set G : E × (K → ℝ) → (K → ℝ) × (K → ℝ) := fun z ↦ (fun k ↦ φ k z.1, z.2)
  have hG : ContinuousOn G S := by
    refine ContinuousOn.prodMk (continuousOn_pi.2 fun k ↦ ?_) continuous_snd.continuousOn
    refine ((hc k).mono fun x hx ↦ hsub ?_).comp continuous_fst.continuousOn fun z hz ↦ hz.1.1.2
    exact closedBall_subset_closedBall (min_le_right _ _) hx
  have hT : IsClosed {w : (K → ℝ) × (K → ℝ) | (∀ k ∉ Q, w.1 k ≤ w.2 k) ∧ ∀ k ∈ Q, w.1 k = w.2 k} := by
    simp only [ofPred_and, ofPred_forall]
    exact (isClosed_iInter fun k ↦ isClosed_iInter fun _ ↦ isClosed_le (by fun_prop)
      (by fun_prop)).inter (isClosed_iInter fun k ↦ isClosed_iInter fun _ ↦ isClosed_eq
      (by fun_prop) (by fun_prop))
  refine ⟨ρ, hρ, ?_⟩
  have heq : constraintGraph φ Q Ω ∩ closedBall p ρ = S ∩ G ⁻¹' {w | (∀ k ∉ Q, w.1 k ≤ w.2 k) ∧
      ∀ k ∈ Q, w.1 k = w.2 k} := by
    ext z
    simp only [constraintGraph, S, G, mem_inter_iff, mem_ofPred_eq, mem_prod, mem_univ, and_true,
      mem_preimage]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, hz⟩; exact ⟨⟨⟨h1, hfst hz⟩, hz⟩, h2, h3⟩
    · rintro ⟨⟨⟨h1, -⟩, hz⟩, h2, h3⟩; exact ⟨⟨h1, h2, h3⟩, hz⟩
  rw [heq]
  exact hG.preimage_isClosed_of_isClosed hS hT

variable [FiniteDimensional ℝ E]

/-- Thm. 6.10 of [Mordukhovich 2018] (condensed lower subdifferential optimality conditions),
first inclusion in (6.23): let `x₀` be a local minimizer of `φ_{k₀}` over the feasible set of
(6.11), with all `φₖ` Lipschitz around `x₀` and `Ω` locally closed around `x₀`. Then there are
multipliers `λ ≠ 0` with `λₖ ≥ 0` for `k ∉ Q`, the complementary slackness conditions (6.16), and
`0 ∈ ∂(∑ₖ λₖ φₖ + δ_Ω)(x₀) = ∂_x 𝓛_Ω(x₀, λ)`. -/
theorem exists_multipliers_zero_mem_subdiff_lagrangian (hk₀ : k₀ ∉ Q)
    (hx : x₀ ∈ feasibleSet Q k₀ Ω φ) (hmin : IsLocalMinOn (φ k₀) (feasibleSet Q k₀ Ω φ) x₀)
    {U : Set E} {L : ℝ≥0} (hU : U ∈ 𝓝 x₀) (hL : ∀ k, LipschitzOnWith L (φ k) U)
    (hΩ : ∃ ρ > 0, IsClosed (Ω ∩ closedBall x₀ ρ)) :
    ∃ lam : K → ℝ, lam ≠ 0 ∧ (∀ k ∉ Q, 0 ≤ lam k) ∧
      (∀ k, k ≠ k₀ → k ∉ Q → lam k * φ k x₀ = 0) ∧
      (0 : StrongDual ℝ E) ∈
        subdiff (fun x ↦ (lagrangian φ lam x : EReal) + Ω.convex_indicator x) x₀ := by
  set c := φ k₀ x₀
  set αb : K → ℝ := Pi.single k₀ c
  set pb : E × (K → ℝ) := (x₀, αb)
  have hαb_ne : ∀ k, k ≠ k₀ → αb k = 0 := fun k hk ↦ by simp [αb, hk]
  have hpb : pb ∈ constraintGraph φ Q Ω := by
    refine ⟨hx.1, fun k hk ↦ ?_, fun k hk ↦ ?_⟩
    · by_cases hkk : k = k₀
      · subst hkk; simp [pb, αb, c]
      · simpa [pb, hαb_ne k hkk] using hx.2.1 k hkk hk
    · have hkk : k ≠ k₀ := fun h ↦ hk₀ (h ▸ hk)
      simpa [pb, hαb_ne k hkk] using hx.2.2 k hk
  -- a radius on which `x₀` minimizes `φ_{k₀}` over the feasible set
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hmin)
  set Ω₂ : Set (E × (K → ℝ)) := closedBall x₀ (δ / 2) ×ˢ {αb}
  -- the shifts `(0, -tₙ e_{k₀})` with `tₙ = 1 / (n + 1)`
  set d : E × (K → ℝ) := ((0 : E), -(Pi.single k₀ (1 : ℝ) : K → ℝ))
  set t : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have ht : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have htpos : ∀ n, 0 < t n := fun n ↦ by positivity
  have hext : IsLocallyExtremal ![constraintGraph φ Q Ω, Ω₂] pb := by
    rw [isLocallyExtremal_iff]
    refine ⟨fun i ↦ ?_, fun i n ↦ if i = 0 then t n • d else 0, fun i ↦ ?_, univ, univ_mem,
      Eventually.of_forall fun n z _ ↦ ?_⟩
    · fin_cases i
      · exact hpb
      · exact ⟨mem_closedBall_self (by positivity), rfl⟩
    · fin_cases i
      · simpa using ht.smul_const d
      · exact tendsto_const_nhds
    · by_contra hcon
      push Not at hcon
      have h0 := hcon 0
      have h1 := hcon 1
      simp only [Fin.isValue, Matrix.cons_val_zero, if_true, Matrix.cons_val_one,
        one_ne_zero, if_false, add_zero] at h0 h1
      obtain ⟨hz1, hz2⟩ := h1
      obtain ⟨x, α⟩ := z
      simp only [mem_singleton_iff] at hz2
      subst hz2
      obtain ⟨hxΩ, hle, heq⟩ := h0
      simp only [d, Prod.fst_add, Prod.smul_fst, smul_zero, add_zero, Prod.snd_add,
        Prod.smul_snd, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at hxΩ hle heq
      have hfeas : x ∈ feasibleSet Q k₀ Ω φ := by
        refine ⟨hxΩ, fun k hk hkQ ↦ ?_, fun k hk ↦ ?_⟩
        · simpa [hαb_ne k hk, Pi.single_eq_of_ne hk] using hle k hkQ
        · have hkk : k ≠ k₀ := fun h ↦ hk₀ (h ▸ hk)
          simpa [hαb_ne k hkk, Pi.single_eq_of_ne hkk] using heq k hk
      have hdist : dist x x₀ < δ := by
        have := mem_closedBall.1 hz1; linarith
      have hmin' := hball hdist hfeas
      have hk := hle k₀ hk₀
      simp only [αb, Pi.single_eq_same, mul_neg, mul_one] at hk
      linarith [htpos n]
  have hlocΩ₂ : ∃ ρ > 0, IsClosed (Ω₂ ∩ closedBall pb ρ) :=
    ⟨1, one_pos, (isClosed_closedBall.prod isClosed_singleton).inter isClosed_closedBall⟩
  obtain ⟨v, hv, hv₂, hv1⟩ := hext.exists_mem_normalCone_pair
    (locallyClosed_constraintGraph hU (fun k ↦ (hL k).continuousOn) hΩ) hlocΩ₂
  -- the `E`-component of `v` vanishes since `x₀` is interior to the ball
  have hinl : v.comp (ContinuousLinearMap.inl ℝ E (K → ℝ)) = 0 := by
    have := (mem_normalCone_prod_iff.1 hv₂).1
    rw [normalCone_of_mem_interior (mem_interior_iff_mem_nhds.2
      (closedBall_mem_nhds x₀ (half_pos hδ))), mem_singleton_iff] at this
    rw [← neg_eq_zero, ← this]
    rfl
  obtain ⟨hnn, hzero, hsub⟩ := mem_subdiff_of_mem_normalCone_constraintGraph hU hL hΩ hv
  refine ⟨multipliers v, fun hlam ↦ ?_, hnn, fun k hk hkQ ↦ ?_, hinl ▸ hsub⟩
  · -- `λ = 0` would force `v = 0`
    have : v = 0 := by
      ext z
      · simpa using congrArg (fun f ↦ f z) hinl
      · change v ((0 : E), z) = 0
        rw [apply_zero_pi, hlam]; simp
    rw [this, norm_zero] at hv1
    exact zero_ne_one hv1
  · rcases (hx.2.1 k hk hkQ).lt_or_eq with hlt | heq
    · rw [hzero k hkQ (by simpa [pb, hαb_ne k hk] using hlt), zero_mul]
    · rw [heq, mul_zero]

/-- Thm. 6.10 of [Mordukhovich 2018], both inclusions in (6.23):
`0 ∈ ∂_x 𝓛_Ω(x₀, λ) ⊆ ∂_x 𝓛(x₀, λ) + N(x₀; Ω)`. -/
theorem exists_multipliers_zero_mem_subdiff_lagrangian_add_normalCone (hk₀ : k₀ ∉ Q)
    (hx : x₀ ∈ feasibleSet Q k₀ Ω φ) (hmin : IsLocalMinOn (φ k₀) (feasibleSet Q k₀ Ω φ) x₀)
    {U : Set E} {L : ℝ≥0} (hU : U ∈ 𝓝 x₀) (hL : ∀ k, LipschitzOnWith L (φ k) U)
    (hΩ : ∃ ρ > 0, IsClosed (Ω ∩ closedBall x₀ ρ)) :
    ∃ lam : K → ℝ, lam ≠ 0 ∧ (∀ k ∉ Q, 0 ≤ lam k) ∧
      (∀ k, k ≠ k₀ → k ∉ Q → lam k * φ k x₀ = 0) ∧
      (0 : StrongDual ℝ E) ∈
        subdiff (fun x ↦ (lagrangian φ lam x : EReal) + Ω.convex_indicator x) x₀ ∧
      (0 : StrongDual ℝ E) ∈ subdiff (fun x ↦ (lagrangian φ lam x : EReal)) x₀ + normalCone Ω x₀ := by
  obtain ⟨lam, hne, hnn, hcs, h0⟩ :=
    exists_multipliers_zero_mem_subdiff_lagrangian hk₀ hx hmin hU hL hΩ
  refine ⟨lam, hne, hnn, hcs, h0, ?_⟩
  have := subdiff_lipschitz_add_subset (convex_indicator_of_mem hx.1)
    (locallyClosed_epi_convex_indicator hΩ) hU (lipschitzOnWith_lagrangian hL lam) h0
  rwa [subdiff_convex_indicator] at this

end Condensed

section Separate

/-! ### Separate subgradients of the data -/

variable {φ : K → E → ℝ} {Q : Set K} {k₀ : K} {Ω : Set E} {x₀ : E}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq K] in
theorem coe_sum_ereal (a : K → ℝ) : (((∑ k, a k : ℝ)) : EReal) = ∑ k, ((a k : ℝ) : EReal) := by
  classical
  induction (Finset.univ : Finset K) using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, EReal.coe_add, ih]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq K] in
theorem sum_subset_sum {F : Type*} [AddCommMonoid F] {A B : K → Set F} (h : ∀ k, A k ⊆ B k) :
    ∑ k, A k ⊆ ∑ k, B k := by
  intro v hv
  obtain ⟨g, hg, rfl⟩ := (Set.mem_fintype_sum _ _).1 hv
  exact (Set.mem_fintype_sum _ _).2 ⟨g, fun k ↦ h k (hg k), rfl⟩

variable [FiniteDimensional ℝ E]

omit [Fintype K] [DecidableEq K] in
/-- Subgradients of `c f` for `f` Lipschitz around `x₀`: `∂(c f)(x₀) ⊆ |c| (∂f(x₀) ∪ ∂(-f)(x₀))`,
and `∂(c f)(x₀) ⊆ c ∂f(x₀)` if `c ≥ 0`. -/
theorem subdiff_const_mul_subset {f : E → ℝ} {U : Set E} {L : ℝ≥0} (hU : U ∈ 𝓝 x₀)
    (hL : LipschitzOnWith L f U) (c : ℝ) :
    subdiff (fun x ↦ ((c * f x : ℝ) : EReal)) x₀ ⊆
      |c| • (subdiff (fun x ↦ (f x : EReal)) x₀ ∪ subdiff (fun x ↦ ((-f x : ℝ) : EReal)) x₀) ∧
    (0 ≤ c → subdiff (fun x ↦ ((c * f x : ℝ) : EReal)) x₀ ⊆
      c • subdiff (fun x ↦ (f x : EReal)) x₀) := by
  have hzero : c = 0 → subdiff (fun x ↦ ((c * f x : ℝ) : EReal)) x₀ ⊆
      c • subdiff (fun x ↦ (f x : EReal)) x₀ := by
    rintro rfl
    have h : subdiff (fun x ↦ (((0 : ℝ) * f x : ℝ) : EReal)) x₀ = {0} := by
      simpa using subdiff_of_hasFDerivAt_of_continuousAt (f := fun _ : E ↦ (0 : ℝ))
        (f' := fun _ ↦ 0) (x₀ := x₀) (Eventually.of_forall fun x ↦ hasFDerivAt_const 0 x)
        continuousAt_const
    rw [h, Set.zero_smul_set (subdiff_nonempty_of_lipschitz hU hL)]
    intro v hv
    simpa using hv
  have hpos : 0 ≤ c → subdiff (fun x ↦ ((c * f x : ℝ) : EReal)) x₀ ⊆
      c • subdiff (fun x ↦ (f x : EReal)) x₀ := fun hc ↦ by
    rcases hc.lt_or_eq with hc | hc
    · rw [subdiff_const_mul hc]
    · exact hzero hc.symm
  refine ⟨?_, hpos⟩
  rcases le_or_gt 0 c with hc | hc
  · rw [abs_of_nonneg hc]
    exact (hpos hc).trans (Set.smul_set_mono subset_union_left)
  · have : (fun x ↦ ((c * f x : ℝ) : EReal)) = fun x ↦ ((|c| * (-f x) : ℝ) : EReal) := by
      funext x; rw [abs_of_neg hc]; ring_nf
    rw [this, subdiff_const_mul (abs_pos.2 hc.ne)]
    exact Set.smul_set_mono subset_union_right

variable (φ Q x₀) in
/-- The sets `∂φₖ(x₀)` for `k ∉ Q` and `∂φₖ(x₀) ∪ ∂(-φₖ)(x₀)` for `k ∈ Q` in (6.17). -/
def separateSubdiff (k : K) : Set (StrongDual ℝ E) :=
  {v | v ∈ subdiff (fun x ↦ (φ k x : EReal)) x₀ ∨
    (k ∈ Q ∧ v ∈ subdiff (fun x ↦ ((-φ k x : ℝ) : EReal)) x₀)}

/-- Thm. 6.5(ii) of [Mordukhovich 2018], (6.17)–(6.18): let `x₀` be a local minimizer of
`φ_{k₀}` over the feasible set of (6.11), with all `φₖ` Lipschitz around `x₀` and `Ω` locally
closed around `x₀`. Then there are nonnegative multipliers `λ ≠ 0` satisfying the complementary
slackness conditions and
`0 ∈ ∑_{k ∉ Q} λₖ ∂φₖ(x₀) + ∑_{k ∈ Q} λₖ [∂φₖ(x₀) ∪ ∂(-φₖ)(x₀)] + N(x₀; Ω)`. -/
theorem exists_multipliers_zero_mem_sum_separateSubdiff (hk₀ : k₀ ∉ Q)
    (hx : x₀ ∈ feasibleSet Q k₀ Ω φ) (hmin : IsLocalMinOn (φ k₀) (feasibleSet Q k₀ Ω φ) x₀)
    {U : Set E} {L : ℝ≥0} (hU : U ∈ 𝓝 x₀) (hL : ∀ k, LipschitzOnWith L (φ k) U)
    (hΩ : ∃ ρ > 0, IsClosed (Ω ∩ closedBall x₀ ρ)) :
    ∃ lam : K → ℝ, lam ≠ 0 ∧ (∀ k, 0 ≤ lam k) ∧ (∀ k, k ≠ k₀ → k ∉ Q → lam k * φ k x₀ = 0) ∧
      (0 : StrongDual ℝ E) ∈ ∑ k, lam k • separateSubdiff φ Q x₀ k + normalCone Ω x₀ := by
  obtain ⟨mu, hne, hnn, hcs, -, h0⟩ :=
    exists_multipliers_zero_mem_subdiff_lagrangian_add_normalCone hk₀ hx hmin hU hL hΩ
  refine ⟨fun k ↦ |mu k|, fun h ↦ hne (funext fun k ↦ abs_eq_zero.1 (congrFun h k)),
    fun k ↦ abs_nonneg _, fun k hk hkQ ↦ by
      show |mu k| * φ k x₀ = 0
      rw [abs_of_nonneg (hnn k hkQ)]; exact hcs k hk hkQ, ?_⟩
  -- the sum rule for the Lagrangian
  have hsum : subdiff (fun x ↦ (lagrangian φ mu x : EReal)) x₀ ⊆
      ∑ k, subdiff (fun x ↦ ((mu k * φ k x : ℝ) : EReal)) x₀ := by
    have hfun : (fun x ↦ (lagrangian φ mu x : EReal)) =
        fun x ↦ ∑ k, ((mu k * φ k x : ℝ) : EReal) := funext fun x ↦ coe_sum_ereal _
    rw [hfun]
    refine subdiff_sum_subset (r := fun k ↦ mu k * φ k x₀) (fun k ↦ rfl)
      (fun k ↦ locallyClosed_epi_of_continuousOn hU
        (lipschitzOnWith_const_mul (hL k) (mu k)).continuousOn _) fun v hv _ k ↦ ?_
    have := hv k
    rwa [singularSubdiff_eq_zero_of_lipschitz hU (lipschitzOnWith_const_mul (hL k) (mu k)),
      mem_singleton_iff] at this
  have hterm : ∀ k, subdiff (fun x ↦ ((mu k * φ k x : ℝ) : EReal)) x₀ ⊆
      |mu k| • separateSubdiff φ Q x₀ k := by
    intro k
    by_cases hkQ : k ∈ Q
    · refine (subdiff_const_mul_subset hU (hL k) (mu k)).1.trans (Set.smul_set_mono ?_)
      rintro v (hv | hv)
      · exact Or.inl hv
      · exact Or.inr ⟨hkQ, hv⟩
    · rw [abs_of_nonneg (hnn k hkQ)]
      exact ((subdiff_const_mul_subset hU (hL k) (mu k)).2 (hnn k hkQ)).trans
        (Set.smul_set_mono fun v hv ↦ Or.inl hv)
  exact Set.add_subset_add_right ((hsum.trans (sum_subset_sum hterm))) h0

variable (φ Q x₀) in
/-- The sets `∂φₖ(x₀)` for `k ∉ Q` and the symmetric subdifferentials `∂⁰φₖ(x₀)` for `k ∈ Q` in
(6.19). -/
def symmSeparateSubdiff (k : K) : Set (StrongDual ℝ E) :=
  {v | v ∈ subdiff (fun x ↦ (φ k x : EReal)) x₀ ∨
    (k ∈ Q ∧ v ∈ upperSubdiff (fun x ↦ (φ k x : EReal)) x₀)}

omit [Fintype K] [DecidableEq K] [FiniteDimensional ℝ E] in
theorem symmSeparateSubdiff_of_mem {k : K} (hk : k ∈ Q) :
    symmSeparateSubdiff φ Q x₀ k = symmSubdiff (fun x ↦ (φ k x : EReal)) x₀ := by
  ext v; simp [symmSeparateSubdiff, symmSubdiff, hk]

/-- Cor. 6.6 of [Mordukhovich 2018] (equality constraints via symmetric subgradients), (6.19):
under the assumptions of Thm. 6.5(ii) there are multipliers `λ ≠ 0` with `λₖ ≥ 0` for `k ∉ Q`,
the complementary slackness conditions, and
`0 ∈ ∑_{k ∉ Q} λₖ ∂φₖ(x₀) + ∑_{k ∈ Q} λₖ ∂⁰φₖ(x₀) + N(x₀; Ω)`. -/
theorem exists_multipliers_zero_mem_sum_symmSeparateSubdiff (hk₀ : k₀ ∉ Q)
    (hx : x₀ ∈ feasibleSet Q k₀ Ω φ) (hmin : IsLocalMinOn (φ k₀) (feasibleSet Q k₀ Ω φ) x₀)
    {U : Set E} {L : ℝ≥0} (hU : U ∈ 𝓝 x₀) (hL : ∀ k, LipschitzOnWith L (φ k) U)
    (hΩ : ∃ ρ > 0, IsClosed (Ω ∩ closedBall x₀ ρ)) :
    ∃ mu : K → ℝ, mu ≠ 0 ∧ (∀ k ∉ Q, 0 ≤ mu k) ∧ (∀ k, k ≠ k₀ → k ∉ Q → mu k * φ k x₀ = 0) ∧
      (0 : StrongDual ℝ E) ∈ ∑ k, mu k • symmSeparateSubdiff φ Q x₀ k + normalCone Ω x₀ := by
  classical
  obtain ⟨lam, hne, hnn, hcs, a, ha, n, hn, han⟩ :=
    exists_multipliers_zero_mem_sum_separateSubdiff hk₀ hx hmin hU hL hΩ
  obtain ⟨g, hg, rfl⟩ := (Set.mem_fintype_sum _ _).1 ha
  choose w hw hgw using fun k ↦ Set.mem_smul_set.1 (hg k)
  set P : K → Prop := fun k ↦ w k ∈ subdiff (fun x ↦ (φ k x : EReal)) x₀
  have hQ : ∀ k, ¬ P k → k ∈ Q ∧ w k ∈ subdiff (fun x ↦ ((-φ k x : ℝ) : EReal)) x₀ := fun k hk ↦
    (hw k).resolve_left hk
  have hPQ : ∀ k ∉ Q, P k := fun k hk ↦ by_contra fun h ↦ hk (hQ k h).1
  refine ⟨fun k ↦ if P k then lam k else -lam k, fun h ↦ hne (funext fun k ↦ ?_),
    fun k hk ↦ by simp [hPQ k hk, hnn k], fun k hk hkQ ↦ by simp [hPQ k hkQ, hcs k hk hkQ],
    ∑ k, g k, (Set.mem_fintype_sum _ _).2 ⟨g, fun k ↦ ?_, rfl⟩, n, hn, han⟩
  · have := congrFun h k
    by_cases hk : P k <;> simp_all
  · refine ⟨if P k then w k else -w k, ?_, ?_⟩
    · by_cases hk : P k
      · simp only [hk, if_true]; exact Or.inl hk
      · simp only [hk, if_false]
        refine Or.inr ⟨(hQ k hk).1, mem_upperSubdiff_iff.2 ?_⟩
        have h := (hQ k hk).2
        rw [neg_neg]
        convert h using 2
        simp
    · by_cases hk : P k
      · simp only [hk, if_true]; exact hgw k
      · simp only [hk, if_false, neg_smul_neg]; exact hgw k

/-- Cor. 6.11 of [Mordukhovich 2018] (abstract maximum principle in nondifferentiable
programming): if moreover `Ω` is convex, there are multipliers `λ ≠ 0` as in Thm. 6.10 and
`v ∈ -∂_x 𝓛(x₀, λ)` with `⟨v, x₀⟩ = max_{x ∈ Ω} ⟨v, x⟩`. -/
theorem exists_multipliers_abstract_maximum_principle (hk₀ : k₀ ∉ Q) (hΩc : Convex ℝ Ω)
    (hx : x₀ ∈ feasibleSet Q k₀ Ω φ) (hmin : IsLocalMinOn (φ k₀) (feasibleSet Q k₀ Ω φ) x₀)
    {U : Set E} {L : ℝ≥0} (hU : U ∈ 𝓝 x₀) (hL : ∀ k, LipschitzOnWith L (φ k) U)
    (hΩ : ∃ ρ > 0, IsClosed (Ω ∩ closedBall x₀ ρ)) :
    ∃ lam : K → ℝ, lam ≠ 0 ∧ (∀ k ∉ Q, 0 ≤ lam k) ∧
      (∀ k, k ≠ k₀ → k ∉ Q → lam k * φ k x₀ = 0) ∧
      ∃ v ∈ -subdiff (fun x ↦ (lagrangian φ lam x : EReal)) x₀, ∀ x ∈ Ω, v x ≤ v x₀ := by
  obtain ⟨lam, hne, hnn, hcs, -, w, hw, n, hn, hwn⟩ :=
    exists_multipliers_zero_mem_subdiff_lagrangian_add_normalCone hk₀ hx hmin hU hL hΩ
  have hnw : n = -w := eq_neg_of_add_eq_zero_right hwn
  refine ⟨lam, hne, hnn, hcs, n, by rw [hnw, Set.neg_mem_neg]; exact hw, fun x hxΩ ↦ ?_⟩
  have := (mem_normalCone_of_convex hΩc hx.1).1 hn x hxΩ
  rw [map_sub] at this
  linarith

end Separate

section Upper

/-! ### Upper subdifferential conditions -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [Fintype K] [DecidableEq K] in
/-- Localized Thm. 1.27(ii) of [Mordukhovich 2018] for upper regular subgradients: for
`v ∈ ∂̂⁺f(x₀)` there is a `C¹` function `ψ ≥ f` near `x₀` with `ψ(x₀) = f(x₀)` and
`∇ψ(x₀) = v`. -/
theorem exists_contDiff_upper_support {f : H → ℝ} {x₀ : H} {v : StrongDual ℝ H}
    (hv : v ∈ upperRegularSubdiff (fun x ↦ (f x : EReal)) x₀) :
    ∃ ψ : H → ℝ, ContDiff ℝ 1 ψ ∧ HasFDerivAt ψ v x₀ ∧ ψ x₀ = f x₀ ∧
      ∀ᶠ x in 𝓝 x₀, f x ≤ ψ x := by
  classical
  have hv' : -v ∈ regularSubdiff (fun x ↦ ((-f x : ℝ) : EReal)) x₀ := by
    have := mem_upperRegularSubdiff_iff.1 hv
    convert this using 2
    funext x; simp
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (mem_regularSubdiff_coe.1 hv' 1 one_pos)
  set G : H → EReal := fun x ↦ if dist x x₀ < δ then ((-f x : ℝ) : EReal) else ⊤
  have hGx : G x₀ = ((-f x₀ : ℝ) : EReal) := by simp [G, hδ]
  have hGeq : G =ᶠ[𝓝 x₀] fun x ↦ ((-f x : ℝ) : EReal) := by
    filter_upwards [Metric.ball_mem_nhds x₀ hδ] with x hx
    simp [G, mem_ball.1 hx]
  have hbdd : ∃ m : ℝ, ∀ x, (m : EReal) ≤ G x := by
    refine ⟨-f x₀ - (‖v‖ + 1) * δ, fun x ↦ ?_⟩
    simp only [G]
    split_ifs with hx
    · rw [EReal.coe_le_coe_iff]
      have h1 := hball hx
      simp only [neg_apply, one_mul] at h1
      have h2 := (v.le_opNorm (x - x₀))
      rw [Real.norm_eq_abs, abs_le] at h2
      have h3 : ‖x - x₀‖ ≤ δ := by rw [← dist_eq_norm]; exact hx.le
      nlinarith [norm_nonneg v, norm_nonneg (x - x₀), mul_le_mul_of_nonneg_left h3 (norm_nonneg v)]
    · exact le_top
  rw [← regularSubdiff_congr hGeq] at hv'
  obtain ⟨ψ, hψc, -, hψd, hψ0, hψlt⟩ := exists_concave_support_of_mem_regularSubdiff hGx hbdd hv'
  refine ⟨fun x ↦ -ψ x, hψc.neg, HasFDerivAt.congr_fderiv hψd.neg (neg_neg v), by simp [hψ0], ?_⟩
  filter_upwards [Metric.ball_mem_nhds x₀ hδ] with x hx
  by_cases hxx : x = x₀
  · subst hxx; simp [hψ0]
  · have := hψlt x hxx
    simp only [G, mem_ball.1 hx, if_true, EReal.coe_lt_coe_iff] at this
    linarith

variable [FiniteDimensional ℝ H] {φ : K → H → ℝ} {Q : Set K} [DecidablePred (· ∈ Q)] {k₀ : K}
  {Ω : Set H} {x₀ : H}

/-- Thm. 6.12 of [Mordukhovich 2018] (upper subdifferential optimality conditions in
nondifferentiable programming), (6.26): let `x₀` be a local minimizer of `φ_{k₀}` over the
feasible set of (6.11), with the equality data `φₖ`, `k ∈ Q`, Lipschitz around `x₀` and `Ω`
locally closed around `x₀`. Then for any `vₖ ∈ ∂̂⁺φₖ(x₀)`, `k ∉ Q`, there are multipliers `λ ≠ 0`
with `λₖ ≥ 0` for `k ∉ Q`, the complementary slackness conditions, and
`-∑_{k ∉ Q} λₖ vₖ ∈ ∂(∑_{k ∈ Q} λₖ φₖ)(x₀) + N(x₀; Ω)`. -/
theorem exists_multipliers_upperRegularSubdiff (hk₀ : k₀ ∉ Q)
    (hx : x₀ ∈ feasibleSet Q k₀ Ω φ) (hmin : IsLocalMinOn (φ k₀) (feasibleSet Q k₀ Ω φ) x₀)
    {U : Set H} {L : ℝ≥0} (hU : U ∈ 𝓝 x₀) (hL : ∀ k ∈ Q, LipschitzOnWith L (φ k) U)
    (hΩ : ∃ ρ > 0, IsClosed (Ω ∩ closedBall x₀ ρ)) (v : K → StrongDual ℝ H)
    (hv : ∀ k ∉ Q, v k ∈ upperRegularSubdiff (fun x ↦ (φ k x : EReal)) x₀) :
    ∃ lam : K → ℝ, lam ≠ 0 ∧ (∀ k ∉ Q, 0 ≤ lam k) ∧
      (∀ k, k ≠ k₀ → k ∉ Q → lam k * φ k x₀ = 0) ∧
      -(∑ k ∈ Finset.univ.filter (· ∉ Q), lam k • v k) ∈
        subdiff (fun x ↦ ((∑ k ∈ Finset.univ.filter (· ∈ Q), lam k * φ k x : ℝ) : EReal)) x₀ +
          normalCone Ω x₀ := by
  -- `C¹` upper supports `ψₖ` of the cost and inequality data
  have hex : ∀ k, ∃ ψ : H → ℝ, (k ∈ Q → ψ = φ k) ∧ (k ∉ Q → ContDiff ℝ 1 ψ ∧
      HasFDerivAt ψ (v k) x₀ ∧ ψ x₀ = φ k x₀ ∧ ∀ᶠ x in 𝓝 x₀, φ k x ≤ ψ x) := by
    intro k
    by_cases hk : k ∈ Q
    · exact ⟨φ k, fun _ ↦ rfl, fun h ↦ absurd hk h⟩
    · obtain ⟨ψ, h⟩ := exists_contDiff_upper_support (hv k hk)
      exact ⟨ψ, fun h' ↦ absurd h' hk, fun _ ↦ h⟩
  choose ψ hψQ hψ using hex
  have hψx₀ : ∀ k, ψ k x₀ = φ k x₀ := fun k ↦ by
    by_cases hk : k ∈ Q
    · rw [hψQ k hk]
    · exact (hψ k hk).2.2.1
  have hle : ∀ᶠ x in 𝓝 x₀, ∀ k, φ k x ≤ ψ k x := by
    rw [Filter.eventually_all]
    intro k
    by_cases hk : k ∈ Q
    · exact Eventually.of_forall fun x ↦ by rw [hψQ k hk]
    · exact (hψ k hk).2.2.2
  -- a common Lipschitz neighborhood for all `ψₖ`
  have hlip : ∀ k, ∃ M : ℝ≥0, ∃ t ∈ 𝓝 x₀, LipschitzOnWith M (ψ k) t := fun k ↦ by
    by_cases hk : k ∈ Q
    · exact ⟨L, U, hU, by rw [hψQ k hk]; exact hL k hk⟩
    · exact (hψ k hk).1.contDiffAt.exists_lipschitzOnWith
  choose M t ht hMt using hlip
  have hU' : (⋂ k, t k) ∈ 𝓝 x₀ := Filter.iInter_mem.2 ht
  have hL' : ∀ k, LipschitzOnWith (∑ j, M j) (ψ k) (⋂ k, t k) := fun k ↦
    ((hMt k).mono (iInter_subset _ k)).weaken
      (Finset.single_le_sum (fun j _ ↦ zero_le) (Finset.mem_univ k))
  -- `x₀` solves the problem with the data `ψ`
  have hxψ : x₀ ∈ feasibleSet Q k₀ Ω ψ :=
    ⟨hx.1, fun k hk hkQ ↦ by rw [hψx₀]; exact hx.2.1 k hk hkQ,
      fun k hk ↦ by rw [hψx₀]; exact hx.2.2 k hk⟩
  have hminψ : IsLocalMinOn (ψ k₀) (feasibleSet Q k₀ Ω ψ) x₀ := by
    refine eventually_nhdsWithin_iff.2 ?_
    filter_upwards [eventually_nhdsWithin_iff.1 hmin, hle] with x h1 h2 hxf
    have hfeas : x ∈ feasibleSet Q k₀ Ω φ :=
      ⟨hxf.1, fun k hk hkQ ↦ (h2 k).trans (hxf.2.1 k hk hkQ),
        fun k hk ↦ by rw [← hxf.2.2 k hk, hψQ k hk]⟩
    rw [hψx₀]
    exact (h1 hfeas).trans (h2 k₀)
  obtain ⟨lam, hne, hnn, hcs, -, a, ha, n, hn, han⟩ :=
    exists_multipliers_zero_mem_subdiff_lagrangian_add_normalCone hk₀ hxψ hminψ hU' hL' hΩ
  refine ⟨lam, hne, hnn, fun k hk hkQ ↦ by rw [← hψx₀]; exact hcs k hk hkQ, ?_⟩
  -- split the Lagrangian into its smooth part `g` and its Lipschitz part `h`
  set S := Finset.univ.filter (· ∉ Q)
  set g : H → ℝ := fun x ↦ ∑ k ∈ S, lam k * ψ k x
  set h : H → ℝ := fun x ↦ ∑ k ∈ Finset.univ.filter (· ∈ Q), lam k * φ k x
  have hsplit : (fun x ↦ (lagrangian ψ lam x : EReal)) =
      fun x ↦ (h x : EReal) + (g x : EReal) := by
    funext x
    rw [← EReal.coe_add]
    congr 1
    simp only [lagrangian, g, h, S]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ Q)]
    congr 1
    exact Finset.sum_congr rfl fun k hk ↦ by rw [hψQ k (Finset.mem_filter.1 hk).2]
  set g' : H → StrongDual ℝ H := fun x ↦ ∑ k ∈ S, lam k • fderiv ℝ (ψ k) x
  have hg : ∀ᶠ x in 𝓝 x₀, HasFDerivAt g (g' x) x := Eventually.of_forall fun x ↦ by
    refine HasFDerivAt.fun_sum fun k hk ↦ ?_
    exact (((hψ k (Finset.mem_filter.1 hk).2).1.differentiable one_ne_zero x).hasFDerivAt).const_mul
      (lam k)
  have hgc : ContinuousAt g' x₀ :=
    (continuous_finsetSum _ fun k hk ↦
      ((hψ k (Finset.mem_filter.1 hk).2).1.continuous_fderiv one_ne_zero).const_smul
        (lam k)).continuousAt
  have hg'x : g' x₀ = ∑ k ∈ S, lam k • v k :=
    Finset.sum_congr rfl fun k hk ↦ by rw [(hψ k (Finset.mem_filter.1 hk).2).2.1.fderiv]
  rw [hsplit, mem_subdiff_add_iff hg hgc, hg'x] at ha
  refine ⟨a - ∑ k ∈ S, lam k • v k, ha, n, hn, ?_⟩
  rw [eq_neg_of_add_eq_zero_right han]
  simp only [S]
  abel

end Upper

section FritzJohn

/-! ### Normals to epigraphs and graphs of the separate data -/

variable (K) in
/-- The projection `(x, α) ↦ (x, αₖ)` of `E × ℝ^K` onto `E × ℝ`. -/
def coordProj (k : K) : (E × (K → ℝ)) →L[ℝ] E × ℝ :=
  (ContinuousLinearMap.fst ℝ E (K → ℝ)).prod
    ((ContinuousLinearMap.proj k).comp (ContinuousLinearMap.snd ℝ E (K → ℝ)))

omit [Fintype K] [DecidableEq K] in
@[simp] theorem coordProj_apply (k : K) (p : E × (K → ℝ)) : coordProj K k p = (p.1, p.2 k) := rfl

omit [Fintype K] in
theorem coordProj_surjective (k : K) : Function.Surjective (coordProj (E := E) K k) :=
  fun q ↦ ⟨(q.1, Pi.single k q.2), by simp⟩

omit [Fintype K] [DecidableEq K] in
/-- Preimages of locally closed sets under continuous linear maps are locally closed. -/
theorem locallyClosed_preimage_continuousLinearMap {F G : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] (P : F →L[ℝ] G) {S : Set G}
    {z : F} (h : ∃ ρ > 0, IsClosed (S ∩ closedBall (P z) ρ)) :
    ∃ ρ > 0, IsClosed (P ⁻¹' S ∩ closedBall z ρ) := by
  obtain ⟨ρ, hρ, hc⟩ := h
  refine ⟨ρ / (‖P‖ + 1), by positivity, ?_⟩
  have : P ⁻¹' S ∩ closedBall z (ρ / (‖P‖ + 1)) =
      P ⁻¹' (S ∩ closedBall (P z) ρ) ∩ closedBall z (ρ / (‖P‖ + 1)) := by
    ext y
    simp only [mem_inter_iff, mem_preimage, mem_closedBall]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, ?_⟩, h2⟩
      rw [dist_eq_norm, ← map_sub]
      rw [dist_eq_norm] at h2
      calc ‖P (y - z)‖ ≤ ‖P‖ * ‖y - z‖ := P.le_opNorm _
        _ ≤ ‖P‖ * (ρ / (‖P‖ + 1)) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ ≤ ρ := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith [norm_nonneg P]
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
  rw [this]
  exact (hc.preimage P.continuous).inter isClosed_closedBall

omit [NormedSpace ℝ E] [Fintype K] [DecidableEq K] in
/-- The graph `{(x, α) | f x = α}` of a function continuous around `x₀` is locally closed. -/
theorem locallyClosed_ereal_graph_of_continuousOn {f : E → EReal} {U : Set E} {x₀ : E}
    (hU : U ∈ 𝓝 x₀) (hf : ContinuousOn f U) (a : ℝ) :
    ∃ ρ > 0, IsClosed ({p : E × ℝ | f p.1 = p.2} ∩ closedBall (x₀, a) ρ) := by
  obtain ⟨ρ, hρ, hsub⟩ := nhds_basis_closedBall.mem_iff.1 hU
  refine ⟨ρ, hρ, ?_⟩
  have hmaps : MapsTo Prod.fst (closedBall ((x₀, a) : E × ℝ) ρ) U := fun p hp ↦ hsub (by
    rw [mem_closedBall] at hp ⊢
    exact (by rw [Prod.dist_eq]; exact le_max_left _ _ : dist p.1 x₀ ≤ dist p (x₀, a)).trans hp)
  have hcont : ContinuousOn (fun p : E × ℝ ↦ (f p.1, (p.2 : EReal)))
      (closedBall ((x₀, a) : E × ℝ) ρ) :=
    (hf.comp continuous_fst.continuousOn hmaps).prodMk
      (continuous_coe_real_ereal.comp continuous_snd).continuousOn
  have := hcont.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_diagonal
  convert this using 1
  ext p
  simp [and_comm]

variable [FiniteDimensional ℝ E] {Q : Set K} {k₀ : K} {Ω : Set E} {x₀ : E}

/-- Thm. 6.5(i) of [Mordukhovich 2018] (lower subdifferential conditions via normals to the
separate constraints), (6.12)–(6.16): let `x₀` be a local minimizer of `φ_{k₀}` over the feasible
set of (6.11), where `φₖ : E → EReal`, `φ_{k₀}(x₀) = c` is finite, the cost and inequality data
are l.s.c. around `x₀`, the equality data are continuous around `x₀`, and `Ω` is locally closed
around `x₀`. Then there are `mₖ = (vₖ, -λₖ) ∈ (E × ℝ)*`, not all zero, and `v ∈ N(x₀; Ω)` with
`m_{k₀} ∈ N((x₀, c); epi φ_{k₀})`, `mₖ ∈ N((x₀, 0); epi φₖ)` for the inequality indices,
`mₖ ∈ N((x₀, 0); gph φₖ)` for `k ∈ Q`, `λₖ ≥ 0` for `k ∉ Q`, and `v + ∑ₖ vₖ = 0`. Moreover
`mₖ = 0` for every inequality index with `φₖ` u.s.c. at `x₀` and `φₖ(x₀) < 0`, which gives the
complementary slackness conditions (6.16). -/
theorem exists_mem_normalCone_epi_graph (hk₀ : k₀ ∉ Q) {φ : K → E → EReal} {c : ℝ}
    (hc : φ k₀ x₀ = c) (hx : x₀ ∈ feasibleSet Q k₀ Ω φ)
    (hmin : IsLocalMinOn (φ k₀) (feasibleSet Q k₀ Ω φ) x₀)
    (hΩ : ∃ ρ > 0, IsClosed (Ω ∩ closedBall x₀ ρ))
    (hlsc : ∀ k ∉ Q, ∃ U ∈ 𝓝 x₀, LowerSemicontinuousOn (φ k) U)
    (hcont : ∀ k ∈ Q, ∃ U ∈ 𝓝 x₀, ContinuousOn (φ k) U) :
    ∃ m : K → StrongDual ℝ (E × ℝ), m ≠ 0 ∧ ∃ v ∈ normalCone Ω x₀,
      m k₀ ∈ normalCone ((φ k₀).Epi univ) (x₀, c) ∧
      (∀ k, k ≠ k₀ → k ∉ Q → m k ∈ normalCone ((φ k).Epi univ) (x₀, 0)) ∧
      (∀ k ∈ Q, m k ∈ normalCone {p : E × ℝ | φ k p.1 = p.2} (x₀, 0)) ∧
      (∀ k ∉ Q, m k (0, 1) ≤ 0) ∧
      v + ∑ k, (m k).comp (ContinuousLinearMap.inl ℝ E ℝ) = 0 ∧
      (∀ k, k ≠ k₀ → k ∉ Q → UpperSemicontinuousAt (φ k) x₀ → φ k x₀ < 0 → m k = 0) := by
  classical
  set αb : K → ℝ := Pi.single k₀ c
  set zb : E × (K → ℝ) := (x₀, αb)
  have hαb : ∀ k, k ≠ k₀ → αb k = 0 := fun k hk ↦ by simp [αb, hk]
  have hαb₀ : αb k₀ = c := by simp [αb]
  set S : K → Set (E × ℝ) := fun k ↦ {p | φ k p.1 ≤ p.2 ∧ (k ∈ Q → φ k p.1 = p.2)}
  have hSepi : ∀ k ∉ Q, S k = (φ k).Epi univ := fun k hk ↦ by
    ext p; simp [S, Function.Epi, hk]
  have hSgr : ∀ k ∈ Q, S k = {p : E × ℝ | φ k p.1 = p.2} := fun k hk ↦ by
    ext p
    simp only [S, mem_ofPred_eq, hk, forall_const]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.le, h⟩⟩
  have hzS : ∀ k, ((x₀, αb k) : E × ℝ) ∈ S k := by
    intro k
    by_cases hkk : k = k₀
    · subst hkk
      exact ⟨by rw [hαb₀, hc], fun h ↦ absurd h hk₀⟩
    · rw [hαb k hkk]
      by_cases hkQ : k ∈ Q
      · have := hx.2.2 k hkQ
        exact ⟨by simp [this], fun _ ↦ by simp [this]⟩
      · exact ⟨by simpa using hx.2.1 k hkk hkQ, fun h ↦ absurd h hkQ⟩
  set Ωs : Option K → Set (E × (K → ℝ)) :=
    fun i ↦ i.elim (Ω ×ˢ {αb}) (fun k ↦ coordProj K k ⁻¹' S k)
  -- a radius on which `x₀` minimizes `φ_{k₀}` over the feasible set
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hmin)
  set d : E × (K → ℝ) := ((0 : E), -(Pi.single k₀ (1 : ℝ) : K → ℝ))
  set t : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have ht : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have htpos : ∀ n, 0 < t n := fun n ↦ by positivity
  have hext : IsLocallyExtremal Ωs zb := by
    rw [isLocallyExtremal_iff]
    refine ⟨fun i ↦ ?_, fun i n ↦ if i = some k₀ then t n • d else 0, fun i ↦ ?_,
      ball x₀ δ ×ˢ univ, prod_mem_nhds (ball_mem_nhds x₀ hδ) univ_mem,
      Eventually.of_forall fun n z hz ↦ ?_⟩
    · cases i with
      | none => exact ⟨hx.1, rfl⟩
      | some k => exact hzS k
    · by_cases hi : i = some k₀
      · simpa [hi] using ht.smul_const d
      · simp [hi]
    · by_contra hcon
      push Not at hcon
      obtain ⟨x, β⟩ := z
      have hn := hcon none
      simp only [Ωs, Option.elim, reduceCtorEq, if_false, add_zero, mem_prod,
        mem_singleton_iff] at hn
      obtain ⟨hxΩ, rfl⟩ := hn
      have hk : ∀ k, ((x, αb k - if k = k₀ then t n else 0) : E × ℝ) ∈ S k := by
        intro k
        have := hcon (some k)
        simp only [Ωs, Option.elim, Option.some.injEq, mem_preimage, coordProj_apply] at this
        by_cases hkk : k = k₀
        · subst hkk
          simpa [d, sub_eq_add_neg] using this
        · simpa [hkk, d, Pi.single_eq_of_ne hkk] using this
      have hfeas : x ∈ feasibleSet Q k₀ Ω φ := by
        refine ⟨hxΩ, fun k hk' hkQ ↦ ?_, fun k hkQ ↦ ?_⟩
        · simpa [hαb k hk', hk'] using (hk k).1
        · have hkk : k ≠ k₀ := fun h ↦ hk₀ (h ▸ hkQ)
          simpa [hαb k hkk, hkk] using (hk k).2 hkQ
      have hmin' := hball (by simpa [dist_eq_norm] using hz.1) hfeas
      have hk₀' := (hk k₀).1
      simp only [hαb₀, if_true] at hk₀'
      rw [hc] at hmin'
      have := hmin'.trans hk₀'
      rw [EReal.coe_le_coe_iff] at this
      linarith [htpos n]
  have hloc : ∀ i, ∃ r > 0, IsClosed (Ωs i ∩ closedBall zb r) := by
    intro i
    cases i with
    | none => exact locallyClosed_prod hΩ ⟨1, one_pos, isClosed_singleton.inter isClosed_closedBall⟩
    | some k =>
      refine locallyClosed_preimage_continuousLinearMap (F := E × (K → ℝ)) (G := E × ℝ)
        (coordProj (E := E) K k) ?_
      show ∃ ρ > 0, IsClosed (S k ∩ closedBall (x₀, αb k) ρ)
      by_cases hkQ : k ∈ Q
      · obtain ⟨U, hU, hf⟩ := hcont k hkQ
        rw [hSgr k hkQ]
        exact locallyClosed_ereal_graph_of_continuousOn hU hf _
      · obtain ⟨U, hU, hf⟩ := hlsc k hkQ
        rw [hSepi k hkQ]
        exact locallyClosed_epi_of_lowerSemicontinuousOn hU hf _
  obtain ⟨ℓ, hℓ, hsum, hnorm⟩ := hext.exists_mem_normalCone hloc
  -- normals to the inverse images `Pₖ⁻¹(Sₖ)`
  have hpre : ∀ k, ∃ m ∈ normalCone (S k) (x₀, αb k), ℓ (some k) = m.comp (coordProj K k) := by
    intro k
    have := hℓ (some k)
    simp only [Ωs, Option.elim] at this
    rw [normalCone_preimage_of_surjective_of_finiteDimensional (D := fun _ ↦ coordProj K k)
      (Eventually.of_forall fun _ ↦ (coordProj (E := E) K k).hasStrictFDerivAt) continuousAt_const
      (coordProj_surjective k)] at this
    obtain ⟨m, hm, hmeq⟩ := this
    exact ⟨m, hm, hmeq.symm⟩
  choose m hm hmeq using hpre
  have hnone : ℓ none ∈ normalCone (Ω ×ˢ {αb}) (x₀, αb) := hℓ none
  set v := (ℓ none).comp (ContinuousLinearMap.inl ℝ E (K → ℝ))
  have hv : v ∈ normalCone Ω x₀ := (mem_normalCone_prod_iff.1 hnone).1
  rw [Fintype.sum_option] at hsum hnorm
  have hsum' : v + ∑ k, (m k).comp (ContinuousLinearMap.inl ℝ E ℝ) = 0 := by
    ext x
    have := congrArg (fun f : StrongDual ℝ (E × (K → ℝ)) ↦ f (x, 0)) hsum
    simpa [v, hmeq] using this
  have hm0 : m ≠ 0 := by
    intro h0
    have hk : ∀ k, ℓ (some k) = 0 := fun k ↦ by rw [hmeq k, congrFun h0 k]; rfl
    have hn : ℓ none = 0 := by simpa [hk] using hsum
    simp [hk, hn] at hnorm
  refine ⟨m, hm0, v, hv, ?_, fun k hk hkQ ↦ ?_, fun k hkQ ↦ ?_, fun k hkQ ↦ ?_, hsum',
    fun k hk hkQ husc hlt ↦ ?_⟩
  · have := hm k₀
    rwa [hSepi k₀ hk₀, hαb₀] at this
  · have := hm k
    rwa [hSepi k hkQ, hαb k hk] at this
  · have hkk : k ≠ k₀ := fun h ↦ hk₀ (h ▸ hkQ)
    have := hm k
    rwa [hSgr k hkQ, hαb k hkk] at this
  · have := hm k
    rw [hSepi k hkQ] at this
    exact apply_zero_one_nonpos_of_mem_normalCone_epi this
  · -- `(x₀, 0)` is an interior point of `epi φₖ`
    obtain ⟨a, ha₁, ha₂⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
    rw [← EReal.coe_zero, EReal.coe_lt_coe_iff] at ha₂
    have hint : ((x₀, (0 : ℝ)) : E × ℝ) ∈ interior ((φ k).Epi univ) := by
      rw [mem_interior_iff_mem_nhds]
      filter_upwards [prod_mem_nhds (husc a ha₁) (Ioi_mem_nhds ha₂)] with p hp
      exact ⟨mem_univ _, (le_of_lt hp.1).trans (EReal.coe_le_coe_iff.2 (le_of_lt hp.2))⟩
    have := hm k
    rw [hSepi k hkQ, hαb k hk, normalCone_of_mem_interior hint] at this
    exact this

end FritzJohn

end VariationalAnalysis
