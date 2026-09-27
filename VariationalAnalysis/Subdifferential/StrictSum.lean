/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import VariationalAnalysis.Subdifferential.Coderivative

/-!
# Sum rule with a strictly differentiable function; compositions `φ(x, g x)`

The basic subdifferential sum rule with a strictly differentiable addition,
`∂(g + r)(x₀) = ∂g(x₀) + ∇r(x₀)` for `g` continuous around `x₀` and `r` strictly differentiable
at `x₀` ([Mordukhovich 2006, Prop. 1.107(ii)]). It extends the `C¹` sum rule of
[Mordukhovich 2018, Prop. 1.30(ii)] (`mem_subdiff_add_iff`) to additions that are strictly
differentiable at `x₀` but need not be differentiable near it. The proof uses the representation
of `∂` through `ω`-subgradients ([Mordukhovich 2018, Thm. 1.28, (1.37)]), as does the book's
proof of Thm. 4.5(ii).

With it we prove [Mordukhovich 2018, Thm. 4.5(ii)]: for `φ : E × F → ℝ` strictly
differentiable at `(x₀, ȳ)` and `g` Lipschitz around `x₀` with `ȳ = g x₀`,

  `∂(φ ∘ (I, g))(x₀) = ∇ₓφ(x₀, ȳ) + ∂⟨∇ᵧφ(x₀, ȳ), g⟩(x₀) = ∇ₓφ(x₀, ȳ) + D*g(x₀)(∇ᵧφ(x₀, ȳ))`,

the second form by the coderivative scalarization [Mordukhovich 2018, Thm. 1.32].

## Main results

* `mem_subdiff_add_strict_iff`: sum rule with a strictly differentiable addition
  ([Mordukhovich 2006, Prop. 1.107(ii)]), finite dimensions.
* `hasStrictFDerivAt_comp_sub_comp_inr`: `x ↦ φ(x, g x) - ⟨∇ᵧφ(x₀, g x₀), g x⟩` is strictly
  differentiable at `x₀` with derivative `∇ₓφ(x₀, g x₀)`.
* `mem_subdiff_comp_strict_iff`, `subdiff_comp_strict_eq`: Thm. 4.5(ii), (4.12), of
  [Mordukhovich 2018].
* `subdiff_comp_strict_eq_coderiv`: (4.12) combined with Thm. 1.32 of [Mordukhovich 2018].
-/

open Set Filter Topology Metric Asymptotics
open scoped NNReal

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section StrictSum

/-- A strict derivative gives a uniform first-order bound on a ball around the point
([Mordukhovich 2018, (1.19)]). -/
theorem exists_ball_strict_bound {r : E → ℝ} {r' : StrongDual ℝ E} {x₀ : E}
    (hr : HasStrictFDerivAt r r' x₀) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ x ∈ ball x₀ δ, ∀ x' ∈ ball x₀ δ, |r x - r x' - r' (x - x')| ≤ η * ‖x - x'‖ := by
  have h := (hasStrictFDerivAt_iff_isLittleO.1 hr).def hη
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 h
  refine ⟨δ, hδ, fun x hx x' hx' ↦ ?_⟩
  have hmem : (x, x') ∈ ball (x₀, x₀) δ := by rw [← ball_prod_same]; exact ⟨hx, hx'⟩
  simpa [Real.norm_eq_abs] using hball _ hmem

/-- `ω`-subgradients of `g + r` give `(ω + η)`-subgradients of `g` where `r` is `η`-close to its
linearization; the estimate in the proof of [Mordukhovich 2018, Thm. 4.5(ii)]. -/
theorem sub_mem_epsSubdiff_of_add {g r : E → ℝ} {r' : StrongDual ℝ E} {x₀ : E}
    {w : StrongDual ℝ E} {ω η : ℝ} {V : Set E} (hV : IsOpen V) (hx₀ : x₀ ∈ V)
    (hstrict : ∀ x ∈ V, ∀ x' ∈ V, |r x - r x' - r' (x - x')| ≤ η * ‖x - x'‖)
    (hw : w ∈ epsSubdiff ω (fun x ↦ ((g x + r x : ℝ) : EReal)) x₀) :
    w - r' ∈ epsSubdiff (ω + η) (fun x ↦ ((g x : ℝ) : EReal)) x₀ := by
  rw [mem_epsSubdiff_iff (φ := fun x ↦ ((g x + r x : ℝ) : EReal)) (x₀ := x₀)
    (r := g x₀ + r x₀) rfl] at hw
  rw [mem_epsSubdiff_iff (φ := fun x ↦ ((g x : ℝ) : EReal)) (x₀ := x₀) (r := g x₀) rfl]
  intro ε hε
  filter_upwards [hw ε hε, hV.mem_nhds hx₀] with x hx hxV
  rw [EReal.coe_le_coe_iff] at hx ⊢
  have h := abs_le.1 (hstrict x hxV x₀ hx₀)
  simp only [FunLike.coe_sub, Pi.sub_apply]
  nlinarith [norm_nonneg (x - x₀)]

variable [FiniteDimensional ℝ E]

/-- One half of the sum rule with a strictly differentiable addition
([Mordukhovich 2006, Prop. 1.107(ii)]): `v ∈ ∂(g + r)(x₀) ⟹ v - ∇r(x₀) ∈ ∂g(x₀)`. -/
theorem sub_mem_subdiff_of_mem_subdiff_add {g r : E → ℝ} {r' : StrongDual ℝ E} {x₀ : E}
    {U : Set E} (hU : U ∈ 𝓝 x₀) (hg : ContinuousOn g U) (hr : HasStrictFDerivAt r r' x₀)
    {v : StrongDual ℝ E} (hv : v ∈ subdiff (fun x ↦ ((g x + r x : ℝ) : EReal)) x₀) :
    v - r' ∈ subdiff (fun x ↦ ((g x : ℝ) : EReal)) x₀ := by
  obtain ⟨K, V, hV, hrV⟩ := hr.exists_lipschitzOnWith
  have hgr : ContinuousOn (fun x ↦ g x + r x) (U ∩ V) :=
    (hg.mono inter_subset_left).add (hrV.continuousOn.mono inter_subset_right)
  rw [subdiff_eq_outerLimit_epsSubdiff (φ := fun x ↦ ((g x + r x : ℝ) : EReal))
    (x₀ := x₀) (r := g x₀ + r x₀) rfl
    (locallyClosed_epi_of_continuousOn (inter_mem hU hV) hgr _)] at hv
  rw [subdiff_eq_outerLimit_epsSubdiff (φ := fun x ↦ ((g x : ℝ) : EReal)) (x₀ := x₀)
    (r := g x₀) rfl (locallyClosed_epi_of_continuousOn hU hg _)]
  obtain ⟨a, w, ha, hw, hmem⟩ := hv
  have ha1 : Tendsto (fun k ↦ (a k).1) atTop (𝓝 x₀) :=
    (tendsto_funNhds_iff.1 (tendsto_fst.comp ha)).1
  have ha2 : Tendsto (fun k ↦ (a k).2) atTop (𝓝[≥] 0) := tendsto_snd.comp ha
  have hδ : ∀ n : ℕ, ∃ δ > 0, ∀ x ∈ ball x₀ δ, ∀ x' ∈ ball x₀ δ,
      |r x - r x' - r' (x - x')| ≤ (1 / ((n : ℝ) + 1)) * ‖x - x'‖ :=
    fun n ↦ exists_ball_strict_bound hr (by positivity)
  choose δ hδpos hδ using hδ
  have hK : ∀ n, ∃ K, ∀ k ≥ K, (a k).1 ∈ ball x₀ (δ n) :=
    fun n ↦ eventually_atTop.1 (ha1 (ball_mem_nhds _ (hδpos n)))
  choose K hK using hK
  set kk : ℕ → ℕ := fun n ↦ max n (K n) with hkk_def
  have hkk : Tendsto kk atTop atTop := tendsto_atTop_mono (fun n ↦ le_max_left _ _) tendsto_id
  refine ⟨fun n ↦ ((a (kk n)).1, (a (kk n)).2 + 1 / ((n : ℝ) + 1)), fun n ↦ w (kk n) - r',
    ?_, (hw.comp hkk).sub_const r', fun n ↦ ?_⟩
  · rw [Filter.tendsto_prod_iff']
    refine ⟨tendsto_funNhds_iff.2 ⟨ha1.comp hkk, ?_⟩, ?_⟩
    · have hgc : ContinuousAt g x₀ := hg.continuousAt hU
      exact (continuous_coe_real_ereal.tendsto _).comp (hgc.tendsto.comp (ha1.comp hkk))
    · have ha2' := tendsto_nhdsWithin_iff.1 ha2
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · simpa using (ha2'.1.comp hkk).add tendsto_one_div_add_atTop_nhds_zero_nat
      · filter_upwards [hkk.eventually ha2'.2] with n hn
        exact mem_Ici.2 (add_nonneg (mem_Ici.1 hn) (by positivity))
  · exact sub_mem_epsSubdiff_of_add isOpen_ball (hK n (kk n) (le_max_right _ _)) (hδ n)
      (hmem (kk n))

/-- Sum rule with a strictly differentiable addition ([Mordukhovich 2006, Prop. 1.107(ii)]),
extending [Mordukhovich 2018, Prop. 1.30(ii)]: `∂(g + r)(x₀) = ∂g(x₀) + ∇r(x₀)` for `g`
continuous around `x₀` and `r` strictly differentiable at `x₀` (finite dimensions). -/
theorem mem_subdiff_add_strict_iff {g r : E → ℝ} {r' : StrongDual ℝ E} {x₀ : E} {U : Set E}
    (hU : U ∈ 𝓝 x₀) (hg : ContinuousOn g U) (hr : HasStrictFDerivAt r r' x₀)
    {v : StrongDual ℝ E} :
    v ∈ subdiff (fun x ↦ ((g x + r x : ℝ) : EReal)) x₀ ↔
      v - r' ∈ subdiff (fun x ↦ ((g x : ℝ) : EReal)) x₀ := by
  refine ⟨sub_mem_subdiff_of_mem_subdiff_add hU hg hr, fun hv ↦ ?_⟩
  obtain ⟨K, V, hV, hrV⟩ := hr.exists_lipschitzOnWith
  have hgr : ContinuousOn (fun x ↦ g x + r x) (U ∩ V) :=
    (hg.mono inter_subset_left).add (hrV.continuousOn.mono inter_subset_right)
  have hfun : (fun x ↦ (((g x + r x) + (-r) x : ℝ) : EReal)) = fun x ↦ ((g x : ℝ) : EReal) := by
    funext x; simp
  have := sub_mem_subdiff_of_mem_subdiff_add (g := fun x ↦ g x + r x) (r := -r) (r' := -r')
    (inter_mem hU hV) hgr hr.neg (v := v - r') (by rw [hfun]; exact hv)
  simpa using this

end StrictSum

section Composition

open ContinuousLinearMap

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The step in the proof of [Mordukhovich 2018, Thm. 4.5(ii)]: for `g` Lipschitz around `x₀`
and `φ` strictly differentiable at `(x₀, g x₀)`, the function
`x ↦ φ(x, g x) - ⟨∇ᵧφ(x₀, g x₀), g x⟩` is strictly differentiable at `x₀` with derivative
`∇ₓφ(x₀, g x₀)`. -/
theorem hasStrictFDerivAt_comp_sub_comp_inr {g : E → F} {U : Set E} {x₀ : E} (hU : U ∈ 𝓝 x₀)
    {K : ℝ≥0} (hg : LipschitzOnWith K g U) {φ : E × F → ℝ} {φ' : StrongDual ℝ (E × F)}
    (hφ : HasStrictFDerivAt φ φ' (x₀, g x₀)) :
    HasStrictFDerivAt (fun x ↦ φ (x, g x) - φ'.comp (inr ℝ E F) (g x))
      (φ'.comp (inl ℝ E F)) x₀ := by
  rw [hasStrictFDerivAt_iff_isLittleO] at hφ ⊢
  have hgc : ContinuousAt g x₀ := hg.continuousOn.continuousAt hU
  set G : E × E → (E × F) × (E × F) := fun q ↦ ((q.1, g q.1), (q.2, g q.2)) with hG
  have hGt : Tendsto G (𝓝 (x₀, x₀)) (𝓝 ((x₀, g x₀), (x₀, g x₀))) := by
    have h1 : Tendsto (fun q : E × E ↦ q.1) (𝓝 (x₀, x₀)) (𝓝 x₀) := continuous_fst.tendsto _
    have h2 : Tendsto (fun q : E × E ↦ q.2) (𝓝 (x₀, x₀)) (𝓝 x₀) := continuous_snd.tendsto _
    exact (h1.prodMk_nhds (hgc.tendsto.comp h1)).prodMk_nhds
      (h2.prodMk_nhds (hgc.tendsto.comp h2))
  have hlo := hφ.comp_tendsto hGt
  have hO : (fun q : E × E ↦ (G q).1 - (G q).2) =O[𝓝 (x₀, x₀)] fun q ↦ q.1 - q.2 := by
    refine IsBigO.of_bound (max 1 K) ?_
    filter_upwards [prod_mem_nhds hU hU] with q hq
    have hlip : ‖g q.1 - g q.2‖ ≤ K * ‖q.1 - q.2‖ := by
      simpa [dist_eq_norm] using hg.dist_le_mul q.1 hq.1 q.2 hq.2
    simp only [hG, Prod.mk_sub_mk, Prod.norm_mk]
    refine max_le ?_ ?_
    · exact le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _)
    · exact hlip.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  refine (hlo.trans_isBigO hO).congr_left fun q ↦ ?_
  have hsplit : ∀ a : E, ∀ b : F, φ' (a, b) = φ'.comp (inl ℝ E F) a + φ'.comp (inr ℝ E F) b := by
    intro a b
    rw [comp_apply, comp_apply, ← map_add]
    simp
  simp only [hG, Function.comp_apply, Prod.mk_sub_mk, hsplit, map_sub]
  ring

variable [FiniteDimensional ℝ E]

/-- Thm. 4.5(ii) of [Mordukhovich 2018], (4.12), pointwise form: for `g : E → F` Lipschitz
around `x₀` and `φ : E × F → ℝ` strictly differentiable at `(x₀, g x₀)`,
`v ∈ ∂(φ ∘ (I, g))(x₀)` iff `v - ∇ₓφ(x₀, g x₀) ∈ ∂⟨∇ᵧφ(x₀, g x₀), g⟩(x₀)`. The book proves it
directly from the `ω`-representation (1.37); here it follows from the strict sum rule
`mem_subdiff_add_strict_iff` and `hasStrictFDerivAt_comp_sub_comp_inr`. -/
theorem mem_subdiff_comp_strict_iff {g : E → F} {U : Set E} {x₀ : E} (hU : U ∈ 𝓝 x₀)
    {K : ℝ≥0} (hg : LipschitzOnWith K g U) {φ : E × F → ℝ} {φ' : StrongDual ℝ (E × F)}
    (hφ : HasStrictFDerivAt φ φ' (x₀, g x₀)) {v : StrongDual ℝ E} :
    v ∈ subdiff (fun x ↦ ((φ (x, g x) : ℝ) : EReal)) x₀ ↔
      v - φ'.comp (inl ℝ E F) ∈ subdiff (fun x ↦ ((φ'.comp (inr ℝ E F) (g x) : ℝ) : EReal)) x₀ := by
  set φy := φ'.comp (inr ℝ E F)
  have hc : ContinuousOn (fun x ↦ φy (g x)) U := φy.continuous.comp_continuousOn hg.continuousOn
  have hfun : (fun x ↦ ((φ (x, g x) : ℝ) : EReal)) =
      fun x ↦ ((φy (g x) + (φ (x, g x) - φy (g x)) : ℝ) : EReal) := by
    funext x; congr 1; ring
  rw [hfun, mem_subdiff_add_strict_iff hU hc (hasStrictFDerivAt_comp_sub_comp_inr hU hg hφ)]

/-- Thm. 4.5(ii) of [Mordukhovich 2018], (4.12): for `g : E → F` Lipschitz around `x₀` and
`φ : E × F → ℝ` strictly differentiable at `(x₀, ȳ)`, `ȳ = g x₀`,
`∂(φ ∘ (I, g))(x₀) = ∇ₓφ(x₀, ȳ) + ∂⟨∇ᵧφ(x₀, ȳ), g⟩(x₀)`, where `∇ₓφ = φ' ∘ inl` and
`∇ᵧφ = φ' ∘ inr`. -/
theorem subdiff_comp_strict_eq {g : E → F} {U : Set E} {x₀ : E} (hU : U ∈ 𝓝 x₀) {K : ℝ≥0}
    (hg : LipschitzOnWith K g U) {φ : E × F → ℝ} {φ' : StrongDual ℝ (E × F)}
    (hφ : HasStrictFDerivAt φ φ' (x₀, g x₀)) :
    subdiff (fun x ↦ ((φ (x, g x) : ℝ) : EReal)) x₀ =
      (fun w ↦ φ'.comp (inl ℝ E F) + w) ''
        subdiff (fun x ↦ ((φ'.comp (inr ℝ E F) (g x) : ℝ) : EReal)) x₀ := by
  ext v
  rw [mem_subdiff_comp_strict_iff hU hg hφ]
  refine ⟨fun hv ↦ ⟨_, hv, add_sub_cancel _ _⟩, ?_⟩
  rintro ⟨w, hw, rfl⟩
  simpa using hw

/-- Thm. 4.5(ii) of [Mordukhovich 2018], (4.12), combined with the coderivative scalarization
[Mordukhovich 2018, Thm. 1.32]: for `g : E → F` Lipschitz around `x₀` and `φ : E × F → ℝ`
strictly differentiable at `(x₀, ȳ)`, `ȳ = g x₀`,
`∂(φ ∘ (I, g))(x₀) = ∇ₓφ(x₀, ȳ) + D*g(x₀)(∇ᵧφ(x₀, ȳ))`. -/
theorem subdiff_comp_strict_eq_coderiv {g : E → F} {U : Set E} {x₀ : E} (hU : U ∈ 𝓝 x₀)
    {K : ℝ≥0} (hg : LipschitzOnWith K g U) {φ : E × F → ℝ} {φ' : StrongDual ℝ (E × F)}
    (hφ : HasStrictFDerivAt φ φ' (x₀, g x₀)) :
    subdiff (fun x ↦ ((φ (x, g x) : ℝ) : EReal)) x₀ =
      {v | ∃ w ∈ coderiv (fun x ↦ ({g x} : Set F)) x₀ (g x₀) (φ'.comp (inr ℝ E F)),
        v = φ'.comp (inl ℝ E F) + w} := by
  rw [subdiff_comp_strict_eq hU hg hφ, subdiff_comp_eq_coderiv hU hg]
  ext v
  exact ⟨fun ⟨w, hw, h⟩ ↦ ⟨w, hw, h.symm⟩, fun ⟨w, hw, h⟩ ↦ ⟨w, hw, h.symm⟩⟩

end Composition

end VariationalAnalysis
