/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Topology.MetricSpace.Sequences
import VariationalAnalysis.Subdifferential.Lipschitz
import VariationalAnalysis.WellPosedness.Monotone

/-!
# Gâteaux differentiability and convex subdifferentials

[Mordukhovich 2018, p. 130] calls `φ : ℝⁿ → ℝ̄`, finite at `x`, *Gâteaux differentiable* at `x`
with Gâteaux derivative `v` if `(φ(x + t w) - φ(x) - t ⟨v, w⟩) / t → 0` as `t → 0` for every
direction `w`. Here `φ : E → EReal` and this is `HasGateauxDerivAt φ v x`: along each line
`t ↦ x + t w`, `φ` agrees near `t = 0` with a real function with derivative `v w` at `0`.

For convex functions, finite near `x`, in finite dimensions, Gâteaux and Fréchet
differentiability agree and are equivalent to `∂φ(x)` being a singleton
[Mordukhovich 2018, Exercise 3.90(iv)]; this is the "well-known fact of convex analysis" used in
the proof of Cor. 3.26. Here `∂φ` is the basic subdifferential `subdiff`, which for convex `φ`
is the subdifferential of convex analysis (`mem_subdiff_of_convex`, Prop. 1.25; for real-valued
functions on Hilbert spaces this is `SubderivAt` of `ConvexAnalysis`, see
`toDual_image_subderivAt`). `ConvexAnalysis` has the direction "differentiable ⇒ singleton"
(`SubderivAt_eq_gradient`, in Hilbert spaces), but not the converse.

## Main declarations

* `HasGateauxDerivAt φ v x`: Gâteaux differentiability of `φ : E → EReal` at `x` with Gâteaux
  derivative `v` [Mordukhovich 2018, p. 130].

## Main results

* `hasGateauxDerivAt_coe_iff`: for real-valued `f`, Gâteaux differentiability is the existence
  of all line derivatives `HasLineDerivAt ℝ f (v w) x w`, given by one linear map `v`.
* `hasGateauxDerivAt_of_hasFDerivAt`: Fréchet differentiability implies Gâteaux differentiability
  [Mordukhovich 2018, p. 130].
* `HasGateauxDerivAt.subdiff_eq_singleton`: for convex `φ`, Gâteaux differentiability at `x`
  implies `∂φ(x) = {v}` (any normed space); `subdiff_eq_singleton_of_hasFDerivAt`.
* `hasFDerivAt_of_subdiff_eq_singleton`: for convex `φ`, finite near `x`, in finite dimensions,
  `∂φ(x) = {v}` implies Fréchet differentiability.
* `tfae_hasGateauxDerivAt_of_convex`, `subdiff_eq_singleton_iff_hasFDerivAt`: Exercise 3.90(iv)
  of [Mordukhovich 2018].
* `hasFDerivAt_of_lipschitzOnWith_of_le`: a function with `f z ≥ f y + ⟨g y, z - y⟩ - c‖z - y‖²`
  for a Lipschitz `g` is of class `C^{1,1}` with `∇f = g`.
* `LipschitzLikeWith.exists_hasFDerivAt_of_convex`: if `∂φ` of a convex `φ` is Lipschitz-like
  around `(x₀, v₀) ∈ gph ∂φ`, then `φ` is of class `C^{1,1}` around `x₀` with
  `∂φ(x) = {∇φ(x)}` (Prop. 3.24 and Exercise 3.90(iv)).
* `not_lipschitzLikeAt_subdiff_of_convex`: the reduced form of Cor. 3.26 and Cor. 3.30 of
  [Mordukhovich 2018]: `∂φ` of a convex `φ` which is not Gâteaux differentiable around `x₀` is
  not Lipschitz-like around `(x₀, v₀)`.

## Using these results for Cor. 3.26 and Cor. 3.30

With Thm. 3.20 (`MetricallyRegularAt (pvsSolutionMap f (subdiff φ)) x₀ y₀ ↔
LipschitzLikeAt (subdiff φ) y₀ (-f (x₀, y₀))`), Cor. 3.26 is
`fun h ↦ not_lipschitzLikeAt_subdiff_of_convex hconv h₀ hnd (thm320.1 h)`, and Cor. 3.30 is the
same argument after Cor. 3.21 (metric regularity ⇔ `∂ψ` Lipschitz-like around `(w₀, v₀)`).
-/

open Filter Topology Set Metric
open scoped NNReal

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Gateaux

/-- Gâteaux differentiability [Mordukhovich 2018, p. 130]: `φ : E → EReal` is Gâteaux
differentiable at `x` with Gâteaux derivative `v` if for every direction `w`,
`(φ(x + t w) - φ(x) - t ⟨v, w⟩) / t → 0` as `t → 0`. Formally: along the line `t ↦ x + t w`,
`φ` agrees near `t = 0` with a real function `g` with `g'(0) = ⟨v, w⟩` (in particular `φ` is
finite at `x` and near `x` along each line). -/
def HasGateauxDerivAt (φ : E → EReal) (v : StrongDual ℝ E) (x : E) : Prop :=
  ∀ w : E, ∃ g : ℝ → ℝ, (∀ᶠ t in 𝓝 (0 : ℝ), φ (x + t • w) = g t) ∧ HasDerivAt g (v w) 0

variable {φ : E → EReal} {v : StrongDual ℝ E} {x : E}

/-- A Gâteaux differentiable function is finite at the point. -/
theorem HasGateauxDerivAt.exists_eq (h : HasGateauxDerivAt φ v x) : ∃ r : ℝ, φ x = r := by
  obtain ⟨g, hg, -⟩ := h 0
  exact ⟨g 0, by simpa using hg.self_of_nhds⟩

/-- For a real-valued `f`, Gâteaux differentiability with derivative `v` means that `f` has the
line derivative `v w` in every direction `w`. -/
theorem hasGateauxDerivAt_coe_iff {f : E → ℝ} :
    HasGateauxDerivAt (fun y ↦ (f y : EReal)) v x ↔ ∀ w, HasLineDerivAt ℝ f (v w) x w := by
  constructor
  · intro h w
    obtain ⟨g, hg, hd⟩ := h w
    exact hd.congr_of_eventuallyEq (hg.mono fun t ht ↦ EReal.coe_eq_coe_iff.1 ht)
  · intro h w
    exact ⟨fun t ↦ f (x + t • w), Eventually.of_forall fun _ ↦ rfl, h w⟩

/-- [Mordukhovich 2018, p. 131]: Fréchet differentiability implies Gâteaux differentiability with
the same derivative. Here `φ` agrees near `x` with a real function `f` differentiable at `x`. -/
theorem hasGateauxDerivAt_of_hasFDerivAt {f : E → ℝ} (hf : HasFDerivAt f v x)
    (hφ : ∀ᶠ y in 𝓝 x, φ y = f y) : HasGateauxDerivAt φ v x := by
  intro w
  refine ⟨fun t ↦ f (x + t • w), ?_, hf.hasLineDerivAt w⟩
  have : Tendsto (fun t : ℝ ↦ x + t • w) (𝓝 0) (𝓝 x) :=
    (continuous_const.add (continuous_id.smul continuous_const)).tendsto' 0 x (by simp)
  exact this.eventually hφ

end Gateaux

section Slope

/-- If `g'(0) = d` and `g t ≤ g 0 + t c` for small `t > 0`, then `d ≤ c`. -/
theorem le_of_hasDerivAt_of_eventually_le {g : ℝ → ℝ} {d c : ℝ} (hg : HasDerivAt g d 0)
    (h : ∀ᶠ t in 𝓝[>] (0 : ℝ), g t ≤ g 0 + t * c) : d ≤ c := by
  refine le_of_tendsto hg.tendsto_slope_zero_right ?_
  filter_upwards [h, self_mem_nhdsWithin] with t ht ht0
  have ht0 : (0 : ℝ) < t := ht0
  rw [zero_add, smul_eq_mul, inv_mul_le_iff₀ ht0]
  linarith

/-- If `g'(0) = d` and `g t ≥ g 0 + t c` for small `t > 0`, then `c ≤ d`. -/
theorem le_of_hasDerivAt_of_eventually_ge {g : ℝ → ℝ} {d c : ℝ} (hg : HasDerivAt g d 0)
    (h : ∀ᶠ t in 𝓝[>] (0 : ℝ), g 0 + t * c ≤ g t) : c ≤ d := by
  refine ge_of_tendsto hg.tendsto_slope_zero_right ?_
  filter_upwards [h, self_mem_nhdsWithin] with t ht ht0
  have ht0 : (0 : ℝ) < t := ht0
  rw [zero_add, smul_eq_mul, le_inv_mul_iff₀ ht0]
  linarith

end Slope

section Convex

variable {φ : E → EReal} {v : StrongDual ℝ E} {x : E}

/-- Convexity of the epigraph along a segment: if `φ x ≤ r` and `φ z ≤ α`, then
`φ (x + t (z - x)) ≤ r + t (α - r)` for `t ∈ [0, 1]`. -/
theorem apply_add_smul_sub_le_of_convex (hconv : Convex ℝ (φ.Epi univ)) {z : E} {r α : ℝ}
    (hx : φ x ≤ r) (hz : φ z ≤ α) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    φ (x + t • (z - x)) ≤ ((r + t * (α - r) : ℝ) : EReal) := by
  have h := (hconv (⟨mem_univ _, hx⟩ : ((x, r) : E × ℝ) ∈ φ.Epi univ)
    (⟨mem_univ _, hz⟩ : ((z, α) : E × ℝ) ∈ φ.Epi univ) (sub_nonneg.2 ht1) ht0
    (sub_add_cancel 1 t)).2
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at h
  have e1 : (1 - t) • x + t • z = x + t • (z - x) := by
    rw [sub_smul, one_smul, smul_sub]; abel
  have e2 : (1 - t) * r + t * α = r + t * (α - r) := by ring
  rwa [e1, e2] at h

/-- A function with convex epigraph which agrees with a real function `f` on a convex set `C` is
convex on `C`. -/
theorem convexOn_of_convex_epi {C : Set E} {f : E → ℝ} (hC : Convex ℝ C)
    (hconv : Convex ℝ (φ.Epi univ)) (hf : ∀ y ∈ C, φ y = f y) : ConvexOn ℝ C f := by
  refine ⟨hC, fun y₁ hy₁ y₂ hy₂ a b ha hb hab ↦ ?_⟩
  have h := (hconv (⟨mem_univ _, (hf y₁ hy₁).le⟩ : ((y₁, f y₁) : E × ℝ) ∈ φ.Epi univ)
    (⟨mem_univ _, (hf y₂ hy₂).le⟩ : ((y₂, f y₂) : E × ℝ) ∈ φ.Epi univ) ha hb hab).2
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at h
  rw [hf _ (hC hy₁ hy₂ ha hb hab), EReal.coe_le_coe_iff] at h
  simpa only [smul_eq_mul] using h

omit [NormedSpace ℝ E] in
/-- A function finite near `x` agrees near `x` with the real function `y ↦ (φ y).toReal`; this
provides the real function `f` of the results below. -/
theorem eventually_eq_toReal {φ : E → EReal} {x : E} (h : ∀ᶠ y in 𝓝 x, φ y ≠ ⊤ ∧ φ y ≠ ⊥) :
    ∀ᶠ y in 𝓝 x, φ y = ((φ y).toReal : EReal) :=
  h.mono fun _ hy ↦ (EReal.coe_toReal hy.1 hy.2).symm

/-- For a convex function, Gâteaux differentiability at `x` with derivative `v` implies
`∂φ(x) = {v}` [Mordukhovich 2018, Exercise 3.90(iv)] (in any normed space). -/
theorem HasGateauxDerivAt.subdiff_eq_singleton (hconv : Convex ℝ (φ.Epi univ))
    (h : HasGateauxDerivAt φ v x) : subdiff φ x = {v} := by
  obtain ⟨r, hr⟩ := h.exists_eq
  have hg0 : ∀ w (g : ℝ → ℝ), (∀ᶠ t in 𝓝 (0 : ℝ), φ (x + t • w) = g t) → g 0 = r := by
    intro w g hg
    have := hg.self_of_nhds
    rw [zero_smul, add_zero, hr, EReal.coe_eq_coe_iff] at this
    exact this.symm
  ext u
  rw [mem_singleton_iff, mem_subdiff_of_convex hconv hr]
  constructor
  · intro hu
    have key : ∀ w, u w ≤ v w := by
      intro w
      obtain ⟨g, hg, hd⟩ := h w
      have h0 := hg0 w g hg
      refine le_of_hasDerivAt_of_eventually_ge hd ?_
      filter_upwards [nhdsWithin_le_nhds hg] with t ht
      have := hu (x + t • w)
      rw [ht, add_sub_cancel_left, map_smul, smul_eq_mul, EReal.coe_le_coe_iff] at this
      rw [h0]
      exact this
    ext w
    have h1 := key w
    have h2 := key (-w)
    rw [map_neg, map_neg] at h2
    linarith
  · intro hu z
    subst hu
    suffices H : ∀ α : ℝ, φ z ≤ α → r + u (z - x) ≤ α by
      induction hφz : φ z with
      | bot =>
        have := H (r + u (z - x) - 1) (by rw [hφz]; exact bot_le)
        linarith
      | top => exact le_top
      | coe s => exact EReal.coe_le_coe_iff.2 (H s hφz.le)
    intro α hα
    obtain ⟨g, hg, hd⟩ := h (z - x)
    have h0 := hg0 _ g hg
    refine add_le_of_le_sub_left (le_of_hasDerivAt_of_eventually_le hd ?_)
    filter_upwards [nhdsWithin_le_nhds hg, Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht ht1
    have := apply_add_smul_sub_le_of_convex hconv hr.le hα ht1.1.le ht1.2.le
    rw [ht, EReal.coe_le_coe_iff] at this
    rw [h0]
    exact this

/-- For a convex function, Fréchet differentiability at `x` with derivative `v` implies
`∂φ(x) = {v}` [Mordukhovich 2018, Exercise 3.90(iv)] (in any normed space). -/
theorem subdiff_eq_singleton_of_hasFDerivAt (hconv : Convex ℝ (φ.Epi univ)) {f : E → ℝ}
    (hφ : ∀ᶠ y in 𝓝 x, φ y = f y) (hf : HasFDerivAt f v x) : subdiff φ x = {v} :=
  (hasGateauxDerivAt_of_hasFDerivAt hf hφ).subdiff_eq_singleton hconv

/-- For a convex function, finite near `x`, in a finite-dimensional space, `∂φ(x) = {v}`
implies Fréchet differentiability at `x` with derivative `v` [Mordukhovich 2018,
Exercise 3.90(iv)]. Here `φ` agrees near `x` with the real function `f`.

The proof is by compactness: if `f y - f x - ⟨v, y - x⟩ > ε ‖y - x‖` along `yₖ → x`, pick
`uₖ ∈ ∂φ(yₖ)` (bounded, since `f` is locally Lipschitz); a cluster point of `(uₖ)` lies in
`∂φ(x) = {v}`, while `⟨uₖ - v, yₖ - x⟩ > ε ‖yₖ - x‖` by the subgradient inequality. -/
theorem hasFDerivAt_of_subdiff_eq_singleton [FiniteDimensional ℝ E]
    (hconv : Convex ℝ (φ.Epi univ)) {f : E → ℝ} (hf : ∀ᶠ y in 𝓝 x, φ y = f y)
    (hv : subdiff φ x = {v}) : HasFDerivAt f v x := by
  obtain ⟨δ, hδ, hδf⟩ := Metric.mem_nhds_iff.1 hf
  have hcvx : ConvexOn ℝ (ball x δ) f :=
    convexOn_of_convex_epi (convex_ball x δ) hconv fun y hy ↦ hδf hy
  obtain ⟨K, t, ht, hK⟩ := hcvx.locallyLipschitzOn isOpen_ball (mem_ball_self hδ)
  rw [isOpen_ball.nhdsWithin_eq (mem_ball_self hδ)] at ht
  obtain ⟨ρ, hρ, hρt⟩ := Metric.mem_nhds_iff.1 (inter_mem ht (ball_mem_nhds x hδ))
  have hBδ : ball x ρ ⊆ ball x δ := fun y hy ↦ (hρt hy).2
  have hKB : LipschitzOnWith K f (ball x ρ) := hK.mono fun y hy ↦ (hρt hy).1
  have hsub : ∀ y ∈ ball x δ, ∀ u ∈ subdiff φ y, ∀ z ∈ ball x δ, f y + u (z - y) ≤ f z := by
    intro y hy u hu z hz
    have := (mem_subdiff_of_convex hconv (hδf hy)).1 hu z
    rwa [hδf hz, EReal.coe_le_coe_iff] at this
  have hne : ∀ y ∈ ball x ρ, ∃ u ∈ subdiff φ y, ‖u‖ ≤ K := by
    intro y hy
    have hBy : ball x ρ ∈ 𝓝 y := isOpen_ball.mem_nhds hy
    have heq : subdiff φ y = subdiff (fun z ↦ (f z : EReal)) y :=
      subdiff_congr (Filter.mem_of_superset hBy fun z hz ↦ hδf (hBδ hz))
    obtain ⟨u, hu⟩ := subdiff_nonempty_of_lipschitz hBy hKB
    exact ⟨u, heq ▸ hu, norm_le_of_mem_subdiff_of_lipschitz hBy hKB hu⟩
  have hvx : v ∈ subdiff φ x := hv ▸ mem_singleton v
  have hlow : ∀ y ∈ ball x δ, f x + v (y - x) ≤ f y := hsub x (mem_ball_self hδ) v hvx
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hfreq : ∃ᶠ y in 𝓝 x, y ∈ ball x ρ ∧ ε * ‖y - x‖ < f y - f x - v (y - x) := by
    refine (hcon.and_eventually (ball_mem_nhds x hρ)).mono fun y ⟨hy1, hy2⟩ ↦ ⟨hy2, ?_⟩
    rw [not_le, Real.norm_eq_abs] at hy1
    have := hlow y (hBδ hy2)
    rwa [abs_of_nonneg (by linarith)] at hy1
  obtain ⟨y, hyx, hyP⟩ := frequently_iff_seq_forall.1 hfreq
  choose u hu huK using fun k ↦ hne (y k) (hyP k).1
  obtain ⟨u₀, -, ψ, hψ, hlim⟩ := tendsto_subseq_of_bounded
    (isBounded_closedBall (x := (0 : StrongDual ℝ E)) (r := K))
    (fun k ↦ mem_closedBall_zero_iff.2 (huK k))
  have hyψ : Tendsto (y ∘ ψ) atTop (𝓝 x) := hyx.comp hψ.tendsto_atTop
  have hfc : ContinuousAt f x := hKB.continuousOn.continuousAt (ball_mem_nhds x hρ)
  have hu₀ : u₀ ∈ subdiff φ x := by
    rw [subdiff_eq_regularSubdiff_of_convex hconv,
      mem_regularSubdiff_iff (hδf (mem_ball_self hδ))]
    intro ε' hε'
    filter_upwards [ball_mem_nhds x hδ] with z hz
    rw [hδf hz, EReal.coe_le_coe_iff]
    have hlimz : Tendsto (fun k ↦ f (y (ψ k)) + u (ψ k) (z - y (ψ k))) atTop
        (𝓝 (f x + u₀ (z - x))) := by
      refine (hfc.tendsto.comp hyψ).add ?_
      exact ((continuous_fst.clm_apply continuous_snd).tendsto (u₀, z - x)).comp
        (hlim.prodMk_nhds (tendsto_const_nhds.sub hyψ))
    have hle : f x + u₀ (z - x) ≤ f z :=
      le_of_tendsto' hlimz fun k ↦ hsub _ (hBδ (hyP (ψ k)).1) _ (hu (ψ k)) z hz
    nlinarith [norm_nonneg (z - x)]
  rw [hv, mem_singleton_iff] at hu₀
  subst hu₀
  have hsmall : ∀ᶠ k in atTop, ‖u (ψ k) - u₀‖ < ε :=
    (tendsto_iff_norm_sub_tendsto_zero.1 hlim).eventually (gt_mem_nhds hε)
  obtain ⟨k, hk⟩ := hsmall.exists
  obtain ⟨hyB, hyε⟩ := hyP (ψ k)
  have h1 := hsub (y (ψ k)) (hBδ hyB) (u (ψ k)) (hu (ψ k)) x (mem_ball_self hδ)
  have h2 : (u (ψ k) - u₀) (y (ψ k) - x) ≤ ‖u (ψ k) - u₀‖ * ‖y (ψ k) - x‖ :=
    le_trans (le_abs_self _) ((u (ψ k) - u₀).le_opNorm _)
  have h3 : u (ψ k) (x - y (ψ k)) = -u (ψ k) (y (ψ k) - x) := by rw [← map_neg, neg_sub]
  rw [sub_apply] at h2
  nlinarith [norm_nonneg (y (ψ k) - x)]

/-- Exercise 3.90(iv) of [Mordukhovich 2018]: for a convex function `φ`, finite near `x` (it
agrees there with the real function `f`), on a finite-dimensional space, the following are
equivalent: `φ` is Gâteaux differentiable at `x` with derivative `v`; `f` is Fréchet
differentiable at `x` with derivative `v`; `∂φ(x) = {v}`. -/
theorem tfae_hasGateauxDerivAt_of_convex [FiniteDimensional ℝ E]
    (hconv : Convex ℝ (φ.Epi univ)) {f : E → ℝ} (hf : ∀ᶠ y in 𝓝 x, φ y = f y) :
    List.TFAE [HasGateauxDerivAt φ v x, HasFDerivAt f v x, subdiff φ x = {v}] := by
  tfae_have 1 → 3 := fun h ↦ h.subdiff_eq_singleton hconv
  tfae_have 3 → 2 := hasFDerivAt_of_subdiff_eq_singleton hconv hf
  tfae_have 2 → 1 := fun h ↦ hasGateauxDerivAt_of_hasFDerivAt h hf
  tfae_finish

/-- [Mordukhovich 2018, Exercise 3.90(iv)]: for a convex function, finite near `x` (where it
agrees with `f`), in finite dimensions, `∂φ(x) = {v}` iff `f` is differentiable at `x` with
derivative `v`. -/
theorem subdiff_eq_singleton_iff_hasFDerivAt [FiniteDimensional ℝ E]
    (hconv : Convex ℝ (φ.Epi univ)) {f : E → ℝ} (hf : ∀ᶠ y in 𝓝 x, φ y = f y) :
    subdiff φ x = {v} ↔ HasFDerivAt f v x :=
  ((tfae_hasGateauxDerivAt_of_convex hconv hf).out 2 1)

/-- [Mordukhovich 2018, Exercise 3.90(iv)]: for a convex function, finite near `x`, in finite
dimensions, Gâteaux and Fréchet differentiability at `x` agree. -/
theorem hasGateauxDerivAt_iff_hasFDerivAt_of_convex [FiniteDimensional ℝ E]
    (hconv : Convex ℝ (φ.Epi univ)) {f : E → ℝ} (hf : ∀ᶠ y in 𝓝 x, φ y = f y) :
    HasGateauxDerivAt φ v x ↔ HasFDerivAt f v x :=
  ((tfae_hasGateauxDerivAt_of_convex hconv hf).out 0 1)

end Convex

section C11

/-- A sandwich criterion for `C^{1,1}` functions: if `g` is Lipschitz on an open set `U` with
modulus `ℓ` and `f z ≥ f y + ⟨g y, z - y⟩ - c ‖z - y‖²` for all `y, z ∈ U`, then `f` is
differentiable at every `y ∈ U` with `∇f(y) = g y`; indeed
`|f z - f y - ⟨g y, z - y⟩| ≤ (ℓ + |c|) ‖z - y‖²`. -/
theorem hasFDerivAt_of_lipschitzOnWith_of_le {U : Set E} (hU : IsOpen U) {f : E → ℝ}
    {g : E → StrongDual ℝ E} {ℓ : ℝ≥0} {c : ℝ} (hg : LipschitzOnWith ℓ g U)
    (h : ∀ y ∈ U, ∀ z ∈ U, f y + g y (z - y) - c * ‖z - y‖ ^ 2 ≤ f z) {y : E} (hy : y ∈ U) :
    HasFDerivAt f (g y) y := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hℓ : (0 : ℝ) ≤ ℓ := ℓ.coe_nonneg
  have hK : 0 < (ℓ : ℝ) + |c| + 1 := by positivity
  filter_upwards [hU.mem_nhds hy, ball_mem_nhds y (div_pos hε hK)] with z hz hzb
  have hzy : ‖z - y‖ < ε / (ℓ + |c| + 1) := by rwa [mem_ball, dist_eq_norm] at hzb
  have h1 := h y hy z hz
  have h2 := h z hz y hy
  have hL : ‖g z - g y‖ ≤ ℓ * ‖z - y‖ := by
    rw [← dist_eq_norm, ← dist_eq_norm]
    exact hg.dist_le_mul z hz y hy
  have h3 : (g z - g y) (z - y) ≤ ‖g z - g y‖ * ‖z - y‖ :=
    le_trans (le_abs_self _) ((g z - g y).le_opNorm _)
  rw [sub_apply] at h3
  have h4 : g z (y - z) = -g z (z - y) := by rw [← map_neg, neg_sub]
  have h5 : ‖y - z‖ = ‖z - y‖ := norm_sub_rev _ _
  rw [h4, h5] at h2
  have hc : c ≤ |c| := le_abs_self c
  have hc' : -c ≤ |c| := neg_le_abs c
  set a := ‖z - y‖ with ha_def
  have ha : 0 ≤ a := norm_nonneg _
  have hLa : ‖g z - g y‖ * a ≤ ℓ * a * a := by nlinarith
  have hD : |f z - f y - g y (z - y)| ≤ (ℓ + |c|) * a ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg a]
  have hsmall : ((ℓ : ℝ) + |c|) * a ≤ ε := by
    rw [lt_div_iff₀ hK] at hzy
    nlinarith [abs_nonneg c]
  rw [Real.norm_eq_abs]
  calc |f z - f y - g y (z - y)| ≤ (ℓ + |c|) * a ^ 2 := hD
    _ = ((ℓ + |c|) * a) * a := by ring
    _ ≤ ε * a := by gcongr

variable {φ : E → EReal} {x₀ : E} {v₀ : StrongDual ℝ E} {ℓ : ℝ≥0}

/-- Prop. 3.24 and Exercise 3.90(iv) of [Mordukhovich 2018] combined, as used in Cor. 3.26: if the
subdifferential of a convex function `φ` is Lipschitz-like with modulus `ℓ` around
`(x₀, v₀) ∈ gph ∂φ`, then `φ` is of class `C^{1,1}` on an open neighborhood `U` of `x₀`: it
agrees on `U` with a real function `f` which is differentiable at every `y ∈ U`, with
`∂φ(y) = {∇f(y)}` and `∇f` Lipschitz on `U` with modulus `ℓ`. No finite dimensionality is
needed. -/
theorem LipschitzLikeWith.exists_hasFDerivAt_of_convex (hconv : Convex ℝ (φ.Epi univ))
    (hL : LipschitzLikeWith ℓ (subdiff φ) x₀ v₀) (h₀ : v₀ ∈ subdiff φ x₀) :
    ∃ U, IsOpen U ∧ x₀ ∈ U ∧ ∃ f : E → ℝ, ∃ g : E → StrongDual ℝ E, (∀ y ∈ U, φ y = f y) ∧
      (∀ y ∈ U, subdiff φ y = {g y}) ∧ (∀ y ∈ U, HasFDerivAt f (g y) y) ∧
      LipschitzOnWith ℓ g U := by
  obtain ⟨U, hU, g, hg, hgL, -⟩ := hL.exists_eq_singleton_of_convex
    (globallyMonotone_subdiff_of_convex hconv).locallyMonotoneAt.locallyHypomonotoneAt h₀
    (Eventually.of_forall (convex_subdiff_of_convex hconv))
  obtain ⟨ρ, hρ, hρU⟩ := Metric.mem_nhds_iff.1 hU
  have hgmem : ∀ y ∈ ball x₀ ρ, g y ∈ subdiff φ y := fun y hy ↦
    (hg y (hρU hy)).symm ▸ mem_singleton _
  have hfin : ∀ y ∈ ball x₀ ρ, φ y = ((φ y).toReal : EReal) := by
    intro y hy
    obtain ⟨r, hr, -⟩ := hgmem y hy
    rw [hr, EReal.toReal_coe]
  refine ⟨ball x₀ ρ, isOpen_ball, mem_ball_self hρ, fun y ↦ (φ y).toReal, g, hfin,
    fun y hy ↦ hg y (hρU hy), fun y hy ↦ hasFDerivAt_of_lipschitzOnWith_of_le isOpen_ball
      (hgL.mono hρU) (c := 0) ?_ hy, hgL.mono hρU⟩
  intro y hy z hz
  have := (mem_subdiff_of_convex hconv (hfin y hy)).1 (hgmem y hy) z
  rw [hfin z hz, EReal.coe_le_coe_iff] at this
  simpa using this

/-- Reduced form of Cor. 3.26 and Cor. 3.30 of [Mordukhovich 2018]: if `φ` is convex,
`v₀ ∈ ∂φ(x₀)` (so `φ` is finite at `x₀`), and `φ` is not Gâteaux differentiable around `x₀`
(there is no neighborhood of `x₀` at each point of which `φ` is Gâteaux differentiable), then the
subgradient mapping `∂φ` is not Lipschitz-like around `(x₀, v₀)`. The book's proof uses the
maximal monotonicity of `∂φ`; monotonicity and the convexity of the values of `∂φ` suffice. -/
theorem not_lipschitzLikeAt_subdiff_of_convex (hconv : Convex ℝ (φ.Epi univ))
    (h₀ : v₀ ∈ subdiff φ x₀) (hnd : ¬ ∃ U ∈ 𝓝 x₀, ∀ y ∈ U, ∃ v, HasGateauxDerivAt φ v y) :
    ¬ LipschitzLikeAt (subdiff φ) x₀ v₀ := by
  rintro ⟨ℓ, hL⟩
  obtain ⟨U, hUo, hx₀U, f, g, hf, -, hd, -⟩ := hL.exists_hasFDerivAt_of_convex hconv h₀
  exact hnd ⟨U, hUo.mem_nhds hx₀U, fun y hy ↦
    ⟨g y, hasGateauxDerivAt_of_hasFDerivAt (hd y hy)
      (Filter.mem_of_superset (hUo.mem_nhds hy) hf)⟩⟩

end C11

end VariationalAnalysis
