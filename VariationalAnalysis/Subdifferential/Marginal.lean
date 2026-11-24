/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Topology.MetricSpace.Sequences
import VariationalAnalysis.SetValued.Basic
import VariationalAnalysis.Subdifferential.SmoothChain
import VariationalAnalysis.Subdifferential.SumRule
import VariationalAnalysis.WellPosedness.Coderivative

/-!
# Subdifferentiation of marginal functions

Basic and singular subgradients of the marginal (optimal value) function
[Mordukhovich 2018, Section 4.1]

  `μ(x) = inf {φ(x, y) | y ∈ G x}`  (4.1),   `M(x) = {y ∈ G x | φ(x, y) = μ(x)}`  (4.2),

for `φ : E × F → EReal` and `G : E ⇉ F` in finite-dimensional real normed spaces. With
`ϑ = φ + δ_{gph G}` (`marginalPenalty`), the book's proof of Thm. 4.1 shows
`∂μ(x₀) ⊆ {x | (x, 0) ∈ ∂ϑ(x₀, y₀)}` and `∂^∞μ(x₀) ⊆ {x | (x, 0) ∈ ∂^∞ϑ(x₀, y₀)}` and applies
the sum rule (Thm. 2.19) to `ϑ` under the qualification condition (4.3)
`∂^∞φ(x₀, y₀) ∩ (-N((x₀, y₀); gph G)) = {0}`. Here both estimates come from one geometric step
(`comp_epiProj_mem_normalCone_epi`): a normal `ℓ` to `epi μ` at `(x₀, μ x₀)` gives the normal
`((x, y), α) ↦ ℓ(x, α)` to `epi ϑ` at `((x₀, y₀), μ x₀)`. It pulls back the regular normals of
the outer limit defining `N(·; epi μ)` along `((x, y), α) ↦ (x, α)`, which maps `epi ϑ` into
`epi μ`, at base points `((xₖ, yₖ), αₖ)` with `yₖ ∈ M(xₖ)`, `yₖ → y₀`; neither `ω`-normals nor
the missing half of (1.38) are needed.

## Hypotheses

* The book assumes `M` inner semicontinuous at `(x₀, y₀)` but uses sequences `xₖ →μ x₀`
  (`xₖ → x₀`, `μ(xₖ) → μ(x₀)`), along which `M(xₖ)` may be empty. The main statements
  (`subdiff_marginal_subset`, `singularSubdiff_marginal_subset`) assume `M` `μ`-inner
  semicontinuous at `(x₀, y₀)` [Mordukhovich 2006, Def. 1.63]: `y₀ ∈ Lim inf_{x →μ x₀} M(x)`.
* For the singular estimate (4.5) the base points of the normals to `epi μ` need not satisfy
  `μ(xₖ) → μ(x₀)`; we add that `μ` is lower semicontinuous at `x₀`. This cannot be dropped:
  for `E = F = ℝ`, `φ(x, y) = -min(1, |y|)`, `G(x) = {0}` for `x ∈ [-1, 0] \ S`,
  `G(-1/k) = {0, k}` (`S = {-1/k | k ≥ 1}`), `G(x) = ∅` otherwise, one has `μ = 0` on
  `[-1, 0] \ S`, `μ = -1` on `S`, `M` is `μ`-inner semicontinuous at `(0, 0)`, `φ` is
  Lipschitz and `gph G` closed, but `-1 ∈ ∂^∞μ(0)` (regular normals `(-1, 0)` to the vertical
  rays `{-1/k} × [-1, ∞)` at `(-1/k, -1/k)`), while the right-hand side of (4.5) is
  `D*G(0, 0)(0) = [0, ∞)`.
* With the book's inner semicontinuity (`InnerSemicontinuousAt`, relative to `dom M`) we add
  that the infimum in (4.1) is attained near `x₀` wherever `μ < ⊤` (`dom μ ⊆ dom M` near `x₀`).
  Then `M` is `μ`-inner semicontinuous (`mem_innerLimit_funNhds_of_innerSemicontinuousAt`) and
  `μ` is l.s.c. at `x₀` (`lowerSemicontinuousAt_marginal_of_innerSemicontinuousAt`), so both
  (4.4) and (4.5) hold (`subdiff_marginal_subset_of_innerSemicontinuousAt`,
  `singularSubdiff_marginal_subset_of_innerSemicontinuousAt`). The same attainment hypothesis
  is used in part (ii), with a closed `gph G`.

Sets of the form `⋃_{(u, v) ∈ ∂φ(x₀, y₀)} [u + D*G(x₀, y₀)(v)]` are written
`{x | ∃ u v, u.coprod v ∈ ∂φ(x₀, y₀) ∧ x - u ∈ D*G(x₀, y₀)(v)}`.

## Main results

* `marginal`, `argminMap`: (4.1), (4.2) of [Mordukhovich 2018].
* `subdiff_marginal_subset_penalty`, `singularSubdiff_marginal_subset_penalty`: the estimates
  through `ϑ` in the proof of Thm. 4.1.
* `subdiff_marginal_subset`, `singularSubdiff_marginal_subset`: Thm. 4.1(i), (4.4), (4.5), under
  `μ`-inner semicontinuity; `..._of_innerSemicontinuousAt`: the book's version.
* `subdiff_marginal_subset_of_locallyBoundedAt`,
  `singularSubdiff_marginal_subset_of_locallyBoundedAt`: Thm. 4.1(ii).
* `marginal_subset_of_lipschitz`, `marginal_subset_of_metricallyRegularAt`: Cor. 4.2, with the
  qualification conditions `marginal_qc_of_lipschitz`, `marginal_qc_of_metricallyRegularAt`.
* `singularSubdiff_marginal_eq_zero_of_lipschitzLikeAt`,
  `singularSubdiff_marginal_eq_zero_of_locallyBoundedAt`: the reduction `∂^∞μ(x₀) = {0}` in the
  proof of Cor. 4.3; Cor. 4.3 itself is in `VariationalAnalysis.Subdifferential.MarginalLipschitz`.
* `subdiff_comp_snd`, `subdiff_comp_fst` (and singular versions): subgradients of functions of
  one variable on a product [Mordukhovich 2018, Exercise 1.72].
-/

open Filter Topology Set Metric
open scoped Pointwise

namespace VariationalAnalysis

section Definitions

variable {E F : Type*}

/-- The marginal (optimal value) function [Mordukhovich 2018, (4.1)]
`μ(x) = inf {φ(x, y) | y ∈ G x}` of a cost `φ : E × F → EReal` and a constraint mapping
`G : E ⇉ F`; it is `⊤` where `G x = ∅`. -/
noncomputable def marginal (φ : E × F → EReal) (G : E → Set F) (x : E) : EReal :=
  ⨅ y ∈ G x, φ (x, y)

/-- The argminimum mapping [Mordukhovich 2018, (4.2)]
`M(x) = {y ∈ G x | φ(x, y) = μ(x)}` of the marginal function (4.1). -/
def argminMap (φ : E × F → EReal) (G : E → Set F) (x : E) : Set F :=
  {y | y ∈ G x ∧ φ (x, y) = marginal φ G x}

variable {φ : E × F → EReal} {G : E → Set F} {x : E} {y : F}

theorem marginal_le (hy : y ∈ G x) : marginal φ G x ≤ φ (x, y) := iInf₂_le y hy

theorem mem_argminMap_iff : y ∈ argminMap φ G x ↔ y ∈ G x ∧ φ (x, y) = marginal φ G x :=
  Iff.rfl

end Definitions

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The function `ϑ(x, y) = φ(x, y) + δ((x, y); gph G)` of the proof of
[Mordukhovich 2018, Thm. 4.1]. -/
noncomputable def marginalPenalty (φ : E × F → EReal) (G : E → Set F) : E × F → EReal :=
  fun p ↦ φ p + (graph G).convex_indicator p


/-- `φ` restricted to `gph G`: `φ` on the graph and `⊤` off it. It agrees with
`ϑ = φ + δ_{gph G}` wherever `φ ≠ ⊥` (`graphRestrict_eq_marginalPenalty`). -/
noncomputable def graphRestrict (φ : E × F → EReal) (G : E → Set F) : E × F → EReal :=
  open scoped Classical in fun p ↦ if p ∈ graph G then φ p else ⊤

/-- The projection `((x, y), α) ↦ (x, α)` of `(E × F) × ℝ` onto `E × ℝ`. -/
noncomputable def epiProj : (E × F) × ℝ →L[ℝ] E × ℝ :=
  (ContinuousLinearMap.fst ℝ E F).prodMap (ContinuousLinearMap.id ℝ ℝ)

section Restrict

variable {φ : E × F → EReal} {G : E → Set F} {x₀ : E} {y₀ : F} {r : ℝ}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem graphRestrict_of_mem {p : E × F} (hp : p ∈ graph G) : graphRestrict φ G p = φ p :=
  if_pos hp

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem graphRestrict_eq_marginalPenalty {p : E × F} (h : φ p ≠ ⊥) :
    graphRestrict φ G p = marginalPenalty φ G p := by
  by_cases hp : p ∈ graph G
  · simp [graphRestrict, marginalPenalty, hp, convex_indicator_of_mem hp]
  · simp [graphRestrict, marginalPenalty, hp, convex_indicator_of_notMem hp,
      EReal.add_top_of_ne_bot h]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Near a point where `φ` is lower semicontinuous and finite, `ϑ` is `φ` restricted to the
graph. -/
theorem graphRestrict_eventuallyEq (hr : φ (x₀, y₀) = r)
    (hl : LowerSemicontinuousAt φ (x₀, y₀)) :
    graphRestrict φ G =ᶠ[𝓝 (x₀, y₀)] marginalPenalty φ G := by
  filter_upwards [hl ⊥ (show ⊥ < φ (x₀, y₀) by rw [hr]; exact EReal.bot_lt_coe r)] with p hp
  exact graphRestrict_eq_marginalPenalty hp.ne'

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem marginal_le_graphRestrict (p : E × F) : marginal φ G p.1 ≤ graphRestrict φ G p := by
  by_cases hp : p ∈ graph G
  · rw [graphRestrict_of_mem hp]
    exact marginal_le hp
  · simp [graphRestrict, hp]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem graphRestrict_eq_marginal {x : E} {y : F} (hy : y ∈ argminMap φ G x) :
    graphRestrict φ G (x, y) = marginal φ G x := by
  rw [graphRestrict_of_mem (show (x, y) ∈ graph G from hy.1), hy.2]

@[simp] theorem epiProj_apply (p : (E × F) × ℝ) : (epiProj p : E × ℝ) = (p.1.1, p.2) := rfl

/-- `epiProj` maps `epi ϑ` into `epi μ`. -/
theorem mapsTo_epiProj : MapsTo (epiProj : (E × F) × ℝ → E × ℝ) ((graphRestrict φ G).Epi univ)
    ((marginal φ G).Epi univ) :=
  fun p hp ↦ ⟨mem_univ _, (marginal_le_graphRestrict p.1).trans hp.2⟩

theorem coprod_comp_epiProj (u : StrongDual ℝ E) (c : StrongDual ℝ ℝ) :
    (u.coprod c).comp (epiProj : (E × F) × ℝ →L[ℝ] E × ℝ) = (u.coprod 0).coprod c := by
  ext <;> simp [epiProj]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- A function lower semicontinuous on a neighborhood of `z` is lower semicontinuous at `z`. -/
theorem lowerSemicontinuousAt_of_lowerSemicontinuousOn {X : Type*} [TopologicalSpace X]
    {f : X → EReal} {z : X} {U : Set X} (hU : U ∈ 𝓝 z) (h : LowerSemicontinuousOn f U) :
    LowerSemicontinuousAt f z := fun c hc ↦ by
  have := lowerSemicontinuousWithinAt_iff.1 (h z (mem_of_mem_nhds hU)) c hc
  rwa [nhdsWithin_eq_nhds.2 hU] at this

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- If `f` is lower semicontinuous at `z`, `zₖ → z` and `f zₖ → t`, then `f z ≤ t`. -/
theorem le_of_tendsto_of_lowerSemicontinuousAt {X : Type*} [TopologicalSpace X] {f : X → EReal}
    {z : X} {t : EReal} (hf : LowerSemicontinuousAt f z) {a : ℕ → X}
    (ha : Tendsto a atTop (𝓝 z)) (ht : Tendsto (fun k ↦ f (a k)) atTop (𝓝 t)) : f z ≤ t :=
  le_of_forall_lt_imp_le_of_dense fun c hc ↦
    ge_of_tendsto ht ((ha.eventually (hf c hc)).mono fun _ hk ↦ hk.le)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- The sequences behind a normal `ℓ` to `epi μ` at `(x₀, μ x₀)`: base points `(xₖ, αₖ)` with
`xₖ →μ x₀` and `αₖ → μ x₀`, and regular normals `ℓₖ → ℓ` at them. The convergence `xₖ →μ x₀`
holds when `ℓ` is slanted (`ℓ (0, 1) < 0`, then `αₖ = μ xₖ` by Exercise 1.62) or when `μ` is
lower semicontinuous at `x₀`. -/
theorem exists_seq_of_mem_normalCone_epi_marginal (hr : marginal φ G x₀ = r)
    {ℓ : StrongDual ℝ (E × ℝ)} (hℓ : ℓ ∈ normalCone ((marginal φ G).Epi univ) (x₀, r))
    (h : ℓ (0, 1) < 0 ∨ LowerSemicontinuousAt (marginal φ G) x₀) :
    ∃ p : ℕ → E × ℝ, ∃ ℓs : ℕ → StrongDual ℝ (E × ℝ),
      Tendsto (fun k ↦ (p k).1) atTop (funNhds (marginal φ G) x₀) ∧
      Tendsto (fun k ↦ (p k).2) atTop (𝓝 r) ∧ Tendsto ℓs atTop (𝓝 ℓ) ∧
      ∀ k, ℓs k ∈ regularNormalCone ((marginal φ G).Epi univ) (p k) := by
  obtain ⟨-, p, ℓs, hp, hℓs, hmem⟩ := hℓ
  have hp' := (tendsto_nhdsWithin_iff.1 hp).1
  have hx : Tendsto (fun k ↦ (p k).1) atTop (𝓝 x₀) := (continuous_fst.tendsto _).comp hp'
  have hα : Tendsto (fun k ↦ (p k).2) atTop (𝓝 r) := (continuous_snd.tendsto _).comp hp'
  have hepi : ∀ k, marginal φ G (p k).1 ≤ (p k).2 := fun k ↦ (hmem k).1.2
  have hμ : Tendsto (fun k ↦ marginal φ G (p k).1) atTop (𝓝 (r : EReal)) := by
    rcases h with h | h
    · have h01 : Tendsto (fun k ↦ ℓs k (0, 1)) atTop (𝓝 (ℓ (0, 1))) :=
        tendsto_dual_apply hℓs tendsto_const_nhds
      have hneg : ∀ᶠ k in atTop, ℓs k (0, 1) < 0 := (tendsto_order.1 h01).2 0 h
      have heq : ∀ᶠ k in atTop, marginal φ G (p k).1 = (p k).2 := hneg.mono fun k hk ↦
        eq_of_mem_regularNormalCone_epi (by simpa using hmem k) hk
      exact ((continuous_coe_real_ereal.tendsto r).comp hα).congr'
        (heq.mono fun k hk ↦ hk.symm)
    · refine tendsto_order.2 ⟨fun a ha ↦ hx.eventually
        (h a (show a < marginal φ G x₀ by rw [hr]; exact ha)), fun b hb ↦ ?_⟩
      filter_upwards [(tendsto_order.1 (EReal.tendsto_coe.2 hα)).2 b hb] with k hk
      exact (hepi k).trans_lt hk
  exact ⟨p, ℓs, tendsto_funNhds_iff.2 ⟨hx, by rw [hr]; exact hμ⟩, hα, hℓs, hmem⟩

/-- Lifting normals from `epi μ` to `epi ϑ` [Mordukhovich 2018, proof of Thm. 4.1]: if regular
normals `ℓₖ → ℓ` to `epi μ` at `(xₖ, αₖ) → (x₀, r)` come with `yₖ ∈ M(xₖ)` with `yₖ → y₀ ∈ M(x₀)`,
then `ℓ ∘ epiProj` is a normal to `epi ϑ` at `((x₀, y₀), r)`. -/
theorem comp_epiProj_mem_normalCone_epi_of_seq (hr : marginal φ G x₀ = r)
    (hy₀ : y₀ ∈ argminMap φ G x₀) {ℓ : StrongDual ℝ (E × ℝ)} {p : ℕ → E × ℝ}
    {ℓs : ℕ → StrongDual ℝ (E × ℝ)} (hx : Tendsto (fun k ↦ (p k).1) atTop (𝓝 x₀))
    (hα : Tendsto (fun k ↦ (p k).2) atTop (𝓝 r)) (hℓs : Tendsto ℓs atTop (𝓝 ℓ))
    (hmem : ∀ k, ℓs k ∈ regularNormalCone ((marginal φ G).Epi univ) (p k)) {y : ℕ → F}
    (hy : Tendsto y atTop (𝓝 y₀)) (hyM : ∀ᶠ k in atTop, y k ∈ argminMap φ G (p k).1) :
    ℓ.comp epiProj ∈ normalCone ((graphRestrict φ G).Epi univ) ((x₀, y₀), r) := by
  have hepi : ∀ k, marginal φ G (p k).1 ≤ (p k).2 := fun k ↦ (hmem k).1.2
  have hbase : ((x₀, y₀), r) ∈ (graphRestrict φ G).Epi univ :=
    ⟨mem_univ _, ((graphRestrict_eq_marginal hy₀).trans hr).le⟩
  have hq : ∀ k, y k ∈ argminMap φ G (p k).1 →
      (((p k).1, y k), (p k).2) ∈ (graphRestrict φ G).Epi univ := fun k hk ↦
    ⟨mem_univ _, (graphRestrict_eq_marginal hk).trans_le (hepi k)⟩
  have hT : Tendsto (fun k ↦ (((p k).1, y k), (p k).2)) atTop
      (𝓝[(graphRestrict φ G).Epi univ] ((x₀, y₀), r)) :=
    tendsto_nhdsWithin_iff.2 ⟨(hx.prodMk_nhds hy).prodMk_nhds hα, hyM.mono hq⟩
  have hL : Tendsto (fun k ↦ (ℓs k).comp (epiProj : (E × F) × ℝ →L[ℝ] E × ℝ)) atTop
      (𝓝 (ℓ.comp epiProj)) :=
    ((((epiProj : (E × F) × ℝ →L[ℝ] E × ℝ).precomp ℝ).continuous.tendsto ℓ).comp hℓs)
  have hN : ∀ k, y k ∈ argminMap φ G (p k).1 → (ℓs k).comp epiProj ∈
      regularNormalCone ((graphRestrict φ G).Epi univ) (((p k).1, y k), (p k).2) := by
    intro k hk
    have he : (epiProj : (E × F) × ℝ →L[ℝ] E × ℝ) (((p k).1, y k), (p k).2) = p k := by
      rw [epiProj_apply]
    have h2 := hmem k
    rw [← he] at h2
    exact comp_mem_regularNormalCone_of_mapsTo (epiProj (E := E) (F := F)) mapsTo_epiProj
      (hq k hk) h2
  exact ⟨hbase, mem_outerLimit_of_eventually _ _ hT hL (hyM.mono hN)⟩

/-- The key step of the proof of [Mordukhovich 2018, Thm. 4.1(i)], in geometric form: under the
`μ`-inner semicontinuity of `M` at `(x₀, y₀)`, a normal `ℓ` to `epi μ` at `(x₀, μ x₀)` gives the
normal `ℓ ∘ epiProj` to `epi ϑ` at `((x₀, y₀), μ x₀)`, provided `ℓ` is slanted (`ℓ (0, 1) < 0`)
or `μ` is lower semicontinuous at `x₀`. -/
theorem comp_epiProj_mem_normalCone_epi (hr : marginal φ G x₀ = r)
    (hy₀ : y₀ ∈ argminMap φ G x₀)
    (hisc : y₀ ∈ innerLimit (funNhds (marginal φ G) x₀) (argminMap φ G))
    {ℓ : StrongDual ℝ (E × ℝ)} (hℓ : ℓ ∈ normalCone ((marginal φ G).Epi univ) (x₀, r))
    (h : ℓ (0, 1) < 0 ∨ LowerSemicontinuousAt (marginal φ G) x₀) :
    ℓ.comp epiProj ∈ normalCone ((graphRestrict φ G).Epi univ) ((x₀, y₀), r) := by
  obtain ⟨p, ℓs, hx, hα, hℓs, hmem⟩ := exists_seq_of_mem_normalCone_epi_marginal hr hℓ h
  obtain ⟨y, hy, hyM⟩ := hisc _ hx
  exact comp_epiProj_mem_normalCone_epi_of_seq hr hy₀ (tendsto_funNhds_iff.1 hx).1 hα hℓs hmem
    hy hyM

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem graphRestrict_apply_eq (hr : marginal φ G x₀ = r) (hy₀ : y₀ ∈ argminMap φ G x₀) :
    graphRestrict φ G (x₀, y₀) = r :=
  (graphRestrict_eq_marginal hy₀).trans hr

/-- [Mordukhovich 2018, proof of Thm. 4.1(i)]: `x ∈ ∂μ(x₀)` implies `(x, 0) ∈ ∂ϑ(x₀, y₀)`, with
`ϑ` written as `φ` restricted to `gph G`. -/
theorem coprod_zero_mem_subdiff_graphRestrict (hr : marginal φ G x₀ = r)
    (hy₀ : y₀ ∈ argminMap φ G x₀)
    (hisc : y₀ ∈ innerLimit (funNhds (marginal φ G) x₀) (argminMap φ G)) {x : StrongDual ℝ E}
    (hx : x ∈ subdiff (marginal φ G) x₀) :
    x.coprod (0 : StrongDual ℝ F) ∈ subdiff (graphRestrict φ G) (x₀, y₀) := by
  rw [mem_subdiff_iff hr] at hx
  rw [mem_subdiff_iff (graphRestrict_apply_eq hr hy₀), ← coprod_comp_epiProj]
  exact comp_epiProj_mem_normalCone_epi hr hy₀ hisc hx (Or.inl (by simp))

/-- [Mordukhovich 2018, proof of Thm. 4.1(i)]: if moreover `μ` is lower semicontinuous at `x₀`,
`x ∈ ∂^∞μ(x₀)` implies `(x, 0) ∈ ∂^∞ϑ(x₀, y₀)`. -/
theorem coprod_zero_mem_singularSubdiff_graphRestrict (hr : marginal φ G x₀ = r)
    (hy₀ : y₀ ∈ argminMap φ G x₀)
    (hisc : y₀ ∈ innerLimit (funNhds (marginal φ G) x₀) (argminMap φ G))
    (hlsc : LowerSemicontinuousAt (marginal φ G) x₀) {x : StrongDual ℝ E}
    (hx : x ∈ singularSubdiff (marginal φ G) x₀) :
    x.coprod (0 : StrongDual ℝ F) ∈ singularSubdiff (graphRestrict φ G) (x₀, y₀) := by
  rw [mem_singularSubdiff_iff hr] at hx
  rw [mem_singularSubdiff_iff (graphRestrict_apply_eq hr hy₀), ← coprod_comp_epiProj]
  exact comp_epiProj_mem_normalCone_epi hr hy₀ hisc hx (Or.inr hlsc)

/-- Regular version of the key step of [Mordukhovich 2018, proof of Thm. 4.1(i)]:
`x ∈ ∂̂μ(x₀)` implies `(x, 0) ∈ ∂̂ϑ(x₀, y₀)` for every `y₀ ∈ M(x₀)`. -/
theorem coprod_zero_mem_regularSubdiff_graphRestrict (hy₀ : y₀ ∈ argminMap φ G x₀)
    {x : StrongDual ℝ E} (hx : x ∈ regularSubdiff (marginal φ G) x₀) :
    x.coprod (0 : StrongDual ℝ F) ∈ regularSubdiff (graphRestrict φ G) (x₀, y₀) := by
  obtain ⟨r, hr, h⟩ := hx
  refine ⟨r, graphRestrict_apply_eq hr hy₀, fun ε hε ↦ ?_⟩
  have hfst : Tendsto Prod.fst (𝓝 (x₀, y₀)) (𝓝 x₀) := continuous_fst.tendsto _
  filter_upwards [hfst.eventually (h ε hε)] with p hp
  refine le_trans (EReal.coe_le_coe_iff.2 ?_) (hp.trans (marginal_le_graphRestrict p))
  have hn : ‖p.1 - x₀‖ ≤ ‖p - (x₀, y₀)‖ := by
    simpa using norm_fst_le (p - (x₀, y₀))
  simp only [ContinuousLinearMap.coprod_apply, Prod.fst_sub, Prod.snd_sub,
    zero_apply, add_zero]
  nlinarith

end Restrict

section Semicontinuity

variable {φ : E × F → EReal} {G : E → Set F} {x₀ : E} {y₀ : F} {r : ℝ}

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Inner semicontinuity of the argminimum mapping at `(x₀, y₀)` [Mordukhovich 2018, Thm. 4.1(i)]
gives `μ`-inner semicontinuity when the infimum in (4.1) is attained near `x₀` wherever it is
finite from above (`dom μ ⊆ dom M` near `x₀`). -/
theorem mem_innerLimit_funNhds_of_innerSemicontinuousAt (hr : marginal φ G x₀ = r)
    (hisc : InnerSemicontinuousAt (argminMap φ G) x₀ y₀)
    (hatt : ∀ᶠ x in 𝓝 x₀, marginal φ G x ≠ ⊤ → (argminMap φ G x).Nonempty) :
    y₀ ∈ innerLimit (funNhds (marginal φ G) x₀) (argminMap φ G) := by
  intro a ha
  obtain ⟨ha1, ha2⟩ := tendsto_funNhds_iff.1 ha
  rw [hr] at ha2
  have hne : ∀ᶠ k in atTop, marginal φ G (a k) ≠ ⊤ :=
    ((tendsto_order.1 ha2).2 ⊤ (EReal.coe_lt_top r)).mono fun _ hk ↦ hk.ne
  exact hisc a (tendsto_nhdsWithin_iff.2
    ⟨ha1, (hne.and (ha1.eventually hatt)).mono fun _ hk ↦ hk.2 hk.1⟩)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Under the assumptions of `mem_innerLimit_funNhds_of_innerSemicontinuousAt` and the lower
semicontinuity of `φ` at `(x₀, y₀)`, the marginal function is lower semicontinuous at `x₀`. -/
theorem lowerSemicontinuousAt_marginal_of_innerSemicontinuousAt (hy₀ : y₀ ∈ argminMap φ G x₀)
    (hisc : InnerSemicontinuousAt (argminMap φ G) x₀ y₀)
    (hatt : ∀ᶠ x in 𝓝 x₀, marginal φ G x ≠ ⊤ → (argminMap φ G x).Nonempty)
    (hlφ : LowerSemicontinuousAt φ (x₀, y₀)) : LowerSemicontinuousAt (marginal φ G) x₀ := by
  intro c hc
  by_contra hcon
  obtain ⟨a, ha, hac⟩ := exists_seq_forall_of_frequently (not_eventually.1 hcon)
  have hle : ∀ k, marginal φ G (a k) ≤ c := fun k ↦ not_lt.1 (hac k)
  have hdom : Tendsto a atTop (𝓝[dom (argminMap φ G)] x₀) :=
    tendsto_nhdsWithin_iff.2 ⟨ha, (ha.eventually hatt).mono fun k hk ↦
      hk (ne_top_of_le_ne_top (ne_top_of_lt hc) (hle k))⟩
  obtain ⟨v, hv, hvM⟩ := hisc a hdom
  have hc' : c < φ (x₀, y₀) := by rw [hy₀.2]; exact hc
  obtain ⟨k, hk1, hk2⟩ := (((ha.prodMk_nhds hv).eventually (hlφ c hc')).and hvM).exists
  rw [hk2.2] at hk1
  exact absurd hk1 (not_lt.2 (hle k))

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Bolzano–Weierstrass for a locally bounded mapping: along `aₖ → x₀` with `S(aₖ) ≠ ∅` for all
large `k`, there are `yₖ ∈ S(aₖ)` (for all large `k`) with a convergent subsequence. -/
theorem exists_subseq_of_locallyBoundedAt [ProperSpace F] {S : E → Set F}
    (hlb : LocallyBoundedAt S x₀) {a : ℕ → E} (ha : Tendsto a atTop (𝓝 x₀))
    (hne : ∀ᶠ k in atTop, (S (a k)).Nonempty) :
    ∃ y : ℕ → F, ∃ z : F, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (y ∘ ψ) atTop (𝓝 z) ∧
      ∀ᶠ k in atTop, y k ∈ S (a k) := by
  classical
  obtain ⟨U, hU, hB⟩ := hlb
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hne.and (ha.eventually hU))
  obtain ⟨w, hw⟩ := (hN N le_rfl).1
  set y : ℕ → F := fun k ↦ if h : (S (a k)).Nonempty ∧ a k ∈ U then h.1.some else w
  have hyB : ∀ k, y k ∈ ⋃ x ∈ U, S x := fun k ↦ by
    by_cases h : (S (a k)).Nonempty ∧ a k ∈ U
    · simp only [y, dif_pos h]; exact mem_biUnion h.2 h.1.some_mem
    · simp only [y, dif_neg h]; exact mem_biUnion (hN N le_rfl).2 hw
  obtain ⟨z, -, ψ, hψ, hlim⟩ := tendsto_subseq_of_bounded hB hyB
  refine ⟨y, z, ψ, hψ, hlim, eventually_atTop.2 ⟨N, fun k hk ↦ ?_⟩⟩
  have h : (S (a k)).Nonempty ∧ a k ∈ U := hN k hk
  simp only [y]
  rw [dif_pos h]
  exact h.1.some_mem

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Limits of argminima: if `aₖ → x₀`, `μ(aₖ) → μ(x₀)`, `yₖ ∈ M(aₖ)` for all large `k` and
`yₖ → z`, then `z ∈ M(x₀)`, provided `gph G` is closed and `φ` is lower semicontinuous at
`(x₀, y)` for every `y ∈ G x₀`. -/
theorem mem_argminMap_of_tendsto (hG : IsClosed (graph G))
    (hlφ : ∀ y ∈ G x₀, LowerSemicontinuousAt φ (x₀, y)) {a : ℕ → E} {y : ℕ → F} {z : F}
    (ha : Tendsto a atTop (funNhds (marginal φ G) x₀)) (hy : Tendsto y atTop (𝓝 z))
    (hyM : ∀ᶠ k in atTop, y k ∈ argminMap φ G (a k)) : z ∈ argminMap φ G x₀ := by
  obtain ⟨ha1, ha2⟩ := tendsto_funNhds_iff.1 ha
  have hzG : z ∈ G x₀ := hG.mem_of_tendsto (ha1.prodMk_nhds hy) (hyM.mono fun _ hk ↦ hk.1)
  refine ⟨hzG, le_antisymm ?_ (marginal_le hzG)⟩
  exact le_of_tendsto_of_lowerSemicontinuousAt (hlφ z hzG) (ha1.prodMk_nhds hy)
    (ha2.congr' (hyM.mono fun _ hk ↦ hk.2.symm))

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Under local boundedness of the argminimum mapping, attainment of the infimum near `x₀`, a
closed `gph G` and the lower semicontinuity of `φ` at the points `(x₀, y)`, `y ∈ G x₀`, the
marginal function is lower semicontinuous at `x₀`. -/
theorem lowerSemicontinuousAt_marginal_of_locallyBoundedAt [ProperSpace F]
    (hlb : LocallyBoundedAt (argminMap φ G) x₀)
    (hatt : ∀ᶠ x in 𝓝 x₀, marginal φ G x ≠ ⊤ → (argminMap φ G x).Nonempty)
    (hG : IsClosed (graph G)) (hlφ : ∀ y ∈ G x₀, LowerSemicontinuousAt φ (x₀, y)) :
    LowerSemicontinuousAt (marginal φ G) x₀ := by
  intro c hc
  by_contra hcon
  obtain ⟨a, ha, hac⟩ := exists_seq_forall_of_frequently (not_eventually.1 hcon)
  have hle : ∀ k, marginal φ G (a k) ≤ c := fun k ↦ not_lt.1 (hac k)
  obtain ⟨y, z, ψ, hψ, hlim, hyM⟩ := exists_subseq_of_locallyBoundedAt hlb ha
    ((ha.eventually hatt).mono fun k hk ↦ hk (ne_top_of_le_ne_top (ne_top_of_lt hc) (hle k)))
  have haψ : Tendsto (a ∘ ψ) atTop (𝓝 x₀) := ha.comp hψ.tendsto_atTop
  have hyMψ : ∀ᶠ k in atTop, (y ∘ ψ) k ∈ argminMap φ G ((a ∘ ψ) k) :=
    hψ.tendsto_atTop.eventually hyM
  have hzG : z ∈ G x₀ := hG.mem_of_tendsto (haψ.prodMk_nhds hlim) (hyMψ.mono fun _ hk ↦ hk.1)
  have hc' : c < φ (x₀, z) := hc.trans_le (marginal_le hzG)
  obtain ⟨k, hk1, hk2⟩ := (((haψ.prodMk_nhds hlim).eventually (hlφ z hzG c hc')).and hyMψ).exists
  rw [hk2.2] at hk1
  exact absurd hk1 (not_lt.2 (hle _))

/-- The key step of [Mordukhovich 2018, proof of Thm. 4.1(ii)]: under local boundedness of `M`,
a normal `ℓ` to `epi μ` at `(x₀, μ x₀)` gives the normal `ℓ ∘ epiProj` to `epi ϑ` at
`((x₀, y₀), μ x₀)` for some `y₀ ∈ M(x₀)`, provided `ℓ` is slanted or `μ` is lower semicontinuous
at `x₀`. -/
theorem exists_comp_epiProj_mem_normalCone_epi_of_locallyBoundedAt [ProperSpace F]
    (hr : marginal φ G x₀ = r) (hlb : LocallyBoundedAt (argminMap φ G) x₀)
    (hatt : ∀ᶠ x in 𝓝 x₀, marginal φ G x ≠ ⊤ → (argminMap φ G x).Nonempty)
    (hG : IsClosed (graph G)) (hlφ : ∀ y ∈ G x₀, LowerSemicontinuousAt φ (x₀, y))
    {ℓ : StrongDual ℝ (E × ℝ)} (hℓ : ℓ ∈ normalCone ((marginal φ G).Epi univ) (x₀, r))
    (h : ℓ (0, 1) < 0 ∨ LowerSemicontinuousAt (marginal φ G) x₀) :
    ∃ y₀ ∈ argminMap φ G x₀,
      ℓ.comp epiProj ∈ normalCone ((graphRestrict φ G).Epi univ) ((x₀, y₀), r) := by
  obtain ⟨p, ℓs, hx, hα, hℓs, hmem⟩ := exists_seq_of_mem_normalCone_epi_marginal hr hℓ h
  obtain ⟨hx1, hx2⟩ := tendsto_funNhds_iff.1 hx
  have hne : ∀ᶠ k in atTop, marginal φ G (p k).1 ≠ ⊤ := by
    rw [hr] at hx2
    exact ((tendsto_order.1 hx2).2 ⊤ (EReal.coe_lt_top r)).mono fun _ hk ↦ hk.ne
  obtain ⟨y, z, ψ, hψ, hlim, hyM⟩ := exists_subseq_of_locallyBoundedAt hlb hx1
    ((hne.and (hx1.eventually hatt)).mono fun _ hk ↦ hk.2 hk.1)
  have hψ' := hψ.tendsto_atTop
  have hz : z ∈ argminMap φ G x₀ :=
    mem_argminMap_of_tendsto (a := fun k ↦ (p (ψ k)).1) hG hlφ (hx.comp hψ') hlim
      (hψ'.eventually hyM)
  exact ⟨z, hz, comp_epiProj_mem_normalCone_epi_of_seq (p := p ∘ ψ) (ℓs := ℓs ∘ ψ) hr hz
    (hx1.comp hψ') (hα.comp hψ') (hℓs.comp hψ') (fun k ↦ hmem (ψ k)) hlim (hψ'.eventually hyM)⟩

end Semicontinuity

section Penalty

variable {φ : E × F → EReal} {G : E → Set F} {x₀ : E} {y₀ : F} {r : ℝ}

/-- `(x, 0) ∈ ∂ϑ(x₀, y₀)` for every `x ∈ ∂μ(x₀)`: the first estimate in the proof of
[Mordukhovich 2018, Thm. 4.1(i)], under the `μ`-inner semicontinuity of the argminimum mapping
at `(x₀, y₀)` and the lower semicontinuity of `φ` at `(x₀, y₀)`. -/
theorem subdiff_marginal_subset_penalty (hr : marginal φ G x₀ = r)
    (hy₀ : y₀ ∈ argminMap φ G x₀)
    (hisc : y₀ ∈ innerLimit (funNhds (marginal φ G) x₀) (argminMap φ G))
    (hlφ : LowerSemicontinuousAt φ (x₀, y₀)) :
    subdiff (marginal φ G) x₀ ⊆
      {x | x.coprod (0 : StrongDual ℝ F) ∈ subdiff (marginalPenalty φ G) (x₀, y₀)} := by
  intro x hx
  rw [mem_ofPred_eq, ← subdiff_congr (graphRestrict_eventuallyEq (hy₀.2.trans hr) hlφ)]
  exact coprod_zero_mem_subdiff_graphRestrict hr hy₀ hisc hx

/-- `(x, 0) ∈ ∂^∞ϑ(x₀, y₀)` for every `x ∈ ∂^∞μ(x₀)`: the second estimate in the proof of
[Mordukhovich 2018, Thm. 4.1(i)]. Besides the assumptions of `subdiff_marginal_subset_penalty`,
this needs `μ` lower semicontinuous at `x₀` (see the module docstring). -/
theorem singularSubdiff_marginal_subset_penalty (hr : marginal φ G x₀ = r)
    (hy₀ : y₀ ∈ argminMap φ G x₀)
    (hisc : y₀ ∈ innerLimit (funNhds (marginal φ G) x₀) (argminMap φ G))
    (hlφ : LowerSemicontinuousAt φ (x₀, y₀)) (hlsc : LowerSemicontinuousAt (marginal φ G) x₀) :
    singularSubdiff (marginal φ G) x₀ ⊆
      {x | x.coprod (0 : StrongDual ℝ F) ∈ singularSubdiff (marginalPenalty φ G) (x₀, y₀)} := by
  intro x hx
  rw [mem_ofPred_eq, ← singularSubdiff_congr (graphRestrict_eventuallyEq (hy₀.2.trans hr) hlφ)]
  exact coprod_zero_mem_singularSubdiff_graphRestrict hr hy₀ hisc hlsc hx

omit [NormedSpace ℝ E] in
/-- The epigraph of the indicator function of a set locally closed around `x₀` is locally closed
around `(x₀, 0)`. -/
theorem locallyClosed_epi_convex_indicator {Ω : Set E} {x₀ : E}
    (h : ∃ ρ > 0, IsClosed (Ω ∩ closedBall x₀ ρ)) :
    ∃ ρ > 0, IsClosed (Ω.convex_indicator.Epi univ ∩ closedBall ((x₀, 0) : E × ℝ) ρ) := by
  obtain ⟨ρ, hρ, hc⟩ := h
  refine ⟨ρ, hρ, ?_⟩
  rw [epi_convex_indicator, ← closedBall_prod_same, prod_inter_prod]
  exact hc.prod (isClosed_Ici.inter isClosed_closedBall)

/-- Splitting `(x, 0) = (u, v) + (x - u, -v)` with `(x - u, -v) ∈ N((x₀, y₀); gph G)`. -/
theorem exists_coprod_of_mem_add_normalCone_graph {A : Set (StrongDual ℝ (E × F))}
    {x : StrongDual ℝ E} (h : x.coprod (0 : StrongDual ℝ F) ∈ A + normalCone (graph G) (x₀, y₀)) :
    ∃ u v, u.coprod v ∈ A ∧ x - u ∈ coderiv G x₀ y₀ v := by
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.1 h
  refine ⟨a.comp (ContinuousLinearMap.inl ℝ E F), a.comp (ContinuousLinearMap.inr ℝ E F),
    by rwa [ContinuousLinearMap.coprod_comp_inl_inr], ?_⟩
  have hb' : b = x.coprod 0 - a := eq_sub_of_add_eq' hab
  change _ ∈ normalCone _ _
  convert hb using 1
  rw [hb']
  ext z <;> simp

end Penalty

section SumRule

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
variable {φ : E × F → EReal} {G : E → Set F} {x₀ : E} {y₀ : F} {r : ℝ}

/-- The last step of the proof of [Mordukhovich 2018, Thm. 4.1(i)]: the sum rule (Thm. 2.19)
applied to `ϑ = φ + δ_{gph G}` under (4.3) turns `(x, 0) ∈ ∂ϑ(x₀, y₀)` into
`x ∈ u + D*G(x₀, y₀)(v)` with `(u, v) ∈ ∂φ(x₀, y₀)`. -/
theorem exists_coprod_of_mem_subdiff_graphRestrict (hr' : φ (x₀, y₀) = r) (hy₀ : y₀ ∈ G x₀)
    (hφ : ∃ ρ > 0, IsClosed (φ.Epi univ ∩ closedBall (((x₀, y₀), r) : (E × F) × ℝ) ρ))
    (hG : ∃ ρ > 0, IsClosed (graph G ∩ closedBall (x₀, y₀) ρ))
    (hqc : ∀ w ∈ singularSubdiff φ (x₀, y₀), -w ∈ normalCone (graph G) (x₀, y₀) → w = 0)
    {x : StrongDual ℝ E}
    (hx : x.coprod (0 : StrongDual ℝ F) ∈ subdiff (graphRestrict φ G) (x₀, y₀)) :
    ∃ u v, u.coprod v ∈ subdiff φ (x₀, y₀) ∧ x - u ∈ coderiv G x₀ y₀ v := by
  rw [subdiff_congr (graphRestrict_eventuallyEq hr'
    (lowerSemicontinuousAt_of_locallyClosed_epi hr' hφ))] at hx
  have h2 := subdiff_add_subset (φ₂ := (graph G).convex_indicator) hr'
    (convex_indicator_of_mem (show (x₀, y₀) ∈ graph G from hy₀)) hφ
    (locallyClosed_epi_convex_indicator hG) (by simpa [singularSubdiff_convex_indicator] using hqc)
    hx
  rw [subdiff_convex_indicator] at h2
  exact exists_coprod_of_mem_add_normalCone_graph h2

/-- The singular counterpart of `exists_coprod_of_mem_subdiff_graphRestrict` (Thm. 2.19, (2.36)). -/
theorem exists_coprod_of_mem_singularSubdiff_graphRestrict (hr' : φ (x₀, y₀) = r)
    (hy₀ : y₀ ∈ G x₀)
    (hφ : ∃ ρ > 0, IsClosed (φ.Epi univ ∩ closedBall (((x₀, y₀), r) : (E × F) × ℝ) ρ))
    (hG : ∃ ρ > 0, IsClosed (graph G ∩ closedBall (x₀, y₀) ρ))
    (hqc : ∀ w ∈ singularSubdiff φ (x₀, y₀), -w ∈ normalCone (graph G) (x₀, y₀) → w = 0)
    {x : StrongDual ℝ E}
    (hx : x.coprod (0 : StrongDual ℝ F) ∈ singularSubdiff (graphRestrict φ G) (x₀, y₀)) :
    ∃ u v, u.coprod v ∈ singularSubdiff φ (x₀, y₀) ∧ x - u ∈ coderiv G x₀ y₀ v := by
  rw [singularSubdiff_congr (graphRestrict_eventuallyEq hr'
    (lowerSemicontinuousAt_of_locallyClosed_epi hr' hφ))] at hx
  have h2 := singularSubdiff_add_subset (φ₂ := (graph G).convex_indicator) hr'
    (convex_indicator_of_mem (show (x₀, y₀) ∈ graph G from hy₀)) hφ
    (locallyClosed_epi_convex_indicator hG) (by simpa [singularSubdiff_convex_indicator] using hqc)
    hx
  rw [singularSubdiff_convex_indicator] at h2
  exact exists_coprod_of_mem_add_normalCone_graph h2

/-- Thm. 4.1(i) of [Mordukhovich 2018], (4.4) (basic subgradients of marginal functions): let
`μ x₀ = r` be finite, `y₀ ∈ M(x₀)`, let the epigraph of `φ` be locally closed around
`((x₀, y₀), r)` (e.g. `φ` l.s.c. around `(x₀, y₀)`), let `gph G` be locally closed around
`(x₀, y₀)`, and assume the qualification condition (4.3)
`∂^∞φ(x₀, y₀) ∩ (-N((x₀, y₀); gph G)) = {0}`. If `M` is `μ`-inner semicontinuous at `(x₀, y₀)`
(`y₀ ∈ Lim inf_{x →μ x₀} M(x)`), then
`∂μ(x₀) ⊆ ⋃_{(u, v) ∈ ∂φ(x₀, y₀)} [u + D*G(x₀, y₀)(v)]`.

The book assumes that `M` is inner semicontinuous at `(x₀, y₀)` and uses sequences `x →μ x₀`;
`subdiff_marginal_subset_of_innerSemicontinuousAt` is that version. -/
theorem subdiff_marginal_subset (hr : marginal φ G x₀ = r) (hy₀ : y₀ ∈ argminMap φ G x₀)
    (hisc : y₀ ∈ innerLimit (funNhds (marginal φ G) x₀) (argminMap φ G))
    (hφ : ∃ ρ > 0, IsClosed (φ.Epi univ ∩ closedBall (((x₀, y₀), r) : (E × F) × ℝ) ρ))
    (hG : ∃ ρ > 0, IsClosed (graph G ∩ closedBall (x₀, y₀) ρ))
    (hqc : ∀ w ∈ singularSubdiff φ (x₀, y₀), -w ∈ normalCone (graph G) (x₀, y₀) → w = 0) :
    subdiff (marginal φ G) x₀ ⊆
      {x | ∃ u v, u.coprod v ∈ subdiff φ (x₀, y₀) ∧ x - u ∈ coderiv G x₀ y₀ v} :=
  fun _ hx ↦ exists_coprod_of_mem_subdiff_graphRestrict (hy₀.2.trans hr) hy₀.1 hφ hG hqc
    (coprod_zero_mem_subdiff_graphRestrict hr hy₀ hisc hx)

/-- Thm. 4.1(i) of [Mordukhovich 2018], (4.5) (singular subgradients of marginal functions):
under the assumptions of `subdiff_marginal_subset`, if moreover `μ` is lower semicontinuous at
`x₀`, then `∂^∞μ(x₀) ⊆ ⋃_{(u, v) ∈ ∂^∞φ(x₀, y₀)} [u + D*G(x₀, y₀)(v)]`. The lower
semicontinuity of `μ` cannot be dropped when `M` is only `μ`-inner semicontinuous (see the module
docstring); it holds under the book's inner semicontinuity
(`lowerSemicontinuousAt_marginal_of_innerSemicontinuousAt`). -/
theorem singularSubdiff_marginal_subset (hr : marginal φ G x₀ = r)
    (hy₀ : y₀ ∈ argminMap φ G x₀)
    (hisc : y₀ ∈ innerLimit (funNhds (marginal φ G) x₀) (argminMap φ G))
    (hlsc : LowerSemicontinuousAt (marginal φ G) x₀)
    (hφ : ∃ ρ > 0, IsClosed (φ.Epi univ ∩ closedBall (((x₀, y₀), r) : (E × F) × ℝ) ρ))
    (hG : ∃ ρ > 0, IsClosed (graph G ∩ closedBall (x₀, y₀) ρ))
    (hqc : ∀ w ∈ singularSubdiff φ (x₀, y₀), -w ∈ normalCone (graph G) (x₀, y₀) → w = 0) :
    singularSubdiff (marginal φ G) x₀ ⊆
      {x | ∃ u v, u.coprod v ∈ singularSubdiff φ (x₀, y₀) ∧ x - u ∈ coderiv G x₀ y₀ v} :=
  fun _ hx ↦ exists_coprod_of_mem_singularSubdiff_graphRestrict (hy₀.2.trans hr) hy₀.1 hφ hG hqc
    (coprod_zero_mem_singularSubdiff_graphRestrict hr hy₀ hisc hlsc hx)

/-- Thm. 4.1(i) of [Mordukhovich 2018], (4.4), with the book's hypothesis: `M` inner
semicontinuous at `(x₀, y₀)` (relative to `dom M`). The book's proof passes to sequences
`xₖ →μ x₀` along which `M(xₖ)` must be nonempty; we assume that the infimum in (4.1) is attained
near `x₀` wherever `μ < ⊤` (`hatt`). Then `M` is `μ`-inner semicontinuous
(`mem_innerLimit_funNhds_of_innerSemicontinuousAt`) and `subdiff_marginal_subset` applies. -/
theorem subdiff_marginal_subset_of_innerSemicontinuousAt (hr : marginal φ G x₀ = r)
    (hy₀ : y₀ ∈ argminMap φ G x₀) (hisc : InnerSemicontinuousAt (argminMap φ G) x₀ y₀)
    (hatt : ∀ᶠ x in 𝓝 x₀, marginal φ G x ≠ ⊤ → (argminMap φ G x).Nonempty)
    (hφ : ∃ ρ > 0, IsClosed (φ.Epi univ ∩ closedBall (((x₀, y₀), r) : (E × F) × ℝ) ρ))
    (hG : ∃ ρ > 0, IsClosed (graph G ∩ closedBall (x₀, y₀) ρ))
    (hqc : ∀ w ∈ singularSubdiff φ (x₀, y₀), -w ∈ normalCone (graph G) (x₀, y₀) → w = 0) :
    subdiff (marginal φ G) x₀ ⊆
      {x | ∃ u v, u.coprod v ∈ subdiff φ (x₀, y₀) ∧ x - u ∈ coderiv G x₀ y₀ v} :=
  subdiff_marginal_subset hr hy₀ (mem_innerLimit_funNhds_of_innerSemicontinuousAt hr hisc hatt)
    hφ hG hqc

/-- Thm. 4.1(i) of [Mordukhovich 2018], (4.5), with the book's hypothesis: `M` inner
semicontinuous at `(x₀, y₀)`, the infimum being attained near `x₀` wherever `μ < ⊤`. Then `μ` is
lower semicontinuous at `x₀` (`lowerSemicontinuousAt_marginal_of_innerSemicontinuousAt`) and
`singularSubdiff_marginal_subset` applies. -/
theorem singularSubdiff_marginal_subset_of_innerSemicontinuousAt (hr : marginal φ G x₀ = r)
    (hy₀ : y₀ ∈ argminMap φ G x₀) (hisc : InnerSemicontinuousAt (argminMap φ G) x₀ y₀)
    (hatt : ∀ᶠ x in 𝓝 x₀, marginal φ G x ≠ ⊤ → (argminMap φ G x).Nonempty)
    (hφ : ∃ ρ > 0, IsClosed (φ.Epi univ ∩ closedBall (((x₀, y₀), r) : (E × F) × ℝ) ρ))
    (hG : ∃ ρ > 0, IsClosed (graph G ∩ closedBall (x₀, y₀) ρ))
    (hqc : ∀ w ∈ singularSubdiff φ (x₀, y₀), -w ∈ normalCone (graph G) (x₀, y₀) → w = 0) :
    singularSubdiff (marginal φ G) x₀ ⊆
      {x | ∃ u v, u.coprod v ∈ singularSubdiff φ (x₀, y₀) ∧ x - u ∈ coderiv G x₀ y₀ v} :=
  singularSubdiff_marginal_subset hr hy₀
    (mem_innerLimit_funNhds_of_innerSemicontinuousAt hr hisc hatt)
    (lowerSemicontinuousAt_marginal_of_innerSemicontinuousAt hy₀ hisc hatt
      (lowerSemicontinuousAt_of_locallyClosed_epi (hy₀.2.trans hr) hφ)) hφ hG hqc

/-- Thm. 4.1(ii) of [Mordukhovich 2018] (basic subgradients of marginal functions under local
boundedness): let `μ x₀ = r` be finite, `M` locally bounded around `x₀`, the infimum in (4.1)
attained near `x₀` wherever `μ < ⊤`, `gph G` closed, `φ` l.s.c. around `(x₀, y)` for every
`y ∈ G x₀`, and (4.3) at every `y ∈ M(x₀)`. Then
`∂μ(x₀) ⊆ ⋃_{y ∈ M(x₀)} ⋃_{(u, v) ∈ ∂φ(x₀, y)} [u + D*G(x₀, y)(v)]`. (The attainment of the
infimum is implicit in the book's proof.) -/
theorem subdiff_marginal_subset_of_locallyBoundedAt (hr : marginal φ G x₀ = r)
    (hlb : LocallyBoundedAt (argminMap φ G) x₀)
    (hatt : ∀ᶠ x in 𝓝 x₀, marginal φ G x ≠ ⊤ → (argminMap φ G x).Nonempty)
    (hG : IsClosed (graph G)) (hφ : ∀ y ∈ G x₀, ∃ U ∈ 𝓝 (x₀, y), LowerSemicontinuousOn φ U)
    (hqc : ∀ y ∈ argminMap φ G x₀, ∀ w ∈ singularSubdiff φ (x₀, y),
      -w ∈ normalCone (graph G) (x₀, y) → w = 0) :
    subdiff (marginal φ G) x₀ ⊆ ⋃ y ∈ argminMap φ G x₀,
      {x | ∃ u v, u.coprod v ∈ subdiff φ (x₀, y) ∧ x - u ∈ coderiv G x₀ y v} := by
  have hlφ : ∀ y ∈ G x₀, LowerSemicontinuousAt φ (x₀, y) := fun y hy ↦
    let ⟨_, hU, h⟩ := hφ y hy; lowerSemicontinuousAt_of_lowerSemicontinuousOn hU h
  intro x hx
  rw [mem_subdiff_iff hr] at hx
  obtain ⟨y, hy, hN⟩ := exists_comp_epiProj_mem_normalCone_epi_of_locallyBoundedAt hr hlb hatt hG
    hlφ hx (Or.inl (by simp))
  rw [coprod_comp_epiProj, ← mem_subdiff_iff (graphRestrict_apply_eq hr hy)] at hN
  obtain ⟨_, hU, h⟩ := hφ y hy.1
  exact mem_iUnion₂.2 ⟨y, hy, exists_coprod_of_mem_subdiff_graphRestrict (hy.2.trans hr) hy.1
    (locallyClosed_epi_of_lowerSemicontinuousOn hU h r) ⟨1, one_pos, hG.inter isClosed_closedBall⟩
    (hqc y hy) hN⟩

/-- Thm. 4.1(ii) of [Mordukhovich 2018] (singular subgradients of marginal functions under local
boundedness): under the assumptions of `subdiff_marginal_subset_of_locallyBoundedAt`,
`∂^∞μ(x₀) ⊆ ⋃_{y ∈ M(x₀)} ⋃_{(u, v) ∈ ∂^∞φ(x₀, y)} [u + D*G(x₀, y)(v)]`. -/
theorem singularSubdiff_marginal_subset_of_locallyBoundedAt (hr : marginal φ G x₀ = r)
    (hlb : LocallyBoundedAt (argminMap φ G) x₀)
    (hatt : ∀ᶠ x in 𝓝 x₀, marginal φ G x ≠ ⊤ → (argminMap φ G x).Nonempty)
    (hG : IsClosed (graph G)) (hφ : ∀ y ∈ G x₀, ∃ U ∈ 𝓝 (x₀, y), LowerSemicontinuousOn φ U)
    (hqc : ∀ y ∈ argminMap φ G x₀, ∀ w ∈ singularSubdiff φ (x₀, y),
      -w ∈ normalCone (graph G) (x₀, y) → w = 0) :
    singularSubdiff (marginal φ G) x₀ ⊆ ⋃ y ∈ argminMap φ G x₀,
      {x | ∃ u v, u.coprod v ∈ singularSubdiff φ (x₀, y) ∧ x - u ∈ coderiv G x₀ y v} := by
  have hlφ : ∀ y ∈ G x₀, LowerSemicontinuousAt φ (x₀, y) := fun y hy ↦
    let ⟨_, hU, h⟩ := hφ y hy; lowerSemicontinuousAt_of_lowerSemicontinuousOn hU h
  intro x hx
  rw [mem_singularSubdiff_iff hr] at hx
  obtain ⟨y, hy, hN⟩ := exists_comp_epiProj_mem_normalCone_epi_of_locallyBoundedAt hr hlb hatt hG
    hlφ hx (Or.inr (lowerSemicontinuousAt_marginal_of_locallyBoundedAt hlb hatt hG hlφ))
  rw [coprod_comp_epiProj, ← mem_singularSubdiff_iff (graphRestrict_apply_eq hr hy)] at hN
  obtain ⟨_, hU, h⟩ := hφ y hy.1
  exact mem_iUnion₂.2 ⟨y, hy, exists_coprod_of_mem_singularSubdiff_graphRestrict (hy.2.trans hr)
    hy.1 (locallyClosed_epi_of_lowerSemicontinuousOn hU h r)
    ⟨1, one_pos, hG.inter isClosed_closedBall⟩ (hqc y hy) hN⟩

end SumRule

section Coordinates

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- Subgradients of a function of the second variable [Mordukhovich 2018, Exercise 1.72]:
`∂(ψ ∘ snd)(x, y) = {(0, v) | v ∈ ∂ψ(y)}`. -/
theorem subdiff_comp_snd (ψ : F → EReal) (p : E × F) :
    subdiff (fun q : E × F ↦ ψ q.2) p =
      (fun v : StrongDual ℝ F ↦ v.comp (ContinuousLinearMap.snd ℝ E F)) '' subdiff ψ p.2 :=
  subdiff_comp_of_surjective (g := Prod.snd) (D := fun _ ↦ ContinuousLinearMap.snd ℝ E F)
    (Eventually.of_forall fun _ ↦ hasStrictFDerivAt_snd) continuousAt_const
    (fun y ↦ ⟨(0, y), rfl⟩)

/-- Singular subgradients of a function of the second variable
[Mordukhovich 2018, Exercise 1.72]: `∂^∞(ψ ∘ snd)(x, y) = {(0, v) | v ∈ ∂^∞ψ(y)}`. -/
theorem singularSubdiff_comp_snd (ψ : F → EReal) (p : E × F) :
    singularSubdiff (fun q : E × F ↦ ψ q.2) p =
      (fun v : StrongDual ℝ F ↦ v.comp (ContinuousLinearMap.snd ℝ E F)) ''
        singularSubdiff ψ p.2 :=
  singularSubdiff_comp_of_surjective (g := Prod.snd) (D := fun _ ↦ ContinuousLinearMap.snd ℝ E F)
    (Eventually.of_forall fun _ ↦ hasStrictFDerivAt_snd) continuousAt_const
    (fun y ↦ ⟨(0, y), rfl⟩)

/-- Subgradients of a function of the first variable [Mordukhovich 2018, Exercise 1.72]:
`∂(ψ ∘ fst)(x, y) = {(v, 0) | v ∈ ∂ψ(x)}`. -/
theorem subdiff_comp_fst (ψ : E → EReal) (p : E × F) :
    subdiff (fun q : E × F ↦ ψ q.1) p =
      (fun v : StrongDual ℝ E ↦ v.comp (ContinuousLinearMap.fst ℝ E F)) '' subdiff ψ p.1 :=
  subdiff_comp_of_surjective (g := Prod.fst) (D := fun _ ↦ ContinuousLinearMap.fst ℝ E F)
    (Eventually.of_forall fun _ ↦ hasStrictFDerivAt_fst) continuousAt_const
    (fun x ↦ ⟨(x, 0), rfl⟩)

/-- Singular subgradients of a function of the first variable
[Mordukhovich 2018, Exercise 1.72]: `∂^∞(ψ ∘ fst)(x, y) = {(v, 0) | v ∈ ∂^∞ψ(x)}`. -/
theorem singularSubdiff_comp_fst (ψ : E → EReal) (p : E × F) :
    singularSubdiff (fun q : E × F ↦ ψ q.1) p =
      (fun v : StrongDual ℝ E ↦ v.comp (ContinuousLinearMap.fst ℝ E F)) ''
        singularSubdiff ψ p.1 :=
  singularSubdiff_comp_of_surjective (g := Prod.fst) (D := fun _ ↦ ContinuousLinearMap.fst ℝ E F)
    (Eventually.of_forall fun _ ↦ hasStrictFDerivAt_fst) continuousAt_const
    (fun x ↦ ⟨(x, 0), rfl⟩)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem comp_snd_eq_coprod (v : StrongDual ℝ F) :
    v.comp (ContinuousLinearMap.snd ℝ E F) = (0 : StrongDual ℝ E).coprod v := by
  ext <;> simp

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem comp_fst_eq_coprod (v : StrongDual ℝ E) :
    v.comp (ContinuousLinearMap.fst ℝ E F) = v.coprod (0 : StrongDual ℝ F) := by
  ext <;> simp

end Coordinates

section Corollaries

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
variable {G : E → Set F} {x₀ : E} {y₀ : F} {r : ℝ}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- [Mordukhovich 2018, proof of Cor. 4.2]: for `φ` Lipschitz around `(x₀, y₀)`, the
qualification condition (4.3) holds, since `∂^∞φ(x₀, y₀) = {0}` (Thm. 1.22). -/
theorem marginal_qc_of_lipschitz {f : E × F → ℝ} {U : Set (E × F)} {L : NNReal}
    (hU : U ∈ 𝓝 (x₀, y₀)) (hL : LipschitzOnWith L f U) :
    ∀ w ∈ singularSubdiff (fun p ↦ (f p : EReal)) (x₀, y₀),
      -w ∈ normalCone (graph G) (x₀, y₀) → w = 0 := by
  intro w hw _
  rwa [singularSubdiff_eq_zero_of_lipschitz hU hL] at hw

/-- [Mordukhovich 2018, proof of Cor. 4.2]: for a cost `φ(x, y) = ψ(y)`, the qualification
condition (4.3) is `∂^∞ψ(y₀) ∩ ker D*G(x₀, y₀) = {0}`; it holds when `G` is metrically regular
around `(x₀, y₀)` (necessity in Thm. 3.3(ii), `MetricallyRegularAt.coderivKer_eq`). -/
theorem marginal_qc_of_metricallyRegularAt {ψ : F → EReal} (hy₀ : y₀ ∈ G x₀)
    (hG : MetricallyRegularAt G x₀ y₀) :
    ∀ w ∈ singularSubdiff (fun p : E × F ↦ ψ p.2) (x₀, y₀),
      -w ∈ normalCone (graph G) (x₀, y₀) → w = 0 := by
  intro w hw hN
  rw [singularSubdiff_comp_snd] at hw
  obtain ⟨v, -, rfl⟩ := hw
  have hv : v ∈ coderivKer G x₀ y₀ := by
    change _ ∈ normalCone _ _
    convert hN using 1
    ext <;> simp
  rw [hG.coderivKer_eq hy₀] at hv
  rw [mem_singleton_iff.1 hv]
  exact ContinuousLinearMap.zero_comp _

/-- Cor. 4.2 of [Mordukhovich 2018] (marginal functions with Lipschitzian data), first case: if
`M` is inner semicontinuous at `(x₀, y₀)` (the infimum being attained near `x₀` wherever
`μ < ⊤`), `φ` is Lipschitz around `(x₀, y₀)` and `gph G` is locally closed around `(x₀, y₀)`,
then (4.4) and (4.5) hold. -/
theorem marginal_subset_of_lipschitz {f : E × F → ℝ} {U : Set (E × F)} {L : NNReal}
    (hU : U ∈ 𝓝 (x₀, y₀)) (hL : LipschitzOnWith L f U)
    (hr : marginal (fun p ↦ (f p : EReal)) G x₀ = r)
    (hy₀ : y₀ ∈ argminMap (fun p ↦ (f p : EReal)) G x₀)
    (hisc : InnerSemicontinuousAt (argminMap (fun p ↦ (f p : EReal)) G) x₀ y₀)
    (hatt : ∀ᶠ x in 𝓝 x₀, marginal (fun p ↦ (f p : EReal)) G x ≠ ⊤ →
      (argminMap (fun p ↦ (f p : EReal)) G x).Nonempty)
    (hG : ∃ ρ > 0, IsClosed (graph G ∩ closedBall (x₀, y₀) ρ)) :
    subdiff (marginal (fun p ↦ (f p : EReal)) G) x₀ ⊆
      {x | ∃ u v, u.coprod v ∈ subdiff (fun p ↦ (f p : EReal)) (x₀, y₀) ∧
        x - u ∈ coderiv G x₀ y₀ v} ∧
    singularSubdiff (marginal (fun p ↦ (f p : EReal)) G) x₀ ⊆
      {x | ∃ u v, u.coprod v ∈ singularSubdiff (fun p ↦ (f p : EReal)) (x₀, y₀) ∧
        x - u ∈ coderiv G x₀ y₀ v} := by
  have hloc := locallyClosed_epi_of_continuousOn hU hL.continuousOn r
  exact ⟨subdiff_marginal_subset_of_innerSemicontinuousAt hr hy₀ hisc hatt hloc hG
    (marginal_qc_of_lipschitz hU hL),
    singularSubdiff_marginal_subset_of_innerSemicontinuousAt hr hy₀ hisc hatt hloc hG
    (marginal_qc_of_lipschitz hU hL)⟩

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- `ψ ∘ snd` is lower semicontinuous on `univ ×ˢ V` if `ψ` is on `V`. -/
theorem lowerSemicontinuousOn_comp_snd {ψ : F → EReal} {V : Set F}
    (hψ : LowerSemicontinuousOn ψ V) :
    LowerSemicontinuousOn (fun p : E × F ↦ ψ p.2) (univ ×ˢ V) := by
  intro p hp
  refine lowerSemicontinuousWithinAt_iff.2 fun c hc ↦ ?_
  have hT : Tendsto Prod.snd (𝓝[univ ×ˢ V] p) (𝓝[V] p.2) :=
    tendsto_nhdsWithin_iff.2 ⟨(continuous_snd.tendsto p).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun q hq ↦ hq.2⟩
  exact hT.eventually (lowerSemicontinuousWithinAt_iff.1 (hψ p.2 hp.2) c hc)

/-- Cor. 4.2 of [Mordukhovich 2018] (marginal functions with metrically regular constraints),
second case: for a cost `φ(x, y) = ψ(y)` with `ψ` l.s.c. around `y₀`, if `M` is inner
semicontinuous at `(x₀, y₀)` (the infimum being attained near `x₀` wherever `μ < ⊤`), `gph G`
is locally closed around `(x₀, y₀)` and `G` is metrically regular around `(x₀, y₀)`, then (4.4)
and (4.5) hold; here they read `∂μ(x₀) ⊆ ⋃_{v ∈ ∂ψ(y₀)} D*G(x₀, y₀)(v)` and
`∂^∞μ(x₀) ⊆ ⋃_{v ∈ ∂^∞ψ(y₀)} D*G(x₀, y₀)(v)`. -/
theorem marginal_subset_of_metricallyRegularAt {ψ : F → EReal} {V : Set F} (hV : V ∈ 𝓝 y₀)
    (hψ : LowerSemicontinuousOn ψ V) (hr : marginal (fun p : E × F ↦ ψ p.2) G x₀ = r)
    (hy₀ : y₀ ∈ argminMap (fun p : E × F ↦ ψ p.2) G x₀)
    (hisc : InnerSemicontinuousAt (argminMap (fun p : E × F ↦ ψ p.2) G) x₀ y₀)
    (hatt : ∀ᶠ x in 𝓝 x₀, marginal (fun p : E × F ↦ ψ p.2) G x ≠ ⊤ →
      (argminMap (fun p : E × F ↦ ψ p.2) G x).Nonempty)
    (hG : ∃ ρ > 0, IsClosed (graph G ∩ closedBall (x₀, y₀) ρ))
    (hreg : MetricallyRegularAt G x₀ y₀) :
    subdiff (marginal (fun p : E × F ↦ ψ p.2) G) x₀ ⊆ ⋃ v ∈ subdiff ψ y₀, coderiv G x₀ y₀ v ∧
    singularSubdiff (marginal (fun p : E × F ↦ ψ p.2) G) x₀ ⊆
      ⋃ v ∈ singularSubdiff ψ y₀, coderiv G x₀ y₀ v := by
  have hloc := locallyClosed_epi_of_lowerSemicontinuousOn (x₀ := (x₀, y₀))
    (prod_mem_nhds univ_mem hV) (lowerSemicontinuousOn_comp_snd hψ) r
  have hqc := marginal_qc_of_metricallyRegularAt (ψ := ψ) hy₀.1 hreg
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨u, v, huv, hx'⟩ := subdiff_marginal_subset_of_innerSemicontinuousAt hr hy₀ hisc hatt
      hloc hG hqc hx
    rw [subdiff_comp_snd] at huv
    obtain ⟨w, hw, hwe⟩ := huv
    replace hwe : (0 : StrongDual ℝ E).coprod w = u.coprod v :=
      (comp_snd_eq_coprod w).symm.trans hwe
    have hu : 0 = u := by simpa using congrArg (fun ℓ ↦ ℓ.comp (ContinuousLinearMap.inl ℝ E F)) hwe
    have hv : w = v := by simpa using congrArg (fun ℓ ↦ ℓ.comp (ContinuousLinearMap.inr ℝ E F)) hwe
    rw [← hu, sub_zero, ← hv] at hx'
    exact mem_iUnion₂.2 ⟨w, hw, hx'⟩
  · obtain ⟨u, v, huv, hx'⟩ := singularSubdiff_marginal_subset_of_innerSemicontinuousAt hr hy₀
      hisc hatt hloc hG hqc hx
    rw [singularSubdiff_comp_snd] at huv
    obtain ⟨w, hw, hwe⟩ := huv
    replace hwe : (0 : StrongDual ℝ E).coprod w = u.coprod v :=
      (comp_snd_eq_coprod w).symm.trans hwe
    have hu : 0 = u := by simpa using congrArg (fun ℓ ↦ ℓ.comp (ContinuousLinearMap.inl ℝ E F)) hwe
    have hv : w = v := by simpa using congrArg (fun ℓ ↦ ℓ.comp (ContinuousLinearMap.inr ℝ E F)) hwe
    rw [← hu, sub_zero, ← hv] at hx'
    exact mem_iUnion₂.2 ⟨w, hw, hx'⟩

/-- The reduction step of Cor. 4.3(i) of [Mordukhovich 2018] (local Lipschitz continuity of
marginal functions): under the assumptions of `marginal_subset_of_lipschitz`, if `G` is
Lipschitz-like around `(x₀, y₀)`, then `∂^∞μ(x₀) = {0}`, since (4.5) reduces to
`∂^∞μ(x₀) ⊆ D*G(x₀, y₀)(0) = {0}` (Thm. 3.3(iii), necessity). The book concludes with the "if"
part of Thm. 1.22, `∂^∞μ(x₀) = {0}` ⟹ `μ` Lipschitz around `x₀` for `μ` l.s.c. around `x₀`. -/
theorem singularSubdiff_marginal_eq_zero_of_lipschitzLikeAt {f : E × F → ℝ} {U : Set (E × F)}
    {L : NNReal} (hU : U ∈ 𝓝 (x₀, y₀)) (hL : LipschitzOnWith L f U)
    (hr : marginal (fun p ↦ (f p : EReal)) G x₀ = r)
    (hy₀ : y₀ ∈ argminMap (fun p ↦ (f p : EReal)) G x₀)
    (hisc : InnerSemicontinuousAt (argminMap (fun p ↦ (f p : EReal)) G) x₀ y₀)
    (hatt : ∀ᶠ x in 𝓝 x₀, marginal (fun p ↦ (f p : EReal)) G x ≠ ⊤ →
      (argminMap (fun p ↦ (f p : EReal)) G x).Nonempty)
    (hG : ∃ ρ > 0, IsClosed (graph G ∩ closedBall (x₀, y₀) ρ))
    (hlip : LipschitzLikeAt G x₀ y₀) :
    singularSubdiff (marginal (fun p ↦ (f p : EReal)) G) x₀ = {0} := by
  refine subset_antisymm (fun x hx ↦ ?_) (singleton_subset_iff.2 (zero_mem_singularSubdiff hr))
  obtain ⟨u, v, huv, hx'⟩ :=
    (marginal_subset_of_lipschitz hU hL hr hy₀ hisc hatt hG).2 hx
  rw [singularSubdiff_eq_zero_of_lipschitz hU hL, mem_singleton_iff] at huv
  have hu : u = 0 := by simpa using congrArg (fun ℓ ↦ ℓ.comp (ContinuousLinearMap.inl ℝ E F)) huv
  have hv : v = 0 := by simpa using congrArg (fun ℓ ↦ ℓ.comp (ContinuousLinearMap.inr ℝ E F)) huv
  rw [hu, hv, sub_zero, hlip.coderiv_zero hy₀.1] at hx'
  exact hx'

/-- The reduction step of Cor. 4.3(ii) of [Mordukhovich 2018]: let `M` be locally bounded around
`x₀`, the infimum in (4.1) attained near `x₀` wherever `μ < ⊤`, `gph G` closed, the real-valued
cost `f` l.s.c. around every `(x₀, y)`, `y ∈ G x₀`, and Lipschitz around `(x₀, y)` with `G`
Lipschitz-like around `(x₀, y)` for every `y ∈ M(x₀)`. Then `∂^∞μ(x₀) = {0}`. -/
theorem singularSubdiff_marginal_eq_zero_of_locallyBoundedAt {f : E × F → ℝ}
    (hr : marginal (fun p ↦ (f p : EReal)) G x₀ = r)
    (hlb : LocallyBoundedAt (argminMap (fun p ↦ (f p : EReal)) G) x₀)
    (hatt : ∀ᶠ x in 𝓝 x₀, marginal (fun p ↦ (f p : EReal)) G x ≠ ⊤ →
      (argminMap (fun p ↦ (f p : EReal)) G x).Nonempty)
    (hG : IsClosed (graph G))
    (hφ : ∀ y ∈ G x₀, ∃ U ∈ 𝓝 (x₀, y), LowerSemicontinuousOn (fun p ↦ (f p : EReal)) U)
    (hL : ∀ y ∈ argminMap (fun p ↦ (f p : EReal)) G x₀,
      ∃ U ∈ 𝓝 (x₀, y), ∃ L : NNReal, LipschitzOnWith L f U)
    (hlip : ∀ y ∈ argminMap (fun p ↦ (f p : EReal)) G x₀, LipschitzLikeAt G x₀ y) :
    singularSubdiff (marginal (fun p ↦ (f p : EReal)) G) x₀ = {0} := by
  refine subset_antisymm (fun x hx ↦ ?_) (singleton_subset_iff.2 (zero_mem_singularSubdiff hr))
  have hqc : ∀ y ∈ argminMap (fun p ↦ (f p : EReal)) G x₀,
      ∀ w ∈ singularSubdiff (fun p ↦ (f p : EReal)) (x₀, y),
        -w ∈ normalCone (graph G) (x₀, y) → w = 0 := fun y hy ↦
    let ⟨_, hU, _, hLy⟩ := hL y hy; marginal_qc_of_lipschitz hU hLy
  obtain ⟨y, hy, u, v, huv, hx'⟩ := mem_iUnion₂.1
    (singularSubdiff_marginal_subset_of_locallyBoundedAt hr hlb hatt hG hφ hqc hx)
  obtain ⟨_, hU, _, hLy⟩ := hL y hy
  rw [singularSubdiff_eq_zero_of_lipschitz hU hLy, mem_singleton_iff] at huv
  have hu : u = 0 := by simpa using congrArg (fun ℓ ↦ ℓ.comp (ContinuousLinearMap.inl ℝ E F)) huv
  have hv : v = 0 := by simpa using congrArg (fun ℓ ↦ ℓ.comp (ContinuousLinearMap.inr ℝ E F)) huv
  rw [hu, hv, sub_zero, (hlip y hy).coderiv_zero hy.1] at hx'
  exact hx'

end Corollaries

end VariationalAnalysis
