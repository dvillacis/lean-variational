/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import VariationalAnalysis.SecondOrder.GraphicalDerivative
import VariationalAnalysis.SecondOrder.ProxRegular

/-!
# Second-order relations for `C^{1,1}` functions

This file follows [Mordukhovich 2024, Sect. 1.4.2] (body numbering): directional
differentiability of single-valued mappings (Def. 1.77) and the inclusion
`∂²_D φ(x̄)(u) ⊆ ∂²φ(x̄)(u)` for `C^{1,1}` functions with directionally differentiable gradient
(Thm. 1.84).

## Main declarations

* `HasDirDerivAt f x w v`, `DirDifferentiableAt f x`: [Mordukhovich 2024, Def. 1.77, (1.101)].
* `blowUp f x₀ t`: the difference quotient `z ↦ (f(x₀ + tz) - f(x₀))/t`.

## Main results

* `graphDeriv_subset_of_hasDirDerivAt`: for a mapping Lipschitz around `x̄` and directionally
  differentiable at `x̄` in the direction `u`, `Df(x̄)(u) ⊆ {f'(x̄; u)}`.
* `tendstoUniformlyOn_blowUp`: the blow-ups converge to `f'(x̄; ·)` uniformly on compact sets.
* `exists_hasFDerivAt_dirDeriv`: if `f = ∇φ` is Lipschitz around `x̄` and directionally
  differentiable at `x̄`, then `f'(x̄; ·)` is a gradient.
* `dirDeriv_mem_subdiff`: `f'(x̄; u) ∈ ∂⟨f(·), u⟩(x̄)`.
* `subgradGraphDeriv_subset_secondOrderSubdiff`: [Mordukhovich 2024, Thm. 1.84, (1.111)].

## Proof of Thm. 1.84

We do not follow the book's proof via Lemma 1.81, which works with projections onto subsets of
`ℝⁿ × ℝⁿ`. Write `f = ∇φ` and `g = f'(x̄; ·)`. By Prop. 1.50, `∂²φ(x̄)(u) = ∂⟨f(·), u⟩(x̄)`, and
`∂²_D φ(x̄)(u) ⊆ {g(u)}`. The blow-ups `gₜ(z) = (f(x̄ + tz) - f(x̄))/t` are gradients and
converge to `g`, which is therefore the gradient of `ψ(z) = ⟨g(z), z⟩/2`; `g` is Lipschitz and
positively homogeneous. At a point `w` of differentiability of `g` (Rademacher), `A = ∇g(w)` is
symmetric and `Aw = g(w)` (Euler's identity), so the gradient `Au` of `⟨g(·), u⟩` at `w` is close
to `g(u)` when `w` is close to `u`. Finally, gradients of the limit `⟨g(·), u⟩` are approximated
by regular subgradients of the blow-ups `⟨gₜ(·), u⟩`, via a smooth support, and these are regular
subgradients of `⟨f(·), u⟩` at points `x̄ + tz → x̄`.
-/

open Filter Topology Set Metric ContinuousLinearMap MeasureTheory
open scoped NNReal

namespace VariationalAnalysis

section Dir

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- [Mordukhovich 2024, Def. 1.77, (1.101)]: `f` is directionally differentiable at `x` in the
direction `w` with directional derivative `f'(x; w) = v` if `(f(x + tw) - f(x))/t → v` as
`t ↓ 0`. -/
def HasDirDerivAt (f : E → F) (x w : E) (v : F) : Prop :=
  Tendsto (fun t : ℝ ↦ t⁻¹ • (f (x + t • w) - f x)) (𝓝[>] 0) (𝓝 v)

/-- [Mordukhovich 2024, Def. 1.77]: `f` is directionally differentiable at `x` if the limit
(1.101) exists in every direction. -/
def DirDifferentiableAt (f : E → F) (x : E) : Prop :=
  ∀ w, ∃ v, HasDirDerivAt f x w v

variable {f : E → F} {x x₀ w u : E} {v v₁ v₂ : F}

theorem HasDirDerivAt.unique (h₁ : HasDirDerivAt f x w v₁) (h₂ : HasDirDerivAt f x w v₂) :
    v₁ = v₂ :=
  tendsto_nhds_unique h₁ h₂

theorem hasDirDerivAt_zero (f : E → F) (x : E) : HasDirDerivAt f x 0 0 := by
  simp [HasDirDerivAt]

/-- Fréchet differentiable mappings are directionally differentiable. -/
theorem HasFDerivAt.hasDirDerivAt {A : E →L[ℝ] F} (hf : HasFDerivAt f A x) (w : E) :
    HasDirDerivAt f x w (A w) := by
  have hl : HasDerivAt (fun t : ℝ ↦ x + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x
  have h := (hf.comp_hasDerivAt_of_eq 0 hl (by simp)).tendsto_slope_zero_right
  simpa [HasDirDerivAt, Function.comp_def] using h

theorem tendsto_add_smul_nhdsGT (x w : E) :
    Tendsto (fun t : ℝ ↦ x + t • w) (𝓝[>] 0) (𝓝 x) := by
  have : Tendsto (fun t : ℝ ↦ x + t • w) (𝓝 0) (𝓝 (x + (0 : ℝ) • w)) :=
    (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
  simpa using this.mono_left nhdsWithin_le_nhds

/-- For a mapping Lipschitz around `x₀` and directionally differentiable at `x₀` in the direction
`u`, the graphical derivative is `Df(x₀)(u) ⊆ {f'(x₀; u)}`. -/
theorem graphDeriv_subset_of_hasDirDerivAt {U : Set E} {L : ℝ≥0} (hU : U ∈ 𝓝 x₀)
    (hL : LipschitzOnWith L f U) (hv : HasDirDerivAt f x₀ u v) :
    graphDeriv (fun x ↦ {f x}) x₀ (f x₀) u ⊆ {v} := by
  rintro v' ⟨-, p, α, hp, hpt, hα⟩
  have hgr : ∀ k, (p k).2 = f (p k).1 := fun k ↦ (hp k).1
  have ha : Tendsto (fun k ↦ α k • ((p k).1 - x₀)) atTop (𝓝 u) := by
    simpa [Function.comp_def] using (continuous_fst.tendsto _).comp hα
  have hb : Tendsto (fun k ↦ α k • (f (p k).1 - f x₀)) atTop (𝓝 v') := by
    simpa [Function.comp_def, hgr] using (continuous_snd.tendsto _).comp hα
  have hx : Tendsto (fun k ↦ (p k).1) atTop (𝓝 x₀) := by
    simpa [Function.comp_def] using (continuous_fst.tendsto _).comp hpt
  have hxU : ∀ᶠ k in atTop, (p k).1 ∈ U := hx.eventually hU
  have hx₀U : x₀ ∈ U := mem_of_mem_nhds hU
  change v' = v
  by_cases hu : u = 0
  · subst hu
    rw [hv.unique (hasDirDerivAt_zero f x₀)]
    have hbound : ∀ᶠ k in atTop,
        ‖α k • (f (p k).1 - f x₀)‖ ≤ L * ‖α k • ((p k).1 - x₀)‖ := by
      filter_upwards [hxU] with k hk
      rw [norm_smul, norm_smul, mul_left_comm]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [← dist_eq_norm, ← dist_eq_norm]
      exact hL.dist_le_mul _ hk _ hx₀U
    refine tendsto_nhds_unique hb (squeeze_zero_norm' hbound ?_)
    simpa using ha.norm.const_mul (L : ℝ)
  · have hu' : 0 < ‖u‖ := norm_pos_iff.2 hu
    have hαtop : Tendsto α atTop atTop := by
      rw [Filter.tendsto_atTop]
      intro M
      have e1 : ∀ᶠ k in atTop, ‖u‖ / 2 < ‖α k • ((p k).1 - x₀)‖ :=
        ha.norm.eventually (lt_mem_nhds (by linarith))
      have e2 : ∀ᶠ k in atTop, ‖(p k).1 - x₀‖ < ‖u‖ / (2 * (|M| + 1)) :=
        (tendsto_iff_norm_sub_tendsto_zero.1 hx).eventually (gt_mem_nhds (by positivity))
      filter_upwards [e1, e2] with k h1 h2
      rw [norm_smul, Real.norm_of_nonneg (hp k).2] at h1
      by_contra hlt
      push Not at hlt
      have h3 : α k * ‖(p k).1 - x₀‖ ≤ (|M| + 1) * ‖(p k).1 - x₀‖ :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self M]) (norm_nonneg _)
      have h4 := (lt_div_iff₀ (by positivity)).1 h2
      linarith
    have hαpos : ∀ᶠ k in atTop, 0 < α k := hαtop.eventually (eventually_gt_atTop 0)
    have hs : Tendsto (fun k ↦ (α k)⁻¹) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_inv_atTop_zero.comp hαtop,
        hαpos.mono fun k hk ↦ inv_pos.2 hk⟩
    have hc : Tendsto (fun k ↦ α k • (f (x₀ + (α k)⁻¹ • u) - f x₀)) atTop (𝓝 v) := by
      refine (hv.comp hs).congr' ?_
      filter_upwards [hαpos] with k hk
      simp [inv_inv]
    have hy : Tendsto (fun k ↦ x₀ + (α k)⁻¹ • u) atTop (𝓝 x₀) :=
      (tendsto_add_smul_nhdsGT x₀ u).comp hs
    have hdiff : Tendsto (fun k ↦ α k • (f (p k).1 - f x₀) -
        α k • (f (x₀ + (α k)⁻¹ • u) - f x₀)) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ (by simpa using ((ha.sub_const u).norm.const_mul (L : ℝ)))
      filter_upwards [hxU, hy.eventually hU, hαpos] with k hk hk' hpos
      rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_of_nonneg hpos.le]
      calc α k * ‖f (p k).1 - f (x₀ + (α k)⁻¹ • u)‖
          ≤ α k * (L * ‖(p k).1 - (x₀ + (α k)⁻¹ • u)‖) := by
            refine mul_le_mul_of_nonneg_left ?_ hpos.le
            rw [← dist_eq_norm, ← dist_eq_norm]
            exact hL.dist_le_mul _ hk _ hk'
        _ = L * ‖α k • ((p k).1 - x₀) - u‖ := by
          rw [show (p k).1 - (x₀ + (α k)⁻¹ • u) = (α k)⁻¹ • (α k • ((p k).1 - x₀) - u) by
              rw [smul_sub, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]; abel,
            norm_smul, Real.norm_of_nonneg (inv_pos.2 hpos).le]
          field_simp
    have := hc.add hdiff
    simp only [add_sub_cancel, add_zero] at this
    exact tendsto_nhds_unique hb this

/-! ### The directional derivative as a blow-up limit -/

section BlowUp

variable {g : E → F}

/-- The directional derivative of `f` at `x₀` is positively homogeneous in the direction. -/
theorem dirDeriv_smul (hg : ∀ u, HasDirDerivAt f x₀ u (g u)) {s : ℝ} (hs : 0 ≤ s) (u : E) :
    g (s • u) = s • g u := by
  rcases hs.eq_or_lt with rfl | hs
  · rw [zero_smul, zero_smul]
    exact (hg 0).unique (hasDirDerivAt_zero f x₀)
  refine (hg (s • u)).unique ?_
  have hmul : Tendsto (fun t : ℝ ↦ t * s) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun t ht ↦
      mul_pos ht hs⟩
    simpa using ((continuous_mul_const s).tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
  refine ((hg u).comp hmul).const_smul s |>.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  change s • ((t * s)⁻¹ • (f (x₀ + (t * s) • u) - f x₀)) = t⁻¹ • (f (x₀ + t • s • u) - f x₀)
  rw [smul_smul, smul_smul, show s * (t * s)⁻¹ = t⁻¹ by field_simp]

/-- The directional derivative of a mapping `L`-Lipschitz around `x₀` is `L`-Lipschitz. -/
theorem dirDeriv_lipschitz {U : Set E} {L : ℝ≥0} (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U)
    (hg : ∀ u, HasDirDerivAt f x₀ u (g u)) : LipschitzWith L g := by
  refine LipschitzWith.of_dist_le_mul fun u u' ↦ ?_
  rw [dist_eq_norm, dist_eq_norm]
  refine le_of_tendsto ((hg u).sub (hg u')).norm ?_
  filter_upwards [(tendsto_add_smul_nhdsGT x₀ u).eventually hU,
    (tendsto_add_smul_nhdsGT x₀ u').eventually hU, self_mem_nhdsWithin] with t hu hu' (ht : 0 < t)
  rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_of_nonneg (inv_pos.2 ht).le]
  have := hL.dist_le_mul _ hu _ hu'
  rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul,
    Real.norm_of_nonneg ht.le] at this
  calc t⁻¹ * ‖f (x₀ + t • u) - f (x₀ + t • u')‖ ≤ t⁻¹ * (L * (t * ‖u - u'‖)) :=
        mul_le_mul_of_nonneg_left this (inv_nonneg.2 ht.le)
    _ = L * ‖u - u'‖ := by field_simp

end BlowUp

end Dir

/-! ### Blow-ups and their uniform convergence -/

section BlowUpConv

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The blow-up `z ↦ (f(x₀ + tz) - f(x₀))/t` of `f` at `x₀`; `f` is directionally differentiable
at `x₀` iff the blow-ups converge pointwise as `t ↓ 0`. -/
noncomputable def blowUp (f : E → F) (x₀ : E) (t : ℝ) (z : E) : F :=
  t⁻¹ • (f (x₀ + t • z) - f x₀)

theorem lipschitzOnWith_blowUp {f : E → F} {x₀ : E} {U S : Set E} {L : ℝ≥0}
    (hL : LipschitzOnWith L f U) {t : ℝ} (ht : 0 < t) (hS : ∀ z ∈ S, x₀ + t • z ∈ U) :
    LipschitzOnWith L (blowUp f x₀ t) S := by
  refine LipschitzOnWith.of_dist_le_mul fun z hz z' hz' ↦ ?_
  rw [dist_eq_norm, dist_eq_norm]
  simp only [blowUp]
  rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_of_nonneg (inv_pos.2 ht).le]
  have := hL.dist_le_mul _ (hS z hz) _ (hS z' hz')
  rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul,
    Real.norm_of_nonneg ht.le] at this
  calc t⁻¹ * ‖f (x₀ + t • z) - f (x₀ + t • z')‖ ≤ t⁻¹ * (L * (t * ‖z - z'‖)) :=
        mul_le_mul_of_nonneg_left this (inv_nonneg.2 ht.le)
    _ = L * ‖z - z'‖ := by field_simp

theorem eventually_add_smul_mem {x₀ : E} {U : Set E} (hU : U ∈ 𝓝 x₀) (R : ℝ) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ closedBall (0 : E) R, x₀ + t • z ∈ U := by
  obtain ⟨η, hη, hηU⟩ := Metric.mem_nhds_iff.1 hU
  have hc : Tendsto (fun t : ℝ ↦ |t| * (|R| + 1)) (𝓝 0) (𝓝 0) := by
    exact (show Continuous (fun t : ℝ ↦ |t| * (|R| + 1)) by fun_prop).tendsto' 0 0 (by simp)
  filter_upwards [nhdsWithin_le_nhds (hc.eventually (gt_mem_nhds hη))] with t ht z hz
  apply hηU
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  have hz' : ‖z‖ ≤ |R| + 1 := by
    rw [mem_closedBall, dist_zero_right] at hz; linarith [le_abs_self R]
  calc |t| * ‖z‖ ≤ |t| * (|R| + 1) := mul_le_mul_of_nonneg_left hz' (abs_nonneg t)
    _ < η := ht

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Pointwise convergence of equi-Lipschitz mappings on a compact set is uniform. -/
theorem tendstoUniformlyOn_of_lipschitzOnWith {ι : Type*} {l : Filter ι} {G : ι → E → F}
    {g : E → F} {S : Set E} {K : ℝ≥0} (hS : IsCompact S)
    (hG : ∀ᶠ i in l, LipschitzOnWith K (G i) S) (hg : LipschitzOnWith K g S)
    (hlim : ∀ z ∈ S, Tendsto (fun i ↦ G i z) l (𝓝 (g z))) : TendstoUniformlyOn G g l S := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨T, hTS, hT, hcov⟩ :=
    finite_cover_balls_of_compact hS (e := ε / (3 * (K + 1))) (by positivity)
  have hfin : ∀ᶠ i in l, ∀ c ∈ T, dist (g c) (G i c) < ε / 3 :=
    (eventually_all_finite hT).2 fun c hc ↦
      ((hlim c (hTS hc)).eventually
        (Metric.ball_mem_nhds (g c) (show (0 : ℝ) < ε / 3 by positivity))).mono
        fun i hi ↦ by rw [dist_comm]; exact hi
  filter_upwards [hfin, hG] with i hi hGi z hz
  obtain ⟨c, hc, hzc⟩ := mem_iUnion₂.1 (hcov hz)
  have h1 := hg.dist_le_mul z hz c (hTS hc)
  have h2 := hGi.dist_le_mul c (hTS hc) z hz
  have h3 := hi c hc
  rw [dist_comm c z] at h2
  have hd : dist z c < ε / (3 * (K + 1)) := hzc
  have hK : (K : ℝ) * dist z c < ε / 3 := by
    calc (K : ℝ) * dist z c ≤ (K + 1) * dist z c :=
          mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
      _ < (K + 1) * (ε / (3 * (K + 1))) := mul_lt_mul_of_pos_left hd (by positivity)
      _ = ε / 3 := by field_simp
  calc dist (g z) (G i z) ≤ dist (g z) (g c) + dist (g c) (G i c) + dist (G i c) (G i z) :=
        dist_triangle4 _ _ _ _
    _ < ε := by linarith

/-- The blow-ups of a mapping Lipschitz around `x₀` and directionally differentiable at `x₀`
converge to the directional derivative uniformly on compact sets. -/
theorem tendstoUniformlyOn_blowUp {f : E → F} {g : E → F} {x₀ : E} {U : Set E} {L : ℝ≥0}
    (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U) (hg : ∀ u, HasDirDerivAt f x₀ u (g u))
    {S : Set E} (hS : IsCompact S) : TendstoUniformlyOn (blowUp f x₀) g (𝓝[>] 0) S := by
  obtain ⟨R, hR⟩ := hS.isBounded.subset_closedBall 0
  refine tendstoUniformlyOn_of_lipschitzOnWith hS ?_
    (dirDeriv_lipschitz hU hL hg).lipschitzOnWith fun z _ ↦ hg z
  filter_upwards [eventually_add_smul_mem hU R, self_mem_nhdsWithin] with t ht (htpos : 0 < t)
  exact lipschitzOnWith_blowUp hL htpos fun z hz ↦ ht z (hR hz)

end BlowUpConv

/-! ### The directional derivative of a gradient is a gradient -/

section Potential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- If `φ'` is the gradient of `φ` around `x₀`, Lipschitz there and directionally differentiable
at `x₀` with directional derivative `g`, then `g` is a gradient on every ball around `0`. -/
theorem exists_hasFDerivAt_dirDeriv {φ : E → ℝ} {φ' g : E → StrongDual ℝ E} {x₀ : E}
    {U : Set E} {L : ℝ≥0} (hU : U ∈ 𝓝 x₀) (hφ : ∀ x ∈ U, HasFDerivAt φ (φ' x) x)
    (hL : LipschitzOnWith L φ' U) (hg : ∀ u, HasDirDerivAt φ' x₀ u (g u)) (R : ℝ) :
    ∃ Ψ : E → ℝ, ∀ z ∈ ball (0 : E) R, HasFDerivAt Ψ (g z) z := by
  obtain ⟨η, hη, hηU⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = η / (|R| + 1) := ⟨_, rfl⟩
  have hτpos : 0 < τ := hτ ▸ by positivity
  let t : ℕ → ℝ := fun n ↦ τ / (n + 1)
  have htpos : ∀ n, 0 < t n := fun n ↦ by positivity
  have htle : ∀ n, t n ≤ τ := fun n ↦ div_le_self hτpos.le (by linarith [n.cast_nonneg (α := ℝ)])
  have hmem : ∀ n, ∀ z ∈ ball (0 : E) R, x₀ + t n • z ∈ U := by
    intro n z hz
    apply hηU
    rw [mem_ball, dist_zero_right] at hz
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (htpos n).le]
    have hR : ‖z‖ < |R| + 1 := by linarith [le_abs_self R]
    calc t n * ‖z‖ ≤ τ * ‖z‖ := mul_le_mul_of_nonneg_right (htle n) (norm_nonneg _)
      _ < τ * (|R| + 1) := mul_lt_mul_of_pos_left hR hτpos
      _ = η := by rw [hτ]; field_simp
  have httend : Tendsto t atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall htpos⟩
    simpa [t, div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul τ)
  let ψ : ℕ → E → ℝ := fun n z ↦ (t n ^ 2)⁻¹ * (φ (x₀ + t n • z) - φ x₀ - t n * φ' x₀ z)
  have hderiv : ∀ n, ∀ z ∈ ball (0 : E) R, HasFDerivAt (ψ n) (blowUp φ' x₀ (t n) z) z := by
    intro n z hz
    have h1 : HasFDerivAt (fun z ↦ x₀ + t n • z) (t n • ContinuousLinearMap.id ℝ E) z :=
      ((hasFDerivAt_id z).const_smul (t n)).const_add x₀
    have h2 := (hφ _ (hmem n z hz)).comp z h1
    have h3 : HasFDerivAt (fun z ↦ t n * φ' x₀ z) (t n • φ' x₀) z :=
      (φ' x₀).hasFDerivAt.const_smul (t n)
    refine (((h2.sub_const (φ x₀)).sub h3).const_mul (t n ^ 2)⁻¹).congr_fderiv ?_
    ext d
    have := (htpos n).ne'
    simp only [blowUp]
    simp
    field_simp
  have hunif : TendstoUniformlyOn (fun n ↦ blowUp φ' x₀ (t n)) g atTop (ball (0 : E) R) := by
    have h := (tendstoUniformlyOn_blowUp hU hL hg (isCompact_closedBall (0 : E) R)).mono
      ball_subset_closedBall
    rw [Metric.tendstoUniformlyOn_iff] at h ⊢
    exact fun ε hε ↦ httend.eventually (h ε hε)
  have hψ0 : Tendsto (fun n ↦ ψ n 0) atTop (𝓝 0) := by simp [ψ]
  have hUC := uniformCauchySeqOn_ball_of_fderiv hunif.uniformCauchySeqOn hderiv hψ0.cauchy_map
  refine ⟨fun z ↦ limUnder atTop fun n ↦ ψ n z, fun z hz ↦ ?_⟩
  exact hasFDerivAt_of_tendstoUniformlyOn isOpen_ball hunif hderiv
    (fun y hy ↦ (hUC.cauchySeq hy).tendsto_limUnder) hz

end Potential

/-! ### Euler's identity and the scaling of regular subgradients -/

section Euler

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Euler's identity: the derivative of a positively homogeneous mapping `g` at `w` maps `w` to
`g(w)`. -/
theorem HasFDerivAt.apply_self_of_homogeneous {g : E → F} {A : E →L[ℝ] F} {w : E}
    (hhom : ∀ s : ℝ, 0 ≤ s → g (s • w) = s • g w) (hA : HasFDerivAt g A w) : A w = g w := by
  have hl : HasDerivAt (fun s : ℝ ↦ s • w) w 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const w
  have h1 : HasDerivAt (fun s : ℝ ↦ g (s • w)) (A w) 1 :=
    hA.comp_hasDerivAt_of_eq 1 hl (by simp)
  have h2 : HasDerivAt (fun s : ℝ ↦ g (s • w)) (g w) 1 := by
    have : HasDerivAt (fun s : ℝ ↦ s • g w) (g w) 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const (g w)
    refine this.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with s hs
    exact hhom s hs.le
  exact h1.unique h2

/-- Regular subgradients of a blow-up of `h` at `z` are regular subgradients of `h` at
`x₀ + tz`. -/
theorem mem_regularSubdiff_of_mem_regularSubdiff_blowUp {h : E → ℝ} {x₀ z : E} {t : ℝ}
    (ht : 0 < t) {b : StrongDual ℝ E}
    (hb : b ∈ regularSubdiff (fun z ↦ ((blowUp h x₀ t z : ℝ) : EReal)) z) :
    b ∈ regularSubdiff (fun x ↦ (h x : EReal)) (x₀ + t • z) := by
  rw [mem_regularSubdiff_iff (φ := fun z ↦ ((blowUp h x₀ t z : ℝ) : EReal)) rfl] at hb
  rw [mem_regularSubdiff_iff (φ := fun x ↦ (h x : EReal)) rfl]
  intro ε hε
  have hc : Tendsto (fun x ↦ t⁻¹ • (x - x₀)) (𝓝 (x₀ + t • z)) (𝓝 z) := by
    have : Continuous (fun x : E ↦ t⁻¹ • (x - x₀)) := by fun_prop
    simpa [smul_smul, inv_mul_cancel₀ ht.ne'] using this.tendsto (x₀ + t • z)
  filter_upwards [hc.eventually (hb ε hε)] with x hx
  have e1 : x₀ + t • (t⁻¹ • (x - x₀)) = x := by
    rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]; abel
  have e2 : t⁻¹ • (x - x₀) - z = t⁻¹ • (x - (x₀ + t • z)) := by
    rw [smul_sub, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]; abel
  simp only [blowUp, e1, e2, map_smul, norm_smul, smul_eq_mul,
    Real.norm_of_nonneg (inv_pos.2 ht).le, EReal.coe_le_coe_iff] at hx
  rw [EReal.coe_le_coe_iff]
  have key : t⁻¹ * (h (x₀ + t • z) + b (x - (x₀ + t • z)) - ε * ‖x - (x₀ + t • z)‖ - h x₀) ≤
      t⁻¹ * (h x - h x₀) := by linarith
  linarith [le_of_mul_le_mul_left key (inv_pos.2 ht)]

/-- Fermat's rule with a smooth perturbation. -/
theorem neg_mem_regularSubdiff_of_isLocalMin_add {k q : E → ℝ} {q' : StrongDual ℝ E} {z : E}
    (hq : HasFDerivAt q q' z) (hmin : IsLocalMin (fun x ↦ k x + q x) z) :
    -q' ∈ regularSubdiff (fun x ↦ (k x : EReal)) z := by
  have hmin' : IsLocalMin (fun x ↦ ((k x + q x : ℝ) : EReal)) z :=
    Filter.Eventually.mono hmin fun x hx ↦ EReal.coe_le_coe_iff.2 hx
  have h0 := zero_mem_regularSubdiff_of_isLocalMin hmin' rfl
  have heq : (fun x ↦ ((k x + q x : ℝ) : EReal)) = fun x ↦ (k x : EReal) + q x :=
    funext fun x ↦ EReal.coe_add _ _
  rwa [heq, mem_regularSubdiff_add_iff hq, zero_sub] at h0

end Euler

/-! ### Approximation of gradients of a uniform limit -/

section Approx

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- If `H` is differentiable at `w` with derivative `a`, then every continuous `k` uniformly close
to `H` on a small ball around `w` has a regular subgradient close to `a` at a point of that
ball. -/
theorem exists_regularSubdiff_near_of_hasFDerivAt {H : E → ℝ} {a : StrongDual ℝ E} {w : E}
    (hH : HasFDerivAt H a w) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ k : E → ℝ, ContinuousOn k (closedBall w r) →
      (∀ z ∈ closedBall w r, |k z - H z| < ε * r / 16) →
      ∃ z ∈ ball w r, ∃ b ∈ regularSubdiff (fun x ↦ (k x : EReal)) z, ‖b - a‖ ≤ ε := by
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = ε / 4 := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; positivity
  obtain ⟨ρ, hρ, hρH⟩ := Metric.eventually_nhds_iff.1 (hH.isLittleO.def hδpos)
  refine ⟨ρ / 2, by positivity, fun k hk hkH ↦ ?_⟩
  obtain ⟨r, hr⟩ : ∃ r, r = ρ / 2 := ⟨_, rfl⟩
  rw [← hr] at hk hkH ⊢
  have hrpos : 0 < r := by rw [hr]; positivity
  have hHr : ∀ z ∈ closedBall w r, |H z - H w - a (z - w)| ≤ δ * ‖z - w‖ := by
    intro z hz
    have := hρH (show dist z w < ρ by rw [mem_closedBall] at hz; linarith)
    simpa [Real.norm_eq_abs] using this
  obtain ⟨c, hc⟩ : ∃ c, c = 4 * δ / r := ⟨_, rfl⟩
  have hcpos : 0 < c := by rw [hc]; positivity
  let q : E → ℝ := fun z ↦ -a z + c / 2 * ‖z - w‖ ^ 2
  have hqc : Continuous q := by fun_prop
  obtain ⟨z, hz, hmin⟩ := (isCompact_closedBall w r).exists_isMinOn
    (nonempty_closedBall.2 hrpos.le) (hk.add hqc.continuousOn)
  have hw : w ∈ closedBall w r := mem_closedBall_self hrpos.le
  have hzw : ‖z - w‖ < r := by
    have hzr : ‖z - w‖ ≤ r := by rwa [mem_closedBall, dist_eq_norm] at hz
    refine lt_of_le_of_ne hzr fun heq ↦ ?_
    have h1 : k z + q z ≤ k w + q w := hmin hw
    simp only [q, sub_self, norm_zero] at h1
    have h2 := hkH z hz
    have h3 := hkH w hw
    have h4 := hHr z hz
    rw [heq, map_sub] at h4
    rw [heq] at h1
    have hq : c / 2 * r ^ 2 = 2 * δ * r := by rw [hc]; field_simp; ring
    rw [abs_le] at h4
    rw [abs_lt] at h2 h3
    have : ε * r / 16 = δ * r / 4 := by rw [hδ]; ring
    nlinarith
  have hzball : z ∈ ball w r := by rwa [mem_ball, dist_eq_norm]
  have hloc : IsLocalMin (fun x ↦ k x + q x) z :=
    hmin.isLocalMin (mem_of_superset (isOpen_ball.mem_nhds hzball) ball_subset_closedBall)
  have hb := neg_mem_regularSubdiff_of_isLocalMin_add (hasFDerivAt_quadPerturb a c w z) hloc
  refine ⟨z, hzball, _, hb, ?_⟩
  rw [neg_add, neg_neg, add_sub_cancel_left, norm_neg, norm_smul, innerSL_apply_norm,
    Real.norm_of_nonneg hcpos.le]
  calc c * ‖z - w‖ ≤ c * r := mul_le_mul_of_nonneg_left hzw.le hcpos.le
    _ = ε := by rw [hc, hδ]; field_simp

end Approx

/-! ### Thm. 1.84 -/

section Main

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Rademacher's theorem, local form, for gradients: a Lipschitz mapping into the dual has points
of differentiability arbitrarily close to any point. -/
theorem mem_closure_differentiableAt_dual {g : E → StrongDual ℝ E} {K : ℝ≥0}
    (hg : LipschitzWith K g) (x : E) : x ∈ closure {z | DifferentiableAt ℝ g z} := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  have hae := hg.ae_differentiableAt (μ := Measure.addHaar)
  rw [mem_closure_iff_nhds]
  intro t ht
  by_contra hne
  have h0 : (Measure.addHaar : Measure E) t = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 hae)
    intro z hzt hz
    exact hne ⟨z, hzt, hz⟩
  exact (Measure.measure_pos_of_mem_nhds _ ht).ne' h0

/-- The main step of Thm. 1.84: for `φ` of class `C^{1,1}` around `x₀` whose gradient `φ'` has
directional derivative `g` at `x₀`, `g(u)` is a limiting subgradient of `⟨φ'(·), u⟩` at `x₀`. -/
theorem dirDeriv_mem_subdiff {φ : E → ℝ} {φ' g : E → StrongDual ℝ E} {x₀ : E} {U : Set E}
    {L : ℝ≥0} (hU : U ∈ 𝓝 x₀) (hφ : ∀ x ∈ U, HasFDerivAt φ (φ' x) x)
    (hL : LipschitzOnWith L φ' U) (hg : ∀ u, HasDirDerivAt φ' x₀ u (g u)) (u : E) :
    g u ∈ subdiff (fun x ↦ ((φ' x u : ℝ) : EReal)) x₀ := by
  set h : E → ℝ := fun x ↦ φ' x u with hh
  suffices hε : ∀ ε > 0, ∃ x, ‖x - x₀‖ < ε ∧
      ∃ b ∈ regularSubdiff (fun x ↦ (h x : EReal)) x, ‖b - g u‖ < ε by
    rw [subdiff_eq_outerLimit (φ := fun x ↦ (h x : EReal)) rfl]
    choose x hx b hb hbg using fun k : ℕ ↦ hε (1 / ((k : ℝ) + 1)) Nat.one_div_pos_of_nat
    have hxt : Tendsto x atTop (𝓝 x₀) := tendsto_iff_norm_sub_tendsto_zero.2
      (squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ (hx k).le)
        tendsto_one_div_add_atTop_nhds_zero_nat)
    refine ⟨x, b, ?_, ?_, hb⟩
    · rw [tendsto_funNhds_iff]
      refine ⟨hxt, ?_⟩
      have hcont : ContinuousAt (fun x ↦ (h x : EReal)) x₀ :=
        continuous_coe_real_ereal.continuousAt.comp
          ((ContinuousLinearMap.apply ℝ ℝ u).continuous.continuousAt.comp
            (hL.continuousOn.continuousAt hU))
      exact hcont.tendsto.comp hxt
    · exact tendsto_iff_norm_sub_tendsto_zero.2
        (squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ (hbg k).le)
          tendsto_one_div_add_atTop_nhds_zero_nat)
  intro ε hε
  have hgL : LipschitzWith L g := dirDeriv_lipschitz hU hL hg
  -- a point of differentiability `w` of `g` close to `u`
  obtain ⟨w, hwd, hwu⟩ : ∃ w, DifferentiableAt ℝ g w ∧
      dist w u < min 1 (ε / (4 * (L + 1))) := by
    obtain ⟨w, hwd, hw⟩ :=
      Metric.mem_closure_iff.1 (mem_closure_differentiableAt_dual hgL u) _
        (show (0 : ℝ) < min 1 (ε / (4 * (L + 1))) by positivity)
    exact ⟨w, hwd, by rw [dist_comm]; exact hw⟩
  have hwu1 : ‖w - u‖ < 1 := by rw [← dist_eq_norm]; exact hwu.trans_le (min_le_left _ _)
  have hwu2 : ‖u - w‖ < ε / (4 * (L + 1)) := by
    rw [← dist_eq_norm, dist_comm]; exact hwu.trans_le (min_le_right _ _)
  obtain ⟨A, hA⟩ : ∃ A, HasFDerivAt g A w := ⟨_, hwd.hasFDerivAt⟩
  -- `A` is symmetric, `Aw = g(w)` and `‖A‖ ≤ L`
  obtain ⟨Ψ, hΨ⟩ := exists_hasFDerivAt_dirDeriv hU hφ hL hg (‖u‖ + 2)
  have hwball : w ∈ ball (0 : E) (‖u‖ + 2) := by
    rw [mem_ball, dist_zero_right]
    have := norm_le_norm_add_norm_sub' w u
    linarith
  have hsymm : ∀ v d, A v d = A d v :=
    second_derivative_symmetric_of_eventually (f := Ψ)
      (Filter.eventually_of_mem (isOpen_ball.mem_nhds hwball) hΨ) hA
  have heuler : A w = g w :=
    HasFDerivAt.apply_self_of_homogeneous (fun s hs ↦ dirDeriv_smul hg hs w) hA
  have hAn : ‖A‖ ≤ L := hA.le_of_lipschitz hgL
  -- the gradient `a = Au` of `⟨g(·), u⟩` at `w` is close to `g(u)`
  have hH : HasFDerivAt (fun z ↦ g z u) ((ContinuousLinearMap.apply ℝ ℝ u).comp A) w :=
    (ContinuousLinearMap.apply ℝ ℝ u).hasFDerivAt.comp w hA
  set a := (ContinuousLinearMap.apply ℝ ℝ u).comp A with ha
  have haA : a = A u := by
    ext d
    simp [ha, hsymm d u]
  have hag : ‖a - g u‖ < ε / 2 := by
    have e : a - g u = A (u - w) + (g w - g u) := by rw [haA, map_sub, heuler]; abel
    have h1 : ‖A (u - w)‖ ≤ L * ‖u - w‖ :=
      (A.le_opNorm _).trans (mul_le_mul_of_nonneg_right hAn (norm_nonneg _))
    have h2 : ‖g w - g u‖ ≤ L * ‖u - w‖ := by
      rw [← dist_eq_norm, ← dist_eq_norm, dist_comm u w]; exact hgL.dist_le_mul w u
    have h3 : (L : ℝ) * ‖u - w‖ < ε / 4 := by
      calc (L : ℝ) * ‖u - w‖ ≤ (L + 1) * ‖u - w‖ :=
            mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
        _ < (L + 1) * (ε / (4 * (L + 1))) := mul_lt_mul_of_pos_left hwu2 (by positivity)
        _ = ε / 4 := by field_simp
    rw [e]
    linarith [norm_add_le (A (u - w)) (g w - g u)]
  -- approximate `a` by regular subgradients of the blow-ups of `h`
  obtain ⟨r, hr, happrox⟩ := exists_regularSubdiff_near_of_hasFDerivAt hH (half_pos hε)
  obtain ⟨r', hr'⟩ : ∃ r', r' = min r 1 := ⟨_, rfl⟩
  have hunif := tendstoUniformlyOn_blowUp hU hL hg (isCompact_closedBall w r)
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  have hsmall : Tendsto (fun t : ℝ ↦ t * (‖w‖ + r)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ ↦ t * (‖w‖ + r)) (𝓝 0) (𝓝 (0 * (‖w‖ + r))) :=
      (continuous_mul_const _).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  obtain ⟨t, ht, htU, htε, htpos⟩ := ((hunif (ε / 2 * r / 16 / (‖u‖ + 1)) (by positivity)).and
    ((eventually_add_smul_mem hU (‖w‖ + r)).and ((hsmall.eventually (gt_mem_nhds hε)).and
      self_mem_nhdsWithin))).exists
  have htpos : (0 : ℝ) < t := htpos
  have hkeq : ∀ z, blowUp h x₀ t z = blowUp φ' x₀ t z u := fun z ↦ by simp [blowUp, hh]
  have hsub : closedBall w r ⊆ closedBall (0 : E) (‖w‖ + r) := by
    intro z hz
    rw [mem_closedBall, dist_zero_right]
    rw [mem_closedBall, dist_eq_norm] at hz
    have := norm_le_norm_add_norm_sub' z w
    linarith
  have hkc : ContinuousOn (blowUp h x₀ t) (closedBall w r) := by
    have := ((lipschitzOnWith_blowUp hL htpos fun z hz ↦ htU z (hsub hz)).continuousOn).clm_apply
      (continuousOn_const (c := u))
    exact this.congr fun z _ ↦ hkeq z
  have hkH : ∀ z ∈ closedBall w r, |blowUp h x₀ t z - g z u| < ε / 2 * r / 16 := by
    intro z hz
    have hd := ht z hz
    rw [dist_eq_norm] at hd
    rw [hkeq, abs_sub_comm, show g z u - blowUp φ' x₀ t z u = (g z - blowUp φ' x₀ t z) u by
      simp, ← Real.norm_eq_abs]
    calc ‖(g z - blowUp φ' x₀ t z) u‖ ≤ ‖g z - blowUp φ' x₀ t z‖ * ‖u‖ := le_opNorm _ _
      _ ≤ ‖g z - blowUp φ' x₀ t z‖ * (‖u‖ + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      _ < ε / 2 * r / 16 / (‖u‖ + 1) * (‖u‖ + 1) :=
        mul_lt_mul_of_pos_right hd (by positivity)
      _ = ε / 2 * r / 16 := by field_simp
  obtain ⟨z, hz, b, hb, hba⟩ := happrox _ hkc hkH
  refine ⟨x₀ + t • z, ?_, b, mem_regularSubdiff_of_mem_regularSubdiff_blowUp htpos hb, ?_⟩
  · rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg htpos.le]
    have hz' : ‖z‖ ≤ ‖w‖ + r := by
      have := hsub (ball_subset_closedBall hz)
      rwa [mem_closedBall, dist_zero_right] at this
    calc t * ‖z‖ ≤ t * (‖w‖ + r) := mul_le_mul_of_nonneg_left hz' htpos.le
      _ < ε := htε
  · calc ‖b - g u‖ = ‖(b - a) + (a - g u)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖b - a‖ + ‖a - g u‖ := norm_add_le _ _
      _ < ε := by linarith

/-- [Mordukhovich 2024, Thm. 1.84, (1.111)] (second-order relations for `C^{1,1}` functions):
if `φ` is of class `C^{1,1}` around `x̄` and its gradient is directionally differentiable at `x̄`,
then `∂²_D φ(x̄)(u) ⊆ ∂²φ(x̄)(u)`. In fact `∂²_D φ(x̄)(u) ⊆ {(∇φ)'(x̄; u)}`, and
`(∇φ)'(x̄; u) ∈ ∂²φ(x̄)(u)`. -/
theorem subgradGraphDeriv_subset_secondOrderSubdiff {φ : E → ℝ} {φ' : E → StrongDual ℝ E}
    {x₀ : E} {U : Set E} {L : ℝ≥0} (hU : U ∈ 𝓝 x₀) (hφ : ∀ x ∈ U, HasFDerivAt φ (φ' x) x)
    (hL : LipschitzOnWith L φ' U) (hdir : DirDifferentiableAt φ' x₀) (u : E) :
    subgradGraphDeriv (fun x ↦ (φ x : EReal)) x₀ (φ' x₀) u ⊆
      secondOrderSubdiff (fun x ↦ (φ x : EReal)) x₀ (φ' x₀) u := by
  choose g hg using hdir
  intro v hv
  have hsub : subgradGraphDeriv (fun x ↦ (φ x : EReal)) x₀ (φ' x₀) u =
      graphDeriv (fun x ↦ {φ' x}) x₀ (φ' x₀) u :=
    graphDeriv_congr (eventually_subdiff_eq_singleton_of_lipschitz hU hφ hL) _ _
  have hv' : v = g u := graphDeriv_subset_of_hasDirDerivAt hU hL (hg u) (hsub ▸ hv)
  rw [hv', secondOrderSubdiff_of_lipschitz hU hφ hL u]
  exact dirDeriv_mem_subdiff hU hφ hL hg u

end Main

end VariationalAnalysis
