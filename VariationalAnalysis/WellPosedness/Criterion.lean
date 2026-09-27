/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import VariationalAnalysis.Principle.Variational
import VariationalAnalysis.Subdifferential.Bridge
import VariationalAnalysis.Subdifferential.SumRule
import VariationalAnalysis.WellPosedness.Coderivative

/-!
# Coderivative criteria for well-posedness (the Mordukhovich criterion)

This file completes [Mordukhovich 2018, Thm. 3.3]: for `S : E ⇉ F` between finite-dimensional
spaces with `gph S` locally closed around `(x₀, y₀) ∈ gph S` (the book's standing closed-graph
assumption),

* (i) `S` has the covering property around `(x₀, y₀)` iff `ker D*S(x₀, y₀) = {0}` (3.6), and
  `cov S (x₀, y₀) = inf {‖u‖ | u ∈ D*S(x₀, y₀)(v), ‖v‖ = 1}` (3.7);
* (ii) `S` is metrically regular around `(x₀, y₀)` iff (3.6) holds, and
  `reg S (x₀, y₀) = ‖D*S(x₀, y₀)⁻¹‖ = ‖D*S⁻¹(y₀, x₀)‖` (3.8);
* (iii) `S` is Lipschitz-like around `(x₀, y₀)` iff `D*S(x₀, y₀)(0) = {0}` (3.9), and
  `lip S (x₀, y₀) = ‖D*S(x₀, y₀)‖` (3.10).

The necessity halves (Step 1 and its consequences) are in
`VariationalAnalysis.WellPosedness.Coderivative`; this file proves Step 2 (sufficiency) and
assembles Step 3. The exact bounds are equalities in `ℝ≥0∞`, valid also when the properties fail
(`cov = 0`, `reg = lip = ∞`, and correspondingly `inf = 0` or `‖·‖ = ∞`).

## Step 2 and the norms

The book negates the covering property (3.1), applies the general variational principle
(Thm. 2.12) with the weighted norm `θ(x, y) = ‖x‖ + r ‖y‖`, the semi-Lipschitzian sum rule
(Cor. 2.20) and the subgradients of the Euclidean norm, and passes to the limit by the
robustness of the normal cone (Prop. 1.3). Here the same variational argument is used to prove
directly that every `μ` with `μ⁻¹ < a(S, x₀, y₀)` is a metric regularity modulus
(`metricallyRegularWith_of_forall_mul_norm_le`, via Step 1 of Thm. 3.2), and covering with
every modulus `κ < a(S, x₀, y₀)` (3.14) follows from Thm. 3.2. The compactness/robustness part
is isolated in `eventually_mul_norm_le_of_mem_coderiv`: `c ‖v‖ ≤ ‖u‖` for `u ∈ D*S(x, y)(v)` at
all graph points near `(x₀, y₀)` whenever `c < a(S, x₀, y₀)`.

Instead of the explicit subdifferential of the Euclidean norm, only the convex subgradient
inequality of `‖y - z‖ + μ⁻¹ (‖x - x̄‖ + r ‖y - ȳ‖)` along two directions is used: it gives
`‖u‖ ≤ μ⁻¹` and `‖v‖ ≥ 1 - r μ⁻¹` for the coderivative pair produced by Cor. 2.20. The argument
therefore works for arbitrary norms on `E` and `F`, the maximum norm on `E × F` (Mathlib's) and
the dual norms on `StrongDual ℝ E`, `StrongDual ℝ F`; nothing depends on the Euclidean structure.

## Hypotheses

* Local closedness of `gph S` around `(x₀, y₀)` and finite dimensions of `E`, `F`: everywhere in
  Step 2 (Thm. 2.12 needs coercivity of `θ` on `E × F`, Prop. 1.3 needs compactness in the duals).
* `Nontrivial E` only for (i) (covering), exactly as in Thm. 3.2: for `E = {0}` and
  `S 0 = ball 0 1 ⊆ ℝ` the kernel is `{0}` at `(0, 0)` but `S` has no covering property.
  (ii) and (iii) need no nontriviality; (iii) is (ii) for `S⁻¹` (`locallyClosed_graph_invMap`).

## Main results

* `posHomLowerNorm_coderiv_pos`: (3.6) implies `a(S, x₀, y₀) > 0` [Mordukhovich 2018, (3.14)].
* `eventually_mul_norm_le_of_mem_coderiv`, `exists_mem_coderiv_of_tendsto`: robustness part of
  Step 2.
* `metricallyRegularWith_of_forall_mul_norm_le`: variational part of Step 2.
* `metricallyRegularWith_of_inv_lt_posHomLowerNorm`, `hasCoveringWith_of_lt_posHomLowerNorm`,
  `posHomLowerNorm_le_covBound`: Step 2 of the proof of Thm. 3.3, (3.14).
* `hasCoveringAt_iff_coderivKer_eq`, `covBound_eq_posHomLowerNorm`: Thm. 3.3(i), (3.6)–(3.7).
* `metricallyRegularAt_iff_coderivKer_eq`, `regBound_eq_inv_posHomLowerNorm`,
  `regBound_eq_posHomNorm_invMap_coderiv`, `regBound_eq_posHomNorm_coderiv_invMap`:
  Thm. 3.3(ii), (3.6), (3.8) [Clason–Valkonen, Cor. 27.12].
* `metricallyRegularAt_iff_forall_zero_mem_coderiv`: Thm. 3.3(ii) in the form
  "`0 ∈ D*S(x₀, y₀)(v)` implies `v = 0`", as used for bilevel programs.
* `lipschitzLikeAt_iff_coderiv_zero_eq`, `lipschitzLikeAt_iff_forall_mem_coderiv_zero`,
  `lipBound_eq_posHomNorm_coderiv`, `lipschitzLikeWith_of_posHomNorm_lt`: Thm. 3.3(iii),
  (3.9)–(3.10) (Mordukhovich criterion) [Clason–Valkonen, Cor. 27.16].
-/

open Filter Topology Set Metric
open scoped NNReal ENNReal

namespace VariationalAnalysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {S : E → Set F} {x₀ : E} {y₀ : F}


section Auxiliary

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- The indicator function takes values in `{0, ⊤}`, hence is nonnegative. -/
theorem convex_indicator_nonneg {α : Type*} (Ω : Set α) (x : α) :
    (0 : EReal) ≤ Ω.convex_indicator x := by
  by_cases hx : x ∈ Ω
  · rw [convex_indicator_of_mem hx]; rfl
  · rw [convex_indicator_of_notMem hx]; exact le_top

omit [NormedSpace ℝ X] in
/-- The epigraph of the indicator function of a set locally closed around `z` is locally closed
around `(z, 0)`. -/
theorem isClosed_epi_convex_indicator_inter_closedBall {Ω : Set X} {z : X}
    (h : ∃ ρ > 0, IsClosed (Ω ∩ closedBall z ρ)) :
    ∃ ρ > 0, IsClosed (Ω.convex_indicator.Epi univ ∩ closedBall ((z, 0) : X × ℝ) ρ) := by
  obtain ⟨ρ, hρ, hcl⟩ := h
  refine ⟨ρ, hρ, ?_⟩
  rw [epi_convex_indicator]
  have : (Ω ×ˢ Ici (0 : ℝ)) ∩ closedBall ((z, 0) : X × ℝ) ρ =
      ((Ω ∩ closedBall z ρ) ×ˢ Ici 0) ∩ closedBall ((z, 0) : X × ℝ) ρ := by
    ext ⟨a, b⟩
    simp only [mem_inter_iff, mem_prod, mem_closedBall, Prod.dist_eq, max_le_iff]
    tauto
  rw [this]
  exact (hcl.prod isClosed_Ici).inter isClosed_closedBall

/-- `q ↦ ‖L q - c‖` is convex for a linear map `L`. -/
theorem convexOn_norm_map_sub (L : X →ₗ[ℝ] Y) (c : Y) :
    ConvexOn ℝ univ (fun q ↦ ‖L q - c‖) := by
  refine ⟨convex_univ, fun p _ q _ a b ha hb hab ↦ ?_⟩
  obtain rfl : b = 1 - a := by linarith
  have : L (a • p + (1 - a) • q) - c = a • (L p - c) + (1 - a) • (L q - c) := by
    rw [map_add, map_smul, map_smul]; module
  simp only [smul_eq_mul]
  rw [this]
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]

end Auxiliary

section Robustness

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- Robustness of the coderivative with normalized directions [Mordukhovich 2018, proof of
Thm. 3.3, Step 2]: if `uₖ ∈ D*S(pₖ)(vₖ)` with `pₖ → (x₀, y₀)` in `gph S`, `‖vₖ‖ = 1` and
`‖uₖ‖ ≤ cₖ → c₀`, then some `u ∈ D*S(x₀, y₀)(v)` has `‖v‖ = 1` and `‖u‖ ≤ c₀`. -/
theorem exists_mem_coderiv_of_tendsto (h₀ : y₀ ∈ S x₀) {p : ℕ → E × F}
    (hp : Tendsto p atTop (𝓝 (x₀, y₀))) (hpS : ∀ k, p k ∈ graph S) {u : ℕ → StrongDual ℝ E}
    {v : ℕ → StrongDual ℝ F} (huv : ∀ k, u k ∈ coderiv S (p k).1 (p k).2 (v k))
    (hv : ∀ k, ‖v k‖ = 1) {c : ℕ → ℝ} {c₀ : ℝ} (hc : Tendsto c atTop (𝓝 c₀))
    (hu : ∀ k, ‖u k‖ ≤ c k) :
    ∃ v₀ : StrongDual ℝ F, ‖v₀‖ = 1 ∧ ∃ u₀ ∈ coderiv S x₀ y₀ v₀, ‖u₀‖ ≤ c₀ := by
  obtain ⟨M, hM⟩ := hc.bddAbove_range
  have hK : IsCompact (closedBall (0 : StrongDual ℝ E) M ×ˢ sphere (0 : StrongDual ℝ F) 1) :=
    (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  obtain ⟨q, hq, φ, hφ, hlim⟩ := hK.tendsto_subseq (x := fun k ↦ (u k, v k)) fun k ↦
    ⟨by simpa using (hu k).trans (hM ⟨k, rfl⟩), by simpa using hv k⟩
  have hφ' := hφ.tendsto_atTop
  have h1 : Tendsto (fun k ↦ u (φ k)) atTop (𝓝 q.1) :=
    (continuous_fst.tendsto _).comp hlim
  have h2 : Tendsto (fun k ↦ v (φ k)) atTop (𝓝 q.2) :=
    (continuous_snd.tendsto _).comp hlim
  refine ⟨q.2, by simpa using hq.2, q.1, ?_, le_of_tendsto_of_tendsto' h1.norm (hc.comp hφ')
    fun k ↦ hu (φ k)⟩
  show q.1.coprod (-q.2) ∈ normalCone (graph S) (x₀, y₀)
  rw [normalCone_eq_outerLimit_normalCone (show (x₀, y₀) ∈ graph S from h₀)]
  exact ⟨fun k ↦ p (φ k), fun k ↦ (u (φ k)).coprod (-v (φ k)),
    tendsto_nhdsWithin_iff.2 ⟨hp.comp hφ', Eventually.of_forall fun k ↦ hpS _⟩,
    tendsto_coprod h1 h2.neg, fun k ↦ huv (φ k)⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Below-the-infimum form of `posHomLowerNorm`: if `inf {‖y‖ | y ∈ H x, ‖x‖ = 1} < c`, some
`y ∈ H x` with `‖x‖ = 1` has `‖y‖ < c`. -/
theorem exists_of_posHomLowerNorm_lt {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    {H : X → Set Y} {c : ℝ≥0∞} (h : posHomLowerNorm H < c) :
    ∃ x, ‖x‖ = 1 ∧ ∃ y ∈ H x, (‖y‖₊ : ℝ≥0∞) < c := by
  simpa [posHomLowerNorm, iInf_lt_iff] using h

/-- [Mordukhovich 2018, proof of Thm. 3.3, Step 2]: the kernel condition (3.6) gives
`a(S, x₀, y₀) = inf {‖u‖ | u ∈ D*S(x₀, y₀)(v), ‖v‖ = 1} > 0` (3.14), by the robustness of the
normal cone. -/
theorem posHomLowerNorm_coderiv_pos (h₀ : y₀ ∈ S x₀) (hker : coderivKer S x₀ y₀ = {0}) :
    0 < posHomLowerNorm (coderiv S x₀ y₀) := by
  by_contra hle
  rw [not_lt, nonpos_iff_eq_zero] at hle
  have key : ∀ k : ℕ, ∃ v : StrongDual ℝ F, ‖v‖ = 1 ∧ ∃ u ∈ coderiv S x₀ y₀ v,
      ‖u‖ ≤ 1 / ((k : ℝ) + 1) := fun k ↦ by
    obtain ⟨v, hv, u, hu, hlt⟩ := exists_of_posHomLowerNorm_lt (H := coderiv S x₀ y₀)
      (c := ENNReal.ofReal (1 / ((k : ℝ) + 1))) (by rw [hle]; simp; positivity)
    refine ⟨v, hv, u, hu, ?_⟩
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm] at hlt
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hlt |>.le
  choose v hv u hu hle using key
  obtain ⟨v₀, hv₀, u₀, hu₀, hle₀⟩ := exists_mem_coderiv_of_tendsto (p := fun _ ↦ (x₀, y₀)) h₀
    tendsto_const_nhds (fun _ ↦ h₀) hu hv tendsto_one_div_add_atTop_nhds_zero_nat hle
  have hu0 : u₀ = 0 := norm_le_zero_iff.1 hle₀
  subst hu0
  have : v₀ ∈ coderivKer S x₀ y₀ := hu₀
  rw [hker, mem_singleton_iff] at this
  simp [this] at hv₀

/-- [Mordukhovich 2018, proof of Thm. 3.3, Step 2], uniform form: if
`c < a(S, x₀, y₀) = inf {‖u‖ | u ∈ D*S(x₀, y₀)(v), ‖v‖ = 1}`, then `c ‖v‖ ≤ ‖u‖` for all
`u ∈ D*S(x, y)(v)` and all `(x, y) ∈ gph S` near `(x₀, y₀)`. This is the compactness and
robustness argument that ends Step 2 of the book (Prop. 1.3). -/
theorem eventually_mul_norm_le_of_mem_coderiv (h₀ : y₀ ∈ S x₀) {c : ℝ}
    (hc : ENNReal.ofReal c < posHomLowerNorm (coderiv S x₀ y₀)) :
    ∀ᶠ p in 𝓝 (x₀, y₀), p ∈ graph S → ∀ (v : StrongDual ℝ F) (u : StrongDual ℝ E),
      u ∈ coderiv S p.1 p.2 v → c * ‖v‖ ≤ ‖u‖ := by
  by_contra hev
  rw [Filter.not_eventually] at hev
  have key : ∀ k : ℕ, ∃ p : E × F, dist p (x₀, y₀) < 1 / ((k : ℝ) + 1) ∧ p ∈ graph S ∧
      ∃ v : StrongDual ℝ F, ‖v‖ = 1 ∧ ∃ u ∈ coderiv S p.1 p.2 v, ‖u‖ ≤ c := fun k ↦ by
    obtain ⟨p, hp, hpb⟩ := (hev.and_eventually (ball_mem_nhds (x₀, y₀)
      (Nat.one_div_pos_of_nat (α := ℝ) (n := k)))).exists
    push Not at hp
    obtain ⟨hpS, v, u, hu, hlt⟩ := hp
    have hv0 : v ≠ 0 := by
      rintro rfl
      simp only [norm_zero, mul_zero] at hlt
      exact (norm_nonneg u).not_gt hlt
    have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
    refine ⟨p, hpb, hpS, ‖v‖⁻¹ • v, ?_, ‖v‖⁻¹ • u, smul_mem_coderiv hu (by positivity), ?_⟩
    · rw [norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ hvpos.ne']
    · rw [norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_le_iff₀ hvpos, mul_comm]
      exact hlt.le
  choose p hpd hpS v hv u hu hle using key
  have hp : Tendsto p atTop (𝓝 (x₀, y₀)) :=
    tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ ↦ dist_nonneg) (fun k ↦ (hpd k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat)
  obtain ⟨v₀, hv₀, u₀, hu₀, hle₀⟩ :=
    exists_mem_coderiv_of_tendsto h₀ hp hpS hu hv tendsto_const_nhds hle
  have : posHomLowerNorm (coderiv S x₀ y₀) ≤ ENNReal.ofReal c := by
    refine (posHomLowerNorm_le_nnnorm hv₀ hu₀).trans ?_
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
    exact ENNReal.ofReal_le_ofReal hle₀
  exact (hc.trans_le this).false

end Robustness

section Sufficiency

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- The weighted norm `θ(x, y) = ‖x‖ + r ‖y‖` of [Mordukhovich 2018, proof of Thm. 3.3, Step 2]
is coercive. -/
theorem tendsto_norm_add_mul_norm_cocompact [ProperSpace E] [ProperSpace F] {r : ℝ}
    (hr : 0 < r) : Tendsto (fun q : E × F ↦ ‖q.1‖ + r * ‖q.2‖) (cocompact (E × F)) atTop := by
  have hm : 0 < min 1 r := lt_min one_pos hr
  refine tendsto_atTop_mono (fun q ↦ ?_) (tendsto_norm_cocompact_atTop.const_mul_atTop hm)
  rw [Prod.norm_def]
  have h1 := min_le_left 1 r
  have h2 := min_le_right 1 r
  have h3 := norm_nonneg q.1
  have h4 := norm_nonneg q.2
  rcases le_total ‖q.1‖ ‖q.2‖ with h | h
  · rw [max_eq_right h]; nlinarith
  · rw [max_eq_left h]; nlinarith

/-- Step 2 of the proof of Thm. 3.3 of [Mordukhovich 2018] (Ekeland part): let `gph S` be
locally closed around `(x₀, y₀) ∈ gph S`, and let `c ‖v‖ ≤ ‖u‖` for all `u ∈ D*S(x, y)(v)`
and all `(x, y) ∈ gph S` near `(x₀, y₀)`, with `c > 0`. Then `S` is metrically regular around
`(x₀, y₀)` with every modulus `μ > c⁻¹`.

The book negates the covering property and applies Thm. 2.12 with the weighted norm
`θ(x, y) = ‖x‖ + r ‖y‖`; here the same variational argument proves the metric regularity
estimate directly (Step 1 of Thm. 3.2 reduces it to points with `dist(y; S x)` small): for
`w ∈ S x` and `d = ‖y - w‖ > 0`, Thm. 2.12 applied to `‖v - y‖ + δ((u, v); gph S)` with
`ε = d`, `λ = μ d` gives `(u', v') ∈ gph S` with `‖u' - x‖ ≤ μ d`; if `v' ≠ y`, the
semi-Lipschitzian sum rule (Cor. 2.20) and the convex subgradient inequality produce
`-a ∈ D*S(u', v')(b)` with `‖a‖ ≤ μ⁻¹` and `‖b‖ ≥ 1 - r μ⁻¹`, contradicting the bound for
`r < (c μ - 1) / c`. Only the subgradient inequality of the convex function
`‖v - y‖ + μ⁻¹ (‖u - u'‖ + r ‖v - v'‖)` along two directions is used, so the argument works for
any norms on `E` and `F`, with the maximum norm on `E × F`. -/
theorem metricallyRegularWith_of_forall_mul_norm_le
    (hloc : ∃ ρ > 0, IsClosed (graph S ∩ closedBall (x₀, y₀) ρ)) (h₀ : y₀ ∈ S x₀)
    {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hb : ∀ p ∈ graph S, dist p (x₀, y₀) < δ → ∀ (v : StrongDual ℝ F) (u : StrongDual ℝ E),
      u ∈ coderiv S p.1 p.2 v → c * ‖v‖ ≤ ‖u‖)
    {μ : ℝ≥0} (hμ : 1 < c * μ) : MetricallyRegularWith μ S x₀ y₀ := by
  obtain ⟨ρ, hρ, hcl⟩ := hloc
  have hμ0 : (0 : ℝ) < μ := by
    by_contra h
    push Not at h
    nlinarith [μ.coe_nonneg]
  set m := min ρ δ with hm_def
  have hm : 0 < m := lt_min hρ hδ
  set η := m / 3 with hη_def
  set γ := m / (3 * ((μ : ℝ) + 1)) with hγ_def
  have hη : 0 < η := by positivity
  have hγ : 0 < γ := by positivity
  have hμγ : (μ : ℝ) * γ < m / 3 := by
    have : (μ : ℝ) * γ = m / 3 * (μ / (μ + 1)) := by rw [hγ_def]; field_simp
    rw [this]
    exact mul_lt_of_lt_one_right (by positivity) ((div_lt_one (by positivity)).2 (by linarith))
  have hγm : γ ≤ m / 3 := by
    rw [hγ_def, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set r := (c * μ - 1) / (2 * c) with hr_def
  have hr : 0 < r := div_pos (by linarith) (by positivity)
  have hcr : c * r = (c * μ - 1) / 2 := by rw [hr_def]; field_simp
  refine metricallyRegularWith_of_forall_dist_lt (by exact_mod_cast hμ0) h₀ hγ
    (ball_mem_nhds x₀ hη) (ball_mem_nhds y₀ hη) fun x hx y hy w hw hwy ε hε ↦ ?_
  have hx' : dist x x₀ < η := hx
  have hy' : dist y y₀ < η := hy
  rcases (dist_nonneg (x := y) (y := w)).eq_or_lt with hd | hd
  · refine ⟨x, ?_, ?_⟩
    · rw [dist_eq_zero.1 hd.symm]; exact hw
    · rw [dist_self, ← hd, mul_zero, zero_add]; exact hε
  set d := dist y w with hd_def
  set Ω := graph S ∩ closedBall (x₀, y₀) ρ with hΩ_def
  set φ : E × F → EReal := fun q ↦ Ω.convex_indicator q + ((‖q.2 - y‖ : ℝ) : EReal)
    with hφ_def
  set θ : E × F → ℝ := fun q ↦ ‖q.1‖ + r * ‖q.2‖ with hθ_def
  have hφlsc : LowerSemicontinuous φ :=
    (lowerSemicontinuous_convex_indicator_of_closed hcl).add'
      (continuous_coe_real_ereal.comp
        ((continuous_snd.sub continuous_const).norm)).lowerSemicontinuous
      fun q ↦ EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
  have hφnn : ∀ q, ((0 : ℝ) : EReal) ≤ φ q := fun q ↦
    add_nonneg (convex_indicator_nonneg _ _) (EReal.coe_nonneg.2 (norm_nonneg _))
  have hxwΩ : (x, w) ∈ Ω := by
    refine ⟨hw, ?_⟩
    rw [mem_closedBall, Prod.dist_eq, max_le_iff]
    have := dist_triangle w y y₀
    rw [dist_comm w y] at this
    constructor <;> linarith [min_le_left ρ δ]
  have hφxw : φ (x, w) = ((d : ℝ) : EReal) := by
    simp only [hφ_def, convex_indicator_of_mem hxwΩ]
    rw [← EReal.coe_add, zero_add, ← dist_eq_norm, dist_comm]
  obtain ⟨z, -, hle, hθz, hmin, -⟩ := general_variational_principle_subadditive
    (x₀ := (x, w)) (ε := d) (ρ := μ * d) (θ := θ) hφlsc ⟨0, hφnn⟩
    (by fun_prop : Continuous θ).lowerSemicontinuous (fun q ↦ by positivity)
    (by simp [hθ_def])
    (fun a b ↦ by
      simp only [hθ_def, Prod.fst_add, Prod.snd_add]
      have := mul_le_mul_of_nonneg_left (norm_add_le a.2 b.2) hr.le
      linarith [norm_add_le a.1 b.1])
    (tendsto_norm_add_mul_norm_cocompact hr) hd (by positivity)
    (by rw [hφxw]; exact EReal.coe_ne_top _)
    (by
      rw [hφxw]
      calc ((d : ℝ) : EReal) = 0 + (d : EReal) := (zero_add _).symm
        _ ≤ (⨅ q, φ q) + d := add_le_add_left (le_iInf fun q ↦ hφnn q) _)
  have hzΩ : z ∈ Ω := by
    by_contra hz
    have : φ z = ⊤ := by simp only [hφ_def, convex_indicator_of_notMem hz, EReal.top_add_coe]
    rw [this, hφxw] at hle
    exact EReal.coe_ne_top _ (top_le_iff.1 hle)
  have hφz : φ z = ((‖z.2 - y‖ : ℝ) : EReal) := by
    simp only [hφ_def, convex_indicator_of_mem hzΩ]
    rw [← EReal.coe_add, zero_add]
  have hzy : ‖z.2 - y‖ ≤ d := by
    rw [hφz, hφxw] at hle
    exact EReal.coe_le_coe_iff.1 hle
  have hzx : ‖z.1 - x‖ ≤ μ * d := by
    have : θ (z - (x, w)) = ‖z.1 - x‖ + r * ‖z.2 - w‖ := rfl
    nlinarith [norm_nonneg (z.2 - w)]
  have hdγ : d < γ := hwy
  have hzdist : dist z (x₀, y₀) < m := by
    rw [Prod.dist_eq, max_lt_iff]
    have h1 := dist_triangle z.1 x x₀
    have h2 := dist_triangle z.2 y y₀
    rw [dist_eq_norm z.1 x] at h1
    rw [dist_eq_norm z.2 y] at h2
    have h3 : (μ : ℝ) * d ≤ μ * γ := by gcongr
    constructor <;> linarith
  have hzρ : dist z (x₀, y₀) < ρ := hzdist.trans_le (min_le_left _ _)
  by_cases hzy0 : z.2 = y
  · refine ⟨z.1, ?_, ?_⟩
    · have : z.2 ∈ S z.1 := hzΩ.1
      rwa [hzy0] at this
    · rw [dist_comm, dist_eq_norm]; linarith
  exfalso
  -- `z` is a local minimizer of `δ(·; gph S) + f`
  set κ : ℝ := (μ : ℝ)⁻¹ with hκ_def
  have hκ : 0 < κ := inv_pos.2 hμ0
  set f : E × F → ℝ := fun q ↦ ‖q.2 - y‖ + κ * (‖q.1 - z.1‖ + r * ‖q.2 - z.2‖) with hf_def
  have hcoef : d / (μ * d) = κ := by rw [hκ_def]; field_simp
  have hfz : f z = ‖z.2 - y‖ := by simp [hf_def]
  have hlocmin : IsLocalMin (fun q ↦ (graph S).convex_indicator q + ((f q : ℝ) : EReal)) z := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball.2 hzρ)] with q hq
    by_cases hqS : q ∈ graph S
    · have hqΩ : q ∈ Ω := ⟨hqS, ball_subset_closedBall hq⟩
      have h1 := hmin q
      rw [hφz, hcoef] at h1
      simp only [hφ_def, convex_indicator_of_mem hqΩ] at h1
      rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
      show (graph S).convex_indicator z + ((f z : ℝ) : EReal) ≤
        (graph S).convex_indicator q + ((f q : ℝ) : EReal)
      rw [convex_indicator_of_mem hzΩ.1, convex_indicator_of_mem hqS, ← EReal.coe_add,
        ← EReal.coe_add, EReal.coe_le_coe_iff, hfz]
      have : θ (q - z) = ‖q.1 - z.1‖ + r * ‖q.2 - z.2‖ := rfl
      rw [this] at h1
      simp only [hf_def]
      linarith
    · show (graph S).convex_indicator z + ((f z : ℝ) : EReal) ≤
        (graph S).convex_indicator q + ((f q : ℝ) : EReal)
      rw [convex_indicator_of_notMem hqS, EReal.top_add_coe]
      exact le_top
  have h0 := zero_mem_subdiff_of_isLocalMin hlocmin
    (show (graph S).convex_indicator z + ((f z : ℝ) : EReal) = ((0 + f z : ℝ) : EReal) by
      rw [convex_indicator_of_mem hzΩ.1, ← EReal.coe_add])
  have hL : LipschitzWith (Real.toNNReal (1 + κ + κ * r)) f := by
    refine LipschitzWith.of_dist_le_mul fun p q ↦ ?_
    rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq]
    have h1 := abs_norm_sub_norm_le (p.2 - y) (q.2 - y)
    have h2 := abs_norm_sub_norm_le (p.1 - z.1) (q.1 - z.1)
    have h3 := abs_norm_sub_norm_le (p.2 - z.2) (q.2 - z.2)
    simp only [sub_sub_sub_cancel_right] at h1 h2 h3
    have h4 : ‖p.1 - q.1‖ ≤ dist p q := by rw [dist_eq_norm]; exact norm_fst_le (p - q)
    have h5 : ‖p.2 - q.2‖ ≤ dist p q := by rw [dist_eq_norm]; exact norm_snd_le (p - q)
    rw [abs_le] at h1 h2 h3 ⊢
    have e1 : f p - f q = (‖p.2 - y‖ - ‖q.2 - y‖) + κ * (‖p.1 - z.1‖ - ‖q.1 - z.1‖) +
        κ * r * (‖p.2 - z.2‖ - ‖q.2 - z.2‖) := by simp only [hf_def]; ring
    have k1 := mul_le_mul_of_nonneg_left h2.2 hκ.le
    have k2 := mul_le_mul_of_nonneg_left h2.1 hκ.le
    have k3 := mul_le_mul_of_nonneg_left h3.2 (mul_pos hκ hr).le
    have k4 := mul_le_mul_of_nonneg_left h3.1 (mul_pos hκ hr).le
    have k5 := mul_le_mul_of_nonneg_left h4 hκ.le
    have k6 := mul_le_mul_of_nonneg_left h5 (mul_pos hκ hr).le
    have e3 : (1 + κ + κ * r) * dist p q = dist p q + κ * dist p q + κ * r * dist p q := by ring
    rw [e1, e3]
    constructor <;> linarith
  obtain ⟨n, hn, w', hw', hsum⟩ := subdiff_add_subset_of_lipschitz
    (φ := (graph S).convex_indicator) (f := f) (x₀ := z) (r := 0)
    (convex_indicator_of_mem hzΩ.1)
    (isClosed_epi_convex_indicator_inter_closedBall (locallyClosed_of_dist_lt hcl hzρ)) univ_mem
    hL.lipschitzOnWith h0
  rw [subdiff_convex_indicator] at hn
  have hconv : ConvexOn ℝ univ f := by
    have := (convexOn_norm_map_sub (LinearMap.snd ℝ E F) y).add
      (((convexOn_norm_map_sub (LinearMap.fst ℝ E F) z.1).add
        ((convexOn_norm_map_sub (LinearMap.snd ℝ E F) z.2).smul hr.le)).smul hκ.le)
    exact this.congr fun q _ ↦ by simp [hf_def, smul_eq_mul]
  rw [mem_subdiff_of_convex (convex_epi_of_convexOn hconv) (r := f z) rfl] at hw'
  have hsub' : ∀ q, f z + w' (q - z) ≤ f q := fun q ↦ EReal.coe_le_coe_iff.1 (hw' q)
  set a := w'.comp (ContinuousLinearMap.inl ℝ E F) with ha_def
  set b := w'.comp (ContinuousLinearMap.inr ℝ E F) with hb_def
  have hcod : -a ∈ coderiv S z.1 z.2 b := by
    show (-a).coprod (-b) ∈ normalCone (graph S) (z.1, z.2)
    have : (-a).coprod (-b) = n := by
      rw [eq_neg_of_add_eq_zero_left hsum]
      ext <;> simp [ha_def, hb_def]
    rw [this]
    exact hn
  have ha : ‖a‖ ≤ κ := by
    refine ContinuousLinearMap.opNorm_le_bound _ hκ.le fun e ↦ abs_le.2 ⟨?_, ?_⟩
    · have hq : ((z.1 - e, z.2) : E × F) - z = (-e, 0) := by ext <;> simp
      have := hsub' (z.1 - e, z.2)
      rw [hq, hfz] at this
      have hfq : f (z.1 - e, z.2) = ‖z.2 - y‖ + κ * ‖e‖ := by simp [hf_def]
      have hae : w' (-e, 0) = -a e := by
        rw [ha_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, ← map_neg,
          Prod.neg_mk, neg_zero]
      rw [hfq, hae] at this
      linarith
    · have hq : ((z.1 + e, z.2) : E × F) - z = (e, 0) := by ext <;> simp
      have := hsub' (z.1 + e, z.2)
      rw [hq, hfz] at this
      have hfq : f (z.1 + e, z.2) = ‖z.2 - y‖ + κ * ‖e‖ := by simp [hf_def]
      have hae : w' (e, 0) = a e := rfl
      rw [hfq, hae] at this
      linarith
  have hbnorm : 1 - κ * r ≤ ‖b‖ := by
    have hq : ((z.1, y) : E × F) - z = (0, y - z.2) := by ext <;> simp
    have := hsub' (z.1, y)
    rw [hq, hfz] at this
    have hfq : f (z.1, y) = κ * (r * ‖z.2 - y‖) := by simp [hf_def, norm_sub_rev y z.2]
    have hbe : w' (0, y - z.2) = -b (z.2 - y) := by
      rw [hb_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, ← map_neg]
      congr 1
      ext <;> simp
    rw [hfq, hbe] at this
    have hpos : 0 < ‖z.2 - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hzy0)
    have hle' : b (z.2 - y) ≤ ‖b‖ * ‖z.2 - y‖ :=
      (le_abs_self _).trans (by simpa using b.le_opNorm (z.2 - y))
    have : (1 - κ * r) * ‖z.2 - y‖ ≤ ‖b‖ * ‖z.2 - y‖ := by nlinarith
    exact le_of_mul_le_mul_right this hpos
  have hcb := hb z hzΩ.1 (hzdist.trans_le (min_le_right _ _)) b (-a) hcod
  rw [norm_neg] at hcb
  have hkey : c * (1 - κ * r) ≤ κ := (mul_le_mul_of_nonneg_left hbnorm hc.le).trans
    (hcb.trans ha)
  have hκμ : κ * μ = 1 := inv_mul_cancel₀ hμ0.ne'
  have := mul_le_mul_of_nonneg_right hkey hμ0.le
  have e2 : c * (1 - κ * r) * μ = c * μ - c * r * (κ * μ) := by ring
  rw [e2, hκμ, hcr] at this
  linarith

end Sufficiency

section Criterion

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- Step 2 of the proof of Thm. 3.3 of [Mordukhovich 2018], regularity form: if `gph S` is
locally closed around `(x₀, y₀) ∈ gph S`, every `μ` with
`μ⁻¹ < a(S, x₀, y₀) = inf {‖u‖ | u ∈ D*S(x₀, y₀)(v), ‖v‖ = 1}` is a metric regularity modulus of
`S` around `(x₀, y₀)`. -/
theorem metricallyRegularWith_of_inv_lt_posHomLowerNorm
    (hloc : ∃ ρ > 0, IsClosed (graph S ∩ closedBall (x₀, y₀) ρ)) (h₀ : y₀ ∈ S x₀) {μ : ℝ≥0}
    (hμ : (μ : ℝ≥0∞)⁻¹ < posHomLowerNorm (coderiv S x₀ y₀)) : MetricallyRegularWith μ S x₀ y₀ := by
  obtain ⟨c, hc1, hc2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hμ
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    simp at hc1
  have hc0 : (0 : ℝ) < c := by
    have : (0 : ℝ≥0∞) < c := (zero_le (a := (μ : ℝ≥0∞)⁻¹)).trans_lt hc1
    exact_mod_cast this
  have hμc : 1 < (c : ℝ) * μ := by
    rw [← ENNReal.coe_inv hμ0, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, NNReal.coe_inv] at hc1
    have hμpos : (0 : ℝ) < μ := by exact_mod_cast pos_iff_ne_zero.2 hμ0
    rw [inv_lt_iff_one_lt_mul₀ hμpos] at hc1
    exact hc1
  have hev := eventually_mul_norm_le_of_mem_coderiv h₀ (c := c)
    (by rwa [ENNReal.ofReal_coe_nnreal])
  obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.1 hev
  exact metricallyRegularWith_of_forall_mul_norm_le hloc h₀ hc0 hδ
    (fun p hp hpd v u hu ↦ hδb hpd hp v u hu) hμc

/-- Step 2 of the proof of Thm. 3.3 of [Mordukhovich 2018] ((3.14), covering form): if `gph S`
is locally closed around `(x₀, y₀) ∈ gph S`, every `0 < κ < a(S, x₀, y₀)` is a covering modulus
of `S` around `(x₀, y₀)`. The domain space must be nontrivial (see
`VariationalAnalysis.WellPosedness.Basic`). -/
theorem hasCoveringWith_of_lt_posHomLowerNorm [Nontrivial E]
    (hloc : ∃ ρ > 0, IsClosed (graph S ∩ closedBall (x₀, y₀) ρ)) (h₀ : y₀ ∈ S x₀) {κ : ℝ≥0}
    (hκ : 0 < κ) (hκa : (κ : ℝ≥0∞) < posHomLowerNorm (coderiv S x₀ y₀)) :
    HasCoveringWith κ S x₀ y₀ := by
  obtain ⟨κ', h1, h2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hκa
  have h1' : κ < κ' := by exact_mod_cast h1
  have hκ'0 : κ' ≠ 0 := (hκ.trans h1').ne'
  refine (metricallyRegularWith_of_inv_lt_posHomLowerNorm hloc h₀ (μ := κ'⁻¹) ?_).hasCoveringWith
    hκ ?_
  · rwa [← ENNReal.coe_inv (inv_ne_zero hκ'0), inv_inv]
  · rw [← div_eq_mul_inv]
    exact (div_lt_one (pos_iff_ne_zero.2 hκ'0)).2 h1'

/-- (3.14) of [Mordukhovich 2018] (Step 2 of the proof of Thm. 3.3):
`inf {‖u‖ | u ∈ D*S(x₀, y₀)(v), ‖v‖ = 1} ≤ cov S (x₀, y₀)` for `gph S` locally closed around
`(x₀, y₀) ∈ gph S` (nontrivial domain space). -/
theorem posHomLowerNorm_le_covBound [Nontrivial E]
    (hloc : ∃ ρ > 0, IsClosed (graph S ∩ closedBall (x₀, y₀) ρ)) (h₀ : y₀ ∈ S x₀) :
    posHomLowerNorm (coderiv S x₀ y₀) ≤ covBound S x₀ y₀ :=
  le_covBound_of_forall_lt fun _ hκ hκa ↦ hasCoveringWith_of_lt_posHomLowerNorm hloc h₀ hκ hκa

/-- Thm. 3.3(ii) of [Mordukhovich 2018], exact bound in the form of (3.7):
`reg S (x₀, y₀) = (inf {‖u‖ | u ∈ D*S(x₀, y₀)(v), ‖v‖ = 1})⁻¹` for `gph S` locally closed
around `(x₀, y₀) ∈ gph S`, in `ℝ≥0∞` (both sides are `∞` when `S` is not metrically regular). -/
theorem regBound_eq_inv_posHomLowerNorm
    (hloc : ∃ ρ > 0, IsClosed (graph S ∩ closedBall (x₀, y₀) ρ)) (h₀ : y₀ ∈ S x₀) :
    regBound S x₀ y₀ = (posHomLowerNorm (coderiv S x₀ y₀))⁻¹ := by
  refine le_antisymm (regBound_le_of_forall_lt fun μ hμ ↦ ?_) ?_
  · exact metricallyRegularWith_of_inv_lt_posHomLowerNorm hloc h₀ (ENNReal.inv_lt_iff_inv_lt.1 hμ)
  · exact ENNReal.inv_le_iff_inv_le.1 (inv_regBound_le_posHomLowerNorm h₀)

/-- Thm. 3.3(ii) of [Mordukhovich 2018], exact bound (3.8), first equality:
`reg S (x₀, y₀) = ‖D*S(x₀, y₀)⁻¹‖` for `gph S` locally closed around `(x₀, y₀) ∈ gph S`
[Clason–Valkonen, Cor. 27.12]. -/
theorem regBound_eq_posHomNorm_invMap_coderiv
    (hloc : ∃ ρ > 0, IsClosed (graph S ∩ closedBall (x₀, y₀) ρ)) (h₀ : y₀ ∈ S x₀) :
    regBound S x₀ y₀ = posHomNorm (invMap (coderiv S x₀ y₀)) := by
  rw [regBound_eq_inv_posHomLowerNorm hloc h₀,
    ← inv_posHomNorm_invMap (posHomogeneous_coderiv h₀).2, inv_inv]

/-- Thm. 3.3(ii) of [Mordukhovich 2018], exact bound (3.8):
`reg S (x₀, y₀) = ‖D*S⁻¹(y₀, x₀)‖` for `gph S` locally closed around `(x₀, y₀) ∈ gph S`. -/
theorem regBound_eq_posHomNorm_coderiv_invMap
    (hloc : ∃ ρ > 0, IsClosed (graph S ∩ closedBall (x₀, y₀) ρ)) (h₀ : y₀ ∈ S x₀) :
    regBound S x₀ y₀ = posHomNorm (coderiv (invMap S) y₀ x₀) := by
  rw [regBound_eq_posHomNorm_invMap_coderiv hloc h₀, posHomNorm_invMap_coderiv]

/-- Thm. 3.3(i) of [Mordukhovich 2018], exact bound (3.7):
`cov S (x₀, y₀) = inf {‖u‖ | u ∈ D*S(x₀, y₀)(v), ‖v‖ = 1}` for `gph S` locally closed around
`(x₀, y₀) ∈ gph S`, in `ℝ≥0∞` (both sides are `0` when `S` has no covering property). The
domain space must be nontrivial, as in Thm. 3.2 (`covBound_eq_inv_regBound`). -/
theorem covBound_eq_posHomLowerNorm [Nontrivial E]
    (hloc : ∃ ρ > 0, IsClosed (graph S ∩ closedBall (x₀, y₀) ρ)) (h₀ : y₀ ∈ S x₀) :
    covBound S x₀ y₀ = posHomLowerNorm (coderiv S x₀ y₀) := by
  rw [covBound_eq_inv_regBound h₀, regBound_eq_inv_posHomLowerNorm hloc h₀, inv_inv]

/-- Thm. 3.3(ii) of [Mordukhovich 2018] (coderivative criterion for metric regularity,
Mordukhovich criterion): if `gph S` is locally closed around `(x₀, y₀) ∈ gph S`, then `S` is
metrically regular around `(x₀, y₀)` iff `ker D*S(x₀, y₀) = {0}` (3.6)
[Clason–Valkonen, Cor. 27.12 for the necessity]. No nontriviality assumption is needed. -/
theorem metricallyRegularAt_iff_coderivKer_eq
    (hloc : ∃ ρ > 0, IsClosed (graph S ∩ closedBall (x₀, y₀) ρ)) (h₀ : y₀ ∈ S x₀) :
    MetricallyRegularAt S x₀ y₀ ↔ coderivKer S x₀ y₀ = {0} := by
  refine ⟨fun h ↦ h.coderivKer_eq h₀, fun h ↦ ?_⟩
  rw [metricallyRegularAt_iff_regBound_lt_top, regBound_eq_inv_posHomLowerNorm hloc h₀]
  exact ENNReal.inv_lt_top.2 (posHomLowerNorm_coderiv_pos h₀ h)

/-- Thm. 3.3(ii) of [Mordukhovich 2018] in the form used for bilevel programs: for `R` with graph
locally closed around `(x₀, z₀) ∈ gph R`, `R` is metrically regular around `(x₀, z₀)` iff
`0 ∈ D*R(x₀, z₀)(z*)` implies `z* = 0`. -/
theorem metricallyRegularAt_iff_forall_zero_mem_coderiv
    (hloc : ∃ ρ > 0, IsClosed (graph S ∩ closedBall (x₀, y₀) ρ)) (h₀ : y₀ ∈ S x₀) :
    MetricallyRegularAt S x₀ y₀ ↔
      ∀ v : StrongDual ℝ F, (0 : StrongDual ℝ E) ∈ coderiv S x₀ y₀ v → v = 0 := by
  rw [metricallyRegularAt_iff_coderivKer_eq hloc h₀]
  refine ⟨fun h v hv ↦ ?_, fun h ↦ ?_⟩
  · have : v ∈ coderivKer S x₀ y₀ := hv
    rwa [h, mem_singleton_iff] at this
  · exact subset_antisymm (fun v hv ↦ h v hv)
      (singleton_subset_iff.2 (zero_mem_coderivKer h₀))

/-- Thm. 3.3(i) of [Mordukhovich 2018] (coderivative criterion for covering): if `gph S` is
locally closed around `(x₀, y₀) ∈ gph S`, then `S` has the covering property around `(x₀, y₀)`
iff `ker D*S(x₀, y₀) = {0}` (3.6). The domain space must be nontrivial: for `E = {0}` and
`S 0 = ball 0 1 ⊆ ℝ`, the kernel is `{0}` at `(0, 0)` but `S` has no covering property. -/
theorem hasCoveringAt_iff_coderivKer_eq [Nontrivial E]
    (hloc : ∃ ρ > 0, IsClosed (graph S ∩ closedBall (x₀, y₀) ρ)) (h₀ : y₀ ∈ S x₀) :
    HasCoveringAt S x₀ y₀ ↔ coderivKer S x₀ y₀ = {0} := by
  rw [hasCoveringAt_iff_metricallyRegularAt h₀, metricallyRegularAt_iff_coderivKer_eq hloc h₀]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The graph of `S⁻¹` is locally closed around `(y₀, x₀)` iff that of `S` is locally closed
around `(x₀, y₀)` (the swap is an isometry of the maximum norm). -/
theorem locallyClosed_graph_invMap
    (hloc : ∃ ρ > 0, IsClosed (graph S ∩ closedBall (x₀, y₀) ρ)) :
    ∃ ρ > 0, IsClosed (graph (invMap S) ∩ closedBall (y₀, x₀) ρ) := by
  obtain ⟨ρ, hρ, hcl⟩ := hloc
  refine ⟨ρ, hρ, ?_⟩
  have : graph (invMap S) ∩ closedBall (y₀, x₀) ρ =
      Prod.swap ⁻¹' (graph S ∩ closedBall (x₀, y₀) ρ) := by
    ext ⟨a, b⟩
    simp only [mem_inter_iff, mem_preimage, Prod.swap_prod_mk, mem_closedBall, Prod.dist_eq]
    rw [max_comm]
    rfl
  rw [this]
  exact hcl.preimage continuous_swap

/-- Thm. 3.3(iii) of [Mordukhovich 2018] (coderivative criterion for the Lipschitz-like property,
Mordukhovich criterion): if `gph S` is locally closed around `(x₀, y₀) ∈ gph S`, then `S` is
Lipschitz-like around `(x₀, y₀)` iff `D*S(x₀, y₀)(0) = {0}` (3.9) [Clason–Valkonen, Cor. 27.16,
Lemma 27.11 for the necessity]. It follows from (ii) applied to `S⁻¹`; no nontriviality
assumption is needed. -/
theorem lipschitzLikeAt_iff_coderiv_zero_eq
    (hloc : ∃ ρ > 0, IsClosed (graph S ∩ closedBall (x₀, y₀) ρ)) (h₀ : y₀ ∈ S x₀) :
    LipschitzLikeAt S x₀ y₀ ↔ coderiv S x₀ y₀ 0 = {0} := by
  rw [lipschitzLikeAt_iff_metricallyRegularAt_invMap h₀,
    metricallyRegularAt_iff_coderivKer_eq (S := invMap S) (locallyClosed_graph_invMap hloc) h₀,
    ← coderiv_invMap_zero_eq_iff (S := invMap S)]
  rfl

/-- Thm. 3.3(iii) of [Mordukhovich 2018] in elementwise form: for `gph S` locally closed around
`(x₀, y₀) ∈ gph S`, `S` is Lipschitz-like around `(x₀, y₀)` iff `u ∈ D*S(x₀, y₀)(0)` implies
`u = 0`. -/
theorem lipschitzLikeAt_iff_forall_mem_coderiv_zero
    (hloc : ∃ ρ > 0, IsClosed (graph S ∩ closedBall (x₀, y₀) ρ)) (h₀ : y₀ ∈ S x₀) :
    LipschitzLikeAt S x₀ y₀ ↔ ∀ u ∈ coderiv S x₀ y₀ 0, u = 0 := by
  rw [lipschitzLikeAt_iff_coderiv_zero_eq hloc h₀]
  refine ⟨fun h u hu ↦ by rwa [h, mem_singleton_iff] at hu, fun h ↦ ?_⟩
  exact subset_antisymm (fun u hu ↦ h u hu) (singleton_subset_iff.2 (posHomogeneous_coderiv h₀).1)

/-- Thm. 3.3(iii) of [Mordukhovich 2018], exact bound (3.10):
`lip S (x₀, y₀) = ‖D*S(x₀, y₀)‖` for `gph S` locally closed around `(x₀, y₀) ∈ gph S`, in
`ℝ≥0∞` (both sides are `∞` when `S` is not Lipschitz-like) [Clason–Valkonen, Cor. 27.16]. -/
theorem lipBound_eq_posHomNorm_coderiv
    (hloc : ∃ ρ > 0, IsClosed (graph S ∩ closedBall (x₀, y₀) ρ)) (h₀ : y₀ ∈ S x₀) :
    lipBound S x₀ y₀ = posHomNorm (coderiv S x₀ y₀) := by
  rw [lipBound_eq_regBound_invMap h₀,
    regBound_eq_posHomNorm_coderiv_invMap (S := invMap S) (locallyClosed_graph_invMap hloc) h₀]
  rfl

/-- Thm. 3.3(iii) of [Mordukhovich 2018], moduli: every `ℓ > ‖D*S(x₀, y₀)‖` is a Lipschitz-like
modulus of `S` around `(x₀, y₀)`, for `gph S` locally closed around `(x₀, y₀) ∈ gph S`. -/
theorem lipschitzLikeWith_of_posHomNorm_lt
    (hloc : ∃ ρ > 0, IsClosed (graph S ∩ closedBall (x₀, y₀) ρ)) (h₀ : y₀ ∈ S x₀) {ℓ : ℝ≥0}
    (hℓ : posHomNorm (coderiv S x₀ y₀) < ℓ) : LipschitzLikeWith ℓ S x₀ y₀ := by
  rw [← lipBound_eq_posHomNorm_coderiv hloc h₀] at hℓ
  obtain ⟨ℓ', hℓ', hlt⟩ := exists_lipschitzLikeWith_of_lipBound_lt hℓ
  exact hℓ'.mono (by exact_mod_cast hlt.le)

end Criterion

end VariationalAnalysis
