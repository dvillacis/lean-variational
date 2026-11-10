/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Topology.MetricSpace.Sequences
import VariationalAnalysis.Normal.Projection
import VariationalAnalysis.Subdifferential.Limiting
import VariationalAnalysis.SetValued.Basic
import VariationalAnalysis.SCD.Derivable

/-!
# Set convergence, epi-convergence and proto-differentiability

This file follows [Mordukhovich 2024, Subsect. 1.4.2–1.4.3] (body numbering): Painlevé–Kuratowski
set convergence, epi-convergence and epi-differentiability, the approximation of basic normals by
proximal normals under set convergence, and proto-differentiability of set-valued mappings.

## Main declarations

* `IsSetLimit l Ω Ω₀`: `Ω₀` is the Painlevé–Kuratowski limit of `Ω` along `l`
  [Mordukhovich 2024, Def. 1.78, (1.102)–(1.104)].
* `EpiTendsto l φ φ₀`: epi-convergence [Mordukhovich 2024, Def. 1.79].
* `diffQuot φ x₀ t w`: the first-order difference quotient `(φ(x̄ + tw) - φ(x̄))/t`
  [Mordukhovich 2024, (1.56)]; `EpiDifferentiableAt φ x₀` [Mordukhovich 2024, Def. 1.80].
* `proxNormalCone Ω x₀`: the proximal normal cone [Mordukhovich 2024, (1.105)].
* `ProtoDifferentiableAt F x₀ y₀`: proto-differentiability [Mordukhovich 2024, Def. 1.85].

## Main results

* `mem_outerLimit_atTop_iff`, `mem_innerLimit_atTop_iff`, `mem_innerLimit_atTop_iff_dist`:
  the sequential descriptions (1.102), (1.103) of the outer and inner limits.
* `innerLimit_subset_outerLimit_atTop`, `isClosed_innerLimit_atTop`.
* `proxNormalCone_subset_regularNormalCone`, `toDual_smul_sub_mem_proxNormalCone`.
* `exists_tendsto_proxNormalCone`: [Mordukhovich 2024, Lemma 1.81].
* `ProtoDifferentiableAt.invMap`, `protoDifferentiableAt_invMap_iff`: proto-differentiability of
  `F` at `(x̄, ȳ)` is equivalent to that of `F⁻¹` at `(ȳ, x̄)` [Mordukhovich 2024, p. 65].

## Implementation notes

* Set limits are taken along an arbitrary filter, using `outerLimit` and `innerLimit` of
  `SetValued/OuterLimit`; Def. 1.78 is the case `l = atTop` on `ℕ`, and Def. 1.80 uses
  `l = 𝓝[>] 0`. Def. 1.78 asks the sets to be nonempty; we only assume this in Lemma 1.81.
* Normals are dual vectors, as everywhere in the library. Lemma 1.81 is stated in
  finite-dimensional real inner product spaces, where the proof by projections works.
* Def. 1.80 is stated for the quotient functions `w ↦ Δ_tφ(x̄)(w)`: `φ` is epi-differentiable at
  `x̄` if `φ(x̄)` is finite and the quotients epi-converge as `t ↓ 0`.
* Proto-differentiability is the geometric derivability of the graph
  (`GeometricallyDerivableAt`, the derivability of [Mordukhovich 2024, Def. 1.9]).
-/

open Filter Topology Set Metric InnerProductSpace
open scoped RealInnerProductSpace

namespace VariationalAnalysis

/-! ### Set convergence -/

section SetLimit

variable {ι X : Type*} [TopologicalSpace X]

/-- `Ω₀` is the (Painlevé–Kuratowski) limit of the family `Ω` along `l`: it is both the outer
and the inner limit [Mordukhovich 2024, Def. 1.78, (1.104)]. -/
def IsSetLimit (l : Filter ι) (Ω : ι → Set X) (Ω₀ : Set X) : Prop :=
  outerLimit l Ω = Ω₀ ∧ innerLimit l Ω = Ω₀

variable {S : ℕ → Set X} {y : X}

/-- The outer limit of a sequence of sets [Mordukhovich 2024, (1.102)]: the limits of
`x_k ∈ Ω_k` along a subsequence. -/
theorem mem_outerLimit_atTop_iff : y ∈ outerLimit atTop S ↔
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℕ → X, Tendsto v atTop (𝓝 y) ∧ ∀ k, v k ∈ S (φ k) := by
  constructor
  · rintro ⟨a, v, ha, hv, hS⟩
    obtain ⟨ψ, hψ, haψ⟩ := strictMono_subseq_of_tendsto_atTop ha
    exact ⟨a ∘ ψ, haψ, v ∘ ψ, hv.comp hψ.tendsto_atTop, fun k ↦ hS (ψ k)⟩
  · rintro ⟨φ, hφ, v, hv, hS⟩
    exact ⟨φ, v, hφ.tendsto_atTop, hv, hS⟩

/-- The inner limit of a sequence of sets [Mordukhovich 2024, (1.103)]: the limits of
`x_k ∈ Ω_k` defined for all but finitely many `k`. -/
theorem mem_innerLimit_atTop_iff : y ∈ innerLimit atTop S ↔
    ∃ v : ℕ → X, Tendsto v atTop (𝓝 y) ∧ ∀ᶠ k in atTop, v k ∈ S k := by
  constructor
  · intro h
    exact h id tendsto_id
  · rintro ⟨v, hv, hS⟩ a ha
    exact ⟨v ∘ a, hv.comp ha, ha.eventually hS⟩

theorem innerLimit_subset_outerLimit_atTop : innerLimit atTop S ⊆ outerLimit atTop S :=
  fun y hy ↦ by
    obtain ⟨v, hv, hS⟩ := mem_innerLimit_atTop_iff.1 hy
    exact mem_outerLimit_of_eventually id v tendsto_id hv hS

end SetLimit

section SetLimitMetric

variable {X : Type*} [PseudoMetricSpace X] {S : ℕ → Set X} {y : X}

/-- The inner limit of a sequence of sets in metric terms: `dist(y; Ω_k) → 0`. -/
theorem mem_innerLimit_atTop_iff_dist : y ∈ innerLimit atTop S ↔
    ∀ ε > 0, ∀ᶠ k in atTop, ∃ z ∈ S k, dist z y < ε := by
  rw [mem_innerLimit_atTop_iff]
  constructor
  · rintro ⟨v, hv, hS⟩ ε hε
    filter_upwards [hS, Metric.tendsto_nhds.1 hv ε hε] with k hk hk' using ⟨v k, hk, hk'⟩
  · intro h
    have hne : ∀ᶠ k in atTop, (S k).Nonempty :=
      (h 1 one_pos).mono fun k ⟨z, hz, _⟩ ↦ ⟨z, hz⟩
    have hc : ∀ k : ℕ, ∃ z, (S k).Nonempty →
        z ∈ S k ∧ dist z y < infDist y (S k) + 1 / ((k : ℝ) + 1) := by
      intro k
      by_cases hk : (S k).Nonempty
      · obtain ⟨z, hz, hd⟩ := (infDist_lt_iff hk).1
          (lt_add_of_pos_right (infDist y (S k)) (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1)))
        exact ⟨z, fun _ ↦ ⟨hz, by rwa [dist_comm]⟩⟩
      · exact ⟨y, fun h ↦ absurd h hk⟩
    choose c hc using hc
    refine ⟨c, Metric.tendsto_nhds.2 fun ε hε ↦ ?_, hne.mono fun k hk ↦ (hc k hk).1⟩
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (half_pos hε)
    filter_upwards [hne, h (ε / 2) (half_pos hε), eventually_ge_atTop N] with k hk hz hkN
    obtain ⟨z, hz, hzd⟩ := hz
    have h1 : infDist y (S k) ≤ dist y z := infDist_le_dist_of_mem hz
    have h2 : 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      have : (N : ℝ) ≤ k := by exact_mod_cast hkN
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    rw [dist_comm] at hzd
    linarith [(hc k hk).2]

theorem isClosed_innerLimit_atTop : IsClosed (innerLimit atTop S) := by
  refine isClosed_of_closure_subset fun y hy ↦ mem_innerLimit_atTop_iff_dist.2 fun ε hε ↦ ?_
  obtain ⟨y', hy', hd⟩ := Metric.mem_closure_iff.1 hy (ε / 2) (half_pos hε)
  filter_upwards [mem_innerLimit_atTop_iff_dist.1 hy' (ε / 2) (half_pos hε)] with k hk
  obtain ⟨z, hz, hzd⟩ := hk
  exact ⟨z, hz, by linarith [dist_triangle z y' y, dist_comm y y']⟩

end SetLimitMetric

/-! ### Epi-convergence and epi-differentiability -/

section Epi

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Epi-convergence `φ_i →ₑ φ₀` along `l`: the epigraphs converge in the sense of
Painlevé–Kuratowski [Mordukhovich 2024, Def. 1.79]. -/
def EpiTendsto (l : Filter ι) (φ : ι → E → EReal) (φ₀ : E → EReal) : Prop :=
  IsSetLimit l (fun i ↦ (φ i).Epi univ) (φ₀.Epi univ)

omit [NormedSpace ℝ E] in
/-- Epi-limits are unique (as epigraphs). -/
theorem EpiTendsto.epi_eq {l : Filter ι} {φ : ι → E → EReal} {ψ₁ ψ₂ : E → EReal}
    (h₁ : EpiTendsto l φ ψ₁) (h₂ : EpiTendsto l φ ψ₂) : ψ₁.Epi univ = ψ₂.Epi univ :=
  h₁.1.symm.trans h₂.1

/-- The first-order difference quotient `Δ_tφ(x̄)(w) = (φ(x̄ + tw) - φ(x̄))/t`
[Mordukhovich 2024, (1.56)]. -/
noncomputable def diffQuot (φ : E → EReal) (x₀ : E) (t : ℝ) (w : E) : EReal :=
  ((t⁻¹ : ℝ) : EReal) * (φ (x₀ + t • w) - φ x₀)

/-- `φ` is epi-differentiable at `x̄ ∈ dom φ` if the difference quotients `Δ_tφ(x̄)` epi-converge
as `t ↓ 0` [Mordukhovich 2024, Def. 1.80]. -/
def EpiDifferentiableAt (φ : E → EReal) (x₀ : E) : Prop :=
  (∃ r : ℝ, φ x₀ = r) ∧ ∃ ψ : E → EReal, EpiTendsto (𝓝[>] (0 : ℝ)) (diffQuot φ x₀) ψ

end Epi

/-! ### Proximal normals and Lemma 1.81 -/

section ProxNormal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Set E} {x₀ : E}

/-- The proximal normal cone [Mordukhovich 2024, (1.105)]: `v` with
`⟨v, x - x̄⟩ ≤ γ‖x - x̄‖²` for all `x ∈ Ω` and some `γ ≥ 0`. -/
def proxNormalCone (Ω : Set E) (x₀ : E) : Set (StrongDual ℝ E) :=
  {v | x₀ ∈ Ω ∧ ∃ γ ≥ (0 : ℝ), ∀ x ∈ Ω, v (x - x₀) ≤ γ * ‖x - x₀‖ ^ 2}

theorem zero_mem_proxNormalCone (hx : x₀ ∈ Ω) : (0 : StrongDual ℝ E) ∈ proxNormalCone Ω x₀ :=
  ⟨hx, 0, le_rfl, fun x _ ↦ by simp⟩

/-- Proximal normals are regular normals. -/
theorem proxNormalCone_subset_regularNormalCone :
    proxNormalCone Ω x₀ ⊆ regularNormalCone Ω x₀ := by
  rintro v ⟨hx, γ, hγ, H⟩
  refine ⟨hx, fun ε hε ↦ ?_⟩
  filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds x₀ (show 0 < ε / (γ + 1) by positivity)),
    self_mem_nhdsWithin] with x hxb hxΩ
  rw [mem_ball, dist_eq_norm, lt_div_iff₀ (by positivity)] at hxb
  have h1 : γ * ‖x - x₀‖ ≤ ε := by linarith [norm_nonneg (x - x₀)]
  calc v (x - x₀) ≤ γ * ‖x - x₀‖ ^ 2 := H x hxΩ
    _ = (γ * ‖x - x₀‖) * ‖x - x₀‖ := by ring
    _ ≤ ε * ‖x - x₀‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

end ProxNormal

section Lemma181

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Projection normals are proximal normals: if `w ∈ Π(y; Ω)` and `α ≥ 0`, then
`α(y - w) ∈ N_P(w; Ω)` [Mordukhovich 2024, (1.106)]. -/
theorem toDual_smul_sub_mem_proxNormalCone {Ω : Set H} {y w : H} (hw : w ∈ euclideanProj Ω y)
    {α : ℝ} (hα : 0 ≤ α) : toDual ℝ H (α • (y - w)) ∈ proxNormalCone Ω w := by
  refine ⟨hw.1, α / 2, by positivity, fun x hx ↦ ?_⟩
  rw [toDual_apply_apply, real_inner_smul_left]
  have := mul_le_mul_of_nonneg_left (inner_sub_proj_le hw hx) hα
  linarith

/-- The projection step (1.106)–(1.107) of [Mordukhovich 2024, Lemma 1.81]: if `Ω_k → Ω` and
`w ∈ Π(y; Ω)`, the projection normal `α(y - w)` at `w` is the limit of proximal normals to `Ω_k`
at points `x_k → w`. -/
theorem exists_tendsto_proj_of_isSetLimit [FiniteDimensional ℝ H] {Ω : Set H} {Ωs : ℕ → Set H}
    (hcl : ∀ k, IsClosed (Ωs k)) (hne : ∀ k, (Ωs k).Nonempty) (hin : Ω ⊆ innerLimit atTop Ωs)
    (hout : outerLimit atTop Ωs ⊆ Ω) {y w : H} (hw : w ∈ euclideanProj Ω y) {α : ℝ}
    (hα : 0 ≤ α) :
    ∃ x : ℕ → H, ∃ v : ℕ → StrongDual ℝ H, (∀ k, v k ∈ proxNormalCone (Ωs k) (x k)) ∧
      Tendsto x atTop (𝓝 w) ∧ Tendsto v atTop (𝓝 (toDual ℝ H (α • (y - w)))) := by
  set z := w + (1 / 2 : ℝ) • (y - w) with hz
  have e2 : z - w = (1 / 2 : ℝ) • (y - w) := by rw [hz]; abel
  -- the ball around `z` of radius `‖z - w‖` meets `Ω` only at `w`, quantitatively
  have hkey : ∀ x ∈ Ω, ‖z - w‖ ^ 2 + ‖x - w‖ ^ 2 / 2 ≤ ‖z - x‖ ^ 2 := by
    intro x hx
    have h := inner_sub_proj_le hw hx
    have e : z - x = (1 / 2 : ℝ) • (y - w) - (x - w) := by rw [hz]; abel
    rw [e, e2, norm_sub_sq_real ((1 / 2 : ℝ) • (y - w)) (x - w), real_inner_smul_left]
    linarith
  -- projections of `z` onto `Ω_k`
  have hproj : ∀ k, ∃ q, q ∈ euclideanProj (Ωs k) z := fun k ↦ by
    obtain ⟨q, hq, hd⟩ := (hcl k).exists_infDist_eq_dist (hne k) z
    exact ⟨q, hq, by rw [hd, dist_eq_norm]⟩
  choose q hq using hproj
  obtain ⟨xt, hxt, hxtS⟩ := mem_innerLimit_atTop_iff.1 (hin hw.1)
  have hle : ∀ᶠ k in atTop, ‖z - q k‖ ≤ ‖z - xt k‖ :=
    hxtS.mono fun k hk ↦ norm_sub_proj_le (hq k) hk
  have hqt : Tendsto q atTop (𝓝 w) := by
    refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
    have hlim : Tendsto (fun n ↦ ‖z - xt (ns n)‖) atTop (𝓝 ‖z - w‖) :=
      (tendsto_const_nhds.sub (hxt.comp hns)).norm
    have hb : ∃ᶠ n in atTop, q (ns n) ∈ closedBall z (‖z - w‖ + 1) := by
      refine Eventually.frequently ?_
      filter_upwards [hns.eventually hle,
        hlim.eventually (gt_mem_nhds (lt_add_one ‖z - w‖))] with n h1 h2
      rw [mem_closedBall, dist_comm, dist_eq_norm]
      linarith
    obtain ⟨a, -, φ, hφ, ha⟩ := tendsto_subseq_of_frequently_bounded isBounded_closedBall hb
    refine ⟨φ, ?_⟩
    have haΩ : a ∈ Ω :=
      hout ⟨ns ∘ φ, fun n ↦ q (ns (φ n)), hns.comp hφ.tendsto_atTop, ha, fun k ↦ (hq _).1⟩
    have hza : ‖z - a‖ ≤ ‖z - w‖ :=
      le_of_tendsto_of_tendsto (tendsto_const_nhds.sub ha).norm (hlim.comp hφ.tendsto_atTop)
        (hφ.tendsto_atTop.eventually (hns.eventually hle))
    have h := hkey a haΩ
    have h2 := pow_le_pow_left₀ (norm_nonneg _) hza 2
    have h0 : ‖a - w‖ ^ 2 ≤ 0 := by linarith
    have haw : a = w := by
      have := (pow_eq_zero_iff (n := 2) two_ne_zero).1 (le_antisymm h0 (sq_nonneg _))
      rwa [norm_eq_zero, sub_eq_zero] at this
    rw [← haw]
    exact ha
  refine ⟨q, fun k ↦ toDual ℝ H ((2 * α) • (z - q k)),
    fun k ↦ toDual_smul_sub_mem_proxNormalCone (hq k) (by positivity), hqt, ?_⟩
  have : α • (y - w) = (2 * α) • (z - w) := by
    rw [e2, smul_smul]
    congr 1
    ring
  rw [this]
  exact ((toDual ℝ H).continuous.tendsto _).comp
    ((tendsto_const_nhds.sub hqt).const_smul (2 * α))

/-- [Mordukhovich 2024, Lemma 1.81] (approximation of basic normals by proximal normals under
set convergence): if `Ω, Ω_k` are nonempty closed sets with `Ω_k → Ω` and `v̄ ∈ N(x̄; Ω)`, then
there are `x_k ∈ Ω_k` and `v_k ∈ N_P(x_k; Ω_k)` with `(x_k, v_k) → (x̄, v̄)`. -/
theorem exists_tendsto_proxNormalCone [FiniteDimensional ℝ H] {Ω : Set H} {Ωs : ℕ → Set H}
    (hΩ : IsClosed Ω) (hcl : ∀ k, IsClosed (Ωs k)) (hne : ∀ k, (Ωs k).Nonempty)
    (hlim : IsSetLimit atTop Ωs Ω) {x₀ : H} {v₀ : StrongDual ℝ H} (hv : v₀ ∈ normalCone Ω x₀) :
    ∃ x : ℕ → H, ∃ v : ℕ → StrongDual ℝ H, (∀ k, v k ∈ proxNormalCone (Ωs k) (x k)) ∧
      Tendsto x atTop (𝓝 x₀) ∧ Tendsto v atTop (𝓝 v₀) := by
  have hin : Ω ⊆ innerLimit atTop Ωs := hlim.2.symm.subset
  have hout : outerLimit atTop Ωs ⊆ Ω := hlim.1.subset
  set S : ℕ → Set (H × StrongDual ℝ H) := fun k ↦ {p | p.2 ∈ proxNormalCone (Ωs k) p.1}
    with hS
  have hmem : (x₀, v₀) ∈ innerLimit atTop S := by
    have hx₀ : x₀ ∈ Ω := hv.1
    rw [← toDual_projNormalCone hx₀ ⟨1, one_pos, hΩ.inter isClosed_closedBall⟩] at hv
    obtain ⟨p₀, ⟨-, a, u, ha, hu, hau⟩, rfl⟩ := hv
    have hau' : ∀ k, ∃ α : ℝ, 0 ≤ α ∧ ∃ w ∈ euclideanProj Ω (a k), u k = α • (a k - w) := hau
    choose α hα w hw hu_eq using hau'
    have hw' : Tendsto w atTop (𝓝 x₀) := by
      refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ ↦ norm_nonneg _)
        (fun j ↦ norm_proj_sub_le (hw j) hx₀) ?_)
      simpa using (tendsto_iff_norm_sub_tendsto_zero.1 ha).const_mul 2
    have hj : ∀ j, (w j, toDual ℝ H (u j)) ∈ innerLimit atTop S := by
      intro j
      obtain ⟨x, v, hxv, hx, hvt⟩ :=
        exists_tendsto_proj_of_isSetLimit hcl hne hin hout (hw j) (hα j)
      rw [hu_eq j]
      exact mem_innerLimit_atTop_iff.2
        ⟨fun k ↦ (x k, v k), hx.prodMk_nhds hvt, Eventually.of_forall hxv⟩
    exact isClosed_innerLimit_atTop.mem_of_tendsto
      (hw'.prodMk_nhds (((toDual ℝ H).continuous.tendsto _).comp hu)) (Eventually.of_forall hj)
  obtain ⟨p, hp, hpS⟩ := mem_innerLimit_atTop_iff.1 hmem
  obtain ⟨N, hN⟩ := eventually_atTop.1 hpS
  choose c hc using hne
  refine ⟨fun k ↦ if N ≤ k then (p k).1 else c k, fun k ↦ if N ≤ k then (p k).2 else 0,
    fun k ↦ ?_, ?_, ?_⟩
  · by_cases hk : N ≤ k
    · simp only [if_pos hk]
      exact hN k hk
    · simp only [if_neg hk]
      exact zero_mem_proxNormalCone (hc k)
  · refine ((continuous_fst.tendsto _).comp hp).congr' ?_
    filter_upwards [eventually_ge_atTop N] with k hk
    simp [if_pos hk]
  · refine ((continuous_snd.tendsto _).comp hp).congr' ?_
    filter_upwards [eventually_ge_atTop N] with k hk
    simp [if_pos hk]

end Lemma181

/-! ### Proto-differentiability -/

section Proto

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

/-- `F` is proto-differentiable at `x̄` for `ȳ ∈ F(x̄)` if its graph is geometrically derivable at
`(x̄, ȳ)` [Mordukhovich 2024, Def. 1.85]. -/
def ProtoDifferentiableAt (F : X → Set Y) (x₀ : X) (y₀ : Y) : Prop :=
  GeometricallyDerivableAt (graph F) (x₀, y₀)

/-- If `F` is proto-differentiable at `(x̄, ȳ)`, then `F⁻¹` is proto-differentiable at `(ȳ, x̄)`
[Mordukhovich 2024, p. 65]. -/
theorem ProtoDifferentiableAt.invMap [CompleteSpace X] [CompleteSpace Y] {F : X → Set Y}
    {x₀ : X} {y₀ : Y}
    (h : ProtoDifferentiableAt F x₀ y₀) (hy : y₀ ∈ F x₀) :
    ProtoDifferentiableAt (invMap F) y₀ x₀ :=
  GeometricallyDerivableAt.of_inter_eq_preimage (Φ := Prod.swap)
    (e := ContinuousLinearEquiv.prodComm ℝ Y X) (W := univ) h univ_mem (by rw [graph_invMap])
    (ContinuousLinearEquiv.prodComm ℝ Y X).hasStrictFDerivAt hy

theorem protoDifferentiableAt_invMap_iff [CompleteSpace X] [CompleteSpace Y] {F : X → Set Y}
    {x₀ : X} {y₀ : Y} (hy : y₀ ∈ F x₀) :
    ProtoDifferentiableAt (invMap F) y₀ x₀ ↔ ProtoDifferentiableAt F x₀ y₀ :=
  ⟨fun h ↦ h.invMap hy, fun h ↦ h.invMap hy⟩

end Proto

end VariationalAnalysis
