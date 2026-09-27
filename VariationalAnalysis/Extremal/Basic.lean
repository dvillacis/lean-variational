/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.MetricSpace.Sequences
import VariationalAnalysis.Normal.Product
import VariationalAnalysis.Normal.Transport

/-!
# The extremal principle for finite systems of sets

A common point `x₀` of finitely many sets `Ω i` is *locally extremal* if the sets can be locally
pushed apart by arbitrarily small translations [Mordukhovich 2018, Def. 2.1]. The basic extremal
principle [Mordukhovich 2018, Thm. 2.3] says that, for sets locally closed around `x₀` in finite
dimensions, local extremality produces basic normals `vᵢ ∈ N(x₀; Ωᵢ)`, not all zero, with
`v₁ + ⋯ + vₛ = 0`: the nonconvex counterpart of the separation theorem.

The proof is the method of metric approximations of [Mordukhovich 2018, p. 70]: minimize
`[∑ᵢ dist²(x + aᵢₖ; Ωᵢ)]^{1/2} + ‖x - x₀‖²`, replace the distances by distances to Euclidean
projections to get a smooth problem, and apply the Fermat rule. It uses the Euclidean structure,
so it is carried out in a finite-dimensional inner product space and then transported to every
finite-dimensional normed space through `toEuclidean`.

## Main declarations

* `IsLocallyExtremal Ω x₀`: [Mordukhovich 2018, Def. 2.1]; `isLocallyExtremal_pair_iff` is the
  two-set description of [Mordukhovich 2018, p. 68].
* `AreSeparated Ω`: separation of finitely many sets, (2.2)–(2.3) of [Mordukhovich 2018].

## Main results

* `AreSeparated.exists_forall_notMem`, `AreSeparated.isLocallyExtremal`,
  `AreSeparated.of_isLocallyExtremal`, `areSeparated_iff_forall_isLocallyExtremal`: Prop. 2.2 of
  [Mordukhovich 2018] (extremality and separation).
* `IsLocallyExtremal.exists_global`: the neighborhood `U` of Def. 2.1 can be taken to be the whole
  space after localizing the sets.
* `exists_metric_approx`: one step of the method of metric approximations (Euclidean spaces).
* `IsLocallyExtremal.exists_mem_normalCone_inner`: Thm. 2.3 of [Mordukhovich 2018] (basic
  extremal principle) in a finite-dimensional inner product space.
* `IsLocallyExtremal.exists_mem_normalCone`, `IsLocallyExtremal.exists_mem_normalCone_ne_zero`:
  Thm. 2.3 in a finite-dimensional normed space.
* `IsLocallyExtremal.exists_mem_normalCone_pair`: the two-set form (2.9).
* `exists_mem_normalCone_norm_eq_one_of_mem_frontier`: Prop. 1.2 recovered from Thm. 2.3.
* `IsLocallyExtremal.exists_approx`: Cor. 2.5 of [Mordukhovich 2018] (approximate extremal
  principle).

Cor. 2.4 of [Mordukhovich 2018] (relative interiors) is not formalized: it rests on proper
separation of convex sets with disjoint relative interiors [Rockafellar 1970, Thm. 11.3], which
is not in Mathlib.
-/

open Filter Topology Set Metric InnerProductSpace

namespace VariationalAnalysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type*}

section LocallyClosed

/-! ### Local closedness -/

variable {Ω Ω₁ Ω₂ : Set E} {x₀ : E}

omit [NormedSpace ℝ E] in
/-- Local closedness can be tested on smaller balls. -/
theorem isClosed_inter_closedBall_of_le {r R : ℝ} (h : IsClosed (Ω ∩ closedBall x₀ r))
    (hR : R ≤ r) : IsClosed (Ω ∩ closedBall x₀ R) := by
  have : Ω ∩ closedBall x₀ R = (Ω ∩ closedBall x₀ r) ∩ closedBall x₀ R := by
    rw [inter_assoc, inter_eq_right.2 (closedBall_subset_closedBall hR)]
  rw [this]; exact h.inter isClosed_closedBall

omit [NormedSpace ℝ E] in
/-- A set locally closed around `x₀` is locally closed around every point close to `x₀`. -/
theorem locallyClosed_of_dist_lt {r : ℝ} (h : IsClosed (Ω ∩ closedBall x₀ r)) {x : E}
    (hx : dist x x₀ < r) : ∃ ρ > 0, IsClosed (Ω ∩ closedBall x ρ) := by
  refine ⟨r - dist x x₀, by linarith, ?_⟩
  have hsub : closedBall x (r - dist x x₀) ⊆ closedBall x₀ r :=
    closedBall_subset_closedBall' (by linarith)
  have : Ω ∩ closedBall x (r - dist x x₀) = (Ω ∩ closedBall x₀ r) ∩ closedBall x (r - dist x x₀) :=
    by rw [inter_assoc, inter_eq_right.2 hsub]
  rw [this]; exact h.inter isClosed_closedBall

omit [NormedSpace ℝ E] in
/-- A set locally closed around `x₀` is locally closed around all points near `x₀`. -/
theorem eventually_locallyClosed (h : ∃ r > 0, IsClosed (Ω ∩ closedBall x₀ r)) :
    ∀ᶠ x in 𝓝 x₀, ∃ ρ > 0, IsClosed (Ω ∩ closedBall x ρ) := by
  obtain ⟨r, hr, hcl⟩ := h
  filter_upwards [ball_mem_nhds x₀ hr] with x hx using locallyClosed_of_dist_lt hcl hx

omit [NormedSpace ℝ E] in
/-- The intersection of two sets locally closed around `x₀` is locally closed around `x₀`. -/
theorem locallyClosed_inter (h₁ : ∃ r > 0, IsClosed (Ω₁ ∩ closedBall x₀ r))
    (h₂ : ∃ r > 0, IsClosed (Ω₂ ∩ closedBall x₀ r)) :
    ∃ r > 0, IsClosed (Ω₁ ∩ Ω₂ ∩ closedBall x₀ r) := by
  obtain ⟨r₁, hr₁, hc₁⟩ := h₁
  obtain ⟨r₂, hr₂, hc₂⟩ := h₂
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, ?_⟩
  have : Ω₁ ∩ Ω₂ ∩ closedBall x₀ (min r₁ r₂) =
      (Ω₁ ∩ closedBall x₀ (min r₁ r₂)) ∩ (Ω₂ ∩ closedBall x₀ (min r₁ r₂)) := by
    ext; simp only [mem_inter_iff]; tauto
  rw [this]
  exact (isClosed_inter_closedBall_of_le hc₁ (min_le_left _ _)).inter
    (isClosed_inter_closedBall_of_le hc₂ (min_le_right _ _))

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- The product of two locally closed sets is locally closed. -/
theorem locallyClosed_prod {Θ : Set F} {y₀ : F} (h₁ : ∃ r > 0, IsClosed (Ω ∩ closedBall x₀ r))
    (h₂ : ∃ r > 0, IsClosed (Θ ∩ closedBall y₀ r)) :
    ∃ r > 0, IsClosed (Ω ×ˢ Θ ∩ closedBall (x₀, y₀) r) := by
  obtain ⟨r₁, hr₁, hc₁⟩ := h₁
  obtain ⟨r₂, hr₂, hc₂⟩ := h₂
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, ?_⟩
  rw [← closedBall_prod_same, prod_inter_prod]
  exact (isClosed_inter_closedBall_of_le hc₁ (min_le_left _ _)).prod
    (isClosed_inter_closedBall_of_le hc₂ (min_le_right _ _))

/-- A positive lower bound for finitely many positive radii. -/
theorem exists_pos_forall_le [Finite ι] (r : ι → ℝ) (hr : ∀ i, 0 < r i) :
    ∃ R > 0, ∀ i, R ≤ r i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i ↦ isEmptyElim i⟩
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min r
    exact ⟨r i₀, hr i₀, hi₀⟩

end LocallyClosed

section Definition

/-! ### Local extremality and separation -/

/-- Def. 2.1 of [Mordukhovich 2018] (local extremality of finitely many sets): `x₀` is a locally
extremal point of the system `{Ω i}` if `x₀ ∈ Ω i` for all `i` and there are translations
`aᵢₖ → 0` (`k → ∞`) and a neighborhood `U` of `x₀` with `⋂ᵢ (Ωᵢ - aᵢₖ) ∩ U = ∅` for all large
`k`. Here `Ωᵢ - aᵢₖ = {x | x + aᵢₖ ∈ Ωᵢ}`. The book asks for `s ≥ 2` sets; with a single set (or
none) the system is never extremal. -/
def IsLocallyExtremal (Ω : ι → Set E) (x₀ : E) : Prop :=
  (∀ i, x₀ ∈ Ω i) ∧ ∃ a : ι → ℕ → E, (∀ i, Tendsto (a i) atTop (𝓝 0)) ∧
    ∃ U ∈ 𝓝 x₀, ∀ᶠ k in atTop, (⋂ i, (fun x ↦ x + a i k) ⁻¹' Ω i) ∩ U = ∅

variable {Ω : ι → Set E} {x₀ : E}

omit [NormedSpace ℝ E] in
theorem isLocallyExtremal_iff : IsLocallyExtremal Ω x₀ ↔
    (∀ i, x₀ ∈ Ω i) ∧ ∃ a : ι → ℕ → E, (∀ i, Tendsto (a i) atTop (𝓝 0)) ∧
      ∃ U ∈ 𝓝 x₀, ∀ᶠ k in atTop, ∀ x ∈ U, ∃ i, x + a i k ∉ Ω i := by
  unfold IsLocallyExtremal
  refine and_congr_right fun _ ↦ exists_congr fun a ↦ and_congr_right fun _ ↦
    exists_congr fun U ↦ and_congr_right fun _ ↦ eventually_congr (Eventually.of_forall
      fun k ↦ ?_)
  simp only [eq_empty_iff_forall_notMem, mem_inter_iff, mem_iInter, mem_preimage, not_and]
  exact ⟨fun h x hx ↦ by_contra fun h' ↦ h x (by simpa using h') hx,
    fun h x hx hU ↦ by obtain ⟨i, hi⟩ := h x hU; exact hi (hx i)⟩

omit [NormedSpace ℝ E] in
/-- [Mordukhovich 2018, p. 68]: in Def. 2.1 the neighborhood `U` can be removed after
localizing the sets. If `x₀` is locally extremal, there are translations `aᵢₖ → 0` and `R₀ > 0`
such that for every `R ∈ (0, R₀]` the sets `Ωᵢ ∩ B(x₀, R)` satisfy
`⋂ᵢ (Ωᵢ ∩ B(x₀, R) - aᵢₖ) = ∅` for all large `k` (extremality with `U = E`). -/
theorem IsLocallyExtremal.exists_global [Finite ι] (h : IsLocallyExtremal Ω x₀) :
    ∃ a : ι → ℕ → E, (∀ i, Tendsto (a i) atTop (𝓝 0)) ∧ ∃ R₀ > 0, ∀ R, 0 < R → R ≤ R₀ →
      ∀ᶠ k in atTop, ∀ x, ∃ i, x + a i k ∉ Ω i ∩ closedBall x₀ R := by
  obtain ⟨-, a, ha, U, hU, hk⟩ := isLocallyExtremal_iff.1 h
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  refine ⟨a, ha, ε / 3, by positivity, fun R hR hRR ↦ ?_⟩
  have hsmall : ∀ᶠ k in atTop, ∀ i, ‖a i k‖ < R := eventually_all.2 fun i ↦
    ((ha i).eventually (ball_mem_nhds 0 hR)).mono fun k hk ↦ mem_ball_zero_iff.1 hk
  filter_upwards [hk, hsmall] with k hk hs x
  by_contra hx
  push Not at hx
  obtain ⟨i₀, -⟩ := hk x₀ (mem_of_mem_nhds hU)
  have hxU : x ∈ U := hball (by
    have h1 := (hx i₀).2
    rw [mem_ball, dist_eq_norm]
    rw [mem_closedBall, dist_eq_norm] at h1
    calc ‖x - x₀‖ = ‖(x + a i₀ k - x₀) - a i₀ k‖ := by congr 1; abel
      _ ≤ ‖x + a i₀ k - x₀‖ + ‖a i₀ k‖ := norm_sub_le _ _
      _ < ε := by linarith [hs i₀])
  obtain ⟨i, hi⟩ := hk x hxU
  exact hi (hx i).1


omit [NormedSpace ℝ E] in
/-- [Mordukhovich 2018, p. 68]: the two-set description of local extremality. `x₀` is a locally
extremal point of `{Ω₁, Ω₂}` iff there are `aₖ → 0` and a neighborhood `U` of `x₀` with
`Ω₁ ∩ (Ω₂ - aₖ) ∩ U = ∅` for all large `k`. -/
theorem isLocallyExtremal_pair_iff {Ω₁ Ω₂ : Set E} :
    IsLocallyExtremal ![Ω₁, Ω₂] x₀ ↔ x₀ ∈ Ω₁ ∧ x₀ ∈ Ω₂ ∧ ∃ a : ℕ → E,
      Tendsto a atTop (𝓝 0) ∧ ∃ U ∈ 𝓝 x₀, ∀ᶠ k in atTop, ∀ x ∈ U, x ∈ Ω₁ → x + a k ∉ Ω₂ := by
  rw [isLocallyExtremal_iff]
  constructor
  · rintro ⟨hx, a, ha, U, hU, hk⟩
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
    refine ⟨by simpa using hx 0, by simpa using hx 1, fun k ↦ a 1 k - a 0 k,
      by simpa using (ha 1).sub (ha 0), ball x₀ (ε / 2), ball_mem_nhds _ (by positivity), ?_⟩
    have hsmall : ∀ᶠ k in atTop, ‖a 0 k‖ < ε / 2 :=
      ((ha 0).eventually (ball_mem_nhds 0 (by positivity))).mono fun k hk ↦
        mem_ball_zero_iff.1 hk
    filter_upwards [hk, hsmall] with k hk hs x hxU hx₁ hx₂
    have hyU : x - a 0 k ∈ U := hball (by
      rw [mem_ball, dist_eq_norm] at hxU ⊢
      calc ‖x - a 0 k - x₀‖ = ‖(x - x₀) - a 0 k‖ := by congr 1; abel
        _ ≤ ‖x - x₀‖ + ‖a 0 k‖ := norm_sub_le _ _
        _ < ε := by linarith)
    obtain ⟨i, hi⟩ := hk _ hyU
    fin_cases i
    · exact hi (by simpa using hx₁)
    · exact hi (by simpa [sub_add_eq_add_sub, add_sub_assoc] using hx₂)
  · rintro ⟨hx₁, hx₂, a, ha, U, hU, hk⟩
    refine ⟨fun i ↦ by fin_cases i <;> simpa, ![fun _ ↦ 0, a], fun i ↦ ?_, U, hU, ?_⟩
    · fin_cases i
      · exact tendsto_const_nhds
      · exact ha
    · filter_upwards [hk] with k hk x hxU
      by_contra h
      push Not at h
      exact hk x hxU (by simpa using h 0) (by simpa using h 1)

/-- The sets `Ω i` are *separated* [Mordukhovich 2018, (2.2)–(2.3)] if there are dual elements
`vᵢ`, not all zero, and numbers `αᵢ` with `vᵢ x ≤ αᵢ` on `Ωᵢ`, `∑ vᵢ = 0` and `∑ αᵢ = 0`. -/
def AreSeparated [Fintype ι] (Ω : ι → Set E) : Prop :=
  ∃ v : ι → StrongDual ℝ E, ∃ α : ι → ℝ, (∃ i, v i ≠ 0) ∧ (∀ i, ∀ x ∈ Ω i, v i x ≤ α i) ∧
    ∑ i, v i = 0 ∧ ∑ i, α i = 0

/-- Prop. 2.2(i) of [Mordukhovich 2018], global form: separated sets can be pushed apart by
arbitrarily small translations, with `U` in Def. 2.1 the whole space. -/
theorem AreSeparated.exists_forall_notMem [Fintype ι] [DecidableEq ι] (h : AreSeparated Ω) :
    ∃ a : ι → ℕ → E, (∀ i, Tendsto (a i) atTop (𝓝 0)) ∧
      ∀ k, ∀ x, ∃ i, x + a i k ∉ Ω i := by
  obtain ⟨v, α, ⟨j, hj⟩, hsep, hv, hα⟩ := h
  obtain ⟨e, he⟩ : ∃ e, v j e ≠ 0 := by
    by_contra h
    push Not at h
    exact hj (ContinuousLinearMap.ext h)
  set e' := (v j e)⁻¹ • e
  have he' : v j e' = 1 := by simp [e', he]
  set a : ι → ℕ → E := fun i k ↦ if i = j then (1 / ((k : ℝ) + 1)) • e' else 0
  refine ⟨a, fun i ↦ ?_, fun k x ↦ ?_⟩
  · by_cases hi : i = j
    · have : Tendsto (fun k : ℕ ↦ (1 / ((k : ℝ) + 1)) • e') atTop (𝓝 ((0 : ℝ) • e')) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.smul_const e'
      simpa [a, hi] using this
    · simp [a, hi]
  · by_contra hcon
    push Not at hcon
    have hle : ∑ i, v i (x + a i k) ≤ ∑ i, α i :=
      Finset.sum_le_sum fun i _ ↦ hsep i _ (hcon i)
    have ha : ∀ i, v i (a i k) = if i = j then 1 / ((k : ℝ) + 1) else 0 := fun i ↦ by
      by_cases hi : i = j
      · subst hi; simp [a, he']
      · simp [a, hi]
    have hsum : ∑ i, v i (x + a i k) = 1 / ((k : ℝ) + 1) := by
      simp only [map_add, Finset.sum_add_distrib, ha, Finset.sum_ite_eq', Finset.mem_univ,
        if_true]
      rw [← sum_apply, hv]
      simp
    rw [hsum, hα] at hle
    have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := Nat.one_div_pos_of_nat
    linarith

/-- Prop. 2.2(i) of [Mordukhovich 2018]: if the sets are separated, every common point is
locally extremal. -/
theorem AreSeparated.isLocallyExtremal [Fintype ι] (h : AreSeparated Ω)
    (hx : ∀ i, x₀ ∈ Ω i) : IsLocallyExtremal Ω x₀ := by
  classical
  obtain ⟨a, ha, hk⟩ := h.exists_forall_notMem
  exact isLocallyExtremal_iff.2 ⟨hx, a, ha, univ, univ_mem,
    Eventually.of_forall fun k x _ ↦ hk k x⟩

end Definition


section Inner

/-! ### The extremal principle in Euclidean spaces -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
variable [Fintype ι]

local notation "⟪" a ", " b "⟫" => @inner ℝ _ _ a b

/-- One step of the method of metric approximations [Mordukhovich 2018, proof of Thm. 2.3].
Let `K i` be compact sets containing `x₀` and let `bᵢ` be translations with
`⋂ᵢ (Kᵢ - bᵢ) = ∅`. Minimizing `[∑ᵢ dist²(x + bᵢ; Kᵢ)]^{1/2} + ‖x - x₀‖²` (2.6) and applying the
Fermat rule to the smooth problem (2.7) gives a point `x`, projections `wᵢ ∈ Kᵢ` of `x + bᵢ` and
proximal normals `vᵢ` at `wᵢ` with `∑ ‖vᵢ‖² = 1` and `∑ vᵢ = -2 (x - x₀)` (2.8), together with the
estimates `‖x - x₀‖² ≤ β` and `‖x + bᵢ - wᵢ‖ ≤ β` for `β = (∑ ‖bᵢ‖²)^{1/2}`. -/
theorem exists_metric_approx {K : ι → Set H} (hK : ∀ i, IsCompact (K i)) {x₀ : H}
    (hx₀ : ∀ i, x₀ ∈ K i) {b : ι → H} (hb : ∀ x, ∃ i, x + b i ∉ K i) :
    ∃ x : H, ∃ w v : ι → H,
      (∀ i, w i ∈ K i ∧ toDual ℝ H (v i) ∈ regularNormalCone (K i) (w i)) ∧
      ∑ i, ‖v i‖ ^ 2 = 1 ∧ ∑ i, v i = (-2 : ℝ) • (x - x₀) ∧
      ‖x - x₀‖ ^ 2 ≤ √(∑ i, ‖b i‖ ^ 2) ∧ ∀ i, ‖x + b i - w i‖ ≤ √(∑ i, ‖b i‖ ^ 2) := by
  set β := √(∑ i, ‖b i‖ ^ 2)
  -- the cost function (2.6)
  set f : H → ℝ := fun x ↦ √(∑ i, infDist (x + b i) (K i) ^ 2) + ‖x - x₀‖ ^ 2 with hf_def
  have hf : Continuous f := by
    refine (Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ ↦
      ((continuous_infDist_pt (K i)).comp (continuous_id.add continuous_const)).pow 2)).add
      ((continuous_id.sub continuous_const).norm.pow 2)
  have hfx₀ : f x₀ ≤ β := by
    simp only [hf_def, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, add_zero, β]
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ ↦ ?_)
    have h1 : infDist (x₀ + b i) (K i) ≤ ‖b i‖ := by
      simpa [dist_eq_norm] using infDist_le_dist_of_mem (x := x₀ + b i) (hx₀ i)
    gcongr
    exact infDist_nonneg
  have hf_ge : ∀ x, ‖x - x₀‖ ^ 2 ≤ f x := fun x ↦ le_add_of_nonneg_left (Real.sqrt_nonneg _)
  -- a global minimizer of (2.6)
  obtain ⟨x, hx⟩ := hf.exists_forall_le' x₀ (by
    refine Filter.mem_of_superset
      (isCompact_closedBall x₀ (√(f x₀) + 1)).compl_mem_cocompact fun y hy ↦ ?_
    rw [mem_compl_iff, mem_closedBall, not_le, dist_eq_norm] at hy
    have h0 : 0 ≤ f x₀ := le_trans (by positivity) (hf_ge x₀)
    have h1 : f x₀ ≤ ‖y - x₀‖ ^ 2 := by
      have := Real.sq_sqrt h0
      nlinarith [Real.sqrt_nonneg (f x₀)]
    exact h1.trans (hf_ge y))
  -- Euclidean projections
  have hproj : ∀ i, ∃ w ∈ K i, infDist (x + b i) (K i) = dist (x + b i) w := fun i ↦
    (hK i).exists_infDist_eq_dist ⟨x₀, hx₀ i⟩ _
  choose w hwK hw using hproj
  set y : ι → H := fun i ↦ x + b i - w i
  have hy : ∀ i, ‖y i‖ = infDist (x + b i) (K i) := fun i ↦ by rw [hw i, dist_eq_norm]
  set S := ∑ i, ‖y i‖ ^ 2
  set ρ := √S
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ ↦ by positivity
  have hSpos : 0 < S := by
    obtain ⟨i, hi⟩ := hb x
    have hyi : y i ≠ 0 := fun h ↦ hi (by rw [sub_eq_zero] at h; rw [h]; exact hwK i)
    exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun i ↦ ‖y i‖ ^ 2)
      (fun i _ ↦ by positivity) (Finset.mem_univ i))
  have hρ : 0 < ρ := Real.sqrt_pos.2 hSpos
  have hρS : ρ ^ 2 = S := Real.sq_sqrt hS0
  have hfx : f x = ρ + ‖x - x₀‖ ^ 2 := by simp only [hf_def, ← hy, ρ, S]
  -- the smooth problem (2.7)
  set ψ : H → ℝ := fun z ↦ √(∑ i, ‖z + b i - w i‖ ^ 2) + ‖z - x₀‖ ^ 2 with hψ_def
  have hψ_ge : ∀ z, f z ≤ ψ z := fun z ↦ by
    simp only [hf_def, hψ_def]
    gcongr with i
    · exact infDist_nonneg
    · simpa [dist_eq_norm] using infDist_le_dist_of_mem (x := z + b i) (hwK i)
  have hψx : ψ x = f x := by rw [hfx]
  have hmin : IsLocalMin ψ x := Eventually.of_forall fun z ↦ by
    rw [hψx]; exact (hx z).trans (hψ_ge z)
  -- the Fermat rule (2.8)
  set v : ι → H := fun i ↦ ρ⁻¹ • y i
  set D : StrongDual ℝ H := (1 / (2 * ρ)) • ∑ i, (2 • (innerSL ℝ (y i)).comp
      (ContinuousLinearMap.id ℝ H)) + 2 • (innerSL ℝ (x - x₀)).comp (ContinuousLinearMap.id ℝ H)
  have hD : HasFDerivAt ψ D x := by
    have h1 : HasFDerivAt (fun z ↦ ∑ i, ‖z + b i - w i‖ ^ 2)
        (∑ i, 2 • (innerSL ℝ (y i)).comp (ContinuousLinearMap.id ℝ H)) x :=
      HasFDerivAt.fun_sum fun i _ ↦ (((hasFDerivAt_id x).add_const (b i)).sub_const
        (w i)).norm_sq
    have h2 := h1.sqrt (by simpa using hSpos.ne')
    exact h2.add ((hasFDerivAt_id x).sub_const x₀).norm_sq
  have hD0 : D = 0 := IsLocalMin.hasFDerivAt_eq_zero hmin hD
  set z := ∑ i, v i + (2 : ℝ) • (x - x₀)
  have hz : z = 0 := by
    have key : ∀ u, D u = ⟪z, u⟫ := fun u ↦ by
      simp only [D, z, v, add_apply, smul_apply, sum_apply, ContinuousLinearMap.coe_comp,
        ContinuousLinearMap.id_apply, Function.comp_apply, innerSL_apply_apply,
        smul_eq_mul, nsmul_eq_mul, inner_add_left, sum_inner, inner_smul_left,
        RCLike.conj_to_real, Finset.mul_sum, Nat.cast_ofNat]
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      field_simp
    have h1 := key z
    rw [hD0, zero_apply, eq_comm, inner_self_eq_zero] at h1
    exact h1
  refine ⟨x, w, v, fun i ↦ ⟨hwK i, ?_⟩, ?_, ?_, ?_, fun i ↦ ?_⟩
  · rw [show v i = ρ⁻¹ • (x + b i - w i) from rfl, toDual_smul]
    refine smul_mem_regularNormalCone (toDual_sub_mem_regularNormalCone ⟨hwK i, ?_⟩)
      (inv_nonneg.2 hρ.le)
    rw [← hy]
  · simp only [v, norm_smul, mul_pow, Real.norm_eq_abs, abs_inv, abs_of_pos hρ, inv_pow,
      ← Finset.mul_sum]
    rw [hρS]; exact inv_mul_cancel₀ hSpos.ne'
  · rw [neg_smul, eq_neg_iff_add_eq_zero]; exact hz
  · have := hx x₀
    rw [hfx] at this
    linarith [hf_ge x₀, hfx₀, hρ.le]
  · have h1 : ‖y i‖ ≤ ρ := by
      rw [Real.le_sqrt (norm_nonneg _) hS0]
      exact Finset.single_le_sum (f := fun i ↦ ‖y i‖ ^ 2) (fun i _ ↦ by positivity)
        (Finset.mem_univ i)
    have := hx x₀
    rw [hfx] at this
    linarith [sq_nonneg ‖x - x₀‖]


/-- Thm. 2.3 of [Mordukhovich 2018] (basic extremal principle) in a finite-dimensional inner
product space: if `x₀` is a locally extremal point of finitely many sets locally closed around
`x₀`, there are basic normals `vᵢ ∈ N(x₀; Ωᵢ)` with `∑ vᵢ = 0` and `∑ ‖vᵢ‖² = 1` (2.4)–(2.5). -/
theorem IsLocallyExtremal.exists_mem_normalCone_inner {Ω : ι → Set H} {x₀ : H}
    (h : IsLocallyExtremal Ω x₀) (hloc : ∀ i, ∃ r > 0, IsClosed (Ω i ∩ closedBall x₀ r)) :
    ∃ v : ι → StrongDual ℝ H, (∀ i, v i ∈ normalCone (Ω i) x₀) ∧ ∑ i, v i = 0 ∧
      ∑ i, ‖v i‖ ^ 2 = 1 := by
  obtain ⟨a, ha, R₀, hR₀, hglob⟩ := h.exists_global
  choose r hr hcl using hloc
  obtain ⟨R₁, hR₁, hR₁r⟩ := exists_pos_forall_le r hr
  set R := min R₀ R₁
  have hR : 0 < R := lt_min hR₀ hR₁
  -- localize: the sets `Kᵢ = Ωᵢ ∩ B(x₀, R)` are compact and extremal with `U = H`
  set K : ι → Set H := fun i ↦ Ω i ∩ closedBall x₀ R
  have hKc : ∀ i, IsCompact (K i) := fun i ↦ (isCompact_closedBall x₀ R).of_isClosed_subset
    (isClosed_inter_closedBall_of_le (hcl i) ((min_le_right _ _).trans (hR₁r i)))
    inter_subset_right
  have hx₀K : ∀ i, x₀ ∈ K i := fun i ↦ ⟨h.1 i, mem_closedBall_self hR.le⟩
  have hKΩ : ∀ i, K i =ᶠ[𝓝 x₀] Ω i := fun i ↦ by
    rw [eventuallyEq_set]
    filter_upwards [closedBall_mem_nhds x₀ hR] with y hy
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hy⟩⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hglob R hR (min_le_left _ _))
  have hstep := fun k ↦ exists_metric_approx hKc hx₀K (b := fun i ↦ a i (k + N))
    (hN _ (Nat.le_add_left _ _))
  choose x w v hmem hnorm hsum hxb hwb using hstep
  set β : ℕ → ℝ := fun k ↦ √(∑ i, ‖a i (k + N)‖ ^ 2)
  have hβ : Tendsto β atTop (𝓝 0) := by
    have h1 : Tendsto (fun k ↦ ∑ i, ‖a i (k + N)‖ ^ 2) atTop (𝓝 (∑ _i : ι, ‖(0 : H)‖ ^ 2)) :=
      tendsto_finsetSum _ fun i _ ↦ ((ha i).comp (tendsto_add_atTop_nat N)).norm.pow 2
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto _).comp h1
  have hβ0 : ∀ k, 0 ≤ β k := fun k ↦ Real.sqrt_nonneg _
  have hsβ : Tendsto (fun k ↦ √(β k)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto _).comp hβ
  have hxk : ∀ k, ‖x k - x₀‖ ≤ √(β k) := fun k ↦
    (Real.le_sqrt (norm_nonneg _) (hβ0 k)).2 (hxb k)
  have hx : Tendsto x atTop (𝓝 x₀) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ ↦ norm_nonneg _) hxk hsβ
  have hw : ∀ i, Tendsto (fun k ↦ w k i) atTop (𝓝 x₀) := fun i ↦ by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have ha' : Tendsto (fun k ↦ ‖a i (k + N)‖) atTop (𝓝 0) := by
      simpa using ((ha i).comp (tendsto_add_atTop_nat N)).norm
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ ?_)
      (by simpa using (hβ.add hsβ).add ha')
    have : w k i - x₀ = (x k - x₀) + a i (k + N) - (x k + a i (k + N) - w k i) := by abel
    rw [this]
    exact (norm_sub_le _ _).trans (by
      linarith [norm_add_le (x k - x₀) (a i (k + N)), hwb k i, hxk k])
  -- compactness of the unit sphere
  have hV : ∀ k, (fun i ↦ v k i) ∈ closedBall (0 : ι → H) 1 := fun k ↦ by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have h1 : ‖v k i‖ ^ 2 ≤ 1 := hnorm k ▸ Finset.single_le_sum
      (f := fun i ↦ ‖v k i‖ ^ 2) (fun i _ ↦ by positivity) (Finset.mem_univ i)
    nlinarith [norm_nonneg (v k i)]
  obtain ⟨V, -, φ, hφ, hVlim⟩ := tendsto_subseq_of_bounded isBounded_closedBall hV
  have hVi : ∀ i, Tendsto (fun k ↦ v (φ k) i) atTop (𝓝 (V i)) := fun i ↦
    tendsto_pi_nhds.1 hVlim i
  have hφ' := hφ.tendsto_atTop
  refine ⟨fun i ↦ toDual ℝ H (V i), fun i ↦ ?_, ?_, ?_⟩
  · rw [← normalCone_congr (hKΩ i)]
    exact ⟨hx₀K i, fun k ↦ w (φ k) i, fun k ↦ toDual ℝ H (v (φ k) i),
      tendsto_nhdsWithin_iff.2 ⟨(hw i).comp hφ', Eventually.of_forall fun k ↦ (hmem (φ k) i).1⟩,
      ((toDual ℝ H).continuous.tendsto _).comp (hVi i), fun k ↦ (hmem (φ k) i).2⟩
  · rw [← map_sum]
    have h1 : Tendsto (fun k ↦ ∑ i, v (φ k) i) atTop (𝓝 (∑ i, V i)) :=
      tendsto_finsetSum _ fun i _ ↦ hVi i
    have h2 : Tendsto (fun k ↦ ∑ i, v (φ k) i) atTop (𝓝 0) := by
      simp only [hsum]
      simpa using ((hx.comp hφ').sub_const x₀).const_smul (-2 : ℝ)
    rw [tendsto_nhds_unique h1 h2, map_zero]
  · simp only [LinearIsometryEquiv.norm_map]
    have h1 : Tendsto (fun k ↦ ∑ i, ‖v (φ k) i‖ ^ 2) atTop (𝓝 (∑ i, ‖V i‖ ^ 2)) :=
      tendsto_finsetSum _ fun i _ ↦ (hVi i).norm.pow 2
    simp only [hnorm] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds

end Inner


section Normed

/-! ### The extremal principle in finite-dimensional normed spaces -/

variable [Fintype ι] {Ω : ι → Set E} {x₀ : E}

omit [Fintype ι] in
/-- Local extremality is preserved by continuous linear isomorphisms. -/
theorem IsLocallyExtremal.image (h : IsLocallyExtremal Ω x₀) (A : E ≃L[ℝ] F) :
    IsLocallyExtremal (fun i ↦ A '' Ω i) (A x₀) := by
  rw [isLocallyExtremal_iff] at h ⊢
  obtain ⟨hx, a, ha, U, hU, hk⟩ := h
  refine ⟨fun i ↦ mem_image_of_mem _ (hx i), fun i k ↦ A (a i k),
    fun i ↦ by simpa [Function.comp_def] using (A.continuous.tendsto 0).comp (ha i), A.symm ⁻¹' U,
    A.symm.continuous.continuousAt.preimage_mem_nhds (by simpa using hU), ?_⟩
  filter_upwards [hk] with k hk y hy
  obtain ⟨i, hi⟩ := hk _ hy
  refine ⟨i, fun ⟨z, hz, hzy⟩ ↦ hi ?_⟩
  have : A.symm y + a i k = z := A.injective (by rw [map_add, A.apply_symm_apply, hzy])
  rw [this]; exact hz

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A family of dual elements, not all zero, can be rescaled by a positive factor to satisfy
`∑ ‖vᵢ‖² = 1`. -/
theorem exists_pos_sum_norm_smul_sq_eq_one {G : Type*} [SeminormedAddCommGroup G]
    [NormedSpace ℝ G] (v : ι → G) (hv : ∃ i, ‖v i‖ ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∑ i, ‖c • v i‖ ^ 2 = 1 := by
  obtain ⟨i₀, hi₀⟩ := hv
  set S := ∑ i, ‖v i‖ ^ 2
  have hS : 0 < S := lt_of_lt_of_le (by positivity) (Finset.single_le_sum
    (f := fun i ↦ ‖v i‖ ^ 2) (fun i _ ↦ by positivity) (Finset.mem_univ i₀))
  refine ⟨(√S)⁻¹, inv_pos.2 (Real.sqrt_pos.2 hS), ?_⟩
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, abs_inv, abs_of_pos (Real.sqrt_pos.2 hS),
    inv_pow, Real.sq_sqrt hS.le, ← Finset.mul_sum]
  exact inv_mul_cancel₀ hS.ne'

/-- Thm. 2.3 of [Mordukhovich 2018] (basic extremal principle) in a finite-dimensional normed
space, norm-free form: if `x₀` is a locally extremal point of finitely many sets locally closed
around `x₀`, there are basic normals `vᵢ ∈ N(x₀; Ωᵢ)`, not all zero, with `∑ vᵢ = 0`. -/
theorem IsLocallyExtremal.exists_mem_normalCone_ne_zero [FiniteDimensional ℝ E]
    (h : IsLocallyExtremal Ω x₀) (hloc : ∀ i, ∃ r > 0, IsClosed (Ω i ∩ closedBall x₀ r)) :
    ∃ v : ι → StrongDual ℝ E, (∀ i, v i ∈ normalCone (Ω i) x₀) ∧ ∑ i, v i = 0 ∧
      ∃ i, v i ≠ 0 := by
  set G := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  set A : E ≃L[ℝ] G := toEuclidean
  obtain ⟨w, hw, hsum, hnorm⟩ :=
    (h.image A).exists_mem_normalCone_inner fun i ↦ locallyClosed_image A (hloc i)
  refine ⟨fun i ↦ (w i).comp (A : E →L[ℝ] G), fun i ↦ (mem_normalCone_image_iff A).1 (hw i),
    ?_, ?_⟩
  · ext y
    simp only [sum_apply, ContinuousLinearMap.coe_comp, Function.comp_apply, zero_apply]
    rw [← sum_apply, hsum, zero_apply]
  · by_contra hall
    push Not at hall
    have hw0 : ∀ i, w i = 0 := fun i ↦ by
      have := congrArg (fun ℓ ↦ ℓ.comp (A.symm : G →L[ℝ] E)) (hall i)
      simp only [ContinuousLinearMap.zero_comp] at this
      rw [← this]
      ext; simp
    simp [hw0] at hnorm

/-- Thm. 2.3 of [Mordukhovich 2018] (basic extremal principle) in a finite-dimensional normed
space: if `x₀` is a locally extremal point of finitely many sets locally closed around `x₀`, there
are basic normals `vᵢ ∈ N(x₀; Ωᵢ)` with `∑ vᵢ = 0` and `∑ ‖vᵢ‖² = 1` (2.4)–(2.5), for the dual
norm of `E`. -/
theorem IsLocallyExtremal.exists_mem_normalCone [FiniteDimensional ℝ E]
    (h : IsLocallyExtremal Ω x₀) (hloc : ∀ i, ∃ r > 0, IsClosed (Ω i ∩ closedBall x₀ r)) :
    ∃ v : ι → StrongDual ℝ E, (∀ i, v i ∈ normalCone (Ω i) x₀) ∧ ∑ i, v i = 0 ∧
      ∑ i, ‖v i‖ ^ 2 = 1 := by
  obtain ⟨v, hv, hsum, i₀, hi₀⟩ := h.exists_mem_normalCone_ne_zero hloc
  obtain ⟨c, hc, hc1⟩ := exists_pos_sum_norm_smul_sq_eq_one v ⟨i₀, norm_ne_zero_iff.2 hi₀⟩
  exact ⟨fun i ↦ c • v i, fun i ↦ smul_mem_normalCone (hv i) hc.le,
    by rw [← Finset.smul_sum, hsum, smul_zero], hc1⟩

omit [Fintype ι] in
/-- Thm. 2.3 of [Mordukhovich 2018] for two sets, (2.9): if `x₀` is a locally extremal point of
`{Ω₁, Ω₂}`, both locally closed around `x₀`, there is `v` with `‖v‖ = 1` (in particular
`v ≠ 0`) and `v ∈ N(x₀; Ω₁) ∩ (-N(x₀; Ω₂))`. -/
theorem IsLocallyExtremal.exists_mem_normalCone_pair [FiniteDimensional ℝ E] {Ω₁ Ω₂ : Set E}
    (h : IsLocallyExtremal ![Ω₁, Ω₂] x₀) (hloc₁ : ∃ r > 0, IsClosed (Ω₁ ∩ closedBall x₀ r))
    (hloc₂ : ∃ r > 0, IsClosed (Ω₂ ∩ closedBall x₀ r)) :
    ∃ v ∈ normalCone Ω₁ x₀, -v ∈ normalCone Ω₂ x₀ ∧ ‖v‖ = 1 := by
  obtain ⟨v, hv, hsum, i₀, hi₀⟩ := h.exists_mem_normalCone_ne_zero fun i ↦ by
    fin_cases i
    · simpa using hloc₁
    · simpa using hloc₂
  rw [Fin.sum_univ_two] at hsum
  have h1 : v 1 = -v 0 := eq_neg_of_add_eq_zero_right hsum
  have h0 : v 0 ≠ 0 := by
    fin_cases i₀
    · exact hi₀
    · intro h0; apply hi₀; simp [h1, h0]
  have hn : 0 < ‖v 0‖ := norm_pos_iff.2 h0
  refine ⟨‖v 0‖⁻¹ • v 0, smul_mem_normalCone (by simpa using hv 0) (inv_nonneg.2 hn.le), ?_, ?_⟩
  · rw [← smul_neg (‖v 0‖⁻¹) (v 0), ← h1]
    exact smul_mem_normalCone (by simpa using hv 1) (inv_nonneg.2 hn.le)
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']

omit [Fintype ι] in
/-- [Mordukhovich 2018, p. 72]: applying the extremal principle to `{Ω, {x₀}}` recovers
Prop. 1.2: at a boundary point of a locally closed set there is a unit basic normal. -/
theorem exists_mem_normalCone_norm_eq_one_of_mem_frontier [FiniteDimensional ℝ E] {Ω : Set E}
    (hx₀ : x₀ ∈ Ω) (hloc : ∃ r > 0, IsClosed (Ω ∩ closedBall x₀ r)) (hfr : x₀ ∈ frontier Ω) :
    ∃ v ∈ normalCone Ω x₀, ‖v‖ = 1 := by
  rw [frontier, Set.mem_sdiff, ← mem_compl_iff, ← closure_compl] at hfr
  obtain ⟨z, hzΩ, hz⟩ := mem_closure_iff_seq_limit.1 hfr.2
  have hext : IsLocallyExtremal ![{x₀}, Ω] x₀ := by
    refine isLocallyExtremal_pair_iff.2 ⟨rfl, hx₀, fun k ↦ z k - x₀,
      by simpa using hz.sub_const x₀, univ, univ_mem, Eventually.of_forall ?_⟩
    rintro k x - rfl
    simpa using hzΩ k
  obtain ⟨v, -, hv, hv1⟩ := hext.exists_mem_normalCone_pair
    ⟨1, one_pos, isClosed_singleton.inter isClosed_closedBall⟩ hloc
  exact ⟨-v, hv, by rw [norm_neg, hv1]⟩

/-- Cor. 2.5 of [Mordukhovich 2018] (approximate extremal principle): if `x₀` is a locally
extremal point of finitely many sets locally closed around `x₀`, then for every `ε > 0` there are
points `xᵢ ∈ Ωᵢ ∩ (x₀ + εB)` and `vᵢ ∈ N̂(xᵢ; Ωᵢ) + εB` with `∑ vᵢ = 0` and `∑ ‖vᵢ‖² = 1`
(2.11). -/
theorem IsLocallyExtremal.exists_approx [FiniteDimensional ℝ E] (h : IsLocallyExtremal Ω x₀)
    (hloc : ∀ i, ∃ r > 0, IsClosed (Ω i ∩ closedBall x₀ r)) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : ι → E, ∃ v : ι → StrongDual ℝ E,
      (∀ i, x i ∈ Ω i ∧ ‖x i - x₀‖ ≤ ε ∧ ∃ u ∈ regularNormalCone (Ω i) (x i), ‖v i - u‖ ≤ ε) ∧
      ∑ i, v i = 0 ∧ ∑ i, ‖v i‖ ^ 2 = 1 := by
  obtain ⟨v, hv, hsum, hnorm⟩ := h.exists_mem_normalCone hloc
  have key : ∀ i, ∃ y ∈ Ω i, ‖y - x₀‖ ≤ ε ∧ ∃ u ∈ regularNormalCone (Ω i) y, ‖v i - u‖ ≤ ε :=
    fun i ↦ by
      obtain ⟨-, a, w, ha, hw, hmem⟩ := hv i
      have ha' := tendsto_nhdsWithin_iff.1 ha
      have h1 := (tendsto_iff_norm_sub_tendsto_zero.1 ha'.1).eventually (gt_mem_nhds hε)
      have h2 := (tendsto_iff_norm_sub_tendsto_zero.1 hw).eventually (gt_mem_nhds hε)
      obtain ⟨k, hk1, hk2, hk3⟩ := (ha'.2.and (h1.and h2)).exists
      exact ⟨a k, hk1, hk2.le, w k, hmem k, by rw [norm_sub_rev]; exact hk3.le⟩
  choose x hx using key
  exact ⟨x, v, fun i ↦ ⟨(hx i).1, (hx i).2⟩, hsum, hnorm⟩

/-- Prop. 2.2(ii) of [Mordukhovich 2018]: locally extremal systems of convex sets locally closed
around the extremal point are separated. -/
theorem AreSeparated.of_isLocallyExtremal [FiniteDimensional ℝ E]
    (hconv : ∀ i, Convex ℝ (Ω i)) (hloc : ∀ i, ∃ r > 0, IsClosed (Ω i ∩ closedBall x₀ r))
    (h : IsLocallyExtremal Ω x₀) : AreSeparated Ω := by
  obtain ⟨v, hv, hsum, hne⟩ := h.exists_mem_normalCone_ne_zero hloc
  refine ⟨v, fun i ↦ v i x₀, hne, fun i x hx ↦ ?_, hsum, ?_⟩
  · have := ((mem_normalCone_of_convex (hconv i) (h.1 i)).1 (hv i)) x hx
    rw [map_sub] at this
    linarith
  · rw [← sum_apply, hsum, zero_apply]

/-- Prop. 2.2(iii) of [Mordukhovich 2018]: closed convex sets with a common point are separated
iff each of their common points is locally extremal. -/
theorem areSeparated_iff_forall_isLocallyExtremal [FiniteDimensional ℝ E]
    (hconv : ∀ i, Convex ℝ (Ω i)) (hcl : ∀ i, IsClosed (Ω i)) (hne : ∃ x₀, ∀ i, x₀ ∈ Ω i) :
    AreSeparated Ω ↔ ∀ x₀, (∀ i, x₀ ∈ Ω i) → IsLocallyExtremal Ω x₀ := by
  refine ⟨fun h x₀ hx ↦ h.isLocallyExtremal hx, fun h ↦ ?_⟩
  obtain ⟨x₀, hx₀⟩ := hne
  exact AreSeparated.of_isLocallyExtremal hconv
    (fun i ↦ ⟨1, one_pos, (hcl i).inter isClosed_closedBall⟩) (h x₀ hx₀)

end Normed

end VariationalAnalysis
