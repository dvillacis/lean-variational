/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.LocallyConvex.Separation
import VariationalAnalysis.Subdifferential.MeanValueIneq
import VariationalAnalysis.Coderivative.SecondOrder

/-!
# Basic subgradients of `-f` for Lipschitz `f`

For a function `f` Lipschitz around `x₀` in finite dimensions,
`∂(-f)(x₀) ⊆ -co ∂f(x₀)`. In [Mordukhovich 2018] this follows from the symmetry
`∂̄(-f)(x₀) = -∂̄f(x₀)` of the convexified (Clarke) subdifferential (1.79) and its representation
`∂̄f(x₀) = co ∂f(x₀)` (1.83); it is used in the proof of Thm. 6.21 for `f = μ`, the lower-level
value function of a bilevel program. The inclusion is proved directly here; it is also a
consequence of `subdiff_neg_subset_neg_clarkeSubdiff` and `clarkeSubdiff_eq_convexHull` in
`VariationalAnalysis.Subdifferential.Clarke`, which formalizes the convexified subdifferential.

## Main results

* `isCompact_convexHull_of_isCompact`: in finite dimensions the convex hull of a compact set is
  compact (a consequence of Carathéodory's theorem).
* `mem_subdiff_of_tendsto`: robustness of basic subgradients of a function continuous at `x₀`.
* `neg_mem_convexHull_subdiff_of_mem_subdiff_neg`: `∂(-f)(x₀) ⊆ -co ∂f(x₀)`.

## Proof

If `-u ∉ co ∂f(x₀)` for some `u ∈ ∂(-f)(x₀)`, a direction `d` separates `-u` from the compact
convex set `co ∂f(x₀)`: `⟨-u, d⟩ < a < ⟨w, d⟩` for `w ∈ ∂f(x₀)`. By robustness and boundedness of
`∂f`, the same bound (with a smaller margin) holds for `w ∈ ∂f(c)` with `c` near `x₀`, and the
mean value inequality (Cor. 4.14(ii)) bounds `f(x + t d) - f(x)` from below. A regular
subgradient of `-f` near `x₀`, close to `u`, bounds the same increment from above, a
contradiction.
-/

open Filter Topology Set Metric
open scoped NNReal

namespace VariationalAnalysis

section ConvexHull

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- In finite dimensions the convex hull of a compact set is compact: by Carathéodory's theorem
it is the image of the compact set `Δₙ × sⁿ`, `n = dim V + 1`, under `(w, z) ↦ ∑ wᵢ zᵢ`. -/
theorem isCompact_convexHull_of_isCompact {s : Set V} (hs : IsCompact s) :
    IsCompact (convexHull ℝ s) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨s₀, hs₀⟩
  · simp
  set n := Module.finrank ℝ V + 1
  set T : Set ((Fin n → ℝ) × (Fin n → V)) := stdSimplex ℝ (Fin n) ×ˢ Set.univ.pi fun _ ↦ s
  have hT : IsCompact T :=
    IsCompact.prod (isCompact_stdSimplex ℝ (Fin n)) (isCompact_univ_pi fun _ ↦ hs)
  have hc : Continuous fun q : (Fin n → ℝ) × (Fin n → V) ↦ ∑ i, q.1 i • q.2 i := by fun_prop
  convert hT.image hc using 1
  ext x
  constructor
  · intro hx
    obtain ⟨ι, _, z, w, hzs, hai, hw0, hw1, hwx⟩ := eq_pos_convex_span_of_mem_convexHull hx
    have hcard : Fintype.card ι ≤ n :=
      hai.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
    -- pad `ι` to `Fin n`
    let e : ι ⊕ Fin (n - Fintype.card ι) ≃ Fin n :=
      ((Fintype.equivFin ι).sumCongr (Equiv.refl _)).trans
        (finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hcard)))
    let W : Fin n → ℝ := fun j ↦ Sum.elim w 0 (e.symm j)
    let Z : Fin n → V := fun j ↦ Sum.elim z (fun _ ↦ s₀) (e.symm j)
    have hsum : ∀ g : ι ⊕ Fin (n - Fintype.card ι) → V, ∑ j, g (e.symm j) = ∑ k, g k :=
      fun g ↦ Equiv.sum_comp e.symm g
    have hsumR : ∀ g : ι ⊕ Fin (n - Fintype.card ι) → ℝ, ∑ j, g (e.symm j) = ∑ k, g k :=
      fun g ↦ Equiv.sum_comp e.symm g
    refine ⟨(W, Z), ⟨⟨fun j ↦ ?_, ?_⟩, fun j _ ↦ ?_⟩, ?_⟩
    · simp only [W]
      rcases e.symm j with i | i
      · exact (hw0 i).le
      · simp
    · simp only [W]
      rw [hsumR (Sum.elim w 0), Fintype.sum_sum_type]
      simpa using hw1
    · simp only [Z]
      rcases e.symm j with i | i
      · exact hzs (mem_range_self i)
      · exact hs₀
    · simp only [W, Z]
      rw [hsum (fun k ↦ Sum.elim w 0 k • Sum.elim z (fun _ ↦ s₀) k), Fintype.sum_sum_type]
      simpa using hwx
  · rintro ⟨q, ⟨hw, hz⟩, rfl⟩
    exact (convex_convexHull ℝ s).sum_mem (fun i _ ↦ hw.1 i) hw.2
      fun i _ ↦ subset_convexHull ℝ s (hz i (mem_univ i))

end ConvexHull

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Robustness of basic subgradients of a function continuous at `x₀`: if `wₖ ∈ ∂f(cₖ)`,
`cₖ → x₀` and `wₖ → w`, then `w ∈ ∂f(x₀)`. -/
theorem mem_subdiff_of_tendsto {f : E → ℝ} {x₀ : E} (hf : ContinuousAt f x₀) {c : ℕ → E}
    {w : ℕ → StrongDual ℝ E} {w₀ : StrongDual ℝ E} (hc : Tendsto c atTop (𝓝 x₀))
    (hw : Tendsto w atTop (𝓝 w₀)) (hmem : ∀ k, w k ∈ subdiff (fun x ↦ (f x : EReal)) (c k)) :
    w₀ ∈ subdiff (fun x ↦ (f x : EReal)) x₀ := by
  have hη : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k ↦ by positivity
  choose x v hv hx _ hvw using fun k ↦
    exists_regularSubdiff_near_of_mem_subdiff (ψ := fun x ↦ (f x : EReal)) rfl (hmem k) (hη k)
  have h0 : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hx' : Tendsto x atTop (𝓝 x₀) := by
    have : Tendsto (fun k ↦ x k - c k) atTop (𝓝 0) :=
      squeeze_zero_norm (fun k ↦ (hx k).le) h0
    simpa using this.add hc
  have hv' : Tendsto v atTop (𝓝 w₀) := by
    have : Tendsto (fun k ↦ v k - w k) atTop (𝓝 0) :=
      squeeze_zero_norm (fun k ↦ (hvw k).le) h0
    simpa using this.add hw
  rw [subdiff_eq_outerLimit (φ := fun x ↦ (f x : EReal)) (r := f x₀) rfl]
  refine ⟨x, v, tendsto_funNhds_iff.2 ⟨hx', ?_⟩, hv', hv⟩
  exact (continuous_coe_real_ereal.continuousAt.comp hf).tendsto.comp hx'

variable [FiniteDimensional ℝ E]

/-- The basic subdifferential of a function Lipschitz around `x₀` is compact. -/
theorem isCompact_subdiff_of_lipschitz {f : E → ℝ} {U : Set E} {L : ℝ≥0} {x₀ : E}
    (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U) :
    IsCompact (subdiff (fun x ↦ (f x : EReal)) x₀) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_
    ((isBounded_closedBall (x := (0 : StrongDual ℝ E)) (r := L)).subset fun v hv ↦
      mem_closedBall_zero_iff.2 (norm_le_of_mem_subdiff_of_lipschitz hU hL hv))
  refine isClosed_of_closure_subset fun w hw ↦ ?_
  obtain ⟨v, hv, hvw⟩ := mem_closure_iff_seq_limit.1 hw
  exact mem_subdiff_of_tendsto (hL.continuousOn.continuousAt hU) tendsto_const_nhds hvw hv

/-- [Mordukhovich 2018, (1.79), (1.83)]: for `f` Lipschitz around `x₀` in finite dimensions,
`∂(-f)(x₀) ⊆ -co ∂f(x₀)`. -/
theorem neg_mem_convexHull_subdiff_of_mem_subdiff_neg {f : E → ℝ} {U : Set E} {L : ℝ≥0} {x₀ : E}
    (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U) {u : StrongDual ℝ E}
    (hu : u ∈ subdiff (fun x ↦ ((-f x : ℝ) : EReal)) x₀) :
    -u ∈ convexHull ℝ (subdiff (fun x ↦ (f x : EReal)) x₀) := by
  obtain ⟨ρ₀, hρ₀, hB⟩ := Metric.mem_nhds_iff.1 hU
  have hLB : LipschitzOnWith L f (ball x₀ ρ₀) := hL.mono hB
  have hC := isCompact_convexHull_of_isCompact (isCompact_subdiff_of_lipschitz hU hL)
  by_contra hnot
  obtain ⟨Φ, a, hΦu, hΦC⟩ :=
    geometric_hahn_banach_point_closed (convex_convexHull ℝ _) hC.isClosed hnot
  obtain ⟨d, rfl⟩ := inclusionInDoubleDual_surjective Φ
  simp only [NormedSpace.dual_def] at hΦu hΦC
  have hw₀ : ∀ w ∈ subdiff (fun x ↦ (f x : EReal)) x₀, a < w d :=
    fun w hw ↦ hΦC w (subset_convexHull ℝ _ hw)
  set η := a + u d with hη_def
  have hη : 0 < η := by simp only [neg_apply] at hΦu; linarith
  -- Step A: a uniform lower bound for `⟨w, d⟩`, `w ∈ ∂f(c)`, `c` near `x₀`
  have hA : ∀ᶠ c in 𝓝 x₀, ∀ w ∈ subdiff (fun x ↦ (f x : EReal)) c, a - η / 4 ≤ w d := by
    by_contra hcon
    rw [not_eventually] at hcon
    obtain ⟨c, hc, hcP⟩ := exists_seq_forall_of_frequently hcon
    simp only [not_forall, not_le, exists_prop] at hcP
    choose w hw hwd using hcP
    have hM : ∀ᶠ k in atTop, ‖w k‖ ≤ L := by
      filter_upwards [hc.eventually (isOpen_ball.mem_nhds (mem_ball_self hρ₀))] with k hk
      exact norm_le_of_mem_subdiff_of_lipschitz (isOpen_ball.mem_nhds hk) hLB (hw k)
    obtain ⟨w₀, -, ψ, hψ, hwψ⟩ := tendsto_subseq_of_frequently_bounded
      (isBounded_closedBall (x := (0 : StrongDual ℝ E)) (r := L))
      (hM.mono fun k hk ↦ mem_closedBall_zero_iff.2 hk).frequently
    have hmem := mem_subdiff_of_tendsto (hL.continuousOn.continuousAt hU)
      (hc.comp hψ.tendsto_atTop) hwψ fun k ↦ hw (ψ k)
    have hlim : Tendsto (fun k ↦ w (ψ k) d) atTop (𝓝 (w₀ d)) :=
      tendsto_dual_apply hwψ tendsto_const_nhds
    have := le_of_tendsto hlim (Eventually.of_forall fun k ↦ (hwd (ψ k)).le)
    linarith [hw₀ w₀ hmem]
  obtain ⟨ρ, hρ, hρA⟩ := Metric.eventually_nhds_iff.1 hA
  set ρ' := min ρ ρ₀
  have hρ' : 0 < ρ' := lt_min hρ hρ₀
  -- Step B: a regular subgradient of `-f` near `x₀`, close to `u`
  set ε := η / (4 * (‖d‖ + 1))
  have hε : 0 < ε := by positivity
  have hεd : ε * ‖d‖ < η / 4 := by
    rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [norm_nonneg d]
  obtain ⟨x₁, v, hv, hx₁, -, hvu⟩ := exists_regularSubdiff_near_of_mem_subdiff
    (ψ := fun x ↦ ((-f x : ℝ) : EReal)) rfl hu (lt_min (half_pos hρ') hε)
  have hvd : u d - η / 4 < v d := by
    have h1 : |(v - u) d| ≤ ‖v - u‖ * ‖d‖ := (v - u).le_opNorm d
    have h2 : ‖v - u‖ * ‖d‖ ≤ ε * ‖d‖ :=
      mul_le_mul_of_nonneg_right ((hvu.trans_le (min_le_right _ _)).le) (norm_nonneg d)
    simp only [sub_apply] at h1
    linarith [neg_abs_le ((v d) - u d)]
  rw [mem_regularSubdiff_iff (φ := fun x ↦ ((-f x : ℝ) : EReal)) rfl] at hv
  have hline : Tendsto (fun t : ℝ ↦ x₁ + t • d) (𝓝[>] 0) (𝓝 x₁) := by
    have : Tendsto (fun t : ℝ ↦ x₁ + t • d) (𝓝 0) (𝓝 (x₁ + (0 : ℝ) • d)) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖t • d‖ < ρ' / 2 := by
    have : Tendsto (fun t : ℝ ↦ t • d) (𝓝 0) (𝓝 ((0 : ℝ) • d)) :=
      (continuous_id.smul continuous_const).tendsto 0
    rw [zero_smul] at this
    exact (this.mono_left nhdsWithin_le_nhds).norm.eventually
      (gt_mem_nhds (by rw [norm_zero]; positivity))
  obtain ⟨t, ht, hts, htpos⟩ :=
    ((hline.eventually (hv ε hε)).and (hsmall.and self_mem_nhdsWithin)).exists
  have htpos' : 0 < t := htpos
  -- the regular subgradient inequality along `x₁ + t d`
  simp only [add_sub_cancel_left, map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs,
    abs_of_pos htpos', EReal.coe_le_coe_iff] at ht
  -- the mean value inequality on `[x₁ + t d, x₁]`
  have hx₁B : x₁ ∈ ball x₀ ρ' := by
    rw [mem_ball, dist_eq_norm]; linarith [hx₁.trans_le (min_le_left _ _)]
  have hx₂B : x₁ + t • d ∈ ball x₀ ρ' := by
    rw [mem_ball, dist_eq_norm, add_sub_right_comm]
    calc ‖x₁ - x₀ + t • d‖ ≤ ‖x₁ - x₀‖ + ‖t • d‖ := norm_add_le _ _
      _ < ρ' := by linarith [hx₁.trans_le (min_le_left _ _)]
  have hseg : segment ℝ (x₁ + t • d) x₁ ⊆ ball x₀ ρ' :=
    (convex_ball x₀ ρ').segment_subset hx₂B hx₁B
  obtain ⟨τ, hτ, w, hw, hmv⟩ := exists_mem_subdiff_mean_value_of_lipschitz isOpen_ball
    (hseg.trans (ball_subset_ball (min_le_right _ _))) hLB
  have hcB : x₁ + t • d + τ • (x₁ - (x₁ + t • d)) ∈ ball x₀ ρ' :=
    hseg (add_smul_sub_mem_segment hτ.1 hτ.2.le)
  have hwd : a - η / 4 ≤ w d :=
    hρA (lt_of_lt_of_le (mem_ball.1 hcB) (min_le_left _ _)) w hw
  have hdiff : x₁ - (x₁ + t • d) = -(t • d) := by abel
  rw [hdiff, map_neg, map_smul, smul_eq_mul] at hmv
  have h1 : t * (a - η / 4) ≤ t * w d := mul_le_mul_of_nonneg_left hwd htpos'.le
  have h2 : t * (u d - η / 4) < t * v d := mul_lt_mul_of_pos_left hvd htpos'
  have h3 : ε * (t * ‖d‖) < t * (η / 4) := by
    rw [mul_left_comm]; exact mul_lt_mul_of_pos_left hεd htpos'
  have h4 : 0 < t * η := mul_pos htpos' hη
  nlinarith

end VariationalAnalysis
