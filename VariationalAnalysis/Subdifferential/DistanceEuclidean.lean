/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.InnerProductSpace.Dual
import ConvexAnalysis.Convex.Radial
import VariationalAnalysis.Normal.Projection
import VariationalAnalysis.Subdifferential.Distance

/-!
# Subgradients of the distance function at out-of-set points

In a finite-dimensional real inner product space `H`, for `Ω` closed and nonempty and `x₀ ∉ Ω`,
with `d = dist(x₀; Ω)` and Euclidean projector `Π(x₀; Ω)`:

## Main results

* `regularSubdiff_distFun_subset`, `regularSubdiff_distFun_of_proj_eq`: Thm. 1.33(ii), first
  formula in (1.44), of [Mordukhovich 2018]: `∂̂d_Ω(x₀) = {(x₀ - w) / d}` if `Π(x₀; Ω) = {w}`, and
  `∂̂d_Ω(x₀) = ∅` if the projection is not unique (`regularSubdiff_distFun_eq_empty`).
* `subdiff_distFun_of_notMem`: Thm. 1.33(ii), second formula in (1.44):
  `∂d_Ω(x₀) = (x₀ - Π(x₀; Ω)) / d`.
-/

open Filter Topology Set Metric InnerProductSpace

namespace VariationalAnalysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Ω : Set H} {x₀ : H}

local notation "⟪" a ", " b "⟫" => @inner ℝ _ _ a b

theorem hasFDerivAt_norm_sub [CompleteSpace H] {w : H} (h : x₀ ≠ w) :
    HasFDerivAt (fun x ↦ ‖x - w‖) (toDual ℝ H (‖x₀ - w‖⁻¹ • (x₀ - w))) x₀ := by
  have := (hasFDerivAt_norm_of_ne_zero (sub_ne_zero.2 h)).comp x₀
    ((hasFDerivAt_id x₀).sub_const w)
  refine this.congr_fderiv ?_
  ext y
  simp

/-- The norm inequality `‖a‖ + ⟪a / ‖a‖, h⟫ ≤ ‖a + h‖` (the gradient inequality of the norm). -/
theorem norm_add_inner_le {a h : H} (ha : a ≠ 0) : ‖a‖ + ⟪‖a‖⁻¹ • a, h⟫ ≤ ‖a + h‖ := by
  have hpos : 0 < ‖a‖ := norm_pos_iff.2 ha
  have h1 : ⟪a, a + h⟫ ≤ ‖a‖ * ‖a + h‖ := real_inner_le_norm _ _
  rw [inner_add_right, real_inner_self_eq_norm_sq] at h1
  rw [real_inner_smul_left]
  have h2 : ‖a‖ * (‖a‖ + ‖a‖⁻¹ * ⟪a, h⟫) = ‖a‖ ^ 2 + ⟪a, h⟫ := by field_simp
  exact le_of_mul_le_mul_left (h2 ▸ h1) hpos

omit [InnerProductSpace ℝ H] in
theorem mem_euclideanProj_iff {x w : H} :
    w ∈ euclideanProj Ω x ↔ w ∈ Ω ∧ infDist x Ω = dist x w := by
  rw [euclideanProj, mem_ofPred_eq, dist_eq_norm, eq_comm]

/-- Thm. 1.33(ii) of [Mordukhovich 2018], first formula in (1.44), inclusion: for every
projection `w ∈ Π(x₀; Ω)` of `x₀ ∉ Ω`, `∂̂d_Ω(x₀) ⊆ {(x₀ - w) / d}`. -/
theorem regularSubdiff_distFun_subset [CompleteSpace H] {w : H} (hw : w ∈ euclideanProj Ω x₀)
    (hx : x₀ ∉ Ω) :
    regularSubdiff (distFun Ω) x₀ ⊆ {toDual ℝ H ((infDist x₀ Ω)⁻¹ • (x₀ - w))} := by
  have hne : x₀ ≠ w := fun h ↦ hx (h ▸ hw.1)
  have hle : ∀ x, distFun Ω x ≤ ((‖x - w‖ : ℝ) : EReal) := fun x ↦ by
    simp only [distFun, EReal.coe_le_coe_iff]
    rw [← dist_eq_norm]; exact infDist_le_dist_of_mem hw.1
  have heq : distFun Ω x₀ = ((‖x₀ - w‖ : ℝ) : EReal) := by rw [hw.2]; rfl
  refine (regularSubdiff_subset_of_le (Eventually.of_forall hle) heq).trans ?_
  rw [regularSubdiff_of_hasFDerivAt (hasFDerivAt_norm_sub hne), hw.2]

/-- Thm. 1.33(ii) of [Mordukhovich 2018]: if the projection of `x₀ ∉ Ω` is not unique, then
`∂̂d_Ω(x₀) = ∅`. -/
theorem regularSubdiff_distFun_eq_empty [CompleteSpace H] {w₁ w₂ : H}
    (hw₁ : w₁ ∈ euclideanProj Ω x₀) (hw₂ : w₂ ∈ euclideanProj Ω x₀) (hne : w₁ ≠ w₂)
    (hx : x₀ ∉ Ω) : regularSubdiff (distFun Ω) x₀ = ∅ := by
  refine eq_empty_of_forall_notMem fun v hv ↦ hne ?_
  have h1 := regularSubdiff_distFun_subset hw₁ hx hv
  have h2 := regularSubdiff_distFun_subset hw₂ hx hv
  rw [mem_singleton_iff] at h1 h2
  have hd : infDist x₀ Ω ≠ 0 := by
    rw [← hw₁.2]; exact norm_ne_zero_iff.2 (sub_ne_zero.2 fun h ↦ hx (h ▸ hw₁.1))
  have := (toDual ℝ H).injective (h1.symm.trans h2)
  have := congrArg (fun y ↦ infDist x₀ Ω • y) this
  simp only [smul_smul, mul_inv_cancel₀ hd, one_smul] at this
  exact (sub_right_injective this)

/-- Projections of points converging to `x₀` have a subsequence converging to a projection of
`x₀` (finite dimensions, `Ω` closed). -/
theorem exists_subseq_tendsto_euclideanProj [FiniteDimensional ℝ H] (hΩ : IsClosed Ω)
    {a w : ℕ → H} (ha : Tendsto a atTop (𝓝 x₀)) (hw : ∀ k, w k ∈ euclideanProj Ω (a k)) :
    ∃ w' ∈ euclideanProj Ω x₀, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (w ∘ φ) atTop (𝓝 w') := by
  set d := infDist x₀ Ω
  have hbd : ∀ᶠ k in atTop, w k ∈ closedBall x₀ (d + 2) := by
    filter_upwards [(tendsto_iff_norm_sub_tendsto_zero.1 ha).eventually (ge_mem_nhds one_pos)]
      with k hk
    rw [mem_closedBall, dist_eq_norm]
    have h1 := norm_sub_le_norm_sub_add_norm_sub (w k) (a k) x₀
    have h2 : ‖w k - a k‖ = infDist (a k) Ω := by rw [norm_sub_rev]; exact (hw k).2
    have h3 : infDist (a k) Ω ≤ d + dist (a k) x₀ := infDist_le_infDist_add_dist
    rw [dist_eq_norm] at h3
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 hbd
  obtain ⟨w', -, ψ, hψ, hlim⟩ := (isCompact_closedBall x₀ (d + 2)).tendsto_subseq
    (x := fun k ↦ w (k + N)) fun k ↦ hN _ (Nat.le_add_left N k)
  set φ : ℕ → ℕ := fun k ↦ ψ k + N
  have hφ : StrictMono φ := fun i j hij ↦ Nat.add_lt_add_right (hψ hij) N
  have hwφ : Tendsto (w ∘ φ) atTop (𝓝 w') := hlim
  have haφ : Tendsto (a ∘ φ) atTop (𝓝 x₀) := ha.comp hφ.tendsto_atTop
  have hw'Ω : w' ∈ Ω := hΩ.mem_of_tendsto hwφ (Eventually.of_forall fun k ↦ (hw (φ k)).1)
  refine ⟨w', ⟨hw'Ω, ?_⟩, φ, hφ, hwφ⟩
  have h1 : Tendsto (fun k ↦ ‖a (φ k) - w (φ k)‖) atTop (𝓝 ‖x₀ - w'‖) :=
    (continuous_norm.tendsto _).comp (haφ.sub hwφ)
  have h2 : Tendsto (fun k ↦ infDist (a (φ k)) Ω) atTop (𝓝 d) :=
    (continuous_infDist_pt Ω |>.tendsto x₀).comp haφ
  exact tendsto_nhds_unique h1 (h2.congr fun k ↦ ((hw (φ k)).2).symm)

/-- Thm. 1.33(ii) of [Mordukhovich 2018], first formula in (1.44): if `Π(x₀; Ω) = {w}` for
`x₀ ∉ Ω`, then `∂̂d_Ω(x₀) = {(x₀ - w) / d}`. -/
theorem regularSubdiff_distFun_of_proj_eq [FiniteDimensional ℝ H] (hΩ : IsClosed Ω)
    (hx : x₀ ∉ Ω) {w : H} (hproj : euclideanProj Ω x₀ = {w}) :
    regularSubdiff (distFun Ω) x₀ = {toDual ℝ H ((infDist x₀ Ω)⁻¹ • (x₀ - w))} := by
  have hw : w ∈ euclideanProj Ω x₀ := hproj ▸ mem_singleton w
  refine subset_antisymm (regularSubdiff_distFun_subset hw hx) ?_
  rintro _ rfl
  set d := infDist x₀ Ω
  have hne : x₀ ≠ w := fun h ↦ hx (h ▸ hw.1)
  have hd : 0 < d := lt_of_lt_of_eq (norm_pos_iff.2 (sub_ne_zero.2 hne)) hw.2
  set e : H := d⁻¹ • (x₀ - w)
  rw [mem_regularSubdiff_iff (φ := distFun Ω) (r := d) rfl]
  intro ε hε
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨x, hxlim, hxv⟩ := exists_seq_forall_of_frequently hcon
  have hne' : Ω.Nonempty := ⟨w, hw.1⟩
  have hproj' : ∀ k, ∃ z ∈ Ω, infDist (x k) Ω = dist (x k) z :=
    fun k ↦ hΩ.exists_infDist_eq_dist hne' (x k)
  choose z hz hdz using hproj'
  have hzp : ∀ k, z k ∈ euclideanProj Ω (x k) := fun k ↦ mem_euclideanProj_iff.2 ⟨hz k, hdz k⟩
  obtain ⟨w', hw', φ, hφ, hzφ⟩ := exists_subseq_tendsto_euclideanProj hΩ hxlim hzp
  rw [hproj, mem_singleton_iff] at hw'
  subst hw'
  have hxφ : Tendsto (x ∘ φ) atTop (𝓝 x₀) := hxlim.comp hφ.tendsto_atTop
  -- unit vectors `(x₀ - zₖ) / ‖x₀ - zₖ‖ → e`
  have hzne : ∀ k, x₀ - z k ≠ 0 := fun k h ↦ hx (sub_eq_zero.1 h ▸ hz k)
  have he : Tendsto (fun k ↦ ‖x₀ - z (φ k)‖⁻¹ • (x₀ - z (φ k))) atTop (𝓝 e) := by
    have h1 : Tendsto (fun k ↦ x₀ - z (φ k)) atTop (𝓝 (x₀ - w')) :=
      tendsto_const_nhds.sub hzφ
    have h2 := ((continuous_norm.tendsto _).comp h1).inv₀ (norm_ne_zero_iff.2 (sub_ne_zero.2 hne))
    have := h2.smul h1
    rwa [hw.2] at this
  obtain ⟨K, hK⟩ := eventually_atTop.1 ((tendsto_iff_norm_sub_tendsto_zero.1 he).eventually
    (Iio_mem_nhds hε))
  have hk : ‖‖x₀ - z (φ K)‖⁻¹ • (x₀ - z (φ K)) - e‖ < ε := hK K le_rfl
  set k := φ K
  have hxk := hxv k
  simp only [distFun, EReal.coe_le_coe_iff, not_le, toDual_apply_apply] at hxk
  -- the gradient inequality of the norm at `x₀ - zₖ`
  have hineq := norm_add_inner_le (h := x k - x₀) (hzne k)
  rw [show x₀ - z k + (x k - x₀) = x k - z k by abel] at hineq
  have hdzk : ‖x k - z k‖ = infDist (x k) Ω := by rw [hdz k, dist_eq_norm]
  have hdz' : d ≤ ‖x₀ - z k‖ := by rw [← dist_eq_norm]; exact infDist_le_dist_of_mem (hz k)
  have hcs : ⟪‖x₀ - z k‖⁻¹ • (x₀ - z k) - e, x k - x₀⟫ ≥ -(ε * ‖x k - x₀‖) := by
    have := real_inner_le_norm (‖x₀ - z k‖⁻¹ • (x₀ - z k) - e) (x k - x₀)
    have h2 := real_inner_le_norm (-(‖x₀ - z k‖⁻¹ • (x₀ - z k) - e)) (x k - x₀)
    rw [inner_neg_left, norm_neg] at h2
    nlinarith [norm_nonneg (x k - x₀)]
  rw [inner_sub_left] at hcs
  linarith

/-- On the open segment from `x₀ ∉ Ω` to a projection `w`, the projection is unique and equal
to `w` (strict convexity of the Euclidean norm). -/
theorem euclideanProj_segment {w : H} (hw : w ∈ euclideanProj Ω x₀) (hx : x₀ ∉ Ω) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    euclideanProj Ω (x₀ + t • (w - x₀)) = {w} ∧
      infDist (x₀ + t • (w - x₀)) Ω = (1 - t) * infDist x₀ Ω := by
  set d := infDist x₀ Ω
  set z := x₀ + t • (w - x₀)
  have hne : x₀ ≠ w := fun h ↦ hx (h ▸ hw.1)
  have hzw : z - w = (1 - t) • (x₀ - w) := by simp only [z]; module
  have hxz : x₀ - z = t • (x₀ - w) := by simp only [z]; module
  have hnzw : ‖z - w‖ = (1 - t) * d := by
    rw [hzw, norm_smul, Real.norm_of_nonneg (by linarith), hw.2]
  have hnxz : ‖x₀ - z‖ = t * d := by rw [hxz, norm_smul, Real.norm_of_nonneg ht0.le, hw.2]
  have hdz : infDist z Ω = (1 - t) * d := by
    refine le_antisymm ?_ ?_
    · rw [← hnzw, ← dist_eq_norm]; exact infDist_le_dist_of_mem hw.1
    · have := infDist_le_infDist_add_dist (x := x₀) (y := z) (s := Ω)
      rw [dist_eq_norm, hnxz] at this
      linarith
  refine ⟨subset_antisymm (fun w' hw' ↦ ?_) ?_, hdz⟩
  · rw [mem_singleton_iff]
    have h1 : ‖z - w'‖ = (1 - t) * d := hw'.2.trans hdz
    have h2 : d ≤ ‖x₀ - w'‖ := by rw [← dist_eq_norm]; exact infDist_le_dist_of_mem hw'.1
    have h3 : ‖(x₀ - z) + (z - w')‖ = ‖x₀ - z‖ + ‖z - w'‖ := by
      refine le_antisymm (norm_add_le _ _) ?_
      rw [show x₀ - z + (z - w') = x₀ - w' by abel, hnxz, h1]
      linarith
    have hsr := sameRay_iff_norm_add.2 h3
    have hxz0 : x₀ - z ≠ 0 := by
      rw [hxz]; exact smul_ne_zero ht0.ne' (sub_ne_zero.2 hne)
    obtain ⟨c, hc, hcz⟩ := hsr.exists_nonneg_left hxz0
    have hd : 0 < d := lt_of_lt_of_eq (norm_pos_iff.2 (sub_ne_zero.2 hne)) hw.2
    have hcval : c * t = 1 - t := by
      have := congrArg norm hcz
      rw [norm_smul, Real.norm_of_nonneg hc, hnxz, h1] at this
      have := mul_right_cancel₀ hd.ne' (by linarith : c * t * d = (1 - t) * d)
      linarith
    have : w' = z - c • (x₀ - z) := by rw [hcz]; abel
    rw [this, hxz, smul_smul, hcval]
    simp only [z]
    module
  · rintro _ rfl
    exact ⟨hw.1, by rw [hnzw, hdz]⟩

/-- Thm. 1.33(ii) of [Mordukhovich 2018], second formula in (1.44): for `Ω` closed and nonempty
in finite dimensions and `x₀ ∉ Ω`, `∂d_Ω(x₀) = (x₀ - Π(x₀; Ω)) / d`. -/
theorem subdiff_distFun_of_notMem [FiniteDimensional ℝ H] (hΩ : IsClosed Ω) (hne : Ω.Nonempty)
    (hx : x₀ ∉ Ω) :
    subdiff (distFun Ω) x₀ =
      (fun w ↦ toDual ℝ H ((infDist x₀ Ω)⁻¹ • (x₀ - w))) '' euclideanProj Ω x₀ := by
  set d := infDist x₀ Ω
  have hd : 0 < d := (hΩ.notMem_iff_infDist_pos hne).1 hx
  rw [subdiff_eq_outerLimit (φ := distFun Ω) (x₀ := x₀) (r := d) rfl]
  ext v
  constructor
  · rintro ⟨a, u, ha, hu, hmem⟩
    obtain ⟨ha1, ha2⟩ := tendsto_funNhds_iff.1 ha
    have ha2' : Tendsto (fun k ↦ infDist (a k) Ω) atTop (𝓝 d) :=
      (continuous_infDist_pt Ω |>.tendsto x₀).comp ha1
    have hproj : ∀ k, ∃ z ∈ Ω, infDist (a k) Ω = dist (a k) z :=
      fun k ↦ hΩ.exists_infDist_eq_dist hne (a k)
    choose z hz hdz using hproj
    have hzp : ∀ k, z k ∈ euclideanProj Ω (a k) := fun k ↦ mem_euclideanProj_iff.2 ⟨hz k, hdz k⟩
    obtain ⟨w, hw, φ, hφ, hzφ⟩ := exists_subseq_tendsto_euclideanProj hΩ ha1 hzp
    have hout : ∀ᶠ k in atTop, a k ∉ Ω := by
      filter_upwards [ha2'.eventually (lt_mem_nhds hd)] with k hk hmemk
      rw [infDist_zero_of_mem hmemk] at hk
      exact lt_irrefl _ hk
    have hueq : ∀ᶠ k in atTop, u k = toDual ℝ H ((infDist (a k) Ω)⁻¹ • (a k - z k)) :=
      hout.mono fun k hk ↦ regularSubdiff_distFun_subset (hzp k) hk (hmem k)
    refine ⟨w, hw, tendsto_nhds_unique ?_ (hu.comp hφ.tendsto_atTop)⟩
    have hlim : Tendsto (fun k ↦ toDual ℝ H ((infDist (a (φ k)) Ω)⁻¹ • (a (φ k) - z (φ k))))
        atTop (𝓝 (toDual ℝ H (d⁻¹ • (x₀ - w)))) :=
      ((toDual ℝ H).continuous.tendsto _).comp
        (((ha2'.comp hφ.tendsto_atTop).inv₀ hd.ne').smul
          ((ha1.comp hφ.tendsto_atTop).sub hzφ))
    exact hlim.congr' ((hφ.tendsto_atTop.eventually hueq).mono fun k hk ↦ hk.symm)
  · rintro ⟨w, hw, rfl⟩
    set t : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 2)
    have ht0 : ∀ k, 0 < t k := fun k ↦ by positivity
    have ht1 : ∀ k, t k < 1 := fun k ↦ by
      simp only [t]; rw [div_lt_one (by positivity)]; linarith [k.cast_nonneg (α := ℝ)]
    have htlim : Tendsto t atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    set z : ℕ → H := fun k ↦ x₀ + t k • (w - x₀)
    have hz : Tendsto z atTop (𝓝 x₀) := by
      simpa using tendsto_const_nhds.add (htlim.smul_const (w - x₀))
    refine ⟨z, fun _ ↦ toDual ℝ H (d⁻¹ • (x₀ - w)), tendsto_funNhds_iff.2 ⟨hz, ?_⟩,
      tendsto_const_nhds, fun k ↦ ?_⟩
    · exact EReal.tendsto_coe.2 ((continuous_infDist_pt Ω |>.tendsto x₀).comp hz)
    · obtain ⟨hpk, hdk⟩ := euclideanProj_segment hw hx (ht0 k) (ht1 k)
      have hzk : z k ∉ Ω := fun h ↦ by
        have := infDist_zero_of_mem h
        rw [hdk] at this
        have : 0 < (1 - t k) * d := mul_pos (by linarith [ht1 k]) hd
        linarith
      have h1 : 1 - t k ≠ 0 := by linarith [ht1 k]
      have hvec : ((1 - t k) * d)⁻¹ • (z k - w) = d⁻¹ • (x₀ - w) := by
        rw [show z k - w = (1 - t k) • (x₀ - w) by simp only [z]; module, smul_smul, mul_inv,
          mul_comm ((1 - t k)⁻¹), mul_assoc, inv_mul_cancel₀ h1, mul_one]
      have := regularSubdiff_distFun_of_proj_eq hΩ hzk hpk
      rw [show infDist (z k) Ω = (1 - t k) * d from hdk, hvec] at this
      rw [this]
      exact mem_singleton _

end VariationalAnalysis
