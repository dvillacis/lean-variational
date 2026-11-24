/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Topology.Order.IntermediateValue
import VariationalAnalysis.Subdifferential.Distance

/-!
# Right-sided subgradients and the distance function at out-of-set points

For `Ω` nonempty and `x₀` with `ρ = dist(x₀; Ω) > 0`, the `ρ`-enlargement is
`Ω(ρ) = {x | dist(x; Ω) ≤ ρ}` [Mordukhovich 2018, (1.49)].

## Main results

* `infDist_enlargement`: (1.51) of [Mordukhovich 2018]: `dist(x; Ω(ρ)) = dist(x; Ω) - ρ` for
  `x ∉ Ω(ρ)`.
* `regularSubdiff_distFun_eq_of_pos`: Lemma 1.34 of [Mordukhovich 2018]:
  `∂̂d_Ω(x₀) = N̂(x₀; Ω(ρ)) ∩ {‖v‖ = 1}`.
* `rightSubdiff`: Def. 1.36 of [Mordukhovich 2018], the right-sided limiting subdifferential;
  `regularSubdiff_subset_rightSubdiff`, `rightSubdiff_subset_subdiff`,
  `rightSubdiff_eq_subdiff_of_isLocalMin`: Prop. 1.37(i).
* `rightSubdiff_distFun_subset`, `mem_normalCone_enlargement_iff`: Thm. 1.38 of
  [Mordukhovich 2018] (finite dimensions).
-/

open Filter Topology Set Metric

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : Set E} {x₀ : E} {v : StrongDual ℝ E}

/-- The `ρ`-enlargement `Ω(ρ) = {x | dist(x; Ω) ≤ ρ}` [Mordukhovich 2018, (1.49)]. -/
def enlargement (Ω : Set E) (ρ : ℝ) : Set E := {x | infDist x Ω ≤ ρ}

omit [NormedSpace ℝ E] in
theorem isClosed_enlargement (Ω : Set E) (ρ : ℝ) : IsClosed (enlargement Ω ρ) :=
  isClosed_le (continuous_infDist_pt Ω) continuous_const

omit [NormedSpace ℝ E] in
theorem subset_enlargement {ρ : ℝ} (hρ : 0 ≤ ρ) : Ω ⊆ enlargement Ω ρ := fun x hx ↦ by
  simp [enlargement, infDist_zero_of_mem hx, hρ]

/-- (1.51) of [Mordukhovich 2018]: `dist(x; Ω(ρ)) = dist(x; Ω) - ρ` whenever
`dist(x; Ω) > ρ > 0`. -/
theorem infDist_enlargement (hne : Ω.Nonempty) {ρ : ℝ} (hρ : 0 < ρ) {x : E}
    (hx : ρ < infDist x Ω) : infDist x (enlargement Ω ρ) = infDist x Ω - ρ := by
  have hne' : (enlargement Ω ρ).Nonempty := hne.mono (subset_enlargement hρ.le)
  refine le_antisymm ?_ ((le_infDist hne').2 fun u hu ↦ ?_)
  · suffices h : infDist x (enlargement Ω ρ) + ρ ≤ infDist x Ω by linarith
    refine (le_infDist hne).2 fun u hu ↦ ?_
    set g : ℝ → ℝ := fun t ↦ infDist (u + t • (x - u)) Ω
    have hg : Continuous g :=
      (continuous_infDist_pt Ω).comp (continuous_const.add (continuous_id.smul continuous_const))
    have hg0 : g 0 = 0 := by simp [g, infDist_zero_of_mem hu]
    have hg1 : g 1 = infDist x Ω := by simp [g]
    obtain ⟨t, ⟨ht0, ht1⟩, hgt⟩ := intermediate_value_Icc zero_le_one hg.continuousOn
      (show ρ ∈ Icc (g 0) (g 1) by rw [hg0, hg1]; exact ⟨hρ.le, hx.le⟩)
    set z := u + t • (x - u)
    have hz : z ∈ enlargement Ω ρ := le_of_eq hgt
    have hxz : dist x z = (1 - t) * dist x u := by
      rw [dist_eq_norm, dist_eq_norm, show x - z = (1 - t) • (x - u) by simp only [z]; module,
        norm_smul, Real.norm_of_nonneg (by linarith)]
    have hzu : ρ ≤ t * dist x u := by
      have h1 := infDist_le_dist_of_mem (x := z) hu
      have h2 : infDist z Ω = ρ := hgt
      rw [h2, dist_eq_norm, show z - u = t • (x - u) by simp only [z]; module,
        norm_smul, Real.norm_of_nonneg ht0, ← dist_eq_norm] at h1
      exact h1
    have := infDist_le_dist_of_mem (x := x) hz
    linarith
  · have := infDist_le_infDist_add_dist (x := x) (y := u) (s := Ω)
    have hu' : infDist u Ω ≤ ρ := hu
    linarith

/-- The map `dist(·; Ω)` equals `dist(·; Ω(ρ)) + ρ` on the open set `{dist(·; Ω) > ρ}`. -/
theorem distFun_eventuallyEq_enlargement (hne : Ω.Nonempty) {ρ : ℝ} (hρ : 0 < ρ) {x : E}
    (hx : ρ < infDist x Ω) :
    distFun Ω =ᶠ[𝓝 x] fun y ↦ distFun (enlargement Ω ρ) y + ((ρ : ℝ) : EReal) := by
  filter_upwards [(continuous_infDist_pt Ω).continuousAt.eventually (lt_mem_nhds hx)] with y hy
  simp only [distFun, infDist_enlargement hne hρ hy, ← EReal.coe_add, sub_add_cancel]

/-- Lemma 1.34 of [Mordukhovich 2018] (regular subgradients of the distance function via regular
normals to enlargements): for `ρ = dist(x₀; Ω) > 0`,
`∂̂d_Ω(x₀) = N̂(x₀; Ω(ρ)) ∩ {‖v‖ = 1}`. -/
theorem regularSubdiff_distFun_eq_of_pos (hne : Ω.Nonempty) (hd : 0 < infDist x₀ Ω) :
    regularSubdiff (distFun Ω) x₀ =
      regularNormalCone (enlargement Ω (infDist x₀ Ω)) x₀ ∩ sphere 0 1 := by
  set ρ := infDist x₀ Ω
  have hx₀ : x₀ ∈ enlargement Ω ρ := show infDist x₀ Ω ≤ ρ from le_rfl
  ext v
  rw [mem_regularSubdiff_iff (φ := distFun Ω) (r := ρ) rfl]
  constructor
  · intro hv
    have hv' : v ∈ regularSubdiff (distFun Ω) x₀ := ⟨ρ, rfl, hv⟩
    have hle1 := norm_le_one_of_mem_regularSubdiff_distFun hv'
    refine ⟨⟨hx₀, fun ε hε ↦ ?_⟩, ?_⟩
    · filter_upwards [nhdsWithin_le_nhds (hv ε hε), self_mem_nhdsWithin] with x h1 h2
      simp only [distFun, EReal.coe_le_coe_iff] at h1
      have : infDist x Ω ≤ ρ := h2
      linarith
    · rw [mem_sphere_zero_iff_norm]
      refine le_antisymm hle1 (not_lt.1 fun hlt ↦ ?_)
      -- `‖v‖ ≥ 1 - 4ε` for every `ε ∈ (0, 1]`
      set ε := min 1 ((1 - ‖v‖) / 8)
      have hε : 0 < ε := lt_min one_pos (by linarith)
      have hε1 : ε ≤ 1 := min_le_left _ _
      have hε2 : ε ≤ (1 - ‖v‖) / 8 := min_le_right _ _
      obtain ⟨ν, hν, hball⟩ := Metric.eventually_nhds_iff.1 (hv ε hε)
      set r := min (min (ε * ρ) 1) (ν / (2 * (ρ + 1)))
      have hr : 0 < r := lt_min (lt_min (mul_pos hε hd) one_pos) (by positivity)
      have hr1 : r ≤ ε * ρ := (min_le_left _ _).trans (min_le_left _ _)
      have hr1' : r ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
      have hr2 : r ≤ ν / (2 * (ρ + 1)) := min_le_right _ _
      have hr2' : r * (2 * (ρ + 1)) ≤ ν := by rwa [le_div_iff₀ (by positivity)] at hr2
      obtain ⟨y, hyΩ, hy⟩ := (infDist_lt_iff hne).1
        (show infDist x₀ Ω < ρ + r ^ 2 by simp only [ρ]; nlinarith)
      rw [dist_eq_norm] at hy
      set D := ‖x₀ - y‖
      have hD : ρ ≤ D := by
        have := infDist_le_dist_of_mem (x := x₀) hyΩ; rwa [dist_eq_norm] at this
      set x := x₀ + r • (y - x₀)
      have hxx : ‖x - x₀‖ = r * D := by
        rw [show x - x₀ = r • (y - x₀) by simp only [x]; abel, norm_smul,
          Real.norm_of_nonneg hr.le, norm_sub_rev]
      have hxy : ‖x - y‖ = (1 - r) * D := by
        rw [show x - y = (1 - r) • (x₀ - y) by simp only [x]; module, norm_smul,
          Real.norm_of_nonneg (by linarith)]
      have hr2le : r ^ 2 ≤ r := by nlinarith
      have hxν : dist x x₀ < ν := by
        rw [dist_eq_norm, hxx]; nlinarith
      have h1 := hball hxν
      simp only [distFun, EReal.coe_le_coe_iff] at h1
      have hdx : infDist x Ω ≤ (1 - r) * D := by
        rw [← hxy, ← dist_eq_norm]; exact infDist_le_dist_of_mem hyΩ
      have hvr : v (x - x₀) = r * v (y - x₀) := by
        rw [show x - x₀ = r • (y - x₀) by simp only [x]; abel, map_smul, smul_eq_mul]
      rw [hvr, hxx] at h1
      -- `q = v (x₀ - y) ≥ ρ - r - ε D`
      have hq : ρ - r - ε * D ≤ -v (y - x₀) := by
        have h2 : r * (ρ - r - ε * D) ≤ r * (-v (y - x₀)) := by nlinarith
        exact le_of_mul_le_mul_left h2 hr
      have hvD : -v (y - x₀) ≤ ‖v‖ * D := by
        rw [← map_neg, neg_sub]
        exact (le_abs_self _).trans (v.le_opNorm _)
      have hDle : D ≤ ρ * (1 + ε) := by nlinarith
      have h3 : ρ * (1 - ε) ≤ (‖v‖ + ε) * D := by nlinarith
      have h4 : (‖v‖ + ε) * D ≤ (‖v‖ + ε) * (ρ * (1 + ε)) :=
        mul_le_mul_of_nonneg_left hDle (by positivity)
      have h5 : 1 - ε ≤ (‖v‖ + ε) * (1 + ε) := by
        have : ρ * (1 - ε) ≤ ρ * ((‖v‖ + ε) * (1 + ε)) := by nlinarith
        exact le_of_mul_le_mul_left this hd
      nlinarith [norm_nonneg v]
  · rintro ⟨hN, hS⟩ ε hε
    rw [mem_sphere_zero_iff_norm] at hS
    have hN' : v ∈ regularSubdiff (distFun (enlargement Ω ρ)) x₀ := by
      rw [regularSubdiff_distFun_of_mem hx₀]
      exact ⟨hN, by rw [mem_closedBall, dist_zero_right, hS]⟩
    rw [mem_regularSubdiff_iff (φ := distFun (enlargement Ω ρ)) (r := 0)
      (distFun_of_mem hx₀)] at hN'
    obtain ⟨ν₂, hν₂, hball⟩ := Metric.mem_nhdsWithin_iff.1 (hN.2 (ε / 2) (half_pos hε))
    filter_upwards [hN' ε hε, ball_mem_nhds x₀ (half_pos hν₂)] with x h1 hxb
    rw [mem_ball, dist_eq_norm] at hxb
    simp only [distFun, EReal.coe_le_coe_iff, zero_add] at h1 ⊢
    by_cases hxΩ : x ∈ enlargement Ω ρ
    · have hxρ : infDist x Ω ≤ ρ := hxΩ
      set σ := ρ - infDist x Ω
      have hσ0 : 0 ≤ σ := by simp only [σ]; linarith
      have hσh : σ ≤ ‖x - x₀‖ := by
        have := infDist_le_infDist_add_dist (x := x₀) (y := x) (s := Ω)
        rw [dist_eq_norm, norm_sub_rev] at this
        simp only [σ, ρ]; linarith
      suffices hs : v (x - x₀) ≤ ε * ‖x - x₀‖ - σ by simp only [σ] at hs; linarith
      have hxball : x ∈ ball x₀ ν₂ := by rw [mem_ball, dist_eq_norm]; linarith
      refine le_of_forall_pos_le_add_mul (c := σ) fun η hη ↦ ?_
      by_cases hη1 : 1 ≤ η
      · have := hball ⟨hxball, hxΩ⟩
        simp only [mem_ofPred_eq] at this
        nlinarith [norm_nonneg (x - x₀)]
      · rw [not_le] at hη1
        obtain ⟨y, hy1, hy2⟩ := v.exists_lt_apply_of_lt_opNorm
          (show 1 - η < ‖v‖ by rw [hS]; linarith)
        obtain ⟨u, hu1, hu2⟩ : ∃ u : E, ‖u‖ ≤ 1 ∧ 1 - η ≤ v u := by
          rcases le_total 0 (v y) with h | h
          · exact ⟨y, hy1.le, by rw [Real.norm_eq_abs, abs_of_nonneg h] at hy2; linarith⟩
          · refine ⟨-y, by rw [norm_neg]; exact hy1.le, ?_⟩
            rw [map_neg]
            rw [Real.norm_eq_abs, abs_of_nonpos h] at hy2
            linarith
        set y' := x + σ • u
        have hy'u : ‖σ • u‖ ≤ σ := by
          rw [norm_smul, Real.norm_of_nonneg hσ0]; nlinarith
        have hy'Ω : y' ∈ enlargement Ω ρ := by
          change infDist y' Ω ≤ ρ
          have := infDist_le_infDist_add_dist (x := y') (y := x) (s := Ω)
          rw [dist_eq_norm, show y' - x = σ • u by simp only [y']; abel] at this
          simp only [σ] at hy'u
          linarith
        have hy'b : ‖y' - x₀‖ ≤ 2 * ‖x - x₀‖ := by
          have := norm_add_le (x - x₀) (σ • u)
          rw [show x - x₀ + σ • u = y' - x₀ by simp only [y']; abel] at this
          linarith
        have hy'ball : y' ∈ ball x₀ ν₂ := by rw [mem_ball, dist_eq_norm]; linarith
        have h2 := hball ⟨hy'ball, hy'Ω⟩
        simp only [mem_ofPred_eq] at h2
        have h3 : v (y' - x₀) = v (x - x₀) + σ * v u := by
          rw [show y' - x₀ = (x - x₀) + σ • u by simp only [y']; abel, map_add, map_smul,
            smul_eq_mul]
        have h4 : ε / 2 * ‖y' - x₀‖ ≤ ε * ‖x - x₀‖ := by nlinarith
        nlinarith
    · have hxρ : ρ < infDist x Ω := lt_of_not_ge hxΩ
      rw [infDist_enlargement hne hd hxρ] at h1
      linarith

section RightSided

variable {φ : E → EReal} {r : ℝ}

/-- The right-sided limiting subdifferential [Mordukhovich 2018, Def. 1.36, (1.53)]: limits of
regular subgradients at points `x →φ x₀` with `φ x ≥ φ x₀`. Empty unless `φ x₀` is finite. -/
def rightSubdiff (φ : E → EReal) (x₀ : E) : Set (StrongDual ℝ E) :=
  {v | ∃ r : ℝ, φ x₀ = r ∧
    v ∈ outerLimit (funNhds φ x₀ ⊓ 𝓟 {x | φ x₀ ≤ φ x}) (regularSubdiff φ)}

theorem mem_rightSubdiff_iff (hr : φ x₀ = r) :
    v ∈ rightSubdiff φ x₀ ↔
      v ∈ outerLimit (funNhds φ x₀ ⊓ 𝓟 {x | φ x₀ ≤ φ x}) (regularSubdiff φ) :=
  ⟨fun ⟨_, _, h⟩ ↦ h, fun h ↦ ⟨r, hr, h⟩⟩

/-- `∂̂φ(x₀) ⊆ ∂≥φ(x₀)` [Mordukhovich 2018, p. 43]. -/
theorem regularSubdiff_subset_rightSubdiff : regularSubdiff φ x₀ ⊆ rightSubdiff φ x₀ :=
  fun v ⟨r, hr, hv⟩ ↦ ⟨r, hr, subset_outerLimit
    (le_inf (pure_le_funNhds φ x₀) (by simp)) _ ⟨r, hr, hv⟩⟩

/-- `∂≥φ(x₀) ⊆ ∂φ(x₀)` [Mordukhovich 2018, p. 43]. -/
theorem rightSubdiff_subset_subdiff : rightSubdiff φ x₀ ⊆ subdiff φ x₀ := by
  rintro v ⟨r, hr, hv⟩
  rw [subdiff_eq_outerLimit hr]
  exact outerLimit_mono_filter inf_le_left _ hv

/-- Prop. 1.37(i) of [Mordukhovich 2018]: at a local minimizer, `∂≥φ(x₀) = ∂φ(x₀)`. -/
theorem rightSubdiff_eq_subdiff_of_isLocalMin (hmin : IsLocalMin φ x₀) (hr : φ x₀ = r) :
    rightSubdiff φ x₀ = subdiff φ x₀ := by
  refine subset_antisymm rightSubdiff_subset_subdiff fun v hv ↦ ⟨r, hr, ?_⟩
  rw [subdiff_eq_outerLimit hr] at hv
  have : funNhds φ x₀ ⊓ 𝓟 {x | φ x₀ ≤ φ x} = funNhds φ x₀ :=
    inf_eq_left.2 (le_principal_iff.2 (inf_le_left (b := comap φ (𝓝 (φ x₀))) hmin))
  rwa [this]

/-- Prop. 1.37(i) of [Mordukhovich 2018]: at a local minimizer, `0 ∈ ∂≥φ(x₀)`. -/
theorem zero_mem_rightSubdiff_of_isLocalMin (hmin : IsLocalMin φ x₀) (hr : φ x₀ = r) :
    (0 : StrongDual ℝ E) ∈ rightSubdiff φ x₀ :=
  regularSubdiff_subset_rightSubdiff (zero_mem_regularSubdiff_of_isLocalMin hmin hr)

end RightSided

section Enlargement

variable [FiniteDimensional ℝ E]

/-- Thm. 1.38, (1.55), of [Mordukhovich 2018]: for `ρ = dist(x₀; Ω) > 0`, right-sided
subgradients of `d_Ω` at `x₀` are unit basic normals to the enlargement `Ω(ρ)`. In particular
`∂≥d_Ω(x₀) ⊆ [N(x₀; Ω(ρ)) ∩ 𝔹] \ {0}`. -/
theorem rightSubdiff_distFun_subset (hne : Ω.Nonempty) (hd : 0 < infDist x₀ Ω) :
    rightSubdiff (distFun Ω) x₀ ⊆ normalCone (enlargement Ω (infDist x₀ Ω)) x₀ ∩ sphere 0 1 := by
  set ρ := infDist x₀ Ω
  have hx₀ : x₀ ∈ enlargement Ω ρ := show infDist x₀ Ω ≤ ρ from le_rfl
  rintro v ⟨r, -, a, u, ha, hu, hmem⟩
  rw [tendsto_inf, tendsto_principal] at ha
  obtain ⟨ha, hright⟩ := ha
  obtain ⟨ha1, -⟩ := tendsto_funNhds_iff.1 ha
  have hright' : ∀ᶠ k in atTop, ρ ≤ infDist (a k) Ω := hright.mono fun k hk ↦ by
    simpa [distFun] using hk
  -- every regular subgradient at `a k` is a unit regular normal to `Ω(ρ)` at a nearby point
  have key : ∀ᶠ k in atTop, ∃ y ∈ enlargement Ω ρ, ‖y - a k‖ ≤ ‖a k - x₀‖ ∧
      u k ∈ regularNormalCone (enlargement Ω ρ) y ∧ ‖u k‖ = 1 := by
    filter_upwards [hright'] with k hk
    have hdk : 0 < infDist (a k) Ω := lt_of_lt_of_le hd hk
    have hLk := regularSubdiff_distFun_eq_of_pos hne hdk ▸ hmem k
    have hLk2 : ‖u k‖ = 1 := mem_sphere_zero_iff_norm.1 hLk.2
    rcases hk.eq_or_lt with heq | hlt
    · refine ⟨a k, show infDist (a k) Ω ≤ ρ from heq.ge, by simp, ?_, hLk2⟩
      rw [show ρ = infDist (a k) Ω from heq]
      exact hLk.1
    · have hcl := isClosed_enlargement Ω ρ
      have hne' : (enlargement Ω ρ).Nonempty := ⟨x₀, hx₀⟩
      obtain ⟨y, hy, hdy⟩ := hcl.exists_infDist_eq_dist hne' (a k)
      have hu' : u k ∈ regularSubdiff (distFun (enlargement Ω ρ)) (a k) := by
        have h1 := hmem k
        rw [regularSubdiff_congr (distFun_eventuallyEq_enlargement hne hd hlt)] at h1
        have := (mem_regularSubdiff_add_iff (hasFDerivAt_const (ρ : ℝ) (a k))).1 h1
        simpa using this
      have hN := mem_regularNormalCone_of_mem_regularSubdiff_distFun hy
        (by rw [hdy, dist_eq_norm]) hu'
      refine ⟨y, hy, ?_, hN.1, hLk2⟩
      rw [norm_sub_rev, ← dist_eq_norm, ← hdy, ← dist_eq_norm]
      exact infDist_le_dist_of_mem hx₀
  have hkey : ∀ k, ∃ y : E, (∃ y ∈ enlargement Ω ρ, ‖y - a k‖ ≤ ‖a k - x₀‖ ∧
      u k ∈ regularNormalCone (enlargement Ω ρ) y ∧ ‖u k‖ = 1) →
      y ∈ enlargement Ω ρ ∧ ‖y - a k‖ ≤ ‖a k - x₀‖ ∧
      u k ∈ regularNormalCone (enlargement Ω ρ) y ∧ ‖u k‖ = 1 := fun k ↦ by
    by_cases h : ∃ y ∈ enlargement Ω ρ, ‖y - a k‖ ≤ ‖a k - x₀‖ ∧
        u k ∈ regularNormalCone (enlargement Ω ρ) y ∧ ‖u k‖ = 1
    · obtain ⟨y, hy⟩ := h; exact ⟨y, fun _ ↦ hy⟩
    · exact ⟨x₀, fun h' ↦ absurd h' h⟩
  choose y hy using hkey
  have hyk : ∀ᶠ k in atTop, y k ∈ enlargement Ω ρ ∧ ‖y k - a k‖ ≤ ‖a k - x₀‖ ∧
      u k ∈ regularNormalCone (enlargement Ω ρ) (y k) ∧ ‖u k‖ = 1 :=
    key.mono fun k hk ↦ hy k hk
  have hylim : Tendsto y atTop (𝓝 x₀) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h2 := (tendsto_iff_norm_sub_tendsto_zero.1 ha1).const_mul 2
    rw [mul_zero] at h2
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ h2
    filter_upwards [hyk] with k hk
    have := norm_sub_le_norm_sub_add_norm_sub (y k) (a k) x₀
    linarith [hk.2.1]
  refine ⟨⟨hx₀, mem_outerLimit_of_eventually y u
    (tendsto_nhdsWithin_iff.2 ⟨hylim, hyk.mono fun k hk ↦ hk.1⟩) hu
    (hyk.mono fun k hk ↦ hk.2.2.1)⟩, ?_⟩
  exact isClosed_sphere.mem_of_tendsto hu (hyk.mono fun k hk ↦ by
    rw [mem_sphere_zero_iff_norm]; exact hk.2.2.2)

/-- Thm. 1.38, (1.56), of [Mordukhovich 2018]: for `ρ = dist(x₀; Ω) > 0`,
`N(x₀; Ω(ρ)) = ⋃_{λ ≥ 0} λ ∂≥d_Ω(x₀)` (with the convention `0 · ∅ = {0}` of the book, i.e. the
cone also contains `0`). -/
theorem mem_normalCone_enlargement_iff (hne : Ω.Nonempty) (hd : 0 < infDist x₀ Ω) :
    v ∈ normalCone (enlargement Ω (infDist x₀ Ω)) x₀ ↔
      v = 0 ∨ ∃ c : ℝ, 0 < c ∧ ∃ u ∈ rightSubdiff (distFun Ω) x₀, v = c • u := by
  set ρ := infDist x₀ Ω
  have hx₀ : x₀ ∈ enlargement Ω ρ := show infDist x₀ Ω ≤ ρ from le_rfl
  constructor
  · intro hv
    by_cases hv0 : v = 0
    · exact Or.inl hv0
    right
    obtain ⟨-, a, u, ha, hu, hmem⟩ := hv
    have ha' := tendsto_nhdsWithin_iff.1 ha
    have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
    have hune : ∀ᶠ k in atTop, u k ≠ 0 := by
      filter_upwards [((continuous_norm.tendsto v).comp hu).eventually (lt_mem_nhds hvpos)]
        with k hk h0
      simp [h0] at hk
    -- at such points `d(a k) = ρ`
    have hdk : ∀ᶠ k in atTop, infDist (a k) Ω = ρ := by
      filter_upwards [hune, ha'.2] with k hk hkΩ
      refine le_antisymm hkΩ (not_lt.1 fun hlt ↦ hk ?_)
      have hint : a k ∈ interior (enlargement Ω ρ) := by
        rw [mem_interior_iff_mem_nhds]
        filter_upwards [(continuous_infDist_pt Ω).continuousAt.eventually (gt_mem_nhds hlt)]
          with y hy using hy.le
      have := hmem k
      rwa [regularNormalCone_of_mem_interior hint, mem_singleton_iff] at this
    refine ⟨‖v‖, hvpos, ‖v‖⁻¹ • v, ⟨ρ, rfl, ?_⟩, by
      rw [smul_smul, mul_inv_cancel₀ hvpos.ne', one_smul]⟩
    refine mem_outerLimit_of_eventually a (fun k ↦ ‖u k‖⁻¹ • u k) ?_ ?_ ?_
    · rw [tendsto_inf, tendsto_principal]
      refine ⟨tendsto_funNhds_iff.2 ⟨ha'.1, tendsto_const_nhds.congr' ?_⟩, ?_⟩
      · filter_upwards [hdk] with k hk
        simp [distFun, hk, ρ]
      · filter_upwards [hdk] with k hk
        simp [distFun, hk, ρ]
    · exact (((continuous_norm.tendsto v).comp hu).inv₀ hvpos.ne').smul hu
    · filter_upwards [hdk, hune] with k hk hk0
      rw [regularSubdiff_distFun_eq_of_pos hne (hk ▸ hd), hk]
      refine ⟨smul_mem_regularNormalCone (hmem k) (by positivity), ?_⟩
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 hk0)]
  · rintro (rfl | ⟨c, hc, u, hu, rfl⟩)
    · exact zero_mem_normalCone hx₀
    · exact smul_mem_normalCone (rightSubdiff_distFun_subset hne hd hu).1 hc.le

end Enlargement

end VariationalAnalysis
