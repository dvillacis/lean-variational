/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import Mathlib.Topology.MetricSpace.Lipschitz
import VariationalAnalysis.Subdifferential.Limiting

/-!
# Subgradients of locally Lipschitzian functions

## Main results

* `subdiff_congr`, `singularSubdiff_congr`: subdifferentials only depend on the function near
  the point.
* `norm_comp_inl_le_of_mem_normalCone_epi`: (1.28) of [Mordukhovich 2018]: for `f` Lipschitz
  around `x₀` with modulus `L`, normals `(v, -μ)` to the epigraph satisfy `‖v‖ ≤ L μ`.
* `singularSubdiff_eq_zero_of_lipschitz`, `norm_le_of_mem_subdiff_of_lipschitz`,
  `subdiff_nonempty_of_lipschitz`: Thm. 1.22 of [Mordukhovich 2018], "only if" part: a function
  Lipschitz around `x₀` has `∂^∞f(x₀) = {0}`, and `∂f(x₀)` is nonempty and contained in the ball
  of radius `L`. (The converse uses the coderivative criterion of Ch. 3.)
* `singularSubdiff_add_of_lipschitz`: Prop. 1.29 of [Mordukhovich 2018] (singular subgradients
  under Lipschitzian additions): `∂^∞(φ + ψ)(x₀) = ∂^∞φ(x₀)`.
-/

open Filter Topology Set Metric
open scoped NNReal

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {x₀ : E} {v : StrongDual ℝ E}

section Locality

variable {φ₁ φ₂ : E → EReal}

omit [NormedSpace ℝ E] in
theorem epi_eventuallyEq (h : φ₁ =ᶠ[𝓝 x₀] φ₂) (r : ℝ) :
    φ₁.Epi univ =ᶠ[𝓝 ((x₀, r) : E × ℝ)] φ₂.Epi univ := by
  filter_upwards [(continuous_fst.tendsto ((x₀, r) : E × ℝ)).eventually h] with p hp
  change (p ∈ φ₁.Epi univ) = (p ∈ φ₂.Epi univ)
  simp [Function.Epi, hp]

/-- Basic subgradients only depend on the function near the point. -/
theorem subdiff_congr (h : φ₁ =ᶠ[𝓝 x₀] φ₂) : subdiff φ₁ x₀ = subdiff φ₂ x₀ := by
  ext v
  constructor
  · rintro ⟨r, hr, hv⟩
    exact ⟨r, h.self_of_nhds ▸ hr, normalCone_congr (epi_eventuallyEq h r) ▸ hv⟩
  · rintro ⟨r, hr, hv⟩
    exact ⟨r, h.self_of_nhds.symm ▸ hr, normalCone_congr (epi_eventuallyEq h r).symm ▸ hv⟩

/-- Singular subgradients only depend on the function near the point. -/
theorem singularSubdiff_congr (h : φ₁ =ᶠ[𝓝 x₀] φ₂) :
    singularSubdiff φ₁ x₀ = singularSubdiff φ₂ x₀ := by
  ext v
  constructor
  · rintro ⟨r, hr, hv⟩
    exact ⟨r, h.self_of_nhds ▸ hr, normalCone_congr (epi_eventuallyEq h r) ▸ hv⟩
  · rintro ⟨r, hr, hv⟩
    exact ⟨r, h.self_of_nhds.symm ▸ hr, normalCone_congr (epi_eventuallyEq h r).symm ▸ hv⟩

end Locality

section Lipschitz

variable {f : E → ℝ} {U : Set E} {L : ℝ≥0}

/-- Regular normals `(v, -μ)` to the epigraph of a function Lipschitz near the base point satisfy
`‖v‖ ≤ L μ`. -/
theorem norm_comp_inl_le_of_mem_regularNormalCone_epi {p : E × ℝ} (hU : U ∈ 𝓝 p.1)
    (hL : LipschitzOnWith L f U) {ℓ : StrongDual ℝ (E × ℝ)}
    (hℓ : ℓ ∈ regularNormalCone ((fun x ↦ (f x : EReal)).Epi univ) p) :
    ‖ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ)‖ ≤ L * -ℓ (0, 1) := by
  have hμ : 0 ≤ -ℓ (0, 1) := by
    linarith [apply_zero_one_nonpos_of_mem_regularNormalCone_epi hℓ]
  obtain ⟨x, α⟩ := p
  have hxα : f x ≤ α := EReal.coe_le_coe_iff.1 hℓ.1.2
  have hxU : x ∈ U := mem_of_mem_nhds hU
  have hdir : ∀ d : E, ℓ (d, 0) ≤ L * -ℓ (0, 1) * ‖d‖ := by
    intro d
    have hray : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        (x, α) + t • (d, (L : ℝ) * ‖d‖) ∈ (fun x ↦ (f x : EReal)).Epi univ := by
      have hT : Tendsto (fun t : ℝ ↦ x + t • d) (𝓝 0) (𝓝 (x + (0 : ℝ) • d)) :=
        ((continuous_id.smul continuous_const).const_add x).tendsto 0
      rw [zero_smul, add_zero] at hT
      filter_upwards [nhdsWithin_le_nhds (hT hU), self_mem_nhdsWithin] with t ht ht0
      refine ⟨mem_univ _, ?_⟩
      have hlip := hL.dist_le_mul (x + t • d) ht x hxU
      rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg
        (le_of_lt ht0)] at hlip
      simp only [Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, EReal.coe_le_coe_iff]
      have := (le_abs_self (f (x + t • d) - f x)).trans hlip
      nlinarith [norm_nonneg d]
    refine le_of_forall_pos_le_add_mul (c := ‖((d, (L : ℝ) * ‖d‖) : E × ℝ)‖) fun ε hε ↦ ?_
    have h := le_of_eventually_ray (hℓ.2 ε hε) hray
    have hsplit : ℓ (d, (L : ℝ) * ‖d‖) = ℓ (d, 0) + (L : ℝ) * ‖d‖ * ℓ (0, 1) := by
      have : ((d, (L : ℝ) * ‖d‖) : E × ℝ) = (d, 0) + ((L : ℝ) * ‖d‖) • ((0 : E), (1 : ℝ)) := by
        ext <;> simp
      rw [this, map_add, map_smul, smul_eq_mul]
    rw [hsplit] at h
    nlinarith
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg L.coe_nonneg hμ) fun d ↦ ?_
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.inl_apply,
    Real.norm_eq_abs]
  refine abs_le.2 ⟨?_, hdir d⟩
  have := hdir (-d)
  rw [show ((-d, 0) : E × ℝ) = -(d, 0) by simp, map_neg, norm_neg] at this
  linarith

/-- (1.28) of [Mordukhovich 2018]: if `f` is Lipschitz around `x₀` with modulus `L`, then every
normal `(v, -μ)` to the epigraph at `(x₀, f x₀)` satisfies `‖v‖ ≤ L μ`. -/
theorem norm_comp_inl_le_of_mem_normalCone_epi (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U)
    {ℓ : StrongDual ℝ (E × ℝ)} {α : ℝ}
    (hℓ : ℓ ∈ normalCone ((fun x ↦ (f x : EReal)).Epi univ) (x₀, α)) :
    ‖ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ)‖ ≤ L * -ℓ (0, 1) := by
  obtain ⟨-, p, w, hp, hw, hmem⟩ := hℓ
  have hp1 : Tendsto (fun k ↦ (p k).1) atTop (𝓝 x₀) :=
    (continuous_fst.tendsto _).comp (tendsto_nhdsWithin_iff.1 hp).1
  have hev : ∀ᶠ k in atTop, U ∈ 𝓝 (p k).1 :=
    hp1.eventually (eventually_mem_nhds_iff.2 hU)
  refine le_of_tendsto_of_tendsto ((continuous_norm.tendsto _).comp (tendsto_comp_inl hw))
    ((tendsto_dual_apply hw tendsto_const_nhds).neg.const_mul (L : ℝ)) ?_
  filter_upwards [hev] with k hk
  exact norm_comp_inl_le_of_mem_regularNormalCone_epi hk hL (hmem k)

/-- Thm. 1.22 of [Mordukhovich 2018]: a function Lipschitz around `x₀` has trivial singular
subdifferential. -/
theorem singularSubdiff_eq_zero_of_lipschitz (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U) :
    singularSubdiff (fun x ↦ (f x : EReal)) x₀ = {0} := by
  refine subset_antisymm (fun v hv ↦ ?_) ?_
  · rw [mem_singularSubdiff_iff (φ := fun x ↦ (f x : EReal)) (x₀ := x₀) (r := f x₀) rfl] at hv
    have := norm_comp_inl_le_of_mem_normalCone_epi hU hL hv
    simp only [ContinuousLinearMap.coprod_comp_inl, ContinuousLinearMap.coprod_apply,
      map_zero, zero_apply, add_zero, neg_zero, mul_zero] at this
    exact mem_singleton_iff.2 (norm_le_zero_iff.1 this)
  · rintro _ rfl
    exact zero_mem_singularSubdiff (φ := fun x ↦ (f x : EReal)) (x₀ := x₀) (r := f x₀) rfl

/-- Thm. 1.22, (1.27), of [Mordukhovich 2018]: basic subgradients of a function Lipschitz
around `x₀` with modulus `L` have norm at most `L`. -/
theorem norm_le_of_mem_subdiff_of_lipschitz (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U)
    (hv : v ∈ subdiff (fun x ↦ (f x : EReal)) x₀) : ‖v‖ ≤ L := by
  rw [mem_subdiff_iff (φ := fun x ↦ (f x : EReal)) (x₀ := x₀) (r := f x₀) rfl] at hv
  have := norm_comp_inl_le_of_mem_normalCone_epi hU hL hv
  simpa using this

omit [NormedSpace ℝ E] in
/-- The epigraph of a function continuous on a neighborhood of `x₀` is locally closed around
`(x₀, α)`. -/
theorem locallyClosed_epi_of_continuousOn (hU : U ∈ 𝓝 x₀) (hf : ContinuousOn f U) (α : ℝ) :
    ∃ ρ > 0, IsClosed ((fun x ↦ (f x : EReal)).Epi univ ∩ closedBall ((x₀, α) : E × ℝ) ρ) := by
  obtain ⟨ρ, hρ, hsub⟩ := nhds_basis_closedBall.mem_iff.1 hU
  refine ⟨ρ, hρ, isClosed_of_closure_subset fun q hq ↦ ?_⟩
  obtain ⟨q', hq', hlim⟩ := mem_closure_iff_seq_limit.1 hq
  have hqb : q ∈ closedBall ((x₀, α) : E × ℝ) ρ :=
    isClosed_closedBall.mem_of_tendsto hlim (Eventually.of_forall fun k ↦ (hq' k).2)
  have hfst : ∀ {p : E × ℝ}, p ∈ closedBall ((x₀, α) : E × ℝ) ρ → p.1 ∈ U := fun hp ↦
    hsub (by
      rw [mem_closedBall, dist_eq_norm] at hp ⊢
      exact (norm_fst_le _).trans hp)
  refine ⟨⟨mem_univ _, ?_⟩, hqb⟩
  have h1 : Tendsto (fun k ↦ (q' k).1) atTop (𝓝[U] q.1) :=
    tendsto_nhdsWithin_iff.2 ⟨(continuous_fst.tendsto _).comp hlim,
      Eventually.of_forall fun k ↦ hfst (hq' k).2⟩
  have h2 := ((hf q.1 (hfst hqb)).tendsto.comp h1)
  have h3 : Tendsto (fun k ↦ (q' k).2) atTop (𝓝 q.2) := (continuous_snd.tendsto _).comp hlim
  exact EReal.coe_le_coe_iff.2 (le_of_tendsto_of_tendsto h2 h3
    (Eventually.of_forall fun k ↦ EReal.coe_le_coe_iff.1 (hq' k).1.2))

/-- Thm. 1.22 of [Mordukhovich 2018]: a function Lipschitz around `x₀` has a nonempty basic
subdifferential (finite dimensions). -/
theorem subdiff_nonempty_of_lipschitz [FiniteDimensional ℝ E] (hU : U ∈ 𝓝 x₀)
    (hL : LipschitzOnWith L f U) : (subdiff (fun x ↦ (f x : EReal)) x₀).Nonempty := by
  set epi := (fun x ↦ (f x : EReal)).Epi univ
  have hmem₀ : ((x₀, f x₀) : E × ℝ) ∈ epi := ⟨mem_univ _, le_rfl⟩
  have hfr : ((x₀, f x₀) : E × ℝ) ∈ frontier epi := by
    refine ⟨subset_closure hmem₀, fun hint ↦ ?_⟩
    have hT : Tendsto (fun t : ℝ ↦ ((x₀, f x₀ - t) : E × ℝ)) (𝓝[>] 0) (𝓝 (x₀, f x₀)) := by
      have : Tendsto (fun t : ℝ ↦ ((x₀, f x₀ - t) : E × ℝ)) (𝓝 0) (𝓝 (x₀, f x₀ - 0)) :=
        (tendsto_const_nhds.prodMk_nhds (tendsto_const_nhds.sub tendsto_id))
      simpa using this.mono_left nhdsWithin_le_nhds
    obtain ⟨t, ht, ht0⟩ :=
      ((hT.eventually (mem_interior_iff_mem_nhds.1 hint)).and self_mem_nhdsWithin).exists
    have : (f x₀ : EReal) ≤ ((f x₀ - t : ℝ) : EReal) := ht.2
    rw [EReal.coe_le_coe_iff] at this
    linarith [show (0 : ℝ) < t from ht0]
  obtain ⟨ℓ, hℓ, hℓ0⟩ := (exists_ne_zero_mem_normalCone_iff hmem₀
    (locallyClosed_epi_of_continuousOn hU hL.continuousOn (f x₀))).2 hfr
  have hbound := norm_comp_inl_le_of_mem_normalCone_epi hU hL hℓ
  have hμ : 0 ≤ -ℓ (0, 1) := by linarith [apply_zero_one_nonpos_of_mem_normalCone_epi hℓ]
  have hμpos : 0 < -ℓ (0, 1) := by
    refine lt_of_le_of_ne hμ fun h ↦ hℓ0 ?_
    rw [← h, mul_zero] at hbound
    have hinl : ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ) = 0 := norm_le_zero_iff.1 hbound
    have hinr : ℓ.comp (ContinuousLinearMap.inr ℝ E ℝ) = 0 := by
      ext; simp; linarith
    rw [← ContinuousLinearMap.coprod_comp_inl_inr ℓ, hinl, hinr]
    ext <;> simp
  set μ := -ℓ (0, 1)
  have hg : μ⁻¹ • ℓ ∈ normalCone epi (x₀, f x₀) := smul_mem_normalCone hℓ (inv_nonneg.2 hμ)
  have hne : ℓ (0, 1) ≠ 0 := fun h ↦ by simp [μ, h] at hμpos
  have h1 : (μ⁻¹ • ℓ) (0, 1) = -1 := by
    simp only [smul_apply, smul_eq_mul, μ]
    rw [inv_neg, neg_mul, inv_mul_cancel₀ hne]
  refine ⟨(μ⁻¹ • ℓ).comp (ContinuousLinearMap.inl ℝ E ℝ), ?_⟩
  rw [mem_subdiff_iff (φ := fun x ↦ (f x : EReal)) (x₀ := x₀) (r := f x₀) rfl,
    ← eq_coprod_neg_one _ h1]
  exact hg

end Lipschitz

section LipschitzAddition

variable {φ : E → EReal} {r : ℝ}

/-- `y + c ≤ A ↔ y ≤ A - c` in `EReal` for real `c`, `A`. -/
theorem add_coe_le_coe_iff {A c : ℝ} {y : EReal} :
    y + c ≤ (A : EReal) ↔ y ≤ ((A - c : ℝ) : EReal) := by
  induction y with
  | bot => simp
  | top => simp only [EReal.top_add_coe, top_le_iff, EReal.coe_ne_top]
  | coe y =>
    rw [← EReal.coe_add, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith

/-- Regular normals to the epigraph of `φ + g` are `|ℓ (0, 1)| L`-normals to the epigraph of `φ`
at the corresponding point, when `g` is `L`-Lipschitz. -/
theorem mem_epsNormalCone_epi_of_add_lipschitz {g : E → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    {x : E} {α : ℝ} {ℓ : StrongDual ℝ (E × ℝ)}
    (hℓ : ℓ ∈ regularNormalCone ((fun y ↦ φ y + g y).Epi univ) (x, α)) :
    ℓ ∈ epsNormalCone (|ℓ (0, 1)| * L) (φ.Epi univ) (x, α - g x) := by
  refine ⟨⟨mem_univ _, add_coe_le_coe_iff.1 hℓ.1.2⟩, fun ε hε ↦ ?_⟩
  set T : E × ℝ → E × ℝ := fun q ↦ (q.1, q.2 + g q.1)
  have hTc : Continuous T := continuous_fst.prodMk (continuous_snd.add (hg.continuous.comp
    continuous_fst))
  have hT : Tendsto T (𝓝[φ.Epi univ] (x, α - g x)) (𝓝[(fun y ↦ φ y + g y).Epi univ] (x, α)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun q hq ↦ ?_⟩
    · have := (hTc.tendsto (x, α - g x)).mono_left (nhdsWithin_le_nhds (s := φ.Epi univ))
      simpa [T] using this
    · refine ⟨mem_univ _, ?_⟩
      show φ q.1 + g q.1 ≤ ((q.2 + g q.1 : ℝ) : EReal)
      rw [add_coe_le_coe_iff, add_sub_cancel_right]
      exact hq.2
  have hδ : 0 < ε / (1 + L) := div_pos hε (by positivity)
  filter_upwards [hT.eventually (hℓ.2 _ hδ)] with q hq
  obtain ⟨y, β⟩ := q
  simp only [T] at hq
  have hsplit : ((y, β) : E × ℝ) - (x, α - g x) =
      ((y, β + g y) - (x, α)) - (g y - g x) • ((0 : E), (1 : ℝ)) := by
    ext <;> simp; ring
  have hlip : |g y - g x| ≤ L * ‖y - x‖ := by
    rw [← Real.dist_eq, ← dist_eq_norm]; exact hg.dist_le_mul y x
  have hnorm : ‖((y, β + g y) : E × ℝ) - (x, α)‖ ≤ (1 + L) * ‖((y, β) : E × ℝ) - (x, α - g x)‖ := by
    simp only [Prod.mk_sub_mk, Prod.norm_mk, Real.norm_eq_abs]
    have h1 : |β + g y - α| ≤ |β - (α - g x)| + |g y - g x| := by
      rw [show β + g y - α = (β - (α - g x)) + (g y - g x) by ring]; exact abs_add_le _ _
    have hm1 := le_max_left ‖y - x‖ |β - (α - g x)|
    have hm2 := le_max_right ‖y - x‖ |β - (α - g x)|
    have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
    have hmax0 : 0 ≤ max ‖y - x‖ |β - (α - g x)| := le_trans (norm_nonneg _) hm1
    have hLm : (L : ℝ) * ‖y - x‖ ≤ L * max ‖y - x‖ |β - (α - g x)| :=
      mul_le_mul_of_nonneg_left hm1 hL0
    refine max_le (by nlinarith) ?_
    nlinarith
  have hc : -(g y - g x) * ℓ (0, 1) ≤ |ℓ (0, 1)| * L * ‖((y, β) : E × ℝ) - (x, α - g x)‖ := by
    have h1 : -(g y - g x) * ℓ (0, 1) ≤ |g y - g x| * |ℓ (0, 1)| := by
      have := le_abs_self (-(g y - g x) * ℓ (0, 1))
      rwa [abs_mul, abs_neg] at this
    have h2 : ‖y - x‖ ≤ ‖((y, β) : E × ℝ) - (x, α - g x)‖ := by
      simp only [Prod.mk_sub_mk]; exact norm_fst_le ((y - x, β - (α - g x)) : E × ℝ)
    calc -(g y - g x) * ℓ (0, 1) ≤ |g y - g x| * |ℓ (0, 1)| := h1
      _ ≤ L * ‖y - x‖ * |ℓ (0, 1)| := by gcongr
      _ ≤ L * ‖((y, β) : E × ℝ) - (x, α - g x)‖ * |ℓ (0, 1)| := by gcongr
      _ = |ℓ (0, 1)| * L * ‖((y, β) : E × ℝ) - (x, α - g x)‖ := by ring
  have hl : ℓ (((y, β) : E × ℝ) - (x, α - g x)) =
      ℓ (((y, β + g y) : E × ℝ) - (x, α)) - (g y - g x) * ℓ (0, 1) := by
    rw [hsplit, map_sub, map_smul, smul_eq_mul]
  have hq' : ℓ (((y, β + g y) : E × ℝ) - (x, α)) ≤
      ε * ‖((y, β) : E × ℝ) - (x, α - g x)‖ := by
    calc ℓ (((y, β + g y) : E × ℝ) - (x, α)) ≤ ε / (1 + L) * ‖((y, β + g y) : E × ℝ) - (x, α)‖ :=
          hq
      _ ≤ ε / (1 + L) * ((1 + L) * ‖((y, β) : E × ℝ) - (x, α - g x)‖) := by gcongr
      _ = ε * ‖((y, β) : E × ℝ) - (x, α - g x)‖ := by field_simp
  rw [hl, add_mul]
  linarith

/-- Prop. 1.29 of [Mordukhovich 2018], inclusion `⊆`, for a globally Lipschitz addition. -/
theorem singularSubdiff_add_subset_of_lipschitzWith [FiniteDimensional ℝ E] {g : E → ℝ}
    {L : ℝ≥0} (hg : LipschitzWith L g) (hr : φ x₀ = r)
    (hloc : ∃ ρ > 0, IsClosed (φ.Epi univ ∩ closedBall ((x₀, r) : E × ℝ) ρ)) :
    singularSubdiff (fun x ↦ φ x + g x) x₀ ⊆ singularSubdiff φ x₀ := by
  intro v hv
  have hr' : (fun x ↦ φ x + g x) x₀ = ((r + g x₀ : ℝ) : EReal) := by simp [hr]
  rw [mem_singularSubdiff_iff (φ := fun x ↦ φ x + g x) (x₀ := x₀) hr'] at hv
  rw [mem_singularSubdiff_iff hr]
  obtain ⟨-, q, ℓ, hq, hℓ, hmem⟩ := hv
  have hq' := tendsto_nhdsWithin_iff.1 hq
  have hq1 : Tendsto (fun k ↦ (q k).1) atTop (𝓝 x₀) := (continuous_fst.tendsto _).comp hq'.1
  have hq2 : Tendsto (fun k ↦ (q k).2) atTop (𝓝 (r + g x₀)) := (continuous_snd.tendsto _).comp hq'.1
  have hmem₀ : ((x₀, r) : E × ℝ) ∈ φ.Epi univ := ⟨mem_univ _, hr.le⟩
  rw [normalCone_eq_outerLimit_epsNormalCone hmem₀ hloc]
  refine ⟨fun k ↦ (((q k).1, (q k).2 - g (q k).1), |ℓ k (0, 1)| * L), ℓ, ?_, hℓ, fun k ↦ ?_⟩
  · have hA : Tendsto (fun k ↦ ((q k).1, (q k).2 - g (q k).1)) atTop
        (𝓝[φ.Epi univ] ((x₀, r) : E × ℝ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨hq1.prodMk_nhds ?_, Eventually.of_forall fun k ↦
        ⟨mem_univ _, add_coe_le_coe_iff.1 (hmem k).1.2⟩⟩
      simpa using hq2.sub ((hg.continuous.tendsto _).comp hq1)
    have hB : Tendsto (fun k ↦ |ℓ k (0, 1)| * L) atTop (𝓝[≥] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k ↦
        mem_Ici.2 (mul_nonneg (abs_nonneg _) L.coe_nonneg)⟩
      have := ((continuous_abs.tendsto _).comp (tendsto_dual_apply hℓ
        (tendsto_const_nhds (x := ((0 : E), (1 : ℝ)))))).mul_const (L : ℝ)
      simpa using this
    exact hA.prodMk hB
  · exact mem_epsNormalCone_epi_of_add_lipschitz hg (hmem k)

omit [NormedSpace ℝ E] in
/-- The epigraph of `φ + g` is locally closed if that of `φ` is and `g` is Lipschitz. -/
theorem locallyClosed_epi_add {g : E → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    (hloc : ∃ ρ > 0, IsClosed (φ.Epi univ ∩ closedBall ((x₀, r) : E × ℝ) ρ)) :
    ∃ ρ > 0, IsClosed ((fun x ↦ φ x + g x).Epi univ ∩
      closedBall ((x₀, r + g x₀) : E × ℝ) ρ) := by
  obtain ⟨ρ, hρ, hcl⟩ := hloc
  refine ⟨ρ / (1 + L), by positivity, isClosed_of_closure_subset fun q hq ↦ ?_⟩
  obtain ⟨q', hq', hlim⟩ := mem_closure_iff_seq_limit.1 hq
  set S : E × ℝ → E × ℝ := fun p ↦ (p.1, p.2 - g p.1)
  have hSc : Continuous S := continuous_fst.prodMk (continuous_snd.sub (hg.continuous.comp
    continuous_fst))
  have hqb : q ∈ closedBall ((x₀, r + g x₀) : E × ℝ) (ρ / (1 + L)) :=
    isClosed_closedBall.mem_of_tendsto hlim (Eventually.of_forall fun k ↦ (hq' k).2)
  have hS : ∀ p ∈ closedBall ((x₀, r + g x₀) : E × ℝ) (ρ / (1 + L)),
      S p ∈ closedBall ((x₀, r) : E × ℝ) ρ := by
    rintro ⟨y, β⟩ hp
    rw [mem_closedBall, dist_eq_norm, Prod.mk_sub_mk, Prod.norm_mk, max_le_iff] at hp
    rw [mem_closedBall, dist_eq_norm]
    simp only [S, Prod.mk_sub_mk, Prod.norm_mk, max_le_iff, Real.norm_eq_abs] at hp ⊢
    have hlip : |g y - g x₀| ≤ L * ‖y - x₀‖ := by
      rw [← Real.dist_eq, ← dist_eq_norm]; exact hg.dist_le_mul y x₀
    have hρ' : ρ / (1 + L) * (1 + L) = ρ := div_mul_cancel₀ _ (by positivity)
    constructor
    · nlinarith [L.coe_nonneg, norm_nonneg (y - x₀)]
    · have : |β - g y - r| ≤ |β - (r + g x₀)| + |g y - g x₀| := by
        rw [show β - g y - r = (β - (r + g x₀)) - (g y - g x₀) by ring]; exact abs_sub _ _
      nlinarith [L.coe_nonneg, norm_nonneg (y - x₀)]
  have hlimS : S q ∈ φ.Epi univ ∩ closedBall ((x₀, r) : E × ℝ) ρ :=
    hcl.mem_of_tendsto ((hSc.tendsto q).comp hlim) (Eventually.of_forall fun k ↦
      ⟨⟨mem_univ _, add_coe_le_coe_iff.1 (hq' k).1.2⟩, hS _ (hq' k).2⟩)
  refine ⟨⟨mem_univ _, ?_⟩, hqb⟩
  rw [add_coe_le_coe_iff]
  exact hlimS.1.2

/-- Prop. 1.29 of [Mordukhovich 2018] (singular subgradients under Lipschitzian additions): if
the epigraph of `φ` is locally closed around `(x₀, φ x₀)` and `ψ` is Lipschitz around `x₀`,
then `∂^∞(φ + ψ)(x₀) = ∂^∞φ(x₀)` (finite dimensions). -/
theorem singularSubdiff_add_of_lipschitz [FiniteDimensional ℝ E] {ψ : E → ℝ} {U : Set E}
    {L : ℝ≥0} (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L ψ U) (hr : φ x₀ = r)
    (hloc : ∃ ρ > 0, IsClosed (φ.Epi univ ∩ closedBall ((x₀, r) : E × ℝ) ρ)) :
    singularSubdiff (fun x ↦ φ x + ψ x) x₀ = singularSubdiff φ x₀ := by
  obtain ⟨g, hg, hgψ⟩ := hL.extend_real
  have heq : (fun x ↦ φ x + ψ x) =ᶠ[𝓝 x₀] fun x ↦ φ x + g x :=
    eventually_of_mem hU fun x hx ↦ by simp [hgψ hx]
  rw [singularSubdiff_congr heq]
  refine subset_antisymm (singularSubdiff_add_subset_of_lipschitzWith hg hr hloc) ?_
  have hback : (fun x ↦ (φ x + g x) + ((-g) x : ℝ)) = φ := by
    funext x; simpa using add_coe_add_coe_neg (φ x) (g x)
  have hr' : (fun x ↦ φ x + g x) x₀ = ((r + g x₀ : ℝ) : EReal) := by simp [hr]
  have := singularSubdiff_add_subset_of_lipschitzWith (φ := fun x ↦ φ x + g x) (g := -g)
    hg.neg hr' (locallyClosed_epi_add hg hloc)
  rwa [hback] at this

end LipschitzAddition

end VariationalAnalysis
