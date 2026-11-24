/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Topology.Semicontinuity.Basic
import VariationalAnalysis.Coderivative.Basic
import VariationalAnalysis.Subdifferential.Lipschitz

/-!
# Subgradients and coderivatives

## Main results

* `subdiff_eq_coderiv_one`: Thm. 1.23, (1.30), of [Mordukhovich 2018]: for `f` lower
  semicontinuous around `x₀`, `∂f(x₀) = D*f(x₀)(1)`. The inclusion `⊆` holds for every
  real-valued `f` (`subdiff_subset_coderiv_one`).
* `singularSubdiff_subset_coderiv_zero`: Thm. 1.23, (1.31): for `f` continuous around `x₀`,
  `∂^∞f(x₀) ⊆ D*f(x₀)(0)`.
* `subdiff_comp_subset_coderiv`, `subdiff_comp_eq_coderiv`: Thm. 1.32 of [Mordukhovich 2018]
  (coderivative scalarization): `∂⟨v, f⟩(x₀) ⊆ D*f(x₀)(v)` for `f` continuous at `x₀`, with
  equality for `f` Lipschitz around `x₀` (finite dimensions).
-/

open Filter Topology Set Metric
open scoped NNReal

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {x₀ : E}

section RealValued

variable {f : E → ℝ}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem graph_subset_epi :
    graph (fun x ↦ ({f x} : Set ℝ)) ⊆ (fun x ↦ (f x : EReal)).Epi univ := by
  rintro ⟨x, y⟩ h
  have : y = f x := h
  exact ⟨mem_univ _, by rw [this]⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem mem_graph_fun_iff {p : E × ℝ} : p ∈ graph (fun x ↦ ({f x} : Set ℝ)) ↔ p.2 = f p.1 :=
  Iff.rfl

/-- At a point where `f` is lower semicontinuous, a regular normal `(w, -1)` to the graph is a
regular normal to the epigraph [Mordukhovich 2018, Thm. 1.23, Step 2]. -/
theorem coprod_neg_one_mem_regularNormalCone_epi_of_graph {x : E}
    (hf : LowerSemicontinuousAt f x) {w : StrongDual ℝ E}
    (hw : w.coprod (-1) ∈ regularNormalCone (graph fun x ↦ ({f x} : Set ℝ)) (x, f x)) :
    w.coprod (-1) ∈ regularNormalCone ((fun x ↦ (f x : EReal)).Epi univ) (x, f x) := by
  refine ⟨⟨mem_univ _, le_rfl⟩, fun ε hε ↦ ?_⟩
  set epi := (fun x ↦ (f x : EReal)).Epi univ
  set ε' := min (ε / 2) (1 / 2)
  have hε' : 0 < ε' := lt_min (half_pos hε) (by norm_num)
  have hε'1 : ε' ≤ ε / 2 := min_le_left _ _
  have hε'2 : ε' ≤ 1 / 2 := min_le_right _ _
  have h1 : Tendsto Prod.fst (𝓝[epi] (x, f x)) (𝓝 x) :=
    (continuous_fst.tendsto _).mono_left nhdsWithin_le_nhds
  have h3 : Tendsto Prod.snd (𝓝[epi] (x, f x)) (𝓝 (f x)) :=
    (continuous_snd.tendsto _).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun p : E × ℝ ↦ f p.1) (𝓝[epi] (x, f x)) (𝓝 (f x)) := by
    rw [tendsto_order]
    refine ⟨fun a ha ↦ h1.eventually (hf a ha), fun a ha ↦ ?_⟩
    filter_upwards [h3.eventually (gt_mem_nhds ha), self_mem_nhdsWithin] with p hp hpE
    exact lt_of_le_of_lt (EReal.coe_le_coe_iff.1 hpE.2) hp
  have hT : Tendsto (fun p : E × ℝ ↦ (p.1, f p.1)) (𝓝[epi] (x, f x))
      (𝓝[graph fun x ↦ ({f x} : Set ℝ)] (x, f x)) :=
    tendsto_nhdsWithin_iff.2 ⟨h1.prodMk_nhds h2,
      Eventually.of_forall fun p ↦ mem_singleton _⟩
  filter_upwards [hT.eventually (hw.2 ε' hε'), self_mem_nhdsWithin] with p hp hpE
  obtain ⟨z, α⟩ := p
  have hb : f z ≤ α := EReal.coe_le_coe_iff.1 hpE.2
  simp only [Prod.mk_sub_mk, ContinuousLinearMap.coprod_apply, neg_apply,
    Prod.norm_mk, Real.norm_eq_abs] at hp ⊢
  change w (z - x) + -(f z - f x) ≤ ε' * max ‖z - x‖ |f z - f x| at hp
  change w (z - x) + -(α - f x) ≤ ε * max ‖z - x‖ |α - f x|
  have hm1 := le_max_left ‖z - x‖ |α - f x|
  have hm2 := le_max_right ‖z - x‖ |α - f x|
  have hM0 : 0 ≤ max ‖z - x‖ |α - f x| := le_trans (norm_nonneg _) hm1
  rcases le_or_gt 0 (f z - f x) with hb0 | hb0
  · have hmb : max ‖z - x‖ |f z - f x| ≤ max ‖z - x‖ |α - f x| :=
      max_le_max le_rfl (by rw [abs_of_nonneg hb0, abs_of_nonneg (by linarith)]; linarith)
    nlinarith
  · have hmb : max ‖z - x‖ |f z - f x| ≤ ‖z - x‖ - (f z - f x) :=
      max_le (by linarith) (by rw [abs_of_neg hb0]; linarith [norm_nonneg (z - x)])
    have hp' : w (z - x) + -(f z - f x) ≤ ε' * (‖z - x‖ - (f z - f x)) :=
      hp.trans (mul_le_mul_of_nonneg_left hmb hε'.le)
    rcases le_or_gt 0 (α - f x) with ha0 | ha0
    · nlinarith
    · have hma : -(α - f x) ≤ max ‖z - x‖ |α - f x| := by
        rw [← abs_of_neg ha0]; exact le_max_right _ _
      have k1 := mul_le_mul_of_nonneg_left hm1 hε'.le
      have k2 := mul_le_mul_of_nonneg_left hma hε'.le
      have k3 : 0 ≤ (1 - ε') * ((α - f x) - (f z - f x)) :=
        mul_nonneg (by linarith) (by linarith)
      have k4 := mul_le_mul_of_nonneg_right hε'1 hM0
      nlinarith

/-- Thm. 1.23 of [Mordukhovich 2018], inclusion `∂f(x₀) ⊆ D*f(x₀)(1)`; this holds for every
real-valued function. -/
theorem subdiff_subset_coderiv_one :
    subdiff (fun x ↦ (f x : EReal)) x₀ ⊆ coderiv (fun x ↦ ({f x} : Set ℝ)) x₀ (f x₀) 1 := by
  intro u hu
  rw [subdiff_eq_outerLimit (φ := fun x ↦ (f x : EReal)) (x₀ := x₀) (r := f x₀) rfl] at hu
  obtain ⟨a, w, ha, hw, hmem⟩ := hu
  obtain ⟨ha1, ha2⟩ := tendsto_funNhds_iff.1 ha
  have hfa : Tendsto (fun k ↦ f (a k)) atTop (𝓝 (f x₀)) := EReal.tendsto_coe.1 ha2
  refine ⟨mem_singleton _, fun k ↦ (a k, f (a k)), fun k ↦ (w k).coprod (-1),
    tendsto_nhdsWithin_iff.2 ⟨ha1.prodMk_nhds hfa, Eventually.of_forall fun k ↦ mem_singleton _⟩,
    tendsto_coprod hw tendsto_const_nhds, fun k ↦ ?_⟩
  have := (mem_regularSubdiff_iff_coprod_mem (φ := fun x ↦ (f x : EReal)) (x₀ := a k)
    (r := f (a k)) rfl).1 (hmem k)
  exact regularNormalCone_anti graph_subset_epi (mem_singleton _) this

/-- Thm. 1.23 of [Mordukhovich 2018], inclusion `D*f(x₀)(1) ⊆ ∂f(x₀)` for `f` lower
semicontinuous around `x₀`. -/
theorem coderiv_one_subset_subdiff (hlsc : ∀ᶠ x in 𝓝 x₀, LowerSemicontinuousAt f x) :
    coderiv (fun x ↦ ({f x} : Set ℝ)) x₀ (f x₀) 1 ⊆ subdiff (fun x ↦ (f x : EReal)) x₀ := by
  rintro u ⟨-, p, ℓ, hp, hℓ, hmem⟩
  rw [subdiff_eq_outerLimit (φ := fun x ↦ (f x : EReal)) (x₀ := x₀) (r := f x₀) rfl]
  have hp' := tendsto_nhdsWithin_iff.1 hp
  have hx : Tendsto (fun k ↦ (p k).1) atTop (𝓝 x₀) := (continuous_fst.tendsto _).comp hp'.1
  have hy : Tendsto (fun k ↦ (p k).2) atTop (𝓝 (f x₀)) := (continuous_snd.tendsto _).comp hp'.1
  have hgraph : ∀ k, (p k).2 = f (p k).1 := fun k ↦ (hmem k).1
  have h01 : Tendsto (fun k ↦ ℓ k (0, 1)) atTop (𝓝 (-1)) := by
    simpa using tendsto_dual_apply hℓ (tendsto_const_nhds (x := ((0 : E), (1 : ℝ))))
  have hneg : ∀ᶠ k in atTop, ℓ k (0, 1) < 0 := (tendsto_order.1 h01).2 0 (by norm_num)
  set μ : ℕ → ℝ := fun k ↦ -ℓ k (0, 1)
  have hμ : Tendsto μ atTop (𝓝 1) := by simpa using h01.neg
  refine mem_outerLimit_of_eventually (fun k ↦ (p k).1)
    (fun k ↦ (μ k)⁻¹ • (ℓ k).comp (ContinuousLinearMap.inl ℝ E ℝ))
    (tendsto_funNhds_iff.2 ⟨hx, ?_⟩) ?_ ?_
  · exact EReal.tendsto_coe.2 (hy.congr hgraph)
  · simpa using (hμ.inv₀ one_ne_zero).smul (tendsto_comp_inl hℓ)
  · filter_upwards [hneg, hx.eventually hlsc] with k hk hlk
    have hμpos : 0 < μ k := by simp only [μ]; linarith
    have hg : (μ k)⁻¹ • ℓ k ∈ regularNormalCone (graph fun x ↦ ({f x} : Set ℝ)) (p k) :=
      smul_mem_regularNormalCone (hmem k) (inv_nonneg.2 hμpos.le)
    have h1 : ((μ k)⁻¹ • ℓ k) (0, 1) = -1 := by
      simp only [smul_apply, smul_eq_mul, μ]
      rw [inv_neg, neg_mul, inv_mul_cancel₀ hk.ne]
    rw [eq_coprod_neg_one _ h1, show p k = ((p k).1, f (p k).1) from Prod.ext rfl (hgraph k)]
      at hg
    have hE := coprod_neg_one_mem_regularNormalCone_epi_of_graph hlk hg
    have := (mem_regularSubdiff_iff_coprod_mem (φ := fun x ↦ (f x : EReal)) (x₀ := (p k).1)
      (r := f (p k).1) rfl).2 hE
    simpa [ContinuousLinearMap.smul_comp] using this

/-- Thm. 1.23, (1.30), of [Mordukhovich 2018] (subdifferentials from coderivatives): for `f`
lower semicontinuous around `x₀`, `∂f(x₀) = D*f(x₀)(1)`. -/
theorem subdiff_eq_coderiv_one (hlsc : ∀ᶠ x in 𝓝 x₀, LowerSemicontinuousAt f x) :
    subdiff (fun x ↦ (f x : EReal)) x₀ = coderiv (fun x ↦ ({f x} : Set ℝ)) x₀ (f x₀) 1 :=
  subset_antisymm subdiff_subset_coderiv_one (coderiv_one_subset_subdiff hlsc)

omit [NormedSpace ℝ E] in
/-- Points strictly above the graph of a function continuous at `x` are interior points of the
epigraph. -/
theorem mem_interior_epi {x : E} {α : ℝ} (hc : ContinuousAt f x) (hlt : f x < α) :
    (x, α) ∈ interior ((fun x ↦ (f x : EReal)).Epi univ) := by
  rw [mem_interior_iff_mem_nhds]
  have hca : ContinuousAt (fun q : E × ℝ ↦ q.2 - f q.1) (x, α) :=
    continuous_snd.continuousAt.sub (hc.comp continuous_fst.continuousAt)
  filter_upwards [hca.eventually (lt_mem_nhds (sub_pos.2 hlt))] with q hq
  exact ⟨mem_univ _, EReal.coe_le_coe_iff.2 (by linarith)⟩

/-- Thm. 1.23, (1.31), of [Mordukhovich 2018]: for `f` continuous around `x₀`,
`∂^∞f(x₀) ⊆ D*f(x₀)(0)`. -/
theorem singularSubdiff_subset_coderiv_zero (hcont : ∀ᶠ x in 𝓝 x₀, ContinuousAt f x) :
    singularSubdiff (fun x ↦ (f x : EReal)) x₀ ⊆
      coderiv (fun x ↦ ({f x} : Set ℝ)) x₀ (f x₀) 0 := by
  intro v hv
  rw [mem_singularSubdiff_iff (φ := fun x ↦ (f x : EReal)) (x₀ := x₀) (r := f x₀) rfl] at hv
  obtain ⟨-, p, ℓ, hp, hℓ, hmem⟩ := hv
  have hp' := tendsto_nhdsWithin_iff.1 hp
  have hgr : ((x₀, f x₀) : E × ℝ) ∈ graph fun x ↦ ({f x} : Set ℝ) := mem_singleton _
  change v.coprod (-(0 : StrongDual ℝ ℝ)) ∈
    normalCone (graph fun x ↦ ({f x} : Set ℝ)) (x₀, f x₀)
  rw [neg_zero]
  by_cases hfr : ∃ᶠ k in atTop, (p k).2 = f (p k).1
  · obtain ⟨φ, hφ, hφP⟩ := extraction_of_frequently_atTop hfr
    refine ⟨hgr, fun k ↦ p (φ k), fun k ↦ ℓ (φ k), tendsto_nhdsWithin_iff.2
      ⟨hp'.1.comp hφ.tendsto_atTop, Eventually.of_forall fun k ↦ hφP k⟩,
      hℓ.comp hφ.tendsto_atTop, fun k ↦ ?_⟩
    exact regularNormalCone_anti graph_subset_epi (hφP k) (hmem (φ k))
  · rw [not_frequently] at hfr
    have hx : Tendsto (fun k ↦ (p k).1) atTop (𝓝 x₀) := (continuous_fst.tendsto _).comp hp'.1
    have hzero : ∀ᶠ k in atTop, ℓ k = 0 := by
      filter_upwards [hfr, hx.eventually hcont] with k hk hck
      have hle : f (p k).1 ≤ (p k).2 := EReal.coe_le_coe_iff.1 (hmem k).1.2
      have hint := mem_interior_epi hck (lt_of_le_of_ne hle (Ne.symm hk))
      have := hmem k
      rw [show p k = ((p k).1, (p k).2) from rfl, regularNormalCone_of_mem_interior hint] at this
      exact this
    have h0 : v.coprod (0 : StrongDual ℝ ℝ) = 0 :=
      tendsto_nhds_unique hℓ (tendsto_const_nhds.congr' (hzero.mono fun k hk ↦ hk.symm))
    rw [h0]
    exact zero_mem_normalCone hgr

end RealValued

section Scalarization

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}

/-- Regular subgradients of the scalarization `⟨v, f⟩` give regular coderivatives of `f`
[Mordukhovich 2018, proof of Thm. 1.32]. -/
theorem coprod_mem_regularNormalCone_graph_of_mem_regularSubdiff {x : E} {v : StrongDual ℝ F}
    {u : StrongDual ℝ E} (hu : u ∈ regularSubdiff (fun x ↦ ((v (f x) : ℝ) : EReal)) x) :
    u.coprod (-v) ∈ regularNormalCone (graph fun x ↦ ({f x} : Set F)) (x, f x) := by
  rw [mem_regularSubdiff_iff (φ := fun x ↦ ((v (f x) : ℝ) : EReal)) (r := v (f x)) rfl] at hu
  refine ⟨mem_singleton _, fun ε hε ↦ ?_⟩
  have h1 : Tendsto Prod.fst (𝓝[graph fun x ↦ ({f x} : Set F)] (x, f x)) (𝓝 x) :=
    (continuous_fst.tendsto _).mono_left nhdsWithin_le_nhds
  filter_upwards [h1.eventually (hu ε hε), self_mem_nhdsWithin] with p hp hpg
  obtain ⟨z, y⟩ := p
  have hy : y = f z := hpg
  subst hy
  simp only [EReal.coe_le_coe_iff] at hp
  simp only [Prod.mk_sub_mk, ContinuousLinearMap.coprod_apply, neg_apply, Prod.norm_mk]
  have h1 := mul_le_mul_of_nonneg_left (le_max_left ‖z - x‖ ‖f z - f x‖) hε.le
  have h2 : v (f z - f x) = v (f z) - v (f x) := map_sub _ _ _
  linarith

/-- Thm. 1.32 of [Mordukhovich 2018] (coderivative scalarization), first part: for `f`
continuous at `x₀`, `∂⟨v, f⟩(x₀) ⊆ D*f(x₀)(v)`. -/
theorem subdiff_comp_subset_coderiv (hf : ContinuousAt f x₀) (v : StrongDual ℝ F) :
    subdiff (fun x ↦ ((v (f x) : ℝ) : EReal)) x₀ ⊆
      coderiv (fun x ↦ ({f x} : Set F)) x₀ (f x₀) v := by
  intro u hu
  rw [subdiff_eq_outerLimit (φ := fun x ↦ ((v (f x) : ℝ) : EReal)) (x₀ := x₀) (r := v (f x₀))
    rfl] at hu
  obtain ⟨a, w, ha, hw, hmem⟩ := hu
  have ha1 := (tendsto_funNhds_iff.1 ha).1
  exact ⟨mem_singleton _, fun k ↦ (a k, f (a k)), fun k ↦ (w k).coprod (-v),
    tendsto_nhdsWithin_iff.2 ⟨ha1.prodMk_nhds (hf.tendsto.comp ha1),
      Eventually.of_forall fun k ↦ mem_singleton _⟩, tendsto_coprod hw tendsto_const_nhds,
    fun k ↦ coprod_mem_regularNormalCone_graph_of_mem_regularSubdiff (hmem k)⟩

/-- Regular coderivatives of a Lipschitz map are `L ‖w - v‖`-subgradients of the scalarization
`⟨v, f⟩`, where `w` is the coderivative argument [Mordukhovich 2018, proof of Thm. 1.32]. -/
theorem mem_epsSubdiff_comp_of_mem_regularNormalCone_graph {x : E} {U : Set E} {L : ℝ≥0}
    (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U) {ℓ : StrongDual ℝ (E × F)}
    (hℓ : ℓ ∈ regularNormalCone (graph fun x ↦ ({f x} : Set F)) (x, f x)) (v : StrongDual ℝ F) :
    ℓ.comp (ContinuousLinearMap.inl ℝ E F) ∈
      epsSubdiff (L * ‖-ℓ.comp (ContinuousLinearMap.inr ℝ E F) - v‖)
        (fun x ↦ ((v (f x) : ℝ) : EReal)) x := by
  rw [mem_epsSubdiff_iff (φ := fun x ↦ ((v (f x) : ℝ) : EReal)) (r := v (f x)) rfl]
  intro ε hε
  set w : StrongDual ℝ F := -ℓ.comp (ContinuousLinearMap.inr ℝ E F)
  have hδ : 0 < ε / (1 + L) := div_pos hε (by positivity)
  have hfc : ContinuousAt f x := hL.continuousOn.continuousAt hU
  have hT : Tendsto (fun z ↦ (z, f z)) (𝓝 x) (𝓝[graph fun x ↦ ({f x} : Set F)] (x, f x)) :=
    tendsto_nhdsWithin_iff.2 ⟨(continuous_id.tendsto x).prodMk_nhds hfc.tendsto,
      Eventually.of_forall fun z ↦ mem_singleton _⟩
  filter_upwards [hT.eventually (hℓ.2 _ hδ), hU] with z hz hzU
  rw [EReal.coe_le_coe_iff]
  have hlip : ‖f z - f x‖ ≤ L * ‖z - x‖ := by
    rw [← dist_eq_norm, ← dist_eq_norm]; exact hL.dist_le_mul z hzU x (mem_of_mem_nhds hU)
  have hsplit : ℓ ((z, f z) - (x, f x)) =
      ℓ.comp (ContinuousLinearMap.inl ℝ E F) (z - x) - w (f z - f x) := by
    rw [Prod.mk_sub_mk, show ((z - x, f z - f x) : E × F) = (z - x, 0) + (0, f z - f x) by simp,
      map_add]
    simp [w]
  rw [hsplit, Prod.mk_sub_mk, Prod.norm_mk] at hz
  have hmax : max ‖z - x‖ ‖f z - f x‖ ≤ (1 + L) * ‖z - x‖ :=
    max_le (by nlinarith [norm_nonneg (z - x), L.coe_nonneg]) (by nlinarith [norm_nonneg (z - x)])
  have h1 : ℓ.comp (ContinuousLinearMap.inl ℝ E F) (z - x) - w (f z - f x) ≤ ε * ‖z - x‖ := by
    calc _ ≤ ε / (1 + L) * max ‖z - x‖ ‖f z - f x‖ := hz
      _ ≤ ε / (1 + L) * ((1 + L) * ‖z - x‖) := by gcongr
      _ = ε * ‖z - x‖ := by field_simp
  have h2 : (w - v) (f z - f x) ≤ L * ‖w - v‖ * ‖z - x‖ := by
    calc (w - v) (f z - f x) ≤ ‖w - v‖ * ‖f z - f x‖ :=
          (le_abs_self _).trans ((w - v).le_opNorm _)
      _ ≤ ‖w - v‖ * (L * ‖z - x‖) := by gcongr
      _ = L * ‖w - v‖ * ‖z - x‖ := by ring
  simp only [sub_apply, map_sub] at h1 h2 ⊢
  nlinarith

/-- Thm. 1.32 of [Mordukhovich 2018] (coderivative scalarization): for `f` Lipschitz around
`x₀`, `D*f(x₀)(v) = ∂⟨v, f⟩(x₀)` (finite dimensions). -/
theorem subdiff_comp_eq_coderiv [FiniteDimensional ℝ E] {U : Set E} {L : ℝ≥0} (hU : U ∈ 𝓝 x₀)
    (hL : LipschitzOnWith L f U) (v : StrongDual ℝ F) :
    subdiff (fun x ↦ ((v (f x) : ℝ) : EReal)) x₀ =
      coderiv (fun x ↦ ({f x} : Set F)) x₀ (f x₀) v := by
  have hfc : ContinuousAt f x₀ := hL.continuousOn.continuousAt hU
  refine subset_antisymm (subdiff_comp_subset_coderiv hfc v) ?_
  rintro u ⟨-, p, ℓ, hp, hℓ, hmem⟩
  have hp' := tendsto_nhdsWithin_iff.1 hp
  have hx : Tendsto (fun k ↦ (p k).1) atTop (𝓝 x₀) := (continuous_fst.tendsto _).comp hp'.1
  have hgraph : ∀ k, (p k).2 = f (p k).1 := fun k ↦ (hmem k).1
  have hvf : ContinuousOn (fun x ↦ v (f x)) U := v.continuous.comp_continuousOn hL.continuousOn
  rw [subdiff_eq_outerLimit_epsSubdiff (φ := fun x ↦ ((v (f x) : ℝ) : EReal)) (x₀ := x₀)
    (r := v (f x₀)) rfl (locallyClosed_epi_of_continuousOn hU hvf _)]
  set w : ℕ → StrongDual ℝ F := fun k ↦ -(ℓ k).comp (ContinuousLinearMap.inr ℝ E F)
  have hw : Tendsto w atTop (𝓝 v) := by simpa [w] using (tendsto_comp_inr hℓ).neg
  have hω : Tendsto (fun k ↦ (L : ℝ) * ‖w k - v‖) atTop (𝓝 0) := by
    simpa using ((continuous_norm.tendsto _).comp (hw.sub_const v)).const_mul (L : ℝ)
  refine mem_outerLimit_of_eventually (fun k ↦ ((p k).1, (L : ℝ) * ‖w k - v‖))
    (fun k ↦ (ℓ k).comp (ContinuousLinearMap.inl ℝ E F)) ?_ ?_ ?_
  · refine (tendsto_funNhds_iff.2 ⟨hx, ?_⟩).prodMk (tendsto_nhdsWithin_iff.2
      ⟨hω, Eventually.of_forall fun k ↦ mem_Ici.2 (mul_nonneg L.coe_nonneg (norm_nonneg _))⟩)
    exact EReal.tendsto_coe.2 ((v.continuous.tendsto _).comp (hfc.tendsto.comp hx))
  · simpa using tendsto_comp_inl hℓ
  · filter_upwards [hx.eventually (eventually_mem_nhds_iff.2 hU)] with k hk
    have hℓk := hmem k
    rw [show p k = ((p k).1, f (p k).1) from Prod.ext rfl (hgraph k)] at hℓk
    exact mem_epsSubdiff_comp_of_mem_regularNormalCone_graph hk hL hℓk v

end Scalarization

end VariationalAnalysis
