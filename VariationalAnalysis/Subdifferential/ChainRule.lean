/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import Mathlib.Analysis.Calculus.MeanValue
import VariationalAnalysis.Subdifferential.Marginal
import VariationalAnalysis.Subdifferential.StrictSum

/-!
# Subdifferentiation of compositions

Basic and singular subgradients of the general composition
`(φ ∘ g)(x) = φ(x, g x)` [Mordukhovich 2018, (4.9)] of `φ : E × F → EReal` with a mapping
`g : E → F` Lipschitz around `x₀`, i.e. the marginal function (4.1) with `G = g`, and the chain
rules for `ψ(g x)`.

For single-valued Lipschitzian `G = g` the argminimum mapping is `g` itself, so it is
automatically `μ`-inner semicontinuous and `μ` is lower semicontinuous at `x₀` when `φ` is; hence
Thm. 4.1 gives (4.10), (4.11) under (4.3) with `G = g`, and the coderivative scalarization
`D*g(x₀)(v) = ∂⟨v, g⟩(x₀)` (Thm. 1.32) turns coderivatives into subgradients.

The book's equality `∂μ(x₀) = {x | (x, 0) ∈ ∂ϑ(x₀, g x₀)}` ("verified similarly to Thm. 3.11(iii)")
is `subdiff_generalComp_eq_penalty` (and its singular version); the new inclusion `⊇` pushes
regular normals of `epi ϑ` forward along `(x, α) ↦ ((x, g x), α)` into `ω`-normals of `epi μ`
(`comp_epiEmbed_mem_epsNormalCone`) and concludes with Thm. 1.6.

## Main results

* `subdiff_generalComp_subset`, `singularSubdiff_generalComp_subset`: Thm. 4.5(i), (4.10), (4.11)
  of [Mordukhovich 2018].
* `generalComp_eq_of_hasFDerivAt`: equality in (4.10) for `φ` of class `C¹`.
* `generalComp_eq_of_lowerRegularAt`: equality in (4.10) and lower regularity of `φ ∘ (I, g)` for
  `φ` lower regular and `g` of class `C¹`.
* `subdiff_generalComp_eq_penalty`, `singularSubdiff_generalComp_eq_penalty`: the equalities
  through `ϑ = φ + δ_{gph g}` in the proof of Thm. 4.5(i).
* `subdiff_comp_lipschitz_subset`, `singularSubdiff_comp_lipschitz_subset`: Cor. 4.6 of
  [Mordukhovich 2018] (chain rules).

Thm. 4.5(ii) is `subdiff_comp_strict_eq` in `VariationalAnalysis.Subdifferential.StrictSum`.
-/

open Filter Topology Set Metric
open scoped Pointwise NNReal

namespace VariationalAnalysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

section Singleton

variable {φ : E × F → EReal} {g : E → F} {x₀ : E}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- For a single-valued constraint `G = g` the marginal function (4.1) is the composition
(4.9) `x ↦ φ(x, g x)`. -/
theorem marginal_singleton (φ : E × F → EReal) (g : E → F) :
    marginal φ (fun x ↦ ({g x} : Set F)) = fun x ↦ φ (x, g x) := by
  funext x
  simp [marginal]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem argminMap_singleton (φ : E × F → EReal) (g : E → F) (x : E) :
    argminMap φ (fun x ↦ ({g x} : Set F)) x = {g x} := by
  ext y
  simp only [argminMap, mem_singleton_iff, marginal_singleton, mem_ofPred_eq]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, h ▸ rfl⟩⟩

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- For a single-valued constraint `G = g` continuous at `x₀`, the argminimum mapping `M = g` is
`μ`-inner semicontinuous at `(x₀, g x₀)`. -/
theorem mem_innerLimit_singleton (hg : ContinuousAt g x₀) :
    g x₀ ∈ innerLimit (funNhds (marginal φ fun x ↦ ({g x} : Set F)) x₀)
      (argminMap φ fun x ↦ ({g x} : Set F)) :=
  fun _ ha ↦ ⟨fun k ↦ g _, hg.tendsto.comp (tendsto_funNhds_iff.1 ha).1,
    Eventually.of_forall fun k ↦ by rw [argminMap_singleton]; rfl⟩

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem lowerSemicontinuousAt_comp_prodMk (hφ : LowerSemicontinuousAt φ (x₀, g x₀))
    (hg : ContinuousAt g x₀) : LowerSemicontinuousAt (fun x ↦ φ (x, g x)) x₀ :=
  LowerSemicontinuousAt.comp (g := fun x ↦ (x, g x)) hφ (continuousAt_id.prodMk hg)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- The epigraph of `x ↦ φ(x, g x)` is locally closed around `(x₀, r)` if that of `φ` is locally
closed around `((x₀, g x₀), r)` and `g` is Lipschitz around `x₀`. -/
theorem locallyClosed_epi_comp_prodMk {U : Set E} {K : ℝ≥0} (hU : U ∈ 𝓝 x₀)
    (hg : LipschitzOnWith K g U) {r : ℝ}
    (hφ : ∃ ρ > 0, IsClosed (φ.Epi univ ∩ closedBall (((x₀, g x₀), r) : (E × F) × ℝ) ρ)) :
    ∃ ρ > 0, IsClosed ((fun x ↦ φ (x, g x)).Epi univ ∩ closedBall ((x₀, r) : E × ℝ) ρ) := by
  obtain ⟨ρ, hρ, hcl⟩ := hφ
  obtain ⟨δ₀, hδ₀, hsub⟩ := nhds_basis_closedBall.mem_iff.1 hU
  set δ := min δ₀ (ρ / (K + 1)) with hδ
  have hδpos : 0 < δ := lt_min hδ₀ (div_pos hρ (by positivity))
  have hδρ : δ ≤ ρ :=
    (min_le_right _ _).trans (div_le_self hρ.le (by linarith [NNReal.coe_nonneg K]))
  have hKδ : K * δ ≤ ρ := by
    have h1 : δ ≤ ρ / (K + 1) := min_le_right _ _
    have h2 : (K : ℝ) * δ ≤ (K + 1) * δ := by nlinarith [NNReal.coe_nonneg K]
    calc (K : ℝ) * δ ≤ (K + 1) * δ := h2
      _ ≤ (K + 1) * (ρ / (K + 1)) := by gcongr
      _ = ρ := by field_simp
  have hcont : ContinuousOn g U := hg.continuousOn
  refine ⟨δ, hδpos, isClosed_of_closure_subset fun q hq ↦ ?_⟩
  obtain ⟨z, hz, hzq⟩ := mem_closure_iff_seq_limit.1 hq
  have hqB : q ∈ closedBall ((x₀, r) : E × ℝ) δ :=
    isClosed_closedBall.mem_of_tendsto hzq (Eventually.of_forall fun k ↦ (hz k).2)
  have hB : ∀ p ∈ closedBall ((x₀, r) : E × ℝ) δ, p.1 ∈ closedBall x₀ δ ∧ |p.2 - r| ≤ δ :=
    fun p hp ↦ by
      rw [mem_closedBall, Prod.dist_eq, max_le_iff] at hp
      exact ⟨mem_closedBall.2 hp.1, by simpa [Real.dist_eq] using hp.2⟩
  have hU' : ∀ p ∈ closedBall ((x₀, r) : E × ℝ) δ, p.1 ∈ U := fun p hp ↦
    hsub (closedBall_subset_closedBall (min_le_left _ _) (hB p hp).1)
  set T : E × ℝ → (E × F) × ℝ := fun p ↦ ((p.1, g p.1), p.2)
  have hT : ∀ p ∈ (fun x ↦ φ (x, g x)).Epi univ ∩ closedBall ((x₀, r) : E × ℝ) δ,
      T p ∈ φ.Epi univ ∩ closedBall (((x₀, g x₀), r) : (E × F) × ℝ) ρ := by
    intro p hp
    refine ⟨⟨mem_univ _, hp.1.2⟩, ?_⟩
    obtain ⟨h1, h2⟩ := hB p hp.2
    have hgd : dist (g p.1) (g x₀) ≤ K * dist p.1 x₀ :=
      hg.dist_le_mul _ (hU' p hp.2) _ (mem_of_mem_nhds hU)
    rw [mem_closedBall] at h1 ⊢
    simp only [T, Prod.dist_eq, max_le_iff, Real.dist_eq]
    refine ⟨⟨h1.trans hδρ, hgd.trans ((mul_le_mul_of_nonneg_left h1 K.coe_nonneg).trans hKδ)⟩,
      h2.trans hδρ⟩
  have hlim : Tendsto (fun k ↦ T (z k)) atTop (𝓝 (T q)) := by
    have h1 : Tendsto (fun k ↦ (z k).1) atTop (𝓝[U] q.1) :=
      tendsto_nhdsWithin_iff.2 ⟨(continuous_fst.tendsto q).comp hzq,
        Eventually.of_forall fun k ↦ hU' _ (hz k).2⟩
    exact (((continuous_fst.tendsto q).comp hzq).prodMk_nhds
      ((hcont _ (hU' q hqB)).tendsto.comp h1)).prodMk_nhds ((continuous_snd.tendsto q).comp hzq)
  have hmem := hcl.mem_of_tendsto hlim (Eventually.of_forall fun k ↦ hT _ (hz k))
  exact ⟨⟨mem_univ _, hmem.1.2⟩, hqB⟩

end Singleton

section Inclusions

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
variable {φ : E × F → EReal} {g : E → F} {x₀ : E} {U : Set E} {K : ℝ≥0} {r : ℝ}

/-- Thm. 4.5(i) of [Mordukhovich 2018], (4.10) (basic subgradients of general compositions): let
`g : E → F` be Lipschitz around `x₀`, `φ(x₀, g x₀) = r` finite, the epigraph of `φ` locally
closed around `((x₀, g x₀), r)`, and assume (4.3) with `G = g`,
`∂^∞φ(x₀, g x₀) ∩ (-N((x₀, g x₀); gph g)) = {0}`. Then
`∂(φ ∘ (I, g))(x₀) ⊆ ⋃_{(u, v) ∈ ∂φ(x₀, g x₀)} [u + ∂⟨v, g⟩(x₀)]`. -/
theorem subdiff_generalComp_subset (hU : U ∈ 𝓝 x₀) (hg : LipschitzOnWith K g U)
    (hr : φ (x₀, g x₀) = r)
    (hφ : ∃ ρ > 0, IsClosed (φ.Epi univ ∩ closedBall (((x₀, g x₀), r) : (E × F) × ℝ) ρ))
    (hqc : ∀ w ∈ singularSubdiff φ (x₀, g x₀),
      -w ∈ normalCone (graph fun x ↦ ({g x} : Set F)) (x₀, g x₀) → w = 0) :
    subdiff (fun x ↦ φ (x, g x)) x₀ ⊆
      {x | ∃ u v, u.coprod v ∈ subdiff φ (x₀, g x₀) ∧
        x - u ∈ subdiff (fun x ↦ ((v (g x) : ℝ) : EReal)) x₀} := by
  have hgc : ContinuousAt g x₀ := hg.continuousOn.continuousAt hU
  intro x hx
  rw [← marginal_singleton] at hx
  have hr' : marginal φ (fun x ↦ ({g x} : Set F)) x₀ = r := by rw [marginal_singleton]; exact hr
  have hy₀ : g x₀ ∈ argminMap φ (fun x ↦ ({g x} : Set F)) x₀ := by
    rw [argminMap_singleton]; rfl
  obtain ⟨u, v, huv, hxu⟩ := subdiff_marginal_subset hr' hy₀ (mem_innerLimit_singleton hgc) hφ
    (locallyClosed_graph_of_continuousOn hU hg.continuousOn) hqc hx
  exact ⟨u, v, huv, by rwa [subdiff_comp_eq_coderiv hU hg]⟩

/-- Thm. 4.5(i) of [Mordukhovich 2018], (4.11) (singular subgradients of general compositions):
under the assumptions of `subdiff_generalComp_subset`,
`∂^∞(φ ∘ (I, g))(x₀) ⊆ ⋃_{(u, v) ∈ ∂^∞φ(x₀, g x₀)} [u + ∂⟨v, g⟩(x₀)]`. -/
theorem singularSubdiff_generalComp_subset (hU : U ∈ 𝓝 x₀) (hg : LipschitzOnWith K g U)
    (hr : φ (x₀, g x₀) = r)
    (hφ : ∃ ρ > 0, IsClosed (φ.Epi univ ∩ closedBall (((x₀, g x₀), r) : (E × F) × ℝ) ρ))
    (hqc : ∀ w ∈ singularSubdiff φ (x₀, g x₀),
      -w ∈ normalCone (graph fun x ↦ ({g x} : Set F)) (x₀, g x₀) → w = 0) :
    singularSubdiff (fun x ↦ φ (x, g x)) x₀ ⊆
      {x | ∃ u v, u.coprod v ∈ singularSubdiff φ (x₀, g x₀) ∧
        x - u ∈ subdiff (fun x ↦ ((v (g x) : ℝ) : EReal)) x₀} := by
  have hgc : ContinuousAt g x₀ := hg.continuousOn.continuousAt hU
  have hlsc : LowerSemicontinuousAt (marginal φ fun x ↦ ({g x} : Set F)) x₀ := by
    rw [marginal_singleton]
    exact lowerSemicontinuousAt_comp_prodMk (lowerSemicontinuousAt_of_locallyClosed_epi hr hφ) hgc
  intro x hx
  rw [← marginal_singleton] at hx
  have hr' : marginal φ (fun x ↦ ({g x} : Set F)) x₀ = r := by rw [marginal_singleton]; exact hr
  have hy₀ : g x₀ ∈ argminMap φ (fun x ↦ ({g x} : Set F)) x₀ := by
    rw [argminMap_singleton]; rfl
  obtain ⟨u, v, huv, hxu⟩ := singularSubdiff_marginal_subset hr' hy₀ (mem_innerLimit_singleton hgc)
    hlsc hφ (locallyClosed_graph_of_continuousOn hU hg.continuousOn) hqc hx
  exact ⟨u, v, huv, by rwa [subdiff_comp_eq_coderiv hU hg]⟩

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The epigraph of `φ ∘ snd` is locally closed around `((x₀, y₀), r)` if that of `φ` is locally
closed around `(y₀, r)`. -/
theorem locallyClosed_epi_comp_snd_of_locallyClosed {ψ : F → EReal} {y₀ : F}
    (hψ : ∃ ρ > 0, IsClosed (ψ.Epi univ ∩ closedBall ((y₀, r) : F × ℝ) ρ)) :
    ∃ ρ > 0, IsClosed ((fun p : E × F ↦ ψ p.2).Epi univ ∩
      closedBall (((x₀, y₀), r) : (E × F) × ℝ) ρ) := by
  obtain ⟨ρ, hρ, hcl⟩ := hψ
  refine ⟨ρ, hρ, ?_⟩
  have heq : (fun p : E × F ↦ ψ p.2).Epi univ ∩ closedBall (((x₀, y₀), r) : (E × F) × ℝ) ρ =
      (fun q : (E × F) × ℝ ↦ (q.1.2, q.2)) ⁻¹' (ψ.Epi univ ∩ closedBall ((y₀, r) : F × ℝ) ρ) ∩
        (fun q : (E × F) × ℝ ↦ q.1.1) ⁻¹' closedBall x₀ ρ := by
    ext ⟨⟨x, y⟩, α⟩
    simp only [Function.Epi, mem_inter_iff, mem_ofPred_eq, mem_univ, true_and, mem_closedBall,
      Prod.dist_eq, max_le_iff, mem_preimage]
    tauto
  rw [heq]
  exact (hcl.preimage ((continuous_snd.comp continuous_fst).prodMk continuous_snd)).inter
    (isClosed_closedBall.preimage (continuous_fst.comp continuous_fst))

/-- The qualification condition of Cor. 4.6 implies (4.3) for `φ(x, y) = ψ(y)` and `G = g`
[Mordukhovich 2018, proof of Cor. 4.6]. -/
theorem generalComp_qc_of_comp {ψ : F → EReal} (hU : U ∈ 𝓝 x₀) (hg : LipschitzOnWith K g U)
    (hqc : ∀ v ∈ singularSubdiff ψ (g x₀),
      (0 : StrongDual ℝ E) ∈ subdiff (fun x ↦ ((v (g x) : ℝ) : EReal)) x₀ → v = 0) :
    ∀ w ∈ singularSubdiff (fun p : E × F ↦ ψ p.2) (x₀, g x₀),
      -w ∈ normalCone (graph fun x ↦ ({g x} : Set F)) (x₀, g x₀) → w = 0 := by
  intro w hw hN
  rw [singularSubdiff_comp_snd] at hw
  obtain ⟨v, hv, rfl⟩ := hw
  have h0 : (0 : StrongDual ℝ E) ∈ coderiv (fun x ↦ ({g x} : Set F)) x₀ (g x₀) v := by
    show _ ∈ normalCone _ _
    convert hN using 1
    ext <;> simp
  rw [← subdiff_comp_eq_coderiv hU hg] at h0
  rw [hqc v hv h0]
  exact ContinuousLinearMap.zero_comp _

/-- Cor. 4.6 of [Mordukhovich 2018] (chain rule for basic subgradients): let `g : E → F` be
Lipschitz around `x₀`, `ψ : F → EReal` finite at `g x₀` with epigraph locally closed around
`(g x₀, ψ (g x₀))` (e.g. `ψ` l.s.c. around `g x₀`), and assume the qualification condition
`∂^∞ψ(g x₀) ∩ ker ∂⟨·, g⟩(x₀) = {0}`, i.e. `v ∈ ∂^∞ψ(g x₀)` and `0 ∈ ∂⟨v, g⟩(x₀)` imply
`v = 0`. Then `∂(ψ ∘ g)(x₀) ⊆ ⋃_{v ∈ ∂ψ(g x₀)} ∂⟨v, g⟩(x₀)`. -/
theorem subdiff_comp_lipschitz_subset {ψ : F → EReal} (hU : U ∈ 𝓝 x₀)
    (hg : LipschitzOnWith K g U) (hr : ψ (g x₀) = r)
    (hψ : ∃ ρ > 0, IsClosed (ψ.Epi univ ∩ closedBall ((g x₀, r) : F × ℝ) ρ))
    (hqc : ∀ v ∈ singularSubdiff ψ (g x₀),
      (0 : StrongDual ℝ E) ∈ subdiff (fun x ↦ ((v (g x) : ℝ) : EReal)) x₀ → v = 0) :
    subdiff (fun x ↦ ψ (g x)) x₀ ⊆
      ⋃ v ∈ subdiff ψ (g x₀), subdiff (fun x ↦ ((v (g x) : ℝ) : EReal)) x₀ := by
  intro x hx
  obtain ⟨u, v, huv, hxu⟩ := subdiff_generalComp_subset (φ := fun p : E × F ↦ ψ p.2) hU hg hr
    (locallyClosed_epi_comp_snd_of_locallyClosed hψ) (generalComp_qc_of_comp hU hg hqc) hx
  rw [subdiff_comp_snd] at huv
  obtain ⟨w, hw, hwe⟩ := huv
  replace hwe : (0 : StrongDual ℝ E).coprod w = u.coprod v :=
    (comp_snd_eq_coprod w).symm.trans hwe
  have hu : 0 = u := by simpa using congrArg (fun ℓ ↦ ℓ.comp (ContinuousLinearMap.inl ℝ E F)) hwe
  have hv : w = v := by simpa using congrArg (fun ℓ ↦ ℓ.comp (ContinuousLinearMap.inr ℝ E F)) hwe
  rw [← hu, sub_zero, ← hv] at hxu
  exact mem_iUnion₂.2 ⟨w, hw, hxu⟩

/-- Cor. 4.6 of [Mordukhovich 2018] (chain rule for singular subgradients): under the
assumptions of `subdiff_comp_lipschitz_subset`,
`∂^∞(ψ ∘ g)(x₀) ⊆ ⋃_{v ∈ ∂^∞ψ(g x₀)} ∂⟨v, g⟩(x₀)`. -/
theorem singularSubdiff_comp_lipschitz_subset {ψ : F → EReal} (hU : U ∈ 𝓝 x₀)
    (hg : LipschitzOnWith K g U) (hr : ψ (g x₀) = r)
    (hψ : ∃ ρ > 0, IsClosed (ψ.Epi univ ∩ closedBall ((g x₀, r) : F × ℝ) ρ))
    (hqc : ∀ v ∈ singularSubdiff ψ (g x₀),
      (0 : StrongDual ℝ E) ∈ subdiff (fun x ↦ ((v (g x) : ℝ) : EReal)) x₀ → v = 0) :
    singularSubdiff (fun x ↦ ψ (g x)) x₀ ⊆
      ⋃ v ∈ singularSubdiff ψ (g x₀), subdiff (fun x ↦ ((v (g x) : ℝ) : EReal)) x₀ := by
  intro x hx
  obtain ⟨u, v, huv, hxu⟩ := singularSubdiff_generalComp_subset (φ := fun p : E × F ↦ ψ p.2) hU
    hg hr (locallyClosed_epi_comp_snd_of_locallyClosed hψ) (generalComp_qc_of_comp hU hg hqc) hx
  rw [singularSubdiff_comp_snd] at huv
  obtain ⟨w, hw, hwe⟩ := huv
  replace hwe : (0 : StrongDual ℝ E).coprod w = u.coprod v :=
    (comp_snd_eq_coprod w).symm.trans hwe
  have hu : 0 = u := by simpa using congrArg (fun ℓ ↦ ℓ.comp (ContinuousLinearMap.inl ℝ E F)) hwe
  have hv : w = v := by simpa using congrArg (fun ℓ ↦ ℓ.comp (ContinuousLinearMap.inr ℝ E F)) hwe
  rw [← hu, sub_zero, ← hv] at hxu
  exact mem_iUnion₂.2 ⟨w, hw, hxu⟩

end Inclusions

/-- The embedding `(x, α) ↦ ((x, 0), α)` of `E × ℝ` into `(E × F) × ℝ`. -/
noncomputable def epiEmbed : E × ℝ →L[ℝ] (E × F) × ℝ :=
  (ContinuousLinearMap.inl ℝ E F).prodMap (ContinuousLinearMap.id ℝ ℝ)

/-- The embedding `y ↦ ((0, y), 0)` of `F` into `(E × F) × ℝ`. -/
noncomputable def epiInr : F →L[ℝ] (E × F) × ℝ :=
  (ContinuousLinearMap.inl ℝ (E × F) ℝ).comp (ContinuousLinearMap.inr ℝ E F)

section Equality

variable {φ : E × F → EReal} {g : E → F} {x₀ : E} {U : Set E} {K : ℝ≥0} {r : ℝ}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem graphRestrict_singleton (x : E) :
    graphRestrict φ (fun x ↦ ({g x} : Set F)) (x, g x) = φ (x, g x) :=
  graphRestrict_of_mem rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem marginalPenalty_singleton (x : E) :
    marginalPenalty φ (fun x ↦ ({g x} : Set F)) (x, g x) = φ (x, g x) := by
  simp [marginalPenalty, convex_indicator_of_mem (show (x, g x) ∈ graph fun x ↦ ({g x} : Set F)
    from rfl)]

/-- [Mordukhovich 2018, proof of Thm. 4.5(i)]: a regular normal `ℓ` to `epi ϑ` at
`((x, g x), α)`, `ϑ = φ + δ_{gph g}`, gives the `K ‖ℓ(0, ·, 0)‖`-normal `ℓ((·, 0), ·)` to the
epigraph of `φ ∘ (I, g)` at `(x, α)`, for `g` `K`-Lipschitz on an open set containing `x`. -/
theorem comp_epiEmbed_mem_epsNormalCone {V : Set E} (hV : IsOpen V) (hg : LipschitzOnWith K g V)
    {x : E} (hx : x ∈ V) {α : ℝ} {ℓ : StrongDual ℝ ((E × F) × ℝ)}
    (hℓ : ℓ ∈ regularNormalCone ((graphRestrict φ fun x ↦ ({g x} : Set F)).Epi univ)
      ((x, g x), α)) :
    ℓ.comp epiEmbed ∈ epsNormalCone (K * ‖ℓ.comp (epiInr (E := E))‖)
      ((fun x ↦ φ (x, g x)).Epi univ) (x, α) := by
  have hbase : φ (x, g x) ≤ α := by have := hℓ.1.2; rwa [graphRestrict_singleton] at this
  refine ⟨⟨mem_univ _, hbase⟩, fun ε hε ↦ ?_⟩
  set c := ‖ℓ.comp (epiInr (E := E))‖
  set T : E × ℝ → (E × F) × ℝ := fun p ↦ ((p.1, g p.1), p.2) with hTdef
  have hgc : ContinuousAt g x := hg.continuousOn.continuousAt (hV.mem_nhds hx)
  have hTc : ContinuousAt T (x, α) :=
    (continuous_fst.continuousAt.prodMk (hgc.comp continuous_fst.continuousAt)).prodMk
      continuous_snd.continuousAt
  have hTt : Tendsto T (𝓝[(fun x ↦ φ (x, g x)).Epi univ] (x, α))
      (𝓝[(graphRestrict φ fun x ↦ ({g x} : Set F)).Epi univ] (T (x, α))) :=
    tendsto_nhdsWithin_iff.2 ⟨hTc.tendsto.mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun p hp ↦
        ⟨mem_univ _, by rw [graphRestrict_singleton]; exact hp.2⟩⟩
  have hK1 : (0 : ℝ) < 1 + K := by positivity
  have hε' : 0 < ε / (1 + K) := div_pos hε hK1
  have hV' : ∀ᶠ p in 𝓝[(fun x ↦ φ (x, g x)).Epi univ] (x, α), p.1 ∈ V :=
    ((continuous_fst.tendsto (x, α)).mono_left nhdsWithin_le_nhds).eventually (hV.mem_nhds hx)
  filter_upwards [hTt.eventually (hℓ.2 _ hε'), hV'] with p hp hpV
  have hdec : T p - T (x, α) = epiEmbed (p - (x, α)) + epiInr (g p.1 - g x) := by
    simp only [hTdef, epiEmbed, epiInr]
    ext <;> simp
  have hgd : ‖g p.1 - g x‖ ≤ K * ‖p.1 - x‖ := by
    rw [← dist_eq_norm, ← dist_eq_norm]; exact hg.dist_le_mul _ hpV _ hx
  have h1 : ‖p.1 - x‖ ≤ ‖p - (x, α)‖ := by simpa using norm_fst_le (p - (x, α))
  have h2 : ‖p.2 - α‖ ≤ ‖p - (x, α)‖ := by simpa using norm_snd_le (p - (x, α))
  have hTn : ‖T p - T (x, α)‖ ≤ (1 + K) * ‖p - (x, α)‖ := by
    have hn : 0 ≤ ‖p - (x, α)‖ := norm_nonneg _
    simp only [hTdef, Prod.mk_sub_mk]
    refine norm_prod_le_iff.2 ⟨norm_prod_le_iff.2 ⟨?_, ?_⟩, ?_⟩
    · nlinarith [NNReal.coe_nonneg K]
    · nlinarith [NNReal.coe_nonneg K]
    · nlinarith [NNReal.coe_nonneg K]
  have hJ : -(ℓ.comp (epiInr (E := E))) (g p.1 - g x) ≤ c * ‖g p.1 - g x‖ :=
    (neg_le_abs _).trans (by simpa [Real.norm_eq_abs] using
      (ℓ.comp (epiInr (E := E))).le_opNorm (g p.1 - g x))
  have hc : 0 ≤ c := norm_nonneg _
  have hp' : ℓ (T p - T (x, α)) ≤ ε / (1 + K) * ‖T p - T (x, α)‖ := hp
  calc (ℓ.comp epiEmbed) (p - (x, α))
      = ℓ (T p - T (x, α)) - (ℓ.comp (epiInr (E := E))) (g p.1 - g x) := by
        rw [hdec, map_add]; simp
    _ ≤ ε / (1 + K) * ‖T p - T (x, α)‖ + c * ‖g p.1 - g x‖ := by linarith
    _ ≤ ε / (1 + K) * ((1 + K) * ‖p - (x, α)‖) + c * (K * ‖p - (x, α)‖) := by
        gcongr
        exact hgd.trans (mul_le_mul_of_nonneg_left h1 K.coe_nonneg)
    _ = (K * c + ε) * ‖p - (x, α)‖ := by field_simp; ring

variable [FiniteDimensional ℝ E]

/-- [Mordukhovich 2018, proof of Thm. 4.5(i)], via `ω`-normals and Thm. 1.6: a normal `ℓ` to
`epi ϑ` at `((x₀, g x₀), r)` with vanishing `F`-component gives the normal `ℓ((·, 0), ·)` to the
epigraph of `φ ∘ (I, g)` at `(x₀, r)`, for `g` Lipschitz around `x₀`. -/
theorem comp_epiEmbed_mem_normalCone (hU : U ∈ 𝓝 x₀) (hg : LipschitzOnWith K g U)
    (hr : φ (x₀, g x₀) = r)
    (hφ : ∃ ρ > 0, IsClosed (φ.Epi univ ∩ closedBall (((x₀, g x₀), r) : (E × F) × ℝ) ρ))
    {ℓ : StrongDual ℝ ((E × F) × ℝ)}
    (hℓ : ℓ ∈ normalCone ((graphRestrict φ fun x ↦ ({g x} : Set F)).Epi univ) ((x₀, g x₀), r))
    (h0 : ℓ.comp (epiInr (E := E)) = 0) :
    ℓ.comp epiEmbed ∈ normalCone ((fun x ↦ φ (x, g x)).Epi univ) (x₀, r) := by
  obtain ⟨V, hVU, hVo, hx₀V⟩ := _root_.mem_nhds_iff.1 hU
  have hgV := hg.mono hVU
  obtain ⟨-, q, ℓs, hq, hℓs, hmem⟩ := hℓ
  have hq' := (tendsto_nhdsWithin_iff.1 hq).1
  have hgraph : ∀ k, (q k).1.2 = g (q k).1.1 := by
    intro k
    have h := (hmem k).1.2
    by_contra hne
    rw [graphRestrict, if_neg (show (q k).1 ∉ graph fun x ↦ ({g x} : Set F) from hne)] at h
    exact EReal.coe_ne_top _ (top_le_iff.1 h)
  set p : ℕ → E × ℝ := fun k ↦ ((q k).1.1, (q k).2) with hpdef
  have hqk : ∀ k, q k = (((p k).1, g (p k).1), (p k).2) := fun k ↦ by
    show q k = (((q k).1.1, g (q k).1.1), (q k).2)
    rw [← hgraph k]
  have hpt : Tendsto p atTop (𝓝 (x₀, r)) :=
    (((continuous_fst.comp continuous_fst).prodMk continuous_snd).tendsto _).comp hq'
  have hpepi : ∀ k, p k ∈ (fun x ↦ φ (x, g x)).Epi univ := fun k ↦ by
    have h := (hmem k).1.2
    rw [hqk k, graphRestrict_singleton] at h
    exact ⟨mem_univ _, h⟩
  have hV : ∀ᶠ k in atTop, (p k).1 ∈ V :=
    ((continuous_fst.tendsto _).comp hpt).eventually (hVo.mem_nhds hx₀V)
  have hω : Tendsto (fun k ↦ (K : ℝ) * ‖(ℓs k).comp (epiInr (E := E))‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k ↦ (ℓs k).comp (epiInr (E := E))) atTop
        (𝓝 (ℓ.comp (epiInr (E := E)))) :=
      (((epiInr (E := E) (F := F)).precomp ℝ).continuous.tendsto ℓ).comp hℓs
    rw [h0] at h1
    simpa using (tendsto_norm_zero.comp h1).const_mul (K : ℝ)
  rw [normalCone_eq_outerLimit_epsNormalCone
    (show ((x₀, r) : E × ℝ) ∈ (fun x ↦ φ (x, g x)).Epi univ from ⟨mem_univ _, hr.le⟩)
    (locallyClosed_epi_comp_prodMk hU hg hφ)]
  have hT1 : Tendsto p atTop (𝓝[(fun x ↦ φ (x, g x)).Epi univ] (x₀, r)) :=
    tendsto_nhdsWithin_iff.2 ⟨hpt, Eventually.of_forall hpepi⟩
  have hT2 : Tendsto (fun k ↦ (K : ℝ) * ‖(ℓs k).comp (epiInr (E := E))‖) atTop
      (𝓝[≥] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hω, Eventually.of_forall fun k ↦ mem_Ici.2 (by positivity)⟩
  refine mem_outerLimit_of_eventually (fun k ↦ (p k, (K : ℝ) * ‖(ℓs k).comp (epiInr (E := E))‖))
    (fun k ↦ (ℓs k).comp epiEmbed) (hT1.prodMk hT2)
    ((((epiEmbed (E := E) (F := F)).precomp ℝ).continuous.tendsto ℓ).comp hℓs) ?_
  filter_upwards [hV] with k hk
  have h := hmem k
  rw [hqk k] at h
  exact comp_epiEmbed_mem_epsNormalCone hVo hgV hk h

omit [FiniteDimensional ℝ E] in
theorem coprod_comp_epiEmbed (x : StrongDual ℝ E) (c : StrongDual ℝ ℝ) :
    ((x.coprod (0 : StrongDual ℝ F)).coprod c).comp epiEmbed = x.coprod c := by
  ext <;> simp [epiEmbed]

omit [FiniteDimensional ℝ E] in
theorem coprod_comp_epiInr (x : StrongDual ℝ E) (c : StrongDual ℝ ℝ) :
    ((x.coprod (0 : StrongDual ℝ F)).coprod c).comp (epiInr (E := E)) = 0 := by
  ext; simp [epiInr]

/-- [Mordukhovich 2018, proof of Thm. 4.5(i)] ("verified similarly to the proof of
Thm. 3.11(iii)"): for `g` Lipschitz around `x₀` and `φ` with epigraph locally closed around
`((x₀, g x₀), φ(x₀, g x₀))`, `∂(φ ∘ (I, g))(x₀) = {x | (x, 0) ∈ ∂ϑ(x₀, g x₀)}` with
`ϑ = φ + δ_{gph g}`. -/
theorem subdiff_generalComp_eq_penalty (hU : U ∈ 𝓝 x₀) (hg : LipschitzOnWith K g U)
    (hr : φ (x₀, g x₀) = r)
    (hφ : ∃ ρ > 0, IsClosed (φ.Epi univ ∩ closedBall (((x₀, g x₀), r) : (E × F) × ℝ) ρ)) :
    subdiff (fun x ↦ φ (x, g x)) x₀ = {x | x.coprod (0 : StrongDual ℝ F) ∈
      subdiff (marginalPenalty φ fun x ↦ ({g x} : Set F)) (x₀, g x₀)} := by
  have hgc : ContinuousAt g x₀ := hg.continuousOn.continuousAt hU
  have hlφ := lowerSemicontinuousAt_of_locallyClosed_epi hr hφ
  have hr' : marginal φ (fun x ↦ ({g x} : Set F)) x₀ = r := by rw [marginal_singleton]; exact hr
  have hy₀ : g x₀ ∈ argminMap φ (fun x ↦ ({g x} : Set F)) x₀ := by
    rw [argminMap_singleton]; rfl
  refine subset_antisymm ?_ fun x hx ↦ ?_
  · rw [← marginal_singleton]
    exact subdiff_marginal_subset_penalty hr' hy₀ (mem_innerLimit_singleton hgc) hlφ
  · rw [mem_ofPred_eq, ← subdiff_congr (graphRestrict_eventuallyEq hr hlφ),
      mem_subdiff_iff ((graphRestrict_singleton x₀).trans hr)] at hx
    rw [mem_subdiff_iff (φ := fun x ↦ φ (x, g x)) hr, ← coprod_comp_epiEmbed (F := F)]
    exact comp_epiEmbed_mem_normalCone hU hg hr hφ hx (coprod_comp_epiInr _ _)

/-- The singular counterpart of `subdiff_generalComp_eq_penalty`:
`∂^∞(φ ∘ (I, g))(x₀) = {x | (x, 0) ∈ ∂^∞ϑ(x₀, g x₀)}`. -/
theorem singularSubdiff_generalComp_eq_penalty (hU : U ∈ 𝓝 x₀) (hg : LipschitzOnWith K g U)
    (hr : φ (x₀, g x₀) = r)
    (hφ : ∃ ρ > 0, IsClosed (φ.Epi univ ∩ closedBall (((x₀, g x₀), r) : (E × F) × ℝ) ρ)) :
    singularSubdiff (fun x ↦ φ (x, g x)) x₀ = {x | x.coprod (0 : StrongDual ℝ F) ∈
      singularSubdiff (marginalPenalty φ fun x ↦ ({g x} : Set F)) (x₀, g x₀)} := by
  have hgc : ContinuousAt g x₀ := hg.continuousOn.continuousAt hU
  have hlφ := lowerSemicontinuousAt_of_locallyClosed_epi hr hφ
  have hr' : marginal φ (fun x ↦ ({g x} : Set F)) x₀ = r := by rw [marginal_singleton]; exact hr
  have hy₀ : g x₀ ∈ argminMap φ (fun x ↦ ({g x} : Set F)) x₀ := by
    rw [argminMap_singleton]; rfl
  have hlsc : LowerSemicontinuousAt (marginal φ fun x ↦ ({g x} : Set F)) x₀ := by
    rw [marginal_singleton]; exact lowerSemicontinuousAt_comp_prodMk hlφ hgc
  refine subset_antisymm ?_ fun x hx ↦ ?_
  · rw [← marginal_singleton]
    exact singularSubdiff_marginal_subset_penalty hr' hy₀ (mem_innerLimit_singleton hgc) hlφ hlsc
  · rw [mem_ofPred_eq, ← singularSubdiff_congr (graphRestrict_eventuallyEq hr hlφ),
      mem_singularSubdiff_iff ((graphRestrict_singleton x₀).trans hr)] at hx
    rw [mem_singularSubdiff_iff (φ := fun x ↦ φ (x, g x)) hr, ← coprod_comp_epiEmbed (F := F)]
    exact comp_epiEmbed_mem_normalCone hU hg hr hφ hx (coprod_comp_epiInr _ _)

end Equality

section Regularity

variable {φ : E × F → EReal} {g : E → F} {x₀ : E} {U : Set E} {K : ℝ≥0} {r : ℝ}

/-- Regular subgradients of `ϑ = φ + δ_{gph g}` of the form `(x, 0)` give regular subgradients of
`φ ∘ (I, g)`, for `g` Lipschitz around `x₀` (the regular part of
[Mordukhovich 2018, proof of Thm. 4.5(i)]). -/
theorem mem_regularSubdiff_generalComp_of_coprod_zero_mem (hU : U ∈ 𝓝 x₀)
    (hg : LipschitzOnWith K g U) {x : StrongDual ℝ E}
    (hx : x.coprod (0 : StrongDual ℝ F) ∈
      regularSubdiff (marginalPenalty φ fun x ↦ ({g x} : Set F)) (x₀, g x₀)) :
    x ∈ regularSubdiff (fun x ↦ φ (x, g x)) x₀ := by
  obtain ⟨r, hr, h⟩ := hx
  rw [marginalPenalty_singleton] at hr
  refine ⟨r, hr, fun ε hε ↦ ?_⟩
  have hK1 : (0 : ℝ) < 1 + K := by positivity
  have hT : Tendsto (fun z ↦ (z, g z)) (𝓝 x₀) (𝓝 (x₀, g x₀)) :=
    (continuousAt_id.prodMk (hg.continuousOn.continuousAt hU)).tendsto
  filter_upwards [hT.eventually (h (ε / (1 + K)) (div_pos hε hK1)), hU] with z hz hzU
  rw [marginalPenalty_singleton] at hz
  refine le_trans (EReal.coe_le_coe_iff.2 ?_) hz
  have hgd : ‖g z - g x₀‖ ≤ K * ‖z - x₀‖ := by
    rw [← dist_eq_norm, ← dist_eq_norm]; exact hg.dist_le_mul _ hzU _ (mem_of_mem_nhds hU)
  have hn : ‖(z, g z) - (x₀, g x₀)‖ ≤ (1 + K) * ‖z - x₀‖ := by
    rw [Prod.mk_sub_mk]
    refine norm_prod_le_iff.2 ⟨?_, ?_⟩ <;> nlinarith [norm_nonneg (z - x₀), NNReal.coe_nonneg K]
  have : ε / (1 + K) * ‖(z, g z) - (x₀, g x₀)‖ ≤ ε * ‖z - x₀‖ := by
    calc ε / (1 + K) * ‖(z, g z) - (x₀, g x₀)‖ ≤ ε / (1 + K) * ((1 + K) * ‖z - x₀‖) := by gcongr
      _ = ε * ‖z - x₀‖ := by field_simp
  simp only [Prod.mk_sub_mk, ContinuousLinearMap.coprod_apply, zero_apply, add_zero] at this ⊢
  linarith

/-- The graph of a mapping of class `C¹` around `x₀` is normally regular at `(x₀, g x₀)`
(Prop. 1.12 of [Mordukhovich 2018]: `D*g(x₀) = D̂*g(x₀) = ∇g(x₀)*`). -/
theorem normallyRegularAt_graph_of_hasFDerivAt {g' : E → E →L[ℝ] F}
    (hgd : ∀ᶠ x in 𝓝 x₀, HasFDerivAt g (g' x) x) (hgc : ContinuousAt g' x₀) :
    NormallyRegularAt (graph fun x ↦ ({g x} : Set F)) (x₀, g x₀) := by
  refine subset_antisymm (fun ℓ hℓ ↦ ?_) regularNormalCone_subset_normalCone
  set u := ℓ.comp (ContinuousLinearMap.inl ℝ E F)
  set v := -ℓ.comp (ContinuousLinearMap.inr ℝ E F)
  have hℓeq : ℓ = u.coprod (-v) := by
    simp only [u, v, neg_neg, ContinuousLinearMap.coprod_comp_inl_inr]
  have hu : u ∈ coderiv (fun x ↦ ({g x} : Set F)) x₀ (g x₀) v := by
    show u.coprod (-v) ∈ normalCone _ _
    rwa [← hℓeq]
  rw [coderiv_of_hasFDerivAt_of_continuousAt hgd hgc] at hu
  have hu' : u ∈ regularCoderiv (fun x ↦ ({g x} : Set F)) x₀ (g x₀) v := by
    rw [regularCoderiv_of_hasFDerivAt hgd.self_of_nhds]; exact hu
  rw [hℓeq]
  exact hu'

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- Thm. 4.5(i) of [Mordukhovich 2018], equality in (4.10) for a lower regular outer function:
if `φ` is lower regular at `(x₀, g x₀)` with epigraph locally closed around `((x₀, g x₀), r)`,
`g` is of class `C¹` around `x₀`, and (4.3) holds, then
`∂(φ ∘ (I, g))(x₀) = ⋃_{(u, v) ∈ ∂φ(x₀, g x₀)} [u + ∂⟨v, g⟩(x₀)]` and `φ ∘ (I, g)` is lower
regular at `x₀`. -/
theorem generalComp_eq_of_lowerRegularAt {g' : E → E →L[ℝ] F}
    (hgd : ∀ᶠ x in 𝓝 x₀, HasFDerivAt g (g' x) x) (hgc : ContinuousAt g' x₀)
    (hr : φ (x₀, g x₀) = r)
    (hφ : ∃ ρ > 0, IsClosed (φ.Epi univ ∩ closedBall (((x₀, g x₀), r) : (E × F) × ℝ) ρ))
    (hqc : ∀ w ∈ singularSubdiff φ (x₀, g x₀),
      -w ∈ normalCone (graph fun x ↦ ({g x} : Set F)) (x₀, g x₀) → w = 0)
    (hreg : LowerRegularAt φ (x₀, g x₀)) :
    subdiff (fun x ↦ φ (x, g x)) x₀ =
        {x | ∃ u v, u.coprod v ∈ subdiff φ (x₀, g x₀) ∧
          x - u ∈ subdiff (fun x ↦ ((v (g x) : ℝ) : EReal)) x₀} ∧
      LowerRegularAt (fun x ↦ φ (x, g x)) x₀ := by
  obtain ⟨K, U, hU, hg⟩ :=
    (hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt hgd hgc).exists_lipschitzOnWith
  have hδreg : LowerRegularAt (graph fun x ↦ ({g x} : Set F)).convex_indicator (x₀, g x₀) := by
    unfold LowerRegularAt
    rw [subdiff_convex_indicator, regularSubdiff_convex_indicator]
    exact normallyRegularAt_graph_of_hasFDerivAt hgd hgc
  obtain ⟨hsum, hϑreg⟩ := subdiff_add_eq (φ₁ := φ)
    (φ₂ := (graph fun x ↦ ({g x} : Set F)).convex_indicator) hr
    (convex_indicator_of_mem (show (x₀, g x₀) ∈ graph fun x ↦ ({g x} : Set F) from rfl)) hφ
    (locallyClosed_epi_convex_indicator (locallyClosed_graph_of_continuousOn hU hg.continuousOn))
    (by simpa [singularSubdiff_convex_indicator] using hqc) hreg hδreg
  have h1 := (subdiff_generalComp_eq_penalty hU hg hr hφ).le
  have h2 : {x | x.coprod (0 : StrongDual ℝ F) ∈
      subdiff (marginalPenalty φ fun x ↦ ({g x} : Set F)) (x₀, g x₀)} ⊆
      regularSubdiff (fun x ↦ φ (x, g x)) x₀ := fun x hx ↦
    mem_regularSubdiff_generalComp_of_coprod_zero_mem hU hg (by
      have : x.coprod (0 : StrongDual ℝ F) ∈ subdiff (fun p ↦ φ p +
        (graph fun x ↦ ({g x} : Set F)).convex_indicator p) (x₀, g x₀) := hx
      rw [hϑreg] at this
      exact this)
  refine ⟨?_, subset_antisymm (h1.trans h2) regularSubdiff_subset_subdiff⟩
  rw [subdiff_generalComp_eq_penalty hU hg hr hφ]
  ext x
  simp only [mem_ofPred_eq]
  rw [show subdiff (marginalPenalty φ fun x ↦ ({g x} : Set F)) (x₀, g x₀) = _ from hsum,
    subdiff_convex_indicator]
  constructor
  · intro h
    obtain ⟨u, v, huv, hxu⟩ := exists_coprod_of_mem_add_normalCone_graph h
    exact ⟨u, v, huv, by rwa [subdiff_comp_eq_coderiv hU hg]⟩
  · rintro ⟨u, v, huv, hxu⟩
    rw [subdiff_comp_eq_coderiv hU hg] at hxu
    exact Set.mem_add.2 ⟨u.coprod v, huv, (x - u).coprod (-v), hxu, by ext <;> simp⟩

omit [FiniteDimensional ℝ F] in
/-- Thm. 4.5(i) of [Mordukhovich 2018], equality in (4.10) for a `C¹` outer function: if
`φ : E × F → ℝ` is of class `C¹` around `(x₀, g x₀)` and `g` is Lipschitz around `x₀`, then
`∂(φ ∘ (I, g))(x₀) = ⋃_{(u, v) ∈ ∂φ(x₀, g x₀)} [u + ∂⟨v, g⟩(x₀)]`, where
`∂φ(x₀, g x₀) = {∇φ(x₀, g x₀)}`. This is also a consequence of Thm. 4.5(ii)
(`subdiff_comp_strict_eq`), which is how it is proved here. -/
theorem generalComp_eq_of_hasFDerivAt (hU : U ∈ 𝓝 x₀) (hg : LipschitzOnWith K g U)
    {f : E × F → ℝ} {f' : E × F → StrongDual ℝ (E × F)}
    (hfd : ∀ᶠ p in 𝓝 (x₀, g x₀), HasFDerivAt f (f' p) p) (hfc : ContinuousAt f' (x₀, g x₀)) :
    subdiff (fun x ↦ ((f (x, g x) : ℝ) : EReal)) x₀ =
      {x | ∃ u v, u.coprod v ∈ subdiff (fun p ↦ (f p : EReal)) (x₀, g x₀) ∧
        x - u ∈ subdiff (fun x ↦ ((v (g x) : ℝ) : EReal)) x₀} := by
  rw [subdiff_of_hasFDerivAt_of_continuousAt hfd hfc, subdiff_comp_strict_eq hU hg
    (hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt hfd hfc)]
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨(f' (x₀, g x₀)).comp (ContinuousLinearMap.inl ℝ E F),
      (f' (x₀, g x₀)).comp (ContinuousLinearMap.inr ℝ E F), ?_, by simpa using hw⟩
    rw [ContinuousLinearMap.coprod_comp_inl_inr]; rfl
  · rintro ⟨u, v, huv, hxu⟩
    rw [mem_singleton_iff] at huv
    have hu : u = (f' (x₀, g x₀)).comp (ContinuousLinearMap.inl ℝ E F) := by rw [← huv]; ext; simp
    have hv : v = (f' (x₀, g x₀)).comp (ContinuousLinearMap.inr ℝ E F) := by rw [← huv]; ext; simp
    subst hu hv
    exact ⟨_, hxu, add_sub_cancel _ _⟩

end Regularity

end VariationalAnalysis
