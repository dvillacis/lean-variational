/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import Mathlib.Analysis.Normed.Ring.Units
import VariationalAnalysis.Coderivative.Variational
import VariationalAnalysis.Subdifferential.SmoothChain
import VariationalAnalysis.WellPosedness.Criterion

/-!
# Metric regularity of parametric variational systems

Coderivative conditions for metric regularity of the solution map
`S(x) = {y | 0 ∈ f(x, y) + Q(y)}` of the parametric variational system (3.34)
[Mordukhovich 2018, Section 3.3.2], combining Thm. 3.3(ii) with the coderivative formulas of
Props. 3.16, 3.18 and 3.19 (`VariationalAnalysis.Coderivative.Variational`).

Throughout, `f` is of class `C¹` around `(x₀, y₀)` (strict derivatives `Df p` near `(x₀, y₀)`,
`Df` continuous at `(x₀, y₀)`) with `∇ₓf(x₀, y₀)` onto, and all spaces are finite-dimensional.
The book's standing assumption that `gph Q` is closed enters as local closedness of `gph Q`
around `(y₀, -f(x₀, y₀))`; it gives the local closedness of `gph S`
(`locallyClosed_graph_pvsSolutionMap`), which is what Thm. 3.3 needs. For the subdifferential
systems, local closedness of `gph ∂ψ` (resp. `gph ∂θ`) gives that of the field
(`locallyClosed_graph_subdiff_comp`, via the chain rule of Exercise 1.72; resp. a preimage under
`(y, q) ↦ (g y, q)`).

## Main results

* `metricallyRegularAt_pvsSolutionMap_iff`,
  `metricallyRegularAt_pvsSolutionMap_iff_lipschitzLikeAt`, `regBound_pvsSolutionMap`:
  Thm. 3.20 of [Mordukhovich 2018], (3.54)–(3.55) (the bound is stated as a supremum; the
  attainment claimed by the book is not formalized).
* `metricallyRegularAt_pvsSolutionMap_compositePotential_iff`: Cor. 3.21.
* `metricallyRegularAt_pvsSolutionMap_compositeField_iff`: Cor. 3.22.
* Auxiliary: `locallyClosed_preimage_of_continuousAt`, `locallyClosed_graph_pvsSolutionMap`,
  `locallyClosed_graph_subdiff_comp`.
-/

open Filter Topology Set Metric ContinuousLinearMap
open scoped NNReal ENNReal

namespace VariationalAnalysis

section Preimage

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- Local closedness pulls back along maps continuous around the point: if `Θ` is locally closed
around `g p₀` and `g` is continuous at every point near `p₀`, then `g⁻¹(Θ)` is locally closed
around `p₀`. -/
theorem locallyClosed_preimage_of_continuousAt {g : X → Y} {Θ : Set Y} {p₀ : X}
    (hg : ∀ᶠ p in 𝓝 p₀, ContinuousAt g p) (hΘ : ∃ ρ > 0, IsClosed (Θ ∩ closedBall (g p₀) ρ)) :
    ∃ ρ > 0, IsClosed (g ⁻¹' Θ ∩ closedBall p₀ ρ) := by
  obtain ⟨ρ, hρ, hcl⟩ := hΘ
  have hball : ∀ᶠ p in 𝓝 p₀, dist (g p) (g p₀) < ρ :=
    (hg.self_of_nhds.tendsto).eventually (ball_mem_nhds _ hρ)
  obtain ⟨δ, hδ, hsub⟩ := nhds_basis_closedBall.mem_iff.1 (hg.and hball)
  refine ⟨δ, hδ, ?_⟩
  have hc : ContinuousOn g (closedBall p₀ δ) := fun p hp ↦ (hsub hp).1.continuousWithinAt
  have : g ⁻¹' Θ ∩ closedBall p₀ δ = closedBall p₀ δ ∩ g ⁻¹' (Θ ∩ closedBall (g p₀) ρ) := by
    ext p
    simp only [mem_inter_iff, mem_preimage, mem_closedBall]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1, (hsub (mem_closedBall.2 h2)).2.le⟩
    · rintro ⟨h1, h2, -⟩
      exact ⟨h2, h1⟩
  rw [this]
  exact hc.preimage_isClosed_of_isClosed isClosed_closedBall hcl

end Preimage

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

section General

variable {f : E × F → G} {Df : E × F → E × F →L[ℝ] G} {Q : F → Set G} {x₀ : E} {y₀ : F}

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G] in
/-- [Mordukhovich 2018, proof of Thm. 3.20]: the graph of the solution map `S` of (3.34) is
locally closed around `(x₀, y₀)` when `gph Q` is locally closed around `(y₀, -f(x₀, y₀))` and
`f` is continuous around `(x₀, y₀)`, since `gph S = g⁻¹(gph Q)` for `g(x, y) = (y, -f(x, y))`. -/
theorem locallyClosed_graph_pvsSolutionMap (hf : ∀ᶠ p in 𝓝 (x₀, y₀), ContinuousAt f p)
    (hQ : ∃ ρ > 0, IsClosed (graph Q ∩ closedBall (y₀, -f (x₀, y₀)) ρ)) :
    ∃ ρ > 0, IsClosed (graph (pvsSolutionMap f Q) ∩ closedBall (x₀, y₀) ρ) := by
  rw [graph_pvsSolutionMap]
  exact locallyClosed_preimage_of_continuousAt (g := fun p : E × F ↦ (p.2, -f p))
    (hf.mono fun p hp ↦ continuousAt_snd.prodMk hp.neg) hQ

end General

section Thm320

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G]
variable {f : E × F → G} {Df : E × F → E × F →L[ℝ] G} {Q : F → Set G} {x₀ : E} {y₀ : F}

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ F] [FiniteDimensional ℝ G] in
/-- `-T = {0}` iff `T = {0}`. -/
theorem neg_eq_zero_set_iff {T : Set G} : -T = {0} ↔ T = {0} := by
  constructor <;> intro h
  · rw [← neg_neg T, h, neg_singleton, neg_zero]
  · rw [h, neg_singleton, neg_zero]

/-- Thm. 3.20 of [Mordukhovich 2018] (metric regularity of general PVS): let `f` be of class `C¹`
around `(x₀, y₀) ∈ gph S` with `∇ₓf(x₀, y₀)` onto, and let `gph Q` be locally closed around
`(y₀, z₀)`, `z₀ = -f(x₀, y₀)`. Then the solution map `S` of (3.34) is metrically regular around
`(x₀, y₀)` iff `D*Q(y₀, z₀)(0) = {0}` (3.54). -/
theorem metricallyRegularAt_pvsSolutionMap_iff
    (hf : ∀ᶠ p in 𝓝 (x₀, y₀), HasStrictFDerivAt f (Df p) p) (hDf : ContinuousAt Df (x₀, y₀))
    (hsurj : Function.Surjective ((Df (x₀, y₀)).comp (inl ℝ E F)))
    (hQ : ∃ ρ > 0, IsClosed (graph Q ∩ closedBall (y₀, -f (x₀, y₀)) ρ))
    (h₀ : y₀ ∈ pvsSolutionMap f Q x₀) :
    MetricallyRegularAt (pvsSolutionMap f Q) x₀ y₀ ↔ coderiv Q y₀ (-f (x₀, y₀)) 0 = {0} := by
  rw [metricallyRegularAt_iff_coderivKer_eq (locallyClosed_graph_pvsSolutionMap
    (hf.mono fun p hp ↦ hp.continuousAt) hQ) h₀, coderivKer_pvsSolutionMap hf hDf hsurj,
    neg_eq_zero_set_iff]

/-- Thm. 3.20 of [Mordukhovich 2018]: under the assumptions of
`metricallyRegularAt_pvsSolutionMap_iff`, the solution map `S` is metrically regular around
`(x₀, y₀)` iff the field `Q` is Lipschitz-like around `(y₀, -f(x₀, y₀))`. -/
theorem metricallyRegularAt_pvsSolutionMap_iff_lipschitzLikeAt
    (hf : ∀ᶠ p in 𝓝 (x₀, y₀), HasStrictFDerivAt f (Df p) p) (hDf : ContinuousAt Df (x₀, y₀))
    (hsurj : Function.Surjective ((Df (x₀, y₀)).comp (inl ℝ E F)))
    (hQ : ∃ ρ > 0, IsClosed (graph Q ∩ closedBall (y₀, -f (x₀, y₀)) ρ))
    (h₀ : y₀ ∈ pvsSolutionMap f Q x₀) :
    MetricallyRegularAt (pvsSolutionMap f Q) x₀ y₀ ↔ LipschitzLikeAt Q y₀ (-f (x₀, y₀)) := by
  rw [metricallyRegularAt_pvsSolutionMap_iff hf hDf hsurj hQ h₀,
    lipschitzLikeAt_iff_coderiv_zero_eq hQ h₀]

/-- Thm. 3.20 of [Mordukhovich 2018], exact regularity bound (3.55): under the assumptions of
`metricallyRegularAt_pvsSolutionMap_iff`,
`reg S (x₀, y₀) = sup {‖y*‖ | ∃ z*, ‖∇ₓf(x₀, y₀)* z*‖ ≤ 1, -y* ∈ ∇ᵧf(x₀, y₀)* z* + D*Q(y₀, z₀)(z*)}`
(the book writes `max`; attainment is not formalized). -/
theorem regBound_pvsSolutionMap
    (hf : ∀ᶠ p in 𝓝 (x₀, y₀), HasStrictFDerivAt f (Df p) p) (hDf : ContinuousAt Df (x₀, y₀))
    (hsurj : Function.Surjective ((Df (x₀, y₀)).comp (inl ℝ E F)))
    (hQ : ∃ ρ > 0, IsClosed (graph Q ∩ closedBall (y₀, -f (x₀, y₀)) ρ))
    (h₀ : y₀ ∈ pvsSolutionMap f Q x₀) :
    regBound (pvsSolutionMap f Q) x₀ y₀ =
      ⨆ (y' : StrongDual ℝ F) (_ : ∃ z' : StrongDual ℝ G,
          ‖z'.comp ((Df (x₀, y₀)).comp (inl ℝ E F))‖ ≤ 1 ∧
          -y' - z'.comp ((Df (x₀, y₀)).comp (inr ℝ E F)) ∈ coderiv Q y₀ (-f (x₀, y₀)) z'),
        (‖y'‖₊ : ℝ≥0∞) := by
  rw [regBound_eq_posHomNorm_invMap_coderiv (locallyClosed_graph_pvsSolutionMap
    (hf.mono fun p hp ↦ hp.continuousAt) hQ) h₀]
  refine le_antisymm (iSup₂_le fun x' hx' ↦ iSup₂_le fun y' hy' ↦ ?_)
    (iSup₂_le fun y' ⟨z', hz1, hz2⟩ ↦ ?_)
  · obtain ⟨z', rfl, hz⟩ := (mem_coderiv_pvsSolutionMap_iff hf hDf hsurj).1 hy'
    exact le_iSup₂_of_le (f := fun (y' : StrongDual ℝ F) (_ : ∃ z' : StrongDual ℝ G,
        ‖z'.comp ((Df (x₀, y₀)).comp (inl ℝ E F))‖ ≤ 1 ∧
        -y' - z'.comp ((Df (x₀, y₀)).comp (inr ℝ E F)) ∈ coderiv Q y₀ (-f (x₀, y₀)) z') ↦
        (‖y'‖₊ : ℝ≥0∞)) y' ⟨z', hx', hz⟩ le_rfl
  · exact nnnorm_le_posHomNorm hz1
      ((mem_coderiv_pvsSolutionMap_iff hf hDf hsurj).2 ⟨z', rfl, hz2⟩)

end Thm320

section Composite

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] in
/-- For an injective map `L` with `L 0 = 0` and `0 ∈ T`: `L '' T = {0}` iff `T = {0}`. -/
theorem image_eq_zero_iff {α β : Type*} [Zero α] [Zero β] {L : α → β} (hL : Function.Injective L)
    (hL0 : L 0 = 0) {T : Set α} : L '' T = {0} ↔ T = {0} := by
  constructor
  · intro h
    refine subset_antisymm (fun t ht ↦ ?_) (fun t ht ↦ ?_)
    · have : L t ∈ L '' T := mem_image_of_mem L ht
      rw [h, mem_singleton_iff, ← hL0] at this
      exact hL this
    · have : (0 : β) ∈ L '' T := by rw [h]; rfl
      obtain ⟨t', ht', hLt'⟩ := this
      rw [mem_singleton_iff.1 ht, ← hL (hLt'.trans hL0.symm)]
      exact ht'
  · rintro rfl
    rw [image_singleton, hL0]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] in
/-- [Mordukhovich 2018, proof of Cor. 3.21]: if `g` is of class `C¹` around `y₀` with `∇g(y₀)`
onto and `gph ∂ψ` is locally closed around `(g y₀, v₀)`, then `gph ∂(ψ ∘ g)` is locally closed
around `(y₀, ∇g(y₀)* v₀)`. Near `y₀`, `∂(ψ ∘ g)(y) = ∇g(y)* ∂ψ(g y)` (Exercise 1.72) and the
subgradient `v` with `q = ∇g(y)* v` depends continuously on `(y, q)`:
`v = q ∘ R ∘ (∇g(y) ∘ R)⁻¹` for a right inverse `R` of `∇g(y₀)`. -/
theorem locallyClosed_graph_subdiff_comp [FiniteDimensional ℝ F] [FiniteDimensional ℝ W]
    {ψ : W → EReal} {g : F → W} {Dg : F → F →L[ℝ] W} {y₀ : F} {v₀ : StrongDual ℝ W}
    (hg : ∀ᶠ y in 𝓝 y₀, HasStrictFDerivAt g (Dg y) y) (hDg : ∀ᶠ y in 𝓝 y₀, ContinuousAt Dg y)
    (hA : Function.Surjective (Dg y₀))
    (hloc : ∃ ρ > 0, IsClosed (graph (subdiff ψ) ∩ closedBall (g y₀, v₀) ρ)) :
    ∃ ρ > 0, IsClosed (graph (fun y ↦ subdiff (fun y ↦ ψ (g y)) y) ∩
      closedBall (y₀, v₀.comp (Dg y₀)) ρ) := by
  obtain ⟨ρ, hρ, hcl⟩ := hloc
  obtain ⟨R, hR⟩ := (Dg y₀).exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hA)
  set M : F → W →L[ℝ] W := fun y ↦ (Dg y).comp R with hM_def
  have hM₀ : M y₀ = 1 := hR
  have hMc : ∀ᶠ y in 𝓝 y₀, ContinuousAt M y := hDg.mono fun y hy ↦ hy.clm_comp continuousAt_const
  have hunit : ∀ᶠ y in 𝓝 y₀, IsUnit (M y) :=
    hMc.self_of_nhds.eventually (by rw [hM₀]; exact Units.nhds (1 : (W →L[ℝ] W)ˣ))
  set N : Set F := {y | (∀ᶠ y' in 𝓝 y, HasStrictFDerivAt g (Dg y') y') ∧ ContinuousAt Dg y ∧
    ContinuousAt M y ∧ IsUnit (M y)} with hN_def
  have hN : N ∈ 𝓝 y₀ := hg.eventually_nhds.and (hDg.and (hMc.and hunit))
  set Φ : F × StrongDual ℝ F → StrongDual ℝ W := fun p ↦ p.2.comp (R.comp (Ring.inverse (M p.1)))
    with hΦ_def
  have hΦcomp : ∀ y ∈ N, ∀ v : StrongDual ℝ W, Φ (y, v.comp (Dg y)) = v := by
    intro y hy v
    have h1 := Ring.mul_inverse_cancel (M y) hy.2.2.2
    rw [mul_def] at h1
    have h2 : (Dg y).comp (R.comp (Ring.inverse (M y))) = 1 := by rw [← comp_assoc]; exact h1
    show (v.comp (Dg y)).comp (R.comp (Ring.inverse (M y))) = v
    rw [comp_assoc, h2, one_def, comp_id]
  have hsurj : ∀ y ∈ N, Function.Surjective (Dg y) := by
    intro y hy w
    refine ⟨R (Ring.inverse (M y) w), ?_⟩
    have := congrArg (fun T : W →L[ℝ] W ↦ T w) (Ring.mul_inverse_cancel (M y) hy.2.2.2)
    simpa [mul_def, hM_def] using this
  have key : ∀ p : F × StrongDual ℝ F, p.1 ∈ N →
      (p ∈ graph (fun y ↦ subdiff (fun y ↦ ψ (g y)) y) ↔
        Φ p ∈ subdiff ψ (g p.1) ∧ p.2 = (Φ p).comp (Dg p.1)) := by
    rintro ⟨y, q⟩ hy
    show q ∈ subdiff (fun y ↦ ψ (g y)) y ↔ _
    rw [subdiff_comp_of_surjective hy.1 hy.2.1 (hsurj y hy)]
    constructor
    · rintro ⟨v, hv, hvq⟩
      dsimp only at hvq
      subst hvq
      rw [hΦcomp y hy v]
      exact ⟨hv, rfl⟩
    · rintro ⟨h1, h2⟩
      exact ⟨_, h1, h2.symm⟩
  set p₀ : F × StrongDual ℝ F := (y₀, v₀.comp (Dg y₀)) with hp₀_def
  set Ψ : F × StrongDual ℝ F → (W × StrongDual ℝ W) × (StrongDual ℝ F × StrongDual ℝ F) :=
    fun p ↦ ((g p.1, Φ p), (p.2, (Φ p).comp (Dg p.1))) with hΨ_def
  have hNp : {p : F × StrongDual ℝ F | p.1 ∈ N} ∈ 𝓝 p₀ :=
    continuousAt_fst.preimage_mem_nhds hN
  have hΨc : ∀ᶠ p in 𝓝 p₀, ContinuousAt Ψ p := by
    filter_upwards [hNp] with p hp
    obtain ⟨hgy, hDgy, hMy, hu⟩ := hp
    have hinv : ContinuousAt Ring.inverse (M p.1) := by
      have := NormedRing.inverse_continuousAt hu.unit
      rwa [hu.unit_spec] at this
    have hΦc : ContinuousAt Φ p :=
      continuousAt_snd.clm_comp (continuousAt_const.clm_comp
        ((hinv.comp hMy).comp continuousAt_fst))
    exact (((hgy.self_of_nhds.continuousAt).comp continuousAt_fst).prodMk hΦc).prodMk
      (continuousAt_snd.prodMk (hΦc.clm_comp (hDgy.comp continuousAt_fst)))
  have hΨ₀ : Ψ p₀ = ((g y₀, v₀), (v₀.comp (Dg y₀), v₀.comp (Dg y₀))) := by
    simp only [hΨ_def, hp₀_def, hΦcomp y₀ (mem_of_mem_nhds hN) v₀]
  set Θ : Set ((W × StrongDual ℝ W) × (StrongDual ℝ F × StrongDual ℝ F)) :=
    graph (subdiff ψ) ×ˢ diagonal (StrongDual ℝ F) with hΘ_def
  have hΘ : ∃ ρ > 0, IsClosed (Θ ∩ closedBall (Ψ p₀) ρ) := by
    refine ⟨ρ, hρ, ?_⟩
    rw [hΨ₀]
    have : Θ ∩ closedBall ((g y₀, v₀), (v₀.comp (Dg y₀), v₀.comp (Dg y₀))) ρ =
        (graph (subdiff ψ) ∩ closedBall (g y₀, v₀) ρ) ×ˢ
          (diagonal (StrongDual ℝ F) ∩ closedBall (v₀.comp (Dg y₀), v₀.comp (Dg y₀)) ρ) := by
      ext ⟨a, b⟩
      simp only [hΘ_def, mem_inter_iff, mem_prod, mem_closedBall, Prod.dist_eq (x := (a, b)),
        max_le_iff]
      tauto
    rw [this]
    exact hcl.prod (isClosed_diagonal.inter isClosed_closedBall)
  obtain ⟨δ₁, hδ₁, hcl₁⟩ := locallyClosed_preimage_of_continuousAt hΨc hΘ
  obtain ⟨δ₂, hδ₂, hsub⟩ := nhds_basis_closedBall.mem_iff.1 hNp
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  have : graph (fun y ↦ subdiff (fun y ↦ ψ (g y)) y) ∩ closedBall p₀ (min δ₁ δ₂) =
      (Ψ ⁻¹' Θ ∩ closedBall p₀ δ₁) ∩ closedBall p₀ (min δ₁ δ₂) := by
    ext p
    simp only [mem_inter_iff]
    constructor
    · rintro ⟨hp, hpb⟩
      have hpN : p.1 ∈ N := hsub (closedBall_subset_closedBall (min_le_right _ _) hpb)
      obtain ⟨h1, h2⟩ := (key p hpN).1 hp
      exact ⟨⟨⟨h1, h2⟩, closedBall_subset_closedBall (min_le_left _ _) hpb⟩, hpb⟩
    · rintro ⟨⟨⟨h1, h2⟩, -⟩, hpb⟩
      have hpN : p.1 ∈ N := hsub (closedBall_subset_closedBall (min_le_right _ _) hpb)
      exact ⟨(key p hpN).2 ⟨h1, h2⟩, hpb⟩
  rw [this]
  exact hcl₁.inter isClosed_closedBall

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ W] {x₀ : E} {y₀ : F}

/-- Cor. 3.22 of [Mordukhovich 2018] (metric regularity of subdifferential PVS with composite
fields): in the setting of Prop. 3.19(i) (`f` of class `C¹` with `∇ₓf(x₀, y₀)` onto, `g` of
class `C¹` with `∇g(y₀)` onto), with `q₀ = -f(x₀, y₀)` and `gph ∂θ` locally closed around
`(g y₀, q₀)`, the solution map `S(x) = {y | 0 ∈ f(x, y) + ∂θ(g y)}` is metrically regular
around `(x₀, y₀) ∈ gph S` iff `∂θ` is Lipschitz-like around `(g y₀, q₀)`. -/
theorem metricallyRegularAt_pvsSolutionMap_compositeField_iff {f : E × F → StrongDual ℝ W}
    {Df : E × F → E × F →L[ℝ] StrongDual ℝ W} {θ : W → EReal} {g : F → W}
    {Dg : F → F →L[ℝ] W} (hf : ∀ᶠ p in 𝓝 (x₀, y₀), HasStrictFDerivAt f (Df p) p)
    (hDf : ContinuousAt Df (x₀, y₀)) (hsurj : Function.Surjective ((Df (x₀, y₀)).comp (inl ℝ E F)))
    (hg : ∀ᶠ y in 𝓝 y₀, HasStrictFDerivAt g (Dg y) y) (hDg : ContinuousAt Dg y₀)
    (hA : Function.Surjective (Dg y₀))
    (hloc : ∃ ρ > 0, IsClosed (graph (subdiff θ) ∩ closedBall (g y₀, -f (x₀, y₀)) ρ))
    (h₀ : y₀ ∈ pvsSolutionMap f (fun y ↦ subdiff θ (g y)) x₀) :
    MetricallyRegularAt (pvsSolutionMap f fun y ↦ subdiff θ (g y)) x₀ y₀ ↔
      LipschitzLikeAt (subdiff θ) (g y₀) (-f (x₀, y₀)) := by
  have hQ : ∃ ρ > 0, IsClosed (graph (fun y ↦ subdiff θ (g y)) ∩
      closedBall (y₀, -f (x₀, y₀)) ρ) :=
    locallyClosed_preimage_of_continuousAt (g := fun p : F × StrongDual ℝ W ↦ (g p.1, p.2))
      (p₀ := (y₀, -f (x₀, y₀)))
      (((continuous_fst.tendsto (y₀, -f (x₀, y₀))).eventually hg).mono fun p hp ↦
        (hp.continuousAt.comp continuousAt_fst).prodMk continuousAt_snd) hloc
  rw [metricallyRegularAt_iff_coderivKer_eq (locallyClosed_graph_pvsSolutionMap
    (hf.mono fun p hp ↦ hp.continuousAt) hQ) h₀,
    coderivKer_pvsSolutionMap_compositeField hf hDf hsurj hg hDg hA, neg_eq_zero_set_iff,
    image_eq_zero_iff (comp_injective_of_surjective hA) (zero_comp _),
    lipschitzLikeAt_iff_coderiv_zero_eq hloc h₀, secondOrderSubdiff, map_zero]

/-- Cor. 3.21 of [Mordukhovich 2018] (metric regularity of subdifferential PVS with composite
potentials): in the setting of Prop. 3.18 (`f` of class `C¹` with `∇ₓf(x₀, y₀)` onto, `g` of
class `C²` with `∇g(y₀)` onto, `-f(x₀, y₀) = ∇g(y₀)* v₀`), with `gph ∂ψ` locally closed around
`(g y₀, v₀)`, the solution map `S(x) = {y | 0 ∈ f(x, y) + ∂(ψ ∘ g)(y)}` is metrically regular
around `(x₀, y₀) ∈ gph S` iff `∂ψ` is Lipschitz-like around `(g y₀, v₀)`. -/
theorem metricallyRegularAt_pvsSolutionMap_compositePotential_iff {f : E × F → StrongDual ℝ F}
    {Df : E × F → E × F →L[ℝ] StrongDual ℝ F} {ψ : W → EReal} {g : F → W}
    {Dg : F → F →L[ℝ] W} {D2g : F → F →L[ℝ] F →L[ℝ] W} {v₀ : StrongDual ℝ W}
    (hf : ∀ᶠ p in 𝓝 (x₀, y₀), HasStrictFDerivAt f (Df p) p) (hDf : ContinuousAt Df (x₀, y₀))
    (hsurj : Function.Surjective ((Df (x₀, y₀)).comp (inl ℝ E F)))
    (hg : ∀ᶠ y in 𝓝 y₀, HasStrictFDerivAt g (Dg y) y)
    (hDg : ∀ᶠ y in 𝓝 y₀, HasStrictFDerivAt Dg (D2g y) y) (hD2c : ContinuousAt D2g y₀)
    (hA : Function.Surjective (Dg y₀)) (hq : -f (x₀, y₀) = v₀.comp (Dg y₀))
    (hloc : ∃ ρ > 0, IsClosed (graph (subdiff ψ) ∩ closedBall (g y₀, v₀) ρ))
    (h₀ : y₀ ∈ pvsSolutionMap f (fun y ↦ subdiff (fun y ↦ ψ (g y)) y) x₀) :
    MetricallyRegularAt (pvsSolutionMap f fun y ↦ subdiff (fun y ↦ ψ (g y)) y) x₀ y₀ ↔
      LipschitzLikeAt (subdiff ψ) (g y₀) v₀ := by
  have hDgc : ∀ᶠ y in 𝓝 y₀, ContinuousAt Dg y := hDg.mono fun y hy ↦ hy.continuousAt
  have hQ := locallyClosed_graph_subdiff_comp hg hDgc hA hloc
  rw [← hq] at hQ
  have hv₀ : v₀ ∈ subdiff ψ (g y₀) := by
    have : -f (x₀, y₀) ∈ subdiff (fun y ↦ ψ (g y)) y₀ := h₀
    rwa [hq, comp_mem_subdiff_comp_iff_of_surjective hg hDgc.self_of_nhds hA] at this
  rw [metricallyRegularAt_iff_coderivKer_eq (locallyClosed_graph_pvsSolutionMap
    (hf.mono fun p hp ↦ hp.continuousAt) hQ) h₀,
    coderivKer_pvsSolutionMap_compositePotential hf hDf hsurj hg hDg hD2c hA hq,
    neg_eq_zero_set_iff, image_eq_zero_iff (comp_injective_of_surjective hA) (zero_comp _),
    lipschitzLikeAt_iff_coderiv_zero_eq hloc hv₀, secondOrderSubdiff, map_zero]

end Composite

end VariationalAnalysis
