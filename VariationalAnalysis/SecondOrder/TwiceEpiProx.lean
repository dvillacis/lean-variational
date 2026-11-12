/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis.SecondOrder.EpiAnalytic
import VariationalAnalysis.SecondOrder.SecondSubderiv

/-!
# Twice epi-differentiability and proximal mappings

This file starts the proof of [Mordukhovich 2024, Thm. 1.98]: for a function `φ` with `φ(0) = 0`
and `φ ≥ -(r/2)‖·‖²` (the normalized form of a prox-regular, prox-bounded function at `x̄ = 0`
for `v̄ = 0`), twice epi-differentiability at `0` for `0` gives the convergence of the difference
quotients `t⁻¹P_λφ(tw)` of the proximal mapping to the proximal mapping of `d²φ(0, 0)/2`.

## Main results

* `twiceEpiDifferentiableAt_iff_epiTendsto`: twice epi-differentiability is the epi-convergence
  of the second-order difference quotients to the second subderivative as `t ↓ 0`.
* `IsSetLimit.image_homeomorph`, `EpiTendsto.coe_mul`: set limits under homeomorphisms and
  epi-limits under positive multiples.
* `TwiceEpiDifferentiableAt.epiTendsto_half`, `half_secondDiffQuot_ge`: the functions
  `Δ²_tφ(0, 0)/2` epi-converge to `d²φ(0, 0)/2` and inherit the quadratic minorant of `φ`.
* `TwiceEpiDifferentiableAt.mem_proximalMap_of_tendsto`: cluster points of `t_k⁻¹p_k` with
  `p_k ∈ P_λφ(t_k w_k)`, `t_k ↓ 0`, `w_k → w`, lie in `P_λ(d²φ(0, 0)/2)(w)`.
* `TwiceEpiDifferentiableAt.tendsto_inv_smul_of_mem_proximalMap`: if `P_λ(d²φ(0, 0)/2)(w)` has
  at most one point `d`, then `t_k⁻¹p_k → d`
  [Mordukhovich 2024, Thm. 1.98 and Cor. 1.101, first part of the proofs].

## Implementation notes

The proof combines [Mordukhovich 2024, Lemma 1.94] (`proximalMap_half_secondDiffQuot`) with
[Mordukhovich 2024, Ex. 1.135] (`EpiTendsto.tendsto_of_mem_proximalMap`). The book assumes
"for simplicity" that the localization of `∂φ` is monotone; we only use the quadratic
minorant.
-/

open Filter Topology Set Metric
open scoped Pointwise

namespace VariationalAnalysis

/-! ### Set limits and epi-limits under homeomorphisms -/

section Image

variable {ι X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {l : Filter ι}
  {S : ι → Set X}

theorem image_outerLimit_subset {f : X → Y} (hf : Continuous f) :
    f '' outerLimit l S ⊆ outerLimit l (fun i ↦ f '' S i) := by
  rintro _ ⟨y, ⟨a, v, ha, hv, hS⟩, rfl⟩
  exact ⟨a, f ∘ v, ha, (hf.tendsto y).comp hv, fun k ↦ mem_image_of_mem f (hS k)⟩

theorem image_innerLimit_subset {f : X → Y} (hf : Continuous f) :
    f '' innerLimit l S ⊆ innerLimit l (fun i ↦ f '' S i) := by
  rintro _ ⟨y, hy, rfl⟩ a ha
  obtain ⟨v, hv, hS⟩ := hy a ha
  exact ⟨f ∘ v, (hf.tendsto y).comp hv, hS.mono fun k hk ↦ mem_image_of_mem f hk⟩

theorem outerLimit_image_homeomorph (e : X ≃ₜ Y) :
    outerLimit l (fun i ↦ e '' S i) = e '' outerLimit l S := by
  refine Subset.antisymm (fun y hy ↦ ?_) (image_outerLimit_subset e.continuous)
  have h := image_outerLimit_subset (l := l) (S := fun i ↦ e '' S i) e.symm.continuous
    (mem_image_of_mem e.symm hy)
  simp only [← image_comp, Homeomorph.symm_comp_self, image_id] at h
  exact ⟨e.symm y, h, e.apply_symm_apply y⟩

theorem innerLimit_image_homeomorph (e : X ≃ₜ Y) :
    innerLimit l (fun i ↦ e '' S i) = e '' innerLimit l S := by
  refine Subset.antisymm (fun y hy ↦ ?_) (image_innerLimit_subset e.continuous)
  have h := image_innerLimit_subset (l := l) (S := fun i ↦ e '' S i) e.symm.continuous
    (mem_image_of_mem e.symm hy)
  simp only [← image_comp, Homeomorph.symm_comp_self, image_id] at h
  exact ⟨e.symm y, h, e.apply_symm_apply y⟩

/-- Set limits are preserved by homeomorphisms. -/
theorem IsSetLimit.image_homeomorph {S₀ : Set X} (h : IsSetLimit l S S₀) (e : X ≃ₜ Y) :
    IsSetLimit l (fun i ↦ e '' S i) (e '' S₀) :=
  ⟨by rw [outerLimit_image_homeomorph, h.1], by rw [innerLimit_image_homeomorph, h.2]⟩

end Image

section TwiceEpi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Epi-limits are preserved by positive multiples. -/
theorem EpiTendsto.coe_mul {ι : Type*} {l : Filter ι} {φ : ι → E → EReal} {φ₀ : E → EReal}
    (h : EpiTendsto l φ φ₀) {c : ℝ} (hc : 0 < c) :
    EpiTendsto l (fun i x ↦ (c : EReal) * φ i x) (fun x ↦ (c : EReal) * φ₀ x) := by
  unfold EpiTendsto
  simp only [epi_coe_mul hc]
  exact h.image_homeomorph (scaleSnd c hc.ne').toHomeomorph

/-- Twice epi-differentiability at `x̄` for `v` [Mordukhovich 2024, Def. 1.89(i)] is the
epi-convergence of the second-order difference quotients `Δ²_tφ(x̄, v)` to the second
subderivative `d²φ(x̄, v)` as `t ↓ 0`. -/
theorem twiceEpiDifferentiableAt_iff_epiTendsto {φ : E → EReal} {x₀ : E}
    {v : StrongDual ℝ E} :
    TwiceEpiDifferentiableAt φ x₀ v ↔ (∃ r : ℝ, φ x₀ = r) ∧
      EpiTendsto (𝓝[>] (0 : ℝ)) (secondDiffQuot φ x₀ v) (secondSubderiv φ x₀ v) := by
  rw [epiTendsto_iff]
  refine and_congr_right fun _ ↦ ⟨fun h w ↦ ⟨le_refl _, fun a ha ↦ (h a ha w).2⟩,
    fun h t ht w ↦ ⟨fun wk hwk ↦ ?_, (h w).2 t ht⟩⟩
  exact liminf_le_liminf_comp (ht.prodMk hwk) _

variable {φ : E → EReal} {m r : ℝ}

/-- If `φ` is twice epi-differentiable at `0` for `0`, the functions `Δ²_tφ(0, 0)/2` epi-converge
to `d²φ(0, 0)/2` as `t ↓ 0`. -/
theorem TwiceEpiDifferentiableAt.epiTendsto_half (H : TwiceEpiDifferentiableAt φ 0 0) :
    EpiTendsto (𝓝[>] (0 : ℝ)) (fun t w ↦ ((1 / 2 : ℝ) : EReal) * secondDiffQuot φ 0 0 t w)
      (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderiv φ 0 0 w) :=
  (twiceEpiDifferentiableAt_iff_epiTendsto.1 H).2.coe_mul (by norm_num)

/-- The functions `Δ²_tφ(0, 0)/2` inherit the quadratic minorant of `φ`. -/
theorem half_secondDiffQuot_ge (h0 : φ 0 = 0)
    (hφ : ∀ x, ((-(r / 2) * ‖x‖ ^ 2 : ℝ) : EReal) ≤ φ x) {t : ℝ} (ht : 0 < t) (w : E) :
    ((-(r / 2) * ‖w‖ ^ 2 : ℝ) : EReal) ≤ ((1 / 2 : ℝ) : EReal) * secondDiffQuot φ 0 0 t w := by
  rw [half_secondDiffQuot_zero h0 ht.ne']
  calc ((-(r / 2) * ‖w‖ ^ 2 : ℝ) : EReal)
      = ((t⁻¹ ^ 2 : ℝ) : EReal) * ((-(r / 2) * ‖t • w‖ ^ 2 : ℝ) : EReal) := by
        rw [← EReal.coe_mul, norm_smul, Real.norm_of_nonneg ht.le]
        congr 1
        field_simp
    _ ≤ ((t⁻¹ ^ 2 : ℝ) : EReal) * φ (t • w) :=
        (coe_mul_le_coe_mul_iff (by positivity)).2 (hφ _)

theorem eventually_half_secondDiffQuot_ge (h0 : φ 0 = 0)
    (hφ : ∀ x, ((-(r / 2) * ‖x‖ ^ 2 : ℝ) : EReal) ≤ φ x) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ w : E, ((-(r / 2) * ‖w‖ ^ 2 : ℝ) : EReal) ≤
      ((1 / 2 : ℝ) : EReal) * secondDiffQuot φ 0 0 t w := by
  filter_upwards [eventually_mem_nhdsWithin] with t ht w
  exact half_secondDiffQuot_ge h0 hφ ht w

/-- The proximal points of `φ` at `t_k w_k`, divided by `t_k`, are proximal points of
`Δ²_{t_k}φ(0, 0)/2` at `w_k` [Mordukhovich 2024, Lemma 1.94]. -/
theorem eventually_inv_smul_mem_proximalMap (h0 : φ 0 = 0) {t : ℕ → ℝ}
    (ht : Tendsto t atTop (𝓝[>] 0)) {w p : ℕ → E}
    (hp : ∀ᶠ k in atTop, p k ∈ proximalMap φ m (t k • w k)) :
    ∀ᶠ k in atTop, (t k)⁻¹ • p k ∈ proximalMap
      (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondDiffQuot φ 0 0 (t k) w) m (w k) := by
  filter_upwards [hp, (tendsto_nhdsWithin_iff.1 ht).2] with k hk htk
  rw [proximalMap_half_secondDiffQuot h0 htk]
  exact smul_mem_smul_set hk

variable [ProperSpace E]

/-- **Cluster points of the difference quotients of the proximal mapping.** Let `φ(0) = 0`,
`φ ≥ -(r/2)‖·‖²`, `λr < 1`, and let `φ` be twice epi-differentiable at `0` for `0`. If
`p_k ∈ P_λφ(t_k w_k)` with `t_k ↓ 0`, `w_k → w` and `t_k⁻¹p_k → d`, then
`d ∈ P_λ(d²φ(0, 0)/2)(w)`. -/
theorem TwiceEpiDifferentiableAt.mem_proximalMap_of_tendsto
    (H : TwiceEpiDifferentiableAt φ 0 0) (h0 : φ 0 = 0) (hm : 0 < m) (hr : 0 ≤ r)
    (hmr : m * r < 1) (hφ : ∀ x, ((-(r / 2) * ‖x‖ ^ 2 : ℝ) : EReal) ≤ φ x) {t : ℕ → ℝ}
    (ht : Tendsto t atTop (𝓝[>] 0)) {w p : ℕ → E} {w₀ d : E} (hw : Tendsto w atTop (𝓝 w₀))
    (hp : ∀ᶠ k in atTop, p k ∈ proximalMap φ m (t k • w k))
    (hd : Tendsto (fun k ↦ (t k)⁻¹ • p k) atTop (𝓝 d)) :
    d ∈ proximalMap (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderiv φ 0 0 w) m w₀ := by
  have hmem : (w₀, d) ∈ outerLimit (𝓝[>] (0 : ℝ)) (fun t ↦ graph
      (proximalMap (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondDiffQuot φ 0 0 t w) m)) :=
    mem_outerLimit_of_eventually t (fun k ↦ (w k, (t k)⁻¹ • p k)) ht (hw.prodMk_nhds hd)
      (eventually_inv_smul_mem_proximalMap h0 ht hp)
  have h1 := H.epiTendsto_half.outerLimit_graph_proximalMap_subset hm hr hmr
    (eventually_half_secondDiffQuot_ge h0 hφ) hmem
  intro y
  exact h1 y

/-- The Moreau envelope of `d²φ(0, 0)/2` is finite from above: `e_λ(d²φ(0, 0)/2)(w) ≤
‖w‖²/(2λ)`. -/
theorem TwiceEpiDifferentiableAt.moreauEnvelope_half_secondSubderiv_le
    (H : TwiceEpiDifferentiableAt φ 0 0) (h0 : φ 0 = 0) (hm : 0 < m) (hr : 0 ≤ r)
    (hmr : m * r < 1) (hφ : ∀ x, ((-(r / 2) * ‖x‖ ^ 2 : ℝ) : EReal) ≤ φ x) (w : E) :
    moreauEnvelope (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderiv φ 0 0 w) m w ≤
      (((2 * m)⁻¹ * ‖w‖ ^ 2 : ℝ) : EReal) := by
  have hE := H.epiTendsto_half.tendsto_moreauEnvelope_apply hm hr hmr
    (eventually_half_secondDiffQuot_ge h0 hφ) w
  refine le_of_tendsto hE ?_
  filter_upwards [eventually_mem_nhdsWithin] with t ht
  have ht : 0 < t := ht
  refine (moreauEnvelope_le w 0).trans (le_of_eq ?_)
  simp only [proxObjective, half_secondDiffQuot_zero h0 ht.ne', smul_zero, h0, mul_zero,
    zero_add, zero_sub, norm_neg]

/-- **Convergence of the difference quotients of the proximal mapping**
[Mordukhovich 2024, Thm. 1.98, Cor. 1.101]. Let `φ(0) = 0`, `φ ≥ -(r/2)‖·‖²`, `λr < 1`, and let
`φ` be twice epi-differentiable at `0` for `0`. If `P_λ(d²φ(0, 0)/2)(w)` has at most one point
`d`, then `t_k⁻¹p_k → d` whenever `p_k ∈ P_λφ(t_k w_k)`, `t_k ↓ 0` and `w_k → w`. -/
theorem TwiceEpiDifferentiableAt.tendsto_inv_smul_of_mem_proximalMap
    (H : TwiceEpiDifferentiableAt φ 0 0) (h0 : φ 0 = 0) (hm : 0 < m) (hr : 0 ≤ r)
    (hmr : m * r < 1) (hφ : ∀ x, ((-(r / 2) * ‖x‖ ^ 2 : ℝ) : EReal) ≤ φ x) {w₀ d : E}
    (huniq : ∀ q ∈ proximalMap (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderiv φ 0 0 w) m w₀,
      q = d)
    {t : ℕ → ℝ} (ht : Tendsto t atTop (𝓝[>] 0)) {w p : ℕ → E} (hw : Tendsto w atTop (𝓝 w₀))
    (hp : ∀ᶠ k in atTop, p k ∈ proximalMap φ m (t k • w k)) :
    Tendsto (fun k ↦ (t k)⁻¹ • p k) atTop (𝓝 d) := by
  have htop : moreauEnvelope (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderiv φ 0 0 w) m w₀
      ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _)
    (H.moreauEnvelope_half_secondSubderiv_le h0 hm hr hmr hφ w₀)
  exact H.epiTendsto_half.tendsto_of_mem_proximalMap hm hr hmr
    (eventually_half_secondDiffQuot_ge h0 hφ) htop huniq ht hw
    (eventually_inv_smul_mem_proximalMap h0 ht hp)

end TwiceEpi

end VariationalAnalysis
