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

* `TwiceEpiDifferentiableAt.exists_proximalMap_half_secondSubderiv_eq_singleton`,
  `TwiceEpiDifferentiableAt.exists_tendsto_inv_smul_proximalMap`: if moreover `P_λφ` is
  nonempty-valued near `0` and the proximal objective grows quadratically around its minimizers,
  then `P_λ(d²φ(0, 0)/2)` is single-valued and `t_k⁻¹p_k` converges to its value at `w`.

* `ProxRegularFor.exists_proxObjective_growth`: for an l.s.c., prox-bounded function that is
  prox-regular at `x̄` for `v̄ = ⟨g, ·⟩` and all small `λ`, `P_λφ` is nonempty-valued near
  `x̄ + λg` and the proximal objective grows quadratically around its minimizers.
* `ProxRegularFor.exists_tendsto_inv_smul_proximalMap`: the semidifferentiability of `P_λφ` at
  `0` for an l.s.c. function with `φ(0) = 0`, `φ ≥ -(r/2)‖·‖²` that is prox-regular and twice
  epi-differentiable at `0` for `0`.

* `shiftTilt`, `mem_proximalMap_shiftTilt_iff`, `secondDiffQuot_shiftTilt`,
  `exists_shiftTilt_ge`: the reduction of `φ` at `x̄` for `v̄ = ⟨g, ·⟩` to the function
  `φ(x̄ + ·) - φ(x̄) - ⟨g, ·⟩` at `0` for `0`.
* `ProxRegularFor.exists_tendsto_inv_smul_sub_proximalMap`: for an l.s.c., prox-bounded `φ`
  that is prox-regular and twice epi-differentiable at `x̄` for `v̄ = ⟨g, ·⟩` and all small `λ`,
  `P_λ(d²φ(x̄, v̄)/2)` is single-valued and `t⁻¹(P_λφ(x̄ + λg + tw') - x̄) → P_λ(d²φ(x̄, v̄)/2)(w)`
  as `t ↓ 0`, `w' → w` [Mordukhovich 2024, Cor. 1.101, one implication].

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

/-- The image of an outer limit under a continuous map is contained in the outer limit of the
images: `f '' Lim sup Sᵢ ⊆ Lim sup f '' Sᵢ`. -/
theorem image_outerLimit_subset {f : X → Y} (hf : Continuous f) :
    f '' outerLimit l S ⊆ outerLimit l (fun i ↦ f '' S i) := by
  rintro _ ⟨y, ⟨a, v, ha, hv, hS⟩, rfl⟩
  exact ⟨a, f ∘ v, ha, (hf.tendsto y).comp hv, fun k ↦ mem_image_of_mem f (hS k)⟩

/-- The image of an inner limit under a continuous map is contained in the inner limit of the
images: `f '' Lim inf Sᵢ ⊆ Lim inf f '' Sᵢ`. -/
theorem image_innerLimit_subset {f : X → Y} (hf : Continuous f) :
    f '' innerLimit l S ⊆ innerLimit l (fun i ↦ f '' S i) := by
  rintro _ ⟨y, hy, rfl⟩ a ha
  obtain ⟨v, hv, hS⟩ := hy a ha
  exact ⟨f ∘ v, (hf.tendsto y).comp hv, hS.mono fun k hk ↦ mem_image_of_mem f hk⟩

/-- Outer limits commute with images under a homeomorphism: `Lim sup e '' Sᵢ = e '' Lim sup Sᵢ`. -/
theorem outerLimit_image_homeomorph (e : X ≃ₜ Y) :
    outerLimit l (fun i ↦ e '' S i) = e '' outerLimit l S := by
  refine Subset.antisymm (fun y hy ↦ ?_) (image_outerLimit_subset e.continuous)
  have h := image_outerLimit_subset (l := l) (S := fun i ↦ e '' S i) e.symm.continuous
    (mem_image_of_mem e.symm hy)
  simp only [← image_comp, Homeomorph.symm_comp_self, image_id] at h
  exact ⟨e.symm y, h, e.apply_symm_apply y⟩

/-- Inner limits commute with images under a homeomorphism: `Lim inf e '' Sᵢ = e '' Lim inf Sᵢ`. -/
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

/-- If `φ(0) = 0` and `φ(x) ≥ -(r/2)‖x‖²` for all `x`, then for all small `t > 0` the halved
second-order difference quotients satisfy `½ Δ²_tφ(0, 0)(w) ≥ -(r/2)‖w‖²` for all `w`. -/
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

omit [ProperSpace E] in
/-- Quadratic growth of the proximal objective passes from `φ` to `Δ²_tφ(0, 0)/2`. -/
theorem proxObjective_half_secondDiffQuot_add_le (h0 : φ 0 = 0) {t : ℝ} (ht : 0 < t) {c : ℝ}
    {u q z : E}
    (h : proxObjective φ m (t • u) (t • q) + ((c * ‖t • z - t • q‖ ^ 2 : ℝ) : EReal) ≤
      proxObjective φ m (t • u) (t • z)) :
    proxObjective (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondDiffQuot φ 0 0 t w) m u q +
        ((c * ‖z - q‖ ^ 2 : ℝ) : EReal) ≤
      proxObjective (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondDiffQuot φ 0 0 t w) m u z := by
  simp only [half_secondDiffQuot_zero h0 ht.ne', proxObjective_scale φ ht]
  have h1 := (coe_mul_le_coe_mul_iff (show (0 : ℝ) < t⁻¹ ^ 2 by positivity)).2 h
  rw [EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.2 (by positivity))
    (EReal.coe_ne_top _), ← EReal.coe_mul] at h1
  have h2 : t⁻¹ ^ 2 * (c * ‖t • z - t • q‖ ^ 2) = c * ‖z - q‖ ^ 2 := by
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg ht.le]
    field_simp
  rwa [h2] at h1

/-- **Single-valuedness of the proximal mapping of `d²φ(0, 0)/2`.** Let `φ(0) = 0`,
`φ ≥ -(r/2)‖·‖²`, `λr < 1`, and let `φ` be twice epi-differentiable at `0` for `0`. If near `0`
the proximal mapping `P_λφ` is nonempty-valued and the proximal objective grows quadratically
around its minimizers on a ball around `0` (as for prox-regular functions), then
`P_λ(d²φ(0, 0)/2)(w)` is a singleton for every `w`. -/
theorem TwiceEpiDifferentiableAt.exists_proximalMap_half_secondSubderiv_eq_singleton
    (H : TwiceEpiDifferentiableAt φ 0 0) (h0 : φ 0 = 0) (hm : 0 < m) (hr : 0 ≤ r)
    (hmr : m * r < 1) (hφ : ∀ x, ((-(r / 2) * ‖x‖ ^ 2 : ℝ) : EReal) ≤ φ x)
    (hex : ∀ᶠ u in 𝓝 (0 : E), (proximalMap φ m u).Nonempty) {c ε : ℝ} (hc : 0 < c)
    (hε : 0 < ε)
    (hqg : ∀ᶠ u in 𝓝 (0 : E), ∀ p ∈ proximalMap φ m u, ∀ x ∈ ball (0 : E) ε,
      proxObjective φ m u p + ((c * ‖x - p‖ ^ 2 : ℝ) : EReal) ≤ proxObjective φ m u x)
    (w : E) :
    ∃ d, proximalMap (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderiv φ 0 0 w) m w = {d} := by
  classical
  have htopE := H.moreauEnvelope_half_secondSubderiv_le h0 hm hr hmr hφ w
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℝ → E → EReal,
      Ψ = fun t w ↦ ((1 / 2 : ℝ) : EReal) * secondDiffQuot φ 0 0 t w := ⟨_, rfl⟩
  obtain ⟨Ψ₀, hΨ₀⟩ : ∃ Ψ₀ : E → EReal,
      Ψ₀ = fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderiv φ 0 0 w := ⟨_, rfl⟩
  rw [← hΨ₀] at htopE ⊢
  have hepi : EpiTendsto (𝓝[>] (0 : ℝ)) Ψ Ψ₀ := by
    rw [hΨ, hΨ₀]
    exact H.epiTendsto_half
  have hbd : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ w : E, ((-(r / 2) * ‖w‖ ^ 2 : ℝ) : EReal) ≤ Ψ t w := by
    rw [hΨ]
    exact eventually_half_secondDiffQuot_ge h0 hφ
  -- a sequence `t_k ↓ 0` and proximal points `p_k ∈ P_λφ(t_k w)`
  obtain ⟨t, ht, htpos⟩ : ∃ t : ℕ → ℝ, Tendsto t atTop (𝓝[>] 0) ∧ ∀ k, 0 < t k :=
    ⟨fun k ↦ 1 / ((k : ℝ) + 1), tendsto_nhdsWithin_iff.2
      ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun k ↦ mem_Ioi.2 Nat.one_div_pos_of_nat⟩,
      fun k ↦ Nat.one_div_pos_of_nat⟩
  have ht0 : Tendsto t atTop (𝓝 0) := tendsto_nhds_of_tendsto_nhdsWithin ht
  have htw : Tendsto (fun k ↦ t k • w) atTop (𝓝 (0 : E)) := by
    simpa using ht0.smul_const w
  have hch : ∀ k, ∃ p, (proximalMap φ m (t k • w)).Nonempty → p ∈ proximalMap φ m (t k • w) := by
    intro k
    by_cases h : (proximalMap φ m (t k • w)).Nonempty
    · exact ⟨h.some, fun _ ↦ h.some_mem⟩
    · exact ⟨0, fun h' ↦ absurd h' h⟩
  choose p hp using hch
  have hp' : ∀ᶠ k in atTop, p k ∈ proximalMap φ m (t k • w) :=
    (htw.eventually hex).mono fun k hk ↦ hp k hk
  set q : ℕ → E := fun k ↦ (t k)⁻¹ • p k with hq_def
  have hq : ∀ᶠ k in atTop, q k ∈ proximalMap (Ψ (t k)) m w := by
    rw [hΨ]
    exact eventually_inv_smul_mem_proximalMap h0 ht (w := fun _ ↦ w) hp'
  have hE : Tendsto (fun k ↦ moreauEnvelope (Ψ (t k)) m w) atTop
      (𝓝 (moreauEnvelope Ψ₀ m w)) :=
    (hepi.tendsto_moreauEnvelope_apply hm hr hmr hbd w).comp ht
  -- every proximal point of the limit is the limit of `q_k`
  have key : ∀ d ∈ proximalMap Ψ₀ m w, Tendsto q atTop (𝓝 d) := by
    intro d hd
    obtain ⟨z, hz, hl⟩ := (epiTendsto_iff.1 hepi d).2 t ht
    have hsb : Ψ₀ d ≠ ⊥ := by
      have h1 : ((-(r / 2) * ‖d‖ ^ 2 - 1 : ℝ) : EReal) ≤
          limsup (fun k ↦ Ψ (t k) (z k)) atTop := by
        refine le_limsup_of_frequently_le' (Eventually.frequently ?_)
        have hc' : Tendsto (fun k ↦ -(r / 2) * ‖z k‖ ^ 2) atTop (𝓝 (-(r / 2) * ‖d‖ ^ 2)) :=
          (hz.norm.pow 2).const_mul _
        filter_upwards [ht.eventually hbd, hc'.eventually_const_lt
          (show -(r / 2) * ‖d‖ ^ 2 - 1 < -(r / 2) * ‖d‖ ^ 2 by linarith)] with k hk1 hk2
        exact (EReal.coe_le_coe_iff.2 hk2.le).trans (hk1 (z k))
      exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (h1.trans hl)
    have hd' : moreauEnvelope Ψ₀ m w = Ψ₀ d + (((2 * m)⁻¹ * ‖d - w‖ ^ 2 : ℝ) : EReal) :=
      moreauEnvelope_eq_of_mem_proximalMap hd
    have hst : Ψ₀ d ≠ ⊤ := by
      intro h
      rw [hd', h, EReal.top_add_coe] at htopE
      exact EReal.coe_ne_top _ (top_le_iff.1 htopE)
    obtain ⟨s₀, hs₀⟩ : ∃ s₀ : ℝ, Ψ₀ d = s₀ := ⟨_, (EReal.coe_toReal hst hsb).symm⟩
    rw [hd', hs₀, ← EReal.coe_add] at hE
    rw [hs₀] at hl
    have hρ : Tendsto (fun k ↦ (2 * m)⁻¹ * ‖z k - w‖ ^ 2) atTop
        (𝓝 ((2 * m)⁻¹ * ‖d - w‖ ^ 2)) := ((hz.sub_const w).norm.pow 2).const_mul _
    have htz : Tendsto (fun k ↦ t k • z k) atTop (𝓝 (0 : E)) := by
      simpa using ht0.smul hz
    have hg : ∀ᶠ k in atTop, proxObjective (Ψ (t k)) m w (q k) +
        ((c * ‖z k - q k‖ ^ 2 : ℝ) : EReal) ≤ proxObjective (Ψ (t k)) m w (z k) := by
      filter_upwards [htw.eventually hqg, hp', htz.eventually (ball_mem_nhds 0 hε)]
        with k hk hpk hzk
      have htq : t k • q k = p k := by
        rw [hq_def]
        simp only [smul_smul, mul_inv_cancel₀ (htpos k).ne', one_smul]
      rw [hΨ]
      refine proxObjective_half_secondDiffQuot_add_le h0 (htpos k) ?_
      rw [htq]
      exact hk (p k) hpk _ hzk
    have hzq : Tendsto (fun k ↦ ‖z k - q k‖) atTop (𝓝 0) := by
      refine Metric.tendsto_nhds.2 fun ε₁ hε₁ ↦ ?_
      have hη : 0 < c * ε₁ ^ 2 / 3 := by positivity
      filter_upwards [hg, hq, hE.eventually_const_lt (show
          ((s₀ + (2 * m)⁻¹ * ‖d - w‖ ^ 2 - c * ε₁ ^ 2 / 3 : ℝ) : EReal) <
            ((s₀ + (2 * m)⁻¹ * ‖d - w‖ ^ 2 : ℝ) : EReal) from
          EReal.coe_lt_coe_iff.2 (by linarith)),
        eventually_lt_of_limsup_lt (hl.trans_lt (show (s₀ : EReal) <
          ((s₀ + c * ε₁ ^ 2 / 3 : ℝ) : EReal) from EReal.coe_lt_coe_iff.2 (by linarith))),
        hρ.eventually_lt_const (show (2 * m)⁻¹ * ‖d - w‖ ^ 2 <
          (2 * m)⁻¹ * ‖d - w‖ ^ 2 + c * ε₁ ^ 2 / 3 by linarith)] with k hgk hqk h1 h2 h3
      rw [moreauEnvelope_eq_of_mem_proximalMap hqk] at h1
      have h4 := EReal.add_lt_add_right_coe h1 (c * ‖z k - q k‖ ^ 2)
      have h5 : proxObjective (Ψ (t k)) m w (z k) < ((s₀ + c * ε₁ ^ 2 / 3 +
          ((2 * m)⁻¹ * ‖d - w‖ ^ 2 + c * ε₁ ^ 2 / 3) : ℝ) : EReal) := by
        rw [EReal.coe_add]
        exact EReal.add_lt_add h2 (EReal.coe_lt_coe_iff.2 h3)
      have h6 := (h4.trans_le hgk).trans h5
      rw [← EReal.coe_add, EReal.coe_lt_coe_iff] at h6
      have h7 : c * ‖z k - q k‖ ^ 2 < c * ε₁ ^ 2 := by linarith
      have h8 : ‖z k - q k‖ ^ 2 < ε₁ ^ 2 := lt_of_mul_lt_mul_left h7 hc.le
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
      exact lt_of_pow_lt_pow_left₀ 2 hε₁.le h8
    have hlim : Tendsto (fun k ↦ z k - (z k - q k)) atTop (𝓝 (d - 0)) :=
      hz.sub (tendsto_zero_iff_norm_tendsto_zero.2 hzq)
    simpa using hlim
  -- existence of a proximal point of the limit, as a cluster point of `q_k`
  obtain ⟨C, hC, -⟩ := EReal.lt_iff_exists_real_btwn.1
    (lt_top_iff_ne_top.2 (ne_top_of_le_ne_top (EReal.coe_ne_top _) htopE))
  have hb : ∀ᶠ k in atTop, q k ∈ closedBall (0 : E)
      (‖w‖ + ((2 * (m * r) * ‖w‖ + 2 * m * |C| + m * r * ‖w‖ ^ 2) / (1 - m * r) + 1)) := by
    filter_upwards [hE.eventually_lt_const hC, hq, ht.eventually hbd] with k hk hqk hbk
    rw [moreauEnvelope_eq_of_mem_proximalMap hqk] at hk
    have hk' : Ψ (t k) (q k) + (((2 * m)⁻¹ * ‖q k - w‖ ^ 2 : ℝ) : EReal) < C := hk
    obtain ⟨s, -, hs0, hsc⟩ := exists_real_of_coe_le_of_add_lt (hbk (q k)) hk'
    exact mem_closedBall_zero_iff.2 (norm_le_of_quadratic_lt hm hr hmr hs0 hsc le_rfl)
  obtain ⟨d, -, θ, hθ, hdθ⟩ :=
    tendsto_subseq_of_frequently_bounded isBounded_closedBall hb.frequently
  have hd : d ∈ proximalMap Ψ₀ m w := by
    rw [hΨ₀]
    exact H.mem_proximalMap_of_tendsto h0 hm hr hmr hφ (ht.comp hθ.tendsto_atTop)
      (w := fun _ ↦ w) (p := fun j ↦ p (θ j)) tendsto_const_nhds
      (hθ.tendsto_atTop.eventually hp') hdθ
  exact ⟨d, Subset.antisymm (fun x hx ↦ tendsto_nhds_unique (key x hx) (key d hd))
    (singleton_subset_iff.2 hd)⟩

/-- **Semidifferentiability of the proximal mapping** [Mordukhovich 2024, Thm. 1.98,
Cor. 1.101], normalized form. Let `φ(0) = 0`, `φ ≥ -(r/2)‖·‖²`, `λr < 1`, and let `φ` be twice
epi-differentiable at `0` for `0`. If near `0` the proximal mapping `P_λφ` is nonempty-valued
and the proximal objective grows quadratically around its minimizers, then
`P_λ(d²φ(0, 0)/2)` is single-valued, with value `D(w)` say, and `t_k⁻¹p_k → D(w)` whenever
`p_k ∈ P_λφ(t_k w_k)`, `t_k ↓ 0` and `w_k → w`. -/
theorem TwiceEpiDifferentiableAt.exists_tendsto_inv_smul_proximalMap
    (H : TwiceEpiDifferentiableAt φ 0 0) (h0 : φ 0 = 0) (hm : 0 < m) (hr : 0 ≤ r)
    (hmr : m * r < 1) (hφ : ∀ x, ((-(r / 2) * ‖x‖ ^ 2 : ℝ) : EReal) ≤ φ x)
    (hex : ∀ᶠ u in 𝓝 (0 : E), (proximalMap φ m u).Nonempty) {c ε : ℝ} (hc : 0 < c)
    (hε : 0 < ε)
    (hqg : ∀ᶠ u in 𝓝 (0 : E), ∀ p ∈ proximalMap φ m u, ∀ x ∈ ball (0 : E) ε,
      proxObjective φ m u p + ((c * ‖x - p‖ ^ 2 : ℝ) : EReal) ≤ proxObjective φ m u x) :
    ∃ D : E → E,
      (∀ w, proximalMap (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderiv φ 0 0 w) m w = {D w}) ∧
      ∀ t : ℕ → ℝ, Tendsto t atTop (𝓝[>] 0) → ∀ (w p : ℕ → E) (w₀ : E),
        Tendsto w atTop (𝓝 w₀) → (∀ᶠ k in atTop, p k ∈ proximalMap φ m (t k • w k)) →
        Tendsto (fun k ↦ (t k)⁻¹ • p k) atTop (𝓝 (D w₀)) := by
  choose D hD using fun w ↦
    H.exists_proximalMap_half_secondSubderiv_eq_singleton h0 hm hr hmr hφ hex hc hε hqg w
  refine ⟨D, hD, fun t ht w p w₀ hw hp ↦ ?_⟩
  refine H.tendsto_inv_smul_of_mem_proximalMap h0 hm hr hmr hφ (fun q hq ↦ ?_) ht hw hp
  rw [hD w₀] at hq
  exact hq

end TwiceEpi

/-! ### Prox-regular functions -/

section ProxRegular

open InnerProductSpace
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {φ : E → EReal} {x₀ : E}

/-- **Quadratic growth of the proximal objective of a prox-regular function.** Let `φ` be l.s.c.,
prox-bounded and prox-regular at `x̄` for `v̄ = ⟨g, ·⟩`. Then for all small `λ > 0` there are
`δ, c, ε > 0` such that for `u ∈ B(x̄ + λg, δ)` the proximal mapping `P_λφ(u)` is nonempty and
`φ(p) + ‖p - u‖²/(2λ) + c‖x - p‖² ≤ φ(x) + ‖x - u‖²/(2λ)` for `p ∈ P_λφ(u)` and
`x ∈ B(x̄, ε)`. -/
theorem ProxRegularFor.exists_proxObjective_growth {g : E}
    (hφ : ProxRegularFor φ x₀ (toDual ℝ E g)) (hlsc : ∀ x, LowerSemicontinuousAt φ x)
    (hbd : ∃ a b : ℝ, ∀ x, ((a - b * ‖x - x₀‖ ^ 2 : ℝ) : EReal) ≤ φ x) :
    ∃ l₀ > (0 : ℝ), ∀ l, 0 < l → l < l₀ → ∃ δ > (0 : ℝ), ∃ c > (0 : ℝ), ∃ ε > (0 : ℝ),
      ∀ u ∈ ball (x₀ + l • g) δ, (proximalMap φ l u).Nonempty ∧
        ∀ p ∈ proximalMap φ l u, ∀ x ∈ ball x₀ ε,
          proxObjective φ l u p + ((c * ‖x - p‖ ^ 2 : ℝ) : EReal) ≤ proxObjective φ l u x := by
  obtain ⟨ε', hε', l₁, hl₁, Hprox⟩ := hφ.exists_proximalMap hlsc hbd
  obtain ⟨hv₀, -, ε, hε, η, hη, H⟩ := hφ
  have ⟨r₀, hr₀, _⟩ := hv₀
  refine ⟨min l₁ (1 / (η + 1)), lt_min hl₁ (by positivity), fun l hl hll ↦ ?_⟩
  have hlη : l * η < 1 := by
    have h1 : l < 1 / (η + 1) := hll.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith
  have hηl : η < l⁻¹ := by
    have := mul_lt_mul_of_pos_right hlη (inv_pos.2 hl)
    rwa [mul_comm l, mul_assoc, mul_inv_cancel₀ hl.ne', mul_one, one_mul] at this
  have h2l : (2 * l)⁻¹ = l⁻¹ / 2 := by rw [mul_inv]; ring
  obtain ⟨δ, hδ, p, hp0, hP, hLip, hloc, -⟩ := Hprox l hl (hll.trans_le (min_le_left _ _))
  have hpc : ContinuousAt p (x₀ + l • g) :=
    hLip.continuousOn.continuousAt (ball_mem_nhds _ hδ)
  have e1 : ∀ᶠ u in 𝓝 (x₀ + l • g), ‖p u - x₀‖ < ε :=
    ContinuousAt.eventually_lt (f := fun u ↦ ‖p u - x₀‖) (g := fun _ ↦ ε)
      (hpc.sub continuousAt_const).norm continuousAt_const (by simpa [hp0] using hε)
  have e2 : ∀ᶠ u in 𝓝 (x₀ + l • g), ‖l⁻¹ • (u - p u) - g‖ < ε :=
    ContinuousAt.eventually_lt (f := fun u ↦ ‖l⁻¹ • (u - p u) - g‖) (g := fun _ ↦ ε)
      (((continuousAt_id.sub hpc).const_smul l⁻¹).sub continuousAt_const).norm
      continuousAt_const (by simpa [hp0, smul_smul, inv_mul_cancel₀ hl.ne'] using hε)
  have e3 : ∀ᶠ u in 𝓝 (x₀ + l • g), (2 * l)⁻¹ * (‖x₀ - u‖ ^ 2 - ‖p u - u‖ ^ 2) < ε :=
    ContinuousAt.eventually_lt
      (f := fun u ↦ (2 * l)⁻¹ * (‖x₀ - u‖ ^ 2 - ‖p u - u‖ ^ 2)) (g := fun _ ↦ ε)
      (continuousAt_const.mul (((continuousAt_const.sub continuousAt_id).norm.pow 2).sub
        ((hpc.sub continuousAt_id).norm.pow 2))) continuousAt_const
      (by simpa [hp0] using hε)
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.eventually_nhds_iff.1
    (e1.and (e2.and (e3.and (eventually_mem_set.2 (ball_mem_nhds _ hδ)))))
  refine ⟨δ₁, hδ₁, (2 * l)⁻¹ - η / 2, by rw [h2l]; linarith, ε, hε, fun u hu ↦ ?_⟩
  obtain ⟨h1, h2, h3, hub⟩ := hball hu
  have hPu := hP u hub
  refine ⟨by rw [hPu]; exact singleton_nonempty _, fun q hq x hx ↦ ?_⟩
  rw [hPu, mem_singleton_iff] at hq
  subst hq
  obtain ⟨hv, -, -, s, hs, -⟩ := hloc u hub
  have hmem : p u ∈ proximalMap φ l u := by rw [hPu]; exact mem_singleton _
  have hmin : φ (p u) + (((2 * l)⁻¹ * ‖p u - u‖ ^ 2 : ℝ) : EReal) ≤
      φ x₀ + (((2 * l)⁻¹ * ‖x₀ - u‖ ^ 2 : ℝ) : EReal) := hmem x₀
  rw [hs, hr₀, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at hmin
  have hs_le : s ≤ r₀ + ε := by linarith
  have hφle : φ (p u) ≤ φ x₀ + (ε : EReal) := by
    rw [hs, hr₀, ← EReal.coe_add]
    exact EReal.coe_le_coe_iff.2 hs_le
  have hvn : ‖toDual ℝ E (l⁻¹ • (u - p u)) - toDual ℝ E g‖ ≤ ε := by
    rw [← map_sub, LinearIsometryEquiv.norm_map]
    exact h2.le
  have key := H (p u) x _ hv s hs hvn (mem_ball_iff_norm.1 hx).le h1.le hφle
  rw [toDual_apply_apply, real_inner_smul_left] at key
  have key' := add_le_add key (le_refl (((2 * l)⁻¹ * ‖x - u‖ ^ 2 : ℝ) : EReal))
  rw [← EReal.coe_add] at key'
  change φ (p u) + (((2 * l)⁻¹ * ‖p u - u‖ ^ 2 : ℝ) : EReal) +
    ((((2 * l)⁻¹ - η / 2) * ‖x - p u‖ ^ 2 : ℝ) : EReal) ≤
    φ x + (((2 * l)⁻¹ * ‖x - u‖ ^ 2 : ℝ) : EReal)
  rw [hs, ← EReal.coe_add, ← EReal.coe_add]
  refine le_trans (EReal.coe_le_coe_iff.2 ?_) key'
  have hN := norm_sub_sq_real (x - p u) (u - p u)
  have e : x - p u - (u - p u) = x - u := by abel
  have hcomm : ⟪x - p u, u - p u⟫_ℝ = ⟪u - p u, x - p u⟫_ℝ := real_inner_comm _ _
  rw [e, hcomm] at hN
  rw [hN, norm_sub_rev (p u) u, h2l]
  linarith

/-- **Semidifferentiability of the proximal mapping of a prox-regular function**
[Mordukhovich 2024, Thm. 1.98, Cor. 1.101], normalized form. Let `φ` be l.s.c. with `φ(0) = 0`
and `φ ≥ -(r/2)‖·‖²`, prox-regular at `0` for `0` and twice epi-differentiable at `0` for `0`.
Then for all small `λ > 0` the proximal mapping `P_λ(d²φ(0, 0)/2)` is single-valued, with value
`D(w)` say, and `t_k⁻¹p_k → D(w)` whenever `p_k ∈ P_λφ(t_k w_k)`, `t_k ↓ 0` and `w_k → w`. -/
theorem ProxRegularFor.exists_tendsto_inv_smul_proximalMap {r : ℝ}
    (hφ : ProxRegularFor φ 0 0) (H : TwiceEpiDifferentiableAt φ 0 0) (h0 : φ 0 = 0)
    (hr : 0 ≤ r) (hmin : ∀ x, ((-(r / 2) * ‖x‖ ^ 2 : ℝ) : EReal) ≤ φ x)
    (hlsc : ∀ x, LowerSemicontinuousAt φ x) :
    ∃ l₀ > (0 : ℝ), ∀ m, 0 < m → m < l₀ → ∃ D : E → E,
      (∀ w, proximalMap (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderiv φ 0 0 w) m w = {D w}) ∧
      ∀ t : ℕ → ℝ, Tendsto t atTop (𝓝[>] 0) → ∀ (w p : ℕ → E) (w₀ : E),
        Tendsto w atTop (𝓝 w₀) → (∀ᶠ k in atTop, p k ∈ proximalMap φ m (t k • w k)) →
        Tendsto (fun k ↦ (t k)⁻¹ • p k) atTop (𝓝 (D w₀)) := by
  have hφ' : ProxRegularFor φ 0 (toDual ℝ E 0) := by simpa using hφ
  have hbd : ∃ a b : ℝ, ∀ x : E, ((a - b * ‖x - 0‖ ^ 2 : ℝ) : EReal) ≤ φ x :=
    ⟨0, r / 2, fun x ↦ by rw [sub_zero, zero_sub, ← neg_mul]; exact hmin x⟩
  obtain ⟨l₁, hl₁, Hg⟩ := hφ'.exists_proxObjective_growth hlsc hbd
  refine ⟨min l₁ (1 / (r + 1)), lt_min hl₁ (by positivity), fun m hm hml ↦ ?_⟩
  have hmr : m * r < 1 := by
    have h1 : m < 1 / (r + 1) := hml.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith
  obtain ⟨δ, hδ, c, hc, ε, hε, Hu⟩ := Hg m hm (hml.trans_le (min_le_left _ _))
  simp only [smul_zero, add_zero] at Hu
  exact H.exists_tendsto_inv_smul_proximalMap h0 hm hr hmr hmin
    (Metric.eventually_nhds_iff.2 ⟨δ, hδ, fun u hu ↦ (Hu u (mem_ball.2 hu)).1⟩) hc hε
    (Metric.eventually_nhds_iff.2 ⟨δ, hδ, fun u hu ↦ (Hu u (mem_ball.2 hu)).2⟩)

/-! #### Reduction to the normalized form -/

/-- The shifted and tilted function `x ↦ φ(x̄ + x) - φ(x̄) - ⟨g, x⟩`, which reduces the study of
`φ` at `x̄` for `v̄ = ⟨g, ·⟩` to that of a function at `0` for `0`. -/
noncomputable def shiftTilt (φ : E → EReal) (x₀ g : E) (x : E) : EReal :=
  φ (x₀ + x) + ((-((φ x₀).toReal + ⟪g, x⟫_ℝ) : ℝ) : EReal)

/-- Adding a real number is strictly monotone on `EReal`: `a + c ≤ b + c ↔ a ≤ b` for `c : ℝ`. -/
theorem add_coe_le_add_coe_iff {a b : EReal} {c : ℝ} : a + (c : EReal) ≤ b + c ↔ a ≤ b := by
  refine ⟨fun h ↦ ?_, fun h ↦ add_le_add h le_rfl⟩
  have := add_le_add h (le_refl ((-c : ℝ) : EReal))
  rwa [add_assoc, add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero,
    add_zero] at this

omit [FiniteDimensional ℝ E] in
/-- If `φ(x̄)` is finite, the shifted and tilted function vanishes at the origin. -/
theorem shiftTilt_zero {r₀ : ℝ} {g : E} (hr₀ : φ x₀ = r₀) : shiftTilt φ x₀ g 0 = 0 := by
  rw [shiftTilt, add_zero, hr₀, EReal.toReal_coe, inner_zero_right, add_zero, ← EReal.coe_add,
    add_neg_cancel, EReal.coe_zero]

omit [FiniteDimensional ℝ E] in
/-- The proximal objective of the shifted and tilted function. -/
theorem proxObjective_shiftTilt (φ : E → EReal) (x₀ g : E) {m : ℝ} (hm : m ≠ 0) (u x : E) :
    proxObjective (shiftTilt φ x₀ g) m u x = proxObjective φ m (x₀ + u + m • g) (x₀ + x) +
      ((-((φ x₀).toReal + ⟪g, u⟫_ℝ + m / 2 * ‖g‖ ^ 2) : ℝ) : EReal) := by
  simp only [proxObjective, shiftTilt]
  rw [add_assoc, add_assoc, ← EReal.coe_add, ← EReal.coe_add]
  congr 2
  have e : x₀ + x - (x₀ + u + m • g) = (x - u) - m • g := by abel
  have h1 : ⟪x - u, m • g⟫_ℝ = m * (⟪g, x⟫_ℝ - ⟪g, u⟫_ℝ) := by
    rw [inner_smul_right, inner_sub_left, real_inner_comm g x, real_inner_comm g u]
  have h2 : ‖m • g‖ ^ 2 = m ^ 2 * ‖g‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [e, norm_sub_sq_real (x - u) (m • g), h1, h2]
  field_simp
  ring

omit [FiniteDimensional ℝ E] in
/-- `P_λ(φ(x̄ + ·) - φ(x̄) - ⟨g, ·⟩)(u) = P_λφ(x̄ + u + λg) - x̄`. -/
theorem mem_proximalMap_shiftTilt_iff {g : E} {m : ℝ} (hm : m ≠ 0) {u x : E} :
    x ∈ proximalMap (shiftTilt φ x₀ g) m u ↔ x₀ + x ∈ proximalMap φ m (x₀ + u + m • g) := by
  constructor
  · intro h y
    have := h (y - x₀)
    rwa [proxObjective_shiftTilt φ x₀ g hm, proxObjective_shiftTilt φ x₀ g hm,
      add_coe_le_add_coe_iff, add_sub_cancel] at this
  · intro h y
    show proxObjective (shiftTilt φ x₀ g) m u x ≤ proxObjective (shiftTilt φ x₀ g) m u y
    rw [proxObjective_shiftTilt φ x₀ g hm, proxObjective_shiftTilt φ x₀ g hm,
      add_coe_le_add_coe_iff]
    exact h (x₀ + y)

/-- The second-order difference quotients of `φ` at `x̄` for `⟨g, ·⟩` are those of the shifted and
tilted function at `0` for `0`. -/
theorem secondDiffQuot_shiftTilt {r₀ : ℝ} {g : E} (hr₀ : φ x₀ = r₀) (t : ℝ) (w : E) :
    secondDiffQuot (shiftTilt φ x₀ g) 0 0 t w = secondDiffQuot φ x₀ (toDual ℝ E g) t w := by
  rw [secondDiffQuot, secondDiffQuot, shiftTilt_zero hr₀, zero_add, sub_zero]
  have h1 : ((t * (0 : StrongDual ℝ E) w : ℝ) : EReal) = 0 := by simp
  have h2 : shiftTilt φ x₀ g (t • w) - 0 =
      φ (x₀ + t • w) - φ x₀ - ((t * toDual ℝ E g w : ℝ) : EReal) := by
    rw [sub_zero, shiftTilt, hr₀, EReal.toReal_coe, toDual_apply_apply, inner_smul_right,
      sub_eq_add_neg, sub_eq_add_neg, ← EReal.coe_neg, ← EReal.coe_neg, add_assoc,
      ← EReal.coe_add, neg_add]
  rw [h1, h2]

/-- A prox-bounded function with a proximal subgradient `⟨g, ·⟩` at `x̄` has a global quadratic
minorant after the shift and tilt. -/
theorem exists_shiftTilt_ge {g : E} (hv : toDual ℝ E g ∈ proxSubdiff φ x₀)
    (hbd : ∃ a b : ℝ, ∀ x, ((a - b * ‖x - x₀‖ ^ 2 : ℝ) : EReal) ≤ φ x) :
    ∃ R ≥ (0 : ℝ), ∀ x, ((-(R / 2) * ‖x‖ ^ 2 : ℝ) : EReal) ≤ shiftTilt φ x₀ g x := by
  obtain ⟨r₀, hr₀, ε, hε, ρ, hρ, Hp⟩ := hv
  obtain ⟨a, b, hab⟩ := hbd
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = |b| + |a - r₀| / ε ^ 2 + ‖g‖ / ε := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  refine ⟨max ρ (2 * Q), hρ.trans (le_max_left _ _), fun x ↦ ?_⟩
  have hRρ : ρ ≤ max ρ (2 * Q) := le_max_left _ _
  have hRQ : 2 * Q ≤ max ρ (2 * Q) := le_max_right _ _
  have key : ((r₀ + ⟪g, x⟫_ℝ - max ρ (2 * Q) / 2 * ‖x‖ ^ 2 : ℝ) : EReal) ≤ φ (x₀ + x) := by
    by_cases hx : ‖x‖ ≤ ε
    · have h1 := Hp (x₀ + x) (by rwa [add_sub_cancel_left])
      rw [add_sub_cancel_left, toDual_apply_apply] at h1
      refine le_trans (EReal.coe_le_coe_iff.2 ?_) h1
      nlinarith [sq_nonneg ‖x‖]
    · have hlt : ε < ‖x‖ := not_le.1 hx
      have h1 := hab (x₀ + x)
      rw [add_sub_cancel_left] at h1
      refine le_trans (EReal.coe_le_coe_iff.2 ?_) h1
      have hn0 : 0 ≤ ‖x‖ := norm_nonneg x
      have g1 : ⟪g, x⟫_ℝ ≤ ‖g‖ * ‖x‖ := real_inner_le_norm g x
      have g2 : ‖g‖ * ‖x‖ ≤ ‖g‖ / ε * ‖x‖ ^ 2 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hε]
        nlinarith [mul_nonneg (mul_nonneg (norm_nonneg g) hn0) (sub_nonneg.2 hlt.le)]
      have g3 : |a - r₀| ≤ |a - r₀| / ε ^ 2 * ‖x‖ ^ 2 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε.le hlt.le 2) (abs_nonneg _)
      have g4 : r₀ - a ≤ |a - r₀| := by linarith [neg_abs_le (a - r₀)]
      have g5 : b * ‖x‖ ^ 2 ≤ |b| * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self b) (sq_nonneg _)
      have g6 : Q * ‖x‖ ^ 2 ≤ max ρ (2 * Q) / 2 * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      have g7 : Q * ‖x‖ ^ 2 =
          |b| * ‖x‖ ^ 2 + |a - r₀| / ε ^ 2 * ‖x‖ ^ 2 + ‖g‖ / ε * ‖x‖ ^ 2 := by
        rw [hQ]; ring
      linarith
  have := add_le_add key (le_refl ((-(r₀ + ⟪g, x⟫_ℝ) : ℝ) : EReal))
  rw [← EReal.coe_add] at this
  rw [shiftTilt, hr₀, EReal.toReal_coe]
  refine le_trans (EReal.coe_le_coe_iff.2 (le_of_eq ?_)) this
  ring

/-- **Semidifferentiability of the proximal mapping of a prox-regular function**
[Mordukhovich 2024, Thm. 1.98, Cor. 1.101]. Let `φ` be l.s.c. and prox-bounded, prox-regular
and twice epi-differentiable at `x̄` for `v̄ = ⟨g, ·⟩`. Then for all small `λ > 0` the proximal
mapping `P_λ(d²φ(x̄, v̄)/2)` is single-valued, with value `D(w)` say, and
`t_k⁻¹(p_k - x̄) → D(w)` whenever `p_k ∈ P_λφ(x̄ + λg + t_k w_k)`, `t_k ↓ 0` and `w_k → w`. -/
theorem ProxRegularFor.exists_tendsto_inv_smul_sub_proximalMap {g : E}
    (hφ : ProxRegularFor φ x₀ (toDual ℝ E g))
    (H : TwiceEpiDifferentiableAt φ x₀ (toDual ℝ E g)) (hlsc : ∀ x, LowerSemicontinuousAt φ x)
    (hbd : ∃ a b : ℝ, ∀ x, ((a - b * ‖x - x₀‖ ^ 2 : ℝ) : EReal) ≤ φ x) :
    ∃ l₀ > (0 : ℝ), ∀ m, 0 < m → m < l₀ → ∃ D : E → E,
      (∀ w, proximalMap
        (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderiv φ x₀ (toDual ℝ E g) w) m w = {D w}) ∧
      ∀ t : ℕ → ℝ, Tendsto t atTop (𝓝[>] 0) → ∀ (w p : ℕ → E) (w₀ : E),
        Tendsto w atTop (𝓝 w₀) →
        (∀ᶠ k in atTop, p k ∈ proximalMap φ m (x₀ + m • g + t k • w k)) →
        Tendsto (fun k ↦ (t k)⁻¹ • (p k - x₀)) atTop (𝓝 (D w₀)) := by
  obtain ⟨⟨r₀, hr₀⟩, H2⟩ := H
  obtain ⟨R, hR, hmin⟩ := exists_shiftTilt_ge hφ.mem_proxSubdiff hbd
  obtain ⟨l₁, hl₁, Hg⟩ := hφ.exists_proxObjective_growth hlsc hbd
  refine ⟨min l₁ (1 / (R + 1)), lt_min hl₁ (by positivity), fun m hm hml ↦ ?_⟩
  have hmr : m * R < 1 := by
    have h1 : m < 1 / (R + 1) := hml.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith
  obtain ⟨δ, hδ, c, hc, ε, hε, Hu⟩ := Hg m hm (hml.trans_le (min_le_left _ _))
  obtain ⟨ψ, hψ⟩ : ∃ ψ : E → EReal, ψ = shiftTilt φ x₀ g := ⟨_, rfl⟩
  have hψ0 : ψ 0 = 0 := by rw [hψ]; exact shiftTilt_zero hr₀
  have hq : ∀ t w, secondDiffQuot ψ 0 0 t w = secondDiffQuot φ x₀ (toDual ℝ E g) t w := by
    rw [hψ]; exact secondDiffQuot_shiftTilt hr₀
  have hsub : ∀ w, secondSubderiv ψ 0 0 w = secondSubderiv φ x₀ (toDual ℝ E g) w := fun w ↦ by
    simp only [secondSubderiv, hq]
  have Hψ : TwiceEpiDifferentiableAt ψ 0 0 := by
    refine ⟨⟨0, by rw [hψ0, EReal.coe_zero]⟩, ?_⟩
    simp only [hq, hsub]
    exact H2
  have hmem : ∀ {u x : E}, x ∈ proximalMap ψ m u ↔ x₀ + x ∈ proximalMap φ m (x₀ + u + m • g) := by
    rw [hψ]; exact mem_proximalMap_shiftTilt_iff hm.ne'
  have hobj : ∀ u x : E, proxObjective ψ m u x = proxObjective φ m (x₀ + u + m • g) (x₀ + x) +
      ((-((φ x₀).toReal + ⟪g, u⟫_ℝ + m / 2 * ‖g‖ ^ 2) : ℝ) : EReal) := by
    rw [hψ]; exact proxObjective_shiftTilt φ x₀ g hm.ne'
  have hu' : ∀ u : E, dist u 0 < δ → x₀ + u + m • g ∈ ball (x₀ + m • g) δ := fun u hu ↦ by
    rw [mem_ball_iff_norm, show x₀ + u + m • g - (x₀ + m • g) = u by abel]
    rwa [dist_zero_right] at hu
  have hex : ∀ᶠ u in 𝓝 (0 : E), (proximalMap ψ m u).Nonempty := by
    refine Metric.eventually_nhds_iff.2 ⟨δ, hδ, fun u hu ↦ ?_⟩
    obtain ⟨p', hp'⟩ := (Hu _ (hu' u hu)).1
    exact ⟨p' - x₀, hmem.2 (by rwa [add_sub_cancel])⟩
  have hqg : ∀ᶠ u in 𝓝 (0 : E), ∀ p ∈ proximalMap ψ m u, ∀ x ∈ ball (0 : E) ε,
      proxObjective ψ m u p + ((c * ‖x - p‖ ^ 2 : ℝ) : EReal) ≤ proxObjective ψ m u x := by
    refine Metric.eventually_nhds_iff.2 ⟨δ, hδ, fun u hu p hp x hx ↦ ?_⟩
    have h1 := (Hu _ (hu' u hu)).2 (x₀ + p) (hmem.1 hp) (x₀ + x)
      (by rw [mem_ball_iff_norm] at hx ⊢; simpa using hx)
    rw [add_sub_add_left_eq_sub] at h1
    rw [hobj, hobj, add_right_comm, add_coe_le_add_coe_iff]
    exact h1
  obtain ⟨D, hD, hconv⟩ :=
    Hψ.exists_tendsto_inv_smul_proximalMap hψ0 hm hR hmr (by rw [hψ]; exact hmin) hex hc hε hqg
  refine ⟨D, fun w ↦ ?_, fun t ht w p w₀ hw hp ↦ ?_⟩
  · have := hD w
    simp only [hsub] at this
    exact this
  · refine hconv t ht w (fun k ↦ p k - x₀) w₀ hw (hp.mono fun k hk ↦ hmem.2 ?_)
    rw [add_sub_cancel, add_right_comm]
    exact hk

end ProxRegular

end VariationalAnalysis
