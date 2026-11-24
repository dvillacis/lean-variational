/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis.Subdifferential.Marginal

/-!
# Subdifferentiation of infimal convolutions

The infimal convolution [Mordukhovich 2018, (4.6)]
`(φ₁ ⊕ φ₂)(x) = inf {φ₁ x₁ + φ₂ x₂ | x₁ + x₂ = x}` and the convolution mapping (4.7)
`C(x) = {(x₁, x₂) | x₁ + x₂ = x, φ₁ x₁ + φ₂ x₂ = (φ₁ ⊕ φ₂)(x)}`. As in the book, Thm. 4.4 follows
from Thm. 4.1 through the marginal representation (4.8) with cost `φ(x, (x₁, x₂)) = φ₁ x₁ + φ₂ x₂`
and constraint `G(x) = {(x₁, x₂) | x₁ + x₂ = x}`: the qualification condition (4.3) holds
automatically (`convCost_qc`), `D*G(x₀, (x₁, x₂))(v₁, v₂) ⊆ {v₁} ∩ {v₂}`
(`eq_of_mem_coderiv_convConstraint`) and `∂φ(x₀, (x₁, x₂)) ⊆ {0} × ∂φ₁(x₁) × ∂φ₂(x₂)`
(`subdiff_sep_subset`, by the sum rule Thm. 2.19, whose qualification condition is automatic for
separable sums).

The hypotheses follow `VariationalAnalysis.Subdifferential.Marginal`: part (i) is stated under
`(φ₁ ⊕ φ₂)`-inner semicontinuity of `C` (plus lower semicontinuity of `φ₁ ⊕ φ₂` at `x₀` for the
singular part), and under the book's inner semicontinuity together with the attainment of the
infimum near `x₀`; part (ii) assumes this attainment as well.

## Main results

* `infConv`, `convMap`: (4.6), (4.7); `infConv_eq_marginal`: (4.8).
* `subdiff_infConv_subset`, `singularSubdiff_infConv_subset`,
  `infConv_subset_of_innerSemicontinuousAt`: Thm. 4.4(i) of [Mordukhovich 2018].
* `infConv_subset_of_locallyBoundedAt`: Thm. 4.4(ii) of [Mordukhovich 2018].
* `subdiff_sep_subset`, `singularSubdiff_sep_subset`: subgradients of separable sums
  `(x, y) ↦ φ₁ x + φ₂ y`.
-/

open Filter Topology Set Metric
open scoped Pointwise

namespace VariationalAnalysis

section Definitions

variable {E : Type*} [Add E]

/-- The infimal convolution [Mordukhovich 2018, (4.6)]
`(φ₁ ⊕ φ₂)(x) = inf {φ₁ x₁ + φ₂ x₂ | x₁ + x₂ = x}`. -/
noncomputable def infConv (φ₁ φ₂ : E → EReal) (x : E) : EReal :=
  ⨅ p ∈ {p : E × E | p.1 + p.2 = x}, φ₁ p.1 + φ₂ p.2

/-- The convolution mapping [Mordukhovich 2018, (4.7)]
`C(x) = {(x₁, x₂) | x₁ + x₂ = x, φ₁ x₁ + φ₂ x₂ = (φ₁ ⊕ φ₂)(x)}`. -/
def convMap (φ₁ φ₂ : E → EReal) (x : E) : Set (E × E) :=
  {p | p.1 + p.2 = x ∧ φ₁ p.1 + φ₂ p.2 = infConv φ₁ φ₂ x}

/-- The cost `φ(x, (x₁, x₂)) = φ₁ x₁ + φ₂ x₂` of the marginal representation (4.8). -/
noncomputable def convCost (φ₁ φ₂ : E → EReal) (q : E × (E × E)) : EReal := φ₁ q.2.1 + φ₂ q.2.2

/-- The constraint `G(x) = {(x₁, x₂) | x₁ + x₂ = x}` of the marginal representation (4.8). -/
def convConstraint (x : E) : Set (E × E) := {p | p.1 + p.2 = x}

/-- [Mordukhovich 2018, (4.8)]: the infimal convolution is a marginal function. -/
theorem infConv_eq_marginal (φ₁ φ₂ : E → EReal) :
    infConv φ₁ φ₂ = marginal (convCost φ₁ φ₂) convConstraint := rfl

/-- [Mordukhovich 2018, proof of Thm. 4.4]: the convolution mapping is the argminimum mapping
of the marginal representation (4.8). -/
theorem convMap_eq_argminMap (φ₁ φ₂ : E → EReal) :
    convMap φ₁ φ₂ = argminMap (convCost φ₁ φ₂) convConstraint := rfl

end Definitions

/-- A finite sum of extended reals has finite summands. -/
theorem exists_coe_of_add_eq_coe {a b : EReal} {r : ℝ} (h : a + b = r) :
    ∃ s t : ℝ, a = s ∧ b = t := by
  induction a using EReal.rec <;> induction b using EReal.rec <;>
    first
    | exact ⟨_, _, rfl, rfl⟩
    | simp at h

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

section Separable

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
variable {φ₁ : E → EReal} {φ₂ : F → EReal} {a : E} {b : F} {r₁ r₂ : ℝ}

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem locallyClosed_epi_comp_fst (r₁ : ℝ) (h₁ : ∃ U ∈ 𝓝 a, LowerSemicontinuousOn φ₁ U) :
    ∃ ρ > 0, IsClosed ((fun p : E × F ↦ φ₁ p.1).Epi univ ∩
      closedBall (((a, b), r₁) : (E × F) × ℝ) ρ) := by
  obtain ⟨U, hU, h⟩ := h₁
  refine locallyClosed_epi_of_lowerSemicontinuousOn (prod_mem_nhds hU univ_mem)
    (h.comp continuousOn_fst fun p hp ↦ hp.1) r₁

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem locallyClosed_epi_comp_snd (r₂ : ℝ) (h₂ : ∃ U ∈ 𝓝 b, LowerSemicontinuousOn φ₂ U) :
    ∃ ρ > 0, IsClosed ((fun p : E × F ↦ φ₂ p.2).Epi univ ∩
      closedBall (((a, b), r₂) : (E × F) × ℝ) ρ) := by
  obtain ⟨U, hU, h⟩ := h₂
  refine locallyClosed_epi_of_lowerSemicontinuousOn (prod_mem_nhds univ_mem hU)
    (h.comp continuousOn_snd fun p hp ↦ hp.2) r₂

/-- The qualification condition (2.34) holds automatically for `φ₁ ∘ fst` and `φ₂ ∘ snd`. -/
theorem sep_qc (w : StrongDual ℝ (E × F))
    (h₁ : w ∈ singularSubdiff (fun p : E × F ↦ φ₁ p.1) (a, b))
    (h₂ : -w ∈ singularSubdiff (fun p : E × F ↦ φ₂ p.2) (a, b)) : w = 0 := by
  rw [singularSubdiff_comp_fst] at h₁
  rw [singularSubdiff_comp_snd] at h₂
  obtain ⟨u, -, rfl⟩ := h₁
  obtain ⟨t, -, ht⟩ := h₂
  have hu : u = 0 := by
    ext x
    have := congrArg (fun ℓ : StrongDual ℝ (E × F) ↦ ℓ (x, 0)) ht
    simpa using this.symm
  subst hu
  exact ContinuousLinearMap.zero_comp _

/-- Subgradients of separable sums [Mordukhovich 2018, proof of Thm. 4.4]: for `φ₁, φ₂` l.s.c.
around `a` and `b` and finite there, `∂(φ₁ ⊕ φ₂)(a, b) ⊆ ∂φ₁(a) × ∂φ₂(b)`, where
`(φ₁ ⊕ φ₂)(x, y) = φ₁ x + φ₂ y` (by the sum rule, Thm. 2.19, whose qualification condition is
automatic). -/
theorem subdiff_sep_subset (hr₁ : φ₁ a = r₁) (hr₂ : φ₂ b = r₂)
    (h₁ : ∃ U ∈ 𝓝 a, LowerSemicontinuousOn φ₁ U) (h₂ : ∃ U ∈ 𝓝 b, LowerSemicontinuousOn φ₂ U) :
    subdiff (fun p : E × F ↦ φ₁ p.1 + φ₂ p.2) (a, b) ⊆
      {w | w.comp (ContinuousLinearMap.inl ℝ E F) ∈ subdiff φ₁ a ∧
        w.comp (ContinuousLinearMap.inr ℝ E F) ∈ subdiff φ₂ b} := by
  intro w hw
  have h := subdiff_add_subset (φ₁ := fun p : E × F ↦ φ₁ p.1) (φ₂ := fun p : E × F ↦ φ₂ p.2)
    (x₀ := (a, b)) hr₁ hr₂ (locallyClosed_epi_comp_fst r₁ h₁) (locallyClosed_epi_comp_snd r₂ h₂)
    sep_qc hw
  rw [subdiff_comp_fst, subdiff_comp_snd] at h
  obtain ⟨_, ⟨u, hu, rfl⟩, _, ⟨t, ht, rfl⟩, rfl⟩ := h
  refine ⟨?_, ?_⟩
  · convert hu using 1; ext; simp
  · convert ht using 1; ext; simp

/-- Singular subgradients of separable sums: `∂^∞(φ₁ ⊕ φ₂)(a, b) ⊆ ∂^∞φ₁(a) × ∂^∞φ₂(b)`. -/
theorem singularSubdiff_sep_subset (hr₁ : φ₁ a = r₁) (hr₂ : φ₂ b = r₂)
    (h₁ : ∃ U ∈ 𝓝 a, LowerSemicontinuousOn φ₁ U) (h₂ : ∃ U ∈ 𝓝 b, LowerSemicontinuousOn φ₂ U) :
    singularSubdiff (fun p : E × F ↦ φ₁ p.1 + φ₂ p.2) (a, b) ⊆
      {w | w.comp (ContinuousLinearMap.inl ℝ E F) ∈ singularSubdiff φ₁ a ∧
        w.comp (ContinuousLinearMap.inr ℝ E F) ∈ singularSubdiff φ₂ b} := by
  intro w hw
  have h := singularSubdiff_add_subset (φ₁ := fun p : E × F ↦ φ₁ p.1)
    (φ₂ := fun p : E × F ↦ φ₂ p.2) (x₀ := (a, b)) hr₁ hr₂ (locallyClosed_epi_comp_fst r₁ h₁)
    (locallyClosed_epi_comp_snd r₂ h₂) sep_qc hw
  rw [singularSubdiff_comp_fst, singularSubdiff_comp_snd] at h
  obtain ⟨_, ⟨u, hu, rfl⟩, _, ⟨t, ht, rfl⟩, rfl⟩ := h
  refine ⟨?_, ?_⟩
  · convert hu using 1; ext; simp
  · convert ht using 1; ext; simp

end Separable

section Convolution

variable {φ₁ φ₂ : E → EReal} {x₀ : E} {r : ℝ}

omit [NormedSpace ℝ E] in
theorem mem_graph_convConstraint {q : E × (E × E)} :
    q ∈ graph (convConstraint : E → Set (E × E)) ↔ q.2.1 + q.2.2 = q.1 := Iff.rfl

theorem convex_graph_convConstraint : Convex ℝ (graph (convConstraint : E → Set (E × E))) := by
  intro a ha b hb s t _ _ _
  rw [mem_graph_convConstraint] at *
  simp only [Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst]
  rw [← ha, ← hb, smul_add, smul_add]
  abel

omit [NormedSpace ℝ E] in
theorem isClosed_graph_convConstraint : IsClosed (graph (convConstraint : E → Set (E × E))) :=
  isClosed_eq ((continuous_fst.comp continuous_snd).add (continuous_snd.comp continuous_snd))
    continuous_fst

/-- [Mordukhovich 2018, proof of Thm. 4.4]: the coderivative of `G(x) = {(x₁, x₂) | x₁ + x₂ = x}`
is `D*G(x₀, (x₁, x₂))(v₁, v₂) = {v₁}` if `v₁ = v₂` and `∅` otherwise; here, the inclusion
`u ∈ D*G(x₀, (x₁, x₂))(v₁, v₂) ⟹ u = v₁ = v₂`. -/
theorem eq_of_mem_coderiv_convConstraint {p₀ : E × E} (hp₀ : p₀ ∈ convConstraint x₀)
    {u : StrongDual ℝ E} {v : StrongDual ℝ (E × E)} (hu : u ∈ coderiv convConstraint x₀ p₀ v) :
    u = v.comp (ContinuousLinearMap.inl ℝ E E) ∧ u = v.comp (ContinuousLinearMap.inr ℝ E E) := by
  have h := (mem_normalCone_of_convex convex_graph_convConstraint
    (show (x₀, p₀) ∈ graph convConstraint from hp₀)).1 hu
  have key : ∀ d d₁ d₂ : E, d₁ + d₂ = d → u d - v (d₁, d₂) ≤ 0 := by
    intro d d₁ d₂ hd
    have hq : ((x₀, p₀) + (d, (d₁, d₂)) : E × (E × E)) ∈ graph convConstraint := by
      rw [mem_graph_convConstraint]
      simp only [Prod.snd_add, Prod.fst_add]
      rw [← hd, ← (show p₀.1 + p₀.2 = x₀ from hp₀)]
      abel
    have := h _ hq
    simp only [add_sub_cancel_left, ContinuousLinearMap.coprod_apply, neg_apply] at this
    linarith
  have hle : ∀ d d₁ d₂ : E, d₁ + d₂ = d → u d = v (d₁, d₂) := fun d d₁ d₂ hd ↦ by
    have h1 := key d d₁ d₂ hd
    have h2 := key (-d) (-d₁) (-d₂) (by rw [← hd, neg_add])
    rw [map_neg, show ((-d₁, -d₂) : E × E) = -(d₁, d₂) from rfl, map_neg] at h2
    linarith
  exact ⟨ContinuousLinearMap.ext fun d ↦ by simpa using hle d d 0 (add_zero d),
    ContinuousLinearMap.ext fun d ↦ by simpa using hle d 0 d (zero_add d)⟩

variable [FiniteDimensional ℝ E]

/-- [Mordukhovich 2018, proof of Thm. 4.4]: the qualification condition (4.3) holds for the
marginal representation (4.8) of the infimal convolution, with no assumption on `φ₁, φ₂`. -/
theorem convCost_qc {p₀ : E × E} (hp₀ : p₀ ∈ convConstraint x₀) :
    ∀ w ∈ singularSubdiff (convCost φ₁ φ₂) (x₀, p₀),
      -w ∈ normalCone (graph convConstraint) (x₀, p₀) → w = 0 := by
  intro w hw hN
  rw [show singularSubdiff (convCost φ₁ φ₂) (x₀, p₀) = _ from
    singularSubdiff_comp_snd (E := E) (fun p : E × E ↦ φ₁ p.1 + φ₂ p.2) (x₀, p₀)] at hw
  obtain ⟨t, -, rfl⟩ := hw
  have h0 : (0 : StrongDual ℝ E) ∈ coderiv convConstraint x₀ p₀ t := by
    change _ ∈ normalCone _ _
    convert hN using 1
    ext <;> simp
  obtain ⟨h1, h2⟩ := eq_of_mem_coderiv_convConstraint hp₀ h0
  have ht : t = 0 := by
    rw [← ContinuousLinearMap.coprod_comp_inl_inr t, ← h1, ← h2]
    ext <;> simp
  subst ht
  exact ContinuousLinearMap.zero_comp _

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The cost of (4.8) is lower semicontinuous around `(x₀, (x₁, x₂))` if `φ₁, φ₂` are lower
semicontinuous around `x₁, x₂` and not `⊥` there. -/
theorem exists_lowerSemicontinuousOn_convCost {p₀ : E × E}
    (h₁ : ∃ U ∈ 𝓝 p₀.1, LowerSemicontinuousOn φ₁ U) (h₂ : ∃ U ∈ 𝓝 p₀.2, LowerSemicontinuousOn φ₂ U)
    (hb₁ : φ₁ p₀.1 ≠ ⊥) (hb₂ : φ₂ p₀.2 ≠ ⊥) :
    ∃ W ∈ 𝓝 (x₀, p₀), LowerSemicontinuousOn (convCost φ₁ φ₂) W := by
  obtain ⟨U₁, hU₁, l₁⟩ := h₁
  obtain ⟨U₂, hU₂, l₂⟩ := h₂
  set V₁ := U₁ ∩ {x | ⊥ < φ₁ x}
  set V₂ := U₂ ∩ {x | ⊥ < φ₂ x}
  have hV₁ : V₁ ∈ 𝓝 p₀.1 := inter_mem hU₁
    (lowerSemicontinuousAt_of_lowerSemicontinuousOn hU₁ l₁ ⊥ (bot_lt_iff_ne_bot.2 hb₁))
  have hV₂ : V₂ ∈ 𝓝 p₀.2 := inter_mem hU₂
    (lowerSemicontinuousAt_of_lowerSemicontinuousOn hU₂ l₂ ⊥ (bot_lt_iff_ne_bot.2 hb₂))
  refine ⟨univ ×ˢ (V₁ ×ˢ V₂), prod_mem_nhds univ_mem (prod_mem_nhds hV₁ hV₂), fun q hq ↦ ?_⟩
  have A : LowerSemicontinuousWithinAt (fun q : E × (E × E) ↦ φ₁ q.2.1) (univ ×ˢ (V₁ ×ˢ V₂)) q :=
    (l₁.mono (inter_subset_left : V₁ ⊆ U₁)).comp
    (continuous_fst.comp continuous_snd).continuousOn
    (fun q (hq : q ∈ univ ×ˢ (V₁ ×ˢ V₂)) ↦ hq.2.1) q hq
  have B : LowerSemicontinuousWithinAt (fun q : E × (E × E) ↦ φ₂ q.2.2) (univ ×ˢ (V₁ ×ˢ V₂)) q :=
    (l₂.mono (inter_subset_left : V₂ ⊆ U₂)).comp
    (continuous_snd.comp continuous_snd).continuousOn
    (fun q (hq : q ∈ univ ×ˢ (V₁ ×ˢ V₂)) ↦ hq.2.2) q hq
  exact LowerSemicontinuousWithinAt.add' A B
    (EReal.continuousAt_add (Or.inr hq.2.2.2.ne') (Or.inl hq.2.1.2.ne'))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A point of `C(x₀)` with `(φ₁ ⊕ φ₂)(x₀)` finite has finite values `φ₁ x₁`, `φ₂ x₂`. -/
theorem exists_coe_of_mem_convMap (hr : infConv φ₁ φ₂ x₀ = r) {p₀ : E × E}
    (hp : p₀ ∈ convMap φ₁ φ₂ x₀) : ∃ a₁ a₂ : ℝ, φ₁ p₀.1 = a₁ ∧ φ₂ p₀.2 = a₂ :=
  exists_coe_of_add_eq_coe (hp.2.trans hr)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- On the constraint set `x₁ + x₂ = x₀`, the values `φ₁ x₁`, `φ₂ x₂` are not `⊥` when
`(φ₁ ⊕ φ₂)(x₀)` is finite. -/
theorem ne_bot_of_mem_convConstraint (hr : infConv φ₁ φ₂ x₀ = r) {p₀ : E × E}
    (hp : p₀ ∈ convConstraint x₀) : φ₁ p₀.1 ≠ ⊥ ∧ φ₂ p₀.2 ≠ ⊥ := by
  have hle : (r : EReal) ≤ φ₁ p₀.1 + φ₂ p₀.2 := by
    rw [← hr]; exact marginal_le (φ := convCost φ₁ φ₂) (G := convConstraint) hp
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [h, EReal.bot_add] at hle; exact EReal.coe_ne_bot r (le_bot_iff.1 hle)
  · rw [h, EReal.add_bot] at hle; exact EReal.coe_ne_bot r (le_bot_iff.1 hle)

/-- The last step of [Mordukhovich 2018, proof of Thm. 4.4]: `x ∈ u + D*G(x₀, p₀)(v)` with
`(u, v) ∈ ∂φ(x₀, p₀)`, `φ(x, (x₁, x₂)) = φ₁ x₁ + φ₂ x₂`, gives `x ∈ ∂φ₁(x₁) ∩ ∂φ₂(x₂)`. -/
theorem mem_inter_subdiff_of_convCost {p₀ : E × E} (hp : p₀ ∈ convConstraint x₀) {a₁ a₂ : ℝ}
    (ha₁ : φ₁ p₀.1 = a₁) (ha₂ : φ₂ p₀.2 = a₂) (h₁ : ∃ U ∈ 𝓝 p₀.1, LowerSemicontinuousOn φ₁ U)
    (h₂ : ∃ U ∈ 𝓝 p₀.2, LowerSemicontinuousOn φ₂ U) {x u : StrongDual ℝ E}
    {v : StrongDual ℝ (E × E)} (huv : u.coprod v ∈ subdiff (convCost φ₁ φ₂) (x₀, p₀))
    (hxu : x - u ∈ coderiv convConstraint x₀ p₀ v) : x ∈ subdiff φ₁ p₀.1 ∩ subdiff φ₂ p₀.2 := by
  rw [show subdiff (convCost φ₁ φ₂) (x₀, p₀) = _ from
    subdiff_comp_snd (E := E) (fun p : E × E ↦ φ₁ p.1 + φ₂ p.2) (x₀, p₀)] at huv
  obtain ⟨t, ht, hte⟩ := huv
  replace hte : (0 : StrongDual ℝ E).coprod t = u.coprod v := (comp_snd_eq_coprod t).symm.trans hte
  have hu : 0 = u := by simpa using congrArg (fun ℓ ↦ ℓ.comp (ContinuousLinearMap.inl ℝ E _)) hte
  have hv : t = v := by simpa using congrArg (fun ℓ ↦ ℓ.comp (ContinuousLinearMap.inr ℝ E _)) hte
  rw [← hu, sub_zero, ← hv] at hxu
  obtain ⟨hx1, hx2⟩ := eq_of_mem_coderiv_convConstraint hp hxu
  obtain ⟨ht1, ht2⟩ := subdiff_sep_subset (a := p₀.1) (b := p₀.2) ha₁ ha₂ h₁ h₂ ht
  exact ⟨hx1 ▸ ht1, hx2 ▸ ht2⟩

/-- The singular counterpart of `mem_inter_subdiff_of_convCost`. -/
theorem mem_inter_singularSubdiff_of_convCost {p₀ : E × E} (hp : p₀ ∈ convConstraint x₀)
    {a₁ a₂ : ℝ} (ha₁ : φ₁ p₀.1 = a₁) (ha₂ : φ₂ p₀.2 = a₂)
    (h₁ : ∃ U ∈ 𝓝 p₀.1, LowerSemicontinuousOn φ₁ U)
    (h₂ : ∃ U ∈ 𝓝 p₀.2, LowerSemicontinuousOn φ₂ U) {x u : StrongDual ℝ E}
    {v : StrongDual ℝ (E × E)} (huv : u.coprod v ∈ singularSubdiff (convCost φ₁ φ₂) (x₀, p₀))
    (hxu : x - u ∈ coderiv convConstraint x₀ p₀ v) :
    x ∈ singularSubdiff φ₁ p₀.1 ∩ singularSubdiff φ₂ p₀.2 := by
  rw [show singularSubdiff (convCost φ₁ φ₂) (x₀, p₀) = _ from
    singularSubdiff_comp_snd (E := E) (fun p : E × E ↦ φ₁ p.1 + φ₂ p.2) (x₀, p₀)] at huv
  obtain ⟨t, ht, hte⟩ := huv
  replace hte : (0 : StrongDual ℝ E).coprod t = u.coprod v := (comp_snd_eq_coprod t).symm.trans hte
  have hu : 0 = u := by simpa using congrArg (fun ℓ ↦ ℓ.comp (ContinuousLinearMap.inl ℝ E _)) hte
  have hv : t = v := by simpa using congrArg (fun ℓ ↦ ℓ.comp (ContinuousLinearMap.inr ℝ E _)) hte
  rw [← hu, sub_zero, ← hv] at hxu
  obtain ⟨hx1, hx2⟩ := eq_of_mem_coderiv_convConstraint hp hxu
  obtain ⟨ht1, ht2⟩ := singularSubdiff_sep_subset (a := p₀.1) (b := p₀.2) ha₁ ha₂ h₁ h₂ ht
  exact ⟨hx1 ▸ ht1, hx2 ▸ ht2⟩

/-- Thm. 4.4(i) of [Mordukhovich 2018] (basic subgradients of infimal convolutions): let
`(φ₁ ⊕ φ₂)(x₀) = r` be finite, `(x₁, x₂) ∈ C(x₀)`, `φ₁, φ₂` l.s.c. around `x₁, x₂`, and let the
convolution mapping (4.7) be `(φ₁ ⊕ φ₂)`-inner semicontinuous at `(x₀, (x₁, x₂))`. Then
`∂(φ₁ ⊕ φ₂)(x₀) ⊆ ∂φ₁(x₁) ∩ ∂φ₂(x₂)`. The book's version with inner semicontinuity of `C` is
`subdiff_infConv_subset_of_innerSemicontinuousAt`. -/
theorem subdiff_infConv_subset (hr : infConv φ₁ φ₂ x₀ = r) {x₁ x₂ : E}
    (hp : (x₁, x₂) ∈ convMap φ₁ φ₂ x₀)
    (hisc : (x₁, x₂) ∈ innerLimit (funNhds (infConv φ₁ φ₂) x₀) (convMap φ₁ φ₂))
    (h₁ : ∃ U ∈ 𝓝 x₁, LowerSemicontinuousOn φ₁ U) (h₂ : ∃ U ∈ 𝓝 x₂, LowerSemicontinuousOn φ₂ U) :
    subdiff (infConv φ₁ φ₂) x₀ ⊆ subdiff φ₁ x₁ ∩ subdiff φ₂ x₂ := by
  obtain ⟨a₁, a₂, ha₁, ha₂⟩ := exists_coe_of_mem_convMap hr hp
  obtain ⟨hb₁, hb₂⟩ := ne_bot_of_mem_convConstraint hr hp.1
  obtain ⟨W, hW, hl⟩ :=
    exists_lowerSemicontinuousOn_convCost (x₀ := x₀) (p₀ := (x₁, x₂)) h₁ h₂ hb₁ hb₂
  rw [infConv_eq_marginal] at hr hisc ⊢
  rw [convMap_eq_argminMap] at hp hisc
  intro x hx
  obtain ⟨u, v, huv, hxu⟩ := subdiff_marginal_subset hr hp hisc
    (locallyClosed_epi_of_lowerSemicontinuousOn hW hl r)
    ⟨1, one_pos, isClosed_graph_convConstraint.inter isClosed_closedBall⟩ (convCost_qc hp.1) hx
  exact mem_inter_subdiff_of_convCost hp.1 ha₁ ha₂ h₁ h₂ huv hxu

/-- Thm. 4.4(i) of [Mordukhovich 2018] (singular subgradients of infimal convolutions): under the
assumptions of `subdiff_infConv_subset`, if moreover `φ₁ ⊕ φ₂` is lower semicontinuous at `x₀`,
then `∂^∞(φ₁ ⊕ φ₂)(x₀) ⊆ ∂^∞φ₁(x₁) ∩ ∂^∞φ₂(x₂)`. -/
theorem singularSubdiff_infConv_subset (hr : infConv φ₁ φ₂ x₀ = r) {x₁ x₂ : E}
    (hp : (x₁, x₂) ∈ convMap φ₁ φ₂ x₀)
    (hisc : (x₁, x₂) ∈ innerLimit (funNhds (infConv φ₁ φ₂) x₀) (convMap φ₁ φ₂))
    (hlsc : LowerSemicontinuousAt (infConv φ₁ φ₂) x₀)
    (h₁ : ∃ U ∈ 𝓝 x₁, LowerSemicontinuousOn φ₁ U) (h₂ : ∃ U ∈ 𝓝 x₂, LowerSemicontinuousOn φ₂ U) :
    singularSubdiff (infConv φ₁ φ₂) x₀ ⊆ singularSubdiff φ₁ x₁ ∩ singularSubdiff φ₂ x₂ := by
  obtain ⟨a₁, a₂, ha₁, ha₂⟩ := exists_coe_of_mem_convMap hr hp
  obtain ⟨hb₁, hb₂⟩ := ne_bot_of_mem_convConstraint hr hp.1
  obtain ⟨W, hW, hl⟩ :=
    exists_lowerSemicontinuousOn_convCost (x₀ := x₀) (p₀ := (x₁, x₂)) h₁ h₂ hb₁ hb₂
  rw [infConv_eq_marginal] at hr hisc hlsc ⊢
  rw [convMap_eq_argminMap] at hp hisc
  intro x hx
  obtain ⟨u, v, huv, hxu⟩ := singularSubdiff_marginal_subset hr hp hisc hlsc
    (locallyClosed_epi_of_lowerSemicontinuousOn hW hl r)
    ⟨1, one_pos, isClosed_graph_convConstraint.inter isClosed_closedBall⟩ (convCost_qc hp.1) hx
  exact mem_inter_singularSubdiff_of_convCost hp.1 ha₁ ha₂ h₁ h₂ huv hxu

/-- Thm. 4.4(i) of [Mordukhovich 2018] with the book's hypothesis: the convolution mapping `C` is
inner semicontinuous at `(x₀, (x₁, x₂))` (relative to `dom C`), and the infimum in (4.6) is
attained near `x₀` wherever it is `< ⊤`. Then both inclusions of Thm. 4.4(i) hold. -/
theorem infConv_subset_of_innerSemicontinuousAt (hr : infConv φ₁ φ₂ x₀ = r) {x₁ x₂ : E}
    (hp : (x₁, x₂) ∈ convMap φ₁ φ₂ x₀) (hisc : InnerSemicontinuousAt (convMap φ₁ φ₂) x₀ (x₁, x₂))
    (hatt : ∀ᶠ x in 𝓝 x₀, infConv φ₁ φ₂ x ≠ ⊤ → (convMap φ₁ φ₂ x).Nonempty)
    (h₁ : ∃ U ∈ 𝓝 x₁, LowerSemicontinuousOn φ₁ U) (h₂ : ∃ U ∈ 𝓝 x₂, LowerSemicontinuousOn φ₂ U) :
    subdiff (infConv φ₁ φ₂) x₀ ⊆ subdiff φ₁ x₁ ∩ subdiff φ₂ x₂ ∧
      singularSubdiff (infConv φ₁ φ₂) x₀ ⊆ singularSubdiff φ₁ x₁ ∩ singularSubdiff φ₂ x₂ := by
  obtain ⟨hb₁, hb₂⟩ := ne_bot_of_mem_convConstraint hr hp.1
  obtain ⟨W, hW, hl⟩ :=
    exists_lowerSemicontinuousOn_convCost (x₀ := x₀) (p₀ := (x₁, x₂)) h₁ h₂ hb₁ hb₂
  have hisc' := mem_innerLimit_funNhds_of_innerSemicontinuousAt (φ := convCost φ₁ φ₂)
    (G := convConstraint) hr hisc hatt
  have hlsc := lowerSemicontinuousAt_marginal_of_innerSemicontinuousAt (φ := convCost φ₁ φ₂)
    (G := convConstraint) hp hisc hatt (lowerSemicontinuousAt_of_lowerSemicontinuousOn hW hl)
  exact ⟨subdiff_infConv_subset hr hp hisc' h₁ h₂,
    singularSubdiff_infConv_subset hr hp hisc' hlsc h₁ h₂⟩

/-- Thm. 4.4(ii) of [Mordukhovich 2018] (subgradients of infimal convolutions under local
boundedness): let `(φ₁ ⊕ φ₂)(x₀) = r` be finite, `φ₁, φ₂` l.s.c., the convolution mapping `C`
locally bounded around `x₀`, and the infimum in (4.6) attained near `x₀` wherever it is `< ⊤`
(implicit in the book). Then `∂(φ₁ ⊕ φ₂)(x₀) ⊆ ⋃_{(x₁, x₂) ∈ C(x₀)} ∂φ₁(x₁) ∩ ∂φ₂(x₂)` and
`∂^∞(φ₁ ⊕ φ₂)(x₀) ⊆ ⋃_{(x₁, x₂) ∈ C(x₀)} ∂^∞φ₁(x₁) ∩ ∂^∞φ₂(x₂)`. -/
theorem infConv_subset_of_locallyBoundedAt (hr : infConv φ₁ φ₂ x₀ = r)
    (hlb : LocallyBoundedAt (convMap φ₁ φ₂) x₀)
    (hatt : ∀ᶠ x in 𝓝 x₀, infConv φ₁ φ₂ x ≠ ⊤ → (convMap φ₁ φ₂ x).Nonempty)
    (hφ₁ : LowerSemicontinuous φ₁) (hφ₂ : LowerSemicontinuous φ₂) :
    subdiff (infConv φ₁ φ₂) x₀ ⊆ ⋃ p ∈ convMap φ₁ φ₂ x₀, subdiff φ₁ p.1 ∩ subdiff φ₂ p.2 ∧
      singularSubdiff (infConv φ₁ φ₂) x₀ ⊆
        ⋃ p ∈ convMap φ₁ φ₂ x₀, singularSubdiff φ₁ p.1 ∩ singularSubdiff φ₂ p.2 := by
  have h₁ : ∀ a : E, ∃ U ∈ 𝓝 a, LowerSemicontinuousOn φ₁ U := fun _ ↦
    ⟨univ, univ_mem, hφ₁.lowerSemicontinuousOn univ⟩
  have h₂ : ∀ a : E, ∃ U ∈ 𝓝 a, LowerSemicontinuousOn φ₂ U := fun _ ↦
    ⟨univ, univ_mem, hφ₂.lowerSemicontinuousOn univ⟩
  have hφ : ∀ y ∈ convConstraint x₀, ∃ U ∈ 𝓝 (x₀, y), LowerSemicontinuousOn (convCost φ₁ φ₂) U :=
    fun y hy ↦ exists_lowerSemicontinuousOn_convCost (h₁ _) (h₂ _)
      (ne_bot_of_mem_convConstraint hr hy).1 (ne_bot_of_mem_convConstraint hr hy).2
  rw [infConv_eq_marginal] at hr hatt ⊢
  rw [convMap_eq_argminMap] at hlb hatt ⊢
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨p, hp, u, v, huv, hxu⟩ := mem_iUnion₂.1 (subdiff_marginal_subset_of_locallyBoundedAt hr
      hlb hatt isClosed_graph_convConstraint hφ (fun y hy ↦ convCost_qc hy.1) hx)
    obtain ⟨a₁, a₂, ha₁, ha₂⟩ := exists_coe_of_mem_convMap hr hp
    exact mem_iUnion₂.2 ⟨p, hp, mem_inter_subdiff_of_convCost hp.1 ha₁ ha₂ (h₁ _) (h₂ _) huv hxu⟩
  · obtain ⟨p, hp, u, v, huv, hxu⟩ := mem_iUnion₂.1
      (singularSubdiff_marginal_subset_of_locallyBoundedAt hr hlb hatt
        isClosed_graph_convConstraint hφ (fun y hy ↦ convCost_qc hy.1) hx)
    obtain ⟨a₁, a₂, ha₁, ha₂⟩ := exists_coe_of_mem_convMap hr hp
    exact mem_iUnion₂.2 ⟨p, hp,
      mem_inter_singularSubdiff_of_convCost hp.1 ha₁ ha₂ (h₁ _) (h₂ _) huv hxu⟩

end Convolution

end VariationalAnalysis
