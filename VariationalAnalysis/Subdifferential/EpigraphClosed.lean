/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Semicontinuity.Basic
import VariationalAnalysis.Subdifferential.Lipschitz

/-!
# Locally closed epigraphs and lower semicontinuity

The standing assumption of [Mordukhovich 2018] for extended-real-valued functions is lower
semicontinuity around the point of interest; the proofs only use that the epigraph is locally
closed around `(x₀, φ x₀)`. This file relates the two and proves the facts about sums
`φ₁ + φ₂` needed for the subdifferential sum rules of Sect. 2.4.

## Main results

* `lowerSemicontinuousAt_of_locallyClosed_epi`: a locally closed epigraph gives lower
  semicontinuity at the point.
* `locallyClosed_epi_of_lowerSemicontinuousOn`: lower semicontinuity on a neighborhood gives a
  locally closed epigraph.
* `exists_tendsto_split_of_mem_epi_add`: points `(xₖ, αₖ) → (x₀, φ₁ x₀ + φ₂ x₀)` of
  `epi (φ₁ + φ₂)` split as `αₖ = aₖ + (αₖ - aₖ)` with `(xₖ, aₖ) ∈ epi φ₁`,
  `(xₖ, αₖ - aₖ) ∈ epi φ₂` and `aₖ → φ₁ x₀`.
* `locallyClosed_epi_add_of_locallyClosed`: the epigraph of `φ₁ + φ₂` is locally closed if those
  of `φ₁` and `φ₂` are.
-/

open Filter Topology Set Metric

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E]
variable {φ φ₁ φ₂ : E → EReal} {x₀ : E} {r r₁ r₂ : ℝ}

/-- A function whose epigraph is locally closed around `(x₀, φ x₀)`, with `φ x₀` finite, is lower
semicontinuous at `x₀`. -/
theorem lowerSemicontinuousAt_of_locallyClosed_epi (hr : φ x₀ = r)
    (hloc : ∃ ρ > 0, IsClosed (φ.Epi univ ∩ closedBall ((x₀, r) : E × ℝ) ρ)) :
    LowerSemicontinuousAt φ x₀ := by
  obtain ⟨ρ, hρ, hcl⟩ := hloc
  rw [lowerSemicontinuousAt_iff]
  intro y hy
  rw [hr] at hy
  obtain ⟨c₀, hyc₀, hc₀r⟩ := EReal.lt_iff_exists_real_btwn.1 hy
  have hc₀r' : c₀ < r := EReal.coe_lt_coe_iff.1 hc₀r
  set c := max c₀ (r - ρ / 2)
  have hyc : y < c := hyc₀.trans_le (EReal.coe_le_coe_iff.2 (le_max_left _ _))
  have hcr : c < r := max_lt hc₀r' (by linarith)
  have hρc : r - ρ ≤ c := (by linarith : r - ρ ≤ r - ρ / 2).trans (le_max_right _ _)
  by_contra hev
  rw [Filter.not_eventually] at hev
  have hfreq : ∃ᶠ x in 𝓝 x₀, ((x, c) : E × ℝ) ∈ φ.Epi univ ∩ closedBall ((x₀, r) : E × ℝ) ρ :=
    (hev.and_eventually (ball_mem_nhds x₀ hρ)).mono fun x hx ↦ by
      refine ⟨⟨mem_univ _, (not_lt.1 hx.1).trans hyc.le⟩, ?_⟩
      rw [mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq, abs_of_nonpos (by linarith)]
      exact ⟨(mem_ball.1 hx.2).le, by linarith⟩
  have hmem : ((x₀, c) : E × ℝ) ∈ φ.Epi univ ∩ closedBall ((x₀, r) : E × ℝ) ρ :=
    hcl.mem_of_frequently_of_tendsto hfreq ((continuous_id.prodMk continuous_const).tendsto x₀)
  have : φ x₀ ≤ c := hmem.1.2
  rw [hr, EReal.coe_le_coe_iff] at this
  linarith

/-- A function lower semicontinuous on a neighborhood of `x₀` has an epigraph locally closed
around every `(x₀, r)`. -/
theorem locallyClosed_epi_of_lowerSemicontinuousOn {U : Set E} (hU : U ∈ 𝓝 x₀)
    (hφ : LowerSemicontinuousOn φ U) (r : ℝ) :
    ∃ ρ > 0, IsClosed (φ.Epi univ ∩ closedBall ((x₀, r) : E × ℝ) ρ) := by
  obtain ⟨ρ, hρ, hsub⟩ := nhds_basis_closedBall.mem_iff.1 hU
  refine ⟨ρ, hρ, isClosed_of_closure_subset fun q hq ↦ ?_⟩
  obtain ⟨z, hz, hzq⟩ := mem_closure_iff_seq_limit.1 hq
  have hqB : q ∈ closedBall ((x₀, r) : E × ℝ) ρ :=
    isClosed_closedBall.mem_of_tendsto hzq (Eventually.of_forall fun k ↦ (hz k).2)
  have hB : ∀ p ∈ closedBall ((x₀, r) : E × ℝ) ρ, p.1 ∈ U := fun p hp ↦ hsub (by
    rw [mem_closedBall, Prod.dist_eq, max_le_iff] at hp
    exact mem_closedBall.2 hp.1)
  refine ⟨⟨mem_univ _, ?_⟩, hqB⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨c, h1, h2⟩ := exists_between hlt
  have hz1 : Tendsto (fun k ↦ (z k).1) atTop (𝓝[U] q.1) :=
    tendsto_nhdsWithin_iff.2 ⟨(continuous_fst.tendsto q).comp hzq,
      Eventually.of_forall fun k ↦ hB _ (hz k).2⟩
  have hz2 : ∀ᶠ k in atTop, ((z k).2 : EReal) < c :=
    (EReal.tendsto_coe.2 ((continuous_snd.tendsto q).comp hzq)).eventually (eventually_lt_nhds h1)
  obtain ⟨k, hk1, hk2⟩ := ((hz1.eventually (lowerSemicontinuousWithinAt_iff.1
    (hφ q.1 (hB q hqB)) c h2)).and hz2).exists
  exact absurd (hk1.trans_le (hz k).1.2) (not_lt.2 hk2.le)

omit [NormedAddCommGroup E] in
/-- Near `x₀`, lower bounds `r₁ - η < φ₁ x`, `r₂ - η < φ₂ x` and `φ₁ x + φ₂ x ≤ α` make `φ₁ x`
finite, with `r₁ - η < φ₁ x` and `φ₂ x ≤ α - φ₁ x`. -/
theorem exists_eq_coe_of_add_le {x : E} {α η : ℝ} (h₁ : ((r₁ - η : ℝ) : EReal) < φ₁ x)
    (h₂ : ((r₂ - η : ℝ) : EReal) < φ₂ x) (h : φ₁ x + φ₂ x ≤ α) :
    ∃ a : ℝ, φ₁ x = a ∧ r₁ - η < a ∧ φ₂ x ≤ ((α - a : ℝ) : EReal) ∧ r₂ - η < α - a := by
  have hne₁ : φ₁ x ≠ ⊥ := ne_bot_of_gt h₁
  have hne₂ : φ₂ x ≠ ⊥ := ne_bot_of_gt h₂
  have hne₁' : φ₁ x ≠ ⊤ := by
    intro htop
    rw [htop, EReal.top_add_of_ne_bot hne₂] at h
    exact EReal.coe_ne_top _ (top_le_iff.1 h)
  refine ⟨(φ₁ x).toReal, (EReal.coe_toReal hne₁' hne₁).symm, ?_, ?_, ?_⟩
  · rw [← EReal.coe_lt_coe_iff, EReal.coe_toReal hne₁' hne₁]; exact h₁
  · rw [← add_coe_le_coe_iff, EReal.coe_toReal hne₁' hne₁, add_comm]; exact h
  · have : φ₂ x ≤ ((α - (φ₁ x).toReal : ℝ) : EReal) := by
      rw [← add_coe_le_coe_iff, EReal.coe_toReal hne₁' hne₁, add_comm]; exact h
    exact EReal.coe_lt_coe_iff.1 (h₂.trans_le this)

/-- [Mordukhovich 2018, proof of Thm. 2.19]: if `φ₁, φ₂` are lower semicontinuous at `x₀` with
finite values `r₁, r₂`, and `(xₖ, αₖ) → (x₀, r₁ + r₂)` with `(xₖ, αₖ) ∈ epi (φ₁ + φ₂)` for
all large `k`, then there are
`aₖ → r₁` with `φ₁ xₖ ≤ aₖ` and `φ₂ xₖ ≤ αₖ - aₖ` for all large `k`. -/
theorem exists_tendsto_split_of_mem_epi_add (hr₁ : φ₁ x₀ = r₁) (hr₂ : φ₂ x₀ = r₂)
    (hl₁ : LowerSemicontinuousAt φ₁ x₀) (hl₂ : LowerSemicontinuousAt φ₂ x₀) {y : ℕ → E × ℝ}
    (hy : Tendsto y atTop (𝓝 (x₀, r₁ + r₂)))
    (hmem : ∀ᶠ k in atTop, y k ∈ (fun x ↦ φ₁ x + φ₂ x).Epi univ) :
    ∃ a : ℕ → ℝ, Tendsto a atTop (𝓝 r₁) ∧
      ∀ᶠ k in atTop, φ₁ (y k).1 ≤ a k ∧ φ₂ (y k).1 ≤ (((y k).2 - a k : ℝ) : EReal) := by
  have hx : Tendsto (fun k ↦ (y k).1) atTop (𝓝 x₀) := (continuous_fst.tendsto _).comp hy
  have hα : Tendsto (fun k ↦ (y k).2) atTop (𝓝 (r₁ + r₂)) := (continuous_snd.tendsto _).comp hy
  have lb : ∀ η > 0, ∀ᶠ k in atTop, ((r₁ - η : ℝ) : EReal) < φ₁ (y k).1 ∧
      ((r₂ - η : ℝ) : EReal) < φ₂ (y k).1 := fun η hη ↦
    (hx.eventually (lowerSemicontinuousAt_iff.1 hl₁ _
      (by rw [hr₁]; exact EReal.coe_lt_coe_iff.2 (by linarith)))).and
      (hx.eventually (lowerSemicontinuousAt_iff.1 hl₂ _
        (by rw [hr₂]; exact EReal.coe_lt_coe_iff.2 (by linarith))))
  have hsplit : ∀ᶠ k in atTop, ∃ a : ℝ, φ₁ (y k).1 = a ∧ r₁ - 1 < a ∧
      φ₂ (y k).1 ≤ (((y k).2 - a : ℝ) : EReal) ∧ r₂ - 1 < (y k).2 - a :=
    ((lb 1 one_pos).and hmem).mono fun k hk ↦ exists_eq_coe_of_add_le hk.1.1 hk.1.2 hk.2.2
  refine ⟨fun k ↦ (φ₁ (y k).1).toReal, tendsto_order.2 ⟨fun b hb ↦ ?_, fun b hb ↦ ?_⟩, ?_⟩
  · filter_upwards [lb (r₁ - b) (by linarith), hsplit] with k hk hsk
    obtain ⟨a, ha, -⟩ := hsk
    rw [ha, EReal.toReal_coe]
    have := hk.1
    rw [ha, sub_sub_cancel] at this
    exact EReal.coe_lt_coe_iff.1 this
  · filter_upwards [lb ((b - r₁) / 2) (by linarith), hsplit,
      hα.eventually (gt_mem_nhds (show r₁ + r₂ < r₁ + r₂ + (b - r₁) / 2 by linarith))]
      with k hk hsk hαk
    obtain ⟨a, ha, -, hle, -⟩ := hsk
    rw [ha, EReal.toReal_coe]
    have := EReal.coe_lt_coe_iff.1 (hk.2.trans_le hle)
    linarith
  · filter_upwards [hsplit] with k hsk
    obtain ⟨a, ha, -, hle, -⟩ := hsk
    rw [ha, EReal.toReal_coe]
    exact ⟨le_rfl, hle⟩

/-- The epigraph of `φ₁ + φ₂` is locally closed around `(x₀, r₁ + r₂)` if those of `φ₁` and `φ₂`
are locally closed around `(x₀, r₁)` and `(x₀, r₂)`, where `rᵢ = φᵢ x₀`. -/
theorem locallyClosed_epi_add_of_locallyClosed (hr₁ : φ₁ x₀ = r₁) (hr₂ : φ₂ x₀ = r₂)
    (hloc₁ : ∃ ρ > 0, IsClosed (φ₁.Epi univ ∩ closedBall ((x₀, r₁) : E × ℝ) ρ))
    (hloc₂ : ∃ ρ > 0, IsClosed (φ₂.Epi univ ∩ closedBall ((x₀, r₂) : E × ℝ) ρ)) :
    ∃ ρ > 0, IsClosed ((fun x ↦ φ₁ x + φ₂ x).Epi univ ∩
      closedBall ((x₀, r₁ + r₂) : E × ℝ) ρ) := by
  have hl₁ := lowerSemicontinuousAt_of_locallyClosed_epi hr₁ hloc₁
  have hl₂ := lowerSemicontinuousAt_of_locallyClosed_epi hr₂ hloc₂
  obtain ⟨ρ₁, hρ₁, hcl₁⟩ := hloc₁
  obtain ⟨ρ₂, hρ₂, hcl₂⟩ := hloc₂
  set η := min ρ₁ ρ₂ / 4
  have hη : 0 < η := by positivity
  have hη₁ : ((r₁ - η : ℝ) : EReal) < φ₁ x₀ := by
    rw [hr₁]; exact EReal.coe_lt_coe_iff.2 (by linarith)
  have hη₂ : ((r₂ - η : ℝ) : EReal) < φ₂ x₀ := by
    rw [hr₂]; exact EReal.coe_lt_coe_iff.2 (by linarith)
  have hlb := (lowerSemicontinuousAt_iff.1 hl₁ _ hη₁).and (lowerSemicontinuousAt_iff.1 hl₂ _ hη₂)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hlb
  set ρ := min (δ / 2) η
  have hρ : 0 < ρ := lt_min (by positivity) hη
  refine ⟨ρ, hρ, isClosed_of_closure_subset fun q hq ↦ ?_⟩
  obtain ⟨z, hz, hzq⟩ := mem_closure_iff_seq_limit.1 hq
  have hqB : q ∈ closedBall ((x₀, r₁ + r₂) : E × ℝ) ρ :=
    isClosed_closedBall.mem_of_tendsto hzq (Eventually.of_forall fun k ↦ (hz k).2)
  refine ⟨⟨mem_univ _, ?_⟩, hqB⟩
  have hbd : ∀ k, dist (z k).1 x₀ ≤ ρ ∧ |(z k).2 - (r₁ + r₂)| ≤ ρ := fun k ↦ by
    have := (hz k).2
    rw [mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq] at this
    exact this
  have hsplit : ∀ k, ∃ a : ℝ, φ₁ (z k).1 = a ∧ r₁ - η < a ∧
      φ₂ (z k).1 ≤ (((z k).2 - a : ℝ) : EReal) ∧ r₂ - η < (z k).2 - a := fun k ↦ by
    have h := hball (show dist (z k).1 x₀ < δ by linarith [(hbd k).1, min_le_left (δ / 2) η])
    exact exists_eq_coe_of_add_le h.1 h.2 (hz k).1.2
  choose a ha hlo hle hlo₂ using hsplit
  have hρη : ρ ≤ η := min_le_right _ _
  have hup : ∀ k, a k < r₁ + 2 * η := fun k ↦ by
    have := (abs_le.1 (hbd k).2).2
    linarith [hlo₂ k]
  -- a convergent subsequence of `aₖ`
  obtain ⟨a₀, -, ψ, hψ, ha₀⟩ := tendsto_subseq_of_bounded (x := a)
    (isBounded_Icc (r₁ - η) (r₁ + 2 * η)) fun k ↦ ⟨(hlo k).le, (hup k).le⟩
  have hz₁ : Tendsto (fun k ↦ (z (ψ k)).1) atTop (𝓝 q.1) :=
    (continuous_fst.tendsto q).comp (hzq.comp hψ.tendsto_atTop)
  have hz₂ : Tendsto (fun k ↦ (z (ψ k)).2) atTop (𝓝 q.2) :=
    (continuous_snd.tendsto q).comp (hzq.comp hψ.tendsto_atTop)
  have hηdef : η = min ρ₁ ρ₂ / 4 := rfl
  have hmin₁ : 2 * η ≤ ρ₁ := by linarith [min_le_left ρ₁ ρ₂]
  have hmin₂ : 2 * η ≤ ρ₂ := by linarith [min_le_right ρ₁ ρ₂]
  have h₁ : ((q.1, a₀) : E × ℝ) ∈ φ₁.Epi univ ∩ closedBall ((x₀, r₁) : E × ℝ) ρ₁ := by
    refine hcl₁.mem_of_tendsto (hz₁.prodMk_nhds ha₀) (Eventually.of_forall fun k ↦ ?_)
    refine ⟨⟨mem_univ _, (ha (ψ k)).le⟩, ?_⟩
    simp only [mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq, abs_le,
      Function.comp_apply]
    exact ⟨by linarith [(hbd (ψ k)).1], by linarith [hlo (ψ k)], by linarith [hup (ψ k)]⟩
  have h₂ : ((q.1, q.2 - a₀) : E × ℝ) ∈ φ₂.Epi univ ∩ closedBall ((x₀, r₂) : E × ℝ) ρ₂ := by
    refine hcl₂.mem_of_tendsto (hz₁.prodMk_nhds (hz₂.sub ha₀))
      (Eventually.of_forall fun k ↦ ?_)
    refine ⟨⟨mem_univ _, hle (ψ k)⟩, ?_⟩
    have := abs_le.1 (hbd (ψ k)).2
    simp only [mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq, abs_le,
      Function.comp_apply]
    exact ⟨by linarith [(hbd (ψ k)).1], by linarith [hlo₂ (ψ k)],
      by linarith [hlo (ψ k)]⟩
  calc φ₁ q.1 + φ₂ q.1 ≤ (a₀ : EReal) + ((q.2 - a₀ : ℝ) : EReal) := add_le_add h₁.1.2 h₂.1.2
    _ = q.2 := by rw [← EReal.coe_add, add_sub_cancel]

end VariationalAnalysis
