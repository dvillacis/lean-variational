/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Painlevé–Kuratowski outer limits

The (sequential) Painlevé–Kuratowski outer limit of a set-valued map `F : α → Set E` along a
filter `l`,

  `Lim sup_{x → l} F x = {y | ∃ xₖ → l, yₖ → y with yₖ ∈ F xₖ}`,

following [Mordukhovich 2018, (1.1)] and [Clason–Valkonen, Section 6.1]. The filter `l` encodes
the mode of convergence of the arguments: `𝓝 x₀` for `x → x₀`, `𝓝[Ω] x₀` for `x →Ω x₀`, and
`funNhds φ x₀` for `x →φ x₀` (i.e. `x → x₀` with `φ x → φ x₀`).

## Main declarations

* `outerLimit l F`: the outer limit of `F` along `l`.
* `funNhds φ x₀`: the filter of `φ`-attentive convergence `x →φ x₀` [Mordukhovich 2018, p. 19].
* `outerLimit_nhdsWithin_diag`: a diagonal argument; outer limits of outer limits along
  `x →Ω x₀` are outer limits.
* `isClosed_outerLimit_nhdsWithin`: such outer limits are closed.
-/

open Filter Topology Set

namespace VariationalAnalysis

section Topological

variable {α E : Type*} [TopologicalSpace E]

/-- The Painlevé–Kuratowski outer limit [Mordukhovich 2018, (1.1)] of a set-valued map `F`
along a filter `l`: the set of limits `y = lim yₖ` of sequences `yₖ ∈ F xₖ` with `xₖ → l`. -/
def outerLimit (l : Filter α) (F : α → Set E) : Set E :=
  {y | ∃ a : ℕ → α, ∃ v : ℕ → E, Tendsto a atTop l ∧ Tendsto v atTop (𝓝 y) ∧ ∀ k, v k ∈ F (a k)}

theorem mem_outerLimit {l : Filter α} {F : α → Set E} {y : E} :
    y ∈ outerLimit l F ↔
      ∃ a : ℕ → α, ∃ v : ℕ → E, Tendsto a atTop l ∧ Tendsto v atTop (𝓝 y) ∧
        ∀ k, v k ∈ F (a k) := Iff.rfl

/-- It suffices that `v k ∈ F (a k)` holds for all large `k`. -/
theorem mem_outerLimit_of_eventually {l : Filter α} {F : α → Set E} {y : E} (a : ℕ → α)
    (v : ℕ → E) (ha : Tendsto a atTop l) (hv : Tendsto v atTop (𝓝 y))
    (h : ∀ᶠ k in atTop, v k ∈ F (a k)) : y ∈ outerLimit l F := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  exact ⟨fun k ↦ a (k + N), fun k ↦ v (k + N), (tendsto_add_atTop_iff_nat N).2 ha,
    (tendsto_add_atTop_iff_nat N).2 hv, fun k ↦ hN _ (Nat.le_add_left N k)⟩

theorem outerLimit_mono {l : Filter α} {F G : α → Set E} (h : ∀ᶠ a in l, F a ⊆ G a) :
    outerLimit l F ⊆ outerLimit l G := by
  rintro y ⟨a, v, ha, hv, hF⟩
  exact mem_outerLimit_of_eventually a v ha hv ((ha.eventually h).mono fun k hk ↦ hk (hF k))

theorem outerLimit_mono_filter {l₁ l₂ : Filter α} (h : l₁ ≤ l₂) (F : α → Set E) :
    outerLimit l₁ F ⊆ outerLimit l₂ F := by
  rintro y ⟨a, v, ha, hv, hF⟩
  exact ⟨a, v, ha.mono_right h, hv, hF⟩

/-- Constant sequences: if `l` contains the point `x`, then `F x ⊆ Lim sup_{l} F`. -/
theorem subset_outerLimit {l : Filter α} {x : α} (h : pure x ≤ l) (F : α → Set E) :
    F x ⊆ outerLimit l F := fun y hy ↦
  ⟨fun _ ↦ x, fun _ ↦ y, tendsto_pure.2 (Eventually.of_forall fun _ ↦ rfl) |>.mono_right h,
    tendsto_const_nhds, fun _ ↦ hy⟩

/-- The filter of `φ`-attentive convergence `x →φ x₀` [Mordukhovich 2018, p. 19]:
`x → x₀` together with `φ x → φ x₀`. -/
def funNhds {E β : Type*} [TopologicalSpace E] [TopologicalSpace β] (φ : E → β) (x₀ : E) :
    Filter E :=
  𝓝 x₀ ⊓ comap φ (𝓝 (φ x₀))

theorem tendsto_funNhds_iff {E β : Type*} [TopologicalSpace E] [TopologicalSpace β]
    {φ : E → β} {x₀ : E} {a : ℕ → E} :
    Tendsto a atTop (funNhds φ x₀) ↔
      Tendsto a atTop (𝓝 x₀) ∧ Tendsto (fun k ↦ φ (a k)) atTop (𝓝 (φ x₀)) := by
  simp [funNhds, tendsto_inf, tendsto_comap_iff, Function.comp_def]

theorem pure_le_funNhds {E β : Type*} [TopologicalSpace E] [TopologicalSpace β]
    (φ : E → β) (x₀ : E) : pure x₀ ≤ funNhds φ x₀ :=
  le_inf (pure_le_nhds x₀) (tendsto_pure_nhds φ x₀).le_comap

end Topological

section Metric

variable {E X : Type*} [PseudoMetricSpace E] [PseudoMetricSpace X]

/-- Diagonal argument: if `aₖ →Ω x₀`, `uₖ → y` and eventually `uₖ ∈ Lim sup_{z →Ω aₖ} F z`,
then `y ∈ Lim sup_{z →Ω x₀} F z`. -/
theorem mem_outerLimit_nhdsWithin_of_seq {Ω : Set X} {x₀ : X} {F : X → Set E} {y : E}
    (a : ℕ → X) (u : ℕ → E) (ha : Tendsto a atTop (𝓝[Ω] x₀)) (hu : Tendsto u atTop (𝓝 y))
    (h : ∀ᶠ k in atTop, u k ∈ outerLimit (𝓝[Ω] (a k)) F) :
    y ∈ outerLimit (𝓝[Ω] x₀) F := by
  have haΩ : ∀ᶠ k in atTop, a k ∈ Ω := (tendsto_nhdsWithin_iff.1 ha).2
  have key : ∀ k : ℕ, ∃ b : X, ∃ w : E, u k ∈ outerLimit (𝓝[Ω] (a k)) F →
      b ∈ Ω ∧ dist b (a k) < 1 / (k + 1) ∧ dist w (u k) < 1 / (k + 1) ∧ w ∈ F b := by
    intro k
    by_cases hk : u k ∈ outerLimit (𝓝[Ω] (a k)) F
    · obtain ⟨b, w, hb, hw, hF⟩ := hk
      have hpos : (0 : ℝ) < 1 / (k + 1) := Nat.one_div_pos_of_nat
      have h1 := (tendsto_nhdsWithin_iff.1 hb).2
      have h2 := Metric.tendsto_nhds.1 (tendsto_nhdsWithin_iff.1 hb).1 _ hpos
      have h3 := Metric.tendsto_nhds.1 hw _ hpos
      obtain ⟨j, hj1, hj2, hj3⟩ := (h1.and (h2.and h3)).exists
      exact ⟨b j, w j, fun _ ↦ ⟨hj1, hj2, hj3, hF j⟩⟩
    · exact ⟨a k, u k, fun h' ↦ absurd h' hk⟩
  choose b w hbw using key
  have hlim : Tendsto (fun k : ℕ ↦ (1 : ℝ) / (k + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hb : Tendsto b atTop (𝓝 x₀) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hax := (tendsto_iff_dist_tendsto_zero.1 (tendsto_nhdsWithin_iff.1 ha).1)
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) ?_ (by
      simpa using hlim.add hax)
    filter_upwards [h] with k hk
    have := (hbw k hk).2.1
    rw [one_div] at this
    linarith [dist_triangle (b k) (a k) x₀]
  have hw : Tendsto w atTop (𝓝 y) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hvy := tendsto_iff_dist_tendsto_zero.1 hu
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) ?_ (by
      simpa using hlim.add hvy)
    filter_upwards [h] with k hk
    have := (hbw k hk).2.2.1
    rw [one_div] at this
    linarith [dist_triangle (w k) (u k) y]
  refine mem_outerLimit_of_eventually b w (tendsto_nhdsWithin_iff.2 ⟨hb, ?_⟩) hw ?_
  · filter_upwards [h] with k hk using (hbw k hk).1
  · filter_upwards [h] with k hk using (hbw k hk).2.2.2

/-- The version of `mem_outerLimit_nhdsWithin_of_seq` for unrestricted convergence. -/
theorem mem_outerLimit_nhds_of_seq {x₀ : X} {F : X → Set E} {y : E}
    (a : ℕ → X) (u : ℕ → E) (ha : Tendsto a atTop (𝓝 x₀)) (hu : Tendsto u atTop (𝓝 y))
    (h : ∀ᶠ k in atTop, u k ∈ outerLimit (𝓝 (a k)) F) : y ∈ outerLimit (𝓝 x₀) F := by
  simp only [← nhdsWithin_univ] at ha h ⊢
  exact mem_outerLimit_nhdsWithin_of_seq a u ha hu h

/-- Diagonal argument: if `G x ⊆ Lim sup_{z →Ω x} F z` at every `x ∈ Ω`, then
`Lim sup_{x →Ω x₀} G x ⊆ Lim sup_{x →Ω x₀} F x`. -/
theorem outerLimit_nhdsWithin_diag {Ω : Set X} {x₀ : X} {F G : X → Set E}
    (h : ∀ x ∈ Ω, G x ⊆ outerLimit (𝓝[Ω] x) F) :
    outerLimit (𝓝[Ω] x₀) G ⊆ outerLimit (𝓝[Ω] x₀) F := by
  rintro y ⟨a, v, ha, hv, hG⟩
  exact mem_outerLimit_nhdsWithin_of_seq a v ha hv
    (((tendsto_nhdsWithin_iff.1 ha).2).mono fun k hk ↦ h _ hk (hG k))

/-- Outer limits along `x →Ω x₀` of a map that is outer semicontinuous relative to `Ω` are
closed: `Lim sup_{x →Ω x₀} F x` is closed whenever `x₀ ∈ Ω`. -/
theorem isClosed_outerLimit_nhdsWithin {Ω : Set X} {x₀ : X} (F : X → Set E) :
    IsClosed (outerLimit (𝓝[Ω] x₀) F) := by
  refine isClosed_of_closure_subset fun y hy ↦ ?_
  obtain ⟨u, hu, huy⟩ := mem_closure_iff_seq_limit.1 hy
  -- a diagonal argument along the constant base point
  have key : ∀ k : ℕ, ∃ b : X, ∃ w : E,
      dist b x₀ < 1 / (k + 1) ∧ b ∈ Ω ∧ dist w (u k) < 1 / (k + 1) ∧ w ∈ F b := by
    intro k
    obtain ⟨a, v, ha, hv, hF⟩ := hu k
    have hpos : (0 : ℝ) < 1 / (k + 1) := Nat.one_div_pos_of_nat
    have h1 := Metric.tendsto_nhds.1 (tendsto_nhdsWithin_iff.1 ha).1 _ hpos
    have h2 := (tendsto_nhdsWithin_iff.1 ha).2
    have h3 := Metric.tendsto_nhds.1 hv _ hpos
    obtain ⟨j, hj1, hj2, hj3⟩ := (h1.and (h2.and h3)).exists
    exact ⟨a j, v j, hj1, hj2, hj3, hF j⟩
  choose b w hbw using key
  have hlim : Tendsto (fun k : ℕ ↦ (1 : ℝ) / (k + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨b, w, tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k ↦ (hbw k).2.1⟩, ?_,
    fun k ↦ (hbw k).2.2.2⟩
  · rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ ↦ dist_nonneg) (fun k ↦ (hbw k).1.le) hlim
  · rw [tendsto_iff_dist_tendsto_zero]
    have := tendsto_iff_dist_tendsto_zero.1 huy
    refine squeeze_zero (fun _ ↦ dist_nonneg) (fun k ↦ ?_) (hlim.add this |>.trans (by simp))
    linarith [dist_triangle (w k) (u k) y, (hbw k).2.2.1]

end Metric

end VariationalAnalysis
