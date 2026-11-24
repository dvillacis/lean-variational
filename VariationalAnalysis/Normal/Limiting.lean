/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis.Normal.Regular
import VariationalAnalysis.SetValued.OuterLimit

/-!
# The limiting (basic, Mordukhovich) normal cone

The limiting normal cone to `Ω` at `x₀ ∈ Ω` is the outer limit of regular normals at nearby
points of `Ω`,

  `N(x₀; Ω) = Lim sup_{x →Ω x₀} N̂(x; Ω)`,

which is the first representation in [Mordukhovich 2018, Thm. 1.6, (1.7)] and the definition
(18.3) in [Clason–Valkonen]. [Mordukhovich 2018, Def. 1.1] defines `N(x₀; Ω)` through Euclidean
projections instead; the two agree for locally closed sets in finite dimensions
(`VariationalAnalysis.Normal.Projection`).

The outer limit is taken in the norm topology of the dual. In finite dimensions this is the
limiting normal cone of the literature; in infinite dimensions the literature uses weak-*
limits, which give a larger cone.

## Main results

* `regularNormalCone_subset_normalCone`, `isClosed_normalCone`, `smul_mem_normalCone`:
  `N(x₀; Ω)` is a closed cone containing `N̂(x₀; Ω)`.
* `normalCone_eq_outerLimit_normalCone`: Prop. 1.3 of [Mordukhovich 2018] (robustness).
* `normalCone_eq_regularNormalCone_of_convex`, `mem_normalCone_of_convex`: Prop. 1.7, (1.9),
  of [Mordukhovich 2018]: for convex sets both cones are the normal cone of convex analysis.
* `normalCone_of_mem_interior`: `N(x₀; Ω) = {0}` at interior points.
-/

open Filter Topology Set

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : Set E} {x₀ : E} {v : StrongDual ℝ E}

/-- The limiting (basic, Mordukhovich) normal cone to `Ω` at `x₀`:
`N(x₀; Ω) = Lim sup_{x →Ω x₀} N̂(x; Ω)` [Mordukhovich 2018, (1.7)], [Clason–Valkonen, (18.3)].
Empty if `x₀ ∉ Ω`. -/
def normalCone (Ω : Set E) (x₀ : E) : Set (StrongDual ℝ E) :=
  {v | x₀ ∈ Ω ∧ v ∈ outerLimit (𝓝[Ω] x₀) (regularNormalCone Ω)}

theorem mem_of_mem_normalCone (hv : v ∈ normalCone Ω x₀) : x₀ ∈ Ω := hv.1

theorem regularNormalCone_subset_normalCone : regularNormalCone Ω x₀ ⊆ normalCone Ω x₀ :=
  fun _ hv ↦ ⟨hv.1, subset_outerLimit (pure_le_nhdsWithin hv.1) _ hv⟩

theorem zero_mem_normalCone (hx : x₀ ∈ Ω) : (0 : StrongDual ℝ E) ∈ normalCone Ω x₀ :=
  regularNormalCone_subset_normalCone (zero_mem_regularNormalCone hx)

theorem smul_mem_normalCone (hv : v ∈ normalCone Ω x₀) {t : ℝ} (ht : 0 ≤ t) :
    t • v ∈ normalCone Ω x₀ := by
  obtain ⟨hx, a, w, ha, hw, hmem⟩ := hv
  exact ⟨hx, a, fun k ↦ t • w k, ha, hw.const_smul t,
    fun k ↦ smul_mem_regularNormalCone (hmem k) ht⟩

/-- `N(x₀; Ω)` is closed. -/
theorem isClosed_normalCone : IsClosed (normalCone Ω x₀) := by
  by_cases hx : x₀ ∈ Ω
  · simpa [normalCone, hx] using isClosed_outerLimit_nhdsWithin (Ω := Ω) (x₀ := x₀)
      (regularNormalCone Ω)
  · simp [normalCone, hx]

/-- Prop. 1.3 of [Mordukhovich 2018] (robustness of basic normals):
`N(x₀; Ω) = Lim sup_{x →Ω x₀} N(x; Ω)`. -/
theorem normalCone_eq_outerLimit_normalCone (hx : x₀ ∈ Ω) :
    normalCone Ω x₀ = outerLimit (𝓝[Ω] x₀) (normalCone Ω) := by
  refine subset_antisymm (fun _ hv ↦ ?_) (fun _ hv ↦ ⟨hx, ?_⟩)
  · exact outerLimit_mono (Eventually.of_forall fun _ ↦ regularNormalCone_subset_normalCone)
      hv.2
  · exact outerLimit_nhdsWithin_diag (fun _ _ _ hw ↦ hw.2) hv

/-- Prop. 1.7, (1.9), of [Mordukhovich 2018]: for convex sets the limiting and regular normal
cones agree. -/
theorem normalCone_eq_regularNormalCone_of_convex (hΩ : Convex ℝ Ω) :
    normalCone Ω x₀ = regularNormalCone Ω x₀ := by
  refine subset_antisymm (fun v hv ↦ ?_) regularNormalCone_subset_normalCone
  obtain ⟨hx, a, w, ha, hw, hmem⟩ := hv
  rw [mem_regularNormalCone_of_convex hΩ hx]
  intro x hxΩ
  have hlim := tendsto_dual_apply hw ((tendsto_nhdsWithin_iff.1 ha).1.const_sub x)
  refine le_of_tendsto hlim (Eventually.of_forall fun k ↦ ?_)
  exact (mem_regularNormalCone_of_convex hΩ (hmem k).1).1 (hmem k) x hxΩ

/-- Prop. 1.7, (1.9), of [Mordukhovich 2018]: limiting normals to a convex set are the normals
of convex analysis. -/
theorem mem_normalCone_of_convex (hΩ : Convex ℝ Ω) (hx : x₀ ∈ Ω) :
    v ∈ normalCone Ω x₀ ↔ ∀ x ∈ Ω, v (x - x₀) ≤ 0 := by
  rw [normalCone_eq_regularNormalCone_of_convex hΩ, mem_regularNormalCone_of_convex hΩ hx]

/-- At an interior point the limiting normal cone is trivial [Mordukhovich 2018, proof of
Prop. 1.2]. -/
theorem normalCone_of_mem_interior (hx : x₀ ∈ interior Ω) : normalCone Ω x₀ = {0} := by
  refine subset_antisymm (fun v hv ↦ ?_) ?_
  · obtain ⟨-, a, w, ha, hw, hmem⟩ := hv
    have hint : ∀ᶠ k in atTop, a k ∈ interior Ω :=
      (tendsto_nhdsWithin_iff.1 ha).1 (isOpen_interior.mem_nhds hx)
    have hw0 : ∀ᶠ k in atTop, w k = 0 := hint.mono fun k hk ↦ by
      simpa [regularNormalCone_of_mem_interior hk] using hmem k
    exact mem_singleton_iff.2 (tendsto_nhds_unique hw (tendsto_const_nhds.congr'
      (hw0.mono fun k hk ↦ hk.symm)))
  · rintro _ rfl
    exact zero_mem_normalCone (interior_subset hx)

end VariationalAnalysis
