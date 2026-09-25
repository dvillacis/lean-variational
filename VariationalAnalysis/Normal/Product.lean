/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import VariationalAnalysis.Normal.Limiting

/-!
# Normals to products; locality of normal cones

## Main results

* `coprod_mem_regularNormalCone_prod_iff`, `coprod_mem_normalCone_prod_iff`: Prop. 1.4 of
  [Mordukhovich 2018]: `N((x₁, x₂); Ω₁ × Ω₂) = N(x₁; Ω₁) × N(x₂; Ω₂)`, and the same for regular
  normals. A dual element `(u, w)` on `E × F` is `u.coprod w`.
* `regularNormalCone_congr`, `normalCone_congr`: normal cones only depend on the set near the
  point.
-/

open Filter Topology Set

namespace VariationalAnalysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

section Locality

variable {Ω₁ Ω₂ : Set E} {x₀ : E}

/-- Regular normals only depend on the set near the point. -/
theorem regularNormalCone_congr (h : Ω₁ =ᶠ[𝓝 x₀] Ω₂) :
    regularNormalCone Ω₁ x₀ = regularNormalCone Ω₂ x₀ := by
  have hmem : x₀ ∈ Ω₁ ↔ x₀ ∈ Ω₂ := Iff.of_eq h.self_of_nhds
  simp only [regularNormalCone, nhdsWithin_eq_iff_eventuallyEq.2 h, hmem]

/-- Limiting normals only depend on the set near the point. -/
theorem normalCone_congr (h : Ω₁ =ᶠ[𝓝 x₀] Ω₂) : normalCone Ω₁ x₀ = normalCone Ω₂ x₀ := by
  have hmem : x₀ ∈ Ω₁ ↔ x₀ ∈ Ω₂ := Iff.of_eq h.self_of_nhds
  have hnhds := nhdsWithin_eq_iff_eventuallyEq.2 h
  have hev : ∀ᶠ x in 𝓝[Ω₂] x₀, regularNormalCone Ω₁ x = regularNormalCone Ω₂ x :=
    nhdsWithin_le_nhds (h.eventuallyEq_nhds.mono fun _ hx ↦ regularNormalCone_congr hx)
  ext v
  simp only [normalCone, mem_ofPred_eq, hmem, hnhds]
  refine and_congr_right fun _ ↦ ⟨fun hv ↦ outerLimit_mono (hev.mono fun _ hx ↦ hx.le) hv,
    fun hv ↦ outerLimit_mono (hev.mono fun _ hx ↦ hx.ge) hv⟩

end Locality

section Product

variable {Ω₁ : Set E} {Ω₂ : Set F} {x₁ : E} {x₂ : F} {u : StrongDual ℝ E}
  {w : StrongDual ℝ F}

/-- Prop. 1.4 of [Mordukhovich 2018] for regular normals:
`N̂((x₁, x₂); Ω₁ × Ω₂) = N̂(x₁; Ω₁) × N̂(x₂; Ω₂)`. -/
theorem coprod_mem_regularNormalCone_prod_iff :
    u.coprod w ∈ regularNormalCone (Ω₁ ×ˢ Ω₂) (x₁, x₂) ↔
      u ∈ regularNormalCone Ω₁ x₁ ∧ w ∈ regularNormalCone Ω₂ x₂ := by
  constructor
  · rintro ⟨⟨hx₁, hx₂⟩, h⟩
    refine ⟨⟨hx₁, fun ε hε ↦ ?_⟩, ⟨hx₂, fun ε hε ↦ ?_⟩⟩
    · have hT : Tendsto (fun x ↦ (x, x₂)) (𝓝[Ω₁] x₁) (𝓝[Ω₁ ×ˢ Ω₂] (x₁, x₂)) := by
        rw [nhdsWithin_prod_eq]
        exact tendsto_id.prodMk
          (tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds, Eventually.of_forall fun _ ↦ hx₂⟩)
      filter_upwards [hT.eventually (h ε hε)] with x hx
      simpa using hx
    · have hT : Tendsto (fun y ↦ (x₁, y)) (𝓝[Ω₂] x₂) (𝓝[Ω₁ ×ˢ Ω₂] (x₁, x₂)) := by
        rw [nhdsWithin_prod_eq]
        exact (tendsto_nhdsWithin_iff.2
          ⟨tendsto_const_nhds, Eventually.of_forall fun _ ↦ hx₁⟩).prodMk tendsto_id
      filter_upwards [hT.eventually (h ε hε)] with y hy
      simpa using hy
  · rintro ⟨⟨hx₁, hu⟩, ⟨hx₂, hw⟩⟩
    refine ⟨⟨hx₁, hx₂⟩, fun ε hε ↦ ?_⟩
    rw [nhdsWithin_prod_eq]
    filter_upwards [(hu (ε / 2) (half_pos hε)).prod_mk (hw (ε / 2) (half_pos hε))] with p hp
    obtain ⟨x, y⟩ := p
    simp only [Prod.mk_sub_mk, ContinuousLinearMap.coprod_apply, Prod.norm_mk]
    have h1 := le_max_left ‖x - x₁‖ ‖y - x₂‖
    have h2 := le_max_right ‖x - x₁‖ ‖y - x₂‖
    nlinarith [hp.1, hp.2]

/-- Prop. 1.4 of [Mordukhovich 2018] (basic normals to products of sets):
`N((x₁, x₂); Ω₁ × Ω₂) = N(x₁; Ω₁) × N(x₂; Ω₂)`. -/
theorem coprod_mem_normalCone_prod_iff :
    u.coprod w ∈ normalCone (Ω₁ ×ˢ Ω₂) (x₁, x₂) ↔
      u ∈ normalCone Ω₁ x₁ ∧ w ∈ normalCone Ω₂ x₂ := by
  constructor
  · rintro ⟨⟨hx₁, hx₂⟩, p, ℓ, hp, hℓ, hmem⟩
    have hp' := tendsto_nhdsWithin_iff.1 hp
    have hmem' : ∀ k, (ℓ k).comp (ContinuousLinearMap.inl ℝ E F) ∈ regularNormalCone Ω₁ (p k).1 ∧
        (ℓ k).comp (ContinuousLinearMap.inr ℝ E F) ∈ regularNormalCone Ω₂ (p k).2 := fun k ↦ by
      rw [← coprod_mem_regularNormalCone_prod_iff, ContinuousLinearMap.coprod_comp_inl_inr]
      exact hmem k
    have hinl := tendsto_comp_inl hℓ
    have hinr := tendsto_comp_inr hℓ
    simp only [ContinuousLinearMap.coprod_comp_inl, ContinuousLinearMap.coprod_comp_inr]
      at hinl hinr
    refine ⟨⟨hx₁, fun k ↦ (p k).1, _, tendsto_nhdsWithin_iff.2
      ⟨(continuous_fst.tendsto _).comp hp'.1, hp'.2.mono fun k hk ↦ hk.1⟩, hinl,
      fun k ↦ (hmem' k).1⟩, ⟨hx₂, fun k ↦ (p k).2, _, tendsto_nhdsWithin_iff.2
      ⟨(continuous_snd.tendsto _).comp hp'.1, hp'.2.mono fun k hk ↦ hk.2⟩, hinr,
      fun k ↦ (hmem' k).2⟩⟩
  · rintro ⟨⟨hx₁, a, u', ha, hu', hmemu⟩, ⟨hx₂, b, w', hb, hw', hmemw⟩⟩
    refine ⟨⟨hx₁, hx₂⟩, fun k ↦ (a k, b k), fun k ↦ (u' k).coprod (w' k), ?_,
      tendsto_coprod hu' hw', fun k ↦ coprod_mem_regularNormalCone_prod_iff.2 ⟨hmemu k, hmemw k⟩⟩
    rw [nhdsWithin_prod_eq]
    exact ha.prodMk hb

/-- Prop. 1.4 of [Mordukhovich 2018] for an arbitrary dual element `ℓ` on `E × F`. -/
theorem mem_normalCone_prod_iff {ℓ : StrongDual ℝ (E × F)} :
    ℓ ∈ normalCone (Ω₁ ×ˢ Ω₂) (x₁, x₂) ↔
      ℓ.comp (ContinuousLinearMap.inl ℝ E F) ∈ normalCone Ω₁ x₁ ∧
        ℓ.comp (ContinuousLinearMap.inr ℝ E F) ∈ normalCone Ω₂ x₂ := by
  rw [← coprod_mem_normalCone_prod_iff, ContinuousLinearMap.coprod_comp_inl_inr]

end Product

end VariationalAnalysis
