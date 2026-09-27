/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.Normed.Module.Complemented
import VariationalAnalysis.Normal.Product

/-!
# Normals to inverse images under smooth mappings

For `g : E → F` strictly differentiable at `x₀` with surjective derivative,
[Mordukhovich 2018, Exercise 1.54] computes the normals to an inverse image:

  `N̂(x₀; g⁻¹(Ω)) = ∇g(x₀)* N̂(g x₀; Ω)`,  `N(x₀; g⁻¹(Ω)) = ∇g(x₀)* N(g x₀; Ω)`,

where `∇g(x₀)* v = v ∘ ∇g(x₀)`. We first treat an invertible derivative, through the local
inverse of `g` (inverse function theorem); this extends `Normal/Transport` (linear isomorphisms)
to nonlinear changes of variables. The surjective case reduces to the invertible one: if `P` is
a continuous projection onto `ker ∇g(x₀)`, the map `x ↦ (g x, P (x - x₀))` has an invertible
derivative and `g⁻¹(Ω)` is the inverse image of `Ω × ker ∇g(x₀)`, whose normals are the
`(v, 0)` with `v` normal to `Ω` (Prop. 1.4 of [Mordukhovich 2018]).

The limiting formulas assume that `g` is `C¹` around `x₀`, in the form: `g` has strict
derivative `D x` at every `x` near `x₀` and `D` is continuous at `x₀`.

## Main results

* `comp_mem_regularNormalCone_of_hasFDerivAt`: regular normals pull back along any map that is
  differentiable at the point and maps `T` into `S` near it.
* `comp_mem_regularNormalCone_preimage_iff`, `regularNormalCone_preimage`: regular normals to an
  inverse image under a map with invertible strict derivative.
* `comp_mem_normalCone_preimage_iff`, `normalCone_preimage`, `mem_normalCone_preimage_iff`:
  limiting normals to an inverse image under a `C¹` map with invertible derivative.
* `regularNormalCone_preimage_of_surjective`, `normalCone_preimage_of_surjective`:
  Exercise 1.54 of [Mordukhovich 2018] (normals to inverse images under mappings with
  surjective derivative), for a complemented kernel; in finite dimensions
  `regularNormalCone_preimage_of_surjective_of_finiteDimensional`,
  `normalCone_preimage_of_surjective_of_finiteDimensional`.
-/

open Filter Topology Set

namespace VariationalAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Regular normals pull back along a map `G` differentiable at `x` with derivative `A` and
mapping `T` into `S` near `x`: if `v ∈ N̂(G x; S)`, then `v ∘ A ∈ N̂(x; T)`. With `T = G⁻¹(S)`
this is the inclusion `⊇` of [Mordukhovich 2018, Exercise 1.54(i)], which only needs Fréchet
differentiability. -/
theorem comp_mem_regularNormalCone_of_hasFDerivAt {G : E → F} {A : E →L[ℝ] F} {x : E}
    {T : Set E} {S : Set F} (hG : HasFDerivAt G A x) (hx : x ∈ T)
    (hTS : ∀ᶠ x' in 𝓝[T] x, G x' ∈ S) {v : StrongDual ℝ F}
    (hv : v ∈ regularNormalCone S (G x)) : v.comp A ∈ regularNormalCone T x := by
  refine ⟨hx, fun ε hε ↦ ?_⟩
  set a := ‖A‖ with ha_def
  set b := ‖v‖ with hb_def
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hε1 : 0 < ε / (2 * (a + 1)) := by positivity
  have hε2 : 0 < min (ε / (2 * (b + 1))) 1 := lt_min (by positivity) one_pos
  have hT : Tendsto G (𝓝[T] x) (𝓝[S] (G x)) :=
    tendsto_nhdsWithin_iff.2 ⟨hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, hTS⟩
  have h1 := hT.eventually (hv.2 _ hε1)
  have h2 : ∀ᶠ x' in 𝓝 x, ‖G x' - G x - A (x' - x)‖ ≤
      min (ε / (2 * (b + 1))) 1 * ‖x' - x‖ := hG.isLittleO.def hε2
  filter_upwards [h1, nhdsWithin_le_nhds h2] with x' hx1 hx2
  set r := G x' - G x - A (x' - x) with hr_def
  set c := min (ε / (2 * (b + 1))) 1
  have hc1 : c ≤ 1 := min_le_right _ _
  have hc2 : c ≤ ε / (2 * (b + 1)) := min_le_left _ _
  have hn0 : 0 ≤ ‖x' - x‖ := norm_nonneg _
  have hGr : G x' - G x = A (x' - x) + r := by rw [hr_def]; abel
  have hn : ‖G x' - G x‖ ≤ (a + 1) * ‖x' - x‖ := by
    rw [hGr]
    calc ‖A (x' - x) + r‖ ≤ ‖A (x' - x)‖ + ‖r‖ := norm_add_le _ _
      _ ≤ a * ‖x' - x‖ + 1 * ‖x' - x‖ := by
          gcongr
          · exact A.le_opNorm _
          · exact hx2.trans (by gcongr)
      _ = (a + 1) * ‖x' - x‖ := by ring
  have hvr : -v r ≤ b * ‖r‖ := (neg_le_abs _).trans (v.le_opNorm r)
  have hbc : b * c ≤ ε / 2 := by
    calc b * c ≤ b * (ε / (2 * (b + 1))) := by gcongr
      _ ≤ ε / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  calc (v.comp A) (x' - x) = v (G x' - G x) - v r := by
        rw [ContinuousLinearMap.comp_apply, hGr, map_add]; ring
    _ ≤ ε / (2 * (a + 1)) * ‖G x' - G x‖ + b * ‖r‖ := by linarith
    _ ≤ ε / (2 * (a + 1)) * ((a + 1) * ‖x' - x‖) + b * (c * ‖x' - x‖) := by gcongr
    _ = ε / 2 * ‖x' - x‖ + (b * c) * ‖x' - x‖ := by
        field_simp
    _ ≤ ε / 2 * ‖x' - x‖ + ε / 2 * ‖x' - x‖ := by gcongr
    _ = ε * ‖x' - x‖ := by ring

variable [CompleteSpace E] {Ω : Set F}

/-- Exercise 1.54(i) of [Mordukhovich 2018] for an invertible derivative: if `Θ` has invertible
strict derivative `D` at `x`, then `v ∘ D ∈ N̂(x; Θ⁻¹(Ω))` iff `v ∈ N̂(Θ x; Ω)`. -/
theorem comp_mem_regularNormalCone_preimage_iff {Θ : E → F} {x : E} {D : E ≃L[ℝ] F}
    (hΘ : HasStrictFDerivAt Θ (D : E →L[ℝ] F) x) {v : StrongDual ℝ F} :
    v.comp (D : E →L[ℝ] F) ∈ regularNormalCone (Θ ⁻¹' Ω) x ↔
      v ∈ regularNormalCone Ω (Θ x) := by
  constructor
  · intro h
    have hx : Θ x ∈ Ω := h.1
    set g := HasStrictFDerivAt.localInverse Θ D x hΘ
    have hg : HasFDerivAt g (D.symm : F →L[ℝ] E) (Θ x) := hΘ.to_localInverse.hasFDerivAt
    have hgx : g (Θ x) = x := hΘ.localInverse_apply_image
    have hTS : ∀ᶠ y in 𝓝[Ω] (Θ x), g y ∈ Θ ⁻¹' Ω := by
      filter_upwards [nhdsWithin_le_nhds hΘ.eventually_right_inverse, self_mem_nhdsWithin]
        with y hy hyΩ
      show Θ (g y) ∈ Ω
      rw [hy]; exact hyΩ
    have h' : v.comp (D : E →L[ℝ] F) ∈ regularNormalCone (Θ ⁻¹' Ω) (g (Θ x)) := by
      rwa [hgx]
    have := comp_mem_regularNormalCone_of_hasFDerivAt hg hx hTS h'
    have hv : (v.comp (D : E →L[ℝ] F)).comp (D.symm : F →L[ℝ] E) = v := by ext; simp
    rwa [hv] at this
  · intro h
    exact comp_mem_regularNormalCone_of_hasFDerivAt hΘ.hasFDerivAt h.1
      (eventually_nhdsWithin_of_forall fun _ hx' ↦ hx') h

/-- Exercise 1.54(i) of [Mordukhovich 2018] for an invertible derivative:
`N̂(x; Θ⁻¹(Ω)) = {v ∘ D | v ∈ N̂(Θ x; Ω)}` for an invertible strict derivative `D`. -/
theorem regularNormalCone_preimage {Θ : E → F} {x : E} {D : E ≃L[ℝ] F}
    (hΘ : HasStrictFDerivAt Θ (D : E →L[ℝ] F) x) :
    regularNormalCone (Θ ⁻¹' Ω) x =
      (fun v : StrongDual ℝ F ↦ v.comp (D : E →L[ℝ] F)) '' regularNormalCone Ω (Θ x) := by
  ext m
  constructor
  · intro hm
    refine ⟨m.comp (D.symm : F →L[ℝ] E), ?_, by ext; simp⟩
    rw [← comp_mem_regularNormalCone_preimage_iff hΘ]
    have : (m.comp (D.symm : F →L[ℝ] E)).comp (D : E →L[ℝ] F) = m := by ext; simp
    rwa [this]
  · rintro ⟨v, hv, rfl⟩
    exact (comp_mem_regularNormalCone_preimage_iff hΘ).2 hv

/-- If `A k → e` for a linear isomorphism `e`, then eventually `e⁻¹ ∘ A k` is a unit of
`E →L[ℝ] E`. -/
theorem eventually_isUnit_symm_comp {α : Type*} {l : Filter α} {A : α → E →L[ℝ] F}
    {e : E ≃L[ℝ] F} (hA : Tendsto A l (𝓝 (e : E →L[ℝ] F))) :
    ∀ᶠ k in l, IsUnit ((e.symm : F →L[ℝ] E).comp (A k)) := by
  have hc : Tendsto (fun k ↦ (e.symm : F →L[ℝ] E).comp (A k)) l (𝓝 1) := by
    have := ((ContinuousLinearMap.compL ℝ E F E (e.symm : F →L[ℝ] E)).continuous.tendsto
      (e : E →L[ℝ] F)).comp hA
    simpa [Function.comp_def, ContinuousLinearMap.one_def] using this
  exact hc.eventually (Units.isOpen.mem_nhds isUnit_one)

omit [CompleteSpace E] in
/-- A map `A` with `e⁻¹ ∘ A` a unit is the forward map of a linear isomorphism. -/
theorem exists_equiv_of_isUnit_symm_comp {A : E →L[ℝ] F} {e : E ≃L[ℝ] F}
    (h : IsUnit ((e.symm : F →L[ℝ] E).comp A)) : ∃ D : E ≃L[ℝ] F, (D : E →L[ℝ] F) = A := by
  obtain ⟨u, hu⟩ := h
  refine ⟨(ContinuousLinearEquiv.unitsEquiv ℝ E u).trans e, ?_⟩
  ext y
  have : (u : E →L[ℝ] E) y = e.symm (A y) := by rw [hu]; rfl
  simp [ContinuousLinearEquiv.unitsEquiv_apply, this]

/-- Exercise 1.54(ii) of [Mordukhovich 2018] for an invertible derivative: if `Θ` has
strict derivative `D x` at every `x` near `x₀`, `D` is continuous at `x₀` and `D x₀ = e` is a
linear isomorphism, then `v ∘ e ∈ N(x₀; Θ⁻¹(Ω))` iff `v ∈ N(Θ x₀; Ω)`. -/
theorem comp_mem_normalCone_preimage_iff {Θ : E → F} {x₀ : E} {D : E → E →L[ℝ] F}
    {e : E ≃L[ℝ] F} (hD : ∀ᶠ x in 𝓝 x₀, HasStrictFDerivAt Θ (D x) x)
    (hDc : ContinuousAt D x₀) (he : D x₀ = e) {v : StrongDual ℝ F} :
    v.comp (e : E →L[ℝ] F) ∈ normalCone (Θ ⁻¹' Ω) x₀ ↔ v ∈ normalCone Ω (Θ x₀) := by
  have hΘ0 : HasStrictFDerivAt Θ (e : E →L[ℝ] F) x₀ := he ▸ hD.self_of_nhds
  have hΘc : ContinuousAt Θ x₀ := hΘ0.continuousAt
  constructor
  · rintro ⟨hx, a, m, ha, hm, hmem⟩
    have ha' := tendsto_nhdsWithin_iff.1 ha
    have hDa : Tendsto (fun k ↦ D (a k)) atTop (𝓝 (e : E →L[ℝ] F)) :=
      he ▸ hDc.tendsto.comp ha'.1
    set U : ℕ → E →L[ℝ] E := fun k ↦ (e.symm : F →L[ℝ] E).comp (D (a k)) with hU_def
    set B : ℕ → F →L[ℝ] E := fun k ↦ (Ring.inverse (U k)).comp (e.symm : F →L[ℝ] E)
      with hB_def
    have hU1 : Tendsto U atTop (𝓝 1) := by
      have := ((ContinuousLinearMap.compL ℝ E F E (e.symm : F →L[ℝ] E)).continuous.tendsto
        (e : E →L[ℝ] F)).comp hDa
      simpa [Function.comp_def, ContinuousLinearMap.one_def, hU_def] using this
    have hB : Tendsto B atTop (𝓝 (e.symm : F →L[ℝ] E)) := by
      have hinv : Tendsto (fun k ↦ Ring.inverse (U k)) atTop (𝓝 1) := by
        have h := (NormedRing.inverse_continuousAt (1 : (E →L[ℝ] E)ˣ)).tendsto.comp hU1
        simpa [Function.comp_def, Ring.inverse_one] using h
      have := ((ContinuousLinearMap.compL ℝ F E E).flip (e.symm : F →L[ℝ] E)).continuous.tendsto
        1 |>.comp hinv
      simpa [Function.comp_def, hB_def, ContinuousLinearMap.one_def] using this
    refine ⟨hx, mem_outerLimit_of_eventually (fun k ↦ Θ (a k)) (fun k ↦ (m k).comp (B k))
      (tendsto_nhdsWithin_iff.2 ⟨hΘc.tendsto.comp ha'.1, ha'.2.mono fun _ hk ↦ hk⟩) ?_ ?_⟩
    · have := tendsto_dual_comp hm hB
      have hv : (v.comp (e : E →L[ℝ] F)).comp (e.symm : F →L[ℝ] E) = v := by ext; simp
      rwa [hv] at this
    · filter_upwards [eventually_isUnit_symm_comp hDa, ha'.1.eventually hD] with k hu hs
      obtain ⟨D', hD'⟩ := exists_equiv_of_isUnit_symm_comp hu
      rw [← hD'] at hs
      rw [← comp_mem_regularNormalCone_preimage_iff hs]
      have h1 : (B k).comp (D (a k)) = 1 := by
        have := Ring.inverse_mul_cancel _ hu
        rw [ContinuousLinearMap.mul_def] at this
        rw [hB_def]
        simpa [ContinuousLinearMap.comp_assoc, hU_def] using this
      have : ((m k).comp (B k)).comp (D' : E →L[ℝ] F) = m k := by
        rw [hD', ContinuousLinearMap.comp_assoc, h1]; rfl
      rw [this]; exact hmem k
  · rintro ⟨hx, y, ℓ, hy, hℓ, hmem⟩
    have hy' := tendsto_nhdsWithin_iff.1 hy
    set g := HasStrictFDerivAt.localInverse Θ e x₀ hΘ0
    have hgc : ContinuousAt g (Θ x₀) := hΘ0.to_localInverse.continuousAt
    have hgx : g (Θ x₀) = x₀ := hΘ0.localInverse_apply_image
    have ha : Tendsto (fun k ↦ g (y k)) atTop (𝓝 x₀) := by
      have := hgc.tendsto.comp hy'.1; rwa [hgx] at this
    have hinv : ∀ᶠ k in atTop, Θ (g (y k)) = y k := hy'.1.eventually hΘ0.eventually_right_inverse
    have hmemΩ : ∀ᶠ k in atTop, g (y k) ∈ Θ ⁻¹' Ω :=
      hinv.mono fun k hk ↦ by show Θ (g (y k)) ∈ Ω; rw [hk]; exact (hmem k).1
    refine ⟨show Θ x₀ ∈ Ω from hx, mem_outerLimit_of_eventually (fun k ↦ g (y k))
      (fun k ↦ (ℓ k).comp (D (g (y k)))) (tendsto_nhdsWithin_iff.2 ⟨ha, hmemΩ⟩) ?_ ?_⟩
    · have := tendsto_dual_comp hℓ (hDc.tendsto.comp ha)
      rwa [he] at this
    · filter_upwards [hinv, hmemΩ, ha.eventually hD] with k hk hkΩ hs
      refine comp_mem_regularNormalCone_of_hasFDerivAt hs.hasFDerivAt hkΩ
        (eventually_nhdsWithin_of_forall fun _ hx' ↦ hx') ?_
      rw [hk]; exact hmem k

/-- Exercise 1.54(ii) of [Mordukhovich 2018] for an invertible derivative:
`N(x₀; Θ⁻¹(Ω)) = {v ∘ D x₀ | v ∈ N(Θ x₀; Ω)}` for a `C¹` map `Θ` with invertible derivative
`D x₀ = e`. -/
theorem normalCone_preimage {Θ : E → F} {x₀ : E} {D : E → E →L[ℝ] F} {e : E ≃L[ℝ] F}
    (hD : ∀ᶠ x in 𝓝 x₀, HasStrictFDerivAt Θ (D x) x) (hDc : ContinuousAt D x₀)
    (he : D x₀ = e) :
    normalCone (Θ ⁻¹' Ω) x₀ =
      (fun v : StrongDual ℝ F ↦ v.comp (D x₀)) '' normalCone Ω (Θ x₀) := by
  ext m
  constructor
  · intro hm
    refine ⟨m.comp (e.symm : F →L[ℝ] E), ?_, by rw [he]; ext; simp⟩
    rw [← comp_mem_normalCone_preimage_iff hD hDc he]
    have : (m.comp (e.symm : F →L[ℝ] E)).comp (e : E →L[ℝ] F) = m := by ext; simp
    rwa [this]
  · rintro ⟨v, hv, rfl⟩
    rw [he]
    exact (comp_mem_normalCone_preimage_iff hD hDc he).2 hv

/-- Variant of `comp_mem_normalCone_preimage_iff`: `m ∈ N(x₀; Θ⁻¹(Ω))` iff
`m ∘ e⁻¹ ∈ N(Θ x₀; Ω)`. -/
theorem mem_normalCone_preimage_iff {Θ : E → F} {x₀ : E} {D : E → E →L[ℝ] F}
    {e : E ≃L[ℝ] F} (hD : ∀ᶠ x in 𝓝 x₀, HasStrictFDerivAt Θ (D x) x)
    (hDc : ContinuousAt D x₀) (he : D x₀ = e) {m : StrongDual ℝ E} :
    m ∈ normalCone (Θ ⁻¹' Ω) x₀ ↔ m.comp (e.symm : F →L[ℝ] E) ∈ normalCone Ω (Θ x₀) := by
  rw [← comp_mem_normalCone_preimage_iff hD hDc he]
  have : (m.comp (e.symm : F →L[ℝ] E)).comp (e : E →L[ℝ] F) = m := by ext; simp
  rw [this]


section Surjective

open ContinuousLinearMap

variable {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]

omit [CompleteSpace E] in
/-- Regular normals to `Ω × K`: `ℓ ∈ N̂((y, z); Ω × K)` iff `ℓ = (v, 0)` with `v ∈ N̂(y; Ω)`
(Prop. 1.4 of [Mordukhovich 2018] with `N̂(z; K) = {0}`). -/
theorem mem_regularNormalCone_prod_univ_iff {y : F} {z : K} {ℓ : StrongDual ℝ (F × K)} :
    ℓ ∈ regularNormalCone (Ω ×ˢ (univ : Set K)) (y, z) ↔
      ℓ.comp (inl ℝ F K) ∈ regularNormalCone Ω y ∧ ℓ.comp (inr ℝ F K) = 0 := by
  conv_lhs => rw [← coprod_comp_inl_inr ℓ]
  rw [coprod_mem_regularNormalCone_prod_iff,
    regularNormalCone_of_mem_interior (by simp : z ∈ interior (univ : Set K)), mem_singleton_iff]

omit [CompleteSpace E] in
/-- Limiting normals to `Ω × K`: `ℓ ∈ N((y, z); Ω × K)` iff `ℓ = (v, 0)` with `v ∈ N(y; Ω)`
(Prop. 1.4 of [Mordukhovich 2018] with `N(z; K) = {0}`). -/
theorem mem_normalCone_prod_univ_iff {y : F} {z : K} {ℓ : StrongDual ℝ (F × K)} :
    ℓ ∈ normalCone (Ω ×ˢ (univ : Set K)) (y, z) ↔
      ℓ.comp (inl ℝ F K) ∈ normalCone Ω y ∧ ℓ.comp (inr ℝ F K) = 0 := by
  rw [mem_normalCone_prod_iff, normalCone_of_mem_interior (by simp : z ∈ interior (univ : Set K)),
    mem_singleton_iff]

omit [CompleteSpace E] in
/-- If `N ⊆ (F × K)*` consists of the `(v, 0)` with `v ∈ M`, then pulling `N` back along
`A.prod P` is the same as pulling `M` back along `A`. -/
theorem image_comp_prod_eq {A : E →L[ℝ] F} {P : E →L[ℝ] K} {N : Set (StrongDual ℝ (F × K))}
    {M : Set (StrongDual ℝ F)}
    (hN : ∀ ℓ, ℓ ∈ N ↔ ℓ.comp (inl ℝ F K) ∈ M ∧ ℓ.comp (inr ℝ F K) = 0) :
    (fun ℓ : StrongDual ℝ (F × K) ↦ ℓ.comp (A.prod P)) '' N =
      (fun v : StrongDual ℝ F ↦ v.comp A) '' M := by
  ext m
  constructor
  · rintro ⟨ℓ, hℓ, rfl⟩
    obtain ⟨h1, h2⟩ := (hN ℓ).1 hℓ
    refine ⟨_, h1, ?_⟩
    ext x
    have h := congrArg (fun f : StrongDual ℝ K ↦ f (P x)) h2
    simp only [comp_apply, inr_apply, zero_apply] at h
    have hsplit : ℓ (A x, P x) = ℓ (A x, 0) + ℓ (0, P x) := by rw [← map_add]; simp
    simp [hsplit, h]
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.coprod 0, (hN _).2 ⟨by simpa using hv, by ext; simp⟩, ?_⟩
    ext x; simp

variable [CompleteSpace F]

/-- The change of variables `x ↦ (g x, P (x - x₀))` behind Exercise 1.54 of
[Mordukhovich 2018]: if `A : E →L[ℝ] F` is surjective and `P` is a continuous projection onto
`ker A`, then `A.prod P : E → F × ker A` is a linear isomorphism. -/
noncomputable def prodKerEquiv {A : E →L[ℝ] F} (hA : Function.Surjective A)
    {P : E →L[ℝ] A.ker} (hP : ∀ x : A.ker, P x = x) : E ≃L[ℝ] F × A.ker :=
  equivProdOfSurjectiveOfIsCompl A P (LinearMap.range_eq_top.2 hA)
    (LinearMap.range_eq_of_proj hP) (LinearMap.isCompl_of_proj hP)

/-- `prodKerEquiv` is `x ↦ (A x, P x)`. -/
theorem coe_prodKerEquiv {A : E →L[ℝ] F} (hA : Function.Surjective A)
    {P : E →L[ℝ] A.ker} (hP : ∀ x : A.ker, P x = x) :
    (prodKerEquiv hA hP : E →L[ℝ] F × A.ker) = A.prod P := rfl

/-- Exercise 1.54(i) of [Mordukhovich 2018] (regular normals to inverse images): for `g`
strictly differentiable at `x₀` with surjective derivative `A` whose kernel is complemented,
`N̂(x₀; g⁻¹(Ω)) = A* N̂(g x₀; Ω)`. The complementation of `ker A` holds automatically in finite
dimensions (`regularNormalCone_preimage_of_surjective_of_finiteDimensional`). -/
theorem regularNormalCone_preimage_of_surjective {g : E → F} {A : E →L[ℝ] F} {x₀ : E}
    (hg : HasStrictFDerivAt g A x₀) (hA : Function.Surjective A) (hK : A.ker.ClosedComplemented) :
    regularNormalCone (g ⁻¹' Ω) x₀ =
      (fun v : StrongDual ℝ F ↦ v.comp A) '' regularNormalCone Ω (g x₀) := by
  obtain ⟨P, hP⟩ := hK
  set G : E → F × A.ker := fun x ↦ (g x, P (x - x₀))
  have hG : HasStrictFDerivAt G (prodKerEquiv hA hP : E →L[ℝ] F × A.ker) x₀ := by
    rw [coe_prodKerEquiv]
    exact hg.prodMk (P.hasStrictFDerivAt.comp x₀ ((hasStrictFDerivAt_id x₀).sub_const x₀))
  have hpre : g ⁻¹' Ω = G ⁻¹' (Ω ×ˢ univ) := by ext; simp [G]
  have hGx : G x₀ = (g x₀, 0) := by simp [G]
  rw [hpre, regularNormalCone_preimage hG, hGx, coe_prodKerEquiv]
  exact image_comp_prod_eq fun _ ↦ mem_regularNormalCone_prod_univ_iff

/-- Exercise 1.54(ii) of [Mordukhovich 2018] (basic normals to inverse images): for `g` of
class `C¹` around `x₀` (strict derivative `D x` at every `x` near `x₀`, `D` continuous at `x₀`)
with surjective derivative `D x₀` whose kernel is complemented,
`N(x₀; g⁻¹(Ω)) = ∇g(x₀)* N(g x₀; Ω)`. The book assumes only strict differentiability at `x₀`;
the `C¹` assumption is the one of [Mordukhovich 2018, Thm. 3.11(iii)], where the exercise is
used. The complementation of `ker ∇g(x₀)` holds automatically in finite dimensions
(`normalCone_preimage_of_surjective_of_finiteDimensional`). -/
theorem normalCone_preimage_of_surjective {g : E → F} {D : E → E →L[ℝ] F} {x₀ : E}
    (hD : ∀ᶠ x in 𝓝 x₀, HasStrictFDerivAt g (D x) x) (hDc : ContinuousAt D x₀)
    (hA : Function.Surjective (D x₀)) (hK : (D x₀).ker.ClosedComplemented) :
    normalCone (g ⁻¹' Ω) x₀ = (fun v : StrongDual ℝ F ↦ v.comp (D x₀)) '' normalCone Ω (g x₀) := by
  obtain ⟨P, hP⟩ := hK
  set G : E → F × (D x₀).ker := fun x ↦ (g x, P (x - x₀))
  set DG : E → E →L[ℝ] F × (D x₀).ker := fun x ↦ (D x).prod P
  have hG : ∀ᶠ x in 𝓝 x₀, HasStrictFDerivAt G (DG x) x := by
    filter_upwards [hD] with x hx
    exact hx.prodMk (P.hasStrictFDerivAt.comp x ((hasStrictFDerivAt_id x).sub_const x₀))
  have hDGc : ContinuousAt DG x₀ :=
    (prodL ℝ).continuous.continuousAt.comp (hDc.prodMk continuousAt_const)
  have hpre : g ⁻¹' Ω = G ⁻¹' (Ω ×ˢ univ) := by ext; simp [G]
  have hGx : G x₀ = (g x₀, 0) := by simp [G]
  rw [hpre, normalCone_preimage hG hDGc (coe_prodKerEquiv hA hP).symm, hGx]
  exact image_comp_prod_eq fun _ ↦ mem_normalCone_prod_univ_iff

omit [CompleteSpace E] [CompleteSpace F] in
/-- The adjoint `v ↦ v ∘ A` of a surjective `A` is injective
([Mordukhovich 2018, Exercise 1.53]). -/
theorem comp_injective_of_surjective {A : E →L[ℝ] F} (hA : Function.Surjective A) :
    Function.Injective fun v : StrongDual ℝ F ↦ v.comp A := by
  intro v w h
  ext y
  obtain ⟨x, rfl⟩ := hA y
  exact congrArg (fun f : StrongDual ℝ E ↦ f x) h

/-- Exercise 1.54(i) of [Mordukhovich 2018], pointwise form: for `g` strictly differentiable at
`x₀` with surjective derivative `A` whose kernel is complemented,
`v ∘ A ∈ N̂(x₀; g⁻¹(Ω))` iff `v ∈ N̂(g x₀; Ω)`. -/
theorem comp_mem_regularNormalCone_preimage_iff_of_surjective {g : E → F} {A : E →L[ℝ] F}
    {x₀ : E} (hg : HasStrictFDerivAt g A x₀) (hA : Function.Surjective A)
    (hK : A.ker.ClosedComplemented) {v : StrongDual ℝ F} :
    v.comp A ∈ regularNormalCone (g ⁻¹' Ω) x₀ ↔ v ∈ regularNormalCone Ω (g x₀) := by
  rw [regularNormalCone_preimage_of_surjective hg hA hK]
  exact (comp_injective_of_surjective hA).mem_set_image

/-- Exercise 1.54(ii) of [Mordukhovich 2018], pointwise form: for `g` of class `C¹` around `x₀`
with surjective derivative `D x₀` whose kernel is complemented,
`v ∘ ∇g(x₀) ∈ N(x₀; g⁻¹(Ω))` iff `v ∈ N(g x₀; Ω)`. -/
theorem comp_mem_normalCone_preimage_iff_of_surjective {g : E → F} {D : E → E →L[ℝ] F}
    {x₀ : E} (hD : ∀ᶠ x in 𝓝 x₀, HasStrictFDerivAt g (D x) x) (hDc : ContinuousAt D x₀)
    (hA : Function.Surjective (D x₀)) (hK : (D x₀).ker.ClosedComplemented)
    {v : StrongDual ℝ F} :
    v.comp (D x₀) ∈ normalCone (g ⁻¹' Ω) x₀ ↔ v ∈ normalCone Ω (g x₀) := by
  rw [normalCone_preimage_of_surjective hD hDc hA hK]
  exact (comp_injective_of_surjective hA).mem_set_image

end Surjective

section FiniteDimensional

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [CompleteSpace E] in
/-- Exercise 1.54(i) of [Mordukhovich 2018] in finite dimensions: for `g` strictly
differentiable at `x₀` with surjective (full-rank) derivative `A`,
`N̂(x₀; g⁻¹(Ω)) = A* N̂(g x₀; Ω)`. -/
theorem regularNormalCone_preimage_of_surjective_of_finiteDimensional {g : E → F}
    {A : E →L[ℝ] F} {x₀ : E} (hg : HasStrictFDerivAt g A x₀) (hA : Function.Surjective A) :
    regularNormalCone (g ⁻¹' Ω) x₀ =
      (fun v : StrongDual ℝ F ↦ v.comp A) '' regularNormalCone Ω (g x₀) :=
  haveI := FiniteDimensional.complete ℝ E
  haveI := FiniteDimensional.complete ℝ F
  regularNormalCone_preimage_of_surjective hg hA
    (Submodule.ClosedComplemented.of_finiteDimensional _)

omit [CompleteSpace E] in
/-- Exercise 1.54(ii) of [Mordukhovich 2018] in finite dimensions: for `g` of class `C¹`
around `x₀` with surjective (full-rank) derivative `∇g(x₀) = D x₀`,
`N(x₀; g⁻¹(Ω)) = ∇g(x₀)* N(g x₀; Ω)`. -/
theorem normalCone_preimage_of_surjective_of_finiteDimensional {g : E → F}
    {D : E → E →L[ℝ] F} {x₀ : E} (hD : ∀ᶠ x in 𝓝 x₀, HasStrictFDerivAt g (D x) x)
    (hDc : ContinuousAt D x₀) (hA : Function.Surjective (D x₀)) :
    normalCone (g ⁻¹' Ω) x₀ = (fun v : StrongDual ℝ F ↦ v.comp (D x₀)) '' normalCone Ω (g x₀) :=
  haveI := FiniteDimensional.complete ℝ E
  haveI := FiniteDimensional.complete ℝ F
  normalCone_preimage_of_surjective hD hDc hA (Submodule.ClosedComplemented.of_finiteDimensional _)

end FiniteDimensional

end VariationalAnalysis
