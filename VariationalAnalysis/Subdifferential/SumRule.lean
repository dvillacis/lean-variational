/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import VariationalAnalysis.Normal.Intersection
import VariationalAnalysis.Subdifferential.EpigraphClosed

/-!
# Subdifferential sum rules

The sum rules for basic and singular subgradients [Mordukhovich 2018, Thm. 2.19]: for
`φ₁, φ₂ : E → EReal` finite at `x₀`, with epigraphs locally closed around `(x₀, φᵢ x₀)` (e.g.
lower semicontinuous around `x₀`, `locallyClosed_epi_of_lowerSemicontinuousOn`), under the
singular qualification condition `∂^∞φ₁(x₀) ∩ (-∂^∞φ₂(x₀)) = {0}` (2.34),

  `∂(φ₁ + φ₂)(x₀) ⊆ ∂φ₁(x₀) + ∂φ₂(x₀)`  (2.35),
  `∂^∞(φ₁ + φ₂)(x₀) ⊆ ∂^∞φ₁(x₀) + ∂^∞φ₂(x₀)`  (2.36).

The proof follows the book: the basic intersection rule (Thm. 2.16) is applied in
`(E × ℝ) × ℝ` to the sets `Θ₁ = {((x, α₁), α₂) | φ₁ x ≤ α₁}` and
`Θ₂ = {((x, α₁), α₂) | φ₂ x ≤ α₂}`. The step "`(v, -λ, -λ)` is normal to `Θ₁ ∩ Θ₂`" uses that
`φ₁` and `φ₂` are lower semicontinuous at `x₀` (a consequence of the local closedness of the
epigraphs), which lets points of `epi (φ₁ + φ₂)` near `(x₀, φ₁ x₀ + φ₂ x₀)` be split into points
of `Θ₁ ∩ Θ₂` near `(x₀, φ₁ x₀, φ₂ x₀)`.

Sums of sets are pointwise sums (`open scoped Pointwise`).

## Main results

* `regularSubdiff_add_subset`: `∂̂φ₁(x₀) + ∂̂φ₂(x₀) ⊆ ∂̂(φ₁ + φ₂)(x₀)`.
* `subdiff_add_subset`, `singularSubdiff_add_subset`: Thm. 2.19 of [Mordukhovich 2018], (2.35)
  and (2.36).
* `subdiff_add_eq`: Thm. 2.19, equality in (2.35) and lower regularity of the sum for lower
  regular functions.
* `subdiff_add_subset_of_lipschitz`, `subdiff_lipschitz_add_subset`: Cor. 2.20 of
  [Mordukhovich 2018] (semi-Lipschitzian sum rule); `exists_mem_subdiff_norm_sub_le_of_lipschitz`
  and `exists_mem_subdiff_norm_le_of_isLocalMin_add` are the forms used in Ekeland-type
  arguments.
* `subdiff_sum_subset`, `singularSubdiff_sum_subset`, `subdiff_sum_eq`: Cor. 2.21 of
  [Mordukhovich 2018] (finite sums).

The equality in (2.36) and the epigraphical regularity of `φ₁ + φ₂` for epigraphically regular
`φ₁, φ₂` (last statement of Thm. 2.19) are not formalized: they need a Lipschitzian lifting of
`epi (φ₁ + φ₂)` to `Θ₁ ∩ Θ₂` (metric regularity of the constraint system, Ch. 3 of the book),
which the book's "verified similarly" does not provide.
-/

open Filter Topology Set Metric
open scoped Pointwise

namespace VariationalAnalysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {φ φ₁ φ₂ : E → EReal} {x₀ : E} {r r₁ r₂ : ℝ}

section Regular

/-- [Mordukhovich 2018, proof of Thm. 2.19]: `∂̂φ₁(x₀) + ∂̂φ₂(x₀) ⊆ ∂̂(φ₁ + φ₂)(x₀)` holds for
arbitrary functions. -/
theorem regularSubdiff_add_subset :
    regularSubdiff φ₁ x₀ + regularSubdiff φ₂ x₀ ⊆ regularSubdiff (fun x ↦ φ₁ x + φ₂ x) x₀ := by
  rintro _ ⟨u, ⟨r₁, hr₁, hu⟩, w, ⟨r₂, hr₂, hw⟩, rfl⟩
  refine ⟨r₁ + r₂, by simp only [hr₁, hr₂, EReal.coe_add], fun ε hε ↦ ?_⟩
  filter_upwards [hu (ε / 2) (half_pos hε), hw (ε / 2) (half_pos hε)] with x hx₁ hx₂
  calc ((r₁ + r₂ + (u + w) (x - x₀) - ε * ‖x - x₀‖ : ℝ) : EReal)
      = ((r₁ + u (x - x₀) - ε / 2 * ‖x - x₀‖ : ℝ) : EReal) +
          ((r₂ + w (x - x₀) - ε / 2 * ‖x - x₀‖ : ℝ) : EReal) := by
        rw [← EReal.coe_add]; congr 1; simp only [add_apply]; ring
    _ ≤ φ₁ x + φ₂ x := add_le_add hx₁ hx₂

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem add_apply_eq_coe (hr₁ : φ₁ x₀ = r₁) (hr₂ : φ₂ x₀ = r₂) :
    (fun x ↦ φ₁ x + φ₂ x) x₀ = ((r₁ + r₂ : ℝ) : EReal) := by
  simp only [hr₁, hr₂, EReal.coe_add]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- A continuous linear map `A` with `A (Ω) ⊆ Θ` maps nearby points of `Ω` to nearby points of
`Θ`. -/
theorem tendsto_nhdsWithin_of_mapsTo {A : E → F} (hA : Continuous A) {Ω : Set E} {Θ : Set F}
    (hmaps : MapsTo A Ω Θ) (x : E) : Tendsto A (𝓝[Ω] x) (𝓝[Θ] (A x)) :=
  tendsto_nhdsWithin_iff.2 ⟨(hA.tendsto x).mono_left nhdsWithin_le_nhds,
    eventually_nhdsWithin_of_forall fun _ hy ↦ hmaps hy⟩

/-- Regular normals pull back along continuous linear maps: if `A (Ω) ⊆ Θ`, `x ∈ Ω` and
`v ∈ N̂(A x; Θ)`, then `v ∘ A ∈ N̂(x; Ω)`. -/
theorem comp_mem_regularNormalCone_of_mapsTo (A : E →L[ℝ] F) {Ω : Set E} {Θ : Set F}
    (hmaps : MapsTo A Ω Θ) {x : E} (hx : x ∈ Ω) {v : StrongDual ℝ F}
    (hv : v ∈ regularNormalCone Θ (A x)) : v.comp A ∈ regularNormalCone Ω x := by
  refine ⟨hx, fun ε hε ↦ ?_⟩
  set c := ‖A‖
  have hδ : 0 < ε / (c + 1) := div_pos hε (by positivity)
  filter_upwards [(tendsto_nhdsWithin_of_mapsTo A.continuous hmaps x).eventually
    (hv.2 _ hδ)] with y hy
  have hA : ‖A y - A x‖ ≤ c * ‖y - x‖ := by rw [← map_sub]; exact A.le_opNorm _
  have hfrac : ε / (c + 1) * c ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith [norm_nonneg A]
  calc (v.comp A) (y - x) = v (A y - A x) := by simp [map_sub]
    _ ≤ ε / (c + 1) * ‖A y - A x‖ := hy
    _ ≤ ε / (c + 1) * (c * ‖y - x‖) := by gcongr
    _ ≤ ε * ‖y - x‖ := by rw [← mul_assoc]; gcongr

end Regular

section Lifting

/-! ### The sets `Θ₁, Θ₂` in `(E × ℝ) × ℝ` -/

/-- The linear isomorphism `((x, a), b) ↦ ((x, b), a)` of `(E × ℝ) × ℝ`. -/
noncomputable def swapLast : ((E × ℝ) × ℝ) ≃L[ℝ] ((E × ℝ) × ℝ) :=
  (ContinuousLinearEquiv.prodAssoc ℝ E ℝ ℝ).trans
    (((ContinuousLinearEquiv.refl ℝ E).prodCongr (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ)).trans
      (ContinuousLinearEquiv.prodAssoc ℝ E ℝ ℝ).symm)

omit [NormedSpace ℝ F] in
@[simp] theorem swapLast_apply (x : E) (a b : ℝ) : swapLast ((x, a), b) = ((x, b), a) := rfl

/-- The linear map `((x, a), b) ↦ (x, a + b)` from `(E × ℝ) × ℝ` to `E × ℝ`. -/
noncomputable def sumLift : ((E × ℝ) × ℝ) →L[ℝ] E × ℝ :=
  ((ContinuousLinearMap.fst ℝ E ℝ).comp (ContinuousLinearMap.fst ℝ (E × ℝ) ℝ)).prod
    ((ContinuousLinearMap.snd ℝ E ℝ).comp (ContinuousLinearMap.fst ℝ (E × ℝ) ℝ) +
      ContinuousLinearMap.snd ℝ (E × ℝ) ℝ)

omit [NormedSpace ℝ F] in
@[simp] theorem sumLift_apply (x : E) (a b : ℝ) : sumLift ((x, a), b) = (x, a + b) := rfl

omit [NormedSpace ℝ F] in
/-- The coordinates of a dual element on `(E × ℝ) × ℝ`. -/
theorem dual_prod_prod_apply (m : StrongDual ℝ ((E × ℝ) × ℝ)) (x : E) (a b : ℝ) :
    m ((x, a), b) = m ((x, 0), 0) + a * m ((0, 1), 0) + b * m ((0, 0), 1) := by
  rw [show (((x, a), b) : (E × ℝ) × ℝ) = ((x, 0), 0) + a • ((0, 1), 0) + b • ((0, 0), 1) by
    simp, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

omit [NormedSpace ℝ F] in
theorem mem_image_swapLast_prod_univ_iff {S : Set (E × ℝ)} {p : (E × ℝ) × ℝ} :
    p ∈ swapLast '' (S ×ˢ univ) ↔ (p.1.1, p.2) ∈ S := by
  constructor
  · rintro ⟨⟨⟨x, b⟩, a⟩, ⟨hS, -⟩, rfl⟩
    simpa using hS
  · intro h
    exact ⟨((p.1.1, p.2), p.1.2), ⟨h, mem_univ _⟩, rfl⟩

omit [NormedSpace ℝ F] in
/-- `N(t; ℝ) = {0}`. -/
theorem apply_one_eq_zero_of_mem_normalCone_univ {c : StrongDual ℝ ℝ} {t : ℝ}
    (hc : c ∈ normalCone (univ : Set ℝ) t) : c 1 = 0 := by
  rw [normalCone_of_mem_interior (by simp), mem_singleton_iff] at hc
  simp [hc]

variable [FiniteDimensional ℝ E]

omit [NormedSpace ℝ F] in
/-- [Mordukhovich 2018, proof of Thm. 2.19]: under (2.34), a basic normal `ℓ` to `epi (φ₁ + φ₂)`
at `(x₀, r₁ + r₂)` splits into basic normals `ℓ₁` to `epi φ₁` at `(x₀, r₁)` and `ℓ₂` to `epi φ₂`
at `(x₀, r₂)` with `ℓ₁ (x, 0) + ℓ₂ (x, 0) = ℓ (x, 0)` and `ℓ₁ (0, 1) = ℓ₂ (0, 1) = ℓ (0, 1)`. -/
theorem exists_mem_normalCone_epi_of_mem_normalCone_epi_add (hr₁ : φ₁ x₀ = r₁)
    (hr₂ : φ₂ x₀ = r₂)
    (hloc₁ : ∃ ρ > 0, IsClosed (φ₁.Epi univ ∩ closedBall ((x₀, r₁) : E × ℝ) ρ))
    (hloc₂ : ∃ ρ > 0, IsClosed (φ₂.Epi univ ∩ closedBall ((x₀, r₂) : E × ℝ) ρ))
    (hqc : ∀ v ∈ singularSubdiff φ₁ x₀, -v ∈ singularSubdiff φ₂ x₀ → v = 0)
    {ℓ : StrongDual ℝ (E × ℝ)}
    (hℓ : ℓ ∈ normalCone ((fun x ↦ φ₁ x + φ₂ x).Epi univ) (x₀, r₁ + r₂)) :
    ∃ ℓ₁ ∈ normalCone (φ₁.Epi univ) (x₀, r₁), ∃ ℓ₂ ∈ normalCone (φ₂.Epi univ) (x₀, r₂),
      ℓ₁.comp (ContinuousLinearMap.inl ℝ E ℝ) + ℓ₂.comp (ContinuousLinearMap.inl ℝ E ℝ) =
        ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ) ∧ ℓ₁ (0, 1) = ℓ (0, 1) ∧ ℓ₂ (0, 1) = ℓ (0, 1) := by
  set Θ₁ : Set ((E × ℝ) × ℝ) := φ₁.Epi univ ×ˢ univ
  set Θ₂ : Set ((E × ℝ) × ℝ) := swapLast '' (φ₂.Epi univ ×ˢ univ)
  set p₀ : (E × ℝ) × ℝ := ((x₀, r₁), r₂)
  have hp₀ : swapLast ((x₀, r₂), r₁) = p₀ := rfl
  have hΘ₂ : ∀ p, p ∈ Θ₂ ↔ φ₂ p.1.1 ≤ p.2 := fun p ↦ by
    rw [mem_image_swapLast_prod_univ_iff]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨mem_univ _, h⟩⟩
  have hp₀₁ : p₀ ∈ Θ₁ := ⟨⟨mem_univ _, hr₁.le⟩, mem_univ _⟩
  have hp₀₂ : p₀ ∈ Θ₂ := (hΘ₂ p₀).2 hr₂.le
  -- normals to `Θ₁` and `Θ₂` at `p₀` (Prop. 1.4)
  have hN₁ : ∀ m, m ∈ normalCone Θ₁ p₀ →
      m.comp (ContinuousLinearMap.inl ℝ (E × ℝ) ℝ) ∈ normalCone (φ₁.Epi univ) (x₀, r₁) ∧
        m ((0, 0), 1) = 0 := fun m hm ↦ by
    obtain ⟨h1, h2⟩ := mem_normalCone_prod_iff.1 hm
    have h3 : m (((0 : E), (0 : ℝ)), (1 : ℝ)) = 0 := apply_one_eq_zero_of_mem_normalCone_univ h2
    exact ⟨h1, h3⟩
  have hN₂ : ∀ m, m ∈ normalCone Θ₂ p₀ →
      (m.comp (swapLast (E := E) : ((E × ℝ) × ℝ) →L[ℝ] ((E × ℝ) × ℝ))).comp
        (ContinuousLinearMap.inl ℝ (E × ℝ) ℝ) ∈ normalCone (φ₂.Epi univ) (x₀, r₂) ∧
        m ((0, 1), 0) = 0 := fun m hm ↦ by
    have hm' : m ∈ normalCone (swapLast '' (φ₂.Epi univ ×ˢ univ)) (swapLast ((x₀, r₂), r₁)) :=
      hm
    obtain ⟨h1, h2⟩ :=
      mem_normalCone_prod_iff.1 ((mem_normalCone_image_iff (swapLast (E := E))).1 hm')
    have h3 : m (swapLast (((0 : E), (0 : ℝ)), (1 : ℝ))) = 0 :=
      apply_one_eq_zero_of_mem_normalCone_univ h2
    rw [swapLast_apply] at h3
    exact ⟨h1, h3⟩
  -- Step 1: `ℓ ∘ L` is a basic normal to `Θ₁ ∩ Θ₂` at `p₀`
  have hmaps : MapsTo (sumLift (E := E)) (Θ₁ ∩ Θ₂) ((fun x ↦ φ₁ x + φ₂ x).Epi univ) := by
    rintro ⟨⟨x, a⟩, b⟩ ⟨⟨⟨-, ha⟩, -⟩, hb⟩
    refine ⟨mem_univ _, ?_⟩
    rw [hΘ₂] at hb
    simp only [sumLift_apply, EReal.coe_add]
    exact add_le_add ha hb
  have hstep1 : ℓ.comp (sumLift (E := E)) ∈ normalCone (Θ₁ ∩ Θ₂) p₀ := by
    obtain ⟨-, y, m, hy, hm, hmem⟩ := hℓ
    have hy' := tendsto_nhdsWithin_iff.1 hy
    obtain ⟨a, ha, hsplit⟩ := exists_tendsto_split_of_mem_epi_add hr₁ hr₂
      (lowerSemicontinuousAt_of_locallyClosed_epi hr₁ hloc₁)
      (lowerSemicontinuousAt_of_locallyClosed_epi hr₂ hloc₂) hy'.1 hy'.2
    set q : ℕ → (E × ℝ) × ℝ := fun k ↦ (((y k).1, a k), (y k).2 - a k)
    have hq : Tendsto q atTop (𝓝 p₀) := by
      have h1 : Tendsto (fun k ↦ (y k).1) atTop (𝓝 x₀) := (continuous_fst.tendsto _).comp hy'.1
      have h2 : Tendsto (fun k ↦ (y k).2) atTop (𝓝 (r₁ + r₂)) :=
        (continuous_snd.tendsto _).comp hy'.1
      have h3 := (h1.prodMk_nhds ha).prodMk_nhds (h2.sub ha)
      simpa using h3
    have hqΘ : ∀ᶠ k in atTop, q k ∈ Θ₁ ∩ Θ₂ := hsplit.mono fun k hk ↦
      ⟨⟨⟨mem_univ _, hk.1⟩, mem_univ _⟩, (hΘ₂ _).2 hk.2⟩
    have hLq : ∀ k, (sumLift (E := E)) (q k) = y k := fun k ↦ by simp [q]
    refine ⟨⟨hp₀₁, hp₀₂⟩, mem_outerLimit_of_eventually q (fun k ↦ (m k).comp (sumLift (E := E)))
      (tendsto_nhdsWithin_iff.2 ⟨hq, hqΘ⟩) (tendsto_dual_comp hm tendsto_const_nhds) ?_⟩
    filter_upwards [hqΘ] with k hk
    exact comp_mem_regularNormalCone_of_mapsTo (sumLift (E := E)) hmaps hk
      (by rw [hLq]; exact hmem k)
  -- Step 2: the intersection rule (Thm. 2.16) in `(E × ℝ) × ℝ`
  have hloc₁' : ∃ ρ > 0, IsClosed (Θ₁ ∩ closedBall p₀ ρ) :=
    locallyClosed_prod hloc₁ ⟨1, one_pos, isClosed_univ.inter isClosed_closedBall⟩
  have hloc₂' : ∃ ρ > 0, IsClosed (Θ₂ ∩ closedBall p₀ ρ) :=
    locallyClosed_image (swapLast (E := E)) (locallyClosed_prod hloc₂
      ⟨1, one_pos, isClosed_univ.inter isClosed_closedBall⟩)
  have hqc' : ∀ m ∈ normalCone Θ₁ p₀, -m ∈ normalCone Θ₂ p₀ → m = 0 := by
    intro m hm hm'
    obtain ⟨h1, h1'⟩ := hN₁ m hm
    obtain ⟨h2, h2'⟩ := hN₂ (-m) hm'
    simp only [neg_apply, neg_eq_zero] at h2'
    set u := (m.comp (ContinuousLinearMap.inl ℝ (E × ℝ) ℝ)).comp (ContinuousLinearMap.inl ℝ E ℝ)
    have hu₁ : u ∈ singularSubdiff φ₁ x₀ := by
      rw [mem_singularSubdiff_iff hr₁]
      have h0 : (m.comp (ContinuousLinearMap.inl ℝ (E × ℝ) ℝ)) (0, 1) = 0 := h2'
      rwa [eq_coprod_zero (m.comp (ContinuousLinearMap.inl ℝ (E × ℝ) ℝ)) h0] at h1
    have hu₂ : -u ∈ singularSubdiff φ₂ x₀ := by
      rw [mem_singularSubdiff_iff hr₂]
      set n := ((-m).comp (swapLast (E := E) : ((E × ℝ) × ℝ) →L[ℝ] ((E × ℝ) × ℝ))).comp
        (ContinuousLinearMap.inl ℝ (E × ℝ) ℝ)
      have hn : n (0, 1) = 0 := by
        change -m (swapLast (((0 : E), (1 : ℝ)), (0 : ℝ))) = 0
        rw [swapLast_apply, h1', neg_zero]
      have hn' : n.comp (ContinuousLinearMap.inl ℝ E ℝ) = -u := by
        refine ContinuousLinearMap.ext fun x ↦ ?_
        change -m (swapLast ((x, (0 : ℝ)), (0 : ℝ))) = -m ((x, 0), 0)
        rw [swapLast_apply]
      rw [eq_coprod_zero n hn, hn'] at h2
      exact h2
    have hu0 := hqc u hu₁ hu₂
    refine ContinuousLinearMap.ext fun p ↦ ?_
    obtain ⟨⟨x, a⟩, b⟩ := p
    have hx : m ((x, 0), 0) = 0 := by
      have := congrArg (fun f ↦ f x) hu0
      simpa [u] using this
    rw [dual_prod_prod_apply, hx, h1', h2']
    simp
  obtain ⟨m₁, hm₁, m₂, hm₂, hsum⟩ := normalCone_inter_subset hloc₁' hloc₂' hqc' hstep1
  obtain ⟨h₁, h₁'⟩ := hN₁ m₁ hm₁
  obtain ⟨h₂, h₂'⟩ := hN₂ m₂ hm₂
  have hsum' : ∀ p, m₁ p + m₂ p = ℓ ((sumLift (E := E)) p) := fun p ↦ by
    have := congrArg (fun f ↦ f p) hsum
    simpa using this
  refine ⟨_, h₁, _, h₂, ?_, ?_, ?_⟩
  · ext x
    have := hsum' ((x, 0), 0)
    simpa using this
  · have := hsum' ((0, 1), 0)
    simp only [sumLift_apply, add_zero, h₂'] at this
    simpa using this
  · have := hsum' ((0, 0), 1)
    simp only [sumLift_apply, zero_add, h₁'] at this
    simpa using this

end Lifting

section SumRule

/-! ### Sum rules for two functions -/

variable [FiniteDimensional ℝ E]

omit [NormedSpace ℝ F] in
/-- Thm. 2.19 of [Mordukhovich 2018] (subdifferential sum rule), (2.35): let `φ₁, φ₂` be finite at
`x₀` with epigraphs locally closed around `(x₀, φᵢ x₀)` (e.g. l.s.c. around `x₀`), and assume the
singular qualification condition (2.34) `∂^∞φ₁(x₀) ∩ (-∂^∞φ₂(x₀)) = {0}`. Then
`∂(φ₁ + φ₂)(x₀) ⊆ ∂φ₁(x₀) + ∂φ₂(x₀)`. -/
theorem subdiff_add_subset (hr₁ : φ₁ x₀ = r₁) (hr₂ : φ₂ x₀ = r₂)
    (hloc₁ : ∃ ρ > 0, IsClosed (φ₁.Epi univ ∩ closedBall ((x₀, r₁) : E × ℝ) ρ))
    (hloc₂ : ∃ ρ > 0, IsClosed (φ₂.Epi univ ∩ closedBall ((x₀, r₂) : E × ℝ) ρ))
    (hqc : ∀ v ∈ singularSubdiff φ₁ x₀, -v ∈ singularSubdiff φ₂ x₀ → v = 0) :
    subdiff (fun x ↦ φ₁ x + φ₂ x) x₀ ⊆ subdiff φ₁ x₀ + subdiff φ₂ x₀ := by
  intro v hv
  rw [mem_subdiff_iff (φ := fun x ↦ φ₁ x + φ₂ x) (add_apply_eq_coe hr₁ hr₂)] at hv
  obtain ⟨ℓ₁, h₁, ℓ₂, h₂, hsum, hc₁, hc₂⟩ :=
    exists_mem_normalCone_epi_of_mem_normalCone_epi_add hr₁ hr₂ hloc₁ hloc₂ hqc hv
  simp only [ContinuousLinearMap.coprod_apply, map_zero, zero_add] at hc₁ hc₂
  refine ⟨_, (mem_subdiff_iff hr₁).2 (by rwa [← eq_coprod_neg_one ℓ₁ (by simpa using hc₁)]),
    _, (mem_subdiff_iff hr₂).2 (by rwa [← eq_coprod_neg_one ℓ₂ (by simpa using hc₂)]), ?_⟩
  simpa using hsum

omit [NormedSpace ℝ F] in
/-- Thm. 2.19 of [Mordukhovich 2018] (singular subdifferential sum rule), (2.36): under the
assumptions of `subdiff_add_subset`, `∂^∞(φ₁ + φ₂)(x₀) ⊆ ∂^∞φ₁(x₀) + ∂^∞φ₂(x₀)`. -/
theorem singularSubdiff_add_subset (hr₁ : φ₁ x₀ = r₁) (hr₂ : φ₂ x₀ = r₂)
    (hloc₁ : ∃ ρ > 0, IsClosed (φ₁.Epi univ ∩ closedBall ((x₀, r₁) : E × ℝ) ρ))
    (hloc₂ : ∃ ρ > 0, IsClosed (φ₂.Epi univ ∩ closedBall ((x₀, r₂) : E × ℝ) ρ))
    (hqc : ∀ v ∈ singularSubdiff φ₁ x₀, -v ∈ singularSubdiff φ₂ x₀ → v = 0) :
    singularSubdiff (fun x ↦ φ₁ x + φ₂ x) x₀ ⊆ singularSubdiff φ₁ x₀ + singularSubdiff φ₂ x₀ := by
  intro v hv
  rw [mem_singularSubdiff_iff (φ := fun x ↦ φ₁ x + φ₂ x) (add_apply_eq_coe hr₁ hr₂)] at hv
  obtain ⟨ℓ₁, h₁, ℓ₂, h₂, hsum, hc₁, hc₂⟩ :=
    exists_mem_normalCone_epi_of_mem_normalCone_epi_add hr₁ hr₂ hloc₁ hloc₂ hqc hv
  simp only [ContinuousLinearMap.coprod_apply, map_zero, zero_add] at hc₁ hc₂
  refine ⟨_, (mem_singularSubdiff_iff hr₁).2 (by rwa [← eq_coprod_zero ℓ₁ hc₁]),
    _, (mem_singularSubdiff_iff hr₂).2 (by rwa [← eq_coprod_zero ℓ₂ hc₂]), ?_⟩
  simpa using hsum

omit [NormedSpace ℝ F] in
/-- Thm. 2.19 of [Mordukhovich 2018], equality statement: if moreover `φ₁` and `φ₂` are lower
regular at `x₀`, then so is `φ₁ + φ₂`, and (2.35) holds as an equality. -/
theorem subdiff_add_eq (hr₁ : φ₁ x₀ = r₁) (hr₂ : φ₂ x₀ = r₂)
    (hloc₁ : ∃ ρ > 0, IsClosed (φ₁.Epi univ ∩ closedBall ((x₀, r₁) : E × ℝ) ρ))
    (hloc₂ : ∃ ρ > 0, IsClosed (φ₂.Epi univ ∩ closedBall ((x₀, r₂) : E × ℝ) ρ))
    (hqc : ∀ v ∈ singularSubdiff φ₁ x₀, -v ∈ singularSubdiff φ₂ x₀ → v = 0)
    (hreg₁ : LowerRegularAt φ₁ x₀) (hreg₂ : LowerRegularAt φ₂ x₀) :
    subdiff (fun x ↦ φ₁ x + φ₂ x) x₀ = subdiff φ₁ x₀ + subdiff φ₂ x₀ ∧
      LowerRegularAt (fun x ↦ φ₁ x + φ₂ x) x₀ := by
  have h1 := subdiff_add_subset hr₁ hr₂ hloc₁ hloc₂ hqc
  have h2 : subdiff φ₁ x₀ + subdiff φ₂ x₀ ⊆ regularSubdiff (fun x ↦ φ₁ x + φ₂ x) x₀ := by
    rw [hreg₁, hreg₂]; exact regularSubdiff_add_subset
  exact ⟨subset_antisymm h1 (h2.trans regularSubdiff_subset_subdiff),
    subset_antisymm (h1.trans h2) regularSubdiff_subset_subdiff⟩

end SumRule

section Lipschitz

/-! ### The semi-Lipschitzian sum rule -/

variable [FiniteDimensional ℝ E] {f : E → ℝ} {U : Set E} {L : NNReal}

omit [NormedSpace ℝ F] in
/-- Cor. 2.20 of [Mordukhovich 2018] (semi-Lipschitzian sum rule): if `φ` is finite at `x₀` with
epigraph locally closed around `(x₀, φ x₀)` and `f` is Lipschitz on a neighborhood of `x₀`, then
`∂(φ + f)(x₀) ⊆ ∂φ(x₀) + ∂f(x₀)`. -/
theorem subdiff_add_subset_of_lipschitz (hr : φ x₀ = r)
    (hloc : ∃ ρ > 0, IsClosed (φ.Epi univ ∩ closedBall ((x₀, r) : E × ℝ) ρ))
    (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U) :
    subdiff (fun x ↦ φ x + f x) x₀ ⊆ subdiff φ x₀ + subdiff (fun x ↦ (f x : EReal)) x₀ := by
  refine subdiff_add_subset (φ₂ := fun x ↦ (f x : EReal)) hr rfl hloc
    (locallyClosed_epi_of_continuousOn hU hL.continuousOn (f x₀)) fun v _ hv ↦ ?_
  rw [singularSubdiff_eq_zero_of_lipschitz hU hL, mem_singleton_iff, neg_eq_zero] at hv
  exact hv

omit [NormedSpace ℝ F] in
/-- Cor. 2.20 of [Mordukhovich 2018] with the Lipschitz function first:
`∂(f + φ)(x₀) ⊆ ∂f(x₀) + ∂φ(x₀)`. -/
theorem subdiff_lipschitz_add_subset (hr : φ x₀ = r)
    (hloc : ∃ ρ > 0, IsClosed (φ.Epi univ ∩ closedBall ((x₀, r) : E × ℝ) ρ))
    (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U) :
    subdiff (fun x ↦ (f x : EReal) + φ x) x₀ ⊆
      subdiff (fun x ↦ (f x : EReal)) x₀ + subdiff φ x₀ := by
  simp_rw [add_comm (f _ : EReal), add_comm (subdiff (fun x ↦ (f x : EReal)) x₀)]
  exact subdiff_add_subset_of_lipschitz hr hloc hU hL

omit [NormedSpace ℝ F] in
/-- Cor. 2.20 of [Mordukhovich 2018] with the bound of Thm. 1.22: if `f` is `L`-Lipschitz near
`x₀`, every `v ∈ ∂(φ + f)(x₀)` is within `L` of some `u ∈ ∂φ(x₀)`. -/
theorem exists_mem_subdiff_norm_sub_le_of_lipschitz (hr : φ x₀ = r)
    (hloc : ∃ ρ > 0, IsClosed (φ.Epi univ ∩ closedBall ((x₀, r) : E × ℝ) ρ))
    (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U) {v : StrongDual ℝ E}
    (hv : v ∈ subdiff (fun x ↦ φ x + f x) x₀) : ∃ u ∈ subdiff φ x₀, ‖v - u‖ ≤ L := by
  obtain ⟨u, hu, w, hw, rfl⟩ := subdiff_add_subset_of_lipschitz hr hloc hU hL hv
  exact ⟨u, hu, by simpa using norm_le_of_mem_subdiff_of_lipschitz hU hL hw⟩

omit [NormedSpace ℝ F] in
/-- Fermat rule for semi-Lipschitzian sums [Mordukhovich 2018, Prop. 1.30(i) and Cor. 2.20]: if
`x₀` is a local minimizer of `φ + f` with `f` `L`-Lipschitz near `x₀`, then some `u ∈ ∂φ(x₀)` has
`‖u‖ ≤ L`, i.e. `0 ∈ ∂φ(x₀) + L 𝔹*`. -/
theorem exists_mem_subdiff_norm_le_of_isLocalMin_add (hr : φ x₀ = r)
    (hloc : ∃ ρ > 0, IsClosed (φ.Epi univ ∩ closedBall ((x₀, r) : E × ℝ) ρ))
    (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U) (hmin : IsLocalMin (fun x ↦ φ x + f x) x₀) :
    ∃ u ∈ subdiff φ x₀, ‖u‖ ≤ L := by
  obtain ⟨u, hu, h⟩ := exists_mem_subdiff_norm_sub_le_of_lipschitz hr hloc hU hL
    (zero_mem_subdiff_of_isLocalMin hmin (by simp only [hr, EReal.coe_add] :
      (fun x ↦ φ x + f x) x₀ = ((r + f x₀ : ℝ) : EReal)))
  exact ⟨u, hu, by simpa using h⟩

end Lipschitz

section FiniteSum

/-! ### Finite sums -/

variable {ι : Type*} {φ : ι → E → EReal} {r : ι → ℝ}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem sum_apply_eq_coe (s : Finset ι) (hr : ∀ i ∈ s, φ i x₀ = r i) :
    ∑ i ∈ s, φ i x₀ = ((∑ i ∈ s, r i : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, EReal.coe_add,
      hr j (Finset.mem_insert_self _ _), ih fun i hi ↦ hr i (Finset.mem_insert_of_mem hi)]

omit [NormedSpace ℝ E] in
/-- The epigraph of a finite sum of functions with locally closed epigraphs is locally closed. -/
theorem locallyClosed_epi_sum (s : Finset ι) (hr : ∀ i ∈ s, φ i x₀ = r i)
    (hloc : ∀ i ∈ s, ∃ ρ > 0, IsClosed ((φ i).Epi univ ∩ closedBall ((x₀, r i) : E × ℝ) ρ)) :
    ∃ ρ > 0, IsClosed ((fun x ↦ ∑ i ∈ s, φ i x).Epi univ ∩
      closedBall ((x₀, ∑ i ∈ s, r i) : E × ℝ) ρ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using locallyClosed_epi_of_continuousOn (f := fun _ : E ↦ (0 : ℝ)) (x₀ := x₀)
      univ_mem continuous_const.continuousOn 0
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact locallyClosed_epi_add_of_locallyClosed (hr j (Finset.mem_insert_self _ _))
      (sum_apply_eq_coe s fun i hi ↦ hr i (Finset.mem_insert_of_mem hi))
      (hloc j (Finset.mem_insert_self _ _))
      (ih (fun i hi ↦ hr i (Finset.mem_insert_of_mem hi))
        fun i hi ↦ hloc i (Finset.mem_insert_of_mem hi))

omit [NormedSpace ℝ F] in
/-- Cor. 2.21 of [Mordukhovich 2018], regular subgradients: `∑ᵢ ∂̂φᵢ(x₀) ⊆ ∂̂(∑ᵢ φᵢ)(x₀)` holds
for arbitrary functions. -/
theorem sum_regularSubdiff_subset (s : Finset ι) :
    ∑ i ∈ s, regularSubdiff (φ i) x₀ ⊆ regularSubdiff (fun x ↦ ∑ i ∈ s, φ i x) x₀ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro v hv
    rw [Finset.sum_empty, Set.mem_zero] at hv
    have h0 : (fun x : E ↦ ∑ i ∈ (∅ : Finset ι), φ i x) = fun x ↦ ((0 : ℝ) : EReal) := by
      ext; simp
    rw [h0, regularSubdiff_of_hasFDerivAt (hasFDerivAt_const 0 x₀), hv]
    exact mem_singleton _
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    simp only [Finset.sum_insert hj]
    exact (Set.add_subset_add_left ih).trans regularSubdiff_add_subset

variable [FiniteDimensional ℝ E]

omit [NormedSpace ℝ F] in
/-- Cor. 2.21 of [Mordukhovich 2018] over a finset `s`, (2.38)–(2.39): if the `φᵢ`, `i ∈ s`, are
finite at `x₀` with epigraphs locally closed around `(x₀, φᵢ x₀)` and the qualification condition
(2.37) holds (`vᵢ ∈ ∂^∞φᵢ(x₀)`, `∑ vᵢ = 0` imply all `vᵢ = 0`), then
`∂(∑ φᵢ)(x₀) ⊆ ∑ ∂φᵢ(x₀)` and `∂^∞(∑ φᵢ)(x₀) ⊆ ∑ ∂^∞φᵢ(x₀)`. -/
theorem subdiff_sum_subset_and (s : Finset ι) (hr : ∀ i ∈ s, φ i x₀ = r i)
    (hloc : ∀ i ∈ s, ∃ ρ > 0, IsClosed ((φ i).Epi univ ∩ closedBall ((x₀, r i) : E × ℝ) ρ))
    (hqc : ∀ v : ι → StrongDual ℝ E, (∀ i ∈ s, v i ∈ singularSubdiff (φ i) x₀) →
      ∑ i ∈ s, v i = 0 → ∀ i ∈ s, v i = 0) :
    subdiff (fun x ↦ ∑ i ∈ s, φ i x) x₀ ⊆ ∑ i ∈ s, subdiff (φ i) x₀ ∧
      singularSubdiff (fun x ↦ ∑ i ∈ s, φ i x) x₀ ⊆ ∑ i ∈ s, singularSubdiff (φ i) x₀ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : (fun x : E ↦ ∑ i ∈ (∅ : Finset ι), φ i x) = fun x ↦ ((0 : ℝ) : EReal) := by
      ext; simp
    rw [h0, subdiff_of_hasFDerivAt_of_continuousAt (f' := fun _ ↦ 0)
      (Eventually.of_forall fun x ↦ hasFDerivAt_const 0 x) continuous_const.continuousAt,
      singularSubdiff_eq_zero_of_lipschitz (f := fun _ ↦ (0 : ℝ)) (L := 0) univ_mem
        (LipschitzWith.const 0).lipschitzOnWith]
    simp [Finset.sum_empty]
  | insert j s hj ih =>
    have hrj := hr j (Finset.mem_insert_self _ _)
    have hr' : ∀ i ∈ s, φ i x₀ = r i := fun i hi ↦ hr i (Finset.mem_insert_of_mem hi)
    have hloc' := fun i hi ↦ hloc i (Finset.mem_insert_of_mem hi)
    -- the qualification condition for the subsystem `s`
    have hqc' : ∀ v : ι → StrongDual ℝ E, (∀ i ∈ s, v i ∈ singularSubdiff (φ i) x₀) →
        ∑ i ∈ s, v i = 0 → ∀ i ∈ s, v i = 0 := by
      intro w hw hsum i hi
      have hne : i ≠ j := fun h ↦ hj (h ▸ hi)
      have := hqc (Function.update w j 0) (fun k hk ↦ by
        rcases Finset.mem_insert.1 hk with rfl | hks
        · simpa using zero_mem_singularSubdiff hrj
        · rw [Function.update_of_ne (fun h ↦ hj (by rwa [h] at hks))]; exact hw k hks)
        (by rw [Finset.sum_insert hj, Function.update_self, zero_add,
          Finset.sum_update_of_notMem hj, hsum]) i (Finset.mem_insert_of_mem hi)
      rwa [Function.update_of_ne hne] at this
    obtain ⟨ih₁, ih₂⟩ := ih hr' hloc' hqc'
    -- the qualification condition (2.34) for `φ j` and `∑_{i ∈ s} φ i`
    have hqc₂ : ∀ u ∈ singularSubdiff (φ j) x₀,
        -u ∈ singularSubdiff (fun x ↦ ∑ i ∈ s, φ i x) x₀ → u = 0 := by
      intro u hu hu'
      obtain ⟨g, hg, hgsum⟩ := (Set.mem_finsetSum _ _ _).1 (ih₂ hu')
      have := hqc (Function.update g j u) (fun k hk ↦ by
        rcases Finset.mem_insert.1 hk with rfl | hks
        · simpa using hu
        · rw [Function.update_of_ne (fun h ↦ hj (by rwa [h] at hks))]; exact hg hks)
        (by rw [Finset.sum_insert hj, Function.update_self, Finset.sum_update_of_notMem hj,
          hgsum, add_neg_cancel]) j (Finset.mem_insert_self _ _)
      simpa using this
    have hsum := sum_apply_eq_coe s hr'
    have hlocs := locallyClosed_epi_sum s hr' hloc'
    simp only [Finset.sum_insert hj]
    exact ⟨(subdiff_add_subset hrj hsum (hloc j (Finset.mem_insert_self _ _)) hlocs hqc₂).trans
      (Set.add_subset_add_left ih₁),
      (singularSubdiff_add_subset hrj hsum (hloc j (Finset.mem_insert_self _ _)) hlocs
        hqc₂).trans (Set.add_subset_add_left ih₂)⟩

omit [NormedSpace ℝ F] in
/-- Cor. 2.21 of [Mordukhovich 2018] (subgradients of finite sums), (2.38): if finitely many
functions `φᵢ` are finite at `x₀` with epigraphs locally closed around `(x₀, φᵢ x₀)` and the
qualification condition (2.37) holds, then `∂(∑ᵢ φᵢ)(x₀) ⊆ ∑ᵢ ∂φᵢ(x₀)`. -/
theorem subdiff_sum_subset [Fintype ι] (hr : ∀ i, φ i x₀ = r i)
    (hloc : ∀ i, ∃ ρ > 0, IsClosed ((φ i).Epi univ ∩ closedBall ((x₀, r i) : E × ℝ) ρ))
    (hqc : ∀ v : ι → StrongDual ℝ E, (∀ i, v i ∈ singularSubdiff (φ i) x₀) → ∑ i, v i = 0 →
      ∀ i, v i = 0) :
    subdiff (fun x ↦ ∑ i, φ i x) x₀ ⊆ ∑ i, subdiff (φ i) x₀ :=
  (subdiff_sum_subset_and Finset.univ (fun i _ ↦ hr i) (fun i _ ↦ hloc i)
    fun v hv hs i _ ↦ hqc v (fun i ↦ hv i (Finset.mem_univ i)) hs i).1

omit [NormedSpace ℝ F] in
/-- Cor. 2.21 of [Mordukhovich 2018] (singular subgradients of finite sums), (2.39). -/
theorem singularSubdiff_sum_subset [Fintype ι] (hr : ∀ i, φ i x₀ = r i)
    (hloc : ∀ i, ∃ ρ > 0, IsClosed ((φ i).Epi univ ∩ closedBall ((x₀, r i) : E × ℝ) ρ))
    (hqc : ∀ v : ι → StrongDual ℝ E, (∀ i, v i ∈ singularSubdiff (φ i) x₀) → ∑ i, v i = 0 →
      ∀ i, v i = 0) :
    singularSubdiff (fun x ↦ ∑ i, φ i x) x₀ ⊆ ∑ i, singularSubdiff (φ i) x₀ :=
  (subdiff_sum_subset_and Finset.univ (fun i _ ↦ hr i) (fun i _ ↦ hloc i)
    fun v hv hs i _ ↦ hqc v (fun i ↦ hv i (Finset.mem_univ i)) hs i).2

omit [NormedSpace ℝ F] in
/-- Cor. 2.21 of [Mordukhovich 2018], equality statement: if moreover all `φᵢ` are lower regular
at `x₀`, then (2.38) holds as an equality and `∑ᵢ φᵢ` is lower regular at `x₀`. -/
theorem subdiff_sum_eq [Fintype ι] (hr : ∀ i, φ i x₀ = r i)
    (hloc : ∀ i, ∃ ρ > 0, IsClosed ((φ i).Epi univ ∩ closedBall ((x₀, r i) : E × ℝ) ρ))
    (hqc : ∀ v : ι → StrongDual ℝ E, (∀ i, v i ∈ singularSubdiff (φ i) x₀) → ∑ i, v i = 0 →
      ∀ i, v i = 0) (hreg : ∀ i, LowerRegularAt (φ i) x₀) :
    subdiff (fun x ↦ ∑ i, φ i x) x₀ = ∑ i, subdiff (φ i) x₀ ∧
      LowerRegularAt (fun x ↦ ∑ i, φ i x) x₀ := by
  have h1 := subdiff_sum_subset hr hloc hqc
  have h2 : ∑ i, subdiff (φ i) x₀ ⊆ regularSubdiff (fun x ↦ ∑ i, φ i x) x₀ := by
    rw [Finset.sum_congr rfl fun i _ ↦ hreg i]
    exact sum_regularSubdiff_subset Finset.univ
  exact ⟨subset_antisymm h1 (h2.trans regularSubdiff_subset_subdiff),
    subset_antisymm (h1.trans h2) regularSubdiff_subset_subdiff⟩

end FiniteSum

end VariationalAnalysis
