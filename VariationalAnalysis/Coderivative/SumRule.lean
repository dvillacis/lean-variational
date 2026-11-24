/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis.Normal.Intersection
import VariationalAnalysis.Subdifferential.SumRule
import VariationalAnalysis.Normal.Diffeomorphism
import VariationalAnalysis.WellPosedness.Coderivative

/-!
# Coderivative sum rules

The general coderivative sum rules of [Mordukhovich 2018, Thm. 3.9] for `F₁, F₂ : E ⇉ F`,
`(F₁ + F₂)(x) = F₁ x + F₂ x` (pointwise sums of sets), in finite dimensions. With the
auxiliary mapping (3.21)

  `S(x, y) = {(y₁, y₂) | y₁ ∈ F₁ x, y₂ ∈ F₂ x, y = y₁ + y₂}`

and the qualification condition (3.22) `D*F₁(x̄, ȳ₁)(0) ∩ (-D*F₂(x̄, ȳ₂)(0)) = {0}`,

  `D*(F₁ + F₂)(x̄, ȳ)(y*) ⊆ D*F₁(x̄, ȳ₁)(y*) + D*F₂(x̄, ȳ₂)(y*)`  (3.23)

when `S` is inner semicontinuous at `(x̄, ȳ, ȳ₁, ȳ₂)`, and the union of the right-hand sides over
`(ȳ₁, ȳ₂) ∈ S(x̄, ȳ)` when `S` is locally bounded around `(x̄, ȳ)`.

As in the book, the proof applies the intersection rule (Thm. 2.16) to
`Ωᵢ = {(x, y₁, y₂) | (x, yᵢ) ∈ gph Fᵢ}` in `E × F × F`. We organize it in two steps, which are
reused by the chain rules (`Coderivative/ChainRule`):

* `Ω₁ ∩ Ω₂` is the graph of the pair mapping `x ↦ F₁ x × F₂ x`, whose coderivative is estimated
  by the intersection rule: this is (3.33) of [Mordukhovich 2018] (proof of Thm. 3.14);
* `gph(F₁ + F₂)` is the image of `Ω₁ ∩ Ω₂` under the linear map `(x, y₁, y₂) ↦ (x, y₁ + y₂)`,
  and limiting normals to the image pull back to the preimage when the points of the image can
  be lifted continuously (inner semicontinuity of `S`) or with bounded lifts (local boundedness
  of `S`).

The equality (3.24) for a `C¹` summand is `coderiv_add'` in `Coderivative/Smooth` (it needs no
qualification condition and is proved there by a change of variables).

The standing closed-graph assumption of the book appears as explicit hypotheses: local closedness
of the graphs around the relevant points for the inner semicontinuous case, closedness of the
graphs for the locally bounded case (the limit point is not known in advance there).

## Main results

* `comp_mem_regularNormalCone_of_mapsTo`, `comp_mem_normalCone_of_lift`,
  `exists_comp_mem_normalCone_of_bounded`: normals to `A '' Ω` pull back along the linear map `A`
  (inner semicontinuous and locally bounded lifts).
* `locallyClosed_preimage_clm`, `locallyClosed_graph_pairMap`, `comp_inl_mem_coderiv`: helpers.
* `normalCone_preimage_clm`, `exists_eq_add_of_mem_normalCone_preimage_inter`: the intersection
  rule (Thm. 2.16) for inverse images under surjective linear maps.
* `pairMap`, `coderiv_pairMap_subset`: (3.33) of [Mordukhovich 2018]:
  `D*F(x̄, ȳ)(y₁*, y₂*) ⊆ D*F₁(x̄, ȳ₁)(y₁*) + D*F₂(x̄, ȳ₂)(y₂*)` for `F(x) = F₁ x × F₂ x`.
* `sumAuxMap`: the auxiliary mapping (3.21).
* `coderiv_add_subset`: Thm. 3.9(i) of [Mordukhovich 2018], (3.23).
* `coderiv_add_subset_iUnion`: Thm. 3.9(ii) of [Mordukhovich 2018].
* `coderiv_add_subset_of_lipschitzLike`, `coderiv_add_subset_iUnion_of_lipschitzLike`:
  Cor. 3.10 of [Mordukhovich 2018].
-/

open Filter Topology Set Metric ContinuousLinearMap
open scoped Pointwise

namespace VariationalAnalysis

section Pullback

/-! ### Normals to linear images and to inverse images -/

variable {P Q : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q]
  [NormedSpace ℝ Q]

/-- [Mordukhovich 2018, proofs of Thms. 3.9(i) and 3.11(i)]: limiting normals pull back along a
continuous linear map `A` with `A '' Ω ⊆ Θ`, provided every sequence `qₖ → A p₀` in `Θ` lifts
to a sequence `pₖ → p₀` in `Ω` with `A pₖ = qₖ` (inner semicontinuity of the lifting). -/
theorem comp_mem_normalCone_of_lift (A : P →L[ℝ] Q) {Ω : Set P} {Θ : Set Q} (hΩ : MapsTo A Ω Θ)
    {p₀ : P} (hp₀ : p₀ ∈ Ω)
    (hlift : ∀ q : ℕ → Q, Tendsto q atTop (𝓝[Θ] (A p₀)) →
      ∃ p : ℕ → P, Tendsto p atTop (𝓝 p₀) ∧ ∀ᶠ k in atTop, p k ∈ Ω ∧ A (p k) = q k)
    {ℓ : StrongDual ℝ Q} (hℓ : ℓ ∈ normalCone Θ (A p₀)) : ℓ.comp A ∈ normalCone Ω p₀ := by
  obtain ⟨-, q, w, hq, hw, hmem⟩ := hℓ
  obtain ⟨p, hp, hev⟩ := hlift q hq
  refine ⟨hp₀, mem_outerLimit_of_eventually p (fun k ↦ (w k).comp A)
    (tendsto_nhdsWithin_iff.2 ⟨hp, hev.mono fun k hk ↦ hk.1⟩)
    (tendsto_dual_comp hw tendsto_const_nhds) (hev.mono fun k hk ↦ ?_)⟩
  have h := hmem k
  rw [← hk.2] at h
  exact comp_mem_regularNormalCone_of_mapsTo A hΩ hk.1 h

/-- [Mordukhovich 2018, proofs of Thms. 3.9(ii) and 3.11(ii)]: if `Ω` is closed, `Θ = A '' Ω`
and the points of `Ω` over a neighborhood of `q₀` form a bounded set, then every limiting normal
`ℓ` to `Θ` at `q₀` pulls back to a limiting normal `ℓ ∘ A` to `Ω` at some `p₀ ∈ Ω` with
`A p₀ = q₀`. -/
theorem exists_comp_mem_normalCone_of_bounded [FiniteDimensional ℝ P] (A : P →L[ℝ] Q)
    {Ω : Set P} {Θ : Set Q} (hΩ : MapsTo A Ω Θ) (hΘ : Θ ⊆ A '' Ω) (hcl : IsClosed Ω) {q₀ : Q}
    (hbd : ∃ U ∈ 𝓝 q₀, Bornology.IsBounded {p | p ∈ Ω ∧ A p ∈ U})
    {ℓ : StrongDual ℝ Q} (hℓ : ℓ ∈ normalCone Θ q₀) :
    ∃ p₀ ∈ Ω, A p₀ = q₀ ∧ ℓ.comp A ∈ normalCone Ω p₀ := by
  obtain ⟨-, q, w, hq, hw, hmem⟩ := hℓ
  have hq' := tendsto_nhdsWithin_iff.1 hq
  have hsplit : ∀ k, ∃ p : P, q k ∈ Θ → p ∈ Ω ∧ A p = q k := fun k ↦ by
    by_cases hk : q k ∈ Θ
    · obtain ⟨p, hp, hpq⟩ := hΘ hk
      exact ⟨p, fun _ ↦ ⟨hp, hpq⟩⟩
    · exact ⟨0, fun h ↦ absurd h hk⟩
  choose p hp using hsplit
  obtain ⟨U, hU, hbdd⟩ := hbd
  have hpB : ∀ᶠ k in atTop, p k ∈ {p | p ∈ Ω ∧ A p ∈ U} := by
    filter_upwards [hq'.2, hq'.1.eventually hU] with k hk hkU
    exact ⟨(hp k hk).1, (hp k hk).2 ▸ hkU⟩
  obtain ⟨p₀, -, φ, hφ, hlim⟩ := tendsto_subseq_of_frequently_bounded hbdd hpB.frequently
  have hφ' := hφ.tendsto_atTop
  have hev : ∀ᶠ k in atTop, p (φ k) ∈ Ω ∧ A (p (φ k)) = q (φ k) :=
    (hφ'.eventually hq'.2).mono fun k hk ↦ hp _ hk
  have hp₀ : p₀ ∈ Ω := hcl.mem_of_tendsto hlim (hev.mono fun k hk ↦ hk.1)
  have hAp₀ : A p₀ = q₀ := tendsto_nhds_unique ((A.continuous.tendsto p₀).comp hlim)
    ((hq'.1.comp hφ').congr' (hev.mono fun k hk ↦ hk.2.symm))
  refine ⟨p₀, hp₀, hAp₀, hp₀, mem_outerLimit_of_eventually (fun k ↦ p (φ k))
    (fun k ↦ (w (φ k)).comp A) (tendsto_nhdsWithin_iff.2 ⟨hlim, hev.mono fun k hk ↦ hk.1⟩)
    (tendsto_dual_comp (hw.comp hφ') tendsto_const_nhds) (hev.mono fun k hk ↦ ?_)⟩
  have h := hmem (φ k)
  rw [← hk.2] at h
  exact comp_mem_regularNormalCone_of_mapsTo A hΩ hk.1 h

/-- Inverse images of locally closed sets under continuous linear maps are locally closed. -/
theorem locallyClosed_preimage_clm (π : P →L[ℝ] Q) {C : Set Q} {p : P}
    (h : ∃ r > 0, IsClosed (C ∩ closedBall (π p) r)) :
    ∃ r > 0, IsClosed (π ⁻¹' C ∩ closedBall p r) := by
  obtain ⟨r, hr, hcl⟩ := h
  refine ⟨r / (‖π‖ + 1), by positivity, ?_⟩
  have heq : π ⁻¹' C ∩ closedBall p (r / (‖π‖ + 1)) =
      π ⁻¹' (C ∩ closedBall (π p) r) ∩ closedBall p (r / (‖π‖ + 1)) := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_closedBall]
    refine ⟨fun ⟨hx, hd⟩ ↦ ⟨⟨hx, ?_⟩, hd⟩, fun ⟨⟨hx, _⟩, hd⟩ ↦ ⟨hx, hd⟩⟩
    rw [dist_eq_norm, ← map_sub]
    rw [dist_eq_norm] at hd
    calc ‖π (x - p)‖ ≤ ‖π‖ * ‖x - p‖ := π.le_opNorm _
      _ ≤ (‖π‖ + 1) * (r / (‖π‖ + 1)) := by gcongr; linarith
      _ = r := by field_simp
  rw [heq]
  exact (hcl.preimage π.continuous).inter isClosed_closedBall

variable [FiniteDimensional ℝ P] [FiniteDimensional ℝ Q]

/-- Exercise 1.54 of [Mordukhovich 2018] for a surjective continuous linear map `π`:
`N(p; π⁻¹(C)) = π* N(π p; C)`. -/
theorem normalCone_preimage_clm {π : P →L[ℝ] Q} (hπ : Function.Surjective π) (C : Set Q)
    (p : P) : normalCone (π ⁻¹' C) p = (fun ℓ : StrongDual ℝ Q ↦ ℓ.comp π) '' normalCone C (π p) :=
  normalCone_preimage_of_surjective_of_finiteDimensional (D := fun _ ↦ π)
    (Eventually.of_forall fun _ ↦ π.hasStrictFDerivAt) continuousAt_const hπ

/-- The intersection rule (Thm. 2.16 of [Mordukhovich 2018]) for inverse images under surjective
continuous linear maps: if `C₁`, `C₂` are locally closed around `π₁ p₀`, `π₂ p₀` and the only
`ℓᵢ ∈ N(πᵢ p₀; Cᵢ)` with `ℓ₁ ∘ π₁ + ℓ₂ ∘ π₂ = 0` have `ℓ₁ = 0`, then every
`ℓ ∈ N(p₀; π₁⁻¹(C₁) ∩ π₂⁻¹(C₂))` is `ℓ₁ ∘ π₁ + ℓ₂ ∘ π₂` with `ℓᵢ ∈ N(πᵢ p₀; Cᵢ)`. -/
theorem exists_eq_add_of_mem_normalCone_preimage_inter {Q₂ : Type*} [NormedAddCommGroup Q₂]
    [NormedSpace ℝ Q₂] [FiniteDimensional ℝ Q₂] {π₁ : P →L[ℝ] Q} {π₂ : P →L[ℝ] Q₂}
    (hπ₁ : Function.Surjective π₁) (hπ₂ : Function.Surjective π₂) {C₁ : Set Q} {C₂ : Set Q₂}
    {p₀ : P} (hloc₁ : ∃ r > 0, IsClosed (C₁ ∩ closedBall (π₁ p₀) r))
    (hloc₂ : ∃ r > 0, IsClosed (C₂ ∩ closedBall (π₂ p₀) r))
    (hqc : ∀ ℓ₁ ∈ normalCone C₁ (π₁ p₀), ∀ ℓ₂ ∈ normalCone C₂ (π₂ p₀),
      ℓ₁.comp π₁ + ℓ₂.comp π₂ = 0 → ℓ₁ = 0)
    {ℓ : StrongDual ℝ P} (hℓ : ℓ ∈ normalCone (π₁ ⁻¹' C₁ ∩ π₂ ⁻¹' C₂) p₀) :
    ∃ ℓ₁ ∈ normalCone C₁ (π₁ p₀), ∃ ℓ₂ ∈ normalCone C₂ (π₂ p₀),
      ℓ = ℓ₁.comp π₁ + ℓ₂.comp π₂ := by
  have hqc' : ∀ v ∈ normalCone (π₁ ⁻¹' C₁) p₀, -v ∈ normalCone (π₂ ⁻¹' C₂) p₀ → v = 0 := by
    intro v hv hv'
    rw [normalCone_preimage_clm hπ₁] at hv
    rw [normalCone_preimage_clm hπ₂] at hv'
    obtain ⟨ℓ₁, h₁, rfl⟩ := hv
    obtain ⟨ℓ₂, h₂, h₂'⟩ := hv'
    have := hqc ℓ₁ h₁ ℓ₂ h₂ (by simp only at h₂'; rw [h₂', add_neg_cancel])
    simp [this]
  obtain ⟨v₁, hv₁, v₂, hv₂, hsum⟩ := normalCone_inter_subset (locallyClosed_preimage_clm π₁ hloc₁)
    (locallyClosed_preimage_clm π₂ hloc₂) hqc' hℓ
  rw [normalCone_preimage_clm hπ₁] at hv₁
  rw [normalCone_preimage_clm hπ₂] at hv₂
  obtain ⟨ℓ₁, h₁, rfl⟩ := hv₁
  obtain ⟨ℓ₂, h₂, rfl⟩ := hv₂
  exact ⟨ℓ₁, h₁, ℓ₂, h₂, hsum.symm⟩

end Pullback

section Graph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- A normal `ℓ` to `gph S` at `(x, y)` with `ℓ ∘ inr = -v` gives `ℓ ∘ inl ∈ D*S(x, y)(v)`. -/
theorem comp_inl_mem_coderiv {S : E → Set F} {x : E} {y : F} {ℓ : StrongDual ℝ (E × F)}
    {v : StrongDual ℝ F} (hℓ : ℓ ∈ normalCone (graph S) (x, y))
    (hv : ℓ.comp (inr ℝ E F) = -v) : ℓ.comp (inl ℝ E F) ∈ coderiv S x y v := by
  change _ ∈ normalCone _ _
  rwa [← hv, coprod_comp_inl_inr]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- A mapping whose graph is closed is locally closed around every point of its graph. -/
theorem locallyClosed_of_isClosed {Ω : Set E} (h : IsClosed Ω) (x : E) :
    ∃ r > 0, IsClosed (Ω ∩ closedBall x r) :=
  ⟨1, one_pos, h.inter isClosed_closedBall⟩

end Graph

section PairMap

/-! ### The pair mapping `x ↦ F₁ x × F₂ x`, (3.33) -/

variable {E Y₁ Y₂ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y₁]
  [NormedSpace ℝ Y₁] [NormedAddCommGroup Y₂] [NormedSpace ℝ Y₂]

/-- The pair mapping `F(x) = F₁ x × F₂ x` of [Mordukhovich 2018, proof of Thm. 3.14]. -/
def pairMap (F₁ : E → Set Y₁) (F₂ : E → Set Y₂) : E → Set (Y₁ × Y₂) := fun x ↦ F₁ x ×ˢ F₂ x

/-- The projection `(x, y₁, y₂) ↦ (x, y₁)`. -/
noncomputable abbrev pairProj₁ : E × (Y₁ × Y₂) →L[ℝ] E × Y₁ :=
  (fst ℝ E (Y₁ × Y₂)).prod ((fst ℝ Y₁ Y₂).comp (snd ℝ E (Y₁ × Y₂)))

/-- The projection `(x, y₁, y₂) ↦ (x, y₂)`. -/
noncomputable abbrev pairProj₂ : E × (Y₁ × Y₂) →L[ℝ] E × Y₂ :=
  (fst ℝ E (Y₁ × Y₂)).prod ((snd ℝ Y₁ Y₂).comp (snd ℝ E (Y₁ × Y₂)))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y₁] [NormedSpace ℝ Y₁]
  [NormedAddCommGroup Y₂] [NormedSpace ℝ Y₂] in
/-- `(y₁, y₂) ∈ F₁ x × F₂ x` iff `y₁ ∈ F₁ x` and `y₂ ∈ F₂ x`. -/
theorem mem_pairMap_iff {F₁ : E → Set Y₁} {F₂ : E → Set Y₂} {x : E} {y : Y₁ × Y₂} :
    y ∈ pairMap F₁ F₂ x ↔ y.1 ∈ F₁ x ∧ y.2 ∈ F₂ x := Iff.rfl

/-- `gph F = Ω₁ ∩ Ω₂` with `Ωᵢ = {(x, y₁, y₂) | (x, yᵢ) ∈ gph Fᵢ}` [Mordukhovich 2018, proof of
Thm. 3.9]. -/
theorem graph_pairMap (F₁ : E → Set Y₁) (F₂ : E → Set Y₂) :
    graph (pairMap F₁ F₂) = pairProj₁ ⁻¹' graph F₁ ∩ pairProj₂ ⁻¹' graph F₂ := rfl

/-- The projection `(x, y₁, y₂) ↦ (x, y₁)` is surjective. -/
theorem pairProj₁_surjective : Function.Surjective (pairProj₁ : E × (Y₁ × Y₂) →L[ℝ] E × Y₁) :=
  fun q ↦ ⟨(q.1, (q.2, 0)), rfl⟩

/-- The projection `(x, y₁, y₂) ↦ (x, y₂)` is surjective. -/
theorem pairProj₂_surjective : Function.Surjective (pairProj₂ : E × (Y₁ × Y₂) →L[ℝ] E × Y₂) :=
  fun q ↦ ⟨(q.1, (0, q.2)), rfl⟩

/-- The graph of the pair mapping is locally closed when those of `F₁`, `F₂` are. -/
theorem locallyClosed_graph_pairMap {F₁ : E → Set Y₁} {F₂ : E → Set Y₂} {x₀ : E} {y₁ : Y₁}
    {y₂ : Y₂} (hloc₁ : ∃ r > 0, IsClosed (graph F₁ ∩ closedBall (x₀, y₁) r))
    (hloc₂ : ∃ r > 0, IsClosed (graph F₂ ∩ closedBall (x₀, y₂) r)) :
    ∃ r > 0, IsClosed (graph (pairMap F₁ F₂) ∩ closedBall (x₀, (y₁, y₂)) r) := by
  have h₁ : ∃ r > 0, IsClosed (pairProj₁ ⁻¹' graph F₁ ∩ closedBall (x₀, (y₁, y₂)) r) :=
    locallyClosed_preimage_clm (pairProj₁ (Y₂ := Y₂)) (C := graph F₁) (p := (x₀, (y₁, y₂))) hloc₁
  have e₂ : (pairProj₂ : E × (Y₁ × Y₂) →L[ℝ] E × Y₂) (x₀, (y₁, y₂)) = (x₀, y₂) := rfl
  rw [← e₂] at hloc₂
  have h₂ : ∃ r > 0, IsClosed (pairProj₂ ⁻¹' graph F₂ ∩ closedBall (x₀, (y₁, y₂)) r) :=
    locallyClosed_preimage_clm _ hloc₂
  rw [graph_pairMap]
  exact locallyClosed_inter h₁ h₂

/-- The graph of the pair mapping is closed when those of `F₁`, `F₂` are. -/
theorem isClosed_graph_pairMap {F₁ : E → Set Y₁} {F₂ : E → Set Y₂} (h₁ : IsClosed (graph F₁))
    (h₂ : IsClosed (graph F₂)) : IsClosed (graph (pairMap F₁ F₂)) := by
  rw [graph_pairMap]
  exact (h₁.preimage pairProj₁.continuous).inter (h₂.preimage pairProj₂.continuous)

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ Y₁] [FiniteDimensional ℝ Y₂]

/-- (3.33) of [Mordukhovich 2018] (proof of Thm. 3.14), coderivatives of the pair mapping
`F(x) = F₁ x × F₂ x`: if the graphs of `F₁`, `F₂` are locally closed around `(x̄, ȳ₁)`,
`(x̄, ȳ₂)` and the qualification condition (3.22)
`D*F₁(x̄, ȳ₁)(0) ∩ (-D*F₂(x̄, ȳ₂)(0)) = {0}` holds, then for every `w = (y₁*, y₂*)`

  `D*F(x̄, (ȳ₁, ȳ₂))(y₁*, y₂*) ⊆ D*F₁(x̄, ȳ₁)(y₁*) + D*F₂(x̄, ȳ₂)(y₂*)`,

where `y₁* = w ∘ inl`, `y₂* = w ∘ inr`. The book obtains it from Thm. 3.9 applied to
`(F₁ × {0}) + ({0} × F₂)`; the qualification condition is the one of that application. It
follows here directly from the intersection rule, `gph F` being `Ω₁ ∩ Ω₂`. -/
theorem coderiv_pairMap_subset {F₁ : E → Set Y₁} {F₂ : E → Set Y₂} {x₀ : E} {y₁ : Y₁}
    {y₂ : Y₂} (hloc₁ : ∃ r > 0, IsClosed (graph F₁ ∩ closedBall (x₀, y₁) r))
    (hloc₂ : ∃ r > 0, IsClosed (graph F₂ ∩ closedBall (x₀, y₂) r))
    (hqc : ∀ u ∈ coderiv F₁ x₀ y₁ 0, -u ∈ coderiv F₂ x₀ y₂ 0 → u = 0)
    (w : StrongDual ℝ (Y₁ × Y₂)) :
    coderiv (pairMap F₁ F₂) x₀ (y₁, y₂) w ⊆
      coderiv F₁ x₀ y₁ (w.comp (inl ℝ Y₁ Y₂)) + coderiv F₂ x₀ y₂ (w.comp (inr ℝ Y₁ Y₂)) := by
  intro u hu
  have hu' : u.coprod (-w) ∈ normalCone (pairProj₁ ⁻¹' graph F₁ ∩ pairProj₂ ⁻¹' graph F₂)
      (x₀, (y₁, y₂)) := hu
  -- evaluation of `ℓ₁ ∘ π₁ + ℓ₂ ∘ π₂` at the points `(x, 0, 0)`, `(0, y, 0)`, `(0, 0, y)`
  have heval : ∀ (ℓ₁ : StrongDual ℝ (E × Y₁)) (ℓ₂ : StrongDual ℝ (E × Y₂)) (x : E) (a : Y₁)
      (b : Y₂), (ℓ₁.comp pairProj₁ + ℓ₂.comp pairProj₂ : StrongDual ℝ (E × (Y₁ × Y₂))) (x, (a, b)) =
        ℓ₁ (x, a) + ℓ₂ (x, b) :=
    fun _ _ _ _ _ ↦ rfl
  obtain ⟨ℓ₁, h₁, ℓ₂, h₂, heq⟩ := exists_eq_add_of_mem_normalCone_preimage_inter
    (pairProj₁_surjective (Y₂ := Y₂)) (pairProj₂_surjective (Y₁ := Y₁)) hloc₁ hloc₂
    (fun ℓ₁ h₁ ℓ₂ h₂ h0 ↦ by
      have e1 : ∀ x, ℓ₁ (x, 0) + ℓ₂ (x, 0) = 0 := fun x ↦ by
        simpa [heval, Prod.mk_zero_zero, map_zero] using
      DFunLike.congr_fun h0 (x, ((0 : Y₁), (0 : Y₂)))
      have e2 : ∀ a : Y₁, ℓ₁ (0, a) = 0 := fun a ↦ by
        simpa [heval, Prod.mk_zero_zero, map_zero] using
      DFunLike.congr_fun h0 ((0 : E), (a, (0 : Y₂)))
      have e3 : ∀ b : Y₂, ℓ₂ (0, b) = 0 := fun b ↦ by
        simpa [heval, Prod.mk_zero_zero, map_zero] using
      DFunLike.congr_fun h0 ((0 : E), ((0 : Y₁), b))
      have m1 : ℓ₁.comp (inl ℝ E Y₁) ∈ coderiv F₁ x₀ y₁ 0 :=
        comp_inl_mem_coderiv h₁ (by ext a; simp [e2])
      have m2 : -ℓ₁.comp (inl ℝ E Y₁) ∈ coderiv F₂ x₀ y₂ 0 := by
        have : -ℓ₁.comp (inl ℝ E Y₁) = ℓ₂.comp (inl ℝ E Y₂) := by
          ext x; simp [eq_neg_of_add_eq_zero_right (e1 x)]
        rw [this]
        exact comp_inl_mem_coderiv h₂ (by ext b; simp [e3])
      have h0' := hqc _ m1 m2
      rw [← coprod_comp_inl_inr ℓ₁, h0']
      ext <;> simp [e2]) hu'
  have e1 : ∀ x, u x = ℓ₁ (x, 0) + ℓ₂ (x, 0) := fun x ↦ by
    simpa [heval, Prod.mk_zero_zero, map_zero] using
      DFunLike.congr_fun heq (x, ((0 : Y₁), (0 : Y₂)))
  have e2 : ∀ a : Y₁, -w (a, 0) = ℓ₁ (0, a) := fun a ↦ by
    simpa [heval, Prod.mk_zero_zero, map_zero] using
      DFunLike.congr_fun heq ((0 : E), (a, (0 : Y₂)))
  have e3 : ∀ b : Y₂, -w (0, b) = ℓ₂ (0, b) := fun b ↦ by
    simpa [heval, Prod.mk_zero_zero, map_zero] using
      DFunLike.congr_fun heq ((0 : E), ((0 : Y₁), b))
  refine ⟨ℓ₁.comp (inl ℝ E Y₁), comp_inl_mem_coderiv h₁ (by ext a; simp [← e2]),
    ℓ₂.comp (inl ℝ E Y₂), comp_inl_mem_coderiv h₂ (by ext b; simp [← e3]), ?_⟩
  ext x
  simp [e1]

end PairMap

section SumRule

/-! ### Sum rules, Thm. 3.9 -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The auxiliary mapping (3.21) of [Mordukhovich 2018]:
`S(x, y) = {(y₁, y₂) | y₁ ∈ F₁ x, y₂ ∈ F₂ x, y = y₁ + y₂}`. -/
def sumAuxMap (F₁ F₂ : E → Set F) : E × F → Set (F × F) :=
  fun q ↦ {s | s.1 ∈ F₁ q.1 ∧ s.2 ∈ F₂ q.1 ∧ q.2 = s.1 + s.2}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- `dom S = gph(F₁ + F₂)` for the mapping (3.21). -/
theorem dom_sumAuxMap (F₁ F₂ : E → Set F) :
    dom (sumAuxMap F₁ F₂) = graph fun x ↦ F₁ x + F₂ x := by
  ext ⟨x, y⟩
  simp only [dom, sumAuxMap, graph, mem_ofPred_eq, Set.mem_add]
  constructor
  · rintro ⟨⟨a, b⟩, ha, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨(a, b), ha, hb, rfl⟩

/-- The linear map `(x, y₁, y₂) ↦ (x, y₁ + y₂)`, which maps `gph(F₁ × F₂)` onto
`gph(F₁ + F₂)`. -/
noncomputable abbrev sumProj : E × (F × F) →L[ℝ] E × F :=
  (fst ℝ E (F × F)).prod ((fst ℝ F F + snd ℝ F F).comp (snd ℝ E (F × F)))

/-- The map `(x, y₁, y₂) ↦ (x, y₁ + y₂)` maps `gph(F₁ × F₂)` into `gph(F₁ + F₂)`. -/
theorem mapsTo_sumProj (F₁ F₂ : E → Set F) :
    MapsTo sumProj (graph (pairMap F₁ F₂)) (graph fun x ↦ F₁ x + F₂ x) :=
  fun _ hp ↦ Set.add_mem_add hp.1 hp.2

/-- The pullback of `(u, -y*)` along `(x, y₁, y₂) ↦ (x, y₁ + y₂)` is `(u, -(y*, y*))`. -/
theorem coprod_comp_sumProj (u : StrongDual ℝ E) (y' : StrongDual ℝ F) :
    (u.coprod (-y')).comp sumProj = u.coprod (-y'.comp (fst ℝ F F + snd ℝ F F)) := by
  ext <;> simp

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- Thm. 3.9(i) of [Mordukhovich 2018] (general sum rule, inner semicontinuous case), (3.23):
let `(ȳ₁, ȳ₂) ∈ S(x̄, ȳ)` for the mapping `S` of (3.21), let `S` be inner semicontinuous at
`(x̄, ȳ, ȳ₁, ȳ₂)`, let the graphs of `F₁`, `F₂` be locally closed around `(x̄, ȳ₁)`, `(x̄, ȳ₂)`,
and let the qualification condition (3.22) `D*F₁(x̄, ȳ₁)(0) ∩ (-D*F₂(x̄, ȳ₂)(0)) = {0}` hold.
Then `D*(F₁ + F₂)(x̄, ȳ)(y*) ⊆ D*F₁(x̄, ȳ₁)(y*) + D*F₂(x̄, ȳ₂)(y*)`. For a `C¹` summand this is
the equality (3.24), `coderiv_add'`, with no qualification condition. -/
theorem coderiv_add_subset {F₁ F₂ : E → Set F} {x₀ : E} {y₀ y₁ y₂ : F}
    (hy : (y₁, y₂) ∈ sumAuxMap F₁ F₂ (x₀, y₀))
    (hS : InnerSemicontinuousAt (sumAuxMap F₁ F₂) (x₀, y₀) (y₁, y₂))
    (hloc₁ : ∃ r > 0, IsClosed (graph F₁ ∩ closedBall (x₀, y₁) r))
    (hloc₂ : ∃ r > 0, IsClosed (graph F₂ ∩ closedBall (x₀, y₂) r))
    (hqc : ∀ u ∈ coderiv F₁ x₀ y₁ 0, -u ∈ coderiv F₂ x₀ y₂ 0 → u = 0) (y' : StrongDual ℝ F) :
    coderiv (fun x ↦ F₁ x + F₂ x) x₀ y₀ y' ⊆ coderiv F₁ x₀ y₁ y' + coderiv F₂ x₀ y₂ y' := by
  obtain ⟨hy₁, hy₂, rfl⟩ := hy
  intro u hu
  have hA : sumProj (x₀, (y₁, y₂)) = (x₀, y₁ + y₂) := rfl
  have hpull := comp_mem_normalCone_of_lift sumProj (mapsTo_sumProj F₁ F₂)
    (p₀ := (x₀, (y₁, y₂))) (show (x₀, (y₁, y₂)) ∈ graph (pairMap F₁ F₂) from ⟨hy₁, hy₂⟩)
    (fun q hq ↦ by
      rw [hA, ← dom_sumAuxMap] at hq
      obtain ⟨v, hv, hvS⟩ := hS q hq
      refine ⟨fun k ↦ ((q k).1, v k),
        ((continuous_fst.tendsto _).comp (tendsto_nhdsWithin_iff.1 hq).1).prodMk_nhds hv,
        hvS.mono fun k hk ↦ ⟨⟨hk.1, hk.2.1⟩, ?_⟩⟩
      exact Prod.ext rfl hk.2.2.symm) (ℓ := u.coprod (-y')) (by rw [hA]; exact hu)
  rw [coprod_comp_sumProj] at hpull
  have h := coderiv_pairMap_subset hloc₁ hloc₂ hqc _ hpull
  have e1 : (y'.comp (fst ℝ F F + snd ℝ F F)).comp (inl ℝ F F) = y' := by ext; simp
  have e2 : (y'.comp (fst ℝ F F + snd ℝ F F)).comp (inr ℝ F F) = y' := by ext; simp
  rwa [e1, e2] at h

/-- Thm. 3.9(ii) of [Mordukhovich 2018] (general sum rule, locally bounded case): let the graphs
of `F₁`, `F₂` be closed, let the mapping `S` of (3.21) be locally bounded around `(x̄, ȳ)`, and
let the qualification condition (3.22) hold for every `(ȳ₁, ȳ₂) ∈ S(x̄, ȳ)`. Then
`D*(F₁ + F₂)(x̄, ȳ)(y*) ⊆ ⋃_{(ȳ₁, ȳ₂) ∈ S(x̄, ȳ)} [D*F₁(x̄, ȳ₁)(y*) + D*F₂(x̄, ȳ₂)(y*)]`. -/
theorem coderiv_add_subset_iUnion {F₁ F₂ : E → Set F} {x₀ : E} {y₀ : F}
    (h₁ : IsClosed (graph F₁)) (h₂ : IsClosed (graph F₂))
    (hS : LocallyBoundedAt (sumAuxMap F₁ F₂) (x₀, y₀))
    (hqc : ∀ s ∈ sumAuxMap F₁ F₂ (x₀, y₀),
      ∀ u ∈ coderiv F₁ x₀ s.1 0, -u ∈ coderiv F₂ x₀ s.2 0 → u = 0) (y' : StrongDual ℝ F) :
    coderiv (fun x ↦ F₁ x + F₂ x) x₀ y₀ y' ⊆
      ⋃ s ∈ sumAuxMap F₁ F₂ (x₀, y₀), coderiv F₁ x₀ s.1 y' + coderiv F₂ x₀ s.2 y' := by
  intro u hu
  obtain ⟨U, hU, hbdd⟩ := hS
  have hA : ∀ p : E × (F × F), sumProj p = (p.1, p.2.1 + p.2.2) := fun _ ↦ rfl
  have hbd : ∃ V ∈ 𝓝 (x₀, y₀), Bornology.IsBounded
      {p | p ∈ graph (pairMap F₁ F₂) ∧ sumProj p ∈ V} := by
    refine ⟨U ∩ ball (x₀, y₀) 1, inter_mem hU (ball_mem_nhds _ one_pos),
      ((isBounded_ball (x := x₀) (r := 1)).prod hbdd).subset ?_⟩
    rintro ⟨x, s⟩ ⟨hp, hV, hball⟩
    rw [hA] at hV hball
    refine ⟨?_, mem_biUnion hV ⟨hp.1, hp.2, rfl⟩⟩
    rw [mem_ball, Prod.dist_eq] at hball
    exact mem_ball.2 ((le_max_left _ _).trans_lt hball)
  obtain ⟨⟨x, a, b⟩, hp, hAp, hpull⟩ := exists_comp_mem_normalCone_of_bounded
    (P := E × (F × F)) (Q := E × F) sumProj
    (mapsTo_sumProj F₁ F₂) (fun q hq ↦ by
      obtain ⟨a, ha, b, hb, hq2⟩ := Set.mem_add.1 (show q.2 ∈ F₁ q.1 + F₂ q.1 from hq)
      exact ⟨(q.1, (a, b)), ⟨ha, hb⟩, by rw [hA]; exact Prod.ext rfl hq2⟩)
    (isClosed_graph_pairMap h₁ h₂) hbd (ℓ := u.coprod (-y'))
    (show u.coprod (-y') ∈ normalCone (graph fun x ↦ F₁ x + F₂ x) (x₀, y₀) from hu)
  rw [hA] at hAp
  have hx : x = x₀ := congrArg Prod.fst hAp
  have hs : y₀ = a + b := (congrArg Prod.snd hAp).symm
  subst hx
  have hsS : (a, b) ∈ sumAuxMap F₁ F₂ (x, y₀) := ⟨hp.1, hp.2, hs⟩
  rw [coprod_comp_sumProj] at hpull
  have h := coderiv_pairMap_subset (F₁ := F₁) (F₂ := F₂) (x₀ := x) (y₁ := a) (y₂ := b)
    (locallyClosed_of_isClosed h₁ (x, a)) (locallyClosed_of_isClosed h₂ (x, b))
    (hqc (a, b) hsS) _ hpull
  have e1 : (y'.comp (fst ℝ F F + snd ℝ F F)).comp (inl ℝ F F) = y' := by ext; simp
  have e2 : (y'.comp (fst ℝ F F + snd ℝ F F)).comp (inr ℝ F F) = y' := by ext; simp
  rw [e1, e2] at h
  exact mem_biUnion hsS h

/-- Cor. 3.10 of [Mordukhovich 2018] (coderivative sum rule for Lipschitz-like multifunctions),
inner semicontinuous case: in the setting of Thm. 3.9(i), if `F₁` is Lipschitz-like around
`(x̄, ȳ₁)` or `F₂` is Lipschitz-like around `(x̄, ȳ₂)`, then the qualification condition (3.22)
holds (Thm. 3.3(iii), `LipschitzLikeAt.coderiv_zero`) and so does the sum rule (3.23). -/
theorem coderiv_add_subset_of_lipschitzLike {F₁ F₂ : E → Set F} {x₀ : E} {y₀ y₁ y₂ : F}
    (hy : (y₁, y₂) ∈ sumAuxMap F₁ F₂ (x₀, y₀))
    (hS : InnerSemicontinuousAt (sumAuxMap F₁ F₂) (x₀, y₀) (y₁, y₂))
    (hloc₁ : ∃ r > 0, IsClosed (graph F₁ ∩ closedBall (x₀, y₁) r))
    (hloc₂ : ∃ r > 0, IsClosed (graph F₂ ∩ closedBall (x₀, y₂) r))
    (hlip : LipschitzLikeAt F₁ x₀ y₁ ∨ LipschitzLikeAt F₂ x₀ y₂) (y' : StrongDual ℝ F) :
    coderiv (fun x ↦ F₁ x + F₂ x) x₀ y₀ y' ⊆ coderiv F₁ x₀ y₁ y' + coderiv F₂ x₀ y₂ y' := by
  refine coderiv_add_subset hy hS hloc₁ hloc₂ (fun u hu hu' ↦ ?_) y'
  rcases hlip with h | h
  · rwa [h.coderiv_zero hy.1] at hu
  · rw [h.coderiv_zero hy.2.1] at hu'
    exact neg_eq_zero.1 hu'

/-- Cor. 3.10 of [Mordukhovich 2018], locally bounded case: in the setting of Thm. 3.9(ii), if
for every `(ȳ₁, ȳ₂) ∈ S(x̄, ȳ)` one of the mappings `Fᵢ` is Lipschitz-like around `(x̄, ȳᵢ)`,
then the sum rule of Thm. 3.9(ii) holds. -/
theorem coderiv_add_subset_iUnion_of_lipschitzLike {F₁ F₂ : E → Set F} {x₀ : E} {y₀ : F}
    (h₁ : IsClosed (graph F₁)) (h₂ : IsClosed (graph F₂))
    (hS : LocallyBoundedAt (sumAuxMap F₁ F₂) (x₀, y₀))
    (hlip : ∀ s ∈ sumAuxMap F₁ F₂ (x₀, y₀),
      LipschitzLikeAt F₁ x₀ s.1 ∨ LipschitzLikeAt F₂ x₀ s.2) (y' : StrongDual ℝ F) :
    coderiv (fun x ↦ F₁ x + F₂ x) x₀ y₀ y' ⊆
      ⋃ s ∈ sumAuxMap F₁ F₂ (x₀, y₀), coderiv F₁ x₀ s.1 y' + coderiv F₂ x₀ s.2 y' := by
  refine coderiv_add_subset_iUnion h₁ h₂ hS (fun s hs u hu hu' ↦ ?_) y'
  rcases hlip s hs with h | h
  · rwa [h.coderiv_zero hs.1] at hu
  · rw [h.coderiv_zero hs.2.1] at hu'
    exact neg_eq_zero.1 hu'

end SumRule

end VariationalAnalysis
