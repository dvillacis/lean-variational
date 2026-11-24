/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Analysis.Normed.Operator.Prod
import VariationalAnalysis.Coderivative.Basic
import VariationalAnalysis.Normal.Diffeomorphism

/-!
# Coderivative calculus with smooth mappings

Coderivative sum and chain rules in which one of the mappings is single-valued and `C¹`
(strict derivative `D x` at every `x` near `x₀`, `D` continuous at `x₀`). They hold as
equalities, with no qualification condition, because the relevant graph is the inverse image of
another graph under a `C¹` mapping with surjective derivative (`Normal/Diffeomorphism`).

The book derives (3.24) from the general sum rule (3.23), which rests on the intersection rule
of Ch. 2; here it follows directly from the graph change `(x, y) ↦ (x, y - F₁ x)`, a `C¹`
diffeomorphism. The chain rule (3.28) with a full-rank inner derivative is proved as in the book.

## Main results

* `mem_coderiv_add_iff`, `coderiv_add`, `coderiv_add'`: (3.24) of [Mordukhovich 2018,
  Thm. 3.9(i)]: `D*(F₁ + F₂)(x₀, y₀)(y*) = ∇F₁(x₀)* y* + D*F₂(x₀, y₀ - F₁ x₀)(y*)` for `F₁` of
  class `C¹` and any set-valued `F₂`.
* `mem_coderiv_neg_iff`: `D*(-F)(x₀, -y₀)(y*) = D*F(x₀, y₀)(-y*)`.
* `mem_coderiv_comp_iff`, `coderiv_comp`: chain rule (3.28) with a `C¹` inner mapping whose
  derivative is invertible (complete spaces).
* `coderiv_comp_of_surjective`, `comp_mem_coderiv_comp_iff_of_surjective`: Thm. 3.11(iii) of
  [Mordukhovich 2018], full-rank case: `D*(F ∘ g)(x₀, z₀)(z*) = ∇g(x₀)* D*F(g x₀, z₀)(z*)` for
  `g` of class `C¹` with surjective derivative (finite dimensions); graph change
  `graph_comp_eq_preimage`. For the regular coderivative (Exercise 1.61 of
  [Mordukhovich 2018]), strict differentiability at `x₀` suffices:
  `regularCoderiv_comp_of_surjective`.
-/

open Filter Topology Set

namespace VariationalAnalysis
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

open ContinuousLinearMap in
/-- (3.24) of [Mordukhovich 2018, Thm. 3.9(i)] (coderivative sum rule with a `C¹` summand),
pointwise form: `m ∈ D*(F₁ + F₂)(x̄, F₁ x̄ + ȳ)(y*)` iff `m - y* ∘ ∇F₁(x̄) ∈ D*F₂(x̄, ȳ)(y*)`,
for `F₁` of class `C¹` around `x̄` and any set-valued `F₂`. -/
theorem mem_coderiv_add_iff {F₁ : E → F} {D : E → E →L[ℝ] F} {F₂ : E → Set F} {x₀ : E}
    {y₀ : F} (hF : ∀ᶠ x in 𝓝 x₀, HasStrictFDerivAt F₁ (D x) x) (hDc : ContinuousAt D x₀)
    {y' : StrongDual ℝ F} {m : StrongDual ℝ E} :
    m ∈ coderiv (fun x ↦ (fun y ↦ F₁ x + y) '' F₂ x) x₀ (F₁ x₀ + y₀) y' ↔
      m - y'.comp (D x₀) ∈ coderiv F₂ x₀ y₀ y' := by
  set Θ : E × F → E × F := fun w ↦ (w.1, w.2 - F₁ w.1)
  set DΘ : E × F → E × F →L[ℝ] E × F := fun w ↦
    ContinuousLinearMap.id ℝ (E × F) - (inr ℝ E F).comp ((D w.1).comp (fst ℝ E F))
  have hgraph : graph (fun x ↦ (fun y ↦ F₁ x + y) '' F₂ x) = Θ ⁻¹' graph F₂ := by
    ext ⟨x, y⟩
    simp only [graph, mem_ofPred_eq, mem_image, mem_preimage, Θ]
    constructor
    · rintro ⟨y₂, hy₂, rfl⟩; simpa using hy₂
    · intro h; exact ⟨y - F₁ x, h, by abel⟩
  have hΘ : ∀ᶠ w in 𝓝 (x₀, F₁ x₀ + y₀), HasStrictFDerivAt Θ (DΘ w) w := by
    have hF' : ∀ᶠ w in 𝓝 (x₀, F₁ x₀ + y₀), HasStrictFDerivAt F₁ (D w.1) w.1 :=
      (continuous_fst.tendsto (x₀, F₁ x₀ + y₀)).eventually hF
    filter_upwards [hF'] with w hw
    have h1 : HasStrictFDerivAt (fun w : E × F ↦ w) (ContinuousLinearMap.id ℝ (E × F)) w :=
      hasStrictFDerivAt_id w
    have h2 : HasStrictFDerivAt (fun w : E × F ↦ ((0 : E), F₁ w.1))
        ((inr ℝ E F).comp ((D w.1).comp (fst ℝ E F))) w :=
      (inr ℝ E F).hasStrictFDerivAt.comp w (hw.comp w (hasStrictFDerivAt_fst))
    have hΘeq : Θ = fun w : E × F ↦ w - ((0 : E), F₁ w.1) := by
      funext w; ext <;> simp [Θ]
    rw [hΘeq]
    exact h1.sub h2
  have hDΘc : ContinuousAt DΘ (x₀, F₁ x₀ + y₀) :=
    continuousAt_const.sub (continuousAt_const.clm_comp
      ((hDc.comp continuousAt_fst).clm_comp continuousAt_const))
  set e : (E × F) ≃L[ℝ] (E × F) := ContinuousLinearEquiv.equivOfInverse (DΘ (x₀, F₁ x₀ + y₀))
    (ContinuousLinearMap.id ℝ (E × F) + (inr ℝ E F).comp ((D x₀).comp (fst ℝ E F)))
    (fun w ↦ by ext <;> simp [DΘ]) (fun w ↦ by ext <;> simp [DΘ])
  have he : DΘ (x₀, F₁ x₀ + y₀) = e := by ext <;> simp [e]
  have hΘx : Θ (x₀, F₁ x₀ + y₀) = (x₀, y₀) := by simp [Θ]
  simp only [coderiv, mem_ofPred_eq, hgraph]
  rw [mem_normalCone_preimage_iff hΘ hDΘc he, hΘx]
  have : (m.coprod (-y')).comp (e.symm : E × F →L[ℝ] E × F) =
      (m - y'.comp (D x₀)).coprod (-y') := by
    ext <;> simp [e, DΘ, sub_eq_add_neg]
  rw [this]

/-- (3.24) of [Mordukhovich 2018, Thm. 3.9(i)] (coderivative sum rule with a `C¹` summand):
`D*(F₁ + F₂)(x̄, F₁ x̄ + ȳ)(y*) = y* ∘ ∇F₁(x̄) + D*F₂(x̄, ȳ)(y*)`. -/
theorem coderiv_add {F₁ : E → F} {D : E → E →L[ℝ] F} {F₂ : E → Set F} {x₀ : E} {y₀ : F}
    (hF : ∀ᶠ x in 𝓝 x₀, HasStrictFDerivAt F₁ (D x) x) (hDc : ContinuousAt D x₀)
    (y' : StrongDual ℝ F) :
    coderiv (fun x ↦ (fun y ↦ F₁ x + y) '' F₂ x) x₀ (F₁ x₀ + y₀) y' =
      (fun u ↦ y'.comp (D x₀) + u) '' coderiv F₂ x₀ y₀ y' := by
  ext m
  rw [mem_coderiv_add_iff hF hDc]
  constructor
  · intro h; exact ⟨_, h, by abel_nf⟩
  · rintro ⟨u, hu, rfl⟩; simpa using hu

omit [CompleteSpace F] in
open ContinuousLinearMap in
/-- (3.28) of [Mordukhovich 2018, Thm. 3.11(iii)] for an invertible inner derivative
(coderivative chain rule with a `C¹` inner map with `∇F₁(x̄) = e` invertible), in complete
spaces: `m ∈ D*(F₃ ∘ F₁)(x̄, z̄)(z*)` iff `m ∘ e⁻¹ ∈ D*F₃(F₁ x̄, z̄)(z*)`. The full-rank case in
finite dimensions is `coderiv_comp_of_surjective`. -/
theorem mem_coderiv_comp_iff {F₁ : E → F} {D : E → E →L[ℝ] F} {e : E ≃L[ℝ] F}
    {F₃ : F → Set G} {x₀ : E} {z₀ : G} (hF : ∀ᶠ x in 𝓝 x₀, HasStrictFDerivAt F₁ (D x) x)
    (hDc : ContinuousAt D x₀) (he : D x₀ = e) {z' : StrongDual ℝ G} {m : StrongDual ℝ E} :
    m ∈ coderiv (fun x ↦ F₃ (F₁ x)) x₀ z₀ z' ↔
      m.comp (e.symm : F →L[ℝ] E) ∈ coderiv F₃ (F₁ x₀) z₀ z' := by
  set Θ : E × G → F × G := fun w ↦ (F₁ w.1, w.2)
  set DΘ : E × G → E × G →L[ℝ] F × G := fun w ↦
    (inl ℝ F G).comp ((D w.1).comp (fst ℝ E G)) + (inr ℝ F G).comp (snd ℝ E G)
  have hgraph : graph (fun x ↦ F₃ (F₁ x)) = Θ ⁻¹' graph F₃ := rfl
  have hΘ : ∀ᶠ w in 𝓝 (x₀, z₀), HasStrictFDerivAt Θ (DΘ w) w := by
    have hF' : ∀ᶠ w in 𝓝 (x₀, z₀), HasStrictFDerivAt F₁ (D w.1) w.1 :=
      (continuous_fst.tendsto (x₀, z₀)).eventually hF
    filter_upwards [hF'] with w hw
    have := (hw.comp w hasStrictFDerivAt_fst).prodMk (hasStrictFDerivAt_snd (p := w))
    exact this.congr_fderiv (by ext <;> simp [DΘ])
  have hDΘc : ContinuousAt DΘ (x₀, z₀) :=
    (continuousAt_const.clm_comp ((hDc.comp continuousAt_fst).clm_comp continuousAt_const)).add
      continuousAt_const
  set e' : (E × G) ≃L[ℝ] (F × G) := e.prodCongr (ContinuousLinearEquiv.refl ℝ G)
  have he' : DΘ (x₀, z₀) = e' := by ext <;> simp [DΘ, e', he]
  simp only [coderiv, mem_ofPred_eq, hgraph]
  rw [mem_normalCone_preimage_iff hΘ hDΘc he']
  have : (m.coprod (-z')).comp (e'.symm : F × G →L[ℝ] E × G) =
      (m.comp (e.symm : F →L[ℝ] E)).coprod (-z') := by
    ext <;> simp [e']
  rw [this]

omit [CompleteSpace F] in
/-- (3.28) of [Mordukhovich 2018, Thm. 3.11(iii)] for an invertible inner derivative:
`D*(F₃ ∘ F₁)(x̄, z̄)(z*) = {w ∘ ∇F₁(x̄) | w ∈ D*F₃(F₁ x̄, z̄)(z*)}`. -/
theorem coderiv_comp {F₁ : E → F} {D : E → E →L[ℝ] F} {e : E ≃L[ℝ] F}
    {F₃ : F → Set G} {x₀ : E} {z₀ : G} (hF : ∀ᶠ x in 𝓝 x₀, HasStrictFDerivAt F₁ (D x) x)
    (hDc : ContinuousAt D x₀) (he : D x₀ = e) (z' : StrongDual ℝ G) :
    coderiv (fun x ↦ F₃ (F₁ x)) x₀ z₀ z' =
      (fun w : StrongDual ℝ F ↦ w.comp (D x₀)) '' coderiv F₃ (F₁ x₀) z₀ z' := by
  ext m
  rw [mem_coderiv_comp_iff hF hDc he]
  constructor
  · intro h
    refine ⟨_, h, ?_⟩
    rw [he]; ext; simp
  · rintro ⟨w, hw, rfl⟩
    rw [he]
    have : ((w.comp (e : E →L[ℝ] F)).comp (e.symm : F →L[ℝ] E)) = w := by ext; simp
    rwa [this]

/-- Coderivative of the negative of a set-valued mapping: `gph(-F₂)` is the inverse image of
`gph F₂` under the linear isomorphism `(x, y) ↦ (x, -y)`, so
`D*(-F₂)(x̄, -ȳ)(y*) = D*F₂(x̄, ȳ)(-y*)` ([Mordukhovich 2018, Exercise 1.54]). -/
theorem mem_coderiv_neg_iff {F₂ : E → Set F} {x₀ : E} {y₀ : F} {y' : StrongDual ℝ F}
    {m : StrongDual ℝ E} :
    m ∈ coderiv (fun x ↦ -F₂ x) x₀ (-y₀) y' ↔ m ∈ coderiv F₂ x₀ y₀ (-y') := by
  set L : (E × F) ≃L[ℝ] (E × F) :=
    (ContinuousLinearEquiv.refl ℝ E).prodCongr (ContinuousLinearEquiv.neg ℝ)
  have hgraph : graph (fun x ↦ -F₂ x) = L ⁻¹' graph F₂ := by
    ext ⟨x, y⟩; simp [graph, L]
  have hL : ∀ᶠ w in 𝓝 (x₀, -y₀), HasStrictFDerivAt L (L : E × F →L[ℝ] E × F) w :=
    Eventually.of_forall fun w ↦ L.hasStrictFDerivAt
  simp only [coderiv, mem_ofPred_eq, hgraph]
  rw [mem_normalCone_preimage_iff (D := fun _ ↦ (L : E × F →L[ℝ] E × F)) hL continuousAt_const rfl]
  have hLx : L (x₀, -y₀) = (x₀, y₀) := by simp [L]
  have : (m.coprod (-y')).comp (L.symm : E × F →L[ℝ] E × F) = m.coprod (-(-y')) := by
    ext <;> simp [L]
  rw [hLx, this]

section BookForm

/-- (3.24) of [Mordukhovich 2018, Thm. 3.9(i)] in the book's form: for `F₁` of class `C¹`
around `x₀` and `(x₀, y₀) ∈ gph(F₁ + F₂)`,
`D*(F₁ + F₂)(x₀, y₀)(y*) = ∇F₁(x₀)* y* + D*F₂(x₀, y₀ - F₁ x₀)(y*)`. -/
theorem coderiv_add' {F₁ : E → F} {D : E → E →L[ℝ] F} {F₂ : E → Set F} {x₀ : E} {y₀ : F}
    (hF : ∀ᶠ x in 𝓝 x₀, HasStrictFDerivAt F₁ (D x) x) (hDc : ContinuousAt D x₀)
    (y' : StrongDual ℝ F) :
    coderiv (fun x ↦ (fun y ↦ F₁ x + y) '' F₂ x) x₀ y₀ y' =
      (fun u ↦ y'.comp (D x₀) + u) '' coderiv F₂ x₀ (y₀ - F₁ x₀) y' := by
  have h := coderiv_add (F₂ := F₂) (y₀ := y₀ - F₁ x₀) hF hDc y'
  rwa [add_sub_cancel] at h

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [CompleteSpace G] in
/-- The graph change in the proof of [Mordukhovich 2018, Thm. 3.11(iii)]:
`gph(F ∘ g) = (g, I)⁻¹(gph F)`. -/
theorem graph_comp_eq_preimage (F₃ : F → Set G) (g : E → F) :
    graph (fun x ↦ F₃ (g x)) = Prod.map g id ⁻¹' graph F₃ := rfl

end BookForm

section Surjective

open ContinuousLinearMap

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace G] in
/-- Pulling back normals to a graph along `A × I`: `(m, -z*) = ℓ ∘ (A × I)` with `ℓ ∈ N` iff
`m = u ∘ A` with `(u, -z*) ∈ N`. -/
theorem coprod_mem_image_comp_prodMap_iff {A : E →L[ℝ] F} {N : Set (StrongDual ℝ (F × G))}
    {z' : StrongDual ℝ G} {m : StrongDual ℝ E} :
    m.coprod (-z') ∈
        (fun ℓ : StrongDual ℝ (F × G) ↦ ℓ.comp (A.prodMap (ContinuousLinearMap.id ℝ G))) '' N ↔
      m ∈ (fun u : StrongDual ℝ F ↦ u.comp A) '' {u | u.coprod (-z') ∈ N} := by
  constructor
  · rintro ⟨ℓ, hℓ, heq⟩
    have h1 : m = (ℓ.comp (inl ℝ F G)).comp A := by
      ext x
      have := congrArg (fun f : StrongDual ℝ (E × G) ↦ f (x, 0)) heq
      simpa using this.symm
    have h2 : ℓ.comp (inr ℝ F G) = -z' := by
      ext z
      have := congrArg (fun f : StrongDual ℝ (E × G) ↦ f (0, z)) heq
      simpa using this
    refine ⟨ℓ.comp (inl ℝ F G), ?_, h1.symm⟩
    change _ ∈ N
    rw [← h2, coprod_comp_inl_inr]
    exact hℓ
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u.coprod (-z'), hu, by ext <;> simp⟩

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G]

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace G] in
/-- Exercise 1.61 of [Mordukhovich 2018] for the regular coderivative (finite dimensions): for
`g` strictly differentiable at `x₀` with surjective derivative `A`,
`D̂*(F ∘ g)(x₀, z₀)(z*) = A* D̂*F(g x₀, z₀)(z*)`. -/
theorem regularCoderiv_comp_of_surjective {g : E → F} {A : E →L[ℝ] F} {F₃ : F → Set G}
    {x₀ : E} {z₀ : G} (hg : HasStrictFDerivAt g A x₀) (hA : Function.Surjective A)
    (z' : StrongDual ℝ G) :
    regularCoderiv (fun x ↦ F₃ (g x)) x₀ z₀ z' =
      (fun w : StrongDual ℝ F ↦ w.comp A) '' regularCoderiv F₃ (g x₀) z₀ z' := by
  have hΘ : HasStrictFDerivAt (Prod.map g id) (A.prodMap (ContinuousLinearMap.id ℝ G)) (x₀, z₀) :=
    hg.prodMap (x₀, z₀) (hasStrictFDerivAt_id z₀)
  have hsurj : Function.Surjective (A.prodMap (ContinuousLinearMap.id ℝ G)) := by
    rintro ⟨y, z⟩
    obtain ⟨x, hx⟩ := hA y
    exact ⟨(x, z), by simp [hx]⟩
  ext m
  simp only [regularCoderiv, mem_ofPred_eq, graph_comp_eq_preimage]
  rw [regularNormalCone_preimage_of_surjective_of_finiteDimensional hΘ hsurj]
  exact coprod_mem_image_comp_prodMap_iff

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace G] in
/-- Thm. 3.11(iii) of [Mordukhovich 2018] (coderivative chain rule (3.28), full-rank case), also
Exercise 1.61: for `g` of class `C¹` around `x₀` with surjective (full-rank) derivative
`∇g(x₀) = D x₀`, `D*(F ∘ g)(x₀, z₀)(z*) = ∇g(x₀)* D*F(g x₀, z₀)(z*)`, with no assumption on
`F`. As in the book, this follows from `gph(F ∘ g) = (g, I)⁻¹(gph F)` (`graph_comp_eq_preimage`)
and Exercise 1.54(ii) (`normalCone_preimage_of_surjective_of_finiteDimensional`). -/
theorem coderiv_comp_of_surjective {g : E → F} {D : E → E →L[ℝ] F} {F₃ : F → Set G} {x₀ : E}
    {z₀ : G} (hg : ∀ᶠ x in 𝓝 x₀, HasStrictFDerivAt g (D x) x) (hDc : ContinuousAt D x₀)
    (hA : Function.Surjective (D x₀)) (z' : StrongDual ℝ G) :
    coderiv (fun x ↦ F₃ (g x)) x₀ z₀ z' =
      (fun w : StrongDual ℝ F ↦ w.comp (D x₀)) '' coderiv F₃ (g x₀) z₀ z' := by
  set DΘ : E × G → E × G →L[ℝ] F × G := fun w ↦ (D w.1).prodMap (ContinuousLinearMap.id ℝ G)
  have hΘ : ∀ᶠ w in 𝓝 (x₀, z₀), HasStrictFDerivAt (Prod.map g id) (DΘ w) w := by
    have hg' : ∀ᶠ w in 𝓝 (x₀, z₀), HasStrictFDerivAt g (D w.1) w.1 :=
      (continuous_fst.tendsto (x₀, z₀)).eventually hg
    filter_upwards [hg'] with w hw
    exact hw.prodMap w (hasStrictFDerivAt_id w.2)
  have hDΘc : ContinuousAt DΘ (x₀, z₀) :=
    (ContinuousLinearMap.prodMapL ℝ E F G G).continuous.continuousAt.comp
      ((hDc.comp continuousAt_fst).prodMk continuousAt_const)
  have hsurj : Function.Surjective (DΘ (x₀, z₀)) := by
    rintro ⟨y, z⟩
    obtain ⟨x, hx⟩ := hA y
    exact ⟨(x, z), by simp [DΘ, hx]⟩
  ext m
  simp only [coderiv, mem_ofPred_eq, graph_comp_eq_preimage]
  rw [normalCone_preimage_of_surjective_of_finiteDimensional hΘ hDΘc hsurj]
  exact coprod_mem_image_comp_prodMap_iff

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace G] in
/-- Thm. 3.11(iii) of [Mordukhovich 2018] (full-rank case), pointwise form: for `g` of class
`C¹` around `x₀` with surjective derivative `∇g(x₀) = D x₀`,
`w ∘ ∇g(x₀) ∈ D*(F ∘ g)(x₀, z₀)(z*)` iff `w ∈ D*F(g x₀, z₀)(z*)`. -/
theorem comp_mem_coderiv_comp_iff_of_surjective {g : E → F} {D : E → E →L[ℝ] F}
    {F₃ : F → Set G} {x₀ : E} {z₀ : G} (hg : ∀ᶠ x in 𝓝 x₀, HasStrictFDerivAt g (D x) x)
    (hDc : ContinuousAt D x₀) (hA : Function.Surjective (D x₀)) {z' : StrongDual ℝ G}
    {w : StrongDual ℝ F} :
    w.comp (D x₀) ∈ coderiv (fun x ↦ F₃ (g x)) x₀ z₀ z' ↔ w ∈ coderiv F₃ (g x₀) z₀ z' := by
  rw [coderiv_comp_of_surjective hg hDc hA]
  exact (comp_injective_of_surjective hA).mem_set_image

end Surjective

end VariationalAnalysis
