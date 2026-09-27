/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import VariationalAnalysis.Coderivative.ChainRule

/-!
# Coderivatives of compositions with respect to binary operations

For `F₁ : X ⇉ Y₁`, `F₂ : X ⇉ Y₂` and a single-valued `h : Y₁ × Y₂ → Z`, the `h`-composition of
[Mordukhovich 2018, Subsection 3.2.3] is

  `(F₁ ⋄_h F₂)(x) = {h(y₁, y₂) | y₁ ∈ F₁ x, y₂ ∈ F₂ x} = h(F₁ x × F₂ x)`,

which covers sums, products, quotients, maxima and minima of set-valued mappings. As in the book,
`F₁ ⋄_h F₂ = h ∘ F` with the pair mapping `F(x) = F₁ x × F₂ x`; the chain rule (Thm. 3.11(i),
through Cor. 3.12 for the locally Lipschitz `h`) and the estimate (3.33) of `D*F` give
Thm. 3.14. The auxiliary mapping of Thm. 3.14,
`S(x, z) = {(y₁, y₂) | yᵢ ∈ Fᵢ(x), z = h(y₁, y₂)}`, is the mapping (3.25) of `h ∘ F`,
`chainAuxMap (fun y ↦ {h y}) (pairMap F₁ F₂)` (`mem_chainAuxMap_pairMap_iff`).

## A missing hypothesis in the book

The book states Thm. 3.14 without a qualification condition, while (3.33) is derived from the
sum rule Thm. 3.9, which needs (3.22): `D*F₁(x̄, ȳ₁)(0) ∩ (-D*F₂(x̄, ȳ₂)(0)) = {0}`. The condition
cannot be dropped: in `ℝ`, let `gph F₁ = {(x, y₁) | x ≤ -y₁²}` and `gph F₂ = {(x, y₂) | x ≥ y₂²}`
and `h(y₁, y₂) = y₁ + y₂`. Then `F₁ ⋄_h F₂` has graph `{(0, 0)}`, so its coderivative at `(0, 0)`
is `ℝ` in every direction `z*`, while `D*F₁(0, 0)(y*) = D*F₂(0, 0)(y*) = ∅` for `y* ≠ 0`, so the
right-hand side of Thm. 3.14 is empty for `z* ≠ 0`. We add (3.22) as a hypothesis (it is also
the hypothesis of Cor. 3.15 in the book).

## Main results

* `binaryComp`: the `h`-composition; `binaryComp_eq_setComp`: `F₁ ⋄_h F₂ = h ∘ (F₁ × F₂)`.
* `coderiv_binaryComp_subset`: Thm. 3.14 of [Mordukhovich 2018] (with (3.22)).
* `coderiv_innerComp_subset`: Cor. 3.15 of [Mordukhovich 2018] (coderivatives of inner products),
  for `F₁, F₂ : X ⇉ Y` with values in a finite-dimensional real inner product space `Y`.
-/

open Filter Topology Set Metric ContinuousLinearMap
open scoped Pointwise NNReal RealInnerProductSpace

namespace VariationalAnalysis

variable {X Y₁ Y₂ Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y₁]
  [NormedSpace ℝ Y₁] [NormedAddCommGroup Y₂] [NormedSpace ℝ Y₂] [NormedAddCommGroup Z]
  [NormedSpace ℝ Z]

section Definition

/-- The `h`-composition `(F₁ ⋄_h F₂)(x) = {h(y₁, y₂) | y₁ ∈ F₁ x, y₂ ∈ F₂ x}` of
[Mordukhovich 2018, Subsection 3.2.3]. -/
def binaryComp (h : Y₁ × Y₂ → Z) (F₁ : X → Set Y₁) (F₂ : X → Set Y₂) : X → Set Z :=
  fun x ↦ h '' (F₁ x ×ˢ F₂ x)

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y₁] [NormedSpace ℝ Y₁]
  [NormedAddCommGroup Y₂] [NormedSpace ℝ Y₂] [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- `F₁ ⋄_h F₂ = h ∘ F` with `F(x) = F₁ x × F₂ x` [Mordukhovich 2018, proof of Thm. 3.14]. -/
theorem binaryComp_eq_setComp (h : Y₁ × Y₂ → Z) (F₁ : X → Set Y₁) (F₂ : X → Set Y₂) :
    binaryComp h F₁ F₂ = setComp (fun y ↦ {h y}) (pairMap F₁ F₂) := by
  funext x
  ext z
  simp only [binaryComp, mem_image, mem_setComp_iff, mem_singleton_iff]
  exact ⟨fun ⟨y, hy, hz⟩ ↦ ⟨y, hy, hz.symm⟩, fun ⟨y, hy, hz⟩ ↦ ⟨y, hy, hz.symm⟩⟩

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y₁] [NormedSpace ℝ Y₁]
  [NormedAddCommGroup Y₂] [NormedSpace ℝ Y₂] [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- The auxiliary mapping of Thm. 3.14 of [Mordukhovich 2018]:
`S(x, z) = {(y₁, y₂) | y₁ ∈ F₁ x, y₂ ∈ F₂ x, z = h(y₁, y₂)}`. -/
theorem mem_chainAuxMap_pairMap_iff {h : Y₁ × Y₂ → Z} {F₁ : X → Set Y₁} {F₂ : X → Set Y₂}
    {x : X} {z : Z} {y : Y₁ × Y₂} :
    y ∈ chainAuxMap (fun y ↦ {h y}) (pairMap F₁ F₂) (x, z) ↔
      y.1 ∈ F₁ x ∧ y.2 ∈ F₂ x ∧ z = h y := by
  simp [chainAuxMap, pairMap, and_assoc]

end Definition

variable [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y₁] [FiniteDimensional ℝ Y₂]
  [FiniteDimensional ℝ Z]

/-- Thm. 3.14 of [Mordukhovich 2018] (coderivatives of compositions with respect to binary
operations): let `(ȳ₁, ȳ₂) ∈ S(x̄, z̄)` for `S(x, z) = {(y₁, y₂) | yᵢ ∈ Fᵢ x, z = h(y₁, y₂)}`, let
`S` be inner semicontinuous at `(x̄, z̄, ȳ₁, ȳ₂)`, let `h` be Lipschitz continuous on a
neighborhood of `ȳ = (ȳ₁, ȳ₂)`, and let the graphs of `F₁`, `F₂` be locally closed around
`(x̄, ȳ₁)`, `(x̄, ȳ₂)`. Under the qualification condition (3.22)
`D*F₁(x̄, ȳ₁)(0) ∩ (-D*F₂(x̄, ȳ₂)(0)) = {0}` (not stated in the book, but needed: see the module
docstring),

  `D*(F₁ ⋄_h F₂)(x̄, z̄)(z*) ⊆ ⋃_{(y₁*, y₂*) ∈ D*h(ȳ)(z*)} [D*F₁(x̄, ȳ₁)(y₁*) + D*F₂(x̄, ȳ₂)(y₂*)]`,

where `(y₁*, y₂*) = (w ∘ inl, w ∘ inr)` for `w ∈ D*h(ȳ)(z*)`. -/
theorem coderiv_binaryComp_subset {h : Y₁ × Y₂ → Z} {F₁ : X → Set Y₁} {F₂ : X → Set Y₂}
    {x₀ : X} {y₁ : Y₁} {y₂ : Y₂} {z₀ : Z}
    (hy : (y₁, y₂) ∈ chainAuxMap (fun y ↦ {h y}) (pairMap F₁ F₂) (x₀, z₀))
    (hS : InnerSemicontinuousAt (chainAuxMap (fun y ↦ {h y}) (pairMap F₁ F₂)) (x₀, z₀) (y₁, y₂))
    {U : Set (Y₁ × Y₂)} (hU : U ∈ 𝓝 (y₁, y₂)) {K : ℝ≥0} (hh : LipschitzOnWith K h U)
    (hloc₁ : ∃ r > 0, IsClosed (graph F₁ ∩ closedBall (x₀, y₁) r))
    (hloc₂ : ∃ r > 0, IsClosed (graph F₂ ∩ closedBall (x₀, y₂) r))
    (hqc : ∀ u ∈ coderiv F₁ x₀ y₁ 0, -u ∈ coderiv F₂ x₀ y₂ 0 → u = 0) (z' : StrongDual ℝ Z) :
    coderiv (binaryComp h F₁ F₂) x₀ z₀ z' ⊆
      ⋃ w ∈ coderiv (fun y ↦ {h y}) (y₁, y₂) z₀ z',
        coderiv F₁ x₀ y₁ (w.comp (inl ℝ Y₁ Y₂)) + coderiv F₂ x₀ y₂ (w.comp (inr ℝ Y₁ Y₂)) := by
  have hz₀ : z₀ = h (y₁, y₂) := hy.2
  subst hz₀
  rw [binaryComp_eq_setComp]
  intro x' hx
  have h1 := coderiv_setComp_subset_of_lipschitzLike_or_metricallyRegular
    (G := pairMap F₁ F₂) (F := fun y ↦ {h y}) (y₀ := (y₁, y₂)) hy hS
    (locallyClosed_graph_pairMap hloc₁ hloc₂) (locallyClosed_graph_of_continuousOn hU hh.continuousOn)
    (Or.inl (lipschitzLikeAt_of_lipschitzOnWith hU hh)) z' hx
  obtain ⟨w, hw, hx'⟩ := mem_iUnion₂.1 h1
  exact mem_biUnion hw (coderiv_pairMap_subset hloc₁ hloc₂ hqc w hx')

section InnerProduct

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

omit [NormedAddCommGroup Y₁] [NormedSpace ℝ Y₁] [NormedAddCommGroup Y₂] [NormedSpace ℝ Y₂]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Y₁] [FiniteDimensional ℝ Y₂]
  [FiniteDimensional ℝ Z] in
/-- Cor. 3.15 of [Mordukhovich 2018] (coderivatives of inner products): for `F₁, F₂ : X ⇉ Y`
with values in a finite-dimensional real inner product space, the inner product
`⟨F₁, F₂⟩(x) = {⟨y₁, y₂⟩ | yᵢ ∈ Fᵢ x}` (the `h`-composition with `h(y₁, y₂) = ⟨y₁, y₂⟩`), and
`ν̄ = ⟨ȳ₁, ȳ₂⟩` with `ȳᵢ ∈ Fᵢ(x̄)`: if the mapping
`(x, ν) ↦ {(y₁, y₂) | yᵢ ∈ Fᵢ x, ν = ⟨y₁, y₂⟩}` is inner semicontinuous at `(x̄, ν̄, ȳ₁, ȳ₂)`,
the graphs of `Fᵢ` are locally closed around `(x̄, ȳᵢ)` and (3.22) holds, then for every
`θ ∈ ℝ` (the direction `z* = θ` is the dual element `z*` of `ℝ` with `z* 1 = θ`)

  `D*⟨F₁, F₂⟩(x̄, ν̄)(θ) ⊆ D*F₁(x̄, ȳ₁)(θ ȳ₂) + D*F₂(x̄, ȳ₂)(θ ȳ₁)`,

where `θ ȳᵢ` is the dual element `θ ⟨ȳᵢ, ·⟩` (`innerSL`). -/
theorem coderiv_innerComp_subset {F₁ F₂ : X → Set Y} {x₀ : X} {y₁ y₂ : Y} {ν₀ : ℝ}
    (hy : (y₁, y₂) ∈ chainAuxMap (fun y : Y × Y ↦ {⟪y.1, y.2⟫}) (pairMap F₁ F₂) (x₀, ν₀))
    (hS : InnerSemicontinuousAt (chainAuxMap (fun y : Y × Y ↦ {⟪y.1, y.2⟫}) (pairMap F₁ F₂))
      (x₀, ν₀) (y₁, y₂))
    (hloc₁ : ∃ r > 0, IsClosed (graph F₁ ∩ closedBall (x₀, y₁) r))
    (hloc₂ : ∃ r > 0, IsClosed (graph F₂ ∩ closedBall (x₀, y₂) r))
    (hqc : ∀ u ∈ coderiv F₁ x₀ y₁ 0, -u ∈ coderiv F₂ x₀ y₂ 0 → u = 0) (z' : StrongDual ℝ ℝ) :
    coderiv (binaryComp (fun y : Y × Y ↦ ⟪y.1, y.2⟫) F₁ F₂) x₀ ν₀ z' ⊆
      coderiv F₁ x₀ y₁ (z' 1 • innerSL ℝ y₂) + coderiv F₂ x₀ y₂ (z' 1 • innerSL ℝ y₁) := by
  have hb := isBoundedBilinearMap_inner (𝕜 := ℝ) (E := Y)
  have hν : ν₀ = ⟪y₁, y₂⟫ := hy.2
  subst hν
  obtain ⟨K, U, hU, hK⟩ := (hb.hasStrictFDerivAt (y₁, y₂)).exists_lipschitzOnWith
  intro x' hx
  have h1 := coderiv_binaryComp_subset hy hS hU hK hloc₁ hloc₂ hqc z' hx
  have hcod : coderiv (fun y : Y × Y ↦ {⟪y.1, y.2⟫}) (y₁, y₂) ⟪(y₁, y₂).1, (y₁, y₂).2⟫ z' =
      {z'.comp (hb.deriv (y₁, y₂))} :=
    coderiv_of_hasFDerivAt_of_continuousAt
      (Eventually.of_forall fun p ↦ (hb.hasStrictFDerivAt p).hasFDerivAt)
      hb.isBoundedLinearMap_deriv.continuous.continuousAt z'
  obtain ⟨w, hw, hx'⟩ := mem_iUnion₂.1 h1
  rw [hcod, mem_singleton_iff] at hw
  subst hw
  have hz : ∀ t : ℝ, z' t = z' 1 * t := fun t ↦ by
    have := z'.map_smul t (1 : ℝ)
    simp only [smul_eq_mul, mul_one] at this
    rw [this, mul_comm]
  have e1 : (z'.comp (hb.deriv (y₁, y₂))).comp (inl ℝ Y Y) = z' 1 • innerSL ℝ y₂ := by
    ext a
    rw [comp_apply, comp_apply, inl_apply, hb.deriv_apply, hz]
    simp [real_inner_comm]
  have e2 : (z'.comp (hb.deriv (y₁, y₂))).comp (inr ℝ Y Y) = z' 1 • innerSL ℝ y₁ := by
    ext b
    rw [comp_apply, comp_apply, inr_apply, hb.deriv_apply, hz]
    simp
  rwa [e1, e2] at hx'

end InnerProduct

end VariationalAnalysis
