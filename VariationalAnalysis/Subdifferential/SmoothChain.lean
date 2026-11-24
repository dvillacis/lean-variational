/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis.Coderivative.Smooth
import VariationalAnalysis.Subdifferential.Limiting

/-!
# Subgradients of compositions with smooth mappings of full rank

For `ψ : W → EReal` and `g : F → W` of class `C¹` around `y₀` with surjective derivative
`∇g(y₀)`, [Mordukhovich 2018, Exercise 1.72] states the chain rules

  `∂̂(ψ ∘ g)(y₀) = ∇g(y₀)* ∂̂ψ(g y₀)`, `∂(ψ ∘ g)(y₀) = ∇g(y₀)* ∂ψ(g y₀)`,
  `∂^∞(ψ ∘ g)(y₀) = ∇g(y₀)* ∂^∞ψ(g y₀)`,

with `∇g(y₀)* v = v ∘ ∇g(y₀)`. Following the hint of the book, we deduce them from the
coderivative chain rule of `Coderivative/Smooth` applied to the epigraphical multifunction
`E_ψ(w) = {α | ψ w ≤ α}` ([Mordukhovich 2018, (1.29)]), whose graph is the epigraph of `ψ`:
`∂ψ(w) = D*E_ψ(w, ψ w)(1)` and `∂^∞ψ(w) = D*E_ψ(w, ψ w)(0)`.

The regular rule only needs strict differentiability at `y₀`; the limiting ones use the `C¹`
convention of `Normal/Diffeomorphism` (strict derivative `D y` at every `y` near `y₀`, `D`
continuous at `y₀`), the setting where the book applies them.

## Main results

* `epiMap`: the epigraphical multifunction `E_ψ` [Mordukhovich 2018, (1.29)];
  `mem_subdiff_iff_mem_coderiv_epiMap`, `mem_singularSubdiff_iff_mem_coderiv_epiMap`,
  `mem_regularSubdiff_iff_mem_regularCoderiv_epiMap`.
* `regularSubdiff_comp_of_surjective`, `subdiff_comp_of_surjective`,
  `singularSubdiff_comp_of_surjective`: Exercise 1.72 of [Mordukhovich 2018] (finite
  dimensions).
* `comp_mem_subdiff_comp_iff_of_surjective`: pointwise form of the basic chain rule.
-/

open Filter Topology Set

namespace VariationalAnalysis

variable {F W : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

section EpiMap

/-- The epigraphical multifunction `E_ψ(w) = {α ∈ ℝ | ψ w ≤ α}` of `ψ : W → EReal`
[Mordukhovich 2018, (1.29)]; its graph is the epigraph of `ψ`. -/
def epiMap (ψ : W → EReal) : W → Set ℝ := fun w ↦ {α : ℝ | ψ w ≤ α}

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The graph of the epigraphical multifunction is the epigraph. -/
theorem graph_epiMap (ψ : W → EReal) : graph (epiMap ψ) = ψ.Epi univ := by
  ext p; simp [graph, epiMap, Function.Epi]

variable {ψ : W → EReal} {w : W} {r : ℝ} {v : StrongDual ℝ W}

/-- `∂ψ(w) = D*E_ψ(w, ψ w)(1)` [Mordukhovich 2018, (1.29)–(1.30)]. -/
theorem mem_subdiff_iff_mem_coderiv_epiMap (hr : ψ w = r) :
    v ∈ subdiff ψ w ↔ v ∈ coderiv (epiMap ψ) w r 1 := by
  rw [mem_subdiff_iff hr]
  simp only [coderiv, mem_ofPred_eq, graph_epiMap]

/-- `∂^∞ψ(w) = D*E_ψ(w, ψ w)(0)` [Mordukhovich 2018, (1.29)–(1.31)]. -/
theorem mem_singularSubdiff_iff_mem_coderiv_epiMap (hr : ψ w = r) :
    v ∈ singularSubdiff ψ w ↔ v ∈ coderiv (epiMap ψ) w r 0 := by
  rw [mem_singularSubdiff_iff hr]
  simp only [coderiv, mem_ofPred_eq, graph_epiMap, neg_zero]

/-- `∂̂ψ(w) = D̂*E_ψ(w, ψ w)(1)` (Thm. 1.26 of [Mordukhovich 2018]). -/
theorem mem_regularSubdiff_iff_mem_regularCoderiv_epiMap (hr : ψ w = r) :
    v ∈ regularSubdiff ψ w ↔ v ∈ regularCoderiv (epiMap ψ) w r 1 := by
  rw [mem_regularSubdiff_iff_coprod_mem hr]
  simp only [regularCoderiv, mem_ofPred_eq, graph_epiMap]

end EpiMap

section Chain

variable [FiniteDimensional ℝ F] [FiniteDimensional ℝ W] {ψ : W → EReal} {g : F → W} {y₀ : F}

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ W] in
/-- A chain rule for a subdifferential construction `∂•` described through the epigraphical
multifunction: if `∂•φ(y) = C(E_φ)(y, φ y)` for a construction `C` satisfying the chain rule
`C(E_ψ ∘ g)(y₀, r) = A* C(E_ψ)(g y₀, r)`, then `∂•(ψ ∘ g)(y₀) = A* ∂•ψ(g y₀)`. -/
private theorem chain_of_epiMap {A : F →L[ℝ] W} {sF : (F → EReal) → F → Set (StrongDual ℝ F)}
    {sW : (W → EReal) → W → Set (StrongDual ℝ W)}
    {CF : (F → Set ℝ) → F → ℝ → Set (StrongDual ℝ F)}
    {CW : (W → Set ℝ) → W → ℝ → Set (StrongDual ℝ W)}
    (hF : ∀ (φ : F → EReal) (y : F) (r : ℝ), φ y = r → ∀ m, m ∈ sF φ y ↔ m ∈ CF (epiMap φ) y r)
    (hW : ∀ (φ : W → EReal) (w : W) (r : ℝ), φ w = r → ∀ m, m ∈ sW φ w ↔ m ∈ CW (epiMap φ) w r)
    (hFnf : ∀ (φ : F → EReal) (y : F), (∀ r : ℝ, φ y ≠ r) → sF φ y = ∅)
    (hWnf : ∀ (φ : W → EReal) (w : W), (∀ r : ℝ, φ w ≠ r) → sW φ w = ∅)
    (hC : ∀ r : ℝ, CF (fun y ↦ epiMap ψ (g y)) y₀ r =
      (fun v : StrongDual ℝ W ↦ v.comp A) '' CW (epiMap ψ) (g y₀) r) :
    sF (fun y ↦ ψ (g y)) y₀ = (fun v : StrongDual ℝ W ↦ v.comp A) '' sW ψ (g y₀) := by
  by_cases hfin : ∃ r : ℝ, ψ (g y₀) = r
  · obtain ⟨r, hr⟩ := hfin
    ext m
    rw [hF (fun y ↦ ψ (g y)) y₀ r hr]
    change m ∈ CF (fun y ↦ epiMap ψ (g y)) y₀ r ↔ _
    rw [hC r]
    simp only [mem_image, hW ψ (g y₀) r hr]
  · push Not at hfin
    rw [hFnf _ _ hfin, hWnf _ _ hfin, image_empty]

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ W] in
private theorem subdiff_eq_empty {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : E → EReal) (x : E) (h : ∀ r : ℝ, φ x ≠ r) : subdiff φ x = ∅ :=
  eq_empty_of_forall_notMem fun _ ⟨r, hr, _⟩ ↦ h r hr

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ W] in
private theorem singularSubdiff_eq_empty {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : E → EReal) (x : E) (h : ∀ r : ℝ, φ x ≠ r) : singularSubdiff φ x = ∅ :=
  eq_empty_of_forall_notMem fun _ ⟨r, hr, _⟩ ↦ h r hr

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ W] in
private theorem regularSubdiff_eq_empty {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : E → EReal) (x : E) (h : ∀ r : ℝ, φ x ≠ r) : regularSubdiff φ x = ∅ :=
  eq_empty_of_forall_notMem fun _ ⟨r, hr, _⟩ ↦ h r hr

/-- Exercise 1.72 of [Mordukhovich 2018] (regular subgradients of compositions): for `g`
strictly differentiable at `y₀` with surjective derivative `A`,
`∂̂(ψ ∘ g)(y₀) = A* ∂̂ψ(g y₀)` (finite dimensions). -/
theorem regularSubdiff_comp_of_surjective {A : F →L[ℝ] W} (hg : HasStrictFDerivAt g A y₀)
    (hA : Function.Surjective A) :
    regularSubdiff (fun y ↦ ψ (g y)) y₀ =
      (fun v : StrongDual ℝ W ↦ v.comp A) '' regularSubdiff ψ (g y₀) :=
  chain_of_epiMap (CF := fun S y r ↦ regularCoderiv S y r 1)
    (CW := fun S w r ↦ regularCoderiv S w r 1)
    (fun _ _ _ hr _ ↦ mem_regularSubdiff_iff_mem_regularCoderiv_epiMap hr)
    (fun _ _ _ hr _ ↦ mem_regularSubdiff_iff_mem_regularCoderiv_epiMap hr)
    regularSubdiff_eq_empty regularSubdiff_eq_empty
    (fun _ ↦ regularCoderiv_comp_of_surjective hg hA 1)

variable {D : F → F →L[ℝ] W}

/-- Exercise 1.72 of [Mordukhovich 2018] (basic subgradients of compositions with surjective
derivatives of inner mappings): for `g` of class `C¹` around `y₀` with surjective derivative
`∇g(y₀) = D y₀`, `∂(ψ ∘ g)(y₀) = ∇g(y₀)* ∂ψ(g y₀)`, with no assumption on `ψ`
(finite dimensions). -/
theorem subdiff_comp_of_surjective (hg : ∀ᶠ y in 𝓝 y₀, HasStrictFDerivAt g (D y) y)
    (hDc : ContinuousAt D y₀) (hA : Function.Surjective (D y₀)) :
    subdiff (fun y ↦ ψ (g y)) y₀ =
      (fun v : StrongDual ℝ W ↦ v.comp (D y₀)) '' subdiff ψ (g y₀) :=
  chain_of_epiMap (CF := fun S y r ↦ coderiv S y r 1) (CW := fun S w r ↦ coderiv S w r 1)
    (fun _ _ _ hr _ ↦ mem_subdiff_iff_mem_coderiv_epiMap hr)
    (fun _ _ _ hr _ ↦ mem_subdiff_iff_mem_coderiv_epiMap hr)
    subdiff_eq_empty subdiff_eq_empty
    (fun _ ↦ coderiv_comp_of_surjective hg hDc hA 1)

/-- Exercise 1.72 of [Mordukhovich 2018] (singular subgradients of compositions): for `g` of
class `C¹` around `y₀` with surjective derivative `∇g(y₀) = D y₀`,
`∂^∞(ψ ∘ g)(y₀) = ∇g(y₀)* ∂^∞ψ(g y₀)` (finite dimensions). -/
theorem singularSubdiff_comp_of_surjective (hg : ∀ᶠ y in 𝓝 y₀, HasStrictFDerivAt g (D y) y)
    (hDc : ContinuousAt D y₀) (hA : Function.Surjective (D y₀)) :
    singularSubdiff (fun y ↦ ψ (g y)) y₀ =
      (fun v : StrongDual ℝ W ↦ v.comp (D y₀)) '' singularSubdiff ψ (g y₀) :=
  chain_of_epiMap (CF := fun S y r ↦ coderiv S y r 0) (CW := fun S w r ↦ coderiv S w r 0)
    (fun _ _ _ hr _ ↦ mem_singularSubdiff_iff_mem_coderiv_epiMap hr)
    (fun _ _ _ hr _ ↦ mem_singularSubdiff_iff_mem_coderiv_epiMap hr)
    singularSubdiff_eq_empty singularSubdiff_eq_empty
    (fun _ ↦ coderiv_comp_of_surjective hg hDc hA 0)

/-- Exercise 1.72 of [Mordukhovich 2018], pointwise form: for `g` of class `C¹` around `y₀`
with surjective derivative `∇g(y₀) = D y₀`, `v ∘ ∇g(y₀) ∈ ∂(ψ ∘ g)(y₀)` iff
`v ∈ ∂ψ(g y₀)`; in particular the `v` representing a subgradient of `ψ ∘ g` is unique. -/
theorem comp_mem_subdiff_comp_iff_of_surjective
    (hg : ∀ᶠ y in 𝓝 y₀, HasStrictFDerivAt g (D y) y) (hDc : ContinuousAt D y₀)
    (hA : Function.Surjective (D y₀)) {v : StrongDual ℝ W} :
    v.comp (D y₀) ∈ subdiff (fun y ↦ ψ (g y)) y₀ ↔ v ∈ subdiff ψ (g y₀) := by
  rw [subdiff_comp_of_surjective hg hDc hA]
  exact (comp_injective_of_surjective hA).mem_set_image

end Chain

end VariationalAnalysis
