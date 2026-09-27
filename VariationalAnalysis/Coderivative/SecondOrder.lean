/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.LinearAlgebra.Dual.Lemmas
import VariationalAnalysis.Subdifferential.SmoothChain

/-!
# Second-order subdifferentials

The second-order subdifferential (generalized Hessian) of `φ : E → EReal` at `x₀` relative to
`v₀ ∈ ∂φ(x₀)` [Mordukhovich 2018, Def. 3.17] is the coderivative of the subgradient mapping,

  `∂²φ(x₀, v₀)(u) = (D*∂φ)(x₀, v₀)(u)`.

**Encoding of the direction `u`.** Subgradients are dual elements, so `∂φ : E → Set E*` and the
coderivative `D*∂φ(x₀, v₀)` acts on the bidual `E**`. The book works in `ℝⁿ`, where
`u ∈ ℝⁿ = (ℝⁿ)**`. We take `u : E` and feed the coderivative with its image under the canonical
embedding `NormedSpace.inclusionInDoubleDual ℝ E : E → E**`, `u ↦ (v ↦ v u)`. In finite
dimensions this embedding is bijective (`inclusionInDoubleDual_surjective`), so nothing is lost:
every `D*∂φ(x₀, v₀)(z)`, `z ∈ E**`, is some `∂²φ(x₀, v₀)(u)`
(`exists_coderiv_subdiff_eq_secondOrderSubdiff`). In infinite dimensions this is the
restriction of the book's (3.76)–(3.77) to `u ∈ E ⊆ E**`.

## Main results

* `inclusionInDoubleDual_surjective`: `E → E**` is onto in finite dimensions.
* `secondOrderSubdiff`: Def. 3.17, (3.42), of [Mordukhovich 2018].
* `coderiv_congr`: coderivatives only depend on the mapping near the point.
* `secondOrderSubdiff_of_hasFDerivAt`: (3.43) of [Mordukhovich 2018]: for `φ` of class `C²`
  around `x₀`, `∂²φ(x₀)(u) = {∇²φ(x₀) u}`.
* `secondOrderSubdiff_comp_of_surjective`: the second-order chain rule (3.47)
  [Mordukhovich 2018, Exercise 3.78(i)]: for `g` of class `C²` around `ȳ` with surjective
  derivative and `q̄ = ∇g(ȳ)* v̄`,
  `∂²(ψ ∘ g)(ȳ, q̄)(u) = ∇²⟨v̄, g⟩(ȳ) u + ∇g(ȳ)* ∂²ψ(g ȳ, v̄)(∇g(ȳ) u)`.

## Proof of the chain rule

By Exercise 1.72 (`subdiff_comp_of_surjective`), `∂(ψ ∘ g)(y) = ∇g(y)* ∂ψ(g y)` for `y` near
`ȳ`. Let `K = ker ∇g(ȳ)` and `P` a continuous projection onto `K`. The map

  `H((y, v), κ) = (y, v ∘ ∇g(y) + κ ∘ P) : (F × W*) × K* → F × F*`

is `C¹` (this uses `g ∈ C²`) with invertible derivative at `((ȳ, v̄), 0)`, and near this point
`H⁻¹(gph ∂(ψ ∘ g)) = gph(∂ψ ∘ g) × {0}`, because `(v, κ) ↦ v ∘ ∇g(y) + κ ∘ P` is injective for
`y` near `ȳ`. The normals to `gph(∂ψ ∘ g)` are given by the full-rank coderivative chain rule
(`coderiv_comp_of_surjective`), and the normals to `gph ∂(ψ ∘ g)` are recovered by
`comp_mem_normalCone_preimage_iff` (Exercise 1.54 for a diffeomorphism).
-/

open Filter Topology Set ContinuousLinearMap

namespace VariationalAnalysis

section DoubleDual

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- In finite dimensions the topological dual has the dimension of the space. -/
theorem finrank_strongDual : Module.finrank ℝ (StrongDual ℝ E) = Module.finrank ℝ E := by
  rw [← LinearEquiv.finrank_eq (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _)]
  exact Subspace.dual_finrank_eq

omit [FiniteDimensional ℝ E] in
/-- The canonical embedding into the bidual is injective (Hahn–Banach). -/
theorem inclusionInDoubleDual_injective :
    Function.Injective (NormedSpace.inclusionInDoubleDual ℝ E) := by
  intro x y h
  by_contra hxy
  have hne : ‖x - y‖ ≠ 0 := by rwa [norm_ne_zero_iff, sub_ne_zero]
  obtain ⟨f, -, hf⟩ := exists_dual_vector ℝ (x - y) hne
  have hxy' : f x = f y := by
    simpa using congrArg (fun φ : StrongDual ℝ (StrongDual ℝ E) ↦ φ f) h
  rw [map_sub, hxy', sub_self] at hf
  exact hne (by exact_mod_cast hf.symm)

/-- In finite dimensions the canonical embedding `E → E**` is onto. -/
theorem inclusionInDoubleDual_surjective :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E) := by
  have h : Module.finrank ℝ E = Module.finrank ℝ (StrongDual ℝ (StrongDual ℝ E)) := by
    rw [finrank_strongDual, finrank_strongDual]
  have hinj : Function.Injective (NormedSpace.inclusionInDoubleDual ℝ E).toLinearMap :=
    inclusionInDoubleDual_injective (E := E)
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h).1 hinj

end DoubleDual

section Locality

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Coderivatives only depend on the mapping near the point. -/
theorem coderiv_congr {S T : E → Set F} {x₀ : E} (h : ∀ᶠ x in 𝓝 x₀, S x = T x) (y₀ : F)
    (v : StrongDual ℝ F) : coderiv S x₀ y₀ v = coderiv T x₀ y₀ v := by
  have hg : graph S =ᶠ[𝓝 (x₀, y₀)] graph T := by
    filter_upwards [(continuous_fst.tendsto (x₀, y₀)).eventually h] with p hp
    show (p.2 ∈ S p.1) = (p.2 ∈ T p.1)
    rw [hp]
  simp only [coderiv, normalCone_congr hg]

/-- Every dual element is normal to a singleton: `N(x₀; {x₀}) = E*`. -/
theorem normalCone_singleton (x₀ : E) : normalCone {x₀} x₀ = univ := by
  refine eq_univ_of_forall fun v ↦ regularNormalCone_subset_normalCone ?_
  refine ⟨rfl, fun ε _ ↦ eventually_nhdsWithin_of_forall fun x hx ↦ ?_⟩
  rw [mem_singleton_iff.1 hx]
  simp

end Locality

section Def

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Def. 3.17, (3.42), of [Mordukhovich 2018] (second-order subdifferential): for `φ : E → EReal`
and `v₀ ∈ ∂φ(x₀)`, `∂²φ(x₀, v₀)(u) = (D*∂φ)(x₀, v₀)(u)`, the coderivative of the subgradient
mapping `∂φ : E ⇉ E*`. The direction `u : E` enters through the canonical embedding into the
bidual (see the module docstring); in finite dimensions this covers every bidual direction. -/
def secondOrderSubdiff (φ : E → EReal) (x₀ : E) (v₀ : StrongDual ℝ E) (u : E) :
    Set (StrongDual ℝ E) :=
  coderiv (subdiff φ) x₀ v₀ (NormedSpace.inclusionInDoubleDual ℝ E u)

/-- Unfolding Def. 3.17: `m ∈ ∂²φ(x₀, v₀)(u)` iff `(m, -u) ∈ N((x₀, v₀); gph ∂φ)`. -/
theorem mem_secondOrderSubdiff_iff {φ : E → EReal} {x₀ u : E} {v₀ m : StrongDual ℝ E} :
    m ∈ secondOrderSubdiff φ x₀ v₀ u ↔
      m.coprod (-NormedSpace.inclusionInDoubleDual ℝ E u) ∈
        normalCone (graph (subdiff φ)) (x₀, v₀) :=
  Iff.rfl

/-- In finite dimensions every coderivative value `D*∂φ(x₀, v₀)(z)`, `z ∈ E**`, is a value of
the second-order subdifferential: the encoding of `Def. 3.17` by `u : E` loses nothing. -/
theorem exists_coderiv_subdiff_eq_secondOrderSubdiff [FiniteDimensional ℝ E] (φ : E → EReal)
    (x₀ : E) (v₀ : StrongDual ℝ E) (z : StrongDual ℝ (StrongDual ℝ E)) :
    ∃ u : E, NormedSpace.inclusionInDoubleDual ℝ E u = z ∧
      coderiv (subdiff φ) x₀ v₀ z = secondOrderSubdiff φ x₀ v₀ u := by
  obtain ⟨u, rfl⟩ := inclusionInDoubleDual_surjective z
  exact ⟨u, rfl, rfl⟩

/-- (3.43) of [Mordukhovich 2018] (second-order subdifferentials of `C²` functions, from
Prop. 1.12 and Cor. 1.24): if `φ` is twice differentiable around `x₀` (`φ' x` its gradient,
`φ'' x` its Hessian) and `φ''` is continuous at `x₀`, then `∂²φ(x₀)(u) = {∇²φ(x₀) u}`. The
coderivative gives `∇²φ(x₀)* u`; the symmetry of the Hessian identifies it with
`∇²φ(x₀) u`. -/
theorem secondOrderSubdiff_of_hasFDerivAt {φ : E → ℝ} {φ' : E → StrongDual ℝ E}
    {φ'' : E → E →L[ℝ] StrongDual ℝ E} {x₀ : E} (hφ : ∀ᶠ x in 𝓝 x₀, HasFDerivAt φ (φ' x) x)
    (hφ' : ∀ᶠ x in 𝓝 x₀, HasFDerivAt φ' (φ'' x) x) (hc : ContinuousAt φ'' x₀) (u : E) :
    secondOrderSubdiff (fun x ↦ (φ x : EReal)) x₀ (φ' x₀) u = {φ'' x₀ u} := by
  have hsub : ∀ᶠ x in 𝓝 x₀, subdiff (fun x ↦ (φ x : EReal)) x = {φ' x} := by
    filter_upwards [hφ.eventually_nhds, hφ'] with x hx hx'
    exact subdiff_of_hasFDerivAt_of_continuousAt hx hx'.continuousAt
  rw [secondOrderSubdiff, coderiv_congr hsub, coderiv_of_hasFDerivAt_of_continuousAt hφ' hc]
  congr 1
  ext h
  simp only [comp_apply, NormedSpace.dual_def]
  exact second_derivative_symmetric_of_eventually hφ hφ'.self_of_nhds h u

end Def

section ChainRule

variable {F W K : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- The change of variables `((y, v), κ) ↦ (y, v ∘ ∇g(y) + κ ∘ P)` in the proof of the
second-order chain rule (3.47). -/
def chainLift (Dg : F → F →L[ℝ] W) (P : F →L[ℝ] K) :
    (F × StrongDual ℝ W) × StrongDual ℝ K → F × StrongDual ℝ F :=
  fun p ↦ (p.1.1, p.1.2.comp (Dg p.1.1) + p.2.comp P)

/-- The derivative of `chainLift` at `p`:
`((dy, dv), dκ) ↦ (dy, v ∘ ∇²g(y) dy + dv ∘ ∇g(y) + dκ ∘ P)`. -/
noncomputable def chainLiftDeriv (Dg : F → F →L[ℝ] W) (D2g : F → F →L[ℝ] F →L[ℝ] W)
    (P : F →L[ℝ] K) (p : (F × StrongDual ℝ W) × StrongDual ℝ K) :
    (F × StrongDual ℝ W) × StrongDual ℝ K →L[ℝ] F × StrongDual ℝ F :=
  ((fst ℝ F (StrongDual ℝ W)).comp (fst ℝ _ (StrongDual ℝ K))).prod
    ((((compL ℝ F W ℝ p.1.2).comp (D2g p.1.1)).coprod ((compL ℝ F W ℝ).flip (Dg p.1.1))).coprod
      ((compL ℝ F K ℝ).flip P))

/-- `chainLiftDeriv` evaluated at a point. -/
@[simp]
theorem chainLiftDeriv_apply (Dg : F → F →L[ℝ] W) (D2g : F → F →L[ℝ] F →L[ℝ] W)
    (P : F →L[ℝ] K) (p : (F × StrongDual ℝ W) × StrongDual ℝ K) (q) :
    chainLiftDeriv Dg D2g P p q =
      (q.1.1, p.1.2.comp (D2g p.1.1 q.1.1) + q.1.2.comp (Dg p.1.1) + q.2.comp P) := by
  simp [chainLiftDeriv]

/-- `chainLift` is strictly differentiable at `p` with derivative `chainLiftDeriv` as soon as
`∇g` is strictly differentiable at `p.1.1`. -/
theorem hasStrictFDerivAt_chainLift {Dg : F → F →L[ℝ] W} {D2g : F → F →L[ℝ] F →L[ℝ] W}
    (P : F →L[ℝ] K) {p : (F × StrongDual ℝ W) × StrongDual ℝ K}
    (h : HasStrictFDerivAt Dg (D2g p.1.1) p.1.1) :
    HasStrictFDerivAt (chainLift Dg P) (chainLiftDeriv Dg D2g P p) p := by
  set L₁ := (fst ℝ F (StrongDual ℝ W)).comp (fst ℝ (F × StrongDual ℝ W) (StrongDual ℝ K))
  set L₂ := (snd ℝ F (StrongDual ℝ W)).comp (fst ℝ (F × StrongDual ℝ W) (StrongDual ℝ K))
  set L₃ := ((compL ℝ F K ℝ).flip P).comp (snd ℝ (F × StrongDual ℝ W) (StrongDual ℝ K))
  have h1 : HasStrictFDerivAt (fun p : (F × StrongDual ℝ W) × StrongDual ℝ K ↦ p.1.1) L₁ p :=
    L₁.hasStrictFDerivAt
  have h2 : HasStrictFDerivAt (fun p : (F × StrongDual ℝ W) × StrongDual ℝ K ↦ p.1.2) L₂ p :=
    L₂.hasStrictFDerivAt
  have h3 : HasStrictFDerivAt (fun p : (F × StrongDual ℝ W) × StrongDual ℝ K ↦ p.2.comp P) L₃ p :=
    L₃.hasStrictFDerivAt
  have hD : HasStrictFDerivAt (fun p : (F × StrongDual ℝ W) × StrongDual ℝ K ↦ Dg p.1.1)
      ((D2g p.1.1).comp L₁) p := h.comp p h1
  refine (h1.prodMk ((h2.clm_comp hD).add h3)).congr_fderiv ?_
  ext q <;> simp [L₁, L₂, L₃]

/-- The derivative of `chainLift` is continuous at `p` if `∇g` and `∇²g` are continuous at
`p.1.1`. -/
theorem continuousAt_chainLiftDeriv {Dg : F → F →L[ℝ] W} {D2g : F → F →L[ℝ] F →L[ℝ] W}
    (P : F →L[ℝ] K) {p : (F × StrongDual ℝ W) × StrongDual ℝ K} (hDg : ContinuousAt Dg p.1.1)
    (hD2g : ContinuousAt D2g p.1.1) : ContinuousAt (chainLiftDeriv Dg D2g P) p := by
  have hfst : ContinuousAt (fun p : (F × StrongDual ℝ W) × StrongDual ℝ K ↦ p.1.1) p :=
    (continuous_fst.comp continuous_fst).continuousAt
  have hD2g' : ContinuousAt (fun p : (F × StrongDual ℝ W) × StrongDual ℝ K ↦ D2g p.1.1) p :=
    ContinuousAt.comp (g := D2g) (f := fun p : (F × StrongDual ℝ W) × StrongDual ℝ K ↦ p.1.1)
      hD2g hfst
  have hDg' : ContinuousAt (fun p : (F × StrongDual ℝ W) × StrongDual ℝ K ↦ Dg p.1.1) p :=
    ContinuousAt.comp (g := Dg) (f := fun p : (F × StrongDual ℝ W) × StrongDual ℝ K ↦ p.1.1)
      hDg hfst
  have hsnd : ContinuousAt (fun p : (F × StrongDual ℝ W) × StrongDual ℝ K ↦ p.1.2) p :=
    (continuous_snd.comp continuous_fst).continuousAt
  have ha : ContinuousAt (fun p : (F × StrongDual ℝ W) × StrongDual ℝ K ↦
      (compL ℝ F W ℝ p.1.2).comp (D2g p.1.1)) p :=
    ((compL ℝ F W ℝ).continuous.continuousAt.comp hsnd).clm_comp hD2g'
  have hb : ContinuousAt (fun p : (F × StrongDual ℝ W) × StrongDual ℝ K ↦
      (compL ℝ F W ℝ).flip (Dg p.1.1)) p :=
    ((compL ℝ F W ℝ).flip).continuous.continuousAt.comp hDg'
  have hab : ContinuousAt (fun p : (F × StrongDual ℝ W) × StrongDual ℝ K ↦
      ((compL ℝ F W ℝ p.1.2).comp (D2g p.1.1)).coprod ((compL ℝ F W ℝ).flip (Dg p.1.1))) p :=
    ((coprodEquivL ℝ).continuous.continuousAt.comp (ha.prodMk hb)).congr
      (Eventually.of_forall fun q ↦ by ext <;> simp)
  have hP : ContinuousAt (fun _ : (F × StrongDual ℝ W) × StrongDual ℝ K ↦
      (compL ℝ F K ℝ).flip P) p := continuousAt_const
  have habc : ContinuousAt (fun p : (F × StrongDual ℝ W) × StrongDual ℝ K ↦
      (((compL ℝ F W ℝ p.1.2).comp (D2g p.1.1)).coprod
        ((compL ℝ F W ℝ).flip (Dg p.1.1))).coprod ((compL ℝ F K ℝ).flip P)) p :=
    ((coprodEquivL ℝ).continuous.continuousAt.comp (hab.prodMk hP)).congr
      (Eventually.of_forall fun q ↦ by ext <;> simp)
  have hc : ContinuousAt (fun _ : (F × StrongDual ℝ W) × StrongDual ℝ K ↦
      (fst ℝ F (StrongDual ℝ W)).comp (fst ℝ (F × StrongDual ℝ W) (StrongDual ℝ K))) p :=
    continuousAt_const
  exact ((prodL ℝ).continuous.continuousAt.comp (hc.prodMk habc)).congr
    (Eventually.of_forall fun q ↦ by ext <;> simp [chainLiftDeriv])

/-- If `e = A × P` is a linear isomorphism `F ≃ W × K`, then `(v, κ) ↦ v ∘ A + κ ∘ P` is
injective. -/
theorem eq_zero_of_comp_add_comp_eq_zero {e : F ≃L[ℝ] W × K} {A : F →L[ℝ] W} {P : F →L[ℝ] K}
    (he : ∀ x, e x = (A x, P x)) {v : StrongDual ℝ W} {κ : StrongDual ℝ K}
    (h : v.comp A + κ.comp P = 0) : v = 0 ∧ κ = 0 := by
  have hc : ∀ z : W × K, v z.1 + κ z.2 = 0 := by
    intro z
    have hz := congrArg (fun ℓ : StrongDual ℝ F ↦ ℓ (e.symm z)) h
    have hez : (A (e.symm z), P (e.symm z)) = z := by rw [← he, e.apply_symm_apply]
    simp only [add_apply, comp_apply, zero_apply] at hz
    rwa [← hez]
  refine ⟨ext fun w ↦ ?_, ext fun k ↦ ?_⟩
  · simpa using hc (w, 0)
  · simpa using hc (0, k)

/-- The inverse of `(v, κ) ↦ v ∘ A + κ ∘ P` for `e = A × P : F ≃ W × K`:
`q ↦ (q ∘ e⁻¹ ∘ inl, q ∘ e⁻¹ ∘ inr)`. -/
theorem comp_add_comp_symm {e : F ≃L[ℝ] W × K} {A : F →L[ℝ] W} {P : F →L[ℝ] K}
    (he : ∀ x, e x = (A x, P x)) (q : StrongDual ℝ F) :
    ((q.comp (e.symm : W × K →L[ℝ] F)).comp (inl ℝ W K)).comp A +
      ((q.comp (e.symm : W × K →L[ℝ] F)).comp (inr ℝ W K)).comp P = q := by
  ext x
  simp only [add_apply, comp_apply, inl_apply, inr_apply]
  rw [← map_add, ← map_add, Prod.mk_add_mk, add_zero, zero_add, ← he]
  simp

/-- The other composition: `q ↦ (q ∘ e⁻¹ ∘ inl, q ∘ e⁻¹ ∘ inr)` is a left inverse of
`(v, κ) ↦ v ∘ A + κ ∘ P` for `e = A × P : F ≃ W × K`. -/
theorem symm_comp_add_comp {e : F ≃L[ℝ] W × K} {A : F →L[ℝ] W} {P : F →L[ℝ] K}
    (he : ∀ x, e x = (A x, P x)) (v : StrongDual ℝ W) (κ : StrongDual ℝ K) :
    ((v.comp A + κ.comp P).comp (e.symm : W × K →L[ℝ] F)).comp (inl ℝ W K) = v ∧
      ((v.comp A + κ.comp P).comp (e.symm : W × K →L[ℝ] F)).comp (inr ℝ W K) = κ := by
  have hez : ∀ z, (A (e.symm z), P (e.symm z)) = z := fun z ↦ by rw [← he, e.apply_symm_apply]
  refine ⟨ext fun w ↦ ?_, ext fun k ↦ ?_⟩
  · have := hez (w, 0)
    simp only [Prod.mk.injEq] at this
    simp [this.1, this.2]
  · have := hez (0, k)
    simp only [Prod.mk.injEq] at this
    simp [this.1, this.2]

/-- The derivative of `chainLift` at `((y₀, v₀), 0)` is invertible when `A × P : F ≃ W × K` is,
where `A = ∇g(y₀)`. -/
theorem exists_equiv_chainLiftDeriv {Dg : F → F →L[ℝ] W} {D2g : F → F →L[ℝ] F →L[ℝ] W}
    {P : F →L[ℝ] K} {y₀ : F} {e₀ : F ≃L[ℝ] W × K} (he₀ : ∀ x, e₀ x = (Dg y₀ x, P x))
    (v₀ : StrongDual ℝ W) :
    ∃ e : ((F × StrongDual ℝ W) × StrongDual ℝ K) ≃L[ℝ] F × StrongDual ℝ F,
      (e : (F × StrongDual ℝ W) × StrongDual ℝ K →L[ℝ] F × StrongDual ℝ F) =
        chainLiftDeriv Dg D2g P ((y₀, v₀), 0) := by
  set M : F →L[ℝ] StrongDual ℝ F := (compL ℝ F W ℝ (-v₀)).comp (D2g y₀)
  set J : StrongDual ℝ F →L[ℝ] StrongDual ℝ W × StrongDual ℝ K :=
    ((compL ℝ W F ℝ).flip ((e₀.symm : W × K →L[ℝ] F).comp (inl ℝ W K))).prod
      ((compL ℝ K F ℝ).flip ((e₀.symm : W × K →L[ℝ] F).comp (inr ℝ W K)))
  set r : F × StrongDual ℝ F →L[ℝ] StrongDual ℝ W × StrongDual ℝ K :=
    J.comp (M.coprod (ContinuousLinearMap.id ℝ (StrongDual ℝ F)))
  set inv : F × StrongDual ℝ F →L[ℝ] (F × StrongDual ℝ W) × StrongDual ℝ K :=
    ((fst ℝ F (StrongDual ℝ F)).prod ((fst ℝ _ _).comp r)).prod ((snd ℝ _ _).comp r)
  have hr : ∀ z : F × StrongDual ℝ F, r z =
      (((z.2 - v₀.comp (D2g y₀ z.1)).comp (e₀.symm : W × K →L[ℝ] F)).comp (inl ℝ W K),
        ((z.2 - v₀.comp (D2g y₀ z.1)).comp (e₀.symm : W × K →L[ℝ] F)).comp (inr ℝ W K)) := by
    intro z
    ext <;> simp [r, J, M, sub_eq_add_neg, add_comm]
  refine ⟨ContinuousLinearEquiv.equivOfInverse (chainLiftDeriv Dg D2g P ((y₀, v₀), 0)) inv
    (fun q ↦ ?_) (fun z ↦ ?_), rfl⟩
  · obtain ⟨⟨dy, dv⟩, dκ⟩ := q
    have h := symm_comp_add_comp he₀ dv dκ
    simp only [inv, coe_comp, Function.comp_apply, prod_apply, coe_fst', coe_snd', hr,
      chainLiftDeriv_apply, add_assoc, add_sub_cancel_left]
    rw [h.1, h.2]
  · obtain ⟨dy, dq⟩ := z
    simp only [inv, coe_comp, Function.comp_apply, prod_apply, coe_fst', coe_snd', hr,
      chainLiftDeriv_apply]
    rw [add_assoc, comp_add_comp_symm he₀, add_sub_cancel]

/-- The pull-back of `(m, -u)` along the derivative of `chainLift` at `((y₀, v₀), 0)`:
`((m - v₀ ∘ ∇²g(y₀) u, -∇g(y₀) u), -P u)` (using the symmetry of `∇²g(y₀)`). -/
theorem coprod_comp_chainLiftDeriv {Dg : F → F →L[ℝ] W} {D2g : F → F →L[ℝ] F →L[ℝ] W}
    {P : F →L[ℝ] K} {y₀ : F} (hsymm : ∀ a b, D2g y₀ a b = D2g y₀ b a) (v₀ : StrongDual ℝ W)
    (m : StrongDual ℝ F) (u : F) :
    (m.coprod (-NormedSpace.inclusionInDoubleDual ℝ F u)).comp
        (chainLiftDeriv Dg D2g P ((y₀, v₀), 0)) =
      ((m - v₀.comp (D2g y₀ u)).coprod (-NormedSpace.inclusionInDoubleDual ℝ W (Dg y₀ u))).coprod
        (-NormedSpace.inclusionInDoubleDual ℝ K (P u)) := by
  refine ContinuousLinearMap.ext fun q ↦ ?_
  obtain ⟨⟨dy, dv⟩, dκ⟩ := q
  simp only [comp_apply, chainLiftDeriv_apply, coprod_apply, neg_apply, NormedSpace.dual_def,
    add_apply, sub_apply, hsymm dy u]
  ring

end ChainRule

section ChainRuleMain

variable {F W : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- Exercise 3.78(i) of [Mordukhovich 2018], the second-order subdifferential chain rule (3.47):
let `g : F → W` be of class `C²` around `ȳ` (strict derivative `Dg y` of `g` and `D2g y` of `Dg`
at every `y` near `ȳ`, `D2g` continuous at `ȳ`) with surjective derivative `∇g(ȳ)`, and let
`q̄ = ∇g(ȳ)* v̄`. Then, for every `u`,

  `∂²(ψ ∘ g)(ȳ, q̄)(u) = ∇²⟨v̄, g⟩(ȳ) u + ∇g(ȳ)* ∂²ψ(g ȳ, v̄)(∇g(ȳ) u)`,

where `∇²⟨v̄, g⟩(ȳ) u = v̄ ∘ ∇²g(ȳ) u`. No assumption is made on `ψ`; the book's requirement
`v̄ ∈ ∂ψ(g ȳ)` (equivalently `q̄ ∈ ∂(ψ ∘ g)(ȳ)`) is not needed, both sides being empty otherwise.
The `v̄` with `q̄ = ∇g(ȳ)* v̄` is unique since `∇g(ȳ)` is onto. -/
theorem secondOrderSubdiff_comp_of_surjective {ψ : W → EReal} {g : F → W}
    {Dg : F → F →L[ℝ] W} {D2g : F → F →L[ℝ] F →L[ℝ] W} {y₀ : F}
    (hg : ∀ᶠ y in 𝓝 y₀, HasStrictFDerivAt g (Dg y) y)
    (hDg : ∀ᶠ y in 𝓝 y₀, HasStrictFDerivAt Dg (D2g y) y) (hD2c : ContinuousAt D2g y₀)
    (hA : Function.Surjective (Dg y₀)) (v₀ : StrongDual ℝ W) (u : F) :
    secondOrderSubdiff (fun y ↦ ψ (g y)) y₀ (v₀.comp (Dg y₀)) u =
      (fun m ↦ v₀.comp (D2g y₀ u) + m.comp (Dg y₀)) ''
        secondOrderSubdiff ψ (g y₀) v₀ (Dg y₀ u) := by
  have := FiniteDimensional.complete ℝ F
  have := FiniteDimensional.complete ℝ W
  obtain ⟨P, hP⟩ := Submodule.ClosedComplemented.of_finiteDimensional (Dg y₀).ker
  set e₀ := prodKerEquiv hA hP
  have he₀ : ∀ x, e₀ x = (Dg y₀ x, P x) := fun x ↦ rfl
  have hDgc : ContinuousAt Dg y₀ := hDg.self_of_nhds.continuousAt
  have hsymm : ∀ a b, D2g y₀ a b = D2g y₀ b a :=
    second_derivative_symmetric_of_eventually (hg.mono fun y hy ↦ hy.hasFDerivAt)
      hDg.self_of_nhds.hasFDerivAt
  -- `(Dg y).prod P` stays invertible near `y₀`
  have hT : Tendsto (fun y ↦ (Dg y).prod P) (𝓝 y₀) (𝓝 (e₀ : F →L[ℝ] W × (Dg y₀).ker)) :=
    have hPc : ContinuousAt (fun _ : F ↦ P) y₀ := continuousAt_const
    ((prodL ℝ).continuous.continuousAt.comp (hDgc.prodMk hPc)).tendsto
  have hinv : ∀ᶠ y in 𝓝 y₀, ∃ e : F ≃L[ℝ] W × (Dg y₀).ker, ∀ x, e x = (Dg y x, P x) := by
    filter_upwards [eventually_isUnit_symm_comp hT] with y hy
    obtain ⟨e, he⟩ := exists_equiv_of_isUnit_symm_comp hy
    exact ⟨e, fun x ↦ by rw [← ContinuousLinearEquiv.coe_coe, he]; rfl⟩
  -- first-order chain rule (Exercise 1.72) near `y₀`
  have hchain : ∀ᶠ y in 𝓝 y₀, subdiff (fun y ↦ ψ (g y)) y =
      (fun v : StrongDual ℝ W ↦ v.comp (Dg y)) '' subdiff ψ (g y) := by
    filter_upwards [hg.eventually_nhds, hDg, hinv] with y hy1 hy2 hy3
    obtain ⟨e, he⟩ := hy3
    refine subdiff_comp_of_surjective hy1 hy2.continuousAt fun w ↦ ⟨e.symm (w, 0), ?_⟩
    have := e.apply_symm_apply (w, 0)
    rw [he] at this
    exact congrArg Prod.fst this
  -- the preimage of `gph ∂(ψ ∘ g)` under `chainLift` is `gph(∂ψ ∘ g) × {0}` near `p₀`
  set p₀ : (F × StrongDual ℝ W) × StrongDual ℝ (Dg y₀).ker := ((y₀, v₀), 0)
  have hloc : chainLift Dg P ⁻¹' graph (subdiff fun y ↦ ψ (g y)) =ᶠ[𝓝 p₀]
      graph (fun y ↦ subdiff ψ (g y)) ×ˢ ({0} : Set (StrongDual ℝ (Dg y₀).ker)) := by
    have hev := ((continuous_fst.comp continuous_fst).tendsto p₀).eventually (hchain.and hinv)
    filter_upwards [hev] with p hp
    obtain ⟨hp1, e, he⟩ := hp
    obtain ⟨⟨y, v⟩, κ⟩ := p
    apply propext
    change v.comp (Dg y) + κ.comp P ∈ subdiff (fun y ↦ ψ (g y)) y ↔
      v ∈ subdiff ψ (g y) ∧ κ = 0
    simp only [Function.comp_apply] at hp1 he
    rw [hp1]
    constructor
    · rintro ⟨v', hv', heq⟩
      have h0 : (v - v').comp (Dg y) + κ.comp P = 0 := by
        ext x
        have := congrArg (fun ℓ : StrongDual ℝ F ↦ ℓ x) heq
        simp only [comp_apply, add_apply] at this
        simp only [add_apply, comp_apply, sub_apply, zero_apply]
        linarith
      obtain ⟨h1, h2⟩ := eq_zero_of_comp_add_comp_eq_zero he h0
      rw [sub_eq_zero] at h1
      exact ⟨h1 ▸ hv', h2⟩
    · rintro ⟨hv, rfl⟩
      exact ⟨v, hv, by simp⟩
  -- the change of variables is `C¹` with invertible derivative at `p₀`
  have hH : ∀ᶠ p in 𝓝 p₀, HasStrictFDerivAt (chainLift Dg P) (chainLiftDeriv Dg D2g P p) p := by
    filter_upwards [((continuous_fst.comp continuous_fst).tendsto p₀).eventually hDg] with p hp
    exact hasStrictFDerivAt_chainLift P hp
  have hDHc : ContinuousAt (chainLiftDeriv Dg D2g P) p₀ := continuousAt_chainLiftDeriv P hDgc hD2c
  obtain ⟨e, he⟩ := exists_equiv_chainLiftDeriv (D2g := D2g) he₀ v₀
  have hH0 : chainLift Dg P p₀ = (y₀, v₀.comp (Dg y₀)) := by simp [chainLift, p₀]
  ext m
  rw [mem_secondOrderSubdiff_iff, ← hH0, ← comp_mem_normalCone_preimage_iff hH hDHc he.symm,
    normalCone_congr hloc, mem_normalCone_prod_iff, normalCone_singleton, he,
    coprod_comp_chainLiftDeriv hsymm, coprod_comp_inl]
  simp only [mem_univ, and_true]
  change m - v₀.comp (D2g y₀ u) ∈ coderiv (fun y ↦ subdiff ψ (g y)) y₀ v₀ _ ↔ _
  rw [coderiv_comp_of_surjective hg hDgc hA]
  constructor
  · rintro ⟨n, hn, hmn⟩
    refine ⟨n, hn, ?_⟩
    simp only at hmn ⊢
    rw [hmn, add_sub_cancel]
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, by simp⟩

end ChainRuleMain

end VariationalAnalysis
