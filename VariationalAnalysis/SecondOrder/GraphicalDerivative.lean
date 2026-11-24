/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Analysis.Convex.Deriv
import VariationalAnalysis.SecondOrder.Basic
import VariationalAnalysis.Tangent.Contingent

/-!
# Subgradient graphical derivatives

This file follows [Mordukhovich 2024, Subsect. 1.4.1–1.4.2]: the graphical derivative
`DF(x̄, ȳ)(u) = {v | (u, v) ∈ T((x̄, ȳ); gph F)}` of a set-valued mapping [Mordukhovich 2024,
(1.39)] and its application to subgradient mappings (primal-dual second-order constructions).

## Main declarations

* `graphDeriv S x₀ y₀ u`: the graphical derivative [Mordukhovich 2024, (1.39)].
* `subgradGraphDeriv φ x₀ v₀ u`, `regularSubgradGraphDeriv φ x₀ v₀ u`: the basic and regular
  subgradient graphical derivatives [Mordukhovich 2024, Def. 1.73, (1.96)–(1.97)].

## Main results

* `contingentCone_congr`, `contingentCone_mono`: locality and monotonicity of the contingent cone.
* `map_mem_contingentCone_of_hasFDerivAt`: contingent cones push forward along maps that are
  differentiable at the point.
* `graphDeriv_of_hasFDerivAt`: [Mordukhovich 2024, (1.99)]: `Df(x̄)(u) = {∇f(x̄) u}` for `f`
  differentiable at `x̄`.
* `graphDeriv_add`: the graphical derivative sum rule [Mordukhovich 2024, (1.41)] with a summand
  differentiable at the point.
* `regularSubgradGraphDeriv_subset`: `∂̂²_D φ(x̄, v̄)(u) ⊆ ∂²_D φ(x̄, v̄)(u)`.
* `subgradGraphDeriv_of_hasFDerivAt`, `regularSubgradGraphDeriv_of_hasFDerivAt`,
  `secondOrderSubdiff_eq_subgradGraphDeriv`: [Mordukhovich 2024, Prop. 1.74, (1.98)]: for `C²`
  functions all these constructions reduce to the Hessian.
* `subgradGraphDeriv_add`, `regularSubgradGraphDeriv_add`: [Mordukhovich 2024, Prop. 1.76]
  (sum rules (1.100)).
* `convexOn_of_monotone_fderiv`: a differentiable function with monotone derivative on a convex
  set is convex there.
* `convexOn_add_sq_of_lipschitzOnWith`, `convexOn_closedBall_add_sq`: [Mordukhovich 2024,
  Lemma 1.82, (1.108)] (local convexification of `C^{1,1}` functions).
* `subgradGraphDeriv_add_sq`: [Mordukhovich 2024, Lemma 1.82, (1.109)], graphical derivative
  part.

## Remarks

Graphical derivatives are positively homogeneous (`smul_mem_graphDeriv`). In (1.100) the book
writes `∇²φ₁(x̄)* u`; the graphical derivative of `∇φ₁` gives `∇²φ₁(x̄) u` directly, without
transposition, so no symmetry of the second derivative is needed here.
-/

open Filter Topology Set Asymptotics ContinuousLinearMap

namespace VariationalAnalysis

section Contingent

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The contingent cone is monotone in the set: `Ω ⊆ Ω'` gives `T(x; Ω) ⊆ T(x; Ω')`. -/
theorem contingentCone_mono {Ω Ω' : Set X} {x : X} (h : Ω ⊆ Ω') :
    contingentCone Ω x ⊆ contingentCone Ω' x := by
  rintro w ⟨hx, xs, α, hxα, h1, h2⟩
  exact ⟨h hx, xs, α, fun k ↦ ⟨h (hxα k).1, (hxα k).2⟩, h1, h2⟩

/-- If `Ω` and `Ω'` coincide near `x`, then `T(x; Ω) ⊆ T(x; Ω')`. -/
theorem contingentCone_subset_of_eventuallyEq {Ω Ω' : Set X} {x : X} (h : Ω =ᶠ[𝓝 x] Ω') :
    contingentCone Ω x ⊆ contingentCone Ω' x := by
  rintro w ⟨hx, xs, α, hxα, h1, h2⟩
  have hx' : x ∈ Ω' := Eq.mp h.self_of_nhds hx
  exact mem_contingentCone_of_eventually hx' xs α
    ((h1.eventually h).mono fun k hk ↦ ⟨Eq.mp hk (hxα k).1, (hxα k).2⟩) h1 h2

/-- Contingent cones only depend on the set near the point. -/
theorem contingentCone_congr {Ω Ω' : Set X} {x : X} (h : Ω =ᶠ[𝓝 x] Ω') :
    contingentCone Ω x = contingentCone Ω' x :=
  subset_antisymm (contingentCone_subset_of_eventuallyEq h)
    (contingentCone_subset_of_eventuallyEq h.symm)

/-- The contingent cone to a singleton is `{0}`. -/
theorem eq_zero_of_mem_contingentCone_singleton {c w : X} (hw : w ∈ contingentCone {c} c) :
    w = 0 := by
  obtain ⟨-, xs, α, hxα, -, h2⟩ := hw
  have : (fun k ↦ α k • (xs k - c)) = fun _ ↦ 0 := by
    funext k; rw [mem_singleton_iff.1 (hxα k).1]; simp
  rw [this] at h2
  exact tendsto_nhds_unique h2 tendsto_const_nhds

/-- Contingent cones push forward along maps differentiable at the point: if `G` is
differentiable at `p` with derivative `A` and maps `Ω` into `Ω'`, then
`A T(p; Ω) ⊆ T(G p; Ω')`. -/
theorem map_mem_contingentCone_of_hasFDerivAt {G : X → Y} {A : X →L[ℝ] Y} {p : X} {q : Y}
    {Ω : Set X} {Ω' : Set Y} (hG : HasFDerivAt G A p) (hGp : G p = q)
    (hΩ : ∀ x ∈ Ω, G x ∈ Ω') {w : X} (hw : w ∈ contingentCone Ω p) :
    A w ∈ contingentCone Ω' q := by
  subst hGp
  obtain ⟨hp, x, α, hxα, hx, hlim⟩ := hw
  refine ⟨hΩ p hp, fun k ↦ G (x k), α, fun k ↦ ⟨hΩ _ (hxα k).1, (hxα k).2⟩,
    hG.continuousAt.tendsto.comp hx, ?_⟩
  have hlo : (fun k ↦ G (x k) - G p - A (x k - p)) =o[atTop] fun k ↦ x k - p :=
    hG.isLittleO.comp_tendsto hx
  have h2 : (fun k ↦ α k • (G (x k) - G p - A (x k - p))) =o[atTop]
      fun k ↦ α k • (x k - p) :=
    (isBigO_refl α atTop).smul_isLittleO hlo
  have h3 : (fun k ↦ α k • (x k - p)) =O[atTop] (fun _ ↦ (1 : ℝ)) := hlim.isBigO_one ℝ
  have h4 := (isLittleO_one_iff ℝ).1 (h2.trans_isBigO h3)
  have h5 : Tendsto (fun k ↦ A (α k • (x k - p))) atTop (𝓝 (A w)) :=
    (A.continuous.tendsto w).comp hlim
  convert h5.add h4 using 1
  · funext k
    simp only [map_smul, map_sub, smul_sub]
    abel_nf
  · simp

end Contingent

section GraphDeriv

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- [Mordukhovich 2024, (1.39)] (graphical derivative): `DS(x₀, y₀)(u)` is the set of `v` with
`(u, v) ∈ T((x₀, y₀); gph S)`. -/
def graphDeriv (S : E → Set F) (x₀ : E) (y₀ : F) (u : E) : Set F :=
  {v | (u, v) ∈ contingentCone (graph S) (x₀, y₀)}

/-- Graphical derivatives are positively homogeneous. -/
theorem smul_mem_graphDeriv {S : E → Set F} {x₀ : E} {y₀ : F} {u : E} {v : F}
    (hv : v ∈ graphDeriv S x₀ y₀ u) {t : ℝ} (ht : 0 ≤ t) : t • v ∈ graphDeriv S x₀ y₀ (t • u) :=
  smul_mem_contingentCone hv ht

/-- Graphical derivatives only depend on the mapping near the point. -/
theorem graphDeriv_congr {S T : E → Set F} {x₀ : E} (h : ∀ᶠ x in 𝓝 x₀, S x = T x) (y₀ : F)
    (u : E) : graphDeriv S x₀ y₀ u = graphDeriv T x₀ y₀ u := by
  have hg : graph S =ᶠ[𝓝 (x₀, y₀)] graph T := by
    filter_upwards [(continuous_fst.tendsto (x₀, y₀)).eventually h] with p hp
    change (p.2 ∈ S p.1) = (p.2 ∈ T p.1)
    rw [hp]
  simp only [graphDeriv, contingentCone_congr hg]

/-- Graphical derivatives are monotone in the mapping: if `S x ⊆ T x` for all `x`, then
`DS(x₀, y₀)(u) ⊆ DT(x₀, y₀)(u)`. -/
theorem graphDeriv_mono {S T : E → Set F} (h : ∀ x, S x ⊆ T x) (x₀ : E) (y₀ : F) (u : E) :
    graphDeriv S x₀ y₀ u ⊆ graphDeriv T x₀ y₀ u :=
  fun _ hv ↦ contingentCone_mono (fun p hp ↦ h p.1 hp) hv

/-- Every direction is tangent to the whole space. -/
theorem mem_contingentCone_univ (x₀ u : E) : u ∈ contingentCone (univ : Set E) x₀ := by
  refine ⟨mem_univ _, fun k ↦ x₀ + (1 / ((k : ℝ) + 1)) • u, fun k ↦ (k : ℝ) + 1,
    fun k ↦ ⟨mem_univ _, by positivity⟩, ?_, ?_⟩
  · have : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using tendsto_const_nhds.add (this.smul_const u)
  · refine tendsto_const_nhds.congr fun k ↦ ?_
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    simp [smul_smul, hk]

/-- [Mordukhovich 2024, (1.99)]: for `f` differentiable at `x₀` with derivative `A`,
`Df(x₀)(u) = {A u}`. -/
theorem graphDeriv_of_hasFDerivAt {f : E → F} {A : E →L[ℝ] F} {x₀ : E} (hf : HasFDerivAt f A x₀)
    (u : E) : graphDeriv (fun x ↦ {f x}) x₀ (f x₀) u = {A u} := by
  ext v
  constructor
  · intro hv
    have hH : HasFDerivAt (fun p : E × F ↦ p.2 - f p.1) (snd ℝ E F - A.comp (fst ℝ E F))
        (x₀, f x₀) := hasFDerivAt_snd.sub (hf.comp (x₀, f x₀) hasFDerivAt_fst)
    have := map_mem_contingentCone_of_hasFDerivAt hH (sub_self _) (Ω' := {0})
      (fun p hp ↦ by rw [mem_singleton_iff.1 hp, sub_self]; rfl) hv
    have h0 := eq_zero_of_mem_contingentCone_singleton this
    simp only [sub_apply, coe_snd', coe_comp, coe_fst', Function.comp_apply,
      sub_eq_zero] at h0
    exact h0
  · rintro rfl
    have hG : HasFDerivAt (fun x ↦ (x, f x)) ((ContinuousLinearMap.id ℝ E).prod A) x₀ :=
      (hasFDerivAt_id x₀).prodMk hf
    exact map_mem_contingentCone_of_hasFDerivAt hG rfl (fun x _ ↦ mem_singleton (f x))
      (mem_contingentCone_univ x₀ u)

/-- [Mordukhovich 2024, (1.41)] (graphical derivative sum rule with a summand differentiable at
the point): for `F₁` differentiable at `x₀` with derivative `A`,
`D(F₁ + F₂)(x₀, F₁ x₀ + y₀)(u) = A u + DF₂(x₀, y₀)(u)`. -/
theorem graphDeriv_add {F₁ : E → F} {A : E →L[ℝ] F} {F₂ : E → Set F} {x₀ : E} {y₀ : F}
    (hF : HasFDerivAt F₁ A x₀) (u : E) :
    graphDeriv (fun x ↦ (fun y ↦ F₁ x + y) '' F₂ x) x₀ (F₁ x₀ + y₀) u =
      (fun v ↦ A u + v) '' graphDeriv F₂ x₀ y₀ u := by
  set Ψ : E × F → E × F := fun p ↦ (p.1, F₁ p.1 + p.2)
  set Θ : E × F → E × F := fun p ↦ (p.1, p.2 - F₁ p.1)
  have hΨ : HasFDerivAt Ψ ((fst ℝ E F).prod (A.comp (fst ℝ E F) + snd ℝ E F)) (x₀, y₀) :=
    hasFDerivAt_fst.prodMk ((hF.comp (x₀, y₀) hasFDerivAt_fst).add hasFDerivAt_snd)
  have hΘ : HasFDerivAt Θ ((fst ℝ E F).prod (snd ℝ E F - A.comp (fst ℝ E F)))
      (x₀, F₁ x₀ + y₀) :=
    hasFDerivAt_fst.prodMk (hasFDerivAt_snd.sub (hF.comp (x₀, F₁ x₀ + y₀) hasFDerivAt_fst))
  have hΘx : Θ (x₀, F₁ x₀ + y₀) = (x₀, y₀) := by simp [Θ]
  have hΨmaps : ∀ p ∈ graph F₂, Ψ p ∈ graph fun x ↦ (fun y ↦ F₁ x + y) '' F₂ x :=
    fun p hp ↦ ⟨p.2, hp, rfl⟩
  have hΘmaps : ∀ p ∈ graph (fun x ↦ (fun y ↦ F₁ x + y) '' F₂ x), Θ p ∈ graph F₂ := by
    rintro ⟨x, y⟩ ⟨z, hz, hzy⟩
    simp only at hz hzy
    change y - F₁ x ∈ F₂ x
    rw [← hzy, add_sub_cancel_left]
    exact hz
  ext v
  constructor
  · intro hv
    have := map_mem_contingentCone_of_hasFDerivAt hΘ hΘx hΘmaps hv
    refine ⟨v - A u, ?_, by abel_nf⟩
    simpa [graphDeriv] using this
  · rintro ⟨w, hw, rfl⟩
    have := map_mem_contingentCone_of_hasFDerivAt hΨ rfl hΨmaps hw
    simpa [graphDeriv] using this

end GraphDeriv

section Subgradient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- [Mordukhovich 2024, Def. 1.73(i), (1.96)] (subgradient graphical derivative):
`∂²_D φ(x₀, v₀)(u) = (D∂φ)(x₀, v₀)(u)`. -/
def subgradGraphDeriv (φ : E → EReal) (x₀ : E) (v₀ : StrongDual ℝ E) (u : E) :
    Set (StrongDual ℝ E) :=
  graphDeriv (subdiff φ) x₀ v₀ u

/-- [Mordukhovich 2024, Def. 1.73(ii), (1.97)] (regular subgradient graphical derivative):
`∂̂²_D φ(x₀, v₀)(u) = (D∂̂φ)(x₀, v₀)(u)`. -/
def regularSubgradGraphDeriv (φ : E → EReal) (x₀ : E) (v₀ : StrongDual ℝ E) (u : E) :
    Set (StrongDual ℝ E) :=
  graphDeriv (regularSubdiff φ) x₀ v₀ u

/-- [Mordukhovich 2024, p. 57]: `∂̂²_D φ(x₀, v₀)(u) ⊆ ∂²_D φ(x₀, v₀)(u)`. -/
theorem regularSubgradGraphDeriv_subset {φ : E → EReal} {x₀ u : E} {v₀ : StrongDual ℝ E} :
    regularSubgradGraphDeriv φ x₀ v₀ u ⊆ subgradGraphDeriv φ x₀ v₀ u :=
  graphDeriv_mono (fun _ ↦ regularSubdiff_subset_subdiff) x₀ v₀ u

/-- [Mordukhovich 2024, Prop. 1.74], basic part: if `φ` is of class `C¹` around `x₀` and `∇φ` is
differentiable at `x₀`, then `∂²_D φ(x₀)(u) = {∇²φ(x₀) u}`. -/
theorem subgradGraphDeriv_of_hasFDerivAt {φ : E → ℝ} {φ' : E → StrongDual ℝ E}
    {φ'' : E →L[ℝ] StrongDual ℝ E} {x₀ : E} (hφ : ∀ᶠ x in 𝓝 x₀, HasFDerivAt φ (φ' x) x)
    (hc : ∀ᶠ x in 𝓝 x₀, ContinuousAt φ' x) (hφ' : HasFDerivAt φ' φ'' x₀) (u : E) :
    subgradGraphDeriv (fun x ↦ (φ x : EReal)) x₀ (φ' x₀) u = {φ'' u} := by
  rw [subgradGraphDeriv, graphDeriv_congr (eventually_subdiff_eq_singleton hφ hc),
    graphDeriv_of_hasFDerivAt hφ']

/-- [Mordukhovich 2024, Prop. 1.74], regular part: if `φ` is differentiable around `x₀` and `∇φ`
is differentiable at `x₀`, then `∂̂²_D φ(x₀)(u) = {∇²φ(x₀) u}`. -/
theorem regularSubgradGraphDeriv_of_hasFDerivAt {φ : E → ℝ} {φ' : E → StrongDual ℝ E}
    {φ'' : E →L[ℝ] StrongDual ℝ E} {x₀ : E} (hφ : ∀ᶠ x in 𝓝 x₀, HasFDerivAt φ (φ' x) x)
    (hφ' : HasFDerivAt φ' φ'' x₀) (u : E) :
    regularSubgradGraphDeriv (fun x ↦ (φ x : EReal)) x₀ (φ' x₀) u = {φ'' u} := by
  have h : ∀ᶠ x in 𝓝 x₀, regularSubdiff (fun x ↦ (φ x : EReal)) x = {φ' x} :=
    hφ.mono fun x hx ↦ regularSubdiff_of_hasFDerivAt hx
  rw [regularSubgradGraphDeriv, graphDeriv_congr h, graphDeriv_of_hasFDerivAt hφ']

/-- [Mordukhovich 2024, Prop. 1.74, (1.98)]: for `φ` of class `C²` around `x₀`,
`∂̂²_D φ(x₀)(u) = ∂²_D φ(x₀)(u) = ∂²φ(x₀)(u) = {∇²φ(x₀) u}`. -/
theorem secondOrderSubdiff_eq_subgradGraphDeriv {φ : E → ℝ} {φ' : E → StrongDual ℝ E}
    {φ'' : E → E →L[ℝ] StrongDual ℝ E} {x₀ : E} (hφ : ∀ᶠ x in 𝓝 x₀, HasFDerivAt φ (φ' x) x)
    (hφ' : ∀ᶠ x in 𝓝 x₀, HasFDerivAt φ' (φ'' x) x) (hc : ContinuousAt φ'' x₀) (u : E) :
    regularSubgradGraphDeriv (fun x ↦ (φ x : EReal)) x₀ (φ' x₀) u =
        subgradGraphDeriv (fun x ↦ (φ x : EReal)) x₀ (φ' x₀) u ∧
      subgradGraphDeriv (fun x ↦ (φ x : EReal)) x₀ (φ' x₀) u =
        secondOrderSubdiff (fun x ↦ (φ x : EReal)) x₀ (φ' x₀) u ∧
      secondOrderSubdiff (fun x ↦ (φ x : EReal)) x₀ (φ' x₀) u = {φ'' x₀ u} := by
  have h2 := secondOrderSubdiff_of_hasFDerivAt hφ hφ' hc u
  have h1 := subgradGraphDeriv_of_hasFDerivAt hφ (hφ'.mono fun x hx ↦ hx.continuousAt)
    hφ'.self_of_nhds u
  have h0 := regularSubgradGraphDeriv_of_hasFDerivAt hφ hφ'.self_of_nhds u
  exact ⟨h0.trans h1.symm, h1.trans h2.symm, h2⟩

/-- [Mordukhovich 2024, Prop. 1.76, (1.100)] (sum rule for subgradient graphical derivatives):
if `f` is of class `C¹` around `x₀` and `∇f` is differentiable at `x₀`, then
`∂²_D(φ + f)(x₀, v₀)(u) = ∇²f(x₀) u + ∂²_D φ(x₀, v₀ - ∇f(x₀))(u)`. -/
theorem subgradGraphDeriv_add {φ : E → EReal} {f : E → ℝ} {f' : E → StrongDual ℝ E}
    {f'' : E →L[ℝ] StrongDual ℝ E} {x₀ : E} (hf : ∀ᶠ x in 𝓝 x₀, HasFDerivAt f (f' x) x)
    (hc : ∀ᶠ x in 𝓝 x₀, ContinuousAt f' x) (hf' : HasFDerivAt f' f'' x₀)
    (v₀ : StrongDual ℝ E) (u : E) :
    subgradGraphDeriv (fun x ↦ φ x + f x) x₀ v₀ u =
      (fun m ↦ f'' u + m) '' subgradGraphDeriv φ x₀ (v₀ - f' x₀) u := by
  have h := graphDeriv_add (F₂ := subdiff φ) (y₀ := v₀ - f' x₀) hf' u
  rw [add_sub_cancel] at h
  rw [subgradGraphDeriv, graphDeriv_congr (eventually_subdiff_add_eq hf hc), h]
  rfl

/-- [Mordukhovich 2024, Prop. 1.76, (1.100)] (sum rule for regular subgradient graphical
derivatives): if `f` is differentiable around `x₀` and `∇f` is differentiable at `x₀`, then
`∂̂²_D(φ + f)(x₀, v₀)(u) = ∇²f(x₀) u + ∂̂²_D φ(x₀, v₀ - ∇f(x₀))(u)`. -/
theorem regularSubgradGraphDeriv_add {φ : E → EReal} {f : E → ℝ} {f' : E → StrongDual ℝ E}
    {f'' : E →L[ℝ] StrongDual ℝ E} {x₀ : E} (hf : ∀ᶠ x in 𝓝 x₀, HasFDerivAt f (f' x) x)
    (hf' : HasFDerivAt f' f'' x₀) (v₀ : StrongDual ℝ E) (u : E) :
    regularSubgradGraphDeriv (fun x ↦ φ x + f x) x₀ v₀ u =
      (fun m ↦ f'' u + m) '' regularSubgradGraphDeriv φ x₀ (v₀ - f' x₀) u := by
  have hsub : ∀ᶠ x in 𝓝 x₀, regularSubdiff (fun x ↦ φ x + f x) x =
      (fun y ↦ f' x + y) '' regularSubdiff φ x := by
    filter_upwards [hf] with x hx
    ext v
    rw [mem_regularSubdiff_add_iff hx]
    constructor
    · intro h; exact ⟨_, h, by abel_nf⟩
    · rintro ⟨w, hw, rfl⟩; simpa using hw
  have h := graphDeriv_add (F₂ := regularSubdiff φ) (y₀ := v₀ - f' x₀) hf' u
  rw [add_sub_cancel] at h
  rw [regularSubgradGraphDeriv, graphDeriv_congr hsub, h]
  rfl

end Subgradient

section Convexification

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- First-order inequality from monotonicity of the derivative: if `ψ` is differentiable on a
convex set `U` with `⟨∇ψ(x) - ∇ψ(y), x - y⟩ ≥ 0` on `U`, then
`ψ(x) + ⟨∇ψ(x), y - x⟩ ≤ ψ(y)` for `x, y ∈ U`. -/
theorem add_apply_sub_le_of_monotone {U : Set E} (hU : Convex ℝ U) {ψ : E → ℝ}
    {ψ' : E → StrongDual ℝ E} (hψ : ∀ x ∈ U, HasFDerivAt ψ (ψ' x) x)
    (hmono : ∀ x ∈ U, ∀ y ∈ U, 0 ≤ (ψ' x - ψ' y) (x - y)) {x y : E} (hx : x ∈ U)
    (hy : y ∈ U) : ψ x + ψ' x (y - x) ≤ ψ y := by
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) ∈ U := fun t ht ↦
    hU.add_smul_sub_mem hx hy ht
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t ↦ ψ (x + t • (y - x)) - t * ψ' x (y - x))
      (ψ' (x + t • (y - x)) (y - x) - ψ' x (y - x)) t := by
    intro t ht
    have hl : HasDerivAt (fun t : ℝ ↦ x + t • (y - x)) (y - x) t := by
      simpa using ((hasDerivAt_id t).smul_const (y - x)).const_add x
    exact ((hψ _ (hmem t ht)).comp_hasDerivAt t hl).sub (hasDerivAt_mul_const (ψ' x (y - x)))
  have hmon : MonotoneOn (fun t ↦ ψ (x + t • (y - x)) - t * ψ' x (y - x)) (Icc 0 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (fun t ht ↦ (hderiv t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (hderiv t (interior_subset ht)).hasDerivWithinAt) fun t ht ↦ ?_
    rw [interior_Icc] at ht
    have h := hmono _ (hmem t (Ioo_subset_Icc_self ht)) x hx
    rw [add_sub_cancel_left, map_smul, smul_eq_mul] at h
    rw [← sub_apply]
    exact (mul_nonneg_iff_of_pos_left ht.1).1 h
  have h01 := hmon ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp only [zero_smul, add_zero, zero_mul, sub_zero, one_smul, add_sub_cancel, one_mul] at h01
  linarith

/-- A differentiable function with monotone derivative on a convex set is convex there. -/
theorem convexOn_of_monotone_fderiv {U : Set E} (hU : Convex ℝ U) {ψ : E → ℝ}
    {ψ' : E → StrongDual ℝ E} (hψ : ∀ x ∈ U, HasFDerivAt ψ (ψ' x) x)
    (hmono : ∀ x ∈ U, ∀ y ∈ U, 0 ≤ (ψ' x - ψ' y) (x - y)) : ConvexOn ℝ U ψ := by
  refine ⟨hU, fun x hx y hy a b ha hb hab ↦ ?_⟩
  have hz := hU hx hy ha hb hab
  have h1 := add_apply_sub_le_of_monotone hU hψ hmono hz hx
  have h2 := add_apply_sub_le_of_monotone hU hψ hmono hz hy
  have h0 : a * ψ' (a • x + b • y) (x - (a • x + b • y)) +
      b * ψ' (a • x + b • y) (y - (a • x + b • y)) = 0 := by
    rw [← smul_eq_mul, ← smul_eq_mul, ← map_smul, ← map_smul, ← map_add]
    convert map_zero (ψ' (a • x + b • y)) using 2
    have hz' : a • (a • x + b • y) + b • (a • x + b • y) = a • x + b • y := by
      rw [← add_smul, hab, one_smul]
    calc a • (x - (a • x + b • y)) + b • (y - (a • x + b • y))
        = (a • x + b • y) - (a • (a • x + b • y) + b • (a • x + b • y)) := by
          rw [smul_sub, smul_sub]; abel
      _ = 0 := by rw [hz', sub_self]
  have h5 : a * ψ (a • x + b • y) + b * ψ (a • x + b • y) = ψ (a • x + b • y) := by
    rw [← add_mul, hab, one_mul]
  simp only [smul_eq_mul]
  linarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

end Convexification

section ConvexificationInner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- In an inner product space, `x ↦ (ρ/2)‖x - x₀‖²` has Fréchet derivative `ρ⟨x - x₀, ·⟩` at `x`. -/
theorem hasFDerivAt_half_mul_norm_sub_sq (ρ : ℝ) (x₀ x : E) :
    HasFDerivAt (fun x ↦ ρ / 2 * ‖x - x₀‖ ^ 2) (ρ • innerSL ℝ (x - x₀)) x := by
  refine ((((hasFDerivAt_id x).sub_const x₀).norm_sq).const_mul (ρ / 2)).congr_fderiv ?_
  ext w
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, coe_comp, coe_id',
    Function.comp_apply, id_eq, nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- [Mordukhovich 2024, Lemma 1.82, (1.108)] (local convexification of `C^{1,1}` functions), on a
convex set: if `φ` is differentiable on a convex set `U` and `∇φ` is `ℓ`-Lipschitz on `U`, then
`φ(x) + ρ/2 ‖x - x₀‖²` is convex on `U` for every `ρ ≥ ℓ`. -/
theorem convexOn_add_sq_of_lipschitzOnWith {U : Set E} (hU : Convex ℝ U) {φ : E → ℝ}
    {φ' : E → StrongDual ℝ E} {ℓ : NNReal} (hφ : ∀ x ∈ U, HasFDerivAt φ (φ' x) x)
    (hL : LipschitzOnWith ℓ φ' U) {ρ : ℝ} (hρ : (ℓ : ℝ) ≤ ρ) (x₀ : E) :
    ConvexOn ℝ U (fun x ↦ φ x + ρ / 2 * ‖x - x₀‖ ^ 2) := by
  refine convexOn_of_monotone_fderiv hU
    (fun x hx ↦ (hφ x hx).add (hasFDerivAt_half_mul_norm_sub_sq ρ x₀ x)) fun x hx y hy ↦ ?_
  have hlip : ‖φ' x - φ' y‖ ≤ ℓ * ‖x - y‖ := by
    simpa [dist_eq_norm] using hL.dist_le_mul x hx y hy
  have hop : |(φ' x - φ' y) (x - y)| ≤ ‖φ' x - φ' y‖ * ‖x - y‖ := by
    rw [← Real.norm_eq_abs]; exact le_opNorm _ _
  have hinner : inner ℝ (x - x₀) (x - y) - inner ℝ (y - x₀) (x - y) = ‖x - y‖ ^ 2 := by
    rw [← inner_sub_left, sub_sub_sub_cancel_right, real_inner_self_eq_norm_sq]
  have hexp : (φ' x + ρ • innerSL ℝ (x - x₀) - (φ' y + ρ • innerSL ℝ (y - x₀))) (x - y) =
      (φ' x - φ' y) (x - y) + ρ * ‖x - y‖ ^ 2 := by
    simp only [sub_apply, add_apply, smul_apply, innerSL_apply_apply, smul_eq_mul]
    rw [← hinner]; ring
  rw [hexp]
  have h1 := neg_abs_le ((φ' x - φ' y) (x - y))
  have h2 : ‖φ' x - φ' y‖ * ‖x - y‖ ≤ ℓ * ‖x - y‖ * ‖x - y‖ :=
    mul_le_mul_of_nonneg_right hlip (norm_nonneg _)
  have h3 : (ℓ : ℝ) * ‖x - y‖ ^ 2 ≤ ρ * ‖x - y‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hρ (by positivity)
  have h4 : (ℓ : ℝ) * ‖x - y‖ * ‖x - y‖ = ℓ * ‖x - y‖ ^ 2 := by ring
  linarith

/-- [Mordukhovich 2024, Lemma 1.82, (1.108)] (local convexification of `C^{1,1}` functions): if
`φ` is differentiable on `B_ε(x₀)` and `∇φ` is `ℓ`-Lipschitz there, then for every `r < ε` and
`ρ ≥ ℓ` the function `φ(x) + ρ/2 ‖x - x₀‖²` is convex on the closed ball `B̄_r(x₀)`. -/
theorem convexOn_closedBall_add_sq {φ : E → ℝ} {φ' : E → StrongDual ℝ E} {ℓ : NNReal} {x₀ : E}
    {ε r : ℝ} (hφ : ∀ x ∈ Metric.ball x₀ ε, HasFDerivAt φ (φ' x) x)
    (hL : LipschitzOnWith ℓ φ' (Metric.ball x₀ ε)) (hr : r < ε) {ρ : ℝ} (hρ : (ℓ : ℝ) ≤ ρ) :
    ConvexOn ℝ (Metric.closedBall x₀ r) (fun x ↦ φ x + ρ / 2 * ‖x - x₀‖ ^ 2) :=
  (convexOn_add_sq_of_lipschitzOnWith (convex_ball x₀ ε) hφ hL hρ x₀).subset
    (Metric.closedBall_subset_ball hr) (convex_closedBall x₀ r)

/-- [Mordukhovich 2024, Lemma 1.82, (1.109)], graphical derivative part: adding
`ρ/2 ‖x - x₀‖²` shifts the subgradient graphical derivative at `x₀` by `ρ I`:
`∂²_D φ_ρ(x₀, v₀)(u) = ρ⟨u, ·⟩ + ∂²_D φ(x₀, v₀)(u)`. -/
theorem subgradGraphDeriv_add_sq (φ : E → EReal) (ρ : ℝ) (x₀ : E) (v₀ : StrongDual ℝ E) (u : E) :
    subgradGraphDeriv (fun x ↦ φ x + ((ρ / 2 * ‖x - x₀‖ ^ 2 : ℝ) : EReal)) x₀ v₀ u =
      (fun m ↦ ρ • innerSL ℝ u + m) '' subgradGraphDeriv φ x₀ v₀ u := by
  have hD : HasFDerivAt (fun x ↦ ρ • innerSL ℝ (x - x₀)) (ρ • innerSL ℝ : E →L[ℝ] StrongDual ℝ E)
      x₀ := by
    have h := ((ρ • innerSL ℝ : E →L[ℝ] StrongDual ℝ E).hasFDerivAt (x := x₀)).sub_const
      ((ρ • innerSL ℝ : E →L[ℝ] StrongDual ℝ E) x₀)
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x ↦ ?_)
    simp [map_sub, smul_sub]
  have h := subgradGraphDeriv_add (φ := φ) (f' := fun x ↦ ρ • innerSL ℝ (x - x₀))
    (Filter.Eventually.of_forall fun x ↦ hasFDerivAt_half_mul_norm_sub_sq ρ x₀ x)
    (Filter.Eventually.of_forall fun _ ↦
      (by fun_prop : Continuous fun x : E ↦ ρ • innerSL ℝ (x - x₀)).continuousAt) hD v₀ u
  simpa using h

end ConvexificationInner

end VariationalAnalysis
