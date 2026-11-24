/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis.Coderivative.SecondOrder
import VariationalAnalysis.WellPosedness.Coderivative

/-!
# Coderivatives of parametric variational systems

For a base mapping `f : E × F → G` and a field `Q : F ⇉ G`, the solution map of the parametric
generalized equation `0 ∈ f(x, y) + Q(y)` [Mordukhovich 2018, (3.34)–(3.35)] is

  `S(x) = {y | 0 ∈ f(x, y) + Q(y)} = {y | -f(x, y) ∈ Q(y)}`.

Throughout, `f` is of class `C¹` around `(x̄, ȳ)` (strict derivative `Df p` at every `p` near
`(x̄, ȳ)`, `Df` continuous at `(x̄, ȳ)`), and its partial derivative `∇ₓf(x̄, ȳ) = Df(x̄, ȳ) ∘ inl`
is surjective (full rank). Partial derivatives are `∇ₓf = Df ∘ inl`, `∇ᵧf = Df ∘ inr`, and the
adjoint `∇ₓf* z*` is `z* ∘ ∇ₓf`.

As in the book, `gph S = g⁻¹(gph Q)` with `g(x, y) = (y, -f(x, y))`, whose derivative is onto
iff `∇ₓf(x̄, ȳ)` is; Exercise 1.54 (`normalCone_preimage_of_surjective_of_finiteDimensional`)
then gives the coderivative of `S`. The book assumes that `Q` has a locally closed graph; the
coderivative formulas do not need it (Exercise 1.54 holds for arbitrary sets), so no closedness
is assumed here. Nor is `(x̄, ȳ) ∈ gph S` needed: both sides of each formula are empty
otherwise.

The subdifferential systems of Props. 3.18–3.19 have `G = F*` resp. `G = W*`; directions in the
biduals `F**`, `W**` are written as `u : F`, `u : W` through the canonical embedding
`NormedSpace.inclusionInDoubleDual`, which is onto in finite dimensions (see
`Coderivative/SecondOrder` for the encoding of `∂²`).

## Main results

* `pvsSolutionMap`: the solution map (3.34) of [Mordukhovich 2018].
* `coderiv_pvsSolutionMap`, `mem_coderiv_pvsSolutionMap_iff`: Prop. 3.16, (3.38), of
  [Mordukhovich 2018]; `regularCoderiv_pvsSolutionMap`: its regular counterpart, for `f`
  strictly differentiable at `(x̄, ȳ)` (cf. Exercise 3.76(i)).
* `coderivKer_pvsSolutionMap`: Prop. 3.16, (3.39): `ker D*S(x̄, ȳ) = -D*Q(ȳ, z̄)(0)`.
* `coderiv_pvsSolutionMap_compositePotential`, `coderivKer_pvsSolutionMap_compositePotential`:
  Prop. 3.18, (3.45)–(3.46) (subdifferential PVS with composite potentials).
* `coderiv_pvsSolutionMap_compositeField`, `coderivKer_pvsSolutionMap_compositeField`:
  Prop. 3.19(i), (3.49)–(3.50) (subdifferential PVS with composite fields, full rank).
-/

open Filter Topology Set ContinuousLinearMap
open scoped Pointwise

namespace VariationalAnalysis

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

section Definition

/-- The solution map (3.34) of the parametric variational system (generalized equation) (3.35)
`0 ∈ f(x, y) + Q(y)` of [Mordukhovich 2018]: `S(x) = {y | -f(x, y) ∈ Q(y)}`. -/
def pvsSolutionMap (f : E × F → G) (Q : F → Set G) : E → Set F := fun x ↦ {y | -f (x, y) ∈ Q y}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedSpace ℝ G] in
/-- `y ∈ S(x)` iff `0 ∈ f(x, y) + Q(y)`. -/
theorem mem_pvsSolutionMap_iff {f : E × F → G} {Q : F → Set G} {x : E} {y : F} :
    y ∈ pvsSolutionMap f Q x ↔ ∃ z ∈ Q y, f (x, y) + z = 0 := by
  refine ⟨fun h ↦ ⟨_, h, add_neg_cancel _⟩, fun ⟨z, hz, h⟩ ↦ ?_⟩
  change -f (x, y) ∈ Q y
  rwa [show -f (x, y) = z from (neg_eq_of_add_eq_zero_right h)]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedSpace ℝ G] in
/-- `gph S = g⁻¹(gph Q)` for `g(x, y) = (y, -f(x, y))` (proof of [Mordukhovich 2018,
Prop. 3.16]). -/
theorem graph_pvsSolutionMap (f : E × F → G) (Q : F → Set G) :
    graph (pvsSolutionMap f Q) = (fun p : E × F ↦ (p.2, -f p)) ⁻¹' graph Q := rfl

end Definition

section Algebra

/-- Two coproducts of dual elements agree iff their components do. -/
theorem coprod_eq_coprod_iff {u u' : StrongDual ℝ E} {w w' : StrongDual ℝ F} :
    u.coprod w = u'.coprod w' ↔ u = u' ∧ w = w' := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨h1, h2⟩ ↦ h1 ▸ h2 ▸ rfl⟩
  · simpa using congrArg (fun ℓ : StrongDual ℝ (E × F) ↦ ℓ.comp (inl ℝ E F)) h
  · simpa using congrArg (fun ℓ : StrongDual ℝ (E × F) ↦ ℓ.comp (inr ℝ E F)) h

/-- The dual computation behind (3.38): for `D : E × F →L G`,
`(x*, -y*) = ℓ ∘ (snd, -D)` with `ℓ ∈ N` iff `x* = z* ∘ D ∘ inl` and
`(-y* - z* ∘ D ∘ inr, -z*) ∈ N` for some `z*`. -/
theorem coprod_mem_image_comp_pvs_iff {D : E × F →L[ℝ] G} {N : Set (StrongDual ℝ (F × G))}
    {x' : StrongDual ℝ E} {y' : StrongDual ℝ F} :
    x'.coprod (-y') ∈ (fun ℓ : StrongDual ℝ (F × G) ↦ ℓ.comp ((snd ℝ E F).prod (-D))) '' N ↔
      ∃ z' : StrongDual ℝ G, x' = z'.comp (D.comp (inl ℝ E F)) ∧
        (-y' - z'.comp (D.comp (inr ℝ E F))).coprod (-z') ∈ N := by
  have key : ∀ a : StrongDual ℝ F, ∀ b : StrongDual ℝ G,
      (a.coprod b).comp ((snd ℝ E F).prod (-D)) =
        (-(b.comp (D.comp (inl ℝ E F)))).coprod (a - b.comp (D.comp (inr ℝ E F))) := by
    intro a b
    refine ContinuousLinearMap.ext fun p ↦ ?_
    obtain ⟨x, y⟩ := p
    have hD : D (x, y) = D (x, 0) + D (0, y) := by rw [← map_add]; simp
    simp [hD]
    ring
  constructor
  · rintro ⟨ℓ, hℓ, heq⟩
    dsimp only at heq
    rw [← coprod_comp_inl_inr ℓ, key, coprod_eq_coprod_iff] at heq
    refine ⟨-(ℓ.comp (inr ℝ F G)), by rw [← heq.1]; ext; simp, ?_⟩
    have h2 : -y' - (-(ℓ.comp (inr ℝ F G))).comp (D.comp (inr ℝ E F)) = ℓ.comp (inl ℝ F G) := by
      rw [← heq.2]; ext; simp
    rw [h2, neg_neg, coprod_comp_inl_inr]
    exact hℓ
  · rintro ⟨z', rfl, hz⟩
    refine ⟨_, hz, ?_⟩
    dsimp only
    rw [key, coprod_eq_coprod_iff]
    constructor
    · ext; simp
    · ext; simp

end Algebra

section Prop316

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G]
  {f : E × F → G} {Df : E × F → E × F →L[ℝ] G} {Q : F → Set G} {x₀ : E} {y₀ : F}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G] in
/-- The derivative `(snd, -Df(x̄, ȳ))` of `g(x, y) = (y, -f(x, y))` is onto iff
`∇ₓf(x̄, ȳ)` is (proof of [Mordukhovich 2018, Prop. 3.16]); we need the "if" part. -/
theorem surjective_snd_prod_neg {D : E × F →L[ℝ] G}
    (hD : Function.Surjective (D.comp (inl ℝ E F))) :
    Function.Surjective ((snd ℝ E F).prod (-D)) := by
  rintro ⟨b, c⟩
  obtain ⟨x, hx⟩ := hD (-c - D (0, b))
  refine ⟨(x, b), ?_⟩
  have hsplit : D (x, b) = D (x, 0) + D (0, b) := by rw [← map_add]; simp
  simp only [comp_apply, inl_apply] at hx
  simp [hsplit, hx]

/-- Prop. 3.16, (3.38), of [Mordukhovich 2018] (coderivative of general PVS), pointwise form:
for `f` of class `C¹` around `(x̄, ȳ)` with `∇ₓf(x̄, ȳ)` surjective and any field `Q`,
`x* ∈ D*S(x̄, ȳ)(y*)` iff `x* = ∇ₓf(x̄, ȳ)* z*` and
`-y* - ∇ᵧf(x̄, ȳ)* z* ∈ D*Q(ȳ, z̄)(z*)`, `z̄ = -f(x̄, ȳ)`, for some `z*`. The closedness of
`gph Q` assumed in the book is not needed. -/
theorem mem_coderiv_pvsSolutionMap_iff (hf : ∀ᶠ p in 𝓝 (x₀, y₀), HasStrictFDerivAt f (Df p) p)
    (hDf : ContinuousAt Df (x₀, y₀)) (hsurj : Function.Surjective ((Df (x₀, y₀)).comp (inl ℝ E F)))
    {y' : StrongDual ℝ F} {x' : StrongDual ℝ E} :
    x' ∈ coderiv (pvsSolutionMap f Q) x₀ y₀ y' ↔
      ∃ z' : StrongDual ℝ G, x' = z'.comp ((Df (x₀, y₀)).comp (inl ℝ E F)) ∧
        -y' - z'.comp ((Df (x₀, y₀)).comp (inr ℝ E F)) ∈ coderiv Q y₀ (-f (x₀, y₀)) z' := by
  set Dg : E × F → E × F →L[ℝ] F × G := fun p ↦ (snd ℝ E F).prod (-(Df p))
  have hg : ∀ᶠ p in 𝓝 (x₀, y₀), HasStrictFDerivAt (fun p : E × F ↦ (p.2, -f p)) (Dg p) p := by
    filter_upwards [hf] with p hp
    exact (hasStrictFDerivAt_snd).prodMk hp.neg
  have hDgc : ContinuousAt Dg (x₀, y₀) := by
    have hc : ContinuousAt (fun _ : E × F ↦ snd ℝ E F) (x₀, y₀) := continuousAt_const
    exact (prodL ℝ).continuous.continuousAt.comp (hc.prodMk hDf.neg)
  simp only [coderiv, mem_ofPred_eq, graph_pvsSolutionMap]
  rw [normalCone_preimage_of_surjective_of_finiteDimensional hg hDgc
    (surjective_snd_prod_neg hsurj)]
  exact coprod_mem_image_comp_pvs_iff

/-- Prop. 3.16, (3.38), of [Mordukhovich 2018] (coderivative calculation for general PVS): for
`f` of class `C¹` around `(x̄, ȳ)` with `∇ₓf(x̄, ȳ)` surjective (full rank), any field `Q` and
`z̄ = -f(x̄, ȳ)`,

  `D*S(x̄, ȳ)(y*) = {x* | ∃ z*, x* = ∇ₓf(x̄, ȳ)* z*, -y* ∈ ∇ᵧf(x̄, ȳ)* z* + D*Q(ȳ, z̄)(z*)}`. -/
theorem coderiv_pvsSolutionMap (hf : ∀ᶠ p in 𝓝 (x₀, y₀), HasStrictFDerivAt f (Df p) p)
    (hDf : ContinuousAt Df (x₀, y₀)) (hsurj : Function.Surjective ((Df (x₀, y₀)).comp (inl ℝ E F)))
    (y' : StrongDual ℝ F) :
    coderiv (pvsSolutionMap f Q) x₀ y₀ y' =
      {x' | ∃ z' : StrongDual ℝ G, x' = z'.comp ((Df (x₀, y₀)).comp (inl ℝ E F)) ∧
        -y' ∈ (fun w ↦ z'.comp ((Df (x₀, y₀)).comp (inr ℝ E F)) + w) ''
          coderiv Q y₀ (-f (x₀, y₀)) z'} := by
  ext x'
  rw [mem_coderiv_pvsSolutionMap_iff hf hDf hsurj]
  refine exists_congr fun z' ↦ and_congr_right fun _ ↦ ⟨fun h ↦ ⟨_, h, by dsimp only; abel⟩, ?_⟩
  rintro ⟨w, hw, hwy⟩
  dsimp only at hwy
  rwa [← hwy, add_sub_cancel_left]

/-- Prop. 3.16, (3.39), of [Mordukhovich 2018]: under the assumptions of (3.38),
`ker D*S(x̄, ȳ) = -D*Q(ȳ, z̄)(0)` with `z̄ = -f(x̄, ȳ)`. -/
theorem coderivKer_pvsSolutionMap (hf : ∀ᶠ p in 𝓝 (x₀, y₀), HasStrictFDerivAt f (Df p) p)
    (hDf : ContinuousAt Df (x₀, y₀))
    (hsurj : Function.Surjective ((Df (x₀, y₀)).comp (inl ℝ E F))) :
    coderivKer (pvsSolutionMap f Q) x₀ y₀ = -coderiv Q y₀ (-f (x₀, y₀)) 0 := by
  ext y'
  rw [mem_coderivKer_iff, mem_coderiv_pvsSolutionMap_iff hf hDf hsurj, Set.mem_neg]
  constructor
  · rintro ⟨z', hz', hmem⟩
    have hz0 : z' = 0 := comp_injective_of_surjective hsurj
      (show z'.comp _ = (0 : StrongDual ℝ G).comp _ by rw [← hz', zero_comp])
    subst hz0
    simpa using hmem
  · intro h
    exact ⟨0, by simp, by simpa using h⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G] in
/-- The regular counterpart of Prop. 3.16, (3.38), of [Mordukhovich 2018] (cf. Exercise 3.76(i)):
for `f` strictly differentiable at `(x̄, ȳ)` with `∇ₓf(x̄, ȳ)` surjective,
`D̂*S(x̄, ȳ)(y*) = {x* | ∃ z*, x* = ∇ₓf(x̄, ȳ)* z*, -y* - ∇ᵧf(x̄, ȳ)* z* ∈ D̂*Q(ȳ, z̄)(z*)}`
(finite dimensions). -/
theorem regularCoderiv_pvsSolutionMap [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [FiniteDimensional ℝ G] {D : E × F →L[ℝ] G} (hf : HasStrictFDerivAt f D (x₀, y₀))
    (hsurj : Function.Surjective (D.comp (inl ℝ E F))) (y' : StrongDual ℝ F) :
    regularCoderiv (pvsSolutionMap f Q) x₀ y₀ y' =
      {x' | ∃ z' : StrongDual ℝ G, x' = z'.comp (D.comp (inl ℝ E F)) ∧
        -y' - z'.comp (D.comp (inr ℝ E F)) ∈ regularCoderiv Q y₀ (-f (x₀, y₀)) z'} := by
  have hg : HasStrictFDerivAt (fun p : E × F ↦ (p.2, -f p)) ((snd ℝ E F).prod (-D)) (x₀, y₀) :=
    (hasStrictFDerivAt_snd).prodMk hf.neg
  ext x'
  simp only [regularCoderiv, mem_ofPred_eq, graph_pvsSolutionMap]
  rw [regularNormalCone_preimage_of_surjective_of_finiteDimensional hg
    (surjective_snd_prod_neg hsurj)]
  exact coprod_mem_image_comp_pvs_iff

end Prop316

section Subdifferential

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ W] {x₀ : E} {y₀ : F}

/-- Prop. 3.19(i), (3.49), of [Mordukhovich 2018] (coderivative of subdifferential PVS with
composite fields, full rank): let `S(x) = {y | 0 ∈ f(x, y) + ∂θ(g y)}` with `f : E × F → W*` of
class `C¹` around `(x̄, ȳ)`, `∇ₓf(x̄, ȳ)` surjective, and `g : F → W` of class `C¹` around `ȳ`
with surjective derivative `∇g(ȳ)`. With `q̄ = -f(x̄, ȳ)` and `w̄ = g ȳ`,

  `D*S(x̄, ȳ)(y*) = {x* | ∃ u, x* = ∇ₓf(x̄, ȳ)* u, -y* ∈ ∇ᵧf(x̄, ȳ)* u + ∇g(ȳ)* ∂²θ(w̄, q̄)(u)}`,

where `u ∈ W ≅ W**` and `∇ₓf* u = x ↦ ⟨∇ₓf(x̄, ȳ) x, u⟩`. No assumption on `θ` is needed; the
book's closed-graph assumption on `∂θ` is not needed in case (i) either. -/
theorem coderiv_pvsSolutionMap_compositeField {f : E × F → StrongDual ℝ W}
    {Df : E × F → E × F →L[ℝ] StrongDual ℝ W} {θ : W → EReal} {g : F → W}
    {Dg : F → F →L[ℝ] W} (hf : ∀ᶠ p in 𝓝 (x₀, y₀), HasStrictFDerivAt f (Df p) p)
    (hDf : ContinuousAt Df (x₀, y₀)) (hsurj : Function.Surjective ((Df (x₀, y₀)).comp (inl ℝ E F)))
    (hg : ∀ᶠ y in 𝓝 y₀, HasStrictFDerivAt g (Dg y) y) (hDg : ContinuousAt Dg y₀)
    (hA : Function.Surjective (Dg y₀)) (y' : StrongDual ℝ F) :
    coderiv (pvsSolutionMap f fun y ↦ subdiff θ (g y)) x₀ y₀ y' =
      {x' | ∃ u : W,
        x' = (NormedSpace.inclusionInDoubleDual ℝ W u).comp ((Df (x₀, y₀)).comp (inl ℝ E F)) ∧
        -y' ∈ (fun m : StrongDual ℝ W ↦
            (NormedSpace.inclusionInDoubleDual ℝ W u).comp ((Df (x₀, y₀)).comp (inr ℝ E F)) +
              m.comp (Dg y₀)) '' secondOrderSubdiff θ (g y₀) (-f (x₀, y₀)) u} := by
  rw [coderiv_pvsSolutionMap hf hDf hsurj]
  ext x'
  simp only [mem_ofPred_eq, coderiv_comp_of_surjective hg hDg hA, image_image]
  constructor
  · rintro ⟨z', hx', hy'⟩
    obtain ⟨u, rfl⟩ := inclusionInDoubleDual_surjective z'
    exact ⟨u, hx', hy'⟩
  · rintro ⟨u, hx', hy'⟩
    exact ⟨_, hx', hy'⟩

/-- Prop. 3.19(i), (3.50), of [Mordukhovich 2018]: under the assumptions of (3.49),
`ker D*S(x̄, ȳ) = -∇g(ȳ)* ∂²θ(w̄, q̄)(0)`. -/
theorem coderivKer_pvsSolutionMap_compositeField {f : E × F → StrongDual ℝ W}
    {Df : E × F → E × F →L[ℝ] StrongDual ℝ W} {θ : W → EReal} {g : F → W}
    {Dg : F → F →L[ℝ] W} (hf : ∀ᶠ p in 𝓝 (x₀, y₀), HasStrictFDerivAt f (Df p) p)
    (hDf : ContinuousAt Df (x₀, y₀)) (hsurj : Function.Surjective ((Df (x₀, y₀)).comp (inl ℝ E F)))
    (hg : ∀ᶠ y in 𝓝 y₀, HasStrictFDerivAt g (Dg y) y) (hDg : ContinuousAt Dg y₀)
    (hA : Function.Surjective (Dg y₀)) :
    coderivKer (pvsSolutionMap f fun y ↦ subdiff θ (g y)) x₀ y₀ =
      -((fun m : StrongDual ℝ W ↦ m.comp (Dg y₀)) ''
        secondOrderSubdiff θ (g y₀) (-f (x₀, y₀)) 0) := by
  rw [coderivKer_pvsSolutionMap hf hDf hsurj, coderiv_comp_of_surjective hg hDg hA,
    secondOrderSubdiff, map_zero]

/-- Prop. 3.18, (3.45), of [Mordukhovich 2018] (coderivative of subdifferential PVS with
composite potentials): let `S(x) = {y | 0 ∈ f(x, y) + ∂(ψ ∘ g)(y)}` with `f : E × F → F*` of
class `C¹` around `(x̄, ȳ)` and `∇ₓf(x̄, ȳ)` surjective, and `g : F → W` of class `C²` around
`ȳ` with surjective derivative `∇g(ȳ)`. Let `q̄ = -f(x̄, ȳ) = ∇g(ȳ)* v̄` (such `v̄` is unique).
Then, with `w̄ = g ȳ`,

  `D*S(x̄, ȳ)(y*) = {x* | ∃ u, x* = ∇ₓf(x̄, ȳ)* u,`
    `-y* ∈ ∇ᵧf(x̄, ȳ)* u + ∇²⟨v̄, g⟩(ȳ) u + ∇g(ȳ)* ∂²ψ(w̄, v̄)(∇g(ȳ) u)}`,

where `u ∈ F ≅ F**`. It combines Prop. 3.16 with the second-order chain rule (3.47)
(`secondOrderSubdiff_comp_of_surjective`). The book's assumption `v̄ ∈ ∂ψ(w̄)` (that is,
`(x̄, ȳ) ∈ gph S`) is not needed. -/
theorem coderiv_pvsSolutionMap_compositePotential {f : E × F → StrongDual ℝ F}
    {Df : E × F → E × F →L[ℝ] StrongDual ℝ F} {ψ : W → EReal} {g : F → W}
    {Dg : F → F →L[ℝ] W} {D2g : F → F →L[ℝ] F →L[ℝ] W} {v₀ : StrongDual ℝ W}
    (hf : ∀ᶠ p in 𝓝 (x₀, y₀), HasStrictFDerivAt f (Df p) p) (hDf : ContinuousAt Df (x₀, y₀))
    (hsurj : Function.Surjective ((Df (x₀, y₀)).comp (inl ℝ E F)))
    (hg : ∀ᶠ y in 𝓝 y₀, HasStrictFDerivAt g (Dg y) y)
    (hDg : ∀ᶠ y in 𝓝 y₀, HasStrictFDerivAt Dg (D2g y) y) (hD2c : ContinuousAt D2g y₀)
    (hA : Function.Surjective (Dg y₀)) (hq : -f (x₀, y₀) = v₀.comp (Dg y₀))
    (y' : StrongDual ℝ F) :
    coderiv (pvsSolutionMap f fun y ↦ subdiff (fun y ↦ ψ (g y)) y) x₀ y₀ y' =
      {x' | ∃ u : F,
        x' = (NormedSpace.inclusionInDoubleDual ℝ F u).comp ((Df (x₀, y₀)).comp (inl ℝ E F)) ∧
        -y' ∈ (fun m : StrongDual ℝ W ↦
            (NormedSpace.inclusionInDoubleDual ℝ F u).comp ((Df (x₀, y₀)).comp (inr ℝ E F)) +
              v₀.comp (D2g y₀ u) + m.comp (Dg y₀)) ''
          secondOrderSubdiff ψ (g y₀) v₀ (Dg y₀ u)} := by
  rw [coderiv_pvsSolutionMap hf hDf hsurj]
  ext x'
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨z', hx', hy'⟩
    obtain ⟨u, rfl⟩ := inclusionInDoubleDual_surjective z'
    refine ⟨u, hx', ?_⟩
    rw [hq] at hy'
    change -y' ∈ _ '' secondOrderSubdiff (fun y ↦ ψ (g y)) y₀ (v₀.comp (Dg y₀)) u at hy'
    rw [secondOrderSubdiff_comp_of_surjective hg hDg hD2c hA, image_image] at hy'
    simpa only [add_assoc] using hy'
  · rintro ⟨u, hx', hy'⟩
    refine ⟨_, hx', ?_⟩
    rw [hq]
    change -y' ∈ _ '' secondOrderSubdiff (fun y ↦ ψ (g y)) y₀ (v₀.comp (Dg y₀)) u
    rw [secondOrderSubdiff_comp_of_surjective hg hDg hD2c hA, image_image]
    simpa only [add_assoc] using hy'

/-- Prop. 3.18, (3.46), of [Mordukhovich 2018]: under the assumptions of (3.45),
`ker D*S(x̄, ȳ) = -∇g(ȳ)* ∂²ψ(w̄, v̄)(0)`. -/
theorem coderivKer_pvsSolutionMap_compositePotential {f : E × F → StrongDual ℝ F}
    {Df : E × F → E × F →L[ℝ] StrongDual ℝ F} {ψ : W → EReal} {g : F → W}
    {Dg : F → F →L[ℝ] W} {D2g : F → F →L[ℝ] F →L[ℝ] W} {v₀ : StrongDual ℝ W}
    (hf : ∀ᶠ p in 𝓝 (x₀, y₀), HasStrictFDerivAt f (Df p) p) (hDf : ContinuousAt Df (x₀, y₀))
    (hsurj : Function.Surjective ((Df (x₀, y₀)).comp (inl ℝ E F)))
    (hg : ∀ᶠ y in 𝓝 y₀, HasStrictFDerivAt g (Dg y) y)
    (hDg : ∀ᶠ y in 𝓝 y₀, HasStrictFDerivAt Dg (D2g y) y) (hD2c : ContinuousAt D2g y₀)
    (hA : Function.Surjective (Dg y₀)) (hq : -f (x₀, y₀) = v₀.comp (Dg y₀)) :
    coderivKer (pvsSolutionMap f fun y ↦ subdiff (fun y ↦ ψ (g y)) y) x₀ y₀ =
      -((fun m : StrongDual ℝ W ↦ m.comp (Dg y₀)) '' secondOrderSubdiff ψ (g y₀) v₀ 0) := by
  rw [coderivKer_pvsSolutionMap hf hDf hsurj, hq]
  have h := secondOrderSubdiff_comp_of_surjective (ψ := ψ) hg hDg hD2c hA v₀ 0
  simp only [map_zero, comp_zero, zero_add] at h
  rw [← h, secondOrderSubdiff, map_zero]

end Subdifferential

end VariationalAnalysis
