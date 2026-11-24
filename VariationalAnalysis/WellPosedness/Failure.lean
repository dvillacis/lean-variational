/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis.WellPosedness.ProxRegular
import VariationalAnalysis.WellPosedness.Variational

/-!
# Failure of metric regularity for parametric variational systems

[Mordukhovich 2018, Subsection 3.3.3]: the solution map
`S(x) = {y | 0 ∈ f(x, y) + Q(y)}` of the parametric variational system (3.34) fails to be
metrically regular for the major classes of fields `Q` (monotone fields, subdifferentials of
convex and of continuously prox-regular potentials, composite fields). Each statement combines the
coderivative characterizations of metric regularity of PVS (Thm. 3.20, Cor. 3.21, Cor. 3.22, in
`VariationalAnalysis.WellPosedness.Variational`) with the obstruction to the Lipschitz-like
property of the field:

* Prop. 3.24 (Kenderov): a locally monotone Lipschitz-like operator is single-valued
  (`VariationalAnalysis.WellPosedness.Monotone`);
* a convex function whose subdifferential is Lipschitz-like is `C^{1,1}`, hence Gâteaux
  differentiable, near the point (`VariationalAnalysis.WellPosedness.Gateaux`);
* Lemma 3.28: the same for continuously prox-regular functions
  (`VariationalAnalysis.WellPosedness.ProxRegular`).

Throughout, as in Thm. 3.20, `f` is of class `C¹` around `(x₀, y₀)` with `∇ₓf(x₀, y₀)` onto and
all spaces are finite-dimensional; "not Gâteaux differentiable around `w₀`" is
`¬ ∃ U ∈ 𝓝 w₀, ∀ w ∈ U, ∃ v, HasGateauxDerivAt ψ v w`.

## Corrections and deviations

* **Thm. 3.25 is false as stated.** The book assumes that "there is no neighborhood of `ȳ` on
  which `Q` is entirely single-valued". With `Q y = {0, 1}` for all `y ∈ ℝ` and `f(x, y) = x`,
  `Q` is locally monotone around `(0, 0)` and single-valued on no neighborhood of `0`, but
  `S x = {y | -x ∈ Q y}` (`= ℝ` for `x ∈ {0, -1}`, `∅` otherwise) is metrically regular around
  `(0, 0)`: near `(0, 0)`, `S x ≠ ∅` iff `x = 0`, and then `S⁻¹ y ∋ 0` for all `y`. What
  Prop. 3.24 excludes is single-valuedness *around the point* `(ȳ, z̄)` of the graph
  (`SingleValuedAround Q ȳ z̄`); `not_metricallyRegularAt_pvsSolutionMap_of_locallyMonotoneAt`
  is the corrected statement. For fields with convex values the two readings agree, and
  `not_metricallyRegularAt_pvsSolutionMap_of_convex_values` keeps the wording of the book.
* The closed-graph standing assumption on `Q` (resp. `∂ψ`, `∂θ`) is the explicit hypothesis of
  local closedness of the graph at the reference point, except for convex l.s.c. potentials
  (Cor. 3.26, Cor. 3.30), where it is proved (`isClosed_graph_subdiff_of_convex`); there, as in
  the book, the convex potential is l.s.c. (standing assumption) with values in `(-∞, ∞]`.
* Cor. 3.26 and Cor. 3.30 do not use maximal monotonicity (the book's route through
  Thm. 3.25); the obstruction is the `C^{1,1}` regularity of convex functions with Lipschitz-like
  subdifferentials. The strong amenability of `ψ ∘ g` mentioned in the title of Cor. 3.30 is not
  needed either.

## Main results

* `not_metricallyRegularAt_pvsSolutionMap_of_locallyMonotoneAt`: Thm. 3.25 of
  [Mordukhovich 2018] (corrected); `not_metricallyRegularAt_pvsSolutionMap_of_convex_values`:
  Thm. 3.25 for convex-valued fields, with the book's hypothesis.
* `not_metricallyRegularAt_pvsSolutionMap_subdiff_of_convex`: Cor. 3.26.
* `not_metricallyRegularAt_pvsSolutionMap_compositePotential_of_proxRegular`: Thm. 3.29.
* `not_metricallyRegularAt_pvsSolutionMap_compositePotential_of_convex`: Cor. 3.30.
* `not_metricallyRegularAt_pvsSolutionMap_compositeField_of_proxRegular`: Thm. 3.31.
* `isClosed_graph_subdiff_of_convex`: the subdifferential of a proper l.s.c. convex function has
  a closed graph [Mordukhovich 2018, proof of Cor. 3.26].
-/

open Filter Topology Set Metric ContinuousLinearMap

namespace VariationalAnalysis

variable {E F W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup W] [NormedSpace ℝ W]

section ClosedGraph

variable {φ : W → EReal}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- [Mordukhovich 2018, proof of Cor. 3.26]: the subgradient mapping of a proper
(`φ > -∞`, `dom φ ≠ ∅`) l.s.c. convex function has a closed graph. It is the intersection over
`x ∈ dom φ` of the closed sets `{(y, v) | φ y ≤ φ x - ⟨v, x - y⟩}`. -/
theorem isClosed_graph_subdiff_of_convex (hconv : Convex ℝ (φ.Epi univ))
    (hlsc : LowerSemicontinuous φ) (hbot : ∀ y, φ y ≠ ⊥) (hdom : ∃ y, φ y ≠ ⊤) :
    IsClosed (graph (subdiff φ)) := by
  have heq : graph (subdiff φ) = ⋂ x ∈ {x | φ x ≠ ⊤},
      {p : W × StrongDual ℝ W | φ p.1 ≤ (((φ x).toReal - p.2 (x - p.1) : ℝ) : EReal)} := by
    ext ⟨y, v⟩
    rw [mem_iInter₂]
    change v ∈ subdiff φ y ↔ ∀ x, φ x ≠ ⊤ → φ y ≤ (((φ x).toReal - v (x - y) : ℝ) : EReal)
    constructor
    · intro hv x hx
      obtain ⟨r, hr, -⟩ := id hv
      have h := (mem_subdiff_of_convex hconv hr).1 hv x
      rw [hr]
      rw [← EReal.coe_toReal hx (hbot x)] at h
      rw [EReal.coe_le_coe_iff] at h ⊢
      linarith
    · intro H
      obtain ⟨x₁, hx₁⟩ := hdom
      have hy : φ y ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) (H x₁ hx₁)
      set r := (φ y).toReal
      have hr : φ y = r := (EReal.coe_toReal hy (hbot y)).symm
      refine (mem_subdiff_of_convex hconv hr).2 fun x ↦ ?_
      by_cases hx : φ x = ⊤
      · rw [hx]; exact le_top
      have h := H x hx
      rw [hr, EReal.coe_le_coe_iff] at h
      rw [← EReal.coe_toReal hx (hbot x), EReal.coe_le_coe_iff]
      linarith
  rw [heq]
  refine isClosed_biInter fun x _ ↦ ?_
  have hc : Continuous fun p : W × StrongDual ℝ W ↦
      (p.1, (((φ x).toReal - p.2 (x - p.1) : ℝ) : EReal)) :=
    continuous_fst.prodMk (continuous_coe_real_ereal.comp
      (continuous_const.sub (continuous_snd.clm_apply (continuous_const.sub continuous_fst))))
  exact hlsc.isClosed_epigraph.preimage hc

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- The graph of the subdifferential of a proper l.s.c. convex function is locally closed around
each of its points. -/
theorem locallyClosed_graph_subdiff_of_convex (hconv : Convex ℝ (φ.Epi univ))
    (hlsc : LowerSemicontinuous φ) (hbot : ∀ y, φ y ≠ ⊥) (w₀ : W) (v₀ : StrongDual ℝ W)
    (h₀ : v₀ ∈ subdiff φ w₀) :
    ∃ ρ > 0, IsClosed (graph (subdiff φ) ∩ closedBall (w₀, v₀) ρ) := by
  obtain ⟨r, hr, -⟩ := h₀
  exact ⟨1, one_pos, (isClosed_graph_subdiff_of_convex hconv hlsc hbot
    ⟨w₀, by rw [hr]; exact EReal.coe_ne_top r⟩).inter isClosed_closedBall⟩

end ClosedGraph

section Monotone

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
variable {f : E × F → StrongDual ℝ F} {Df : E × F → E × F →L[ℝ] StrongDual ℝ F}
  {Q : F → Set (StrongDual ℝ F)} {x₀ : E} {y₀ : F}

/-- Thm. 3.25 of [Mordukhovich 2018] (failure of metric regularity for PVS with monotone fields),
corrected: in the setting of Thm. 3.20 (`f` of class `C¹` around `(x₀, y₀) ∈ gph S` with
`∇ₓf(x₀, y₀)` onto, `gph Q` locally closed around `(y₀, z₀)`, `z₀ = -f(x₀, y₀)`), if `Q` is locally
monotone around `(y₀, z₀)` and not single-valued around `(y₀, z₀)`, then `S` is not metrically
regular around `(x₀, y₀)`. The book's weaker hypothesis "`Q` is single-valued on no neighborhood
of `y₀`" does not suffice (see the module docstring). -/
theorem not_metricallyRegularAt_pvsSolutionMap_of_locallyMonotoneAt
    (hf : ∀ᶠ p in 𝓝 (x₀, y₀), HasStrictFDerivAt f (Df p) p) (hDf : ContinuousAt Df (x₀, y₀))
    (hsurj : Function.Surjective ((Df (x₀, y₀)).comp (inl ℝ E F)))
    (hQ : ∃ ρ > 0, IsClosed (graph Q ∩ closedBall (y₀, -f (x₀, y₀)) ρ))
    (h₀ : y₀ ∈ pvsSolutionMap f Q x₀) (hmon : LocallyMonotoneAt Q y₀ (-f (x₀, y₀)))
    (hsv : ¬ SingleValuedAround Q y₀ (-f (x₀, y₀))) :
    ¬ MetricallyRegularAt (pvsSolutionMap f Q) x₀ y₀ := fun h ↦
  not_lipschitzLikeAt_of_locallyMonotoneAt hmon hsv
    ((metricallyRegularAt_pvsSolutionMap_iff_lipschitzLikeAt hf hDf hsurj hQ h₀).1 h)

/-- Thm. 3.25 of [Mordukhovich 2018] for fields with convex values, with the hypothesis of the
book: in the setting of Thm. 3.20, if `Q` is locally monotone around `(y₀, z₀)`,
`z₀ = -f(x₀, y₀)`, has convex values near `y₀`, and there is no neighborhood of `y₀` on which `Q`
is single-valued, then `S` is not metrically regular around `(x₀, y₀)`. -/
theorem not_metricallyRegularAt_pvsSolutionMap_of_convex_values
    (hf : ∀ᶠ p in 𝓝 (x₀, y₀), HasStrictFDerivAt f (Df p) p) (hDf : ContinuousAt Df (x₀, y₀))
    (hsurj : Function.Surjective ((Df (x₀, y₀)).comp (inl ℝ E F)))
    (hQ : ∃ ρ > 0, IsClosed (graph Q ∩ closedBall (y₀, -f (x₀, y₀)) ρ))
    (h₀ : y₀ ∈ pvsSolutionMap f Q x₀) (hmon : LocallyMonotoneAt Q y₀ (-f (x₀, y₀)))
    (hconv : ∀ᶠ y in 𝓝 y₀, Convex ℝ (Q y)) (hsv : ¬ ∃ U ∈ 𝓝 y₀, ∀ y ∈ U, ∃ z, Q y = {z}) :
    ¬ MetricallyRegularAt (pvsSolutionMap f Q) x₀ y₀ := fun h ↦
  not_lipschitzLikeAt_of_convex_values hmon h₀ hconv hsv
    ((metricallyRegularAt_pvsSolutionMap_iff_lipschitzLikeAt hf hDf hsurj hQ h₀).1 h)

/-- Cor. 3.26 of [Mordukhovich 2018] (failure of metric regularity for subdifferential PVS with
convex potentials): let `Q = ∂φ` in the setting of Thm. 3.20, with `φ : F → (-∞, ∞]` convex and
l.s.c. (the standing assumption), finite at `y₀` and not Gâteaux differentiable around `y₀`. Then
`S(x) = {y | 0 ∈ f(x, y) + ∂φ(y)}` is not metrically regular around `(x₀, y₀) ∈ gph S`. The
closed-graph property of `∂φ` is proved (`isClosed_graph_subdiff_of_convex`). -/
theorem not_metricallyRegularAt_pvsSolutionMap_subdiff_of_convex {φ : F → EReal}
    (hf : ∀ᶠ p in 𝓝 (x₀, y₀), HasStrictFDerivAt f (Df p) p) (hDf : ContinuousAt Df (x₀, y₀))
    (hsurj : Function.Surjective ((Df (x₀, y₀)).comp (inl ℝ E F)))
    (hconv : Convex ℝ (φ.Epi univ)) (hlsc : LowerSemicontinuous φ) (hbot : ∀ y, φ y ≠ ⊥)
    (h₀ : y₀ ∈ pvsSolutionMap f (subdiff φ) x₀)
    (hnd : ¬ ∃ U ∈ 𝓝 y₀, ∀ y ∈ U, ∃ v, HasGateauxDerivAt φ v y) :
    ¬ MetricallyRegularAt (pvsSolutionMap f (subdiff φ)) x₀ y₀ := fun h ↦
  not_lipschitzLikeAt_subdiff_of_convex hconv h₀ hnd
    ((metricallyRegularAt_pvsSolutionMap_iff_lipschitzLikeAt hf hDf hsurj
      (locallyClosed_graph_subdiff_of_convex hconv hlsc hbot y₀ _ h₀) h₀).1 h)

end Monotone

section Composite

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ W] {x₀ : E} {y₀ : F}

/-- Thm. 3.29 of [Mordukhovich 2018] (failure of metric regularity for subdifferential PVS with
continuously prox-regular potentials): in the setting of Cor. 3.21 (`f` of class `C¹` with
`∇ₓf(x₀, y₀)` onto, `g` of class `C²` with `∇g(y₀)` onto, `-f(x₀, y₀) = ∇g(y₀)* v₀`, `gph ∂ψ`
locally closed around `(g y₀, v₀)`), if `ψ` is continuously prox-regular at `w₀ = g y₀` for `v₀`
and not Gâteaux differentiable around `w₀`, then `S(x) = {y | 0 ∈ f(x, y) + ∂(ψ ∘ g)(y)}` is not
metrically regular around `(x₀, y₀) ∈ gph S`. -/
theorem not_metricallyRegularAt_pvsSolutionMap_compositePotential_of_proxRegular
    {f : E × F → StrongDual ℝ F} {Df : E × F → E × F →L[ℝ] StrongDual ℝ F} {ψ : W → EReal}
    {g : F → W} {Dg : F → F →L[ℝ] W} {D2g : F → F →L[ℝ] F →L[ℝ] W} {v₀ : StrongDual ℝ W}
    (hf : ∀ᶠ p in 𝓝 (x₀, y₀), HasStrictFDerivAt f (Df p) p) (hDf : ContinuousAt Df (x₀, y₀))
    (hsurj : Function.Surjective ((Df (x₀, y₀)).comp (inl ℝ E F)))
    (hg : ∀ᶠ y in 𝓝 y₀, HasStrictFDerivAt g (Dg y) y)
    (hDg : ∀ᶠ y in 𝓝 y₀, HasStrictFDerivAt Dg (D2g y) y) (hD2c : ContinuousAt D2g y₀)
    (hA : Function.Surjective (Dg y₀)) (hq : -f (x₀, y₀) = v₀.comp (Dg y₀))
    (hloc : ∃ ρ > 0, IsClosed (graph (subdiff ψ) ∩ closedBall (g y₀, v₀) ρ))
    (h₀ : y₀ ∈ pvsSolutionMap f (fun y ↦ subdiff (fun y ↦ ψ (g y)) y) x₀)
    (hψ : ContinuouslyProxRegularFor ψ (g y₀) v₀)
    (hnd : ¬ ∃ U ∈ 𝓝 (g y₀), ∀ w ∈ U, ∃ v, HasGateauxDerivAt ψ v w) :
    ¬ MetricallyRegularAt (pvsSolutionMap f fun y ↦ subdiff (fun y ↦ ψ (g y)) y) x₀ y₀ :=
  fun h ↦ not_lipschitzLikeAt_subdiff_of_continuouslyProxRegularFor hψ hnd
    ((metricallyRegularAt_pvsSolutionMap_compositePotential_iff hf hDf hsurj hg hDg hD2c hA hq
      hloc h₀).1 h)

/-- Cor. 3.30 of [Mordukhovich 2018] (failure of metric regularity for composite subdifferential
PVS with convex outer potentials): in the setting of Prop. 3.18 (`f` of class `C¹` with
`∇ₓf(x₀, y₀)` onto, `g` of class `C²` with `∇g(y₀)` onto, `-f(x₀, y₀) = ∇g(y₀)* v₀`), if
`ψ : W → (-∞, ∞]` is convex and l.s.c. (the standing assumption) and not Gâteaux differentiable
around `w₀ = g y₀`, then `S(x) = {y | 0 ∈ f(x, y) + ∂(ψ ∘ g)(y)}` is not metrically regular around
`(x₀, y₀) ∈ gph S`. The closed-graph requirement of Cor. 3.21 on `∂ψ` is proved
(`isClosed_graph_subdiff_of_convex`), and `ψ` finite at `w₀` follows from `(x₀, y₀) ∈ gph S`. -/
theorem not_metricallyRegularAt_pvsSolutionMap_compositePotential_of_convex
    {f : E × F → StrongDual ℝ F} {Df : E × F → E × F →L[ℝ] StrongDual ℝ F} {ψ : W → EReal}
    {g : F → W} {Dg : F → F →L[ℝ] W} {D2g : F → F →L[ℝ] F →L[ℝ] W} {v₀ : StrongDual ℝ W}
    (hf : ∀ᶠ p in 𝓝 (x₀, y₀), HasStrictFDerivAt f (Df p) p) (hDf : ContinuousAt Df (x₀, y₀))
    (hsurj : Function.Surjective ((Df (x₀, y₀)).comp (inl ℝ E F)))
    (hg : ∀ᶠ y in 𝓝 y₀, HasStrictFDerivAt g (Dg y) y)
    (hDg : ∀ᶠ y in 𝓝 y₀, HasStrictFDerivAt Dg (D2g y) y) (hD2c : ContinuousAt D2g y₀)
    (hA : Function.Surjective (Dg y₀)) (hq : -f (x₀, y₀) = v₀.comp (Dg y₀))
    (hconv : Convex ℝ (ψ.Epi univ)) (hlsc : LowerSemicontinuous ψ) (hbot : ∀ w, ψ w ≠ ⊥)
    (h₀ : y₀ ∈ pvsSolutionMap f (fun y ↦ subdiff (fun y ↦ ψ (g y)) y) x₀)
    (hnd : ¬ ∃ U ∈ 𝓝 (g y₀), ∀ w ∈ U, ∃ v, HasGateauxDerivAt ψ v w) :
    ¬ MetricallyRegularAt (pvsSolutionMap f fun y ↦ subdiff (fun y ↦ ψ (g y)) y) x₀ y₀ := by
  have hv₀ : v₀ ∈ subdiff ψ (g y₀) := by
    have : -f (x₀, y₀) ∈ subdiff (fun y ↦ ψ (g y)) y₀ := h₀
    rwa [hq, comp_mem_subdiff_comp_iff_of_surjective hg
      (hDg.self_of_nhds.continuousAt) hA] at this
  exact fun h ↦ not_lipschitzLikeAt_subdiff_of_convex hconv hv₀ hnd
    ((metricallyRegularAt_pvsSolutionMap_compositePotential_iff hf hDf hsurj hg hDg hD2c hA hq
      (locallyClosed_graph_subdiff_of_convex hconv hlsc hbot _ _ hv₀) h₀).1 h)

/-- Thm. 3.31 of [Mordukhovich 2018] (failure of metric regularity for PVS with composite fields
containing subdifferentials of prox-regular functions): in the setting of Cor. 3.22 (`f` of class
`C¹` with `∇ₓf(x₀, y₀)` onto, `g` of class `C¹` with `∇g(y₀)` onto, `gph ∂θ` locally closed
around `(g y₀, q₀)`, `q₀ = -f(x₀, y₀)`), if `θ` is continuously prox-regular at `w₀ = g y₀` for
`q₀` and not Gâteaux differentiable around `w₀`, then `S(x) = {y | 0 ∈ f(x, y) + ∂θ(g y)}` is not
metrically regular around `(x₀, y₀) ∈ gph S`. -/
theorem not_metricallyRegularAt_pvsSolutionMap_compositeField_of_proxRegular
    {f : E × F → StrongDual ℝ W} {Df : E × F → E × F →L[ℝ] StrongDual ℝ W} {θ : W → EReal}
    {g : F → W} {Dg : F → F →L[ℝ] W} (hf : ∀ᶠ p in 𝓝 (x₀, y₀), HasStrictFDerivAt f (Df p) p)
    (hDf : ContinuousAt Df (x₀, y₀)) (hsurj : Function.Surjective ((Df (x₀, y₀)).comp (inl ℝ E F)))
    (hg : ∀ᶠ y in 𝓝 y₀, HasStrictFDerivAt g (Dg y) y) (hDg : ContinuousAt Dg y₀)
    (hA : Function.Surjective (Dg y₀))
    (hloc : ∃ ρ > 0, IsClosed (graph (subdiff θ) ∩ closedBall (g y₀, -f (x₀, y₀)) ρ))
    (h₀ : y₀ ∈ pvsSolutionMap f (fun y ↦ subdiff θ (g y)) x₀)
    (hθ : ContinuouslyProxRegularFor θ (g y₀) (-f (x₀, y₀)))
    (hnd : ¬ ∃ U ∈ 𝓝 (g y₀), ∀ w ∈ U, ∃ v, HasGateauxDerivAt θ v w) :
    ¬ MetricallyRegularAt (pvsSolutionMap f fun y ↦ subdiff θ (g y)) x₀ y₀ := fun h ↦
  not_lipschitzLikeAt_subdiff_of_continuouslyProxRegularFor hθ hnd
    ((metricallyRegularAt_pvsSolutionMap_compositeField_iff hf hDf hsurj hg hDg hA hloc h₀).1 h)

end Composite

end VariationalAnalysis
