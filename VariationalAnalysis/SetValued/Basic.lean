/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis.Coderivative.Basic
import VariationalAnalysis.Subdifferential.Limiting

/-!
# Set-valued mappings and regularity notions

Vocabulary shared by Ch. 2–4 of [Mordukhovich 2018]: domains and inverses of set-valued maps,
inner semicontinuity and local boundedness (the two assumptions under which the calculus rules
of Ch. 2–4 are stated), and the regularity notions under which these rules hold as equalities.

## Main declarations

* `dom S`, `invMap S`: the domain `{x | S x ≠ ∅}` and the inverse `S⁻¹(y) = {x | y ∈ S x}`.
* `InnerSemicontinuousAt S x₀ y₀`: `S` is inner semicontinuous at `(x₀, y₀) ∈ gph S`
  [Mordukhovich 2018, Exercise 2.46]: every `xₖ → x₀` in `dom S` admits `yₖ ∈ S xₖ` with
  `yₖ → y₀`.
* `locallyClosed_graph_of_continuousOn`: graphs of continuous maps are locally closed.
* `LocallyBoundedAt S x₀`: `S` is locally (uniformly) bounded around `x₀`
  [Mordukhovich 2018, Subsection 1.2.1].
* `NormallyRegularAt Ω x₀`: `N(x₀; Ω) = N̂(x₀; Ω)` [Mordukhovich 2018, (1.55)].
* `GraphicallyRegularAt S x₀ y₀`: `gph S` is normally regular at `(x₀, y₀)`.
* `LowerRegularAt φ x₀`: `∂φ(x₀) = ∂̂φ(x₀)` [Mordukhovich 2018, Exercise 1.74].
* `EpiRegularAt φ x₀`: `epi φ` is normally regular at `(x₀, φ x₀)` (epigraphical regularity).
-/

open Filter Topology Set

namespace VariationalAnalysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

section SetValued

/-- The domain `dom S = {x | S x ≠ ∅}` of a set-valued mapping. -/
def dom (S : E → Set F) : Set E := {x | (S x).Nonempty}

/-- The inverse `S⁻¹ : F ⇉ E`, `S⁻¹(y) = {x | y ∈ S x}`, of a set-valued mapping. -/
def invMap (S : E → Set F) : F → Set E := fun y ↦ {x | y ∈ S x}

/-- `S` is inner semicontinuous at `(x₀, y₀) ∈ gph S` [Mordukhovich 2018, Exercise 2.46]: for
every sequence `xₖ → x₀` with `xₖ ∈ dom S` there are `yₖ ∈ S xₖ` (for large `k`) with
`yₖ → y₀`. -/
def InnerSemicontinuousAt (S : E → Set F) (x₀ : E) (y₀ : F) : Prop :=
  y₀ ∈ innerLimit (𝓝[dom S] x₀) S

/-- `S` is locally bounded around `x₀`: the values of `S` on a neighborhood of `x₀` lie in a
common bounded set [Mordukhovich 2018, Subsection 1.2.1]. -/
def LocallyBoundedAt (S : E → Set F) (x₀ : E) : Prop :=
  ∃ U ∈ 𝓝 x₀, Bornology.IsBounded (⋃ x ∈ U, S x)

variable {S : E → Set F} {x₀ : E} {y₀ : F}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- `x ∈ dom S` if and only if `S x` is nonempty. -/
@[simp] theorem mem_dom_iff {x : E} : x ∈ dom S ↔ (S x).Nonempty := Iff.rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- `x ∈ S⁻¹(y)` if and only if `y ∈ S x`. -/
@[simp] theorem mem_invMap_iff {x : E} {y : F} : x ∈ invMap S y ↔ y ∈ S x := Iff.rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- `(x, y) ∈ gph S` if and only if `y ∈ S x`. -/
theorem mem_graph_iff {x : E} {y : F} : (x, y) ∈ graph S ↔ y ∈ S x := Iff.rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- The graph of the inverse is the graph of `S` with the coordinates swapped. -/
theorem graph_invMap : graph (invMap S) = Prod.swap ⁻¹' graph S := rfl

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Local boundedness around `x₀` passes to any mapping `T` with `T x ⊆ S x` for all `x`
near `x₀`. -/
theorem LocallyBoundedAt.mono {T : E → Set F} (h : LocallyBoundedAt S x₀)
    (hT : ∀ᶠ x in 𝓝 x₀, T x ⊆ S x) : LocallyBoundedAt T x₀ := by
  obtain ⟨U, hU, hb⟩ := h
  refine ⟨U ∩ {x | T x ⊆ S x}, inter_mem hU hT, hb.subset ?_⟩
  simp only [iUnion_subset_iff]
  intro x hx y hy
  exact mem_biUnion hx.1 (hx.2 hy)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- The graph of a single-valued mapping continuous on a neighborhood of `x₀` is locally closed
around `(x₀, f x₀)`. -/
theorem locallyClosed_graph_of_continuousOn {f : E → F} {x₀ : E} {U : Set E} (hU : U ∈ 𝓝 x₀)
    (hf : ContinuousOn f U) :
    ∃ ρ > 0, IsClosed (graph (fun x ↦ ({f x} : Set F)) ∩ Metric.closedBall (x₀, f x₀) ρ) := by
  obtain ⟨ρ, hρ, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hU
  refine ⟨ρ, hρ, ?_⟩
  have hmaps : MapsTo Prod.fst (Metric.closedBall (x₀, f x₀) ρ) U := fun p hp ↦ hsub (by
    rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff] at hp
    exact Metric.mem_closedBall.2 hp.1)
  have hc : ContinuousOn (fun p : E × F ↦ (p.2, f p.1)) (Metric.closedBall (x₀, f x₀) ρ) :=
    continuous_snd.continuousOn.prodMk (hf.comp continuous_fst.continuousOn hmaps)
  have : graph (fun x ↦ ({f x} : Set F)) ∩ Metric.closedBall (x₀, f x₀) ρ =
      Metric.closedBall (x₀, f x₀) ρ ∩ (fun p : E × F ↦ (p.2, f p.1)) ⁻¹' diagonal F := by
    ext p
    simp only [graph, mem_inter_iff, mem_ofPred_eq, mem_singleton_iff, mem_preimage,
      mem_diagonal_iff]
    tauto
  rw [this]
  exact hc.preimage_isClosed_of_isClosed Metric.isClosed_closedBall isClosed_diagonal

end SetValued

section Regularity

/-- `Ω` is normally regular at `x₀` if `N(x₀; Ω) = N̂(x₀; Ω)` [Mordukhovich 2018, (1.55)]. -/
def NormallyRegularAt (Ω : Set E) (x₀ : E) : Prop := normalCone Ω x₀ = regularNormalCone Ω x₀

/-- `S` is graphically regular at `(x₀, y₀)` if `gph S` is normally regular there, i.e.
`D*S(x₀, y₀) = D̂*S(x₀, y₀)`. -/
def GraphicallyRegularAt (S : E → Set F) (x₀ : E) (y₀ : F) : Prop :=
  NormallyRegularAt (graph S) (x₀, y₀)

/-- `φ` is lower regular at `x₀` if `∂φ(x₀) = ∂̂φ(x₀)` [Mordukhovich 2018, Exercise 1.74]. -/
def LowerRegularAt (φ : E → EReal) (x₀ : E) : Prop := subdiff φ x₀ = regularSubdiff φ x₀

/-- `φ` is epigraphically regular at `x₀` (with `φ x₀ = r` finite) if `epi φ` is normally
regular at `(x₀, r)` [Mordukhovich 2018, Exercise 1.74]. -/
def EpiRegularAt (φ : E → EReal) (x₀ : E) : Prop :=
  ∃ r : ℝ, φ x₀ = r ∧ NormallyRegularAt (φ.Epi univ) (x₀, r)

/-- Convex sets are normally regular at every point. -/
theorem normallyRegularAt_of_convex {Ω : Set E} {x₀ : E} (hΩ : Convex ℝ Ω) :
    NormallyRegularAt Ω x₀ :=
  normalCone_eq_regularNormalCone_of_convex hΩ

/-- If `S` is graphically regular at `(x₀, y₀)`, then `D*S(x₀, y₀)(v) = D̂*S(x₀, y₀)(v)` for all
`v`. -/
theorem GraphicallyRegularAt.coderiv_eq {S : E → Set F} {x₀ : E} {y₀ : F}
    (h : GraphicallyRegularAt S x₀ y₀) (v : StrongDual ℝ F) :
    coderiv S x₀ y₀ v = regularCoderiv S x₀ y₀ v := by
  ext u
  simp only [coderiv, regularCoderiv, mem_ofPred_eq]
  rw [show normalCone (graph S) (x₀, y₀) = _ from h]

/-- Functions with convex epigraph are lower regular at every point. -/
theorem lowerRegularAt_of_convex {φ : E → EReal} {x₀ : E} (hconv : Convex ℝ (φ.Epi univ)) :
    LowerRegularAt φ x₀ :=
  subdiff_eq_regularSubdiff_of_convex hconv

end Regularity

end VariationalAnalysis
