/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis.Normal.Intersection

/-!
# Normals to level sets and coderivatives of implicit multifunctions

Let `R : P ⇉ Z` have a graph locally closed around `(p̄, z̄)` and satisfy the kernel condition

  `ker D*R(p̄, z̄) = {0}`, i.e. `0 ∈ D*R(p̄, z̄)(z*) ⟹ z* = 0`.

Then the level set `R⁻¹(z̄) = {p | z̄ ∈ R p}` satisfies

  `N(p̄; R⁻¹(z̄)) ⊆ ⋃_{z*} D*R(p̄, z̄)(z*)`,

with equality, and normal regularity of `R⁻¹(z̄)`, when `R` is graphically regular at `(p̄, z̄)`.
This is Cor. 3.13 of [Mordukhovich 2018] with `Θ = {z̄}` (for which the qualification condition
(3.32) is the kernel condition and the local boundedness assumption is automatic). We prove it
directly from the intersection rule (Thm. 2.16) through

  `R⁻¹(z̄) × {z̄} = gph R ∩ (P × {z̄})`:

the normals to `P × {z̄}` are the `(0, z*)` (Prop. 1.4), so the qualification condition (2.26) of
Thm. 2.16 is the kernel condition, and Prop. 1.4 reads off the normals to `R⁻¹(z̄)`.

Applied to `P = X × Y`, `z̄ = 0` and a mapping `S : X ⇉ Y` with `gph S = {(x, y) | 0 ∈ R(x, y)}`
near `(x̄, ȳ)`, this is the coderivative estimate for implicit multifunctions
[Mordukhovich 2006, Cor. 4.34]:

  `D*S(x̄, ȳ)(y*) ⊆ {x* | (x*, -y*) ∈ D*R((x̄, ȳ), 0)(z*) for some z*}`,

with equality (and graphical regularity of `S`) when `R` is graphically regular at `((x̄, ȳ), 0)`.

The kernel condition is `coderivKer R p̄ z̄ ⊆ {0}` in the notation of
`WellPosedness/Coderivative`; by the coderivative criterion [Mordukhovich 2018, Thm. 3.3(ii)] it
is equivalent to the metric regularity of `R` around `(p̄, z̄)` (for `R` with locally closed graph
in finite dimensions). This file does not use that equivalence.

## Main results

* `invMap_prod_singleton_eq`: `R⁻¹(z̄) × {z̄} = gph R ∩ (P × {z̄})`.
* `mem_normalCone_univ_prod_singleton_iff`: `N((p, z̄); P × {z̄}) = {0} × Z*` (Prop. 1.4).
* `locallyClosed_invMap`: level sets of mappings with locally closed graph are locally closed.
* `normalCone_invMap_subset`: Cor. 3.13 of [Mordukhovich 2018] for `Θ = {z̄}` (normals to level
  sets of set-valued mappings).
* `normalCone_invMap_eq`: equality and normal regularity under graphical regularity.
* `coderiv_implicit_subset`, `coderiv_implicit_eq` (and the `_of_eventually` local forms): the
  coderivative of an implicit multifunction [Mordukhovich 2006, Cor. 4.34].
* `coderiv_implicit_singleton_subset`, `coderiv_implicit_singleton_eq` (and the
  `_of_eventually` local forms): the same for single-valued implicit maps `x ↦ {s x}`, in the form
  used by the bilevel paper (Lemma `lemma:scalarization_S_gamma_subdifferential`).
* `locallyClosed_graph_singleton_of_continuousOn`, `locallyClosed_graph_singleton`: local
  closedness of graphs of continuous single-valued mappings.
* `graphicallyRegularAt_of_hasFDerivAt`, `forall_eq_zero_of_zero_mem_coderiv_of_surjective`:
  a `C¹` single-valued mapping is graphically regular, and satisfies the kernel condition when
  its derivative is surjective.
* `coderiv_implicit_smooth_eq`: the coderivative of a map `s` defined implicitly by
  `r(x, s x) = 0` with `r` of class `C¹` and `∇r(x̄, s x̄)` surjective.
-/

open Filter Topology Set Metric ContinuousLinearMap
open scoped Pointwise

namespace VariationalAnalysis

section Slice

/-! ### Normals to `P × {z̄}` -/

variable {P Z : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Z]
  [NormedSpace ℝ Z]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
private theorem regularNormalCone_singleton_self (z : Z) :
    regularNormalCone ({z} : Set Z) z = univ := by
  refine eq_univ_of_forall fun v ↦ ⟨rfl, fun ε _ ↦ ?_⟩
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [mem_singleton_iff.1 hx]
  simp

/-- Regular normals to `P × {z̄}` (Prop. 1.4 of [Mordukhovich 2018] with `N̂(p; P) = {0}` and
`N̂(z̄; {z̄}) = Z*`): `ℓ ∈ N̂((p, z̄); P × {z̄})` iff `ℓ = (0, z*)`. -/
theorem mem_regularNormalCone_univ_prod_singleton_iff {p : P} {z : Z}
    {ℓ : StrongDual ℝ (P × Z)} :
    ℓ ∈ regularNormalCone ((univ : Set P) ×ˢ {z}) (p, z) ↔ ℓ.comp (inl ℝ P Z) = 0 := by
  conv_lhs => rw [← coprod_comp_inl_inr ℓ]
  rw [coprod_mem_regularNormalCone_prod_iff,
    regularNormalCone_of_mem_interior (by simp : p ∈ interior (univ : Set P)),
    regularNormalCone_singleton_self]
  simp

/-- Limiting normals to `P × {z̄}` (Prop. 1.4 of [Mordukhovich 2018] with `N(p; P) = {0}` and
`N(z̄; {z̄}) = Z*`): `ℓ ∈ N((p, z̄); P × {z̄})` iff `ℓ = (0, z*)`. -/
theorem mem_normalCone_univ_prod_singleton_iff {p : P} {z : Z} {ℓ : StrongDual ℝ (P × Z)} :
    ℓ ∈ normalCone ((univ : Set P) ×ˢ {z}) (p, z) ↔ ℓ.comp (inl ℝ P Z) = 0 := by
  rw [mem_normalCone_prod_iff, normalCone_of_mem_interior (by simp : p ∈ interior (univ : Set P)),
    mem_singleton_iff, and_iff_left_iff_imp]
  exact fun _ ↦ regularNormalCone_subset_normalCone (by simp [regularNormalCone_singleton_self])

/-- `P × {z̄}` is normally regular at each of its points. -/
theorem normallyRegularAt_univ_prod_singleton (p : P) (z : Z) :
    NormallyRegularAt ((univ : Set P) ×ˢ {z}) (p, z) := by
  ext ℓ
  rw [mem_normalCone_univ_prod_singleton_iff, mem_regularNormalCone_univ_prod_singleton_iff]

end Slice

section LevelSet

/-! ### Normals to level sets of set-valued mappings -/

variable {P Z : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Z]
  [NormedSpace ℝ Z]
variable {R : P → Set Z} {p₀ : P} {z₀ : Z}

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- The level set `R⁻¹(z̄) = {p | z̄ ∈ R p}` times `{z̄}` is the slice `gph R ∩ (P × {z̄})`. -/
theorem invMap_prod_singleton_eq (R : P → Set Z) (z : Z) :
    invMap R z ×ˢ {z} = graph R ∩ ((univ : Set P) ×ˢ {z}) := by
  ext ⟨p, w⟩
  simp only [mem_prod, mem_invMap_iff, mem_singleton_iff, mem_inter_iff, mem_graph_iff, mem_univ,
    true_and]
  constructor <;> rintro ⟨h, rfl⟩ <;> exact ⟨h, rfl⟩

omit [NormedSpace ℝ P] [NormedSpace ℝ Z] in
/-- If `gph R` is locally closed around `(p̄, z̄)`, the level set `R⁻¹(z̄)` is locally closed
around `p̄`. -/
theorem locallyClosed_invMap (hloc : ∃ r > 0, IsClosed (graph R ∩ closedBall (p₀, z₀) r)) :
    ∃ r > 0, IsClosed (invMap R z₀ ∩ closedBall p₀ r) := by
  obtain ⟨r, hr, hcl⟩ := hloc
  refine ⟨r, hr, ?_⟩
  have : invMap R z₀ ∩ closedBall p₀ r =
      (fun p ↦ (p, z₀)) ⁻¹' (graph R ∩ closedBall (p₀, z₀) r) := by
    ext p
    simp only [mem_inter_iff, mem_invMap_iff, mem_closedBall, mem_preimage, mem_graph_iff,
      Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
  rw [this]
  exact hcl.preimage (continuous_id.prodMk continuous_const)

variable [FiniteDimensional ℝ P] [FiniteDimensional ℝ Z]

/-- Cor. 3.13 of [Mordukhovich 2018] (normals to inverse images) for `Θ = {z̄}`, i.e. normals to
level sets of set-valued mappings: if `gph R` is locally closed around `(p̄, z̄)` and the kernel
condition `ker D*R(p̄, z̄) = {0}` (the qualification condition (3.32) for `Θ = {z̄}`) holds, then

  `N(p̄; R⁻¹(z̄)) ⊆ {p* | p* ∈ D*R(p̄, z̄)(z*) for some z*}`.

For `Θ = {z̄}` the local boundedness assumption of the book is automatic, and it is not needed in
this proof, which applies Thm. 2.16 to `R⁻¹(z̄) × {z̄} = gph R ∩ (P × {z̄})`. The kernel
condition is equivalent to the metric regularity of `R` around `(p̄, z̄)` by Thm. 3.3(ii). -/
theorem normalCone_invMap_subset (hloc : ∃ r > 0, IsClosed (graph R ∩ closedBall (p₀, z₀) r))
    (hker : ∀ w : StrongDual ℝ Z, (0 : StrongDual ℝ P) ∈ coderiv R p₀ z₀ w → w = 0) :
    normalCone (invMap R z₀) p₀ ⊆ {u | ∃ w, u ∈ coderiv R p₀ z₀ w} := by
  intro u hu
  have hu' : u.coprod 0 ∈ normalCone (graph R ∩ ((univ : Set P) ×ˢ {z₀})) (p₀, z₀) := by
    rw [← invMap_prod_singleton_eq, coprod_mem_normalCone_prod_iff]
    exact ⟨hu, zero_mem_normalCone rfl⟩
  have hloc₂ : ∃ r > 0, IsClosed (((univ : Set P) ×ˢ {z₀}) ∩ closedBall (p₀, z₀) r) :=
    ⟨1, one_pos, (isClosed_univ.prod isClosed_singleton).inter isClosed_closedBall⟩
  have hqc : ∀ v ∈ normalCone (graph R) (p₀, z₀),
      -v ∈ normalCone ((univ : Set P) ×ˢ {z₀}) (p₀, z₀) → v = 0 := by
    intro v hv hv'
    rw [mem_normalCone_univ_prod_singleton_iff, neg_comp, neg_eq_zero] at hv'
    have hv0 : (0 : StrongDual ℝ P) ∈ coderiv R p₀ z₀ (-v.comp (inr ℝ P Z)) := by
      change (0 : StrongDual ℝ P).coprod (-(-v.comp (inr ℝ P Z))) ∈ normalCone (graph R) (p₀, z₀)
      rwa [neg_neg, ← hv', coprod_comp_inl_inr]
    rw [← coprod_comp_inl_inr v, hv', neg_eq_zero.1 (hker _ hv0)]
    ext <;> simp
  obtain ⟨a, ha, b, hb, hab⟩ := normalCone_inter_subset hloc hloc₂ hqc hu'
  rw [mem_normalCone_univ_prod_singleton_iff] at hb
  have hau : a.comp (inl ℝ P Z) = u := by
    have := congrArg (fun ℓ : StrongDual ℝ (P × Z) ↦ ℓ.comp (inl ℝ P Z)) hab
    simpa only [add_comp, hb, add_zero, coprod_comp_inl] using this
  refine ⟨-a.comp (inr ℝ P Z), ?_⟩
  change u.coprod (-(-a.comp (inr ℝ P Z))) ∈ normalCone (graph R) (p₀, z₀)
  rwa [neg_neg, ← hau, coprod_comp_inl_inr]

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ Z] in
/-- [Mordukhovich 2018, Cor. 3.13], the inclusion `⊇` for `Θ = {z̄}`: if `R` is graphically
regular at `(p̄, z̄)`, then every `p* ∈ D*R(p̄, z̄)(z*)` is a regular normal to `R⁻¹(z̄)` at `p̄`.
No closedness or qualification condition is needed, and the spaces are arbitrary. -/
theorem coderiv_subset_regularNormalCone_invMap (hreg : GraphicallyRegularAt R p₀ z₀) :
    {u | ∃ w, u ∈ coderiv R p₀ z₀ w} ⊆ regularNormalCone (invMap R z₀) p₀ := by
  rintro u ⟨w, hw⟩
  have h1 : u.coprod (-w) ∈ regularNormalCone (graph R) (p₀, z₀) := by
    have : u.coprod (-w) ∈ normalCone (graph R) (p₀, z₀) := hw
    rwa [show normalCone (graph R) (p₀, z₀) = regularNormalCone (graph R) (p₀, z₀) from hreg]
      at this
  have h2 : (0 : StrongDual ℝ P).coprod w ∈ regularNormalCone ((univ : Set P) ×ˢ {z₀}) (p₀, z₀) :=
    mem_regularNormalCone_univ_prod_singleton_iff.2 (coprod_comp_inl _ _)
  have h3 := regularNormalCone_add_subset_inter (Set.add_mem_add h1 h2)
  have hsum : u.coprod (-w) + (0 : StrongDual ℝ P).coprod w = u.coprod 0 := by
    ext <;> simp
  rw [hsum, ← invMap_prod_singleton_eq, coprod_mem_regularNormalCone_prod_iff] at h3
  exact h3.1

/-- Cor. 3.13 of [Mordukhovich 2018] for `Θ = {z̄}`, equality: if moreover `R` is graphically
regular at `(p̄, z̄)`, then

  `N(p̄; R⁻¹(z̄)) = {p* | p* ∈ D*R(p̄, z̄)(z*) for some z*}`

and `R⁻¹(z̄)` is normally regular at `p̄`. The book states the equality for single-valued `C¹`
mappings, which are graphically regular (`graphicallyRegularAt_of_hasFDerivAt`). -/
theorem normalCone_invMap_eq (hloc : ∃ r > 0, IsClosed (graph R ∩ closedBall (p₀, z₀) r))
    (hker : ∀ w : StrongDual ℝ Z, (0 : StrongDual ℝ P) ∈ coderiv R p₀ z₀ w → w = 0)
    (hreg : GraphicallyRegularAt R p₀ z₀) :
    normalCone (invMap R z₀) p₀ = {u | ∃ w, u ∈ coderiv R p₀ z₀ w} ∧
      NormallyRegularAt (invMap R z₀) p₀ := by
  have h1 := normalCone_invMap_subset hloc hker
  have h2 := coderiv_subset_regularNormalCone_invMap hreg
  exact ⟨subset_antisymm h1 (h2.trans regularNormalCone_subset_normalCone),
    subset_antisymm (h1.trans h2) regularNormalCone_subset_normalCone⟩

end LevelSet

section Implicit

/-! ### Coderivatives of implicit multifunctions -/

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable {S : X → Set Y} {R : X × Y → Set Z} {x₀ : X} {y₀ : Y}

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] [NormedSpace ℝ Z] in
/-- If `gph S = {(x, y) | 0 ∈ R(x, y)}` near `(x̄, ȳ)`, then `gph S` and `R⁻¹(0)` agree near
`(x̄, ȳ)`. -/
theorem graph_eventuallyEq_invMap (hgph : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ∈ S p.1 ↔ (0 : Z) ∈ R p) :
    graph S =ᶠ[𝓝 (x₀, y₀)] invMap R 0 :=
  eventuallyEq_set.2 hgph

variable [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ Z]

/-- Coderivatives of implicit multifunctions [Mordukhovich 2006, Cor. 4.34], local form: if
`gph S = {(x, y) | 0 ∈ R(x, y)}` near `(x̄, ȳ)`, `gph R` is locally closed around `((x̄, ȳ), 0)`
and `ker D*R((x̄, ȳ), 0) = {0}`, then

  `D*S(x̄, ȳ)(y*) ⊆ {x* | (x*, -y*) ∈ D*R((x̄, ȳ), 0)(z*) for some z*}`.

This is `normalCone_invMap_subset` (Cor. 3.13 of [Mordukhovich 2018] for `Θ = {0}`) applied to
`gph S`. The kernel condition is equivalent to the metric regularity of `R` around `((x̄, ȳ), 0)`
by the coderivative criterion [Mordukhovich 2018, Thm. 3.3(ii)]. -/
theorem coderiv_implicit_subset_of_eventually
    (hgph : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ∈ S p.1 ↔ (0 : Z) ∈ R p)
    (hloc : ∃ r > 0, IsClosed (graph R ∩ closedBall ((x₀, y₀), (0 : Z)) r))
    (hker : ∀ w : StrongDual ℝ Z, (0 : StrongDual ℝ (X × Y)) ∈ coderiv R (x₀, y₀) 0 w → w = 0)
    (v : StrongDual ℝ Y) :
    coderiv S x₀ y₀ v ⊆ {u | ∃ w : StrongDual ℝ Z, u.coprod (-v) ∈ coderiv R (x₀, y₀) 0 w} := by
  intro u hu
  have hu' : u.coprod (-v) ∈ normalCone (invMap R 0) (x₀, y₀) := by
    rw [← normalCone_congr (graph_eventuallyEq_invMap hgph)]
    exact hu
  exact normalCone_invMap_subset hloc hker hu'

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ Z] in
/-- [Mordukhovich 2006, Cor. 4.34], the inclusion `⊇`, local form: if
`gph S = {(x, y) | 0 ∈ R(x, y)}` near `(x̄, ȳ)` and `R` is graphically regular at
`((x̄, ȳ), 0)`, then `{x* | (x*, -y*) ∈ D*R((x̄, ȳ), 0)(z*) for some z*} ⊆ D̂*S(x̄, ȳ)(y*)`. -/
theorem subset_regularCoderiv_implicit_of_eventually
    (hgph : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ∈ S p.1 ↔ (0 : Z) ∈ R p)
    (hreg : GraphicallyRegularAt R (x₀, y₀) 0) (v : StrongDual ℝ Y) :
    {u | ∃ w : StrongDual ℝ Z, u.coprod (-v) ∈ coderiv R (x₀, y₀) 0 w} ⊆
      regularCoderiv S x₀ y₀ v := by
  rintro u ⟨w, hw⟩
  have := coderiv_subset_regularNormalCone_invMap hreg ⟨w, hw⟩
  change u.coprod (-v) ∈ regularNormalCone (graph S) (x₀, y₀)
  rwa [regularNormalCone_congr (graph_eventuallyEq_invMap hgph)]

/-- Coderivatives of implicit multifunctions [Mordukhovich 2006, Cor. 4.34], equality, local
form: under the assumptions of `coderiv_implicit_subset_of_eventually`, if moreover `R` is
graphically regular at `((x̄, ȳ), 0)`, then

  `D*S(x̄, ȳ)(y*) = {x* | (x*, -y*) ∈ D*R((x̄, ȳ), 0)(z*) for some z*}`

for every `y*`, and `S` is graphically regular at `(x̄, ȳ)`. -/
theorem coderiv_implicit_eq_of_eventually
    (hgph : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ∈ S p.1 ↔ (0 : Z) ∈ R p)
    (hloc : ∃ r > 0, IsClosed (graph R ∩ closedBall ((x₀, y₀), (0 : Z)) r))
    (hker : ∀ w : StrongDual ℝ Z, (0 : StrongDual ℝ (X × Y)) ∈ coderiv R (x₀, y₀) 0 w → w = 0)
    (hreg : GraphicallyRegularAt R (x₀, y₀) 0) :
    (∀ v : StrongDual ℝ Y,
      coderiv S x₀ y₀ v = {u | ∃ w : StrongDual ℝ Z, u.coprod (-v) ∈ coderiv R (x₀, y₀) 0 w}) ∧
      GraphicallyRegularAt S x₀ y₀ := by
  have hEq := graph_eventuallyEq_invMap hgph
  obtain ⟨-, hnr⟩ := normalCone_invMap_eq hloc hker hreg
  refine ⟨fun v ↦ subset_antisymm (coderiv_implicit_subset_of_eventually hgph hloc hker v)
    ((subset_regularCoderiv_implicit_of_eventually hgph hreg v).trans
      regularCoderiv_subset_coderiv), ?_⟩
  unfold GraphicallyRegularAt NormallyRegularAt
  rw [normalCone_congr hEq, regularNormalCone_congr hEq]
  exact hnr

/-- Coderivatives of implicit multifunctions [Mordukhovich 2006, Cor. 4.34]: if
`gph S = {(x, y) | 0 ∈ R(x, y)}`, `gph R` is locally closed around `((x̄, ȳ), 0)` and
`ker D*R((x̄, ȳ), 0) = {0}`, then
`D*S(x̄, ȳ)(y*) ⊆ {x* | (x*, -y*) ∈ D*R((x̄, ȳ), 0)(z*) for some z*}`. -/
theorem coderiv_implicit_subset (hgph : ∀ x y, y ∈ S x ↔ (0 : Z) ∈ R (x, y))
    (hloc : ∃ r > 0, IsClosed (graph R ∩ closedBall ((x₀, y₀), (0 : Z)) r))
    (hker : ∀ w : StrongDual ℝ Z, (0 : StrongDual ℝ (X × Y)) ∈ coderiv R (x₀, y₀) 0 w → w = 0)
    (v : StrongDual ℝ Y) :
    coderiv S x₀ y₀ v ⊆ {u | ∃ w : StrongDual ℝ Z, u.coprod (-v) ∈ coderiv R (x₀, y₀) 0 w} :=
  coderiv_implicit_subset_of_eventually (Eventually.of_forall fun p ↦ hgph p.1 p.2) hloc hker v

/-- Coderivatives of implicit multifunctions [Mordukhovich 2006, Cor. 4.34], equality: under the
assumptions of `coderiv_implicit_subset`, if moreover `R` is graphically regular at
`((x̄, ȳ), 0)`, then `D*S(x̄, ȳ)(y*) = {x* | (x*, -y*) ∈ D*R((x̄, ȳ), 0)(z*) for some z*}` and
`S` is graphically regular at `(x̄, ȳ)`. -/
theorem coderiv_implicit_eq (hgph : ∀ x y, y ∈ S x ↔ (0 : Z) ∈ R (x, y))
    (hloc : ∃ r > 0, IsClosed (graph R ∩ closedBall ((x₀, y₀), (0 : Z)) r))
    (hker : ∀ w : StrongDual ℝ Z, (0 : StrongDual ℝ (X × Y)) ∈ coderiv R (x₀, y₀) 0 w → w = 0)
    (hreg : GraphicallyRegularAt R (x₀, y₀) 0) :
    (∀ v : StrongDual ℝ Y,
      coderiv S x₀ y₀ v = {u | ∃ w : StrongDual ℝ Z, u.coprod (-v) ∈ coderiv R (x₀, y₀) 0 w}) ∧
      GraphicallyRegularAt S x₀ y₀ :=
  coderiv_implicit_eq_of_eventually (Eventually.of_forall fun p ↦ hgph p.1 p.2) hloc hker hreg

/-! ### Single-valued implicit maps -/

variable {s : X → Y}

/-- [Mordukhovich 2006, Cor. 4.34] for a single-valued implicit map `s`, local form (the
inclusion of Lemma `lemma:scalarization_S_gamma_subdifferential` of the bilevel paper): if
`y = s x ⟺ 0 ∈ R(x, y)` near `(x̄, s x̄)`, `gph R` is locally closed around `((x̄, s x̄), 0)` and
`ker D*R((x̄, s x̄), 0) = {0}`, then
`D*s(x̄)(y*) ⊆ {x* | (x*, -y*) ∈ D*R((x̄, s x̄), 0)(z*) for some z*}`. -/
theorem coderiv_implicit_singleton_subset_of_eventually
    (hgph : ∀ᶠ p in 𝓝 (x₀, s x₀), p.2 = s p.1 ↔ (0 : Z) ∈ R p)
    (hloc : ∃ r > 0, IsClosed (graph R ∩ closedBall ((x₀, s x₀), (0 : Z)) r))
    (hker : ∀ w : StrongDual ℝ Z, (0 : StrongDual ℝ (X × Y)) ∈ coderiv R (x₀, s x₀) 0 w → w = 0)
    (v : StrongDual ℝ Y) :
    coderiv (fun x ↦ ({s x} : Set Y)) x₀ (s x₀) v ⊆
      {u | ∃ w : StrongDual ℝ Z, u.coprod (-v) ∈ coderiv R (x₀, s x₀) 0 w} :=
  coderiv_implicit_subset_of_eventually hgph hloc hker v

/-- [Mordukhovich 2006, Cor. 4.34] for a single-valued implicit map `s`, equality, local form
(the equality part of Lemma `lemma:scalarization_S_gamma_subdifferential` of the bilevel paper):
if moreover `R` is graphically regular at `((x̄, s x̄), 0)`, then
`D*s(x̄)(y*) = {x* | (x*, -y*) ∈ D*R((x̄, s x̄), 0)(z*) for some z*}` for every `y*`, and `s` is
graphically regular at `x̄`. -/
theorem coderiv_implicit_singleton_eq_of_eventually
    (hgph : ∀ᶠ p in 𝓝 (x₀, s x₀), p.2 = s p.1 ↔ (0 : Z) ∈ R p)
    (hloc : ∃ r > 0, IsClosed (graph R ∩ closedBall ((x₀, s x₀), (0 : Z)) r))
    (hker : ∀ w : StrongDual ℝ Z, (0 : StrongDual ℝ (X × Y)) ∈ coderiv R (x₀, s x₀) 0 w → w = 0)
    (hreg : GraphicallyRegularAt R (x₀, s x₀) 0) :
    (∀ v : StrongDual ℝ Y, coderiv (fun x ↦ ({s x} : Set Y)) x₀ (s x₀) v =
      {u | ∃ w : StrongDual ℝ Z, u.coprod (-v) ∈ coderiv R (x₀, s x₀) 0 w}) ∧
      GraphicallyRegularAt (fun x ↦ ({s x} : Set Y)) x₀ (s x₀) :=
  coderiv_implicit_eq_of_eventually hgph hloc hker hreg

/-- [Mordukhovich 2006, Cor. 4.34] for a single-valued implicit map `s` with
`y = s x ⟺ 0 ∈ R(x, y)` for all `(x, y)`: under local closedness of `gph R` around
`((x̄, s x̄), 0)` and `ker D*R((x̄, s x̄), 0) = {0}`,
`D*s(x̄)(y*) ⊆ {x* | (x*, -y*) ∈ D*R((x̄, s x̄), 0)(z*) for some z*}`. -/
theorem coderiv_implicit_singleton_subset (hgph : ∀ x y, y = s x ↔ (0 : Z) ∈ R (x, y))
    (hloc : ∃ r > 0, IsClosed (graph R ∩ closedBall ((x₀, s x₀), (0 : Z)) r))
    (hker : ∀ w : StrongDual ℝ Z, (0 : StrongDual ℝ (X × Y)) ∈ coderiv R (x₀, s x₀) 0 w → w = 0)
    (v : StrongDual ℝ Y) :
    coderiv (fun x ↦ ({s x} : Set Y)) x₀ (s x₀) v ⊆
      {u | ∃ w : StrongDual ℝ Z, u.coprod (-v) ∈ coderiv R (x₀, s x₀) 0 w} :=
  coderiv_implicit_subset hgph hloc hker v

/-- [Mordukhovich 2006, Cor. 4.34] for a single-valued implicit map `s` with
`y = s x ⟺ 0 ∈ R(x, y)` for all `(x, y)`, equality: if moreover `R` is graphically regular at
`((x̄, s x̄), 0)`, then `D*s(x̄)(y*) = {x* | (x*, -y*) ∈ D*R((x̄, s x̄), 0)(z*) for some z*}` and
`s` is graphically regular at `x̄`. -/
theorem coderiv_implicit_singleton_eq (hgph : ∀ x y, y = s x ↔ (0 : Z) ∈ R (x, y))
    (hloc : ∃ r > 0, IsClosed (graph R ∩ closedBall ((x₀, s x₀), (0 : Z)) r))
    (hker : ∀ w : StrongDual ℝ Z, (0 : StrongDual ℝ (X × Y)) ∈ coderiv R (x₀, s x₀) 0 w → w = 0)
    (hreg : GraphicallyRegularAt R (x₀, s x₀) 0) :
    (∀ v : StrongDual ℝ Y, coderiv (fun x ↦ ({s x} : Set Y)) x₀ (s x₀) v =
      {u | ∃ w : StrongDual ℝ Z, u.coprod (-v) ∈ coderiv R (x₀, s x₀) 0 w}) ∧
      GraphicallyRegularAt (fun x ↦ ({s x} : Set Y)) x₀ (s x₀) :=
  coderiv_implicit_eq hgph hloc hker hreg

end Implicit

section Smooth

/-! ### Single-valued residuals -/

variable {P Z : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Z]
  [NormedSpace ℝ Z]
variable {r : P → Z} {p₀ : P}

omit [NormedSpace ℝ P] [NormedSpace ℝ Z] in
/-- If `r` is continuous on a closed ball around `p̄`, the graph of `p ↦ {r p}` is locally closed
around `(p̄, z̄)` for every `z̄`. -/
theorem locallyClosed_graph_singleton_of_continuousOn {ρ : ℝ} (hρ : 0 < ρ)
    (hr : ContinuousOn r (closedBall p₀ ρ)) (z₀ : Z) :
    ∃ ρ > 0, IsClosed (graph (fun p ↦ ({r p} : Set Z)) ∩ closedBall (p₀, z₀) ρ) := by
  refine ⟨ρ, hρ, ?_⟩
  have hmaps : MapsTo Prod.fst (closedBall (p₀, z₀) ρ) (closedBall p₀ ρ) := fun q hq ↦
    mem_closedBall.2 ((le_max_left _ _).trans ((Prod.dist_eq (x := q)).symm.trans_le
      (mem_closedBall.1 hq)))
  have hcont : ContinuousOn (fun q : P × Z ↦ (q.2, r q.1)) (closedBall (p₀, z₀) ρ) :=
    continuous_snd.continuousOn.prodMk (hr.comp continuous_fst.continuousOn hmaps)
  have : graph (fun p ↦ ({r p} : Set Z)) ∩ closedBall (p₀, z₀) ρ =
      closedBall (p₀, z₀) ρ ∩ (fun q : P × Z ↦ (q.2, r q.1)) ⁻¹' diagonal Z := by
    ext q
    simp only [mem_inter_iff, mem_preimage, mem_diagonal_iff]
    exact and_comm
  rw [this]
  exact hcont.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_diagonal

omit [NormedSpace ℝ P] [NormedSpace ℝ Z] in
/-- If `r` is continuous, the graph of `p ↦ {r p}` is locally closed around every point. -/
theorem locallyClosed_graph_singleton (hr : Continuous r) (q : P × Z) :
    ∃ ρ > 0, IsClosed (graph (fun p ↦ ({r p} : Set Z)) ∩ closedBall q ρ) :=
  locallyClosed_graph_singleton_of_continuousOn one_pos hr.continuousOn q.2

/-- If `r` is differentiable around `p̄`, the graph of `p ↦ {r p}` is locally closed around
`(p̄, z̄)` for every `z̄`. -/
theorem locallyClosed_graph_singleton_of_hasFDerivAt {r' : P → P →L[ℝ] Z}
    (hf : ∀ᶠ p in 𝓝 p₀, HasFDerivAt r (r' p) p) (z₀ : Z) :
    ∃ ρ > 0, IsClosed (graph (fun p ↦ ({r p} : Set Z)) ∩ closedBall (p₀, z₀) ρ) := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hf
  refine locallyClosed_graph_singleton_of_continuousOn (half_pos hε)
    (continuousOn_of_forall_continuousAt fun p hp ↦ (hball p ?_).continuousAt) z₀
  exact mem_ball.2 ((mem_closedBall.1 hp).trans_lt (half_lt_self hε))

/-- A mapping `p ↦ {r p}` with `r` of class `C¹` around `p̄` is graphically regular at
`(p̄, r p̄)`: by Prop. 1.12 of [Mordukhovich 2018] and its proof, both coderivatives are the
adjoint of `∇r(p̄)`. -/
theorem graphicallyRegularAt_of_hasFDerivAt {r' : P → P →L[ℝ] Z}
    (hf : ∀ᶠ p in 𝓝 p₀, HasFDerivAt r (r' p) p) (hc : ContinuousAt r' p₀) :
    GraphicallyRegularAt (fun p ↦ ({r p} : Set Z)) p₀ (r p₀) := by
  refine subset_antisymm (fun ℓ hℓ ↦ ?_) regularNormalCone_subset_normalCone
  have h1 : ℓ.comp (inl ℝ P Z) ∈
      coderiv (fun p ↦ ({r p} : Set Z)) p₀ (r p₀) (-ℓ.comp (inr ℝ P Z)) := by
    change (ℓ.comp (inl ℝ P Z)).coprod (-(-ℓ.comp (inr ℝ P Z))) ∈ normalCone _ _
    rwa [neg_neg, coprod_comp_inl_inr]
  rw [coderiv_of_hasFDerivAt_of_continuousAt hf hc,
    ← regularCoderiv_of_hasFDerivAt hf.self_of_nhds] at h1
  change (ℓ.comp (inl ℝ P Z)).coprod (-(-ℓ.comp (inr ℝ P Z))) ∈ regularNormalCone _ _ at h1
  rwa [neg_neg, coprod_comp_inl_inr] at h1

/-- The kernel condition for a `C¹` mapping `p ↦ {r p}` with surjective derivative `∇r(p̄)`:
`0 ∈ D*r(p̄)(z*) = {∇r(p̄)* z*}` forces `z* = 0` [Mordukhovich 2018, Prop. 1.12]. -/
theorem forall_eq_zero_of_zero_mem_coderiv_of_surjective {r' : P → P →L[ℝ] Z}
    (hf : ∀ᶠ p in 𝓝 p₀, HasFDerivAt r (r' p) p) (hc : ContinuousAt r' p₀)
    (hsurj : Function.Surjective (r' p₀)) (w : StrongDual ℝ Z)
    (hw : (0 : StrongDual ℝ P) ∈ coderiv (fun p ↦ ({r p} : Set Z)) p₀ (r p₀) w) : w = 0 := by
  rw [coderiv_of_hasFDerivAt_of_continuousAt hf hc, mem_singleton_iff] at hw
  ext z
  obtain ⟨p, rfl⟩ := hsurj z
  simpa using (congrArg (fun m : StrongDual ℝ P ↦ m p) hw).symm

end Smooth

section SmoothImplicit

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ Z]
variable {s : X → Y} {x₀ : X} {r : X × Y → Z} {r' : X × Y → X × Y →L[ℝ] Z}

/-- Coderivative of a single-valued map `s` given implicitly by `r(x, s x) = 0`, with `r` of
class `C¹` around `(x̄, s x̄)` and `∇r(x̄, s x̄)` surjective (the setting of the implicit function
theorem; cf. Cor. 3.13 of [Mordukhovich 2018] for single-valued `C¹` mappings of full rank):
`D*s(x̄)(y*) = {x* | (x*, -y*) = ∇r(x̄, s x̄)* z* for some z*}`. Here `r(x̄, s x̄) = 0` follows from
the local description of `gph s`. -/
theorem coderiv_implicit_smooth_eq (hgph : ∀ᶠ p in 𝓝 (x₀, s x₀), p.2 = s p.1 ↔ r p = 0)
    (hf : ∀ᶠ p in 𝓝 (x₀, s x₀), HasFDerivAt r (r' p) p) (hc : ContinuousAt r' (x₀, s x₀))
    (hsurj : Function.Surjective (r' (x₀, s x₀))) (v : StrongDual ℝ Y) :
    coderiv (fun x ↦ ({s x} : Set Y)) x₀ (s x₀) v =
      {u | ∃ w : StrongDual ℝ Z, u.coprod (-v) = w.comp (r' (x₀, s x₀))} := by
  have hr0 : r (x₀, s x₀) = 0 := (hgph.self_of_nhds).1 rfl
  have hgph' : ∀ᶠ p in 𝓝 (x₀, s x₀), p.2 = s p.1 ↔ (0 : Z) ∈ ({r p} : Set Z) :=
    hgph.mono fun p hp ↦ hp.trans ⟨Eq.symm, Eq.symm⟩
  have hloc := locallyClosed_graph_singleton_of_hasFDerivAt hf (0 : Z)
  have hker := forall_eq_zero_of_zero_mem_coderiv_of_surjective hf hc hsurj
  rw [hr0] at hker
  have hreg := graphicallyRegularAt_of_hasFDerivAt hf hc
  rw [hr0] at hreg
  rw [(coderiv_implicit_singleton_eq_of_eventually (R := fun p ↦ ({r p} : Set Z)) hgph' hloc hker
    hreg).1 v]
  have hcod := coderiv_of_hasFDerivAt_of_continuousAt hf hc
  rw [hr0] at hcod
  simp only [hcod, mem_singleton_iff]

end SmoothImplicit

end VariationalAnalysis
