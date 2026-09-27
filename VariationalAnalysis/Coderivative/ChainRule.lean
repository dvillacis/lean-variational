/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import VariationalAnalysis.Coderivative.SumRule
import VariationalAnalysis.Coderivative.Smooth
import VariationalAnalysis.Coderivative.SecondOrder

/-!
# Coderivative chain rules

The general coderivative chain rules of [Mordukhovich 2018, Thm. 3.11] and their consequences
(Cor. 3.12, Cor. 3.13), in finite dimensions. For `G : X ⇉ Y` and `F : Y ⇉ Z`, the composition
is `(F ∘ G)(x) = ⋃_{y ∈ G x} F y` (`setComp F G`), and the auxiliary mapping (3.25) is

  `S(x, z) = G(x) ∩ F⁻¹(z) = {y ∈ G x | z ∈ F y}`.

Under the qualification condition (3.26) `D*F(ȳ, z̄)(0) ∩ ker D*G(x̄, ȳ) = {0}`,

  `D*(F ∘ G)(x̄, z̄)(z*) ⊆ D*G(x̄, ȳ) ∘ D*F(ȳ, z̄)(z*)`  (3.27)

when `S` is inner semicontinuous at `(x̄, z̄, ȳ)`, and the union over `ȳ ∈ S(x̄, z̄)` of the
right-hand sides when `S` is locally bounded around `(x̄, z̄)`.

The proof follows the book. The mapping `Φ(x, y) = F(y) + Δ((x, y); gph G)` of (3.29)
(`chainGraphMap`, whose graph is `{((x, y), z) | y ∈ G x, z ∈ F y}`) satisfies

  `D*Φ(x̄, ȳ, z̄)(z*) ⊆ (0, D*F(ȳ, z̄)(z*)) + N((x̄, ȳ); gph G)`  (3.30)

under (3.26), and `D*(F ∘ G)(x̄, z̄)(z*) ⊆ {x* | (x*, 0) ∈ D*Φ(x̄, ȳ, z̄)(z*)}` (3.31), with
equality when `G = g` is single-valued and locally Lipschitz. The book obtains (3.30) from the
sum rule Thm. 3.9(ii) and Exercise 1.59; since `gph Φ` is the intersection of the inverse images
of `gph G` and `gph F` under projections, we obtain it directly from the intersection rule
(Thm. 2.16), which is what the sum rule reduces to in this case.

Exercise 1.59 (indicator mappings `Δ(x; Ω) = {0}` on `Ω`, `∅` off `Ω`, with
`D*Δ(·; Ω)(x̄, 0)(z*) = N(x̄; Ω)`) is `coderiv_indicatorMap`; it gives Cor. 3.13 (normals to
inverse images) from the chain rule.

## Main results

* `indicatorMap`, `coderiv_indicatorMap`, `regularCoderiv_indicatorMap`: Exercise 1.59 of
  [Mordukhovich 2018]; `graphicallyRegularAt_indicatorMap_iff`.
* `setComp`, `chainAuxMap` (3.25), `chainGraphMap` (3.29), `chainGraphMap_eq_add`.
* `coderiv_chainGraphMap_subset`: (3.30) of [Mordukhovich 2018].
* `coprod_zero_mem_coderiv_chainGraphMap`, `exists_coprod_zero_mem_coderiv_chainGraphMap`:
  (3.31) (inner semicontinuous and locally bounded cases);
  `coprod_zero_mem_coderiv_chainGraphMap_iff`: equality in (3.31) for locally Lipschitz `g`.
* `coderiv_setComp_subset`: Thm. 3.11(i) of [Mordukhovich 2018], (3.27).
* `coderiv_setComp_subset_iUnion`: Thm. 3.11(ii).
* `coderiv_comp_subset`: (3.27) for a `C¹` inner mapping (inner semicontinuity is automatic).
* `coderiv_comp_eq_of_graphicallyRegularAt`, `graphicallyRegularAt_comp`: Thm. 3.11(iii),
  graphically regular case of (3.28). The full-rank case of (3.28) is
  `coderiv_comp_of_surjective` (`Coderivative/Smooth`).
* `coderiv_setComp_subset_of_lipschitzLike_or_metricallyRegular`,
  `coderiv_setComp_subset_iUnion_of_lipschitzLike_or_metricallyRegular`: Cor. 3.12.
* `normalCone_preimage_setValued_subset`,
  `normalCone_preimage_setValued_subset_of_metricallyRegular`,
  `normalCone_preimage_eq_of_normallyRegularAt`: Cor. 3.13 of [Mordukhovich 2018]. The full-rank
  case of the equality is Exercise 1.54(ii),
  `normalCone_preimage_of_surjective_of_finiteDimensional` (`Normal/Diffeomorphism`).

Helpers: `locallyClosed_preimage_of_continuousOn`, `locallyClosed_graph_of_continuousOn`,
`locallyClosed_graph_comp` (local closedness of inverse images and graphs),
`lipschitzLikeAt_of_lipschitzOnWith` (locally Lipschitz mappings are Lipschitz-like),
`innerSemicontinuousAt_chainAuxMap_singleton` (inner semicontinuity of (3.25) for a continuous
inner mapping), `comp_mem_epsNormalCone_graph_comp`.
-/

open Filter Topology Set Metric ContinuousLinearMap
open scoped Pointwise NNReal

namespace VariationalAnalysis

section LocallyClosed

/-! ### Local closedness of inverse images and graphs -/

variable {P Q : Type*} [PseudoMetricSpace P] [PseudoMetricSpace Q]

/-- The inverse image of a set locally closed around `Θ p₀` under a map continuous on a
neighborhood of `p₀` is locally closed around `p₀`. -/
theorem locallyClosed_preimage_of_continuousOn {Θ : P → Q} {C : Set Q} {p₀ : P} {V : Set P}
    (hV : V ∈ 𝓝 p₀) (hΘ : ContinuousOn Θ V) (h : ∃ r > 0, IsClosed (C ∩ closedBall (Θ p₀) r)) :
    ∃ r > 0, IsClosed (Θ ⁻¹' C ∩ closedBall p₀ r) := by
  obtain ⟨R, hR, hcl⟩ := h
  obtain ⟨δ, hδ, hδR⟩ := Metric.continuousAt_iff.1 (hΘ.continuousAt hV) R hR
  obtain ⟨ρ, hρ, hρV⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hV
  refine ⟨min (δ / 2) ρ, lt_min (half_pos hδ) hρ, ?_⟩
  have hsub : closedBall p₀ (min (δ / 2) ρ) ⊆ V :=
    (closedBall_subset_closedBall (min_le_right _ _)).trans hρV
  have heq : Θ ⁻¹' C ∩ closedBall p₀ (min (δ / 2) ρ) =
      closedBall p₀ (min (δ / 2) ρ) ∩ Θ ⁻¹' (C ∩ closedBall (Θ p₀) R) := by
    ext p
    simp only [mem_inter_iff, mem_preimage, mem_closedBall]
    refine ⟨fun ⟨hC, hp⟩ ↦ ⟨hp, hC, (hδR ?_).le⟩, fun ⟨hp, hC, _⟩ ↦ ⟨hC, hp⟩⟩
    exact hp.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hδ))
  rw [heq]
  exact (hΘ.mono hsub).preimage_isClosed_of_isClosed isClosed_closedBall hcl

end LocallyClosed

section Indicator

/-! ### Indicator mappings, Exercise 1.59 -/

variable {E Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Q]
  [NormedSpace ℝ Q]

/-- The indicator mapping `Δ(·; Ω) : E ⇉ Q` of [Mordukhovich 2018, Exercise 1.59]:
`Δ(x; Ω) = {0}` for `x ∈ Ω` and `Δ(x; Ω) = ∅` otherwise. -/
def indicatorMap (Ω : Set E) : E → Set Q := fun x ↦ {y | x ∈ Ω ∧ y = 0}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ Q] in
theorem graph_indicatorMap (Ω : Set E) : graph (indicatorMap Ω : E → Set Q) = Ω ×ˢ {0} := rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ Q] in
theorem dom_indicatorMap (Ω : Set E) : dom (indicatorMap Ω : E → Set Q) = Ω := by
  ext x
  exact ⟨fun ⟨_, h, _⟩ ↦ h, fun h ↦ ⟨0, h, rfl⟩⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Every dual element is a regular normal to a singleton. -/
theorem regularNormalCone_singleton (y : Q) : regularNormalCone {y} y = univ := by
  refine eq_univ_of_forall fun v ↦ ⟨rfl, fun ε hε ↦ ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [mem_singleton_iff.1 hz]
  simp

/-- Exercise 1.59 of [Mordukhovich 2018] (coderivatives of indicator mappings):
`D*Δ(·; Ω)(x̄, 0)(z*) = N(x̄; Ω)` for every `z*`. -/
theorem coderiv_indicatorMap (Ω : Set E) (x₀ : E) (z' : StrongDual ℝ Q) :
    coderiv (indicatorMap Ω : E → Set Q) x₀ 0 z' = normalCone Ω x₀ := by
  ext u
  simp only [coderiv, mem_ofPred_eq, graph_indicatorMap, coprod_mem_normalCone_prod_iff,
    normalCone_singleton, mem_univ, and_true]

/-- Exercise 1.59 of [Mordukhovich 2018] for the regular coderivative:
`D̂*Δ(·; Ω)(x̄, 0)(z*) = N̂(x̄; Ω)`. -/
theorem regularCoderiv_indicatorMap (Ω : Set E) (x₀ : E) (z' : StrongDual ℝ Q) :
    regularCoderiv (indicatorMap Ω : E → Set Q) x₀ 0 z' = regularNormalCone Ω x₀ := by
  ext u
  simp only [regularCoderiv, mem_ofPred_eq, graph_indicatorMap,
    coprod_mem_regularNormalCone_prod_iff, regularNormalCone_singleton, mem_univ, and_true]

/-- `Δ(·; Ω)` is graphically regular at `(x̄, 0)` iff `Ω` is normally regular at `x̄`. -/
theorem graphicallyRegularAt_indicatorMap_iff {Ω : Set E} {x₀ : E} :
    GraphicallyRegularAt (indicatorMap Ω : E → Set Q) x₀ 0 ↔ NormallyRegularAt Ω x₀ := by
  have key : ∀ ℓ : StrongDual ℝ (E × Q),
      (ℓ ∈ normalCone (graph (indicatorMap Ω : E → Set Q)) (x₀, 0) ↔
        ℓ.comp (inl ℝ E Q) ∈ normalCone Ω x₀) ∧
      (ℓ ∈ regularNormalCone (graph (indicatorMap Ω : E → Set Q)) (x₀, 0) ↔
        ℓ.comp (inl ℝ E Q) ∈ regularNormalCone Ω x₀) := fun ℓ ↦ by
    rw [← coprod_comp_inl_inr ℓ, graph_indicatorMap, coprod_mem_normalCone_prod_iff,
      coprod_mem_regularNormalCone_prod_iff, normalCone_singleton, regularNormalCone_singleton]
    simp
  constructor
  · intro h
    ext v
    have := (key (v.coprod 0)).1
    rw [h, (key (v.coprod 0)).2] at this
    simpa using this.symm
  · intro h
    ext ℓ
    rw [(key ℓ).1, (key ℓ).2, h]

end Indicator

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

section Composition

/-! ### Compositions and the auxiliary mappings (3.25), (3.29) -/

/-- The composition `(F ∘ G)(x) = ⋃_{y ∈ G x} F y` of set-valued mappings
[Mordukhovich 2018, Subsection 3.2.2]. -/
def setComp (F : Y → Set Z) (G : X → Set Y) : X → Set Z := fun x ↦ ⋃ y ∈ G x, F y

/-- The auxiliary mapping (3.25) of [Mordukhovich 2018]:
`S(x, z) = G(x) ∩ F⁻¹(z) = {y ∈ G x | z ∈ F y}`. -/
def chainAuxMap (F : Y → Set Z) (G : X → Set Y) : X × Z → Set Y :=
  fun q ↦ {y | y ∈ G q.1 ∧ q.2 ∈ F y}

/-- The mapping `Φ(x, y) = F(y) + Δ((x, y); gph G)` of [Mordukhovich 2018, (3.29)]:
`Φ(x, y) = F y` if `y ∈ G x` and `∅` otherwise (`chainGraphMap_eq_add`). -/
def chainGraphMap (F : Y → Set Z) (G : X → Set Y) : X × Y → Set Z :=
  fun p ↦ {z | p.2 ∈ G p.1 ∧ z ∈ F p.2}

variable {F : Y → Set Z} {G : X → Set Y}

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
theorem mem_setComp_iff {x : X} {z : Z} : z ∈ setComp F G x ↔ ∃ y ∈ G x, z ∈ F y := by
  simp [setComp]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- For a single-valued inner mapping, `F ∘ g` is `x ↦ F (g x)`. -/
theorem setComp_singleton (F : Y → Set Z) (g : X → Y) :
    setComp F (fun x ↦ {g x}) = fun x ↦ F (g x) := by
  funext x
  simp [setComp]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- `dom S = gph(F ∘ G)` for the mapping (3.25). -/
theorem dom_chainAuxMap : dom (chainAuxMap F G) = graph (setComp F G) := by
  ext ⟨x, z⟩
  simp only [dom, chainAuxMap, graph, mem_ofPred_eq, mem_setComp_iff]
  exact ⟨fun ⟨y, hy, hz⟩ ↦ ⟨y, hy, hz⟩, fun ⟨y, hy, hz⟩ ↦ ⟨y, hy, hz⟩⟩

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedSpace ℝ Z] in
/-- `Φ(x, y) = F(y) + Δ((x, y); gph G)` [Mordukhovich 2018, (3.29)], with the indicator mapping
of Exercise 1.59. -/
theorem chainGraphMap_eq_add (p : X × Y) :
    chainGraphMap F G p = F p.2 + indicatorMap (graph G) p := by
  ext z
  simp only [chainGraphMap, indicatorMap, graph, mem_ofPred_eq, Set.mem_add]
  constructor
  · rintro ⟨hp, hz⟩
    exact ⟨z, hz, 0, ⟨hp, rfl⟩, add_zero z⟩
  · rintro ⟨z', hz', _, ⟨hp, rfl⟩, rfl⟩
    exact ⟨hp, by simpa using hz'⟩

/-- The projection `((x, y), z) ↦ (x, y)`. -/
noncomputable abbrev chainProj₁ : (X × Y) × Z →L[ℝ] X × Y := fst ℝ (X × Y) Z

/-- The projection `((x, y), z) ↦ (y, z)`. -/
noncomputable abbrev chainProj₂ : (X × Y) × Z →L[ℝ] Y × Z :=
  ((snd ℝ X Y).comp (fst ℝ (X × Y) Z)).prod (snd ℝ (X × Y) Z)

/-- The projection `((x, y), z) ↦ (x, z)`, which maps `gph Φ` onto `gph(F ∘ G)`. -/
noncomputable abbrev chainProj : (X × Y) × Z →L[ℝ] X × Z :=
  ((fst ℝ X Y).comp (fst ℝ (X × Y) Z)).prod (snd ℝ (X × Y) Z)

/-- `gph Φ = {((x, y), z) | (x, y) ∈ gph G} ∩ {((x, y), z) | (y, z) ∈ gph F}`. -/
theorem graph_chainGraphMap :
    graph (chainGraphMap F G) = chainProj₁ ⁻¹' graph G ∩ chainProj₂ ⁻¹' graph F := rfl

theorem chainProj₁_surjective : Function.Surjective (chainProj₁ : (X × Y) × Z →L[ℝ] X × Y) :=
  fun q ↦ ⟨(q, 0), rfl⟩

theorem chainProj₂_surjective : Function.Surjective (chainProj₂ : (X × Y) × Z →L[ℝ] Y × Z) :=
  fun q ↦ ⟨((0, q.1), q.2), rfl⟩

theorem mapsTo_chainProj :
    MapsTo chainProj (graph (chainGraphMap F G)) (graph (setComp F G)) :=
  fun _ hp ↦ mem_setComp_iff.2 ⟨_, hp.1, hp.2⟩

/-- The pullback of `(x*, -z*)` along `((x, y), z) ↦ (x, z)` is `((x*, 0), -z*)`. -/
theorem coprod_comp_chainProj (x' : StrongDual ℝ X) (z' : StrongDual ℝ Z) :
    (x'.coprod (-z')).comp chainProj = (x'.coprod (0 : StrongDual ℝ Y)).coprod (-z') := by
  ext <;> simp

/-- The graph of `Φ` is closed when those of `G` and `F` are. -/
theorem isClosed_graph_chainGraphMap (hG : IsClosed (graph G)) (hF : IsClosed (graph F)) :
    IsClosed (graph (chainGraphMap F G)) :=
  (hG.preimage chainProj₁.continuous).inter (hF.preimage chainProj₂.continuous)

end Composition

section ChainRule

variable [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ Z]
  {F : Y → Set Z} {G : X → Set Y} {x₀ : X} {y₀ : Y} {z₀ : Z}

/-- (3.30) of [Mordukhovich 2018] (proof of Thm. 3.11): if the graphs of `G`, `F` are locally
closed around `(x̄, ȳ)`, `(ȳ, z̄)` and the qualification condition (3.26)
`D*F(ȳ, z̄)(0) ∩ ker D*G(x̄, ȳ) = {0}` holds, then
`D*Φ(x̄, ȳ, z̄)(z*) ⊆ (0, D*F(ȳ, z̄)(z*)) + N((x̄, ȳ); gph G)`. -/
theorem coderiv_chainGraphMap_subset
    (hlocG : ∃ r > 0, IsClosed (graph G ∩ closedBall (x₀, y₀) r))
    (hlocF : ∃ r > 0, IsClosed (graph F ∩ closedBall (y₀, z₀) r))
    (hqc : ∀ w ∈ coderiv F y₀ z₀ 0, w ∈ coderivKer G x₀ y₀ → w = 0) (z' : StrongDual ℝ Z) :
    coderiv (chainGraphMap F G) (x₀, y₀) z₀ z' ⊆
      (fun w ↦ (0 : StrongDual ℝ X).coprod w) '' coderiv F y₀ z₀ z' +
        normalCone (graph G) (x₀, y₀) := by
  intro m hm
  have hm' : m.coprod (-z') ∈ normalCone (chainProj₁ ⁻¹' graph G ∩ chainProj₂ ⁻¹' graph F)
      ((x₀, y₀), z₀) := hm
  have heval : ∀ (ℓ₁ : StrongDual ℝ (X × Y)) (ℓ₂ : StrongDual ℝ (Y × Z)) (x : X) (y : Y) (z : Z),
      (ℓ₁.comp chainProj₁ + ℓ₂.comp chainProj₂ : StrongDual ℝ ((X × Y) × Z)) ((x, y), z) =
        ℓ₁ (x, y) + ℓ₂ (y, z) := fun _ _ _ _ _ ↦ rfl
  obtain ⟨ℓ₁, h₁, ℓ₂, h₂, heq⟩ := exists_eq_add_of_mem_normalCone_preimage_inter
    (P := (X × Y) × Z) (Q := X × Y) (Q₂ := Y × Z) chainProj₁_surjective chainProj₂_surjective
    hlocG hlocF (fun ℓ₁ h₁ ℓ₂ h₂ h0 ↦ by
      have e1 : ∀ x y, ℓ₁ (x, y) + ℓ₂ (y, 0) = 0 := fun x y ↦ by
        simpa [heval] using DFunLike.congr_fun h0 ((x, y), (0 : Z))
      have e2 : ∀ z, ℓ₂ (0, z) = 0 := fun z ↦ by
        simpa [heval, Prod.mk_zero_zero, map_zero] using
          DFunLike.congr_fun h0 (((0 : X), (0 : Y)), z)
      have hw : ℓ₂.comp (inl ℝ Y Z) ∈ coderiv F y₀ z₀ 0 :=
        comp_inl_mem_coderiv h₂ (by ext z; simp [e2])
      have hℓ₁ : ℓ₁ = (0 : StrongDual ℝ X).coprod (-ℓ₂.comp (inl ℝ Y Z)) := by
        ext x <;> simp [eq_neg_of_add_eq_zero_left (e1 _ _), Prod.mk_zero_zero, map_zero]
      have hker : ℓ₂.comp (inl ℝ Y Z) ∈ coderivKer G x₀ y₀ := by
        show _ ∈ normalCone _ _
        rw [← hℓ₁]
        exact h₁
      rw [hℓ₁, hqc _ hw hker]
      ext <;> simp) hm'
  have e1 : ∀ x y, m (x, y) = ℓ₁ (x, y) + ℓ₂ (y, 0) := fun x y ↦ by
    simpa [heval] using DFunLike.congr_fun heq ((x, y), (0 : Z))
  have e2 : ∀ z, -z' z = ℓ₂ (0, z) := fun z ↦ by
    simpa [heval, Prod.mk_zero_zero, map_zero] using
      DFunLike.congr_fun heq (((0 : X), (0 : Y)), z)
  have hw : ℓ₂.comp (inl ℝ Y Z) ∈ coderiv F y₀ z₀ z' :=
    comp_inl_mem_coderiv h₂ (by ext z; simp [← e2])
  refine ⟨_, ⟨_, hw, rfl⟩, ℓ₁, h₁, ?_⟩
  ext x <;> simp [e1, add_comm, Prod.mk_zero_zero, map_zero]

/-- Combining (3.30) with `(x*, 0) ∈ D*Φ(x̄, ȳ, z̄)(z*)`: under (3.26),
`x* ∈ D*G(x̄, ȳ)(D*F(ȳ, z̄)(z*))` [Mordukhovich 2018, proof of Thm. 3.11]. -/
theorem mem_iUnion_coderiv_of_coprod_zero_mem
    (hlocG : ∃ r > 0, IsClosed (graph G ∩ closedBall (x₀, y₀) r))
    (hlocF : ∃ r > 0, IsClosed (graph F ∩ closedBall (y₀, z₀) r))
    (hqc : ∀ w ∈ coderiv F y₀ z₀ 0, w ∈ coderivKer G x₀ y₀ → w = 0) {z' : StrongDual ℝ Z}
    {x' : StrongDual ℝ X} (h : x'.coprod 0 ∈ coderiv (chainGraphMap F G) (x₀, y₀) z₀ z') :
    x' ∈ ⋃ w ∈ coderiv F y₀ z₀ z', coderiv G x₀ y₀ w := by
  obtain ⟨_, ⟨w, hw, rfl⟩, n, hn, heq⟩ := coderiv_chainGraphMap_subset hlocG hlocF hqc z' h
  refine mem_biUnion hw ?_
  have : x'.coprod (-w) = n := by
    rw [eq_sub_of_add_eq' heq]
    ext <;> simp
  show _ ∈ normalCone _ _
  rwa [this]

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ Z] in
/-- (3.31) of [Mordukhovich 2018] (proof of Thm. 3.11(i)): if `ȳ ∈ S(x̄, z̄)` and the mapping
`S` of (3.25) is inner semicontinuous at `(x̄, z̄, ȳ)`, then
`x* ∈ D*(F ∘ G)(x̄, z̄)(z*)` implies `(x*, 0) ∈ D*Φ(x̄, ȳ, z̄)(z*)`. -/
theorem coprod_zero_mem_coderiv_chainGraphMap (hy : y₀ ∈ chainAuxMap F G (x₀, z₀))
    (hS : InnerSemicontinuousAt (chainAuxMap F G) (x₀, z₀) y₀) {z' : StrongDual ℝ Z}
    {x' : StrongDual ℝ X} (hx : x' ∈ coderiv (setComp F G) x₀ z₀ z') :
    x'.coprod 0 ∈ coderiv (chainGraphMap F G) (x₀, y₀) z₀ z' := by
  have hpull := comp_mem_normalCone_of_lift (P := (X × Y) × Z) (Q := X × Z) chainProj
    mapsTo_chainProj (p₀ := ((x₀, y₀), z₀))
    (show ((x₀, y₀), z₀) ∈ graph (chainGraphMap F G) from hy) (fun q hq ↦ by
      rw [show chainProj ((x₀, y₀), z₀) = (x₀, z₀) from rfl, ← dom_chainAuxMap] at hq
      obtain ⟨v, hv, hvS⟩ := hS q hq
      have hq1 := (tendsto_nhdsWithin_iff.1 hq).1
      exact ⟨fun k ↦ (((q k).1, v k), (q k).2),
        (((continuous_fst.tendsto _).comp hq1).prodMk_nhds hv).prodMk_nhds
          ((continuous_snd.tendsto _).comp hq1), hvS.mono fun k hk ↦ ⟨hk, rfl⟩⟩)
    (ℓ := x'.coprod (-z')) hx
  rw [coprod_comp_chainProj] at hpull
  exact hpull

/-- (3.31) of [Mordukhovich 2018], locally bounded case (proof of Thm. 3.11(ii)): if the graphs
of `G`, `F` are closed and `S` of (3.25) is locally bounded around `(x̄, z̄)`, then for every
`x* ∈ D*(F ∘ G)(x̄, z̄)(z*)` there is `ȳ ∈ S(x̄, z̄)` with `(x*, 0) ∈ D*Φ(x̄, ȳ, z̄)(z*)`. -/
theorem exists_coprod_zero_mem_coderiv_chainGraphMap (hG : IsClosed (graph G))
    (hF : IsClosed (graph F)) (hS : LocallyBoundedAt (chainAuxMap F G) (x₀, z₀))
    {z' : StrongDual ℝ Z} {x' : StrongDual ℝ X} (hx : x' ∈ coderiv (setComp F G) x₀ z₀ z') :
    ∃ y₀ ∈ chainAuxMap F G (x₀, z₀), x'.coprod 0 ∈ coderiv (chainGraphMap F G) (x₀, y₀) z₀ z' := by
  obtain ⟨U, hU, hbdd⟩ := hS
  have hA : ∀ p : (X × Y) × Z, chainProj p = (p.1.1, p.2) := fun _ ↦ rfl
  have hbd : ∃ V ∈ 𝓝 (x₀, z₀), Bornology.IsBounded
      {p | p ∈ graph (chainGraphMap F G) ∧ chainProj p ∈ V} := by
    refine ⟨U ∩ ball (x₀, z₀) 1, inter_mem hU (ball_mem_nhds _ one_pos),
      (((isBounded_ball (x := x₀) (r := 1)).prod hbdd).prod
        (isBounded_ball (x := z₀) (r := 1))).subset ?_⟩
    rintro ⟨⟨x, y⟩, z⟩ ⟨hp, hV, hball⟩
    rw [hA] at hV hball
    rw [mem_ball, Prod.dist_eq] at hball
    exact ⟨⟨mem_ball.2 ((le_max_left _ _).trans_lt hball), mem_biUnion hV hp⟩,
      mem_ball.2 ((le_max_right _ _).trans_lt hball)⟩
  obtain ⟨⟨⟨x, y⟩, z⟩, hp, hAp, hpull⟩ := exists_comp_mem_normalCone_of_bounded
    (P := (X × Y) × Z) (Q := X × Z) chainProj mapsTo_chainProj (fun q hq ↦ by
      obtain ⟨y, hy, hz⟩ := mem_setComp_iff.1 (show q.2 ∈ setComp F G q.1 from hq)
      exact ⟨((q.1, y), q.2), ⟨hy, hz⟩, rfl⟩)
    (isClosed_graph_chainGraphMap hG hF) hbd (ℓ := x'.coprod (-z')) hx
  rw [hA] at hAp
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hAp
  rw [coprod_comp_chainProj] at hpull
  exact ⟨y, hp, hpull⟩

/-- Thm. 3.11(i) of [Mordukhovich 2018] (general coderivative chain rule, inner semicontinuous
case), (3.27): let `ȳ ∈ S(x̄, z̄)` for the mapping `S(x, z) = G(x) ∩ F⁻¹(z)` of (3.25), let `S`
be inner semicontinuous at `(x̄, z̄, ȳ)`, let the graphs of `G`, `F` be locally closed around
`(x̄, ȳ)`, `(ȳ, z̄)`, and let the qualification condition (3.26)
`D*F(ȳ, z̄)(0) ∩ ker D*G(x̄, ȳ) = {0}` hold. Then
`D*(F ∘ G)(x̄, z̄)(z*) ⊆ D*G(x̄, ȳ) ∘ D*F(ȳ, z̄)(z*) = ⋃_{y* ∈ D*F(ȳ, z̄)(z*)} D*G(x̄, ȳ)(y*)`. -/
theorem coderiv_setComp_subset (hy : y₀ ∈ chainAuxMap F G (x₀, z₀))
    (hS : InnerSemicontinuousAt (chainAuxMap F G) (x₀, z₀) y₀)
    (hlocG : ∃ r > 0, IsClosed (graph G ∩ closedBall (x₀, y₀) r))
    (hlocF : ∃ r > 0, IsClosed (graph F ∩ closedBall (y₀, z₀) r))
    (hqc : ∀ w ∈ coderiv F y₀ z₀ 0, w ∈ coderivKer G x₀ y₀ → w = 0) (z' : StrongDual ℝ Z) :
    coderiv (setComp F G) x₀ z₀ z' ⊆ ⋃ w ∈ coderiv F y₀ z₀ z', coderiv G x₀ y₀ w :=
  fun _ hx ↦ mem_iUnion_coderiv_of_coprod_zero_mem hlocG hlocF hqc
    (coprod_zero_mem_coderiv_chainGraphMap hy hS hx)

/-- Thm. 3.11(ii) of [Mordukhovich 2018] (general coderivative chain rule, locally bounded
case): let the graphs of `G`, `F` be closed, let `S` of (3.25) be locally bounded around
`(x̄, z̄)`, and let the qualification condition (3.26) hold for every `ȳ ∈ S(x̄, z̄)`. Then
`D*(F ∘ G)(x̄, z̄)(z*) ⊆ ⋃_{ȳ ∈ S(x̄, z̄)} D*G(x̄, ȳ) ∘ D*F(ȳ, z̄)(z*)`. -/
theorem coderiv_setComp_subset_iUnion (hG : IsClosed (graph G)) (hF : IsClosed (graph F))
    (hS : LocallyBoundedAt (chainAuxMap F G) (x₀, z₀))
    (hqc : ∀ y ∈ chainAuxMap F G (x₀, z₀), ∀ w ∈ coderiv F y z₀ 0, w ∈ coderivKer G x₀ y → w = 0)
    (z' : StrongDual ℝ Z) :
    coderiv (setComp F G) x₀ z₀ z' ⊆
      ⋃ y ∈ chainAuxMap F G (x₀, z₀), ⋃ w ∈ coderiv F y z₀ z', coderiv G x₀ y w := by
  intro x' hx
  obtain ⟨y, hy, h⟩ := exists_coprod_zero_mem_coderiv_chainGraphMap hG hF hS hx
  exact mem_biUnion hy (mem_iUnion_coderiv_of_coprod_zero_mem (locallyClosed_of_isClosed hG _)
    (locallyClosed_of_isClosed hF _) (hqc y hy) h)

/-- Cor. 3.12 of [Mordukhovich 2018] (coderivative chain rules for Lipschitz-like and metrically
regular mappings), inner semicontinuous case: the chain rule (3.27) of Thm. 3.11(i) holds if
either `F` is Lipschitz-like around `(ȳ, z̄)` or `G` is metrically regular around `(x̄, ȳ)`
(Thm. 3.3 gives (3.26): `LipschitzLikeAt.coderiv_zero`, `MetricallyRegularAt.coderivKer_eq`). -/
theorem coderiv_setComp_subset_of_lipschitzLike_or_metricallyRegular
    (hy : y₀ ∈ chainAuxMap F G (x₀, z₀))
    (hS : InnerSemicontinuousAt (chainAuxMap F G) (x₀, z₀) y₀)
    (hlocG : ∃ r > 0, IsClosed (graph G ∩ closedBall (x₀, y₀) r))
    (hlocF : ∃ r > 0, IsClosed (graph F ∩ closedBall (y₀, z₀) r))
    (hwp : LipschitzLikeAt F y₀ z₀ ∨ MetricallyRegularAt G x₀ y₀) (z' : StrongDual ℝ Z) :
    coderiv (setComp F G) x₀ z₀ z' ⊆ ⋃ w ∈ coderiv F y₀ z₀ z', coderiv G x₀ y₀ w := by
  refine coderiv_setComp_subset hy hS hlocG hlocF (fun w hw hker ↦ ?_) z'
  rcases hwp with h | h
  · rwa [h.coderiv_zero hy.2] at hw
  · rwa [h.coderivKer_eq hy.1] at hker

/-- Cor. 3.12 of [Mordukhovich 2018], locally bounded case: the chain rule of Thm. 3.11(ii)
holds if for every `ȳ ∈ S(x̄, z̄)` either `F` is Lipschitz-like around `(ȳ, z̄)` or `G` is
metrically regular around `(x̄, ȳ)`. -/
theorem coderiv_setComp_subset_iUnion_of_lipschitzLike_or_metricallyRegular
    (hG : IsClosed (graph G)) (hF : IsClosed (graph F))
    (hS : LocallyBoundedAt (chainAuxMap F G) (x₀, z₀))
    (hwp : ∀ y ∈ chainAuxMap F G (x₀, z₀), LipschitzLikeAt F y z₀ ∨ MetricallyRegularAt G x₀ y)
    (z' : StrongDual ℝ Z) :
    coderiv (setComp F G) x₀ z₀ z' ⊆
      ⋃ y ∈ chainAuxMap F G (x₀, z₀), ⋃ w ∈ coderiv F y z₀ z', coderiv G x₀ y w := by
  refine coderiv_setComp_subset_iUnion hG hF hS (fun y hy w hw hker ↦ ?_) z'
  rcases hwp y hy with h | h
  · rwa [h.coderiv_zero hy.2] at hw
  · rwa [h.coderivKer_eq hy.1] at hker

end ChainRule

section SingleValued

/-! ### Single-valued mappings -/

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] [NormedSpace ℝ Z] in
/-- The graph of `F ∘ g` is locally closed around `(x₀, z₀)` if that of `F` is around
`(g x₀, z₀)` and `g` is continuous on a neighborhood of `x₀`. -/
theorem locallyClosed_graph_comp {g : X → Y} {F : Y → Set Z} {x₀ : X} {z₀ : Z} {V : Set X}
    (hV : V ∈ 𝓝 x₀) (hg : ContinuousOn g V)
    (hloc : ∃ r > 0, IsClosed (graph F ∩ closedBall (g x₀, z₀) r)) :
    ∃ r > 0, IsClosed (graph (fun x ↦ F (g x)) ∩ closedBall (x₀, z₀) r) :=
  locallyClosed_preimage_of_continuousOn (Θ := Prod.map g id) (C := graph F) (p₀ := (x₀, z₀))
    (V := V ×ˢ univ) (prod_mem_nhds hV univ_mem)
    ((hg.comp continuousOn_fst fun _ hp ↦ hp.1).prodMk continuousOn_snd) hloc

omit [NormedSpace ℝ Y] [NormedSpace ℝ Z] in
/-- A mapping Lipschitz continuous on a neighborhood of `ȳ` is Lipschitz-like around
`(ȳ, h ȳ)` [Mordukhovich 2018, Def. 3.1(c)]. -/
theorem lipschitzLikeAt_of_lipschitzOnWith {h : Y → Z} {U : Set Y} {y₀ : Y} (hU : U ∈ 𝓝 y₀)
    {K : ℝ≥0} (hh : LipschitzOnWith K h U) : LipschitzLikeAt (fun y ↦ {h y}) y₀ (h y₀) :=
  ⟨K, U, hU, univ, univ_mem, fun x hx u hu y hy ↦
    ⟨h u, rfl, by rw [mem_singleton_iff.1 hy.1]; exact hh.dist_le_mul x hx u hu⟩⟩

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] [NormedSpace ℝ Z] in
/-- For a single-valued inner mapping `g` continuous at `x̄`, the mapping `S` of (3.25) is
inner semicontinuous at `(x̄, z̄, g x̄)` [Mordukhovich 2018, proof of Thm. 3.11(iii)]. -/
theorem innerSemicontinuousAt_chainAuxMap_singleton {g : X → Y} {F : Y → Set Z} {x₀ : X}
    {z₀ : Z} (hg : ContinuousAt g x₀) :
    InnerSemicontinuousAt (chainAuxMap F fun x ↦ {g x}) (x₀, z₀) (g x₀) := by
  intro q hq
  rw [dom_chainAuxMap] at hq
  refine ⟨fun k ↦ g (q k).1,
    hg.tendsto.comp ((continuous_fst.tendsto _).comp (tendsto_nhdsWithin_iff.1 hq).1), ?_⟩
  filter_upwards [(tendsto_nhdsWithin_iff.1 hq).2] with k hk
  obtain ⟨y, hy, hz⟩ := mem_setComp_iff.1 hk
  exact ⟨rfl, (mem_singleton_iff.1 hy) ▸ hz⟩

/-- The linear map `(x, z) ↦ ((x, 0), z)`. -/
noncomputable abbrev chainInj : X × Z →L[ℝ] (X × Y) × Z :=
  ((inl ℝ X Y).comp (fst ℝ X Z)).prod (snd ℝ X Z)

/-- The linear map `y ↦ ((0, y), 0)`. -/
noncomputable abbrev chainInjY : Y →L[ℝ] (X × Y) × Z := (inl ℝ (X × Y) Z).comp (inr ℝ X Y)

/-- [Mordukhovich 2018, proof of Thm. 3.11(iii)]: if `g` is Lipschitz continuous with modulus
`L` around `x₁` and `m` is a regular normal to `gph Φ` at `((x₁, g x₁), z₁)`, then
`(x, z) ↦ m ((x, 0), z)` is an `ω`-normal to `gph(F ∘ g)` at `(x₁, z₁)` with
`ω = L ‖m ((0, ·), 0)‖`. -/
theorem comp_mem_epsNormalCone_graph_comp {g : X → Y} {F : Y → Set Z} {U : Set X} {L : ℝ≥0}
    (hg : LipschitzOnWith L g U) {x₁ : X} {z₁ : Z} (hU : U ∈ 𝓝 x₁)
    {m : StrongDual ℝ ((X × Y) × Z)}
    (hm : m ∈ regularNormalCone (graph (chainGraphMap F fun x ↦ {g x})) ((x₁, g x₁), z₁)) :
    m.comp chainInj ∈ epsNormalCone (L * ‖m.comp chainInjY‖) (graph fun x ↦ F (g x)) (x₁, z₁) := by
  refine ⟨hm.1.2, fun ε hε ↦ ?_⟩
  set c : ℝ := L + 1 with hc_def
  have hL : (0 : ℝ) ≤ L := L.coe_nonneg
  have hc : 0 < c := by positivity
  have hT : Tendsto (fun p : X × Z ↦ ((p.1, g p.1), p.2)) (𝓝[graph fun x ↦ F (g x)] (x₁, z₁))
      (𝓝[graph (chainGraphMap F fun x ↦ {g x})] ((x₁, g x₁), z₁)) := by
    have hgc : ContinuousAt g x₁ := hg.continuousOn.continuousAt hU
    have hcont : ContinuousAt (fun p : X × Z ↦ ((p.1, g p.1), p.2)) (x₁, z₁) :=
      (continuousAt_fst.prodMk (hgc.comp continuousAt_fst)).prodMk continuousAt_snd
    exact tendsto_nhdsWithin_iff.2 ⟨hcont.tendsto.mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun p hp ↦ ⟨rfl, hp⟩⟩
  have hUev : ∀ᶠ p in 𝓝[graph fun x ↦ F (g x)] (x₁, z₁), p.1 ∈ U :=
    nhdsWithin_le_nhds ((continuous_fst.tendsto (x₁, z₁)).eventually hU)
  filter_upwards [hT.eventually (hm.2 (ε / c) (by positivity)), hUev] with p hp hpU
  obtain ⟨x, z⟩ := p
  simp only at hp hpU
  have hLip : ‖g x - g x₁‖ ≤ L * ‖x - x₁‖ := by
    rw [← dist_eq_norm, ← dist_eq_norm]
    exact hg.dist_le_mul x hpU x₁ (mem_of_mem_nhds hU)
  set d : ℝ := max ‖x - x₁‖ ‖z - z₁‖ with hd
  have hxd : ‖x - x₁‖ ≤ d := le_max_left _ _
  have hzd : ‖z - z₁‖ ≤ d := le_max_right _ _
  have hd0 : 0 ≤ d := (norm_nonneg _).trans hxd
  have hnorm : max (max ‖x - x₁‖ ‖g x - g x₁‖) ‖z - z₁‖ ≤ c * d := by
    refine max_le (max_le ?_ ?_) ?_
    · nlinarith
    · nlinarith [mul_le_mul_of_nonneg_left hxd hL]
    · nlinarith
  simp only [Prod.mk_sub_mk, Prod.norm_mk] at hp
  have hsplit : m ((x - x₁, g x - g x₁), z - z₁) =
      m.comp chainInj (x - x₁, z - z₁) + m.comp chainInjY (g x - g x₁) := by
    rw [comp_apply, comp_apply, ← map_add]
    congr 1
    simp
  have hgd : ‖g x - g x₁‖ ≤ L * d := hLip.trans (by gcongr)
  have hβ : -m.comp chainInjY (g x - g x₁) ≤ ‖m.comp chainInjY‖ * (L * d) :=
    (neg_le_abs _).trans (((m.comp chainInjY).le_opNorm _).trans (by gcongr))
  simp only [Prod.mk_sub_mk, Prod.norm_mk]
  calc m.comp chainInj (x - x₁, z - z₁)
      = m ((x - x₁, g x - g x₁), z - z₁) - m.comp chainInjY (g x - g x₁) := by
        rw [hsplit]; ring
    _ ≤ ε / c * (c * d) + ‖m.comp chainInjY‖ * (L * d) := by
        have := hp.trans (mul_le_mul_of_nonneg_left hnorm (by positivity))
        linarith
    _ = (L * ‖m.comp chainInjY‖ + ε) * d := by field_simp; ring

variable [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ Z]

omit [FiniteDimensional ℝ Y] in
/-- Equality in (3.31) of [Mordukhovich 2018] for a locally Lipschitz inner mapping (proof of
Thm. 3.11(iii)): if `g` is Lipschitz continuous on a neighborhood of `x̄` and `gph(F ∘ g)` is
locally closed around `(x̄, z̄)`, then `(x*, 0) ∈ D*Φ(x̄, g x̄, z̄)(z*)` iff
`x* ∈ D*(F ∘ g)(x̄, z̄)(z*)`. The implication `⇐` is (3.31) (inner semicontinuity of `S` being
automatic); `⇒` uses the `ω`-normal representation of Thm. 1.6. -/
theorem coprod_zero_mem_coderiv_chainGraphMap_iff {g : X → Y} {F : Y → Set Z} {x₀ : X}
    {z₀ : Z} {U : Set X} (hU : U ∈ 𝓝 x₀) {L : ℝ≥0} (hg : LipschitzOnWith L g U)
    (hloc : ∃ r > 0, IsClosed (graph (fun x ↦ F (g x)) ∩ closedBall (x₀, z₀) r))
    {z' : StrongDual ℝ Z} {x' : StrongDual ℝ X} :
    x'.coprod 0 ∈ coderiv (chainGraphMap F fun x ↦ {g x}) (x₀, g x₀) z₀ z' ↔
      x' ∈ coderiv (fun x ↦ F (g x)) x₀ z₀ z' := by
  constructor
  · rintro ⟨hp₀, a, w, ha, hw, hmem⟩
    have hx₀ : (x₀, z₀) ∈ graph fun x ↦ F (g x) := hp₀.2
    show x'.coprod (-z') ∈ normalCone _ _
    rw [normalCone_eq_outerLimit_epsNormalCone hx₀ hloc]
    have ha' := tendsto_nhdsWithin_iff.1 ha
    have hax : Tendsto (fun k ↦ (a k).1.1) atTop (𝓝 x₀) :=
      ((continuous_fst.comp continuous_fst).tendsto _).comp ha'.1
    have haz : Tendsto (fun k ↦ (a k).2) atTop (𝓝 z₀) := (continuous_snd.tendsto _).comp ha'.1
    have hag : ∀ k, a k = (((a k).1.1, g (a k).1.1), (a k).2) := fun k ↦ by
      have h := (hmem k).1.1
      rw [mem_singleton_iff] at h
      rw [← h]
    have hgraph : ∀ k, (a k).2 ∈ F (g (a k).1.1) := fun k ↦ by
      have h := (hmem k).1
      rw [hag k] at h
      exact h.2
    have hβ : Tendsto (fun k ↦ (L : ℝ) * ‖(w k).comp chainInjY‖) atTop (𝓝 0) := by
      have h1 := tendsto_dual_comp hw (tendsto_const_nhds (x := (chainInjY : Y →L[ℝ] _)))
      have h0 : ((x'.coprod (0 : StrongDual ℝ Y)).coprod (-z')).comp
          (chainInjY : Y →L[ℝ] (X × Y) × Z) = 0 := by ext; simp
      rw [h0] at h1
      simpa using h1.norm.const_mul (L : ℝ)
    refine mem_outerLimit_of_eventually (fun k ↦ (((a k).1.1, (a k).2), (L : ℝ) * ‖(w k).comp
      chainInjY‖)) (fun k ↦ (w k).comp chainInj) ?_ ?_ ?_
    · exact (tendsto_nhdsWithin_iff.2 ⟨hax.prodMk_nhds haz, Eventually.of_forall hgraph⟩).prodMk
        (tendsto_nhdsWithin_iff.2 ⟨hβ, Eventually.of_forall fun k ↦ mem_Ici.2 (by positivity)⟩)
    · have h0 : ((x'.coprod (0 : StrongDual ℝ Y)).coprod (-z')).comp
          (chainInj : X × Z →L[ℝ] (X × Y) × Z) = x'.coprod (-z') := by ext <;> simp
      have := tendsto_dual_comp hw (tendsto_const_nhds (x := (chainInj : X × Z →L[ℝ] _)))
      rwa [h0] at this
    · filter_upwards [hax.eventually (interior_mem_nhds.2 hU)] with k hk
      have hm := hmem k
      rw [hag k] at hm
      exact comp_mem_epsNormalCone_graph_comp hg (mem_interior_iff_mem_nhds.1 hk) hm
  · intro hx
    have hx' : x' ∈ coderiv (setComp F fun x ↦ {g x}) x₀ z₀ z' := by rwa [setComp_singleton]
    have hz : z₀ ∈ F (g x₀) := hx.1
    exact coprod_zero_mem_coderiv_chainGraphMap (F := F) (G := fun x ↦ {g x}) (x₀ := x₀)
      (y₀ := g x₀) (z₀ := z₀) ⟨mem_singleton _, hz⟩
      (innerSemicontinuousAt_chainAuxMap_singleton (hg.continuousOn.continuousAt hU)) hx'

/-- (3.27) of [Mordukhovich 2018] for a `C¹` inner mapping (Thm. 3.11(i) with `G = g`, as in the
proof of Thm. 3.11(iii) and of Prop. 3.19(ii)): if `g` is `C¹` around `x̄`, `gph F` is locally
closed around `(g x̄, z̄)` and (3.26) holds in the form `D*F(g x̄, z̄)(0) ∩ ker ∇g(x̄)* = {0}`,
then `D*(F ∘ g)(x̄, z̄)(z*) ⊆ ∇g(x̄)* D*F(g x̄, z̄)(z*)`. Inner semicontinuity of `S` is
automatic here. -/
theorem coderiv_comp_subset {g : X → Y} {D : X → X →L[ℝ] Y} {F : Y → Set Z} {x₀ : X} {z₀ : Z}
    (hg : ∀ᶠ x in 𝓝 x₀, HasStrictFDerivAt g (D x) x) (hDc : ContinuousAt D x₀)
    (hlocF : ∃ r > 0, IsClosed (graph F ∩ closedBall (g x₀, z₀) r))
    (hqc : ∀ w ∈ coderiv F (g x₀) z₀ 0, w.comp (D x₀) = 0 → w = 0) (z' : StrongDual ℝ Z) :
    coderiv (fun x ↦ F (g x)) x₀ z₀ z' ⊆ (fun w ↦ w.comp (D x₀)) '' coderiv F (g x₀) z₀ z' := by
  intro x' hx
  have hz : z₀ ∈ F (g x₀) := hx.1
  have hcod : ∀ w, coderiv (fun x ↦ {g x}) x₀ (g x₀) w = {w.comp (D x₀)} :=
    coderiv_of_hasFDerivAt_of_continuousAt (hg.mono fun x hx ↦ hx.hasFDerivAt) hDc
  have hx' : x' ∈ coderiv (setComp F fun x ↦ {g x}) x₀ z₀ z' := by rwa [setComp_singleton]
  have h := coderiv_setComp_subset (G := fun x ↦ {g x}) (y₀ := g x₀) ⟨rfl, hz⟩
    (innerSemicontinuousAt_chainAuxMap_singleton hg.self_of_nhds.continuousAt)
    (locallyClosed_graph_of_continuousOn hg fun x hx ↦ hx.continuousAt.continuousWithinAt) hlocF
    (fun w hw hker ↦ by
      rw [mem_coderivKer_iff, hcod, mem_singleton_iff] at hker
      exact hqc w hw hker.symm) z' hx'
  obtain ⟨w, hw, hx''⟩ := mem_iUnion₂.1 h
  rw [hcod, mem_singleton_iff] at hx''
  exact ⟨w, hw, hx''.symm⟩

/-- Thm. 3.11(iii) of [Mordukhovich 2018], graphically regular case of (3.28): if `g` is `C¹`
around `x̄`, `gph F` is locally closed around `(g x̄, z̄)`, the qualification condition (3.26)
holds and `F` is graphically regular at `(g x̄, z̄)`, then
`D*(F ∘ g)(x̄, z̄)(z*) = ∇g(x̄)* D*F(g x̄, z̄)(z*) = D̂*(F ∘ g)(x̄, z̄)(z*)`. The full-rank case of
(3.28) is `coderiv_comp_of_surjective`. -/
theorem coderiv_comp_eq_of_graphicallyRegularAt {g : X → Y} {D : X → X →L[ℝ] Y}
    {F : Y → Set Z} {x₀ : X} {z₀ : Z} (hg : ∀ᶠ x in 𝓝 x₀, HasStrictFDerivAt g (D x) x)
    (hDc : ContinuousAt D x₀) (hlocF : ∃ r > 0, IsClosed (graph F ∩ closedBall (g x₀, z₀) r))
    (hqc : ∀ w ∈ coderiv F (g x₀) z₀ 0, w.comp (D x₀) = 0 → w = 0)
    (hreg : GraphicallyRegularAt F (g x₀) z₀) (z' : StrongDual ℝ Z) :
    coderiv (fun x ↦ F (g x)) x₀ z₀ z' = (fun w ↦ w.comp (D x₀)) '' coderiv F (g x₀) z₀ z' ∧
      coderiv (fun x ↦ F (g x)) x₀ z₀ z' = regularCoderiv (fun x ↦ F (g x)) x₀ z₀ z' := by
  have h1 := coderiv_comp_subset hg hDc hlocF hqc z'
  have h2 : (fun w ↦ w.comp (D x₀)) '' coderiv F (g x₀) z₀ z' ⊆
      regularCoderiv (fun x ↦ F (g x)) x₀ z₀ z' := by
    rintro _ ⟨w, hw, rfl⟩
    rw [hreg.coderiv_eq] at hw
    have hΘ : HasFDerivAt (Prod.map g id) ((D x₀).prodMap (ContinuousLinearMap.id ℝ Z))
        (x₀, z₀) := (hg.self_of_nhds.prodMap (x₀, z₀) (hasStrictFDerivAt_id z₀)).hasFDerivAt
    have h := comp_mem_regularNormalCone_of_hasFDerivAt hΘ (T := graph fun x ↦ F (g x))
      (S := graph F) (show (x₀, z₀) ∈ graph fun x ↦ F (g x) from hw.1)
      (eventually_nhdsWithin_of_forall fun _ hp ↦ hp) hw
    have e : (w.coprod (-z')).comp ((D x₀).prodMap (ContinuousLinearMap.id ℝ Z)) =
        (w.comp (D x₀)).coprod (-z') := by ext <;> simp
    rw [e] at h
    exact h
  exact ⟨subset_antisymm h1 (h2.trans regularCoderiv_subset_coderiv),
    subset_antisymm (h1.trans h2) regularCoderiv_subset_coderiv⟩

/-- Thm. 3.11(iii) of [Mordukhovich 2018], graphically regular case: under the assumptions of
`coderiv_comp_eq_of_graphicallyRegularAt`, the composition `F ∘ g` is graphically regular at
`(x̄, z̄)`. -/
theorem graphicallyRegularAt_comp {g : X → Y} {D : X → X →L[ℝ] Y} {F : Y → Set Z} {x₀ : X}
    {z₀ : Z} (hg : ∀ᶠ x in 𝓝 x₀, HasStrictFDerivAt g (D x) x) (hDc : ContinuousAt D x₀)
    (hlocF : ∃ r > 0, IsClosed (graph F ∩ closedBall (g x₀, z₀) r))
    (hqc : ∀ w ∈ coderiv F (g x₀) z₀ 0, w.comp (D x₀) = 0 → w = 0)
    (hreg : GraphicallyRegularAt F (g x₀) z₀) : GraphicallyRegularAt (fun x ↦ F (g x)) x₀ z₀ := by
  refine subset_antisymm (fun ℓ hℓ ↦ ?_) regularNormalCone_subset_normalCone
  have hmem : ℓ.comp (inl ℝ X Z) ∈ coderiv (fun x ↦ F (g x)) x₀ z₀ (-ℓ.comp (inr ℝ X Z)) :=
    comp_inl_mem_coderiv hℓ (neg_neg _).symm
  rw [(coderiv_comp_eq_of_graphicallyRegularAt hg hDc hlocF hqc hreg _).2] at hmem
  have e : ℓ = (ℓ.comp (inl ℝ X Z)).coprod (-(-ℓ.comp (inr ℝ X Z))) := by
    rw [neg_neg, coprod_comp_inl_inr]
  rw [e]
  exact hmem

end SingleValued

section InverseImage

/-! ### Normals to inverse images, Cor. 3.13 -/

variable [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] in
/-- `Δ(x; G⁻¹(Θ)) = (Δ(·; Θ) ∘ G)(x)` [Mordukhovich 2018, proof of Cor. 3.13], where
`G⁻¹(Θ) = {x | G x ∩ Θ ≠ ∅}`. -/
theorem setComp_indicatorMap (G : X → Set Y) (Θ : Set Y) :
    setComp (indicatorMap Θ : Y → Set ℝ) G = indicatorMap {x | (G x ∩ Θ).Nonempty} := by
  funext x
  ext z
  simp only [mem_setComp_iff, indicatorMap, mem_ofPred_eq]
  constructor
  · rintro ⟨y, hy, hΘ, rfl⟩
    exact ⟨⟨y, hy, hΘ⟩, rfl⟩
  · rintro ⟨⟨y, hy, hΘ⟩, rfl⟩
    exact ⟨y, hy, hΘ, rfl⟩

/-- Cor. 3.13 of [Mordukhovich 2018] (normals to inverse images): let `gph G` and `Θ` be closed,
let `x ↦ G x ∩ Θ` be locally bounded around `x̄`, and let the qualification condition (3.32)
`N(ȳ; Θ) ∩ ker D*G(x̄, ȳ) = {0}` hold for every `ȳ ∈ G(x̄) ∩ Θ`. Then
`N(x̄; G⁻¹(Θ)) ⊆ ⋃ {D*G(x̄, ȳ)(y*) | y* ∈ N(ȳ; Θ), ȳ ∈ G(x̄) ∩ Θ}`. As in the book, this is
Thm. 3.11(ii) for `Δ(·; Θ) ∘ G = Δ(·; G⁻¹(Θ))` with Exercise 1.59. -/
theorem normalCone_preimage_setValued_subset {G : X → Set Y} {Θ : Set Y} {x₀ : X}
    (hG : IsClosed (graph G)) (hΘ : IsClosed Θ) (hbd : LocallyBoundedAt (fun x ↦ G x ∩ Θ) x₀)
    (hqc : ∀ y ∈ G x₀ ∩ Θ, ∀ w ∈ normalCone Θ y, w ∈ coderivKer G x₀ y → w = 0) :
    normalCone {x | (G x ∩ Θ).Nonempty} x₀ ⊆
      ⋃ y ∈ G x₀ ∩ Θ, ⋃ w ∈ normalCone Θ y, coderiv G x₀ y w := by
  intro v hv
  rw [← coderiv_indicatorMap (Q := ℝ) _ x₀ 0, ← setComp_indicatorMap] at hv
  obtain ⟨U, hU, hb⟩ := hbd
  have h := coderiv_setComp_subset_iUnion (F := (indicatorMap Θ : Y → Set ℝ)) (z₀ := 0) hG
    (by rw [graph_indicatorMap]; exact hΘ.prod isClosed_singleton)
    ⟨U ×ˢ univ, prod_mem_nhds hU univ_mem, hb.subset (iUnion₂_subset fun q hq y hy ↦
      mem_biUnion hq.1 ⟨hy.1, hy.2.1⟩)⟩
    (fun y hy w hw hker ↦ hqc y ⟨hy.1, hy.2.1⟩ w (by rwa [coderiv_indicatorMap] at hw) hker) 0 hv
  simp only [mem_iUnion, coderiv_indicatorMap] at h
  obtain ⟨y, hy, w, hw, hvw⟩ := h
  exact mem_biUnion (x := y) ⟨hy.1, hy.2.1⟩ (mem_biUnion hw hvw)

/-- Cor. 3.13 of [Mordukhovich 2018], metrically regular case: the qualification condition
(3.32) is automatic when `G` is metrically regular around `(x̄, ȳ)` for every
`ȳ ∈ G(x̄) ∩ Θ` (Thm. 3.3(ii), `MetricallyRegularAt.coderivKer_eq`). -/
theorem normalCone_preimage_setValued_subset_of_metricallyRegular {G : X → Set Y} {Θ : Set Y}
    {x₀ : X} (hG : IsClosed (graph G)) (hΘ : IsClosed Θ)
    (hbd : LocallyBoundedAt (fun x ↦ G x ∩ Θ) x₀)
    (hmr : ∀ y ∈ G x₀ ∩ Θ, MetricallyRegularAt G x₀ y) :
    normalCone {x | (G x ∩ Θ).Nonempty} x₀ ⊆
      ⋃ y ∈ G x₀ ∩ Θ, ⋃ w ∈ normalCone Θ y, coderiv G x₀ y w :=
  normalCone_preimage_setValued_subset hG hΘ hbd fun y hy w _ hker ↦ by
    rwa [(hmr y hy).coderivKer_eq hy.1] at hker

/-- Cor. 3.13 of [Mordukhovich 2018], equality for smooth mappings and normally regular sets:
let `g` be `C¹` around `x̄`, let `Θ` be locally closed around `ȳ = g x̄` and normally regular at
`ȳ`, and let (3.32) hold: `N(ȳ; Θ) ∩ ker ∇g(x̄)* = {0}`. Then
`N(x̄; g⁻¹(Θ)) = ∇g(x̄)* N(ȳ; Θ)` and `g⁻¹(Θ)` is normally regular at `x̄`. As in the book, this
is Thm. 3.11(iii) for `Δ(·; Θ) ∘ g`. When `∇g(x̄)` has full rank, the equality holds with no
assumption on `Θ`: Exercise 1.54(ii), `normalCone_preimage_of_surjective_of_finiteDimensional`. -/
theorem normalCone_preimage_eq_of_normallyRegularAt {g : X → Y} {D : X → X →L[ℝ] Y} {Θ : Set Y}
    {x₀ : X} (hg : ∀ᶠ x in 𝓝 x₀, HasStrictFDerivAt g (D x) x) (hDc : ContinuousAt D x₀)
    (hloc : ∃ r > 0, IsClosed (Θ ∩ closedBall (g x₀) r))
    (hqc : ∀ w ∈ normalCone Θ (g x₀), w.comp (D x₀) = 0 → w = 0)
    (hreg : NormallyRegularAt Θ (g x₀)) :
    normalCone (g ⁻¹' Θ) x₀ = (fun w ↦ w.comp (D x₀)) '' normalCone Θ (g x₀) ∧
      NormallyRegularAt (g ⁻¹' Θ) x₀ := by
  have e : (fun x ↦ (indicatorMap Θ : Y → Set ℝ) (g x)) = indicatorMap (g ⁻¹' Θ) := rfl
  have hlocF : ∃ r > 0, IsClosed (graph (indicatorMap Θ : Y → Set ℝ) ∩ closedBall (g x₀, 0) r) := by
    rw [graph_indicatorMap]
    exact locallyClosed_prod hloc ⟨1, one_pos, isClosed_singleton.inter isClosed_closedBall⟩
  have hqc' : ∀ w ∈ coderiv (indicatorMap Θ : Y → Set ℝ) (g x₀) 0 0, w.comp (D x₀) = 0 → w = 0 :=
    fun w hw ↦ hqc w (by rwa [coderiv_indicatorMap] at hw)
  have hregF := (graphicallyRegularAt_indicatorMap_iff (Q := ℝ)).2 hreg
  have h1 := (coderiv_comp_eq_of_graphicallyRegularAt hg hDc hlocF hqc' hregF 0).1
  have h2 := graphicallyRegularAt_comp hg hDc hlocF hqc' hregF
  rw [e, coderiv_indicatorMap, coderiv_indicatorMap] at h1
  rw [e, graphicallyRegularAt_indicatorMap_iff] at h2
  exact ⟨h1, h2⟩

end InverseImage

end VariationalAnalysis
