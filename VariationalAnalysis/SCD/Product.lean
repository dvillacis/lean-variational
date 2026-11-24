/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.MetricSpace.HausdorffDistance
import VariationalAnalysis.SCD.Basic

/-!
# Products of SCD mappings

For `F₁ : E₁ ⇉ E₁` and `F₂ : E₂ ⇉ E₂` consider `F(x₁, x₂) = F₁(x₁) × F₂(x₂)`
[Gfrerer–Mandlmayr–Outrata–Valdman 2023, (3.5)] with two factors. The SCD machinery needs an
inner product on the domain, so `F` acts on `WithLp 2 (E₁ × E₂)`. Its graph is the preimage of
`gph F₁ × gph F₂` under the shuffle `((x₁, x₂), (y₁, y₂)) ↦ ((x₁, y₁), (x₂, y₂))`.

## Main declarations

* `GeometricallyDerivableAt Ω x`: every tangent `u ∈ T_Ω(x)` is derivable,
  `dist(x + t u, Ω) / t → 0` as `t ↓ 0` [Gfrerer–Mandlmayr–Outrata–Valdman 2023, Def. 2.1(i)].
* `prodMap F₁ F₂`: the product mapping (3.5); `graphShuffle`: the shuffle of coordinates.
* `prodSubspace L₁ L₂`: `{((u₁, u₂), (v₁, v₂)) | (uᵢ, vᵢ) ∈ Lᵢ}`.
* `HasFullDimTangentSubspaces F`: every tangent cone to `gph F` that is a subspace has
  dimension `dim E` (the extra hypothesis for equality in Prop. 3.5).

## Main results

* `contingentCone_prod_subset`, `contingentCone_prod_eq`: `T_{Ω₁ × Ω₂} ⊆ T_{Ω₁} × T_{Ω₂}`
  (cf. [Rockafellar–Wets 1998, Prop. 6.41]), with equality when one factor is geometrically
  derivable.
* `GrassTendsto.prodSubspace`, `adjointSubspace_prodSubspace`: products of subspaces converge
  componentwise, and `(L₁ × L₂)* = L₁* × L₂*`.
* `GraphicallySmoothAt.exists_submodule_fst`, `GraphicallySmoothAt.exists_submodule_snd`,
  `graphicallySmoothAt_prodMap`: Lemma 3.4 of [Gfrerer–Mandlmayr–Outrata–Valdman 2023].
* `prodSubspace_mem_scDeriv`, `prodSubspace_mem_scCoderiv`, `IsSCDMapping.prodMap`: Prop. 3.5,
  inclusions (3.8)–(3.10) and the SCD property of `F`.
* `graphicallySmoothAt_prodMap_iff`, `scDeriv_prodMap`, `scCoderiv_prodMap`: equality in
  (3.8)–(3.10) under the dimension hypothesis.
-/

open Filter Topology Set Module
open scoped InnerProductSpace

namespace VariationalAnalysis

/-! ### Contingent cones of images and products -/

section Cones

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

/-- Continuous linear maps send tangents to tangents of the image. -/
theorem map_mem_contingentCone (A : X →L[ℝ] Y) {Ω : Set X} {Ω' : Set Y} (hA : MapsTo A Ω Ω')
    {p w : X} (hw : w ∈ contingentCone Ω p) : A w ∈ contingentCone Ω' (A p) := by
  obtain ⟨hp, x, α, hxα, hx, hlim⟩ := hw
  refine ⟨hA hp, fun k ↦ A (x k), α, fun k ↦ ⟨hA (hxα k).1, (hxα k).2⟩,
    (A.continuous.tendsto _).comp hx, ?_⟩
  have := (A.continuous.tendsto _).comp hlim
  simpa [Function.comp_def, map_sub, map_smul] using this

/-- Contingent cones of preimages under continuous linear equivalences. -/
theorem contingentCone_preimage_equiv (σ : X ≃L[ℝ] Y) (Ω : Set Y) (p : X) :
    contingentCone (σ ⁻¹' Ω) p = σ ⁻¹' contingentCone Ω (σ p) := by
  ext w
  refine ⟨fun hw ↦ map_mem_contingentCone (σ : X →L[ℝ] Y) (fun _ hx ↦ hx) hw, fun hw ↦ ?_⟩
  have := map_mem_contingentCone (σ.symm : Y →L[ℝ] X) (Ω' := σ ⁻¹' Ω)
    (fun x hx ↦ by simpa using hx) hw
  simpa using this

variable {Ω₁ : Set X} {Ω₂ : Set Y} {a : X} {b : Y}

/-- `T_{Ω₁ × Ω₂}(a, b) ⊆ T_{Ω₁}(a) × T_{Ω₂}(b)` [Gfrerer–Mandlmayr–Outrata–Valdman 2023, (3.7)],
cf. [Rockafellar–Wets 1998, Prop. 6.41]. -/
theorem contingentCone_prod_subset :
    contingentCone (Ω₁ ×ˢ Ω₂) (a, b) ⊆ contingentCone Ω₁ a ×ˢ contingentCone Ω₂ b :=
  fun _ hw ↦ ⟨map_mem_contingentCone (ContinuousLinearMap.fst ℝ X Y) (fun _ hx ↦ hx.1) hw,
    map_mem_contingentCone (ContinuousLinearMap.snd ℝ X Y) (fun _ hx ↦ hx.2) hw⟩

theorem mk_zero_mem_contingentCone_prod_iff (hb : b ∈ Ω₂) {t : X} :
    (t, 0) ∈ contingentCone (Ω₁ ×ˢ Ω₂) (a, b) ↔ t ∈ contingentCone Ω₁ a := by
  refine ⟨fun h ↦ (contingentCone_prod_subset h).1, fun h ↦ ?_⟩
  obtain ⟨ha, x, α, hxα, hx, hlim⟩ := h
  refine ⟨⟨ha, hb⟩, fun k ↦ (x k, b), α, fun k ↦ ⟨⟨(hxα k).1, hb⟩, (hxα k).2⟩,
    hx.prodMk_nhds tendsto_const_nhds, ?_⟩
  have : (fun k ↦ α k • ((x k, b) - (a, b))) = fun k ↦ (α k • (x k - a), (0 : Y)) := by
    funext k; simp
  rw [this]
  exact hlim.prodMk_nhds tendsto_const_nhds

theorem zero_mk_mem_contingentCone_prod_iff (ha : a ∈ Ω₁) {t : Y} :
    (0, t) ∈ contingentCone (Ω₁ ×ˢ Ω₂) (a, b) ↔ t ∈ contingentCone Ω₂ b := by
  refine ⟨fun h ↦ (contingentCone_prod_subset h).2, fun h ↦ ?_⟩
  obtain ⟨hb, x, α, hxα, hx, hlim⟩ := h
  refine ⟨⟨ha, hb⟩, fun k ↦ (a, x k), α, fun k ↦ ⟨⟨ha, (hxα k).1⟩, (hxα k).2⟩,
    tendsto_const_nhds.prodMk_nhds hx, ?_⟩
  have : (fun k ↦ α k • ((a, x k) - (a, b))) = fun k ↦ ((0 : X), α k • (x k - b)) := by
    funext k; simp
  rw [this]
  exact tendsto_const_nhds.prodMk_nhds hlim

end Cones

/-! ### Geometric derivability -/

section Derivable

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

/-- `Ω` is geometrically derivable at `x` if every tangent `u ∈ T_Ω(x)` is derivable:
`dist(x + t u, Ω) / t → 0` as `t ↓ 0` [Gfrerer–Mandlmayr–Outrata–Valdman 2023, Def. 2.1(i)]. -/
def GeometricallyDerivableAt (Ω : Set X) (x : X) : Prop :=
  ∀ u ∈ contingentCone Ω x,
    Tendsto (fun t : ℝ ↦ Metric.infDist (x + t • u) Ω / t) (𝓝[>] 0) (𝓝 0)

/-- Along any `tₖ ↓ 0`, a derivable tangent is the limit of `(zₖ - x) / tₖ` with `zₖ ∈ Ω`. -/
theorem GeometricallyDerivableAt.exists_seq {Ω : Set X} {x u : X}
    (h : GeometricallyDerivableAt Ω x) (hx : x ∈ Ω) (hu : u ∈ contingentCone Ω x) {t : ℕ → ℝ}
    (ht : Tendsto t atTop (𝓝[>] 0)) :
    ∃ z : ℕ → X, (∀ k, z k ∈ Ω) ∧ Tendsto (fun k ↦ (t k)⁻¹ • (z k - x)) atTop (𝓝 u) := by
  have key : ∀ k, ∃ z ∈ Ω, 0 < t k →
      dist (x + t k • u) z < Metric.infDist (x + t k • u) Ω + t k ^ 2 := by
    intro k
    by_cases hk : 0 < t k
    · obtain ⟨z, hz, hd⟩ := (Metric.infDist_lt_iff ⟨x, hx⟩).1
        (lt_add_of_pos_right (Metric.infDist (x + t k • u) Ω) (pow_pos hk 2))
      exact ⟨z, hz, fun _ ↦ hd⟩
    · exact ⟨x, hx, fun h ↦ absurd h hk⟩
  choose z hz hzd using key
  refine ⟨z, hz, ?_⟩
  have hpos : ∀ᶠ k in atTop, 0 < t k := (tendsto_nhdsWithin_iff.1 ht).2
  have ht0 : Tendsto t atTop (𝓝 0) := tendsto_nhds_of_tendsto_nhdsWithin ht
  have hbound : Tendsto (fun k ↦ Metric.infDist (x + t k • u) Ω / t k + t k) atTop (𝓝 0) := by
    simpa using ((h u hu).comp ht).add ht0
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hbound
  filter_upwards [hpos] with k hk
  have hne : t k ≠ 0 := hk.ne'
  have heq : (t k)⁻¹ • (z k - x) - u = (t k)⁻¹ • (z k - (x + t k • u)) := by
    rw [smul_sub, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hne, one_smul]; abel
  rw [heq, norm_smul, norm_inv, Real.norm_of_nonneg hk.le, ← dist_eq_norm, dist_comm]
  have := hzd k hk
  calc (t k)⁻¹ * dist (x + t k • u) (z k)
      ≤ (t k)⁻¹ * (Metric.infDist (x + t k • u) Ω + t k ^ 2) :=
        mul_le_mul_of_nonneg_left this.le (inv_nonneg.2 hk.le)
    _ = Metric.infDist (x + t k • u) Ω / t k + t k := by field_simp

variable {Ω₁ : Set X} {Ω₂ : Set Y} {a : X} {b : Y}

theorem contingentCone_prod_eq_of_derivable_left (ha : a ∈ Ω₁) (hb : b ∈ Ω₂)
    (h : GeometricallyDerivableAt Ω₁ a) :
    contingentCone (Ω₁ ×ˢ Ω₂) (a, b) = contingentCone Ω₁ a ×ˢ contingentCone Ω₂ b := by
  refine subset_antisymm contingentCone_prod_subset ?_
  rintro ⟨u₁, u₂⟩ ⟨hu₁, hu₂⟩
  rw [contingentCone_eq_outerLimit hb] at hu₂
  obtain ⟨t, v, ht, hv, hmem⟩ := hu₂
  obtain ⟨z, hz, hzlim⟩ := h.exists_seq ha hu₁ ht
  rw [contingentCone_eq_outerLimit (show (a, b) ∈ Ω₁ ×ˢ Ω₂ from ⟨ha, hb⟩)]
  refine ⟨t, fun k ↦ ((t k)⁻¹ • (z k - a), v k), ht, hzlim.prodMk_nhds hv, fun k ↦ ?_⟩
  obtain ⟨_, ⟨y, hy, rfl⟩, hyv⟩ := Set.mem_smul_set.1 (hmem k)
  refine Set.mem_smul_set.2 ⟨(z k - a, y - b), ⟨(z k, y), ⟨hz k, hy⟩, rfl⟩, ?_⟩
  change _ = ((t k)⁻¹ • (z k - a), v k)
  rw [← hyv]; rfl

theorem contingentCone_prod_eq_of_derivable_right (ha : a ∈ Ω₁) (hb : b ∈ Ω₂)
    (h : GeometricallyDerivableAt Ω₂ b) :
    contingentCone (Ω₁ ×ˢ Ω₂) (a, b) = contingentCone Ω₁ a ×ˢ contingentCone Ω₂ b := by
  have hswap := contingentCone_preimage_equiv (ContinuousLinearEquiv.prodComm ℝ X Y)
    (Ω₂ ×ˢ Ω₁) (a, b)
  have hpre : (ContinuousLinearEquiv.prodComm ℝ X Y) ⁻¹' (Ω₂ ×ˢ Ω₁) = Ω₁ ×ˢ Ω₂ := by
    ext ⟨x, y⟩; simp [and_comm]
  rw [hpre] at hswap
  rw [hswap]
  ext ⟨u₁, u₂⟩
  simp only [mem_preimage, ContinuousLinearEquiv.prodComm_apply, Prod.swap_prod_mk]
  rw [contingentCone_prod_eq_of_derivable_left hb ha h]
  simp [and_comm]

/-- Equality in (3.7) of [Gfrerer–Mandlmayr–Outrata–Valdman 2023] when one factor is
geometrically derivable (cf. [Rockafellar–Wets 1998, Prop. 6.41]). -/
theorem contingentCone_prod_eq (ha : a ∈ Ω₁) (hb : b ∈ Ω₂)
    (h : GeometricallyDerivableAt Ω₁ a ∨ GeometricallyDerivableAt Ω₂ b) :
    contingentCone (Ω₁ ×ˢ Ω₂) (a, b) = contingentCone Ω₁ a ×ˢ contingentCone Ω₂ b :=
  h.elim (contingentCone_prod_eq_of_derivable_left ha hb)
    (contingentCone_prod_eq_of_derivable_right ha hb)

end Derivable

/-! ### Hypotheses of Prop. 3.5 -/

section Hypotheses

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- `gph F` is geometrically derivable at every point of `O_F`, the derivability hypothesis of
[Gfrerer–Mandlmayr–Outrata–Valdman 2023, Prop. 3.5]. -/
def GraphDerivableAtSmoothPoints (F : E → Set E) : Prop :=
  ∀ q, GraphicallySmoothAt F q → GeometricallyDerivableAt (graph F) q

/-- Every tangent cone to `gph F` that is a subspace has dimension `dim E`, the hypothesis for
equality in [Gfrerer–Mandlmayr–Outrata–Valdman 2023, Prop. 3.5]. -/
def HasFullDimTangentSubspaces (F : E → Set E) : Prop :=
  ∀ q ∈ graph F, ∀ L : Submodule ℝ (E × E), (L : Set (E × E)) = contingentCone (graph F) q →
    finrank ℝ L = finrank ℝ E

end Hypotheses

/-! ### The product mapping -/

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
  [FiniteDimensional ℝ E₁] [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
  [FiniteDimensional ℝ E₂]

local notation "𝔼" => WithLp 2 (E₁ × E₂)

/-- The product mapping `F(x₁, x₂) = F₁(x₁) × F₂(x₂)`
[Gfrerer–Mandlmayr–Outrata–Valdman 2023, (3.5)], on the Euclidean product. -/
def prodMap (F₁ : E₁ → Set E₁) (F₂ : E₂ → Set E₂) : 𝔼 → Set 𝔼 :=
  fun x ↦ {y | y.fst ∈ F₁ x.fst ∧ y.snd ∈ F₂ x.snd}

/-- The shuffle `((x₁, x₂), (y₁, y₂)) ↦ ((x₁, y₁), (x₂, y₂))`. -/
noncomputable def graphShuffle : (𝔼 × 𝔼) ≃L[ℝ] (E₁ × E₁) × (E₂ × E₂) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).prodCongr
    (WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂)).trans
    (ContinuousLinearEquiv.prodProdProdComm ℝ E₁ E₂ E₁ E₂)

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] in
@[simp] theorem graphShuffle_apply (w : 𝔼 × 𝔼) :
    graphShuffle w = ((w.1.fst, w.2.fst), (w.1.snd, w.2.snd)) := rfl

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] in
theorem graphShuffle_symm_apply (q : (E₁ × E₁) × (E₂ × E₂)) :
    graphShuffle.symm q = (WithLp.toLp 2 (q.1.1, q.2.1), WithLp.toLp 2 (q.1.2, q.2.2)) := by
  rw [ContinuousLinearEquiv.symm_apply_eq]; rfl

variable {F₁ : E₁ → Set E₁} {F₂ : E₂ → Set E₂}

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] in
theorem graph_prodMap : graph (prodMap F₁ F₂) = graphShuffle ⁻¹' (graph F₁ ×ˢ graph F₂) := rfl

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] in
theorem mem_graph_prodMap_iff (p : 𝔼 × 𝔼) :
    p ∈ graph (prodMap F₁ F₂) ↔ (graphShuffle p).1 ∈ graph F₁ ∧ (graphShuffle p).2 ∈ graph F₂ :=
  Iff.rfl

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] in
/-- (3.6) of [Gfrerer–Mandlmayr–Outrata–Valdman 2023]. -/
theorem contingentCone_graph_prodMap (p : 𝔼 × 𝔼) :
    contingentCone (graph (prodMap F₁ F₂)) p =
      graphShuffle ⁻¹' contingentCone (graph F₁ ×ˢ graph F₂) (graphShuffle p) := by
  rw [graph_prodMap, contingentCone_preimage_equiv]

/-! ### Products of subspaces -/

/-- The subspace `{((u₁, u₂), (v₁, v₂)) | (u₁, v₁) ∈ L₁, (u₂, v₂) ∈ L₂}`. -/
noncomputable def prodSubspace (L₁ : Submodule ℝ (E₁ × E₁)) (L₂ : Submodule ℝ (E₂ × E₂)) :
    Submodule ℝ (𝔼 × 𝔼) :=
  (L₁.prod L₂).comap (graphShuffle (E₁ := E₁) (E₂ := E₂)).toLinearEquiv.toLinearMap

variable {L₁ : Submodule ℝ (E₁ × E₁)} {L₂ : Submodule ℝ (E₂ × E₂)}

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] in
theorem mem_prodSubspace_iff {w : 𝔼 × 𝔼} :
    w ∈ prodSubspace L₁ L₂ ↔ (w.1.fst, w.2.fst) ∈ L₁ ∧ (w.1.snd, w.2.snd) ∈ L₂ := Iff.rfl

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] in
theorem coe_prodSubspace :
    (prodSubspace L₁ L₂ : Set (𝔼 × 𝔼)) = graphShuffle ⁻¹' ((L₁ : Set _) ×ˢ (L₂ : Set _)) := rfl

theorem finrank_submodule_prod (L₁ : Submodule ℝ (E₁ × E₁)) (L₂ : Submodule ℝ (E₂ × E₂)) :
    finrank ℝ (L₁.prod L₂) = finrank ℝ L₁ + finrank ℝ L₂ := by
  have h : LinearMap.range (L₁.subtype.prodMap L₂.subtype) = L₁.prod L₂ := by
    rw [LinearMap.range_prodMap, Submodule.range_subtype, Submodule.range_subtype]
  rw [← h, LinearMap.finrank_range_of_inj, Module.finrank_prod]
  rw [LinearMap.coe_prodMap]
  exact Subtype.val_injective.prodMap Subtype.val_injective

theorem finrank_prodSubspace (L₁ : Submodule ℝ (E₁ × E₁)) (L₂ : Submodule ℝ (E₂ × E₂)) :
    finrank ℝ (prodSubspace L₁ L₂) = finrank ℝ L₁ + finrank ℝ L₂ := by
  rw [prodSubspace, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq,
    finrank_submodule_prod]

theorem finrank_withLp_prod : finrank ℝ 𝔼 = finrank ℝ E₁ + finrank ℝ E₂ := by
  rw [(WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).toLinearEquiv.finrank_eq, Module.finrank_prod]

/-- Products of convergent sequences of subspaces converge in the Grassmannian metric. -/
theorem GrassTendsto.prodSubspace {L₁ : ℕ → Submodule ℝ (E₁ × E₁)}
    {L₂ : ℕ → Submodule ℝ (E₂ × E₂)} {M₁ : Submodule ℝ (E₁ × E₁)} {M₂ : Submodule ℝ (E₂ × E₂)}
    {n₁ n₂ : ℕ} (hn₁ : ∀ k, finrank ℝ (L₁ k) = n₁) (hn₂ : ∀ k, finrank ℝ (L₂ k) = n₂)
    (h₁ : GrassTendsto L₁ M₁) (h₂ : GrassTendsto L₂ M₂) :
    GrassTendsto (fun k ↦ VariationalAnalysis.prodSubspace (L₁ k) (L₂ k))
      (VariationalAnalysis.prodSubspace M₁ M₂) := by
  refine grassTendsto_of_outerLimit_subset (n := n₁ + n₂)
    (fun k ↦ by rw [finrank_prodSubspace, hn₁, hn₂])
    (by rw [finrank_prodSubspace, h₁.finrank_eq hn₁, h₂.finrank_eq hn₂]) ?_
  rintro w ⟨a, v, ha, hv, hmem⟩
  have hσ := (graphShuffle.continuous.tendsto _).comp hv
  exact mem_prodSubspace_iff.2 ⟨(h₁.comp ha).mem_of_tendsto
      (fun k ↦ (mem_prodSubspace_iff.1 (hmem k)).1) ((continuous_fst.tendsto _).comp hσ),
    (h₂.comp ha).mem_of_tendsto (fun k ↦ (mem_prodSubspace_iff.1 (hmem k)).2)
      ((continuous_snd.tendsto _).comp hσ)⟩

/-- `(L₁ × L₂)* = L₁* × L₂*` [Gfrerer–Mandlmayr–Outrata–Valdman 2023, proof of Prop. 3.5]. -/
theorem adjointSubspace_prodSubspace (L₁ : Submodule ℝ (E₁ × E₁))
    (L₂ : Submodule ℝ (E₂ × E₂)) :
    adjointSubspace (prodSubspace L₁ L₂) =
      prodSubspace (adjointSubspace L₁) (adjointSubspace L₂) := by
  have hle : prodSubspace (adjointSubspace L₁) (adjointSubspace L₂) ≤
      adjointSubspace (prodSubspace L₁ L₂) := by
    intro w hw
    refine mem_adjointSubspace_iff.2 fun q hq ↦ ?_
    have h₁ := inner_eq_of_mem_adjointSubspace (mem_prodSubspace_iff.1 hw).1
      (mem_prodSubspace_iff.1 hq).1
    have h₂ := inner_eq_of_mem_adjointSubspace (mem_prodSubspace_iff.1 hw).2
      (mem_prodSubspace_iff.1 hq).2
    simp only [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd] at h₁ h₂ ⊢
    rw [h₁, h₂]
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  have hd₁ : finrank ℝ L₁ ≤ 2 * finrank ℝ E₁ := by
    have := Submodule.finrank_le L₁; rw [Module.finrank_prod] at this; omega
  have hd₂ : finrank ℝ L₂ ≤ 2 * finrank ℝ E₂ := by
    have := Submodule.finrank_le L₂; rw [Module.finrank_prod] at this; omega
  rw [finrank_prodSubspace, finrank_adjointSubspace, finrank_adjointSubspace,
    finrank_adjointSubspace, finrank_prodSubspace, finrank_withLp_prod]
  omega

/-! ### Lemma 3.4: smooth points of the product -/

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] in
theorem shuffle_symm_mk_zero_mem_contingentCone_iff {p : 𝔼 × 𝔼}
    (hp : p ∈ graph (prodMap F₁ F₂)) {t : E₁ × E₁} :
    graphShuffle.symm (t, 0) ∈ contingentCone (graph (prodMap F₁ F₂)) p ↔
      t ∈ contingentCone (graph F₁) (graphShuffle p).1 := by
  rw [contingentCone_graph_prodMap, mem_preimage, ContinuousLinearEquiv.apply_symm_apply]
  exact mk_zero_mem_contingentCone_prod_iff ((mem_graph_prodMap_iff p).1 hp).2

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] in
theorem shuffle_symm_zero_mk_mem_contingentCone_iff {p : 𝔼 × 𝔼}
    (hp : p ∈ graph (prodMap F₁ F₂)) {t : E₂ × E₂} :
    graphShuffle.symm (0, t) ∈ contingentCone (graph (prodMap F₁ F₂)) p ↔
      t ∈ contingentCone (graph F₂) (graphShuffle p).2 := by
  rw [contingentCone_graph_prodMap, mem_preimage, ContinuousLinearEquiv.apply_symm_apply]
  exact zero_mk_mem_contingentCone_prod_iff ((mem_graph_prodMap_iff p).1 hp).1

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] in
/-- Lemma 3.4(i) of [Gfrerer–Mandlmayr–Outrata–Valdman 2023]: if `p ∈ O_F`, then
`T_{gph F₁}(x₁, y₁)` is a subspace. -/
theorem GraphicallySmoothAt.exists_submodule_fst {p : 𝔼 × 𝔼}
    (h : GraphicallySmoothAt (prodMap F₁ F₂) p) :
    ∃ L : Submodule ℝ (E₁ × E₁),
      (L : Set (E₁ × E₁)) = contingentCone (graph F₁) (graphShuffle p).1 := by
  refine ⟨(tangentSubspace (prodMap F₁ F₂) p).comap
    ((graphShuffle (E₁ := E₁) (E₂ := E₂)).symm.toLinearEquiv.toLinearMap ∘ₗ
      LinearMap.inl ℝ (E₁ × E₁) (E₂ × E₂)), ?_⟩
  ext t
  rw [SetLike.mem_coe, Submodule.mem_comap, ← shuffle_symm_mk_zero_mem_contingentCone_iff h.1,
    ← h.mem_tangentSubspace_iff]
  rfl

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] in
/-- Lemma 3.4(i) of [Gfrerer–Mandlmayr–Outrata–Valdman 2023] for the second factor. -/
theorem GraphicallySmoothAt.exists_submodule_snd {p : 𝔼 × 𝔼}
    (h : GraphicallySmoothAt (prodMap F₁ F₂) p) :
    ∃ L : Submodule ℝ (E₂ × E₂),
      (L : Set (E₂ × E₂)) = contingentCone (graph F₂) (graphShuffle p).2 := by
  refine ⟨(tangentSubspace (prodMap F₁ F₂) p).comap
    ((graphShuffle (E₁ := E₁) (E₂ := E₂)).symm.toLinearEquiv.toLinearMap ∘ₗ
      LinearMap.inr ℝ (E₁ × E₁) (E₂ × E₂)), ?_⟩
  ext t
  rw [SetLike.mem_coe, Submodule.mem_comap, ← shuffle_symm_zero_mk_mem_contingentCone_iff h.1,
    ← h.mem_tangentSubspace_iff]
  rfl

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] in
/-- (3.7) of [Gfrerer–Mandlmayr–Outrata–Valdman 2023] with equality when one of the graphs is
geometrically derivable. -/
theorem contingentCone_graph_prodMap_eq {p : 𝔼 × 𝔼} (hp : p ∈ graph (prodMap F₁ F₂))
    (hd : GeometricallyDerivableAt (graph F₁) (graphShuffle p).1 ∨
      GeometricallyDerivableAt (graph F₂) (graphShuffle p).2) :
    contingentCone (graph (prodMap F₁ F₂)) p = graphShuffle ⁻¹'
      (contingentCone (graph F₁) (graphShuffle p).1 ×ˢ
        contingentCone (graph F₂) (graphShuffle p).2) := by
  rw [contingentCone_graph_prodMap, ← contingentCone_prod_eq ((mem_graph_prodMap_iff p).1 hp).1
    ((mem_graph_prodMap_iff p).1 hp).2 hd]

/-- Lemma 3.4(ii) of [Gfrerer–Mandlmayr–Outrata–Valdman 2023]: if `(xᵢ, yᵢ) ∈ O_{Fᵢ}` and one of
the graphs is geometrically derivable there, then `p ∈ O_F`. -/
theorem graphicallySmoothAt_prodMap {p : 𝔼 × 𝔼}
    (h₁ : GraphicallySmoothAt F₁ (graphShuffle p).1)
    (h₂ : GraphicallySmoothAt F₂ (graphShuffle p).2)
    (hd : GeometricallyDerivableAt (graph F₁) (graphShuffle p).1 ∨
      GeometricallyDerivableAt (graph F₂) (graphShuffle p).2) :
    GraphicallySmoothAt (prodMap F₁ F₂) p := by
  have hp : p ∈ graph (prodMap F₁ F₂) := (mem_graph_prodMap_iff p).2 ⟨h₁.1, h₂.1⟩
  refine ⟨hp, prodSubspace (tangentSubspace F₁ (graphShuffle p).1)
    (tangentSubspace F₂ (graphShuffle p).2), ?_, ?_⟩
  · rw [finrank_prodSubspace, h₁.finrank_tangentSubspace, h₂.finrank_tangentSubspace,
      finrank_withLp_prod]
  · rw [contingentCone_graph_prodMap_eq hp hd, coe_prodSubspace, h₁.coe_tangentSubspace,
      h₂.coe_tangentSubspace]

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] in
/-- At a point of `O_F` the tangent subspace is the product of the tangent cones of the factors
(no derivability is needed once `T_{gph F}(p)` is a subspace). -/
theorem GraphicallySmoothAt.tangentSubspace_prodMap_eq {p : 𝔼 × 𝔼}
    (h : GraphicallySmoothAt (prodMap F₁ F₂) p)
    (hL₁ : (L₁ : Set (E₁ × E₁)) = contingentCone (graph F₁) (graphShuffle p).1)
    (hL₂ : (L₂ : Set (E₂ × E₂)) = contingentCone (graph F₂) (graphShuffle p).2) :
    tangentSubspace (prodMap F₁ F₂) p = prodSubspace L₁ L₂ := by
  apply SetLike.coe_injective
  rw [h.coe_tangentSubspace, coe_prodSubspace, hL₁, hL₂]
  ext w
  constructor
  · intro hw
    rw [contingentCone_graph_prodMap] at hw
    exact contingentCone_prod_subset hw
  · rintro ⟨hw₁, hw₂⟩
    have hdecomp : w = graphShuffle.symm ((graphShuffle w).1, 0) +
        graphShuffle.symm (0, (graphShuffle w).2) := by
      rw [← map_add, Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta,
        ContinuousLinearEquiv.symm_apply_apply]
    have h₁ := (shuffle_symm_mk_zero_mem_contingentCone_iff h.1).2 hw₁
    have h₂ := (shuffle_symm_zero_mk_mem_contingentCone_iff h.1).2 hw₂
    rw [← h.mem_tangentSubspace_iff] at h₁ h₂ ⊢
    rw [hdecomp]
    exact add_mem h₁ h₂

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] in
theorem GraphicallySmoothAt.tangentSubspace_prodMap {p : 𝔼 × 𝔼}
    (h : GraphicallySmoothAt (prodMap F₁ F₂) p)
    (h₁ : GraphicallySmoothAt F₁ (graphShuffle p).1)
    (h₂ : GraphicallySmoothAt F₂ (graphShuffle p).2) :
    tangentSubspace (prodMap F₁ F₂) p = prodSubspace (tangentSubspace F₁ (graphShuffle p).1)
      (tangentSubspace F₂ (graphShuffle p).2) :=
  h.tangentSubspace_prodMap_eq h₁.coe_tangentSubspace h₂.coe_tangentSubspace

/-- Converse of Lemma 3.4(ii) under the dimension hypothesis: points of `O_F` have components in
`O_{F₁}` and `O_{F₂}` (equality in (3.8) of [Gfrerer–Mandlmayr–Outrata–Valdman 2023]). -/
theorem GraphicallySmoothAt.prodMap_components {p : 𝔼 × 𝔼}
    (h : GraphicallySmoothAt (prodMap F₁ F₂) p)
    (hdim : HasFullDimTangentSubspaces F₁ ∨ HasFullDimTangentSubspaces F₂) :
    GraphicallySmoothAt F₁ (graphShuffle p).1 ∧ GraphicallySmoothAt F₂ (graphShuffle p).2 := by
  obtain ⟨L₁, hL₁⟩ := h.exists_submodule_fst
  obtain ⟨L₂, hL₂⟩ := h.exists_submodule_snd
  have hp := (mem_graph_prodMap_iff p).1 h.1
  have hdimF := h.finrank_tangentSubspace
  rw [h.tangentSubspace_prodMap_eq hL₁ hL₂, finrank_prodSubspace, finrank_withLp_prod] at hdimF
  have hd : finrank ℝ L₁ = finrank ℝ E₁ ∧ finrank ℝ L₂ = finrank ℝ E₂ := by
    rcases hdim with hdim | hdim
    · have := hdim _ hp.1 L₁ hL₁; omega
    · have := hdim _ hp.2 L₂ hL₂; omega
  exact ⟨⟨hp.1, L₁, hd.1, hL₁⟩, ⟨hp.2, L₂, hd.2, hL₂⟩⟩

/-- Equality in (3.8) of [Gfrerer–Mandlmayr–Outrata–Valdman 2023]:
`O_F = {p | (x₁, y₁) ∈ O_{F₁}, (x₂, y₂) ∈ O_{F₂}}`. -/
theorem graphicallySmoothAt_prodMap_iff
    (hd : GraphDerivableAtSmoothPoints F₁ ∨ GraphDerivableAtSmoothPoints F₂)
    (hdim : HasFullDimTangentSubspaces F₁ ∨ HasFullDimTangentSubspaces F₂) (p : 𝔼 × 𝔼) :
    GraphicallySmoothAt (prodMap F₁ F₂) p ↔
      GraphicallySmoothAt F₁ (graphShuffle p).1 ∧ GraphicallySmoothAt F₂ (graphShuffle p).2 :=
  ⟨fun h ↦ h.prodMap_components hdim, fun ⟨h₁, h₂⟩ ↦
    graphicallySmoothAt_prodMap h₁ h₂ (hd.imp (fun h ↦ h _ h₁) (fun h ↦ h _ h₂))⟩

/-! ### Prop. 3.5: SC derivatives of the product -/

/-- (3.9) of [Gfrerer–Mandlmayr–Outrata–Valdman 2023, Prop. 3.5]:
`L₁ ∈ 𝒮F₁(x₁, y₁)`, `L₂ ∈ 𝒮F₂(x₂, y₂)` ⇒ `L₁ × L₂ ∈ 𝒮F(x, y)`. -/
theorem prodSubspace_mem_scDeriv
    (hd : GraphDerivableAtSmoothPoints F₁ ∨ GraphDerivableAtSmoothPoints F₂) {p : 𝔼 × 𝔼}
    (h₁ : L₁ ∈ scDeriv F₁ (graphShuffle p).1) (h₂ : L₂ ∈ scDeriv F₂ (graphShuffle p).2) :
    prodSubspace L₁ L₂ ∈ scDeriv (prodMap F₁ F₂) p := by
  obtain ⟨q₁, hq₁, hq₁lim, hT₁⟩ := h₁
  obtain ⟨q₂, hq₂, hq₂lim, hT₂⟩ := h₂
  have hgr : ∀ k, graphShuffle (graphShuffle.symm (q₁ k, q₂ k)) = (q₁ k, q₂ k) := fun k ↦
    graphShuffle.apply_symm_apply _
  have hsm₁ : ∀ k, GraphicallySmoothAt F₁ (graphShuffle (graphShuffle.symm (q₁ k, q₂ k))).1 :=
    fun k ↦ by rw [hgr]; exact hq₁ k
  have hsm₂ : ∀ k, GraphicallySmoothAt F₂ (graphShuffle (graphShuffle.symm (q₁ k, q₂ k))).2 :=
    fun k ↦ by rw [hgr]; exact hq₂ k
  have hsm : ∀ k, GraphicallySmoothAt (prodMap F₁ F₂) (graphShuffle.symm (q₁ k, q₂ k)) :=
    fun k ↦ graphicallySmoothAt_prodMap (hsm₁ k) (hsm₂ k)
      (hd.imp (fun h ↦ h _ (hsm₁ k)) (fun h ↦ h _ (hsm₂ k)))
  refine ⟨fun k ↦ graphShuffle.symm (q₁ k, q₂ k), hsm, ?_, ?_⟩
  · have := (graphShuffle.symm.continuous.tendsto _).comp (hq₁lim.prodMk_nhds hq₂lim)
    rwa [Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply] at this
  · have heq : (fun k ↦ tangentSubspace (prodMap F₁ F₂) (graphShuffle.symm (q₁ k, q₂ k))) =
        fun k ↦ prodSubspace (tangentSubspace F₁ (q₁ k)) (tangentSubspace F₂ (q₂ k)) := by
      funext k
      have := (hsm k).tangentSubspace_prodMap (hsm₁ k) (hsm₂ k)
      rwa [hgr] at this
    have := GrassTendsto.prodSubspace (fun k ↦ (hq₁ k).finrank_tangentSubspace)
      (fun k ↦ (hq₂ k).finrank_tangentSubspace) hT₁ hT₂
    rw [← heq] at this
    exact this

/-- (3.10) of [Gfrerer–Mandlmayr–Outrata–Valdman 2023, Prop. 3.5]:
`L₁ ∈ 𝒮*F₁(x₁, y₁)`, `L₂ ∈ 𝒮*F₂(x₂, y₂)` ⇒ `L₁ × L₂ ∈ 𝒮*F(x, y)`. -/
theorem prodSubspace_mem_scCoderiv
    (hd : GraphDerivableAtSmoothPoints F₁ ∨ GraphDerivableAtSmoothPoints F₂) {p : 𝔼 × 𝔼}
    (h₁ : L₁ ∈ scCoderiv F₁ (graphShuffle p).1) (h₂ : L₂ ∈ scCoderiv F₂ (graphShuffle p).2) :
    prodSubspace L₁ L₂ ∈ scCoderiv (prodMap F₁ F₂) p := by
  rw [mem_scCoderiv_iff_adjoint_mem_scDeriv, adjointSubspace_prodSubspace]
  exact prodSubspace_mem_scDeriv hd (mem_scCoderiv_iff_adjoint_mem_scDeriv.1 h₁)
    (mem_scCoderiv_iff_adjoint_mem_scDeriv.1 h₂)

theorem HasSCDPropertyAt.prodMap
    (hd : GraphDerivableAtSmoothPoints F₁ ∨ GraphDerivableAtSmoothPoints F₂) {p : 𝔼 × 𝔼}
    (h₁ : HasSCDPropertyAt F₁ (graphShuffle p).1) (h₂ : HasSCDPropertyAt F₂ (graphShuffle p).2) :
    HasSCDPropertyAt (prodMap F₁ F₂) p :=
  ⟨_, prodSubspace_mem_scDeriv hd h₁.some_mem h₂.some_mem⟩

/-- Prop. 3.5 of [Gfrerer–Mandlmayr–Outrata–Valdman 2023]: the product of SCD mappings is an SCD
mapping when all but at most one of the graphs are geometrically derivable on `O_{Fᵢ}`. -/
theorem IsSCDMapping.prodMap (hF₁ : IsSCDMapping F₁) (hF₂ : IsSCDMapping F₂)
    (hd : GraphDerivableAtSmoothPoints F₁ ∨ GraphDerivableAtSmoothPoints F₂) :
    IsSCDMapping (prodMap F₁ F₂) := fun p hp ↦
  HasSCDPropertyAt.prodMap hd (hF₁ _ ((mem_graph_prodMap_iff p).1 hp).1)
    (hF₂ _ ((mem_graph_prodMap_iff p).1 hp).2)

/-- Equality in (3.9) of [Gfrerer–Mandlmayr–Outrata–Valdman 2023, Prop. 3.5] under the dimension
hypothesis: `𝒮F(x, y) = {L₁ × L₂ | Lᵢ ∈ 𝒮Fᵢ(xᵢ, yᵢ)}`. -/
theorem scDeriv_prodMap
    (hd : GraphDerivableAtSmoothPoints F₁ ∨ GraphDerivableAtSmoothPoints F₂)
    (hdim : HasFullDimTangentSubspaces F₁ ∨ HasFullDimTangentSubspaces F₂) (p : 𝔼 × 𝔼) :
    scDeriv (prodMap F₁ F₂) p =
      image2 prodSubspace (scDeriv F₁ (graphShuffle p).1) (scDeriv F₂ (graphShuffle p).2) := by
  refine subset_antisymm ?_ ?_
  · rintro L ⟨r, hr, hrlim, hT⟩
    have hc : ∀ k, GraphicallySmoothAt F₁ (graphShuffle (r k)).1 ∧
        GraphicallySmoothAt F₂ (graphShuffle (r k)).2 := fun k ↦ (hr k).prodMap_components hdim
    have hgs : Tendsto (fun k ↦ graphShuffle (r k)) atTop (𝓝 (graphShuffle p)) :=
      (graphShuffle.continuous.tendsto _).comp hrlim
    obtain ⟨M₁, -, φ, hφ, hM₁⟩ := exists_grassTendsto_subseq
      (fun k ↦ tangentSubspace F₁ (graphShuffle (r k)).1) (n := finrank ℝ E₁)
      fun k ↦ (hc k).1.finrank_tangentSubspace
    obtain ⟨M₂, -, ψ, hψ, hM₂⟩ := exists_grassTendsto_subseq
      (fun k ↦ tangentSubspace F₂ (graphShuffle (r (φ k))).2) (n := finrank ℝ E₂)
      fun k ↦ (hc (φ k)).2.finrank_tangentSubspace
    have hM₁' : GrassTendsto (fun k ↦ tangentSubspace F₁ (graphShuffle (r (φ (ψ k)))).1) M₁ :=
      hM₁.comp hψ.tendsto_atTop
    have hprod := GrassTendsto.prodSubspace (fun k ↦ (hc (φ (ψ k))).1.finrank_tangentSubspace)
      (fun k ↦ (hc (φ (ψ k))).2.finrank_tangentSubspace) hM₁' hM₂
    have hT' : GrassTendsto (fun k ↦ tangentSubspace (prodMap F₁ F₂) (r (φ (ψ k)))) L :=
      hT.comp (hφ.comp hψ).tendsto_atTop
    have heq : (fun k ↦ tangentSubspace (prodMap F₁ F₂) (r (φ (ψ k)))) = fun k ↦
        prodSubspace (tangentSubspace F₁ (graphShuffle (r (φ (ψ k)))).1)
          (tangentSubspace F₂ (graphShuffle (r (φ (ψ k)))).2) :=
      funext fun k ↦ (hr _).tangentSubspace_prodMap (hc _).1 (hc _).2
    rw [heq] at hT'
    have hlim := hgs.comp (hφ.comp hψ).tendsto_atTop
    exact ⟨M₁, ⟨fun k ↦ (graphShuffle (r (φ (ψ k)))).1, fun k ↦ (hc _).1,
      (continuous_fst.tendsto _).comp hlim, hM₁'⟩, M₂,
      ⟨fun k ↦ (graphShuffle (r (φ (ψ k)))).2, fun k ↦ (hc _).2,
      (continuous_snd.tendsto _).comp hlim, hM₂⟩, (hT'.unique hprod).symm⟩
  · rintro _ ⟨L₁, h₁, L₂, h₂, rfl⟩
    exact prodSubspace_mem_scDeriv hd h₁ h₂

/-- Equality in (3.10) of [Gfrerer–Mandlmayr–Outrata–Valdman 2023, Prop. 3.5] under the dimension
hypothesis: `𝒮*F(x, y) = {L₁ × L₂ | Lᵢ ∈ 𝒮*Fᵢ(xᵢ, yᵢ)}`. -/
theorem scCoderiv_prodMap
    (hd : GraphDerivableAtSmoothPoints F₁ ∨ GraphDerivableAtSmoothPoints F₂)
    (hdim : HasFullDimTangentSubspaces F₁ ∨ HasFullDimTangentSubspaces F₂) (p : 𝔼 × 𝔼) :
    scCoderiv (prodMap F₁ F₂) p =
      image2 prodSubspace (scCoderiv F₁ (graphShuffle p).1)
        (scCoderiv F₂ (graphShuffle p).2) := by
  ext L
  rw [mem_scCoderiv_iff_adjoint_mem_scDeriv, scDeriv_prodMap hd hdim]
  constructor
  · rintro ⟨M₁, h₁, M₂, h₂, hM⟩
    refine ⟨adjointSubspace M₁, ?_, adjointSubspace M₂, ?_, ?_⟩
    · exact mem_scCoderiv_iff_adjoint_mem_scDeriv.2 (by rwa [adjointSubspace_adjointSubspace])
    · exact mem_scCoderiv_iff_adjoint_mem_scDeriv.2 (by rwa [adjointSubspace_adjointSubspace])
    · rw [← adjointSubspace_prodSubspace, hM, adjointSubspace_adjointSubspace]
  · rintro ⟨M₁, h₁, M₂, h₂, rfl⟩
    exact ⟨adjointSubspace M₁, mem_scCoderiv_iff_adjoint_mem_scDeriv.1 h₁, adjointSubspace M₂,
      mem_scCoderiv_iff_adjoint_mem_scDeriv.1 h₂, (adjointSubspace_prodSubspace M₁ M₂).symm⟩

end VariationalAnalysis
