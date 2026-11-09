/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import VariationalAnalysis.SCD.Product
import VariationalAnalysis.SCD.GraphLipschitz

/-!
# Geometric derivability of graphically Lipschitzian graphs

Lemma 3.7 of [Gfrerer–Mandlmayr–Outrata–Valdman 2023]: if `F` is graphically Lipschitzian at
`(x̄, ȳ)`, then near `(x̄, ȳ)` the graph of `F` is geometrically derivable at every point of
`O_F`, and every tangent cone to `gph F` that is a subspace has dimension `n`. These are the two
hypotheses of the product rule [Gfrerer–Mandlmayr–Outrata–Valdman 2023, Prop. 3.5], so products
with a graphically Lipschitzian factor (for instance a Lipschitz single-valued mapping) satisfy
the product formulas for `𝒮` and `𝒮*` with equality.

## Main results

* `geometricallyDerivableAt_of_seq`: a sequential criterion for geometric derivability.
* `geometricallyDerivableAt_graph_of_hasFDerivAt`: the graph of a mapping differentiable at `u`
  is geometrically derivable at `(u, f u)` (cf. [Rockafellar–Wets 1998, Prop. 8.41]).
* `GeometricallyDerivableAt.of_inter_eq_preimage`: geometric derivability transfers along a local
  change of coordinates with invertible strict derivative.
* `IsGraphLipschitzTransform.geometricallyDerivableAt`,
  `GraphicallyLipschitzianAt.exists_nhds_derivable_finrank`: Lemma 3.7(i)–(ii) of
  [Gfrerer–Mandlmayr–Outrata–Valdman 2023].
* `graphDerivableAtSmoothPoints_of_graphicallyLipschitzian`,
  `hasFullDimTangentSubspaces_of_graphicallyLipschitzian`: the hypotheses of Prop. 3.5 for
  mappings that are graphically Lipschitzian at every point of their graph.
* `graphicallyLipschitzianAt_of_lipschitzOnWith`: Lipschitz single-valued mappings are
  graphically Lipschitzian.
* `IsSCDMapping.prodMap_of_graphicallyLipschitzian_left`,
  `scDeriv_prodMap_of_graphicallyLipschitzian_left`,
  `scCoderiv_prodMap_of_graphicallyLipschitzian_left` (and `_right`): Prop. 3.5 with equality in
  (3.8)–(3.10) when one factor is graphically Lipschitzian at every point of its graph.
-/

open Filter Topology Set Module Asymptotics
open scoped NNReal

namespace VariationalAnalysis

/-! ### Geometric derivability via sequences -/

section General

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

/-- First-order expansion along sequences: if `yₖ → x` and `αₖ (yₖ - x) → u`, then
`αₖ (g yₖ - g x) → ∇g(x) u`. -/
theorem tendsto_smul_sub_apply_of_hasFDerivAt {g : X → Y} {A : X →L[ℝ] Y} {x : X}
    (hg : HasFDerivAt g A x) {y : ℕ → X} {α : ℕ → ℝ} {u : X} (hy : Tendsto y atTop (𝓝 x))
    (hu : Tendsto (fun k ↦ α k • (y k - x)) atTop (𝓝 u)) :
    Tendsto (fun k ↦ α k • (g (y k) - g x)) atTop (𝓝 (A u)) := by
  have h1 : (fun k ↦ g (y k) - g x - A (y k - x)) =o[atTop] (fun k ↦ y k - x) :=
    hg.isLittleO.comp_tendsto hy
  have h2 : (fun k ↦ α k • (g (y k) - g x - A (y k - x))) =o[atTop]
      (fun k ↦ α k • (y k - x)) :=
    (isBigO_refl α atTop).smul_isLittleO h1
  have h3 : Tendsto (fun k ↦ α k • (g (y k) - g x - A (y k - x))) atTop (𝓝 0) :=
    (isLittleO_one_iff ℝ).1 (h2.trans_isBigO (hu.isBigO_one ℝ))
  have h4 : Tendsto (fun k ↦ A (α k • (y k - x))) atTop (𝓝 (A u)) :=
    (A.continuous.tendsto u).comp hu
  have := h3.add h4
  simp only [zero_add] at this
  refine this.congr fun k ↦ ?_
  rw [map_smul, map_sub, smul_sub, smul_sub, smul_sub]
  abel

/-- If `tₖ ↓ 0` and `tₖ⁻¹ (aₖ - x) → u`, then `aₖ → x`. -/
theorem tendsto_of_tendsto_inv_smul_sub {t : ℕ → ℝ} (ht : Tendsto t atTop (𝓝[>] 0))
    {a : ℕ → X} {x u : X} (ha : Tendsto (fun k ↦ (t k)⁻¹ • (a k - x)) atTop (𝓝 u)) :
    Tendsto a atTop (𝓝 x) := by
  have ht0 : Tendsto t atTop (𝓝 0) := tendsto_nhds_of_tendsto_nhdsWithin ht
  have hpos : ∀ᶠ k in atTop, 0 < t k := (tendsto_nhdsWithin_iff.1 ht).2
  have h1 : Tendsto (fun k ↦ t k • ((t k)⁻¹ • (a k - x))) atTop (𝓝 ((0 : ℝ) • u)) :=
    ht0.smul ha
  rw [zero_smul] at h1
  have h2 : Tendsto (fun k ↦ a k - x) atTop (𝓝 0) := by
    refine h1.congr' ?_
    filter_upwards [hpos] with k hk
    rw [smul_smul, mul_inv_cancel₀ hk.ne', one_smul]
  simpa using h2.add_const x

/-- A sequential criterion for geometric derivability: `Ω` is geometrically derivable at `x` if
for every tangent `u` and every `tₖ ↓ 0` there are `aₖ ∈ Ω` (eventually) with
`tₖ⁻¹ (aₖ - x) → u`. -/
theorem geometricallyDerivableAt_of_seq {Ω : Set X} {x : X}
    (h : ∀ u ∈ contingentCone Ω x, ∀ t : ℕ → ℝ, Tendsto t atTop (𝓝[>] 0) →
      ∃ a : ℕ → X, (∀ᶠ k in atTop, a k ∈ Ω) ∧
        Tendsto (fun k ↦ (t k)⁻¹ • (a k - x)) atTop (𝓝 u)) :
    GeometricallyDerivableAt Ω x := by
  intro u hu
  rw [tendsto_iff_seq_tendsto]
  intro t ht
  obtain ⟨a, haΩ, halim⟩ := h u hu t ht
  have hpos : ∀ᶠ k in atTop, 0 < t k := (tendsto_nhdsWithin_iff.1 ht).2
  have hbound : Tendsto (fun k ↦ ‖u - (t k)⁻¹ • (a k - x)‖) atTop (𝓝 0) := by
    have := ((tendsto_const_nhds (x := u)).sub halim).norm
    simpa using this
  refine squeeze_zero' ?_ ?_ hbound
  · filter_upwards [hpos] with k hk
    exact div_nonneg Metric.infDist_nonneg hk.le
  · filter_upwards [hpos, haΩ] with k hk hak
    show Metric.infDist (x + t k • u) Ω / t k ≤ _
    rw [div_le_iff₀ hk]
    calc Metric.infDist (x + t k • u) Ω ≤ dist (x + t k • u) (a k) :=
          Metric.infDist_le_dist_of_mem hak
      _ = ‖t k • (u - (t k)⁻¹ • (a k - x))‖ := by
          rw [dist_eq_norm, smul_sub, smul_smul, mul_inv_cancel₀ hk.ne', one_smul]
          congr 1; abel
      _ = ‖u - (t k)⁻¹ • (a k - x)‖ * t k := by
          rw [norm_smul, Real.norm_of_nonneg hk.le, mul_comm]

variable [CompleteSpace X] [CompleteSpace Y]

omit [CompleteSpace Y] in
/-- Geometric derivability transfers along a local change of coordinates: if `Ω = Φ⁻¹(Ω')` near
`x ∈ Ω`, `Φ` has an invertible strict derivative at `x` and `Ω'` is geometrically derivable at
`Φ x`, then `Ω` is geometrically derivable at `x`. -/
theorem GeometricallyDerivableAt.of_inter_eq_preimage {Ω W : Set X} {Ω' : Set Y} {Φ : X → Y}
    {e : X ≃L[ℝ] Y} {x : X} (hd : GeometricallyDerivableAt Ω' (Φ x)) (hW : W ∈ 𝓝 x)
    (hloc : Ω ∩ W = Φ ⁻¹' Ω' ∩ W) (hΦ : HasStrictFDerivAt Φ (e : X →L[ℝ] Y) x) (hx : x ∈ Ω) :
    GeometricallyDerivableAt Ω x := by
  have hxΩ' : Φ x ∈ Ω' := by
    have : x ∈ Ω ∩ W := ⟨hx, mem_of_mem_nhds hW⟩
    rw [hloc] at this
    exact this.1
  refine geometricallyDerivableAt_of_seq fun z hz t ht ↦ ?_
  rw [contingentCone_congr_of_inter_eq hW hloc] at hz
  have hez := (mem_contingentCone_preimage_iff hΦ).1 hz
  obtain ⟨b, hb, hblim⟩ := hd.exists_seq hxΩ' hez ht
  have hb0 : Tendsto b atTop (𝓝 (Φ x)) := tendsto_of_tendsto_inv_smul_sub ht hblim
  have hψx : hΦ.localInverse Φ e x (Φ x) = x := hΦ.localInverse_apply_image
  have hψc : Tendsto (fun k ↦ hΦ.localInverse Φ e x (b k)) atTop (𝓝 x) := by
    have := (hΦ.localInverse_continuousAt.tendsto).comp hb0
    rw [hψx] at this
    exact this
  refine ⟨fun k ↦ hΦ.localInverse Φ e x (b k), ?_, ?_⟩
  · filter_upwards [hb0.eventually hΦ.eventually_right_inverse, hψc.eventually hW]
      with k hk hkW
    have : hΦ.localInverse Φ e x (b k) ∈ Φ ⁻¹' Ω' ∩ W :=
      ⟨by show Φ (hΦ.localInverse Φ e x (b k)) ∈ Ω'; rw [hk]; exact hb k, hkW⟩
    rw [← hloc] at this
    exact this.1
  · have := tendsto_smul_sub_apply_of_hasFDerivAt hΦ.to_localInverse.hasFDerivAt hb0 hblim
    rwa [hψx, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] at this

end General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : E → Set E} {p q : E × E}

/-! ### Graphs of differentiable mappings -/

omit [FiniteDimensional ℝ E] in
/-- The graph of a mapping differentiable at `u` is geometrically derivable at `(u, f u)`
(cf. [Rockafellar–Wets 1998, Prop. 8.41]): the tangent `(w, ∇f(u) w)` is attained along the
points `(u + t w, f(u + t w))`. -/
theorem geometricallyDerivableAt_graph_of_hasFDerivAt {f : E → E} {A : E →L[ℝ] E} {u : E}
    (hf : HasFDerivAt f A u) :
    GeometricallyDerivableAt (graph fun x ↦ ({f x} : Set E)) (u, f u) := by
  refine geometricallyDerivableAt_of_seq fun z hz t ht ↦ ?_
  rw [contingentCone_graph_of_hasFDerivAt hf] at hz
  obtain ⟨w, v⟩ := z
  have hv : v = A w := by simpa [LinearMap.mem_graph_iff] using hz
  subst hv
  have hpos : ∀ᶠ k in atTop, 0 < t k := (tendsto_nhdsWithin_iff.1 ht).2
  have hw : Tendsto (fun k ↦ (t k)⁻¹ • ((u + t k • w) - u)) atTop (𝓝 w) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hpos] with k hk
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hk.ne', one_smul]
  have hy : Tendsto (fun k ↦ u + t k • w) atTop (𝓝 u) := tendsto_of_tendsto_inv_smul_sub ht hw
  have hfy := tendsto_smul_sub_apply_of_hasFDerivAt hf hy hw
  refine ⟨fun k ↦ (u + t k • w, f (u + t k • w)), Eventually.of_forall fun k ↦ rfl, ?_⟩
  refine (hw.prodMk_nhds hfy).congr fun k ↦ ?_
  rfl

/-! ### Lemma 3.7 of [Gfrerer–Mandlmayr–Outrata–Valdman 2023] -/

namespace IsGraphLipschitzTransform

variable {W : Set (E × E)} {Φ : E × E → E × E} {D : E × E → (E × E) →L[ℝ] (E × E)}
  {U : Set E} {f : E → E} {K : ℝ≥0}

/-- Lemma 3.7(i) of [Gfrerer–Mandlmayr–Outrata–Valdman 2023]: if `q ∈ gph F ∩ W` is a point of
graphical smoothness, then `gph F` is geometrically derivable at `q` (via
[Gfrerer–Outrata 2022, Remark 3.18] and [Rockafellar–Wets 1998, Prop. 8.41]). -/
theorem geometricallyDerivableAt (h : IsGraphLipschitzTransform F W Φ D U f K)
    (hq : q ∈ graph F) (hqW : q ∈ W) (hs : GraphicallySmoothAt F q) :
    GeometricallyDerivableAt (graph F) q := by
  obtain ⟨hW', hloc⟩ := h.nhds_inter_eq hq hqW
  obtain ⟨e, he⟩ := h.exists_equiv q hqW
  have hΦ : HasStrictFDerivAt Φ (e : (E × E) →L[ℝ] (E × E)) q := he ▸ h.hasStrictFDerivAt q hqW
  obtain ⟨u, -, hΦq⟩ := h.exists_apply_eq hq hqW
  have hdiff := (h.graphicallySmoothAt_iff hq hqW).1 hs
  rw [hΦq] at hdiff
  have hd : GeometricallyDerivableAt (graph fun x ↦ ({f x} : Set E)) (Φ q) := by
    rw [hΦq]; exact geometricallyDerivableAt_graph_of_hasFDerivAt hdiff.hasFDerivAt
  exact hd.of_inter_eq_preimage hW' hloc hΦ hq

end IsGraphLipschitzTransform

/-- Lemma 3.7 of [Gfrerer–Mandlmayr–Outrata–Valdman 2023]: if `F` is graphically Lipschitzian at
`p`, there is a neighborhood `W` of `p` such that for all `q ∈ gph F ∩ W`, (i) `gph F` is
geometrically derivable at `q` whenever `q ∈ O_F`, and (ii) every tangent cone
`T_{gph F}(q)` which is a subspace has dimension `n`. -/
theorem GraphicallyLipschitzianAt.exists_nhds_derivable_finrank
    (h : GraphicallyLipschitzianAt F p) :
    ∃ W ∈ 𝓝 p, ∀ q ∈ graph F ∩ W,
      (GraphicallySmoothAt F q → GeometricallyDerivableAt (graph F) q) ∧
      ∀ L : Submodule ℝ (E × E), (L : Set (E × E)) = contingentCone (graph F) q →
        finrank ℝ L = finrank ℝ E := by
  obtain ⟨-, W, Φ, D, U, f, K, hpW, hT⟩ := h
  exact ⟨W, hT.isOpen_W.mem_nhds hpW, fun q ⟨hq, hqW⟩ ↦
    ⟨hT.geometricallyDerivableAt hq hqW, fun L hL ↦
      hT.finrank_eq_of_coe_eq_contingentCone hq hqW hL⟩⟩

/-- Lemma 3.7(i) of [Gfrerer–Mandlmayr–Outrata–Valdman 2023] at the reference point. -/
theorem GraphicallyLipschitzianAt.geometricallyDerivableAt (h : GraphicallyLipschitzianAt F p)
    (hs : GraphicallySmoothAt F p) : GeometricallyDerivableAt (graph F) p := by
  obtain ⟨W, hW, hWp⟩ := h.exists_nhds_derivable_finrank
  exact (hWp p ⟨h.1, mem_of_mem_nhds hW⟩).1 hs

/-- If `F` is graphically Lipschitzian at every point of its graph, then `gph F` is geometrically
derivable at every point of `O_F` (the derivability hypothesis of
[Gfrerer–Mandlmayr–Outrata–Valdman 2023, Prop. 3.5]). -/
theorem graphDerivableAtSmoothPoints_of_graphicallyLipschitzian
    (hF : ∀ p ∈ graph F, GraphicallyLipschitzianAt F p) : GraphDerivableAtSmoothPoints F :=
  fun q hs ↦ (hF q hs.1).geometricallyDerivableAt hs

/-- If `F` is graphically Lipschitzian at every point of its graph, then every tangent cone to
`gph F` that is a subspace has dimension `n` (the dimension hypothesis of
[Gfrerer–Mandlmayr–Outrata–Valdman 2023, Prop. 3.5]). -/
theorem hasFullDimTangentSubspaces_of_graphicallyLipschitzian
    (hF : ∀ p ∈ graph F, GraphicallyLipschitzianAt F p) : HasFullDimTangentSubspaces F := by
  intro q hq L hL
  obtain ⟨W, hW, hWq⟩ := (hF q hq).exists_nhds_derivable_finrank
  exact (hWq q ⟨hq, mem_of_mem_nhds hW⟩).2 L hL

/-- A mapping that is graphically Lipschitzian at every point of its graph is an SCD mapping
[Gfrerer–Outrata 2022, Prop. 3.17]. -/
theorem isSCDMapping_of_graphicallyLipschitzian
    (hF : ∀ p ∈ graph F, GraphicallyLipschitzianAt F p) : IsSCDMapping F := fun p hp ↦ by
  obtain ⟨W, hW, hWp⟩ := (hF p hp).hasSCDPropertyAround
  exact hWp p ⟨hp, mem_of_mem_nhds hW⟩

/-! ### Lipschitz single-valued mappings -/

omit [FiniteDimensional ℝ E] in
/-- A single-valued mapping that is Lipschitz on an open set `U` is graphically Lipschitzian at
every point `(u, f u)` with `u ∈ U`, with the identity as transformation mapping. -/
theorem graphicallyLipschitzianAt_of_lipschitzOnWith {f : E → E} {U : Set E} {K : ℝ≥0}
    (hU : IsOpen U) (hf : LipschitzOnWith K f U) {u : E} (hu : u ∈ U) :
    GraphicallyLipschitzianAt (fun x ↦ ({f x} : Set E)) (u, f u) := by
  refine ⟨mem_singleton _, U ×ˢ univ, id, fun _ ↦ ContinuousLinearMap.id ℝ (E × E), U, f, K,
    mk_mem_prod hu trivial, ?_⟩
  exact
    { isOpen_W := hU.prod isOpen_univ
      isOpen_U := hU
      hasStrictFDerivAt := fun q _ ↦ hasStrictFDerivAt_id q
      continuousOn := continuousOn_const
      exists_equiv := fun _ _ ↦ ⟨ContinuousLinearEquiv.refl ℝ (E × E), rfl⟩
      injOn := Function.injective_id.injOn
      lipschitzOnWith := hf
      image_eq := image_id _ }

omit [FiniteDimensional ℝ E] in
/-- A Lipschitz single-valued mapping is graphically Lipschitzian at every point of its graph. -/
theorem LipschitzWith.graphicallyLipschitzianAt {f : E → E} {K : ℝ≥0} (hf : LipschitzWith K f)
    (p : E × E) (hp : p ∈ graph fun x ↦ ({f x} : Set E)) :
    GraphicallyLipschitzianAt (fun x ↦ ({f x} : Set E)) p := by
  obtain ⟨x, y⟩ := p
  have hy : y = f x := hp
  subst hy
  exact graphicallyLipschitzianAt_of_lipschitzOnWith isOpen_univ (hf.lipschitzOnWith) trivial

/-! ### Products with a graphically Lipschitzian factor -/

section Product

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
  [FiniteDimensional ℝ E₁] [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
  [FiniteDimensional ℝ E₂]
variable {F₁ : E₁ → Set E₁} {F₂ : E₂ → Set E₂}

local notation "𝔼" => WithLp 2 (E₁ × E₂)

/-- [Gfrerer–Mandlmayr–Outrata–Valdman 2023, Prop. 3.5 with Lemma 3.7]: if `F₁` is graphically
Lipschitzian at every point of its graph and `F₂` is an SCD mapping, then `F₁ × F₂` is an SCD
mapping. -/
theorem IsSCDMapping.prodMap_of_graphicallyLipschitzian_left
    (h₁ : ∀ p ∈ graph F₁, GraphicallyLipschitzianAt F₁ p) (hF₂ : IsSCDMapping F₂) :
    IsSCDMapping (VariationalAnalysis.prodMap F₁ F₂) :=
  (isSCDMapping_of_graphicallyLipschitzian h₁).prodMap hF₂
    (Or.inl (graphDerivableAtSmoothPoints_of_graphicallyLipschitzian h₁))

/-- The version of `IsSCDMapping.prodMap_of_graphicallyLipschitzian_left` with the graphically
Lipschitzian factor on the right. -/
theorem IsSCDMapping.prodMap_of_graphicallyLipschitzian_right (hF₁ : IsSCDMapping F₁)
    (h₂ : ∀ p ∈ graph F₂, GraphicallyLipschitzianAt F₂ p) :
    IsSCDMapping (VariationalAnalysis.prodMap F₁ F₂) :=
  hF₁.prodMap (isSCDMapping_of_graphicallyLipschitzian h₂)
    (Or.inr (graphDerivableAtSmoothPoints_of_graphicallyLipschitzian h₂))

/-- Equality in (3.8) of [Gfrerer–Mandlmayr–Outrata–Valdman 2023] when `F₁` is graphically
Lipschitzian at every point of its graph (no assumption on `F₂`). -/
theorem graphicallySmoothAt_prodMap_iff_of_graphicallyLipschitzian_left
    (h₁ : ∀ p ∈ graph F₁, GraphicallyLipschitzianAt F₁ p) (p : 𝔼 × 𝔼) :
    GraphicallySmoothAt (prodMap F₁ F₂) p ↔
      GraphicallySmoothAt F₁ (graphShuffle p).1 ∧ GraphicallySmoothAt F₂ (graphShuffle p).2 :=
  graphicallySmoothAt_prodMap_iff
    (Or.inl (graphDerivableAtSmoothPoints_of_graphicallyLipschitzian h₁))
    (Or.inl (hasFullDimTangentSubspaces_of_graphicallyLipschitzian h₁)) p

/-- Equality in (3.9) of [Gfrerer–Mandlmayr–Outrata–Valdman 2023, Prop. 3.5] when `F₁` is
graphically Lipschitzian at every point of its graph (no assumption on `F₂`):
`𝒮(F₁ × F₂)(x, y) = {L₁ × L₂ | Lᵢ ∈ 𝒮Fᵢ(xᵢ, yᵢ)}`. -/
theorem scDeriv_prodMap_of_graphicallyLipschitzian_left
    (h₁ : ∀ p ∈ graph F₁, GraphicallyLipschitzianAt F₁ p) (p : 𝔼 × 𝔼) :
    scDeriv (prodMap F₁ F₂) p =
      image2 prodSubspace (scDeriv F₁ (graphShuffle p).1) (scDeriv F₂ (graphShuffle p).2) :=
  scDeriv_prodMap (Or.inl (graphDerivableAtSmoothPoints_of_graphicallyLipschitzian h₁))
    (Or.inl (hasFullDimTangentSubspaces_of_graphicallyLipschitzian h₁)) p

/-- Equality in (3.10) of [Gfrerer–Mandlmayr–Outrata–Valdman 2023, Prop. 3.5] when `F₁` is
graphically Lipschitzian at every point of its graph (no assumption on `F₂`). -/
theorem scCoderiv_prodMap_of_graphicallyLipschitzian_left
    (h₁ : ∀ p ∈ graph F₁, GraphicallyLipschitzianAt F₁ p) (p : 𝔼 × 𝔼) :
    scCoderiv (prodMap F₁ F₂) p =
      image2 prodSubspace (scCoderiv F₁ (graphShuffle p).1)
        (scCoderiv F₂ (graphShuffle p).2) :=
  scCoderiv_prodMap (Or.inl (graphDerivableAtSmoothPoints_of_graphicallyLipschitzian h₁))
    (Or.inl (hasFullDimTangentSubspaces_of_graphicallyLipschitzian h₁)) p

/-- The version of `graphicallySmoothAt_prodMap_iff_of_graphicallyLipschitzian_left` with the
graphically Lipschitzian factor on the right. -/
theorem graphicallySmoothAt_prodMap_iff_of_graphicallyLipschitzian_right
    (h₂ : ∀ p ∈ graph F₂, GraphicallyLipschitzianAt F₂ p) (p : 𝔼 × 𝔼) :
    GraphicallySmoothAt (prodMap F₁ F₂) p ↔
      GraphicallySmoothAt F₁ (graphShuffle p).1 ∧ GraphicallySmoothAt F₂ (graphShuffle p).2 :=
  graphicallySmoothAt_prodMap_iff
    (Or.inr (graphDerivableAtSmoothPoints_of_graphicallyLipschitzian h₂))
    (Or.inr (hasFullDimTangentSubspaces_of_graphicallyLipschitzian h₂)) p

/-- The version of `scDeriv_prodMap_of_graphicallyLipschitzian_left` with the graphically
Lipschitzian factor on the right. -/
theorem scDeriv_prodMap_of_graphicallyLipschitzian_right
    (h₂ : ∀ p ∈ graph F₂, GraphicallyLipschitzianAt F₂ p) (p : 𝔼 × 𝔼) :
    scDeriv (prodMap F₁ F₂) p =
      image2 prodSubspace (scDeriv F₁ (graphShuffle p).1) (scDeriv F₂ (graphShuffle p).2) :=
  scDeriv_prodMap (Or.inr (graphDerivableAtSmoothPoints_of_graphicallyLipschitzian h₂))
    (Or.inr (hasFullDimTangentSubspaces_of_graphicallyLipschitzian h₂)) p

/-- The version of `scCoderiv_prodMap_of_graphicallyLipschitzian_left` with the graphically
Lipschitzian factor on the right. -/
theorem scCoderiv_prodMap_of_graphicallyLipschitzian_right
    (h₂ : ∀ p ∈ graph F₂, GraphicallyLipschitzianAt F₂ p) (p : 𝔼 × 𝔼) :
    scCoderiv (prodMap F₁ F₂) p =
      image2 prodSubspace (scCoderiv F₁ (graphShuffle p).1)
        (scCoderiv F₂ (graphShuffle p).2) :=
  scCoderiv_prodMap (Or.inr (graphDerivableAtSmoothPoints_of_graphicallyLipschitzian h₂))
    (Or.inr (hasFullDimTangentSubspaces_of_graphicallyLipschitzian h₂)) p

end Product

end VariationalAnalysis
