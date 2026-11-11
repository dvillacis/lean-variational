/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis.SCD.Minty

/-!
# Locally maximally (hypo)monotone mappings are SCD

We prove [Gfrerer–Outrata 2022, Prop. 3.22, Cor. 3.23, Cor. 3.24] for the local notions of
[Gfrerer–Outrata 2022, Def. 3.20]. As in the paper, a mapping `F` which is locally maximally
monotone at `p`, with neighborhood `X × Y`, is replaced by a maximally monotone extension `F̃` of
`gph F ∩ (X × Y)` (Zorn's lemma, [Rockafellar–Wets, Prop. 12.6]); local maximality gives
`gph F ∩ (X × Y) = gph F̃ ∩ (X × Y)`, Minty's theorem (`IsMaximalMonotoneOp.exists_sub_mem`) gives
`rge(I + F̃) = E`, and the global results of `SCD/Monotone` apply to `F̃`.

## Main declarations

* `IsMaximalMonotoneOn F W`: `gph F ∩ W` is monotone and agrees on `W` with every monotone
  mapping containing it.
* `IsLocallyMaximalMonotoneAt`, `IsLocallyMaximalHypomonotoneAt`:
  [Gfrerer–Outrata 2022, Def. 3.20].

## Main results

* `IsMonotoneOp.exists_isMaximalMonotoneOp_ge`: every monotone mapping has a maximally monotone
  extension [Rockafellar–Wets, Prop. 12.6].
* `IsMaximalMonotoneOn.exists_isMaximalMonotoneOp`: the local version of Minty's theorem, as
  used in the proof of [Gfrerer–Outrata 2022, Prop. 3.22].
* `IsLocallyMaximalMonotoneAt.scd`: [Gfrerer–Outrata 2022, Prop. 3.22].
* `IsLocallyMaximalHypomonotoneAt.scd`: [Gfrerer–Outrata 2022, Cor. 3.23].
* `isSCDMapping_of_dense`: [Gfrerer–Outrata 2022, Cor. 3.24].
-/

open Filter Topology Set Module InnerProductSpace
open scoped InnerProductSpace NNReal

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F T : E → Set E} {W : Set (E × E)}

/-! ### Maximally monotone extensions -/

/-- Every monotone mapping has a maximally monotone extension
[Rockafellar–Wets, Prop. 12.6]. -/
theorem IsMonotoneOp.exists_isMaximalMonotoneOp_ge (hF : IsMonotoneOp F) :
    ∃ G : E → Set E, IsMaximalMonotoneOp G ∧ ∀ x, F x ⊆ G x := by
  have ih : ∀ c ⊆ {G : E → Set E | IsMonotoneOp G}, IsChain (· ≤ ·) c → ∀ H ∈ c,
      ∃ ub ∈ {G : E → Set E | IsMonotoneOp G}, ∀ K ∈ c, K ≤ ub := by
    intro c hc hchain H _
    refine ⟨fun x ↦ ⋃ K ∈ c, K x, ?_, fun K hK x y hy ↦ mem_biUnion hK hy⟩
    intro x₁ x₂ y₁ h₁ y₂ h₂
    simp only [mem_iUnion, exists_prop] at h₁ h₂
    obtain ⟨K₁, hK₁, h₁⟩ := h₁
    obtain ⟨K₂, hK₂, h₂⟩ := h₂
    have hm₁ : IsMonotoneOp K₁ := hc hK₁
    have hm₂ : IsMonotoneOp K₂ := hc hK₂
    rcases hchain.total hK₁ hK₂ with h | h
    · exact hm₂ x₁ x₂ y₁ (h x₁ h₁) y₂ h₂
    · exact hm₁ x₁ x₂ y₁ h₁ y₂ (h x₂ h₂)
  obtain ⟨G, hFG, hG⟩ := zorn_le_nonempty₀ _ ih F hF
  have hGm : IsMonotoneOp G := hG.prop
  refine ⟨G, ⟨hGm, fun x y hxy ↦ ?_⟩, hFG⟩
  have hG' : IsMonotoneOp fun x' ↦ G x' ∪ {y' | x' = x ∧ y' = y} := by
    rintro x₁ x₂ y₁ (h₁ | ⟨hx₁, hy₁⟩) y₂ (h₂ | ⟨hx₂, hy₂⟩)
    · exact hGm x₁ x₂ y₁ h₁ y₂ h₂
    · have := hxy x₁ y₁ h₁
      rwa [hx₂, hy₂, ← neg_sub y, ← neg_sub x, inner_neg_neg]
    · rw [hx₁, hy₁]
      exact hxy x₂ y₂ h₂
    · simp [hx₁, hy₁, hx₂, hy₂]
  exact hG.le_of_ge (y := fun x' ↦ G x' ∪ {y' | x' = x ∧ y' = y}) hG'
    (fun x' ↦ subset_union_left) x (Or.inr ⟨rfl, rfl⟩)

/-! ### Local maximal monotonicity -/

/-- `F` is maximally monotone on `W`: `gph F ∩ W` is monotone, and `gph F ∩ W = gph T ∩ W` for
every monotone `T` with `gph F ∩ W ⊆ gph T` [Gfrerer–Outrata 2022, Def. 3.20(1)]. -/
def IsMaximalMonotoneOn (F : E → Set E) (W : Set (E × E)) : Prop :=
  (∀ q ∈ graph F ∩ W, ∀ q' ∈ graph F ∩ W, 0 ≤ ⟪q.2 - q'.2, q.1 - q'.1⟫_ℝ) ∧
    ∀ T : E → Set E, IsMonotoneOp T → graph F ∩ W ⊆ graph T → graph F ∩ W = graph T ∩ W

/-- `F` is locally maximally monotone at `p` [Gfrerer–Outrata 2022, Def. 3.20(1)]: it is
maximally monotone on an open neighborhood `X × Y` of `p`. (We do not ask for `p ∈ gph F`.) -/
def IsLocallyMaximalMonotoneAt (F : E → Set E) (p : E × E) : Prop :=
  ∃ X Y : Set E, IsOpen X ∧ IsOpen Y ∧ p ∈ X ×ˢ Y ∧ IsMaximalMonotoneOn F (X ×ˢ Y)

/-- `F` is locally maximally hypomonotone at `p` [Gfrerer–Outrata 2022, Def. 3.20(2)]: for
some `γ ≥ 0`, `γI + F` is locally maximally monotone at `(p.1, p.2 + γ p.1)`. -/
def IsLocallyMaximalHypomonotoneAt (F : E → Set E) (p : E × E) : Prop :=
  ∃ γ : ℝ, 0 ≤ γ ∧
    IsLocallyMaximalMonotoneAt (fun x ↦ (fun y ↦ y + γ • x) '' F x) (p.1, p.2 + γ • p.1)

/-- A maximally monotone mapping is locally maximally monotone at every point. -/
theorem IsMaximalMonotoneOp.isLocallyMaximalMonotoneAt (hT : IsMaximalMonotoneOp T)
    (p : E × E) : IsLocallyMaximalMonotoneAt T p := by
  refine ⟨univ, univ, isOpen_univ, isOpen_univ, ⟨mem_univ _, mem_univ _⟩,
    fun q hq q' hq' ↦ hT.1 _ _ _ hq.1 _ hq'.1, fun T' hT' hsub ↦ ?_⟩
  rw [univ_prod_univ, inter_univ] at hsub ⊢
  rw [inter_univ]
  exact hsub.antisymm fun q hq ↦ hT.2 q.1 q.2 fun x' y' hy' ↦
    hT' q.1 x' q.2 hq y' (hsub (a := (x', y')) hy')

variable [FiniteDimensional ℝ E]

/-- The local version of Minty's theorem, as used in the proof of
[Gfrerer–Outrata 2022, Prop. 3.22]: if `F` is maximally monotone on `W`, then on `W` its graph
is the graph of a maximally monotone `F̃`; in particular `F̃` is monotone with
`rge(I + F̃) = E`. -/
theorem IsMaximalMonotoneOn.exists_isMaximalMonotoneOp (hF : IsMaximalMonotoneOn F W) :
    ∃ F' : E → Set E, IsMaximalMonotoneOp F' ∧ (∀ u, ∃ x, u - x ∈ F' x) ∧
      graph F ∩ W = graph F' ∩ W := by
  have hloc : IsMonotoneOp fun x ↦ {y | y ∈ F x ∧ (x, y) ∈ W} :=
    fun x₁ x₂ y₁ h₁ y₂ h₂ ↦ hF.1 (x₁, y₁) h₁ (x₂, y₂) h₂
  obtain ⟨F', hF', hle⟩ := hloc.exists_isMaximalMonotoneOp_ge
  exact ⟨F', hF', hF'.exists_sub_mem, hF.2 F' hF'.1 fun q hq ↦ hle q.1 ⟨hq.1, hq.2⟩⟩

/-- [Gfrerer–Outrata 2022, Prop. 3.22]: a locally maximally monotone mapping has the SCD
property around `p`, and every `L ∈ 𝒮F(q)` at nearby `q ∈ gph F` is `rge(B, I - B)` with `B`
firmly nonexpansive and `L* = rge(Bᵀ, I - Bᵀ)`. -/
theorem IsLocallyMaximalMonotoneAt.scd {p : E × E} (hF : IsLocallyMaximalMonotoneAt F p) :
    HasSCDPropertyAround F p ∧ ∃ U ∈ 𝓝 p, ∀ q ∈ graph F ∩ U, ∀ L ∈ scDeriv F q,
      ∃ B : E →L[ℝ] E, IsFirmlyNonexpansiveOp B ∧ L = mintySubspace B ∧
        adjointSubspace L = mintySubspace (ContinuousLinearMap.adjoint B) := by
  obtain ⟨X, Y, hX, hY, hpW, hmax⟩ := hF
  obtain ⟨F', hF'max, hs, h⟩ := hmax.exists_isMaximalMonotoneOp
  have hF' := hF'max.1
  have hW : IsOpen (X ×ˢ Y) := hX.prod hY
  have hq' : ∀ q ∈ graph F ∩ X ×ˢ Y, q ∈ graph F' := fun q hq ↦
    (show q ∈ graph F' ∩ X ×ˢ Y by rw [← h]; exact hq).1
  refine ⟨⟨_, hW.mem_nhds hpW, fun q hq ↦ ?_⟩, _, hW.mem_nhds hpW, fun q hq L hL ↦ ?_⟩
  · obtain ⟨L, hL⟩ := hF'.isSCDMapping hs q (hq' q hq)
    exact ⟨L, scDeriv_subset_of_inter_eq_of_isOpen hW h.symm hq.2 hL⟩
  · exact hF'.exists_firm_of_mem_scDeriv hs (hq' q hq)
      (scDeriv_subset_of_inter_eq_of_isOpen hW h hq.2 hL)

/-- [Gfrerer–Outrata 2022, Cor. 3.23]: a locally maximally hypomonotone mapping has the SCD
property around `p`, and for some `γ ≥ 0` every `L ∈ 𝒮F(q)` at nearby `q ∈ gph F` is
`rge(B, I - (1 + γ)B)` with `B` firmly nonexpansive, and `L* = rge(Bᵀ, I - (1 + γ)Bᵀ)`. -/
theorem IsLocallyMaximalHypomonotoneAt.scd {p : E × E}
    (hF : IsLocallyMaximalHypomonotoneAt F p) :
    HasSCDPropertyAround F p ∧ ∃ γ : ℝ, 0 ≤ γ ∧ ∃ U ∈ 𝓝 p, ∀ q ∈ graph F ∩ U,
      ∀ L ∈ scDeriv F q, ∃ B : E →L[ℝ] E, IsFirmlyNonexpansiveOp B ∧
        L = hypoMintySubspace (1 + γ) B ∧
        adjointSubspace L = hypoMintySubspace (1 + γ) (ContinuousLinearMap.adjoint B) := by
  obtain ⟨γ, hγ, hG⟩ := hF
  obtain ⟨⟨U, hU, hUG⟩, V, hV, hVG⟩ := hG.scd
  have hψ : Continuous fun q : E × E ↦ (q.1, q.2 + γ • q.1) :=
    continuous_fst.prodMk (continuous_snd.add (continuous_fst.const_smul γ))
  have hU' : (fun q : E × E ↦ (q.1, q.2 + γ • q.1)) ⁻¹' U ∈ 𝓝 p :=
    hψ.continuousAt.preimage_mem_nhds hU
  have hV' : (fun q : E × E ↦ (q.1, q.2 + γ • q.1)) ⁻¹' V ∈ 𝓝 p :=
    hψ.continuousAt.preimage_mem_nhds hV
  have hh : ∀ u : E, HasStrictFDerivAt (fun x : E ↦ γ • x) (γ • ContinuousLinearMap.id ℝ E) u :=
    fun u ↦ (hasStrictFDerivAt_id u).const_smul γ
  have hadd0 : ∀ q : E × E,
      scDeriv (fun u ↦ (fun v ↦ v + (fun x : E ↦ γ • x) u) '' F u)
        (q.1, q.2 + (fun x : E ↦ γ • x) q.1) =
      (fun L ↦ L.map (shearCLM ((fun _ : E ↦ γ • ContinuousLinearMap.id ℝ E) q.1) :
        (E × E) →ₗ[ℝ] (E × E))) '' scDeriv F (q.1, q.2) := fun q ↦
    scDeriv_add (Dh := fun _ ↦ γ • ContinuousLinearMap.id ℝ E) (Eventually.of_forall hh)
      continuousAt_const
  have hadd : ∀ q : E × E, scDeriv (fun x ↦ (fun y ↦ y + γ • x) '' F x) (q.1, q.2 + γ • q.1) =
      (fun L ↦ L.map (shearCLM (γ • ContinuousLinearMap.id ℝ E) : (E × E) →ₗ[ℝ] (E × E))) ''
        scDeriv F q := fun q ↦ by
    have := hadd0 q
    simp only [Prod.mk.eta] at this
    exact this
  refine ⟨⟨_, hU', fun q hq ↦ ?_⟩, γ, hγ, _, hV', fun q hq L hL ↦ ?_⟩
  · obtain ⟨L, hL⟩ := hUG (q.1, q.2 + γ • q.1) ⟨(mem_graph_add_smul_iff γ).2 hq.1, hq.2⟩
    rw [hadd q] at hL
    obtain ⟨L', hL', -⟩ := hL
    exact ⟨L', hL'⟩
  · have hmem : L.map (shearCLM (γ • ContinuousLinearMap.id ℝ E) : (E × E) →ₗ[ℝ] (E × E)) ∈
        scDeriv (fun x ↦ (fun y ↦ y + γ • x) '' F x) (q.1, q.2 + γ • q.1) := by
      rw [hadd q]; exact ⟨L, hL, rfl⟩
    obtain ⟨B, hB, hLB, -⟩ :=
      hVG (q.1, q.2 + γ • q.1) ⟨(mem_graph_add_smul_iff γ).2 hq.1, hq.2⟩ _ hmem
    have hL' : L = hypoMintySubspace (1 + γ) B := by
      rw [← map_shearCLM_mintySubspace, ← hLB]
      exact (map_symm_map_eq (shear (γ • ContinuousLinearMap.id ℝ E)) L).symm
    exact ⟨B, hB, hL', by rw [hL', adjointSubspace_hypoMintySubspace]⟩

/-- [Gfrerer–Outrata 2022, Cor. 3.24]: a mapping which is locally maximally hypomonotone on a
dense subset of its graph is an SCD mapping. -/
theorem isSCDMapping_of_dense {D : Set (E × E)} (hD : graph F ⊆ closure D)
    (hDF : ∀ p ∈ D, IsLocallyMaximalHypomonotoneAt F p) (hDg : D ⊆ graph F) :
    IsSCDMapping F := by
  intro p hp
  obtain ⟨d, hd, hdlim⟩ := mem_closure_iff_seq_limit.1 (hD hp)
  refine hasSCDPropertyAt_of_tendsto hdlim fun k ↦ ?_
  obtain ⟨U, hU, hUF⟩ := (hDF _ (hd k)).scd.1
  exact hUF _ ⟨hDg (hd k), mem_of_mem_nhds hU⟩

end VariationalAnalysis
