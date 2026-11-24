/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Prod
import VariationalAnalysis.SCD.Basic
import VariationalAnalysis.Normal.Diffeomorphism

/-!
# Calculus rules for SC derivatives

Changes of variables in the graph [Gfrerer–Outrata 2022, Prop. 3.14] and addition of a smooth
single-valued mapping [Gfrerer–Outrata 2022, Prop. 3.15].

If `gph F = Φ⁻¹(gph G)` with `Φ` continuously differentiable near `p` and `∇Φ(p)` invertible,
then `T_{gph F}(q) = ∇Φ(q)⁻¹ T_{gph G}(Φ q)` near `p` ([Rockafellar–Wets 1998, Exercise 6.7]),
and passing to limits gives `𝒮G(Φ p) = ∇Φ(p) 𝒮F(p)`. As in `Normal/Diffeomorphism`, "`C¹`
near `p`" is expressed as: `Φ` has strict derivative `D q` at every `q` near `p` and `D` is
continuous at `p`.

## Main declarations

* `shearCLM M`, `shear M`: the map `(u, v) ↦ (u, v + M u)` of `E × E` and its inverse
  `shear (-M)`.

## Main results

* `apply_mem_contingentCone_of_hasFDerivAt`, `mem_contingentCone_preimage_iff`,
  `contingentCone_eq_image_preimage`: contingent cones under differentiable maps and under maps
  with invertible strict derivative [Rockafellar–Wets 1998, Exercise 6.7].
* `GrassTendsto.map_of_tendsto`: if `Lₖ → L` and `Aₖ → e` (with `e` invertible), then
  `Aₖ Lₖ → e L` in the Grassmannian metric [Gfrerer–Outrata 2022, Lemma 3.1(iii)].
* `graphicallySmoothAt_iff_of_preimage`, `tangentSubspace_eq_map_of_preimage`: points of
  graphical smoothness and tangent subspaces under a change of variables.
* `scDeriv_preimage`, `scDeriv_eq_image_symm`, `hasSCDPropertyAt_iff_of_preimage`:
  Prop. 3.14 (20) of [Gfrerer–Outrata 2022]; `scDeriv_image_linear` is the linear case.
* `scDeriv_add`, `scDeriv_add_of_contDiffAt`, `scCoderiv_add`, `hasSCDPropertyAt_add_iff`:
  Prop. 3.15 of [Gfrerer–Outrata 2022], (22) and (23).
-/

open Filter Topology Set Module Asymptotics
open scoped InnerProductSpace

namespace VariationalAnalysis

/-! ### Contingent cones under smooth maps -/

section Tangent

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- If `φ` is differentiable at `x` with derivative `A` and maps `Ω` into `Ω'` near `x`, then
`A T_Ω(x) ⊆ T_{Ω'}(φ x)`. -/
theorem apply_mem_contingentCone_of_hasFDerivAt {φ : X → Y} {A : X →L[ℝ] Y} {x : X}
    {Ω : Set X} {Ω' : Set Y} (hφ : HasFDerivAt φ A x) (hmaps : ∀ᶠ z in 𝓝 x, z ∈ Ω → φ z ∈ Ω')
    {w : X} (hw : w ∈ contingentCone Ω x) : A w ∈ contingentCone Ω' (φ x) := by
  obtain ⟨hx, z, α, hzα, hzlim, hlim⟩ := hw
  have hr : (fun k ↦ α k • (φ (z k) - φ x - A (z k - x))) =o[atTop]
      (fun _ ↦ (1 : ℝ)) :=
    ((isBigO_refl α atTop).smul_isLittleO (hφ.isLittleO.comp_tendsto hzlim)).trans_isBigO
      (hlim.isBigO_one (F := ℝ))
  refine mem_contingentCone_of_eventually (hmaps.self_of_nhds hx) (fun k ↦ φ (z k)) α
    ((hzlim.eventually hmaps).mono fun k hk ↦ ⟨hk (hzα k).1, (hzα k).2⟩)
    (hφ.continuousAt.tendsto.comp hzlim) ?_
  have := ((A.continuous.tendsto w).comp hlim).add ((isLittleO_one_iff ℝ).1 hr)
  rw [add_zero] at this
  refine this.congr fun k ↦ ?_
  simp only [Function.comp_apply, map_smul, map_sub, smul_sub]
  abel

variable [CompleteSpace X] [CompleteSpace Y]

omit [CompleteSpace Y] in
/-- [Rockafellar–Wets 1998, Exercise 6.7]: for `Φ` with invertible strict derivative `e` at `x`,
`w ∈ T_{Φ⁻¹(Ω')}(x)` iff `e w ∈ T_{Ω'}(Φ x)`. -/
theorem mem_contingentCone_preimage_iff {Φ : X → Y} {e : X ≃L[ℝ] Y} {x : X} {Ω' : Set Y}
    (hΦ : HasStrictFDerivAt Φ (e : X →L[ℝ] Y) x) {w : X} :
    w ∈ contingentCone (Φ ⁻¹' Ω') x ↔ e w ∈ contingentCone Ω' (Φ x) := by
  constructor
  · exact apply_mem_contingentCone_of_hasFDerivAt hΦ.hasFDerivAt
      (Eventually.of_forall fun _ hz ↦ hz)
  · intro hw
    have h := apply_mem_contingentCone_of_hasFDerivAt (Ω := Ω') (Ω' := Φ ⁻¹' Ω')
      hΦ.to_localInverse.hasFDerivAt
      (hΦ.eventually_right_inverse.mono fun y hy hyΩ ↦ by
        change Φ _ ∈ Ω'
        rw [hy]; exact hyΩ) hw
    rwa [hΦ.localInverse_apply_image, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] at h

omit [CompleteSpace Y] in
/-- [Rockafellar–Wets 1998, Exercise 6.7]: `T_{Ω'}(Φ x) = ∇Φ(x) T_{Φ⁻¹(Ω')}(x)`. -/
theorem contingentCone_eq_image_preimage {Φ : X → Y} {e : X ≃L[ℝ] Y} {x : X} {Ω' : Set Y}
    (hΦ : HasStrictFDerivAt Φ (e : X →L[ℝ] Y) x) :
    contingentCone Ω' (Φ x) = e '' contingentCone (Φ ⁻¹' Ω') x := by
  ext z
  constructor
  · intro hz
    exact ⟨e.symm z, (mem_contingentCone_preimage_iff hΦ).2 (by simpa using hz), by simp⟩
  · rintro ⟨w, hw, rfl⟩
    exact (mem_contingentCone_preimage_iff hΦ).1 hw

end Tangent

/-! ### Linear images of converging subspaces -/

section Grass

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- A variant of `GrassTendsto.mem_of_tendsto` along a subsequence, with eventual
membership. -/
theorem GrassTendsto.mem_of_eventually {L : ℕ → Submodule ℝ V} {L₀ : Submodule ℝ V}
    (h : GrassTendsto L L₀) {a : ℕ → ℕ} (ha : Tendsto a atTop atTop) {w : ℕ → V} {w₀ : V}
    (hw : ∀ᶠ k in atTop, w k ∈ L (a k)) (hlim : Tendsto w atTop (𝓝 w₀)) : w₀ ∈ L₀ := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hw
  exact (h.comp (ha.comp (tendsto_add_atTop_nat N))).mem_of_tendsto (w := fun k ↦ w (k + N))
    (fun k ↦ hN _ (Nat.le_add_left N k)) ((tendsto_add_atTop_iff_nat N).2 hlim)

/-- Convergence of subspaces is not affected by finitely many terms. -/
theorem GrassTendsto.congr_eventually {L M : ℕ → Submodule ℝ V} {L₀ : Submodule ℝ V}
    (h : GrassTendsto L L₀) (hLM : ∀ᶠ k in atTop, L k = M k) : GrassTendsto M L₀ :=
  Tendsto.congr' (hLM.mono fun _ hk ↦ congrArg grassProj hk) h

/-- A variant of `grassTendsto_of_outerLimit_subset` in which the dimensions are only eventually
equal. -/
theorem grassTendsto_of_eventually {L : ℕ → Submodule ℝ V} {L₀ : Submodule ℝ V} {n : ℕ}
    (hL : ∀ᶠ k in atTop, finrank ℝ (L k) = n) (hL₀ : finrank ℝ L₀ = n)
    (h : ∀ (a : ℕ → ℕ) (w : ℕ → V) (w₀ : V), Tendsto a atTop atTop →
      Tendsto w atTop (𝓝 w₀) → (∀ k, w k ∈ L (a k)) → w₀ ∈ L₀) :
    GrassTendsto L L₀ := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hL
  have : GrassTendsto (fun k ↦ L (k + N)) L₀ :=
    grassTendsto_of_outerLimit_subset (fun k ↦ hN _ (Nat.le_add_left N k)) hL₀ (by
      rintro w₀ ⟨a, w, ha, hw, hmem⟩
      exact h (fun k ↦ a k + N) w w₀ ((tendsto_add_atTop_nat N).comp ha) hw hmem)
  exact (tendsto_add_atTop_iff_nat (f := fun k ↦ grassProj (L k)) N).1 this

/-- If `Aₖ → e` with `e` invertible, there are `Bₖ → e⁻¹` with `Bₖ Aₖ = I` eventually. -/
theorem exists_tendsto_leftInverse {A : ℕ → V →L[ℝ] V} {e : V ≃L[ℝ] V}
    (hA : Tendsto A atTop (𝓝 (e : V →L[ℝ] V))) :
    ∃ B : ℕ → V →L[ℝ] V, Tendsto B atTop (𝓝 (e.symm : V →L[ℝ] V)) ∧
      ∀ᶠ k in atTop, (B k).comp (A k) = ContinuousLinearMap.id ℝ V := by
  set U : ℕ → V →L[ℝ] V := fun k ↦ (e.symm : V →L[ℝ] V).comp (A k) with hU_def
  have hU1 : Tendsto U atTop (𝓝 1) := by
    have := ((ContinuousLinearMap.compL ℝ V V V (e.symm : V →L[ℝ] V)).continuous.tendsto
      (e : V →L[ℝ] V)).comp hA
    simpa [Function.comp_def, ContinuousLinearMap.one_def, hU_def] using this
  refine ⟨fun k ↦ (Ring.inverse (U k)).comp (e.symm : V →L[ℝ] V), ?_, ?_⟩
  · have hinv : Tendsto (fun k ↦ Ring.inverse (U k)) atTop (𝓝 1) := by
      have h := (NormedRing.inverse_continuousAt (1 : (V →L[ℝ] V)ˣ)).tendsto.comp hU1
      simpa [Function.comp_def, Ring.inverse_one] using h
    have := ((ContinuousLinearMap.compL ℝ V V V).flip (e.symm : V →L[ℝ] V)).continuous.tendsto
      1 |>.comp hinv
    simpa [Function.comp_def, ContinuousLinearMap.one_def] using this
  · filter_upwards [eventually_isUnit_symm_comp hA] with k hu
    have := Ring.inverse_mul_cancel _ hu
    rw [ContinuousLinearMap.mul_def] at this
    rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.one_def]
    exact this

/-- [Gfrerer–Outrata 2022, Lemma 3.1(iii)]: if `Lₖ → L₀` and `Aₖ → e` with `e` invertible, then
`Aₖ Lₖ → e L₀` in the Grassmannian metric. -/
theorem GrassTendsto.map_of_tendsto {L : ℕ → Submodule ℝ V} {L₀ : Submodule ℝ V} {n : ℕ}
    (hn : ∀ k, finrank ℝ (L k) = n) (h : GrassTendsto L L₀) {A : ℕ → V →L[ℝ] V}
    {e : V ≃L[ℝ] V} (hA : Tendsto A atTop (𝓝 (e : V →L[ℝ] V))) :
    GrassTendsto (fun k ↦ (L k).map (A k : V →ₗ[ℝ] V))
      (L₀.map ((e : V →L[ℝ] V) : V →ₗ[ℝ] V)) := by
  obtain ⟨B, hB, hBA⟩ := exists_tendsto_leftInverse hA
  have hinj : ∀ᶠ k in atTop, Function.Injective (A k) := hBA.mono fun k hk x y hxy ↦ by
    have h1 : ((B k).comp (A k)) x = ((B k).comp (A k)) y := by
      simp only [ContinuousLinearMap.comp_apply, hxy]
    rw [hk] at h1
    exact h1
  refine grassTendsto_of_eventually (n := n) (hinj.mono fun k hk ↦ ?_) ?_ ?_
  · exact (Submodule.equivMapOfInjective _ hk (L k)).finrank_eq.symm.trans (hn k)
  · exact (Submodule.equivMapOfInjective _ e.injective L₀).finrank_eq.symm.trans
      (h.finrank_eq hn)
  · intro a w w₀ ha hw hmem
    have hv : ∀ᶠ k in atTop, B (a k) (w k) ∈ L (a k) := by
      filter_upwards [ha.eventually hBA] with k hk
      obtain ⟨u, hu, hwu⟩ := Submodule.mem_map.1 (hmem k)
      have hBu : B (a k) (A (a k) u) = u := by
        rw [← ContinuousLinearMap.comp_apply, hk]; rfl
      rw [← hwu, ContinuousLinearMap.coe_coe, hBu]
      exact hu
    have hlim : Tendsto (fun k ↦ B (a k) (w k)) atTop (𝓝 ((e.symm : V →L[ℝ] V) w₀)) :=
      tendsto_clm_apply (hB.comp ha) hw
    exact Submodule.mem_map.2 ⟨e.symm w₀, h.mem_of_eventually ha hv hlim, by simp⟩

omit [FiniteDimensional ℝ V] in
/-- For a linear isomorphism `e` and a subspace `L`, `e⁻¹(e L) = L`. -/
theorem map_symm_map_eq (e : V ≃L[ℝ] V) (L : Submodule ℝ V) :
    (L.map ((e : V →L[ℝ] V) : V →ₗ[ℝ] V)).map ((e.symm : V →L[ℝ] V) : V →ₗ[ℝ] V) = L := by
  rw [← Submodule.map_comp]
  convert Submodule.map_id L
  ext v; simp

omit [FiniteDimensional ℝ V] in
/-- For a linear isomorphism `e` and a subspace `L`, `e(e⁻¹ L) = L`. -/
theorem map_map_symm_eq (e : V ≃L[ℝ] V) (L : Submodule ℝ V) :
    (L.map ((e.symm : V →L[ℝ] V) : V →ₗ[ℝ] V)).map ((e : V →L[ℝ] V) : V →ₗ[ℝ] V) = L := by
  rw [← Submodule.map_comp]
  convert Submodule.map_id L
  ext v; simp

end Grass

/-! ### Change of variables: Prop. 3.14 -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F G : E → Set E} {Φ : E × E → E × E}

/-- The SC derivative is unchanged if the defining sequence is only eventually smooth. -/
theorem mem_scDeriv_of_eventually {p : E × E} {q : ℕ → E × E} {L : Submodule ℝ (E × E)}
    (hq : ∀ᶠ k in atTop, GraphicallySmoothAt F (q k)) (hqlim : Tendsto q atTop (𝓝 p))
    (hT : GrassTendsto (fun k ↦ tangentSubspace F (q k)) L) : L ∈ scDeriv F p := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hq
  exact ⟨fun k ↦ q (k + N), fun k ↦ hN _ (Nat.le_add_left N k),
    (tendsto_add_atTop_iff_nat N).2 hqlim,
    (tendsto_add_atTop_iff_nat (f := fun k ↦ grassProj (tangentSubspace F (q k))) N).2 hT⟩

section Pointwise

variable (hFG : graph F = Φ ⁻¹' graph G) {q : E × E} {e : (E × E) ≃L[ℝ] (E × E)}
  (hΦ : HasStrictFDerivAt Φ (e : (E × E) →L[ℝ] (E × E)) q)
include hFG hΦ

/-- [Rockafellar–Wets 1998, Exercise 6.7]: `T_{gph G}(Φ q) = ∇Φ(q) T_{gph F}(q)`. -/
theorem contingentCone_graph_eq_image_of_preimage :
    contingentCone (graph G) (Φ q) = e '' contingentCone (graph F) q := by
  rw [hFG]; exact contingentCone_eq_image_preimage hΦ

/-- If `gph F = Φ⁻¹(gph G)` and `Φ` has invertible strict derivative `e` at `q`, then the tangent
subspace of `G` at `Φ q` is the image under `e` of the tangent subspace of `F` at `q`. -/
theorem tangentSubspace_eq_map_of_preimage :
    tangentSubspace G (Φ q) =
      (tangentSubspace F q).map ((e : (E × E) →L[ℝ] (E × E)) : (E × E) →ₗ[ℝ] (E × E)) := by
  rw [tangentSubspace, tangentSubspace, contingentCone_graph_eq_image_of_preimage hFG hΦ,
    ← Submodule.span_image]
  rfl

/-- Points of graphical smoothness correspond under the change of variables:
`O_G ∩ W̃ = Φ(O_F ∩ W)` [Gfrerer–Outrata 2022, proof of Prop. 3.14]. -/
theorem graphicallySmoothAt_iff_of_preimage :
    GraphicallySmoothAt G (Φ q) ↔ GraphicallySmoothAt F q := by
  have hq : Φ q ∈ graph G ↔ q ∈ graph F := by rw [hFG]; rfl
  constructor
  · rintro ⟨hq', L, hdim, hL⟩
    refine ⟨hq.1 hq', L.map ((e.symm : (E × E) →L[ℝ] (E × E)) : (E × E) →ₗ[ℝ] (E × E)), ?_, ?_⟩
    · rw [← hdim]; exact (Submodule.equivMapOfInjective _ e.symm.injective L).finrank_eq.symm
    · rw [Submodule.map_coe, hL, contingentCone_graph_eq_image_of_preimage hFG hΦ]
      ext w; simp [Set.image_image]
  · rintro ⟨hq', L, hdim, hL⟩
    refine ⟨hq.2 hq', L.map ((e : (E × E) →L[ℝ] (E × E)) : (E × E) →ₗ[ℝ] (E × E)), ?_, ?_⟩
    · rw [← hdim]; exact (Submodule.equivMapOfInjective _ e.injective L).finrank_eq.symm
    · rw [Submodule.map_coe, hL, contingentCone_graph_eq_image_of_preimage hFG hΦ]
      rfl

end Pointwise

/-- Near `p`, the derivative `D q` of a `C¹` map with invertible `D p` is invertible. -/
theorem eventually_exists_equiv {p : E × E} {D : E × E → (E × E) →L[ℝ] (E × E)}
    {e : (E × E) ≃L[ℝ] (E × E)} (hD : ∀ᶠ q in 𝓝 p, HasStrictFDerivAt Φ (D q) q)
    (hDc : ContinuousAt D p) (he : D p = e) :
    ∀ᶠ q in 𝓝 p, ∃ e' : (E × E) ≃L[ℝ] (E × E), (e' : (E × E) →L[ℝ] (E × E)) = D q ∧
      HasStrictFDerivAt Φ (e' : (E × E) →L[ℝ] (E × E)) q := by
  have hDe : Tendsto D (𝓝 p) (𝓝 (e : (E × E) →L[ℝ] (E × E))) := by
    rw [← he]; exact hDc.tendsto
  filter_upwards [eventually_isUnit_symm_comp hDe, hD] with q hu hq
  obtain ⟨e', he'⟩ := exists_equiv_of_isUnit_symm_comp hu
  exact ⟨e', he', he' ▸ hq⟩

/-- Prop. 3.14, (20), of [Gfrerer–Outrata 2022]: if `gph F = Φ⁻¹(gph G)` with `Φ` `C¹` near
`p` and `∇Φ(p) = e` invertible, then `𝒮G(Φ p) = ∇Φ(p) 𝒮F(p)`. -/
theorem scDeriv_preimage (hFG : graph F = Φ ⁻¹' graph G) {p : E × E}
    {D : E × E → (E × E) →L[ℝ] (E × E)} {e : (E × E) ≃L[ℝ] (E × E)}
    (hD : ∀ᶠ q in 𝓝 p, HasStrictFDerivAt Φ (D q) q) (hDc : ContinuousAt D p) (he : D p = e) :
    scDeriv G (Φ p) =
      (fun L ↦ L.map ((e : (E × E) →L[ℝ] (E × E)) : (E × E) →ₗ[ℝ] (E × E))) '' scDeriv F p := by
  have hDe : Tendsto D (𝓝 p) (𝓝 (e : (E × E) →L[ℝ] (E × E))) := by
    rw [← he]; exact hDc.tendsto
  have hloc := eventually_exists_equiv hD hDc he
  have hΦp : HasStrictFDerivAt Φ (e : (E × E) →L[ℝ] (E × E)) p := he ▸ hD.self_of_nhds
  ext L'
  constructor
  · rintro ⟨z, hz, hzlim, hT⟩
    set g := HasStrictFDerivAt.localInverse Φ e p hΦp
    have hgc : ContinuousAt g (Φ p) := hΦp.to_localInverse.continuousAt
    have hgp : g (Φ p) = p := hΦp.localInverse_apply_image
    have hq : Tendsto (fun k ↦ g (z k)) atTop (𝓝 p) := by
      have := hgc.tendsto.comp hzlim; rwa [hgp] at this
    have hinv : ∀ᶠ k in atTop, Φ (g (z k)) = z k :=
      hzlim.eventually hΦp.eventually_right_inverse
    have hloc' := hq.eventually hloc
    obtain ⟨B, hB, hBD⟩ := exists_tendsto_leftInverse (hDe.comp hq)
    refine ⟨L'.map ((e.symm : (E × E) →L[ℝ] (E × E)) : (E × E) →ₗ[ℝ] (E × E)), ?_,
      map_map_symm_eq e L'⟩
    refine mem_scDeriv_of_eventually (q := fun k ↦ g (z k)) ?_ hq ?_
    · filter_upwards [hloc', hinv] with k hek hk
      obtain ⟨e', -, he'⟩ := hek
      rw [← graphicallySmoothAt_iff_of_preimage hFG he', hk]
      exact hz k
    · have h1 := hT.map_of_tendsto (n := finrank ℝ E)
        (fun k ↦ (hz k).finrank_tangentSubspace) (e := e.symm) hB
      refine h1.congr_eventually ?_
      filter_upwards [hloc', hinv, hBD] with k hek hk hBk
      obtain ⟨e', he'D, he'⟩ := hek
      have hBk' : (B k).comp (e' : (E × E) →L[ℝ] (E × E)) = ContinuousLinearMap.id ℝ _ := by
        rw [he'D]; exact hBk
      have hBe : B k = (e'.symm : (E × E) →L[ℝ] (E × E)) := by
        refine ContinuousLinearMap.ext fun v ↦ ?_
        have := congrArg (fun f ↦ f (e'.symm v)) hBk'
        simpa using this
      have key := tangentSubspace_eq_map_of_preimage hFG he'
      rw [hk] at key
      rw [key, hBe, map_symm_map_eq]
  · rintro ⟨L, ⟨q, hq, hqlim, hT⟩, rfl⟩
    have hloc' := hqlim.eventually hloc
    refine mem_scDeriv_of_eventually (q := fun k ↦ Φ (q k)) ?_
      (hΦp.continuousAt.tendsto.comp hqlim) ?_
    · filter_upwards [hloc'] with k hek
      obtain ⟨e', -, he'⟩ := hek
      exact (graphicallySmoothAt_iff_of_preimage hFG he').2 (hq k)
    · have h1 := hT.map_of_tendsto (n := finrank ℝ E)
        (fun k ↦ (hq k).finrank_tangentSubspace) (hDe.comp hqlim)
      refine h1.congr_eventually ?_
      filter_upwards [hloc'] with k hek
      obtain ⟨e', he'D, he'⟩ := hek
      rw [tangentSubspace_eq_map_of_preimage hFG he', he'D]
      rfl

/-- Prop. 3.14, (20), of [Gfrerer–Outrata 2022] in the form of the paper:
`𝒮F(p) = ∇Φ(p)⁻¹ 𝒮G(Φ p)`. -/
theorem scDeriv_eq_image_symm (hFG : graph F = Φ ⁻¹' graph G) {p : E × E}
    {D : E × E → (E × E) →L[ℝ] (E × E)} {e : (E × E) ≃L[ℝ] (E × E)}
    (hD : ∀ᶠ q in 𝓝 p, HasStrictFDerivAt Φ (D q) q) (hDc : ContinuousAt D p) (he : D p = e) :
    scDeriv F p = (fun L ↦ L.map ((e.symm : (E × E) →L[ℝ] (E × E)) : (E × E) →ₗ[ℝ] (E × E))) ''
      scDeriv G (Φ p) := by
  rw [scDeriv_preimage hFG hD hDc he, Set.image_image]
  simp only [map_symm_map_eq, Set.image_id']

/-- The SCD property is invariant under `C¹` changes of variables
[Gfrerer–Outrata 2022, Prop. 3.14]. -/
theorem hasSCDPropertyAt_iff_of_preimage (hFG : graph F = Φ ⁻¹' graph G) {p : E × E}
    {D : E × E → (E × E) →L[ℝ] (E × E)} {e : (E × E) ≃L[ℝ] (E × E)}
    (hD : ∀ᶠ q in 𝓝 p, HasStrictFDerivAt Φ (D q) q) (hDc : ContinuousAt D p) (he : D p = e) :
    HasSCDPropertyAt G (Φ p) ↔ HasSCDPropertyAt F p := by
  rw [HasSCDPropertyAt, HasSCDPropertyAt, scDeriv_preimage hFG hD hDc he, Set.image_nonempty]

/-- Prop. 3.14 of [Gfrerer–Outrata 2022] for a linear change of variables: if
`gph G = e(gph F)`, then `𝒮G(e p) = e 𝒮F(p)`. -/
theorem scDeriv_image_linear (e : (E × E) ≃L[ℝ] (E × E)) (hGF : graph G = e '' graph F)
    (p : E × E) :
    scDeriv G (e p) =
      (fun L ↦ L.map ((e : (E × E) →L[ℝ] (E × E)) : (E × E) →ₗ[ℝ] (E × E))) '' scDeriv F p := by
  have hFG : graph F = e ⁻¹' graph G := by
    rw [hGF, Set.preimage_image_eq _ e.injective]
  exact scDeriv_preimage (Φ := e) hFG (D := fun _ ↦ e)
    (Eventually.of_forall fun _ ↦ e.hasStrictFDerivAt) continuousAt_const rfl

/-! ### Adding a smooth mapping: Prop. 3.15 -/

/-- The shear `(u, v) ↦ (u, v + M u)` of `E × E`, i.e. the block matrix `[I 0; M I]`. -/
noncomputable def shearCLM (M : E →L[ℝ] E) : (E × E) →L[ℝ] (E × E) :=
  ContinuousLinearMap.id ℝ (E × E) +
    (ContinuousLinearMap.inr ℝ E E).comp (M.comp (ContinuousLinearMap.fst ℝ E E))

omit [FiniteDimensional ℝ E] in
/-- `shearCLM M` maps `(u, v)` to `(u, v + M u)`. -/
@[simp] theorem shearCLM_apply (M : E →L[ℝ] E) (w : E × E) :
    shearCLM M w = (w.1, w.2 + M w.1) := by
  ext <;> simp [shearCLM]

/-- The shear `[I 0; M I]` as a linear isomorphism, with inverse `[I 0; -M I]`. -/
noncomputable def shear (M : E →L[ℝ] E) : (E × E) ≃L[ℝ] (E × E) :=
  ContinuousLinearEquiv.equivOfInverse (shearCLM M) (shearCLM (-M))
    (fun w ↦ by simp) (fun w ↦ by simp)

omit [FiniteDimensional ℝ E] in
/-- The continuous linear map underlying `shear M` is `shearCLM M`. -/
@[simp] theorem coe_shear (M : E →L[ℝ] E) :
    (shear M : (E × E) →L[ℝ] (E × E)) = shearCLM M := rfl

omit [FiniteDimensional ℝ E] in
/-- The inverse of `shear M` is the shear `shearCLM (-M)`, i.e. `[I 0; -M I]`. -/
theorem coe_shear_symm (M : E →L[ℝ] E) :
    ((shear M).symm : (E × E) →L[ℝ] (E × E)) = shearCLM (-M) := rfl

omit [FiniteDimensional ℝ E] in
/-- `M ↦ shearCLM M` is continuous in operator norm. -/
theorem continuous_shearCLM : Continuous (shearCLM (E := E)) :=
  continuous_const.add (continuous_const.clm_comp (continuous_id.clm_comp continuous_const))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- `gph (F + h) = Φ⁻¹(gph F)` with `Φ(x, y) = (x, y - h x)`. -/
theorem graph_add_eq_preimage (h : E → E) :
    graph (fun x ↦ (fun y ↦ y + h x) '' F x) =
      (fun w : E × E ↦ (w.1, w.2 - h w.1)) ⁻¹' graph F := by
  ext ⟨x, y⟩
  simp only [graph, Set.mem_ofPred_eq, mem_preimage, mem_image]
  exact ⟨fun ⟨v, hv, hvy⟩ ↦ by rw [← hvy]; simpa using hv,
    fun hy ↦ ⟨y - h x, hy, by simp⟩⟩

/-- Prop. 3.15, (22), of [Gfrerer–Outrata 2022]: if `h` is `C¹` near `x` (strict derivative
`Dh u` near `x`, `Dh` continuous at `x`), then
`𝒮(F + h)(x, y + h x) = {[I 0; ∇h(x) I] L | L ∈ 𝒮F(x, y)}`. -/
theorem scDeriv_add {h : E → E} {Dh : E → E →L[ℝ] E} {x y : E}
    (hh : ∀ᶠ u in 𝓝 x, HasStrictFDerivAt h (Dh u) u) (hDh : ContinuousAt Dh x) :
    scDeriv (fun u ↦ (fun v ↦ v + h u) '' F u) (x, y + h x) =
      (fun L ↦ L.map (shearCLM (Dh x) : (E × E) →ₗ[ℝ] (E × E))) '' scDeriv F (x, y) := by
  set Φ : E × E → E × E := fun w ↦ (w.1, w.2 - h w.1) with hΦ_def
  have hD : ∀ᶠ q in 𝓝 (x, y + h x),
      HasStrictFDerivAt Φ (shearCLM (-(Dh q.1))) q := by
    filter_upwards [(continuous_fst.tendsto (x, y + h x)).eventually hh] with q hq
    have h1 := hasStrictFDerivAt_fst.prodMk
      (hasStrictFDerivAt_snd.sub (hq.comp q hasStrictFDerivAt_fst))
    refine h1.congr_fderiv ?_
    ext w <;> simp [sub_eq_add_neg]
  have hDc : ContinuousAt (fun q : E × E ↦ shearCLM (-(Dh q.1))) (x, y + h x) :=
    continuous_shearCLM.continuousAt.comp (hDh.comp continuous_fst.continuousAt).neg
  have := scDeriv_eq_image_symm (graph_add_eq_preimage (F := F) h) hD hDc
    (e := shear (-(Dh x))) rfl
  rw [show ((x, y + h x).1, (x, y + h x).2 - h (x, y + h x).1) = (x, y) by simp] at this
  rw [this, coe_shear_symm, neg_neg]

/-- Prop. 3.15, (22), of [Gfrerer–Outrata 2022] for `h` continuously differentiable at `x`. -/
theorem scDeriv_add_of_contDiffAt {h : E → E} {x y : E} (hh : ContDiffAt ℝ 1 h x) :
    scDeriv (fun u ↦ (fun v ↦ v + h u) '' F u) (x, y + h x) =
      (fun L ↦ L.map (shearCLM (fderiv ℝ h x) : (E × E) →ₗ[ℝ] (E × E))) ''
        scDeriv F (x, y) :=
  scDeriv_add ((hh.eventually (by simp)).mono fun _ hu ↦ hu.hasStrictFDerivAt one_ne_zero)
    (hh.continuousAt_fderiv one_ne_zero)

/-- Prop. 3.15 of [Gfrerer–Outrata 2022]: `F + h` has the SCD property at `(x, y + h x)` iff `F`
has it at `(x, y)`. -/
theorem hasSCDPropertyAt_add_iff {h : E → E} {Dh : E → E →L[ℝ] E} {x y : E}
    (hh : ∀ᶠ u in 𝓝 x, HasStrictFDerivAt h (Dh u) u) (hDh : ContinuousAt Dh x) :
    HasSCDPropertyAt (fun u ↦ (fun v ↦ v + h u) '' F u) (x, y + h x) ↔
      HasSCDPropertyAt F (x, y) := by
  rw [HasSCDPropertyAt, HasSCDPropertyAt, scDeriv_add hh hDh, Set.image_nonempty]

/-- `([I 0; M I] L)* = [I 0; Mᵀ I] L*`. -/
theorem adjointSubspace_map_shearCLM (M : E →L[ℝ] E) (L : Submodule ℝ (E × E)) :
    adjointSubspace (L.map (shearCLM M : (E × E) →ₗ[ℝ] (E × E))) =
      (adjointSubspace L).map
        (shearCLM (ContinuousLinearMap.adjoint M) : (E × E) →ₗ[ℝ] (E × E)) := by
  ext ⟨y, x⟩
  constructor
  · intro hmem
    refine Submodule.mem_map.2 ⟨(y, x - ContinuousLinearMap.adjoint M y), ?_, by simp⟩
    rw [mk_mem_adjointSubspace_iff]
    intro u v huv
    have := mk_mem_adjointSubspace_iff.1 hmem u (v + M u)
      (Submodule.mem_map.2 ⟨(u, v), huv, by simp⟩)
    rw [inner_sub_left, ContinuousLinearMap.adjoint_inner_left, this, inner_add_right]
    ring
  · intro hmem
    obtain ⟨⟨y', x'⟩, hw, hwe⟩ := Submodule.mem_map.1 hmem
    simp only [ContinuousLinearMap.coe_coe, shearCLM_apply, Prod.mk.injEq] at hwe
    obtain ⟨rfl, rfl⟩ := hwe
    rw [mk_mem_adjointSubspace_iff]
    intro u v' huv
    obtain ⟨⟨u₀, v₀⟩, h₀, h₀e⟩ := Submodule.mem_map.1 huv
    simp only [ContinuousLinearMap.coe_coe, shearCLM_apply, Prod.mk.injEq] at h₀e
    obtain ⟨rfl, rfl⟩ := h₀e
    have := mk_mem_adjointSubspace_iff.1 hw u₀ v₀ h₀
    rw [inner_add_left, this, ContinuousLinearMap.adjoint_inner_left, inner_add_right]

/-- Prop. 3.15, (23), of [Gfrerer–Outrata 2022]:
`𝒮*(F + h)(x, y + h x) = {[I 0; ∇h(x)ᵀ I] L | L ∈ 𝒮*F(x, y)}`. -/
theorem scCoderiv_add {h : E → E} {Dh : E → E →L[ℝ] E} {x y : E}
    (hh : ∀ᶠ u in 𝓝 x, HasStrictFDerivAt h (Dh u) u) (hDh : ContinuousAt Dh x) :
    scCoderiv (fun u ↦ (fun v ↦ v + h u) '' F u) (x, y + h x) =
      (fun L ↦ L.map
        (shearCLM (ContinuousLinearMap.adjoint (Dh x)) : (E × E) →ₗ[ℝ] (E × E))) ''
        scCoderiv F (x, y) := by
  rw [scCoderiv, scCoderiv, scDeriv_add hh hDh, Set.image_image, Set.image_image]
  simp only [adjointSubspace_map_shearCLM]

end VariationalAnalysis
