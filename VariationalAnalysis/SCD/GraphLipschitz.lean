/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import Mathlib.Topology.MetricSpace.Sequences
import VariationalAnalysis.SCD.Calculus
import VariationalAnalysis.SCD.SingleValued
import VariationalAnalysis.SetValued.Basic

/-!
# Graphically Lipschitzian mappings

A mapping `F : E ⇉ E` is graphically Lipschitzian (of dimension `n = dim E`) at `(x̄, ȳ) ∈ gph F`
if, after a `C¹` change of coordinates `Φ` near `(x̄, ȳ)`, its graph becomes the graph of a
Lipschitz continuous single-valued mapping [Gfrerer–Outrata 2022, Def. 3.16],
[Rockafellar–Wets 1998, Def. 9.66]. Such mappings have the SCD property around `(x̄, ȳ)`, and
their SC derivatives are the images of the graphs of the elements of the B-subdifferential of the
Lipschitz mapping [Gfrerer–Outrata 2022, Prop. 3.17]. Mappings `F` for which `F + h` is strongly
metrically regular for some `C¹` mapping `h` are graphically Lipschitzian
[Gfrerer–Outrata 2022, Cor. 3.19].

## Conventions

* "`C¹` on `W`" is expressed as in `SCD/Calculus`: `Φ` has strict derivative `D q` at every
  `q ∈ W` and `D` is continuous on `W`. The paper also asks that `Φ` maps `W` one-to-one onto an
  open set with `C¹` inverse; we require `Φ` injective on `W` with `D q` invertible for `q ∈ W`.
  By the inverse function theorem this is the same: `Φ(W)` is then open and `Φ⁻¹` is `C¹`.
* Only the dimension `d = n` is considered: `f : E → E` is Lipschitz on an open set `U ⊆ E`, and
  its graph is `gph f ∩ (U × E)`.
* Strong metric regularity of `F + h` enters Cor. 3.19 through its characterization by a Lipschitz
  continuous single-valued localization of the inverse [Gfrerer–Outrata 2022, Thm. 2.6],
  [Dontchev–Rockafellar 2014, Prop. 3G.1], `HasLipschitzInvLocalization`.

## Main declarations

* `IsGraphLipschitzTransform F W Φ D U f K`: the data of Def. 3.16 of [Gfrerer–Outrata 2022].
* `GraphicallyLipschitzianAt F p`: Def. 3.16 of [Gfrerer–Outrata 2022].
* `HasLipschitzInvLocalization F x̄ ȳ`: `F⁻¹` has a Lipschitz continuous single-valued
  localization around `(ȳ, x̄)`.

## Main results

* `contingentCone_congr_of_inter_eq`, `scDeriv_congr`, `hasSCDPropertyAround_congr`: SC
  derivatives and the SCD property only depend on the graph near the point.
* `scDeriv_preimage_of_inter_eq`, `scDeriv_eq_image_symm_of_inter_eq`: Prop. 3.14 of
  [Gfrerer–Outrata 2022] when `gph F = Φ⁻¹(gph G)` only holds near the point.
* `IsGraphLipschitzTransform.graphicallySmoothAt_iff`: Remark 3.18: `Φ(O_F ∩ W) = O_f`, the
  points where `f` is differentiable.
* `IsGraphLipschitzTransform.mem_scDeriv_iff`, `IsGraphLipschitzTransform.mem_scCoderiv_iff`,
  `GraphicallyLipschitzianAt.hasSCDPropertyAround`: Prop. 3.17, (24a), and the SCD property
  around `(x̄, ȳ)`.
* `IsGraphLipschitzTransform.finrank_eq_of_coe_eq_contingentCone`: Lemma 3.7(ii) of
  [Gfrerer–Mandlmayr–Outrata–Valdman 2023]: a tangent cone to `gph F` near `(x̄, ȳ)` which is a
  subspace has dimension `n`.
* `isGraphLipschitzTransform_of_add`, `mem_scDeriv_iff_of_add`,
  `graphicallyLipschitzianAt_of_add`, `hasSCDPropertyAround_of_add`: Cor. 3.19, (25a).
-/

open Filter Topology Set Module
open scoped InnerProductSpace NNReal

namespace VariationalAnalysis

/-! ### Locality of contingent cones and SC derivatives -/

section Locality

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Contingent cones are local: if `Ω ∩ W = Ω' ∩ W` for a neighborhood `W` of `x`, then
`T_Ω(x) = T_{Ω'}(x)`. -/
theorem contingentCone_congr_of_inter_eq {Ω Ω' W : Set X} {x : X} (hW : W ∈ 𝓝 x)
    (h : Ω ∩ W = Ω' ∩ W) : contingentCone Ω x = contingentCone Ω' x := by
  suffices key : ∀ A B : Set X, A ∩ W = B ∩ W → contingentCone A x ⊆ contingentCone B x from
    (key Ω Ω' h).antisymm (key Ω' Ω h.symm)
  intro A B hAB w ⟨hx, z, α, hzα, hzlim, hlim⟩
  have hxB : x ∈ B ∩ W := by rw [← hAB]; exact ⟨hx, mem_of_mem_nhds hW⟩
  refine mem_contingentCone_of_eventually hxB.1 z α ?_ hzlim hlim
  filter_upwards [hzlim.eventually hW] with k hk
  have : z k ∈ B ∩ W := by rw [← hAB]; exact ⟨(hzα k).1, hk⟩
  exact ⟨this.1, (hzα k).2⟩

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
theorem inter_eq_inter_of_subset {Ω Ω' W V : Set X} (h : Ω ∩ W = Ω' ∩ W) (hVW : V ⊆ W) :
    Ω ∩ V = Ω' ∩ V := by
  ext z
  constructor
  · rintro ⟨hz, hV⟩
    have : z ∈ Ω' ∩ W := by rw [← h]; exact ⟨hz, hVW hV⟩
    exact ⟨this.1, hV⟩
  · rintro ⟨hz, hV⟩
    have : z ∈ Ω ∩ W := by rw [h]; exact ⟨hz, hVW hV⟩
    exact ⟨this.1, hV⟩

end Locality

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F G : E → Set E} {p q : E × E} {W : Set (E × E)}

omit [FiniteDimensional ℝ E] in
theorem graphicallySmoothAt_congr (hW : W ∈ 𝓝 q) (h : graph F ∩ W = graph G ∩ W) :
    GraphicallySmoothAt F q ↔ GraphicallySmoothAt G q := by
  have hq : q ∈ graph F ↔ q ∈ graph G := by
    constructor
    · intro hq
      have : q ∈ graph G ∩ W := by rw [← h]; exact ⟨hq, mem_of_mem_nhds hW⟩
      exact this.1
    · intro hq
      have : q ∈ graph F ∩ W := by rw [h]; exact ⟨hq, mem_of_mem_nhds hW⟩
      exact this.1
  rw [GraphicallySmoothAt, GraphicallySmoothAt, hq, contingentCone_congr_of_inter_eq hW h]

omit [FiniteDimensional ℝ E] in
theorem tangentSubspace_congr (hW : W ∈ 𝓝 q) (h : graph F ∩ W = graph G ∩ W) :
    tangentSubspace F q = tangentSubspace G q := by
  rw [tangentSubspace, tangentSubspace, contingentCone_congr_of_inter_eq hW h]

theorem scDeriv_subset_of_inter_eq (hW : W ∈ 𝓝 p) (h : graph F ∩ W = graph G ∩ W) :
    scDeriv F p ⊆ scDeriv G p := by
  rintro L ⟨q, hq, hqlim, hT⟩
  have hint : ∀ᶠ k in atTop, q k ∈ interior W := hqlim.eventually (interior_mem_nhds.2 hW)
  have h' : graph F ∩ interior W = graph G ∩ interior W :=
    inter_eq_inter_of_subset h interior_subset
  refine mem_scDeriv_of_eventually ?_ hqlim (hT.congr_eventually ?_)
  · filter_upwards [hint] with k hk
    exact (graphicallySmoothAt_congr (isOpen_interior.mem_nhds hk) h').1 (hq k)
  · filter_upwards [hint] with k hk
    exact tangentSubspace_congr (isOpen_interior.mem_nhds hk) h'

/-- SC derivatives are local: if `gph F ∩ W = gph G ∩ W` for a neighborhood `W` of `p`, then
`𝒮F(p) = 𝒮G(p)`. -/
theorem scDeriv_congr (hW : W ∈ 𝓝 p) (h : graph F ∩ W = graph G ∩ W) :
    scDeriv F p = scDeriv G p :=
  (scDeriv_subset_of_inter_eq hW h).antisymm (scDeriv_subset_of_inter_eq hW h.symm)

theorem scCoderiv_congr (hW : W ∈ 𝓝 p) (h : graph F ∩ W = graph G ∩ W) :
    scCoderiv F p = scCoderiv G p := by
  rw [scCoderiv, scCoderiv, scDeriv_congr hW h]

theorem hasSCDPropertyAt_congr (hW : W ∈ 𝓝 p) (h : graph F ∩ W = graph G ∩ W) :
    HasSCDPropertyAt F p ↔ HasSCDPropertyAt G p := by
  rw [HasSCDPropertyAt, HasSCDPropertyAt, scDeriv_congr hW h]

theorem HasSCDPropertyAround.congr (hF : HasSCDPropertyAround F p) (hW : W ∈ 𝓝 p)
    (h : graph F ∩ W = graph G ∩ W) : HasSCDPropertyAround G p := by
  obtain ⟨U, hU, hUF⟩ := hF
  have h' : graph F ∩ interior W = graph G ∩ interior W :=
    inter_eq_inter_of_subset h interior_subset
  refine ⟨U ∩ interior W, inter_mem hU (interior_mem_nhds.2 hW), fun q ⟨hqG, hqU, hqW⟩ ↦ ?_⟩
  have hqF : q ∈ graph F := by
    have : q ∈ graph F ∩ interior W := by rw [h']; exact ⟨hqG, hqW⟩
    exact this.1
  exact (hasSCDPropertyAt_congr (isOpen_interior.mem_nhds hqW) h').1 (hUF q ⟨hqF, hqU⟩)

/-- The SCD property around `p` only depends on the graph near `p`. -/
theorem hasSCDPropertyAround_congr (hW : W ∈ 𝓝 p) (h : graph F ∩ W = graph G ∩ W) :
    HasSCDPropertyAround F p ↔ HasSCDPropertyAround G p :=
  ⟨fun hF ↦ hF.congr hW h, fun hG ↦ hG.congr hW h.symm⟩

/-! ### Local changes of variables -/

section LocalChange

variable {Φ : E × E → E × E} {D : E × E → (E × E) →L[ℝ] (E × E)} {e : (E × E) ≃L[ℝ] (E × E)}

/-- The mapping whose graph is `Φ⁻¹(gph G)`. -/
def preimageMap (Φ : E × E → E × E) (G : E → Set E) : E → Set E :=
  fun x ↦ {y | Φ (x, y) ∈ graph G}

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem graph_preimageMap (Φ : E × E → E × E) (G : E → Set E) :
    graph (preimageMap Φ G) = Φ ⁻¹' graph G := rfl

/-- Prop. 3.14, (20), of [Gfrerer–Outrata 2022] when `gph F = Φ⁻¹(gph G)` only holds near `p`:
`𝒮G(Φ p) = ∇Φ(p) 𝒮F(p)`. -/
theorem scDeriv_preimage_of_inter_eq (hW : W ∈ 𝓝 p) (hFG : graph F ∩ W = Φ ⁻¹' graph G ∩ W)
    (hD : ∀ᶠ q in 𝓝 p, HasStrictFDerivAt Φ (D q) q) (hDc : ContinuousAt D p) (he : D p = e) :
    scDeriv G (Φ p) =
      (fun L ↦ L.map ((e : (E × E) →L[ℝ] (E × E)) : (E × E) →ₗ[ℝ] (E × E))) '' scDeriv F p := by
  rw [scDeriv_congr hW (hFG.trans (congrArg (· ∩ W) (graph_preimageMap Φ G).symm)),
    scDeriv_preimage (graph_preimageMap Φ G) hD hDc he]

/-- Prop. 3.14, (20), of [Gfrerer–Outrata 2022], local form: `𝒮F(p) = ∇Φ(p)⁻¹ 𝒮G(Φ p)`. -/
theorem scDeriv_eq_image_symm_of_inter_eq (hW : W ∈ 𝓝 p)
    (hFG : graph F ∩ W = Φ ⁻¹' graph G ∩ W)
    (hD : ∀ᶠ q in 𝓝 p, HasStrictFDerivAt Φ (D q) q) (hDc : ContinuousAt D p) (he : D p = e) :
    scDeriv F p = (fun L ↦ L.map ((e.symm : (E × E) →L[ℝ] (E × E)) : (E × E) →ₗ[ℝ] (E × E))) ''
      scDeriv G (Φ p) := by
  rw [scDeriv_preimage_of_inter_eq hW hFG hD hDc he, Set.image_image]
  simp only [map_symm_map_eq, Set.image_id']

/-- Local form of the transfer of graphical smoothness [Gfrerer–Outrata 2022, proof of
Prop. 3.14]. -/
theorem graphicallySmoothAt_iff_of_inter_eq (hW : W ∈ 𝓝 q)
    (hFG : graph F ∩ W = Φ ⁻¹' graph G ∩ W)
    (hΦ : HasStrictFDerivAt Φ (e : (E × E) →L[ℝ] (E × E)) q) :
    GraphicallySmoothAt G (Φ q) ↔ GraphicallySmoothAt F q := by
  rw [graphicallySmoothAt_iff_of_preimage (graph_preimageMap Φ G) hΦ,
    graphicallySmoothAt_congr hW (hFG.trans (congrArg (· ∩ W) (graph_preimageMap Φ G).symm))]

/-- Local form of `T_{gph G}(Φ q) = ∇Φ(q) T_{gph F}(q)` [Rockafellar–Wets 1998, Exercise 6.7]. -/
theorem contingentCone_graph_eq_image_of_inter_eq (hW : W ∈ 𝓝 q)
    (hFG : graph F ∩ W = Φ ⁻¹' graph G ∩ W)
    (hΦ : HasStrictFDerivAt Φ (e : (E × E) →L[ℝ] (E × E)) q) :
    contingentCone (graph G) (Φ q) = e '' contingentCone (graph F) q := by
  rw [contingentCone_graph_eq_image_of_preimage (graph_preimageMap Φ G) hΦ,
    contingentCone_congr_of_inter_eq hW
      (hFG.trans (congrArg (· ∩ W) (graph_preimageMap Φ G).symm))]

end LocalChange

/-! ### Tangent cones to graphs of Lipschitz mappings -/

/-- If `f` is Lipschitz near `u` and `T_{gph f}(u, f u)` is a subspace, then it has dimension
`n = dim E`: calmness makes the projection onto the first factor injective, and compactness
makes it surjective [Gfrerer–Mandlmayr–Outrata–Valdman 2023, proof of Lemma 3.7(ii)]. -/
theorem finrank_eq_of_coe_eq_contingentCone_graph {f : E → E} {U : Set E} {K : ℝ≥0}
    (hf : LipschitzOnWith K f U) {u : E} (hU : U ∈ 𝓝 u) {L : Submodule ℝ (E × E)}
    (hL : (L : Set (E × E)) = contingentCone (graph fun x ↦ ({f x} : Set E)) (u, f u)) :
    finrank ℝ L = finrank ℝ E := by
  have hcalm : ∀ᶠ x' in 𝓝 u, ‖f x' - f u‖ ≤ K * ‖x' - u‖ := by
    filter_upwards [hU] with x' hx' using hf.norm_sub_le hx' (mem_of_mem_nhds hU)
  have hinj : ∀ v, ((0 : E), v) ∈ L → v = 0 := fun v hv ↦
    eq_zero_of_mk_zero_mem_contingentCone hcalm (by rw [← hL]; exact hv)
  have hsurj : ∀ w : E, ∃ v, (w, v) ∈ L := by
    intro w
    set x : ℕ → E := fun k ↦ u + (1 / ((k : ℝ) + 1)) • w with hx_def
    have hx : Tendsto x atTop (𝓝 u) := by
      have h0 : Tendsto (fun k : ℕ ↦ (1 / ((k : ℝ) + 1)) • w) atTop (𝓝 ((0 : ℝ) • w)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.smul_const w
      rw [zero_smul] at h0
      simpa [hx_def] using (tendsto_const_nhds (x := u)).add h0
    have hαx : ∀ k : ℕ, ((k : ℝ) + 1) • (x k - u) = w := by
      intro k
      rw [show x k - u = (1 / ((k : ℝ) + 1)) • w by simp [hx_def], smul_smul,
        mul_one_div_cancel (by positivity), one_smul]
    set y : ℕ → E := fun k ↦ ((k : ℝ) + 1) • (f (x k) - f u) with hy_def
    have hbd : ∀ᶠ k in atTop, y k ∈ Metric.closedBall (0 : E) (K * ‖w‖) := by
      filter_upwards [hx.eventually hU] with k hk
      rw [mem_closedBall_zero_iff, hy_def, norm_smul, Real.norm_of_nonneg (by positivity)]
      calc ((k : ℝ) + 1) * ‖f (x k) - f u‖ ≤ ((k : ℝ) + 1) * (K * ‖x k - u‖) :=
            mul_le_mul_of_nonneg_left (hf.norm_sub_le hk (mem_of_mem_nhds hU)) (by positivity)
        _ = K * ‖((k : ℝ) + 1) • (x k - u)‖ := by
            rw [norm_smul, Real.norm_of_nonneg (by positivity)]; ring
        _ = K * ‖w‖ := by rw [hαx]
    obtain ⟨a, -, φ, hφ, hlim⟩ :=
      tendsto_subseq_of_frequently_bounded Metric.isBounded_closedBall hbd.frequently
    refine ⟨a, ?_⟩
    rw [← SetLike.mem_coe, hL]
    have hfc : ContinuousAt f u := continuousAt_of_calm hcalm
    have hxφ := hx.comp hφ.tendsto_atTop
    refine mem_contingentCone_of_eventually (mem_singleton _)
      (fun k ↦ (x (φ k), f (x (φ k)))) (fun k ↦ ((φ k : ℝ) + 1))
      (Eventually.of_forall fun k ↦ ⟨mem_singleton _, by positivity⟩)
      (hxφ.prodMk_nhds (hfc.tendsto.comp hxφ)) ?_
    refine ((tendsto_const_nhds (x := w)).prodMk_nhds hlim).congr fun k ↦ ?_
    refine Prod.ext ?_ ?_
    · simp only [Prod.smul_fst, Prod.fst_sub]
      exact (hαx (φ k)).symm
    · simp [hy_def]
  let π : L →ₗ[ℝ] E := (LinearMap.fst ℝ E E).comp L.subtype
  have hπi : Function.Injective π := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have h1 : (z : E × E).1 = 0 := hz
    have h2 : ((0 : E), (z : E × E).2) ∈ L := by
      rw [show ((0 : E), (z : E × E).2) = (z : E × E) from Prod.ext h1.symm rfl]
      exact z.2
    exact Subtype.ext (Prod.ext h1 (hinj _ h2))
  have hπs : Function.Surjective π := fun w ↦ by
    obtain ⟨v, hv⟩ := hsurj w
    exact ⟨⟨(w, v), hv⟩, rfl⟩
  exact (LinearEquiv.ofBijective π ⟨hπi, hπs⟩).finrank_eq

/-! ### Graphically Lipschitzian mappings: Def. 3.16 -/

/-- The data of Def. 3.16 of [Gfrerer–Outrata 2022]: on the open set `W`, `Φ` is `C¹` (strict
derivative `D q`, `D` continuous on `W`) and injective with invertible derivative, and
`Φ(gph F ∩ W)` is the graph of `f`, Lipschitz on the open set `U`, with modulus `K`. -/
structure IsGraphLipschitzTransform (F : E → Set E) (W : Set (E × E)) (Φ : E × E → E × E)
    (D : E × E → (E × E) →L[ℝ] (E × E)) (U : Set E) (f : E → E) (K : ℝ≥0) : Prop where
  isOpen_W : IsOpen W
  isOpen_U : IsOpen U
  hasStrictFDerivAt : ∀ q ∈ W, HasStrictFDerivAt Φ (D q) q
  continuousOn : ContinuousOn D W
  exists_equiv : ∀ q ∈ W, ∃ e : (E × E) ≃L[ℝ] (E × E), (e : (E × E) →L[ℝ] (E × E)) = D q
  injOn : InjOn Φ W
  lipschitzOnWith : LipschitzOnWith K f U
  image_eq : Φ '' (graph F ∩ W) = graph (fun u ↦ ({f u} : Set E)) ∩ (U ×ˢ univ)

/-- `F` is graphically Lipschitzian (of dimension `n = dim E`) at `p ∈ gph F`
[Gfrerer–Outrata 2022, Def. 3.16], [Rockafellar–Wets 1998, Def. 9.66]: there are an open
neighborhood `W` of `p` and a transformation mapping `Φ`, `C¹` and one-to-one on `W` with
invertible derivative, such that `Φ(gph F ∩ W)` is the graph of a Lipschitz mapping on an open
set. -/
def GraphicallyLipschitzianAt (F : E → Set E) (p : E × E) : Prop :=
  p ∈ graph F ∧ ∃ (W : Set (E × E)) (Φ : E × E → E × E) (D : E × E → (E × E) →L[ℝ] (E × E))
    (U : Set E) (f : E → E) (K : ℝ≥0), p ∈ W ∧ IsGraphLipschitzTransform F W Φ D U f K

namespace IsGraphLipschitzTransform

variable {Φ : E × E → E × E} {D : E × E → (E × E) →L[ℝ] (E × E)} {U : Set E} {f : E → E}
  {K : ℝ≥0} (h : IsGraphLipschitzTransform F W Φ D U f K)
include h

omit [FiniteDimensional ℝ E] in
/-- `Φ` maps `gph F ∩ W` into `gph f` over `U`. -/
theorem exists_apply_eq (hq : q ∈ graph F) (hqW : q ∈ W) : ∃ u ∈ U, Φ q = (u, f u) := by
  have : Φ q ∈ Φ '' (graph F ∩ W) := mem_image_of_mem Φ ⟨hq, hqW⟩
  rw [h.image_eq] at this
  exact ⟨(Φ q).1, this.2.1, Prod.ext rfl this.1⟩

omit [FiniteDimensional ℝ E] in
/-- Near `q ∈ gph F ∩ W`, `gph F = Φ⁻¹(gph f)`. -/
theorem nhds_inter_eq (hq : q ∈ graph F) (hqW : q ∈ W) :
    W ∩ Φ ⁻¹' (U ×ˢ univ) ∈ 𝓝 q ∧
      graph F ∩ (W ∩ Φ ⁻¹' (U ×ˢ univ)) =
        Φ ⁻¹' graph (fun u ↦ ({f u} : Set E)) ∩ (W ∩ Φ ⁻¹' (U ×ˢ univ)) := by
  obtain ⟨u, hu, hΦq⟩ := h.exists_apply_eq hq hqW
  refine ⟨inter_mem (h.isOpen_W.mem_nhds hqW)
    ((h.hasStrictFDerivAt q hqW).continuousAt.preimage_mem_nhds
      ((h.isOpen_U.prod isOpen_univ).mem_nhds (by rw [hΦq]; exact mk_mem_prod hu trivial))), ?_⟩
  ext z
  constructor
  · rintro ⟨hz, hzW, hzU⟩
    have : Φ z ∈ Φ '' (graph F ∩ W) := mem_image_of_mem Φ ⟨hz, hzW⟩
    rw [h.image_eq] at this
    exact ⟨this.1, hzW, hzU⟩
  · rintro ⟨hz, hzW, hzU⟩
    have : Φ z ∈ graph (fun u ↦ ({f u} : Set E)) ∩ (U ×ˢ univ) := ⟨hz, hzU⟩
    rw [← h.image_eq] at this
    obtain ⟨z', ⟨hz'F, hz'W⟩, hz'⟩ := this
    rw [← h.injOn hz'W hzW hz']
    exact ⟨hz'F, hz'W, by rw [h.injOn hz'W hzW hz']; exact hzU⟩

omit [FiniteDimensional ℝ E] in
theorem eventually_hasStrictFDerivAt (hqW : q ∈ W) :
    ∀ᶠ q' in 𝓝 q, HasStrictFDerivAt Φ (D q') q' :=
  eventually_of_mem (h.isOpen_W.mem_nhds hqW) h.hasStrictFDerivAt

omit [FiniteDimensional ℝ E] in
theorem continuousAt (hqW : q ∈ W) : ContinuousAt D q :=
  h.continuousOn.continuousAt (h.isOpen_W.mem_nhds hqW)

/-- Remark 3.18 of [Gfrerer–Outrata 2022]: `Φ(O_F ∩ W) = O_f`; a point `q ∈ gph F ∩ W` is a point
of graphical smoothness of `F` iff `f` is differentiable at `π₁(Φ q)`. -/
theorem graphicallySmoothAt_iff (hq : q ∈ graph F) (hqW : q ∈ W) :
    GraphicallySmoothAt F q ↔ DifferentiableAt ℝ f (Φ q).1 := by
  obtain ⟨hW', hloc⟩ := h.nhds_inter_eq hq hqW
  obtain ⟨e, he⟩ := h.exists_equiv q hqW
  have hΦ : HasStrictFDerivAt Φ (e : (E × E) →L[ℝ] (E × E)) q := he ▸ h.hasStrictFDerivAt q hqW
  obtain ⟨u, hu, hΦq⟩ := h.exists_apply_eq hq hqW
  rw [← graphicallySmoothAt_iff_of_inter_eq hW' hloc hΦ, hΦq]
  exact graphicallySmoothAt_iff_differentiableAt h.lipschitzOnWith (h.isOpen_U.mem_nhds hu)

/-- Prop. 3.17, first equality in (24a), of [Gfrerer–Outrata 2022]:
`𝒮F(q) = ∇Φ(q)⁻¹ 𝒮f(π₁(Φ q))` for `q ∈ gph F ∩ W`. -/
theorem scDeriv_eq (hq : q ∈ graph F) (hqW : q ∈ W) {e : (E × E) ≃L[ℝ] (E × E)}
    (he : (e : (E × E) →L[ℝ] (E × E)) = D q) :
    scDeriv F q = (fun L ↦ L.map ((e.symm : (E × E) →L[ℝ] (E × E)) : (E × E) →ₗ[ℝ] (E × E))) ''
      scDeriv (fun u ↦ ({f u} : Set E)) (Φ q) := by
  obtain ⟨hW', hloc⟩ := h.nhds_inter_eq hq hqW
  exact scDeriv_eq_image_symm_of_inter_eq hW' hloc (h.eventually_hasStrictFDerivAt hqW)
    (h.continuousAt hqW) he.symm

/-- Prop. 3.17, (24a), of [Gfrerer–Outrata 2022]: for `q ∈ gph F ∩ W`,
`𝒮F(q) = {∇Φ(q)⁻¹ rge(I, B) | B ∈ ∇̄f(u)}` with `u = π₁(Φ q)`. -/
theorem mem_scDeriv_iff (hq : q ∈ graph F) (hqW : q ∈ W) {e : (E × E) ≃L[ℝ] (E × E)}
    (he : (e : (E × E) →L[ℝ] (E × E)) = D q) {L : Submodule ℝ (E × E)} :
    L ∈ scDeriv F q ↔ ∃ B ∈ bSubdiff f (Φ q).1,
      L = (B : E →ₗ[ℝ] E).graph.map ((e.symm : (E × E) →L[ℝ] (E × E)) : (E × E) →ₗ[ℝ] (E × E)) := by
  obtain ⟨u, hu, hΦq⟩ := h.exists_apply_eq hq hqW
  have hS : ∀ L' : Submodule ℝ (E × E), L' ∈ scDeriv (fun u ↦ ({f u} : Set E)) (u, f u) ↔
      ∃ B ∈ bSubdiff f u, L' = (B : E →ₗ[ℝ] E).graph := fun L' ↦
    mem_scDeriv_iff_of_lipschitzOnWith h.lipschitzOnWith (h.isOpen_U.mem_nhds hu)
  rw [h.scDeriv_eq hq hqW he, hΦq]
  constructor
  · rintro ⟨L', hL', rfl⟩
    obtain ⟨B, hB, rfl⟩ := (hS _).1 hL'
    exact ⟨B, hB, rfl⟩
  · rintro ⟨B, hB, rfl⟩
    exact ⟨_, (hS _).2 ⟨B, hB, rfl⟩, rfl⟩

/-- Prop. 3.17 of [Gfrerer–Outrata 2022], the SC adjoint derivative: for `q ∈ gph F ∩ W`,
`𝒮*F(q) = {(∇Φ(q)⁻¹ rge(I, B))* | B ∈ ∇̄f(u)}` with `u = π₁(Φ q)`. -/
theorem mem_scCoderiv_iff (hq : q ∈ graph F) (hqW : q ∈ W) {e : (E × E) ≃L[ℝ] (E × E)}
    (he : (e : (E × E) →L[ℝ] (E × E)) = D q) {L : Submodule ℝ (E × E)} :
    L ∈ scCoderiv F q ↔ ∃ B ∈ bSubdiff f (Φ q).1, L = adjointSubspace
      ((B : E →ₗ[ℝ] E).graph.map ((e.symm : (E × E) →L[ℝ] (E × E)) : (E × E) →ₗ[ℝ] (E × E))) := by
  constructor
  · rintro ⟨L', hL', rfl⟩
    obtain ⟨B, hB, rfl⟩ := (h.mem_scDeriv_iff hq hqW he).1 hL'
    exact ⟨B, hB, rfl⟩
  · rintro ⟨B, hB, rfl⟩
    exact ⟨_, (h.mem_scDeriv_iff hq hqW he).2 ⟨B, hB, rfl⟩, rfl⟩

/-- Prop. 3.17 of [Gfrerer–Outrata 2022]: `F` has the SCD property at every `q ∈ gph F ∩ W`. -/
theorem hasSCDPropertyAt (hq : q ∈ graph F) (hqW : q ∈ W) : HasSCDPropertyAt F q := by
  obtain ⟨e, he⟩ := h.exists_equiv q hqW
  obtain ⟨u, hu, hΦq⟩ := h.exists_apply_eq hq hqW
  rw [HasSCDPropertyAt, h.scDeriv_eq hq hqW he, image_nonempty, hΦq]
  exact hasSCDPropertyAt_of_lipschitzOnWith h.lipschitzOnWith (h.isOpen_U.mem_nhds hu)

/-- Lemma 3.7(ii) of [Gfrerer–Mandlmayr–Outrata–Valdman 2023]: if `T_{gph F}(q)` is a subspace
for some `q ∈ gph F ∩ W`, then it has dimension `n = dim E`. -/
theorem finrank_eq_of_coe_eq_contingentCone (hq : q ∈ graph F) (hqW : q ∈ W)
    {L : Submodule ℝ (E × E)} (hL : (L : Set (E × E)) = contingentCone (graph F) q) :
    finrank ℝ L = finrank ℝ E := by
  obtain ⟨hW', hloc⟩ := h.nhds_inter_eq hq hqW
  obtain ⟨e, he⟩ := h.exists_equiv q hqW
  have hΦ : HasStrictFDerivAt Φ (e : (E × E) →L[ℝ] (E × E)) q := he ▸ h.hasStrictFDerivAt q hqW
  have hcone := contingentCone_graph_eq_image_of_inter_eq hW' hloc hΦ
  obtain ⟨u, hu, hΦq⟩ := h.exists_apply_eq hq hqW
  rw [hΦq] at hcone
  have hL' : ((L.map ((e : (E × E) →L[ℝ] (E × E)) : (E × E) →ₗ[ℝ] (E × E)) : Submodule ℝ (E × E))
      : Set (E × E)) = contingentCone (graph fun x ↦ ({f x} : Set E)) (u, f u) := by
    rw [Submodule.map_coe, hcone, hL]
    rfl
  rw [← finrank_eq_of_coe_eq_contingentCone_graph h.lipschitzOnWith (h.isOpen_U.mem_nhds hu) hL']
  exact (Submodule.equivMapOfInjective _ e.injective L).finrank_eq

end IsGraphLipschitzTransform

/-- Prop. 3.17 of [Gfrerer–Outrata 2022]: a graphically Lipschitzian mapping has the SCD
property around the reference point. -/
theorem GraphicallyLipschitzianAt.hasSCDPropertyAround (h : GraphicallyLipschitzianAt F p) :
    HasSCDPropertyAround F p := by
  obtain ⟨-, W, Φ, D, U, f, K, hpW, hT⟩ := h
  exact ⟨W, hT.isOpen_W.mem_nhds hpW, fun q ⟨hq, hqW⟩ ↦ hT.hasSCDPropertyAt hq hqW⟩

/-! ### Strong metric regularity of `F + h`: Cor. 3.19 -/

/-- `F⁻¹` has a Lipschitz continuous single-valued localization around `(y₀, x₀)`: there are
neighborhoods `U` of `y₀` and `X` of `x₀` and a mapping `g`, Lipschitz on `U`, with
`F⁻¹(y) ∩ X = {g y}` for `y ∈ U`. By [Gfrerer–Outrata 2022, Thm. 2.6]
([Dontchev–Rockafellar 2014, Prop. 3G.1]) this characterizes strong metric regularity of `F`
around `(x₀, y₀)`. -/
def HasLipschitzInvLocalization (F : E → Set E) (x₀ y₀ : E) : Prop :=
  ∃ U ∈ 𝓝 y₀, ∃ X ∈ 𝓝 x₀, ∃ g : E → E, ∃ K : ℝ≥0,
    LipschitzOnWith K g U ∧ ∀ y ∈ U, invMap F y ∩ X = {g y}

section Add

/-- The transformation mapping `Φ(x, y) = (y + h x, x)` of [Gfrerer–Outrata 2022, Cor. 3.19]. -/
def addSwap (h : E → E) (q : E × E) : E × E := (q.2 + h q.1, q.1)

/-- The derivative `∇Φ(x, y) = [∇h(x) I; I 0]` of `addSwap`, a linear isomorphism. -/
noncomputable def addSwapEquiv (M : E →L[ℝ] E) : (E × E) ≃L[ℝ] (E × E) :=
  (shear M).trans (ContinuousLinearEquiv.prodComm ℝ E E)

omit [FiniteDimensional ℝ E] in
@[simp] theorem addSwapEquiv_apply (M : E →L[ℝ] E) (w : E × E) :
    addSwapEquiv M w = (w.2 + M w.1, w.1) := by
  simp [addSwapEquiv, shear]

omit [FiniteDimensional ℝ E] in
@[simp] theorem addSwapEquiv_symm_apply (M : E →L[ℝ] E) (w : E × E) :
    (addSwapEquiv M).symm w = (w.2, w.1 - M w.2) := by
  apply (addSwapEquiv M).injective
  simp

omit [FiniteDimensional ℝ E] in
theorem continuous_addSwapEquiv :
    Continuous fun M : E →L[ℝ] E ↦ ((addSwapEquiv M : (E × E) ≃L[ℝ] (E × E)) :
      (E × E) →L[ℝ] (E × E)) := by
  have : (fun M : E →L[ℝ] E ↦ ((addSwapEquiv M : (E × E) ≃L[ℝ] (E × E)) :
      (E × E) →L[ℝ] (E × E))) = fun M ↦
        (ContinuousLinearEquiv.prodComm ℝ E E : (E × E) →L[ℝ] (E × E)).comp (shearCLM M) := by
    funext M
    ext w <;> simp
  rw [this]
  exact continuous_const.clm_comp continuous_shearCLM

omit [FiniteDimensional ℝ E] in
theorem hasStrictFDerivAt_addSwap {h : E → E} {M : E →L[ℝ] E} {q : E × E}
    (hq : HasStrictFDerivAt h M q.1) :
    HasStrictFDerivAt (addSwap h) ((addSwapEquiv M : (E × E) ≃L[ℝ] (E × E)) :
      (E × E) →L[ℝ] (E × E)) q := by
  have h1 := (hasStrictFDerivAt_snd.add (hq.comp q hasStrictFDerivAt_fst)).prodMk
    (hasStrictFDerivAt_fst (p := q))
  refine h1.congr_fderiv ?_
  ext w <;> simp

omit [FiniteDimensional ℝ E] in
/-- `∇Φ(x, y)⁻¹ rge(I, B) = rge(B, I - ∇h(x) B)` [Gfrerer–Outrata 2022, proof of Cor. 3.19]. -/
theorem map_symm_addSwapEquiv_graph (M B : E →L[ℝ] E) :
    (B : E →ₗ[ℝ] E).graph.map
        (((addSwapEquiv M).symm : (E × E) →L[ℝ] (E × E)) : (E × E) →ₗ[ℝ] (E × E)) =
      LinearMap.range ((B : E →ₗ[ℝ] E).prod (LinearMap.id - (M : E →ₗ[ℝ] E) ∘ₗ (B : E →ₗ[ℝ] E))) := by
  rw [LinearMap.graph_eq_range_prod, ← LinearMap.range_comp]
  congr 1
  refine LinearMap.ext fun w ↦ ?_
  simp

/-- `rge(B, I - M B)* = rge(Bᵀ, I - Mᵀ Bᵀ)` [Gfrerer–Outrata 2022, (25b)]. -/
theorem adjointSubspace_range_prod (M B : E →L[ℝ] E) :
    adjointSubspace
        (LinearMap.range ((B : E →ₗ[ℝ] E).prod (LinearMap.id - (M : E →ₗ[ℝ] E) ∘ₗ (B : E →ₗ[ℝ] E)))) =
      LinearMap.range ((ContinuousLinearMap.adjoint B : E →ₗ[ℝ] E).prod (LinearMap.id -
        (ContinuousLinearMap.adjoint M : E →ₗ[ℝ] E) ∘ₗ (ContinuousLinearMap.adjoint B : E →ₗ[ℝ] E))) := by
  have hinj : ∀ C N : E →L[ℝ] E,
      Function.Injective ((C : E →ₗ[ℝ] E).prod (LinearMap.id - (N : E →ₗ[ℝ] E) ∘ₗ (C : E →ₗ[ℝ] E))) := by
    intro C N z z' hzz'
    have h1 : C z = C z' := by simpa using congrArg Prod.fst hzz'
    have h2 : z - N (C z) = z' - N (C z') := by simpa using congrArg Prod.snd hzz'
    rw [h1] at h2
    exact sub_left_injective h2
  symm
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨z, rfl⟩
    rw [mem_adjointSubspace_iff]
    rintro _ ⟨w, rfl⟩
    show ⟪z - ContinuousLinearMap.adjoint M (ContinuousLinearMap.adjoint B z), B w⟫_ℝ =
      ⟪ContinuousLinearMap.adjoint B z, w - M (B w)⟫_ℝ
    rw [inner_sub_left, inner_sub_right, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
  · rw [finrank_adjointSubspace_of_eq (LinearMap.finrank_range_of_inj (hinj B M)),
      LinearMap.finrank_range_of_inj (hinj _ _)]

variable {h : E → E} {Dh : E → E →L[ℝ] E} {V U X : Set E} {x₀ y₀ : E} {g : E → E} {K : ℝ≥0}

omit [FiniteDimensional ℝ E] in
/-- Cor. 3.19 of [Gfrerer–Outrata 2022]: if `h` is `C¹` on an open neighborhood `V` of `x₀` and
`(F + h)⁻¹` has a Lipschitz continuous single-valued localization `g` around `(y₀ + h x₀, x₀)`, then
`F` is graphically Lipschitzian at `(x₀, y₀)` with transformation mapping `Φ(x, y) = (y + h x, x)`
and Lipschitz mapping `g`. -/
theorem isGraphLipschitzTransform_of_add (hp : y₀ ∈ F x₀) (hV : IsOpen V) (hxV : x₀ ∈ V)
    (hh : ∀ x ∈ V, HasStrictFDerivAt h (Dh x) x) (hDh : ContinuousOn Dh V)
    (hU : U ∈ 𝓝 (y₀ + h x₀)) (hX : X ∈ 𝓝 x₀) (hg : LipschitzOnWith K g U)
    (hloc : ∀ y ∈ U, invMap (fun x ↦ (fun v ↦ v + h x) '' F x) y ∩ X = {g y}) :
    ∃ W : Set (E × E), ∃ U' ⊆ U, (x₀, y₀) ∈ W ∧ W ⊆ V ×ˢ univ ∧
      IsGraphLipschitzTransform F W (addSwap h)
        (fun q ↦ ((addSwapEquiv (Dh q.1) : (E × E) ≃L[ℝ] (E × E)) : (E × E) →L[ℝ] (E × E)))
        U' g K := by
  set S : E → Set E := fun x ↦ (fun v ↦ v + h x) '' F x with hS
  set X' := interior X ∩ V with hX'_def
  set U' := interior U ∩ g ⁻¹' X' with hU'_def
  have hgc : ContinuousOn g (interior U) := (hg.mono interior_subset).continuousOn
  have hX' : IsOpen X' := isOpen_interior.inter hV
  have hU' : IsOpen U' := hgc.isOpen_inter_preimage isOpen_interior hX'
  have hgy₀ : g (y₀ + h x₀) = x₀ := by
    have hmem : x₀ ∈ invMap S (y₀ + h x₀) ∩ X := ⟨⟨y₀, hp, rfl⟩, mem_of_mem_nhds hX⟩
    rw [hloc _ (mem_of_mem_nhds hU)] at hmem
    exact hmem.symm
  have hhc : ContinuousOn h V := fun x hx ↦ (hh x hx).continuousAt.continuousWithinAt
  have hΦc : ContinuousOn (addSwap h) (X' ×ˢ univ) :=
    (continuousOn_snd.add (hhc.comp continuousOn_fst fun q hq ↦ hq.1.2)).prodMk continuousOn_fst
  set W := X' ×ˢ univ ∩ addSwap h ⁻¹' (U' ×ˢ univ) with hW_def
  have hW : IsOpen W := hΦc.isOpen_inter_preimage (hX'.prod isOpen_univ) (hU'.prod isOpen_univ)
  refine ⟨W, U', fun y hy ↦ interior_subset hy.1, ⟨⟨⟨mem_interior_iff_mem_nhds.2 hX, hxV⟩,
    trivial⟩, ⟨mem_interior_iff_mem_nhds.2 hU, ?_⟩, trivial⟩, fun q hq ↦ ⟨hq.1.1.2, trivial⟩,
    ⟨hW, hU', fun q hq ↦ hasStrictFDerivAt_addSwap (hh q.1 hq.1.1.2),
    continuous_addSwapEquiv.comp_continuousOn (hDh.comp continuousOn_fst fun q hq ↦ hq.1.1.2),
    fun q _ ↦ ⟨_, rfl⟩, ?_, hg.mono fun y hy ↦ interior_subset hy.1, ?_⟩⟩
  · show g (y₀ + h x₀) ∈ X'
    rw [hgy₀]
    exact ⟨mem_interior_iff_mem_nhds.2 hX, hxV⟩
  · intro z _ z' _ hzz'
    have h1 : z.1 = z'.1 := congrArg Prod.snd hzz'
    have h2 : z.2 + h z.1 = z'.2 + h z'.1 := congrArg Prod.fst hzz'
    rw [h1] at h2
    exact Prod.ext h1 (add_right_cancel h2)
  · ext ⟨u, v⟩
    constructor
    · rintro ⟨⟨x, y⟩, ⟨hxy, ⟨⟨hxX, -⟩, -⟩, ⟨hu', -⟩⟩, heq⟩
      simp only [addSwap, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      have hx' : x ∈ invMap S (y + h x) ∩ X := ⟨⟨y, hxy, rfl⟩, interior_subset hxX⟩
      rw [hloc (y + h x) (interior_subset hu'.1)] at hx'
      exact ⟨hx', hu', trivial⟩
    · rintro ⟨hv, hu, -⟩
      have hv' : v = g u := hv
      have hgu : g u ∈ invMap S u ∩ X := by
        rw [hloc u (interior_subset hu.1)]; exact mem_singleton _
      obtain ⟨y, hy, hyu⟩ := hgu.1
      replace hyu : y + h (g u) = u := hyu
      refine ⟨(g u, y), ⟨hy, ⟨hu.2, trivial⟩, ?_⟩, ?_⟩
      · show y + h (g u) ∈ U' ∧ g u ∈ univ
        rw [hyu]; exact ⟨hu, trivial⟩
      · show (y + h (g u), g u) = (u, v)
        rw [hyu, hv']

/-- Cor. 3.19, (25a), of [Gfrerer–Outrata 2022]: under the assumptions of
`isGraphLipschitzTransform_of_add`, for `(x, y) ∈ gph F` near `(x₀, y₀)`,
`𝒮F(x, y) = {rge(B, I - ∇h(x) B) | B ∈ ∇̄g(y + h x)}`. -/
theorem mem_scDeriv_iff_of_add (hp : y₀ ∈ F x₀) (hV : IsOpen V) (hxV : x₀ ∈ V)
    (hh : ∀ x ∈ V, HasStrictFDerivAt h (Dh x) x) (hDh : ContinuousOn Dh V)
    (hU : U ∈ 𝓝 (y₀ + h x₀)) (hX : X ∈ 𝓝 x₀) (hg : LipschitzOnWith K g U)
    (hloc : ∀ y ∈ U, invMap (fun x ↦ (fun v ↦ v + h x) '' F x) y ∩ X = {g y}) :
    ∀ᶠ q in 𝓝 (x₀, y₀), q ∈ graph F → ∀ L : Submodule ℝ (E × E),
      (L ∈ scDeriv F q ↔ ∃ B ∈ bSubdiff g (q.2 + h q.1), L = LinearMap.range
        ((B : E →ₗ[ℝ] E).prod (LinearMap.id - (Dh q.1 : E →ₗ[ℝ] E) ∘ₗ (B : E →ₗ[ℝ] E)))) ∧
      (L ∈ scCoderiv F q ↔ ∃ B ∈ bSubdiff g (q.2 + h q.1), L = LinearMap.range
        ((ContinuousLinearMap.adjoint B : E →ₗ[ℝ] E).prod (LinearMap.id -
          (ContinuousLinearMap.adjoint (Dh q.1) : E →ₗ[ℝ] E) ∘ₗ
            (ContinuousLinearMap.adjoint B : E →ₗ[ℝ] E)))) := by
  obtain ⟨W, U', -, hpW, -, hT⟩ := isGraphLipschitzTransform_of_add hp hV hxV hh hDh hU hX hg hloc
  filter_upwards [hT.isOpen_W.mem_nhds hpW] with q hqW hq L
  constructor
  · rw [hT.mem_scDeriv_iff hq hqW rfl]
    simp only [map_symm_addSwapEquiv_graph]
    rfl
  · rw [hT.mem_scCoderiv_iff hq hqW rfl]
    simp only [map_symm_addSwapEquiv_graph, adjointSubspace_range_prod]
    rfl

omit [FiniteDimensional ℝ E] in
/-- Cor. 3.19 of [Gfrerer–Outrata 2022]: if `h` is `C¹` near `x₀` and `F + h` is strongly
metrically regular around `(x₀, y₀ + h x₀)` (in the form `HasLipschitzInvLocalization`), then `F`
is graphically Lipschitzian at `(x₀, y₀)`. -/
theorem graphicallyLipschitzianAt_of_add (hp : y₀ ∈ F x₀) (hV : IsOpen V) (hxV : x₀ ∈ V)
    (hh : ∀ x ∈ V, HasStrictFDerivAt h (Dh x) x) (hDh : ContinuousOn Dh V)
    (hreg : HasLipschitzInvLocalization (fun x ↦ (fun v ↦ v + h x) '' F x) x₀ (y₀ + h x₀)) :
    GraphicallyLipschitzianAt F (x₀, y₀) := by
  obtain ⟨U, hU, X, hX, g, K, hg, hloc⟩ := hreg
  obtain ⟨W, U', -, hpW, -, hT⟩ := isGraphLipschitzTransform_of_add hp hV hxV hh hDh hU hX hg hloc
  exact ⟨hp, W, _, _, U', g, K, hpW, hT⟩

/-- Cor. 3.19 of [Gfrerer–Outrata 2022]: under the assumptions of
`graphicallyLipschitzianAt_of_add`, `F` has the SCD property around `(x₀, y₀)`. -/
theorem hasSCDPropertyAround_of_add (hp : y₀ ∈ F x₀) (hV : IsOpen V) (hxV : x₀ ∈ V)
    (hh : ∀ x ∈ V, HasStrictFDerivAt h (Dh x) x) (hDh : ContinuousOn Dh V)
    (hreg : HasLipschitzInvLocalization (fun x ↦ (fun v ↦ v + h x) '' F x) x₀ (y₀ + h x₀)) :
    HasSCDPropertyAround F (x₀, y₀) :=
  (graphicallyLipschitzianAt_of_add hp hV hxV hh hDh hreg).hasSCDPropertyAround

end Add

end VariationalAnalysis
