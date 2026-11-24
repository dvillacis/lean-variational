/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.SpecificLimits.Basic
import VariationalAnalysis.SCD.Adjoint
import VariationalAnalysis.Coderivative.Basic
import VariationalAnalysis.Tangent.Contingent
import VariationalAnalysis.Normal.Limiting

/-!
# Subspace containing derivatives (SCD mappings)

Following [Gfrerer–Outrata 2022, Section 3], let `E` be a finite-dimensional real inner product
space of dimension `n` and `F : E → Set E`. A point `p ∈ gph F` is a point of *graphical
smoothness* (of dimension `n`) if the contingent cone `T_{gph F}(p)` is an `n`-dimensional
subspace (Def. 3.3); the set of these points is `O_F`. The *SC derivative* `𝒮F(p)` collects the
limits, in the Grassmannian metric, of tangent subspaces `T_{gph F}(pₖ)` along `O_F ∋ pₖ → p`,
and the *SC adjoint derivative* is `𝒮*F(p) = {L* | L ∈ 𝒮F(p)}` (Remark 3.5). `F` has the *SCD
property* at `p` if `𝒮F(p) ≠ ∅`.

Normals live in `StrongDual ℝ E` in this library; an element `(y*, x*)` of a subspace of
`E × E` corresponds to the functional `(u, v) ↦ ⟪x*, u⟫ - ⟪y*, v⟫`, i.e. the pair
`(toDual x*, -toDual y*)` used by `coderiv`.

## Main declarations

* `GraphicallySmoothAt F p`: `p ∈ O_F` [Gfrerer–Outrata 2022, Def. 3.3].
* `tangentSubspace F p`: the span of `T_{gph F}(p)`; equal to `T_{gph F}(p)` on `O_F`.
* `scDeriv F p`, `scCoderiv F p`: `𝒮F(p)` and `𝒮*F(p)` [Gfrerer–Outrata 2022, Def. 3.3,
  Remark 3.5].
* `HasSCDPropertyAt`, `HasSCDPropertyAround`, `IsSCDMapping` [Gfrerer–Outrata 2022, Def. 3.3].
* `sharpTangentCone`, `sharpDeriv`: the outer limiting tangent cone `T♯` and the derivative
  `D♯F` [Gfrerer–Outrata 2022, Def. 3.8].

## Main results

* `GraphicallySmoothAt.mem_adjoint_tangentSubspace_iff`: Remark 3.4 of
  [Gfrerer–Outrata 2022]: on `O_F` the regular coderivative has graph `T_{gph F}(p)*`.
* `mem_scCoderiv_iff`: Remark 3.5: `𝒮*F(p)` is the limit set of the adjoint tangent subspaces.
* `hasSCDPropertyAt_iff_mem_closure`: Lemma 3.6: `F` has the SCD property at `p` iff
  `p ∈ cl O_F`.
* `toDual_mem_coderiv_of_mem_scCoderiv`: Lemma 3.7: `⋃ 𝒮*F(p) ⊆ gph D*F(p)`.
* `mem_sharpTangentCone_of_mem_scDeriv`: Lemma 3.10: `⋃ 𝒮F(p) ⊆ gph D♯F(p)`.
* `mem_scDeriv_of_tendsto`: Lemma 3.13 (robustness): `Lim sup_{q → p} 𝒮F(q) ⊆ 𝒮F(p)`.
-/

open Filter Topology Set Module InnerProductSpace
open scoped InnerProductSpace

namespace VariationalAnalysis

section SharpCone

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The outer limiting tangent cone `T♯_Ω(x) = Lim sup_{x' →Ω x} T_Ω(x')`
[Gfrerer–Outrata 2022, Def. 3.8]. -/
def sharpTangentCone (Ω : Set X) (x : X) : Set X :=
  outerLimit (𝓝[Ω] x) (contingentCone Ω)

/-- For `x ∈ Ω`, the contingent cone is contained in the outer limiting tangent cone:
`T_Ω(x) ⊆ T♯_Ω(x)`. -/
theorem contingentCone_subset_sharpTangentCone {Ω : Set X} {x : X} (hx : x ∈ Ω) :
    contingentCone Ω x ⊆ sharpTangentCone Ω x :=
  subset_outerLimit (pure_le_nhdsWithin hx) _

/-- The outer limiting tangent cone `T♯_Ω(x)` is closed. -/
theorem isClosed_sharpTangentCone (Ω : Set X) (x : X) : IsClosed (sharpTangentCone Ω x) :=
  isClosed_outerLimit_nhdsWithin _

end SharpCone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : E → Set E} {p q : E × E}

/-- The outer graphical derivative `D♯F(x, y)`, with graph `T♯_{gph F}(x, y)`
[Gfrerer–Outrata 2022, Def. 3.8]. -/
def sharpDeriv (F : E → Set E) (x y : E) (u : E) : Set E :=
  {v | (u, v) ∈ sharpTangentCone (graph F) (x, y)}

/-! ### Points of graphical smoothness -/

/-- `F` is graphically smooth of dimension `n = dim E` at `p ∈ gph F` if `T_{gph F}(p)` is an
`n`-dimensional subspace [Gfrerer–Outrata 2022, Def. 3.3]. -/
def GraphicallySmoothAt (F : E → Set E) (p : E × E) : Prop :=
  p ∈ graph F ∧ ∃ L : Submodule ℝ (E × E), finrank ℝ L = finrank ℝ E ∧
    (L : Set (E × E)) = contingentCone (graph F) p

/-- The subspace spanned by `T_{gph F}(p)`; it is `T_{gph F}(p)` itself on `O_F`. -/
noncomputable def tangentSubspace (F : E → Set E) (p : E × E) : Submodule ℝ (E × E) :=
  Submodule.span ℝ (contingentCone (graph F) p)

omit [FiniteDimensional ℝ E] in
/-- At a point of graphical smoothness, `tangentSubspace F p` is the contingent cone
`T_{gph F}(p)` as a set. -/
theorem GraphicallySmoothAt.coe_tangentSubspace (h : GraphicallySmoothAt F p) :
    (tangentSubspace F p : Set (E × E)) = contingentCone (graph F) p := by
  obtain ⟨-, L, -, hL⟩ := h
  rw [tangentSubspace, ← hL, Submodule.span_eq]

omit [FiniteDimensional ℝ E] in
/-- At a point of graphical smoothness, `w ∈ tangentSubspace F p` iff `w ∈ T_{gph F}(p)`. -/
theorem GraphicallySmoothAt.mem_tangentSubspace_iff (h : GraphicallySmoothAt F p) {w : E × E} :
    w ∈ tangentSubspace F p ↔ w ∈ contingentCone (graph F) p := by
  rw [← SetLike.mem_coe, h.coe_tangentSubspace]

omit [FiniteDimensional ℝ E] in
/-- At a point of graphical smoothness, the tangent subspace has dimension `n = dim E`. -/
theorem GraphicallySmoothAt.finrank_tangentSubspace (h : GraphicallySmoothAt F p) :
    finrank ℝ (tangentSubspace F p) = finrank ℝ E := by
  obtain ⟨-, L, hdim, hL⟩ := h
  rw [tangentSubspace, ← hL, Submodule.span_eq, hdim]

/-- The functional `(u, v) ↦ ⟪x*, u⟫ - ⟪y*, v⟫` on `E × E` attached to `(y*, x*)`; this is how
an element of an adjoint subspace is read as a normal to a graph. -/
noncomputable def graphFunctional (y x : E) : StrongDual ℝ (E × E) :=
  (toDual ℝ E x).coprod (-(toDual ℝ E y))

/-- `graphFunctional y x` is the functional `w ↦ ⟪x, w.1⟫ - ⟪y, w.2⟫`. -/
@[simp] theorem graphFunctional_apply (y x : E) (w : E × E) :
    graphFunctional y x w = ⟪x, w.1⟫_ℝ - ⟪y, w.2⟫_ℝ := by
  simp [graphFunctional, ContinuousLinearMap.coprod_apply, toDual_apply_apply, sub_eq_add_neg]

/-- `graphFunctional` is sequentially continuous: if `yₖ → y₀` and `xₖ → x₀`, then
`graphFunctional yₖ xₖ → graphFunctional y₀ x₀` in `StrongDual ℝ (E × E)`. -/
theorem tendsto_graphFunctional {y x : ℕ → E} {y₀ x₀ : E} (hy : Tendsto y atTop (𝓝 y₀))
    (hx : Tendsto x atTop (𝓝 x₀)) :
    Tendsto (fun k ↦ graphFunctional (y k) (x k)) atTop (𝓝 (graphFunctional y₀ x₀)) :=
  tendsto_coprod (((toDual ℝ E).continuous.tendsto x₀).comp hx)
    (((toDual ℝ E).continuous.tendsto y₀).comp hy).neg

/-- Remark 3.4 of [Gfrerer–Outrata 2022]: at a point of graphical smoothness, the regular normals
to `gph F` are exactly the elements of the adjoint tangent subspace `T_{gph F}(p)*`. -/
theorem GraphicallySmoothAt.mem_adjoint_tangentSubspace_iff (h : GraphicallySmoothAt F p)
    {y x : E} : graphFunctional y x ∈ regularNormalCone (graph F) p ↔
      (y, x) ∈ adjointSubspace (tangentSubspace F p) := by
  rw [regularNormalCone_eq_polar_contingentCone h.1, ← h.coe_tangentSubspace,
    mk_mem_adjointSubspace_iff]
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, graphFunctional_apply]
  constructor
  · intro H u v huv
    have h1 := H (u, v) huv
    have h2 := H (-(u, v)) (neg_mem huv)
    simp only [Prod.fst_neg, Prod.snd_neg, inner_neg_right] at h1 h2
    linarith
  · intro H w hw
    have := H w.1 w.2 hw
    linarith

/-- Remark 3.4 of [Gfrerer–Outrata 2022] in coderivative form:
`gph D̂*F(p) = T_{gph F}(p)*` on `O_F`. -/
theorem GraphicallySmoothAt.mem_regularCoderiv_iff (h : GraphicallySmoothAt F p) {y x : E} :
    toDual ℝ E x ∈ regularCoderiv F p.1 p.2 (toDual ℝ E y) ↔
      (y, x) ∈ adjointSubspace (tangentSubspace F p) :=
  h.mem_adjoint_tangentSubspace_iff

/-! ### SC derivatives -/

/-- The SC derivative `𝒮F(p)`: all limits `L = lim T_{gph F}(pₖ)` in the Grassmannian metric
along sequences `O_F ∋ pₖ → p` [Gfrerer–Outrata 2022, Def. 3.3]. -/
def scDeriv (F : E → Set E) (p : E × E) : Set (Submodule ℝ (E × E)) :=
  {L | ∃ q : ℕ → E × E, (∀ k, GraphicallySmoothAt F (q k)) ∧ Tendsto q atTop (𝓝 p) ∧
    GrassTendsto (fun k ↦ tangentSubspace F (q k)) L}

/-- The SC adjoint derivative `𝒮*F(p) = {L* | L ∈ 𝒮F(p)}` [Gfrerer–Outrata 2022,
Remark 3.5]. -/
def scCoderiv (F : E → Set E) (p : E × E) : Set (Submodule ℝ (E × E)) :=
  adjointSubspace '' scDeriv F p

/-- `F` has the SCD property at `p` if `𝒮F(p) ≠ ∅` [Gfrerer–Outrata 2022, Def. 3.3]. -/
def HasSCDPropertyAt (F : E → Set E) (p : E × E) : Prop := (scDeriv F p).Nonempty

/-- `F` has the SCD property around `p` if it has it at every point of `gph F` near `p`
[Gfrerer–Outrata 2022, Def. 3.3]. -/
def HasSCDPropertyAround (F : E → Set E) (p : E × E) : Prop :=
  ∃ U ∈ 𝓝 p, ∀ q ∈ graph F ∩ U, HasSCDPropertyAt F q

/-- `F` is an SCD mapping if it has the SCD property at every point of its graph
[Gfrerer–Outrata 2022, Def. 3.3]. -/
def IsSCDMapping (F : E → Set E) : Prop := ∀ p ∈ graph F, HasSCDPropertyAt F p

/-- An SCD mapping has the SCD property around every point `p`. -/
theorem IsSCDMapping.hasSCDPropertyAround (hF : IsSCDMapping F) (p : E × E) :
    HasSCDPropertyAround F p :=
  ⟨univ, univ_mem, fun q hq ↦ hF q hq.1⟩

/-- `F` has the SCD property at `p` iff `𝒮*F(p) ≠ ∅`. -/
theorem hasSCDPropertyAt_iff_scCoderiv_nonempty :
    HasSCDPropertyAt F p ↔ (scCoderiv F p).Nonempty :=
  image_nonempty.symm

/-- Every subspace `L ∈ 𝒮F(p)` has dimension `n = dim E`. -/
theorem finrank_of_mem_scDeriv {L : Submodule ℝ (E × E)} (hL : L ∈ scDeriv F p) :
    finrank ℝ L = finrank ℝ E := by
  obtain ⟨q, hq, -, hT⟩ := hL
  exact hT.finrank_eq fun k ↦ (hq k).finrank_tangentSubspace

/-- Every subspace `L ∈ 𝒮*F(p)` has dimension `n = dim E`. -/
theorem finrank_of_mem_scCoderiv {L : Submodule ℝ (E × E)} (hL : L ∈ scCoderiv F p) :
    finrank ℝ L = finrank ℝ E := by
  obtain ⟨L', hL', rfl⟩ := hL
  exact finrank_adjointSubspace_of_eq (finrank_of_mem_scDeriv hL')

/-- `L ∈ 𝒮*F(p)` iff `L* ∈ 𝒮F(p)`. -/
theorem mem_scCoderiv_iff_adjoint_mem_scDeriv {L : Submodule ℝ (E × E)} :
    L ∈ scCoderiv F p ↔ adjointSubspace L ∈ scDeriv F p := by
  constructor
  · rintro ⟨L', hL', rfl⟩
    rwa [adjointSubspace_adjointSubspace]
  · exact fun h ↦ ⟨_, h, adjointSubspace_adjointSubspace L⟩

/-- At a point of graphical smoothness the tangent subspace belongs to `𝒮F(p)`. -/
theorem GraphicallySmoothAt.tangentSubspace_mem_scDeriv (h : GraphicallySmoothAt F p) :
    tangentSubspace F p ∈ scDeriv F p :=
  ⟨fun _ ↦ p, fun _ ↦ h, tendsto_const_nhds, grassTendsto_const _⟩

/-- `F` has the SCD property at every point of graphical smoothness. -/
theorem GraphicallySmoothAt.hasSCDPropertyAt (h : GraphicallySmoothAt F p) :
    HasSCDPropertyAt F p :=
  ⟨_, h.tangentSubspace_mem_scDeriv⟩

/-- Remark 3.5 of [Gfrerer–Outrata 2022]: `𝒮*F(p)` is the set of limits of the adjoint tangent
subspaces `T_{gph F}(pₖ)*` along `O_F ∋ pₖ → p`. -/
theorem mem_scCoderiv_iff {L : Submodule ℝ (E × E)} :
    L ∈ scCoderiv F p ↔ ∃ q : ℕ → E × E, (∀ k, GraphicallySmoothAt F (q k)) ∧
      Tendsto q atTop (𝓝 p) ∧
      GrassTendsto (fun k ↦ adjointSubspace (tangentSubspace F (q k))) L := by
  constructor
  · rintro ⟨L', ⟨q, hq, hqlim, hT⟩, rfl⟩
    exact ⟨q, hq, hqlim, hT.adjointSubspace (fun k ↦ (hq k).finrank_tangentSubspace)
      (hT.finrank_eq fun k ↦ (hq k).finrank_tangentSubspace)⟩
  · rintro ⟨q, hq, hqlim, hT⟩
    have hdim : ∀ k, finrank ℝ (adjointSubspace (tangentSubspace F (q k))) = finrank ℝ E :=
      fun k ↦ finrank_adjointSubspace_of_eq (hq k).finrank_tangentSubspace
    have h2 := hT.adjointSubspace hdim (hT.finrank_eq hdim)
    simp only [adjointSubspace_adjointSubspace] at h2
    exact mem_scCoderiv_iff_adjoint_mem_scDeriv.2 ⟨q, hq, hqlim, h2⟩

/-- Lemma 3.6 of [Gfrerer–Outrata 2022]: `F` has the SCD property at `p` iff `p ∈ cl O_F`. -/
theorem hasSCDPropertyAt_iff_mem_closure :
    HasSCDPropertyAt F p ↔ p ∈ closure {q | GraphicallySmoothAt F q} := by
  constructor
  · rintro ⟨L, q, hq, hqlim, -⟩
    exact mem_closure_of_tendsto hqlim (Eventually.of_forall hq)
  · intro hp
    obtain ⟨q, hq, hqlim⟩ := mem_closure_iff_seq_limit.1 hp
    obtain ⟨L₀, -, φ, hφ, hL₀⟩ := exists_grassTendsto_subseq (fun k ↦ tangentSubspace F (q k))
      (n := finrank ℝ E) fun k ↦ (hq k).finrank_tangentSubspace
    exact ⟨L₀, q ∘ φ, fun k ↦ hq (φ k), hqlim.comp hφ.tendsto_atTop, hL₀⟩

/-- Lemma 3.7 of [Gfrerer–Outrata 2022]: `⋃ 𝒮*F(p) ⊆ gph D*F(p)`: if `(y*, x*) ∈ L ∈ 𝒮*F(p)`,
then `x* ∈ D*F(p)(y*)`. -/
theorem toDual_mem_coderiv_of_mem_scCoderiv (hp : p ∈ graph F) {L : Submodule ℝ (E × E)}
    (hL : L ∈ scCoderiv F p) {y x : E} (hyx : (y, x) ∈ L) :
    toDual ℝ E x ∈ coderiv F p.1 p.2 (toDual ℝ E y) := by
  obtain ⟨q, hq, hqlim, hT⟩ := mem_scCoderiv_iff.1 hL
  obtain ⟨w, hw, hwlim⟩ := hT.exists_tendsto hyx
  refine ⟨hp, q, fun k ↦ graphFunctional (w k).1 (w k).2,
    tendsto_nhdsWithin_iff.2 ⟨hqlim, Eventually.of_forall fun k ↦ (hq k).1⟩,
    tendsto_graphFunctional ((continuous_fst.tendsto _).comp hwlim)
      ((continuous_snd.tendsto _).comp hwlim), fun k ↦ ?_⟩
  exact (hq k).mem_adjoint_tangentSubspace_iff.2 (hw k)

/-- Lemma 3.10 of [Gfrerer–Outrata 2022]: `⋃ 𝒮F(p) ⊆ gph D♯F(p)`. -/
theorem mem_sharpTangentCone_of_mem_scDeriv {L : Submodule ℝ (E × E)} (hL : L ∈ scDeriv F p)
    {w : E × E} (hw : w ∈ L) : w ∈ sharpTangentCone (graph F) p := by
  obtain ⟨q, hq, hqlim, hT⟩ := hL
  obtain ⟨v, hv, hvlim⟩ := hT.exists_tendsto hw
  exact ⟨q, v, tendsto_nhdsWithin_iff.2 ⟨hqlim, Eventually.of_forall fun k ↦ (hq k).1⟩, hvlim,
    fun k ↦ (hq k).mem_tangentSubspace_iff.1 (hv k)⟩

/-- Lemma 3.10 of [Gfrerer–Outrata 2022] in derivative form: if `(u, v) ∈ L ∈ 𝒮F(p)`, then
`v ∈ D♯F(p)(u)`. -/
theorem mem_sharpDeriv_of_mem_scDeriv {L : Submodule ℝ (E × E)} (hL : L ∈ scDeriv F p)
    {u v : E} (huv : (u, v) ∈ L) : v ∈ sharpDeriv F p.1 p.2 u :=
  mem_sharpTangentCone_of_mem_scDeriv hL huv

/-- Approximation of an element of `𝒮F(p)` by tangent subspaces at nearby smooth points. -/
theorem exists_graphicallySmoothAt_of_mem_scDeriv {L : Submodule ℝ (E × E)}
    (hL : L ∈ scDeriv F p) {ε : ℝ} (hε : 0 < ε) :
    ∃ r, GraphicallySmoothAt F r ∧ dist r p < ε ∧ grassDist (tangentSubspace F r) L < ε := by
  obtain ⟨q, hq, hqlim, hT⟩ := hL
  have h1 : ∀ᶠ k in atTop, dist (q k) p < ε := hqlim.eventually (Metric.ball_mem_nhds p hε)
  have h2 : ∀ᶠ k in atTop, grassDist (tangentSubspace F (q k)) L < ε :=
    (grassTendsto_iff.1 hT).eventually (gt_mem_nhds hε)
  obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
  exact ⟨q k, hq k, hk1, hk2⟩

/-- Lemma 3.13 of [Gfrerer–Outrata 2022] (robustness of `𝒮F`): if `qₖ → p`, `Lₖ ∈ 𝒮F(qₖ)` and
`Lₖ → L`, then `L ∈ 𝒮F(p)`. -/
theorem mem_scDeriv_of_tendsto {q : ℕ → E × E} {L : ℕ → Submodule ℝ (E × E)}
    {L₀ : Submodule ℝ (E × E)} (hq : Tendsto q atTop (𝓝 p)) (hL : ∀ k, L k ∈ scDeriv F (q k))
    (hlim : GrassTendsto L L₀) : L₀ ∈ scDeriv F p := by
  have key : ∀ k : ℕ, ∃ r, GraphicallySmoothAt F r ∧ dist r (q k) < 1 / ((k : ℝ) + 1) ∧
      grassDist (tangentSubspace F r) (L k) < 1 / ((k : ℝ) + 1) := fun k ↦
    exists_graphicallySmoothAt_of_mem_scDeriv (hL k) Nat.one_div_pos_of_nat
  choose r hr hrd hrg using key
  have hδ : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨r, hr, ?_, ?_⟩
  · refine hq.congr_dist ?_
    refine squeeze_zero (fun k ↦ dist_nonneg) (fun k ↦ ?_) hδ
    rw [dist_comm]; exact (hrd k).le
  · exact hlim.of_grassDist_tendsto
      (squeeze_zero (fun k ↦ grassDist_nonneg _ _) (fun k ↦ (hrg k).le) hδ)

/-- Lemma 3.13 of [Gfrerer–Outrata 2022]: `𝒮F(p) = Lim sup_{q → p} 𝒮F(q)`, i.e. `L ∈ 𝒮F(p)` iff
there are `qₖ → p` and `Lₖ ∈ 𝒮F(qₖ)` with `Lₖ → L`. -/
theorem mem_scDeriv_iff_exists_seq {L₀ : Submodule ℝ (E × E)} :
    L₀ ∈ scDeriv F p ↔ ∃ q : ℕ → E × E, ∃ L : ℕ → Submodule ℝ (E × E),
      Tendsto q atTop (𝓝 p) ∧ (∀ k, L k ∈ scDeriv F (q k)) ∧ GrassTendsto L L₀ := by
  constructor
  · rintro ⟨q, hq, hqlim, hT⟩
    exact ⟨q, _, hqlim, fun k ↦ (hq k).tangentSubspace_mem_scDeriv, hT⟩
  · rintro ⟨q, L, hq, hL, hlim⟩
    exact mem_scDeriv_of_tendsto hq hL hlim

/-- The SCD property is closed: if `F` has the SCD property at points `qₖ → p`, then also at
`p` (Lemma 3.13 together with the compactness of the Grassmannian). -/
theorem hasSCDPropertyAt_of_tendsto {q : ℕ → E × E} (hq : Tendsto q atTop (𝓝 p))
    (h : ∀ k, HasSCDPropertyAt F (q k)) : HasSCDPropertyAt F p := by
  choose L hL using h
  obtain ⟨L₀, -, φ, hφ, hL₀⟩ := exists_grassTendsto_subseq L (n := finrank ℝ E)
    fun k ↦ finrank_of_mem_scDeriv (hL k)
  exact ⟨L₀, mem_scDeriv_of_tendsto (hq.comp hφ.tendsto_atTop) (fun k ↦ hL (φ k)) hL₀⟩

/-- Lemma 3.13 for `𝒮*F`: if `qₖ → p`, `Lₖ ∈ 𝒮*F(qₖ)` and `Lₖ → L`, then `L ∈ 𝒮*F(p)`. -/
theorem mem_scCoderiv_of_tendsto {q : ℕ → E × E} {L : ℕ → Submodule ℝ (E × E)}
    {L₀ : Submodule ℝ (E × E)} (hq : Tendsto q atTop (𝓝 p)) (hL : ∀ k, L k ∈ scCoderiv F (q k))
    (hlim : GrassTendsto L L₀) : L₀ ∈ scCoderiv F p := by
  have hdim : ∀ k, finrank ℝ (L k) = finrank ℝ E := fun k ↦ finrank_of_mem_scCoderiv (hL k)
  exact mem_scCoderiv_iff_adjoint_mem_scDeriv.2 (mem_scDeriv_of_tendsto hq
    (fun k ↦ mem_scCoderiv_iff_adjoint_mem_scDeriv.1 (hL k))
    (hlim.adjointSubspace hdim (hlim.finrank_eq hdim)))

end VariationalAnalysis
