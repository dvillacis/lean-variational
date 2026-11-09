/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import VariationalAnalysis.SCD.Grassmannian

/-!
# Adjoint subspaces

For a subspace `L` of `E × E`, [Gfrerer–Outrata 2022, (15)] define the adjoint subspace
`L* = {(-v*, u*) | (u*, v*) ∈ L^⊥}`, so that `(y*, x*) ∈ L*` iff `⟪x*, u⟫ = ⟪y*, v⟫` for all
`(u, v) ∈ L`. When `L = gph DF(x, y)` is the graph of the graphical derivative, `L*` is the graph
of the regular coderivative (Remark 3.4 there). We define `L*` as the orthogonal of `L` with
respect to the alternating bilinear form `ω((u, v), (y*, x*)) = ⟪v, y*⟫ - ⟪u, x*⟫` on `E × E`,
which needs no inner product on the product space.

## Main results

* `mem_adjointSubspace_iff`: `(y*, x*) ∈ L*` iff `⟪x*, u⟫ = ⟪y*, v⟫` for all `(u, v) ∈ L`.
* `finrank_adjointSubspace`: `dim L* = 2n - dim L`; `adjointSubspace_adjointSubspace`:
  `(L*)* = L`.
* `GrassTendsto.adjointSubspace`: `L ↦ L*` is continuous in the Grassmannian metric
  (it is in fact an isometry [Gfrerer–Outrata 2022, p. 10]).
* `adjointSubspace_graph`: `(gph A)* = gph A†` for a linear map `A`.
-/

open Filter Topology Set Module
open scoped InnerProductSpace

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Pairing

/-- The alternating pairing `ω((u, v), (y*, x*)) = ⟪v, y*⟫ - ⟪u, x*⟫` on `E × E`. -/
noncomputable def graphPairing : LinearMap.BilinForm ℝ (E × E) :=
  LinearMap.BilinForm.comp (innerₗ E) (LinearMap.snd ℝ E E) (LinearMap.fst ℝ E E) -
    LinearMap.BilinForm.comp (innerₗ E) (LinearMap.fst ℝ E E) (LinearMap.snd ℝ E E)

@[simp] theorem graphPairing_apply (p q : E × E) :
    graphPairing p q = ⟪p.2, q.1⟫_ℝ - ⟪p.1, q.2⟫_ℝ := by
  simp [graphPairing, LinearMap.BilinForm.comp_apply]

theorem graphPairing_isAlt : LinearMap.IsAlt (graphPairing (E := E)) := fun p ↦ by
  simp [real_inner_comm]

theorem graphPairing_isRefl : LinearMap.IsRefl (graphPairing (E := E)) :=
  graphPairing_isAlt.isRefl

theorem graphPairing_isRefl' : LinearMap.BilinForm.IsRefl (graphPairing (E := E)) :=
  graphPairing_isRefl

theorem graphPairing_separatingLeft : LinearMap.SeparatingLeft (graphPairing (E := E)) := by
  intro p hp
  have := hp (-p.2, p.1)
  simp only [graphPairing_apply, inner_neg_right, real_inner_self_eq_norm_sq] at this
  have h1 : ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 = 0 := by linarith
  obtain ⟨h2, h3⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).1 h1
  exact Prod.ext (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2))
    (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h3))

theorem graphPairing_nondegenerate : LinearMap.BilinForm.Nondegenerate (graphPairing (E := E)) :=
  (LinearMap.IsRefl.nondegenerate_iff_separatingLeft graphPairing_isRefl).2
    graphPairing_separatingLeft

/-- The pairing is jointly continuous. -/
theorem tendsto_graphPairing {α : Type*} {l : Filter α} {p q : α → E × E} {p₀ q₀ : E × E}
    (hp : Tendsto p l (𝓝 p₀)) (hq : Tendsto q l (𝓝 q₀)) :
    Tendsto (fun k ↦ graphPairing (p k) (q k)) l (𝓝 (graphPairing p₀ q₀)) := by
  simp only [graphPairing_apply]
  exact (((continuous_snd.tendsto _).comp hp).inner ((continuous_fst.tendsto _).comp hq)).sub
    (((continuous_fst.tendsto _).comp hp).inner ((continuous_snd.tendsto _).comp hq))

end Pairing

/-- The adjoint subspace `L* = {(y*, x*) | ⟪x*, u⟫ = ⟪y*, v⟫ ∀ (u, v) ∈ L}`
[Gfrerer–Outrata 2022, (15)]. -/
noncomputable def adjointSubspace (L : Submodule ℝ (E × E)) : Submodule ℝ (E × E) :=
  graphPairing.orthogonal L

variable {L : Submodule ℝ (E × E)}

theorem mem_adjointSubspace_iff {p : E × E} :
    p ∈ adjointSubspace L ↔ ∀ q ∈ L, ⟪p.2, q.1⟫_ℝ = ⟪p.1, q.2⟫_ℝ := by
  simp only [adjointSubspace, LinearMap.BilinForm.mem_orthogonal_iff, graphPairing_apply,
    sub_eq_zero]
  refine forall₂_congr fun q _ ↦ ?_
  rw [real_inner_comm p.1 q.2, real_inner_comm p.2 q.1]
  exact eq_comm

theorem mk_mem_adjointSubspace_iff {y x : E} :
    (y, x) ∈ adjointSubspace L ↔ ∀ u v, (u, v) ∈ L → ⟪x, u⟫_ℝ = ⟪y, v⟫_ℝ := by
  rw [mem_adjointSubspace_iff]
  exact ⟨fun h u v huv ↦ h (u, v) huv, fun h q hq ↦ h q.1 q.2 hq⟩

theorem inner_eq_of_mem_adjointSubspace {p q : E × E} (hp : p ∈ adjointSubspace L) (hq : q ∈ L) :
    ⟪p.2, q.1⟫_ℝ = ⟪p.1, q.2⟫_ℝ :=
  mem_adjointSubspace_iff.1 hp q hq

variable [FiniteDimensional ℝ E]

theorem adjointSubspace_adjointSubspace (L : Submodule ℝ (E × E)) :
    adjointSubspace (adjointSubspace L) = L := by
  show graphPairing.orthogonal (graphPairing.orthogonal L) = L
  exact LinearMap.BilinForm.orthogonal_orthogonal graphPairing_nondegenerate
    graphPairing_isRefl' L

theorem adjointSubspace_injective : Function.Injective (adjointSubspace (E := E)) :=
  fun L₁ L₂ h ↦ by
    rw [← adjointSubspace_adjointSubspace L₁, h, adjointSubspace_adjointSubspace]

theorem finrank_adjointSubspace (L : Submodule ℝ (E × E)) :
    finrank ℝ (adjointSubspace L) = 2 * finrank ℝ E - finrank ℝ L := by
  rw [adjointSubspace, LinearMap.BilinForm.finrank_orthogonal graphPairing_nondegenerate,
    Module.finrank_prod, two_mul]

/-- For a subspace of dimension `n = dim E`, the adjoint subspace has dimension `n` as well. -/
theorem finrank_adjointSubspace_of_eq (h : finrank ℝ L = finrank ℝ E) :
    finrank ℝ (adjointSubspace L) = finrank ℝ E := by
  rw [finrank_adjointSubspace, h]; omega

omit [FiniteDimensional ℝ E] in
theorem adjointSubspace_anti {L₁ L₂ : Submodule ℝ (E × E)} (h : L₁ ≤ L₂) :
    adjointSubspace L₂ ≤ adjointSubspace L₁ := fun _ hp ↦
  mem_adjointSubspace_iff.2 fun _ hq ↦ inner_eq_of_mem_adjointSubspace hp (h hq)

/-- `L ↦ L*` is continuous in the Grassmannian metric: if `Lₖ → L₀` and all these subspaces
have the same dimension, then `Lₖ* → L₀*` [Gfrerer–Outrata 2022, p. 10]. -/
theorem GrassTendsto.adjointSubspace {L : ℕ → Submodule ℝ (E × E)} {L₀ : Submodule ℝ (E × E)}
    {n : ℕ} (hn : ∀ k, finrank ℝ (L k) = n) (hn₀ : finrank ℝ L₀ = n) (h : GrassTendsto L L₀) :
    GrassTendsto (fun k ↦ adjointSubspace (L k)) (adjointSubspace L₀) := by
  refine grassTendsto_of_outerLimit_subset (n := 2 * finrank ℝ E - n)
    (fun k ↦ by rw [finrank_adjointSubspace, hn]) (by rw [finrank_adjointSubspace, hn₀]) ?_
  rintro p ⟨a, w, ha, hw, hmem⟩
  refine mem_adjointSubspace_iff.2 fun q hq ↦ ?_
  obtain ⟨v, hv, hvlim⟩ := (h.comp ha).exists_tendsto hq
  have h1 : Tendsto (fun k ↦ graphPairing (v k) (w k)) atTop (𝓝 (graphPairing q p)) :=
    tendsto_graphPairing hvlim hw
  have h2 : ∀ k, graphPairing (v k) (w k) = 0 := fun k ↦
    LinearMap.BilinForm.mem_orthogonal_iff.1 (hmem k) _ (hv k)
  have := tendsto_nhds_unique h1 (by simp [h2] : Tendsto
    (fun k ↦ graphPairing (v k) (w k)) atTop (𝓝 0))
  simp only [graphPairing_apply, sub_eq_zero] at this
  rw [real_inner_comm p.1 q.2, real_inner_comm p.2 q.1] at this
  exact this.symm

section Graph

variable (A : E →L[ℝ] E)

omit [FiniteDimensional ℝ E] in
/-- The graph `{(u, A u)}` of a linear map has dimension `dim E`. -/
theorem finrank_graph (A : E →ₗ[ℝ] E) : finrank ℝ A.graph = finrank ℝ E := by
  rw [LinearMap.graph_eq_range_prod]
  exact LinearMap.finrank_range_of_inj fun x y hxy ↦ by
    simpa using congrArg Prod.fst hxy

/-- `(gph A)* = gph A†`: `(y*, x*) ∈ (gph A)*` iff `x* = A† y*`
[Gfrerer–Outrata 2022, proof of Lemma 3.11]. -/
theorem adjointSubspace_graph :
    adjointSubspace (A : E →ₗ[ℝ] E).graph = (ContinuousLinearMap.adjoint A : E →ₗ[ℝ] E).graph := by
  ext ⟨y, x⟩
  rw [mk_mem_adjointSubspace_iff, LinearMap.mem_graph_iff]
  simp only [ContinuousLinearMap.coe_coe, LinearMap.mem_graph_iff]
  constructor
  · intro h
    refine ext_inner_right ℝ fun u ↦ ?_
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact h u (A u) rfl
  · rintro rfl u v rfl
    rw [ContinuousLinearMap.adjoint_inner_left]

end Graph

end VariationalAnalysis
