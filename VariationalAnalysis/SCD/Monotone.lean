/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import VariationalAnalysis.SCD.SingleValued
import VariationalAnalysis.SCD.Calculus
import VariationalAnalysis.WellPosedness.MaximalMonotone

/-!
# Monotone mappings and convex subdifferentials are SCD mappings

Following [Gfrerer–Outrata 2022, Prop. 3.22–Cor. 3.28], we show that monotone mappings
`F : E ⇉ E` with `rge(I + F) = E` and subdifferentials of proper l.s.c. convex functions are
SCD mappings, and describe their SC derivatives. The tool is the Minty parametrization: the linear
isomorphism `Φ(x, y) = (x + y, x)` maps `gph F` onto the graph of the resolvent `(I + F)⁻¹`, which
for monotone `F` with `rge(I + F) = E` is single-valued and firmly nonexpansive, hence Lipschitz.
Lemma 3.11 (`mem_scDeriv_iff_of_lipschitzOnWith`) and the linear case of Prop. 3.14
(`scDeriv_image_linear`) then give `𝒮F(x, y) = {rge(B, I - B) | B ∈ ∇̄(I + F)⁻¹(x + y)}`.

For a convex function `φ`, `rge(I + ∂φ) = E` is proved directly (the proximal point minimizes
`φ + ½‖· - u‖²`), and the symmetry of the matrices `B` comes from the fact that the proximal
mapping is the gradient of `½‖·‖² - e φ`, with `e φ` the Moreau envelope, so its derivatives are
Hessians (`second_derivative_symmetric_of_eventually_of_real`).

Maximal monotonicity enters only through `rge(I + F) = E`: for monotone `F` this implies maximal
monotonicity (`IsMonotoneOp.isMaximalMonotoneOp`), and the converse is Minty's theorem
(`SCD/Minty`). The local notions of [Gfrerer–Outrata 2022, Def. 3.20] and Prop. 3.22, Cor. 3.23,
Cor. 3.24 for them are in `SCD/LocalMonotone`.

## Main declarations

* `mintyMap`: `Φ(x, y) = (x + y, x)`; `mintySubspace B = rge(B, I - B)`,
  `hypoMintySubspace c B = rge(B, I - c B)`.
* `IsFirmlyNonexpansive`, `IsFirmlyNonexpansiveOp` [Gfrerer–Outrata 2022, Def. 3.21].
* `IsMonotoneOp`, `IsMaximalMonotoneOp` [Gfrerer–Outrata 2022, p. 15]; `resolvent F = (I + F)⁻¹`.
* `subdiffMap φ`: `∂φ : E ⇉ E` through the Riesz map; `moreauEnv φ`: the Moreau envelope.

## Main results

* `IsMonotoneOp.isSCDMapping`, `IsMonotoneOp.mem_scDeriv_iff`, `IsMonotoneOp.mem_scCoderiv_iff`,
  `IsMonotoneOp.exists_firm_of_mem_scDeriv`: [Gfrerer–Outrata 2022, Prop. 3.22] for monotone `F`
  with `rge(I + F) = E`: `F` is an SCD mapping, `𝒮F(x, y) = {rge(B, I - B)}` and
  `𝒮*F(x, y) = {rge(Bᵀ, I - Bᵀ)}` over `B ∈ ∇̄(I + F)⁻¹(x + y)`, all firmly nonexpansive.
* `exists_sub_mem_subdiffMap`: `rge(I + ∂φ) = E` for proper l.s.c. convex `φ`.
* `isSCDMapping_subdiffMap`, `exists_symm_of_mem_scDeriv_subdiffMap`,
  `adjointSubspace_eq_of_mem_scDeriv_subdiffMap`, `scCoderiv_subdiffMap`:
  [Gfrerer–Outrata 2022, Cor. 3.28] (= [Gfrerer–Outrata 2022b, Thm. 3.6], the paper on
  variational inequalities of the second kind): `∂φ` is an SCD mapping, `𝒮*∂φ = 𝒮∂φ`, and every
  `L ∈ 𝒮∂φ(x, x*)` is `rge(B, I - B) = L*` with `B` symmetric positive semidefinite, `‖B‖ ≤ 1`.
* `hasFDerivAt_moreauEnv`: `∇ e φ(u) = u - prox u`.
* `scDeriv_eq_of_inter_eq`: `𝒮F(p)` only depends on `gph F` near `p`.
-/

open Filter Topology Set Module InnerProductSpace
open scoped InnerProductSpace NNReal

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### The Minty parametrization -/

section Linear

/-- `(x, y) ↦ (x + y, x)`. -/
noncomputable def mintyCLM : (E × E) →L[ℝ] (E × E) :=
  (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E).prod
    (ContinuousLinearMap.fst ℝ E E)

/-- `(u, x) ↦ (x, u - x)`. -/
noncomputable def mintyInvCLM : (E × E) →L[ℝ] (E × E) :=
  (ContinuousLinearMap.snd ℝ E E).prod
    (ContinuousLinearMap.fst ℝ E E - ContinuousLinearMap.snd ℝ E E)

omit [FiniteDimensional ℝ E] in
@[simp] theorem mintyCLM_apply (w : E × E) : mintyCLM w = (w.1 + w.2, w.1) := rfl

omit [FiniteDimensional ℝ E] in
@[simp] theorem mintyInvCLM_apply (w : E × E) : mintyInvCLM w = (w.2, w.1 - w.2) := rfl

/-- The transformation mapping `Φ(x, y) = (x + y, x)` of [Gfrerer–Outrata 2022, Prop. 3.22]:
it maps `gph F` onto the graph of the resolvent `(I + F)⁻¹`. -/
noncomputable def mintyMap : (E × E) ≃L[ℝ] (E × E) :=
  ContinuousLinearEquiv.equivOfInverse mintyCLM mintyInvCLM (fun w ↦ by simp)
    (fun w ↦ by simp)

omit [FiniteDimensional ℝ E] in
@[simp] theorem mintyMap_apply (w : E × E) : mintyMap w = (w.1 + w.2, w.1) := rfl

omit [FiniteDimensional ℝ E] in
@[simp] theorem mintyMap_symm_apply (w : E × E) : mintyMap.symm w = (w.2, w.1 - w.2) := rfl

/-- The subspace `rge(B, I - B) = {(B v, v - B v) | v ∈ E}`. -/
noncomputable def mintySubspace (B : E →L[ℝ] E) : Submodule ℝ (E × E) :=
  LinearMap.range ((B : E →ₗ[ℝ] E).prod (LinearMap.id - (B : E →ₗ[ℝ] E)))

omit [FiniteDimensional ℝ E] in
theorem mem_mintySubspace_iff {B : E →L[ℝ] E} {w : E × E} :
    w ∈ mintySubspace B ↔ ∃ v, B v = w.1 ∧ v - B v = w.2 := by
  rw [mintySubspace, LinearMap.mem_range]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v, rfl, rfl⟩
  · rintro ⟨v, h1, h2⟩
    exact ⟨v, Prod.ext h1 h2⟩

omit [FiniteDimensional ℝ E] in
/-- `Φ⁻¹ rge(I, B) = rge(B, I - B)` for `Φ(x, y) = (x + y, x)`. -/
theorem map_graph_mintyMap_symm (B : E →L[ℝ] E) :
    (B : E →ₗ[ℝ] E).graph.map
        (((mintyMap (E := E)).symm : (E × E) →L[ℝ] (E × E)) : (E × E) →ₗ[ℝ] (E × E)) =
      mintySubspace B := by
  ext w
  rw [Submodule.mem_map, mem_mintySubspace_iff]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [LinearMap.mem_graph_iff] at hq
    refine ⟨q.1, ?_, ?_⟩
    · change B q.1 = q.2
      exact hq.symm
    · change q.1 - B q.1 = q.1 - q.2
      rw [← ContinuousLinearMap.coe_coe, ← hq]
  · rintro ⟨v, h1, h2⟩
    refine ⟨(v, B v), (LinearMap.mem_graph_iff _ _).2 rfl, ?_⟩
    change (B v, v - B v) = w
    exact Prod.ext h1 h2

omit [FiniteDimensional ℝ E] in
/-- `rge(B, I - B)* = rge(Bᵀ, I - Bᵀ)` [Gfrerer–Outrata 2022, Prop. 3.22]. -/
theorem adjointSubspace_mintySubspace [CompleteSpace E] (B : E →L[ℝ] E) :
    adjointSubspace (mintySubspace B) = mintySubspace (ContinuousLinearMap.adjoint B) := by
  ext ⟨y, x⟩
  rw [mk_mem_adjointSubspace_iff, mem_mintySubspace_iff]
  constructor
  · intro h
    have h1 : ContinuousLinearMap.adjoint B (x + y) = y := by
      refine ext_inner_right ℝ fun w ↦ ?_
      rw [ContinuousLinearMap.adjoint_inner_left, inner_add_left,
        h (B w) (w - B w) (mem_mintySubspace_iff.2 ⟨w, rfl, rfl⟩), inner_sub_right]
      ring
    exact ⟨x + y, h1, by rw [h1]; abel⟩
  · rintro ⟨z, hz1, hz2⟩ u v huv
    obtain ⟨w, hw1, hw2⟩ := mem_mintySubspace_iff.1 huv
    simp only at hz1 hz2 hw1 hw2
    subst hz1 hz2 hw1 hw2
    rw [inner_sub_left, inner_sub_right, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_left]

end Linear

/-! ### Firmly nonexpansive mappings -/

section Firm

/-- A linear map `B` is firmly nonexpansive if `‖B v‖² ≤ ⟪B v, v⟫` for all `v`
[Gfrerer–Outrata 2022, Def. 3.21(2)]. -/
def IsFirmlyNonexpansiveOp (B : E →L[ℝ] E) : Prop := ∀ v, ‖B v‖ ^ 2 ≤ ⟪B v, v⟫_ℝ

/-- `f` is firmly nonexpansive if `‖f u₁ - f u₂‖² ≤ ⟪f u₁ - f u₂, u₁ - u₂⟫`
[Gfrerer–Outrata 2022, Def. 3.21(1)]. -/
def IsFirmlyNonexpansive (f : E → E) : Prop :=
  ∀ u₁ u₂, ‖f u₁ - f u₂‖ ^ 2 ≤ ⟪f u₁ - f u₂, u₁ - u₂⟫_ℝ

omit [FiniteDimensional ℝ E] in
theorem norm_le_of_sq_le_inner {a b : E} (h : ‖a‖ ^ 2 ≤ ⟪a, b⟫_ℝ) : ‖a‖ ≤ ‖b‖ := by
  have h2 := real_inner_le_norm a b
  rcases (norm_nonneg a).eq_or_lt with ha | ha
  · rw [← ha]; exact norm_nonneg b
  · nlinarith

variable {B : E →L[ℝ] E} {f : E → E}

omit [FiniteDimensional ℝ E] in
/-- A firmly nonexpansive matrix is positive semidefinite. -/
theorem IsFirmlyNonexpansiveOp.inner_nonneg (h : IsFirmlyNonexpansiveOp B) (v : E) :
    0 ≤ ⟪B v, v⟫_ℝ :=
  (sq_nonneg _).trans (h v)

omit [FiniteDimensional ℝ E] in
/-- A firmly nonexpansive matrix has norm at most one. -/
theorem IsFirmlyNonexpansiveOp.norm_le_one (h : IsFirmlyNonexpansiveOp B) : ‖B‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ by
    rw [one_mul]; exact norm_le_of_sq_le_inner (h v)

omit [FiniteDimensional ℝ E] in
theorem isClosed_setOf_isFirmlyNonexpansiveOp :
    IsClosed {B : E →L[ℝ] E | IsFirmlyNonexpansiveOp B} := by
  simp only [IsFirmlyNonexpansiveOp, ofPred_forall]
  refine isClosed_iInter fun v ↦ isClosed_le ?_ ?_
  · exact ((continuous_id.clm_apply continuous_const).norm.pow 2)
  · exact (continuous_id.clm_apply continuous_const).inner continuous_const

omit [FiniteDimensional ℝ E] in
theorem IsFirmlyNonexpansive.lipschitzWith (h : IsFirmlyNonexpansive f) : LipschitzWith 1 f :=
  LipschitzWith.of_dist_le_mul fun u₁ u₂ ↦ by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
    exact norm_le_of_sq_le_inner (h u₁ u₂)

omit [FiniteDimensional ℝ E] in
/-- The derivative of a firmly nonexpansive mapping is firmly nonexpansive. -/
theorem IsFirmlyNonexpansive.isFirmlyNonexpansiveOp_of_hasFDerivAt (h : IsFirmlyNonexpansive f)
    {u : E} (hA : HasFDerivAt f B u) : IsFirmlyNonexpansiveOp B := by
  intro v
  have hc : Tendsto (fun n : ℕ ↦ ‖(n : ℝ)‖) atTop atTop := by
    simpa using tendsto_natCast_atTop_atTop
  have hlim := hA.lim v hc
  refine le_of_tendsto_of_tendsto (hlim.norm.pow 2) (hlim.inner tendsto_const_nhds) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set Δ := f (u + (n : ℝ)⁻¹ • v) - f u
  have key := h (u + (n : ℝ)⁻¹ • v) u
  rw [add_sub_cancel_left, real_inner_smul_right] at key
  rw [norm_smul, mul_pow, real_inner_smul_left, Real.norm_eq_abs, sq_abs]
  have e : (n : ℝ) ^ 2 * ((n : ℝ)⁻¹ * ⟪Δ, v⟫_ℝ) = n * ⟪Δ, v⟫_ℝ := by
    field_simp
  rw [← e]
  exact mul_le_mul_of_nonneg_left key (sq_nonneg _)

omit [FiniteDimensional ℝ E] in
/-- The elements of the B-subdifferential of a firmly nonexpansive mapping are firmly
nonexpansive [Gfrerer–Outrata 2022, proof of Prop. 3.22]. -/
theorem IsFirmlyNonexpansive.isFirmlyNonexpansiveOp_of_mem_bSubdiff (h : IsFirmlyNonexpansive f)
    {u : E} (hB : B ∈ bSubdiff f u) : IsFirmlyNonexpansiveOp B := by
  obtain ⟨y, hd, -, hlim⟩ := hB
  exact isClosed_setOf_isFirmlyNonexpansiveOp.mem_of_tendsto hlim
    (Eventually.of_forall fun k ↦ h.isFirmlyNonexpansiveOp_of_hasFDerivAt (hd k).hasFDerivAt)

end Firm

/-! ### Monotone mappings and their resolvents -/

section Monotone

/-- `F : E ⇉ E` is monotone if `⟪y₁ - y₂, x₁ - x₂⟫ ≥ 0` on `gph F`
[Gfrerer–Outrata 2022, p. 15]. -/
def IsMonotoneOp (F : E → Set E) : Prop :=
  ∀ x₁ x₂, ∀ y₁ ∈ F x₁, ∀ y₂ ∈ F x₂, 0 ≤ ⟪y₁ - y₂, x₁ - x₂⟫_ℝ

/-- `F : E ⇉ E` is maximally monotone if it is monotone and every pair monotonically related
to `gph F` lies in `gph F` [Gfrerer–Outrata 2022, p. 15]. -/
def IsMaximalMonotoneOp (F : E → Set E) : Prop :=
  IsMonotoneOp F ∧ ∀ x y, (∀ x', ∀ y' ∈ F x', 0 ≤ ⟪y - y', x - x'⟫_ℝ) → y ∈ F x

open Classical in
/-- The resolvent `(I + F)⁻¹`, i.e. the point `x` with `u - x ∈ F x` (if there is one). -/
noncomputable def resolvent (F : E → Set E) (u : E) : E :=
  if h : ∃ x, u - x ∈ F x then h.choose else u

variable {F : E → Set E}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem resolvent_spec {u : E} (h : ∃ x, u - x ∈ F x) :
    u - resolvent F u ∈ F (resolvent F u) := by
  classical
  rw [resolvent, dif_pos h]
  exact h.choose_spec

omit [FiniteDimensional ℝ E] in
/-- The resolvent of a monotone mapping is firmly nonexpansive on its domain. -/
theorem IsMonotoneOp.sq_norm_le (hF : IsMonotoneOp F) {u₁ u₂ x₁ x₂ : E} (h₁ : u₁ - x₁ ∈ F x₁)
    (h₂ : u₂ - x₂ ∈ F x₂) : ‖x₁ - x₂‖ ^ 2 ≤ ⟪x₁ - x₂, u₁ - u₂⟫_ℝ := by
  have := hF x₁ x₂ _ h₁ _ h₂
  rw [show u₁ - x₁ - (u₂ - x₂) = (u₁ - u₂) - (x₁ - x₂) by abel, inner_sub_left,
    real_inner_self_eq_norm_sq] at this
  linarith [real_inner_comm (x₁ - x₂) (u₁ - u₂)]

omit [FiniteDimensional ℝ E] in
theorem IsMonotoneOp.eq_of_mem (hF : IsMonotoneOp F) {u x₁ x₂ : E} (h₁ : u - x₁ ∈ F x₁)
    (h₂ : u - x₂ ∈ F x₂) : x₁ = x₂ := by
  have := hF.sq_norm_le h₁ h₂
  rw [sub_self, inner_zero_right] at this
  have h0 : ‖x₁ - x₂‖ = 0 := by nlinarith [norm_nonneg (x₁ - x₂)]
  exact sub_eq_zero.1 (norm_eq_zero.1 h0)

omit [FiniteDimensional ℝ E] in
theorem IsMonotoneOp.resolvent_eq (hF : IsMonotoneOp F) {u x : E} (h : u - x ∈ F x) :
    resolvent F u = x :=
  hF.eq_of_mem (resolvent_spec ⟨x, h⟩) h

variable (hF : IsMonotoneOp F) (hs : ∀ u, ∃ x, u - x ∈ F x)
include hF hs

omit [FiniteDimensional ℝ E] in
/-- Minty: for monotone `F` with `rge(I + F) = E`, the resolvent `(I + F)⁻¹` is single-valued
and firmly nonexpansive [Gfrerer–Outrata 2022, proof of Prop. 3.22]. -/
theorem IsMonotoneOp.isFirmlyNonexpansive_resolvent : IsFirmlyNonexpansive (resolvent F) :=
  fun u₁ u₂ ↦ hF.sq_norm_le (resolvent_spec (hs u₁)) (resolvent_spec (hs u₂))

omit [FiniteDimensional ℝ E] in
/-- The easy half of Minty's theorem: a monotone `F` with `rge(I + F) = E` is maximally
monotone. -/
theorem IsMonotoneOp.isMaximalMonotoneOp : IsMaximalMonotoneOp F := by
  refine ⟨hF, fun x y hxy ↦ ?_⟩
  set x' := resolvent F (x + y)
  have h1 : x + y - x' ∈ F x' := resolvent_spec (hs _)
  have h2 := hxy x' _ h1
  rw [show y - (x + y - x') = -(x - x') by abel, inner_neg_left, real_inner_self_eq_norm_sq]
    at h2
  have h3 : ‖x - x'‖ = 0 := by nlinarith [norm_nonneg (x - x')]
  have hx : x' = x := (sub_eq_zero.1 (norm_eq_zero.1 h3)).symm
  rw [hx, add_sub_cancel_left] at h1
  exact h1

omit [FiniteDimensional ℝ E] in
/-- `gph F = Φ⁻¹(gph (I + F)⁻¹)` with `Φ(x, y) = (x + y, x)`. -/
theorem IsMonotoneOp.graph_eq_image_resolvent :
    graph F = mintyMap.symm '' graph (fun u ↦ ({resolvent F u} : Set E)) := by
  ext ⟨x, y⟩
  constructor
  · intro hxy
    have h : x + y - x ∈ F x := by rw [add_sub_cancel_left]; exact hxy
    refine ⟨(x + y, x), (hF.resolvent_eq h).symm, ?_⟩
    simp
  · rintro ⟨⟨u, z⟩, hz, hq⟩
    have hz' : z = resolvent F u := hz
    simp only [mintyMap_symm_apply, Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    change u - z ∈ F z
    rw [hz']
    exact resolvent_spec (hs u)

/-- `𝒮F(p) = Φ⁻¹ 𝒮(I + F)⁻¹(Φ p)` for `Φ(x, y) = (x + y, x)`. -/
theorem IsMonotoneOp.scDeriv_eq (p : E × E) :
    scDeriv F p = (fun L ↦ L.map
        (((mintyMap (E := E)).symm : (E × E) →L[ℝ] (E × E)) : (E × E) →ₗ[ℝ] (E × E))) ''
      scDeriv (fun u ↦ ({resolvent F u} : Set E)) (mintyMap p) := by
  have := scDeriv_image_linear (F := fun u ↦ ({resolvent F u} : Set E)) (G := F) mintyMap.symm
    (hF.graph_eq_image_resolvent hs) (mintyMap p)
  rwa [ContinuousLinearEquiv.symm_apply_apply] at this

/-- [Gfrerer–Outrata 2022, Prop. 3.22], global form: for a monotone `F` with
`rge(I + F) = E` (by Minty's theorem, exactly the maximally monotone mappings),
`𝒮F(x, y) = {rge(B, I - B) | B ∈ ∇̄(I + F)⁻¹(x + y)}`. -/
theorem IsMonotoneOp.mem_scDeriv_iff {p : E × E} (hp : p ∈ graph F) {L : Submodule ℝ (E × E)} :
    L ∈ scDeriv F p ↔ ∃ B ∈ bSubdiff (resolvent F) (p.1 + p.2), L = mintySubspace B := by
  have hp' : p.1 + p.2 - p.1 ∈ F p.1 := by rw [add_sub_cancel_left]; exact hp
  have hmp : mintyMap p = (p.1 + p.2, resolvent F (p.1 + p.2)) := by
    rw [hF.resolvent_eq hp']; rfl
  have hlip := ((hF.isFirmlyNonexpansive_resolvent hs).lipschitzWith).lipschitzOnWith
    (s := univ)
  rw [hF.scDeriv_eq hs, hmp]
  constructor
  · rintro ⟨L', hL', rfl⟩
    obtain ⟨B, hB, rfl⟩ := (mem_scDeriv_iff_of_lipschitzOnWith hlip univ_mem).1 hL'
    exact ⟨B, hB, map_graph_mintyMap_symm B⟩
  · rintro ⟨B, hB, rfl⟩
    exact ⟨_, (mem_scDeriv_iff_of_lipschitzOnWith hlip univ_mem).2 ⟨B, hB, rfl⟩,
      map_graph_mintyMap_symm B⟩

/-- [Gfrerer–Outrata 2022, Prop. 3.22], global form, for `𝒮*F`:
`𝒮*F(x, y) = {rge(Bᵀ, I - Bᵀ) | B ∈ ∇̄(I + F)⁻¹(x + y)}`. -/
theorem IsMonotoneOp.mem_scCoderiv_iff {p : E × E} (hp : p ∈ graph F)
    {L : Submodule ℝ (E × E)} :
    L ∈ scCoderiv F p ↔ ∃ B ∈ bSubdiff (resolvent F) (p.1 + p.2),
      L = mintySubspace (ContinuousLinearMap.adjoint B) := by
  constructor
  · rintro ⟨L', hL', rfl⟩
    obtain ⟨B, hB, rfl⟩ := (hF.mem_scDeriv_iff hs hp).1 hL'
    exact ⟨B, hB, adjointSubspace_mintySubspace B⟩
  · rintro ⟨B, hB, rfl⟩
    exact ⟨_, (hF.mem_scDeriv_iff hs hp).2 ⟨B, hB, rfl⟩, adjointSubspace_mintySubspace B⟩

/-- [Gfrerer–Outrata 2022, Prop. 3.22], global form: every `L ∈ 𝒮F(x, y)` is `rge(B, I - B)`
with `B` firmly nonexpansive, and then `L* = rge(Bᵀ, I - Bᵀ)`. -/
theorem IsMonotoneOp.exists_firm_of_mem_scDeriv {p : E × E} (hp : p ∈ graph F)
    {L : Submodule ℝ (E × E)} (hL : L ∈ scDeriv F p) :
    ∃ B : E →L[ℝ] E, IsFirmlyNonexpansiveOp B ∧ L = mintySubspace B ∧
      adjointSubspace L = mintySubspace (ContinuousLinearMap.adjoint B) := by
  obtain ⟨B, hB, rfl⟩ := (hF.mem_scDeriv_iff hs hp).1 hL
  exact ⟨B, (hF.isFirmlyNonexpansive_resolvent hs).isFirmlyNonexpansiveOp_of_mem_bSubdiff hB,
    rfl, adjointSubspace_mintySubspace B⟩

/-- [Gfrerer–Outrata 2022, Prop. 3.22], global form: a monotone `F` with `rge(I + F) = E` is an
SCD mapping. -/
theorem IsMonotoneOp.isSCDMapping : IsSCDMapping F := by
  intro p hp
  obtain ⟨B, hB⟩ := bSubdiff_nonempty_of_lipschitzOnWith
    (((hF.isFirmlyNonexpansive_resolvent hs).lipschitzWith).lipschitzOnWith (s := univ))
    (x := p.1 + p.2) univ_mem
  exact ⟨_, (hF.mem_scDeriv_iff hs hp).2 ⟨B, hB, rfl⟩⟩

end Monotone

/-! ### Symmetric linear maps -/

section Symmetric

/-- `B` is symmetric: `⟪B v, w⟫ = ⟪B w, v⟫`. -/
def IsSymmetricOp (B : E →L[ℝ] E) : Prop := ∀ v w, ⟪B v, w⟫_ℝ = ⟪B w, v⟫_ℝ

omit [FiniteDimensional ℝ E] in
theorem isClosed_setOf_isSymmetricOp : IsClosed {B : E →L[ℝ] E | IsSymmetricOp B} := by
  simp only [IsSymmetricOp, ofPred_forall]
  exact isClosed_iInter fun v ↦ isClosed_iInter fun w ↦ isClosed_eq
    ((continuous_id.clm_apply continuous_const).inner continuous_const)
    ((continuous_id.clm_apply continuous_const).inner continuous_const)

omit [FiniteDimensional ℝ E] in
theorem IsSymmetricOp.adjoint_eq [CompleteSpace E] {B : E →L[ℝ] E} (h : IsSymmetricOp B) :
    ContinuousLinearMap.adjoint B = B :=
  ((ContinuousLinearMap.eq_adjoint_iff B B).2 fun v w ↦ by
    rw [h, real_inner_comm]).symm

end Symmetric

/-! ### Subdifferentials of convex functions: Cor. 3.28 -/

section Convex

variable {φ : E → EReal}

/-- The subdifferential mapping `∂φ : E ⇉ E` of `φ : E → EReal`, with subgradients read in `E`
through the Riesz map. -/
noncomputable def subdiffMap (φ : E → EReal) (x : E) : Set E :=
  (toDual ℝ E).symm '' subdiff φ x

theorem mem_subdiffMap_iff {x y : E} : y ∈ subdiffMap φ x ↔ toDual ℝ E y ∈ subdiff φ x := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa using hv
  · intro h
    exact ⟨_, h, by simp⟩

/-- The subdifferential of a convex function is monotone. -/
theorem isMonotoneOp_subdiffMap (hconv : Convex ℝ (φ.Epi univ)) : IsMonotoneOp (subdiffMap φ) := by
  intro x₁ x₂ y₁ hy₁ y₂ hy₂
  have := globallyMonotone_subdiff_of_convex hconv x₁ x₂ _ (mem_subdiffMap_iff.1 hy₁) _
    (mem_subdiffMap_iff.1 hy₂)
  simpa [toDual_apply_apply, inner_sub_left] using this


/-- The Moreau envelope `e φ(u) = φ(prox u) + ½‖prox u - u‖²` at the proximal point
`prox u = (I + ∂φ)⁻¹ u`. -/
noncomputable def moreauEnv (φ : E → EReal) (u : E) : ℝ :=
  (φ (resolvent (subdiffMap φ) u)).toReal + ‖resolvent (subdiffMap φ) u - u‖ ^ 2 / 2

omit [FiniteDimensional ℝ E] in
/-- The two-sided estimate behind the differentiability of the Moreau envelope. -/
theorem moreauEnv_estimate_aux (d p q : E) (r r' : ℝ) (h1 : r + ⟪p, d - q⟫_ℝ ≤ r')
    (h2 : r' + ⟪p + q, q - d⟫_ℝ ≤ r) :
    0 ≤ r' + ‖p + q‖ ^ 2 / 2 - (r + ‖p‖ ^ 2 / 2) - ⟪p, d⟫_ℝ ∧
      r' + ‖p + q‖ ^ 2 / 2 - (r + ‖p‖ ^ 2 / 2) - ⟪p, d⟫_ℝ ≤ ‖d‖ ^ 2 / 2 := by
  have e1 := norm_add_sq_real p q
  have e2 := norm_sub_sq_real q d
  have e3 : 0 ≤ ‖q - d‖ ^ 2 := sq_nonneg _
  have e4 : 0 ≤ ‖q‖ ^ 2 := sq_nonneg _
  simp only [inner_sub_right, inner_add_left, real_inner_self_eq_norm_sq] at h1 h2
  constructor <;> nlinarith

variable (hconv : Convex ℝ (φ.Epi univ)) (hlsc : LowerSemicontinuous φ) (hbot : ∀ y, φ y ≠ ⊥)
  (hdom : ∃ y, φ y ≠ ⊤)
include hconv hlsc hbot hdom

/-- Minty's theorem for subdifferentials: for a proper l.s.c. convex `φ`, `rge(I + ∂φ) = E`;
the point is the proximal point, the minimizer of `φ + ½‖· - u‖²`. -/
theorem exists_sub_mem_subdiffMap (u : E) : ∃ x, u - x ∈ subdiffMap φ x := by
  obtain ⟨w, b, hwb⟩ := exists_affine_minorant_of_convex hconv hbot hdom
  set h : E → ℝ := fun y ↦ (1 / 2) * ‖y - u‖ ^ 2 with h_def
  set h' : E → StrongDual ℝ E := fun y ↦
    (1 / 2 : ℝ) • (2 • (innerSL ℝ (y - u)).comp (ContinuousLinearMap.id ℝ E)) with h'_def
  have hh : ∀ y, HasFDerivAt h (h' y) y := fun y ↦
    (((hasFDerivAt_id y).sub_const u).norm_sq).const_mul (1 / 2)
  have hhc : Continuous h := continuous_iff_continuousAt.2 fun y ↦ (hh y).continuousAt
  set ψ : E → EReal := fun y ↦ φ y + (h y : EReal) with hψ_def
  have hψlsc : LowerSemicontinuous ψ :=
    hlsc.add' (continuous_coe_real_ereal.comp hhc).lowerSemicontinuous fun y ↦
      EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
  obtain ⟨y₀, hy₀⟩ := hdom
  set c₀ : ℝ := (φ y₀).toReal + h y₀
  have hc₀ : ψ y₀ = c₀ := by
    rw [hψ_def, EReal.coe_add, EReal.coe_toReal hy₀ (hbot y₀)]
  set K := {y | ψ y ≤ c₀}
  have hKc : IsClosed K := hψlsc.isClosed_preimage (c₀ : EReal)
  set C := |c₀ + b - w u|
  set R := 2 * ‖w‖ + 2 * C + 1
  have hC0 : 0 ≤ C := abs_nonneg _
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
  have hKb : K ⊆ Metric.closedBall u R := by
    intro y hy
    have hle : ((w y - b + h y : ℝ) : EReal) ≤ c₀ := by
      rw [EReal.coe_add]
      exact (add_le_add (hwb y) le_rfl).trans hy
    rw [EReal.coe_le_coe_iff] at hle
    set s := ‖y - u‖ with hs_def
    have hs0 : 0 ≤ s := norm_nonneg _
    have hw : -(‖w‖ * s) ≤ w y - w u := by
      have h1 := w.le_opNorm (y - u)
      rw [map_sub, Real.norm_eq_abs] at h1
      linarith [neg_abs_le (w y - w u)]
    have hC : c₀ + b - w u ≤ C := le_abs_self _
    have hs2 : s ^ 2 ≤ 2 * C + 2 * ‖w‖ * s := by
      simp only [h_def] at hle
      nlinarith
    rw [Metric.mem_closedBall, dist_eq_norm]
    by_contra hcon
    push Not at hcon
    have hs1 : 1 ≤ s := by linarith
    have h3 : R * s < s ^ 2 := by nlinarith
    nlinarith [mul_nonneg hC0 (sub_nonneg.2 hs1)]
  obtain ⟨ys, hysK, hmin⟩ := (hψlsc.lowerSemicontinuousOn K).exists_isMinOn
    ⟨y₀, show ψ y₀ ≤ c₀ from hc₀.le⟩
    ((isCompact_closedBall u R).of_isClosed_subset hKc hKb)
  have hglob : ∀ y, ψ ys ≤ ψ y := by
    intro y
    by_cases hy : y ∈ K
    · exact hmin hy
    · exact (show ψ ys ≤ c₀ from hysK).trans (not_le.1 hy).le
  have hφys : φ ys ≠ ⊤ := by
    intro htop
    have : ψ ys = ⊤ := by rw [hψ_def]; simp [htop]
    have := (show ψ ys ≤ c₀ from hysK)
    simp_all
  set r := (φ ys).toReal
  have hr : φ ys = r := (EReal.coe_toReal hφys (hbot ys)).symm
  have hψr : ψ ys = ((r + h ys : ℝ) : EReal) := by
    change φ ys + ((h ys : ℝ) : EReal) = _
    rw [hr, ← EReal.coe_add]
  have h0 := zero_mem_regularSubdiff_of_isLocalMin
    (Eventually.of_forall hglob : IsLocalMin ψ ys) hψr
  have hmem : 0 - h' ys ∈ subdiff φ ys := by
    rw [subdiff_eq_regularSubdiff_of_convex hconv]
    exact (mem_regularSubdiff_add_iff (hh ys)).1 h0
  refine ⟨ys, mem_subdiffMap_iff.2 ?_⟩
  convert hmem using 1
  ext v
  simp only [h'_def, toDual_apply_apply, zero_sub, neg_apply, smul_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    inner_sub_left]
  ring

/-- [Gfrerer–Outrata 2022, Cor. 3.28]: the subdifferential of a proper l.s.c. convex function
is an SCD mapping. -/
theorem isSCDMapping_subdiffMap : IsSCDMapping (subdiffMap φ) :=
  (isMonotoneOp_subdiffMap hconv).isSCDMapping (exists_sub_mem_subdiffMap hconv hlsc hbot hdom)

/-- `u - prox u ∈ ∂φ(prox u)`. -/
theorem toDual_sub_resolvent_mem_subdiff (u : E) :
    toDual ℝ E (u - resolvent (subdiffMap φ) u) ∈ subdiff φ (resolvent (subdiffMap φ) u) :=
  mem_subdiffMap_iff.1 (resolvent_spec (exists_sub_mem_subdiffMap hconv hlsc hbot hdom u))

theorem resolvent_subdiffMap_eq_toReal (u : E) :
    φ (resolvent (subdiffMap φ) u) = ((φ (resolvent (subdiffMap φ) u)).toReal : EReal) := by
  obtain ⟨r, hr, -⟩ := toDual_sub_resolvent_mem_subdiff hconv hlsc hbot hdom u
  rw [hr, EReal.toReal_coe]

/-- The subgradient inequality between proximal points. -/
theorem resolvent_subdiffMap_subgradient (u u' : E) :
    (φ (resolvent (subdiffMap φ) u)).toReal +
        ⟪u - resolvent (subdiffMap φ) u,
          resolvent (subdiffMap φ) u' - resolvent (subdiffMap φ) u⟫_ℝ ≤
      (φ (resolvent (subdiffMap φ) u')).toReal := by
  have := (mem_subdiff_of_convex hconv (resolvent_subdiffMap_eq_toReal hconv hlsc hbot hdom u)).1
    (toDual_sub_resolvent_mem_subdiff hconv hlsc hbot hdom u) (resolvent (subdiffMap φ) u')
  rwa [resolvent_subdiffMap_eq_toReal hconv hlsc hbot hdom u', EReal.coe_le_coe_iff,
    toDual_apply_apply] at this

/-- The Moreau envelope is differentiable with `∇ e φ(u) = u - prox u`. -/
theorem hasFDerivAt_moreauEnv (u : E) :
    HasFDerivAt (moreauEnv φ) (innerSL ℝ (u - resolvent (subdiffMap φ) u)) u := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine (Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun d ↦ ?_)).trans_isLittleO
    (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  set a := resolvent (subdiffMap φ) u
  set a' := resolvent (subdiffMap φ) (u + d)
  set r := (φ a).toReal
  set r' := (φ a').toReal
  have h1 := resolvent_subdiffMap_subgradient hconv hlsc hbot hdom u (u + d)
  have h2 := resolvent_subdiffMap_subgradient hconv hlsc hbot hdom (u + d) u
  set p := u - a
  set q := (u + d - a') - (u - a)
  have ea : a' - a = d - q := by simp only [q]; abel
  have eb : u + d - a' = p + q := by simp only [p, q]; abel
  have ec : a - a' = q - d := by simp only [q]; abel
  rw [ea] at h1
  rw [eb, ec] at h2
  obtain ⟨hlo, hhi⟩ := moreauEnv_estimate_aux d p q r r' h1 h2
  have hm : moreauEnv φ (u + d) - moreauEnv φ u - innerSL ℝ (u - a) d =
      r' + ‖p + q‖ ^ 2 / 2 - (r + ‖p‖ ^ 2 / 2) - ⟪p, d⟫_ℝ := by
    simp only [moreauEnv, innerSL_apply_apply]
    rw [← eb, norm_sub_rev a' (u + d), norm_sub_rev a u]
  rw [hm, Real.norm_eq_abs, abs_of_nonneg hlo, one_mul, norm_pow, norm_norm]
  linarith

/-- `prox = ∇(½‖·‖² - e φ)`. -/
theorem hasFDerivAt_proxPotential (u : E) :
    HasFDerivAt (fun u ↦ 1 / 2 * ‖u‖ ^ 2 - moreauEnv φ u)
      (innerSL ℝ (resolvent (subdiffMap φ) u)) u := by
  have h := ((hasFDerivAt_id u).norm_sq.const_mul (1 / 2)).sub
    (hasFDerivAt_moreauEnv hconv hlsc hbot hdom u)
  refine h.congr_fderiv ?_
  ext w
  simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, inner_sub_left, id_eq]
  ring

/-- The derivative of the proximal mapping is symmetric wherever it exists (it is a Hessian). -/
theorem isSymmetricOp_of_hasFDerivAt_resolvent {A : E →L[ℝ] E} {x : E}
    (hA : HasFDerivAt (resolvent (subdiffMap φ)) A x) : IsSymmetricOp A := by
  intro v w
  have := second_derivative_symmetric_of_eventually_of_real
    (f := fun u ↦ 1 / 2 * ‖u‖ ^ 2 - moreauEnv φ u)
    (f' := fun y ↦ innerSL ℝ (resolvent (subdiffMap φ) y))
    (Eventually.of_forall fun y ↦ hasFDerivAt_proxPotential hconv hlsc hbot hdom y)
    ((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).hasFDerivAt.comp x hA) v w
  simp only [ContinuousLinearMap.comp_apply] at this
  exact this

theorem isSymmetricOp_of_mem_bSubdiff_resolvent {B : E →L[ℝ] E} {u : E}
    (hB : B ∈ bSubdiff (resolvent (subdiffMap φ)) u) : IsSymmetricOp B := by
  obtain ⟨y, hd, -, hlim⟩ := hB
  exact isClosed_setOf_isSymmetricOp.mem_of_tendsto hlim
    (Eventually.of_forall fun k ↦
      isSymmetricOp_of_hasFDerivAt_resolvent hconv hlsc hbot hdom (hd k).hasFDerivAt)

/-- [Gfrerer–Outrata 2022, Cor. 3.28]: for every `L ∈ 𝒮∂φ(x, x*)` there is a symmetric positive
semidefinite `B` with `‖B‖ ≤ 1` and `L = rge(B, I - B)`. -/
theorem exists_symm_of_mem_scDeriv_subdiffMap {p : E × E} (hp : p ∈ graph (subdiffMap φ))
    {L : Submodule ℝ (E × E)} (hL : L ∈ scDeriv (subdiffMap φ) p) :
    ∃ B : E →L[ℝ] E, IsSymmetricOp B ∧ (∀ v, 0 ≤ ⟪B v, v⟫_ℝ) ∧ ‖B‖ ≤ 1 ∧
      L = mintySubspace B := by
  have hF := isMonotoneOp_subdiffMap hconv
  have hs := exists_sub_mem_subdiffMap hconv hlsc hbot hdom
  obtain ⟨B, hB, rfl⟩ := (hF.mem_scDeriv_iff hs hp).1 hL
  have hfirm := (hF.isFirmlyNonexpansive_resolvent hs).isFirmlyNonexpansiveOp_of_mem_bSubdiff hB
  exact ⟨B, isSymmetricOp_of_mem_bSubdiff_resolvent hconv hlsc hbot hdom hB, hfirm.inner_nonneg,
    hfirm.norm_le_one, rfl⟩

/-- [Gfrerer–Outrata 2022, Cor. 3.28]: `L* = L` for every `L ∈ 𝒮∂φ(x, x*)`. -/
theorem adjointSubspace_eq_of_mem_scDeriv_subdiffMap {p : E × E}
    (hp : p ∈ graph (subdiffMap φ)) {L : Submodule ℝ (E × E)}
    (hL : L ∈ scDeriv (subdiffMap φ) p) : adjointSubspace L = L := by
  obtain ⟨B, hB, -, -, rfl⟩ := exists_symm_of_mem_scDeriv_subdiffMap hconv hlsc hbot hdom hp hL
  rw [adjointSubspace_mintySubspace, hB.adjoint_eq]

/-- [Gfrerer–Outrata 2022, Cor. 3.28]: `𝒮*∂φ(x, x*) = 𝒮∂φ(x, x*)`. -/
theorem scCoderiv_subdiffMap {p : E × E} (hp : p ∈ graph (subdiffMap φ)) :
    scCoderiv (subdiffMap φ) p = scDeriv (subdiffMap φ) p := by
  ext L
  constructor
  · rintro ⟨L', hL', rfl⟩
    rwa [adjointSubspace_eq_of_mem_scDeriv_subdiffMap hconv hlsc hbot hdom hp hL']
  · intro hL
    exact ⟨L, hL, adjointSubspace_eq_of_mem_scDeriv_subdiffMap hconv hlsc hbot hdom hp hL⟩

end Convex

/-! ### Locality of `𝒮F` and the subspaces `rge(B, I - c B)` -/

section Local

omit [FiniteDimensional ℝ E] in
/-- The contingent cone only depends on the set near the point. -/
theorem contingentCone_subset_of_inter_eq {Ω Ω' W : Set (E × E)} (hW : IsOpen W)
    (h : Ω ∩ W = Ω' ∩ W) {q : E × E} (hq : q ∈ W) :
    contingentCone Ω q ⊆ contingentCone Ω' q := by
  rintro w ⟨hqΩ, s, α, hsα, hslim, hw⟩
  have hq' : q ∈ Ω' := (show q ∈ Ω' ∩ W by rw [← h]; exact ⟨hqΩ, hq⟩).1
  refine mem_contingentCone_of_eventually hq' s α ?_ hslim hw
  filter_upwards [hslim.eventually (hW.mem_nhds hq)] with k hk
  exact ⟨(show s k ∈ Ω' ∩ W by rw [← h]; exact ⟨(hsα k).1, hk⟩).1, (hsα k).2⟩

variable {F G : E → Set E} {W : Set (E × E)}

omit [FiniteDimensional ℝ E] in
theorem graphicallySmoothAt_of_inter_eq (hW : IsOpen W) (h : graph F ∩ W = graph G ∩ W)
    {q : E × E} (hq : q ∈ W) (hsm : GraphicallySmoothAt F q) :
    GraphicallySmoothAt G q ∧ tangentSubspace F q = tangentSubspace G q := by
  have hcone : contingentCone (graph F) q = contingentCone (graph G) q :=
    subset_antisymm (contingentCone_subset_of_inter_eq hW h hq)
      (contingentCone_subset_of_inter_eq hW h.symm hq)
  obtain ⟨hqF, L, hdim, hL⟩ := hsm
  refine ⟨⟨(show q ∈ graph G ∩ W by rw [← h]; exact ⟨hqF, hq⟩).1, L, hdim, hL.trans hcone⟩, ?_⟩
  rw [tangentSubspace, tangentSubspace, hcone]

/-- `𝒮F(p)` only depends on `gph F` near `p`. -/
theorem scDeriv_subset_of_inter_eq_of_isOpen (hW : IsOpen W) (h : graph F ∩ W = graph G ∩ W)
    {p : E × E} (hp : p ∈ W) : scDeriv F p ⊆ scDeriv G p := by
  rintro L ⟨q, hq, hqlim, hT⟩
  have hev : ∀ᶠ k in atTop, q k ∈ W := hqlim.eventually (hW.mem_nhds hp)
  exact mem_scDeriv_of_eventually
    (hev.mono fun k hk ↦ (graphicallySmoothAt_of_inter_eq hW h hk (hq k)).1) hqlim
    (hT.congr_eventually (hev.mono fun k hk ↦ (graphicallySmoothAt_of_inter_eq hW h hk (hq k)).2))

theorem scDeriv_eq_of_inter_eq (hW : IsOpen W) (h : graph F ∩ W = graph G ∩ W) {p : E × E}
    (hp : p ∈ W) : scDeriv F p = scDeriv G p :=
  subset_antisymm (scDeriv_subset_of_inter_eq_of_isOpen hW h hp)
    (scDeriv_subset_of_inter_eq_of_isOpen hW h.symm hp)

/-- The subspace `rge(B, I - c B) = {(B v, v - c B v) | v ∈ E}`. -/
noncomputable def hypoMintySubspace (c : ℝ) (B : E →L[ℝ] E) : Submodule ℝ (E × E) :=
  LinearMap.range ((B : E →ₗ[ℝ] E).prod (LinearMap.id - c • (B : E →ₗ[ℝ] E)))

omit [FiniteDimensional ℝ E] in
theorem mem_hypoMintySubspace_iff {c : ℝ} {B : E →L[ℝ] E} {w : E × E} :
    w ∈ hypoMintySubspace c B ↔ ∃ v, B v = w.1 ∧ v - c • B v = w.2 := by
  rw [hypoMintySubspace, LinearMap.mem_range]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v, rfl, rfl⟩
  · rintro ⟨v, h1, h2⟩
    exact ⟨v, Prod.ext h1 h2⟩

omit [FiniteDimensional ℝ E] in
/-- `rge(B, I - c B)* = rge(Bᵀ, I - c Bᵀ)`. -/
theorem adjointSubspace_hypoMintySubspace [CompleteSpace E] (c : ℝ) (B : E →L[ℝ] E) :
    adjointSubspace (hypoMintySubspace c B) =
      hypoMintySubspace c (ContinuousLinearMap.adjoint B) := by
  ext ⟨y, x⟩
  rw [mk_mem_adjointSubspace_iff, mem_hypoMintySubspace_iff]
  constructor
  · intro h
    have h1 : ContinuousLinearMap.adjoint B (x + c • y) = y := by
      refine ext_inner_right ℝ fun w ↦ ?_
      rw [ContinuousLinearMap.adjoint_inner_left, inner_add_left, real_inner_smul_left,
        h (B w) (w - c • B w) (mem_hypoMintySubspace_iff.2 ⟨w, rfl, rfl⟩), inner_sub_right,
        real_inner_smul_right]
      ring
    exact ⟨x + c • y, h1, by rw [h1]; abel⟩
  · rintro ⟨z, hz1, hz2⟩ u v huv
    obtain ⟨w, hw1, hw2⟩ := mem_hypoMintySubspace_iff.1 huv
    simp only at hz1 hz2 hw1 hw2
    subst hz1 hz2 hw1 hw2
    rw [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]

omit [FiniteDimensional ℝ E] in
/-- `[I 0; -γI I] rge(B, I - B) = rge(B, I - (1 + γ)B)`. -/
theorem map_shearCLM_mintySubspace (γ : ℝ) (B : E →L[ℝ] E) :
    (mintySubspace B).map (shearCLM (-(γ • ContinuousLinearMap.id ℝ E)) : (E × E) →ₗ[ℝ] (E × E)) =
      hypoMintySubspace (1 + γ) B := by
  ext w
  rw [Submodule.mem_map, mem_hypoMintySubspace_iff]
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨v, h1, h2⟩ := mem_mintySubspace_iff.1 hq
    refine ⟨v, by simp [h1], ?_⟩
    simp only [ContinuousLinearMap.coe_coe, shearCLM_apply, neg_apply, smul_apply,
      ContinuousLinearMap.id_apply, ← h1, ← h2]
    rw [add_smul, one_smul]
    abel
  · rintro ⟨v, h1, h2⟩
    refine ⟨(B v, v - B v), mem_mintySubspace_iff.2 ⟨v, rfl, rfl⟩, ?_⟩
    simp only [ContinuousLinearMap.coe_coe, shearCLM_apply, neg_apply, smul_apply,
      ContinuousLinearMap.id_apply]
    refine Prod.ext h1 ?_
    rw [← h2, add_smul, one_smul]
    abel_nf

omit [FiniteDimensional ℝ E] in
theorem mem_graph_add_smul_iff (γ : ℝ) {q : E × E} :
    (q.1, q.2 + γ • q.1) ∈ graph (fun x ↦ (fun y ↦ y + γ • x) '' F x) ↔ q ∈ graph F := by
  constructor
  · rintro ⟨y, hy, hyq⟩
    have : y = q.2 := add_right_cancel hyq
    change q.2 ∈ F q.1
    rw [← this]
    exact hy
  · intro hq
    exact ⟨q.2, hq, rfl⟩

end Local

end VariationalAnalysis
