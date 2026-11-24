/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import VariationalAnalysis.SCD.Basic

/-!
# SCD regularity

Following [Gfrerer–Outrata 2022, Section 4], a subspace `L ⊆ E × E` with `dim L = n = dim E` is
*regular* (`L ∈ 𝓛ₙ^reg`) if `(y*, 0) ∈ L` forces `y* = 0`. Every regular subspace is the range
`rge(C_L, I) = {(C_L x*, x*)}` of a unique linear map `C_L` (Prop. 4.2), and
`L* = rge(C_Lᵀ, I)`. A mapping `F` is *SCD regular* around `(x̄, ȳ)` if it has the SCD property
around `(x̄, ȳ)` and every `L ∈ 𝒮*F(x̄, ȳ)` is regular (Def. 4.1); the modulus of SCD regularity is
`scdreg F(x̄, ȳ) = sup {‖y*‖ | (y*, x*) ∈ ⋃ 𝒮*F(x̄, ȳ), ‖x*‖ ≤ 1}`.

We take `scdreg` with values in `ℝ≥0∞` (the supremum of the empty family is `0`, and the value
`∞` is allowed a priori). Norm bounds are stated for the components `x*, y* ∈ E` separately, so
the choice of norm on `E × E` (the sup norm in Lean, the Euclidean norm in the paper) plays no
role in this file.

## Main declarations

* `IsRegularSubspace L`: `L ∈ 𝓛ₙ^reg` [Gfrerer–Outrata 2022, Def. 4.1(1)].
* `regularSubspaceOp L`: the operator `C_L` with `L = rge(C_L, I)` [Gfrerer–Outrata 2022,
  Prop. 4.2] (defined as `0` for non-regular `L`).
* `rgeSubspace C`: the subspace `rge(C, I) = {(C x, x)}`.
* `subspaceBound L`: `sup {‖y*‖ | (y*, x*) ∈ L, ‖x*‖ ≤ 1}`.
* `IsSCDRegularAround F p`: SCD regularity [Gfrerer–Outrata 2022, Def. 4.1(2)].
* `scdreg F p`: the modulus of SCD regularity [Gfrerer–Outrata 2022, Def. 4.1(2)].

## Main results

* `isRegularSubspace_range_prod_iff`, `IsRegularSubspace.regularSubspaceOp_apply_snd`:
  Prop. 4.2 and Remark 4.3: `rge(B, A)` is regular iff `A` is invertible, and then
  `C_L = B A⁻¹`.
* `IsRegularSubspace.mem_iff`, `IsRegularSubspace.eq_rgeSubspace`: `L = rge(C_L, I)`.
* `IsRegularSubspace.adjointSubspace_eq`, `IsRegularSubspace.adjoint`,
  `IsRegularSubspace.regularSubspaceOp_adjointSubspace`: `L* = rge(C_Lᵀ, I) ∈ 𝓛ₙ^reg`.
* `IsRegularSubspace.inner_adjoint_eq`: (32); `IsRegularSubspace.norm_fst_le`: (33).
* `IsRegularSubspace.subspaceBound_eq`, `scdreg_eq_iSup_nnnorm`: (34).
* `isSCDRegularAround_iff_scDeriv`, `scdreg_eq_iSup_scDeriv`: Lemma 4.5.
* `IsSCDRegularAround.scdreg_lt_top`: Lemma 4.7.
* `eventually_forall_norm_lt_of_scdreg_lt`, `IsSCDRegularAround.eventually`: Prop. 4.8.
-/

open Filter Topology Set Module
open scoped InnerProductSpace NNReal ENNReal

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Regular subspaces -/

/-- `L ∈ 𝓛ₙ^reg`: `dim L = dim E` and `(y*, 0) ∈ L ⇒ y* = 0`
[Gfrerer–Outrata 2022, Def. 4.1(1)]. -/
def IsRegularSubspace (L : Submodule ℝ (E × E)) : Prop :=
  finrank ℝ L = finrank ℝ E ∧ ∀ y : E, (y, 0) ∈ L → y = 0

/-- The subspace `rge(C, I) = {(C x, x) | x ∈ E}`. -/
noncomputable def rgeSubspace (C : E →L[ℝ] E) : Submodule ℝ (E × E) :=
  LinearMap.range ((C : E →ₗ[ℝ] E).prod LinearMap.id)

omit [FiniteDimensional ℝ E] in
theorem mem_rgeSubspace_iff {C : E →L[ℝ] E} {w : E × E} : w ∈ rgeSubspace C ↔ w.1 = C w.2 := by
  constructor
  · rintro ⟨x, rfl⟩
    simp
  · intro h
    exact ⟨w.2, Prod.ext (by simp [h]) (by simp)⟩

omit [FiniteDimensional ℝ E] in
theorem mk_mem_rgeSubspace_iff {C : E →L[ℝ] E} {y x : E} : (y, x) ∈ rgeSubspace C ↔ y = C x :=
  mem_rgeSubspace_iff

omit [FiniteDimensional ℝ E] in
theorem finrank_rgeSubspace (C : E →L[ℝ] E) : finrank ℝ (rgeSubspace C) = finrank ℝ E :=
  LinearMap.finrank_range_of_inj fun x y hxy ↦ by simpa using congrArg Prod.snd hxy

omit [FiniteDimensional ℝ E] in
theorem isRegularSubspace_rgeSubspace (C : E →L[ℝ] E) : IsRegularSubspace (rgeSubspace C) :=
  ⟨finrank_rgeSubspace C, fun y hy ↦ by simpa using mk_mem_rgeSubspace_iff.1 hy⟩

section Op

variable {L : Submodule ℝ (E × E)}

/-- The second projection `L → E`. -/
noncomputable def subspaceSnd (L : Submodule ℝ (E × E)) : L →ₗ[ℝ] E :=
  (LinearMap.snd ℝ E E).comp L.subtype

theorem IsRegularSubspace.bijective_subspaceSnd (hL : IsRegularSubspace L) :
    Function.Bijective (subspaceSnd L) := by
  have hinj : Function.Injective (subspaceSnd L) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨y, x⟩, hw⟩ h0
    have hx : x = 0 := h0
    subst hx
    have := hL.2 y hw
    subst this
    rfl
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hL.1).1 hinj⟩

/-- For regular `L`, the second projection is a linear equivalence `L ≃ E`. -/
noncomputable def IsRegularSubspace.sndEquiv (hL : IsRegularSubspace L) : L ≃ₗ[ℝ] E :=
  LinearEquiv.ofBijective (subspaceSnd L) hL.bijective_subspaceSnd

open Classical in
/-- The operator `C_L` with `L = rge(C_L, I)` for `L ∈ 𝓛ₙ^reg` [Gfrerer–Outrata 2022,
Prop. 4.2]; it is `0` when `L` is not regular. -/
noncomputable def regularSubspaceOp (L : Submodule ℝ (E × E)) : E →L[ℝ] E :=
  if hL : IsRegularSubspace L then
    LinearMap.toContinuousLinearMap
      ((LinearMap.fst ℝ E E).comp (L.subtype.comp hL.sndEquiv.symm.toLinearMap))
  else 0

theorem IsRegularSubspace.regularSubspaceOp_apply (hL : IsRegularSubspace L) (x : E) :
    regularSubspaceOp L x = (hL.sndEquiv.symm x : E × E).1 := by
  rw [regularSubspaceOp, dif_pos hL]
  rfl

theorem IsRegularSubspace.snd_sndEquiv_symm (hL : IsRegularSubspace L) (x : E) :
    (hL.sndEquiv.symm x : E × E).2 = x :=
  hL.sndEquiv.apply_symm_apply x

/-- `(C_L x*, x*) ∈ L`. -/
theorem IsRegularSubspace.mk_mem (hL : IsRegularSubspace L) (x : E) :
    (regularSubspaceOp L x, x) ∈ L := by
  have h := (hL.sndEquiv.symm x).2
  have he : (hL.sndEquiv.symm x : E × E) = (regularSubspaceOp L x, x) :=
    Prod.ext (hL.regularSubspaceOp_apply x).symm (hL.snd_sndEquiv_symm x)
  rwa [he] at h

/-- Prop. 4.2 of [Gfrerer–Outrata 2022]: `L = rge(C_L, I)`, i.e. `(y*, x*) ∈ L ↔ y* = C_L x*`. -/
theorem IsRegularSubspace.mem_iff (hL : IsRegularSubspace L) {y x : E} :
    (y, x) ∈ L ↔ y = regularSubspaceOp L x := by
  constructor
  · intro h
    have h1 : hL.sndEquiv ⟨(y, x), h⟩ = x := rfl
    have h2 : hL.sndEquiv.symm x = ⟨(y, x), h⟩ := (LinearEquiv.symm_apply_eq _).2 h1.symm
    rw [hL.regularSubspaceOp_apply, h2]
  · rintro rfl
    exact hL.mk_mem x

theorem IsRegularSubspace.mem_iff' (hL : IsRegularSubspace L) {w : E × E} :
    w ∈ L ↔ w.1 = regularSubspaceOp L w.2 :=
  hL.mem_iff

theorem IsRegularSubspace.eq_rgeSubspace (hL : IsRegularSubspace L) :
    L = rgeSubspace (regularSubspaceOp L) := by
  ext w
  rw [hL.mem_iff', mem_rgeSubspace_iff]

/-- Uniqueness of `C_L` in Prop. 4.2 of [Gfrerer–Outrata 2022]: if `L = rge(C, I)`, then `L` is
regular and `C_L = C`. -/
theorem regularSubspaceOp_of_forall_mem_iff {C : E →L[ℝ] E}
    (h : ∀ y x : E, (y, x) ∈ L ↔ y = C x) :
    IsRegularSubspace L ∧ regularSubspaceOp L = C := by
  have hL : L = rgeSubspace C := by
    ext w
    rw [mem_rgeSubspace_iff]
    exact h w.1 w.2
  subst hL
  have hreg := isRegularSubspace_rgeSubspace C
  refine ⟨hreg, ContinuousLinearMap.ext fun x ↦ ?_⟩
  exact ((h _ _).1 (hreg.mk_mem x))

theorem regularSubspaceOp_rgeSubspace (C : E →L[ℝ] E) : regularSubspaceOp (rgeSubspace C) = C :=
  (regularSubspaceOp_of_forall_mem_iff fun _ _ ↦ mk_mem_rgeSubspace_iff).2

/-- Prop. 4.2 of [Gfrerer–Outrata 2022]: `rge(B, A) ∈ 𝓛ₙ^reg` iff `A` is invertible, for an
injective `(B, A) : E → E × E` (a `2n × n` matrix `Z` of full column rank with `π₁ Z = B`,
`π₂ Z = A`). -/
theorem isRegularSubspace_range_prod_iff {B A : E →ₗ[ℝ] E}
    (hinj : Function.Injective (B.prod A)) :
    IsRegularSubspace (LinearMap.range (B.prod A)) ↔ Function.Bijective A := by
  have hdim : finrank ℝ (LinearMap.range (B.prod A)) = finrank ℝ E :=
    LinearMap.finrank_range_of_inj hinj
  constructor
  · intro hL
    have hA : Function.Injective A := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro p hp
      have hB : B p = 0 := hL.2 (B p) ⟨p, by simp [hp]⟩
      exact hinj (by simp [hB, hp])
    exact ⟨hA, LinearMap.injective_iff_surjective.1 hA⟩
  · intro hA
    refine ⟨hdim, fun y ⟨p, hp⟩ ↦ ?_⟩
    have h1 : B p = y := congrArg Prod.fst hp
    have h2 : A p = 0 := congrArg Prod.snd hp
    have : p = 0 := hA.1 (by rw [h2, map_zero])
    rw [← h1, this, map_zero]

/-- Remark 4.3 of [Gfrerer–Outrata 2022]: for `L = rge(B, A) ∈ 𝓛ₙ^reg`, `C_L A = B`,
i.e. `C_L = B A⁻¹`. -/
theorem IsRegularSubspace.regularSubspaceOp_apply_snd {B A : E →ₗ[ℝ] E}
    (hL : IsRegularSubspace (LinearMap.range (B.prod A))) (p : E) :
    regularSubspaceOp (LinearMap.range (B.prod A)) (A p) = B p :=
  (hL.mem_iff.1 ⟨p, rfl⟩).symm

/-- Prop. 4.2 of [Gfrerer–Outrata 2022]: `L* = rge(C_Lᵀ, I)`. -/
theorem IsRegularSubspace.adjointSubspace_eq (hL : IsRegularSubspace L) :
    adjointSubspace L = rgeSubspace (ContinuousLinearMap.adjoint (regularSubspaceOp L)) := by
  ext ⟨y, x⟩
  rw [mk_mem_adjointSubspace_iff, mk_mem_rgeSubspace_iff]
  constructor
  · intro h
    refine ext_inner_right ℝ fun v ↦ ?_
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact (h _ v (hL.mk_mem v)).symm
  · rintro rfl u v huv
    rw [hL.mem_iff.1 huv, ContinuousLinearMap.adjoint_inner_left]

/-- Prop. 4.2 of [Gfrerer–Outrata 2022]: `L* ∈ 𝓛ₙ^reg`. -/
theorem IsRegularSubspace.adjoint (hL : IsRegularSubspace L) :
    IsRegularSubspace (adjointSubspace L) := by
  rw [hL.adjointSubspace_eq]
  exact isRegularSubspace_rgeSubspace _

/-- Prop. 4.2 of [Gfrerer–Outrata 2022]: `C_{L*} = C_Lᵀ`. -/
theorem IsRegularSubspace.regularSubspaceOp_adjointSubspace (hL : IsRegularSubspace L) :
    regularSubspaceOp (adjointSubspace L) = ContinuousLinearMap.adjoint (regularSubspaceOp L) := by
  rw [hL.adjointSubspace_eq, regularSubspaceOp_rgeSubspace]

/-- For `n`-dimensional `L`, `L ∈ 𝓛ₙ^reg` iff `L* ∈ 𝓛ₙ^reg`. -/
theorem isRegularSubspace_adjointSubspace_iff :
    IsRegularSubspace (adjointSubspace L) ↔ IsRegularSubspace L := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.adjoint⟩
  simpa [adjointSubspace_adjointSubspace] using h.adjoint

/-- (32) of [Gfrerer–Outrata 2022]: `⟪x*, C_Lᵀ v⟫ = ⟪y*, v⟫` for `(y*, x*) ∈ L`. -/
theorem IsRegularSubspace.inner_adjoint_eq (hL : IsRegularSubspace L) {y x : E} (h : (y, x) ∈ L)
    (v : E) : ⟪x, ContinuousLinearMap.adjoint (regularSubspaceOp L) v⟫_ℝ = ⟪y, v⟫_ℝ := by
  rw [ContinuousLinearMap.adjoint_inner_right, ← hL.mem_iff.1 h]

/-- (33) of [Gfrerer–Outrata 2022]: `‖y*‖ ≤ ‖C_L‖ ‖x*‖` for `(y*, x*) ∈ L`. -/
theorem IsRegularSubspace.norm_fst_le (hL : IsRegularSubspace L) {y x : E} (h : (y, x) ∈ L) :
    ‖y‖ ≤ ‖regularSubspaceOp L‖ * ‖x‖ := by
  rw [hL.mem_iff.1 h]
  exact (regularSubspaceOp L).le_opNorm x

end Op

/-! ### The bound `sup {‖y*‖ | (y*, x*) ∈ L, ‖x*‖ ≤ 1}` -/

section Bound

variable {L : Submodule ℝ (E × E)}

/-- `sup {‖y*‖ | (y*, x*) ∈ L, ‖x*‖ ≤ 1}` (in `ℝ≥0∞`). -/
noncomputable def subspaceBound (L : Submodule ℝ (E × E)) : ℝ≥0∞ :=
  ⨆ (w : E × E) (_ : w ∈ L) (_ : ‖w.2‖ ≤ 1), (‖w.1‖₊ : ℝ≥0∞)

omit [FiniteDimensional ℝ E] in
theorem le_subspaceBound {w : E × E} (hw : w ∈ L) (h : ‖w.2‖ ≤ 1) :
    (‖w.1‖₊ : ℝ≥0∞) ≤ subspaceBound L :=
  le_iSup₂_of_le w hw (le_iSup_of_le h le_rfl)

omit [FiniteDimensional ℝ E] in
theorem subspaceBound_le_iff {c : ℝ≥0∞} :
    subspaceBound L ≤ c ↔ ∀ w ∈ L, ‖w.2‖ ≤ 1 → (‖w.1‖₊ : ℝ≥0∞) ≤ c := by
  simp [subspaceBound]

omit [FiniteDimensional ℝ E] in
theorem lt_subspaceBound_iff {c : ℝ≥0∞} :
    c < subspaceBound L ↔ ∃ w ∈ L, ‖w.2‖ ≤ 1 ∧ c < ‖w.1‖₊ := by
  simp only [subspaceBound, lt_iSup_iff, exists_prop]

omit [FiniteDimensional ℝ E] in
/-- A bound on `‖y*‖` over `(y*, x*) ∈ L`, `‖x*‖ ≤ 1`, makes an `n`-dimensional `L` regular. -/
theorem isRegularSubspace_of_bound (hdim : finrank ℝ L = finrank ℝ E) {κ : ℝ}
    (h : ∀ w ∈ L, ‖w.2‖ ≤ 1 → ‖w.1‖ ≤ κ) : IsRegularSubspace L := by
  refine ⟨hdim, fun y hy ↦ ?_⟩
  by_contra hne
  have hpos : 0 < ‖y‖ := norm_pos_iff.2 hne
  have hκ : 0 ≤ κ := by simpa using h 0 (zero_mem L) (by simp)
  set t : ℝ := (κ + 1) / ‖y‖
  have hmem : (t • y, (0 : E)) ∈ L := by simpa using L.smul_mem t hy
  have := h _ hmem (by simp)
  simp only [norm_smul, Real.norm_eq_abs, t, abs_div, abs_norm] at this
  rw [abs_of_pos (by linarith), div_mul_cancel₀ _ hpos.ne'] at this
  linarith

/-- If `‖y*‖ ≤ κ` whenever `(y*, x*) ∈ L`, `‖x*‖ ≤ 1`, then `‖C_L‖ ≤ κ`. -/
theorem IsRegularSubspace.norm_le_of_bound (hL : IsRegularSubspace L) {κ : ℝ} (hκ : 0 ≤ κ)
    (h : ∀ w ∈ L, ‖w.2‖ ≤ 1 → ‖w.1‖ ≤ κ) : ‖regularSubspaceOp L‖ ≤ κ :=
  ContinuousLinearMap.opNorm_le_of_unit_norm hκ fun x hx ↦
    h (regularSubspaceOp L x, x) (hL.mk_mem x) hx.le

/-- (34) of [Gfrerer–Outrata 2022] for a single subspace: for `L ∈ 𝓛ₙ^reg`,
`sup {‖y*‖ | (y*, x*) ∈ L, ‖x*‖ ≤ 1} = ‖C_L‖`. -/
theorem IsRegularSubspace.subspaceBound_eq (hL : IsRegularSubspace L) :
    subspaceBound L = ‖regularSubspaceOp L‖₊ := by
  refine le_antisymm (subspaceBound_le_iff.2 fun w hw hw2 ↦ ?_) ?_
  · rw [hL.mem_iff'.1 hw, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
    calc ‖regularSubspaceOp L w.2‖ ≤ ‖regularSubspaceOp L‖ * ‖w.2‖ :=
        (regularSubspaceOp L).le_opNorm _
      _ ≤ ‖regularSubspaceOp L‖ * 1 := by gcongr
      _ = _ := mul_one _
  · rcases eq_top_or_lt_top (subspaceBound L) with htop | hlt
    · rw [htop]; exact le_top
    · lift subspaceBound L to ℝ≥0 using hlt.ne with s hs
      have hb : ∀ w ∈ L, ‖w.2‖ ≤ 1 → ‖w.1‖ ≤ s := fun w hw hw2 ↦ by
        have := le_subspaceBound hw hw2
        rw [← hs, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm] at this
        exact this
      rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm]
      exact hL.norm_le_of_bound s.2 hb

/-- `sup {‖y*‖ | (y*, x*) ∈ L*, ‖x*‖ ≤ 1} = sup {‖u‖ | (u, v) ∈ L, ‖v‖ ≤ 1}` for regular `L`
(the isometry `C ↦ Cᵀ`). -/
theorem IsRegularSubspace.subspaceBound_adjointSubspace (hL : IsRegularSubspace L) :
    subspaceBound (adjointSubspace L) = subspaceBound L := by
  rw [hL.adjoint.subspaceBound_eq, hL.subspaceBound_eq,
    hL.regularSubspaceOp_adjointSubspace, ContinuousLinearMap.adjoint.nnnorm_map]

end Bound

/-! ### SCD regularity -/

variable {F : E → Set E} {p : E × E}

/-- `F` is SCD regular around `p ∈ gph F` if it has the SCD property around `p` and
`(y*, 0) ∈ ⋃ 𝒮*F(p) ⇒ y* = 0` [Gfrerer–Outrata 2022, Def. 4.1(2)]. -/
def IsSCDRegularAround (F : E → Set E) (p : E × E) : Prop :=
  HasSCDPropertyAround F p ∧ ∀ L ∈ scCoderiv F p, ∀ y : E, (y, 0) ∈ L → y = 0

/-- The modulus of SCD regularity
`scdreg F(p) = sup {‖y*‖ | (y*, x*) ∈ ⋃ 𝒮*F(p), ‖x*‖ ≤ 1}` [Gfrerer–Outrata 2022, Def. 4.1(2)]. -/
noncomputable def scdreg (F : E → Set E) (p : E × E) : ℝ≥0∞ :=
  ⨆ L ∈ scCoderiv F p, subspaceBound L

theorem IsSCDRegularAround.isRegularSubspace (h : IsSCDRegularAround F p)
    {L : Submodule ℝ (E × E)} (hL : L ∈ scCoderiv F p) : IsRegularSubspace L :=
  ⟨finrank_of_mem_scCoderiv hL, h.2 L hL⟩

theorem le_scdreg {L : Submodule ℝ (E × E)} (hL : L ∈ scCoderiv F p) {w : E × E} (hw : w ∈ L)
    (h : ‖w.2‖ ≤ 1) : (‖w.1‖₊ : ℝ≥0∞) ≤ scdreg F p :=
  (le_subspaceBound hw h).trans (le_iSup₂_of_le L hL le_rfl)

theorem scdreg_le_iff {c : ℝ≥0∞} :
    scdreg F p ≤ c ↔ ∀ L ∈ scCoderiv F p, ∀ w ∈ L, ‖w.2‖ ≤ 1 → (‖w.1‖₊ : ℝ≥0∞) ≤ c := by
  simp only [scdreg, iSup_le_iff, subspaceBound_le_iff]

theorem lt_scdreg_iff {c : ℝ≥0∞} :
    c < scdreg F p ↔ ∃ L ∈ scCoderiv F p, ∃ w ∈ L, ‖w.2‖ ≤ 1 ∧ c < ‖w.1‖₊ := by
  simp only [scdreg, lt_iSup_iff, lt_subspaceBound_iff, exists_prop]

/-- (34) of [Gfrerer–Outrata 2022]: under SCD regularity,
`scdreg F(p) = sup {‖C_L‖ | L ∈ 𝒮*F(p)}`. -/
theorem IsSCDRegularAround.scdreg_eq_iSup_nnnorm (h : IsSCDRegularAround F p) :
    scdreg F p = ⨆ L ∈ scCoderiv F p, (‖regularSubspaceOp L‖₊ : ℝ≥0∞) :=
  iSup_congr fun _ ↦ iSup_congr fun hL ↦ (h.isRegularSubspace hL).subspaceBound_eq

/-- `‖C_L‖ ≤ scdreg F(p)` for `L ∈ 𝒮*F(p)` (from (34) of [Gfrerer–Outrata 2022]). -/
theorem IsSCDRegularAround.nnnorm_regularSubspaceOp_le (h : IsSCDRegularAround F p)
    {L : Submodule ℝ (E × E)} (hL : L ∈ scCoderiv F p) :
    (‖regularSubspaceOp L‖₊ : ℝ≥0∞) ≤ scdreg F p := by
  rw [← (h.isRegularSubspace hL).subspaceBound_eq]
  exact le_iSup₂_of_le L hL le_rfl

/-- Lemma 4.5 of [Gfrerer–Outrata 2022]: `F` is SCD regular around `p` iff it has the SCD
property around `p` and `(u, 0) ∈ ⋃ 𝒮F(p) ⇒ u = 0`. -/
theorem isSCDRegularAround_iff_scDeriv :
    IsSCDRegularAround F p ↔
      HasSCDPropertyAround F p ∧ ∀ L ∈ scDeriv F p, ∀ u : E, (u, 0) ∈ L → u = 0 := by
  refine and_congr_right fun _ ↦ ⟨fun h L hL ↦ ?_, fun h L hL ↦ ?_⟩
  · have hreg : IsRegularSubspace (adjointSubspace L) :=
      ⟨finrank_of_mem_scCoderiv ⟨L, hL, rfl⟩, h _ ⟨L, hL, rfl⟩⟩
    exact (isRegularSubspace_adjointSubspace_iff.1 hreg).2
  · obtain ⟨L', hL', rfl⟩ := hL
    exact (IsRegularSubspace.adjoint ⟨finrank_of_mem_scDeriv hL', h L' hL'⟩).2

/-- Lemma 4.5 of [Gfrerer–Outrata 2022]: under SCD regularity,
`scdreg F(p) = sup {‖u‖ | (u, v) ∈ ⋃ 𝒮F(p), ‖v‖ ≤ 1} = sup {‖C_L‖ | L ∈ 𝒮F(p)}`. -/
theorem IsSCDRegularAround.scdreg_eq_iSup_scDeriv (h : IsSCDRegularAround F p) :
    scdreg F p = ⨆ L ∈ scDeriv F p, subspaceBound L := by
  have h' := (isSCDRegularAround_iff_scDeriv.1 h).2
  rw [scdreg, scCoderiv, iSup_image]
  exact iSup_congr fun L ↦ iSup_congr fun hL ↦
    IsRegularSubspace.subspaceBound_adjointSubspace ⟨finrank_of_mem_scDeriv hL, h' L hL⟩

theorem IsSCDRegularAround.scdreg_eq_iSup_scDeriv_nnnorm (h : IsSCDRegularAround F p) :
    scdreg F p = ⨆ L ∈ scDeriv F p, (‖regularSubspaceOp L‖₊ : ℝ≥0∞) := by
  have h' := (isSCDRegularAround_iff_scDeriv.1 h).2
  rw [h.scdreg_eq_iSup_scDeriv]
  exact iSup_congr fun L ↦ iSup_congr fun hL ↦
    IsRegularSubspace.subspaceBound_eq ⟨finrank_of_mem_scDeriv hL, h' L hL⟩

/-! ### Compactness: Lemma 4.7 and Prop. 4.8 -/

/-- Compactness of `𝒮*F` along `qₖ → p` (from Lemma 3.13 of [Gfrerer–Outrata 2022] and
compactness of the Grassmannian): bounded `wₖ ∈ Lₖ ∈ 𝒮*F(qₖ)` have a subsequence converging to
some `w ∈ L ∈ 𝒮*F(p)`. -/
theorem exists_mem_scCoderiv_of_bounded {q : ℕ → E × E} (hq : Tendsto q atTop (𝓝 p))
    {L : ℕ → Submodule ℝ (E × E)} (hL : ∀ k, L k ∈ scCoderiv F (q k)) {w : ℕ → E × E}
    (hw : ∀ k, w k ∈ L k) {R : ℝ} (hR : ∀ k, ‖w k‖ ≤ R) :
    ∃ L₀ ∈ scCoderiv F p, ∃ w₀ ∈ L₀, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (w ∘ φ) atTop (𝓝 w₀) := by
  obtain ⟨L₀, -, φ₁, hφ₁, hL₀⟩ := exists_grassTendsto_subseq L (n := finrank ℝ E)
    fun k ↦ finrank_of_mem_scCoderiv (hL k)
  obtain ⟨w₀, -, φ₂, hφ₂, hw₀⟩ := (isCompact_closedBall (0 : E × E) R).tendsto_subseq
    (x := fun k ↦ w (φ₁ k)) fun k ↦ mem_closedBall_zero_iff.2 (hR _)
  have hconv : GrassTendsto (L ∘ (φ₁ ∘ φ₂)) L₀ := hL₀.comp hφ₂.tendsto_atTop
  refine ⟨L₀, mem_scCoderiv_of_tendsto (hq.comp (hφ₁.comp hφ₂).tendsto_atTop)
    (fun k ↦ hL _) hconv, w₀, hconv.mem_of_tendsto (fun k ↦ hw _) hw₀, φ₁ ∘ φ₂,
    hφ₁.comp hφ₂, hw₀⟩

theorem coe_nnnorm_eq_ofReal {G : Type*} [SeminormedAddCommGroup G] (x : G) :
    (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ := by
  rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]

/-- Lemma 4.7 of [Gfrerer–Outrata 2022]: if `F` is SCD regular around `p`, then
`scdreg F(p) < ∞`. -/
theorem IsSCDRegularAround.scdreg_lt_top (h : IsSCDRegularAround F p) : scdreg F p < ∞ := by
  by_contra htop
  rw [not_lt_top_iff] at htop
  have key : ∀ k : ℕ, ∃ L ∈ scCoderiv F p, ∃ w ∈ L, ‖w.2‖ ≤ 1 ∧
      ENNReal.ofReal ((k : ℝ) + 1) < ‖w.1‖₊ :=
    fun k ↦ lt_scdreg_iff.1 (htop ▸ ENNReal.ofReal_lt_top)
  choose L hL w hw hw2 hw1 using key
  have hw1' : ∀ k : ℕ, (k : ℝ) + 1 < ‖(w k).1‖ := fun k ↦ by
    have := hw1 k
    rw [coe_nnnorm_eq_ofReal] at this
    exact (ENNReal.ofReal_lt_ofReal_iff'.1 this).1
  have hpos : ∀ k, 0 < ‖(w k).1‖ := fun k ↦ lt_trans (by positivity) (hw1' k)
  set v : ℕ → E × E := fun k ↦ ‖(w k).1‖⁻¹ • w k with hv
  have hv1 : ∀ k, ‖(v k).1‖ = 1 := fun k ↦ by
    simp [v, norm_smul, inv_mul_cancel₀ (hpos k).ne']
  have hv2 : ∀ k, ‖(v k).2‖ ≤ 1 / ((k : ℝ) + 1) := fun k ↦ by
    simp only [v, Prod.smul_snd, norm_smul, norm_inv, norm_norm]
    rw [inv_mul_le_iff₀ (hpos k)]
    calc ‖(w k).2‖ ≤ 1 := hw2 k
      _ ≤ ‖(w k).1‖ * (1 / ((k : ℝ) + 1)) := by
        rw [mul_one_div, le_div_iff₀ (by positivity)]
        linarith [hw1' k]
  have hvR : ∀ k, ‖v k‖ ≤ 1 := fun k ↦ by
    rw [Prod.norm_def, max_le_iff]
    refine ⟨(hv1 k).le, (hv2 k).trans ?_⟩
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  obtain ⟨L₀, hL₀, w₀, hw₀, φ, hφ, hlim⟩ := exists_mem_scCoderiv_of_bounded
    (tendsto_const_nhds (x := p)) hL (w := v) (fun k ↦ (L k).smul_mem _ (hw k)) hvR
  have h1 : ‖w₀.1‖ = 1 := by
    have := ((continuous_norm.comp continuous_fst).tendsto w₀).comp hlim
    simp only [Function.comp_def, hv1] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  have h2 : w₀.2 = 0 := by
    have ht := ((continuous_norm.comp continuous_snd).tendsto w₀).comp hlim
    have hδ : Tendsto (fun k ↦ 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    have h0 := squeeze_zero (fun k ↦ norm_nonneg _) (fun k ↦ hv2 (φ k)) hδ
    exact norm_eq_zero.1 (tendsto_nhds_unique ht h0)
  have hmem : (w₀.1, (0 : E)) ∈ L₀ := by
    rw [← h2]; exact hw₀
  have := h.2 L₀ hL₀ w₀.1 hmem
  rw [this, norm_zero] at h1
  exact zero_ne_one h1

/-- Prop. 4.8 of [Gfrerer–Outrata 2022] (core estimate): if `scdreg F(p) < κ`, then for all `q`
near `p`, `‖y*‖ < κ` whenever `(y*, x*) ∈ ⋃ 𝒮*F(q)` and `‖x*‖ ≤ 1`. In particular
`limsup_{q → p} scdreg F(q) ≤ scdreg F(p)`. -/
theorem eventually_forall_norm_lt_of_scdreg_lt {κ : ℝ} (hκ : scdreg F p < ENNReal.ofReal κ) :
    ∀ᶠ q in 𝓝 p, ∀ L ∈ scCoderiv F q, ∀ w ∈ L, ‖w.2‖ ≤ 1 → ‖w.1‖ < κ := by
  have hκpos : 0 < κ := ENNReal.ofReal_pos.1 (lt_of_le_of_lt zero_le hκ)
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨q, hq, hbad⟩ := exists_seq_forall_of_frequently hcon
  simp only [not_forall, not_lt, exists_prop] at hbad
  choose L hL w hw hw2 hw1 using hbad
  have hpos : ∀ k, 0 < ‖(w k).1‖ := fun k ↦ lt_of_lt_of_le hκpos (hw1 k)
  set v : ℕ → E × E := fun k ↦ ‖(w k).1‖⁻¹ • w k with hv
  have hv1 : ∀ k, ‖(v k).1‖ = 1 := fun k ↦ by
    simp [v, norm_smul, inv_mul_cancel₀ (hpos k).ne']
  have hv2 : ∀ k, ‖(v k).2‖ ≤ κ⁻¹ := fun k ↦ by
    simp only [v, Prod.smul_snd, norm_smul, norm_inv, norm_norm]
    rw [inv_mul_le_iff₀ (hpos k)]
    calc ‖(w k).2‖ ≤ 1 := hw2 k
      _ ≤ ‖(w k).1‖ * κ⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hκpos, one_mul]
        exact hw1 k
  have hvR : ∀ k, ‖v k‖ ≤ max 1 κ⁻¹ := fun k ↦ by
    rw [Prod.norm_def]
    exact max_le_max (hv1 k).le (hv2 k)
  obtain ⟨L₀, hL₀, w₀, hw₀, φ, hφ, hlim⟩ := exists_mem_scCoderiv_of_bounded hq hL (w := v)
    (fun k ↦ (L k).smul_mem _ (hw k)) hvR
  have h1 : ‖w₀.1‖ = 1 := by
    have := ((continuous_norm.comp continuous_fst).tendsto w₀).comp hlim
    simp only [Function.comp_def, hv1] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  have h2 : ‖w₀.2‖ ≤ κ⁻¹ :=
    le_of_tendsto (((continuous_norm.comp continuous_snd).tendsto w₀).comp hlim)
      (Eventually.of_forall fun k ↦ hv2 (φ k))
  have hmem : κ • w₀ ∈ L₀ := L₀.smul_mem κ hw₀
  have hle := le_scdreg hL₀ hmem (by
    rw [Prod.smul_snd, norm_smul, Real.norm_of_nonneg hκpos.le]
    calc κ * ‖w₀.2‖ ≤ κ * κ⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hκpos.ne')
  rw [Prod.smul_fst, coe_nnnorm_eq_ofReal, norm_smul, h1, mul_one,
    Real.norm_of_nonneg hκpos.le] at hle
  exact absurd (lt_of_le_of_lt hle hκ) (lt_irrefl _)

/-- Under `scdreg F(p) < κ`, every `L ∈ 𝒮*F(q)` with `q` near `p` is regular and satisfies
`‖C_L‖ ≤ κ` (Prop. 4.8 and (34) of [Gfrerer–Outrata 2022]). -/
theorem eventually_isRegularSubspace_and_norm_le {κ : ℝ} (hκ : scdreg F p < ENNReal.ofReal κ) :
    ∀ᶠ q in 𝓝 p, ∀ L ∈ scCoderiv F q,
      IsRegularSubspace L ∧ ‖regularSubspaceOp L‖ ≤ κ := by
  have hκpos : 0 < κ := ENNReal.ofReal_pos.1 (lt_of_le_of_lt zero_le hκ)
  filter_upwards [eventually_forall_norm_lt_of_scdreg_lt hκ] with q hq L hL
  have hb : ∀ w ∈ L, ‖w.2‖ ≤ 1 → ‖w.1‖ ≤ κ := fun w hw hw2 ↦ (hq L hL w hw hw2).le
  have hreg := isRegularSubspace_of_bound (finrank_of_mem_scCoderiv hL) hb
  exact ⟨hreg, hreg.norm_le_of_bound hκpos.le hb⟩

/-- Prop. 4.8 of [Gfrerer–Outrata 2022]: if `F` is SCD regular around `p` and
`scdreg F(p) < κ`, then `F` is SCD regular around every `q` near `p`, with `scdreg F(q) ≤ κ`. -/
theorem IsSCDRegularAround.eventually (h : IsSCDRegularAround F p) {κ : ℝ}
    (hκ : scdreg F p < ENNReal.ofReal κ) :
    ∀ᶠ q in 𝓝 p, IsSCDRegularAround F q ∧ scdreg F q ≤ ENNReal.ofReal κ := by
  obtain ⟨U, hU, hscd⟩ := h.1
  filter_upwards [eventually_mem_nhds_iff.2 hU, eventually_forall_norm_lt_of_scdreg_lt hκ,
    eventually_isRegularSubspace_and_norm_le hκ] with q hUq hq hreg
  refine ⟨⟨⟨U, hUq, hscd⟩, fun L hL y hy ↦ (hreg L hL).1.2 y hy⟩, scdreg_le_iff.2 ?_⟩
  intro L hL w hw hw2
  rw [coe_nnnorm_eq_ofReal]
  exact ENNReal.ofReal_le_ofReal (hq L hL w hw hw2).le

/-- Uniform bound near an SCD regular point (Lemma 4.7 and Prop. 4.8 of
[Gfrerer–Outrata 2022]): there is `κ ≥ 0` such that every `L ∈ 𝒮*F(q)`, `q` near `p`, is regular
with `‖C_L‖ ≤ κ`. -/
theorem IsSCDRegularAround.exists_eventually_norm_le (h : IsSCDRegularAround F p) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ᶠ q in 𝓝 p, ∀ L ∈ scCoderiv F q,
      IsRegularSubspace L ∧ ‖regularSubspaceOp L‖ ≤ κ := by
  refine ⟨(scdreg F p).toReal + 1, by positivity, eventually_isRegularSubspace_and_norm_le ?_⟩
  calc scdreg F p = ENNReal.ofReal (scdreg F p).toReal :=
        (ENNReal.ofReal_toReal h.scdreg_lt_top.ne).symm
    _ < ENNReal.ofReal ((scdreg F p).toReal + 1) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (lt_add_one _)

end VariationalAnalysis
