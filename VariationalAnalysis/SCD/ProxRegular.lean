/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis.SecondOrder.ProtoDiff

/-!
# SC derivatives of subdifferentials of prox-regular functions

We prove the second half of [Gfrerer–Outrata 2022, Prop. 3.26] and Cor. 3.27: if `q` is
prox-regular and subdifferentially continuous at `x̄` for `x̄*`, then there is `λ > 0` such that
for all `(x, x*) ∈ gph ∂q` near `(x̄, x̄*)` every `L ∈ 𝒮∂q(x, x*)` is
`rge(B, λ⁻¹(I - B))` with `B` symmetric positive semidefinite, `L* = L` and
`𝒮*∂q(x, x*) = 𝒮∂q(x, x*)`.

## Proof

By `ContinuouslyProxRegularFor.exists_local_moreau`, near `(x̄, x̄*)` the graph of `∂q` is the
preimage under the shear `Φ(x, x*) = (x + λx*, x*)` of the graph of `f = ∇e_λ q̂`, the Lipschitz
gradient of the Moreau envelope of a localization `q̂` of `q`. Hence
`𝒮∂q(x, x*) = {Φ⁻¹ gph C | C ∈ ∇̄f(x + λx*)}` and `Φ⁻¹ gph C = rge(B, λ⁻¹(I - B))` with
`B = I - λC`. The matrices `C` are symmetric as limits of Hessians, and `B` is positive
semidefinite because `I - λf` is the proximal mapping of `q̂`, which is monotone. (The paper uses
the transformation `(x, x*) ↦ (x + λx*, x)` and the Lipschitz mapping `(I + λ∂q̂)⁻¹`, which gives
the same subspaces.)

## Main declarations

* `proxSubspace l B = rge(B, λ⁻¹(I - B))`.

## Main results

* `ContinuouslyProxRegularFor.scd_symm`: [Gfrerer–Outrata 2022, Prop. 3.26], the description of
  `𝒮∂q` and `𝒮*∂q`.
* `isSCDMapping_subdiffMap_of_dense`: [Gfrerer–Outrata 2022, Cor. 3.27].
-/

open Filter Topology Set Metric InnerProductSpace
open scoped NNReal RealInnerProductSpace

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The subspaces `rge(B, λ⁻¹(I - B))` -/

/-- The subspace `rge(B, λ⁻¹(I - B)) = {(B v, λ⁻¹(v - B v)) | v ∈ E}`. -/
noncomputable def proxSubspace (l : ℝ) (B : E →L[ℝ] E) : Submodule ℝ (E × E) :=
  LinearMap.range ((B : E →ₗ[ℝ] E).prod (l⁻¹ • (LinearMap.id - (B : E →ₗ[ℝ] E))))

theorem mem_proxSubspace_iff {l : ℝ} {B : E →L[ℝ] E} {w : E × E} :
    w ∈ proxSubspace l B ↔ ∃ v, B v = w.1 ∧ l⁻¹ • (v - B v) = w.2 := by
  rw [proxSubspace, LinearMap.mem_range]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v, rfl, rfl⟩
  · rintro ⟨v, h1, h2⟩
    exact ⟨v, Prod.ext h1 h2⟩

/-- `rge(B, λ⁻¹(I - B))* = rge(Bᵀ, λ⁻¹(I - Bᵀ))`. -/
theorem adjointSubspace_proxSubspace [CompleteSpace E] {l : ℝ} (hl : l ≠ 0) (B : E →L[ℝ] E) :
    adjointSubspace (proxSubspace l B) = proxSubspace l (ContinuousLinearMap.adjoint B) := by
  ext ⟨y, x⟩
  rw [mk_mem_adjointSubspace_iff, mem_proxSubspace_iff]
  constructor
  · intro h
    have h1 : ContinuousLinearMap.adjoint B (l • x + y) = y := by
      refine ext_inner_right ℝ fun w ↦ ?_
      have := h (B w) (l⁻¹ • (w - B w)) (mem_proxSubspace_iff.2 ⟨w, rfl, rfl⟩)
      rw [real_inner_smul_right, inner_sub_right] at this
      rw [ContinuousLinearMap.adjoint_inner_left, inner_add_left, real_inner_smul_left, this]
      field_simp
      ring
    refine ⟨l • x + y, h1, ?_⟩
    rw [h1, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hl, one_smul]
  · rintro ⟨z, hz1, hz2⟩ u v huv
    obtain ⟨w, hw1, hw2⟩ := mem_proxSubspace_iff.1 huv
    simp only at hz1 hz2 hw1 hw2
    subst hz1 hz2 hw1 hw2
    rw [real_inner_smul_left, real_inner_smul_right, inner_sub_left, inner_sub_right,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]

/-- `Φ⁻¹ rge(I, C) = rge(B, λ⁻¹(I - B))` for the shear `Φ(x, y) = (x + λy, y)` and
`B = I - λC`. -/
theorem map_graphShear_symm_graph {l : ℝ} (hl : l ≠ 0) (C : E →L[ℝ] E) :
    (C : E →ₗ[ℝ] E).graph.map
        (((graphShear (l • ContinuousLinearMap.id ℝ E)).symm : (E × E) →L[ℝ] (E × E)) :
          (E × E) →ₗ[ℝ] (E × E)) =
      proxSubspace l (ContinuousLinearMap.id ℝ E - l • C) := by
  ext w
  rw [Submodule.mem_map, mem_proxSubspace_iff]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [LinearMap.mem_graph_iff] at hq
    refine ⟨q.1, by simp [hq], ?_⟩
    simp [hq, smul_smul, hl]
  · rintro ⟨v, h1, h2⟩
    refine ⟨(v, C v), by simp [LinearMap.mem_graph_iff], ?_⟩
    refine Prod.ext ?_ ?_
    · simpa using h1
    · rw [← h2]
      simp [smul_smul, hl]

/-! ### Derivatives of monotone mappings and of gradients -/

/-- The derivative of a mapping which is monotone around `y` is positive semidefinite. -/
theorem inner_nonneg_of_hasFDerivAt_of_monotone {P : E → E} {D : E →L[ℝ] E} {y : E} {s : Set E}
    (hs : s ∈ 𝓝 y) (hmono : ∀ u₁ ∈ s, ∀ u₂ ∈ s, 0 ≤ ⟪P u₁ - P u₂, u₁ - u₂⟫_ℝ)
    (hD : HasFDerivAt P D y) (v : E) : 0 ≤ ⟪D v, v⟫_ℝ := by
  have hc : Tendsto (fun n : ℕ ↦ ‖(n : ℝ)‖) atTop atTop := by
    simpa using tendsto_natCast_atTop_atTop
  have hlim := hD.lim v hc
  have hy : Tendsto (fun n : ℕ ↦ y + (n : ℝ)⁻¹ • v) atTop (𝓝 y) := by
    have h := ((tendsto_inv_atTop_zero (𝕜 := ℝ)).comp tendsto_natCast_atTop_atTop).smul_const v
    simpa using h.const_add y
  refine ge_of_tendsto (hlim.inner tendsto_const_nhds) ?_
  filter_upwards [eventually_gt_atTop 0, hy.eventually hs] with n hn hns
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have key := hmono _ hns y (mem_of_mem_nhds hs)
  rw [add_sub_cancel_left, real_inner_smul_right] at key
  rw [real_inner_smul_left]
  have := (mul_nonneg_iff_of_pos_left (inv_pos.2 hn')).1 key
  positivity

variable [FiniteDimensional ℝ E]

/-- The derivative of a gradient mapping is symmetric. -/
theorem isSymmetricOp_of_hasFDerivAt_gradient {e : E → ℝ} {f : E → E} {A : E →L[ℝ] E} {y : E}
    (he : ∀ᶠ u in 𝓝 y, HasFDerivAt e (toDual ℝ E (f u)) u) (hA : HasFDerivAt f A y) :
    IsSymmetricOp A := by
  intro v w
  have he' : ∀ᶠ u in 𝓝 y, HasFDerivAt e (innerSL ℝ (f u)) u := he
  have := second_derivative_symmetric_of_eventually_of_real (f := e)
    (f' := fun u ↦ innerSL ℝ (f u)) he'
    ((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).hasFDerivAt.comp y hA) v w
  simp only [ContinuousLinearMap.comp_apply] at this
  exact this

/-! ### Prop. 3.26 and Cor. 3.27 -/

variable {φ : E → EReal} {x₀ : E}

/-- [Gfrerer–Outrata 2022, Prop. 3.26]: if `φ` is prox-regular and subdifferentially continuous at
`x̄` for `x̄* = ⟨g, ·⟩`, then there is `λ > 0` such that for all `(x, x*) ∈ gph ∂φ` near
`(x̄, x̄*)`, `𝒮*∂φ(x, x*) = 𝒮∂φ(x, x*)`, and every `L ∈ 𝒮∂φ(x, x*)` is `rge(B, λ⁻¹(I - B))` with
`B` symmetric positive semidefinite, and `L* = L`. -/
theorem ContinuouslyProxRegularFor.scd_symm {g : E}
    (hφ : ContinuouslyProxRegularFor φ x₀ (toDual ℝ E g)) :
    ∃ l > (0 : ℝ), ∀ᶠ q in 𝓝 (x₀, g), q ∈ graph (subdiffMap φ) →
      scCoderiv (subdiffMap φ) q = scDeriv (subdiffMap φ) q ∧
      ∀ L ∈ scDeriv (subdiffMap φ) q, ∃ B : E →L[ℝ] E, IsSymmetricOp B ∧
        (∀ v, 0 ≤ ⟪B v, v⟫_ℝ) ∧ L = proxSubspace l B ∧ adjointSubspace L = L := by
  obtain ⟨l, hl, δ, hδ, e, f, K, he, hfL, hmono, hloc⟩ := hφ.exists_local_moreau
  refine ⟨l, hl, ?_⟩
  set Φ := graphShear (l • ContinuousLinearMap.id ℝ E) with hΦ
  have hΦc : Continuous fun q : E × E ↦ q.1 + l • q.2 := by fun_prop
  have hball : ∀ᶠ q : E × E in 𝓝 (x₀, g), q.1 + l • q.2 ∈ ball (x₀ + l • g) δ :=
    hΦc.continuousAt.eventually (ball_mem_nhds _ hδ)
  -- the key description of `𝒮∂φ(q)`
  have key : ∀ᶠ q in 𝓝 (x₀, g), q ∈ graph (subdiffMap φ) → ∀ L ∈ scDeriv (subdiffMap φ) q,
      ∃ B : E →L[ℝ] E, IsSymmetricOp B ∧ (∀ v, 0 ≤ ⟪B v, v⟫_ℝ) ∧ L = proxSubspace l B := by
    filter_upwards [eventually_eventually_nhds.2 (hloc.and hball)] with q hq hqgr L hL
    obtain ⟨hq1, hq2⟩ := hq.self_of_nhds
    set u := q.1 + l • q.2 with hu
    have hqf : q.2 = f u := hq1.1 (mem_subdiffMap_iff.1 hqgr)
    have hFG : graph (subdiffMap φ) ∩ {q' | (toDual ℝ E q'.2 ∈ subdiff φ q'.1 ↔
          q'.2 = f (q'.1 + l • q'.2)) ∧ q'.1 + l • q'.2 ∈ ball (x₀ + l • g) δ} =
        Φ ⁻¹' graph (fun u ↦ ({f u} : Set E)) ∩ {q' | (toDual ℝ E q'.2 ∈ subdiff φ q'.1 ↔
          q'.2 = f (q'.1 + l • q'.2)) ∧ q'.1 + l • q'.2 ∈ ball (x₀ + l • g) δ} := by
      ext q'
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h2.1.1 (mem_subdiffMap_iff.1 h1), h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨mem_subdiffMap_iff.2 (h2.1.2 h1), h2⟩
    have hsc := scDeriv_eq_image_symm_of_inter_eq (p := q) (Φ := Φ)
      (D := fun _ ↦ (Φ : (E × E) →L[ℝ] (E × E))) (e := Φ) hq hFG
      (Eventually.of_forall fun q' ↦ Φ.hasStrictFDerivAt) continuousAt_const rfl
    have hΦq : Φ q = (u, f u) := Prod.ext rfl hqf
    rw [hsc, hΦq] at hL
    obtain ⟨L', hL', rfl⟩ := hL
    obtain ⟨C, hC, rfl⟩ :=
      (mem_scDeriv_iff_of_lipschitzOnWith hfL (isOpen_ball.mem_nhds hq2)).1 hL'
    obtain ⟨y, hd, hy, hlim⟩ := hC
    have hev : ∀ᶠ k in atTop, y k ∈ ball (x₀ + l • g) δ := hy.eventually (isOpen_ball.mem_nhds hq2)
    refine ⟨ContinuousLinearMap.id ℝ E - l • C, ?_, fun v ↦ ?_, map_graphShear_symm_graph hl.ne' C⟩
    · have hCs : IsSymmetricOp C := isClosed_setOf_isSymmetricOp.mem_of_tendsto hlim
        (hev.mono fun k hk ↦ isSymmetricOp_of_hasFDerivAt_gradient
          (eventually_of_mem (isOpen_ball.mem_nhds hk) he) (hd k).hasFDerivAt)
      intro v w
      simp only [sub_apply, ContinuousLinearMap.id_apply, smul_apply, inner_sub_left,
        real_inner_smul_left, hCs v w, real_inner_comm v w]
    · have hcont : Continuous fun A : E →L[ℝ] E ↦ ⟪v - l • A v, v⟫_ℝ := by fun_prop
      refine ge_of_tendsto ((hcont.tendsto C).comp hlim) (hev.mono fun k hk ↦ ?_)
      have hP : HasFDerivAt (fun u ↦ u - l • f u)
          (ContinuousLinearMap.id ℝ E - l • fderiv ℝ f (y k)) (y k) :=
        (hasFDerivAt_id (y k)).sub ((hd k).hasFDerivAt.const_smul l)
      exact inner_nonneg_of_hasFDerivAt_of_monotone (isOpen_ball.mem_nhds hk) hmono hP v
  have hadj : ∀ᶠ q in 𝓝 (x₀, g), q ∈ graph (subdiffMap φ) → ∀ L ∈ scDeriv (subdiffMap φ) q,
      adjointSubspace L = L := by
    filter_upwards [key] with q hq hqgr L hL
    obtain ⟨B, hB, -, rfl⟩ := hq hqgr L hL
    rw [adjointSubspace_proxSubspace hl.ne', hB.adjoint_eq]
  filter_upwards [key, hadj] with q hq hq' hqgr
  refine ⟨?_, fun L hL ↦ ?_⟩
  · ext L
    constructor
    · rintro ⟨L', hL', rfl⟩
      rwa [hq' hqgr L' hL']
    · exact fun hL ↦ ⟨L, hL, hq' hqgr L hL⟩
  · obtain ⟨B, hB, hpsd, hLB⟩ := hq hqgr L hL
    exact ⟨B, hB, hpsd, hLB, hq' hqgr L hL⟩

/-- [Gfrerer–Outrata 2022, Cor. 3.27]: if `φ` is prox-regular and subdifferentially continuous
at `x` for `x*` for all `(x, x*)` in a dense subset of `gph ∂φ`, then `∂φ` is an SCD mapping. -/
theorem isSCDMapping_subdiffMap_of_dense {D : Set (E × E)}
    (hD : graph (subdiffMap φ) ⊆ closure D)
    (hDφ : ∀ p ∈ D, ContinuouslyProxRegularFor φ p.1 (toDual ℝ E p.2)) :
    IsSCDMapping (subdiffMap φ) := by
  intro p hp
  obtain ⟨d, hd, hdlim⟩ := mem_closure_iff_seq_limit.1 (hD hp)
  refine hasSCDPropertyAt_of_tendsto hdlim fun k ↦ ?_
  obtain ⟨U, hU, hUF⟩ := (hDφ _ (hd k)).hasSCDPropertyAround
  exact hUF _ ⟨mem_subdiffMap_iff.2 (hDφ _ (hd k)).1.1, mem_of_mem_nhds hU⟩

end VariationalAnalysis
