/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import VariationalAnalysis.SCD.Semismooth

/-!
# Semismoothness* with respect to a cone-valued mapping and its primal form

Following [Gfrerer–Outrata 2024, Section 2.5], a mapping `F : E ⇉ E` is *semismooth** at
`(x̄, ȳ)` with respect to a cone-valued `Γ : E × E ⇉ E × E` if `gph F` lies near `(x̄, ȳ)` in
`dom Γ` and
`|⟪x*, x - x̄⟫ - ⟪y*, y - ȳ⟫| ≤ ε ‖(x, y) - (x̄, ȳ)‖ ‖(y*, x*)‖` for all `(x, y) ∈ gph F` near
`(x̄, ȳ)` and all `(y*, x*) ∈ Γ(x, y)` (Def. 2.10). For `Γ = gph D*F` this is semismoothness*
(Def. 2.9); for `Γ = ⋃ 𝒮*F` it is SCD semismoothness* (Def. 2.11), which agrees with
`IsSCDSemismoothStarAt` [Gfrerer–Outrata 2022, Def. 5.1]. Prop. 2.12 gives the primal form: under
the SCD property around `(x̄, ȳ)`, SCD semismoothness* means
`dist((x, y) - (x̄, ȳ), L) = o(‖(x, y) - (x̄, ȳ)‖)` uniformly in `L ∈ 𝒮F(x, y)`.

## Norms and the statement of Prop. 2.12

`E × E` carries the sup norm in Lean. In the primal characterization the passage from the dual
estimate to the distance estimate has constant `1`, and the converse has constant `2` (we use
`ε / 2`); since both sides are statements "for every `ε > 0`", the characterization is the same
as for the Euclidean norm. The paper writes the distance to subspaces `L ∈ 𝒮*F(x, y)`, but the
vector `(x - x̄, y - ȳ)` lives in the primal space and the argument of [Gfrerer–Outrata 2022,
Prop. 2.12] uses the primal subspaces `L ∈ 𝒮F(x, y)` (equivalently, `L = (L*)*` with
`L* ∈ 𝒮*F(x, y)`); we state it in this form.

## Main declarations

* `IsSemismoothStarWrtAt Γ F p`: semismoothness* with respect to `Γ`
  [Gfrerer–Outrata 2024, Def. 2.10].
* `coderivGraph F q`, `IsSemismoothStarAt F p`: semismoothness* with respect to the limiting
  coderivative [Gfrerer–Outrata 2024, Def. 2.9].
* `scCoderivUnion F q`: the union `⋃ 𝒮*F(q)` [Gfrerer–Outrata 2024, Def. 2.11].

## Main results

* `isSemismoothStarAt_iff`: the explicit form of Def. 2.9.
* `isSCDSemismoothStarAt_iff_wrt`: Def. 2.11 agrees with [Gfrerer–Outrata 2022, Def. 5.1].
* `IsSemismoothStarAt.isSCDSemismoothStarAt`: semismoothness* together with the SCD property
  around implies SCD semismoothness* (via [Gfrerer–Outrata 2022, Lemma 3.7]).
* `isSCDSemismoothStarAt_iff_infDist`: [Gfrerer–Outrata 2024, Prop. 2.12].
-/

open Filter Topology Set Module InnerProductSpace
open scoped InnerProductSpace

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : E → Set E} {p : E × E}

/-! ### Semismoothness* with respect to a mapping -/

/-- `F` is semismooth* at `p = (x̄, ȳ)` with respect to `Γ` if `Γ` is cone-valued, `gph F ⊆ dom Γ`
near `p`, and for every `ε > 0`, `|⟪x*, x - x̄⟫ - ⟪y*, y - ȳ⟫| ≤ ε ‖(x, y) - p‖ ‖(y*, x*)‖` for all
`(x, y) ∈ gph F` near `p` and all `(y*, x*) ∈ Γ(x, y)` [Gfrerer–Outrata 2024, Def. 2.10]. -/
def IsSemismoothStarWrtAt (Γ : E × E → Set (E × E)) (F : E → Set E) (p : E × E) : Prop :=
  (∀ q, ∀ w ∈ Γ q, ∀ t : ℝ, 0 ≤ t → t • w ∈ Γ q) ∧
  (∀ᶠ q in 𝓝 p, q ∈ graph F → (Γ q).Nonempty) ∧
  ∀ ε > 0, ∀ᶠ q in 𝓝 p, q ∈ graph F → ∀ w ∈ Γ q,
    |⟪w.2, q.1 - p.1⟫_ℝ - ⟪w.1, q.2 - p.2⟫_ℝ| ≤ ε * ‖q - p‖ * ‖w‖

omit [FiniteDimensional ℝ E] in
/-- Semismoothness* passes to smaller cone-valued mappings with the same domain near the graph. -/
theorem IsSemismoothStarWrtAt.mono {Γ Γ' : E × E → Set (E × E)}
    (h : IsSemismoothStarWrtAt Γ F p) (hcone : ∀ q, ∀ w ∈ Γ' q, ∀ t : ℝ, 0 ≤ t → t • w ∈ Γ' q)
    (hdom : ∀ᶠ q in 𝓝 p, q ∈ graph F → (Γ' q).Nonempty)
    (hsub : ∀ᶠ q in 𝓝 p, q ∈ graph F → Γ' q ⊆ Γ q) : IsSemismoothStarWrtAt Γ' F p := by
  refine ⟨hcone, hdom, fun ε hε ↦ ?_⟩
  filter_upwards [h.2.2 ε hε, hsub] with q hq hqs hgr w hw using hq hgr w (hqs hgr hw)

/-- The graph of the limiting coderivative `gph D*F(q) = {(y*, x*) | x* ∈ D*F(q)(y*)}`, with
vectors identified with dual elements through `toDual`. -/
def coderivGraph (F : E → Set E) (q : E × E) : Set (E × E) :=
  {w | toDual ℝ E w.2 ∈ coderiv F q.1 q.2 (toDual ℝ E w.1)}

/-- `F` is semismooth* at `p` [Gfrerer–Outrata 2024, Def. 2.9]: semismooth* with respect to the
graph of the limiting coderivative. -/
def IsSemismoothStarAt (F : E → Set E) (p : E × E) : Prop :=
  IsSemismoothStarWrtAt (coderivGraph F) F p

theorem coderivGraph_smul {q w : E × E} (hw : w ∈ coderivGraph F q) {t : ℝ} (ht : 0 ≤ t) :
    t • w ∈ coderivGraph F q := by
  have h := smul_mem_coderiv hw ht
  simpa [coderivGraph] using h

theorem zero_mem_coderivGraph {q : E × E} (hq : q ∈ graph F) : (0 : E × E) ∈ coderivGraph F q := by
  change toDual ℝ E 0 ∈ coderiv F q.1 q.2 (toDual ℝ E 0)
  have h0 : ((0 : StrongDual ℝ E).coprod (-(0 : StrongDual ℝ E))) = 0 := by ext <;> simp
  simp only [map_zero]
  change (0 : StrongDual ℝ E).coprod (-0) ∈ normalCone (graph F) (q.1, q.2)
  rw [h0]
  exact zero_mem_normalCone hq

/-- The explicit form of Def. 2.9 of [Gfrerer–Outrata 2024]. -/
theorem isSemismoothStarAt_iff :
    IsSemismoothStarAt F p ↔ ∀ ε > 0, ∀ᶠ q in 𝓝 p, q ∈ graph F → ∀ y x : E,
      toDual ℝ E x ∈ coderiv F q.1 q.2 (toDual ℝ E y) →
        |⟪x, q.1 - p.1⟫_ℝ - ⟪y, q.2 - p.2⟫_ℝ| ≤ ε * ‖q - p‖ * ‖(y, x)‖ := by
  constructor
  · intro h ε hε
    filter_upwards [h.2.2 ε hε] with q hq hgr y x hyx using hq hgr (y, x) hyx
  · intro h
    refine ⟨fun q w hw t ht ↦ coderivGraph_smul hw ht,
      Eventually.of_forall fun q hq ↦ ⟨0, zero_mem_coderivGraph hq⟩, fun ε hε ↦ ?_⟩
    filter_upwards [h ε hε] with q hq hgr w hw using hq hgr w.1 w.2 hw

/-! ### SCD semismoothness* as semismoothness* with respect to `⋃ 𝒮*F` -/

/-- The union `(⋃ 𝒮*F)(q) = ⋃_{L ∈ 𝒮*F(q)} L` [Gfrerer–Outrata 2024, Def. 2.11]. -/
def scCoderivUnion (F : E → Set E) (q : E × E) : Set (E × E) :=
  ⋃ L ∈ scCoderiv F q, (L : Set (E × E))

theorem mem_scCoderivUnion_iff {q w : E × E} :
    w ∈ scCoderivUnion F q ↔ ∃ L ∈ scCoderiv F q, w ∈ L := by
  simp [scCoderivUnion]

theorem scCoderivUnion_smul {q w : E × E} (hw : w ∈ scCoderivUnion F q) (t : ℝ) :
    t • w ∈ scCoderivUnion F q := by
  obtain ⟨L, hL, hwL⟩ := mem_scCoderivUnion_iff.1 hw
  exact mem_scCoderivUnion_iff.2 ⟨L, hL, L.smul_mem t hwL⟩

theorem scCoderivUnion_nonempty_iff {q : E × E} :
    (scCoderivUnion F q).Nonempty ↔ HasSCDPropertyAt F q := by
  rw [hasSCDPropertyAt_iff_scCoderiv_nonempty]
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨L, hL, -⟩ := mem_scCoderivUnion_iff.1 hw
    exact ⟨L, hL⟩
  · rintro ⟨L, hL⟩
    exact ⟨0, mem_scCoderivUnion_iff.2 ⟨L, hL, L.zero_mem⟩⟩

theorem hasSCDPropertyAround_iff_eventually :
    HasSCDPropertyAround F p ↔ ∀ᶠ q in 𝓝 p, q ∈ graph F → HasSCDPropertyAt F q := by
  constructor
  · rintro ⟨U, hU, h⟩
    filter_upwards [hU] with q hqU hq using h q ⟨hq, hqU⟩
  · intro h
    exact ⟨_, h, fun q hq ↦ hq.2 hq.1⟩

/-- Def. 2.11 of [Gfrerer–Outrata 2024] (semismoothness* with respect to `⋃ 𝒮*F`) agrees with SCD
semismoothness* [Gfrerer–Outrata 2022, Def. 5.1]. -/
theorem isSCDSemismoothStarAt_iff_wrt :
    IsSCDSemismoothStarAt F p ↔ IsSemismoothStarWrtAt (scCoderivUnion F) F p := by
  constructor
  · rintro ⟨hF, h⟩
    refine ⟨fun q w hw t _ ↦ scCoderivUnion_smul hw t, ?_, fun ε hε ↦ ?_⟩
    · filter_upwards [hasSCDPropertyAround_iff_eventually.1 hF] with q hq hgr
      exact scCoderivUnion_nonempty_iff.2 (hq hgr)
    · filter_upwards [h ε hε] with q hq hgr w hw
      obtain ⟨L, hL, hwL⟩ := mem_scCoderivUnion_iff.1 hw
      exact hq hgr L hL w hwL
  · rintro ⟨-, hdom, h⟩
    refine ⟨hasSCDPropertyAround_iff_eventually.2 ?_, fun ε hε ↦ ?_⟩
    · filter_upwards [hdom] with q hq hgr using scCoderivUnion_nonempty_iff.1 (hq hgr)
    · filter_upwards [h ε hε] with q hq hgr L hL w hw
      exact hq hgr w (mem_scCoderivUnion_iff.2 ⟨L, hL, hw⟩)

/-- Semismoothness* [Gfrerer–Outrata 2024, Def. 2.9] together with the SCD property around `p`
implies SCD semismoothness*, since `⋃ 𝒮*F(q) ⊆ gph D*F(q)` [Gfrerer–Outrata 2022, Lemma 3.7]. -/
theorem IsSemismoothStarAt.isSCDSemismoothStarAt (h : IsSemismoothStarAt F p)
    (hF : HasSCDPropertyAround F p) : IsSCDSemismoothStarAt F p := by
  refine isSCDSemismoothStarAt_iff_wrt.2 (IsSemismoothStarWrtAt.mono h
    (fun q w hw t _ ↦ scCoderivUnion_smul hw t) ?_ (Eventually.of_forall fun q hq w hw ↦ ?_))
  · filter_upwards [hasSCDPropertyAround_iff_eventually.1 hF] with q hq hgr
    exact scCoderivUnion_nonempty_iff.2 (hq hgr)
  · obtain ⟨L, hL, hwL⟩ := mem_scCoderivUnion_iff.1 hw
    exact toDual_mem_coderiv_of_mem_scCoderiv hq hL (y := w.1) (x := w.2) hwL

/-! ### The primal characterization -/

/-- If `w ∈ L*`, then `|⟪w.2, z.1⟫ - ⟪w.1, z.2⟫| ≤ 2 ‖w‖ dist(z, L)`. -/
theorem abs_pairing_le_infDist {L : Submodule ℝ (E × E)} {w : E × E}
    (hw : w ∈ adjointSubspace L) (z : E × E) :
    |⟪w.2, z.1⟫_ℝ - ⟪w.1, z.2⟫_ℝ| ≤ 2 * ‖w‖ * Metric.infDist z (L : Set (E × E)) := by
  obtain ⟨u, hu, hdist⟩ := (Submodule.closed_of_finiteDimensional L).exists_infDist_eq_dist
    ⟨0, L.zero_mem⟩ z
  have hwu := inner_eq_of_mem_adjointSubspace hw hu
  have key : ⟪w.2, z.1⟫_ℝ - ⟪w.1, z.2⟫_ℝ = ⟪w.2, (z - u).1⟫_ℝ - ⟪w.1, (z - u).2⟫_ℝ := by
    simp only [Prod.fst_sub, Prod.snd_sub, inner_sub_right, hwu]; ring
  rw [hdist, dist_eq_norm, key]
  have h1 : |⟪w.2, (z - u).1⟫_ℝ| ≤ ‖w‖ * ‖z - u‖ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (norm_snd_le w) (norm_fst_le _) (norm_nonneg _) (norm_nonneg _))
  have h2 : |⟪w.1, (z - u).2⟫_ℝ| ≤ ‖w‖ * ‖z - u‖ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (norm_fst_le w) (norm_snd_le _) (norm_nonneg _) (norm_nonneg _))
  calc |⟪w.2, (z - u).1⟫_ℝ - ⟪w.1, (z - u).2⟫_ℝ|
      ≤ |⟪w.2, (z - u).1⟫_ℝ| + |⟪w.1, (z - u).2⟫_ℝ| := abs_sub _ _
    _ ≤ 2 * ‖w‖ * ‖z - u‖ := by linarith

/-- Witness for the distance to a subspace: there are `w ∈ L*` and `ρ ≥ 0` with
`⟪w.2, z.1⟫ - ⟪w.1, z.2⟫ = ρ²`, `‖w‖ ≤ ρ` and `dist(z, L) ≤ ρ`. Here `ρ` is the Euclidean distance
from `z` to `L`, obtained from the orthogonal projection in `WithLp 2 (E × E)`. -/
theorem exists_mem_adjointSubspace_pairing_eq (L : Submodule ℝ (E × E)) (z : E × E) :
    ∃ w ∈ adjointSubspace L, ∃ ρ : ℝ, 0 ≤ ρ ∧ ⟪w.2, z.1⟫_ℝ - ⟪w.1, z.2⟫_ℝ = ρ ^ 2 ∧ ‖w‖ ≤ ρ ∧
      Metric.infDist z (L : Set (E × E)) ≤ ρ := by
  set K : Submodule ℝ (WithLp 2 (E × E)) :=
    L.map ((WithLp.linearEquiv 2 ℝ (E × E)).symm : (E × E) →ₗ[ℝ] WithLp 2 (E × E)) with hK
  have hmemK : ∀ k : WithLp 2 (E × E), k ∈ K ↔ WithLp.ofLp k ∈ L := by
    intro k
    rw [hK, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hk; exact ⟨WithLp.ofLp k, hk, rfl⟩
  set z' : WithLp 2 (E × E) := WithLp.toLp 2 z with hz'
  set P := K.starProjection z' with hP
  set r := z' - P with hr
  have hPK : P ∈ K := K.starProjection_apply_mem z'
  have hrK : r ∈ Kᗮ := K.sub_starProjection_mem_orthogonal z'
  refine ⟨(-r.snd, r.fst), ?_, ‖r‖, norm_nonneg _, ?_, ?_, ?_⟩
  · refine mem_adjointSubspace_iff.2 fun q hq ↦ ?_
    have hqK : WithLp.toLp 2 q ∈ K := (hmemK _).2 hq
    have h0 := Submodule.inner_right_of_mem_orthogonal hqK hrK
    rw [WithLp.prod_inner_apply] at h0
    simp only [WithLp.ofLp_fst, WithLp.ofLp_snd] at h0
    simp only [inner_neg_left]
    rw [real_inner_comm q.1 r.fst, real_inner_comm q.2 r.snd]
    linarith
  · have hrP : ⟪r, P⟫_ℝ = 0 := Submodule.inner_left_of_mem_orthogonal hPK hrK
    have hzrP : z' = r + P := by rw [hr]; abel
    have h1 : ⟪r, z'⟫_ℝ = ‖r‖ ^ 2 := by
      rw [hzrP, inner_add_right, hrP, add_zero, real_inner_self_eq_norm_sq]
    rw [WithLp.prod_inner_apply] at h1
    simp only [WithLp.ofLp_fst, WithLp.ofLp_snd, hz'] at h1
    simp only [inner_neg_left]
    linarith
  · rw [Prod.norm_def, norm_neg]
    exact max_le (WithLp.norm_snd_le (x := r)) (WithLp.norm_fst_le (x := r))
  · have hPL : WithLp.ofLp P ∈ L := (hmemK P).1 hPK
    refine (Metric.infDist_le_dist_of_mem (SetLike.mem_coe.2 hPL)).trans ?_
    rw [dist_eq_norm, Prod.norm_def]
    have e1 : (z - WithLp.ofLp P).1 = r.fst := rfl
    have e2 : (z - WithLp.ofLp P).2 = r.snd := rfl
    rw [e1, e2]
    exact max_le (WithLp.norm_fst_le (x := r)) (WithLp.norm_snd_le (x := r))

/-- Prop. 2.12 of [Gfrerer–Outrata 2024] (primal form of SCD semismoothness*): if `F` has the SCD
property around `p`, then `F` is SCD semismooth* at `p` iff for every `ε > 0`,
`dist((x, y) - p, L) ≤ ε ‖(x, y) - p‖` for all `(x, y) ∈ gph F` near `p` and all
`L ∈ 𝒮F(x, y)`. -/
theorem isSCDSemismoothStarAt_iff_infDist (hF : HasSCDPropertyAround F p) :
    IsSCDSemismoothStarAt F p ↔ ∀ ε > 0, ∀ᶠ q in 𝓝 p, q ∈ graph F → ∀ L ∈ scDeriv F q,
      Metric.infDist (q - p) (L : Set (E × E)) ≤ ε * ‖q - p‖ := by
  constructor
  · intro h ε hε
    filter_upwards [h.2 ε hε] with q hq hgr L hL
    have hL' : adjointSubspace L ∈ scCoderiv F q :=
      mem_scCoderiv_iff_adjoint_mem_scDeriv.2 (by rwa [adjointSubspace_adjointSubspace])
    obtain ⟨w, hw, ρ, hρ, hpair, hwρ, hdist⟩ := exists_mem_adjointSubspace_pairing_eq L (q - p)
    have hss := hq hgr _ hL' w hw
    simp only [Prod.fst_sub, Prod.snd_sub] at hpair
    rw [hpair, abs_of_nonneg (sq_nonneg ρ)] at hss
    have hεq : 0 ≤ ε * ‖q - p‖ := mul_nonneg hε.le (norm_nonneg _)
    have hρle : ρ ≤ ε * ‖q - p‖ := by
      rcases hρ.eq_or_lt with h0 | hpos
      · rw [← h0]; exact hεq
      · have : ρ ^ 2 ≤ ε * ‖q - p‖ * ρ :=
          hss.trans (mul_le_mul_of_nonneg_left hwρ hεq)
        nlinarith
    exact hdist.trans hρle
  · intro h
    refine ⟨hF, fun ε hε ↦ ?_⟩
    filter_upwards [h (ε / 2) (half_pos hε)] with q hq hgr L hL w hw
    obtain ⟨L₀, hL₀, rfl⟩ := hL
    have h1 := abs_pairing_le_infDist hw (q - p)
    simp only [Prod.fst_sub, Prod.snd_sub] at h1
    have h2 := hq hgr L₀ hL₀
    calc |⟪w.2, q.1 - p.1⟫_ℝ - ⟪w.1, q.2 - p.2⟫_ℝ|
        ≤ 2 * ‖w‖ * Metric.infDist (q - p) (L₀ : Set (E × E)) := h1
      _ ≤ 2 * ‖w‖ * (ε / 2 * ‖q - p‖) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ε * ‖q - p‖ * ‖w‖ := by ring

end VariationalAnalysis
