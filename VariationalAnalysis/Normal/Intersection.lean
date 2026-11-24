/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import VariationalAnalysis.Extremal.Basic
import VariationalAnalysis.SetValued.Basic

/-!
# Normals to intersections and sums of sets

The basic intersection rule [Mordukhovich 2018, Thm. 2.16]: for sets locally closed around
`x₀` in finite dimensions, under the normal qualification condition
`N(x₀; Ω₁) ∩ (-N(x₀; Ω₂)) = {0}` (2.26),

  `N(x₀; Ω₁ ∩ Ω₂) ⊆ N(x₀; Ω₁) + N(x₀; Ω₂)`  (2.27),

with equality and normal regularity of `Ω₁ ∩ Ω₂` when both sets are normally regular. The proof
follows the book: the extremal principle (Thm. 2.3) is applied in `E × ℝ` to `Ω₁ × ℝ₊` and the
sets `Λ₂ₖ` of (2.28) built from regular normals `vₖ` to the intersection at `xₖ → x₀`; the
normals to `Λ₂ₖ` are turned into `ω`-normals to `Ω₂` (with `ω → 0`), and the limits are taken
with Prop. 1.3, Prop. 1.4 and both representations in Thm. 1.6.

Sums of sets are pointwise sums (`open scoped Pointwise`): `A + B = {a + b | a ∈ A, b ∈ B}`.

## Main results

* `regularNormalCone_add_subset_inter`: `N̂(x₀; Ω₁) + N̂(x₀; Ω₂) ⊆ N̂(x₀; Ω₁ ∩ Ω₂)`.
* `normalCone_inter_subset`: Thm. 2.16 of [Mordukhovich 2018] (basic intersection rule), (2.27).
* `normalCone_inter_eq`: Thm. 2.16, equality and normal regularity for normally regular sets.
* `normalCone_iInter_subset`, `normalCone_iInter_eq`: Cor. 2.17 of [Mordukhovich 2018]
  (normals to finite intersections).
* `normalCone_add_subset`: Cor. 2.18 of [Mordukhovich 2018] (normals to sums of sets).
-/

open Filter Topology Set Metric
open scoped Pointwise

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Regular

variable {Ω₁ Ω₂ : Set E} {x₀ : E}

/-- [Mordukhovich 2018, proof of Thm. 2.16]: the inclusion
`N̂(x₀; Ω₁) + N̂(x₀; Ω₂) ⊆ N̂(x₀; Ω₁ ∩ Ω₂)` always holds. -/
theorem regularNormalCone_add_subset_inter :
    regularNormalCone Ω₁ x₀ + regularNormalCone Ω₂ x₀ ⊆ regularNormalCone (Ω₁ ∩ Ω₂) x₀ := by
  rintro _ ⟨u, hu, w, hw, rfl⟩
  have hx : x₀ ∈ Ω₁ ∩ Ω₂ := ⟨hu.1, hw.1⟩
  exact add_mem_regularNormalCone (regularNormalCone_anti inter_subset_left hx hu)
    (regularNormalCone_anti inter_subset_right hx hw)

end Regular

section Auxiliary

/-! ### The sets `Λ₂` of (2.28) -/

variable {Ω₂ : Set E} {x : E} {w : StrongDual ℝ E} {ε : ℝ}

/-- The set `Λ₂ = {(y, α) | y ∈ Ω₂, α ≤ ⟨w, y - x⟩ - ε ‖y - x‖}` of [Mordukhovich 2018, (2.28)]. -/
def interAuxSet (Ω₂ : Set E) (x : E) (w : StrongDual ℝ E) (ε : ℝ) : Set (E × ℝ) :=
  {p | p.1 ∈ Ω₂ ∧ p.2 ≤ w (p.1 - x) - ε * ‖p.1 - x‖}

/-- `m (a, b) = m (a, 0) + b m (0, 1)` for a dual element on `E × ℝ`. -/
theorem dual_prod_apply (m : StrongDual ℝ (E × ℝ)) (a : E) (b : ℝ) :
    m (a, b) = m.comp (ContinuousLinearMap.inl ℝ E ℝ) a + b * m (0, 1) := by
  rw [show ((a, b) : E × ℝ) = (a, 0) + b • ((0 : E), (1 : ℝ)) by simp, map_add, map_smul,
    smul_eq_mul]
  rfl

/-- `|m (0, 1)| ≤ ‖m‖` on `E × ℝ`. -/
theorem abs_apply_zero_one_le (m : StrongDual ℝ (E × ℝ)) : |m (0, 1)| ≤ ‖m‖ := by
  have := m.le_opNorm ((0 : E), (1 : ℝ))
  simpa [Prod.norm_def] using this

/-- `‖m ∘ inl‖ ≤ ‖m‖` on `E × ℝ`. -/
theorem norm_comp_inl_le (m : StrongDual ℝ (E × ℝ)) :
    ‖m.comp (ContinuousLinearMap.inl ℝ E ℝ)‖ ≤ ‖m‖ :=
  (m.opNorm_comp_le _).trans (mul_le_of_le_one_right (norm_nonneg _)
    (ContinuousLinearMap.norm_inl_le_one ℝ E ℝ))

/-- [Mordukhovich 2018, proof of Thm. 2.16, (2.31)]: a regular normal `m` to `Λ₂` at `(y, β)`
has `m (0, 1) ≥ 0`, and `m ∘ inl + m (0, 1) w` is an `ω`-normal to `Ω₂` at `y` with
`ω = m (0, 1) ε`. -/
theorem mem_epsNormalCone_of_mem_regularNormalCone_interAuxSet (hε : 0 ≤ ε) {p : E × ℝ}
    {m : StrongDual ℝ (E × ℝ)} (hm : m ∈ regularNormalCone (interAuxSet Ω₂ x w ε) p) :
    0 ≤ m (0, 1) ∧ m.comp (ContinuousLinearMap.inl ℝ E ℝ) + m (0, 1) • w ∈
      epsNormalCone (m (0, 1) * ε) Ω₂ p.1 := by
  obtain ⟨⟨hpΩ, hpg⟩, hreg⟩ := hm
  set g : E → ℝ := fun y ↦ w (y - x) - ε * ‖y - x‖ with hg_def
  set q := m (0, 1)
  -- the vertical ray `p - t (0, 1)` stays in `Λ₂`
  have hq : 0 ≤ q := by
    have hray : ∀ᶠ t in 𝓝[>] (0 : ℝ), p + t • ((0 : E), (-1 : ℝ)) ∈ interAuxSet Ω₂ x w ε := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      refine ⟨by simpa using hpΩ, ?_⟩
      simp only [Prod.fst_add, Prod.smul_mk, smul_zero, add_zero, Prod.snd_add, smul_eq_mul,
        mul_neg, mul_one]
      have : (0 : ℝ) < t := ht
      linarith
    have h1 : m ((0 : E), (-1 : ℝ)) ≤ 0 := le_of_forall_pos_le_add_mul (c := 1) fun δ hδ ↦ by
      simpa using le_of_eventually_ray (hreg δ hδ) hray
    have h2 : m ((0 : E), (-1 : ℝ)) = -q := by
      rw [show ((0 : E), (-1 : ℝ)) = -((0 : E), (1 : ℝ)) by simp, map_neg]
    linarith
  refine ⟨hq, hpΩ, fun η hη ↦ ?_⟩
  set C := ‖w‖ + ε + 1
  have hC : 0 < C := by positivity
  -- lifting `y ↦ (y, p.2 + g y - g p.1)` maps `Ω₂` into `Λ₂`
  set h : E → E × ℝ := fun y ↦ (y, p.2 + (g y - g p.1))
  have hgc : Continuous g := by
    simp only [hg_def]; fun_prop
  have hh : Tendsto h (𝓝[Ω₂] p.1) (𝓝[interAuxSet Ω₂ x w ε] p) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun y hy ↦ ?_⟩
    · have : Continuous h := continuous_id.prodMk (continuous_const.add (hgc.sub continuous_const))
      have h0 : h p.1 = p := by simp [h]
      exact h0 ▸ (this.tendsto p.1).mono_left nhdsWithin_le_nhds
    · refine ⟨hy, ?_⟩
      simp only [h]
      linarith
  filter_upwards [hh.eventually (hreg (η / C) (div_pos hη hC)), self_mem_nhdsWithin] with y hy hyΩ
  rw [show ((y, p.2 + (g y - g p.1)) : E × ℝ) - p = (y - p.1, g y - g p.1) by
    ext <;> simp, dual_prod_apply] at hy
  set d := y - p.1
  have hg1 : g y - g p.1 = w d - ε * (‖y - x‖ - ‖p.1 - x‖) := by
    simp only [hg_def, d, map_sub]; ring
  have hnorm : |‖y - x‖ - ‖p.1 - x‖| ≤ ‖d‖ := by
    have := abs_norm_sub_norm_le (y - x) (p.1 - x)
    rwa [sub_sub_sub_cancel_right] at this
  have hwd : |w d| ≤ ‖w‖ * ‖d‖ := w.le_opNorm d |>.trans' (le_of_eq (Real.norm_eq_abs _).symm)
  have hgd : |g y - g p.1| ≤ (‖w‖ + ε) * ‖d‖ := by
    rw [hg1]
    calc |w d - ε * (‖y - x‖ - ‖p.1 - x‖)| ≤ |w d| + |ε * (‖y - x‖ - ‖p.1 - x‖)| :=
          abs_sub _ _
      _ ≤ ‖w‖ * ‖d‖ + ε * ‖d‖ := by
          rw [abs_mul, abs_of_nonneg hε]
          gcongr
      _ = (‖w‖ + ε) * ‖d‖ := by ring
  have hmax : ‖((d, g y - g p.1) : E × ℝ)‖ ≤ C * ‖d‖ := by
    rw [Prod.norm_def, max_le_iff]
    constructor
    · nlinarith [norm_nonneg d, norm_nonneg w]
    · rw [Real.norm_eq_abs]; nlinarith [norm_nonneg d]
  have hlow : q * (w d - ε * ‖d‖) ≤ q * (g y - g p.1) := by
    apply mul_le_mul_of_nonneg_left _ hq
    rw [hg1]
    nlinarith [le_abs_self (‖y - x‖ - ‖p.1 - x‖)]
  have hup : η / C * ‖((d, g y - g p.1) : E × ℝ)‖ ≤ η * ‖d‖ := by
    calc η / C * ‖((d, g y - g p.1) : E × ℝ)‖ ≤ η / C * (C * ‖d‖) := by gcongr
      _ = η * ‖d‖ := by field_simp
  simp only [add_apply, smul_apply, smul_eq_mul]
  nlinarith


/-- [Mordukhovich 2018, proof of Thm. 2.16], one step. Let `x ∈ Ω₁ ∩ Ω₂` with both sets locally
closed around `x`, `w ∈ N̂(x; Ω₁ ∩ Ω₂)` and `ε, δ > 0`. The extremal principle applied to the
extremal system `{Ω₁ × ℝ₊, Λ₂, (x, 0)}` of (2.28) gives `ℓ = (u, λ)` with `‖ℓ‖ = 1`,
`u ∈ N(x; Ω₁)`, `λ ≤ 0`, and an `ω`-normal `z ∈ N̂_{2ε}(y; Ω₂)` at some `y ∈ Ω₂` near `x` with
`z` close to `-u - λ w`. -/
theorem exists_approx_normal_inter [FiniteDimensional ℝ E] {Ω₁ : Set E} (hx₁ : x ∈ Ω₁)
    (hx₂ : x ∈ Ω₂) (hloc₁ : ∃ r > 0, IsClosed (Ω₁ ∩ closedBall x r))
    (hloc₂ : ∃ r > 0, IsClosed (Ω₂ ∩ closedBall x r)) (hw : w ∈ regularNormalCone (Ω₁ ∩ Ω₂) x)
    (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ℓ : StrongDual ℝ (E × ℝ), ‖ℓ‖ = 1 ∧ ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ) ∈ normalCone Ω₁ x ∧
      ℓ (0, 1) ≤ 0 ∧ ∃ y ∈ Ω₂, ‖y - x‖ < δ ∧ ∃ z ∈ epsNormalCone (2 * ε) Ω₂ y,
        ‖z + ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ) + ℓ (0, 1) • w‖ < δ := by
  set Λ₁ : Set (E × ℝ) := Ω₁ ×ˢ Ici 0
  set Λ₂ := interAuxSet Ω₂ x w ε
  have hΛ₁ : ((x, 0) : E × ℝ) ∈ Λ₁ := ⟨hx₁, self_mem_Ici⟩
  have hΛ₂ : ((x, 0) : E × ℝ) ∈ Λ₂ := ⟨hx₂, by simp⟩
  -- `(x, 0)` is a locally extremal point of `{Λ₁, Λ₂}`
  have hext : IsLocallyExtremal ![Λ₁, Λ₂] ((x, 0) : E × ℝ) := by
    have hV := eventually_nhdsWithin_iff.1 (hw.2 ε hε)
    refine isLocallyExtremal_pair_iff.2 ⟨hΛ₁, hΛ₂, fun k ↦ ((0 : E), 1 / ((k : ℝ) + 1)),
      ?_, Prod.fst ⁻¹' {y | y ∈ Ω₁ ∩ Ω₂ → w (y - x) ≤ ε * ‖y - x‖},
      continuous_fst.continuousAt.preimage_mem_nhds hV, Eventually.of_forall ?_⟩
    · have : Tendsto (fun k : ℕ ↦ ((0 : E), 1 / ((k : ℝ) + 1))) atTop (𝓝 ((0 : E), (0 : ℝ))) :=
        tendsto_const_nhds.prodMk_nhds tendsto_one_div_add_atTop_nhds_zero_nat
      rwa [Prod.mk_zero_zero] at this
    · rintro k ⟨y, α⟩ hU ⟨hy₁, hα⟩ hmem₂
      simp only [mem_preimage, mem_ofPred_eq] at hU
      obtain ⟨hy₂, hle⟩ := hmem₂
      simp only [Prod.fst_add, Prod.snd_add, add_zero] at hy₂ hle
      have h1 := hU ⟨hy₁, hy₂⟩
      have h2 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := Nat.one_div_pos_of_nat
      have h3 : (0 : ℝ) ≤ α := hα
      linarith
  have hlocΛ₁ : ∃ r > 0, IsClosed (Λ₁ ∩ closedBall ((x, 0) : E × ℝ) r) :=
    locallyClosed_prod hloc₁ ⟨1, one_pos, isClosed_Ici.inter isClosed_closedBall⟩
  have hlocΛ₂ : ∃ r > 0, IsClosed (Λ₂ ∩ closedBall ((x, 0) : E × ℝ) r) := by
    obtain ⟨r, hr, hcl⟩ := hloc₂
    refine ⟨r, hr, ?_⟩
    have : Λ₂ ∩ closedBall ((x, 0) : E × ℝ) r = ((Ω₂ ∩ closedBall x r) ×ˢ closedBall 0 r) ∩
        {p | p.2 ≤ w (p.1 - x) - ε * ‖p.1 - x‖} := by
      rw [← closedBall_prod_same]
      ext p
      simp only [Λ₂, interAuxSet, mem_inter_iff, mem_prod, mem_ofPred_eq]
      tauto
    rw [this]
    exact (hcl.prod isClosed_closedBall).inter (isClosed_le continuous_snd (by fun_prop))
  -- the extremal principle (2.29)
  obtain ⟨ℓ, hℓ₁, hℓ₂, hℓ⟩ := hext.exists_mem_normalCone_pair hlocΛ₁ hlocΛ₂
  obtain ⟨hu, hlam⟩ := mem_normalCone_prod_iff.1 hℓ₁
  have hlam' : ℓ (0, 1) ≤ 0 := by
    have := (mem_normalCone_of_convex (convex_Ici (0 : ℝ)) self_mem_Ici).1 hlam 1
      (by norm_num : (1 : ℝ) ∈ Ici 0)
    simpa using this
  refine ⟨ℓ, hℓ, hu, hlam', ?_⟩
  -- regular normals to `Λ₂` near `(x, 0)` approximating `-ℓ`
  obtain ⟨-, a, m, ha, hm, hmem⟩ := hℓ₂
  have ha' := tendsto_nhdsWithin_iff.1 ha
  set η := min 1 (δ / (‖w‖ + 1))
  have hη : 0 < η := lt_min one_pos (div_pos hδ (by positivity))
  obtain ⟨k, hk₁, hk₂⟩ := (((tendsto_iff_norm_sub_tendsto_zero.1 ha'.1).eventually
    (gt_mem_nhds hδ)).and ((tendsto_iff_norm_sub_tendsto_zero.1 hm).eventually
    (gt_mem_nhds hη))).exists
  rw [sub_neg_eq_add] at hk₂
  obtain ⟨hq, hz⟩ := mem_epsNormalCone_of_mem_regularNormalCone_interAuxSet hε.le (hmem k)
  set q := m k (0, 1)
  have hq2 : q ≤ 2 := by
    have h1 := abs_apply_zero_one_le (m k + ℓ)
    have h2 := abs_apply_zero_one_le ℓ
    rw [hℓ] at h2
    simp only [add_apply] at h1
    have h3 : ‖m k + ℓ‖ ≤ 1 := hk₂.le.trans (min_le_left _ _)
    rw [abs_le] at h1 h2
    linarith
  refine ⟨(a k).1, (hmem k).1.1, ?_, _, epsNormalCone_mono (by nlinarith) hz, ?_⟩
  · calc ‖(a k).1 - x‖ = ‖(a k - (x, 0)).1‖ := by simp
      _ ≤ ‖a k - (x, 0)‖ := norm_fst_le _
      _ < δ := hk₁
  · have heq : (m k).comp (ContinuousLinearMap.inl ℝ E ℝ) + q • w +
        ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ) + ℓ (0, 1) • w =
        (m k + ℓ).comp (ContinuousLinearMap.inl ℝ E ℝ) + (m k + ℓ) (0, 1) • w := by
      simp only [ContinuousLinearMap.add_comp, add_apply, add_smul, q]
      abel
    rw [heq]
    have h1 := norm_comp_inl_le (m k + ℓ)
    have h2 := abs_apply_zero_one_le (m k + ℓ)
    have h3 : ‖m k + ℓ‖ * (‖w‖ + 1) < δ := by
      have := hk₂.trans_le (min_le_right _ _)
      rwa [lt_div_iff₀ (by positivity)] at this
    calc ‖(m k + ℓ).comp (ContinuousLinearMap.inl ℝ E ℝ) + (m k + ℓ) (0, 1) • w‖
        ≤ ‖(m k + ℓ).comp (ContinuousLinearMap.inl ℝ E ℝ)‖ + |(m k + ℓ) (0, 1)| * ‖w‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖m k + ℓ‖ + ‖m k + ℓ‖ * ‖w‖ := by gcongr
      _ < δ := by linarith

end Auxiliary

section IntersectionRule

variable [FiniteDimensional ℝ E] {Ω₁ Ω₂ : Set E} {x₀ : E}

/-- Thm. 2.16 of [Mordukhovich 2018] (basic intersection rule), (2.27): if `Ω₁, Ω₂` are locally
closed around `x₀` and the normal qualification condition (2.26)
`N(x₀; Ω₁) ∩ (-N(x₀; Ω₂)) = {0}` holds, then `N(x₀; Ω₁ ∩ Ω₂) ⊆ N(x₀; Ω₁) + N(x₀; Ω₂)`. -/
theorem normalCone_inter_subset (hloc₁ : ∃ r > 0, IsClosed (Ω₁ ∩ closedBall x₀ r))
    (hloc₂ : ∃ r > 0, IsClosed (Ω₂ ∩ closedBall x₀ r))
    (hqc : ∀ v ∈ normalCone Ω₁ x₀, -v ∈ normalCone Ω₂ x₀ → v = 0) :
    normalCone (Ω₁ ∩ Ω₂) x₀ ⊆ normalCone Ω₁ x₀ + normalCone Ω₂ x₀ := by
  rintro v ⟨hx, a, w, ha, hw, hmem⟩
  have ha' := tendsto_nhdsWithin_iff.1 ha
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ha'.2.and ((ha'.1.eventually
    (eventually_locallyClosed hloc₁)).and (ha'.1.eventually (eventually_locallyClosed hloc₂))))
  have key : ∀ k : ℕ, ∃ ℓ : StrongDual ℝ (E × ℝ), ‖ℓ‖ = 1 ∧
      ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ) ∈ normalCone Ω₁ (a (k + N)) ∧ ℓ (0, 1) ≤ 0 ∧
      ∃ y ∈ Ω₂, ‖y - a (k + N)‖ < 1 / ((k : ℝ) + 1) ∧
        ∃ z ∈ epsNormalCone (2 * (1 / ((k : ℝ) + 1))) Ω₂ y,
          ‖z + ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ) + ℓ (0, 1) • w (k + N)‖ <
            1 / ((k : ℝ) + 1) := fun k ↦ by
    obtain ⟨hmemΩ, hl₁, hl₂⟩ := hN (k + N) (Nat.le_add_left _ _)
    exact exists_approx_normal_inter hmemΩ.1 hmemΩ.2 hl₁ hl₂ (hmem _) Nat.one_div_pos_of_nat
      Nat.one_div_pos_of_nat
  choose ℓ hℓ₁ hu hlam y hyΩ hyx z hz hzest using key
  -- compactness of the unit sphere in the dual of `E × ℝ`
  obtain ⟨ℓ₀, hℓ₀, φ, hφ, hlim⟩ := (isCompact_sphere (0 : StrongDual ℝ (E × ℝ)) 1).tendsto_subseq
    (x := ℓ) fun k ↦ by simpa using hℓ₁ k
  have hφ' := hφ.tendsto_atTop
  have hN' : Tendsto (fun k ↦ φ k + N) atTop atTop := (tendsto_add_atTop_nat N).comp hφ'
  set u₀ := ℓ₀.comp (ContinuousLinearMap.inl ℝ E ℝ)
  set lam₀ := ℓ₀ (0, 1)
  have hinl : Tendsto (fun k ↦ (ℓ (φ k)).comp (ContinuousLinearMap.inl ℝ E ℝ)) atTop (𝓝 u₀) :=
    tendsto_comp_inl hlim
  have hlamlim : Tendsto (fun k ↦ ℓ (φ k) (0, 1)) atTop (𝓝 lam₀) :=
    tendsto_dual_apply hlim tendsto_const_nhds
  have hr : Tendsto (fun k : ℕ ↦ 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ'
  -- `u₀ ∈ N(x₀; Ω₁)` by robustness (Prop. 1.3)
  have hu₀ : u₀ ∈ normalCone Ω₁ x₀ := by
    rw [normalCone_eq_outerLimit_normalCone hx.1]
    exact ⟨fun k ↦ a (φ k + N), fun k ↦ (ℓ (φ k)).comp (ContinuousLinearMap.inl ℝ E ℝ),
      tendsto_nhdsWithin_iff.2 ⟨ha'.1.comp hN', Eventually.of_forall fun k ↦
        (hN _ (Nat.le_add_left _ _)).1.1⟩, hinl, fun k ↦ hu (φ k)⟩
  have hlam₀ : lam₀ ≤ 0 := le_of_tendsto' hlamlim fun k ↦ hlam (φ k)
  -- `-u₀ - lam₀ v ∈ N(x₀; Ω₂)` by the `ω`-representation (Thm. 1.6)
  have hz₀ : -u₀ - lam₀ • v ∈ normalCone Ω₂ x₀ := by
    rw [normalCone_eq_outerLimit_epsNormalCone hx.2 hloc₂]
    have hy : Tendsto (fun k ↦ y (φ k)) atTop (𝓝 x₀) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h1 := tendsto_iff_norm_sub_tendsto_zero.1 (ha'.1.comp hN')
      refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ ?_) (by simpa using hr.add h1)
      have : y (φ k) - x₀ = (y (φ k) - a (φ k + N)) + (a (φ k + N) - x₀) := by abel
      rw [this]
      have h2 := hyx (φ k)
      rw [one_div] at h2
      exact (norm_add_le _ _).trans (by linarith)
    have hzlim : Tendsto (fun k ↦ z (φ k)) atTop (𝓝 (-u₀ - lam₀ • v)) := by
      have h0 : Tendsto (fun k ↦ z (φ k) + (ℓ (φ k)).comp (ContinuousLinearMap.inl ℝ E ℝ) +
          ℓ (φ k) (0, 1) • w (φ k + N)) atTop (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ (hzest (φ k)).le) hr
      have := (h0.sub hinl).sub (hlamlim.smul (hw.comp hN'))
      simp only [zero_sub] at this
      refine this.congr fun k ↦ ?_
      simp only [Function.comp_apply]
      abel
    refine ⟨fun k ↦ (y (φ k), 2 * (1 / ((φ k : ℝ) + 1))), fun k ↦ z (φ k), ?_, hzlim,
      fun k ↦ hz (φ k)⟩
    refine (tendsto_nhdsWithin_iff.2 ⟨hy, Eventually.of_forall fun k ↦ hyΩ (φ k)⟩).prodMk
      (tendsto_nhdsWithin_iff.2 ⟨by simpa using hr.const_mul 2, Eventually.of_forall
        fun k ↦ ?_⟩)
    exact mem_Ici.2 (by positivity)
  -- `lam₀ < 0` by the qualification condition (2.26)
  have hlamneg : lam₀ < 0 := by
    refine lt_of_le_of_ne hlam₀ fun h0 ↦ ?_
    have hu0 : u₀ = 0 := hqc u₀ hu₀ (by simpa [h0] using hz₀)
    have : ℓ₀ = 0 := by
      rw [eq_coprod_zero ℓ₀ h0]
      change u₀.coprod 0 = 0
      rw [hu0]; ext <;> simp
    rw [mem_sphere_zero_iff_norm, this, norm_zero] at hℓ₀
    exact zero_ne_one hℓ₀
  set μ := -lam₀
  have hμ : 0 < μ := neg_pos.2 hlamneg
  refine ⟨μ⁻¹ • u₀, smul_mem_normalCone hu₀ (inv_nonneg.2 hμ.le), μ⁻¹ • (-u₀ - lam₀ • v),
    smul_mem_normalCone hz₀ (inv_nonneg.2 hμ.le), ?_⟩
  change μ⁻¹ • u₀ + μ⁻¹ • (-u₀ - lam₀ • v) = v
  ext y
  simp only [add_apply, smul_apply, sub_apply, neg_apply, smul_eq_mul, μ]
  have hl0 : lam₀ ≠ 0 := hlamneg.ne
  field_simp
  ring

/-- Thm. 2.16 of [Mordukhovich 2018], second part: if moreover `Ω₁` and `Ω₂` are normally regular
at `x₀`, then (2.27) holds as an equality and `Ω₁ ∩ Ω₂` is normally regular at `x₀`. -/
theorem normalCone_inter_eq (hloc₁ : ∃ r > 0, IsClosed (Ω₁ ∩ closedBall x₀ r))
    (hloc₂ : ∃ r > 0, IsClosed (Ω₂ ∩ closedBall x₀ r))
    (hqc : ∀ v ∈ normalCone Ω₁ x₀, -v ∈ normalCone Ω₂ x₀ → v = 0)
    (hr₁ : NormallyRegularAt Ω₁ x₀) (hr₂ : NormallyRegularAt Ω₂ x₀) :
    normalCone (Ω₁ ∩ Ω₂) x₀ = normalCone Ω₁ x₀ + normalCone Ω₂ x₀ ∧
      NormallyRegularAt (Ω₁ ∩ Ω₂) x₀ := by
  have h1 := normalCone_inter_subset hloc₁ hloc₂ hqc
  have h2 : normalCone Ω₁ x₀ + normalCone Ω₂ x₀ ⊆ regularNormalCone (Ω₁ ∩ Ω₂) x₀ := by
    rw [hr₁, hr₂]; exact regularNormalCone_add_subset_inter
  exact ⟨subset_antisymm h1 (h2.trans regularNormalCone_subset_normalCone),
    subset_antisymm (h1.trans h2) regularNormalCone_subset_normalCone⟩

end IntersectionRule

section FiniteIntersection

/-! ### Finite intersections -/

variable {ι : Type*} {Ω : ι → Set E} {x₀ : E}

omit [NormedSpace ℝ E] in
/-- A finite intersection of sets locally closed around `x₀` is locally closed around `x₀`. -/
theorem locallyClosed_biInter (s : Finset ι)
    (hloc : ∀ i ∈ s, ∃ r > 0, IsClosed (Ω i ∩ closedBall x₀ r)) :
    ∃ r > 0, IsClosed ((⋂ i ∈ s, Ω i) ∩ closedBall x₀ r) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simpa using isClosed_closedBall⟩
  | insert j s hj ih =>
    rw [Finset.set_biInter_insert]
    exact locallyClosed_inter (hloc j (Finset.mem_insert_self _ _))
      (ih fun i hi ↦ hloc i (Finset.mem_insert_of_mem hi))

/-- Cor. 2.17 of [Mordukhovich 2018], regular normals: `∑ᵢ N̂(x₀; Ωᵢ) ⊆ N̂(x₀; ⋂ᵢ Ωᵢ)` for
finitely many sets. -/
theorem sum_regularNormalCone_subset_biInter (s : Finset ι) :
    ∑ i ∈ s, regularNormalCone (Ω i) x₀ ⊆ regularNormalCone (⋂ i ∈ s, Ω i) x₀ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro v hv
    rw [Finset.sum_empty, Set.mem_zero] at hv
    simpa [hv] using zero_mem_regularNormalCone (mem_univ x₀)
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.set_biInter_insert]
    exact (Set.add_subset_add_left ih).trans regularNormalCone_add_subset_inter

variable [FiniteDimensional ℝ E]

/-- Cor. 2.17 of [Mordukhovich 2018] over a finset `s`: if the sets `Ωᵢ`, `i ∈ s`, are locally
closed around `x₀` and the system `vᵢ ∈ N(x₀; Ωᵢ)`, `∑_{i ∈ s} vᵢ = 0` has only the trivial
solution, then `N(x₀; ⋂_{i ∈ s} Ωᵢ) ⊆ ∑_{i ∈ s} N(x₀; Ωᵢ)`. -/
theorem normalCone_biInter_subset (s : Finset ι)
    (hloc : ∀ i ∈ s, ∃ r > 0, IsClosed (Ω i ∩ closedBall x₀ r))
    (hqc : ∀ v : ι → StrongDual ℝ E, (∀ i ∈ s, v i ∈ normalCone (Ω i) x₀) →
      ∑ i ∈ s, v i = 0 → ∀ i ∈ s, v i = 0) :
    normalCone (⋂ i ∈ s, Ω i) x₀ ⊆ ∑ i ∈ s, normalCone (Ω i) x₀ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro v hv
    have h0 : (⋂ i ∈ (∅ : Finset ι), Ω i) = univ := by simp
    rw [h0, normalCone_of_mem_interior (by simp)] at hv
    rw [Finset.sum_empty, Set.mem_zero]
    exact hv
  | insert j s hj ih =>
    intro v hv
    have hx : x₀ ∈ Ω j ∧ x₀ ∈ ⋂ i ∈ s, Ω i := by
      have := hv.1
      rwa [Finset.set_biInter_insert] at this
    -- the qualification condition for the subsystem `s`
    have hqc' : ∀ v : ι → StrongDual ℝ E, (∀ i ∈ s, v i ∈ normalCone (Ω i) x₀) →
        ∑ i ∈ s, v i = 0 → ∀ i ∈ s, v i = 0 := by
      intro w hw hsum i hi
      have hne : i ≠ j := fun h ↦ hj (h ▸ hi)
      have := hqc (Function.update w j 0) (fun k hk ↦ by
        rcases Finset.mem_insert.1 hk with rfl | hks
        · simpa using zero_mem_normalCone hx.1
        · rw [Function.update_of_ne (fun h ↦ hj (by rwa [h] at hks))]; exact hw k hks)
        (by rw [Finset.sum_insert hj, Function.update_self, zero_add,
          Finset.sum_update_of_notMem hj, hsum]) i (Finset.mem_insert_of_mem hi)
      rwa [Function.update_of_ne hne] at this
    have hIH := ih (fun i hi ↦ hloc i (Finset.mem_insert_of_mem hi)) hqc'
    -- the qualification condition (2.26) for `Ω j` and `⋂_{i ∈ s} Ωᵢ`
    have hqc₂ : ∀ u ∈ normalCone (Ω j) x₀, -u ∈ normalCone (⋂ i ∈ s, Ω i) x₀ → u = 0 := by
      intro u hu hu'
      obtain ⟨g, hg, hgsum⟩ := (Set.mem_finsetSum _ _ _).1 (hIH hu')
      have := hqc (Function.update g j u) (fun k hk ↦ by
        rcases Finset.mem_insert.1 hk with rfl | hks
        · simpa using hu
        · rw [Function.update_of_ne (fun h ↦ hj (by rwa [h] at hks))]; exact hg hks)
        (by rw [Finset.sum_insert hj, Function.update_self, Finset.sum_update_of_notMem hj,
          hgsum, add_neg_cancel]) j (Finset.mem_insert_self _ _)
      simpa using this
    rw [Finset.set_biInter_insert] at hv
    rw [Finset.sum_insert hj]
    exact Set.add_subset_add_left hIH (normalCone_inter_subset
      (hloc j (Finset.mem_insert_self _ _))
      (locallyClosed_biInter s fun i hi ↦ hloc i (Finset.mem_insert_of_mem hi)) hqc₂ hv)

/-- Cor. 2.17 of [Mordukhovich 2018] (normals to finite set intersections), (2.32): if finitely
many sets `Ωᵢ` are locally closed around `x₀` and the system `vᵢ ∈ N(x₀; Ωᵢ)`, `∑ vᵢ = 0` has
only the trivial solution, then `N(x₀; ⋂ᵢ Ωᵢ) ⊆ ∑ᵢ N(x₀; Ωᵢ)`. -/
theorem normalCone_iInter_subset [Fintype ι]
    (hloc : ∀ i, ∃ r > 0, IsClosed (Ω i ∩ closedBall x₀ r))
    (hqc : ∀ v : ι → StrongDual ℝ E, (∀ i, v i ∈ normalCone (Ω i) x₀) → ∑ i, v i = 0 →
      ∀ i, v i = 0) :
    normalCone (⋂ i, Ω i) x₀ ⊆ ∑ i, normalCone (Ω i) x₀ := by
  have := normalCone_biInter_subset (Ω := Ω) (x₀ := x₀) Finset.univ (fun i _ ↦ hloc i)
    fun v hv hs i _ ↦ hqc v (fun i ↦ hv i (Finset.mem_univ i)) hs i
  simpa using this

/-- Cor. 2.17 of [Mordukhovich 2018], second part: if moreover all the sets `Ωᵢ` are normally
regular at `x₀`, then (2.32) holds as an equality and `⋂ᵢ Ωᵢ` is normally regular at `x₀`. -/
theorem normalCone_iInter_eq [Fintype ι]
    (hloc : ∀ i, ∃ r > 0, IsClosed (Ω i ∩ closedBall x₀ r))
    (hqc : ∀ v : ι → StrongDual ℝ E, (∀ i, v i ∈ normalCone (Ω i) x₀) → ∑ i, v i = 0 →
      ∀ i, v i = 0) (hr : ∀ i, NormallyRegularAt (Ω i) x₀) :
    normalCone (⋂ i, Ω i) x₀ = ∑ i, normalCone (Ω i) x₀ ∧ NormallyRegularAt (⋂ i, Ω i) x₀ := by
  have h1 := normalCone_iInter_subset hloc hqc
  have h2 : ∑ i, normalCone (Ω i) x₀ ⊆ regularNormalCone (⋂ i, Ω i) x₀ := by
    rw [Finset.sum_congr rfl fun i _ ↦ hr i]
    simpa using sum_regularNormalCone_subset_biInter (Ω := Ω) (x₀ := x₀) Finset.univ
  exact ⟨subset_antisymm h1 (h2.trans regularNormalCone_subset_normalCone),
    subset_antisymm (h1.trans h2) regularNormalCone_subset_normalCone⟩

end FiniteIntersection

section Sum

/-! ### Normals to sums of sets -/

variable {Ω₁ Ω₂ : Set E} {x₀ : E}

/-- [Mordukhovich 2018, proof of Cor. 2.18, (2.33)]: a regular normal to `Ω₁ + Ω₂` at
`x₁ + x₂` is a regular normal to `Ω₁` at `x₁` and to `Ω₂` at `x₂`. -/
theorem mem_regularNormalCone_of_mem_regularNormalCone_add {x₁ x₂ : E} (hx₁ : x₁ ∈ Ω₁)
    (hx₂ : x₂ ∈ Ω₂) {v : StrongDual ℝ E} (hv : v ∈ regularNormalCone (Ω₁ + Ω₂) (x₁ + x₂)) :
    v ∈ regularNormalCone Ω₁ x₁ ∧ v ∈ regularNormalCone Ω₂ x₂ := by
  refine ⟨⟨hx₁, fun ε hε ↦ ?_⟩, ⟨hx₂, fun ε hε ↦ ?_⟩⟩
  · have hT : Tendsto (fun y ↦ y + x₂) (𝓝[Ω₁] x₁) (𝓝[Ω₁ + Ω₂] (x₁ + x₂)) :=
      tendsto_nhdsWithin_iff.2 ⟨((continuous_id.add continuous_const).tendsto x₁).mono_left
        nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun y hy ↦ Set.add_mem_add hy hx₂⟩
    filter_upwards [hT.eventually (hv.2 ε hε)] with y hy
    simpa [add_sub_add_right_eq_sub] using hy
  · have hT : Tendsto (fun y ↦ x₁ + y) (𝓝[Ω₂] x₂) (𝓝[Ω₁ + Ω₂] (x₁ + x₂)) :=
      tendsto_nhdsWithin_iff.2 ⟨((continuous_const.add continuous_id).tendsto x₂).mono_left
        nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun y hy ↦ Set.add_mem_add hx₁ hy⟩
    filter_upwards [hT.eventually (hv.2 ε hε)] with y hy
    simpa [add_sub_add_left_eq_sub] using hy

/-- Cor. 2.18 of [Mordukhovich 2018] (normals to sums of sets): let `Ω₁, Ω₂` be closed and let
`S(x) = {(x₁, x₂) | x₁ + x₂ = x, x₁ ∈ Ω₁, x₂ ∈ Ω₂}` be locally bounded around `x₀`. Then
`N(x₀; Ω₁ + Ω₂) ⊆ ⋃_{(x₁, x₂) ∈ S(x₀)} N(x₁; Ω₁) ∩ N(x₂; Ω₂)`. -/
theorem normalCone_add_subset [FiniteDimensional ℝ E] (h₁ : IsClosed Ω₁) (h₂ : IsClosed Ω₂)
    (hS : LocallyBoundedAt (fun x ↦ {p : E × E | p.1 + p.2 = x ∧ p.1 ∈ Ω₁ ∧ p.2 ∈ Ω₂}) x₀) :
    normalCone (Ω₁ + Ω₂) x₀ ⊆
      ⋃ p ∈ {p : E × E | p.1 + p.2 = x₀ ∧ p.1 ∈ Ω₁ ∧ p.2 ∈ Ω₂},
        normalCone Ω₁ p.1 ∩ normalCone Ω₂ p.2 := by
  rintro v ⟨-, a, w, ha, hw, hmem⟩
  have ha' := tendsto_nhdsWithin_iff.1 ha
  have hsplit : ∀ k, ∃ p : E × E, a k ∈ Ω₁ + Ω₂ → p.1 + p.2 = a k ∧ p.1 ∈ Ω₁ ∧ p.2 ∈ Ω₂ :=
    fun k ↦ by
      by_cases hk : a k ∈ Ω₁ + Ω₂
      · obtain ⟨y₁, hy₁, y₂, hy₂, hy⟩ := hk
        exact ⟨(y₁, y₂), fun _ ↦ ⟨hy, hy₁, hy₂⟩⟩
      · exact ⟨0, fun h ↦ absurd h hk⟩
  choose p hp using hsplit
  obtain ⟨U, hU, hbdd⟩ := hS
  have hpB : ∀ᶠ k in atTop, p k ∈ ⋃ x ∈ U, {p : E × E | p.1 + p.2 = x ∧ p.1 ∈ Ω₁ ∧ p.2 ∈ Ω₂} := by
    filter_upwards [ha'.2, ha'.1.eventually hU] with k hk hkU
    exact mem_biUnion hkU (hp k hk)
  obtain ⟨q, -, φ, hφ, hq⟩ := tendsto_subseq_of_frequently_bounded hbdd hpB.frequently
  have hφ' := hφ.tendsto_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hφ'.eventually ha'.2)
  have hpk : ∀ k, N ≤ k → (p (φ k)).1 + (p (φ k)).2 = a (φ k) ∧ (p (φ k)).1 ∈ Ω₁ ∧
      (p (φ k)).2 ∈ Ω₂ := fun k hk ↦ hp _ (hN k hk)
  have hq₁ : Tendsto (fun k ↦ (p (φ k)).1) atTop (𝓝 q.1) := (continuous_fst.tendsto q).comp hq
  have hq₂ : Tendsto (fun k ↦ (p (φ k)).2) atTop (𝓝 q.2) := (continuous_snd.tendsto q).comp hq
  have hev : ∀ᶠ k in atTop, N ≤ k := eventually_ge_atTop N
  have hqΩ₁ : q.1 ∈ Ω₁ := h₁.mem_of_tendsto hq₁ (hev.mono fun k hk ↦ (hpk k hk).2.1)
  have hqΩ₂ : q.2 ∈ Ω₂ := h₂.mem_of_tendsto hq₂ (hev.mono fun k hk ↦ (hpk k hk).2.2)
  have hqsum : q.1 + q.2 = x₀ := tendsto_nhds_unique (hq₁.add hq₂)
    ((ha'.1.comp hφ').congr' (hev.mono fun k hk ↦ (hpk k hk).1.symm))
  have hreg : ∀ k, N ≤ k → w (φ k) ∈ regularNormalCone Ω₁ (p (φ k)).1 ∧
      w (φ k) ∈ regularNormalCone Ω₂ (p (φ k)).2 := fun k hk ↦ by
    have h := hmem (φ k)
    rw [← (hpk k hk).1] at h
    exact mem_regularNormalCone_of_mem_regularNormalCone_add (hpk k hk).2.1 (hpk k hk).2.2 h
  refine mem_biUnion (x := q) ⟨hqsum, hqΩ₁, hqΩ₂⟩ ⟨⟨hqΩ₁, ?_⟩, ⟨hqΩ₂, ?_⟩⟩
  · exact mem_outerLimit_of_eventually _ _ (tendsto_nhdsWithin_iff.2 ⟨hq₁,
      hev.mono fun k hk ↦ (hpk k hk).2.1⟩) (hw.comp hφ') (hev.mono fun k hk ↦ (hreg k hk).1)
  · exact mem_outerLimit_of_eventually _ _ (tendsto_nhdsWithin_iff.2 ⟨hq₂,
      hev.mono fun k hk ↦ (hpk k hk).2.2⟩) (hw.comp hφ') (hev.mono fun k hk ↦ (hreg k hk).2)

end Sum


end VariationalAnalysis
