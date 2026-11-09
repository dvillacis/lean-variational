/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import VariationalAnalysis.SCD.Semismooth
import VariationalAnalysis.SCD.Subregularity

/-!
# Strong metric subregularity of SCD regular, SCD semismooth* mappings

Following [Gfrerer–Outrata 2022, Section 6], SCD regularity together with SCD semismoothness*
is sufficient for strong metric subregularity, with `subreg F(x̄, ȳ) ≤ scdreg F(x̄, ȳ)`
(Thm 6.2). Conversely, strong metric subregularity around `(x̄, ȳ)` gives SCD regularity
around `(x̄, ȳ)` and `l-subreg F(x̄, ȳ) ≥ scdreg F(x̄, ȳ)` (the remark before Thm 6.2, from
Lemma 3.10 and Lemma 4.5), so that for SCD semismooth* mappings the two properties are
equivalent and the moduli agree (Cor. 6.4).

All moduli involved (`subreg`, `l-subreg`, `scdreg`) only use the norm of `E`, so the
statements do not depend on the choice of norm on `E × E`. In the proofs, the estimate of
Prop. 5.3 is used with the constant `max 1 ‖C_L‖` of `IsSCDSemismoothStarAt.eventually_norm_le`
instead of `√(n(1 + ‖C_L‖²))`.

## Main results

* `IsSCDSemismoothStarAt.stronglyMetricallySubregularWith`,
  `IsSCDSemismoothStarAt.subregBound_le`: if `F` is SCD semismooth* at `p`, then `F` is strongly
  metrically subregular at `p` with every modulus `κ > scdreg F(p)`, and
  `subreg F(p) ≤ scdreg F(p)` (the core of [Gfrerer–Outrata 2022, Thm 6.2]; no SCD regularity
  hypothesis beyond `scdreg F(p) < ∞` is needed).
* `IsSCDRegularAround.eventually_stronglyMetricallySubregularWith`:
  [Gfrerer–Outrata 2022, Thm 6.2]: if `F` is SCD regular around `p` and `κ > scdreg F(p)`, then
  near `p`, at every point of `gph F` where `F` is SCD semismooth*, `F` is strongly metrically
  subregular with modulus `κ` and `subreg F < κ`.
* `StronglyMetricallySubregularAround.isSCDRegularAround`,
  `IsSCDRegularAround.scdreg_le_lsubregBound`: the remark before [Gfrerer–Outrata 2022,
  Thm 6.2].
* `IsSCDSemismoothStarAround.stronglyMetricallySubregularAround_iff`,
  `IsSCDSemismoothStarAround.lsubregBound_eq`: [Gfrerer–Outrata 2022, Cor. 6.4].
-/

open Filter Topology Set Metric
open scoped NNReal ENNReal

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : E → Set E} {p : E × E}

/-- The core of [Gfrerer–Outrata 2022, Thm 6.2]: if `F` is SCD semismooth* at `p` and
`scdreg F(p) < κ`, then `F` is strongly metrically subregular at `p` with modulus `κ`. -/
theorem IsSCDSemismoothStarAt.stronglyMetricallySubregularWith (hss : IsSCDSemismoothStarAt F p)
    {κ : ℝ≥0} (hκ : scdreg F p < κ) : StronglyMetricallySubregularWith κ F p.1 p.2 := by
  obtain ⟨κ', h1, h2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hκ
  have hκ'κ : (κ' : ℝ) < κ := by exact_mod_cast h2
  have hκ' : (0 : ℝ) ≤ κ' := κ'.coe_nonneg
  have hκpos : (0 : ℝ) < κ := lt_of_le_of_lt hκ' hκ'κ
  set M : ℝ := max 1 (κ' : ℝ) with hMdef
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_left _ _)
  set α : ℝ := (κ - κ') / (1 + κ) with hαdef
  have hα : 0 < α := div_pos (sub_pos.2 hκ'κ) (by positivity)
  have hα1 : 0 < 1 - α := by
    rw [sub_pos, div_lt_one (by positivity)]
    linarith
  have hkey : (κ' : ℝ) + α = κ * (1 - α) := by
    rw [hαdef]
    field_simp
    ring
  set ε : ℝ := α / M
  have hε : 0 < ε := div_pos hα hM
  have hεM : ε * M = α := div_mul_cancel₀ _ hM.ne'
  -- the estimate `‖x - x̄‖ ≤ κ' ‖y - ȳ‖ + α ‖(x, y) - (x̄, ȳ)‖` near `p`
  obtain ⟨U, hU, hscd⟩ := hss.1
  have hreg := eventually_isRegularSubspace_and_norm_le (F := F) (p := p) (κ := κ')
    (by rwa [ENNReal.ofReal_coe_nnreal])
  have H : ∀ᶠ q in 𝓝 p, q ∈ graph F →
      ‖q.1 - p.1‖ ≤ κ' * ‖q.2 - p.2‖ + α * ‖q - p‖ := by
    filter_upwards [hU, hreg, hss.eventually_norm_le hε] with q hqU hqreg hqest hqF
    obtain ⟨L, hL⟩ := hasSCDPropertyAt_iff_scCoderiv_nonempty.1 (hscd q ⟨hqF, hqU⟩)
    obtain ⟨hLr, hLn⟩ := hqreg L hL
    have hest := hqest hqF L hL hLr
    set C := regularSubspaceOp L
    have hC : ‖ContinuousLinearMap.adjoint C (q.2 - p.2)‖ ≤ κ' * ‖q.2 - p.2‖ :=
      ((ContinuousLinearMap.adjoint C).le_opNorm _).trans (by
        rw [ContinuousLinearMap.adjoint.norm_map]
        gcongr)
    have hεC : ε * max 1 ‖C‖ ≤ α := by
      rw [← hεM]
      exact mul_le_mul_of_nonneg_left (max_le_max le_rfl hLn) hε.le
    calc ‖q.1 - p.1‖
        = ‖ContinuousLinearMap.adjoint C (q.2 - p.2) +
            (q.1 - ContinuousLinearMap.adjoint C (q.2 - p.2) - p.1)‖ := by congr 1; abel
      _ ≤ ‖ContinuousLinearMap.adjoint C (q.2 - p.2)‖ +
            ‖q.1 - ContinuousLinearMap.adjoint C (q.2 - p.2) - p.1‖ := norm_add_le _ _
      _ ≤ κ' * ‖q.2 - p.2‖ + ε * max 1 ‖C‖ * ‖q - p‖ := add_le_add hC hest
      _ ≤ κ' * ‖q.2 - p.2‖ + α * ‖q - p‖ := by gcongr
  obtain ⟨δ, hδ, hδH⟩ := Metric.eventually_nhds_iff.1 H
  refine stronglyMetricallySubregularWith_of_dist_le (by exact_mod_cast hκpos) ?_
  refine Metric.eventually_nhds_iff.2 ⟨min δ (κ * δ), lt_min hδ (mul_pos hκpos hδ),
    fun x hx y hy ↦ ?_⟩
  rw [dist_eq_norm, dist_eq_norm]
  rw [dist_eq_norm] at hx
  have hxδ : ‖x - p.1‖ < δ := lt_of_lt_of_le hx (min_le_left _ _)
  by_cases hyδ : ‖y - p.2‖ < δ
  · have hq : dist (x, y) p < δ := by
      rw [dist_eq_norm, Prod.norm_def]
      exact max_lt hxδ hyδ
    have h := hδH hq hy
    have hn : ‖(x, y) - p‖ ≤ ‖x - p.1‖ + ‖y - p.2‖ := by
      rw [Prod.norm_def]
      exact max_le (le_add_of_nonneg_right (norm_nonneg _))
        (le_add_of_nonneg_left (norm_nonneg _))
    simp only at h
    have h3 : (1 - α) * ‖x - p.1‖ ≤ (1 - α) * (κ * ‖y - p.2‖) := by
      nlinarith [mul_le_mul_of_nonneg_left hn hα.le]
    exact le_of_mul_le_mul_left h3 hα1
  · push Not at hyδ
    calc ‖x - p.1‖ ≤ κ * δ := (lt_of_lt_of_le hx (min_le_right _ _)).le
      _ ≤ κ * ‖y - p.2‖ := by gcongr

/-- [Gfrerer–Outrata 2022, Thm 6.2]: at a point where `F` is SCD semismooth*,
`subreg F(p) ≤ scdreg F(p)`. -/
theorem IsSCDSemismoothStarAt.subregBound_le (hss : IsSCDSemismoothStarAt F p) :
    subregBound F p.1 p.2 ≤ scdreg F p := by
  by_contra hcon
  obtain ⟨κ, h1, h2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (not_le.1 hcon)
  exact absurd (hss.stronglyMetricallySubregularWith h1).subregBound_le (not_le.2 h2)

/-- [Gfrerer–Outrata 2022, Thm 6.2]: if `F` is SCD regular around `p` and
`κ > scdreg F(p)`, then there is a neighborhood `W` of `p` such that `F` is strongly
metrically subregular with modulus `κ`, and `subreg F(q) < κ`, at every `q ∈ gph F ∩ W` where
`F` is SCD semismooth*. -/
theorem IsSCDRegularAround.eventually_stronglyMetricallySubregularWith
    (h : IsSCDRegularAround F p) {κ : ℝ≥0} (hκ : scdreg F p < κ) :
    ∀ᶠ q in 𝓝 p, q ∈ graph F → IsSCDSemismoothStarAt F q →
      StronglyMetricallySubregularWith κ F q.1 q.2 ∧ subregBound F q.1 q.2 < κ := by
  obtain ⟨κ', h1, h2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hκ
  filter_upwards [h.eventually (κ := κ') (by rwa [ENNReal.ofReal_coe_nnreal])] with q hq _ hss
  have hq' : scdreg F q ≤ κ' := by simpa using hq.2
  exact ⟨hss.stronglyMetricallySubregularWith (hq'.trans_lt h2),
    (hss.subregBound_le.trans hq').trans_lt h2⟩

/-- The remark before [Gfrerer–Outrata 2022, Thm 6.2] (Lemma 3.10 with Lemma 4.5): if `F` has
the SCD property around `p` and is strongly metrically subregular around `p`, then `F` is SCD
regular around `p`. -/
theorem StronglyMetricallySubregularAround.isSCDRegularAround
    (h : StronglyMetricallySubregularAround F p.1 p.2) (hscd : HasSCDPropertyAround F p) :
    IsSCDRegularAround F p :=
  isSCDRegularAround_iff_scDeriv.2 ⟨hscd, fun _ hL _ hu ↦ h.eq_zero_of_mem_scDeriv hL hu⟩

/-- The remark before [Gfrerer–Outrata 2022, Thm 6.2] (Lemma 3.10 with Lemma 4.5):
`scdreg F(p) ≤ l-subreg F(p)` for `F` SCD regular around `p`. -/
theorem IsSCDRegularAround.scdreg_le_lsubregBound (h : IsSCDRegularAround F p) :
    scdreg F p ≤ lsubregBound F p.1 p.2 := by
  rw [h.scdreg_eq_iSup_scDeriv, lsubregBound_eq_coneBound]
  refine iSup₂_le fun L hL ↦ subspaceBound_le_iff.2 fun w hw hw2 ↦ ?_
  rw [coe_nnnorm_eq_ofReal]
  exact le_coneBound (mem_sharpTangentCone_of_mem_scDeriv hL hw) hw2

/-- SCD regularity and SCD semismoothness* around `p` give strong metric subregularity around
`p` with every modulus `κ > scdreg F(p)` (Thm 6.2 of [Gfrerer–Outrata 2022]). -/
theorem IsSCDSemismoothStarAround.eventually_stronglyMetricallySubregularWith
    (hss : IsSCDSemismoothStarAround F p) (h : IsSCDRegularAround F p) {κ : ℝ≥0}
    (hκ : scdreg F p < κ) :
    ∀ᶠ q in 𝓝 p, q ∈ graph F → StronglyMetricallySubregularWith κ F q.1 q.2 := by
  filter_upwards [h.eventually_stronglyMetricallySubregularWith hκ, hss.eventually]
    with q hq hq' hqF
  exact (hq hqF ((hq' hqF).isSCDSemismoothStarAt hqF)).1

/-- The "if" part of [Gfrerer–Outrata 2022, Cor. 6.4]. -/
theorem IsSCDSemismoothStarAround.stronglyMetricallySubregularAround
    (hss : IsSCDSemismoothStarAround F p) (h : IsSCDRegularAround F p) :
    StronglyMetricallySubregularAround F p.1 p.2 := by
  obtain ⟨κ, h1, -⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 h.scdreg_lt_top
  exact ⟨κ, hss.eventually_stronglyMetricallySubregularWith h h1⟩

/-- `l-subreg F(p) ≤ scdreg F(p)` under SCD regularity and SCD semismoothness* around `p`
(from Thm 6.2 of [Gfrerer–Outrata 2022]). -/
theorem IsSCDSemismoothStarAround.lsubregBound_le (hss : IsSCDSemismoothStarAround F p)
    (h : IsSCDRegularAround F p) : lsubregBound F p.1 p.2 ≤ scdreg F p := by
  by_contra hcon
  obtain ⟨κ, h1, h2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (not_le.1 hcon)
  exact absurd (lsubregBound_le_of_eventually
    (hss.eventually_stronglyMetricallySubregularWith h h1)) (not_le.2 h2)

/-- [Gfrerer–Outrata 2022, Cor. 6.4]: for `F` SCD semismooth* around `p ∈ gph F`, strong metric
subregularity around `p` is equivalent to SCD regularity around `p`. -/
theorem IsSCDSemismoothStarAround.stronglyMetricallySubregularAround_iff
    (hss : IsSCDSemismoothStarAround F p) (hp : p ∈ graph F) :
    StronglyMetricallySubregularAround F p.1 p.2 ↔ IsSCDRegularAround F p :=
  ⟨fun h ↦ h.isSCDRegularAround (hss.isSCDSemismoothStarAt hp).1,
    hss.stronglyMetricallySubregularAround⟩

/-- [Gfrerer–Outrata 2022, Cor. 6.4]: in this case `l-subreg F(p) = scdreg F(p)`. -/
theorem IsSCDSemismoothStarAround.lsubregBound_eq (hss : IsSCDSemismoothStarAround F p)
    (h : IsSCDRegularAround F p) : lsubregBound F p.1 p.2 = scdreg F p :=
  le_antisymm (hss.lsubregBound_le h) h.scdreg_le_lsubregBound

end VariationalAnalysis
