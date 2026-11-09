/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import VariationalAnalysis.SCD.Basic
import VariationalAnalysis.WellPosedness.Basic

/-!
# Strong metric subregularity and the outer limiting graphical derivative

A mapping `S : E ⇉ F` is *strongly metrically subregular* at `(x₀, y₀) ∈ gph S` with modulus
`κ ≥ 0` if `‖x - x₀‖ ≤ κ dist(y₀, S x)` for all `x` near `x₀` [Gfrerer–Outrata 2022, Def. 2.5];
it is strongly metrically subregular *around* `(x₀, y₀)` if this holds at every point of
`gph S` near `(x₀, y₀)` with `l-subreg S (x₀, y₀) = Lim sup subreg S (x, y) < ∞`
[Gfrerer–Outrata 2022, Def. 2.8]. In finite dimensions, strong metric subregularity at a point is
characterized by the graphical derivative (the Levy–Rockafellar criterion) and strong metric
subregularity around a point by the outer limiting graphical derivative `D♯S`
[Gfrerer–Outrata 2022, Thm 6.1].

## Design choices

* As in `VariationalAnalysis.WellPosedness.Basic`, distances to sets are extended distances
  `Metric.infEDist` in `ℝ≥0∞`, so that `dist(y₀, ∅) = ∞`, and moduli are in `ℝ≥0`.
* We define strong metric subregularity directly by the estimate `‖x - x₀‖ ≤ κ dist(y₀, S x)`;
  `stronglyMetricallySubregularAt_iff_subregular_isolated` shows that this is the paper's
  definition (metric subregularity plus isolatedness of `x₀` in `S⁻¹ y₀`).
* Strong metric subregularity around `(x₀, y₀)` is defined with a uniform modulus `κ` on a
  neighborhood; `stronglyMetricallySubregularAround_iff_lsubregBound_lt_top` shows that this
  is the paper's condition `l-subreg S (x₀, y₀) < ∞`.
* The graphical derivative `DS(x₀, y₀)` is the contingent cone `T_{gph S}(x₀, y₀)` and
  `D♯S(x₀, y₀)` has graph `sharpTangentCone (gph S) (x₀, y₀)`. For a cone `C ⊆ E × F`,
  `coneBound C = sup {‖u‖ | (u, v) ∈ C, ‖v‖ ≤ 1} ∈ ℝ≥0∞`.
* The characterizations need no closedness of `gph S`.

## Main declarations

* `StronglyMetricallySubregularWith κ S x₀ y₀`, `StronglyMetricallySubregularAt`,
  `subregBound`: [Gfrerer–Outrata 2022, Def. 2.5(2)].
* `StronglyMetricallySubregularAround`, `lsubregBound`: [Gfrerer–Outrata 2022, Def. 2.8].
* `coneBound C`: `sup {‖u‖ | (u, v) ∈ C, ‖v‖ ≤ 1}`.

## Main results

* `stronglyMetricallySubregularAt_iff`, `subregBound_eq_coneBound`: the Levy–Rockafellar
  criterion [Gfrerer–Outrata 2022, Thm 2.7(i)]: `S` is strongly metrically subregular at
  `(x₀, y₀)` iff `0 ∈ DS(x₀, y₀)(u) ⇒ u = 0`, and
  `subreg S (x₀, y₀) = sup {‖u‖ | (u, v) ∈ gph DS(x₀, y₀), ‖v‖ ≤ 1}`.
* `stronglyMetricallySubregularAround_iff`, `lsubregBound_eq_coneBound`:
  [Gfrerer–Outrata 2022, Thm 6.1]: `S` is strongly metrically subregular around `(x₀, y₀)` iff
  `0 ∈ D♯S(x₀, y₀)(u) ⇒ u = 0`, and (43)
  `l-subreg S (x₀, y₀) = sup {‖u‖ | (u, v) ∈ gph D♯S(x₀, y₀), ‖v‖ ≤ 1}`.
* `StronglyMetricallySubregularAround.eq_zero_of_mem_scDeriv`: for `S : E ⇉ E`, strong metric
  subregularity around `(x₀, y₀)` gives `(u, 0) ∈ L ∈ 𝒮S(x₀, y₀) ⇒ u = 0` (by Lemma 3.10).
-/

open Filter Topology Set Metric
open scoped NNReal ENNReal

namespace VariationalAnalysis

section Definitions

variable {E F : Type*} [MetricSpace E] [MetricSpace F]

/-- Strong metric subregularity with modulus `κ` at `(x₀, y₀)`: `‖x - x₀‖ ≤ κ dist(y₀, S x)` for
all `x` near `x₀` [Gfrerer–Outrata 2022, Def. 2.5(2)] (see
`stronglyMetricallySubregularAt_iff_subregular_isolated` for the equivalence with the paper's
formulation). The distance is the extended distance, `dist(y₀, ∅) = ∞`. -/
def StronglyMetricallySubregularWith (κ : ℝ≥0) (S : E → Set F) (x₀ : E) (y₀ : F) : Prop :=
  ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, edist x x₀ ≤ κ * infEDist y₀ (S x)

/-- `S` is strongly metrically subregular at `(x₀, y₀)` [Gfrerer–Outrata 2022, Def. 2.5(2)]. -/
def StronglyMetricallySubregularAt (S : E → Set F) (x₀ : E) (y₀ : F) : Prop :=
  ∃ κ, StronglyMetricallySubregularWith κ S x₀ y₀

/-- The modulus `subreg S (x₀, y₀)`: the infimum of all moduli of strong metric subregularity
(`∞` if there is none) [Gfrerer–Outrata 2022, Def. 2.5]. -/
noncomputable def subregBound (S : E → Set F) (x₀ : E) (y₀ : F) : ℝ≥0∞ :=
  ⨅ (κ : ℝ≥0) (_ : StronglyMetricallySubregularWith κ S x₀ y₀), (κ : ℝ≥0∞)

/-- Strong metric subregularity around `(x₀, y₀)` (on a neighborhood): there is a uniform
modulus `κ` at all points of `gph S` near `(x₀, y₀)`. By
`stronglyMetricallySubregularAround_iff_lsubregBound_lt_top` this is
[Gfrerer–Outrata 2022, Def. 2.8]. -/
def StronglyMetricallySubregularAround (S : E → Set F) (x₀ : E) (y₀ : F) : Prop :=
  ∃ κ : ℝ≥0, ∀ᶠ p in 𝓝 (x₀, y₀), p ∈ graph S → StronglyMetricallySubregularWith κ S p.1 p.2

/-- `l-subreg S (x₀, y₀) = Lim sup_{(x, y) →gph S (x₀, y₀)} subreg S (x, y)`
[Gfrerer–Outrata 2022, Def. 2.8]. -/
noncomputable def lsubregBound (S : E → Set F) (x₀ : E) (y₀ : F) : ℝ≥0∞ :=
  limsup (fun p : E × F ↦ subregBound S p.1 p.2) (𝓝[graph S] (x₀, y₀))

end Definitions

section Metric

variable {E F : Type*} [MetricSpace E] [MetricSpace F]
variable {S : E → Set F} {x₀ : E} {y₀ : F} {κ κ' : ℝ≥0}

theorem StronglyMetricallySubregularWith.mono (h : StronglyMetricallySubregularWith κ S x₀ y₀)
    (hle : κ ≤ κ') : StronglyMetricallySubregularWith κ' S x₀ y₀ := by
  obtain ⟨U, hU, h⟩ := h
  exact ⟨U, hU, fun x hx ↦ (h x hx).trans (by gcongr)⟩

theorem StronglyMetricallySubregularWith.subregBound_le
    (h : StronglyMetricallySubregularWith κ S x₀ y₀) : subregBound S x₀ y₀ ≤ κ :=
  iInf₂_le κ h

theorem StronglyMetricallySubregularWith.stronglyMetricallySubregularAt
    (h : StronglyMetricallySubregularWith κ S x₀ y₀) : StronglyMetricallySubregularAt S x₀ y₀ :=
  ⟨κ, h⟩

theorem stronglyMetricallySubregularAt_iff_subregBound_lt_top :
    StronglyMetricallySubregularAt S x₀ y₀ ↔ subregBound S x₀ y₀ < ⊤ := by
  constructor
  · rintro ⟨κ, h⟩
    exact h.subregBound_le.trans_lt ENNReal.coe_lt_top
  · intro h
    simp only [subregBound, iInf_lt_iff] at h
    obtain ⟨κ, hκ, -⟩ := h
    exact ⟨κ, hκ⟩

/-- Elementwise form of strong metric subregularity. -/
theorem StronglyMetricallySubregularWith.dist_le (h : StronglyMetricallySubregularWith κ S x₀ y₀) :
    ∀ᶠ x in 𝓝 x₀, ∀ y ∈ S x, dist x x₀ ≤ κ * dist y y₀ := by
  obtain ⟨U, hU, h⟩ := h
  filter_upwards [hU] with x hx y hy
  have h1 : edist x x₀ ≤ κ * edist y y₀ :=
    (h x hx).trans (by gcongr; exact (infEDist_le_edist_of_mem hy).trans_eq (edist_comm _ _))
  rw [edist_nndist, edist_nndist, ← ENNReal.coe_mul, ENNReal.coe_le_coe] at h1
  rw [dist_nndist, dist_nndist]
  exact_mod_cast h1

theorem stronglyMetricallySubregularWith_of_dist_le (hκ : 0 < κ)
    (h : ∀ᶠ x in 𝓝 x₀, ∀ y ∈ S x, dist x x₀ ≤ κ * dist y y₀) :
    StronglyMetricallySubregularWith κ S x₀ y₀ := by
  refine ⟨_, h, fun x hx ↦ ?_⟩
  rw [← infEDist_singleton]
  refine (infEDist_le_mul_infEDist_iff hκ).2 fun y hy ε hε ↦ ⟨x₀, mem_singleton _, ?_⟩
  have := hx y hy
  rw [dist_comm y₀ y]
  linarith

/-- [Gfrerer–Outrata 2022, Def. 2.5(2)]: strong metric subregularity at `(x₀, y₀) ∈ gph S` is
metric subregularity, `dist(x, S⁻¹ y₀) ≤ κ dist(y₀, S x)` near `x₀`, together with the
isolatedness of `x₀` in `S⁻¹ y₀`. -/
theorem stronglyMetricallySubregularAt_iff_subregular_isolated (hp : (x₀, y₀) ∈ graph S) :
    StronglyMetricallySubregularAt S x₀ y₀ ↔
      (∃ κ : ℝ≥0, ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, infEDist x (invMap S y₀) ≤ κ * infEDist y₀ (S x)) ∧
        ∃ U ∈ 𝓝 x₀, invMap S y₀ ∩ U = {x₀} := by
  constructor
  · rintro ⟨κ, U, hU, h⟩
    refine ⟨⟨κ, U, hU, fun x hx ↦
      (infEDist_le_edist_of_mem (show x₀ ∈ invMap S y₀ from hp)).trans (h x hx)⟩, U, hU, ?_⟩
    refine subset_antisymm (fun x ⟨hx, hxU⟩ ↦ ?_) (singleton_subset_iff.2 ⟨hp, mem_of_mem_nhds hU⟩)
    have h1 := h x hxU
    rw [infEDist_zero_of_mem (show y₀ ∈ S x from hx), mul_zero, nonpos_iff_eq_zero, edist_eq_zero] at h1
    exact h1
  · rintro ⟨⟨κ, U, hU, h⟩, U', hU', hiso⟩
    obtain ⟨r, hr, hrU'⟩ := Metric.mem_nhds_iff.1 hU'
    refine ⟨κ, U ∩ ball x₀ (r / 2), inter_mem hU (ball_mem_nhds _ (half_pos hr)),
      fun x ⟨hxU, hxr⟩ ↦ le_trans ?_ (h x hxU)⟩
    refine le_infEDist.2 fun z hz ↦ ?_
    by_cases hzr : z ∈ ball x₀ r
    · have : z ∈ invMap S y₀ ∩ U' := ⟨hz, hrU' hzr⟩
      rw [hiso] at this
      rw [mem_singleton_iff.1 this]
    · rw [mem_ball, not_lt] at hzr
      rw [mem_ball] at hxr
      rw [edist_dist, edist_dist]
      refine ENNReal.ofReal_le_ofReal ?_
      have := dist_triangle z x x₀
      rw [dist_comm z x] at this
      linarith

theorem stronglyMetricallySubregularAround_iff_eventually :
    StronglyMetricallySubregularAround S x₀ y₀ ↔
      ∃ κ : ℝ≥0, ∀ᶠ p in 𝓝[graph S] (x₀, y₀), StronglyMetricallySubregularWith κ S p.1 p.2 := by
  simp only [StronglyMetricallySubregularAround, eventually_nhdsWithin_iff]

theorem lsubregBound_le_of_eventually
    (h : ∀ᶠ p in 𝓝 (x₀, y₀), p ∈ graph S → StronglyMetricallySubregularWith κ S p.1 p.2) :
    lsubregBound S x₀ y₀ ≤ κ := by
  refine limsup_le_of_le (by isBoundedDefault) ?_
  rw [eventually_nhdsWithin_iff]
  filter_upwards [h] with p hp hpg using (hp hpg).subregBound_le

theorem eventually_stronglyMetricallySubregularWith_of_lsubregBound_lt
    (hM : lsubregBound S x₀ y₀ < κ) :
    ∀ᶠ p in 𝓝 (x₀, y₀), p ∈ graph S → StronglyMetricallySubregularWith κ S p.1 p.2 := by
  have hev := eventually_lt_of_limsup_lt hM
  rw [eventually_nhdsWithin_iff] at hev
  filter_upwards [hev] with p hp hpg
  have := hp hpg
  simp only [subregBound, iInf_lt_iff] at this
  obtain ⟨κ', hκ', hlt⟩ := this
  exact hκ'.mono (by exact_mod_cast hlt.le)

/-- [Gfrerer–Outrata 2022, Def. 2.8]: `S` is strongly metrically subregular around `(x₀, y₀)` in
the sense of a uniform modulus iff `l-subreg S (x₀, y₀) < ∞`. -/
theorem stronglyMetricallySubregularAround_iff_lsubregBound_lt_top :
    StronglyMetricallySubregularAround S x₀ y₀ ↔ lsubregBound S x₀ y₀ < ⊤ := by
  constructor
  · rintro ⟨κ, h⟩
    exact (lsubregBound_le_of_eventually h).trans_lt ENNReal.coe_lt_top
  · intro hlt
    obtain ⟨M, hM, -⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
    exact ⟨M, eventually_stronglyMetricallySubregularWith_of_lsubregBound_lt hM⟩

end Metric

section Cone

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- `coneBound C = sup {‖u‖ | (u, v) ∈ C, ‖v‖ ≤ 1}`, the norm of a cone `C ⊆ E × F` regarded as
a set-valued map `v ↦ {u | (u, v) ∈ C}`. -/
noncomputable def coneBound (C : Set (E × F)) : ℝ≥0∞ :=
  ⨆ w ∈ C, ⨆ (_ : ‖w.2‖ ≤ 1), ENNReal.ofReal ‖w.1‖

variable {C : Set (E × F)}

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem le_coneBound {w : E × F} (hw : w ∈ C) (hw2 : ‖w.2‖ ≤ 1) :
    ENNReal.ofReal ‖w.1‖ ≤ coneBound C :=
  le_iSup₂_of_le w hw (le_iSup (fun _ : ‖w.2‖ ≤ 1 ↦ ENNReal.ofReal ‖w.1‖) hw2)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem coneBound_le {κ : ℝ≥0} (h : ∀ w ∈ C, ‖w.1‖ ≤ κ * ‖w.2‖) : coneBound C ≤ κ := by
  refine iSup₂_le fun w hw ↦ iSup_le fun hw2 ↦ ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal ((h w hw).trans (mul_le_of_le_one_right κ.coe_nonneg hw2))

/-- For a cone with `coneBound C < ∞`, `‖u‖ ≤ coneBound C ‖v‖` on `C`. -/
theorem norm_fst_le_coneBound (hcone : ∀ w ∈ C, ∀ t : ℝ, 0 ≤ t → t • w ∈ C)
    (hfin : coneBound C ≠ ⊤) {w : E × F} (hw : w ∈ C) :
    ‖w.1‖ ≤ (coneBound C).toNNReal * ‖w.2‖ := by
  set γ := (coneBound C).toNNReal
  have hγ : coneBound C = γ := (ENNReal.coe_toNNReal hfin).symm
  have key : ∀ t : ℝ, 0 ≤ t → t * ‖w.2‖ ≤ 1 → t * ‖w.1‖ ≤ γ := by
    intro t ht ht1
    have h1 := le_coneBound (hcone w hw t ht)
      (by rw [Prod.smul_snd, norm_smul, Real.norm_of_nonneg ht]; exact ht1)
    rwa [hγ, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_ofReal_iff γ.coe_nonneg,
      Prod.smul_fst, norm_smul, Real.norm_of_nonneg ht] at h1
  rcases (norm_nonneg w.2).eq_or_lt with h0 | h0
  · rw [← h0, mul_zero]
    by_contra hne
    push Not at hne
    have := key ((γ + 1) / ‖w.1‖) (by positivity) (by rw [← h0, mul_zero]; exact zero_le_one)
    rw [div_mul_cancel₀ _ hne.ne'] at this
    linarith
  · have := key ‖w.2‖⁻¹ (inv_nonneg.2 h0.le) (by rw [inv_mul_cancel₀ h0.ne'])
    rw [inv_mul_le_iff₀ h0] at this
    linarith

/-- Normalizing an element `(u, v)` of a cone with `c ‖v‖ < ‖u‖` to `‖u‖ = 1`. -/
theorem normalize_mem_cone (hcone : ∀ w ∈ C, ∀ t : ℝ, 0 ≤ t → t • w ∈ C) {w : E × F}
    (hw : w ∈ C) {c : ℝ} (hc : 0 < c) (hlt : c * ‖w.2‖ < ‖w.1‖) :
    ‖w.1‖⁻¹ • w ∈ C ∧ ‖(‖w.1‖⁻¹ • w).1‖ = 1 ∧ ‖(‖w.1‖⁻¹ • w).2‖ ≤ 1 / c := by
  have hpos : 0 < ‖w.1‖ := lt_of_le_of_lt (by positivity) hlt
  refine ⟨hcone w hw _ (inv_nonneg.2 hpos.le), ?_, ?_⟩
  · rw [Prod.smul_fst, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hpos.le),
      inv_mul_cancel₀ hpos.ne']
  · rw [Prod.smul_snd, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hpos.le), le_div_iff₀ hc,
      inv_mul_eq_div, div_mul_eq_mul_div, div_le_one hpos]
    linarith

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- Compactness: a sequence `(uₖ, vₖ)` with `‖uₖ‖ = 1` and `‖vₖ‖ ≤ cₖ → c₀` has a convergent
subsequence whose limit `(u, v)` satisfies `‖u‖ = 1` and `‖v‖ ≤ c₀`. -/
theorem exists_tendsto_subseq_of_norm_fst_eq_one {w : ℕ → E × F} {c : ℕ → ℝ} {R c₀ : ℝ}
    (h1 : ∀ k, ‖(w k).1‖ = 1) (h2 : ∀ k, ‖(w k).2‖ ≤ c k) (hR : ∀ k, c k ≤ R)
    (hc : Tendsto c atTop (𝓝 c₀)) :
    ∃ w₀ : E × F, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (w ∘ φ) atTop (𝓝 w₀) ∧
      ‖w₀.1‖ = 1 ∧ ‖w₀.2‖ ≤ c₀ := by
  have hmem : ∀ k, w k ∈ closedBall (0 : E × F) (max 1 R) := fun k ↦ by
    rw [mem_closedBall_zero_iff, Prod.norm_def, h1]
    exact max_le_max le_rfl ((h2 k).trans (hR k))
  obtain ⟨w₀, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : E × F) (max 1 R)).tendsto_subseq hmem
  refine ⟨w₀, φ, hφ, hlim, ?_, ?_⟩
  · exact tendsto_nhds_unique (((continuous_norm.comp continuous_fst).tendsto w₀).comp hlim)
      (tendsto_const_nhds.congr fun k ↦ (h1 (φ k)).symm)
  · exact le_of_tendsto_of_tendsto' (((continuous_norm.comp continuous_snd).tendsto w₀).comp hlim)
      (hc.comp hφ.tendsto_atTop) fun k ↦ h2 (φ k)

/-- A closed cone `C ⊆ E × F` with `(u, 0) ∈ C ⇒ u = 0` satisfies `‖u‖ ≤ γ ‖v‖` on `C` for
some `γ`. -/
theorem exists_bound_of_isClosed_cone (hC : IsClosed C)
    (hcone : ∀ w ∈ C, ∀ t : ℝ, 0 ≤ t → t • w ∈ C) (h : ∀ u : E, (u, (0 : F)) ∈ C → u = 0) :
    ∃ γ : ℝ≥0, ∀ w ∈ C, ‖w.1‖ ≤ γ * ‖w.2‖ := by
  by_contra hcon
  push Not at hcon
  have key : ∀ k : ℕ, ∃ w ∈ C, ‖w.1‖ = 1 ∧ ‖w.2‖ ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨w, hw, hlt⟩ := hcon ((k : ℝ≥0) + 1)
    push_cast at hlt
    obtain ⟨h1, h2, h3⟩ := normalize_mem_cone hcone hw (by positivity) hlt
    exact ⟨_, h1, h2, h3⟩
  choose w hw h1 h2 using key
  obtain ⟨w₀, φ, hφ, hlim, hn1, hn2⟩ := exists_tendsto_subseq_of_norm_fst_eq_one h1 h2 (R := 1)
    (fun k ↦ by rw [div_le_one (by positivity)]; linarith [k.cast_nonneg (α := ℝ)])
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hmem : w₀ ∈ C := hC.mem_of_tendsto hlim (Eventually.of_forall fun k ↦ hw (φ k))
  have h0 : w₀.2 = 0 := norm_le_zero_iff.1 hn2
  have := h w₀.1 (by rw [← h0]; exact hmem)
  rw [this, norm_zero] at hn1
  exact zero_ne_one hn1

theorem coneBound_ne_top_iff (hC : IsClosed C) (hcone : ∀ w ∈ C, ∀ t : ℝ, 0 ≤ t → t • w ∈ C) :
    coneBound C ≠ ⊤ ↔ ∀ u : E, (u, (0 : F)) ∈ C → u = 0 := by
  constructor
  · intro hfin u hu
    have := norm_fst_le_coneBound hcone hfin hu
    simpa using this
  · intro h
    obtain ⟨γ, hγ⟩ := exists_bound_of_isClosed_cone hC hcone h
    exact ne_top_of_le_ne_top ENNReal.coe_ne_top (coneBound_le hγ)

end Cone

section Tangent

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The contingent cone is closed. -/
theorem isClosed_contingentCone {Ω : Set X} {x₀ : X} (hx : x₀ ∈ Ω) :
    IsClosed (contingentCone Ω x₀) := by
  rw [contingentCone_eq_outerLimit hx]
  exact isClosed_outerLimit_nhdsWithin _

/-- The outer limiting tangent cone is a cone. -/
theorem smul_mem_sharpTangentCone {Ω : Set X} {x w : X} (hw : w ∈ sharpTangentCone Ω x) {t : ℝ}
    (ht : 0 ≤ t) : t • w ∈ sharpTangentCone Ω x := by
  obtain ⟨a, v, ha, hv, hmem⟩ := hw
  exact ⟨a, fun k ↦ t • v k, ha, hv.const_smul t, fun k ↦ smul_mem_contingentCone (hmem k) ht⟩

end Tangent

section Criteria

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]
variable {S : E → Set F} {x₀ : E} {y₀ : F} {κ : ℝ≥0}

/-- Strong metric subregularity with modulus `κ` gives `‖u‖ ≤ κ ‖v‖` on `gph DS(x₀, y₀)`
(the "only if" part of [Gfrerer–Outrata 2022, Thm 2.7(i)]). -/
theorem StronglyMetricallySubregularWith.norm_fst_le
    (h : StronglyMetricallySubregularWith κ S x₀ y₀) {w : E × F}
    (hw : w ∈ contingentCone (graph S) (x₀, y₀)) : ‖w.1‖ ≤ κ * ‖w.2‖ := by
  obtain ⟨-, p, α, hpα, hplim, hlim⟩ := hw
  have hev : ∀ᶠ k in atTop,
      ‖(α k • (p k - (x₀, y₀))).1‖ ≤ κ * ‖(α k • (p k - (x₀, y₀))).2‖ := by
    filter_upwards [((continuous_fst.tendsto _).comp hplim).eventually h.dist_le] with k hk
    have h1 : dist (p k).1 x₀ ≤ κ * dist (p k).2 y₀ := hk (p k).2 (hpα k).1
    rw [dist_eq_norm, dist_eq_norm] at h1
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, norm_smul,
      Real.norm_of_nonneg (hpα k).2]
    calc α k * ‖(p k).1 - x₀‖ ≤ α k * (κ * ‖(p k).2 - y₀‖) :=
          mul_le_mul_of_nonneg_left h1 (hpα k).2
      _ = κ * (α k * ‖(p k).2 - y₀‖) := by ring
  exact le_of_tendsto_of_tendsto (((continuous_norm.comp continuous_fst).tendsto w).comp hlim)
    ((((continuous_norm.comp continuous_snd).tendsto w).comp hlim).const_mul (κ : ℝ)) hev

theorem StronglyMetricallySubregularWith.eq_zero_of_mem_contingentCone
    (h : StronglyMetricallySubregularWith κ S x₀ y₀) {u : E}
    (hu : (u, (0 : F)) ∈ contingentCone (graph S) (x₀, y₀)) : u = 0 := by
  have := h.norm_fst_le hu
  simpa using this

/-- Strong metric subregularity around `(x₀, y₀)` with modulus `κ` gives `‖u‖ ≤ κ ‖v‖` on
`gph D♯S(x₀, y₀)` (the "only if" part of [Gfrerer–Outrata 2022, Thm 6.1]). -/
theorem norm_fst_le_of_mem_sharpTangentCone
    (h : ∀ᶠ p in 𝓝 (x₀, y₀), p ∈ graph S → StronglyMetricallySubregularWith κ S p.1 p.2)
    {w : E × F} (hw : w ∈ sharpTangentCone (graph S) (x₀, y₀)) : ‖w.1‖ ≤ κ * ‖w.2‖ := by
  obtain ⟨a, v, ha, hv, hmem⟩ := hw
  obtain ⟨ha1, ha2⟩ := tendsto_nhdsWithin_iff.1 ha
  have hev : ∀ᶠ k in atTop, ‖(v k).1‖ ≤ κ * ‖(v k).2‖ := by
    filter_upwards [ha1.eventually h, ha2] with k hk hk2
    exact (hk hk2).norm_fst_le (hmem k)
  exact le_of_tendsto_of_tendsto (((continuous_norm.comp continuous_fst).tendsto w).comp hv)
    ((((continuous_norm.comp continuous_snd).tendsto w).comp hv).const_mul (κ : ℝ)) hev

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- The "if" part of [Gfrerer–Outrata 2022, Thm 2.7(i)] with moduli: if `‖u‖ ≤ γ ‖v‖` on
`gph DS(x₀, y₀)`, then `S` is strongly metrically subregular at `(x₀, y₀)` with every modulus
`κ > γ`. -/
theorem stronglyMetricallySubregularWith_of_forall_le (hp : (x₀, y₀) ∈ graph S) {γ : ℝ≥0}
    (hγκ : γ < κ) (h : ∀ w ∈ contingentCone (graph S) (x₀, y₀), ‖w.1‖ ≤ γ * ‖w.2‖) :
    StronglyMetricallySubregularWith κ S x₀ y₀ := by
  have hκ : (0 : ℝ) < κ := lt_of_le_of_lt γ.coe_nonneg (by exact_mod_cast hγκ)
  by_contra hcon
  have key : ∀ k : ℕ, ∃ x : E, ∃ y : F, y ∈ S x ∧ dist x x₀ < 1 / ((k : ℝ) + 1) ∧
      κ * dist y y₀ < dist x x₀ := by
    intro k
    by_contra hk
    push Not at hk
    refine hcon (stronglyMetricallySubregularWith_of_dist_le (by exact_mod_cast hκ) ?_)
    filter_upwards [ball_mem_nhds x₀ (Nat.one_div_pos_of_nat (n := k))] with x hx y hy
    exact hk x y hy (mem_ball.1 hx)
  choose x y hy hx hxy using key
  have hpos : ∀ k, 0 < dist (x k) x₀ := fun k ↦ lt_of_le_of_lt (by positivity) (hxy k)
  have hδ : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hxlim : Tendsto x atTop (𝓝 x₀) := tendsto_iff_dist_tendsto_zero.2
    (squeeze_zero (fun k ↦ dist_nonneg) (fun k ↦ (hx k).le) hδ)
  have hylim : Tendsto y atTop (𝓝 y₀) := by
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun k ↦ dist_nonneg) (fun k ↦ ?_)
      (by simpa using hδ.div_const (κ : ℝ)))
    have h1 := hx k
    have h2 := hxy k
    simp only [one_div] at h1 ⊢
    rw [le_div_iff₀ hκ]
    linarith
  set w : ℕ → E × F := fun k ↦ (dist (x k) x₀)⁻¹ • ((x k, y k) - (x₀, y₀)) with hw_def
  have hw1 : ∀ k, ‖(w k).1‖ = 1 := fun k ↦ by
    rw [hw_def, Prod.smul_fst, Prod.fst_sub, norm_smul, ← dist_eq_norm,
      Real.norm_of_nonneg (inv_nonneg.2 (hpos k).le)]
    exact inv_mul_cancel₀ (hpos k).ne'
  have hw2 : ∀ k, ‖(w k).2‖ ≤ 1 / (κ : ℝ) := fun k ↦ by
    rw [hw_def, Prod.smul_snd, Prod.snd_sub, norm_smul, ← dist_eq_norm,
      Real.norm_of_nonneg (inv_nonneg.2 (hpos k).le), inv_mul_eq_div,
      div_le_div_iff₀ (hpos k) hκ]
    linarith [hxy k]
  obtain ⟨w₀, φ, hφ, hlim, hn1, hn2⟩ := exists_tendsto_subseq_of_norm_fst_eq_one hw1
    (c := fun _ ↦ 1 / (κ : ℝ)) (R := 1 / (κ : ℝ)) hw2 (fun _ ↦ le_rfl) tendsto_const_nhds
  have hw₀ : w₀ ∈ contingentCone (graph S) (x₀, y₀) :=
    ⟨hp, fun k ↦ (x (φ k), y (φ k)), fun k ↦ (dist (x (φ k)) x₀)⁻¹,
      fun k ↦ ⟨hy (φ k), inv_nonneg.2 (hpos _).le⟩,
      (hxlim.comp hφ.tendsto_atTop).prodMk_nhds (hylim.comp hφ.tendsto_atTop), hlim⟩
  have := h w₀ hw₀
  rw [hn1] at this
  have h3 : (κ : ℝ) * ‖w₀.2‖ ≤ 1 := by
    rw [le_div_iff₀ hκ] at hn2
    linarith
  have hγκ' : (γ : ℝ) < κ := by exact_mod_cast hγκ
  rcases (norm_nonneg w₀.2).eq_or_lt with h0 | h0
  · rw [← h0, mul_zero] at this
    linarith
  · nlinarith [mul_lt_mul_of_pos_right hγκ' h0]

/-- The Levy–Rockafellar criterion [Gfrerer–Outrata 2022, Thm 2.7(i)]: `S` is strongly
metrically subregular at `(x₀, y₀) ∈ gph S` iff `0 ∈ DS(x₀, y₀)(u) ⇒ u = 0`. -/
theorem stronglyMetricallySubregularAt_iff (hp : (x₀, y₀) ∈ graph S) :
    StronglyMetricallySubregularAt S x₀ y₀ ↔
      ∀ u : E, (u, (0 : F)) ∈ contingentCone (graph S) (x₀, y₀) → u = 0 := by
  constructor
  · rintro ⟨κ, h⟩ u hu
    exact h.eq_zero_of_mem_contingentCone hu
  · intro h
    obtain ⟨γ, hγ⟩ := exists_bound_of_isClosed_cone (isClosed_contingentCone hp)
      (fun w hw t ht ↦ smul_mem_contingentCone hw ht) h
    exact ⟨γ + 1, stronglyMetricallySubregularWith_of_forall_le hp (lt_add_one γ) hγ⟩

/-- The modulus formula of [Gfrerer–Outrata 2022, Thm 2.7(i)]:
`subreg S (x₀, y₀) = sup {‖u‖ | (u, v) ∈ gph DS(x₀, y₀), ‖v‖ ≤ 1}` (both sides are `∞` when
`S` is not strongly metrically subregular at `(x₀, y₀)`). -/
theorem subregBound_eq_coneBound (hp : (x₀, y₀) ∈ graph S) :
    subregBound S x₀ y₀ = coneBound (contingentCone (graph S) (x₀, y₀)) := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε hlt ↦ ?_)
    (le_iInf₂ fun κ hκ ↦ coneBound_le fun w hw ↦ hκ.norm_fst_le hw)
  have hbd := fun w (hw : w ∈ contingentCone (graph S) (x₀, y₀)) ↦
    norm_fst_le_coneBound (fun w hw t ht ↦ smul_mem_contingentCone hw ht) hlt.ne hw
  rw [← ENNReal.coe_toNNReal hlt.ne, ← ENNReal.coe_add]
  exact (stronglyMetricallySubregularWith_of_forall_le hp (lt_add_of_pos_right _ hε)
    hbd).subregBound_le

/-- The "if" part of [Gfrerer–Outrata 2022, Thm 6.1] with moduli: if `‖u‖ ≤ γ ‖v‖` on
`gph D♯S(x₀, y₀)`, then `S` is strongly metrically subregular with modulus `κ` at all points of
`gph S` near `(x₀, y₀)`, for every `κ > γ`. -/
theorem eventually_stronglyMetricallySubregularWith_of_forall_le {γ : ℝ≥0} (hγκ : γ < κ)
    (h : ∀ w ∈ sharpTangentCone (graph S) (x₀, y₀), ‖w.1‖ ≤ γ * ‖w.2‖) :
    ∀ᶠ p in 𝓝 (x₀, y₀), p ∈ graph S → StronglyMetricallySubregularWith κ S p.1 p.2 := by
  obtain ⟨γ', hγ1, hγ2⟩ := exists_between hγκ
  have hγ'pos : (0 : ℝ) < γ' := lt_of_le_of_lt γ.coe_nonneg (by exact_mod_cast hγ1)
  suffices hsuff : ∀ᶠ p in 𝓝 (x₀, y₀), p ∈ graph S →
      ∀ w ∈ contingentCone (graph S) p, ‖w.1‖ ≤ γ' * ‖w.2‖ by
    filter_upwards [hsuff] with p hp hpg
    exact stronglyMetricallySubregularWith_of_forall_le hpg hγ2 (hp hpg)
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨p, hplim, hp⟩ := exists_seq_forall_of_frequently hcon
  push Not at hp
  choose hpg w hw hlt using hp
  have hn := fun k ↦ normalize_mem_cone (fun w hw t ht ↦ smul_mem_contingentCone hw ht) (hw k)
    hγ'pos (hlt k)
  choose hmem h1 h2 using hn
  obtain ⟨w₀, φ, hφ, hlim, hn1, hn2⟩ := exists_tendsto_subseq_of_norm_fst_eq_one h1
    (c := fun _ ↦ 1 / (γ' : ℝ)) (R := 1 / (γ' : ℝ)) h2 (fun _ ↦ le_rfl) tendsto_const_nhds
  have hw₀ : w₀ ∈ sharpTangentCone (graph S) (x₀, y₀) :=
    ⟨p ∘ φ, _, tendsto_nhdsWithin_iff.2 ⟨hplim.comp hφ.tendsto_atTop,
      Eventually.of_forall fun k ↦ hpg (φ k)⟩, hlim, fun k ↦ hmem (φ k)⟩
  have := h w₀ hw₀
  rw [hn1] at this
  have h3 : (γ' : ℝ) * ‖w₀.2‖ ≤ 1 := by
    rw [le_div_iff₀ hγ'pos] at hn2
    linarith
  have hγγ' : (γ : ℝ) < γ' := by exact_mod_cast hγ1
  rcases (norm_nonneg w₀.2).eq_or_lt with h0 | h0
  · rw [← h0, mul_zero] at this
    linarith
  · nlinarith [mul_lt_mul_of_pos_right hγγ' h0]

/-- [Gfrerer–Outrata 2022, Thm 6.1]: `S` is strongly metrically subregular around `(x₀, y₀)`
iff `0 ∈ D♯S(x₀, y₀)(u) ⇒ u = 0` (42). No closedness of `gph S` is needed. -/
theorem stronglyMetricallySubregularAround_iff :
    StronglyMetricallySubregularAround S x₀ y₀ ↔
      ∀ u : E, (u, (0 : F)) ∈ sharpTangentCone (graph S) (x₀, y₀) → u = 0 := by
  constructor
  · rintro ⟨κ, h⟩ u hu
    have := norm_fst_le_of_mem_sharpTangentCone h hu
    simpa using this
  · intro h
    obtain ⟨γ, hγ⟩ := exists_bound_of_isClosed_cone (isClosed_sharpTangentCone _ _)
      (fun w hw t ht ↦ smul_mem_sharpTangentCone hw ht) h
    exact ⟨γ + 1, eventually_stronglyMetricallySubregularWith_of_forall_le (lt_add_one γ) hγ⟩

/-- (43) of [Gfrerer–Outrata 2022, Thm 6.1]:
`l-subreg S (x₀, y₀) = sup {‖u‖ | (u, v) ∈ gph D♯S(x₀, y₀), ‖v‖ ≤ 1}` (both sides are `∞` when
`S` is not strongly metrically subregular around `(x₀, y₀)`). -/
theorem lsubregBound_eq_coneBound :
    lsubregBound S x₀ y₀ = coneBound (sharpTangentCone (graph S) (x₀, y₀)) := by
  have hcone : ∀ w ∈ sharpTangentCone (graph S) (x₀, y₀), ∀ t : ℝ, 0 ≤ t →
      t • w ∈ sharpTangentCone (graph S) (x₀, y₀) := fun w hw t ht ↦
    smul_mem_sharpTangentCone hw ht
  apply le_antisymm
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt ↦ ?_
    have hbd := fun w hw ↦ norm_fst_le_coneBound hcone hlt.ne (w := w) hw
    rw [← ENNReal.coe_toNNReal hlt.ne, ← ENNReal.coe_add]
    exact lsubregBound_le_of_eventually
      (eventually_stronglyMetricallySubregularWith_of_forall_le (lt_add_of_pos_right _ hε) hbd)
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt ↦ ?_
    have hM : lsubregBound S x₀ y₀ < ((lsubregBound S x₀ y₀).toNNReal + ε : ℝ≥0) := by
      rw [ENNReal.coe_add, ENNReal.coe_toNNReal hlt.ne]
      exact ENNReal.lt_add_right hlt.ne (ENNReal.coe_ne_zero.2 hε.ne')
    have := coneBound_le fun w hw ↦ norm_fst_le_of_mem_sharpTangentCone
      (eventually_stronglyMetricallySubregularWith_of_lsubregBound_lt hM) (w := w) hw
    rwa [ENNReal.coe_add, ENNReal.coe_toNNReal hlt.ne] at this

end Criteria

section SCD

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : E → Set E} {x y : E}

/-- [Gfrerer–Outrata 2022, Thm 6.1] in terms of `D♯F`: `F` is strongly metrically subregular
around `(x, y)` iff `0 ∈ D♯F(x, y)(u) ⇒ u = 0`. -/
theorem stronglyMetricallySubregularAround_iff_sharpDeriv :
    StronglyMetricallySubregularAround F x y ↔ ∀ u : E, 0 ∈ sharpDeriv F x y u → u = 0 :=
  stronglyMetricallySubregularAround_iff

/-- Strong metric subregularity around `(x, y)` with modulus `κ` gives `‖u‖ ≤ κ ‖v‖` for
`(u, v) ∈ L ∈ 𝒮F(x, y)` (Thm 6.1 and Lemma 3.10 of [Gfrerer–Outrata 2022]). -/
theorem norm_le_of_mem_scDeriv {κ : ℝ≥0}
    (h : ∀ᶠ p in 𝓝 (x, y), p ∈ graph F → StronglyMetricallySubregularWith κ F p.1 p.2)
    {L : Submodule ℝ (E × E)} (hL : L ∈ scDeriv F (x, y)) {u v : E} (huv : (u, v) ∈ L) :
    ‖u‖ ≤ κ * ‖v‖ :=
  norm_fst_le_of_mem_sharpTangentCone h (w := (u, v)) (mem_sharpTangentCone_of_mem_scDeriv hL huv)

/-- If `F` is strongly metrically subregular around `(x, y)`, then `(u, 0) ∈ L ∈ 𝒮F(x, y)`
implies `u = 0` (Thm 6.1 and Lemma 3.10 of [Gfrerer–Outrata 2022]). -/
theorem StronglyMetricallySubregularAround.eq_zero_of_mem_scDeriv
    (h : StronglyMetricallySubregularAround F x y) {L : Submodule ℝ (E × E)}
    (hL : L ∈ scDeriv F (x, y)) {u : E} (hu : (u, 0) ∈ L) : u = 0 :=
  stronglyMetricallySubregularAround_iff.1 h u (mem_sharpTangentCone_of_mem_scDeriv hL hu)

end SCD

end VariationalAnalysis
