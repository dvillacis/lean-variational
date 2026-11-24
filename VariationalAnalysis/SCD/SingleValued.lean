/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Topology.MetricSpace.Sequences
import VariationalAnalysis.SCD.Basic

/-!
# SCD properties of single-valued mappings

For `f : E → E` we consider the single-valued mapping `x ↦ {f x}` and its SC derivatives
[Gfrerer–Outrata 2022, Section 3].

## Main declarations

* `bSubdiff f x`: the B-subdifferential `∇̄f(x)`, the limits of `∇f(xₖ)` along
  differentiability points `xₖ → x`.

## Main results

* `contingentCone_graph_of_hasFDerivAt`: Lemma 3.2(i) of [Gfrerer–Outrata 2022]: at a point of
  differentiability, `T_{gph f}(x, f x) = rge(I, ∇f(x))`.
* `hasFDerivAt_of_graphicallySmoothAt`: Lemma 3.2(ii): if `f` is calm at `x` and
  `T_{gph f}(x, f x)` is an `n`-dimensional subspace, then `f` is differentiable at `x`.
* `grassTendsto_graph`: `Aₖ → A` implies `rge(I, Aₖ) → rge(I, A)` [Gfrerer–Outrata 2022,
  Lemma 3.1(i)].
* `graph_mem_scDeriv_of_mem_bSubdiff`, `graph_adjoint_mem_scCoderiv_of_mem_bSubdiff`:
  Lemma 3.11, (18) and (19).
* `mem_scDeriv_iff_of_lipschitzOnWith`, `mem_scCoderiv_iff_of_lipschitzOnWith`: Lemma 3.11,
  equality for locally Lipschitz `f`.
* `hasSCDPropertyAround_of_lipschitzOnWith`, `LipschitzWith.isSCDMapping`: Lemma 3.11 and
  Remark 3.12: locally Lipschitz mappings are SCD mappings (via Rademacher's theorem).
-/

open Filter Topology Set Module Asymptotics MeasureTheory
open scoped InnerProductSpace NNReal

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {f : E → E} {x : E} {A : E →L[ℝ] E}

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem mem_graph_singleton_iff {p : E × E} : p ∈ graph (fun x ↦ ({f x} : Set E)) ↔ p.2 = f p.1 :=
  Iff.rfl

omit [FiniteDimensional ℝ E] in
/-- First-order expansion along sequences: if `yₖ → x` and `αₖ (yₖ - x) → u`, then
`αₖ (f yₖ - f x) → ∇f(x) u`. -/
theorem tendsto_smul_sub_of_hasFDerivAt (hf : HasFDerivAt f A x) {y : ℕ → E} {α : ℕ → ℝ}
    {u : E} (hy : Tendsto y atTop (𝓝 x)) (hu : Tendsto (fun k ↦ α k • (y k - x)) atTop (𝓝 u)) :
    Tendsto (fun k ↦ α k • (f (y k) - f x)) atTop (𝓝 (A u)) := by
  have h1 : (fun k ↦ f (y k) - f x - A (y k - x)) =o[atTop] (fun k ↦ y k - x) :=
    hf.isLittleO.comp_tendsto hy
  have h2 : (fun k ↦ α k • (f (y k) - f x - A (y k - x))) =o[atTop]
      (fun k ↦ α k • (y k - x)) :=
    (isBigO_refl α atTop).smul_isLittleO h1
  have h3 : Tendsto (fun k ↦ α k • (f (y k) - f x - A (y k - x))) atTop (𝓝 0) :=
    (isLittleO_one_iff ℝ).1 (h2.trans_isBigO (hu.isBigO_one ℝ))
  have h4 : Tendsto (fun k ↦ A (α k • (y k - x))) atTop (𝓝 (A u)) :=
    (A.continuous.tendsto u).comp hu
  have := h3.add h4
  simp only [zero_add] at this
  refine this.congr fun k ↦ ?_
  rw [map_smul, map_sub, smul_sub, smul_sub, smul_sub]
  abel

omit [FiniteDimensional ℝ E] in
/-- Lemma 3.2(i) of [Gfrerer–Outrata 2022]: at a point of Fréchet differentiability the
contingent cone to the graph is the graph of the derivative,
`T_{gph f}(x, f x) = rge(I, ∇f(x))`. -/
theorem contingentCone_graph_of_hasFDerivAt (hf : HasFDerivAt f A x) :
    contingentCone (graph fun x ↦ ({f x} : Set E)) (x, f x) =
      ((A : E →ₗ[ℝ] E).graph : Set (E × E)) := by
  ext ⟨u, v⟩
  simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, ContinuousLinearMap.coe_coe]
  constructor
  · rintro ⟨-, p, α, hpα, hplim, hlim⟩
    have hp : ∀ k, p k = ((p k).1, f (p k).1) := fun k ↦ Prod.ext rfl (hpα k).1
    have h1 : Tendsto (fun k ↦ α k • ((p k).1 - x)) atTop (𝓝 u) :=
      (continuous_fst.tendsto _).comp hlim
    have h2 : Tendsto (fun k ↦ α k • (f (p k).1 - f x)) atTop (𝓝 v) := by
      refine ((continuous_snd.tendsto _).comp hlim).congr fun k ↦ ?_
      simp only [Function.comp_apply, Prod.smul_snd, Prod.snd_sub]
      rw [show (p k).2 = f (p k).1 from (hpα k).1]
    have h3 := tendsto_smul_sub_of_hasFDerivAt hf ((continuous_fst.tendsto _).comp hplim) h1
    exact tendsto_nhds_unique h2 h3
  · rintro rfl
    have hδ : Tendsto (fun k : ℕ ↦ ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hpos : ∀ k : ℕ, ((k : ℝ) + 1) ≠ 0 := fun k ↦ by positivity
    have hy : Tendsto (fun k : ℕ ↦ x + ((k : ℝ) + 1)⁻¹ • u) atTop (𝓝 x) := by
      simpa using tendsto_const_nhds.add (hδ.smul_const u)
    have hu : Tendsto (fun k : ℕ ↦ ((k : ℝ) + 1) • (x + ((k : ℝ) + 1)⁻¹ • u - x)) atTop
        (𝓝 u) := by
      refine tendsto_const_nhds.congr fun k ↦ ?_
      simp [smul_smul, hpos k]
    refine ⟨rfl, fun k ↦ (x + ((k : ℝ) + 1)⁻¹ • u, f (x + ((k : ℝ) + 1)⁻¹ • u)),
      fun k ↦ (k : ℝ) + 1, fun k ↦ ⟨rfl, by positivity⟩, hy.prodMk_nhds
        ((hf.continuousAt.tendsto).comp hy), ?_⟩
    have h := hu.prodMk_nhds (tendsto_smul_sub_of_hasFDerivAt hf hy hu)
    refine h.congr fun k ↦ ?_
    rw [Prod.mk_sub_mk, Prod.smul_mk]

omit [FiniteDimensional ℝ E] in
theorem graphicallySmoothAt_of_hasFDerivAt (hf : HasFDerivAt f A x) :
    GraphicallySmoothAt (fun x ↦ ({f x} : Set E)) (x, f x) :=
  ⟨rfl, _, finrank_graph _, (contingentCone_graph_of_hasFDerivAt hf).symm⟩

omit [FiniteDimensional ℝ E] in
theorem tangentSubspace_of_hasFDerivAt (hf : HasFDerivAt f A x) :
    tangentSubspace (fun x ↦ ({f x} : Set E)) (x, f x) = (A : E →ₗ[ℝ] E).graph := by
  rw [tangentSubspace, contingentCone_graph_of_hasFDerivAt hf, Submodule.span_eq]

theorem graph_mem_scDeriv_of_hasFDerivAt (hf : HasFDerivAt f A x) :
    (A : E →ₗ[ℝ] E).graph ∈ scDeriv (fun x ↦ ({f x} : Set E)) (x, f x) := by
  rw [← tangentSubspace_of_hasFDerivAt hf]
  exact (graphicallySmoothAt_of_hasFDerivAt hf).tangentSubspace_mem_scDeriv

/-- `Aₖ → A` implies `rge(I, Aₖ) → rge(I, A)` in the Grassmannian metric
[Gfrerer–Outrata 2022, Lemma 3.1(i)]. -/
theorem grassTendsto_graph {B : ℕ → E →L[ℝ] E} (hB : Tendsto B atTop (𝓝 A)) :
    GrassTendsto (fun k ↦ (B k : E →ₗ[ℝ] E).graph) (A : E →ₗ[ℝ] E).graph := by
  refine grassTendsto_of_outerLimit_subset (n := finrank ℝ E) (fun k ↦ finrank_graph _)
    (finrank_graph _) ?_
  rintro w ⟨a, v, ha, hv, hmem⟩
  simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, ContinuousLinearMap.coe_coe] at hmem ⊢
  have h1 : Tendsto (fun k ↦ B (a k) (v k).1) atTop (𝓝 (A w.1)) :=
    tendsto_clm_apply (hB.comp ha) ((continuous_fst.tendsto _).comp hv)
  have h2 : Tendsto (fun k ↦ (v k).2) atTop (𝓝 w.2) := (continuous_snd.tendsto _).comp hv
  exact tendsto_nhds_unique h2 (h1.congr fun k ↦ (hmem k).symm)

/-! ### Lemma 3.2(ii): calmness and graphical smoothness give differentiability -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem continuousAt_of_calm {κ : ℝ} (hcalm : ∀ᶠ x' in 𝓝 x, ‖f x' - f x‖ ≤ κ * ‖x' - x‖) :
    ContinuousAt f x := by
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun x' ↦ κ * ‖x' - x‖) (𝓝 x) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := κ)).mul
      ((continuous_id.sub continuous_const).norm.tendsto' x 0 (by simp))
  exact squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) hcalm h0

omit [FiniteDimensional ℝ E] in
/-- Under calmness, `(0, v) ∈ T_{gph f}(x, f x)` forces `v = 0`. -/
theorem eq_zero_of_mk_zero_mem_contingentCone {κ : ℝ}
    (hcalm : ∀ᶠ x' in 𝓝 x, ‖f x' - f x‖ ≤ κ * ‖x' - x‖) {v : E}
    (hv : ((0 : E), v) ∈ contingentCone (graph fun x ↦ ({f x} : Set E)) (x, f x)) : v = 0 := by
  obtain ⟨-, p, α, hpα, hplim, hlim⟩ := hv
  have h1 : Tendsto (fun k ↦ α k • ((p k).1 - x)) atTop (𝓝 0) :=
    (continuous_fst.tendsto _).comp hlim
  have h2 : Tendsto (fun k ↦ α k • ((p k).2 - f x)) atTop (𝓝 v) :=
    (continuous_snd.tendsto _).comp hlim
  have hev : ∀ᶠ k in atTop, ‖α k • ((p k).2 - f x)‖ ≤ κ * ‖α k • ((p k).1 - x)‖ := by
    filter_upwards [((continuous_fst.tendsto _).comp hplim).eventually hcalm] with k hk
    have hk' : ‖f (p k).1 - f x‖ ≤ κ * ‖(p k).1 - x‖ := hk
    rw [show (p k).2 = f (p k).1 from (hpα k).1, norm_smul, norm_smul,
      Real.norm_of_nonneg (hpα k).2]
    nlinarith [(hpα k).2]
  have h3 : Tendsto (fun k ↦ κ * ‖α k • ((p k).1 - x)‖) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := κ)).mul h1.norm
  have := le_of_tendsto_of_tendsto h2.norm h3 hev
  exact norm_le_zero_iff.1 this

/-- Under calmness, an `n`-dimensional tangent subspace `T_{gph f}(x, f x)` is the graph of a
linear map [Gfrerer–Outrata 2022, proof of Lemma 3.2(ii)]. -/
theorem exists_clm_of_graphicallySmoothAt {κ : ℝ}
    (hcalm : ∀ᶠ x' in 𝓝 x, ‖f x' - f x‖ ≤ κ * ‖x' - x‖)
    (h : GraphicallySmoothAt (fun x ↦ ({f x} : Set E)) (x, f x)) :
    ∃ B : E →L[ℝ] E, ∀ u v, (u, v) ∈ contingentCone (graph fun x ↦ ({f x} : Set E)) (x, f x) →
      v = B u := by
  obtain ⟨-, L, hdim, hL⟩ := h
  set π : L →ₗ[ℝ] E := (LinearMap.fst ℝ E E).comp L.subtype with hπ
  have hinj : Function.Injective π := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨u, v⟩, hw⟩ h0
    have hu : u = 0 := by simpa [hπ] using h0
    subst hu
    have hv := eq_zero_of_mk_zero_mem_contingentCone hcalm
      (show ((0 : E), v) ∈ contingentCone _ _ by rw [← hL]; exact hw)
    subst hv
    rfl
  have hsurj : Function.Surjective π :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj
  let e := LinearEquiv.ofBijective π ⟨hinj, hsurj⟩
  refine ⟨LinearMap.toContinuousLinearMap
    (((LinearMap.snd ℝ E E).comp L.subtype).comp e.symm.toLinearMap), fun u v huv ↦ ?_⟩
  have hw : (u, v) ∈ L := by rw [← SetLike.mem_coe, hL]; exact huv
  have he : e.symm u = ⟨(u, v), hw⟩ := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp [he]

/-- Lemma 3.2(ii) of [Gfrerer–Outrata 2022]: if `f` is calm at `x` and `T_{gph f}(x, f x)` is an
`n`-dimensional subspace, then `f` is Fréchet differentiable at `x`. -/
theorem differentiableAt_of_graphicallySmoothAt {κ : ℝ}
    (hcalm : ∀ᶠ x' in 𝓝 x, ‖f x' - f x‖ ≤ κ * ‖x' - x‖)
    (h : GraphicallySmoothAt (fun x ↦ ({f x} : Set E)) (x, f x)) : DifferentiableAt ℝ f x := by
  obtain ⟨B, hB⟩ := exists_clm_of_graphicallySmoothAt hcalm h
  have hcont := continuousAt_of_calm hcalm
  refine ⟨B, hasFDerivAt_iff_tendsto.2 (tendsto_nhds_iff_seq_tendsto.2 fun y hy ↦ ?_)⟩
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  set z : ℕ → E := fun k ↦ y (ns k) with hz_def
  have hz : Tendsto z atTop (𝓝 x) := hy.comp hns
  set α : ℕ → ℝ := fun k ↦ ‖z k - x‖⁻¹ with hα_def
  have hα0 : ∀ k, 0 ≤ α k := fun k ↦ inv_nonneg.2 (norm_nonneg _)
  have hα1 : ∀ k, α k * ‖z k - x‖ ≤ 1 := fun k ↦ by
    rcases eq_or_lt_of_le (norm_nonneg (z k - x)) with h0 | h0
    · simp [← h0]
    · rw [hα_def, inv_mul_cancel₀ h0.ne']
  set w : ℕ → E × E := fun k ↦ (α k • (z k - x), α k • (f (z k) - f x)) with hw_def
  have hbd : ∀ᶠ k in atTop, w k ∈ Metric.closedBall (0 : E × E) (1 + |κ|) := by
    filter_upwards [hz.eventually hcalm] with k hk
    have hk' : ‖f (z k) - f x‖ ≤ κ * ‖z k - x‖ := hk
    rw [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff]
    simp only [hw_def, norm_smul, Real.norm_of_nonneg (hα0 k)]
    constructor
    · linarith [hα1 k, abs_nonneg κ]
    · have h1 : α k * ‖f (z k) - f x‖ ≤ κ * (α k * ‖z k - x‖) := by
        nlinarith [hα0 k]
      have h2 : κ * (α k * ‖z k - x‖) ≤ |κ| := by
        have := mul_nonneg (hα0 k) (norm_nonneg (z k - x))
        nlinarith [le_abs_self κ, abs_nonneg κ, hα1 k]
      linarith
  obtain ⟨w₀, -, φ, hφ, hw⟩ := tendsto_subseq_of_frequently_bounded Metric.isBounded_closedBall
    hbd.frequently
  have hzφ : Tendsto (z ∘ φ) atTop (𝓝 x) := hz.comp hφ.tendsto_atTop
  have hw₀ : w₀ ∈ contingentCone (graph fun x ↦ ({f x} : Set E)) (x, f x) := by
    refine ⟨rfl, fun k ↦ (z (φ k), f (z (φ k))), fun k ↦ α (φ k), fun k ↦ ⟨rfl, hα0 _⟩,
      hzφ.prodMk_nhds ((hcont.tendsto).comp hzφ), hw.congr fun k ↦ ?_⟩
    simp [hw_def, Prod.smul_mk]
  have hB₀ := hB _ _ hw₀
  refine ⟨φ, ?_⟩
  have hlim : Tendsto (fun k ↦ ‖(w (φ k)).2 - B (w (φ k)).1‖) atTop (𝓝 0) := by
    have := (((continuous_snd.sub (B.continuous.comp continuous_fst)).norm).tendsto w₀).comp hw
    simpa [Function.comp_def, ← hB₀] using this
  refine hlim.congr fun k ↦ ?_
  simp only [hw_def, Function.comp_apply, map_smul, ← smul_sub, norm_smul, hα_def, hz_def,
    norm_inv, norm_norm, sub_sub]

/-- For `f` Lipschitz around `x`, `(x, f x) ∈ O_f` iff `f` is differentiable at `x`
[Gfrerer–Outrata 2022, Lemma 3.2]. -/
theorem graphicallySmoothAt_iff_differentiableAt {s : Set E} {K : ℝ≥0}
    (hf : LipschitzOnWith K f s) (hs : s ∈ 𝓝 x) :
    GraphicallySmoothAt (fun x ↦ ({f x} : Set E)) (x, f x) ↔ DifferentiableAt ℝ f x := by
  refine ⟨fun h ↦ differentiableAt_of_graphicallySmoothAt (κ := K) ?_ h,
    fun h ↦ graphicallySmoothAt_of_hasFDerivAt h.hasFDerivAt⟩
  filter_upwards [hs] with x' hx'
  exact lipschitzOnWith_iff_norm_sub_le.1 hf hx' (mem_of_mem_nhds hs)

/-! ### The B-subdifferential and Lemma 3.11 -/

/-- The B-subdifferential `∇̄f(x)`: the limits of `∇f(xₖ)` along points of differentiability
`xₖ → x` [Gfrerer–Outrata 2022, p. 11]. -/
def bSubdiff (f : E → E) (x : E) : Set (E →L[ℝ] E) :=
  {A | ∃ y : ℕ → E, (∀ k, DifferentiableAt ℝ f (y k)) ∧ Tendsto y atTop (𝓝 x) ∧
    Tendsto (fun k ↦ fderiv ℝ f (y k)) atTop (𝓝 A)}

/-- Lemma 3.11, (18), of [Gfrerer–Outrata 2022]: `𝒮f(x) ⊇ {rge(I, A) | A ∈ ∇̄f(x)}`. -/
theorem graph_mem_scDeriv_of_mem_bSubdiff (hc : ContinuousAt f x) (hA : A ∈ bSubdiff f x) :
    (A : E →ₗ[ℝ] E).graph ∈ scDeriv (fun x ↦ ({f x} : Set E)) (x, f x) := by
  obtain ⟨y, hd, hy, hAlim⟩ := hA
  refine ⟨fun k ↦ (y k, f (y k)), fun k ↦ graphicallySmoothAt_of_hasFDerivAt (hd k).hasFDerivAt,
    hy.prodMk_nhds ((hc.tendsto).comp hy), ?_⟩
  have h := grassTendsto_graph hAlim
  convert h using 2 with k
  exact tangentSubspace_of_hasFDerivAt (hd k).hasFDerivAt

/-- Lemma 3.11, (19), of [Gfrerer–Outrata 2022]: `𝒮*f(x) ⊇ {rge(I, Aᵀ) | A ∈ ∇̄f(x)}`. -/
theorem graph_adjoint_mem_scCoderiv_of_mem_bSubdiff (hc : ContinuousAt f x)
    (hA : A ∈ bSubdiff f x) :
    (ContinuousLinearMap.adjoint A : E →ₗ[ℝ] E).graph ∈
      scCoderiv (fun x ↦ ({f x} : Set E)) (x, f x) :=
  ⟨_, graph_mem_scDeriv_of_mem_bSubdiff hc hA, adjointSubspace_graph A⟩

/-- Lemma 3.11 of [Gfrerer–Outrata 2022], equality in (18) for `f` Lipschitz around `x`. -/
theorem exists_mem_bSubdiff_of_mem_scDeriv {s : Set E} {K : ℝ≥0} (hf : LipschitzOnWith K f s)
    (hs : s ∈ 𝓝 x) {L : Submodule ℝ (E × E)}
    (hL : L ∈ scDeriv (fun x ↦ ({f x} : Set E)) (x, f x)) :
    ∃ A ∈ bSubdiff f x, L = (A : E →ₗ[ℝ] E).graph := by
  obtain ⟨q, hq, hqlim, hT⟩ := hL
  have hqk : ∀ k, q k = ((q k).1, f (q k).1) := fun k ↦ Prod.ext rfl (hq k).1
  have hy : Tendsto (fun k ↦ (q k).1) atTop (𝓝 x) := (continuous_fst.tendsto _).comp hqlim
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hy.eventually (interior_mem_nhds.2 hs))
  have hsN : ∀ k, N ≤ k → s ∈ 𝓝 (q k).1 := fun k hk ↦ mem_interior_iff_mem_nhds.1 (hN k hk)
  have hdiff : ∀ k, N ≤ k → DifferentiableAt ℝ f (q k).1 := fun k hk ↦ by
    have h := hq k
    rw [hqk k] at h
    exact (graphicallySmoothAt_iff_differentiableAt hf (hsN k hk)).1 h
  set D : ℕ → E →L[ℝ] E := fun k ↦ fderiv ℝ f (q (k + N)).1 with hD
  have hDb : ∀ k, D k ∈ Metric.closedBall (0 : E →L[ℝ] E) K := fun k ↦ by
    rw [mem_closedBall_zero_iff]
    exact norm_fderiv_le_of_lipschitzOn ℝ (hsN _ (Nat.le_add_left N k)) hf
  obtain ⟨A, -, φ, hφ, hA⟩ := (isCompact_closedBall (0 : E →L[ℝ] E) K).tendsto_subseq hDb
  set ψ : ℕ → ℕ := fun k ↦ φ k + N with hψ
  have hψt : Tendsto ψ atTop atTop :=
    tendsto_atTop_mono (fun k ↦ Nat.le_add_right _ _) hφ.tendsto_atTop
  refine ⟨A, ⟨fun k ↦ (q (ψ k)).1, fun k ↦ hdiff _ (Nat.le_add_left N _), hy.comp hψt, hA⟩, ?_⟩
  refine (hT.comp hψt).unique ?_
  have h := grassTendsto_graph hA
  convert h using 2 with k
  simp only [Function.comp_apply]
  rw [hqk (ψ k)]
  exact tangentSubspace_of_hasFDerivAt (hdiff _ (Nat.le_add_left N _)).hasFDerivAt

/-- Lemma 3.11 of [Gfrerer–Outrata 2022]: for `f` Lipschitz around `x`,
`𝒮f(x) = {rge(I, A) | A ∈ ∇̄f(x)}`. -/
theorem mem_scDeriv_iff_of_lipschitzOnWith {s : Set E} {K : ℝ≥0} (hf : LipschitzOnWith K f s)
    (hs : s ∈ 𝓝 x) {L : Submodule ℝ (E × E)} :
    L ∈ scDeriv (fun x ↦ ({f x} : Set E)) (x, f x) ↔
      ∃ A ∈ bSubdiff f x, L = (A : E →ₗ[ℝ] E).graph := by
  refine ⟨exists_mem_bSubdiff_of_mem_scDeriv hf hs, ?_⟩
  rintro ⟨A, hA, rfl⟩
  exact graph_mem_scDeriv_of_mem_bSubdiff (hf.continuousOn.continuousAt hs) hA

/-- Lemma 3.11 of [Gfrerer–Outrata 2022]: for `f` Lipschitz around `x`,
`𝒮*f(x) = {rge(I, Aᵀ) | A ∈ ∇̄f(x)}`. -/
theorem mem_scCoderiv_iff_of_lipschitzOnWith {s : Set E} {K : ℝ≥0}
    (hf : LipschitzOnWith K f s) (hs : s ∈ 𝓝 x) {L : Submodule ℝ (E × E)} :
    L ∈ scCoderiv (fun x ↦ ({f x} : Set E)) (x, f x) ↔
      ∃ A ∈ bSubdiff f x, L = (ContinuousLinearMap.adjoint A : E →ₗ[ℝ] E).graph := by
  constructor
  · rintro ⟨L', hL', rfl⟩
    obtain ⟨A, hA, rfl⟩ := exists_mem_bSubdiff_of_mem_scDeriv hf hs hL'
    exact ⟨A, hA, adjointSubspace_graph A⟩
  · rintro ⟨A, hA, rfl⟩
    exact graph_adjoint_mem_scCoderiv_of_mem_bSubdiff (hf.continuousOn.continuousAt hs) hA

/-! ### Lipschitz mappings are SCD mappings -/

/-- Rademacher's theorem, local form: a mapping Lipschitz around `x` has points of
differentiability arbitrarily close to `x`. -/
theorem mem_closure_differentiableAt {s : Set E} {K : ℝ≥0} (hf : LipschitzOnWith K f s)
    (hs : s ∈ 𝓝 x) : x ∈ closure {z | DifferentiableAt ℝ f z} := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  have hae := hf.ae_differentiableWithinAt_of_mem (μ := Measure.addHaar)
  rw [mem_closure_iff_nhds]
  intro t ht
  by_contra hne
  have h0 : (Measure.addHaar : Measure E) (t ∩ interior s) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 hae)
    rintro z ⟨hzt, hzs⟩
    change ¬(z ∈ s → _)
    intro h
    exact hne ⟨z, hzt, (h (interior_subset hzs)).differentiableAt
      (mem_interior_iff_mem_nhds.1 hzs)⟩
  exact (Measure.measure_pos_of_mem_nhds _ (inter_mem ht (interior_mem_nhds.2 hs))).ne' h0

/-- Lemma 3.11 / Remark 3.12 of [Gfrerer–Outrata 2022]: a mapping that is Lipschitz around `x`
has the SCD property at `(x, f x)`. -/
theorem hasSCDPropertyAt_of_lipschitzOnWith {s : Set E} {K : ℝ≥0} (hf : LipschitzOnWith K f s)
    (hs : s ∈ 𝓝 x) : HasSCDPropertyAt (fun x ↦ ({f x} : Set E)) (x, f x) := by
  rw [hasSCDPropertyAt_iff_mem_closure]
  obtain ⟨z, hz, hzlim⟩ := mem_closure_iff_seq_limit.1 (mem_closure_differentiableAt hf hs)
  exact mem_closure_of_tendsto
    (hzlim.prodMk_nhds (((hf.continuousOn.continuousAt hs).tendsto).comp hzlim))
    (Eventually.of_forall fun k ↦ graphicallySmoothAt_of_hasFDerivAt (hz k).hasFDerivAt)

/-- For `f` Lipschitz around `x`, the B-subdifferential `∇̄f(x)` is nonempty. -/
theorem bSubdiff_nonempty_of_lipschitzOnWith {s : Set E} {K : ℝ≥0} (hf : LipschitzOnWith K f s)
    (hs : s ∈ 𝓝 x) : (bSubdiff f x).Nonempty := by
  obtain ⟨L, hL⟩ := hasSCDPropertyAt_of_lipschitzOnWith hf hs
  obtain ⟨A, hA, -⟩ := exists_mem_bSubdiff_of_mem_scDeriv hf hs hL
  exact ⟨A, hA⟩

/-- Lemma 3.11 of [Gfrerer–Outrata 2022]: a mapping that is Lipschitz around `x` has the SCD
property around `(x, f x)`. -/
theorem hasSCDPropertyAround_of_lipschitzOnWith {s : Set E} {K : ℝ≥0}
    (hf : LipschitzOnWith K f s) (hs : s ∈ 𝓝 x) :
    HasSCDPropertyAround (fun x ↦ ({f x} : Set E)) (x, f x) := by
  refine ⟨interior s ×ˢ univ, prod_mem_nhds (interior_mem_nhds.2 hs) univ_mem,
    fun q ⟨hq, hqU⟩ ↦ ?_⟩
  rw [show q = (q.1, f q.1) from Prod.ext rfl hq]
  exact hasSCDPropertyAt_of_lipschitzOnWith hf (mem_interior_iff_mem_nhds.1 hqU.1)

/-- Remark 3.12 of [Gfrerer–Outrata 2022]: every Lipschitz mapping is an SCD mapping. -/
theorem LipschitzWith.isSCDMapping {K : ℝ≥0} (hf : LipschitzWith K f) :
    IsSCDMapping (fun x ↦ ({f x} : Set E)) := fun p hp ↦ by
  rw [show p = (p.1, f p.1) from Prod.ext rfl hp]
  exact hasSCDPropertyAt_of_lipschitzOnWith (hf.lipschitzOnWith (s := univ)) univ_mem

/-- A differentiable mapping is an SCD mapping: every point of its graph is a point of graphical
smoothness [Gfrerer–Outrata 2022, Lemma 3.2(i)]. -/
theorem Differentiable.isSCDMapping (hf : Differentiable ℝ f) :
    IsSCDMapping (fun x ↦ ({f x} : Set E)) := fun p hp ↦ by
  rw [show p = (p.1, f p.1) from Prod.ext rfl hp]
  exact (graphicallySmoothAt_of_hasFDerivAt (hf p.1).hasFDerivAt).hasSCDPropertyAt

end VariationalAnalysis
