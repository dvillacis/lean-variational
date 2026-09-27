/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Topology.MetricSpace.Sequences
import VariationalAnalysis.Normal.Diffeomorphism
import VariationalAnalysis.Subdifferential.Coderivative
import VariationalAnalysis.WellPosedness.Criterion

/-!
# Coderivative criteria for well-posedness: special cases

Consequences of the Mordukhovich criterion [Mordukhovich 2018, Thm. 3.3] in special cases
[Mordukhovich 2018, Section 3.1.3], in finite-dimensional spaces:

* Cor. 3.5: local (Hausdorff) Lipschitz continuity of locally bounded set-valued mappings. The
  library has no Hausdorff-Lipschitz notion; `LocallyLipschitzWith ℓ S x₀` is (3.3) with `V` the
  whole space, as the book defines it on p. 112, and `lipBoundAt S x₀` is the exact bound
  `lip S (x₀)`.
* Cor. 3.6: mappings with convex graphs (`rge S = dom S⁻¹`).
* Cor. 3.7: single-valued locally Lipschitzian mappings, via the scalarization
  `D*f(x₀)(v) = ∂⟨v, f⟩(x₀)` (Thm. 1.32).
* Cor. 3.8: smooth mappings: metric regularity iff `∇f(x₀)` is onto (3.17), with the bounds
  (3.18); the proof goes through Thm. 3.3 and Prop. 1.12 (the Lyusternik–Graves proof of the
  book is not formalized).

## Deviations from the book

* Cor. 3.5 assumes, instead of the global closed-graph standing assumption, that
  `gph S ∩ (closedBall x₀ r × F)` is closed for some `r > 0` (closedness over a neighborhood of
  `x₀`), which is what the finite-subcovering argument uses.
* In Cor. 3.6–3.8 the exact bounds are stated as suprema and infima (norms (1.14) of the relevant
  positively homogeneous mappings, in `ℝ≥0∞`); the attainment claimed by the book (`max`, `min`)
  is not formalized. In Cor. 3.5 the maximum is attained (`exists_isMaxOn_posHomNorm_coderiv`).
* The covering statements need a nontrivial domain space, as in Thm. 3.2.

## Main results

* `locallyLipschitzAt_iff_forall_coderiv_zero_eq`, `lipBoundAt_eq_iSup_posHomNorm_coderiv`,
  `exists_isMaxOn_posHomNorm_coderiv`: Cor. 3.5 of [Mordukhovich 2018].
* `metricallyRegularAt_iff_mem_interior_of_convex`, `hasCoveringAt_iff_mem_interior_of_convex`,
  `regBound_eq_of_convex`, `covBound_eq_of_convex`: Cor. 3.6.
* `metricallyRegularAt_iff_of_lipschitz`, `hasCoveringAt_iff_of_lipschitz`,
  `regBound_eq_of_lipschitz`, `covBound_eq_of_lipschitz`: Cor. 3.7.
* `metricallyRegularAt_iff_surjective`, `hasCoveringAt_iff_surjective`,
  `regBound_eq_of_hasFDerivAt`, `covBound_eq_of_hasFDerivAt` (3.18), `covBound_eq_inv_norm_symm`
  (square case `cov f (x₀) = ‖∇f(x₀)⁻¹‖⁻¹`): Cor. 3.8.
* Auxiliary: `locallyLipschitzWith_of_forall_lipschitzLikeWith` (finite subcovering),
  `upperSemicontinuousOn_lipBound`, `exists_ne_zero_forall_le_of_notMem_interior` (supporting
  hyperplanes in finite dimensions), `forall_comp_eq_zero_iff_surjective`
  ([Mordukhovich 2018, Exercise 1.53]), `posHomNorm_comp` (`‖A*‖ = ‖A‖`),
  `locallyClosed_graph_of_continuousOn`.
-/

open Filter Topology Set Metric
open scoped NNReal ENNReal

namespace VariationalAnalysis

section Definitions

variable {E F : Type*} [MetricSpace E] [MetricSpace F]

/-- Local (Hausdorff) Lipschitz continuity of a set-valued mapping around `x₀` with modulus `ℓ`
[Mordukhovich 2018, p. 112]: (3.3) with `V` the whole space, i.e. there is a neighborhood `U` of
`x₀` with `S x ⊆ S u + ℓ ‖x - u‖ 𝔹` for all `x, u ∈ U`. -/
def LocallyLipschitzWith (ℓ : ℝ≥0) (S : E → Set F) (x₀ : E) : Prop :=
  ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, ∀ u ∈ U, ∀ y ∈ S x, ∃ w ∈ S u, dist y w ≤ ℓ * dist x u

/-- `S` is locally Lipschitzian around `x₀` [Mordukhovich 2018, p. 112]. -/
def LocallyLipschitzAt (S : E → Set F) (x₀ : E) : Prop := ∃ ℓ, LocallyLipschitzWith ℓ S x₀

/-- The exact Lipschitzian bound `lip S (x₀)` of a set-valued mapping around `x₀`
[Mordukhovich 2018, Cor. 3.5]: the infimum of its local Lipschitz moduli, in `ℝ≥0∞`. -/
noncomputable def lipBoundAt (S : E → Set F) (x₀ : E) : ℝ≥0∞ :=
  ⨅ (ℓ : ℝ≥0) (_ : LocallyLipschitzWith ℓ S x₀), (ℓ : ℝ≥0∞)

variable {S : E → Set F} {x₀ : E} {ℓ : ℝ≥0}

/-- Local Lipschitz continuity around `x₀` gives the Lipschitz-like property around every
`(x₀, y₀)`, with the same modulus. -/
theorem LocallyLipschitzWith.lipschitzLikeWith (h : LocallyLipschitzWith ℓ S x₀) (y₀ : F) :
    LipschitzLikeWith ℓ S x₀ y₀ := by
  obtain ⟨U, hU, H⟩ := h
  exact ⟨U, hU, univ, univ_mem, fun x hx u hu y hy ↦ H x hx u hu y hy.1⟩

/-- Local Lipschitz moduli can be increased. -/
theorem LocallyLipschitzWith.mono {ℓ' : ℝ≥0} (h : LocallyLipschitzWith ℓ S x₀) (hle : ℓ ≤ ℓ') :
    LocallyLipschitzWith ℓ' S x₀ := by
  obtain ⟨U, hU, H⟩ := h
  refine ⟨U, hU, fun x hx u hu y hy ↦ ?_⟩
  obtain ⟨w, hw, hyw⟩ := H x hx u hu y hy
  exact ⟨w, hw, hyw.trans (by gcongr)⟩

/-- The exact bound `lip S (x₀)` is at most every local Lipschitz modulus. -/
theorem LocallyLipschitzWith.lipBoundAt_le (h : LocallyLipschitzWith ℓ S x₀) :
    lipBoundAt S x₀ ≤ ℓ :=
  iInf₂_le (f := fun (ℓ : ℝ≥0) (_ : LocallyLipschitzWith ℓ S x₀) ↦ (ℓ : ℝ≥0∞)) ℓ h

/-- A lower bound for all local Lipschitz moduli is a lower bound for `lip S (x₀)`. -/
theorem le_lipBoundAt {c : ℝ≥0∞} (h : ∀ ℓ, LocallyLipschitzWith ℓ S x₀ → c ≤ ℓ) :
    c ≤ lipBoundAt S x₀ :=
  le_iInf₂ h

/-- Above `lip S (x₀)` there is a local Lipschitz modulus. -/
theorem exists_locallyLipschitzWith_of_lipBoundAt_lt {c : ℝ≥0∞} (hc : lipBoundAt S x₀ < c) :
    ∃ ℓ, LocallyLipschitzWith ℓ S x₀ ∧ (ℓ : ℝ≥0∞) < c := by
  simpa [lipBoundAt, iInf_lt_iff] using hc

/-- If every `ℓ > c` is a local Lipschitz modulus, then `lip S (x₀) ≤ c`. -/
theorem lipBoundAt_le_of_forall_lt {c : ℝ≥0∞}
    (h : ∀ ℓ : ℝ≥0, c < ℓ → LocallyLipschitzWith ℓ S x₀) : lipBoundAt S x₀ ≤ c := by
  refine le_of_forall_gt fun d hd ↦ ?_
  obtain ⟨ℓ, hcℓ, hℓd⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hd
  exact (h ℓ hcℓ).lipBoundAt_le.trans_lt hℓd

/-- `S` is locally Lipschitzian around `x₀` iff `lip S (x₀) < ∞`. -/
theorem locallyLipschitzAt_iff_lipBoundAt_lt_top :
    LocallyLipschitzAt S x₀ ↔ lipBoundAt S x₀ < ∞ := by
  refine ⟨fun ⟨ℓ, h⟩ ↦ h.lipBoundAt_le.trans_lt ENNReal.coe_lt_top, fun h ↦ ?_⟩
  obtain ⟨ℓ, hℓ, -⟩ := exists_locallyLipschitzWith_of_lipBoundAt_lt h
  exact ⟨ℓ, hℓ⟩

/-- `lip S (x₀, y₀) ≤ lip S (x₀)`. -/
theorem lipBound_le_lipBoundAt (y₀ : F) : lipBound S x₀ y₀ ≤ lipBoundAt S x₀ :=
  le_lipBoundAt fun _ hℓ ↦ (hℓ.lipschitzLikeWith y₀).lipBound_le

/-- The exact Lipschitzian bound `y ↦ lip S (x₀, y)` is upper semicontinuous on `S x₀`, by the
robustness of the Lipschitz-like property [Mordukhovich 2018, proof of Cor. 3.5]. -/
theorem upperSemicontinuousOn_lipBound :
    UpperSemicontinuousOn (fun y ↦ lipBound S x₀ y) (S x₀) := by
  intro y₀ _ c hc
  obtain ⟨ℓ, hℓ, hlt⟩ := exists_lipschitzLikeWith_of_lipBound_lt hc
  have ht : Tendsto (fun y ↦ (x₀, y)) (𝓝 y₀) (𝓝 (x₀, y₀)) :=
    (continuous_const.prodMk continuous_id).tendsto y₀
  exact nhdsWithin_le_nhds ((ht.eventually hℓ.eventually).mono fun y hy ↦
    hy.lipBound_le.trans_lt hlt)

end Definitions

section Cor35

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {S : E → Set F} {x₀ : E} {ℓ : ℝ≥0}

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- If `gph S` is closed over a closed ball around `x₀`, then `gph S` is locally closed around
every `(x₀, y₀)`. -/
theorem locallyClosed_graph_of_isClosed_prod {r : ℝ} (hr : 0 < r)
    (hcl : IsClosed (graph S ∩ closedBall x₀ r ×ˢ univ)) (y₀ : F) :
    ∃ ρ > 0, IsClosed (graph S ∩ closedBall (x₀, y₀) ρ) := by
  refine ⟨r, hr, ?_⟩
  have : graph S ∩ closedBall (x₀, y₀) r =
      (graph S ∩ closedBall x₀ r ×ˢ univ) ∩ closedBall (x₀, y₀) r := by
    ext ⟨a, b⟩
    simp only [mem_inter_iff, mem_prod, mem_closedBall, Prod.dist_eq, max_le_iff, mem_univ,
      and_true]
    tauto
  rw [this]
  exact hcl.inter isClosed_closedBall

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- [Mordukhovich 2018, proof of Cor. 3.5] (finite subcovering): let `S` be locally bounded
around `x₀` with `gph S` closed over a ball around `x₀`, in a proper space `F`. If `S` is
Lipschitz-like around every `(x₀, y₀)`, `y₀ ∈ S x₀`, with a common modulus `ℓ`, then `S` is
locally Lipschitzian around `x₀` with modulus `ℓ`. -/
theorem locallyLipschitzWith_of_forall_lipschitzLikeWith [ProperSpace F]
    (hbd : LocallyBoundedAt S x₀) {r : ℝ} (hr : 0 < r)
    (hcl : IsClosed (graph S ∩ closedBall x₀ r ×ˢ univ))
    (h : ∀ y ∈ S x₀, LipschitzLikeWith ℓ S x₀ y) : LocallyLipschitzWith ℓ S x₀ := by
  obtain ⟨B, hB, hBb⟩ := hbd
  have hSx₀ : S x₀ = (fun y ↦ (x₀, y)) ⁻¹' (graph S ∩ closedBall x₀ r ×ˢ univ) := by
    ext y
    simp [graph, hr.le]
  have hK : IsCompact (S x₀) := by
    refine isCompact_of_isClosed_isBounded ?_ (hBb.subset ?_)
    · rw [hSx₀]
      exact hcl.preimage (continuous_const.prodMk continuous_id)
    · exact subset_biUnion_of_mem (u := S) (mem_of_mem_nhds hB)
  choose U hU V hV H using h
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun y hy ↦ interior (V y hy))
    (fun y hy ↦ interior_mem_nhds.2 (hV y hy))
  set W := ⋃ y ∈ t, interior (V y.1 y.2) with hW_def
  have hWo : IsOpen W := isOpen_biUnion fun _ _ ↦ isOpen_interior
  -- outer semicontinuity: `S x ⊆ W` for `x` near `x₀`
  have hosc : ∀ᶠ x in 𝓝 x₀, S x ⊆ W := by
    by_contra hc
    rw [Filter.not_eventually] at hc
    have key : ∀ k : ℕ, ∃ x ∈ B, dist x x₀ < min r (1 / ((k : ℝ) + 1)) ∧
        ∃ y ∈ S x, y ∉ W := fun k ↦ by
      obtain ⟨x, hx, hxB, hxd⟩ := (hc.and_eventually (inter_mem hB (ball_mem_nhds x₀
        (lt_min hr (Nat.one_div_pos_of_nat (α := ℝ) (n := k)))))).exists
      obtain ⟨y, hy, hyW⟩ := not_subset.1 hx
      exact ⟨x, hxB, hxd, y, hy, hyW⟩
    choose x hxB hxd y hy hyW using key
    obtain ⟨y₁, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded hBb
      (x := y) fun k ↦ mem_biUnion (hxB k) (hy k)
    have hx : Tendsto (fun k ↦ x (φ k)) atTop (𝓝 x₀) := by
      refine (tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ ↦ dist_nonneg)
        (fun k ↦ (hxd k).le.trans (min_le_right _ _))
        tendsto_one_div_add_atTop_nhds_zero_nat)).comp hφ.tendsto_atTop
    have hmem : (x₀, y₁) ∈ graph S ∩ closedBall x₀ r ×ˢ univ :=
      hcl.mem_of_tendsto (hx.prodMk_nhds hlim) (Eventually.of_forall fun k ↦
        ⟨hy (φ k), mem_closedBall.2 ((hxd (φ k)).le.trans (min_le_left _ _)), mem_univ _⟩)
    have hy₁W : y₁ ∈ W := ht hmem.1
    obtain ⟨k, hk⟩ := (hlim.eventually (hWo.mem_nhds hy₁W)).exists
    exact hyW (φ k) hk
  refine ⟨(⋂ y ∈ t, U y.1 y.2) ∩ {x | S x ⊆ W},
    inter_mem ((biInter_finset_mem t).2 fun y _ ↦ hU _ _) hosc, ?_⟩
  intro x hx u hu z hz
  obtain ⟨y, hyt, hzV⟩ := mem_iUnion₂.1 (hx.2 hz)
  exact H y.1 y.2 x (mem_iInter₂.1 hx.1 y hyt) u (mem_iInter₂.1 hu.1 y hyt) z
    ⟨hz, interior_subset hzV⟩

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- Cor. 3.5 of [Mordukhovich 2018] (exact bound): let `S` be locally bounded around `x₀`, with
`gph S` closed over a ball around `x₀`. Then
`lip S (x₀) = sup {‖D*S(x₀, y)‖ | y ∈ S x₀}` in `ℝ≥0∞` (the supremum is a maximum when
`S x₀ ≠ ∅`, `exists_isMaxOn_posHomNorm_coderiv`). -/
theorem lipBoundAt_eq_iSup_posHomNorm_coderiv (hbd : LocallyBoundedAt S x₀) {r : ℝ} (hr : 0 < r)
    (hcl : IsClosed (graph S ∩ closedBall x₀ r ×ˢ univ)) :
    lipBoundAt S x₀ = ⨆ y ∈ S x₀, posHomNorm (coderiv S x₀ y) := by
  have heq : ∀ y ∈ S x₀, lipBound S x₀ y = posHomNorm (coderiv S x₀ y) := fun y hy ↦
    lipBound_eq_posHomNorm_coderiv (locallyClosed_graph_of_isClosed_prod hr hcl y) hy
  refine le_antisymm (lipBoundAt_le_of_forall_lt fun ℓ hℓ ↦ ?_)
    (iSup₂_le fun y hy ↦ (heq y hy).symm.trans_le (lipBound_le_lipBoundAt y))
  refine locallyLipschitzWith_of_forall_lipschitzLikeWith hbd hr hcl fun y hy ↦ ?_
  have hlt : lipBound S x₀ y < ℓ := by
    rw [heq y hy]
    exact (le_iSup₂ (f := fun y (_ : y ∈ S x₀) ↦ posHomNorm (coderiv S x₀ y)) y hy).trans_lt hℓ
  obtain ⟨ℓ', hℓ', hlt'⟩ := exists_lipschitzLikeWith_of_lipBound_lt hlt
  exact hℓ'.mono (by exact_mod_cast hlt'.le)

/-- Cor. 3.5 of [Mordukhovich 2018] (the maximum is attained): under the assumptions of
`lipBoundAt_eq_iSup_posHomNorm_coderiv` and `x₀ ∈ dom S`, there is `ȳ ∈ S x₀` with
`lip S (x₀) = ‖D*S(x₀, ȳ)‖ = max {‖D*S(x₀, y)‖ | y ∈ S x₀}` (upper semicontinuity of
`lip S (x₀, ·)` on the compact set `S x₀`). -/
theorem exists_isMaxOn_posHomNorm_coderiv (hbd : LocallyBoundedAt S x₀) {r : ℝ} (hr : 0 < r)
    (hcl : IsClosed (graph S ∩ closedBall x₀ r ×ˢ univ)) (hne : x₀ ∈ dom S) :
    ∃ y₁ ∈ S x₀, IsMaxOn (fun y ↦ posHomNorm (coderiv S x₀ y)) (S x₀) y₁ ∧
      lipBoundAt S x₀ = posHomNorm (coderiv S x₀ y₁) := by
  have heq : ∀ y ∈ S x₀, lipBound S x₀ y = posHomNorm (coderiv S x₀ y) := fun y hy ↦
    lipBound_eq_posHomNorm_coderiv (locallyClosed_graph_of_isClosed_prod hr hcl y) hy
  obtain ⟨B, hB, hBb⟩ := hbd
  have hK : IsCompact (S x₀) := by
    refine isCompact_of_isClosed_isBounded ?_ (hBb.subset ?_)
    · have : S x₀ = (fun y ↦ (x₀, y)) ⁻¹' (graph S ∩ closedBall x₀ r ×ˢ univ) := by
        ext y
        simp [graph, hr.le]
      rw [this]
      exact hcl.preimage (continuous_const.prodMk continuous_id)
    · exact subset_biUnion_of_mem (u := S) (mem_of_mem_nhds hB)
  obtain ⟨y₁, hy₁, hmax⟩ := upperSemicontinuousOn_lipBound.exists_isMaxOn hne hK
  have hmax' : IsMaxOn (fun y ↦ posHomNorm (coderiv S x₀ y)) (S x₀) y₁ := fun y hy ↦ by
    simp only [mem_ofPred_eq, ← heq y hy, ← heq y₁ hy₁]
    exact hmax hy
  refine ⟨y₁, hy₁, hmax', ?_⟩
  rw [lipBoundAt_eq_iSup_posHomNorm_coderiv ⟨B, hB, hBb⟩ hr hcl]
  exact le_antisymm (iSup₂_le fun y hy ↦ hmax' hy) (le_iSup₂_of_le y₁ hy₁ le_rfl)

/-- Cor. 3.5 of [Mordukhovich 2018] (coderivative criterion for local Lipschitz continuity of
set-valued mappings): let `S` be locally bounded around `x₀`, with `gph S` closed over a ball
around `x₀`. Then `S` is locally Lipschitzian around `x₀` iff `D*S(x₀, y)(0) = {0}` for all
`y ∈ S x₀`. -/
theorem locallyLipschitzAt_iff_forall_coderiv_zero_eq (hbd : LocallyBoundedAt S x₀) {r : ℝ}
    (hr : 0 < r) (hcl : IsClosed (graph S ∩ closedBall x₀ r ×ˢ univ)) :
    LocallyLipschitzAt S x₀ ↔ ∀ y ∈ S x₀, coderiv S x₀ y 0 = {0} := by
  refine ⟨fun ⟨ℓ, h⟩ y hy ↦ (h.lipschitzLikeWith y).lipschitzLikeAt.coderiv_zero hy,
    fun h ↦ ?_⟩
  rcases (S x₀).eq_empty_or_nonempty with he | hne
  · exact ⟨0, locallyLipschitzWith_of_forall_lipschitzLikeWith hbd hr hcl
      fun y hy ↦ absurd hy (he ▸ notMem_empty y)⟩
  obtain ⟨y₁, hy₁, -, hlip⟩ := exists_isMaxOn_posHomNorm_coderiv hbd hr hcl hne
  rw [locallyLipschitzAt_iff_lipBoundAt_lt_top, hlip,
    ← lipBound_eq_posHomNorm_coderiv (locallyClosed_graph_of_isClosed_prod hr hcl y₁) hy₁,
    ← lipschitzLikeAt_iff_lipBound_lt_top,
    lipschitzLikeAt_iff_coderiv_zero_eq (locallyClosed_graph_of_isClosed_prod hr hcl y₁) hy₁]
  exact h y₁ hy₁

end Cor35

section Cor36

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {S : E → Set F} {x₀ : E} {y₀ : F}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Supporting hyperplanes in finite dimensions: if `C` is convex and `y ∈ C \ int C`, a nonzero
linear functional attains its maximum over `C` at `y`. When `int C = ∅`, `C` lies in a proper
affine subspace and the functional is constant on `C`. -/
theorem exists_ne_zero_forall_le_of_notMem_interior [FiniteDimensional ℝ F] {C : Set F}
    (hC : Convex ℝ C) {y : F} (hy : y ∈ C) (hint : y ∉ interior C) :
    ∃ f : StrongDual ℝ F, f ≠ 0 ∧ ∀ a ∈ C, f a ≤ f y := by
  by_cases hne : (interior C).Nonempty
  · exact geometric_hahn_banach_of_nonempty_interior_point hC hint hne
  have hspan : affineSpan ℝ C ≠ ⊤ := fun h ↦ hne (hC.interior_nonempty_iff_affineSpan_eq_top.2 h)
  have hdir : (affineSpan ℝ C).direction < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h ↦ hspan ?_
    exact (AffineSubspace.direction_eq_top_iff_of_nonempty
      ((nonempty_of_mem hy).mono (subset_affineSpan ℝ C))).1 h
  obtain ⟨f, hf0, hfker⟩ := Submodule.exists_le_ker_of_lt_top _ hdir
  refine ⟨LinearMap.toContinuousLinearMap f, fun h ↦ hf0 ?_, fun a ha ↦ le_of_eq ?_⟩
  · ext v
    simpa using congrArg (fun g : StrongDual ℝ F ↦ g v) h
  · have hmem : a - y ∈ (affineSpan ℝ C).direction :=
      AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ C ha) (subset_affineSpan ℝ C hy)
    have := hfker hmem
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
    simpa using this

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- The range `rge S = dom S⁻¹` is the projection of the graph. -/
theorem dom_invMap_eq_image_graph : dom (invMap S) = Prod.snd '' graph S := by
  ext y
  simp only [dom, invMap, mem_image, graph, Prod.exists, exists_eq_right]
  rfl

/-- [Mordukhovich 2018, proof of Cor. 3.6]: for a mapping with convex graph,
`ker D*S(x₀, y₀) = {0}` iff `y₀ ∈ int (rge S)`, in finite dimensions. -/
theorem coderivKer_eq_iff_mem_interior_of_convex [FiniteDimensional ℝ F]
    (hS : Convex ℝ (graph S)) (h₀ : y₀ ∈ S x₀) :
    coderivKer S x₀ y₀ = {0} ↔ y₀ ∈ interior (dom (invMap S)) := by
  have hker : ∀ v : StrongDual ℝ F, v ∈ coderivKer S x₀ y₀ ↔ ∀ y ∈ dom (invMap S), v y₀ ≤ v y := by
    intro v
    rw [mem_coderivKer_iff, mem_coderiv_of_convex hS h₀]
    simp only [zero_apply, zero_sub, neg_le_neg_iff]
    exact ⟨fun h y ⟨x, hx⟩ ↦ h x y hx, fun h x y hx ↦ h y ⟨x, hx⟩⟩
  have hconv : Convex ℝ (dom (invMap S)) := by
    rw [dom_invMap_eq_image_graph]
    exact hS.linear_image (LinearMap.snd ℝ E F)
  have hy₀ : y₀ ∈ dom (invMap S) := ⟨x₀, h₀⟩
  constructor
  · intro h
    by_contra hint
    obtain ⟨f, hf0, hf⟩ := exists_ne_zero_forall_le_of_notMem_interior hconv hy₀ hint
    have : -f ∈ coderivKer S x₀ y₀ := (hker _).2 fun y hy ↦ by
      simpa using hf y hy
    rw [h, mem_singleton_iff, neg_eq_zero] at this
    exact hf0 this
  · intro hint
    refine subset_antisymm (fun v hv ↦ ?_) (singleton_subset_iff.2 (zero_mem_coderivKer h₀))
    rw [hker] at hv
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
    have key : ∀ d : F, 0 ≤ v d := by
      intro d
      set t := ε / (2 * (‖d‖ + 1))
      have ht : 0 < t := by positivity
      have hmem : y₀ + t • d ∈ dom (invMap S) := hball (by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le]
        have : t * ‖d‖ < t * (‖d‖ + 1) := by nlinarith
        have h2 : t * (‖d‖ + 1) = ε / 2 := by simp only [t]; field_simp
        linarith)
      have := hv _ hmem
      rw [map_add, map_smul, smul_eq_mul] at this
      nlinarith
    refine mem_singleton_iff.2 (ContinuousLinearMap.ext fun d ↦ ?_)
    have h1 := key d
    have h2 := key (-d)
    rw [map_neg] at h2
    simp only [zero_apply]
    linarith

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- Cor. 3.6 of [Mordukhovich 2018] (metric regularity of convex-graph multifunctions): if
`gph S` is convex and locally closed around `(x₀, y₀) ∈ gph S`, then `S` is metrically regular
around `(x₀, y₀)` iff `y₀ ∈ int (rge S)`. -/
theorem metricallyRegularAt_iff_mem_interior_of_convex (hS : Convex ℝ (graph S))
    (hloc : ∃ ρ > 0, IsClosed (graph S ∩ closedBall (x₀, y₀) ρ)) (h₀ : y₀ ∈ S x₀) :
    MetricallyRegularAt S x₀ y₀ ↔ y₀ ∈ interior (dom (invMap S)) := by
  rw [metricallyRegularAt_iff_coderivKer_eq hloc h₀, coderivKer_eq_iff_mem_interior_of_convex hS h₀]

/-- Cor. 3.6 of [Mordukhovich 2018] (covering of convex-graph multifunctions): if `gph S` is
convex and locally closed around `(x₀, y₀) ∈ gph S`, then `S` has the covering property around
`(x₀, y₀)` iff `y₀ ∈ int (rge S)` (nontrivial domain space). -/
theorem hasCoveringAt_iff_mem_interior_of_convex [Nontrivial E] (hS : Convex ℝ (graph S))
    (hloc : ∃ ρ > 0, IsClosed (graph S ∩ closedBall (x₀, y₀) ρ)) (h₀ : y₀ ∈ S x₀) :
    HasCoveringAt S x₀ y₀ ↔ y₀ ∈ interior (dom (invMap S)) := by
  rw [hasCoveringAt_iff_coderivKer_eq hloc h₀, coderivKer_eq_iff_mem_interior_of_convex hS h₀]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The coderivative of a convex-graph mapping, as a mapping of `v` (Prop. 1.13 of
[Mordukhovich 2018]): `u ∈ D*S(x₀, y₀)(v)` iff `⟨u, x - x₀⟩ ≤ ⟨v, y - y₀⟩` on `gph S`. -/
theorem coderiv_eq_of_convex (hS : Convex ℝ (graph S)) (h₀ : y₀ ∈ S x₀) :
    coderiv S x₀ y₀ = fun v ↦ {u | ∀ x y, y ∈ S x → u (x - x₀) ≤ v (y - y₀)} := by
  ext v u
  rw [mem_coderiv_of_convex hS h₀]
  simp only [mem_ofPred_eq, map_sub]
  exact forall₃_congr fun _ _ _ ↦ by constructor <;> intro h <;> linarith

/-- Cor. 3.6 of [Mordukhovich 2018], exact regularity bound: for `gph S` convex and locally
closed around `(x₀, y₀) ∈ gph S`,
`reg S (x₀, y₀) = sup_{‖u‖ ≤ 1} {‖v‖ | ⟨u, x - x₀⟩ ≤ ⟨v, y - y₀⟩ for all (x, y) ∈ gph S}`
(the book writes `max`; attainment is not formalized). -/
theorem regBound_eq_of_convex (hS : Convex ℝ (graph S))
    (hloc : ∃ ρ > 0, IsClosed (graph S ∩ closedBall (x₀, y₀) ρ)) (h₀ : y₀ ∈ S x₀) :
    regBound S x₀ y₀ = posHomNorm (invMap fun v : StrongDual ℝ F ↦
      {u : StrongDual ℝ E | ∀ x y, y ∈ S x → u (x - x₀) ≤ v (y - y₀)}) := by
  rw [regBound_eq_posHomNorm_invMap_coderiv hloc h₀, coderiv_eq_of_convex hS h₀]

/-- Cor. 3.6 of [Mordukhovich 2018], exact covering bound: for `gph S` convex and locally closed
around `(x₀, y₀) ∈ gph S` (nontrivial domain space),
`cov S (x₀, y₀) = inf_{‖v‖ = 1} {‖u‖ | ⟨u, x - x₀⟩ ≤ ⟨v, y - y₀⟩ for all (x, y) ∈ gph S}`
(the book writes `min`; attainment is not formalized). -/
theorem covBound_eq_of_convex [Nontrivial E] (hS : Convex ℝ (graph S))
    (hloc : ∃ ρ > 0, IsClosed (graph S ∩ closedBall (x₀, y₀) ρ)) (h₀ : y₀ ∈ S x₀) :
    covBound S x₀ y₀ = posHomLowerNorm fun v : StrongDual ℝ F ↦
      {u : StrongDual ℝ E | ∀ x y, y ∈ S x → u (x - x₀) ≤ v (y - y₀)} := by
  rw [covBound_eq_posHomLowerNorm hloc h₀, coderiv_eq_of_convex hS h₀]

end Cor36

section SingleValued

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {f : E → F} {x₀ : E}


/-- In finite dimensions, `A : E →L F` is onto iff its adjoint `v ↦ v ∘ A` is injective
[Mordukhovich 2018, Exercise 1.53]. -/
theorem forall_comp_eq_zero_iff_surjective [FiniteDimensional ℝ F] (A : E →L[ℝ] F) :
    (∀ v : StrongDual ℝ F, v.comp A = 0 → v = 0) ↔ Function.Surjective A := by
  refine ⟨fun h ↦ ?_, fun hA v hv ↦ comp_injective_of_surjective hA (by simpa using hv)⟩
  by_contra hA
  have hlt : LinearMap.range (A : E →ₗ[ℝ] F) < ⊤ :=
    lt_top_iff_ne_top.2 fun htop ↦ hA (LinearMap.range_eq_top.1 htop)
  obtain ⟨g, hg0, hgker⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  refine hg0 (LinearMap.ext fun y ↦ ?_)
  have := h (LinearMap.toContinuousLinearMap g) (ContinuousLinearMap.ext fun x ↦ by
    simpa using hgker (LinearMap.mem_range_self (A : E →ₗ[ℝ] F) x))
  simpa using congrArg (fun w : StrongDual ℝ F ↦ w y) this

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

section Lipschitz

variable {U : Set E} {L : ℝ≥0}

/-- Cor. 3.7 of [Mordukhovich 2018] (metric regularity of locally Lipschitzian mappings): if
`f` is Lipschitz around `x₀`, then `f` is metrically regular around `x₀` iff
`0 ∈ ∂⟨v, f⟩(x₀)` implies `v = 0`. -/
theorem metricallyRegularAt_iff_of_lipschitz (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U) :
    MetricallyRegularAt (fun x ↦ ({f x} : Set F)) x₀ (f x₀) ↔
      ∀ v : StrongDual ℝ F, (0 : StrongDual ℝ E) ∈ subdiff (fun x ↦ ((v (f x) : ℝ) : EReal)) x₀ →
        v = 0 := by
  rw [metricallyRegularAt_iff_forall_zero_mem_coderiv
    (locallyClosed_graph_of_continuousOn hU hL.continuousOn)
    (mem_singleton (f x₀))]
  simp only [subdiff_comp_eq_coderiv hU hL]

/-- Cor. 3.7 of [Mordukhovich 2018] (covering of locally Lipschitzian mappings): if `f` is
Lipschitz around `x₀`, then `f` has the covering property around `x₀` iff `0 ∈ ∂⟨v, f⟩(x₀)`
implies `v = 0` (nontrivial domain space). -/
theorem hasCoveringAt_iff_of_lipschitz [Nontrivial E] (hU : U ∈ 𝓝 x₀)
    (hL : LipschitzOnWith L f U) :
    HasCoveringAt (fun x ↦ ({f x} : Set F)) x₀ (f x₀) ↔
      ∀ v : StrongDual ℝ F, (0 : StrongDual ℝ E) ∈ subdiff (fun x ↦ ((v (f x) : ℝ) : EReal)) x₀ →
        v = 0 := by
  rw [hasCoveringAt_iff_metricallyRegularAt (S := fun x ↦ ({f x} : Set F)) (x₀ := x₀)
    (mem_singleton (f x₀)), metricallyRegularAt_iff_of_lipschitz hU hL]

/-- Cor. 3.7 of [Mordukhovich 2018], exact regularity bound: for `f` Lipschitz around `x₀`,
`reg f (x₀) = sup {‖v‖ | u ∈ ∂⟨v, f⟩(x₀), ‖u‖ ≤ 1}` (the book writes `max`; attainment is not
formalized). -/
theorem regBound_eq_of_lipschitz (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U) :
    regBound (fun x ↦ ({f x} : Set F)) x₀ (f x₀) =
      posHomNorm (invMap fun v : StrongDual ℝ F ↦
        subdiff (fun x ↦ ((v (f x) : ℝ) : EReal)) x₀) := by
  rw [regBound_eq_posHomNorm_invMap_coderiv
    (locallyClosed_graph_of_continuousOn hU hL.continuousOn)
    (mem_singleton (f x₀))]
  congr 2
  ext v : 1
  exact (subdiff_comp_eq_coderiv hU hL v).symm

/-- Cor. 3.7 of [Mordukhovich 2018], exact covering bound: for `f` Lipschitz around `x₀`,
`cov f (x₀) = inf {‖u‖ | u ∈ ∂⟨v, f⟩(x₀), ‖v‖ = 1}` (nontrivial domain space; the book writes
`min`; attainment is not formalized). -/
theorem covBound_eq_of_lipschitz [Nontrivial E] (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U) :
    covBound (fun x ↦ ({f x} : Set F)) x₀ (f x₀) =
      posHomLowerNorm fun v : StrongDual ℝ F ↦ subdiff (fun x ↦ ((v (f x) : ℝ) : EReal)) x₀ := by
  rw [covBound_eq_posHomLowerNorm (locallyClosed_graph_of_continuousOn hU hL.continuousOn)
    (mem_singleton (f x₀))]
  congr 1
  ext v : 1
  exact (subdiff_comp_eq_coderiv hU hL v).symm

end Lipschitz

section Smooth

variable {f' : E → E →L[ℝ] F}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- A mapping differentiable around `x₀` is continuous on a neighborhood of `x₀`. -/
theorem continuousOn_of_eventually_hasFDerivAt (hf : ∀ᶠ x in 𝓝 x₀, HasFDerivAt f (f' x) x) :
    ∃ U ∈ 𝓝 x₀, ContinuousOn f U :=
  ⟨_, hf, fun _ hx ↦ (hx.continuousAt).continuousWithinAt⟩

/-- Cor. 3.8 of [Mordukhovich 2018] (metric regularity of smooth mappings): if `f` is of class
`C¹` around `x₀`, then `f` is metrically regular around `x₀` iff `∇f(x₀)` is onto (3.17). -/
theorem metricallyRegularAt_iff_surjective (hf : ∀ᶠ x in 𝓝 x₀, HasFDerivAt f (f' x) x)
    (hc : ContinuousAt f' x₀) :
    MetricallyRegularAt (fun x ↦ ({f x} : Set F)) x₀ (f x₀) ↔ Function.Surjective (f' x₀) := by
  obtain ⟨U, hU, hfU⟩ := continuousOn_of_eventually_hasFDerivAt hf
  rw [metricallyRegularAt_iff_forall_zero_mem_coderiv (locallyClosed_graph_of_continuousOn hU hfU)
    (mem_singleton (f x₀)), ← forall_comp_eq_zero_iff_surjective]
  simp only [coderiv_of_hasFDerivAt_of_continuousAt hf hc, mem_singleton_iff, eq_comm]

/-- Cor. 3.8 of [Mordukhovich 2018] (covering of smooth mappings): if `f` is of class `C¹` around
`x₀`, then `f` has the covering property around `x₀` iff `∇f(x₀)` is onto (nontrivial domain
space). -/
theorem hasCoveringAt_iff_surjective [Nontrivial E] (hf : ∀ᶠ x in 𝓝 x₀, HasFDerivAt f (f' x) x)
    (hc : ContinuousAt f' x₀) :
    HasCoveringAt (fun x ↦ ({f x} : Set F)) x₀ (f x₀) ↔ Function.Surjective (f' x₀) := by
  rw [hasCoveringAt_iff_metricallyRegularAt (S := fun x ↦ ({f x} : Set F)) (x₀ := x₀)
    (mem_singleton (f x₀)), metricallyRegularAt_iff_surjective hf hc]

/-- Cor. 3.8 of [Mordukhovich 2018], exact regularity bound (3.18): for `f` of class `C¹` around
`x₀`, `reg f (x₀) = ‖(∇f(x₀)*)⁻¹‖`, the norm (1.14) of the inverse of the adjoint
`v ↦ v ∘ ∇f(x₀)`. -/
theorem regBound_eq_of_hasFDerivAt (hf : ∀ᶠ x in 𝓝 x₀, HasFDerivAt f (f' x) x)
    (hc : ContinuousAt f' x₀) :
    regBound (fun x ↦ ({f x} : Set F)) x₀ (f x₀) =
      posHomNorm (invMap fun v : StrongDual ℝ F ↦ ({v.comp (f' x₀)} : Set (StrongDual ℝ E))) := by
  obtain ⟨U, hU, hfU⟩ := continuousOn_of_eventually_hasFDerivAt hf
  rw [regBound_eq_posHomNorm_invMap_coderiv (locallyClosed_graph_of_continuousOn hU hfU)
    (mem_singleton (f x₀))]
  congr 2
  ext v : 1
  exact coderiv_of_hasFDerivAt_of_continuousAt hf hc v

/-- Cor. 3.8 of [Mordukhovich 2018], exact covering bound (3.18): for `f` of class `C¹` around
`x₀`, `cov f (x₀) = inf {‖∇f(x₀)* v‖ | ‖v‖ = 1}` (nontrivial domain space; the book writes
`min`). -/
theorem covBound_eq_of_hasFDerivAt [Nontrivial E] (hf : ∀ᶠ x in 𝓝 x₀, HasFDerivAt f (f' x) x)
    (hc : ContinuousAt f' x₀) :
    covBound (fun x ↦ ({f x} : Set F)) x₀ (f x₀) =
      ⨅ (v : StrongDual ℝ F) (_ : ‖v‖ = 1), (‖v.comp (f' x₀)‖₊ : ℝ≥0∞) := by
  obtain ⟨U, hU, hfU⟩ := continuousOn_of_eventually_hasFDerivAt hf
  rw [covBound_eq_posHomLowerNorm (locallyClosed_graph_of_continuousOn hU hfU)
    (mem_singleton (f x₀)),
    posHomLowerNorm]
  refine iInf_congr fun v ↦ iInf_congr fun _ ↦ ?_
  simp [coderiv_of_hasFDerivAt_of_continuousAt hf hc v]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The norm (1.14) of the adjoint `u ↦ u ∘ B` of `B : F →L E` is `‖B‖` (Hahn–Banach). -/
theorem posHomNorm_comp (B : F →L[ℝ] E) :
    posHomNorm (fun u : StrongDual ℝ E ↦ ({u.comp B} : Set (StrongDual ℝ F))) = ‖B‖₊ := by
  refine le_antisymm (posHomNorm_le fun u w hw ↦ ?_) ?_
  · rw [mem_singleton_iff.1 hw, coe_nnnorm, mul_comm]
    exact u.opNorm_comp_le B
  · by_cases htop : posHomNorm (fun u : StrongDual ℝ E ↦ ({u.comp B} : Set (StrongDual ℝ F))) = ⊤
    · rw [htop]; exact le_top
    set c := (posHomNorm (fun u : StrongDual ℝ E ↦ ({u.comp B} : Set (StrongDual ℝ F))))
      |>.toNNReal
    have hc : posHomNorm (fun u : StrongDual ℝ E ↦ ({u.comp B} : Set (StrongDual ℝ F))) = c :=
      (ENNReal.coe_toNNReal htop).symm
    have hbound : ∀ u : StrongDual ℝ E, ‖u.comp B‖ ≤ c * ‖u‖ := fun u ↦
      norm_le_of_posHomNorm_le (fun t _ u w hw ↦ by
        rw [mem_singleton_iff.1 hw]; simp [ContinuousLinearMap.smul_comp]) hc.le
        (mem_singleton _)
    rw [hc, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm]
    refine B.opNorm_le_bound c.coe_nonneg fun y ↦ ?_
    refine NormedSpace.norm_le_dual_bound ℝ (B y) (by positivity) fun u ↦ ?_
    calc ‖u (B y)‖ = ‖(u.comp B) y‖ := rfl
      _ ≤ ‖u.comp B‖ * ‖y‖ := (u.comp B).le_opNorm y
      _ ≤ c * ‖u‖ * ‖y‖ := by gcongr; exact hbound u
      _ = c * ‖y‖ * ‖u‖ := by ring

/-- Cor. 3.8 of [Mordukhovich 2018], square case: if `∇f(x₀)` is invertible, with inverse
`A⁻¹ = e.symm`, then `cov f (x₀) = ‖∇f(x₀)⁻¹‖⁻¹` (nontrivial domain space). -/
theorem covBound_eq_inv_norm_symm [Nontrivial E] (hf : ∀ᶠ x in 𝓝 x₀, HasFDerivAt f (f' x) x)
    (hc : ContinuousAt f' x₀) (e : E ≃L[ℝ] F) (he : f' x₀ = e) :
    covBound (fun x ↦ ({f x} : Set F)) x₀ (f x₀) = (‖(e.symm : F →L[ℝ] E)‖₊ : ℝ≥0∞)⁻¹ := by
  obtain ⟨U, hU, hfU⟩ := continuousOn_of_eventually_hasFDerivAt hf
  have hH : coderiv (fun x ↦ ({f x} : Set F)) x₀ (f x₀) =
      fun v ↦ ({v.comp (e : E →L[ℝ] F)} : Set (StrongDual ℝ E)) := by
    ext v : 1
    rw [coderiv_of_hasFDerivAt_of_continuousAt hf hc v, he]
  have hinv : invMap (fun v : StrongDual ℝ F ↦ ({v.comp (e : E →L[ℝ] F)} : Set (StrongDual ℝ E)))
      = fun u ↦ {u.comp (e.symm : F →L[ℝ] E)} := by
    ext u v
    simp only [invMap, mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro rfl; ext y; simp
    · rintro rfl; ext y; simp
  rw [covBound_eq_posHomLowerNorm (locallyClosed_graph_of_continuousOn hU hfU)
    (mem_singleton (f x₀)), hH,
    ← inv_posHomNorm_invMap (fun t _ v u hu ↦ by
      rw [mem_singleton_iff.1 hu]; simp [ContinuousLinearMap.smul_comp]), hinv,
    posHomNorm_comp]

end Smooth

end SingleValued

end VariationalAnalysis
