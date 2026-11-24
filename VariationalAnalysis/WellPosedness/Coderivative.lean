/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis.Normal.Transport
import VariationalAnalysis.WellPosedness.Basic

/-!
# Coderivatives and well-posedness: the necessity halves of the Mordukhovich criterion

This file contains the coderivative side of [Mordukhovich 2018, Thm. 3.3] that does not need
the extremal principle: the norm (1.14) of positively homogeneous mappings, the kernel of the
coderivative, the coderivative of the inverse mapping, Step 1 of the proof of Thm. 3.3
(`‖D*S(x₀, y₀)‖ ≤ lip S (x₀, y₀)`), and the resulting necessity parts of Thm. 3.3(i)–(iii).
The sufficiency parts (Step 2 of the proof of Thm. 3.3) need Ekeland's variational principle and
the subdifferential sum rules of Ch. 2.

Everything here holds in arbitrary real normed spaces, with the limiting coderivative defined
through norm limits in the dual (`coderiv`); no closedness of the graph is needed.

## Main declarations

* `PosHomogeneous H`: `H` is positively homogeneous: `0 ∈ H 0` and `t H x ⊆ H (t x)` for
  `t > 0` [Mordukhovich 2018, p. 12].
* `posHomNorm H`: the norm `‖H‖ = sup {‖y‖ | y ∈ H x, ‖x‖ ≤ 1}` [Mordukhovich 2018, (1.14)], in
  `ℝ≥0∞`.
* `posHomLowerNorm H`: `inf {‖y‖ | y ∈ H x, ‖x‖ = 1}` (in `ℝ≥0∞`), the right-hand side of
  [Mordukhovich 2018, (3.7)] for `H = D*S(x₀, y₀)`.
* `coderivKer S x₀ y₀`: `ker D*S(x₀, y₀) = {v | 0 ∈ D*S(x₀, y₀)(v)}`
  [Mordukhovich 2018, (3.6)].

## Main results

* `inv_posHomNorm_invMap`: `‖H⁻¹‖⁻¹ = inf {‖y‖ | y ∈ H x, ‖x‖ = 1}` for positively homogeneous
  `H` [Mordukhovich 2018, proof of Thm. 3.3, Step 3].
* `mem_coderiv_invMap_iff`: `u ∈ D*S(x₀, y₀)(v) ↔ -v ∈ D*S⁻¹(y₀, x₀)(-u)`, and consequences:
  `posHomNorm_invMap_coderiv` (`‖D*S(x₀, y₀)⁻¹‖ = ‖D*S⁻¹(y₀, x₀)‖`, the second equality in
  (3.8)) and `coderiv_invMap_zero_eq_iff` (`D*S⁻¹(y₀, x₀)(0) = {0} ↔ ker D*S(x₀, y₀) = {0}`).
* `LipschitzLikeWith.norm_le_of_mem_coderiv`, `LipschitzLikeWith.posHomNorm_coderiv_le`,
  `posHomNorm_coderiv_le_lipBound`, `LipschitzLikeAt.coderiv_zero`: Step 1 of the proof of
  Thm. 3.3 of [Mordukhovich 2018]: (3.12), (3.11) and (3.9) (necessity in Thm. 3.3(iii))
  [Clason–Valkonen, Lemma 27.11].
* `MetricallyRegularAt.coderivKer_eq`, `posHomNorm_invMap_coderiv_le_regBound`: necessity in
  Thm. 3.3(ii) of [Mordukhovich 2018]: metric regularity implies `ker D*S(x₀, y₀) = {0}` and
  `‖D*S(x₀, y₀)⁻¹‖ ≤ reg S (x₀, y₀)` [Clason–Valkonen, Cor. 27.12].
* `HasCoveringAt.coderivKer_eq`, `covBound_le_posHomLowerNorm`: necessity in Thm. 3.3(i) of
  [Mordukhovich 2018]: covering implies `ker D*S(x₀, y₀) = {0}` and
  `cov S (x₀, y₀) ≤ inf {‖u‖ | u ∈ D*S(x₀, y₀)(v), ‖v‖ = 1}`.
-/

open Filter Topology Set Metric
open scoped NNReal ENNReal

namespace VariationalAnalysis

section PosHomogeneous

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

/-- A set-valued mapping `H` is positively homogeneous if `0 ∈ H 0` and `t H x ⊆ H (t x)` for
all `t > 0` [Mordukhovich 2018, p. 12], i.e. its graph is a cone. -/
def PosHomogeneous (H : X → Set Y) : Prop :=
  0 ∈ H 0 ∧ ∀ t : ℝ, 0 < t → ∀ x, ∀ y ∈ H x, t • y ∈ H (t • x)

/-- The norm of a positively homogeneous mapping [Mordukhovich 2018, (1.14)]:
`‖H‖ = sup {‖y‖ | y ∈ H x, ‖x‖ ≤ 1}`, in `ℝ≥0∞`. -/
noncomputable def posHomNorm (H : X → Set Y) : ℝ≥0∞ :=
  ⨆ (x : X) (_ : ‖x‖ ≤ 1) (y : Y) (_ : y ∈ H x), (‖y‖₊ : ℝ≥0∞)

/-- The lower norm `inf {‖y‖ | y ∈ H x, ‖x‖ = 1}` of a set-valued mapping, in `ℝ≥0∞`: the
right-hand side of [Mordukhovich 2018, (3.7)] for `H = D*S(x₀, y₀)`. For positively homogeneous
`H`, it equals `‖H⁻¹‖⁻¹` (`inv_posHomNorm_invMap`). -/
noncomputable def posHomLowerNorm (H : X → Set Y) : ℝ≥0∞ :=
  ⨅ (x : X) (_ : ‖x‖ = 1) (y : Y) (_ : y ∈ H x), (‖y‖₊ : ℝ≥0∞)

variable {H : X → Set Y}

/-- The inverse of a positively homogeneous mapping is positively homogeneous. -/
theorem PosHomogeneous.invMap (hH : PosHomogeneous H) : PosHomogeneous (invMap H) :=
  ⟨hH.1, fun t ht _ _ hx ↦ hH.2 t ht _ _ hx⟩

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] in
/-- The norm `‖H‖` bounds the values on the unit ball: `‖y‖ ≤ ‖H‖` for `y ∈ H x`, `‖x‖ ≤ 1`. -/
theorem nnnorm_le_posHomNorm {x : X} {y : Y} (hx : ‖x‖ ≤ 1) (hy : y ∈ H x) :
    (‖y‖₊ : ℝ≥0∞) ≤ posHomNorm H :=
  le_iSup₂_of_le (f := fun (x : X) (_ : ‖x‖ ≤ 1) ↦ ⨆ (y : Y) (_ : y ∈ H x), (‖y‖₊ : ℝ≥0∞))
    x hx (le_iSup₂_of_le (f := fun (y : Y) (_ : y ∈ H x) ↦ (‖y‖₊ : ℝ≥0∞)) y hy le_rfl)

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] in
/-- The lower norm bounds the values on the unit sphere from below:
`posHomLowerNorm H ≤ ‖y‖` for `y ∈ H x`, `‖x‖ = 1`. -/
theorem posHomLowerNorm_le_nnnorm {x : X} {y : Y} (hx : ‖x‖ = 1) (hy : y ∈ H x) :
    posHomLowerNorm H ≤ ‖y‖₊ :=
  iInf₂_le_of_le (f := fun (x : X) (_ : ‖x‖ = 1) ↦ ⨅ (y : Y) (_ : y ∈ H x), (‖y‖₊ : ℝ≥0∞))
    x hx (iInf₂_le_of_le (f := fun (y : Y) (_ : y ∈ H x) ↦ (‖y‖₊ : ℝ≥0∞)) y hy le_rfl)

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] in
/-- `‖H‖ ≤ c` as soon as `‖y‖ ≤ c ‖x‖` for all `y ∈ H x`. -/
theorem posHomNorm_le {c : ℝ≥0} (h : ∀ x, ∀ y ∈ H x, ‖y‖ ≤ c * ‖x‖) : posHomNorm H ≤ c := by
  refine iSup₂_le fun x hx ↦ iSup₂_le fun y hy ↦ ENNReal.coe_le_coe.2 ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm]
  calc ‖y‖ ≤ c * ‖x‖ := h x y hy
    _ ≤ c * 1 := by gcongr
    _ = c := mul_one _

/-- For a positively homogeneous `H` (it suffices that `gph H` is closed under multiplication by
positive scalars), `‖H‖ ≤ c < ∞` gives `‖y‖ ≤ c ‖x‖` for all `y ∈ H x`
[Mordukhovich 2018, proof of Thm. 3.3, Step 1]. -/
theorem norm_le_of_posHomNorm_le (hH : ∀ t : ℝ, 0 < t → ∀ x, ∀ y ∈ H x, t • y ∈ H (t • x))
    {c : ℝ≥0} (hc : posHomNorm H ≤ c) {x : X} {y : Y} (hy : y ∈ H x) : ‖y‖ ≤ c * ‖x‖ := by
  have key : ∀ x' : X, ‖x'‖ ≤ 1 → ∀ y' ∈ H x', ‖y'‖ ≤ c := by
    intro x' hx' y' hy'
    have := (nnnorm_le_posHomNorm hx' hy').trans hc
    rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm] at this
    exact this
  rcases eq_or_ne x 0 with rfl | hx
  · rw [norm_zero, mul_zero]
    by_contra hpos
    push Not at hpos
    have := key 0 (by simp) _ (by simpa using hH ((c + 1) / ‖y‖) (by positivity) 0 y hy)
    rw [norm_smul, Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ hpos.ne'] at this
    linarith
  · have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
    have := key _ (by rw [norm_smul, Real.norm_of_nonneg (by positivity),
      inv_mul_cancel₀ hxpos.ne']) _ (hH ‖x‖⁻¹ (by positivity) x y hy)
    rw [norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_le_iff₀ hxpos] at this
    linarith

/-- For positively homogeneous `H`: `‖H‖ ≤ c` iff `‖y‖ ≤ c ‖x‖` for all `y ∈ H x`. -/
theorem PosHomogeneous.posHomNorm_le_iff (hH : PosHomogeneous H) {c : ℝ≥0} :
    posHomNorm H ≤ c ↔ ∀ x, ∀ y ∈ H x, ‖y‖ ≤ c * ‖x‖ :=
  ⟨fun hc _ _ hy ↦ norm_le_of_posHomNorm_le hH.2 hc hy, posHomNorm_le⟩

/-- A positively homogeneous mapping of finite norm satisfies `H 0 = {0}`. -/
theorem PosHomogeneous.eq_zero_of_posHomNorm_ne_top (hH : PosHomogeneous H)
    (hfin : posHomNorm H ≠ ∞) : H 0 = {0} := by
  refine subset_antisymm (fun y hy ↦ ?_) (singleton_subset_iff.2 hH.1)
  have := norm_le_of_posHomNorm_le hH.2 (c := (posHomNorm H).toNNReal)
    (ENNReal.coe_toNNReal hfin).ge hy
  rw [norm_zero, mul_zero] at this
  exact norm_le_zero_iff.1 this

/-- [Mordukhovich 2018, proof of Thm. 3.3, Step 3]: for a mapping `H` whose graph is closed under
multiplication by positive scalars (e.g. a positively homogeneous one),
`‖H⁻¹‖⁻¹ = inf {‖y‖ | y ∈ H x, ‖x‖ = 1}`. -/
theorem inv_posHomNorm_invMap (hH : ∀ t : ℝ, 0 < t → ∀ x, ∀ y ∈ H x, t • y ∈ H (t • x)) :
    (posHomNorm (invMap H))⁻¹ = posHomLowerNorm H := by
  refine le_antisymm (le_iInf₂ fun x hx ↦ le_iInf₂ fun y hy ↦ ?_) ?_
  · -- `‖H⁻¹‖⁻¹ ≤ ‖y‖` for `y ∈ H x`, `‖x‖ = 1`
    rw [ENNReal.inv_le_iff_inv_le]
    rcases eq_or_ne y 0 with rfl | hy0
    · simp only [nnnorm_zero, ENNReal.coe_zero, ENNReal.inv_zero, top_le_iff]
      refine ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_
      have hmem : ((r : ℝ) + 1) • x ∈ invMap H ((r + 1 : ℝ) • (0 : Y)) :=
        hH ((r : ℝ) + 1) (by positivity) x 0 hy
      rw [smul_zero] at hmem
      refine le_trans ?_ (nnnorm_le_posHomNorm (by simp) hmem)
      rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, norm_smul, hx, mul_one,
        Real.norm_of_nonneg (by positivity)]
      linarith
    · have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy0
      have hmem : ‖y‖⁻¹ • x ∈ invMap H (‖y‖⁻¹ • y) := hH ‖y‖⁻¹ (by positivity) x y hy
      refine le_trans (le_of_eq ?_) (nnnorm_le_posHomNorm ?_ hmem)
      · rw [← ENNReal.coe_inv (nnnorm_ne_zero_iff.2 hy0), ENNReal.coe_inj, ← NNReal.coe_inj,
          NNReal.coe_inv, coe_nnnorm, coe_nnnorm, norm_smul, hx, mul_one,
          Real.norm_of_nonneg (by positivity)]
      · rw [norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ hypos.ne']
  · -- `inf ≤ ‖H⁻¹‖⁻¹`, i.e. `‖x‖ ≤ inf⁻¹` for `y ∈ H x`, `‖y‖ ≤ 1`
    rw [ENNReal.le_inv_iff_le_inv]
    refine iSup₂_le fun y hy ↦ iSup₂_le fun x hx ↦ ?_
    change y ∈ H x at hx
    rw [ENNReal.le_inv_iff_le_inv]
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    · have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
      have hmem : ‖x‖⁻¹ • y ∈ H (‖x‖⁻¹ • x) := hH ‖x‖⁻¹ (by positivity) x y hx
      refine (posHomLowerNorm_le_nnnorm ?_ hmem).trans ?_
      · rw [norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ hxpos.ne']
      · rw [← ENNReal.coe_inv (nnnorm_ne_zero_iff.2 hx0), ENNReal.coe_le_coe,
          ← NNReal.coe_le_coe, NNReal.coe_inv, coe_nnnorm, coe_nnnorm, norm_smul,
          Real.norm_of_nonneg (by positivity)]
        calc ‖x‖⁻¹ * ‖y‖ ≤ ‖x‖⁻¹ * 1 := by gcongr
          _ = ‖x‖⁻¹ := mul_one _

end PosHomogeneous

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {S : E → Set F} {x₀ : E} {y₀ : F} {u : StrongDual ℝ E} {v : StrongDual ℝ F}

section Inverse

/-- The kernel `ker D*S(x₀, y₀) = {v | 0 ∈ D*S(x₀, y₀)(v)}` of the coderivative
[Mordukhovich 2018, (3.6)]. -/
def coderivKer (S : E → Set F) (x₀ : E) (y₀ : F) : Set (StrongDual ℝ F) :=
  {v | (0 : StrongDual ℝ E) ∈ coderiv S x₀ y₀ v}

/-- Membership in the kernel of the coderivative: `v ∈ ker D*S(x₀, y₀)` iff
`0 ∈ D*S(x₀, y₀)(v)`. -/
theorem mem_coderivKer_iff : v ∈ coderivKer S x₀ y₀ ↔ (0 : StrongDual ℝ E) ∈ coderiv S x₀ y₀ v :=
  Iff.rfl

/-- The coderivative at a point of the graph is positively homogeneous. -/
theorem posHomogeneous_coderiv (h₀ : y₀ ∈ S x₀) : PosHomogeneous (coderiv S x₀ y₀) := by
  refine ⟨?_, fun t ht v u hu ↦ smul_mem_coderiv hu ht.le⟩
  change (0 : StrongDual ℝ E).coprod (-0) ∈ normalCone (graph S) (x₀, y₀)
  have h0 : (0 : StrongDual ℝ E).coprod (-(0 : StrongDual ℝ F)) = 0 := by ext <;> simp
  rw [h0]
  exact zero_mem_normalCone (show (x₀, y₀) ∈ graph S from h₀)

/-- For `(x₀, y₀) ∈ gph S`, the kernel `ker D*S(x₀, y₀)` contains `0`. -/
theorem zero_mem_coderivKer (h₀ : y₀ ∈ S x₀) : (0 : StrongDual ℝ F) ∈ coderivKer S x₀ y₀ :=
  (posHomogeneous_coderiv h₀).1

/-- The graph of `S⁻¹` is the image of `gph S` under the swap `(x, y) ↦ (y, x)`. -/
theorem graph_invMap_eq_image :
    graph (invMap S) = ContinuousLinearEquiv.prodComm ℝ E F '' graph S := by
  ext ⟨y, x⟩
  simp [graph, invMap]

/-- Normals to the graph of the inverse: `(a, b) ∈ N((y₀, x₀); gph S⁻¹)` iff
`(b, a) ∈ N((x₀, y₀); gph S)`. -/
theorem coprod_mem_normalCone_graph_invMap_iff {a : StrongDual ℝ F} {b : StrongDual ℝ E} :
    a.coprod b ∈ normalCone (graph (invMap S)) (y₀, x₀) ↔
      b.coprod a ∈ normalCone (graph S) (x₀, y₀) := by
  have h := mem_normalCone_image_iff (ContinuousLinearEquiv.prodComm ℝ E F) (Ω := graph S)
    (x₀ := (x₀, y₀)) (v := a.coprod b)
  rw [← graph_invMap_eq_image] at h
  have hcomp : (a.coprod b).comp
      (ContinuousLinearEquiv.prodComm ℝ E F : (E × F) →L[ℝ] (F × E)) = b.coprod a := by
    ext <;> simp
  rw [hcomp] at h
  exact h

/-- The coderivative of the inverse mapping [Mordukhovich 2018, proof of Thm. 3.3, Step 3]:
`u ∈ D*S(x₀, y₀)(v)` iff `-v ∈ D*S⁻¹(y₀, x₀)(-u)`. -/
theorem mem_coderiv_invMap_iff :
    u ∈ coderiv S x₀ y₀ v ↔ -v ∈ coderiv (invMap S) y₀ x₀ (-u) := by
  simp only [coderiv, mem_ofPred_eq, neg_neg]
  exact coprod_mem_normalCone_graph_invMap_iff.symm

/-- `v ∈ D*S(x₀, y₀)⁻¹(u)` iff `-v ∈ D*S⁻¹(y₀, x₀)(-u)`. -/
theorem mem_invMap_coderiv_iff :
    v ∈ invMap (coderiv S x₀ y₀) u ↔ -v ∈ coderiv (invMap S) y₀ x₀ (-u) :=
  mem_coderiv_invMap_iff

/-- The second equality in [Mordukhovich 2018, (3.8)]:
`‖D*S(x₀, y₀)⁻¹‖ = ‖D*S⁻¹(y₀, x₀)‖`. -/
theorem posHomNorm_invMap_coderiv :
    posHomNorm (invMap (coderiv S x₀ y₀)) = posHomNorm (coderiv (invMap S) y₀ x₀) := by
  refine le_antisymm (iSup₂_le fun w hw ↦ iSup₂_le fun v hv ↦ ?_)
    (iSup₂_le fun w hw ↦ iSup₂_le fun v hv ↦ ?_)
  · rw [← nnnorm_neg v]
    exact nnnorm_le_posHomNorm (by rwa [norm_neg]) (mem_invMap_coderiv_iff.1 hv)
  · have hv' : -v ∈ invMap (coderiv S x₀ y₀) (-w) := by
      rw [mem_invMap_coderiv_iff, neg_neg, neg_neg]; exact hv
    rw [← nnnorm_neg v]
    exact nnnorm_le_posHomNorm (by rwa [norm_neg]) hv'

/-- [Mordukhovich 2018, proof of Thm. 3.3, Step 3]: `D*S⁻¹(y₀, x₀)(0) = {0}` iff
`ker D*S(x₀, y₀) = {0}`. -/
theorem coderiv_invMap_zero_eq_iff :
    coderiv (invMap S) y₀ x₀ 0 = {0} ↔ coderivKer S x₀ y₀ = {0} := by
  have key : ∀ w : StrongDual ℝ F, w ∈ coderiv (invMap S) y₀ x₀ 0 ↔ -w ∈ coderivKer S x₀ y₀ := by
    intro w
    rw [mem_coderivKer_iff, mem_coderiv_invMap_iff (S := S), neg_neg, neg_zero]
  constructor
  · intro h
    ext w
    have := key (-w)
    rw [neg_neg, h, mem_singleton_iff, neg_eq_zero] at this
    rw [mem_singleton_iff, this]
  · intro h
    ext w
    rw [key, h, mem_singleton_iff, mem_singleton_iff, neg_eq_zero]

end Inverse

section Necessity

variable {κ μ ℓ : ℝ≥0}

/-- Step 1 of the proof of Thm. 3.3 of [Mordukhovich 2018], for regular coderivatives: if `S`
is Lipschitz-like around `(x, y)` with modulus `ℓ`, then `‖u‖ ≤ ℓ ‖v‖` for every
`u ∈ D̂*S(x, y)(v)`. -/
theorem LipschitzLikeWith.norm_le_of_mem_regularCoderiv {x : E} {y : F}
    (h : LipschitzLikeWith ℓ S x y) (hu : u ∈ regularCoderiv S x y v) : ‖u‖ ≤ ℓ * ‖v‖ := by
  obtain ⟨hxy, hN⟩ := hu
  change y ∈ S x at hxy
  obtain ⟨U, hU, V, hV, H⟩ := h
  obtain ⟨η, hη, hηU⟩ := Metric.mem_nhds_iff.1 hU
  have hℓ : (0 : ℝ) ≤ ℓ := ℓ.coe_nonneg
  have key : ∀ d : E, u d ≤ ℓ * ‖v‖ * ‖d‖ := by
    intro d
    rcases eq_or_ne d 0 with rfl | hd
    · simp
    have hdpos : 0 < ‖d‖ := norm_pos_iff.2 hd
    refine le_of_forall_pos_le_add_mul (c := (1 + ℓ) * ‖d‖) fun ε hε ↦ ?_
    obtain ⟨δ, hδ, hball⟩ :=
      Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 (hN ε hε))
    set ρ := min δ η
    have hρ : 0 < ρ := lt_min hδ hη
    set t := ρ / (2 * (1 + ℓ) * ‖d‖)
    have ht : 0 < t := by positivity
    have htd : (1 + ℓ) * (t * ‖d‖) = ρ / 2 := by
      simp only [t]; field_simp
    have htd' : t * ‖d‖ ≤ (1 + ℓ) * (t * ‖d‖) := le_mul_of_one_le_left (by positivity)
      (by linarith)
    have hzx : dist (x + t • d) x = t * ‖d‖ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le]
    have hzU : x + t • d ∈ U := hηU (by
      rw [mem_ball, hzx]; linarith [min_le_right δ η])
    obtain ⟨w, hw, hyw⟩ := H x (mem_of_mem_nhds hU) _ hzU y ⟨hxy, mem_of_mem_nhds hV⟩
    rw [dist_comm x, hzx] at hyw
    have hwy : ‖w - y‖ ≤ ℓ * (t * ‖d‖) := by rw [← dist_eq_norm, dist_comm]; exact hyw
    have hnorm : ‖(t • d, w - y)‖ ≤ (1 + ℓ) * (t * ‖d‖) := by
      refine norm_prod_le_iff.2 ⟨?_, hwy.trans (by nlinarith)⟩
      rw [norm_smul, Real.norm_of_nonneg ht.le]; exact htd'
    have hdist : dist (x + t • d, w) (x, y) < δ := by
      rw [dist_eq_norm, Prod.mk_sub_mk, add_sub_cancel_left]
      linarith [min_le_left δ η]
    have hmain := hball hdist hw
    simp only [Prod.mk_sub_mk, add_sub_cancel_left, ContinuousLinearMap.coprod_apply, neg_apply,
      map_smul, smul_eq_mul] at hmain
    have hv : v (w - y) ≤ ‖v‖ * (ℓ * (t * ‖d‖)) :=
      (le_abs_self _).trans ((v.le_opNorm _).trans (by gcongr))
    have hε' : ε * ‖(t • d, w - y)‖ ≤ ε * ((1 + ℓ) * (t * ‖d‖)) := by gcongr
    have : t * u d ≤ t * (ℓ * ‖v‖ * ‖d‖ + ε * ((1 + ℓ) * ‖d‖)) := by nlinarith
    exact le_of_mul_le_mul_left this ht
  refine ContinuousLinearMap.opNorm_le_bound u (by positivity) fun d ↦ abs_le.2 ⟨?_, key d⟩
  have := key (-d)
  rw [map_neg, norm_neg] at this
  linarith

/-- Step 1 of the proof of Thm. 3.3 of [Mordukhovich 2018]: if `S` is Lipschitz-like around
`(x₀, y₀)` with modulus `ℓ`, then `‖u‖ ≤ ℓ ‖v‖` for every `u ∈ D*S(x₀, y₀)(v)`. The proof uses
the limiting representation (1.17) and the robustness of the Lipschitz-like property; no
closedness of `gph S` is needed. -/
theorem LipschitzLikeWith.norm_le_of_mem_coderiv (h : LipschitzLikeWith ℓ S x₀ y₀)
    (hu : u ∈ coderiv S x₀ y₀ v) : ‖u‖ ≤ ℓ * ‖v‖ := by
  have hg : (x₀, y₀) ∈ graph S := hu.1
  rw [coderiv_eq_outerLimit hg] at hu
  obtain ⟨a, w, ha, hw, hmem⟩ := hu
  have ha1 : Tendsto (fun k ↦ (a k).1) atTop (𝓝 (x₀, y₀)) :=
    (tendsto_fst.comp ha).mono_right nhdsWithin_le_nhds
  have ha2 : Tendsto (fun k ↦ (a k).2) atTop (𝓝 v) := tendsto_snd.comp ha
  have hle : ∀ᶠ k in atTop, ‖w k‖ ≤ ℓ * ‖(a k).2‖ :=
    (ha1.eventually h.eventually).mono fun k hk ↦ hk.norm_le_of_mem_regularCoderiv (hmem k)
  exact le_of_tendsto_of_tendsto hw.norm (ha2.norm.const_mul _) hle

/-- (3.12) in the proof of Thm. 3.3 of [Mordukhovich 2018]: if `S` is Lipschitz-like around
`(x₀, y₀)` with modulus `ℓ`, then `‖D*S(x₀, y₀)‖ ≤ ℓ`. -/
theorem LipschitzLikeWith.posHomNorm_coderiv_le (h : LipschitzLikeWith ℓ S x₀ y₀) :
    posHomNorm (coderiv S x₀ y₀) ≤ ℓ :=
  posHomNorm_le fun _ _ hu ↦ h.norm_le_of_mem_coderiv hu

/-- (3.11) in the proof of Thm. 3.3 of [Mordukhovich 2018] (Step 1):
`‖D*S(x₀, y₀)‖ ≤ lip S (x₀, y₀)`; the right-hand side is finite iff `S` is Lipschitz-like
around `(x₀, y₀)` (`lipschitzLikeAt_iff_lipBound_lt_top`). This is the inequality `≤` in
(3.10). -/
theorem posHomNorm_coderiv_le_lipBound :
    posHomNorm (coderiv S x₀ y₀) ≤ lipBound S x₀ y₀ :=
  le_lipBound fun _ hℓ ↦ hℓ.posHomNorm_coderiv_le

/-- (3.9) of [Mordukhovich 2018] (Step 1 of the proof of Thm. 3.3; necessity in Thm. 3.3(iii)):
if `S` is Lipschitz-like around `(x₀, y₀) ∈ gph S`, then `D*S(x₀, y₀)(0) = {0}`
[Clason–Valkonen, Lemma 27.11]. -/
theorem LipschitzLikeAt.coderiv_zero (h : LipschitzLikeAt S x₀ y₀) (h₀ : y₀ ∈ S x₀) :
    coderiv S x₀ y₀ 0 = {0} := by
  obtain ⟨ℓ, hℓ⟩ := h
  exact (posHomogeneous_coderiv h₀).eq_zero_of_posHomNorm_ne_top
    (ne_top_of_le_ne_top ENNReal.coe_ne_top hℓ.posHomNorm_coderiv_le)

/-- Necessity in Thm. 3.3(ii) of [Mordukhovich 2018], quantitative form: if `S` is metrically
regular around `(x₀, y₀)` with modulus `μ`, then `‖v‖ ≤ μ ‖u‖` for every `u ∈ D*S(x₀, y₀)(v)`
(via Thm. 3.2(ii), Step 1 for `S⁻¹` and the coderivative of the inverse). -/
theorem MetricallyRegularWith.norm_le_of_mem_coderiv (h : MetricallyRegularWith μ S x₀ y₀)
    (hu : u ∈ coderiv S x₀ y₀ v) : ‖v‖ ≤ μ * ‖u‖ := by
  have hu' := mem_coderiv_invMap_iff.1 hu
  refine le_of_forall_pos_le_add_mul (c := ‖u‖) fun ε hε ↦ ?_
  have hlip : LipschitzLikeWith (μ + ε.toNNReal) (invMap S) y₀ x₀ :=
    MetricallyRegularWith.lipschitzLikeWith_of_invMap (S := invMap S) h
      (lt_add_of_pos_right _ (Real.toNNReal_pos.2 hε))
  have := hlip.norm_le_of_mem_coderiv hu'
  rw [norm_neg, norm_neg, NNReal.coe_add, Real.coe_toNNReal _ hε.le, add_mul] at this
  exact this

/-- Necessity in Thm. 3.3(ii) of [Mordukhovich 2018], (3.8) `≤`:
`‖D*S(x₀, y₀)⁻¹‖ ≤ reg S (x₀, y₀)`. -/
theorem posHomNorm_invMap_coderiv_le_regBound :
    posHomNorm (invMap (coderiv S x₀ y₀)) ≤ regBound S x₀ y₀ :=
  le_regBound fun _ hμ ↦ posHomNorm_le fun _ _ hv ↦ hμ.norm_le_of_mem_coderiv hv

/-- Necessity in Thm. 3.3(ii) of [Mordukhovich 2018], (3.8) `≤`:
`‖D*S⁻¹(y₀, x₀)‖ ≤ reg S (x₀, y₀)`. -/
theorem posHomNorm_coderiv_invMap_le_regBound :
    posHomNorm (coderiv (invMap S) y₀ x₀) ≤ regBound S x₀ y₀ :=
  posHomNorm_invMap_coderiv.symm.trans_le posHomNorm_invMap_coderiv_le_regBound

/-- Necessity in Thm. 3.3(ii) of [Mordukhovich 2018], in the form of (3.7):
`reg S (x₀, y₀)⁻¹ ≤ inf {‖u‖ | u ∈ D*S(x₀, y₀)(v), ‖v‖ = 1}`. -/
theorem inv_regBound_le_posHomLowerNorm (h₀ : y₀ ∈ S x₀) :
    (regBound S x₀ y₀)⁻¹ ≤ posHomLowerNorm (coderiv S x₀ y₀) := by
  rw [← inv_posHomNorm_invMap (posHomogeneous_coderiv h₀).2]
  exact ENNReal.inv_le_inv.2 posHomNorm_invMap_coderiv_le_regBound

/-- Necessity in Thm. 3.3(ii) of [Mordukhovich 2018]: if `S` is metrically regular around
`(x₀, y₀) ∈ gph S`, then `ker D*S(x₀, y₀) = {0}` (3.6)
[Clason–Valkonen, Cor. 27.12]. -/
theorem MetricallyRegularAt.coderivKer_eq (h : MetricallyRegularAt S x₀ y₀) (h₀ : y₀ ∈ S x₀) :
    coderivKer S x₀ y₀ = {0} := by
  obtain ⟨μ, hμ⟩ := h
  refine subset_antisymm (fun v hv ↦ ?_) (singleton_subset_iff.2 (zero_mem_coderivKer h₀))
  have := hμ.norm_le_of_mem_coderiv hv
  rw [norm_zero, mul_zero] at this
  exact norm_le_zero_iff.1 this

/-- Necessity in Thm. 3.3(i) of [Mordukhovich 2018], quantitative form: if `S` has the covering
property around `(x₀, y₀) ∈ gph S` with modulus `κ`, then `κ ‖v‖ ≤ ‖u‖` for every
`u ∈ D*S(x₀, y₀)(v)`. -/
theorem HasCoveringWith.mul_norm_le_of_mem_coderiv (h : HasCoveringWith κ S x₀ y₀)
    (h₀ : y₀ ∈ S x₀) (hu : u ∈ coderiv S x₀ y₀ v) : κ * ‖v‖ ≤ ‖u‖ := by
  have := (h.metricallyRegularWith h₀).norm_le_of_mem_coderiv hu
  have hκ : (0 : ℝ) < κ := h.pos
  rw [NNReal.coe_inv, ← div_eq_inv_mul, le_div_iff₀ hκ] at this
  linarith

/-- Necessity in Thm. 3.3(i) of [Mordukhovich 2018], (3.7) `≤`:
`cov S (x₀, y₀) ≤ inf {‖u‖ | u ∈ D*S(x₀, y₀)(v), ‖v‖ = 1}`. -/
theorem covBound_le_posHomLowerNorm (h₀ : y₀ ∈ S x₀) :
    covBound S x₀ y₀ ≤ posHomLowerNorm (coderiv S x₀ y₀) := by
  refine covBound_le fun κ hκ ↦ le_iInf₂ fun v hv ↦ le_iInf₂ fun u hu ↦ ?_
  have := hκ.mul_norm_le_of_mem_coderiv h₀ hu
  rw [hv, mul_one] at this
  exact ENNReal.coe_le_coe.2 (by rw [← NNReal.coe_le_coe, coe_nnnorm]; exact this)

/-- Necessity in Thm. 3.3(i) of [Mordukhovich 2018]: if `S` has the covering property around
`(x₀, y₀) ∈ gph S`, then `ker D*S(x₀, y₀) = {0}` (3.6). -/
theorem HasCoveringAt.coderivKer_eq (h : HasCoveringAt S x₀ y₀) (h₀ : y₀ ∈ S x₀) :
    coderivKer S x₀ y₀ = {0} := by
  obtain ⟨κ, hκ⟩ := h
  exact (hκ.metricallyRegularWith h₀).metricallyRegularAt.coderivKer_eq h₀

end Necessity

end VariationalAnalysis
