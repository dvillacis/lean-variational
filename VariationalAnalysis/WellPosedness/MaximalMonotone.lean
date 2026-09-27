/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import ConvexAnalysis.Extended.AffineMinorantExistence
import ConvexAnalysis.Extended.Epigraph
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import VariationalAnalysis.WellPosedness.Monotone

/-!
# Maximal monotonicity of convex subdifferentials

The subgradient mapping of a proper l.s.c. convex function `φ : ℝⁿ → (-∞, ∞]` is globally maximal
monotone (Moreau, Rockafellar); [Mordukhovich 2018] uses this in the proof of Cor. 3.26 and
recalls it on p. 179. We prove it in finite-dimensional real normed spaces, with the classical
argument: if `(x, v)` is monotonically related to `gph ∂φ`, a minimizer `y` of
`φ - v + ‖e(· - x)‖²` (for a Euclidean structure `e = toEuclidean`) exists by coercivity, and the
Fermat rule gives `v - 2 ⟨e(y - x), e(·)⟩ ∈ ∂φ(y)`; monotonicity forces `y = x`.

Coercivity comes from an affine minorant of `φ` (`exists_affine_minorant_of_convex`), obtained
from `exists_inner_minorant_of_proper_convex` of `ConvexAnalysis` (Rockafellar, Cor. 12.1.2).

## Main results

* `exists_affine_minorant_of_convex`: a proper convex function on a finite-dimensional normed
  space has an affine minorant `w - b`.
* `globallyMaximalMonotone_subdiff_of_convex`: [Mordukhovich 2018, p. 179, proof of Cor. 3.26]:
  the subdifferential of a proper l.s.c. convex function is globally maximal monotone.
-/

open Filter Topology Set Metric

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {φ : E → EReal}

/-- A proper convex function (never `⊥`, somewhere finite) on a finite-dimensional normed space
has an affine minorant: `w y - b ≤ φ y` for some `w ∈ E*`, `b ∈ ℝ` (Rockafellar, Cor. 12.1.2,
via `exists_inner_minorant_of_proper_convex` of `ConvexAnalysis` and `toEuclidean`). -/
theorem exists_affine_minorant_of_convex (hconv : Convex ℝ (φ.Epi univ)) (hbot : ∀ y, φ y ≠ ⊥)
    (hdom : ∃ y, φ y ≠ ⊤) :
    ∃ w : StrongDual ℝ E, ∃ b : ℝ, ∀ y, ((w y - b : ℝ) : EReal) ≤ φ y := by
  set G := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  set e : E ≃L[ℝ] G := toEuclidean
  set f : G → EReal := fun z ↦ φ (e.symm z)
  have hfp : ProperFunction univ f := by
    obtain ⟨y, hy⟩ := hdom
    refine ⟨fun z _ ↦ bot_lt_iff_ne_bot.2 (hbot _), Or.inr ⟨e y, mem_univ _, ?_⟩⟩
    simpa [f] using lt_top_iff_ne_top.2 hy
  have hfe : Convex ℝ (f.Epi univ) := by
    intro p hp q hq a b ha hb hab
    have := (hconv (x := (e.symm p.1, p.2)) ⟨mem_univ _, hp.2⟩ (y := (e.symm q.1, q.2))
      ⟨mem_univ _, hq.2⟩ ha hb hab).2
    refine ⟨mem_univ _, ?_⟩
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at this ⊢
    simpa [f, map_add, map_smul] using this
  obtain ⟨a, b, hab⟩ := exists_inner_minorant_of_proper_convex hfp (convex_epigraph_convex hfe)
  refine ⟨(innerSL ℝ a).comp (e : E →L[ℝ] G), b, fun y ↦ ?_⟩
  have := hab (e y)
  simp only [f, ContinuousLinearEquiv.symm_apply_apply] at this
  rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, real_inner_comm, EReal.coe_sub]
  exact this

/-- The subdifferential of a proper l.s.c. convex function `φ` (never `⊥`, finite somewhere) on a
finite-dimensional normed space is globally maximal monotone (Moreau, Rockafellar;
[Mordukhovich 2018, p. 179], used in the proof of Cor. 3.26). -/
theorem globallyMaximalMonotone_subdiff_of_convex (hconv : Convex ℝ (φ.Epi univ))
    (hlsc : LowerSemicontinuous φ) (hbot : ∀ y, φ y ≠ ⊥) (hdom : ∃ y, φ y ≠ ⊤) :
    GloballyMaximalMonotone (subdiff φ) := by
  rw [globallyMaximalMonotone_iff]
  refine ⟨globallyMonotone_subdiff_of_convex hconv, fun x v H ↦ ?_⟩
  obtain ⟨w, b, hwb⟩ := exists_affine_minorant_of_convex hconv hbot hdom
  set G := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  set e : E ≃L[ℝ] G := toEuclidean
  set h : E → ℝ := fun y ↦ -v y + ‖e y - e x‖ ^ 2 with h_def
  set h' : E → StrongDual ℝ E := fun y ↦ -v + 2 • (innerSL ℝ (e y - e x)).comp (e : E →L[ℝ] G)
    with h'_def
  have hh : ∀ y, HasFDerivAt h (h' y) y := fun y ↦
    v.hasFDerivAt.neg.add ((e : E →L[ℝ] G).hasFDerivAt.sub_const (e x)).norm_sq
  have hhc : Continuous h := continuous_iff_continuousAt.2 fun y ↦ (hh y).continuousAt
  set ψ : E → EReal := fun y ↦ φ y + (h y : EReal) with hψ_def
  have hψlsc : LowerSemicontinuous ψ :=
    hlsc.add' (continuous_coe_real_ereal.comp hhc).lowerSemicontinuous fun y ↦
      EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
  -- a point of the domain, and the sublevel set through it
  obtain ⟨y₀, hy₀⟩ := hdom
  set c₀ : ℝ := (φ y₀).toReal + h y₀
  have hc₀ : ψ y₀ = c₀ := by
    rw [hψ_def, EReal.coe_add, EReal.coe_toReal hy₀ (hbot y₀)]
  set K := {y | ψ y ≤ c₀}
  have hKc : IsClosed K := hψlsc.isClosed_preimage (c₀ : EReal)
  -- coercivity: `K` is bounded
  set M := ‖(e.symm : G →L[ℝ] E)‖
  set C₁ := |c₀ + b + (v - w) x|
  set C₂ := ‖v - w‖ * M
  have hKb : Bornology.IsBounded K := by
    refine (isBounded_closedBall (x := x) (r := M * max 1 (C₁ + C₂))).subset fun y hy ↦ ?_
    have hle : ((w y - b + h y : ℝ) : EReal) ≤ c₀ := by
      rw [EReal.coe_add]
      exact (add_le_add (hwb y) le_rfl).trans hy
    rw [EReal.coe_le_coe_iff] at hle
    set s := ‖e y - e x‖ with hs_def
    have hs : 0 ≤ s := norm_nonneg _
    have hts : ‖y - x‖ ≤ M * s := by
      have := (e.symm : G →L[ℝ] E).le_opNorm (e y - e x)
      rwa [← map_sub, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
        map_sub] at this
    have hM : 0 ≤ M := norm_nonneg _
    have hvw : (v - w) (y - x) ≤ C₂ * s := by
      calc (v - w) (y - x) ≤ ‖(v - w) (y - x)‖ := le_abs_self _
        _ ≤ ‖v - w‖ * ‖y - x‖ := (v - w).le_opNorm _
        _ ≤ ‖v - w‖ * (M * s) := by gcongr
        _ = C₂ * s := by ring
    have hsq : s ^ 2 ≤ C₁ + C₂ * s := by
      have e1 : (v - w) (y - x) = v y - w y - (v - w) x := by
        simp only [map_sub, sub_apply]
      have e2 : c₀ + b + (v - w) x ≤ C₁ := le_abs_self _
      simp only [h_def] at hle
      rw [e1] at hvw
      nlinarith
    have hC₁ : 0 ≤ C₁ := abs_nonneg _
    have hC₂ : 0 ≤ C₂ := by positivity
    have hsR : s ≤ max 1 (C₁ + C₂) := by
      rcases le_or_gt s 1 with h1 | h1
      · exact h1.trans (le_max_left _ _)
      · refine le_max_of_le_right ?_
        by_contra hcon
        push Not at hcon
        nlinarith
    rw [mem_closedBall, dist_eq_norm]
    exact hts.trans (by gcongr)
  -- a minimizer of `ψ`
  obtain ⟨ys, hysK, hmin⟩ := (hψlsc.lowerSemicontinuousOn K).exists_isMinOn
    ⟨y₀, show ψ y₀ ≤ c₀ from hc₀.le⟩ (Metric.isCompact_of_isClosed_isBounded hKc hKb)
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
    show φ ys + ((h ys : ℝ) : EReal) = _
    rw [hr, ← EReal.coe_add]
  -- the Fermat rule
  have h0 := zero_mem_regularSubdiff_of_isLocalMin
    (Eventually.of_forall hglob : IsLocalMin ψ ys) hψr
  have hmem : 0 - h' ys ∈ subdiff φ ys := by
    rw [subdiff_eq_regularSubdiff_of_convex hconv]
    exact (mem_regularSubdiff_add_iff (hh ys)).1 h0
  have hmono := H ys _ hmem
  have hkey : (v - (0 - h' ys)) (x - ys) = -(2 * ‖e ys - e x‖ ^ 2) := by
    have hA : v - (0 - h' ys) = 2 • (innerSL ℝ (e ys - e x)).comp (e : E →L[ℝ] G) := by
      simp only [h'_def]; abel
    rw [hA]
    simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, innerSL_apply_apply]
    rw [show e (x - ys) = -(e ys - e x) by rw [map_sub]; abel, inner_neg_right,
      real_inner_self_eq_norm_sq]
    ring
  rw [hkey] at hmono
  have hys : ys = x := by
    have : ‖e ys - e x‖ ^ 2 ≤ 0 := by linarith
    have : ‖e ys - e x‖ = 0 := by nlinarith [norm_nonneg (e ys - e x)]
    exact e.injective (sub_eq_zero.1 (norm_eq_zero.1 this))
  subst hys
  have : 0 - h' ys = v := by simp [h'_def]
  rwa [this] at hmem

end VariationalAnalysis
