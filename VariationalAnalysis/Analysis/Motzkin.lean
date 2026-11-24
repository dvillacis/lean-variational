/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Analysis.LocallyConvex.Separation
import VariationalAnalysis.Coderivative.SecondOrder

/-!
# Motzkin's theorem of the alternative

A form of Motzkin's theorem of the alternative [Mordukhovich 2024, Lemma 3.1] in a
finite-dimensional normed space, with equality constraints in place of the nonnegativity
constraints `Bx ≥ 0`: if the system `⟨ηᵢ, d⟩ < 0` (`i ∈ A`), `⟨ξₖ, d⟩ = 0` has no solution, then
`∑ λᵢ ηᵢ + ∑ μₖ ξₖ = 0` for some `λ ≥ 0`, `λ ≠ 0`, supported on `A`.

The proof separates `0` from the closed convex set `co {ηᵢ | i ∈ A} + span {ξₖ}`.

## References

* B. S. Mordukhovich, *Second-Order Variational Analysis in Optimization, Variational Stability,
  and Control*, Springer, 2024.
-/

open Filter Topology Set
open scoped Pointwise

namespace VariationalAnalysis

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  {I K : Type*} [Fintype I] [Fintype K]

/-- Motzkin's theorem of the alternative: if the system `⟨ηᵢ, d⟩ < 0` (`i ∈ A`), `⟨ξₖ, d⟩ = 0`
has no solution, then `∑ λᵢ ηᵢ + ∑ μₖ ξₖ = 0` for some `λ ≥ 0`, `λ ≠ 0`, supported on `A`. -/
theorem exists_multipliers_of_not_exists_direction (η : I → StrongDual ℝ X)
    (ξ : K → StrongDual ℝ X) (A : Set I)
    (h : ¬ ∃ d : X, (∀ i ∈ A, η i d < 0) ∧ ∀ k, ξ k d = 0) :
    ∃ lam : I → ℝ, ∃ μ : K → ℝ, (∀ i, 0 ≤ lam i) ∧ (∀ i ∉ A, lam i = 0) ∧ lam ≠ 0 ∧
      ∑ i, lam i • η i + ∑ k, μ k • ξ k = 0 := by
  classical
  rcases A.eq_empty_or_nonempty with hA | ⟨i₀, hi₀⟩
  · exact absurd ⟨0, by simp [hA], by simp⟩ h
  by_contra hne
  push Not at hne
  set Δ : Set (I → ℝ) := {lam | (∀ i, 0 ≤ lam i) ∧ (∀ i ∉ A, lam i = 0) ∧ ∑ i, lam i = 1}
  set T : (I → ℝ) → StrongDual ℝ X := fun lam ↦ ∑ i, lam i • η i
  set S₂ : Submodule ℝ (StrongDual ℝ X) := Submodule.span ℝ (range ξ)
  set S : Set (StrongDual ℝ X) := T '' Δ + (S₂ : Set (StrongDual ℝ X))
  -- `Δ` is a compact convex set and `S` is closed and convex
  have hΔc : Convex ℝ Δ := by
    rintro a ⟨ha0, haA, ha1⟩ b ⟨hb0, hbA, hb1⟩ s t hs ht hst
    refine ⟨fun i ↦ ?_, fun i hi ↦ ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := ha0 i
      have := hb0 i
      positivity
    · simp [haA i hi, hbA i hi]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, ha1, hb1, mul_one, hst]
  have hΔcl : IsClosed Δ := by
    have : Δ = (⋂ i, {lam : I → ℝ | 0 ≤ lam i}) ∩ (⋂ i ∈ Aᶜ, {lam : I → ℝ | lam i = 0}) ∩
        {lam | ∑ i, lam i = 1} := by
      ext lam
      simp [Δ, and_assoc]
    rw [this]
    exact ((isClosed_iInter fun i ↦ isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_biInter fun i _ ↦ isClosed_eq (continuous_apply i) continuous_const)).inter
      (isClosed_eq (continuous_finsetSum _ fun i _ ↦ continuous_apply i) continuous_const)
  have hΔk : IsCompact Δ :=
    (isCompact_univ_pi fun _ ↦ isCompact_Icc).of_isClosed_subset hΔcl
      fun lam ⟨h0, _, h1⟩ i _ ↦
        ⟨h0 i, h1 ▸ Finset.single_le_sum (fun j _ ↦ h0 j) (Finset.mem_univ i)⟩
  have hTc : Continuous T :=
    continuous_finsetSum _ fun i _ ↦ (continuous_apply i).smul continuous_const
  have hTl : IsLinearMap ℝ T :=
    ⟨fun a b ↦ by simp [T, add_smul, Finset.sum_add_distrib],
      fun c a ↦ by simp [T, Finset.smul_sum, smul_smul]⟩
  have hSconv : Convex ℝ S := (hΔc.is_linear_image hTl).add S₂.convex
  have hScl : IsClosed S := S₂.closed_of_finiteDimensional.add_left_of_isCompact (hΔk.image hTc)
  -- `0 ∉ S`
  have h0 : (0 : StrongDual ℝ X) ∉ S := by
    rintro ⟨_, ⟨lam, ⟨hl0, hlA, hl1⟩, rfl⟩, b, hb, hsum⟩
    obtain ⟨μ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hb
    exact hne lam μ hl0 hlA (fun hl ↦ by simp [hl] at hl1) hsum
  -- separation
  obtain ⟨f, u, hf0, hfS⟩ := geometric_hahn_banach_point_closed hSconv hScl h0
  obtain ⟨d, rfl⟩ := inclusionInDoubleDual_surjective f
  simp only [map_zero, NormedSpace.dual_def] at hf0 hfS
  have hmem : ∀ lam ∈ Δ, ∀ μ : K → ℝ, T lam + ∑ k, μ k • ξ k ∈ S := fun lam hl μ ↦
    ⟨T lam, ⟨lam, hl, rfl⟩, _, (Submodule.mem_span_range_iff_exists_fun ℝ).2 ⟨μ, rfl⟩, rfl⟩
  have hsingle : ∀ i ∈ A, (Pi.single i 1 : I → ℝ) ∈ Δ := fun i hi ↦
    ⟨fun j ↦ by rw [Pi.single_apply]; split_ifs <;> norm_num,
      fun j hj ↦ by rw [Pi.single_apply, if_neg (fun h : j = i ↦ hj (h ▸ hi))], by simp⟩
  have hTs : ∀ i, T (Pi.single i 1) = η i := fun i ↦ by
    simp [T]
  have hη : ∀ i ∈ A, u < η i d := fun i hi ↦ by
    simpa [hTs] using hfS _ (hmem _ (hsingle i hi) 0)
  have hξ : ∀ k, ξ k d = 0 := fun k ↦ by
    by_contra hk
    have key := hfS _ (hmem _ (hsingle i₀ hi₀) (Pi.single k ((u - η i₀ d - 1) / ξ k d)))
    simp only [hTs, Pi.single_apply, ite_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, add_apply, smul_apply,
      smul_eq_mul] at key
    rw [div_mul_cancel₀ _ hk] at key
    linarith
  exact h ⟨-d, fun i hi ↦ by simp only [map_neg]; linarith [hη i hi], fun k ↦ by simp [hξ k]⟩

end VariationalAnalysis
