/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis.Subdifferential.MeanValueIneq

/-!
# Subdifferential characterizations of Lipschitz continuity and strict differentiability

Consequences of the approximate mean value theorem [Mordukhovich 2018, Section 4.4.3]. A function
`φ : E → EReal` is *Lipschitz continuous around `x₀` with modulus `ℓ`* if on a neighborhood `U` of
`x₀` it is real-valued and `ℓ`-Lipschitz; this is written
`∃ U ∈ 𝓝 x₀, ∃ f : E → ℝ, (∀ x ∈ U, φ x = f x) ∧ LipschitzOnWith ℓ f U`, so that the results of
`Subdifferential/Lipschitz` for `fun x ↦ (f x : EReal)` apply through `subdiff_congr`.

## Main results

* `lipschitz_tfae`: Thm. 4.15 of [Mordukhovich 2018], (a) ⇔ (b) ⇔ (c) (subdifferential
  characterizations of local Lipschitz continuity with a given modulus); the main steps are
  `exists_nhds_forall_norm_le_of_forall_norm_le` ((a) ⇒ (b)) and
  `exists_lipschitzOnWith_ball_of_forall_norm_le` ((b) ⇒ (c)).
* `exists_lipschitzOnWith_of_singularSubdiff`: Thm. 4.15, singular criterion, and Thm. 1.22 of
  [Mordukhovich 2018], "if" part: `∂^∞φ(x₀) = {0}` implies that `φ` is locally Lipschitz.
* `exists_lipschitzOnWith_iff_singularSubdiff_eq_zero`: Thm. 1.22 of [Mordukhovich 2018]
  (both directions), with `singularSubdiff_eq_zero_of_eqOn_lipschitz` and
  `subdiff_nonempty_and_norm_le_of_eqOn_lipschitz` ("only if" consequences for
  extended-real-valued functions).
* `eventually_eq_iff_regularSubdiff_subset_zero`, `forall_eq_iff_regularSubdiff_subset_zero`:
  Cor. 4.16 of [Mordukhovich 2018] (constancy).
* `strictDifferentiability_tfae`: Thm. 4.17 of [Mordukhovich 2018] (strict differentiability).

## Remarks

* In Thm. 4.15(a) the same `η` bounds `‖x - x₀‖` and `|φ(x) - φ(x₀)|`, as in the book. The
  book's constant `min {ν, η, η/ℓ}` is replaced by `min {ν, η/(ℓ + 1)}`, which also covers
  `ℓ = 0`.
* Thm. 4.17 needs no lower semicontinuity: each of (a), (b), (c) implies Lipschitz continuity.
  The proof of (b) ⇒ (c) uses the Lipschitz mean value inequality of Cor. 4.14(ii) and the upper
  semicontinuity of `∂φ` at `x₀` (`eventually_forall_mem_subdiff_norm_sub_le`), instead of the
  sequences of the book.
* Cor. 4.16 is stated for l.s.c. `φ : E → EReal` without the value `⊥` on the open set `U`
  (the value `∞` is allowed); the connected case is `forall_eq_iff_regularSubdiff_subset_zero`.
-/

open Filter Topology Set Metric
open scoped Pointwise NNReal

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Lipschitz

variable [FiniteDimensional ℝ E] {φ : E → EReal} {x₀ : E} {r : ℝ}

/-- Thm. 4.15 of [Mordukhovich 2018], (b) ⇒ (c) on balls: if `φ` is l.s.c. on the ball
`B(x₀, 3ρ)`, has no value `⊥` there, is finite at `x₀`, and `‖x*‖ ≤ ℓ` for all regular
subgradients `x* ∈ ∂̂φ(x)`, `x ∈ B(x₀, 3ρ)`, then `φ` is real-valued and `ℓ`-Lipschitz on
`B(x₀, ρ)`. The proof uses the increment estimate (4.25) of Cor. 4.14(i). -/
theorem exists_lipschitzOnWith_ball_of_forall_norm_le {ρ : ℝ} (hρ : 0 < ρ) {ℓ : ℝ≥0}
    (hlsc : ∀ x ∈ ball x₀ (3 * ρ), LowerSemicontinuousAt φ x)
    (hbot : ∀ x ∈ ball x₀ (3 * ρ), φ x ≠ ⊥)
    (hM : ∀ x ∈ ball x₀ (3 * ρ), ∀ v ∈ regularSubdiff φ x, ‖v‖ ≤ ℓ) (hx₀ : φ x₀ ≠ ⊤) :
    ∃ f : E → ℝ, (∀ x ∈ ball x₀ ρ, φ x = f x) ∧ LipschitzOnWith ℓ f (ball x₀ ρ) := by
  -- the increment estimate on segments inside `B(x₀, ρ)`
  have hinc : ∀ a ∈ ball x₀ ρ, ∀ b ∈ ball x₀ ρ, ∀ α : ℝ, φ a = α →
      ∃ β : ℝ, φ b = β ∧ |β - α| ≤ ‖b - a‖ * ℓ := by
    intro a ha b hb α hα
    have hseg : segment ℝ a b ⊆ closedBall x₀ ρ :=
      (convex_closedBall x₀ ρ).segment_subset (ball_subset_closedBall ha)
        (ball_subset_closedBall hb)
    have hthick : cthickening ρ (segment ℝ a b) ⊆ ball x₀ (3 * ρ) := by
      refine ((cthickening_subset_of_subset ρ hseg).trans ?_)
      rw [cthickening_closedBall hρ.le hρ.le]
      exact closedBall_subset_ball (by linarith)
    have hsegB : segment ℝ a b ⊆ ball x₀ (3 * ρ) :=
      (self_subset_cthickening _).trans hthick
    exact abs_sub_le_norm_mul_of_forall_norm_le hα
      (fun x hx ↦ eventually_of_mem (isOpen_ball.mem_nhds (hsegB hx)) hlsc)
      (fun x hx ↦ hbot x (hsegB hx)) hρ fun y hy v hv ↦ hM y (hthick hy) v hv
  have hx₀b : x₀ ∈ ball x₀ ρ := mem_ball_self hρ
  have hfin : ∀ x ∈ ball x₀ ρ, φ x = (φ x).toReal := fun x hx ↦ by
    obtain ⟨β, hβ, -⟩ := hinc x₀ hx₀b x hx (φ x₀).toReal
      (EReal.coe_toReal hx₀ (hbot x₀ (ball_subset_ball (by linarith) hx₀b))).symm
    rw [hβ, EReal.toReal_coe]
  refine ⟨fun x ↦ (φ x).toReal, hfin, LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_⟩
  obtain ⟨β, hβ, hle⟩ := hinc y hy x hx (φ y).toReal (hfin y hy)
  rw [hβ, EReal.toReal_coe, Real.dist_eq, dist_eq_norm, mul_comm]
  exact hle

/-- Thm. 4.15 of [Mordukhovich 2018], (a) ⇒ (b): if `φ` is finite at `x₀` and l.s.c. around
`x₀`, and `‖x*‖ ≤ ℓ` for all `x* ∈ ∂̂φ(x)` with `‖x - x₀‖ < η` and `|φ(x) - φ(x₀)| < η`, then
`‖x*‖ ≤ ℓ` for all `x* ∈ ∂̂φ(x)` with `x` in a neighborhood of `x₀`. The proof follows the book:
if `φ(b) ≥ φ(x₀) + η` for some `b` close to `x₀`, the approximate mean value theorem
(Thm. 4.13) applied to `min {φ, φ(x₀) + η}` on `[x₀, b]` produces regular subgradients of norm
larger than `ℓ`. -/
theorem exists_nhds_forall_norm_le_of_forall_norm_le (hr : φ x₀ = r)
    (hlsc : ∀ᶠ x in 𝓝 x₀, LowerSemicontinuousAt φ x) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {η : ℝ}
    (hη : 0 < η)
    (ha : ∀ x, ‖x - x₀‖ < η → ((r - η : ℝ) : EReal) < φ x → φ x < ((r + η : ℝ) : EReal) →
      ∀ v ∈ regularSubdiff φ x, ‖v‖ ≤ ℓ) :
    ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, ∀ v ∈ regularSubdiff φ x, ‖v‖ ≤ ℓ := by
  have h1 : ∀ᶠ x in 𝓝 x₀, (∀ᶠ y in 𝓝 x, LowerSemicontinuousAt φ y) ∧
      ((r - η : ℝ) : EReal) < φ x :=
    hlsc.eventually_nhds.and (hlsc.self_of_nhds ((r - η : ℝ) : EReal) (by
      change ((r - η : ℝ) : EReal) < φ x₀
      rw [hr]; exact EReal.coe_lt_coe_iff.2 (by linarith)))
  obtain ⟨ν, hν, hνsub⟩ := Metric.mem_nhds_iff.1 h1
  set θ := min ν (η / (ℓ + 1)) with hθdef
  have hθ : 0 < θ := lt_min hν (by positivity)
  have hθη : θ ≤ η := (min_le_right _ _).trans (div_le_self hη.le (by linarith))
  have hθℓ : ℓ * θ < η := by
    have h2 : θ ≤ η / (ℓ + 1) := min_le_right _ _
    have h3 : ℓ * θ ≤ ℓ * (η / (ℓ + 1)) := mul_le_mul_of_nonneg_left h2 hℓ
    have h4 : ℓ * (η / (ℓ + 1)) < η := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
    linarith
  have hball : ball x₀ θ ⊆ ball x₀ ν := ball_subset_ball (min_le_left _ _)
  have claim : ∀ b ∈ ball x₀ θ, φ b < ((r + η : ℝ) : EReal) := by
    intro b hb
    by_contra hge
    push Not at hge
    have hbx₀ : x₀ ≠ b := by
      rintro rfl
      rw [hr, EReal.coe_le_coe_iff] at hge
      linarith
    set ψ : E → EReal := fun x ↦ min (φ x) ((r + η : ℝ) : EReal) with hψdef
    have hψx₀ : ψ x₀ = r := by
      change min (φ x₀) _ = _
      rw [hr, min_eq_left (EReal.coe_le_coe_iff.2 (by linarith))]
    have hψb : ψ b = ((r + η : ℝ) : EReal) := min_eq_right hge
    have hseg : segment ℝ x₀ b ⊆ ball x₀ θ :=
      (convex_ball x₀ θ).segment_subset (mem_ball_self hθ) hb
    have hψlsc : ∀ x ∈ segment ℝ x₀ b, ∀ᶠ y in 𝓝 x, LowerSemicontinuousAt ψ y :=
      fun x hx ↦ (hνsub (hball (hseg hx))).1.mono fun y hy ↦ hy.inf lowerSemicontinuousAt_const
    have hψbot : ∀ x ∈ segment ℝ x₀ b, ψ x ≠ ⊥ := fun x hx ↦ by
      have h := (hνsub (hball (hseg hx))).2
      exact ne_bot_of_gt (lt_min h (EReal.coe_lt_coe_iff.2 (by linarith)))
    obtain ⟨c, hc, hcb, hmin⟩ := exists_isMinOn_approx_mean_value hbx₀ hψx₀ hψb
      fun x hx ↦ (hψlsc x hx).self_of_nhds
    obtain ⟨x, v, hx, hv, -, h2, -⟩ := approx_mean_value hbx₀ hψx₀ hψlsc hψbot hc hcb hmin
    set D := ‖b - x₀‖ with hD
    have hDθ : D < θ := by rw [hD, ← dist_eq_norm]; exact hb
    obtain ⟨τ, ⟨hτ0, hτ1⟩, hcτ⟩ := mem_segment_iff_eq_add_smul.1 hc
    have hτ1' : τ < 1 := lt_of_le_of_ne hτ1 fun h ↦ hcb (by rw [hcτ, h, one_smul]; abel)
    have hψc : ψ c < ((r + η : ℝ) : EReal) := by
      have h := hmin (left_mem_segment ℝ x₀ b)
      simp only [mem_ofPred_eq, sub_self, norm_zero, mul_zero, EReal.coe_zero, sub_zero,
        hψx₀] at h
      rw [hcτ, sub_coe_div_mul_norm_eq hbx₀ hτ0, ← hcτ] at h
      have h' : ψ c ≤ ((r + (r + η - r) * τ : ℝ) : EReal) := by
        rw [EReal.coe_add]
        exact (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
          (Or.inl (EReal.coe_ne_top _))).1 h
      refine lt_of_le_of_lt h' (EReal.coe_lt_coe_iff.2 ?_)
      nlinarith
    obtain ⟨hx1, hx2⟩ := tendsto_funNhds_iff.1 hx
    have hε : 0 < (η - ℓ * D) / 2 := by
      have : ℓ * D ≤ ℓ * θ := mul_le_mul_of_nonneg_left hDθ.le hℓ
      linarith
    obtain ⟨k, hk1, hk2, hk3⟩ := ((hx2.eventually (Iio_mem_nhds hψc)).and
      ((hx1.eventually (isOpen_ball.mem_nhds (hseg hc))).and (h2 _ hε))).exists
    have hlt : φ (x k) < ((r + η : ℝ) : EReal) := by
      by_contra h
      push Not at h
      exact (lt_irrefl _) (lt_of_lt_of_le hk1 (le_min h le_rfl))
    have hψk : ψ (x k) = φ (x k) := min_eq_left hlt.le
    have hvk : v k ∈ regularSubdiff φ (x k) :=
      regularSubdiff_subset_of_le (Eventually.of_forall fun y ↦ min_le_left _ _) hψk (hv k)
    have hnorm := ha (x k) (by rw [← dist_eq_norm]; exact lt_of_lt_of_le hk2 hθη)
      (hνsub (hball hk2)).2 hlt (v k) hvk
    have h3 := apply_le_norm_mul (v k) (b - x₀)
    have h4 : ‖v k‖ * ‖b - x₀‖ ≤ ℓ * D := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    rw [← hD] at h3 h4
    have h5 : ℓ * D ≤ ℓ * θ := mul_le_mul_of_nonneg_left hDθ.le hℓ
    linarith
  refine ⟨ball x₀ θ, ball_mem_nhds x₀ hθ, fun x hx v hv ↦ ha x ?_ (hνsub (hball hx)).2
    (claim x hx) v hv⟩
  rw [← dist_eq_norm]
  exact lt_of_lt_of_le hx hθη

/-- Thm. 4.15 of [Mordukhovich 2018] (subdifferential characterizations of local Lipschitz
continuity): for `φ` finite at `x₀` and l.s.c. around `x₀`, and `ℓ ≥ 0`, the following are
equivalent:
(a) there is `η > 0` with `∂̂φ(x) ⊆ ℓ 𝔹` whenever `‖x - x₀‖ < η` and `|φ(x) - φ(x₀)| < η`;
(b) there is a neighborhood `U` of `x₀` with `∂̂φ(x) ⊆ ℓ 𝔹` for all `x ∈ U`;
(c) `φ` is Lipschitz continuous around `x₀` with modulus `ℓ`: on a neighborhood `U` of `x₀`,
`φ` is real-valued, `φ = f` with `f` `ℓ`-Lipschitz on `U`. -/
theorem lipschitz_tfae (hr : φ x₀ = r) (hlsc : ∀ᶠ x in 𝓝 x₀, LowerSemicontinuousAt φ x)
    (ℓ : ℝ≥0) :
    List.TFAE [
      ∃ η > 0, ∀ x, ‖x - x₀‖ < η → ((r - η : ℝ) : EReal) < φ x →
        φ x < ((r + η : ℝ) : EReal) → ∀ v ∈ regularSubdiff φ x, ‖v‖ ≤ ℓ,
      ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, ∀ v ∈ regularSubdiff φ x, ‖v‖ ≤ ℓ,
      ∃ U ∈ 𝓝 x₀, ∃ f : E → ℝ, (∀ x ∈ U, φ x = f x) ∧ LipschitzOnWith ℓ f U] := by
  tfae_have 1 → 2 := fun ⟨η, hη, ha⟩ ↦
    exists_nhds_forall_norm_le_of_forall_norm_le hr hlsc ℓ.coe_nonneg hη ha
  tfae_have 2 → 1 := fun ⟨U, hU, h⟩ ↦ by
    obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.1 hU
    exact ⟨η, hη, fun x hx _ _ v hv ↦ h x (hball (by rw [mem_ball, dist_eq_norm]; exact hx)) v hv⟩
  tfae_have 2 → 3 := fun ⟨U, hU, h⟩ ↦ by
    have hbot : ∀ᶠ x in 𝓝 x₀, ⊥ < φ x :=
      hlsc.self_of_nhds ⊥ (by change ⊥ < φ x₀; rw [hr]; exact EReal.bot_lt_coe r)
    obtain ⟨ρ₃, hρ₃, hsub⟩ := Metric.mem_nhds_iff.1
      (((show ∀ᶠ x in 𝓝 x₀, x ∈ U from hU).and hlsc).and hbot)
    have h3 : 3 * (ρ₃ / 3) = ρ₃ := by ring
    obtain ⟨f, hf, hL⟩ := exists_lipschitzOnWith_ball_of_forall_norm_le (x₀ := x₀)
      (ρ := ρ₃ / 3) (by positivity) (fun x hx ↦ (hsub (h3 ▸ hx)).1.2)
      (fun x hx ↦ (hsub (h3 ▸ hx)).2.ne') (fun x hx ↦ h x (hsub (h3 ▸ hx)).1.1)
      (by rw [hr]; exact EReal.coe_ne_top r)
    exact ⟨ball x₀ (ρ₃ / 3), ball_mem_nhds x₀ (by positivity), f, hf, hL⟩
  tfae_have 3 → 2 := fun ⟨U, hU, f, hf, hL⟩ ↦ by
    refine ⟨interior U, interior_mem_nhds.2 hU, fun x hx v hv ↦ ?_⟩
    have hUx : U ∈ 𝓝 x := mem_interior_iff_mem_nhds.1 hx
    have heq : φ =ᶠ[𝓝 x] fun y ↦ (f y : EReal) := eventually_of_mem hUx hf
    rw [regularSubdiff_congr heq] at hv
    exact norm_le_of_mem_subdiff_of_lipschitz hUx hL (regularSubdiff_subset_subdiff hv)
  tfae_finish

/-- Thm. 4.15 of [Mordukhovich 2018], singular criterion, main step: if `∂^∞φ(x₀) = {0}`, then
condition (a) of `lipschitz_tfae` holds for some `ℓ` and `η > 0`. Otherwise there are
`xₖ →φ x₀` and `x*ₖ ∈ ∂̂φ(xₖ)` with `‖x*ₖ‖ → ∞`, and a limit of `x*ₖ / ‖x*ₖ‖` is a nonzero singular
subgradient (Thm. 1.28, (1.38)). -/
theorem exists_forall_norm_le_of_singularSubdiff (hr : φ x₀ = r)
    (h0 : ∀ v ∈ singularSubdiff φ x₀, v = 0) :
    ∃ ℓ : ℝ≥0, ∃ η > 0, ∀ x, ‖x - x₀‖ < η → ((r - η : ℝ) : EReal) < φ x →
      φ x < ((r + η : ℝ) : EReal) → ∀ v ∈ regularSubdiff φ x, ‖v‖ ≤ ℓ := by
  by_contra h
  push Not at h
  choose x hx1 hx2 hx3 v hv hvn using fun n : ℕ ↦ h n (1 / ((n : ℝ) + 1))
    Nat.one_div_pos_of_nat
  simp only [NNReal.coe_natCast] at hvn
  have hinv : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hxt : Tendsto x atTop (𝓝 x₀) :=
    tendsto_iff_norm_sub_tendsto_zero.2
      (squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ (hx1 n).le) hinv)
  have hφt : Tendsto (fun n ↦ φ (x n)) atTop (𝓝 (φ x₀)) := by
    rw [hr]
    have hl : Tendsto (fun n : ℕ ↦ ((r - 1 / ((n : ℝ) + 1) : ℝ) : EReal)) atTop (𝓝 (r : EReal)) :=
      (continuous_coe_real_ereal.tendsto r).comp (by simpa using tendsto_const_nhds.sub hinv)
    have hu : Tendsto (fun n : ℕ ↦ ((r + 1 / ((n : ℝ) + 1) : ℝ) : EReal)) atTop (𝓝 (r : EReal)) :=
      (continuous_coe_real_ereal.tendsto r).comp (by simpa using tendsto_const_nhds.add hinv)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu (fun n ↦ (hx2 n).le)
      (fun n ↦ (hx3 n).le)
  have hvpos : ∀ n, 0 < ‖v n‖ := fun n ↦ lt_of_le_of_lt (Nat.cast_nonneg n) (hvn n)
  have hvt : Tendsto (fun n ↦ ‖v n‖) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ (hvn n).le) tendsto_natCast_atTop_atTop
  set lam : ℕ → ℝ := fun n ↦ ‖v n‖⁻¹ with hlam
  have hlamt : Tendsto lam atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hvt.inv_tendsto_atTop,
      Eventually.of_forall fun n ↦ inv_pos.2 (hvpos n)⟩
  set w : ℕ → StrongDual ℝ E := fun n ↦ lam n • v n with hw
  have hwn : ∀ n, ‖w n‖ = 1 := fun n ↦ by
    rw [hw, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg _)),
      inv_mul_cancel₀ (hvpos n).ne']
  obtain ⟨w₀, -, ψ, hψ, hwt⟩ := tendsto_subseq_of_bounded
    (isBounded_closedBall (x := (0 : StrongDual ℝ E)) (r := 1))
    (fun n ↦ mem_closedBall_zero_iff.2 (hwn n).le)
  have hw₀ : ‖w₀‖ = 1 := by
    have := (continuous_norm.tendsto w₀).comp hwt
    simp only [Function.comp_def, hwn] at this
    exact (tendsto_nhds_unique tendsto_const_nhds this).symm
  have hmem : w₀ ∈ singularSubdiff φ x₀ := outerLimit_smul_regularSubdiff_subset_singularSubdiff hr
    ⟨fun j ↦ (x (ψ j), lam (ψ j)), w ∘ ψ,
      ((tendsto_funNhds_iff.2 ⟨hxt, hφt⟩).comp hψ.tendsto_atTop).prodMk
        (hlamt.comp hψ.tendsto_atTop), hwt, fun j ↦ Set.smul_mem_smul_set (hv (ψ j))⟩
  rw [h0 w₀ hmem, norm_zero] at hw₀
  exact zero_ne_one hw₀

/-- Thm. 1.22 of [Mordukhovich 2018], "if" part, and the singular criterion of Thm. 4.15: if
`φ` is finite at `x₀`, l.s.c. around `x₀`, and `∂^∞φ(x₀) = {0}`, then `φ` is locally Lipschitz
around `x₀`: on a neighborhood `U` of `x₀`, `φ` is real-valued, `φ = f` with `f` Lipschitz on
`U`. -/
theorem exists_lipschitzOnWith_of_singularSubdiff (hr : φ x₀ = r)
    (hlsc : ∀ᶠ x in 𝓝 x₀, LowerSemicontinuousAt φ x) (h0 : ∀ v ∈ singularSubdiff φ x₀, v = 0) :
    ∃ U ∈ 𝓝 x₀, ∃ L : ℝ≥0, ∃ f : E → ℝ, (∀ x ∈ U, φ x = f x) ∧ LipschitzOnWith L f U := by
  obtain ⟨ℓ, ha⟩ := exists_forall_norm_le_of_singularSubdiff hr h0
  obtain ⟨U, hU, f, hf, hL⟩ := (lipschitz_tfae hr hlsc ℓ).out 0 2 |>.1 ha
  exact ⟨U, hU, ℓ, f, hf, hL⟩

omit [FiniteDimensional ℝ E] in
/-- Thm. 1.22 of [Mordukhovich 2018], "only if" part, for extended-real-valued functions: if `φ`
agrees on a neighborhood `U` of `x₀` with a real function `f` Lipschitz on `U`, then
`∂^∞φ(x₀) = {0}`. -/
theorem singularSubdiff_eq_zero_of_eqOn_lipschitz {U : Set E} {f : E → ℝ} {L : ℝ≥0}
    (hU : U ∈ 𝓝 x₀) (hf : ∀ x ∈ U, φ x = f x) (hL : LipschitzOnWith L f U) :
    singularSubdiff φ x₀ = {0} := by
  rw [singularSubdiff_congr (eventually_of_mem hU hf)]
  exact singularSubdiff_eq_zero_of_lipschitz hU hL

/-- Thm. 1.22 of [Mordukhovich 2018], (1.27), for extended-real-valued functions: if `φ` agrees
on a neighborhood `U` of `x₀` with a real function `f` that is `L`-Lipschitz on `U`, then
`∂φ(x₀)` is nonempty and contained in the ball of radius `L`. -/
theorem subdiff_nonempty_and_norm_le_of_eqOn_lipschitz {U : Set E} {f : E → ℝ} {L : ℝ≥0}
    (hU : U ∈ 𝓝 x₀) (hf : ∀ x ∈ U, φ x = f x) (hL : LipschitzOnWith L f U) :
    (subdiff φ x₀).Nonempty ∧ ∀ v ∈ subdiff φ x₀, ‖v‖ ≤ L := by
  rw [subdiff_congr (eventually_of_mem hU hf)]
  exact ⟨subdiff_nonempty_of_lipschitz hU hL, fun v hv ↦
    norm_le_of_mem_subdiff_of_lipschitz hU hL hv⟩

/-- Thm. 1.22 of [Mordukhovich 2018] (subdifferentials of locally Lipschitzian functions), and
the singular criterion of Thm. 4.15: let `φ` be finite at `x₀` and l.s.c. around `x₀`. Then `φ`
is locally Lipschitz around `x₀` (real-valued and Lipschitz on a neighborhood of `x₀`) if and
only if `∂^∞φ(x₀) = {0}`. In this case `∂φ(x₀) ≠ ∅` and `‖v‖ ≤ L` for `v ∈ ∂φ(x₀)`
(`subdiff_nonempty_and_norm_le_of_eqOn_lipschitz`). -/
theorem exists_lipschitzOnWith_iff_singularSubdiff_eq_zero (hr : φ x₀ = r)
    (hlsc : ∀ᶠ x in 𝓝 x₀, LowerSemicontinuousAt φ x) :
    (∃ U ∈ 𝓝 x₀, ∃ L : ℝ≥0, ∃ f : E → ℝ, (∀ x ∈ U, φ x = f x) ∧ LipschitzOnWith L f U) ↔
      singularSubdiff φ x₀ = {0} := by
  constructor
  · rintro ⟨U, hU, L, f, hf, hL⟩
    exact singularSubdiff_eq_zero_of_eqOn_lipschitz hU hf hL
  · intro h
    exact exists_lipschitzOnWith_of_singularSubdiff hr hlsc fun v hv ↦ by
      rw [h] at hv; exact hv

end Lipschitz

section Constancy

variable [FiniteDimensional ℝ E] {φ : E → EReal} {U : Set E}

/-- The step behind Cor. 4.16 of [Mordukhovich 2018]: if `B(x₀, 3ρ) ⊆ U`, `φ` is l.s.c. on `U`
with no value `⊥`, and `∂̂φ(x) ⊆ {0}` on `U`, then `φ` takes the finite value `φ(a)` at every
`b ∈ B(x₀, ρ)` whenever `a ∈ B(x₀, ρ)` and `φ(a)` is finite (by (4.25) with `M = 0`). -/
theorem eq_of_regularSubdiff_subset_zero (hU : IsOpen U)
    (hlsc : ∀ x ∈ U, LowerSemicontinuousAt φ x) (hbot : ∀ x ∈ U, φ x ≠ ⊥)
    (h0 : ∀ x ∈ U, ∀ v ∈ regularSubdiff φ x, v = 0) {x₀ : E} {ρ : ℝ} (hρ : 0 < ρ)
    (hball : ball x₀ (3 * ρ) ⊆ U) {a b : E} (ha : a ∈ ball x₀ ρ) (hb : b ∈ ball x₀ ρ) {α : ℝ}
    (hα : φ a = α) : φ b = α := by
  have hseg : segment ℝ a b ⊆ closedBall x₀ ρ :=
    (convex_closedBall x₀ ρ).segment_subset (ball_subset_closedBall ha) (ball_subset_closedBall hb)
  have hthick : cthickening ρ (segment ℝ a b) ⊆ U := by
    refine ((cthickening_subset_of_subset ρ hseg).trans ?_).trans hball
    rw [cthickening_closedBall hρ.le hρ.le]
    exact closedBall_subset_ball (by linarith)
  have hsegU : segment ℝ a b ⊆ U := (self_subset_cthickening _).trans hthick
  obtain ⟨β, hβ, hle⟩ := abs_sub_le_norm_mul_of_forall_norm_le (M := 0) hα
    (fun x hx ↦ eventually_of_mem (hU.mem_nhds (hsegU hx)) hlsc)
    (fun x hx ↦ hbot x (hsegU hx)) hρ fun y hy v hv ↦ by rw [h0 y (hthick hy) v hv, norm_zero]
  rw [mul_zero, abs_nonpos_iff, sub_eq_zero] at hle
  rw [hβ, hle]

/-- Cor. 4.16 of [Mordukhovich 2018] (subdifferential characterization of constancy for l.s.c.
functions): let `φ` be l.s.c. on an open set `U` with no value `⊥` there. Then `φ` is locally
constant on `U` if and only if `x* ∈ ∂̂φ(x)` implies `x* = 0` for all `x ∈ U`. -/
theorem eventually_eq_iff_regularSubdiff_subset_zero (hU : IsOpen U)
    (hlsc : ∀ x ∈ U, LowerSemicontinuousAt φ x) (hbot : ∀ x ∈ U, φ x ≠ ⊥) :
    (∀ x ∈ U, ∀ᶠ y in 𝓝 x, φ y = φ x) ↔ ∀ x ∈ U, ∀ v ∈ regularSubdiff φ x, v = 0 := by
  constructor
  · intro h x hx v hv
    obtain ⟨r, hr, -⟩ := id hv
    have heq : φ =ᶠ[𝓝 x] fun _ ↦ ((fun _ : E ↦ r) x : EReal) := (h x hx).mono fun y hy ↦ by
      rw [hy, hr]
    rw [regularSubdiff_congr heq, regularSubdiff_of_hasFDerivAt (hasFDerivAt_const r x)] at hv
    exact hv
  · intro h0 x hx
    obtain ⟨ρ₃, hρ₃, hsub⟩ := Metric.isOpen_iff.1 hU x hx
    set ρ := ρ₃ / 3 with hρdef
    have hρ : 0 < ρ := by positivity
    have hball : ball x (3 * ρ) ⊆ U := by rw [hρdef, mul_div_cancel₀ _ three_ne_zero]; exact hsub
    filter_upwards [ball_mem_nhds x hρ] with y hy
    by_cases htop : φ x = ⊤
    · by_contra hne
      rw [htop] at hne
      obtain ⟨β, hβ⟩ := exists_eq_coe_of_ne_bot_of_ne_top (hbot y (hball
        (ball_subset_ball (by linarith) hy))) hne
      have := eq_of_regularSubdiff_subset_zero hU hlsc hbot h0 hρ hball hy (mem_ball_self hρ) hβ
      rw [htop] at this
      exact EReal.coe_ne_top β this.symm
    · obtain ⟨α, hα⟩ := exists_eq_coe_of_ne_bot_of_ne_top (hbot x hx) htop
      rw [hα]
      exact eq_of_regularSubdiff_subset_zero hU hlsc hbot h0 hρ hball (mem_ball_self hρ) hy hα

/-- Cor. 4.16 of [Mordukhovich 2018], connected case: if moreover `U` is connected, `φ` is
constant on `U` if and only if `x* ∈ ∂̂φ(x)` implies `x* = 0` for all `x ∈ U`. -/
theorem forall_eq_iff_regularSubdiff_subset_zero (hU : IsOpen U) (hUc : IsPreconnected U)
    (hlsc : ∀ x ∈ U, LowerSemicontinuousAt φ x) (hbot : ∀ x ∈ U, φ x ≠ ⊥) :
    (∀ x ∈ U, ∀ y ∈ U, φ x = φ y) ↔ ∀ x ∈ U, ∀ v ∈ regularSubdiff φ x, v = 0 := by
  rw [← eventually_eq_iff_regularSubdiff_subset_zero hU hlsc hbot]
  constructor
  · intro h x hx
    exact eventually_of_mem (hU.mem_nhds hx) fun y hy ↦ h y hy x hx
  · intro h x hx y hy
    by_contra hne
    obtain ⟨z, -, hz1, hz2⟩ := hUc {z | ∀ᶠ w in 𝓝 z, φ w = φ x} {z | ∀ᶠ w in 𝓝 z, φ w ≠ φ x}
      isOpen_setOfPred_eventually_nhds isOpen_setOfPred_eventually_nhds
      (fun z hz ↦ by
        by_cases hzx : φ z = φ x
        · exact Or.inl ((h z hz).mono fun w hw ↦ hw.trans hzx)
        · exact Or.inr ((h z hz).mono fun w hw ↦ hw ▸ hzx))
      ⟨x, hx, (h x hx)⟩ ⟨y, hy, (h y hy).mono fun w hw ↦ hw ▸ Ne.symm hne⟩
    exact (hz1.and hz2).self_of_nhds.2 (hz1.self_of_nhds)

end Constancy

section StrictDifferentiability

variable {φ : E → EReal} {x₀ : E} {x' : StrongDual ℝ E}

/-- Thm. 4.17 of [Mordukhovich 2018], (c) ⇒ (a), main step: if `φ` agrees near `x₀` with a
function `f` strictly differentiable at `x₀` with `∇f(x₀) = x̄*`, then for every `ε > 0`,
`‖x* - x̄*‖ ≤ ε` for all `x* ∈ ∂̂φ(x)` and all `x` close to `x₀`. -/
theorem eventually_forall_norm_sub_le_of_hasStrictFDerivAt {f : E → ℝ}
    (hf : HasStrictFDerivAt f x' x₀) (hφ : ∀ᶠ x in 𝓝 x₀, φ x = f x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ∀ v ∈ regularSubdiff φ x, ‖v - x'‖ ≤ ε := by
  have hlo := (hasStrictFDerivAt_iff_isLittleO.1 hf).def hε
  obtain ⟨δ, hδ, hδsub⟩ := Metric.eventually_nhds_iff.1 hlo
  obtain ⟨δ', hδ', hδ'sub⟩ := Metric.eventually_nhds_iff.1 hφ
  set δ₁ := min δ δ' with hδ₁
  have hδ₁pos : 0 < δ₁ := lt_min hδ hδ'
  filter_upwards [ball_mem_nhds x₀ hδ₁pos] with x hx v hv
  have heq : φ =ᶠ[𝓝 x] fun y ↦ (f y : EReal) :=
    eventually_of_mem (isOpen_ball.mem_nhds hx) fun y hy ↦
      hδ'sub (lt_of_lt_of_le (mem_ball.1 hy) (min_le_right _ _))
  rw [regularSubdiff_congr heq, mem_regularSubdiff_coe] at hv
  refine norm_le_of_forall_eventually_le (z := x) hε.le fun η hη ↦ ?_
  filter_upwards [hv η hη, isOpen_ball.mem_nhds hx] with y hy1 hy2
  have hp : dist ((y, x) : E × E) (x₀, x₀) < δ := by
    rw [Prod.dist_eq]
    exact max_lt (lt_of_lt_of_le (mem_ball.1 hy2) (min_le_left _ _))
      (lt_of_lt_of_le (mem_ball.1 hx) (min_le_left _ _))
  have h := hδsub hp
  simp only [Real.norm_eq_abs] at h
  have h' := (abs_le.1 h).2
  simp only [sub_apply]
  nlinarith

/-- Thm. 4.17 of [Mordukhovich 2018], (b) ⇒ (c), main step (upper semicontinuity of `∂f`): if `f`
is Lipschitz on a neighborhood of `x₀` and `∂f(x₀) = {x̄*}`, then for every `ε > 0`,
`‖x* - x̄*‖ ≤ ε` for all `x* ∈ ∂f(y)` and all `y` close to `x₀`. -/
theorem eventually_forall_mem_subdiff_norm_sub_le [FiniteDimensional ℝ E] {f : E → ℝ}
    {U : Set E} {L : ℝ≥0} (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U)
    (h : subdiff (fun x ↦ (f x : EReal)) x₀ = {x'}) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 x₀, ∀ w ∈ subdiff (fun x ↦ (f x : EReal)) y, ‖w - x'‖ ≤ ε := by
  by_contra hne
  rw [not_eventually] at hne
  have hsel : ∀ n : ℕ, ∃ y, dist y x₀ < 1 / ((n : ℝ) + 1) ∧
      ∃ w ∈ subdiff (fun x ↦ (f x : EReal)) y, ε < ‖w - x'‖ := fun n ↦ by
    obtain ⟨y, hy1, hy2⟩ := (hne.and_eventually (ball_mem_nhds x₀ Nat.one_div_pos_of_nat)).exists
    push Not at hy1
    exact ⟨y, hy2, hy1⟩
  choose y hy w hw hwε using hsel
  have hyt : Tendsto y atTop (𝓝 x₀) := tendsto_iff_dist_tendsto_zero.2
    (squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ (hy n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat)
  have hM : ∀ᶠ n in atTop, ‖w n‖ ≤ L := by
    filter_upwards [hyt.eventually (interior_mem_nhds.2 hU)] with n hn
    exact norm_le_of_mem_subdiff_of_lipschitz (mem_interior_iff_mem_nhds.1 hn) hL (hw n)
  obtain ⟨w₀, -, ψ, hψ, hwt⟩ := tendsto_subseq_of_frequently_bounded
    (isBounded_closedBall (x := (0 : StrongDual ℝ E)) (r := L))
    (hM.mono fun n hn ↦ mem_closedBall_zero_iff.2 hn).frequently
  have hfc : ContinuousAt f x₀ := hL.continuousOn.continuousAt hU
  have hmem : w₀ ∈ subdiff (fun x ↦ (f x : EReal)) x₀ := by
    rw [subdiff_eq_outerLimit_subdiff (φ := fun x ↦ (f x : EReal)) (r := f x₀) rfl]
    refine ⟨y ∘ ψ, w ∘ ψ, tendsto_funNhds_iff.2 ⟨hyt.comp hψ.tendsto_atTop, ?_⟩, hwt,
      fun n ↦ hw (ψ n)⟩
    exact (continuous_coe_real_ereal.tendsto _).comp ((hfc.tendsto.comp hyt).comp
      hψ.tendsto_atTop)
  rw [h, mem_singleton_iff] at hmem
  subst hmem
  have := (hwt.sub_const w₀).norm
  rw [sub_self, norm_zero] at this
  obtain ⟨n, hn⟩ := (this.eventually (Iio_mem_nhds hε)).exists
  exact lt_irrefl _ ((hwε (ψ n)).trans hn)

/-- Thm. 4.17 of [Mordukhovich 2018] (subdifferential characterizations of strict
differentiability): for `φ : E → EReal`, `x₀ ∈ E` and `x̄* ∈ E*`, the following are equivalent:
(a) `φ` is Lipschitz continuous around `x₀`, and `x*ₖ → x̄*` for all sequences `xₖ → x₀` and
`x*ₖ ∈ ∂̂φ(xₖ)`;
(b) `φ` is Lipschitz continuous around `x₀` and `∂φ(x₀) = {x̄*}`;
(c) `φ` is strictly differentiable at `x₀` with `∇φ(x₀) = x̄*` (i.e. `φ` agrees near `x₀` with a
real function `f` with `HasStrictFDerivAt f x̄* x₀`).
"Lipschitz continuous around `x₀`" means: on a neighborhood `U` of `x₀`, `φ` agrees with a real
function Lipschitz on `U`. No lower semicontinuity assumption is needed. -/
theorem strictDifferentiability_tfae [FiniteDimensional ℝ E] :
    List.TFAE [
      (∃ U ∈ 𝓝 x₀, ∃ L : ℝ≥0, ∃ f : E → ℝ, (∀ x ∈ U, φ x = f x) ∧ LipschitzOnWith L f U) ∧
        ∀ (x : ℕ → E) (v : ℕ → StrongDual ℝ E), Tendsto x atTop (𝓝 x₀) →
          (∀ k, v k ∈ regularSubdiff φ (x k)) → Tendsto v atTop (𝓝 x'),
      (∃ U ∈ 𝓝 x₀, ∃ L : ℝ≥0, ∃ f : E → ℝ, (∀ x ∈ U, φ x = f x) ∧ LipschitzOnWith L f U) ∧
        subdiff φ x₀ = {x'},
      ∃ f : E → ℝ, (∀ᶠ x in 𝓝 x₀, φ x = f x) ∧ HasStrictFDerivAt f x' x₀] := by
  tfae_have 1 → 2 := fun ⟨⟨U, hU, L, f, hf, hL⟩, hseq⟩ ↦ by
    refine ⟨⟨U, hU, L, f, hf, hL⟩, ?_⟩
    have hfx₀ : φ x₀ = f x₀ := hf x₀ (mem_of_mem_nhds hU)
    have hsub : subdiff φ x₀ ⊆ {x'} := fun w hw ↦ by
      rw [subdiff_eq_outerLimit hfx₀] at hw
      obtain ⟨a, u, ha, hu, hmem⟩ := hw
      exact mem_singleton_iff.2 (tendsto_nhds_unique hu
        (hseq a u (tendsto_funNhds_iff.1 ha).1 hmem))
    obtain ⟨w, hw⟩ := (subdiff_nonempty_and_norm_le_of_eqOn_lipschitz hU hf hL).1
    have hwx := hsub hw
    rw [mem_singleton_iff] at hwx
    subst hwx
    exact subset_antisymm hsub (singleton_subset_iff.2 hw)
  tfae_have 2 → 3 := fun ⟨⟨U, hU, L, f, hf, hL⟩, h⟩ ↦ by
    refine ⟨f, eventually_of_mem hU hf, ?_⟩
    rw [subdiff_congr (eventually_of_mem hU hf)] at h
    have hV : IsOpen (interior U) := isOpen_interior
    have hLV : LipschitzOnWith L f (interior U) := hL.mono interior_subset
    refine hasStrictFDerivAt_iff_isLittleO.2 (Asymptotics.IsLittleO.of_bound fun ε hε ↦ ?_)
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1
      ((eventually_forall_mem_subdiff_norm_sub_le hU hL h hε).and (interior_mem_nhds.2 hU))
    -- the mean value inequality of Cor. 4.14(ii) on segments in `B(x₀, δ)`
    have hmv : ∀ y ∈ ball x₀ δ, ∀ z ∈ ball x₀ δ, f y - f z - x' (y - z) ≤ ε * ‖y - z‖ := by
      intro y hy z hz
      have hseg : segment ℝ z y ⊆ ball x₀ δ := (convex_ball x₀ δ).segment_subset hz hy
      obtain ⟨t, ht, w, hw, hineq⟩ := exists_mem_subdiff_mean_value_of_lipschitz hV
        (fun p hp ↦ (hδsub (hseg hp)).2) hLV
      have hpt : z + t • (y - z) ∈ ball x₀ δ := hseg (add_smul_sub_mem_segment ht.1 ht.2.le)
      have hnorm := (hδsub hpt).1 w hw
      have h1 := apply_le_norm_mul (w - x') (y - z)
      have h2 : ‖w - x'‖ * ‖y - z‖ ≤ ε * ‖y - z‖ :=
        mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
      rw [sub_apply] at h1
      linarith
    filter_upwards [prod_mem_nhds (ball_mem_nhds x₀ hδ) (ball_mem_nhds x₀ hδ)] with p hp
    obtain ⟨hp1, hp2⟩ := hp
    have h1 := hmv p.1 hp1 p.2 hp2
    have h2 := hmv p.2 hp2 p.1 hp1
    rw [norm_sub_rev p.2 p.1, show p.2 - p.1 = -(p.1 - p.2) by abel, map_neg] at h2
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  tfae_have 3 → 1 := fun ⟨f, hφf, hf⟩ ↦ by
    obtain ⟨K, s, hs, hK⟩ := hf.exists_lipschitzOnWith
    refine ⟨⟨s ∩ {x | φ x = f x}, inter_mem hs hφf, K, f, fun x hx ↦ hx.2,
      hK.mono inter_subset_left⟩, fun x v hx hv ↦ Metric.tendsto_nhds.2 fun ε hε ↦ ?_⟩
    filter_upwards [hx.eventually (eventually_forall_norm_sub_le_of_hasStrictFDerivAt hf hφf
      (half_pos hε))] with k hk
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (hk (v k) (hv k)) (half_lt_self hε)
  tfae_finish

end StrictDifferentiability

end VariationalAnalysis
