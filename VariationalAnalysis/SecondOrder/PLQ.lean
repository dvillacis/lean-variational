/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis.SecondOrder.SecondSubderiv

/-!
# Piecewise linear-quadratic functions

This file defines piecewise linear-quadratic and piecewise linear functions
[Mordukhovich 2024, Def. 1.59] and proves [Mordukhovich 2024, Thm. 1.91] (body numbering) on the
second subderivatives of convex piecewise linear-quadratic functions.

## Proof

Around a point `x̄ ∈ dom φ`, a polyhedral set is a translated polyhedral cone, so a piecewise
linear-quadratic function has a *local model* (`LocalPLQ`): finitely many closed cones `T j` with
`φ(x̄ + w) = φ(x̄) + ⟨g j, w⟩ + ½⟨A j w, w⟩` for small `w ∈ T j`, and `φ(x̄ + w) = ∞` for small `w`
outside the cones. On overlapping cones the linear and quadratic parts agree
(`LocalPLQ.consistent`). The difference quotients are then explicit, and the lower limits
defining `dφ(x̄)`, `d²φ(x̄)` and `d²φ(x̄, v)` are computed by `liminf_nhdsGT_prod_eq`: lower bounds
near `(0, w)` on each cone through `w`, and the limit along `u = w`. Convexity enters only through
`⟨v, u⟩ ≤ ⟨g j, u⟩` and `⟨A j w, w⟩ ≥ 0` on `T j`.

## Main declarations

* `IsPolyhedral`: finite intersections of closed half-spaces.
* `IsPLQ`, `IsPiecewiseLinear`: [Mordukhovich 2024, Def. 1.59].
* `LocalPLQ`: the local linear-quadratic model on cones.

## Main results

* `IsPolyhedral.exists_cone`, `IsPLQ.exists_localPLQ`: the local conic structure.
* `LocalPLQ.subderiv_of_mem`, `LocalPLQ.secondSubderiv'_of_mem`,
  `LocalPLQ.secondSubderiv_of_mem_of_eq`, `LocalPLQ.mem_criticalCone_iff`: the formulas for
  `dφ(x̄)`, `d²φ(x̄)`, `d²φ(x̄, v)` and `K_φ(x̄, v)` from the proof of Thm. 1.91.
* `IsPLQ.twiceEpiDifferentiableAt`, `IsPLQ.exists_eq_add_subderiv_add`: Thm. 1.91(i), (1.126).
* `IsPLQ.tendsto_secondDiffQuot'`, `IsPLQ.secondSubderiv'_nonneg`, `IsPLQ.isPLQ_secondSubderiv'`:
  Thm. 1.91(ii), (1.127).
* `IsPLQ.tendsto_secondDiffQuot`, `IsPLQ.secondSubderiv_eq`, `IsPLQ.convex_epi_secondSubderiv`,
  `IsPLQ.isPLQ_secondSubderiv`, `IsPLQ.exists_criticalCone_eq`: Thm. 1.91(iii), (1.128).

## Implementation notes

* Everything holds in a real normed space; the symmetric operator `A` of Def. 1.59 is a symmetric
  continuous bilinear form `E →L[ℝ] StrongDual ℝ E`.
* (1.126), (1.127) (except `≥ 0`) and the piecewise linear-quadratic structure of `d²φ(x̄)` do not
  use convexity.
* The critical cone is shown to be a finite union of polyhedral cones; that it is itself
  polyhedral (being convex) is not formalized.
-/

open Filter Topology Set Metric

namespace VariationalAnalysis

/-! ### Lower limits along `t ↓ 0`, `u → w` -/

section Liminf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- A continuous `F : ℝ × E → ℝ` tends to `F (0, w)` as `t ↓ 0`, `u → w`. -/
theorem tendsto_nhdsGT_prod_of_continuous {F : ℝ × E → ℝ} (hF : Continuous F) (w : E) :
    Tendsto F (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 (F (0, w))) :=
  (hF.tendsto (0, w)).mono_left (by rw [nhds_prod_eq]; exact prod_mono nhdsWithin_le_nhds le_rfl)

/-- For continuous `G : ℝ → ℝ`, `G t → G 0` in `EReal` as `t ↓ 0`. -/
theorem tendsto_coe_nhdsGT {G : ℝ → ℝ} (hG : Continuous G) :
    Tendsto (fun t ↦ ((G t : ℝ) : EReal)) (𝓝[>] 0) (𝓝 ((G 0 : ℝ) : EReal)) :=
  (continuous_coe_real_ereal.tendsto _).comp ((hG.tendsto 0).mono_left nhdsWithin_le_nhds)

omit [NormedSpace ℝ E] in
/-- A property which holds eventually as `t ↓ 0`, `u → w` holds eventually as `t ↓ 0` along
`u = w`. -/
theorem eventually_nhdsGT_of_prod {P : ℝ × E → Prop} {w : E}
    (h : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, P p) : ∀ᶠ t in 𝓝[>] (0 : ℝ), P (t, w) :=
  (tendsto_id.prodMk (tendsto_const_nhds (x := w))).eventually h

omit [NormedSpace ℝ E] in
/-- A lower limit as `t ↓ 0`, `u → w` is computed by lower bounds near `(0, w)` and the limit
along `u = w`. -/
theorem liminf_nhdsGT_prod_eq {f : ℝ × E → EReal} {w : E} {c : EReal}
    (hlow : ∀ b : ℝ, (b : EReal) < c → ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, (b : EReal) ≤ f p)
    (hup : Tendsto (fun t ↦ f (t, w)) (𝓝[>] 0) (𝓝 c)) :
    liminf f (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) = c := by
  refine le_antisymm ?_ (le_of_forall_lt fun b hb ↦ ?_)
  · have hle : map (fun t : ℝ ↦ (t, w)) (𝓝[>] 0) ≤ 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w := by
      rw [← prod_pure]
      exact prod_mono le_rfl (pure_le_nhds w)
    refine (liminf_le_liminf_of_le hle).trans_eq ?_
    rw [← hup.liminf_eq]
    rfl
  · obtain ⟨b', hb1, hb2⟩ := EReal.lt_iff_exists_real_btwn.1 hb
    exact hb1.trans_le (le_liminf_of_le (by isBoundedDefault) (hlow b' hb2))

omit [NormedSpace ℝ E] in
/-- If `f` is eventually above every real `b` as `t ↓ 0`, `u → w`, then `f (t, w) → ∞` as
`t ↓ 0`. -/
theorem tendsto_top_of_eventually_le {f : ℝ × E → EReal} {w : E}
    (hlow : ∀ b : ℝ, ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, (b : EReal) ≤ f p) :
    Tendsto (fun t ↦ f (t, w)) (𝓝[>] 0) (𝓝 ⊤) := by
  rw [EReal.tendsto_nhds_top_iff_real]
  intro x
  filter_upwards [eventually_nhdsGT_of_prod (hlow (x + 1))] with t ht
  exact (EReal.coe_lt_coe_iff.2 (lt_add_one x)).trans_le ht

omit [NormedSpace ℝ E] in
/-- If `f` is eventually above every real `b` as `t ↓ 0`, `u → w`, then its lower limit there
is `∞`. -/
theorem liminf_nhdsGT_prod_eq_top {f : ℝ × E → EReal} {w : E}
    (hlow : ∀ b : ℝ, ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, (b : EReal) ≤ f p) :
    liminf f (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) = ⊤ :=
  liminf_nhdsGT_prod_eq (fun b _ ↦ hlow b) (tendsto_top_of_eventually_le hlow)

/-- If the second-order difference quotients converge pointwise to the second subderivative,
then `φ` is twice epi-differentiable. -/
theorem twiceEpiDifferentiableAt_of_tendsto {φ : E → EReal} {x₀ : E} {v : StrongDual ℝ E}
    (hr : ∃ r : ℝ, φ x₀ = r)
    (h : ∀ w, Tendsto (fun t ↦ secondDiffQuot φ x₀ v t w) (𝓝[>] 0)
      (𝓝 (secondSubderiv φ x₀ v w))) : TwiceEpiDifferentiableAt φ x₀ v := by
  refine ⟨hr, fun t ht w ↦ ⟨fun wk hwk ↦ ?_, fun _ ↦ w, tendsto_const_nhds, ?_⟩⟩
  · have hle : map (fun k ↦ (t k, wk k)) atTop ≤ 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w := ht.prodMk hwk
    exact liminf_le_liminf_of_le hle
  · exact ((h w).comp ht).limsup_eq.le

end Liminf

/-! ### Functions which are linear-quadratic on finitely many cones around a point -/

section Local

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

/-- A local linear-quadratic model of `φ` at `x₀`: `φ(x₀) = φ₀` and, for `‖w‖ < r`,
`φ(x₀ + w) = φ₀ + ⟨g j, w⟩ + ½⟨A j w, w⟩` when `w` lies in the closed cone `T j`, and
`φ(x₀ + w) = ∞` when `w` lies in none of the cones. -/
structure LocalPLQ (φ : E → EReal) (x₀ : E) (T : ι → Set E) (g : ι → StrongDual ℝ E)
    (A : ι → E →L[ℝ] StrongDual ℝ E) (φ₀ r : ℝ) : Prop where
  /-- The radius `r` of the model is positive. -/
  r_pos : 0 < r
  /-- The value `φ(x₀)` is the real number `φ₀`. -/
  eq₀ : φ x₀ = φ₀
  /-- The cones `T j` are closed. -/
  isClosed : ∀ j, IsClosed (T j)
  /-- The sets `T j` are cones: `cw ∈ T j` for `c > 0` and `w ∈ T j`. -/
  smul_mem : ∀ j (c : ℝ) w, 0 < c → w ∈ T j → c • w ∈ T j
  /-- On each cone the model is linear-quadratic: `φ(x₀ + w) = φ₀ + ⟨g j, w⟩ + ½⟨A j w, w⟩` for
  `w ∈ T j`, `‖w‖ < r`. -/
  eq_of_mem : ∀ j w, ‖w‖ < r → w ∈ T j →
    φ (x₀ + w) = ((φ₀ + g j w + 1 / 2 * A j w w : ℝ) : EReal)
  /-- `φ(x₀ + w) = ∞` for `‖w‖ < r` outside all the cones. -/
  eq_top : ∀ w, ‖w‖ < r → (∀ j, w ∉ T j) → φ (x₀ + w) = ⊤

namespace LocalPLQ

variable {φ : E → EReal} {x₀ : E} {T : ι → Set E} {g : ι → StrongDual ℝ E}
  {A : ι → E →L[ℝ] StrongDual ℝ E} {φ₀ r : ℝ} (h : LocalPLQ φ x₀ T g A φ₀ r)
  {j k : ι} {t : ℝ} {u w : E} {v : StrongDual ℝ E}
include h

/-- The model along a ray: `φ(x₀ + tu) = φ₀ + t⟨g k, u⟩ + (t²/2)⟨A k u, u⟩` for `u ∈ T k`, `t > 0`
and `‖tu‖ < r`. -/
theorem apply_smul (hu : u ∈ T k) (ht : 0 < t) (hs : ‖t • u‖ < r) :
    φ (x₀ + t • u) = ((φ₀ + t * g k u + t ^ 2 / 2 * A k u u : ℝ) : EReal) := by
  rw [h.eq_of_mem k _ hs (h.smul_mem k t u ht hu)]
  congr 1
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

/-- `φ(x₀ + tu) = ∞` for `u` in none of the cones, `t > 0` and `‖tu‖ < r`. -/
theorem apply_smul_of_not_mem (hu : ∀ k, u ∉ T k) (ht : 0 < t) (hs : ‖t • u‖ < r) :
    φ (x₀ + t • u) = ⊤ := by
  refine h.eq_top _ hs fun k hk ↦ hu k ?_
  have := h.smul_mem k t⁻¹ _ (inv_pos.2 ht) hk
  rwa [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at this

/-- For every `w` there is `t > 0` with `‖sw‖ < r` for all `0 < s ≤ t`. -/
theorem exists_small (w : E) : ∃ t > (0 : ℝ), ∀ s, 0 < s → s ≤ t → ‖s • w‖ < r := by
  refine ⟨r / (‖w‖ + 1), div_pos h.r_pos (by positivity), fun s hs hst ↦ ?_⟩
  rw [norm_smul, Real.norm_of_nonneg hs.le]
  have h1 : s * ‖w‖ ≤ r / (‖w‖ + 1) * ‖w‖ := mul_le_mul_of_nonneg_right hst (norm_nonneg w)
  have h2 : r / (‖w‖ + 1) * ‖w‖ < r := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [h.r_pos, norm_nonneg w]
  linarith

/-- As `t ↓ 0`, `u → w`, eventually `t > 0` and `‖tu‖ < r`. -/
theorem eventually_small (w : E) :
    ∀ᶠ p : ℝ × E in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, 0 < p.1 ∧ ‖p.1 • p.2‖ < r :=
  (eventually_pos_nhdsGT_prod w).and
    (((tendsto_smul_nhdsGT_prod w).eventually (ball_mem_nhds 0 h.r_pos)).mono
      fun p hp ↦ by simpa using hp)

/-- As `t ↓ 0`, eventually `t > 0` and `‖tw‖ < r`. -/
theorem eventually_small' (w : E) : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ ‖t • w‖ < r :=
  eventually_nhdsGT_of_prod (h.eventually_small w)

/-- On overlapping cones the linear and quadratic parts agree. -/
theorem consistent (hj : w ∈ T j) (hk : w ∈ T k) : g j w = g k w ∧ A j w w = A k w w := by
  obtain ⟨t, ht, hsmall⟩ := h.exists_small w
  have e1 := (h.apply_smul hj ht (hsmall t ht le_rfl)).symm.trans
    (h.apply_smul hk ht (hsmall t ht le_rfl))
  have e2 := (h.apply_smul hj (half_pos ht) (hsmall _ (half_pos ht) (by linarith))).symm.trans
    (h.apply_smul hk (half_pos ht) (hsmall _ (half_pos ht) (by linarith)))
  rw [EReal.coe_eq_coe_iff] at e1 e2
  have hb : t ^ 2 * (A j w w - A k w w) = 0 := by ring_nf at e1 e2 ⊢; linarith
  have hb' : A j w w = A k w w := by
    rcases mul_eq_zero.1 hb with h0 | h0
    · exact absurd ((pow_eq_zero_iff two_ne_zero).1 h0) ht.ne'
    · linarith
  rw [hb'] at e1
  have ha : t * (g j w - g k w) = 0 := by ring_nf at e1 ⊢; linarith
  rcases mul_eq_zero.1 ha with h0 | h0
  · exact absurd h0 ht.ne'
  · exact ⟨by linarith, hb'⟩

/-! #### Difference quotients -/

/-- The first-order difference quotient on a cone: `Δ_tφ(x̄)(u) = ⟨g k, u⟩ + (t/2)⟨A k u, u⟩` for
`u ∈ T k`, `t > 0` and `‖tu‖ < r`. -/
theorem diffQuot_of_mem (hu : u ∈ T k) (ht : 0 < t) (hs : ‖t • u‖ < r) :
    diffQuot φ x₀ t u = ((g k u + t / 2 * A k u u : ℝ) : EReal) := by
  rw [diffQuot, h.apply_smul hu ht hs, h.eq₀, ← EReal.coe_sub, ← EReal.coe_mul]
  congr 1
  field_simp
  ring

/-- `Δ_tφ(x̄)(u) = ∞` for `u` in none of the cones, `t > 0` and `‖tu‖ < r`. -/
theorem diffQuot_of_not_mem (hu : ∀ k, u ∉ T k) (ht : 0 < t) (hs : ‖t • u‖ < r) :
    diffQuot φ x₀ t u = ⊤ := by
  rw [diffQuot, h.apply_smul_of_not_mem hu ht hs, h.eq₀, EReal.top_sub_coe,
    EReal.coe_mul_top_of_pos (inv_pos.2 ht)]

/-- The second-order difference quotient on a cone:
`Δ²_tφ(x̄, v)(u) = ⟨A k u, u⟩ + (2/t)(⟨g k, u⟩ - ⟨v, u⟩)` for `u ∈ T k`, `t > 0` and `‖tu‖ < r`. -/
theorem secondDiffQuot_of_mem (hu : u ∈ T k) (ht : 0 < t) (hs : ‖t • u‖ < r) :
    secondDiffQuot φ x₀ v t u = ((A k u u + 2 / t * (g k u - v u) : ℝ) : EReal) := by
  rw [secondDiffQuot, h.apply_smul hu ht hs, h.eq₀, ← EReal.coe_sub, ← EReal.coe_sub,
    ← EReal.coe_mul]
  congr 1
  field_simp
  ring

/-- `Δ²_tφ(x̄, v)(u) = ∞` for `u` in none of the cones, `t > 0` and `‖tu‖ < r`. -/
theorem secondDiffQuot_of_not_mem (hu : ∀ k, u ∉ T k) (ht : 0 < t) (hs : ‖t • u‖ < r) :
    secondDiffQuot φ x₀ v t u = ⊤ := by
  rw [secondDiffQuot, h.apply_smul_of_not_mem hu ht hs, h.eq₀, EReal.top_sub_coe,
    EReal.top_sub_coe, EReal.coe_mul_top_of_pos (by positivity)]

variable [Finite ι]

/-- For `u` near `w`, every cone `T k` containing `u` contains `w` (finitely many closed cones). -/
theorem eventually_mem_imp (w : E) : ∀ᶠ u in 𝓝 w, ∀ k, u ∈ T k → w ∈ T k := by
  refine eventually_all.2 fun k ↦ ?_
  by_cases hk : w ∈ T k
  · exact Eventually.of_forall fun _ _ ↦ hk
  · filter_upwards [(h.isClosed k).isOpen_compl.mem_nhds hk] with u hu hu'
    exact absurd hu' hu

/-- Lower bounds for a function which dominates a continuous function on each cone and is `∞`
outside the cones. -/
theorem eventually_le_of_pieces {f : ℝ × E → EReal} {F : ι → ℝ × E → ℝ} {b : ℝ}
    (hF : ∀ k, Continuous (F k))
    (hval : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, ∀ k, p.2 ∈ T k → ((F k p : ℝ) : EReal) ≤ f p)
    (htop : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, (∀ k, p.2 ∉ T k) → f p = ⊤)
    (hb : ∀ k, w ∈ T k → b < F k (0, w)) :
    ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, (b : EReal) ≤ f p := by
  have hmem : ∀ᶠ p : ℝ × E in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, ∀ k, p.2 ∈ T k → w ∈ T k :=
    tendsto_snd.eventually (h.eventually_mem_imp w)
  have hlt : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, ∀ k, w ∈ T k → b < F k p := by
    refine eventually_all.2 fun k ↦ ?_
    by_cases hk : w ∈ T k
    · exact ((tendsto_nhdsGT_prod_of_continuous (hF k) w).eventually
        (lt_mem_nhds (hb k hk))).mono fun p hp _ ↦ hp
    · exact Eventually.of_forall fun p hk' ↦ absurd hk' hk
  filter_upwards [hval, htop, hmem, hlt] with p h1 h2 h3 h4
  by_cases hp : ∃ k, p.2 ∈ T k
  · obtain ⟨k, hk⟩ := hp
    exact (EReal.coe_le_coe_iff.2 (h4 k (h3 k hk)).le).trans (h1 k hk)
  · rw [h2 (not_exists.1 hp)]; exact le_top

/-! #### The subderivative -/

/-- If `b < ⟨g k, w⟩` for every cone `T k` containing `w`, then `b ≤ Δ_tφ(x̄)(u)` eventually as
`t ↓ 0`, `u → w`. -/
theorem eventually_le_diffQuot {b : ℝ} (hb : ∀ k, w ∈ T k → b < g k w) :
    ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, (b : EReal) ≤ diffQuot φ x₀ p.1 p.2 := by
  refine h.eventually_le_of_pieces (F := fun k p ↦ g k p.2 + p.1 / 2 * A k p.2 p.2)
    (fun k ↦ by fun_prop) ?_ ?_ fun k hk ↦ by simpa using hb k hk
  · filter_upwards [h.eventually_small w] with p hp k hk
    rw [h.diffQuot_of_mem hk hp.1 hp.2]
  · filter_upwards [h.eventually_small w] with p hp hk
    exact h.diffQuot_of_not_mem hk hp.1 hp.2

/-- The subderivative on a cone: `dφ(x̄)(w) = ⟨g j, w⟩` for `w ∈ T j`. -/
theorem subderiv_of_mem (hw : w ∈ T j) : subderiv φ x₀ w = (g j w : ℝ) := by
  refine liminf_nhdsGT_prod_eq (fun b hb ↦ h.eventually_le_diffQuot fun k hk ↦ ?_) ?_
  · rw [(h.consistent hk hw).1]; exact_mod_cast hb
  · have ev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        diffQuot φ x₀ t w = ((g j w + t / 2 * A j w w : ℝ) : EReal) :=
      (h.eventually_small' w).mono fun t ht ↦ h.diffQuot_of_mem hw ht.1 ht.2
    refine Tendsto.congr' (EventuallyEq.symm ev) ?_
    simpa using tendsto_coe_nhdsGT (G := fun t ↦ g j w + t / 2 * A j w w) (by fun_prop)

/-- `dφ(x̄)(w) = ∞` for `w` in none of the cones. -/
theorem subderiv_of_not_mem (hw : ∀ k, w ∉ T k) : subderiv φ x₀ w = ⊤ :=
  liminf_nhdsGT_prod_eq_top fun _ ↦ h.eventually_le_diffQuot fun k hk ↦ absurd hk (hw k)

/-! #### The second subderivative `d²φ(x̄)` -/

/-- The second-order difference quotient on a cone: `Δ²_tφ(x̄)(u) = ⟨A k u, u⟩` for `u ∈ T k`,
`t > 0` and `‖tu‖ < r`. -/
theorem secondDiffQuot'_of_mem (hu : u ∈ T k) (ht : 0 < t) (hs : ‖t • u‖ < r) :
    secondDiffQuot' φ x₀ t u = ((A k u u : ℝ) : EReal) := by
  have happ := h.apply_smul hu ht hs
  rw [secondDiffQuot', if_neg, happ, h.eq₀, h.subderiv_of_mem hu, ← EReal.coe_mul,
    ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_mul]
  · congr 1
    field_simp
    ring
  · rintro (⟨h1, -⟩ | ⟨h1, -⟩)
    · rw [happ] at h1; exact EReal.coe_ne_top _ h1
    · rw [happ] at h1; exact EReal.coe_ne_bot _ h1

/-- `Δ²_tφ(x̄)(u) = ∞` for `u` in none of the cones, `t > 0` and `‖tu‖ < r`. -/
theorem secondDiffQuot'_of_not_mem (hu : ∀ k, u ∉ T k) (ht : 0 < t) (hs : ‖t • u‖ < r) :
    secondDiffQuot' φ x₀ t u = ⊤ := by
  rw [secondDiffQuot',
    if_pos (Or.inl ⟨h.apply_smul_of_not_mem hu ht hs, h.subderiv_of_not_mem hu⟩)]

/-- If `b < ⟨A k w, w⟩` for every cone `T k` containing `w`, then `b ≤ Δ²_tφ(x̄)(u)` eventually as
`t ↓ 0`, `u → w`. -/
theorem eventually_le_secondDiffQuot' {b : ℝ} (hb : ∀ k, w ∈ T k → b < A k w w) :
    ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, (b : EReal) ≤ secondDiffQuot' φ x₀ p.1 p.2 := by
  refine h.eventually_le_of_pieces (F := fun k p ↦ A k p.2 p.2)
    (fun k ↦ by fun_prop) ?_ ?_ fun k hk ↦ hb k hk
  · filter_upwards [h.eventually_small w] with p hp k hk
    rw [h.secondDiffQuot'_of_mem hk hp.1 hp.2]
  · filter_upwards [h.eventually_small w] with p hp hk
    exact h.secondDiffQuot'_of_not_mem hk hp.1 hp.2

/-- `Δ²_tφ(x̄)(w) → ⟨A j w, w⟩` as `t ↓ 0` for `w ∈ T j`. -/
theorem tendsto_secondDiffQuot'_of_mem (hw : w ∈ T j) :
    Tendsto (fun t ↦ secondDiffQuot' φ x₀ t w) (𝓝[>] 0) (𝓝 ((A j w w : ℝ) : EReal)) := by
  have ev : ∀ᶠ t in 𝓝[>] (0 : ℝ), secondDiffQuot' φ x₀ t w = ((A j w w : ℝ) : EReal) :=
    (h.eventually_small' w).mono fun t ht ↦ h.secondDiffQuot'_of_mem hw ht.1 ht.2
  exact Tendsto.congr' (EventuallyEq.symm ev) tendsto_const_nhds

/-- The second subderivative on a cone: `d²φ(x̄)(w) = ⟨A j w, w⟩` for `w ∈ T j`. -/
theorem secondSubderiv'_of_mem (hw : w ∈ T j) :
    secondSubderiv' φ x₀ w = ((A j w w : ℝ) : EReal) :=
  liminf_nhdsGT_prod_eq (fun b hb ↦ h.eventually_le_secondDiffQuot' fun k hk ↦ by
    rw [(h.consistent hk hw).2]; exact_mod_cast hb) (h.tendsto_secondDiffQuot'_of_mem hw)

/-- `d²φ(x̄)(w) = ∞` for `w` in none of the cones. -/
theorem secondSubderiv'_of_not_mem (hw : ∀ k, w ∉ T k) : secondSubderiv' φ x₀ w = ⊤ :=
  liminf_nhdsGT_prod_eq_top fun _ ↦
    h.eventually_le_secondDiffQuot' fun k hk ↦ absurd hk (hw k)

/-- [Mordukhovich 2024, (1.127)]: `d²φ(x̄)(w) = lim_{t ↓ 0} Δ²_tφ(x̄)(w)`. -/
theorem tendsto_secondDiffQuot' (w : E) :
    Tendsto (fun t ↦ secondDiffQuot' φ x₀ t w) (𝓝[>] 0) (𝓝 (secondSubderiv' φ x₀ w)) := by
  by_cases hw : ∃ j, w ∈ T j
  · obtain ⟨j, hj⟩ := hw
    rw [h.secondSubderiv'_of_mem hj]
    exact h.tendsto_secondDiffQuot'_of_mem hj
  · rw [h.secondSubderiv'_of_not_mem (not_exists.1 hw)]
    exact tendsto_top_of_eventually_le fun _ ↦
      h.eventually_le_secondDiffQuot' fun k hk ↦ absurd hk (not_exists.1 hw k)

/-- [Mordukhovich 2024, (1.126)]: the local second-order representation. -/
theorem eq_add_subderiv_add (hw : ‖w‖ < r) (hfin : φ (x₀ + w) ≠ ⊤) :
    φ (x₀ + w) = φ x₀ + subderiv φ x₀ w + ((1 / 2 : ℝ) : EReal) * secondSubderiv' φ x₀ w := by
  obtain ⟨j, hj⟩ : ∃ j, w ∈ T j := by
    by_contra hne
    exact hfin (h.eq_top w hw (not_exists.1 hne))
  rw [h.eq_of_mem j w hw hj, h.eq₀, h.subderiv_of_mem hj, h.secondSubderiv'_of_mem hj,
    ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add]

/-! #### The second subderivative `d²φ(x̄, v)` -/

/-- The critical cone of the local model: `w ∈ K_φ(x̄, v)` iff `w ∈ T j` and `⟨g j, w⟩ = ⟨v, w⟩`
for some `j`. -/
theorem mem_criticalCone_iff : w ∈ criticalCone φ x₀ v ↔ ∃ j, w ∈ T j ∧ g j w = v w := by
  change subderiv φ x₀ w = _ ↔ _
  by_cases hw : ∃ j, w ∈ T j
  · obtain ⟨j, hj⟩ := hw
    rw [h.subderiv_of_mem hj, EReal.coe_eq_coe_iff]
    exact ⟨fun he ↦ ⟨j, hj, he⟩, fun ⟨k, hk, he⟩ ↦ by rw [(h.consistent hj hk).1, he]⟩
  · rw [h.subderiv_of_not_mem (not_exists.1 hw)]
    exact iff_of_false (by simp) fun ⟨j, hj, _⟩ ↦ hw ⟨j, hj⟩

/-- For `w` in none of the cones, `d²φ(x̄, v)(w) = ∞` and `Δ²_tφ(x̄, v)(w) → ∞` as `t ↓ 0`. -/
theorem secondSubderiv_of_not_mem (hw : ∀ k, w ∉ T k) :
    secondSubderiv φ x₀ v w = ⊤ ∧
      Tendsto (fun t ↦ secondDiffQuot φ x₀ v t w) (𝓝[>] 0) (𝓝 ⊤) := by
  have hlow : ∀ b : ℝ, ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w,
      (b : EReal) ≤ secondDiffQuot φ x₀ v p.1 p.2 := by
    intro b
    refine h.eventually_le_of_pieces (F := fun _ _ ↦ b) (fun _ ↦ continuous_const) ?_ ?_
      fun k hk ↦ absurd hk (hw k)
    · filter_upwards [tendsto_snd.eventually (h.eventually_mem_imp w)] with p hp k hk
      exact absurd (hp k hk) (hw k)
    · filter_upwards [h.eventually_small w] with p hp hk
      exact h.secondDiffQuot_of_not_mem hk hp.1 hp.2
  exact ⟨liminf_nhdsGT_prod_eq_top hlow, tendsto_top_of_eventually_le hlow⟩

variable (hv : ∀ k, ∀ u ∈ T k, v u ≤ g k u)
include hv

/-- Assume `⟨v, u⟩ ≤ ⟨g k, u⟩` on each cone `T k`. If `b < ⟨A k w, w⟩ + M(⟨g k, w⟩ - ⟨v, w⟩)` for
every cone `T k` containing `w`, then `b ≤ Δ²_tφ(x̄, v)(u)` eventually as `t ↓ 0`, `u → w`. -/
theorem eventually_le_secondDiffQuot {b M : ℝ}
    (hb : ∀ k, w ∈ T k → b < A k w w + M * (g k w - v w)) :
    ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, (b : EReal) ≤ secondDiffQuot φ x₀ v p.1 p.2 := by
  refine h.eventually_le_of_pieces (F := fun k p ↦ A k p.2 p.2 + M * (g k p.2 - v p.2))
    (fun k ↦ by fun_prop) ?_ ?_ fun k hk ↦ hb k hk
  · have hM : ∀ᶠ p : ℝ × E in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, p.1 * M < 2 :=
      tendsto_fst.eventually (nhdsWithin_le_nhds (eventually_mul_lt M two_pos))
    filter_upwards [h.eventually_small w, hM] with p hp hpM k hk
    rw [h.secondDiffQuot_of_mem hk hp.1 hp.2, EReal.coe_le_coe_iff]
    have h1 : M ≤ 2 / p.1 := by rw [le_div_iff₀ hp.1]; linarith
    have h2 : 0 ≤ g k p.2 - v p.2 := sub_nonneg.2 (hv k _ hk)
    linarith [mul_le_mul_of_nonneg_right h1 h2]
  · filter_upwards [h.eventually_small w] with p hp hk
    exact h.secondDiffQuot_of_not_mem hk hp.1 hp.2

/-- Assume `⟨v, u⟩ ≤ ⟨g k, u⟩` on each cone `T k`. For `w ∈ T j` with `⟨g j, w⟩ = ⟨v, w⟩`,
`d²φ(x̄, v)(w) = ⟨A j w, w⟩`, and `Δ²_tφ(x̄, v)(w)` converges to this value as `t ↓ 0`. -/
theorem secondSubderiv_of_mem_of_eq (hw : w ∈ T j) (he : g j w = v w) :
    secondSubderiv φ x₀ v w = ((A j w w : ℝ) : EReal) ∧
      Tendsto (fun t ↦ secondDiffQuot φ x₀ v t w) (𝓝[>] 0) (𝓝 ((A j w w : ℝ) : EReal)) := by
  have hup : Tendsto (fun t ↦ secondDiffQuot φ x₀ v t w) (𝓝[>] 0)
      (𝓝 ((A j w w : ℝ) : EReal)) := by
    have ev : ∀ᶠ t in 𝓝[>] (0 : ℝ), secondDiffQuot φ x₀ v t w = ((A j w w : ℝ) : EReal) :=
      (h.eventually_small' w).mono fun t ht ↦ by
        rw [h.secondDiffQuot_of_mem hw ht.1 ht.2, he, sub_self, mul_zero, add_zero]
    exact Tendsto.congr' (EventuallyEq.symm ev) tendsto_const_nhds
  refine ⟨liminf_nhdsGT_prod_eq (fun b hb ↦ ?_) hup, hup⟩
  refine h.eventually_le_secondDiffQuot hv (M := 0) fun k hk ↦ ?_
  rw [zero_mul, add_zero, (h.consistent hk hw).2]
  exact_mod_cast hb

/-- Assume `⟨v, u⟩ ≤ ⟨g k, u⟩` on each cone `T k`. For `w ∈ T j` with `⟨g j, w⟩ ≠ ⟨v, w⟩`,
`d²φ(x̄, v)(w) = ∞` and `Δ²_tφ(x̄, v)(w) → ∞` as `t ↓ 0`. -/
theorem secondSubderiv_of_mem_of_ne (hw : w ∈ T j) (hne : g j w ≠ v w) :
    secondSubderiv φ x₀ v w = ⊤ ∧
      Tendsto (fun t ↦ secondDiffQuot φ x₀ v t w) (𝓝[>] 0) (𝓝 ⊤) := by
  have hη : 0 < g j w - v w := sub_pos.2 (lt_of_le_of_ne (hv j w hw) (Ne.symm hne))
  have hlow : ∀ b : ℝ, ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w,
      (b : EReal) ≤ secondDiffQuot φ x₀ v p.1 p.2 := by
    intro b
    refine h.eventually_le_secondDiffQuot hv
      (M := (|b - A j w w| + 1) / (g j w - v w)) fun k hk ↦ ?_
    rw [(h.consistent hk hw).1, (h.consistent hk hw).2, div_mul_cancel₀ _ hη.ne']
    linarith [le_abs_self (b - A j w w)]
  exact ⟨liminf_nhdsGT_prod_eq_top hlow, tendsto_top_of_eventually_le hlow⟩

open Classical in
/-- [Mordukhovich 2024, (1.128)]: `d²φ(x̄, v) = d²φ(x̄) + δ_{K_φ(x̄, v)}`. -/
theorem secondSubderiv_eq (w : E) :
    secondSubderiv φ x₀ v w =
      if w ∈ criticalCone φ x₀ v then secondSubderiv' φ x₀ w else ⊤ := by
  by_cases hw : ∃ j, w ∈ T j
  · obtain ⟨j, hj⟩ := hw
    by_cases he : g j w = v w
    · rw [if_pos (h.mem_criticalCone_iff.2 ⟨j, hj, he⟩), h.secondSubderiv'_of_mem hj]
      exact (h.secondSubderiv_of_mem_of_eq hv hj he).1
    · rw [if_neg fun hK ↦ ?_]
      · exact (h.secondSubderiv_of_mem_of_ne hv hj he).1
      · obtain ⟨k, hk, hke⟩ := h.mem_criticalCone_iff.1 hK
        exact he (by rw [(h.consistent hj hk).1, hke])
  · rw [if_neg fun hK ↦ ?_]
    · exact (h.secondSubderiv_of_not_mem (not_exists.1 hw)).1
    · obtain ⟨k, hk, -⟩ := h.mem_criticalCone_iff.1 hK
      exact hw ⟨k, hk⟩

/-- [Mordukhovich 2024, (1.128)]: `d²φ(x̄, v)(w) = lim_{t ↓ 0} Δ²_tφ(x̄, v)(w)`. -/
theorem tendsto_secondDiffQuot (w : E) :
    Tendsto (fun t ↦ secondDiffQuot φ x₀ v t w) (𝓝[>] 0) (𝓝 (secondSubderiv φ x₀ v w)) := by
  by_cases hw : ∃ j, w ∈ T j
  · obtain ⟨j, hj⟩ := hw
    by_cases he : g j w = v w
    · rw [(h.secondSubderiv_of_mem_of_eq hv hj he).1]
      exact (h.secondSubderiv_of_mem_of_eq hv hj he).2
    · rw [(h.secondSubderiv_of_mem_of_ne hv hj he).1]
      exact (h.secondSubderiv_of_mem_of_ne hv hj he).2
  · rw [(h.secondSubderiv_of_not_mem (not_exists.1 hw)).1]
    exact (h.secondSubderiv_of_not_mem (not_exists.1 hw)).2

/-- A function with a local linear-quadratic model at `x̄` on finitely many cones is twice
epi-differentiable at `x̄` for every `v` with `⟨v, u⟩ ≤ ⟨g k, u⟩` on each cone `T k`. -/
theorem twiceEpiDifferentiableAt : TwiceEpiDifferentiableAt φ x₀ v :=
  twiceEpiDifferentiableAt_of_tendsto ⟨φ₀, h.eq₀⟩ (h.tendsto_secondDiffQuot hv)

omit hv

/-! #### Convexity -/

omit [Finite ι] in
/-- For convex `φ`, the quadratic parts of the local model are nonnegative on their cones:
`⟨A j w, w⟩ ≥ 0` for `w ∈ T j`. -/
theorem nonneg_of_convex (hconv : Convex ℝ (φ.Epi univ)) (hw : w ∈ T j) : 0 ≤ A j w w := by
  obtain ⟨t, ht, hsmall⟩ := h.exists_small w
  have h1 := h.apply_smul hw ht (hsmall t ht le_rfl)
  have h2 := h.apply_smul hw (half_pos ht) (hsmall _ (half_pos ht) (by linarith))
  obtain ⟨-, hc⟩ := hconv (x := (x₀, φ₀)) (y := (x₀ + t • w, φ₀ + t * g j w + t ^ 2 / 2 * A j w w))
    ⟨mem_univ _, h.eq₀.le⟩ ⟨mem_univ _, h1.le⟩ (a := 1 / 2) (b := 1 / 2) (by norm_num)
    (by norm_num) (by norm_num)
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hc
  have e : (1 / 2 : ℝ) • x₀ + (1 / 2 : ℝ) • (x₀ + t • w) = x₀ + (t / 2) • w := by module
  rw [e, h2, EReal.coe_le_coe_iff] at hc
  have h3 : 0 ≤ t ^ 2 * A j w w := by ring_nf at hc ⊢; linarith
  exact (mul_nonneg_iff_of_pos_left (by positivity)).1 h3

omit [Finite ι] in
/-- For convex `φ` and `v ∈ ∂φ(x̄)`, `⟨v, u⟩ ≤ ⟨g k, u⟩` for `u ∈ T k`. -/
theorem le_of_mem_subdiff (hconv : Convex ℝ (φ.Epi univ)) (hvs : v ∈ subdiff φ x₀)
    (hu : u ∈ T k) : v u ≤ g k u := by
  rw [mem_subdiff_of_convex hconv h.eq₀] at hvs
  have ev : ∀ᶠ t in 𝓝[>] (0 : ℝ), v u - g k u ≤ t / 2 * A k u u := by
    filter_upwards [h.eventually_small' u] with t ht
    have := hvs (x₀ + t • u)
    rw [h.apply_smul hu ht.1 ht.2, EReal.coe_le_coe_iff, add_sub_cancel_left, map_smul,
      smul_eq_mul] at this
    have h1 : t * (v u - g k u) ≤ t * (t / 2 * A k u u) := by ring_nf at this ⊢; linarith
    exact le_of_mul_le_mul_left h1 ht.1
  have hlim : Tendsto (fun t : ℝ ↦ t / 2 * A k u u) (𝓝[>] 0) (𝓝 0) := by
    have : Continuous fun t : ℝ ↦ t / 2 * A k u u := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  linarith [le_of_tendsto_of_tendsto tendsto_const_nhds hlim ev]

end LocalPLQ

end Local

/-! ### Polyhedral sets -/

section Polyhedral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Set E}

/-- A polyhedral (convex) set: a finite intersection of closed half-spaces. -/
def IsPolyhedral (Ω : Set E) : Prop :=
  ∃ (n : ℕ) (b : Fin n → StrongDual ℝ E) (β : Fin n → ℝ), Ω = {x | ∀ i, b i x ≤ β i}

/-- Polyhedral sets are closed. -/
theorem IsPolyhedral.isClosed (h : IsPolyhedral Ω) : IsClosed Ω := by
  obtain ⟨n, b, β, rfl⟩ := h
  simp only [ofPred_forall]
  exact isClosed_iInter fun i ↦ isClosed_le (b i).continuous continuous_const

/-- The empty set is polyhedral. -/
theorem isPolyhedral_empty : IsPolyhedral (∅ : Set E) :=
  ⟨1, fun _ ↦ 0, fun _ ↦ -1, by ext x; simp⟩

/-- The intersection of a polyhedral set with a closed half-space `{x | ⟨c, x⟩ ≤ γ}` is
polyhedral. -/
theorem IsPolyhedral.inter_halfspace (h : IsPolyhedral Ω) (c : StrongDual ℝ E) (γ : ℝ) :
    IsPolyhedral (Ω ∩ {x | c x ≤ γ}) := by
  obtain ⟨n, b, β, rfl⟩ := h
  refine ⟨n + 1, Fin.cons c b, Fin.cons γ β, ?_⟩
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
  exact and_comm

/-- Around any point, a polyhedral set is a translated polyhedral cone (its tangent cone; empty
if the point is not in the set). -/
theorem IsPolyhedral.exists_cone (h : IsPolyhedral Ω) (x₀ : E) :
    ∃ T : Set E, IsPolyhedral T ∧ (∀ (c : ℝ) w, 0 < c → w ∈ T → c • w ∈ T) ∧
      (T.Nonempty → x₀ ∈ Ω) ∧ ∃ r > (0 : ℝ), ∀ w, ‖w‖ < r → (x₀ + w ∈ Ω ↔ w ∈ T) := by
  by_cases hx : x₀ ∈ Ω
  · obtain ⟨n, b, β, rfl⟩ := h
    classical
    have hx' : ∀ i, b i x₀ ≤ β i := hx
    have hev : ∀ᶠ w in 𝓝 (0 : E), ∀ i, b i x₀ < β i → b i (x₀ + w) < β i := by
      refine eventually_all.2 fun i ↦ ?_
      by_cases hi : b i x₀ < β i
      · have hc : Continuous fun w : E ↦ b i (x₀ + w) := by fun_prop
        exact ((hc.tendsto' 0 (b i x₀) (by simp)).eventually (gt_mem_nhds hi)).mono
          fun w hw _ ↦ hw
      · exact Eventually.of_forall fun w hi' ↦ absurd hi' hi
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hev
    refine ⟨{w | ∀ i, (if b i x₀ = β i then b i else 0) w ≤ 0}, ⟨n, _, fun _ ↦ 0, rfl⟩, ?_,
      fun _ ↦ hx, r, hr, fun w hw ↦ ?_⟩
    · intro c w hc hw i
      have := hw i
      rw [map_smul, smul_eq_mul]
      nlinarith
    · have hw' := hball (y := w) (by rwa [dist_zero_right])
      change (∀ i, b i (x₀ + w) ≤ β i) ↔ ∀ i, (if b i x₀ = β i then b i else 0) w ≤ 0
      constructor
      · intro hall i
        split_ifs with hi
        · have := hall i
          rw [map_add, hi] at this
          linarith
        · simp
      · intro hall i
        by_cases hi : b i x₀ = β i
        · have := hall i
          rw [if_pos hi] at this
          rw [map_add, hi]
          linarith
        · exact (hw' i (lt_of_le_of_ne (hx' i) hi)).le
  · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 h.isClosed.isOpen_compl x₀ hx
    exact ⟨∅, isPolyhedral_empty, fun _ _ _ hw ↦ absurd hw (notMem_empty _),
      fun ⟨w, hw⟩ ↦ absurd hw (notMem_empty _), r, hr, fun w hw ↦
        iff_of_false (hball (by simpa [dist_eq_norm] using hw)) (notMem_empty _)⟩

end Polyhedral

/-! ### Piecewise linear-quadratic functions and Thm. 1.91 -/

section PLQ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {φ : E → EReal} {x₀ : E} {v : StrongDual ℝ E}

/-- [Mordukhovich 2024, Def. 1.59(i)]: `φ` is piecewise linear-quadratic if `dom φ` is the union
of finitely many polyhedral sets, on each of which `φ(x) = ½⟨x, Ax⟩ + ⟨a, x⟩ + α` with `A`
symmetric. The symmetric operator `A` is given as a symmetric bilinear form. -/
def IsPLQ (φ : E → EReal) : Prop :=
  ∃ (s : ℕ) (Ω : Fin s → Set E) (A : Fin s → E →L[ℝ] StrongDual ℝ E)
    (a : Fin s → StrongDual ℝ E) (α : Fin s → ℝ),
    (∀ j, IsPolyhedral (Ω j)) ∧ (∀ j x y, A j x y = A j y x) ∧ {x | φ x ≠ ⊤} = ⋃ j, Ω j ∧
    ∀ j, ∀ x ∈ Ω j, φ x = ((1 / 2 * A j x x + a j x + α j : ℝ) : EReal)

/-- [Mordukhovich 2024, Def. 1.59(ii)]: piecewise linear functions. -/
def IsPiecewiseLinear (φ : E → EReal) : Prop :=
  ∃ (s : ℕ) (Ω : Fin s → Set E) (a : Fin s → StrongDual ℝ E) (α : Fin s → ℝ),
    (∀ j, IsPolyhedral (Ω j)) ∧ {x | φ x ≠ ⊤} = ⋃ j, Ω j ∧
    ∀ j, ∀ x ∈ Ω j, φ x = ((a j x + α j : ℝ) : EReal)

/-- Piecewise linear functions are piecewise linear-quadratic (with `A = 0`). -/
theorem IsPiecewiseLinear.isPLQ (h : IsPiecewiseLinear φ) : IsPLQ φ := by
  obtain ⟨s, Ω, a, α, hΩ, hdom, hval⟩ := h
  exact ⟨s, Ω, fun _ ↦ 0, a, α, hΩ, fun _ _ _ ↦ rfl, hdom, fun j x hx ↦ by
    rw [hval j x hx]; simp⟩

/-- Around a point of its domain, a piecewise linear-quadratic function has a local
linear-quadratic model on polyhedral cones [Mordukhovich 2024, proof of Thm. 1.91]. -/
theorem IsPLQ.exists_localPLQ (hφ : IsPLQ φ) (hx₀ : φ x₀ ≠ ⊤) :
    ∃ (s : ℕ) (T : Fin s → Set E) (g : Fin s → StrongDual ℝ E)
      (A : Fin s → E →L[ℝ] StrongDual ℝ E) (φ₀ r : ℝ),
      LocalPLQ φ x₀ T g A φ₀ r ∧ (∀ j, IsPolyhedral (T j)) ∧ ∀ j x y, A j x y = A j y x := by
  obtain ⟨s, Ω, A, a, α, hΩ, hsym, hdom, hval⟩ := hφ
  choose T hTpoly hTsmul hTne rT hrT hT using fun j ↦ (hΩ j).exists_cone x₀
  obtain ⟨r, hr, hrj⟩ : ∃ r : ℝ, 0 < r ∧ ∀ j, r < rT j := by
    have h1 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ j, ρ < rT j :=
      eventually_all.2 fun j ↦ nhdsWithin_le_nhds (gt_mem_nhds (hrT j))
    exact ((eventually_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0)).and h1).exists
  obtain ⟨j₀, hj₀⟩ : ∃ j, x₀ ∈ Ω j := by
    have : x₀ ∈ {x | φ x ≠ ⊤} := hx₀
    rw [hdom] at this
    exact mem_iUnion.1 this
  have h0 := hval j₀ x₀ hj₀
  refine ⟨s, T, fun j ↦ A j x₀ + a j, A, 1 / 2 * A j₀ x₀ x₀ + a j₀ x₀ + α j₀, r,
    ⟨hr, h0, fun j ↦ (hTpoly j).isClosed, hTsmul, fun j w hw hwT ↦ ?_, fun w hw hwT ↦ ?_⟩,
    hTpoly, hsym⟩
  · have hxj : x₀ ∈ Ω j := hTne j ⟨w, hwT⟩
    have hmem : x₀ + w ∈ Ω j := (hT j w (hw.trans (hrj j))).2 hwT
    have e0 := (hval j x₀ hxj).symm.trans h0
    rw [EReal.coe_eq_coe_iff] at e0
    rw [hval j _ hmem, EReal.coe_eq_coe_iff]
    simp only [map_add, add_apply]
    linarith [hsym j w x₀]
  · by_contra hne
    have : x₀ + w ∈ {x | φ x ≠ ⊤} := hne
    rw [hdom] at this
    obtain ⟨j, hj⟩ := mem_iUnion.1 this
    exact hwT j ((hT j w (hw.trans (hrj j))).1 hj)

/-- The local model at `x̄` for a convex piecewise linear-quadratic function and a subgradient
`v ∈ ∂φ(x̄)`: `⟨v, u⟩ ≤ ⟨g j, u⟩` on each cone and the quadratic parts are nonnegative. -/
theorem IsPLQ.exists_localPLQ_of_mem_subdiff (hφ : IsPLQ φ) (hconv : Convex ℝ (φ.Epi univ))
    (hv : v ∈ subdiff φ x₀) :
    ∃ (s : ℕ) (T : Fin s → Set E) (g : Fin s → StrongDual ℝ E)
      (A : Fin s → E →L[ℝ] StrongDual ℝ E) (φ₀ r : ℝ),
      LocalPLQ φ x₀ T g A φ₀ r ∧ (∀ j, IsPolyhedral (T j)) ∧ (∀ j x y, A j x y = A j y x) ∧
        ∀ k, ∀ u ∈ T k, v u ≤ g k u := by
  have hx₀ : φ x₀ ≠ ⊤ := by
    obtain ⟨r, hr, -⟩ := hv
    rw [hr]
    exact EReal.coe_ne_top _
  obtain ⟨s, T, g, A, φ₀, r, h, hT, hsym⟩ := hφ.exists_localPLQ hx₀
  exact ⟨s, T, g, A, φ₀, r, h, hT, hsym, fun k u hu ↦ h.le_of_mem_subdiff hconv hv hu⟩

/-- [Mordukhovich 2024, Thm. 1.91(i), (1.126)]: the local second-order representation of a
piecewise linear-quadratic function. -/
theorem IsPLQ.exists_eq_add_subderiv_add (hφ : IsPLQ φ) (hx₀ : φ x₀ ≠ ⊤) :
    ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, φ x ≠ ⊤ → φ x = φ x₀ + subderiv φ x₀ (x - x₀) +
      ((1 / 2 : ℝ) : EReal) * secondSubderiv' φ x₀ (x - x₀) := by
  obtain ⟨s, T, g, A, φ₀, r, h, -, -⟩ := hφ.exists_localPLQ hx₀
  refine ⟨ball x₀ r, ball_mem_nhds _ h.r_pos, fun x hx hfin ↦ ?_⟩
  have hw : ‖x - x₀‖ < r := by rwa [← dist_eq_norm]
  have := h.eq_add_subderiv_add hw (by rwa [add_sub_cancel])
  rwa [add_sub_cancel] at this

/-- [Mordukhovich 2024, Thm. 1.91(ii), (1.127)]: `d²φ(x̄)(w) = lim_{t ↓ 0} Δ²_tφ(x̄)(w)`. -/
theorem IsPLQ.tendsto_secondDiffQuot' (hφ : IsPLQ φ) (hx₀ : φ x₀ ≠ ⊤) (w : E) :
    Tendsto (fun t ↦ secondDiffQuot' φ x₀ t w) (𝓝[>] 0) (𝓝 (secondSubderiv' φ x₀ w)) := by
  obtain ⟨s, T, g, A, φ₀, r, h, -, -⟩ := hφ.exists_localPLQ hx₀
  exact h.tendsto_secondDiffQuot' w

/-- [Mordukhovich 2024, Thm. 1.91(ii), (1.127)]: `d²φ(x̄)(w) ≥ 0` for convex `φ`. -/
theorem IsPLQ.secondSubderiv'_nonneg (hφ : IsPLQ φ) (hconv : Convex ℝ (φ.Epi univ))
    (hx₀ : φ x₀ ≠ ⊤) (w : E) : 0 ≤ secondSubderiv' φ x₀ w := by
  obtain ⟨s, T, g, A, φ₀, r, h, -, -⟩ := hφ.exists_localPLQ hx₀
  by_cases hw : ∃ j, w ∈ T j
  · obtain ⟨j, hj⟩ := hw
    rw [h.secondSubderiv'_of_mem hj]
    exact_mod_cast h.nonneg_of_convex hconv hj
  · rw [h.secondSubderiv'_of_not_mem (not_exists.1 hw)]
    exact le_top

/-- [Mordukhovich 2024, Thm. 1.91(ii)]: `d²φ(x̄)` is piecewise linear-quadratic. -/
theorem IsPLQ.isPLQ_secondSubderiv' (hφ : IsPLQ φ) (hx₀ : φ x₀ ≠ ⊤) :
    IsPLQ (secondSubderiv' φ x₀) := by
  obtain ⟨s, T, g, A, φ₀, r, h, hT, hsym⟩ := hφ.exists_localPLQ hx₀
  refine ⟨s, T, fun j ↦ (2 : ℝ) • A j, fun _ ↦ 0, fun _ ↦ 0, hT,
    fun j x y ↦ by simp [hsym j x y], ?_, fun j w hw ↦ ?_⟩
  · ext w
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro hne
      by_contra hno
      exact hne (h.secondSubderiv'_of_not_mem (not_exists.1 hno))
    · rintro ⟨j, hj⟩
      rw [h.secondSubderiv'_of_mem hj]
      exact EReal.coe_ne_top _
  · rw [h.secondSubderiv'_of_mem hw]
    congr 1
    simp

/-- [Mordukhovich 2024, Thm. 1.91(iii), (1.128)]:
`d²φ(x̄, v)(w) = lim_{t ↓ 0} Δ²_tφ(x̄, v)(w)`. -/
theorem IsPLQ.tendsto_secondDiffQuot (hφ : IsPLQ φ) (hconv : Convex ℝ (φ.Epi univ))
    (hv : v ∈ subdiff φ x₀) (w : E) :
    Tendsto (fun t ↦ secondDiffQuot φ x₀ v t w) (𝓝[>] 0) (𝓝 (secondSubderiv φ x₀ v w)) := by
  obtain ⟨s, T, g, A, φ₀, r, h, -, -, hvg⟩ := hφ.exists_localPLQ_of_mem_subdiff hconv hv
  exact h.tendsto_secondDiffQuot hvg w

/-- [Mordukhovich 2024, Thm. 1.91(i)]: a convex piecewise linear-quadratic function is twice
epi-differentiable at `x̄` for every `v ∈ ∂φ(x̄)`. -/
theorem IsPLQ.twiceEpiDifferentiableAt (hφ : IsPLQ φ) (hconv : Convex ℝ (φ.Epi univ))
    (hv : v ∈ subdiff φ x₀) : TwiceEpiDifferentiableAt φ x₀ v := by
  obtain ⟨s, T, g, A, φ₀, r, h, -, -, hvg⟩ := hφ.exists_localPLQ_of_mem_subdiff hconv hv
  exact h.twiceEpiDifferentiableAt hvg

open Classical in
/-- [Mordukhovich 2024, Thm. 1.91(iii), (1.128)]:
`d²φ(x̄, v)(w) = d²φ(x̄)(w) + δ(w; K_φ(x̄, v))`. -/
theorem IsPLQ.secondSubderiv_eq (hφ : IsPLQ φ) (hconv : Convex ℝ (φ.Epi univ))
    (hv : v ∈ subdiff φ x₀) (w : E) :
    secondSubderiv φ x₀ v w =
      if w ∈ criticalCone φ x₀ v then secondSubderiv' φ x₀ w else ⊤ := by
  obtain ⟨s, T, g, A, φ₀, r, h, -, -, hvg⟩ := hφ.exists_localPLQ_of_mem_subdiff hconv hv
  exact h.secondSubderiv_eq hvg w

/-- [Mordukhovich 2024, Thm. 1.91(iii)]: `d²φ(x̄, v)` is convex. -/
theorem IsPLQ.convex_epi_secondSubderiv (hφ : IsPLQ φ) (hconv : Convex ℝ (φ.Epi univ))
    (hv : v ∈ subdiff φ x₀) : Convex ℝ ((secondSubderiv φ x₀ v).Epi univ) :=
  VariationalAnalysis.convex_epi_secondSubderiv hconv (hφ.twiceEpiDifferentiableAt hconv hv)

/-- [Mordukhovich 2024, Thm. 1.91(iii)]: `d²φ(x̄, v)` is piecewise linear-quadratic. -/
theorem IsPLQ.isPLQ_secondSubderiv (hφ : IsPLQ φ) (hconv : Convex ℝ (φ.Epi univ))
    (hv : v ∈ subdiff φ x₀) : IsPLQ (secondSubderiv φ x₀ v) := by
  obtain ⟨s, T, g, A, φ₀, r, h, hT, hsym, hvg⟩ := hφ.exists_localPLQ_of_mem_subdiff hconv hv
  refine ⟨s, fun j ↦ T j ∩ {w | (g j - v) w ≤ 0}, fun j ↦ (2 : ℝ) • A j, fun _ ↦ 0,
    fun _ ↦ 0, fun j ↦ (hT j).inter_halfspace _ _, fun j x y ↦ by simp [hsym j x y], ?_,
    fun j w hw ↦ ?_⟩
  · ext w
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, sub_apply, sub_nonpos]
    constructor
    · intro hne
      by_contra hno
      refine hne ?_
      by_cases hw : ∃ j, w ∈ T j
      · obtain ⟨j, hj⟩ := hw
        exact (h.secondSubderiv_of_mem_of_ne hvg hj fun he ↦ hno ⟨j, hj, he.le⟩).1
      · exact (h.secondSubderiv_of_not_mem (not_exists.1 hw)).1
    · rintro ⟨j, hj, hle⟩
      rw [(h.secondSubderiv_of_mem_of_eq hvg hj (le_antisymm hle (hvg j w hj))).1]
      exact EReal.coe_ne_top _
  · obtain ⟨hw1, hw2⟩ := hw
    have hle : g j w ≤ v w := by simpa using hw2
    rw [(h.secondSubderiv_of_mem_of_eq hvg hw1 (le_antisymm hle (hvg j w hw1))).1]
    congr 1
    simp

/-- [Mordukhovich 2024, Thm. 1.91(iii)]: the critical cone `K_φ(x̄, v)` is a finite union of
polyhedral cones. -/
theorem IsPLQ.exists_criticalCone_eq (hφ : IsPLQ φ) (hconv : Convex ℝ (φ.Epi univ))
    (hv : v ∈ subdiff φ x₀) :
    ∃ (s : ℕ) (K : Fin s → Set E), (∀ j, IsPolyhedral (K j)) ∧
      (∀ j (c : ℝ) w, 0 < c → w ∈ K j → c • w ∈ K j) ∧ criticalCone φ x₀ v = ⋃ j, K j := by
  obtain ⟨s, T, g, A, φ₀, r, h, hT, -, hvg⟩ := hφ.exists_localPLQ_of_mem_subdiff hconv hv
  refine ⟨s, fun j ↦ T j ∩ {w | (g j - v) w ≤ 0}, fun j ↦ (hT j).inter_halfspace _ _,
    fun j c w hc hw ↦ ⟨h.smul_mem j c w hc hw.1, ?_⟩, ?_⟩
  · have : (g j - v) w ≤ 0 := hw.2
    change (g j - v) (c • w) ≤ 0
    rw [map_smul, smul_eq_mul]
    nlinarith
  · ext w
    rw [h.mem_criticalCone_iff]
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, sub_apply, sub_nonpos]
    exact ⟨fun ⟨j, hj, he⟩ ↦ ⟨j, hj, he.le⟩,
      fun ⟨j, hj, hle⟩ ↦ ⟨j, hj, le_antisymm hle (hvg j w hj)⟩⟩

end PLQ

end VariationalAnalysis
