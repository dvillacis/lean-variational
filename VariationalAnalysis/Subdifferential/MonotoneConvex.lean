/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis.Subdifferential.MeanValueIneq

/-!
# Monotonicity of functions and convexity from monotone subgradients

Applications of the approximate mean value theorem [Mordukhovich 2018, Section 4.4.3].

## Main results

* `antitone_iff_regularSubdiff_subset_polar`: Thm. 4.18 of [Mordukhovich 2018]
  (subdifferential characterization of `K`-monotonicity; the directions are
  `regularSubdiff_subset_polar_of_antitone` and `antitone_of_regularSubdiff_subset_polar`).
* `le_of_mem_regularSubdiff_of_monotone`: (4.28) of [Mordukhovich 2018]: for a globally
  monotone `∂̂φ`, regular subgradients are subgradients of convex analysis.
* `convex_epi_of_monotone_regularSubdiff`, `convex_epi_of_monotone_subdiff`: Thm. 4.19 of
  [Mordukhovich 2018] (global monotonicity of `∂̂φ` or of `∂φ` implies convexity of `φ`).

## Remarks on the book

* Thm. 4.18: the implication (b) ⇒ (a) needs the segments `[x, u]`, `x, u ∈ U`, to lie in `U`;
  it is stated for open convex `U` (see the docstring of
  `antitone_iff_regularSubdiff_subset_polar` for a counterexample otherwise). The cone `K` only
  needs to be invariant under positive scalings, and only for (a) ⇒ (b).
* Thm. 4.19: `φ : E → EReal` is l.s.c. with no value `⊥` (the book's `φ : ℝⁿ → (-∞, ∞]`), and
  convexity of `φ` is the convexity of its epigraph. The book's "we can always suppose that
  `0 ∈ ∂̂φ(uₖ)`" is the reduction `le_convex_comb_of_mem_regularSubdiff` (subtract a linear
  function); after it, `uₖ` is a global minimizer by (4.28). The proof then follows the book's
  two cases (`le_convex_comb_of_zero_mem`); in the second case a single point `s` close to `w`
  with `φ(s) < φ(w)` suffices, by lower semicontinuity at `w`.
-/

open Filter Topology Set Metric
open scoped NNReal

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section ConeMonotone

variable {φ : E → EReal} {U K : Set E}

/-- Thm. 4.18 of [Mordukhovich 2018], (a) ⇒ (b): if `φ` is `K`-nonincreasing on an open set `U`
(`x, u ∈ U`, `u - x ∈ K` imply `φ(u) ≤ φ(x)`) for a cone `K`, then `∂̂φ(x) ⊆ K*` for `x ∈ U`,
where `K* = {x* | ⟨x*, w⟩ ≤ 0 for all w ∈ K}` is the polar cone. -/
theorem regularSubdiff_subset_polar_of_antitone (hU : IsOpen U)
    (hK : ∀ w ∈ K, ∀ t : ℝ, 0 < t → t • w ∈ K)
    (hmono : ∀ x ∈ U, ∀ u ∈ U, u - x ∈ K → φ u ≤ φ x) :
    ∀ x ∈ U, ∀ v ∈ regularSubdiff φ x, ∀ w ∈ K, v w ≤ 0 := by
  intro x hx v hv w hw
  obtain ⟨r, hr, hv'⟩ := hv
  refine le_of_forall_pos_le_add_mul (c := ‖w‖) fun ε hε ↦ ?_
  rw [zero_add]
  refine le_of_eventually_ray (Ω := {y | y ∈ U ∧ y - x ∈ K}) (x₀ := x) (d := w) ?_ ?_
  · rw [eventually_nhdsWithin_iff]
    filter_upwards [hv' ε hε] with y hy hyΩ
    have h := hy.trans (hmono x hx y hyΩ.1 hyΩ.2)
    rw [hr, EReal.coe_le_coe_iff] at h
    linarith
  · have hT : Tendsto (fun t : ℝ ↦ x + t • w) (𝓝 0) (𝓝 (x + (0 : ℝ) • w)) :=
      ((continuous_id.smul continuous_const).const_add x).tendsto 0
    rw [zero_smul, add_zero] at hT
    filter_upwards [nhdsWithin_le_nhds (hT (hU.mem_nhds hx)), self_mem_nhdsWithin] with t ht ht0
    exact ⟨ht, by rw [add_sub_cancel_left]; exact hK w hw t ht0⟩

variable [FiniteDimensional ℝ E]

/-- Thm. 4.18 of [Mordukhovich 2018], (b) ⇒ (a): if `φ` is l.s.c. on an open convex set `U` with
no value `⊥` there, and `∂̂φ(x) ⊆ K*` for all `x ∈ U`, then `φ` is `K`-nonincreasing on `U`. The
proof uses the mean value inequality of Cor. 4.14(i). -/
theorem antitone_of_regularSubdiff_subset_polar (hU : IsOpen U) (hUc : Convex ℝ U)
    (hlsc : ∀ x ∈ U, LowerSemicontinuousAt φ x) (hbot : ∀ x ∈ U, φ x ≠ ⊥)
    (hpol : ∀ x ∈ U, ∀ v ∈ regularSubdiff φ x, ∀ w ∈ K, v w ≤ 0) :
    ∀ x ∈ U, ∀ u ∈ U, u - x ∈ K → φ u ≤ φ x := by
  intro x hx u hu hux
  by_contra hlt
  push Not at hlt
  obtain ⟨α, hα⟩ := exists_eq_coe_of_ne_bot_of_ne_top (hbot x hx) (ne_top_of_lt hlt)
  have hseg : segment ℝ x u ⊆ U := hUc.segment_subset hx hu
  obtain ⟨c, hc, y, v, hy, hv, hineq⟩ := mean_value_ineq hα
    (fun z hz ↦ eventually_of_mem (hU.mem_nhds (hseg hz)) hlsc) (fun z hz ↦ hbot z (hseg hz))
  have hpos : (0 : EReal) < φ u - α := by
    rw [hα] at hlt
    exact EReal.sub_pos.2 hlt
  obtain ⟨M, hM0, hM⟩ := EReal.lt_iff_exists_real_btwn.1 hpos
  rw [EReal.coe_pos] at hM0
  obtain ⟨k, hk1, hk2⟩ := ((hineq M hM).and
    ((tendsto_funNhds_iff.1 hy).1.eventually (hU.mem_nhds (hseg hc)))).exists
  have := hpol (y k) hk2 (v k) (hv k) (u - x) hux
  linarith

/-- Thm. 4.18 of [Mordukhovich 2018] (subdifferential characterization of monotonicity for
l.s.c. functions): let `φ` be l.s.c. on an open convex set `U` with no value `⊥` there, and let
`K` be a cone with polar `K* = {x* | ⟨x*, w⟩ ≤ 0 for all w ∈ K}`. Then `φ` is `K`-nonincreasing
on `U` (`x, u ∈ U`, `u - x ∈ K` imply `φ(u) ≤ φ(x)`) if and only if `∂̂φ(x) ⊆ K*` for all
`x ∈ U`. The convexity of `U`, not in the book's statement, is needed for "if": for `U` the union
of two disjoint balls, `K = E` and `φ` equal to `0` on one ball and `1` on the other, `∂̂φ ⊆ {0}`
but `φ` is not `K`-nonincreasing. -/
theorem antitone_iff_regularSubdiff_subset_polar (hU : IsOpen U) (hUc : Convex ℝ U)
    (hK : ∀ w ∈ K, ∀ t : ℝ, 0 < t → t • w ∈ K)
    (hlsc : ∀ x ∈ U, LowerSemicontinuousAt φ x) (hbot : ∀ x ∈ U, φ x ≠ ⊥) :
    (∀ x ∈ U, ∀ u ∈ U, u - x ∈ K → φ u ≤ φ x) ↔
      ∀ x ∈ U, ∀ v ∈ regularSubdiff φ x, ∀ w ∈ K, v w ≤ 0 :=
  ⟨regularSubdiff_subset_polar_of_antitone hU hK,
    antitone_of_regularSubdiff_subset_polar hU hUc hlsc hbot⟩

end ConeMonotone

section Convexity

variable [FiniteDimensional ℝ E] {φ : E → EReal}

/-- Thm. 4.19 of [Mordukhovich 2018], first step, (4.28): if `φ` is l.s.c. with no value `⊥`
and `∂̂φ` is globally monotone (4.27), then every regular subgradient is a subgradient in the
sense of convex analysis: `φ(x) + ⟨v, u - x⟩ ≤ φ(u)` for all `u`, for `v ∈ ∂̂φ(x)`. The proof
uses (4.22) of Thm. 4.13 on `[u, x]`. -/
theorem le_of_mem_regularSubdiff_of_monotone (hlsc : LowerSemicontinuous φ)
    (hbot : ∀ x, φ x ≠ ⊥)
    (hmono : ∀ x₁ x₂, ∀ v₁ ∈ regularSubdiff φ x₁, ∀ v₂ ∈ regularSubdiff φ x₂,
      0 ≤ (v₁ - v₂) (x₁ - x₂))
    {x : E} {r : ℝ} (hr : φ x = r) {v : StrongDual ℝ E} (hv : v ∈ regularSubdiff φ x) (u : E) :
    ((r + v (u - x) : ℝ) : EReal) ≤ φ u := by
  by_cases htop : φ u = ⊤
  · rw [htop]; exact le_top
  obtain ⟨s, hs⟩ := exists_eq_coe_of_ne_bot_of_ne_top (hbot u) htop
  rcases eq_or_ne u x with rfl | hux
  · rw [sub_self, map_zero, add_zero, ← hr]
  have hlsc' : ∀ y ∈ segment ℝ u x, ∀ᶠ z in 𝓝 y, LowerSemicontinuousAt φ z :=
    fun _ _ ↦ Eventually.of_forall fun z ↦ hlsc z
  obtain ⟨c, hc, hcx, hmin⟩ := exists_isMinOn_approx_mean_value hux hs hr fun y _ ↦ hlsc y
  obtain ⟨xs, vs, hxs, hvs, h1, -, -⟩ :=
    approx_mean_value hux hs hlsc' (fun y _ ↦ hbot y) hc hcx hmin
  set D := ‖x - u‖ with hD
  have hDpos : 0 < D := norm_pos_iff.2 (sub_ne_zero.2 hux.symm)
  have hlim : Tendsto (fun k ↦ v (x - xs k)) atTop (𝓝 (v (x - c))) :=
    (v.continuous.tendsto _).comp (tendsto_const_nhds.sub (tendsto_funNhds_iff.1 hxs).1)
  have hA : (r - s) / D * ‖x - c‖ ≤ v (x - c) := by
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    have hev : ∀ᶠ k in atTop, (r - s) / D * ‖x - c‖ - ε ≤ v (x - xs k) :=
      (h1 ε hε).mono fun k hk ↦ by
        have hm := hmono x (xs k) v hv (vs k) (hvs k)
        rw [sub_apply] at hm
        linarith
    have := ge_of_tendsto hlim hev
    linarith
  obtain ⟨τ, ⟨hτ0, hτ1⟩, rfl⟩ := mem_segment_iff_eq_add_smul.1 hc
  have hτ1' : τ < 1 := lt_of_le_of_ne hτ1 fun h ↦ hcx (by rw [h, one_smul]; abel)
  rw [norm_sub_add_smul_sub hτ1,
    show x - (u + τ • (x - u)) = (1 - τ) • (x - u) by rw [sub_smul, one_smul]; abel,
    map_smul, smul_eq_mul, ← hD] at hA
  have hA' : (r - s) * (1 - τ) ≤ v (x - u) * (1 - τ) := by
    have : (r - s) / D * ((1 - τ) * D) = (r - s) * (1 - τ) := by field_simp
    linarith
  have hrs := le_of_mul_le_mul_right hA' (by linarith)
  rw [hs, EReal.coe_le_coe_iff, show u - x = -(x - u) by abel, map_neg]
  linarith

/-- Thm. 4.19 of [Mordukhovich 2018], second step, normalized: if `φ` is l.s.c. with no value
`⊥`, `∂̂φ` is globally monotone, `0 ∈ ∂̂φ(u)`, and `φ` is finite at `u` and `x`, then
`φ(θ u + (1 - θ) x) ≤ θ φ(u) + (1 - θ) φ(x)` for `0 < θ < 1`. The proof follows the book: first
`θ u + (1 - θ) x ∈ dom φ` (by Thm. 4.13 applied to `φ` modified at `θ u + (1 - θ) x`), then the
two cases whether `θ u + (1 - θ) x` is a local minimizer of `φ` or not. -/
theorem le_convex_comb_of_zero_mem (hlsc : LowerSemicontinuous φ) (hbot : ∀ x, φ x ≠ ⊥)
    (hmono : ∀ x₁ x₂, ∀ v₁ ∈ regularSubdiff φ x₁, ∀ v₂ ∈ regularSubdiff φ x₂,
      0 ≤ (v₁ - v₂) (x₁ - x₂))
    {u x : E} {α β θ : ℝ} (hu : φ u = α) (hx : φ x = β) (h0 : 0 ∈ regularSubdiff φ u)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    φ (θ • u + (1 - θ) • x) ≤ ((θ * α + (1 - θ) * β : ℝ) : EReal) := by
  set w := θ • u + (1 - θ) • x with hwdef
  have hlsc' : ∀ (a b : E), ∀ y ∈ segment ℝ a b, ∀ᶠ z in 𝓝 y, LowerSemicontinuousAt φ z :=
    fun _ _ _ _ ↦ Eventually.of_forall fun z ↦ hlsc z
  have hglob : ∀ y, (α : EReal) ≤ φ y := fun y ↦ by
    have := le_of_mem_regularSubdiff_of_monotone hlsc hbot hmono hu h0 y
    simpa using this
  have hwx : w - x = θ • (u - x) := by rw [hwdef, smul_sub, sub_smul, one_smul]; abel
  -- `w ∈ dom φ`
  have hwtop : φ w ≠ ⊤ := by
    intro htop
    have hxu : x ≠ u := by
      rintro rfl
      rw [hwdef, ← add_smul, add_sub_cancel, one_smul, hu] at htop
      exact EReal.coe_ne_top α htop
    have hxw : x ≠ w := by
      intro h
      have : w - x = 0 := by rw [h, sub_self]
      rw [hwx, smul_eq_zero] at this
      rcases this with h1 | h1
      · linarith
      · exact hxu (sub_eq_zero.1 h1).symm
    obtain ⟨c, -, hcw, -, z, v, -, hv, h1, h2⟩ := approx_mean_value_of_le (β := β + 1) hxw hx
      (by rw [htop]; exact le_top) (hlsc' x w) (fun y _ ↦ hbot y)
    have hA : 0 < ‖w - c‖ / ‖w - x‖ := div_pos (norm_pos_iff.2 (sub_ne_zero.2 hcw.symm))
      (norm_pos_iff.2 (sub_ne_zero.2 hxw.symm))
    obtain ⟨k, hk1, hk2⟩ := ((h1 _ (half_pos hA)).and (h2 (1 / 2) one_half_pos)).exists
    have hm := hmono (z k) u (v k) (hv k) 0 h0
    have hdec : v k (u - z k) = v k (w - z k) + (1 - θ) / θ * v k (w - x) := by
      have e : u - z k = (w - z k) + ((1 - θ) / θ) • (w - x) := by
        rw [hwx, smul_smul, div_mul_cancel₀ _ hθ0.ne', hwdef]
        module
      rw [e, map_add, map_smul, smul_eq_mul]
    rw [sub_zero, show z k - u = -(u - z k) by abel, map_neg, hdec] at hm
    have e : (β + 1 - β) / ‖w - x‖ * ‖w - c‖ = ‖w - c‖ / ‖w - x‖ := by ring
    rw [e] at hk1
    have hθ' : 0 ≤ (1 - θ) / θ := div_nonneg (by linarith) hθ0.le
    have : 0 ≤ (1 - θ) / θ * v k (w - x) := mul_nonneg hθ' (by linarith)
    linarith
  obtain ⟨γ, hγ⟩ := exists_eq_coe_of_ne_bot_of_ne_top (hbot w) hwtop
  rw [hγ, EReal.coe_le_coe_iff]
  by_cases hloc : IsLocalMin φ w
  · -- Case 1: `w` is a local minimizer, so `0 ∈ ∂̂φ(w)`
    have hw0 := zero_mem_regularSubdiff_of_isLocalMin hloc hγ
    have h1 := le_of_mem_regularSubdiff_of_monotone hlsc hbot hmono hγ hw0 u
    have h2 := le_of_mem_regularSubdiff_of_monotone hlsc hbot hmono hγ hw0 x
    rw [hu, zero_apply, add_zero, EReal.coe_le_coe_iff] at h1
    rw [hx, zero_apply, add_zero, EReal.coe_le_coe_iff] at h2
    nlinarith
  · -- Case 2: `w` is not a local minimizer
    by_contra hT
    push Not at hT
    set T := θ * α + (1 - θ) * β with hTdef
    have hev : ∀ᶠ y in 𝓝 w, (T : EReal) < φ y :=
      hlsc w T (by change (T : EReal) < φ w; rw [hγ]; exact EReal.coe_lt_coe_iff.2 hT)
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.1 hev
    have hfreq : ∃ᶠ y in 𝓝 w, φ y < φ w := by
      rw [IsLocalMin, IsMinFilter, not_eventually] at hloc
      exact hloc.mono fun y hy ↦ lt_of_not_ge hy
    obtain ⟨s, hs1, hs2⟩ := (hfreq.and_eventually (ball_mem_nhds w hρ)).exists
    rw [hγ] at hs1
    obtain ⟨σ, hσ⟩ := exists_eq_coe_of_ne_bot_of_ne_top (hbot s) (ne_top_of_lt hs1)
    rw [hσ, EReal.coe_lt_coe_iff] at hs1
    have hsw : s ≠ w := fun h ↦ by rw [h, hγ, EReal.coe_eq_coe_iff] at hσ; linarith
    obtain ⟨c, hc, hcw, hmin⟩ := exists_isMinOn_approx_mean_value hsw hσ hγ fun y _ ↦ hlsc y
    obtain ⟨z, v, hz, hv, h1, -, -⟩ :=
      approx_mean_value hsw hσ (hlsc' s w) (fun y _ ↦ hbot y) hc hcw hmin
    have hcball : c ∈ ball w ρ := (convex_ball w ρ).segment_subset hs2 (mem_ball_self hρ) hc
    have hcT := hρsub hcball
    obtain ⟨y', hy'1, hy'2⟩ := EReal.lt_iff_exists_real_btwn.1 hcT
    rw [EReal.coe_lt_coe_iff] at hy'1
    have hnn : 0 ≤ (γ - σ) / ‖w - s‖ * ‖w - c‖ :=
      mul_nonneg (div_nonneg (by linarith) (norm_nonneg _)) (norm_nonneg _)
    -- along `zₖ`, `φ(zₖ) ≤ T + ε`
    have hle : ∀ᶠ k in atTop, φ (z k) ≤ ((y' : ℝ) : EReal) := by
      filter_upwards [h1 (y' - T) (by linarith)] with k hk
      obtain ⟨ρk, hρk, -⟩ := id (hv k)
      have e1 := le_of_mem_regularSubdiff_of_monotone hlsc hbot hmono hρk (hv k) u
      have e2 := le_of_mem_regularSubdiff_of_monotone hlsc hbot hmono hρk (hv k) x
      rw [hu, EReal.coe_le_coe_iff] at e1
      rw [hx, EReal.coe_le_coe_iff] at e2
      have hcomb : v k (w - z k) = θ * v k (u - z k) + (1 - θ) * v k (x - z k) := by
        rw [← smul_eq_mul, ← smul_eq_mul, ← map_smul, ← map_smul, ← map_add, hwdef]
        congr 1
        module
      rw [hρk, EReal.coe_le_coe_iff]
      nlinarith
    have := le_of_tendsto (tendsto_funNhds_iff.1 hz).2 hle
    exact absurd (lt_of_lt_of_le hy'2 this) (lt_irrefl _)

/-- Thm. 4.19 of [Mordukhovich 2018], second step: under the assumptions of
`le_convex_comb_of_zero_mem`, with `0 ∈ ∂̂φ(u)` replaced by `∂̂φ(u) ≠ ∅` (the book's
"we can always suppose that `0 ∈ ∂̂φ(uₖ)`", obtained by subtracting a linear function). -/
theorem le_convex_comb_of_mem_regularSubdiff (hlsc : LowerSemicontinuous φ)
    (hbot : ∀ x, φ x ≠ ⊥)
    (hmono : ∀ x₁ x₂, ∀ v₁ ∈ regularSubdiff φ x₁, ∀ v₂ ∈ regularSubdiff φ x₂,
      0 ≤ (v₁ - v₂) (x₁ - x₂))
    {u x : E} {α β θ : ℝ} (hu : φ u = α) (hx : φ x = β) {p : StrongDual ℝ E}
    (hp : p ∈ regularSubdiff φ u) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    φ (θ • u + (1 - θ) • x) ≤ ((θ * α + (1 - θ) * β : ℝ) : EReal) := by
  set ψ : E → EReal := fun y ↦ φ y + ((-p y : ℝ) : EReal) with hψdef
  have hder : ∀ y, HasFDerivAt (fun y ↦ -p y) (-p) y := fun y ↦ (-p).hasFDerivAt
  have hsub : ∀ y, ∀ v ∈ regularSubdiff ψ y, v + p ∈ regularSubdiff φ y := fun y v hv ↦ by
    have := (mem_regularSubdiff_add_iff (hder y)).1 hv
    rwa [sub_neg_eq_add] at this
  have hψlsc : LowerSemicontinuous ψ := fun y ↦ lowerSemicontinuousAt_add_coe (hlsc y)
    p.continuous.neg.continuousAt
  have hψbot : ∀ y, ψ y ≠ ⊥ := fun y ↦ EReal.add_ne_bot_iff.2 ⟨hbot y, EReal.coe_ne_bot _⟩
  have hψmono : ∀ x₁ x₂, ∀ v₁ ∈ regularSubdiff ψ x₁, ∀ v₂ ∈ regularSubdiff ψ x₂,
      0 ≤ (v₁ - v₂) (x₁ - x₂) := fun x₁ x₂ v₁ hv₁ v₂ hv₂ ↦ by
    have := hmono x₁ x₂ _ (hsub x₁ v₁ hv₁) _ (hsub x₂ v₂ hv₂)
    rwa [add_sub_add_right_eq_sub] at this
  have h0 : (0 : StrongDual ℝ E) ∈ regularSubdiff ψ u :=
    (mem_regularSubdiff_add_iff (hder u)).2 (by rwa [zero_sub, neg_neg])
  have hψu : ψ u = ((α - p u : ℝ) : EReal) := by
    simp only [hψdef, hu, ← EReal.coe_add]; ring_nf
  have hψx : ψ x = ((β - p x : ℝ) : EReal) := by
    simp only [hψdef, hx, ← EReal.coe_add]; ring_nf
  have h := le_convex_comb_of_zero_mem hψlsc hψbot hψmono hψu hψx h0 hθ0 hθ1
  have hφψ : φ (θ • u + (1 - θ) • x) =
      ψ (θ • u + (1 - θ) • x) + ((p (θ • u + (1 - θ) • x) : ℝ) : EReal) := by
    have := add_coe_add_coe_neg (φ (θ • u + (1 - θ) • x)) (-p (θ • u + (1 - θ) • x))
    rw [neg_neg] at this
    exact this.symm
  rw [hφψ]
  calc ψ (θ • u + (1 - θ) • x) + ((p (θ • u + (1 - θ) • x) : ℝ) : EReal)
      ≤ ((θ * (α - p u) + (1 - θ) * (β - p x) : ℝ) : EReal) +
          ((p (θ • u + (1 - θ) • x) : ℝ) : EReal) := add_le_add_left h _
    _ = ((θ * α + (1 - θ) * β : ℝ) : EReal) := by
        rw [← EReal.coe_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
        congr 1
        ring

/-- Thm. 4.19 of [Mordukhovich 2018], convexity inequality: if `φ` is l.s.c. with no value `⊥`
and `∂̂φ` is globally monotone, then `φ(θ u + (1 - θ) x) ≤ θ φ(u) + (1 - θ) φ(x)` for `u, x` in
`dom φ` and `0 < θ < 1`. The points `u` are approximated by points of `dom ∂̂φ`
(Exercise 2.25(iii)) and the inequality passes to the limit by lower semicontinuity. -/
theorem le_convex_comb_of_monotone (hlsc : LowerSemicontinuous φ) (hbot : ∀ x, φ x ≠ ⊥)
    (hmono : ∀ x₁ x₂, ∀ v₁ ∈ regularSubdiff φ x₁, ∀ v₂ ∈ regularSubdiff φ x₂,
      0 ≤ (v₁ - v₂) (x₁ - x₂))
    {u x : E} {α β θ : ℝ} (hu : φ u = α) (hx : φ x = β) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    φ (θ • u + (1 - θ) • x) ≤ ((θ * α + (1 - θ) * β : ℝ) : EReal) := by
  obtain ⟨uk, hukt, hφuk, huk⟩ := exists_seq_tendsto_regularSubdiff_nonempty hu
    (Eventually.of_forall fun y ↦ hlsc y)
  have hfin : ∀ k, ∃ a : ℝ, φ (uk k) = a := fun k ↦ exists_eq_coe_of_ne_bot_of_ne_top
    (hbot _) (ne_top_of_le_ne_top (by rw [hu]; exact EReal.coe_ne_top α) (huk k).1)
  choose a ha using hfin
  have hat : Tendsto a atTop (𝓝 α) := tendsto_of_eq_coe hu ha hφuk
  have hineq : ∀ k, φ (θ • uk k + (1 - θ) • x) ≤ ((θ * a k + (1 - θ) * β : ℝ) : EReal) :=
    fun k ↦ by
      obtain ⟨p, hp⟩ := (huk k).2
      exact le_convex_comb_of_mem_regularSubdiff hlsc hbot hmono (ha k) hx hp hθ0 hθ1
  by_contra hT
  push Not at hT
  obtain ⟨T', hT'1, hT'2⟩ := EReal.lt_iff_exists_real_btwn.1 hT
  rw [EReal.coe_lt_coe_iff] at hT'1
  have hwt : Tendsto (fun k ↦ θ • uk k + (1 - θ) • x) atTop (𝓝 (θ • u + (1 - θ) • x)) :=
    (hukt.const_smul θ).add tendsto_const_nhds
  have hct : Tendsto (fun k ↦ θ * a k + (1 - θ) * β) atTop (𝓝 (θ * α + (1 - θ) * β)) :=
    (hat.const_mul θ).add tendsto_const_nhds
  obtain ⟨k, hk1, hk2⟩ := ((hwt.eventually (hlsc _ _ hT'2)).and
    (hct.eventually (Iio_mem_nhds hT'1))).exists
  have := lt_of_lt_of_le hk1 (hineq k)
  rw [EReal.coe_lt_coe_iff] at this
  exact lt_irrefl _ (this.trans hk2)

/-- Thm. 4.19 of [Mordukhovich 2018] (subdifferential monotonicity and convexity for l.s.c.
functions), regular subgradients: if `φ` is l.s.c. with no value `⊥` and the regular
subdifferential mapping `∂̂φ` is globally monotone (4.27), then `φ` is convex (its epigraph is
convex). -/
theorem convex_epi_of_monotone_regularSubdiff (hlsc : LowerSemicontinuous φ)
    (hbot : ∀ x, φ x ≠ ⊥)
    (hmono : ∀ x₁ x₂, ∀ v₁ ∈ regularSubdiff φ x₁, ∀ v₂ ∈ regularSubdiff φ x₂,
      0 ≤ (v₁ - v₂) (x₁ - x₂)) :
    Convex ℝ (φ.Epi univ) := by
  rintro ⟨x₁, t₁⟩ ⟨-, h₁⟩ ⟨x₂, t₂⟩ ⟨-, h₂⟩ a b ha hb hab
  refine ⟨mem_univ _, ?_⟩
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  obtain ⟨α₁, hα₁⟩ := exists_eq_coe_of_ne_bot_of_ne_top (hbot x₁) (ereal_ne_top_of_le_coe h₁)
  obtain ⟨α₂, hα₂⟩ := exists_eq_coe_of_ne_bot_of_ne_top (hbot x₂) (ereal_ne_top_of_le_coe h₂)
  rw [hα₁, EReal.coe_le_coe_iff] at h₁
  rw [hα₂, EReal.coe_le_coe_iff] at h₂
  rcases ha.eq_or_lt with rfl | ha'
  · rw [zero_add] at hab
    subst hab
    simpa [hα₂] using h₂
  rcases hb.eq_or_lt with rfl | hb'
  · rw [add_zero] at hab
    subst hab
    simpa [hα₁] using h₁
  have hb1 : b = 1 - a := by linarith
  subst hb1
  refine (le_convex_comb_of_monotone hlsc hbot hmono hα₁ hα₂ ha' (by linarith)).trans
    (EReal.coe_le_coe_iff.2 ?_)
  nlinarith

/-- Thm. 4.19 of [Mordukhovich 2018], basic subgradients: if `φ` is l.s.c. with no value `⊥` and
the basic subdifferential mapping `∂φ` is globally monotone (4.27), then `φ` is convex. (By
`∂̂φ ⊆ ∂φ`, this reduces to `convex_epi_of_monotone_regularSubdiff`.) -/
theorem convex_epi_of_monotone_subdiff (hlsc : LowerSemicontinuous φ) (hbot : ∀ x, φ x ≠ ⊥)
    (hmono : ∀ x₁ x₂, ∀ v₁ ∈ subdiff φ x₁, ∀ v₂ ∈ subdiff φ x₂, 0 ≤ (v₁ - v₂) (x₁ - x₂)) :
    Convex ℝ (φ.Epi univ) :=
  convex_epi_of_monotone_regularSubdiff hlsc hbot fun x₁ x₂ v₁ hv₁ v₂ hv₂ ↦
    hmono x₁ x₂ v₁ (regularSubdiff_subset_subdiff hv₁) v₂ (regularSubdiff_subset_subdiff hv₂)

end Convexity

end VariationalAnalysis
