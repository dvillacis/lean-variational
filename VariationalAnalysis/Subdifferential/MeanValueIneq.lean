/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis.Subdifferential.MeanValue

/-!
# Mean value inequalities

The mean value inequalities of [Mordukhovich 2018, Cor. 4.14], consequences of the approximate
mean value theorem (Thm. 4.13, `approx_mean_value`).

## Main results

* `mean_value_ineq`: Cor. 4.14(i) of [Mordukhovich 2018] (mean value inequality (4.23) for
  l.s.c. functions finite at `a`, including the case `φ(b) = ∞`).
* `abs_sub_le_norm_mul_of_forall_norm_le`: Cor. 4.14(i), increment estimate (4.25).
* `exists_mem_subdiff_mean_value_of_lipschitz`, `abs_sub_le_norm_mul_of_lipschitz`:
  Cor. 4.14(ii) of [Mordukhovich 2018] (mean value inequality and increment estimate for
  Lipschitz functions with basic subgradients).

## Remarks on the book

* For `φ(b) = ∞` the book applies (4.23) to the functions `φₛ` equal to `φ` except
  `φₛ(b) = φ(a) + s`; this gives points `cₛ` depending on `s`. To obtain a single point `c`, as in
  the statement, `mean_value_ineq_of_eq_top` shows that the minimizers `cₛ = a + τₛ (b - a)` of
  Thm. 4.13 have `τₛ` nondecreasing in `s`, so `cₛ → c` with `φ(cₛ) → φ(c)`, and concludes by a
  diagonal argument.
* In the increment estimate of Cor. 4.14(ii) the supremum is over `c ∈ [a, b)`; the bound
  `f(a) - f(b) ≤ ‖b - a‖ M` is obtained by applying the mean value inequality to `[bθ, a]` with
  `bθ = a + θ (b - a)` and letting `θ ↑ 1`.
* `(4.25)` is stated with a bound `M` for the supremum: if `‖x*‖ ≤ M` for all regular subgradients
  at points of `[a, b] + ε 𝔹`, then `φ(b)` is finite and `|φ(b) - φ(a)| ≤ ‖b - a‖ M`.
-/

open Filter Topology Set Metric
open scoped NNReal

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section MeanValueIneq

variable [FiniteDimensional ℝ E] {φ : E → EReal} {a b : E} {α β : ℝ}

/-- The key estimate behind (4.25) of [Mordukhovich 2018, Cor. 4.14(i)]: if `‖x*‖ ≤ M` for all
regular subgradients `x* ∈ ∂̂φ(y)` at points `y ∈ [a, b] + ε 𝔹`, then `β - φ(a) ≤ ‖b - a‖ M` for
every real `β ≤ φ(b)`. -/
theorem sub_le_norm_mul_of_forall_norm_le (ha : φ a = α) (hb : (β : EReal) ≤ φ b)
    (hlsc : ∀ x ∈ segment ℝ a b, ∀ᶠ y in 𝓝 x, LowerSemicontinuousAt φ y)
    (hbot : ∀ x ∈ segment ℝ a b, φ x ≠ ⊥) {ε M : ℝ} (hε : 0 < ε)
    (hM : ∀ y ∈ cthickening ε (segment ℝ a b), ∀ v ∈ regularSubdiff φ y, ‖v‖ ≤ M) :
    β - α ≤ ‖b - a‖ * M := by
  rcases eq_or_ne a b with rfl | hab
  · rw [ha, EReal.coe_le_coe_iff] at hb
    simp only [sub_self, norm_zero, zero_mul]
    linarith
  obtain ⟨c, hc, -, -, x, v, hx, hv, -, h2⟩ := approx_mean_value_of_le hab ha hb hlsc hbot
  have hx1 := (tendsto_funNhds_iff.1 hx).1
  refine le_of_forall_pos_le_add fun η hη ↦ ?_
  obtain ⟨k, hk1, hk2⟩ := ((h2 η hη).and (hx1.eventually (ball_mem_nhds c hε))).exists
  have hmem : x k ∈ cthickening ε (segment ℝ a b) :=
    mem_cthickening_of_dist_le _ c ε _ hc (mem_ball.1 hk2).le
  have h3 := apply_le_norm_mul (v k) (b - a)
  have h4 : ‖v k‖ * ‖b - a‖ ≤ M * ‖b - a‖ :=
    mul_le_mul_of_nonneg_right (hM _ hmem _ (hv k)) (norm_nonneg _)
  linarith

/-- Cor. 4.14(i) of [Mordukhovich 2018], increment estimate (4.25): let `φ` be finite at `a`,
l.s.c. around `[a, b]` with no value `⊥` there. If `‖x*‖ ≤ M` for all `x* ∈ ∂̂φ(y)`,
`y ∈ [a, b] + ε 𝔹` (i.e. the supremum in (4.25) is at most `M`), then `φ(b)` is finite and
`|φ(b) - φ(a)| ≤ ‖b - a‖ M`. -/
theorem abs_sub_le_norm_mul_of_forall_norm_le (ha : φ a = α)
    (hlsc : ∀ x ∈ segment ℝ a b, ∀ᶠ y in 𝓝 x, LowerSemicontinuousAt φ y)
    (hbot : ∀ x ∈ segment ℝ a b, φ x ≠ ⊥) {ε M : ℝ} (hε : 0 < ε)
    (hM : ∀ y ∈ cthickening ε (segment ℝ a b), ∀ v ∈ regularSubdiff φ y, ‖v‖ ≤ M) :
    ∃ β : ℝ, φ b = β ∧ |β - α| ≤ ‖b - a‖ * M := by
  have htop : φ b ≠ ⊤ := fun h ↦ by
    have := sub_le_norm_mul_of_forall_norm_le (β := α + ‖b - a‖ * M + 1) ha
      (by rw [h]; exact le_top) hlsc hbot hε hM
    linarith
  obtain ⟨β, hβ⟩ := exists_eq_coe_of_ne_bot_of_ne_top (hbot b (right_mem_segment ℝ a b)) htop
  refine ⟨β, hβ, abs_le.2 ⟨?_, sub_le_norm_mul_of_forall_norm_le ha hβ.ge hlsc hbot hε hM⟩⟩
  rw [segment_symm] at hlsc hbot hM
  have := sub_le_norm_mul_of_forall_norm_le hβ ha.ge hlsc hbot hε hM
  rw [norm_sub_rev] at this
  linarith

omit [FiniteDimensional ℝ E] in
/-- Along the segment, the function `ϑ` of Thm. 4.13 is `φ(a + t (b - a)) - t (β - α)`. -/
theorem sub_coe_div_mul_norm_eq (hab : a ≠ b) {t : ℝ} (ht : 0 ≤ t) :
    (β - α) / ‖b - a‖ * ‖a + t • (b - a) - a‖ = (β - α) * t := by
  have hD : 0 < ‖b - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hab.symm)
  rw [norm_add_smul_sub_sub_left ht]
  field_simp

/-- Cor. 4.14(i) of [Mordukhovich 2018] when `φ(b) = ∞`: a diagonal argument over the modified
functions `φₛ` of the book's proof (`φₛ(b) = φ(a) + s`). The minimizers `cₛ = a + τₛ (b - a)`
given by Thm. 4.13 have `τₛ` nondecreasing in `s`, so they converge to some `c ∈ [a, b]` with
`φ(cₛ) → φ(c)`; this gives a single point `c` with `xₖ →φ c`, `x*ₖ ∈ ∂̂φ(xₖ)` and
`⟨x*ₖ, b - a⟩ → ∞`. -/
theorem mean_value_ineq_of_eq_top (hab : a ≠ b) (ha : φ a = α) (hb : φ b = ⊤)
    (hlsc : ∀ x ∈ segment ℝ a b, ∀ᶠ y in 𝓝 x, LowerSemicontinuousAt φ y)
    (hbot : ∀ x ∈ segment ℝ a b, φ x ≠ ⊥) :
    ∃ c ∈ segment ℝ a b, ∃ (x : ℕ → E) (v : ℕ → StrongDual ℝ E),
      Tendsto x atTop (funNhds φ c) ∧ (∀ k, v k ∈ regularSubdiff φ (x k)) ∧
      ∀ M : ℝ, ∀ᶠ k in atTop, M ≤ v k (b - a) := by
  set lam : ℕ → ℝ := fun s ↦ (s : ℝ) + 1 with hlam
  have H := fun s : ℕ ↦ approx_mean_value_of_le (β := α + lam s) hab ha
    (by rw [hb]; exact le_top) hlsc hbot
  choose c hc _hcb hmin x v hx hv _h1 h2 using H
  choose τ hτ hcτ using fun s ↦ mem_segment_iff_eq_add_smul.1 (hc s)
  -- the minimality of `cₛ` in terms of the parameter
  have hminτ : ∀ s, ∀ t ∈ Icc (0 : ℝ) 1,
      φ (c s) - ((lam s * τ s : ℝ) : EReal) ≤ φ (a + t • (b - a)) - ((lam s * t : ℝ) : EReal) := by
    intro s t ht
    have h := hmin s (add_smul_sub_mem_segment ht.1 ht.2)
    simp only [mem_ofPred_eq] at h
    rw [hcτ s, sub_coe_div_mul_norm_eq hab (hτ s).1, sub_coe_div_mul_norm_eq hab ht.1,
      add_sub_cancel_left, ← hcτ s] at h
    exact h
  -- `φ(cₛ)` is finite
  have hfin : ∀ s, ∃ γ : ℝ, φ (c s) = γ := fun s ↦ by
    have h := hminτ s 0 ⟨le_rfl, zero_le_one⟩
    rw [zero_smul, add_zero, ha, mul_zero, EReal.coe_zero, sub_zero] at h
    have h' : φ (c s) ≤ ((α + lam s * τ s : ℝ) : EReal) := by
      rw [EReal.coe_add]
      exact (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
        (Or.inl (EReal.coe_ne_top _))).1 h
    exact exists_eq_coe_of_ne_bot_of_ne_top (hbot _ (hc s)) (ereal_ne_top_of_le_coe h')
  choose γ hγ using hfin
  have hminγ : ∀ s, ∀ t ∈ Icc (0 : ℝ) 1, ∀ g : ℝ, φ (a + t • (b - a)) = g →
      γ s - lam s * τ s ≤ g - lam s * t := fun s t ht g hg ↦ by
    have h := hminτ s t ht
    rw [hγ s, hg, ← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff] at h
    exact h
  -- `τₛ` is nondecreasing
  have hmono : Monotone τ := by
    refine monotone_nat_of_le_succ fun s ↦ ?_
    have h1 := hminγ s (τ (s + 1)) (hτ (s + 1)) (γ (s + 1)) (by rw [← hcτ, hγ])
    have h2 := hminγ (s + 1) (τ s) (hτ s) (γ s) (by rw [← hcτ, hγ])
    simp only [hlam, Nat.cast_add, Nat.cast_one] at h1 h2
    nlinarith
  have hbdd : BddAbove (range τ) := ⟨1, by rintro _ ⟨s, rfl⟩; exact (hτ s).2⟩
  set τs := ⨆ s, τ s with hτs
  have hτt : Tendsto τ atTop (𝓝 τs) := tendsto_atTop_ciSup hmono hbdd
  have hτle : ∀ s, τ s ≤ τs := fun s ↦ le_ciSup hbdd s
  have hτs : τs ∈ Icc (0 : ℝ) 1 := ⟨(hτ 0).1.trans (hτle 0), ciSup_le fun s ↦ (hτ s).2⟩
  set cs := a + τs • (b - a) with hcs
  have hcsS : cs ∈ segment ℝ a b := add_smul_sub_mem_segment hτs.1 hτs.2
  have hct : Tendsto c atTop (𝓝 cs) := by
    have : Tendsto (fun s ↦ a + τ s • (b - a)) atTop (𝓝 cs) :=
      tendsto_const_nhds.add (hτt.smul_const _)
    exact this.congr fun s ↦ (hcτ s).symm
  -- `φ(cₛ) → φ(c)`
  have hφle : ∀ s, φ (c s) ≤ φ cs := fun s ↦ by
    by_cases htop : φ cs = ⊤
    · rw [htop]; exact le_top
    obtain ⟨g, hg⟩ := exists_eq_coe_of_ne_bot_of_ne_top (hbot cs hcsS) htop
    have h := hminγ s τs hτs g hg
    have h' : lam s * τ s ≤ lam s * τs :=
      mul_le_mul_of_nonneg_left (hτle s) (by simp only [hlam]; positivity)
    rw [hγ s, hg, EReal.coe_le_coe_iff]
    linarith
  have hφt : Tendsto (fun s ↦ φ (c s)) atTop (𝓝 (φ cs)) :=
    tendsto_order.2 ⟨fun y hy ↦ hct.eventually ((hlsc cs hcsS).self_of_nhds y hy),
      fun y hy ↦ Eventually.of_forall fun s ↦ lt_of_le_of_lt (hφle s) hy⟩
  -- diagonal selection
  have hsel : ∀ s : ℕ, ∃ k, ‖x s k - c s‖ < 1 / ((s : ℝ) + 1) ∧
      ((γ s - 1 / ((s : ℝ) + 1) : ℝ) : EReal) < φ (x s k) ∧
      φ (x s k) < ((γ s + 1 / ((s : ℝ) + 1) : ℝ) : EReal) ∧
      (s : ℝ) ≤ v s k (b - a) := fun s ↦ by
    obtain ⟨hx1, hx2⟩ := tendsto_funNhds_iff.1 (hx s)
    rw [hγ s] at hx2
    have hpos : (0 : ℝ) < 1 / ((s : ℝ) + 1) := Nat.one_div_pos_of_nat
    have e1 := hx1.eventually (ball_mem_nhds (c s) hpos)
    have e2 := hx2.eventually (Ioi_mem_nhds (EReal.coe_lt_coe_iff.2
      (show γ s - 1 / ((s : ℝ) + 1) < γ s by linarith)))
    have e3 := hx2.eventually (Iio_mem_nhds (EReal.coe_lt_coe_iff.2
      (show γ s < γ s + 1 / ((s : ℝ) + 1) by linarith)))
    obtain ⟨k, hk1, hk2, hk3, hk4⟩ := (e1.and (e2.and (e3.and (h2 s 1 one_pos)))).exists
    refine ⟨k, by rw [← dist_eq_norm]; exact hk1, hk2, hk3, ?_⟩
    simp only [hlam] at hk4
    linarith
  choose k hk1 hk2 hk3 hk4 using hsel
  have hinv : Tendsto (fun s : ℕ ↦ 1 / ((s : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨cs, hcsS, fun s ↦ x s (k s), fun s ↦ v s (k s), ?_, fun s ↦ hv s (k s), fun M ↦ ?_⟩
  · refine tendsto_funNhds_iff.2 ⟨?_, ?_⟩
    · have h1 : Tendsto (fun s ↦ x s (k s) - c s) atTop (𝓝 0) :=
        squeeze_zero_norm (fun s ↦ (hk1 s).le) hinv
      simpa using h1.add hct
    · have hγt : Tendsto (fun s ↦ ((γ s : ℝ) : EReal)) atTop (𝓝 (φ cs)) :=
        hφt.congr fun s ↦ hγ s
      have hadd : ∀ {e : ℕ → ℝ}, Tendsto e atTop (𝓝 0) →
          Tendsto (fun s ↦ ((γ s + e s : ℝ) : EReal)) atTop (𝓝 (φ cs)) := fun {e} he ↦ by
        have := (EReal.continuousAt_add (p := (φ cs, ((0 : ℝ) : EReal)))
          (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))).tendsto.comp
          (hγt.prodMk_nhds ((continuous_coe_real_ereal.tendsto 0).comp he))
        simpa [Function.comp_def, EReal.coe_add] using this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le
        (hadd (by simpa using hinv.neg)) (hadd hinv) (fun s ↦ (hk2 s).le) (fun s ↦ (hk3 s).le)
  · obtain ⟨N, hN⟩ := exists_nat_ge M
    filter_upwards [eventually_ge_atTop N] with s hs
    exact hN.trans ((Nat.cast_le.2 hs).trans (hk4 s))

/-- Cor. 4.14(i) of [Mordukhovich 2018] (mean value inequality): let `φ` be finite at `a`,
l.s.c. around `[a, b]` with no value `⊥` there. Then there are `c ∈ [a, b]`, `xₖ →φ c` and
`x*ₖ ∈ ∂̂φ(xₖ)` with `lim inf ⟨x*ₖ, b - a⟩ ≥ φ(b) - φ(a)` (4.23), including the case
`φ(b) = ∞`. The `lim inf` condition is stated as: `M ≤ ⟨x*ₖ, b - a⟩` eventually, for every real
`M < φ(b) - φ(a)`. -/
theorem mean_value_ineq (ha : φ a = α)
    (hlsc : ∀ x ∈ segment ℝ a b, ∀ᶠ y in 𝓝 x, LowerSemicontinuousAt φ y)
    (hbot : ∀ x ∈ segment ℝ a b, φ x ≠ ⊥) :
    ∃ c ∈ segment ℝ a b, ∃ (x : ℕ → E) (v : ℕ → StrongDual ℝ E),
      Tendsto x atTop (funNhds φ c) ∧ (∀ k, v k ∈ regularSubdiff φ (x k)) ∧
      ∀ M : ℝ, (M : EReal) < φ b - α → ∀ᶠ k in atTop, M ≤ v k (b - a) := by
  rcases eq_or_ne a b with rfl | hab
  · obtain ⟨x, hxt, hφx, hx⟩ := exists_seq_tendsto_regularSubdiff_nonempty ha
      (hlsc a (left_mem_segment ℝ a a))
    choose v hv using fun k ↦ (hx k).2
    refine ⟨a, left_mem_segment ℝ a a, x, v, tendsto_funNhds_iff.2 ⟨hxt, hφx⟩, hv,
      fun M hM ↦ Eventually.of_forall fun k ↦ ?_⟩
    rw [ha, ← EReal.coe_sub, sub_self, EReal.coe_lt_coe_iff] at hM
    rw [sub_self, map_zero]
    exact hM.le
  by_cases htop : φ b = ⊤
  · obtain ⟨c, hc, x, v, hx, hv, h⟩ := mean_value_ineq_of_eq_top hab ha htop hlsc hbot
    exact ⟨c, hc, x, v, hx, hv, fun M _ ↦ h M⟩
  obtain ⟨β, hβ⟩ := exists_eq_coe_of_ne_bot_of_ne_top (hbot b (right_mem_segment ℝ a b)) htop
  obtain ⟨c, hc, -, -, x, v, hx, hv, -, h2⟩ := approx_mean_value_of_le hab ha hβ.ge hlsc hbot
  refine ⟨c, hc, x, v, hx, hv, fun M hM ↦ ?_⟩
  rw [hβ, ← EReal.coe_sub, EReal.coe_lt_coe_iff] at hM
  filter_upwards [h2 (β - α - M) (by linarith)] with k hk
  linarith

end MeanValueIneq

section Lipschitz

variable [FiniteDimensional ℝ E] {a b : E} {f : E → ℝ} {U : Set E} {L : ℝ≥0}

/-- A bounded sequence of regular subgradients `vₖ ∈ ∂̂φ(xₖ)` along `xₖ →φ c` has a subsequence
converging to a basic subgradient `w ∈ ∂φ(c)` (by (1.37)). -/
theorem exists_subseq_tendsto_mem_subdiff {φ : E → EReal} {c : E} {r : ℝ} (hr : φ c = r)
    {x : ℕ → E} {v : ℕ → StrongDual ℝ E} (hx : Tendsto x atTop (funNhds φ c))
    (hv : ∀ k, v k ∈ regularSubdiff φ (x k)) {M : ℝ} (hM : ∀ᶠ k in atTop, ‖v k‖ ≤ M) :
    ∃ w ∈ subdiff φ c, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (v ∘ ψ) atTop (𝓝 w) := by
  obtain ⟨w, -, ψ, hψ, hw⟩ := tendsto_subseq_of_frequently_bounded
    (isBounded_closedBall (x := (0 : StrongDual ℝ E)) (r := M))
    (hM.mono fun k hk ↦ mem_closedBall_zero_iff.2 hk).frequently
  refine ⟨w, ?_, ψ, hψ, hw⟩
  rw [subdiff_eq_outerLimit hr]
  exact ⟨x ∘ ψ, v ∘ ψ, hx.comp hψ.tendsto_atTop, hw, fun k ↦ hv (ψ k)⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A function Lipschitz on an open set `U` is l.s.c. around every point of `U`. -/
theorem eventually_lowerSemicontinuousAt_of_lipschitzOnWith (hU : IsOpen U)
    (hL : LipschitzOnWith L f U) {x : E} (hx : x ∈ U) :
    ∀ᶠ y in 𝓝 x, LowerSemicontinuousAt (fun z ↦ (f z : EReal)) y :=
  eventually_of_mem (hU.mem_nhds hx) fun _ hy ↦
    (continuous_coe_real_ereal.continuousAt.comp
      (hL.continuousOn.continuousAt (hU.mem_nhds hy))).lowerSemicontinuousAt

/-- Cor. 4.14(ii) of [Mordukhovich 2018] (mean value inequality for Lipschitz functions): if `f`
is Lipschitz on an open set `U ⊇ [a, b]`, then `⟨x*, b - a⟩ ≥ f(b) - f(a)` for some
`x* ∈ ∂f(c)`, `c ∈ [a, b)` (written `c = a + t (b - a)`, `0 ≤ t < 1`). -/
theorem exists_mem_subdiff_mean_value_of_lipschitz (hU : IsOpen U) (hsub : segment ℝ a b ⊆ U)
    (hL : LipschitzOnWith L f U) :
    ∃ t ∈ Ico (0 : ℝ) 1, ∃ v ∈ subdiff (fun x ↦ (f x : EReal)) (a + t • (b - a)),
      f b - f a ≤ v (b - a) := by
  rcases eq_or_ne a b with rfl | hab
  · obtain ⟨v, hv⟩ := subdiff_nonempty_of_lipschitz (hU.mem_nhds (hsub (left_mem_segment ℝ a a)))
      hL
    exact ⟨0, ⟨le_rfl, zero_lt_one⟩, v, by simpa using hv, by simp⟩
  have hlsc : ∀ x ∈ segment ℝ a b, ∀ᶠ y in 𝓝 x, LowerSemicontinuousAt (fun z ↦ (f z : EReal)) y :=
    fun x hx ↦ eventually_lowerSemicontinuousAt_of_lipschitzOnWith hU hL (hsub hx)
  obtain ⟨c, hc, hcb, hmin⟩ := exists_isMinOn_approx_mean_value (φ := fun z ↦ (f z : EReal)) hab
    rfl rfl fun x hx ↦ (hlsc x hx).self_of_nhds
  obtain ⟨x, v, hx, hv, -, h2, -⟩ := approx_mean_value hab rfl hlsc
    (fun x _ ↦ EReal.coe_ne_bot _) hc hcb hmin
  have hxc := (tendsto_funNhds_iff.1 hx).1
  have hM : ∀ᶠ k in atTop, ‖v k‖ ≤ L := by
    filter_upwards [hxc.eventually (hU.mem_nhds (hsub hc))] with k hk
    exact norm_le_of_mem_subdiff_of_lipschitz (hU.mem_nhds hk) hL
      (regularSubdiff_subset_subdiff (hv k))
  obtain ⟨w, hw, ψ, hψ, hwt⟩ := exists_subseq_tendsto_mem_subdiff
    (φ := fun z ↦ (f z : EReal)) (r := f c) rfl hx hv hM
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := mem_segment_iff_eq_add_smul.1 hc
  have ht1' : t < 1 := lt_of_le_of_ne ht1 fun h ↦ hcb (by rw [h, one_smul]; abel)
  refine ⟨t, ⟨ht0, ht1'⟩, w, hw, le_of_forall_pos_le_add fun ε hε ↦ ?_⟩
  have hlim : Tendsto (fun k ↦ (v ∘ ψ) k (b - a)) atTop (𝓝 (w (b - a))) :=
    tendsto_dual_apply hwt tendsto_const_nhds
  have := ge_of_tendsto hlim (hψ.tendsto_atTop.eventually (h2 ε hε))
  linarith

/-- Cor. 4.14(ii) of [Mordukhovich 2018], increment estimate: if `f` is Lipschitz on an open set
`U ⊇ [a, b]` and `‖x*‖ ≤ M` for all `x* ∈ ∂f(c)`, `c ∈ [a, b)`, then
`|f(b) - f(a)| ≤ ‖b - a‖ M`. -/
theorem abs_sub_le_norm_mul_of_lipschitz (hU : IsOpen U) (hsub : segment ℝ a b ⊆ U)
    (hL : LipschitzOnWith L f U) {M : ℝ}
    (hM : ∀ t ∈ Ico (0 : ℝ) 1, ∀ v ∈ subdiff (fun x ↦ (f x : EReal)) (a + t • (b - a)), ‖v‖ ≤ M) :
    |f b - f a| ≤ ‖b - a‖ * M := by
  refine abs_le.2 ⟨?_, ?_⟩
  · -- `f a - f b ≤ ‖b - a‖ M`, through the points `a + θ (b - a)`, `θ ↑ 1`
    have hkey : ∀ θ ∈ Ioo (0 : ℝ) 1, f a - f (a + θ • (b - a)) ≤ θ * (‖b - a‖ * M) := by
      intro θ hθ
      set bθ := a + θ • (b - a)
      have hbθ : bθ ∈ segment ℝ a b := add_smul_sub_mem_segment hθ.1.le hθ.2.le
      have hsub' : segment ℝ bθ a ⊆ U :=
        ((convex_segment a b).segment_subset hbθ (left_mem_segment ℝ a b)).trans hsub
      obtain ⟨s, ⟨hs0, hs1⟩, v, hv, hineq⟩ :=
        exists_mem_subdiff_mean_value_of_lipschitz hU hsub' hL
      have hpt : bθ + s • (a - bθ) = a + ((1 - s) * θ) • (b - a) := by
        simp only [bθ]; module
      rw [hpt] at hv
      have hnv := hM _ ⟨by nlinarith [hθ.1, hθ.2], by nlinarith [hθ.1, hθ.2]⟩ v hv
      have hv' : v (a - bθ) = θ * -v (b - a) := by
        rw [show a - bθ = (-θ) • (b - a) by simp only [bθ]; module, map_smul, smul_eq_mul]
        ring
      have h3 := apply_le_norm_mul v (-(b - a))
      rw [map_neg, norm_neg] at h3
      have h4 : ‖v‖ * ‖b - a‖ ≤ M * ‖b - a‖ := mul_le_mul_of_nonneg_right hnv (norm_nonneg _)
      have h5 : θ * -v (b - a) ≤ θ * (‖b - a‖ * M) :=
        mul_le_mul_of_nonneg_left (by linarith) hθ.1.le
      linarith
    have hbU : b ∈ U := hsub (right_mem_segment ℝ a b)
    have hT : Tendsto (fun θ : ℝ ↦ a + θ • (b - a)) (𝓝[<] 1) (𝓝 b) := by
      have : Tendsto (fun θ : ℝ ↦ a + θ • (b - a)) (𝓝 1) (𝓝 (a + (1 : ℝ) • (b - a))) :=
        (continuous_const.add (continuous_id.smul continuous_const)).tendsto 1
      rw [one_smul, add_sub_cancel] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hf : Tendsto (fun θ : ℝ ↦ f a - f (a + θ • (b - a))) (𝓝[<] 1) (𝓝 (f a - f b)) :=
      tendsto_const_nhds.sub ((hL.continuousOn.continuousAt (hU.mem_nhds hbU)).tendsto.comp hT)
    have hg : Tendsto (fun θ : ℝ ↦ θ * (‖b - a‖ * M)) (𝓝[<] 1) (𝓝 (1 * (‖b - a‖ * M))) :=
      ((continuous_id.mul continuous_const).tendsto 1).mono_left nhdsWithin_le_nhds
    have := le_of_tendsto_of_tendsto hf hg
      (eventually_of_mem (Ioo_mem_nhdsLT zero_lt_one) hkey)
    linarith
  · obtain ⟨t, ht, v, hv, hineq⟩ := exists_mem_subdiff_mean_value_of_lipschitz hU hsub hL
    have h3 := apply_le_norm_mul v (b - a)
    have h4 : ‖v‖ * ‖b - a‖ ≤ M * ‖b - a‖ :=
      mul_le_mul_of_nonneg_right (hM t ht v hv) (norm_nonneg _)
    linarith

end Lipschitz

end VariationalAnalysis
