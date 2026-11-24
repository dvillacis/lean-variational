/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis.SecondOrder.CyclicMonotone

/-!
# Minty's theorem

A monotone mapping `T : E ⇉ E` on a finite-dimensional real inner product space is maximally
monotone iff `rge(I + T) = E` (Minty 1962). The "if" part is `IsMonotoneOp.isMaximalMonotoneOp`
(`SCD/Monotone`); here we prove the "only if" part, the step [Mordukhovich 2024, Lemma 1.95]
delegates to the extension result of Exercise 1.145(ii).

## Proof

We use the Fitzpatrick function
`F_T(x, x*) = sup_{(y, y*) ∈ gph T} ⟨x*, y⟩ + ⟨y*, x⟩ - ⟨y*, y⟩`
(Fitzpatrick 1988), which needs neither fixed-point theorems nor Fenchel duality. `F_T` is
convex and lower semicontinuous, `F_T ≤ ⟨x, x*⟩` exactly at the pairs monotonically related to
`gph T`, so for maximally monotone `T` we have `F_T ≥ ⟨x, x*⟩` everywhere, with equality on
`gph T`. The function `F_T + ‖x‖²/2 + ‖x*‖²/2` is coercive and attains its minimum at some
`(a, a*)`. Comparing with the points `(a, a*) + s((y, y*) - (a, a*))`, `(y, y*) ∈ gph T`,
`s ↓ 0`, gives `⟨y + a*, y* + a⟩ ≥ ‖a + a*‖²` on `gph T`; by maximality `(-a*, -a) ∈ gph T`, and
then `a* = -a`, i.e. `-a ∈ T a`. Translating `T` gives `u - x ∈ T x` for every `u`.

## Main results

* `IsMaximalMonotoneOp.exists_sub_mem`: Minty's theorem, `rge(I + T) = E`.
* `isMaximalMonotoneOp_iff`: `T` is maximally monotone iff monotone with `rge(I + T) = E`.
* `IsMaximalMonotoneOp.resolventMap_nonempty`: [Mordukhovich 2024, Lemma 1.95], the remaining
  implication: `dom(I + λT)⁻¹ = E` for `λ > 0`.
* `IsMaximalMonotoneOp.isSCDMapping`: [Gfrerer–Outrata 2022, Prop. 3.22] for maximally monotone
  mappings, without the extra hypothesis `rge(I + F) = E`. The local versions are in
  `SCD/LocalMonotone`.
-/

open Filter Topology Set Metric
open scoped InnerProductSpace Pointwise

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {T : E → Set E}

/-! ### The Fitzpatrick function -/

/-- The affine pieces `(x, x*) ↦ ⟨x*, y⟩ + ⟨y*, x⟩ - ⟨y*, y⟩` of the Fitzpatrick function,
indexed by `p = (y, y*)`. -/
def fitzPiece (p z : E × E) : ℝ :=
  ⟪z.2, p.1⟫_ℝ + ⟪p.2, z.1⟫_ℝ - ⟪p.2, p.1⟫_ℝ

/-- The Fitzpatrick function `F_T(z) = sup_{p ∈ gph T} fitzPiece p z`. -/
noncomputable def fitzpatrick (T : E → Set E) (z : E × E) : EReal :=
  ⨆ p : {p : E × E // p.2 ∈ T p.1}, (fitzPiece p.1 z : EReal)

/-- With `p = (y, y*)` and `z = (x, x*)`,
`fitzPiece p z = ⟨x, x*⟩ - ⟨x* - y*, x - y⟩`. -/
theorem fitzPiece_eq (p z : E × E) :
    fitzPiece p z = ⟪z.1, z.2⟫_ℝ - ⟪z.2 - p.2, z.1 - p.1⟫_ℝ := by
  simp only [fitzPiece, inner_sub_left, inner_sub_right]
  rw [real_inner_comm z.1 z.2, real_inner_comm p.1 z.2]
  ring

/-- On the diagonal, `fitzPiece z z = ⟨x, x*⟩` for `z = (x, x*)`. -/
theorem fitzPiece_self (z : E × E) : fitzPiece z z = ⟪z.1, z.2⟫_ℝ := by
  rw [fitzPiece_eq]; simp

/-- For monotone `T` and `p, z ∈ gph T` with `z = (x, x*)`, `fitzPiece p z ≤ ⟨x, x*⟩`. -/
theorem fitzPiece_le_of_mem (hT : IsMonotoneOp T) {p z : E × E} (hp : p.2 ∈ T p.1)
    (hz : z.2 ∈ T z.1) : fitzPiece p z ≤ ⟪z.1, z.2⟫_ℝ := by
  rw [fitzPiece_eq]; linarith [hT z.1 p.1 z.2 hz p.2 hp]

/-- `fitzPiece p` is affine along lines: for all real `s`,
`fitzPiece p (z + s(w - z)) = fitzPiece p z + s (fitzPiece p w - fitzPiece p z)`. -/
theorem fitzPiece_segment (p z w : E × E) (s : ℝ) :
    fitzPiece p (z + s • (w - z)) = fitzPiece p z + s * (fitzPiece p w - fitzPiece p z) := by
  simp only [fitzPiece, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
    Prod.snd_sub, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    inner_sub_left, inner_sub_right, RCLike.conj_to_real]
  ring

/-- Each affine piece with `p ∈ gph T` minorizes the Fitzpatrick function:
`fitzPiece p z ≤ F_T(z)`. -/
theorem fitzPiece_le_fitzpatrick {p : E × E} (hp : p.2 ∈ T p.1) (z : E × E) :
    (fitzPiece p z : EReal) ≤ fitzpatrick T z :=
  le_iSup (fun p' : {p : E × E // p.2 ∈ T p.1} ↦ (fitzPiece p'.1 z : EReal)) ⟨p, hp⟩

/-- For monotone `T`, `F_T(x, x*) ≤ ⟨x, x*⟩` on `gph T`. -/
theorem fitzpatrick_le_of_mem (hT : IsMonotoneOp T) {z : E × E} (hz : z.2 ∈ T z.1) :
    fitzpatrick T z ≤ (⟪z.1, z.2⟫_ℝ : EReal) :=
  iSup_le fun p ↦ EReal.coe_le_coe_iff.2 (fitzPiece_le_of_mem hT p.2 hz)

/-- For a maximally monotone `T`, `F_T(x, x*) ≥ ⟨x, x*⟩`. -/
theorem IsMaximalMonotoneOp.inner_le_fitzpatrick (hT : IsMaximalMonotoneOp T) (z : E × E) :
    (⟪z.1, z.2⟫_ℝ : EReal) ≤ fitzpatrick T z := by
  by_contra hlt
  push Not at hlt
  have hz : z.2 ∈ T z.1 := hT.2 z.1 z.2 fun x' y' hy' ↦ by
    have := (fitzPiece_le_fitzpatrick (p := (x', y')) hy' z).trans_lt hlt
    rw [EReal.coe_lt_coe_iff, fitzPiece_eq] at this
    linarith
  exact absurd (fitzPiece_le_fitzpatrick hz z) (by rw [fitzPiece_self]; exact not_le.2 hlt)

/-- The Fitzpatrick function `F_T` is lower semicontinuous, as a supremum of continuous
functions. -/
theorem lowerSemicontinuous_fitzpatrick : LowerSemicontinuous (fitzpatrick T) := by
  refine lowerSemicontinuous_iSup fun p ↦ ?_
  refine (continuous_coe_real_ereal.comp ?_).lowerSemicontinuous
  unfold fitzPiece
  fun_prop

/-! ### Coercivity -/

/-- For `a, β ≥ 0`, the bound `a²/2 - βa ≤ C` implies `a ≤ 2β + 2|C| + 2`. -/
theorem le_of_half_sq_sub_le {a β C : ℝ} (ha : 0 ≤ a) (hβ : 0 ≤ β) (h : a ^ 2 / 2 - β * a ≤ C) :
    a ≤ 2 * β + 2 * |C| + 2 := by
  by_contra hlt
  push Not at hlt
  have h1 : |C| + 1 < a / 2 - β := by linarith
  have h2 : 1 ≤ a := by linarith [abs_nonneg C]
  have h3 : a * (|C| + 1) ≤ a * (a / 2 - β) := mul_le_mul_of_nonneg_left h1.le ha
  have h4 : |C| + 1 ≤ a * (|C| + 1) := le_mul_of_one_le_left (by positivity) h2
  have h5 : a ^ 2 / 2 - β * a = a * (a / 2 - β) := by ring
  linarith [le_abs_self C]

/-- For real `a` and `β`, `-β²/2 ≤ a²/2 - βa`. -/
theorem neg_sq_le_half_sq_sub (a β : ℝ) : -(β ^ 2 / 2) ≤ a ^ 2 / 2 - β * a := by
  nlinarith [sq_nonneg (a - β)]

/-- The sublevel sets of `fitzPiece p₀ + ‖·‖²/2` are bounded. -/
theorem exists_norm_le_of_fitzPiece_add_le (p₀ : E × E) (M : ℝ) :
    ∃ R, ∀ z : E × E, fitzPiece p₀ z + (‖z.1‖ ^ 2 / 2 + ‖z.2‖ ^ 2 / 2) ≤ M → ‖z‖ ≤ R := by
  set β := ‖p₀.2‖
  set γ := ‖p₀.1‖
  set c := ⟪p₀.2, p₀.1⟫_ℝ
  refine ⟨max (2 * β + 2 * |M + c + γ ^ 2 / 2| + 2) (2 * γ + 2 * |M + c + β ^ 2 / 2| + 2),
    fun z hz ↦ ?_⟩
  have i1 : -(γ * ‖z.2‖) ≤ ⟪z.2, p₀.1⟫_ℝ := by
    have := abs_real_inner_le_norm z.2 p₀.1
    rw [abs_le] at this; nlinarith [this.1]
  have i2 : -(β * ‖z.1‖) ≤ ⟪p₀.2, z.1⟫_ℝ := by
    have := abs_real_inner_le_norm p₀.2 z.1
    rw [abs_le] at this; nlinarith [this.1]
  have hsum : ‖z.1‖ ^ 2 / 2 - β * ‖z.1‖ + (‖z.2‖ ^ 2 / 2 - γ * ‖z.2‖) ≤ M + c := by
    simp only [fitzPiece] at hz
    linarith
  have j1 := neg_sq_le_half_sq_sub ‖z.1‖ β
  have j2 := neg_sq_le_half_sq_sub ‖z.2‖ γ
  rw [norm_prod_le_iff]
  constructor
  · exact (le_of_half_sq_sub_le (norm_nonneg _) (norm_nonneg _) (by linarith)).trans
      (le_max_left _ _)
  · exact (le_of_half_sq_sub_le (norm_nonneg _) (norm_nonneg _) (by linarith)).trans
      (le_max_right _ _)

/-! ### Minty's theorem -/

/-- Expansion of the square: `‖a + s d‖² = ‖a‖² + 2s⟨a, d⟩ + s²‖d‖²`. -/
theorem norm_add_smul_sq (a d : E) (s : ℝ) :
    ‖a + s • d‖ ^ 2 = ‖a‖ ^ 2 + 2 * s * ⟪a, d⟫_ℝ + s ^ 2 * ‖d‖ ^ 2 := by
  rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

variable [FiniteDimensional ℝ E]

/-- Minty's theorem, normalized form: a maximally monotone `T` has a point with `-x ∈ T x`. -/
theorem IsMaximalMonotoneOp.exists_neg_mem (hT : IsMaximalMonotoneOp T) : ∃ x, -x ∈ T x := by
  -- the graph is nonempty
  obtain ⟨p₀, hp₀⟩ : ∃ p : E × E, p.2 ∈ T p.1 := by
    by_contra h
    push Not at h
    exact h (0, 0) (hT.2 0 0 fun x' y' hy' ↦ absurd hy' (h (x', y')))
  set F := fitzpatrick T
  set q : E × E → ℝ := fun z ↦ ‖z.1‖ ^ 2 / 2 + ‖z.2‖ ^ 2 / 2 with hq
  set h : E × E → EReal := fun z ↦ F z + (q z : EReal) with hh
  set M := fitzPiece p₀ p₀ + q p₀
  obtain ⟨R, hR⟩ := exists_norm_le_of_fitzPiece_add_le p₀ M
  have hlow : ∀ z, ((fitzPiece p₀ z + q z : ℝ) : EReal) ≤ h z := fun z ↦ by
    rw [EReal.coe_add]; exact add_le_add (fitzPiece_le_fitzpatrick hp₀ z) le_rfl
  have hp₀M : h p₀ ≤ M := by
    rw [EReal.coe_add]
    refine add_le_add ?_ le_rfl
    rw [fitzPiece_self]; exact fitzpatrick_le_of_mem hT.1 hp₀
  -- a minimizer of `h` on a closed ball is a global minimizer
  have hlsc : LowerSemicontinuous h := by
    refine lowerSemicontinuous_fitzpatrick.add' (continuous_coe_real_ereal.comp
      (by simp only [hq]; fun_prop)).lowerSemicontinuous fun z ↦ ?_
    exact EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
  have hp₀K : p₀ ∈ closedBall (0 : E × E) R := by
    rw [mem_closedBall, dist_zero_right]; exact hR p₀ le_rfl
  obtain ⟨z₀, -, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn ⟨p₀, hp₀K⟩
    (isCompact_closedBall _ _) (hlsc.lowerSemicontinuousOn _)
  have hglob : ∀ z, h z₀ ≤ h z := by
    intro z
    by_cases hz : z ∈ closedBall (0 : E × E) R
    · exact isMinOn_iff.1 hmin z hz
    · refine (isMinOn_iff.1 hmin p₀ hp₀K).trans (hp₀M.trans (le_trans ?_ (hlow z)))
      rw [EReal.coe_le_coe_iff]
      by_contra hlt
      push Not at hlt
      exact hz (by rw [mem_closedBall, dist_zero_right]; exact hR z hlt.le)
  -- `F z₀` is finite
  have hFtop : F z₀ ≠ ⊤ := fun htop ↦ by
    have := (hglob p₀).trans hp₀M
    simp only [hh, htop, EReal.top_add_coe, top_le_iff] at this
    exact EReal.coe_ne_top _ this
  have hFbot : F z₀ ≠ ⊥ := fun hbot ↦ by
    have : (fitzPiece p₀ z₀ : EReal) ≤ F z₀ := fitzPiece_le_fitzpatrick hp₀ z₀
    rw [hbot] at this
    exact absurd this (not_le.2 (EReal.bot_lt_coe _))
  set f₀ := (F z₀).toReal
  have hf₀ : F z₀ = f₀ := (EReal.coe_toReal hFtop hFbot).symm
  obtain ⟨a, a'⟩ := z₀
  -- the variational inequality at the minimizer
  have hvi : ∀ y y', y' ∈ T y →
      f₀ ≤ ⟪y, y'⟫_ℝ + ⟪a, y - a⟫_ℝ + ⟪a', y' - a'⟫_ℝ := by
    intro y y' hy
    set d : E × E := (y, y') - (a, a')
    have hseg : ∀ s : ℝ, 0 < s → s ≤ 1 →
        f₀ ≤ ⟪y, y'⟫_ℝ + ⟪a, y - a⟫_ℝ + ⟪a', y' - a'⟫_ℝ +
          s * ((‖y - a‖ ^ 2 + ‖y' - a'‖ ^ 2) / 2) := by
      intro s hs hs1
      have hFs : F ((a, a') + s • d) ≤ (((1 - s) * f₀ + s * ⟪y, y'⟫_ℝ : ℝ) : EReal) := by
        refine iSup_le fun p ↦ EReal.coe_le_coe_iff.2 ?_
        rw [fitzPiece_segment]
        have e1 : fitzPiece p.1 (a, a') ≤ f₀ := by
          rw [← EReal.coe_le_coe_iff, ← hf₀]; exact fitzPiece_le_fitzpatrick p.2 _
        have e2 : fitzPiece p.1 (y, y') ≤ ⟪y, y'⟫_ℝ := fitzPiece_le_of_mem hT.1 p.2 hy
        have := mul_le_mul_of_nonneg_left e1 (by linarith : (0 : ℝ) ≤ 1 - s)
        have := mul_le_mul_of_nonneg_left e2 hs.le
        nlinarith
      have hcmp := (hglob ((a, a') + s • d)).trans (add_le_add hFs le_rfl)
      simp only [hh, hf₀, ← EReal.coe_add, EReal.coe_le_coe_iff] at hcmp
      simp only [hq, d, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        Prod.fst_sub, Prod.snd_sub, norm_add_smul_sq] at hcmp
      have key : s * f₀ ≤ s * (⟪y, y'⟫_ℝ + ⟪a, y - a⟫_ℝ + ⟪a', y' - a'⟫_ℝ +
          s * ((‖y - a‖ ^ 2 + ‖y' - a'‖ ^ 2) / 2)) := by nlinarith
      exact le_of_mul_le_mul_left key hs
    by_contra hlt
    push Not at hlt
    set δ := f₀ - (⟪y, y'⟫_ℝ + ⟪a, y - a⟫_ℝ + ⟪a', y' - a'⟫_ℝ) with hδdef
    set Q := (‖y - a‖ ^ 2 + ‖y' - a'‖ ^ 2) / 2
    have hδ : 0 < δ := by simp only [δ]; linarith
    have hQ : 0 ≤ Q := by positivity
    set s := min 1 (δ / (2 * (Q + 1)))
    have hs : 0 < s := lt_min one_pos (by positivity)
    have hsQ : s * Q < δ := by
      calc s * Q ≤ δ / (2 * (Q + 1)) * Q := mul_le_mul_of_nonneg_right (min_le_right _ _) hQ
        _ < δ := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith
    have := hseg s hs (min_le_left _ _)
    linarith
  have hge : ⟪a, a'⟫_ℝ ≤ f₀ := by
    rw [← EReal.coe_le_coe_iff, ← hf₀]; exact hT.inner_le_fitzpatrick (a, a')
  have hstrong : ∀ y y', y' ∈ T y → ‖a + a'‖ ^ 2 ≤ ⟪y + a', y' + a⟫_ℝ := by
    intro y y' hy
    have h1 := hvi y y' hy
    rw [norm_add_sq_real]
    simp only [inner_add_left, inner_add_right, inner_sub_right, real_inner_self_eq_norm_sq]
      at h1 ⊢
    rw [real_inner_comm a' a, real_inner_comm y a] at *
    linarith
  -- maximality gives `(-a', -a) ∈ gph T`, and then `a' = -a`
  have hmem : -a ∈ T (-a') := hT.2 (-a') (-a) fun x' y' hy' ↦ by
    have := (sq_nonneg _).trans (hstrong x' y' hy')
    have e : ⟪-a - y', -a' - x'⟫_ℝ = ⟪x' + a', y' + a⟫_ℝ := by
      rw [show -a - y' = -(y' + a) by abel, show -a' - x' = -(x' + a') by abel, inner_neg_neg,
        real_inner_comm]
    rw [e]; exact this
  have h0 := hstrong (-a') (-a) hmem
  simp only [neg_add_cancel, inner_zero_left] at h0
  have ha' : a' = -a := by
    have : a + a' = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm h0 (sq_nonneg _))
      exact norm_eq_zero.1 this
    rw [← neg_add_cancel_left a a', this, add_zero]
  exact ⟨a, by rw [← neg_neg a, ← ha']; simpa [ha'] using hmem⟩

omit [FiniteDimensional ℝ E] in
/-- Translating the values preserves maximal monotonicity. -/
theorem IsMaximalMonotoneOp.sub_const (hT : IsMaximalMonotoneOp T) (u : E) :
    IsMaximalMonotoneOp fun x ↦ (fun y ↦ y - u) '' T x := by
  refine ⟨?_, fun x y hxy ↦ ⟨y + u, hT.2 x (y + u) fun x' y' hy' ↦ ?_, by simp⟩⟩
  · rintro x₁ x₂ _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩
    simpa using hT.1 x₁ x₂ y₁ hy₁ y₂ hy₂
  · have := hxy x' (y' - u) ⟨y', hy', rfl⟩
    rwa [show y - (y' - u) = y + u - y' by abel] at this

/-- **Minty's theorem**: a maximally monotone mapping on a finite-dimensional space satisfies
`rge(I + T) = E`. -/
theorem IsMaximalMonotoneOp.exists_sub_mem (hT : IsMaximalMonotoneOp T) (u : E) :
    ∃ x, u - x ∈ T x := by
  obtain ⟨x, y, hy, hxy⟩ := (hT.sub_const u).exists_neg_mem
  simp only at hxy
  have e : u - x = y := by rw [sub_eq_add_neg, ← hxy]; abel
  exact ⟨x, e ▸ hy⟩

/-- Minty's characterization: `T` is maximally monotone iff it is monotone and
`rge(I + T) = E`. -/
theorem isMaximalMonotoneOp_iff : IsMaximalMonotoneOp T ↔ IsMonotoneOp T ∧ ∀ u, ∃ x, u - x ∈ T x :=
  ⟨fun hT ↦ ⟨hT.1, hT.exists_sub_mem⟩, fun h ↦ h.1.isMaximalMonotoneOp h.2⟩

omit [FiniteDimensional ℝ E] in
/-- Positive multiples of maximally monotone mappings are maximally monotone. -/
theorem IsMaximalMonotoneOp.smul (hT : IsMaximalMonotoneOp T) {l : ℝ} (hl : 0 < l) :
    IsMaximalMonotoneOp fun x ↦ l • T x := by
  refine ⟨?_, fun x y hxy ↦ ?_⟩
  · rintro x₁ x₂ _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩
    rw [← smul_sub, real_inner_smul_left]
    exact mul_nonneg hl.le (hT.1 x₁ x₂ y₁ hy₁ y₂ hy₂)
  · refine ⟨l⁻¹ • y, hT.2 x _ fun x' y' hy' ↦ ?_, by simp [smul_smul, hl.ne']⟩
    have := hxy x' (l • y') ⟨y', hy', rfl⟩
    rw [show l⁻¹ • y - y' = l⁻¹ • (y - l • y') by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hl.ne', one_smul], real_inner_smul_left]
    exact mul_nonneg (inv_nonneg.2 hl.le) this

/-- [Mordukhovich 2024, Lemma 1.95], the implication via Minty's theorem: for maximally monotone
`T` and `λ > 0`, `dom(I + λT)⁻¹ = E`. -/
theorem IsMaximalMonotoneOp.resolventMap_nonempty (hT : IsMaximalMonotoneOp T) {l : ℝ}
    (hl : 0 < l) (u : E) : (resolventMap T l u).Nonempty := by
  obtain ⟨x, y, hy, hxy⟩ := (hT.smul hl).exists_sub_mem u
  simp only at hxy
  exact ⟨x, y, hy, by rw [hxy]; abel⟩

/-- [Mordukhovich 2024, Lemma 1.95]: a monotone `T` is maximally monotone iff
`dom(I + λT)⁻¹ = E`, for any `λ > 0`. -/
theorem isMaximalMonotoneOp_iff_resolventMap (hT : IsMonotoneOp T) {l : ℝ} (hl : 0 < l) :
    IsMaximalMonotoneOp T ↔ ∀ u, (resolventMap T l u).Nonempty :=
  ⟨fun h ↦ h.resolventMap_nonempty hl,
    fun h ↦ hT.isMaximalMonotoneOp_of_resolventMap hl fun u ↦ h u⟩

/-! ### Consequences for SCD mappings -/

/-- [Gfrerer–Outrata 2022, Prop. 3.22]: maximally monotone mappings are SCD. -/
theorem IsMaximalMonotoneOp.isSCDMapping (hT : IsMaximalMonotoneOp T) : IsSCDMapping T :=
  hT.1.isSCDMapping hT.exists_sub_mem

end VariationalAnalysis
