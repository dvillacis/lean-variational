/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis.WellPosedness.Basic

/-!
# Monotone operators and single-valuedness of Lipschitz-like monotone operators

For an operator `T : E ⇉ E*` (values in `StrongDual ℝ E`, pairing `⟨v, x⟩ = v x`),
[Mordukhovich 2018] uses the following monotonicity notions:

* *local monotonicity* around `(x₀, v₀) ∈ gph T` (Subsection 3.3.3, Def. 5.10(i)): there are
  neighborhoods `U ∋ x₀`, `V ∋ v₀` with `⟨v₁ - v₂, x₁ - x₂⟩ ≥ 0` for all
  `(x₁, v₁), (x₂, v₂) ∈ gph T ∩ (U × V)`;
* *local hypomonotonicity* around `(x₀, v₀)` (Def. 5.1(iii)): the same with
  `⟨v₁ - v₂, x₁ - x₂⟩ ≥ -r ‖x₁ - x₂‖²` for some `r > 0`;
* *global monotonicity* (4.27) and *global maximal monotonicity* (p. 179).

The key fact of Subsection 3.3.3 is Prop. 3.24 (a specification of Kenderov's theorem): a locally
monotone operator which is Lipschitz-like around `(x₀, v₀)` is single-valued around this point.
The proof works verbatim for locally hypomonotone operators (which is what Lemma 3.28 needs) and
in every real normed space: the direction `z_k = (u_k - y_k)/‖u_k - y_k‖` of the book is replaced
by a vector `z` of norm `< 1` with `⟨u - y, z⟩ > ‖u - y‖ / 2`, which exists by definition of the
dual norm.

## Main declarations

* `LocallyMonotoneAt T x₀ v₀`, `LocallyHypomonotoneAt T x₀ v₀`, `GloballyMonotone T`,
  `GloballyMaximalMonotone T`: the monotonicity notions above.
* `SingleValuedAround S x₀ y₀`: `S` is single-valued around `(x₀, y₀)`: there are neighborhoods
  `U ∋ x₀`, `V ∋ y₀` such that `S x ∩ V` has at most one element for `x ∈ U`.

## Main results

* `LipschitzLikeWith.exists_lipschitzOnWith_of_locallyHypomonotoneAt`: Prop. 3.24 of
  [Mordukhovich 2018] (strong form, for hypomonotone operators): a locally hypomonotone operator
  which is Lipschitz-like around `(x₀, v₀) ∈ gph T` with modulus `ℓ` admits a single-valued
  localization `T x ∩ V = {g x}`, `x ∈ U`, with `g` Lipschitz on `U` with modulus `ℓ`
  (a Lipschitzian single-valued localization in the sense of Def. 5.11).
* `LipschitzLikeAt.singleValuedAround`: Prop. 3.24 of [Mordukhovich 2018].
* `not_lipschitzLikeAt_of_locallyMonotoneAt`: the reduced form of Thm. 3.25 of
  [Mordukhovich 2018]: a locally monotone field `Q` which is not single-valued around `(y₀, z₀)`
  is not Lipschitz-like around `(y₀, z₀)`. `not_lipschitzLikeAt_of_convex_values` is the version
  with the hypothesis of the book ("no neighborhood of `y₀` on which `Q` is single-valued") for
  fields with convex values.
* `globallyMonotone_subdiff_of_convex`: the subdifferential of a convex function is globally
  monotone [Mordukhovich 2018, p. 179].
* `globallyMaximalMonotone_iff`: elementwise characterization of global maximal monotonicity.

## Using these results for Thm. 3.25

Once Thm. 3.20 of [Mordukhovich 2018] is available in the form
`MetricallyRegularAt (pvsSolutionMap f Q) x₀ y₀ ↔ LipschitzLikeAt Q y₀ (-f (x₀, y₀))`, Thm. 3.25
is `fun h ↦ not_lipschitzLikeAt_of_locallyMonotoneAt hQ hsv (thm320.1 h)`.

Note that Thm. 3.25 needs the single-valuedness *around* `(y₀, z₀)`: with `Q y = {0, 1}` for all
`y ∈ ℝ` and `f (x, y) = x`, `Q` is locally monotone around `(0, 0)` and single-valued on no
neighborhood of `0`, yet `S x = {y | -x ∈ Q y}` is metrically regular around `(0, 0)` (and `Q` is
Lipschitz-like around `(0, 0)`). For convex-valued fields (e.g. convex subdifferentials) the two
readings agree (`not_lipschitzLikeAt_of_convex_values`).
-/

open Filter Topology Set Metric
open scoped NNReal

namespace VariationalAnalysis

section SingleValued

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

/-- `S` is single-valued around `(x₀, y₀)` [Mordukhovich 2018, Prop. 3.24]: there are
neighborhoods `U` of `x₀` and `V` of `y₀` such that `S x ∩ V` contains at most one point for
every `x ∈ U`. (Its negation, "`S` is multivalued in any neighborhood of `(x₀, y₀)`", is what the
proof of Prop. 3.24 argues against.) -/
def SingleValuedAround (S : α → Set β) (x₀ : α) (y₀ : β) : Prop :=
  ∃ U ∈ 𝓝 x₀, ∃ V ∈ 𝓝 y₀, ∀ x ∈ U, (S x ∩ V).Subsingleton

end SingleValued

section Definitions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Local monotonicity of `T : E ⇉ E*` around `(x₀, v₀)` [Mordukhovich 2018, Subsection 3.3.3,
Def. 5.10(i)]: there are neighborhoods `U` of `x₀` and `V` of `v₀` such that
`⟨v₁ - v₂, x₁ - x₂⟩ ≥ 0` for all `(x₁, v₁), (x₂, v₂) ∈ gph T ∩ (U × V)`. -/
def LocallyMonotoneAt (T : E → Set (StrongDual ℝ E)) (x₀ : E) (v₀ : StrongDual ℝ E) : Prop :=
  ∃ U ∈ 𝓝 x₀, ∃ V ∈ 𝓝 v₀, ∀ x₁ ∈ U, ∀ x₂ ∈ U, ∀ v₁ ∈ T x₁ ∩ V, ∀ v₂ ∈ T x₂ ∩ V,
    0 ≤ (v₁ - v₂) (x₁ - x₂)

/-- Local hypomonotonicity of `T : E ⇉ E*` around `(x₀, v₀)` [Mordukhovich 2018,
Def. 5.1(iii)]: there are neighborhoods `U` of `x₀`, `V` of `v₀` and `r > 0` such that
`⟨v₁ - v₂, x₁ - x₂⟩ ≥ -r ‖x₁ - x₂‖²` for all `(x₁, v₁), (x₂, v₂) ∈ gph T ∩ (U × V)` (5.1). -/
def LocallyHypomonotoneAt (T : E → Set (StrongDual ℝ E)) (x₀ : E) (v₀ : StrongDual ℝ E) :
    Prop :=
  ∃ r > (0 : ℝ), ∃ U ∈ 𝓝 x₀, ∃ V ∈ 𝓝 v₀, ∀ x₁ ∈ U, ∀ x₂ ∈ U, ∀ v₁ ∈ T x₁ ∩ V,
    ∀ v₂ ∈ T x₂ ∩ V, -(r * ‖x₁ - x₂‖ ^ 2) ≤ (v₁ - v₂) (x₁ - x₂)

/-- Global monotonicity of `T : E ⇉ E*` [Mordukhovich 2018, (4.27)]:
`⟨v₁ - v₂, x₁ - x₂⟩ ≥ 0` for all `(x₁, v₁), (x₂, v₂) ∈ gph T`. -/
def GloballyMonotone (T : E → Set (StrongDual ℝ E)) : Prop :=
  ∀ x₁ x₂, ∀ v₁ ∈ T x₁, ∀ v₂ ∈ T x₂, 0 ≤ (v₁ - v₂) (x₁ - x₂)

/-- Global maximal monotonicity of `T : E ⇉ E*` [Mordukhovich 2018, p. 179]: `T` is globally
monotone and `gph T = gph S` for every globally monotone `S` with `gph T ⊆ gph S`. -/
def GloballyMaximalMonotone (T : E → Set (StrongDual ℝ E)) : Prop :=
  GloballyMonotone T ∧ ∀ S : E → Set (StrongDual ℝ E), GloballyMonotone S → (∀ x, T x ⊆ S x) →
    S = T

variable {T : E → Set (StrongDual ℝ E)} {x₀ : E} {v₀ : StrongDual ℝ E}

/-- A globally monotone operator is locally monotone around every point. -/
theorem GloballyMonotone.locallyMonotoneAt (hT : GloballyMonotone T) :
    LocallyMonotoneAt T x₀ v₀ :=
  ⟨univ, univ_mem, univ, univ_mem, fun x₁ _ x₂ _ v₁ hv₁ v₂ hv₂ ↦ hT x₁ x₂ v₁ hv₁.1 v₂ hv₂.1⟩

/-- A locally monotone operator is locally hypomonotone (with `r = 1`, say). -/
theorem LocallyMonotoneAt.locallyHypomonotoneAt (hT : LocallyMonotoneAt T x₀ v₀) :
    LocallyHypomonotoneAt T x₀ v₀ := by
  obtain ⟨U, hU, V, hV, H⟩ := hT
  refine ⟨1, one_pos, U, hU, V, hV, fun x₁ hx₁ x₂ hx₂ v₁ hv₁ v₂ hv₂ ↦ ?_⟩
  have := H x₁ hx₁ x₂ hx₂ v₁ hv₁ v₂ hv₂
  nlinarith [sq_nonneg ‖x₁ - x₂‖]

/-- Elementwise characterization of global maximal monotonicity: `T` is globally monotone, and
every `(x, v)` which is monotonically related to all of `gph T` lies in `gph T`. -/
theorem globallyMaximalMonotone_iff :
    GloballyMaximalMonotone T ↔ GloballyMonotone T ∧
      ∀ x v, (∀ x', ∀ v' ∈ T x', 0 ≤ (v - v') (x - x')) → v ∈ T x := by
  constructor
  · rintro ⟨hT, hmax⟩
    refine ⟨hT, fun x v hv ↦ ?_⟩
    set S : E → Set (StrongDual ℝ E) := fun y ↦ {w | w ∈ T y ∨ (y = x ∧ w = v)}
    have hS : GloballyMonotone S := by
      rintro x₁ x₂ v₁ (hv₁ | ⟨rfl, rfl⟩) v₂ (hv₂ | ⟨rfl, rfl⟩)
      · exact hT x₁ x₂ v₁ hv₁ v₂ hv₂
      · have := hv x₁ v₁ hv₁
        rw [show (v₁ - v₂) (x₁ - x₂) = (v₂ - v₁) (x₂ - x₁) by simp; ring]
        exact this
      · exact hv x₂ v₂ hv₂
      · simp
    have := congrFun (hmax S hS fun y w hw ↦ Or.inl hw) x
    rw [← this]
    exact Or.inr ⟨rfl, rfl⟩
  · rintro ⟨hT, hmax⟩
    refine ⟨hT, fun S hS hTS ↦ funext fun y ↦ subset_antisymm (fun w hw ↦ ?_) (hTS y)⟩
    exact hmax y w fun x' v' hv' ↦ hS y x' w hw v' (hTS x' hv')

end Definitions

section Prop324

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {T : E → Set (StrongDual ℝ E)} {x₀ : E} {v₀ : StrongDual ℝ E} {ℓ : ℝ≥0}

/-- For a nonzero dual element `a` there is a vector `z` with `‖z‖ < 1` and `a z > ‖a‖ / 2`. -/
theorem StrongDual.exists_norm_lt_one_half_lt_apply {a : StrongDual ℝ E} (ha : a ≠ 0) :
    ∃ z : E, ‖z‖ < 1 ∧ ‖a‖ / 2 < a z := by
  have hpos : 0 < ‖a‖ := norm_pos_iff.2 ha
  obtain ⟨z, hz, hlt⟩ := a.exists_lt_apply_of_lt_opNorm (half_lt_self hpos)
  rw [Real.norm_eq_abs] at hlt
  rcases le_or_gt 0 (a z) with h | h
  · exact ⟨z, hz, by rwa [abs_of_nonneg h] at hlt⟩
  · refine ⟨-z, by rwa [norm_neg], ?_⟩
    rw [map_neg]
    rwa [abs_of_neg h] at hlt

/-- The core of the proof of Prop. 3.24 of [Mordukhovich 2018]: if `T` is locally hypomonotone
and Lipschitz-like around `(x₀, v₀)`, then there is `η > 0` such that `T x ∩ ball v₀ η` has at
most one element for every `x ∈ ball x₀ η`, and `ball x₀ (2η)`, `ball v₀ (2η)` lie in the
neighborhoods of the Lipschitz-like property. -/
theorem LipschitzLikeWith.exists_subsingleton_of_locallyHypomonotoneAt
    (hL : LipschitzLikeWith ℓ T x₀ v₀) (hT : LocallyHypomonotoneAt T x₀ v₀) :
    ∃ η > (0 : ℝ), (∀ x ∈ ball x₀ (2 * η), ∀ u ∈ ball x₀ (2 * η),
      ∀ y ∈ T x ∩ ball v₀ (2 * η), ∃ w ∈ T u, dist y w ≤ ℓ * dist x u) ∧
      ∀ x ∈ ball x₀ η, (T x ∩ ball v₀ η).Subsingleton := by
  obtain ⟨r, hr, U₁, hU₁, V₁, hV₁, Hm⟩ := hT
  obtain ⟨U₂, hU₂, V₂, hV₂, HL⟩ := hL
  obtain ⟨a₁, ha₁, hUa₁⟩ := Metric.mem_nhds_iff.1 (inter_mem hU₁ hU₂)
  obtain ⟨a₂, ha₂, hVa₂⟩ := Metric.mem_nhds_iff.1 (inter_mem hV₁ hV₂)
  set η := min a₁ a₂ / 2 with hη_def
  have hη : 0 < η := by positivity
  have hU : ball x₀ (2 * η) ⊆ U₁ ∩ U₂ :=
    (ball_subset_ball (by rw [hη_def]; linarith [min_le_left a₁ a₂])).trans hUa₁
  have hV : ball v₀ (2 * η) ⊆ V₁ ∩ V₂ :=
    (ball_subset_ball (by rw [hη_def]; linarith [min_le_right a₁ a₂])).trans hVa₂
  refine ⟨η, hη, fun x hx u hu y hy ↦ HL x (hU hx).2 u (hU hu).2 y ⟨hy.1, (hV hy.2).2⟩, ?_⟩
  intro x hx u hu y hy
  by_contra hne
  have hne' : u - y ≠ 0 := sub_ne_zero.2 hne
  set a := ‖u - y‖ with ha_def
  have ha : 0 < a := norm_pos_iff.2 hne'
  obtain ⟨z, hz, hza⟩ := StrongDual.exists_norm_lt_one_half_lt_apply hne'
  have hxη : dist x x₀ < η := hx
  have huη : dist u v₀ < η := hu.2
  have hyη : dist y v₀ < η := hy.2
  have ha2 : a < 2 * η := by
    have := dist_triangle_right u y v₀
    rw [dist_eq_norm] at this
    linarith
  have hℓ : (0 : ℝ) ≤ ℓ := ℓ.coe_nonneg
  set ν := a / (2 * (ℓ + r + 1)) with hν_def
  have hν : 0 < ν := by positivity
  have hνa : (ℓ + r) * ν < a / 2 := by
    rw [hν_def, mul_div_assoc', div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hνη : ν ≤ η := by
    rw [hν_def, div_le_iff₀ (by positivity)]
    nlinarith
  have hℓν : (ℓ : ℝ) * ν < η := by nlinarith
  -- the Lipschitz-like property at `x`, `x + ν z`
  have hx2 : x ∈ ball x₀ (2 * η) := ball_subset_ball (by linarith) hx
  have hxz : x + ν • z ∈ ball x₀ (2 * η) := by
    rw [mem_ball, dist_eq_norm, add_sub_right_comm]
    calc ‖x - x₀ + ν • z‖ ≤ ‖x - x₀‖ + ‖ν • z‖ := norm_add_le _ _
      _ < η + ν := by
          rw [norm_smul, Real.norm_of_nonneg hν.le, ← dist_eq_norm]
          exact add_lt_add hxη (mul_lt_of_lt_one_right hν hz)
      _ ≤ 2 * η := by linarith
  obtain ⟨w, hw, hyw⟩ := HL x (hU hx2).2 (x + ν • z) (hU hxz).2 y
    ⟨hy.1, (hV (ball_subset_ball (by linarith) hy.2)).2⟩
  have hxxz : dist x (x + ν • z) = ν * ‖z‖ := by
    rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg hν.le]
  rw [hxxz] at hyw
  have hyw' : ‖w - y‖ ≤ ℓ * ν := by
    rw [← dist_eq_norm, dist_comm]
    exact hyw.trans (mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hν.le hz.le) hℓ)
  have hwV : w ∈ ball v₀ (2 * η) := by
    rw [mem_ball]
    calc dist w v₀ ≤ dist w y + dist y v₀ := dist_triangle _ _ _
      _ < ℓ * ν + η := by rw [dist_eq_norm]; exact add_lt_add_of_le_of_lt hyw' hyη
      _ ≤ 2 * η := by linarith
  -- local hypomonotonicity at `(x + ν z, w)` and `(x, u)`
  have hmono := Hm (x + ν • z) (hU hxz).1 x (hU hx2).1 w ⟨hw, (hV hwV).1⟩ u
    ⟨hu.1, (hV (ball_subset_ball (by linarith) hu.2)).1⟩
  rw [add_sub_cancel_left, map_smul, smul_eq_mul, norm_smul, Real.norm_of_nonneg hν.le] at hmono
  have hz2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
  have h1 : -(r * ν) ≤ (w - u) z := by
    have h1' : ν * (-(r * ν)) ≤ ν * (w - u) z := by
      have : r * (ν * ‖z‖) ^ 2 ≤ r * ν ^ 2 := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (sq_nonneg ν) hz2) hr.le
      nlinarith
    exact le_of_mul_le_mul_left h1' hν
  have h2 : (w - y) z ≤ ℓ * ν := by
    calc (w - y) z ≤ ‖(w - y) z‖ := le_abs_self _
      _ ≤ ‖w - y‖ * ‖z‖ := (w - y).le_opNorm z
      _ ≤ ℓ * ν * 1 := by gcongr
      _ = ℓ * ν := mul_one _
  have h3 : (u - y) z = (w - y) z - (w - u) z := by simp
  rw [← ha_def] at hza
  nlinarith

/-- Prop. 3.24 of [Mordukhovich 2018] (single-valuedness of Lipschitz-like monotone operators),
strong form, for locally hypomonotone operators: if `T : E ⇉ E*` is locally hypomonotone and
Lipschitz-like with modulus `ℓ` around `(x₀, v₀) ∈ gph T`, then `T` admits a Lipschitzian
single-valued localization around `(x₀, v₀)` [Mordukhovich 2018, Def. 5.11]: there are a
neighborhood `U` of `x₀`, an open neighborhood `V` of `v₀` and a mapping `g`, Lipschitz on `U`
with modulus `ℓ`, with `T x ∩ V = {g x}` for all `x ∈ U`, and `g x₀ = v₀`. The book assumes local
monotonicity; its proof gives the hypomonotone case as well. -/
theorem LipschitzLikeWith.exists_lipschitzOnWith_of_locallyHypomonotoneAt
    (hL : LipschitzLikeWith ℓ T x₀ v₀) (hT : LocallyHypomonotoneAt T x₀ v₀) (h₀ : v₀ ∈ T x₀) :
    ∃ U ∈ 𝓝 x₀, ∃ V, IsOpen V ∧ v₀ ∈ V ∧ ∃ g : E → StrongDual ℝ E,
      (∀ x ∈ U, T x ∩ V = {g x}) ∧ LipschitzOnWith ℓ g U ∧ g x₀ = v₀ := by
  obtain ⟨η, hη, HL, Hsub⟩ := hL.exists_subsingleton_of_locallyHypomonotoneAt hT
  have hℓ : (0 : ℝ) ≤ ℓ := ℓ.coe_nonneg
  set ρ := η / (3 * ℓ + 1) with hρ_def
  have hρ : 0 < ρ := by positivity
  have hρη : ρ ≤ η := by
    rw [hρ_def, div_le_iff₀ (by positivity)]
    nlinarith
  have hℓρ : 3 * ℓ * ρ < η := by
    rw [hρ_def, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  have hx₀ : x₀ ∈ ball x₀ (2 * η) := mem_ball_self (by positivity)
  have hv₀ : v₀ ∈ T x₀ ∩ ball v₀ (2 * η) := ⟨h₀, mem_ball_self (by positivity)⟩
  -- existence of elements of `T x` near `v₀`
  have hex : ∀ x ∈ ball x₀ ρ, ∃ w ∈ T x, dist w v₀ ≤ ℓ * dist x x₀ := by
    intro x hx
    obtain ⟨w, hw, hdw⟩ := HL x₀ hx₀ x (ball_subset_ball (by linarith) hx) v₀ hv₀
    exact ⟨w, hw, by rw [dist_comm w, dist_comm x]; exact hdw⟩
  set g : E → StrongDual ℝ E := fun x ↦ Classical.epsilon fun w ↦ w ∈ T x ∩ ball v₀ η
  have hg : ∀ x ∈ ball x₀ ρ, g x ∈ T x ∩ ball v₀ η ∧ dist (g x) v₀ ≤ ℓ * dist x x₀ := by
    intro x hx
    obtain ⟨w, hw, hdw⟩ := hex x hx
    have hwV : w ∈ T x ∩ ball v₀ η := by
      refine ⟨hw, lt_of_le_of_lt hdw ?_⟩
      have : dist x x₀ < ρ := hx
      nlinarith
    have hgx : g x ∈ T x ∩ ball v₀ η := Classical.epsilon_spec ⟨w, hwV⟩
    have := Hsub x (ball_subset_ball hρη hx) hgx hwV
    exact ⟨hgx, this ▸ hdw⟩
  have hsing : ∀ x ∈ ball x₀ ρ, T x ∩ ball v₀ η = {g x} := fun x hx ↦
    (Hsub x (ball_subset_ball hρη hx)).eq_singleton_of_mem (hg x hx).1
  refine ⟨ball x₀ ρ, ball_mem_nhds _ hρ, ball v₀ η, isOpen_ball, mem_ball_self hη, g, hsing,
    LipschitzOnWith.of_dist_le_mul fun x hx u hu ↦ ?_, ?_⟩
  · obtain ⟨hgx, hgx₀⟩ := hg x hx
    have hxρ : dist x x₀ < ρ := hx
    have huρ : dist u x₀ < ρ := hu
    obtain ⟨w, hw, hdw⟩ := HL x (ball_subset_ball (by linarith) hx) u
      (ball_subset_ball (by linarith) hu) (g x) ⟨hgx.1, ball_subset_ball (by linarith) hgx.2⟩
    have hxu : dist x u < 2 * ρ := by
      calc dist x u ≤ dist x x₀ + dist u x₀ := dist_triangle_right _ _ _
        _ < 2 * ρ := by linarith
    have hwV : w ∈ T u ∩ ball v₀ η := by
      refine ⟨hw, ?_⟩
      rw [mem_ball]
      calc dist w v₀ ≤ dist w (g x) + dist (g x) v₀ := dist_triangle _ _ _
        _ ≤ ℓ * dist x u + ℓ * dist x x₀ := by rw [dist_comm]; exact add_le_add hdw hgx₀
        _ ≤ ℓ * (2 * ρ) + ℓ * ρ := by gcongr
        _ < η := by linarith
    have : w = g u := by
      rw [hsing u hu] at hwV
      exact hwV
    rw [← this]
    exact hdw
  · have := (hg x₀ (mem_ball_self hρ)).2
    rw [dist_self, mul_zero] at this
    exact dist_le_zero.1 this

/-- Prop. 3.24 of [Mordukhovich 2018] (single-valuedness of Lipschitz-like monotone operators):
if `T : E ⇉ E*` is locally monotone and Lipschitz-like around `(x₀, v₀)`, then `T` is
single-valued around `(x₀, v₀)`. (This part of the statement does not need `v₀ ∈ T x₀`.) -/
theorem LipschitzLikeAt.singleValuedAround (hL : LipschitzLikeAt T x₀ v₀)
    (hT : LocallyMonotoneAt T x₀ v₀) : SingleValuedAround T x₀ v₀ := by
  obtain ⟨ℓ, hℓ⟩ := hL
  obtain ⟨η, hη, -, Hsub⟩ :=
    hℓ.exists_subsingleton_of_locallyHypomonotoneAt hT.locallyHypomonotoneAt
  exact ⟨ball x₀ η, ball_mem_nhds _ hη, ball v₀ η, ball_mem_nhds _ hη, Hsub⟩

/-- Prop. 3.24 of [Mordukhovich 2018] for locally hypomonotone operators. -/
theorem LipschitzLikeAt.singleValuedAround_of_locallyHypomonotoneAt (hL : LipschitzLikeAt T x₀ v₀)
    (hT : LocallyHypomonotoneAt T x₀ v₀) : SingleValuedAround T x₀ v₀ := by
  obtain ⟨ℓ, hℓ⟩ := hL
  obtain ⟨η, hη, -, Hsub⟩ := hℓ.exists_subsingleton_of_locallyHypomonotoneAt hT
  exact ⟨ball x₀ η, ball_mem_nhds _ hη, ball v₀ η, ball_mem_nhds _ hη, Hsub⟩

/-- Reduced form of Thm. 3.25 of [Mordukhovich 2018] (failure of metric regularity for PVS with
monotone fields): a field `Q : F ⇉ F*` which is locally monotone around `(y₀, z₀)` and not
single-valued around this point is not Lipschitz-like around `(y₀, z₀)`. Combined with Thm. 3.20
(metric regularity of the solution map ⇔ Lipschitz-like property of the field) this is Thm. 3.25.
-/
theorem not_lipschitzLikeAt_of_locallyMonotoneAt {Q : E → Set (StrongDual ℝ E)} {y₀ : E}
    {z₀ : StrongDual ℝ E} (hQ : LocallyMonotoneAt Q y₀ z₀) (hsv : ¬ SingleValuedAround Q y₀ z₀) :
    ¬ LipschitzLikeAt Q y₀ z₀ :=
  fun hL ↦ hsv (hL.singleValuedAround hQ)

/-- A convex set whose intersection with a neighborhood of one of its points `a` is `{a}` is
`{a}`. -/
theorem eq_singleton_of_convex_of_inter_eq {C V : Set E} {a : E} (hC : Convex ℝ C)
    (hV : V ∈ 𝓝 a) (h : C ∩ V = {a}) : C = {a} := by
  have ha : a ∈ C := (h.symm ▸ mem_singleton a : a ∈ C ∩ V).1
  refine subset_antisymm (fun w hw ↦ ?_) (singleton_subset_iff.2 ha)
  have hT : Tendsto (fun t : ℝ ↦ a + t • (w - a)) (𝓝[>] 0) (𝓝 a) := by
    have : Tendsto (fun t : ℝ ↦ a + t • (w - a)) (𝓝 0) (𝓝 (a + (0 : ℝ) • (w - a))) :=
      tendsto_const_nhds.add (tendsto_id.smul_const _)
    rw [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨t, ⟨htV, ht1⟩, ht0⟩ :=
    (((hT.eventually hV).and (Ioo_mem_nhdsGT (zero_lt_one' ℝ))).and self_mem_nhdsWithin).exists
  have ht0 : (0 : ℝ) < t := ht0
  have hmem : a + t • (w - a) ∈ C ∩ V :=
    ⟨hC.add_smul_sub_mem ha hw ⟨ht0.le, ht1.2.le⟩, htV⟩
  rw [h, mem_singleton_iff, add_eq_left, smul_eq_zero] at hmem
  rcases hmem with h0 | h0
  · exact absurd h0 ht0.ne'
  · exact mem_singleton_iff.2 (sub_eq_zero.1 h0)

/-- Prop. 3.24 of [Mordukhovich 2018] for operators with convex values: a locally hypomonotone
operator with convex values near `x₀`, Lipschitz-like with modulus `ℓ` around `(x₀, v₀) ∈ gph T`,
is single-valued (`T x = {g x}`) on a neighborhood of `x₀`, with `g` Lipschitz with modulus `ℓ`
there. -/
theorem LipschitzLikeWith.exists_eq_singleton_of_convex
    (hL : LipschitzLikeWith ℓ T x₀ v₀) (hT : LocallyHypomonotoneAt T x₀ v₀) (h₀ : v₀ ∈ T x₀)
    (hconv : ∀ᶠ x in 𝓝 x₀, Convex ℝ (T x)) :
    ∃ U ∈ 𝓝 x₀, ∃ g : E → StrongDual ℝ E, (∀ x ∈ U, T x = {g x}) ∧ LipschitzOnWith ℓ g U ∧
      g x₀ = v₀ := by
  obtain ⟨U, hU, V, hVo, -, g, hg, hgL, hg₀⟩ :=
    hL.exists_lipschitzOnWith_of_locallyHypomonotoneAt hT h₀
  refine ⟨U ∩ {x | Convex ℝ (T x)}, inter_mem hU hconv, g, fun x hx ↦ ?_,
    hgL.mono inter_subset_left, hg₀⟩
  have hgx : g x ∈ V := ((hg x hx.1).symm ▸ mem_singleton (g x) : g x ∈ T x ∩ V).2
  exact eq_singleton_of_convex_of_inter_eq hx.2 (hVo.mem_nhds hgx) (hg x hx.1)

/-- Thm. 3.25 of [Mordukhovich 2018] in reduced form, with the book's hypothesis that there is no
neighborhood of `y₀` on which `Q` is single-valued, for fields with convex values (e.g.
subdifferentials of convex functions): such a locally monotone field is not Lipschitz-like around
`(y₀, z₀) ∈ gph Q`. -/
theorem not_lipschitzLikeAt_of_convex_values {Q : E → Set (StrongDual ℝ E)} {y₀ : E}
    {z₀ : StrongDual ℝ E} (hQ : LocallyMonotoneAt Q y₀ z₀) (h₀ : z₀ ∈ Q y₀)
    (hconv : ∀ᶠ y in 𝓝 y₀, Convex ℝ (Q y)) (hsv : ¬ ∃ U ∈ 𝓝 y₀, ∀ y ∈ U, ∃ z, Q y = {z}) :
    ¬ LipschitzLikeAt Q y₀ z₀ := by
  rintro ⟨ℓ, hL⟩
  obtain ⟨U, hU, g, hg, -⟩ :=
    hL.exists_eq_singleton_of_convex hQ.locallyHypomonotoneAt h₀ hconv
  exact hsv ⟨U, hU, fun y hy ↦ ⟨g y, hg y hy⟩⟩

end Prop324

section Convex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {φ : E → EReal}

/-- The subdifferential of a convex function is globally monotone [Mordukhovich 2018, p. 179]:
`⟨v₁ - v₂, x₁ - x₂⟩ ≥ 0` for `v₁ ∈ ∂φ(x₁)`, `v₂ ∈ ∂φ(x₂)`. -/
theorem globallyMonotone_subdiff_of_convex (hconv : Convex ℝ (φ.Epi univ)) :
    GloballyMonotone (subdiff φ) := by
  rintro x₁ x₂ v₁ ⟨r₁, hr₁, hv₁⟩ v₂ ⟨r₂, hr₂, hv₂⟩
  have h₁ := (mem_subdiff_of_convex hconv hr₁).1 ⟨r₁, hr₁, hv₁⟩ x₂
  have h₂ := (mem_subdiff_of_convex hconv hr₂).1 ⟨r₂, hr₂, hv₂⟩ x₁
  rw [hr₂, EReal.coe_le_coe_iff] at h₁
  rw [hr₁, EReal.coe_le_coe_iff] at h₂
  have : v₁ (x₂ - x₁) = -v₁ (x₁ - x₂) := by rw [← map_neg, neg_sub]
  simp only [sub_apply]
  linarith

/-- The subdifferential of a convex function has convex values. -/
theorem convex_subdiff_of_convex (hconv : Convex ℝ (φ.Epi univ)) (x₀ : E) :
    Convex ℝ (subdiff φ x₀) := by
  intro v₁ hv₁ v₂ hv₂ a b ha hb hab
  obtain ⟨r, hr, -⟩ := id hv₁
  rw [mem_subdiff_of_convex hconv hr] at hv₁ hv₂ ⊢
  intro x
  have h₁ := hv₁ x
  have h₂ := hv₂ x
  induction hφ : φ x with
  | bot => rw [hφ] at h₁; exact absurd (le_bot_iff.1 h₁) (EReal.coe_ne_bot _)
  | top => exact le_top
  | coe s =>
    rw [hφ, EReal.coe_le_coe_iff] at h₁ h₂
    rw [EReal.coe_le_coe_iff]
    simp only [add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    have h3 := add_le_add (mul_le_mul_of_nonneg_left h₁ ha) (mul_le_mul_of_nonneg_left h₂ hb)
    have hs : a * s + b * s = s := by rw [← add_mul, hab, one_mul]
    have hr' : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
    nlinarith

end Convex

end VariationalAnalysis
