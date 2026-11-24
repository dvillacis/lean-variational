/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Analysis.Normed.Module.HahnBanach
import VariationalAnalysis.Principle.AlmostStationary
import VariationalAnalysis.Subdifferential.SumRule

/-!
# Approximate mean value theorem

The approximate mean value theorem for lower semicontinuous functions
[Mordukhovich 2018, Thm. 4.13]: for `φ : E → EReal` l.s.c. around `[a, b]`, finite at `a ≠ b`,
and `c ∈ [a, b)` minimizing `ϑ(x) = φ(x) - (φ(b) - φ(a)) / ‖b - a‖ · ‖x - a‖` over `[a, b]`,
there are `xₖ →φ c` and `x*ₖ ∈ ∂̂φ(xₖ)` with

  `lim inf ⟨x*ₖ, b - xₖ⟩ ≥ (φ(b) - φ(a)) / ‖b - a‖ · ‖b - c‖`   (4.22),
  `lim inf ⟨x*ₖ, b - a⟩ ≥ φ(b) - φ(a)`   (4.23),

and `⟨x*ₖ, b - a⟩ → φ(b) - φ(a)` if `c ≠ a`. The `lim inf` conditions are written as "for every
`ε > 0`, eventually `… - ε ≤ …`".

## Main results

* `exists_isMinOn_approx_mean_value`: Thm. 4.13 of [Mordukhovich 2018], existence of `c ∈ [a, b)`.
* `approx_mean_value`: Thm. 4.13 of [Mordukhovich 2018], (4.22), (4.23) and the equality for
  `c ≠ a`.
* `approx_mean_value_of_le`: (4.22)–(4.23) with a real lower bound `β ≤ φ(b)` in place of
  `φ(b)` (the modified functions of the proof of Cor. 4.14(i)).
* Steps of the proof: `exists_subdiff_ekeland_step` (Ekeland's variational principle and
  Cor. 2.20), `approx_mean_value_estimates` (the projection estimates),
  `exists_approx_mean_value_step`, `exists_seq_approx_mean_value_of_isMinOn`.
* Auxiliary: `convexOn_infDist` (the distance function of a convex set is convex),
  `exists_cthickening_lsc_bdd` (l.s.c. functions are bounded below near compact sets),
  `lowerSemicontinuousAt_update`.

## Remarks on the book and on norms

* The statement does not depend on the norm: on `[a, b]`, `‖x - a‖ / ‖b - a‖` is the parameter
  `t` of `x = a + t (b - a)`, and `‖b - c‖ / ‖b - a‖ = 1 - t`. The proof works for any norm on the
  finite-dimensional space `E`: it only uses that `dist(·; [a, b])` is convex and `1`-Lipschitz,
  so no Euclidean structure is needed.
* The book applies the sum rule of Cor. 2.20 to `ϑₖ + k⁻¹ ‖· - xₖ‖` and then again to
  `φ + tₖ dist(·; [a, b])`, and uses `∂‖·‖(0) = 𝔹`. Here Cor. 2.20 is applied once, to `φ` and the
  convex Lipschitz function `gₖ = tₖ dist(·; [a, b]) + k⁻¹ ‖· - xₖ‖`, and the subgradient of `gₖ`
  is handled by convex analysis (`mem_subdiff_of_convex`); the projection estimates are those of
  the book.
* The book's functions take values in `(-∞, ∞]`; this is the hypothesis `φ x ≠ ⊥` on `[a, b]`.
* In `approx_mean_value` the value `β = φ(b)` only enters through the minimality of `c`, so `β`
  is an arbitrary real number there.
-/

open Filter Topology Set Metric
open scoped Pointwise NNReal

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Segment

/-- The points of `[a, b]` are the `a + t (b - a)`, `t ∈ [0, 1]`. -/
theorem mem_segment_iff_eq_add_smul {a b x : E} :
    x ∈ segment ℝ a b ↔ ∃ t ∈ Icc (0 : ℝ) 1, x = a + t • (b - a) := by
  rw [segment_eq_image']
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩

/-- `a + t (b - a) ∈ [a, b]` for `t ∈ [0, 1]`. -/
theorem add_smul_sub_mem_segment {a b : E} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    a + t • (b - a) ∈ segment ℝ a b :=
  mem_segment_iff_eq_add_smul.2 ⟨t, ⟨ht0, ht1⟩, rfl⟩

/-- The segment `[a, b]` is compact. -/
theorem isCompact_segment' (a b : E) : IsCompact (segment ℝ a b) := by
  rw [segment_eq_image']
  exact isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))

/-- `‖(a + t (b - a)) - a‖ = t ‖b - a‖` for `t ≥ 0`. -/
theorem norm_add_smul_sub_sub_left {a b : E} {t : ℝ} (ht : 0 ≤ t) :
    ‖a + t • (b - a) - a‖ = t * ‖b - a‖ := by
  rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht]

/-- `‖b - (a + t (b - a))‖ = (1 - t) ‖b - a‖` for `t ≤ 1`. -/
theorem norm_sub_add_smul_sub {a b : E} {t : ℝ} (ht : t ≤ 1) :
    ‖b - (a + t • (b - a))‖ = (1 - t) * ‖b - a‖ := by
  rw [show b - (a + t • (b - a)) = (1 - t) • (b - a) by rw [sub_smul, one_smul]; abel,
    norm_smul, Real.norm_of_nonneg (by linarith)]

/-- `(a + s (b - a)) - (a + t (b - a)) = (s - t) (b - a)`. -/
theorem add_smul_sub_sub_add_smul_sub {a b : E} {s t : ℝ} :
    a + s • (b - a) - (a + t • (b - a)) = (s - t) • (b - a) := by
  rw [sub_smul]; abel

end Segment

section Convexity

/-- The distance function of a convex set is convex. -/
theorem convexOn_infDist {S : Set E} (hS : Convex ℝ S) :
    ConvexOn ℝ univ (fun x ↦ infDist x S) := by
  refine ⟨convex_univ, fun x _ y _ θ μ hθ hμ hθμ ↦ ?_⟩
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨p, hp, hxp⟩ := (infDist_lt_iff hne).1 (lt_add_of_pos_right (infDist x S) hε)
  obtain ⟨q, hq, hyq⟩ := (infDist_lt_iff hne).1 (lt_add_of_pos_right (infDist y S) hε)
  have hmem : θ • p + μ • q ∈ S := hS hp hq hθ hμ hθμ
  have h1 : dist (θ • x + μ • y) (θ • p + μ • q) ≤ θ * dist x p + μ * dist y q := by
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm,
      show θ • x + μ • y - (θ • p + μ • q) = θ • (x - p) + μ • (y - q) by
        rw [smul_sub, smul_sub]; abel]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hθ, Real.norm_of_nonneg hμ]
  calc infDist (θ • x + μ • y) S ≤ dist (θ • x + μ • y) (θ • p + μ • q) :=
        infDist_le_dist_of_mem hmem
    _ ≤ θ * dist x p + μ * dist y q := h1
    _ ≤ θ * (infDist x S + ε) + μ * (infDist y S + ε) := by gcongr
    _ = θ • infDist x S + μ • infDist y S + ε := by
        simp only [smul_eq_mul]
        have : θ * ε + μ * ε = ε := by rw [← add_mul, hθμ, one_mul]
        linarith

/-- A real convex function has a convex epigraph in the sense of `Function.Epi`. -/
theorem convex_epi_coe_of_convexOn {g : E → ℝ} (hg : ConvexOn ℝ univ g) :
    Convex ℝ ((fun x ↦ (g x : EReal)).Epi univ) := by
  have h := hg.convex_epigraph
  convert h using 1
  ext p
  simp [Function.Epi, EReal.coe_le_coe_iff]

end Convexity

section EReal

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- `y - s + e = y + (e - s)` in `EReal` for real `s`, `e`. -/
theorem ereal_sub_coe_add_coe (y : EReal) (s e : ℝ) :
    y - (s : EReal) + (e : EReal) = y + ((e - s : ℝ) : EReal) := by
  induction y with
  | bot => simp
  | top => simp only [EReal.top_sub_coe, EReal.top_add_coe]
  | coe y =>
    rw [← EReal.coe_sub, ← EReal.coe_add, ← EReal.coe_add]
    congr 1; ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- An extended real bounded above by a real number is not `⊤`. -/
theorem ereal_ne_top_of_le_coe {y : EReal} {s : ℝ} (h : y ≤ (s : EReal)) : y ≠ ⊤ :=
  ne_top_of_le_ne_top (EReal.coe_ne_top s) h

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- An extended real that is neither `⊥` nor `⊤` is a real number. -/
theorem exists_eq_coe_of_ne_bot_of_ne_top {y : EReal} (hb : y ≠ ⊥) (ht : y ≠ ⊤) :
    ∃ s : ℝ, y = s :=
  ⟨y.toReal, (EReal.coe_toReal ht hb).symm⟩

end EReal

section Setup

variable [FiniteDimensional ℝ E]

/-- A function that is l.s.c. around every point of a compact set `K` and has no value `⊥` on `K`
is l.s.c. around, and bounded below on, a closed neighborhood `K + r 𝔹` of `K`. -/
theorem exists_cthickening_lsc_bdd {K : Set E} (hK : IsCompact K) {φ : E → EReal}
    (hlsc : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, LowerSemicontinuousAt φ y) (hbot : ∀ x ∈ K, φ x ≠ ⊥)
    (htop : ∃ x ∈ K, φ x ≠ ⊤) :
    ∃ r > 0, ∃ m : ℝ, ∀ y ∈ cthickening r K,
      (∀ᶠ z in 𝓝 y, LowerSemicontinuousAt φ z) ∧ (m : EReal) ≤ φ y := by
  set U := {y : E | ∀ᶠ z in 𝓝 y, LowerSemicontinuousAt φ z ∧ φ z ≠ ⊥}
  have hU : IsOpen U := isOpen_setOfPred_eventually_nhds
  have hKU : K ⊆ U := fun x hx ↦ by
    have h1 := hlsc x hx
    have h2 : ∀ᶠ z in 𝓝 x, ⊥ < φ z := h1.self_of_nhds ⊥ (bot_lt_iff_ne_bot.2 (hbot x hx))
    filter_upwards [h1, h2] with z hz1 hz2 using ⟨hz1, hz2.ne'⟩
  obtain ⟨r, hr, hsub⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨x₁, hx₁K, hx₁⟩ := htop
  have hK' : IsCompact (cthickening r K) := hK.cthickening
  have hlscOn : LowerSemicontinuousOn φ (cthickening r K) := fun y hy ↦
    ((hsub hy).self_of_nhds.1).lowerSemicontinuousWithinAt _
  obtain ⟨x₀, hx₀, hmin⟩ := hlscOn.exists_isMinOn
    ⟨x₁, self_subset_cthickening K hx₁K⟩ hK'
  have hx₀b : φ x₀ ≠ ⊥ := (hsub hx₀).self_of_nhds.2
  have hx₀t : φ x₀ ≠ ⊤ := ne_top_of_le_ne_top hx₁ (hmin (self_subset_cthickening K hx₁K))
  refine ⟨r, hr, (φ x₀).toReal, fun y hy ↦ ⟨(hsub hy).mono fun z hz ↦ hz.1, ?_⟩⟩
  rw [EReal.coe_toReal hx₀t hx₀b]
  exact hmin hy

end Setup

section Dual

/-- `⟨u, h⟩ ≤ ‖u‖ ‖h‖`. -/
theorem apply_le_norm_mul (u : StrongDual ℝ E) (h : E) : u h ≤ ‖u‖ * ‖h‖ :=
  (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact u.le_opNorm h)

/-- `-‖u‖ ‖h‖ ≤ ⟨u, h⟩`. -/
theorem neg_norm_mul_le_apply (u : StrongDual ℝ E) (h : E) : -(‖u‖ * ‖h‖) ≤ u h := by
  have := apply_le_norm_mul u (-h)
  rw [map_neg, norm_neg] at this
  linarith

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- If `θ ≥ κ / 2 > 0` and `-A ≤ θ X` with `A ≥ 0`, then `-(2 A / κ) ≤ X`. -/
theorem neg_div_le_of_le_mul {A θ κ X : ℝ} (hκ : 0 < κ) (hθ : κ / 2 ≤ θ) (hA : 0 ≤ A)
    (h : -A ≤ θ * X) : -(2 * A / κ) ≤ X := by
  have key : -(2 * A) ≤ κ * X := by
    rcases le_or_gt 0 X with hX | hX
    · nlinarith
    · nlinarith
  rw [show -(2 * A / κ) = -(2 * A) / κ by ring, div_le_iff₀ hκ]
  linarith

end Dual

section Core

/-- (1.37): a basic subgradient `u ∈ ∂ψ(z)` is approximated by regular subgradients `v ∈ ∂̂ψ(x)`
with `x` close to `z` and `ψ x` close to `ψ z`. -/
theorem exists_regularSubdiff_near_of_mem_subdiff {ψ : E → EReal} {z : E} {s : ℝ}
    {u : StrongDual ℝ E} (hs : ψ z = s) (hu : u ∈ subdiff ψ z) {η : ℝ} (hη : 0 < η) :
    ∃ x, ∃ v ∈ regularSubdiff ψ x, ‖x - z‖ < η ∧ ψ x < ((s + η : ℝ) : EReal) ∧ ‖v - u‖ < η := by
  rw [subdiff_eq_outerLimit hs] at hu
  obtain ⟨xs, us, hxs, hus, hmem⟩ := hu
  obtain ⟨hxs1, hxs2⟩ := tendsto_funNhds_iff.1 hxs
  have e1 : ∀ᶠ k in atTop, dist (xs k) z < η := hxs1.eventually (ball_mem_nhds z hη)
  have e2 : ∀ᶠ k in atTop, ψ (xs k) < ((s + η : ℝ) : EReal) := by
    rw [hs] at hxs2
    exact hxs2.eventually (Iio_mem_nhds (EReal.coe_lt_coe_iff.2 (by linarith)))
  have e3 : ∀ᶠ k in atTop, dist (us k) u < η := hus.eventually (ball_mem_nhds u hη)
  obtain ⟨k, hk1, hk2, hk3⟩ := (e1.and (e2.and e3)).exists
  rw [dist_eq_norm] at hk1 hk3
  exact ⟨xs k, us k, hmem k, hk1, hk2, hk3⟩

variable [FiniteDimensional ℝ E] {ψ : E → EReal} {a b c : E} {τ γ : ℝ}

/-- The variational step in the proof of Thm. 4.13 of [Mordukhovich 2018]. Let `c ∈ [a, b]`
minimize `ψ` over `[a, b]`, and let `ψ` be l.s.c. around and bounded below by `m` on
`[a, b] + r 𝔹`. For `0 < δ < r`, Ekeland's variational principle applied to
`ψ + δ_{[a, b] + r 𝔹} + t dist(·; [a, b])` (with `t` large) and the semi-Lipschitzian sum rule
(Cor. 2.20) give `z` with `‖z - c‖ ≤ δ`, `ψ z ≤ ψ c`, and `u ∈ ∂ψ(z)` such that `-u` is a
subgradient of the convex function `t dist(·; [a, b]) + δ ‖· - z‖` at `z`. -/
theorem exists_subdiff_ekeland_step (hcS : c ∈ segment ℝ a b) (hγ : ψ c = γ)
    (hmin : ∀ x ∈ segment ℝ a b, ψ c ≤ ψ x) {r m : ℝ} (hr : 0 < r)
    (hΩ : ∀ y ∈ cthickening r (segment ℝ a b),
      (∀ᶠ z in 𝓝 y, LowerSemicontinuousAt ψ z) ∧ (m : EReal) ≤ ψ y)
    {δ : ℝ} (hδ : 0 < δ) (hδr : δ < r) :
    ∃ z t, ∃ s : ℝ, ∃ u ∈ subdiff ψ z, ‖z - c‖ ≤ δ ∧ ψ z = s ∧ s ≤ γ ∧ 0 ≤ t ∧
      ∀ y, t * infDist z (segment ℝ a b) - u (y - z) ≤
        t * infDist y (segment ℝ a b) + δ * ‖y - z‖ := by
  classical
  set S := segment ℝ a b with hS
  have hSc : IsCompact S := isCompact_segment' a b
  have hSne : S.Nonempty := ⟨a, left_mem_segment ℝ a b⟩
  have hΩS : S ⊆ cthickening r S := self_subset_cthickening S
  -- Step 1: a radius `r'` on which `ψ > γ - δ²`.
  set ε := δ ^ 2 with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨r₁, hr₁, hr₁sub⟩ := hSc.exists_cthickening_subset_open
    (isOpen_setOfPred_eventually_nhds (p := fun z ↦ ((γ - ε : ℝ) : EReal) < ψ z))
    (fun x hx ↦ ((hΩ x (hΩS hx)).1.self_of_nhds) _
      (lt_of_lt_of_le (by rw [hγ]; exact EReal.coe_lt_coe_iff.2 (by linarith)) (hmin x hx)))
  set r' := min r₁ r with hr'def
  have hr' : 0 < r' := lt_min hr₁ hr
  have hr'sub : ∀ y, infDist y S ≤ r' → ((γ - ε : ℝ) : EReal) < ψ y := fun y hy ↦ by
    obtain ⟨p, hp, hyp⟩ := hSc.exists_infDist_eq_dist hSne y
    have : y ∈ cthickening r₁ S :=
      mem_cthickening_of_dist_le y p r₁ S hp (hyp ▸ hy.trans (min_le_left _ _))
    exact (hr₁sub this).self_of_nhds
  -- Step 2: the penalty coefficient `t`.
  set t := max 0 ((γ - ε - m) / r') with htdef
  have ht0 : 0 ≤ t := le_max_left _ _
  have htr : γ - ε - m ≤ t * r' := by
    have := le_max_right 0 ((γ - ε - m) / r')
    calc γ - ε - m = (γ - ε - m) / r' * r' := by field_simp
      _ ≤ t * r' := mul_le_mul_of_nonneg_right this hr'.le
  have hlow : ∀ y ∈ cthickening r S,
      ((γ - ε : ℝ) : EReal) ≤ ψ y + ((t * infDist y S : ℝ) : EReal) := by
    intro y hy
    by_cases hyd : infDist y S ≤ r'
    · exact le_trans (hr'sub y hyd).le
        (le_add_of_nonneg_right (EReal.coe_nonneg.2 (mul_nonneg ht0 infDist_nonneg)))
    · push Not at hyd
      have h1 : t * r' ≤ t * infDist y S := mul_le_mul_of_nonneg_left hyd.le ht0
      calc ((γ - ε : ℝ) : EReal) ≤ ((m + t * infDist y S : ℝ) : EReal) :=
            EReal.coe_le_coe_iff.2 (by linarith)
        _ = (m : EReal) + ((t * infDist y S : ℝ) : EReal) := EReal.coe_add _ _
        _ ≤ ψ y + _ := add_le_add_left (hΩ y hy).2 _
  -- Step 3: Ekeland's variational principle.
  set Ω := cthickening r S with hΩdef
  set ϑ : E → EReal := fun y ↦ if y ∈ Ω then ψ y + ((t * infDist y S : ℝ) : EReal) else ⊤
    with hϑ
  have hϑΩ : ∀ y ∈ Ω, ϑ y = ψ y + ((t * infDist y S : ℝ) : EReal) := fun y hy ↦ if_pos hy
  have hϑnΩ : ∀ y ∉ Ω, ϑ y = ⊤ := fun y hy ↦ if_neg hy
  have hcont : Continuous fun z ↦ ((t * infDist z S : ℝ) : EReal) :=
    continuous_coe_real_ereal.comp (continuous_const.mul (continuous_infDist_pt S))
  have hϑlsc : LowerSemicontinuous ϑ := by
    intro y
    by_cases hy : y ∈ Ω
    · have h1 : LowerSemicontinuousAt (fun z ↦ ψ z + ((t * infDist z S : ℝ) : EReal)) y :=
        ((hΩ y hy).1.self_of_nhds).add' hcont.continuousAt.lowerSemicontinuousAt
          (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _)))
      intro z hz
      rw [hϑΩ y hy] at hz
      filter_upwards [h1 z hz] with w hw
      by_cases hw' : w ∈ Ω
      · rw [hϑΩ w hw']; exact hw
      · rw [hϑnΩ w hw']; exact lt_of_lt_of_le hw le_top
    · intro z hz
      rw [hϑnΩ y hy] at hz
      filter_upwards [isClosed_cthickening.isOpen_compl.mem_nhds hy] with w hw
      rw [hϑnΩ w hw]
      exact hz
  have hbdd' : ∀ y, ((γ - ε : ℝ) : EReal) ≤ ϑ y := fun y ↦ by
    by_cases hy : y ∈ Ω
    · rw [hϑΩ y hy]; exact hlow y hy
    · rw [hϑnΩ y hy]; exact le_top
  have hϑc : ϑ c = γ := by
    rw [hϑΩ c (hΩS hcS), infDist_zero_of_mem hcS, mul_zero, EReal.coe_zero, add_zero, hγ]
  have hsub : ϑ c ≤ (⨅ y, ϑ y) + (ε : EReal) := by
    rw [hϑc]
    calc (γ : EReal) = ((γ - ε : ℝ) : EReal) + (ε : EReal) := by
          rw [← EReal.coe_add]; congr 1; ring
      _ ≤ (⨅ y, ϑ y) + (ε : EReal) := add_le_add_left (le_iInf hbdd') _
  obtain ⟨z, hzc, hzle, hz⟩ := ekeland_variational_principle hϑlsc ⟨γ - ε, hbdd'⟩ hεpos hδ
    (by rw [hϑc]; exact EReal.coe_ne_top γ) hsub
  have hεδ : ε / δ = δ := by rw [hε, sq, mul_div_assoc, div_self hδ.ne', mul_one]
  rw [hεδ] at hz
  have hzall := forall_le_add_norm_of_forall_ne hz
  -- Step 4: properties of the point `z`.
  have hzc' : dist z c ≤ δ := by rw [dist_eq_norm]; exact hzc
  have hdz : infDist z S ≤ δ := (infDist_le_dist_of_mem hcS).trans hzc'
  have hzΩ : z ∈ Ω := mem_cthickening_of_dist_le z c r S hcS (hzc'.trans hδr.le)
  set V := {y : E | infDist y S < r} with hVdef
  have hVo : IsOpen V := isOpen_lt (continuous_infDist_pt S) continuous_const
  have hzV : z ∈ V := lt_of_le_of_lt hdz hδr
  have hVΩ : V ⊆ Ω := fun y hy ↦ by
    obtain ⟨p, hp, hyp⟩ := (infDist_lt_iff hSne).1 hy
    exact mem_cthickening_of_dist_le y p r S hp hyp.le
  have hψz_le : ψ z ≤ ((γ - t * infDist z S : ℝ) : EReal) := by
    have := hzle
    rw [hϑc, hϑΩ z hzΩ] at this
    exact add_coe_le_coe_iff.1 this
  obtain ⟨s, hs⟩ := exists_eq_coe_of_ne_bot_of_ne_top
    (ne_bot_of_le_ne_bot (EReal.coe_ne_bot m) (hΩ z hzΩ).2) (ereal_ne_top_of_le_coe hψz_le)
  have hsγ : s ≤ γ := by
    rw [hs, EReal.coe_le_coe_iff] at hψz_le
    have : 0 ≤ t * infDist z S := mul_nonneg ht0 infDist_nonneg
    linarith
  -- Step 5: `z` minimizes `ψ + g` locally, `g = t dist(·; [a, b]) + δ ‖· - z‖`.
  set g : E → ℝ := fun y ↦ t * infDist y S + δ * dist y z with hgdef
  have hgconv : ConvexOn ℝ univ g := by
    have h1 : ConvexOn ℝ univ fun y ↦ t * infDist y S :=
      (convexOn_infDist (convex_segment a b)).smul ht0
    have h2 : ConvexOn ℝ univ fun y ↦ δ * dist y z := (convexOn_dist z convex_univ).smul hδ.le
    exact h1.add h2
  have hglip : LipschitzWith (Real.toNNReal (t + δ)) g := LipschitzWith.of_dist_le_mul fun x y ↦ by
    rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq]
    have h1 : |infDist x S - infDist y S| ≤ dist x y := by
      have := (lipschitz_infDist_pt S).dist_le_mul x y
      rwa [Real.dist_eq, NNReal.coe_one, one_mul] at this
    have h2 : |dist x z - dist y z| ≤ dist x y := abs_dist_sub_le x y z
    have h3 : |t * (infDist x S - infDist y S)| ≤ t * dist x y := by
      rw [abs_mul, abs_of_nonneg ht0]; exact mul_le_mul_of_nonneg_left h1 ht0
    have h4 : |δ * (dist x z - dist y z)| ≤ δ * dist x y := by
      rw [abs_mul, abs_of_nonneg hδ.le]; exact mul_le_mul_of_nonneg_left h2 hδ.le
    calc |g x - g y| = |t * (infDist x S - infDist y S) + δ * (dist x z - dist y z)| := by
          simp only [g]; ring_nf
      _ ≤ |t * (infDist x S - infDist y S)| + |δ * (dist x z - dist y z)| := abs_add_le _ _
      _ ≤ (t + δ) * dist x y := by linarith
  have hmin' : IsLocalMin (fun y ↦ ψ y + ((g y : ℝ) : EReal)) z := by
    filter_upwards [hVo.mem_nhds hzV] with y hy
    have h1 := hzall y
    rw [hϑΩ z hzΩ, hϑΩ y (hVΩ hy)] at h1
    simp only [g, dist_self, mul_zero, add_zero]
    rw [dist_eq_norm, EReal.coe_add, ← add_assoc]
    exact h1
  -- Step 6: Fermat rule and the semi-Lipschitzian sum rule (Cor. 2.20).
  have hloc : ∃ ρ > 0, IsClosed (ψ.Epi univ ∩ closedBall ((z, s) : E × ℝ) ρ) :=
    locallyClosed_epi_of_lowerSemicontinuousOn (U := {w | LowerSemicontinuousAt ψ w})
      (hΩ z hzΩ).1 (fun w hw ↦ hw.lowerSemicontinuousWithinAt _) s
  have h0 : (0 : StrongDual ℝ E) ∈ subdiff (fun y ↦ ψ y + g y) z :=
    zero_mem_subdiff_of_isLocalMin hmin' (r := s + g z) (by simp [hs])
  obtain ⟨u, hu, w, hw, huw⟩ :=
    subdiff_add_subset_of_lipschitz hs hloc univ_mem hglip.lipschitzOnWith h0
  have hwu : w = -u := eq_neg_of_add_eq_zero_right huw
  refine ⟨z, t, s, u, hu, hzc, hs, hsγ, ht0, fun y ↦ ?_⟩
  have := (mem_subdiff_of_convex (convex_epi_coe_of_convexOn hgconv) (r := g z) rfl).1 hw y
  rw [EReal.coe_le_coe_iff, hwu] at this
  simp only [g, dist_self, mul_zero, add_zero, neg_apply] at this
  rw [← dist_eq_norm]
  linarith

omit [FiniteDimensional ℝ E] in
/-- The estimates in the proof of Thm. 4.13 of [Mordukhovich 2018]: if `c = a + τ (b - a)`,
`‖z - c‖ ≤ δ` and `-u` is a subgradient of `t dist(·; [a, b]) + δ ‖· - z‖` at `z`, then
`⟨u, b - z⟩ ≥ -δ ‖b - z‖` and `⟨u, b - a⟩ ≥ -O(δ)`, and `⟨u, b - a⟩ ≤ O(δ)` if `τ > 0`. The proof
uses a projection `p` of `z` onto `[a, b]`, as in the book. -/
theorem approx_mean_value_estimates (hab : a ≠ b) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hc : c = a + τ • (b - a)) {z : E} {u : StrongDual ℝ E} {t δ κ : ℝ} (ht0 : 0 ≤ t)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hzc : ‖z - c‖ ≤ δ)
    (hH : ∀ y, t * infDist z (segment ℝ a b) - u (y - z) ≤
      t * infDist y (segment ℝ a b) + δ * ‖y - z‖)
    (hκ : 0 < κ) (hκτ : κ ≤ 1 - τ) (hκτ' : 0 < τ → κ ≤ τ) (hδκ : δ ≤ κ * ‖b - a‖ / 4) :
    -(δ * ‖b - z‖) ≤ u (b - z) ∧ -(2 * (δ * (‖b - a‖ + 2)) / κ) ≤ u (b - a) ∧
      (0 < τ → u (b - a) ≤ 2 * (δ * (‖b - a‖ + 2)) / κ) := by
  set S := segment ℝ a b with hS
  set D := ‖b - a‖ with hD
  have hDpos : 0 < D := norm_pos_iff.2 (sub_ne_zero.2 hab.symm)
  have hSc : IsCompact S := isCompact_segment' a b
  have hSne : S.Nonempty := ⟨a, left_mem_segment ℝ a b⟩
  have hcS : c ∈ S := hc ▸ add_smul_sub_mem_segment hτ0 hτ1.le
  set d := infDist z S with hddef
  have hdz : d ≤ δ := (infDist_le_dist_of_mem hcS).trans (by rw [dist_eq_norm]; exact hzc)
  have hd0 : 0 ≤ d := infDist_nonneg
  have htd : 0 ≤ t * d := mul_nonneg ht0 hd0
  obtain ⟨p, hpS, hdp⟩ := hSc.exists_infDist_eq_dist hSne z
  obtain ⟨σ, ⟨hσ0, hσ1⟩, rfl⟩ := mem_segment_iff_eq_add_smul.1 hpS
  set p := a + σ • (b - a) with hpdef
  have hdp' : d = ‖z - p‖ := by rw [← dist_eq_norm]; exact hdp
  have hup : u (p - z) ≤ t * d + δ * d := by
    have h := hH (z + (z - p))
    have hd' : infDist (z + (z - p)) S ≤ d + d := by
      have := infDist_le_infDist_add_dist (s := S) (x := z + (z - p)) (y := z)
      rwa [dist_eq_norm, add_sub_cancel_left, ← hdp'] at this
    rw [add_sub_cancel_left, ← hdp'] at h
    have e : u (p - z) = -u (z - p) := by rw [← map_neg, neg_sub]
    have h2 : t * infDist (z + (z - p)) S ≤ t * (d + d) := mul_le_mul_of_nonneg_left hd' ht0
    rw [e]
    linarith
  have hyS : ∀ y ∈ S, -(δ * ‖y - z‖) - δ * d ≤ u (y - p) := by
    intro y hy
    have h := hH y
    rw [infDist_zero_of_mem hy, mul_zero] at h
    have e : u (y - p) = u (y - z) - u (p - z) := by rw [← map_sub]; congr 1; abel
    rw [e]
    linarith
  have hub : -(δ * ‖b - z‖) ≤ u (b - z) := by
    have h := hH b
    rw [infDist_zero_of_mem (right_mem_segment ℝ a b), mul_zero] at h
    linarith
  refine ⟨hub, ?_⟩
  have hbc : ‖b - c‖ ≤ D := by
    rw [hc, norm_sub_add_smul_sub hτ1.le, sub_mul, one_mul]
    linarith [mul_nonneg hτ0 hDpos.le]
  have hac : ‖a - c‖ ≤ D := by
    rw [hc, show a - (a + τ • (b - a)) = -(τ • (b - a)) by abel, norm_neg, norm_smul,
      Real.norm_of_nonneg hτ0]
    nlinarith
  have hbz : ‖b - z‖ ≤ D + 1 := by
    have := norm_sub_le_norm_sub_add_norm_sub b c z
    rw [norm_sub_rev c z] at this; linarith
  have haz : ‖a - z‖ ≤ D + 1 := by
    have := norm_sub_le_norm_sub_add_norm_sub a c z
    rw [norm_sub_rev c z] at this; linarith
  have hστ : |σ - τ| * D ≤ 2 * δ := by
    have h1 : ‖p - c‖ = |σ - τ| * D := by
      rw [hc, hpdef, add_smul_sub_sub_add_smul_sub, norm_smul, Real.norm_eq_abs]
    have h2 := norm_sub_le_norm_sub_add_norm_sub p z c
    rw [norm_sub_rev p z, ← hdp', h1] at h2
    linarith
  have hσκ : |σ - τ| ≤ κ / 2 := by
    have : |σ - τ| * D ≤ κ / 2 * D := by linarith
    exact le_of_mul_le_mul_right this hDpos
  obtain ⟨hσκ1, hσκ2⟩ := abs_le.1 hσκ
  have hK : 0 ≤ δ * (D + 2) := by positivity
  have hδd : δ * d ≤ δ * 1 := mul_le_mul_of_nonneg_left (hdz.trans hδ1) hδ.le
  have hbp : u (b - p) = (1 - σ) * u (b - a) := by
    rw [hpdef, show b - (a + σ • (b - a)) = (1 - σ) • (b - a) by rw [sub_smul, one_smul]; abel,
      map_smul, smul_eq_mul]
  have hap : u (a - p) = σ * -u (b - a) := by
    rw [hpdef, show a - (a + σ • (b - a)) = (-σ) • (b - a) by rw [neg_smul]; abel,
      map_smul, smul_eq_mul]
    ring
  refine ⟨neg_div_le_of_le_mul hκ (θ := 1 - σ) (by linarith) hK ?_, fun hτ ↦ ?_⟩
  · have h1 := hyS b (right_mem_segment ℝ a b)
    have h2 : δ * ‖b - z‖ ≤ δ * (D + 1) := mul_le_mul_of_nonneg_left hbz hδ.le
    rw [hbp] at h1
    linarith
  · have hκτ'' := hκτ' hτ
    have h := neg_div_le_of_le_mul (X := -u (b - a)) hκ (θ := σ) (by linarith) hK (by
      have h1 := hyS a (left_mem_segment ℝ a b)
      have h2 : δ * ‖a - z‖ ≤ δ * (D + 1) := mul_le_mul_of_nonneg_left haz hδ.le
      rw [hap] at h1
      linarith)
    linarith

/-- One step of the proof of Thm. 4.13 of [Mordukhovich 2018]: under the assumptions of
`exists_subdiff_ekeland_step`, with `c = a + τ (b - a)`, `0 ≤ τ < 1`, for `δ > 0` small there are
`x` with `‖x - c‖ ≤ 2 δ`, `ψ x ≤ ψ c + δ`, and `v ∈ ∂̂ψ(x)` with `⟨v, b - x⟩ ≥ -O(δ)`,
`⟨v, b - a⟩ ≥ -O(δ)`, and `⟨v, b - a⟩ ≤ O(δ)` if `τ > 0`. -/
theorem exists_approx_mean_value_step (hab : a ≠ b) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hc : c = a + τ • (b - a)) (hγ : ψ c = γ) (hmin : ∀ x ∈ segment ℝ a b, ψ c ≤ ψ x)
    {r m : ℝ} (hr : 0 < r)
    (hΩ : ∀ y ∈ cthickening r (segment ℝ a b),
      (∀ᶠ z in 𝓝 y, LowerSemicontinuousAt ψ z) ∧ (m : EReal) ≤ ψ y)
    {κ δ : ℝ} (hκ : 0 < κ) (hκτ : κ ≤ 1 - τ) (hκτ' : 0 < τ → κ ≤ τ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδr : δ < r) (hδκ : δ ≤ κ * ‖b - a‖ / 4) :
    ∃ x v, v ∈ regularSubdiff ψ x ∧ ‖x - c‖ ≤ 2 * δ ∧ ψ x ≤ ((γ + δ : ℝ) : EReal) ∧
      -(δ * (2 * ‖b - a‖ + 4)) ≤ v (b - x) ∧
      -(δ * (2 * (‖b - a‖ + 2) / κ + ‖b - a‖)) ≤ v (b - a) ∧
      (0 < τ → v (b - a) ≤ δ * (2 * (‖b - a‖ + 2) / κ + ‖b - a‖)) := by
  have hcS : c ∈ segment ℝ a b := hc ▸ add_smul_sub_mem_segment hτ0 hτ1.le
  obtain ⟨z, t, s, u, hu, hzc, hs, hsγ, ht0, hH⟩ :=
    exists_subdiff_ekeland_step hcS hγ hmin hr hΩ hδ hδr
  obtain ⟨hub, hlowb, hupb⟩ :=
    approx_mean_value_estimates hab hτ0 hτ1 hc ht0 hδ hδ1 hzc hH hκ hκτ hκτ' hδκ
  set D := ‖b - a‖ with hD
  have hu0 := norm_nonneg u
  set δ' := δ / (1 + ‖u‖) with hδ'def
  have hδ' : 0 < δ' := by positivity
  have hδ'δ : δ' ≤ δ := div_le_self hδ.le (by linarith)
  have hδ'u : ‖u‖ * δ' ≤ δ := by
    rw [hδ'def, mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  obtain ⟨x, v, hv, hx1, hx2, hx3⟩ := exists_regularSubdiff_near_of_mem_subdiff hs hu hδ'
  have hvu : ∀ h : E, -(δ' * ‖h‖) ≤ (v - u) h ∧ (v - u) h ≤ δ' * ‖h‖ := fun h ↦ by
    have h1 := apply_le_norm_mul (v - u) h
    have h2 := neg_norm_mul_le_apply (v - u) h
    have h3 : ‖v - u‖ * ‖h‖ ≤ δ' * ‖h‖ := mul_le_mul_of_nonneg_right hx3.le (norm_nonneg h)
    constructor <;> linarith
  have hsplit : v (b - a) = u (b - a) + (v - u) (b - a) := by simp
  have h4 : δ' * ‖b - a‖ ≤ δ * D := mul_le_mul_of_nonneg_right hδ'δ (norm_nonneg _)
  have hK : 2 * (δ * (D + 2)) / κ = δ * (2 * (D + 2) / κ) := by ring
  refine ⟨x, v, hv, ?_, ?_, ?_, ?_, ?_⟩
  · have := norm_sub_le_norm_sub_add_norm_sub x z c
    linarith
  · exact (hx2.trans_le (EReal.coe_le_coe_iff.2 (by linarith))).le
  · have hdec : v (b - x) = u (b - z) + u (z - x) + (v - u) (b - x) := by
      simp only [sub_apply, map_sub]; ring
    have hzx : -δ ≤ u (z - x) := by
      have := neg_norm_mul_le_apply u (z - x)
      rw [norm_sub_rev] at this
      have h5 : ‖u‖ * ‖x - z‖ ≤ ‖u‖ * δ' := mul_le_mul_of_nonneg_left hx1.le hu0
      linarith
    have hbc : ‖b - c‖ ≤ D := by
      rw [hc, norm_sub_add_smul_sub hτ1.le, sub_mul, one_mul]
      linarith [mul_nonneg hτ0 (norm_nonneg (b - a))]
    have hbz : ‖b - z‖ ≤ D + 1 := by
      have := norm_sub_le_norm_sub_add_norm_sub b c z
      rw [norm_sub_rev c z] at this; linarith
    have hbx : ‖b - x‖ ≤ D + 2 := by
      have := norm_sub_le_norm_sub_add_norm_sub b z x
      rw [norm_sub_rev z x] at this; linarith
    have h3 := (hvu (b - x)).1
    have h6 : δ' * ‖b - x‖ ≤ δ * (D + 2) := mul_le_mul hδ'δ hbx (norm_nonneg _) hδ.le
    have h5 : δ * ‖b - z‖ ≤ δ * (D + 1) := mul_le_mul_of_nonneg_left hbz hδ.le
    rw [hdec]
    linarith
  · have h3 := (hvu (b - a)).1
    rw [hsplit]
    rw [hK] at hlowb
    linarith
  · intro hτ
    have h3 := (hvu (b - a)).2
    have h5 := hupb hτ
    rw [hK] at h5
    rw [hsplit]
    linarith

/-- Thm. 4.13 of [Mordukhovich 2018] in the normalized case of its proof: if `c = a + τ (b - a)`,
`0 ≤ τ < 1`, minimizes `ψ` over `[a, b]` (with `ψ c` finite), and `ψ` is l.s.c. around `[a, b]`
with no value `⊥` there, then there are `xₖ →ψ c` and `vₖ ∈ ∂̂ψ(xₖ)` with
`lim inf ⟨vₖ, b - xₖ⟩ ≥ 0`, `lim inf ⟨vₖ, b - a⟩ ≥ 0`, and `⟨vₖ, b - a⟩ → 0` if `c ≠ a`
(i.e. `τ > 0`). -/
theorem exists_seq_approx_mean_value_of_isMinOn (hab : a ≠ b) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hc : c = a + τ • (b - a)) (hγ : ψ c = γ) (hmin : ∀ x ∈ segment ℝ a b, ψ c ≤ ψ x)
    (hlsc : ∀ x ∈ segment ℝ a b, ∀ᶠ y in 𝓝 x, LowerSemicontinuousAt ψ y)
    (hbot : ∀ x ∈ segment ℝ a b, ψ x ≠ ⊥) :
    ∃ (x : ℕ → E) (v : ℕ → StrongDual ℝ E), Tendsto x atTop (funNhds ψ c) ∧
      (∀ k, v k ∈ regularSubdiff ψ (x k)) ∧
      (∀ ε > 0, ∀ᶠ k in atTop, -ε ≤ v k (b - x k)) ∧
      (∀ ε > 0, ∀ᶠ k in atTop, -ε ≤ v k (b - a)) ∧
      (0 < τ → Tendsto (fun k ↦ v k (b - a)) atTop (𝓝 0)) := by
  have hcS : c ∈ segment ℝ a b := hc ▸ add_smul_sub_mem_segment hτ0 hτ1.le
  obtain ⟨r, hr, m, hΩ⟩ := exists_cthickening_lsc_bdd (isCompact_segment' a b) hlsc hbot
    ⟨c, hcS, by rw [hγ]; exact EReal.coe_ne_top γ⟩
  set D := ‖b - a‖ with hD
  have hDpos : 0 < D := norm_pos_iff.2 (sub_ne_zero.2 hab.symm)
  set κ := if 0 < τ then min τ (1 - τ) else 1 - τ with hκdef
  have hκ : 0 < κ := by
    simp only [hκdef]; split_ifs with h
    · exact lt_min h (by linarith)
    · linarith
  have hκτ : κ ≤ 1 - τ := by
    simp only [hκdef]; split_ifs
    · exact min_le_right _ _
    · exact le_rfl
  have hκτ' : 0 < τ → κ ≤ τ := fun h ↦ by
    simp only [hκdef, if_pos h]; exact min_le_left _ _
  set δ₀ := min 1 (min (r / 2) (κ * D / 4)) with hδ₀def
  have hδ₀ : 0 < δ₀ := lt_min one_pos (lt_min (by linarith) (by positivity))
  set δ : ℕ → ℝ := fun k ↦ δ₀ / (k + 1) with hδdef
  have hδk : ∀ k, 0 < δ k ∧ δ k ≤ 1 ∧ δ k < r ∧ δ k ≤ κ * D / 4 := fun k ↦ by
    have h1 : δ k ≤ δ₀ := div_le_self hδ₀.le (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    have h2 : δ₀ ≤ 1 := min_le_left _ _
    have h3 : δ₀ ≤ r / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have h4 : δ₀ ≤ κ * D / 4 := (min_le_right _ _).trans (min_le_right _ _)
    exact ⟨by positivity, by linarith, by linarith, by linarith⟩
  have hδt : Tendsto δ atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ₀
    rw [mul_zero] at this
    refine this.congr fun k ↦ ?_
    change δ₀ * (1 / ((k : ℝ) + 1)) = δ₀ / ((k : ℝ) + 1)
    ring
  choose x v hv h1 h2 h3 h4 h5 using fun k ↦ exists_approx_mean_value_step hab hτ0 hτ1 hc hγ
    hmin hr hΩ hκ hκτ hκτ' (hδk k).1 (hδk k).2.1 (hδk k).2.2.1 (hδk k).2.2.2
  have hxt : Tendsto x atTop (𝓝 c) := by
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun k ↦ norm_nonneg _) h1 ?_)
    simpa using hδt.const_mul 2
  have hψt : Tendsto (fun k ↦ ψ (x k)) atTop (𝓝 (ψ c)) := by
    refine tendsto_order.2 ⟨fun y hy ↦ hxt.eventually ((hlsc c hcS).self_of_nhds y hy),
      fun y hy ↦ ?_⟩
    rw [hγ] at hy
    obtain ⟨y', hy1, hy2⟩ := EReal.lt_iff_exists_real_btwn.1 hy
    rw [EReal.coe_lt_coe_iff] at hy1
    filter_upwards [hδt.eventually (Iio_mem_nhds (sub_pos.2 hy1))] with k hk
    exact lt_of_le_of_lt (h2 k) (lt_trans (EReal.coe_lt_coe_iff.2 (by linarith)) hy2)
  have hbound : ∀ C : ℝ, ∀ ε > 0, ∀ᶠ k in atTop, δ k * C < ε := fun C ε hε ↦ by
    have := hδt.mul_const C
    rw [zero_mul] at this
    exact this.eventually (Iio_mem_nhds hε)
  refine ⟨x, v, tendsto_funNhds_iff.2 ⟨hxt, hψt⟩, hv, fun ε hε ↦ ?_, fun ε hε ↦ ?_, fun hτ ↦ ?_⟩
  · filter_upwards [hbound (2 * D + 4) ε hε] with k hk
    linarith [h3 k]
  · filter_upwards [hbound (2 * (D + 2) / κ + D) ε hε] with k hk
    linarith [h4 k]
  · set K := 2 * (D + 2) / κ + D
    have hl : Tendsto (fun k ↦ -(δ k * K)) atTop (𝓝 0) := by
      simpa using (hδt.mul_const K).neg
    have hu : Tendsto (fun k ↦ δ k * K) atTop (𝓝 0) := by simpa using hδt.mul_const K
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu (fun k ↦ h4 k) (fun k ↦ h5 k hτ)

end Core

section AMVT

variable [FiniteDimensional ℝ E] {φ : E → EReal} {a b c : E} {α β : ℝ}

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Adding a continuous real function preserves lower semicontinuity. -/
theorem lowerSemicontinuousAt_add_coe {h : E → ℝ} {x : E} (hφ : LowerSemicontinuousAt φ x)
    (hh : ContinuousAt h x) : LowerSemicontinuousAt (fun y ↦ φ y + ((h y : ℝ) : EReal)) x :=
  hφ.add' (continuous_coe_real_ereal.continuousAt.comp hh).lowerSemicontinuousAt
    (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _)))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- If `xₖ →ψ c` for `ψ = φ + h`, with `h` real and continuous, then `xₖ →φ c`. -/
theorem tendsto_funNhds_of_add_coe {h : E → ℝ} (hh : Continuous h) {x : ℕ → E}
    (hx : Tendsto x atTop (funNhds (fun y ↦ φ y + ((h y : ℝ) : EReal)) c)) :
    Tendsto x atTop (funNhds φ c) := by
  obtain ⟨hx1, hx2⟩ := tendsto_funNhds_iff.1 hx
  refine tendsto_funNhds_iff.2 ⟨hx1, ?_⟩
  have hc := ((EReal.continuousAt_add (p := (φ c + ((h c : ℝ) : EReal), ((-h c : ℝ) : EReal)))
    (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))).tendsto.comp
    (hx2.prodMk_nhds ((continuous_coe_real_ereal.tendsto _).comp
      ((hh.neg.tendsto c).comp hx1))))
  simp only [Function.comp_def, Pi.neg_apply, add_coe_add_coe_neg] at hc
  exact hc

omit [FiniteDimensional ℝ E] in
/-- Thm. 4.13 of [Mordukhovich 2018] (approximate mean value theorem for l.s.c. functions),
existence of the point `c`: if `φ` is l.s.c. at the points of `[a, b]` and finite at `a ≠ b`,
the function `ϑ(x) = φ(x) - (φ(b) - φ(a)) / ‖b - a‖ · ‖x - a‖` attains its minimum over `[a, b]`
at some `c ∈ [a, b)`. -/
theorem exists_isMinOn_approx_mean_value (hab : a ≠ b) (ha : φ a = α) (hb : φ b = β)
    (hlsc : ∀ x ∈ segment ℝ a b, LowerSemicontinuousAt φ x) :
    ∃ c ∈ segment ℝ a b, c ≠ b ∧
      IsMinOn (fun x ↦ φ x - (((β - α) / ‖b - a‖ * ‖x - a‖ : ℝ) : EReal)) (segment ℝ a b) c := by
  set ϑ := fun x ↦ φ x - (((β - α) / ‖b - a‖ * ‖x - a‖ : ℝ) : EReal) with hϑ
  have hDpos : 0 < ‖b - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hab.symm)
  have hϑ' : ϑ = fun x ↦ φ x + ((-((β - α) / ‖b - a‖ * ‖x - a‖) : ℝ) : EReal) := by
    funext x; simp only [hϑ, sub_eq_add_neg, EReal.coe_neg]
  have hlscOn : LowerSemicontinuousOn ϑ (segment ℝ a b) := fun x hx ↦ by
    rw [hϑ']
    exact (lowerSemicontinuousAt_add_coe (hlsc x hx) (by fun_prop)).lowerSemicontinuousWithinAt _
  obtain ⟨c₀, hc₀, hmin⟩ := hlscOn.exists_isMinOn ⟨a, left_mem_segment ℝ a b⟩
    (isCompact_segment' a b)
  by_cases hc₀b : c₀ = b
  · rw [hc₀b] at hmin
    refine ⟨a, left_mem_segment ℝ a b, hab, fun x hx ↦ ?_⟩
    have h1 : ϑ a = ϑ b := by
      simp only [hϑ, ha, hb, sub_self, norm_zero, mul_zero, EReal.coe_zero, sub_zero]
      rw [div_mul_cancel₀ _ hDpos.ne', ← EReal.coe_sub, sub_sub_cancel]
    rw [mem_ofPred_eq, h1]
    exact hmin hx
  · exact ⟨c₀, hc₀, hc₀b, hmin⟩

/-- Thm. 4.13 of [Mordukhovich 2018] (approximate mean value theorem for l.s.c. functions): let
`φ` be l.s.c. around `[a, b]` (with no value `⊥` there) and finite at `a ≠ b`, and let
`c ∈ [a, b)` minimize `ϑ(x) = φ(x) - (φ(b) - φ(a)) / ‖b - a‖ · ‖x - a‖` over `[a, b]`. Then there
are `xₖ →φ c` and `x*ₖ ∈ ∂̂φ(xₖ)` with

  `lim inf ⟨x*ₖ, b - xₖ⟩ ≥ (φ(b) - φ(a)) / ‖b - a‖ · ‖b - c‖`   (4.22),
  `lim inf ⟨x*ₖ, b - a⟩ ≥ φ(b) - φ(a)`   (4.23),

and `⟨x*ₖ, b - a⟩ → φ(b) - φ(a)` if `c ≠ a`. The `lim inf` conditions are stated in the form
"for every `ε > 0`, eventually". The proof follows the book: after subtracting a linear
function `ℓ` with `ℓ (b - a) = φ(b) - φ(a)`, Ekeland's variational principle is applied to
`φ + δ_Ω + tₖ dist(·; [a, b])`, and the sum rule Cor. 2.20 gives the subgradients. The
statement holds for any norm on `E`. The value `β = φ b` of the book only enters through the
minimality of `c`, so `β` is an arbitrary real number here (see
`exists_isMinOn_approx_mean_value` for the existence of `c` when `β = φ b`). -/
theorem approx_mean_value (hab : a ≠ b) (ha : φ a = α)
    (hlsc : ∀ x ∈ segment ℝ a b, ∀ᶠ y in 𝓝 x, LowerSemicontinuousAt φ y)
    (hbot : ∀ x ∈ segment ℝ a b, φ x ≠ ⊥) (hc : c ∈ segment ℝ a b) (hcb : c ≠ b)
    (hmin : IsMinOn (fun x ↦ φ x - (((β - α) / ‖b - a‖ * ‖x - a‖ : ℝ) : EReal))
      (segment ℝ a b) c) :
    ∃ (x : ℕ → E) (v : ℕ → StrongDual ℝ E), Tendsto x atTop (funNhds φ c) ∧
      (∀ k, v k ∈ regularSubdiff φ (x k)) ∧
      (∀ ε > 0, ∀ᶠ k in atTop, (β - α) / ‖b - a‖ * ‖b - c‖ - ε ≤ v k (b - x k)) ∧
      (∀ ε > 0, ∀ᶠ k in atTop, β - α - ε ≤ v k (b - a)) ∧
      (c ≠ a → Tendsto (fun k ↦ v k (b - a)) atTop (𝓝 (β - α))) := by
  obtain ⟨τ, ⟨hτ0, hτ1'⟩, rfl⟩ := mem_segment_iff_eq_add_smul.1 hc
  have hτ1 : τ < 1 := lt_of_le_of_ne hτ1' fun h ↦ hcb (by rw [h, one_smul]; abel)
  set c := a + τ • (b - a) with hcdef
  set D := ‖b - a‖ with hD
  have hDpos : 0 < D := norm_pos_iff.2 (sub_ne_zero.2 hab.symm)
  obtain ⟨g, -, hg⟩ := exists_dual_vector'' ℝ (b - a)
  replace hg : g (b - a) = D := by simpa using hg
  set ℓ : StrongDual ℝ E := ((β - α) / D) • g with hℓdef
  have hℓ : ℓ (b - a) = β - α := by
    simp only [hℓdef, smul_apply, smul_eq_mul, hg]
    field_simp
  set ψ : E → EReal := fun x ↦ φ x + ((-ℓ x : ℝ) : EReal) with hψdef
  have hψϑ : ∀ x ∈ segment ℝ a b, ψ x =
      φ x - (((β - α) / D * ‖x - a‖ : ℝ) : EReal) + ((-ℓ a : ℝ) : EReal) := by
    intro x hx
    obtain ⟨t, ⟨ht0, -⟩, rfl⟩ := mem_segment_iff_eq_add_smul.1 hx
    rw [ereal_sub_coe_add_coe, norm_add_smul_sub_sub_left ht0]
    simp only [hψdef]
    congr 2
    rw [map_add, map_smul, hℓ, smul_eq_mul, ← hD]
    field_simp
    ring
  have hmin' : ∀ x ∈ segment ℝ a b, ψ c ≤ ψ x := fun x hx ↦ by
    rw [hψϑ c hc, hψϑ x hx]
    exact add_le_add_left (hmin hx) _
  have hψa : ψ a = ((α - ℓ a : ℝ) : EReal) := by
    simp only [hψdef, ha, ← EReal.coe_add]; ring_nf
  have hψbot : ∀ x ∈ segment ℝ a b, ψ x ≠ ⊥ := fun x hx ↦
    EReal.add_ne_bot_iff.2 ⟨hbot x hx, EReal.coe_ne_bot _⟩
  obtain ⟨γ, hγ⟩ := exists_eq_coe_of_ne_bot_of_ne_top (hψbot c hc)
    (ereal_ne_top_of_le_coe ((hmin' a (left_mem_segment ℝ a b)).trans hψa.le))
  have hψlsc : ∀ x ∈ segment ℝ a b, ∀ᶠ y in 𝓝 x, LowerSemicontinuousAt ψ y := fun x hx ↦
    (hlsc x hx).mono fun y hy ↦ lowerSemicontinuousAt_add_coe hy (by fun_prop)
  obtain ⟨x, v, hx, hv, h1, h2, h3⟩ :=
    exists_seq_approx_mean_value_of_isMinOn hab hτ0 hτ1 rfl hγ hmin' hψlsc hψbot
  have hxc : Tendsto x atTop (𝓝 c) := (tendsto_funNhds_iff.1 hx).1
  have hder : ∀ y, HasFDerivAt (fun y ↦ -ℓ y) (-ℓ) y := fun y ↦ (-ℓ).hasFDerivAt
  refine ⟨x, fun k ↦ v k + ℓ, ?_, fun k ↦ ?_, fun ε hε ↦ ?_, fun ε hε ↦ ?_, fun hca ↦ ?_⟩
  · exact tendsto_funNhds_of_add_coe (h := fun y ↦ -ℓ y) (by fun_prop) hx
  · have := (mem_regularSubdiff_add_iff (hder (x k))).1 (hv k)
    rwa [sub_neg_eq_add] at this
  · have hbc : ℓ (b - c) = (β - α) / D * ‖b - c‖ := by
      rw [hcdef, norm_sub_add_smul_sub hτ1.le,
        show b - (a + τ • (b - a)) = (1 - τ) • (b - a) by rw [sub_smul, one_smul]; abel,
        map_smul, hℓ, smul_eq_mul, ← hD]
      field_simp
    have hlim : Tendsto (fun k ↦ ℓ (b - x k)) atTop (𝓝 (ℓ (b - c))) :=
      ((ℓ.continuous.tendsto _).comp (tendsto_const_nhds.sub hxc))
    filter_upwards [h1 (ε / 2) (half_pos hε),
      hlim.eventually (Ioi_mem_nhds (show ℓ (b - c) - ε / 2 < ℓ (b - c) by linarith))]
      with k hk1 hk2
    rw [add_apply]
    linarith
  · filter_upwards [h2 ε hε] with k hk
    rw [add_apply, hℓ]
    linarith
  · have hτ : 0 < τ := lt_of_le_of_ne hτ0 fun h ↦ hca (by rw [hcdef, ← h, zero_smul, add_zero])
    simpa [hℓ] using (h3 hτ).add_const (β - α)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
open scoped Classical in
/-- Lower semicontinuity is preserved by lowering the value at one point. -/
theorem lowerSemicontinuousAt_update {b y : E} {β : EReal} (hβ : β ≤ φ b)
    (hy : LowerSemicontinuousAt φ y) : LowerSemicontinuousAt (Function.update φ b β) y := by
  classical
  by_cases hyb : y = b
  · subst hyb
    intro z hz
    rw [Function.update_self] at hz
    filter_upwards [hy z (lt_of_lt_of_le hz hβ)] with w hw
    by_cases hwy : w = y
    · subst hwy; rw [Function.update_self]; exact hz
    · rwa [Function.update_of_ne hwy]
  · intro z hz
    rw [Function.update_of_ne hyb] at hz
    filter_upwards [hy z hz, isOpen_ne.mem_nhds hyb] with w hw hwb
    rwa [Function.update_of_ne hwb]

/-- The mean value inequalities (4.22)–(4.23) of Thm. 4.13 of [Mordukhovich 2018] with a real
lower bound `β ≤ φ b` in place of `φ b`, as in the proof of Cor. 4.14(i): applying Thm. 4.13 to
`φ` modified at `b` gives `c ∈ [a, b)`, minimizing
`ϑ(x) = φ(x) - (β - φ(a)) / ‖b - a‖ · ‖x - a‖` over `[a, b]`, and `xₖ →φ c`, `x*ₖ ∈ ∂̂φ(xₖ)` with
`lim inf ⟨x*ₖ, b - xₖ⟩ ≥ (β - φ(a)) / ‖b - a‖ · ‖b - c‖` and `lim inf ⟨x*ₖ, b - a⟩ ≥ β - φ(a)`. -/
theorem approx_mean_value_of_le (hab : a ≠ b) (ha : φ a = α) (hb : (β : EReal) ≤ φ b)
    (hlsc : ∀ x ∈ segment ℝ a b, ∀ᶠ y in 𝓝 x, LowerSemicontinuousAt φ y)
    (hbot : ∀ x ∈ segment ℝ a b, φ x ≠ ⊥) :
    ∃ c ∈ segment ℝ a b, c ≠ b ∧
      IsMinOn (fun x ↦ φ x - (((β - α) / ‖b - a‖ * ‖x - a‖ : ℝ) : EReal)) (segment ℝ a b) c ∧
      ∃ (x : ℕ → E) (v : ℕ → StrongDual ℝ E), Tendsto x atTop (funNhds φ c) ∧
        (∀ k, v k ∈ regularSubdiff φ (x k)) ∧
        (∀ ε > 0, ∀ᶠ k in atTop, (β - α) / ‖b - a‖ * ‖b - c‖ - ε ≤ v k (b - x k)) ∧
        (∀ ε > 0, ∀ᶠ k in atTop, β - α - ε ≤ v k (b - a)) := by
  classical
  set φ' := Function.update φ b (β : EReal) with hφ'
  have hφ'a : φ' a = α := by rw [hφ', Function.update_of_ne hab, ha]
  have hφ'b : φ' b = β := Function.update_self _ _ _
  have hφ'le : ∀ x, φ' x ≤ φ x := fun x ↦ by
    by_cases hx : x = b
    · subst hx; rw [hφ'b]; exact hb
    · rw [hφ', Function.update_of_ne hx]
  have hlsc' : ∀ x ∈ segment ℝ a b, ∀ᶠ y in 𝓝 x, LowerSemicontinuousAt φ' y := fun x hx ↦
    (hlsc x hx).mono fun y hy ↦ lowerSemicontinuousAt_update hb hy
  have hbot' : ∀ x ∈ segment ℝ a b, φ' x ≠ ⊥ := fun x hx ↦ by
    by_cases hxb : x = b
    · subst hxb; rw [hφ'b]; exact EReal.coe_ne_bot _
    · rw [hφ', Function.update_of_ne hxb]; exact hbot x hx
  obtain ⟨c, hc, hcb, hmin⟩ := exists_isMinOn_approx_mean_value hab hφ'a hφ'b
    fun x hx ↦ (hlsc' x hx).self_of_nhds
  have hφ'c : φ' c = φ c := by rw [hφ', Function.update_of_ne hcb]
  have hmin' : IsMinOn (fun x ↦ φ x - (((β - α) / ‖b - a‖ * ‖x - a‖ : ℝ) : EReal))
      (segment ℝ a b) c := fun x hx ↦ by
    have h := hmin hx
    simp only [mem_ofPred_eq, hφ'c] at h ⊢
    exact h.trans (EReal.sub_le_sub (hφ'le x) le_rfl)
  obtain ⟨x, v, hx, hv, h1, h2, -⟩ := approx_mean_value hab hφ'a hlsc' hbot' hc hcb hmin
  obtain ⟨hx1, hx2⟩ := tendsto_funNhds_iff.1 hx
  have hev : ∀ᶠ k in atTop, x k ≠ b := hx1.eventually (isOpen_ne.mem_nhds hcb)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have heq : ∀ k, N ≤ k → φ' =ᶠ[𝓝 (x k)] φ := fun k hk ↦
    eventually_of_mem (isOpen_ne.mem_nhds (hN k hk)) fun y hy ↦ by
      rw [hφ', Function.update_of_ne (show y ≠ b from hy)]
  refine ⟨c, hc, hcb, hmin', fun k ↦ x (k + N), fun k ↦ v (k + N), ?_, fun k ↦ ?_,
    fun ε hε ↦ (tendsto_add_atTop_nat N).eventually (h1 ε hε),
    fun ε hε ↦ (tendsto_add_atTop_nat N).eventually (h2 ε hε)⟩
  · refine tendsto_funNhds_iff.2 ⟨(tendsto_add_atTop_iff_nat N).2 hx1, ?_⟩
    rw [← hφ'c]
    refine ((tendsto_add_atTop_iff_nat N).2 hx2).congr fun k ↦ ?_
    exact (heq (k + N) (Nat.le_add_left N k)).self_of_nhds
  · rw [← regularSubdiff_congr (heq (k + N) (Nat.le_add_left N k))]
    exact hv (k + N)

end AMVT

end VariationalAnalysis
