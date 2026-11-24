/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import VariationalAnalysis.WellPosedness.Gateaux

/-!
# Amenable and prox-regular functions; Lipschitz-like subdifferentials

This file contains the classes of functions of [Mordukhovich 2018, Subsections 3.3.2–3.3.3]
and Lemma 3.28:

* amenable and strongly amenable functions (Def. 3.23): locally `φ = θ ∘ h` with `h` of class
  `C¹` (resp. `C²`), `θ` convex l.s.c. and `∂^∞θ(h x₀) ∩ ker ∇h(x₀)* = {0}`;
* prox-regular and subdifferentially continuous functions (Def. 3.27);
* Lemma 3.28: a continuously prox-regular function whose subgradient mapping is Lipschitz-like
  around `(x₀, v₀)` is of class `C^{1,1}` around `x₀`.

The book leaves the proof of Lemma 3.28 to Exercise 3.93, via maximal hypomonotonicity. Here it
follows from Prop. 3.24 for hypomonotone operators
(`LipschitzLikeWith.exists_lipschitzOnWith_of_locallyHypomonotoneAt`): prox-regularity together
with subdifferential continuity makes `∂φ` locally hypomonotone around `(x₀, v₀)`, so `∂φ` has a
Lipschitzian single-valued localization `g`, and the prox-regularity inequality sandwiches
`φ(z) - φ(y) - ⟨g y, z - y⟩` between `±(ℓ + η/2) ‖z - y‖²`. The assumption `x₀ ∈ int(dom φ)` of
the book is not needed (the Lipschitz-like property forces `∂φ(x) ≠ ∅`, hence `φ` finite, near
`x₀`), and neither is finite dimensionality.

## Main declarations

* `AmenableAtOfClass n φ x₀`, `AmenableAt φ x₀`, `StronglyAmenableAt φ x₀`: Def. 3.23 of
  [Mordukhovich 2018].
* `ProxRegularFor φ x₀ v₀`, `ProxRegularAt φ x₀`, `SubdiffContinuousFor φ x₀ v₀`,
  `SubdiffContinuousAt φ x₀`, `ContinuouslyProxRegularFor φ x₀ v₀`,
  `ContinuouslyProxRegularAt φ x₀`: Def. 3.27 of [Mordukhovich 2018].

## Main results

* `SubdiffContinuousFor.tendsto`: subdifferential continuity in filter form.
* `ContinuouslyProxRegularFor.locallyHypomonotoneAt`: the subgradient mapping of a continuously
  prox-regular function is locally hypomonotone [Mordukhovich 2018, p. 192].
* `ContinuouslyProxRegularFor.exists_C11`: Lemma 3.28 of [Mordukhovich 2018].
* `not_lipschitzLikeAt_subdiff_of_continuouslyProxRegularFor`: reduced form of Thm. 3.29 and
  Thm. 3.31 of [Mordukhovich 2018]: if `φ` is continuously prox-regular at `x₀` for `v₀` and not
  Gâteaux differentiable around `x₀`, then `∂φ` is not Lipschitz-like around `(x₀, v₀)`.
* `continuouslyProxRegularFor_of_convex`: Exercise 3.92(i): l.s.c. convex functions are
  continuously prox-regular.
* `continuouslyProxRegularFor_of_C11`: Exercise 3.92(iii): `C^{1,1}` functions are continuously
  prox-regular.

## Using these results for Thm. 3.29 and Thm. 3.31

By Cor. 3.21 (resp. Cor. 3.22), the metric regularity of `S` is equivalent to the Lipschitz-like
property of `∂ψ` around `(w₀, v₀)` (resp. `(w₀, q₀)`); Thm. 3.29 (resp. 3.31) is then
`fun h ↦ not_lipschitzLikeAt_subdiff_of_continuouslyProxRegularFor hψ hnd (cor321.1 h)`.
-/

open Filter Topology Set Metric
open scoped NNReal

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Amenable

/-- Def. 3.23 of [Mordukhovich 2018] with smoothness class `n` of the inner mapping: `φ` is
finite at `x₀` and there are an open neighborhood `U` of `x₀`, a mapping `h : E → ℝᵐ` of class
`Cⁿ` on `U` and a convex l.s.c. function `θ : ℝᵐ → (-∞, ∞]` with `φ = θ ∘ h` on `U` and the
qualification condition `∂^∞θ(h x₀) ∩ ker ∇h(x₀)* = {0}` (the book writes `ȳ := θ(x̄)` for the
point `h(x̄)`). Here `ℝᵐ` is `EuclideanSpace ℝ (Fin m)`, and `∇h(x₀)* w = w ∘ ∇h(x₀)`. -/
def AmenableAtOfClass (n : WithTop ℕ∞) (φ : E → EReal) (x₀ : E) : Prop :=
  φ x₀ ≠ ⊤ ∧ ∃ (m : ℕ) (U : Set E) (h : E → EuclideanSpace ℝ (Fin m))
    (θ : EuclideanSpace ℝ (Fin m) → EReal), IsOpen U ∧ x₀ ∈ U ∧ ContDiffOn ℝ n h U ∧
    Convex ℝ (θ.Epi univ) ∧ LowerSemicontinuous θ ∧ (∀ w, θ w ≠ ⊥) ∧ (∀ x ∈ U, φ x = θ (h x)) ∧
    ∀ w ∈ singularSubdiff θ (h x₀), w.comp (fderiv ℝ h x₀) = 0 → w = 0

/-- Def. 3.23 of [Mordukhovich 2018]: `φ` is amenable at `x₀ ∈ dom φ` if near `x₀` it is a
composition `θ ∘ h` of a `C¹` mapping `h` and a convex l.s.c. function `θ` with
`∂^∞θ(h x₀) ∩ ker ∇h(x₀)* = {0}`. -/
def AmenableAt (φ : E → EReal) (x₀ : E) : Prop := AmenableAtOfClass 1 φ x₀

/-- Def. 3.23 of [Mordukhovich 2018]: `φ` is strongly amenable at `x₀` if the inner mapping `h`
of an amenable representation can be chosen of class `C²`. -/
def StronglyAmenableAt (φ : E → EReal) (x₀ : E) : Prop := AmenableAtOfClass 2 φ x₀

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Amenability with inner mapping of class `Cⁿ` implies amenability of class `Cᵐ` for `m ≤ n`. -/
theorem AmenableAtOfClass.mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → EReal} {x₀ : E} {m n : WithTop ℕ∞} (h : AmenableAtOfClass n φ x₀) (hmn : m ≤ n) :
    AmenableAtOfClass m φ x₀ := by
  obtain ⟨hx, k, U, h, θ, hU, hxU, hh, hθ⟩ := h
  exact ⟨hx, k, U, h, θ, hU, hxU, hh.of_le hmn, hθ⟩

/-- Strongly amenable functions are amenable. -/
theorem StronglyAmenableAt.amenableAt {φ : E → EReal} {x₀ : E} (h : StronglyAmenableAt φ x₀) :
    AmenableAt φ x₀ :=
  AmenableAtOfClass.mono h (by norm_num)

end Amenable

section ProxRegular

/-- Def. 3.27(i) of [Mordukhovich 2018]: `φ` is prox-regular at `x₀` for `v₀ ∈ ∂φ(x₀)` if it is
l.s.c. around `x₀` and there are `ε > 0` and `η ≥ 0` with
`φ(u) ≥ φ(x) + ⟨v, u - x⟩ - (η/2) ‖u - x‖²` whenever `v ∈ ∂φ(x)`, `‖v - v₀‖ ≤ ε`,
`‖u - x₀‖ ≤ ε`, `‖x - x₀‖ ≤ ε` and `φ(x) ≤ φ(x₀) + ε`. (In a finite-dimensional space the
class of such functions does not depend on the norm; the book uses the Euclidean norm.) -/
def ProxRegularFor (φ : E → EReal) (x₀ : E) (v₀ : StrongDual ℝ E) : Prop :=
  v₀ ∈ subdiff φ x₀ ∧ (∀ᶠ x in 𝓝 x₀, LowerSemicontinuousAt φ x) ∧
    ∃ ε > (0 : ℝ), ∃ η ≥ (0 : ℝ), ∀ x u : E, ∀ v ∈ subdiff φ x, ∀ r : ℝ, φ x = r →
      ‖v - v₀‖ ≤ ε → ‖u - x₀‖ ≤ ε → ‖x - x₀‖ ≤ ε → φ x ≤ φ x₀ + (ε : EReal) →
        ((r + v (u - x) - η / 2 * ‖u - x‖ ^ 2 : ℝ) : EReal) ≤ φ u

/-- Def. 3.27(i) of [Mordukhovich 2018]: `φ` is prox-regular at `x₀` if it is prox-regular at
`x₀` for every `v₀ ∈ ∂φ(x₀)`. -/
def ProxRegularAt (φ : E → EReal) (x₀ : E) : Prop :=
  ∀ v₀ ∈ subdiff φ x₀, ProxRegularFor φ x₀ v₀

/-- Def. 3.27(ii) of [Mordukhovich 2018]: `φ` is subdifferentially continuous at `x₀` for
`v₀ ∈ ∂φ(x₀)` if `φ(xₖ) → φ(x₀)` whenever `xₖ → x₀`, `vₖ → v₀` with `vₖ ∈ ∂φ(xₖ)`. -/
def SubdiffContinuousFor (φ : E → EReal) (x₀ : E) (v₀ : StrongDual ℝ E) : Prop :=
  v₀ ∈ subdiff φ x₀ ∧ ∀ (x : ℕ → E) (v : ℕ → StrongDual ℝ E), Tendsto x atTop (𝓝 x₀) →
    Tendsto v atTop (𝓝 v₀) → (∀ k, v k ∈ subdiff φ (x k)) →
      Tendsto (fun k ↦ φ (x k)) atTop (𝓝 (φ x₀))

/-- Def. 3.27(ii) of [Mordukhovich 2018]: `φ` is subdifferentially continuous at `x₀` if it is
so for every `v₀ ∈ ∂φ(x₀)`. -/
def SubdiffContinuousAt (φ : E → EReal) (x₀ : E) : Prop :=
  ∀ v₀ ∈ subdiff φ x₀, SubdiffContinuousFor φ x₀ v₀

/-- [Mordukhovich 2018, p. 132]: `φ` is continuously prox-regular at `x₀` for `v₀` if it is
prox-regular and subdifferentially continuous at `x₀` for `v₀` (Def. 3.27). -/
def ContinuouslyProxRegularFor (φ : E → EReal) (x₀ : E) (v₀ : StrongDual ℝ E) : Prop :=
  ProxRegularFor φ x₀ v₀ ∧ SubdiffContinuousFor φ x₀ v₀

/-- [Mordukhovich 2018, p. 132]: `φ` is continuously prox-regular at `x₀` if it is prox-regular
and subdifferentially continuous at `x₀` (Def. 3.27). -/
def ContinuouslyProxRegularAt (φ : E → EReal) (x₀ : E) : Prop :=
  ProxRegularAt φ x₀ ∧ SubdiffContinuousAt φ x₀

variable {φ : E → EReal} {x₀ : E} {v₀ : StrongDual ℝ E}

/-- A function continuously prox-regular at `x₀` is continuously prox-regular at `x₀` for every
`v₀ ∈ ∂φ(x₀)`. -/
theorem ContinuouslyProxRegularAt.continuouslyProxRegularFor (h : ContinuouslyProxRegularAt φ x₀)
    (hv₀ : v₀ ∈ subdiff φ x₀) : ContinuouslyProxRegularFor φ x₀ v₀ :=
  ⟨h.1 v₀ hv₀, h.2 v₀ hv₀⟩

/-- Subdifferential continuity [Mordukhovich 2018, Def. 3.27(ii)] in filter form: `φ(x) → φ(x₀)`
as `(x, v) → (x₀, v₀)` within `gph ∂φ`. -/
theorem SubdiffContinuousFor.tendsto (h : SubdiffContinuousFor φ x₀ v₀) :
    Tendsto (fun p : E × StrongDual ℝ E ↦ φ p.1) (𝓝[{p | p.2 ∈ subdiff φ p.1}] (x₀, v₀))
      (𝓝 (φ x₀)) := by
  classical
  rw [tendsto_iff_seq_tendsto]
  intro p hp
  have hs : ∀ᶠ k in atTop, (p k).2 ∈ subdiff φ (p k).1 := (tendsto_nhdsWithin_iff.1 hp).2
  set q : ℕ → E × StrongDual ℝ E := fun k ↦
    if (p k).2 ∈ subdiff φ (p k).1 then p k else (x₀, v₀) with hq_def
  have hpq : ∀ᶠ k in atTop, q k = p k := hs.mono fun k hk ↦ if_pos hk
  have hq : Tendsto q atTop (𝓝 (x₀, v₀)) :=
    (tendsto_nhdsWithin_iff.1 hp).1.congr' (hpq.mono fun _ hk ↦ hk.symm)
  have hqs : ∀ k, (q k).2 ∈ subdiff φ (q k).1 := by
    intro k
    have hqk : q k = if (p k).2 ∈ subdiff φ (p k).1 then p k else (x₀, v₀) := rfl
    by_cases hk : (p k).2 ∈ subdiff φ (p k).1
    · rw [hqk, if_pos hk]; exact hk
    · rw [hqk, if_neg hk]; exact h.1
  have := h.2 (fun k ↦ (q k).1) (fun k ↦ (q k).2) ((continuous_fst.tendsto _).comp hq)
    ((continuous_snd.tendsto _).comp hq) hqs
  exact this.congr' (hpq.mono fun k hk ↦ by simp [hk])

/-- Subdifferential continuity [Mordukhovich 2018, Def. 3.27(ii)], quantitative form: for every
`ε > 0` there is `δ > 0` such that `φ(x) ≤ φ(x₀) + ε` whenever `v ∈ ∂φ(x)`, `‖x - x₀‖ < δ` and
`‖v - v₀‖ < δ`. -/
theorem SubdiffContinuousFor.exists_forall_le (h : SubdiffContinuousFor φ x₀ v₀) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > (0 : ℝ), ∀ x, ∀ v ∈ subdiff φ x, ‖x - x₀‖ < δ → ‖v - v₀‖ < δ →
      φ x ≤ φ x₀ + (ε : EReal) := by
  obtain ⟨r, hr, -⟩ := h.1
  have hI : Iio ((r + ε : ℝ) : EReal) ∈ 𝓝 (φ x₀) :=
    Iio_mem_nhds (by rw [hr, EReal.coe_lt_coe_iff]; linarith)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 (h.tendsto hI)
  refine ⟨δ, hδ, fun x v hv hx hv' ↦ ?_⟩
  have hmem : (x, v) ∈ ball (x₀, v₀) δ ∩ {p : E × StrongDual ℝ E | p.2 ∈ subdiff φ p.1} := by
    refine ⟨?_, hv⟩
    rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm]
    exact ⟨hx, hv'⟩
  have := hball hmem
  simp only [mem_preimage, mem_Iio] at this
  rw [hr, ← EReal.coe_add]
  exact this.le

/-- The prox-regularity inequality [Mordukhovich 2018, Def. 3.27(i)] on neighborhoods, for a
continuously prox-regular function: subdifferential continuity removes the constraint
`φ(x) ≤ φ(x₀) + ε`. -/
theorem ContinuouslyProxRegularFor.exists_forall_le (h : ContinuouslyProxRegularFor φ x₀ v₀) :
    ∃ δ > (0 : ℝ), ∃ η ≥ (0 : ℝ), ∀ x u : E, ∀ v ∈ subdiff φ x, ∀ r : ℝ, φ x = r →
      ‖v - v₀‖ < δ → ‖u - x₀‖ < δ → ‖x - x₀‖ < δ →
        ((r + v (u - x) - η / 2 * ‖u - x‖ ^ 2 : ℝ) : EReal) ≤ φ u := by
  obtain ⟨⟨-, -, ε, hε, η, hη, H⟩, hc⟩ := h
  obtain ⟨δ₁, hδ₁, Hc⟩ := hc.exists_forall_le hε
  refine ⟨min ε δ₁, lt_min hε hδ₁, η, hη, fun x u v hv r hr hvv hu hx ↦ ?_⟩
  exact H x u v hv r hr (hvv.le.trans (min_le_left _ _)) (hu.le.trans (min_le_left _ _))
    (hx.le.trans (min_le_left _ _))
    (Hc x v hv (hx.trans_le (min_le_right _ _)) (hvv.trans_le (min_le_right _ _)))

/-- The subgradient mapping of a continuously prox-regular function is locally hypomonotone
around `(x₀, v₀)` [Mordukhovich 2018, Def. 5.1(iii) and p. 192]: adding the prox-regularity
inequalities at `(x₁, v₁)` and `(x₂, v₂)` gives `⟨v₁ - v₂, x₁ - x₂⟩ ≥ -η ‖x₁ - x₂‖²`. -/
theorem ContinuouslyProxRegularFor.locallyHypomonotoneAt (h : ContinuouslyProxRegularFor φ x₀ v₀) :
    LocallyHypomonotoneAt (subdiff φ) x₀ v₀ := by
  obtain ⟨δ, hδ, η, hη, H⟩ := h.exists_forall_le
  refine ⟨η + 1, by linarith, ball x₀ δ, ball_mem_nhds _ hδ, ball v₀ δ, ball_mem_nhds _ hδ,
    fun x₁ hx₁ x₂ hx₂ v₁ hv₁ v₂ hv₂ ↦ ?_⟩
  obtain ⟨r₁, hr₁, -⟩ := hv₁.1
  obtain ⟨r₂, hr₂, -⟩ := hv₂.1
  have hx₁' : ‖x₁ - x₀‖ < δ := by rw [← dist_eq_norm]; exact hx₁
  have hx₂' : ‖x₂ - x₀‖ < δ := by rw [← dist_eq_norm]; exact hx₂
  have hv₁' : ‖v₁ - v₀‖ < δ := by rw [← dist_eq_norm]; exact hv₁.2
  have hv₂' : ‖v₂ - v₀‖ < δ := by rw [← dist_eq_norm]; exact hv₂.2
  have h₁ := H x₁ x₂ v₁ hv₁.1 r₁ hr₁ hv₁' hx₂' hx₁'
  have h₂ := H x₂ x₁ v₂ hv₂.1 r₂ hr₂ hv₂' hx₁' hx₂'
  rw [hr₂, EReal.coe_le_coe_iff] at h₁
  rw [hr₁, EReal.coe_le_coe_iff] at h₂
  have e₁ : v₁ (x₂ - x₁) = -v₁ (x₁ - x₂) := by rw [← map_neg, neg_sub]
  have e₂ : ‖x₂ - x₁‖ = ‖x₁ - x₂‖ := norm_sub_rev _ _
  rw [e₁, e₂] at h₁
  rw [sub_apply]
  nlinarith [sq_nonneg ‖x₁ - x₂‖]

variable {ℓ : ℝ≥0}

/-- Lemma 3.28 of [Mordukhovich 2018] (continuously prox-regular functions with Lipschitz-like
subdifferentials): if `φ` is continuously prox-regular at `x₀` for `v₀ ∈ ∂φ(x₀)` and `∂φ` is
Lipschitz-like around `(x₀, v₀)` with modulus `ℓ`, then `φ` is of class `C^{1,1}` on an open
neighborhood `U` of `x₀`: it agrees on `U` with a real function `f` differentiable at every point
of `U`, `∇f` is Lipschitz on `U` with modulus `ℓ`, and `∂φ(y) = {∇f(y)}` for `y ∈ U`.
The book's assumption `x₀ ∈ int(dom φ)` is not needed, nor is finite dimensionality. -/
theorem ContinuouslyProxRegularFor.exists_C11 (h : ContinuouslyProxRegularFor φ x₀ v₀)
    (hL : LipschitzLikeWith ℓ (subdiff φ) x₀ v₀) :
    ∃ U, IsOpen U ∧ x₀ ∈ U ∧ ∃ f : E → ℝ, ∃ g : E → StrongDual ℝ E, (∀ y ∈ U, φ y = f y) ∧
      (∀ y ∈ U, subdiff φ y = {g y}) ∧ (∀ y ∈ U, HasFDerivAt f (g y) y) ∧
      LipschitzOnWith ℓ g U := by
  obtain ⟨δ, hδ, η, hη, H⟩ := h.exists_forall_le
  obtain ⟨U', hU', V', -, -, g, hg, hgL, hg₀⟩ :=
    hL.exists_lipschitzOnWith_of_locallyHypomonotoneAt h.locallyHypomonotoneAt h.1.1
  obtain ⟨ρ₀, hρ₀, hρ₀U⟩ := Metric.mem_nhds_iff.1 hU'
  have hℓ : (0 : ℝ) ≤ ℓ := ℓ.coe_nonneg
  set ρ := min ρ₀ (δ / (ℓ + 1)) with hρ_def
  have hρ : 0 < ρ := lt_min hρ₀ (by positivity)
  have hρU : ball x₀ ρ ⊆ U' := (ball_subset_ball (min_le_left _ _)).trans hρ₀U
  have hρδ' : (ℓ + 1) * ρ ≤ δ := by
    have := min_le_right ρ₀ (δ / (ℓ + 1))
    rw [← hρ_def, le_div_iff₀ (by positivity)] at this
    linarith
  have hρδ : ρ ≤ δ := by nlinarith
  set B := ball x₀ ρ
  have hgL' : LipschitzOnWith ℓ g B := hgL.mono hρU
  have hgmem : ∀ y ∈ B, g y ∈ subdiff φ y := fun y hy ↦
    ((hg y (hρU hy)).symm ▸ mem_singleton (g y) : g y ∈ subdiff φ y ∩ V').1
  have hgv : ∀ y ∈ B, ‖g y - v₀‖ < δ := by
    intro y hy
    have hy' : dist y x₀ < ρ := hy
    rw [← dist_eq_norm, ← hg₀]
    calc dist (g y) (g x₀) ≤ ℓ * dist y x₀ := hgL'.dist_le_mul y hy x₀ (mem_ball_self hρ)
      _ ≤ ℓ * ρ := by gcongr
      _ < δ := by nlinarith
  have hnorm : ∀ y ∈ B, ‖y - x₀‖ < δ := fun y hy ↦ by
    rw [← dist_eq_norm]; exact (mem_ball.1 hy).trans_le hρδ
  have hfin : ∀ y ∈ B, φ y = ((φ y).toReal : EReal) := by
    intro y hy
    obtain ⟨r, hr, -⟩ := hgmem y hy
    rw [hr, EReal.toReal_coe]
  have hineq : ∀ y ∈ B, ∀ z ∈ B,
      (φ y).toReal + g y (z - y) - η / 2 * ‖z - y‖ ^ 2 ≤ (φ z).toReal := by
    intro y hy z hz
    have := H y z (g y) (hgmem y hy) _ (hfin y hy) (hgv y hy) (hnorm z hz) (hnorm y hy)
    rwa [hfin z hz, EReal.coe_le_coe_iff] at this
  have hd : ∀ y ∈ B, HasFDerivAt (fun z ↦ (φ z).toReal) (g y) y := fun y hy ↦
    hasFDerivAt_of_lipschitzOnWith_of_le isOpen_ball hgL' hineq hy
  refine ⟨B, isOpen_ball, mem_ball_self hρ, fun z ↦ (φ z).toReal, g, hfin, fun y hy ↦ ?_, hd,
    hgL'⟩
  rw [subdiff_congr (Filter.mem_of_superset (isOpen_ball.mem_nhds hy) hfin)]
  exact subdiff_of_hasFDerivAt_of_continuousAt
    (Filter.mem_of_superset (isOpen_ball.mem_nhds hy) hd)
    (hgL'.continuousOn.continuousAt (isOpen_ball.mem_nhds hy))

/-- Reduced form of Thm. 3.29 and Thm. 3.31 of [Mordukhovich 2018]: if `φ` is continuously
prox-regular at `x₀` for `v₀ ∈ ∂φ(x₀)` and not Gâteaux differentiable around `x₀` (there is no
neighborhood of `x₀` at each point of which `φ` is Gâteaux differentiable), then `∂φ` is not
Lipschitz-like around `(x₀, v₀)`. This is Lemma 3.28 combined with Exercise 3.90(ii)
(`C^{1,1}` functions are Gâteaux differentiable). -/
theorem not_lipschitzLikeAt_subdiff_of_continuouslyProxRegularFor
    (h : ContinuouslyProxRegularFor φ x₀ v₀)
    (hnd : ¬ ∃ U ∈ 𝓝 x₀, ∀ y ∈ U, ∃ v, HasGateauxDerivAt φ v y) :
    ¬ LipschitzLikeAt (subdiff φ) x₀ v₀ := by
  rintro ⟨ℓ, hL⟩
  obtain ⟨U, hUo, hx₀U, f, g, hf, -, hd, -⟩ := h.exists_C11 hL
  exact hnd ⟨U, hUo.mem_nhds hx₀U, fun y hy ↦
    ⟨g y, hasGateauxDerivAt_of_hasFDerivAt (hd y hy)
      (Filter.mem_of_superset (hUo.mem_nhds hy) hf)⟩⟩

end ProxRegular

section Examples

variable {φ : E → EReal} {x₀ : E} {v₀ : StrongDual ℝ E}

/-- Exercise 3.92(i) of [Mordukhovich 2018]: an l.s.c. convex function is continuously
prox-regular at every `x₀ ∈ dom φ` for every `v₀ ∈ ∂φ(x₀)` (with `η = 0`). -/
theorem continuouslyProxRegularFor_of_convex (hconv : Convex ℝ (φ.Epi univ))
    (hlsc : LowerSemicontinuous φ) (h₀ : v₀ ∈ subdiff φ x₀) :
    ContinuouslyProxRegularFor φ x₀ v₀ := by
  refine ⟨⟨h₀, Eventually.of_forall hlsc, 1, one_pos, 0, le_rfl,
    fun x u v hv r hr _ _ _ _ ↦ ?_⟩, h₀, fun x v hx hv hmem ↦ ?_⟩
  · have := (mem_subdiff_of_convex hconv hr).1 hv u
    simpa using this
  · obtain ⟨r₀, hr₀, -⟩ := h₀
    rw [hr₀]
    refine tendsto_order.2 ⟨fun a ha ↦ hx.eventually
        (hlsc x₀ a (show a < φ x₀ by rw [hr₀]; exact ha)),
      fun b hb ↦ ?_⟩
    have hup : ∀ k, φ (x k) ≤ ((r₀ - v k (x₀ - x k) : ℝ) : EReal) := by
      intro k
      obtain ⟨r, hr, -⟩ := hmem k
      have := (mem_subdiff_of_convex hconv hr).1 (hmem k) x₀
      rw [hr₀, EReal.coe_le_coe_iff] at this
      rw [hr, EReal.coe_le_coe_iff]
      linarith
    have hT : Tendsto (fun k ↦ ((r₀ - v k (x₀ - x k) : ℝ) : EReal)) atTop (𝓝 (r₀ : EReal)) := by
      refine (continuous_coe_real_ereal.tendsto _).comp ?_
      have : Tendsto (fun k ↦ v k (x₀ - x k)) atTop (𝓝 (v₀ (x₀ - x₀))) :=
        ((continuous_fst.clm_apply continuous_snd).tendsto (v₀, x₀ - x₀)).comp
          (hv.prodMk_nhds (tendsto_const_nhds.sub hx))
      simpa using (tendsto_const_nhds (x := r₀)).sub this
    filter_upwards [hT.eventually (gt_mem_nhds hb)] with k hk
    exact (hup k).trans_lt hk

/-- Exercise 3.92(iii) of [Mordukhovich 2018]: a function of class `C^{1,1}` on an open set `U`
(it agrees on `U` with a real function `f` differentiable on `U` with `∇f = g` Lipschitz on `U`)
is continuously prox-regular at every `x₀ ∈ U` (for `v₀ = ∇f(x₀)`, the only subgradient). -/
theorem continuouslyProxRegularFor_of_C11 {U : Set E} (hU : IsOpen U) {f : E → ℝ}
    {g : E → StrongDual ℝ E} {L : ℝ≥0} (hφ : ∀ y ∈ U, φ y = f y)
    (hf : ∀ y ∈ U, HasFDerivAt f (g y) y) (hg : LipschitzOnWith L g U) (hx₀ : x₀ ∈ U) :
    ContinuouslyProxRegularFor φ x₀ (g x₀) := by
  have hsub : ∀ y ∈ U, subdiff φ y = {g y} := by
    intro y hy
    rw [subdiff_congr (Filter.mem_of_superset (hU.mem_nhds hy) hφ)]
    exact subdiff_of_hasFDerivAt_of_continuousAt (Filter.mem_of_superset (hU.mem_nhds hy) hf)
      (hg.continuousOn.continuousAt (hU.mem_nhds hy))
  have hcont : ∀ y ∈ U, ContinuousAt φ y := by
    intro y hy
    have : ContinuousAt (fun z ↦ (f z : EReal)) y :=
      continuous_coe_real_ereal.continuousAt.comp (hf y hy).continuousAt
    exact this.congr (Filter.mem_of_superset (hU.mem_nhds hy) fun z hz ↦ (hφ z hz).symm)
  have h₀ : g x₀ ∈ subdiff φ x₀ := (hsub x₀ hx₀).symm ▸ mem_singleton _
  obtain ⟨ε, hε, hεU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx₀)
  refine ⟨⟨h₀, Filter.mem_of_superset (hU.mem_nhds hx₀) fun y hy ↦
    (hcont y hy).lowerSemicontinuousAt,
    ε, hε, 2 * L, by positivity, fun x u v hv r hr _ hu hx _ ↦ ?_⟩, h₀, fun x v hx hv hmem ↦ ?_⟩
  · have hxU : x ∈ closedBall x₀ ε := by rw [mem_closedBall, dist_eq_norm]; exact hx
    have huU : u ∈ closedBall x₀ ε := by rw [mem_closedBall, dist_eq_norm]; exact hu
    rw [hsub x (hεU hxU), mem_singleton_iff] at hv
    subst hv
    rw [hφ x (hεU hxU), EReal.coe_eq_coe_iff] at hr
    subst hr
    rw [hφ u (hεU huU), EReal.coe_le_coe_iff]
    have hseg : segment ℝ x u ⊆ closedBall x₀ ε := (convex_closedBall x₀ ε).segment_subset hxU huU
    have hmv := (convex_segment x u).norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (f := f) (f' := g) (φ := g x) (C := L * ‖u - x‖)
      (fun z hz ↦ (hf z (hεU (hseg hz))).hasFDerivWithinAt)
      (fun z hz ↦ by
        rw [← dist_eq_norm]
        calc dist (g z) (g x) ≤ L * dist z x :=
              hg.dist_le_mul z (hεU (hseg hz)) x (hεU (hseg (left_mem_segment ℝ x u)))
          _ ≤ L * ‖u - x‖ := by
              rw [dist_eq_norm]; gcongr; exact norm_sub_le_of_mem_segment hz)
      (left_mem_segment ℝ x u) (right_mem_segment ℝ x u)
    rw [Real.norm_eq_abs, abs_le] at hmv
    nlinarith [hmv.1, norm_nonneg (u - x), L.coe_nonneg]
  · exact (hcont x₀ hx₀).tendsto.comp hx

end Examples

end VariationalAnalysis
