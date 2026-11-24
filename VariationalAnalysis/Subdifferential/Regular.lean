/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Topology.Instances.EReal.Lemmas
import ConvexAnalysis.Extended.ConvexIndicator
import ConvexAnalysis.Extended.Epigraph
import VariationalAnalysis.Normal.Regular

/-!
# Regular (Fréchet) subgradients

For `φ : E → EReal` finite at `x₀`, the *regular subdifferential* (presubdifferential, Fréchet
subdifferential) [Mordukhovich 2018, (1.33)], [Clason–Valkonen, (16.2)] is

  `∂̂φ(x₀) = {v ∈ E* | lim inf_{x → x₀} (φ x - φ x₀ - ⟨v, x - x₀⟩) / ‖x - x₀‖ ≥ 0}`,

and its `ω`-enlargement [Mordukhovich 2018, (1.34)] replaces `0` by `-ω`. The `lim inf` condition
is unfolded as: for every `ε > 0`, `φ x₀ + v (x - x₀) - (ω + ε) ‖x - x₀‖ ≤ φ x` for `x` near
`x₀`. Both sets are empty when `φ x₀` is not finite.

The epigraph is `Function.Epi φ univ ⊆ E × ℝ` from `ConvexAnalysis`, and the indicator function
of a set is `Set.convex_indicator` (`0` on the set, `⊤` off it).

## Main results

* `zero_mem_regularSubdiff_of_isLocalMin`: generalized Fermat rule [Mordukhovich 2018,
  Prop. 1.30(i)], [Clason–Valkonen, Thm. 16.2].
* `regularSubdiff_of_hasFDerivAt`: `∂̂f(x₀) = {f'(x₀)}` for differentiable `f`
  [Mordukhovich 2018, p. 28], [Clason–Valkonen, Thm. 16.4].
* `mem_regularSubdiff_iff_exists_support`: Thm. 1.27 of [Mordukhovich 2018], first part (smooth
  variational description of regular subgradients).
* `mem_regularSubdiff_add_iff`: sum rule with a differentiable function
  [Mordukhovich 2018, Prop. 1.30(ii)].
* `epsSubdiff_convex_indicator`: `∂̂_ω δ_Ω(x₀) = N̂_ω(x₀; Ω)` [Mordukhovich 2018, p. 29],
  [Clason–Valkonen, Cor. 18.7].
* `mem_regularSubdiff_iff_coprod_mem`: Thm. 1.26, (1.36), of [Mordukhovich 2018]: regular
  subgradients are the regular normals `(v, -1)` to the epigraph.
* `eq_of_mem_regularNormalCone_epi`: Exercise 1.62 of [Mordukhovich 2018]: slanted regular
  normals to the epigraph live on the graph.
* `mem_regularSubdiff_of_convex`: Prop. 1.25 of [Mordukhovich 2018] for regular subgradients of
  functions with convex epigraph.
-/

open Filter Topology Set

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {φ : E → EReal} {x₀ : E} {v : StrongDual ℝ E} {ω r : ℝ}

/-- The `ω`-subgradients of `φ` at `x₀` [Mordukhovich 2018, (1.34)]. Empty unless `φ x₀` is
finite. -/
def epsSubdiff (ω : ℝ) (φ : E → EReal) (x₀ : E) : Set (StrongDual ℝ E) :=
  {v | ∃ r : ℝ, φ x₀ = r ∧
    ∀ ε > 0, ∀ᶠ x in 𝓝 x₀, ((r + v (x - x₀) - (ω + ε) * ‖x - x₀‖ : ℝ) : EReal) ≤ φ x}

/-- The regular (Fréchet) subdifferential of `φ` at `x₀` [Mordukhovich 2018, (1.33)],
[Clason–Valkonen, (16.2)]. Empty unless `φ x₀` is finite. -/
def regularSubdiff (φ : E → EReal) (x₀ : E) : Set (StrongDual ℝ E) :=
  {v | ∃ r : ℝ, φ x₀ = r ∧
    ∀ ε > 0, ∀ᶠ x in 𝓝 x₀, ((r + v (x - x₀) - ε * ‖x - x₀‖ : ℝ) : EReal) ≤ φ x}

/-- Cancelling a finite summand in `EReal`: `A ≤ y + c ↔ A - c ≤ y`. -/
theorem coe_le_add_coe_iff {A c : ℝ} {y : EReal} :
    (A : EReal) ≤ y + c ↔ ((A - c : ℝ) : EReal) ≤ y := by
  induction y with
  | bot => simp only [EReal.bot_add, le_bot_iff, EReal.coe_ne_bot]
  | top => simp
  | coe y =>
    rw [← EReal.coe_add, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith

/-- The indicator function `δ_Ω` vanishes on `Ω`. -/
theorem convex_indicator_of_mem {α : Type*} {Ω : Set α} {x : α} (h : x ∈ Ω) :
    Ω.convex_indicator x = ((0 : ℝ) : EReal) := by
  simp [Set.convex_indicator, h]

/-- The indicator function `δ_Ω` equals `⊤` off `Ω`. -/
theorem convex_indicator_of_notMem {α : Type*} {Ω : Set α} {x : α} (h : x ∉ Ω) :
    Ω.convex_indicator x = ⊤ := by
  simp [Set.convex_indicator, h]

/-- For `ω = 0` the `ω`-subgradients are the regular subgradients: `∂̂₀φ(x₀) = ∂̂φ(x₀)`. -/
theorem epsSubdiff_zero : epsSubdiff 0 φ x₀ = regularSubdiff φ x₀ := by
  ext v; simp [epsSubdiff, regularSubdiff]

/-- Membership in `∂̂φ(x₀)` when `φ(x₀) = r` is finite: `v ∈ ∂̂φ(x₀)` iff for every `ε > 0`,
`r + ⟨v, x - x₀⟩ - ε ‖x - x₀‖ ≤ φ(x)` for all `x` near `x₀`. -/
theorem mem_regularSubdiff_iff (hr : φ x₀ = r) : v ∈ regularSubdiff φ x₀ ↔
    ∀ ε > 0, ∀ᶠ x in 𝓝 x₀, ((r + v (x - x₀) - ε * ‖x - x₀‖ : ℝ) : EReal) ≤ φ x := by
  refine ⟨fun ⟨s, hs, h⟩ ↦ ?_, fun h ↦ ⟨r, hr, h⟩⟩
  rw [hr, EReal.coe_eq_coe_iff] at hs
  exact hs ▸ h

/-- Membership in `∂̂_ωφ(x₀)` when `φ(x₀) = r` is finite: `v ∈ ∂̂_ωφ(x₀)` iff for every `ε > 0`,
`r + ⟨v, x - x₀⟩ - (ω + ε) ‖x - x₀‖ ≤ φ(x)` for all `x` near `x₀`. -/
theorem mem_epsSubdiff_iff (hr : φ x₀ = r) : v ∈ epsSubdiff ω φ x₀ ↔
    ∀ ε > 0, ∀ᶠ x in 𝓝 x₀, ((r + v (x - x₀) - (ω + ε) * ‖x - x₀‖ : ℝ) : EReal) ≤ φ x := by
  refine ⟨fun ⟨s, hs, h⟩ ↦ ?_, fun h ↦ ⟨r, hr, h⟩⟩
  rw [hr, EReal.coe_eq_coe_iff] at hs
  exact hs ▸ h

/-- Regular subgradients of a real-valued function. -/
theorem mem_regularSubdiff_coe {f : E → ℝ} : v ∈ regularSubdiff (fun x ↦ (f x : EReal)) x₀ ↔
    ∀ ε > 0, ∀ᶠ x in 𝓝 x₀, f x₀ + v (x - x₀) - ε * ‖x - x₀‖ ≤ f x := by
  rw [mem_regularSubdiff_iff (φ := fun x ↦ (f x : EReal)) (r := f x₀) rfl]
  simp only [EReal.coe_le_coe_iff]

/-- Regular subgradients are `ω`-subgradients for every `ω ≥ 0`: `∂̂φ(x₀) ⊆ ∂̂_ωφ(x₀)`. -/
theorem regularSubdiff_subset_epsSubdiff (hω : 0 ≤ ω) :
    regularSubdiff φ x₀ ⊆ epsSubdiff ω φ x₀ := by
  refine fun v ⟨r, hr, h⟩ ↦ ⟨r, hr, fun ε hε ↦ (h ε hε).mono fun x hx ↦ le_trans ?_ hx⟩
  exact EReal.coe_le_coe_iff.2 (by nlinarith [norm_nonneg (x - x₀)])

/-- If `φ ≤ ψ` near `x₀` with equality at `x₀`, then `∂̂φ(x₀) ⊆ ∂̂ψ(x₀)`. -/
theorem regularSubdiff_subset_of_le {ψ : E → EReal} (hle : ∀ᶠ x in 𝓝 x₀, φ x ≤ ψ x)
    (heq : φ x₀ = ψ x₀) : regularSubdiff φ x₀ ⊆ regularSubdiff ψ x₀ := by
  rintro v ⟨r, hr, h⟩
  exact ⟨r, heq ▸ hr, fun ε hε ↦ ((h ε hε).and hle).mono fun x hx ↦ hx.1.trans hx.2⟩

/-- Regular subgradients only depend on the function near the point. -/
theorem regularSubdiff_congr {ψ : E → EReal} (h : φ =ᶠ[𝓝 x₀] ψ) :
    regularSubdiff φ x₀ = regularSubdiff ψ x₀ :=
  subset_antisymm (regularSubdiff_subset_of_le (h.mono fun _ hx ↦ hx.le) h.self_of_nhds)
    (regularSubdiff_subset_of_le (h.mono fun _ hx ↦ hx.ge) h.self_of_nhds.symm)

/-- Prop. 1.30(i) of [Mordukhovich 2018], Thm. 16.2 of [Clason–Valkonen] (generalized Fermat
rule): at a local minimizer where `φ` is finite, `0 ∈ ∂̂φ(x₀)`. -/
theorem zero_mem_regularSubdiff_of_isLocalMin (hmin : IsLocalMin φ x₀) (hr : φ x₀ = r) :
    (0 : StrongDual ℝ E) ∈ regularSubdiff φ x₀ := by
  refine ⟨r, hr, fun ε hε ↦ ?_⟩
  filter_upwards [hmin] with x hx
  refine le_trans ?_ (hr ▸ hx)
  exact EReal.coe_le_coe_iff.2 (by
    simp only [zero_apply, add_zero, tsub_le_iff_right, le_add_iff_nonneg_right]; positivity)

/-- The regular subdifferential of the indicator function of `Ω` is the set of `ω`-normals
[Mordukhovich 2018, p. 29]. -/
theorem epsSubdiff_convex_indicator (Ω : Set E) :
    epsSubdiff ω Ω.convex_indicator x₀ = epsNormalCone ω Ω x₀ := by
  ext v
  by_cases hx : x₀ ∈ Ω
  · rw [mem_epsSubdiff_iff (convex_indicator_of_mem hx)]
    simp only [epsNormalCone, mem_ofPred_eq, hx, true_and, eventually_nhdsWithin_iff]
    refine forall₂_congr fun ε hε ↦ eventually_congr (Eventually.of_forall fun x ↦ ?_)
    by_cases hxΩ : x ∈ Ω
    · rw [convex_indicator_of_mem hxΩ, EReal.coe_le_coe_iff, imp_iff_right hxΩ]
      constructor <;> intro h <;> linarith
    · simp [convex_indicator_of_notMem hxΩ, hxΩ]
  · simp [epsSubdiff, epsNormalCone, Set.convex_indicator, hx]

/-- The regular subdifferential of the indicator function of `Ω` is the regular normal cone
[Mordukhovich 2018, p. 29], [Clason–Valkonen, Cor. 18.7]. -/
theorem regularSubdiff_convex_indicator (Ω : Set E) :
    regularSubdiff Ω.convex_indicator x₀ = regularNormalCone Ω x₀ := by
  rw [← epsSubdiff_zero, ← epsNormalCone_zero, epsSubdiff_convex_indicator]

/-- Prop. 1.30(ii) of [Mordukhovich 2018] (sum rule with a differentiable addition):
`v ∈ ∂̂(φ + f)(x₀)` iff `v - f'(x₀) ∈ ∂̂φ(x₀)`. -/
theorem mem_regularSubdiff_add_iff {f : E → ℝ} {f' : StrongDual ℝ E}
    (hf : HasFDerivAt f f' x₀) :
    v ∈ regularSubdiff (fun x ↦ φ x + f x) x₀ ↔ v - f' ∈ regularSubdiff φ x₀ := by
  have hlo := hf.isLittleO
  constructor
  · rintro ⟨s, hs, h⟩
    replace hs : φ x₀ + f x₀ = s := hs
    obtain ⟨r, hr⟩ : ∃ r : ℝ, φ x₀ = r := by
      induction h0 : φ x₀ with
      | bot => simp [h0] at hs
      | top => simp [h0] at hs
      | coe r => exact ⟨r, rfl⟩
    have hsr : s = r + f x₀ := by
      rw [hr, ← EReal.coe_add, EReal.coe_eq_coe_iff] at hs; exact hs.symm
    refine ⟨r, hr, fun ε hε ↦ ?_⟩
    filter_upwards [h (ε / 2) (half_pos hε), hlo.def (half_pos hε)] with x hx hfx
    rw [Real.norm_eq_abs, abs_le] at hfx
    have hx' := coe_le_add_coe_iff.1 hx
    refine le_trans (EReal.coe_le_coe_iff.2 ?_) hx'
    rw [hsr]
    simp only [sub_apply]
    nlinarith [hfx.2, norm_nonneg (x - x₀)]
  · rintro ⟨r, hr, h⟩
    refine ⟨r + f x₀, by simp [hr], fun ε hε ↦ ?_⟩
    filter_upwards [h (ε / 2) (half_pos hε), hlo.def (half_pos hε)] with x hx hfx
    rw [Real.norm_eq_abs, abs_le] at hfx
    show _ ≤ φ x + f x
    rw [coe_le_add_coe_iff]
    refine le_trans (EReal.coe_le_coe_iff.2 ?_) hx
    simp only [sub_apply]
    nlinarith [hfx.1, norm_nonneg (x - x₀)]

/-- For a differentiable function, `∂̂f(x₀) = {f'(x₀)}` [Mordukhovich 2018, p. 28],
[Clason–Valkonen, Thm. 16.4]. -/
theorem regularSubdiff_of_hasFDerivAt {f : E → ℝ} {f' : StrongDual ℝ E}
    (hf : HasFDerivAt f f' x₀) : regularSubdiff (fun x ↦ (f x : EReal)) x₀ = {f'} := by
  have hφ : (fun x ↦ (f x : EReal)) = fun x ↦ ((fun _ ↦ (0 : EReal)) x + f x) := by simp
  ext v
  rw [hφ, mem_regularSubdiff_add_iff hf, mem_singleton_iff, ← sub_eq_zero]
  constructor
  · intro hv
    -- `v - f'` is a regular normal to `univ`, hence zero.
    have hN : v - f' ∈ regularNormalCone (univ : Set E) x₀ := by
      obtain ⟨r, hr, h⟩ := hv
      have hr0 : r = 0 := by simpa using hr.symm
      refine ⟨mem_univ _, fun ε hε ↦ ?_⟩
      rw [nhdsWithin_univ]
      filter_upwards [h ε hε] with x hx
      rw [hr0, EReal.coe_nonpos] at hx
      linarith
    rw [regularNormalCone_of_mem_interior (by simp)] at hN
    exact hN
  · intro hv
    rw [hv]
    exact zero_mem_regularSubdiff_of_isLocalMin isLocalMin_const (r := 0) (by simp)

/-- Thm. 1.27 of [Mordukhovich 2018], first part (smooth variational description of regular
subgradients): `v ∈ ∂̂φ(x₀)` iff there is a function `ψ` differentiable at `x₀` with
`∇ψ(x₀) = v`, `ψ x₀ = φ x₀` and `ψ ≤ φ` near `x₀`. -/
theorem mem_regularSubdiff_iff_exists_support (hr : φ x₀ = r) :
    v ∈ regularSubdiff φ x₀ ↔
      ∃ ψ : E → ℝ, HasFDerivAt ψ v x₀ ∧ ψ x₀ = r ∧ ∀ᶠ x in 𝓝 x₀, (ψ x : EReal) ≤ φ x := by
  constructor
  · intro hv
    rw [mem_regularSubdiff_iff hr] at hv
    classical
    set g : E → ℝ := fun x ↦ r + v (x - x₀)
    set ψ : E → ℝ := fun x ↦ if φ x < g x then (φ x).toReal else g x
    have hψ0 : ψ x₀ = r := by simp [ψ, hr, g]
    refine ⟨ψ, ?_, hψ0, ?_⟩
    · refine HasFDerivAt.of_isLittleO (Asymptotics.IsLittleO.of_bound fun c hc ↦ ?_)
      filter_upwards [hv c hc] with x hx
      rw [hψ0]
      simp only [ψ, g]
      split_ifs with hlt
      · have hbot : φ x ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hx
        have htop : φ x ≠ ⊤ := ne_top_of_lt hlt
        have h1 : r + v (x - x₀) - c * ‖x - x₀‖ ≤ (φ x).toReal := by
          rw [← EReal.coe_le_coe_iff, EReal.coe_toReal htop hbot]; exact hx
        have h2 : (φ x).toReal < r + v (x - x₀) := by
          rw [← EReal.coe_lt_coe_iff, EReal.coe_toReal htop hbot]; exact hlt
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith
      · simpa using mul_nonneg hc.le (norm_nonneg (x - x₀))
    · filter_upwards [hv 1 one_pos] with x hx
      simp only [ψ, g]
      split_ifs with hlt
      · have hbot : φ x ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hx
        rw [EReal.coe_toReal (ne_top_of_lt hlt) hbot]
      · exact not_lt.1 hlt
  · rintro ⟨ψ, hψ, hψr, hle⟩
    refine ⟨r, hr, fun ε hε ↦ ?_⟩
    filter_upwards [hle, hψ.isLittleO.def hε] with x hx hx'
    refine le_trans (EReal.coe_le_coe_iff.2 ?_) hx
    rw [Real.norm_eq_abs, abs_le] at hx'
    rw [hψr] at hx'
    linarith [hx'.1]

section Epigraph

/-- Thm. 1.26 of [Mordukhovich 2018], first inclusion: `ω`-subgradients give `ω`-normals
`(v, -1)` to the epigraph at `(x₀, φ x₀)`. -/
theorem coprod_mem_epsNormalCone_of_mem_epsSubdiff (hω : 0 ≤ ω) (hr : φ x₀ = r)
    (hv : v ∈ epsSubdiff ω φ x₀) :
    v.coprod (-1) ∈ epsNormalCone ω (φ.Epi univ) (x₀, r) := by
  rw [mem_epsSubdiff_iff hr] at hv
  refine ⟨⟨mem_univ _, hr.le⟩, fun ε hε ↦ ?_⟩
  have hfst : Tendsto Prod.fst (𝓝[φ.Epi univ] ((x₀, r) : E × ℝ)) (𝓝 x₀) :=
    (continuous_fst.tendsto _).mono_left nhdsWithin_le_nhds
  filter_upwards [hfst.eventually (hv ε hε), self_mem_nhdsWithin] with p hp hpE
  obtain ⟨x, a⟩ := p
  have h1 : ((r + v (x - x₀) - (ω + ε) * ‖x - x₀‖ : ℝ) : EReal) ≤ a := hp.trans hpE.2
  rw [EReal.coe_le_coe_iff] at h1
  simp only [Prod.mk_sub_mk, ContinuousLinearMap.coprod_apply, neg_apply]
  change v (x - x₀) + -(a - r) ≤ _
  have h2 : ‖x - x₀‖ ≤ ‖((x - x₀, a - r) : E × ℝ)‖ := norm_fst_le ((x - x₀, a - r) : E × ℝ)
  have h3 : 0 ≤ ω + ε := by linarith
  nlinarith

/-- Prop. 1.17 of [Mordukhovich 2018] for regular normals: a regular normal `ℓ` to the epigraph
satisfies `ℓ (0, 1) ≤ 0`. -/
theorem apply_zero_one_nonpos_of_mem_regularNormalCone_epi {p : E × ℝ}
    {ℓ : StrongDual ℝ (E × ℝ)} (hℓ : ℓ ∈ regularNormalCone (φ.Epi univ) p) : ℓ (0, 1) ≤ 0 := by
  have hray : ∀ᶠ t in 𝓝[>] (0 : ℝ), p + t • ((0 : E), (1 : ℝ)) ∈ φ.Epi univ := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    refine ⟨mem_univ _, ?_⟩
    have hp := hℓ.1.2
    simp only [Prod.fst_add, Prod.smul_fst, smul_zero, add_zero, Prod.snd_add, Prod.smul_snd,
      smul_eq_mul, mul_one]
    exact hp.trans (EReal.coe_le_coe_iff.2 (by linarith [show (0 : ℝ) < t from ht]))
  refine le_of_forall_pos_le_add_mul (c := ‖((0 : E), (1 : ℝ))‖) fun ε hε ↦ ?_
  have := le_of_eventually_ray (hℓ.2 ε hε) hray
  linarith

/-- Exercise 1.62 of [Mordukhovich 2018] (slanted regular normals to epigraphs): if `ℓ` is a
regular normal to the epigraph at `(x, α)` with `ℓ (0, 1) < 0`, then `α = φ x`. -/
theorem eq_of_mem_regularNormalCone_epi {x : E} {α : ℝ} {ℓ : StrongDual ℝ (E × ℝ)}
    (hℓ : ℓ ∈ regularNormalCone (φ.Epi univ) (x, α)) (hneg : ℓ (0, 1) < 0) : φ x = α := by
  have hle : φ x ≤ α := hℓ.1.2
  by_contra hne
  obtain ⟨s, hs1, hs2⟩ := EReal.lt_iff_exists_real_btwn.1 (lt_of_le_of_ne hle hne)
  rw [EReal.coe_lt_coe_iff] at hs2
  have hray : ∀ᶠ t in 𝓝[>] (0 : ℝ), (x, α) + t • ((0 : E), (-1 : ℝ)) ∈ φ.Epi univ := by
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hs2)] with t ht
    refine ⟨mem_univ _, ?_⟩
    simp only [Prod.smul_mk, smul_zero, smul_eq_mul, mul_neg, mul_one, Prod.mk_add_mk, add_zero]
    exact hs1.le.trans (EReal.coe_le_coe_iff.2 (by linarith [ht.2]))
  have hd : ℓ ((0 : E), (-1 : ℝ)) = -ℓ (0, 1) := by
    rw [← map_neg]; simp
  have := le_of_eventually_ray (hℓ.2 (-ℓ (0, 1) / 2) (by linarith)) hray
  rw [hd] at this
  simp only [Prod.norm_mk, norm_zero, norm_neg, norm_one, zero_le_one, sup_of_le_right,
    mul_one] at this
  linarith

/-- Thm. 1.26 of [Mordukhovich 2018], converse inclusion: if `0 ≤ ω < 1` and `(v, -1)` is an
`ω`-normal to the epigraph at `(x₀, φ x₀)`, then `v` is an `ω₁`-subgradient with
`ω₁ = ω (1 + ‖v‖) / (1 - ω)`. (The book uses the sum norm on `E × ℝ`; the same `ω₁` works for the
max norm, which is smaller.) -/
theorem mem_epsSubdiff_of_coprod_mem_epsNormalCone {ω : ℝ} (hω0 : 0 ≤ ω) (hω1 : ω < 1)
    (hr : φ x₀ = r) (hN : v.coprod (-1) ∈ epsNormalCone ω (φ.Epi univ) (x₀, r)) :
    v ∈ epsSubdiff (ω * (1 + ‖v‖) / (1 - ω)) φ x₀ := by
  set ω₁ := ω * (1 + ‖v‖) / (1 - ω) with hω₁
  have hω₁0 : 0 ≤ ω₁ := div_nonneg (mul_nonneg hω0 (by positivity)) (by linarith)
  have hω₁eq : ω₁ * (1 - ω) = ω * (1 + ‖v‖) := div_mul_cancel₀ _ (by linarith)
  rw [mem_epsSubdiff_iff hr]
  intro ε hε
  set C : ℝ := 1 + ‖v‖ + ω₁ + ε with hC_def
  have hC : 0 < C := by positivity
  set ε' : ℝ := ε * (1 - ω) / (2 * C) with hε'_def
  have hε' : 0 < ε' := div_pos (mul_pos hε (by linarith)) (by positivity)
  have hkey : (ω + ε') * C < ω₁ + ε := by
    have : ε' * C = ε * (1 - ω) / 2 := by rw [hε'_def]; field_simp
    nlinarith
  set β : E → ℝ := fun x ↦ r + v (x - x₀) - (ω₁ + ε) * ‖x - x₀‖ with hβ_def
  have hβ : Tendsto (fun x ↦ (x, β x)) (𝓝 x₀) (𝓝 (x₀, r)) := by
    have hcont : Continuous fun x ↦ (x, β x) :=
      continuous_id.prodMk ((continuous_const.add (v.continuous.comp
        (continuous_id.sub continuous_const))).sub
        (continuous_const.mul (continuous_id.sub continuous_const).norm))
    simpa [β] using hcont.tendsto x₀
  filter_upwards [hβ.eventually (eventually_nhdsWithin_iff.1 (hN.2 ε' hε'))] with x hx
  by_contra hlt
  rw [not_le] at hlt
  have h := hx ⟨mem_univ _, hlt.le⟩
  simp only [Prod.mk_sub_mk, ContinuousLinearMap.coprod_apply, neg_apply, Prod.norm_mk] at h
  change v (x - x₀) + -(β x - r) ≤ _ at h
  have hβr : β x - r = v (x - x₀) - (ω₁ + ε) * ‖x - x₀‖ := by simp only [hβ_def]; ring
  have hvb : |v (x - x₀)| ≤ ‖v‖ * ‖x - x₀‖ := by
    rw [← Real.norm_eq_abs]; exact v.le_opNorm _
  have hb : ‖β x - r‖ ≤ (‖v‖ + ω₁ + ε) * ‖x - x₀‖ := by
    rw [Real.norm_eq_abs, hβr]
    calc |v (x - x₀) - (ω₁ + ε) * ‖x - x₀‖| ≤ |v (x - x₀)| + |(ω₁ + ε) * ‖x - x₀‖| :=
          abs_sub _ _
      _ ≤ ‖v‖ * ‖x - x₀‖ + (ω₁ + ε) * ‖x - x₀‖ := by
          rw [abs_of_nonneg (mul_nonneg (by linarith) (norm_nonneg _))]; linarith
      _ = (‖v‖ + ω₁ + ε) * ‖x - x₀‖ := by ring
  have hC1 : 1 ≤ C := by rw [hC_def]; linarith [norm_nonneg v]
  have hC2 : ‖v‖ + ω₁ + ε ≤ C := by rw [hC_def]; linarith
  have hmax : max ‖x - x₀‖ ‖β x - r‖ ≤ C * ‖x - x₀‖ :=
    max_le (le_mul_of_one_le_left (norm_nonneg _) hC1)
      (hb.trans (mul_le_mul_of_nonneg_right hC2 (norm_nonneg _)))
  have hlhs : v (x - x₀) + -(β x - r) = (ω₁ + ε) * ‖x - x₀‖ := by rw [hβr]; ring
  rw [hlhs] at h
  have h2 : (ω₁ + ε) * ‖x - x₀‖ ≤ (ω + ε') * C * ‖x - x₀‖ := by
    calc (ω₁ + ε) * ‖x - x₀‖ ≤ (ω + ε') * max ‖x - x₀‖ ‖β x - r‖ := h
      _ ≤ (ω + ε') * (C * ‖x - x₀‖) := by gcongr
      _ = (ω + ε') * C * ‖x - x₀‖ := by ring
  have h0 : ‖x - x₀‖ = 0 := by nlinarith [norm_nonneg (x - x₀)]
  rw [norm_eq_zero, sub_eq_zero] at h0
  subst h0
  rw [hr] at hlt
  simp at hlt

/-- Thm. 1.26, (1.36), of [Mordukhovich 2018] (geometric description of regular subgradients):
`v ∈ ∂̂φ(x₀)` iff `(v, -1)` is a regular normal to the epigraph at `(x₀, φ x₀)`. -/
theorem mem_regularSubdiff_iff_coprod_mem (hr : φ x₀ = r) :
    v ∈ regularSubdiff φ x₀ ↔ v.coprod (-1) ∈ regularNormalCone (φ.Epi univ) (x₀, r) := by
  constructor
  · intro hv
    rw [← epsNormalCone_zero]
    exact coprod_mem_epsNormalCone_of_mem_epsSubdiff le_rfl hr (by rwa [epsSubdiff_zero])
  · intro hN
    have := mem_epsSubdiff_of_coprod_mem_epsNormalCone le_rfl one_pos hr
      (by rwa [epsNormalCone_zero])
    simpa [epsSubdiff_zero] using this

/-- Prop. 1.25 of [Mordukhovich 2018] (`ω`-subgradients of convex functions): if the epigraph
of `φ` is convex and `ω ≥ 0`, then `v ∈ ∂̂_ω φ(x₀)` iff
`⟨v, x - x₀⟩ ≤ φ x - φ x₀ + ω ‖x - x₀‖` for all `x`. -/
theorem mem_epsSubdiff_of_convex {ω : ℝ} (hconv : Convex ℝ (φ.Epi univ)) (hr : φ x₀ = r) :
    v ∈ epsSubdiff ω φ x₀ ↔ ∀ x, ((r + v (x - x₀) - ω * ‖x - x₀‖ : ℝ) : EReal) ≤ φ x := by
  constructor
  · intro hv x
    rw [mem_epsSubdiff_iff hr] at hv
    suffices h : ∀ α : ℝ, φ x ≤ α → r + v (x - x₀) - ω * ‖x - x₀‖ ≤ α by
      induction hφx : φ x with
      | bot =>
        have := h (r + v (x - x₀) - ω * ‖x - x₀‖ - 1) (by rw [hφx]; exact bot_le)
        linarith
      | top => exact le_top
      | coe s => exact EReal.coe_le_coe_iff.2 (h s hφx.le)
    intro α hα
    have hmem₀ : ((x₀, r) : E × ℝ) ∈ φ.Epi univ := ⟨mem_univ _, hr.le⟩
    have hmem : ((x, α) : E × ℝ) ∈ φ.Epi univ := ⟨mem_univ _, hα⟩
    refine le_of_forall_pos_le_add_mul (c := ‖x - x₀‖) fun ε hε ↦ ?_
    have hT : Tendsto (fun t : ℝ ↦ x₀ + t • (x - x₀)) (𝓝[>] 0) (𝓝 x₀) := by
      have : Tendsto (fun t : ℝ ↦ x₀ + t • (x - x₀)) (𝓝 0) (𝓝 (x₀ + (0 : ℝ) • (x - x₀))) :=
        ((continuous_id.smul continuous_const).const_add x₀).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    obtain ⟨t, ht1, ⟨ht0, ht1'⟩⟩ := ((hT.eventually (hv ε hε)).and
      (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos))).exists
    have hconvt := hconv.add_smul_sub_mem hmem₀ hmem ⟨ht0.le, ht1'.le⟩
    have hle : φ (x₀ + t • (x - x₀)) ≤ ((r + t * (α - r) : ℝ) : EReal) := by
      have := hconvt.2
      simpa using this
    have := EReal.coe_le_coe_iff.1 (ht1.trans hle)
    simp only [add_sub_cancel_left, map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht0] at this
    nlinarith
  · intro h
    refine ⟨r, hr, fun ε hε ↦ Eventually.of_forall fun x ↦ le_trans ?_ (h x)⟩
    exact EReal.coe_le_coe_iff.2 (by nlinarith [norm_nonneg (x - x₀)])

/-- Prop. 1.25 of [Mordukhovich 2018] for regular subgradients: if the epigraph of `φ` is
convex, `v ∈ ∂̂φ(x₀)` iff `v` is a subgradient in the sense of convex analysis. -/
theorem mem_regularSubdiff_of_convex (hconv : Convex ℝ (φ.Epi univ)) (hr : φ x₀ = r) :
    v ∈ regularSubdiff φ x₀ ↔ ∀ x, ((r + v (x - x₀) : ℝ) : EReal) ≤ φ x := by
  rw [← epsSubdiff_zero, mem_epsSubdiff_of_convex hconv hr]
  simp

end Epigraph

end VariationalAnalysis
