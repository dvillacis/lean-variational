/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import Mathlib.Analysis.Convex.Continuous
import VariationalAnalysis.Subdifferential.NegConvexHull
import VariationalAnalysis.Subdifferential.Characterizations
import VariationalAnalysis.Subdifferential.SumRule
import VariationalAnalysis.Subdifferential.ProductRule

/-!
# Clarke's generalized directional derivative and generalized gradient

For `f : E → ℝ` we define Clarke's generalized directional derivative
`f°(x₀; v) = limsup_{x → x₀, t ↓ 0} (f(x + t v) - f(x)) / t` [Mordukhovich–Nam 2022, Def. 7.1(a)]
(as an `EReal`-valued upper limit) and the generalized gradient (convexified or Clarke
subdifferential) `∂̄f(x₀) = {ξ | ⟨ξ, v⟩ ≤ f°(x₀; v) for all v}` [Def. 7.21(a)], see also
[Mordukhovich 2018, (1.79)] and [Clason–Valkonen, Ch. 13].

The central result is the representation `∂̄f(x₀) = co ∂f(x₀)` in finite dimensions for `f`
Lipschitz around `x₀` [Mordukhovich–Nam 2022, Thm. 7.69, (7.89)], [Mordukhovich 2018, (1.83)],
[Clason–Valkonen, Thm. 16.10], which links the generalized gradient to the limiting subdifferential
of this library. Most properties of `∂̄f` are then consequences of the calculus of `∂f`.

## Main definitions

* `clarkeDeriv f x₀ v`: the generalized directional derivative `f°(x₀; v)`.
* `clarkeSubdiff f x₀`: the generalized gradient `∂̄f(x₀)`.

## Main results

In normed spaces:
* `convex_clarkeSubdiff`, `isClosed_clarkeSubdiff`: `∂̄f(x₀)` is convex and closed.
* `subdiff_subset_clarkeSubdiff`: `∂f(x₀) ⊆ ∂̄f(x₀)` [Mordukhovich–Nam 2022, Exercise 7.148].
* `clarkeDeriv_neg`, `clarkeSubdiff_neg`: `(-f)°(x₀; v) = f°(x₀; -v)` and `∂̄(-f)(x₀) = -∂̄f(x₀)`
  [Prop. 7.11, (7.54)]; `subdiff_neg_subset_neg_clarkeSubdiff`: `∂(-f)(x₀) ⊆ -∂̄f(x₀)`.
* `zero_mem_clarkeSubdiff_of_isLocalMin`, `zero_mem_clarkeSubdiff_of_isLocalMax`: Fermat's rule
  for local minima and maxima.

In finite dimensions, for `f` Lipschitz around `x₀`:
* `clarkeDeriv_eq_iSup`, `clarkeDeriv_eq_iSup_clarkeSubdiff`, `exists_mem_clarkeSubdiff_eq`:
  `f°(x₀; v) = max {⟨ξ, v⟩ | ξ ∈ ∂̄f(x₀)} = sup {⟨w, v⟩ | w ∈ ∂f(x₀)}` [Thm. 7.31, (7.91)].
* `clarkeSubdiff_eq_convexHull`: `∂̄f(x₀) = co ∂f(x₀)` [Thm. 7.69].
* `clarkeSubdiff_nonempty`, `isCompact_clarkeSubdiff`, `norm_le_of_mem_clarkeSubdiff`:
  `∂̄f(x₀)` is nonempty, compact and bounded by the Lipschitz constant [Thm. 7.24];
  `clarkeDeriv_le_mul_norm`, `neg_mul_norm_le_clarkeDeriv` [Prop. 7.8].
* `clarkeDeriv_add_le`, `clarkeDeriv_smul`: `f°(x₀; ·)` is subadditive and positively
  homogeneous [Prop. 7.8, Thm. 7.10].
* `clarkeSubdiff_eq_singleton_of_hasStrictFDerivAt`: `∂̄f(x₀) = {∇f(x₀)}` for strictly
  differentiable `f` [Prop. 7.5].
* `clarkeSubdiff_eq_of_convexOn`: for convex `f`, `∂̄f(x₀)` is the subdifferential of convex
  analysis.
* `clarkeSubdiff_add_subset`, `clarkeSubdiff_const_mul`: the sum rule
  `∂̄(f + g)(x₀) ⊆ ∂̄f(x₀) + ∂̄g(x₀)` [Thm. 7.32, (7.44)] and `∂̄(t f)(x₀) = t ∂̄f(x₀)` [(7.54)].
* `clarkeSubdiff_add_eq_of_hasStrictFDerivAt`: `∂̄(f + g)(x₀) = ∇f(x₀) + ∂̄g(x₀)` for `f`
  strictly differentiable and `g` Lipschitz.
* `clarkeSubdiff_comp_fst`, `clarkeSubdiff_sub_comp_fst`: `∂̄(ψ ∘ fst)(x, y) = ∂̄ψ(x) × {0}` and
  `∂̄(φ - μ ∘ fst)(p) = ∇φ(p) - ∂̄μ(p.1) × {0}`.

## Implementation notes

`f°(x₀; v)` is an upper limit in `EReal`, so it is defined for every `f`; for `f` Lipschitz around
`x₀` it is finite (`clarkeDeriv_le_mul_norm`, `neg_mul_norm_le_clarkeDeriv`). The book proves the
properties of `f°` directly and derives `∂̄f(x₀) ≠ ∅` from the Hahn–Banach theorem; here, in finite
dimensions, everything is obtained from the representation of `f°` through `∂f`, which combines
`∂f ⊆ ∂̄f` with the mean value inequality [Mordukhovich 2018, Cor. 4.14(ii)] and robustness of
`∂f` (`eventually_forall_mem_subdiff_apply_le`).
-/

open Filter Topology Set Metric
open scoped NNReal Pointwise

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Clarke's generalized directional derivative
`f°(x₀; v) = limsup_{x → x₀, t ↓ 0} (f(x + t v) - f(x)) / t`
[Mordukhovich–Nam 2022, Def. 7.1(a)], [Dempe 2002, Def. 4.12]. -/
noncomputable def clarkeDeriv (f : E → ℝ) (x₀ v : E) : EReal :=
  limsup (fun p : E × ℝ ↦ (((f (p.1 + p.2 • v) - f p.1) / p.2 : ℝ) : EReal)) (𝓝 x₀ ×ˢ 𝓝[>] 0)

/-- Clarke's generalized gradient `∂̄f(x₀) = {ξ | ⟨ξ, v⟩ ≤ f°(x₀; v) for all v}`
[Mordukhovich–Nam 2022, Def. 7.21(a)]. -/
def clarkeSubdiff (f : E → ℝ) (x₀ : E) : Set (StrongDual ℝ E) :=
  {ξ | ∀ v, (ξ v : EReal) ≤ clarkeDeriv f x₀ v}

variable {f g : E → ℝ} {x₀ : E}

theorem mem_clarkeSubdiff_iff {ξ : StrongDual ℝ E} :
    ξ ∈ clarkeSubdiff f x₀ ↔ ∀ v, (ξ v : EReal) ≤ clarkeDeriv f x₀ v :=
  Iff.rfl

/-! ### Normed spaces -/

section Normed

theorem convex_setOf_coe_apply_le (v : E) (c : EReal) :
    Convex ℝ {ξ : StrongDual ℝ E | (ξ v : EReal) ≤ c} := by
  induction c with
  | bot => simp; exact convex_empty
  | top => simp; exact convex_univ
  | coe c =>
    intro a ha b hb s t hs ht hst
    simp only [mem_ofPred_eq, EReal.coe_le_coe_iff, add_apply, smul_apply, smul_eq_mul] at ha hb ⊢
    have e : s * c + t * c = c := by rw [← add_mul, hst, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left ha hs, mul_le_mul_of_nonneg_left hb ht]

theorem isClosed_setOf_coe_apply_le (v : E) (c : EReal) :
    IsClosed {ξ : StrongDual ℝ E | (ξ v : EReal) ≤ c} := by
  induction c with
  | bot => simp
  | top => simp
  | coe c =>
    simp only [EReal.coe_le_coe_iff]
    exact isClosed_le (continuous_id.clm_apply continuous_const) continuous_const

theorem clarkeSubdiff_eq_iInter :
    clarkeSubdiff f x₀ = ⋂ v, {ξ : StrongDual ℝ E | (ξ v : EReal) ≤ clarkeDeriv f x₀ v} := by
  ext ξ
  simp [clarkeSubdiff]

/-- `∂̄f(x₀)` is convex [Mordukhovich–Nam 2022, Thm. 7.24]. -/
theorem convex_clarkeSubdiff : Convex ℝ (clarkeSubdiff f x₀) := by
  rw [clarkeSubdiff_eq_iInter]
  exact convex_iInter fun v ↦ convex_setOf_coe_apply_le v _

/-- `∂̄f(x₀)` is closed [Mordukhovich–Nam 2022, Thm. 7.24]. -/
theorem isClosed_clarkeSubdiff : IsClosed (clarkeSubdiff f x₀) := by
  rw [clarkeSubdiff_eq_iInter]
  exact isClosed_iInter fun v ↦ isClosed_setOf_coe_apply_le v _

/-- Basic subgradients are generalized gradients: `∂f(x₀) ⊆ ∂̄f(x₀)`
[Mordukhovich–Nam 2022, Exercise 7.148]. If `u ∈ ∂f(x₀)` is the limit of regular subgradients
`wₖ ∈ ∂̂f(xₖ)`, `xₖ → x₀`, the regular subgradient inequality along `xₖ + t v` gives difference
quotients at `(xₖ, tₖ)`, `tₖ ↓ 0`, bounded below by `⟨wₖ, v⟩ - εₖ ‖v‖ → ⟨u, v⟩`. -/
theorem subdiff_subset_clarkeSubdiff :
    subdiff (fun x ↦ (f x : EReal)) x₀ ⊆ clarkeSubdiff f x₀ := by
  intro u hu v
  have hη : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k ↦ by positivity
  choose x w hw hx _ hwu using fun k ↦
    exists_regularSubdiff_near_of_mem_subdiff (ψ := fun x ↦ (f x : EReal)) rfl hu (hη k)
  have hstep : ∀ k : ℕ, ∃ t : ℝ, 0 < t ∧ t < 1 / ((k : ℝ) + 1) ∧
      w k v - 1 / ((k : ℝ) + 1) * ‖v‖ ≤ (f (x k + t • v) - f (x k)) / t := by
    intro k
    have hreg := mem_regularSubdiff_coe.1 (hw k) _ (hη k)
    have hline : Tendsto (fun t : ℝ ↦ x k + t • v) (𝓝[>] 0) (𝓝 (x k)) := by
      have : Tendsto (fun t : ℝ ↦ x k + t • v) (𝓝 0) (𝓝 (x k + (0 : ℝ) • v)) :=
        (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    obtain ⟨t, ht, ht1⟩ := ((hline.eventually hreg).and (Ioo_mem_nhdsGT (hη k))).exists
    refine ⟨t, ht1.1, ht1.2, ?_⟩
    simp only [add_sub_cancel_left, map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht1.1] at ht
    rw [le_div_iff₀ ht1.1]
    nlinarith
  choose t ht0 ht1 hq using hstep
  have h0 : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hx' : Tendsto x atTop (𝓝 x₀) := by
    have : Tendsto (fun k ↦ x k - x₀) atTop (𝓝 0) := squeeze_zero_norm (fun k ↦ (hx k).le) h0
    simpa using this.add_const x₀
  have ht' : Tendsto t atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨squeeze_zero (fun k ↦ (ht0 k).le) (fun k ↦ (ht1 k).le) h0,
      Eventually.of_forall ht0⟩
  have hp : Tendsto (fun k ↦ (x k, t k)) atTop (𝓝 x₀ ×ˢ 𝓝[>] 0) := hx'.prodMk ht'
  have hw' : Tendsto w atTop (𝓝 u) := by
    have : Tendsto (fun k ↦ w k - u) atTop (𝓝 0) := squeeze_zero_norm (fun k ↦ (hwu k).le) h0
    simpa using this.add_const u
  have hlow : Tendsto (fun k ↦ w k v - 1 / ((k : ℝ) + 1) * ‖v‖) atTop (𝓝 (u v)) := by
    have := (tendsto_dual_apply hw'
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ v) atTop (𝓝 v))).sub (h0.mul_const ‖v‖)
    simpa using this
  refine le_of_forall_lt_imp_le_of_dense fun c hc ↦ ?_
  obtain ⟨b, hcb, hbu⟩ := EReal.lt_iff_exists_real_btwn.1 hc
  unfold clarkeDeriv
  refine hcb.le.trans (le_limsup_of_frequently_le (hp.frequently (Eventually.frequently ?_)))
  filter_upwards [hlow.eventually (eventually_gt_nhds (EReal.coe_lt_coe_iff.1 hbu))] with k hk
  exact EReal.coe_le_coe_iff.2 (hk.le.trans (hq k))

theorem regularSubdiff_subset_clarkeSubdiff :
    regularSubdiff (fun x ↦ (f x : EReal)) x₀ ⊆ clarkeSubdiff f x₀ :=
  regularSubdiff_subset_subdiff.trans subdiff_subset_clarkeSubdiff

/-- `(x, t) ↦ (x + t w, t)` maps `𝓝 x₀ ×ˢ 𝓝[>] 0` into itself. -/
theorem tendsto_add_smul_prod (w : E) :
    Tendsto (fun p : E × ℝ ↦ (p.1 + p.2 • w, p.2)) (𝓝 x₀ ×ˢ 𝓝[>] 0) (𝓝 x₀ ×ˢ 𝓝[>] 0) := by
  have hF : (𝓝 x₀ ×ˢ 𝓝[>] (0 : ℝ)) = 𝓝[univ ×ˢ Ioi 0] (x₀, (0 : ℝ)) := by
    rw [nhdsWithin_prod_eq, nhdsWithin_univ]
  rw [hF]
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun p hp ↦
    ⟨mem_univ _, hp.2⟩⟩
  have hc : Continuous fun p : E × ℝ ↦ (p.1 + p.2 • w, p.2) := by fun_prop
  have := (hc.tendsto (x₀, (0 : ℝ))).mono_left (nhdsWithin_le_nhds (s := univ ×ˢ Ioi 0))
  simpa using this

/-- The symmetry `(-f)°(x₀; v) = f°(x₀; -v)` [Mordukhovich–Nam 2022, Prop. 7.11]. -/
theorem clarkeDeriv_neg (v : E) : clarkeDeriv (fun x ↦ -f x) x₀ v = clarkeDeriv f x₀ (-v) := by
  let T : E × ℝ → E × ℝ := fun p ↦ (p.1 + p.2 • v, p.2)
  have hTS : (T ∘ fun p : E × ℝ ↦ (p.1 + p.2 • (-v), p.2)) = id := by
    funext p
    simp [T]
  have hmap : map T (𝓝 x₀ ×ˢ 𝓝[>] 0) = 𝓝 x₀ ×ˢ 𝓝[>] 0 :=
    le_antisymm (tendsto_add_smul_prod v) (by
      calc 𝓝 x₀ ×ˢ 𝓝[>] 0
          = map T (map (fun p : E × ℝ ↦ (p.1 + p.2 • (-v), p.2)) (𝓝 x₀ ×ˢ 𝓝[>] 0)) := by
            rw [map_map, hTS, map_id]
        _ ≤ map T (𝓝 x₀ ×ˢ 𝓝[>] 0) := map_mono (tendsto_add_smul_prod (-v)))
  unfold clarkeDeriv
  conv_rhs => rw [← hmap, ← limsup_comp]
  congr 1
  funext p
  simp only [Function.comp_apply, T, smul_neg, add_neg_cancel_right]
  congr 1
  ring

/-- `∂̄(-f)(x₀) = -∂̄f(x₀)` [Mordukhovich–Nam 2022, (7.54)]. -/
theorem clarkeSubdiff_neg : clarkeSubdiff (fun x ↦ -f x) x₀ = -clarkeSubdiff f x₀ := by
  ext ξ
  rw [Set.mem_neg]
  show (∀ v, (ξ v : EReal) ≤ clarkeDeriv (fun x ↦ -f x) x₀ v) ↔
    ∀ v, ((-ξ) v : EReal) ≤ clarkeDeriv f x₀ v
  simp only [clarkeDeriv_neg, neg_apply]
  refine ⟨fun h v ↦ ?_, fun h v ↦ ?_⟩
  · simpa using h (-v)
  · simpa using h (-v)

/-- `∂(-f)(x₀) ⊆ -∂̄f(x₀)`: with `clarkeSubdiff_eq_convexHull` this is
`neg_mem_convexHull_subdiff_of_mem_subdiff_neg`. -/
theorem subdiff_neg_subset_neg_clarkeSubdiff :
    subdiff (fun x ↦ ((-f x : ℝ) : EReal)) x₀ ⊆ -clarkeSubdiff f x₀ :=
  clarkeSubdiff_neg (f := f) ▸ subdiff_subset_clarkeSubdiff

/-- Fermat's rule for the generalized gradient at local minima. -/
theorem zero_mem_clarkeSubdiff_of_isLocalMin (h : IsLocalMin f x₀) :
    (0 : StrongDual ℝ E) ∈ clarkeSubdiff f x₀ :=
  subdiff_subset_clarkeSubdiff (zero_mem_subdiff_of_isLocalMin (φ := fun x ↦ (f x : EReal))
    (h.comp_mono EReal.coe_strictMono.monotone) rfl)

/-- Fermat's rule for the generalized gradient at local maxima (by the symmetry
`∂̄(-f) = -∂̄f`; this fails for the limiting subdifferential, e.g. for `-|x|`). -/
theorem zero_mem_clarkeSubdiff_of_isLocalMax (h : IsLocalMax f x₀) :
    (0 : StrongDual ℝ E) ∈ clarkeSubdiff f x₀ := by
  have := zero_mem_clarkeSubdiff_of_isLocalMin (f := fun x ↦ -f x) h.neg
  rwa [clarkeSubdiff_neg, Set.mem_neg, neg_zero] at this

theorem clarkeDeriv_zero : clarkeDeriv f x₀ 0 = 0 := by
  simp only [clarkeDeriv, smul_zero, add_zero, sub_self, zero_div, EReal.coe_zero]
  exact limsup_const 0

omit [NormedSpace ℝ E] in
theorem lipschitzOnWith_neg {U : Set E} {K : ℝ≥0} (hf : LipschitzOnWith K f U) :
    LipschitzOnWith K (fun x ↦ -f x) U :=
  LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ by
    rw [dist_neg_neg]
    exact hf.dist_le_mul x hx y hy

end Normed

section Projection

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `(ψ ∘ fst)°((x, y); v) = ψ°(x; v.1)`. -/
theorem clarkeDeriv_comp_fst (ψ : E → ℝ) (p v : E × F) :
    clarkeDeriv (fun q : E × F ↦ ψ q.1) p v = clarkeDeriv ψ p.1 v.1 := by
  have hfun : (fun q : (E × F) × ℝ ↦ (((ψ (q.1 + q.2 • v).1 - ψ q.1.1) / q.2 : ℝ) : EReal)) =
      (fun r : E × ℝ ↦ (((ψ (r.1 + r.2 • v.1) - ψ r.1) / r.2 : ℝ) : EReal)) ∘
        fun q ↦ (q.1.1, q.2) := by
    funext q
    simp
  have hmap : map (fun q : (E × F) × ℝ ↦ (q.1.1, q.2)) (𝓝 p ×ˢ 𝓝[>] 0) =
      𝓝 p.1 ×ˢ 𝓝[>] (0 : ℝ) := by
    have := (prod_map_map_eq (f₁ := 𝓝 p) (f₂ := 𝓝[>] (0 : ℝ)) (m₁ := Prod.fst)
      (m₂ := id)).symm
    rwa [map_fst_nhds, map_id] at this
  unfold clarkeDeriv
  rw [hfun, limsup_comp, hmap]

/-- The generalized gradient of `ψ ∘ fst` is `∂̄ψ × {0}`. -/
theorem clarkeSubdiff_comp_fst (ψ : E → ℝ) (p : E × F) :
    clarkeSubdiff (fun q : E × F ↦ ψ q.1) p =
      (fun u : StrongDual ℝ E ↦ u.comp (ContinuousLinearMap.fst ℝ E F)) '' clarkeSubdiff ψ p.1 := by
  ext ξ
  simp only [clarkeSubdiff, mem_ofPred_eq, mem_image, clarkeDeriv_comp_fst]
  constructor
  · intro h
    have h0 : ∀ w : F, ξ (0, w) = 0 := fun w ↦ by
      have h1 := h (0, w)
      have h2 := h (0, -w)
      simp only [clarkeDeriv_zero, EReal.coe_nonpos] at h1 h2
      have : ξ (0, -w) = -ξ (0, w) := by rw [← map_neg]; simp
      linarith
    refine ⟨ξ.comp (ContinuousLinearMap.inl ℝ E F), fun w ↦ by simpa using h (w, 0), ?_⟩
    refine ContinuousLinearMap.ext fun v ↦ ?_
    have hv : ξ v = ξ (v.1, 0) + ξ (0, v.2) := by rw [← map_add]; simp
    simp [hv, h0]
  · rintro ⟨u, hu, rfl⟩ v
    simpa using hu v.1

end Projection

/-! ### Finite dimensions -/

section FiniteDimensional

variable [FiniteDimensional ℝ E] {U V : Set E} {L K : ℝ≥0}

/-- Robustness of basic subgradients of a function Lipschitz around `x₀`: a strict bound
`⟨w, v⟩ < a` on `∂f(x₀)` gives `⟨w, v⟩ ≤ a` on `∂f(c)` for `c` near `x₀`. -/
theorem eventually_forall_mem_subdiff_apply_le (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U)
    {v : E} {a : ℝ} (ha : ∀ w ∈ subdiff (fun x ↦ (f x : EReal)) x₀, w v < a) :
    ∀ᶠ c in 𝓝 x₀, ∀ w ∈ subdiff (fun x ↦ (f x : EReal)) c, w v ≤ a := by
  obtain ⟨ρ₀, hρ₀, hB⟩ := Metric.mem_nhds_iff.1 hU
  have hLB : LipschitzOnWith L f (ball x₀ ρ₀) := hL.mono hB
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨c, hc, hcP⟩ := exists_seq_forall_of_frequently hcon
  simp only [not_forall, not_le, exists_prop] at hcP
  choose w hw hwd using hcP
  have hM : ∀ᶠ k in atTop, ‖w k‖ ≤ L := by
    filter_upwards [hc.eventually (isOpen_ball.mem_nhds (mem_ball_self hρ₀))] with k hk
    exact norm_le_of_mem_subdiff_of_lipschitz (isOpen_ball.mem_nhds hk) hLB (hw k)
  obtain ⟨w₀, -, ψ, hψ, hwψ⟩ := tendsto_subseq_of_frequently_bounded
    (isBounded_closedBall (x := (0 : StrongDual ℝ E)) (r := L))
    (hM.mono fun k hk ↦ mem_closedBall_zero_iff.2 hk).frequently
  have hmem := mem_subdiff_of_tendsto (hL.continuousOn.continuousAt hU)
    (hc.comp hψ.tendsto_atTop) hwψ fun k ↦ hw (ψ k)
  have hlim : Tendsto (fun k ↦ w (ψ k) v) atTop (𝓝 (w₀ v)) :=
    tendsto_dual_apply hwψ tendsto_const_nhds
  have := ge_of_tendsto hlim (Eventually.of_forall fun k ↦ (hwd (ψ k)).le)
  linarith [ha w₀ hmem]

/-- If `⟨w, v⟩ < a` for all `w ∈ ∂f(x₀)`, then `f°(x₀; v) ≤ a`: by the mean value inequality
[Mordukhovich 2018, Cor. 4.14(ii)], `f(x + t v) - f(x) ≤ t ⟨w, v⟩` for some `w ∈ ∂f(c)`,
`c ∈ [x, x + t v]`, and `⟨w, v⟩ ≤ a` for `c` near `x₀` by robustness. -/
theorem clarkeDeriv_le_of_forall_mem_subdiff (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U)
    {v : E} {a : ℝ} (ha : ∀ w ∈ subdiff (fun x ↦ (f x : EReal)) x₀, w v < a) :
    clarkeDeriv f x₀ v ≤ a := by
  obtain ⟨ρ₁, hρ₁, hA⟩ :=
    Metric.eventually_nhds_iff.1 (eventually_forall_mem_subdiff_apply_le hU hL ha)
  obtain ⟨ρ₀, hρ₀, hB⟩ := Metric.mem_nhds_iff.1 hU
  set ρ := min ρ₁ ρ₀
  have hρ : 0 < ρ := lt_min hρ₁ hρ₀
  have hLB : LipschitzOnWith L f (ball x₀ ρ) :=
    hL.mono ((ball_subset_ball (min_le_right _ _)).trans hB)
  have h1 : ∀ᶠ p : E × ℝ in 𝓝 x₀ ×ˢ 𝓝[>] 0, p.1 ∈ ball x₀ (ρ / 2) :=
    tendsto_fst.eventually (ball_mem_nhds x₀ (half_pos hρ))
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖t • v‖ < ρ / 2 := by
    have : Tendsto (fun t : ℝ ↦ t • v) (𝓝 0) (𝓝 ((0 : ℝ) • v)) :=
      (continuous_id.smul continuous_const).tendsto 0
    rw [zero_smul] at this
    exact (this.mono_left nhdsWithin_le_nhds).norm.eventually
      (gt_mem_nhds (by rw [norm_zero]; positivity))
  have h2 : ∀ᶠ p : E × ℝ in 𝓝 x₀ ×ˢ 𝓝[>] 0, 0 < p.2 ∧ ‖p.2 • v‖ < ρ / 2 :=
    tendsto_snd.eventually ((eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)).and hsmall)
  unfold clarkeDeriv
  refine limsup_le_of_le (h := ?_)
  filter_upwards [h1, h2] with p hp1 hp2
  obtain ⟨y, t⟩ := p
  obtain ⟨ht, htv⟩ := hp2
  simp only at hp1 ht htv ⊢
  have hyB : y ∈ ball x₀ ρ := ball_subset_ball (half_le_self hρ.le) hp1
  have hytB : y + t • v ∈ ball x₀ ρ := by
    rw [mem_ball, dist_eq_norm, add_sub_right_comm]
    rw [mem_ball, dist_eq_norm] at hp1
    calc ‖y - x₀ + t • v‖ ≤ ‖y - x₀‖ + ‖t • v‖ := norm_add_le _ _
      _ < ρ := by linarith
  have hseg : segment ℝ y (y + t • v) ⊆ ball x₀ ρ := (convex_ball x₀ ρ).segment_subset hyB hytB
  obtain ⟨τ, hτ, w, hw, hmv⟩ := exists_mem_subdiff_mean_value_of_lipschitz isOpen_ball hseg hLB
  have hcB : y + τ • (y + t • v - y) ∈ ball x₀ ρ := hseg (add_smul_sub_mem_segment hτ.1 hτ.2.le)
  have hwv : w v ≤ a := hA (lt_of_lt_of_le (mem_ball.1 hcB) (min_le_left _ _)) w hw
  rw [add_sub_cancel_left, map_smul, smul_eq_mul] at hmv
  rw [EReal.coe_le_coe_iff, div_le_iff₀ ht]
  nlinarith

/-- `f°(x₀; v) = sup {⟨w, v⟩ | w ∈ ∂f(x₀)}` [Mordukhovich–Nam 2022, (7.91)]. -/
theorem clarkeDeriv_eq_iSup (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U) (v : E) :
    clarkeDeriv f x₀ v = ⨆ w ∈ subdiff (fun x ↦ (f x : EReal)) x₀, (w v : EReal) := by
  refine le_antisymm ?_ (iSup₂_le fun w hw ↦ subdiff_subset_clarkeSubdiff hw v)
  refine EReal.le_of_forall_lt_iff_le.1 fun a ha ↦ ?_
  refine (clarkeDeriv_le_of_forall_mem_subdiff hU hL fun w hw ↦ ?_)
  exact EReal.coe_lt_coe_iff.1 ((le_iSup₂ (f := fun w _ ↦ (w v : EReal)) w hw).trans_lt ha)

/-- Thm. 7.69 of [Mordukhovich–Nam 2022] (see also [Mordukhovich 2018, (1.83)],
[Clason–Valkonen, Thm. 16.10]): for `f` Lipschitz around `x₀` in finite dimensions,
`∂̄f(x₀) = co ∂f(x₀)`. -/
theorem clarkeSubdiff_eq_convexHull (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U) :
    clarkeSubdiff f x₀ = convexHull ℝ (subdiff (fun x ↦ (f x : EReal)) x₀) := by
  refine subset_antisymm (fun ξ hξ ↦ ?_)
    (convexHull_min subdiff_subset_clarkeSubdiff convex_clarkeSubdiff)
  have hC := isCompact_convexHull_of_isCompact (isCompact_subdiff_of_lipschitz hU hL)
  by_contra hnot
  obtain ⟨Φ, a, hΦξ, hΦC⟩ :=
    geometric_hahn_banach_point_closed (convex_convexHull ℝ _) hC.isClosed hnot
  obtain ⟨d, rfl⟩ := inclusionInDoubleDual_surjective Φ
  simp only [NormedSpace.dual_def] at hΦξ hΦC
  have h1 : clarkeDeriv f x₀ (-d) ≤ ((-a : ℝ) : EReal) :=
    clarkeDeriv_le_of_forall_mem_subdiff hU hL fun w hw ↦ by
      have := hΦC w (subset_convexHull ℝ _ hw)
      rw [map_neg]
      linarith
  have h2 := (hξ (-d)).trans h1
  rw [EReal.coe_le_coe_iff, map_neg] at h2
  linarith

/-- `∂̄f(x₀)` is nonempty [Mordukhovich–Nam 2022, Thm. 7.24]. -/
theorem clarkeSubdiff_nonempty (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U) :
    (clarkeSubdiff f x₀).Nonempty :=
  (subdiff_nonempty_of_lipschitz hU hL).mono subdiff_subset_clarkeSubdiff

/-- `∂̄f(x₀)` is compact [Mordukhovich–Nam 2022, Thm. 7.24]. -/
theorem isCompact_clarkeSubdiff (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U) :
    IsCompact (clarkeSubdiff f x₀) := by
  rw [clarkeSubdiff_eq_convexHull hU hL]
  exact isCompact_convexHull_of_isCompact (isCompact_subdiff_of_lipschitz hU hL)

/-- (7.36) of [Mordukhovich–Nam 2022]: generalized gradients are bounded by the Lipschitz
constant. -/
theorem norm_le_of_mem_clarkeSubdiff (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U)
    {ξ : StrongDual ℝ E} (hξ : ξ ∈ clarkeSubdiff f x₀) : ‖ξ‖ ≤ L := by
  rw [clarkeSubdiff_eq_convexHull hU hL] at hξ
  have h : convexHull ℝ (subdiff (fun x ↦ (f x : EReal)) x₀) ⊆ closedBall 0 L :=
    convexHull_min (fun w hw ↦ mem_closedBall_zero_iff.2
      (norm_le_of_mem_subdiff_of_lipschitz hU hL hw)) (convex_closedBall 0 L)
  simpa using h hξ

/-- Thm. 7.31 of [Mordukhovich–Nam 2022] (full duality):
`f°(x₀; v) = sup {⟨ξ, v⟩ | ξ ∈ ∂̄f(x₀)}`. -/
theorem clarkeDeriv_eq_iSup_clarkeSubdiff (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U) (v : E) :
    clarkeDeriv f x₀ v = ⨆ ξ ∈ clarkeSubdiff f x₀, (ξ v : EReal) :=
  le_antisymm ((clarkeDeriv_eq_iSup hU hL v).trans_le
    (biSup_mono fun _ hw ↦ subdiff_subset_clarkeSubdiff hw)) (iSup₂_le fun _ hξ ↦ hξ v)

/-- The supremum in `clarkeDeriv_eq_iSup` is attained, at a basic subgradient. -/
theorem exists_mem_subdiff_eq_clarkeDeriv (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U) (v : E) :
    ∃ w ∈ subdiff (fun x ↦ (f x : EReal)) x₀, (w v : EReal) = clarkeDeriv f x₀ v := by
  obtain ⟨w, hw, hmax⟩ := (isCompact_subdiff_of_lipschitz hU hL).exists_isMaxOn
    (subdiff_nonempty_of_lipschitz hU hL)
    (continuous_id.clm_apply (continuous_const (y := v))).continuousOn
  refine ⟨w, hw, le_antisymm (subdiff_subset_clarkeSubdiff hw v) ?_⟩
  rw [clarkeDeriv_eq_iSup hU hL v]
  exact iSup₂_le fun w' hw' ↦ EReal.coe_le_coe_iff.2 (hmax hw')

/-- Thm. 7.31 of [Mordukhovich–Nam 2022]: `f°(x₀; v) = max {⟨ξ, v⟩ | ξ ∈ ∂̄f(x₀)}`. -/
theorem exists_mem_clarkeSubdiff_eq (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U) (v : E) :
    ∃ ξ ∈ clarkeSubdiff f x₀, (ξ v : EReal) = clarkeDeriv f x₀ v :=
  let ⟨w, hw, h⟩ := exists_mem_subdiff_eq_clarkeDeriv hU hL v
  ⟨w, subdiff_subset_clarkeSubdiff hw, h⟩

/-- Prop. 7.8 of [Mordukhovich–Nam 2022]: `f°(x₀; v) ≤ L ‖v‖`. -/
theorem clarkeDeriv_le_mul_norm (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U) (v : E) :
    clarkeDeriv f x₀ v ≤ ((L * ‖v‖ : ℝ) : EReal) := by
  rw [clarkeDeriv_eq_iSup hU hL v]
  refine iSup₂_le fun w hw ↦ EReal.coe_le_coe_iff.2 ?_
  exact (w.le_opNorm v).trans' (le_abs_self _) |>.trans
    (mul_le_mul_of_nonneg_right (norm_le_of_mem_subdiff_of_lipschitz hU hL hw) (norm_nonneg v))

/-- Prop. 7.8 of [Mordukhovich–Nam 2022]: `-L ‖v‖ ≤ f°(x₀; v)`. -/
theorem neg_mul_norm_le_clarkeDeriv (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U) (v : E) :
    ((-(L * ‖v‖) : ℝ) : EReal) ≤ clarkeDeriv f x₀ v := by
  obtain ⟨w, hw⟩ := subdiff_nonempty_of_lipschitz hU hL
  refine le_trans (EReal.coe_le_coe_iff.2 ?_) (subdiff_subset_clarkeSubdiff hw v)
  have h1 := neg_abs_le (w v)
  have h2 := (w.le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (norm_le_of_mem_subdiff_of_lipschitz hU hL hw) (norm_nonneg v))
  rw [Real.norm_eq_abs] at h2
  linarith

/-- Thm. 7.10 of [Mordukhovich–Nam 2022]: `f°(x₀; ·)` is subadditive. -/
theorem clarkeDeriv_add_le (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U) (v₁ v₂ : E) :
    clarkeDeriv f x₀ (v₁ + v₂) ≤ clarkeDeriv f x₀ v₁ + clarkeDeriv f x₀ v₂ := by
  rw [clarkeDeriv_eq_iSup hU hL (v₁ + v₂)]
  refine iSup₂_le fun w hw ↦ ?_
  rw [map_add, EReal.coe_add]
  exact add_le_add (subdiff_subset_clarkeSubdiff hw v₁) (subdiff_subset_clarkeSubdiff hw v₂)

/-- Prop. 7.8 of [Mordukhovich–Nam 2022]: `f°(x₀; ·)` is positively homogeneous. -/
theorem clarkeDeriv_smul (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U) {t : ℝ} (ht : 0 ≤ t)
    (v : E) : clarkeDeriv f x₀ (t • v) = (t : EReal) * clarkeDeriv f x₀ v := by
  obtain ⟨ξ₀, hξ₀, h₀⟩ := exists_mem_clarkeSubdiff_eq hU hL v
  obtain ⟨ξ₁, hξ₁, h₁⟩ := exists_mem_clarkeSubdiff_eq hU hL (t • v)
  rw [← h₀, ← h₁, ← EReal.coe_mul, EReal.coe_eq_coe_iff, map_smul, smul_eq_mul]
  have a1 : ξ₁ v ≤ ξ₀ v := EReal.coe_le_coe_iff.1 ((hξ₁ v).trans h₀.ge)
  have a2 : ξ₀ (t • v) ≤ ξ₁ (t • v) := EReal.coe_le_coe_iff.1 ((hξ₀ (t • v)).trans h₁.ge)
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at a2
  nlinarith

/-- Prop. 7.5 of [Mordukhovich–Nam 2022]: `∂̄f(x₀) = {∇f(x₀)}` for `f` strictly differentiable at
`x₀`. -/
theorem clarkeSubdiff_eq_singleton_of_hasStrictFDerivAt {f' : StrongDual ℝ E}
    (hf : HasStrictFDerivAt f f' x₀) : clarkeSubdiff f x₀ = {f'} := by
  obtain ⟨K, U, hU, hL⟩ := hf.exists_lipschitzOnWith
  rw [clarkeSubdiff_eq_convexHull hU hL]
  have h := (strictDifferentiability_tfae (φ := fun x ↦ (f x : EReal)) (x₀ := x₀)
    (x' := f')).out 2 1
  rw [(h.1 ⟨f, Eventually.of_forall fun _ ↦ rfl, hf⟩).2, convexHull_singleton]

/-- For a convex function, the generalized gradient is the subdifferential of convex analysis
[Mordukhovich–Nam 2022, after Def. 7.21, and Prop. 7.4]. -/
theorem clarkeSubdiff_eq_of_convexOn (hf : ConvexOn ℝ univ f) :
    clarkeSubdiff f x₀ = {ξ | ∀ x, f x₀ + ξ (x - x₀) ≤ f x} := by
  obtain ⟨K, U, hU, hL⟩ := ConvexOn.locallyLipschitz hf x₀
  have hS : subdiff (fun x ↦ (f x : EReal)) x₀ = {ξ | ∀ x, f x₀ + ξ (x - x₀) ≤ f x} := by
    ext ξ
    rw [mem_subdiff_of_convex (convex_epi_coe_of_convexOn hf) rfl]
    simp only [EReal.coe_le_coe_iff]
    exact Iff.rfl
  have hc : Convex ℝ {ξ : StrongDual ℝ E | ∀ x, f x₀ + ξ (x - x₀) ≤ f x} := by
    intro a ha b hb s t hs ht hst x
    have h1 : f x₀ + a (x - x₀) ≤ f x := ha x
    have h2 : f x₀ + b (x - x₀) ≤ f x := hb x
    simp only [add_apply, smul_apply, smul_eq_mul]
    have e1 : s * f x + t * f x = f x := by rw [← add_mul, hst, one_mul]
    have e2 : s * f x₀ + t * f x₀ = f x₀ := by rw [← add_mul, hst, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left h1 hs, mul_le_mul_of_nonneg_left h2 ht]
  rw [clarkeSubdiff_eq_convexHull hU hL, hS, hc.convexHull_eq]

/-- Thm. 7.32 of [Mordukhovich–Nam 2022], (7.44) (sum rule):
`∂̄(f + g)(x₀) ⊆ ∂̄f(x₀) + ∂̄g(x₀)`. -/
theorem clarkeSubdiff_add_subset (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U) (hV : V ∈ 𝓝 x₀)
    (hK : LipschitzOnWith K g V) :
    clarkeSubdiff (fun x ↦ f x + g x) x₀ ⊆ clarkeSubdiff f x₀ + clarkeSubdiff g x₀ := by
  have hLK : LipschitzOnWith (L + K) (fun x ↦ f x + g x) (U ∩ V) :=
    (hL.mono inter_subset_left).add (hK.mono inter_subset_right)
  rw [clarkeSubdiff_eq_convexHull (inter_mem hU hV) hLK, clarkeSubdiff_eq_convexHull hU hL,
    clarkeSubdiff_eq_convexHull hV hK, ← convexHull_add]
  refine convexHull_mono ?_
  have := subdiff_add_subset_of_lipschitz (φ := fun x ↦ (f x : EReal)) (f := g) rfl
    (locallyClosed_epi_of_continuousOn hU hL.continuousOn (f x₀)) hV hK
  simpa only [← EReal.coe_add] using this

/-- `∂̄(t f)(x₀) = t ∂̄f(x₀)` [Mordukhovich–Nam 2022, (7.54)]. -/
theorem clarkeSubdiff_const_mul (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith L f U) (t : ℝ) :
    clarkeSubdiff (fun x ↦ t * f x) x₀ = t • clarkeSubdiff f x₀ := by
  have hpos : ∀ s : ℝ, 0 < s → clarkeSubdiff (fun x ↦ s * f x) x₀ = s • clarkeSubdiff f x₀ :=
    fun s hs ↦ by
      rw [clarkeSubdiff_eq_convexHull hU (lipschitzOnWith_const_mul hL s),
        clarkeSubdiff_eq_convexHull hU hL, ← convexHull_smul, subdiff_const_mul hs]
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have e : (fun x ↦ t * f x) = fun x ↦ -((-t) * f x) := by
      funext x
      ring
    rw [e, clarkeSubdiff_neg (f := fun x ↦ (-t) * f x), hpos (-t) (neg_pos.2 ht)]
    ext ξ
    simp only [Set.mem_neg, Set.mem_smul_set]
    refine ⟨fun ⟨y, hy, h⟩ ↦ ⟨y, hy, ?_⟩, fun ⟨y, hy, h⟩ ↦ ⟨y, hy, ?_⟩⟩ <;> ext v <;>
      have := congrArg (fun T : StrongDual ℝ E ↦ T v) h <;>
      simp only [smul_apply, smul_eq_mul, neg_apply, neg_mul] at this ⊢ <;> linarith
  · have h0 : HasStrictFDerivAt (fun x : E ↦ (0 : ℝ) * f x) (0 : StrongDual ℝ E) x₀ := by
      simpa using hasStrictFDerivAt_const (0 : ℝ) x₀
    rw [clarkeSubdiff_eq_singleton_of_hasStrictFDerivAt h0,
      Set.zero_smul_set (clarkeSubdiff_nonempty hU hL)]
    rfl
  · exact hpos t ht

/-- `∂̄(f + g)(x₀) = ∇f(x₀) + ∂̄g(x₀)` if `f` is strictly differentiable at `x₀` and `g` is
Lipschitz around `x₀` [Mordukhovich–Nam 2022, Cor. of Thm. 7.32 and Prop. 7.5]. -/
theorem clarkeSubdiff_add_eq_of_hasStrictFDerivAt {f' : StrongDual ℝ E}
    (hf : HasStrictFDerivAt f f' x₀) (hU : U ∈ 𝓝 x₀) (hg : LipschitzOnWith L g U) :
    clarkeSubdiff (fun x ↦ f x + g x) x₀ = {f'} + clarkeSubdiff g x₀ := by
  obtain ⟨K', V', hV', hK'⟩ := hf.exists_lipschitzOnWith
  refine subset_antisymm ?_ ?_
  · have := clarkeSubdiff_add_subset hV' hK' hU hg
    rwa [clarkeSubdiff_eq_singleton_of_hasStrictFDerivAt hf] at this
  · rintro x ⟨a', ha', ξ, hξ, hx⟩
    rw [mem_singleton_iff] at ha'
    simp only at hx
    rw [← hx, ha']
    have hfg : LipschitzOnWith (K' + L) (fun x ↦ f x + g x) (V' ∩ U) :=
      (hK'.mono inter_subset_left).add (hg.mono inter_subset_right)
    have h := clarkeSubdiff_add_subset (inter_mem hV' hU) hfg hV' (lipschitzOnWith_neg hK')
    have hg' : (fun x ↦ (f x + g x) + -f x) = g := by funext x; ring
    rw [hg', clarkeSubdiff_neg, clarkeSubdiff_eq_singleton_of_hasStrictFDerivAt hf,
      neg_singleton] at h
    obtain ⟨a, ha, b, hb, hab⟩ := h hξ
    rw [mem_singleton_iff] at hb
    simp only at hab
    subst hb
    have : f' + ξ = a := by rw [← hab]; abel
    rw [this]
    exact ha

end FiniteDimensional

section ProjectionFiniteDimensional

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ F]

/-- `∂̄(φ - μ ∘ fst)(p) = ∇φ(p) - ∂̄μ(p.1) × {0}` for `φ` strictly differentiable at `p` and `μ`
Lipschitz around `p.1`. -/
theorem clarkeSubdiff_sub_comp_fst {φ : E × F → ℝ} {φ' : StrongDual ℝ (E × F)} {p : E × F}
    (hφ : HasStrictFDerivAt φ φ' p) {μ : E → ℝ} {U : Set E} {L : ℝ≥0} (hU : U ∈ 𝓝 p.1)
    (hL : LipschitzOnWith L μ U) :
    clarkeSubdiff (fun q ↦ φ q - μ q.1) p =
      {φ'} - (fun u : StrongDual ℝ E ↦ u.comp (ContinuousLinearMap.fst ℝ E F)) ''
        clarkeSubdiff μ p.1 := by
  have hU' : Prod.fst ⁻¹' U ∈ 𝓝 p := continuous_fst.continuousAt.preimage_mem_nhds hU
  have hL' : LipschitzOnWith (L * 1) (fun q : E × F ↦ μ q.1) (Prod.fst ⁻¹' U) :=
    hL.comp LipschitzWith.prod_fst.lipschitzOnWith fun _ hq ↦ hq
  rw [show (fun q ↦ φ q - μ q.1) = fun q ↦ φ q + -μ q.1 from funext fun q ↦ sub_eq_add_neg _ _,
    clarkeSubdiff_add_eq_of_hasStrictFDerivAt hφ hU' (lipschitzOnWith_neg hL'),
    clarkeSubdiff_neg, clarkeSubdiff_comp_fst, sub_eq_add_neg]

end ProjectionFiniteDimensional

end VariationalAnalysis
