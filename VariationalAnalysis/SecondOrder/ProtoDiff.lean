/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis.SecondOrder.C11
import VariationalAnalysis.SecondOrder.EpiConvergence
import VariationalAnalysis.SecondOrder.Moreau
import VariationalAnalysis.SCD.Calculus

/-!
# Second-order relations for prox-regular functions

This file proves [Mordukhovich 2024, Thm. 1.86] (body numbering): for a function `φ` continuously
prox-regular at `x̄` for `v̄` whose subgradient mapping is proto-differentiable at `(x̄, v̄)`
(Def. 1.85), the subgradient graphical derivative is contained in the combined second-order
subdifferential, `∂²_D φ(x̄, v̄)(u) ⊆ ∂²φ(x̄, v̄)(u)` (1.116).

## Main results

* `graphDeriv_shear_iff`, `coderiv_shear_iff`, `ProtoDifferentiableAt.of_shear`: graphical
  derivatives, coderivatives and proto-differentiability under the graphShear
  `L(x, y) = (x + B y, y)` of the graph (the book's (1.117)–(1.118)).
* `dirDifferentiableAt_of_geometricallyDerivableAt`: a mapping Lipschitz around `x` whose graph is
  geometrically derivable at `(x, f x)` is directionally differentiable at `x`.
* `ContinuouslyProxRegularFor.exists_local_moreau`: near `(x̄, v̄)`, the graph of `∂φ` is the
  image under the graphShear `(u, v) ↦ (u - λv, v)` of the graph of the Lipschitz gradient of a
  Moreau envelope (from the proofs of Thm. 1.71 and Cor. 1.72).
* `ContinuouslyProxRegularFor.subgradGraphDeriv_subset_secondOrderSubdiff`:
  [Mordukhovich 2024, Thm. 1.86, (1.116)].

## Implementation notes

Following the book, the proof reduces to Thm. 1.84 for the Moreau envelope `e_λ φ` at
`x̄ + λv̄`: proto-differentiability of `∂φ` gives geometric derivability of the graph of
`∇e_λ φ`, hence directional differentiability of `∇e_λ φ`, and graphical derivatives and
coderivatives of `∂φ` and `∇e_λ φ` correspond under the graphShear. As in Cor. 1.72, `φ` is first
replaced by `φ` plus the indicator of a closed ball, so no global prox-boundedness or lower
semicontinuity is needed.
-/

open Filter Topology Set Metric ContinuousLinearMap InnerProductSpace
open scoped NNReal RealInnerProductSpace

namespace VariationalAnalysis

/-! ### Shears of graphs -/

section Shear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The graphShear `(x, y) ↦ (x + B y, y)` of `E × F`. -/
noncomputable def graphShear (B : F →L[ℝ] E) : (E × F) ≃L[ℝ] (E × F) :=
  ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.fst ℝ E F + B.comp (ContinuousLinearMap.snd ℝ E F)).prod
      (ContinuousLinearMap.snd ℝ E F))
    ((ContinuousLinearMap.fst ℝ E F - B.comp (ContinuousLinearMap.snd ℝ E F)).prod
      (ContinuousLinearMap.snd ℝ E F))
    (fun q ↦ by ext <;> simp) (fun q ↦ by ext <;> simp)

/-- The shear acts by `graphShear B (x, y) = (x + B y, y)`. -/
@[simp] theorem graphShear_apply (B : F →L[ℝ] E) (q : E × F) :
    graphShear B q = (q.1 + B q.2, q.2) := rfl

/-- The inverse shear acts by `(graphShear B).symm (x, y) = (x - B y, y)`. -/
@[simp] theorem graphShear_symm_apply (B : F →L[ℝ] E) (q : E × F) :
    (graphShear B).symm q = (q.1 - B q.2, q.2) := rfl

variable [CompleteSpace E] [CompleteSpace F] {S T : E → Set F} {x₀ : E} {y₀ : F}
  {B : F →L[ℝ] E}

omit [CompleteSpace E] [CompleteSpace F] in
/-- If `y ∈ S x ↔ y ∈ T (x + B y)` for all `(x, y)` near `(x₀, y₀)`, then `gph S` coincides near
`(x₀, y₀)` with the preimage of `gph T` under the shear `(x, y) ↦ (x + B y, y)`. -/
theorem graph_eventuallyEq_graphShear
    (hloc : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ∈ S p.1 ↔ p.2 ∈ T (p.1 + B p.2)) :
    graph S =ᶠ[𝓝 (x₀, y₀)] graphShear B ⁻¹' graph T :=
  eventuallyEq_set.2 hloc

/-- Graphical derivatives under a graphShear of the graph: if `gph S = L⁻¹(gph T)` near `(x₀, y₀)`
with `L(x, y) = (x + B y, y)`, then `z ∈ DS(x₀, y₀)(u)` iff `z ∈ DT(x₀ + B y₀, y₀)(u + B z)`. -/
theorem graphDeriv_shear_iff
    (hloc : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ∈ S p.1 ↔ p.2 ∈ T (p.1 + B p.2)) {u : E} {z : F} :
    z ∈ graphDeriv S x₀ y₀ u ↔ z ∈ graphDeriv T (x₀ + B y₀) y₀ (u + B z) := by
  change (u, z) ∈ contingentCone (graph S) (x₀, y₀) ↔
    (u + B z, z) ∈ contingentCone (graph T) (x₀ + B y₀, y₀)
  rw [contingentCone_congr (graph_eventuallyEq_graphShear hloc),
    mem_contingentCone_preimage_iff (graphShear B).hasStrictFDerivAt]
  rfl

/-- Coderivatives under a graphShear of the graph (the book's (1.118)): if `gph S = L⁻¹(gph T)` near
`(x₀, y₀)` with `L(x, y) = (x + B y, y)`, then `x* ∈ D*S(x₀, y₀)(y*)` iff
`x* ∈ D*T(x₀ + B y₀, y₀)(y* + x* ∘ B)`. -/
theorem coderiv_shear_iff
    (hloc : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ∈ S p.1 ↔ p.2 ∈ T (p.1 + B p.2))
    {xs : StrongDual ℝ E} {ys : StrongDual ℝ F} :
    xs ∈ coderiv S x₀ y₀ ys ↔ xs ∈ coderiv T (x₀ + B y₀) y₀ (ys + xs.comp B) := by
  change xs.coprod (-ys) ∈ normalCone (graph S) (x₀, y₀) ↔
    xs.coprod (-(ys + xs.comp B)) ∈ normalCone (graph T) (x₀ + B y₀, y₀)
  rw [normalCone_congr (graph_eventuallyEq_graphShear hloc),
    mem_normalCone_preimage_iff (D := fun _ ↦ ((graphShear B : (E × F) ≃L[ℝ] (E × F)) :
      (E × F) →L[ℝ] (E × F)))
      (Eventually.of_forall fun _ ↦ (graphShear B).hasStrictFDerivAt) continuousAt_const rfl]
  have : (xs.coprod (-ys)).comp ((graphShear B).symm : (E × F) →L[ℝ] (E × F)) =
      xs.coprod (-(ys + xs.comp B)) := by
    refine ContinuousLinearMap.ext fun q ↦ ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      graphShear_symm_apply, ContinuousLinearMap.coprod_apply, map_sub]
    simp
    ring
  rw [this]
  rfl

/-- Proto-differentiability transfers along a graphShear of the graph. -/
theorem ProtoDifferentiableAt.of_shear
    (hloc : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ∈ S p.1 ↔ p.2 ∈ T (p.1 + B p.2)) (hy : y₀ ∈ S x₀)
    (h : ProtoDifferentiableAt S x₀ y₀) : ProtoDifferentiableAt T (x₀ + B y₀) y₀ := by
  obtain ⟨W, hW, hWloc⟩ := hloc.exists_mem
  have hsx : (graphShear B).symm (x₀ + B y₀, y₀) = (x₀, y₀) := by simp
  have hc : Tendsto (graphShear B).symm (𝓝 (x₀ + B y₀, y₀)) (𝓝 (x₀, y₀)) := by
    have := (graphShear B).symm.continuous.tendsto (x₀ + B y₀, y₀)
    rwa [hsx] at this
  refine GeometricallyDerivableAt.of_inter_eq_preimage (Φ := (graphShear B).symm)
    (e := (graphShear B).symm) (by rw [hsx]; exact h) (hc hW) ?_
    (graphShear B).symm.hasStrictFDerivAt ?_
  · ext p
    simp only [mem_inter_iff, mem_preimage]
    have := hWloc ((graphShear B).symm p)
    simp only [graphShear_symm_apply, sub_add_cancel] at this
    constructor
    · rintro ⟨hp, hpW⟩
      exact ⟨(this hpW).2 hp, hpW⟩
    · rintro ⟨hp, hpW⟩
      exact ⟨(this hpW).1 hp, hpW⟩
  · exact (hWloc (x₀, y₀) (mem_of_mem_nhds hW)).1 hy

end Shear

/-! ### Derivable graphs of Lipschitz mappings -/

section Derivable

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

/-- Geometric derivability is a local property. -/
theorem GeometricallyDerivableAt.congr [CompleteSpace X] {Ω Ω' : Set X} {x : X}
    (h : GeometricallyDerivableAt Ω x) (hΩ : Ω =ᶠ[𝓝 x] Ω') (hx : x ∈ Ω') :
    GeometricallyDerivableAt Ω' x := by
  obtain ⟨W, hW, hWΩ⟩ := (eventuallyEq_set.1 hΩ).exists_mem
  refine GeometricallyDerivableAt.of_inter_eq_preimage (Φ := ContinuousLinearEquiv.refl ℝ X)
    (e := ContinuousLinearEquiv.refl ℝ X) (by simpa using h) hW ?_
    (ContinuousLinearEquiv.refl ℝ X).hasStrictFDerivAt hx
  ext y
  simp only [mem_inter_iff, mem_preimage, ContinuousLinearEquiv.coe_refl', id_eq]
  exact ⟨fun ⟨hy, hyW⟩ ↦ ⟨(hWΩ y hyW).2 hy, hyW⟩, fun ⟨hy, hyW⟩ ↦ ⟨(hWΩ y hyW).1 hy, hyW⟩⟩

variable [FiniteDimensional ℝ Y]

/-- A mapping Lipschitz around `x` whose graph is geometrically derivable at `(x, f x)` is
directionally differentiable at `x`. -/
theorem dirDifferentiableAt_of_geometricallyDerivableAt {f : X → Y} {x : X} {U : Set X}
    {K : ℝ≥0} (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith K f U)
    (hd : GeometricallyDerivableAt (graph fun x ↦ ({f x} : Set Y)) (x, f x)) :
    DirDifferentiableAt f x := by
  intro w
  have hx0 : (x, f x) ∈ graph fun x ↦ ({f x} : Set Y) := mem_singleton (f x)
  have hxU : x ∈ U := mem_of_mem_nhds hU
  have hfc : ContinuousAt f x := hL.continuousOn.continuousAt hU
  -- a cluster point `z` of the difference quotients, so `(w, z)` is tangent
  obtain ⟨z, hz⟩ : ∃ z, (w, z) ∈ contingentCone (graph fun x ↦ ({f x} : Set Y)) (x, f x) := by
    obtain ⟨η, hη, hηU⟩ := Metric.mem_nhds_iff.1 hU
    obtain ⟨c, hc⟩ : ∃ c, c = η / (2 * (‖w‖ + 1)) := ⟨_, rfl⟩
    have hcpos : 0 < c := by rw [hc]; positivity
    let s : ℕ → ℝ := fun n ↦ c * (1 / ((n : ℝ) + 1))
    have hspos : ∀ n, 0 < s n := fun n ↦ by positivity
    have hsle : ∀ n, s n ≤ c := fun n ↦ by
      have : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
      calc s n ≤ c * 1 := mul_le_mul_of_nonneg_left this hcpos.le
        _ = c := mul_one c
    have hsU : ∀ n, x + s n • w ∈ U := fun n ↦ by
      apply hηU
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg (hspos n).le]
      calc s n * ‖w‖ ≤ c * ‖w‖ := mul_le_mul_of_nonneg_right (hsle n) (norm_nonneg _)
        _ ≤ c * (‖w‖ + 1) := mul_le_mul_of_nonneg_left (by linarith) hcpos.le
        _ < η := by rw [hc]; field_simp; linarith
    let q : ℕ → Y := fun n ↦ (s n)⁻¹ • (f (x + s n • w) - f x)
    have hq : ∀ n, q n ∈ closedBall (0 : Y) (K * ‖w‖) := fun n ↦ by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (inv_pos.2 (hspos n)).le]
      have := hL.dist_le_mul _ (hsU n) _ hxU
      rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg (hspos n).le] at this
      calc (s n)⁻¹ * ‖f (x + s n • w) - f x‖ ≤ (s n)⁻¹ * (K * (s n * ‖w‖)) :=
            mul_le_mul_of_nonneg_left this (inv_nonneg.2 (hspos n).le)
        _ = K * ‖w‖ := by field_simp [(hspos n).ne']
    obtain ⟨z, -, ψ, hψ, hlim⟩ := tendsto_subseq_of_bounded isBounded_closedBall hq
    have hs0 : Tendsto s atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul c
      rwa [mul_zero] at this
    have hsψ : Tendsto (s ∘ ψ) atTop (𝓝 0) := hs0.comp hψ.tendsto_atTop
    have hxs : Tendsto (fun k ↦ x + s (ψ k) • w) atTop (𝓝 x) := by
      simpa using (tendsto_const_nhds (x := x)).add (hsψ.smul_const w)
    refine ⟨z, hx0, fun k ↦ (x + s (ψ k) • w, f (x + s (ψ k) • w)), fun k ↦ (s (ψ k))⁻¹,
      fun k ↦ ⟨mem_singleton _, (inv_pos.2 (hspos _)).le⟩,
      hxs.prodMk_nhds (hfc.tendsto.comp hxs), ?_⟩
    refine Tendsto.prodMk_nhds ?_ hlim
    refine tendsto_const_nhds.congr fun k ↦ ?_
    simp [smul_smul, inv_mul_cancel₀ (hspos (ψ k)).ne']
  refine ⟨z, ?_⟩
  unfold HasDirDerivAt
  rw [tendsto_iff_seq_tendsto]
  intro t ht
  obtain ⟨p, hp, hplim⟩ := hd.exists_seq hx0 hz ht
  have hpf : ∀ k, (p k).2 = f (p k).1 := fun k ↦ hp k
  have h1 : Tendsto (fun k ↦ (t k)⁻¹ • ((p k).1 - x)) atTop (𝓝 w) := by
    simpa [Function.comp_def] using (continuous_fst.tendsto _).comp hplim
  have h2 : Tendsto (fun k ↦ (t k)⁻¹ • (f (p k).1 - f x)) atTop (𝓝 z) := by
    simpa [Function.comp_def, hpf] using (continuous_snd.tendsto _).comp hplim
  have ha : Tendsto (fun k ↦ (p k).1) atTop (𝓝 x) := tendsto_of_tendsto_inv_smul_sub ht h1
  have hpos : ∀ᶠ k in atTop, 0 < t k := (tendsto_nhdsWithin_iff.1 ht).2
  have hxt : Tendsto (fun k ↦ x + t k • w) atTop (𝓝 x) := (tendsto_add_smul_nhdsGT x w).comp ht
  have hdiff : Tendsto (fun k ↦ (t k)⁻¹ • (f (x + t k • w) - f x) -
      (t k)⁻¹ • (f (p k).1 - f x)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using ((h1.sub_const w).norm.const_mul (K : ℝ)))
    filter_upwards [hpos, hxt.eventually hU, ha.eventually hU] with k hk hk1 hk2
    rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_of_nonneg (inv_pos.2 hk).le]
    calc (t k)⁻¹ * ‖f (x + t k • w) - f (p k).1‖
        ≤ (t k)⁻¹ * (K * ‖x + t k • w - (p k).1‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hk).le
          rw [← dist_eq_norm, ← dist_eq_norm]
          exact hL.dist_le_mul _ hk1 _ hk2
      _ = K * ‖(t k)⁻¹ • ((p k).1 - x) - w‖ := by
          rw [show x + t k • w - (p k).1 = -(t k • ((t k)⁻¹ • ((p k).1 - x) - w)) by
              rw [smul_sub, smul_smul, mul_inv_cancel₀ hk.ne', one_smul]; abel,
            norm_neg, norm_smul, Real.norm_of_nonneg hk.le]
          field_simp
  have := h2.add hdiff
  simp only [add_sub_cancel, add_zero] at this
  exact this

end Derivable

/-! ### Local structure of the subgradient graph of a prox-regular function -/

section Moreau

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {φ : E → EReal} {x₀ : E}

/-- For `φ` continuously prox-regular at `x₀` for `v₀ = ⟨g, ·⟩`, there are `λ > 0` and a function
`e` (the Moreau envelope of a localization of `φ`) with gradient `⟨f(·), ·⟩` Lipschitz around
`ū = x₀ + λg`, such that near `(x₀, g)`, `⟨y, ·⟩ ∈ ∂φ(x)` iff `y = f(x + λy)`. Moreover
`u ↦ u - λ f(u)` (the proximal mapping of the localization) is monotone around `ū`. -/
theorem ContinuouslyProxRegularFor.exists_local_moreau {g : E}
    (hφ : ContinuouslyProxRegularFor φ x₀ (toDual ℝ E g)) :
    ∃ l > (0 : ℝ), ∃ δ > (0 : ℝ), ∃ e : E → ℝ, ∃ f : E → E, ∃ K : ℝ≥0,
      (∀ u ∈ ball (x₀ + l • g) δ, HasFDerivAt e (toDual ℝ E (f u)) u) ∧
      LipschitzOnWith K f (ball (x₀ + l • g) δ) ∧
      (∀ u₁ ∈ ball (x₀ + l • g) δ, ∀ u₂ ∈ ball (x₀ + l • g) δ,
        0 ≤ ⟪(u₁ - l • f u₁) - (u₂ - l • f u₂), u₁ - u₂⟫_ℝ) ∧
      ∀ᶠ q : E × E in 𝓝 (x₀, g), (toDual ℝ E q.2 ∈ subdiff φ q.1 ↔ q.2 = f (q.1 + l • q.2)) := by
  classical
  obtain ⟨hpr, hsc⟩ := hφ
  set v₀ := toDual ℝ E g with hv₀
  obtain ⟨r₀, hr₀, -⟩ := hpr.1
  obtain ⟨δl, hδl, Hlsc⟩ := Metric.eventually_nhds_iff.1 hpr.2.1
  obtain ⟨r₀', hr₀', ε₀, hε₀, α, hα, Hprox⟩ := hpr.mem_proxSubdiff
  have hrr : r₀' = r₀ := by rw [hr₀] at hr₀'; exact_mod_cast hr₀'.symm
  rw [hrr] at Hprox
  obtain ⟨ρ, hρ, hρl, hρ0⟩ : ∃ ρ > (0 : ℝ), ρ < δl ∧ ρ ≤ ε₀ :=
    ⟨min (δl / 2) ε₀, lt_min (half_pos hδl) hε₀,
      (min_le_left _ _).trans_lt (half_lt_self hδl), min_le_right _ _⟩
  -- the localized function `φ + δ_{B̄(x̄, ρ)}`
  set ψ : E → EReal := fun x ↦ if x ∈ closedBall x₀ ρ then φ x else ⊤ with hψ_def
  have hψeq : ∀ x ∈ closedBall x₀ ρ, ψ x = φ x := fun x hx ↦ if_pos hx
  have hψtop : ∀ x ∉ closedBall x₀ ρ, ψ x = ⊤ := fun x hx ↦ if_neg hx
  have hψball : ∀ x ∈ ball x₀ ρ, ψ x = φ x := fun x hx ↦ hψeq x (ball_subset_closedBall hx)
  have hψS : ∀ x ∈ ball x₀ ρ, subdiff ψ x = subdiff φ x := fun x hx ↦
    subdiff_congr (eventually_of_mem (isOpen_ball.mem_nhds hx) hψball)
  have hψpr : ProxRegularFor ψ x₀ v₀ := hpr.congr hρ hψball
  have hψlsc : ∀ x, LowerSemicontinuousAt ψ x := by
    intro y c hc
    by_cases hy : y ∈ closedBall x₀ ρ
    · rw [hψeq y hy] at hc
      have hyl : dist y x₀ < δl := (mem_closedBall.1 hy).trans_lt hρl
      filter_upwards [Hlsc hyl c hc] with z hz
      by_cases hz' : z ∈ closedBall x₀ ρ
      · rwa [hψeq z hz']
      · rw [hψtop z hz']; exact hz.trans_le le_top
    · rw [hψtop y hy] at hc
      filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hy] with z hz
      rw [hψtop z hz]; exact hc
  have hψbd : ∃ a b : ℝ, ∀ x, ((a - b * ‖x - x₀‖ ^ 2 : ℝ) : EReal) ≤ ψ x := by
    refine ⟨r₀ - ‖g‖ * ρ - α / 2 * ρ ^ 2, 0, fun x ↦ ?_⟩
    by_cases hx : x ∈ closedBall x₀ ρ
    · rw [hψeq x hx]
      have hxn : ‖x - x₀‖ ≤ ρ := by rw [← dist_eq_norm]; exact mem_closedBall.1 hx
      refine le_trans (EReal.coe_le_coe_iff.2 ?_) (Hprox x (hxn.trans hρ0))
      rw [hv₀, toDual_apply_apply]
      have h1 := abs_le.1 (abs_real_inner_le_norm g (x - x₀))
      have h2 : ‖g‖ * ‖x - x₀‖ ≤ ‖g‖ * ρ := mul_le_mul_of_nonneg_left hxn (norm_nonneg g)
      have h3 : ‖x - x₀‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxn 2
      have h4 := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ α / 2)
      linarith [h1.1]
    · rw [hψtop x hx]; exact le_top
  -- the proximal mapping and the Moreau envelope of `ψ`
  obtain ⟨ε, hε, l₀, hl₀, H⟩ := hψpr.exists_proximalMap hψlsc hψbd
  obtain ⟨l₁, hl₁, H'⟩ := hψpr.exists_moreauEnvelope hψlsc hψbd
  obtain ⟨l, hl_def⟩ : ∃ l, l = min l₀ l₁ / 2 := ⟨_, rfl⟩
  have hl : 0 < l := by rw [hl_def]; exact half_pos (lt_min hl₀ hl₁)
  have hll₀ : l < l₀ := by
    rw [hl_def]; linarith [min_le_left l₀ l₁, half_lt_self (lt_min hl₀ hl₁)]
  have hll₁ : l < l₁ := by
    rw [hl_def]; linarith [min_le_right l₀ l₁, half_lt_self (lt_min hl₀ hl₁)]
  obtain ⟨δ, hδ, p, hp0, hpU, hLip, hloc, huniq⟩ := H l hl hll₀
  obtain ⟨δ₂, hδ₂, p₂, hpU₂, -, hder, -⟩ := H' l hl hll₁
  -- subdifferential continuity
  obtain ⟨r₁, hr₁, hcont⟩ : ∃ r₁ > (0 : ℝ), ∀ x (v : StrongDual ℝ E), ‖x - x₀‖ < r₁ →
      ‖v - v₀‖ < r₁ → v ∈ subdiff φ x → ∃ s : ℝ, φ x = s ∧ |s - r₀| < ε := by
    have ht := hsc.tendsto
    rw [hr₀] at ht
    have hI : Ioo ((r₀ - ε : ℝ) : EReal) ((r₀ + ε : ℝ) : EReal) ∈ 𝓝 ((r₀ : ℝ) : EReal) :=
      Ioo_mem_nhds (EReal.coe_lt_coe_iff.2 (by linarith)) (EReal.coe_lt_coe_iff.2 (by linarith))
    obtain ⟨O, hO, hO0, hOs⟩ := mem_nhdsWithin.1 (ht hI)
    obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.1 hO _ hO0
    refine ⟨r₁, hr₁, fun x v hx hv hvx ↦ ?_⟩
    have hmem : (x, v) ∈ O := hball (by
      rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm]; exact ⟨hx, hv⟩)
    obtain ⟨s, hs, hs1, hs2⟩ := exists_real_of_mem_Ioo (hOs ⟨hmem, hvx⟩)
    exact ⟨s, hs, abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩⟩
  -- the radii
  obtain ⟨τ, hτ, hτr, hτε, hτρ⟩ : ∃ τ > (0 : ℝ), τ ≤ r₁ ∧ τ ≤ ε ∧ τ < ρ :=
    ⟨min (min r₁ ε) (ρ / 2), lt_min (lt_min hr₁ hε) (half_pos hρ),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans_lt (half_lt_self hρ)⟩
  obtain ⟨δ', hδ', hδ'δ, hδ'δ₂, hδ'τ, hδ'τl⟩ : ∃ δ' > (0 : ℝ), δ' ≤ δ ∧ δ' ≤ δ₂ ∧ 4 * δ' ≤ τ ∧
      4 * δ' ≤ τ * l := by
    refine ⟨min (min δ δ₂) (min (τ / 4) (τ * l / 4)),
      lt_min (lt_min hδ hδ₂) (lt_min (by positivity) (by positivity)),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      ?_, ?_⟩
    · have := (min_le_right (min δ δ₂) _).trans (min_le_left (τ / 4) (τ * l / 4)); linarith
    · have := (min_le_right (min δ δ₂) _).trans (min_le_right (τ / 4) (τ * l / 4)); linarith
  set f : E → E := fun u ↦ l⁻¹ • (u - p u) with hf
  have hc : x₀ + l • g ∈ ball (x₀ + l • g) δ := mem_ball_self hδ
  have hdual : ∀ y : E, ‖toDual ℝ E y - v₀‖ = dist y g := fun y ↦ by
    rw [hv₀, ← map_sub, LinearIsometryEquiv.norm_map, dist_eq_norm]
  refine ⟨l, hl, δ', hδ', fun u ↦ (moreauEnvelope ψ l u).toReal, f, Real.toNNReal (3 / l),
    fun u hu ↦ ?_, ?_, ?_, ?_⟩
  · -- the gradient of the envelope
    have hu₁ : u ∈ ball (x₀ + l • g) δ := ball_subset_ball hδ'δ hu
    have hu₂ : u ∈ ball (x₀ + l • g) δ₂ := ball_subset_ball hδ'δ₂ hu
    have hpp : p₂ u = p u := by
      have := (hpU₂ u hu₂).symm.trans (hpU u hu₁)
      exact Set.singleton_eq_singleton_iff.1 this
    have := hder u hu₂
    rwa [hpp] at this
  · refine LipschitzOnWith.of_dist_le_mul fun u₁ hu₁ u₂ hu₂ ↦ ?_
    have := hLip.dist_le_mul u₁ (ball_subset_ball hδ'δ hu₁) u₂ (ball_subset_ball hδ'δ hu₂)
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_ofNat] at this
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity), hf, ← smul_sub,
      norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hl.le),
      show u₁ - p u₁ - (u₂ - p u₂) = (u₁ - u₂) - (p u₁ - p u₂) by abel, div_eq_mul_inv,
      mul_comm 3, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hl.le)
    linarith [norm_sub_le (u₁ - u₂) (p u₁ - p u₂)]
  · -- monotonicity of the proximal mapping
    intro u₁ hu₁ u₂ hu₂
    have hu₁' : u₁ ∈ ball (x₀ + l • g) δ := ball_subset_ball hδ'δ hu₁
    have hu₂' : u₂ ∈ ball (x₀ + l • g) δ := ball_subset_ball hδ'δ hu₂
    have hfp : ∀ u : E, u - l • f u = p u := fun u ↦ by
      rw [hf]; dsimp only
      rw [smul_smul, mul_inv_cancel₀ hl.ne', one_smul, sub_sub_cancel]
    obtain ⟨-, -, -, s₁, hs₁, -⟩ := hloc u₁ hu₁'
    obtain ⟨-, -, -, s₂, hs₂, -⟩ := hloc u₂ hu₂'
    rw [hfp, hfp]
    exact inner_nonneg_of_mem_proximalMap hl hs₁ hs₂ (by rw [hpU u₁ hu₁']; rfl)
      (by rw [hpU u₂ hu₂']; rfl)
  · -- the local description of the graph
    set W : Set (E × E) := {q | dist q.1 x₀ < τ ∧ dist q.2 g < τ ∧
      dist (q.1 + l • q.2) (x₀ + l • g) < δ'} with hW
    have hWo : IsOpen W := by
      have c1 : Continuous fun q : E × E ↦ dist q.1 x₀ := by fun_prop
      have c2 : Continuous fun q : E × E ↦ dist q.2 g := by fun_prop
      have c3 : Continuous fun q : E × E ↦ dist (q.1 + l • q.2) (x₀ + l • g) := by fun_prop
      exact (isOpen_lt c1 continuous_const).inter
        ((isOpen_lt c2 continuous_const).inter (isOpen_lt c3 continuous_const))
    have hW0 : (x₀, g) ∈ W := ⟨by simpa using hτ, by simpa using hτ, by simpa using hδ'⟩
    filter_upwards [hWo.mem_nhds hW0] with ⟨x, y'⟩ ⟨hx1, hx2, hx3⟩
    have hx1' : dist x x₀ < τ := hx1
    have hx2' : dist y' g < τ := hx2
    have hx3' : dist (x + l • y') (x₀ + l • g) < δ' := hx3
    dsimp only
    constructor
    · intro hgr'
      have hxρ : x ∈ ball x₀ ρ := by rw [mem_ball]; linarith
      have hu : x + l • y' ∈ ball (x₀ + l • g) δ := ball_subset_ball hδ'δ hx3'
      have hxe : x = p (x + l • y') := by
        refine huniq _ hu x ?_
        rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hl.ne', one_smul]
        obtain ⟨s, hs, hsr⟩ := hcont x (toDual ℝ E y') (by rw [← dist_eq_norm]; linarith)
          (by rw [hdual]; linarith) hgr'
        refine ⟨by rwa [hψS x hxρ], by rw [← dist_eq_norm]; linarith, by rw [hdual]; linarith,
          s, by rw [hψball x hxρ, hs], ?_⟩
        rwa [hψball x₀ (mem_ball_self hρ), hr₀, EReal.toReal_coe]
      rw [hf]
      dsimp only
      rw [← hxe, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hl.ne', one_smul]
    · intro hy
      set u := x + l • y' with hu_def
      have hu' : dist u (x₀ + l • g) < δ' := hx3'
      have huδ : u ∈ ball (x₀ + l • g) δ := ball_subset_ball hδ'δ hu'
      have hpu : ‖p u - x₀‖ ≤ 2 * ‖u - (x₀ + l • g)‖ := by
        have := hLip.dist_le_mul u huδ (x₀ + l • g) hc
        rwa [dist_eq_norm, dist_eq_norm, hp0, NNReal.coe_ofNat] at this
      rw [dist_eq_norm] at hu'
      have hpuρ : p u ∈ ball x₀ ρ := by rw [mem_ball, dist_eq_norm]; linarith
      have hpf : p u + l • f u = u := by
        rw [hf]; dsimp only
        rw [smul_smul, mul_inv_cancel₀ hl.ne', one_smul, add_sub_cancel]
      have hpx : p u = x := by
        rw [← hy] at hpf
        rw [hu_def] at hpf
        exact add_right_cancel hpf
      have := (hloc u huδ).1
      rw [hψS (p u) hpuρ, hpx] at this
      have hfy : l⁻¹ • (u - x) = y' := by rw [← hpx]; exact hy.symm
      rwa [hfy] at this

end Moreau

/-! ### Thm. 1.86 -/

section Main

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {φ : E → EReal} {x₀ : E}

/-- [Mordukhovich 2024, Thm. 1.86, (1.116)] (second-order relations for prox-regular functions):
if `φ` is continuously prox-regular at `x̄` for `v̄` and `∂φ` is proto-differentiable at
`(x̄, v̄)`, then `∂²_D φ(x̄, v̄)(u) ⊆ ∂²φ(x̄, v̄)(u)` for all `u`. -/
theorem ContinuouslyProxRegularFor.subgradGraphDeriv_subset_secondOrderSubdiff {g : E}
    (hφ : ContinuouslyProxRegularFor φ x₀ (toDual ℝ E g))
    (hproto : ProtoDifferentiableAt (subdiff φ) x₀ (toDual ℝ E g)) (u : E) :
    subgradGraphDeriv φ x₀ (toDual ℝ E g) u ⊆ secondOrderSubdiff φ x₀ (toDual ℝ E g) u := by
  obtain ⟨l, hl, δ, hδ, e, f, K, he, hfL, -, hloc⟩ := hφ.exists_local_moreau
  have hv₀mem : toDual ℝ E g ∈ subdiff φ x₀ := hφ.1.1
  set v₀ := toDual ℝ E g with hv₀
  set ū := x₀ + l • g with hū
  set φ' : E → StrongDual ℝ E := fun u ↦ toDual ℝ E (f u) with hφ'
  have hφ'L : LipschitzOnWith (1 * K) φ' (ball ū δ) :=
    (toDual ℝ E).lipschitz.comp_lipschitzOnWith hfL
  have hfū : f ū = g := ((hloc.self_of_nhds).1 hv₀mem).symm
  have hφ'ū : φ' ū = v₀ := by change toDual ℝ E (f ū) = v₀; rw [hfū]
  let B : StrongDual ℝ E →L[ℝ] E :=
    { toFun := fun v ↦ l • (toDual ℝ E).symm v
      map_add' := fun v w ↦ by simp [smul_add]
      map_smul' := fun c v ↦ by simp [smul_comm l c]
      cont := continuous_const.smul (toDual ℝ E).symm.continuous }
  have hB : ∀ v, B v = l • (toDual ℝ E).symm v := fun v ↦ rfl
  set T := subdiff fun u ↦ (e u : EReal) with hT_def
  have hT : ∀ᶠ u in 𝓝 ū, T u = {φ' u} :=
    eventually_subdiff_eq_singleton_of_lipschitz (ball_mem_nhds ū hδ) he hφ'L
  have hx₀B : x₀ + B v₀ = ū := by rw [hB, hv₀, LinearIsometryEquiv.symm_apply_apply]
  -- the graphShear relating the graphs of `∂φ` and `∇e`
  have hshear : ∀ᶠ p : E × StrongDual ℝ E in 𝓝 (x₀, v₀),
      p.2 ∈ subdiff φ p.1 ↔ p.2 ∈ T (p.1 + B p.2) := by
    have hc1 : Tendsto (fun p : E × StrongDual ℝ E ↦ (p.1, (toDual ℝ E).symm p.2))
        (𝓝 (x₀, v₀)) (𝓝 (x₀, g)) := by
      have : Continuous (fun p : E × StrongDual ℝ E ↦ (p.1, (toDual ℝ E).symm p.2)) :=
        continuous_fst.prodMk ((toDual ℝ E).symm.continuous.comp continuous_snd)
      have h := this.tendsto (x₀, v₀)
      simp only [hv₀, LinearIsometryEquiv.symm_apply_apply] at h
      exact h
    have hc2 : Tendsto (fun p : E × StrongDual ℝ E ↦ p.1 + B p.2) (𝓝 (x₀, v₀)) (𝓝 ū) := by
      have : Continuous (fun p : E × StrongDual ℝ E ↦ p.1 + B p.2) :=
        continuous_fst.add (B.continuous.comp continuous_snd)
      have h := this.tendsto (x₀, v₀)
      rwa [hx₀B] at h
    filter_upwards [hc1.eventually hloc, hc2.eventually hT] with p h1 h2
    rw [h2, mem_singleton_iff]
    simp only [LinearIsometryEquiv.apply_symm_apply] at h1
    rw [h1, LinearIsometryEquiv.symm_apply_eq, hB]
  -- `∇e` is directionally differentiable at `ū`
  have hprotoT : ProtoDifferentiableAt T ū v₀ := hx₀B ▸ hproto.of_shear hshear hv₀mem
  have hdT :
      GeometricallyDerivableAt (graph fun u ↦ ({φ' u} : Set (StrongDual ℝ E))) (ū, φ' ū) := by
    rw [hφ'ū]
    refine GeometricallyDerivableAt.congr hprotoT ?_ ?_
    · have := (continuous_fst.tendsto (ū, v₀)).eventually hT
      exact eventuallyEq_set.2 (this.mono fun q hq ↦ by
        change q.2 ∈ T q.1 ↔ q.2 ∈ ({φ' q.1} : Set _)
        rw [hq])
    · change v₀ ∈ ({φ' ū} : Set _)
      rw [hφ'ū]; exact mem_singleton _
  have hdir : DirDifferentiableAt φ' ū :=
    dirDifferentiableAt_of_geometricallyDerivableAt (ball_mem_nhds ū hδ) hφ'L hdT
  -- transfer through the graphShear and apply Thm. 1.84 to `e` at `ū`
  intro z hz
  have hz' : z ∈ graphDeriv T ū v₀ (u + B z) := by
    rw [← hx₀B]; exact (graphDeriv_shear_iff hshear).1 hz
  have h184 := _root_.VariationalAnalysis.subgradGraphDeriv_subset_secondOrderSubdiff
    (ball_mem_nhds ū hδ) he hφ'L hdir
    (u + B z)
  have hfv : toDual ℝ E (f ū) = v₀ := hφ'ū
  rw [hfv] at h184
  have hz2 : z ∈ coderiv T ū v₀ (NormedSpace.inclusionInDoubleDual ℝ E (u + B z)) := h184 hz'
  change z ∈ coderiv (subdiff φ) x₀ v₀ (NormedSpace.inclusionInDoubleDual ℝ E u)
  rw [coderiv_shear_iff hshear, hx₀B]
  have hι : NormedSpace.inclusionInDoubleDual ℝ E u + z.comp B =
      NormedSpace.inclusionInDoubleDual ℝ E (u + B z) := by
    refine ContinuousLinearMap.ext fun v ↦ ?_
    change v u + z (B v) = v (u + B z)
    rw [hB, hB, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      ← toDual_symm_apply (x := (toDual ℝ E).symm v) (y := z),
      ← toDual_symm_apply (x := (toDual ℝ E).symm z) (y := v), real_inner_comm]
  rwa [hι]

end Main

end VariationalAnalysis
