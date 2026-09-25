/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import Mathlib.Analysis.Calculus.FDeriv.Basic
import VariationalAnalysis.Normal.Limiting

/-!
# Coderivatives of set-valued mappings

For a set-valued mapping `S : E → Set F` and `(x₀, y₀) ∈ gph S`, the basic (limiting,
Mordukhovich) coderivative [Mordukhovich 2018, Def. 1.11, (1.15)] and the regular coderivative
(precoderivative) [Mordukhovich 2018, (1.16)] are

  `D*S(x₀, y₀)(v) = {u | (u, -v) ∈ N((x₀, y₀); gph S)}`,
  `D̂*S(x₀, y₀)(v) = {u | (u, -v) ∈ N̂((x₀, y₀); gph S)}`,

where `(u, -v)` is the dual element `u.coprod (-v)` on `E × F`. A single-valued map `f` is the
set-valued map `fun x ↦ {f x}`.

## Main results

* `regularCoderiv_subset_coderiv`, `smul_mem_coderiv`: `D*S(x₀, y₀)` contains
  `D̂*S(x₀, y₀)` and is positively homogeneous.
* `regularCoderiv_of_hasFDerivAt`: `D̂*f(x₀)(v) = {∇f(x₀)* v}` for `f` differentiable at `x₀`
  [Mordukhovich 2018, proof of Prop. 1.12].
* `coderiv_of_hasFDerivAt_of_continuousAt`: Prop. 1.12 of [Mordukhovich 2018] (coderivatives of
  smooth mappings): `D*f(x₀)(v) = D̂*f(x₀)(v) = {∇f(x₀)* v}` for `f` of class `C¹` around `x₀`.
-/

open Filter Topology Set

namespace VariationalAnalysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The graph `gph S = {(x, y) | y ∈ S x}` of a set-valued mapping. -/
def graph (S : E → Set F) : Set (E × F) := {p | p.2 ∈ S p.1}

/-- The regular coderivative (precoderivative) [Mordukhovich 2018, (1.16)]. -/
def regularCoderiv (S : E → Set F) (x₀ : E) (y₀ : F) (v : StrongDual ℝ F) :
    Set (StrongDual ℝ E) :=
  {u | u.coprod (-v) ∈ regularNormalCone (graph S) (x₀, y₀)}

/-- The basic (limiting, Mordukhovich) coderivative [Mordukhovich 2018, Def. 1.11, (1.15)]. -/
def coderiv (S : E → Set F) (x₀ : E) (y₀ : F) (v : StrongDual ℝ F) : Set (StrongDual ℝ E) :=
  {u | u.coprod (-v) ∈ normalCone (graph S) (x₀, y₀)}

variable {S : E → Set F} {x₀ : E} {y₀ : F} {u : StrongDual ℝ E} {v : StrongDual ℝ F}

theorem regularCoderiv_subset_coderiv : regularCoderiv S x₀ y₀ v ⊆ coderiv S x₀ y₀ v :=
  fun _ hu ↦ regularNormalCone_subset_normalCone hu

/-- The coderivative is positively homogeneous. -/
theorem smul_mem_coderiv (hu : u ∈ coderiv S x₀ y₀ v) {t : ℝ} (ht : 0 ≤ t) :
    t • u ∈ coderiv S x₀ y₀ (t • v) := by
  have h : (t • u).coprod (-(t • v)) = t • u.coprod (-v) := by ext <;> simp
  simpa [coderiv, h] using smul_mem_normalCone hu ht

section Smooth

variable {f : E → F}

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Approaching `(x₀, f x₀)` within the graph of `f` means approaching `x₀`. -/
theorem eventually_graph_of_eventually {P : E → F → Prop} (hP : ∀ᶠ x in 𝓝 x₀, P x (f x)) :
    ∀ᶠ p in 𝓝[graph fun x ↦ {f x}] (x₀, f x₀), P p.1 p.2 := by
  have hfst : Tendsto Prod.fst (𝓝[graph fun x ↦ {f x}] (x₀, f x₀)) (𝓝 x₀) :=
    (continuous_fst.tendsto _).mono_left nhdsWithin_le_nhds
  filter_upwards [hfst.eventually hP, self_mem_nhdsWithin] with p hp hpg
  obtain ⟨x, y⟩ := p
  have : y = f x := hpg
  subst this
  exact hp

/-- The regular coderivative of a map differentiable at `x₀` is the adjoint of its derivative
[Mordukhovich 2018, proof of Prop. 1.12]. -/
theorem regularCoderiv_of_hasFDerivAt {f' : E →L[ℝ] F} (hf : HasFDerivAt f f' x₀)
    (v : StrongDual ℝ F) : regularCoderiv (fun x ↦ {f x}) x₀ (f x₀) v = {v.comp f'} := by
  have hlo := hf.isLittleO
  have hgr : ((x₀, f x₀) : E × F) ∈ graph fun x ↦ {f x} := rfl
  refine subset_antisymm (fun u hu ↦ ?_) ?_
  · -- `u - v ∘ f'` is a regular normal to `univ`, hence zero
    suffices hN : u - v.comp f' ∈ regularNormalCone (univ : Set E) x₀ by
      rw [regularNormalCone_of_mem_interior (by simp), mem_singleton_iff, sub_eq_zero] at hN
      exact hN
    refine ⟨mem_univ _, fun ε hε ↦ ?_⟩
    rw [nhdsWithin_univ]
    set c₁ : ℝ := ‖f'‖ + 1
    set c₂ : ℝ := ‖v‖ + 1
    have hc₁ : 0 < c₁ := by positivity
    have hc₂ : 0 < c₂ := by positivity
    have hT : Tendsto (fun x ↦ (x, f x)) (𝓝 x₀) (𝓝[graph fun x ↦ {f x}] (x₀, f x₀)) :=
      tendsto_nhdsWithin_iff.2 ⟨(continuous_id.tendsto x₀).prodMk_nhds
        hf.continuousAt.tendsto, Eventually.of_forall fun x ↦ rfl⟩
    filter_upwards [hT.eventually (hu.2 (ε / (2 * c₁)) (by positivity)),
      hlo.def (show (0 : ℝ) < 1 by norm_num), hlo.def (show 0 < ε / (2 * c₂) by positivity)]
      with x h1 h2 h3
    simp only [Prod.mk_sub_mk, ContinuousLinearMap.coprod_apply, neg_apply,
      Prod.norm_mk] at h1
    set h := x - x₀
    have hr : ‖f x - f x₀ - f' h‖ ≤ 1 * ‖h‖ := h2
    have hfx : ‖f x - f x₀‖ ≤ c₁ * ‖h‖ := by
      have := norm_add_le (f' h) (f x - f x₀ - f' h)
      rw [add_sub_cancel] at this
      have := f'.le_opNorm h
      nlinarith [norm_nonneg h]
    have hc1 : 1 ≤ c₁ := show 1 ≤ ‖f'‖ + 1 by linarith [norm_nonneg f']
    have hmax : max ‖h‖ ‖f x - f x₀‖ ≤ c₁ * ‖h‖ :=
      max_le (le_mul_of_one_le_left (norm_nonneg h) hc1) hfx
    have hvr : v (f x - f x₀ - f' h) ≤ ‖v‖ * (ε / (2 * c₂) * ‖h‖) :=
      (le_abs_self _).trans ((v.le_opNorm _).trans (by gcongr))
    have hmain : u h + -v (f x - f x₀) ≤ ε / 2 * ‖h‖ := by
      calc u h + -v (f x - f x₀) ≤ ε / (2 * c₁) * max ‖h‖ ‖f x - f x₀‖ := h1
        _ ≤ ε / (2 * c₁) * (c₁ * ‖h‖) := by gcongr
        _ = ε / 2 * ‖h‖ := by field_simp
    have hv2 : ‖v‖ * (ε / (2 * c₂) * ‖h‖) ≤ ε / 2 * ‖h‖ := by
      have : ‖v‖ / c₂ ≤ 1 := by rw [div_le_one hc₂]; linarith
      calc ‖v‖ * (ε / (2 * c₂) * ‖h‖) = ‖v‖ / c₂ * (ε / 2 * ‖h‖) := by field_simp
        _ ≤ 1 * (ε / 2 * ‖h‖) := by gcongr
        _ = ε / 2 * ‖h‖ := one_mul _
    have e1 : v (f x - f x₀ - f' h) = v (f x - f x₀) - v (f' h) := map_sub _ _ _
    show u h - v (f' h) ≤ ε * ‖h‖
    linarith
  · rintro _ rfl
    refine ⟨hgr, fun ε hε ↦ ?_⟩
    set c : ℝ := ‖v‖ + 1
    have hc : 0 < c := by positivity
    filter_upwards [eventually_graph_of_eventually (P := fun x y ↦
      ‖f x - f x₀ - f' (x - x₀)‖ ≤ ε / c * ‖x - x₀‖ ∧ y = f x)
      ((hlo.def (show 0 < ε / c by positivity)).mono fun x hx ↦ ⟨hx, rfl⟩)] with p hp
    obtain ⟨x, y⟩ := p
    simp only at hp
    obtain ⟨hp1, rfl⟩ := hp
    simp only [Prod.mk_sub_mk, ContinuousLinearMap.coprod_apply, neg_apply,
      ContinuousLinearMap.coe_comp, Function.comp_apply, Prod.norm_mk]
    have h1 : v (f' (x - x₀)) + -v (f x - f x₀) = -v (f x - f x₀ - f' (x - x₀)) := by
      simp only [map_sub]; ring
    rw [h1]
    have h2 : -v (f x - f x₀ - f' (x - x₀)) ≤ ‖v‖ * (ε / c * ‖x - x₀‖) :=
      (neg_le_abs _).trans ((v.le_opNorm _).trans (by gcongr))
    have h3 : ‖v‖ * (ε / c * ‖x - x₀‖) ≤ ε * ‖x - x₀‖ := by
      have : ‖v‖ / c ≤ 1 := by rw [div_le_one hc]; linarith
      calc ‖v‖ * (ε / c * ‖x - x₀‖) = ‖v‖ / c * (ε * ‖x - x₀‖) := by field_simp
        _ ≤ 1 * (ε * ‖x - x₀‖) := by gcongr
        _ = ε * ‖x - x₀‖ := one_mul _
    exact h2.trans (h3.trans (by gcongr; exact le_max_left _ _))

/-- Prop. 1.12 of [Mordukhovich 2018] (coderivatives of smooth mappings): if `f` is
differentiable around `x₀` with derivative continuous at `x₀`, then
`D*f(x₀)(v) = {∇f(x₀)* v}`. -/
theorem coderiv_of_hasFDerivAt_of_continuousAt {f' : E → E →L[ℝ] F}
    (hf : ∀ᶠ x in 𝓝 x₀, HasFDerivAt f (f' x) x) (hc : ContinuousAt f' x₀)
    (v : StrongDual ℝ F) : coderiv (fun x ↦ {f x}) x₀ (f x₀) v = {v.comp (f' x₀)} := by
  refine subset_antisymm (fun u hu ↦ ?_) ?_
  · obtain ⟨-, p, ℓ, hp, hℓ, hmem⟩ := hu
    have hp' := tendsto_nhdsWithin_iff.1 hp
    have hfst : Tendsto (fun k ↦ (p k).1) atTop (𝓝 x₀) := (continuous_fst.tendsto _).comp hp'.1
    -- `ℓₖ = (ℓₖ ∘ inl, -vₖ)` with `ℓₖ ∘ inl = vₖ ∘ f'(xₖ)`
    set w : ℕ → StrongDual ℝ F := fun k ↦ -(ℓ k).comp (ContinuousLinearMap.inr ℝ E F)
    have hw : Tendsto w atTop (𝓝 v) := by
      have := (tendsto_comp_inr hℓ).neg
      simpa [w] using this
    have hkey : ∀ᶠ k in atTop,
        (ℓ k).comp (ContinuousLinearMap.inl ℝ E F) = (w k).comp (f' (p k).1) := by
      filter_upwards [hfst.eventually hf, hp'.2] with k hk hkg
      have hpk : p k = ((p k).1, f (p k).1) := Prod.ext rfl (mem_singleton_iff.1 hkg)
      have hℓk : ((ℓ k).comp (ContinuousLinearMap.inl ℝ E F)) ∈
          regularCoderiv (fun x ↦ {f x}) (p k).1 (f (p k).1) (w k) := by
        show _ ∈ regularNormalCone _ _
        have : ((ℓ k).comp (ContinuousLinearMap.inl ℝ E F)).coprod (-w k) = ℓ k := by
          simp [w]
        rw [this, ← hpk]
        exact hmem k
      rw [regularCoderiv_of_hasFDerivAt hk] at hℓk
      exact hℓk
    have h1 := tendsto_comp_inl hℓ
    have h2 := (tendsto_dual_comp hw (hc.tendsto.comp hfst)).congr'
      (hkey.mono fun k hk ↦ hk.symm)
    have := tendsto_nhds_unique h1 h2
    simpa using this
  · rintro _ rfl
    refine regularCoderiv_subset_coderiv ?_
    rw [regularCoderiv_of_hasFDerivAt hf.self_of_nhds]
    rfl

end Smooth

end VariationalAnalysis
