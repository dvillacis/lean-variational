/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import VariationalAnalysis.Normal.Limiting
import VariationalAnalysis.Subdifferential.Regular

/-!
# Basic (limiting, Mordukhovich) and singular subdifferentials

For `φ : E → EReal` finite at `x₀`, [Mordukhovich 2018, Def. 1.18] defines the basic and the
singular subdifferential through the normal cone to the epigraph:

  `∂φ(x₀) = {v | (v, -1) ∈ N((x₀, φ x₀); epi φ)}`,  `∂^∞φ(x₀) = {v | (v, 0) ∈ N((x₀, φ x₀); epi φ)}`.

Here `(v, c)` is the dual element `v.coprod c` on `E × ℝ`.

## Main results

* `apply_zero_one_nonpos_of_mem_normalCone_epi`: Prop. 1.17 of [Mordukhovich 2018]: normals
  `ℓ` to epigraphs have `ℓ (0, 1) ≤ 0`.
* `subdiff_eq_outerLimit`: Thm. 1.28, (1.37), of [Mordukhovich 2018]: `∂φ(x₀)` is the outer
  limit of `∂̂φ(x)` as `x →φ x₀` ([Clason–Valkonen, (16.5)] in finite dimensions).
* `regularSubdiff_subset_subdiff`, `zero_mem_subdiff_of_isLocalMin`: Prop. 1.30(i) of
  [Mordukhovich 2018] (generalized Fermat rule), [Clason–Valkonen, Cor. 16.6].
* `subdiff_of_hasFDerivAt_of_continuousAt`: Cor. 1.24 of [Mordukhovich 2018],
  [Clason–Valkonen, Thm. 16.9]: `∂f(x₀) = {∇f(x₀)}` for `f` of class `C¹` around `x₀`.
* `subdiff_convex_indicator`: Prop. 1.19 of [Mordukhovich 2018]: `∂δ_Ω(x₀) = N(x₀; Ω)`.
* `subdiff_eq_regularSubdiff_of_convex`, `mem_subdiff_of_convex`: Prop. 1.25, (1.35), of
  [Mordukhovich 2018]: for convex functions the basic subdifferential is the subdifferential of
  convex analysis ([Clason–Valkonen, Thm. 16.8] in finite dimensions).
-/

open Filter Topology Set

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {φ : E → EReal} {x₀ : E} {v : StrongDual ℝ E} {r : ℝ}

/-- The basic (limiting, Mordukhovich) subdifferential [Mordukhovich 2018, Def. 1.18, (1.24)].
Empty unless `φ x₀` is finite. -/
def subdiff (φ : E → EReal) (x₀ : E) : Set (StrongDual ℝ E) :=
  {v | ∃ r : ℝ, φ x₀ = r ∧ v.coprod (-1) ∈ normalCone (φ.Epi univ) (x₀, r)}

/-- The singular subdifferential [Mordukhovich 2018, Def. 1.18, (1.25)]. Empty unless `φ x₀` is
finite. -/
def singularSubdiff (φ : E → EReal) (x₀ : E) : Set (StrongDual ℝ E) :=
  {v | ∃ r : ℝ, φ x₀ = r ∧ v.coprod 0 ∈ normalCone (φ.Epi univ) (x₀, r)}

theorem mem_subdiff_iff (hr : φ x₀ = r) :
    v ∈ subdiff φ x₀ ↔ v.coprod (-1) ∈ normalCone (φ.Epi univ) (x₀, r) := by
  refine ⟨fun ⟨s, hs, h⟩ ↦ ?_, fun h ↦ ⟨r, hr, h⟩⟩
  rw [hr, EReal.coe_eq_coe_iff] at hs
  exact hs ▸ h

theorem mem_singularSubdiff_iff (hr : φ x₀ = r) :
    v ∈ singularSubdiff φ x₀ ↔ v.coprod 0 ∈ normalCone (φ.Epi univ) (x₀, r) := by
  refine ⟨fun ⟨s, hs, h⟩ ↦ ?_, fun h ↦ ⟨r, hr, h⟩⟩
  rw [hr, EReal.coe_eq_coe_iff] at hs
  exact hs ▸ h

theorem zero_mem_singularSubdiff (hr : φ x₀ = r) :
    (0 : StrongDual ℝ E) ∈ singularSubdiff φ x₀ := by
  rw [mem_singularSubdiff_iff hr]
  have h0 : (0 : StrongDual ℝ E).coprod (0 : StrongDual ℝ ℝ) = 0 := by ext <;> simp
  rw [h0]
  exact zero_mem_normalCone (Ω := φ.Epi univ) (x₀ := (x₀, r)) ⟨mem_univ x₀, hr.le⟩

/-- Prop. 1.17 of [Mordukhovich 2018]: a normal `ℓ` to the epigraph satisfies `ℓ (0, 1) ≤ 0`. -/
theorem apply_zero_one_nonpos_of_mem_normalCone_epi {p : E × ℝ} {ℓ : StrongDual ℝ (E × ℝ)}
    (hℓ : ℓ ∈ normalCone (φ.Epi univ) p) : ℓ (0, 1) ≤ 0 := by
  obtain ⟨-, a, w, -, hw, hmem⟩ := hℓ
  exact le_of_tendsto (tendsto_dual_apply hw tendsto_const_nhds)
    (Eventually.of_forall fun k ↦ apply_zero_one_nonpos_of_mem_regularNormalCone_epi (hmem k))

/-- Thm. 1.28, (1.37), of [Mordukhovich 2018] (limiting representation of basic subgradients):
`∂φ(x₀) = Lim sup_{x →φ x₀} ∂̂φ(x)`. -/
theorem subdiff_eq_outerLimit (hr : φ x₀ = r) :
    subdiff φ x₀ = outerLimit (funNhds φ x₀) (regularSubdiff φ) := by
  ext v
  rw [mem_subdiff_iff hr]
  constructor
  · rintro ⟨-, p, ℓ, hp, hℓ, hmem⟩
    have hp' := tendsto_nhdsWithin_iff.1 hp
    have hfst : Tendsto (fun k ↦ (p k).1) atTop (𝓝 x₀) := (continuous_fst.tendsto _).comp hp'.1
    have hsnd : Tendsto (fun k ↦ (p k).2) atTop (𝓝 r) := (continuous_snd.tendsto _).comp hp'.1
    -- `ℓₖ (0, 1) → -1`
    have h01 : Tendsto (fun k ↦ ℓ k (0, 1)) atTop (𝓝 (-1)) := by
      simpa using tendsto_dual_apply hℓ (tendsto_const_nhds (x := ((0 : E), (1 : ℝ))))
    have hneg : ∀ᶠ k in atTop, ℓ k (0, 1) < 0 := (tendsto_order.1 h01).2 0 (by norm_num)
    have hgraph : ∀ᶠ k in atTop, φ (p k).1 = (p k).2 := hneg.mono fun k hk ↦
      eq_of_mem_regularNormalCone_epi (by simpa using hmem k) hk
    set μ : ℕ → ℝ := fun k ↦ -ℓ k (0, 1)
    have hμ : Tendsto μ atTop (𝓝 1) := by simpa using h01.neg
    set u : ℕ → StrongDual ℝ E := fun k ↦ (μ k)⁻¹ • (ℓ k).comp (ContinuousLinearMap.inl ℝ E ℝ)
    refine mem_outerLimit_of_eventually (fun k ↦ (p k).1) u
      (tendsto_funNhds_iff.2 ⟨hfst, ?_⟩) ?_ ?_
    · rw [hr]
      exact ((continuous_coe_real_ereal.tendsto r).comp hsnd).congr'
        (hgraph.mono fun k hk ↦ hk.symm)
    · have := (hμ.inv₀ one_ne_zero).smul (tendsto_comp_inl hℓ)
      simpa using this
    · filter_upwards [hneg, hgraph] with k hk hkg
      have hμpos : 0 < μ k := by simp only [μ]; linarith
      have hg : (μ k)⁻¹ • ℓ k ∈ regularNormalCone (φ.Epi univ) ((p k).1, (p k).2) :=
        smul_mem_regularNormalCone (by simpa using hmem k) (inv_nonneg.2 hμpos.le)
      have h1 : ((μ k)⁻¹ • ℓ k) (0, 1) = -1 := by
        have hne : ℓ k (0, 1) ≠ 0 := hk.ne
        simp only [smul_apply, smul_eq_mul, μ]
        field_simp
      have hg' := eq_coprod_neg_one _ h1 ▸ hg
      have := (mem_regularSubdiff_iff_coprod_mem hkg).2 hg'
      simpa [u, ContinuousLinearMap.smul_comp] using this
  · rintro ⟨a, w, ha, hw, hmem⟩
    obtain ⟨ha1, ha2⟩ := tendsto_funNhds_iff.1 ha
    choose s hs using fun k ↦ hmem k
    have hs' : Tendsto s atTop (𝓝 r) := by
      have : Tendsto (fun k ↦ (s k : EReal)) atTop (𝓝 (r : EReal)) := by
        rw [← hr]; simpa [fun k ↦ (hs k).1] using ha2
      exact EReal.tendsto_coe.1 this
    refine ⟨⟨mem_univ _, hr.le⟩, fun k ↦ (a k, s k), fun k ↦ (w k).coprod (-1), ?_,
      tendsto_coprod hw tendsto_const_nhds, fun k ↦ ?_⟩
    · exact tendsto_nhdsWithin_iff.2 ⟨ha1.prodMk_nhds hs',
        Eventually.of_forall fun k ↦ ⟨mem_univ _, (hs k).1.le⟩⟩
    · exact (mem_regularSubdiff_iff_coprod_mem (hs k).1).1 (hmem k)

/-- `∂̂φ(x₀) ⊆ ∂φ(x₀)` [Mordukhovich 2018, p. 33]. -/
theorem regularSubdiff_subset_subdiff : regularSubdiff φ x₀ ⊆ subdiff φ x₀ := by
  rintro v ⟨r, hr, hv⟩
  rw [subdiff_eq_outerLimit hr]
  exact subset_outerLimit (pure_le_funNhds φ x₀) _ ⟨r, hr, hv⟩

/-- Prop. 1.30(i) of [Mordukhovich 2018], Cor. 16.6 of [Clason–Valkonen] (generalized Fermat
rule for basic subgradients). -/
theorem zero_mem_subdiff_of_isLocalMin (hmin : IsLocalMin φ x₀) (hr : φ x₀ = r) :
    (0 : StrongDual ℝ E) ∈ subdiff φ x₀ :=
  regularSubdiff_subset_subdiff (zero_mem_regularSubdiff_of_isLocalMin hmin hr)

/-- Cor. 1.24 of [Mordukhovich 2018], Thm. 16.9 of [Clason–Valkonen] (subgradients of smooth
functions): if `f` is differentiable around `x₀` with derivative continuous at `x₀`, then
`∂f(x₀) = {f'(x₀)}`. -/
theorem subdiff_of_hasFDerivAt_of_continuousAt {f : E → ℝ} {f' : E → StrongDual ℝ E}
    (hf : ∀ᶠ x in 𝓝 x₀, HasFDerivAt f (f' x) x) (hc : ContinuousAt f' x₀) :
    subdiff (fun x ↦ (f x : EReal)) x₀ = {f' x₀} := by
  refine subset_antisymm (fun v hv ↦ ?_) ?_
  · rw [subdiff_eq_outerLimit (φ := fun x ↦ (f x : EReal)) (r := f x₀) rfl] at hv
    obtain ⟨a, w, ha, hw, hmem⟩ := hv
    have ha' := (tendsto_funNhds_iff.1 ha).1
    have hweq : ∀ᶠ k in atTop, w k = f' (a k) := (ha'.eventually hf).mono fun k hk ↦ by
      simpa [regularSubdiff_of_hasFDerivAt hk] using hmem k
    exact mem_singleton_iff.2 (tendsto_nhds_unique hw ((hc.tendsto.comp ha').congr'
      (hweq.mono fun k hk ↦ hk.symm)))
  · rintro _ rfl
    apply regularSubdiff_subset_subdiff
    rw [regularSubdiff_of_hasFDerivAt hf.self_of_nhds]
    rfl

omit [NormedSpace ℝ E] in
/-- `x →δ_Ω x₀` is `x →Ω x₀` for `x₀ ∈ Ω`. -/
theorem funNhds_convex_indicator {Ω : Set E} (hx : x₀ ∈ Ω) :
    funNhds Ω.convex_indicator x₀ = 𝓝[Ω] x₀ := by
  have hcomap : comap Ω.convex_indicator (𝓝 (Ω.convex_indicator x₀)) = 𝓟 Ω := by
    rw [convex_indicator_of_mem hx]
    refine le_antisymm ?_ ?_
    · rw [le_principal_iff]
      refine ⟨Iio ⊤, Iio_mem_nhds (EReal.coe_lt_top 0), fun x hx' ↦ ?_⟩
      by_contra hxΩ
      rw [mem_preimage, convex_indicator_of_notMem hxΩ] at hx'
      exact lt_irrefl _ (mem_Iio.1 hx')
    · rw [← tendsto_iff_comap]
      exact tendsto_const_nhds.congr' ((eventually_principal.2 fun x hx' ↦
        (convex_indicator_of_mem hx').symm))
  rw [funNhds, hcomap, nhdsWithin]

/-- Prop. 1.19 of [Mordukhovich 2018] (basic subgradients of indicator functions):
`∂δ_Ω(x₀) = N(x₀; Ω)`. -/
theorem subdiff_convex_indicator (Ω : Set E) :
    subdiff Ω.convex_indicator x₀ = normalCone Ω x₀ := by
  by_cases hx : x₀ ∈ Ω
  · rw [subdiff_eq_outerLimit (convex_indicator_of_mem hx), funNhds_convex_indicator hx]
    ext v
    simp only [normalCone, mem_ofPred_eq, hx, true_and]
    rw [show regularSubdiff Ω.convex_indicator = regularNormalCone Ω from
      funext fun _ ↦ regularSubdiff_convex_indicator Ω]
  · ext v
    simp only [normalCone, mem_ofPred_eq, hx, false_and, iff_false]
    rintro ⟨r, hr, -⟩
    rw [convex_indicator_of_notMem hx] at hr
    exact EReal.coe_ne_top r hr.symm

/-- Prop. 1.25, (1.35), of [Mordukhovich 2018]: for a function with convex epigraph the basic
and regular subdifferentials agree ([Clason–Valkonen, Thm. 16.8] in finite dimensions). -/
theorem subdiff_eq_regularSubdiff_of_convex (hconv : Convex ℝ (φ.Epi univ)) :
    subdiff φ x₀ = regularSubdiff φ x₀ := by
  refine subset_antisymm (fun v ⟨r, hr, hv⟩ ↦ ?_) regularSubdiff_subset_subdiff
  rw [normalCone_eq_regularNormalCone_of_convex hconv] at hv
  exact (mem_regularSubdiff_iff_coprod_mem hr).2 hv

/-- Prop. 1.25, (1.35), of [Mordukhovich 2018]: for a function with convex epigraph, basic
subgradients are the subgradients of convex analysis. -/
theorem mem_subdiff_of_convex (hconv : Convex ℝ (φ.Epi univ)) (hr : φ x₀ = r) :
    v ∈ subdiff φ x₀ ↔ ∀ x, ((r + v (x - x₀) : ℝ) : EReal) ≤ φ x := by
  rw [subdiff_eq_regularSubdiff_of_convex hconv, mem_regularSubdiff_of_convex hconv hr]

end VariationalAnalysis
