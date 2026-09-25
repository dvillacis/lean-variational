/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import ConvexAnalysis.Extended.ProperFunction
import VariationalAnalysis.Normal.Product
import VariationalAnalysis.Normal.Transport
import VariationalAnalysis.Subdifferential.Regular

/-!
# Basic (limiting, Mordukhovich) and singular subdifferentials

For `φ : E → EReal` finite at `x₀`, [Mordukhovich 2018, Def. 1.18] defines the basic and the
singular subdifferential through the normal cone to the epigraph:

  `∂φ(x₀) = {v | (v, -1) ∈ N((x₀, φ x₀); epi φ)}`,
  `∂^∞φ(x₀) = {v | (v, 0) ∈ N((x₀, φ x₀); epi φ)}`.

Here `(v, c)` is the dual element `v.coprod c` on `E × ℝ`.

## Main results

* `apply_zero_one_nonpos_of_mem_normalCone_epi`, `mem_normalCone_epi_iff`: Prop. 1.17 of
  [Mordukhovich 2018]: normals to epigraphs are the positive multiples of `(v, -1)`,
  `v ∈ ∂φ(x₀)`, and the `(v, 0)`, `v ∈ ∂^∞φ(x₀)`.
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
open scoped Pointwise

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

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- If `φ xₖ = sₖ` and `φ xₖ → φ x₀ = r`, then `sₖ → r`. -/
theorem tendsto_of_eq_coe {a : ℕ → E} {s : ℕ → ℝ} (hr : φ x₀ = r) (hs : ∀ k, φ (a k) = s k)
    (h : Tendsto (fun k ↦ φ (a k)) atTop (𝓝 (φ x₀))) : Tendsto s atTop (𝓝 r) := by
  have : (fun k ↦ φ (a k)) = fun k ↦ ((s k : ℝ) : EReal) := funext hs
  rw [this, hr] at h
  exact EReal.tendsto_coe.1 h

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
    have hs' : Tendsto s atTop (𝓝 r) := tendsto_of_eq_coe hr (fun k ↦ (hs k).1) ha2
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

/-- Prop. 1.17 of [Mordukhovich 2018] (basic normals to epigraphs): a normal to the epigraph at
`(x₀, φ x₀)` is either a positive multiple of `(v, -1)` with `v ∈ ∂φ(x₀)` or `(v, 0)` with
`v ∈ ∂^∞φ(x₀)`. -/
theorem mem_normalCone_epi_iff (hr : φ x₀ = r) {ℓ : StrongDual ℝ (E × ℝ)} :
    ℓ ∈ normalCone (φ.Epi univ) (x₀, r) ↔
      (∃ μ : ℝ, 0 < μ ∧ ∃ v ∈ subdiff φ x₀, ℓ = μ • v.coprod (-1)) ∨
        ∃ v ∈ singularSubdiff φ x₀, ℓ = v.coprod 0 := by
  constructor
  · intro hℓ
    have hμ := apply_zero_one_nonpos_of_mem_normalCone_epi hℓ
    rcases hμ.lt_or_eq with hlt | heq
    · left
      set μ := -ℓ (0, 1)
      have hμpos : 0 < μ := by simp only [μ]; linarith
      have h1 : (μ⁻¹ • ℓ) (0, 1) = -1 := by
        simp only [smul_apply, smul_eq_mul, μ]
        rw [inv_neg, neg_mul, inv_mul_cancel₀ hlt.ne]
      refine ⟨μ, hμpos, (μ⁻¹ • ℓ).comp (ContinuousLinearMap.inl ℝ E ℝ), ?_, ?_⟩
      · rw [mem_subdiff_iff hr, ← eq_coprod_neg_one _ h1]
        exact smul_mem_normalCone hℓ (inv_nonneg.2 hμpos.le)
      · rw [← eq_coprod_neg_one _ h1, smul_smul, mul_inv_cancel₀ hμpos.ne', one_smul]
    · right
      refine ⟨ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ), ?_, eq_coprod_zero ℓ heq⟩
      rw [mem_singularSubdiff_iff hr, ← eq_coprod_zero ℓ heq]
      exact hℓ
  · rintro (⟨μ, hμ, v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
    · exact smul_mem_normalCone ((mem_subdiff_iff hr).1 hv) hμ.le
    · exact (mem_singularSubdiff_iff hr).1 hv

section Robustness

/-- Outer limits of the sets `{v | (v, c) ∈ N((x, φ x); epi φ)}` along `x →φ x₀`. -/
private theorem outerLimit_coprod_normalCone_subset (c : StrongDual ℝ ℝ) (hr : φ x₀ = r) :
    outerLimit (funNhds φ x₀)
        (fun x ↦ {v : StrongDual ℝ E | ∃ s : ℝ, φ x = s ∧
          v.coprod c ∈ normalCone (φ.Epi univ) (x, s)}) ⊆
      {v : StrongDual ℝ E | v.coprod c ∈ normalCone (φ.Epi univ) (x₀, r)} := by
  rintro v ⟨a, w, ha, hw, hmem⟩
  obtain ⟨ha1, ha2⟩ := tendsto_funNhds_iff.1 ha
  choose s hs using hmem
  have hs' : Tendsto s atTop (𝓝 r) := tendsto_of_eq_coe hr (fun k ↦ (hs k).1) ha2
  have hmem₀ : ((x₀, r) : E × ℝ) ∈ φ.Epi univ := ⟨mem_univ _, hr.le⟩
  show v.coprod c ∈ normalCone (φ.Epi univ) (x₀, r)
  rw [normalCone_eq_outerLimit_normalCone hmem₀]
  exact ⟨fun k ↦ (a k, s k), fun k ↦ (w k).coprod c, tendsto_nhdsWithin_iff.2
    ⟨ha1.prodMk_nhds hs', Eventually.of_forall fun k ↦ ⟨mem_univ _, (hs k).1.le⟩⟩,
    tendsto_coprod hw tendsto_const_nhds, fun k ↦ (hs k).2⟩

/-- Prop. 1.20 of [Mordukhovich 2018] (robustness of the basic subdifferential):
`∂φ(x₀) = Lim sup_{x →φ x₀} ∂φ(x)`. -/
theorem subdiff_eq_outerLimit_subdiff (hr : φ x₀ = r) :
    subdiff φ x₀ = outerLimit (funNhds φ x₀) (subdiff φ) :=
  subset_antisymm (subset_outerLimit (pure_le_funNhds φ x₀) _) fun _ hv ↦
    ⟨r, hr, outerLimit_coprod_normalCone_subset (-1) hr hv⟩

/-- Prop. 1.20 of [Mordukhovich 2018] (robustness of the singular subdifferential):
`∂^∞φ(x₀) = Lim sup_{x →φ x₀} ∂^∞φ(x)`. -/
theorem singularSubdiff_eq_outerLimit_singularSubdiff (hr : φ x₀ = r) :
    singularSubdiff φ x₀ = outerLimit (funNhds φ x₀) (singularSubdiff φ) :=
  subset_antisymm (subset_outerLimit (pure_le_funNhds φ x₀) _) fun _ hv ↦
    ⟨r, hr, outerLimit_coprod_normalCone_subset 0 hr hv⟩

end Robustness

section Indicator

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem epi_convex_indicator (Ω : Set E) : Ω.convex_indicator.Epi univ = Ω ×ˢ Ici 0 := by
  ext ⟨x, α⟩
  by_cases hx : x ∈ Ω
  · simp [Function.Epi, convex_indicator_of_mem hx, hx]
  · simp [Function.Epi, convex_indicator_of_notMem hx, hx]

/-- Prop. 1.19 of [Mordukhovich 2018] (singular subgradients of indicator functions):
`∂^∞δ_Ω(x₀) = N(x₀; Ω)`. -/
theorem singularSubdiff_convex_indicator (Ω : Set E) :
    singularSubdiff Ω.convex_indicator x₀ = normalCone Ω x₀ := by
  by_cases hx : x₀ ∈ Ω
  · ext v
    rw [mem_singularSubdiff_iff (convex_indicator_of_mem hx), epi_convex_indicator,
      coprod_mem_normalCone_prod_iff]
    simp [zero_mem_normalCone (mem_Ici.2 (le_refl (0 : ℝ)))]
  · ext v
    simp only [normalCone, mem_ofPred_eq, hx, false_and, iff_false]
    rintro ⟨r, hr, -⟩
    rw [convex_indicator_of_notMem hx] at hr
    exact EReal.coe_ne_top r hr.symm

end Indicator

section Convex

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem mem_dom_iff_exists_le {x : E} : x ∈ dom univ φ ↔ ∃ α : ℝ, φ x ≤ α := by
  simp only [dom, mem_univ, true_and, mem_ofPred_eq]
  constructor
  · intro h
    induction hφ : φ x with
    | bot => exact ⟨0, bot_le⟩
    | top => rw [hφ] at h; exact absurd h (lt_irrefl _)
    | coe s => exact ⟨s, le_rfl⟩
  · rintro ⟨α, hα⟩
    exact hα.trans_lt (EReal.coe_lt_top α)

/-- Prop. 1.25 of [Mordukhovich 2018] (singular subgradients of convex functions): if the
epigraph of `φ` is convex, then `∂^∞φ(x₀) = N(x₀; dom φ)`. -/
theorem singularSubdiff_eq_normalCone_dom_of_convex (hconv : Convex ℝ (φ.Epi univ))
    (hr : φ x₀ = r) : singularSubdiff φ x₀ = normalCone (dom univ φ) x₀ := by
  have hdom : dom univ φ = LinearMap.fst ℝ E ℝ '' φ.Epi univ := by
    ext x
    rw [mem_dom_iff_exists_le]
    constructor
    · rintro ⟨α, hα⟩; exact ⟨(x, α), ⟨mem_univ _, hα⟩, rfl⟩
    · rintro ⟨⟨y, α⟩, ⟨-, hα⟩, rfl⟩; exact ⟨α, hα⟩
  have hdomc : Convex ℝ (dom univ φ) := hdom ▸ hconv.linear_image _
  have hx₀ : x₀ ∈ dom univ φ := mem_dom_iff_exists_le.2 ⟨r, hr.le⟩
  ext v
  rw [mem_singularSubdiff_iff hr, mem_normalCone_of_convex hconv ⟨mem_univ _, hr.le⟩,
    mem_normalCone_of_convex hdomc hx₀]
  constructor
  · intro h x hx
    obtain ⟨α, hα⟩ := mem_dom_iff_exists_le.1 hx
    simpa using h (x, α) ⟨mem_univ _, hα⟩
  · rintro h ⟨x, α⟩ ⟨-, hα⟩
    simpa using h x (mem_dom_iff_exists_le.2 ⟨α, hα⟩)

end Convex

section SumRule

/-- `y + c + (-c) = y` in `EReal` for real `c`. -/
theorem add_coe_add_coe_neg (y : EReal) (c : ℝ) : y + c + ((-c : ℝ) : EReal) = y := by
  induction y with
  | bot => simp
  | top => simp
  | coe y => rw [← EReal.coe_add, ← EReal.coe_add]; congr 1; ring

/-- Prop. 1.30(ii) of [Mordukhovich 2018], Cor. 25.27 of [Clason–Valkonen] (sum rule with a
`C¹` addition): if `f` is differentiable around `x₀` with derivative continuous at `x₀`, then
`∂(φ + f)(x₀) = ∂φ(x₀) + ∇f(x₀)`. -/
theorem mem_subdiff_add_iff {f : E → ℝ} {f' : E → StrongDual ℝ E}
    (hf : ∀ᶠ x in 𝓝 x₀, HasFDerivAt f (f' x) x) (hc : ContinuousAt f' x₀) :
    v ∈ subdiff (fun x ↦ φ x + f x) x₀ ↔ v - f' x₀ ∈ subdiff φ x₀ := by
  have hfc : ContinuousAt f x₀ := hf.self_of_nhds.continuousAt
  by_cases hfin : ∃ r : ℝ, φ x₀ = r
  swap
  · push Not at hfin
    refine ⟨fun ⟨s, hs, _⟩ ↦ absurd ?_ (hfin (s - f x₀)), fun ⟨r, hr, _⟩ ↦ absurd hr (hfin r)⟩
    have := congrArg (fun y : EReal ↦ y + ((-f x₀ : ℝ) : EReal)) hs
    simp only [add_coe_add_coe_neg] at this
    rw [this, ← EReal.coe_add, sub_eq_add_neg]
  obtain ⟨r, hr⟩ := hfin
  have hr' : (fun x ↦ φ x + f x) x₀ = ((r + f x₀ : ℝ) : EReal) := by simp [hr]
  rw [subdiff_eq_outerLimit (φ := fun x ↦ φ x + f x) (x₀ := x₀) hr', subdiff_eq_outerLimit hr]
  constructor
  · rintro ⟨a, w, ha, hw, hmem⟩
    obtain ⟨ha1, ha2⟩ := tendsto_funNhds_iff.1 ha
    refine mem_outerLimit_of_eventually a (fun k ↦ w k - f' (a k))
      (tendsto_funNhds_iff.2 ⟨ha1, ?_⟩) (hw.sub (hc.tendsto.comp ha1)) ?_
    · have h1 := ((EReal.continuousAt_add_coe_coe (r + f x₀) (-f x₀)).tendsto.comp
        ((by simpa [hr'] using ha2 : Tendsto (fun k ↦ φ (a k) + f (a k)) atTop
          (𝓝 ((r + f x₀ : ℝ) : EReal))).prodMk_nhds
          (EReal.tendsto_coe.2 (hfc.tendsto.comp ha1).neg)))
      rw [hr]
      have e0 : ((r + f x₀ : ℝ) : EReal) + ((-f x₀ : ℝ) : EReal) = (r : EReal) := by
        rw [← EReal.coe_add]; congr 1; ring
      simp only [Function.comp_def, add_coe_add_coe_neg, e0] at h1
      exact h1
    · filter_upwards [ha1.eventually hf] with k hk using (mem_regularSubdiff_add_iff hk).1 (hmem k)
  · rintro ⟨a, w, ha, hw, hmem⟩
    obtain ⟨ha1, ha2⟩ := tendsto_funNhds_iff.1 ha
    refine mem_outerLimit_of_eventually a (fun k ↦ w k + f' (a k))
      (tendsto_funNhds_iff.2 ⟨ha1, ?_⟩) (by simpa using hw.add (hc.tendsto.comp ha1)) ?_
    · have h1 := ((EReal.continuousAt_add_coe_coe r (f x₀)).tendsto.comp
        ((by simpa [hr] using ha2 : Tendsto (fun k ↦ φ (a k)) atTop (𝓝 (r : EReal))).prodMk_nhds
          (EReal.tendsto_coe.2 (hfc.tendsto.comp ha1))))
      simpa [Function.comp_def, hr', ← EReal.coe_add] using h1
    · filter_upwards [ha1.eventually hf] with k hk
      exact (mem_regularSubdiff_add_iff hk).2 (by simpa using hmem k)

end SumRule

section LimitingRepresentations

/-- Thm. 1.28, (1.37), of [Mordukhovich 2018], representation through `ω`-subgradients: in
finite dimensions, if the epigraph of `φ` is locally closed around `(x₀, φ x₀)`, then
`∂φ(x₀) = Lim sup_{x →φ x₀, ω ↓ 0} ∂̂_ω φ(x)`. -/
theorem subdiff_eq_outerLimit_epsSubdiff [FiniteDimensional ℝ E] (hr : φ x₀ = r)
    (hloc : ∃ ρ > 0, IsClosed (φ.Epi univ ∩ Metric.closedBall ((x₀, r) : E × ℝ) ρ)) :
    subdiff φ x₀ =
      outerLimit (funNhds φ x₀ ×ˢ 𝓝[≥] (0 : ℝ)) (fun p ↦ epsSubdiff p.2 φ p.1) := by
  refine subset_antisymm (fun v hv ↦ ?_) (fun v hv ↦ ?_)
  · rw [subdiff_eq_outerLimit hr] at hv
    obtain ⟨a, w, ha, hw, hmem⟩ := hv
    refine ⟨fun k ↦ (a k, 0), w, ha.prodMk (tendsto_nhdsWithin_iff.2
      ⟨tendsto_const_nhds, Eventually.of_forall fun _ ↦ mem_Ici.2 le_rfl⟩), hw, fun k ↦ ?_⟩
    simpa [epsSubdiff_zero] using hmem k
  obtain ⟨p, w, hp, hw, hmem⟩ := hv
  have hpa₀ : Tendsto (fun k ↦ (p k).1) atTop (funNhds φ x₀) := tendsto_fst.comp hp
  have hpω₀ : Tendsto (fun k ↦ (p k).2) atTop (𝓝[≥] (0 : ℝ)) := tendsto_snd.comp hp
  obtain ⟨ha1, ha2⟩ := tendsto_funNhds_iff.1 hpa₀
  have hpω := tendsto_nhdsWithin_iff.1 hpω₀
  choose s hs using hmem
  have hs' : Tendsto s atTop (𝓝 r) := tendsto_of_eq_coe hr (fun k ↦ (hs k).1) ha2
  have hmem₀ : ((x₀, r) : E × ℝ) ∈ φ.Epi univ := ⟨mem_univ _, hr.le⟩
  refine ⟨r, hr, ?_⟩
  rw [normalCone_eq_outerLimit_epsNormalCone hmem₀ hloc]
  have hT : Tendsto (fun k ↦ ((p k).1, s k)) atTop (𝓝[φ.Epi univ] (x₀, r)) :=
    tendsto_nhdsWithin_iff.2 ⟨ha1.prodMk_nhds hs',
      Eventually.of_forall fun k ↦ ⟨mem_univ _, (hs k).1.le⟩⟩
  refine mem_outerLimit_of_eventually (fun k ↦ (((p k).1, s k), (p k).2))
    (fun k ↦ (w k).coprod (-1)) (hT.prodMk hpω₀) (tendsto_coprod hw tendsto_const_nhds) ?_
  filter_upwards [hpω.2] with k hk
  exact coprod_mem_epsNormalCone_of_mem_epsSubdiff hk (hs k).1 ⟨s k, (hs k).1, (hs k).2⟩

/-- Thm. 1.28, (1.38), of [Mordukhovich 2018], inclusion `⊇`: limits of `λ ∂̂φ(x)` as
`x →φ x₀` and `λ ↓ 0` are singular subgradients. -/
theorem outerLimit_smul_regularSubdiff_subset_singularSubdiff (hr : φ x₀ = r) :
    outerLimit (funNhds φ x₀ ×ˢ 𝓝[>] (0 : ℝ)) (fun p ↦ p.2 • regularSubdiff φ p.1) ⊆
      singularSubdiff φ x₀ := by
  rintro v ⟨p, w, hp, hw, hmem⟩
  have hpa₀ : Tendsto (fun k ↦ (p k).1) atTop (funNhds φ x₀) := tendsto_fst.comp hp
  have hpl₀ : Tendsto (fun k ↦ (p k).2) atTop (𝓝[>] (0 : ℝ)) := tendsto_snd.comp hp
  obtain ⟨ha1, ha2⟩ := tendsto_funNhds_iff.1 hpa₀
  have hpl := tendsto_nhdsWithin_iff.1 hpl₀
  choose u hu hwu using fun k ↦ Set.mem_smul_set.1 (hmem k)
  choose s hs using hu
  have hs' : Tendsto s atTop (𝓝 r) := tendsto_of_eq_coe hr (fun k ↦ (hs k).1) ha2
  have hmem₀ : ((x₀, r) : E × ℝ) ∈ φ.Epi univ := ⟨mem_univ _, hr.le⟩
  refine ⟨r, hr, hmem₀, ?_⟩
  refine mem_outerLimit_of_eventually (fun k ↦ ((p k).1, s k))
    (fun k ↦ (w k).coprod ((p k).2 • (-1 : StrongDual ℝ ℝ))) (tendsto_nhdsWithin_iff.2
      ⟨ha1.prodMk_nhds hs', Eventually.of_forall fun k ↦ ⟨mem_univ _, (hs k).1.le⟩⟩) ?_ ?_
  · have := tendsto_coprod hw (hpl.1.smul_const (-1 : StrongDual ℝ ℝ))
    simpa using this
  · filter_upwards [hpl.2] with k hk
    have hN := (mem_regularSubdiff_iff_coprod_mem (hs k).1).1 ⟨s k, (hs k).1, (hs k).2⟩
    have hk' := smul_mem_regularNormalCone hN (le_of_lt (mem_Ioi.1 hk))
    have heq : (p k).2 • (u k).coprod (-1 : StrongDual ℝ ℝ) =
        (w k).coprod ((p k).2 • (-1 : StrongDual ℝ ℝ)) := by
      rw [← hwu k]; ext <;> simp
    rwa [heq] at hk'

end LimitingRepresentations

end VariationalAnalysis
