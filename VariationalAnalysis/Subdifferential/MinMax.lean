/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import VariationalAnalysis.Subdifferential.ChainRule
import VariationalAnalysis.Subdifferential.ProductRule

/-!
# Subdifferentiation of minima and maxima

Prop. 4.9 and Thm. 4.10 of [Mordukhovich 2018]: subgradients of `min φᵢ` and `max φᵢ` for
finitely many functions `φᵢ : E → EReal` (indexed by a finite type `ι`), with the active index
sets `I_min(x₀)`, `I_max(x₀)` (`maxActive`) and the multipliers
`Λ(x₀) = {θ | θᵢ ≥ 0, ∑ θᵢ = 1, θᵢ (φᵢ(x₀) - max φⱼ(x₀)) = 0}` (`maxMultipliers`).

Both results are proved on epigraphs. For the minimum, `epi (min φᵢ) = ⋃ epi φᵢ` and a normal to
a finite union at a point is a normal to one of the sets containing it; this handles basic and
singular subgradients alike, so the missing inclusion `⊆` of (1.38) used in the book is not
needed. For the maximum, `epi (max φᵢ) = ⋂ epi φᵢ` coincides near `(x₀, max φᵢ(x₀))` with the
intersection over the active indices (upper semicontinuity of the inactive ones), and Cor. 2.17
applies. The epi-regular equality statement of Thm. 4.10(i) only needs Cor. 2.17 and its regular
counterpart. Thm. 4.10(ii) is Cor. 4.6 for `max ∘ (f₁, …, fₛ)` with `max` on `ι → ℝ` (`vecMax`),
whose subgradients are the `θ ∈ Λ` (`mem_maxMultipliers_of_mem_subdiff_vecMax`); its equality
statement compares `∑ θᵢ fᵢ ≤ max fᵢ` (equality at `x₀`) through regular subgradients.

## Main results

* `subdiff_iInf_subset`, `singularSubdiff_iInf_subset`: Prop. 4.9, (4.15), (4.16).
* `subdiff_iSup_subset`, `singularSubdiff_iSup_subset`: Thm. 4.10(i) (`θ ∘ ∂φ` is
  `smulSubdiff`).
* `iSup_eq_of_epiRegularAt`: Thm. 4.10(i), equalities and epigraphical regularity.
* `subdiff_iSup_lipschitz_subset`: Thm. 4.10(ii).
* `iSup_lipschitz_eq_of_lowerRegularAt`: Thm. 4.10(ii), equality and lower regularity.
-/

open Filter Topology Set Metric
open scoped Pointwise NNReal

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} {φ : ι → E → EReal} {x₀ : E} {r : ℝ}

section Minimum

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The epigraph of a finite minimum is the union of the epigraphs. -/
theorem epi_iInf [Finite ι] [Nonempty ι] :
    (fun x ↦ ⨅ i, φ i x).Epi univ = ⋃ i, (φ i).Epi univ := by
  ext p
  simp only [Function.Epi, mem_ofPred_eq, mem_univ, true_and, mem_iUnion]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun i ↦ φ i p.1)
    exact ⟨i, hi ▸ h⟩
  · rintro ⟨i, hi⟩
    exact (iInf_le (fun i ↦ φ i p.1) i).trans hi

omit [NormedSpace ℝ E] in
/-- A limit `f z ≤ t` of points `(zₖ, tₖ)` of the epigraph of a function lower semicontinuous
at `z`. -/
theorem le_of_tendsto_epi {f : E → EReal} {z : E} {t : ℝ} (hf : LowerSemicontinuousAt f z)
    {p : ℕ → E × ℝ} (hp : Tendsto p atTop (𝓝 (z, t))) (hmem : ∀ k, p k ∈ f.Epi univ) :
    f z ≤ t := by
  refine le_of_forall_lt_imp_le_of_dense fun c hc ↦ ?_
  have h1 := ((continuous_fst.tendsto (z, t)).comp hp).eventually (hf c hc)
  have h2 : Tendsto (fun k ↦ ((p k).2 : EReal)) atTop (𝓝 (t : EReal)) :=
    EReal.tendsto_coe.2 ((continuous_snd.tendsto (z, t)).comp hp)
  exact ge_of_tendsto h2 (h1.mono fun k hk ↦ (hk.trans_le (hmem k).2).le)

/-- [Mordukhovich 2018, proof of Prop. 4.9], in geometric form: for finitely many functions
lower semicontinuous at `x₀`, a normal to the epigraph of `min φᵢ` at `(x₀, min φᵢ(x₀))` is a
normal to the epigraph of some active `φᵢ` at the same point. -/
theorem exists_mem_normalCone_epi_of_iInf [Finite ι] (hl : ∀ i, LowerSemicontinuousAt (φ i) x₀)
    (hr : ⨅ i, φ i x₀ = r) {ℓ : StrongDual ℝ (E × ℝ)}
    (hℓ : ℓ ∈ normalCone ((fun x ↦ ⨅ i, φ i x).Epi univ) (x₀, r)) :
    ∃ i, φ i x₀ = r ∧ ℓ ∈ normalCone ((φ i).Epi univ) (x₀, r) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [iInf_of_empty] at hr; exact absurd hr.symm (EReal.coe_ne_top r)
  obtain ⟨-, p, ℓs, hp, hℓs, hmem⟩ := hℓ
  have hp' := (tendsto_nhdsWithin_iff.1 hp).1
  have hpi : ∀ k, ∃ i, p k ∈ (φ i).Epi univ := fun k ↦ by
    have := (hmem k).1
    rw [epi_iInf] at this
    exact mem_iUnion.1 this
  choose c hc using hpi
  obtain ⟨i, hi⟩ : ∃ i, ∃ᶠ k in atTop, c k = i := by
    by_contra h
    push Not at h
    obtain ⟨k, hk⟩ := (eventually_all.2 h).exists
    exact hk (c k) rfl
  obtain ⟨ψ, hψ, hψi⟩ := extraction_of_frequently_atTop hi
  have hmemi : ∀ n, p (ψ n) ∈ (φ i).Epi univ := fun n ↦ hψi n ▸ hc (ψ n)
  have hpψ : Tendsto (p ∘ ψ) atTop (𝓝 (x₀, r)) := hp'.comp hψ.tendsto_atTop
  have hle : φ i x₀ ≤ r := le_of_tendsto_epi (hl i) hpψ hmemi
  have hri : φ i x₀ = r := le_antisymm hle (hr ▸ iInf_le (fun i ↦ φ i x₀) i)
  have hsub : (φ i).Epi univ ⊆ (fun x ↦ ⨅ i, φ i x).Epi univ := by
    rw [epi_iInf]; exact subset_iUnion (fun i ↦ (φ i).Epi univ) i
  refine ⟨i, hri, ⟨mem_univ _, hle⟩, p ∘ ψ, ℓs ∘ ψ,
    tendsto_nhdsWithin_iff.2 ⟨hpψ, Eventually.of_forall hmemi⟩, hℓs.comp hψ.tendsto_atTop,
    fun n ↦ regularNormalCone_anti hsub (hmemi n) (hmem (ψ n))⟩

/-- Prop. 4.9 of [Mordukhovich 2018], (4.15) (basic subgradients of minimum functions): for
finitely many functions `φᵢ` lower semicontinuous at `x₀`,
`∂(min φᵢ)(x₀) ⊆ ⋃ {∂φᵢ(x₀) | i ∈ I_min(x₀)}`. -/
theorem subdiff_iInf_subset [Finite ι] (hl : ∀ i, LowerSemicontinuousAt (φ i) x₀) :
    subdiff (fun x ↦ ⨅ i, φ i x) x₀ ⊆
      ⋃ i ∈ {i | φ i x₀ = ⨅ j, φ j x₀}, subdiff (φ i) x₀ := by
  rintro v ⟨r, hr, hv⟩
  obtain ⟨i, hri, hi⟩ := exists_mem_normalCone_epi_of_iInf hl hr hv
  exact mem_iUnion₂.2 ⟨i, hri.trans hr.symm, (mem_subdiff_iff hri).2 hi⟩

/-- Prop. 4.9 of [Mordukhovich 2018], (4.16) (singular subgradients of minimum functions): for
finitely many functions `φᵢ` lower semicontinuous at `x₀`,
`∂^∞(min φᵢ)(x₀) ⊆ ⋃ {∂^∞φᵢ(x₀) | i ∈ I_min(x₀)}`. The book's proof uses the missing inclusion
`⊆` of (1.38); here the geometric argument of `exists_mem_normalCone_epi_of_iInf` covers both
cases. -/
theorem singularSubdiff_iInf_subset [Finite ι] (hl : ∀ i, LowerSemicontinuousAt (φ i) x₀) :
    singularSubdiff (fun x ↦ ⨅ i, φ i x) x₀ ⊆
      ⋃ i ∈ {i | φ i x₀ = ⨅ j, φ j x₀}, singularSubdiff (φ i) x₀ := by
  rintro v ⟨r, hr, hv⟩
  obtain ⟨i, hri, hi⟩ := exists_mem_normalCone_epi_of_iInf hl hr hv
  exact mem_iUnion₂.2 ⟨i, hri.trans hr.symm, (mem_singularSubdiff_iff hri).2 hi⟩

end Minimum

section Definitions

/-- `θ ∘ ∂φ(x)` [Mordukhovich 2018, Thm. 4.10]: `θ ∂φ(x)` for `θ > 0` and `∂^∞φ(x)` for
`θ = 0`. -/
noncomputable def smulSubdiff (θ : ℝ) (φ : E → EReal) (x : E) : Set (StrongDual ℝ E) :=
  if 0 < θ then θ • subdiff φ x else singularSubdiff φ x

/-- The set of active indices `I_max(x) = {i | φᵢ(x) = max φⱼ(x)}` of a finite maximum. -/
noncomputable def maxActive [Fintype ι] (φ : ι → E → EReal) (x : E) : Finset ι :=
  open scoped Classical in Finset.univ.filter fun i ↦ φ i x = ⨆ j, φ j x

/-- The multipliers `Λ(x) = {θ | θᵢ ≥ 0, ∑ θᵢ = 1, θᵢ (aᵢ - max aⱼ) = 0}` of
[Mordukhovich 2018, Thm. 4.10] for the values `aᵢ = φᵢ(x)`. -/
def maxMultipliers [Fintype ι] (a : ι → EReal) : Set (ι → ℝ) :=
  {θ | (∀ i, 0 ≤ θ i) ∧ ∑ i, θ i = 1 ∧ ∀ i, a i ≠ ⨆ j, a j → θ i = 0}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem mem_maxActive [Fintype ι] {i : ι} : i ∈ maxActive φ x₀ ↔ φ i x₀ = ⨆ j, φ j x₀ := by
  classical
  simp [maxActive]

end Definitions

section Maximum

variable [Fintype ι]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] in
/-- The epigraph of a maximum is the intersection of the epigraphs. -/
theorem epi_iSup : (fun x ↦ ⨆ i, φ i x).Epi univ = ⋂ i, (φ i).Epi univ := by
  ext p
  simp only [Function.Epi, mem_ofPred_eq, mem_univ, true_and, mem_iInter, iSup_le_iff]

omit [NormedSpace ℝ E] in
/-- [Mordukhovich 2018, proof of Thm. 4.10]: by the upper semicontinuity of the inactive `φᵢ`,
near `(x₀, max φᵢ(x₀))` the epigraph of the maximum is the intersection of the epigraphs of the
active functions. -/
theorem epi_iSup_eventuallyEq (hr : ⨆ i, φ i x₀ = r)
    (husc : ∀ i ∉ maxActive φ x₀, UpperSemicontinuousAt (φ i) x₀) :
    (fun x ↦ ⨆ i, φ i x).Epi univ =ᶠ[𝓝 ((x₀, r) : E × ℝ)]
      ⋂ i ∈ maxActive φ x₀, (φ i).Epi univ := by
  have key : ∀ i ∉ maxActive φ x₀, ∀ᶠ q in 𝓝 ((x₀, r) : E × ℝ), q ∈ (φ i).Epi univ := by
    intro i hi
    have hlt : φ i x₀ < r := by
      refine lt_of_le_of_ne (hr ▸ le_iSup (fun j ↦ φ j x₀) i) fun h ↦ hi ?_
      rw [mem_maxActive, h, hr]
    obtain ⟨c, hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
    have h1 := ((continuous_fst.tendsto ((x₀, r) : E × ℝ)).eventually (husc i hi c hc1))
    have h2 : ∀ᶠ q in 𝓝 ((x₀, r) : E × ℝ), c < q.2 :=
      (continuous_snd.tendsto ((x₀, r) : E × ℝ)).eventually
        (lt_mem_nhds (EReal.coe_lt_coe_iff.1 hc2))
    filter_upwards [h1, h2] with q hq1 hq2
    exact ⟨mem_univ _, hq1.le.trans (EReal.coe_le_coe_iff.2 hq2.le)⟩
  rw [epi_iSup, eventuallyEq_set]
  filter_upwards [eventually_all.2 fun i ↦ (show ∀ᶠ q in 𝓝 ((x₀, r) : E × ℝ),
    i ∉ maxActive φ x₀ → q ∈ (φ i).Epi univ from by
      by_cases hi : i ∈ maxActive φ x₀
      · exact Eventually.of_forall fun _ h ↦ absurd hi h
      · exact (key i hi).mono fun _ hq _ ↦ hq)] with q hq
  simp only [mem_iInter]
  exact ⟨fun h i _ ↦ h i, fun h i ↦ by
    by_cases hi : i ∈ maxActive φ x₀
    · exact h i hi
    · exact hq i hi⟩

omit [Fintype ι] in
theorem sum_coprod (s : Finset ι) (a : ι → StrongDual ℝ E) (b : ι → StrongDual ℝ ℝ) :
    ∑ i ∈ s, (a i).coprod (b i) = (∑ i ∈ s, a i).coprod (∑ i ∈ s, b i) := by
  ext z <;> simp

omit [Fintype ι] in
theorem sum_comp_inl (s : Finset ι) (g : ι → StrongDual ℝ (E × ℝ)) :
    (∑ i ∈ s, g i).comp (ContinuousLinearMap.inl ℝ E ℝ) =
      ∑ i ∈ s, (g i).comp (ContinuousLinearMap.inl ℝ E ℝ) := by
  ext z; simp

omit [Fintype ι] in
theorem sum_apply_zero_one (s : Finset ι) (g : ι → StrongDual ℝ (E × ℝ)) :
    (∑ i ∈ s, g i) (0, 1) = ∑ i ∈ s, g i (0, 1) := by
  simp

/-- The qualification condition (2.37) for the active `φᵢ` gives the normal qualification
condition of Cor. 2.17 for their epigraphs [Mordukhovich 2018, proof of Thm. 4.10]. -/
theorem epi_qc_of_singular_qc (hr : ⨆ i, φ i x₀ = r)
    (hqc : ∀ v : ι → StrongDual ℝ E, (∀ i ∈ maxActive φ x₀, v i ∈ singularSubdiff (φ i) x₀) →
      ∑ i ∈ maxActive φ x₀, v i = 0 → ∀ i ∈ maxActive φ x₀, v i = 0) :
    ∀ v : ι → StrongDual ℝ (E × ℝ),
      (∀ i ∈ maxActive φ x₀, v i ∈ normalCone ((φ i).Epi univ) (x₀, r)) →
        ∑ i ∈ maxActive φ x₀, v i = 0 → ∀ i ∈ maxActive φ x₀, v i = 0 := by
  intro v hv hsum
  have hri : ∀ i ∈ maxActive φ x₀, φ i x₀ = r := fun i hi ↦ (mem_maxActive.1 hi).trans hr
  have h01 : ∀ i ∈ maxActive φ x₀, v i (0, 1) = 0 := by
    have hle : ∀ i ∈ maxActive φ x₀, v i (0, 1) ≤ 0 := fun i hi ↦
      apply_zero_one_nonpos_of_mem_normalCone_epi (hv i hi)
    have h0 : ∑ i ∈ maxActive φ x₀, v i (0, 1) = 0 := by
      rw [← sum_apply_zero_one, hsum]; rfl
    exact (Finset.sum_eq_zero_iff_of_nonpos hle).1 h0
  have hsing : ∀ i ∈ maxActive φ x₀,
      (v i).comp (ContinuousLinearMap.inl ℝ E ℝ) ∈ singularSubdiff (φ i) x₀ := fun i hi ↦ by
    rw [mem_singularSubdiff_iff (hri i hi), ← eq_coprod_zero _ (h01 i hi)]
    exact hv i hi
  have h0 := hqc (fun i ↦ (v i).comp (ContinuousLinearMap.inl ℝ E ℝ)) hsing
    (by rw [← sum_comp_inl, hsum]; rfl)
  intro i hi
  rw [eq_coprod_zero (v i) (h01 i hi), h0 i hi]
  ext <;> simp

/-- [Mordukhovich 2018, proof of Thm. 4.10(i)]: Cor. 2.17 applied to the epigraphs of the active
functions gives `N((x₀, r); epi max φᵢ) ⊆ ∑_{i ∈ I_max(x₀)} N((x₀, r); epi φᵢ)`. -/
theorem normalCone_epi_iSup_subset [FiniteDimensional ℝ E] (hr : ⨆ i, φ i x₀ = r)
    (hloc : ∀ i ∈ maxActive φ x₀,
      ∃ ρ > 0, IsClosed ((φ i).Epi univ ∩ closedBall ((x₀, r) : E × ℝ) ρ))
    (husc : ∀ i ∉ maxActive φ x₀, UpperSemicontinuousAt (φ i) x₀)
    (hqc : ∀ v : ι → StrongDual ℝ E, (∀ i ∈ maxActive φ x₀, v i ∈ singularSubdiff (φ i) x₀) →
      ∑ i ∈ maxActive φ x₀, v i = 0 → ∀ i ∈ maxActive φ x₀, v i = 0) :
    normalCone ((fun x ↦ ⨆ i, φ i x).Epi univ) (x₀, r) ⊆
      ∑ i ∈ maxActive φ x₀, normalCone ((φ i).Epi univ) (x₀, r) := by
  rw [normalCone_congr (epi_iSup_eventuallyEq hr husc)]
  exact normalCone_biInter_subset _ hloc (epi_qc_of_singular_qc hr hqc)

/-- Thm. 4.10(i) of [Mordukhovich 2018] (basic subgradients of maximum functions): let
`max φᵢ(x₀) = r` be finite, the active `φᵢ` (`i ∈ I_max(x₀)`) have epigraphs locally closed
around `(x₀, r)` (e.g. l.s.c. around `x₀`), the inactive ones be upper semicontinuous at `x₀`,
and assume (2.37) for the active indices. Then
`∂(max φᵢ)(x₀) ⊆ ⋃ {∑_{i ∈ I_max(x₀)} θᵢ ∘ ∂φᵢ(x₀) | θ ∈ Λ(x₀)}`, where `θ ∘ ∂φ = θ ∂φ` for
`θ > 0` and `∂^∞φ` for `θ = 0` (`smulSubdiff`). -/
theorem subdiff_iSup_subset [FiniteDimensional ℝ E] (hr : ⨆ i, φ i x₀ = r)
    (hloc : ∀ i ∈ maxActive φ x₀,
      ∃ ρ > 0, IsClosed ((φ i).Epi univ ∩ closedBall ((x₀, r) : E × ℝ) ρ))
    (husc : ∀ i ∉ maxActive φ x₀, UpperSemicontinuousAt (φ i) x₀)
    (hqc : ∀ v : ι → StrongDual ℝ E, (∀ i ∈ maxActive φ x₀, v i ∈ singularSubdiff (φ i) x₀) →
      ∑ i ∈ maxActive φ x₀, v i = 0 → ∀ i ∈ maxActive φ x₀, v i = 0) :
    subdiff (fun x ↦ ⨆ i, φ i x) x₀ ⊆ {x | ∃ θ ∈ maxMultipliers (fun i ↦ φ i x₀),
      x ∈ ∑ i ∈ maxActive φ x₀, smulSubdiff (θ i) (φ i) x₀} := by
  classical
  intro x hx
  rw [mem_subdiff_iff (φ := fun x ↦ ⨆ i, φ i x) hr] at hx
  obtain ⟨g, hg, hgx⟩ :=
    (Set.mem_finsetSum _ _ _).1 (normalCone_epi_iSup_subset hr hloc husc hqc hx)
  have hri : ∀ i ∈ maxActive φ x₀, φ i x₀ = r := fun i hi ↦ (mem_maxActive.1 hi).trans hr
  set θ : ι → ℝ := fun i ↦ if i ∈ maxActive φ x₀ then -g i (0, 1) else 0 with hθ
  have hθnn : ∀ i, 0 ≤ θ i := fun i ↦ by
    by_cases hi : i ∈ maxActive φ x₀
    · simp only [hθ, if_pos hi]
      linarith [apply_zero_one_nonpos_of_mem_normalCone_epi (hg hi)]
    · simp [hθ, if_neg hi]
  have hθsum : ∑ i, θ i = 1 := by
    simp only [hθ, Finset.sum_ite_mem_eq, Finset.sum_neg_distrib, ← sum_apply_zero_one, hgx]
    simp
  refine ⟨θ, ⟨hθnn, hθsum, fun i hi ↦ ?_⟩, (Set.mem_finsetSum _ _ _).2
    ⟨fun i ↦ (g i).comp (ContinuousLinearMap.inl ℝ E ℝ), fun {i} hi ↦ ?_, ?_⟩⟩
  · simp only [hθ, if_neg (show i ∉ maxActive φ x₀ from fun h ↦ hi (mem_maxActive.1 h))]
  · rcases (mem_normalCone_epi_iff (hri i hi)).1 (hg hi) with ⟨μ, hμ, u, hu, he⟩ | ⟨u, hu, he⟩
    · have hθi : θ i = μ := by simp [hθ, if_pos hi, he]
      simp only [smulSubdiff, hθi, if_pos hμ]
      exact ⟨u, hu, by rw [he]; ext; simp⟩
    · have hθi : θ i = 0 := by simp [hθ, if_pos hi, he]
      simp only [smulSubdiff, hθi, lt_irrefl, if_false]
      rw [he]; convert hu using 1; ext; simp
  · rw [← sum_comp_inl, hgx]; ext; simp

/-- Thm. 4.10(i) of [Mordukhovich 2018] (singular subgradients of maximum functions): under the
assumptions of `subdiff_iSup_subset`, `∂^∞(max φᵢ)(x₀) ⊆ ∑_{i ∈ I_max(x₀)} ∂^∞φᵢ(x₀)`. -/
theorem singularSubdiff_iSup_subset [FiniteDimensional ℝ E] (hr : ⨆ i, φ i x₀ = r)
    (hloc : ∀ i ∈ maxActive φ x₀,
      ∃ ρ > 0, IsClosed ((φ i).Epi univ ∩ closedBall ((x₀, r) : E × ℝ) ρ))
    (husc : ∀ i ∉ maxActive φ x₀, UpperSemicontinuousAt (φ i) x₀)
    (hqc : ∀ v : ι → StrongDual ℝ E, (∀ i ∈ maxActive φ x₀, v i ∈ singularSubdiff (φ i) x₀) →
      ∑ i ∈ maxActive φ x₀, v i = 0 → ∀ i ∈ maxActive φ x₀, v i = 0) :
    singularSubdiff (fun x ↦ ⨆ i, φ i x) x₀ ⊆
      ∑ i ∈ maxActive φ x₀, singularSubdiff (φ i) x₀ := by
  intro x hx
  rw [mem_singularSubdiff_iff (φ := fun x ↦ ⨆ i, φ i x) hr] at hx
  obtain ⟨g, hg, hgx⟩ :=
    (Set.mem_finsetSum _ _ _).1 (normalCone_epi_iSup_subset hr hloc husc hqc hx)
  have hri : ∀ i ∈ maxActive φ x₀, φ i x₀ = r := fun i hi ↦ (mem_maxActive.1 hi).trans hr
  have h01 : ∀ i ∈ maxActive φ x₀, g i (0, 1) = 0 := by
    have hle : ∀ i ∈ maxActive φ x₀, g i (0, 1) ≤ 0 := fun i hi ↦
      apply_zero_one_nonpos_of_mem_normalCone_epi (hg hi)
    have h0 : ∑ i ∈ maxActive φ x₀, g i (0, 1) = 0 := by
      rw [← sum_apply_zero_one, hgx]; simp
    exact (Finset.sum_eq_zero_iff_of_nonpos hle).1 h0
  refine (Set.mem_finsetSum _ _ _).2
    ⟨fun i ↦ (g i).comp (ContinuousLinearMap.inl ℝ E ℝ), fun {i} hi ↦ ?_, ?_⟩
  · rw [mem_singularSubdiff_iff (hri i hi), ← eq_coprod_zero _ (h01 i hi)]
    exact hg hi
  · rw [← sum_comp_inl, hgx]; ext; simp

/-- Thm. 4.10(i) of [Mordukhovich 2018], equality statement: if moreover every active `φᵢ` is
epigraphically regular at `x₀`, then the maximum function is epigraphically regular at `x₀` and
both inclusions of Thm. 4.10(i) hold as equalities. (This uses only the intersection rule
Cor. 2.17 and its regular counterpart, not the missing epi-regular part of Thm. 2.19.) -/
theorem iSup_eq_of_epiRegularAt [FiniteDimensional ℝ E] (hr : ⨆ i, φ i x₀ = r)
    (hloc : ∀ i ∈ maxActive φ x₀,
      ∃ ρ > 0, IsClosed ((φ i).Epi univ ∩ closedBall ((x₀, r) : E × ℝ) ρ))
    (husc : ∀ i ∉ maxActive φ x₀, UpperSemicontinuousAt (φ i) x₀)
    (hqc : ∀ v : ι → StrongDual ℝ E, (∀ i ∈ maxActive φ x₀, v i ∈ singularSubdiff (φ i) x₀) →
      ∑ i ∈ maxActive φ x₀, v i = 0 → ∀ i ∈ maxActive φ x₀, v i = 0)
    (hreg : ∀ i ∈ maxActive φ x₀, EpiRegularAt (φ i) x₀) :
    subdiff (fun x ↦ ⨆ i, φ i x) x₀ = {x | ∃ θ ∈ maxMultipliers (fun i ↦ φ i x₀),
        x ∈ ∑ i ∈ maxActive φ x₀, smulSubdiff (θ i) (φ i) x₀} ∧
      singularSubdiff (fun x ↦ ⨆ i, φ i x) x₀ =
        ∑ i ∈ maxActive φ x₀, singularSubdiff (φ i) x₀ ∧
      EpiRegularAt (fun x ↦ ⨆ i, φ i x) x₀ := by
  have hri : ∀ i ∈ maxActive φ x₀, φ i x₀ = r := fun i hi ↦ (mem_maxActive.1 hi).trans hr
  have hreg' : ∀ i ∈ maxActive φ x₀, NormallyRegularAt ((φ i).Epi univ) (x₀, r) := by
    intro i hi
    obtain ⟨s, hs, h⟩ := hreg i hi
    rw [hri i hi, EReal.coe_eq_coe_iff] at hs
    rwa [← hs] at h
  have key : ∑ i ∈ maxActive φ x₀, normalCone ((φ i).Epi univ) (x₀, r) ⊆
      regularNormalCone ((fun x ↦ ⨆ i, φ i x).Epi univ) (x₀, r) := by
    rw [Finset.sum_congr rfl hreg', regularNormalCone_congr (epi_iSup_eventuallyEq hr husc)]
    exact sum_regularNormalCone_subset_biInter _
  have hmem : ∀ c : StrongDual ℝ ℝ, ∀ x : StrongDual ℝ E,
      x.coprod c ∈ ∑ i ∈ maxActive φ x₀, normalCone ((φ i).Epi univ) (x₀, r) →
        x.coprod c ∈ normalCone ((fun x ↦ ⨆ i, φ i x).Epi univ) (x₀, r) :=
    fun _ _ h ↦ regularNormalCone_subset_normalCone (key h)
  refine ⟨subset_antisymm (subdiff_iSup_subset hr hloc husc hqc) ?_,
    subset_antisymm (singularSubdiff_iSup_subset hr hloc husc hqc) ?_,
    ⟨r, hr, subset_antisymm ((normalCone_epi_iSup_subset hr hloc husc hqc).trans key)
      regularNormalCone_subset_normalCone⟩⟩
  · rintro x ⟨θ, ⟨hθnn, hθsum, hθ0⟩, hx⟩
    obtain ⟨w, hw, hwx⟩ := (Set.mem_finsetSum _ _ _).1 hx
    rw [mem_subdiff_iff (φ := fun x ↦ ⨆ i, φ i x) hr]
    have hθI : ∑ i ∈ maxActive φ x₀, θ i = 1 := by
      rw [← hθsum]
      refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi ↦ hθ0 i fun h ↦ hi ?_
      exact mem_maxActive.2 h
    have hg : ∀ i ∈ maxActive φ x₀,
        (w i).coprod (θ i • (-1 : StrongDual ℝ ℝ)) ∈ normalCone ((φ i).Epi univ) (x₀, r) := by
      intro i hi
      have hwi := hw hi
      by_cases hθi : 0 < θ i
      · simp only [smulSubdiff, if_pos hθi] at hwi
        obtain ⟨u, hu, hue⟩ := hwi
        have := smul_mem_normalCone ((mem_subdiff_iff (hri i hi)).1 hu) hθi.le
        convert this using 1
        rw [← hue]; ext <;> simp
      · have hθi0 : θ i = 0 := le_antisymm (not_lt.1 hθi) (hθnn i)
        simp only [smulSubdiff, if_neg hθi] at hwi
        rw [hθi0, zero_smul]
        exact (mem_singularSubdiff_iff (hri i hi)).1 hwi
    have hs : ∑ i ∈ maxActive φ x₀, (w i).coprod (θ i • (-1 : StrongDual ℝ ℝ)) ∈
        ∑ i ∈ maxActive φ x₀, normalCone ((φ i).Epi univ) (x₀, r) :=
      (Set.mem_finsetSum _ _ _).2 ⟨_, fun {i} hi ↦ hg i hi, rfl⟩
    rw [sum_coprod, hwx, ← Finset.sum_smul, hθI, one_smul] at hs
    exact hmem _ x hs
  · intro x hx
    obtain ⟨w, hw, hwx⟩ := (Set.mem_finsetSum _ _ _).1 hx
    rw [mem_singularSubdiff_iff (φ := fun x ↦ ⨆ i, φ i x) hr]
    have hs : ∑ i ∈ maxActive φ x₀, (w i).coprod (0 : StrongDual ℝ ℝ) ∈
        ∑ i ∈ maxActive φ x₀, normalCone ((φ i).Epi univ) (x₀, r) :=
      (Set.mem_finsetSum _ _ _).2
        ⟨_, fun {i} hi ↦ (mem_singularSubdiff_iff (hri i hi)).1 (hw hi), rfl⟩
    rw [sum_coprod, hwx, Finset.sum_const_zero] at hs
    exact hmem _ x hs

end Maximum

section MaxFunction

variable [Fintype ι] [Nonempty ι]

/-- The real maximum `max_i yᵢ` of a vector `y : ι → ℝ`. -/
noncomputable def vecMax (y : ι → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty y

omit [Nonempty ι] in
theorem le_vecMax [Nonempty ι] (y : ι → ℝ) (i : ι) : y i ≤ vecMax y :=
  Finset.le_sup' y (Finset.mem_univ i)

omit [Nonempty ι] in
theorem vecMax_le_iff [Nonempty ι] {y : ι → ℝ} {c : ℝ} : vecMax y ≤ c ↔ ∀ i, y i ≤ c := by
  simp [vecMax, Finset.sup'_le_iff]

theorem iSup_coe_eq_vecMax (y : ι → ℝ) : ⨆ i, ((y i : ℝ) : EReal) = ((vecMax y : ℝ) : EReal) := by
  refine le_antisymm (iSup_le fun i ↦ EReal.coe_le_coe_iff.2 (le_vecMax y i)) ?_
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty y
  rw [vecMax, hi]
  exact le_iSup (fun i ↦ ((y i : ℝ) : EReal)) i

/-- `max` is `1`-Lipschitz for the sup norm. -/
theorem lipschitzWith_vecMax : LipschitzWith 1 (vecMax : (ι → ℝ) → ℝ) := by
  have key : ∀ y z : ι → ℝ, vecMax y ≤ vecMax z + dist y z := fun y z ↦ vecMax_le_iff.2 fun i ↦ by
    have h1 := dist_le_pi_dist y z i
    rw [Real.dist_eq] at h1
    linarith [le_abs_self (y i - z i), le_vecMax z i]
  refine LipschitzWith.of_dist_le_mul fun y z ↦ ?_
  rw [Real.dist_eq, NNReal.coe_one, one_mul, abs_le]
  constructor
  · linarith [key z y, dist_comm y z]
  · linarith [key y z]

theorem continuous_vecMax : Continuous (vecMax : (ι → ℝ) → ℝ) :=
  Continuous.finset_sup'_apply (f := fun i (y : ι → ℝ) ↦ y i) _ fun i _ ↦ continuous_apply i

/-- The epigraph of `max` on `ι → ℝ` is convex. -/
theorem convex_epi_vecMax :
    Convex ℝ ((fun y : ι → ℝ ↦ ((vecMax y : ℝ) : EReal)).Epi univ) := by
  rintro ⟨y, α⟩ ⟨-, hy⟩ ⟨z, β⟩ ⟨-, hz⟩ a b ha hb hab
  refine ⟨mem_univ _, ?_⟩
  simp only [EReal.coe_le_coe_iff] at hy hz ⊢
  refine vecMax_le_iff.2 fun i ↦ ?_
  simp only [Prod.smul_fst, Prod.fst_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Prod.smul_snd, Prod.snd_add]
  nlinarith [le_vecMax y i, le_vecMax z i]

theorem vecMax_add_const_le (y : ι → ℝ) (c : ℝ) : vecMax (fun i ↦ y i + c) ≤ vecMax y + c :=
  vecMax_le_iff.2 fun i ↦ by linarith [le_vecMax y i]

/-- Subgradients of `max` on `ι → ℝ` [Mordukhovich 2018, proof of Thm. 4.10(ii)]: every
`v ∈ ∂(max)(y₀)` is `v(y) = ∑ θᵢ yᵢ` with `θ ∈ Λ(y₀)`. -/
theorem mem_maxMultipliers_of_mem_subdiff_vecMax [DecidableEq ι] {y₀ : ι → ℝ}
    {v : StrongDual ℝ (ι → ℝ)}
    (hv : v ∈ subdiff (fun y ↦ ((vecMax y : ℝ) : EReal)) y₀) :
    (fun i ↦ v fun j ↦ if i = j then 1 else 0) ∈ maxMultipliers (fun i ↦ ((y₀ i : ℝ) : EReal)) ∧
      ∀ y, v y = ∑ i, (v fun j ↦ if i = j then 1 else 0) * y i := by
  have hc := convex_epi_vecMax (ι := ι)
  have hv1 := (mem_subdiff_of_convex hc
    (show (fun y : ι → ℝ ↦ ((vecMax y : ℝ) : EReal)) y₀ = vecMax y₀ from rfl)).1 hv
  have hv' : ∀ y, vecMax y₀ + v (y - y₀) ≤ vecMax y := fun y ↦ EReal.coe_le_coe_iff.1 (hv1 y)
  set θ : ι → ℝ := fun i ↦ v fun j ↦ if i = j then 1 else 0 with hθ
  have hdec : ∀ y, v y = ∑ i, θ i * y i := fun y ↦ by
    rw [show v y = v.toLinearMap y from rfl, LinearMap.pi_apply_eq_sum_univ]
    simp [hθ, mul_comm]
  refine ⟨⟨fun i ↦ ?_, ?_, fun i hi ↦ ?_⟩, hdec⟩
  · have h := hv' (fun j ↦ y₀ j - if i = j then 1 else 0)
    have hle : vecMax (fun j ↦ y₀ j - if i = j then 1 else 0) ≤ vecMax y₀ :=
      vecMax_le_iff.2 fun j ↦ by
        have := le_vecMax y₀ j
        split_ifs <;> linarith
    have e : (fun j ↦ y₀ j - if i = j then (1 : ℝ) else 0) - y₀ =
        -fun j ↦ if i = j then 1 else 0 := by
      ext j; simp
    rw [e, map_neg] at h
    linarith
  · have h1 := hv' (fun j ↦ y₀ j + 1)
    have h2 := hv' (fun j ↦ y₀ j + -1)
    have e1 : (fun j ↦ y₀ j + 1) - y₀ = fun _ ↦ (1 : ℝ) := by ext; simp
    have e2 : (fun j ↦ y₀ j + -1) - y₀ = fun _ ↦ (-1 : ℝ) := by ext; simp
    rw [e1, hdec] at h1
    rw [e2, hdec] at h2
    have h3 := vecMax_add_const_le y₀ 1
    have h4 := vecMax_add_const_le y₀ (-1)
    simp only [mul_one, mul_neg, Finset.sum_neg_distrib] at h1 h2
    linarith
  · have hlt : y₀ i < vecMax y₀ := by
      refine lt_of_le_of_ne (le_vecMax y₀ i) fun h ↦ hi ?_
      simp only
      rw [iSup_coe_eq_vecMax, h]
    set s := vecMax y₀ - y₀ i
    have h := hv' (fun j ↦ y₀ j + if i = j then s else 0)
    have hle : vecMax (fun j ↦ y₀ j + if i = j then s else 0) ≤ vecMax y₀ :=
      vecMax_le_iff.2 fun j ↦ by
        have := le_vecMax y₀ j
        split_ifs with hij
        · subst hij; simp [s]
        · linarith
    have e : (fun j ↦ y₀ j + if i = j then s else 0) - y₀ = s • fun j ↦ if i = j then 1 else 0 := by
      ext j; simp
    rw [e, map_smul, smul_eq_mul] at h
    have hs : 0 < s := by simp only [s]; linarith
    have hθi : θ i ≤ 0 := by nlinarith
    exact le_antisymm hθi (by
      have h' := hv' (fun j ↦ y₀ j - if i = j then 1 else 0)
      have hle' : vecMax (fun j ↦ y₀ j - if i = j then 1 else 0) ≤ vecMax y₀ :=
        vecMax_le_iff.2 fun j ↦ by
          have := le_vecMax y₀ j
          split_ifs <;> linarith
      have e' : (fun j ↦ y₀ j - if i = j then (1 : ℝ) else 0) - y₀ =
          -fun j ↦ if i = j then 1 else 0 := by ext j; simp
      rw [e', map_neg] at h'
      linarith)

end MaxFunction

section LipschitzMax

variable [Fintype ι] [Nonempty ι]
variable {f : ι → E → ℝ} {U : ι → Set E} {K : ι → ℝ≥0}

omit [NormedSpace ℝ E] [Nonempty ι] in
theorem lipschitzOnWith_pi (hL : ∀ i, LipschitzOnWith (K i) (f i) (U i)) :
    LipschitzOnWith (Finset.univ.sup K) (fun x i ↦ f i x) (⋂ i, U i) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦
    (dist_pi_le_iff (by positivity)).2 fun i ↦ ?_
  refine ((hL i).dist_le_mul x (mem_iInter.1 hx i) y (mem_iInter.1 hy i)).trans ?_
  exact mul_le_mul_of_nonneg_right
    (NNReal.coe_le_coe.2 (Finset.le_sup (f := K) (Finset.mem_univ i))) dist_nonneg

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem iSup_coe_fun_eq :
    (fun x ↦ ⨆ i, (f i x : EReal)) = fun x ↦ ((vecMax (fun i ↦ f i x) : ℝ) : EReal) :=
  funext fun _ ↦ iSup_coe_eq_vecMax _

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] [Nonempty ι] in
theorem coe_finset_sum_ereal (s : Finset ι) (a : ι → ℝ) :
    ((∑ i ∈ s, a i : ℝ) : EReal) = ∑ i ∈ s, ((a i : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, EReal.coe_add, ih]

variable [FiniteDimensional ℝ E]

/-- Thm. 4.10(ii) of [Mordukhovich 2018] (subgradients of maxima of Lipschitzian functions): for
finitely many functions `fᵢ` Lipschitz around `x₀`,
`∂(max fᵢ)(x₀) ⊆ ⋃ {∂(∑ θᵢ fᵢ)(x₀) | θ ∈ Λ(x₀)}`. Here `∑` runs over all indices; since
`θᵢ = 0` for the inactive ones, this is the book's sum over `I_max(x₀)`. The proof applies the
chain rule of Cor. 4.6 to `max ∘ (f₁, …, fₛ)` and the subgradients of the convex function `max`
(`mem_maxMultipliers_of_mem_subdiff_vecMax`). -/
theorem subdiff_iSup_lipschitz_subset (hU : ∀ i, U i ∈ 𝓝 x₀)
    (hL : ∀ i, LipschitzOnWith (K i) (f i) (U i)) :
    subdiff (fun x ↦ ⨆ i, (f i x : EReal)) x₀ ⊆
      ⋃ θ ∈ maxMultipliers (fun i ↦ (f i x₀ : EReal)),
        subdiff (fun x ↦ ((∑ i, θ i * f i x : ℝ) : EReal)) x₀ := by
  classical
  rw [iSup_coe_fun_eq]
  intro x hx
  have hU' : (⋂ i, U i) ∈ 𝓝 x₀ := iInter_mem.2 hU
  have hsing : singularSubdiff (fun y : ι → ℝ ↦ ((vecMax y : ℝ) : EReal)) (fun i ↦ f i x₀) =
      {0} :=
    singularSubdiff_eq_zero_of_lipschitz univ_mem lipschitzWith_vecMax.lipschitzOnWith
  have hloc : ∃ ρ > 0, IsClosed ((fun y : ι → ℝ ↦ ((vecMax y : ℝ) : EReal)).Epi univ ∩
      closedBall (((fun i ↦ f i x₀), vecMax fun i ↦ f i x₀) : (ι → ℝ) × ℝ) ρ) :=
    locallyClosed_epi_of_continuousOn univ_mem continuous_vecMax.continuousOn _
  have hqc : ∀ v ∈ singularSubdiff (fun y : ι → ℝ ↦ ((vecMax y : ℝ) : EReal)) (fun i ↦ f i x₀),
      (0 : StrongDual ℝ E) ∈ subdiff (fun x ↦ ((v (fun i ↦ f i x) : ℝ) : EReal)) x₀ → v = 0 :=
    fun v hv _ ↦ by rwa [hsing] at hv
  have h := subdiff_comp_lipschitz_subset (ψ := fun y : ι → ℝ ↦ ((vecMax y : ℝ) : EReal))
    (g := fun x i ↦ f i x) (r := vecMax fun i ↦ f i x₀) hU' (lipschitzOnWith_pi hL) rfl
    hloc hqc hx
  obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.1 h
  obtain ⟨hθ, hdec⟩ := mem_maxMultipliers_of_mem_subdiff_vecMax hv
  refine mem_iUnion₂.2 ⟨_, hθ, ?_⟩
  have hfun : (fun z ↦ ((v (fun i ↦ f i z) : ℝ) : EReal)) =
      fun z ↦ ((∑ i, (v fun j ↦ if i = j then 1 else 0) * f i z : ℝ) : EReal) :=
    funext fun z ↦ by rw [hdec]
  rwa [hfun] at hxv

omit [FiniteDimensional ℝ E] in
/-- A constant function is lower regular. -/
theorem lowerRegularAt_const (c : ℝ) : LowerRegularAt (fun _ : E ↦ (c : EReal)) x₀ := by
  have h1 : subdiff (fun _ : E ↦ (c : EReal)) x₀ = {0} :=
    subdiff_of_hasFDerivAt_of_continuousAt (f := fun _ ↦ c) (f' := fun _ ↦ 0)
      (Eventually.of_forall fun _ ↦ hasFDerivAt_const _ _) continuousAt_const
  have h2 : regularSubdiff (fun _ : E ↦ (c : EReal)) x₀ = {0} :=
    regularSubdiff_of_hasFDerivAt (f := fun _ ↦ c) (hasFDerivAt_const _ _)
  unfold LowerRegularAt
  rw [h1, h2]

/-- Thm. 4.10(ii) of [Mordukhovich 2018], equality statement: if moreover every active `fᵢ` is
lower regular at `x₀`, then `∂(max fᵢ)(x₀) = ⋃ {∂(∑ θᵢ fᵢ)(x₀) | θ ∈ Λ(x₀)}` and `max fᵢ` is
lower regular at `x₀`. -/
theorem iSup_lipschitz_eq_of_lowerRegularAt (hU : ∀ i, U i ∈ 𝓝 x₀)
    (hL : ∀ i, LipschitzOnWith (K i) (f i) (U i))
    (hreg : ∀ i ∈ maxActive (fun i x ↦ (f i x : EReal)) x₀,
      LowerRegularAt (fun x ↦ (f i x : EReal)) x₀) :
    subdiff (fun x ↦ ⨆ i, (f i x : EReal)) x₀ =
        ⋃ θ ∈ maxMultipliers (fun i ↦ (f i x₀ : EReal)),
          subdiff (fun x ↦ ((∑ i, θ i * f i x : ℝ) : EReal)) x₀ ∧
      LowerRegularAt (fun x ↦ ⨆ i, (f i x : EReal)) x₀ := by
  have key : ∀ θ ∈ maxMultipliers (fun i ↦ (f i x₀ : EReal)),
      subdiff (fun x ↦ ((∑ i, θ i * f i x : ℝ) : EReal)) x₀ ⊆
        regularSubdiff (fun x ↦ ⨆ i, (f i x : EReal)) x₀ := by
    intro θ hθ
    have hact : ∀ i, θ i ≠ 0 → f i x₀ = vecMax (fun j ↦ f j x₀) := fun i hi ↦ by
      by_contra h
      refine hi (hθ.2.2 i fun h' ↦ h ?_)
      have h'' : (f i x₀ : EReal) = ⨆ j, (f j x₀ : EReal) := h'
      rw [iSup_coe_eq_vecMax] at h''
      exact EReal.coe_eq_coe_iff.1 h''
    have hregi : ∀ i, LowerRegularAt (fun x ↦ ((θ i * f i x : ℝ) : EReal)) x₀ := fun i ↦ by
      by_cases hpos : 0 < θ i
      · refine LowerRegularAt.const_mul hpos (hreg i (mem_maxActive.2 ?_))
        show (f i x₀ : EReal) = ⨆ j, (f j x₀ : EReal)
        rw [iSup_coe_eq_vecMax, hact i hpos.ne']
      · have h0 : θ i = 0 := le_antisymm (not_lt.1 hpos) (hθ.1 i)
        have : (fun x ↦ ((θ i * f i x : ℝ) : EReal)) = fun _ ↦ ((0 : ℝ) : EReal) :=
          funext fun x ↦ by rw [h0, zero_mul]
        rw [this]
        exact lowerRegularAt_const 0
    have hsum := (subdiff_sum_eq (φ := fun i x ↦ ((θ i * f i x : ℝ) : EReal))
      (r := fun i ↦ θ i * f i x₀) (fun i ↦ rfl)
      (fun i ↦ locallyClosed_epi_of_continuousOn (hU i)
        (lipschitzOnWith_const_mul (hL i) (θ i)).continuousOn _)
      (fun v hv _ i ↦ by
        have := hv i
        rwa [singularSubdiff_eq_zero_of_lipschitz (hU i) (lipschitzOnWith_const_mul (hL i) (θ i))]
          at this) hregi).2
    have hfun : (fun x ↦ ((∑ i, θ i * f i x : ℝ) : EReal)) =
        fun x ↦ ∑ i, ((θ i * f i x : ℝ) : EReal) :=
      funext fun x ↦ coe_finset_sum_ereal _ _
    rw [hfun]
    unfold LowerRegularAt at hsum
    rw [hsum, ← hfun, iSup_coe_fun_eq]
    refine regularSubdiff_subset_of_le (Eventually.of_forall fun x ↦ ?_) ?_
    · refine EReal.coe_le_coe_iff.2 ?_
      calc ∑ i, θ i * f i x ≤ ∑ i, θ i * vecMax (fun j ↦ f j x) :=
            Finset.sum_le_sum fun i _ ↦
              mul_le_mul_of_nonneg_left (le_vecMax (fun j ↦ f j x) i) (hθ.1 i)
        _ = vecMax (fun j ↦ f j x) := by rw [← Finset.sum_mul, hθ.2.1, one_mul]
    · refine EReal.coe_eq_coe_iff.2 ?_
      calc ∑ i, θ i * f i x₀ = ∑ i, θ i * vecMax (fun j ↦ f j x₀) :=
            Finset.sum_congr rfl fun i _ ↦ by
              by_cases h : θ i = 0
              · rw [h, zero_mul, zero_mul]
              · rw [hact i h]
        _ = vecMax (fun j ↦ f j x₀) := by rw [← Finset.sum_mul, hθ.2.1, one_mul]
  have hsub := subdiff_iSup_lipschitz_subset hU hL
  exact ⟨subset_antisymm hsub (iUnion₂_subset fun θ hθ ↦ (key θ hθ).trans
    regularSubdiff_subset_subdiff),
    subset_antisymm (hsub.trans (iUnion₂_subset key)) regularSubdiff_subset_subdiff⟩

end LipschitzMax

end VariationalAnalysis
