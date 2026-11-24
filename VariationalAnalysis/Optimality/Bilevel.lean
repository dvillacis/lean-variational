/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis.Subdifferential.Marginal
import VariationalAnalysis.SetValued.Basic

/-!
# Problems of bilevel programming

Sect. 6.2 of [Mordukhovich 2018]: the optimistic and pessimistic versions of bilevel programs,
the value function approach, partial calmness and weak sharp minima.

The upper-level (leader's) problem minimizes `f(x, y)` over `x ∈ Ω` along solutions `y` of the
lower-level (follower's) problem (6.28)–(6.29)
`minimize_y φ(x, y)` subject to `y ∈ G(x) = {y | gᵢ(x, y) ≤ 0, i ∈ ι}`.
The data are `f φ : E × F → ℝ`, `g : ι → E × F → ℝ` and `Ω : Set E`.

## Main definitions

* `lowerFeasible g x`: the lower-level constraint set `G(x)` (6.29).
* `lowerValue φ g`: the lower-level value function `μ` (6.33), a marginal function (4.1).
* `lowerSolution φ g`: the lower-level solution map `S` (6.30).
* `optimisticValue f φ g`, `pessimisticValue f φ g`: `f_opt` (6.31) and `f_pes` (6.32).
* `optimisticSolution f φ g`: the map `S̃` (6.36) of lower-level solutions realizing `f_opt`.
* `valueFeasible φ g Ω`: the feasible set of the value function reformulation (6.34).
* `PartiallyCalmWith`, `PartiallyCalm`: Def. 6.14 (partial calmness).
* `penalizedObjective f φ g κ`: the objective `f + κ (φ - μ)` of the penalized problem (6.40).
* `IsLocalWeakSharpMin`: Def. 6.16 (local weak sharp minima).

## Main results

* `isLocalMinOn_valueFeasible_of_isLocalMinOn_optimisticValue`,
  `isLocalMinOn_optimisticValue_of_isLocalMinOn_valueFeasible`: Prop. 6.13 (local solutions of
  (6.31) and (6.34)).
* `isLocalMinOn_penalizedObjective`, `partiallyCalmWith_of_isLocalMinOn_penalizedObjective`:
  Prop. 6.15 (penalization via partial calmness).
* `partiallyCalm_of_uniform_weakSharp`: Prop. 6.17 (partial calmness from uniform weak sharp
  minima).
* `exists_weakSharp_of_kkt`, `isLocalWeakSharpMin_of_kkt`: Prop. 6.18 (weak sharp minima from
  the KKT conditions and the kernel condition (6.46)).

## Remarks on the book

* The book defines `S̃(x) = argmin {φ(x, y) | g(x, y) ≤ 0, f(x, y) ≤ η(x)}` with the two-level value
  function `η` (6.35), and asserts `S̃(x) ⊆ S(x)`. Since `φ(x, y) ≤ μ(x)` and `g(x, y) ≤ 0` mean
  `y ∈ S(x)`, `η = f_opt`; the inclusion `S̃(x) ⊆ S(x)` holds when some `y ∈ S(x)` realizes
  `f_opt(x)`, but can fail otherwise. Its proof of Prop. 6.13(ii) uses `S̃ ⊆ S`, so we take
  `S̃(x) = {y ∈ S(x) | f(x, y) = f_opt(x)}`.
* In Prop. 6.13(ii), inner semicontinuity of `S̃` is relative to `dom S̃` (Exercise 2.46), and
  the book's proof picks `yₖ ∈ S̃(xₖ)`; we assume that the infimum in `f_opt` is attained near
  `x̄` wherever `f_opt` is finite (as in Thm. 4.1,
  `subdiff_marginal_subset_of_innerSemicontinuousAt`).
* In Def. 6.14 the perturbed constraint `φ(x, y) - μ(x) + ϑ = 0` of (6.38) is written
  `μ(x) = φ(x, y) + ϑ`, which also excludes `μ(x) = -∞`. The objective of (6.40) is
  `f + κ φ - κ μ`, equal to `+∞` where `μ = -∞`.
* Prop. 6.17 uses the book's standing assumption that `S(x)` is nonempty near `x̄` (for
  `x ∈ Ω`); since a Lipschitz constant `ℓ` may vanish we take `κ = 2 (ℓ + 1) / α`.
* In Prop. 6.18 local optimality of `z̄` is not needed (it follows from (6.47)); the KKT
  multipliers are indexed by all constraints with complementary slackness, and the derivatives
  `∇ψᵢ(z̄)` are only used for the active constraints.
-/

open Filter Topology Set Metric
open scoped NNReal

namespace VariationalAnalysis

variable {E F : Type*} {ι : Type*}

section Definitions

variable (f φ : E × F → ℝ) (g : ι → E × F → ℝ) (Ω : Set E)

/-- The lower-level constraint set `G(x) = {y | gᵢ(x, y) ≤ 0 for all i}` [Mordukhovich 2018,
(6.29)]. -/
def lowerFeasible (x : E) : Set F := {y | ∀ i, g i (x, y) ≤ 0}

/-- The lower-level value function `μ(x) = inf {φ(x, y) | y ∈ G(x)}` [Mordukhovich 2018, (6.33)]. -/
noncomputable def lowerValue : E → EReal := marginal (fun p ↦ (φ p : EReal)) (lowerFeasible g)

/-- The lower-level solution map `S(x) = argmin {φ(x, y) | y ∈ G(x)}` [Mordukhovich 2018,
(6.30)]. -/
def lowerSolution : E → Set F := argminMap (fun p ↦ (φ p : EReal)) (lowerFeasible g)

/-- The optimistic upper-level objective `f_opt(x) = inf {f(x, y) | y ∈ S(x)}` [Mordukhovich 2018,
(6.31)]. -/
noncomputable def optimisticValue (x : E) : EReal := ⨅ y ∈ lowerSolution φ g x, (f (x, y) : EReal)

/-- The pessimistic upper-level objective `f_pes(x) = sup {f(x, y) | y ∈ S(x)}`
[Mordukhovich 2018, (6.32)]. -/
noncomputable def pessimisticValue (x : E) : EReal :=
  ⨆ y ∈ lowerSolution φ g x, (f (x, y) : EReal)

/-- The lower-level solutions realizing the optimistic value, `S̃(x) = {y ∈ S(x) | f(x, y) =
f_opt(x)}` [Mordukhovich 2018, (6.36)] (see the module docstring). -/
def optimisticSolution (x : E) : Set F :=
  {y | y ∈ lowerSolution φ g x ∧ (f (x, y) : EReal) = optimisticValue f φ g x}

/-- The feasible set of the value function reformulation (6.34) of [Mordukhovich 2018]:
`x ∈ Ω`, `g(x, y) ≤ 0` and `φ(x, y) ≤ μ(x)`. -/
def valueFeasible : Set (E × F) :=
  {p | p.1 ∈ Ω ∧ p.2 ∈ lowerFeasible g p.1 ∧ (φ p : EReal) ≤ lowerValue φ g p.1}

/-- The objective `f + κ (φ - μ)` of the penalized problem (6.40) of [Mordukhovich 2018], written
`f + κ φ - κ μ` in `EReal`. -/
noncomputable def penalizedObjective (κ : ℝ) (p : E × F) : EReal :=
  ((f p + κ * φ p : ℝ) : EReal) - (κ : EReal) * lowerValue φ g p.1

end Definitions

/-- `P ⊆ Q` is a set of local weak sharp minima of `ϕ` over `Q` at `z₀ ∈ P` with modulus
`α > 0` [Mordukhovich 2018, Def. 6.16]: `ϕ(z) ≥ ϕ(z₀) + α dist(z; P)` for `z ∈ Q` near `z₀`
(6.42). -/
def IsLocalWeakSharpMin {Z : Type*} [PseudoMetricSpace Z] (ϕ : Z → ℝ) (P Q : Set Z) (z₀ : Z)
    (α : ℝ) : Prop :=
  P ⊆ Q ∧ z₀ ∈ P ∧ 0 < α ∧ ∀ᶠ z in 𝓝[Q] z₀, ϕ z₀ + α * infDist z P ≤ ϕ z

variable {f φ : E × F → ℝ} {g : ι → E × F → ℝ} {Ω : Set E} {x₀ : E} {y₀ : F}

/-- `y ∈ S(x)` iff `y ∈ G(x)` and `φ(x, y) = μ(x)`. -/
theorem mem_lowerSolution_iff {x : E} {y : F} :
    y ∈ lowerSolution φ g x ↔ y ∈ lowerFeasible g x ∧ (φ (x, y) : EReal) = lowerValue φ g x :=
  Iff.rfl

/-- `μ(x) = φ(x, y)` for a lower-level solution `y ∈ S(x)`. -/
theorem lowerValue_eq_of_mem_lowerSolution {x : E} {y : F} (hy : y ∈ lowerSolution φ g x) :
    lowerValue φ g x = φ (x, y) :=
  hy.2.symm

/-- `μ(x) ≤ φ(x, y)` for a lower-level feasible `y ∈ G(x)`. -/
theorem lowerValue_le {x : E} {y : F} (hy : y ∈ lowerFeasible g x) :
    lowerValue φ g x ≤ φ (x, y) :=
  marginal_le hy

/-- The feasible set of the value function reformulation is the graph of `S` over `Ω`: `(x, y)` is
feasible iff `x ∈ Ω` and `y ∈ S(x)`. -/
theorem mem_valueFeasible_iff {p : E × F} :
    p ∈ valueFeasible φ g Ω ↔ p.1 ∈ Ω ∧ p.2 ∈ lowerSolution φ g p.1 :=
  ⟨fun ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, le_antisymm h3 (lowerValue_le h2)⟩,
    fun ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, h3.le⟩⟩

/-- `f_opt(x) ≤ f(x, y)` for a lower-level solution `y ∈ S(x)`. -/
theorem optimisticValue_le {x : E} {y : F} (hy : y ∈ lowerSolution φ g x) :
    optimisticValue f φ g x ≤ f (x, y) :=
  iInf₂_le y hy

/-- `μ(x) < ∞` if `G(x)` is nonempty. -/
theorem lowerValue_ne_top {x : E} {y : F} (hy : y ∈ lowerFeasible g x) : lowerValue φ g x ≠ ⊤ :=
  ne_top_of_le_ne_top (EReal.coe_ne_top _) (lowerValue_le hy)

/-- Where `μ(x) = c` is finite, the penalized objective at `(x, y)` is the real number
`f(x, y) + κ φ(x, y) - κ c`. -/
theorem penalizedObjective_of_eq {κ c : ℝ} {p : E × F} (h : lowerValue φ g p.1 = c) :
    penalizedObjective f φ g κ p = ((f p + κ * φ p - κ * c : ℝ) : EReal) := by
  rw [penalizedObjective, h, ← EReal.coe_mul, ← EReal.coe_sub]

/-- Where `μ(x) = -∞`, the penalized objective with `κ > 0` equals `+∞`. -/
theorem penalizedObjective_of_eq_bot {κ : ℝ} (hκ : 0 < κ) {p : E × F}
    (h : lowerValue φ g p.1 = ⊥) : penalizedObjective f φ g κ p = ⊤ := by
  rw [penalizedObjective, h, EReal.coe_mul_bot_of_pos hκ, EReal.coe_sub_bot]

/-- On the feasible set of the value function reformulation the penalized objective equals `f`,
for every `κ`. -/
theorem penalizedObjective_of_mem_valueFeasible {κ : ℝ} {p : E × F}
    (hp : p ∈ valueFeasible φ g Ω) : penalizedObjective f φ g κ p = f p := by
  rw [penalizedObjective_of_eq (c := φ p) (mem_valueFeasible_iff.1 hp).2.2.symm]
  congr 1; ring

variable [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- Partial calmness with modulus `κ` [Mordukhovich 2018, Def. 6.14]: there is a neighborhood
`U` of `((x̄, ȳ), 0)` such that `f(x, y) - f(x̄, ȳ) + κ |ϑ| ≥ 0` (6.39) whenever
`((x, y), ϑ) ∈ U` is feasible for the perturbed problem (6.38): `x ∈ Ω`, `y ∈ G(x)` and
`μ(x) = φ(x, y) + ϑ`. -/
def PartiallyCalmWith (f φ : E × F → ℝ) (g : ι → E × F → ℝ) (Ω : Set E) (κ : ℝ) (x₀ : E)
    (y₀ : F) : Prop :=
  ∃ U ∈ 𝓝 (((x₀, y₀), (0 : ℝ)) : (E × F) × ℝ), ∀ x y ϑ, ((x, y), ϑ) ∈ U → x ∈ Ω →
    y ∈ lowerFeasible g x → lowerValue φ g x = ((φ (x, y) + ϑ : ℝ) : EReal) →
      f (x₀, y₀) ≤ f (x, y) + κ * |ϑ|

/-- The value function reformulation (6.34) is partially calm at `(x̄, ȳ)` [Mordukhovich 2018,
Def. 6.14]. -/
def PartiallyCalm (f φ : E × F → ℝ) (g : ι → E × F → ℝ) (Ω : Set E) (x₀ : E) (y₀ : F) : Prop :=
  ∃ κ > 0, PartiallyCalmWith f φ g Ω κ x₀ y₀

/-! ### Prop. 6.13: local solutions of optimistic bilevel programs -/

/-- Prop. 6.13(i) of [Mordukhovich 2018]: if `x̄` is a local optimal solution of the optimistic
bilevel program (6.31), then `(x̄, ȳ)` is a local optimal solution of (6.34) for every
`ȳ ∈ S̃(x̄)`. -/
theorem isLocalMinOn_valueFeasible_of_isLocalMinOn_optimisticValue
    (hmin : IsLocalMinOn (optimisticValue f φ g) Ω x₀) (hy₀ : y₀ ∈ optimisticSolution f φ g x₀) :
    IsLocalMinOn f (valueFeasible φ g Ω) (x₀, y₀) := by
  have hfst : Tendsto Prod.fst (𝓝[valueFeasible φ g Ω] (x₀, y₀)) (𝓝[Ω] x₀) :=
    tendsto_nhdsWithin_iff.2 ⟨(continuous_fst.tendsto _).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun p hp ↦ (mem_valueFeasible_iff.1 hp).1⟩
  filter_upwards [hfst.eventually hmin, self_mem_nhdsWithin] with p hp hpF
  have h := optimisticValue_le (f := f) (mem_valueFeasible_iff.1 hpF).2
  rw [← hy₀.2] at hp
  exact EReal.coe_le_coe_iff.1 (hp.trans h)

/-- Prop. 6.13(ii) of [Mordukhovich 2018]: let `(x̄, ȳ)`, `ȳ ∈ S̃(x̄)`, be a local optimal solution
of (6.34), let `S̃` be inner semicontinuous at `(x̄, ȳ)`, and let the infimum defining `f_opt` be
attained near `x̄` wherever it is finite. Then `x̄` is a local optimal solution of the optimistic
bilevel program (6.31). -/
theorem isLocalMinOn_optimisticValue_of_isLocalMinOn_valueFeasible
    (hmin : IsLocalMinOn f (valueFeasible φ g Ω) (x₀, y₀))
    (hy₀ : y₀ ∈ optimisticSolution f φ g x₀)
    (hisc : InnerSemicontinuousAt (optimisticSolution f φ g) x₀ y₀)
    (hatt : ∀ᶠ x in 𝓝 x₀, optimisticValue f φ g x ≠ ⊤ → (optimisticSolution f φ g x).Nonempty) :
    IsLocalMinOn (optimisticValue f φ g) Ω x₀ := by
  by_contra hcon
  rw [IsLocalMinOn, IsMinFilter, not_eventually] at hcon
  have hcon' : ∃ᶠ x in 𝓝[Ω] x₀, x ∈ Ω ∧ optimisticValue f φ g x < optimisticValue f φ g x₀ ∧
      (optimisticSolution f φ g x).Nonempty :=
    (hcon.and_eventually (eventually_mem_nhdsWithin.and (nhdsWithin_le_nhds hatt))).mono
      fun x ⟨hlt, hxΩ, hx⟩ ↦ ⟨hxΩ, not_le.1 hlt, hx (ne_top_of_lt (not_le.1 hlt))⟩
  obtain ⟨a, ha, haP⟩ := exists_seq_forall_of_frequently hcon'
  have ha' : Tendsto a atTop (𝓝[dom (optimisticSolution f φ g)] x₀) :=
    tendsto_nhdsWithin_iff.2 ⟨(tendsto_nhdsWithin_iff.1 ha).1,
      Eventually.of_forall fun k ↦ (haP k).2.2⟩
  obtain ⟨b, hb, hbmem⟩ := hisc a ha'
  have hab : Tendsto (fun k ↦ (a k, b k)) atTop (𝓝[valueFeasible φ g Ω] (x₀, y₀)) :=
    tendsto_nhdsWithin_iff.2 ⟨(tendsto_nhdsWithin_iff.1 ha).1.prodMk_nhds hb,
      hbmem.mono fun k hk ↦ mem_valueFeasible_iff.2 ⟨(haP k).1, hk.1⟩⟩
  obtain ⟨k, hk1, hk2⟩ := ((hab.eventually hmin).and hbmem).exists
  have h3 := (haP k).2.1
  rw [← hk2.2, ← hy₀.2] at h3
  exact absurd (EReal.coe_lt_coe_iff.1 h3) (not_lt.2 hk1)

/-! ### Prop. 6.15: penalization via partial calmness -/

/-- Prop. 6.15 of [Mordukhovich 2018], first part: if (6.34) is partially calm at its feasible
point `(x̄, ȳ)` with modulus `κ > 0` and `f` is continuous at `(x̄, ȳ)`, then `(x̄, ȳ)` is a local
optimal solution of the penalized problem (6.40): minimize `f + κ (φ - μ)` over `x ∈ Ω`,
`y ∈ G(x)`. -/
theorem isLocalMinOn_penalizedObjective {κ : ℝ} (hκ : 0 < κ)
    (hcalm : PartiallyCalmWith f φ g Ω κ x₀ y₀) (hf : ContinuousAt f (x₀, y₀))
    (hx : (x₀, y₀) ∈ valueFeasible φ g Ω) :
    IsLocalMinOn (penalizedObjective f φ g κ) {p | p.1 ∈ Ω ∧ p.2 ∈ lowerFeasible g p.1}
      (x₀, y₀) := by
  obtain ⟨U, hU, hcalm⟩ := hcalm
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  have hfc : ∀ᶠ p in 𝓝 (x₀, y₀), |f p - f (x₀, y₀)| < κ * r := by
    have := hf.eventually (Metric.ball_mem_nhds (f (x₀, y₀)) (mul_pos hκ hr))
    exact this.mono fun p hp ↦ by rwa [Real.dist_eq] at hp
  have hval : penalizedObjective f φ g κ (x₀, y₀) = f (x₀, y₀) :=
    penalizedObjective_of_mem_valueFeasible hx
  filter_upwards [nhdsWithin_le_nhds (hfc.and (ball_mem_nhds _ hr)), self_mem_nhdsWithin] with
    p ⟨hp1, hp2⟩ ⟨hpΩ, hpG⟩
  rw [hval]
  have hle : lowerValue φ g p.1 ≤ φ p := lowerValue_le hpG
  induction h : lowerValue φ g p.1 with
  | bot => rw [penalizedObjective_of_eq_bot hκ h]; exact le_top
  | top => exact absurd h (lowerValue_ne_top hpG)
  | coe c =>
    rw [penalizedObjective_of_eq h, EReal.coe_le_coe_iff]
    rw [h, EReal.coe_le_coe_iff] at hle
    have habs : |c - φ p| = φ p - c := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    by_cases hϑ : φ p - c < r
    · have hmem : ((p.1, p.2), c - φ p) ∈ U := hrU (by
        rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, sub_zero, habs]
        exact ⟨hp2, hϑ⟩)
      have := hcalm p.1 p.2 (c - φ p) hmem hpΩ hpG (by rw [h]; congr 1; ring)
      rw [habs] at this
      linarith
    · push Not at hϑ
      have := (abs_lt.1 hp1).1
      nlinarith

/-- Prop. 6.15 of [Mordukhovich 2018], converse: a local optimal solution `(x̄, ȳ)` of the
penalized problem (6.40) that is feasible for (6.34) is partially calm with modulus `κ`. -/
theorem partiallyCalmWith_of_isLocalMinOn_penalizedObjective {κ : ℝ}
    (hx : (x₀, y₀) ∈ valueFeasible φ g Ω)
    (hmin : IsLocalMinOn (penalizedObjective f φ g κ) {p | p.1 ∈ Ω ∧ p.2 ∈ lowerFeasible g p.1}
      (x₀, y₀)) :
    PartiallyCalmWith f φ g Ω κ x₀ y₀ := by
  obtain ⟨V, hV, hVmin⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hmin
  refine ⟨Prod.fst ⁻¹' V, (continuous_fst.tendsto _) hV, fun x y ϑ hU hxΩ hyG hμ ↦ ?_⟩
  have := hVmin ⟨hU, hxΩ, hyG⟩
  simp only [mem_ofPred_eq] at this
  rw [penalizedObjective_of_mem_valueFeasible hx, penalizedObjective_of_eq hμ,
    EReal.coe_le_coe_iff] at this
  have hle := lowerValue_le (φ := φ) hyG
  rw [hμ, EReal.coe_le_coe_iff] at hle
  rw [abs_of_nonpos (by linarith)]
  linarith

/-! ### Prop. 6.17: partial calmness from uniform weak sharp minima -/

/-- Prop. 6.17 of [Mordukhovich 2018]: let `(x̄, ȳ)` be a local optimal solution of (6.34)
satisfying the uniform weak sharp minimum condition (6.43)
`φ(x, y) - μ(x) ≥ α dist(y; S(x))` for `(x, y)` near `(x̄, ȳ)`, `x ∈ Ω`, `y ∈ G(x)`. If `f` is
Lipschitz around `(x̄, ȳ)` and `S(x) ≠ ∅` for `x ∈ Ω` near `x̄`, then (6.34) is partially calm at
`(x̄, ȳ)`. -/
theorem partiallyCalm_of_uniform_weakSharp (hmin : IsLocalMinOn f (valueFeasible φ g Ω) (x₀, y₀))
    {α : ℝ} (hα : 0 < α)
    (hwsm : ∀ᶠ p in 𝓝 (x₀, y₀), p.1 ∈ Ω → p.2 ∈ lowerFeasible g p.1 →
      lowerValue φ g p.1 + ((α * infDist p.2 (lowerSolution φ g p.1) : ℝ) : EReal) ≤ φ p)
    (hne : ∀ᶠ x in 𝓝 x₀, x ∈ Ω → (lowerSolution φ g x).Nonempty)
    {U : Set (E × F)} {L : ℝ≥0} (hU : U ∈ 𝓝 (x₀, y₀)) (hL : LipschitzOnWith L f U) :
    PartiallyCalm f φ g Ω x₀ y₀ := by
  have hall : ∀ᶠ p in 𝓝 (x₀, y₀), p ∈ U ∧ (p.1 ∈ Ω → p.2 ∈ lowerFeasible g p.1 →
      lowerValue φ g p.1 + ((α * infDist p.2 (lowerSolution φ g p.1) : ℝ) : EReal) ≤ φ p) ∧
      (p ∈ valueFeasible φ g Ω → f (x₀, y₀) ≤ f p) ∧
      (p.1 ∈ Ω → (lowerSolution φ g p.1).Nonempty) :=
    (show ∀ᶠ p in 𝓝 (x₀, y₀), p ∈ U from hU).and (hwsm.and ((eventually_nhdsWithin_iff.1 hmin).and
      ((continuous_fst.tendsto (x₀, y₀)).eventually hne)))
  obtain ⟨r, hr, hrP⟩ := Metric.eventually_nhds_iff.1 hall
  set κ : ℝ := 2 * ((L : ℝ) + 1) / α
  refine ⟨κ, by positivity, Prod.fst ⁻¹' ball (x₀, y₀) (r / 2) ∩
    Prod.snd ⁻¹' ball 0 (α * r / 8), inter_mem ((continuous_fst.tendsto _)
      (ball_mem_nhds _ (half_pos hr))) ((continuous_snd.tendsto _)
      (ball_mem_nhds _ (by positivity))), fun x y ϑ ⟨hp, hϑ⟩ hxΩ hyG hμ ↦ ?_⟩
  simp only [mem_preimage, mem_ball, Real.dist_eq, sub_zero] at hp hϑ
  obtain ⟨hpU, hpw, -, hpne⟩ := hrP (hp.trans (half_lt_self hr))
  -- `α dist(y; S(x)) ≤ -ϑ`
  have hd := hpw hxΩ hyG
  rw [hμ, ← EReal.coe_add, EReal.coe_le_coe_iff] at hd
  have hd0 := infDist_nonneg (x := y) (s := lowerSolution φ g x)
  have hϑ0 : ϑ ≤ 0 := by nlinarith
  -- a nearby lower-level solution `v`
  obtain ⟨v, hvS, hvy⟩ : ∃ v ∈ lowerSolution φ g x, dist y v ≤ -2 * ϑ / α := by
    rcases hϑ0.lt_or_eq with hlt | rfl
    · obtain ⟨v, hv, hvd⟩ := (infDist_lt_iff (hpne hxΩ)).1
        (show infDist y (lowerSolution φ g x) < -2 * ϑ / α by
          rw [lt_div_iff₀ hα]; nlinarith)
      exact ⟨v, hv, hvd.le⟩
    · refine ⟨y, ⟨hyG, ?_⟩, by simp⟩
      change (φ (x, y) : EReal) = lowerValue φ g x
      rw [hμ, add_zero]
  have hϑr : -2 * ϑ / α < r / 4 := by
    rw [div_lt_iff₀ hα]; rw [abs_lt] at hϑ; nlinarith
  have hxv : dist (x, v) (x₀, y₀) < r := by
    rw [Prod.dist_eq] at hp ⊢
    have h1 : dist v y₀ ≤ dist v y + dist y y₀ := dist_triangle _ _ _
    rw [dist_comm] at hvy
    exact max_lt (by linarith [le_max_left (dist x x₀) (dist y y₀)])
      (by linarith [le_max_right (dist x x₀) (dist y y₀)])
  obtain ⟨hvU, -, hvmin, -⟩ := hrP hxv
  have hfv := hvmin (mem_valueFeasible_iff.2 ⟨hxΩ, hvS⟩)
  have hlip := hL.dist_le_mul _ hpU _ hvU
  rw [Prod.dist_eq, dist_self, Real.dist_eq] at hlip
  rw [max_eq_right dist_nonneg] at hlip
  rw [abs_of_nonpos hϑ0]
  have hκ : (L : ℝ) * dist y v ≤ κ * -ϑ := by
    calc (L : ℝ) * dist y v ≤ L * (-2 * ϑ / α) :=
          mul_le_mul_of_nonneg_left hvy L.coe_nonneg
      _ ≤ ((L : ℝ) + 1) * (-2 * ϑ / α) :=
          mul_le_mul_of_nonneg_right (by linarith) (div_nonneg (by linarith) hα.le)
      _ = κ * -ϑ := by simp only [κ]; ring
  linarith [(abs_le.1 hlip).1]

/-! ### Prop. 6.18: weak sharp minima in nonlinear programming -/

section WeakSharp

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [Fintype ι]

/-- Prop. 6.18 of [Mordukhovich 2018] (weak sharp minima from the KKT conditions), (6.47): let
`ϕ` be differentiable at `z̄`, the active constraints `ψᵢ` (`ψᵢ(z̄) = 0`) differentiable at `z̄`,
and let `∇ϕ(z̄) + ∑ λᵢ ∇ψᵢ(z̄) = 0` with `λᵢ ≥ 0`, `λᵢ ψᵢ(z̄) = 0`, satisfying the kernel condition
(6.46) `⋂_{λᵢ > 0} ker ∇ψᵢ(z̄) = {0}`. Then `ϕ(z) - ϕ(z̄) ≥ α ‖z - z̄‖` for some `α > 0` and all
`z` near `z̄` with `ψᵢ(z) ≤ 0`. -/
theorem exists_weakSharp_of_kkt {ϕ : Z → ℝ} {ψ : ι → Z → ℝ} {z₀ : Z} {ϕ' : StrongDual ℝ Z}
    {ψ' : ι → StrongDual ℝ Z} (hϕ : HasFDerivAt ϕ ϕ' z₀)
    (hψ : ∀ i, ψ i z₀ = 0 → HasFDerivAt (ψ i) (ψ' i) z₀) (lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hcs : ∀ i, lam i * ψ i z₀ = 0) (hkkt : ϕ' + ∑ i, lam i • ψ' i = 0)
    (hker : ∀ d : Z, (∀ i, 0 < lam i → ψ' i d = 0) → d = 0) :
    ∃ α > 0, ∀ᶠ z in 𝓝 z₀, (∀ i, ψ i z ≤ 0) → ϕ z₀ + α * ‖z - z₀‖ ≤ ϕ z := by
  classical
  set I := Finset.univ.filter fun i ↦ ψ i z₀ = 0
  have hactive : ∀ i, 0 < lam i → ψ i z₀ = 0 := fun i hi ↦
    (mul_eq_zero.1 (hcs i)).resolve_left hi.ne'
  set h : Z → ℝ := fun d ↦ max (ϕ' d) (∑ i ∈ I, max (ψ' i d) 0)
  have hcont : Continuous h :=
    ϕ'.continuous.max (continuous_finsetSum _ fun i _ ↦ (ψ' i).continuous.max continuous_const)
  have hpos : ∀ d : Z, ‖d‖ = 1 → 0 < h d := by
    intro d hd
    by_contra hle
    push Not at hle
    have h1 : ϕ' d ≤ 0 := (le_max_left _ _).trans hle
    have h3 : ∀ i ∈ I, max (ψ' i d) 0 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ le_max_right _ _).1
        (le_antisymm ((le_max_right _ _).trans hle)
          (Finset.sum_nonneg fun i _ ↦ le_max_right _ _))
    have hterm : ∀ i, lam i * ψ' i d ≤ 0 := fun i ↦ by
      rcases (hlam i).lt_or_eq with hi | hi
      · have := h3 i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hactive i hi⟩)
        exact mul_nonpos_of_nonneg_of_nonpos hi.le (by
          have := le_max_left (ψ' i d) 0; linarith)
      · rw [← hi, zero_mul]
    have hk : ϕ' d + ∑ i, lam i * ψ' i d = 0 := by
      have := congrArg (fun T : StrongDual ℝ Z ↦ T d) hkkt
      simpa using this
    have hsum : ∑ i, lam i * ψ' i d = 0 :=
      le_antisymm (Finset.sum_nonpos fun i _ ↦ hterm i) (by linarith)
    have h0 := (Finset.sum_eq_zero_iff_of_nonpos fun i _ ↦ hterm i).1 hsum
    have : d = 0 := hker d fun i hi ↦
      (mul_eq_zero.1 (h0 i (Finset.mem_univ _))).resolve_left hi.ne'
    rw [this, norm_zero] at hd
    exact zero_ne_one hd
  by_cases hS : (sphere (0 : Z) 1).Nonempty
  swap
  · refine ⟨1, one_pos, Eventually.of_forall fun z _ ↦ ?_⟩
    have : z = z₀ := by
      by_contra hz
      have hn : ‖z - z₀‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hz)
      exact hS ⟨‖z - z₀‖⁻¹ • (z - z₀), by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]⟩
    simp [this]
  obtain ⟨d₀, hd₀, hmin⟩ := (isCompact_sphere (0 : Z) 1).exists_isMinOn hS hcont.continuousOn
  set m := h d₀
  have hm : 0 < m := hpos d₀ (mem_sphere_zero_iff_norm.1 hd₀)
  set ε := m / (2 * ((I.card : ℝ) + 1))
  have hε : 0 < ε := by positivity
  have hεm : (I.card : ℝ) * ε < m := by
    simp only [ε]
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  have eϕ := hϕ.isLittleO.bound (half_pos hm)
  have eψ : ∀ᶠ z in 𝓝 z₀, ∀ i ∈ I, ‖ψ i z - ψ i z₀ - ψ' i (z - z₀)‖ ≤ ε * ‖z - z₀‖ :=
    (Finset.eventually_all I).2 fun i hi ↦
      (hψ i (Finset.mem_filter.1 hi).2).isLittleO.bound hε
  refine ⟨m / 2, half_pos hm, ?_⟩
  filter_upwards [eϕ, eψ] with z hzϕ hzψ hfeas
  rcases eq_or_ne z z₀ with rfl | hz
  · simp
  set n := ‖z - z₀‖
  have hn : 0 < n := norm_pos_iff.2 (sub_ne_zero.2 hz)
  set d := n⁻¹ • (z - z₀)
  have hd : ‖d‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hzd : z - z₀ = n • d := by simp [d, smul_smul, mul_inv_cancel₀ hn.ne']
  have hhd : m ≤ h d := hmin (mem_sphere_zero_iff_norm.2 hd)
  -- the active constraints have nearly nonpositive slope along `d`
  have hψd : ∀ i ∈ I, max (ψ' i d) 0 ≤ ε := by
    intro i hi
    have h1 := (abs_le.1 (hzψ i hi)).1
    rw [(Finset.mem_filter.1 hi).2, hzd, map_smul, smul_eq_mul] at h1
    have h2 := hfeas i
    have : ψ' i d ≤ ε := by
      by_contra hc
      push Not at hc
      nlinarith
    exact max_le this hε.le
  have hsum : ∑ i ∈ I, max (ψ' i d) 0 < m := by
    calc ∑ i ∈ I, max (ψ' i d) 0 ≤ ∑ _i ∈ I, ε := Finset.sum_le_sum hψd
      _ = I.card * ε := by simp
      _ < m := hεm
  have hϕd : m ≤ ϕ' d := by
    by_contra hc
    push Not at hc
    exact absurd hhd (not_le.2 (max_lt hc hsum))
  have h1 := (abs_le.1 (show |ϕ z - ϕ z₀ - ϕ' (z - z₀)| ≤ m / 2 * n from hzϕ)).1
  rw [hzd, map_smul, smul_eq_mul] at h1
  nlinarith

/-- Prop. 6.18 of [Mordukhovich 2018], conclusion: under the assumptions of
`exists_weakSharp_of_kkt`, if `z̄` is feasible then `{z̄}` is a set of local weak sharp minima of
`ϕ` over `Q = {z | ψᵢ(z) ≤ 0 for all i}` at `z̄`. -/
theorem isLocalWeakSharpMin_of_kkt {ϕ : Z → ℝ} {ψ : ι → Z → ℝ} {z₀ : Z} {ϕ' : StrongDual ℝ Z}
    {ψ' : ι → StrongDual ℝ Z} (hz₀ : ∀ i, ψ i z₀ ≤ 0) (hϕ : HasFDerivAt ϕ ϕ' z₀)
    (hψ : ∀ i, ψ i z₀ = 0 → HasFDerivAt (ψ i) (ψ' i) z₀) (lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hcs : ∀ i, lam i * ψ i z₀ = 0) (hkkt : ϕ' + ∑ i, lam i • ψ' i = 0)
    (hker : ∀ d : Z, (∀ i, 0 < lam i → ψ' i d = 0) → d = 0) :
    ∃ α, IsLocalWeakSharpMin ϕ {z₀} {z | ∀ i, ψ i z ≤ 0} z₀ α := by
  obtain ⟨α, hα, h⟩ := exists_weakSharp_of_kkt hϕ hψ lam hlam hcs hkkt hker
  refine ⟨α, singleton_subset_iff.2 hz₀, rfl, hα, ?_⟩
  filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with z hz hzQ
  rw [infDist_singleton, dist_eq_norm]
  exact hz hzQ

end WeakSharp

end VariationalAnalysis
