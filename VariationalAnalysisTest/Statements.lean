/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis

/-!
# Statements of the main results

Each `example` restates one of the results listed under "Selected results" in `README.md`,
with all its hypotheses written out, and proves it by the library theorem. If a change to the
library alters the statement of one of these theorems (a new hypothesis, a weaker conclusion, a
renamed definition), this file stops compiling. Changing an `example` here is therefore a
breaking change, to be recorded in `CHANGELOG.md`.
-/

open VariationalAnalysis Set Metric Filter Topology Pointwise

section Normed

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Ekeland's variational principle [Mordukhovich 2018, Thm. 2.13]. -/
example {φ : E → EReal} {x₀ : E} {ε ρ : ℝ} (hφ : LowerSemicontinuous φ)
    (hbdd : ∃ m : ℝ, ∀ x, (m : EReal) ≤ φ x) (hε : 0 < ε) (hρ : 0 < ρ) (hx₀ : φ x₀ ≠ ⊤)
    (hmin : φ x₀ ≤ (⨅ x, φ x) + ε) :
    ∃ z, ‖z - x₀‖ ≤ ρ ∧ φ z ≤ φ x₀ ∧ ∀ x, x ≠ z → φ z < φ x + ↑(ε / ρ * ‖x - z‖) :=
  ekeland_variational_principle hφ hbdd hε hρ hx₀ hmin

/-- The basic extremal principle [Mordukhovich 2018, Thm. 2.3]. -/
example {ι : Type*} [Fintype ι] {Ω : ι → Set E} {x₀ : E} (hext : IsLocallyExtremal Ω x₀)
    (hcl : ∀ i, ∃ r > 0, IsClosed (Ω i ∩ closedBall x₀ r)) :
    ∃ v : ι → StrongDual ℝ E,
      (∀ i, v i ∈ normalCone (Ω i) x₀) ∧ ∑ i, v i = 0 ∧ ∑ i, ‖v i‖ ^ 2 = 1 :=
  hext.exists_mem_normalCone hcl

/-- Normals to intersections [Mordukhovich 2018, Thm. 2.16]. -/
example {Ω₁ Ω₂ : Set E} {x₀ : E} (h₁ : ∃ r > 0, IsClosed (Ω₁ ∩ closedBall x₀ r))
    (h₂ : ∃ r > 0, IsClosed (Ω₂ ∩ closedBall x₀ r))
    (hqc : ∀ v ∈ normalCone Ω₁ x₀, -v ∈ normalCone Ω₂ x₀ → v = 0) :
    normalCone (Ω₁ ∩ Ω₂) x₀ ⊆ normalCone Ω₁ x₀ + normalCone Ω₂ x₀ :=
  normalCone_inter_subset h₁ h₂ hqc

/-- The subdifferential sum rule [Mordukhovich 2018, Thm. 2.19, (2.35)]. -/
example {φ₁ φ₂ : E → EReal} {x₀ : E} {r₁ r₂ : ℝ} (hr₁ : φ₁ x₀ = r₁) (hr₂ : φ₂ x₀ = r₂)
    (h₁ : ∃ ρ > 0, IsClosed (Function.Epi φ₁ univ ∩ closedBall (x₀, r₁) ρ))
    (h₂ : ∃ ρ > 0, IsClosed (Function.Epi φ₂ univ ∩ closedBall (x₀, r₂) ρ))
    (hqc : ∀ v ∈ singularSubdiff φ₁ x₀, -v ∈ singularSubdiff φ₂ x₀ → v = 0) :
    subdiff (fun x ↦ φ₁ x + φ₂ x) x₀ ⊆ subdiff φ₁ x₀ + subdiff φ₂ x₀ :=
  subdiff_add_subset hr₁ hr₂ h₁ h₂ hqc

/-- The Mordukhovich criterion for metric regularity [Mordukhovich 2018, Thm. 3.3(ii)]. -/
example {S : E → Set F} {x₀ : E} {y₀ : F}
    (hcl : ∃ ρ > 0, IsClosed (graph S ∩ closedBall (x₀, y₀) ρ)) (hy₀ : y₀ ∈ S x₀) :
    MetricallyRegularAt S x₀ y₀ ↔ coderivKer S x₀ y₀ = {0} :=
  metricallyRegularAt_iff_coderivKer_eq hcl hy₀

/-- Covering is equivalent to metric regularity [Mordukhovich 2018, Thm. 3.2(i)]. -/
example [Nontrivial E] {S : E → Set F} {x₀ : E} {y₀ : F} (hy₀ : y₀ ∈ S x₀) :
    HasCoveringAt S x₀ y₀ ↔ MetricallyRegularAt S x₀ y₀ :=
  hasCoveringAt_iff_metricallyRegularAt hy₀

/-- The symmetric mean value theorem [Mordukhovich 2018, Thm. 4.11]. -/
example {a b : E} {f : E → ℝ} {U : Set E} (hU : IsOpen U) (hseg : segment ℝ a b ⊆ U)
    (hf : ContinuousOn f U)
    (hqc : ∀ x ∈ openSegment ℝ a b, ∀ v ∈ symmSingularSubdiff (fun y ↦ (f y : EReal)) x,
      v (b - a) = 0 → v = 0) :
    ∃ c ∈ openSegment ℝ a b, ∃ v ∈ symmSubdiff (fun y ↦ (f y : EReal)) c,
      f b - f a = v (b - a) :=
  symmetric_mean_value hU hseg hf hqc

/-- Tangential preduality `N̂ = T*` [Mordukhovich 2018, Prop. 1.9]. -/
example {Ω : Set E} {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    regularNormalCone Ω x₀ = {v | ∀ w ∈ contingentCone Ω x₀, v w ≤ 0} :=
  regularNormalCone_eq_polar_contingentCone hx₀

/-- Rockafellar's theorem: the maximal cyclically monotone mappings are the subdifferentials
of proper l.s.c. convex functions [Mordukhovich 2024, Lemma 1.97]. -/
example {T : E → Set (StrongDual ℝ E)} :
    MaximalCyclicallyMonotone T ↔
      ∃ φ : E → EReal, Convex ℝ (Function.Epi φ univ) ∧ LowerSemicontinuous φ ∧
        (∀ y, φ y ≠ ⊥) ∧ (∃ y, φ y ≠ ⊤) ∧ T = subdiff φ :=
  maximalCyclicallyMonotone_iff

end Normed

section NoDimension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For convex sets the limiting and regular normal cones agree
[Mordukhovich 2018, Prop. 1.7]. -/
example {Ω : Set E} {x₀ : E} (hΩ : Convex ℝ Ω) :
    normalCone Ω x₀ = regularNormalCone Ω x₀ :=
  normalCone_eq_regularNormalCone_of_convex hΩ

end NoDimension

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Minty's theorem: a monotone operator is maximal iff `I + T` is onto. -/
example {T : E → Set E} :
    IsMaximalMonotoneOp T ↔ IsMonotoneOp T ∧ ∀ u, ∃ x, u - x ∈ T x :=
  isMaximalMonotoneOp_iff

/-- Local superlinear convergence of the SCD semismooth* Newton method
[Gfrerer–Outrata 2022, Thm. 5.4]. -/
example {F : E → Set E} {xbar : E} (h : IsSCDSemismoothStarAt F (xbar, 0)) {η : ℝ} (hη : 0 < η)
    (κ : ℝ) (happ : ∀ᶠ x in 𝓝 xbar, 0 ∉ F x → (newtonApproxSet F xbar η κ x).Nonempty) :
    ∃ δ > 0, ∀ x₀, ‖x₀ - xbar‖ < δ →
      (∃ x : ℕ → E, x 0 = x₀ ∧ IsSCDNewtonSeq F xbar η κ x) ∧
        ∀ x : ℕ → E, x 0 = x₀ → IsSCDNewtonSeq F xbar η κ x → SCDNewtonConverges F xbar x :=
  h.scdNewton_converges hη κ happ

/-- For continuously prox-regular functions, twice epi-differentiability of `φ` is equivalent
to proto-differentiability of `∂φ` [Mordukhovich 2024, Thm. 1.98]. -/
example {φ : E → EReal} {x₀ g : E}
    (h : ContinuouslyProxRegularFor φ x₀ (InnerProductSpace.toDual ℝ E g)) :
    TwiceEpiDifferentiableAt φ x₀ (InnerProductSpace.toDual ℝ E g) ↔
      ProtoDifferentiableAt (subdiff φ) x₀ (InnerProductSpace.toDual ℝ E g) :=
  h.twiceEpiDifferentiableAt_iff_protoDifferentiableAt

end Inner
