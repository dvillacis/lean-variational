/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.MetricSpace.HausdorffDistance
import VariationalAnalysis.SetValued.Basic

/-!
# Well-posedness of set-valued mappings: covering, metric regularity, Lipschitz-like property

For a set-valued mapping `S : E ⇉ F` and a point `(x₀, y₀) ∈ gph S`,
[Mordukhovich 2018, Def. 3.1] introduces three well-posedness properties around `(x₀, y₀)`:

* (a) *covering* (linear openness) with modulus `κ > 0`: there are neighborhoods `U ∋ x₀`,
  `V ∋ y₀` with `S x ∩ V + κ r 𝔹 ⊆ S (x + r 𝔹)` whenever `x + r 𝔹 ⊆ U`, `r > 0`;
* (b) *metric regularity* with modulus `μ > 0`: `dist(x; S⁻¹ y) ≤ μ dist(y; S x)` for
  `x ∈ U`, `y ∈ V`;
* (c) the *Lipschitz-like* (Aubin, pseudo-Lipschitz) property with modulus `ℓ ≥ 0`:
  `S x ∩ V ⊆ S u + ℓ ‖x - u‖ 𝔹` for `x, u ∈ U`;

together with the exact bounds `cov S (x₀, y₀)` (supremum of covering moduli), `reg S (x₀, y₀)`
and `lip S (x₀, y₀)` (infima of the regularity and Lipschitz-like moduli).

## Design choices

* The definitions and all results except Step 2 of Thm. 3.2 are stated in metric spaces `E`, `F`
  (the book notes that the proof of Thm. 3.2 works in any metric space). `x + r 𝔹` is
  `closedBall x r`, and the pointwise-sum inclusions of (3.1) and (3.3) are unfolded
  elementwise.
* The book uses `dist(·; ∅) = ∞`, while Mathlib's `Metric.infDist x ∅ = 0`. Metric regularity
  is therefore stated with the extended distance `Metric.infEDist : ℝ≥0∞`, for which
  `infEDist x ∅ = ∞`: the estimate `infEDist x (S⁻¹ y) ≤ μ * infEDist y (S x)` in `ℝ≥0∞`
  says in particular that `S⁻¹ y ≠ ∅` whenever `S x ≠ ∅`, as in the book.
  `infEDist_le_mul_infEDist_iff` turns it into an elementwise real inequality.
* Moduli are nonnegative reals `ℝ≥0` (as in Mathlib's `LipschitzWith`), with `0 < κ` and
  `0 < μ` part of the definitions (a) and (b). The exact bounds take values in `ℝ≥0∞`:
  `covBound = 0` when `S` has no covering modulus, `regBound = ∞` (resp. `lipBound = ∞`) when
  `S` is not metrically regular (resp. Lipschitz-like). With these conventions
  `covBound = regBound⁻¹` holds literally, in all cases.
* Step 2 of Thm. 3.2 (metric regularity implies covering) needs `E` to be a nontrivial real
  normed space: the inclusion `closedBall x r ⊆ ball x₀ ν` must force `r < ν`. For `E = {0}`
  the equivalence fails (`S 0 = ball 0 1 ⊆ ℝ` is metrically regular around `(0, 0)`, with any
  modulus, but has no covering property). The book works in `ℝⁿ`, `n ≥ 1`.

## Main declarations

* `HasCoveringWith κ S x₀ y₀`, `MetricallyRegularWith μ S x₀ y₀`, `LipschitzLikeWith ℓ S x₀ y₀`:
  Def. 3.1(a)–(c) of [Mordukhovich 2018] with a given modulus.
* `HasCoveringAt`, `MetricallyRegularAt`, `LipschitzLikeAt`: the properties with some modulus.
* `covBound`, `regBound`, `lipBound`: the exact covering, regularity and Lipschitzian bounds
  `cov S (x₀, y₀)`, `reg S (x₀, y₀)`, `lip S (x₀, y₀)` of Def. 3.1.

## Main results

* `HasCoveringWith.eventually`, `MetricallyRegularWith.eventually`,
  `LipschitzLikeWith.eventually`: robustness [Mordukhovich 2018, p. 104]: each property holds
  with the same modulus around all nearby points.
* `infEDist_le_mul_infEDist_iff`, `metricallyRegularWith_iff`: elementwise form of (3.2).
* `metricallyRegularWith_of_infEDist_le`, `metricallyRegularWith_of_forall_dist_lt`: Step 1 of
  the proof of Thm. 3.2 of [Mordukhovich 2018]: metric regularity needs only be checked where
  `dist(y; S x) ≤ γ`.
* `MetricallyRegularWith.hasCoveringWith`, `HasCoveringWith.metricallyRegularWith`: Steps 2
  and 3 of the proof of Thm. 3.2.
* `hasCoveringAt_iff_metricallyRegularAt`, `covBound_eq_inv_regBound`: Thm. 3.2(i) of
  [Mordukhovich 2018]: covering ⇔ metric regularity, with `cov S (x₀, y₀) = reg S (x₀, y₀)⁻¹`.
* `LipschitzLikeWith.metricallyRegularWith_invMap`,
  `MetricallyRegularWith.lipschitzLikeWith_of_invMap`: Steps 4 and 5 of the proof of Thm. 3.2.
* `lipschitzLikeAt_iff_metricallyRegularAt_invMap`, `lipBound_eq_regBound_invMap` (and, for
  `S⁻¹`, `metricallyRegularAt_iff_lipschitzLikeAt_invMap`, `regBound_eq_lipBound_invMap`):
  Thm. 3.2(ii) of [Mordukhovich 2018]: `S` is Lipschitz-like around `(x₀, y₀)` iff `S⁻¹` is
  metrically regular around `(y₀, x₀)`, with `lip S (x₀, y₀) = reg S⁻¹ (y₀, x₀)`
  [Clason–Valkonen, Thm. 27.3] (there the Aubin property is defined by the metric regularity
  of the inverse, (27.1), and Thm. 27.3 shows the equivalence with the inclusion (3.3)).
-/

open Filter Topology Set Metric
open scoped NNReal ENNReal

namespace VariationalAnalysis

/-- The inverse of the inverse is the mapping itself. -/
@[simp] theorem invMap_invMap {E F : Type*} (S : E → Set F) : invMap (invMap S) = S := rfl

section Distance

variable {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]

/-- Elementwise form of an estimate `dist(x; A) ≤ μ dist(y; B)` between extended distances
(`dist(·; ∅) = ∞`): for every `b ∈ B` and `ε > 0` there is `a ∈ A` with
`dist x a < μ dist y b + ε`. -/
theorem infEDist_le_mul_infEDist_iff {μ : ℝ≥0} (hμ : 0 < μ) {x : α} {A : Set α} {y : β}
    {B : Set β} :
    infEDist x A ≤ μ * infEDist y B ↔ ∀ b ∈ B, ∀ ε > 0, ∃ a ∈ A, dist x a < μ * dist y b + ε := by
  constructor
  · intro h b hb ε hε
    have h1 : infEDist x A < ENNReal.ofReal (μ * dist y b + ε) := by
      calc infEDist x A ≤ μ * infEDist y B := h
        _ ≤ μ * edist y b := by gcongr; exact infEDist_le_edist_of_mem hb
        _ = ENNReal.ofReal (μ * dist y b) := by
            rw [edist_dist, ENNReal.ofReal_mul μ.coe_nonneg, ENNReal.ofReal_coe_nnreal]
        _ < ENNReal.ofReal (μ * dist y b + ε) :=
            (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
    obtain ⟨a, ha, hlt⟩ := infEDist_lt_iff.1 h1
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff (by positivity)] at hlt
    exact ⟨a, ha, hlt⟩
  · intro h
    rw [show infEDist y B = ⨅ b ∈ B, edist y b from rfl,
      ENNReal.mul_iInf_of_ne (by exact_mod_cast hμ.ne') ENNReal.coe_ne_top]
    refine le_iInf fun b ↦ ?_
    rw [ENNReal.mul_iInf_of_ne (by exact_mod_cast hμ.ne') ENNReal.coe_ne_top]
    refine le_iInf fun hb ↦ ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
    obtain ⟨a, ha, hlt⟩ := h b hb ε (by exact_mod_cast hε)
    calc infEDist x A ≤ edist x a := infEDist_le_edist_of_mem ha
      _ = ENNReal.ofReal (dist x a) := edist_dist _ _
      _ ≤ ENNReal.ofReal (μ * dist y b + ε) := ENNReal.ofReal_le_ofReal hlt.le
      _ = μ * edist y b + ε := by
          rw [ENNReal.ofReal_add (by positivity) ε.coe_nonneg, ENNReal.ofReal_mul μ.coe_nonneg,
            ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal, edist_dist]

end Distance

section Definitions

variable {E F : Type*} [MetricSpace E] [MetricSpace F]

/-- Def. 3.1(a) of [Mordukhovich 2018] (covering, or linear openness, with modulus `κ > 0`
around `(x₀, y₀)`): there are neighborhoods `U` of `x₀` and `V` of `y₀` such that
`S x ∩ V + κ r 𝔹 ⊆ S (x + r 𝔹)` whenever `x + r 𝔹 ⊆ U` and `r > 0` (3.1). The inclusion is
unfolded: every `y'` within `κ r` of a point `y ∈ S x ∩ V` lies in `S x'` for some `x'` within
`r` of `x`. -/
def HasCoveringWith (κ : ℝ≥0) (S : E → Set F) (x₀ : E) (y₀ : F) : Prop :=
  0 < κ ∧ ∃ U ∈ 𝓝 x₀, ∃ V ∈ 𝓝 y₀, ∀ (x : E) (r : ℝ), 0 < r → closedBall x r ⊆ U →
    ∀ y ∈ S x ∩ V, ∀ y', dist y' y ≤ κ * r → ∃ x', dist x' x ≤ r ∧ y' ∈ S x'

/-- Def. 3.1(b) of [Mordukhovich 2018] (metric regularity with modulus `μ > 0` around
`(x₀, y₀)`): there are neighborhoods `U` of `x₀` and `V` of `y₀` such that
`dist(x; S⁻¹ y) ≤ μ dist(y; S x)` for all `x ∈ U`, `y ∈ V` (3.2). Distances are extended
distances `infEDist` in `ℝ≥0∞`, so that, as in the book, the distance to `∅` is `∞`. -/
def MetricallyRegularWith (μ : ℝ≥0) (S : E → Set F) (x₀ : E) (y₀ : F) : Prop :=
  0 < μ ∧ ∃ U ∈ 𝓝 x₀, ∃ V ∈ 𝓝 y₀, ∀ x ∈ U, ∀ y ∈ V,
    infEDist x (invMap S y) ≤ μ * infEDist y (S x)

/-- Def. 3.1(c) of [Mordukhovich 2018] (Lipschitz-like, Aubin or pseudo-Lipschitz, property
with modulus `ℓ ≥ 0` around `(x₀, y₀)`): there are neighborhoods `U` of `x₀` and `V` of `y₀`
such that `S x ∩ V ⊆ S u + ℓ ‖x - u‖ 𝔹` for all `x, u ∈ U` (3.3). -/
def LipschitzLikeWith (ℓ : ℝ≥0) (S : E → Set F) (x₀ : E) (y₀ : F) : Prop :=
  ∃ U ∈ 𝓝 x₀, ∃ V ∈ 𝓝 y₀, ∀ x ∈ U, ∀ u ∈ U, ∀ y ∈ S x ∩ V, ∃ w ∈ S u, dist y w ≤ ℓ * dist x u

/-- `S` has the covering property around `(x₀, y₀)` [Mordukhovich 2018, Def. 3.1(a)]. -/
def HasCoveringAt (S : E → Set F) (x₀ : E) (y₀ : F) : Prop := ∃ κ, HasCoveringWith κ S x₀ y₀

/-- `S` is metrically regular around `(x₀, y₀)` [Mordukhovich 2018, Def. 3.1(b)]. -/
def MetricallyRegularAt (S : E → Set F) (x₀ : E) (y₀ : F) : Prop :=
  ∃ μ, MetricallyRegularWith μ S x₀ y₀

/-- `S` is Lipschitz-like around `(x₀, y₀)` [Mordukhovich 2018, Def. 3.1(c)]. -/
def LipschitzLikeAt (S : E → Set F) (x₀ : E) (y₀ : F) : Prop :=
  ∃ ℓ, LipschitzLikeWith ℓ S x₀ y₀

/-- The exact covering bound `cov S (x₀, y₀)` [Mordukhovich 2018, Def. 3.1(a)]: the supremum
of all covering moduli, in `ℝ≥0∞`; it is `0` if `S` has no covering property. -/
noncomputable def covBound (S : E → Set F) (x₀ : E) (y₀ : F) : ℝ≥0∞ :=
  ⨆ (κ : ℝ≥0) (_ : HasCoveringWith κ S x₀ y₀), (κ : ℝ≥0∞)

/-- The exact regularity bound `reg S (x₀, y₀)` [Mordukhovich 2018, Def. 3.1(b)]: the infimum
of all metric regularity moduli, in `ℝ≥0∞`; it is `∞` if `S` is not metrically regular. -/
noncomputable def regBound (S : E → Set F) (x₀ : E) (y₀ : F) : ℝ≥0∞ :=
  ⨅ (μ : ℝ≥0) (_ : MetricallyRegularWith μ S x₀ y₀), (μ : ℝ≥0∞)

/-- The exact Lipschitzian bound `lip S (x₀, y₀)` [Mordukhovich 2018, Def. 3.1(c)]: the
infimum of all Lipschitz-like moduli, in `ℝ≥0∞`; it is `∞` if `S` is not Lipschitz-like. -/
noncomputable def lipBound (S : E → Set F) (x₀ : E) (y₀ : F) : ℝ≥0∞ :=
  ⨅ (ℓ : ℝ≥0) (_ : LipschitzLikeWith ℓ S x₀ y₀), (ℓ : ℝ≥0∞)

end Definitions

section Basic

variable {E F : Type*} [MetricSpace E] [MetricSpace F]
variable {S : E → Set F} {x₀ : E} {y₀ : F} {κ μ ℓ : ℝ≥0}

theorem HasCoveringWith.pos (h : HasCoveringWith κ S x₀ y₀) : 0 < κ := h.1

theorem MetricallyRegularWith.pos (h : MetricallyRegularWith μ S x₀ y₀) : 0 < μ := h.1

/-- Elementwise form of metric regularity [Mordukhovich 2018, Def. 3.1(b)]: for `x`, `y` near
`x₀`, `y₀`, every `w ∈ S x` and every `ε > 0` there is `u ∈ S⁻¹ y` with
`dist x u < μ dist y w + ε`. -/
theorem metricallyRegularWith_iff :
    MetricallyRegularWith μ S x₀ y₀ ↔ 0 < μ ∧ ∃ U ∈ 𝓝 x₀, ∃ V ∈ 𝓝 y₀, ∀ x ∈ U, ∀ y ∈ V,
      ∀ w ∈ S x, ∀ ε > 0, ∃ u, y ∈ S u ∧ dist x u < μ * dist y w + ε := by
  constructor
  · rintro ⟨hμ, U, hU, V, hV, H⟩
    exact ⟨hμ, U, hU, V, hV, fun x hx y hy ↦ (infEDist_le_mul_infEDist_iff hμ).1 (H x hx y hy)⟩
  · rintro ⟨hμ, U, hU, V, hV, H⟩
    exact ⟨hμ, U, hU, V, hV, fun x hx y hy ↦ (infEDist_le_mul_infEDist_iff hμ).2 (H x hx y hy)⟩

/-- Covering moduli can be decreased. -/
theorem HasCoveringWith.mono {κ' : ℝ≥0} (h : HasCoveringWith κ S x₀ y₀) (hκ' : 0 < κ')
    (hle : κ' ≤ κ) : HasCoveringWith κ' S x₀ y₀ := by
  obtain ⟨-, U, hU, V, hV, H⟩ := h
  refine ⟨hκ', U, hU, V, hV, fun x r hr hxr y hy y' hy' ↦ H x r hr hxr y hy y' (hy'.trans ?_)⟩
  gcongr

/-- Metric regularity moduli can be increased. -/
theorem MetricallyRegularWith.mono {μ' : ℝ≥0} (h : MetricallyRegularWith μ S x₀ y₀)
    (hle : μ ≤ μ') : MetricallyRegularWith μ' S x₀ y₀ := by
  obtain ⟨hμ, U, hU, V, hV, H⟩ := h
  exact ⟨hμ.trans_le hle, U, hU, V, hV, fun x hx y hy ↦ (H x hx y hy).trans (by gcongr)⟩

/-- Lipschitz-like moduli can be increased. -/
theorem LipschitzLikeWith.mono {ℓ' : ℝ≥0} (h : LipschitzLikeWith ℓ S x₀ y₀) (hle : ℓ ≤ ℓ') :
    LipschitzLikeWith ℓ' S x₀ y₀ := by
  obtain ⟨U, hU, V, hV, H⟩ := h
  refine ⟨U, hU, V, hV, fun x hx u hu y hy ↦ ?_⟩
  obtain ⟨w, hw, hyw⟩ := H x hx u hu y hy
  exact ⟨w, hw, hyw.trans (by gcongr)⟩

/-- A property of pairs of neighborhoods which is inherited by smaller neighborhoods, and holds
for some neighborhoods of `(x₀, y₀)`, holds for some neighborhoods of every nearby point. -/
theorem eventually_exists_nhds_of_antitone {P : Set E → Set F → Prop}
    (hP : ∀ U U' V V', U' ⊆ U → V' ⊆ V → P U V → P U' V')
    (h : ∃ U ∈ 𝓝 x₀, ∃ V ∈ 𝓝 y₀, P U V) :
    ∀ᶠ p in 𝓝 (x₀, y₀), ∃ U ∈ 𝓝 p.1, ∃ V ∈ 𝓝 p.2, P U V := by
  obtain ⟨U, hU, V, hV, hUV⟩ := h
  filter_upwards [prod_mem_nhds (interior_mem_nhds.2 hU) (interior_mem_nhds.2 hV)] with p hp
  exact ⟨interior U, isOpen_interior.mem_nhds hp.1, interior V, isOpen_interior.mem_nhds hp.2,
    hP _ _ _ _ interior_subset interior_subset hUV⟩

/-- Robustness of the covering property [Mordukhovich 2018, p. 104]: a covering modulus around
`(x₀, y₀)` is a covering modulus around every nearby point. -/
theorem HasCoveringWith.eventually (h : HasCoveringWith κ S x₀ y₀) :
    ∀ᶠ p in 𝓝 (x₀, y₀), HasCoveringWith κ S p.1 p.2 := by
  obtain ⟨hκ, h⟩ := h
  refine (eventually_exists_nhds_of_antitone ?_ h).mono fun p hp ↦ ⟨hκ, hp⟩
  intro U U' V V' hU hV H x r hr hxr y hy
  exact H x r hr (hxr.trans hU) y ⟨hy.1, hV hy.2⟩

/-- Robustness of metric regularity [Mordukhovich 2018, p. 104]: a regularity modulus around
`(x₀, y₀)` is a regularity modulus around every nearby point. -/
theorem MetricallyRegularWith.eventually (h : MetricallyRegularWith μ S x₀ y₀) :
    ∀ᶠ p in 𝓝 (x₀, y₀), MetricallyRegularWith μ S p.1 p.2 := by
  obtain ⟨hμ, h⟩ := h
  refine (eventually_exists_nhds_of_antitone ?_ h).mono fun p hp ↦ ⟨hμ, hp⟩
  intro U U' V V' hU hV H x hx y hy
  exact H x (hU hx) y (hV hy)

/-- Robustness of the Lipschitz-like property [Mordukhovich 2018, p. 104]: a Lipschitz-like
modulus around `(x₀, y₀)` is a Lipschitz-like modulus around every nearby point. -/
theorem LipschitzLikeWith.eventually (h : LipschitzLikeWith ℓ S x₀ y₀) :
    ∀ᶠ p in 𝓝 (x₀, y₀), LipschitzLikeWith ℓ S p.1 p.2 := by
  refine eventually_exists_nhds_of_antitone ?_ h
  intro U U' V V' hU hV H x hx u hu y hy
  exact H x (hU hx) u (hU hu) y ⟨hy.1, hV hy.2⟩

/-! ### Moduli and exact bounds -/

theorem HasCoveringWith.hasCoveringAt (h : HasCoveringWith κ S x₀ y₀) : HasCoveringAt S x₀ y₀ :=
  ⟨κ, h⟩

theorem MetricallyRegularWith.metricallyRegularAt (h : MetricallyRegularWith μ S x₀ y₀) :
    MetricallyRegularAt S x₀ y₀ :=
  ⟨μ, h⟩

theorem LipschitzLikeWith.lipschitzLikeAt (h : LipschitzLikeWith ℓ S x₀ y₀) :
    LipschitzLikeAt S x₀ y₀ :=
  ⟨ℓ, h⟩

/-- A covering modulus is at most the exact covering bound. -/
theorem HasCoveringWith.le_covBound (h : HasCoveringWith κ S x₀ y₀) :
    (κ : ℝ≥0∞) ≤ covBound S x₀ y₀ :=
  le_iSup₂ (f := fun (κ : ℝ≥0) (_ : HasCoveringWith κ S x₀ y₀) ↦ (κ : ℝ≥0∞)) κ h

/-- The exact regularity bound is at most every regularity modulus. -/
theorem MetricallyRegularWith.regBound_le (h : MetricallyRegularWith μ S x₀ y₀) :
    regBound S x₀ y₀ ≤ μ :=
  iInf₂_le (f := fun (μ : ℝ≥0) (_ : MetricallyRegularWith μ S x₀ y₀) ↦ (μ : ℝ≥0∞)) μ h

/-- The exact Lipschitzian bound is at most every Lipschitz-like modulus. -/
theorem LipschitzLikeWith.lipBound_le (h : LipschitzLikeWith ℓ S x₀ y₀) :
    lipBound S x₀ y₀ ≤ ℓ :=
  iInf₂_le (f := fun (ℓ : ℝ≥0) (_ : LipschitzLikeWith ℓ S x₀ y₀) ↦ (ℓ : ℝ≥0∞)) ℓ h

theorem covBound_le {c : ℝ≥0∞} (h : ∀ κ, HasCoveringWith κ S x₀ y₀ → (κ : ℝ≥0∞) ≤ c) :
    covBound S x₀ y₀ ≤ c :=
  iSup₂_le h

theorem le_regBound {c : ℝ≥0∞} (h : ∀ μ, MetricallyRegularWith μ S x₀ y₀ → c ≤ μ) :
    c ≤ regBound S x₀ y₀ :=
  le_iInf₂ h

theorem le_lipBound {c : ℝ≥0∞} (h : ∀ ℓ, LipschitzLikeWith ℓ S x₀ y₀ → c ≤ ℓ) :
    c ≤ lipBound S x₀ y₀ :=
  le_iInf₂ h

/-- Below the exact covering bound there is a covering modulus. -/
theorem exists_hasCoveringWith_of_lt_covBound {c : ℝ≥0∞} (hc : c < covBound S x₀ y₀) :
    ∃ κ, HasCoveringWith κ S x₀ y₀ ∧ c < κ := by
  simpa [covBound, lt_iSup_iff] using hc

/-- Above the exact regularity bound there is a regularity modulus. -/
theorem exists_metricallyRegularWith_of_regBound_lt {c : ℝ≥0∞} (hc : regBound S x₀ y₀ < c) :
    ∃ μ, MetricallyRegularWith μ S x₀ y₀ ∧ (μ : ℝ≥0∞) < c := by
  simpa [regBound, iInf_lt_iff] using hc

/-- Above the exact Lipschitzian bound there is a Lipschitz-like modulus. -/
theorem exists_lipschitzLikeWith_of_lipBound_lt {c : ℝ≥0∞} (hc : lipBound S x₀ y₀ < c) :
    ∃ ℓ, LipschitzLikeWith ℓ S x₀ y₀ ∧ (ℓ : ℝ≥0∞) < c := by
  simpa [lipBound, iInf_lt_iff] using hc

/-- If every `μ' > μ` is a regularity modulus, then `reg S (x₀, y₀) ≤ μ`. -/
theorem regBound_le_of_forall_lt {c : ℝ≥0∞}
    (h : ∀ μ : ℝ≥0, c < μ → MetricallyRegularWith μ S x₀ y₀) : regBound S x₀ y₀ ≤ c := by
  refine le_of_forall_gt fun d hd ↦ ?_
  obtain ⟨μ, hcμ, hμd⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hd
  exact (h μ hcμ).regBound_le.trans_lt hμd

/-- If every `ℓ' > ℓ` is a Lipschitz-like modulus, then `lip S (x₀, y₀) ≤ ℓ`. -/
theorem lipBound_le_of_forall_lt {c : ℝ≥0∞}
    (h : ∀ ℓ : ℝ≥0, c < ℓ → LipschitzLikeWith ℓ S x₀ y₀) : lipBound S x₀ y₀ ≤ c := by
  refine le_of_forall_gt fun d hd ↦ ?_
  obtain ⟨ℓ, hcℓ, hℓd⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hd
  exact (h ℓ hcℓ).lipBound_le.trans_lt hℓd

/-- If every `κ' ∈ (0, κ)` is a covering modulus, then `κ ≤ cov S (x₀, y₀)`. -/
theorem le_covBound_of_forall_lt {c : ℝ≥0∞}
    (h : ∀ κ : ℝ≥0, 0 < κ → (κ : ℝ≥0∞) < c → HasCoveringWith κ S x₀ y₀) :
    c ≤ covBound S x₀ y₀ := by
  refine le_of_forall_lt fun d hd ↦ ?_
  obtain ⟨κ, hdκ, hκc⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hd
  exact hdκ.trans_le (h κ (by exact_mod_cast (zero_le (a := d)).trans_lt hdκ) hκc).le_covBound

theorem hasCoveringAt_iff_covBound_pos : HasCoveringAt S x₀ y₀ ↔ 0 < covBound S x₀ y₀ := by
  refine ⟨fun ⟨κ, h⟩ ↦ (by exact_mod_cast h.pos : (0 : ℝ≥0∞) < κ).trans_le h.le_covBound,
    fun h ↦ ?_⟩
  obtain ⟨κ, hκ, -⟩ := exists_hasCoveringWith_of_lt_covBound h
  exact ⟨κ, hκ⟩

theorem metricallyRegularAt_iff_regBound_lt_top :
    MetricallyRegularAt S x₀ y₀ ↔ regBound S x₀ y₀ < ∞ := by
  refine ⟨fun ⟨μ, h⟩ ↦ h.regBound_le.trans_lt ENNReal.coe_lt_top, fun h ↦ ?_⟩
  obtain ⟨μ, hμ, -⟩ := exists_metricallyRegularWith_of_regBound_lt h
  exact ⟨μ, hμ⟩

theorem lipschitzLikeAt_iff_lipBound_lt_top :
    LipschitzLikeAt S x₀ y₀ ↔ lipBound S x₀ y₀ < ∞ := by
  refine ⟨fun ⟨ℓ, h⟩ ↦ h.lipBound_le.trans_lt ENNReal.coe_lt_top, fun h ↦ ?_⟩
  obtain ⟨ℓ, hℓ, -⟩ := exists_lipschitzLikeWith_of_lipBound_lt h
  exact ⟨ℓ, hℓ⟩

end Basic

section Equivalence

variable {E F : Type*} [MetricSpace E] [MetricSpace F]
variable {S : E → Set F} {x₀ : E} {y₀ : F} {κ μ ℓ : ℝ≥0}

/-- Step 1 of the proof of Thm. 3.2 of [Mordukhovich 2018], elementwise form: to prove metric
regularity with modulus `μ` around `(x₀, y₀) ∈ gph S`, it suffices to find, for `x`, `y` near
`x₀`, `y₀`, every `w ∈ S x` with `dist y w < γ` (for some fixed `γ > 0`) and every `ε > 0`, a
point `u ∈ S⁻¹ y` with `dist x u < μ dist y w + ε`. -/
theorem metricallyRegularWith_of_forall_dist_lt (hμ : 0 < μ) (h₀ : y₀ ∈ S x₀) {γ : ℝ}
    (hγ : 0 < γ) {U : Set E} {V : Set F} (hU : U ∈ 𝓝 x₀) (hV : V ∈ 𝓝 y₀)
    (h : ∀ x ∈ U, ∀ y ∈ V, ∀ w ∈ S x, dist y w < γ →
      ∀ ε > 0, ∃ u, y ∈ S u ∧ dist x u < μ * dist y w + ε) :
    MetricallyRegularWith μ S x₀ y₀ := by
  obtain ⟨η, hη, hηU⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨η', hη', hηV⟩ := Metric.mem_nhds_iff.1 hV
  have hμ' : (0 : ℝ) < μ := hμ
  set ν := min (min η η') (γ * μ / (μ + 1)) with hν_def
  have hν : 0 < ν := lt_min (lt_min hη hη') (by positivity)
  have hνη : ν ≤ η := (min_le_left _ _).trans (min_le_left _ _)
  have hνη' : ν ≤ η' := (min_le_left _ _).trans (min_le_right _ _)
  have hνγ : ν * (μ + 1) ≤ γ * μ := by
    have := min_le_right (min η η') (γ * μ / (μ + 1))
    rw [← hν_def, le_div_iff₀ (by positivity)] at this
    exact this
  refine ⟨hμ, ball x₀ ν, ball_mem_nhds _ hν, ball y₀ ν, ball_mem_nhds _ hν,
    fun x hx y hy ↦ (infEDist_le_mul_infEDist_iff hμ).2 fun w hw ε hε ↦ ?_⟩
  have hx' : dist x x₀ < ν := hx
  have hy' : dist y y₀ < ν := hy
  have hxU : x ∈ U := hηU (lt_of_lt_of_le hx' hνη)
  have hyV : y ∈ V := hηV (lt_of_lt_of_le hy' hνη')
  by_cases hwy : dist y w < γ
  · exact h x hxU y hyV w hw hwy ε hε
  · replace hwy := not_lt.1 hwy
    have hyγ : dist y y₀ < γ := by nlinarith
    obtain ⟨u, hu, hxu⟩ := h x₀ (mem_of_mem_nhds hU) y hyV y₀ h₀ hyγ ε hε
    refine ⟨u, hu, ?_⟩
    have h1 : (μ : ℝ) * dist y y₀ ≤ μ * ν := by gcongr
    have h2 : (μ : ℝ) * γ ≤ μ * dist y w := by gcongr
    calc dist x u ≤ dist x x₀ + dist x₀ u := dist_triangle _ _ _
      _ < ν + (μ * ν + ε) := add_lt_add hx' (hxu.trans_le (by linarith))
      _ ≤ μ * dist y w + ε := by nlinarith

/-- Step 1 of the proof of Thm. 3.2 of [Mordukhovich 2018]: metric regularity around
`(x₀, y₀) ∈ gph S` can be verified only for pairs `(x, y)` near `(x₀, y₀)` with
`dist(y; S x) ≤ γ`, for some `γ > 0`. -/
theorem metricallyRegularWith_of_infEDist_le (hμ : 0 < μ) (h₀ : y₀ ∈ S x₀) {γ : ℝ}
    (hγ : 0 < γ) {U : Set E} {V : Set F} (hU : U ∈ 𝓝 x₀) (hV : V ∈ 𝓝 y₀)
    (h : ∀ x ∈ U, ∀ y ∈ V, infEDist y (S x) ≤ ENNReal.ofReal γ →
      infEDist x (invMap S y) ≤ μ * infEDist y (S x)) :
    MetricallyRegularWith μ S x₀ y₀ := by
  refine metricallyRegularWith_of_forall_dist_lt hμ h₀ hγ hU hV
    fun x hx y hy w hw hwy ↦ (infEDist_le_mul_infEDist_iff hμ).1 (h x hx y hy ?_) w hw
  exact (infEDist_le_edist_of_mem hw).trans ((edist_dist y w).trans_le
    (ENNReal.ofReal_le_ofReal hwy.le))

/-- Step 3 of the proof of Thm. 3.2 of [Mordukhovich 2018]: covering with modulus `κ` around
`(x₀, y₀) ∈ gph S` implies metric regularity with modulus `κ⁻¹`. -/
theorem HasCoveringWith.metricallyRegularWith (h : HasCoveringWith κ S x₀ y₀)
    (h₀ : y₀ ∈ S x₀) : MetricallyRegularWith κ⁻¹ S x₀ y₀ := by
  obtain ⟨hκ, U, hU, V, hV, H⟩ := h
  obtain ⟨η₁, hη₁, hηU⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨η₂, hη₂, hηV⟩ := Metric.mem_nhds_iff.1 hV
  set η := min η₁ η₂
  have hη : 0 < η := lt_min hη₁ hη₂
  have hκ' : (0 : ℝ) < κ := hκ
  refine metricallyRegularWith_of_forall_dist_lt (inv_pos.2 hκ) h₀
    (γ := min (η / 2) (κ * η / 2)) (lt_min (by positivity) (by positivity))
    (ball_mem_nhds x₀ (half_pos hη)) (ball_mem_nhds y₀ (half_pos hη))
    fun x hx y hy w hw hwy ε hε ↦ ?_
  have hx' : dist x x₀ < η / 2 := hx
  have hy' : dist y y₀ < η / 2 := hy
  set d := dist y w
  have hd0 : 0 ≤ d := dist_nonneg
  have hd1 : d < η / 2 := hwy.trans_le (min_le_left _ _)
  have hd2 : d < κ * η / 2 := hwy.trans_le (min_le_right _ _)
  have hdκ : d / κ < η / 2 := by rw [div_lt_iff₀ hκ']; linarith
  set s := min (ε / 2) ((η / 2 - d / κ) / 2)
  have hs : 0 < s := lt_min (by positivity) (by linarith)
  have hs1 : s ≤ ε / 2 := min_le_left _ _
  have hs2 : s ≤ (η / 2 - d / κ) / 2 := min_le_right _ _
  set r := d / κ + s
  have hr : 0 < r := by positivity
  have hwV : w ∈ V := by
    refine hηV (lt_of_le_of_lt (dist_triangle w y y₀) ?_ |>.trans_le (min_le_right η₁ η₂))
    rw [dist_comm]; linarith
  have hball : closedBall x r ⊆ U := by
    intro z hz
    refine hηU (lt_of_le_of_lt (dist_triangle z x x₀) ?_ |>.trans_le (min_le_left η₁ η₂))
    have : dist z x ≤ r := hz
    linarith
  have hyw : dist y w ≤ κ * r := by
    have : (κ : ℝ) * r = d + κ * s := by
      simp only [r, mul_add]; field_simp
    rw [this]; nlinarith
  obtain ⟨x', hx'x, hyx'⟩ := H x r hr hball w ⟨hw, hwV⟩ y hyw
  refine ⟨x', hyx', ?_⟩
  rw [dist_comm]
  calc dist x' x ≤ r := hx'x
    _ ≤ d / κ + ε / 2 := by linarith
    _ < ((κ⁻¹ : ℝ≥0) : ℝ) * d + ε := by
        rw [NNReal.coe_inv, div_eq_inv_mul]; linarith

/-- Step 3 of the proof of Thm. 3.2 of [Mordukhovich 2018] (qualitative form): covering around
`(x₀, y₀) ∈ gph S` implies metric regularity. Unlike the converse, this holds in all metric
spaces. -/
theorem HasCoveringAt.metricallyRegularAt (h : HasCoveringAt S x₀ y₀) (h₀ : y₀ ∈ S x₀) :
    MetricallyRegularAt S x₀ y₀ :=
  let ⟨_, hκ⟩ := h
  (hκ.metricallyRegularWith h₀).metricallyRegularAt

/-- Step 3 of the proof of Thm. 3.2 of [Mordukhovich 2018] (bounds): if `κ` is a covering
modulus, then `reg S (x₀, y₀) ≤ κ⁻¹`. -/
theorem HasCoveringWith.regBound_le (h : HasCoveringWith κ S x₀ y₀) (h₀ : y₀ ∈ S x₀) :
    regBound S x₀ y₀ ≤ (κ : ℝ≥0∞)⁻¹ := by
  rw [← ENNReal.coe_inv h.pos.ne']
  exact (h.metricallyRegularWith h₀).regBound_le

/-- Step 4 of the proof of Thm. 3.2 of [Mordukhovich 2018]: if `S` is Lipschitz-like around
`(x₀, y₀) ∈ gph S` with modulus `ℓ`, then `S⁻¹` is metrically regular around `(y₀, x₀)` with
every modulus `μ ≥ ℓ`, `μ > 0`. -/
theorem LipschitzLikeWith.metricallyRegularWith_invMap (h : LipschitzLikeWith ℓ S x₀ y₀)
    (h₀ : y₀ ∈ S x₀) (hμ : 0 < μ) (hℓμ : ℓ ≤ μ) : MetricallyRegularWith μ (invMap S) y₀ x₀ := by
  obtain ⟨U, hU, V, hV, H⟩ := h
  obtain ⟨η, hη, hηU⟩ := Metric.mem_nhds_iff.1 hU
  refine metricallyRegularWith_of_forall_dist_lt hμ h₀ (half_pos hη) hV
    (ball_mem_nhds x₀ (half_pos hη)) fun y hy x hx u hu hxu ε hε ↦ ?_
  have hx' : dist x x₀ < η / 2 := hx
  have hxU : x ∈ U := hηU (hx'.trans (half_lt_self hη))
  have huU : u ∈ U := by
    refine hηU (lt_of_le_of_lt (dist_triangle u x x₀) ?_)
    rw [dist_comm]; linarith
  obtain ⟨w, hw, hyw⟩ := H u huU x hxU y ⟨hu, hy⟩
  refine ⟨w, hw, ?_⟩
  have : (ℓ : ℝ) * dist u x ≤ μ * dist x u := by
    rw [dist_comm]; gcongr
  linarith

/-- Step 5 of the proof of Thm. 3.2 of [Mordukhovich 2018]: if `S⁻¹` is metrically regular
around `(y₀, x₀)` with modulus `μ`, then `S` is Lipschitz-like around `(x₀, y₀)` with every
modulus `ℓ > μ`. -/
theorem MetricallyRegularWith.lipschitzLikeWith_of_invMap
    (h : MetricallyRegularWith μ (invMap S) y₀ x₀) (hμℓ : μ < ℓ) :
    LipschitzLikeWith ℓ S x₀ y₀ := by
  obtain ⟨hμ, V, hV, U, hU, H⟩ := h
  refine ⟨U, hU, V, hV, fun x hx u hu y hy ↦ ?_⟩
  rcases eq_or_ne x u with rfl | hxu
  · exact ⟨y, hy.1, by simp⟩
  have hd : 0 < dist u x := dist_pos.2 hxu.symm
  have hμℓ' : (μ : ℝ) < ℓ := hμℓ
  obtain ⟨w, hw, hyw⟩ := (infEDist_le_mul_infEDist_iff hμ).1 (H y hy.2 u hu) x hy.1
    ((ℓ - μ) * dist u x) (by nlinarith)
  refine ⟨w, hw, ?_⟩
  rw [dist_comm x u]
  linarith

/-- Thm. 3.2(ii) of [Mordukhovich 2018] (exact bounds): `lip S (x₀, y₀) = reg S⁻¹ (y₀, x₀)`
cf. [Clason–Valkonen, (27.1), Thm. 27.3]. -/
theorem lipBound_eq_regBound_invMap (h₀ : y₀ ∈ S x₀) :
    lipBound S x₀ y₀ = regBound (invMap S) y₀ x₀ := by
  refine le_antisymm (le_regBound fun μ hμ ↦ lipBound_le_of_forall_lt fun ℓ hℓ ↦
    hμ.lipschitzLikeWith_of_invMap (by exact_mod_cast hℓ))
    (le_lipBound fun ℓ hℓ ↦ regBound_le_of_forall_lt fun μ hμ ↦ ?_)
  have hℓμ : ℓ < μ := by exact_mod_cast hμ
  exact hℓ.metricallyRegularWith_invMap h₀ ((zero_le (a := ℓ)).trans_lt hℓμ) hℓμ.le

/-- Thm. 3.2(ii) of [Mordukhovich 2018]: `S` is Lipschitz-like around `(x₀, y₀) ∈ gph S` iff
`S⁻¹` is metrically regular around `(y₀, x₀)` [Clason–Valkonen, Thm. 27.3]. -/
theorem lipschitzLikeAt_iff_metricallyRegularAt_invMap (h₀ : y₀ ∈ S x₀) :
    LipschitzLikeAt S x₀ y₀ ↔ MetricallyRegularAt (invMap S) y₀ x₀ := by
  rw [lipschitzLikeAt_iff_lipBound_lt_top, metricallyRegularAt_iff_regBound_lt_top,
    lipBound_eq_regBound_invMap h₀]

/-- Thm. 3.2(ii) of [Mordukhovich 2018], read for `S⁻¹`: `S` is metrically regular around
`(x₀, y₀) ∈ gph S` iff `S⁻¹` is Lipschitz-like around `(y₀, x₀)`, with
`reg S (x₀, y₀) = lip S⁻¹ (y₀, x₀)`. -/
theorem regBound_eq_lipBound_invMap (h₀ : y₀ ∈ S x₀) :
    regBound S x₀ y₀ = lipBound (invMap S) y₀ x₀ :=
  (lipBound_eq_regBound_invMap (S := invMap S) h₀).symm

theorem metricallyRegularAt_iff_lipschitzLikeAt_invMap (h₀ : y₀ ∈ S x₀) :
    MetricallyRegularAt S x₀ y₀ ↔ LipschitzLikeAt (invMap S) y₀ x₀ :=
  (lipschitzLikeAt_iff_metricallyRegularAt_invMap (S := invMap S) h₀).symm

end Equivalence

section Normed

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E] [MetricSpace F]
variable {S : E → Set F} {x₀ : E} {y₀ : F} {κ μ : ℝ≥0}

/-- In a nontrivial real normed space, `closedBall x r ⊆ ball x₀ ν` with `r ≥ 0` forces
`r < ν`. -/
theorem lt_of_closedBall_subset_ball {x x₀ : E} {r ν : ℝ} (hr : 0 ≤ r)
    (h : closedBall x r ⊆ ball x₀ ν) : r < ν := by
  obtain ⟨z, hz⟩ := exists_norm_eq E hr
  have h1 : dist (x + z) x₀ < ν := h (by simp [hz])
  have h2 : dist (x - z) x₀ < ν := h (by simp [hz])
  have h3 : dist (x + z) (x - z) = 2 * r := by
    rw [dist_eq_norm, show x + z - (x - z) = (2 : ℝ) • z by rw [two_smul]; abel, norm_smul,
      hz, Real.norm_two]
  have := dist_triangle_right (x + z) (x - z) x₀
  linarith

/-- Step 2 of the proof of Thm. 3.2 of [Mordukhovich 2018]: metric regularity with modulus
`μ` implies covering with every modulus `κ > 0` with `κ μ < 1`. The domain space must be a
nontrivial normed space (see the module docstring). -/
theorem MetricallyRegularWith.hasCoveringWith (h : MetricallyRegularWith μ S x₀ y₀)
    (hκ : 0 < κ) (hκμ : κ * μ < 1) : HasCoveringWith κ S x₀ y₀ := by
  obtain ⟨hμ, U, hU, V, hV, H⟩ := h
  obtain ⟨η₁, hη₁, hηU⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨η₂, hη₂, hηV⟩ := Metric.mem_nhds_iff.1 hV
  set η := min η₁ η₂
  have hη : 0 < η := lt_min hη₁ hη₂
  have hκ' : (0 : ℝ) < κ := hκ
  have hκμ' : (κ : ℝ) * μ < 1 := by exact_mod_cast hκμ
  set ν := η / (2 * (κ + 1))
  have hν : 0 < ν := by positivity
  have hκν : κ * ν < η / 2 := by
    rw [show (κ : ℝ) * ν = η / 2 * (κ / (κ + 1)) by simp only [ν]; field_simp]
    exact mul_lt_of_lt_one_right (half_pos hη) ((div_lt_one (by positivity)).2 (by linarith))
  have hνη : ν ≤ η := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  refine ⟨hκ, ball x₀ ν, ball_mem_nhds _ hν, ball y₀ (η / 2), ball_mem_nhds _ (half_pos hη),
    fun x r hr hxr y hy y' hy' ↦ ?_⟩
  have hrν : r < ν := lt_of_closedBall_subset_ball hr.le hxr
  have hx : dist x x₀ < ν := hxr (mem_closedBall_self hr.le)
  have hxU : x ∈ U := hηU (hx.trans_le (hνη.trans (min_le_left _ _)))
  have hyy₀ : dist y y₀ < η / 2 := hy.2
  have hy'V : y' ∈ V := by
    refine hηV (lt_of_le_of_lt (dist_triangle y' y y₀) ?_ |>.trans_le (min_le_right η₁ η₂))
    have : (κ : ℝ) * r ≤ κ * ν := by gcongr
    linarith
  obtain ⟨u, hu, hxu⟩ := (infEDist_le_mul_infEDist_iff hμ).1 (H x hxU y' hy'V) y hy.1
    ((1 - κ * μ) * r) (by nlinarith)
  refine ⟨u, ?_, hu⟩
  rw [dist_comm]
  have : (μ : ℝ) * dist y' y ≤ μ * (κ * r) := by gcongr
  nlinarith

/-- Step 2 of the proof of Thm. 3.2 of [Mordukhovich 2018] (bounds): if `μ` is a regularity
modulus, then `μ⁻¹ ≤ cov S (x₀, y₀)`. -/
theorem MetricallyRegularWith.inv_le_covBound (h : MetricallyRegularWith μ S x₀ y₀) :
    (μ : ℝ≥0∞)⁻¹ ≤ covBound S x₀ y₀ := by
  refine le_covBound_of_forall_lt fun κ hκ hκμ ↦ h.hasCoveringWith hκ ?_
  rw [← ENNReal.coe_inv h.pos.ne', ENNReal.coe_lt_coe] at hκμ
  exact (NNReal.lt_inv_iff_mul_lt h.pos.ne').1 hκμ

/-- Thm. 3.2(i) of [Mordukhovich 2018] (exact bounds): `cov S (x₀, y₀) = reg S (x₀, y₀)⁻¹`
for `(x₀, y₀) ∈ gph S`, in `ℝ≥0∞`. -/
theorem covBound_eq_inv_regBound (h₀ : y₀ ∈ S x₀) :
    covBound S x₀ y₀ = (regBound S x₀ y₀)⁻¹ := by
  refine le_antisymm (covBound_le fun κ hκ ↦ ?_) ?_
  · exact ENNReal.le_inv_iff_le_inv.1 (hκ.regBound_le h₀)
  · rw [regBound, ENNReal.inv_iInf]
    refine iSup_le fun μ ↦ ?_
    rw [ENNReal.inv_iInf]
    exact iSup_le fun hμ ↦ hμ.inv_le_covBound

/-- Thm. 3.2(i) of [Mordukhovich 2018]: `S` has the covering property around
`(x₀, y₀) ∈ gph S` iff it is metrically regular around this point. -/
theorem hasCoveringAt_iff_metricallyRegularAt (h₀ : y₀ ∈ S x₀) :
    HasCoveringAt S x₀ y₀ ↔ MetricallyRegularAt S x₀ y₀ := by
  rw [hasCoveringAt_iff_covBound_pos, metricallyRegularAt_iff_regBound_lt_top,
    covBound_eq_inv_regBound h₀, ENNReal.inv_pos, lt_top_iff_ne_top]

end Normed

end VariationalAnalysis
