/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Order.LocalExtr
import VariationalAnalysis.Basic

/-!
# Regular (Fréchet) normals and their `ω`-enlargements

For a set `Ω` in a real normed space `E` and `x₀ ∈ Ω`, the *regular normal cone* (prenormal
cone, Fréchet normal cone) [Mordukhovich 2018, (1.5)], [Clason–Valkonen, (18.2)] is

  `N̂(x₀; Ω) = {v ∈ E* | lim sup_{x →Ω x₀} ⟨v, x - x₀⟩ / ‖x - x₀‖ ≤ 0}`,

and its `ω`-enlargement [Mordukhovich 2018, (1.6)], [Clason–Valkonen, (18.7)] replaces `0` by
`ω`. The `lim sup` condition is unfolded as: for every `ε > 0`, `v (x - x₀) ≤ (ω + ε) ‖x - x₀‖`
for all `x ∈ Ω` near `x₀`.

Normals are elements of the dual `StrongDual ℝ E = E →L[ℝ] ℝ`. In a Hilbert space they are
identified with vectors through `InnerProductSpace.toDual`. Following [Rockafellar–Wets 1998],
the cones are empty when `x₀ ∉ Ω`.

## Main declarations

* `epsNormalCone ω Ω x₀`: the `ω`-normals `N̂_ω(x₀; Ω)`.
* `regularNormalCone Ω x₀`: the regular normals `N̂(x₀; Ω)`.

## Main results

* `convex_regularNormalCone`, `isClosed_regularNormalCone`: `N̂(x₀; Ω)` is a closed convex cone.
* `regularNormalCone_of_mem_interior`: `N̂(x₀; Ω) = {0}` at interior points.
* `mem_epsNormalCone_of_convex`, `mem_regularNormalCone_of_convex`: Prop. 1.7, (1.8), of
  [Mordukhovich 2018]: normals to convex sets.
* `mem_regularNormalCone_iff_exists_localMax`: Thm. 1.10(i) of [Mordukhovich 2018]: smooth
  variational description of regular normals.
-/

open Filter Topology Set

namespace VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : Set E} {x₀ : E} {v w : StrongDual ℝ E} {ω : ℝ}

/-- The `ω`-normals to `Ω` at `x₀` [Mordukhovich 2018, (1.6)]: `v` with
`lim sup_{x →Ω x₀} v (x - x₀) / ‖x - x₀‖ ≤ ω`. Empty if `x₀ ∉ Ω`. -/
def epsNormalCone (ω : ℝ) (Ω : Set E) (x₀ : E) : Set (StrongDual ℝ E) :=
  {v | x₀ ∈ Ω ∧ ∀ ε > 0, ∀ᶠ x in 𝓝[Ω] x₀, v (x - x₀) ≤ (ω + ε) * ‖x - x₀‖}

/-- The regular (Fréchet) normal cone, or prenormal cone, to `Ω` at `x₀`
[Mordukhovich 2018, (1.5)]: `v` with `lim sup_{x →Ω x₀} v (x - x₀) / ‖x - x₀‖ ≤ 0`.
Empty if `x₀ ∉ Ω`. -/
def regularNormalCone (Ω : Set E) (x₀ : E) : Set (StrongDual ℝ E) :=
  {v | x₀ ∈ Ω ∧ ∀ ε > 0, ∀ᶠ x in 𝓝[Ω] x₀, v (x - x₀) ≤ ε * ‖x - x₀‖}

theorem epsNormalCone_zero : epsNormalCone 0 Ω x₀ = regularNormalCone Ω x₀ := by
  ext v; simp [epsNormalCone, regularNormalCone]

theorem mem_of_mem_regularNormalCone (hv : v ∈ regularNormalCone Ω x₀) : x₀ ∈ Ω := hv.1

theorem mem_of_mem_epsNormalCone (hv : v ∈ epsNormalCone ω Ω x₀) : x₀ ∈ Ω := hv.1

theorem regularNormalCone_subset_epsNormalCone (hω : 0 ≤ ω) :
    regularNormalCone Ω x₀ ⊆ epsNormalCone ω Ω x₀ := by
  refine fun v ⟨hx, hv⟩ ↦ ⟨hx, fun ε hε ↦ (hv ε hε).mono fun x hx ↦ hx.trans ?_⟩
  gcongr; linarith

theorem epsNormalCone_mono {ω₁ ω₂ : ℝ} (h : ω₁ ≤ ω₂) :
    epsNormalCone ω₁ Ω x₀ ⊆ epsNormalCone ω₂ Ω x₀ := by
  refine fun v ⟨hx, hv⟩ ↦ ⟨hx, fun ε hε ↦ (hv ε hε).mono fun x hx ↦ hx.trans ?_⟩
  gcongr

theorem zero_mem_regularNormalCone (hx : x₀ ∈ Ω) : (0 : StrongDual ℝ E) ∈ regularNormalCone Ω x₀ :=
  ⟨hx, fun ε hε ↦ Eventually.of_forall fun x ↦ by
    simpa using mul_nonneg hε.le (norm_nonneg (x - x₀))⟩

theorem smul_mem_regularNormalCone (hv : v ∈ regularNormalCone Ω x₀) {t : ℝ} (ht : 0 ≤ t) :
    t • v ∈ regularNormalCone Ω x₀ := by
  refine ⟨hv.1, fun ε hε ↦ ?_⟩
  filter_upwards [hv.2 (ε / (t + 1)) (div_pos hε (by linarith))] with x hx
  simp only [smul_apply, smul_eq_mul]
  calc t * v (x - x₀) ≤ t * (ε / (t + 1) * ‖x - x₀‖) := mul_le_mul_of_nonneg_left hx ht
    _ = t / (t + 1) * (ε * ‖x - x₀‖) := by ring
    _ ≤ 1 * (ε * ‖x - x₀‖) := by
        gcongr
        rw [div_le_one (by linarith)]; linarith
    _ = ε * ‖x - x₀‖ := one_mul _

theorem add_mem_regularNormalCone (hv : v ∈ regularNormalCone Ω x₀)
    (hw : w ∈ regularNormalCone Ω x₀) : v + w ∈ regularNormalCone Ω x₀ := by
  refine ⟨hv.1, fun ε hε ↦ ?_⟩
  filter_upwards [hv.2 (ε / 2) (half_pos hε), hw.2 (ε / 2) (half_pos hε)] with x hx₁ hx₂
  simp only [add_apply]
  linarith

/-- `N̂(x₀; Ω)` is convex [Mordukhovich 2018, p. 4]. -/
theorem convex_regularNormalCone : Convex ℝ (regularNormalCone Ω x₀) := by
  intro v hv w hw a b ha hb _
  exact add_mem_regularNormalCone (smul_mem_regularNormalCone hv ha)
    (smul_mem_regularNormalCone hw hb)

/-- `N̂_ω(x₀; Ω)` is closed. -/
theorem isClosed_epsNormalCone : IsClosed (epsNormalCone ω Ω x₀) := by
  refine isClosed_of_closure_subset fun v hv ↦ ?_
  have hx : x₀ ∈ Ω := by
    obtain ⟨w, hw, -⟩ := Metric.mem_closure_iff.1 hv 1 one_pos
    exact hw.1
  refine ⟨hx, fun ε hε ↦ ?_⟩
  obtain ⟨w, hw, hvw⟩ := Metric.mem_closure_iff.1 hv (ε / 2) (half_pos hε)
  filter_upwards [hw.2 (ε / 2) (half_pos hε)] with x hx
  have h1 : (v - w) (x - x₀) ≤ ‖v - w‖ * ‖x - x₀‖ :=
    (le_abs_self _).trans ((v - w).le_opNorm _)
  have h2 : ‖v - w‖ * ‖x - x₀‖ ≤ ε / 2 * ‖x - x₀‖ := by
    rw [← dist_eq_norm]; gcongr
  simp only [sub_apply] at h1
  linarith

/-- `N̂(x₀; Ω)` is closed. -/
theorem isClosed_regularNormalCone : IsClosed (regularNormalCone Ω x₀) :=
  epsNormalCone_zero (Ω := Ω) (x₀ := x₀) ▸ isClosed_epsNormalCone

/-- At an interior point the regular normal cone is trivial. -/
theorem regularNormalCone_of_mem_interior (hx : x₀ ∈ interior Ω) :
    regularNormalCone Ω x₀ = {0} := by
  refine subset_antisymm (fun v hv ↦ ?_) ?_
  · have hray : ∀ d : E, ∀ᶠ t in 𝓝[>] (0 : ℝ), x₀ + t • d ∈ Ω := by
      intro d
      have hc : Tendsto (fun t : ℝ ↦ x₀ + t • d) (𝓝 0) (𝓝 (x₀ + (0 : ℝ) • d)) :=
        ((continuous_id.smul continuous_const).const_add x₀).tendsto 0
      rw [zero_smul, add_zero] at hc
      exact nhdsWithin_le_nhds (hc (mem_interior_iff_mem_nhds.1 hx))
    have hle : ∀ d : E, v d ≤ 0 := fun d ↦
      le_of_forall_pos_le_add_mul fun ε hε ↦ by
        simpa using le_of_eventually_ray (hv.2 ε hε) (hray d)
    ext d
    simpa using le_antisymm (hle d) (by simpa using hle (-d))
  · rintro _ rfl
    exact zero_mem_regularNormalCone (interior_subset hx)

/-- Prop. 1.7, (1.8), of [Mordukhovich 2018]: `ω`-normals to a convex set. -/
theorem mem_epsNormalCone_of_convex (hΩ : Convex ℝ Ω) (hx : x₀ ∈ Ω) :
    v ∈ epsNormalCone ω Ω x₀ ↔ ∀ x ∈ Ω, v (x - x₀) ≤ ω * ‖x - x₀‖ := by
  refine ⟨fun hv x hxΩ ↦ ?_, fun h ↦ ⟨hx, fun ε hε ↦ ?_⟩⟩
  · have hray : ∀ᶠ t in 𝓝[>] (0 : ℝ), x₀ + t • (x - x₀) ∈ Ω := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with t ht
      exact hΩ.add_smul_sub_mem hx hxΩ ⟨ht.1.le, ht.2.le⟩
    refine le_of_forall_pos_le_add_mul (c := ‖x - x₀‖) fun ε hε ↦ ?_
    have := le_of_eventually_ray (hv.2 ε hε) hray
    linarith
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact (h y hy).trans (by nlinarith [norm_nonneg (y - x₀)])

/-- Prop. 1.7, (1.9), of [Mordukhovich 2018]: regular normals to a convex set are the normals of
convex analysis. -/
theorem mem_regularNormalCone_of_convex (hΩ : Convex ℝ Ω) (hx : x₀ ∈ Ω) :
    v ∈ regularNormalCone Ω x₀ ↔ ∀ x ∈ Ω, v (x - x₀) ≤ 0 := by
  rw [← epsNormalCone_zero, mem_epsNormalCone_of_convex hΩ hx]
  simp

/-- Thm. 1.10(i) of [Mordukhovich 2018] (smooth variational description of regular normals):
`v ∈ N̂(x₀; Ω)` iff `v` is the derivative at `x₀` of a function attaining a local maximum
relative to `Ω` at `x₀`. -/
theorem mem_regularNormalCone_iff_exists_localMax (hx : x₀ ∈ Ω) :
    v ∈ regularNormalCone Ω x₀ ↔ ∃ ψ : E → ℝ, HasFDerivAt ψ v x₀ ∧ IsLocalMaxOn ψ Ω x₀ := by
  constructor
  · intro hv
    classical
    refine ⟨fun x ↦ if x ∈ Ω then min 0 (v (x - x₀)) else v (x - x₀), ?_, ?_⟩
    · refine HasFDerivAt.of_isLittleO (Asymptotics.IsLittleO.of_bound fun c hc ↦ ?_)
      have := eventually_nhdsWithin_iff.1 (hv.2 c hc)
      filter_upwards [this] with x hxc
      simp only [hx, if_true, sub_self, map_zero, min_self, sub_zero]
      split_ifs with hxΩ
      · have h1 := hxc hxΩ
        rw [Real.norm_eq_abs, abs_le]
        constructor
        · have : min 0 (v (x - x₀)) - v (x - x₀) ≥ -(c * ‖x - x₀‖) := by
            rcases le_total 0 (v (x - x₀)) with h | h
            · rw [min_eq_left h]; linarith
            · rw [min_eq_right h]; nlinarith [norm_nonneg (x - x₀)]
          linarith
        · have : min 0 (v (x - x₀)) ≤ v (x - x₀) := min_le_right _ _
          nlinarith [norm_nonneg (x - x₀)]
      · simpa using mul_nonneg hc.le (norm_nonneg (x - x₀))
    · filter_upwards [self_mem_nhdsWithin] with x hxΩ
      simp [hxΩ, hx]
  · rintro ⟨ψ, hψ, hmax⟩
    refine ⟨hx, fun ε hε ↦ ?_⟩
    filter_upwards [hmax, nhdsWithin_le_nhds (hψ.isLittleO.def hε)] with x hx₁ hx₂
    rw [Real.norm_eq_abs, abs_le] at hx₂
    linarith [hx₂.1]

end VariationalAnalysis
