/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.MetricSpace.HausdorffDistance
import VariationalAnalysis.Normal.Limiting

/-!
# Normals via Euclidean projections

[Mordukhovich 2018, Def. 1.1] defines the basic normal cone to `Ω` at `x₀ ∈ Ω` through the
Euclidean projector `Π(x; Ω) = {w ∈ Ω | ‖x - w‖ = dist(x; Ω)}` (1.3):

  `N(x₀; Ω) = Lim sup_{x → x₀} cone(x - Π(x; Ω))`  (1.4).

This file works in a real inner product space `H`, with vectors identified with dual elements by
`InnerProductSpace.toDual`, and proves that (1.4) agrees with the limiting normal cone
`normalCone` for locally closed sets in finite dimensions, together with the representation by
`ω`-normals.

## Main declarations

* `euclideanProj Ω x`: the Euclidean projector `Π(x; Ω)` [Mordukhovich 2018, (1.3)].
* `projNormalCone Ω x₀`: the normal cone of [Mordukhovich 2018, Def. 1.1].

## Main results

* `toDual_sub_mem_regularNormalCone`: [Mordukhovich 2018, Thm. 1.6, Step 1]: `x - w` is a
  regular normal at any projection `w ∈ Π(x; Ω)`.
* `toDual_projNormalCone`: Thm. 1.6 of [Mordukhovich 2018]: `N(x₀; Ω)` from (1.4) is the
  limiting normal cone, for `Ω` locally closed around `x₀` in finite dimensions.
* `normalCone_eq_outerLimit_epsNormalCone_inner`: Thm. 1.6, second representation in (1.7):
  `N(x₀; Ω) = Lim sup_{x →Ω x₀, ω ↓ 0} N̂_ω(x; Ω)`.
* `exists_ne_zero_mem_normalCone_iff_inner`: Prop. 1.2 of [Mordukhovich 2018]: `x₀ ∈ Ω` is a
  boundary point iff `N(x₀; Ω) ≠ {0}`.

The last two results hold in every finite-dimensional normed space; see
`VariationalAnalysis.Normal.Transport`.
-/

open Filter Topology Set Metric InnerProductSpace

namespace VariationalAnalysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Ω : Set H} {x₀ x w u : H}

local notation "⟪" a ", " b "⟫" => @inner ℝ _ _ a b

/-- The Euclidean projector `Π(x; Ω)` [Mordukhovich 2018, (1.3)]. -/
def euclideanProj (Ω : Set H) (x : H) : Set H :=
  {w | w ∈ Ω ∧ ‖x - w‖ = infDist x Ω}

/-- The basic normal cone of [Mordukhovich 2018, Def. 1.1], as a set of vectors:
`Lim sup_{x → x₀} cone(x - Π(x; Ω))`. Empty if `x₀ ∉ Ω`. -/
def projNormalCone (Ω : Set H) (x₀ : H) : Set H :=
  {v | x₀ ∈ Ω ∧
    v ∈ outerLimit (𝓝 x₀) (fun x ↦ {u | ∃ α : ℝ, 0 ≤ α ∧ ∃ w ∈ euclideanProj Ω x, u = α • (x - w)})}

/-- The Riesz map `toDual ℝ H` commutes with multiplication by real scalars. -/
theorem toDual_smul (t : ℝ) (y : H) [CompleteSpace H] : toDual ℝ H (t • y) = t • toDual ℝ H y := by
  simp

omit [InnerProductSpace ℝ H] in
/-- A projection is not farther from `x` than any point of `Ω`. -/
theorem norm_sub_proj_le (hw : w ∈ euclideanProj Ω x) {z : H} (hz : z ∈ Ω) :
    ‖x - w‖ ≤ ‖x - z‖ := by
  rw [hw.2, ← dist_eq_norm]; exact infDist_le_dist_of_mem hz

omit [InnerProductSpace ℝ H] in
/-- Projections of points near `x₀ ∈ Ω` are near `x₀`: `‖w - x₀‖ ≤ 2 ‖x - x₀‖`. -/
theorem norm_proj_sub_le (hw : w ∈ euclideanProj Ω x) (hx₀ : x₀ ∈ Ω) :
    ‖w - x₀‖ ≤ 2 * ‖x - x₀‖ := by
  have := norm_sub_proj_le hw hx₀
  have h := norm_add_le (w - x) (x - x₀)
  rw [sub_add_sub_cancel, norm_sub_rev w x] at h
  linarith

/-- The projection inequality `⟪x - w, z - w⟫ ≤ ‖z - w‖² / 2` for `z ∈ Ω`. -/
theorem inner_sub_proj_le (hw : w ∈ euclideanProj Ω x) {z : H} (hz : z ∈ Ω) :
    ⟪x - w, z - w⟫ ≤ ‖z - w‖ ^ 2 / 2 := by
  have h := norm_sub_proj_le hw hz
  have h2 : ‖x - w‖ ^ 2 ≤ ‖x - z‖ ^ 2 := by gcongr
  have : x - z = (x - w) - (z - w) := by abel
  rw [this, norm_sub_sq_real (x - w) (z - w)] at h2
  linarith

/-- [Mordukhovich 2018, Thm. 1.6, Step 1]: if `w ∈ Π(x; Ω)`, then `x - w ∈ N̂(w; Ω)`. -/
theorem toDual_sub_mem_regularNormalCone [CompleteSpace H] (hw : w ∈ euclideanProj Ω x) :
    toDual ℝ H (x - w) ∈ regularNormalCone Ω w := by
  refine ⟨hw.1, fun ε hε ↦ ?_⟩
  filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds w (show 0 < 2 * ε by linarith)),
    self_mem_nhdsWithin] with z hzb hzΩ
  rw [toDual_apply_apply]
  have h := inner_sub_proj_le hw hzΩ
  rw [mem_ball, dist_eq_norm] at hzb
  nlinarith [norm_nonneg (z - w)]

/-- [Mordukhovich 2018, Thm. 1.6, Step 2]: if `x ∈ Ω` and `w ∈ Π(x + λ v; Ω)`, then
`‖w - x‖² ≤ 2 λ ⟪v, w - x⟫`. -/
theorem sq_norm_proj_sub_le (hx : x ∈ Ω) {v : H} {l : ℝ}
    (hw : w ∈ euclideanProj Ω (x + l • v)) : ‖w - x‖ ^ 2 ≤ 2 * l * ⟪v, w - x⟫ := by
  have h := norm_sub_proj_le hw hx
  rw [add_sub_cancel_left] at h
  have h2 : ‖x + l • v - w‖ ^ 2 ≤ ‖l • v‖ ^ 2 := by gcongr
  have : x + l • v - w = l • v - (w - x) := by abel
  rw [this, norm_sub_sq_real, inner_smul_left] at h2
  simp only [conj_trivial] at h2
  linarith

/-- If `x ∈ Ω`, `λ ≥ 0` and `w ∈ Π(x + λ v; Ω)`, then `‖w - x‖ ≤ 2 λ ‖v‖`. -/
theorem norm_proj_sub_le_of_smul (hx : x ∈ Ω) {v : H} {l : ℝ} (hl : 0 ≤ l)
    (hw : w ∈ euclideanProj Ω (x + l • v)) : ‖w - x‖ ≤ 2 * l * ‖v‖ := by
  have h := sq_norm_proj_sub_le hx hw
  have h2 : ⟪v, w - x⟫ ≤ ‖v‖ * ‖w - x‖ := real_inner_le_norm _ _
  have h3 : ‖w - x‖ ^ 2 ≤ 2 * l * ‖v‖ * ‖w - x‖ := by nlinarith
  rcases (norm_nonneg (w - x)).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · nlinarith

/-- Projections exist near a point around which `Ω` is locally closed (finite dimensions). -/
theorem eventually_euclideanProj_nonempty [FiniteDimensional ℝ H] (hx₀ : x₀ ∈ Ω)
    (hloc : ∃ r > 0, IsClosed (Ω ∩ closedBall x₀ r)) :
    ∀ᶠ x in 𝓝 x₀, (euclideanProj Ω x).Nonempty := by
  obtain ⟨r, hr, hcl⟩ := hloc
  set K := Ω ∩ closedBall x₀ r
  have hK : IsCompact K := (isCompact_closedBall x₀ r).of_isClosed_subset hcl inter_subset_right
  have hKne : K.Nonempty := ⟨x₀, hx₀, mem_closedBall_self hr.le⟩
  filter_upwards [ball_mem_nhds x₀ (half_pos hr)] with x hx
  rw [mem_ball] at hx
  obtain ⟨w, hwK, hw⟩ := hK.exists_infDist_eq_dist hKne x
  have hsub : infDist x Ω ≤ infDist x K := infDist_le_infDist_of_subset inter_subset_left hKne
  have hsup : infDist x K ≤ infDist x Ω := by
    refine (le_infDist ⟨x₀, hx₀⟩).2 fun z hz ↦ ?_
    by_cases hzr : z ∈ closedBall x₀ r
    · exact infDist_le_dist_of_mem ⟨hz, hzr⟩
    · rw [mem_closedBall, not_le] at hzr
      have h1 : infDist x K ≤ dist x x₀ := infDist_le_dist_of_mem ⟨hx₀, mem_closedBall_self hr.le⟩
      have h2 := dist_triangle z x x₀
      rw [dist_comm z x] at h2
      linarith
  exact ⟨w, hwK.1, by rw [← dist_eq_norm, ← hw]; linarith⟩

/-- Thm. 1.6 of [Mordukhovich 2018], inclusion `⊆`: normals from projections are limiting
normals. This holds for any set. -/
theorem toDual_mem_normalCone_of_mem_projNormalCone [CompleteSpace H] {v : H}
    (hv : v ∈ projNormalCone Ω x₀) : toDual ℝ H v ∈ normalCone Ω x₀ := by
  obtain ⟨hx₀, x, y, hx, hy, hmem⟩ := hv
  choose α hα w hw hyα using hmem
  refine ⟨hx₀, w, fun k ↦ toDual ℝ H (y k), ?_, (toDual ℝ H).continuous.tendsto _ |>.comp hy,
    fun k ↦ ?_⟩
  · refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k ↦ (hw k).1⟩
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have := (tendsto_iff_norm_sub_tendsto_zero.1 hx).const_mul 2
    rw [mul_zero] at this
    exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ norm_proj_sub_le (hw k) hx₀) this
  · change toDual ℝ H (y k) ∈ _
    rw [hyα, toDual_smul]
    exact smul_mem_regularNormalCone (toDual_sub_mem_regularNormalCone (hw k)) (hα k)

/-- [Mordukhovich 2018, Thm. 1.6, Step 4]: a regular normal at a point near which projections
exist is a limit of proximal normals at nearby points. -/
theorem mem_outerLimit_proj_of_regular [CompleteSpace H] {a u : H} (ha : a ∈ Ω)
    (hproj : ∀ᶠ z in 𝓝 a, (euclideanProj Ω z).Nonempty)
    (hu : toDual ℝ H u ∈ regularNormalCone Ω a) :
    u ∈ outerLimit (𝓝 a)
      (fun x ↦ {y | ∃ α : ℝ, 0 ≤ α ∧ ∃ w ∈ euclideanProj Ω x, y = α • (x - w)}) := by
  set l : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 1)
  have hl0 : Tendsto l atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlpos : ∀ j, 0 < l j := fun j ↦ Nat.one_div_pos_of_nat
  set z : ℕ → H := fun j ↦ a + l j • u
  have hz : Tendsto z atTop (𝓝 a) := by
    simpa [z] using (hl0.smul_const u).const_add a
  have hzproj : ∀ᶠ j in atTop, (euclideanProj Ω (z j)).Nonempty := hz.eventually hproj
  have key : ∀ j, ∃ w : H, (euclideanProj Ω (z j)).Nonempty → w ∈ euclideanProj Ω (z j) :=
    fun j ↦ by
      by_cases h : (euclideanProj Ω (z j)).Nonempty
      · exact ⟨h.some, fun _ ↦ h.some_mem⟩
      · exact ⟨a, fun h' ↦ absurd h' h⟩
  choose w hw using key
  have hwa : ∀ᶠ j in atTop, ‖w j - a‖ ≤ 2 * l j * ‖u‖ :=
    hzproj.mono fun j hj ↦ norm_proj_sub_le_of_smul ha (hlpos j).le (hw j hj)
  have hwlim : Tendsto w atTop (𝓝[Ω] a) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hzproj.mono fun j hj ↦ (hw j hj).1⟩
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) hwa ?_
    simpa using (hl0.const_mul 2).mul_const ‖u‖
  -- `(w j - a) / l j → 0`
  have hsmall : Tendsto (fun j ↦ (l j)⁻¹ • (w j - a)) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
    have hev := hwlim.eventually (hu.2 (ε / 4) (by positivity))
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hev.and hzproj)
    refine ⟨N, fun j hj ↦ ?_⟩
    obtain ⟨h1, h2⟩ := hN j hj
    rw [toDual_apply_apply] at h1
    have h3 := sq_norm_proj_sub_le ha (hw j h2)
    have h4 : ‖w j - a‖ ≤ 2 * l j * (ε / 4) := by
      rcases (norm_nonneg (w j - a)).eq_or_lt with h0 | h0
      · rw [← h0]; have := hlpos j; positivity
      · nlinarith [hlpos j]
    rw [dist_zero_right, norm_norm, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (hlpos j).le)]
    rw [inv_mul_lt_iff₀ (hlpos j)]
    nlinarith [hlpos j]
  refine mem_outerLimit_of_eventually z (fun j ↦ (l j)⁻¹ • (z j - w j)) hz ?_ ?_
  · have : (fun j ↦ (l j)⁻¹ • (z j - w j)) = fun j ↦ u - (l j)⁻¹ • (w j - a) := by
      funext j
      simp only [z, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ (hlpos j).ne', one_smul]
      abel
    rw [this]
    simpa using tendsto_const_nhds.sub hsmall
  · filter_upwards [hzproj] with j hj
    exact ⟨(l j)⁻¹, inv_nonneg.2 (hlpos j).le, w j, hw j hj, rfl⟩

/-- Thm. 1.6 of [Mordukhovich 2018]: for `Ω` locally closed around `x₀ ∈ Ω` in finite
dimensions, the normal cone (1.4) defined through projections is the limiting normal cone
`Lim sup_{x →Ω x₀} N̂(x; Ω)`. -/
theorem toDual_projNormalCone [FiniteDimensional ℝ H] (hx₀ : x₀ ∈ Ω)
    (hloc : ∃ r > 0, IsClosed (Ω ∩ closedBall x₀ r)) :
    toDual ℝ H '' projNormalCone Ω x₀ = normalCone Ω x₀ := by
  refine subset_antisymm (image_subset_iff.2 fun v hv ↦
    toDual_mem_normalCone_of_mem_projNormalCone hv) fun v' hv' ↦ ?_
  obtain ⟨-, a, v, ha, hv, hmem⟩ := hv'
  refine ⟨(toDual ℝ H).symm v', ⟨hx₀, ?_⟩, by simp⟩
  have hproj := eventually_euclideanProj_nonempty hx₀ hloc
  have ha' := (tendsto_nhdsWithin_iff.1 ha)
  refine mem_outerLimit_nhds_of_seq a (fun k ↦ (toDual ℝ H).symm (v k)) ha'.1
    (((toDual ℝ H).symm.continuous.tendsto _).comp hv) ?_
  filter_upwards [ha'.1.eventually (eventually_eventually_nhds.2 hproj)] with k hk
  exact mem_outerLimit_proj_of_regular (hmem k).1 hk (by simpa using hmem k)

/-- Thm. 1.6 of [Mordukhovich 2018], second representation in (1.7): for `Ω` locally closed
around `x₀ ∈ Ω` in finite dimensions, `N(x₀; Ω) = Lim sup_{x →Ω x₀, ω ↓ 0} N̂_ω(x; Ω)`. -/
theorem normalCone_eq_outerLimit_epsNormalCone_inner [FiniteDimensional ℝ H] (hx₀ : x₀ ∈ Ω)
    (hloc : ∃ r > 0, IsClosed (Ω ∩ closedBall x₀ r)) :
    normalCone Ω x₀ =
      outerLimit (𝓝[Ω] x₀ ×ˢ 𝓝[≥] (0 : ℝ)) (fun p ↦ epsNormalCone p.2 Ω p.1) := by
  refine subset_antisymm (fun v hv ↦ ?_) (fun v' hv' ↦ ⟨hx₀, ?_⟩)
  · obtain ⟨-, a, w, ha, hw, hmem⟩ := hv
    refine ⟨fun k ↦ (a k, 0), w, ha.prodMk (tendsto_nhdsWithin_iff.2
      ⟨tendsto_const_nhds, Eventually.of_forall fun _ ↦ mem_Ici.2 le_rfl⟩), hw, fun k ↦ ?_⟩
    simpa [epsNormalCone_zero] using hmem k
  obtain ⟨p, v, hp, hv, hmem⟩ := hv'
  have hpa := tendsto_nhdsWithin_iff.1 (tendsto_fst.comp hp)
  have hpω := tendsto_nhdsWithin_iff.1 (tendsto_snd.comp hp)
  simp only [Function.comp_def] at hpa hpω
  have hproj := eventually_euclideanProj_nonempty hx₀ hloc
  -- Step 3: for each `k`, move to a nearby point `wₖ` with an honest regular normal.
  have key : ∀ k : ℕ, ∃ b : H, ∃ y : H, ((p k).1 ∈ Ω ∧ 0 ≤ (p k).2 ∧
      ∀ᶠ z in 𝓝 (p k).1, (euclideanProj Ω z).Nonempty) →
      toDual ℝ H y ∈ regularNormalCone Ω b ∧
        ‖b - (p k).1‖ ≤ 2 * (1 / (k + 1)) * ((p k).2 + 1 / (k + 1)) ∧
        ‖y - (toDual ℝ H).symm (v k)‖ ≤ 2 * ((p k).2 + 1 / (k + 1)) := by
    intro k
    by_cases hk : (p k).1 ∈ Ω ∧ 0 ≤ (p k).2 ∧ ∀ᶠ z in 𝓝 (p k).1, (euclideanProj Ω z).Nonempty
    swap
    · exact ⟨0, 0, fun h ↦ absurd h hk⟩
    obtain ⟨hxΩ, hω, hpr⟩ := hk
    set xk := (p k).1
    set ω := (p k).2
    set u := (toDual ℝ H).symm (v k)
    have hu : toDual ℝ H u ∈ epsNormalCone ω Ω xk := by simpa [u] using hmem k
    have hε : (0 : ℝ) < 1 / (k + 1) := Nat.one_div_pos_of_nat
    set ε : ℝ := 1 / (k + 1)
    -- choose a small step `t`
    have hzt : Tendsto (fun t : ℝ ↦ xk + t • u) (𝓝[>] 0) (𝓝 xk) := by
      have : Tendsto (fun t : ℝ ↦ xk + t • u) (𝓝 0) (𝓝 (xk + (0 : ℝ) • u)) :=
        ((continuous_id.smul continuous_const).const_add xk).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    have hprt : ∀ᶠ t in 𝓝[>] (0 : ℝ), (euclideanProj Ω (xk + t • u)).Nonempty := hzt.eventually hpr
    -- projections of `xk + t • u` converge to `xk` within `Ω`
    have hsel : ∀ t : ℝ, ∃ w : H, (euclideanProj Ω (xk + t • u)).Nonempty →
        w ∈ euclideanProj Ω (xk + t • u) := fun t ↦ by
      by_cases h : (euclideanProj Ω (xk + t • u)).Nonempty
      · exact ⟨h.some, fun _ ↦ h.some_mem⟩
      · exact ⟨xk, fun h' ↦ absurd h' h⟩
    choose W hW using hsel
    have hWlim : Tendsto W (𝓝[>] 0) (𝓝[Ω] xk) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, hprt.mono fun t ht ↦ (hW t ht).1⟩
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h0 : Tendsto (fun t : ℝ ↦ 2 * t * ‖u‖) (𝓝[>] 0) (𝓝 0) := by
        have : Tendsto (fun t : ℝ ↦ 2 * t * ‖u‖) (𝓝 0) (𝓝 (2 * 0 * ‖u‖)) := by
          exact ((continuous_const.mul continuous_id).mul continuous_const).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ h0
      filter_upwards [hprt, self_mem_nhdsWithin] with t ht htpos
      exact norm_proj_sub_le_of_smul hxΩ (le_of_lt htpos) (hW t ht)
    have hev := hWlim.eventually (hu.2 ε hε)
    have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ≤ ε := by
      filter_upwards [Ioo_mem_nhdsGT hε] with t ht using ht.2.le
    obtain ⟨t, ⟨⟨h1, h2⟩, h3⟩, htpos⟩ := ((hev.and hprt).and hsmall |>.and
      self_mem_nhdsWithin).exists
    have htpos : (0 : ℝ) < t := htpos
    have hWt := hW t h2
    rw [toDual_apply_apply] at h1
    have hsq := sq_norm_proj_sub_le hxΩ hWt
    have hbd : ‖W t - xk‖ ≤ 2 * t * (ω + ε) := by
      rcases (norm_nonneg (W t - xk)).eq_or_lt with h0 | h0
      · rw [← h0]; have : 0 ≤ ω + ε := by linarith
        positivity
      · nlinarith
    refine ⟨W t, t⁻¹ • (xk + t • u - W t), fun _ ↦ ⟨?_, ?_, ?_⟩⟩
    · rw [toDual_smul]
      exact smul_mem_regularNormalCone (toDual_sub_mem_regularNormalCone hWt)
        (inv_nonneg.2 htpos.le)
    · have : 0 ≤ ω + ε := by linarith
      calc ‖W t - xk‖ ≤ 2 * t * (ω + ε) := hbd
        _ ≤ 2 * ε * (ω + ε) := by gcongr
    · have : t⁻¹ • (xk + t • u - W t) - u = -(t⁻¹ • (W t - xk)) := by
        rw [smul_sub, smul_add, smul_smul, inv_mul_cancel₀ htpos.ne', one_smul, smul_sub]
        abel
      rw [this, norm_neg, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 htpos.le),
        inv_mul_le_iff₀ htpos]
      linarith
  choose b y hby using key
  have hgood : ∀ᶠ k in atTop, (p k).1 ∈ Ω ∧ 0 ≤ (p k).2 ∧
      ∀ᶠ z in 𝓝 (p k).1, (euclideanProj Ω z).Nonempty :=
    hpa.2.and (hpω.2.and (hpa.1.eventually (eventually_eventually_nhds.2 hproj)))
  have hε : Tendsto (fun k : ℕ ↦ (1 : ℝ) / (k + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hb : Tendsto b atTop (𝓝 x₀) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h1 : Tendsto (fun k : ℕ ↦ 2 * (1 / ((k : ℝ) + 1)) * ((p k).2 + 1 / (k + 1)) +
        ‖(p k).1 - x₀‖) atTop (𝓝 (2 * 0 * (0 + 0) + 0)) :=
      ((hε.const_mul 2).mul (hpω.1.add hε)).add (tendsto_iff_norm_sub_tendsto_zero.1 hpa.1)
    rw [show (2 : ℝ) * 0 * (0 + 0) + 0 = 0 by ring] at h1
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ h1
    filter_upwards [hgood] with k hk
    have := (hby k hk).2.1
    have h2 := norm_add_le (b k - (p k).1) ((p k).1 - x₀)
    rw [sub_add_sub_cancel] at h2
    linarith
  have hy : Tendsto y atTop (𝓝 ((toDual ℝ H).symm v')) := by
    have hu : Tendsto (fun k ↦ (toDual ℝ H).symm (v k)) atTop (𝓝 ((toDual ℝ H).symm v')) :=
      ((toDual ℝ H).symm.continuous.tendsto _).comp hv
    have hd : Tendsto (fun k ↦ y k - (toDual ℝ H).symm (v k)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h1 : Tendsto (fun k : ℕ ↦ 2 * ((p k).2 + 1 / ((k : ℝ) + 1))) atTop (𝓝 (2 * (0 + 0))) :=
        (hpω.1.add hε).const_mul 2
      rw [show (2 : ℝ) * (0 + 0) = 0 by ring] at h1
      refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ h1
      filter_upwards [hgood] with k hk using (hby k hk).2.2
    simpa using hd.add hu
  refine mem_outerLimit_of_eventually b (fun k ↦ toDual ℝ H (y k))
    (tendsto_nhdsWithin_iff.2 ⟨hb, hgood.mono fun k hk ↦ (hby k hk).1.1⟩) ?_
    (hgood.mono fun k hk ↦ (hby k hk).1)
  simpa [Function.comp_def] using ((toDual ℝ H).continuous.tendsto _).comp hy

/-- Prop. 1.2 of [Mordukhovich 2018] (normal cone characterization of boundary points): for `Ω`
locally closed around `x₀ ∈ Ω` in finite dimensions, `x₀` is a boundary point of `Ω` iff the
normal cone `N(x₀; Ω)` is nontrivial. -/
theorem exists_ne_zero_mem_normalCone_iff_inner [FiniteDimensional ℝ H] (hx₀ : x₀ ∈ Ω)
    (hloc : ∃ r > 0, IsClosed (Ω ∩ closedBall x₀ r)) :
    (∃ v ∈ normalCone Ω x₀, v ≠ 0) ↔ x₀ ∈ frontier Ω := by
  rw [frontier, Set.mem_sdiff, and_iff_right (subset_closure hx₀)]
  constructor
  · rintro ⟨v, hv, hv0⟩ hint
    rw [normalCone_of_mem_interior hint] at hv
    exact hv0 hv
  · intro hint
    have hcl : x₀ ∈ closure Ωᶜ := by rwa [closure_compl, mem_compl_iff]
    obtain ⟨x, hxΩ, hx⟩ := mem_closure_iff_seq_limit.1 hcl
    have hproj := hx.eventually (eventually_euclideanProj_nonempty hx₀ hloc)
    have hsel : ∀ k, ∃ w : H, (euclideanProj Ω (x k)).Nonempty → w ∈ euclideanProj Ω (x k) :=
      fun k ↦ by
        by_cases h : (euclideanProj Ω (x k)).Nonempty
        · exact ⟨h.some, fun _ ↦ h.some_mem⟩
        · exact ⟨x₀, fun h' ↦ absurd h' h⟩
    choose w hw using hsel
    set u : ℕ → H := fun k ↦ ‖x k - w k‖⁻¹ • (x k - w k)
    have hne : ∀ᶠ k in atTop, x k - w k ≠ 0 := hproj.mono fun k hk h ↦ by
      rw [sub_eq_zero] at h
      exact hxΩ k (h ▸ (hw k hk).1)
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hproj.and hne)
    have hus : ∀ k, u (k + N) ∈ sphere (0 : H) 1 := fun k ↦ by
      have := (hN (k + N) (Nat.le_add_left N k)).2
      simp [u, norm_smul, this]
    obtain ⟨u₀, hu₀, φ, hφ, hlim⟩ := (isCompact_sphere (0 : H) 1).tendsto_subseq hus
    have hmem : u₀ ∈ projNormalCone Ω x₀ := by
      refine ⟨hx₀, fun k ↦ x (φ k + N), fun k ↦ u (φ k + N), ?_, hlim, fun k ↦ ?_⟩
      · exact hx.comp ((tendsto_add_atTop_nat N).comp hφ.tendsto_atTop)
      · exact ⟨_, inv_nonneg.2 (norm_nonneg _), w (φ k + N),
          hw _ (hN _ (Nat.le_add_left N _)).1, rfl⟩
    refine ⟨toDual ℝ H u₀, toDual_mem_normalCone_of_mem_projNormalCone hmem, fun h ↦ ?_⟩
    have : ‖toDual ℝ H u₀‖ = 1 := by rw [LinearIsometryEquiv.norm_map]; simpa using hu₀
    rw [h, norm_zero] at this
    exact zero_ne_one this

end VariationalAnalysis
