/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis.SecondOrder.ProtoTwiceEpi

/-!
# Semidifferentiability of proximal mappings

This file proves the part of [Mordukhovich 2024, Cor. 1.101] on proximal mappings: for a
function `φ` that is l.s.c., prox-bounded and continuously prox-regular at `x̄` for `v̄`, and all
small `λ > 0`, twice epi-differentiability of `φ` at `x̄` for `v̄` is equivalent to
proto-differentiability of `P_λφ` at `x̄ + λv̄`, and to semidifferentiability of `P_λφ` at
`x̄ + λv̄`; moreover `DP_λφ = P_λ(d²φ(x̄, v̄)/2)`.

## Main results

* `tendsto_inv_smul_of_hasDirDerivAt`: for a Lipschitz mapping, directional derivatives are
  limits of difference quotients along `t_k ↓ 0`, `w_k → w`.
* `isSemiderivative_singleton_of_tendsto`, `exists_tendsto_of_semidifferentiableAt`: for a
  locally single-valued mapping, semidifferentiability in the sense of
  [Mordukhovich 2024, Def. 1.100] is the convergence of the difference quotients.
* `ContinuouslyProxRegularFor.exists_twiceEpiDifferentiableAt_iff_proximalMap`:
  [Mordukhovich 2024, Cor. 1.101], the equivalence with (b) and (c).
* `ContinuouslyProxRegularFor.exists_isSemiderivative_proximalMap`:
  [Mordukhovich 2024, Cor. 1.101], the formula `DP_λφ = P_λ(d²φ/2)`.
-/

open Filter Topology Set Metric InnerProductSpace
open scoped NNReal RealInnerProductSpace

namespace VariationalAnalysis

section Semiderivative

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

/-- For a mapping Lipschitz around `x`, a directional derivative at `x` in the direction `w₀` is
the limit of the difference quotients along `t_k ↓ 0`, `w_k → w₀`. -/
theorem tendsto_inv_smul_of_hasDirDerivAt {f : X → Y} {x : X} {U : Set X} {K : ℝ≥0}
    (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith K f U) {w₀ : X} {v : Y}
    (h : HasDirDerivAt f x w₀ v) {t : ℕ → ℝ} (ht : Tendsto t atTop (𝓝[>] 0)) {w : ℕ → X}
    (hw : Tendsto w atTop (𝓝 w₀)) :
    Tendsto (fun k ↦ (t k)⁻¹ • (f (x + t k • w k) - f x)) atTop (𝓝 v) := by
  have h1 : Tendsto (fun k ↦ (t k)⁻¹ • (f (x + t k • w₀) - f x)) atTop (𝓝 v) := h.comp ht
  have hpos : ∀ᶠ k in atTop, 0 < t k := (tendsto_nhdsWithin_iff.1 ht).2
  have ht0 : Tendsto t atTop (𝓝 0) := tendsto_nhds_of_tendsto_nhdsWithin ht
  have hx : ∀ {z : ℕ → X} {z₀ : X}, Tendsto z atTop (𝓝 z₀) →
      Tendsto (fun k ↦ x + t k • z k) atTop (𝓝 x) := fun hz ↦ by
    have := (tendsto_const_nhds (x := x)).add (ht0.smul hz)
    simpa using this
  have hdiff : Tendsto (fun k ↦ (t k)⁻¹ • (f (x + t k • w k) - f x) -
      (t k)⁻¹ • (f (x + t k • w₀) - f x)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using ((hw.sub_const w₀).norm.const_mul (K : ℝ)))
    filter_upwards [hpos, (hx hw).eventually hU,
      (hx (tendsto_const_nhds (x := w₀))).eventually hU] with k hk hk1 hk2
    have := hL.dist_le_mul _ hk1 _ hk2
    rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul,
      Real.norm_of_nonneg hk.le] at this
    rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_of_nonneg (inv_pos.2 hk).le]
    calc (t k)⁻¹ * ‖f (x + t k • w k) - f (x + t k • w₀)‖
        ≤ (t k)⁻¹ * (K * (t k * ‖w k - w₀‖)) :=
          mul_le_mul_of_nonneg_left this (inv_pos.2 hk).le
      _ = K * ‖w k - w₀‖ := by field_simp
  have := h1.add hdiff
  simp only [add_sub_cancel, add_zero] at this
  exact this

/-- Along `t_k ↓ 0`, `w_k → w₀`, the difference quotient sets of a locally single-valued mapping
are singletons. -/
theorem eventually_image_eq_singleton {S : X → Set Y} {f : X → Y} {x : X}
    (hS : ∀ᶠ u in 𝓝 x, S u = {f u}) {w₀ : X} {a : ℕ → ℝ × X}
    (ha : Tendsto a atTop (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w₀)) :
    ∀ᶠ k in atTop, (fun y ↦ (a k).1⁻¹ • (y - f x)) '' S (x + (a k).1 • (a k).2) =
      {(a k).1⁻¹ • (f (x + (a k).1 • (a k).2) - f x)} := by
  have hx : Tendsto (fun k ↦ x + (a k).1 • (a k).2) atTop (𝓝 x) := by
    have := (tendsto_const_nhds (x := x)).add
      ((tendsto_nhds_of_tendsto_nhdsWithin (tendsto_fst.comp ha)).smul (tendsto_snd.comp ha))
    simpa using this
  filter_upwards [hx.eventually hS] with k hk
  rw [hk, image_singleton]

/-- If `S = {f(·)}` near `x` and the difference quotients of `f` at `x` converge to `d` along
`t_k ↓ 0`, `w_k → w₀`, then `{d}` is the semiderivative of `S` at `x` for `f x` and `w₀`
[Mordukhovich 2024, Def. 1.100]. -/
theorem isSemiderivative_singleton_of_tendsto {S : X → Set Y} {f : X → Y} {x : X}
    (hS : ∀ᶠ u in 𝓝 x, S u = {f u}) {w₀ : X} {d : Y}
    (hD : ∀ t : ℕ → ℝ, Tendsto t atTop (𝓝[>] 0) → ∀ w : ℕ → X, Tendsto w atTop (𝓝 w₀) →
      Tendsto (fun k ↦ (t k)⁻¹ • (f (x + t k • w k) - f x)) atTop (𝓝 d)) :
    IsSemiderivative S x (f x) w₀ {d} := by
  have hlim : ∀ a : ℕ → ℝ × X, Tendsto a atTop (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w₀) →
      Tendsto (fun k ↦ (a k).1⁻¹ • (f (x + (a k).1 • (a k).2) - f x)) atTop (𝓝 d) :=
    fun a ha ↦ hD _ (tendsto_fst.comp ha) _ (tendsto_snd.comp ha)
  have hinner : ({d} : Set Y) ⊆ innerLimit (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w₀)
      (fun q : ℝ × X ↦ (fun y ↦ q.1⁻¹ • (y - f x)) '' S (x + q.1 • q.2)) := by
    rintro y rfl a ha
    exact ⟨_, hlim a ha, (eventually_image_eq_singleton hS ha).mono fun k hk ↦ by
      show _ ∈ (fun y ↦ (a k).1⁻¹ • (y - f x)) '' S (x + (a k).1 • (a k).2)
      rw [hk]; exact mem_singleton _⟩
  have houter : outerLimit (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w₀)
      (fun q : ℝ × X ↦ (fun y ↦ q.1⁻¹ • (y - f x)) '' S (x + q.1 • q.2)) ⊆ {d} := by
    rintro y ⟨a, v, ha, hv, hmem⟩
    refine tendsto_nhds_unique hv ((hlim a ha).congr' ?_)
    filter_upwards [eventually_image_eq_singleton hS ha] with k hk
    have : v k ∈ (fun y ↦ (a k).1⁻¹ • (y - f x)) '' S (x + (a k).1 • (a k).2) := hmem k
    rw [hk] at this
    exact this.symm
  exact ⟨Subset.antisymm houter (hinner.trans (innerLimit_subset_outerLimit _ _)),
    Subset.antisymm ((innerLimit_subset_outerLimit _ _).trans houter) hinner⟩

/-- A mapping that is single-valued and Lipschitz around `x` and semidifferentiable at `x`
[Mordukhovich 2024, Def. 1.100] has convergent difference quotients along `t_k ↓ 0`,
`w_k → w₀`. -/
theorem exists_tendsto_of_semidifferentiableAt [ProperSpace Y] {S : X → Set Y} {f : X → Y}
    {x : X} {U : Set X} {K : ℝ≥0} (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith K f U)
    (hS : ∀ᶠ u in 𝓝 x, S u = {f u}) (h : SemidifferentiableAt' S x (f x)) :
    ∃ D : X → Y, ∀ t : ℕ → ℝ, Tendsto t atTop (𝓝[>] 0) → ∀ (w : ℕ → X) (w₀ : X),
      Tendsto w atTop (𝓝 w₀) →
      Tendsto (fun k ↦ (t k)⁻¹ • (f (x + t k • w k) - f x)) atTop (𝓝 (D w₀)) := by
  suffices H : ∀ w₀ : X, ∃ d : Y, ∀ t : ℕ → ℝ, Tendsto t atTop (𝓝[>] 0) → ∀ w : ℕ → X,
      Tendsto w atTop (𝓝 w₀) →
      Tendsto (fun k ↦ (t k)⁻¹ • (f (x + t k • w k) - f x)) atTop (𝓝 d) by
    choose D hD using H
    exact ⟨D, fun t ht w w₀ hw ↦ hD w₀ t ht w hw⟩
  intro w₀
  obtain ⟨Dset, hout, hinn⟩ := h w₀
  have hxU : x ∈ U := mem_of_mem_nhds hU
  -- a cluster point of the difference quotients along `t = 1/(k+1)`
  obtain ⟨t₀, ht₀_def⟩ : ∃ t₀ : ℕ → ℝ, t₀ = fun k : ℕ ↦ 1 / ((k : ℝ) + 1) := ⟨_, rfl⟩
  have ht₀ : Tendsto t₀ atTop (𝓝[>] 0) := by
    rw [ht₀_def]
    exact tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun k ↦ show (0 : ℝ) < 1 / ((k : ℝ) + 1) from
        Nat.one_div_pos_of_nat⟩
  have ha₀ : Tendsto (fun k ↦ (t₀ k, w₀)) atTop (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w₀) :=
    ht₀.prodMk tendsto_const_nhds
  have hx₀ : Tendsto (fun k ↦ x + t₀ k • w₀) atTop (𝓝 x) := by
    have := (tendsto_const_nhds (x := x)).add
      ((tendsto_nhds_of_tendsto_nhdsWithin ht₀).smul_const w₀)
    simpa using this
  have hbd : ∀ᶠ k in atTop, (t₀ k)⁻¹ • (f (x + t₀ k • w₀) - f x) ∈
      closedBall (0 : Y) (K * ‖w₀‖) := by
    filter_upwards [(tendsto_nhdsWithin_iff.1 ht₀).2, hx₀.eventually hU] with k hk hkU
    have hk : 0 < t₀ k := hk
    have := hL.dist_le_mul _ hkU _ hxU
    rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hk.le] at this
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (inv_pos.2 hk).le]
    calc (t₀ k)⁻¹ * ‖f (x + t₀ k • w₀) - f x‖ ≤ (t₀ k)⁻¹ * (K * (t₀ k * ‖w₀‖)) :=
          mul_le_mul_of_nonneg_left this (inv_pos.2 hk).le
      _ = K * ‖w₀‖ := by field_simp
  obtain ⟨d, -, ψ, hψ, hlim⟩ := tendsto_subseq_of_frequently_bounded isBounded_closedBall
    hbd.frequently
  have hd : d ∈ Dset := by
    rw [← hout]
    refine mem_outerLimit_of_eventually (fun k ↦ (t₀ (ψ k), w₀)) _
      (ha₀.comp hψ.tendsto_atTop) hlim ?_
    filter_upwards [eventually_image_eq_singleton hS (ha₀.comp hψ.tendsto_atTop)] with k hk
    simp only [Function.comp_apply] at hk
    show _ ∈ (fun y ↦ (t₀ (ψ k))⁻¹ • (y - f x)) '' S (x + t₀ (ψ k) • w₀)
    rw [hk]
    exact mem_singleton _
  rw [← hinn] at hd
  refine ⟨d, fun t ht w hw ↦ ?_⟩
  obtain ⟨v, hv, hvm⟩ := hd (fun k ↦ (t k, w k)) (ht.prodMk hw)
  refine hv.congr' ?_
  filter_upwards [hvm, eventually_image_eq_singleton hS (ht.prodMk hw)] with k h1 h2
  have h1 : v k ∈ (fun y ↦ (t k)⁻¹ • (y - f x)) '' S (x + t k • w k) := h1
  rw [h2] at h1
  exact h1

end Semiderivative

section Prox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {φ : E → EReal} {x₀ : E}

/-- **Semidifferentiability of proximal mappings** [Mordukhovich 2024, Cor. 1.101], the
equivalences with (b) and (c): let `φ` be l.s.c., prox-bounded and continuously prox-regular at
`x̄` for `v̄ = ⟨g, ·⟩`. Then for all small `λ > 0`, `φ` is twice epi-differentiable at `x̄` for
`v̄` iff `P_λφ` is proto-differentiable at `(x̄ + λg, x̄)`, iff `P_λφ` is semidifferentiable at
`x̄ + λg` for `x̄`. -/
theorem ContinuouslyProxRegularFor.exists_twiceEpiDifferentiableAt_iff_proximalMap {g : E}
    (hφ : ContinuouslyProxRegularFor φ x₀ (toDual ℝ E g))
    (hlsc : ∀ x, LowerSemicontinuousAt φ x)
    (hbd : ∃ a b : ℝ, ∀ x, ((a - b * ‖x - x₀‖ ^ 2 : ℝ) : EReal) ≤ φ x) :
    ∃ l₀ > (0 : ℝ), ∀ l, 0 < l → l < l₀ →
      (TwiceEpiDifferentiableAt φ x₀ (toDual ℝ E g) ↔
        ProtoDifferentiableAt (proximalMap φ l) (x₀ + l • g) x₀) ∧
      (TwiceEpiDifferentiableAt φ x₀ (toDual ℝ E g) ↔
        SemidifferentiableAt' (proximalMap φ l) (x₀ + l • g) x₀) := by
  obtain ⟨l₀, hl₀, H⟩ := hφ.eventually_mem_subdiff_iff hlsc hbd
  refine ⟨l₀, hl₀, fun l hl hll ↦ ?_⟩
  obtain ⟨δ, hδ, p, hp0, hpU, hLip, hgraph⟩ := H l hl hll
  have hball := ball_mem_nhds (x₀ + l • g) hδ
  have hS : ∀ᶠ u in 𝓝 (x₀ + l • g), proximalMap φ l u = {p u} := eventually_of_mem hball hpU
  have hmemP : x₀ ∈ proximalMap φ l (x₀ + l • g) := by
    rw [hpU _ (mem_ball_self hδ), hp0]; exact mem_singleton _
  have hmemp : x₀ ∈ ({p (x₀ + l • g)} : Set E) := by rw [hp0]; exact mem_singleton _
  have hEq : graph (proximalMap φ l) =ᶠ[𝓝 (x₀ + l • g, x₀)]
      graph fun u ↦ ({p u} : Set E) := by
    refine eventuallyEq_set.2 ?_
    filter_upwards [(continuous_fst.tendsto (x₀ + l • g, x₀)).eventually hball] with q hq
    show q.2 ∈ proximalMap φ l q.1 ↔ q.2 ∈ ({p q.1} : Set E)
    rw [hpU _ hq]
  -- twice epi-differentiability is geometric derivability of the graph of `p`
  have h1 : TwiceEpiDifferentiableAt φ x₀ (toDual ℝ E g) ↔
      GeometricallyDerivableAt (graph fun u ↦ ({p u} : Set E)) (x₀ + l • g, x₀) :=
    hφ.twiceEpiDifferentiableAt_iff_protoDifferentiableAt.trans
      (protoDifferentiableAt_iff_geometricallyDerivableAt_graph hl.ne' hp0 hgraph)
  have h2 : ProtoDifferentiableAt (proximalMap φ l) (x₀ + l • g) x₀ ↔
      GeometricallyDerivableAt (graph fun u ↦ ({p u} : Set E)) (x₀ + l • g, x₀) :=
    ⟨fun h ↦ GeometricallyDerivableAt.congr h hEq hmemp,
      fun h ↦ GeometricallyDerivableAt.congr h hEq.symm hmemP⟩
  refine ⟨h1.trans h2.symm, h1.trans ⟨fun hG ↦ ?_, fun hsemi ↦ ?_⟩⟩
  · have hG' : GeometricallyDerivableAt (graph fun u ↦ ({p u} : Set E))
        (x₀ + l • g, p (x₀ + l • g)) := by rw [hp0]; exact hG
    have hdir := dirDifferentiableAt_of_geometricallyDerivableAt hball hLip hG'
    intro w₀
    obtain ⟨d, hd⟩ := hdir w₀
    have := isSemiderivative_singleton_of_tendsto (S := proximalMap φ l) hS
      (fun t ht w hw ↦ tendsto_inv_smul_of_hasDirDerivAt hball hLip hd ht hw)
    rw [hp0] at this
    exact ⟨{d}, this⟩
  · have hsemi' : SemidifferentiableAt' (proximalMap φ l) (x₀ + l • g) (p (x₀ + l • g)) := by
      rw [hp0]; exact hsemi
    obtain ⟨D, hD⟩ := exists_tendsto_of_semidifferentiableAt hball hLip hS hsemi'
    have := geometricallyDerivableAt_graph_of_tendsto hball hLip hD
    rwa [hp0] at this

/-- **The semiderivative of the proximal mapping** [Mordukhovich 2024, Cor. 1.101]: let `φ` be
l.s.c., prox-bounded, continuously prox-regular and twice epi-differentiable at `x̄` for
`v̄ = ⟨g, ·⟩`. Then for all small `λ > 0` the semiderivative of `P_λφ` at `x̄ + λg` for `x̄` in
any direction `w` is `P_λ(d²φ(x̄, v̄)/2)(w)`, which is a singleton. -/
theorem ContinuouslyProxRegularFor.exists_isSemiderivative_proximalMap {g : E}
    (hφ : ContinuouslyProxRegularFor φ x₀ (toDual ℝ E g))
    (H : TwiceEpiDifferentiableAt φ x₀ (toDual ℝ E g))
    (hlsc : ∀ x, LowerSemicontinuousAt φ x)
    (hbd : ∃ a b : ℝ, ∀ x, ((a - b * ‖x - x₀‖ ^ 2 : ℝ) : EReal) ≤ φ x) :
    ∃ l₀ > (0 : ℝ), ∀ l, 0 < l → l < l₀ → ∀ w,
      (proximalMap (fun w ↦ ((1 / 2 : ℝ) : EReal) *
        secondSubderiv φ x₀ (toDual ℝ E g) w) l w).Subsingleton ∧
      IsSemiderivative (proximalMap φ l) (x₀ + l • g) x₀ w
        (proximalMap (fun w ↦ ((1 / 2 : ℝ) : EReal) *
          secondSubderiv φ x₀ (toDual ℝ E g) w) l w) := by
  obtain ⟨l₁, hl₁, H1⟩ := hφ.eventually_mem_subdiff_iff hlsc hbd
  obtain ⟨l₂, hl₂, H2⟩ := hφ.1.exists_tendsto_inv_smul_sub_proximalMap H hlsc hbd
  refine ⟨min l₁ l₂, lt_min hl₁ hl₂, fun l hl hll w₀ ↦ ?_⟩
  obtain ⟨δ, hδ, p, hp0, hpU, -, -⟩ := H1 l hl (hll.trans_le (min_le_left _ _))
  obtain ⟨D, hD, hconv⟩ := H2 l hl (hll.trans_le (min_le_right _ _))
  have hball := ball_mem_nhds (x₀ + l • g) hδ
  have hS : ∀ᶠ u in 𝓝 (x₀ + l • g), proximalMap φ l u = {p u} := eventually_of_mem hball hpU
  have := isSemiderivative_singleton_of_tendsto (S := proximalMap φ l) (d := D w₀) hS
    (fun t ht w hw ↦ by
      rw [hp0]
      refine hconv t ht w (fun k ↦ p (x₀ + l • g + t k • w k)) w₀ hw ?_
      have hx : Tendsto (fun k ↦ x₀ + l • g + t k • w k) atTop (𝓝 (x₀ + l • g)) := by
        have := (tendsto_const_nhds (x := x₀ + l • g)).add
          ((tendsto_nhds_of_tendsto_nhdsWithin ht).smul hw)
        simpa using this
      filter_upwards [hx.eventually hball] with k hk
      rw [hpU _ hk]
      exact mem_singleton _)
  rw [hp0] at this
  rw [hD w₀]
  exact ⟨subsingleton_singleton, this⟩

end Prox

end VariationalAnalysis
