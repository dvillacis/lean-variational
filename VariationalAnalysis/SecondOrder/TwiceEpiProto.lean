/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis.SecondOrder.TwiceEpiProx
import VariationalAnalysis.SecondOrder.ProtoDiff

/-!
# Twice epi-differentiability implies proto-differentiability of the subgradient mapping

This file proves one implication of [Mordukhovich 2024, Thm. 1.98]: if `φ` is continuously
prox-regular at `x̄` for `v̄` and twice epi-differentiable at `x̄` for `v̄`, then `∂φ` is
proto-differentiable at `(x̄, v̄)`.

## Main results

* `geometricallyDerivableAt_graph_of_tendsto`: the graph of a mapping that is Lipschitz around
  `x` and semidifferentiable at `x` is geometrically derivable at `(x, f x)`.
* `ContinuouslyProxRegularFor.eventually_mem_subdiff_iff`: for an l.s.c., prox-bounded,
  continuously prox-regular function and small `λ`, near `(x̄, g)` one has `⟨y, ·⟩ ∈ ∂φ(x)` iff
  `x = P_λφ(x + λy)`.
* `proxGraphEquiv`: the linear isomorphism `(x, v) ↦ (x + λv, x)` of `E × E*` onto `E × E`.
* `protoDifferentiableAt_iff_geometricallyDerivableAt_graph`: under this isomorphism,
  proto-differentiability of a mapping corresponds to geometric derivability of the graph of
  its resolvent.
* `TwiceEpiDifferentiableAt.congr`, `SubdiffContinuousFor.congr`,
  `ProxRegularFor.exists_localization`: twice epi-differentiability and subdifferential
  continuity are local properties, and a prox-regular function agrees near `x̄` with an l.s.c.,
  prox-bounded one.
* `ContinuouslyProxRegularFor.protoDifferentiableAt_subdiff`:
  [Mordukhovich 2024, Thm. 1.98], the implication from twice epi-differentiability of `φ` to
  proto-differentiability of `∂φ`.

## Implementation notes

The function is first replaced by `φ` plus the indicator of a closed ball around `x̄`, which is
l.s.c. and prox-bounded. For such a function, `SecondOrder/TwiceEpiProx` gives the
semidifferentiability of `P_λφ` at `x̄ + λv̄`, so the graph of `P_λφ` is geometrically derivable,
and the graph of `∂φ` is locally the preimage of the graph of `P_λφ` under the linear isomorphism
`(x, v) ↦ (x + λv, x)`.
-/

open Filter Topology Set Metric InnerProductSpace
open scoped NNReal RealInnerProductSpace

namespace VariationalAnalysis

/-! ### Graphs of semidifferentiable mappings -/

section Graph

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

/-- The graph of a mapping `f` that is Lipschitz around `x` and semidifferentiable at `x`
(`t_k⁻¹(f(x + t_k w_k) - f(x)) → D(w)` for `t_k ↓ 0`, `w_k → w`) is geometrically derivable at
`(x, f x)`. -/
theorem geometricallyDerivableAt_graph_of_tendsto {f : X → Y} {x : X} {U : Set X} {K : ℝ≥0}
    (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith K f U) {D : X → Y}
    (hD : ∀ t : ℕ → ℝ, Tendsto t atTop (𝓝[>] 0) → ∀ (w : ℕ → X) (w₀ : X),
      Tendsto w atTop (𝓝 w₀) →
      Tendsto (fun k ↦ (t k)⁻¹ • (f (x + t k • w k) - f x)) atTop (𝓝 (D w₀))) :
    GeometricallyDerivableAt (graph fun x ↦ ({f x} : Set Y)) (x, f x) := by
  have hxU : x ∈ U := mem_of_mem_nhds hU
  -- `D 0 = 0`
  have hD0 : D 0 = 0 := by
    have ht : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun k ↦ show (0 : ℝ) < 1 / ((k : ℝ) + 1) from
          Nat.one_div_pos_of_nat⟩
    have h := hD _ ht (fun _ ↦ 0) 0 tendsto_const_nhds
    simp only [smul_zero, add_zero, sub_self] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  -- tangents to the graph are of the form `(w, D w)`
  have htan : ∀ q ∈ contingentCone (graph fun x ↦ ({f x} : Set Y)) (x, f x), q.2 = D q.1 := by
    rintro ⟨w, z⟩ ⟨-, a, α, ha, halim, hlim⟩
    have haf : ∀ k, (a k).2 = f (a k).1 := fun k ↦ (ha k).1
    have hα : ∀ k, 0 ≤ α k := fun k ↦ (ha k).2
    have ha1 : Tendsto (fun k ↦ (a k).1) atTop (𝓝 x) :=
      (continuous_fst.tendsto (x, f x)).comp halim
    have h1 : Tendsto (fun k ↦ α k • ((a k).1 - x)) atTop (𝓝 w) := by
      simpa [Function.comp_def] using (continuous_fst.tendsto (w, z)).comp hlim
    have h2 : Tendsto (fun k ↦ α k • (f (a k).1 - f x)) atTop (𝓝 z) := by
      simpa [Function.comp_def, haf] using (continuous_snd.tendsto (w, z)).comp hlim
    show z = D w
    by_cases hw : w = 0
    · rw [hw, hD0]
      rw [hw] at h1
      refine tendsto_nhds_unique h2 (squeeze_zero_norm' ?_
        (by simpa using (h1.norm.const_mul (K : ℝ))))
      filter_upwards [ha1.eventually hU] with k hk
      have := hL.dist_le_mul _ hk _ hxU
      rw [dist_eq_norm, dist_eq_norm] at this
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (hα k), mul_left_comm]
      exact mul_le_mul_of_nonneg_left this (hα k)
    · have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
      have hev : ∀ᶠ k in atTop, ‖w‖ / 2 < α k * ‖(a k).1 - x‖ := by
        have := h1.norm.eventually (lt_mem_nhds (half_lt_self hwpos))
        filter_upwards [this] with k hk
        rwa [norm_smul, Real.norm_of_nonneg (hα k)] at hk
      have hαpos : ∀ᶠ k in atTop, 0 < α k := by
        filter_upwards [hev] with k hk
        rcases (hα k).eq_or_lt with h0 | h0
        · rw [← h0, zero_mul] at hk; linarith
        · exact h0
      have ht : Tendsto (fun k ↦ (α k)⁻¹) atTop (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, hαpos.mono fun k hk ↦ inv_pos.2 hk⟩
        have hb : Tendsto (fun k ↦ 2 / ‖w‖ * ‖(a k).1 - x‖) atTop (𝓝 0) := by
          have := ((ha1.sub_const x).norm).const_mul (2 / ‖w‖)
          simpa using this
        refine squeeze_zero' (hαpos.mono fun k hk ↦ (inv_pos.2 hk).le) ?_ hb
        filter_upwards [hev, hαpos] with k hk hk0
        rw [inv_le_iff_one_le_mul₀ hk0]
        have : 2 / ‖w‖ * ‖(a k).1 - x‖ * α k = 2 / ‖w‖ * (α k * ‖(a k).1 - x‖) := by ring
        rw [this, div_mul_eq_mul_div, le_div_iff₀ hwpos]
        linarith
      have h3 := hD _ ht (fun k ↦ α k • ((a k).1 - x)) w h1
      refine tendsto_nhds_unique h2 (h3.congr' ?_)
      filter_upwards [hαpos] with k hk
      rw [inv_inv, smul_smul, inv_mul_cancel₀ hk.ne', one_smul, add_sub_cancel]
  refine geometricallyDerivableAt_of_seq fun q hq t ht ↦ ?_
  obtain ⟨w, z⟩ := q
  have hz : z = D w := htan _ hq
  refine ⟨fun k ↦ (x + t k • w, f (x + t k • w)), Eventually.of_forall fun k ↦ mem_singleton _,
    ?_⟩
  have hpos : ∀ᶠ k in atTop, 0 < t k := (tendsto_nhdsWithin_iff.1 ht).2
  have h1 : Tendsto (fun k ↦ (t k)⁻¹ • (x + t k • w - x)) atTop (𝓝 w) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hpos] with k hk
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hk.ne', one_smul]
  have h2 := hD t ht (fun _ ↦ w) w tendsto_const_nhds
  rw [hz]
  exact h1.prodMk_nhds h2

end Graph

/-! ### Local properties -/

section Local

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {φ ψ : E → EReal} {x₀ : E}
  {v₀ : StrongDual ℝ E}

/-- Twice epi-differentiability is a local property. -/
theorem TwiceEpiDifferentiableAt.congr (h : TwiceEpiDifferentiableAt φ x₀ v₀)
    (hψ : ∀ᶠ x in 𝓝 x₀, ψ x = φ x) : TwiceEpiDifferentiableAt ψ x₀ v₀ := by
  have h0 : ψ x₀ = φ x₀ := hψ.self_of_nhds
  have hq : ∀ t w, ψ (x₀ + t • w) = φ (x₀ + t • w) →
      secondDiffQuot ψ x₀ v₀ t w = secondDiffQuot φ x₀ v₀ t w := fun t w htw ↦ by
    rw [secondDiffQuot, secondDiffQuot, htw, h0]
  have hsub : ∀ w, secondSubderiv ψ x₀ v₀ w = secondSubderiv φ x₀ v₀ w := fun w ↦ by
    refine liminf_congr ?_
    have ht : Tendsto (fun p : ℝ × E ↦ x₀ + p.1 • p.2) (𝓝[>] 0 ×ˢ 𝓝 w) (𝓝 x₀) := by
      have := (tendsto_const_nhds (x := x₀)).add
        (((tendsto_fst (f := 𝓝[>] (0 : ℝ)) (g := 𝓝 w)).mono_right nhdsWithin_le_nhds).smul
          tendsto_snd)
      simpa using this
    filter_upwards [ht.eventually hψ] with p hp
    exact hq _ _ hp
  have hseq : ∀ (t : ℕ → ℝ) (wk : ℕ → E) (w : E), Tendsto t atTop (𝓝[>] 0) →
      Tendsto wk atTop (𝓝 w) → ∀ᶠ k in atTop,
        secondDiffQuot ψ x₀ v₀ (t k) (wk k) = secondDiffQuot φ x₀ v₀ (t k) (wk k) := by
    intro t wk w ht hwk
    have hx : Tendsto (fun k ↦ x₀ + t k • wk k) atTop (𝓝 x₀) := by
      have := (tendsto_const_nhds (x := x₀)).add
        ((tendsto_nhds_of_tendsto_nhdsWithin ht).smul hwk)
      simpa using this
    filter_upwards [hx.eventually hψ] with k hk
    exact hq _ _ hk
  obtain ⟨⟨r, hr⟩, H⟩ := h
  refine ⟨⟨r, by rw [h0, hr]⟩, fun t ht w ↦ ⟨fun wk hwk ↦ ?_, ?_⟩⟩
  · rw [hsub, liminf_congr (hseq t wk w ht hwk)]
    exact (H t ht w).1 wk hwk
  · obtain ⟨wk, hwk, hle⟩ := (H t ht w).2
    refine ⟨wk, hwk, ?_⟩
    rw [hsub, limsup_congr (hseq t wk w ht hwk)]
    exact hle

/-- Subdifferential continuity is a local property. -/
theorem SubdiffContinuousFor.congr (h : SubdiffContinuousFor φ x₀ v₀)
    (hψ : ∀ᶠ x in 𝓝 x₀, ψ x = φ x) : SubdiffContinuousFor ψ x₀ v₀ := by
  classical
  obtain ⟨U, hUsub, hUo, hx₀U⟩ := _root_.eventually_nhds_iff.1 hψ
  have hS : ∀ x ∈ U, subdiff ψ x = subdiff φ x := fun x hx ↦
    subdiff_congr (eventually_of_mem (hUo.mem_nhds hx) hUsub)
  refine ⟨by rw [hS x₀ hx₀U]; exact h.1, fun x v hx hv hvx ↦ ?_⟩
  have hev : ∀ᶠ k in atTop, x k ∈ U := hx.eventually (hUo.mem_nhds hx₀U)
  have h1 := h.2 (fun k ↦ if x k ∈ U then x k else x₀) (fun k ↦ if x k ∈ U then v k else v₀)
    (hx.congr' (hev.mono fun k hk ↦ (if_pos hk).symm))
    (hv.congr' (hev.mono fun k hk ↦ (if_pos hk).symm)) (fun k ↦ by
      by_cases hk : x k ∈ U
      · rw [if_pos hk, if_pos hk, ← hS _ hk]; exact hvx k
      · rw [if_neg hk, if_neg hk]; exact h.1)
  rw [hUsub x₀ hx₀U]
  refine h1.congr' (hev.mono fun k hk ↦ ?_)
  show φ (if x k ∈ U then x k else x₀) = ψ (x k)
  rw [if_pos hk, hUsub _ hk]

/-- A prox-regular function agrees near `x̄` with an l.s.c. and prox-bounded function, namely `φ`
plus the indicator of a small closed ball around `x̄`. -/
theorem ProxRegularFor.exists_localization (hφ : ProxRegularFor φ x₀ v₀) :
    ∃ ρ > (0 : ℝ), ∃ ψ : E → EReal, (∀ x ∈ ball x₀ ρ, ψ x = φ x) ∧
      (∀ x, LowerSemicontinuousAt ψ x) ∧
      ∃ a b : ℝ, ∀ x, ((a - b * ‖x - x₀‖ ^ 2 : ℝ) : EReal) ≤ ψ x := by
  classical
  obtain ⟨δl, hδl, Hlsc⟩ := Metric.eventually_nhds_iff.1 hφ.2.1
  obtain ⟨r₀, hr₀, ε₀, hε₀, α, hα, Hprox⟩ := hφ.mem_proxSubdiff
  obtain ⟨ρ, hρ, hρl, hρ0⟩ : ∃ ρ > (0 : ℝ), ρ < δl ∧ ρ ≤ ε₀ :=
    ⟨min (δl / 2) ε₀, lt_min (half_pos hδl) hε₀,
      (min_le_left _ _).trans_lt (half_lt_self hδl), min_le_right _ _⟩
  obtain ⟨ψ, hψ_def⟩ : ∃ ψ : E → EReal, ψ = fun x ↦ if x ∈ closedBall x₀ ρ then φ x else ⊤ :=
    ⟨_, rfl⟩
  have hψeq : ∀ x ∈ closedBall x₀ ρ, ψ x = φ x := fun x hx ↦ by rw [hψ_def]; exact if_pos hx
  have hψtop : ∀ x ∉ closedBall x₀ ρ, ψ x = ⊤ := fun x hx ↦ by rw [hψ_def]; exact if_neg hx
  refine ⟨ρ, hρ, ψ, fun x hx ↦ hψeq x (ball_subset_closedBall hx), ?_,
    r₀ - ‖v₀‖ * ρ - α / 2 * ρ ^ 2, 0, fun x ↦ ?_⟩
  · intro y c hc
    by_cases hy : y ∈ closedBall x₀ ρ
    · rw [hψeq y hy] at hc
      have hyl : dist y x₀ < δl := (mem_closedBall.1 hy).trans_lt hρl
      filter_upwards [Hlsc hyl c hc] with z hz
      by_cases hz' : z ∈ closedBall x₀ ρ
      · rwa [hψeq z hz']
      · rw [hψtop z hz']; exact hz.trans_le le_top
    · rw [hψtop y hy] at hc
      filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hy] with z hz
      rw [hψtop z hz]; exact hc
  · by_cases hx : x ∈ closedBall x₀ ρ
    · rw [hψeq x hx]
      have hxn : ‖x - x₀‖ ≤ ρ := by rw [← dist_eq_norm]; exact mem_closedBall.1 hx
      refine le_trans (EReal.coe_le_coe_iff.2 ?_) (Hprox x (hxn.trans hρ0))
      have h1 : |v₀ (x - x₀)| ≤ ‖v₀‖ * ‖x - x₀‖ := by
        simpa [Real.norm_eq_abs] using v₀.le_opNorm (x - x₀)
      have h2 : ‖v₀‖ * ‖x - x₀‖ ≤ ‖v₀‖ * ρ := mul_le_mul_of_nonneg_left hxn (norm_nonneg v₀)
      have h3 : ‖x - x₀‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxn 2
      have h4 := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ α / 2)
      linarith [neg_abs_le (v₀ (x - x₀))]
    · rw [hψtop x hx]; exact le_top

end Local

/-! ### Proto-differentiability of the subgradient mapping -/

section Main

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {φ : E → EReal} {x₀ : E}

/-- For `φ` l.s.c., prox-bounded and continuously prox-regular at `x̄` for `v̄ = ⟨g, ·⟩` and all
small `λ > 0`, the proximal mapping `P_λφ` is single-valued and Lipschitz around `x̄ + λg`, and
near `(x̄, g)` one has `⟨y, ·⟩ ∈ ∂φ(x)` iff `x = P_λφ(x + λy)`. -/
theorem ContinuouslyProxRegularFor.eventually_mem_subdiff_iff {g : E}
    (hφ : ContinuouslyProxRegularFor φ x₀ (toDual ℝ E g))
    (hlsc : ∀ x, LowerSemicontinuousAt φ x)
    (hbd : ∃ a b : ℝ, ∀ x, ((a - b * ‖x - x₀‖ ^ 2 : ℝ) : EReal) ≤ φ x) :
    ∃ l₀ > (0 : ℝ), ∀ l, 0 < l → l < l₀ → ∃ δ > (0 : ℝ), ∃ p : E → E,
      p (x₀ + l • g) = x₀ ∧
      (∀ u ∈ ball (x₀ + l • g) δ, proximalMap φ l u = {p u}) ∧
      LipschitzOnWith 2 p (ball (x₀ + l • g) δ) ∧
      ∀ᶠ q : E × E in 𝓝 (x₀, g),
        (toDual ℝ E q.2 ∈ subdiff φ q.1 ↔ q.1 = p (q.1 + l • q.2)) := by
  obtain ⟨hpr, hsc⟩ := hφ
  obtain ⟨r₀, hr₀, -⟩ := hpr.1
  obtain ⟨ε, hε, l₀, hl₀, H⟩ := hpr.exists_proximalMap hlsc hbd
  -- subdifferential continuity
  obtain ⟨r₁, hr₁, hcont⟩ : ∃ r₁ > (0 : ℝ), ∀ x (v : StrongDual ℝ E), ‖x - x₀‖ < r₁ →
      ‖v - toDual ℝ E g‖ < r₁ → v ∈ subdiff φ x → ∃ s : ℝ, φ x = s ∧ |s - r₀| < ε := by
    have ht := hsc.tendsto
    rw [hr₀] at ht
    have hI : Ioo ((r₀ - ε : ℝ) : EReal) ((r₀ + ε : ℝ) : EReal) ∈ 𝓝 ((r₀ : ℝ) : EReal) :=
      Ioo_mem_nhds (EReal.coe_lt_coe_iff.2 (by linarith)) (EReal.coe_lt_coe_iff.2 (by linarith))
    obtain ⟨O, hO, hO0, hOs⟩ := mem_nhdsWithin.1 (ht hI)
    obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.1 hO _ hO0
    refine ⟨r₁, hr₁, fun x v hx hv hvx ↦ ?_⟩
    have hmem : (x, v) ∈ O := hball (by
      rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm]; exact ⟨hx, hv⟩)
    obtain ⟨s, hs, hs1, hs2⟩ := exists_real_of_mem_Ioo (hOs ⟨hmem, hvx⟩)
    exact ⟨s, hs, abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩⟩
  refine ⟨l₀, hl₀, fun l hl hll ↦ ?_⟩
  obtain ⟨δ, hδ, p, hp0, hpU, hLip, hloc, huniq⟩ := H l hl hll
  refine ⟨δ, hδ, p, hp0, hpU, hLip, ?_⟩
  obtain ⟨τ, hτ, hτr, hτε⟩ : ∃ τ > (0 : ℝ), τ ≤ r₁ ∧ τ ≤ ε :=
    ⟨min r₁ ε, lt_min hr₁ hε, min_le_left _ _, min_le_right _ _⟩
  have hdual : ∀ y : E, ‖toDual ℝ E y - toDual ℝ E g‖ = dist y g := fun y ↦ by
    rw [← map_sub, LinearIsometryEquiv.norm_map, dist_eq_norm]
  have hWo : IsOpen {q : E × E | dist q.1 x₀ < τ ∧ dist q.2 g < τ ∧
      dist (q.1 + l • q.2) (x₀ + l • g) < δ} := by
    have c1 : Continuous fun q : E × E ↦ dist q.1 x₀ := by fun_prop
    have c2 : Continuous fun q : E × E ↦ dist q.2 g := by fun_prop
    have c3 : Continuous fun q : E × E ↦ dist (q.1 + l • q.2) (x₀ + l • g) := by fun_prop
    exact (isOpen_lt c1 continuous_const).inter
      ((isOpen_lt c2 continuous_const).inter (isOpen_lt c3 continuous_const))
  filter_upwards [hWo.mem_nhds (show (x₀, g) ∈ {q : E × E | dist q.1 x₀ < τ ∧ dist q.2 g < τ ∧
    dist (q.1 + l • q.2) (x₀ + l • g) < δ} from
      ⟨by simpa using hτ, by simpa using hτ, by simpa using hδ⟩)] with ⟨x, y⟩ ⟨hx1, hx2, hx3⟩
  have hx1' : dist x x₀ < τ := hx1
  have hx2' : dist y g < τ := hx2
  have hu : x + l • y ∈ ball (x₀ + l • g) δ := hx3
  have hxy : l⁻¹ • (x + l • y - x) = y := by
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hl.ne', one_smul]
  show toDual ℝ E y ∈ subdiff φ x ↔ x = p (x + l • y)
  constructor
  · intro hgr
    refine huniq _ hu x ?_
    rw [hxy]
    obtain ⟨s, hs, hsr⟩ := hcont x (toDual ℝ E y) (by rw [← dist_eq_norm]; linarith)
      (by rw [hdual]; linarith) hgr
    refine ⟨hgr, by rw [← dist_eq_norm]; linarith, by rw [hdual]; linarith, s, hs, ?_⟩
    rwa [hr₀, EReal.toReal_coe]
  · intro hxp
    have := (hloc _ hu).1
    rwa [← hxp, hxy] at this

/-- The linear isomorphism `(x, v) ↦ (x + λv, x)` of `E × E*` onto `E × E`, which maps the
graph of `∂φ` to the graph of `P_λφ` near the reference point. -/
noncomputable def proxGraphEquiv (l : ℝ) (hl : l ≠ 0) : (E × StrongDual ℝ E) ≃L[ℝ] (E × E) :=
  ContinuousLinearEquiv.equivOfInverse
    { toFun := fun q ↦ (q.1 + l • (toDual ℝ E).symm q.2, q.1)
      map_add' := fun a b ↦ Prod.ext (by simp [smul_add]; abel) (by simp)
      map_smul' := fun c a ↦ Prod.ext (by simp [smul_add, smul_comm l c]) (by simp)
      cont := (continuous_fst.add
        (((toDual ℝ E).symm.continuous.comp continuous_snd).const_smul l)).prodMk
          continuous_fst }
    { toFun := fun q ↦ (q.2, toDual ℝ E (l⁻¹ • (q.1 - q.2)))
      map_add' := fun a b ↦ Prod.ext (by simp) (by simp [smul_sub, smul_add]; abel)
      map_smul' := fun c a ↦ Prod.ext (by simp)
        (by simp [smul_sub, smul_comm l⁻¹ c])
      cont := continuous_snd.prodMk ((toDual ℝ E).continuous.comp
        ((continuous_fst.sub continuous_snd).const_smul l⁻¹)) }
    (fun q ↦ Prod.ext rfl (by
      show toDual ℝ E (l⁻¹ • (q.1 + l • (toDual ℝ E).symm q.2 - q.1)) = q.2
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hl, one_smul,
        LinearIsometryEquiv.apply_symm_apply]))
    (fun q ↦ Prod.ext (by
      show q.2 + l • (toDual ℝ E).symm (toDual ℝ E (l⁻¹ • (q.1 - q.2))) = q.1
      rw [LinearIsometryEquiv.symm_apply_apply, smul_smul, mul_inv_cancel₀ hl, one_smul,
        add_sub_cancel]) rfl)

theorem proxGraphEquiv_apply {l : ℝ} (hl : l ≠ 0) (q : E × StrongDual ℝ E) :
    proxGraphEquiv l hl q = (q.1 + l • (toDual ℝ E).symm q.2, q.1) := rfl

theorem proxGraphEquiv_symm_apply {l : ℝ} (hl : l ≠ 0) (q : E × E) :
    (proxGraphEquiv l hl).symm q = (q.2, toDual ℝ E (l⁻¹ • (q.1 - q.2))) := rfl

/-- If near `(x̄, g)` one has `⟨y, ·⟩ ∈ S(x)` iff `x = p(x + λy)`, then `S` is proto-differentiable
at `(x̄, ⟨g, ·⟩)` iff the graph of `p` is geometrically derivable at `(x̄ + λg, x̄)`. -/
theorem protoDifferentiableAt_iff_geometricallyDerivableAt_graph
    {S : E → Set (StrongDual ℝ E)} {p : E → E} {l : ℝ} (hl : l ≠ 0) {g : E}
    (hp0 : p (x₀ + l • g) = x₀)
    (hgraph : ∀ᶠ q : E × E in 𝓝 (x₀, g),
      (toDual ℝ E q.2 ∈ S q.1 ↔ q.1 = p (q.1 + l • q.2))) :
    ProtoDifferentiableAt S x₀ (toDual ℝ E g) ↔
      GeometricallyDerivableAt (graph fun u ↦ ({p u} : Set E)) (x₀ + l • g, x₀) := by
  have hmem : toDual ℝ E g ∈ S x₀ := hgraph.self_of_nhds.2 hp0.symm
  let e : (E × StrongDual ℝ E) ≃L[ℝ] (E × E) := proxGraphEquiv l hl
  have he : ∀ q : E × StrongDual ℝ E, e q = (q.1 + l • (toDual ℝ E).symm q.2, q.1) :=
    fun q ↦ rfl
  have hes : ∀ q : E × E, e.symm q = (q.2, toDual ℝ E (l⁻¹ • (q.1 - q.2))) := fun q ↦ rfl
  have he0 : e (x₀, toDual ℝ E g) = (x₀ + l • g, x₀) := by
    rw [he, LinearIsometryEquiv.symm_apply_apply]
  have hes0 : e.symm (x₀ + l • g, x₀) = (x₀, toDual ℝ E g) := by
    rw [hes]
    simp only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hl, one_smul]
  constructor
  · intro hproto
    have hc : Tendsto (fun q : E × E ↦ (q.2, l⁻¹ • (q.1 - q.2))) (𝓝 (x₀ + l • g, x₀))
        (𝓝 (x₀, g)) := by
      have : Continuous (fun q : E × E ↦ (q.2, l⁻¹ • (q.1 - q.2))) := by fun_prop
      have h := this.tendsto (x₀ + l • g, x₀)
      simp only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hl, one_smul] at h
      exact h
    obtain ⟨W, hW, hWloc⟩ := (hc.eventually hgraph).exists_mem
    refine GeometricallyDerivableAt.of_inter_eq_preimage (Φ := e.symm) (e := e.symm)
      (by rw [hes0]; exact hproto) hW ?_ e.symm.hasStrictFDerivAt
      (show x₀ ∈ ({p (x₀ + l • g)} : Set E) by rw [hp0]; exact mem_singleton _)
    ext q
    have h1 := hWloc q
    have h3 : q.2 + l • l⁻¹ • (q.1 - q.2) = q.1 := by
      rw [smul_smul, mul_inv_cancel₀ hl, one_smul, add_sub_cancel]
    rw [h3] at h1
    have h2 : q ∈ e.symm ⁻¹' graph S ↔ toDual ℝ E (l⁻¹ • (q.1 - q.2)) ∈ S q.2 := Iff.rfl
    have h4 : q ∈ (graph fun u ↦ ({p u} : Set E)) ↔ q.2 = p q.1 := Iff.rfl
    simp only [mem_inter_iff]
    rw [h2, h4]
    exact ⟨fun ⟨hq, hqW⟩ ↦ ⟨(h1 hqW).2 hq, hqW⟩, fun ⟨hq, hqW⟩ ↦ ⟨(h1 hqW).1 hq, hqW⟩⟩
  · intro hG
    have hc : Tendsto (fun q : E × StrongDual ℝ E ↦ (q.1, (toDual ℝ E).symm q.2))
        (𝓝 (x₀, toDual ℝ E g)) (𝓝 (x₀, g)) := by
      have : Continuous (fun q : E × StrongDual ℝ E ↦ (q.1, (toDual ℝ E).symm q.2)) :=
        continuous_fst.prodMk ((toDual ℝ E).symm.continuous.comp continuous_snd)
      have h := this.tendsto (x₀, toDual ℝ E g)
      simp only [LinearIsometryEquiv.symm_apply_apply] at h
      exact h
    obtain ⟨W, hW, hWloc⟩ := (hc.eventually hgraph).exists_mem
    refine GeometricallyDerivableAt.of_inter_eq_preimage (Φ := e) (e := e)
      (by rw [he0]; exact hG) hW ?_ e.hasStrictFDerivAt hmem
    ext q
    have h1 := hWloc q
    simp only [LinearIsometryEquiv.apply_symm_apply] at h1
    have h2 : q ∈ e ⁻¹' (graph fun u ↦ ({p u} : Set E)) ↔
        q.1 = p (q.1 + l • (toDual ℝ E).symm q.2) := Iff.rfl
    simp only [mem_inter_iff]
    rw [h2]
    exact ⟨fun ⟨hq, hqW⟩ ↦ ⟨(h1 hqW).1 hq, hqW⟩, fun ⟨hq, hqW⟩ ↦ ⟨(h1 hqW).2 hq, hqW⟩⟩

/-- [Mordukhovich 2024, Thm. 1.98], one implication for l.s.c. and prox-bounded functions. -/
theorem ContinuouslyProxRegularFor.protoDifferentiableAt_subdiff_of_lsc {g : E}
    (hφ : ContinuouslyProxRegularFor φ x₀ (toDual ℝ E g))
    (H : TwiceEpiDifferentiableAt φ x₀ (toDual ℝ E g))
    (hlsc : ∀ x, LowerSemicontinuousAt φ x)
    (hbd : ∃ a b : ℝ, ∀ x, ((a - b * ‖x - x₀‖ ^ 2 : ℝ) : EReal) ≤ φ x) :
    ProtoDifferentiableAt (subdiff φ) x₀ (toDual ℝ E g) := by
  obtain ⟨l₁, hl₁, H1⟩ := hφ.eventually_mem_subdiff_iff hlsc hbd
  obtain ⟨l₂, hl₂, H2⟩ := hφ.1.exists_tendsto_inv_smul_sub_proximalMap H hlsc hbd
  obtain ⟨l, hl_def⟩ : ∃ l, l = min l₁ l₂ / 2 := ⟨_, rfl⟩
  have hl : 0 < l := by rw [hl_def]; exact half_pos (lt_min hl₁ hl₂)
  have hll₁ : l < l₁ := by
    rw [hl_def]; linarith [min_le_left l₁ l₂, half_lt_self (lt_min hl₁ hl₂)]
  have hll₂ : l < l₂ := by
    rw [hl_def]; linarith [min_le_right l₁ l₂, half_lt_self (lt_min hl₁ hl₂)]
  obtain ⟨δ, hδ, p, hp0, hpU, hLip, hgraph⟩ := H1 l hl hll₁
  obtain ⟨D, -, hconv⟩ := H2 l hl hll₂
  -- the graph of `P_λφ` is geometrically derivable at `(x̄ + λg, x̄)`
  have hG : GeometricallyDerivableAt (graph fun u ↦ ({p u} : Set E)) (x₀ + l • g, x₀) := by
    have := geometricallyDerivableAt_graph_of_tendsto (f := p) (D := D)
      (ball_mem_nhds (x₀ + l • g) hδ) hLip (fun t ht w w₀ hw ↦ by
        rw [hp0]
        refine hconv t ht w (fun k ↦ p (x₀ + l • g + t k • w k)) w₀ hw ?_
        have hx : Tendsto (fun k ↦ x₀ + l • g + t k • w k) atTop (𝓝 (x₀ + l • g)) := by
          have := (tendsto_const_nhds (x := x₀ + l • g)).add
            ((tendsto_nhds_of_tendsto_nhdsWithin ht).smul hw)
          simpa using this
        filter_upwards [hx.eventually (ball_mem_nhds _ hδ)] with k hk
        rw [hpU _ hk]
        exact mem_singleton _)
    rwa [hp0] at this
  exact (protoDifferentiableAt_iff_geometricallyDerivableAt_graph hl.ne' hp0 hgraph).2 hG

/-- [Mordukhovich 2024, Thm. 1.98], one implication: if `φ` is continuously prox-regular at `x̄`
for `v̄` and twice epi-differentiable at `x̄` for `v̄`, then `∂φ` is proto-differentiable at
`(x̄, v̄)`. -/
theorem ContinuouslyProxRegularFor.protoDifferentiableAt_subdiff {g : E}
    (hφ : ContinuouslyProxRegularFor φ x₀ (toDual ℝ E g))
    (H : TwiceEpiDifferentiableAt φ x₀ (toDual ℝ E g)) :
    ProtoDifferentiableAt (subdiff φ) x₀ (toDual ℝ E g) := by
  obtain ⟨ρ, hρ, ψ, hψball, hψlsc, hψbd⟩ := hφ.1.exists_localization
  have hev : ∀ᶠ x in 𝓝 x₀, ψ x = φ x := eventually_of_mem (ball_mem_nhds x₀ hρ) hψball
  have hS : ∀ x ∈ ball x₀ ρ, subdiff ψ x = subdiff φ x := fun x hx ↦
    subdiff_congr (eventually_of_mem (isOpen_ball.mem_nhds hx) hψball)
  have hψ : ContinuouslyProxRegularFor ψ x₀ (toDual ℝ E g) :=
    ⟨hφ.1.congr hρ hψball, hφ.2.congr hev⟩
  have hG := hψ.protoDifferentiableAt_subdiff_of_lsc (H.congr hev) hψlsc hψbd
  refine GeometricallyDerivableAt.congr hG (eventuallyEq_set.2 ?_) hφ.1.1
  filter_upwards [(continuous_fst.tendsto (x₀, toDual ℝ E g)).eventually
    (ball_mem_nhds x₀ hρ)] with q hq
  show q.2 ∈ subdiff ψ q.1 ↔ q.2 ∈ subdiff φ q.1
  rw [hS q.1 hq]

end Main

end VariationalAnalysis
