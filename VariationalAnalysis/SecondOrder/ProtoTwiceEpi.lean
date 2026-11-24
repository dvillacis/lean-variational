/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis.SecondOrder.EnvelopeExpansion

/-!
# Proto-differentiability of the subgradient mapping implies twice epi-differentiability

This file completes the proof of the equivalence in [Mordukhovich 2024, Thm. 1.98]: a function
`φ` that is continuously prox-regular at `x̄` for `v̄` is twice epi-differentiable at `x̄` for `v̄`
if and only if `∂φ` is proto-differentiable at `(x̄, v̄)`.

## Main results

* `coeMulOrderIso`, `coe_mul_liminf`, `lowerSemicontinuous_liminf_prod`: auxiliary facts on
  multiplication by positive reals in `EReal` and on lower limits.
* `twiceEpiDifferentiableAt_zero_of_moreauEnvelope`: a function `ψ` with `ψ(0) = 0` and a
  quadratic minorant is twice epi-differentiable at `0` for `0` if, for all small `λ`, `P_λψ` is
  single-valued near `0` and directionally differentiable at `0`, and `t⁻²e_λψ(tw)` converges as
  `t ↓ 0`.
* `ContinuouslyProxRegularFor.twiceEpiDifferentiableAt_of_protoDifferentiableAt`: the converse
  implication of Thm. 1.98.
* `ContinuouslyProxRegularFor.twiceEpiDifferentiableAt_iff_protoDifferentiableAt`:
  [Mordukhovich 2024, Thm. 1.98], the equivalence.

## Implementation notes

By Lemma 1.94 the Moreau envelopes of `Δ²_tψ(0, 0)/2` are `t⁻²e_λψ(t·)`, which converge by
`SecondOrder/EnvelopeExpansion`. The limit is identified with the envelope of `d²ψ(0, 0)/2`, and
the converse part of Ex. 1.135 gives the epi-convergence of `Δ²_tψ(0, 0)/2`. The general case is
reduced to this one by the shift and tilt of `SecondOrder/TwiceEpiProx` and by localization.
-/

open Filter Topology Set Metric InnerProductSpace
open scoped NNReal RealInnerProductSpace Pointwise

namespace VariationalAnalysis

/-! ### Lower limits -/

section Liminf

/-- Multiplication by a positive real as an order isomorphism of `EReal`. -/
noncomputable def coeMulOrderIso (c : ℝ) (hc : 0 < c) : EReal ≃o EReal where
  toFun a := (c : EReal) * a
  invFun a := ((c⁻¹ : ℝ) : EReal) * a
  left_inv a := by
    change ((c⁻¹ : ℝ) : EReal) * ((c : EReal) * a) = a
    rw [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hc.ne', EReal.coe_one, one_mul]
  right_inv a := by
    change (c : EReal) * (((c⁻¹ : ℝ) : EReal) * a) = a
    rw [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hc.ne', EReal.coe_one, one_mul]
  map_rel_iff' := coe_mul_le_coe_mul_iff hc

/-- For `c > 0`, the order isomorphism `coeMulOrderIso c hc` is `a ↦ c * a`. -/
theorem coeMulOrderIso_apply {c : ℝ} (hc : 0 < c) (a : EReal) :
    coeMulOrderIso c hc a = (c : EReal) * a := rfl

/-- Multiplication by a positive real commutes with lower limits in `EReal`. -/
theorem coe_mul_liminf {ι : Type*} {F : Filter ι} {c : ℝ} (hc : 0 < c) (u : ι → EReal) :
    (c : EReal) * liminf u F = liminf (fun i ↦ (c : EReal) * u i) F :=
  (coeMulOrderIso c hc).liminf_apply

/-- If `a + b = c` in `EReal` with `b, c` real, then `a = c - b`. -/
theorem eq_coe_sub_of_add_coe_eq {a : EReal} {b c : ℝ} (h : a + (b : EReal) = c) :
    a = ((c - b : ℝ) : EReal) := by
  induction a using EReal.rec with
  | bot => rw [EReal.bot_add] at h; exact absurd h (EReal.bot_ne_coe c)
  | top => rw [EReal.top_add_coe] at h; exact absurd h (EReal.top_ne_coe c)
  | coe s =>
    rw [← EReal.coe_add, EReal.coe_eq_coe_iff] at h
    rw [EReal.coe_eq_coe_iff]
    linarith

/-- Adding a real constant commutes with infima in `EReal`. -/
theorem iInf_add_coe {ι : Type*} (g : ι → EReal) (c : ℝ) :
    ⨅ i, (g i + (c : EReal)) = (⨅ i, g i) + (c : EReal) := by
  refine le_antisymm ?_ (le_iInf fun i ↦ add_le_add (iInf_le g i) le_rfl)
  have h1 : ∀ i, (⨅ j, (g j + (c : EReal))) + ((-c : ℝ) : EReal) ≤ g i := fun i ↦ by
    have := add_le_add (iInf_le (fun j ↦ g j + (c : EReal)) i) (le_refl ((-c : ℝ) : EReal))
    rwa [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero] at this
  have h2 := add_le_add (le_iInf h1) (le_refl (c : EReal))
  rwa [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero] at h2

variable {E : Type*} [NormedAddCommGroup E]

/-- A lower limit over `t ↓ 0`, `w' → w` is a lower semicontinuous function of `w`. -/
theorem lowerSemicontinuous_liminf_prod (Φ : ℝ × E → EReal) :
    LowerSemicontinuous fun w ↦ liminf Φ (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) := by
  intro w c hc
  obtain ⟨c', hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.1 hc
  obtain ⟨pa, hpa, pb, hpb, H⟩ := eventually_prod_iff.1
    (eventually_lt_of_lt_liminf hc2 (by isBoundedDefault))
  filter_upwards [hpb.eventually_nhds] with w' hw'
  refine hc1.trans_le (le_liminf_of_le (by isBoundedDefault) ?_)
  exact (hpa.prod_mk hw').mono fun q hq ↦ (H hq.1 hq.2).le

end Liminf

/-! ### The normalized form -/

section Normalized

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **From Moreau envelopes to twice epi-differentiability.** Let `ψ(0) = 0` and
`ψ ≥ -(r/2)‖·‖²`. Assume that for all small `λ > 0` the proximal mapping `P_λψ = p` is
single-valued near `0` with `p(0) = 0`, directionally differentiable at `0`, the envelope `e_λψ`
is finite near `0`, and `t_k⁻²e_λψ(t_k w)` converges for all `t_k ↓ 0`. Then `ψ` is twice
epi-differentiable at `0` for `0`. -/
theorem twiceEpiDifferentiableAt_zero_of_moreauEnvelope {ψ : E → EReal} {r : ℝ}
    (h0 : ψ 0 = 0) (hr : 0 ≤ r) (hmin : ∀ x, ((-(r / 2) * ‖x‖ ^ 2 : ℝ) : EReal) ≤ ψ x)
    {l₀ : ℝ} (hl₀ : 0 < l₀)
    (H : ∀ l, 0 < l → l < l₀ → ∃ δ > (0 : ℝ), ∃ p D : E → E, ∃ Q : E → ℝ, p 0 = 0 ∧
      (∀ u ∈ ball (0 : E) δ, proximalMap ψ l u = {p u}) ∧
      (∀ u ∈ ball (0 : E) δ,
        (((moreauEnvelope ψ l u).toReal : ℝ) : EReal) = moreauEnvelope ψ l u) ∧
      (∀ w, HasDirDerivAt p 0 w (D w)) ∧
      ∀ t : ℕ → ℝ, Tendsto t atTop (𝓝[>] 0) → ∀ w,
        Tendsto (fun k ↦ ((t k) ^ 2)⁻¹ * (moreauEnvelope ψ l (t k • w)).toReal) atTop
          (𝓝 (Q w))) :
    TwiceEpiDifferentiableAt ψ 0 0 := by
  obtain ⟨f, hf_def⟩ : ∃ f : ℝ → E → EReal,
      f = fun t w ↦ ((1 / 2 : ℝ) : EReal) * secondDiffQuot ψ 0 0 t w := ⟨_, rfl⟩
  obtain ⟨φ₀, hφ₀_def⟩ : ∃ φ₀ : E → EReal,
      φ₀ = fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderiv ψ 0 0 w := ⟨_, rfl⟩
  have hf : ∀ t : ℝ, 0 < t → f t = fun w ↦ ((t⁻¹ ^ 2 : ℝ) : EReal) * ψ (t • w) := fun t ht ↦ by
    rw [hf_def]
    funext w
    exact half_secondDiffQuot_zero h0 ht.ne' w
  have hφ₀ : ∀ w, φ₀ w = liminf (fun q : ℝ × E ↦ f q.1 q.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) := fun w ↦ by
    rw [hφ₀_def, hf_def]
    exact coe_mul_liminf (by norm_num) _
  have hfmin : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ w : E, ((-(r / 2) * ‖w‖ ^ 2 : ℝ) : EReal) ≤ f t w := by
    rw [hf_def]
    exact eventually_half_secondDiffQuot_ge h0 hmin
  have hφ₀min : ∀ w : E, ((-(r / 2) * ‖w‖ ^ 2 : ℝ) : EReal) ≤ φ₀ w := fun w ↦ by
    rw [hφ₀]
    have ht : Tendsto (fun q : ℝ × E ↦ ((-(r / 2) * ‖q.2‖ ^ 2 : ℝ) : EReal))
        (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 ((-(r / 2) * ‖w‖ ^ 2 : ℝ) : EReal)) :=
      (continuous_coe_real_ereal.tendsto _).comp ((tendsto_snd.norm.pow 2).const_mul _)
    rw [← ht.liminf_eq]
    refine liminf_le_liminf ?_
    filter_upwards [(tendsto_fst (f := 𝓝[>] (0 : ℝ)) (g := 𝓝 w)).eventually hfmin] with q hq
    exact hq q.2
  have hlsc : LowerSemicontinuous φ₀ := by
    have : φ₀ = fun w ↦ liminf (fun q : ℝ × E ↦ f q.1 q.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) :=
      funext hφ₀
    rw [this]
    exact lowerSemicontinuous_liminf_prod _
  -- convergence of the Moreau envelopes
  have key : ∀ l ∈ Ioo 0 l₀, ∀ u,
      Tendsto (fun t ↦ moreauEnvelope (f t) l u) (𝓝[>] 0) (𝓝 (moreauEnvelope φ₀ l u)) := by
    rintro l ⟨hl, hll⟩ u
    obtain ⟨δ, hδ, p, D, Q, hp0, hpU, hfin, hD, hQ⟩ := H l hl hll
    have hball : ∀ t : ℕ → ℝ, Tendsto t atTop (𝓝[>] 0) →
        ∀ᶠ k in atTop, t k • u ∈ ball (0 : E) δ := fun t ht ↦ by
      have := (tendsto_nhds_of_tendsto_nhdsWithin ht).smul_const u
      rw [zero_smul] at this
      exact this.eventually (ball_mem_nhds _ hδ)
    have hE : ∀ t : ℕ → ℝ, Tendsto t atTop (𝓝[>] 0) →
        Tendsto (fun k ↦ moreauEnvelope (f (t k)) l u) atTop (𝓝 ((Q u : ℝ) : EReal)) := by
      intro t ht
      refine ((continuous_coe_real_ereal.tendsto (Q u)).comp (hQ t ht u)).congr' ?_
      filter_upwards [(tendsto_nhdsWithin_iff.1 ht).2, hball t ht] with k hk hkb
      change ((((t k) ^ 2)⁻¹ * (moreauEnvelope ψ l (t k • u)).toReal : ℝ) : EReal) =
        moreauEnvelope (f (t k)) l u
      rw [hf _ hk, moreauEnvelope_scale ψ hk, ← hfin _ hkb, ← EReal.coe_mul, inv_pow,
        EReal.toReal_coe]
    have hid : moreauEnvelope φ₀ l u = ((Q u : ℝ) : EReal) := by
      refine le_antisymm ?_ (le_iInf fun x ↦ ?_)
      · -- minimizers of the envelopes converge to `D u`
        obtain ⟨t, ht_def⟩ : ∃ t : ℕ → ℝ, t = fun k : ℕ ↦ 1 / ((k : ℝ) + 1) := ⟨_, rfl⟩
        have ht : Tendsto t atTop (𝓝[>] 0) := by
          rw [ht_def]
          exact tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
            Eventually.of_forall fun k ↦ show (0 : ℝ) < 1 / ((k : ℝ) + 1) from
              Nat.one_div_pos_of_nat⟩
        have hpos : ∀ᶠ k in atTop, 0 < t k := (tendsto_nhdsWithin_iff.1 ht).2
        have hx : Tendsto (fun k ↦ (t k)⁻¹ • p (t k • u)) atTop (𝓝 (D u)) := by
          have := (hD u).comp ht
          simpa [Function.comp_def, hp0] using this
        obtain ⟨b, hb⟩ : ∃ b : ℝ, b = (2 * l)⁻¹ * ‖D u - u‖ ^ 2 := ⟨_, rfl⟩
        have hbk : Tendsto (fun k ↦ (2 * l)⁻¹ * ‖(t k)⁻¹ • p (t k • u) - u‖ ^ 2) atTop
            (𝓝 b) := by
          rw [hb]; exact ((hx.sub_const u).norm.pow 2).const_mul _
        have hval : Tendsto (fun k ↦ f (t k) ((t k)⁻¹ • p (t k • u))) atTop
            (𝓝 ((Q u - b : ℝ) : EReal)) := by
          refine ((continuous_coe_real_ereal.tendsto _).comp
            ((hQ t ht u).sub hbk)).congr' ?_
          filter_upwards [hpos, hball t ht] with k hk hkb
          have hmem : (t k)⁻¹ • p (t k • u) ∈ proximalMap (f (t k)) l u := by
            rw [hf _ hk, proximalMap_scale ψ hk l u, hpU _ hkb, smul_set_singleton]
            exact mem_singleton _
          have h1 := moreauEnvelope_eq_of_mem_proximalMap hmem
          have h2 : moreauEnvelope (f (t k)) l u =
              ((((t k) ^ 2)⁻¹ * (moreauEnvelope ψ l (t k • u)).toReal : ℝ) : EReal) := by
            rw [hf _ hk, moreauEnvelope_scale ψ hk, ← hfin _ hkb, ← EReal.coe_mul, inv_pow,
              EReal.toReal_coe]
          rw [h2] at h1
          exact (eq_coe_sub_of_add_coe_eq h1.symm).symm
        have h3 : φ₀ (D u) ≤ ((Q u - b : ℝ) : EReal) := by
          rw [hφ₀, ← hval.liminf_eq]
          exact liminf_le_liminf_comp (ht.prodMk hx) _
        have h4 := add_le_add h3 (le_refl ((b : ℝ) : EReal))
        rw [← EReal.coe_add, sub_add_cancel] at h4
        refine le_trans (moreauEnvelope_le u (D u)) ?_
        change φ₀ (D u) + (((2 * l)⁻¹ * ‖D u - u‖ ^ 2 : ℝ) : EReal) ≤ _
        rw [← hb]
        exact h4
      · change ((Q u : ℝ) : EReal) ≤ φ₀ x + (((2 * l)⁻¹ * ‖x - u‖ ^ 2 : ℝ) : EReal)
        refine ereal_le_of_forall_real_gt fun c hc ↦ ?_
        have hc' : φ₀ x < ((c - (2 * l)⁻¹ * ‖x - u‖ ^ 2 : ℝ) : EReal) := by
          by_contra hn
          have := add_le_add (not_lt.1 hn) (le_refl ((((2 * l)⁻¹ * ‖x - u‖ ^ 2 : ℝ)) : EReal))
          rw [← EReal.coe_add, sub_add_cancel] at this
          exact (not_le.2 hc) this
        rw [hφ₀] at hc'
        obtain ⟨q, hq, hlt⟩ := exists_seq_forall_of_frequently
          (frequently_lt_of_liminf_lt (by isBoundedDefault) hc')
        have ht : Tendsto (fun k ↦ (q k).1) atTop (𝓝[>] 0) := tendsto_fst.comp hq
        have hx : Tendsto (fun k ↦ (q k).2) atTop (𝓝 x) := tendsto_snd.comp hq
        have hR : Tendsto (fun k ↦ ((c - (2 * l)⁻¹ * ‖x - u‖ ^ 2 +
            (2 * l)⁻¹ * ‖(q k).2 - u‖ ^ 2 : ℝ) : EReal)) atTop
            (𝓝 ((c - (2 * l)⁻¹ * ‖x - u‖ ^ 2 + (2 * l)⁻¹ * ‖x - u‖ ^ 2 : ℝ) : EReal)) :=
          (continuous_coe_real_ereal.tendsto _).comp
            (tendsto_const_nhds.add (((hx.sub_const u).norm.pow 2).const_mul _))
        rw [sub_add_cancel] at hR
        refine le_of_tendsto_of_tendsto' (hE _ ht) hR fun k ↦ ?_
        refine (moreauEnvelope_le u (q k).2).trans ?_
        change f (q k).1 (q k).2 + (((2 * l)⁻¹ * ‖(q k).2 - u‖ ^ 2 : ℝ) : EReal) ≤ _
        rw [EReal.coe_add]
        exact add_le_add (hlt k).le le_rfl
    rw [hid]
    exact tendsto_of_seq_tendsto fun t ht ↦ hE t ht
  have hepi := (epiTendsto_of_tendsto_moreauEnvelope hr hfmin hφ₀min hlsc hl₀ key).coe_mul
    (c := 2) two_pos
  have htwo : ∀ a : EReal, ((2 : ℝ) : EReal) * (((1 / 2 : ℝ) : EReal) * a) = a := fun a ↦ by
    rw [← mul_assoc, ← EReal.coe_mul]
    norm_num
  have e1 : (fun (t : ℝ) (w : E) ↦ ((2 : ℝ) : EReal) * f t w) = secondDiffQuot ψ 0 0 := by
    funext t w
    rw [hf_def]
    exact htwo _
  have e2 : (fun w : E ↦ ((2 : ℝ) : EReal) * φ₀ w) = secondSubderiv ψ 0 0 := by
    funext w
    rw [hφ₀_def]
    exact htwo _
  rw [e1, e2] at hepi
  exact twiceEpiDifferentiableAt_iff_epiTendsto.2 ⟨⟨0, by rw [h0, EReal.coe_zero]⟩, hepi⟩

end Normalized

/-! ### Prox-regular functions -/

section Main

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {φ : E → EReal} {x₀ : E}

/-- [Mordukhovich 2024, Thm. 1.98], the converse implication for l.s.c. and prox-bounded
functions. -/
theorem ContinuouslyProxRegularFor.twiceEpiDifferentiableAt_of_lsc {g : E}
    (hφ : ContinuouslyProxRegularFor φ x₀ (toDual ℝ E g))
    (hproto : ProtoDifferentiableAt (subdiff φ) x₀ (toDual ℝ E g))
    (hlsc : ∀ x, LowerSemicontinuousAt φ x)
    (hbd : ∃ a b : ℝ, ∀ x, ((a - b * ‖x - x₀‖ ^ 2 : ℝ) : EReal) ≤ φ x) :
    TwiceEpiDifferentiableAt φ x₀ (toDual ℝ E g) := by
  obtain ⟨r₀, hr₀, -⟩ := hφ.1.1
  obtain ⟨R, hR, hmin⟩ := exists_shiftTilt_ge hφ.1.mem_proxSubdiff hbd
  obtain ⟨l₀, hl₀, H⟩ := hφ.exists_tendsto_moreauEnvelope_second_quot hproto hlsc hbd
  obtain ⟨ψ, hψ⟩ : ∃ ψ : E → EReal, ψ = shiftTilt φ x₀ g := ⟨_, rfl⟩
  have hψ0 : ψ 0 = 0 := by rw [hψ]; exact shiftTilt_zero hr₀
  have hq : ∀ t w, secondDiffQuot ψ 0 0 t w = secondDiffQuot φ x₀ (toDual ℝ E g) t w := by
    rw [hψ]; exact secondDiffQuot_shiftTilt hr₀
  have hsub : ∀ w, secondSubderiv ψ 0 0 w = secondSubderiv φ x₀ (toDual ℝ E g) w := fun w ↦ by
    simp only [secondSubderiv, hq]
  have Hψ : TwiceEpiDifferentiableAt ψ 0 0 := by
    refine twiceEpiDifferentiableAt_zero_of_moreauEnvelope hψ0 hR (by rw [hψ]; exact hmin) hl₀
      fun l hl hll ↦ ?_
    obtain ⟨δ, hδ, p, D, hp0, hpU, hfin, hD, hexp⟩ := H l hl hll
    have hmem : ∀ {u x : E},
        x ∈ proximalMap ψ l u ↔ x₀ + x ∈ proximalMap φ l (x₀ + u + l • g) := by
      rw [hψ]; exact mem_proximalMap_shiftTilt_iff hl.ne'
    have hobj : ∀ u x : E, proxObjective ψ l u x =
        proxObjective φ l (x₀ + u + l • g) (x₀ + x) +
          ((-((φ x₀).toReal + ⟪g, u⟫_ℝ + l / 2 * ‖g‖ ^ 2) : ℝ) : EReal) := by
      rw [hψ]; exact proxObjective_shiftTilt φ x₀ g hl.ne'
    have hcomm : ∀ u : E, x₀ + u + l • g = x₀ + l • g + u := fun u ↦ by abel
    have hin : ∀ u ∈ ball (0 : E) δ, x₀ + l • g + u ∈ ball (x₀ + l • g) δ := fun u hu ↦ by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact mem_ball_zero_iff.1 hu
    have henv : ∀ u, moreauEnvelope ψ l u = moreauEnvelope φ l (x₀ + l • g + u) +
        ((-((φ x₀).toReal + ⟪g, u⟫_ℝ + l / 2 * ‖g‖ ^ 2) : ℝ) : EReal) := fun u ↦ by
      change (⨅ x, proxObjective ψ l u x) = (⨅ y, proxObjective φ l (x₀ + l • g + u) y) + _
      simp only [hobj, hcomm]
      rw [iInf_add_coe]
      congr 1
      exact (show Function.Surjective fun x : E ↦ x₀ + x from
        fun y ↦ ⟨y - x₀, add_sub_cancel _ _⟩).iInf_comp
          (fun y ↦ proxObjective φ l (x₀ + l • g + u) y)
    have htoReal : ∀ u ∈ ball (0 : E) δ, (moreauEnvelope ψ l u).toReal =
        (moreauEnvelope φ l (x₀ + l • g + u)).toReal -
          ((φ x₀).toReal + ⟪g, u⟫_ℝ + l / 2 * ‖g‖ ^ 2) := fun u hu ↦ by
      rw [henv, ← hfin _ (hin u hu), ← EReal.coe_add, EReal.toReal_coe, EReal.toReal_coe]
      ring
    obtain ⟨p', hp'⟩ : ∃ p' : E → E, p' = fun u ↦ p (x₀ + l • g + u) - x₀ := ⟨_, rfl⟩
    have hp'0 : p' 0 = 0 := by rw [hp']; simp only [add_zero, hp0, sub_self]
    have hp'U : ∀ u ∈ ball (0 : E) δ, proximalMap ψ l u = {p' u} := fun u hu ↦ by
      ext x
      rw [hmem, hcomm, hpU _ (hin u hu), mem_singleton_iff, mem_singleton_iff, hp',
        eq_sub_iff_add_eq']
    have h0mem : (0 : E) ∈ ball (0 : E) δ := mem_ball_self hδ
    have hψe0 : moreauEnvelope ψ l 0 = 0 := by
      have h1 : (0 : E) ∈ proximalMap ψ l 0 := by
        rw [hp'U 0 h0mem, hp'0]; exact mem_singleton _
      rw [moreauEnvelope_eq_of_mem_proximalMap h1]
      change ψ 0 + (((2 * l)⁻¹ * ‖(0 : E) - 0‖ ^ 2 : ℝ) : EReal) = 0
      simp [hψ0]
    have hEū : (moreauEnvelope φ l (x₀ + l • g)).toReal = (φ x₀).toReal + l / 2 * ‖g‖ ^ 2 := by
      have := htoReal 0 h0mem
      rw [hψe0, EReal.toReal_zero, add_zero, inner_zero_right] at this
      linarith
    refine ⟨δ, hδ, p', D, fun w ↦ (2 * l)⁻¹ * (‖w‖ ^ 2 - ⟪D w, w⟫_ℝ), hp'0, hp'U,
      fun u hu ↦ ?_, fun w ↦ ?_, fun t ht w ↦ ?_⟩
    · rw [henv, ← hfin _ (hin u hu), ← EReal.coe_add, EReal.toReal_coe]
    · refine Tendsto.congr (fun s ↦ ?_) (hD w)
      simp only [hp', zero_add, add_zero, sub_sub_sub_cancel_right]
    · refine (hexp t ht (fun _ ↦ w) w tendsto_const_nhds).congr' ?_
      have hb : ∀ᶠ k in atTop, t k • w ∈ ball (0 : E) δ := by
        have := (tendsto_nhds_of_tendsto_nhdsWithin ht).smul_const w
        rw [zero_smul] at this
        exact this.eventually (ball_mem_nhds _ hδ)
      filter_upwards [hb] with k hk
      rw [htoReal _ hk, hEū, real_inner_smul_right]
      ring
  obtain ⟨-, H2⟩ := Hψ
  refine ⟨⟨r₀, hr₀⟩, ?_⟩
  simp only [hq, hsub] at H2
  exact H2

/-- [Mordukhovich 2024, Thm. 1.98], the converse implication: if `φ` is continuously prox-regular
at `x̄` for `v̄` and `∂φ` is proto-differentiable at `(x̄, v̄)`, then `φ` is twice
epi-differentiable at `x̄` for `v̄`. -/
theorem ContinuouslyProxRegularFor.twiceEpiDifferentiableAt_of_protoDifferentiableAt {g : E}
    (hφ : ContinuouslyProxRegularFor φ x₀ (toDual ℝ E g))
    (hproto : ProtoDifferentiableAt (subdiff φ) x₀ (toDual ℝ E g)) :
    TwiceEpiDifferentiableAt φ x₀ (toDual ℝ E g) := by
  obtain ⟨ρ, hρ, ψ, hψball, hψlsc, hψbd⟩ := hφ.1.exists_localization
  have hev : ∀ᶠ x in 𝓝 x₀, ψ x = φ x := eventually_of_mem (ball_mem_nhds x₀ hρ) hψball
  have hS : ∀ x ∈ ball x₀ ρ, subdiff ψ x = subdiff φ x := fun x hx ↦
    subdiff_congr (eventually_of_mem (isOpen_ball.mem_nhds hx) hψball)
  have hψ : ContinuouslyProxRegularFor ψ x₀ (toDual ℝ E g) :=
    ⟨hφ.1.congr hρ hψball, hφ.2.congr hev⟩
  have hprotoψ : ProtoDifferentiableAt (subdiff ψ) x₀ (toDual ℝ E g) := by
    refine GeometricallyDerivableAt.congr hproto (eventuallyEq_set.2 ?_) hψ.1.1
    filter_upwards [(continuous_fst.tendsto (x₀, toDual ℝ E g)).eventually
      (ball_mem_nhds x₀ hρ)] with q hq
    change q.2 ∈ subdiff φ q.1 ↔ q.2 ∈ subdiff ψ q.1
    rw [hS q.1 hq]
  exact (hψ.twiceEpiDifferentiableAt_of_lsc hprotoψ hψlsc hψbd).congr
    (hev.mono fun x hx ↦ hx.symm)

/-- **Twice epi-differentiability and proto-differentiability** [Mordukhovich 2024, Thm. 1.98]:
a function `φ` continuously prox-regular at `x̄` for `v̄` is twice epi-differentiable at `x̄` for
`v̄` if and only if `∂φ` is proto-differentiable at `(x̄, v̄)`. -/
theorem ContinuouslyProxRegularFor.twiceEpiDifferentiableAt_iff_protoDifferentiableAt {g : E}
    (hφ : ContinuouslyProxRegularFor φ x₀ (toDual ℝ E g)) :
    TwiceEpiDifferentiableAt φ x₀ (toDual ℝ E g) ↔
      ProtoDifferentiableAt (subdiff φ) x₀ (toDual ℝ E g) :=
  ⟨hφ.protoDifferentiableAt_subdiff, hφ.twiceEpiDifferentiableAt_of_protoDifferentiableAt⟩

end Main

end VariationalAnalysis
