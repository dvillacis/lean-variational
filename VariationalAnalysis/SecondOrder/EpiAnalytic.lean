/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis.SecondOrder.EpiConvergence
import VariationalAnalysis.SecondOrder.Moreau

/-!
# Analytic descriptions of epi-convergence and proto-differentiability

This file formalizes the exercises of [Mordukhovich 2024, Sect. 1.6] that describe set and
epi-convergence analytically. They are used in the proof of [Mordukhovich 2024, Thm. 1.98].

## Main results

* `epiTendsto_iff`, `epiTendsto_atTop_iff`: the analytic description of epi-convergence
  [Mordukhovich 2024, Ex. 1.133], along a countably generated filter and for sequences.
* `convex_innerLimit`, `EpiTendsto.convex_epi`: inner limits of convex sets and epi-limits of
  convex functions are convex [Mordukhovich 2024, Ex. 1.134(i), (iii)].
* `moreauEnvelope_anti`, `tendsto_moreauEnvelope_nhdsGT_zero`: `e_λφ(u) ↑ φ(u)` as `λ ↓ 0` for a
  nonnegative function `φ` that is l.s.c. at `u` [Mordukhovich 2024, Ex. 1.136].
* `EpiTendsto.tendsto_moreauEnvelope`, `epiTendsto_of_tendsto_moreauEnvelope`: for nonnegative
  functions, epi-convergence is equivalent to the convergence of the Moreau envelopes for all
  small `λ > 0` [Mordukhovich 2024, Ex. 1.135(i)].
* `geometricallyDerivableAt_iff_isSetLimit`, `protoDifferentiableAt_iff_isSetLimit`:
  proto-differentiability of `F` at `(x̄, ȳ)` is the set convergence of `(gph F - (x̄, ȳ))/t` to
  the tangent cone as `t ↓ 0` [Mordukhovich 2024, Ex. 1.139(iii)].

## Implementation notes

* Epigraphs are subsets of `E × ℝ`, so a point `x` with `φ₀(x) = -∞` needs a diagonal argument
  in the recovery part of Ex. 1.133 (`exists_diag_seq`).
* In Ex. 1.135(i) the uniform convergence on bounded sets is stated as continuous convergence,
  `e_λφ_i(u') → e_λφ₀(u)` as `i → l`, `u' → u`, with values in `EReal`; this needs a proper
  (finite-dimensional) space. Neither direction needs the functions to be proper, and only the
  converse needs `φ₀` to be l.s.c.
* Along a general filter `l` the lower estimate of Ex. 1.133 is a lower limit along `l ×ˢ 𝓝 x`,
  and the recovery sequence is asked along every sequence in `l`, as in `innerLimit`.
-/

open Filter Topology Set Metric
open scoped Pointwise

namespace VariationalAnalysis

/-! ### Auxiliary sequences -/

section Aux

/-- A convergent sequence indexed by a strictly increasing `ψ` extends to a convergent sequence
indexed by `ℕ`. -/
theorem exists_seq_extend_of_strictMono {X : Type*} [TopologicalSpace X] {ψ : ℕ → ℕ}
    (hψ : StrictMono ψ) {v : ℕ → X} {y : X} (hv : Tendsto v atTop (𝓝 y)) :
    ∃ x : ℕ → X, Tendsto x atTop (𝓝 y) ∧ ∀ j, x (ψ j) = v j := by
  classical
  refine ⟨fun k ↦ if h : ∃ j, ψ j = k then v h.choose else y, ?_, fun j ↦ ?_⟩
  · refine tendsto_nhds.2 fun U hU hy ↦ ?_
    obtain ⟨J, hJ⟩ := eventually_atTop.1 (hv.eventually_mem (hU.mem_nhds hy))
    filter_upwards [eventually_ge_atTop (ψ J)] with k hk
    show (if h : ∃ j, ψ j = k then v h.choose else y) ∈ U
    split_ifs with h
    · have h1 : ψ h.choose = k := h.choose_spec
      exact hJ _ (hψ.le_iff_le.1 (by rw [h1]; exact hk))
    · exact hy
  · have h : ∃ i, ψ i = ψ j := ⟨j, rfl⟩
    have h1 : h.choose = j := hψ.injective h.choose_spec
    simp only [dif_pos h, h1]

/-- A diagonal sequence: if `v n k → x` as `k → ∞` for each `n` and `P n k` holds for large `k`,
then some `n(k) → ∞` has `v (n k) k → x` and `P (n k) k` for large `k`. -/
theorem exists_diag_seq {X : Type*} [PseudoMetricSpace X] {x : X} {v : ℕ → ℕ → X}
    (hv : ∀ n, Tendsto (v n) atTop (𝓝 x)) {P : ℕ → ℕ → Prop}
    (hP : ∀ n, ∀ᶠ k in atTop, P n k) :
    ∃ n : ℕ → ℕ, Tendsto n atTop atTop ∧ Tendsto (fun k ↦ v (n k) k) atTop (𝓝 x) ∧
      ∀ᶠ k in atTop, P (n k) k := by
  classical
  have hQ : ∀ n, ∃ N, ∀ k ≥ N, P n k ∧ dist (v n k) x < 1 / ((n : ℝ) + 1) := fun n ↦
    eventually_atTop.1 ((hP n).and (Metric.tendsto_nhds.1 (hv n) _ (by positivity)))
  choose N hN using hQ
  let n : ℕ → ℕ := fun k ↦ Nat.findGreatest (fun m ↦ ∀ i ≤ m, N i ≤ k) k
  have hspec : ∀ k, N 0 ≤ k → N (n k) ≤ k := by
    intro k hk
    have h0 : ∀ i ≤ 0, N i ≤ k := fun i hi ↦ by rwa [Nat.le_zero.1 hi]
    exact Nat.findGreatest_spec (P := fun m ↦ ∀ i ≤ m, N i ≤ k) (Nat.zero_le k) h0 _ le_rfl
  have hge : ∀ m, ∀ᶠ k in atTop, m ≤ n k := by
    intro m
    filter_upwards [eventually_ge_atTop ((Finset.range (m + 1)).sup N),
      eventually_ge_atTop m] with k hk hkm
    refine Nat.le_findGreatest hkm fun i hi ↦ le_trans ?_ hk
    exact Finset.le_sup (f := N) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  refine ⟨n, tendsto_atTop.2 hge, Metric.tendsto_nhds.2 fun ε hε ↦ ?_, ?_⟩
  · obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    filter_upwards [hge m, eventually_ge_atTop (N 0)] with k hk hk0
    have h1 := (hN (n k) k (hspec k hk0)).2
    have h2 : 1 / ((n k : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      have : (m : ℝ) ≤ n k := by exact_mod_cast hk
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  · filter_upwards [eventually_ge_atTop (N 0)] with k hk0
    exact (hN (n k) k (hspec k hk0)).1

/-- Lower limits decrease along the target filter of a map. -/
theorem liminf_le_liminf_comp {α β : Type*} {l : Filter α} {l' : Filter β} {g : α → β}
    (hg : Tendsto g l l') (u : β → EReal) : liminf u l' ≤ liminf (u ∘ g) l :=
  (liminf_le_liminf_of_le hg : liminf u l' ≤ liminf u (map g l))

/-- Upper limits increase along the target filter of a map. -/
theorem limsup_comp_le_limsup {α β : Type*} {l : Filter α} {l' : Filter β} {g : α → β}
    (hg : Tendsto g l l') (u : β → EReal) : limsup (u ∘ g) l ≤ limsup u l' :=
  (limsup_le_limsup_of_le hg : limsup u (map g l) ≤ limsup u l')

end Aux

/-! ### Set limits -/

section SetLimit

variable {ι X : Type*} [TopologicalSpace X]

/-- The inner limit is contained in the outer limit along a nontrivial countably generated
filter. -/
theorem innerLimit_subset_outerLimit (l : Filter ι) [l.IsCountablyGenerated] [l.NeBot]
    (S : ι → Set X) : innerLimit l S ⊆ outerLimit l S := fun y hy ↦ by
  obtain ⟨a, ha⟩ := l.exists_seq_tendsto
  obtain ⟨v, hv, hS⟩ := hy a ha
  exact mem_outerLimit_of_eventually a v ha hv hS

/-- Set convergence in terms of two inclusions. -/
theorem isSetLimit_iff_subset {l : Filter ι} [l.IsCountablyGenerated] [l.NeBot] {S : ι → Set X}
    {S₀ : Set X} : IsSetLimit l S S₀ ↔ outerLimit l S ⊆ S₀ ∧ S₀ ⊆ innerLimit l S := by
  have hio := innerLimit_subset_outerLimit l S
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1.subset, h2.ge⟩
  · rintro ⟨ho, hi⟩
    exact ⟨ho.antisymm (hi.trans hio), (hio.trans ho).antisymm hi⟩

end SetLimit

section Convex

variable {ι X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The inner limit of convex sets is convex [Mordukhovich 2024, Ex. 1.134(i)]. -/
theorem convex_innerLimit {l : Filter ι} {S : ι → Set X} (h : ∀ᶠ i in l, Convex ℝ (S i)) :
    Convex ℝ (innerLimit l S) := by
  intro y hy z hz s t hs ht hst a ha
  obtain ⟨v, hv, hvS⟩ := hy a ha
  obtain ⟨w, hw, hwS⟩ := hz a ha
  refine ⟨fun k ↦ s • v k + t • w k, (hv.const_smul s).add (hw.const_smul t), ?_⟩
  filter_upwards [ha.eventually h, hvS, hwS] with k hk hvk hwk using hk hvk hwk hs ht hst

end Convex

/-! ### Exercise 1.133: the analytic description of epi-convergence -/

section Epi

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {l : Filter ι}
  {φ : ι → E → EReal} {φ₀ : E → EReal}

/-- The epi-limit of convex functions is convex [Mordukhovich 2024, Ex. 1.134(iii)]. -/
theorem EpiTendsto.convex_epi (h : EpiTendsto l φ φ₀)
    (hc : ∀ᶠ i in l, Convex ℝ ((φ i).Epi univ)) : Convex ℝ (φ₀.Epi univ) :=
  h.2 ▸ convex_innerLimit hc

omit [NormedSpace ℝ E] in
/-- The outer limit of the epigraphs lies in `epi φ₀` if and only if
`φ₀(x) ≤ lim inf φ_i(x')` as `i → l`, `x' → x`. -/
theorem outerLimit_epi_subset_iff [l.IsCountablyGenerated] :
    outerLimit l (fun i ↦ (φ i).Epi univ) ⊆ φ₀.Epi univ ↔
      ∀ x, φ₀ x ≤ liminf (fun p : ι × E ↦ φ p.1 p.2) (l ×ˢ 𝓝 x) := by
  constructor
  · intro h x
    by_contra hlt
    obtain ⟨c, hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.1 (not_le.1 hlt)
    obtain ⟨ns, hns, hlt'⟩ := exists_seq_forall_of_frequently
      (frequently_lt_of_liminf_lt (by isBoundedDefault) hc1)
    have hmem : (x, c) ∈ outerLimit l (fun i ↦ (φ i).Epi univ) :=
      ⟨fun k ↦ (ns k).1, fun k ↦ ((ns k).2, c), tendsto_fst.comp hns,
        (tendsto_snd.comp hns).prodMk_nhds tendsto_const_nhds,
        fun k ↦ ⟨mem_univ _, (hlt' k).le⟩⟩
    exact not_le.2 hc2 (h hmem).2
  · rintro h ⟨y, α⟩ ⟨a, v, ha, hv, hS⟩
    refine ⟨mem_univ _, ?_⟩
    have hv1 : Tendsto (fun k ↦ (v k).1) atTop (𝓝 y) := (continuous_fst.tendsto (y, α)).comp hv
    have hv2 : Tendsto (fun k ↦ (((v k).2 : ℝ) : EReal)) atTop (𝓝 (α : EReal)) :=
      (continuous_coe_real_ereal.tendsto _).comp ((continuous_snd.tendsto (y, α)).comp hv)
    calc φ₀ y ≤ liminf (fun p : ι × E ↦ φ p.1 p.2) (l ×ˢ 𝓝 y) := h y
      _ ≤ liminf (fun k ↦ φ (a k) (v k).1) atTop :=
        liminf_le_liminf_comp (ha.prodMk hv1) _
      _ ≤ liminf (fun k ↦ (((v k).2 : ℝ) : EReal)) atTop :=
        liminf_le_liminf (Eventually.of_forall fun k ↦ (hS k).2)
      _ = α := hv2.liminf_eq

omit [NormedSpace ℝ E] in
/-- `epi φ₀` lies in the inner limit of the epigraphs if and only if every point `x` has, along
every sequence `i_k → l`, a recovery sequence `x_k → x` with `lim sup φ_{i_k}(x_k) ≤ φ₀(x)`. -/
theorem epi_subset_innerLimit_iff :
    φ₀.Epi univ ⊆ innerLimit l (fun i ↦ (φ i).Epi univ) ↔
      ∀ x, ∀ a : ℕ → ι, Tendsto a atTop l → ∃ z : ℕ → E, Tendsto z atTop (𝓝 x) ∧
        limsup (fun k ↦ φ (a k) (z k)) atTop ≤ φ₀ x := by
  classical
  constructor
  · intro h x a ha
    rcases eq_or_ne (φ₀ x) ⊤ with hx | hxt
    · exact ⟨fun _ ↦ x, tendsto_const_nhds, hx ▸ le_top⟩
    rcases eq_or_ne (φ₀ x) ⊥ with hx | hxb
    · -- a diagonal sequence through the levels `-n`
      have hw : ∀ n : ℕ, ∃ w : ℕ → E × ℝ, Tendsto w atTop (𝓝 (x, -(n : ℝ))) ∧
          ∀ᶠ k in atTop, w k ∈ (φ (a k)).Epi univ := fun n ↦
        h (show (x, -(n : ℝ)) ∈ φ₀.Epi univ from ⟨mem_univ _, hx ▸ bot_le⟩) a ha
      choose w hw hwS using hw
      obtain ⟨n, hn, hz, hP⟩ := exists_diag_seq (v := fun n k ↦ (w n k).1)
        (P := fun n k ↦ φ (a k) (w n k).1 ≤ ((-(n : ℝ) + 1 : ℝ) : EReal))
        (fun n ↦ (continuous_fst.tendsto (x, -(n : ℝ))).comp (hw n)) (fun n ↦ by
          have h2 : ∀ᶠ k in atTop, (w n k).2 < -(n : ℝ) + 1 :=
            ((continuous_snd.tendsto (x, -(n : ℝ))).comp (hw n)).eventually_lt_const (by simp)
          filter_upwards [hwS n, h2] with k hk hk2
          exact hk.2.trans (EReal.coe_le_coe_iff.2 hk2.le))
      refine ⟨fun k ↦ (w (n k) k).1, hz, ?_⟩
      rw [hx, le_bot_iff, EReal.eq_bot_iff_forall_lt]
      intro c
      refine lt_of_le_of_lt (limsup_le_of_le (by isBoundedDefault) ?_)
        (EReal.coe_lt_coe_iff.2 (sub_one_lt c))
      filter_upwards [hP, hn.eventually_ge_atTop ⌈2 - c⌉₊] with k hk hkn
      refine hk.trans (EReal.coe_le_coe_iff.2 ?_)
      have h1 : 2 - c ≤ (n k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hkn)
      linarith
    · obtain ⟨r, hr⟩ : ∃ r : ℝ, φ₀ x = r := ⟨_, (EReal.coe_toReal hxt hxb).symm⟩
      obtain ⟨w, hw, hwS⟩ := h (show (x, r) ∈ φ₀.Epi univ from ⟨mem_univ _, hr.le⟩) a ha
      refine ⟨fun k ↦ (w k).1, (continuous_fst.tendsto (x, r)).comp hw, ?_⟩
      have hw2 : Tendsto (fun k ↦ (((w k).2 : ℝ) : EReal)) atTop (𝓝 (r : EReal)) :=
        (continuous_coe_real_ereal.tendsto _).comp ((continuous_snd.tendsto (x, r)).comp hw)
      calc limsup (fun k ↦ φ (a k) (w k).1) atTop
          ≤ limsup (fun k ↦ (((w k).2 : ℝ) : EReal)) atTop :=
            limsup_le_limsup (hwS.mono fun k hk ↦ hk.2)
        _ = r := hw2.limsup_eq
        _ = φ₀ x := hr.symm
  · rintro h ⟨x, α⟩ ⟨-, hα⟩ a ha
    obtain ⟨z, hz, hl⟩ := h x a ha
    have hev : ∀ ε > (0 : ℝ), ∀ᶠ k in atTop, φ (a k) (z k) < ((α + ε : ℝ) : EReal) := fun ε hε ↦
      eventually_lt_of_limsup_lt
        ((hl.trans hα).trans_lt (EReal.coe_lt_coe_iff.2 (lt_add_of_pos_right α hε)))
    let β : ℕ → ℝ := fun k ↦ if φ (a k) (z k) ≤ α then α else (φ (a k) (z k)).toReal
    have hβ : ∀ ε > (0 : ℝ), ∀ k, φ (a k) (z k) < ((α + ε : ℝ) : EReal) →
        φ (a k) (z k) ≤ β k ∧ α ≤ β k ∧ β k < α + ε := by
      intro ε hε k hk
      by_cases hc : φ (a k) (z k) ≤ α
      · have : β k = α := if_pos hc
        rw [this]
        exact ⟨hc, le_rfl, lt_add_of_pos_right α hε⟩
      · have hβk : β k = (φ (a k) (z k)).toReal := if_neg hc
        have hgt := not_le.1 hc
        obtain ⟨r, hr⟩ : ∃ r : ℝ, φ (a k) (z k) = r :=
          ⟨_, (EReal.coe_toReal hk.ne_top (bot_lt_iff_ne_bot.1 (bot_le.trans_lt hgt))).symm⟩
        rw [hβk, hr, EReal.toReal_coe]
        rw [hr] at hk hgt
        exact ⟨le_rfl, (EReal.coe_lt_coe_iff.1 hgt).le, EReal.coe_lt_coe_iff.1 hk⟩
    refine ⟨fun k ↦ (z k, β k), hz.prodMk_nhds (Metric.tendsto_nhds.2 fun ε hε ↦ ?_), ?_⟩
    · filter_upwards [hev ε hε] with k hk
      obtain ⟨-, h1, h2⟩ := hβ ε hε k hk
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    · filter_upwards [hev 1 one_pos] with k hk
      exact ⟨mem_univ _, (hβ 1 one_pos k hk).1⟩

omit [NormedSpace ℝ E] in
/-- **Analytic description of epi-convergence** [Mordukhovich 2024, Ex. 1.133] along a countably
generated filter: `φ_i →ₑ φ₀` if and only if at each `x` we have
`φ₀(x) ≤ lim inf φ_i(x')` as `i → l`, `x' → x`, and along every sequence `i_k → l` there is
`x_k → x` with `lim sup φ_{i_k}(x_k) ≤ φ₀(x)`. -/
theorem epiTendsto_iff [l.IsCountablyGenerated] [l.NeBot] :
    EpiTendsto l φ φ₀ ↔ ∀ x,
      φ₀ x ≤ liminf (fun p : ι × E ↦ φ p.1 p.2) (l ×ˢ 𝓝 x) ∧
      ∀ a : ℕ → ι, Tendsto a atTop l → ∃ z : ℕ → E, Tendsto z atTop (𝓝 x) ∧
        limsup (fun k ↦ φ (a k) (z k)) atTop ≤ φ₀ x := by
  rw [EpiTendsto, isSetLimit_iff_subset, outerLimit_epi_subset_iff, epi_subset_innerLimit_iff,
    forall_and]

omit [NormedSpace ℝ E] in
/-- **Analytic description of epi-convergence** [Mordukhovich 2024, Ex. 1.133]: `φ_k →ₑ φ₀` if
and only if at each `x` we have `lim inf φ_k(x_k) ≥ φ₀(x)` for every sequence `x_k → x` and
`lim sup φ_k(x_k) ≤ φ₀(x)` for some sequence `x_k → x`. -/
theorem epiTendsto_atTop_iff {φ : ℕ → E → EReal} :
    EpiTendsto atTop φ φ₀ ↔ ∀ x,
      (∀ z : ℕ → E, Tendsto z atTop (𝓝 x) → φ₀ x ≤ liminf (fun k ↦ φ k (z k)) atTop) ∧
      ∃ z : ℕ → E, Tendsto z atTop (𝓝 x) ∧ limsup (fun k ↦ φ k (z k)) atTop ≤ φ₀ x := by
  rw [epiTendsto_iff]
  refine forall_congr' fun x ↦ and_congr ⟨fun h z hz ↦ ?_, fun h ↦ ?_⟩ ⟨fun h ↦ ?_, fun h a ha ↦ ?_⟩
  · exact h.trans (liminf_le_liminf_comp (tendsto_id.prodMk hz) _)
  · by_contra hlt
    obtain ⟨c, hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.1 (not_le.1 hlt)
    obtain ⟨ns, hns, hlt'⟩ := exists_seq_forall_of_frequently
      (frequently_lt_of_liminf_lt (by isBoundedDefault) hc1)
    obtain ⟨ψ, hψ, hψ'⟩ := strictMono_subseq_of_tendsto_atTop (tendsto_fst.comp hns)
    obtain ⟨z, hz, hzv⟩ := exists_seq_extend_of_strictMono hψ'
      ((tendsto_snd.comp hns).comp hψ.tendsto_atTop)
    have h1 : liminf (fun k ↦ φ k (z k)) atTop ≤ c := by
      refine (liminf_le_liminf_comp hψ'.tendsto_atTop _).trans
        (liminf_le_of_frequently_le' (Eventually.of_forall fun j ↦ ?_).frequently)
      have := hzv j
      simp only [Function.comp_apply] at this ⊢
      rw [this]
      exact (hlt' (ψ j)).le
    exact not_le.2 hc2 ((h z hz).trans h1)
  · exact h id tendsto_id
  · obtain ⟨z, hz, hl⟩ := h
    exact ⟨z ∘ a, hz.comp ha, (limsup_comp_le_limsup ha fun k ↦ φ k (z k)).trans hl⟩

end Epi

/-! ### Exercise 1.136: Moreau envelopes as `λ ↓ 0` -/

section Moreau

variable {E : Type*} [NormedAddCommGroup E] {φ : E → EReal} {u : E}

/-- The Moreau envelope `e_λφ(u)` is nonincreasing in `λ > 0`. -/
theorem moreauEnvelope_anti {l₁ l₂ : ℝ} (hl : 0 < l₁) (h : l₁ ≤ l₂) :
    moreauEnvelope φ l₂ u ≤ moreauEnvelope φ l₁ u := by
  refine iInf_mono fun x ↦ add_le_add le_rfl (EReal.coe_le_coe_iff.2 ?_)
  exact mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) (by linarith)) (sq_nonneg _)

/-- **`λ`-convergence of Moreau envelopes** [Mordukhovich 2024, Ex. 1.136]: if `φ ≥ 0` is l.s.c.
at `u`, then `e_λφ(u) → φ(u)` as `λ ↓ 0`; the convergence is monotone by
`moreauEnvelope_anti`. -/
theorem tendsto_moreauEnvelope_nhdsGT_zero (hφ : ∀ x, 0 ≤ φ x)
    (hlsc : LowerSemicontinuousAt φ u) :
    Tendsto (fun l ↦ moreauEnvelope φ l u) (𝓝[>] 0) (𝓝 (φ u)) := by
  refine tendsto_order.2 ⟨fun c hc ↦ ?_, fun c hc ↦ Eventually.of_forall fun l ↦
    (moreauEnvelope_le_self (φ := φ) (l := l) u).trans_lt hc⟩
  obtain ⟨c', hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.1 hc
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hlsc _ hc2)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds
    (Iio_mem_nhds (show (0 : ℝ) < δ ^ 2 / (2 * (|c'| + 1)) by positivity))] with l hl hlt
  have hl : 0 < l := hl
  refine hc1.trans_le (le_iInf fun x ↦ ?_)
  show (c' : EReal) ≤ φ x + (((2 * l)⁻¹ * ‖x - u‖ ^ 2 : ℝ) : EReal)
  by_cases hx : dist x u < δ
  · exact (hball hx).le.trans (le_add_of_nonneg_right (EReal.coe_nonneg.2 (by positivity)))
  · refine le_trans (EReal.coe_le_coe_iff.2 ?_) (le_add_of_nonneg_left (hφ x))
    have hd : δ ≤ ‖x - u‖ := by rw [← dist_eq_norm]; exact not_lt.1 hx
    have hd2 : δ ^ 2 ≤ ‖x - u‖ ^ 2 := pow_le_pow_left₀ hδ.le hd 2
    have h1 : l * (2 * (|c'| + 1)) < δ ^ 2 := (lt_div_iff₀ (by positivity)).1 hlt
    have h2 : c' * l ≤ |c'| * l := mul_le_mul_of_nonneg_right (le_abs_self c') hl.le
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
    linarith

end Moreau

/-! ### Exercise 1.135(i): epi-convergence via Moreau envelopes -/

section MoreauEpi

/-- A diagonal choice of indices: if `P n k` holds for large `k` for each `n`, then some
`n(k) → ∞` has `P (n k) k` for large `k`. -/
theorem exists_diag_nat {P : ℕ → ℕ → Prop} (hP : ∀ n, ∀ᶠ k in atTop, P n k) :
    ∃ n : ℕ → ℕ, Tendsto n atTop atTop ∧ ∀ᶠ k in atTop, P (n k) k := by
  obtain ⟨n, hn, -, h⟩ := exists_diag_seq (x := (0 : ℝ)) (v := fun _ _ ↦ 0)
    (fun _ ↦ tendsto_const_nhds) hP
  exact ⟨n, hn, h⟩

/-- `a ≤ b` in `EReal` if `a ≤ c` for every real `c > b`. -/
theorem ereal_le_of_forall_real_gt {a b : EReal} (h : ∀ c : ℝ, b < c → a ≤ c) : a ≤ b := by
  by_contra hlt
  obtain ⟨c, hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.1 (not_le.1 hlt)
  exact not_le.2 hc2 (h c hc1)

variable {ι E : Type*} [NormedAddCommGroup E] {l : Filter ι} {φ : ι → E → EReal}
  {φ₀ : E → EReal}

/-- The sequential core of Ex. 1.135(i): the two conditions of Ex. 1.133 give the continuous
convergence of the Moreau envelopes of nonnegative functions. -/
theorem tendsto_moreauEnvelope_of_seq [ProperSpace E] {φ : ℕ → E → EReal} {m : ℝ}
    (hm : 0 < m) (hφ : ∀ k x, 0 ≤ φ k x)
    (hinf : ∀ x, ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ z : ℕ → E, Tendsto z atTop (𝓝 x) →
      φ₀ x ≤ liminf (fun j ↦ φ (ψ j) (z j)) atTop)
    (hsup : ∀ x, ∃ z : ℕ → E, Tendsto z atTop (𝓝 x) ∧
      limsup (fun k ↦ φ k (z k)) atTop ≤ φ₀ x)
    {u : ℕ → E} {u₀ : E} (hu : Tendsto u atTop (𝓝 u₀)) :
    Tendsto (fun k ↦ moreauEnvelope (φ k) m (u k)) atTop (𝓝 (moreauEnvelope φ₀ m u₀)) := by
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
  · -- lower estimate, by compactness of near-minimizers
    by_contra hlt
    obtain ⟨c, hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.1 (not_le.1 hlt)
    obtain ⟨ψ, hψ, hlt'⟩ := extraction_of_frequently_atTop
      (frequently_lt_of_liminf_lt (by isBoundedDefault) hc1)
    have hx : ∀ j, ∃ x, proxObjective (φ (ψ j)) m (u (ψ j)) x < c := fun j ↦ by
      have h : (⨅ x, proxObjective (φ (ψ j)) m (u (ψ j)) x) < c := hlt' j
      exact iInf_lt_iff.1 h
    choose x hx using hx
    have hs : ∀ j, ∃ s : ℝ, φ (ψ j) (x j) = s ∧ 0 ≤ s ∧
        s + (2 * m)⁻¹ * ‖x j - u (ψ j)‖ ^ 2 < c := by
      intro j
      have h' : φ (ψ j) (x j) + (((2 * m)⁻¹ * ‖x j - u (ψ j)‖ ^ 2 : ℝ) : EReal) < c := hx j
      have h0 := hφ (ψ j) (x j)
      have hlt : φ (ψ j) (x j) < c :=
        (le_add_of_nonneg_right (EReal.coe_nonneg.2 (by positivity))).trans_lt h'
      obtain ⟨s, hs⟩ : ∃ s : ℝ, φ (ψ j) (x j) = s :=
        ⟨_, (EReal.coe_toReal (ne_top_of_lt hlt)
          (lt_of_lt_of_le EReal.bot_lt_zero h0).ne').symm⟩
      rw [hs] at h' h0
      exact ⟨s, hs, by exact_mod_cast h0, by exact_mod_cast h'⟩
    choose s hs hs0 hsc using hs
    -- the near-minimizers are bounded
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 (isBounded_range_of_tendsto u hu)
    have hb : ∀ j, x j ∈ closedBall (0 : E) (R + (2 * m * c + 1)) := by
      intro j
      rw [mem_closedBall_zero_iff]
      have h1 := hsc j
      have h2 : ‖x j - u (ψ j)‖ ^ 2 < 2 * m * c := by
        have h3 : (2 * m)⁻¹ * ‖x j - u (ψ j)‖ ^ 2 < c := by linarith [hs0 j]
        rwa [inv_mul_eq_div, div_lt_iff₀ (by positivity), mul_comm] at h3
      have h4 : ‖x j - u (ψ j)‖ ≤ 2 * m * c + 1 := by
        nlinarith [sq_nonneg (‖x j - u (ψ j)‖ - 1), norm_nonneg (x j - u (ψ j))]
      have h5 : ‖x j‖ ≤ ‖u (ψ j)‖ + ‖x j - u (ψ j)‖ := by
        simpa using norm_add_le (u (ψ j)) (x j - u (ψ j))
      linarith [hR (u (ψ j)) (mem_range_self _)]
    obtain ⟨x₀, -, θ, hθ, hxθ⟩ := tendsto_subseq_of_bounded isBounded_closedBall hb
    have hlim := hinf x₀ (fun j ↦ ψ (θ j)) (hψ.comp hθ) (fun j ↦ x (θ j)) hxθ
    have hr : Tendsto (fun j ↦ (2 * m)⁻¹ * ‖x (θ j) - u (ψ (θ j))‖ ^ 2) atTop
        (𝓝 ((2 * m)⁻¹ * ‖x₀ - u₀‖ ^ 2)) :=
      ((hxθ.sub (hu.comp (hψ.comp hθ).tendsto_atTop)).norm.pow 2).const_mul _
    have hle : φ₀ x₀ ≤ ((c - (2 * m)⁻¹ * ‖x₀ - u₀‖ ^ 2 : ℝ) : EReal) := by
      refine ereal_le_of_forall_real_gt fun d hd ↦ ?_
      have hd : c - (2 * m)⁻¹ * ‖x₀ - u₀‖ ^ 2 < d := EReal.coe_lt_coe_iff.1 hd
      refine hlim.trans (liminf_le_of_frequently_le' (Eventually.frequently ?_))
      filter_upwards [hr.eventually_const_lt (show c - d < (2 * m)⁻¹ * ‖x₀ - u₀‖ ^ 2 by
        linarith)] with j hj
      show φ (ψ (θ j)) (x (θ j)) ≤ (d : EReal)
      rw [hs (θ j)]
      exact EReal.coe_le_coe_iff.2 (by linarith [hsc (θ j)])
    have hfin : moreauEnvelope φ₀ m u₀ ≤ c := by
      refine (moreauEnvelope_le u₀ x₀).trans ?_
      have := add_le_add hle (le_refl (((2 * m)⁻¹ * ‖x₀ - u₀‖ ^ 2 : ℝ) : EReal))
      rwa [← EReal.coe_add, sub_add_cancel] at this
    exact not_le.2 hc2 hfin
  · -- upper estimate, by recovery sequences
    refine le_iInf fun x ↦ ereal_le_of_forall_real_gt fun c hc ↦ ?_
    obtain ⟨z, hz, hl⟩ := hsup x
    have hc' : φ₀ x + (((2 * m)⁻¹ * ‖x - u₀‖ ^ 2 : ℝ) : EReal) < c := hc
    have h1 : φ₀ x < ((c - (2 * m)⁻¹ * ‖x - u₀‖ ^ 2 : ℝ) : EReal) := by
      by_contra h
      have := add_le_add (not_lt.1 h) (le_refl (((2 * m)⁻¹ * ‖x - u₀‖ ^ 2 : ℝ) : EReal))
      rw [← EReal.coe_add, sub_add_cancel] at this
      exact not_le.2 hc' this
    obtain ⟨d, hd1, hd2⟩ := EReal.lt_iff_exists_real_btwn.1 h1
    have hd2 : d < c - (2 * m)⁻¹ * ‖x - u₀‖ ^ 2 := EReal.coe_lt_coe_iff.1 hd2
    have he1 : ∀ᶠ k in atTop, φ k (z k) < d := eventually_lt_of_limsup_lt (hl.trans_lt hd1)
    have hr : Tendsto (fun k ↦ (2 * m)⁻¹ * ‖z k - u k‖ ^ 2) atTop
        (𝓝 ((2 * m)⁻¹ * ‖x - u₀‖ ^ 2)) := ((hz.sub hu).norm.pow 2).const_mul _
    refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [he1, hr.eventually_lt_const (show (2 * m)⁻¹ * ‖x - u₀‖ ^ 2 < c - d by
      linarith)] with k hk1 hk2
    refine (moreauEnvelope_le (u k) (z k)).trans ?_
    have := EReal.add_lt_add hk1 (EReal.coe_lt_coe_iff.2 hk2)
    rw [← EReal.coe_add, add_sub_cancel] at this
    exact this.le

/-- **Epi-convergence via Moreau envelopes** [Mordukhovich 2024, Ex. 1.135(i)], the direct
part: if the nonnegative functions `φ_i` epi-converge to `φ₀`, then for every `λ > 0` the Moreau
envelopes converge continuously, `e_λφ_i(u') → e_λφ₀(u)` as `i → l`, `u' → u`. In particular
they converge pointwise, and locally uniformly where `e_λφ₀` is finite. -/
theorem EpiTendsto.tendsto_moreauEnvelope [ProperSpace E] [l.IsCountablyGenerated] [l.NeBot]
    (h : EpiTendsto l φ φ₀) (hφ : ∀ i x, 0 ≤ φ i x) {m : ℝ} (hm : 0 < m) (u₀ : E) :
    Tendsto (fun p : ι × E ↦ moreauEnvelope (φ p.1) m p.2) (l ×ˢ 𝓝 u₀)
      (𝓝 (moreauEnvelope φ₀ m u₀)) := by
  rw [epiTendsto_iff] at h
  refine tendsto_of_seq_tendsto fun p hp ↦ ?_
  have ha : Tendsto (fun k ↦ (p k).1) atTop l := tendsto_fst.comp hp
  have hu : Tendsto (fun k ↦ (p k).2) atTop (𝓝 u₀) := tendsto_snd.comp hp
  exact tendsto_moreauEnvelope_of_seq (φ := fun k ↦ φ (p k).1) hm (fun k x ↦ hφ _ x)
    (fun x ψ hψ z hz ↦ (h x).1.trans
      (liminf_le_liminf_comp ((ha.comp hψ.tendsto_atTop).prodMk hz) _))
    (fun x ↦ (h x).2 _ ha) hu

/-- Pointwise convergence of the Moreau envelopes under epi-convergence
[Mordukhovich 2024, Ex. 1.135(i)]. -/
theorem EpiTendsto.tendsto_moreauEnvelope_apply [ProperSpace E] [l.IsCountablyGenerated]
    [l.NeBot] (h : EpiTendsto l φ φ₀) (hφ : ∀ i x, 0 ≤ φ i x) {m : ℝ} (hm : 0 < m) (u : E) :
    Tendsto (fun i ↦ moreauEnvelope (φ i) m u) l (𝓝 (moreauEnvelope φ₀ m u)) :=
  (h.tendsto_moreauEnvelope hφ hm u).comp (tendsto_id.prodMk tendsto_const_nhds)

/-- **Epi-convergence via Moreau envelopes** [Mordukhovich 2024, Ex. 1.135(i)], the converse
part: if `φ_i ≥ 0`, `φ₀ ≥ 0` is l.s.c., and `e_λφ_i → e_λφ₀` pointwise for all small `λ > 0`,
then `φ_i` epi-converges to `φ₀`. -/
theorem epiTendsto_of_tendsto_moreauEnvelope [l.IsCountablyGenerated] [l.NeBot]
    (hφ : ∀ i x, 0 ≤ φ i x) (hφ₀ : ∀ x, 0 ≤ φ₀ x) (hlsc : LowerSemicontinuous φ₀) {m₀ : ℝ}
    (hm₀ : 0 < m₀)
    (h : ∀ m ∈ Ioo 0 m₀, ∀ u,
      Tendsto (fun i ↦ moreauEnvelope (φ i) m u) l (𝓝 (moreauEnvelope φ₀ m u))) :
    EpiTendsto l φ φ₀ := by
  classical
  rw [epiTendsto_iff]
  refine fun x ↦ ⟨?_, fun a ha ↦ ?_⟩
  · by_contra hlt
    obtain ⟨c, hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.1 (not_le.1 hlt)
    obtain ⟨c', hc3, hc4⟩ := EReal.lt_iff_exists_real_btwn.1 hc2
    have hcc : c < c' := EReal.coe_lt_coe_iff.1 hc3
    obtain ⟨p, hp, hlt'⟩ := exists_seq_forall_of_frequently
      (frequently_lt_of_liminf_lt (by isBoundedDefault) hc1)
    have hev : ∀ᶠ m in 𝓝[>] (0 : ℝ), (c' : EReal) < moreauEnvelope φ₀ m x ∧ m ∈ Ioo 0 m₀ :=
      ((tendsto_moreauEnvelope_nhdsGT_zero hφ₀ (hlsc x)).eventually_const_lt hc4).and
        (Ioo_mem_nhdsGT hm₀)
    obtain ⟨m, hm1, hm2⟩ := hev.exists
    have ht : Tendsto (fun k ↦ moreauEnvelope (φ (p k).1) m x) atTop
        (𝓝 (moreauEnvelope φ₀ m x)) := (h m hm2 x).comp (tendsto_fst.comp hp)
    have hr : Tendsto (fun k ↦ (2 * m)⁻¹ * ‖(p k).2 - x‖ ^ 2) atTop
        (𝓝 ((2 * m)⁻¹ * ‖x - x‖ ^ 2)) :=
      (((tendsto_snd.comp hp).sub_const x).norm.pow 2).const_mul _
    have hr0 : (2 * m)⁻¹ * ‖x - x‖ ^ 2 = 0 := by simp
    rw [hr0] at hr
    have he : ∀ᶠ k in atTop, moreauEnvelope (φ (p k).1) m x < c' := by
      filter_upwards [hr.eventually_lt_const (sub_pos.2 hcc)] with k hk
      refine (moreauEnvelope_le x (p k).2).trans_lt ?_
      have := EReal.add_lt_add (hlt' k) (EReal.coe_lt_coe_iff.2 hk)
      rwa [← EReal.coe_add, add_sub_cancel] at this
    obtain ⟨k, hk1, hk2⟩ := ((ht.eventually_const_lt hm1).and he).exists
    exact lt_asymm hk1 hk2
  · have hx0 := hφ₀ x
    rcases eq_or_ne (φ₀ x) ⊤ with hx | hxt
    · exact ⟨fun _ ↦ x, tendsto_const_nhds, hx ▸ le_top⟩
    obtain ⟨s, hs⟩ : ∃ s : ℝ, φ₀ x = s :=
      ⟨_, (EReal.coe_toReal hxt (lt_of_lt_of_le EReal.bot_lt_zero hx0).ne').symm⟩
    have hs0 : 0 ≤ s := by rw [hs] at hx0; exact_mod_cast hx0
    -- near-minimizers of the envelopes with parameters `m₀/(n + 2) ↓ 0`
    have hmpos : ∀ n : ℕ, 0 < m₀ / ((n : ℝ) + 2) := fun n ↦ by positivity
    have hmm : ∀ n : ℕ, m₀ / ((n : ℝ) + 2) ∈ Ioo 0 m₀ := fun n ↦ ⟨hmpos n, by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]⟩
    let P : ℕ → ℕ → Prop := fun n k ↦ ∃ y,
      proxObjective (φ (a k)) (m₀ / ((n : ℝ) + 2)) x y < ((s + 1 / ((n : ℝ) + 1) : ℝ) : EReal)
    have hP : ∀ n, ∀ᶠ k in atTop, P n k := by
      intro n
      have ht : Tendsto (fun k ↦ moreauEnvelope (φ (a k)) (m₀ / ((n : ℝ) + 2)) x) atTop
          (𝓝 (moreauEnvelope φ₀ (m₀ / ((n : ℝ) + 2)) x)) := (h _ (hmm n) x).comp ha
      have hlt : moreauEnvelope φ₀ (m₀ / ((n : ℝ) + 2)) x
          < ((s + 1 / ((n : ℝ) + 1) : ℝ) : EReal) := by
        refine (moreauEnvelope_le_self x).trans_lt ?_
        rw [hs]
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        exact EReal.coe_lt_coe_iff.2 (by linarith)
      filter_upwards [ht.eventually_lt_const hlt] with k hk
      have hk' : (⨅ y, proxObjective (φ (a k)) (m₀ / ((n : ℝ) + 2)) x y)
          < ((s + 1 / ((n : ℝ) + 1) : ℝ) : EReal) := hk
      exact iInf_lt_iff.1 hk'
    obtain ⟨n, hn, hPn⟩ := exists_diag_nat hP
    let z : ℕ → E := fun k ↦ if hk : P (n k) k then hk.choose else x
    have hz : ∀ᶠ k in atTop, φ (a k) (z k) < ((s + 1 / ((n k : ℝ) + 1) : ℝ) : EReal) ∧
        ‖z k - x‖ ^ 2 < 2 * (m₀ / ((n k : ℝ) + 2)) * (s + 1) := by
      filter_upwards [hPn] with k hk
      have hzk : z k = hk.choose := dif_pos hk
      have hspec : φ (a k) (z k)
          + (((2 * (m₀ / ((n k : ℝ) + 2)))⁻¹ * ‖z k - x‖ ^ 2 : ℝ) : EReal)
          < ((s + 1 / ((n k : ℝ) + 1) : ℝ) : EReal) := by
        rw [hzk]
        exact hk.choose_spec
      have hmk := hmpos (n k)
      have hnn : (0 : EReal)
          ≤ (((2 * (m₀ / ((n k : ℝ) + 2)))⁻¹ * ‖z k - x‖ ^ 2 : ℝ) : EReal) :=
        EReal.coe_nonneg.2 (by positivity)
      refine ⟨(le_add_of_nonneg_right hnn).trans_lt hspec, ?_⟩
      have h2 : (2 * (m₀ / ((n k : ℝ) + 2)))⁻¹ * ‖z k - x‖ ^ 2 < s + 1 / ((n k : ℝ) + 1) :=
        EReal.coe_lt_coe_iff.1 ((le_add_of_nonneg_left (hφ (a k) (z k))).trans_lt hspec)
      have h3 : 1 / ((n k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [Nat.cast_nonneg (α := ℝ) (n k)]
      rw [inv_mul_eq_div, div_lt_iff₀ (by positivity)] at h2
      calc ‖z k - x‖ ^ 2 < (s + 1 / ((n k : ℝ) + 1)) * (2 * (m₀ / ((n k : ℝ) + 2))) := h2
        _ ≤ (s + 1) * (2 * (m₀ / ((n k : ℝ) + 2))) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
        _ = 2 * (m₀ / ((n k : ℝ) + 2)) * (s + 1) := by ring
    refine ⟨z, Metric.tendsto_nhds.2 fun ε hε ↦ ?_, ?_⟩
    · filter_upwards [hz, hn.eventually_ge_atTop ⌈2 * m₀ * (s + 1) / ε ^ 2⌉₊] with k hk hkn
      have h1 : 2 * m₀ * (s + 1) / ε ^ 2 ≤ (n k : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast hkn)
      rw [div_le_iff₀ (by positivity)] at h1
      have h2 : 2 * (m₀ / ((n k : ℝ) + 2)) * (s + 1) < ε ^ 2 := by
        have h3 : 2 * (m₀ / ((n k : ℝ) + 2)) * (s + 1)
            = 2 * m₀ * (s + 1) / ((n k : ℝ) + 2) := by ring
        rw [h3, div_lt_iff₀ (by positivity)]
        nlinarith [sq_pos_of_pos hε]
      rw [dist_eq_norm]
      exact lt_of_pow_lt_pow_left₀ 2 hε.le (hk.2.trans h2)
    · rw [hs]
      refine ereal_le_of_forall_real_gt fun c hc ↦ ?_
      have hc : s < c := EReal.coe_lt_coe_iff.1 hc
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt (sub_pos.2 hc)
      refine limsup_le_of_le (by isBoundedDefault) ?_
      filter_upwards [hz, hn.eventually_ge_atTop N] with k hk hkn
      refine hk.1.le.trans (EReal.coe_le_coe_iff.2 ?_)
      have h1 : (N : ℝ) ≤ n k := by exact_mod_cast hkn
      have h2 : 1 / ((n k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith

end MoreauEpi

/-! ### Exercise 1.139(iii): proto-differentiability as set convergence -/

section Proto

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

/-- `Ω` is geometrically derivable at `x ∈ Ω` if and only if the sets `(Ω - x)/t` converge to
the contingent cone as `t ↓ 0`. -/
theorem geometricallyDerivableAt_iff_isSetLimit {Ω : Set X} {x : X} (hx : x ∈ Ω) :
    GeometricallyDerivableAt Ω x ↔
      IsSetLimit (𝓝[>] (0 : ℝ)) (fun t ↦ t⁻¹ • ((· - x) '' Ω)) (contingentCone Ω x) := by
  rw [isSetLimit_iff_subset, ← contingentCone_eq_outerLimit hx]
  refine ⟨fun h ↦ ⟨Subset.rfl, fun u hu a ha ↦ ?_⟩, fun h u hu ↦ ?_⟩
  · obtain ⟨z, hz, hlim⟩ := h.exists_seq hx hu ha
    exact ⟨_, hlim, Eventually.of_forall fun k ↦ smul_mem_smul_set ⟨z k, hz k, rfl⟩⟩
  · refine tendsto_of_seq_tendsto fun a ha ↦ ?_
    obtain ⟨v, hv, hS⟩ := h.2 hu a ha
    have hpos : ∀ᶠ k in atTop, 0 < a k := (tendsto_nhdsWithin_iff.1 ha).2
    refine squeeze_zero' (hpos.mono fun k hk ↦ div_nonneg infDist_nonneg hk.le) ?_
      (tendsto_iff_norm_sub_tendsto_zero.1 hv)
    filter_upwards [hpos, hS] with k hk hvk
    obtain ⟨_, ⟨z, hz, rfl⟩, hzv⟩ := hvk
    have hzv : (a k)⁻¹ • (z - x) = v k := hzv
    have hz' : z = x + a k • v k := by
      rw [← hzv, smul_smul, mul_inv_cancel₀ hk.ne', one_smul]
      exact (add_sub_cancel x z).symm
    calc infDist (x + a k • u) Ω / a k ≤ dist (x + a k • u) z / a k :=
          div_le_div_of_nonneg_right (infDist_le_dist_of_mem hz) hk.le
      _ = ‖v k - u‖ := by
          rw [hz', dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul,
            Real.norm_of_nonneg hk.le, mul_div_cancel_left₀ _ hk.ne', norm_sub_rev]

/-- **Proto-differentiability as set convergence** [Mordukhovich 2024, Ex. 1.139(iii)]: `F` is
proto-differentiable at `x̄` for `ȳ ∈ F(x̄)` if and only if `(gph F - (x̄, ȳ))/t` converges to the
tangent cone `T((x̄, ȳ); gph F)` as `t ↓ 0`. -/
theorem protoDifferentiableAt_iff_isSetLimit {F : X → Set Y} {x₀ : X} {y₀ : Y}
    (hy : y₀ ∈ F x₀) :
    ProtoDifferentiableAt F x₀ y₀ ↔
      IsSetLimit (𝓝[>] (0 : ℝ)) (fun t ↦ t⁻¹ • ((· - (x₀, y₀)) '' graph F))
        (contingentCone (graph F) (x₀, y₀)) :=
  geometricallyDerivableAt_iff_isSetLimit (Ω := graph F) (x := (x₀, y₀)) hy

end Proto

end VariationalAnalysis
