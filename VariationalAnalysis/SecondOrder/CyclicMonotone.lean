/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis.SCD.Monotone

/-!
# Resolvents and cyclically monotone mappings

This file follows [Mordukhovich 2024, Sect. 1.5.2] (body numbering): resolvents of monotone
operators (Lemma 1.95), cyclical monotonicity (Def. 1.96), and Rockafellar's characterization of
maximal cyclically monotone mappings as subdifferentials of convex functions (Lemma 1.97).

## Main declarations

* `resolventMap T l`: the resolvent `(I + λT)⁻¹ : E ⇉ E` of `T : E ⇉ E`.
* `CyclicallyMonotone T`, `MaximalCyclicallyMonotone T`: [Mordukhovich 2024, Def. 1.96].
* `CMChain T x₀ v₀`, `rockafellarFun T x₀ v₀`: chains in `gph T` starting at `(x₀, v₀)` and
  Rockafellar's function, the supremum of the affine functions they generate.

## Main results

* `IsMonotoneOp.isMonotoneOp_resolventMap`, `IsMonotoneOp.norm_sub_le_of_mem_resolventMap`,
  `IsMonotoneOp.isMaximalMonotoneOp_of_resolventMap`,
  `IsMonotoneOp.exists_resolventMap_eq_singleton`: [Mordukhovich 2024, Lemma 1.95], except the
  implication "maximal monotone ⇒ `dom (I + λT)⁻¹ = E`" (Minty's theorem).
* `isMaximalMonotoneOp_of_continuous`: continuous monotone single-valued operators are maximal
  monotone [Mordukhovich 2024, Ex. 1.146].
* `cyclicallyMonotone_subdiff_of_convex`, `rockafellarFun_zero`, `convex_epi_rockafellarFun`,
  `lowerSemicontinuous_rockafellarFun`, `mem_subdiff_rockafellarFun`,
  `maximalCyclicallyMonotone_iff`: [Mordukhovich 2024, Lemma 1.97], without the uniqueness of
  `φ` up to an additive constant.
-/

open Filter Topology Set Finset
open scoped InnerProductSpace Pointwise

namespace VariationalAnalysis

/-! ### Lemma 1.95: resolvents of monotone operators -/

section Resolvent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The resolvent `(I + λT)⁻¹ : E ⇉ E`: `x ∈ (I + λT)⁻¹(u)` iff `u ∈ x + λT(x)`. -/
def resolventMap (T : E → Set E) (l : ℝ) (u : E) : Set E :=
  {x | ∃ y ∈ T x, u = x + l • y}

variable {T : E → Set E} {l : ℝ}

theorem IsMonotoneOp.sq_norm_le_of_mem_resolventMap (hT : IsMonotoneOp T) (hl : 0 ≤ l)
    {u₁ u₂ x₁ x₂ : E} (h₁ : x₁ ∈ resolventMap T l u₁) (h₂ : x₂ ∈ resolventMap T l u₂) :
    ‖x₁ - x₂‖ ^ 2 ≤ ⟪x₁ - x₂, u₁ - u₂⟫_ℝ := by
  obtain ⟨y₁, hy₁, rfl⟩ := h₁
  obtain ⟨y₂, hy₂, rfl⟩ := h₂
  have hm := hT x₁ x₂ y₁ hy₁ y₂ hy₂
  have e : x₁ + l • y₁ - (x₂ + l • y₂) = (x₁ - x₂) + l • (y₁ - y₂) := by
    rw [smul_sub]; abel
  rw [e, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, real_inner_comm]
  have : 0 ≤ l * ⟪y₁ - y₂, x₁ - x₂⟫_ℝ := mul_nonneg hl hm
  linarith

/-- [Mordukhovich 2024, Lemma 1.95]: the resolvent of a monotone operator is monotone. -/
theorem IsMonotoneOp.isMonotoneOp_resolventMap (hT : IsMonotoneOp T) (hl : 0 ≤ l) :
    IsMonotoneOp (resolventMap T l) := fun _ _ _ h₁ _ h₂ ↦
  (sq_nonneg _).trans (hT.sq_norm_le_of_mem_resolventMap hl h₁ h₂)

/-- [Mordukhovich 2024, Lemma 1.95]: the resolvent of a monotone operator is nonexpansive. -/
theorem IsMonotoneOp.norm_sub_le_of_mem_resolventMap (hT : IsMonotoneOp T) (hl : 0 ≤ l)
    {u₁ u₂ x₁ x₂ : E} (h₁ : x₁ ∈ resolventMap T l u₁) (h₂ : x₂ ∈ resolventMap T l u₂) :
    ‖x₁ - x₂‖ ≤ ‖u₁ - u₂‖ :=
  norm_le_of_sq_le_inner (hT.sq_norm_le_of_mem_resolventMap hl h₁ h₂)

/-- The resolvent of a monotone operator is single-valued on its domain. -/
theorem IsMonotoneOp.eq_of_mem_resolventMap (hT : IsMonotoneOp T) (hl : 0 ≤ l) {u x₁ x₂ : E}
    (h₁ : x₁ ∈ resolventMap T l u) (h₂ : x₂ ∈ resolventMap T l u) : x₁ = x₂ := by
  have := hT.norm_sub_le_of_mem_resolventMap hl h₁ h₂
  rw [sub_self, norm_zero] at this
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

/-- Positive multiples of monotone operators are monotone. -/
theorem IsMonotoneOp.smul (hT : IsMonotoneOp T) (hl : 0 ≤ l) :
    IsMonotoneOp fun x ↦ l • T x := by
  rintro x₁ x₂ _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩
  rw [← smul_sub, inner_smul_left]
  exact mul_nonneg hl (hT x₁ x₂ y₁ hy₁ y₂ hy₂)

/-- [Mordukhovich 2024, Lemma 1.95]: a monotone operator `T` with `dom (I + λT)⁻¹ = E` for some
`λ > 0` is maximal monotone. (The converse is Minty's theorem, not formalized here.) -/
theorem IsMonotoneOp.isMaximalMonotoneOp_of_resolventMap (hT : IsMonotoneOp T) (hl : 0 < l)
    (hdom : ∀ u, (resolventMap T l u).Nonempty) : IsMaximalMonotoneOp T := by
  have hs : ∀ u, ∃ x, u - x ∈ (fun x ↦ l • T x) x := by
    intro u
    obtain ⟨x, y, hy, hu⟩ := hdom u
    exact ⟨x, ⟨y, hy, by rw [hu]; abel⟩⟩
  have hmax := (hT.smul hl.le).isMaximalMonotoneOp hs
  refine ⟨hT, fun x y hxy ↦ ?_⟩
  have : l • y ∈ l • T x := by
    refine hmax.2 x (l • y) fun x' _ ⟨y', hy', hyy'⟩ ↦ ?_
    rw [← hyy', ← smul_sub, inner_smul_left]
    exact mul_nonneg hl.le (hxy x' y' hy')
  exact (Set.smul_mem_smul_set_iff₀ hl.ne' _ _).1 this

/-- [Mordukhovich 2024, Ex. 1.146]: a continuous monotone single-valued operator is maximal
monotone. -/
theorem isMaximalMonotoneOp_of_continuous {f : E → E} (hf : Continuous f)
    (hmono : ∀ u₁ u₂, 0 ≤ ⟪f u₁ - f u₂, u₁ - u₂⟫_ℝ) :
    IsMaximalMonotoneOp fun u ↦ {f u} := by
  refine ⟨?_, fun u x hux ↦ ?_⟩
  · rintro u₁ u₂ _ rfl _ rfl
    exact hmono u₁ u₂
  set d := x - f u
  have hlim : Tendsto (fun t : ℝ ↦ ⟪x - f (u + t • d), d⟫_ℝ) (𝓝[>] 0) (𝓝 ⟪x - f u, d⟫_ℝ) := by
    have hc : Continuous fun t : ℝ ↦ ⟪x - f (u + t • d), d⟫_ℝ := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hle : ⟪x - f u, d⟫_ℝ ≤ 0 := by
    refine le_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have h := hux (u + t • d) (f (u + t • d)) rfl
    rw [show u - (u + t • d) = -(t • d) by abel, inner_neg_right, inner_smul_right] at h
    nlinarith
  have : ‖d‖ ^ 2 ≤ 0 := by rwa [← real_inner_self_eq_norm_sq]
  have hd : d = 0 := by
    have := norm_nonneg d
    exact norm_eq_zero.1 (by nlinarith)
  exact mem_singleton_iff.2 (sub_eq_zero.1 hd)

/-- [Mordukhovich 2024, Lemma 1.95]: if `T` is monotone and `dom (I + λT)⁻¹ = E`, then the
resolvent is single-valued, `1`-Lipschitz and maximal monotone. -/
theorem IsMonotoneOp.exists_resolventMap_eq_singleton (hT : IsMonotoneOp T) (hl : 0 < l)
    (hdom : ∀ u, (resolventMap T l u).Nonempty) :
    ∃ r : E → E, (∀ u, resolventMap T l u = {r u}) ∧ LipschitzWith 1 r ∧
      IsMaximalMonotoneOp (resolventMap T l) := by
  choose r hr using hdom
  have hsing : ∀ u, resolventMap T l u = {r u} := fun u ↦
    Set.eq_singleton_iff_unique_mem.2 ⟨hr u, fun x hx ↦ hT.eq_of_mem_resolventMap hl.le hx (hr u)⟩
  have hlip : LipschitzWith 1 r := LipschitzWith.of_dist_le_mul fun u₁ u₂ ↦ by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
    exact hT.norm_sub_le_of_mem_resolventMap hl.le (hr u₁) (hr u₂)
  refine ⟨r, hsing, hlip, ?_⟩
  have hfun : resolventMap T l = fun u ↦ {r u} := funext hsing
  rw [hfun]
  refine isMaximalMonotoneOp_of_continuous hlip.continuous fun u₁ u₂ ↦ ?_
  have := hT.isMonotoneOp_resolventMap hl.le u₁ u₂ (r u₁) (hr u₁) (r u₂) (hr u₂)
  exact this

end Resolvent

/-! ### Def. 1.96: cyclical monotonicity -/

section Cyclic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- [Mordukhovich 2024, Def. 1.96]: `T : E ⇉ E*` is cyclically monotone if
`⟨v₀, x₁ - x₀⟩ + ⟨v₁, x₂ - x₁⟩ + ⋯ + ⟨vₘ, x₀ - xₘ⟩ ≤ 0` whenever `vᵢ ∈ T(xᵢ)`, `i = 0, …, m`. -/
def CyclicallyMonotone (T : E → Set (StrongDual ℝ E)) : Prop :=
  ∀ (m : ℕ) (x : ℕ → E) (v : ℕ → StrongDual ℝ E), (∀ i ≤ m, v i ∈ T (x i)) →
    ∑ i ∈ range m, v i (x (i + 1) - x i) + v m (x 0 - x m) ≤ 0

/-- [Mordukhovich 2024, Def. 1.96]: `T` is maximal cyclically monotone if it is cyclically
monotone and its graph cannot be enlarged without destroying cyclical monotonicity. -/
def MaximalCyclicallyMonotone (T : E → Set (StrongDual ℝ E)) : Prop :=
  CyclicallyMonotone T ∧
    ∀ S : E → Set (StrongDual ℝ E), CyclicallyMonotone S → (∀ x, T x ⊆ S x) → S = T

variable {T : E → Set (StrongDual ℝ E)}

/-- Cyclically monotone mappings are monotone (take `m = 1`). -/
theorem CyclicallyMonotone.globallyMonotone (hT : CyclicallyMonotone T) : GloballyMonotone T := by
  intro x₁ x₂ v₁ hv₁ v₂ hv₂
  have h := hT 1 (fun i ↦ if i = 0 then x₁ else x₂) (fun i ↦ if i = 0 then v₁ else v₂)
    (fun i hi ↦ by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hi with rfl | rfl <;> simp [hv₁, hv₂])
  simp only [range_one, sum_singleton, one_ne_zero, if_false, if_true, zero_add] at h
  have e1 : v₁ (x₂ - x₁) = -v₁ (x₁ - x₂) := by rw [← map_neg, neg_sub]
  have e2 : (v₁ - v₂) (x₁ - x₂) = v₁ (x₁ - x₂) - v₂ (x₁ - x₂) := rfl
  rw [e2]
  linarith

end Cyclic

/-! ### Lemma 1.97: Rockafellar's theorem -/

section Rockafellar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- [Mordukhovich 2024, Lemma 1.97, (1.134)]: the subdifferential of a convex function is
cyclically monotone. -/
theorem cyclicallyMonotone_subdiff_of_convex {φ : E → EReal} (hconv : Convex ℝ (φ.Epi univ)) :
    CyclicallyMonotone (subdiff φ) := by
  intro m x v hv
  have hfin : ∀ i ≤ m, φ (x i) = ((φ (x i)).toReal : EReal) := by
    intro i hi
    obtain ⟨r, hr, -⟩ := hv i hi
    rw [hr, EReal.toReal_coe]
  set r : ℕ → ℝ := fun i ↦ (φ (x i)).toReal
  have hineq : ∀ i ≤ m, ∀ j ≤ m, v i (x j - x i) ≤ r j - r i := by
    intro i hi j hj
    have h := (mem_subdiff_of_convex hconv (hfin i hi)).1 (hv i hi) (x j)
    rw [hfin j hj, EReal.coe_le_coe_iff] at h
    simp only [r]
    linarith
  have hsum : ∑ i ∈ range m, v i (x (i + 1) - x i) ≤ ∑ i ∈ range m, (r (i + 1) - r i) :=
    sum_le_sum fun i hi ↦ hineq i (mem_range.1 hi).le (i + 1) (mem_range.1 hi)
  rw [sum_range_sub] at hsum
  have := hineq m le_rfl 0 (Nat.zero_le _)
  linarith

variable {T : E → Set (StrongDual ℝ E)} {x₀ : E} {v₀ : StrongDual ℝ E}

/-- A chain `(x₀, v₀), (x₁, v₁), …, (xₘ, vₘ)` in `gph T` starting at `(x₀, v₀)`. -/
structure CMChain (T : E → Set (StrongDual ℝ E)) (x₀ : E) (v₀ : StrongDual ℝ E) where
  /-- The index `m` of the last point. -/
  len : ℕ
  /-- The points `xᵢ`. -/
  pt : ℕ → E
  /-- The dual vectors `vᵢ`. -/
  dual : ℕ → StrongDual ℝ E
  pt_zero : pt 0 = x₀
  dual_zero : dual 0 = v₀
  mem : ∀ i ≤ len, dual i ∈ T (pt i)

/-- The affine function `⟨vₘ, x - xₘ⟩ + ⟨vₘ₋₁, xₘ - xₘ₋₁⟩ + ⋯ + ⟨v₀, x₁ - x₀⟩` of a chain. -/
def CMChain.val (c : CMChain T x₀ v₀) (y : E) : ℝ :=
  ∑ i ∈ range c.len, c.dual i (c.pt (i + 1) - c.pt i) + c.dual c.len (y - c.pt c.len)

/-- Rockafellar's function [Mordukhovich 2024, proof of Lemma 1.97]: the supremum of the affine
functions generated by chains in `gph T` starting at `(x₀, v₀)`. -/
noncomputable def rockafellarFun (T : E → Set (StrongDual ℝ E)) (x₀ : E) (v₀ : StrongDual ℝ E)
    (y : E) : EReal :=
  ⨆ c : CMChain T x₀ v₀, (c.val y : EReal)

/-- The trivial chain `(x₀, v₀)`. -/
def CMChain.base (h : v₀ ∈ T x₀) : CMChain T x₀ v₀ where
  len := 0
  pt := fun _ ↦ x₀
  dual := fun _ ↦ v₀
  pt_zero := rfl
  dual_zero := rfl
  mem := fun _ _ ↦ h

theorem CMChain.base_val (h : v₀ ∈ T x₀) (y : E) : (CMChain.base h).val y = v₀ (y - x₀) := by
  simp [CMChain.val, CMChain.base]

/-- A chain extended by a point `(x, v) ∈ gph T`. -/
def CMChain.extend (c : CMChain T x₀ v₀) {x : E} {v : StrongDual ℝ E} (h : v ∈ T x) :
    CMChain T x₀ v₀ where
  len := c.len + 1
  pt := fun i ↦ if i = c.len + 1 then x else c.pt i
  dual := fun i ↦ if i = c.len + 1 then v else c.dual i
  pt_zero := by simp [c.pt_zero]
  dual_zero := by simp [c.dual_zero]
  mem := by
    intro i hi
    by_cases hi' : i = c.len + 1
    · simp [hi', h]
    · simp only [hi', if_false]
      exact c.mem i (by omega)

theorem CMChain.extend_val (c : CMChain T x₀ v₀) {x : E} {v : StrongDual ℝ E} (h : v ∈ T x)
    (y : E) : (c.extend h).val y = c.val x + v (y - x) := by
  simp only [CMChain.val, CMChain.extend, sum_range_succ, if_true]
  have hs : ∑ i ∈ range c.len, (if i = c.len + 1 then v else c.dual i)
      ((if i + 1 = c.len + 1 then x else c.pt (i + 1)) - if i = c.len + 1 then x else c.pt i) =
      ∑ i ∈ range c.len, c.dual i (c.pt (i + 1) - c.pt i) := by
    refine sum_congr rfl fun i hi ↦ ?_
    have h1 : i ≠ c.len + 1 := by have := mem_range.1 hi; omega
    have := mem_range.1 hi
    simp [h1, show i ≠ c.len by omega]
  rw [hs]
  simp

/-- Cyclical monotonicity bounds every chain value at `x₀` by `0`. -/
theorem CyclicallyMonotone.val_le (hT : CyclicallyMonotone T) (c : CMChain T x₀ v₀) :
    c.val x₀ ≤ 0 := by
  have := hT c.len c.pt c.dual c.mem
  rwa [c.pt_zero] at this

theorem le_rockafellarFun (c : CMChain T x₀ v₀) (y : E) :
    (c.val y : EReal) ≤ rockafellarFun T x₀ v₀ y :=
  le_iSup (fun c : CMChain T x₀ v₀ ↦ (c.val y : EReal)) c

/-- [Mordukhovich 2024, proof of Lemma 1.97]: Rockafellar's function vanishes at `x₀`. -/
theorem rockafellarFun_zero (hT : CyclicallyMonotone T) (h : v₀ ∈ T x₀) :
    rockafellarFun T x₀ v₀ x₀ = 0 := by
  refine le_antisymm (iSup_le fun c ↦ EReal.coe_nonpos.2 (hT.val_le c)) ?_
  have := le_rockafellarFun (CMChain.base h) x₀
  rwa [CMChain.base_val, sub_self, map_zero, EReal.coe_zero] at this

theorem rockafellarFun_ne_bot (h : v₀ ∈ T x₀) (y : E) : rockafellarFun T x₀ v₀ y ≠ ⊥ :=
  ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_rockafellarFun (CMChain.base h) y)

/-- Rockafellar's function is convex. -/
theorem convex_epi_rockafellarFun : Convex ℝ ((rockafellarFun T x₀ v₀).Epi univ) := by
  rintro ⟨p₁, p₂⟩ ⟨-, hp⟩ ⟨q₁, q₂⟩ ⟨-, hq⟩ a b ha hb hab
  refine ⟨mem_univ _, ?_⟩
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  refine iSup_le fun c ↦ ?_
  have hp' := EReal.coe_le_coe_iff.1 ((le_rockafellarFun c p₁).trans hp)
  have hq' := EReal.coe_le_coe_iff.1 ((le_rockafellarFun c q₁).trans hq)
  have e : c.val (a • p₁ + b • q₁) = a * c.val p₁ + b * c.val q₁ := by
    simp only [CMChain.val, map_sub, map_add, map_smul, smul_eq_mul]
    have : b = 1 - a := by linarith
    subst this
    ring
  rw [EReal.coe_le_coe_iff, e]
  have h1 := mul_le_mul_of_nonneg_left hp' ha
  have h2 := mul_le_mul_of_nonneg_left hq' hb
  linarith

/-- Rockafellar's function is lower semicontinuous. -/
theorem lowerSemicontinuous_rockafellarFun : LowerSemicontinuous (rockafellarFun T x₀ v₀) := by
  refine lowerSemicontinuous_iSup fun c ↦ ?_
  refine (continuous_coe_real_ereal.comp ?_).lowerSemicontinuous
  unfold CMChain.val
  fun_prop

/-- [Mordukhovich 2024, proof of Lemma 1.97]: `gph T ⊆ gph ∂φ` for Rockafellar's function `φ`. -/
theorem mem_subdiff_rockafellarFun (hT : CyclicallyMonotone T) (h₀ : v₀ ∈ T x₀) {x : E}
    {v : StrongDual ℝ E} (h : v ∈ T x) : v ∈ subdiff (rockafellarFun T x₀ v₀) x := by
  -- `rockafellarFun T x₀ v₀ y ≥ c.val x + v (y - x)` for every chain `c`
  have hext : ∀ y, ∀ c : CMChain T x₀ v₀, ((c.val x + v (y - x) : ℝ) : EReal) ≤ rockafellarFun T x₀ v₀ y := by
    intro y c
    rw [← c.extend_val h]
    exact le_rockafellarFun _ y
  -- `rockafellarFun T x₀ v₀ x ≤ s - v (y - x)` whenever `rockafellarFun T x₀ v₀ y = s`
  have hup : ∀ y (s : ℝ), rockafellarFun T x₀ v₀ y = s → rockafellarFun T x₀ v₀ x ≤ ((s - v (y - x) : ℝ) : EReal) := by
    intro y s hs
    refine iSup_le fun c ↦ ?_
    have := hext y c
    rw [hs, EReal.coe_le_coe_iff] at this
    exact EReal.coe_le_coe_iff.2 (by linarith)
  have hx0 : rockafellarFun T x₀ v₀ x ≤ ((0 - v (x₀ - x) : ℝ) : EReal) :=
    hup x₀ 0 (by rw [rockafellarFun_zero hT h₀, EReal.coe_zero])
  have hxtop : rockafellarFun T x₀ v₀ x ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hx0
  have hr : rockafellarFun T x₀ v₀ x = ((rockafellarFun T x₀ v₀ x).toReal : EReal) :=
    (EReal.coe_toReal hxtop (rockafellarFun_ne_bot h₀ x)).symm
  rw [mem_subdiff_of_convex convex_epi_rockafellarFun hr]
  intro y
  by_cases hy : rockafellarFun T x₀ v₀ y = ⊤
  · rw [hy]; exact le_top
  have hy' : rockafellarFun T x₀ v₀ y = ((rockafellarFun T x₀ v₀ y).toReal : EReal) :=
    (EReal.coe_toReal hy (rockafellarFun_ne_bot h₀ y)).symm
  have := hup y _ hy'
  rw [hr, EReal.coe_le_coe_iff] at this
  rw [hy', EReal.coe_le_coe_iff]
  linarith

variable [FiniteDimensional ℝ E]

/-- [Mordukhovich 2024, Lemma 1.97] (Rockafellar): `T : E ⇉ E*` is maximal cyclically monotone if
and only if `T = ∂φ` for some proper, l.s.c. and convex function `φ`. -/
theorem maximalCyclicallyMonotone_iff :
    MaximalCyclicallyMonotone T ↔
      ∃ φ : E → EReal, Convex ℝ (φ.Epi univ) ∧ LowerSemicontinuous φ ∧ (∀ y, φ y ≠ ⊥) ∧
        (∃ y, φ y ≠ ⊤) ∧ T = subdiff φ := by
  constructor
  · rintro ⟨hT, hmax⟩
    -- the graph of `T` is nonempty
    obtain ⟨x₀, v₀, h₀⟩ : ∃ x₀ v₀, v₀ ∈ T x₀ := by
      classical
      by_contra hne
      push Not at hne
      set S : E → Set (StrongDual ℝ E) := fun x ↦ if x = 0 then {0} else ∅
      have hS : CyclicallyMonotone S := by
        intro m x v hv
        have hx : ∀ i ≤ m, x i = 0 := fun i hi ↦ by
          by_contra hxi
          have := hv i hi
          simp [S] at this
          exact hxi this.1
        have hv0 : ∀ i ≤ m, v i = 0 := fun i hi ↦ by
          have := hv i hi
          simpa [S, hx i hi] using this
        rw [sum_eq_zero fun i hi ↦ by simp [hv0 i (mem_range.1 hi).le], hv0 m le_rfl]
        simp
      have := hmax S hS fun x v hv ↦ absurd hv (hne x v)
      have h0 : (0 : StrongDual ℝ E) ∈ S 0 := by simp [S]
      rw [this] at h0
      exact hne 0 0 h0
    have hsub : ∀ x, T x ⊆ subdiff (rockafellarFun T x₀ v₀) x := fun x v hv ↦ mem_subdiff_rockafellarFun hT h₀ hv
    refine ⟨rockafellarFun T x₀ v₀, convex_epi_rockafellarFun, lowerSemicontinuous_rockafellarFun,
      rockafellarFun_ne_bot h₀, ⟨x₀, by rw [rockafellarFun_zero hT h₀]; exact EReal.zero_ne_top⟩,
      (hmax _ (cyclicallyMonotone_subdiff_of_convex convex_epi_rockafellarFun) hsub).symm⟩
  · rintro ⟨φ, hconv, hlsc, hbot, hdom, rfl⟩
    refine ⟨cyclicallyMonotone_subdiff_of_convex hconv, fun S hS hsub ↦ ?_⟩
    exact (globallyMaximalMonotone_subdiff_of_convex hconv hlsc hbot hdom).2 S
      hS.globallyMonotone hsub

end Rockafellar

end VariationalAnalysis
