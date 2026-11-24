/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import VariationalAnalysis

/-!
# The example of the README

Keep this file and the "Example" section of `README.md` identical, so that the code shown
there is known to compile.
-/

open VariationalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The generalized Fermat rule: `0 ∈ ∂φ(x₀)` at a local minimizer where `φ` is finite. -/
example {φ : E → EReal} {x₀ : E} {r : ℝ} (hmin : IsLocalMin φ x₀) (hr : φ x₀ = r) :
    (0 : StrongDual ℝ E) ∈ subdiff φ x₀ :=
  zero_mem_subdiff_of_isLocalMin hmin hr
