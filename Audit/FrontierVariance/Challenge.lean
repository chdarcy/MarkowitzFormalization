import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Matrix.PosDef

/-!
# Comparator Challenge — Frontier Variance Closed Form

Mathlib-only statement of `frontierPortfolio_variance_closed_form_of_market`. The
definitions required to *state* the theorem are copied here verbatim from the
`MarkowitzFormalization` library (into a dedicated
`MarkowitzFormalization.StatementAudit` namespace) so that this file depends on
nothing but Mathlib. The imports mirror the library's `Basic.lean`, so no Mathlib
module beyond what the project already builds is needed. The proof is left as `sorry`;
the matching `Solution.lean` supplies a real proof by delegating to the library
theorem.
-/

open Matrix

namespace MarkowitzFormalization.StatementAudit

variable (n : Type) [Fintype n] [DecidableEq n]

/-- Copy of `portfolioWeights`: a risky-asset weight vector. -/
abbrev portfolioWeights : Type := n → ℝ

/-- Copy of `onesVec`: the all-ones vector. -/
def onesVec : portfolioWeights n :=
  fun _ => 1

/-- Copy of `portfolioVariance`: `wᵀ Σ w`. -/
def portfolioVariance (covM : Matrix n n ℝ) (w : portfolioWeights n) : ℝ :=
  w ⬝ᵥ covM.mulVec w

/-- Copy of `NonDegenerateMarket`: positive-definite covariance with non-constant `μ`. -/
structure NonDegenerateMarket
    (μ : portfolioWeights n)
    (covM : Matrix n n ℝ) : Prop where
  posDef : covM.PosDef
  not_proportional : ¬ ∃ c : ℝ, μ = fun _ => c

/-- Copy of `frontierA`: `A = 1ᵀ Σ⁻¹ μ`. -/
noncomputable def frontierA (covM : Matrix n n ℝ) (μ : portfolioWeights n) : ℝ :=
  onesVec n ⬝ᵥ covM⁻¹.mulVec μ

/-- Copy of `frontierB`: `B = μᵀ Σ⁻¹ μ`. -/
noncomputable def frontierB (covM : Matrix n n ℝ) (μ : portfolioWeights n) : ℝ :=
  μ ⬝ᵥ covM⁻¹.mulVec μ

/-- Copy of `frontierC`: `C = 1ᵀ Σ⁻¹ 1`. -/
noncomputable def frontierC (covM : Matrix n n ℝ) : ℝ :=
  onesVec n ⬝ᵥ covM⁻¹.mulVec (onesVec n)

/-- Copy of `frontierD`: `D = B C - A²`. -/
noncomputable def frontierD (covM : Matrix n n ℝ) (μ : portfolioWeights n) : ℝ :=
  frontierB n covM μ * frontierC n covM - (frontierA n covM μ) ^ 2

/-- Copy of `frontierLambda`: `λ(m) = (C m - A) / D`. -/
noncomputable def frontierLambda (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ) : ℝ :=
  (frontierC n covM * m - frontierA n covM μ) / frontierD n covM μ

/-- Copy of `frontierGamma`: `γ(m) = (B - A m) / D`. -/
noncomputable def frontierGamma (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ) : ℝ :=
  (frontierB n covM μ - frontierA n covM μ * m) / frontierD n covM μ

/-- Copy of `frontierPortfolio`: `w★(m) = λ(m) Σ⁻¹ μ + γ(m) Σ⁻¹ 1`. -/
noncomputable def frontierPortfolio (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ) :
    portfolioWeights n :=
  frontierLambda n covM μ m • covM⁻¹.mulVec μ +
    frontierGamma n covM μ m • covM⁻¹.mulVec (onesVec n)

/-- **Frontier variance closed form** (challenge statement): on a non-degenerate market
the minimum-variance frontier portfolio has variance `(C m² − 2A m + B)/D`. -/
theorem frontierPortfolio_variance_closed_form_of_market
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ)
    (market : NonDegenerateMarket n μ covM) [Nonempty n] :
    portfolioVariance n covM (frontierPortfolio n covM μ m)
      = (frontierC n covM * m ^ 2
          - 2 * frontierA n covM μ * m
          + frontierB n covM μ) / frontierD n covM μ := by
  sorry

end MarkowitzFormalization.StatementAudit
