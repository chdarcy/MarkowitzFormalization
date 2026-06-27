import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Matrix.PosDef

/-!
# Comparator Challenge — Risk-Free One-Fund Separation

Mathlib-only statement of `rfFrontierPortfolio_one_fund`. The definitions required to
*state* the theorem are copied here verbatim from the `MarkowitzFormalization`
library (into a dedicated `MarkowitzFormalization.StatementAudit` namespace) so that
this file depends on nothing but Mathlib. The imports mirror the library's
`Basic.lean`, so no Mathlib module beyond what the project already builds is needed.
The proof is left as `sorry`; the matching `Solution.lean` supplies a real proof by
delegating to the library theorem.
-/

open Matrix

namespace MarkowitzFormalization.StatementAudit

variable (n : Type) [Fintype n] [DecidableEq n]

/-- Copy of `portfolioWeights`: a risky-asset weight vector. -/
abbrev portfolioWeights : Type := n → ℝ

/-- Copy of `excessReturn`: `e = μ - rf·1`. -/
def excessReturn (μ : portfolioWeights n) (rf : ℝ) : portfolioWeights n :=
  fun i => μ i - rf

/-- Copy of `onesVec`: the all-ones vector. -/
def onesVec : portfolioWeights n :=
  fun _ => 1

/-- Copy of `sharpeSquared`: `eᵀ Σ⁻¹ e`, the squared Sharpe ratio (CML slope²). -/
noncomputable def sharpeSquared
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (rf : ℝ) : ℝ :=
  excessReturn n μ rf ⬝ᵥ covM⁻¹.mulVec (excessReturn n μ rf)

/-- Copy of `tangencyDenominator`: `1ᵀ Σ⁻¹ e`. -/
noncomputable def tangencyDenominator
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (rf : ℝ) : ℝ :=
  onesVec n ⬝ᵥ covM⁻¹.mulVec (excessReturn n μ rf)

/-- Copy of `rfFrontierPortfolio`: `w★ = ((m - rf) / eᵀΣ⁻¹e) · Σ⁻¹ e`. -/
noncomputable def rfFrontierPortfolio
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (rf m : ℝ) :
    portfolioWeights n :=
  ((m - rf) / sharpeSquared n covM μ rf)
    • covM⁻¹.mulVec (excessReturn n μ rf)

/-- Copy of `tangencyPortfolio`: `w_T = (1 / 1ᵀΣ⁻¹e) · Σ⁻¹ e`. -/
noncomputable def tangencyPortfolio
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (rf : ℝ) :
    portfolioWeights n :=
  (1 / tangencyDenominator n covM μ rf)
    • covM⁻¹.mulVec (excessReturn n μ rf)

/-- **One-fund separation** (challenge statement): every risk-free frontier portfolio
is a scalar multiple of the single tangency portfolio. -/
theorem rfFrontierPortfolio_one_fund
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (rf m : ℝ)
    (hD : tangencyDenominator n covM μ rf ≠ 0) :
    rfFrontierPortfolio n covM μ rf m
      =
    (((m - rf) * tangencyDenominator n covM μ rf)
      / sharpeSquared n covM μ rf)
      • tangencyPortfolio n covM μ rf := by
  sorry

end MarkowitzFormalization.StatementAudit
