import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Matrix.PosDef

/-!
# Comparator Challenge — Squared Capital Market Line

Mathlib-only statement of `capitalMarketLine_squared`. The definitions required to
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

/-- Copy of `portfolioVariance`: `wᵀ Σ w`. -/
def portfolioVariance (covM : Matrix n n ℝ) (w : portfolioWeights n) : ℝ :=
  w ⬝ᵥ covM.mulVec w

/-- Copy of `riskFreeVariance`: total variance equals the risky quadratic form. -/
def riskFreeVariance (covM : Matrix n n ℝ) (w : portfolioWeights n) : ℝ :=
  portfolioVariance n covM w

/-- Copy of `sharpeSquared`: `eᵀ Σ⁻¹ e`, the squared Sharpe ratio (CML slope²). -/
noncomputable def sharpeSquared
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (rf : ℝ) : ℝ :=
  excessReturn n μ rf ⬝ᵥ covM⁻¹.mulVec (excessReturn n μ rf)

/-- Copy of `rfFrontierPortfolio`: `w★ = ((m - rf) / eᵀΣ⁻¹e) · Σ⁻¹ e`. -/
noncomputable def rfFrontierPortfolio
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (rf m : ℝ) :
    portfolioWeights n :=
  ((m - rf) / sharpeSquared n covM μ rf)
    • covM⁻¹.mulVec (excessReturn n μ rf)

/-- **Squared Capital Market Line** (challenge statement): the risk-free frontier
variance times the squared Sharpe ratio equals `(m - rf)²`. -/
theorem capitalMarketLine_squared
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (rf m : ℝ)
    (hcov : covM.PosDef)
    (he : excessReturn n μ rf ≠ 0) :
    riskFreeVariance n covM (rfFrontierPortfolio n covM μ rf m)
      * sharpeSquared n covM μ rf
        = (m - rf) ^ 2 := by
  sorry

end MarkowitzFormalization.StatementAudit
