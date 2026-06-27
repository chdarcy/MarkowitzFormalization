import MarkowitzFormalization

/-!
# Comparator Solution — Risk-Free One-Fund Separation

Restates `rfFrontierPortfolio_one_fund` with the **same** copied definitions and the
**same** `MarkowitzFormalization.StatementAudit` namespace as `Challenge.lean`, so the
two theorem statements are identical for Comparator. The proof delegates to the
library theorem `_root_.rfFrontierPortfolio_one_fund`; the copied definitions are
definitionally equal to the library ones, so `exact` closes the goal.
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

/-- **One-fund separation** (solution): identical statement to the challenge, proved by
delegating to the library theorem. -/
theorem rfFrontierPortfolio_one_fund
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (rf m : ℝ)
    (hD : tangencyDenominator n covM μ rf ≠ 0) :
    rfFrontierPortfolio n covM μ rf m
      =
    (((m - rf) * tangencyDenominator n covM μ rf)
      / sharpeSquared n covM μ rf)
      • tangencyPortfolio n covM μ rf := by
  exact _root_.rfFrontierPortfolio_one_fund n covM μ rf m hD

end MarkowitzFormalization.StatementAudit
