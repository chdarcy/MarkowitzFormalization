import MarkowitzFormalization

/-!
# Comparator Solution — Risk-Free Frontier Optimality

Restates `rfFrontierPortfolio_optimal` with the **same** copied definitions and the
**same** `MarkowitzFormalization.StatementAudit` namespace as `Challenge.lean`, so the
two theorem statements are identical for Comparator. The proof delegates to the
library theorem `_root_.rfFrontierPortfolio_optimal`; the copied definitions are
definitionally equal to the library ones, so `exact` closes the goal.
-/

open Finset Matrix

namespace MarkowitzFormalization.StatementAudit

variable (n : Type) [Fintype n] [DecidableEq n]

/-- Copy of `portfolioWeights`: a risky-asset weight vector. -/
abbrev portfolioWeights : Type := n → ℝ

/-- Copy of `excessReturn`: `e = μ - rf·1`. -/
def excessReturn (μ : portfolioWeights n) (rf : ℝ) : portfolioWeights n :=
  fun i => μ i - rf

/-- Copy of `expectedReturn`: `∑ i, wᵢ μᵢ`. -/
def expectedReturn (μ : portfolioWeights n) (w : portfolioWeights n) : ℝ :=
  ∑ i, w i * μ i

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

/-- Copy of `totalExpectedReturn`: `rf + wᵀ e`. -/
def totalExpectedReturn (μ : portfolioWeights n) (rf : ℝ) (w : portfolioWeights n) : ℝ :=
  rf + expectedReturn n (excessReturn n μ rf) w

/-- Copy of `rfFrontierPortfolio`: `w★ = ((m - rf) / eᵀΣ⁻¹e) · Σ⁻¹ e`. -/
noncomputable def rfFrontierPortfolio
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (rf m : ℝ) :
    portfolioWeights n :=
  ((m - rf) / sharpeSquared n covM μ rf)
    • covM⁻¹.mulVec (excessReturn n μ rf)

/-- **Risk-free frontier optimality** (solution): identical statement to the challenge,
proved by delegating to the library theorem. -/
theorem rfFrontierPortfolio_optimal
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (rf m : ℝ)
    (hcov : covM.PosDef)
    (he : excessReturn n μ rf ≠ 0) :
    ∀ w : portfolioWeights n,
      totalExpectedReturn n μ rf w = m →
      riskFreeVariance n covM (rfFrontierPortfolio n covM μ rf m)
        ≤ riskFreeVariance n covM w := by
  exact _root_.rfFrontierPortfolio_optimal n covM μ rf m hcov he

end MarkowitzFormalization.StatementAudit
