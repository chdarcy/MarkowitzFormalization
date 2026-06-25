import MarkowitzFormalization.Frontier

/-!
# Risk-Free Asset

The risky-asset Markowitz core (`Frontier.lean`) is extended with a single
risk-free asset paying a deterministic return `rf : ℝ`, which has zero variance
and zero covariance with the risky assets.

We use the **implicit cash-weight** model. A risky exposure vector
`w : portfolioWeights n` records only the risky-asset holdings; the risk-free
holding is the derived scalar `1 - ∑ i, w i`, so the risky weights are
unconstrained in sum. Total variance is then exactly the risky quadratic form
`portfolioVariance n covM w`, and the total expected return is
`rf + wᵀ(μ - rf·1)`.

Writing `e := μ - rf·1` for the excess-return vector, the relevant scalar is the
squared Sharpe ratio `eᵀ Σ⁻¹ e` (the CML slope²), and the risk-free frontier
portfolio is proportional to `Σ⁻¹ e`.
-/

open Finset Matrix

variable (n : Type) [Fintype n] [DecidableEq n]

/-- The **excess-return vector** `e = μ - rf·1`. -/
def excessReturn (μ : portfolioWeights n) (rf : ℝ) : portfolioWeights n :=
  fun i => μ i - rf

/-- The implicit **risk-free (cash) weight** `w₀ = 1 - ∑ i, w i`. -/
def riskFreeWeight (w : portfolioWeights n) : ℝ :=
  1 - ∑ i, w i

/-- The **total expected return** `rf + wᵀ e = rf·w₀ + wᵀμ`. -/
def totalExpectedReturn (μ : portfolioWeights n) (rf : ℝ) (w : portfolioWeights n) : ℝ :=
  rf + expectedReturn n (excessReturn n μ rf) w

/-- The **total variance** with a risk-free asset: the risk-free holding
contributes nothing, so this is just the risky quadratic form `wᵀ Σ w`. -/
def riskFreeVariance (covM : Matrix n n ℝ) (w : portfolioWeights n) : ℝ :=
  portfolioVariance n covM w

/-- The **squared Sharpe ratio** `eᵀ Σ⁻¹ e` (the slope² of the Capital Market Line). -/
noncomputable def sharpeSquared
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (rf : ℝ) : ℝ :=
  excessReturn n μ rf ⬝ᵥ covM⁻¹.mulVec (excessReturn n μ rf)

/-- The **risk-free frontier portfolio** for target return `m`:
`w★ = ((m - rf) / eᵀΣ⁻¹e) · Σ⁻¹ e`. -/
noncomputable def rfFrontierPortfolio
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (rf m : ℝ) :
    portfolioWeights n :=
  ((m - rf) / sharpeSquared n covM μ rf)
    • covM⁻¹.mulVec (excessReturn n μ rf)

/-- The **tangency normaliser** `1ᵀ Σ⁻¹ e = A - C·rf`. -/
noncomputable def tangencyDenominator
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (rf : ℝ) : ℝ :=
  onesVec n ⬝ᵥ covM⁻¹.mulVec (excessReturn n μ rf)

/-- The **tangency portfolio**: the fully invested risky portfolio on the CML,
`w_T = Σ⁻¹ e / (1ᵀ Σ⁻¹ e)`. -/
noncomputable def tangencyPortfolio
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (rf : ℝ) :
    portfolioWeights n :=
  (1 / tangencyDenominator n covM μ rf)
    • covM⁻¹.mulVec (excessReturn n μ rf)

/-!
## Unfolding lemmas
-/

omit [Fintype n] [DecidableEq n] in
theorem excessReturn_def (μ : portfolioWeights n) (rf : ℝ) (i : n) :
    excessReturn n μ rf i = μ i - rf :=
  rfl

omit [DecidableEq n] in
theorem riskFreeWeight_def (w : portfolioWeights n) :
    riskFreeWeight n w = 1 - ∑ i, w i :=
  rfl

omit [DecidableEq n] in
theorem totalExpectedReturn_def (μ : portfolioWeights n) (rf : ℝ) (w : portfolioWeights n) :
    totalExpectedReturn n μ rf w = rf + expectedReturn n (excessReturn n μ rf) w :=
  rfl

omit [DecidableEq n] in
theorem riskFreeVariance_def (covM : Matrix n n ℝ) (w : portfolioWeights n) :
    riskFreeVariance n covM w = portfolioVariance n covM w :=
  rfl

theorem rfFrontierPortfolio_def (covM : Matrix n n ℝ) (μ : portfolioWeights n) (rf m : ℝ) :
    rfFrontierPortfolio n covM μ rf m
      = ((m - rf) / sharpeSquared n covM μ rf) • covM⁻¹.mulVec (excessReturn n μ rf) :=
  rfl

theorem tangencyPortfolio_def (covM : Matrix n n ℝ) (μ : portfolioWeights n) (rf : ℝ) :
    tangencyPortfolio n covM μ rf
      = (1 / tangencyDenominator n covM μ rf) • covM⁻¹.mulVec (excessReturn n μ rf) :=
  rfl
