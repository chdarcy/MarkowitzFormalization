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

/-!
## Squared Sharpe ratio as a variance
-/

/-- The squared Sharpe ratio `eᵀ Σ⁻¹ e` is the risky variance of the vector
`Σ⁻¹ e`: since `Σ(Σ⁻¹e) = e`, we have `eᵀΣ⁻¹e = (Σ⁻¹e)ᵀ Σ (Σ⁻¹e)`. -/
theorem sharpeSquared_eq_portfolioVariance
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (rf : ℝ)
    (hcov : covM.PosDef) :
    sharpeSquared n covM μ rf
      = portfolioVariance n covM (covM⁻¹.mulVec (excessReturn n μ rf)) := by
  unfold sharpeSquared portfolioVariance
  rw [posDef_mulVec_inv_mulVec n hcov (excessReturn n μ rf)]
  exact dotProduct_comm _ _

/-- **Positivity of the squared Sharpe ratio**: when the excess-return vector is
nonzero (`μ ≠ rf·1`), `eᵀΣ⁻¹e > 0`. The single denominator the risk-free frontier
divides by is therefore strictly positive. -/
theorem sharpeSquared_pos
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (rf : ℝ)
    (hcov : covM.PosDef)
    (he : excessReturn n μ rf ≠ 0) :
    0 < sharpeSquared n covM μ rf := by
  set y := covM⁻¹.mulVec (excessReturn n μ rf) with hy
  have hkey : covM.mulVec y = excessReturn n μ rf :=
    posDef_mulVec_inv_mulVec n hcov (excessReturn n μ rf)
  have hyne : y ≠ 0 := by
    intro hzero
    apply he
    rw [← hkey, hzero, Matrix.mulVec_zero]
  rw [sharpeSquared_eq_portfolioVariance n covM μ rf hcov, ← hy]
  unfold portfolioVariance
  have hpos := hcov.dotProduct_mulVec_pos hyne
  simp only [star_trivial] at hpos
  exact hpos

/-- **Constraint satisfaction**: the risk-free frontier portfolio attains the target
total return `m`. Its expected excess return is `((m - rf)/eᵀΣ⁻¹e)·eᵀΣ⁻¹e = m - rf`,
so the total return is `rf + (m - rf) = m`. -/
theorem rfFrontierPortfolio_totalExpectedReturn
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (rf m : ℝ)
    (hcov : covM.PosDef)
    (he : excessReturn n μ rf ≠ 0) :
    totalExpectedReturn n μ rf (rfFrontierPortfolio n covM μ rf m) = m := by
  have hS : sharpeSquared n covM μ rf ≠ 0 := (sharpeSquared_pos n covM μ rf hcov he).ne'
  have hexp : expectedReturn n (excessReturn n μ rf) (covM⁻¹.mulVec (excessReturn n μ rf))
      = sharpeSquared n covM μ rf := by
    unfold expectedReturn sharpeSquared
    exact dotProduct_comm _ _
  unfold totalExpectedReturn rfFrontierPortfolio
  rw [expectedReturn_smul, hexp]
  field_simp
  ring

/-- **Variance closed form** (the Capital Market Line): the risk-free frontier
portfolio for target `m` has variance `(m - rf)² / eᵀΣ⁻¹e`. Since `w★ = a • Σ⁻¹e`
with `a = (m-rf)/S`, the quadratic form scales as `a² · S = (m-rf)²/S`. -/
theorem rfFrontierPortfolio_variance
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (rf m : ℝ)
    (hcov : covM.PosDef)
    (he : excessReturn n μ rf ≠ 0) :
    riskFreeVariance n covM (rfFrontierPortfolio n covM μ rf m)
      = (m - rf) ^ 2 / sharpeSquared n covM μ rf := by
  have hS : sharpeSquared n covM μ rf ≠ 0 := (sharpeSquared_pos n covM μ rf hcov he).ne'
  unfold riskFreeVariance rfFrontierPortfolio
  set a := (m - rf) / sharpeSquared n covM μ rf with ha
  set y := covM⁻¹.mulVec (excessReturn n μ rf) with hy
  have hvar : portfolioVariance n covM (a • y) = a ^ 2 * portfolioVariance n covM y := by
    unfold portfolioVariance
    rw [Matrix.mulVec_smul, smul_dotProduct,
      dotProduct_comm y (a • covM.mulVec y), smul_dotProduct,
      dotProduct_comm (covM.mulVec y) y]
    simp only [smul_eq_mul]
    ring
  have hSeq : portfolioVariance n covM y = sharpeSquared n covM μ rf := by
    rw [hy]
    exact (sharpeSquared_eq_portfolioVariance n covM μ rf hcov).symm
  rw [hvar, hSeq, ha]
  field_simp

/-!
## Optimality of the risk-free frontier portfolio
-/

/-- **Image under `Σ`**: since `w★ = a • Σ⁻¹e`, we have `Σ w★ = a • e`. This is the
keystone for the cross-term and optimality arguments. -/
theorem mulVec_rfFrontierPortfolio
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (rf m : ℝ)
    (hcov : covM.PosDef) :
    covM.mulVec (rfFrontierPortfolio n covM μ rf m)
      = ((m - rf) / sharpeSquared n covM μ rf) • excessReturn n μ rf := by
  unfold rfFrontierPortfolio
  rw [Matrix.mulVec_smul, posDef_mulVec_inv_mulVec n hcov (excessReturn n μ rf)]
