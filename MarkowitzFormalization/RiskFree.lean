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

/-- **Cross term vanishes**: if a deviation `z` has zero excess return
(`eᵀz = 0`), then it is `Σ`-orthogonal to the risk-free frontier portfolio,
because `Σ w★ = a • e` and so `zᵀ Σ w★ = a · (eᵀz) = 0`. -/
theorem rfFrontierPortfolio_cross_zero
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (rf m : ℝ)
    (z : portfolioWeights n)
    (hcov : covM.PosDef)
    (hz : expectedReturn n (excessReturn n μ rf) z = 0) :
    z ⬝ᵥ covM.mulVec (rfFrontierPortfolio n covM μ rf m) = 0 := by
  have hz' : z ⬝ᵥ excessReturn n μ rf = 0 := hz
  rw [mulVec_rfFrontierPortfolio n covM μ rf m hcov, dotProduct_comm z,
    smul_dotProduct, dotProduct_comm (excessReturn n μ rf) z, hz', smul_zero]

/-- **Feasible deviation has zero excess return**: if `w` attains total return `m`,
then so does the frontier portfolio `w★`, so their difference `w - w★` carries zero
expected excess return. This is the single linear condition the optimality argument
feeds into `rfFrontierPortfolio_cross_zero`. -/
theorem rf_feasible_deviation_expectedReturn_zero
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (rf m : ℝ)
    (hcov : covM.PosDef)
    (he : excessReturn n μ rf ≠ 0)
    (w : portfolioWeights n)
    (hw : totalExpectedReturn n μ rf w = m) :
    expectedReturn n (excessReturn n μ rf)
      (w - rfFrontierPortfolio n covM μ rf m) = 0 := by
  have hwexp : rf + expectedReturn n (excessReturn n μ rf) w = m := by
    rw [← totalExpectedReturn_def]; exact hw
  have hstar : rf + expectedReturn n (excessReturn n μ rf)
      (rfFrontierPortfolio n covM μ rf m) = m := by
    rw [← totalExpectedReturn_def]
    exact rfFrontierPortfolio_totalExpectedReturn n covM μ rf m hcov he
  have hsplit : rfFrontierPortfolio n covM μ rf m
      + (w - rfFrontierPortfolio n covM μ rf m) = w := by abel
  have hadd := expectedReturn_add n (excessReturn n μ rf)
    (rfFrontierPortfolio n covM μ rf m) (w - rfFrontierPortfolio n covM μ rf m)
  rw [hsplit] at hadd
  linarith

/-- **Optimality of the risk-free frontier portfolio**: among all risky exposure
vectors attaining total return `m`, the frontier portfolio `w★` has the least
variance. Writing any feasible `w = w★ + z`, the deviation `z` carries zero excess
return, hence is `Σ`-orthogonal to `w★`, so `Var w = Var w★ + Var z ≥ Var w★`. -/
theorem rfFrontierPortfolio_optimal
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (rf m : ℝ)
    (hcov : covM.PosDef)
    (he : excessReturn n μ rf ≠ 0) :
    ∀ w : portfolioWeights n,
      totalExpectedReturn n μ rf w = m →
      riskFreeVariance n covM (rfFrontierPortfolio n covM μ rf m)
        ≤ riskFreeVariance n covM w := by
  intro w hw
  have hzret := rf_feasible_deviation_expectedReturn_zero n covM μ rf m hcov he w hw
  have hcross := rfFrontierPortfolio_cross_zero n covM μ rf m
    (w - rfFrontierPortfolio n covM μ rf m) hcov hzret
  have hadd := portfolioVariance_add_of_cross_zero n covM
    (rfFrontierPortfolio n covM μ rf m) (w - rfFrontierPortfolio n covM μ rf m) hcov hcross
  have hsplit : rfFrontierPortfolio n covM μ rf m
      + (w - rfFrontierPortfolio n covM μ rf m) = w := by abel
  rw [hsplit] at hadd
  have hznn := portfolioVariance_nonneg n covM hcov.posSemidef
    (w - rfFrontierPortfolio n covM μ rf m)
  unfold riskFreeVariance
  linarith

/-- **Uniqueness of the risk-free frontier optimiser**: any risky exposure vector
attaining return `m` with the minimal variance must equal `w★`. The deviation
`z = w - w★` is `Σ`-orthogonal to `w★`, so equal variances force `Var z = 0`, and
positive-definiteness gives `z = 0`. -/
theorem rfFrontierPortfolio_unique
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (rf m : ℝ)
    (hcov : covM.PosDef)
    (he : excessReturn n μ rf ≠ 0)
    (w : portfolioWeights n)
    (hw : totalExpectedReturn n μ rf w = m)
    (hopt :
      riskFreeVariance n covM w
        = riskFreeVariance n covM (rfFrontierPortfolio n covM μ rf m)) :
    w = rfFrontierPortfolio n covM μ rf m := by
  have hzret := rf_feasible_deviation_expectedReturn_zero n covM μ rf m hcov he w hw
  have hcross := rfFrontierPortfolio_cross_zero n covM μ rf m
    (w - rfFrontierPortfolio n covM μ rf m) hcov hzret
  have hadd := portfolioVariance_add_of_cross_zero n covM
    (rfFrontierPortfolio n covM μ rf m) (w - rfFrontierPortfolio n covM μ rf m) hcov hcross
  have hsplit : rfFrontierPortfolio n covM μ rf m
      + (w - rfFrontierPortfolio n covM μ rf m) = w := by abel
  rw [hsplit] at hadd
  rw [riskFreeVariance_def, riskFreeVariance_def] at hopt
  have hVarz : portfolioVariance n covM (w - rfFrontierPortfolio n covM μ rf m) = 0 := by
    linarith
  have hz0 : w - rfFrontierPortfolio n covM μ rf m = 0 :=
    portfolioVariance_eq_zero_of_posDef n covM hcov _ hVarz
  exact sub_eq_zero.mp hz0

/-!
## Tangency portfolio basics
-/

omit [Fintype n] [DecidableEq n] in
/-- The **excess-return vector** as a vector difference: `e = μ - rf·1`. This recasts
`excessReturn` so the `Σ⁻¹`/dot-product linearity lemmas can split the tangency
denominator into the frontier scalars `A` and `C`. -/
theorem excessReturn_eq_sub_smul_ones (μ : portfolioWeights n) (rf : ℝ) :
    excessReturn n μ rf = μ - rf • onesVec n := by
  funext i
  simp [excessReturn, onesVec]

/-- **Tangency denominator in frontier scalars**: `1ᵀΣ⁻¹e = A - rf·C`. Splitting
`e = μ - rf·1` through the linearity of `Σ⁻¹·` and the dot product gives
`1ᵀΣ⁻¹μ - rf·(1ᵀΣ⁻¹1) = A - rf·C`. -/
theorem tangencyDenominator_eq_frontierA_sub_rf_frontierC
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (rf : ℝ) :
    tangencyDenominator n covM μ rf
      = frontierA n covM μ - rf * frontierC n covM := by
  unfold tangencyDenominator frontierA frontierC
  rw [excessReturn_eq_sub_smul_ones, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub,
    dotProduct_comm (onesVec n) (rf • covM⁻¹.mulVec (onesVec n)), smul_dotProduct,
    dotProduct_comm (covM⁻¹.mulVec (onesVec n)) (onesVec n), smul_eq_mul]

/-- **Expected excess return of the tangency portfolio**: `eᵀ w_T = S / (1ᵀΣ⁻¹e)`.
Since `w_T = (1/D)·Σ⁻¹e` with `D = 1ᵀΣ⁻¹e`, its expected excess return is
`(1/D)·(eᵀΣ⁻¹e) = S/D`. This holds unconditionally — if `D = 0` both sides are `0`. -/
theorem tangencyPortfolio_expectedExcessReturn
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (rf : ℝ) :
    expectedReturn n (excessReturn n μ rf)
      (tangencyPortfolio n covM μ rf)
      =
    sharpeSquared n covM μ rf / tangencyDenominator n covM μ rf := by
  have hexp : expectedReturn n (excessReturn n μ rf)
      (covM⁻¹.mulVec (excessReturn n μ rf)) = sharpeSquared n covM μ rf := by
    unfold expectedReturn sharpeSquared
    exact dotProduct_comm _ _
  unfold tangencyPortfolio
  rw [expectedReturn_smul, hexp]
  ring

/-- **Tangency portfolio is fully invested**: when the tangency denominator is
nonzero, the risky weights sum to `1` (so the implicit cash weight is `0`). Since
`w_T = (1/D)·Σ⁻¹e` and `1ᵀΣ⁻¹e = D`, the total risky weight is `(1/D)·D = 1`. -/
theorem tangencyPortfolio_budget
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (rf : ℝ)
    (hD : tangencyDenominator n covM μ rf ≠ 0) :
    expectedReturn n (onesVec n) (tangencyPortfolio n covM μ rf) = 1 := by
  have hD' : expectedReturn n (onesVec n)
      (covM⁻¹.mulVec (excessReturn n μ rf)) = tangencyDenominator n covM μ rf := by
    unfold expectedReturn tangencyDenominator
    exact dotProduct_comm _ _
  unfold tangencyPortfolio
  rw [expectedReturn_smul, hD']
  field_simp

omit [DecidableEq n] in
/-- **Total risky weight as an expected return**: `1ᵀ w = ∑ i, w i`. Reading the
expected return against the all-ones vector recovers the total risky weight, the
quantity the implicit cash weight `riskFreeWeight` completes to `1`. -/
theorem expectedReturn_onesVec_eq_sum (w : portfolioWeights n) :
    expectedReturn n (onesVec n) w = ∑ i, w i := by
  unfold expectedReturn onesVec
  simp

/-- **Tangency portfolio holds no cash**: the implicit risk-free weight of the
tangency portfolio is `0` (it is fully invested in risky assets). Immediate from
`riskFreeWeight = 1 - ∑ wᵢ` and the budget normalisation `∑ wᵢ = 1`. -/
theorem tangencyPortfolio_riskFreeWeight_zero
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (rf : ℝ)
    (hD : tangencyDenominator n covM μ rf ≠ 0) :
    riskFreeWeight n (tangencyPortfolio n covM μ rf) = 0 := by
  unfold riskFreeWeight
  rw [← expectedReturn_onesVec_eq_sum, tangencyPortfolio_budget n covM μ rf hD]
  ring

/-- **One-fund separation**: every risk-free frontier portfolio is a scalar multiple
of the single tangency portfolio. Both `w★` and `w_T` are multiples of `Σ⁻¹e`, so
`w★ = ((m - rf)·D / S) • w_T`, with `D = 1ᵀΣ⁻¹e`. Pure algebra — needs only `D ≠ 0`. -/
theorem rfFrontierPortfolio_one_fund
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (rf m : ℝ)
    (hD : tangencyDenominator n covM μ rf ≠ 0) :
    rfFrontierPortfolio n covM μ rf m
      =
    (((m - rf) * tangencyDenominator n covM μ rf)
      / sharpeSquared n covM μ rf)
      • tangencyPortfolio n covM μ rf := by
  unfold rfFrontierPortfolio tangencyPortfolio
  rw [smul_smul]
  congr 1
  field_simp
