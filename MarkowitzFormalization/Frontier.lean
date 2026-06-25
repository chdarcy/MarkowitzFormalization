import MarkowitzFormalization.Portfolio

/-!
# Frontier

Frontier scalars `A`, `B`, `C`, `D` for the Markowitz minimum-variance problem.

Following the lecture notes, with `Σ` the covariance matrix and `μ` the mean
vector, these are
```
A = 1ᵀ Σ⁻¹ μ,   B = μᵀ Σ⁻¹ μ,   C = 1ᵀ Σ⁻¹ 1,   D = B C - A².
```
-/

open Matrix

variable (n : Type) [Fintype n] [DecidableEq n]

/-- The all-ones vector in `portfolioWeights n`. -/
def onesVec : portfolioWeights n :=
  fun _ => 1

/-- `A = 1ᵀ Σ⁻¹ μ`. -/
noncomputable def frontierA (covM : Matrix n n ℝ) (μ : portfolioWeights n) : ℝ :=
  onesVec n ⬝ᵥ covM⁻¹.mulVec μ

/-- `B = μᵀ Σ⁻¹ μ`. -/
noncomputable def frontierB (covM : Matrix n n ℝ) (μ : portfolioWeights n) : ℝ :=
  μ ⬝ᵥ covM⁻¹.mulVec μ

/-- `C = 1ᵀ Σ⁻¹ 1`. -/
noncomputable def frontierC (covM : Matrix n n ℝ) : ℝ :=
  onesVec n ⬝ᵥ covM⁻¹.mulVec (onesVec n)

/-- `D = B C - A²`. -/
noncomputable def frontierD (covM : Matrix n n ℝ) (μ : portfolioWeights n) : ℝ :=
  frontierB n covM μ * frontierC n covM - (frontierA n covM μ) ^ 2

/-- `λ(m) = (C m - A) / D`. -/
noncomputable def frontierLambda (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ) : ℝ :=
  (frontierC n covM * m - frontierA n covM μ) / frontierD n covM μ

/-- `γ(m) = (B - A m) / D`. -/
noncomputable def frontierGamma (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ) : ℝ :=
  (frontierB n covM μ - frontierA n covM μ * m) / frontierD n covM μ

/-- `w★(m) = λ(m) Σ⁻¹ μ + γ(m) Σ⁻¹ 1`. -/
noncomputable def frontierPortfolio (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ) :
    portfolioWeights n :=
  frontierLambda n covM μ m • covM⁻¹.mulVec μ +
    frontierGamma n covM μ m • covM⁻¹.mulVec (onesVec n)

/-!
## Inverse helper lemmas

Under `covM.PosDef` the determinant is positive, hence a unit, so `covM⁻¹` is a
genuine two-sided inverse. We expose this both as matrix identities and in the
`mulVec` form used by the portfolio definitions.
-/

/-- A positive definite covariance matrix has a unit determinant. -/
theorem isUnit_det_of_posDef {covM : Matrix n n ℝ} (hcov : covM.PosDef) :
    IsUnit covM.det :=
  (Matrix.PosDef.det_pos hcov).ne'.isUnit

theorem posDef_mul_inv {covM : Matrix n n ℝ} (hcov : covM.PosDef) :
    covM * covM⁻¹ = 1 :=
  Matrix.mul_nonsing_inv covM (isUnit_det_of_posDef n hcov)

theorem posDef_inv_mul {covM : Matrix n n ℝ} (hcov : covM.PosDef) :
    covM⁻¹ * covM = 1 :=
  Matrix.nonsing_inv_mul covM (isUnit_det_of_posDef n hcov)

theorem posDef_mulVec_inv_mulVec {covM : Matrix n n ℝ} (hcov : covM.PosDef)
    (x : portfolioWeights n) :
    covM.mulVec (covM⁻¹.mulVec x) = x := by
  rw [Matrix.mulVec_mulVec, posDef_mul_inv n hcov, Matrix.one_mulVec]

theorem posDef_inv_mulVec_mulVec {covM : Matrix n n ℝ} (hcov : covM.PosDef)
    (x : portfolioWeights n) :
    covM⁻¹.mulVec (covM.mulVec x) = x := by
  rw [Matrix.mulVec_mulVec, posDef_inv_mul n hcov, Matrix.one_mulVec]

/-- The inverse of a positive definite (hence Hermitian, hence over `ℝ` symmetric)
matrix is symmetric. -/
theorem covInv_transpose {covM : Matrix n n ℝ} (hcov : covM.PosDef) :
    (covM⁻¹)ᵀ = covM⁻¹ := by
  have hsymm : covMᵀ = covM := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hcov.1.eq
  rw [Matrix.transpose_nonsing_inv, hsymm]

/-- Symmetry of the `Σ⁻¹`-bilinear form: `xᵀ Σ⁻¹ y = yᵀ Σ⁻¹ x`. -/
theorem dotProduct_covInv_symm {covM : Matrix n n ℝ} (hcov : covM.PosDef)
    (x y : portfolioWeights n) :
    x ⬝ᵥ covM⁻¹.mulVec y = y ⬝ᵥ covM⁻¹.mulVec x := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, covInv_transpose n hcov,
    dotProduct_comm]

omit [DecidableEq n] in
/-- Symmetry of the `Σ`-bilinear form: `xᵀ Σ y = yᵀ Σ x` (for symmetric, hence positive
definite, `Σ`). -/
theorem cov_dotProduct_symm (covM : Matrix n n ℝ) (hcov : covM.PosDef)
    (x y : portfolioWeights n) :
    x ⬝ᵥ covM.mulVec y = y ⬝ᵥ covM.mulVec x := by
  have hsymm : covMᵀ = covM := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hcov.1.eq
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, dotProduct_comm]

/-!
## The `Σ⁻¹` bilinear form

`innerCov covM x y = xᵀ Σ⁻¹ y` packages the inverse-covariance bilinear form, the
inner product underlying the Cauchy–Schwarz argument for `D > 0`.
-/

/-- The bilinear form `⟨x, y⟩ = xᵀ Σ⁻¹ y` induced by the inverse covariance matrix. -/
noncomputable def innerCov (covM : Matrix n n ℝ) (x y : portfolioWeights n) : ℝ :=
  x ⬝ᵥ covM⁻¹.mulVec y

/-- The `Σ⁻¹` form is symmetric (for positive definite, hence symmetric, `Σ`). -/
theorem innerCov_symm {covM : Matrix n n ℝ} (hcov : covM.PosDef)
    (x y : portfolioWeights n) :
    innerCov n covM x y = innerCov n covM y x :=
  dotProduct_covInv_symm n hcov x y

/-- Left scalar homogeneity. -/
theorem innerCov_smul_left {covM : Matrix n n ℝ} (a : ℝ) (x y : portfolioWeights n) :
    innerCov n covM (a • x) y = a * innerCov n covM x y := by
  unfold innerCov
  rw [smul_dotProduct, smul_eq_mul]

/-- Left additivity. -/
theorem innerCov_add_left {covM : Matrix n n ℝ} (x₁ x₂ y : portfolioWeights n) :
    innerCov n covM (x₁ + x₂) y = innerCov n covM x₁ y + innerCov n covM x₂ y := by
  unfold innerCov
  rw [add_dotProduct]

/-- Right scalar homogeneity, via symmetry and left homogeneity. -/
theorem innerCov_smul_right {covM : Matrix n n ℝ} (hcov : covM.PosDef)
    (a : ℝ) (x y : portfolioWeights n) :
    innerCov n covM x (a • y) = a * innerCov n covM x y := by
  rw [innerCov_symm n hcov x (a • y), innerCov_smul_left, innerCov_symm n hcov y x]

/-- Right additivity, via symmetry and left additivity. -/
theorem innerCov_add_right {covM : Matrix n n ℝ} (hcov : covM.PosDef)
    (x y₁ y₂ : portfolioWeights n) :
    innerCov n covM x (y₁ + y₂) = innerCov n covM x y₁ + innerCov n covM x y₂ := by
  rw [innerCov_symm n hcov x (y₁ + y₂), innerCov_add_left, innerCov_symm n hcov y₁ x,
    innerCov_symm n hcov y₂ x]

/-! ### Scalar identification: the `Σ⁻¹` form recovers `A`, `B`, `C`. -/

/-- `⟨1, μ⟩ = A`. -/
theorem innerCov_ones_left (covM : Matrix n n ℝ) (μ : portfolioWeights n) :
    innerCov n covM (onesVec n) μ = frontierA n covM μ :=
  rfl

/-- `⟨μ, 1⟩ = A`, via symmetry. -/
theorem innerCov_mu_ones {covM : Matrix n n ℝ} (hcov : covM.PosDef)
    (μ : portfolioWeights n) :
    innerCov n covM μ (onesVec n) = frontierA n covM μ := by
  rw [innerCov_symm n hcov]
  rfl

/-- `⟨μ, μ⟩ = B`. -/
theorem innerCov_mu_mu (covM : Matrix n n ℝ) (μ : portfolioWeights n) :
    innerCov n covM μ μ = frontierB n covM μ :=
  rfl

/-- `⟨1, 1⟩ = C`. -/
theorem innerCov_ones_ones (covM : Matrix n n ℝ) :
    innerCov n covM (onesVec n) (onesVec n) = frontierC n covM :=
  rfl

/-- The discriminant expansion: `⟨Cμ − A·1, Cμ − A·1⟩ = C · D`. -/
theorem innerCov_frontierVec {covM : Matrix n n ℝ} (hcov : covM.PosDef)
    (μ : portfolioWeights n) :
    innerCov n covM
        (frontierC n covM • μ - frontierA n covM μ • onesVec n)
        (frontierC n covM • μ - frontierA n covM μ • onesVec n)
      = frontierC n covM * frontierD n covM μ := by
  -- First distribute the bilinear form fully into the four basis pairings.
  simp only [sub_eq_add_neg, ← neg_smul, innerCov_add_left, innerCov_add_right n hcov,
    innerCov_smul_left, innerCov_smul_right n hcov]
  -- Then identify each basis pairing with A, B, C (⟨1,1⟩ before the general ⟨1,·⟩ rule).
  rw [innerCov_mu_mu, innerCov_ones_ones, innerCov_mu_ones n hcov, innerCov_ones_left]
  unfold frontierD
  ring

/-! ### Positivity of `C` -/

omit [Fintype n] [DecidableEq n] in
/-- The all-ones vector is nonzero on a nonempty index set. -/
theorem onesVec_ne_zero [Nonempty n] : onesVec n ≠ 0 := by
  intro h
  have hi := congrFun h (Classical.arbitrary n)
  simp [onesVec] at hi

/-- `C = 1ᵀ Σ⁻¹ 1 > 0`, since `Σ⁻¹` is positive definite and `1 ≠ 0`. -/
theorem frontierC_pos (covM : Matrix n n ℝ) (hcov : covM.PosDef) [Nonempty n] :
    0 < frontierC n covM := by
  have h := hcov.inv.dotProduct_mulVec_pos (onesVec_ne_zero n)
  simpa [frontierC, star_trivial] using h

/-! ### Non-negativity of `D` -/

/-- `D = B·C − A² ≥ 0`: the discriminant vector `v = Cμ − A·1` satisfies
`⟨v, v⟩ = C·D ≥ 0` by positive semidefiniteness, and `C > 0`. -/
theorem frontierD_nonneg (covM : Matrix n n ℝ) (μ : portfolioWeights n)
    (market : NonDegenerateMarket n μ covM) [Nonempty n] :
    0 ≤ frontierD n covM μ := by
  have hcov := market.posDef
  have hCD : 0 ≤ frontierC n covM * frontierD n covM μ := by
    rw [← innerCov_frontierVec n hcov]
    have h := hcov.inv.posSemidef.dotProduct_mulVec_nonneg
      (frontierC n covM • μ - frontierA n covM μ • onesVec n)
    simpa [innerCov, star_trivial] using h
  have hC := frontierC_pos n covM hcov
  nlinarith [hCD, hC]

/-! ### Equality case: `v = 0` forces `μ` constant -/

/-- If the discriminant vector `Cμ − A·1` vanishes (with `C ≠ 0`), then `μ` is the
constant vector `A/C`, i.e. proportional to `1`. -/
theorem frontierVec_eq_zero_implies_mu_constant
    (covM : Matrix n n ℝ) (μ : portfolioWeights n)
    (hC : frontierC n covM ≠ 0)
    (hvec : frontierC n covM • μ - frontierA n covM μ • onesVec n = 0) :
    ∃ c : ℝ, μ = fun _ => c := by
  refine ⟨frontierA n covM μ / frontierC n covM, ?_⟩
  funext i
  show μ i = frontierA n covM μ / frontierC n covM
  have hi := congrFun hvec i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, onesVec, Pi.zero_apply, mul_one] at hi
  rw [eq_div_iff hC]
  linear_combination hi

/-! ### `D ≠ 0` -/

/-- `D ≠ 0` on a non-degenerate market: if `D = 0` then `⟨v, v⟩ = C·D = 0`, forcing
the discriminant vector `v` to vanish, hence `μ` constant — contradicting
non-proportionality. -/
theorem frontierD_ne_zero (covM : Matrix n n ℝ) (μ : portfolioWeights n)
    (market : NonDegenerateMarket n μ covM) [Nonempty n] :
    frontierD n covM μ ≠ 0 := by
  have hcov := market.posDef
  intro hD0
  have hvv : innerCov n covM
      (frontierC n covM • μ - frontierA n covM μ • onesVec n)
      (frontierC n covM • μ - frontierA n covM μ • onesVec n) = 0 := by
    rw [innerCov_frontierVec n hcov, hD0, mul_zero]
  have hvec : frontierC n covM • μ - frontierA n covM μ • onesVec n = 0 := by
    by_contra hne
    have hpos := hcov.inv.dotProduct_mulVec_pos hne
    have hpos' : (0 : ℝ) < innerCov n covM
        (frontierC n covM • μ - frontierA n covM μ • onesVec n)
        (frontierC n covM • μ - frontierA n covM μ • onesVec n) := by
      simpa [innerCov, star_trivial] using hpos
    rw [hvv] at hpos'
    exact lt_irrefl 0 hpos'
  have hCne : frontierC n covM ≠ 0 := (frontierC_pos n covM hcov).ne'
  obtain ⟨c, hc⟩ := frontierVec_eq_zero_implies_mu_constant n covM μ hCne hvec
  exact market.not_proportional ⟨c, hc⟩

/-- `D = B·C − A² > 0` on a non-degenerate market: it is non-negative and nonzero. -/
theorem frontierD_pos (covM : Matrix n n ℝ) (μ : portfolioWeights n)
    (market : NonDegenerateMarket n μ covM) [Nonempty n] :
    0 < frontierD n covM μ :=
  (frontierD_nonneg n covM μ market).lt_of_ne (frontierD_ne_zero n covM μ market).symm

/-!
## The Markowitz minimum-variance problem
-/

/-- Portfolios achieving a target expected return `m`. -/
def targetReturnSet (μ : portfolioWeights n) (m : ℝ) : Set (portfolioWeights n) :=
  {w | expectedReturn n μ w = m}

/-- Feasible portfolios: fully invested with target expected return `m`. -/
def feasibleSet (μ : portfolioWeights n) (m : ℝ) : Set (portfolioWeights n) :=
  {w | w ∈ budgetSet n ∧ expectedReturn n μ w = m}

/-- The Markowitz objective `½ wᵀ Σ w`. -/
noncomputable def markowitzObjective (covM : Matrix n n ℝ) (w : portfolioWeights n) : ℝ :=
  (1 / 2 : ℝ) * portfolioVariance n covM w

/-- A portfolio is Markowitz-optimal for target `m` if it is feasible and minimises
the objective over the feasible set. -/
def markowitzOptimal (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ)
    (w : portfolioWeights n) : Prop :=
  w ∈ feasibleSet n μ m ∧
    ∀ v ∈ feasibleSet n μ m, markowitzObjective n covM w ≤ markowitzObjective n covM v

/-!
## Unfolding lemmas
-/

omit [DecidableEq n] in
theorem mem_targetReturnSet (μ : portfolioWeights n) (m : ℝ) (w : portfolioWeights n) :
    w ∈ targetReturnSet n μ m ↔ expectedReturn n μ w = m :=
  Iff.rfl

omit [DecidableEq n] in
theorem mem_feasibleSet (μ : portfolioWeights n) (m : ℝ) (w : portfolioWeights n) :
    w ∈ feasibleSet n μ m ↔ w ∈ budgetSet n ∧ expectedReturn n μ w = m :=
  Iff.rfl

omit [DecidableEq n] in
theorem markowitzObjective_def (covM : Matrix n n ℝ) (w : portfolioWeights n) :
    markowitzObjective n covM w = (1 / 2 : ℝ) * portfolioVariance n covM w :=
  rfl

omit [DecidableEq n] in
theorem markowitzOptimal_def (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ)
    (w : portfolioWeights n) :
    markowitzOptimal n covM μ m w ↔
      w ∈ feasibleSet n μ m ∧
        ∀ v ∈ feasibleSet n μ m, markowitzObjective n covM w ≤ markowitzObjective n covM v :=
  Iff.rfl

theorem frontierLambda_def (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ) :
    frontierLambda n covM μ m =
      (frontierC n covM * m - frontierA n covM μ) / frontierD n covM μ :=
  rfl

theorem frontierGamma_def (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ) :
    frontierGamma n covM μ m =
      (frontierB n covM μ - frontierA n covM μ * m) / frontierD n covM μ :=
  rfl

theorem frontierPortfolio_def (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ) :
    frontierPortfolio n covM μ m =
      frontierLambda n covM μ m • covM⁻¹.mulVec μ +
        frontierGamma n covM μ m • covM⁻¹.mulVec (onesVec n) :=
  rfl

theorem frontierD_eq (covM : Matrix n n ℝ) (μ : portfolioWeights n) :
    frontierD n covM μ =
      frontierB n covM μ * frontierC n covM - frontierA n covM μ ^ 2 :=
  rfl

/-!
## Constraint satisfaction for the frontier portfolio
-/

/-- The frontier portfolio attains its target expected return. -/
theorem frontierPortfolio_expectedReturn (covM : Matrix n n ℝ) (μ : portfolioWeights n)
    (m : ℝ) (hcov : covM.PosDef) (hD : frontierD n covM μ ≠ 0) :
    expectedReturn n μ (frontierPortfolio n covM μ m) = m := by
  change frontierPortfolio n covM μ m ⬝ᵥ μ = m
  have hp : covM⁻¹.mulVec μ ⬝ᵥ μ = frontierB n covM μ := by
    unfold frontierB; rw [dotProduct_comm]
  have hq : covM⁻¹.mulVec (onesVec n) ⬝ᵥ μ = frontierA n covM μ := by
    unfold frontierA; rw [dotProduct_comm, dotProduct_covInv_symm n hcov]
  rw [frontierPortfolio_def, add_dotProduct, smul_dotProduct, smul_dotProduct,
    smul_eq_mul, smul_eq_mul, hp, hq, frontierLambda_def, frontierGamma_def]
  field_simp [hD]
  rw [frontierD_eq]
  ring

/-- The frontier portfolio is fully invested (lies in the budget set). -/
theorem frontierPortfolio_budget (covM : Matrix n n ℝ) (μ : portfolioWeights n)
    (m : ℝ) (hD : frontierD n covM μ ≠ 0) :
    frontierPortfolio n covM μ m ∈ budgetSet n := by
  change ∑ i, frontierPortfolio n covM μ m i = 1
  have hsum : ∑ i, frontierPortfolio n covM μ m i
      = frontierPortfolio n covM μ m ⬝ᵥ onesVec n := by
    simp [dotProduct, onesVec]
  have hA : covM⁻¹.mulVec μ ⬝ᵥ onesVec n = frontierA n covM μ := by
    unfold frontierA; rw [dotProduct_comm]
  have hC : covM⁻¹.mulVec (onesVec n) ⬝ᵥ onesVec n = frontierC n covM := by
    unfold frontierC; rw [dotProduct_comm]
  rw [hsum, frontierPortfolio_def, add_dotProduct, smul_dotProduct, smul_dotProduct,
    smul_eq_mul, smul_eq_mul, hA, hC, frontierLambda_def, frontierGamma_def]
  field_simp [hD]
  rw [frontierD_eq]
  ring

/-- The frontier portfolio is feasible for target return `m`: it satisfies both the
budget and the target-return constraints. -/
theorem frontierPortfolio_feasible (covM : Matrix n n ℝ) (μ : portfolioWeights n)
    (m : ℝ) (hcov : covM.PosDef) (hD : frontierD n covM μ ≠ 0) :
    frontierPortfolio n covM μ m ∈ feasibleSet n μ m :=
  ⟨frontierPortfolio_budget n covM μ m hD,
    frontierPortfolio_expectedReturn n covM μ m hcov hD⟩

/-! ### Market wrappers (discharging `hD` via `frontierD_pos`) -/

/-- On a non-degenerate market the frontier portfolio attains target return `m`,
with the `D ≠ 0` hypothesis discharged by `frontierD_pos`. -/
theorem frontierPortfolio_expectedReturn_of_market (covM : Matrix n n ℝ)
    (μ : portfolioWeights n) (m : ℝ) (market : NonDegenerateMarket n μ covM) [Nonempty n] :
    expectedReturn n μ (frontierPortfolio n covM μ m) = m :=
  frontierPortfolio_expectedReturn n covM μ m market.posDef
    (frontierD_pos n covM μ market).ne'

/-- On a non-degenerate market the frontier portfolio is fully invested. -/
theorem frontierPortfolio_budget_of_market (covM : Matrix n n ℝ)
    (μ : portfolioWeights n) (m : ℝ) (market : NonDegenerateMarket n μ covM) [Nonempty n] :
    frontierPortfolio n covM μ m ∈ budgetSet n :=
  frontierPortfolio_budget n covM μ m (frontierD_pos n covM μ market).ne'

/-- On a non-degenerate market the frontier portfolio is feasible for target `m`. -/
theorem frontierPortfolio_feasible_of_market (covM : Matrix n n ℝ)
    (μ : portfolioWeights n) (m : ℝ) (market : NonDegenerateMarket n μ covM) [Nonempty n] :
    frontierPortfolio n covM μ m ∈ feasibleSet n μ m :=
  frontierPortfolio_feasible n covM μ m market.posDef
    (frontierD_pos n covM μ market).ne'

/-! ### Optimality helpers -/

/-- The covariance matrix applied to the frontier portfolio: `Σ w★ = λ·μ + γ·1`,
since `Σ (Σ⁻¹ x) = x`. -/
theorem mulVec_frontierPortfolio (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ)
    (hcov : covM.PosDef) :
    covM.mulVec (frontierPortfolio n covM μ m)
      = frontierLambda n covM μ m • μ + frontierGamma n covM μ m • onesVec n := by
  rw [frontierPortfolio_def, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    posDef_mulVec_inv_mulVec n hcov, posDef_mulVec_inv_mulVec n hcov]

omit [DecidableEq n] in
/-- Variance is additive across `w` and `z` when their `Σ`-cross term vanishes
(`z ⬝ᵥ Σ w = 0`): `var(w + z) = var w + var z`. The two cross terms agree by symmetry
of the `Σ`-form and both vanish. -/
theorem portfolioVariance_add_of_cross_zero
    (covM : Matrix n n ℝ) (w z : portfolioWeights n)
    (hcov : covM.PosDef)
    (hcross : z ⬝ᵥ covM.mulVec w = 0) :
    portfolioVariance n covM (w + z)
      = portfolioVariance n covM w + portfolioVariance n covM z := by
  unfold portfolioVariance
  rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
    cov_dotProduct_symm n covM hcov w z, hcross]
  ring

/-- A deviation `z` with zero expected return and zero budget has vanishing `Σ`-cross
term against the frontier portfolio: `z ⬝ᵥ Σ w★ = λ·(μ⬝ᵥz) + γ·(1⬝ᵥz) = 0`. -/
theorem frontierPortfolio_cross_zero
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ)
    (z : portfolioWeights n) (hcov : covM.PosDef)
    (hzret : expectedReturn n μ z = 0)
    (hzbud : ∑ i, z i = 0) :
    z ⬝ᵥ covM.mulVec (frontierPortfolio n covM μ m) = 0 := by
  rw [mulVec_frontierPortfolio n covM μ m hcov, dotProduct_comm, add_dotProduct,
    smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  have h1 : μ ⬝ᵥ z = 0 := by rw [dotProduct_comm]; exact hzret
  have h2 : onesVec n ⬝ᵥ z = 0 := by
    simp only [dotProduct, onesVec, one_mul]
    exact hzbud
  rw [h1, h2]
  ring

/-- A feasible `v` deviates from the frontier portfolio with zero excess return:
`expectedReturn μ (v − w★) = m − m = 0`. -/
theorem feasible_deviation_expectedReturn_zero
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ)
    (market : NonDegenerateMarket n μ covM) [Nonempty n]
    (v : portfolioWeights n)
    (hv : v ∈ feasibleSet n μ m) :
    expectedReturn n μ (v - frontierPortfolio n covM μ m) = 0 := by
  obtain ⟨_, hvret⟩ := (mem_feasibleSet n μ m v).mp hv
  have hwret : expectedReturn n μ (frontierPortfolio n covM μ m) = m :=
    frontierPortfolio_expectedReturn_of_market n covM μ m market
  have hsplit : expectedReturn n μ (v - frontierPortfolio n covM μ m)
      = expectedReturn n μ v - expectedReturn n μ (frontierPortfolio n covM μ m) := by
    simp only [expectedReturn, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  rw [hsplit, hvret, hwret]
  ring

/-- A feasible `v` deviates from the frontier portfolio with zero net budget:
`∑ (v − w★) = 1 − 1 = 0`. -/
theorem feasible_deviation_budget_zero
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ)
    (market : NonDegenerateMarket n μ covM) [Nonempty n]
    (v : portfolioWeights n)
    (hv : v ∈ feasibleSet n μ m) :
    ∑ i, (v - frontierPortfolio n covM μ m) i = 0 := by
  obtain ⟨hvbud, _⟩ := (mem_feasibleSet n μ m v).mp hv
  have hvsum : ∑ i, v i = 1 := hvbud
  have hwsum : ∑ i, frontierPortfolio n covM μ m i = 1 :=
    frontierPortfolio_budget_of_market n covM μ m market
  simp only [Pi.sub_apply, Finset.sum_sub_distrib]
  rw [hvsum, hwsum]
  ring

/-- **Optimality of the frontier portfolio.** In a non-degenerate market the frontier
portfolio minimises variance (equivalently the Markowitz objective) over all feasible
portfolios with the prescribed expected return `m`. The proof completes the square:
any feasible `v` writes as `w★ + z` with `z` of zero excess return and zero budget, so
the `Σ`-cross term vanishes and `var v = var w★ + var z ≥ var w★`. -/
theorem frontierPortfolio_optimal_of_market
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ)
    (market : NonDegenerateMarket n μ covM) [Nonempty n] :
    markowitzOptimal n covM μ m (frontierPortfolio n covM μ m) := by
  refine ⟨frontierPortfolio_feasible_of_market n covM μ m market, ?_⟩
  intro v hv
  set z := v - frontierPortfolio n covM μ m with hz
  have hzret : expectedReturn n μ z = 0 :=
    feasible_deviation_expectedReturn_zero n covM μ m market v hv
  have hzbud : ∑ i, z i = 0 :=
    feasible_deviation_budget_zero n covM μ m market v hv
  have hcross : z ⬝ᵥ covM.mulVec (frontierPortfolio n covM μ m) = 0 :=
    frontierPortfolio_cross_zero n covM μ m z market.posDef hzret hzbud
  have hvwz : v = frontierPortfolio n covM μ m + z := by rw [hz]; abel
  have hvar : portfolioVariance n covM v
      = portfolioVariance n covM (frontierPortfolio n covM μ m)
        + portfolioVariance n covM z := by
    rw [hvwz]
    exact portfolioVariance_add_of_cross_zero n covM
      (frontierPortfolio n covM μ m) z market.posDef hcross
  have hznn : 0 ≤ portfolioVariance n covM z :=
    portfolioVariance_nonneg n covM market.posDef.posSemidef z
  simp only [markowitzObjective_def]
  rw [hvar]
  nlinarith [hznn]

/-! ### Frontier variance equation -/

/-- The optimal variance equals the affine expression `λ·m + γ` in the multipliers.
This is the key step `σ²(m) = w★ᵀ(λμ + γ1) = λ·(w★ᵀμ) + γ·(w★ᵀ1) = λ·m + γ`,
using that `w★` attains target return `m` and is fully invested. -/
theorem frontierPortfolio_variance_eq_lambda_gamma
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ)
    (hcov : covM.PosDef) (hD : frontierD n covM μ ≠ 0) :
    portfolioVariance n covM (frontierPortfolio n covM μ m)
      = frontierLambda n covM μ m * m + frontierGamma n covM μ m := by
  have hmu : μ ⬝ᵥ frontierPortfolio n covM μ m = m := by
    rw [dotProduct_comm]
    exact frontierPortfolio_expectedReturn n covM μ m hcov hD
  have hone : onesVec n ⬝ᵥ frontierPortfolio n covM μ m = 1 := by
    have hb : ∑ i, frontierPortfolio n covM μ m i = 1 :=
      frontierPortfolio_budget n covM μ m hD
    simp only [dotProduct, onesVec, one_mul]
    exact hb
  unfold portfolioVariance
  rw [mulVec_frontierPortfolio n covM μ m hcov, dotProduct_comm, add_dotProduct,
    smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul, hmu, hone]
  ring

/-- Closed form for the affine optimal variance: substituting the Cramer formulas
`λ = (Cm − A)/D`, `γ = (B − Am)/D` gives `λ·m + γ = (Cm² − 2Am + B)/D`. Pure algebra
over the common denominator `D ≠ 0`. -/
theorem frontier_affine_closed_form
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ)
    (hD : frontierD n covM μ ≠ 0) :
    frontierLambda n covM μ m * m + frontierGamma n covM μ m
      = (frontierC n covM * m ^ 2
          - 2 * frontierA n covM μ * m
          + frontierB n covM μ) / frontierD n covM μ := by
  rw [frontierLambda_def, frontierGamma_def]
  field_simp [hD]
  ring

/-- **Equation of the minimum-variance frontier** (`thm:parabola`, first equality):
the optimal variance is the quadratic `σ²(m) = (Cm² − 2Am + B)/D` in the target return. -/
theorem frontierPortfolio_variance_closed_form
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ)
    (hcov : covM.PosDef) (hD : frontierD n covM μ ≠ 0) :
    portfolioVariance n covM (frontierPortfolio n covM μ m)
      = (frontierC n covM * m ^ 2
          - 2 * frontierA n covM μ * m
          + frontierB n covM μ) / frontierD n covM μ := by
  rw [frontierPortfolio_variance_eq_lambda_gamma n covM μ m hcov hD,
    frontier_affine_closed_form n covM μ m hD]

/-- The frontier variance equation on a non-degenerate market, with `D ≠ 0`
discharged by `frontierD_pos`. -/
theorem frontierPortfolio_variance_closed_form_of_market
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ)
    (market : NonDegenerateMarket n μ covM) [Nonempty n] :
    portfolioVariance n covM (frontierPortfolio n covM μ m)
      = (frontierC n covM * m ^ 2
          - 2 * frontierA n covM μ * m
          + frontierB n covM μ) / frontierD n covM μ :=
  frontierPortfolio_variance_closed_form n covM μ m market.posDef
    (frontierD_pos n covM μ market).ne'

/-- **Vertex (completed-square) form** of the frontier variance equation
(`thm:parabola`, second equality):
`σ²(m) = 1/C + (C/D)·(m − A/C)²`. This exhibits the parabola's minimum at `m = A/C`
with value `1/C`. The algebraic key is `B·C = D + A²` (from `frontierD_eq`). -/
theorem frontierPortfolio_variance_completed_square
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ)
    (market : NonDegenerateMarket n μ covM) [Nonempty n] :
    portfolioVariance n covM (frontierPortfolio n covM μ m)
      = 1 / frontierC n covM
          + (frontierC n covM / frontierD n covM μ)
              * (m - frontierA n covM μ / frontierC n covM) ^ 2 := by
  have hC : frontierC n covM ≠ 0 := (frontierC_pos n covM market.posDef).ne'
  have hD : frontierD n covM μ ≠ 0 := (frontierD_pos n covM μ market).ne'
  have key : frontierB n covM μ
      = (frontierD n covM μ + frontierA n covM μ ^ 2) / frontierC n covM := by
    rw [eq_div_iff hC, frontierD_eq]; ring
  rw [frontierPortfolio_variance_closed_form_of_market n covM μ m market, key]
  field_simp
  ring

/-- **GMVP weights** (`cor:gmvp`): at the vertex return `m = A/C` the multiplier `λ`
vanishes and `γ = 1/C`, so the frontier portfolio collapses to
`w_g = (1/C)·Σ⁻¹1`, the global minimum-variance portfolio. -/
theorem frontierPortfolio_gmvp_weights
    (covM : Matrix n n ℝ) (μ : portfolioWeights n)
    (market : NonDegenerateMarket n μ covM) [Nonempty n] :
    frontierPortfolio n covM μ (frontierA n covM μ / frontierC n covM)
      = (1 / frontierC n covM) • covM⁻¹.mulVec (onesVec n) := by
  have hC : frontierC n covM ≠ 0 := (frontierC_pos n covM market.posDef).ne'
  have hD : frontierD n covM μ ≠ 0 := (frontierD_pos n covM μ market).ne'
  have key : frontierB n covM μ
      = (frontierD n covM μ + frontierA n covM μ ^ 2) / frontierC n covM := by
    rw [eq_div_iff hC, frontierD_eq]; ring
  rw [frontierPortfolio_def, frontierLambda_def, frontierGamma_def, key]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- **GMVP variance** (`cor:gmvp`): at the vertex return `m = A/C` the squared term in
the completed-square form vanishes, so the minimal variance is `σ²_g = 1/C`. -/
theorem frontierPortfolio_gmvp_variance
    (covM : Matrix n n ℝ) (μ : portfolioWeights n)
    (market : NonDegenerateMarket n μ covM) [Nonempty n] :
    portfolioVariance n covM
      (frontierPortfolio n covM μ (frontierA n covM μ / frontierC n covM))
      = 1 / frontierC n covM := by
  rw [frontierPortfolio_variance_completed_square n covM μ
    (frontierA n covM μ / frontierC n covM) market]
  ring

/-- **Global minimality of the GMVP** (`cor:gmvp`): every frontier portfolio has variance
at least `1/C`, the variance of the GMVP. The completed-square form makes this immediate
since `(C/D)·(m − A/C)² ≥ 0`. -/
theorem frontierPortfolio_variance_ge_gmvp
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ)
    (market : NonDegenerateMarket n μ covM) [Nonempty n] :
    1 / frontierC n covM
      ≤ portfolioVariance n covM (frontierPortfolio n covM μ m) := by
  rw [frontierPortfolio_variance_completed_square n covM μ m market]
  have hC := frontierC_pos n covM market.posDef
  have hD := frontierD_pos n covM μ market
  have hterm : 0 ≤ (frontierC n covM / frontierD n covM μ)
      * (m - frontierA n covM μ / frontierC n covM) ^ 2 :=
    mul_nonneg (div_pos hC hD).le (sq_nonneg _)
  linarith

/-! ### Affine structure of the frontier (towards two-fund separation) -/

/-- The frontier portfolio is an **affine function of the target return** `m`:
`w★(m) = m·a + b` with fixed direction `a = (C·Σ⁻¹μ − A·Σ⁻¹1)/D` and offset
`b = (B·Σ⁻¹1 − A·Σ⁻¹μ)/D`. This is the structural core of two-fund separation. -/
theorem frontierPortfolio_affine_in_m
    (covM : Matrix n n ℝ) (μ : portfolioWeights n)
    (m : ℝ) (hD : frontierD n covM μ ≠ 0) :
    frontierPortfolio n covM μ m
      =
        m • ((frontierC n covM / frontierD n covM μ) • covM⁻¹.mulVec μ
              - (frontierA n covM μ / frontierD n covM μ) • covM⁻¹.mulVec (onesVec n))
        +
        ((frontierB n covM μ / frontierD n covM μ) • covM⁻¹.mulVec (onesVec n)
              - (frontierA n covM μ / frontierD n covM μ) • covM⁻¹.mulVec μ) := by
  rw [frontierPortfolio_def, frontierLambda_def, frontierGamma_def]
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hD]
  ring

/-- **Two-fund separation theorem** (`thm:twofund`): every frontier portfolio is the
affine combination `w★(m) = α·w★(m₁) + (1−α)·w★(m₂)` of any two distinct frontier
portfolios, with mixing weight `α = (m − m₂)/(m₁ − m₂)`. A direct consequence of the
affineness of `w★(·)` in the target return. -/
theorem frontierPortfolio_two_fund
    (covM : Matrix n n ℝ) (μ : portfolioWeights n)
    (m m₁ m₂ : ℝ)
    (hD : frontierD n covM μ ≠ 0)
    (hm : m₁ ≠ m₂) :
    frontierPortfolio n covM μ m
      =
        ((m - m₂) / (m₁ - m₂)) • frontierPortfolio n covM μ m₁
        + (1 - (m - m₂) / (m₁ - m₂)) • frontierPortfolio n covM μ m₂ := by
  rw [frontierPortfolio_affine_in_m n covM μ m hD,
    frontierPortfolio_affine_in_m n covM μ m₁ hD,
    frontierPortfolio_affine_in_m n covM μ m₂ hD]
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hD, sub_ne_zero.mpr hm]
  ring

/-! ### Uniqueness of the frontier minimiser -/

/-- **Uniqueness of the Markowitz minimiser** (`thm:frontier`, uniqueness part): any
feasible portfolio attaining the optimal objective value equals the frontier portfolio.
The deviation `z = v − w★` has zero variance (the objective values agree and variance
splits as `var v = var w★ + var z`), so positive definiteness forces `z = 0`. -/
theorem frontierPortfolio_unique_of_market
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ)
    (market : NonDegenerateMarket n μ covM) [Nonempty n]
    (v : portfolioWeights n)
    (hv : v ∈ feasibleSet n μ m)
    (hobj : markowitzObjective n covM v
              = markowitzObjective n covM (frontierPortfolio n covM μ m)) :
    v = frontierPortfolio n covM μ m := by
  set z := v - frontierPortfolio n covM μ m with hz
  have hzret : expectedReturn n μ z = 0 :=
    feasible_deviation_expectedReturn_zero n covM μ m market v hv
  have hzbud : ∑ i, z i = 0 :=
    feasible_deviation_budget_zero n covM μ m market v hv
  have hcross : z ⬝ᵥ covM.mulVec (frontierPortfolio n covM μ m) = 0 :=
    frontierPortfolio_cross_zero n covM μ m z market.posDef hzret hzbud
  have hvwz : v = frontierPortfolio n covM μ m + z := by rw [hz]; abel
  have hvar : portfolioVariance n covM v
      = portfolioVariance n covM (frontierPortfolio n covM μ m)
        + portfolioVariance n covM z := by
    rw [hvwz]
    exact portfolioVariance_add_of_cross_zero n covM
      (frontierPortfolio n covM μ m) z market.posDef hcross
  have hzvar : portfolioVariance n covM z = 0 := by
    rw [markowitzObjective_def, markowitzObjective_def, hvar] at hobj
    linarith
  have hz0 : z = 0 :=
    portfolioVariance_eq_zero_of_posDef n covM market.posDef z hzvar
  rw [hvwz, hz0, add_zero]

/-- **Uniqueness of the optimal portfolio**: any Markowitz-optimal portfolio is *the*
frontier portfolio. Both `v` and `w★` minimise the objective over the same feasible set,
so their objective values coincide by antisymmetry, and uniqueness applies. -/
theorem frontierPortfolio_optimal_unique_of_market
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ)
    (market : NonDegenerateMarket n μ covM) [Nonempty n]
    (v : portfolioWeights n)
    (hvopt : markowitzOptimal n covM μ m v) :
    v = frontierPortfolio n covM μ m := by
  obtain ⟨hvfeas, hvmin⟩ := hvopt
  obtain ⟨hsfeas, hsmin⟩ := frontierPortfolio_optimal_of_market n covM μ m market
  have hobj : markowitzObjective n covM v
      = markowitzObjective n covM (frontierPortfolio n covM μ m) :=
    le_antisymm (hvmin _ hsfeas) (hsmin _ hvfeas)
  exact frontierPortfolio_unique_of_market n covM μ m market v hvfeas hobj

/-! ### Efficient frontier -/

/-- `w'` **dominates** `w` if it offers at least as much expected return, no greater
variance, and is strictly better in at least one of the two (Pareto domination). -/
def dominates (μ : portfolioWeights n) (covM : Matrix n n ℝ)
    (w' w : portfolioWeights n) : Prop :=
  expectedReturn n μ w ≤ expectedReturn n μ w'
  ∧ portfolioVariance n covM w' ≤ portfolioVariance n covM w
  ∧ (expectedReturn n μ w < expectedReturn n μ w'
      ∨ portfolioVariance n covM w' < portfolioVariance n covM w)

/-- A portfolio is **efficient** if it is fully invested (budget-feasible) and not
dominated by any other budget-feasible portfolio. -/
def efficientPortfolio (μ : portfolioWeights n) (covM : Matrix n n ℝ)
    (w : portfolioWeights n) : Prop :=
  w ∈ budgetSet n ∧ ¬ ∃ w' ∈ budgetSet n, dominates n μ covM w' w

/-- **Symmetry of the variance parabola** about the vertex return `A/C`:
`σ²(2·(A/C) − m) = σ²(m)`, since the completed-square offset only changes sign. -/
theorem frontierPortfolio_variance_symm
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ)
    (market : NonDegenerateMarket n μ covM) [Nonempty n] :
    portfolioVariance n covM
      (frontierPortfolio n covM μ
        (2 * (frontierA n covM μ / frontierC n covM) - m))
      =
    portfolioVariance n covM
      (frontierPortfolio n covM μ m) := by
  rw [frontierPortfolio_variance_completed_square n covM μ
      (2 * (frontierA n covM μ / frontierC n covM) - m) market,
    frontierPortfolio_variance_completed_square n covM μ m market]
  ring

/-- **Frontier portfolios below the GMVP return are inefficient**: for `m < A/C` the
vertex-reflected portfolio `w★(2·A/C − m)` has the same variance but strictly greater
expected return, hence dominates `w★(m)`. -/
theorem frontierPortfolio_dominated_of_lt_gmvp
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ)
    (market : NonDegenerateMarket n μ covM) [Nonempty n]
    (hm : m < frontierA n covM μ / frontierC n covM) :
    dominates n μ covM
      (frontierPortfolio n covM μ
        (2 * (frontierA n covM μ / frontierC n covM) - m))
      (frontierPortfolio n covM μ m) := by
  have hret : expectedReturn n μ (frontierPortfolio n covM μ m) = m :=
    frontierPortfolio_expectedReturn_of_market n covM μ m market
  have hret' : expectedReturn n μ
      (frontierPortfolio n covM μ (2 * (frontierA n covM μ / frontierC n covM) - m))
        = 2 * (frontierA n covM μ / frontierC n covM) - m :=
    frontierPortfolio_expectedReturn_of_market n covM μ
      (2 * (frontierA n covM μ / frontierC n covM) - m) market
  have hvar : portfolioVariance n covM
      (frontierPortfolio n covM μ (2 * (frontierA n covM μ / frontierC n covM) - m))
        = portfolioVariance n covM (frontierPortfolio n covM μ m) :=
    frontierPortfolio_variance_symm n covM μ m market
  refine ⟨?_, le_of_eq hvar, ?_⟩
  · rw [hret, hret']; linarith
  · left; rw [hret, hret']; linarith

/-- **Frontier portfolios below the GMVP return are not efficient**: the
vertex-reflected portfolio is a budget-feasible witness that dominates `w★(m)`. -/
theorem frontierPortfolio_not_efficient_of_lt_gmvp
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ)
    (market : NonDegenerateMarket n μ covM) [Nonempty n]
    (hm : m < frontierA n covM μ / frontierC n covM) :
    ¬ efficientPortfolio n μ covM (frontierPortfolio n covM μ m) := by
  rintro ⟨_, hnot⟩
  exact hnot ⟨frontierPortfolio n covM μ
      (2 * (frontierA n covM μ / frontierC n covM) - m),
    frontierPortfolio_budget_of_market n covM μ
      (2 * (frontierA n covM μ / frontierC n covM) - m) market,
    frontierPortfolio_dominated_of_lt_gmvp n covM μ m market hm⟩

/-- **Lower envelope**: the frontier portfolio matching a budget-feasible portfolio's
own expected return has no greater variance — the frontier is the variance-minimising
boundary at each return level. -/
theorem budget_variance_ge_frontier_at_return
    (covM : Matrix n n ℝ) (μ : portfolioWeights n)
    (market : NonDegenerateMarket n μ covM) [Nonempty n]
    (w : portfolioWeights n)
    (hw : w ∈ budgetSet n) :
    portfolioVariance n covM
      (frontierPortfolio n covM μ (expectedReturn n μ w))
      ≤ portfolioVariance n covM w := by
  obtain ⟨_, hmin⟩ :=
    frontierPortfolio_optimal_of_market n covM μ (expectedReturn n μ w) market
  have hwfeas : w ∈ feasibleSet n μ (expectedReturn n μ w) := ⟨hw, rfl⟩
  have hobj := hmin w hwfeas
  rw [markowitzObjective_def, markowitzObjective_def] at hobj
  linarith

/-- **Strict monotonicity on the upper branch**: for target returns at or above the
GMVP return `A/C`, the frontier variance is strictly increasing in `m`. -/
theorem frontierPortfolio_variance_strictMono_ge
    (covM : Matrix n n ℝ) (μ : portfolioWeights n)
    (m₁ m₂ : ℝ)
    (market : NonDegenerateMarket n μ covM) [Nonempty n]
    (hge : frontierA n covM μ / frontierC n covM ≤ m₁)
    (hlt : m₁ < m₂) :
    portfolioVariance n covM (frontierPortfolio n covM μ m₁)
      < portfolioVariance n covM (frontierPortfolio n covM μ m₂) := by
  have hCD : 0 < frontierC n covM / frontierD n covM μ :=
    div_pos (frontierC_pos n covM market.posDef) (frontierD_pos n covM μ market)
  have h0 : 0 ≤ m₁ - frontierA n covM μ / frontierC n covM := by linarith
  have h1 : m₁ - frontierA n covM μ / frontierC n covM
      < m₂ - frontierA n covM μ / frontierC n covM := by linarith
  have hsq : (m₁ - frontierA n covM μ / frontierC n covM) ^ 2
      < (m₂ - frontierA n covM μ / frontierC n covM) ^ 2 := by nlinarith [h0, h1]
  rw [frontierPortfolio_variance_completed_square n covM μ m₁ market,
    frontierPortfolio_variance_completed_square n covM μ m₂ market]
  linarith [mul_lt_mul_of_pos_left hsq hCD]
