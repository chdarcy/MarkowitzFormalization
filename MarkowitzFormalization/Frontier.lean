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
