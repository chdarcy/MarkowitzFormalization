import MarkowitzFormalization.Basic

/-!
# Portfolio

Basic portfolio definitions.
-/

open Finset

variable (n : Type) [Fintype n] [DecidableEq n]

abbrev portfolioWeights : Type :=
  n → ℝ

def budgetSet : Set (portfolioWeights n) :=
  {w | ∑ i, w i = 1}

def expectedReturn
    (μ : portfolioWeights n)
    (w : portfolioWeights n) : ℝ :=
  ∑ i, w i * μ i

omit [DecidableEq n] in
theorem expectedReturn_zero (μ : portfolioWeights n) :
    expectedReturn n μ 0 = 0 := by
  simp [expectedReturn]

omit [DecidableEq n] in
theorem expectedReturn_add (μ w₁ w₂ : portfolioWeights n) :
    expectedReturn n μ (w₁ + w₂) = expectedReturn n μ w₁ + expectedReturn n μ w₂ := by
  simp [expectedReturn, add_mul, Finset.sum_add_distrib]

omit [DecidableEq n] in
theorem expectedReturn_smul (μ w : portfolioWeights n) (c : ℝ) :
    expectedReturn n μ (c • w) = c * expectedReturn n μ w := by
  simp [expectedReturn, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-!
## Portfolio Variance and Risk
-/

open Matrix in
def portfolioVariance
    (covM : Matrix n n ℝ)
    (w : portfolioWeights n) : ℝ :=
  w ⬝ᵥ covM.mulVec w

open Matrix in
noncomputable def portfolioRisk
    (covM : Matrix n n ℝ)
    (w : portfolioWeights n) : ℝ :=
  Real.sqrt (portfolioVariance n covM w)

/-!
## Covariance Matrix and Market Assumptions
-/

def CovarianceMatrix (covM : Matrix n n ℝ) : Prop :=
  covM.PosSemidef

omit [DecidableEq n] in
theorem portfolioVariance_nonneg
    (covM : Matrix n n ℝ)
    (hcov : CovarianceMatrix n covM)
    (w : portfolioWeights n) :
    0 ≤ portfolioVariance n covM w := by
  unfold portfolioVariance
  have h := hcov.dotProduct_mulVec_nonneg w
  simp only [star_trivial] at h
  exact h

omit [DecidableEq n] in
theorem portfolioRisk_nonneg
    (covM : Matrix n n ℝ)
    (w : portfolioWeights n) :
    0 ≤ portfolioRisk n covM w :=
  Real.sqrt_nonneg _

structure NonDegenerateMarket
    (μ : portfolioWeights n)
    (covM : Matrix n n ℝ) : Prop where
  posDef : covM.PosDef
  not_proportional : ¬ ∃ c : ℝ, μ = fun _ => c
