import MarkowitzFormalization

/-!
# Comparator Solution — Frontier Variance Closed Form

Restates `frontierPortfolio_variance_closed_form_of_market` with the **same** copied
definitions and the **same** `MarkowitzFormalization.StatementAudit` namespace as
`Challenge.lean`, so the two theorem statements are identical for Comparator.

The plain (`def`) copies are definitionally equal to the library ones. The one
exception is `NonDegenerateMarket`, which is a `structure`: a copied structure is a
*fresh* inductive type, not definitionally equal to the library's. So the proof
repacks the hypothesis through its two fields — `⟨market.posDef, market.not_proportional⟩`
— to build the library `_root_.NonDegenerateMarket` and then delegates to the library
theorem. The conclusion matches by `def`-level defeq.
-/

open Matrix

namespace MarkowitzFormalization.StatementAudit

variable (n : Type) [Fintype n] [DecidableEq n]

/-- Copy of `portfolioWeights`: a risky-asset weight vector. -/
abbrev portfolioWeights : Type := n → ℝ

/-- Copy of `onesVec`: the all-ones vector. -/
def onesVec : portfolioWeights n :=
  fun _ => 1

/-- Copy of `portfolioVariance`: `wᵀ Σ w`. -/
def portfolioVariance (covM : Matrix n n ℝ) (w : portfolioWeights n) : ℝ :=
  w ⬝ᵥ covM.mulVec w

/-- Copy of `NonDegenerateMarket`: positive-definite covariance with non-constant `μ`. -/
structure NonDegenerateMarket
    (μ : portfolioWeights n)
    (covM : Matrix n n ℝ) : Prop where
  posDef : covM.PosDef
  not_proportional : ¬ ∃ c : ℝ, μ = fun _ => c

/-- Copy of `frontierA`: `A = 1ᵀ Σ⁻¹ μ`. -/
noncomputable def frontierA (covM : Matrix n n ℝ) (μ : portfolioWeights n) : ℝ :=
  onesVec n ⬝ᵥ covM⁻¹.mulVec μ

/-- Copy of `frontierB`: `B = μᵀ Σ⁻¹ μ`. -/
noncomputable def frontierB (covM : Matrix n n ℝ) (μ : portfolioWeights n) : ℝ :=
  μ ⬝ᵥ covM⁻¹.mulVec μ

/-- Copy of `frontierC`: `C = 1ᵀ Σ⁻¹ 1`. -/
noncomputable def frontierC (covM : Matrix n n ℝ) : ℝ :=
  onesVec n ⬝ᵥ covM⁻¹.mulVec (onesVec n)

/-- Copy of `frontierD`: `D = B C - A²`. -/
noncomputable def frontierD (covM : Matrix n n ℝ) (μ : portfolioWeights n) : ℝ :=
  frontierB n covM μ * frontierC n covM - (frontierA n covM μ) ^ 2

/-- Copy of `frontierLambda`: `λ(m) = (C m - A) / D`. -/
noncomputable def frontierLambda (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ) : ℝ :=
  (frontierC n covM * m - frontierA n covM μ) / frontierD n covM μ

/-- Copy of `frontierGamma`: `γ(m) = (B - A m) / D`. -/
noncomputable def frontierGamma (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ) : ℝ :=
  (frontierB n covM μ - frontierA n covM μ * m) / frontierD n covM μ

/-- Copy of `frontierPortfolio`: `w★(m) = λ(m) Σ⁻¹ μ + γ(m) Σ⁻¹ 1`. -/
noncomputable def frontierPortfolio (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ) :
    portfolioWeights n :=
  frontierLambda n covM μ m • covM⁻¹.mulVec μ +
    frontierGamma n covM μ m • covM⁻¹.mulVec (onesVec n)

/-- **Frontier variance closed form** (solution): identical statement to the challenge,
proved by delegating to the library theorem. The `NonDegenerateMarket` hypothesis is
repacked field-by-field into the library structure (a copied `structure` is not defeq
to the library one); the conclusion matches by `def`-level defeq. -/
theorem frontierPortfolio_variance_closed_form_of_market
    (covM : Matrix n n ℝ) (μ : portfolioWeights n) (m : ℝ)
    (market : NonDegenerateMarket n μ covM) [Nonempty n] :
    portfolioVariance n covM (frontierPortfolio n covM μ m)
      = (frontierC n covM * m ^ 2
          - 2 * frontierA n covM μ * m
          + frontierB n covM μ) / frontierD n covM μ := by
  exact _root_.frontierPortfolio_variance_closed_form_of_market n covM μ m
    ⟨market.posDef, market.not_proportional⟩

end MarkowitzFormalization.StatementAudit
