# Correspondence: mathematics ↔ Lean

This document maps the mathematical statements of deterministic Markowitz
mean-variance portfolio theory (as presented in the Markowitz lecture notes and the
classical mean-variance framework) to their Lean 4 / Mathlib formalisations in this
repository. Every declaration listed is fully proved (no `sorry` / `admit`); the
project builds cleanly (`lake build`, 2602 jobs).

Throughout, `n` is a finite asset type (`Fintype n`, `DecidableEq n`), `μ : n → ℝ` is
the expected-return vector, `Σ = covM : Matrix n n ℝ` is the covariance matrix, `1` is
the all-ones vector (`onesVec`), and weights live in `portfolioWeights n := n → ℝ`.
The frontier scalars are `A = 1ᵀΣ⁻¹μ`, `B = μᵀΣ⁻¹μ`, `C = 1ᵀΣ⁻¹1`, `D = BC − A²`.

All library declarations live in the root namespace and module
`MarkowitzFormalization`.

## 1. Core definitions

| Mathematics | Lean declaration | Module |
|---|---|---|
| Weight vector `w ∈ ℝⁿ` | `portfolioWeights` | `Portfolio` |
| Budget set `{w : ∑ wᵢ = 1}` | `budgetSet` | `Portfolio` |
| Expected return `wᵀμ` | `expectedReturn` | `Portfolio` |
| Variance `wᵀΣw` | `portfolioVariance` | `Portfolio` |
| Risk `√(wᵀΣw)` | `portfolioRisk` | `Portfolio` |
| Σ positive semidefinite | `CovarianceMatrix` | `Portfolio` |
| Non-degenerate market (Σ ≻ 0, μ not constant) | `NonDegenerateMarket` | `Portfolio` |
| All-ones vector `1` | `onesVec` | `Frontier` |
| Frontier scalars `A, B, C, D` | `frontierA`, `frontierB`, `frontierC`, `frontierD` | `Frontier` |
| Multipliers `λ(m), γ(m)` | `frontierLambda`, `frontierGamma` | `Frontier` |
| Frontier portfolio `w★(m) = λΣ⁻¹μ + γΣ⁻¹1` | `frontierPortfolio` | `Frontier` |
| Markowitz objective `½ wᵀΣw` | `markowitzObjective` | `Frontier` |
| Feasible set (budget ∧ target return) | `feasibleSet` | `Frontier` |
| Markowitz-optimal predicate | `markowitzOptimal` | `Frontier` |
| Pareto domination / efficiency | `dominates`, `efficientPortfolio` | `Frontier` |

## 2. Risky-asset core results

| Mathematics | Lean declaration | Module |
|---|---|---|
| `wᵀΣw ≥ 0` under Σ ⪰ 0 | `portfolioVariance_nonneg` | `Portfolio` |
| `wᵀΣw = 0 ⇒ w = 0` under Σ ≻ 0 | `portfolioVariance_eq_zero_of_posDef` | `Portfolio` |
| `C > 0` | `frontierC_pos` | `Frontier` |
| `D = BC − A² ≥ 0` | `frontierD_nonneg` | `Frontier` |
| `D ≠ 0` on a non-degenerate market | `frontierD_ne_zero` | `Frontier` |
| `D > 0` on a non-degenerate market | `frontierD_pos` | `Frontier` |
| `w★(m)` attains target return `m` | `frontierPortfolio_expectedReturn` / `..._of_market` | `Frontier` |
| `w★(m)` is fully invested | `frontierPortfolio_budget` / `..._of_market` | `Frontier` |
| `w★(m)` is feasible | `frontierPortfolio_feasible` / `..._of_market` | `Frontier` |
| **Optimality** of `w★(m)` | `frontierPortfolio_optimal_of_market` | `Frontier` |
| **Uniqueness** of the minimiser | `frontierPortfolio_unique_of_market` | `Frontier` |
| Optimal portfolio equals `w★(m)` | `frontierPortfolio_optimal_unique_of_market` | `Frontier` |
| **Variance parabola** `σ²(m) = (Cm² − 2Am + B)/D` | `frontierPortfolio_variance_closed_form` / `..._of_market` | `Frontier` |
| **Completed square** `σ²(m) = 1/C + (C/D)(m − A/C)²` | `frontierPortfolio_variance_completed_square` | `Frontier` |
| GMVP weights `(1/C)Σ⁻¹1` | `frontierPortfolio_gmvp_weights` | `Frontier` |
| GMVP variance `1/C` | `frontierPortfolio_gmvp_variance` | `Frontier` |
| Global lower bound `σ²(m) ≥ 1/C` | `frontierPortfolio_variance_ge_gmvp` | `Frontier` |
| Variance symmetry about `A/C` | `frontierPortfolio_variance_symm` | `Frontier` |
| Lower branch (`m < A/C`) not efficient | `frontierPortfolio_not_efficient_of_lt_gmvp` | `Frontier` |
| Upper branch (`m ≥ A/C`) efficient | `frontierPortfolio_efficient_of_ge_gmvp` | `Frontier` |
| Strict variance monotonicity on upper branch | `frontierPortfolio_variance_strictMono_ge` | `Frontier` |
| Frontier is the lower variance envelope | `budget_variance_ge_frontier_at_return` | `Frontier` |
| Affine structure `w★(m) = m·a + b` | `frontierPortfolio_affine_in_m` | `Frontier` |
| **Two-fund separation** | `frontierPortfolio_two_fund` | `Frontier` |

## 3. Risk-free extension (implicit cash-weight model)

A risky exposure `w` carries implicit cash weight `w₀ = 1 − ∑ wᵢ`; total variance is the
risky quadratic form, and `e = μ − rf·1` is the excess-return vector. The slope² of the
capital market line is the squared Sharpe ratio `S = eᵀΣ⁻¹e`.

| Mathematics | Lean declaration | Module |
|---|---|---|
| Excess return `e = μ − rf·1` | `excessReturn` | `RiskFree` |
| Cash weight `w₀ = 1 − ∑ wᵢ` | `riskFreeWeight` | `RiskFree` |
| Total expected return `rf + wᵀe` | `totalExpectedReturn` | `RiskFree` |
| Total variance `wᵀΣw` | `riskFreeVariance` | `RiskFree` |
| Squared Sharpe ratio `S = eᵀΣ⁻¹e` | `sharpeSquared` | `RiskFree` |
| Risk-free frontier portfolio `w★ = ((m−rf)/S)·Σ⁻¹e` | `rfFrontierPortfolio` | `RiskFree` |
| Tangency denominator `D_t = 1ᵀΣ⁻¹e` | `tangencyDenominator` | `RiskFree` |
| Tangency portfolio `w_T = (1/D_t)·Σ⁻¹e` | `tangencyPortfolio` | `RiskFree` |
| `S > 0` when `e ≠ 0` | `sharpeSquared_pos` | `RiskFree` |
| `S` as a variance `(Σ⁻¹e)ᵀΣ(Σ⁻¹e)` | `sharpeSquared_eq_portfolioVariance` | `RiskFree` |
| `w★` attains total return `m` | `rfFrontierPortfolio_totalExpectedReturn` | `RiskFree` |
| `w★` variance `(m−rf)²/S` | `rfFrontierPortfolio_variance` | `RiskFree` |
| **Optimality** of `w★` | `rfFrontierPortfolio_optimal` | `RiskFree` |
| **Uniqueness** of `w★` | `rfFrontierPortfolio_unique` | `RiskFree` |
| **Squared capital market line** `σ²·S = (m−rf)²` | `capitalMarketLine_squared` | `RiskFree` |
| `D_t = A − rf·C` | `tangencyDenominator_eq_frontierA_sub_rf_frontierC` | `RiskFree` |
| Tangency expected excess return `S/D_t` | `tangencyPortfolio_expectedExcessReturn` | `RiskFree` |
| Tangency portfolio fully invested | `tangencyPortfolio_budget` | `RiskFree` |
| Tangency portfolio holds no cash | `tangencyPortfolio_riskFreeWeight_zero` | `RiskFree` |
| Tangency total return `rf + S/D_t` | `tangencyPortfolio_totalExpectedReturn` | `RiskFree` |
| **One-fund separation** | `rfFrontierPortfolio_one_fund` | `RiskFree` |
| Cash leg of one-fund separation | `rfFrontierPortfolio_riskFreeWeight` | `RiskFree` |
| Image under Σ: `Σw_T = (1/D_t)·e` | `mulVec_tangencyPortfolio` | `RiskFree` |

## 4. Comparator-validated targets

Four headline theorems are additionally checked by the Lean FRO Comparator (an
independent re-elaboration of a Mathlib-only statement plus Lean-kernel acceptance of
the delegating proof). Each has a triple under `Audit/`. See `COMPARATOR.md`.

| Audit target | Library theorem | Comparator result |
|---|---|---|
| `Audit/CapitalMarketLine` | `capitalMarketLine_squared` | `Your solution is okay!` |
| `Audit/RiskFreeOptimal` | `rfFrontierPortfolio_optimal` | `Your solution is okay!` |
| `Audit/OneFundSeparation` | `rfFrontierPortfolio_one_fund` | `Your solution is okay!` |
| `Audit/FrontierVariance` | `frontierPortfolio_variance_closed_form_of_market` | `Your solution is okay!` |

## 5. Scope boundary

The project formalises the deterministic mean-vector / covariance-matrix layer. It does
**not** construct `μ` and `Σ` from random variables or measure-theoretic probability
spaces, and it does **not** yet formalise CAPM or the security-market-line (beta
pricing). These are upstream/downstream extensions, not gaps in the formalised results.
