# Comparator validation

Four headline theorems of this project are independently validated with the
[Lean FRO Comparator](https://github.com/leanprover/comparator). The Comparator
re-elaborates a *Mathlib-only* statement of each theorem and checks, with the Lean
kernel, that a delegating proof against the full library closes exactly that statement
using only a permitted set of axioms. All four currently report:

```
Your solution is okay!
```

## 1. How the audit triples are structured

Each audited theorem `T` has a directory `Audit/<Target>/` containing three files:

- **`Challenge.lean`** — a *Mathlib-only* file. It imports nothing from this project
  (only the specific Mathlib modules the library's `Basic.lean` uses — never the
  umbrella `import Mathlib`, which would force building thousands of unused modules).
  It copies, verbatim, the minimal definitions needed to *state* `T` into the namespace
  `MarkowitzFormalization.StatementAudit`, and states `T` with proof `:= by sorry`. This
  is the statement whose meaning the Comparator pins down independently of our proofs.

- **`Solution.lean`** — imports the full `MarkowitzFormalization` library, repeats the
  **identical** copied definitions and the **identical** statement of `T` in the same
  `MarkowitzFormalization.StatementAudit` namespace, and proves it by delegating to the
  real library theorem. Because the copied definitions are *definitionally equal* to the
  library ones, the delegation is:

  ```lean
  theorem T … := by exact _root_.T n covM μ … hyps
  ```

  The `_root_.` prefix is required to escape the same-named `StatementAudit.T`.

- **`comparator.json`** — the run configuration:

  ```json
  {
      "challenge_module": "Audit.<Target>.Challenge",
      "solution_module": "Audit.<Target>.Solution",
      "theorem_names": ["MarkowitzFormalization.StatementAudit.<T>"],
      "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
      "enable_nanoda": false
  }
  ```

### Definitional-equality vs. structures

Plain `def`/`abbrev` copies (e.g. `portfolioVariance`, `rfFrontierPortfolio`) are
definitionally equal to the library versions, so the Solution proof is a bare `exact`.

One target is different. `frontierPortfolio_variance_closed_form_of_market` takes a
`NonDegenerateMarket` argument, which is a **`structure`**. A copied `structure` is a
*fresh inductive type*, **not** definitionally equal to the library's even with identical
fields — so a bare `exact` fails on that hypothesis. The Solution repacks it field by
field through the anonymous constructor:

```lean
exact _root_.frontierPortfolio_variance_closed_form_of_market n covM μ m
  ⟨market.posDef, market.not_proportional⟩
```

The conclusion still matches by `def`-level defeq. **Rule of thumb:** any audited
theorem whose statement mentions a project `structure`/`class`/`inductive` needs this
anonymous-constructor repack in its Solution.

### Build wiring

`lakefile.toml` registers a second library that is **not** in `defaultTargets`:

```toml
[[lean_lib]]
name = "Audit"
globs = ["Audit.+"]
```

So a plain `lake build` builds only `MarkowitzFormalization` (2602 jobs) and is
unaffected by the audit files; the triples are built explicitly by module name.

## 2. Which targets passed

| Audit target | Library theorem (`MarkowitzFormalization.StatementAudit.…`) | Delegation | Result |
|---|---|---|---|
| `Audit/CapitalMarketLine` | `capitalMarketLine_squared` | bare `exact` | ✅ `Your solution is okay!` |
| `Audit/RiskFreeOptimal` | `rfFrontierPortfolio_optimal` | bare `exact` | ✅ `Your solution is okay!` |
| `Audit/OneFundSeparation` | `rfFrontierPortfolio_one_fund` | bare `exact` | ✅ `Your solution is okay!` |
| `Audit/FrontierVariance` | `frontierPortfolio_variance_closed_form_of_market` | struct repack | ✅ `Your solution is okay!` |

Each run elaborates the Challenge (with its expected `sorry` warning), exports the
statement with `lean4export`, builds and exports the Solution's statement, confirms the
two exported statements are identical, checks the axioms against the permitted set, and
has the Lean default kernel accept the Solution's proof.

## 3. Exact commands

### 3a. Authoring + build check (Windows, native, project toolchain v4.31.0)

```powershell
# Build a triple's Challenge + Solution; Challenge emits an expected `sorry` warning,
# Solution must build clean.
lake build Audit.CapitalMarketLine.Challenge Audit.CapitalMarketLine.Solution `
           Audit.RiskFreeOptimal.Challenge  Audit.RiskFreeOptimal.Solution `
           Audit.OneFundSeparation.Challenge Audit.OneFundSeparation.Solution `
           Audit.FrontierVariance.Challenge  Audit.FrontierVariance.Solution

# Main library is unaffected (still 2602 jobs, clean):
lake build
```

### 3b. Comparator run (WSL — see §5)

The Comparator's execution pipeline `CreateProcess`-es a sandbox helper, which does not
work natively on Windows, so the actual checks are run in WSL. From the Linux copy of
the project (`~/MarkowitzFormalization`):

```bash
export PATH="$HOME/.elan/bin:$PATH"
export COMPARATOR_LEAN4EXPORT="$HOME/tools/lean4export/.lake/build/bin/lean4export"
export COMPARATOR_LANDRUN="$HOME/tools/comparator/scripts/fake-landrun.sh"
CMP="$HOME/tools/comparator/.lake/build/bin/comparator"

# Build the triples in the Linux copy first:
lake build Audit.CapitalMarketLine.Challenge Audit.CapitalMarketLine.Solution \
           Audit.RiskFreeOptimal.Challenge  Audit.RiskFreeOptimal.Solution \
           Audit.OneFundSeparation.Challenge Audit.OneFundSeparation.Solution \
           Audit.FrontierVariance.Challenge  Audit.FrontierVariance.Solution

# Run each check (from the project root):
lake env "$CMP" Audit/CapitalMarketLine/comparator.json
lake env "$CMP" Audit/RiskFreeOptimal/comparator.json
lake env "$CMP" Audit/OneFundSeparation/comparator.json
lake env "$CMP" Audit/FrontierVariance/comparator.json
```

Each prints `Lean default kernel accepts the solution` / `Your solution is okay!` and
exits 0.

## 4. `fake-landrun` caveat

The runs above use `scripts/fake-landrun.sh`, an **insecure** development shim shipped
with the Comparator that runs the Solution build **unsandboxed** (it prints
`WARNING: THIS IS NOT REAL LANDRUN!`). This is acceptable here because the Challenge and
Solution are both authored by us: the sandbox only protects the checker host from a
*malicious untrusted* Solution, and the validity of the result (identical exported
statements + kernel acceptance + axiom check) does not depend on sandboxing.

For an adversarial or official submission, replace it with the real
[`landrun`](https://github.com/Zouuup/landrun) Linux sandbox and point
`COMPARATOR_LANDRUN` at it, optionally wrapping the run in the Comparator README's
`systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user …` guard.

## 5. WSL setup (one-time)

The project toolchain is **Lean v4.31.0 / Mathlib v4.31.0**; the Comparator's own
checkout uses v4.32.0-rc1. These coexist in separate checkouts.

1. **Distro:** WSL2 Ubuntu-24.04 (systemd enabled).
2. **Toolchain:** install `elan` (`curl …/elan-init.sh | sh -s -- -y --default-toolchain none`);
   the project toolchain v4.31.0 is fetched on the first `lake` invocation.
3. **Project copy:** copy the source tree (excluding `.lake`) into the Linux filesystem
   at `~/MarkowitzFormalization`. **Do not** build the `/mnt/c` Windows checkout from
   WSL — it would share `.lake/` with the Windows build and corrupt its oleans. Sync only
   source files; rebuild oleans in the Linux copy (`lake exe cache get` for Mathlib).
4. **Comparator:** clone `github.com/leanprover/comparator` → `~/tools/comparator`,
   `lake build` → binary at `~/tools/comparator/.lake/build/bin/comparator`. The
   `fake-landrun.sh` shim is at `~/tools/comparator/scripts/fake-landrun.sh`.
5. **lean4export (version-matched):** clone `github.com/leanprover/lean4export` →
   `~/tools/lean4export`, **check out the v4.31.0-matched commit `8554815c2d`** (so its
   export format matches the project's oleans — the bundled v4.32 export must not be used
   on v4.31.0 oleans), then `lake build` → binary at
   `~/tools/lean4export/.lake/build/bin/lean4export`. This is `COMPARATOR_LEAN4EXPORT`.

After the one-time setup, re-validating after editing the triples is just: sync the
changed `Audit/<Target>` source files into `~/MarkowitzFormalization/Audit/`, then run
§3b. With Mathlib oleans cached, the per-triple build is ~25 s.

> Disk note: the WSL2 vhdx lives on the Windows system drive and grows with the Mathlib
> olean cache (~8–10 GB peak). Ensure ≥ ~15 GB free before `lake exe cache get`.
