# Collatz endpoint sparsity: Lean 4 formalization

[![Lean verification](https://github.com/Esythium/collatz-endpoint-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/Esythium/collatz-endpoint-lean/actions/workflows/lean.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](LICENSE)

**Author: Esm.** Licensed under [Apache 2.0](LICENSE).

[Repository](https://github.com/Esythium/collatz-endpoint-lean) ·
[GitHub Actions](https://github.com/Esythium/collatz-endpoint-lean/actions)

This project formalizes the mathematical results of **A Logarithmic Endpoint Refinement of Collatz Orbit Sparsity** (Esm, 12 October 2026). Its main import is:

```lean
import CollatzEndpoint.MainResults
```

The formalization proves the uniform window estimate with constant **400**, the exact entropy-defined exponents, the exclusion of the critical slow-divergence rate, and the successive-odd-iterate drift consequences. The final trajectory results instantiate the counting bounds and dynamical hypotheses for the actual Collatz maps. They do not assume the window estimate or an unproved property of divergent orbits.

This is **not a proof of the Collatz conjecture**. A positive orbit satisfying the specified slow-growth bound is proved eventually periodic; arrival at 1 is not proved, and nontrivial finite cycles are not excluded. Kernel checking establishes the encoded mathematical implications. It does not establish historical priority, global originality, or external peer review. AI assistance was used in preparing and checking this formalization.

## Template provenance

The repository scaffolding is adapted from the Lean community's
[LeanProject template](https://github.com/leanprover-community/LeanProject/tree/d4f099e563310c15189cf5b73c39efe6e8fdfd4b),
at commit `d4f099e563310c15189cf5b73c39efe6e8fdfd4b`. Its Apache 2.0 license and
VS Code Lean extension recommendation are retained, with adapted editor configuration
that omits the unused blueprint and LaTeX settings. The project name, mathematical source,
contribution instructions, documentation, and verification records are specific
to this formalization. Template provenance does not imply endorsement of the
mathematical claims by the Lean community.

## Pinned environment

Keep the supplied `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` unchanged when reproducing this version.

| Component | Pinned version |
| --- | --- |
| Lean | `leanprover/lean4:v4.35.0-rc4` |
| mathlib | `021c46bdd042f67b538b9f9871d556a93713a9a9` |
| Transitive Lake dependencies | Exact revisions recorded in `lake-manifest.json` |

The mathlib checkout is [fixed at this commit](https://github.com/leanprover-community/mathlib4/tree/021c46bdd042f67b538b9f9871d556a93713a9a9). The release-candidate Lean version is intentional; replacing it with a newer release changes the reproduction environment.

## Build and audit

Install [elan, the Lean version manager](https://github.com/leanprover/elan), and Git. Ensure `lake` is available in the shell. Elan reads `lean-toolchain` from the project directory and installs/selects the requested Lean toolchain. Run the following commands **from the directory containing `lakefile.toml`**:

```text
lake --version
lake exe cache get
lake build
lake env lean Audit.lean
```

The first cache command downloads precompiled mathlib dependencies. Without module arguments it can download a large cache and require substantial disk space. The source archive does not need to contain `.lake/` or a copy of Lean. Initial dependency and toolchain downloads require network access; cached dependencies can be reused on later builds.

`lake build` compiles this project's source modules. `lake env lean Audit.lean` then prints the axiom dependencies of the selected final declarations. Its output should contain only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`, or subsets thereof. It must not contain `sorryAx` or an unproved project-specific axiom. A successful build by itself is not a substitute for this check, because Lean can compile a file containing an admitted proof with a warning.

The verification uses the pinned Lean kernel and mathlib dependencies. Downloading dependency caches does not constitute rebuilding the entirety of mathlib from source. No LaTeX installation, PDF tool, numerical search program, or private service is needed to check the mathematical project.

### Fresh kernel replay

After building, an additional check can replay the imported and local declarations into a fresh kernel environment:

```text
lake env leanchecker --fresh --verbose CollatzEndpoint
```

This checks all safe, non-partial declarations in the target module and its imports using the same official Lean kernel. It is not an independent third-party kernel implementation. The replay does not replace the axiom audit above: declared axioms are permitted by the kernel, so their dependencies must still be inspected. The recorded run completed with exit code 0 in 287.654 seconds; [verification/kernel_fresh_replay.log](verification/kernel_fresh_replay.log) records the command, start and finish times, and status. Runtime on another machine may differ.

### Smaller cache download

As an alternative to the unqualified cache command, this PowerShell command extracts the actual direct mathlib imports from the project and requests those modules and their transitive dependencies:

```powershell
$mathlibImports = Get-ChildItem -LiteralPath './CollatzEndpoint' -Filter '*.lean' |
    Select-String -Pattern '^import (Mathlib\.[A-Za-z0-9_.]+)\s*$' |
    ForEach-Object { $_.Matches[0].Groups[1].Value } |
    Sort-Object -Unique
lake exe cache get @mathlibImports
lake build
lake env lean Audit.lean
```

The direct imports include `Mathlib.Analysis.SpecialFunctions.Stirling`, `Mathlib.Analysis.SpecialFunctions.BinaryEntropy`, `Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics`, `Mathlib.NumberTheory.Padics.PadicVal.Basic`, and the finite-set, filter, and tactic modules used by the source. The complete list is extracted rather than maintained separately. Mathlib's [cache command at the pinned revision](https://github.com/leanprover-community/mathlib4/blob/021c46bdd042f67b538b9f9871d556a93713a9a9/Cache/README.md) accepts module names and includes their imports.

## Main declarations

All names below are in the `CollatzEndpoint` namespace; importing `CollatzEndpoint.MainResults` makes them available.

| Declaration | Result |
| --- | --- |
| `uniform_window_bound` | Every collision-free set has at most `400 * X^beta / (logb 2 X)^gamma` elements in every integer window of length `X >= 2`. |
| `divergent_prefixMax_lower` | Explicit lower bound for the maximum of the first `N` shortcut iterates. |
| `divergent_not_isBigO` | Excludes `O(n^(1/beta) (log_2 n)^c)` for every `c < gamma/beta`. |
| `eventuallyPeriodic_of_critical_power` | A positive shortcut orbit satisfying `O(n^(1/beta))` is eventually periodic. |
| `divergent_odd_prefixMax_lower` | The same prefix-maximum bound for successive odd iterates, including an even initial seed. |
| `eventuallyPeriodic_of_odd_critical_power` | The critical pure-power bound on successive odd iterates implies eventual periodicity. |
| `divergent_reciprocal_summable`, `divergent_odd_reciprocal_summable` | Reciprocal summability for the actual divergent trajectories. |
| `collatz_product_identity`, `divergent_correctionProduct_converges` | Exact drift product formula and convergence of its correction factor for actual odd iterates. |
| `divergent_not_drift_upper` | Excludes every eventual drift upper envelope in Corollary 5.2. |
| `divergent_drift_limsup` | The normalized drift has extended-real limsup at least `gamma/beta`. |

See [THEOREM_MAP.md](THEOREM_MAP.md) for exact paper correspondence, definitions, hypotheses, and proof-route differences. The theorem statements in the source are authoritative.

## Reading the source

`Parity` and `Counting` prove the exact finite combinatorics. `Entropy` defines and characterizes the exact constants. `LayerEstimate` proves the logarithmic gain for every depth. `WindowCover`, `WindowEstimate`, and `Windows` establish the uniform interval theorem. `Dynamics`, `OrbitGrowth`, `Reciprocal`, and `Drift` supply the dynamical and analytic consequences. `MainResults` combines these ingredients into the concrete statements listed above.

The decimal approximations in the paper are explanatory; the formal statements use exact real-number definitions. Finite exploratory computations and literature-search conclusions are not premises of the formal proofs.

## Verification records and contributions

[verification/README.md](verification/README.md) describes the retained build,
axiom, dependency, kernel-replay, and semantic-audit records. The Lean sources and
lock files in this repository match the verified source snapshot; their SHA-256
hashes are listed in [verification/source_sha256.json](verification/source_sha256.json).
The records document local verification of this snapshot. Repository CI results,
when available, are a separate check of the pushed revision.

See [CONTRIBUTING.md](CONTRIBUTING.md) for the required build and axiom checks when
proposing a change.

Citation metadata is available in [CITATION.cff](CITATION.cff).
