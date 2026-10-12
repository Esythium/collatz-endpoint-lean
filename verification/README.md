# Verification records

These records describe the local verification completed on 12 October 2026 for
the source and dependency snapshot distributed in this repository. They are
retained evidence, not a claim that a later revision has already been checked.

| Record | What it records |
| --- | --- |
| `source_sha256.json` | SHA-256 hashes of the project Lean files, `Audit.lean`, and version/configuration lock files; the published copies match the verified source files. |
| `dependency_provenance.json` | The nine dependency revisions, comparison with the locked revisions, and absence of tracked dependency edits at verification time. |
| `build.log` | The project build against the pinned dependencies. |
| `clean_build.log` | A fresh build of all project modules without reusing this project's compiled outputs; external dependency caches were reused. |
| `audit.log` | Printed definitions, final theorem types, and 21 selected transitive axiom closures. |
| `kernel_recheck.log` | A further audit invocation with Lean's `--trust=0` option. |
| `kernel_fresh_replay.log` | A successful `leanchecker --fresh --verbose CollatzEndpoint` replay with timestamps, elapsed time, and exit status. |
| `audit_semantics.txt` | Review of definitions, domains, quantifiers, hypotheses, exact constants, actual orbit integration, and the extended-real limsup. |
| `FORMALIZATION_STATUS.txt` | The completed mathematical scope and the limits of the verification claim. |

The logs are publication copies. Local absolute filesystem paths were removed,
and the development-specific Lake launcher name was normalized to `lake`.
Mathematical output, axiom lists, reported statuses, and timestamps were retained.
The original mathematical Lean source and pinned configuration files were copied
byte for byte; publication editing did not alter the proofs.

The fresh replay uses the official Lean kernel in a fresh environment, including
the imported safe declarations. It is not an independent implementation of the
kernel. Downloaded external dependency caches were used; the record does not
claim a source rebuild of all of mathlib.

The semantic review was performed with AI assistance and is not external peer
review. Kernel checks establish the encoded implications. They do not establish
historical priority, exhaustive literature coverage, or the full Collatz
conjecture.
