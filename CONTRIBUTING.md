# Contributing

This project formalizes the endpoint sparsity and growth statements described in
[THEOREM_MAP.md](THEOREM_MAP.md). Contributions may improve the proofs,
documentation, reproducibility, or library interfaces while preserving the
intended mathematical statements.

Use the versions pinned by `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`. Keep a proposed dependency update separate from a change to
the mathematics, and explain any changed assumptions, constants, domains, or
quantifiers in the pull request.

Before proposing a change, run from the repository root:

```text
lake exe cache get
lake build
lake env lean Audit.lean
```

For a change to a final theorem or its proof dependencies, also run:

```text
lake env leanchecker --fresh --verbose CollatzEndpoint
```

Review the axiom output as well as the compiler result. Final results must not
depend on `sorryAx` or a new unproved project axiom. The standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound` may occur. A build containing an
admitted proof can still succeed with a warning, so build success alone is not
the acceptance criterion.

Keep the source statements and theorem map consistent. Include the exact
reproduction commands and relevant results in the pull request. Do not commit
toolchain installations, `.lake`, local environment files, credentials, or
machine-specific launchers. Existing records under `verification/` describe the
verified snapshot; label new verification records with the revision they check
instead of silently presenting old logs as evidence for a new proof.

Report a mathematical concern by naming the declaration and explaining the
definition, hypothesis, or inference at issue. Discussion of novelty or
literature priority should identify the relevant primary source and statement;
kernel verification alone does not decide those questions.

By contributing, you agree that your contribution is licensed under the
repository's [Apache License 2.0](LICENSE).
