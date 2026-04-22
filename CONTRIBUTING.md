# Contributing

Issues and pull requests are welcome. This repository accompanies a research paper; the main invariants to preserve are:

1. **Zero `sorry` / zero `admit`.** Any PR that introduces either must be marked as WIP and cannot be merged to `main`.
2. **Axiom discipline.** New `axiom` declarations require explicit justification in the PR description, a citation to the classical result being imported, and an update to the axiom list in `README.md` and Appendix C of the paper.
3. **Mathlib pinning.** Bumping the Mathlib revision requires regenerating `lake-manifest.json` and confirming all modules still build. Keep the `lean-toolchain` and `lake-manifest.json` aligned.
4. **Paper-to-Lean consistency.** If a result in `PAPER_MAPPING.md` changes status (proved ↔ partial ↔ not formalized), update the mapping in the same PR as the Lean change.

## How to work locally

```sh
git clone https://github.com/jzilly/QuantumRelational.git
cd QuantumRelational
lake exe cache get
lake build
```

After changes:

```sh
lake build                       # verify everything still type-checks
python3 scripts/dep_graph.py     # refresh dependency report
lake env lean QuantumRelational/AxiomCheck.lean   # confirm axiom list
```

## Style

- Match the existing file-header convention: a module docstring describing the paper section it corresponds to, the key results, and any scope caveats.
- Prefer explicit types and fully-qualified names over `autoImplicit` (disabled project-wide in `lakefile.lean`).
- Keep proofs structured: `by` blocks broken into labeled steps matching the paper-prose proof outline where applicable.

## Reporting issues

Useful bug reports include: Lean/Mathlib version, the exact `lake build` or `lake env lean ...` command, and the error output. Type errors after a Mathlib bump often indicate that the pinned revision needs updating.
