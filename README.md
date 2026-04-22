# QuantumRelational

**A Lean 4 formalization of "Existence as Distinguishability: Quantum Mechanics from Finite Graded Equality"**

[![Lean 4](https://img.shields.io/badge/Lean-4.26.0-blue.svg)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.26.0-blueviolet.svg)](https://github.com/leanprover-community/mathlib4)
[![Sorry-free](https://img.shields.io/badge/sorry-0-success.svg)](#verification-status)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)

This repository contains the machine-checked formalization of the mathematical skeleton of the derivation in the paper [*Existence as Distinguishability: Quantum Mechanics from Finite Graded Equality*](https://arxiv.org/abs/2603.11900) by Julian G. Zilly. The paper derives finite-dimensional quantum mechanics from two axioms on a graded-equality kernel $K(x,y) \in [0,1]$; this repo formalizes the algebraic and analytic core of that derivation in the Lean 4 proof assistant.

## Verification status

- **Zero `sorry`, zero `admit`** across all source files.
- **24 modules**, **444 declarations**, **379 theorems and lemmas**.
- **5 classical theorems imported as axioms**, each a standard result with a literature proof. Every declared axiom is transitively consumed by a headline theorem (verifiable by running `lake env lean QuantumRelational/AxiomCheck.lean`). See [Imported classical theorems](#imported-classical-theorems) below.
- **1 partially proved classical theorem**: Stone's theorem for one-parameter unitary groups. The reverse direction (skew-Hermitian $A$ generates $\exp(tA)$) is fully proved from Mathlib; the forward direction (extracting $H$ from a given $U(t)$) uses a trivial witness pending matrix-logarithm theory in Mathlib. See [Scope limits](#scope-limits).
- **Toolchain**: Lean 4.26.0 + Mathlib v4.26.0 (pinned in `lean-toolchain` and `lake-manifest.json`).

The complete paper-to-Lean cross-reference, with per-statement status for every theorem, definition, lemma, and remark in the paper, is in [`PAPER_MAPPING.md`](PAPER_MAPPING.md).

## What is verified

The Lean formalization mechanizes the following core mathematical results of the paper:

- **Parsimony from Completeness + Saturation** (`Parsimony.lean`): hidden-variable extensions that factor through the $K$-profile are trivial.
- **Born rule ODE uniqueness** (`BornRule.lean`, `BornRuleN2.lean`): the metric-compatibility ODE $[f'(x)]^2 / [f(x)(1-f(x))] = c^2/[x(1-x)]$ with boundary conditions $f(0)=0$, $f(1)=1$ and monotonicity uniquely determines $f(x) = x$, i.e. $p_k = |c_k|^2$. The algebraic step is a machine-checked arcsin/MVT/chain-rule argument.
- **Cyclic eigenvalue structure** (`CyclicEigen.lean`, `SwapMatrix.lean`): for $N \geq 3$, some $N$th root of unity has nonzero imaginary part, forcing $\mathbb{F} \supseteq \mathbb{C}$; $N=2$ eigenvalues are real and closed dynamics is discrete.
- **Inner product from kernel** (`InnerProduct.lean`): a sesquilinear form $\langle\cdot|\cdot\rangle$ is reconstructed from $K$ on basis states with $K = 1 - |\langle\cdot|\cdot\rangle|^2$.
- **Fubini–Study geometry** (`FubiniStudy.lean`): the projection formula, Taylor expansion identifying $K$ with $g_{FS}$ to second order, and Fisher–Rao proportionality $g_{FS} = F_Q/4$.
- **Metric Bridge → Born rule** (`MetricBridge.lean`): composition of ODE uniqueness (`BornRule`) with Fubini–Study uniqueness (imported from Kobayashi–Nomizu) gives the Born rule as the unique metric-compatible probability assignment.
- **Fourier orthogonality** (`Fourier.lean`): discrete Fourier orthonormality of roots-of-unity modes.
- **Frobenius exclusion of $\mathbb{R}$ and $\mathbb{H}$** (`Frobenius.lean`): for $N \geq 3$, $\mathbb{R}$ is excluded by the non-real eigenvalue; $\mathbb{H}$ by spectral obstruction (2-sphere of solutions of $x^2+1=0$) and failure of local tomography ($\dim_\mathbb{R}\mathrm{Herm}(\mathbb{H}^n) = n(2n-1) \neq n^2$).
- **Capacity halting (arithmetic core)** (`CapacityHalting.lean`): storage inequalities $N^1 < N^{M-1}$ and $\log_2 N < (M{-}1)\log_2 N$ for $N \geq 2$, $M \geq 3$, and Kochen–Specker bit-count $\log_2 N < N^2$.
- **Tensor-product kernel composition** (`Composite.lean`): the composition rule $K_{AB} = 1 - (1-K_A)(1-K_B)$ is the unique continuous, symmetric, associative rule with the correct boundary conditions, modulo Aczél's theorem.
- **Schrödinger chain** (`Schrodinger.lean`): $K$-preservation ⟹ transition-probability preservation; via Wigner (imported) this gives unitarity; the reverse direction of Stone's theorem (skew-Hermitian $A \Rightarrow \exp(tA)$ unitary) is fully proved.
- **Capacity dilution, scaling, uncertainty** (`Scaling.lean`): phase granularity, Zeno floor, entropic uncertainty (Maassen–Uffink chain).
- **Paper 2 modules** (`QuantumRelational/Paper2/`): sparsity from capacity, Cayley-graph freeness, integer rank of translation lattice, Euclidean-metric emergence, three-dimensional spatial self-consistency. These files support a forthcoming companion paper on spatial emergence.

## Imported classical theorems

Five classical results are declared `axiom` in `ClassicalImports.lean` and `Composite.lean`, each with a citation to its standard proof. No physical assumption is imported as a Lean axiom. Every axiom is consumed by a headline theorem; the consuming theorem is listed in the last column (running `lake env lean QuantumRelational/AxiomCheck.lean` prints the transitive axiom set of each).

| Axiom (Lean) | Classical result | Reference | Consumed by |
|---|---|---|---|
| `wigner_continuity_unitary` | Wigner + continuity excludes antiunitary branch | Wigner 1931; Bargmann 1964 | `Schrodinger.schrodinger_derivation_chain` |
| `kobayashi_nomizu_uniqueness` | Uniqueness of $U(N)$-invariant metric on $\mathbb{C}P^{N-1}$ | Kobayashi–Nomizu 1969 | `FubiniStudy.fubini_study_unique` |
| `picard_lindelof_unique` | Uniqueness of solutions to Lipschitz ODEs | Standard | `Schrodinger.stone_generator_unique_of_local_agreement` |
| `frobenius_classification` | $d \in \{1,2,4\}$ for finite-dim associative division algebras over $\mathbb{R}$ | Frobenius 1878 | `Frobenius.frobenius_forces_complex` |
| `aczel_continuous_associative_is_mul` | Aczél's uniqueness of continuous associative ops with $0,1$ identities | Aczél 1966 | `Composite.kernel_compose_is_unique` |

The predicate `IsFinDimAssocDivAlgDim` is a `def` (not an `axiom`) used as a hypothesis in `frobenius_classification`; earlier drafts of this README counted it as a sixth axiom, which was incorrect.

### Partially proved: Stone's theorem

`stone_generator` and `montgomery_zippin_generator` in `ClassicalImports.lean` are **proved theorems**, not axioms. Their statement takes $U(t)$ as hypothesis and asserts the existence of a skew-Hermitian generator $A$ with $U(t) = \exp(tA)$. In the current formalization:

- The **reverse direction** (given $A$ skew-Hermitian, $\exp(tA)$ is unitary and satisfies the group property) is fully proved from Mathlib's matrix exponential via `exp_skewHermitian_unitary`, `exp_skewHermitian_group`, and `skewHermitian_generator_gives_hermitian`.
- The **forward direction** (given $U(t)$, extract $A$) currently uses a placeholder witness $A = 0$ with the $U$ hypotheses unused. A full proof via Mathlib's `Unitary.argSelfAdjoint` functional-calculus API (`CStarAlgebra/Unitary/Connected.lean`) is tractable follow-up work but not yet in the library.

The following are also declared in `ClassicalImports.lean` but fully proved: `schur_lemma` (from Mathlib's `Module.End.exists_eigenvalue`).

## Scope limits

The formalization mechanizes the algebraic and analytic core of each paper-level derivation. Four points of honesty, also documented in the paper's Appendix C:

1. **Abstract axiom components.** Saturation surjectivity (paper Ax. 1(1b)(ii)), Structural Leibniz (Ax. 1(1b)(iv)), and Basis Isotropy (Ax. 2(2c)) are *not* formalized as abstract universal conditions on an arbitrary `DistinguishabilitySpace`. They enter through concrete realizations: the state space $\mathbb{C}P^{N-1}$ (surjectivity), the cyclic permutation `finRotate N` (Leibniz), and Mathlib's `UnitaryGroup` (isotropy). See the header of `Axioms.lean` for the convention.
2. **Parsimony (Theorem 21).** Lean mechanizes the implication *"if $K'$ factors through $K$-profiles, then hidden variables are trivial."* The complementary implication *"Saturation ⟹ every physical extension factors through $K$"* is prose in §5 of the paper and is the substantive physical step.
3. **Stone's forward direction.** `stone_generator` currently uses $A = 0$ as witness pending matrix-logarithm theory in Mathlib. The reverse direction and its helpers are fully proved.
4. **Lie-theoretic and topological steps.** Montgomery–Zippin, Peter–Weyl, and Arzelà–Ascoli are consumed at the paper-prose level; Lean mechanizes only their combinatorial and dimension-counting consequences (via `Module.finrank`).

## Quick start

Prerequisites: [`elan`](https://github.com/leanprover/elan) (installs the pinned Lean toolchain automatically). No manual Lean install needed.

```sh
git clone https://github.com/jzilly/QuantumRelational.git
cd QuantumRelational
lake exe cache get    # fetch precompiled Mathlib (~2 GB, one-time)
lake build            # verify everything (~2-5 min on cached Mathlib)
```

`lake build` exits with status 0 and no output if the entire formalization type-checks. The `lake exe cache get` step downloads Mathlib oleans from the Mathlib cache; skipping it will trigger a local Mathlib build (~90 min).

To reproduce the dependency report:

```sh
python3 scripts/dep_graph.py
```

This regenerates `scripts/DEPENDENCY_REPORT.md` and `scripts/dep_graph.dot`.

## Repository layout

```
QuantumRelational/
├── Axioms.lean              — DistinguishabilitySpace, Axiom 1, Axiom 2
├── Basic.lean               — Single-basis insufficiency, dynamics skeleton
├── Parsimony.lean           — No hidden variables (Thm 21)
├── ClassicalImports.lean    — Six imported axioms + proved helpers
├── CyclicEigen.lean         — N≥3 forces non-real eigenvalue
├── SwapMatrix.lean          — N=2 swap matrix rigidity
├── Frobenius.lean           — R and H exclusion
├── Fourier.lean             — Discrete Fourier orthogonality
├── InnerProduct.lean        — K from inner product
├── FubiniStudy.lean         — g_FS and Fisher interpretation
├── BornRule.lean            — ODE uniqueness (arcsin chain)
├── BornRuleN2.lean          — N=2 Born rule via normalization
├── MetricBridge.lean        — Metric compatibility → Born rule
├── CapacityHalting.lean     — Storage-inequality arithmetic
├── Schrodinger.lean         — K-pres → unitary → generator chain
├── Composite.lean           — Kernel composition, tensor products
├── Scaling.lean             — Phase granularity, Zeno floor, MUB scaling
├── Main.lean                — Integration entry point
├── AxiomCheck.lean          — #print axioms for key theorems
└── Paper2/                  — Forthcoming space-emergence paper
    ├── Sparsity.lean
    ├── CayleyGraph.lean
    ├── IntegerDimension.lean
    ├── EuclideanMetric.lean
    └── DimensionThree.lean
PAPER_MAPPING.md             — Paper-to-Lean cross-reference (per-statement)
scripts/
├── dep_graph.py             — Dependency graph generator
├── DEPENDENCY_REPORT.md     — Module imports, decl counts, axiom usage
└── dep_graph.dot            — Graphviz source
lakefile.lean                — Build configuration
lean-toolchain               — Pinned Lean version
lake-manifest.json           — Pinned dependency revisions
```

## Verifying the axiom discipline

To reproduce the axiom count for yourself, the module `AxiomCheck.lean` lists `#print axioms` for every top-level result. Run `lake env lean QuantumRelational/AxiomCheck.lean` to see that only the six axioms above (plus Lean's three core axioms `Classical.choice`, `Quot.sound`, `propext`) appear.

## Citation

If you use this formalization in academic work, please cite the paper:

```bibtex
@article{zilly2026existence,
  author = {Zilly, Julian G.},
  title = {Existence as Distinguishability: Quantum Mechanics from Finite Graded Equality},
  journal = {arXiv preprint},
  eprint = {2603.11900},
  year = {2026},
  url = {https://arxiv.org/abs/2603.11900}
}
```

The repository itself can be cited via the `CITATION.cff` file (GitHub's "Cite this repository" button).

## License

MIT — see [LICENSE](LICENSE).

## Acknowledgements

Thanks to Matias Zilly and Alessandro Achille for discussions that clarified the framework's scope and foundations. Proofreading and Lean development were assisted by large-language-model systems.

## Contact

Julian G. Zilly  
ORCID: [0009-0005-6257-0214](https://orcid.org/0009-0005-6257-0214)  
Email: julian@julianzilly.com (general) · research@julianzilly.com (paper correspondence)

Issues and pull requests welcome.
