# QuantumRelational

**A Lean 4 formalization of "Existence as Distinguishability: Quantum Mechanics from Finite Graded Equality"**

[![Lean 4](https://img.shields.io/badge/Lean-4.26.0-blue.svg)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.26.0-blueviolet.svg)](https://github.com/leanprover-community/mathlib4)
[![Sorry free](https://img.shields.io/badge/sorry-0-brightgreen.svg)](#verification-status)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)

This repository contains the machine-checked formalization of the mathematical skeleton of the derivation in the paper [*Existence as Distinguishability: Quantum Mechanics from Finite Graded Equality*](https://arxiv.org/abs/2603.11900) by Julian G. Zilly. The paper derives finite-dimensional quantum mechanics from two axioms on a graded-equality kernel $K(x,y) \in [0,1]$; this repo formalizes the algebraic and analytic core of that derivation in the Lean 4 proof assistant.

## Verification status

- **Fully `sorry`-free, zero `admit`.** Every source file is `sorry`-free, including the mixed-state purification `QubitRecovery.partialTraceE_mixed_purification` (every positive-semidefinite qubit state is the environment-reduced state of a pure composite, built from the matrix square root `CFC.sqrt`), which was the last remaining `sorry` and is now fully proved.
- **4 classical theorems imported as axioms**, each a standard result with a literature proof. Every declared axiom is transitively consumed by a headline theorem (verifiable by running `lake env lean QuantumRelational/AxiomCheck.lean`). See [Imported classical theorems](#imported-classical-theorems) below.
- **1 partially proved classical theorem**: Stone's theorem for one-parameter unitary groups. The reverse direction (skew-Hermitian $A$ generates $\exp(tA)$) is fully proved from Mathlib, and generator uniqueness is proved modulo Picard–Lindelöf; the **existence** direction (extracting $H$ from a given $U(t)$) is neither proved nor axiomatized — it is elementary finite-dimensional matrix Lie theory carried by the paper's prose, and appears here only as the explicit hypothesis `Schrodinger.HasHermitianGenerator`. **No vacuously witnessed placeholder remains in the library.** See [Scope limits](#scope-limits).
- **Toolchain**: Lean 4.26.0 + Mathlib v4.26.0 (pinned in `lean-toolchain` and `lake-manifest.json`).

The complete paper-to-Lean cross-reference, with per-statement status for every theorem, definition, lemma, and remark in the paper, is in [`PAPER_MAPPING.md`](PAPER_MAPPING.md).

## What is verified

The Lean formalization mechanizes the following core mathematical results of the paper:

- **Parsimony from Completeness + Saturation** (`Parsimony.lean`): hidden-variable extensions that factor through the $K$-profile are trivial.
- **Born rule ODE uniqueness** (`BornRule.lean`, `BornRuleN2.lean`): the metric-compatibility ODE $[f'(x)]^2 / [f(x)(1-f(x))] = c^2/[x(1-x)]$ with boundary conditions $f(0)=0$, $f(1)=1$ and monotonicity uniquely determines $f(x) = x$, i.e. $p_k = |c_k|^2$. The algebraic step is a machine-checked arcsin/MVT/chain-rule argument.
- **Cyclic eigenvalue structure** (`CyclicEigen.lean`, `SwapMatrix.lean`): for $N \geq 3$, some $N$th root of unity has nonzero imaginary part, forcing $\mathbb{F} \supseteq \mathbb{C}$; $N=2$ eigenvalues are real and closed dynamics is discrete.
- **Nondegenerate-spectrum rigidity of the cyclic generator** (`CyclicRigidity.lean`): the eigenvalue $1$ of the permutation lift $\prod_\ell(\lambda^{n_\ell}-1)$ has multiplicity equal to the number of cycles, so a simple (nondegenerate) spectrum holds **exactly** for a single $N$-cycle (`nodup_iff_single_cycle`); the $N=4$ double transposition $(0\,1)(2\,3)$ has cycle type $\{2,2\}$ and a degenerate spectrum, so it is excluded as a generator despite its real Hadamard unbiased eigenbasis (`doubleTransposition_degenerate`). This is the mechanized spectral core of `lem:cyclic-rigidity`, and it is exactly the machine-checked content of the paper's **Self-Description principle** (`prin:self-description`, single-seed dynamical closure): no relative phase is frozen under the generated flow iff the permutation lift has a simple spectrum, which holds exactly for a single $N$-cycle. It pins the generator to the $N$-cycle, whose spectrum contains a non-real member for $N \geq 3$. Foundations-only (no classical import). The principle itself is a prose-level input recorded in the paper's input ledger (`tab:input-ledger`).
- **Inner product from kernel** (`InnerProduct.lean`): a sesquilinear form $\langle\cdot|\cdot\rangle$ is reconstructed from $K$ on basis states with $K = 1 - |\langle\cdot|\cdot\rangle|^2$.
- **Fubini–Study geometry** (`FubiniStudy.lean`): the projection formula, Taylor expansion identifying $K$ with $g_{FS}$ to second order, and Fisher–Rao proportionality $g_{FS} = F_Q/4$.
- **Metric Bridge → Born rule** (`MetricBridge.lean`): composition of ODE uniqueness (`BornRule`) with Fubini–Study uniqueness (imported from Kobayashi–Nomizu) gives the Born rule as the unique metric-compatible probability assignment.
- **Fourier orthogonality** (`Fourier.lean`): discrete Fourier orthonormality of roots-of-unity modes.
- **Frobenius exclusion of $\mathbb{R}$ and $\mathbb{H}$** (`Frobenius.lean`): the $\mathbb{R}$-exclusion ($d \neq 1$) is discharged at the algebra level and foundations-only — a finite-dimensional real division algebra containing a primitive cube root of unity $\omega$ (the $N=3$ eigenvalue) has real dimension $\neq 1$ (`finrank_ne_one_of_cube_root`), so `complex_dimension_from_cube_root` forces $d = 2$ taking only the quaternionic exclusion $d \neq 4$ as input; $\mathbb{H}$ is excluded by the spectral obstruction (2-sphere of solutions of $x^2+1=0$) and failure of local tomography (`quaternion_excluded`).
- **Capacity halting (arithmetic core)** (`CapacityHalting.lean`): storage inequalities $N^1 < N^{M-1}$ and $\log_2 N < (M{-}1)\log_2 N$ for $N \geq 2$, $M \geq 3$, and Kochen–Specker bit-count $\log_2 N < N^2$.
- **Tensor-product kernel composition** (`Composite.lean`): the composition rule $K_{AB} = 1 - (1-K_A)(1-K_B)$ is the unique continuous, symmetric, associative rule with the correct boundary conditions and the independence (factor-homogeneity) clause. `Composite.lean` is axiom-free: multiplication of affinities is pinned directly by `mul_of_factor_homogeneous`, so the uniqueness theorem `kernel_compose_is_unique` imports no axiom.
- **Schrödinger chain** (`Schrodinger.lean`): $K$-preservation ⟹ transition-probability preservation; via Wigner (imported) this gives unitarity; the reverse direction of Stone's theorem (skew-Hermitian $A \Rightarrow \exp(tA)$ unitary) is fully proved. The generator-existence step is the explicit hypothesis `HasHermitianGenerator`, from which `derivation_chain_of_hermitian_generator` derives $U(t) = e^{-itH}$, unitarity, the group law and $U(0) = 1$; energy conservation from $[H,U] = 0$ is `energy_conservation_from_commutant`.
- **Capacity dilution, scaling, uncertainty** (`Scaling.lean`): phase granularity, Zeno floor, entropic uncertainty (Maassen–Uffink chain).
- **Paper 2 modules** (`QuantumRelational/Paper2/`): sparsity from capacity, Cayley-graph freeness, integer rank of translation lattice, Euclidean-metric emergence, three-dimensional spatial self-consistency. These files support a forthcoming companion paper on spatial emergence.

## Imported classical theorems

Four classical results are declared `axiom` in `ClassicalImports.lean`, each with a citation to its standard proof. No physical assumption is imported as a Lean axiom. Every axiom is consumed by a headline theorem; the consuming theorem is listed in the last column (running `lake env lean QuantumRelational/AxiomCheck.lean` prints the transitive axiom set of each).

| Axiom (Lean) | Classical result | Reference | Consumed by |
|---|---|---|---|
| `wigner_continuity_unitary` | Wigner + continuity excludes antiunitary branch | Wigner 1931; Bargmann 1964 | `Schrodinger.schrodinger_derivation_chain` |
| `kobayashi_nomizu_uniqueness` | Uniqueness of $U(N)$-invariant metric on $\mathbb{C}P^{N-1}$ | Kobayashi–Nomizu 1969 | `FubiniStudy.fubini_study_unique` |
| `picard_lindelof_unique` | Uniqueness of solutions to Lipschitz ODEs | Standard | `Schrodinger.stone_generator_unique_of_local_agreement` |
| `frobenius_classification` | $d \in \{1,2,4\}$ for finite-dim associative division algebras over $\mathbb{R}$ | Frobenius 1878 | `Frobenius.frobenius_forces_complex` |

The predicate `IsFinDimAssocDivAlgDim` is a `def` (not an `axiom`) used as a hypothesis in `frobenius_classification`; it must not be counted as an additional axiom. The former fifth axiom `aczel_continuous_associative_is_mul` (the strict t-norm / Aczél classification) has been eliminated: `Composite.lean` is now axiom-free, with the kernel-composition uniqueness pinned by the explicit independence / factor-homogeneity clause (vi) via `mul_of_factor_homogeneous`.

### Partially proved: Stone's theorem

Stone's theorem is neither imported as an axiom nor stood in for by a placeholder. The former trivially witnessed statements — `ClassicalImports.stone_generator`, `ClassicalImports.montgomery_zippin_generator` and their only consumers `Schrodinger.stone_gives_hermitian_generator`, `Schrodinger.full_derivation_chain`, all witnessed by $A = 0$ with the $U$ hypotheses unused — have been **deleted**. In the current formalization:

- The **reverse direction** (given $A$ skew-Hermitian, $\exp(tA)$ is unitary and satisfies the group property) is fully proved from Mathlib's matrix exponential via `exp_skewHermitian_unitary`, `exp_skewHermitian_group`, `exp_skewHermitian_id`, and `skewHermitian_generator_gives_hermitian`; at the interface, `Schrodinger.hasHermitianGenerator_exp`.
- The **existence half of the forward direction** (given $U(t)$, extract $H$) is an explicit hypothesis, `Schrodinger.HasHermitianGenerator U` := `∃ H, Hᴴ = H ∧ ∀ t, U t = exp (t • (−i • H))`. Its mathematical content is elementary in finite dimension (a continuous one-parameter subgroup of $U(N)$ is smooth and $H = i\,U'(0)$ is Hermitian) and is carried by the paper's prose; the Lean-side gap is a Mathlib interface for extracting $U'(0)$ (matrix logarithm / functional calculus for `Matrix.exp`, e.g. via `Unitary.argSelfAdjoint` in `CStarAlgebra/Unitary/Connected.lean`), which is tractable follow-up work.
- `Schrodinger.derivation_chain_of_hermitian_generator` derives from that hypothesis alone that $U(t) = e^{-itH}$ with $H$ Hermitian, that each $U(t)$ is unitary, that $U$ is a one-parameter group, and that $U(0) = 1$.
- The **uniqueness half of the forward direction** is `Schrodinger.stone_generator_unique_of_local_agreement`, proved modulo `picard_lindelof_unique`.

Montgomery–Zippin (continuous homomorphisms $\mathbb{R} \to U(n)$ are smooth) is the smoothness half of the same prose argument and is likewise a prose-level classical input, with no Lean declaration.

The following are also declared in `ClassicalImports.lean` but fully proved: `schur_lemma` (from Mathlib's `Module.End.exists_eigenvalue`).

## Scope limits

The formalization mechanizes the algebraic and analytic core of each paper-level derivation. Five points of honesty, also documented in the paper's Appendix (`app:formal-verification`):

1. **Abstract axiom components.** Saturation surjectivity (paper Ax. 1(1b)(ii)), Structural Leibniz (Ax. 1(1b)(iv)), and Basis Isotropy (Ax. 2(2c)) are *not* formalized as abstract universal conditions on an arbitrary `DistinguishabilitySpace`. They enter through concrete realizations: the state space $\mathbb{C}P^{N-1}$ (surjectivity), the cyclic permutation `finRotate N` (Leibniz), and Mathlib's `UnitaryGroup` (isotropy). See the header of `Axioms.lean` for the convention.
2. **Parsimony** (Theorem `thm:parsimony-derived`, "Parsimony from Identity and Definability"; Lean symbol `Parsimony.parsimony`). Lean mechanizes the implication *"if $K'$ factors through $K$-profiles, then hidden variables are trivial."* The complementary implication *"Saturation ⟹ every physical extension factors through $K$"* is prose in §5 of the paper and is the substantive physical step.
3. **Stone's forward direction (existence).** Not mechanized and not axiomatized: it is stated as the explicit hypothesis `Schrodinger.HasHermitianGenerator`, its content being the paper's elementary finite-dimensional matrix-Lie-theory argument, pending a Mathlib interface for extracting $U'(0)$. The reverse direction and its helpers are fully proved, and uniqueness is proved modulo Picard–Lindelöf. The former $A = 0$ placeholders have been deleted.
4. **Lie-theoretic and topological steps.** Montgomery–Zippin, Peter–Weyl, and Arzelà–Ascoli are consumed at the paper-prose level; Lean mechanizes only their combinatorial and dimension-counting consequences (via `Module.finrank`).
5. **Prose-level inputs with no Lean counterpart** (itemized in the paper's input ledger, Table `tab:input-ledger`): the **Self-Description principle** (`prin:self-description`, single-seed dynamical closure) — only its spectral content is machine-checked, namely `CyclicRigidity.lean` (no frozen relative phase ⟺ simple spectrum of the permutation lift ⟺ a single $N$-cycle) — the two Stone interface items above (existence direction; missing `U'(0)` interface), the regularity condition (R), and the strict t-norm representation theorem used in the paper's prose proof of kernel composition.

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
├── Parsimony.lean           — No hidden variables (`thm:parsimony-derived` / `Parsimony.parsimony`)
├── ClassicalImports.lean    — Four imported axioms + proved helpers
├── CyclicEigen.lean         — N≥3 forces non-real eigenvalue
├── CyclicRigidity.lean      — nondegenerate spectrum ⟺ single N-cycle
├── SwapMatrix.lean          — N=2 swap matrix rigidity
├── Frobenius.lean           — R and H exclusion (R-exclusion discharged)
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

To reproduce the axiom count for yourself, the module `AxiomCheck.lean` lists `#print axioms` for every top-level result. Run `lake env lean QuantumRelational/AxiomCheck.lean` to see that only the four axioms above (plus Lean's three core axioms `Classical.choice`, `Quot.sound`, `propext`) appear.

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
