# Paper-Lean Mapping

Reference: `QuantumMechanicsFromFiniteGradedEquality.tex` → `lean-verification/QuantumRelational/`

Last updated: 2026-04-30

## Conventions

| Status | Meaning |
|--------|---------|
| ✓ Proved | Full Lean proof, no `sorry`, relies only on Mathlib + the 5 classical imports (Frobenius, Wigner, Kobayashi–Nomizu, Picard–Lindelöf, Aczél) |
| ⚠ Partial | Lean statement exists but is weaker/narrower than the paper claim, or depends on a specific classical axiom, or formalizes only the arithmetic / algebraic core |
| ✗ Not formalized | Paper statement has no Lean counterpart (argued in prose only) |

The five classical imports are listed in the final section. Stone's theorem is partially mechanized rather than imported as an axiom: the reverse direction (skew-Hermitian generates exp) is fully proved from Mathlib's matrix exponential; the uniqueness portion of the forward direction is proved modulo `picard_lindelof_unique`; the existence portion uses a placeholder witness `A = 0` and is not consumed by `schrodinger_derivation_chain` (verifiable via `lake env lean QuantumRelational/AxiomCheck.lean`). All file paths below are relative to `lean-verification/QuantumRelational/`. Theorem names are given in `file.lean : symbol` form.

---

## §1 Introduction — Main Theorem

| Paper Label | Name | Lean location | Status | Notes |
|-------------|------|---------------|--------|-------|
| Thm. `thm:main` | Main Theorem (characterization of relational theories) | `Main.lean : main_theorem`, `conclusion_i_parsimony`, `conclusion_ii_capacity_halting`, `conclusion_iii_complex_forced`, `conclusion_iv_born_rule`, `conclusion_v_n2_static` | ⚠ Partial | The five conclusions of the Main Theorem are stated as a conjunction; each conclusion's proof is in the corresponding sub-file (Parsimony, CapacityHalting, CyclicEigen, BornRule, CyclicEigen.N2_eigenvalues_real). The conjunction itself is `Main.main_theorem`. Status follows from each conclusion's status (Parsimony ✓, CapacityHalting ⚠ arithmetic only, etc.). |

---

## §2 Existence as Distinguishability (sec:graded-equality)

| Paper Label | Name | Lean location | Status | Notes |
|-------------|------|---------------|--------|-------|
| Def. `def:graded-equality` | Graded equality kernel K | `Axioms.lean : DistinguishabilitySpace` | ✓ Proved | Structure captures K_nonneg, K_le_one, K_refl, K_symm, K_ident |
| Rem. `rem:classical-limit` | Classical limit (K binary ⟹ discrete identity) | — | ✗ Not formalized | Prose remark only |
| Prop. `prop:single-basis-insufficient` | Insufficiency of a single reference set | `Basic.lean : single_basis_insufficient` | ✓ Proved | Shows completeness (full K-profile) ⟹ saturation (basis K-profile) |
| Prop. `prop:dynamics-from-self-resolution` | Dynamics from self-resolution | `Basic.lean : cyclic_dynamics_periodic` | ✓ Proved | Every injective endomorphism on Fin N has all points periodic |
| Prop. `prop:cyclicity-from-self-resolution` | Cyclicity from self-resolution | `Basic.lean : cyclic_dynamics_iff_injective` | ✓ Proved | Paired with `cyclic_dynamics_period_bound` |
| Thm. `thm:dynamical-constitution` | Dynamical constitution of identity | — | ✗ Not formalized | Paper narrative theorem combining self-resolution + injectivity |
| Prop. `prop:non-termination` | Non-termination of self-resolution | `Basic.lean : non_terminating_self_resolution` + `no_fixed_point_of_genuine_dynamics` | ✓ Proved | Fixed point ⟹ K(x*, f x*) = 0 |
| Prop. `prop:stochastic-outcomes` | Stochastic outcomes | `Basic.lean : stochastic_outcomes_period_divides_card`, `stochastic_outcomes_rational`, `stochastic_outcomes_uniform_visitation`, `stochastic_outcomes_cycle_period` | ✓ Proved | Period bound, rational frequency, cycle uniformity (via `finRotate`) |
| Rem. `rem:randomized-algorithms` | Randomized-algorithm analogy | — | ✗ Not formalized | Prose only |
| Rem. `rem:randomized-algorithms` | Page–Wootters context | — | ✗ Not formalized | Prose only |
| Rem. `rem:axioms-from-graded-equality` | Axioms motivated by graded equality | — | ✗ Not formalized | Prose-only meta-remark |

---

## §3 Relational Structure and Axioms (sec:axioms)

| Paper Label | Name | Lean location | Status | Notes |
|-------------|------|---------------|--------|-------|
| Def. `def:dspace` | Distinguishability space | `Axioms.lean : DistinguishabilitySpace` | ✓ Proved | See §2 |
| Rem. `rem:K-operational-status` | Operational status of K | — | ✗ Not formalized | Prose only |
| Def. `def:basis` | Basis and capacity N | `Axioms.lean : BasisStructure` + `Axiom1.basis`, `Axiom1.basis_distinguishable` | ✓ Proved | N ≥ 2 required |
| Def. `def:frame` | Measurement frame | — | ✗ Not formalized | Used only informally |
| Def. `def:symmetry-group` | Symmetry group G | `Basic.lean : SymmetryGroup`, `Parsimony.lean : IsKernelAut` | ✓ Proved | Both K-preserving bijection bundle and predicate form |
| Axiom `ax:finite` (1a) | Finite Capacity existence | `Axioms.lean : Axiom1` (fields `N`, `basis`, `basis_distinguishable`) | ✓ Proved | |
| Axiom `ax:finite` (1b)(i) Identity | Identity of indiscernibles | `Axioms.lean : DistinguishabilitySpace.K_ident` | ✓ Proved | |
| Axiom `ax:finite` (1b)(ii) Surjectivity | Every consistent profile is a state | — | ⚠ Partial | Not axiomatized; enters via explicit state-space realizations (Fin N, ℂP^(N-1)); discussed in `Axioms.lean` header |
| Axiom `ax:finite` (1b)(iii) Finite determinacy | Basis-restricted saturation | `Axioms.lean : Axiom2.saturation` | ✓ Proved | Basis-restricted separating set |
| Axiom `ax:finite` (1b)(iv) Structural Leibniz | K-symmetries extend globally | — | ⚠ Partial | Not axiomatized; used concretely via `finRotate N` instantiation; discussed in `Axioms.lean` header |
| Rem. `rem:structural-leibniz-weight` | Weight of Structural Leibniz | — | ✗ Not formalized | Prose only |
| Rem. `rem:finite-bandwidth` | Finite bandwidth interpretation | — | ✗ Not formalized | Prose only |
| Rem. `rem:saturation-stability` | Dynamical stability of saturation | `Parsimony.lean : decoupling_dichotomy`, `decoupling_case_trivial`, `decoupling_case_detectable` | ✓ Proved | Formal version of the decoupling argument |
| Axiom `ax:relational` (2a) Operational Completeness | K(x,y) = 0 ⟹ x = y | `Axioms.lean : DistinguishabilitySpace.K_ident` and `Axiom2.completeness` | ✓ Proved | |
| Axiom `ax:relational` (2b) Transport consistency | Meaningful DOFs are K-comparable | — | ✗ Not formalized | Prose level; no free-floating DOFs |
| Axiom `ax:relational` (2c) Basis isotropy | G acts transitively on bases | — | ⚠ Partial | Not axiomatized; Lie/unitary structure enters via Mathlib `UnitaryGroup`; see `Axioms.lean` header |
| Thm. `thm:permutation-invariance` | Permutation invariance of basis K-values | `Basic.lean : single_basis_insufficient` (related); `CyclicEigen.lean : cyclic_group_structure` | ⚠ Partial | The paper's "forced by Structural Leibniz" direction is not proved; cyclic permutation instantiated directly |
| Lem. `lem:dynamics-constitutive` | Dynamics is constitutive, not superadded | — | ✗ Not formalized | Paper narrative lemma |
| Rem. `rem:axiom-independence` | Axiom independence | — | ✗ Not formalized | Prose only |
| §3 Qutrit worked example `sec:example-n3` | N = 3 concrete computation | — | ✗ Not formalized | Illustrative prose |

---

## §5 Consequences of Relationality (sec:consequences)

| Paper Label | Name | Lean location | Status | Notes |
|-------------|------|---------------|--------|-------|
| Def. `def:hv-extension` | Hidden-variable extension | `Parsimony.lean : HiddenVariableExtension` | ✓ Proved | |
| Thm. `thm:parsimony-derived` | Parsimony (no hidden variables) | `Parsimony.lean : parsimony`, `parsimony_from_axioms`, `hidden_variables_trivial`, `hidden_variables_collapse` | ✓ Proved | Main parsimony result via FactorsThroughK |
| Cor. `cor:parsimony` | Information parsimony G ≅ Aut(X, K) | `Parsimony.lean : IsKernelAut`, `isKernelAut_refl`, `isKernelAut_trans`, `isKernelAut_symm`, `kernel_aut_preserves_equivalence`, `parsimony_aut_characterization` | ✓ Proved | Characterization of physical symmetries as K-automorphisms |
| Rem. `rem:topology-from-K` | Topology from K | — | ✗ Not formalized | Prose only |
| Thm. `thm:complexity-constraint` | Complexity constraint on symmetry | `Basic.lean : symmetry_group_card_perm`, `symmetry_group_traceless_constraint`, `symmetry_group_sq_ge_four`, `symmetry_group_nontrivial`, `symmetry_group_dim_factored`, `symmetry_group_dim_ge_N`, `independent_K_values_lt_sq` | ⚠ Partial | Arithmetic/finite-group skeleton of dim G ≤ N² − 1; Lie-dimension claim is not formalized as a Lie-group bound |
| Thm. `thm:quaternion-obstruction` | Quaternionic obstruction | `Frobenius.lean : quaternion_noncommutative`, `quaternion_many_square_roots_of_neg_one`, `quaternionic_local_tomography_obstruction`, `quaternionic_dimension_discrepancy`, `quaternion_excluded` | ✓ Proved | Spectral obstruction (S² of √−1) plus symplectic-dimension multiplicativity failure. Non-commutativity retained as witness only |
| Rem. `rem:basis-isotropy-physical` | Physical meaning of isotropy | — | ✗ Not formalized | Prose only |
| Prop. `prop:closure` | Closure of the relational system | `Basic.lean : relational_closure_contrapositive`, `relational_closure_symm` | ✓ Proved | |
| Thm. `thm:time-emergence` | Continuous time from one-parameter subgroup | `Basic.lean : OneParameterSubgroup`, `time_evolution_invertible` | ⚠ Partial | Algebraic structure of one-parameter subgroups only; Stone's forward direction imported (see `ClassicalImports.stone_generator` honesty note) |
| Cor. `cor:energy-rate` | Energy as rate of relational update | `Schrodinger.lean : energy_conservation_from_commutant`, `energy_expectation_constant` | ⚠ Partial | Energy conservation from commutant proved; identification E = dK/dt is prose |
| Lem. `lem:intermediate-K` | Intermediate K-values exist | `Basic.lean : intermediate_K_values`, `SecondBasis`, `basis_element_not_maxdist_all` | ✓ Proved | |
| (deleted: `thm:continuity-forced`) | Content moved to `app:structural-conditions` | `Basic.lean : continuity_state_dim_le_group_dim` | ⚠ Partial | Paper label removed; continuity of K is now automatic in the K-pseudometric topology of Axiom (1c). The dimension-count formalization is still useful and now corresponds to the Compactness/Smoothness theorems of Appendix B. |
| Rem. `rem:nyquist-manifold` | Nyquist manifold interpretation | — | ✗ Not formalized | Prose only |
| Thm. `thm:continuous-sampled` | Continuous vs sampled indistinguishability | `Basic.lean : nyquist_sample_count`; `Scaling.lean : quantum_sampling_mub_tomography` | ⚠ Partial | Arithmetic inequalities only (N < 2N; 2(finrank−1) = 2N−2). Nyquist argument is prose |

---

## §6 Emergence of Complex Structure (sec:complex-structure)

| Paper Label | Name | Lean location | Status | Notes |
|-------------|------|---------------|--------|-------|
| Thm. `thm:points-sections` | Points as global sections | `Basic.lean : SignatureSheaf`, `GlobalSection`, `kProfileSection`, `kProfile_injective`, `basis_kProfile_determined`, `basis_sections_distinct` | ✓ Proved | Injectivity of the K-profile map from saturation |
| Rem. `lem:signature-sheaf` | Sheaf perspective | — | ✗ Not formalized | Prose only |
| Rem. `lem:signature-sheaf` | Cocycle selection | — | ✗ Not formalized | Prose only |
| Thm. `thm:dynamics-derived` | Cyclic generator π with spectrum {e^{2πik/N}} | `CyclicEigen.lean : rootOfUnity`, `rootOfUnity_pow`, `nonreal_eigenvalue`, `N2_eigenvalues_real`, `complex_forced`, `orderOf_finRotate`, `card_zpowers_finRotate`, `cyclic_group_structure` | ✓ Proved | Roots of unity + cyclic subgroup structure |
| Rem. `rem:axiom3-status` | Status of any implicit "Axiom 3" | — | ✗ Not formalized | Prose only |
| Thm. `thm:basis-topology` | Basis-space topology | `Basic.lean : basis_space_dim_via_finrank`, `flag_manifold_dim` | ⚠ Partial | Dimension identity only; topological structure itself is prose |
| Lem. `lem:sheaf-complex` | Sheaf glueing / complex structure consistency | `Basic.lean : sheaf_glueing_local`, `sheaf_glueing_identity`, `sheaf_glueing_cocycle` | ✓ Proved | |
| Thm. `thm:frobenius` | Frobenius classification (ℂ is unique) | `Frobenius.lean : C_is_unique_field`, `frobenius_forces_complex`, `quaternion_excluded`; `ClassicalImports.lean : frobenius_classification` (axiom) | ⚠ Partial | Frobenius trichotomy imported as axiom; ℝ/ℍ exclusion proved |
| Cor. `thm:basis-topology` | Flag manifold U(N)/(U(1))^N | `Basic.lean : flag_manifold_dim`, `flag_vs_state_dim`, `basis_space_dim_via_finrank` | ⚠ Partial | Dimension arithmetic only; the Lie-quotient identification is prose |
| Thm. `thm:hilbert-representation` | Hilbert space representation | `Basic.lean : HilbertSpaceRepresentation`, `hilbert_rep_reflexive`, `hilbert_rep_symmetric`, `hilbert_rep_basis_orthogonal`, `hilbert_rep_K_bounded`, `cpn_real_dimension_from_finrank`, `state_space_dim_from_quotient`, `minimal_representation_finrank`, `standard_basis_orthonormal_rep` | ✓ Proved | Faithful embedding into ℂ^N with K = 1 − |⟨·|·⟩|² |
| Rem. `rem:equivariant-injection` | Equivariant injection | — | ✗ Not formalized | Prose only |

---

## §7 Cyclic Symmetry (sec:symmetry)

| Paper Label | Name | Lean location | Status | Notes |
|-------------|------|---------------|--------|-------|
| Lem. `lem:cyclic-rigidity` | Rigidity of cyclic dynamics | `Basic.lean : cyclic_shift_injective`, `cyclic_shift_bijective`, `cyclic_shift_period_N`, `cyclic_shift_minimal_period_zero` | ✓ Proved | Explicit cyclic shift + order-N analysis |
| Rem. `rem:kinematical-vs-dynamical` | Kinematical vs dynamical symmetries | — | ✗ Not formalized | Prose only |
| Lem. `lem:minimal-rep` | Minimal representation is ℂ^N | `Basic.lean : minimal_representation_finrank`, `standard_basis_orthonormal_rep` | ✓ Proved | finrank = N; standard basis orthonormal |
| Thm. `thm:cyclic` | G_dyn ≅ ℤ_N | `CyclicEigen.lean : cyclic_group_structure`, `orderOf_finRotate`, `card_zpowers_finRotate` | ✓ Proved | Via `IsCyclic (Subgroup.zpowers (finRotate N))` with cardinality N |
| Rem. `rem:ZN-to-UN` | From ℤ_N to U(N) | — | ✗ Not formalized | Prose only |

---

## §8 Gauge Symmetry from Sheaf Consistency (sec:gauge)

| Paper Label | Name | Lean location | Status | Notes |
|-------------|------|---------------|--------|-------|
| Thm. `thm:gauge` | Emergence of gauge invariance | `Basic.lean : gauge_invariance_inner_product_sq`, `gauge_invariance_K`, `gauge_invariance_K_clean`, `gauge_invariance_bilateral` | ✓ Proved | Phase-rotation invariance of |⟨·|·⟩|² and hence K |
| Rem. `rem:gauge-berry` | Gauge / Berry connection | — | ✗ Not formalized | Prose only |

---

## §9 The Hilbert Space (sec:hilbert)

| Paper Label | Name | Lean location | Status | Notes |
|-------------|------|---------------|--------|-------|
| Thm. `thm:n2-static` | N = 2 is static / no continuous dynamics | `CyclicEigen.lean : N2_eigenvalues_real`; `SwapMatrix.lean : S_sq_eq_one`, `S_eigenvalues_pm1`, `commuting_with_S_form`, `real_orthogonal_commuting_discrete` | ✓ Proved | Both eigenvalue form (±1 real) and swap-matrix rigidity (discrete {I, −I, S, −S}) |
| Rem. `rem:n2-interpretation` | Interpretation of the N = 2 exception | — | ✗ Not formalized | Prose only |
| Thm. `thm:complex` | Emergence of complex numbers | `CyclicEigen.lean : complex_forced`; `Frobenius.lean : C_is_unique_field`, `frobenius_forces_complex` | ⚠ Partial | Non-real eigenvalue for N ≥ 3 is fully proved; uniqueness depends on imported Frobenius axiom |
| Thm. `thm:inner-product-existence` | Inner product from K | `InnerProduct.lean : kernel_from_inner_product`, `kernel_reflexive`, `kernel_symmetric`, `K_eq_one_iff_orthogonal`, `inner_product_from_kernel_basis`, `standard_basis_orthonormal`, `kernel_standard_basis`, `inner_product_sesquilinear` | ✓ Proved | Standard-basis construction and uniqueness-on-basis (sesquilinear extension) |
| Rem. `rem:fourier-inner-product` | Fourier inner product | `Fourier.lean : roots_of_unity_orthogonality`, `fourier_orthonormal` | ✓ Proved | Discrete Fourier orthogonality |
| Thm. `thm:kernel-inner` | K = 1 − \|⟨·\|·⟩\|² (kernel from inner product) | `InnerProduct.lean : kernel_from_inner_product`, `kernel_reflexive`, `K_eq_one_iff_orthogonal`; `FubiniStudy.lean : K_equals_projection_distance` | ✓ Proved | Both the analytic formula and its projection-distance interpretation |

---

## §10 Geometry and the Born Rule (sec:geometry)

| Paper Label | Name | Lean location | Status | Notes |
|-------------|------|---------------|--------|-------|
| Thm. `thm:fs-from-K` | Fubini–Study from K | `FubiniStudy.lean : fubini_study_form`, `fubini_study_projection`, `K_equals_projection_distance`, `projection_orthogonal`, `K_bounds_from_projection`, `K_taylor_is_gFS_axiom` | ✓ Proved | Projection formula and Taylor expansion K = g_FS + O(‖dψ‖³) (name contains "_axiom" for historical reasons; it is fully proved with explicit remainder) |
| Thm. `thm:fisher-interpretation` | Fisher interpretation g_FS = F_Q/4 | `FubiniStudy.lean : gFS_quarter_FQ` | ✓ Proved | |
| Thm. `thm:fs-unique` | Uniqueness of Fubini–Study | `FubiniStudy.lean : fubini_study_unique`; `ClassicalImports.lean : kobayashi_nomizu_uniqueness` (axiom) | ⚠ Partial | Conclusion proved from imported Kobayashi–Nomizu axiom |
| Lem. `lem:continuity-from-dynamics` | Continuity of probability from reversible dynamics | `MetricBridge.lean : continuity_of_probability`, `K_from_overlap_sq_continuous`, `born_probability_continuous`, `born_probability_from_K_continuous` | ✓ Proved | Composition of continuous maps |
| (deleted: `thm:metric-bridge`; content absorbed into `thm:born-kernel`, `lem:metric-compatibility`) | ODE-uniqueness step within Born rule derivation | `MetricBridge.lean : MetricCompatible`, `metric_bridge`, `metric_bridge_constant`, `id_is_metric_compatible`, `born_rule_unique_metric_compatible`, `fisher_rao_proportionality_constant`, `metric_compatibility_forces_alpha_2`, `FisherRaoWeight`, `fisher_rao_weight_alpha_2` | ✓ Proved | Uses ODE uniqueness from `BornRule.lean` and FS uniqueness from `FubiniStudy.lean`. Now corresponds to `thm:born-kernel` Part 1 / `lem:metric-compatibility` (Step 1b ODE) in the paper. |
| Rem. `rem:born-robustness` | Why squared probabilities | — | ✗ Not formalized | Prose only |
| Rem. `rem:born-robustness` | Geometric monism | — | ✗ Not formalized | Prose only |
| Lem. `lem:metric-compatibility` | Metric compatibility ODE | `BornRule.lean : MetricCompatibilityODE`, `antiderivative_form`, `c_eq_one_of_antideriv`, `f_eq_id_on_unit_interval`, `ode_uniqueness_born_rule` | ✓ Proved | Binary form of the ODE (see next row); uniqueness proved from scratch (no axiom) |
| Rem. `rem:ode-binary-form` | ODE binary form vs per-component | `BornRule.lean` header | ⚠ Partial | Lean uses the binary Bernoulli form `[f']²/[f(1−f)] = c²/[x(1−x)]`; paper Lem. `lem:metric-compatibility` presents the per-component form `[f']²/f = c/x`. The two are equivalent on [0,1]; only the binary form is mechanized |
| Def. `def:measure-setup` | Probability-measure setup | `BornRule.lean : AdmissibleProbAssignment` | ✓ Proved | |
| Thm. `thm:born-kernel` | Born rule from K + metric compatibility | `BornRule.lean : born_f`, `born_f_zero`, `born_f_one`, `born_f_nonneg`, `born_f_le_one`, `born_f_monotone`, `born_f_differentiable`, `born_f_preserves_sum`, `born_admissible`, `id_satisfies_ode`, `id_has_deriv`, `born_rule_unique`, `power_law_forces_alpha_2`, `born_rule_ode_integration`, `boundary_forces_c_eq_1`, `born_rule_normalization`, `born_rule_prob_dist`, `born_rule_normalization_inner` | ✓ Proved | f = id uniqueness is `ode_uniqueness_born_rule`; normalization from ‖ψ‖ = 1 |
| Rem. `rem:born-robustness` | Born rule depends on parsimony | — | ✗ Not formalized | Prose only |
| Cor. `cor:born-n2` | Born rule at N = 2 (beyond Gleason) | `BornRuleN2.lean : QubitNormalization`, `qubit_norm_at_p_1`, `half_power_constraint`, `rpow_half_eq_half_forces_p_1`, `born_rule_n2`, `born_rule_n2_is_identity`, `qubit_normalization`, `qubit_born_from_kernel`, `metric_bridge_n2`, `born_rule_n2_vs_gleason` | ✓ Proved | Power-law + normalization at x=1/2 route |
| Rem. `rem:born-robustness` | Independent routes to α=2 (Gleason + Fisher-Rao consistency); the paper consolidates the historical duplicate-label aliases (`cor:dynamics-born`, `rem:two-arguments`, `rem:born-parsimony-dep`, `rem:why-squared`, `rem:geometric-monism`) into the canonical `rem:born-robustness` | `BornRule.lean : k_affinities_give_born_probabilities`, `k_affinities_born_normalized`, `k_affinity_born_valid`, `KAffinityNormalized`, `k_affinity_nonneg`, `k_affinity_le_one`, `k_affinity_prob_dist` | ✓ Proved | p_k = 1 − K(ψ, a_k) agrees with Born rule |
| Rem. `rem:born-robustness` | Two arguments (Born + metric) | — | ✗ Not formalized | Prose only |
| Cor. `cor:entropic` | Entropic uncertainty | `Scaling.lean : log_reciprocal`, `log_sqrt_eq_half_log`, `maassen_uffink_mub_bound`, `maassen_uffink_full_chain`, `entropic_uncertainty_nontrivial`, `entropy_range_nontrivial` | ✓ Proved | MUB chain −2 log(1/√N) = log N |

---

## §11 Dynamics, Energy, and the Origin of ℏ (sec:evolution)

| Paper Label | Name | Lean location | Status | Notes |
|-------------|------|---------------|--------|-------|
| Cor. `thm:noether` | Energy conservation (Noether) | `Schrodinger.lean : energy_conservation_from_commutant`, `commutant_conjugation_invariant`, `energy_expectation_constant`, `commutator`, `commutator_antisymm`, `commutator_add_left`, `commutator_mul_right`, `unitary_group_inverse`, `unitary_group_inverse_right`, `unitary_group_assoc`, `unitary_from_adjoint_inverse` | ✓ Proved | ⟨ψ(t)\|H\|ψ(t)⟩ = ⟨ψ\|H\|ψ⟩ from [H, U] = 0 |
| Prop. `thm:phase-granularity` | Phase resolution limit | `Scaling.lean : phase_granularity`, `phase_granularity_monotone`, `consecutive_phase_separation` | ✓ Proved | δφ = 2π/N |
| Cor. `cor:phase-granularity` | Finite-N phase granularity | `Scaling.lean : phase_granularity`, `phase_granularity_monotone` | ✓ Proved | |
| Thm. `thm:zeno-floor` | Informational Zeno floor | `Scaling.lean : zeno_floor_positive`, `zeno_floor_upper_bound`, `zeno_floor_monotone_decreasing`, `zeno_floor_qubit`, `zeno_product_in_unit_interval` | ✓ Proved | 1/N² floor properties |
| Thm. `thm:quantum-sampling` | Finite-capacity reconstruction | `Scaling.lean : quantum_sampling_mub_tomography`; `Basic.lean : nyquist_sample_count` | ⚠ Partial | Parameter counting via `finrank`; Peter–Weyl argument itself is prose |
| Cor. `cor:uv-cutoff` | Natural UV cutoff | `Scaling.lean : energy_gap_lower_bound` | ⚠ Partial | Only lower bound on gap formalized; ℏ/δt identification is prose |
| Cor. `thm:quantum-sampling` | Heisenberg uncertainty | `Scaling.lean : entropic_uncertainty_nontrivial`, `maassen_uffink_mub_bound` (Maassen–Uffink form) | ⚠ Partial | Entropic form formalized; product form ΔE·Δt ≥ 2πℏ/N is prose |
| Thm. `thm:schrodinger` | Schrödinger equation | `Schrodinger.lean : unitary_preserves_K`, `K_pres_implies_transition_prob_pres`, `norm_sq_eq_implies_norm_eq`, `K_pres_implies_norm_inner_pres`, `schrodinger_derivation_chain`, `stone_gives_hermitian_generator`, `full_derivation_chain`, `inner_pres_iff_K_pres`; uses `ClassicalImports.wigner_continuity_unitary`, `ClassicalImports.stone_generator` | ⚠ Partial | Steps 1–2 (K-pres ⟹ unitary via Wigner + continuity) fully proved. Step 3 (existence of Hermitian generator) uses Stone as axiom; its current Lean witness is A = 0 (forward direction requires matrix-log theory not in Mathlib). See file headers for honesty notes. Matrix-exponential REVERSE direction fully proved (`ClassicalImports : exp_skewHermitian_unitary`, `skewHermitian_generator_gives_hermitian`, `exp_skewHermitian_group`, `exp_skewHermitian_id`) |

---

## §12 The Capacity Halting Principle (sec:measurement)

| Paper Label | Name | Lean location | Status | Notes |
|-------------|------|---------------|--------|-------|
| Def. `def:info-capacity` | Information-theoretic capacity | `CapacityHalting.lean : info_capacity`, `info_capacity_ge_one`, `info_capacity_mono`, `capacity_is_log_bits`, `total_info_M_measurements`, `measurement_configurations`, `single_measurement_bound` | ✓ Proved | C = log₂ N |
| Prop. `prop:capacity-bound` | Capacity as physical bound | `CapacityHalting.lean : single_measurement_bound`, `capacity_is_log_bits` | ✓ Proved | |
| Def. `def:hv-assignment` | Hidden-variable assignment | `CapacityHalting.lean : HiddenVariableAssignment`, `hva_storage_exceeds_capacity` | ✓ Proved | |
| Thm. `thm:capacity-halting` | Capacity halting principle | `CapacityHalting.lean : capacity_deficit`, `capacity_deficit_bits`, `assignment_count_exceeds_capacity`, `capacity_overflow_strict`, `storage_overflow_ratio`, `storage_overflow_multiplicative`, `assignment_exceeds_capacity_squared` | ⚠ Partial | Arithmetic inequalities `N^1 < N^(M−1)` and `log₂ N < (M−1) log₂ N` fully proved. The physical content (MUB geometry, Kochen–Specker, Chaitin incompressibility) is paper prose only; see file header and paper App. `app:formal-verification` |
| Thm. `thm:ks-bits` | Kochen–Specker bit count | `CapacityHalting.lean : ks_bit_count_exceeds_capacity` | ⚠ Partial | log₂ N < N² arithmetic only (qualitatively-correct loose form). The paper's sharper `(M-1) log₂ N` bit-count, scaling to Θ(N log₂ N) for prime-power N at M = N+1, is argued via MUB structure in `lem:incompressibility`(a) and is paper prose for the full KS projector geometry |
| Lem. `lem:incompressibility` | Incompressibility (Chaitin) | `CapacityHalting.lean : incompressibility_combinatorial`, `mub_overlap_uniform` | ⚠ Partial | (a) combinatorial lower bound proved; (b) Kolmogorov-complexity refinement is paper prose |
| Rem. `rem:mub-existence` | Existence of MUBs | `Scaling.lean : mub_full_tomography_params`, `mub_complete_characterization`, `mub_tomography_sufficient`, `mub_overlap_completeness` | ⚠ Partial | Counting identities proved; existence of N+1 MUBs (prime-power case) is paper prose |
| Rem. `rem:mub-existence` | Compression does not help | — | ✗ Not formalized | Prose only |
| Rem. `rem:contextuality-overflow` | Contextuality as overflow | `CapacityHalting.lean : contextuality_storage_exceeds_capacity`, `contextuality_deficit_factor`, `contextuality_minimal_case`, `contextuality_full` | ⚠ Partial | Bit-count deficit only; full non-contextuality argument is paper prose |
| Lem. `lem:affinity-normalization` | K-affinity normalization | `BornRule.lean : KAffinityNormalized`, `k_affinity_nonneg`, `k_affinity_le_one`, `k_affinity_prob_dist` | ✓ Proved | Σ(1 − K) = 1 as structural predicate |
| Thm. `thm:prob-from-K` | Probabilities from K | `BornRule.lean : k_affinities_give_born_probabilities`, `k_affinities_born_normalized`, `k_affinity_born_valid`, `k_affinity_monotone`, `k_affinity_strict_monotone`, `k_affinity_max_at_zero`, `k_affinity_min_at_one`, `kolmogorov_from_K_structure` | ✓ Proved | Kolmogorov axioms from K-affinities |
| Thm. `thm:contextuality` | Contextuality from finite capacity | `CapacityHalting.lean : contextuality_storage_exceeds_capacity`, `contextuality_full` | ⚠ Partial | Arithmetic part only |
| Thm. `thm:entropy-floor` | Operational entropy floor | `Scaling.lean : entropy_range_nontrivial`, `entropic_uncertainty_nontrivial` | ⚠ Partial | log N > 0 for N ≥ 2; full entropy-floor geometry is prose |
| Thm. `thm:entropy-floor` | Conservation of ignorance | — | ✗ Not formalized | Prose only |
| Thm. `thm:continuum-limit` | Continuum limit → standard QM | — | ✗ Not formalized | Prose only |
| Rem. `thm:continuum-limit` | Entrenchment of finite N | — | ✗ Not formalized | Prose only |
| Def. `def:measurement-interaction` | Measurement as correlation formation | — | ✗ Not formalized | Prose definition |
| Prop. `prop:measurement-born` | Measurement-Born correspondence | `BornRule.lean : k_affinities_give_born_probabilities`, `k_affinities_born_normalized` | ⚠ Partial | K-affinity-to-Born bridge proved; measurement-interaction framing is paper prose |
| Rem. `rem:collapse` | Collapse as correlation formation | — | ✗ Not formalized | Prose only |

---

## §13 Composite Systems and No-Cloning (sec:composite)

| Paper Label | Name | Lean location | Status | Notes |
|-------------|------|---------------|--------|-------|
| Def. `def:independent` | Spatially separated / independent subsystems | `Composite.lean : SpatialSeparation` | ✓ Proved | |
| Thm. `thm:independence-characterization` | Characterization of independence | `Composite.lean : no_signaling_A`, `no_signaling_B`, `no_signaling_general`, `independent_outcomes_product`, `characterization_of_independence`, `local_actions_commute`, `local_symmetries_commute_kernel` | ✓ Proved | No-signaling + factorization + commutativity |
| Lem. `lem:commutativity` | Commutativity of local actions | `Composite.lean : local_actions_commute`, `local_symmetries_commute_kernel` | ✓ Proved | |
| Thm. `thm:capacity-mult` | Capacity multiplicativity | `Composite.lean : dimension_multiplicativity`, `product_basis_self_identical`, `product_basis_mutual_distinguishability`, `product_basis_distinguishable`, `composite_dimension_qubit`, `composite_continuous_threshold` | ✓ Proved | N_AB = N_A · N_B via product basis |
| Def. `def:local-tomography` | Local tomography | `Composite.lean : LocalTomography`, `complex_local_tomography` | ✓ Proved | |
| Thm. `thm:tensor` | Tensor-product structure | `Composite.lean : compositeIndexEquiv`, `composite_index_card`, `composite_index_val_qubit`, `productState`, `productState_apply`, `IsSeparable`, `IsEntangled`, `bellState`, `separable_cross_ratio`, `bell_state_entangled`, `entangled_states_exist`, `product_state_norm_sq_factorizes` | ✓ Proved | Fin NA × Fin NB ≃ Fin(NA·NB), product states, Bell-state entanglement witness |
| Rem. `rem:local-tomography-derived` | Local tomography is derived | `Composite.lean : local_tomography_dimension`, `power_function_multiplicative`, `local_tomography_complex_unique`, `real_fails_local_tomography`, `real_local_tomography_fails`, `quaternionic_local_tomography_fails`, `real_dim_not_multiplicative`, `quaternionic_dim_not_multiplicative`, `local_tomography_parameter_decomposition`, `correlation_parameters_positive`, `qubit_qubit_decomposition`, `qutrit_qutrit_decomposition`, `entanglement_parameter_dominance`, `entanglement_gap` | ✓ Proved | ℂ-case multiplicativity + ℝ/ℍ failure + parameter decomposition |
| Thm. `thm:kernel-composition` | Kernel composition rule from associativity | `Composite.lean : kernel_compose`, `compose_zero_zero`, `compose_one_left`, `compose_one_right`, `compose_zero_left`, `compose_zero_right`, `compose_symm`, `compose_assoc`, `kernel_compose_unique_characterization`, `kernel_compose_survival`, `kernel_compose_unique_from_survival`, `survivalTransform`, `survivalTransform_zero_left`, `survivalTransform_zero_right`, `survivalTransform_one_left`, `survivalTransform_one_right`, `survivalTransform_comm`, `survivalTransform_assoc`, `survival_multiplicativity_from_assoc`, `kernel_compose_is_unique`, `kernel_product_states`, `kernel_compose_eq_zero_iff` | ⚠ Partial | Full uniqueness proved modulo `aczel_continuous_associative_is_mul` axiom (Aczél's theorem for continuous associative operations) |
| Rem. `rem:tensor-kernel` | Tensor kernel interpretation | — | ✗ Not formalized | Prose only |
| Thm. `thm:capacity-dilution-composite` | Capacity dilution | `Composite.lean : capacity_dilution_continuous_dynamics`, `capacity_dilution_sufficient`, `composite_continuous_threshold`; `Scaling.lean : capacity_dilution_ratio`, `effective_phase_granularity`, `composite_phase_finer`, `dilution_ratio_le_one` | ✓ Proved | |
| Cor. `cor:scaling-law` | Scaling law | `Scaling.lean : capacity_dilution_ratio`, `effective_phase_granularity`, `composite_phase_finer`, `dilution_ratio_le_one` | ✓ Proved | |
| Rem. `rem:standard-consequences` | Standard consequences (monogamy, no-cloning) | — | ✗ Not formalized | Prose only |

---

## §14 Discussion (sec:discussion)

All subsections of §14 (`From Distinguishability to Quantum Mechanics`, `Saturation as the Formal Expression of the Ontology`, `Two Routes to Indeterminism`, `Finite-Dimensionality as Fundamental`, `Scope and Refutability`, `Conclusion and Open Questions`) are expository prose and not formalized. Status: ✗ Not formalized.

---

## Appendix A: Classical Theorems Used (app:classical-theorems)

See the Classical Imports section below.

---

## Appendix B: Regularity Conditions (app:structural-conditions)

| Paper Label | Name | Lean location | Status | Notes |
|-------------|------|---------------|--------|-------|
| Thm. `thm:compactness-forced` | Compactness of X and G | — | ✗ Not formalized | Tychonoff + Arzelà–Ascoli argument in paper prose |
| Thm. `thm:smoothness-forced` | Smooth manifold / Lie group | — | ⚠ Partial | Relies on Montgomery–Zippin (imported indirectly via `ClassicalImports`); concrete smoothness not formalized |
| Thm. `thm:K-smooth` | K is C^∞ | — | ✗ Not formalized | Lie-smoothness argument in paper prose |
| Thm. `thm:convexity-forced` | Full state space is convex hull | — | ✗ Not formalized | Density-matrix extension argued in paper prose |

---

## Appendix C: Formal Verification Scope (app:formal-verification)

The paper's own scope statement lists machine-checked results and imported axioms. All six classical imports it enumerates (Frobenius, Wigner, Stone, Kobayashi–Nomizu, Picard–Lindelöf, Aczél) appear in the table below and are the only declared axioms used in the `QuantumRelational` formalization.

---

## Paper 2 cross-references (QuantumRelational/Paper2/)

Not sections of Paper 1, but these files are referenced by Paper 1's main-paper verification and are bundled with the formalization.

| File | Purpose | Status |
|------|---------|--------|
| `Paper2/CayleyGraph.lean` | Translations as fixed-point-free permutations; Cayley graph freeness | ✓ Proved (no sorry/axiom) |
| `Paper2/DimensionThree.lean` | d = 3 as self-consistent spatial dimension (Pólya recurrence + virial) | ✓ Proved (no sorry/axiom) |
| `Paper2/EuclideanMetric.lean` | L¹/L² norm equivalence on ℝ^d; Euclidean emergence | ✓ Proved (no sorry/axiom) |
| `Paper2/IntegerDimension.lean` | Integer rank d of the translation lattice ℤ^d | ✓ Proved (no sorry/axiom) |
| `Paper2/Sparsity.lean` | Hamiltonian sparsity from capacity bound (log₂ N bits) | ✓ Proved (no sorry/axiom) |

---

## Classical Imports (axioms in `ClassicalImports.lean` and `Composite.lean`)

| Axiom | Declared in | Used for (paper label) | Reference |
|-------|-------------|------------------------|-----------|
| `wigner_continuity_unitary` | `ClassicalImports.lean` | Thm. `thm:schrodinger` — unitarity of time evolution (excluding antiunitary branch via continuity) | Wigner (1931) \cite{wigner1931gruppentheorie}; Bargmann (1964) \cite{bargmann1964note} |
| `kobayashi_nomizu_uniqueness` | `ClassicalImports.lean` | Thm. `thm:fs-unique` — uniqueness of U(N)-invariant metric on ℂP^(N-1) | Kobayashi–Nomizu (1969) \cite{kobayashi1969foundations} |
| `picard_lindelof_unique` | `ClassicalImports.lean` | Uniqueness step in smoothness / generator chain (Thm. `thm:schrodinger` related) | Standard ODE theory |
| `IsFinDimAssocDivAlgDim` | `ClassicalImports.lean` | Opaque predicate for "d is the real dimension of a finite-dimensional associative division algebra over ℝ" | Frobenius (1878) |
| `frobenius_classification` | `ClassicalImports.lean` | Thm. `thm:frobenius` — d ∈ {1, 2, 4} for real associative division algebras | Frobenius (1878) |
| `aczel_continuous_associative_is_mul` | `Composite.lean` | Thm. `thm:kernel-composition` — uniqueness of 1 − (1−x)(1−y) via Aczél | Aczél (1966) \cite{aczel1966functional} |

**Provably proved (NOT axioms) but worth flagging:** `stone_generator` and `montgomery_zippin_generator` in `ClassicalImports.lean` are **theorems** (proved from the matrix-exponential REVERSE direction: skew-Hermitian A generates a unitary group `exp(tA)`). However, they do NOT extract the generator of a given U(t) — the witness is A = 0, with the U hypotheses unused. The forward direction (matrix logarithm) is not yet in Mathlib. This caveat is relevant to `thm:schrodinger`, `thm:time-emergence`, and the quantified Lean content of Appendix B (`thm:smoothness-forced`). The reverse direction helpers (`exp_skewHermitian_unitary`, `skewHermitian_generator_gives_hermitian`, `exp_skewHermitian_group`, `exp_skewHermitian_id`) are fully proved and carry the genuine mathematical content used downstream.

`schur_lemma` is also stated in `ClassicalImports.lean` but proved from Mathlib's `Module.End.exists_eigenvalue` (no axiom).
