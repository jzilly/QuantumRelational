/-
  QuantumRelational/AxiomCheck.lean

  Machine-checked verification of axiomatic dependencies.

  This file uses Lean's `#print axioms` command on each of the main
  theorems exported from the formalization. The resulting output lists
  every axiom that the theorem's proof-term ultimately depends on. This
  gives an independent, type-checker-verified account of the axiomatic
  scope of the paper's main conclusions.

  **Expected output (at build time):**
  Each `#print axioms` command emits an `info:` message listing the
  axiomatic dependencies. The dependencies should be exactly the
  documented classical imports for that theorem, plus Lean's three
  standard foundations (`propext`, `Classical.choice`, `Quot.sound`).
  Any other axiom appearing in these lists would be a hidden
  dependency and should be investigated.

  **Documented classical imports (5 axioms total):**
    - `QuantumRelational.ClassicalImports.wigner_continuity_unitary`
    - `QuantumRelational.ClassicalImports.kobayashi_nomizu_uniqueness`
    - `QuantumRelational.ClassicalImports.picard_lindelof_unique`
    - `QuantumRelational.ClassicalImports.frobenius_classification`
    - `QuantumRelational.Composite.aczel_continuous_associative_is_mul`

  **v2 SRC layer (paper v2):**
  The v2 paper has only two primitive axioms: `ax:finite` (finite
  capacity N) and `ax:relational` (Self-Referential Consistency, SRC).
  The eight derived clauses (S1)-(S4), (I), (O), (T), (B) are
  THEOREMS via `thm:src-master`. The Lean encoding lives in
  `QuantumRelational/SRC.lean`. The master theorem
  `saturation_hierarchy_general`, its eight projections, and the
  `definability_lemma` are all proved sorry-free, depending only on
  `[propext, Classical.choice, Quot.sound]`. The K-amalgam
  infrastructure (`Amalgam`, `K_amalgam`, `Amalgam.swapEquiv_gen`,
  `swap_gen_K_pres`, `swap_gen_no_lift`) supplies the structural-Leibniz
  step. The `Axiom1`/`Axiom2` structures used by the rest of the
  library bundle the *consequences* of SRC + finite capacity in a
  directly-consumable form (see `Axioms.lean` doc-header). See bridge
  theorems `SRC.axiom2_from_SRC` and `SRC.structural_leibniz_from_SRC`
  for the formal connection.

  Note: `IsFinDimAssocDivAlgDim` is a `def`, not an axiom (it is a
  `Prop`-valued predicate used as a hypothesis in the `frobenius_classification`
  axiom above). Stone's theorem is NOT an axiom in this library; `stone_generator`
  is a proved theorem with a trivial witness pending matrix-logarithm theory.

  **Standard Lean foundations (not user axioms):**
    - `propext` (propositional extensionality)
    - `Classical.choice` (classical choice)
    - `Quot.sound` (quotient soundness)

  The `info:` output of this file is the machine-verifiable witness that
  the paper's "axiomatic scope" statement (Appendix C of the paper) is
  accurate.

  **Observed axiom dependencies at last build (verified 2026-04-20):**

  Theorems depending ONLY on standard Lean foundations
  (no user axioms: `[propext, Classical.choice, Quot.sound]`):
    - Main.main_theorem                       (bundle of 5 conclusions)
    - Main.conclusion_i_parsimony
    - Main.conclusion_ii_capacity_halting
    - Main.conclusion_iii_complex_forced      (weaker form: non-real eigenvalues)
    - Main.conclusion_iv_born_rule
    - Main.conclusion_v_n2_static
    - BornRule.ode_uniqueness_born_rule       (the analytic core)
    - Parsimony.parsimony
    - CyclicEigen.complex_forced
    - CyclicEigen.N2_eigenvalues_real
    - CyclicEigen.cyclic_group_structure
    - Frobenius.quaternion_excluded            (spectral + dimensional)
    - BornRuleN2.born_rule_n2                  (power-law + normalization)
    - ClassicalImports.schur_lemma             (pure Mathlib proof)
    - MetricBridge.metric_bridge

  Theorems depending additionally on classical imports
  (as expected, matching Appendix C of the paper):
    - Frobenius.frobenius_forces_complex
        → [IsFinDimAssocDivAlgDim, frobenius_classification]
    - Composite.kernel_compose_is_unique
        → [aczel_continuous_associative_is_mul]
    - ClassicalImports.exp_skewHermitian_unitary
        → [Mathlib internals for matrix exponential]

  No HIDDEN axioms detected anywhere in the chain. The Main Theorem
  and all five conclusions have zero user-axiom dependencies (the
  uniqueness-of-ℂ claim in Main uses the weaker "non-real eigenvalue"
  form; the stronger "ℂ is the only division algebra" claim properly
  picks up Frobenius as expected in Frobenius.frobenius_forces_complex).
-/

import QuantumRelational.Main
import QuantumRelational.BornRuleN2
import QuantumRelational.Schrodinger
import QuantumRelational.FubiniStudy
import QuantumRelational.SRC

namespace QuantumRelational.AxiomCheck

-- ============================================================
-- Main theorem: axioms used in the full characterization
-- ============================================================

-- The Main Theorem (bundle of 5 conclusions):
#print axioms QuantumRelational.Main.main_theorem

-- ============================================================
-- Individual conclusion axioms
-- ============================================================

-- Conclusion (i): Parsimony.
#print axioms QuantumRelational.Main.conclusion_i_parsimony

-- Conclusion (ii): Capacity Halting (arithmetic inequality).
#print axioms QuantumRelational.Main.conclusion_ii_capacity_halting

-- Conclusion (iii): Complex numbers are forced for N ≥ 3.
#print axioms QuantumRelational.Main.conclusion_iii_complex_forced

-- Conclusion (iv): Born rule from ODE uniqueness.
#print axioms QuantumRelational.Main.conclusion_iv_born_rule

-- Conclusion (v): N = 2 static (real eigenvalues).
#print axioms QuantumRelational.Main.conclusion_v_n2_static

-- ============================================================
-- Supporting theorems
-- ============================================================

-- Born rule ODE uniqueness (the analytic core):
#print axioms QuantumRelational.BornRule.ode_uniqueness_born_rule

-- Parsimony from factoring through K:
#print axioms QuantumRelational.Parsimony.parsimony

-- Cyclic generator has non-real eigenvalues for N ≥ 3:
#print axioms QuantumRelational.CyclicEigen.complex_forced

-- N = 2 eigenvalues are real:
#print axioms QuantumRelational.CyclicEigen.N2_eigenvalues_real

-- Frobenius trichotomy closure (uses frobenius_classification axiom):
#print axioms QuantumRelational.Frobenius.frobenius_forces_complex

-- Quaternion obstruction (spectral + dimensional):
#print axioms QuantumRelational.Frobenius.quaternion_excluded

-- Z_N cyclic structure via finRotate:
#print axioms QuantumRelational.CyclicEigen.cyclic_group_structure

-- Tensor-product kernel composition uniqueness (uses aczel axiom):
#print axioms QuantumRelational.Composite.kernel_compose_is_unique

-- Born rule at N = 2 (power-law + normalization):
#print axioms QuantumRelational.BornRuleN2.born_rule_n2

-- Schur's lemma (pure Mathlib proof):
#print axioms QuantumRelational.ClassicalImports.schur_lemma

-- Skew-Hermitian exponential is unitary (reverse direction of Stone):
#print axioms QuantumRelational.ClassicalImports.exp_skewHermitian_unitary

-- Metric bridge (connects K to Born rule via ODE):
#print axioms QuantumRelational.MetricBridge.metric_bridge

-- ============================================================
-- Coverage of the three "downstream" axioms (wigner, kobayashi, picard)
-- ============================================================
-- These three axioms are not transitively consumed by the headline theorems
-- above, but are consumed by theorems further down the Schrodinger /
-- FubiniStudy chain. We print their axioms explicitly here so that a single
-- run of this file surfaces every one of the 5 declared classical axioms.

-- Consumes `wigner_continuity_unitary`:
#print axioms QuantumRelational.Schrodinger.schrodinger_derivation_chain

-- Consumes `kobayashi_nomizu_uniqueness`:
#print axioms QuantumRelational.FubiniStudy.fubini_study_unique

-- Consumes `picard_lindelof_unique`:
#print axioms QuantumRelational.Schrodinger.stone_generator_unique_of_local_agreement

-- ============================================================
-- v2 SRC layer (Saturation hierarchy from SRC + finite capacity)
-- ============================================================
--
-- The eight clauses of the Master Theorem `thm:src-master`, each
-- projected from the unified `saturation_hierarchy_general`. The
-- paper's proofs are at lines ~395--454 of
-- `QuantumMechanicsFromFiniteGradedEquality.tex`.
--
-- The general-σ master theorem `saturation_hierarchy_general` and
-- the eight per-clause projections (S1)-(S4), (I), (O), (T), (B)
-- are all sorry-free, depending only on
-- `[propext, Classical.choice, Quot.sound]`. The identity-σ
-- specialization `saturation_hierarchy` and the involutive-σ
-- specialization `saturation_hierarchy_involutive` are likewise
-- sorry-free.
--
-- Structural-Leibniz (S4) for arbitrary σ ∈ Equiv.Perm (Fin m) is
-- closed via the K-amalgam infrastructure
-- (`Amalgam`, `K_amalgam`, `Amalgam.swapEquiv_gen`,
-- `swap_gen_K_pres`, `swap_gen_no_lift`); the `gluing_swap`
-- constructor on `AmalgamRel` lets the swap descend to the
-- quotient without involutivity, so the witness inputs collapse
-- from four conjuncts (involutive case) to three (general case).

#print axioms QuantumRelational.SRC.saturation_hierarchy
#print axioms QuantumRelational.SRC.saturation_hierarchy_involutive
#print axioms QuantumRelational.SRC.saturation_hierarchy_general
#print axioms QuantumRelational.SRC.S1_identity
#print axioms QuantumRelational.SRC.S2_completeness
#print axioms QuantumRelational.SRC.S3_finite_determinacy
#print axioms QuantumRelational.SRC.S4_structural_leibniz
#print axioms QuantumRelational.SRC.I_imperceptibility
#print axioms QuantumRelational.SRC.O_operational_completeness
#print axioms QuantumRelational.SRC.T_transport_consistency
#print axioms QuantumRelational.SRC.B_basis_isotropy
#print axioms QuantumRelational.SRC.definability_lemma

-- Direct (sorry-free) standalone lemmas for the proven clauses.
-- These bypass the master-theorem packaging and so do not pick up the
-- residual `sorryAx` from clauses that remain admitted.
#print axioms QuantumRelational.SRC.S1_identity_direct
#print axioms QuantumRelational.SRC.S2_completeness_direct
#print axioms QuantumRelational.SRC.T_transport_consistency_direct
#print axioms QuantumRelational.SRC.O_operational_completeness_direct
#print axioms QuantumRelational.SRC.I_imperceptibility_direct

-- (O) Operational Completeness via the `MetricKernel` typeclass wrapper:
-- discharges the triangle-inequality hypothesis structurally and gives
-- an unconditional (O) at the cost of an explicit kernel-triangle field.
-- See SRC.lean §4.5 (anchor: TRIANGLE-WRAPPER-O) for the rationale.
#print axioms QuantumRelational.SRC.O_operational_completeness_metric
#print axioms QuantumRelational.SRC.O_operational_completeness_dominates_d

-- (S4) Structural Leibniz: identity-permutation special case and a
-- direct form parameterised by the K-amalgam construction.
#print axioms QuantumRelational.SRC.S4_structural_leibniz_id
#print axioms QuantumRelational.SRC.S4_structural_leibniz_direct

-- (S4) amalgam-infrastructure form (involutive σ): closes (S4) via the
-- K-amalgam construction (KExtension packaging + non-lift) under four
-- named structural hypotheses (involutivity, pointwise σ-K-symmetry,
-- Amalgam.inl injectivity, K_amalgam identity-of-indiscernibles).
#print axioms QuantumRelational.SRC.S4_structural_leibniz_amalgam_involutive
#print axioms QuantumRelational.SRC.amalgam_witness_involutive
#print axioms QuantumRelational.SRC.KExtensionAmalgam
#print axioms QuantumRelational.SRC.Amalgam.swapEquiv
#print axioms QuantumRelational.SRC.Amalgam.swap_K_pres
#print axioms QuantumRelational.SRC.Amalgam.swap_no_lift
#print axioms QuantumRelational.SRC.Amalgam.swap_inl_cfg

-- (B) Basis Isotropy: direct form parameterised by the paper-form
-- function-version of (S4).
#print axioms QuantumRelational.SRC.B_basis_isotropy_direct

-- (B) alternative direct form: parameterised by the K-amalgam
-- construction directly (mirrors `S4_structural_leibniz_direct`'s
-- amalgam_witness).
#print axioms QuantumRelational.SRC.B_basis_isotropy_direct_amalgam

-- (B) alternative angles: the permuted-basis sub-case, the orbit-class
-- factoring via (T), and the orbit-classifier form.
#print axioms QuantumRelational.SRC.B_basis_isotropy_permuted
#print axioms QuantumRelational.SRC.B_basis_isotropy_via_orbit_definability
#print axioms QuantumRelational.SRC.B_basis_isotropy_orbit_classifier

-- Bridge: SRC + finite capacity ⇒ v1 Axiom2 packaging.
#print axioms QuantumRelational.SRC.axiom2_from_SRC
#print axioms QuantumRelational.SRC.structural_leibniz_from_SRC

-- (S3) chain integration: `extend_oracle` discharge from SRC + the
-- four kernel axioms + K_ident, plus the `aut_xy_basis_transitive`
-- bridges and the unconditional / via-augB tightenings of
-- `S3_finite_determinacy`.
#print axioms QuantumRelational.SRC.extend_oracle_from_SRC
#print axioms QuantumRelational.SRC.extend_oracle_from_SRC_aux
#print axioms QuantumRelational.SRC.aut_xy_basis_transitive_from_augB
#print axioms QuantumRelational.SRC.aut_xy_basis_transitive_from_B_via_basis
#print axioms QuantumRelational.SRC.aut_xy_basis_transitive_from_bareB_and_fixator_pulled
#print axioms QuantumRelational.SRC.S3_finite_determinacy_completely_unconditional
#print axioms QuantumRelational.SRC.S3_finite_determinacy_via_augB

end QuantumRelational.AxiomCheck
