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

  **Documented classical imports (4 axioms total):**
    - `QuantumRelational.ClassicalImports.wigner_continuity_unitary`
    - `QuantumRelational.ClassicalImports.kobayashi_nomizu_uniqueness`
    - `QuantumRelational.ClassicalImports.picard_lindelof_unique`
    - `QuantumRelational.ClassicalImports.frobenius_classification`

  The former fifth axiom `Composite.aczel_continuous_associative_is_mul`
  (strict t-norm / Aczél classification) has been eliminated:
  `Composite.lean` is now axiom-free, and the tensor-product kernel
  composition uniqueness is pinned directly by the independence /
  factor-homogeneity clause (vi) via `mul_of_factor_homogeneous`.

  **SRC layer:**
  The paper has only two primitive axioms: `ax:finite` (finite
  scale-free capacity N) and `ax:relational` (Self-Referential
  Consistency, SRC), joined by the Self-Description principle
  (`prin:self-description`), whose machine-checked spectral content is
  `CyclicRigidity.lean`. The derived saturation clauses are THEOREMS via
  `thm:src-master`.

  **Paper-side clause names (current revision).** The paper's hierarchy
  is stated as SIX clauses; the Lean projection names below are the
  historical eight and are deliberately UNCHANGED. The correspondence:
    * Identity                          <- `S1_identity`, and
      `O_operational_completeness*` (the paper's former clause
      "Operational Completeness" is now Identity's single-evaluation
      case `K x y = 0 -> x = y`)
    * Limit Completeness (= (C2))       <- `S2_completeness`
    * Structural Leibniz (context form, = (C3))
                                        <- `S4_structural_leibniz*`, and
      `S3_basis_profile_symmetry*` (the paper's former clause
      "Basis-Profile Symmetry" is now the basis-anchor case of this
      clause)
    * Scale-Freeness (= `ax:finite`(ii))<- `I_imperceptibility*`
      (the paper's former clause name "Imperceptibility" was renamed
      "Scale-Freeness"; the Lean spelling is unchanged)
    * Transport Consistency (from (C1)) <- `T_transport_consistency*`
    * Basis Isotropy (from (C3))        <- `B_basis_isotropy*`
  See `PAPER_MAPPING.md` §3 for the same table with paper labels.

  The Lean encoding lives in
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

  **(S3) restatement (paper revision May 2026; absorbed in the current
  revision).** The clause (S3) of `thm:src-master` was restated. The
  previous reading "K-profile equality on a basis implies state equality"
  is genuinely false in CP^{N-1}: orthogonal rays can share basis
  K-profiles. The restated (S3) was **Basis-Profile Symmetry**, which in
  the current paper revision is no longer a clause of its own: it is the
  basis-anchor case of **Structural Leibniz (context form)** (= (C3)).
  The Lean names `S3_basis_profile_symmetry*` are unchanged. Its content:
  equal basis profiles yield only the existence of an
  Aut-element fixing the basis pointwise and swapping x ↔ y, NOT
  state equality. The new clause follows directly from (S4) applied
  to the configuration C := S ∪ {x, y} with the involution swapping
  x ↔ y while fixing S, and is exposed as
  `S3_basis_profile_symmetry` (master-theorem projection) and
  `S3_basis_profile_symmetry_direct` (standalone). The auxiliary
  chain `S3_finite_determinacy_*`, `aut_xy_basis_transitive_*`,
  `extend_oracle_from_SRC`, etc., that targeted the v1 reading was
  deleted in this revision (their hypotheses were paper-equivalent
  to false-in-QM bipartition-trivialisation; see SRC.lean §4.3-§4.4
  anchor `S3-OLD-DELETED` for the deletion record).

  Note: `IsFinDimAssocDivAlgDim` is a `def`, not an axiom (it is a
  `Prop`-valued predicate used as a hypothesis in the `frobenius_classification`
  axiom above). Stone's theorem is NOT an axiom in this library, and it is
  no longer backed by a trivially witnessed theorem either: the former
  `ClassicalImports.stone_generator` / `montgomery_zippin_generator` and
  their two Schrodinger-side consumers (`stone_gives_hermitian_generator`,
  `full_derivation_chain`, witness A = 0) have been deleted. The reverse
  direction is proved; the existence direction is the paper's elementary
  finite-dimensional prose argument and appears in Lean only as the
  explicit hypothesis `Schrodinger.HasHermitianGenerator`.

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
    - Composite.kernel_compose_is_unique       (now axiom-free; independence clause)

  Theorems depending additionally on classical imports
  (as expected, matching Appendix C of the paper):
    - Frobenius.frobenius_forces_complex
        → [IsFinDimAssocDivAlgDim, frobenius_classification]
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
import QuantumRelational.SRCv2
import QuantumRelational.CovarianceNoGo
import QuantumRelational.BinaryInsufficiency
import QuantumRelational.ModelExistence
import QuantumRelational.Paper2.GrowthDegree
import QuantumRelational.Paper2.DimensionSelection
import QuantumRelational.Paper2.HomogeneityLaw
import QuantumRelational.QubitRecovery

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

-- Nondegeneracy mechanism (Lemma cyclic-rigidity, spectral core; foundations-only):
--   multiplicity of eigenvalue 1 = number of cycles
#print axioms QuantumRelational.CyclicRigidity.count_root_one_cyclePoly
--   simple spectrum ⟺ single N-cycle
#print axioms QuantumRelational.CyclicRigidity.nodup_iff_single_cycle
--   (0 1)(2 3) has cycle type {2,2} and a degenerate spectrum (N = 4 obstruction)
#print axioms QuantumRelational.CyclicRigidity.doubleTransposition_cycleType
#print axioms QuantumRelational.CyclicRigidity.doubleTransposition_degenerate
--   the single N-cycle's simple spectrum has a non-real member (forces ℂ)
#print axioms QuantumRelational.CyclicRigidity.N_cycle_has_nonreal_root

-- Frobenius trichotomy closure (uses frobenius_classification axiom):
#print axioms QuantumRelational.Frobenius.frobenius_forces_complex

-- ℝ-exclusion (d ≠ 1) discharged at the algebra level from the cube root of unity:
#print axioms QuantumRelational.Frobenius.finrank_ne_one_of_cube_root
-- ℂ forced (d = 2) with d ≠ 1 derived, only the ℍ-exclusion d ≠ 4 as input:
#print axioms QuantumRelational.Frobenius.complex_dimension_from_cube_root

-- Quaternion obstruction (spectral + dimensional):
#print axioms QuantumRelational.Frobenius.quaternion_excluded

-- Z_N cyclic structure via finRotate:
#print axioms QuantumRelational.CyclicEigen.cyclic_group_structure

-- Tensor-product kernel composition uniqueness (axiom-free; independence clause):
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
-- run of this file surfaces every one of the 4 declared classical axioms.

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
-- The eight Lean projections of the Master Theorem `thm:src-master`,
-- each projected from the unified `saturation_hierarchy_general`. On the
-- paper side the hierarchy now has SIX clauses (Identity, Limit
-- Completeness, Structural Leibniz (context form), Scale-Freeness,
-- Transport Consistency, Basis Isotropy); the Lean names below are
-- unchanged, with `O_…` mapping to Identity's single-evaluation case and
-- `S3_…` to Structural Leibniz's basis-anchor case, and
-- `I_imperceptibility` carrying the clause the paper now calls
-- Scale-Freeness (see the file header for the full correspondence).
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
-- (S3) is the Basis-Profile Symmetry statement (the old
-- `S3_finite_determinacy` projection name was replaced by
-- `S3_basis_profile_symmetry` when the paper restated the clause).
-- Paper side, current revision: this is no longer a clause of its own,
-- but the basis-anchor case of Structural Leibniz (context form).
#print axioms QuantumRelational.SRC.S3_basis_profile_symmetry
#print axioms QuantumRelational.SRC.S3_basis_profile_symmetry_direct
#print axioms QuantumRelational.SRC.S4_structural_leibniz
-- (I): the clause the paper now calls **Scale-Freeness** (K-image dense
-- in [0,1]); Lean name unchanged.
#print axioms QuantumRelational.SRC.I_imperceptibility
-- (O): the paper's former "Operational Completeness" clause, now the
-- single-evaluation case of **Identity**; Lean name unchanged.
#print axioms QuantumRelational.SRC.O_operational_completeness
#print axioms QuantumRelational.SRC.T_transport_consistency
#print axioms QuantumRelational.SRC.B_basis_isotropy
#print axioms QuantumRelational.SRC.definability_lemma

-- Direct standalone lemmas for the individual clauses. These bypass the
-- master-theorem packaging (historically they also avoided a residual
-- `sorryAx` from clauses that were still admitted; no `sorryAx` appears
-- anywhere in the library today, as the output of this file shows).
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

-- Bridge: SRC + finite capacity ⇒ v1 Axiom2 packaging. The
-- `axiom2_from_SRC` bridge now takes the v1 `saturation` field as an
-- explicit input (since the v1 reading "K-profile equality on a basis
-- ⟹ x = y" is genuinely false in CP^{N-1} and cannot be derived
-- from SRC + finite capacity). The new SRC-derivable (S3) is the
-- Basis-Profile Symmetry statement above.
#print axioms QuantumRelational.SRC.axiom2_from_SRC
#print axioms QuantumRelational.SRC.structural_leibniz_from_SRC

-- ============================================================
-- v3 paper additions (May 2026)
-- ============================================================
--
-- Paper v3 added three pieces of structure. Each is mechanized to
-- the extent supported by Mathlib + the existing framework:
--
--  1. **Qubit Recovery** (paper Theorem `thm:capacity-dilution-composite`,
--     v3 lines 1688-1715): four-clause structural inheritance of
--     state space, ℂ-coefficients, Born rule, and SU(2) dynamics on
--     the qubit factor of an N≥3 composite. Mechanized in
--     `QubitRecovery.lean`, sorry-free. The mixed-state surjectivity
--     (clause (a)) is now fully proved as the purification theorem
--     `partialTraceE_mixed_purification` via the Mathlib matrix
--     square root `CFC.sqrt`.
--
--  2. **Strict Monotonicity from Transport Consistency** (paper
--     line 1668, clause (iv) of `thm:kernel-composition`):
--     mechanized in `Composite.lean` as
--     `kernel_compose_transport_consistency`,
--     `kernel_compose_strict_mono_left/_right`, and
--     `kernel_compose_strict_mono_from_transport`. Sorry-free.
--
--  3. **SRC Equivalence** (paper Axiom 2, line 351): operational
--     and information-theoretic forms are equivalent under
--     model-theoretic bridges; the bridges encode the paper's
--     prose argument. Mechanized in `SRC.lean` as
--     `src_forms_equivalent` (conditional, with bridge hypotheses)
--     and `aut_invariant_definable_implies_S1` (unconditional
--     diagonal consequence).

-- Qubit Recovery (paper `thm:capacity-dilution-composite`):
#print axioms QuantumRelational.QubitRecovery.qubit_recovery
#print axioms QuantumRelational.QubitRecovery.partialTraceE_pure_product
#print axioms QuantumRelational.QubitRecovery.partialTraceE_kron
#print axioms QuantumRelational.QubitRecovery.local_Born_rule
#print axioms QuantumRelational.QubitRecovery.productForm_summands_commute
#print axioms QuantumRelational.QubitRecovery.kron_unitary_unitary
#print axioms QuantumRelational.QubitRecovery.qubit_recovery_capacity_threshold
-- Mixed-state purification (clause (a), mixed case): every PSD qubit
-- state is the environment-reduced state of a pure composite state.
-- Now fully proved (sorry-free) via the Mathlib matrix square root.
#print axioms QuantumRelational.QubitRecovery.partialTraceE_mixed_purification

-- Strict Monotonicity from Transport (paper line 1668):
#print axioms QuantumRelational.Composite.kernel_compose_transport_consistency
#print axioms QuantumRelational.Composite.kernel_compose_strict_mono_left
#print axioms QuantumRelational.Composite.kernel_compose_strict_mono_right
#print axioms QuantumRelational.Composite.kernel_compose_strict_mono_from_transport
#print axioms QuantumRelational.Composite.strict_mono_of_mono_and_injective

-- SRC Equivalence (v1-retired packaging; see revision note in paper appendix):
#print axioms QuantumRelational.SRC.src_forms_equivalent
#print axioms QuantumRelational.SRC.operational_from_info_theoretic
#print axioms QuantumRelational.SRC.info_theoretic_from_operational
#print axioms QuantumRelational.SRC.aut_invariant_definable_implies_S1

-- ============================================================
-- Corrected axioms (paper revision 2026-07-01): SRCv2 (C1)-(C3)
-- ============================================================

-- (S1) from (C1) and Corollary cor:homogeneity from (C3):
#print axioms QuantumRelational.SRCv2.S1_identity_from_C1
#print axioms QuantumRelational.SRCv2.transitivity_from_C3
#print axioms QuantumRelational.SRCv2.two_point_homogeneity_from_C3
#print axioms QuantumRelational.SRCv2.pair_completeness_from_C3
#print axioms QuantumRelational.SRCv2.permutation_invariance_from_C3
#print axioms QuantumRelational.SRCv2.basis_isotropy_from_C3

-- Covariance No-Go (paper Theorem thm:covariance-nogo):
#print axioms QuantumRelational.CovarianceNoGo.covariance_nogo
#print axioms QuantumRelational.CovarianceNoGo.no_covariant_deterministic_assignment

-- Binary Insufficiency counterexample (paper Theorem thm:binary-insufficiency):
#print axioms QuantumRelational.BinaryInsufficiency.pairwise_overlaps_match
#print axioms QuantumRelational.BinaryInsufficiency.no_unitary_extension
#print axioms QuantumRelational.BinaryInsufficiency.no_antiunitary_extension
#print axioms QuantumRelational.BinaryInsufficiency.no_extension

-- Model Existence (paper Theorem thm:model-existence):
#print axioms QuantumRelational.ModelExistence.model
#print axioms QuantumRelational.ModelExistence.basisRay_isBasisFamily
#print axioms QuantumRelational.ModelExistence.K_image_full
#print axioms QuantumRelational.ModelExistence.limitCompleteness_model
#print axioms QuantumRelational.ModelExistence.context_homogeneity_full_basis
#print axioms QuantumRelational.ModelExistence.context_homogeneity_S3

-- Paper 2, revision 2026-07-05: Bass--Guivarc'h arithmetic and Flatness
-- Theorem (paper Theorems thm:integer-dimension, thm:translation-group):
#print axioms QuantumRelational.Paper2.GrowthDegree.GrowthRanks.classification_low
#print axioms QuantumRelational.Paper2.GrowthDegree.GrowthRanks.flatness_at_three
#print axioms QuantumRelational.Paper2.GrowthDegree.GrowthRanks.dichotomy_at_four
#print axioms QuantumRelational.Paper2.GrowthDegree.degree_heisenberg
#print axioms QuantumRelational.Paper2.GrowthDegree.heisenberg_excluded

-- Paper 2, revision 2026-07-05: corrected D = 3 selection (paper Theorems
-- thm:recurrence, thm:bound-states corrected, thm:d3-unique):
#print axioms QuantumRelational.Paper2.DimensionSelection.heatKernel_summable_iff
#print axioms QuantumRelational.Paper2.DimensionSelection.fall_to_center
#print axioms QuantumRelational.Paper2.DimensionSelection.no_collapse_at_three
#print axioms QuantumRelational.Paper2.DimensionSelection.unique_selfconsistent
#print axioms QuantumRelational.Paper2.DimensionSelection.selection_forces_flatness
#print axioms QuantumRelational.Paper2.DimensionSelection.heisenberg_at_four

-- Paper 2, revision 2026-07-05: No Definable Vertex Distinction (paper
-- Lemma lem:no-definable-distinction, rigorous half of Homogeneity of Law):
#print axioms QuantumRelational.Paper2.HomogeneityLaw.invariant_constant_on_orbit
#print axioms QuantumRelational.Paper2.HomogeneityLaw.permRayEquiv_isKAutomorphism
#print axioms QuantumRelational.Paper2.HomogeneityLaw.no_definable_vertex_distinction

end QuantumRelational.AxiomCheck
