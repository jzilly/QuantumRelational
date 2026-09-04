# Paper-Lean Mapping

Reference: `QuantumMechanicsFromFiniteGradedEquality.tex` → `lean-verification/QuantumRelational/`

Last updated: re-synced after the 2026-08/09 flow passes on the manuscript (presentation only; no mathematical statement changed). That revision:

- reordered §*Composite Systems and No-Cloning* (`sec:composite`) into dependency order: `thm:kernel-composition` now precedes `thm:capacity-mult` and `thm:tensor`;
- wove several Remark environments into main-text prose and **retired their labels**: `rem:connection-triadic`, `rem:context-boundary`, `rem:triadic-counting`, `rem:independence-characterization`, `rem:nyquist-manifold`, `rem:cyclic-spacing-not-quantum` (rows below name the prose location instead);
- relocated two remarks **with labels intact**: `rem:gauge-berry` (now Appendix `app:structural-conditions`, retitled *Three N-controlled phases distinguished*) and `rem:hamacher` (now in the Deferred Proofs appendix `app:deferred`); `rem:observer-internal` now closes `sec:composite`;
- moved the proofs of `thm:n2-static` and `lem:distance-kernel` to `app:deferred` behind sketches.

Previous sync: against the 2026-07-01 manuscript (`2026_07_01_QuantumMechanicsFromFiniteGradedEquality.tex`) after its saturation-hierarchy consolidation. This pass:

- recorded the **six-clause** saturation hierarchy (`thm:src-master`): Operational Completeness was absorbed into **Identity** (its single-evaluation case `K(x,y) = 0 ⟹ x = y`), Basis-Profile Symmetry into **Structural Leibniz (context form)** (its basis-anchor case), and Imperceptibility was renamed **Scale-Freeness**. *No Lean declaration was renamed*; the Lean names `S1_identity`, `S3_basis_profile_symmetry`, `I_imperceptibility`, `O_operational_completeness`, … now map onto the consolidated paper clauses as recorded in the §3 table below;
- folded the dynamical input into Axiom `ax:relational` as clause **(C4) Dynamical Closure (Self-Description)**, renaming the axiom **Self-Referentially Consistent Closure (SRC)**; the interim standalone Principle `prin:self-description` is retired, its calibration remark `rem:self-description-status` now lives in the paper's `sec:field-selection`, and the machine-checked spectral content is exactly `CyclicRigidity.lean`;
- retired the standalone paper theorem `thm:permutation-invariance` (now cited as Corollary `cor:homogeneity`(iv); Lean `SRCv2.permutation_invariance_from_C3`, unchanged);
- merged the two sampling theorems into the single dual-labelled statement `thm:quantum-sampling` = `thm:continuous-sampled`;
- applied the label renames `prop:closure`→`rem:closure`, `thm:ks-bits`→`lem:ks-bits`, `prop:capacity-bound`→`lem:capacity-bound`, `thm:entropy-floor`→`rem:entropy-floor`, `thm:continuum-limit`→`rem:continuum-limit`, `thm:basis-topology`→`cor:basis-topology`, `thm:independence-characterization`→`rem:independence-characterization`, `thm:cyclic-spectrum`→`lem:cyclic-spectrum`, `thm:fisher-interpretation`→`cor:fisher-interpretation`, `lem:continuity-from-dynamics`→`asm:continuity-from-dynamics`, `thm:noether`→`cor:noether`;
- recorded the new paper anchors `tab:input-ledger` (input ledger), `rem:dynamics-scope`, `rem:c1-status`, `rem:single-seed`, and the relocation of field selection (`sec:field-selection`) and time emergence (`sec:time-emergence`) into §6 *Emergence of Complex Structure* (`sec:complex-structure`);
- removed the two trivially witnessed Stone placeholders from the Lean side (`Schrodinger.stone_gives_hermitian_generator`, `Schrodinger.full_derivation_chain`, together with `ClassicalImports.stone_generator` and `montgomery_zippin_generator` which only they consumed) and replaced them with the explicit hypothesis `Schrodinger.HasHermitianGenerator`;
- corrected two stale statements of this file: the library imports **four** classical axioms, not five or six (the Aczél / strict-t-norm axiom was deleted when `Composite.lean` became axiom-free), and `SRC.definability_lemma` is proved, with no residual `sorry` anywhere in the library.

Earlier layers: v3 (May 2026) Qubit Recovery, strict monotonicity, SRC equivalence; v2 two-axiom restructuring; the July renames (`thm:gauge`, `thm:K-smooth` retitle, `thm:main` restatement) and the removal of `cor:energy-rate`.

## v3 update notes

Paper v3 (May 2026) added three pieces of mathematical content that
were extended into the Lean library:

1. **Qubit Recovery theorem** (`thm:capacity-dilution-composite`,
   paper lines 1688-1715): the full four-clause structural
   inheritance theorem for the qubit factor of an N≥3 composite —
   state space C P^1 / Bloch ball, ℂ-coefficients, Born rule on
   local POVMs, SU(2) dynamics for product-form H. Mechanized in
   the new file `QubitRecovery.lean`. The pure-state, Born-rule, and
   product-form-Hamiltonian commutation clauses are sorry-free; the
   mixed-state purification clause (`partialTraceE_mixed_purification`)
   is now **also sorry-free** — every positive-semidefinite qubit state
   is the environment-reduced state of a pure composite, built from the
   matrix square root `CFC.sqrt`. This was the last residual `sorry` in
   the file, so `QubitRecovery.lean` is now entirely sorry-free (the
   top-level `qubit_recovery` bundle no longer depends on any open
   clause).

2. **Strict monotonicity from Transport Consistency** (paper line
   1668, clause (iv) of `thm:kernel-composition`): the v3 paper
   replaces the prior strict-t-norm appeal with a Transport-
   Consistency-based argument on the joint K-profile. Mechanized in
   `Composite.lean` as `kernel_compose_transport_consistency`,
   `kernel_compose_strict_mono_left/_right`, and
   `kernel_compose_strict_mono_from_transport`. Sorry-free.

3. **SRC equivalence** (paper Axiom 2, line 351): operational form
   (`no_richer_extension`) and information-theoretic form
   (`aut_invariant_definable`) are equivalent under model-theoretic
   bridges encoding the paper's prose argument. Mechanized in
   `SRC.lean` as `src_forms_equivalent` (conditional on bridges) plus
   the unconditional diagonal consequence
   `aut_invariant_definable_implies_S1`. The bridges themselves
   surface the missing model-theoretic content explicitly; downstream
   consumers needing the equivalence can discharge them locally for
   their concrete `(α, K)` instances.

All three additions depend only on `[propext, Classical.choice,
Quot.sound]` (verifiable via `lake env lean
QuantumRelational/AxiomCheck.lean`).

## v2 update notes

The paper was restructured to expose only TWO primitive axioms
(`ax:finite` finite capacity + `ax:relational` Self-Referential
Consistency); the eight named conditions (S1)-(S4), (I), (O), (T), (B)
that previously appeared as separate sub-axioms are now derived in
the Master Theorem `thm:src-master`. The Lean library was extended
with `QuantumRelational/SRC.lean` carrying:

1. The SRC predicate (`SelfReferentialConsistency`) bundling the
   operational and information-theoretic forms.
2. `definability_lemma` (paper Lemma `lem:definability`), proved
   sorry-free.
3. `saturation_hierarchy_general` (Master Theorem `thm:src-master`)
   with all eight clauses derived from SRC + finite capacity for an
   arbitrary K-symmetry σ, proved sorry-free. Identity-σ and
   involutive-σ specializations (`saturation_hierarchy`,
   `saturation_hierarchy_involutive`) are likewise sorry-free. The
   eight projections `S1_identity`, `S2_completeness`, ...,
   `B_basis_isotropy` are exposed individually. **(Current revision:
   the paper's hierarchy is consolidated to six clauses; the eight Lean
   projections are unchanged and two of them now map onto sub-cases of
   consolidated clauses — see the §3 table.)**
4. The K-amalgam construction (`Amalgam`, `K_amalgam`,
   `Amalgam.swapEquiv_gen`, `swap_gen_K_pres`, `swap_gen_no_lift`)
   supplying the structural-Leibniz step underlying (S4) for
   arbitrary σ.
5. Bridges `axiom2_from_SRC` and `structural_leibniz_from_SRC`
   showing the v1 `Axiom1`/`Axiom2`/`StructuralLeibniz` packaging is
   recovered from SRC + finite capacity.

Every theorem above depends only on `[propext, Classical.choice,
Quot.sound]` (verifiable via `lake env lean
QuantumRelational/AxiomCheck.lean`).

Several paper labels were renamed/cut in v2; the §3 and §6 sections
below have been updated:
- `thm:imperceptibility-connectedness` (v1) → `thm:imperceptibility-connectedness` (v2; renamed "Connectedness from Imperceptibility", part (a) extracted to `cor:k-image-full`).
- `thm:complex` (v1) → cut; content subsumed in `lem:sheaf-complex`.
- `thm:contextuality` (v1) → demoted to one-line corollary.

Label drifts in §10/§11/§12 (`thm:cyclic` → `lem:cyclic-spectrum`,
`thm:metric-bridge` absorbed into `thm:born-kernel` and
`lem:metric-compatibility`, `thm:zeno-floor` and `cor:uv-cutoff`
consolidated under `thm:quantum-sampling`) have been resolved in the
rows below; the canonical labels are used and the deprecated aliases
are recorded as deletion notes. The current revision adds the renames
and mergers listed at the top of this file (`prop:closure`→`rem:closure`,
`thm:ks-bits`→`lem:ks-bits`, `prop:capacity-bound`→`lem:capacity-bound`,
`thm:entropy-floor`→`rem:entropy-floor`,
`thm:continuum-limit`→`rem:continuum-limit`,
`thm:basis-topology`→`cor:basis-topology`,
`thm:independence-characterization`→`rem:independence-characterization`,
`thm:cyclic-spectrum`→`lem:cyclic-spectrum`,
`thm:fisher-interpretation`→`cor:fisher-interpretation`,
`lem:continuity-from-dynamics`→`asm:continuity-from-dynamics`,
`thm:noether`→`cor:noether`; `thm:permutation-invariance` deleted in
favour of `cor:homogeneity`(iv); `thm:quantum-sampling` and
`thm:continuous-sampled` merged into one dual-labelled statement).

## Conventions

| Status | Meaning |
|--------|---------|
| ✓ Proved | Full Lean proof, no `sorry`, relies only on Mathlib + the 4 classical imports (Frobenius, Wigner, Kobayashi–Nomizu, Picard–Lindelöf) |
| ⚠ Partial | Lean statement exists but is weaker/narrower than the paper claim, or depends on a specific classical axiom, or formalizes only the arithmetic / algebraic core |
| ✗ Not formalized | Paper statement has no Lean counterpart (argued in prose only) |

The four classical imports are listed in the final section; they are the only `axiom` declarations in the library, and the library is `sorry`-free throughout. Stone's theorem is partially mechanized rather than imported as an axiom: the reverse direction (skew-Hermitian generates `exp`) is fully proved from Mathlib's matrix exponential; the uniqueness portion of the forward direction is proved modulo `picard_lindelof_unique`; the **existence** portion is neither proved nor axiomatized in Lean — it is carried by the paper's elementary finite-dimensional prose argument (matrix Lie theory, `H = i U'(0)`) and appears on the Lean side only as the explicit hypothesis `Schrodinger.HasHermitianGenerator`, consumed by `Schrodinger.derivation_chain_of_hermitian_generator`. The former trivially witnessed (`A = 0`) placeholders have been deleted (see the `thm:schrodinger` row and the Classical Imports section). All file paths below are relative to `lean-verification/QuantumRelational/`. Theorem names are given in `file.lean : symbol` form.

---

## §1 Introduction — Main Theorem

| Paper Label | Name | Lean location | Status | Notes |
|-------------|------|---------------|--------|-------|
| Thm. `thm:main` | Main Theorem: Characterization of Relational Theories | `Main.lean : main_theorem`, `conclusion_i_parsimony`, `conclusion_ii_capacity_halting`, `conclusion_iii_complex_forced`, `conclusion_iv_born_rule`, `conclusion_v_n2_static` | ⚠ Partial | Restated in the 2026-07 revision (same label). The five conclusions of the Main Theorem are stated as a conjunction; each conclusion's proof is in the corresponding sub-file (Parsimony, CapacityHalting, CyclicEigen, BornRule, CyclicEigen.N2_eigenvalues_real). The conjunction itself is `Main.main_theorem`. Status follows from each conclusion's status (Parsimony ✓, CapacityHalting ⚠ arithmetic only, etc.). Conclusion (iii) `conclusion_iii_complex_forced` mechanizes the auxiliary fact that for N ≥ 3 some N-th root of unity is non-real (so a real representation cannot carry the cyclic dynamics); the nondegeneracy mechanism forcing the single N-cycle is now mechanized (`CyclicRigidity.lean`) and the ℝ-exclusion is discharged (`Frobenius.finrank_ne_one_of_cube_root`), leaving the ℍ-exclusion coupling and the geometric identification prose-level (see `lem:cyclic-rigidity` and `thm:frobenius` rows). |

---

## §2 Existence as Distinguishability (sec:graded-equality)

**2026-07 revision:** §2 (`sec:graded-equality`) was reduced to the kernel definition plus one remark. The former self-resolution / stochastic-dynamics statements (`prop:dynamics-from-self-resolution`, `prop:cyclicity-from-self-resolution`, `prop:non-termination`, `prop:stochastic-outcomes`, `thm:dynamical-constitution`) and the randomized-algorithm / graded-equality-motivation remarks were cut from the paper. Their still-valid `Basic.lean` mechanizations (`cyclic_dynamics_periodic`, `cyclic_dynamics_iff_injective`, `cyclic_dynamics_period_bound`, `non_terminating_self_resolution`, `no_fixed_point_of_genuine_dynamics`, `stochastic_outcomes_period_divides_card`, `stochastic_outcomes_rational`, `stochastic_outcomes_uniform_visitation`, `stochastic_outcomes_cycle_period`) are rehomed under `lem:dynamics-constitutive` in §3 below.

| Paper Label | Name | Lean location | Status | Notes |
|-------------|------|---------------|--------|-------|
| Def. `def:graded-equality`, `def:dspace` | Graded equality / distinguishability space K | `Axioms.lean : DistinguishabilitySpace` | ✓ Proved | Structure captures K_nonneg, K_le_one, K_refl, K_symm, K_ident |
| Rem. `rem:classical-limit` (with `rem:K-vs-other-measures`, `rem:why-continuity`) | K versus other distinguishability measures; classical limit | — | ✗ Not formalized | Prose remark only |
| Thm. `thm:binary-insufficiency` (was `prop:single-basis-insufficient`) | Binary Insufficiency (a single reference set cannot separate states) | `Basic.lean : single_basis_insufficient`; `BinaryInsufficiency.lean : pairwise_overlaps_match`, `bargmann_x`, `bargmann_y`, `no_unitary_extension`, `no_antiunitary_extension`, `no_extension` | ✓ Proved | `single_basis_insufficient`: completeness (full K-profile) ⟹ saturation (basis K-profile). The explicit Bargmann-product construction (2i vs 2) and the no-(anti)unitary-extension argument live in `BinaryInsufficiency.lean` (see the 2026-07-01 revision table below). |

---

## §3 Relational Structure and Axioms (sec:axioms)

**Current framing:** the paper has TWO primitive axioms, `ax:finite`
(finite scale-free capacity N) and `ax:relational` (**Self-Referentially
Consistent Closure**, SRC, as the internal clauses (C1)–(C4): three
static, one dynamical). Clause (C4) (Dynamical Closure / Self-Description)
states its kernel-level content in the axiom (one seed context, one
context-preserving operation, continuous extension in the profile metric)
and defers its frozen-label demand to the spectral form used by
`lem:cyclic-rigidity`, paralleling condition (R); the deferred spectral
reading is itemized in the input ledger `tab:input-ledger`. The named saturation conditions,
consolidated in the current revision to **six** clauses (Identity, Limit
Completeness, Structural Leibniz (context form), Scale-Freeness,
Transport Consistency, Basis Isotropy), are derived as Theorem
`thm:src-master`; the former clauses *Operational Completeness* and
*Basis-Profile Symmetry* are now sub-cases of Identity and of Structural
Leibniz respectively, and *Imperceptibility* is renamed *Scale-Freeness*.
**No Lean declaration was renamed on account of this consolidation.**
The Lean library reflects the axiom layer by introducing
`SRC.lean`, which carries the v2 axioms and the master theorem closed
sorry-free for an arbitrary K-symmetry σ; the `Axiom1`/`Axiom2`
structures continue to bundle the *consequences* of SRC + finite
capacity for downstream consumption. See `SRC.axiom2_from_SRC` for the
formal bridge.

| Paper Label | Name | Lean location | Status | Notes |
|-------------|------|---------------|--------|-------|
| Def. `def:dspace` | Distinguishability space | `Axioms.lean : DistinguishabilitySpace` | ✓ Proved | See §2 |
| Def. `def:basis` | Basis and capacity N | `Axioms.lean : BasisStructure` + `Axiom1.basis`, `Axiom1.basis_distinguishable` | ✓ Proved | N ≥ 2 required |
| Def. `def:frame` | Measurement frame | — | ✗ Not formalized | Used only informally |
| Def. `def:symmetry-group` | Symmetry group G | `Basic.lean : SymmetryGroup`, `Parsimony.lean : IsKernelAut`, `SRC.lean : IsKAut`, `SRC.lean : Aut` | ✓ Proved | Bundle and predicate forms |
| **Axiom `ax:finite`** | **Finite Capacity** | `Axioms.lean : Axiom1.N`, `Axiom1.basis`, `Axiom1.basis_distinguishable` | ✓ Stated | Paper v2 primitive axiom (only N, basis, basis-distinct). |
| **Axiom `ax:relational`** | **Self-Referentially Consistent Closure (SRC)**, clauses (C1)–(C4) | `SRC.lean : SelfReferentialConsistency`, **`src_forms_equivalent`, `operational_from_info_theoretic`, `info_theoretic_from_operational`, `aut_invariant_definable_implies_S1` (v3)** | ✓ Stated | Paper v2 primitive axiom. Bundle of (i) `no_richer_extension` (operational form) and (ii) `aut_invariant_definable` (information-theoretic form). v3 (paper line 351) adds the conditional equivalence between the two forms: `src_forms_equivalent` is a biconditional under two model-theoretic *bridge* hypotheses (profile-encoding bridge for forward direction, augmentation bridge for backward direction) that surface the missing model-theoretic content of paper line 351; the bridges themselves remain as structural commitments. The unconditional diagonal consequence `aut_invariant_definable_implies_S1` (info-theoretic ⟹ K-profile equality forces state equality) is proved sorry-free, providing one half of the line-352 paragraph directly. All v3 additions depend only on `[propext, Classical.choice, Quot.sound]`. **Current revision:** the axiom is renamed **Self-Referentially Consistent Closure** and extended with the dynamical clause (C4) (next row); the paper now states the clauses formally, with motivation extracted to a preceding exclusion-schema paragraph. |
| **Ax. `ax:relational`(C4)** (with Rem. `rem:self-description-status`, now in the paper's `sec:field-selection`) | **Dynamical Closure (Self-Description)**: one seed context, one context-preserving operation, continuously extended; the generated flow freezes no relative phase (spectral form in `lem:cyclic-rigidity`) | `CyclicRigidity.lean : cyclePoly`, `count_root_one_cyclePoly`, `nodup_iff_single_cycle`, `not_nodup_of_two_cycles`, `doubleTransposition_cycleType`, `doubleTransposition_degenerate`, `N_cycle_has_nonreal_root`, `finRotate_cycleType` | ⚠ Partial (kernel-level part stated in the axiom; spectral content mechanized) | **Current revision:** the interim standalone Principle `prin:self-description` is retired and folded into Axiom `ax:relational` as clause (C4); the clause's kernel-level existence data (seed basis, context-preserving automorphism, continuous one-parameter family in the profile metric) are axiom content, and the frozen-label demand is deferred to its spectral form, recorded in the input ledger (Table `tab:input-ledger`). It is not a Lean declaration. Its machine-checked spectral content is exactly `CyclicRigidity.lean`: no relative phase is frozen under the generated flow **iff** the permutation lift has a simple spectrum, which holds **exactly** for a single N-cycle (multiplicity of the eigenvalue 1 = number of cycles, `count_root_one_cyclePoly` + `nodup_iff_single_cycle`); the N = 4 double transposition (0 1)(2 3) is verified degenerate and hence excluded (`doubleTransposition_degenerate`), despite its real Hadamard unbiased eigenbasis. Foundations-only `[propext, Classical.choice, Quot.sound]`. Consumed by Lem. `lem:dynamics-constitutive`, Lem. `lem:cyclic-rigidity` and, downstream, Lem. `lem:sheaf-complex` (field selection, `sec:field-selection`). Rem. `rem:self-description-status` (relocated to the paper's `sec:field-selection`) calibrates the clause: the stronger single-orbit-determination reading is false in the derived model by one-dimensional phase retrieval, and the operational discrete-ambiguity reading collapses over ℝ (phases degenerate to signs, so every ambiguity becomes discrete and ℝ would not be excluded), which is why the spectral form is the correct, field-blind strength. Model Existence (`thm:model-existence`) now verifies (C4) for the cyclic clock. Neither the calibration nor the independence witnesses are mechanized. |
| **Tab. `tab:input-ledger`** | **Input ledger: every input beyond the two axioms** | — (bookkeeping table; per-item Lean status is this file) | ✗ Not formalized | New in the current revision. Itemizes each input, where it enters, and whether it is mechanized. The entries that are *prose-level* and deliberately have no Lean counterpart include: the spectral form of dynamical closure (C4) (row above), the Stone existence direction (see `thm:schrodinger`), regularity condition (R) (App. `app:structural-conditions`), and the classical results consumed at prose level (Cartan–Wang, Montgomery–Zippin, Peter–Weyl, Arzelà–Ascoli, strict t-norm representation). |
| **Lem. `lem:definability`** | **Profile Factorization (Definability under (C1))** | `SRC.lean : definability_lemma`, `definability_lemma_binary`; `SRCv2.lean : DefinabilityBinary` | ✓ Proved | Both the binary case (`definability_lemma_binary`, a field of `SelfReferentialConsistency`) and the general k-ary `definability_lemma` are proved sorry-free; the k-ary proof reduces to the binary Definability Lemma applied to the diagonal predicate, exactly the inlined argument of `S1_identity_direct`. (An earlier draft of this file reported a residual `sorry` on the binary→k-ary inductive step; that is stale — the library is sorry-free throughout.) The paper consumes only arity ≤ 2 (Rem. `rem:higher-arity`), for which `SRCv2.DefinabilityBinary` is the current form. |
| **Thm. `thm:src-master`** | **Saturation hierarchy from the axioms (Master Theorem)** | `SRC.lean : saturation_hierarchy_general` (general σ); `saturation_hierarchy` (identity σ); `saturation_hierarchy_involutive` (involutive σ) | ✓ Proved | **Consolidated to six paper clauses** in the current revision (Identity, Limit Completeness, Structural Leibniz (context form), Scale-Freeness, Transport Consistency, Basis Isotropy); four are restatements of Ax. `ax:finite`/`ax:relational`/Def. `def:graded-equality` and two (Transport Consistency, Basis Isotropy) are one-step derivations. **The Lean declaration names are unchanged**: the library still exposes eight projections `S1_identity`, `S2_completeness`, `S3_basis_profile_symmetry`, `S4_structural_leibniz`, `I_imperceptibility`, `O_operational_completeness`, `T_transport_consistency`, `B_basis_isotropy`, two of which (`O_…`, `S3_…`) now correspond to *sub-cases* of consolidated paper clauses rather than to clauses of their own (rows below). All sorry-free. Paper proof: §3 (`sec:axioms`), Thm. `thm:src-master` and its proof sketch. |
| Thm. `thm:src-master` — **Identity** | Full K-profile separates states; in particular `K(x,y) = 0 ⟹ x = y` (single-evaluation case) | `SRC.lean : S1_identity`, `S1_identity_direct`, **`O_operational_completeness`, `O_operational_completeness_direct`, `O_operational_completeness_metric`, `O_operational_completeness_dominates_d`**; `SRCv2.lean : S1_identity_from_C1`; `Axioms.lean : Axiom2.completeness`, `DistinguishabilitySpace.K_ident`; `Parsimony.lean : axiom2_operationally_complete` | ✓ Proved | **Absorption:** the former clause **(O) Operational Completeness** is no longer a separate paper clause — it is Identity's single-evaluation case, so the Lean `O_operational_completeness*` family now maps here. Derived sorry-free; `SRCv2.S1_identity_from_C1` is the current (C1)-based derivation. v1 packaging: structure fields `Axiom2.completeness` / `DistinguishabilitySpace.K_ident`. |
| Thm. `thm:src-master` — **Limit Completeness** (= (C2); also called Saturation) | Realized K-profiles are closed under pointwise limits | `SRC.lean : S2_completeness`, `S2_completeness_direct`; `SRCv2.lean : LimitCompleteness`; `ModelExistence.lean : limitCompleteness_model` | ✓ Proved | Derived sorry-free; the model-side witness (net/filter form via ultrafilter compactness of the unit sphere) is `ModelExistence.limitCompleteness_model`. |
| Thm. `thm:src-master` — **Structural Leibniz (context form)** (= (C3)) | For a finite mutually fully distinguishable anchor C (∅ allowed; a basis S the maximal case), equal K-profiles on C ⟹ the swap x ↔ y extends to a global automorphism fixing C pointwise | `SRC.lean : S4_structural_leibniz`, `S4_structural_leibniz_amalgam_general`, `structural_leibniz_from_SRC`, **`S3_basis_profile_symmetry`, `S3_basis_profile_symmetry_direct`**; `SRCv2.lean : ContextHomogeneity`, `IsContext`; `ModelExistence.lean : context_homogeneity_full_basis`, `context_homogeneity_S3`; `Axioms.lean : StructuralLeibniz`, `permutation_invariance_abstract` | ✓ Proved | **Absorption:** the former clause **Basis-Profile Symmetry** is no longer a separate paper clause — it is the *basis-anchor case* of this clause (anchor C = a full basis S), so the Lean `S3_basis_profile_symmetry*` pair now maps here. The *blanket* form (arbitrary finite anchor) is **not** a clause: it is refuted in the derived model by Thm. `thm:binary-insufficiency`, and the context restriction is the surviving residue (context-boundary discussion in `sec:binary-insufficiency`, prose since 2026-09). Model-side (C3) is proved for full-basis anchors; partial-context (C3) remains open (see Model Existence section). |
| Thm. `thm:src-master` — **Scale-Freeness** (= Ax. `ax:finite`(ii)) | `K(𝒳 × 𝒳)` is dense in [0,1] | `SRC.lean : I_imperceptibility`, `I_imperceptibility_direct`; `ModelExistence.lean : K_image_full` | ✓ Proved | **Rename:** the clause formerly called **Imperceptibility** is now **Scale-Freeness** on the paper side; the Lean names retain the historical `I_imperceptibility` spelling and are unchanged. `ModelExistence.K_image_full` gives the stronger surjectivity `K(𝒳 × 𝒳) = [0,1]` for the model. |
| Thm. `thm:src-master` — **Transport Consistency** (from (C1)) | Every Aut-invariant feature factors through the K-profile map | `SRC.lean : T_transport_consistency`, `T_transport_consistency_direct` | ✓ Proved | Derived sorry-free via the Definability Lemma (`lem:definability`). v1: not axiomatised; prose only. |
| Thm. `thm:src-master` — **Basis Isotropy** (from (C3)) | G acts transitively on the basis manifold 𝔅 | `SRC.lean : B_basis_isotropy`, `B_basis_isotropy_direct`, `B_basis_isotropy_direct_amalgam`, `B_basis_isotropy_permuted`, `B_basis_isotropy_via_orbit_definability`, `B_basis_isotropy_orbit_classifier`; `SRCv2.lean : basis_isotropy_from_C3` | ✓ Proved | Derived sorry-free; paper proof is the N-step element-by-element alignment of bases from (C3), mechanized as `SRCv2.basis_isotropy_from_C3`. v1: enters concretely via Mathlib `UnitaryGroup`. |
| *(retired paper clause name)* Operational Completeness | — | see the **Identity** row | ✓ Proved | Retired as a separate clause in the current revision; absorbed into Identity (single-evaluation case). Lean names unchanged. |
| *(retired paper clause name)* Basis-Profile Symmetry | — | see the **Structural Leibniz (context form)** row | ✓ Proved | Retired as a separate clause in the current revision; absorbed into Structural Leibniz (context form) as the basis-anchor case. Lean names unchanged. The May-2026 history is preserved: the v1 reading "basis-K-profile equality ⟹ x = y" is genuinely false in ℂP^{N-1} (orthogonal rays can share basis profiles), which is why the clause is the Aut-orbit (anchored-swap) statement; the v1 `Axiom2.saturation` field is retained for downstream API stability but is not derivable from the axioms, and the bridge `axiom2_from_SRC` takes it as an explicit input callers must discharge. |
| K-amalgam construction | $X \sqcup_C X$ pushout-style space glued along a K-symmetry | `SRC.lean : Amalgam`, `K_amalgam`, `K_amalgam_refl`, `K_amalgam_symm`, `K_amalgam_nonneg`, `K_amalgam_le_one`, `Amalgam.swapEquiv_gen`, `Amalgam.swap_gen_K_pres`, `Amalgam.swap_gen_no_lift` | ✓ Proved | Inductive type with `gluing` and `gluing_swap` constructors; kernel laws verified; swap automorphism is K-preserving and non-liftable to a labelling extension. Underlies (S4) for arbitrary σ. |
| Bridge: SRC + finite capacity ⇒ v1 `Axiom2` | Compatibility lemma | `SRC.lean : axiom2_from_SRC`, `structural_leibniz_from_SRC` | ✓ Proved | Constructive bridge from SRC + finite capacity to the v1 packaging. |
| Def. `def:s5` | Structural Unambiguity (S5) | `MetricBridge.lean : MetricCompatible`, `metric_bridge`, `id_is_metric_compatible` | ⚠ Partial | S5 = Fisher-Rao = Fubini-Study consistency; mechanised as ODE uniqueness in Born rule chain. Itself derived for finite-N QM as Thm `thm:s5-finite-N`. |
| Rem. `rem:axiom-counting` | Why SRC strength is necessary | — | ✗ Not formalized | Prose only |
| Rem. (no current paper label) | Dynamical stability of saturation / decoupling | `Parsimony.lean : decoupling_dichotomy`, `decoupling_case_trivial`, `decoupling_case_detectable` | ✓ Proved | Formal version of the decoupling argument. The v1 `rem:saturation-stability` (and the `rem:structural-leibniz-weight` / `rem:finite-bandwidth` prose remarks) were removed from the paper in the 2026-07 revision; the Lean decoupling lemmas are retained here as Lean-only content. |
| **Cor. `cor:homogeneity`** | **Homogeneity consequences of (C3)**: (i) transitivity, (ii) two-point homogeneity, (iii) pair-completeness, (iv) **Permutation Invariance** | `SRCv2.lean : transitivity_from_C3`, `two_point_homogeneity_from_C3`, `pair_completeness_from_C3`, `permutation_invariance_from_C3`; (supporting: `Basic.lean : single_basis_insufficient`, `CyclicEigen.lean : cyclic_group_structure`, `Axioms.lean : permutation_invariance_abstract`) | ✓ Proved | All four clauses mechanized sorry-free from (C3), foundations-only. **Clause (iv) replaces the deleted standalone theorem `thm:permutation-invariance`**: the paper now cites Permutation Invariance as `cor:homogeneity`(iv); the Lean name `permutation_invariance_from_C3` is unchanged. Clause (i) is (C3) with the empty anchor; (iv) is (C3) with the anchor 𝓑 ∖ {b_i, b_j}, transpositions generating S_N. |
| *(deleted paper label: `thm:permutation-invariance`)* | Permutation invariance of basis K-values | see `cor:homogeneity`(iv) above | ✓ Proved | The standalone theorem was removed in the current revision; the content is now Corollary `cor:homogeneity`(iv). Lean declaration `SRCv2.permutation_invariance_from_C3` unchanged. |
| Rem. `rem:c1-status` | Status of (C1) relative to (C3) (near-redundancy at the consumed arities) | — | ✗ Not formalized | New in the current revision; prose only. Relevant to the Lean side only in that the chain consumes (C1) at arity ≤ 2 (`SRCv2.DefinabilityBinary`), so no k-ary obligation is outstanding. |
| Lem. `lem:dynamics-constitutive` | Constitutive Necessity of Dynamics | `Basic.lean : cyclic_dynamics_periodic`, `cyclic_dynamics_iff_injective`, `cyclic_dynamics_period_bound`, `non_terminating_self_resolution`, `no_fixed_point_of_genuine_dynamics`, `stochastic_outcomes_period_divides_card`, `stochastic_outcomes_rational`, `stochastic_outcomes_uniform_visitation`, `stochastic_outcomes_cycle_period` | ⚠ Partial | Self-resolution forces genuine (fixed-point-free) dynamics: fixed point ⟹ K(x*, f x*) = 0; every injective endomorphism of Fin N is periodic; period bound, rational visitation frequency, cycle uniformity (via `finRotate`). These `Basic.lean` results were rehomed here from the cut §2 self-resolution/stochastic-outcome propositions; the paper's narrative lemma itself is prose. |
| Rem. `rem:excluded-models` (was `rem:axiom-independence`) | Excluded discrete-K models and axiom independence | — | ✗ Not formalized | Prose only |
| §3 Qutrit worked example `sec:example-n3` | N = 3 concrete computation | — | ✗ Not formalized | Illustrative prose |

### v2 Axiom Layer Summary

The Lean library realises the v2 axiom structure as follows:

| Component | Lean | Status |
|-----------|------|--------|
| Axiom 1 (`ax:finite`) | `Axioms.lean : Axiom1` (N, basis, basis_distinguishable) | ✓ Stated |
| Axiom 2 (`ax:relational`, SRC) | `SRC.lean : SelfReferentialConsistency` | ✓ Stated; operational and information-theoretic forms exposed as fields |
| K-extension `(α, K) ↪ (β, K')` | `SRC.lean : KExtension` | ✓ Stated |
| Strictly-richer relation | `SRC.lean : IsRicherThan` | ✓ Stated |
| Aut-invariant predicates | `SRC.lean : IsAutInvariantBinary`, `IsAutInvariant` | ✓ Stated |
| Definability Lemma (`lem:definability`) | `SRC.lean : definability_lemma_binary` (binary case, field of SRC structure) and `SRC.definability_lemma` (k-ary); `SRCv2.DefinabilityBinary` (current, arity ≤ 2) | ✓ Proved (both, sorry-free) |
| Master Theorem (`thm:src-master`) | `SRC.lean : saturation_hierarchy_general` (and `saturation_hierarchy`, `saturation_hierarchy_involutive`) | ✓ Proved; 8 Lean projections, mapping onto the paper's 6 consolidated clauses (see §3 table) |
| Dynamical closure clause (C4), spectral form | deferred axiom reading; spectral content in `CyclicRigidity.lean` (`nodup_iff_single_cycle`, `count_root_one_cyclePoly`, `doubleTransposition_degenerate`) | ⚠ Clause's spectral form not formalized as stated; spectral content ✓ Proved |
| K-amalgam construction | `SRC.lean : Amalgam`, `K_amalgam`, `Amalgam.swapEquiv_gen`, `swap_gen_K_pres`, `swap_gen_no_lift` | ✓ Proved |
| Bridge to v1 packaging | `SRC.lean : axiom2_from_SRC`, `structural_leibniz_from_SRC` | ✓ Proved (saturation field now an explicit input — see (S3) row) |

### Topological Consequences of the Axioms (sec:axiom-consequences)

| Paper Label | Name | Lean location | Status | Notes |
|-------------|------|---------------|--------|-------|
| Lem. `lem:compactness-from-capacity` | Compactness of α via K-profile homeomorphism | — | ✗ Not formalized | Argued via K-profile map being a homeomorphism onto a compact subset of `[0,1]^N`; uses (S1) for state injectivity and joint K-continuity. (Note: under the v2 (S3) Basis-Profile Symmetry restatement, this lemma's separation step now appeals to (S1) full-K-profile injectivity rather than basis-profile injectivity, as recorded in the paper's §3 closing remark.) |
| Cor. `cor:k-image-full` | K-image equals `[0,1]`, M(K) = ∞ | — | ✗ Not formalized | Was part (a) of the former `thm:imperceptibility-connectedness`; promoted to its own corollary in v2. Closed dense subset of `[0,1]` is `[0,1]`. |
| Thm. `thm:imperceptibility-connectedness` | Connectedness from Imperceptibility (b) | — | ✗ Not formalized | **Renamed from "Imperceptibility-Connectedness equivalence" in v2 to "Connectedness from Imperceptibility"; only part (b) (path-connectedness via the structural identification α ≅ FP^(N-1)) survives. Part (a) (closure-of-K-image-is-[0,1]) is now `cor:k-image-full`.** |

---

## §5 Consequences of Relationality (sec:consequences)

| Paper Label | Name | Lean location | Status | Notes |
|-------------|------|---------------|--------|-------|
| Def. `def:hv-extension` | Hidden-variable extension | `Parsimony.lean : HiddenVariableExtension` | ✓ Proved | |
| Thm. `thm:parsimony-derived` | Parsimony (no hidden variables) | `Parsimony.lean : parsimony`, `parsimony_from_axioms`, `hidden_variables_trivial`, `hidden_variables_collapse` | ✓ Proved | Main parsimony result via FactorsThroughK |
| Cor. `cor:parsimony` | Information parsimony G ≅ Aut(X, K) | `Parsimony.lean : IsKernelAut`, `isKernelAut_refl`, `isKernelAut_trans`, `isKernelAut_symm`, `kernel_aut_preserves_equivalence`, `parsimony_aut_characterization` | ✓ Proved | Characterization of physical symmetries as K-automorphisms |
| Rem. `rem:topology-provenance` (was `rem:topology-from-K`) | Topology Provenance (topology from K) | — | ✗ Not formalized | Prose only |
| Thm. `thm:complexity-constraint` | Complexity constraint on symmetry | `Basic.lean : symmetry_group_card_perm`, `symmetry_group_traceless_constraint`, `symmetry_group_sq_ge_four`, `symmetry_group_nontrivial`, `symmetry_group_dim_factored`, `symmetry_group_dim_ge_N`, `independent_K_values_lt_sq` | ⚠ Partial | Arithmetic/finite-group skeleton of dim G ≤ N² − 1; Lie-dimension claim is not formalized as a Lie-group bound |
| Thm. `thm:quaternion-obstruction` | Quaternionic obstruction | `Frobenius.lean : quaternion_noncommutative`, `quaternion_many_square_roots_of_neg_one`, `quaternionic_local_tomography_obstruction`, `quaternionic_dimension_discrepancy`, `quaternion_excluded` | ✓ Proved | Spectral obstruction (S² of √−1) plus symplectic-dimension multiplicativity failure. Non-commutativity retained as witness only |
| Rem. `rem:closure` (was `prop:closure`) | Closure of the relational system | `Basic.lean : relational_closure_contrapositive`, `relational_closure_symm` | ✓ Proved | **Now a Remark in the paper, not a Proposition; the label was renamed `prop:closure` → `rem:closure` in the current revision.** Lean facts unchanged. |
| Thm. `thm:time-emergence` → **relocated to §6** (`sec:time-emergence`) | Continuous Time as Reconstructed Parameterization | `Basic.lean : OneParameterSubgroup`, `time_evolution_invertible` | ⚠ Partial | The theorem now lives in §6 *Emergence of Complex Structure*, subsection `sec:time-emergence` (see the §6 table); the row is kept here as a pointer. Lean mechanizes the algebraic structure of one-parameter subgroups only. The generator-existence step is **not** imported: it is the paper's elementary finite-dimensional prose argument, exposed in Lean as the explicit hypothesis `Schrodinger.HasHermitianGenerator` (the former trivially witnessed `ClassicalImports.stone_generator` has been deleted). |
| Lem. `lem:intermediate-K` | Intermediate K-values exist | `Basic.lean : intermediate_K_values`, `SecondBasis`, `basis_element_not_maxdist_all` | ✓ Proved | |
| (deleted: `thm:continuity-forced`) | Content moved to `app:structural-conditions` | `Basic.lean : continuity_state_dim_le_group_dim` | ⚠ Partial | Paper label removed; continuity of K is now automatic in the K-pseudometric topology of Axiom (1c). The dimension-count formalization is still useful and now corresponds to the Compactness/Smoothness theorems of Appendix B. |
| Nyquist-manifold discussion (prose in `sec:phase-structure`; label `rem:nyquist-manifold` retired 2026-09) | Nyquist manifold interpretation | — | ✗ Not formalized | Prose only |
| Thm. `thm:continuous-sampled` = `thm:quantum-sampling` (**merged, dual-labelled**) | Sampling, Band Limit, and the Resolution Floor | `Basic.lean : nyquist_sample_count`; `Scaling.lean : quantum_sampling_mub_tomography` (full decl list in the §11 row) | ⚠ Partial | **The two former sampling theorems were merged into one statement in the current revision**, carrying both labels `thm:quantum-sampling` and `thm:continuous-sampled`; either label resolves to the same theorem. Lean side unchanged: arithmetic/parameter-counting only (N < 2N; 2(finrank−1) = 2N−2), the Nyquist / Peter–Weyl band-limit argument is prose. See the `thm:quantum-sampling` row in §11 for the complete declaration list. |

---

## §6 Emergence of Complex Structure (sec:complex-structure)

**Current revision:** field selection and time emergence were relocated *into* this section as the subsections `sec:field-selection` ("The Cyclic Generator and Selection of ℂ": Thm. `thm:dynamics-derived`, Rem. `rem:single-seed`, Lem. `lem:cyclic-rigidity`, Lem. `lem:sheaf-complex`, Thm. `thm:quaternion-obstruction`) and `sec:time-emergence` ("Continuous Time as Band-Limited Interpolation": Thm. `thm:time-emergence`, Rem. `rem:dynamics-scope`). Rows for `thm:time-emergence` and `lem:cyclic-rigidity` that previously sat in §5 and §7 are pointed at from here; the Lean declarations are unchanged.

| Paper Label | Name | Lean location | Status | Notes |
|-------------|------|---------------|--------|-------|
| §6 subsection `sec:field-selection` | The Cyclic Generator and Selection of ℂ | `CyclicRigidity.lean` (whole file); `CyclicEigen.lean : complex_forced`, `N2_eigenvalues_real`; `Frobenius.lean : finrank_ne_one_of_cube_root`, `complex_dimension_from_cube_root`, `quaternion_excluded` | ⚠ Partial | Section anchor. The spectral core (Self-Description ⟹ nondegenerate generator ⟹ single N-cycle ⟹ non-real eigenvalue) is mechanized; the ℍ-exclusion coupling to composites and the geometric identification remain prose. |
| Rem. `rem:single-seed` | The single-seed germ (seed context = orbit of one state under one operation; complementary context = its eigenstructure) | — | ✗ Not formalized | New in the current revision; prose only. Its spectral ingredients are `CyclicRigidity.nodup_iff_single_cycle` (the operation is a single N-cycle) and `Fourier.lean : fourier_orthonormal`, `roots_of_unity_orthogonality` (the eigenbasis is the unbiased Fourier basis). |
| §6 subsection `sec:time-emergence` | Continuous Time as Band-Limited Interpolation | `Basic.lean : OneParameterSubgroup`, `time_evolution_invertible` | ⚠ Partial | Section anchor; holds Thm. `thm:time-emergence` (relocated from §5) and Rem. `rem:dynamics-scope`. |
| Rem. `rem:dynamics-scope` | What the dynamics derivation does and does not pin (the clock is one distinguished one-parameter subgroup of G⁰ ≅ PU(N); a specific Hamiltonian is not derived) | — | ✗ Not formalized | New in the current revision; prose only. This is the paper-side scope note matching the Lean scope of `Schrodinger.lean`: unitarity and the algebraic package are mechanized, the choice of H is not. |
| Thm. `thm:points-sections` | Points as global sections | `Basic.lean : SignatureSheaf`, `GlobalSection`, `kProfileSection`, `kProfile_injective`, `basis_kProfile_determined`, `basis_sections_distinct` | ✓ Proved | Injectivity of the K-profile map from saturation |
| Rem. `lem:signature-sheaf` | Sheaf perspective | — | ✗ Not formalized | Prose only |
| Rem. `lem:signature-sheaf` | Cocycle selection | — | ✗ Not formalized | Prose only |
| Thm. `thm:dynamics-derived` | Cyclic Dynamics from Finite Graded Equality (generator spectrum {e^{2πik/N}}) | `CyclicEigen.lean : rootOfUnity`, `rootOfUnity_pow`, `nonreal_eigenvalue`, `N2_eigenvalues_real`, `complex_forced`, `orderOf_finRotate`, `card_zpowers_finRotate`, `cyclic_group_structure` | ⚠ Partial | Roots of unity + cyclic subgroup structure fully proved. Note: `complex_forced` mechanizes the auxiliary fact that the N-cycle has a non-real eigenvalue for N ≥ 3 (some N-th root of unity is non-real, so a real representation cannot carry the dynamics). The nondegeneracy mechanism that pins the generator to the N-cycle is now mechanized in `CyclicRigidity.lean` (see `lem:cyclic-rigidity` row), and the field selection is completed via `thm:frobenius` (ℝ-exclusion discharged; ℍ-exclusion and geometric identification prose-level). |
| Cor. `cor:basis-topology` | Basis-space topology | `Basic.lean : basis_space_dim_via_finrank`, `flag_manifold_dim` | ⚠ Partial | Dimension identity only; topological structure itself is prose |
| Lem. `lem:sheaf-complex` | Sheaf glueing / complex structure consistency | `Basic.lean : sheaf_glueing_local`, `sheaf_glueing_identity`, `sheaf_glueing_cocycle` | ✓ Proved | |
| Thm. `thm:frobenius` | Frobenius Classification: ℂ is Unique | `Frobenius.lean : C_is_unique_field`, `frobenius_forces_complex`, `finrank_ne_one_of_cube_root`, `complex_dimension_from_cube_root`, `complex_is_the_cube_root_witness`, `quaternion_excluded`; `ClassicalImports.lean : frobenius_classification` (axiom) | ⚠ Partial | Frobenius trichotomy d ∈ {1,2,4} imported as the axiom `frobenius_classification`. **The ℝ-exclusion (d ≠ 1) is now discharged at the algebra level**, foundations-only: `finrank_ne_one_of_cube_root` proves that a finite-dimensional real division algebra containing a primitive cube root of unity ω (the N=3 eigenvalue, `CyclicRigidity.cube_root_of_unity_in_C`) has real dimension ≠ 1. `complex_dimension_from_cube_root` then concludes d = 2 taking only the quaternionic exclusion d ≠ 4 as an input (itself algebraically witnessed by `quaternion_excluded`); `complex_is_the_cube_root_witness` confirms ℂ realizes the d=2 case. The residual `frobenius_forces_complex` is the underlying reduction of {1,2,4} → 2. What remains prose-level: the coupling of d ≠ 4 to composite systems, and the geometric identification 𝒳 ≅ ℂP^{N-1}. |
| Cor. `cor:basis-topology` | Flag manifold U(N)/(U(1))^N | `Basic.lean : flag_manifold_dim`, `flag_vs_state_dim`, `basis_space_dim_via_finrank` | ⚠ Partial | Dimension arithmetic only; the Lie-quotient identification is prose |
| Thm. `thm:hilbert-representation` | Hilbert space representation | `Basic.lean : HilbertSpaceRepresentation`, `hilbert_rep_reflexive`, `hilbert_rep_symmetric`, `hilbert_rep_basis_orthogonal`, `hilbert_rep_K_bounded`, `cpn_real_dimension_from_finrank`, `state_space_dim_from_quotient`, `minimal_representation_finrank`, `standard_basis_orthonormal_rep` | ✓ Proved | Faithful embedding into ℂ^N with K = 1 − |⟨·|·⟩|² |
---

## §7 Cyclic Symmetry (sec:symmetry)

| Paper Label | Name | Lean location | Status | Notes |
|-------------|------|---------------|--------|-------|
| Lem. `lem:cyclic-rigidity` | Rigidity of cyclic dynamics: nondegenerate spectrum ⟺ single N-cycle | `CyclicRigidity.lean : cyclePoly`, `count_root_one_cyclePoly`, `nodup_iff_single_cycle`, `not_nodup_of_two_cycles`, `doubleTransposition_cycleType`, `doubleTransposition_degenerate`, `N_cycle_has_nonreal_root`, `cube_root_of_unity_in_C`, `finRotate_cycleType`; (order-N shift kinematics in `Basic.lean : cyclic_shift_injective`, `cyclic_shift_bijective`) | ✓ Proved | **Spectral core mechanized, foundations-only** `[propext, Classical.choice, Quot.sound]`: the eigenvalue 1 of the permutation lift ∏(λ^{n_ℓ}−1) has multiplicity = number of cycles, so a simple spectrum holds exactly for a single N-cycle; the N=4 double transposition (0 1)(2 3) is verified to have cycle type {2,2} and a degenerate spectrum (excluded despite its real Hadamard unbiased eigenbasis); the single N-cycle's spectrum has a non-real member for N ≥ 3. Standard permutation-lift factorization ∏(λ^{n_ℓ}−1) is the classical input. Two decisive cases grounded in genuine Mathlib permutations (`finRotate N`, `swap 0 1 * swap 2 3`). |
| Lem. `lem:minimal-rep` | Minimal representation is ℂ^N | `Basic.lean : minimal_representation_finrank`, `standard_basis_orthonormal_rep` | ✓ Proved | finrank = N; standard basis orthonormal |
| Lem. `lem:cyclic-spectrum` (formerly `thm:cyclic`) | G_dyn ≅ ℤ_N | `CyclicEigen.lean : cyclic_group_structure`, `orderOf_finRotate`, `card_zpowers_finRotate` | ✓ Proved | Via `IsCyclic (Subgroup.zpowers (finRotate N))` with cardinality N. Paper label renamed to `lem:cyclic-spectrum` (with `thm:dynamics-derived` covering the spectrum-side content). |
| Rem. `rem:ZN-to-UN` | From ℤ_N to U(N) | — | ✗ Not formalized | Prose only |

---

## §8 Gauge Symmetry from Sheaf Consistency (sec:gauge)

| Paper Label | Name | Lean location | Status | Notes |
|-------------|------|---------------|--------|-------|
| Thm. `thm:gauge` | Gauge structure from signature transport (was "Emergence of Gauge Invariance") | `Basic.lean : gauge_invariance_inner_product_sq`, `gauge_invariance_K`, `gauge_invariance_K_clean`, `gauge_invariance_bilateral` | ✓ Proved | Retitled in the 2026-07 revision. Phase-rotation invariance of |⟨·|·⟩|² and hence K |
| Berry-connection prose in `sec:gauge` + Rem. `rem:gauge-berry` (now Appendix `app:structural-conditions`, *Three N-controlled phases distinguished*) | Gauge / Berry connection | — | ✗ Not formalized | Prose only |

---

## §9 The Hilbert Space (sec:hilbert)

| Paper Label | Name | Lean location | Status | Notes |
|-------------|------|---------------|--------|-------|
| Thm. `thm:n2-static` | N = 2 is static / no continuous dynamics | `CyclicEigen.lean : N2_eigenvalues_real`; `SwapMatrix.lean : S_sq_eq_one`, `S_eigenvalues_pm1`, `commuting_with_S_form`, `real_orthogonal_commuting_discrete` | ✓ Proved | Both eigenvalue form (±1 real) and swap-matrix rigidity (discrete {I, −I, S, −S}) |
| (deleted: `thm:complex`) | Emergence of complex numbers — content subsumed in `lem:sheaf-complex` | `CyclicEigen.lean : complex_forced`; `Frobenius.lean : C_is_unique_field`, `frobenius_forces_complex` | ⚠ Partial | Paper label removed; the non-real-eigenvalue argument is now packaged inside `lem:sheaf-complex` (and `Frobenius.frobenius_forces_complex` for the field-uniqueness side). The Lean theorems remain as before; only the paper label changed. |
| Thm. `thm:inner-product-existence` | Inner product from K | `InnerProduct.lean : kernel_from_inner_product`, `kernel_reflexive`, `kernel_symmetric`, `K_eq_one_iff_orthogonal`, `inner_product_from_kernel_basis`, `standard_basis_orthonormal`, `kernel_standard_basis`, `inner_product_sesquilinear` | ✓ Proved | Standard-basis construction and uniqueness-on-basis (sesquilinear extension) |
| Rem. (no current paper label) | Fourier inner product / discrete Fourier orthogonality | `Fourier.lean : roots_of_unity_orthogonality`, `fourier_orthonormal` | ✓ Proved | The v1 `rem:fourier-inner-product` remark was removed in the 2026-07 revision; the Lean orthogonality result is retained as supporting content for `thm:inner-product-existence` / `thm:kernel-inner`. |
| Thm. `thm:kernel-inner` | K = 1 − \|⟨·\|·⟩\|² (kernel from inner product) | `InnerProduct.lean : kernel_from_inner_product`, `kernel_reflexive`, `K_eq_one_iff_orthogonal`; `FubiniStudy.lean : K_equals_projection_distance` | ✓ Proved | Both the analytic formula and its projection-distance interpretation |

---

## §10 Geometry and the Born Rule (sec:geometry)

| Paper Label | Name | Lean location | Status | Notes |
|-------------|------|---------------|--------|-------|
| Thm. `thm:fs-from-K` | Fubini–Study from K | `FubiniStudy.lean : fubini_study_form`, `fubini_study_projection`, `K_equals_projection_distance`, `projection_orthogonal`, `K_bounds_from_projection`, `K_taylor_is_gFS_axiom` | ✓ Proved | Projection formula and Taylor expansion K = g_FS + O(‖dψ‖³) (name contains "_axiom" for historical reasons; it is fully proved with explicit remainder) |
| Cor. `cor:fisher-interpretation` | Fisher interpretation g_FS = F_Q/4 | `FubiniStudy.lean : gFS_quarter_FQ` | ✓ Proved | |
| Thm. `thm:fs-unique` | Uniqueness of Fubini–Study | `FubiniStudy.lean : fubini_study_unique`; `ClassicalImports.lean : kobayashi_nomizu_uniqueness` (axiom) | ⚠ Partial | Conclusion proved from imported Kobayashi–Nomizu axiom |
| Assum. `asm:continuity-from-dynamics` | Continuity of the Probability Rule (regularity assumption) | `MetricBridge.lean : continuity_of_probability`, `K_from_overlap_sq_continuous`, `born_probability_continuous`, `born_probability_from_K_continuous` | ⚠ Assumption in paper | **In the 2026-07 revision this is a stated `assumption` in the paper ("Continuity of the Probability Rule"), not a proved Lemma. The paper does not derive it; it is assumed as standard Gleason-tradition regularity.** The Lean decls mechanize only the downstream composition-of-continuous-maps fact (continuity of the output given continuity of the inputs); they do not discharge the paper's regularity premise. |
| (deleted: `thm:metric-bridge`; content absorbed into `thm:born-kernel`, `lem:metric-compatibility`) | ODE-uniqueness step within Born rule derivation | `MetricBridge.lean : MetricCompatible`, `metric_bridge`, `metric_bridge_constant`, `id_is_metric_compatible`, `born_rule_unique_metric_compatible`, `fisher_rao_proportionality_constant`, `metric_compatibility_forces_alpha_2`, `FisherRaoWeight`, `fisher_rao_weight_alpha_2` | ✓ Proved | Uses ODE uniqueness from `BornRule.lean` and FS uniqueness from `FubiniStudy.lean`. Now corresponds to `thm:born-kernel` Part 1 / `lem:metric-compatibility` (Step 1b ODE) in the paper. |
| Lem. `lem:metric-compatibility` | Metric compatibility ODE | `BornRule.lean : MetricCompatibilityODE`, `antiderivative_form`, `c_eq_one_of_antideriv`, `f_eq_id_on_unit_interval`, `ode_uniqueness_born_rule` | ✓ Proved | Binary form of the ODE (see next row); uniqueness proved from scratch (no axiom) |
| Rem. `rem:ode-binary-form` | ODE binary form vs per-component | `BornRule.lean` header | ⚠ Partial | Lean uses the binary Bernoulli form `[f']²/[f(1−f)] = c²/[x(1−x)]`; paper Lem. `lem:metric-compatibility` presents the per-component form `[f']²/f = c/x`. The two are equivalent on [0,1]; only the binary form is mechanized |
| Def. `def:measure-setup` | Probability-measure setup | `BornRule.lean : AdmissibleProbAssignment` | ✓ Proved | |
| Thm. `thm:born-kernel` | Born rule from K + metric compatibility | `BornRule.lean : born_f`, `born_f_zero`, `born_f_one`, `born_f_nonneg`, `born_f_le_one`, `born_f_monotone`, `born_f_differentiable`, `born_f_preserves_sum`, `born_admissible`, `id_satisfies_ode`, `id_has_deriv`, `born_rule_unique`, `power_law_forces_alpha_2`, `born_rule_ode_integration`, `boundary_forces_c_eq_1`, `born_rule_normalization`, `born_rule_prob_dist`, `born_rule_normalization_inner` | ✓ Proved | f = id uniqueness is `ode_uniqueness_born_rule`; normalization from ‖ψ‖ = 1 |
| Cor. `thm:born-kernel` (N = 2 case; was `cor:born-n2`) | Born rule at N = 2 (beyond Gleason) | `BornRuleN2.lean : QubitNormalization`, `qubit_norm_at_p_1`, `half_power_constraint`, `rpow_half_eq_half_forces_p_1`, `born_rule_n2`, `born_rule_n2_is_identity`, `qubit_normalization`, `qubit_born_from_kernel`, `metric_bridge_n2`, `born_rule_n2_vs_gleason` | ✓ Proved | The separate `cor:born-n2` label was removed in the 2026-07 revision; the N = 2 Born-rule content is now the N = 2 case of `thm:born-kernel` (discussed in `sec:n2-discussion`). Power-law + normalization at x = 1/2 route. |
| Rem. (no current paper label) | Independent routes to α = 2; p_k = 1 − K(ψ, a_k) agrees with the Born rule | `BornRule.lean : k_affinities_give_born_probabilities`, `k_affinities_born_normalized`, `k_affinity_born_valid`, `KAffinityNormalized`, `k_affinity_nonneg`, `k_affinity_le_one`, `k_affinity_prob_dist` | ✓ Proved | The v1/v2 `rem:born-robustness` remark (and its consolidated duplicate-label aliases) was removed from the paper in the 2026-07 revision; the K-affinity ↔ Born equivalence is retained here as supporting content for `thm:born-kernel` and `prop:measurement-born`. |
| Cor. `cor:entropic` | Entropic uncertainty | `Scaling.lean : log_reciprocal`, `log_sqrt_eq_half_log`, `maassen_uffink_mub_bound`, `maassen_uffink_full_chain`, `entropic_uncertainty_nontrivial`, `entropy_range_nontrivial` | ✓ Proved | MUB chain −2 log(1/√N) = log N |

---

## §11 Dynamics, Energy, and the Origin of ℏ (sec:evolution)

| Paper Label | Name | Lean location | Status | Notes |
|-------------|------|---------------|--------|-------|
| Cor. `cor:noether` | Energy conservation (Noether) | `Schrodinger.lean : energy_conservation_from_commutant`, `commutant_conjugation_invariant`, `energy_expectation_constant`, `commutator`, `commutator_antisymm`, `commutator_add_left`, `commutator_mul_right`, `unitary_group_inverse`, `unitary_group_inverse_right`, `unitary_group_assoc`, `unitary_from_adjoint_inverse` | ✓ Proved | ⟨ψ(t)\|H\|ψ(t)⟩ = ⟨ψ\|H\|ψ⟩ from [H, U] = 0 |
| Cyclic-spacing caution (prose in `sec:phase-structure`; label `rem:cyclic-spacing-not-quantum` retired 2026-09; was `thm:phase-granularity` / `cor:phase-granularity`) | Cyclic spacing is one operator's spectrum, not a phase quantum | `Scaling.lean : phase_granularity`, `phase_granularity_monotone`, `consecutive_phase_separation` | ⚠ Partial | The v1 phase-granularity theorem and corollary were removed in the 2026-07 revision. The paper now reframes the δφ = 2π/N spacing as the spectrum of the cyclic generator (`lem:cyclic-spectrum`), explicitly *not* a fundamental phase quantum. The `Scaling.lean` spacing/monotonicity arithmetic is retained. |
| Thm. `thm:quantum-sampling` = `thm:continuous-sampled` (**merged, dual-labelled**) | Sampling, Band Limit, and the Resolution Floor (incorporates Zeno floor, UV cutoff, Heisenberg uncertainty; absorbs the former "Continuous vs sampled indistinguishability" theorem) | `Scaling.lean : quantum_sampling_mub_tomography`, `zeno_floor_positive`, `zeno_floor_upper_bound`, `zeno_floor_monotone_decreasing`, `zeno_floor_qubit`, `zeno_product_in_unit_interval`, `energy_gap_lower_bound`, `entropic_uncertainty_nontrivial`, `maassen_uffink_mub_bound`; `Basic.lean : nyquist_sample_count` | ⚠ Partial | Parameter counting via `finrank`; Peter–Weyl argument itself is prose. **In the current revision the two sampling theorems were merged into this single statement, which carries both labels `thm:quantum-sampling` and `thm:continuous-sampled`** (see the §5 pointer row). Subsumes the former `thm:zeno-floor` (1/N² floor properties), `cor:uv-cutoff` (lower bound on gap; ℏ/δt identification is prose), and a Heisenberg-uncertainty corollary (entropic form formalized; product form ΔE·Δt ≥ 2πℏ/N is prose). |
| (deleted: `thm:zeno-floor`; content absorbed into `thm:quantum-sampling`) | Informational Zeno floor | `Scaling.lean : zeno_floor_positive`, `zeno_floor_upper_bound`, `zeno_floor_monotone_decreasing`, `zeno_floor_qubit`, `zeno_product_in_unit_interval` | ✓ Proved | Now packaged inside `thm:quantum-sampling`; Lean theorems unchanged. |
| (deleted: `cor:uv-cutoff`; content absorbed into `thm:quantum-sampling`) | Natural UV cutoff | `Scaling.lean : energy_gap_lower_bound` | ⚠ Partial | Now packaged inside `thm:quantum-sampling`; Lean theorem unchanged. |
| Thm. `thm:schrodinger` | Schrödinger equation | `Schrodinger.lean : unitary_preserves_K`, `K_pres_implies_transition_prob_pres`, `norm_sq_eq_implies_norm_eq`, `K_pres_implies_norm_inner_pres`, `schrodinger_derivation_chain`, `inner_pres_iff_K_pres`, **`HasHermitianGenerator` (explicit hypothesis), `skewHermitian_neg_I_smul`, `hasHermitianGenerator_exp`, `derivation_chain_of_hermitian_generator`**, `stone_generator_unique_of_local_agreement`; uses `ClassicalImports.wigner_continuity_unitary`, `ClassicalImports.picard_lindelof_unique` | ⚠ Partial | Steps 1–2 (K-preservation ⟹ transition-probability preservation ⟹ unitarity, via Wigner + continuity) fully proved. **Step 3 (existence of a Hermitian generator) is not a Lean theorem and is not an axiom:** it is carried by the paper's elementary finite-dimensional prose argument (matrix Lie theory: a continuous one-parameter subgroup of U(N) is smooth, `H := i U'(0)` is Hermitian), and appears in Lean only as the explicit hypothesis `HasHermitianGenerator U` (`U t = exp(t • (−i H))` with `Hᴴ = H`), consumed by `derivation_chain_of_hermitian_generator`, which derives unitarity, the group law and `U 0 = 1` from it. The former **trivially witnessed placeholders `stone_gives_hermitian_generator` and `full_derivation_chain` (witness `A = 0`, `U`-hypotheses unused) have been deleted**, together with `ClassicalImports.stone_generator` and `montgomery_zippin_generator`, which nothing else consumed; the "cleaner future state" of the paper's Appendix `app:formal-verification` is thus the state of the repository. Nothing vacuous remains, and the deletion added no axiom. The matrix-exponential **reverse** direction is fully proved (`ClassicalImports : exp_skewHermitian_unitary`, `skewHermitian_generator_gives_hermitian`, `exp_skewHermitian_group`, `exp_skewHermitian_id`, and `Schrodinger.hasHermitianGenerator_exp` at the interface); generator **uniqueness** is proved modulo `picard_lindelof_unique` (`stone_generator_unique_of_local_agreement`). Remaining gap: a Mathlib interface for extracting `U'(0)` (matrix logarithm / functional calculus for `Matrix.exp`), not a mathematical one. |

---

## §12 The Capacity Halting Principle (sec:measurement)

| Paper Label | Name | Lean location | Status | Notes |
|-------------|------|---------------|--------|-------|
| Def. `def:info-capacity` | Information-theoretic capacity | `CapacityHalting.lean : info_capacity`, `info_capacity_ge_one`, `info_capacity_mono`, `capacity_is_log_bits`, `total_info_M_measurements`, `measurement_configurations`, `single_measurement_bound` | ✓ Proved | C = log₂ N |
| Lem. `lem:capacity-bound` | Capacity as physical bound | `CapacityHalting.lean : single_measurement_bound`, `capacity_is_log_bits` | ✓ Proved | |
| Def. `def:hv-assignment` | Hidden-variable assignment | `CapacityHalting.lean : HiddenVariableAssignment`, `hva_storage_exceeds_capacity` | ✓ Proved | |
| Thm. `thm:capacity-halting` | Capacity halting principle | `CapacityHalting.lean : capacity_deficit`, `capacity_deficit_bits`, `assignment_count_exceeds_capacity`, `capacity_overflow_strict`, `storage_overflow_ratio`, `storage_overflow_multiplicative`, `assignment_exceeds_capacity_squared` | ⚠ Partial | Arithmetic inequalities `N^1 < N^(M−1)` and `log₂ N < (M−1) log₂ N` fully proved. The physical content (MUB geometry, Kochen–Specker, Chaitin incompressibility) is paper prose only; see file header and paper App. `app:formal-verification` |
| Lem. `lem:ks-bits` | Kochen–Specker bit count | `CapacityHalting.lean : ks_bit_count_exceeds_capacity` | ⚠ Partial | log₂ N < N² arithmetic only (qualitatively-correct loose form). The paper's sharper `(M-1) log₂ N` bit-count, scaling to Θ(N log₂ N) for prime-power N at M = N+1, is argued via MUB structure in `lem:incompressibility`(a) and is paper prose for the full KS projector geometry |
| Lem. `lem:incompressibility` | Incompressibility (Chaitin) | `CapacityHalting.lean : incompressibility_combinatorial`, `mub_overlap_uniform` | ⚠ Partial | (a) combinatorial lower bound proved; (b) Kolmogorov-complexity refinement is paper prose |
| Rem. (MUB support for `lem:ks-bits`; was `rem:mub-existence`) | Existence / counting of MUBs | `Scaling.lean : mub_full_tomography_params`, `mub_complete_characterization`, `mub_tomography_sufficient`, `mub_overlap_completeness` | ⚠ Partial | The v1 `rem:mub-existence` remarks were removed in the 2026-07 revision; the MUB counting identities are retained as support for `lem:ks-bits` (Complementarity Bit-Count). Existence of N+1 MUBs (prime-power case) remains paper prose. |
| Lem. `lem:affinity-normalization` | K-affinity normalization | `BornRule.lean : KAffinityNormalized`, `k_affinity_nonneg`, `k_affinity_le_one`, `k_affinity_prob_dist` | ✓ Proved | Σ(1 − K) = 1 as structural predicate |
| Lem. `prop:measurement-born` (Kolmogorov-axioms facet; was `thm:prob-from-K`) | Probabilities from K (Kolmogorov axioms from K-affinities) | `BornRule.lean : k_affinities_give_born_probabilities`, `k_affinities_born_normalized`, `k_affinity_born_valid`, `k_affinity_monotone`, `k_affinity_strict_monotone`, `k_affinity_max_at_zero`, `k_affinity_min_at_one`, `kolmogorov_from_K_structure` | ✓ Proved | The `thm:prob-from-K` label was removed in the 2026-07 revision; this content is the Kolmogorov-axioms facet of `prop:measurement-born` (K-Affinities Give Born Probabilities). |
| Cor. `thm:contextuality` | Kochen--Specker contextuality (now a corollary) | `CapacityHalting.lean : contextuality_storage_exceeds_capacity`, `contextuality_deficit_factor`, `contextuality_minimal_case`, `contextuality_full` | ⚠ Partial | Demoted from theorem to corollary in paper v2; arithmetic (bit-count / overflow) part only in Lean. Absorbs the former `rem:contextuality-overflow` (contextuality-as-overflow) Lean decls. |
| Rem. `rem:entropy-floor` | Operational entropy floor | `Scaling.lean : entropy_range_nontrivial`, `entropic_uncertainty_nontrivial` | ⚠ Partial | log N > 0 for N ≥ 2; full entropy-floor geometry is prose |
| Rem. `rem:entropy-floor` | Conservation of ignorance | — | ✗ Not formalized | Prose only |
| Rem. `rem:continuum-limit` | Continuum limit → standard QM | — | ✗ Not formalized | Prose only |
| Rem. `rem:continuum-limit` | Entrenchment of finite N | — | ✗ Not formalized | Prose only |
| Def. `def:measurement-interaction` | Measurement as correlation formation | — | ✗ Not formalized | Prose definition |
| Prop. `prop:measurement-born` | Measurement-Born correspondence | `BornRule.lean : k_affinities_give_born_probabilities`, `k_affinities_born_normalized` | ⚠ Partial | K-affinity-to-Born bridge proved; measurement-interaction framing is paper prose |
| Rem. `rem:collapse` | Collapse as correlation formation | — | ✗ Not formalized | Prose only |

---

## §13 Composite Systems and No-Cloning (sec:composite)

| Paper Label | Name | Lean location | Status | Notes |
|-------------|------|---------------|--------|-------|
| Def. `def:independent` | Spatially separated / independent subsystems | `Composite.lean : SpatialSeparation` | ✓ Proved | |
| Rem. `rem:independence-characterization` | Independence and its consequences (was Thm. "Characterization of Independence") | `Composite.lean : no_signaling_A`, `no_signaling_B`, `no_signaling_general`, `independent_outcomes_product`, `characterization_of_independence`, `local_actions_commute`, `local_symmetries_commute_kernel` | ✓ Proved | **Now prose immediately after Definition `def:independent` (2026-09 flow pass); the standalone label is retired.** No-signaling + factorization + commutativity. |
| Lem. `lem:commutativity` | Commutativity of local actions | `Composite.lean : local_actions_commute`, `local_symmetries_commute_kernel` | ✓ Proved | |
| Thm. `thm:capacity-mult` | Capacity multiplicativity | `Composite.lean : dimension_multiplicativity`, `product_basis_self_identical`, `product_basis_mutual_distinguishability`, `product_basis_distinguishable`, `composite_dimension_qubit`, `composite_continuous_threshold` | ✓ Proved | N_AB = N_A · N_B via product basis |
| Def. `def:local-tomography` | Local tomography | `Composite.lean : LocalTomography`, `complex_local_tomography` | ✓ Proved | |
| Thm. `thm:tensor` | Tensor-product structure | `Composite.lean : compositeIndexEquiv`, `composite_index_card`, `composite_index_val_qubit`, `productState`, `productState_apply`, `IsSeparable`, `IsEntangled`, `bellState`, `separable_cross_ratio`, `bell_state_entangled`, `entangled_states_exist`, `product_state_norm_sq_factorizes` | ✓ Proved | Fin NA × Fin NB ≃ Fin(NA·NB), product states, Bell-state entanglement witness |
| Cor. `cor:local-tomography-derived` (was `rem:local-tomography-derived`) | Derived Local Tomography | `Composite.lean : local_tomography_dimension`, `power_function_multiplicative`, `local_tomography_complex_unique`, `real_fails_local_tomography`, `real_local_tomography_fails`, `quaternionic_local_tomography_fails`, `real_dim_not_multiplicative`, `quaternionic_dim_not_multiplicative`, `local_tomography_parameter_decomposition`, `correlation_parameters_positive`, `qubit_qubit_decomposition`, `qutrit_qutrit_decomposition`, `entanglement_parameter_dominance`, `entanglement_gap` | ✓ Proved | ℂ-case multiplicativity + ℝ/ℍ failure + parameter decomposition |
| Thm. `thm:kernel-composition` | Kernel composition rule from associativity | `Composite.lean : kernel_compose`, `compose_zero_zero`, `compose_one_left`, `compose_one_right`, `compose_zero_left`, `compose_zero_right`, `compose_symm`, `compose_assoc`, `kernel_compose_unique_characterization`, `kernel_compose_survival`, `kernel_compose_unique_from_survival`, `survivalTransform`, `survivalTransform_zero_left`, `survivalTransform_zero_right`, `survivalTransform_one_left`, `survivalTransform_one_right`, `survivalTransform_comm`, `survivalTransform_assoc`, `survival_multiplicativity_from_assoc`, `kernel_compose_is_unique`, `kernel_product_states`, `kernel_compose_eq_zero_iff`, **`TransportConsistencyBinary`, `strict_monotone_from_transport`, `kernel_compose_transport_consistency`, `kernel_compose_strict_mono_left`, `kernel_compose_strict_mono_right`, `strict_mono_of_mono_and_injective`, `kernel_compose_strict_mono_from_transport` (v3)** | ✓ Proved | **Axiom-free.** The uniqueness `kernel_compose_is_unique` is pinned directly by the independence / factor-homogeneity clause (vi) via `mul_of_factor_homogeneous`; the former `aczel_continuous_associative_is_mul` axiom (Aczél / strict t-norm representation) has been **deleted**, so `Composite.lean` imports no axiom. The paper's *prose* proof still invokes the strict t-norm representation theorem as a classical result, which is why the paper lists it among prose-level classical inputs rather than among the four Lean axioms. v3 strict-monotonicity argument (paper line 1668) added: `kernel_compose_transport_consistency` proves `kernel_compose` injective in each argument when the other is in `(0,1)`, and `kernel_compose_strict_mono_left/_right` establish strict monotonicity directly; `strict_mono_of_mono_and_injective` packages the Transport-Consistency-based reasoning chain (TConsistency + monotonicity ⟹ strict monotonicity), discharging the v3 paper's Transport-Consistency argument structurally. All v3 additions sorry-free. |
| Thm. `thm:capacity-dilution-composite` | Qubit Recovery from Composite Embedding | `QubitRecovery.lean : qubit_recovery`, `partialTraceE`, `partialTraceE_kron`, `partialTraceE_kron_one`, `partialTraceE_pure_product`, `productOuter`, `productOuter_kron`, `local_Born_rule`, `productForm_summands_commute`, `productFormHamiltonian`, `kron_unitary_group`, `kron_unitary_unitary`, `coefficient_field_inheritance`, `partialTraceE_mixed_purification`, `qubit_recovery_capacity_threshold`; `Composite.lean : capacity_dilution_continuous_dynamics`, `capacity_dilution_sufficient`, `composite_continuous_threshold`, `compositeIndexEquiv`, `productState`, `kernel_product_states`; `Scaling.lean : capacity_dilution_ratio`, `effective_phase_granularity`, `composite_phase_finer`, `dilution_ratio_le_one` | ✓ Proved | v3 paper four-clause Qubit Recovery theorem mechanized in `QubitRecovery.lean`. The top-level `qubit_recovery` bundle is sorry-free, depending only on `[propext, Classical.choice, Quot.sound]`: clause (a) pure-case via `partialTraceE_pure_product`, (b) coefficient-field inheritance via `coefficient_field_inheritance`, (c) local Born rule via `local_Born_rule`, (d) product-form summand commutation via `productForm_summands_commute`. Mixed-state purification (`partialTraceE_mixed_purification`) is **now also sorry-free**: every positive-semidefinite qubit state is realized as the environment-reduced state of a pure composite, built from the matrix square root `CFC.sqrt`. This was the last residual `sorry` in `QubitRecovery.lean`, which is now entirely sorry-free. The geometric identification U(2)/U(1) ≅ SU(2)/Z_2 ≅ SO(3) on the Bloch ball is standard projective-geometry prose not separately mechanized. |
| Cor. `cor:no-cloning`, `cor:tsirelson` (was `rem:standard-consequences`) | No-Cloning and Tsirelson bound (standard consequences: monogamy, no-cloning) | — | ✗ Not formalized | Now explicit corollaries in the paper (2026-07 revision): `cor:no-cloning` and `cor:tsirelson`, previously folded into `rem:standard-consequences` prose. Not separately formalized. The former `cor:scaling-law` row was removed as redundant — its `Scaling.lean` capacity-dilution decls (`capacity_dilution_ratio`, `effective_phase_granularity`, `composite_phase_finer`, `dilution_ratio_le_one`) are listed in the `thm:capacity-dilution-composite` row above. |

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
| Thm. `thm:K-smooth` | Regularity of K (was "K is C^∞") | — | ✗ Not formalized | Retitled and restated in the 2026-07 revision: the statement is now about the diagonal Hessian of K, with global C^∞ smoothness obtained a posteriori. Lie-smoothness argument remains paper prose. |
| Thm. `thm:convexity-forced` | Full state space is convex hull | — | ✗ Not formalized | Density-matrix extension argued in paper prose |

---

## Appendix C: Formal Verification Scope (app:formal-verification)

The paper's own scope statement lists machine-checked results and imported axioms. **Four** classical results are declared as Lean `axiom`s — Frobenius, Wigner, Kobayashi–Nomizu, Picard–Lindelöf — and they are the only declared axioms in the `QuantumRelational` formalization (table below). Two further items the appendix discusses are *not* Lean axioms:

- **Stone's theorem.** Only the reverse direction is mechanized; the uniqueness half of the forward direction is proved modulo Picard–Lindelöf; the **existence** half is a prose-level input (elementary matrix Lie theory in finite dimension) exposed in Lean as the explicit hypothesis `Schrodinger.HasHermitianGenerator`. The two former trivially witnessed placeholders (`stone_gives_hermitian_generator`, `full_derivation_chain`) and the two `ClassicalImports` declarations that backed them (`stone_generator`, `montgomery_zippin_generator`) have been deleted, so the library contains no vacuously witnessed statement and the `sorry`-free claim needs no scoping caveat.
- **The strict t-norm representation theorem** (Aczél / Klement–Mesiar–Pap / Schweizer–Sklar), used in the paper's prose proof of `thm:kernel-composition`, is no longer a Lean axiom: `Composite.lean` is axiom-free.

Prose-level inputs recorded in the paper's input ledger (Table `tab:input-ledger`) that deliberately have **no** mechanized counterpart: the **spectral form of the dynamical closure clause (C4)** of Axiom `ax:relational` (whose content alone is machine-checked in `CyclicRigidity.lean`), the **Stone existence direction** and the **Mathlib `U'(0)` interface gap** (the two Stone interface items above), regularity condition (R) (`cond:regularity`, Rem. `rem:finite-dim-status`), and the prose-level classical results (Cartan–Wang, Montgomery–Zippin, Peter–Weyl, Arzelà–Ascoli).

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

## Classical Imports (the four `axiom` declarations, all in `ClassicalImports.lean`)

Exactly four classical theorems are imported as Lean `axiom`s, matching the paper's Appendix `app:formal-verification`; `Composite.lean` is axiom-free. `IsFinDimAssocDivAlgDim` is a `def` (a `Prop`-valued predicate used as a hypothesis of `frobenius_classification`) and must not be counted as a fifth axiom.

| Axiom | Declared in | Used for (paper label) | Reference |
|-------|-------------|------------------------|-----------|
| `wigner_continuity_unitary` | `ClassicalImports.lean` | Thm. `thm:schrodinger` — unitarity of time evolution (excluding antiunitary branch via continuity) | Wigner (1931) \cite{wigner1931gruppentheorie}; Bargmann (1964) \cite{bargmann1964note} |
| `kobayashi_nomizu_uniqueness` | `ClassicalImports.lean` | Thm. `thm:fs-unique` — uniqueness of U(N)-invariant metric on ℂP^(N-1) | Kobayashi–Nomizu (1969) \cite{kobayashi1969foundations} |
| `picard_lindelof_unique` | `ClassicalImports.lean` | Generator-uniqueness step, consumed by `Schrodinger.stone_generator_unique_of_local_agreement` (Thm. `thm:schrodinger` related) | Standard ODE theory |
| *(not an axiom)* `IsFinDimAssocDivAlgDim` | `ClassicalImports.lean` | `def`, not `axiom`: opaque predicate for "d is the real dimension of a finite-dimensional associative division algebra over ℝ", used as a hypothesis of `frobenius_classification` | Frobenius (1878) |
| `frobenius_classification` | `ClassicalImports.lean` | Thm. `thm:frobenius` — d ∈ {1, 2, 4} for real associative division algebras | Frobenius (1878) |
| *(deleted)* `aczel_continuous_associative_is_mul` | formerly `Composite.lean` | Thm. `thm:kernel-composition` | **No longer an axiom.** Deleted when the uniqueness proof was rerouted through the independence / factor-homogeneity clause (`mul_of_factor_homogeneous`); `Composite.lean` is axiom-free. The strict t-norm representation theorem (Aczél 1966; Klement–Mesiar–Pap; Schweizer–Sklar) survives only in the paper's prose proof. |

**Stone's theorem, current state (no placeholders):** `ClassicalImports.stone_generator` and `montgomery_zippin_generator` — theorems whose witness was `A = 0`, with the `U` hypotheses unused, so that they asserted nothing about the given one-parameter group — have been **deleted**, together with the two Schrödinger-side statements that were their only consumers (`Schrodinger.stone_gives_hermitian_generator`, `Schrodinger.full_derivation_chain`). In their place:

- the generator-existence conclusion is the explicit hypothesis `Schrodinger.HasHermitianGenerator U` := `∃ H, Hᴴ = H ∧ ∀ t, U t = exp (t • (−i • H))`;
- `Schrodinger.derivation_chain_of_hermitian_generator` derives, from that hypothesis alone, that `U t = e^{−itH}` with `H` Hermitian, that each `U t` is unitary, that `U` is a one-parameter group, and that `U 0 = 1`;
- `Schrodinger.hasHermitianGenerator_exp` proves the reverse direction at the interface (a skew-Hermitian `A` yields the hypothesis with `H = iA`), and `skewHermitian_neg_I_smul` is the Lie-algebra step `Hᴴ = H ⟹ (−iH)ᴴ = −(−iH)`;
- the reverse-direction helpers (`exp_skewHermitian_unitary`, `skewHermitian_generator_gives_hermitian`, `exp_skewHermitian_group`, `exp_skewHermitian_id`) are unchanged and fully proved from Mathlib's matrix exponential;
- generator uniqueness remains `Schrodinger.stone_generator_unique_of_local_agreement`, proved modulo `picard_lindelof_unique`.

The mathematical content of the existence direction is the paper's elementary finite-dimensional argument (matrix Lie theory: a continuous one-parameter subgroup of `U(N)` is smooth and `H = i U'(0)` is Hermitian); the residual gap is a Mathlib interface for extracting `U'(0)`, not a mathematical step. This affects the *quantified Lean content* of `thm:schrodinger`, `thm:time-emergence` and Appendix B's `thm:smoothness-forced` (Montgomery–Zippin is likewise a prose-level classical input), and it adds no axiom: the deletion left the `AxiomCheck.lean` output unchanged.

`schur_lemma` is also stated in `ClassicalImports.lean` but proved from Mathlib's `Module.End.exists_eigenvalue` (no axiom).


## Revision 2026-07-01: corrected SRC packaging (SRCv2)

The paper revision `2026_07_01_QuantumMechanicsFromFiniteGradedEquality.tex`
restates the axioms (Axiom 1 with scale-freeness clause; SRC as internal
clauses (C1)-(C3)) and retires the v1 extension-based SRC and blanket
Structural Leibniz. New machine-checked material (all sorry-free; axioms
`[propext, Classical.choice, Quot.sound]` only):

| Paper statement | Lean declaration |
|---|---|
| Axiom `ax:relational`(C1), binary consumed form | `SRCv2.DefinabilityBinary` |
| Axiom `ax:relational`(C2), limit completeness | `SRCv2.LimitCompleteness` |
| Axiom `ax:relational`(C3), context homogeneity | `SRCv2.ContextHomogeneity` (contexts: `SRCv2.IsContext`) |
| Thm `thm:src-master`(S1) via (C1) diagonal argument | `SRCv2.S1_identity_from_C1` |
| Cor `cor:homogeneity`(i) transitivity | `SRCv2.transitivity_from_C3` |
| Cor `cor:homogeneity`(ii) two-point homogeneity | `SRCv2.two_point_homogeneity_from_C3` |
| Cor `cor:homogeneity`(iii) pair-completeness | `SRCv2.pair_completeness_from_C3` |
| Cor `cor:homogeneity`(iv) permutation invariance | `SRCv2.permutation_invariance_from_C3` |
| Thm `thm:src-master` **Basis Isotropy** (aligned-anchor induction) | `SRCv2.basis_isotropy_from_C3` |
| Ax. `ax:relational`(C4) — spectral content (no frozen relative phase ⟺ simple spectrum of the permutation lift ⟺ single N-cycle) | `CyclicRigidity.count_root_one_cyclePoly`, `.nodup_iff_single_cycle`, `.not_nodup_of_two_cycles`, `.doubleTransposition_cycleType`, `.doubleTransposition_degenerate`, `.N_cycle_has_nonreal_root` |
| Thm `thm:covariance-nogo` | `CovarianceNoGo.covariance_nogo`, `.no_covariant_deterministic_assignment` |
| Thm `thm:binary-insufficiency`, K-symmetry premise | `BinaryInsufficiency.pairwise_overlaps_match` |
| Thm `thm:binary-insufficiency`, Bargmann products 2i vs 2 | `BinaryInsufficiency.bargmann_x`, `.bargmann_y` |
| Thm `thm:binary-insufficiency`, no unitary/antiunitary extension | `BinaryInsufficiency.no_unitary_extension`, `.no_antiunitary_extension`, `.no_extension` |

v1-retired artifacts kept for the record: the two-form SRC structure and
equivalence bridges (`SRC.src_forms_equivalent` and friends) and the
amalgam construction supporting blanket (S4).

**Prose-level inputs of this revision with no mechanized counterpart** (all recorded in the paper's input ledger, Table `tab:input-ledger`):

| Paper item | Status in Lean |
|---|---|
| Ax. `ax:relational`(C4) (dynamical closure) and Rem. `rem:self-description-status` (in `sec:field-selection`) | Clause's spectral form not formalized; only its spectral content (`CyclicRigidity.lean`, table above) is machine-checked |
| Stone existence direction (matrix Lie theory: `H = i U'(0)`) | Not proved, not axiomatized; exposed as the explicit hypothesis `Schrodinger.HasHermitianGenerator` |
| Mathlib interface for extracting `U'(0)` from a one-parameter matrix group | Missing (the residual gap; the mathematics is elementary and prose-level) |
| Regularity condition (R), `cond:regularity` / Rem. `rem:finite-dim-status` | Prose only |
| Strict t-norm representation theorem (paper's prose proof of `thm:kernel-composition`) | Prose only; no longer a Lean axiom |

### Model Existence (`ModelExistence.lean`, added 2026-07-02)

Machine-checked pieces of paper Thm `thm:model-existence` (all sorry-free):

| Paper statement | Lean declaration |
|---|---|
| Kernel laws for (ℙ ℂ (ℂ^N), Fubini-Study K), incl. identity of indiscernibles via Cauchy-Schwarz equality case | `ModelExistence.model` |
| Axiom 1(i), existence half: standard-basis rays are a basis family | `ModelExistence.basisRay_isBasisFamily` |
| Axiom 1(ii): K-image is all of [0,1] (surjectivity, stronger than density) | `ModelExistence.K_image_full` |
| Clause (C2) for the model, full net/filter form, via ultrafilter compactness of the unit sphere | `ModelExistence.limitCompleteness_model` |
| Clause (C3), full-basis anchors: the explicit antiunitary D∘conj (θ_k = y_k/conj(x_k)) | `ModelExistence.context_homogeneity_full_basis` |
| (S3) in profile form (rescaling wrapper) | `ModelExistence.context_homogeneity_S3` |

Remaining gaps in the Model Existence mechanization (documented in the
file header): (C3) for partial contexts (the cycle-flip gauge
construction; needs a Gram-congruence toolkit), clause (C1) for the
model, and the maximality bound in Axiom 1(i) (every maximal family has
exactly N elements; only the existence half is formalized).

## Paper 2 revision 2026-07-05: emergent spatial dimension (new modules)

Paper: `modest_number_space/2026_07_05_spatial_geometry_emergent_dimension.tex`.

| Paper statement | Lean declaration | Status |
|---|---|---|
| Thm `thm:integer-dimension` (integer dimension via Bass–Guivarc'h, no flatness assumed) | `Paper2.GrowthDegree.GrowthRanks.degree` + `classification_low` | sorry-free (arithmetic core; Trofimov/Gromov/Bass–Guivarc'h encoded as `supp`/`gen` fields) |
| Thm `thm:translation-group`(ii) (Flatness Theorem: D = 3 ⟹ virtually ℤ³) | `Paper2.GrowthDegree.GrowthRanks.flatness_at_three` | sorry-free |
| Thm `thm:translation-group`(iii) (D = 4 dichotomy: ℤ⁴ or Heisenberg) | `Paper2.GrowthDegree.GrowthRanks.dichotomy_at_four` | sorry-free |
| Heisenberg profile: D = 4, excluded with ℤ⁴ | `Paper2.GrowthDegree.degree_heisenberg`, `heisenberg_excluded`, `Paper2.DimensionSelection.heisenberg_at_four` | sorry-free |
| Thm `thm:recurrence` (return-mass threshold, Varopoulos core) | `Paper2.DimensionSelection.heatKernel_summable_iff`, `recurrent_of_le_two`, `transient_of_three_le` | sorry-free (summability half; heat-kernel bound p_t ≍ t^{-D/2} is cited mathematics) |
| Thm `thm:bound-states`(iv) corrected (fall to center at D ≥ 5) | `Paper2.DimensionSelection.fall_to_center` | sorry-free (variational scaling; replaces retired Kato–Rellich argument) |
| Thm `thm:bound-states`(ii) shadow (D = 3 bounded below) | `Paper2.DimensionSelection.no_collapse_at_three` | sorry-free |
| Thm `thm:d3-unique` (unique selection + flatness corollary) | `Paper2.DimensionSelection.unique_selfconsistent`, `selection_forces_flatness` | sorry-free |
| Lemma `lem:no-definable-distinction` (abstract) | `Paper2.HomogeneityLaw.invariant_constant_on_orbit` | sorry-free |
| Lemma `lem:no-definable-distinction` (concrete: index-permutation unitaries are kernel automorphisms of the model; invariant predicates constant on basis rays) | `Paper2.HomogeneityLaw.permRayEquiv_isKAutomorphism`, `no_definable_vertex_distinction` | sorry-free |

Remaining gaps (documented, not formalized): the full Trofimov/Gromov/Bass–Guivarc'h theorems and Hebisch–Saloff-Coste bounds themselves (imported as hypotheses/cited math); the Homogeneity of Law and Extended Geometry principles (non-theorem content by design); spectral-dimension anomalous-diffusion formulas; the quasimomentum commutator dictionary (candidate for a future `Paper2.LatticeBoost` module).
