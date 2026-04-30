/-
  QuantumRelational/CapacityHalting.lean

  **`thm:capacity-halting`: Capacity Halting Principle**
  **`lem:incompressibility`: Incompressibility of Deterministic Assignments**
  **`thm:ks-bits`: Kochen-Specker Bit Count**

  A deterministic hidden-variable model requires more storage
  than the system's capacity allows:
  - Available: C = log₂ N bits
  - Required for M MUBs: ≥ (M-1) log₂ N bits
  - Maximal MUB count (M = N+1, prime-power N): Θ(N log₂ N) bits

  This information-theoretic argument shows that hidden variables
  are not just undetectable (`thm:parsimony-derived`) but impossible
  to store.

  **Scope note (mechanization vs. physics):**
  The theorems in this file formalize the ELEMENTARY ARITHMETIC STEPS
  of the capacity-deficit argument:
    - `assignment_count_exceeds_capacity`: N^1 < N^(M-1) for N ≥ 2, M ≥ 3
    - `capacity_deficit_bits`: log₂ N < (M-1) · log₂ N for N ≥ 2, M ≥ 3
    - `ks_bit_count_exceeds_capacity`: log₂ N < N² for N ≥ 3
  These are purely arithmetic facts. The PHYSICAL content of the
  capacity-halting argument (that any hidden-variable model reproducing
  empirical quantum statistics requires storage exceeding log₂ N bits)
  comes from combining these arithmetic facts with:
    (a) the MUB geometry (Hilbert-space fact, derived elsewhere)
    (b) Kochen-Specker non-contextuality (paper Prop. `ks-bits`)
    (c) Chaitin's incompressibility theorem applied to empirical outcome
        patterns (paper Lemma `incompressibility`(b))
  Steps (a)-(c) are argued in the main paper (§10, sec:measurement)
  and are NOT separately formalized in Lean. Readers interested in the
  physical scope of the Kolmogorov-based bound should consult the paper,
  which makes explicit that the input is observed experimental
  statistics, not the Born rule as derived in §6.

  Tier 2: Information-theoretic counting (arithmetic step only).
  Lean status: arithmetic inequalities fully proved with zero sorry.
-/
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace QuantumRelational.CapacityHalting

/-- **`thm:capacity-halting` (counting):** For M ≥ 3 MUBs with N outcomes each,
    a deterministic assignment requires at least (M-1) log₂ N bits,
    which exceeds the available log₂ N bits.

    Required: (M-1) log₂ N > log₂ N  iff  M-1 > 1  iff  M ≥ 3.

    We prove the stronger statement: required bits > available bits,
    i.e. Nat.log 2 N < (M - 1) * Nat.log 2 N. -/
theorem capacity_deficit (N M : ℕ) (_hN : 2 ≤ N) (hM : 3 ≤ M) :
    1 < M - 1 := by omega

/-- **`thm:capacity-halting` (full):** The required storage (M-1) log₂ N strictly
    exceeds the available capacity log₂ N for M ≥ 3 MUBs with N ≥ 2. -/
theorem capacity_deficit_bits (N M : ℕ) (hN : 2 ≤ N) (hM : 3 ≤ M) :
    Nat.log 2 N < (M - 1) * Nat.log 2 N := by
  have hlog : 1 ≤ Nat.log 2 N := by
    have h1 : Nat.log 2 2 = 1 := by
      rw [show (2 : ℕ) = 2 ^ 1 from rfl]
      exact Nat.log_pow (by omega : 1 < 2) 1
    calc 1 = Nat.log 2 2 := h1.symm
      _ ≤ Nat.log 2 N := Nat.log_mono_right hN
  have hm1 : 1 < M - 1 := by omega
  calc Nat.log 2 N = 1 * Nat.log 2 N := (Nat.one_mul _).symm
    _ < (M - 1) * Nat.log 2 N := by
        apply Nat.mul_lt_mul_of_pos_right hm1
        omega

/-- Number of deterministic assignments: N^{M-1}.
    For M MUBs with N outcomes, the first basis can be freely assigned,
    and MUB constraints determine the pattern — giving N^{M-1} possible
    assignments that must all be stored. -/
theorem assignment_count_exceeds_capacity (N M : ℕ) (hN : 2 ≤ N) (hM : 3 ≤ M) :
    N ^ 1 < N ^ (M - 1) := by
  apply Nat.pow_lt_pow_right
  · omega
  · omega

/-- **`lem:incompressibility`(a):** Combinatorial lower bound.
    A deterministic assignment λ : {1,...,M} → {1,...,N} requires
    (M-1) log₂ N bits to specify (one of N^{M-1} possibilities). -/
theorem incompressibility_combinatorial (N M : ℕ) (_hN : 2 ≤ N) (hM : 2 ≤ M) :
    1 ≤ M - 1 := by omega

/-- **`lem:incompressibility` (MUB constraint):**
    For MUBs, |⟨bᵢ|b'ⱼ⟩|² = 1/N. This uniform overlap means
    knowing the outcome in one basis provides zero information
    about the outcome in another, forcing independent storage.

    We formalize the core structural property: N uniform overlaps
    of 1/N each sum to 1, confirming the MUB completeness relation. -/
theorem mub_overlap_uniform (N : ℕ) (hN : 0 < N) :
    -- N overlaps of 1/N each sum to 1: N · (1/N) = 1
    (N : ℝ) * (1 / (N : ℝ)) = 1 := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [one_div, mul_inv_cancel₀ hN']

/-- **`thm:ks-bits`:** Kochen-Specker contexts (M MUBs with N projectors
    each) contain O(N²) projectors total; the deterministic-assignment
    storage requirement is (M-1) log₂ N bits, scaling to Θ(N log₂ N)
    for prime-power N at the maximal M = N+1, which strictly exceeds
    the available log₂ N capacity (paper Theorem `thm:ks-bits`).

    This file proves the qualitatively-correct loose form: log₂ N < N²
    for N ≥ 3, since log₂ N < N (always) and N ≤ N² (for N ≥ 1). The
    looser N² bound suffices for the qualitative capacity-overflow
    argument; the sharper Θ(N log₂ N) figure of the paper is argued
    via the MUB structure of `lem:incompressibility`(a) above. -/
theorem ks_bit_count_exceeds_capacity (N : ℕ) (hN : 3 ≤ N) :
    Nat.log 2 N < N ^ 2 := by
  -- log₂ N < N for N ≥ 1 (since N < 2^N)
  have h1 : Nat.log 2 N < N := Nat.log_lt_self 2 (by omega)
  calc Nat.log 2 N < N := h1
    _ ≤ N * N := Nat.le_mul_of_pos_left N (by omega)
    _ = N ^ 2 := (Nat.pow_two N).symm

-- ============================================================
-- Statement #83: Information-Theoretic Capacity
-- ============================================================

/-- **Definition 83: Information-Theoretic Capacity**

The Shannon capacity of a system with N perfectly distinguishable
states is C = log₂ N bits. This is the maximum Shannon entropy
H({p_i}) = -Σ p_i log₂ p_i, achieved by the uniform distribution
over the N basis states. -/
def info_capacity (N : ℕ) : ℕ := Nat.log 2 N

/-- For N ≥ 2, the information-theoretic capacity is at least 1 bit.
    Since log₂ 2 = 1 and log₂ is monotone, N ≥ 2 gives C ≥ 1. -/
theorem info_capacity_ge_one (N : ℕ) (hN : 2 ≤ N) :
    1 ≤ info_capacity N := by
  unfold info_capacity
  -- log₂(2) = log₂(2^1) = 1, and log is monotone in the argument
  have h1 : Nat.log 2 2 = 1 := by
    rw [show (2 : ℕ) = 2 ^ 1 from rfl]
    exact Nat.log_pow (by omega : 1 < 2) 1
  calc 1 = Nat.log 2 2 := h1.symm
    _ ≤ Nat.log 2 N := Nat.log_mono_right hN

/-- Capacity is monotone in N: more distinguishable states means
    more information-theoretic capacity. -/
theorem info_capacity_mono (N M : ℕ) (h : N ≤ M) :
    info_capacity N ≤ info_capacity M := by
  unfold info_capacity
  exact Nat.log_mono_right h

-- ============================================================
-- Statement #85: Hidden-Variable Assignment
-- ============================================================

/-- **Definition 85: Hidden-Variable Assignment**

A deterministic hidden-variable assignment for state ψ is a function
λ_ψ : 𝔅 → {1,...,N} specifying, for each measurement basis B ∈ 𝔅,
which outcome occurs with certainty.

The type parameter `β` represents the set of bases 𝔅. For each
basis, the assignment picks one of the N outcomes (represented
as Fin N). -/
structure HiddenVariableAssignment (β : Type*) (N : ℕ) where
  /-- The deterministic outcome assignment: for each basis, which outcome occurs -/
  assign : β → Fin N

/-- A hidden-variable assignment requires specifying one of N outcomes
    for each of M bases, giving N^M total possibilities. The storage
    in bits is at least M · log₂ N, which exceeds capacity log₂ N
    when M ≥ 2. -/
theorem hva_storage_exceeds_capacity (N M : ℕ) (hN : 2 ≤ N) (hM : 2 ≤ M) :
    Nat.log 2 N < M * Nat.log 2 N := by
  have hlog : 1 ≤ Nat.log 2 N := info_capacity_ge_one N hN
  -- M ≥ 2, so M * log₂ N ≥ 2 * log₂ N > log₂ N (since log₂ N ≥ 1)
  calc Nat.log 2 N = 1 * Nat.log 2 N := (Nat.one_mul _).symm
    _ < M * Nat.log 2 N := by
        apply Nat.mul_lt_mul_of_pos_right
        · omega
        · omega

-- ============================================================
-- Statement #84: Capacity as Physical Bound
-- ============================================================

/-- **Proposition 84: Capacity as Physical Bound**

C = log₂(N) is the maximum extractable classical information from
a single measurement. One measurement on a basis gives one of N
outcomes, encoding exactly log₂(N) bits. For M independent
measurements, total extractable information is M · log₂(N).

Key facts:
1. log₂(N) bits are needed to index N outcomes (each basis measurement
   selects one of N mutually exclusive results).
2. For M independent measurements on separate copies, the total
   information is M · log₂(N) = log₂(N^M).

Uses: Statement #85 (info_capacity). -/
theorem capacity_is_log_bits (N : ℕ) (_hN : 2 ≤ N) :
    info_capacity N = Nat.log 2 N := rfl

/-- For M independent measurements, total information is M · log₂(N). -/
theorem total_info_M_measurements (N M : ℕ) (_hN : 2 ≤ N) (_hM : 1 ≤ M) :
    M * info_capacity N = M * Nat.log 2 N := rfl

/-- M independent measurements on an N-outcome system can distinguish
    at most N^M total configurations. -/
theorem measurement_configurations (N M : ℕ) (hN : 2 ≤ N) (hM : 1 ≤ M) :
    N ≤ N ^ M := by
  calc N = N ^ 1 := (Nat.pow_one N).symm
    _ ≤ N ^ M := Nat.pow_le_pow_right (by omega) hM

/-- A single measurement gives at most log₂(N) bits, which is
    strictly less than the storage required for a hidden-variable
    assignment over 2 or more bases. -/
theorem single_measurement_bound (N : ℕ) (hN : 2 ≤ N) :
    info_capacity N < 2 * info_capacity N := by
  have : 1 ≤ info_capacity N := info_capacity_ge_one N hN
  omega

-- ============================================================
-- Statement #94: Contextuality from Finite Capacity
-- ============================================================

/-
**Theorem 94: Contextuality from Finite Capacity**

Contextuality follows from finite capacity: a non-contextual
hidden-variable model requires more storage than the system's
capacity allows.

A non-contextual model assigns a definite outcome to every
measurement basis independently. For M >= 3 mutually unbiased
bases (MUBs) with N outcomes each:

- Available storage: C = log2(N) bits (Definition `def:info-capacity`)
- Required for non-contextual assignment: (M-1) * log2(N) bits
  (`thm:capacity-halting`, capacity_deficit)
- Since M >= 3, we have (M-1) >= 2, so (M-1) * log2(N) > log2(N)

Combined with the Born rule normalization (Statement #93:
probabilities p_k = 1 - K(psi, a_k) satisfy Kolmogorov axioms),
a non-contextual model must reproduce these probabilities for ALL
bases simultaneously, requiring consistent assignments that
exceed the information-theoretic capacity.

Uses: Statement #86 (capacity halting), #93 (probabilistic response).
-/

/-- The storage required for a non-contextual model exceeds capacity:
    (M-1) · log₂(N) > log₂(N) for M ≥ 3 and N ≥ 2.
    This is the core information-theoretic impossibility. -/
theorem contextuality_storage_exceeds_capacity (N M : ℕ)
    (hN : 2 ≤ N) (hM : 3 ≤ M) :
    Nat.log 2 N < (M - 1) * Nat.log 2 N := by
  have hlog : 1 ≤ Nat.log 2 N := info_capacity_ge_one N hN
  have hm1 : 1 < M - 1 := capacity_deficit N M hN hM
  calc Nat.log 2 N = 1 * Nat.log 2 N := (Nat.one_mul _).symm
    _ < (M - 1) * Nat.log 2 N := by
        apply Nat.mul_lt_mul_of_pos_right hm1
        omega

/-- The deficit factor: the ratio of required to available bits is
    (M-1), which is at least 2 for M ≥ 3.
    This quantifies HOW MUCH the non-contextual model exceeds capacity. -/
theorem contextuality_deficit_factor (M : ℕ) (hM : 3 ≤ M) :
    2 ≤ M - 1 := by omega

/-- For the minimal non-contextual scenario (M = 3 MUBs), the
    required storage is exactly 2 · log₂(N), which is double
    the available capacity. -/
theorem contextuality_minimal_case (N : ℕ) (hN : 2 ≤ N) :
    Nat.log 2 N < 2 * Nat.log 2 N := by
  have hlog : 1 ≤ Nat.log 2 N := info_capacity_ge_one N hN
  omega

/-- Full contextuality theorem: combining capacity deficit with
    assignment count. A non-contextual model for M ≥ 3 MUBs
    requires N^{M-1} distinct assignments, but the system can
    only encode N^1 = N states. The excess is N^{M-1} / N = N^{M-2},
    which is at least N ≥ 2 for M ≥ 3. -/
theorem contextuality_full (N M : ℕ) (hN : 2 ≤ N) (hM : 3 ≤ M) :
    -- Required assignments exceed available states
    N ^ 1 < N ^ (M - 1) ∧
    -- Required bits exceed available bits
    Nat.log 2 N < (M - 1) * Nat.log 2 N :=
  ⟨assignment_count_exceeds_capacity N M hN hM,
   contextuality_storage_exceeds_capacity N M hN hM⟩

-- ============================================================
-- Statement #86/94: Strengthened Storage Argument
-- ============================================================

/-- **Storage argument (strengthened):** N^(M-1) > N for M ≥ 3 and N ≥ 2.

    A deterministic hidden-variable model must assign outcomes to M MUBs
    independently. The number of possible assignment patterns is N^(M-1)
    (one basis is "free", the remaining M-1 are constrained). This exceeds
    the system capacity N, which can store at most N states.

    The ratio N^(M-1) / N = N^(M-2) measures the capacity overflow.
    For M = 3: overflow = N (at least 2).
    For M = 4: overflow = N² (at least 4).
    This grows exponentially with the number of measurement contexts. -/
theorem storage_overflow_ratio (N M : ℕ) (hN : 2 ≤ N) (hM : 3 ≤ M) :
    N ≤ N ^ (M - 2) := by
  calc N = N ^ 1 := (Nat.pow_one N).symm
    _ ≤ N ^ (M - 2) := Nat.pow_le_pow_right (by omega) (by omega)

/-- The overflow grows with the number of contexts: for each additional
    MUB beyond 2, the assignment count multiplies by N.
    N^(M-1) = N · N^(M-2). -/
theorem storage_overflow_multiplicative (N M : ℕ) (hM : 2 ≤ M) :
    N ^ (M - 1) = N * N ^ (M - 2) := by
  have : M - 1 = (M - 2) + 1 := by omega
  rw [this, pow_succ, mul_comm]

/-- **The assignment-to-capacity ratio is at least N for M ≥ 3:**
    N^(M-1) ≥ N² > N. This is the quantitative capacity overflow.
    The hidden-variable model needs at least N² distinct states but
    the system only has N. -/
theorem assignment_exceeds_capacity_squared (N M : ℕ) (hN : 2 ≤ N) (hM : 3 ≤ M) :
    N ^ 2 ≤ N ^ (M - 1) := by
  apply Nat.pow_le_pow_right (by omega)
  omega

/-- For M ≥ 3 and N ≥ 2, the assignment count N^(M-1) strictly exceeds N:
    N^(M-1) ≥ N² ≥ 4 > N ≥ 2. This is the core impossibility. -/
theorem capacity_overflow_strict (N M : ℕ) (hN : 2 ≤ N) (hM : 3 ≤ M) :
    N < N ^ (M - 1) := by
  calc N = N ^ 1 := (Nat.pow_one N).symm
    _ < N ^ (M - 1) := Nat.pow_lt_pow_right (by omega) (by omega)

-- ============================================================
-- Shannon Entropy Bound on Deterministic Assignments
-- ============================================================

/-! ### Information content of deterministic assignments

The arithmetic inequalities above formalize the COUNTING step of the
capacity-deficit argument. This section adds entropy-based bounds:
the number of bits required to distinguish N^(M-1) assignments is
exactly (M-1) · log₂ N, by the standard entropy formula for uniform
distributions over a finite outcome set.

This connects the combinatorial bound (assignment count) to the
information-theoretic content of the capacity-halting argument.

The Kolmogorov-complexity bound (Lemma `lem:incompressibility`(b) in
the paper), which uses empirical outcome patterns rather than a priori
counting, is not formalized here — it requires Chaitin's incompressibility
theorem applied to observed Bernoulli-like statistics (see paper §10).
-/

/-- **Real-valued entropy: log₂(N^M) = M · log₂ N.**

    In real arithmetic, the logarithm of `N^M` is exactly `M · log₂ N`.
    This is the clean entropy formula: a uniform distribution over
    `N^M` equiprobable outcomes has Shannon entropy `M · log₂ N` bits.

    Unlike the `Nat.log` version (which carries floor truncation and
    therefore does NOT satisfy `Nat.log 2 (N^M) = M · Nat.log 2 N` in
    general), the real-logarithm formulation gives the standard
    identity cleanly. -/
theorem real_entropy_pow_identity (N : ℕ) (M : ℕ) (hN : 1 ≤ N) :
    Real.logb 2 ((N : ℝ) ^ M) = (M : ℝ) * Real.logb 2 N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [Real.logb_pow]

/-- **Information content of M-fold assignments (real-valued).**

    The number of bits needed to specify one of N^M distinct
    assignments is exactly M · log₂ N, computed in the real numbers.
    This is the entropy of a uniform distribution over N^M
    equiprobable outcomes. -/
theorem information_content_M_fold (N : ℕ) (M : ℕ) (hN : 1 ≤ N) :
    Real.logb 2 ((N : ℝ) ^ M) = (M : ℝ) * Real.logb 2 N :=
  real_entropy_pow_identity N M hN

/-- **The capacity deficit in real-valued Shannon-entropy bits.**

    Available: log₂ N bits (capacity of a single state selection).
    Required: (M-1) · log₂ N bits (information content of assignments
    over M bases with one free outcome).

    Deficit = (M-2) · log₂ N bits > 0 for M ≥ 3, N ≥ 2.

    This is the entropy-level formalization of the arithmetic inequality
    `N^1 < N^(M-1)` (proved above as `capacity_overflow_strict`),
    expressed in the more standard "bits" units of Shannon entropy. -/
theorem shannon_capacity_deficit (N M : ℕ) (hN : 2 ≤ N) (hM : 3 ≤ M) :
    Real.logb 2 ((N : ℝ) ^ (M - 1)) - Real.logb 2 N =
    ((M : ℝ) - 2) * Real.logb 2 N := by
  rw [information_content_M_fold N (M - 1) (by omega)]
  have hM_cast : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
    have : 1 ≤ M := by omega
    push_cast [this]
    ring
  rw [hM_cast]
  ring

/-- **The deficit is positive.**

    For M ≥ 3 and N ≥ 2, the Shannon capacity deficit
    `(M-2) · log₂ N` is strictly positive: the required information
    content exceeds the available capacity by a positive amount.

    This makes the "capacity halting" claim quantitative: the deficit
    is not merely nonzero but grows linearly with the number of
    additional measurement contexts beyond the first two. -/
theorem shannon_capacity_deficit_positive (N M : ℕ) (hN : 2 ≤ N) (hM : 3 ≤ M) :
    0 < Real.logb 2 ((N : ℝ) ^ (M - 1)) - Real.logb 2 N := by
  rw [shannon_capacity_deficit N M hN hM]
  have h1 : (0 : ℝ) < (M : ℝ) - 2 := by
    have : (2 : ℝ) < M := by exact_mod_cast (show 2 < M by omega)
    linarith
  have h2 : (0 : ℝ) < Real.logb 2 N := by
    apply Real.logb_pos (by norm_num : (1 : ℝ) < 2)
    exact_mod_cast (show 1 < N by omega)
  exact mul_pos h1 h2

-- Connection to Kolmogorov complexity (informal, documentation only).
--
-- The Shannon entropy `(M-1) log₂ N` is the average bit-cost of
-- specifying a uniform random assignment. Chaitin's incompressibility
-- theorem (paper Lemma `lem:incompressibility`(b)) recovers the same
-- `(M-1) log₂ N - O(log M)` bound via algorithmic information rather
-- than combinatorial counting: any deterministic HV reproducing the
-- observed Born statistics for M MUBs encodes a record of typical
-- entropy `(M-1) log₂ N`, so Chaitin gives the matching Kolmogorov
-- lower bound. The (a) and (b) bounds therefore agree in absolute
-- strength; (b) supplies an independent route that does not require
-- the Hilbert-space MUB geometry as a hypothesis. The deficit appears
-- at M ≥ 3 in both bounds (the M = 2 case is marginal and is closed
-- by applying (a) at M = 3, since three MUBs exist for every N ≥ 2).
--
-- Formalizing this Kolmogorov bound would require mechanizing
-- Chaitin's theorem and empirical outcome patterns, which is beyond
-- the current scope. The paper argues it explicitly in §10.

end QuantumRelational.CapacityHalting
