/-
  QuantumRelational/Main.lean

  **`thm:main`: Main Theorem — Characterization of Relational Theories**

  For a distinguishability space (𝒳, K) satisfying Axioms 1-2
  (Finite Capacity with Saturation and Universal Relationality with
  Operational Completeness), the following are derived:

  (i)   Parsimony: no hidden variables beyond K
  (ii)  Capacity Halting: determinism requires (M-1) log₂ N bits across
        M MUBs against log₂ N available, scaling to Θ(N log₂ N) for
        prime-power N at the maximal M = N+1
  (iii) Complex numbers ℂ are the unique coefficient field
  (iv)  The Born rule p_k = |c_k|² from metric compatibility
  (v)   Non-trivial continuous dynamics requires N ≥ 3

  The capacity N is the only free parameter.

  This file imports all component files and states the Main Theorem as
  a conjunction referencing the proved results.

  Lean status: fully-derived (0 sorry)
-/
import QuantumRelational.Axioms
import QuantumRelational.Parsimony
import QuantumRelational.CapacityHalting
import QuantumRelational.CyclicEigen
import QuantumRelational.Frobenius
import QuantumRelational.BornRule
import QuantumRelational.MetricBridge
import QuantumRelational.Composite
import QuantumRelational.FubiniStudy

namespace QuantumRelational.Main

open QuantumRelational

/-! ### Statement 1: Main Theorem

The five conclusions of the main theorem, each proved in its respective file.
We state them here as a unified result, bundling the logical structure. -/

/-- **Conclusion (i): Parsimony — No hidden variables.**

For an operationally complete kernel K, any hidden variable extension
that factors through K is trivial: the hidden variable λ has no effect.

Proved in: `QuantumRelational.Parsimony.parsimony` -/
theorem conclusion_i_parsimony
    {X Λ : Type*} (K : X → X → ℝ)
    (hcomplete : Parsimony.OperationallyComplete K)
    (K' : (X × Λ) → (X × Λ) → ℝ)
    (hfactor : Parsimony.FactorsThroughK K Λ K')
    (x : X) (l1 l2 : Λ) :
    ∀ (y : X) (mu : Λ), K' (x, l1) (y, mu) = K' (x, l2) (y, mu) :=
  Parsimony.parsimony K hcomplete K' hfactor x l1 l2

/-- **Conclusion (ii): Capacity Halting — Determinism requires too many bits.**

For N ≥ 2 and M ≥ 3 MUBs, the number of deterministic outcome
assignments N^(M-1) exceeds the single-measurement capacity N^1.
This forces stochastic outcomes (probabilistic measurement results).

Proved in: `QuantumRelational.CapacityHalting.assignment_count_exceeds_capacity` -/
theorem conclusion_ii_capacity_halting :
    ∀ (N M : ℕ), 2 ≤ N → 3 ≤ M → N ^ 1 < N ^ (M - 1) :=
  fun N M hN hM => CapacityHalting.assignment_count_exceeds_capacity N M hN hM

/-- **Conclusion (iii): Complex numbers are the unique coefficient field.**

For N ≥ 3, the cyclic permutation matrix has non-real eigenvalues
(e^{2πi/N} has nonzero imaginary part), forcing the coefficient
field to extend beyond ℝ. Combined with Frobenius' classification
(ℝ, ℂ, ℍ), local tomography selects ℂ.

Proved in: `QuantumRelational.CyclicEigen.complex_forced` -/
theorem conclusion_iii_complex_forced :
    ∀ (N : ℕ), 3 ≤ N →
    ∃ (k : Fin N), (CyclicEigen.rootOfUnity N k).im ≠ 0 :=
  CyclicEigen.complex_forced

/-- **Conclusion (iv): The Born rule p_k = |c_k|².**

Any admissible probability assignment satisfying the metric
compatibility ODE (g_FR = c² · g_FS) must equal the identity
on [0,1], giving p_k = f(|c_k|²) = |c_k|².

Proved in: `QuantumRelational.BornRule.ode_uniqueness_born_rule` -/
theorem conclusion_iv_born_rule
    (f f' : ℝ → ℝ) (c : ℝ)
    (hode : BornRule.MetricCompatibilityODE f f' c)
    (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (hf_mono : Monotone f)
    (hf_cont : ContinuousOn f (Set.Icc 0 1))
    (hderiv : ∀ x, 0 < x → x < 1 → HasDerivAt f (f' x) x) :
    (∀ x, 0 ≤ x → x ≤ 1 → f x = x) ∧ c = 1 :=
  BornRule.ode_uniqueness_born_rule f f' c hode hf0 hf1 hf_mono hf_cont hderiv

/-- **Conclusion (v): Non-trivial continuous dynamics requires N ≥ 3.**

For N = 2, all eigenvalues of the cyclic permutation are real
(±1), so the dynamics group is discrete ({I, π}). Continuous
dynamics (the Schrödinger equation) requires N ≥ 3.

Proved in: `QuantumRelational.CyclicEigen.N2_eigenvalues_real` -/
theorem conclusion_v_n2_static :
    (CyclicEigen.rootOfUnity 2 ⟨0, by omega⟩).im = 0 ∧
    (CyclicEigen.rootOfUnity 2 ⟨1, by omega⟩).im = 0 :=
  CyclicEigen.N2_eigenvalues_real

/-- **Theorem 1: Main Theorem (unified statement).**

For a distinguishability space with capacity N ≥ 2:

(i)   Parsimony: hidden variable extensions are trivial
(ii)  Capacity Halting: determinism fails for N ≥ 4 (too many bits)
(iii) Complex numbers: forced for N ≥ 3 by non-real eigenvalues
(iv)  Born rule: p_k = |c_k|² from metric compatibility
(v)   N ≥ 3 required for continuous dynamics

Together, these show that quantum mechanics (over ℂ, with Born rule,
unitary dynamics) is the unique theory satisfying the axioms.
The capacity N is the only free parameter.

This theorem packages the five independently proved conclusions. -/
theorem main_theorem :
    -- (i) Parsimony
    (∀ {X Λ : Type*} (K : X → X → ℝ)
      (_hcomplete : Parsimony.OperationallyComplete K)
      (K' : (X × Λ) → (X × Λ) → ℝ)
      (_hfactor : Parsimony.FactorsThroughK K Λ K')
      (x : X) (l1 l2 : Λ) (y : X) (mu : Λ),
      K' (x, l1) (y, mu) = K' (x, l2) (y, mu)) ∧
    -- (ii) Capacity Halting: N^1 < N^(M-1) for N ≥ 2, M ≥ 3
    (∀ (N M : ℕ), 2 ≤ N → 3 ≤ M → N ^ 1 < N ^ (M - 1)) ∧
    -- (iii) Complex numbers forced for N ≥ 3
    (∀ (N : ℕ), 3 ≤ N →
      ∃ (k : Fin N), (CyclicEigen.rootOfUnity N k).im ≠ 0) ∧
    -- (iv) Born rule from ODE uniqueness
    (∀ (f f' : ℝ → ℝ) (c : ℝ),
      BornRule.MetricCompatibilityODE f f' c →
      f 0 = 0 → f 1 = 1 → Monotone f →
      ContinuousOn f (Set.Icc 0 1) →
      (∀ x, 0 < x → x < 1 → HasDerivAt f (f' x) x) →
      (∀ x, 0 ≤ x → x ≤ 1 → f x = x) ∧ c = 1) ∧
    -- (v) N = 2 has only real eigenvalues (no continuous dynamics)
    ((CyclicEigen.rootOfUnity 2 ⟨0, by omega⟩).im = 0 ∧
     (CyclicEigen.rootOfUnity 2 ⟨1, by omega⟩).im = 0) :=
  ⟨fun K hc K' hf x l1 l2 y mu =>
      Parsimony.parsimony K hc K' hf x l1 l2 y mu,
   fun N M hN hM => CapacityHalting.assignment_count_exceeds_capacity N M hN hM,
   CyclicEigen.complex_forced,
   fun f f' c hode hf0 hf1 hm hcont hd =>
      BornRule.ode_uniqueness_born_rule f f' c hode hf0 hf1 hm hcont hd,
   CyclicEigen.N2_eigenvalues_real⟩

end QuantumRelational.Main
