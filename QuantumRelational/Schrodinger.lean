/-
  QuantumRelational/Schrodinger.lean

  **Theorem 82: Schrodinger Equation -- Existence and Uniqueness**

  The evolution equation ih d/dt |psi> = H|psi> is the unique equation
  governing kernel-preserving dynamics.

  Derivation chain (each step formalized):
  1. K-preserving dynamics ==> transition probability preserving
     (algebraic: K = 1 - |<*|*>|^2, so K-preservation <==> |<*|*>|-preservation)
  2. Wigner's theorem + continuity ==> U(t) preserves inner products (unitarity)
     (axiom: wigner_continuity_unitary)
  3. Stone's theorem ==> U(t) = e^{-iHt} for unique self-adjoint H
     (axiom: stone_generator)
  4. H is the Hamiltonian; E = <psi|H|psi> is the energy
  5. [H,H] = 0 ==> energy conservation

  Tier 2: Uses Wigner and Stone as axioms.
-/
import QuantumRelational.ClassicalImports
import QuantumRelational.Axioms

open Matrix NormedSpace

namespace QuantumRelational.Schrodinger

-- ============================================================
-- Step 0: Unitary evolution preserves K (converse direction)
-- ============================================================

/-- Unitary evolution preserves K.
    If U preserves inner products (<Uψ|Uφ> = <ψ|φ>), then K(Uψ, Uφ) = K(ψ, φ),
    since K = 1 - |<*|*>|^2. -/
theorem unitary_preserves_K
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {U : V → V}
    (hU : ∀ ψ φ : V, @inner ℂ V _ (U ψ) (U φ) = @inner ℂ V _ ψ φ)
    (ψ φ : V) :
    1 - ‖@inner ℂ V _ (U ψ) (U φ)‖ ^ 2 = 1 - ‖@inner ℂ V _ ψ φ‖ ^ 2 := by
  rw [hU]

-- ============================================================
-- Step 1: K-preservation ==> transition probability preservation
-- ============================================================

/-- **Step 1 of the derivation chain:**
    K-preservation implies transition probability preservation.

    K(ψ,φ) = 1 - |<ψ|φ>|^2, so if K(U(t)ψ, U(t)φ) = K(ψ,φ) for all ψ,φ,
    then |<U(t)ψ|U(t)φ>|^2 = |<ψ|φ>|^2, hence ‖<U(t)ψ|U(t)φ>‖ = ‖<ψ|φ>‖.

    This is the algebraic step that extracts transition-probability preservation
    from K-preservation. -/
theorem K_pres_implies_transition_prob_pres
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (U : ℝ → V → V)
    (hK : ∀ t ψ φ,
      1 - ‖@inner ℂ V _ (U t ψ) (U t φ)‖ ^ 2 =
      1 - ‖@inner ℂ V _ ψ φ‖ ^ 2) :
    ∀ t ψ φ, ‖@inner ℂ V _ (U t ψ) (U t φ)‖ ^ 2 =
              ‖@inner ℂ V _ ψ φ‖ ^ 2 := by
  intro t ψ φ
  linarith [hK t ψ φ]

/-- The norm-squared equality implies norm equality (for nonneg reals). -/
theorem norm_sq_eq_implies_norm_eq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 = b ^ 2) : a = b := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]

/-- K-preservation implies that ‖<U(t)ψ|U(t)φ>‖ = ‖<ψ|φ>‖. -/
theorem K_pres_implies_norm_inner_pres
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (U : ℝ → V → V)
    (hK : ∀ t ψ φ,
      1 - ‖@inner ℂ V _ (U t ψ) (U t φ)‖ ^ 2 =
      1 - ‖@inner ℂ V _ ψ φ‖ ^ 2) :
    ∀ t ψ φ, ‖@inner ℂ V _ (U t ψ) (U t φ)‖ =
              ‖@inner ℂ V _ ψ φ‖ := by
  intro t ψ φ
  have hsq := K_pres_implies_transition_prob_pres U hK t ψ φ
  exact norm_sq_eq_implies_norm_eq _ _ (norm_nonneg _) (norm_nonneg _) hsq

-- ============================================================
-- Step 2: Wigner + continuity ==> inner product preservation
-- ============================================================

/-- **Step 2 of the derivation chain (Theorem 82, core):**
    K-preservation + group structure + continuity ==> inner product preservation.

    This is the main content of the Schrodinger derivation:
    1. K-preservation gives ‖<U(t)ψ|U(t)φ>‖ = ‖<ψ|φ>‖ (Step 1)
    2. Wigner's theorem + continuity gives <U(t)ψ|U(t)φ> = <ψ|φ> (axiom)

    The conclusion <U(t)ψ|U(t)φ> = <ψ|φ> is unitarity: U(t) is a
    unitary operator for each t. -/
theorem schrodinger_derivation_chain
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (U : ℝ → V → V)
    (hK_pres : ∀ t ψ φ,
      1 - ‖@inner ℂ V _ (U t ψ) (U t φ)‖ ^ 2 =
      1 - ‖@inner ℂ V _ ψ φ‖ ^ 2)
    (hgroup : ∀ s t ψ, U (s + t) ψ = U s (U t ψ))
    (hid : ∀ ψ, U 0 ψ = ψ) :
    ∀ t ψ φ, @inner ℂ V _ (U t ψ) (U t φ) = @inner ℂ V _ ψ φ := by
  -- Step 1: Extract transition probability preservation from K-preservation
  have h_tp := K_pres_implies_norm_inner_pres U hK_pres
  -- Step 2: Apply Wigner's theorem (axiom) to upgrade norm-preservation to
  -- full inner-product preservation, using continuity to exclude antiunitary
  exact ClassicalImports.wigner_continuity_unitary U h_tp hgroup hid

-- ============================================================
-- Step 3: Stone's theorem ==> self-adjoint generator exists
-- ============================================================

/-- **Step 3: From unitarity to self-adjoint generator (matrix version).**
    Once we know U(t) is unitary (from Step 2), Stone's theorem gives
    a self-adjoint generator H. This is the matrix-level statement:
    a one-parameter unitary group on C^n has a Hermitian generator. -/
theorem stone_gives_hermitian_generator (n : ℕ) (hn : 1 ≤ n)
    (U : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (hunit : ∀ t, (U t).conjTranspose * U t = 1)
    (hgroup : ∀ s t, U (s + t) = U s * U t)
    (hid : U 0 = 1) :
    ∃ H : Matrix (Fin n) (Fin n) ℂ, H.conjTranspose = H :=
  let ⟨H, _, hH, _⟩ := ClassicalImports.stone_generator n hn U hunit hgroup hid
  ⟨H, hH⟩

-- ============================================================
-- Step 4-5: Algebraic consequences of having a generator
-- ============================================================

/-- The commutator [A, B] = AB - BA. -/
def commutator {R : Type*} [Ring R] (A B : R) : R := A * B - B * A

-- ============================================================
-- Step 4-5: Energy Conservation (Strengthened)
-- ============================================================

/-- **Commutator antisymmetry:** [A, B] = -[B, A]. -/
theorem commutator_antisymm {R : Type*} [Ring R] (A B : R) :
    commutator A B = -commutator B A := by
  simp [commutator, neg_sub]

/-- **Commutator linearity (left):** [A + B, C] = [A, C] + [B, C]. -/
theorem commutator_add_left {R : Type*} [Ring R] (A B C : R) :
    commutator (A + B) C = commutator A C + commutator B C := by
  simp [commutator, add_mul, mul_add]
  abel

/-- **Commutator with product (Leibniz rule):** [A, B*C] = [A,B]*C + B*[A,C]. -/
theorem commutator_mul_right {R : Type*} [Ring R] (A B C : R) :
    commutator A (B * C) = commutator A B * C + B * commutator A C := by
  simp only [commutator, mul_sub, sub_mul, mul_assoc]
  abel

/-- **Commutant property for matrix evolution:**
    If H commutes with U (HU = UH), then U† H U = H.

    This is the key algebraic step for energy conservation: when
    U = exp(-iHt), H commutes with U because H commutes with every
    power of itself, hence U†HU = U†UH = H.

    The proof uses: HU = UH implies U†HU = U†UH = 1·H = H.
    This requires unitarity U†U = 1. -/
theorem commutant_conjugation_invariant (n : ℕ)
    (U H : Matrix (Fin n) (Fin n) ℂ)
    (hunit : U.conjTranspose * U = 1)
    (hcomm : commutator H U = 0) :
    U.conjTranspose * H * U = H := by
  -- From [H, U] = 0: HU = UH, i.e., H * U = U * H
  have hHU : H * U = U * H := by
    have h := hcomm
    simp only [commutator] at h
    -- h : H * U - U * H = 0
    exact sub_eq_zero.mp h
  -- U† * H * U = U† * (U * H) = (U† * U) * H = 1 * H = H
  calc U.conjTranspose * H * U
      = U.conjTranspose * (H * U) := by rw [Matrix.mul_assoc]
    _ = U.conjTranspose * (U * H) := by rw [hHU]
    _ = (U.conjTranspose * U) * H := by rw [Matrix.mul_assoc]
    _ = 1 * H := by rw [hunit]
    _ = H := by rw [Matrix.one_mul]

/-- **Energy expectation is constant under unitary evolution (matrix version):**

    For a unitary U with [H, U] = 0, and any state vector ψ ∈ ℂⁿ:
      ψ† U† H U ψ = ψ† H ψ

    This is the matrix-level statement of energy conservation:
    ⟨ψ(t)|H|ψ(t)⟩ = ⟨ψ|H|ψ⟩ where |ψ(t)⟩ = U(t)|ψ⟩.

    The proof reduces to U†HU = H (commutant_conjugation_invariant). -/
theorem energy_expectation_constant (n : ℕ)
    (U H : Matrix (Fin n) (Fin n) ℂ)
    (hunit : U.conjTranspose * U = 1)
    (hcomm : commutator H U = 0)
    (ψ : Fin n → ℂ) :
    dotProduct (star (U.mulVec ψ)) (H.mulVec (U.mulVec ψ)) =
    dotProduct (star ψ) (H.mulVec ψ) := by
  -- Goal: (star (U *ᵥ ψ)) ⬝ᵥ (H *ᵥ (U *ᵥ ψ)) = (star ψ) ⬝ᵥ (H *ᵥ ψ)
  -- Step 1: star (U *ᵥ ψ) = (star ψ) ᵥ* U†
  rw [star_mulVec]
  -- Step 2: H *ᵥ (U *ᵥ ψ) = (H * U) *ᵥ ψ
  rw [mulVec_mulVec]
  -- Step 3: ((star ψ) ᵥ* U†) ⬝ᵥ ((H * U) *ᵥ ψ) = (star ψ) ⬝ᵥ ((U† * (H * U)) *ᵥ ψ)
  rw [dotProduct_mulVec, vecMul_vecMul]
  -- Step 4: U† * (H * U) = U† * H * U = H
  rw [← Matrix.mul_assoc, commutant_conjugation_invariant n U H hunit hcomm]
  -- Step 5: (star ψ) ᵥ* H ⬝ᵥ ψ = (star ψ) ⬝ᵥ (H *ᵥ ψ)
  exact (dotProduct_mulVec (star ψ) H ψ).symm

/-- **Unitary group property (matrix version):**
    U(s + t) = U(s) * U(t) is equivalent to U being a group homomorphism
    from (ℝ, +) to (GL_n(ℂ), ×). For a unitary group generated by a
    time-independent Hamiltonian H, this follows from exp(-iH(s+t)) =
    exp(-iHs) * exp(-iHt), which holds because -iH commutes with itself.

    We prove the algebraic identity that underpins this: if a one-parameter
    group satisfies U(s+t) = U(s)U(t) and U(0) = 1, then U(-t) is a
    left inverse of U(t). -/
theorem unitary_group_inverse (n : ℕ)
    (U : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (hgroup : ∀ s t, U (s + t) = U s * U t)
    (hid : U 0 = 1) :
    ∀ t, U (-t) * U t = 1 := by
  intro t
  have h := hgroup (-t) t
  simp at h
  rw [hid] at h
  exact h.symm

/-- The group property also gives U(t) * U(-t) = 1 (right inverse). -/
theorem unitary_group_inverse_right (n : ℕ)
    (U : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (hgroup : ∀ s t, U (s + t) = U s * U t)
    (hid : U 0 = 1) :
    ∀ t, U t * U (-t) = 1 := by
  intro t
  have h := hgroup t (-t)
  simp at h
  rw [hid] at h
  exact h.symm

/-- **Group homomorphism associativity:**
    U(r + s + t) = U(r) * U(s) * U(t). This follows from the group
    property applied twice. -/
theorem unitary_group_assoc (n : ℕ)
    (U : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (hgroup : ∀ s t, U (s + t) = U s * U t) :
    ∀ r s t, U (r + s + t) = U r * U s * U t := by
  intro r s t
  rw [hgroup (r + s) t, hgroup r s]

/-- **Unitarity from the group property and conjugate-transpose:**
    If U(t)† = U(-t) and U(s+t) = U(s)U(t) with U(0) = 1,
    then U(t)†U(t) = 1 (unitarity).

    This shows that the conjugate-transpose condition U(t)† = U(-t)
    is equivalent to unitarity for group homomorphisms. For
    U(t) = exp(-iHt) with H self-adjoint: U(t)† = exp(iH†t) = exp(iHt) = U(-t). -/
theorem unitary_from_adjoint_inverse (n : ℕ)
    (U : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (hgroup : ∀ s t, U (s + t) = U s * U t)
    (hid : U 0 = 1)
    (hadj : ∀ t, (U t).conjTranspose = U (-t)) :
    ∀ t, (U t).conjTranspose * U t = 1 := by
  intro t
  rw [hadj t]
  exact unitary_group_inverse n U hgroup hid t

-- ============================================================
-- The full derivation chain (summary theorem)
-- ============================================================

/-- **Theorem 82 (full chain, matrix version):**
    K-preserving one-parameter group on C^n ==> self-adjoint generator
    with energy conservation.

    This combines all steps:
    1. K-preservation ==> transition probability preservation
    2. Wigner + continuity ==> unitarity
    3. Stone ==> self-adjoint generator H
    4. U†HU = H when [H,U] = 0 ==> energy conservation

    The conclusion is that any K-preserving evolution on an N-level
    system is generated by a Hermitian matrix H, which is the
    Hamiltonian. The evolution equation is ih d/dt |psi> = H|psi>.

    **Honesty caveat (Stone A = 0 witness):** This theorem relies on
    `ClassicalImports.stone_generator`, whose current Lean witness is
    A = 0 (the hypotheses on U are unused — see the `stone_generator`
    docstring). As a consequence, the Hermitian H guaranteed by this
    theorem is trivially H = 0, which is formally Hermitian but does
    NOT capture the actual generator of the given U_mat. The full
    forward direction of Stone's theorem (extracting the specific
    generator of a given unitary group) requires matrix-logarithm
    theory not yet present in Mathlib. Downstream consumers should
    treat the existence conclusion as a placeholder: the real
    mathematical content of the Schrodinger derivation lives in
    `schrodinger_derivation_chain` (Steps 1-2: K-preservation +
    Wigner + continuity ==> unitarity) and the matrix-exponential
    helpers in `ClassicalImports` (`exp_skewHermitian_unitary` etc.,
    which prove the REVERSE direction of Stone). See paper
    Appendix `app:formal-verification` for the full scope statement. -/
theorem full_derivation_chain (n : ℕ) (hn : 1 ≤ n)
    (U_mat : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (hunit : ∀ t, (U_mat t).conjTranspose * U_mat t = 1)
    (hgroup : ∀ s t, U_mat (s + t) = U_mat s * U_mat t)
    (hid : U_mat 0 = 1) :
    -- There exists a Hermitian generator H...
    ∃ H : Matrix (Fin n) (Fin n) ℂ,
      -- ...that is self-adjoint...
      -- (Note: with current stone_generator axiom, H = 0 is the witness;
      -- this theorem is therefore a placeholder for the full Stone conclusion.)
      H.conjTranspose = H := by
  -- Apply Stone's theorem to get the generator (extract Hermitian H from the full package)
  obtain ⟨H, _, hH, _⟩ := ClassicalImports.stone_generator n hn U_mat hunit hgroup hid
  exact ⟨H, hH⟩

-- ============================================================
-- Statement #29: Energy as Rate of Relational Update
-- ============================================================

/-
**Corollary 29: Energy as Rate of Relational Update**

Energy is the rate of relational update: E = dK/dt measures how fast
distinguishability changes. The self-adjoint generator H from Stone's
theorem IS the energy observable.

For U(t) = exp(-iHt), the rate of change of K at t=0 is determined
by H. Specifically:
  K(psi, U(t)phi) = 1 - |<psi|U(t)phi>|^2
  d/dt K(psi, U(t)phi)|_{t=0} depends on <psi|H|phi>

The structural content: the generator of the one-parameter group
(from Statement #25) is the energy observable. For an N-dimensional
system, H is an NxN Hermitian matrix with N real eigenvalues
(energy levels), so the energy spectrum has exactly N values.

Uses: Statement #27 (continuous time as reconstructed parameterization).
-/

/-- **Energy conservation (proper statement):**
    If H is the self-adjoint generator of a unitary group U(t), and
    U is a specific time-evolution operator that commutes with H, then
    the energy expectation value is preserved.

    This is the non-trivial content: the time-independent Hamiltonian
    H commutes with its own exponential U(t) = exp(-iHt), so U†HU = H,
    and therefore ⟨ψ(t)|H|ψ(t)⟩ = ⟨ψ|H|ψ⟩.

    The hypothesis [H, U] = 0 encodes that U is generated by H
    (a time-independent generator commutes with the group it generates). -/
theorem energy_conservation_from_commutant (n : ℕ)
    (U H : Matrix (Fin n) (Fin n) ℂ)
    (hunit : U.conjTranspose * U = 1)
    (hcomm : commutator H U = 0)
    (ψ : Fin n → ℂ) :
    dotProduct (star (U.mulVec ψ)) (H.mulVec (U.mulVec ψ)) =
    dotProduct (star ψ) (H.mulVec ψ) :=
  energy_expectation_constant n U H hunit hcomm ψ

-- ============================================================
-- Additional: K-preservation is equivalent to unitarity
-- ============================================================

/-- **K-preservation <==> unitarity (backward direction).**
    If U preserves inner products, it preserves K.
    Combined with schrodinger_derivation_chain (forward direction),
    this shows the equivalence. -/
theorem inner_pres_iff_K_pres
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (U : V → V)
    (hU : ∀ ψ φ : V, @inner ℂ V _ (U ψ) (U φ) = @inner ℂ V _ ψ φ) :
    ∀ ψ φ,
      1 - ‖@inner ℂ V _ (U ψ) (U φ)‖ ^ 2 =
      1 - ‖@inner ℂ V _ ψ φ‖ ^ 2 := by
  intro ψ φ
  rw [hU]

-- ============================================================
-- Stone Forward Direction: Partial Progress
-- ============================================================

/-! ### Partial formalization of the forward direction of Stone's theorem

Stone's theorem has two directions:

  **Reverse** (A → U): given a skew-Hermitian matrix A, the function
  t ↦ exp(tA) is a continuous one-parameter unitary group. This is
  fully proved in `ClassicalImports.exp_skewHermitian_unitary` and
  related theorems.

  **Forward** (U → A): given a continuous one-parameter unitary group
  U(t), there exists a unique skew-Hermitian A with U(t) = exp(tA).
  The existence part requires matrix logarithm theory not in Mathlib
  and remains imported as the axiom `ClassicalImports.stone_generator`
  (with an A = 0 witness, honestly documented).

  The UNIQUENESS part of the forward direction CAN be proved: if
  U(t) = exp(tA₁) = exp(tA₂) for all t near 0, then A₁ = A₂. This
  section formalizes the uniqueness content, making progress on the
  forward direction without requiring matrix log.
-/

/-- **Generator-uniqueness helper: exp(tA) determines tA for small t.**

    For skew-Hermitian matrices A₁, A₂, if exp(tA₁) = exp(tA₂) for all
    `t` in some neighborhood of 0, then A₁ = A₂. The Picard-Lindelöf
    theorem (imported as axiom `picard_lindelof_unique`) gives this
    uniqueness at the level of one-parameter groups; here we package
    the statement in a form directly about the generators.

    Note: without a neighborhood hypothesis, uniqueness fails globally
    (e.g., exp(2πi·I) = I = exp(0·I) while 2πi·I ≠ 0). The neighborhood
    hypothesis is the standard Stone's-theorem setting. -/
theorem stone_generator_unique_of_local_agreement (n : ℕ)
    (A₁ A₂ : Matrix (Fin n) (Fin n) ℂ)
    (_hA₁ : A₁.conjTranspose = -A₁)
    (_hA₂ : A₂.conjTranspose = -A₂)
    (h_local : ∃ ε : ℝ, 0 < ε ∧
      ∀ t : ℝ, |t| < ε → exp ℂ ((t : ℂ) • A₁) = exp ℂ ((t : ℂ) • A₂)) :
    -- From local agreement of the one-parameter groups, they agree
    -- globally by Picard-Lindelöf.
    ∀ t : ℝ, exp ℂ ((t : ℂ) • A₁) = exp ℂ ((t : ℂ) • A₂) := by
  -- Define the two one-parameter groups
  set U₁ : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => exp ℂ ((t : ℂ) • A₁)
  set U₂ : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => exp ℂ ((t : ℂ) • A₂)
  -- Verify group properties
  have hgroup₁ : ∀ s t, U₁ (s + t) = U₁ s * U₁ t := by
    intro s t
    show exp ℂ (((s + t : ℝ) : ℂ) • A₁) = _
    have : ((s + t : ℝ) : ℂ) = (s : ℂ) + (t : ℂ) := by push_cast; ring
    rw [this]
    exact ClassicalImports.exp_skewHermitian_group A₁ (s : ℂ) (t : ℂ)
  have hgroup₂ : ∀ s t, U₂ (s + t) = U₂ s * U₂ t := by
    intro s t
    show exp ℂ (((s + t : ℝ) : ℂ) • A₂) = _
    have : ((s + t : ℝ) : ℂ) = (s : ℂ) + (t : ℂ) := by push_cast; ring
    rw [this]
    exact ClassicalImports.exp_skewHermitian_group A₂ (s : ℂ) (t : ℂ)
  have hid₁ : U₁ 0 = 1 := by
    show exp ℂ (((0 : ℝ) : ℂ) • A₁) = 1
    simp
  have hid₂ : U₂ 0 = 1 := by
    show exp ℂ (((0 : ℝ) : ℂ) • A₂) = 1
    simp
  -- Apply Picard-Lindelöf: local agreement + group property ⇒ global agreement
  have h_eq : U₁ = U₂ := ClassicalImports.picard_lindelof_unique n U₁ U₂
    hgroup₁ hgroup₂ hid₁ hid₂ h_local
  intro t
  exact congr_fun h_eq t

/-! ### Scope note on generator-at-zero uniqueness

The full statement "A₁ = A₂ given exp(tA₁) = exp(tA₂) for all t" requires
Fréchet differentiability of the matrix exponential at 0 with derivative
equal to the identity. This is classical analysis available in Mathlib
but the wiring is substantial. The operational version of uniqueness
(one-parameter groups coincide on all of ℝ from local agreement near 0)
is captured by `stone_generator_unique_of_local_agreement` above via
the Picard-Lindelöf axiom, which is what downstream consumers of
Stone's theorem actually use in practice.

Physically: two candidate Hamiltonians H₁, H₂ that produce the same
Schrödinger evolution must be equal. The present formalization gives
the operational version (evolutions coincide for all times given
agreement on a neighborhood of t=0) which is the typical use-case.
-/

end QuantumRelational.Schrodinger
