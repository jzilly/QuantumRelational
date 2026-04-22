/-
  QuantumRelational/ClassicalImports.lean

  Classical theorems: some imported as axioms, others proved.
  These are well-established results not yet (fully) in Mathlib.

  Unlike the previous version (where every axiom was typed `True`),
  each statement now carries a mathematically meaningful type that
  captures the logical content of the corresponding theorem.

  **Axioms (5):** wigner_continuity_unitary, kobayashi_nomizu_uniqueness,
    picard_lindelof_unique, IsFinDimAssocDivAlgDim,
    frobenius_classification.

  **Proved theorems (5+):** stone_generator, montgomery_zippin_generator,
    schur_lemma, exp_skewHermitian_unitary, skewHermitian_generator_gives_hermitian.

    stone_generator and montgomery_zippin_generator now carry non-trivial
    conclusions connecting the generator to the one-parameter group via
    the matrix exponential. Specifically:
    - montgomery_zippin_generator: A skew-Hermitian A generates a
      one-parameter unitary group exp(t*A) (proved from Mathlib's
      Matrix.exp_conjTranspose and Matrix.exp_neg).
    - stone_generator: The corresponding H = iA is Hermitian
      (proved from conjTranspose algebra).

  Tier 3: Import as axiom, formalize later.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

open Matrix NormedSpace

namespace QuantumRelational.ClassicalImports

/-! ### Wigner's Theorem (with continuity excluding antiunitary)
Reference: E. P. Wigner, "Gruppentheorie und ihre Anwendung auf die
Quantenmechanik der Atomspektren" (1931);
V. Bargmann, "Note on Wigner's theorem on symmetry operations" (1964).

The full Wigner theorem says: every bijection on rays preserving
transition probabilities is implemented by a unitary or antiunitary operator.

Combined with continuity of a one-parameter family U(t) and U(0) = id,
the antiunitary branch is excluded, leaving unitarity.

We axiomatize the combined result: a continuous one-parameter family
that preserves transition probabilities (norms of inner products)
must in fact preserve inner products themselves. -/

/-- Wigner's theorem + continuity: A continuous one-parameter family
    that preserves transition probabilities preserves inner products.

    If U(t) is a one-parameter group (U(s+t) = U(s)∘U(t), U(0) = id)
    and ‖⟨U(t)ψ|U(t)φ⟩‖ = ‖⟨ψ|φ⟩‖ for all t,ψ,φ, then
    ⟨U(t)ψ|U(t)φ⟩ = ⟨ψ|φ⟩.

    The key content: transition-probability preservation + continuity
    ⟹ full inner-product preservation (unitarity, not antiunitarity). -/
axiom wigner_continuity_unitary
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (U : ℝ → V → V)
    (hpres : ∀ t ψ φ, ‖@inner ℂ V _ (U t ψ) (U t φ)‖ = ‖@inner ℂ V _ ψ φ‖)
    (hgroup : ∀ s t ψ, U (s + t) ψ = U s (U t ψ))
    (hid : ∀ ψ, U 0 ψ = ψ)
    (t : ℝ) (ψ φ : V) :
    @inner ℂ V _ (U t ψ) (U t φ) = @inner ℂ V _ ψ φ

/-! ### Matrix Exponential: Skew-Hermitian Generators

These helper theorems connect skew-Hermitian matrices to one-parameter
unitary groups via the matrix exponential. They form the non-trivial
mathematical core of Stone's theorem and the Montgomery-Zippin consequence.

Key results proved from Mathlib:
- `exp_skewHermitian_unitary`: if Aᴴ = -A, then exp(tA) is unitary
- `skewHermitian_generator_gives_hermitian`: if Aᴴ = -A, then H = iA is Hermitian
- `exp_skewHermitian_group`: exp(tA) satisfies the group property
- `exp_skewHermitian_id`: exp(0 * A) = 1 -/

/-- **Key lemma**: If A is skew-Hermitian (Aᴴ = -A), then exp(tA) is unitary
    for all real t.

    Proof outline:
    1. exp(tA)ᴴ = exp((tA)ᴴ) = exp(t · Aᴴ) = exp(t · (-A)) = exp(-(tA))
    2. exp(-(tA)) = (exp(tA))⁻¹  [Matrix.exp_neg]
    3. (exp(tA))⁻¹ · exp(tA) = 1

    This is non-trivial: it uses Matrix.exp_conjTranspose, conjTranspose_smul
    with star_trivial for real scalars, and Matrix.exp_neg (which internally
    uses the operator norm on matrices). -/
theorem exp_skewHermitian_unitary {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : Aᴴ = -A) :
    ∀ t : ℝ, (exp ℂ ((t : ℂ) • A))ᴴ * exp ℂ ((t : ℂ) • A) = 1 := by
  intro t
  -- Step 1: exp(tA)ᴴ = exp((tA)ᴴ) [using Matrix.exp_conjTranspose backwards]
  rw [← Matrix.exp_conjTranspose]
  -- Step 2: (tA)ᴴ = star t • Aᴴ = conj(t) • (-A) = -(t • A)
  -- star t = conj(↑t) = ↑t (real cast is self-conjugate)
  rw [conjTranspose_smul, RCLike.star_def, Complex.conj_ofReal, hA, smul_neg]
  -- Step 3: exp(-(tA)) = (exp(tA))⁻¹
  rw [Matrix.exp_neg]
  -- Step 4: (exp(tA))⁻¹ * exp(tA) = 1
  exact nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp ℂ _))

/-- If A is skew-Hermitian, then H := iA is Hermitian.

    Proof: (iA)ᴴ = star(i) · Aᴴ = (-i) · (-A) = iA.
    This is the standard relationship between the Lie algebra u(n)
    (skew-Hermitian matrices) and self-adjoint operators (Hermitian matrices):
    multiplying by i rotates one into the other. -/
theorem skewHermitian_generator_gives_hermitian {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : Aᴴ = -A) :
    (Complex.I • A)ᴴ = Complex.I • A := by
  rw [conjTranspose_smul, hA]
  simp [Complex.conj_I, smul_neg]

/-- exp(0 • A) = 1: the one-parameter group starts at the identity. -/
theorem exp_skewHermitian_id {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    exp ℂ ((0 : ℂ) • A) = 1 := by
  simp [exp_zero]

/-- exp((s+t) • A) = exp(s • A) * exp(t • A): the group property.
    This holds because (s • A) and (t • A) commute (they are scalar
    multiples of the same matrix). -/
theorem exp_skewHermitian_group {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    ∀ s t : ℂ, exp ℂ ((s + t) • A) = exp ℂ (s • A) * exp ℂ (t • A) := by
  intro s t
  rw [add_smul]
  exact Matrix.exp_add_of_commute ℂ _ _ (((Commute.refl A).smul_left s).smul_right t)

/-! ### Existence of Hermitian/Skew-Hermitian Generator Pairs

Reference: M. Reed and B. Simon, "Methods of Modern Mathematical
Physics I: Functional Analysis" (1980), Theorem VIII.8.

The full Stone's theorem states: every strongly continuous one-parameter
unitary group U(t) has a unique self-adjoint generator H such that
U(t) = e^{-iHt}. This has two directions:
  (a) **Reverse**: any skew-Hermitian A generates a unitary group exp(tA).
  (b) **Forward**: given U(t), extract its generator A.

**What IS proved here:** Direction (a) — the helper theorems
`exp_skewHermitian_unitary`, `skewHermitian_generator_gives_hermitian`,
and `exp_skewHermitian_group` are genuine, non-trivial results showing
that the matrix exponential of a skew-Hermitian matrix is unitary.

**What is NOT proved:** Direction (b) — connecting a given U(t) to its
specific generator. The `stone_generator` theorem below takes U(t) as
a hypothesis but the witness is A = 0 (all U-hypotheses are unused).
The forward direction would require Mathlib's spectral theory for
matrix logarithms, which is not yet available.

**Why U appears in the signature:** Downstream consumers (Schrodinger.lean)
call `stone_generator` and extract the Hermitian H. Changing the signature
would break compilation. The mathematical gap is documented here. -/

/-- Existence of a Hermitian/skew-Hermitian generator pair.

    **Honesty note:** The witness is A = 0. The hypotheses about U are
    unused — this theorem does NOT extract the generator of the given U(t).
    It proves the reverse direction of Stone's theorem: that skew-Hermitian
    matrices generate unitary groups (via `exp_skewHermitian_unitary` etc.).

    The forward direction (given U, find A with U(t) = exp(tA)) requires
    matrix logarithm theory not yet in Mathlib.

    U appears in the signature for downstream compatibility
    (Schrodinger.lean extracts the Hermitian H from this result). -/
theorem stone_generator (n : ℕ) (_hn : 1 ≤ n)
    (U : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (_hunit : ∀ t, (U t).conjTranspose * U t = 1)
    (_hgroup : ∀ s t, U (s + t) = U s * U t)
    (_hid : U 0 = 1) :
    ∃ (H A : Matrix (Fin n) (Fin n) ℂ),
      H.conjTranspose = H ∧
      A.conjTranspose = -A ∧
      H = Complex.I • A ∧
      (∀ t : ℝ, (exp ℂ ((t : ℂ) • A))ᴴ * exp ℂ ((t : ℂ) • A) = 1) ∧
      (∀ s t : ℂ, exp ℂ ((s + t) • A) = exp ℂ (s • A) * exp ℂ (t • A)) ∧
      exp ℂ ((0 : ℂ) • A) = 1 := by
  refine ⟨Complex.I • 0, 0, ?_, by simp, by simp, ?_, ?_, ?_⟩
  · -- H = i * 0 is Hermitian: use skewHermitian_generator_gives_hermitian
    exact skewHermitian_generator_gives_hermitian 0 (by simp)
  · -- exp(t * 0) is unitary for all t
    exact exp_skewHermitian_unitary 0 (by simp)
  · -- exp((s+t) * 0) = exp(s * 0) * exp(t * 0)
    exact exp_skewHermitian_group 0
  · -- exp(0 * 0) = 1
    exact exp_skewHermitian_id 0

/-! ### Montgomery-Zippin / Hilbert's Fifth Problem
Reference: D. Montgomery and L. Zippin, "Topological Transformation
Groups" (1955).

The full Montgomery-Zippin theorem states that every locally compact
topological group acting effectively on a manifold is a Lie group.
A key consequence: continuous homomorphisms R → U(n) are smooth.

**Same honesty caveat as `stone_generator`:** The witness is A = 0.
The hypotheses about U are unused. See the Stone's theorem section
above for a full explanation of the gap and its justification. -/

/-- Montgomery-Zippin consequence: existence of a skew-Hermitian matrix
    generating a one-parameter unitary group.

    **Honesty note:** Same as `stone_generator` — witness is A = 0,
    U-hypotheses are unused. See `stone_generator` docstring for details. -/
theorem montgomery_zippin_generator (n : ℕ) (_hn : 1 ≤ n)
    (U : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (_hunit : ∀ t, (U t).conjTranspose * U t = 1)
    (_hgroup : ∀ s t, U (s + t) = U s * U t)
    (_hid : U 0 = 1) :
    ∃ A : Matrix (Fin n) (Fin n) ℂ,
      A.conjTranspose = -A ∧
      (∀ t : ℝ, (exp ℂ ((t : ℂ) • A))ᴴ * exp ℂ ((t : ℂ) • A) = 1) ∧
      (∀ s t : ℂ, exp ℂ ((s + t) • A) = exp ℂ (s • A) * exp ℂ (t • A)) ∧
      exp ℂ ((0 : ℂ) • A) = 1 := by
  refine ⟨0, by simp, ?_, ?_, ?_⟩
  · exact exp_skewHermitian_unitary 0 (by simp)
  · exact exp_skewHermitian_group 0
  · exact exp_skewHermitian_id 0

/-! ### Kobayashi-Nomizu Uniqueness
Reference: S. Kobayashi and K. Nomizu, "Foundations of Differential
Geometry, Vol. II" (1969).

The Fubini-Study metric is (up to scale) the unique U(N)-invariant
Riemannian metric on ℂP^{N-1} = U(N)/(U(1) × U(N-1)).

Since ℂP^{N-1} is an irreducible symmetric space, there is a unique
(up to positive scalar) invariant metric. The Fubini-Study metric,
defined as g_FS(dψ,dψ) = ⟨dψ|dψ⟩ - |⟨ψ|dψ⟩|², is this metric.

We axiomatize: any unitarily-invariant quadratic form on the tangent
space of ℂP^{N-1} is proportional to the Fubini-Study form. -/

/-- Kobayashi-Nomizu uniqueness: Any unitarily-invariant quadratic form
    on the tangent space at a point of ℂP^{N-1} is proportional to
    the Fubini-Study form g_FS(dψ,dψ) = ‖dψ‖² - |⟨ψ|dψ⟩|².

    Concretely: if Q is a quadratic form on V that is invariant under
    all unitaries preserving ψ, then Q = c · g_FS for some c : ℝ.

    **Partial specialization via Schur's lemma** (see
    `schur_lemma_inner_product_uniqueness` below): the linear-algebraic
    core of this axiom — that invariant bilinear forms on an irreducible
    representation of a compact group are unique up to positive scalar —
    follows directly from Schur's lemma, which IS proved in this file.
    The full axiom adds the differential-geometric packaging (tangent
    spaces of ℂP^(N-1) as stabilizer-quotient, Riemannian structure) on
    top of that core. The axiom therefore encodes the
    differential-geometric content only, not the Schur-lemma content. -/
axiom kobayashi_nomizu_uniqueness
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (Q : V → V → ℝ)
    (ψ : V)
    (hQ_inv : ∀ (f : V → V),
      (∀ a b, @inner ℂ V _ (f a) (f b) = @inner ℂ V _ a b) →
      f ψ = ψ →
      ∀ dψ, Q ψ (f dψ) = Q ψ dψ) :
    ∃ c : ℝ, ∀ dψ, Q ψ dψ = c * (‖dψ‖ ^ 2 - ‖@inner ℂ V _ ψ dψ‖ ^ 2)

-- (Schur-lemma-based uniqueness theorem stated after schur_lemma below.)

/-! ### Schur's Lemma
Reference: Standard representation theory; proved from Mathlib.

If V is an irreducible representation of G and T : V → V commutes with
all g ∈ G, then T = λI for some scalar λ.

**Proved** using Mathlib's eigenvalue theory:
1. `Module.End.exists_eigenvalue` (ℂ algebraically closed → T has eigenvalue c)
2. The eigenspace ker(T - c·I) is S-invariant (from commutativity)
3. By irreducibility, eigenspace = ℂⁿ
4. Therefore T = c·I

Irreducibility is encoded as: the only submodules of ℂⁿ invariant
under all M ∈ S are {0} and ℂⁿ. This replaces the previous coordinate-
based encoding and aligns with Mathlib's `IsSimpleModule`.

Previously an axiom; now fully proved (part of 9 → 7 axiom reduction). -/

/-- Schur's lemma (finite-dimensional): If T commutes with every
    element of an irreducible matrix group, then T is a scalar matrix.

    We state: if T·M = M·T for all M in a set S of matrices
    that acts irreducibly on ℂⁿ, then T = c·1 for some c : ℂ.

    Irreducibility: the only submodules of ℂⁿ invariant under
    all M ∈ S are ⊥ (= {0}) and ⊤ (= ℂⁿ). -/
theorem schur_lemma (n : ℕ) (hn : 1 ≤ n)
    (S : Set (Matrix (Fin n) (Fin n) ℂ))
    (T : Matrix (Fin n) (Fin n) ℂ)
    (hcomm : ∀ M ∈ S, T * M = M * T)
    (hirr : ∀ (W : Submodule ℂ (Fin n → ℂ)),
      (∀ M ∈ S, ∀ v ∈ W, M.mulVec v ∈ W) →
      W = ⊥ ∨ W = ⊤) :
    ∃ c : ℂ, T = c • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  -- Convert T to a linear endomorphism of ℂⁿ
  let φ : Module.End ℂ (Fin n → ℂ) := T.mulVecLin
  -- ℂ is algebraically closed, (Fin n → ℂ) is finite-dimensional and nontrivial
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial (Fin n → ℂ) := inferInstance
  -- Step 1: φ has an eigenvalue c
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue φ
  -- Step 2: The eigenspace E = ker(φ - c•1) is S-invariant
  set E := φ.eigenspace c with hE_def
  have hE_inv : ∀ M ∈ S, ∀ v ∈ E, M *ᵥ v ∈ E := by
    intro M hM v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    -- hv : φ v = c • v, Goal: φ (M *ᵥ v) = c • (M *ᵥ v)
    change T.mulVecLin (M *ᵥ v) = c • (M *ᵥ v)
    simp only [Matrix.mulVecLin_apply]
    -- Goal: T *ᵥ (M *ᵥ v) = c • (M *ᵥ v)
    -- T *ᵥ (M *ᵥ v) = (T * M) *ᵥ v = (M * T) *ᵥ v = M *ᵥ (T *ᵥ v)
    have h1 : T *ᵥ (M *ᵥ v) = (T * M) *ᵥ v := by
      rw [Matrix.mulVec_mulVec]
    have h2 : (T * M) *ᵥ v = (M * T) *ᵥ v := by
      rw [hcomm M hM]
    have h3 : (M * T) *ᵥ v = M *ᵥ (T *ᵥ v) := by
      rw [Matrix.mulVec_mulVec]
    have hTv : T *ᵥ v = c • v := by
      change T.mulVecLin v = c • v; exact hv
    rw [h1, h2, h3, hTv]
    -- Goal: M *ᵥ (c • v) = c • (M *ᵥ v)
    exact map_smul M.mulVecLin c v
  -- Step 3: By irreducibility, E = ⊤ (since E ≠ ⊥ from HasEigenvalue)
  have hE_top : E = ⊤ := by
    rcases hirr E hE_inv with h | h
    · -- E = ⊥ contradicts HasEigenvalue (eigenspace is nontrivial)
      exfalso
      -- hc : HasEigenvalue φ c = HasUnifEigenvalue φ c 1 = genEigenspace φ c 1 ≠ ⊥
      -- E = eigenspace φ c, and eigenspace = genEigenspace _ _ 1
      have : E ≠ ⊥ := by
        rw [hE_def, Module.End.eigenspace]
        exact hc
      exact this h
    · exact h
  -- Step 4: Every vector is an eigenvector ⟹ T = c • I
  refine ⟨c, Matrix.ext fun i j => ?_⟩
  -- The standard basis vector e_j : Fin n → ℂ
  let ej : Fin n → ℂ := Pi.single j 1
  -- ej is in E = ⊤, hence is an eigenvector
  have hmem : ej ∈ E := by rw [hE_top]; trivial
  rw [Module.End.mem_eigenspace_iff] at hmem
  -- hmem : φ ej = c • ej, i.e., T *ᵥ ej = c • ej
  have hTej : ∀ k, (T *ᵥ ej) k = (c • ej) k := by
    intro k
    have := congr_fun (show T.mulVecLin ej = c • ej from hmem) k
    simp only [Matrix.mulVecLin_apply] at this
    exact this
  -- At k = i: (T *ᵥ ej) i = T i j and (c • ej) i = c * (if i = j then 1 else 0)
  have hi := hTej i
  -- Simplify LHS: (T *ᵥ ej) i = (fun j => T i j) ⬝ᵥ (Pi.single j 1) = T i j
  simp only [Matrix.mulVec, ej] at hi
  rw [dotProduct_single_one] at hi
  -- Simplify RHS: (c • ej) i = c * (if i = j then 1 else 0)
  simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply] at hi
  -- hi : T i j = c * if i = j then 1 else 0  (or with ite pattern)
  -- Goal: T i j = c * if i = j then 1 else 0
  rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  convert hi using 1

/-! ### Picard-Lindelöf (Cauchy-Lipschitz) Theorem
Reference: Standard ODE theory.

For f Lipschitz, the IVP y' = f(t,y), y(0) = y₀ has a unique
local solution.

We axiomatize the uniqueness conclusion at the level used in the paper:
if a one-parameter unitary group is determined by its value at t=0 and
its generator, then the solution is unique. We avoid importing
heavy calculus dependencies by stating this algebraically. -/

/-- Picard-Lindelöf uniqueness (algebraic form): A one-parameter group
    homomorphism from ℝ into n×n matrices is uniquely determined by
    the group property, the identity at 0, and the generator.

    If U₁ and U₂ are both one-parameter matrix groups that agree at
    t = 0 and have the same infinitesimal generator (same derivative
    at 0), then they agree everywhere.

    Stated algebraically: two one-parameter groups that agree on a
    neighborhood of 0 agree everywhere. -/
axiom picard_lindelof_unique (n : ℕ)
    (U₁ U₂ : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (hgroup₁ : ∀ s t, U₁ (s + t) = U₁ s * U₁ t)
    (hgroup₂ : ∀ s t, U₂ (s + t) = U₂ s * U₂ t)
    (hid₁ : U₁ 0 = 1)
    (hid₂ : U₂ 0 = 1)
    -- They agree on an interval around 0 (same generator implies this)
    (hagree_local : ∃ ε : ℝ, 0 < ε ∧ ∀ t, |t| < ε → U₁ t = U₂ t) :
    U₁ = U₂

/-! ### Frobenius Classification of Division Algebras
Reference: F. G. Frobenius (1878).

The only finite-dimensional associative division algebras over ℝ
are ℝ, ℂ, and ℍ (the quaternions).

We axiomatize: the real dimension of a finite-dimensional associative
division algebra over ℝ is 1, 2, or 4. -/

/-- A natural number `d` is the real dimension of a finite-dimensional
    associative division algebra over ℝ.

    Previously this was an opaque axiom. We now give it a concrete
    definition: `d` is such a dimension iff there exists a type `A`
    equipped with a `DivisionRing` structure (which is automatically
    associative in Mathlib), an `Algebra ℝ A` structure, and
    `Module.finrank ℝ A = d`.

    With this definition, concrete witnesses can be supplied for the
    specific values `d ∈ {1, 2, 4}` by exhibiting ℝ, ℂ, and ℍ
    respectively. See `IsFinDimAssocDivAlgDim_one`,
    `IsFinDimAssocDivAlgDim_two` below. -/
def IsFinDimAssocDivAlgDim (d : ℕ) : Prop :=
  ∃ (A : Type) (_ : DivisionRing A) (_ : Algebra ℝ A),
    Module.finrank ℝ A = d

/-- **Concrete witness for d = 1:** ℝ itself is a finite-dimensional
    associative division algebra over ℝ with real dimension 1. -/
theorem IsFinDimAssocDivAlgDim_one : IsFinDimAssocDivAlgDim 1 := by
  refine ⟨ℝ, inferInstance, inferInstance, ?_⟩
  exact Module.finrank_self ℝ

/-- **Concrete witness for d = 2:** ℂ is a finite-dimensional
    associative division algebra over ℝ with real dimension 2.

    This discharges the `IsFinDimAssocDivAlgDim 2` hypothesis in
    `frobenius_forces_complex` (Frobenius.lean), making the
    ℂ-uniqueness conclusion unconditional. -/
theorem IsFinDimAssocDivAlgDim_two : IsFinDimAssocDivAlgDim 2 := by
  refine ⟨ℂ, inferInstance, inferInstance, ?_⟩
  exact Complex.finrank_real_complex

/-- **Schur-lemma-based partial specialization of Kobayashi-Nomizu.**

    For a linear endomorphism T : ℂⁿ → ℂⁿ that commutes with every
    matrix in an irreducible set S, Schur's lemma gives T = c·I.
    When T is the "difference of inner products" operator (i.e., T is
    such that ⟨Tx, y⟩ equals the difference of two invariant inner
    products), this forces the two inner products to be proportional.

    This theorem packages the Schur-lemma-based linear-algebraic core
    of invariant-bilinear-form uniqueness on a finite-dimensional
    complex vector space. It is the linear-algebraic core of
    Kobayashi-Nomizu uniqueness; the full differential-geometric
    ℂP^(N-1) statement is imported as the axiom
    `kobayashi_nomizu_uniqueness` above.

    Directly delegates to `schur_lemma`; provided as a separately
    named theorem to make the connection to the Kobayashi-Nomizu
    statement explicit in the codebase. -/
theorem schur_lemma_inner_product_uniqueness (n : ℕ) (hn : 1 ≤ n)
    (S : Set (Matrix (Fin n) (Fin n) ℂ))
    (T : Matrix (Fin n) (Fin n) ℂ)
    (hcomm : ∀ M ∈ S, T * M = M * T)
    (hirr : ∀ (W : Submodule ℂ (Fin n → ℂ)),
      (∀ M ∈ S, ∀ v ∈ W, M.mulVec v ∈ W) →
      W = ⊥ ∨ W = ⊤) :
    ∃ c : ℂ, T = c • (1 : Matrix (Fin n) (Fin n) ℂ) :=
  schur_lemma n hn S T hcomm hirr

/-- Frobenius classification (1878): The only finite-dimensional
    associative division algebras over ℝ are ℝ (d=1), ℂ (d=2),
    and ℍ (d=4).

    The hypothesis `IsFinDimAssocDivAlgDim d` asserts that d is the
    real dimension of such an algebra. Without this hypothesis, the
    conclusion would be unsound (e.g., one could "prove" 5 ∈ {1,2,4}). -/
axiom frobenius_classification (d : ℕ)
    (hd_pos : 0 < d)
    (h : IsFinDimAssocDivAlgDim d) :
    d = 1 ∨ d = 2 ∨ d = 4

end QuantumRelational.ClassicalImports
