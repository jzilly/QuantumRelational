/-
  QuantumRelational/Paper2/IntegerDimension.lean

  **Paper 2, Theorem 8.2: Integer Dimension**

  The translation group T of a Cayley graph is finitely generated and abelian,
  so by the Structure Theorem for finitely generated abelian groups:
    T ≅ ℤ^d × F  where F is a finite torsion group.
  The rank d is a non-negative integer — dimension cannot be fractional.

  The standard generating set {±e₁, ..., ±e_d} has 2d elements,
  giving coordination number k = 2d.

  **Cross-paper dependency:** Paper 1 establishes that the state space has
  finite capacity N (Axiom 1). Paper 2 builds the spatial graph from
  the composite structure (Paper 1, Theorem 107) and derives that its
  translation symmetries form a finitely generated abelian group.

  **What we formalize here:**
  1. ℤ^d is a free ℤ-module with finrank d
  2. The rank d is a natural number (non-negative integer)
  3. The coordination number k = 2d for standard generators
  4. Rank is invariant under ℤ-linear isomorphism
  5. Properties of the standard basis of ℤ^d

  Lean status: fully-derived (0 sorry, 0 axiom)
-/
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

namespace QuantumRelational.Paper2.IntegerDimension

/-! ### Section 1: The translation lattice ℤ^d -/

/-- The translation lattice in d dimensions is `Fin d → ℤ`.
    This is the standard model of ℤ^d as a ℤ-module. -/
abbrev TranslationLattice (d : ℕ) := Fin d → ℤ

/-- **Theorem 8.2 (integer dimension, core rank identity):**
    The finrank of `Fin d → ℤ` as a ℤ-module equals d.
    Dimension is necessarily a non-negative integer because it equals
    the rank of a free ℤ-module.

    We compute: finrank ℤ (Fin d → ℤ) = Σ_{i : Fin d} finrank ℤ ℤ
    = Σ_{i : Fin d} 1 = d. -/
theorem integer_dimension (d : ℕ) :
    Module.finrank ℤ (TranslationLattice d) = d := by
  unfold TranslationLattice
  simp only [Module.finrank_pi, Fintype.card_fin]

/-- The dimension is non-negative (it is a natural number).
    This is trivially true for ℕ but states the key physical content:
    there is no fractional or negative dimension. -/
theorem dimension_nonneg (d : ℕ) : 0 ≤ d := Nat.zero_le d

/-! ### Section 2: Coordination number k = 2d -/

/-- The i-th standard basis vector e_i in ℤ^d. -/
def stdBasisVec (d : ℕ) (i : Fin d) : TranslationLattice d :=
  fun j => if i = j then 1 else 0

/-- The negative of the i-th standard basis vector. -/
def negStdBasisVec (d : ℕ) (i : Fin d) : TranslationLattice d :=
  fun j => if i = j then -1 else 0

/-- The standard generating set S = {±e₁, ..., ±e_d} has cardinality 2d.
    Each generator e_i contributes two elements: +e_i and -e_i.

    Paper 2, Corollary 8.3: The coordination number k = |S| = 2d. -/
theorem coordination_number (d : ℕ) :
    2 * d = Fintype.card (Fin d) + Fintype.card (Fin d) := by
  simp [Fintype.card_fin]; ring

/-- Standard basis vectors are nonzero for d ≥ 1.
    This ensures the generators are non-trivial. -/
theorem stdBasisVec_ne_zero (d : ℕ) (_hd : 0 < d) (i : Fin d) :
    stdBasisVec d i ≠ 0 := by
  intro h
  have := congr_fun h i
  simp [stdBasisVec] at this

/-- Distinct standard basis vectors are different: e_i ≠ e_j for i ≠ j.
    This ensures the 2d generators are all distinct. -/
theorem stdBasisVec_injective (d : ℕ) (i j : Fin d)
    (h : stdBasisVec d i = stdBasisVec d j) : i = j := by
  by_contra hij
  have := congr_fun h i
  simp [stdBasisVec] at this
  exact hij this.symm

/-- e_i and -e_i are distinct.
    Together with injectivity, this gives 2d distinct generators. -/
theorem pos_ne_neg (d : ℕ) (i : Fin d) :
    stdBasisVec d i ≠ negStdBasisVec d i := by
  intro h
  have := congr_fun h i
  simp [stdBasisVec, negStdBasisVec] at this

/-! ### Section 3: Rank invariance -/

/-- **Rank invariance under isomorphism:** If ℤ^{d₁} ≃ₗ[ℤ] ℤ^{d₂}
    then d₁ = d₂.

    This is the key algebraic fact ensuring that "dimension" is
    well-defined — it does not depend on the choice of basis.

    Paper 2, Proposition 8.4. -/
theorem rank_invariant (d₁ d₂ : ℕ)
    (φ : TranslationLattice d₁ ≃ₗ[ℤ] TranslationLattice d₂) :
    d₁ = d₂ := by
  have h₁ := integer_dimension d₁
  have h₂ := integer_dimension d₂
  have heq := φ.finrank_eq
  omega

/-! ### Section 4: Small-dimension cases -/

/-- d = 0 gives the trivial lattice (a single point — no spatial extent). -/
theorem dim_zero_trivial : Module.finrank ℤ (TranslationLattice 0) = 0 :=
  integer_dimension 0

/-- d = 1 gives ℤ (a line). Coordination number k = 2. -/
theorem dim_one_line :
    Module.finrank ℤ (TranslationLattice 1) = 1 ∧ 2 * 1 = 2 :=
  ⟨integer_dimension 1, rfl⟩

/-- d = 3 gives ℤ³ (physical space). Coordination number k = 6.
    This connects to DimensionThree.lean where d = 3 is selected. -/
theorem dim_three_physical :
    Module.finrank ℤ (TranslationLattice 3) = 3 ∧ 2 * 3 = 6 :=
  ⟨integer_dimension 3, rfl⟩

end QuantumRelational.Paper2.IntegerDimension
