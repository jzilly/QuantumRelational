/-
  QuantumRelational/Paper2/HomogeneityLaw.lean

  **Paper 2 (revision 2026-07-05): the No Definable Vertex Distinction
  lemma** (paper Lemma `lem:no-definable-distinction`), the rigorous
  half of the Homogeneity of Law principle.

  Earlier drafts derived vertex-transitivity of the interaction graph
  from Paper 1's Permutation Invariance; that argument was circular (a
  specific sparse Hamiltonian breaks the S_M relabeling symmetry by
  construction) and is retired in the 2026-07-05 revision. What
  survives, and is machine-checked here, is the limitative statement:

  * `invariant_constant_on_orbit` (abstract form): on any
    distinguishability space, a predicate invariant under all
    K-automorphisms is constant along any family whose members are
    pairwise connected by K-automorphisms.
  * `permMap` / `permRayEquiv`: every permutation of the standard
    basis index set induces a kernel automorphism of the concrete
    model ℙ ℂ (ℂ^N) (the permutation unitary, descended to rays).
    This is the index-permutation form of the paper's factor-swap
    unitaries: the swap of two elementary tensor factors permutes the
    product basis, so the factor-swap case is an instance.
  * `no_definable_vertex_distinction` (concrete form): any predicate
    on the model invariant under all kernel automorphisms takes the
    same value on all standard-basis rays. No relationally definable
    property singles out a vertex of the interaction graph.

  What is NOT claimed (and is the honest content of the Homogeneity of
  Law principle in the paper): that the law itself cannot distinguish
  vertices. A contingent, non-definable inhomogeneity is logically
  possible; excluding it is the principle's content, exactly parallel
  to Paper 1's treatment of Context Homogeneity.

  Lean status: fully-derived (0 sorry, 0 axiom beyond the standard
  three).
-/
import QuantumRelational.ModelExistence

namespace QuantumRelational
namespace Paper2
namespace HomogeneityLaw

open Complex Projectivization WithLp
open scoped InnerProductSpace ComplexConjugate LinearAlgebra.Projectivization
open QuantumRelational.ModelExistence

/-! ### The abstract limitative lemma -/

/-- **No definable distinction, abstract form**: a predicate invariant
under every K-automorphism is constant along any K-homogeneous family.
The paper's Lemma `lem:no-definable-distinction` follows because
{K,=}-definable predicates are automorphism-invariant (Paper 1, clause
(C1)). -/
theorem invariant_constant_on_orbit {α ι : Type*}
    (ax : DistinguishabilitySpace α) (v : ι → α) (P : α → Prop)
    (hinv : ∀ g : α ≃ α, IsKAutomorphism ax g → ∀ z, P (g z) ↔ P z)
    (htrans : ∀ i j : ι, ∃ g : α ≃ α, IsKAutomorphism ax g ∧ g (v i) = v j)
    (i j : ι) : P (v i) ↔ P (v j) := by
  obtain ⟨g, hgK, hgij⟩ := htrans i j
  rw [← hgij]
  exact (hinv g hgK (v i)).symm

/-! ### Permutation unitaries on the model -/

variable {N : ℕ}

/-- The permutation map on ℂ^N induced by a permutation of the index
set: the permutation unitary. -/
noncomputable def permMap (σ : Equiv.Perm (Fin N)) (v : E N) : E N :=
  toLp 2 (fun k => v (σ.symm k))

theorem permMap_apply (σ : Equiv.Perm (Fin N)) (v : E N) (k : Fin N) :
    permMap σ v k = v (σ.symm k) := rfl

theorem permMap_smul (σ : Equiv.Perm (Fin N)) (a : ℂ) (v : E N) :
    permMap σ (a • v) = a • permMap σ v := by
  ext k
  simp only [permMap_apply, PiLp.smul_apply, smul_eq_mul]

theorem permMap_inv_comp (σ : Equiv.Perm (Fin N)) (v : E N) :
    permMap σ⁻¹ (permMap σ v) = v := by
  ext k
  rw [permMap_apply, permMap_apply]
  simp [Equiv.Perm.inv_def]

theorem permMap_comp_inv (σ : Equiv.Perm (Fin N)) (v : E N) :
    permMap σ (permMap σ⁻¹ v) = v := by
  have h := permMap_inv_comp σ⁻¹ v
  rwa [inv_inv] at h

theorem permMap_zero (σ : Equiv.Perm (Fin N)) :
    permMap σ (0 : E N) = 0 := by
  ext k
  rw [permMap_apply]
  simp

theorem permMap_ne_zero (σ : Equiv.Perm (Fin N)) {v : E N} (hv : v ≠ 0) :
    permMap σ v ≠ 0 := by
  intro h
  apply hv
  have h2 := congrArg (permMap σ⁻¹) h
  rwa [permMap_inv_comp, permMap_zero] at h2

/-- The permutation unitary preserves the inner product (it reindexes
the defining sum). -/
theorem permMap_inner (σ : Equiv.Perm (Fin N)) (u v : E N) :
    ⟪permMap σ u, permMap σ v⟫_ℂ = ⟪u, v⟫_ℂ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  exact Fintype.sum_equiv σ.symm _ _ (fun k => rfl)

theorem permMap_norm_sq (σ : Equiv.Perm (Fin N)) (v : E N) :
    ‖permMap σ v‖ ^ 2 = ‖v‖ ^ 2 := by
  have h1 := inner_self_eq_norm_sq (𝕜 := ℂ) (permMap σ v)
  have h2 := inner_self_eq_norm_sq (𝕜 := ℂ) v
  rw [← h1, ← h2, permMap_inner]

/-- The permutation unitary preserves the Fubini--Study kernel at the
vector level. -/
theorem permMap_Kvec (σ : Equiv.Perm (Fin N)) (u v : E N) :
    Kvec (permMap σ u) (permMap σ v) = Kvec u v := by
  unfold Kvec
  rw [permMap_inner, permMap_norm_sq, permMap_norm_sq]

/-! ### Descent to rays -/

/-- The induced map on rays. -/
noncomputable def permRay (σ : Equiv.Perm (Fin N)) (p : ℙ ℂ (E N)) :
    ℙ ℂ (E N) :=
  Projectivization.mk ℂ (permMap σ p.rep) (permMap_ne_zero σ p.rep_nonzero)

theorem permRay_mk (σ : Equiv.Perm (Fin N)) (v : E N) (hv : v ≠ 0) :
    permRay σ (Projectivization.mk ℂ v hv)
      = Projectivization.mk ℂ (permMap σ v) (permMap_ne_zero σ hv) := by
  unfold permRay
  obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep ℂ v hv
  rw [mk_eq_mk_iff']
  refine ⟨(a : ℂ), ?_⟩
  have hrep : ((a : ℂ)) • v = (Projectivization.mk ℂ v hv).rep := by
    rw [← Units.smul_def]
    exact ha
  rw [← permMap_smul, hrep]

/-- The ray-level permutation is a bijection of the model's state
space. -/
noncomputable def permRayEquiv (σ : Equiv.Perm (Fin N)) :
    ℙ ℂ (E N) ≃ ℙ ℂ (E N) where
  toFun := permRay σ
  invFun := permRay σ⁻¹
  left_inv p := by
    conv_lhs =>
      rw [show p = Projectivization.mk ℂ p.rep p.rep_nonzero from
        (mk_rep p).symm]
    rw [permRay_mk, permRay_mk]
    conv_rhs => rw [← mk_rep p]
    rw [mk_eq_mk_iff']
    exact ⟨1, by rw [one_smul, permMap_inv_comp]⟩
  right_inv p := by
    conv_lhs =>
      rw [show p = Projectivization.mk ℂ p.rep p.rep_nonzero from
        (mk_rep p).symm]
    rw [permRay_mk, permRay_mk]
    conv_rhs => rw [← mk_rep p]
    rw [mk_eq_mk_iff']
    exact ⟨1, by rw [one_smul, permMap_comp_inv]⟩

/-- **Permutation unitaries are kernel automorphisms of the model**:
the concrete mechanism behind the paper's factor-swap argument. -/
theorem permRayEquiv_isKAutomorphism (σ : Equiv.Perm (Fin N)) :
    IsKAutomorphism (model N) (permRayEquiv σ) := by
  intro p q
  show Kray (permRay σ p) (permRay σ q) = Kray p q
  unfold permRay
  rw [Kray_mk, permMap_Kvec]
  rfl

/-! ### Action on the standard-basis rays -/

theorem permMap_single (σ : Equiv.Perm (Fin N)) (k : Fin N) :
    permMap σ (EuclideanSpace.single k (1 : ℂ))
      = EuclideanSpace.single (σ k) (1 : ℂ) := by
  ext j
  rw [permMap_apply, EuclideanSpace.single_apply, EuclideanSpace.single_apply]
  by_cases h : j = σ k
  · have h' : σ.symm j = k := by rw [h, Equiv.symm_apply_apply]
    simp [h']
    exact h
  · have h' : σ.symm j ≠ k := by
      intro hc
      exact h (by rw [← hc, Equiv.apply_symm_apply])
    simp [h, h']

theorem permRayEquiv_basisRay (σ : Equiv.Perm (Fin N)) (k : Fin N) :
    permRayEquiv σ (basisRay N k) = basisRay N (σ k) := by
  show permRay σ (basisRay N k) = basisRay N (σ k)
  unfold basisRay
  rw [permRay_mk, mk_eq_mk_iff']
  exact ⟨1, by rw [one_smul, permMap_single]⟩

/-! ### The concrete limitative theorem -/

/-- **No Definable Vertex Distinction** (paper Lemma
`lem:no-definable-distinction`, concrete form): any predicate on the
model invariant under all kernel automorphisms takes the same value on
all standard-basis rays. The witness for the pair (i, j) is the
permutation unitary of the transposition (i j); the paper's
factor-swap unitaries are the special case in which the index set is a
product and the permutation swaps two factors. Combined with Paper 1's
Definability clause (C1), no {K,=}-definable property singles out a
vertex of the interaction graph; the passage from this limitative
statement to full vertex-transitivity is the (non-theorem) content of
the Homogeneity of Law principle. -/
theorem no_definable_vertex_distinction (P : ℙ ℂ (E N) → Prop)
    (hinv : ∀ g : ℙ ℂ (E N) ≃ ℙ ℂ (E N),
      IsKAutomorphism (model N) g → ∀ z, P (g z) ↔ P z)
    (i j : Fin N) : P (basisRay N i) ↔ P (basisRay N j) := by
  refine invariant_constant_on_orbit (model N) (basisRay N) P hinv ?_ i j
  intro i' j'
  refine ⟨permRayEquiv (Equiv.swap i' j'),
    permRayEquiv_isKAutomorphism _, ?_⟩
  rw [permRayEquiv_basisRay, Equiv.swap_apply_left]

end HomogeneityLaw
end Paper2
end QuantumRelational
