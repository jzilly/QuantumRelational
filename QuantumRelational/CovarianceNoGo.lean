/-
  QuantumRelational/CovarianceNoGo.lean

  **The Covariance No-Go theorem** (paper Theorem `thm:covariance-nogo`,
  revision 2026-07-01).

  A deterministic outcome assignment covariant under the derived
  symmetries is impossible: the cyclic automorphism π fixes the uniform
  state f₀ while permuting the basis outcomes freely, so covariance at
  g = π forces the outcome at f₀ to be a fixed point of a fixed-point-free
  permutation.

  This is the framework's primary, symmetry-only exclusion of determinism;
  the storage form (paper Theorem `thm:capacity-halting`, mechanized as
  arithmetic in `CapacityHalting.lean`) is its quantitative companion.

  Mechanization shape: the abstract kernel of the argument. The model
  supplies the two structural inputs as hypotheses:
    * a state `f0` fixed by the automorphism `g` (in the model: the
      uniform superposition, fixed as a ray by the cyclic permutation,
      Lemma `lem:sheaf-complex`(a));
    * covariance of the outcome map along `g`, with `g` acting on the
      outcome labels of the fixed basis as the free N-cycle
      (`finRotate`), which is how the cyclic automorphism of paper
      Theorem `thm:dynamics-derived` acts on its basis.
  The conclusion is `False`: no such outcome map exists.
-/
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.GroupTheory.Perm.Cycle.Concrete

namespace QuantumRelational
namespace CovarianceNoGo

/-- The `N`-cycle `finRotate` has no fixed point for `N ≥ 2`. -/
theorem finRotate_ne_self {n : ℕ} (k : Fin (n + 2)) :
    finRotate (n + 2) k ≠ k := by
  rw [finRotate_succ_apply]
  intro h
  have h1 : k + 1 = k + 0 := by rw [add_zero]; exact h
  have h0 : (1 : Fin (n + 2)) = 0 := add_left_cancel h1
  have hval : ((1 : Fin (n + 2)) : ℕ) = ((0 : Fin (n + 2)) : ℕ) :=
    congrArg Fin.val h0
  simp at hval

/-- **Covariance No-Go** (paper Theorem `thm:covariance-nogo`). Let
`out : α → Fin (n+2)` be a deterministic outcome assignment for a fixed
basis with `N = n + 2 ≥ 2` outcomes, let `g : α ≃ α` be a symmetry
fixing the state `f0` and acting on the outcome labels as the free
`N`-cycle, and suppose `out` is covariant along `g`. Then `False`. -/
theorem covariance_nogo {α : Type*} {n : ℕ}
    (out : α → Fin (n + 2)) (g : α ≃ α) (f0 : α)
    (hfix : g f0 = f0)
    (hcov : ∀ ψ : α, out (g ψ) = finRotate (n + 2) (out ψ)) : False := by
  have h := hcov f0
  rw [hfix] at h
  exact finRotate_ne_self (out f0) h.symm

/-- Packaging: no covariant deterministic outcome assignment exists on
any space carrying a symmetry with a fixed state that cycles the
outcomes. (The intended model satisfies the two structural hypotheses
with `f0` the uniform state and `g` the cyclic automorphism.) -/
theorem no_covariant_deterministic_assignment {α : Type*} {n : ℕ}
    (g : α ≃ α) (f0 : α) (hfix : g f0 = f0) :
    ¬ ∃ out : α → Fin (n + 2),
        ∀ ψ : α, out (g ψ) = finRotate (n + 2) (out ψ) := by
  rintro ⟨out, hcov⟩
  exact covariance_nogo out g f0 hfix hcov

end CovarianceNoGo
end QuantumRelational
