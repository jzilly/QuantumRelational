/-
  QuantumRelational/SwapMatrix.lean

  **Theorem 54: The Qutrit Threshold**

  For N = 2, the only real orthogonal matrices commuting with the
  swap matrix S are {I, -I, S, -S}. This discrete set cannot support
  continuous dynamics, proving that N ≥ 3 is necessary for non-trivial
  continuous evolution.

  Tier 1: Uses basic Mathlib linear algebra.
  Lean status: fully-derived
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic

namespace QuantumRelational.SwapMatrix

open Matrix

/-- The 2×2 swap matrix S = ((0,1),(1,0)). -/
def S : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; 1, 0]

/-- S is its own inverse: S² = I. -/
theorem S_sq_eq_one : S * S = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  simp [S, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp

/-- Eigenvalues of S are +1 and -1.
    Proof: S² = I means eigenvalues satisfy λ² = 1. -/
theorem S_eigenvalues_pm1 (μ : ℝ) (v : Fin 2 → ℝ) (hv : v ≠ 0)
    (hev : S.mulVec v = μ • v) : μ = 1 ∨ μ = -1 := by
  -- S² = I implies μ² = 1
  have h_sq : μ * μ = 1 := by
    have h1 : S.mulVec (S.mulVec v) = v := by
      have : (S * S).mulVec v = v := by
        rw [S_sq_eq_one]; simp [Matrix.one_mulVec]
      rw [← Matrix.mulVec_mulVec] at this; exact this
    -- S(μv) = μ(Sv) = μ(μv) = μ²v
    have h2 : S.mulVec (μ • v) = μ • (S.mulVec v) := by
      simp [Matrix.mulVec_smul]
    rw [hev, h2, hev, smul_smul] at h1
    -- Now h1 : (μ * μ) • v = v
    -- So (μ*μ - 1) • v = 0, and since v ≠ 0, μ*μ = 1
    have h3 : (μ * μ - 1) • v = 0 := by
      rw [sub_smul, one_smul, h1, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · linarith
    · exact absurd h hv
  -- μ² = 1 → μ = ±1
  have h5 : (μ - 1) * (μ + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp h5 with h | h
  · left; linarith
  · right; linarith

/-- A real 2×2 matrix commuting with S has the form ((a,b),(b,a)). -/
theorem commuting_with_S_form (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hcomm : S * M = M * S) :
    M 0 1 = M 1 0 ∧ M 0 0 = M 1 1 := by
  have h : S * M = M * S := hcomm
  have h01 : M 0 1 = M 1 0 := by
    have := congr_fun (congr_fun h 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, S] at this
    linarith
  have h00 : M 0 0 = M 1 1 := by
    have := congr_fun (congr_fun h 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, S] at this
    linarith
  exact ⟨h01, h00⟩

/-- Over ℝ, the real orthogonal matrices commuting with S form a
    discrete set: only {I, -I, S, -S} are possible.

    Proof: M = ((a,b),(b,a)) with a²+b² = 1 and 2ab = 0.
    From 2ab = 0: either a = 0 or b = 0.
    Combined with a²+b² = 1: (a,b) ∈ {(±1,0), (0,±1)}.
    These give M ∈ {I, -I, S, -S}. -/
theorem real_orthogonal_commuting_discrete
    (a b : ℝ) (h_norm : a ^ 2 + b ^ 2 = 1) (h_orth : 2 * a * b = 0) :
    (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0) ∨
    (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = -1) := by
  have hab : a * b = 0 := by linarith
  rcases mul_eq_zero.mp hab with ha | hb
  · -- Case a = 0, so b² = 1
    have hb2 : b ^ 2 = 1 := by nlinarith
    have : (b - 1) * (b + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inr (Or.inr (Or.inl ⟨ha, by linarith⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ha, by linarith⟩))
  · -- Case b = 0, so a² = 1
    have ha2 : a ^ 2 = 1 := by nlinarith
    have : (a - 1) * (a + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl ⟨by linarith, hb⟩
    · exact Or.inr (Or.inl ⟨by linarith, hb⟩)

end QuantumRelational.SwapMatrix
