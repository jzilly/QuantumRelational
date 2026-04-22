/-
  QuantumRelational/Fourier.lean

  **Remark 58: Fourier Orthogonality**

  The discrete Fourier basis vectors |vₖ⟩ = N^{-1/2} Σⱼ e^{2πijk/N} |j⟩
  are orthonormal: ⟨vₖ|vₗ⟩ = δₖₗ.

  This provides an alternative construction of the inner product
  from the kernel K via Fourier analysis on ℤ/Nℤ.

  Tier 1: Uses Mathlib complex exponentials and finite sums.
  Lean status: fully-derived
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.GeomSum

namespace QuantumRelational.Fourier

open Complex Finset

-- Note: fourierCoeff was removed as unused (no theorem in the project references it).

/-- Orthogonality of roots of unity:
    Σⱼ e^{2πi(k-l)j/N} = N δₖₗ

    This is the fundamental discrete Fourier orthogonality relation. -/
theorem roots_of_unity_orthogonality (N : ℕ) (hN : 0 < N) (k l : Fin N) :
    ∑ j : Fin N, exp (2 * Real.pi * I * (k.val - l.val) * j.val / N) =
    if k = l then (N : ℂ) else 0 := by
  split
  case isTrue heq =>
    -- When k = l, each term is exp(0) = 1, and the sum of N ones is N
    subst heq
    simp only [sub_self, mul_zero, zero_mul, zero_div, exp_zero]
    simp [Finset.sum_const, nsmul_eq_mul, mul_one]
  case isFalse hne =>
    -- When k ≠ l, this is a geometric series with ratio ω = exp(2πi(k-l)/N)
    -- Define ω
    set ω : ℂ := exp (2 * ↑Real.pi * I * (↑k.val - ↑l.val) / ↑N) with hω_def
    -- Each summand equals ω ^ j
    have hterm : ∀ j : Fin N,
        exp (2 * ↑Real.pi * I * (↑k.val - ↑l.val) * ↑j.val / ↑N) = ω ^ j.val := by
      intro j
      rw [hω_def, ← exp_nat_mul]
      congr 1
      ring
    simp_rw [hterm]
    -- Show the sum is zero via geometric series argument
    -- Step 1: ω^N = 1 (exp of integer multiple of 2πi)
    have hωN : ω ^ N = 1 := by
      rw [hω_def, ← exp_nat_mul]
      have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hrw : ↑N * (2 * ↑Real.pi * I * (↑k.val - ↑l.val) / ↑N) =
             ↑(↑k.val - ↑l.val : ℤ) * (2 * ↑Real.pi * I) := by
        field_simp
        push_cast
        ring
      rw [hrw]
      exact exp_int_mul_two_pi_mul_I (↑k.val - ↑l.val)
    -- Step 2: ω ≠ 1 (since k ≠ l and both in Fin N)
    -- If ω = exp(θI) = 1, then cos(θ) = 1, so θ = 2πn, giving k = l.
    have hω_ne_one : ω ≠ 1 := by
      -- Define the real angle
      set θ : ℝ := 2 * Real.pi * (↑k.val - ↑l.val) / ↑N with hθ_def
      have hω_eq : ω = exp (↑θ * I) := by
        rw [hω_def, hθ_def]
        congr 1
        push_cast
        ring
      rw [hω_eq]
      intro h
      -- exp(θI) = 1, so cos(θ) + i·sin(θ) = 1
      -- Extract the real part: cos(θ) = 1
      have hre : (exp (↑θ * I)).re = (1 : ℂ).re := congr_arg Complex.re h
      rw [exp_mul_I] at hre
      simp only [Complex.add_re, Complex.mul_re,
                 Complex.I_re, Complex.I_im,
                 mul_zero, mul_one, sub_zero, add_zero, Complex.one_re,
                 cos_ofReal_re, sin_ofReal_im] at hre
      -- cos(θ) = 1 implies θ = n * 2π for some integer n
      rw [Real.cos_eq_one_iff] at hre
      obtain ⟨n, hn⟩ := hre
      -- θ = n * 2π means 2π(k-l)/N = n * 2π, so (k-l)/N = n, hence k-l = nN
      have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      have hpi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
      have hmN : (↑k.val : ℤ) - ↑l.val = n * ↑N := by
        have h1 : (↑k.val - ↑l.val : ℝ) = ↑n * ↑N := by
          have hθ_eq := hn  -- θ = ↑n * (2 * π)
          rw [hθ_def] at hθ_eq
          -- hθ_eq : 2 * π * (↑k.val - ↑l.val) / ↑N = ↑n * (2 * π)
          -- Multiply both sides by N/(2π) to get k - l = n * N
          have h2 : (↑k.val - ↑l.val : ℝ) / ↑N = ↑n := by
            have hpi_ne : (2 : ℝ) * Real.pi ≠ 0 := ne_of_gt hpi_pos
            have : 2 * Real.pi * ((↑k.val - ↑l.val : ℝ) / ↑N) = 2 * Real.pi * ↑n := by
              rw [show 2 * Real.pi * ((↑k.val - ↑l.val : ℝ) / ↑N) =
                       2 * Real.pi * (↑k.val - ↑l.val) / ↑N by ring]
              linarith
            exact mul_left_cancel₀ hpi_ne this
          have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
          rwa [div_eq_iff hNne] at h2
        exact_mod_cast (show ((↑k.val - ↑l.val : ℤ) : ℝ) = ((n * ↑N : ℤ) : ℝ) by
          push_cast at h1 ⊢; linarith)
      have hk_bound : (k.val : ℤ) < N := Int.ofNat_lt.mpr k.isLt
      have hl_bound : (l.val : ℤ) < N := Int.ofNat_lt.mpr l.isLt
      have hn_zero : n = 0 := by
        by_contra hn_ne
        have : n ≤ -1 ∨ 1 ≤ n := by omega
        rcases this with hn_neg | hn_pos
        · have : n * (N : ℤ) ≤ -(N : ℤ) := by nlinarith
          linarith
        · have : (N : ℤ) ≤ n * (N : ℤ) := by nlinarith
          linarith
      rw [hn_zero] at hmN; simp at hmN
      exact hne (Fin.ext (by omega))
    -- Step 3: Use geometric series to show sum = 0
    have hω_sub_ne : ω - 1 ≠ 0 := sub_ne_zero.mpr hω_ne_one
    -- Relate the Fin N sum to a Finset.range N sum
    have hsum_eq : (∑ j : Fin N, ω ^ j.val) = ∑ i ∈ Finset.range N, ω ^ i :=
      Fin.sum_univ_eq_sum_range (fun i => ω ^ i) N
    rw [hsum_eq]
    -- Apply geometric series identity: (∑ ω^i) * (ω - 1) = ω^N - 1 = 0
    have hgeo : (∑ i ∈ Finset.range N, ω ^ i) * (ω - 1) = ω ^ N - 1 :=
      geom_sum_mul ω N
    rw [hωN, sub_self] at hgeo
    exact (mul_eq_zero.mp hgeo).resolve_right hω_sub_ne

/-- Fourier modes are orthonormal:
    ⟨vₖ|vₗ⟩ = (1/N) Σⱼ e^{2πi(k-l)j/N} = δₖₗ

    The normalized discrete Fourier inner product reduces to
    the roots-of-unity orthogonality scaled by 1/N. -/
theorem fourier_orthonormal (N : ℕ) (hN : 0 < N) (k l : Fin N) :
    (1 / (N : ℂ)) * ∑ j : Fin N,
      exp (2 * Real.pi * I * (k.val - l.val) * j.val / N) =
    if k = l then 1 else 0 := by
  rw [roots_of_unity_orthogonality N hN k l]
  split
  case isTrue heq =>
    -- k = l: (1/N) * N = 1
    have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
  case isFalse hne =>
    -- k ≠ l: (1/N) * 0 = 0
    simp

end QuantumRelational.Fourier
