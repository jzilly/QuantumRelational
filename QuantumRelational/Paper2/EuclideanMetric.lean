/-
  QuantumRelational/Paper2/EuclideanMetric.lean

  **Paper 2, Theorem 9.2: Norm Equivalence and Euclidean Emergence**

  On ℝ^d, the L¹ and L² norms are equivalent:
    ‖v‖₂ ≤ ‖v‖₁ ≤ √d · ‖v‖₂

  The graph distance on the Cayley graph of ℤ^d with standard generators
  equals the L¹ norm. At macroscopic scales (by the CLT), the L¹ metric
  converges to Euclidean L² geometry. The norm equivalence bounds quantify
  the rate of this convergence.

  **Cross-paper dependency:** Paper 1 provides the finite capacity N and
  the inner product structure (Theorem 52). Paper 2's Theorem 8.2
  (IntegerDimension.lean) establishes d ∈ ℕ. This file shows that
  the resulting ℤ^d lattice metric is equivalent to Euclidean.

  **What we formalize here:**
  1. L¹ norm on ℝ^d: ‖v‖₁ = Σ|v_i|
  2. Squared L² norm: ‖v‖₂² = Σ v_i²
  3. ‖v‖₂² ≤ ‖v‖₁² (each |v_i| ≤ Σ|v_j|, then sum squares)
  4. ‖v‖₁² ≤ d · ‖v‖₂² (Cauchy-Schwarz with constant function 1)
  5. Specific cases: d = 1 (norms equal), d = 3 (factor √3)

  Lean status: fully-derived (0 sorry, 0 axiom)
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Chebyshev

namespace QuantumRelational.Paper2.EuclideanMetric

open Finset

/-! ### Section 1: Norm definitions on ℝ^d -/

/-- The L¹ norm on ℝ^d: sum of absolute values. -/
noncomputable def l1norm (d : ℕ) (v : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, |v i|

/-- The squared L² norm on ℝ^d: sum of squares. -/
noncomputable def l2normSq (d : ℕ) (v : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, (v i) ^ 2

/-- The L¹ norm is non-negative. -/
theorem l1norm_nonneg (d : ℕ) (v : Fin d → ℝ) : 0 ≤ l1norm d v :=
  Finset.sum_nonneg (fun i _ => abs_nonneg (v i))

/-- The squared L² norm is non-negative. -/
theorem l2normSq_nonneg (d : ℕ) (v : Fin d → ℝ) : 0 ≤ l2normSq d v :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (v i))

/-! ### Section 2: ‖v‖₂² ≤ ‖v‖₁² -/

/-- Each |v_i| is at most the L¹ norm (a single term ≤ the sum). -/
theorem abs_le_l1norm (d : ℕ) (v : Fin d → ℝ) (i : Fin d) :
    |v i| ≤ l1norm d v :=
  Finset.single_le_sum (fun j _ => abs_nonneg (v j)) (Finset.mem_univ i)

/-- **Theorem 9.2a (squared form):** ‖v‖₂² ≤ ‖v‖₁².

    Proof: v_i² = |v_i|² ≤ |v_i| · ‖v‖₁ (since |v_i| ≤ ‖v‖₁).
    Summing: ‖v‖₂² = Σ v_i² ≤ Σ |v_i| · ‖v‖₁ = ‖v‖₁ · ‖v‖₁ = ‖v‖₁². -/
theorem l2sq_le_l1sq (d : ℕ) (v : Fin d → ℝ) :
    l2normSq d v ≤ (l1norm d v) ^ 2 := by
  unfold l2normSq l1norm
  -- Step 1: Σ v_i² ≤ Σ (|v_i| · S) where S = Σ|v_j|
  let S := ∑ i : Fin d, |v i|
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => abs_nonneg (v i))
  -- Step 2: Σ (|v_i| · S) = S · S = S²
  calc ∑ i : Fin d, (v i) ^ 2
      = ∑ i : Fin d, |v i| ^ 2 := by
        apply Finset.sum_congr rfl; intro i _; exact (sq_abs _).symm
    _ ≤ ∑ i : Fin d, |v i| * S := by
        apply Finset.sum_le_sum; intro i _
        rw [sq]
        exact mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (fun j _ => abs_nonneg (v j)) (Finset.mem_univ i))
          (abs_nonneg (v i))
    _ = S * S := by rw [← Finset.sum_mul]
    _ = S ^ 2 := (sq S).symm

/-! ### Section 3: ‖v‖₁² ≤ d · ‖v‖₂² (Cauchy-Schwarz) -/

/-- **Theorem 9.2b (squared form):** ‖v‖₁² ≤ d · ‖v‖₂².
    Equivalently, ‖v‖₁ ≤ √d · ‖v‖₂.

    Proof by Cauchy-Schwarz: ‖v‖₁ = Σ 1·|v_i| = ⟨𝟏, |v|⟩
    ≤ ‖𝟏‖ · ‖|v|‖ = √d · ‖v‖₂. Squaring gives ‖v‖₁² ≤ d · ‖v‖₂².

    We use `sq_sum_le_card_mul_sum_sq` (Chebyshev / Cauchy-Schwarz):
    (Σ f i)² ≤ |s| * Σ (f i)² applied with f = |v|. -/
theorem l1sq_le_d_mul_l2sq (d : ℕ) (v : Fin d → ℝ) :
    (l1norm d v) ^ 2 ≤ (d : ℝ) * l2normSq d v := by
  unfold l1norm l2normSq
  -- Apply Chebyshev/Cauchy-Schwarz: (Σ |v_i|)² ≤ #univ * Σ |v_i|²
  have cs := @sq_sum_le_card_mul_sum_sq (Fin d) ℝ _ _ _ _
    Finset.univ (fun i => |v i|)
  simp only [Finset.card_univ, Fintype.card_fin, sq_abs] at cs
  exact cs

/-! ### Section 4: Combined norm equivalence -/

/-- **Theorem 9.2 (combined, squared form):** For all v ∈ ℝ^d:
      ‖v‖₂² ≤ ‖v‖₁² ≤ d · ‖v‖₂²

    This is the squared form of: ‖v‖₂ ≤ ‖v‖₁ ≤ √d · ‖v‖₂.
    The equivalence constant √d shows that the graph (L¹) and
    Euclidean (L²) metrics define the same topology on ℤ^d.

    Physical interpretation: at macroscopic scales (many lattice steps),
    the L¹ graph distance converges to Euclidean distance by the CLT. -/
theorem norm_equivalence (d : ℕ) (v : Fin d → ℝ) :
    l2normSq d v ≤ (l1norm d v) ^ 2 ∧
    (l1norm d v) ^ 2 ≤ (d : ℝ) * l2normSq d v :=
  ⟨l2sq_le_l1sq d v, l1sq_le_d_mul_l2sq d v⟩

/-! ### Section 5: Specific dimensions -/

/-- For d = 1, the equivalence constant is 1: ‖v‖₁² ≤ 1 · ‖v‖₂².
    The norms coincide on ℝ¹. -/
theorem dim_one_equivalence (v : Fin 1 → ℝ) :
    (l1norm 1 v) ^ 2 ≤ (1 : ℝ) * l2normSq 1 v := by
  have := l1sq_le_d_mul_l2sq 1 v
  simp at this
  linarith

/-- For d = 3 (physical space): ‖v‖₁² ≤ 3 · ‖v‖₂².
    The equivalence factor √3 ≈ 1.73 bounds the deviation between
    graph distance and Euclidean distance. -/
theorem dim_three_equivalence (v : Fin 3 → ℝ) :
    (l1norm 3 v) ^ 2 ≤ (3 : ℝ) * l2normSq 3 v :=
  l1sq_le_d_mul_l2sq 3 v

/-- The L¹ norm of the zero vector is zero. -/
theorem l1norm_zero (d : ℕ) : l1norm d (fun _ => 0) = 0 := by
  simp [l1norm]

/-- The L² squared norm of the zero vector is zero. -/
theorem l2normSq_zero (d : ℕ) : l2normSq d (fun _ => 0) = 0 := by
  simp [l2normSq]

end QuantumRelational.Paper2.EuclideanMetric
