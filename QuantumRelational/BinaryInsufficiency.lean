/-
  QuantumRelational/BinaryInsufficiency.lean

  **Binary Insufficiency: the machine-checked counterexample**
  (paper Theorem `thm:binary-insufficiency`, revision 2026-07-01).

  In ℂ³ take the four vectors (Gaussian-integer entries, exact arithmetic)

      x = (1, -1+2i, 0),  y = (1, 1, 2),  z = (1, 0, 0),  w = (1, 1, 0),

  with ‖x‖² = ‖y‖² = 6, ‖z‖² = 1, ‖w‖² = 2. Then:

  1. `pairwise_overlaps_match`: the swap σ : x ↔ y fixing z, w preserves
     every pairwise projective overlap, hence every pairwise K-value on
     the configuration {x, y, z, w}:
         |⟨x|z⟩|² = |⟨y|z⟩|² = 1  and  |⟨x|w⟩|² = |⟨y|w⟩|² = 4,
     with matching norms, so K(x,z) = K(y,z) = 5/6 and
     K(x,w) = K(y,w) = 2/3.

  2. `no_unitary_extension` / `no_antiunitary_extension`: no inner-product
     preserving map (unitary case) and no inner-product conjugating map
     (antiunitary case) fixes the rays of z and w while sending the ray
     of x to the ray of y. The obstruction is the Bargmann product:
         ⟨x|z⟩⟨z|w⟩⟨w|x⟩ = 2i   but   ⟨y|z⟩⟨z|w⟩⟨w|y⟩ = 2,
     and unitaries preserve this product while antiunitaries conjugate
     it; a positive-real scalar mismatch (from the ray phases) cannot
     turn 2 into ±2i.

  By Wigner's theorem in Uhlhorn's form (paper import, cited in the
  paper's proof), every automorphism of (ℂP², K) is induced by a unitary
  or an antiunitary map, so 1 + 2 together refute the blanket Structural
  Leibniz clause in the intended model: σ is a pairwise K-symmetry of a
  finite configuration with no global extension. The context-restricted
  clause (C3) of `SRCv2.lean` is the corrected residue. Note the anchor
  {z, w} here is NOT a context: ⟨z|w⟩ = 1 ≠ 0.

  The Wigner step itself is the only part not mechanized here; the two
  obstruction theorems below are complete and sorry-free.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination

namespace QuantumRelational
namespace BinaryInsufficiency

open Complex

/-- The (unnormalized) sesquilinear inner product on ℂ³, conjugate-linear
in the first slot: `ip u v = ∑ conj(uᵢ) vᵢ`. Rays do not require unit
representatives; all statements below are phrased projectively. -/
def ip (u v : Fin 3 → ℂ) : ℂ := ∑ i, (starRingEnd ℂ) (u i) * v i

/-- x = (1, -1+2i, 0). -/
def xv : Fin 3 → ℂ := ![1, -1 + 2 * I, 0]
/-- y = (1, 1, 2). -/
def yv : Fin 3 → ℂ := ![1, 1, 2]
/-- z = (1, 0, 0). -/
def zv : Fin 3 → ℂ := ![1, 0, 0]
/-- w = (1, 1, 0). -/
def wv : Fin 3 → ℂ := ![1, 1, 0]

/-! ### Scalar behaviour of `ip` -/

theorem ip_smul_left (s : ℂ) (u v : Fin 3 → ℂ) :
    ip (s • u) v = (starRingEnd ℂ) s * ip u v := by
  simp only [ip, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem ip_smul_right (s : ℂ) (u v : Fin 3 → ℂ) :
    ip u (s • v) = s * ip u v := by
  simp only [ip, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### The eight overlap values (exact arithmetic) -/

theorem ip_xz : ip xv zv = 1 := by
  simp [ip, Fin.sum_univ_three, xv, zv]

theorem ip_yz : ip yv zv = 1 := by
  simp [ip, Fin.sum_univ_three, yv, zv]

theorem ip_zw : ip zv wv = 1 := by
  simp [ip, Fin.sum_univ_three, zv, wv]

theorem ip_xw : ip xv wv = -2 * I := by
  simp [ip, Fin.sum_univ_three, xv, wv, Complex.conj_ofNat]

theorem ip_wx : ip wv xv = 2 * I := by
  simp [ip, Fin.sum_univ_three, wv, xv]

theorem ip_yw : ip yv wv = 2 := by
  simp [ip, Fin.sum_univ_three, yv, wv]
  ring

theorem ip_wy : ip wv yv = 2 := by
  simp [ip, Fin.sum_univ_three, wv, yv]
  ring

theorem ip_xx : ip xv xv = 6 := by
  simp [ip, Fin.sum_univ_three, xv, map_add, map_neg, map_mul, Complex.ext_iff]
  norm_num

theorem ip_yy : ip yv yv = 6 := by
  simp [ip, Fin.sum_univ_three, yv, Complex.ext_iff]
  norm_num

/-! ### Premise: the swap is a pairwise K-symmetry -/

/-- **The swap σ : x ↔ y (fixing z, w) preserves all pairwise projective
overlaps.** With `‖x‖² = ‖y‖² = 6`, the matching moduli
`|⟨x|z⟩|² = |⟨y|z⟩|² = 1` and `|⟨x|w⟩|² = |⟨y|w⟩|² = 4` give equal
projective K-values: `K(x,z) = K(y,z) = 5/6`, `K(x,w) = K(y,w) = 2/3`;
the value `K(x,y)` is preserved by symmetry of `K`. This is the
K-symmetry premise of paper Theorem `thm:binary-insufficiency`. -/
theorem pairwise_overlaps_match :
    ip xv xv = 6 ∧ ip yv yv = 6 ∧
    normSq (ip xv zv) = 1 ∧ normSq (ip yv zv) = 1 ∧
    normSq (ip xv wv) = 4 ∧ normSq (ip yv wv) = 4 := by
  refine ⟨ip_xx, ip_yy, ?_, ?_, ?_, ?_⟩
  · rw [ip_xz]; simp
  · rw [ip_yz]; simp
  · rw [ip_xw]; norm_num [Complex.normSq_apply]
  · rw [ip_yw]; norm_num [Complex.normSq_apply]

/-! ### Obstruction: the Bargmann products -/

theorem bargmann_x : ip xv zv * ip zv wv * ip wv xv = 2 * I := by
  rw [ip_xz, ip_zw, ip_wx]; ring

theorem bargmann_y : ip yv zv * ip zv wv * ip wv yv = 2 := by
  rw [ip_yz, ip_zw, ip_wy]; ring

/-- Helper: the accumulated ray-phase factor is a nonnegative real. -/
theorem phase_factor_real (a b c : ℂ) :
    ((starRingEnd ℂ) c * a) * (((starRingEnd ℂ) a * b) * ((starRingEnd ℂ) b * c))
      = ((normSq a * normSq b * normSq c : ℝ) : ℂ) := by
  have ha := Complex.mul_conj a
  have hb := Complex.mul_conj b
  have hc := Complex.mul_conj c
  calc ((starRingEnd ℂ) c * a) * (((starRingEnd ℂ) a * b) * ((starRingEnd ℂ) b * c))
      = (a * (starRingEnd ℂ) a) * ((b * (starRingEnd ℂ) b) * (c * (starRingEnd ℂ) c)) := by
        ring
    _ = ((normSq a : ℂ)) * (((normSq b : ℂ)) * ((normSq c : ℂ))) := by
        rw [ha, hb, hc]
    _ = ((normSq a * normSq b * normSq c : ℝ) : ℂ) := by
        push_cast; ring

/-- **No unitary extension** (paper Theorem `thm:binary-insufficiency`,
unitary branch). There is no map `U` on ℂ³ that preserves the inner
product on the configuration and sends the rays `z ↦ z`, `w ↦ w`,
`x ↦ y` (ray equality expressed by scalars `a, b, c`). Only the
inner-product rule and the three image equations are used; linearity is
not needed. -/
theorem no_unitary_extension (U : (Fin 3 → ℂ) → (Fin 3 → ℂ)) (a b c : ℂ)
    (hip : ∀ u v, ip (U u) (U v) = ip u v)
    (hz : U zv = a • zv) (hw : U wv = b • wv) (hx : U xv = c • yv) :
    False := by
  -- Cycle equation (x, z): conj c * a = 1.
  have h1 : (starRingEnd ℂ) c * a = 1 := by
    have h := hip xv zv
    rw [hx, hz, ip_smul_left, ip_smul_right, ip_yz, ip_xz] at h
    simpa using h
  -- Cycle equation (z, w): conj a * b = 1.
  have h2 : (starRingEnd ℂ) a * b = 1 := by
    have h := hip zv wv
    rw [hz, hw, ip_smul_left, ip_smul_right, ip_zw] at h
    simpa using h
  -- Cycle equation (w, x): conj b * c = i.
  have h3 : (starRingEnd ℂ) b * c = I := by
    have h := hip wv xv
    rw [hw, hx, ip_smul_left, ip_smul_right, ip_wy, ip_wx] at h
    have h' : ((starRingEnd ℂ) b * c) * 2 = I * 2 := by linear_combination h
    exact mul_right_cancel₀ two_ne_zero h'
  -- Product of the three equations: a nonnegative real equals i.
  have hprod : ((normSq a * normSq b * normSq c : ℝ) : ℂ) = I := by
    rw [← phase_factor_real a b c, h1, h2, h3]
    ring
  -- Compare imaginary parts: 0 = 1.
  have him := congrArg Complex.im hprod
  simp at him

/-- **No antiunitary extension** (paper Theorem
`thm:binary-insufficiency`, antiunitary branch). There is no map `T` on
ℂ³ that conjugates the inner product on the configuration and sends the
rays `z ↦ z`, `w ↦ w`, `x ↦ y`. -/
theorem no_antiunitary_extension (T : (Fin 3 → ℂ) → (Fin 3 → ℂ)) (a b c : ℂ)
    (hip : ∀ u v, ip (T u) (T v) = (starRingEnd ℂ) (ip u v))
    (hz : T zv = a • zv) (hw : T wv = b • wv) (hx : T xv = c • yv) :
    False := by
  -- Cycle equation (x, z): conj c * a = conj 1 = 1.
  have h1 : (starRingEnd ℂ) c * a = 1 := by
    have h := hip xv zv
    rw [hx, hz, ip_smul_left, ip_smul_right, ip_yz, ip_xz] at h
    simpa using h
  -- Cycle equation (z, w): conj a * b = conj 1 = 1.
  have h2 : (starRingEnd ℂ) a * b = 1 := by
    have h := hip zv wv
    rw [hz, hw, ip_smul_left, ip_smul_right, ip_zw] at h
    simpa using h
  -- Cycle equation (w, x): conj b * c = conj(2i)/2 = -i.
  have h3 : (starRingEnd ℂ) b * c = -I := by
    have h := hip wv xv
    rw [hw, hx, ip_smul_left, ip_smul_right, ip_wy, ip_wx] at h
    have hconj : (starRingEnd ℂ) (2 * I) = -2 * I := by
      simp only [map_mul, Complex.conj_ofNat, Complex.conj_I]
      ring
    rw [hconj] at h
    have h' : ((starRingEnd ℂ) b * c) * 2 = (-I) * 2 := by linear_combination h
    exact mul_right_cancel₀ two_ne_zero h'
  -- Product: a nonnegative real equals -i.
  have hprod : ((normSq a * normSq b * normSq c : ℝ) : ℂ) = -I := by
    rw [← phase_factor_real a b c, h1, h2, h3]
    ring
  have him := congrArg Complex.im hprod
  simp at him

/-- **Packaging: no unitary-or-antiunitary extension exists.** Combined
with Wigner's theorem in Uhlhorn's form (classical import: every
automorphism of (ℂP², K) is induced by a unitary or antiunitary map),
this refutes the blanket Structural Leibniz clause in the intended
model: the pairwise K-symmetry certified by `pairwise_overlaps_match`
admits no global extension. -/
theorem no_extension :
    (¬ ∃ (U : (Fin 3 → ℂ) → (Fin 3 → ℂ)) (a b c : ℂ),
      (∀ u v, ip (U u) (U v) = ip u v) ∧
      U zv = a • zv ∧ U wv = b • wv ∧ U xv = c • yv) ∧
    (¬ ∃ (T : (Fin 3 → ℂ) → (Fin 3 → ℂ)) (a b c : ℂ),
      (∀ u v, ip (T u) (T v) = (starRingEnd ℂ) (ip u v)) ∧
      T zv = a • zv ∧ T wv = b • wv ∧ T xv = c • yv) := by
  constructor
  · rintro ⟨U, a, b, c, hip, hz, hw, hx⟩
    exact no_unitary_extension U a b c hip hz hw hx
  · rintro ⟨T, a, b, c, hip, hz, hw, hx⟩
    exact no_antiunitary_extension T a b c hip hz hw hx

end BinaryInsufficiency
end QuantumRelational
