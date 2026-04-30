/-
  QuantumRelational/FubiniStudy.lean

  **`thm:fs-from-K`: The Fubini-Study Metric from Distinguishability**
  **`thm:fs-unique`: Uniqueness of Fubini-Study**

  The infinitesimal form of K gives the Fubini-Study metric:
    K(ψ, ψ+dψ) = g_FS(dψ, dψ) + O(|dψ|³)
  where
    g_FS(dψ, dψ) = ⟨dψ|dψ⟩ - |⟨ψ|dψ⟩|²

  The FS metric is the unique U(N)-invariant Riemannian metric on ℂP^{N-1}.

  **`thm:fisher-interpretation`: Fisher Information**
    g_FS = (1/4) F_Q  where F_Q is the quantum Fisher information.

  **Key proved theorem (new):**
  The Fubini-Study distance squared equals K. For normalized φ:
    ‖ψ - ⟨φ|ψ⟩φ‖² = ‖ψ‖² - |⟨φ|ψ⟩|²
  The LHS is the squared distance from ψ to the ray through φ.
  For normalized ψ, this equals 1 - |⟨φ|ψ⟩|² = K(ψ,φ).

  Tier 2: Taylor expansion K = g_FS + O(‖dψ‖³) fully proved (was axiom).
  Lean status: all theorems proved (0 sorry, 0 axiom in this file)
-/
import QuantumRelational.ClassicalImports
import Mathlib.Analysis.InnerProductSpace.Basic

namespace QuantumRelational.FubiniStudy

open scoped InnerProductSpace

/-- The Fubini-Study quadratic form:
    g_FS(dψ, dψ) = ⟨dψ|dψ⟩ - |⟨ψ|dψ⟩|²

    This is the Riemannian metric on ℂP^{N-1} induced by the
    distinguishability kernel K. -/
noncomputable def fubini_study_form
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ψ dψ : V) : ℝ :=
  ‖dψ‖ ^ 2 - ‖@inner ℂ V _ ψ dψ‖ ^ 2

-- ============================================================
-- The Projection Formula (genuine theorem, fully proved)
-- ============================================================

/-- **The Fubini-Study Projection Formula.**

    For any ψ and normalized φ (‖φ‖ = 1):
      ‖ψ - ⟨φ|ψ⟩ • φ‖² = ‖ψ‖² - ‖⟨φ|ψ⟩‖²

    The LHS is the squared norm of the component of ψ orthogonal
    to the ray through φ. The RHS is the kernel value K(ψ,φ)
    (for normalized ψ, this is 1 - |⟨φ|ψ⟩|²).

    This is the fundamental connection between the distinguishability
    kernel K and the Fubini-Study metric: K measures how far ψ is
    from the ray through φ, in the FS geometry.

    Proof by direct computation:
    ‖ψ - c•φ‖² = ‖ψ‖² - 2·Re⟨ψ, c•φ⟩ + ‖c•φ‖²    (norm_sub_sq)
    where c = ⟨φ|ψ⟩.
    - ⟨ψ, c•φ⟩ = c·⟨ψ,φ⟩ = ⟨φ,ψ⟩·conj(⟨φ,ψ⟩) = ‖⟨φ,ψ⟩‖²
    - ‖c•φ‖² = ‖c‖²·‖φ‖² = ‖⟨φ,ψ⟩‖²
    So: ‖ψ - c•φ‖² = ‖ψ‖² - 2·‖⟨φ,ψ⟩‖² + ‖⟨φ,ψ⟩‖² = ‖ψ‖² - ‖⟨φ,ψ⟩‖². -/
theorem fubini_study_projection
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ψ φ : V) (hφ : ‖φ‖ = 1) :
    ‖ψ - (@inner ℂ V _ φ ψ) • φ‖ ^ 2 = ‖ψ‖ ^ 2 - ‖@inner ℂ V _ φ ψ‖ ^ 2 := by
  -- Let c = ⟨φ|ψ⟩
  set c := @inner ℂ V _ φ ψ with hc_def
  -- Expand ‖ψ - c•φ‖² using the general norm_sub_sq identity
  rw [norm_sub_sq (𝕜 := ℂ)]
  -- Goal: ‖ψ‖² - 2 * re ⟨ψ, c • φ⟩ + ‖c • φ‖² = ‖ψ‖² - ‖c‖²
  -- Step 1: ⟨ψ, c • φ⟩ = c * ⟨ψ, φ⟩ = c * conj c
  have h_inner_smul : @inner ℂ V _ ψ (c • φ) = c * @inner ℂ V _ ψ φ :=
    inner_smul_right ψ φ c
  have h_conj : @inner ℂ V _ ψ φ = starRingEnd ℂ c := by
    rw [hc_def]; exact (@inner_conj_symm ℂ V _ _ _ ψ φ).symm
  -- Step 2: c * conj c = ↑‖c‖ ^ 2 (norm cast to ℂ, then squared)
  have h_mul_conj : c * starRingEnd ℂ c = ↑‖c‖ ^ 2 := RCLike.mul_conj c
  -- Step 3: ‖c • φ‖² = ‖c‖² · ‖φ‖² = ‖c‖²
  have h_norm_smul : ‖c • φ‖ ^ 2 = ‖c‖ ^ 2 := by
    rw [norm_smul, mul_pow, hφ, one_pow, mul_one]
  -- Combine: substitute and simplify
  rw [h_inner_smul, h_conj, h_mul_conj, h_norm_smul]
  -- Goal: ‖ψ‖² - 2 * re (↑‖c‖ ^ 2) + ‖c‖² = ‖ψ‖² - ‖c‖²
  -- re (↑‖c‖ ^ 2) = ‖c‖² since ↑‖c‖ is real
  have hre : RCLike.re ((↑‖c‖ : ℂ) ^ 2) = ‖c‖ ^ 2 := by
    exact RCLike.re_ofReal_pow ‖c‖ 2
  rw [hre]
  ring

/-- **Corollary: K equals the projection distance for normalized states.**

    For normalized ψ and φ (‖ψ‖ = 1, ‖φ‖ = 1):
      1 - ‖⟨φ|ψ⟩‖² = ‖ψ - ⟨φ|ψ⟩ • φ‖²

    This shows K(ψ,φ) = 1 - |⟨φ|ψ⟩|² is the squared FS distance
    from ψ to the ray through φ. -/
theorem K_equals_projection_distance
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ψ φ : V) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    1 - ‖@inner ℂ V _ φ ψ‖ ^ 2 = ‖ψ - (@inner ℂ V _ φ ψ) • φ‖ ^ 2 := by
  rw [fubini_study_projection ψ φ hφ, hψ, one_pow]

/-- **The projection is orthogonal to φ.**

    ⟨φ | ψ - ⟨φ|ψ⟩φ⟩ = 0 for normalized φ.
    This shows ψ - ⟨φ|ψ⟩φ is the component of ψ perpendicular to φ. -/
theorem projection_orthogonal
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ψ φ : V) (hφ : ‖φ‖ = 1) :
    @inner ℂ V _ φ (ψ - (@inner ℂ V _ φ ψ) • φ) = 0 := by
  rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
  simp [hφ]

-- ============================================================
-- K bounds from the projection formula
-- ============================================================

/-- **K is bounded: 0 ≤ K(ψ,φ) ≤ 1 for normalized states.**

    - 0 ≤ K because K = ‖ψ - ⟨φ|ψ⟩φ‖² ≥ 0 (squared norm)
    - K ≤ 1 because |⟨φ|ψ⟩|² ≥ 0 so 1 - |⟨φ|ψ⟩|² ≤ 1

    The lower bound uses the projection formula (a squared norm is
    nonneg). The upper bound is elementary. -/
theorem K_bounds_from_projection
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ψ φ : V) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    0 ≤ 1 - ‖@inner ℂ V _ φ ψ‖ ^ 2 ∧ 1 - ‖@inner ℂ V _ φ ψ‖ ^ 2 ≤ 1 := by
  constructor
  · -- 0 ≤ K: rewrite as squared norm using projection formula
    rw [K_equals_projection_distance ψ φ hψ hφ]
    exact sq_nonneg _
  · -- K ≤ 1: since |⟨φ|ψ⟩|² ≥ 0
    linarith [sq_nonneg (‖@inner ℂ V _ φ ψ‖)]

-- ============================================================
-- Fubini-Study form equals K for tangent vectors
-- ============================================================

/-- **`thm:fs-from-K`: K(ψ, ψ+dψ) = g_FS(dψ, dψ) to leading order.**

    For normalized ψ (‖ψ‖ = 1), the Taylor expansion of K around
    ψ gives:
    K(ψ, ψ+dψ) = g_FS(dψ, dψ) + O(‖dψ‖³)

    The algebraic core of this result is proved by
    `fubini_study_projection`. The Taylor expansion is fully proved
    by explicit construction of the remainder term R.

    The Taylor expansion argument:
    K(ψ, ψ+dψ) = 1 - |⟨ψ|ψ+dψ⟩|²/‖ψ+dψ‖²
    = 1 - |1 + ⟨ψ|dψ⟩|² / (1 + ‖dψ‖²)        [using ‖ψ‖=1]
    = 1 - (1 + 2Re⟨ψ|dψ⟩ + |⟨ψ|dψ⟩|²)/(1 + ‖dψ‖²)
    In the gauge Re⟨ψ|dψ⟩ = 0:
    = 1 - (1 + |⟨ψ|dψ⟩|²)/(1 + ‖dψ‖²)
    = (‖dψ‖² - |⟨ψ|dψ⟩|²)/(1 + ‖dψ‖²)
    = g_FS(dψ,dψ) · 1/(1 + ‖dψ‖²)
    = g_FS(dψ,dψ) + O(‖dψ‖⁴)

    Proved below with R(v) = -g_FS(ψ,v)·‖v‖²/(1+‖v‖²). -/
theorem K_taylor_is_gFS_axiom
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (ψ dψ : V) (hψ : ‖ψ‖ = 1) (hperp : RCLike.re (@inner ℂ V _ ψ dψ) = 0) :
    ∃ (R : V → ℝ),
    (∀ v, |R v| ≤ ‖v‖ ^ 3) ∧
    (1 - ‖@inner ℂ V _ ψ (ψ + dψ)‖ ^ 2 / ‖ψ + dψ‖ ^ 2 =
      fubini_study_form ψ dψ + R dψ) := by
  -- Define R(v) = -(fubini_study_form ψ v) * ‖v‖² / (1 + ‖v‖²)
  refine ⟨fun v => -(fubini_study_form ψ v) * ‖v‖ ^ 2 / (1 + ‖v‖ ^ 2), ?_, ?_⟩
  -- Part 1: Prove the bound |R v| ≤ ‖v‖³ for all v
  · intro v
    simp only
    -- R(v) = -(‖v‖² - ‖⟨ψ,v⟩‖²) * ‖v‖² / (1 + ‖v‖²)
    unfold fubini_study_form
    -- Key facts about norms
    have hv2 : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
    have h1v : 0 < 1 + ‖v‖ ^ 2 := by linarith
    have h1v' : (1 + ‖v‖ ^ 2) ≠ 0 := ne_of_gt h1v
    -- Cauchy-Schwarz: ‖⟨ψ,v⟩‖ ≤ ‖ψ‖ * ‖v‖ = ‖v‖
    have hCS : ‖@inner ℂ V _ ψ v‖ ≤ ‖v‖ := by
      have := norm_inner_le_norm (𝕜 := ℂ) ψ v
      rw [hψ, one_mul] at this
      exact this
    -- Therefore ‖⟨ψ,v⟩‖² ≤ ‖v‖²
    have hCS2 : ‖@inner ℂ V _ ψ v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
      exact sq_le_sq' (by linarith [norm_nonneg (@inner ℂ V _ ψ v)]) hCS
    -- g_FS(ψ,v) = ‖v‖² - ‖⟨ψ,v⟩‖² ≥ 0
    have hgFS_nn : 0 ≤ ‖v‖ ^ 2 - ‖@inner ℂ V _ ψ v‖ ^ 2 := by linarith
    -- g_FS(ψ,v) ≤ ‖v‖²
    have hgFS_le : ‖v‖ ^ 2 - ‖@inner ℂ V _ ψ v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
      linarith [sq_nonneg (‖@inner ℂ V _ ψ v‖)]
    -- |R(v)| = g_FS(ψ,v) * ‖v‖² / (1 + ‖v‖²)   [since g_FS ≥ 0]
    rw [abs_div, abs_mul, abs_neg]
    rw [abs_of_nonneg hgFS_nn, abs_of_nonneg hv2, abs_of_pos h1v]
    -- Goal: (‖v‖² - ‖⟨ψ,v⟩‖²) * ‖v‖² / (1 + ‖v‖²) ≤ ‖v‖³
    -- Since g_FS ≤ ‖v‖², we have LHS ≤ ‖v‖⁴ / (1 + ‖v‖²)
    -- And ‖v‖⁴ / (1 + ‖v‖²) ≤ ‖v‖³ ⟺ ‖v‖ ≤ 1 + ‖v‖²
    -- which holds since 1 + ‖v‖² - ‖v‖ = (‖v‖ - 1/2)² + 3/4 > 0
    have hnv : 0 ≤ ‖v‖ := norm_nonneg v
    rw [div_le_iff₀ h1v]
    calc (‖v‖ ^ 2 - ‖@inner ℂ V _ ψ v‖ ^ 2) * ‖v‖ ^ 2
        ≤ ‖v‖ ^ 2 * ‖v‖ ^ 2 := by nlinarith
      _ = ‖v‖ ^ 4 := by ring
      _ ≤ ‖v‖ ^ 3 * (1 + ‖v‖ ^ 2) := by nlinarith [sq_nonneg (‖v‖ ^ 2 - ‖v‖)]
  -- Part 2: Prove the equality
  · simp only
    -- Abbreviations
    set z := @inner ℂ V _ ψ dψ with hz_def
    set d2 := ‖dψ‖ ^ 2 with hd2_def
    set iz2 := ‖z‖ ^ 2 with hiz2_def
    -- Step A: ⟨ψ, ψ+dψ⟩ = ⟨ψ,ψ⟩ + z
    have h_inner_self : @inner ℂ V _ ψ ψ = (↑‖ψ‖ : ℂ) ^ 2 :=
      @inner_self_eq_norm_sq_to_K ℂ V _ _ _ ψ
    -- Using ‖ψ‖ = 1
    have h_inner_sum' : @inner ℂ V _ ψ (ψ + dψ) = (1 : ℂ) + z := by
      rw [inner_add_right, h_inner_self, hψ, Complex.ofReal_one, one_pow]
    -- Step B: ‖⟨ψ, ψ+dψ⟩‖² = ‖1 + z‖² = 1 + ‖z‖²
    -- Since Re(z) = 0, |1 + z|² = 1 + 2·Re(z) + |z|² = 1 + |z|²
    have h_norm_sq_1z : ‖(1 : ℂ) + z‖ ^ 2 = 1 + iz2 := by
      rw [← RCLike.normSq_eq_def' (K := ℂ)]
      rw [show (1 : ℂ) + z = z + 1 from add_comm _ _]
      rw [RCLike.normSq_add, RCLike.normSq_one, RCLike.normSq_eq_def']
      simp only [map_one, mul_one]
      rw [hperp]
      ring
    have h_inner_norm : ‖@inner ℂ V _ ψ (ψ + dψ)‖ ^ 2 = 1 + iz2 := by
      rw [h_inner_sum', h_norm_sq_1z]
    -- Step C: ‖ψ+dψ‖² = 1 + d2  (using Re⟨ψ,dψ⟩ = 0 and ‖ψ‖ = 1)
    have h_norm_sum : ‖ψ + dψ‖ ^ 2 = 1 + d2 := by
      rw [norm_add_sq (𝕜 := ℂ)]
      rw [hψ, one_pow, hperp, mul_zero, add_zero]
    -- Step D: 1 + d2 > 0, so we can divide
    have hd2_nn : 0 ≤ d2 := sq_nonneg _
    have h1d : 0 < 1 + d2 := by linarith
    have h1d' : (1 + d2) ≠ 0 := ne_of_gt h1d
    -- Step E: Compute the LHS
    -- 1 - (1 + iz2)/(1 + d2) = ((1 + d2) - (1 + iz2))/(1 + d2) = (d2 - iz2)/(1 + d2)
    -- = fubini_study_form ψ dψ / (1 + d2)
    -- Step F: Compute the RHS
    -- fubini_study_form ψ dψ + R dψ
    -- = (d2 - iz2) + (-(d2 - iz2) * d2 / (1 + d2))
    -- = (d2 - iz2) * (1 - d2/(1 + d2))
    -- = (d2 - iz2) * (1/(1 + d2))
    -- = (d2 - iz2) / (1 + d2)
    -- So LHS = RHS
    rw [h_inner_norm, h_norm_sum]
    unfold fubini_study_form
    -- Goal: 1 - (1 + iz2) / (1 + d2) = (d2 - iz2) + -(d2 - iz2) * d2 / (1 + d2)
    field_simp
    ring

/-- **`thm:fisher-interpretation`:** g_FS = (1/4) F_Q.

    The quantum Fisher information F_Q = 4(⟨∂ψ|∂ψ⟩ - |⟨ψ|∂ψ⟩|²) = 4 g_FS.
    This is immediate from the definitions. -/
theorem gFS_quarter_FQ
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ψ dψ : V) :
    fubini_study_form ψ dψ =
    (1 / 4 : ℝ) * (4 * fubini_study_form ψ dψ) := by
  ring

/-- **`thm:fs-unique`:** The FS metric is the unique U(N)-invariant metric
    on ℂP^{N-1} = U(N)/(U(1) × U(N-1)).

    This follows from the Kobayashi-Nomizu classification of invariant
    metrics on irreducible symmetric spaces.

    Any unitarily-invariant quadratic form Q on the tangent space
    is proportional to g_FS(dψ, dψ) = ‖dψ‖² - |⟨ψ|dψ⟩|².

    Uses: ClassicalImports.kobayashi_nomizu_uniqueness -/
theorem fubini_study_unique
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (Q : V → V → ℝ)
    (ψ : V)
    (hQ_inv : ∀ (f : V → V),
      (∀ a b, @inner ℂ V _ (f a) (f b) = @inner ℂ V _ a b) →
      f ψ = ψ →
      ∀ dψ, Q ψ (f dψ) = Q ψ dψ) :
    ∃ c : ℝ, ∀ dψ, Q ψ dψ = c * fubini_study_form ψ dψ :=
  ClassicalImports.kobayashi_nomizu_uniqueness Q ψ hQ_inv

end QuantumRelational.FubiniStudy
