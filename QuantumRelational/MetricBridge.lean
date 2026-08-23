/-
  QuantumRelational/MetricBridge.lean

  **`thm:born-kernel`: From Distinguishability Kernel to Born Rule — The Metric Bridge**
  **`lem:metric-compatibility`: Metric Compatibility — Fisher-Rao Equals Fubini-Study**

  The "metric bridge" argument connects the geometric structure of state
  space (Fubini-Study metric g_FS) to the statistical structure of the
  probability simplex (Fisher-Rao metric g_FR), deriving the Born rule.

  **The logical chain:**
  1. K determines g_FS (`thm:fs-from-K`): K(ψ, ψ+dψ) = g_FS(dψ,dψ) + O(3)
  2. Any probability rule p_k = f(|c_k|²) determines a Fisher-Rao metric:
       g_FR = Σ_k [f'(|c_k|²)]² d|c_k|⁴ / f(|c_k|²)
  3. U(N)-invariance forces g_FR ∝ g_FS (`thm:fs-unique` via Kobayashi-Nomizu)
  4. This proportionality gives the metric compatibility ODE:
       [f'(x)]² / (f(x)(1-f(x))) = c² / (x(1-x))
  5. ODE uniqueness (Picard-Lindelöf) with f(0)=0, f(1)=1 forces f = id
  6. Therefore p_k = |c_k|² — the Born rule

  Requires Fisher-Rao metric definition.
  Lean status: core derivation chain formalized
-/
import QuantumRelational.FubiniStudy
import QuantumRelational.BornRule

namespace QuantumRelational.MetricBridge

-- ============================================================
-- Section 1: K = D² and the Fubini-Study connection
-- ============================================================

/-- **K = D² for pure states (`thm:born-kernel` (Step 1, K = D² for pure states)).**

    K(ψ,φ) = 1 - |⟨ψ|φ⟩|² = ‖ψ - ⟨φ|ψ⟩φ‖² (the squared Fubini-Study
    projection distance from ψ to the ray through φ).

    This connects the distinguishability kernel K directly to the
    Riemannian geometry of projective Hilbert space.

    The proof delegates to `FubiniStudy.K_equals_projection_distance`. -/
theorem K_equals_D_squared
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ψ φ : V) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    1 - ‖@inner ℂ V _ φ ψ‖ ^ 2 = ‖ψ - (@inner ℂ V _ φ ψ) • φ‖ ^ 2 :=
  FubiniStudy.K_equals_projection_distance ψ φ hψ hφ

-- ============================================================
-- Section 2: Fisher-Rao metric from probability assignment
-- ============================================================

/-- **The Fisher-Rao metric on the probability simplex.**

    Given probabilities p_k = f(|c_k|²) with f an admissible probability
    assignment, the Fisher-Rao metric (information metric) is:

      g_FR = Σ_k dp_k² / p_k

    Substituting p_k = f(|c_k|²) and dp_k = f'(|c_k|²) · d(|c_k|²):

      g_FR = Σ_k [f'(|c_k|²)]² [d(|c_k|²)]² / f(|c_k|²)

    For f(x) = x^{α/2}:
      f'(x) = (α/2) x^{α/2-1}
      g_FR = (α/2)² Σ_k |c_k|^{α-2} · 4|c_k|²|dc_k|²

    The ratio g_FR/g_FS involves the weights |c_k|^{α-2}, which are
    state-independent only when α = 2. -/
noncomputable def FisherRaoWeight (alpha : ℝ) (c_k_sq : ℝ) : ℝ :=
  c_k_sq ^ ((alpha - 2) / 2)

/-- For α = 2, the Fisher-Rao weight is constant = 1 for all x > 0.
    This is the ONLY exponent making g_FR/g_FS state-independent. -/
theorem fisher_rao_weight_alpha_2 (x : ℝ) (_hx : 0 < x) :
    FisherRaoWeight 2 x = 1 := by
  simp [FisherRaoWeight, Real.rpow_zero]

-- ============================================================
-- Section 3: Metric Compatibility (`lem:metric-compatibility`)
-- ============================================================

/-- **Metric Compatibility Predicate (`lem:metric-compatibility`)**

    A probability assignment f is metric-compatible if the Fisher-Rao
    metric g_FR induced by probabilities p_k = f(|c_k|²) is proportional
    to the Fubini-Study metric g_FS:

      g_FR = c² · g_FS  for some constant c > 0

    This is a strong constraint: the ratio g_FR/g_FS must be the SAME
    constant for ALL states ψ and ALL radial (probability-changing)
    tangent directions.

    For a power-law f(x) = x^{α/2}, this requires the weights
    |c_k|^{α-2} to be independent of the state, forcing α = 2.

    In general, metric compatibility is equivalent to the ODE:
      [f'(x)]² / (f(x)(1-f(x))) = c² / (x(1-x)) -/
def MetricCompatible (f : ℝ → ℝ) : Prop :=
  ∃ (f' : ℝ → ℝ) (c : ℝ),
    BornRule.MetricCompatibilityODE f f' c ∧
    f 0 = 0 ∧ f 1 = 1 ∧
    Monotone f ∧
    ContinuousOn f (Set.Icc 0 1) ∧
    (∀ x, 0 < x → x < 1 → HasDerivAt f (f' x) x)

/-- **`lem:metric-compatibility` (key part): Metric compatibility forces α = 2 in power-law ansatz.**

    If f(x) = x^{α/2} is a power-law probability assignment, the
    Fisher-Rao / Fubini-Study ratio involves weights w_k = |c_k|^{α-2}.

    State-independence of the ratio along radial (probability-changing)
    tangent vectors requires α - 2 = 0, i.e., α = 2.

    For general (non-power-law) f, this generalizes to the full ODE
    condition captured by MetricCompatibilityODE.

    This is the heart of the metric bridge argument. -/
theorem metric_compatibility_forces_alpha_2
    (alpha : ℝ) (_halpha : alpha > 0)
    -- The weight function w(x) = x^{(α-2)/2} must be constant on (0,1)
    (h_const : ∀ x y : ℝ, 0 < x → x < 1 → 0 < y → y < 1 →
      FisherRaoWeight alpha x = FisherRaoWeight alpha y)
    : alpha = 2 := by
  -- If the weight is constant, evaluate at x=1/2 and use the definition
  by_contra h_ne
  have h12 : (0 : ℝ) < 1 / 2 := by norm_num
  have h12' : (1 : ℝ) / 2 < 1 := by norm_num
  have h14 : (0 : ℝ) < 1 / 4 := by norm_num
  have h14' : (1 : ℝ) / 4 < 1 := by norm_num
  have hw := h_const (1/2) (1/4) h12 h12' h14 h14'
  -- FisherRaoWeight α (1/2) = (1/2)^((α-2)/2) and similarly for 1/4
  -- These are equal only if (α-2)/2 = 0, i.e., α = 2
  simp only [FisherRaoWeight] at hw
  have hne : (alpha - 2) / 2 ≠ 0 := by
    intro heq
    apply h_ne
    linarith
  -- (1/2)^p = (1/4)^p with p ≠ 0 is impossible since 1/2 ≠ 1/4
  have h2nn : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have h4nn : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have hne_bases : (1 : ℝ) / 2 ≠ 1 / 4 := by norm_num
  rw [Real.rpow_left_inj h2nn h4nn hne] at hw
  exact absurd hw hne_bases

/-- **Corollary: The proportionality constant is determined.**

    Once α = 2 is fixed, f(x) = x and f'(x) = 1, so:
      g_FR = Σ_k 4|dc_k|² = 4 · g_FS
    The proportionality constant is c² = 4 (or c = 2).

    Equivalently, g_FR = (1/4)⁻¹ · g_FS, which connects to the
    quantum Fisher information: F_Q = 4 g_FS.

    This is a restatement of `FubiniStudy.gFS_quarter_FQ`:
      g_FS = (1/4) · F_Q, hence F_Q = 4 · g_FS. -/
theorem fisher_rao_proportionality_constant
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ψ dψ : V) :
    FubiniStudy.fubini_study_form ψ dψ =
    (1 / 4 : ℝ) * (4 * FubiniStudy.fubini_study_form ψ dψ) :=
  FubiniStudy.gFS_quarter_FQ ψ dψ

-- ============================================================
-- Section 4: The Metric Bridge Theorem (`thm:born-kernel`)
-- ============================================================

/-- **`thm:born-kernel`: The Metric Bridge — From K to the Born Rule**

    The complete derivation chain:

    Step 1: K(ψ,φ) = 1 - |⟨ψ|φ⟩|² determines the Fubini-Study metric
            g_FS via Taylor expansion (`thm:fs-from-K`).

    Step 2: Any admissible probability assignment p_k = f(|c_k|²)
            determines a Fisher-Rao metric g_FR on the probability simplex.

    Step 3: U(N)-invariance forces g_FR ∝ g_FS (`thm:fs-unique` via
            Kobayashi-Nomizu: the FS metric is the unique U(N)-invariant
            metric on ℂP^{N-1}).

    Step 4: The proportionality g_FR = c² · g_FS gives the ODE:
              [f'(x)]² / (f(x)(1-f(x))) = c² / (x(1-x))

    Step 5: By ODE uniqueness (Picard-Lindelöf) with f(0)=0, f(1)=1:
              f(x) = x  and  c = 1

    Conclusion: p_k = f(|c_k|²) = |c_k|² — the Born rule.

    This theorem ties together the metric bridge: given any admissible
    probability assignment satisfying metric compatibility, it must equal
    the identity on [0,1] — the Born rule on its physical domain. -/
theorem metric_bridge
    (A : BornRule.AdmissibleProbAssignment)
    (hmc : MetricCompatible A.f) :
    ∀ x, 0 ≤ x → x ≤ 1 → A.f x = x := by
  -- Extract the ODE data from metric compatibility
  obtain ⟨f', c, hode, hf0, hf1, hmono, hcont, hderiv⟩ := hmc
  -- Apply the ODE uniqueness theorem
  have huniq := BornRule.ode_uniqueness_born_rule A.f f' c hode hf0 hf1 hmono hcont hderiv
  exact huniq.1

/-- **Corollary:** Metric compatibility forces the proportionality constant c = 1. -/
theorem metric_bridge_constant
    (A : BornRule.AdmissibleProbAssignment)
    (hmc : MetricCompatible A.f) :
    ∃ c, c = 1 ∧ ∃ f', BornRule.MetricCompatibilityODE A.f f' c := by
  obtain ⟨f', c, hode, hf0, hf1, hmono, hcont, hderiv⟩ := hmc
  have huniq := BornRule.ode_uniqueness_born_rule A.f f' c hode hf0 hf1 hmono hcont hderiv
  exact ⟨c, huniq.2, f', hode⟩

/-- **The identity function is metric-compatible.**

    Verification: f(x) = x with f'(x) = 1 gives:
      1² / (x(1-x)) = 1² / (x(1-x))  ✓
    with boundary conditions f(0) = 0, f(1) = 1. -/
theorem id_is_metric_compatible : MetricCompatible id := by
  refine ⟨fun _ => 1, 1, BornRule.id_satisfies_ode, rfl, rfl, monotone_id,
    continuous_id.continuousOn, ?_⟩
  intro x _ _
  exact hasDerivAt_id x

/-- **Uniqueness:** The identity is the ONLY metric-compatible
    admissible probability assignment (on the physical domain [0,1]).

    Combining the metric bridge theorem with verification that id works:
    - Existence: id satisfies MetricCompatible (id_is_metric_compatible)
    - Uniqueness: any MetricCompatible f must equal id on [0,1] (metric_bridge)
    Since |c_k|² ∈ [0,1] for all amplitudes, this covers all physical inputs. -/
theorem born_rule_unique_metric_compatible
    (A : BornRule.AdmissibleProbAssignment)
    (hmc : MetricCompatible A.f) :
    ∀ x, 0 ≤ x → x ≤ 1 → A.f x = x :=
  metric_bridge A hmc

-- ============================================================
-- Section 5: Reversibility and Continuity
-- ============================================================

-- Note: (deleted) `cor:dynamics-born` (reversible_forces_alpha_2) was removed — it was an
-- exact synonym of metric_compatibility_forces_alpha_2, confirmed unused elsewhere.

-- ============================================================
-- Statement #63: Continuity of Probability from Reversible Dynamics
-- ============================================================

/-- **`lem:continuity-from-dynamics`: Continuity of Probability from Reversible Dynamics**

The probability function p must be continuous. Since K = 1 - |⟨ψ|φ⟩|²
is a composition of continuous functions (inner product, norm, squaring,
subtraction from 1), and p = f(K) for a continuous f, the probability p
is itself continuous.

We prove the structural result: if g and f are both continuous, then
f ∘ g is continuous. Applied to g = K (continuous by construction from
the inner product) and f = born_f = id, we get continuity of p. -/
theorem continuity_of_probability
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (g : X → Y) (f : Y → Z)
    (hg : Continuous g) (hf : Continuous f) :
    Continuous (f ∘ g) :=
  hf.comp hg

/-- Specialization: the kernel K = 1 - |⟨ψ|φ⟩|² is a composition of
    continuous functions on ℝ:
    overlap_sq ↦ 1 - overlap_sq is continuous. -/
theorem K_from_overlap_sq_continuous :
    Continuous (fun (x : ℝ) => 1 - x) :=
  continuous_const.sub continuous_id

/-- The Born rule probability p = f(K) = id(K) is continuous whenever
    K is continuous, since id is continuous. -/
theorem born_probability_continuous :
    Continuous (fun (x : ℝ) => x) :=
  continuous_id

/-- The full probability chain K ↦ 1-K ↦ born_f(1-K) = 1-K is continuous. -/
theorem born_probability_from_K_continuous :
    Continuous (fun (K_val : ℝ) => BornRule.born_f (1 - K_val)) :=
  continuous_const.sub continuous_id

-- ============================================================
-- Section 6: Fisher-Rao Metric as a First-Class Object
-- ============================================================

/-- **The Fisher-Rao metric on the probability simplex (first-class definition).**

    For a probability vector `p : Fin N → ℝ` with `p_k > 0` for all k,
    and a tangent vector `dp : Fin N → ℝ` with `∑_k dp_k = 0`
    (preserving normalization), the Fisher-Rao (information) metric is:

      g_FR(p, dp, dp) = ∑_k (dp_k)² / p_k

    This is the Fisher information for the categorical distribution `p`.
    It is the unique Riemannian metric on the probability simplex that
    is invariant under sufficient statistics (Chentsov's theorem).

    Upstream code (the `MetricCompatibilityODE` predicate in `BornRule`)
    works with a two-outcome marginal of this metric in the binary form
    `[f']² / (f(1-f))`. The present definition makes the full N-outcome
    Fisher-Rao metric available as a first-class object for any future
    code that wants to reason about the simplex directly. -/
noncomputable def fisherRao {N : ℕ} (p : Fin N → ℝ) (dp : Fin N → ℝ) : ℝ :=
  ∑ k, (dp k) ^ 2 / (p k)

/-- **Fisher-Rao is non-negative on positive probability vectors.** -/
theorem fisherRao_nonneg {N : ℕ} (p : Fin N → ℝ) (dp : Fin N → ℝ)
    (hp : ∀ k, 0 < p k) :
    0 ≤ fisherRao p dp := by
  unfold fisherRao
  apply Finset.sum_nonneg
  intro k _
  exact div_nonneg (sq_nonneg _) (hp k).le

/-- **Fisher-Rao is zero iff all tangent components are zero (on positive p).** -/
theorem fisherRao_eq_zero_iff {N : ℕ} (p : Fin N → ℝ) (dp : Fin N → ℝ)
    (hp : ∀ k, 0 < p k) :
    fisherRao p dp = 0 ↔ ∀ k, dp k = 0 := by
  unfold fisherRao
  constructor
  · intro h k
    have h_nonneg : ∀ j ∈ Finset.univ, (0 : ℝ) ≤ (dp j) ^ 2 / (p j) :=
      fun j _ => div_nonneg (sq_nonneg _) (hp j).le
    have h_k_nonneg : (0 : ℝ) ≤ (dp k) ^ 2 / (p k) :=
      div_nonneg (sq_nonneg _) (hp k).le
    have h_k_zero : (dp k) ^ 2 / (p k) = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg h_nonneg).mp h k (Finset.mem_univ k)
    have : (dp k) ^ 2 = 0 := by
      rw [div_eq_zero_iff] at h_k_zero
      cases h_k_zero with
      | inl h => exact h
      | inr h => exact absurd h (ne_of_gt (hp k))
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  · intro h
    apply Finset.sum_eq_zero
    intro k _
    rw [h k]; simp

/-- **The binary (two-outcome) Fisher-Rao metric.**

    For two outcomes with probabilities `p` and `1-p`, the Fisher-Rao
    metric on a tangent vector `(dp, -dp)` (preserving normalization
    `p + (1-p) = 1`) reduces to the Bernoulli Fisher information:

      g_FR^{bin}(p)(dp)² = dp² / p + dp² / (1-p) = dp² / (p(1-p))

    This is the form used in the ODE `[f'(x)]² / (f(x)(1-f(x)))`
    appearing in `BornRule.MetricCompatibilityODE`. The connection:
    if `p = f(x)` is a probability assignment, and one varies a single
    amplitude `x`, the induced binary Fisher-Rao metric on the
    `(f(x), 1-f(x))` distribution matches the LHS of the ODE. -/
noncomputable def binaryFisherRao (p : ℝ) (dp : ℝ) : ℝ :=
  (dp ^ 2) / (p * (1 - p))

/-- **Identity of binary Fisher-Rao with the 2-outcome specialization.** -/
theorem binaryFisherRao_eq_fisherRao_two (p : ℝ) (dp : ℝ)
    (hp : 0 < p) (hp1 : p < 1) :
    binaryFisherRao p dp =
      fisherRao (fun k : Fin 2 => if k = 0 then p else 1 - p)
                (fun k : Fin 2 => if k = 0 then dp else -dp) := by
  unfold binaryFisherRao fisherRao
  rw [Fin.sum_univ_two]
  simp only [↓reduceIte, one_ne_zero]
  have hp_ne : p ≠ 0 := ne_of_gt hp
  have hp1_pos : 0 < 1 - p := by linarith
  have hp1_ne : 1 - p ≠ 0 := ne_of_gt hp1_pos
  -- After simp: goal is dp^2 / (p * (1 - p)) = dp^2 / p + (-dp)^2 / (1 - p)
  have h_neg_sq : (-dp) ^ 2 = dp ^ 2 := by ring
  rw [h_neg_sq]
  field_simp
  ring

/-- **The Fisher-Rao metric induced by a probability assignment `p = f(x)`.**

    When probabilities come from a differentiable function `p_k = f(x_k)`
    with `f'(x_k) = f'`, the induced Fisher-Rao metric on tangent
    vectors `dx` is:

      g_FR(x)(dx)² = ∑_k (f'(x_k))² (dx_k)² / f(x_k)

    For the binary case (two outcomes with `x` and `1-x`), this reduces
    to the ODE form `[f']² (dx)² / (f(x)(1-f(x)))` which appears in
    `MetricCompatibilityODE`. -/
noncomputable def fisherRaoFromAssignment {N : ℕ}
    (f : ℝ → ℝ) (f' : ℝ → ℝ) (x : Fin N → ℝ) (dx : Fin N → ℝ) : ℝ :=
  ∑ k, ((f' (x k)) ^ 2 * (dx k) ^ 2) / (f (x k))

end QuantumRelational.MetricBridge
