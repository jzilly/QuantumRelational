/-
  QuantumRelational/ModelExistence.lean

  **Model Existence** (paper Theorem `thm:model-existence`, revision
  2026-07-01): the concrete model of the corrected axioms.

  The state space is the projective space ℙ ℂ (ℂ^N) (rays of nonzero
  vectors), with the Fubini--Study kernel

      K([u], [v]) = 1 - ‖⟪u, v⟫‖² / (‖u‖² ‖v‖²),

  well-defined on rays. This file machine-checks:

  * `model N : DistinguishabilitySpace (ℙ ℂ (E N))`: the kernel laws,
    including identity of indiscernibles via the equality case of
    Cauchy--Schwarz (`norm_inner_eq_norm_iff`).
  * **Axiom 1(i), existence half**: the standard-basis rays form a
    basis family of size `N` (`basisRay_isBasisFamily`).
  * **Axiom 1(ii), scale-freeness**: the K-image is all of [0,1]
    (`K_image_full`), verified by an explicit two-component family;
    surjectivity is strictly stronger than the density the axiom
    demands.
  * **(C2) Saturation**: `limitCompleteness_model` proves the full
    net/filter form of `SRCv2.LimitCompleteness` for the model, via
    ultrafilter compactness of the unit sphere (finite dimension) and
    continuity of the kernel: a pointwise-convergent net of realized
    profiles has a realized limit. In particular mixed-state profiles,
    not being pointwise limits of pure profiles, are not forced
    (paper Remark `rem:internal-closure`).
  * **(C3), full-basis anchors**: `context_homogeneity_full_basis` and
    the profile-hypothesis form `context_homogeneity_S3` construct the
    paper's explicit antiunitary `D ∘ conj` (diagonal phases
    θ_k = y_k / conj(x_k)) implementing the anchored swap x ↔ y fixing
    every standard-basis ray. This is clause (S3) of Theorem
    `thm:src-master` verified in the model, and the witness lies in the
    antiunitary component of Aut, as the paper's Remark
    `rem:context-boundary` says it must.

  **Remaining gap (documented):** (C3) for *partial* contexts
  (orthonormal anchors of size < N, and the empty and singleton
  anchors consumed by Corollary `cor:homogeneity`) requires the
  cycle-flip gauge construction of the paper's proof (choose phases
  making the swapped Gram matrix equal the conjugated Gram matrix,
  then extend by conjugation on the orthocomplement); its
  formalization needs a Gram-congruence toolkit not yet in Mathlib and
  is left open here. The full-basis case below contains the
  characteristic mechanism (the diagonal-phase antiunitary and the
  automatic involutivity `A y = x`).
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Complex.Norm
import QuantumRelational.Axioms
import QuantumRelational.SRCv2

namespace QuantumRelational
namespace ModelExistence

open Complex Projectivization WithLp
open scoped InnerProductSpace ComplexConjugate LinearAlgebra.Projectivization

/-- The ambient Hilbert space ℂ^N. -/
abbrev E (N : ℕ) := EuclideanSpace ℂ (Fin N)

variable {N : ℕ}

/-! ### The vector-level kernel and its ray invariance -/

/-- The Fubini--Study kernel at the level of (nonzero) vector
representatives. -/
noncomputable def Kvec (u v : E N) : ℝ :=
  1 - ‖⟪u, v⟫_ℂ‖ ^ 2 / (‖u‖ ^ 2 * ‖v‖ ^ 2)

theorem Kvec_smul_left (a : ℂ) (ha : a ≠ 0) (u v : E N)
    (hu : u ≠ 0) (hv : v ≠ 0) : Kvec (a • u) v = Kvec u v := by
  have h1 : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have h2 : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have h3 : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  unfold Kvec
  rw [inner_smul_left, norm_mul, RCLike.norm_conj, norm_smul]
  field_simp

theorem Kvec_smul_right (a : ℂ) (ha : a ≠ 0) (u v : E N)
    (hu : u ≠ 0) (hv : v ≠ 0) : Kvec u (a • v) = Kvec u v := by
  have h1 : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have h2 : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have h3 : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  unfold Kvec
  rw [inner_smul_right, norm_mul, norm_smul]
  field_simp

theorem Kvec_symm (u v : E N) : Kvec u v = Kvec v u := by
  unfold Kvec
  rw [← inner_conj_symm u v, RCLike.norm_conj]
  ring_nf

theorem Kvec_self (u : E N) (hu : u ≠ 0) : Kvec u u = 0 := by
  have h2 : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  unfold Kvec
  rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg u)]
  have hne : (‖u‖ ^ 2 * ‖u‖ ^ 2 : ℝ) ≠ 0 := by positivity
  rw [show ((‖u‖ ^ 2 : ℝ)) ^ 2 = ‖u‖ ^ 2 * ‖u‖ ^ 2 from by ring, div_self hne]
  norm_num

theorem Kvec_nonneg (u v : E N) (hu : u ≠ 0) (hv : v ≠ 0) :
    0 ≤ Kvec u v := by
  have h2 : (0:ℝ) < ‖u‖ := norm_pos_iff.mpr hu
  have h3 : (0:ℝ) < ‖v‖ := norm_pos_iff.mpr hv
  have hcs : ‖⟪u, v⟫_ℂ‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
  have hsq : ‖⟪u, v⟫_ℂ‖ ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hcs 2
  have hden : (0:ℝ) < ‖u‖ ^ 2 * ‖v‖ ^ 2 := by positivity
  unfold Kvec
  rw [sub_nonneg, div_le_one hden]
  calc ‖⟪u, v⟫_ℂ‖ ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := hsq
    _ = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by ring

theorem Kvec_le_one (u v : E N) : Kvec u v ≤ 1 := by
  unfold Kvec
  have : (0:ℝ) ≤ ‖⟪u, v⟫_ℂ‖ ^ 2 / (‖u‖ ^ 2 * ‖v‖ ^ 2) := by positivity
  linarith

/-! ### The ray-level kernel via canonical representatives -/

/-- The Fubini--Study kernel on rays, via the canonical representative
`Projectivization.rep`. `Kray_mk` shows the value is representative-
independent. -/
noncomputable def Kray (p q : ℙ ℂ (E N)) : ℝ := Kvec p.rep q.rep

theorem Kray_mk (u v : E N) (hu : u ≠ 0) (hv : v ≠ 0) :
    Kray (Projectivization.mk ℂ u hu) (Projectivization.mk ℂ v hv)
      = Kvec u v := by
  obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep ℂ u hu
  obtain ⟨b, hb⟩ := exists_smul_eq_mk_rep ℂ v hv
  unfold Kray
  have hau : ((a : ℂ)) • u ≠ 0 := smul_ne_zero a.ne_zero hu
  rw [← ha, ← hb, Units.smul_def, Units.smul_def,
      Kvec_smul_right _ b.ne_zero _ _ hau hv,
      Kvec_smul_left _ a.ne_zero _ _ hu hv]

theorem Kray_mk_left (u : E N) (hu : u ≠ 0) (q : ℙ ℂ (E N)) :
    Kray (Projectivization.mk ℂ u hu) q = Kvec u q.rep := by
  conv_lhs =>
    rw [show q = Projectivization.mk ℂ q.rep q.rep_nonzero from (mk_rep q).symm]
  exact Kray_mk u q.rep hu q.rep_nonzero

/-! ### The model is a distinguishability space -/

/-- **The concrete model** (paper Theorem `thm:model-existence`, kernel
laws): rays of ℂ^N with the Fubini--Study kernel form a
distinguishability space. Identity of indiscernibles is the equality
case of Cauchy--Schwarz. -/
noncomputable def model (N : ℕ) : DistinguishabilitySpace (ℙ ℂ (E N)) where
  K := Kray
  K_nonneg p q := by
    unfold Kray
    exact Kvec_nonneg _ _ p.rep_nonzero q.rep_nonzero
  K_le_one p q := by
    unfold Kray
    exact Kvec_le_one _ _
  K_refl p := by
    unfold Kray
    exact Kvec_self _ p.rep_nonzero
  K_symm p q := by
    unfold Kray
    exact Kvec_symm _ _
  K_ident p q h := by
    have hu : p.rep ≠ 0 := p.rep_nonzero
    have hv : q.rep ≠ 0 := q.rep_nonzero
    have h2 : (0:ℝ) < ‖p.rep‖ := norm_pos_iff.mpr hu
    have h3 : (0:ℝ) < ‖q.rep‖ := norm_pos_iff.mpr hv
    -- From K = 0, the Cauchy-Schwarz inequality is saturated.
    have hnum : ‖⟪p.rep, q.rep⟫_ℂ‖ ^ 2 = ‖p.rep‖ ^ 2 * ‖q.rep‖ ^ 2 := by
      have h' : ‖⟪p.rep, q.rep⟫_ℂ‖ ^ 2 / (‖p.rep‖ ^ 2 * ‖q.rep‖ ^ 2) = 1 := by
        unfold Kray Kvec at h
        linarith
      have hden : (‖p.rep‖ ^ 2 * ‖q.rep‖ ^ 2 : ℝ) ≠ 0 := by positivity
      field_simp at h'
      linarith
    have heq : ‖⟪p.rep, q.rep⟫_ℂ‖ = ‖p.rep‖ * ‖q.rep‖ := by
      have hL := Real.sqrt_sq (norm_nonneg (⟪p.rep, q.rep⟫_ℂ))
      have hR := Real.sqrt_sq (le_of_lt (mul_pos h2 h3))
      calc ‖⟪p.rep, q.rep⟫_ℂ‖
          = Real.sqrt (‖⟪p.rep, q.rep⟫_ℂ‖ ^ 2) := hL.symm
        _ = Real.sqrt ((‖p.rep‖ * ‖q.rep‖) ^ 2) := by rw [hnum]; ring_nf
        _ = ‖p.rep‖ * ‖q.rep‖ := hR
    obtain ⟨r, hr, hvu⟩ := (norm_inner_eq_norm_iff hu hv).mp heq
    rw [← mk_rep p, ← mk_rep q, mk_eq_mk_iff']
    exact ⟨r⁻¹, by rw [hvu, smul_smul, inv_mul_cancel₀ hr, one_smul]⟩

/-! ### Axiom 1(i): the standard basis family -/

theorem single_one_ne_zero (k : Fin N) :
    EuclideanSpace.single k (1:ℂ) ≠ 0 := by
  simp [EuclideanSpace.single_eq_zero_iff]

/-- The ray of the `k`-th standard basis vector. -/
noncomputable def basisRay (N : ℕ) (k : Fin N) : ℙ ℂ (E N) :=
  Projectivization.mk ℂ (EuclideanSpace.single k (1:ℂ)) (single_one_ne_zero k)

/-- **Axiom 1(i), existence half**: the `N` standard-basis rays are
mutually fully distinguishable (`K = 1` pairwise). -/
theorem basisRay_isBasisFamily :
    SRCv2.IsBasisFamily (model N) (basisRay N) := by
  intro i j hij
  show Kray (basisRay N i) (basisRay N j) = 1
  unfold basisRay
  rw [Kray_mk _ _ (single_one_ne_zero i) (single_one_ne_zero j)]
  unfold Kvec
  rw [EuclideanSpace.inner_single_left]
  simp [EuclideanSpace.single_apply, hij]

/-! ### Axiom 1(ii): scale-freeness (the K-image is all of [0,1]) -/

/-- **Axiom 1(ii)**: every value `t ∈ [0,1]` is realized as a K-value
(for `N ≥ 2`), witnessed by the pair `e₀` and `√(1-t)·e₀ + √t·e₁`. -/
theorem K_image_full {n : ℕ} (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ p q : ℙ ℂ (E (n+2)), (model (n+2)).K p q = t := by
  have hne01 : (0 : Fin (n+2)) ≠ 1 := by
    intro h
    have := congrArg Fin.val h
    simp at this
  set s0 : E (n+2) := EuclideanSpace.single 0 (1:ℂ) with hs0
  set s1 : E (n+2) := EuclideanSpace.single 1 (1:ℂ) with hs1
  have h1t : (0:ℝ) ≤ 1 - t := by linarith
  set a : ℂ := (Real.sqrt (1-t) : ℂ) with ha_def
  set b : ℂ := (Real.sqrt t : ℂ) with hb_def
  set v : E (n+2) := a • s0 + b • s1 with hv
  -- The four base inner products.
  have h00 : ⟪s0, s0⟫_ℂ = 1 := by
    rw [hs0, EuclideanSpace.inner_single_left]
    simp [EuclideanSpace.single_apply]
  have h01 : ⟪s0, s1⟫_ℂ = 0 := by
    rw [hs0, hs1, EuclideanSpace.inner_single_left]
    simp [EuclideanSpace.single_apply, hne01]
  have h10 : ⟪s1, s0⟫_ℂ = 0 := by
    rw [hs0, hs1, EuclideanSpace.inner_single_left]
    simp [EuclideanSpace.single_apply, hne01.symm]
  have h11 : ⟪s1, s1⟫_ℂ = 1 := by
    rw [hs1, EuclideanSpace.inner_single_left]
    simp [EuclideanSpace.single_apply]
  -- Inner products with v.
  have hip0 : ⟪s0, v⟫_ℂ = a := by
    rw [hv]
    simp only [inner_add_right, inner_smul_right, h00, h01]
    ring
  have hipv : ⟪v, v⟫_ℂ = 1 := by
    rw [hv]
    simp only [inner_add_right, inner_add_left, inner_smul_right, inner_smul_left,
      h00, h01, h10, h11]
    rw [ha_def, hb_def, Complex.conj_ofReal, Complex.conj_ofReal]
    have hkey : (↑(Real.sqrt (1-t)) : ℂ) * ↑(Real.sqrt (1-t))
        + (↑(Real.sqrt t) : ℂ) * ↑(Real.sqrt t) = 1 := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul,
          Real.mul_self_sqrt h1t, Real.mul_self_sqrt ht0]
      push_cast
      ring
    linear_combination hkey
  -- Norms.
  have hnv : ‖v‖ ^ 2 = 1 := by
    have h := inner_self_eq_norm_sq (𝕜 := ℂ) v
    rw [hipv] at h
    simpa using h.symm
  have hv0 : v ≠ 0 := by
    intro h
    rw [h] at hnv
    simp at hnv
  have hs00 : s0 ≠ 0 := by rw [hs0]; exact single_one_ne_zero 0
  have hns0 : ‖s0‖ = 1 := by rw [hs0]; simp
  -- Assemble.
  refine ⟨Projectivization.mk ℂ s0 hs00, Projectivization.mk ℂ v hv0, ?_⟩
  show Kray _ _ = t
  rw [Kray_mk _ _ hs00 hv0]
  unfold Kvec
  rw [hip0, hns0, hnv, ha_def, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt h1t]
  norm_num

/-! ### Clause (C2): limit completeness for the model -/

/-- **Clause (C2) verified for the model** (paper Theorem
`thm:model-existence`, (C2)): a pointwise-convergent net of realized
K-profiles has a realized limit. Proof: normalize representatives onto
the unit sphere (compact in finite dimension), pass to an ultrafilter,
extract a limit representative, and use continuity of the kernel at
nonzero points. -/
theorem limitCompleteness_model (N : ℕ) :
    SRCv2.LimitCompleteness (model N) := by
  constructor
  intro ι l hl xs f hf
  haveI := hl
  -- Unit representatives.
  set u : ι → E N := fun i => ((‖(xs i).rep‖⁻¹ : ℝ) : ℂ) • (xs i).rep with hu_def
  have hrep_pos : ∀ i, (0:ℝ) < ‖(xs i).rep‖ :=
    fun i => norm_pos_iff.mpr (xs i).rep_nonzero
  have hu_norm : ∀ i, ‖u i‖ = 1 := by
    intro i
    rw [hu_def]
    simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (inv_pos.mpr (hrep_pos i))]
    exact inv_mul_cancel₀ (ne_of_gt (hrep_pos i))
  have hscal_ne : ∀ i, ((‖(xs i).rep‖⁻¹ : ℝ) : ℂ) ≠ 0 := by
    intro i
    simp only [ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact ne_of_gt (hrep_pos i)
  -- K-values along the net, in terms of the unit representatives.
  have hKu : ∀ i (z : ℙ ℂ (E N)), Kvec (u i) z.rep = Kray (xs i) z := by
    intro i z
    rw [hu_def]
    exact Kvec_smul_left _ (hscal_ne i) _ _ (xs i).rep_nonzero z.rep_nonzero
  -- Ultrafilter refinement and sphere compactness.
  set L : Ultrafilter ι := Ultrafilter.of l with hL_def
  have hL : (L : Filter ι) ≤ l := Ultrafilter.of_le l
  have hmem : ∀ i, u i ∈ Metric.sphere (0 : E N) 1 := by
    intro i
    rw [mem_sphere_zero_iff_norm]
    exact hu_norm i
  have hle : (Ultrafilter.map u L : Filter (E N))
      ≤ Filter.principal (Metric.sphere (0 : E N) 1) := by
    rw [Filter.le_principal_iff, Ultrafilter.coe_map, Filter.mem_map]
    exact Filter.univ_mem' hmem
  obtain ⟨a, ha_mem, ha_le⟩ :=
    (isCompact_sphere (0 : E N) 1).ultrafilter_le_nhds (Ultrafilter.map u L) hle
  have ha_norm : ‖a‖ = 1 := mem_sphere_zero_iff_norm.mp ha_mem
  have ha0 : a ≠ 0 := by
    intro h
    rw [h] at ha_norm
    simp at ha_norm
  have hconv : Filter.Tendsto u (L : Filter ι) (nhds a) := by
    rwa [Filter.Tendsto, ← Ultrafilter.coe_map]
  refine ⟨Projectivization.mk ℂ a ha0, fun z => ?_⟩
  -- Continuity of w ↦ Kvec w z.rep at a.
  have hzn : ‖z.rep‖ ≠ 0 := norm_ne_zero_iff.mpr z.rep_nonzero
  have han : (‖a‖ ^ 2 * ‖z.rep‖ ^ 2 : ℝ) ≠ 0 := by
    rw [ha_norm]
    simpa using pow_ne_zero 2 hzn
  have hcont : ContinuousAt (fun w : E N => Kvec w z.rep) a := by
    unfold Kvec
    apply ContinuousAt.sub continuousAt_const
    apply ContinuousAt.div
    · exact ((continuous_id.inner continuous_const).norm.pow 2).continuousAt
    · exact ((continuous_norm.pow 2).mul continuous_const).continuousAt
    · exact han
  -- Two limits along the ultrafilter agree.
  have h1 : Filter.Tendsto (fun i => Kvec (u i) z.rep) (L : Filter ι)
      (nhds (Kvec a z.rep)) := hcont.tendsto.comp hconv
  have h2 : Filter.Tendsto (fun i => Kvec (u i) z.rep) (L : Filter ι)
      (nhds (f z)) := by
    have heq : (fun i => Kvec (u i) z.rep) = fun i => Kray (xs i) z :=
      funext fun i => hKu i z
    rw [heq]
    exact (hf z).mono_left hL
  have hfz : Kvec a z.rep = f z := tendsto_nhds_unique h1 h2
  show Kray _ z = f z
  rw [Kray_mk_left a ha0 z]
  exact hfz

/-! ### Clause (C3), full-basis anchors: the explicit antiunitary -/

section FullBasisAnchor

variable (x y : E N)

/-- The diagonal phases `θ_k = y_k / conj(x_k)` of the paper's
construction (with the convention `θ_k = 1` where `x_k = 0`). -/
noncomputable def theta (k : Fin N) : ℂ :=
  if x k = 0 then 1 else y k / conj (x k)

variable {x y}

theorem theta_conj_mul (hmod : ∀ k, normSq (x k) = normSq (y k)) (k : Fin N) :
    conj (theta x y k) * theta x y k = 1 := by
  unfold theta
  by_cases hx : x k = 0
  · simp [hx]
  · have hxs : normSq (x k) ≠ 0 := by
      simpa [Complex.normSq_eq_zero] using hx
    rw [if_neg hx]
    have hval : conj (y k / conj (x k)) * (y k / conj (x k))
        = ((normSq (y k) / normSq (x k) : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj]
      rw [Complex.normSq_div, Complex.normSq_conj]
    rw [hval, ← hmod k, div_self hxs]
    norm_num

theorem theta_ne_zero (hmod : ∀ k, normSq (x k) = normSq (y k)) (k : Fin N) :
    theta x y k ≠ 0 := by
  intro h
  have hc := theta_conj_mul hmod k
  rw [h, mul_zero] at hc
  exact zero_ne_one hc

variable (x y)

/-- The antiunitary `A = D ∘ conj`: componentwise conjugation followed
by the diagonal phases. -/
noncomputable def Amap (v : E N) : E N :=
  toLp 2 (fun k => theta x y k * conj (v k))

variable {x y}

theorem Amap_apply (v : E N) (k : Fin N) :
    Amap x y v k = theta x y k * conj (v k) := rfl

theorem Amap_involutive (hmod : ∀ k, normSq (x k) = normSq (y k)) :
    Function.Involutive (Amap x y) := by
  intro v
  ext k
  rw [Amap_apply, Amap_apply, map_mul]
  have hθ := theta_conj_mul hmod k
  calc theta x y k * (conj (theta x y k) * conj (conj (v k)))
      = (conj (theta x y k) * theta x y k) * conj (conj (v k)) := by ring
    _ = v k := by rw [hθ, one_mul, Complex.conj_conj]

theorem Amap_smul (a : ℂ) (v : E N) :
    Amap x y (a • v) = conj a • Amap x y v := by
  ext k
  rw [Amap_apply]
  simp only [PiLp.smul_apply, smul_eq_mul, map_mul]
  rw [Amap_apply]
  ring

theorem Amap_ne_zero (hmod : ∀ k, normSq (x k) = normSq (y k))
    {v : E N} (hv : v ≠ 0) : Amap x y v ≠ 0 := by
  intro h
  apply hv
  ext k
  have hk : Amap x y v k = 0 := by rw [h]; rfl
  rw [Amap_apply] at hk
  rcases mul_eq_zero.mp hk with h1 | h2
  · exact absurd h1 (theta_ne_zero hmod k)
  · have hvk : v k = 0 := by
      have := congrArg conj h2
      simpa using this
    simpa using hvk

/-- The antiunitary conjugates inner products. -/
theorem Amap_inner (hmod : ∀ k, normSq (x k) = normSq (y k)) (u v : E N) :
    ⟪Amap x y u, Amap x y v⟫_ℂ = conj ⟪u, v⟫_ℂ := by
  rw [PiLp.inner_apply, PiLp.inner_apply, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [RCLike.inner_apply, RCLike.inner_apply, Amap_apply, Amap_apply]
  have hθ := theta_conj_mul hmod k
  simp only [map_mul, Complex.conj_conj]
  linear_combination ((starRingEnd ℂ) (v k) * u k) * hθ

theorem Amap_norm_sq (hmod : ∀ k, normSq (x k) = normSq (y k)) (v : E N) :
    ‖Amap x y v‖ ^ 2 = ‖v‖ ^ 2 := by
  have h1 := inner_self_eq_norm_sq (𝕜 := ℂ) (Amap x y v)
  have h2 := inner_self_eq_norm_sq (𝕜 := ℂ) v
  rw [← h1, ← h2, Amap_inner hmod]
  exact RCLike.conj_re _

theorem Amap_Kvec (hmod : ∀ k, normSq (x k) = normSq (y k)) (u v : E N) :
    Kvec (Amap x y u) (Amap x y v) = Kvec u v := by
  unfold Kvec
  rw [Amap_inner hmod, RCLike.norm_conj, Amap_norm_sq hmod, Amap_norm_sq hmod]

/-- `A x = y` (exact vector equality, from the phase choice). -/
theorem Amap_x (hmod : ∀ k, normSq (x k) = normSq (y k)) :
    Amap x y x = y := by
  ext k
  rw [Amap_apply]
  unfold theta
  by_cases hx : x k = 0
  · have hy : y k = 0 := by
      have h := hmod k
      rw [hx] at h
      simp only [map_zero] at h
      exact Complex.normSq_eq_zero.mp h.symm
    rw [if_pos hx, hx, hy]
    simp
  · rw [if_neg hx]
    have hcx : conj (x k) ≠ 0 := by simpa using hx
    field_simp

/-- `A y = x` (automatic from `|y_k| = |x_k|`; the paper's
`|y_k|²/conj(x_k) = x_k` computation). -/
theorem Amap_y (hmod : ∀ k, normSq (x k) = normSq (y k)) :
    Amap x y y = x := by
  ext k
  rw [Amap_apply]
  unfold theta
  by_cases hx : x k = 0
  · have hy : y k = 0 := by
      have h := hmod k
      rw [hx] at h
      simp only [map_zero] at h
      exact Complex.normSq_eq_zero.mp h.symm
    rw [if_pos hx, hx, hy]
    simp
  · rw [if_neg hx]
    have hcx : conj (x k) ≠ 0 := by simpa using hx
    have hyc : y k * conj (y k) = x k * conj (x k) := by
      have h1 := Complex.mul_conj (y k)
      have h2 := Complex.mul_conj (x k)
      rw [h1, h2, ← hmod k]
    field_simp
    calc y k * conj (y k) = x k * conj (x k) := hyc
      _ = conj (x k) * x k := by ring

/-- `A` fixes each standard basis vector up to the phase `θ_j`. -/
theorem Amap_single (j : Fin N) :
    Amap x y (EuclideanSpace.single j (1:ℂ))
      = theta x y j • EuclideanSpace.single j (1:ℂ) := by
  ext k
  rw [Amap_apply]
  simp only [PiLp.smul_apply, smul_eq_mul, EuclideanSpace.single_apply]
  by_cases hk : k = j
  · simp [hk]
  · simp [hk]

/-- The descended ray map. -/
noncomputable def grayFun (hmod : ∀ k, normSq (x k) = normSq (y k)) :
    ℙ ℂ (E N) → ℙ ℂ (E N) :=
  fun p => Projectivization.mk ℂ (Amap x y p.rep)
    (Amap_ne_zero hmod p.rep_nonzero)

theorem grayFun_mk (hmod : ∀ k, normSq (x k) = normSq (y k))
    (v : E N) (hv : v ≠ 0) :
    grayFun hmod (Projectivization.mk ℂ v hv)
      = Projectivization.mk ℂ (Amap x y v) (Amap_ne_zero hmod hv) := by
  unfold grayFun
  obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep ℂ v hv
  rw [mk_eq_mk_iff']
  refine ⟨conj (a : ℂ), ?_⟩
  have hrep : ((a : ℂ)) • v = (Projectivization.mk ℂ v hv).rep := by
    rw [← Units.smul_def]
    exact ha
  rw [← hrep, ← Amap_smul]

theorem grayFun_involutive (hmod : ∀ k, normSq (x k) = normSq (y k)) :
    Function.Involutive (grayFun hmod) := by
  intro p
  conv_lhs =>
    rw [show p = Projectivization.mk ℂ p.rep p.rep_nonzero from (mk_rep p).symm]
  rw [grayFun_mk hmod, grayFun_mk hmod]
  have h := Amap_involutive (x := x) (y := y) hmod p.rep
  conv_rhs => rw [← mk_rep p]
  rw [mk_eq_mk_iff']
  exact ⟨1, by rw [one_smul, h]⟩

/-- **Clause (C3) for full-basis anchors** (paper Theorem
`thm:model-existence`, clause (C3), full-basis case; equivalently
clause (S3) of Theorem `thm:src-master` verified in the model): if `x`
and `y` have equal componentwise moduli in the standard basis, an
automorphism of the model fixes every standard-basis ray and swaps the
rays of `x` and `y`. The witness is the antiunitary `D ∘ conj`; it lies
in the antiunitary component of `Aut`, as Remark `rem:context-boundary`
requires. -/
theorem context_homogeneity_full_basis (x y : E N) (hx : x ≠ 0) (hy : y ≠ 0)
    (hmod : ∀ k, normSq (x k) = normSq (y k)) :
    ∃ g : Equiv.Perm (ℙ ℂ (E N)),
      IsKAutomorphism (model N) g ∧
      (∀ k, g (basisRay N k) = basisRay N k) ∧
      g (Projectivization.mk ℂ x hx) = Projectivization.mk ℂ y hy ∧
      g (Projectivization.mk ℂ y hy) = Projectivization.mk ℂ x hx := by
  refine ⟨(grayFun_involutive hmod).toPerm, ?_, ?_, ?_, ?_⟩
  · -- K-preservation
    intro p q
    show Kray (grayFun hmod p) (grayFun hmod q) = Kray p q
    unfold grayFun
    rw [Kray_mk]
    exact Amap_Kvec hmod p.rep q.rep
  · -- basis rays fixed
    intro k
    show grayFun hmod (basisRay N k) = basisRay N k
    unfold basisRay
    rw [grayFun_mk hmod]
    rw [mk_eq_mk_iff']
    refine ⟨theta x y k, ?_⟩
    rw [Amap_single]
  · -- x ↦ y
    show grayFun hmod (Projectivization.mk ℂ x hx) = Projectivization.mk ℂ y hy
    rw [grayFun_mk hmod]
    rw [mk_eq_mk_iff']
    exact ⟨1, by rw [one_smul, Amap_x hmod]⟩
  · -- y ↦ x
    show grayFun hmod (Projectivization.mk ℂ y hy) = Projectivization.mk ℂ x hx
    rw [grayFun_mk hmod]
    rw [mk_eq_mk_iff']
    exact ⟨1, by rw [one_smul, Amap_y hmod]⟩

end FullBasisAnchor

/-! ### (S3) in profile form -/

/-- The K-profile of a ray against a standard-basis ray, in closed
form. -/
theorem Kray_basisRay (v : E N) (hv : v ≠ 0) (k : Fin N) :
    Kray (Projectivization.mk ℂ v hv) (basisRay N k)
      = 1 - ‖v k‖ ^ 2 / ‖v‖ ^ 2 := by
  unfold basisRay
  rw [Kray_mk _ _ hv (single_one_ne_zero k)]
  unfold Kvec
  rw [EuclideanSpace.inner_single_right]
  simp only [one_mul, RCLike.norm_conj]
  rw [show ‖EuclideanSpace.single k (1:ℂ)‖ = (1:ℝ) by simp]
  norm_num

/-- **(S3) for the model, profile form** (paper Theorem
`thm:src-master`(S3) verified in the model): states with equal
K-profiles against the standard basis are swapped by an automorphism
fixing every basis ray. The moduli hypothesis of
`context_homogeneity_full_basis` is recovered by rescaling the second
representative to match norms. -/
theorem context_homogeneity_S3 (x y : E N) (hx : x ≠ 0) (hy : y ≠ 0)
    (hprof : ∀ k, (model N).K (Projectivization.mk ℂ x hx) (basisRay N k)
      = (model N).K (Projectivization.mk ℂ y hy) (basisRay N k)) :
    ∃ g : Equiv.Perm (ℙ ℂ (E N)),
      IsKAutomorphism (model N) g ∧
      (∀ k, g (basisRay N k) = basisRay N k) ∧
      g (Projectivization.mk ℂ x hx) = Projectivization.mk ℂ y hy ∧
      g (Projectivization.mk ℂ y hy) = Projectivization.mk ℂ x hx := by
  have hnx : (0:ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  have hny : (0:ℝ) < ‖y‖ := norm_pos_iff.mpr hy
  -- Rescale y to match the norm of x.
  set c : ℝ := ‖x‖ / ‖y‖ with hc
  have hcpos : (0:ℝ) < c := div_pos hnx hny
  have hcne : ((c:ℝ):ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hcpos
  set y' : E N := ((c:ℝ):ℂ) • y with hy'
  have hy'0 : y' ≠ 0 := smul_ne_zero hcne hy
  -- Ray identity: mk y' = mk y.
  have hmk_y : Projectivization.mk ℂ y' hy'0 = Projectivization.mk ℂ y hy := by
    rw [mk_eq_mk_iff']
    exact ⟨((c:ℝ):ℂ), rfl⟩
  -- Componentwise moduli match after rescaling.
  have hmod : ∀ k, normSq (x k) = normSq (y' k) := by
    intro k
    have hpk := hprof k
    rw [show (model N).K = Kray from rfl, Kray_basisRay x hx k,
        Kray_basisRay y hy k] at hpk
    have hratio : ‖x k‖ ^ 2 / ‖x‖ ^ 2 = ‖y k‖ ^ 2 / ‖y‖ ^ 2 := by linarith
    have hy'k : y' k = ((c:ℝ):ℂ) * y k := by
      rw [hy']
      simp [PiLp.smul_apply]
    have hx2 : (‖x‖ ^ 2 : ℝ) ≠ 0 := by positivity
    have hy2 : (‖y‖ ^ 2 : ℝ) ≠ 0 := by positivity
    have hcross : ‖x k‖ ^ 2 * ‖y‖ ^ 2 = ‖y k‖ ^ 2 * ‖x‖ ^ 2 := by
      field_simp at hratio
      linarith
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hy'k,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos,
        mul_pow, hc, div_pow]
    rw [div_mul_eq_mul_div, eq_div_iff hy2]
    linarith
  obtain ⟨g, hgK, hgB, hgx, hgy⟩ :=
    context_homogeneity_full_basis x y' hx hy'0 hmod
  refine ⟨g, hgK, hgB, ?_, ?_⟩
  · rw [hgx, hmk_y]
  · rw [← hmk_y]
    exact hgy

end ModelExistence
end QuantumRelational
