/-
  QuantumRelational/Paper2/DimensionSelection.lean

  **Paper 2 (revision 2026-07-05): the corrected D = 3 selection**
  (paper Theorems `thm:recurrence`, `thm:bound-states`,
  `thm:d3-unique`).

  This module machine-checks the analytic and arithmetic content of
  the corrected dimension-selection argument:

  * `heatKernel_summable_iff`: the total return mass Σ_t t^{-D/2} of
    the heat kernel converges iff D > 2. Combined with the
    Hebisch--Saloff-Coste bound p_t ≍ t^{-D/2} (imported as cited
    mathematics in the paper), this is the recurrence/transience
    threshold of Varopoulos' theorem: permanent escape (S2) needs
    D ≥ 3.
  * `fall_to_center`: for D ≥ 5, the variational energy
    E(λ) = T·λ² − V·λ^{D−2} tends to −∞ as the trial state shrinks
    (λ → ∞): fall to the center. This replaces the earlier draft's
    erroneous Kato--Rellich argument (paper Theorem
    `thm:bound-states`(iv), corrected): for D ≥ 5 the failure mode is
    catastrophic collapse, not absence of binding.
  * `no_collapse_at_three`: at D = 3 the same variational energy is
    bounded below (the exponent comparison 1 < 2), the arithmetic
    shadow of the hydrogen tower's stability.
  * `subcritical_tail_iff` / `unique_selfconsistent`: the propagator
    tail exponent γ = D − 2 is subcritical (γ < 2) among transient
    degrees iff D = 3; the unique growth degree satisfying both
    stability requirements is 3.
  * `selection_forces_flatness`: combining the selection with the
    Bass--Guivarc'h classification (`GrowthDegree.flatness_at_three`),
    the selected translation structure is virtually ℤ³. The
    Heisenberg profile is excluded at D = 4 by `heisenberg_at_four`.

  Lean status: fully-derived (0 sorry, 0 axiom beyond the standard
  three).
-/
import Mathlib.Analysis.PSeries
import Mathlib.Order.Filter.AtTopBot.Ring
import Mathlib.Tactic
import QuantumRelational.Paper2.GrowthDegree

namespace QuantumRelational.Paper2.DimensionSelection

open Filter
open QuantumRelational.Paper2.GrowthDegree

/-! ### Recurrence threshold (paper Theorem `thm:recurrence`) -/

/-- **Heat-kernel return-mass threshold.** With p_t(x,x) ≍ t^{-D/2} on
a vertex-transitive graph of growth degree D (Hebisch--Saloff-Coste),
the total return mass converges iff D > 2: the walk is transient iff
the growth degree is at least three. This is the summability core of
Varopoulos' theorem. -/
theorem heatKernel_summable_iff (D : ℕ) :
    Summable (fun t : ℕ => ((t : ℝ) ^ ((D : ℝ) / 2))⁻¹) ↔ 2 < D := by
  rw [Real.summable_nat_rpow_inv]
  constructor
  · intro h
    have h2 : (2 : ℝ) < (D : ℝ) := by linarith
    exact_mod_cast h2
  · intro h
    have h2 : (2 : ℝ) < (D : ℝ) := by exact_mod_cast h
    linarith

/-- Permanent escape (S2) fails for D ≤ 2: the return mass diverges,
the walk is recurrent, and no emission is final. -/
theorem recurrent_of_le_two {D : ℕ} (h : D ≤ 2) :
    ¬ Summable (fun t : ℕ => ((t : ℝ) ^ ((D : ℝ) / 2))⁻¹) := by
  rw [heatKernel_summable_iff]; omega

/-- Permanent escape (S2) holds from D = 3 on. -/
theorem transient_of_three_le {D : ℕ} (h : 3 ≤ D) :
    Summable (fun t : ℕ => ((t : ℝ) ^ ((D : ℝ) / 2))⁻¹) :=
  (heatKernel_summable_iff D).mpr (by omega)

/-! ### Fall to the center (paper Theorem `thm:bound-states`(iv),
corrected) -/

/-- **Fall to the center at D ≥ 5.** For the propagator-mediated
attraction V(r) ~ −α/r^{D−2}, a trial state of spatial extent 1/λ has
energy E(λ) = T·λ² − V·λ^{D−2}. For D ≥ 5 the potential exponent
exceeds the kinetic one and E(λ) → −∞: the continuum operator is
unbounded below for every coupling, and lattice states collapse to the
cutoff scale. This corrects the earlier draft's Kato--Rellich
argument. -/
theorem fall_to_center {T V : ℝ} (_hT : 0 < T) (hV : 0 < V) {D : ℕ}
    (hD : 5 ≤ D) :
    Tendsto (fun lam : ℝ => T * lam ^ 2 - V * lam ^ (D - 2))
      atTop atBot := by
  have hexp : D - 2 = (D - 4) + 2 := by omega
  have hfac : (fun lam : ℝ => T * lam ^ 2 - V * lam ^ (D - 2))
      = fun lam : ℝ => (T - V * lam ^ (D - 4)) * lam ^ 2 := by
    funext lam
    rw [hexp, pow_add]
    ring
  rw [hfac]
  have hpow : Tendsto (fun lam : ℝ => lam ^ (D - 4)) atTop atTop :=
    tendsto_pow_atTop (by omega : D - 4 ≠ 0)
  have hVpow : Tendsto (fun lam : ℝ => V * lam ^ (D - 4)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hV).mpr hpow
  have hneg : Tendsto (fun lam : ℝ => T - V * lam ^ (D - 4)) atTop atBot := by
    have := tendsto_neg_atTop_atBot.comp hVpow
    have h2 : Tendsto (fun lam : ℝ => T + -(V * lam ^ (D - 4))) atTop atBot :=
      tendsto_atBot_add_const_left atTop T this
    simpa [sub_eq_add_neg] using h2
  have hsq : Tendsto (fun lam : ℝ => lam ^ 2) atTop atTop :=
    tendsto_pow_atTop (two_ne_zero)
  exact hneg.atBot_mul_atTop₀ hsq

/-- **No collapse at D = 3**: the trial energy T·λ² − V·λ is bounded
below (the potential exponent 1 = D − 2 is subcritical against the
kinetic exponent 2). The arithmetic shadow of the hydrogen tower's
stability; the full spectral statement is cited mathematics in the
paper. -/
theorem no_collapse_at_three {T V : ℝ} (hT : 0 < T) :
    ∃ B : ℝ, ∀ lam : ℝ, B ≤ T * lam ^ 2 - V * lam ^ (3 - 2) := by
  refine ⟨-(V ^ 2 / (4 * T)), fun lam => ?_⟩
  have h4T : (0 : ℝ) < 4 * T := by positivity
  have hpow : lam ^ (3 - 2) = lam := by norm_num
  rw [hpow, ← neg_div, div_le_iff₀ h4T]
  nlinarith [sq_nonneg (2 * T * lam - V)]

/-! ### The selection (paper Theorem `thm:d3-unique`) -/

/-- The propagator tail exponent γ = D − 2 is subcritical (γ < 2)
among transient degrees iff D = 3. -/
theorem subcritical_tail_iff (D : ℕ) (h3 : 3 ≤ D) : D - 2 < 2 ↔ D = 3 := by
  omega

/-- **Unique self-consistency** (paper Theorem `thm:d3-unique`,
arithmetic core): the unique growth degree satisfying permanent escape
(transience: 2 < D) and geometry-scale localization (subcritical tail:
D − 2 < 2) is D = 3. -/
theorem unique_selfconsistent (D : ℕ) : (2 < D ∧ D - 2 < 2) ↔ D = 3 := by
  omega

/-- **Selection forces flatness** (paper Theorem `thm:d3-unique`,
final clause): a translation structure whose growth degree passes both
stability requirements has abelianization rank three and all higher
layers torsion, i.e. it is virtually ℤ³. Space is flat by theorem. -/
theorem selection_forces_flatness (R : GrowthRanks)
    (hesc : 2 < R.degree) (hloc : R.degree - 2 < 2) :
    R.r 1 = 3 ∧ R.IsFlat :=
  R.flatness_at_three ((unique_selfconsistent R.degree).mp ⟨hesc, hloc⟩)

/-- The Heisenberg translation structure sits at growth degree four
and fails the localization requirement exactly as ℤ⁴ does: it is not
a competitor at D = 3. -/
theorem heisenberg_at_four :
    heisenbergRanks.degree = 4 ∧
      ¬ (2 < heisenbergRanks.degree ∧ heisenbergRanks.degree - 2 < 2) := by
  refine ⟨degree_heisenberg, ?_⟩
  rw [degree_heisenberg]
  omega

end QuantumRelational.Paper2.DimensionSelection
