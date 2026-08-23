/-
  QuantumRelational/Paper2/GrowthDegree.lean

  **Paper 2 (revision 2026-07-05): the Bass--Guivarc'h arithmetic and
  the Flatness Theorem** (paper Theorems `thm:integer-dimension`,
  `thm:translation-group`).

  For a finitely generated nilpotent translation structure with lower
  central series ranks r_m = rank(γ_m/γ_{m+1}), the growth degree is
  the Bass--Guivarc'h sum

      D = Σ_m m · r_m.

  We formalize the *arithmetic core* of the paper's classification:
  the group-theoretic inputs (Trofimov, Gromov, Bass--Guivarc'h, and
  the degree-one generation of the rational lower central series) are
  encoded as the two structure fields `supp` and `gen`, and everything
  downstream is machine-checked:

  * `degree` is a non-negative integer by construction: **integer
    dimension holds before and without flatness** (paper Theorem
    `thm:integer-dimension`).
  * `flatness_at_three`: D = 3 forces r₁ = 3 and all higher ranks
    zero, i.e. the translation structure is virtually ℤ³. **Flatness
    is a theorem at D = 3, not an assumption** (paper Theorem
    `thm:translation-group`(ii)).
  * `classification_low`: the same at D = 1, 2 (virtually ℤ, ℤ²),
    matching Varopoulos' recurrent classes.
  * `dichotomy_at_four`: D = 4 admits exactly two rank profiles,
    ℤ⁴-type (r₁ = 4) and Heisenberg-type (r₁ = 2, r₂ = 1). Growth
    degree four is the first dimension where curved (non-abelian)
    translation structure is possible.
  * `heisenbergRanks`: the discrete Heisenberg group's rank data,
    with `degree_heisenberg : degree = 4` and hence excluded by the
    D = 3 selection exactly as ℤ⁴ is.

  The `gen` field encodes: if the abelianization has rank ≤ 1, all
  higher rational layers vanish (the lower central series is generated
  in degree one; a nilpotent group with rationally-cyclic
  abelianization is virtually abelian). This is the only
  group-theoretic fact imported; it is stated as a hypothesis, not an
  axiom.

  Lean status: fully-derived (0 sorry, 0 axiom beyond the standard
  three).
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace QuantumRelational.Paper2.GrowthDegree

/-- Rank data of a finitely generated nilpotent translation structure:
`r m` is the rank of the m-th rational lower-central-series layer.
`supp` records finite nilpotency class; `gen` records degree-one
generation of the rational lower central series (rank-≤-1
abelianization forces all higher layers to vanish). -/
structure GrowthRanks where
  /-- Layer ranks r_m = rank(γ_m/γ_{m+1}); the m = 0 slot is unused. -/
  r : ℕ → ℕ
  /-- Nilpotency window: layers vanish from `n` on. -/
  n : ℕ
  /-- Finite nilpotency class. -/
  supp : ∀ m, n ≤ m → r m = 0
  /-- Degree-one generation: rationally cyclic or trivial
      abelianization kills every higher layer. -/
  gen : r 1 ≤ 1 → ∀ m, 2 ≤ m → r m = 0

namespace GrowthRanks

variable (R : GrowthRanks)

/-- The Bass--Guivarc'h growth degree `D = Σ_m m · r_m`, summed over a
window large enough to contain all nonzero layers. -/
def degree : ℕ := ∑ m ∈ Finset.range (R.n + 3), m * R.r m

/-- Partial Bass--Guivarc'h sum from layer `k` up. -/
def tailFrom (k : ℕ) : ℕ := ∑ m ∈ Finset.Ico k (R.n + 3), m * R.r m

theorem degree_split : R.degree = R.r 1 + R.tailFrom 2 := by
  unfold degree tailFrom
  rw [Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive (fun m => m * R.r m)
      (Nat.zero_le 2) (by omega : 2 ≤ R.n + 3)]
  congr 1
  rw [Nat.Ico_zero_eq_range, Finset.sum_range_succ, Finset.sum_range_one]
  simp

theorem tailFrom_split : R.tailFrom 2 = 2 * R.r 2 + R.tailFrom 3 := by
  unfold tailFrom
  rw [← Finset.sum_Ico_consecutive (fun m => m * R.r m)
      (by omega : 2 ≤ 3) (by omega : 3 ≤ R.n + 3)]
  congr 1

theorem tailFrom_eq_zero_iff (k : ℕ) (hk : 1 ≤ k) :
    R.tailFrom k = 0 ↔ ∀ m, k ≤ m → R.r m = 0 := by
  unfold tailFrom
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h m hm
    by_cases hmW : m < R.n + 3
    · have hterm := h m (Finset.mem_Ico.mpr ⟨hm, hmW⟩)
      rcases Nat.mul_eq_zero.mp hterm with h0 | h0
      · omega
      · exact h0
    · exact R.supp m (by omega)
  · intro h m hm
    rw [h m (Finset.mem_Ico.mp hm).1, Nat.mul_zero]

theorem tailFrom_ge (k : ℕ) (h : R.tailFrom k ≠ 0) : k ≤ R.tailFrom k := by
  unfold tailFrom at h ⊢
  obtain ⟨m, hm, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hle : m * R.r m ≤ ∑ m ∈ Finset.Ico k (R.n + 3), m * R.r m :=
    Finset.single_le_sum (f := fun m => m * R.r m)
      (fun i _ => Nat.zero_le _) hm
  have hmk : k ≤ m := (Finset.mem_Ico.mp hm).1
  have hr : 1 ≤ R.r m := Nat.one_le_iff_ne_zero.mpr (by
    intro h0; exact hne (by rw [h0, Nat.mul_zero]))
  calc k ≤ m := hmk
    _ = m * 1 := (Nat.mul_one m).symm
    _ ≤ m * R.r m := Nat.mul_le_mul_left m hr
    _ ≤ _ := hle

/-- Flatness: all layers above the abelianization are torsion, so the
translation structure is virtually abelian (virtually ℤ^{r₁}). -/
def IsFlat : Prop := ∀ m, 2 ≤ m → R.r m = 0

theorem degree_of_flat (h : R.IsFlat) : R.degree = R.r 1 := by
  have ht : R.tailFrom 2 = 0 := (R.tailFrom_eq_zero_iff 2 (by omega)).mpr h
  have := R.degree_split
  omega

/-- **Integer dimension** (paper Theorem `thm:integer-dimension`): the
growth degree is a natural number by construction, for every
admissible rank profile, abelian or not. Stated explicitly as the
paper does: the Bass--Guivarc'h sum quantizes spatial dimension before
flatness is available. -/
theorem degree_integer : ∃ D : ℕ, R.degree = D := ⟨R.degree, rfl⟩

/-- **Low-degree classification** (paper Theorem
`thm:translation-group`(i),(ii)): at growth degree D ∈ {1, 2, 3} the
translation structure is virtually ℤ^D. In particular **flatness is
forced at D = 3**. -/
theorem classification_low (hD : R.degree = 1 ∨ R.degree = 2 ∨ R.degree = 3) :
    R.r 1 = R.degree ∧ R.IsFlat := by
  rcases Nat.lt_or_ge (R.r 1) 2 with h1 | h1
  · have hflat : R.IsFlat := R.gen (by omega)
    have hdeg := R.degree_of_flat hflat
    exact ⟨by omega, hflat⟩
  · have hsplit := R.degree_split
    rcases eq_or_ne (R.tailFrom 2) 0 with ht | ht
    · have hflat : R.IsFlat := (R.tailFrom_eq_zero_iff 2 (by omega)).mp ht
      exact ⟨by omega, hflat⟩
    · have := R.tailFrom_ge 2 ht
      exfalso; omega

/-- **The Flatness Theorem** (paper Theorem `thm:translation-group`(ii)):
growth degree three forces rank three and virtual abelianness. No
curved (non-abelian nilpotent) translation structure exists in three
dimensions. -/
theorem flatness_at_three (hD : R.degree = 3) : R.r 1 = 3 ∧ R.IsFlat := by
  obtain ⟨h1, h2⟩ := R.classification_low (Or.inr (Or.inr hD))
  exact ⟨by omega, h2⟩

/-- **The D = 4 dichotomy** (paper Theorem `thm:translation-group`(iii)):
growth degree four admits exactly the flat profile (r₁ = 4, virtually
ℤ⁴) and the Heisenberg profile (r₁ = 2, r₂ = 1). Four is the first
growth degree at which non-flat translation structure is possible. -/
theorem dichotomy_at_four (hD : R.degree = 4) :
    (R.r 1 = 4 ∧ R.IsFlat) ∨
      (R.r 1 = 2 ∧ R.r 2 = 1 ∧ ∀ m, 3 ≤ m → R.r m = 0) := by
  have hsplit := R.degree_split
  rcases Nat.lt_or_ge (R.r 1) 2 with h1 | h1
  · have hflat : R.IsFlat := R.gen (by omega)
    have hdeg := R.degree_of_flat hflat
    exfalso; omega
  · rcases eq_or_ne (R.tailFrom 2) 0 with ht | ht
    · exact Or.inl ⟨by omega, (R.tailFrom_eq_zero_iff 2 (by omega)).mp ht⟩
    · have ht2 := R.tailFrom_ge 2 ht
      have hsplit3 := R.tailFrom_split
      rcases eq_or_ne (R.tailFrom 3) 0 with ht3 | ht3
      · have h3 := (R.tailFrom_eq_zero_iff 3 (by omega)).mp ht3
        exact Or.inr ⟨by omega, by omega, h3⟩
      · have := R.tailFrom_ge 3 ht3
        exfalso; omega

end GrowthRanks

/-! ### Concrete instances: ℤ^d and the discrete Heisenberg group -/

/-- The rank profile of ℤ^d: a single degree-one layer of rank d. -/
def flatRanks (d : ℕ) : GrowthRanks where
  r := fun m => if m = 1 then d else 0
  n := 2
  supp := by
    intro m hm
    have hne : m ≠ 1 := by omega
    simp [hne]
  gen := by
    intro _ m hm
    have hne : m ≠ 1 := by omega
    simp [hne]

theorem degree_flatRanks (d : ℕ) : (flatRanks d).degree = d := by
  simp [GrowthRanks.degree, flatRanks]

theorem flatRanks_isFlat (d : ℕ) : (flatRanks d).IsFlat := by
  intro m hm
  have hne : m ≠ 1 := by omega
  simp [flatRanks, hne]

/-- The rank profile of the discrete Heisenberg group H₃(ℤ):
abelianization rank 2, one central layer of rank 1. -/
def heisenbergRanks : GrowthRanks where
  r := fun m => if m = 1 then 2 else if m = 2 then 1 else 0
  n := 3
  supp := by
    intro m hm
    have h1 : m ≠ 1 := by omega
    have h2 : m ≠ 2 := by omega
    simp [h1, h2]
  gen := by intro h; simp at h

/-- The Heisenberg geometry has growth degree four (Bass--Guivarc'h:
D = 1·2 + 2·1 = 4). -/
theorem degree_heisenberg : heisenbergRanks.degree = 4 := by
  simp [GrowthRanks.degree, heisenbergRanks, Finset.sum_range_succ]

theorem heisenberg_not_flat : ¬ heisenbergRanks.IsFlat := by
  intro h
  have := h 2 (by omega)
  simp [heisenbergRanks] at this

/-- The Heisenberg geometry is **not** a competitor at D = 3: it sits
at growth degree four, where the paper's stability analysis excludes
it by the same bound-state criterion that excludes ℤ⁴. -/
theorem heisenberg_excluded : heisenbergRanks.degree ≠ 3 := by
  rw [degree_heisenberg]; omega

end QuantumRelational.Paper2.GrowthDegree
