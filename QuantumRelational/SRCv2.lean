/-
  QuantumRelational/SRCv2.lean

  **Corrected SRC axioms (paper revision 2026-07-01) and the corrected
  saturation hierarchy.**

  The revised paper (`2026_07_01_QuantumMechanicsFromFiniteGradedEquality.tex`)
  restates Axiom 2 (Self-Referential Consistency) as three internal clauses:

    (C1) Definability: every Aut-invariant predicate factors through K-profiles
         (paper Axiom `ax:relational`(C1); Lemma `lem:definability`).
    (C2) Saturation (limit completeness): realized K-profiles are closed
         under pointwise limits (paper Axiom `ax:relational`(C2)).
    (C3) Context Homogeneity: swaps anchored on a mutually fully
         distinguishable set extend to global automorphisms
         (paper Axiom `ax:relational`(C3)).

  The v1 blanket Structural Leibniz clause (`StructuralLeibniz` in
  `Axioms.lean`: EVERY pairwise K-symmetry of EVERY finite configuration
  extends) is RETIRED: it is refuted in the intended model by the paper's
  Theorem `thm:binary-insufficiency`, whose concrete counterexample is
  machine-checked in `QuantumRelational/BinaryInsufficiency.lean`. (C3) is
  the exact surviving residue: anchors restricted to measurement contexts.

  This file mechanizes, from (C1) and (C3) alone:
    * (S1) Identity via the diagonal-predicate argument
      (paper Theorem `thm:src-master`(S1); also derivable from the kernel
      laws directly, see `Axioms.completeness_derived`);
    * Corollary `cor:homogeneity`:
        (i)   transitivity of Aut on states        (`transitivity_from_C3`)
        (ii)  two-point homogeneity                (`two_point_homogeneity_from_C3`)
        (iii) pair-completeness (orbit form)       (immediate from (ii))
        (iv)  Permutation Invariance               (`permutation_invariance_from_C3`)
    * (B) Basis Isotropy by the aligned-anchor induction
      (paper Theorem `thm:src-master`(B); `basis_isotropy_from_C3`).

  (C2) is stated (`LimitCompleteness`) for the axiom packaging; its
  downstream consumer is the compactness lemma, whose topological content
  (Tychonoff) is imported classically in the paper.
-/
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.GroupTheory.Perm.Sign
import QuantumRelational.Axioms

namespace QuantumRelational
namespace SRCv2

open scoped BigOperators

variable {α : Type*}

/-- **(C1) Definability, binary consumed form** (paper Axiom
`ax:relational`(C1), in the form consumed by the derivation chain via
(S1) and (T)): every `Aut(𝒳,K)`-invariant binary predicate factors
through the pair of full K-profiles. -/
structure DefinabilityBinary (ax : DistinguishabilitySpace α) : Prop where
  factors : ∀ P : α → α → Prop,
    (∀ g : α ≃ α, IsKAutomorphism ax g → ∀ x y, (P (g x) (g y) ↔ P x y)) →
    ∃ Q : (α → ℝ) → (α → ℝ) → Prop, ∀ x y, (P x y ↔ Q (ax.K x) (ax.K y))

/-- **(C2) Saturation (limit completeness)** (paper Axiom
`ax:relational`(C2)): a pointwise-convergent net of realized K-profiles
has a realized limit. Stated with filters; `l.NeBot` excludes the trivial
filter. -/
structure LimitCompleteness (ax : DistinguishabilitySpace α) : Prop where
  limit_realized : ∀ {ι : Type} (l : Filter ι), l.NeBot →
    ∀ (xs : ι → α) (f : α → ℝ),
    (∀ z : α, Filter.Tendsto (fun i => ax.K (xs i) z) l (nhds (f z))) →
    ∃ x : α, ∀ z : α, ax.K x z = f z

/-- A finite set is a *(partial) context* if its elements are mutually
fully distinguishable (pairwise `K = 1`). The empty set and singletons
are contexts vacuously. -/
def IsContext (ax : DistinguishabilitySpace α) (C : Finset α) : Prop :=
  ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → ax.K c c' = 1

/-- **(C3) Context Homogeneity** (paper Axiom `ax:relational`(C3)): if
`x` and `y` have equal K-profiles on a context `C`, the anchored swap
`x ↔ y` extends to a global K-automorphism fixing `C` pointwise.

This is the exact corrected residue of the retired blanket Structural
Leibniz clause: the paper's Theorem `thm:binary-insufficiency`
(mechanized in `BinaryInsufficiency.lean`) shows that widening the
anchor class beyond contexts is false in the intended model. -/
structure ContextHomogeneity (ax : DistinguishabilitySpace α) : Prop where
  swap_extends : ∀ C : Finset α, IsContext ax C →
    ∀ x y : α, (∀ c ∈ C, ax.K x c = ax.K y c) →
    ∃ g : α ≃ α, IsKAutomorphism ax g ∧
      (∀ c ∈ C, g c = c) ∧ g x = y ∧ g y = x

/-- **Axiom 2 (SRC), corrected packaging**: the three clauses
(C1)-(C3) of the revised paper's Axiom `ax:relational`. -/
structure SRC (ax : DistinguishabilitySpace α) : Prop where
  c1 : DefinabilityBinary ax
  c2 : LimitCompleteness ax
  c3 : ContextHomogeneity ax

/-! ### (S1) Identity from (C1): the diagonal-predicate argument -/

/-- **(S1) Identity from Definability** (paper Theorem
`thm:src-master`(S1), proved exactly as in the paper): apply (C1) to the
diagonal predicate `D(u,v) := (u = v)`, which is Aut-invariant since
bijections preserve equality; the resulting profile functional forces
K-profile equality to imply state equality.

(As the paper notes, (S1) is also derivable from the kernel laws alone,
`completeness_derived` in `Axioms.lean`; this theorem mechanizes the
paper's (C1)-route.) -/
theorem S1_identity_from_C1 (ax : DistinguishabilitySpace α)
    (c1 : DefinabilityBinary ax) :
    ∀ x y : α, (∀ z : α, ax.K x z = ax.K y z) → x = y := by
  intro x y hxy
  -- The diagonal predicate is Aut-invariant.
  have hinv : ∀ g : α ≃ α, IsKAutomorphism ax g →
      ∀ u v : α, ((g u = g v) ↔ u = v) := by
    intro g _ u v
    exact ⟨fun h => g.injective h, fun h => congrArg g h⟩
  obtain ⟨Q, hQ⟩ := c1.factors (fun u v => u = v) hinv
  -- Q holds on the pair of equal profiles (K x ·, K x ·).
  have hQxx : Q (ax.K x) (ax.K x) := (hQ x x).mp rfl
  -- The hypothesis says the profiles agree as functions.
  have hfun : ax.K x = ax.K y := funext hxy
  -- Substitute to get Q on (K x ·, K y ·), hence x = y.
  have hQxy : Q (ax.K x) (ax.K y) := by rw [← hfun]; exact hQxx
  exact (hQ x y).mpr hQxy

/-! ### Corollary `cor:homogeneity` from (C3) -/

/-- K-automorphisms compose. -/
theorem isKAutomorphism_trans (ax : DistinguishabilitySpace α)
    {g g' : α ≃ α} (hg : IsKAutomorphism ax g) (hg' : IsKAutomorphism ax g') :
    IsKAutomorphism ax (g.trans g') := by
  intro x y
  have : ax.K (g' (g x)) (g' (g y)) = ax.K (g x) (g y) := hg' (g x) (g y)
  simpa [Equiv.trans_apply] using this.trans (hg x y)

/-- The empty set is a context. -/
theorem isContext_empty (ax : DistinguishabilitySpace α) :
    IsContext ax (∅ : Finset α) := by
  intro c hc
  exact absurd hc (Finset.notMem_empty c)

/-- Singletons are contexts (no distinct pairs). -/
theorem isContext_singleton (ax : DistinguishabilitySpace α) (a : α) :
    IsContext ax ({a} : Finset α) := by
  intro c hc c' hc' hne
  rw [Finset.mem_singleton] at hc hc'
  exact absurd (hc.trans hc'.symm) hne

/-- **Corollary `cor:homogeneity`(i): transitivity.** (C3) with the empty
anchor swaps any two states. -/
theorem transitivity_from_C3 (ax : DistinguishabilitySpace α)
    (c3 : ContextHomogeneity ax) (x y : α) :
    ∃ g : α ≃ α, IsKAutomorphism ax g ∧ g x = y := by
  obtain ⟨g, hgK, _, hgx, _⟩ :=
    c3.swap_extends ∅ (isContext_empty ax) x y
      (fun c hc => absurd hc (Finset.notMem_empty c))
  exact ⟨g, hgK, hgx⟩

/-- **Corollary `cor:homogeneity`(ii): two-point homogeneity.** Pairs
with equal K-value are Aut-conjugate: move `x₁` to `x₂` by the empty
anchor, then correct `y` within the singleton anchor `{x₂}`. -/
theorem two_point_homogeneity_from_C3 (ax : DistinguishabilitySpace α)
    (c3 : ContextHomogeneity ax) (x₁ y₁ x₂ y₂ : α)
    (hK : ax.K x₁ y₁ = ax.K x₂ y₂) :
    ∃ g : α ≃ α, IsKAutomorphism ax g ∧ g x₁ = x₂ ∧ g y₁ = y₂ := by
  obtain ⟨h, hhK, hhx⟩ := transitivity_from_C3 ax c3 x₁ x₂
  -- Profiles of u := h y₁ and v := y₂ agree on the singleton anchor {x₂}.
  have hprof : ∀ c ∈ ({x₂} : Finset α), ax.K (h y₁) c = ax.K y₂ c := by
    intro c hc
    rw [Finset.mem_singleton] at hc
    rw [hc]
    calc ax.K (h y₁) x₂ = ax.K (h y₁) (h x₁) := by rw [hhx]
      _ = ax.K y₁ x₁ := by
            have := hhK y₁ x₁; simpa using this
      _ = ax.K x₁ y₁ := ax.K_symm y₁ x₁
      _ = ax.K x₂ y₂ := hK
      _ = ax.K y₂ x₂ := ax.K_symm x₂ y₂
  obtain ⟨h', hh'K, hh'C, hh'u, _⟩ :=
    c3.swap_extends {x₂} (isContext_singleton ax x₂) (h y₁) y₂ hprof
  refine ⟨h.trans h', isKAutomorphism_trans ax hhK hh'K, ?_, ?_⟩
  · show h' (h x₁) = x₂
    rw [hhx]
    exact hh'C x₂ (Finset.mem_singleton_self x₂)
  · show h' (h y₁) = y₂
    exact hh'u

/-- **Corollary `cor:homogeneity`(iii): pair-completeness** (orbit
form): the K-value classifies pairs up to Aut, so every Aut-invariant
binary function of a pair is a function of `K` alone. Stated as: any
Aut-invariant `F` agrees on pairs with equal K-value. -/
theorem pair_completeness_from_C3 (ax : DistinguishabilitySpace α)
    (c3 : ContextHomogeneity ax) {β : Type*} (F : α → α → β)
    (hF : ∀ g : α ≃ α, IsKAutomorphism ax g → ∀ x y, F (g x) (g y) = F x y)
    (x₁ y₁ x₂ y₂ : α) (hK : ax.K x₁ y₁ = ax.K x₂ y₂) :
    F x₁ y₁ = F x₂ y₂ := by
  obtain ⟨g, hgK, hgx, hgy⟩ :=
    two_point_homogeneity_from_C3 ax c3 x₁ y₁ x₂ y₂ hK
  calc F x₁ y₁ = F (g x₁) (g y₁) := (hF g hgK x₁ y₁).symm
    _ = F x₂ y₂ := by rw [hgx, hgy]

/-! ### Permutation Invariance from (C3) -/

section PermutationInvariance

variable [DecidableEq α] (ax : DistinguishabilitySpace α) {N : ℕ} (b : Fin N → α)

/-- A *basis family*: `N` mutually fully distinguishable states. -/
def IsBasisFamily : Prop :=
  ∀ i j : Fin N, i ≠ j → ax.K (b i) (b j) = 1

omit [DecidableEq α] in
/-- Basis families are injective (distinct indices give distinct states,
since `K = 1 ≠ 0 = K(c,c)`). -/
theorem basisFamily_injective (hb : IsBasisFamily ax b) :
    Function.Injective b := by
  intro i j hij
  by_contra hne
  have h1 : ax.K (b i) (b j) = 1 := hb i j hne
  rw [hij, ax.K_refl] at h1
  exact one_ne_zero h1.symm

/-- Any image of a subset of a basis family is a context. -/
theorem isContext_of_basisFamily (hb : IsBasisFamily ax b)
    (s : Finset (Fin N)) : IsContext ax (s.image b) := by
  intro c hc c' hc' hne
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hc'
  exact hb i j (fun h => hne (congrArg b h))

/-- **Transposition realization.** For `i ≠ j`, some K-automorphism fixes
the rest of the basis family and swaps `b i ↔ b j`: apply (C3) with the
anchor `{b k : k ≠ i, k ≠ j}`, against which `b i` and `b j` have equal
profiles (`≡ 1`). -/
theorem swap_realized_from_C3 (c3 : ContextHomogeneity ax)
    (hb : IsBasisFamily ax b) (i j : Fin N) (hij : i ≠ j) :
    ∃ g : α ≃ α, IsKAutomorphism ax g ∧
      ∀ k : Fin N, g (b k) = b (Equiv.swap i j k) := by
  classical
  set s : Finset (Fin N) := Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j) with hs
  have hCctx : IsContext ax (s.image b) := isContext_of_basisFamily ax b hb s
  have hprof : ∀ c ∈ s.image b, ax.K (b i) c = ax.K (b j) c := by
    intro c hc
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hc
    rw [hs, Finset.mem_filter] at hm
    obtain ⟨-, hmi, hmj⟩ := hm
    rw [hb i m (fun h => hmi h.symm), hb j m (fun h => hmj h.symm)]
  obtain ⟨g, hgK, hgC, hgi, hgj⟩ :=
    c3.swap_extends (s.image b) hCctx (b i) (b j) hprof
  refine ⟨g, hgK, ?_⟩
  intro k
  by_cases hki : k = i
  · subst hki; rw [Equiv.swap_apply_left]; exact hgi
  · by_cases hkj : k = j
    · subst hkj; rw [Equiv.swap_apply_right]; exact hgj
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
      apply hgC
      exact Finset.mem_image.mpr ⟨k, by rw [hs]; simp [hki, hkj], rfl⟩

/-- **Corollary `cor:homogeneity`(iv): Permutation Invariance from (C3)**
(paper Corollary `cor:homogeneity`(iv), formerly the standalone theorem `thm:permutation-invariance`, corrected derivation):
every `σ ∈ S_N` is realized on the basis family by a global
K-automorphism. Proof: transpositions are realized by
`swap_realized_from_C3`, and transpositions generate `S_N`. -/
theorem permutation_invariance_from_C3 (c3 : ContextHomogeneity ax)
    (hb : IsBasisFamily ax b) (σ : Equiv.Perm (Fin N)) :
    ∃ g : α ≃ α, IsKAutomorphism ax g ∧
      ∀ k : Fin N, g (b k) = b (σ k) := by
  classical
  induction σ using Equiv.Perm.swap_induction_on with
  | one =>
      exact ⟨Equiv.refl α, fun x y => rfl, fun k => rfl⟩
  | swap_mul f x y hxy ih =>
      obtain ⟨gf, hgfK, hgfb⟩ := ih
      obtain ⟨gs, hgsK, hgsb⟩ := swap_realized_from_C3 ax b c3 hb x y hxy
      refine ⟨gf.trans gs, isKAutomorphism_trans ax hgfK hgsK, ?_⟩
      intro k
      show gs (gf (b k)) = b ((Equiv.swap x y * f) k)
      rw [hgfb k, hgsb (f k)]
      rfl

end PermutationInvariance

/-! ### (B) Basis Isotropy from (C3): the aligned-anchor induction -/

section BasisIsotropy

variable [DecidableEq α] (ax : DistinguishabilitySpace α) {N : ℕ}

/-- **(B) Basis Isotropy from (C3)** (paper Theorem `thm:src-master`(B),
corrected derivation): any two basis families are related by a global
K-automorphism, built by aligning one element at a time; at step `k`
the anchor is the already-aligned context `{b'_0, ..., b'_{k-1}}`,
against which both candidates have profile `≡ 1`. -/
theorem basis_isotropy_from_C3 (c3 : ContextHomogeneity ax)
    (b b' : Fin N → α)
    (hb : IsBasisFamily ax b) (hb' : IsBasisFamily ax b') :
    ∃ g : α ≃ α, IsKAutomorphism ax g ∧ ∀ i : Fin N, g (b i) = b' i := by
  classical
  suffices h : ∀ k : ℕ, k ≤ N →
      ∃ g : α ≃ α, IsKAutomorphism ax g ∧
        ∀ i : Fin N, (i : ℕ) < k → g (b i) = b' i by
    obtain ⟨g, hgK, hgb⟩ := h N le_rfl
    exact ⟨g, hgK, fun i => hgb i i.isLt⟩
  intro k
  induction k with
  | zero =>
      intro _
      exact ⟨Equiv.refl α, fun x y => rfl,
        fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
      intro hk1
      obtain ⟨g, hgK, hgb⟩ := ih (Nat.le_of_succ_le hk1)
      have hkN : k < N := hk1
      set kk : Fin N := ⟨k, hkN⟩ with hkk
      -- Anchor: the aligned initial segment of b'.
      set s : Finset (Fin N) := Finset.univ.filter (fun i => (i : ℕ) < k) with hs
      have hCctx : IsContext ax (s.image b') := isContext_of_basisFamily ax b' hb' s
      -- Both candidates have profile ≡ 1 on the anchor.
      have hne_of_mem : ∀ i : Fin N, (i : ℕ) < k → i ≠ kk := by
        intro i hi h
        rw [h] at hi
        exact Nat.lt_irrefl k hi
      have hprof : ∀ c ∈ s.image b',
          ax.K (g (b kk)) c = ax.K (b' kk) c := by
        intro c hc
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hc
        rw [hs, Finset.mem_filter] at hi
        have hik : (i : ℕ) < k := hi.2
        have hui : ax.K (g (b kk)) (b' i) = 1 := by
          rw [← hgb i hik]
          rw [hgK (b kk) (b i)]
          exact hb kk i (fun h => hne_of_mem i hik h.symm)
        have hvi : ax.K (b' kk) (b' i) = 1 :=
          hb' kk i (fun h => hne_of_mem i hik h.symm)
        rw [hui, hvi]
      obtain ⟨g', hg'K, hg'C, hg'u, _⟩ :=
        c3.swap_extends (s.image b') hCctx (g (b kk)) (b' kk) hprof
      refine ⟨g.trans g', isKAutomorphism_trans ax hgK hg'K, ?_⟩
      intro i hi
      show g' (g (b i)) = b' i
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hik | hik
      · rw [hgb i hik]
        apply hg'C
        exact Finset.mem_image.mpr ⟨i, by rw [hs]; simp [hik], rfl⟩
      · have : i = kk := Fin.ext hik
        subst this
        exact hg'u

end BasisIsotropy

end SRCv2
end QuantumRelational
