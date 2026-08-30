/-
  QuantumRelational/Axioms.lean

  Axiom 1 (Graded Equality / Distinguishability) and Axiom 2 (Saturation)
  from "Quantum Mechanics from Finite Relational Structure".

  These are the two foundational axioms from which all of quantum mechanics
  is derived in the paper.

  **Paper v2 framing note (added 2026-04-30).**

  In the v2 paper (`QuantumMechanicsFromFiniteGradedEquality.tex`), the
  framework has only TWO primitive axioms: `ax:finite` (finite capacity
  N) and `ax:relational` (Self-Referentially Consistent Closure, SRC). The eight
  named sub-clauses (S1)--(S4), (I), (O), (T), (B) that previously
  appeared as separate axioms or sub-axioms are now THEOREMS, derived
  from SRC + finite capacity in the Master Theorem `thm:src-master`.

  The v2 axioms are formalised in `QuantumRelational/SRC.lean`; the
  bridge `SRC.axiom2_from_SRC` shows that any space satisfying SRC +
  finite capacity also satisfies the structure recorded by `Axiom2`
  below. The Lean structures `Axiom1` and `Axiom2` in this file are
  preserved as the *consumption interface* used by all downstream files
  (`Parsimony`, `CyclicEigen`, `CapacityHalting`, ...): they bundle the
  *consequences* of SRC + finite capacity in a directly-usable form,
  with each field corresponding to a clause of `thm:src-master`. The
  v1-vs-v2 axiom-counting question is settled in the paper, not in the
  Lean library; the Lean library carries the structural derivation.

  **Scope note (axiom formalization vs. paper):**

  The paper's axioms (v1 §3 / `sec:axioms`) had several named
  sub-components, all of which are now derived clauses of
  `thm:src-master`:

    Axiom 1 (Finite Capacity with Saturation):
      (1a) Existence: every basis has N elements (paper Ax. `ax:finite`).
      (1b)(i) Identity/injectivity: K(x,z) = K(y,z) ∀z ⟹ x = y
              (now Theorem `thm:src-master`(S1)).
      (1b)(ii) Completeness/surjectivity: every consistent K-profile is a state
              (now Theorem `thm:src-master`(S2)).
      (1b)(iii) Finite determinacy: finite separating set S
              (now Theorem `thm:src-master`(S3)).
      (1b)(iv) Structural Leibniz: K-symmetries of finite configs extend globally
              (now Theorem `thm:src-master`(S4)).
      (1c) Connectedness: α is connected in the K-pseudometric topology
           (continuity of K is automatic in this topology, not an axiom).

    Axiom 2 (Universal Relationality):
      (2a) K(x,y) = 0 ⟹ x = y
              (Lean projection `thm:src-master`(O); on the paper side the
              former clause "Operational Completeness" is now the
              single-evaluation case of **Identity**).
      (2b) Transport Consistency: meaningful DOFs are K-comparable
              (now Theorem `thm:src-master`(T)).
      (2c) Basis Isotropy: symmetry group acts transitively on bases
              (now Theorem `thm:src-master`(B)).

  The clause carried by the Lean projection `thm:src-master`(I) is the
  one the current paper calls **Scale-Freeness** (K-image dense in
  [0,1]); it was called *Imperceptibility* in earlier revisions, and the
  v1 paper recorded it as an `(1c)`-style commitment. The Lean names are
  unchanged. Paper side, the hierarchy now has six clauses (Identity,
  Limit Completeness, Structural Leibniz (context form), Scale-Freeness,
  Transport Consistency, Basis Isotropy); see `AxiomCheck.lean`'s header
  or `PAPER_MAPPING.md` §3 for the full name correspondence.

  This Lean formalization captures the components that enter the
  mechanized proofs:
    - `K_refl`, `K_symm` encode the kernel definition
    - `K_ident` (in Axiom1) corresponds to paper (2a), i.e. the
      single-evaluation case of the paper's **Identity** clause
      (formerly the separate clause "Operational Completeness")
    - `completeness` (in Axiom2) corresponds to paper (1b)(i) Identity
    - `saturation` (in Axiom2) is a basis-restricted form of paper (1b)(iii)

  Components NOT axiomatized here but used in the paper's derivation:
    - Paper (1b)(ii) Surjectivity: enters implicitly via the specific
      instantiation of the state space (e.g., Fin N for the combinatorial
      files, ℂP^(N-1) for the geometric files).
    - Paper (1b)(iv) Structural Leibniz: the paper uses this to derive
      Permutation Invariance (paper Thm `permutation-invariance`), which
      drives cyclic dynamics. In Lean, the cyclic permutation is instantiated
      directly via Mathlib's `finRotate N` in `CyclicEigen.lean`, so
      Structural Leibniz enters as a specific concrete construction rather
      than as a general extension axiom. The paper argues this construction
      is forced by the axiom; the Lean does not prove the "forced" direction.
    - Paper (2c) Basis Isotropy: the paper uses this (with Montgomery--Zippin)
      to derive the Lie group structure of the symmetry group. In Lean, the
      Lie/unitary structure enters via specific Mathlib instances (e.g.,
      `UnitaryGroup`) rather than being derived from a transitivity axiom.

  The Lean formalization therefore verifies the mathematical skeleton of
  the derivation; the "these are the only axioms compatible with the
  structural constraints" claim rests on arguments made in the paper prose
  (particularly §3, §5) that are not separately formalized. See
  Appendix `app:formal-verification` of the paper for the complete scope.
-/
import Mathlib.Topology.MetricSpace.Basic

namespace QuantumRelational

/-- **Definition 10: Distinguishability Space**
A distinguishability space (𝒳, K) consists of a set 𝒳 equipped with a
symmetric kernel K : 𝒳 × 𝒳 → [0,1] satisfying:
  (i)   K(x,x) = 0              (reflexivity)
  (ii)  K(x,y) = K(y,x)         (symmetry)
  (iii) K(x,y) = 0 → x = y     (identity of indiscernibles)
  (iv)  K(x,y) = 1 ↔ x,y perfectly distinguishable -/
structure DistinguishabilitySpace (α : Type*) where
  /-- The distinguishability kernel K : α × α → ℝ -/
  K : α → α → ℝ
  /-- K takes values in [0,1] -/
  K_nonneg : ∀ (x y : α), 0 ≤ K x y
  K_le_one : ∀ (x y : α), K x y ≤ 1
  /-- K(x,x) = 0 (reflexivity) -/
  K_refl : ∀ (x : α), K x x = 0
  /-- K(x,y) = K(y,x) (symmetry) -/
  K_symm : ∀ (x y : α), K x y = K y x
  /-- K(x,y) = 0 → x = y (identity of indiscernibles) -/
  K_ident : ∀ (x y : α), K x y = 0 → x = y

/-- **Definition 12: Basis and Capacity**
A basis ℬ is a maximal set of mutually perfectly distinguishable elements.
The capacity N = |ℬ| is the cardinality of any basis. -/
structure BasisStructure (α : Type*) extends DistinguishabilitySpace α where
  /-- The capacity (dimension) N ≥ 2 -/
  N : ℕ
  N_ge_two : 2 ≤ N

/-- **Axiom 1: Graded Equality (Distinguishability)**
There exists a distinguishability kernel K satisfying the properties
of Definition 10, with finite capacity N. This encodes the idea that
physical systems have a relational, graded notion of equality rather
than a binary one. -/
structure Axiom1 (α : Type*) extends BasisStructure α where
  /-- There exists a basis (maximal mutually distinguishable set) -/
  basis : Fin N → α
  /-- Basis elements are mutually perfectly distinguishable -/
  basis_distinguishable : ∀ (i j : Fin N), i ≠ j → K (basis i) (basis j) = 1
  -- Note: basis_self (K(b_i, b_i) = 0) is redundant with inherited K_refl.
  /-- **Axiom (1c): Connectedness (Lean encoding of the paper's Scale-Freeness
      commitment; the clause was called *Imperceptibility* in earlier
      revisions).**
      The state space α is connected in the K-pseudometric topology
      `d(x, y) := ⨆ z, |K(x, z) - K(y, z)|`.

      **Paper-Lean asymmetry.** The paper states (1c) as *Scale-Freeness*
      (the clause formerly named *Imperceptibility*):
      `K(α × α)` is dense in `[0,1]` (equivalently, the K-image equals
      `[0,1]`, since the closure of K(α × α) is closed in the compact unit
      interval). The Lean encoding takes the topologically equivalent
      *Connectedness* condition as the primitive structure field. Under the
      framework's structural identification (paper Theorems
      `thm:complexity-constraint`, `thm:points-sections`), Imperceptibility
      and Connectedness are equivalent (paper Theorem
      `thm:imperceptibility-connectedness`); the choice between them is a
      presentation matter that does not affect any downstream Lean proof.

      **Provenance of the topological content (paper §3, §4).** In the
      current paper, scale-freeness ("N is the only scale", Axiom 1(ii))
      is the primitive commitment, and its topological content is
      *derived*: read on the symmetry group, "N is the only scale" is the
      no-small-subgroups property (a nontrivial subgroup in an arbitrarily
      small neighborhood of the identity would move states at a scale
      beneath the capacity), which by Gleason-Yamabe makes `Aut(α, K)` a
      Lie group and `α = G/H` a finite-dimensional manifold (paper
      `thm:complexity-constraint`, regularity condition (R),
      `rem:finite-dim-status`), hence connected
      (`thm:imperceptibility-connectedness`). This Lean structure takes
      that downstream consequence, connectedness, as its convenient
      primitive; the no-small-subgroups -> Lie -> finite-dimensional ->
      connected chain is the paper's prose derivation and is not
      mechanized here (see the scope note in paper Appendix
      `app:formal-verification`). The two views are the same equivalence.

      The Lean encoding takes connectedness as primitive because it is
      directly usable as a `ConnectedSpace` instance for topological proofs;
      no Lean theorem in this library consumes density of the K-image as a
      hypothesis where it is not interchangeable with connectedness.

      `d` is a genuine metric by `K_ident` (Saturation (i)); the triangle
      inequality `|K(x,y) - K(x',y')| ≤ d(x,x') + d(y,y')` makes K jointly
      continuous in this metric, so continuity of K is *automatic* and is
      not an additional axiom (the paper's Appendix B,
      `app:structural-conditions`, derives joint continuity of K from the
      K-pseudometric; see paper Remark `rem:topology-from-K`).

      Connectedness is the framework's only commitment beyond finite
      capacity (1a) and saturation (1b). Compactness of α, density of the
      K-image, the identity K(α × α) = [0,1], and M(K) = ∞ are all
      theorems rather than axioms (derivable from (1a) + (1b) + (1c) via
      the K-profile embedding α ↪ [0,1]^N).

      This axiom excludes binary K (the classical N-state register, where
      the K-pseudometric is the discrete metric, making α totally
      disconnected) and all finite-resolution refinements (where α is a
      finite K-symmetric subset, again disconnected in the K-metric).

      **Lean encoding.** The K-pseudometric topology is bundled as a
      structure field `topology : TopologicalSpace α` (intended to be the
      topology induced by the K-pseudometric, in which K is continuous
      automatically). The connectedness commitment is the field
      `connected`. Downstream proofs may use `letI := ax.topology` to
      bring the topology into instance scope and then reference
      `ConnectedSpace` in its standard form. -/
  topology : TopologicalSpace α
  /-- α is connected in the K-pseudometric topology. -/
  connected : @ConnectedSpace α topology

/-- **Axiom 2: Saturation (Completeness)**
Every state is a complete probabilistic mixture over any basis.
For any state x and basis ℬ, the values K(x, bₖ) collectively
determine x up to gauge equivalence. There are no "hidden" degrees
of freedom beyond what K encodes.

Formally: the kernel K is *complete* — it captures all physically
accessible information about the relational state.

**Redundancy note:** The `completeness` field below is derivable from
`K_ident` (inherited via `DistinguishabilitySpace`) together with
`K_refl` and `K_symm`: from `(∀ z, K x z = K y z)`, specialize to z = x
to get K x x = K y x; by K_refl the LHS is 0, so K y x = 0, hence
K x y = 0 by K_symm, hence x = y by K_ident. The `completeness` field
is retained for downstream API convenience (it is used directly in
`Parsimony.lean`), but it carries no additional logical content beyond
the base `DistinguishabilitySpace` axioms. The `saturation` field IS
independent: it constrains states using only a FINITE separating set
(the basis), whereas `completeness`/`K_ident` implicitly quantify over
all states. -/
structure Axiom2 (α : Type*) extends Axiom1 α where
  /-- Completeness: K-equivalence implies physical identity.
      If K(x, z) = K(y, z) for all z, then x and y are
      physically identical. Derivable from K_ident + K_refl + K_symm;
      kept as a named field for downstream API clarity. -/
  completeness : ∀ (x y : α), (∀ (z : α), K x z = K y z) → x = y
  /-- Saturation: the values {K(x, bₖ)} over a basis determine all
      K-values K(x, y). Equivalently, K(x, ·) restricted to a basis
      determines K(x, ·) on all of 𝒳. This is the finite-bandwidth
      content of the paper's Axiom 1(1b)(iii) and is genuinely
      independent of `completeness` (which quantifies over all of 𝒳). -/
  saturation : ∀ (x y : α),
    (∀ (i : Fin N), K x (basis i) = K y (basis i)) → x = y

/-- The full axiom system: Axiom 1 + Axiom 2. -/
abbrev FullAxioms (α : Type*) := Axiom2 α

/-- **The `completeness` field is redundant (machine-checked derivation).**

    Given a `DistinguishabilitySpace` (which carries `K_refl`, `K_symm`,
    and `K_ident`), the `completeness` property `(∀ z, K x z = K y z) → x = y`
    follows automatically. Specialize the premise to `z = x`: we get
    `K x x = K y x`, hence `K y x = 0` by `K_refl`, hence `K x y = 0`
    by `K_symm`, hence `x = y` by `K_ident`.

    This theorem is a machine-checked witness that the `completeness`
    field of `Axiom2` carries no additional logical content beyond the
    base `DistinguishabilitySpace` axioms. The field is retained in the
    `Axiom2` structure for downstream API convenience (it is used
    directly in `Parsimony.lean` and `Basic.lean`), but could be
    removed entirely with only cosmetic changes. -/
theorem completeness_derived {α : Type*} (ax : DistinguishabilitySpace α) :
    ∀ (x y : α), (∀ (z : α), ax.K x z = ax.K y z) → x = y := by
  intro x y h
  have hxx : ax.K x x = ax.K y x := h x
  have hyx_zero : ax.K y x = 0 := by rw [← hxx]; exact ax.K_refl x
  have hxy_zero : ax.K x y = 0 := by rw [ax.K_symm]; exact hyx_zero
  exact ax.K_ident x y hxy_zero

-- ============================================================
-- Abstract Structural Leibniz (Paper Axiom 1(1b)(iv))
-- ============================================================

/-- **Definition: K-symmetry of a finite configuration.**

    A permutation σ of the index set {0, ..., n-1} is a K-symmetry of
    the configuration `cfg : Fin n → α` if it preserves all pairwise
    K-values: K(cfg(σ(i)), cfg(σ(j))) = K(cfg(i), cfg(j)) for all i, j.

    This captures the paper's notion: a relabeling of finitely many
    states that leaves every distinguishability value unchanged.
    The hypothesis of Structural Leibniz. -/
def IsKSymmetry {α : Type*} (ax : DistinguishabilitySpace α)
    {n : ℕ} (cfg : Fin n → α) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ (i j : Fin n), ax.K (cfg (σ i)) (cfg (σ j)) = ax.K (cfg i) (cfg j)

/-- **Definition: K-preserving automorphism of the whole space.**

    A bijection `g : α ≃ α` is a K-preserving automorphism if
    K(g(x), g(y)) = K(x, y) for all x, y. -/
def IsKAutomorphism {α : Type*} (ax : DistinguishabilitySpace α)
    (g : α ≃ α) : Prop :=
  ∀ (x y : α), ax.K (g x) (g y) = ax.K x y

/-- **Axiom 3 (Structural Leibniz): K-symmetries of finite configurations
    extend to global automorphisms.**

    This is the paper's Axiom 1(1b)(iv), stated abstractly: for any
    finite configuration admitting a K-symmetry σ, there exists a
    global K-preserving automorphism g of the space such that g agrees
    with σ on the configuration (i.e., g(cfg(i)) = cfg(σ(i)) for all i).

    **Paper motivation (Remark `structural-leibniz-weight`):** A
    K-symmetry that fails to extend globally would require structure
    beyond K to obstruct it; in the ontology where K is exhaustive,
    such structure does not exist, so every K-symmetry is genuine.

    **Axiomatic status:** This is one of the strongest axioms in the
    paper; it encodes a global extension property that is not automatic
    in abstract metric spaces. We state it as a separate axiom (paper
    statement); concrete instances (e.g., Fin N with the discrete
    distinguishability kernel, `finRotate N` as the cyclic automorphism)
    satisfy it via direct construction, which is how `CyclicEigen`
    instantiates the paper's derivation in Lean. -/
structure StructuralLeibniz {α : Type*} (ax : DistinguishabilitySpace α) : Prop where
  /-- Every K-symmetry of a finite configuration extends to a global
      K-preserving automorphism that agrees with the symmetry on the config. -/
  extends_globally : ∀ {n : ℕ} (cfg : Fin n → α) (σ : Equiv.Perm (Fin n)),
    IsKSymmetry ax cfg σ →
    ∃ (g : α ≃ α), IsKAutomorphism ax g ∧ ∀ (i : Fin n), g (cfg i) = cfg (σ i)

/-- **Permutation Invariance from Structural Leibniz (abstract version).**

    Given Axiom 1 (which supplies a basis of `N` mutually distinguishable
    elements with K(b_i, b_j) = 1 for i ≠ j and K(b_i, b_i) = 0) and
    Structural Leibniz (which extends K-symmetries of finite configs to
    global automorphisms), every permutation σ ∈ S_N acts as a
    K-preserving automorphism of (α, K).

    This is the paper's Theorem `permutation-invariance`, stated and
    proved abstractly at the level of the axioms (without instantiating
    a specific automorphism group). It is the source of cyclic dynamics
    in the paper: the cyclic permutation `(0 1 2 ... N-1)` corresponds
    to a global K-preserving automorphism whose action on the basis is
    an N-cycle.

    **Note:** The Lean formalization in `CyclicEigen` instantiates this
    abstract conclusion for the concrete space `Fin N` via `finRotate N`.
    The present theorem shows that the abstract derivation from the
    axioms goes through as in the paper; `CyclicEigen` provides the
    specific automorphism used in downstream proofs. -/
theorem permutation_invariance_abstract
    {α : Type*} (ax : Axiom1 α) (sl : StructuralLeibniz ax.toDistinguishabilitySpace)
    (σ : Equiv.Perm (Fin ax.N)) :
    ∃ (g : α ≃ α), IsKAutomorphism ax.toDistinguishabilitySpace g ∧
      ∀ (i : Fin ax.N), g (ax.basis i) = ax.basis (σ i) := by
  -- Claim: σ is a K-symmetry of the basis configuration.
  have h_sym : IsKSymmetry ax.toDistinguishabilitySpace ax.basis σ := by
    intro i j
    -- Both sides are 1 if i ≠ j (via σ(i) ≠ σ(j) ↔ i ≠ j for a permutation)
    -- and 0 if i = j (via K_refl).
    by_cases hij : i = j
    · subst hij
      -- K(b_{σ(i)}, b_{σ(i)}) = 0 = K(b_i, b_i)
      rw [ax.K_refl, ax.K_refl]
    · -- σ is a bijection, so σ(i) ≠ σ(j) iff i ≠ j
      have hσij : σ i ≠ σ j := fun h => hij (σ.injective h)
      rw [ax.basis_distinguishable (σ i) (σ j) hσij,
          ax.basis_distinguishable i j hij]
  -- Apply Structural Leibniz to extend the K-symmetry globally.
  exact sl.extends_globally ax.basis σ h_sym

end QuantumRelational
