/-
  QuantumRelational/Paper2/CayleyGraph.lean

  **Paper 2: Lattice Structure from Graph Translations**

  Formalizes the graph-theoretic foundations of Paper 2's spatial
  structure argument:

  1. **Translations** are fixed-point-free permutations (automorphisms
     with no fixed points). Paper 2's Permutation Invariance principle
     requires that non-identity symmetries act freely.

  2. **Freeness argument:** If a non-identity automorphism tau fixes a
     point x, then {x} vs its complement forms a canonical partition
     that breaks permutation invariance. Therefore translations must
     be fixed-point-free.

  3. **Cayley graphs:** For a group G with generating set S, the Cayley
     graph Cay(G, S) has vertex set G and edges g ~ g*s for s in S.
     Left multiplication by any group element is a graph automorphism
     that acts freely and transitively.

  4. **Connection to Paper 1:** The cyclic structure (CyclicEigen) from
     Paper 1 is the 1D case; Paper 2 extends to higher-dimensional
     lattices via products of cyclic groups.

  Tier 2: Algebraic/combinatorial structure.
  Lean status: fully-derived (no sorry/axiom).
-/
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace QuantumRelational.Paper2.CayleyGraph

-- ============================================================
-- Section 1: Translations (Fixed-Point-Free Permutations)
-- ============================================================

/-- **Definition (Translation).**
A translation on a type alpha is a permutation that is not the identity
and has no fixed points. This captures Paper 2's notion of a graph
translation: a symmetry that moves every vertex.

In the physics: translations correspond to spatial shifts on the
lattice. The requirement of no fixed points means every site gets
mapped to a different site. -/
def IsTranslation {α : Type*} (τ : Equiv.Perm α) : Prop :=
  τ ≠ 1 ∧ ∀ x, τ x ≠ x

/-- The identity is not a translation. -/
theorem id_not_translation {α : Type*} [Nonempty α] :
    ¬IsTranslation (1 : Equiv.Perm α) := by
  intro ⟨h, _⟩
  exact h rfl

/-- A translation has no fixed points (unfolded form). -/
theorem translation_no_fixed_point {α : Type*} {τ : Equiv.Perm α}
    (h : IsTranslation τ) (x : α) : τ x ≠ x :=
  h.2 x

/-- If a permutation fixes some point, it is not a translation. -/
theorem not_translation_of_fixed_point {α : Type*} {τ : Equiv.Perm α}
    (x : α) (hx : τ x = x) : ¬IsTranslation τ := by
  intro ⟨_, hfree⟩
  exact hfree x hx

-- ============================================================
-- Section 2: Freeness from Permutation Invariance
-- ============================================================

/-- **Paper 2, Freeness Argument:**
If a non-identity permutation tau fixes a point x, then x is
distinguished from all other points (it is the unique element
of the singleton {x} that is invariant under tau). This breaks
permutation invariance, which requires all vertices to be
structurally identical.

Formalized as: for a non-identity permutation on a finite type,
if it has a fixed point, then it must also have a non-fixed point
(since it is not the identity). This creates an asymmetry. -/
theorem freeness_dichotomy {α : Type*} [Fintype α] [DecidableEq α]
    (τ : Equiv.Perm α) (hne : τ ≠ 1) :
    ∃ y : α, τ y ≠ y := by
  by_contra h
  push_neg at h
  apply hne
  ext x
  exact h x

/-- **Partition from a fixed point:**
If tau fixes x but is not the identity, then the type partitions
into fixed points and moved points, with both parts nonempty.
This is the canonical partition that breaks permutation invariance. -/
theorem partition_from_fixed_point {α : Type*} [Fintype α] [DecidableEq α]
    (τ : Equiv.Perm α) (hne : τ ≠ 1) (x : α) (hx : τ x = x) :
    (∃ y : α, τ y ≠ y) ∧ (∃ z : α, τ z = z) :=
  ⟨freeness_dichotomy τ hne, ⟨x, hx⟩⟩

/-- **Contrapositive (the key theorem):**
If we demand that no canonical partition exists (i.e., permutation
invariance holds), then every non-identity permutation must be
fixed-point-free -- i.e., it must be a translation.

Stated as: if any fixed point forces the permutation to be identity,
then the permutation is either the identity or a translation. -/
theorem translation_or_id {α : Type*} [Fintype α] [DecidableEq α]
    (τ : Equiv.Perm α) (hfree : ∀ x, τ x = x → τ = 1) :
    τ = 1 ∨ IsTranslation τ := by
  by_cases h : τ = 1
  · left; exact h
  · right
    refine ⟨h, fun x hx => ?_⟩
    exact h (hfree x hx)

/-- **Permutation invariance implies freeness (Paper 2 core argument):**
If no non-identity element has a fixed point, then every non-identity
element is a translation. This is the spatial analog of Paper 1's
result that cyclic permutations have no fixed points. -/
theorem perm_invariance_implies_free {α : Type*} [Fintype α] [DecidableEq α]
    (τ : Equiv.Perm α) (hne : τ ≠ 1)
    (h_no_fix : ∀ x : α, τ x ≠ x) :
    IsTranslation τ :=
  ⟨hne, h_no_fix⟩

-- ============================================================
-- Section 3: Free and Transitive Group Actions
-- ============================================================

/-- **Definition (Free action).**
A group action is free if the only element that fixes any point is
the identity. -/
def IsFreeAction (G : Type*) (α : Type*) [Group G] [MulAction G α] : Prop :=
  ∀ (g : G), g ≠ 1 → ∀ x : α, g • x ≠ x

/-- **Definition (Transitive action).**
A group action is transitive if for any two points, some group
element sends one to the other. -/
def IsTransitiveAction (G : Type*) (α : Type*) [Group G] [MulAction G α] : Prop :=
  ∀ x y : α, ∃ g : G, g • x = y

/-- **Definition (Simply transitive / regular action).**
An action is simply transitive if it is both free and transitive.
This is the key property of Cayley graphs: the group acts on
itself by left multiplication, and this action is simply transitive. -/
def IsSimplyTransitive (G : Type*) (α : Type*) [Group G] [MulAction G α] : Prop :=
  IsFreeAction G α ∧ IsTransitiveAction G α

-- ============================================================
-- Section 4: Left Multiplication on a Group
-- ============================================================

/-- Left multiplication by g in a group G is free: if g * x = x
then g = 1. This is immediate from group cancellation. -/
theorem left_mul_free (G : Type*) [Group G] (g : G) (hg : g ≠ 1) (x : G) :
    g * x ≠ x := by
  intro h
  have : g = 1 := mul_right_cancel (h.trans (one_mul x).symm)
  exact hg this

/-- Left multiplication by any group element is a bijection. -/
theorem left_mul_bijective (G : Type*) [Group G] (g : G) :
    Function.Bijective (fun x : G => g * x) := by
  constructor
  · intro x y h
    exact mul_left_cancel h
  · intro y
    exact ⟨g⁻¹ * y, by simp [mul_assoc]⟩

/-- Left multiplication is transitive: for any x, y in G,
g = y * x⁻¹ sends x to y. -/
theorem left_mul_transitive (G : Type*) [Group G] (x y : G) :
    (y * x⁻¹) * x = y := by
  simp [mul_assoc]

/-- **Paper 2 key theorem: The left regular action of a group on itself
is free.**

On a Cayley graph Cay(G, S), the vertex set is G itself, and left
multiplication by any g in G is a graph automorphism. The action
is free: g * x = x implies g = 1 by cancellation. -/
theorem left_regular_free (G : Type*) [Group G] (g : G) (hg : g ≠ 1) (x : G) :
    g * x ≠ x :=
  left_mul_free G g hg x

/-- **Paper 2 key theorem: The left regular action of a group on itself
is transitive.**

For any x, y in G, the element g = y * x⁻¹ satisfies g * x = y.
Combined with freeness, this gives a simply transitive (regular) action.

This is the algebraic foundation for Paper 2's lattice structure:
the spatial lattice Z^d arises as the Cayley graph of the abelian
group Z^d with standard generators. -/
theorem left_regular_transitive (G : Type*) [Group G] (x y : G) :
    ∃ g : G, g * x = y :=
  ⟨y * x⁻¹, by simp [mul_assoc]⟩

/-- **Uniqueness of the transporting element:**
In a free transitive action, the element g sending x to y is unique.
For left multiplication: if g * x = y and h * x = y, then g = h. -/
theorem left_regular_unique (G : Type*) [Group G] (x y : G)
    (g h : G) (hg : g * x = y) (hh : h * x = y) : g = h := by
  have : g * x = h * x := hg.trans hh.symm
  exact mul_right_cancel this

-- ============================================================
-- Section 5: Connection to Additive Groups (Link to Paper 1)
-- ============================================================

/-- In an additive group, addition by a nonzero element has no
fixed points: x + a = x implies a = 0. This is the additive
analog of left_mul_free. -/
theorem add_shift_free {G : Type*} [AddGroup G] (a : G) (ha : a ≠ 0)
    (x : G) : x + a ≠ x := by
  intro h
  apply ha
  -- From x + a = x, cancel x on the left: a = 0
  have : x + a = x + 0 := by rw [add_zero]; exact h
  exact add_left_cancel this

/-- Addition is transitive: for any x, y in an additive group,
a = y - x satisfies x + a = y. -/
theorem add_shift_transitive {G : Type*} [AddGroup G] (x y : G) :
    ∃ a : G, x + a = y :=
  ⟨-x + y, by rw [← add_assoc, add_neg_cancel, zero_add]⟩

/-- **Simply transitive action of an additive group on itself:**
This is the foundation for Paper 2's lattice structure. The Cayley
graph of Z^d with standard generators is the d-dimensional lattice,
and the translation group Z^d acts on it simply transitively.

The 1-dimensional case (Z/nZ acting on the cycle graph C_n)
corresponds to Paper 1's cyclic eigenvalue structure. -/
theorem additive_regular_action {G : Type*} [AddGroup G] :
    -- Free: a != 0 implies x + a != x for all x
    (∀ (a : G), a ≠ 0 → ∀ x : G, x + a ≠ x) ∧
    -- Transitive: for all x y, exists a such that x + a = y
    (∀ x y : G, ∃ a : G, x + a = y) :=
  ⟨fun a ha x => add_shift_free a ha x,
   fun x y => add_shift_transitive x y⟩

end QuantumRelational.Paper2.CayleyGraph
