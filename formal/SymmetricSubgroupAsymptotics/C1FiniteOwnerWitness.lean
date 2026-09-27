import Mathlib.GroupTheory.PGroup

/-!
# Intrinsic witnesses for the bounded c=1 earlier owners

These structures state the group-theoretic content used by the degree-six
and degree-twelve earlier-owner rows.  They contain actual subgroups of the
original finite group.  A catalogue label or an asserted abstract group name
is therefore not an owner witness.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G]

/-- The first degree-six owner: a normal 3-subgroup of index two. -/
structure C1OddIndexTwoOwnerWitness (G : Type*) [Group G] where
  ternary : Subgroup G
  normal : ternary.Normal
  ternaryPGroup : IsPGroup 3 ternary
  index_two : ternary.index = 2

/-- Conjugation of a member of a normal subgroup, retained as a member of
that same subgroup. -/
def normalConjugate (B : Subgroup G) (hB : B.Normal) (v : B) (g : G) : B :=
  ⟨g * (v : G) * g⁻¹, hB.conj_mem (v : G) v.2 g⟩

@[simp] theorem normalConjugate_coe (B : Subgroup G) (hB : B.Normal)
    (v : B) (g : G) : (normalConjugate B hB v g : G) = g * (v : G) * g⁻¹ := rfl

/-- The cyclic binary-module owner.  `base` is an elementary binary normal
subgroup, `complement` is an elementary ternary subgroup, and together they
give an internal semidirect product.  The conjugates of `vector` by the
actual complement generate the whole base, which records cyclicity of the
binary module without choosing coordinates or an abstract group identifier. -/
structure C1CyclicBinaryModuleOwnerWitness (G : Type*) [Group G] where
  base : Subgroup G
  complement : Subgroup G
  base_normal : base.Normal
  basePGroup : IsPGroup 2 base
  complementPGroup : IsPGroup 3 complement
  base_exponent_two : ∀ x : base, x ^ 2 = 1
  complement_exponent_three : ∀ x : complement, x ^ 3 = 1
  intersection_trivial : ∀ x : G, x ∈ base → x ∈ complement → x = 1
  factorBase : G → base
  factorComplement : G → complement
  factorization : ∀ x : G, (factorBase x : G) * (factorComplement x : G) = x
  vector : base
  cyclicWord : base → List complement
  cyclic_word_eq : ∀ x : base,
    ((cyclicWord x).map fun c : complement =>
      normalConjugate base base_normal vector (c : G)).prod = x

namespace C1CyclicBinaryModuleOwnerWitness

variable (W : C1CyclicBinaryModuleOwnerWitness G)

theorem disjoint : W.base ⊓ W.complement = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  exact W.intersection_trivial x hx.1 hx.2

theorem generate : W.base ⊔ W.complement = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [← W.factorization x]
  exact Subgroup.mul_mem _
    ((show W.base ≤ W.base ⊔ W.complement from le_sup_left)
      (W.factorBase x).property)
    ((show W.complement ≤ W.base ⊔ W.complement from le_sup_right)
      (W.factorComplement x).property)

theorem cyclic : Subgroup.closure
    (Set.range fun c : W.complement =>
      normalConjugate W.base W.base_normal W.vector (c : G)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [← W.cyclic_word_eq x]
  apply Subgroup.list_prod_mem
  intro y hy
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hy
  exact Subgroup.subset_closure (Set.mem_range_self c)

end C1CyclicBinaryModuleOwnerWitness

end SymmetricSubgroupAsymptotics
