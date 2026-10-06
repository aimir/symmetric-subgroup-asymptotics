import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Recover transitivity from a one-orbit certificate

These elementary bridges turn the finite orbit-quotient certificates used
by the scalar Schur rows into the typeclass expected by induced-module head
bounds, including the literal coset action at a point stabilizer.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- A finite action whose orbit quotient has one point is pretransitive. -/
theorem isPretransitive_of_orbitQuotient_card_eq_one
    {G X : Type} [Group G] [Finite X] [MulAction G X]
    (hcard : Nat.card (MulAction.orbitRel.Quotient G X) = 1) :
    MulAction.IsPretransitive G X := by
  have hunique := Nat.card_eq_one_iff_unique.mp hcard
  letI : Unique (MulAction.orbitRel.Quotient G X) :=
    ⟨⟨Classical.choice hunique.2⟩, fun _ ↦ hunique.1.elim _ _⟩
  exact (MulAction.pretransitive_iff_subsingleton_quotient G X).mpr
    inferInstance

/-- If a subgroup is transitive on the original transitive set, it is also
transitive on the cosets of the original point stabilizer. -/
theorem stabilizerCosets_isPretransitive_of_isPretransitive
    {G X : Type} [Group G] [MulAction G X]
    [MulAction.IsPretransitive G X]
    (K : Subgroup G) [MulAction.IsPretransitive K X] (x : X) :
    MulAction.IsPretransitive K (G ⧸ MulAction.stabilizer G x) := by
  let e := MulAction.orbitEquivQuotientStabilizer G x
  constructor
  intro q r
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K
    ((e.symm q : MulAction.orbit G x) : X)
    ((e.symm r : MulAction.orbit G x) : X)
  refine ⟨k, e.symm.injective (Subtype.ext ?_)⟩
  change MulAction.ofQuotientStabilizer G x ((k : G) • q) =
    MulAction.ofQuotientStabilizer G x r
  rw [MulAction.ofQuotientStabilizer_smul]
  exact hk

end SymmetricSubgroupAsymptotics

end
