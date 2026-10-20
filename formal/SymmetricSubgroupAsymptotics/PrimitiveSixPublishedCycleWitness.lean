import SymmetricSubgroupAsymptotics.PrimitiveSixFinalPublishedNormalGenerators
import SymmetricSubgroupAsymptotics.SixPointFiveCyclePrimitive

/-! The two existing final published inputs also give an actual five-cycle
inside the original primitive six-point group. Cauchy's theorem supplies
order five; the six-point degree makes that permutation a single cycle.
A conjugacy is returned on the original point set, not an abstract model. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveSixPublishedCycleWitness

open Non2UnipotentPrefixFiniteMenu

theorem exists_five_cycle
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (P : Subgroup (Equiv.Perm (Fin 6))) [MulAction.IsPreprimitive P (Fin 6)] :
    ∃ g : P, (g : Equiv.Perm (Fin 6)).IsCycle ∧
      (g : Equiv.Perm (Fin 6)).support.card = 5 := by
  obtain ⟨g,hg⟩ := PrimitiveSixFinalPublishedNormalGenerators.exists_order_five socle catalogue P
  have ho : orderOf (g : Equiv.Perm (Fin 6)) = 5 :=
    (orderOf_injective P.subtype Subtype.coe_injective g).trans hg
  have hcycle : (g : Equiv.Perm (Fin 6)).IsCycle :=
    Equiv.Perm.isCycle_of_prime_order' (by rw [ho]; decide) (by rw [ho]; decide)
  exact ⟨g,hcycle,hcycle.orderOf.symm.trans ho⟩

private theorem standard_cycleType :
    SixPointFiveCyclePrimitive.cycle.cycleType = ({5} : Multiset ℕ) := by
  decide +kernel

theorem exists_original_point_conjugacy
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (P : Subgroup (Equiv.Perm (Fin 6))) [MulAction.IsPreprimitive P (Fin 6)] :
    ∃ (g : P) (c : Equiv.Perm (Fin 6)),
      c * (g : Equiv.Perm (Fin 6)) * c⁻¹ = SixPointFiveCyclePrimitive.cycle := by
  obtain ⟨g,hg,hcard⟩ := exists_five_cycle socle catalogue P
  have ht : (g : Equiv.Perm (Fin 6)).cycleType = SixPointFiveCyclePrimitive.cycle.cycleType := by
    rw [hg.cycleType,hcard,standard_cycleType]
  obtain ⟨c,hc⟩ := isConj_iff.mp (Equiv.Perm.isConj_of_cycleType_eq ht)
  exact ⟨g,c,hc⟩

end SymmetricSubgroupAsymptotics.PrimitiveSixPublishedCycleWitness

end
