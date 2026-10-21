import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixFiveDivisibility
import SymmetricSubgroupAsymptotics.SixPointFiveCyclePrimitive

/-! Cauchy and the proved degree-six divisibility theorem give a literal
five-cycle and a point conjugacy in the unchanged actual primitive top. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSixActualCycleWitness

theorem exists_five_cycle
    (P : Subgroup (Equiv.Perm (Fin 6))) [MulAction.IsPreprimitive P (Fin 6)] :
    ∃ g : P,(g : Equiv.Perm (Fin 6)).IsCycle ∧
      (g : Equiv.Perm (Fin 6)).support.card=5 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' 5
    (primitive_degreeSix_five_dvd_card_without_catalogue (G := P) (X := Fin 6) (by simp))
  have ho : orderOf (g : Equiv.Perm (Fin 6))=5 :=
    (orderOf_injective P.subtype Subtype.coe_injective g).trans hg
  have hc : (g : Equiv.Perm (Fin 6)).IsCycle :=
    Equiv.Perm.isCycle_of_prime_order' (by rw [ho];decide) (by rw [ho];decide)
  exact ⟨g,hc,hc.orderOf.symm.trans ho⟩

private theorem standard_cycleType :
    SixPointFiveCyclePrimitive.cycle.cycleType=({5} : Multiset ℕ) := by decide +kernel

theorem exists_original_point_conjugacy
    (P : Subgroup (Equiv.Perm (Fin 6))) [MulAction.IsPreprimitive P (Fin 6)] :
    ∃ (g : P) (c : Equiv.Perm (Fin 6)),
      c*(g : Equiv.Perm (Fin 6))*c⁻¹=SixPointFiveCyclePrimitive.cycle := by
  obtain ⟨g,hg,hs⟩ := exists_five_cycle P
  have ht : (g : Equiv.Perm (Fin 6)).cycleType=SixPointFiveCyclePrimitive.cycle.cycleType := by
    rw [hg.cycleType,hs,standard_cycleType]
  obtain ⟨c,hc⟩ := isConj_iff.mp (Equiv.Perm.isConj_of_cycleType_eq ht)
  exact ⟨g,c,hc⟩

end SymmetricSubgroupAsymptotics.PrimitiveSixActualCycleWitness
