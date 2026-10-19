import SymmetricSubgroupAsymptotics.NaturalFourNormalChains
import SymmetricSubgroupAsymptotics.FiniteNormalChainGenerators
import SymmetricSubgroupAsymptotics.NormalGeneratorQuotientSocles

/-! Every actual block image containing A4 is A4 or S4 and normally cyclic. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.AlternatingTopImageNormalGenerators

theorem above_alternating (B : Subgroup (Equiv.Perm (Fin 4)))
    (hAB : alternatingGroup (Fin 4)≤B) : B=alternatingGroup (Fin 4) ∨ B=⊤ := by
  have hm := Subgroup.relIndex_mul_index hAB
  rw [alternatingGroup.index_eq_two] at hm
  have hd : B.index∣2 := ⟨(alternatingGroup (Fin 4)).relIndex B,
    by simpa only [Nat.mul_comm] using hm.symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact Or.inr (Subgroup.index_eq_one.mp h)
  · left
    have hr : (alternatingGroup (Fin 4)).relIndex B=1 := by
      rw [h] at hm
      omega
    exact le_antisymm (Subgroup.relIndex_eq_one.mp hr) hAB

theorem normal_generating_singletons (B : Subgroup (Equiv.Perm (Fin 4)))
    (hAB : alternatingGroup (Fin 4)≤B) :
    ∀ N : Subgroup B, N.Normal →
      ∃ x : Fin 1 → B, Subgroup.normalClosure (Set.range x)=N := by
  rcases above_alternating B hAB with h | h
  · let E := MulEquiv.subgroupCongr h
    exact normal_generating_tuples_of_surjective E.symm.toMonoidHom E.symm.surjective
      (normal_generating_singletons_of_finite_normal_total
        NaturalFourNormalChains.alternating_normal_total)
  · let E : B ≃* Equiv.Perm (Fin 4) := MulEquiv.ofBijective B.subtype
      ⟨Subtype.val_injective,fun x => ⟨⟨x,by rw [h]; trivial⟩,rfl⟩⟩
    exact normal_generating_tuples_of_surjective E.symm.toMonoidHom E.symm.surjective
      (normal_generating_singletons_of_finite_normal_total
        NaturalFourNormalChains.symmetric_normal_total)

end SymmetricSubgroupAsymptotics.AlternatingTopImageNormalGenerators
