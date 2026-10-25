import SymmetricSubgroupAsymptotics.FiniteGroupPrimeMultiplicityGenerators
import SymmetricSubgroupAsymptotics.CoprimeNilpotentProductGenerators
import Mathlib.GroupTheory.OrderOfElement

/-! A genuine element of order four saves an ordinary generator over
the prime-multiplicity bound. The relative greedy construction begins
with its actual cyclic subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.FiniteGroupPrimeMultiplicityGeneratorSaving
open FiniteGroupPrimeMultiplicityGenerators

theorem genRank_add_one_le_of_order_four
    {G : Type*} [Group G] [Finite G] (g : G) (hg : orderOf g=4) :
    MarkedC4.genRank G + 1 ≤ ArithmeticFunction.cardFactors (Nat.card G) := by
  let R := Subgroup.zpowers g
  obtain ⟨S,_,hgen,hcard⟩ := exists_relative_generating_finset R ⊤ le_top
  have hR : ArithmeticFunction.cardFactors (Nat.card R)=2 := by
    have hc : Nat.card R=4 := by simpa only [R,Nat.card_zpowers] using hg
    rw [hc]
    decide +kernel
  have hbound : S.card+2 ≤ ArithmeticFunction.cardFactors (Nat.card G) := by
    simpa only [hR,Subgroup.card_top] using hcard
  have hT : Subgroup.closure ((insert g S : Finset G) : Set G)=⊤ := by
    rw [Finset.coe_insert,Set.insert_eq,Subgroup.closure_union,
      ←Subgroup.zpowers_eq_closure,sup_comm]
    have he : Subgroup.closure ((S : Set G) ∪ R)=
        Subgroup.closure (S : Set G) ⊔ R := by
      rw [Subgroup.closure_union,Subgroup.closure_eq]
    exact he.symm.trans hgen
  have hrank := MarkedC4.genRank_le hT
  have hsize := Finset.card_insert_le g S
  omega

/-- Every subgroup of a group containing an order-four element saves
one generator over the ambient prime-multiplicity count: a proper range
already loses a prime factor, and a full range uses the cyclic saving. -/
theorem genRank_add_one_le_of_injective_into_order_four
    {H G : Type} [Group H] [Group G] [Finite H] [Finite G]
    (f : H →* G) (hf : Function.Injective f) (g : G) (hg : orderOf g=4) :
    MarkedC4.genRank H + 1 ≤ ArithmeticFunction.cardFactors (Nat.card G) := by
  by_cases htop : f.range=⊤
  · let e : H ≃* G := MulEquiv.ofBijective f ⟨hf,MonoidHom.range_eq_top.mp htop⟩
    rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv e]
    exact genRank_add_one_le_of_order_four g hg
  · have hc : Nat.card H=Nat.card f.range :=
      Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
    have hle : Nat.card f.range ≤ Nat.card G :=
      Nat.card_le_card_of_injective f.range.subtype Subtype.val_injective
    have hlt : Nat.card f.range < Nat.card G := by
      by_contra h
      have he : Nat.card f.range=Nat.card G := by omega
      apply htop
      exact Subgroup.eq_of_le_of_card_ge le_top (by simpa only [Subgroup.card_top] using he.ge)
    have hOmega := cardFactors_add_one_le_of_dvd_lt (Nat.card_pos (α := f.range))
      (Subgroup.card_subgroup_dvd_card f.range) hlt
    rw [←hc] at hOmega
    exact (Nat.add_le_add_right (genRank_le_cardFactors H) 1).trans hOmega

end SymmetricSubgroupAsymptotics.FiniteGroupPrimeMultiplicityGeneratorSaving
