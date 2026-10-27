import SymmetricSubgroupAsymptotics.ThreeTransitiveNineOrdinaryGenerators
import SymmetricSubgroupAsymptotics.PrimitivePrimeCycleMultipleTransitivity
import SymmetricSubgroupAsymptotics.CFSGSolublePrimitiveContainersCover
import SymmetricSubgroupAsymptotics.PrimitiveAffineNineOrdinaryGenerators
import SymmetricSubgroupAsymptotics.BurnsideTwoPrimeSolvability
import Mathlib.Data.Nat.Factorization.Basic

/-! Every actual primitive degree9 permutation group has ordinary rank≤4.
A5/7-divisor gives one prime cycle and proved Marggraff gives3-transitivity.
Otherwise Burnside makes the actual group soluble and the proved affine9
consumer applies. No CFSG, simple model, Tracey or McIver-Neumann input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveNineOrdinaryGeneratorsWithoutClassification

private theorem solvable_of_no_five_seven (J : Subgroup (Equiv.Perm (Fin 9)))
    (h5 : ¬5 ∣ Nat.card J) (h7 : ¬7 ∣ Nat.card J) : IsSolvable J := by
  have hd : Nat.card J ∣ 362880 := by
    simpa only [Nat.card_perm,Nat.card_fin] using J.card_subgroup_dvd_card
  have hc5 : Nat.Coprime (Nat.card J) 5 :=
    ((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr h5).symm
  have hc7 : Nat.Coprime (Nat.card J) 7 :=
    ((by decide : Nat.Prime 7).coprime_iff_not_dvd.mpr h7).symm
  have hc : Nat.Coprime (Nat.card J) 35 := Nat.coprime_mul_iff_right.mpr ⟨hc5,hc7⟩
  have hd' : Nat.card J ∣ 10368 := hc.dvd_mul_right.mp hd
  obtain ⟨a,m,hnot2,he⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (Nat.card_pos (α := J)).ne' 2 (by decide : 2≠1)
  have hmcard : m ∣ Nat.card J := by
    rw [he]
    exact dvd_mul_left m (2^a)
  have hmdiv : m ∣ 2^7*3^4 := hmcard.trans hd'
  have hmcoprime : Nat.Coprime m (2^7) :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr hnot2).symm.pow_right 7
  have hmthree : m ∣ 3^4 := hmcoprime.dvd_mul_left.mp hmdiv
  obtain ⟨b,_hb,hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hmthree
  have horder : Nat.card J=2^a*3^b := by rw [he,hm]
  exact burnsideTwoPrimeSolvability.solvable J 2 3 a b
    Nat.prime_two Nat.prime_three horder

 theorem genRank_le_four_of_five_or_seven_dvd
    (J : Subgroup (Equiv.Perm (Fin 9))) (hp : MulAction.IsPreprimitive J (Fin 9))
    (hprime : 5 ∣ Nat.card J ∨ 7 ∣ Nat.card J) : MarkedC4.genRank J≤4 := by
  apply ThreeTransitiveNineOrdinaryGenerators.genRank_le_four
  rcases hprime with h5 | h7
  · letI : Fact (Nat.Prime 5) := ⟨by decide⟩
    obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := J) 5 h5
    have ho : orderOf (g : Equiv.Perm (Fin 9))=5 := (Subgroup.orderOf_coe g).trans hg
    have hc : (g : Equiv.Perm (Fin 9)).IsCycle := Equiv.Perm.isCycle_of_prime_order'
      (by rw [ho]; decide) (by rw [ho]; decide)
    have hs : (g : Equiv.Perm (Fin 9)).support.card=5 := hc.orderOf.symm.trans ho
    letI : MulAction.IsMultiplyPretransitive J (Fin 9) 5 :=
      PrimitivePrimeCycleMultipleTransitivity.isMultiplyPretransitive J hp
        (by decide : Nat.Prime 5) (by decide : 9=5+(3+1)) g.val hc hs g.property
    exact MulAction.isMultiplyPretransitive_of_le (by decide : 3≤5) (by simp)
  · letI : Fact (Nat.Prime 7) := ⟨by decide⟩
    obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := J) 7 h7
    have ho : orderOf (g : Equiv.Perm (Fin 9))=7 := (Subgroup.orderOf_coe g).trans hg
    have hc : (g : Equiv.Perm (Fin 9)).IsCycle := Equiv.Perm.isCycle_of_prime_order'
      (by rw [ho]; decide) (by rw [ho]; decide)
    have hs : (g : Equiv.Perm (Fin 9)).support.card=7 := hc.orderOf.symm.trans ho
    exact PrimitivePrimeCycleMultipleTransitivity.isMultiplyPretransitive J hp
      (by decide : Nat.Prime 7) (by decide : 9=7+(1+1)) g.val hc hs g.property

 theorem genRank_le_four (J : Subgroup (Equiv.Perm (Fin 9)))
    (hp : MulAction.IsPreprimitive J (Fin 9)) : MarkedC4.genRank J≤4 := by
  by_cases h5 : 5 ∣ Nat.card J
  · exact genRank_le_four_of_five_or_seven_dvd J hp (Or.inl h5)
  by_cases h7 : 7 ∣ Nat.card J
  · exact genRank_le_four_of_five_or_seven_dvd J hp (Or.inr h7)
  letI : IsSolvable J := solvable_of_no_five_seven J h5 h7
  letI : MulAction.IsPreprimitive J (Fin 9) := hp
  let P := Classical.choice (CFSGSolublePrimitiveContainers.soluble_primitive_profile J (Fin 9))
  exact PrimitiveAffineNineOrdinaryGenerators.genRank_le_four P hp (by simp)

end SymmetricSubgroupAsymptotics.PrimitiveNineOrdinaryGeneratorsWithoutClassification
