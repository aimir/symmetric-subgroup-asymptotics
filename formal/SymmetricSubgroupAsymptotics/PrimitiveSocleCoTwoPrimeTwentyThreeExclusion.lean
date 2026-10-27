import SymmetricSubgroupAsymptotics.CFSGCoTwoSelectedWordTwentyThreePrimeDivisor
import SymmetricSubgroupAsymptotics.PrimitiveSocleElevenPointTitsExclusion

/-! Prime23 in the SAME original Co2 presentation excludes small faithful
socle actions. The finite model instance comes only from the actual hit.
No period, order, external model recognition or new source callback remains. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleCoTwoPrimeTwentyThreeExclusion
open PrimitiveSocleRawStructure

theorem simple_twentyThree_dvd
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (e : D.Simple ≃* CFSG.Models.Presentations.Co2.Model) :
    23 ∣ Nat.card D.Simple := by
  letI : Finite CFSG.Models.Presentations.Co2.Model := Finite.of_equiv D.Simple e.toEquiv
  rw [Nat.card_congr e.toEquiv]
  exact CFSGCoTwoSelectedWordTwentyThreePrimeDivisor.twentyThree_dvd_card

theorem twentyThree_le_actual_degree
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (e : D.Simple ≃* CFSG.Models.Presentations.Co2.Model) :
    23 ≤ Nat.card X := by
  exact (show Nat.Prime 23 by decide).dvd_factorial.mp
    ((simple_twentyThree_dvd D e).trans
      (PrimitiveSocleElevenPointTitsExclusion.simple_card_dvd_degree_factorial D))

theorem not_coTwo_of_degree_le_twentyOne
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (hsmall : Nat.card X ≤ 21)
    (e : D.Simple ≃* CFSG.Models.Presentations.Co2.Model) : False := by
  have h23 := twentyThree_le_actual_degree D e
  omega

theorem not_coTwo_of_degree_le_ten
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (hsmall : Nat.card X ≤ 10)
    (e : D.Simple ≃* CFSG.Models.Presentations.Co2.Model) : False := by
  exact not_coTwo_of_degree_le_twentyOne D (by omega) e

end SymmetricSubgroupAsymptotics.PrimitiveSocleCoTwoPrimeTwentyThreeExclusion
