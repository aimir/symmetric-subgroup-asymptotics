import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoPrimeTwentyThree
import SymmetricSubgroupAsymptotics.PrimitiveSocleElevenPointTitsExclusion

/-! The SAME pinned Co3 model's selected positive-word vector period23
excludes original faithful degree<=21. No whole matrix order, group order,
outer bound or replacement action/model is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleCoThreePrimeTwentyThreeExclusion
open PrimitiveSocleRawStructure

attribute [local irreducible] CFSG.Models.MatrixData.matrix
  CFSG.Models.MatrixData.generators CFSG.Models.MatrixGroups.Co3.rows1
  CFSG.Models.MatrixGroups.Co3.rows2

private theorem noncommutative_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hn : ¬IsMulCommutative A) : ¬IsMulCommutative B := by
  intro hc
  apply hn
  apply IsMulCommutative.of_comm
  intro a b
  apply e.injective
  rw [map_mul,map_mul]
  exact hc.is_comm.comm (e a) (e b)

theorem degree_ge_twentyThree
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (e : D.Simple ≃* CFSG.Models.MatrixGroups.Co3.Model) :
    23 ≤ Nat.card X := by
  have hn : ¬IsMulCommutative CFSG.Models.MatrixGroups.Co3.Model :=
    @noncommutative_transport D.Simple CFSG.Models.MatrixGroups.Co3.Model D.group
      (inferInstance : Group CFSG.Models.MatrixGroups.Co3.Model) e D.noncommutative
  have hd := PrimitiveSocleElevenPointTitsExclusion.simple_card_dvd_degree_factorial D
  rw [Nat.card_congr e.toEquiv] at hd
  exact (show Nat.Prime 23 by decide).dvd_factorial.mp
    ((CFSGCoThreeSelectedPositiveThirtyTwoPrimeTwentyThree.twenty_three_dvd_card hn).trans hd)

theorem not_co_three_of_degree_le_twentyOne
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (hsmall : Nat.card X ≤ 21)
    (e : D.Simple ≃* CFSG.Models.MatrixGroups.Co3.Model) : False := by
  have h := degree_ge_twentyThree D e
  omega

end SymmetricSubgroupAsymptotics.PrimitiveSocleCoThreePrimeTwentyThreeExclusion
