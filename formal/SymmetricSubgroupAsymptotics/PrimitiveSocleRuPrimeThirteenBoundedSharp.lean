import SymmetricSubgroupAsymptotics.CFSGRuSelectedProductPrimeThirteen
import SymmetricSubgroupAsymptotics.PrimitiveSocleLargePrimePairBoundedSharp

/-! The literal Ru AB/e0 prime-period certificate supplies13 dividing
the SAME original matrix model. Its checked actual two-generator theorem
then feeds the generic normalizer consumer; no whole matrix/group order
or outer budget is assumed. This extends the large-prime tag internally. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRuPrimeThirteenBoundedSharp
open PrimitiveSocleRawStructure CFSGReduction TraceySharpHalfDegreeNumerics

-- The checked Co3 installer uses this same opacity boundary: this file
-- transports group data, so array decoding must not enter group-instance
-- comparison. These remain the original literal definitions.
attribute [local irreducible] CFSG.Models.MatrixData.matrix
  CFSG.Models.MatrixData.generators CFSG.Models.MatrixGroups.Ru.rows1
  CFSG.Models.MatrixGroups.Ru.rows2

private theorem noncommutative_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hn : ¬IsMulCommutative A) : ¬IsMulCommutative B := by
  intro hc
  apply hn
  apply IsMulCommutative.of_comm
  intro a b
  apply e.injective
  rw [map_mul,map_mul]
  exact hc.is_comm.comm (e a) (e b)

private theorem pair_head_transport {A B : Type} [Group A] [Group B]
    (e : A ≃* B) (hpair : CFSGGeneration.TwoGenerated B) : MarkedC4.genRank A ≤ 2 := by
  obtain ⟨S,hS,hcard⟩ := CFSGGeneration.of_mulEquiv e.symm hpair
  exact (MarkedC4.genRank_le hS).trans hcard

def ExpandedLargePrimePairTag (s : CFSG.Sporadic) : Prop :=
  PrimitiveSocleLargePrimePairBoundedSharp.LargePrimePairTag s ∨ s=.ru

theorem genRank_le_sharpFloor_of_ru
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (hCFSG : CFSG.CFSGClassification) (hhi : Nat.card X ≤ 21)
    (e : D.Simple ≃* CFSG.Models.MatrixGroups.Ru.Model) :
    MarkedC4.genRank G ≤ sharpFloor (Nat.card X) := by
  have hn : ¬IsMulCommutative CFSG.Models.MatrixGroups.Ru.Model :=
    @noncommutative_transport D.Simple CFSG.Models.MatrixGroups.Ru.Model D.group
      (inferInstance : Group CFSG.Models.MatrixGroups.Ru.Model) e D.noncommutative
  have hd : 13 ∣ Nat.card D.Simple := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSGRuSelectedProductPrimeThirteen.thirteen_dvd_card hn
  have hhead : MarkedC4.genRank D.Simple ≤ 2 :=
    @pair_head_transport D.Simple CFSG.Models.MatrixGroups.Ru.Model D.group
      (inferInstance : Group CFSG.Models.MatrixGroups.Ru.Model) e CFSGGeneration.ru_twoGenerated
  exact PrimitiveSocleLargePrimePairBoundedSharp.genRank_le_sharpFloor_of_prime
    D hCFSG hhi 13 (by decide) (by decide) hd hhead

theorem not_ru_of_degree_le_ten
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (hsmall : Nat.card X ≤ 10)
    (e : D.Simple ≃* CFSG.Models.MatrixGroups.Ru.Model) : False := by
  have hn : ¬IsMulCommutative CFSG.Models.MatrixGroups.Ru.Model :=
    @noncommutative_transport D.Simple CFSG.Models.MatrixGroups.Ru.Model D.group
      (inferInstance : Group CFSG.Models.MatrixGroups.Ru.Model) e D.noncommutative
  have hd := PrimitiveSocleElevenPointTitsExclusion.simple_card_dvd_degree_factorial D
  rw [Nat.card_congr e.toEquiv] at hd
  have h13 : 13 ≤ Nat.card X := (show Nat.Prime 13 by decide).dvd_factorial.mp
    ((CFSGRuSelectedProductPrimeThirteen.thirteen_dvd_card hn).trans hd)
  omega

theorem genRank_le_sharpFloor_of_expanded_model
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (hCFSG : CFSG.CFSGClassification) (hhi : Nat.card X ≤ 21)
    (s : CFSG.Sporadic) (hs : ExpandedLargePrimePairTag s) (e : D.Simple ≃* s.Model) :
    MarkedC4.genRank G ≤ sharpFloor (Nat.card X) := by
  rcases hs with hs | rfl
  · exact PrimitiveSocleLargePrimePairBoundedSharp.genRank_le_sharpFloor_of_model D hCFSG hhi s hs e
  · exact genRank_le_sharpFloor_of_ru D hCFSG hhi e

end SymmetricSubgroupAsymptotics.PrimitiveSocleRuPrimeThirteenBoundedSharp
