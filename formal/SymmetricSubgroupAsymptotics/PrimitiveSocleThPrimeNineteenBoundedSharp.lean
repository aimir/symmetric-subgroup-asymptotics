import SymmetricSubgroupAsymptotics.CFSGThSelectedProductPrimeNineteen
import SymmetricSubgroupAsymptotics.PrimitiveSocleLargePrimePairBoundedSharp

/-! Consume the original Th prime19 vector certificate in the SAME actual
D. There is no supplied period, capacity or order premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleThPrimeNineteenBoundedSharp
open PrimitiveSocleRawStructure CFSGReduction TraceySharpHalfDegreeNumerics

attribute [local irreducible] CFSG.Models.MatrixData.matrix
  CFSG.Models.MatrixData.generators CFSG.Models.MatrixGroups.Th.rows1
  CFSG.Models.MatrixGroups.Th.rows2

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

theorem simple_nineteen_dvd
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (e : D.Simple ≃* CFSG.Models.MatrixGroups.Th.Model) :
    19 ∣ Nat.card D.Simple := by
  have hn : ¬IsMulCommutative CFSG.Models.MatrixGroups.Th.Model :=
    @noncommutative_transport D.Simple CFSG.Models.MatrixGroups.Th.Model D.group
      (inferInstance : Group CFSG.Models.MatrixGroups.Th.Model) e D.noncommutative
  rw [Nat.card_congr e.toEquiv]
  exact CFSGThSelectedProductPrimeNineteen.nineteen_dvd_card hn

set_option maxRecDepth 4096 in
theorem genRank_le_sharpFloor_of_th
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (hCFSG : CFSG.CFSGClassification) (hhi : Nat.card X ≤ 21)
    (e : D.Simple ≃* CFSG.Models.MatrixGroups.Th.Model) :
    MarkedC4.genRank G ≤ sharpFloor (Nat.card X) := by
  have hhead : MarkedC4.genRank D.Simple ≤ 2 :=
    @pair_head_transport D.Simple CFSG.Models.MatrixGroups.Th.Model D.group
      (inferInstance : Group CFSG.Models.MatrixGroups.Th.Model) e CFSGGeneration.th_twoGenerated
  exact PrimitiveSocleLargePrimePairBoundedSharp.genRank_le_sharpFloor_of_prime
    D hCFSG hhi 19 (by decide) (by decide) (simple_nineteen_dvd D e) hhead

theorem not_th_of_degree_le_ten
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (hsmall : Nat.card X ≤ 10)
    (e : D.Simple ≃* CFSG.Models.MatrixGroups.Th.Model) : False := by
  have hd := PrimitiveSocleElevenPointTitsExclusion.simple_card_dvd_degree_factorial D
  have h19 : 19 ≤ Nat.card X := (show Nat.Prime 19 by decide).dvd_factorial.mp
    ((simple_nineteen_dvd D e).trans hd)
  omega

end SymmetricSubgroupAsymptotics.PrimitiveSocleThPrimeNineteenBoundedSharp
