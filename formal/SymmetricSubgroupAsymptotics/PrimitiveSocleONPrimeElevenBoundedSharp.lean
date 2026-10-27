import SymmetricSubgroupAsymptotics.CFSGONSelectedProductPrimeEleven
import SymmetricSubgroupAsymptotics.PrimitiveSocleLargePrimePairBoundedSharp

/-! Consume the original ON prime11 vector certificate in the SAME actual
D. No period, capacity, order or model identification premise is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleONPrimeElevenBoundedSharp
open PrimitiveSocleRawStructure CFSGReduction TraceySharpHalfDegreeNumerics

attribute [local irreducible] CFSG.Models.MatrixData.matrix
  CFSG.Models.MatrixData.generators CFSG.Models.MatrixGroups.ON.rows1
  CFSG.Models.MatrixGroups.ON.rows2

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

theorem simple_eleven_dvd
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (e : D.Simple ≃* CFSG.Models.MatrixGroups.ON.Model) :
    11 ∣ Nat.card D.Simple := by
  have hn : ¬IsMulCommutative CFSG.Models.MatrixGroups.ON.Model :=
    @noncommutative_transport D.Simple CFSG.Models.MatrixGroups.ON.Model D.group
      (inferInstance : Group CFSG.Models.MatrixGroups.ON.Model) e D.noncommutative
  rw [Nat.card_congr e.toEquiv]
  exact CFSGONSelectedProductPrimeEleven.eleven_dvd_card hn

set_option maxRecDepth 4096 in
theorem genRank_le_sharpFloor_of_onan
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (hCFSG : CFSG.CFSGClassification) (hhi : Nat.card X ≤ 21)
    (e : D.Simple ≃* CFSG.Models.MatrixGroups.ON.Model) :
    MarkedC4.genRank G ≤ sharpFloor (Nat.card X) := by
  have hhead : MarkedC4.genRank D.Simple ≤ 2 :=
    @pair_head_transport D.Simple CFSG.Models.MatrixGroups.ON.Model D.group
      (inferInstance : Group CFSG.Models.MatrixGroups.ON.Model) e CFSGGeneration.onan_twoGenerated
  exact PrimitiveSocleLargePrimePairBoundedSharp.genRank_le_sharpFloor_of_prime
    D hCFSG hhi 11 (by decide) (by decide) (simple_eleven_dvd D e) hhead

theorem not_onan_of_degree_le_ten
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (hsmall : Nat.card X ≤ 10)
    (e : D.Simple ≃* CFSG.Models.MatrixGroups.ON.Model) : False := by
  have hd := PrimitiveSocleElevenPointTitsExclusion.simple_card_dvd_degree_factorial D
  have h11 : 11 ≤ Nat.card X := (show Nat.Prime 11 by decide).dvd_factorial.mp
    ((simple_eleven_dvd D e).trans hd)
  omega

end SymmetricSubgroupAsymptotics.PrimitiveSocleONPrimeElevenBoundedSharp
