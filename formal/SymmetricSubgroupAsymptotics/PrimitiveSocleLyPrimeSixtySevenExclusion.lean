import SymmetricSubgroupAsymptotics.CFSGLySelectedPositiveSevenPrimeSixtySeven
import SymmetricSubgroupAsymptotics.PrimitiveSocleElevenPointTitsExclusion

/-! The original selected prime67 vector certificate excludes the SAME
Ly factor in every faithful action of degree at most21. No full order,
model identification, pair-rank or outer budget is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleLyPrimeSixtySevenExclusion
open PrimitiveSocleRawStructure

attribute [local irreducible] CFSG.Models.MatrixData.matrix
  CFSG.Models.MatrixData.generators CFSG.Models.MatrixGroups.Ly.rows1
  CFSG.Models.MatrixGroups.Ly.rows2

private theorem noncommutative_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hn : ¬IsMulCommutative A) : ¬IsMulCommutative B := by
  intro hc
  apply hn
  apply IsMulCommutative.of_comm
  intro a b
  apply e.injective
  rw [map_mul,map_mul]
  exact hc.is_comm.comm (e a) (e b)

theorem degree_ge_sixtySeven
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (e : D.Simple ≃* CFSG.Models.MatrixGroups.Ly.Model) :
    67 ≤ Nat.card X := by
  have hn : ¬IsMulCommutative CFSG.Models.MatrixGroups.Ly.Model :=
    @noncommutative_transport D.Simple CFSG.Models.MatrixGroups.Ly.Model D.group
      (inferInstance : Group CFSG.Models.MatrixGroups.Ly.Model) e D.noncommutative
  have hd := PrimitiveSocleElevenPointTitsExclusion.simple_card_dvd_degree_factorial D
  rw [Nat.card_congr e.toEquiv] at hd
  exact (show Nat.Prime 67 by decide).dvd_factorial.mp
    ((CFSGLySelectedPositiveSevenPrimeSixtySeven.sixty_seven_dvd_card hn).trans hd)

theorem not_ly_of_degree_le_twentyOne
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (hsmall : Nat.card X ≤ 21)
    (e : D.Simple ≃* CFSG.Models.MatrixGroups.Ly.Model) : False := by
  have h := degree_ge_sixtySeven D e
  omega

end SymmetricSubgroupAsymptotics.PrimitiveSocleLyPrimeSixtySevenExclusion
