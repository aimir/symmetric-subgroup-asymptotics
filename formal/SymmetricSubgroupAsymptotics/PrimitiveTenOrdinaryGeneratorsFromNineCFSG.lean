import SymmetricSubgroupAsymptotics.NinePointHalfDegreeCompleteCFSG
import SymmetricSubgroupAsymptotics.PointStabilizerComplementFaithful
import SymmetricSubgroupAsymptotics.MaximalSubgroupOrdinaryGenerators

/-! An actual primitive10-point group has maximal point stabilizer with
faithful action on its actual complement9. The proved full nine-point
bound and one outside element give rank≤5. No primitivity or transitivity
of that complement action is asserted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveTenOrdinaryGeneratorsFromNineCFSG

 theorem genRank_le_five (hCFSG : CFSG.CFSGClassification)
    (J : Subgroup (Equiv.Perm (Fin 10))) (hp : MulAction.IsPreprimitive J (Fin 10)) :
    MarkedC4.genRank J≤5 := by
  letI : MulAction.IsPreprimitive J (Fin 10) := hp
  let x : Fin 10 := 0
  let H := MulAction.stabilizer J x
  let Y := SubMulAction.ofStabilizer J x
  letI : FaithfulSMul H Y := PointStabilizerComplementFaithful.faithfulSMul J (Fin 10) x
  have hY : Nat.card Y=9 := by
    simpa only [Nat.card_fin] using SubMulAction.nat_card_ofStabilizer_eq J x
  have hr := NinePointHalfDegreeCompleteCFSG.genRank_le_four_of_faithful (G := H) (X := Y) hCFSG hY
  have hcoat : IsCoatom H := (MulAction.isCoatom_stabilizer_iff_preprimitive J x).mpr hp
  have hJ := MaximalSubgroupOrdinaryGenerators.genRank_le_add_one H hcoat
  omega

end SymmetricSubgroupAsymptotics.PrimitiveTenOrdinaryGeneratorsFromNineCFSG
