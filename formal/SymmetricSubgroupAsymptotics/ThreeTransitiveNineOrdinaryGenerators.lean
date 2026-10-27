import SymmetricSubgroupAsymptotics.PrimitiveEightOrdinaryGeneratorsFromCanonicalCoverage
import SymmetricSubgroupAsymptotics.FaithfulFiniteActionImage
import SymmetricSubgroupAsymptotics.PointStabilizerComplementFaithful
import SymmetricSubgroupAsymptotics.MaximalSubgroupOrdinaryGenerators
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-! Every actual faithful3-transitive degree9 action has rank≤4.
The point stabilizer's actual complement8 is2-transitive, so the proved
primitive8 rank3 theorem applies, with no simple-socle recognition. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ThreeTransitiveNineOrdinaryGenerators

theorem primitive_eight_genRank_le_three {H X : Type} [Group H] [Finite H]
    [Finite X] [MulAction H X] [FaithfulSMul H X]
    (hp : MulAction.IsPreprimitive H X) (hdegree : Nat.card X=8) :
    MarkedC4.genRank H≤3 := by
  letI : MulAction.IsPreprimitive H X := hp
  let points : X ≃ Fin 8 := Finite.equivFinOfCardEq hdegree
  have hi : MulAction.IsPreprimitive (labelledActionImage (A := H) points) (Fin 8) :=
    (labelledAction_preprimitive_iff points).mp hp
  exact (CoprimeNilpotentProductGenerators.genRank_mulEquiv (faithfulLabelledActionEquiv points)).le.trans
    (PrimitiveEightOrdinaryGeneratorsFromCanonicalCoverage.genRank_le_three _ hi)

theorem genRank_le_four {G : Type} [Group G] [Finite G]
    [MulAction G (Fin 9)] [FaithfulSMul G (Fin 9)]
    (h3 : MulAction.IsMultiplyPretransitive G (Fin 9) 3) : MarkedC4.genRank G≤4 := by
  letI : MulAction.IsMultiplyPretransitive G (Fin 9) 3 := h3
  letI : MulAction.IsMultiplyPretransitive G (Fin 9) 2 :=
    MulAction.isMultiplyPretransitive_of_le (by decide : 2≤3) (by simp)
  letI : MulAction.IsPretransitive G (Fin 9) := MulAction.isPretransitive_of_is_two_pretransitive
  have hp : MulAction.IsPreprimitive G (Fin 9) :=
    MulAction.isPreprimitive_of_is_two_pretransitive inferInstance
  let x : Fin 9 := 0
  let H := MulAction.stabilizer G x
  let Y := SubMulAction.ofStabilizer G x
  have h2 : MulAction.IsMultiplyPretransitive H Y 2 :=
    (SubMulAction.ofStabilizer.isMultiplyPretransitive (G := G) (a := x)).mp h3
  have hpH : MulAction.IsPreprimitive H Y := MulAction.isPreprimitive_of_is_two_pretransitive h2
  have hY : Nat.card Y=8 := by
    simpa only [Nat.card_fin] using SubMulAction.nat_card_ofStabilizer_eq G x
  letI : FaithfulSMul H Y := PointStabilizerComplementFaithful.faithfulSMul G (Fin 9) x
  have hr := primitive_eight_genRank_le_three hpH hY
  have hcoat : IsCoatom H := (MulAction.isCoatom_stabilizer_iff_preprimitive G x).mpr hp
  have hG := MaximalSubgroupOrdinaryGenerators.genRank_le_add_one H hcoat
  omega

end SymmetricSubgroupAsymptotics.ThreeTransitiveNineOrdinaryGenerators
