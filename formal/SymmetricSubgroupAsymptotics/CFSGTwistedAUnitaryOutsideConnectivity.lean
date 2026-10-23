import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOutsideBypass

/-! The literal singular vectors outside the four-dimensional half-sum
form one connected orthogonality graph. The proportional-projection case
is bypassed inside the original standard plane, including q2. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists

abbrev UnitaryRankFourOutside (q : CFSG.PrimePower) :=
  {x : Fin 5 → q.Extension 2 // unitaryNaturalPair q 4 x x = 0 ∧ x ∉ unitaryRankFourHalf q}

def UnitaryRankFourOutsideAdjacent (q : CFSG.PrimePower) (R S : UnitaryRankFourOutside q) : Prop :=
  unitaryNaturalPair q 4 R.val S.val = 0

private theorem path_of_independent_projection (q : CFSG.PrimePower)
    (R S : UnitaryRankFourOutside q)
    (hproj : LinearIndependent (q.Extension 2) ![unitaryRankFourProjection q R.val,
      unitaryRankFourProjection q S.val]) :
    Relation.ReflTransGen (UnitaryRankFourOutsideAdjacent q) R S := by
  by_cases hSR : unitaryNaturalPair q 4 S.val R.val = 0
  · exact Relation.ReflTransGen.single ((unitaryNaturalPair_zero_swap q 4 S.val R.val).mp hSR)
  obtain ⟨v,hv0,hvn,hvW,hRv,hSv⟩ := exists_unitary_independent_projection_common_neighbor q
    R.val S.val R.property.1 hSR hproj
  let V : UnitaryRankFourOutside q := ⟨v,hvn,hvW⟩
  have hRV : UnitaryRankFourOutsideAdjacent q R V := hRv
  have hVS : UnitaryRankFourOutsideAdjacent q V S := (unitaryNaturalPair_zero_swap q 4 S.val v).mp hSv
  exact (Relation.ReflTransGen.single hRV).trans (Relation.ReflTransGen.single hVS)

theorem unitaryRankFour_outside_connected (q : CFSG.PrimePower) (R S : UnitaryRankFourOutside q) :
    Relation.ReflTransGen (UnitaryRankFourOutsideAdjacent q) R S := by
  classical
  by_cases hproj : LinearIndependent (q.Extension 2) ![unitaryRankFourProjection q R.val,
      unitaryRankFourProjection q S.val]
  · exact path_of_independent_projection q R S hproj
  obtain ⟨t,htn,htW,hRt,htproj⟩ := exists_unitaryRankFour_outside_bypass q R.val S.val
    R.property.1 S.property.1 R.property.2 S.property.2 hproj
  let T : UnitaryRankFourOutside q := ⟨t,htn,htW⟩
  have hRT : UnitaryRankFourOutsideAdjacent q R T := hRt
  exact (Relation.ReflTransGen.single hRT).trans (path_of_independent_projection q T S htproj)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
