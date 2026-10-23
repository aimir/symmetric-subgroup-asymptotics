import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOddOutsideBypass

/-! Uniform odd-dimensional reconstruction in the literal signed unitary coordinates. The finite field may have order two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists

abbrev UnitaryOddOutside (q : CFSG.PrimePower) (m : ℕ) :=
  {x : Fin (2*m+5) → q.Extension 2 // unitaryNaturalPair q (2*m+4) x x = 0 ∧ x ∉ unitaryOddHalf q m}

def UnitaryOddOutsideAdjacent (q : CFSG.PrimePower) (m : ℕ) (R S : UnitaryOddOutside q m) : Prop :=
  unitaryNaturalPair q (2*m+4) R.val S.val = 0

private theorem path_of_independent_projection (q : CFSG.PrimePower) (m : ℕ)
    (R S : UnitaryOddOutside q m)
    (hproj : LinearIndependent (q.Extension 2) ![unitaryOddProjection q m R.val,
      unitaryOddProjection q m S.val]) :
    Relation.ReflTransGen (UnitaryOddOutsideAdjacent q m) R S := by
  by_cases hSR : unitaryNaturalPair q (2*m+4) S.val R.val = 0
  · exact Relation.ReflTransGen.single ((unitaryNaturalPair_zero_swap q (2*m+4) S.val R.val).mp hSR)
  obtain ⟨v,hv0,hvn,hvW,hRv,hSv⟩ := exists_unitary_odd_independent_projection_common_neighbor q m
    R.val S.val R.property.1 hSR hproj
  let V : UnitaryOddOutside q m := ⟨v,hvn,hvW⟩
  have hRV : UnitaryOddOutsideAdjacent q m R V := hRv
  have hVS : UnitaryOddOutsideAdjacent q m V S := (unitaryNaturalPair_zero_swap q (2*m+4) S.val v).mp hSv
  exact (Relation.ReflTransGen.single hRV).trans (Relation.ReflTransGen.single hVS)

theorem unitaryOdd_outside_connected (q : CFSG.PrimePower) (m : ℕ) (R S : UnitaryOddOutside q m) :
    Relation.ReflTransGen (UnitaryOddOutsideAdjacent q m) R S := by
  classical
  by_cases hproj : LinearIndependent (q.Extension 2) ![unitaryOddProjection q m R.val,
      unitaryOddProjection q m S.val]
  · exact path_of_independent_projection q m R S hproj
  obtain ⟨t,htn,htW,hRt,htproj⟩ := exists_unitaryOdd_outside_bypass q m R.val S.val
    R.property.1 S.property.1 R.property.2 S.property.2 hproj
  let T : UnitaryOddOutside q m := ⟨t,htn,htW⟩
  have hRT : UnitaryOddOutsideAdjacent q m R T := hRt
  exact (Relation.ReflTransGen.single hRT).trans (path_of_independent_projection q m T S htproj)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
