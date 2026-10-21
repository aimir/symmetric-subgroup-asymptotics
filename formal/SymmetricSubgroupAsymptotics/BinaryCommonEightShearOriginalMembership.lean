import SymmetricSubgroupAsymptotics.BinaryCommonEightShearCoordinates

/-! Common shear monomials belong to the same original invariant kernel,
via the explicit original-point labels and reversible coordinate map. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U (Fin 8))

def originalPointMonomial (b : Fin 16) : X → ZMod 2 := fun x =>
  BinaryCommonEightShearCoordinates.originalMonomial b (F.canonicalPointLabels x)

theorem originalPointMonomial_coordinates (b : Fin 16) :
    F.originalCoordinateEquiv (F.originalPointMonomial b) =
      binaryEightCanonicalLayerChange
        (BinaryCommonEightShearCoordinates.originalMonomial b) := by
  rw [F.originalCoordinateEquiv_canonicalPointLabels]
  apply congrArg binaryEightCanonicalLayerChange
  funext j
  change BinaryCommonEightShearCoordinates.originalMonomial b
    (F.canonicalPointLabels (F.canonicalPointLabels.symm j)) = _
  rw [Equiv.apply_symm_apply]

theorem originalPointMonomial_mem_of_coordinate_mem
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (b : Fin 16)
    (hb : binaryEightCanonicalLayerChange
      (BinaryCommonEightShearCoordinates.originalMonomial b) ∈
        (F.originalCoordinateSubrepresentation W).toSubmodule) :
    F.originalPointMonomial b ∈ W.toSubmodule := by
  have hm : F.originalCoordinateEquiv (F.originalPointMonomial b) ∈
      (F.originalCoordinateSubrepresentation W).toSubmodule := by
    rwa [F.originalPointMonomial_coordinates]
  have hm' := (F.mem_originalCoordinateSubrepresentation_iff W _).mp hm
  simpa only [LinearEquiv.symm_apply_apply] using hm'

theorem regular_zero_originalPointMonomial_mem
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hW : (F.originalCoordinateSubrepresentation W).toSubmodule =
      (BinaryRegular46GraphHeadRigidity.stateChart 0).space)
    (b : Fin 16) (hb : BinaryThreeVariablePairMonomialWidth.Allowed
      (BinaryElementaryPairMonomialWidth.support b)) :
    F.originalPointMonomial b ∈ W.toSubmodule := by
  apply F.originalPointMonomial_mem_of_coordinate_mem W b
  rw [hW]
  exact BinaryCommonEightShearCoordinates.regular_zero_contains_common_monomials b hb

theorem heisenberg_zero_originalPointMonomial_mem
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hW : (F.originalCoordinateSubrepresentation W).toSubmodule =
      (BinaryHeisenberg14GraphHeadRigidity.stateChart 0).space)
    (b : Fin 16) (hb : BinaryThreeVariablePairMonomialWidth.Allowed
      (BinaryElementaryPairMonomialWidth.support b)) :
    F.originalPointMonomial b ∈ W.toSubmodule := by
  apply F.originalPointMonomial_mem_of_coordinate_mem W b
  rw [hW]
  exact BinaryCommonEightShearCoordinates.heisenberg_zero_contains_common_monomials b hb

theorem elementary_zero_originalPointMonomial_mem
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hW : (F.originalCoordinateSubrepresentation W).toSubmodule =
      (BinaryElementary16GraphHeadRigidity.stateChart 0).space)
    (b : Fin 16) (hb : BinaryThreeVariablePairMonomialWidth.Allowed
      (BinaryElementaryPairMonomialWidth.support b)) :
    F.originalPointMonomial b ∈ W.toSubmodule := by
  apply F.originalPointMonomial_mem_of_coordinate_mem W b
  rw [hW]
  exact BinaryCommonEightShearCoordinates.elementary_zero_contains_common_monomials b hb

end SymmetricSubgroupAsymptotics.BinaryPairFrame
