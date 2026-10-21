import SymmetricSubgroupAsymptotics.BinarySplitRegular46FullConstantStabilizerData
import SymmetricSubgroupAsymptotics.BinaryPairScalarGraphCharts
import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerGraph

/-! A full constant layer removes the graph ambiguity. The checked
full-constant state is therefore the entire original module with the
specified literal layers, not a chosen projection or a replacement state. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private theorem fullconstant_state_sum_basis : ∀ j : Fin 12,
    (BinaryPairFrame.pairLayerFlatten.symm
      (BinarySplitRegular46FullConstantStabilizer.state.inclusion (Pi.single j 1))).2 ∈
        (BinaryRegularEightNaturalRegistry.charts 46).2.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel

namespace BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (E : BinaryPairFrame U (Fin 8))

theorem regular_fullconstant_layers_original_state
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hS : (E.pairSumModuleLayer W).toSubmodule =
      (BinaryRegularEightNaturalRegistry.charts 46).2.space)
    (hL : (E.pairConstantModuleLayer W).toSubmodule =
      (BinaryRegularEightNaturalRegistry.charts 1).2.space) :
    (E.originalCoordinateSubrepresentation W).toSubmodule =
      BinarySplitRegular46FullConstantStabilizer.state.space := by
  have hLtop : (E.pairConstantModuleLayer W).toSubmodule = ⊤ := by
    rw [hL]
    apply Submodule.eq_top_of_finrank_eq
    rw [(BinaryRegularEightNaturalRegistry.charts 1).2.finrank]
    change 8 = Module.finrank (ZMod 2) (Fin 8 → ZMod 2)
    simp
  apply E.originalCoordinateSubrepresentation_eq_chart W
    BinarySplitRegular46FullConstantStabilizer.state
  · rw [hS,hL]
    rw [(BinaryRegularEightNaturalRegistry.charts 46).2.finrank,
      (BinaryRegularEightNaturalRegistry.charts 1).2.finrank]
    change 4 + 8 = 12
    decide
  · intro j
    rw [E.pairModule_eq_pairSum_preimage_of_constant_top W hLtop]
    change E.pairSum (E.originalCoordinateEquiv.symm
      (BinarySplitRegular46FullConstantStabilizer.state.inclusion (Pi.single j 1))) ∈
        (E.pairSumModuleLayer W).toSubmodule
    rw [E.pairSum_originalCoordinateEquiv_symm,hS]
    exact fullconstant_state_sum_basis j

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
