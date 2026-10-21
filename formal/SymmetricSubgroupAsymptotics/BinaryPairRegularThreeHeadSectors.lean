import SymmetricSubgroupAsymptotics.BinaryPairLargeProductLowerLayer
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryHeads
import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerDimension

/-! Exact original regular-top sectors above the small-order range.
Pointwise products force the full lower layer. The already complete
eight-point upper registry then leaves precisely its two head-three
spaces, with all original lift offsets and module correlations retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance regularThreeHeadSectorsPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (E : BinaryPairFrame U (Fin 8))

theorem regular_high_head_layers_of_large_product
    (hU : IsPGroup 2 U) (hH : E.top.range=BinaryRegularEightNaturalRegistry.H)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hlarge : 8<Module.finrank (ZMod 2) E.kernelSpace+
      Module.finrank (ZMod 2) (E.pairSumModuleLayer W).toSubmodule)
    (hhead : 3≤Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) :
    (E.pairConstantModuleLayer W).toSubmodule=⊤ ∧
      ((E.pairSumModuleLayer W).toSubmodule=(BinaryRegularEightNaturalRegistry.charts 45).2.space ∨
       (E.pairSumModuleLayer W).toSubmodule=(BinaryRegularEightNaturalRegistry.charts 46).2.space) := by
  have hLow := E.pairConstantLayer_eq_top_of_dimension_sum hU (0 : Fin 8) W hlarge
  have hupper := E.pairModuleHead_le_upperHead_of_dimension_sum hU (0 : Fin 8) W hlarge
  let S := E.literalPairLayer BinaryRegularEightNaturalRegistry.H hH (E.pairSumModuleLayer W)
  have hShead : 2<Module.finrank (ZMod 2) S.toRepresentation.Coinvariants := by
    rw [E.literalPairLayer_head]
    omega
  have hspace : S.toSubmodule=(E.pairSumModuleLayer W).toSubmodule :=
    E.literalPairLayer_space _ hH _
  refine ⟨hLow,?_⟩
  rcases BinaryRegularEightNaturalRegistry.head_gt_two_states S hShead with hs | hs
  · exact Or.inl (hspace.symm.trans ((congrArg Subrepresentation.toSubmodule hs).trans
      (BinaryRegularEightNaturalRegistry.states_space 45)))
  · exact Or.inr (hspace.symm.trans ((congrArg Subrepresentation.toSubmodule hs).trans
      (BinaryRegularEightNaturalRegistry.states_space 46)))

theorem regular45_head_three_large_dimension_layers
    (hU : IsPGroup 2 U) (hH : E.top.range=BinaryRegularEightNaturalRegistry.H)
    (hJ : E.kernelSpace=(BinaryRegularEightNaturalRegistry.charts 45).2.space)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hhead : 3≤Module.finrank (ZMod 2) W.toRepresentation.Coinvariants)
    (hdim : 11<Module.finrank (ZMod 2) W.toSubmodule) :
    (E.pairConstantModuleLayer W).toSubmodule=⊤ ∧
      ((E.pairSumModuleLayer W).toSubmodule=(BinaryRegularEightNaturalRegistry.charts 45).2.space ∨
       (E.pairSumModuleLayer W).toSubmodule=(BinaryRegularEightNaturalRegistry.charts 46).2.space) := by
  apply E.regular_high_head_layers_of_large_product hU hH W ?_ hhead
  have hd := E.pairModuleLayers_finrank W
  have hL := Submodule.finrank_le (E.pairConstantModuleLayer W).toSubmodule
  have hJdim : Module.finrank (ZMod 2) E.kernelSpace=7 := by
    rw [hJ]
    exact (BinaryRegularEightNaturalRegistry.charts 45).2.finrank
  have hp : Module.finrank (ZMod 2) (Fin 8 → ZMod 2)=8 := by simp
  rw [hp] at hL
  omega

theorem regular46_head_three_large_dimension_layers
    (hU : IsPGroup 2 U) (hH : E.top.range=BinaryRegularEightNaturalRegistry.H)
    (hJ : E.kernelSpace=(BinaryRegularEightNaturalRegistry.charts 46).2.space)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hhead : 3≤Module.finrank (ZMod 2) W.toRepresentation.Coinvariants)
    (hdim : 12<Module.finrank (ZMod 2) W.toSubmodule) :
    (E.pairConstantModuleLayer W).toSubmodule=⊤ ∧
      (E.pairSumModuleLayer W).toSubmodule=(BinaryRegularEightNaturalRegistry.charts 45).2.space := by
  have hd := E.pairModuleLayers_finrank W
  have hL := Submodule.finrank_le (E.pairConstantModuleLayer W).toSubmodule
  have hJdim : Module.finrank (ZMod 2) E.kernelSpace=4 := by
    rw [hJ]
    exact (BinaryRegularEightNaturalRegistry.charts 46).2.finrank
  have hp : Module.finrank (ZMod 2) (Fin 8 → ZMod 2)=8 := by simp
  rw [hp] at hL
  obtain ⟨hLow,h45 | h46⟩ := E.regular_high_head_layers_of_large_product hU hH W (by omega) hhead
  · exact ⟨hLow,h45⟩
  · have hs : Module.finrank (ZMod 2) (E.pairSumModuleLayer W).toSubmodule=4 := by
      rw [h46]
      exact (BinaryRegularEightNaturalRegistry.charts 46).2.finrank
    omega

end SymmetricSubgroupAsymptotics.BinaryPairFrame
