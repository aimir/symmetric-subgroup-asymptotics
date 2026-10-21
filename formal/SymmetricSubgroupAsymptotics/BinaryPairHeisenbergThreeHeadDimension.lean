import SymmetricSubgroupAsymptotics.BinaryPairLargeProductLowerLayer
import SymmetricSubgroupAsymptotics.BinaryHeisenbergEightNaturalHeads
import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerDimension

/-! The literal Heisenberg eight-point upper module has head at most
two. Hence a head-three original state cannot have a full actual product
layer, giving an exact dimension bound without a sixteen-point census. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics
local instance heisenbergThreeHeadDimensionPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private theorem heisenberg_eight_head_ceiling_le_two : ∀ i : Fin 15,
    BinaryHeisenbergEightNaturalHeads.headCeiling i≤2 := by decide +kernel

namespace BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (E : BinaryPairFrame U (Fin 8))

theorem heisenberg_head_three_dimension_add_kernel_le_sixteen
    (hU : IsPGroup 2 U) (hH : E.top.range=BinaryHeisenbergEightNaturalHeads.H)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hhead : 3≤Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) :
    Module.finrank (ZMod 2) W.toSubmodule+Module.finrank (ZMod 2) E.kernelSpace≤16 := by
  let S := E.literalPairLayer BinaryHeisenbergEightNaturalHeads.H hH (E.pairSumModuleLayer W)
  have hupp : Module.finrank (ZMod 2) (E.pairSumModuleLayer W).toRepresentation.Coinvariants≤2 := by
    have hh : Module.finrank (ZMod 2) S.toRepresentation.Coinvariants≤2 := by
      obtain ⟨i,hi⟩ := BinaryHeisenbergEightNaturalHeads.complete S
      rw [←hi]
      exact (BinaryHeisenbergEightNaturalHeads.coinvariants_finrank_le i).trans
        (heisenberg_eight_head_ceiling_le_two i)
    rwa [E.literalPairLayer_head] at hh
  by_contra hnot
  have hd := E.pairModuleLayers_finrank W
  have hL := Submodule.finrank_le (E.pairConstantModuleLayer W).toSubmodule
  have hp : Module.finrank (ZMod 2) (Fin 8 → ZMod 2)=8 := by simp
  rw [hp] at hL
  have hlarge : 8<Module.finrank (ZMod 2) E.kernelSpace+
      Module.finrank (ZMod 2) (E.pairSumModuleLayer W).toSubmodule := by omega
  have hh := E.pairModuleHead_le_upperHead_of_dimension_sum hU (0 : Fin 8) W hlarge
  omega

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
