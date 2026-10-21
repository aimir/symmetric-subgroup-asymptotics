import SymmetricSubgroupAsymptotics.BinaryPairSubgroupRestriction
import SymmetricSubgroupAsymptotics.BinaryRegularEightSixKernelHead

/-! The selected six-kernel head-three theorem also applies after
restricting to an actual regular-eight subgroup of a larger top. The
original source module and inner kernel are unchanged by restriction. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (E : BinaryPairFrame U (Fin 8))

theorem naturalModuleHead_le_three_of_regular_subgroup_kernel_dimension_six
    (hregular : BinaryRegularEightNaturalRegistry.H ≤ E.top.range)
    (hdim : Module.finrank (ZMod 2) E.kernelSpace = 6)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X)) :
    Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ 3 := by
  let H := BinaryRegularEightNaturalRegistry.H
  let V := E.topSubgroupPreimage H
  let j : V →* U := Subgroup.inclusion (E.topSubgroupPreimage_le H)
  let rho := permutationFunctionRepresentation (ZMod 2) U X
  let tau := permutationFunctionRepresentation (ZMod 2) V X
  have he (v : V) (x : X → ZMod 2) : rho (j v) x = tau v x := rfl
  let M := restrictionSameVectors rho tau j he W
  have hh := restrictionSameVectors_head_le rho tau j he W
  have hd : Module.finrank (ZMod 2) (E.restrictTopSubgroup H).kernelSpace = 6 := by
    rw [E.restrictTopSubgroup_kernelSpace]
    exact hdim
  have hb := (E.restrictTopSubgroup H).naturalModuleHead_le_three_of_regular_kernel_dimension_six
    (E.restrictTopSubgroup_range H hregular) hd M
  exact hh.trans hb

end SymmetricSubgroupAsymptotics.BinaryPairFrame
