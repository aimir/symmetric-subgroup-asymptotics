import SymmetricSubgroupAsymptotics.BinaryPermutationPointwiseProductFull
import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerTopTransport
import SymmetricSubgroupAsymptotics.BinaryPairLargeSectionCharacter

/-! Large actual pair-sum and kernel dimensions force the FULL original
lower layer. The actual pointwise products already vanish in the head,
so in this case the original whole head is bounded by the upper head. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance largeProductLowerLayerPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w)) [MulAction.IsPretransitive U X]

theorem actual_kernel_pairSum_product_eq_top_of_dimension_sum
    (hU : IsPGroup 2 U) (i : Fin w)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hlarge : w < Module.finrank (ZMod 2) F.kernelSpace+
      Module.finrank (ZMod 2) (F.pairSumModuleLayer W).toSubmodule) :
    binaryCoordinateProductSpan F.kernelSpace (F.pairSumModuleLayer W).toSubmodule=⊤ := by
  letI : MulAction.IsPretransitive F.top.range (Fin w) := F.top_pretransitive
  exact binary_pointwise_productSpan_eq_top_of_dimension_sum (F.top_isPGroup hU) i
    F.kernelTopPermutationSubrepresentation (F.descendPairLayer (F.pairSumModuleLayer W)) hlarge

theorem pairConstantLayer_eq_top_of_dimension_sum
    (hU : IsPGroup 2 U) (i : Fin w)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hlarge : w < Module.finrank (ZMod 2) F.kernelSpace+
      Module.finrank (ZMod 2) (F.pairSumModuleLayer W).toSubmodule) :
    (F.pairConstantModuleLayer W).toSubmodule=⊤ := by
  have hh := F.actual_kernel_pairSum_product_le_constantLayer W
  rw [F.actual_kernel_pairSum_product_eq_top_of_dimension_sum hU i W hlarge] at hh
  exact top_le_iff.mp hh

theorem pairModuleHead_le_upperHead_of_dimension_sum
    (hU : IsPGroup 2 U) (i : Fin w)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hlarge : w < Module.finrank (ZMod 2) F.kernelSpace+
      Module.finrank (ZMod 2) (F.pairSumModuleLayer W).toSubmodule) :
    Module.finrank (ZMod 2) W.toRepresentation.Coinvariants≤
      Module.finrank (ZMod 2) (F.pairSumModuleLayer W).toRepresentation.Coinvariants := by
  have hprod := F.actual_kernel_pairSum_product_eq_top_of_dimension_sum hU i W hlarge
  have hden : F.pairLayerProductDenominator W=⊤ := by
    unfold pairLayerProductDenominator
    rw [hprod,Submodule.comap_top,top_sup_eq]
  have hh := F.pairModuleHead_le_product_quotient_add W
  rw [hden] at hh
  simpa only [Module.finrank_zero_of_subsingleton,zero_add] using hh

end SymmetricSubgroupAsymptotics.BinaryPairFrame
