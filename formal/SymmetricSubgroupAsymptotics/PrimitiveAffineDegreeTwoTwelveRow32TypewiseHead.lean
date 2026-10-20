import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow32BinaryBlocks
import SymmetricSubgroupAsymptotics.RepresentationNormalCoinvariantSchurHead
import SymmetricSubgroupAsymptotics.NormalPSubgroupSimpleFixed

/-!
# The actual row-32 head bound for the scalar degree-two type

For every subrepresentation of the literal twelve-point permutation
module, maps to an actual simple target with binary dimension two and
endomorphism dimension two form a space of dimension at most four.

The nonextremal binary head rounds down by Schur divisibility. An
extremal head forces the original source to equal the augmentation sum,
whose two original orbit seeds give the same bound. The displayed target
dimensions are type invariants, not finite module-capacity certificates.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveRow32TypewiseHead


/-- Both branches retain the original numerator and actual top action. -/
theorem intertwining_finrank_le_four
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (sigma : Representation (ZMod 2) PrimitiveAffineDegreeTwoTwelveRow32BinaryChart.Top W)
    [IsSimpleModule (ZMod 2)[PrimitiveAffineDegreeTwoTwelveRow32BinaryChart.Top] sigma.asModule]
    (hdim : Module.finrank (ZMod 2) W = 2)
    (hEnd : Module.finrank (ZMod 2) (Module.End (ZMod 2)[PrimitiveAffineDegreeTwoTwelveRow32BinaryChart.Top] sigma.asModule) = 2)
    (M : Subrepresentation PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.representation) :
    Module.finrank (ZMod 2) (M.toRepresentation.IntertwiningMap sigma) ≤ 4 := by
  by_cases hhead : 6 ≤ Module.finrank (ZMod 2)
      ((PrimitiveAffineDegreeTwoTwelveRow32BinaryBlocks.restricted M).IntertwiningMap
        (Representation.trivial (ZMod 2) PrimitiveAffineDegreeTwoTwelveRow32BinaryBlocks.P (ZMod 2)))
  · rw [PrimitiveAffineDegreeTwoTwelveRow32BinaryBlocks.eq_augmentation_of_binary_head_ge_six M hhead]
    have h := PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.augmentation_hom_finrank_le_two_mul sigma
    simpa only [hdim] using h
  · letI : Finite W := Module.finite_of_finite (ZMod 2)
    have hfix := normal_pSubgroup_simple_representation_fixed
      sigma PrimitiveAffineDegreeTwoTwelveRow32BinaryChart.beta.ker PrimitiveAffineDegreeTwoTwelveRow32BinaryChart.binaryKernel_isPGroup
    exact intertwining_finrank_le_even_of_normal_coinvariant_head
      M.toRepresentation sigma PrimitiveAffineDegreeTwoTwelveRow32BinaryChart.beta.ker hfix hEnd 2 (by
        change Module.finrank (ZMod 2)
          ((PrimitiveAffineDegreeTwoTwelveRow32BinaryBlocks.restricted M).IntertwiningMap
            (Representation.trivial (ZMod 2) PrimitiveAffineDegreeTwoTwelveRow32BinaryBlocks.P (ZMod 2))) ≤ 2 * 2 + 1
        omega)

end PrimitiveAffineDegreeTwoTwelveRow32TypewiseHead
end SymmetricSubgroupAsymptotics

end
