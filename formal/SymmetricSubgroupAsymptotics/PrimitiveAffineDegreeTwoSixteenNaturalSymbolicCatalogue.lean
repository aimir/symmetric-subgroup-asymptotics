import SymmetricSubgroupAsymptotics.NaturalBinaryAlternatingCyclic
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenNaturalFiniteRows

/-!
# The natural degree-sixteen packages from symbolic cyclicity

The natural binary modules for `A_16` and `S_16` have a uniform one-generator
bound. Padding to four joins the existing structural quotient-socle fields
and closes the two-row natural catalogue without an invariant-vector census.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoSixteenNaturalFiniteRows

/-- Symbolic cyclicity of every natural `A_16` invariant binary subspace. -/
theorem alternatingNatural_uniform_one :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2)
        (naturalTopSubgroup .alternating) (Fin 16)) 1 := by
  apply NaturalBinaryAlternating.uniform_one
  · exact le_rfl
  · norm_num
  · norm_num

/-- Symbolic cyclicity of every natural `S_16` invariant binary subspace. -/
theorem symmetricNatural_uniform_one :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2)
        (naturalTopSubgroup .symmetric) (Fin 16)) 1 := by
  apply NaturalBinaryAlternating.uniform_one
  · exact le_top
  · norm_num
  · norm_num

/-- The natural alternating row, with its symbolic cyclic module bound
padded to the common four-place interface. -/
noncomputable def alternatingSymbolicRow :
    DegreeTwoSixteenNaturalFiniteRowData .alternating :=
  DegreeTwoSixteenNaturalFiniteRowData.alternatingOfNaturalModule
    (alternatingNatural_uniform_one.mono (by norm_num))

/-- The natural symmetric row, with its symbolic cyclic module bound
padded to the common four-place interface. -/
noncomputable def symmetricSymbolicRow :
    DegreeTwoSixteenNaturalFiniteRowData .symmetric :=
  DegreeTwoSixteenNaturalFiniteRowData.symmetricOfNaturalModule
    (symmetricNatural_uniform_one.mono (by norm_num))

/-- Both natural degree-sixteen rows, with no external module-bound input. -/
noncomputable def symbolicCatalogue : DegreeTwoSixteenNaturalFiniteCatalogueData where
  alternating := alternatingSymbolicRow
  symmetric := symmetricSymbolicRow

end DegreeTwoSixteenNaturalFiniteRows
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
