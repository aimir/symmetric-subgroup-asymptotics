import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenOddOrbitFrames
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTensorOddFrames
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenRemainingOddFrames
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenOtherTensorFrames
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenNaturalOddFrames

/-! The complete literal list of twenty affine primitive-sixteen actions
and the two natural actions satisfies one original-normal/frame budget.
Every local two-dimensional representation is covered, so no stabilizer
quotient eligibility classification is needed. Catalogue exhaustiveness
and exact canonical binding remain separate from this proved estimate. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenAllLiteralFrames
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

def top : Fin 22 → Subgroup (Equiv.Perm (Fin 16)) :=
  ![DegreeTwoPrimitiveSixteenInterfaces.Row1Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row2Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row3Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row4Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row5Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row6Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row7Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row8Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row9Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row10Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row11Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row12Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row13Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row14Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row15Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row16Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row17Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row18Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row19Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row20Top,
    DegreeTwoSixteenNaturalFiniteRows.naturalTopSubgroup .alternating,
    DegreeTwoSixteenNaturalFiniteRows.naturalTopSubgroup .symmetric]

theorem quotientSocle (j : Fin 22)
    (N : {N : Subgroup (top j) // N.Normal}) :
    SocleNormalGeneratorBound (top j ⧸ N.1) 2 := by
  fin_cases j
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.topSocle N
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow2AffineSocles.topSocle N
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow3AffineSocles.topSocle N
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow4AffineSocles.topSocle N
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow5AffineSocles.topSocle N
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow6AffineSocles.topSocle N
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow7AffineSocles.topSocle N
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow8AffineSocles.topSocle N
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow9AffineSocles.topSocle N
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow10AffineSocles.topSocle N
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow11AffineSocles.topSocle N
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow12AffineSocles.topSocle N
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow13AffineSocles.topSocle N
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow14AffineSocles.topSocle N
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow15AffineSocles.topSocle N
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow16AffineSocles.topSocle N
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow17AffineSocles.topSocle N
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow18AffineSocles.topSocle N
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow19AffineSocles.topSocle N
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow20AffineSocles.topSocle N
  · exact DegreeTwoSixteenNaturalFiniteRows.alternatingTopSocle N
  · exact DegreeTwoSixteenNaturalFiniteRows.symmetricTopSocle N

theorem relative_head_le_two (j : Fin 22)
    (N : Subgroup (top j)) [N.Normal] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤ 2 :=
  primeRelativeHead_le_of_all_quotient_socles 2 2 (quotientSocle j) N

theorem original_head_le_eight (j : Fin 22)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (x : Fin 16) (rho : Representation (ZMod 2) (MulAction.stabilizer (top j) x) V)
    (hdim : Module.finrank (ZMod 2) V = 2)
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer (top j) x).subtype rho)) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) (top j) (ZMod 2))) ≤ 8 := by
  fin_cases j
  · exact PrimitiveAffineSixteenRemainingOddFrames.original_head_le_eight 0 x rho hdim B
  · exact PrimitiveAffineSixteenRemainingOddFrames.original_head_le_eight 1 x rho hdim B
  · exact (PrimitiveAffineSixteenOddOrbitFrames.original_head_le_four 0 x rho hdim B).trans (by decide)
  · exact PrimitiveAffineSixteenTensorOddFrames.original_head_le_eight 0 x rho hdim B
  · exact PrimitiveAffineSixteenRemainingOddFrames.original_head_le_eight 2 x rho hdim B
  · exact (PrimitiveAffineSixteenOddOrbitFrames.original_head_le_four 1 x rho hdim B).trans (by decide)
  · exact PrimitiveAffineSixteenTensorOddFrames.original_head_le_eight 1 x rho hdim B
  · exact PrimitiveAffineSixteenOtherTensorFrames.original_head_le_eight 0 x rho hdim B
  · exact (PrimitiveAffineSixteenOddOrbitFrames.original_head_le_four 2 x rho hdim B).trans (by decide)
  · exact PrimitiveAffineSixteenOtherTensorFrames.original_head_le_eight 1 x rho hdim B
  · exact PrimitiveAffineSixteenRemainingOddFrames.original_head_le_eight 3 x rho hdim B
  · exact (PrimitiveAffineSixteenOddOrbitFrames.original_head_le_four 3 x rho hdim B).trans (by decide)
  · exact PrimitiveAffineSixteenRemainingOddFrames.original_head_le_eight 4 x rho hdim B
  · exact (PrimitiveAffineSixteenOddOrbitFrames.original_head_le_four 4 x rho hdim B).trans (by decide)
  · exact PrimitiveAffineSixteenRemainingOddFrames.original_head_le_eight 5 x rho hdim B
  · exact PrimitiveAffineSixteenRemainingOddFrames.original_head_le_eight 6 x rho hdim B
  · exact PrimitiveAffineSixteenRemainingOddFrames.original_head_le_eight 7 x rho hdim B
  · exact PrimitiveAffineSixteenRemainingOddFrames.original_head_le_eight 8 x rho hdim B
  · exact PrimitiveAffineSixteenRemainingOddFrames.original_head_le_eight 9 x rho hdim B
  · exact PrimitiveAffineSixteenRemainingOddFrames.original_head_le_eight 10 x rho hdim B
  · exact (PrimitiveAffineSixteenNaturalOddFrames.original_head_le_four .alternating x rho hdim B).trans (by decide)
  · exact (PrimitiveAffineSixteenNaturalOddFrames.original_head_le_four .symmetric x rho hdim B).trans (by decide)

theorem original_frame_sum_le_ten (j : Fin 22)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (x : Fin 16) (rho : Representation (ZMod 2) (MulAction.stabilizer (top j) x) V)
    (hdim : Module.finrank (ZMod 2) V = 2)
    (N : Subgroup (top j)) [N.Normal]
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer (top j) x).subtype rho)) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) +
      Module.finrank (ZMod 2)
        (B.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod 2) (top j) (ZMod 2))) ≤ 10 := by
  have hn := relative_head_le_two j N
  have hb := original_head_le_eight j x rho hdim B
  omega

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenAllLiteralFrames
end
