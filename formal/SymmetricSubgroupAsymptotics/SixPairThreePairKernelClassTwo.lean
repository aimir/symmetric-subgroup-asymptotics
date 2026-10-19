import SymmetricSubgroupAsymptotics.BinaryTwoLayerLocalClassTwo
import SymmetricSubgroupAsymptotics.SixPairThreePairKernelExponent

/-! Class two in the SAME original coarse kernel, transported through
literal restrictions to its physical four-point fibres. The kernel is not
replaced by a split model and is not assumed elementary. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairThreePairKernelClassTwo

variable {X I J : Type} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I) (E : ProductBlockFrame F.top.range J (ZMod 2))

/-- Every actual four-point restriction preserves the original two pairs. -/
theorem coordinate_preserves (j : J)
    (u : (SixPairNestedTopFrames.nestedFrame F E).top.ker) :
    BinaryTwoLayerLocalClassTwo.Preserves
      ((SixPairNestedTopFrames.nestedFrame F E).kernelCoordinate j u) := by
  intro x y hxy
  have hx := F.intertwine u.val (E.frame (j,x.1),x.2)
  have hy := F.intertwine u.val (E.frame (j,y.1),y.2)
  change
    (E.frame.symm ((F.frame.symm ((u.val : Equiv.Perm X)
      (F.frame (E.frame (j,x.1),x.2)))).1)).2 =
    (E.frame.symm ((F.frame.symm ((u.val : Equiv.Perm X)
      (F.frame (E.frame (j,y.1),y.2)))).1)).2
  rw [hx,hy,hxy]

/-- All commutators in the actual coarse kernel are central there. This
includes noncommutative nonsplit subgroups of the three local binary wreath
products. Centrality in the whole original group is NOT asserted. -/
theorem commutator_central
    (a b c : (SixPairNestedTopFrames.nestedFrame F E).top.ker) :
    (a*b*a⁻¹*b⁻¹)*c=c*(a*b*a⁻¹*b⁻¹) := by
  apply (SixPairNestedTopFrames.nestedFrame F E).kernelCoordinates_joint_injective
  funext j
  have h := BinaryTwoLayerLocalClassTwo.commutator_central
    ((SixPairNestedTopFrames.nestedFrame F E).kernelCoordinate j a)
    ((SixPairNestedTopFrames.nestedFrame F E).kernelCoordinate j b)
    ((SixPairNestedTopFrames.nestedFrame F E).kernelCoordinate j c)
    (coordinate_preserves F E j a) (coordinate_preserves F E j b)
    (coordinate_preserves F E j c)
  simpa only [map_mul,map_inv] using h

end SymmetricSubgroupAsymptotics.SixPairThreePairKernelClassTwo
