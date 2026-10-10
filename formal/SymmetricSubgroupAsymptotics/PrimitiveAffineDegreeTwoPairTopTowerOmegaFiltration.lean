import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopTowerQuotient
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoRelativeKernelOrbitAnchor

/-!
# The omega filtration through two pair kernels

The central omega of the direct two-frame kernel maps onto its actual image
in the second section module.  This file records that map equivariantly for
the original quotient action, retaining the literal kernels and charts.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairTopTowerRealization

variable {s t : ℕ} {D : DegreeTwoPairTopFiniteInterface t}
  {p : PreE7PairActionClass s}
  (R : DegreeTwoPairTopTowerRealization D p)

/-- Projection to the second kernel commutes with ambient conjugation on
the intrinsic central omega. -/
theorem rawKernelOmegaProjection_conjugate
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (q : preE7PairAction s p ⧸ N.1)
    (z : binaryCentralOmega (R.rawQuotientMap N).ker) :
    R.rawKernelOmegaProjection N
        (binaryKernelOmegaConjugateOmega (R.rawQuotientMap N) q z) =
      MulAut.conjNormal (R.outerQuotientMap N q)
        (R.rawKernelOmegaProjection N z) := by
  apply Subtype.ext
  change R.outerQuotientMap N
      ((binaryKernelOmegaConjugate
        (R.rawQuotientMap N) q z : (R.rawQuotientMap N).ker) :
          preE7PairAction s p ⧸ N.1) =
    R.outerQuotientMap N q *
      (R.rawKernelOmegaProjection N z :
        R.frame.top.range ⧸ R.outerTopNormal N.1) *
      (R.outerQuotientMap N q)⁻¹
  rw [binaryKernelOmegaConjugate_val, map_mul, map_mul, map_inv]
  rfl

/-- The projected omega coordinate map is equivariant for the original
quotient, with the second section action pulled back along the direct map. -/
theorem rawKernelOmegaInnerSectionMap_equivariant
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (q : preE7PairAction s p ⧸ N.1)
    (z : binaryCentralOmega (R.rawQuotientMap N).ker) :
    R.rawKernelOmegaInnerSectionMap N
        (binaryKernelOmegaConjugationRepresentation
          (R.rawQuotientMap N) q (Additive.ofMul z)) =
      (R.innerSectionModule N).ρ (R.rawQuotientMap N q)
        (R.rawKernelOmegaInnerSectionMap N (Additive.ofMul z)) := by
  let E := R.innerSectionModuleChart N
  change (E.equiv.symm
      (R.rawKernelOmegaProjection N
        (binaryKernelOmegaConjugateOmega
          (R.rawQuotientMap N) q z))).toAdd =
    (R.innerSectionModule N).ρ
      (R.innerQuotientMap N (R.outerQuotientMap N q))
      (E.equiv.symm (R.rawKernelOmegaProjection N z)).toAdd
  apply Multiplicative.ofAdd.injective
  apply E.equiv.injective
  apply Subtype.ext
  rw [E.equiv.apply_symm_apply]
  rw [E.conjugate]
  exact congrArg Subtype.val
    (R.rawKernelOmegaProjection_conjugate N q z)

/-- The concrete omega-to-inner-section map as an intertwiner of original
quotient representations. -/
noncomputable def rawKernelOmegaInnerSectionIntertwiner
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (binaryKernelOmegaConjugationRepresentation
      (R.rawQuotientMap N)).IntertwiningMap
      ((R.innerSectionModule N).ρ.comp (R.rawQuotientMap N)) where
  toLinearMap := R.rawKernelOmegaInnerSectionMap N
  isIntertwining' := by
    intro q
    apply LinearMap.ext
    intro z
    obtain ⟨z, rfl⟩ := Additive.toMul.surjective z
    exact R.rawKernelOmegaInnerSectionMap_equivariant N q z

end DegreeTwoPairTopTowerRealization
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
