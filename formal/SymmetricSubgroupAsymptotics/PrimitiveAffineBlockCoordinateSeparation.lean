import SymmetricSubgroupAsymptotics.OriginalBlockCharacterSeparation
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveBlockTransfer

/-!
# A literal affine coordinate separates the translation intersection

The coordinate selected by the actual wreath embedding differs from the
original action on the base block only by the chosen transporter of that
block.  Hence its kernel is contained in the kernel of the original block
evaluation.  Retaining all ambient conjugates then separates the whole
translation intersection.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The actual translation intersection lies in the kernel of the literal
action on blocks. -/
theorem translationIntersection_le_blockKernel :
    E block P ≤ block.topMap.ker := by
  intro a ha
  apply MonoidHom.mem_ker.mpr
  have hcompressed :
      PermutationalWreathProduct.mapBase (localMap block P)
          (ambientEmbedding block a) = 1 :=
    MonoidHom.mem_ker.mp ha
  have hright := congrArg PermutationalWreathProduct.right hcompressed
  simpa only [PermutationalWreathProduct.mapBase_right,
    PermutationalWreathProduct.one_right] using congrArg Subtype.val hright

/-- Vanishing of the selected affine translation coordinate forces
vanishing of the original evaluation on the selected block. -/
theorem translationCoordinate_ker_le_originalBlockEvaluation_ker :
    (coordinate block P block.base).ker ≤
      (originalBlockEvaluation block.map block.map_equivariant block.base
        (E block P) (translationIntersection_le_blockKernel block P)).ker := by
  intro a ha
  apply MonoidHom.mem_ker.mpr
  apply Subtype.ext
  apply Equiv.ext
  intro omega
  apply Subtype.ext
  let r : preE7NonPairAction w U :=
    ActualBlockWreathEmbedding.representative
      (A := preE7NonPairAction w U) block.base block.base
  have hr : r • block.base = block.base :=
    ActualBlockWreathEmbedding.representative_smul
      (A := preE7NonPairAction w U) block.base block.base
  let v : originalBlockFibre block.map block.base :=
    ⟨r⁻¹ • omega.1, by
      rw [block.map_equivariant, omega.2]
      calc
        r⁻¹ • block.base = r⁻¹ • (r • block.base) :=
          congrArg (r⁻¹ • ·) hr.symm
        _ = block.base := inv_smul_smul r block.base⟩
  have hcoordinate :
      PermutationalWreathProduct.Compression.kernelCoordinate
          (ambientEmbedding block) (localMap block P) block.base a = 1 := by
    apply (localKernelEquiv block P).symm.injective
    simpa only [coordinate, MonoidHom.comp_apply, map_one] using
      MonoidHom.mem_ker.mp ha
  have hlocal :
      ActualBlockWreathEmbedding.localCoordinate block.map
          block.map_equivariant block.base a.1 block.base = 1 := by
    exact congrArg Subtype.val hcoordinate
  have hv := congrArg
    (fun z : block.Component =>
      (((z : Equiv.Perm block.Fibre) v : block.Fibre) : Fin w)) hlocal
  change
    ((ActualBlockWreathEmbedding.localStabilizer block.base a.1 block.base :
        preE7NonPairAction w U) • v.1) = v.1 at hv
  have hfix : (a.1 : preE7NonPairAction w U) • omega.1 = omega.1 := by
    have hh := congrArg (fun z : Fin w => r • z) hv
    dsimp only [ActualBlockWreathEmbedding.localStabilizer, v, r] at hh
    have htop : block.topMap a.1 = 1 := MonoidHom.mem_ker.mp
      ((translationIntersection_le_blockKernel block P) a.2)
    have htopInv : block.topMap a.1⁻¹ = 1 := by
      rw [map_inv, htop, inv_one]
    have haInvFix : a.1⁻¹ • block.base = block.base := by
      exact congrArg (fun z : Equiv.Perm block.Points => z block.base) htopInv
    rw [haInvFix] at hh
    simpa only [mul_smul, smul_inv_smul, inv_smul_smul] using hh
  exact hfix

/-- One literal affine translation coordinate separates the whole
translation intersection after retaining its ambient conjugates. -/
theorem translationCoordinate_conjugates_separate
    (a : E block P)
    (ha : ∀ g : preE7NonPairAction w U,
      coordinate block P block.base (MulAut.conjNormal g a) = 1) :
    a = 1 := by
  exact originalBlockKernelLabel_conjugates_separate
    block.map block.map_equivariant block.base
    (E block P) (translationIntersection_le_blockKernel block P)
    (coordinate block P block.base)
    (translationCoordinate_ker_le_originalBlockEvaluation_ker block P)
    a ha

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
