import SymmetricSubgroupAsymptotics.AlternatingFourTernaryActualQuotientSocles
import SymmetricSubgroupAsymptotics.BinaryPlaneWreathActualOddKernelStructure
import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingKernelPartition
import SymmetricSubgroupAsymptotics.CyclicSocleQuotientTools

/-! All actual A4/S4 quartet linear images have quotient-socle bound two.
Literal local S3 affine coordinates retain the correlated ternary kernel
and the complete actual signed block image. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingLinearSocles
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneWreathNormalGenerators
open LinearSemidirectSubgroupKernelChart
abbrev Model := AlternatingFourTernaryActualSubgroupNormalGenerators.Model
abbrev action := AlternatingFourTernaryActualSubgroupNormalGenerators.action

def affineMap (C : Subgroup Frame) : C →* Model :=
  TernaryPermutationWreathEmbedding.affine.comp
    ((wreathMap (R := Equiv.Perm (Fin 4)) (I := Fin 4)).comp C.subtype)

theorem affineMap_injective (C : Subgroup Frame) : Function.Injective (affineMap C) :=
  TernaryPermutationWreathEmbedding.affine_injective.comp
    (wreathMap_injective.comp Subtype.val_injective)

theorem socle_of_surjective (C : Subgroup Frame)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    {Q : Type} [Group Q] (phi : C →* Q) (hphi : Function.Surjective phi) :
    SocleNormalGeneratorBound Q 2 := by
  let f := affineMap C
  let J : Subgroup Model := f.range
  let e : C ≃* J := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun _ _ h => affineMap_injective C (congrArg Subtype.val h),f.rangeRestrict_surjective⟩
  have hEven : alternatingGroup (Fin 4)≤AlternatingSignedImageNormalGenerators.blockImage
      (AlternatingFourTernaryActualSubgroupNormalGenerators.SignedImage J) := by
    intro p hp
    obtain ⟨c,hc⟩ := heven ⟨p,hp⟩
    refine ⟨(projection action J).rangeRestrict (e c),?_⟩
    exact hc
  let psi := phi.comp e.symm.toMonoidHom
  have hpsi : Function.Surjective psi := hphi.comp e.symm.surjective
  let eqQ := QuotientGroup.quotientKerEquivOfSurjective psi hpsi
  exact CyclicSocleQuotientTools.socleBound_equiv eqQ
    (AlternatingFourTernaryActualQuotientSocles.quotientSocle J hEven psi.ker)

theorem quotientSocle (C : Subgroup Frame)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    (N : Subgroup C) [N.Normal] : SocleNormalGeneratorBound (C ⧸ N) 2 :=
  socle_of_surjective C heven (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingLinearSocles
