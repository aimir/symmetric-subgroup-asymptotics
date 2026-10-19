import SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalGeometry
import SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulTopUniform

/-! Uniform two in the honest zero-odd, original no-pair quartet branch.
The original geometric hypothesis first forces actual top faithfulness;
its actual normalized operators then prove the bound. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalUniform
open BinaryPlanePermutationAffineEquiv
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneWreathActualOddKernel
open BinaryPlaneLineFramePairing (Affine Point)

theorem uniform (U : Subgroup (Equiv.Perm (Fin 16)))
    (C : Subgroup Frame) (rho : U →* Affine) (pi : U →* C)
    (hlinear : ∀ u : U, (rho u).right=(pi u : Frame))
    (chart : Point ≃ Fin 16)
    (hpoint : ∀ (u : U) p, chart (BinaryPlanePermutationWreathCoordinates.pointAction
      (rho u) p)=(u : Equiv.Perm (Fin 16)) (chart p))
    (hzero : oddKernel C=⊥)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    (hNoPair : ¬ Nonempty (BinaryPairFrame U (Fin 8))) :
    UniformSubrepresentationGeneratorBound
      (BinaryPlaneCyclicWreathUniform.representation C) 2 :=
  BinaryPlaneFaithfulTopUniform.uniform C
    (BinaryPlaneZeroOddOriginalGeometry.top_injective U C rho pi hlinear
      chart hpoint hzero heven hNoPair) heven

end SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalUniform
