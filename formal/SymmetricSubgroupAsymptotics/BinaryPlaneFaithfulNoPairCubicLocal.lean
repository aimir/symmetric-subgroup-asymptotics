import SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulUntwistedLineFrame
import SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalGeometry

/-! The original no-pair geometry excludes the untwisted local factor of
an actual top-three lift. This is stronger than abstract top faithfulness. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulNoPairCubicLocal
open BinaryPlanePermutationAffineEquiv
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneAlternatingCentralizerCommutators (top)
open BinaryPlaneLineFramePairing (Affine Point)
open AlternatingFourBinaryActualPolynomialUniform (cycle)

theorem nontrivial (U : Subgroup (Equiv.Perm (Fin 16)))
    (C : Subgroup Frame) (rho : U →* Affine) (pi : U →* C)
    (hlinear : ∀ u : U, (rho u).right=(pi u : Frame))
    (chart : Point ≃ Fin 16)
    (hpoint : ∀ (u : U) p, chart (BinaryPlanePermutationWreathCoordinates.pointAction
      (rho u) p)=(u : Equiv.Perm (Fin 16)) (chart p))
    (hinj : Function.Injective (top C))
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    (hNoPair : ¬ Nonempty (BinaryPairFrame U (Fin 8)))
    (g : C) (hg : (g : Frame).right=cycle) : (g : Frame).left 0≠1 := by
  intro hlocal
  obtain ⟨v,hv,hline⟩ :=
    BinaryPlaneFaithfulUntwistedLineFrame.exists_frame C hinj heven g hg hlocal
  apply hNoPair
  refine ⟨BinaryPlaneZeroOddOriginalGeometry.originalFrame U rho chart hpoint v hv ?_⟩
  intro u i
  rw [hlinear u]
  exact hline (pi u) i

end SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulNoPairCubicLocal
