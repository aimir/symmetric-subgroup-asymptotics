import SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddDichotomy
import SymmetricSubgroupAsymptotics.BinaryPlaneLineFramePairing
import SymmetricSubgroupAsymptotics.EquivariantPairingBinaryFrame

/-! The invariant-line branch gives an actual pair frame on the original
sixteen points. An explicit geometric no-pair hypothesis therefore forces
faithfulness of the quartet top in the zero-odd branch. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalGeometry
open BinaryPlanePermutationAffineEquiv
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneAlternatingCentralizerCommutators (top)
open BinaryPlaneWreathActualOddKernel
open BinaryPlaneLineFramePairing (Affine Point)

/-- No change of the original subgroup or point action occurs here. -/
def originalFrame (U : Subgroup (Equiv.Perm (Fin 16)))
    (rho : U →* Affine) (chart : Point ≃ Fin 16)
    (hpoint : ∀ (u : U) p, chart (BinaryPlanePermutationWreathCoordinates.pointAction
      (rho u) p)=(u : Equiv.Perm (Fin 16)) (chart p))
    (v : Fin 4 → Plane) (hv : ∀ i, v i≠0)
    (hline : ∀ (u : U) (i : Fin 4),
      (rho u).right.left ((rho u).right.right i) (v i)=v ((rho u).right.right i)) :
    BinaryPairFrame U (Fin 8) :=
  EquivariantPairingBinaryFrame.frameFin U
    (BinaryPlaneLineFramePairing.originalPairing U rho chart hpoint v hv hline)
    8 (by rw [Nat.card_fin])

/-- The no-pair premise is the actual geometric branch condition, rather
than a numerical or semantic catalogue exclusion. -/
theorem top_injective (U : Subgroup (Equiv.Perm (Fin 16)))
    (C : Subgroup Frame) (rho : U →* Affine) (pi : U →* C)
    (hlinear : ∀ u : U, (rho u).right=(pi u : Frame))
    (chart : Point ≃ Fin 16)
    (hpoint : ∀ (u : U) p, chart (BinaryPlanePermutationWreathCoordinates.pointAction
      (rho u) p)=(u : Equiv.Perm (Fin 16)) (chart p))
    (hzero : oddKernel C=⊥)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    (hNoPair : ¬ Nonempty (BinaryPairFrame U (Fin 8))) :
    Function.Injective (top C) := by
  rcases BinaryPlaneZeroOddDichotomy.dichotomy C hzero heven with hi | hl
  · exact hi
  · obtain ⟨v,hv,hline⟩ := hl
    apply False.elim
    apply hNoPair
    refine ⟨originalFrame U rho chart hpoint v hv ?_⟩
    intro u i
    rw [hlinear u]
    exact hline (pi u) i

end SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalGeometry
