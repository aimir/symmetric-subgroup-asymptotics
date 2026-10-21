import SymmetricSubgroupAsymptotics.BinaryPairOriginalCoordinateRepresentation
import SymmetricSubgroupAsymptotics.BinaryBitmaskCoordinates
import Mathlib.Logic.Equiv.Fin.Basic

/-! The canonical low/high eight-point labels used by the outer carry
certificates are an explicit bijection of the original framed points. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

/-- Pair index occupies the low three bits; the physical bit is high. -/
def binaryEightPairPointLabels : (Fin 8 × ZMod 2) ≃ Fin 16 :=
  (Equiv.prodCongr (Equiv.refl (Fin 8)) (ZMod.finEquiv 2).symm.toEquiv).trans
    ((Equiv.prodComm (Fin 8) (Fin 2)).trans finProdFinEquiv)

/-- A dummy trivial action supplies only the explicit canonical frame;
no action replacement is used in the subsequent original-coordinate lemma. -/
def binaryEightCanonicalPairFrame :
    BinaryPairFrame (⊥ : Subgroup (Equiv.Perm (Fin 16))) (Fin 8) where
  frame := binaryEightPairPointLabels
  top := 1
  intertwine u p := by
    have hu : (u : Equiv.Perm (Fin 16)) = 1 := Subgroup.mem_bot.mp u.property
    change (binaryEightPairPointLabels.symm
      ((u : Equiv.Perm (Fin 16)) (binaryEightPairPointLabels p))).1 = p.1
    rw [hu]
    exact congrArg Prod.fst (binaryEightPairPointLabels.symm_apply_apply p)

/-- The literal point-to-zero/sum matrix used in all four selected outer
carry packets. Its columns, rather than a coordinate-name convention,
fix the transformation. -/
def binaryEightCanonicalLayerChange :
    (Fin 16 → ZMod 2) →ₗ[ZMod 2] (Fin 16 → ZMod 2) :=
  (binaryRectangularMatrixOfColumnMasks 16 16
    (![257,514,1028,2056,4112,8224,16448,32896,
      256,512,1024,2048,4096,8192,16384,32768] : Fin 16 → ℕ)).mulVecLin

private theorem canonicalLayerChange_basis : ∀ i,
    binaryEightCanonicalLayerChange (Pi.single i 1) =
      binaryEightCanonicalPairFrame.originalCoordinateEquiv (Pi.single i 1) := by decide +kernel

theorem canonicalLayerChange_eq : binaryEightCanonicalLayerChange =
    binaryEightCanonicalPairFrame.originalCoordinateEquiv.toLinearMap := by
  apply LinearMap.pi_ext
  intro i c
  have hs : Pi.single i c = c • Pi.single i (1 : ZMod 2) := by
    ext j
    simp [Pi.single_apply,mul_ite]
  simp only [hs,map_smul,canonicalLayerChange_basis]
  rfl

namespace BinaryPairFrame
variable {X : Type} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U (Fin 8))

/-- This changes only the labels of the same original sixteen points. -/
def canonicalPointLabels : X ≃ Fin 16 := F.frame.symm.trans binaryEightPairPointLabels

/-- Original pair-layer coordinates and the selected literal matrix agree
under the explicitly displayed original-point relabelling. -/
theorem originalCoordinateEquiv_canonicalPointLabels (f : X → ZMod 2) :
    F.originalCoordinateEquiv f = binaryEightCanonicalLayerChange
      (fun j => f (F.canonicalPointLabels.symm j)) := by
  rw [canonicalLayerChange_eq]
  change pairLayerFlatten (F.pairLayerCoordinateEquiv f) =
    pairLayerFlatten (binaryEightCanonicalPairFrame.pairLayerCoordinateEquiv
      (fun j => f (F.canonicalPointLabels.symm j)))
  apply congrArg pairLayerFlatten
  apply Prod.ext
  · funext i
    change f (F.frame (i,0)) =
      f (F.frame (binaryEightPairPointLabels.symm (binaryEightPairPointLabels (i,0))))
    rw [binaryEightPairPointLabels.symm_apply_apply]
  · funext i
    change f (F.frame (i,0)) + f (F.frame (i,1)) =
      f (F.frame (binaryEightPairPointLabels.symm (binaryEightPairPointLabels (i,0)))) +
        f (F.frame (binaryEightPairPointLabels.symm (binaryEightPairPointLabels (i,1))))
    rw [binaryEightPairPointLabels.symm_apply_apply,binaryEightPairPointLabels.symm_apply_apply]

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
