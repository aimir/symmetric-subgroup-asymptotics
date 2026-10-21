import SymmetricSubgroupAsymptotics.BinaryPairCanonicalPointCoordinates
import SymmetricSubgroupAsymptotics.BinaryPairSplitAffineRows

/-! Canonical labels transport the literal affine rows of the same
original frame to the literal low/high point formulas of the carry
packets. This statement asserts no split model or group classification. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U (Fin 8))

theorem canonicalPointLabels_frame (i : Fin 8) (b : ZMod 2) :
    F.canonicalPointLabels (F.frame (i, b)) = binaryEightCanonicalPairFrame.frame (i, b) := by
  change binaryEightPairPointLabels (F.frame.symm (F.frame (i, b))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem canonicalPointLabels_symm_frame (i : Fin 8) (b : ZMod 2) :
    F.canonicalPointLabels.symm (binaryEightCanonicalPairFrame.frame (i, b)) = F.frame (i, b) := by
  apply F.canonicalPointLabels.injective
  rw [Equiv.apply_symm_apply, F.canonicalPointLabels_frame]

theorem canonical_affinePermutation (t : Equiv.Perm (Fin 8)) (a : Fin 8 → ZMod 2) :
    F.canonicalPointLabels.permCongrHom (F.affinePermutation t a) =
      binaryEightCanonicalPairFrame.affinePermutation t a := by
  apply Equiv.ext
  intro x
  obtain ⟨⟨i, b⟩, rfl⟩ := binaryEightCanonicalPairFrame.frame.surjective x
  change F.canonicalPointLabels (F.affinePermutation t a
    (F.canonicalPointLabels.symm (binaryEightCanonicalPairFrame.frame (i, b)))) = _
  rw [F.canonicalPointLabels_symm_frame, F.affinePermutation_apply_frame,
    binaryEightCanonicalPairFrame.affinePermutation_apply_frame, F.canonicalPointLabels_frame]

end SymmetricSubgroupAsymptotics.BinaryPairFrame
