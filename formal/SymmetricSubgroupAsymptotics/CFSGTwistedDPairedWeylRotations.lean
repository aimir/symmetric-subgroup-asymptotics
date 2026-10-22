import SymmetricSubgroupAsymptotics.CFSGTwistedDPairedWeyl
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationForkAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDMatrixWeylParity

/-! The actual relative terminal Weyl word is a product of four sparse
coordinate rotations. This uses the checked chain and fork identities,
rather than a finite-entry expansion of the six-root product. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDPairedWeylRotations
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGOrthogonalDBinaryElements CFSGTwistedDPairedWeyl CFSGMatrixPairRotation

theorem penWeyl_val (K : Type) [Field K] (s : ℕ) :
    ((simpleWeyl K (s + 4) (pen (s + 2))).val : Mat K (s + 4)) =
      chainWeylMatrix K (s + 3) (Fin.last (s + 2)) := by
  change (1 + (-1 : K) • rootMatrix K (s + 4) false (pen (s + 2))) *
      (1 + (1 : K) • rootMatrix K (s + 4) true (pen (s + 2))) *
      (1 + (-1 : K) • rootMatrix K (s + 4) false (pen (s + 2))) = _
  simp only [rootMatrix, Bool.false_eq_true, if_false, if_true,
    neg_one_smul, one_smul, ← sub_eq_add_neg, chainWeylMatrix]
  rfl

theorem pairedWeyl_rotations (s : ℕ) (q : CFSG.PrimePower) :
    ((pairedWeyl s q).val : Mat (q.Extension 2) (s + 4)) =
      (rotation (q.Extension 2) (Sum.inl (pen (s + 2))) (Sum.inl (last (s + 2))) *
        rotation (q.Extension 2) (Sum.inr (pen (s + 2))) (Sum.inr (last (s + 2)))) *
      (rotation (q.Extension 2) (Sum.inl (pen (s + 2))) (Sum.inr (last (s + 2))) *
        rotation (q.Extension 2) (Sum.inr (pen (s + 2))) (Sum.inl (last (s + 2)))) := by
  rw [pairedWeyl_eq_nodes]
  change ((simpleWeyl (q.Extension 2) (s + 4) (pen (s + 2))).val : Mat (q.Extension 2) (s + 4)) *
    ((simpleWeyl (q.Extension 2) (s + 4) (last (s + 2))).val : Mat (q.Extension 2) (s + 4)) = _
  rw [penWeyl_val, chainWeylMatrix_rotation,
    CFSGOrthogonalDGenerationForkAction.fork_rotations]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedDPairedWeylRotations
