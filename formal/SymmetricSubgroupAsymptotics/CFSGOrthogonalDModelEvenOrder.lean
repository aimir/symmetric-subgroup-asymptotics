import SymmetricSubgroupAsymptotics.CFSGOrthogonalDProjectiveRealization
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDElementaryEvenOrder

/-! Even cardinality for each original, untransposed type-D model,
using its checked actual elementary-projective realization. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
open CFSG.Models.Chevalley

theorem serreTypeD_even_card (K : Type) [Field K] (r : ℕ)
    [IsSimpleGroup (Projective (CartanMatrix.D (r + 4)) K)] :
    Even (Nat.card (Projective (CartanMatrix.D (r + 4)) K)) := by
  rw [Nat.card_congr (serreProjectiveEquivElementaryProjective K r).toEquiv]
  exact elementaryProjective_even_card K (r + 2)

theorem typeD_even_card (r : ℕ) (q : CFSG.PrimePower) (hr : 4 ≤ r)
    [IsSimpleGroup (CFSG.Models.D r q)] : Even (Nat.card (CFSG.Models.D r q)) := by
  have he : r - 4 + 4 = r := by omega
  letI : IsSimpleGroup (Projective (CartanMatrix.D (r - 4 + 4)) q.Field) := by
    rw [he]
    infer_instance
  have h := serreTypeD_even_card q.Field (r - 4)
  rw [he] at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
