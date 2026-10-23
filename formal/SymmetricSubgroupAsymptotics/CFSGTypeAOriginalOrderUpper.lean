import SymmetricSubgroupAsymptotics.External.CFSG.Models.LieFamilies
import Mathlib.SetTheory.Cardinal.Finite

/-! The ORIGINAL A model is defined as the centre quotient of its
literal determinant-one matrices. Its order is therefore at most the
full matrix-space cardinality. No classical-group order formula is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

theorem typeA_order_le_matrix_power (r : ℕ) (q : CFSG.PrimePower) :
    Nat.card (CFSG.Models.A r q) ≤ q.order^((r+1)^2) := by
  let S := Matrix.SpecialLinearGroup (Fin (r+1)) q.Field
  have hs : Nat.card S ≤ Nat.card (Matrix (Fin (r+1)) (Fin (r+1)) q.Field) :=
    Nat.card_le_card_of_injective (fun A : S => A.val) Subtype.val_injective
  have hm : Nat.card (Matrix (Fin (r+1)) (Fin (r+1)) q.Field)=q.order^((r+1)^2) := by
    change Nat.card (Fin (r+1) → Fin (r+1) → q.Field)=_
    rw [Nat.card_fun,Nat.card_fun,Nat.card_fin,q.card_field,←pow_mul,pow_two]
  exact (Nat.card_le_card_of_surjective (QuotientGroup.mk' (Subgroup.center S))
    (QuotientGroup.mk'_surjective _)).trans (hs.trans_eq hm)

end SymmetricSubgroupAsymptotics.CFSGReduction
