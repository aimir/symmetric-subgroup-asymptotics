import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryPointIndex
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBCharTwoProjectiveEquiv
import SymmetricSubgroupAsymptotics.PrimitiveSocleSymplecticLiteralCapacity

/-! The binary rank-four point-radical index pays the literal component
cube for both original C and original B. The model equivalence, original
action, every factor count and both degree forms stay unchanged. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction CFSGSymplecticSerreMatrices
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subgroup_class_cube_le_of_symplectic_binary_point_rank_four_literal
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order=2)
    (e : D.Simple ≃* elementaryProjective q.Field 4) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  have hprime : q.prime=2 := by
    have h := Nat.le_self_pow q.exponent_pos.ne' q.prime
    have hlo := q.prime_isPrime.two_le
    change q.prime ≤ q.order at h
    omega
  letI : CharP q.Field 2 := by rw [←hprime]; infer_instance
  letI : IsSimpleGroup (elementaryProjective q.Field 4) := e.symm.isSimpleGroup
  apply D.subgroup_class_cube_le_of_symplectic_literal_budget 4 (by omega) q e
    56 (by omega) _ _ H
  · intro K hK
    have h := CFSGSymplecticBinaryPointIndex.binary_point_radical_proper_index
      q.Field (q.card_field.trans hq) 4 (by omega) K hK
    norm_num at h
    exact h
  · rw [hq]
    norm_num

theorem NonaffineData.subgroup_class_cube_le_of_typeC_binary_point_rank_four
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order=2)
    (e : D.Simple ≃* CFSG.Models.C 4 q) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.C 4 q) := e.symm.isSimpleGroup
  exact D.subgroup_class_cube_le_of_symplectic_binary_point_rank_four_literal q hq
    (e.trans (serreProjectiveEquivElementaryProjective q.Field 3)) H

theorem NonaffineData.subgroup_class_cube_le_of_typeB_binary_point_rank_four
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hprime : q.prime=2) (hq : q.order=2)
    (e : D.Simple ≃* CFSG.Models.B 4 q) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.B 4 q) := e.symm.isSimpleGroup
  letI : CharP q.Field 2 := by rw [←hprime]; infer_instance
  exact D.subgroup_class_cube_le_of_symplectic_binary_point_rank_four_literal q hq
    (e.trans (CFSGOrthogonalBSerreMatrices.serreProjectiveEquivSymplecticProjective_charTwo
      q.Field 3 (by omega))) H

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
