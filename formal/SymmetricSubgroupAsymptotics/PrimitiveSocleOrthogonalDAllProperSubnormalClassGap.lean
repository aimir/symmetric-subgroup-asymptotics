import SymmetricSubgroupAsymptotics.PrimitiveSocleOrthogonalDProperClassPackets

/-! The proved point-radical range and literal binary rank4 packets
exhaust both original split and twisted D families. All factors, the
same actual proper subnormal H and both degree forms are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.proper_subnormal_class_cube_le_of_typeD_all_fields
    (D : NonaffineData G X) (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.D r q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  by_cases hwindow : 3 ≤ q.order ∨ 5 ≤ r
  · exact D.proper_subnormal_class_cube_le_of_typeD_point_radical r hr q e hwindow H hH hne
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  have hr4 : r=4 := by omega
  subst r
  exact D.proper_subnormal_class_cube_le_of_typeD_binary_rank_four q (by omega) e H hH hne

theorem NonaffineData.proper_subnormal_class_cube_le_of_twistedD_all_fields
    (D : NonaffineData G X) (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.TwistedD r q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  by_cases hwindow : 3 ≤ q.order ∨ 5 ≤ r
  · exact D.proper_subnormal_class_cube_le_of_twistedD_point_radical r hr q e hwindow H hH hne
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  have hr4 : r=4 := by omega
  subst r
  exact D.proper_subnormal_class_cube_le_of_typeTwistedD_binary_rank_four q (by omega) e H hH hne

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
