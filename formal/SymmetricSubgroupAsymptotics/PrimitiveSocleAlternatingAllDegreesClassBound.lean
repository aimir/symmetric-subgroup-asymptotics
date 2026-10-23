import SymmetricSubgroupAsymptotics.PrimitiveSocleAlternatingSixClassBound

/-! Every alternating simple component, every raw factor count, and
every original ambient degree satisfy the GM cube bound for actual
SUBNORMAL subgroups. The degree-six exceptional automorphisms are handled
by the original action, not removed by an automorphism-identification
assumption. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]

theorem NonaffineData.subnormal_class_cube_le_of_alternating_all_degrees
    (D : NonaffineData G X) (m : ℕ) (hm : 5 ≤ m)
    (e : D.Simple ≃* alternatingGroup (Fin m)) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 1) := by
  by_cases he : m = 6
  · subst m
    exact D.subnormal_class_cube_le_of_alternating_six_all_degrees e H hH
  · exact D.subnormal_class_cube_le_of_alternating_ne_six_all_degrees m hm he e H hH

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
