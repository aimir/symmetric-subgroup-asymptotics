import SymmetricSubgroupAsymptotics.PrimitiveSocleWeakClassSquareProperGap
import SymmetricSubgroupAsymptotics.AlternatingNaturalClassExtraGap
import SymmetricSubgroupAsymptotics.CFSGAlternatingOuterBound

/-! The full alternating-socle family outside degree six pays the
proper-subnormal extra exponent in EVERY original representation and at
EVERY factor count. The actual outer factor two is retained literally. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.proper_subnormal_class_cube_le_of_alternating_component
    (D : NonaffineData G X) (m : ℕ) (hm : 5 ≤ m) (hmsix : m ≠ 6)
    (e : D.Simple ≃* alternatingGroup (Fin m))
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  refine D.proper_subnormal_class_cube_le_of_weak_model_square_capacity
    (alternatingGroup (Fin m)) e m hm
    (CFSGAlternatingMinimumIndex.degree_le_proper_index m hm) ?_
    (CFSGAlternatingMinimumIndex.degree_square_lt_card m hm).le H hH hne
  have ho : Nat.card (Outer (alternatingGroup (Fin m)))=2 :=
    CFSGAlternatingOuterBound.outer_card_eq_two_of_ne_six m hm hmsix
  rw [ho]
  calc
    (Nat.card (ConjClasses (alternatingGroup (Fin m)))*2)^3 =
        8*Nat.card (ConjClasses (alternatingGroup (Fin m)))^3 := by ring
    _ ≤ 8*5^(m-2) := Nat.mul_le_mul_left 8
      (AlternatingNaturalClassExtraGap.alternating_class_cube_le m hm)

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
