import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoSylowOuterNormalization
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoFiveTransversalCover

/-! Genuine images of the second selected generator have no fixed
point in the SAME original22-point action. Base-image laws therefore
reject whole decoder subtrees before any finite incidence calculation.
No candidate capacity, element census, or outer-order bound is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoIncidenceNoFixedPoint
open CFSGMathieuTwentyTwoElevenGeneration CFSGMathieuTwentyTwoFiveTransversalCover

theorem secondElement_order : orderOf secondElement = 11 := by
  have he : secondElement = (MulAut.conj originalA) firstElement := rfl
  rw [he,(MulAut.conj originalA).orderOf_eq]
  exact CFSGMathieuTwentyTwoSylowOuterNormalization.firstElement_order

theorem map_second_no_fixed_point (f : MulAut CFSG.Models.Mathieu22) (p : Fin 22) :
    (f secondElement).val p ≠ p :=
  CFSGMathieuTwentyTwoActualOrder.no_fixed_point_of_order_eleven (f secondElement)
    ((f.orderOf_eq secondElement).trans secondElement_order) p

private theorem decode_zero (c : Code) : (decode c).val 0 = c.1.1 := by
  simp only [decode,Subgroup.coe_mul,Equiv.Perm.mul_apply,
    fifth_zero,fourth_zero,third_zero,second_zero,first_zero]

private theorem decode_one (c : Code) : (decode c).val 1 = (first c.1.1).val c.1.2.val := by
  simp only [decode,Subgroup.coe_mul,Equiv.Perm.mul_apply,
    fifth_one,fourth_one,third_one,second_one]

theorem first_prefix_ne_zero (f : MulAut CFSG.Models.Mathieu22) (c : Code)
    (hc : decode c = f secondElement) : c.1.1 ≠ 0 := by
  have h := map_second_no_fixed_point f (0 : Fin 22)
  rw [←hc,decode_zero] at h
  exact h

theorem second_prefix_no_fixed_one (f : MulAut CFSG.Models.Mathieu22) (c : Code)
    (hc : decode c = f secondElement) : (first c.1.1).val c.1.2.val ≠ 1 := by
  have h := map_second_no_fixed_point f (1 : Fin 22)
  rw [←hc,decode_one] at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoIncidenceNoFixedPoint
