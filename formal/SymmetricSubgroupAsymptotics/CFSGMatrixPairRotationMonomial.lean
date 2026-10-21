import SymmetricSubgroupAsymptotics.CFSGMatrixPairRotation
import SymmetricSubgroupAsymptotics.CFSGTypeAMonomialMatrices

/-! A sparse coordinate rotation is a literal signed monomial matrix. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGMatrixPairRotation
variable (R : Type*) [Field R] {I : Type*} [Fintype I] [DecidableEq I]

theorem rotation_monomial (p q : I) (hpq : p ≠ q) :
    rotation R p q = CFSGTypeAMonomialMatrices.monomial (Equiv.swap p q)
      (fun x => if x = p then -1 else 1) := by
  ext x y
  simp only [rotation, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, CFSGTypeAMonomialMatrices.monomial_apply]
  by_cases hxp : x = p
  · subst x
    rw [Equiv.swap_apply_left]
    by_cases hyp : y = p
    · subst y; simp [hpq, Ne.symm hpq]
    · by_cases hyq : y = q
      · subst y; simp [hpq, Ne.symm hpq]
      · simp [hyp, hyq, Ne.symm hyp, Ne.symm hyq, hpq, Ne.symm hpq]
  · by_cases hxq : x = q
    · subst x
      rw [Equiv.swap_apply_right]
      by_cases hyp : y = p
      · subst y; simp [hpq, Ne.symm hpq]
      · by_cases hyq : y = q
        · subst y; simp [hpq, Ne.symm hpq]
        · simp [hyp, hyq, Ne.symm hyp, Ne.symm hyq, hpq, Ne.symm hpq]
    · rw [Equiv.swap_apply_of_ne_of_ne hxp hxq]
      simp [hxp, hxq, Ne.symm hxp, Ne.symm hxq]

end SymmetricSubgroupAsymptotics.CFSGMatrixPairRotation
