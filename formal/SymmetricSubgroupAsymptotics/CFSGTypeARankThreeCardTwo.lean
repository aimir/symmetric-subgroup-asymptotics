import SymmetricSubgroupAsymptotics.CFSGProjectiveSpecialLinearOrder
import SymmetricSubgroupAsymptotics.CFSGTypeARankTwoCardTwo

/-! Exact order of the literal binary rank-three projective model from
its finite-field determinant/central-quotient formula. No exceptional
isomorphism or permutation representation is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeARankThreeCardTwo

theorem order_eq_20160 (q : CFSG.PrimePower) (hq : q.order=2) :
    Nat.card (CFSG.Models.A 3 q)=20160 := by
  have h := CFSGProjectiveSpecialLinearOrder.projective_card_fin q.Field 4 (by decide)
  simpa only [q.card_field,hq,Fin.prod_univ_four] using h

end SymmetricSubgroupAsymptotics.CFSGTypeARankThreeCardTwo
