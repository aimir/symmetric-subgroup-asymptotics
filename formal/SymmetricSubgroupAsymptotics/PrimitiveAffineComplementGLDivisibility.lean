import SymmetricSubgroupAsymptotics.PrimitiveAffineComplementRepresentationCore
import SymmetricSubgroupAsymptotics.FaithfulFiniteLinearRepresentationOrder

/-! The ACTUAL point stabilizer of a primitive affine profile has order
dividing GL_d(F_p), through its proved faithful conjugation representation
on the literal translation chart. No complement recognition is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineProfile

variable {G X : Type} [Group G] [Finite G] [Finite X] [Nontrivial X]
    [MulAction G X] [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)

theorem complement_card_dvd_matrix_GL
    (hprimitive : MulAction.IsPreprimitive G X) (C : P.ElementaryChart hprimitive) (x : X) :
    Nat.card (P.complement x) ∣ Nat.card (Matrix.GeneralLinearGroup (Fin C.d) (ZMod P.p)) := by
  letI : Fact P.p.Prime := C.primeFact
  have h := FaithfulFiniteLinearRepresentationOrder.card_dvd_matrix_GL
    (P.complementRepresentationCore hprimitive C x).ρ
    (P.complementRepresentationCore_injective hprimitive C x)
  simpa only [ElementaryChart.d] using h

theorem complement_card_dvd_GL_order
    (hprimitive : MulAction.IsPreprimitive G X) (C : P.ElementaryChart hprimitive) (x : X) :
    Nat.card (P.complement x) ∣ ∏ i : Fin C.d, (P.p ^ C.d - P.p ^ (i : ℕ)) := by
  letI : Fact P.p.Prime := C.primeFact
  have h := FaithfulFiniteLinearRepresentationOrder.card_dvd_GL_order
    (P.complementRepresentationCore hprimitive C x).ρ
    (P.complementRepresentationCore_injective hprimitive C x)
  simpa only [ElementaryChart.d, Nat.card_zmod] using h

end SymmetricSubgroupAsymptotics.PrimitiveAffineProfile
