import SymmetricSubgroupAsymptotics.PrimitiveAffineComplementRepresentationCore
import SymmetricSubgroupAsymptotics.PrimitiveAffineDimensionOrder
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-! Actual faithful affine actions divide the elementary full affine order.
No subgroup classification or bounded primitive correspondence is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

abbrev fullLinearOrder (p d : ℕ) : ℕ := ∏ i : Fin d,(p^d-p^i.val)
abbrev fullAffineOrder (p d : ℕ) : ℕ := p^d*fullLinearOrder p d

namespace PrimitiveAffineProfile
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X]

/-- The dimension and field characteristic are recovered from the literal
translation module; the divisor uses its actual conjugation representation. -/
theorem exists_prime_dimension_order_divisor
    (P : PrimitiveAffineProfile G X) (hp : MulAction.IsPreprimitive G X) :
    ∃ p d : ℕ,p.Prime ∧ 0<d ∧ Nat.card X=p^d ∧
      Nat.card G∣fullAffineOrder p d ∧ fullAffineOrder p d≠0 := by
  let C := P.elementaryChart hp
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v)) C.equiv.symm.injective
  let x : X := Classical.choice inferInstance
  have hdegree : Nat.card X=P.p^C.d := P.degree_eq_prime_pow_finrank C.equiv x
  let basis := Module.finBasis (ZMod P.p) C.V
  let rho := (P.complementRepresentationCore hp C x).ρ
  let phi : P.complement x →* Matrix.GeneralLinearGroup (Fin C.d) (ZMod P.p) :=
    (Matrix.GeneralLinearGroup.toLin' basis).symm.toMonoidHom.comp
      (Representation.asGroupHom rho)
  have hphi : Function.Injective phi := by
    intro a b hab
    apply P.complementRepresentationCore_injective hp C x
    have he : Representation.asGroupHom rho a=Representation.asGroupHom rho b :=
      (Matrix.GeneralLinearGroup.toLin' basis).symm.injective hab
    exact congrArg Units.val he
  have hgl : Nat.card (Matrix.GeneralLinearGroup (Fin C.d) (ZMod P.p))=
      fullLinearOrder P.p C.d := by
    rw [Matrix.card_GL_field]
    simp only [ZMod.card]
  have hcomp : Nat.card (P.complement x)∣fullLinearOrder P.p C.d :=
    hgl ▸ Subgroup.card_dvd_of_injective phi hphi
  have hfactor : Nat.card G=Nat.card X*Nat.card (P.complement x) := by
    simpa only [P.card_eq x] using (P.isComplement'_complement x).card_mul.symm
  have hdiv : Nat.card G∣fullAffineOrder P.p C.d := by
    rw [hfactor,hdegree]
    exact Nat.mul_dvd_mul_left _ hcomp
  have hne : fullAffineOrder P.p C.d≠0 := by
    unfold fullAffineOrder
    rw [←hgl]
    exact mul_ne_zero (pow_ne_zero _ P.p_prime.ne_zero) Nat.card_pos.ne'
  exact ⟨P.p,C.d,P.p_prime,C.d_pos,hdegree,hdiv,hne⟩

end PrimitiveAffineProfile
end SymmetricSubgroupAsymptotics
