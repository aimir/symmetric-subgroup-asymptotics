import SymmetricSubgroupAsymptotics.CFSGFiniteFieldSignedSquares
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Two nonlinear Ree weights cannot be the square values of a
normalized additive map unless the field endomorphism is the identity.
These are scalar identities, with no group reconstruction premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCharacteristicThreeWeightRigidity

theorem middle_square_rigidity {K : Type*} [Field K] [CharP K 3]
    (α : K→+*K) (H : K→+K) (h1 : H 1=1)
    (hsq : ∀x, H (x^2)=(x*α x)^2) (x : K) : α x=x := by
  have h3 : (3:K)=0 := CharP.cast_eq_zero K 3
  have hi : (x+1)^2+(1-x)^2+x^2+1=0 := by
    linear_combination (x^2+1)*h3
  have hh := congrArg H hi
  rw [map_add,map_add,map_add,map_zero,h1,hsq,hsq,hsq] at hh
  have hp : ((x+1)*(α x+1))^2+((1-x)*(1-α x))^2+(x*α x)^2+1=0 := by
    simpa only [map_add,map_sub,map_one] using hh
  have hz : (α x-x)^2=0 := by
    calc
      _ = -(((x+1)*(α x+1))^2+((1-x)*(1-α x))^2+(x*α x)^2+1) := by
        linear_combination ((x*α x)^2+x^2+(α x)^2+2*x*α x+1)*h3
      _ = 0 := by rw [hp,neg_zero]
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hz)

theorem cube_square_rigidity {K : Type*} [Field K] [Finite K] [CharP K 3]
    (hcard : Nat.card K%4=3) (α : K→+*K) (H : K→+K) (h1 : H 1=1)
    (hsq : ∀x, H (x^2)=(x^2)^2*α (x^2)) (x : K) : α x=x := by
  have h3 : (3:K)=0 := CharP.cast_eq_zero K 3
  have hf (a : K) : H a=a^2*α a := by
    rcases CFSGFiniteFieldSignedSquares.isSquare_or_neg K hcard a with ⟨b,hb⟩ | ⟨b,hb⟩
    · rw [hb,←pow_two,hsq]
    · have ha : a=-(b^2) := by
        simpa only [pow_two,neg_neg] using congrArg Neg.neg hb
      rw [ha,map_neg,hsq]
      simp only [neg_sq,map_neg,mul_neg]
  have hh := map_add H x 1
  rw [hf,hf,h1] at hh
  have hp : (1-x)*(α x-x)=0 := by
    calc
      _ = (x+1)^2*α (x+1)-x^2*α x-1 := by
        simp only [map_add,map_one]
        linear_combination -(x*α x+x)*h3
      _ = 0 := by rw [hh]; ring
  by_cases hx : x=1
  · simp only [hx,map_one]
  have hleft : 1-x≠0 := by
    intro he
    exact hx (sub_eq_zero.mp he).symm
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hleft)

end SymmetricSubgroupAsymptotics.CFSGCharacteristicThreeWeightRigidity
