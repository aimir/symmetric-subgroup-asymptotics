import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.CharP.Reduced

/-! Odd-degree exceptional field powers. These are literal iterated
Frobenius maps on a field of cardinality p^(2m+1), with proved inverse
maps. No exceptional group endomorphism or generated graph is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalOddFieldPowers
variable (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (m : ℕ)

def upperPower : K →+* K := iterateFrobenius K p (m+1)

def lowerPower : K →+* K := iterateFrobenius K p m

@[simp] theorem upperPower_apply (x : K) : upperPower K p m x=x^(p^(m+1)) := rfl

@[simp] theorem lowerPower_apply (x : K) : lowerPower K p m x=x^(p^m) := rfl

theorem upperPower_eq_lower_pow (x : K) :
    upperPower K p m x=(lowerPower K p m x)^p := by
  change iterateFrobenius K p (m+1) x=(iterateFrobenius K p m x)^p
  rw [show m+1=1+m by omega,iterateFrobenius_add_apply,iterateFrobenius_one_apply]

variable [Finite K] (hcard : Nat.card K=p^(2*m+1))
include hcard

theorem frobenius_cycle (x : K) : iterateFrobenius K p (2*m+1) x=x := by
  letI : Fintype K := Fintype.ofFinite K
  change x^(p^(2*m+1))=x
  have hc : Fintype.card K=p^(2*m+1) := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  rw [←hc]
  exact FiniteField.pow_card x

theorem upper_lower (x : K) : upperPower K p m (lowerPower K p m x)=x := by
  change iterateFrobenius K p (m+1) (iterateFrobenius K p m x)=x
  rw [←iterateFrobenius_add_apply,show (m+1)+m=2*m+1 by omega]
  exact frobenius_cycle K p m hcard x

theorem lower_upper (x : K) : lowerPower K p m (upperPower K p m x)=x := by
  change iterateFrobenius K p m (iterateFrobenius K p (m+1) x)=x
  rw [←iterateFrobenius_add_apply,show m+(m+1)=2*m+1 by omega]
  exact frobenius_cycle K p m hcard x

theorem upper_twice (x : K) : upperPower K p m (upperPower K p m x)=x^p := by
  change iterateFrobenius K p (m+1) (iterateFrobenius K p (m+1) x)=x^p
  rw [←iterateFrobenius_add_apply,
    show (m+1)+(m+1)=(2*m+1)+1 by omega,iterateFrobenius_add_apply,
    frobenius_cycle K p m hcard,iterateFrobenius_one_apply]

def upperEquiv : K ≃+* K where
  __ := upperPower K p m
  invFun := lowerPower K p m
  left_inv := lower_upper K p m hcard
  right_inv := upper_lower K p m hcard

@[simp] theorem upperEquiv_apply (x : K) :
    upperEquiv K p m hcard x=upperPower K p m x := rfl

@[simp] theorem upperEquiv_symm_apply (x : K) :
    (upperEquiv K p m hcard).symm x=lowerPower K p m x := rfl

end SymmetricSubgroupAsymptotics.CFSGExceptionalOddFieldPowers
