import SymmetricSubgroupAsymptotics.External.CFSG.Models.Suzuki
import Mathlib.Algebra.CharP.Reduced

/-! Exact defining-field parameters of the pinned Suzuki matrices.
The twist is the actual iterated Frobenius on GF(2^(2m+1)); it is not an
independently supplied field automorphism or a presentation parameter. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiFieldParameters

abbrev Field (m : ℕ) := CFSG.Models.SuzukiConstruction.Field m

def theta (m : ℕ) : Field m →+* Field m := iterateFrobenius (Field m) 2 (m+1)

def inverseTheta (m : ℕ) : Field m →+* Field m := iterateFrobenius (Field m) 2 m

@[simp] theorem theta_apply (m : ℕ) (x : Field m) : theta m x=x^(2^(m+1)) := rfl

@[simp] theorem inverseTheta_apply (m : ℕ) (x : Field m) : inverseTheta m x=x^(2^m) := rfl

theorem field_card (m : ℕ) : Nat.card (Field m)=2^(2*m+1) :=
  GaloisField.card 2 (2*m+1) (by omega)

theorem frobenius_cycle (m : ℕ) (x : Field m) :
    iterateFrobenius (Field m) 2 (2*m+1) x=x := by
  letI : Fintype (Field m) := Fintype.ofFinite _
  change x^(2^(2*m+1))=x
  have hc : Fintype.card (Field m)=2^(2*m+1) := by
    simpa only [Nat.card_eq_fintype_card] using field_card m
  rw [←hc]
  exact FiniteField.pow_card x

theorem theta_twice (m : ℕ) (x : Field m) : theta m (theta m x)=x^2 := by
  change iterateFrobenius (Field m) 2 (m+1)
    (iterateFrobenius (Field m) 2 (m+1) x)=x^2
  rw [←iterateFrobenius_add_apply]
  rw [show (m+1)+(m+1)=(2*m+1)+1 by omega,iterateFrobenius_add_apply,
    frobenius_cycle,iterateFrobenius_one_apply]

theorem inverseTheta_theta (m : ℕ) (x : Field m) : inverseTheta m (theta m x)=x := by
  change iterateFrobenius (Field m) 2 m (iterateFrobenius (Field m) 2 (m+1) x)=x
  rw [←iterateFrobenius_add_apply,show m+(m+1)=2*m+1 by omega,frobenius_cycle]

theorem theta_inverseTheta (m : ℕ) (x : Field m) : theta m (inverseTheta m x)=x := by
  change iterateFrobenius (Field m) 2 (m+1) (iterateFrobenius (Field m) 2 m x)=x
  rw [←iterateFrobenius_add_apply,show (m+1)+m=2*m+1 by omega,frobenius_cycle]

def thetaEquiv (m : ℕ) : Field m ≃+* Field m where
  __ := theta m
  invFun := inverseTheta m
  left_inv := inverseTheta_theta m
  right_inv := theta_inverseTheta m

theorem theta_bijective (m : ℕ) : Function.Bijective (theta m) := (thetaEquiv m).bijective

/-- The fixed field of the actual twist consists exactly of its prime
field elements zero and one. -/
theorem theta_fixed_iff (m : ℕ) (x : Field m) : theta m x=x ↔ x=0 ∨ x=1 := by
  constructor
  · intro hx
    have hs : x^2=x := by rw [←theta_twice m x,hx,hx]
    have hz : x*(x-1)=0 := by rw [mul_sub,mul_one,←pow_two,hs,sub_self]
    rcases mul_eq_zero.mp hz with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  · rintro (rfl | rfl)
    · exact map_zero _
    · exact map_one _

end SymmetricSubgroupAsymptotics.CFSGSuzukiFieldParameters
