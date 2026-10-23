import SymmetricSubgroupAsymptotics.CFSGExceptionalOddFieldPowers
import SymmetricSubgroupAsymptotics.External.CFSG.Models.LieFamilies

/-! Exact arithmetic of the two powers in the ORIGINAL ReeG2 twist.
The first pinned G2 node uses alpha=t^(3^(m+1)), the other beta=t^(3^m).
These inverse field maps are not an asserted exceptional group action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoFieldParameters
open CFSGExceptionalOddFieldPowers

abbrev Field (m : ℕ) := GaloisField 3 (2*m+1)

def alpha (m : ℕ) : Field m →+* Field m := upperPower (Field m) 3 m

def beta (m : ℕ) : Field m →+* Field m := lowerPower (Field m) 3 m

@[simp] theorem alpha_apply (m : ℕ) (x : Field m) : alpha m x=x^(3^(m+1)) := rfl

@[simp] theorem beta_apply (m : ℕ) (x : Field m) : beta m x=x^(3^m) := rfl

theorem field_card (m : ℕ) : Nat.card (Field m)=3^(2*m+1) :=
  GaloisField.card 3 (2*m+1) (by omega)

theorem field_cycle (m : ℕ) (x : Field m) : x^(3^(2*m+1))=x :=
  frobenius_cycle (Field m) 3 m (field_card m) x

theorem alpha_beta (m : ℕ) (x : Field m) : alpha m (beta m x)=x :=
  upper_lower (Field m) 3 m (field_card m) x

theorem beta_alpha (m : ℕ) (x : Field m) : beta m (alpha m x)=x :=
  lower_upper (Field m) 3 m (field_card m) x

theorem alpha_twice (m : ℕ) (x : Field m) : alpha m (alpha m x)=x^3 :=
  upper_twice (Field m) 3 m (field_card m) x

theorem alpha_eq_beta_cube (m : ℕ) (x : Field m) : alpha m x=(beta m x)^3 :=
  upperPower_eq_lower_pow (Field m) 3 m x

def alphaEquiv (m : ℕ) : Field m ≃+* Field m := upperEquiv (Field m) 3 m (field_card m)

@[simp] theorem alphaEquiv_apply (m : ℕ) (x : Field m) : alphaEquiv m x=alpha m x := rfl

@[simp] theorem alphaEquiv_symm_apply (m : ℕ) (x : Field m) :
    (alphaEquiv m).symm x=beta m x := rfl

/-- This is the exact exponent function used in Models.ReeG2. -/
def originalExponent (m : ℕ) (i : Fin 2) : ℕ :=
  if i.val=0 then 3^(m+1) else 3^m

theorem original_parameter_power (m : ℕ) (i : Fin 2) (x : Field m) :
    x^(originalExponent m i)=if i.val=0 then alpha m x else beta m x := by
  by_cases hi : i.val=0 <;> simp only [originalExponent,hi,if_true,if_false,alpha_apply,beta_apply]

theorem original_parameter_power_twice (m : ℕ) (i : Fin 2) (x : Field m) :
    (x^(originalExponent m i))^(originalExponent m (CFSG.Models.reverseNode i))=x := by
  fin_cases i
  · change beta m (alpha m x)=x
    exact beta_alpha m x
  · change alpha m (beta m x)=x
    exact alpha_beta m x

end SymmetricSubgroupAsymptotics.CFSGReeGTwoFieldParameters
