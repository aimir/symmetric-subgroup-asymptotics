import SymmetricSubgroupAsymptotics.CFSGExceptionalOddFieldPowers
import SymmetricSubgroupAsymptotics.External.CFSG.Models.LieFamilies

/-! The literal two field powers prescribed by ORIGINAL ReeF4, including
m=0 for Tits. These arithmetic maps use the common odd-degree Frobenius
certificate; no fixed-group or quotient lifting claim is made here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFieldParameters
open CFSGExceptionalOddFieldPowers

abbrev Field (m:ℕ):=GaloisField 2 (2*m+1)
def alpha (m:ℕ):Field m→+*Field m:=upperPower (Field m) 2 m
def beta (m:ℕ):Field m→+*Field m:=lowerPower (Field m) 2 m
@[simp] theorem alpha_apply (m:ℕ) (x:Field m):alpha m x=x^(2^(m+1)):=rfl
@[simp] theorem beta_apply (m:ℕ) (x:Field m):beta m x=x^(2^m):=rfl
theorem field_card (m:ℕ):Nat.card (Field m)=2^(2*m+1):=
  GaloisField.card 2 (2*m+1) (by omega)
theorem field_cycle (m:ℕ) (x:Field m):x^(2^(2*m+1))=x:=
  frobenius_cycle (Field m) 2 m (field_card m) x
theorem alpha_beta (m:ℕ) (x:Field m):alpha m (beta m x)=x:=
  upper_lower (Field m) 2 m (field_card m) x
theorem beta_alpha (m:ℕ) (x:Field m):beta m (alpha m x)=x:=
  lower_upper (Field m) 2 m (field_card m) x
theorem alpha_twice (m:ℕ) (x:Field m):alpha m (alpha m x)=x^2:=
  upper_twice (Field m) 2 m (field_card m) x
theorem alpha_eq_beta_square (m:ℕ) (x:Field m):alpha m x=(beta m x)^2:=
  upperPower_eq_lower_pow (Field m) 2 m x
def alphaEquiv (m:ℕ):Field m≃+*Field m:=upperEquiv (Field m) 2 m (field_card m)
@[simp] theorem alphaEquiv_apply (m:ℕ) (x:Field m):alphaEquiv m x=alpha m x:=rfl
@[simp] theorem alphaEquiv_symm_apply (m:ℕ) (x:Field m):(alphaEquiv m).symm x=beta m x:=rfl

/-- Exactly the exponent function in Models.ReeF4. -/
def originalExponent (m:ℕ) (i:Fin 4):ℕ:=if i.val<2 then 2^(m+1) else 2^m

theorem original_parameter_power (m:ℕ) (i:Fin 4) (x:Field m):
    x^(originalExponent m i)=if i.val<2 then alpha m x else beta m x:=by
  by_cases hi:i.val<2 <;> simp only [originalExponent,hi,if_true,if_false,alpha_apply,beta_apply]

theorem original_parameter_power_twice (m:ℕ) (i:Fin 4) (x:Field m):
    (x^(originalExponent m i))^(originalExponent m (CFSG.Models.reverseNode i))=x:=by
  fin_cases i
  · change beta m (alpha m x)=x
    exact beta_alpha m x
  · change beta m (alpha m x)=x
    exact beta_alpha m x
  · change alpha m (beta m x)=x
    exact alpha_beta m x
  · change alpha m (beta m x)=x
    exact alpha_beta m x

end SymmetricSubgroupAsymptotics.CFSGReeFFourFieldParameters
