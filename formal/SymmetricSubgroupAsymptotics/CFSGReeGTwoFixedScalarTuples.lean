import SymmetricSubgroupAsymptotics.CFSGReeGTwoFieldParameters
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckScalarTorus
import Mathlib.Tactic.Ring

/-! Scalar arithmetic for the exact ReeG2 powers. The unimodular G2
Cartan map lifts (r,r^(3 theta)) to a tuple satisfying the swapped
exceptional power equations. These are equations of units/field values,
not a claim that a torus element is fixed by a group endomorphism. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoFixedScalarTuples
open CFSGGTwoD4GeckScalarTorus CFSGReeGTwoFieldParameters
variable {G : Type*} [CommGroup G]

def desiredScalars (theta : ℕ) (r : G) : Fin 2→G := ![r,r^(3*theta)]

def fixedScalarTuple (theta : ℕ) (r : G) : Fin 2→G :=
  (scalarEquiv G).symm (desiredScalars theta r)

theorem fixedScalarTuple_zero (theta : ℕ) (r : G) :
    fixedScalarTuple theta r 0=r^2*r^(3*theta) := by
  change (scalarEquiv G).symm (desiredScalars theta r) 0=_
  rw [scalarEquiv_symm_short]
  rfl

theorem fixedScalarTuple_one (theta : ℕ) (r : G) :
    fixedScalarTuple theta r 1=r^3*(r^(3*theta))^2 := by
  change (scalarEquiv G).symm (desiredScalars theta r) 1=_
  rw [scalarEquiv_symm_long]
  rfl

theorem fixedScalarTuple_scalars (theta : ℕ) (r : G) :
    scalarEquiv G (fixedScalarTuple theta r)=desiredScalars theta r :=
  (scalarEquiv G).apply_symm_apply _

theorem fixedScalarTuple_short_scalar (theta : ℕ) (r : G) :
    (fixedScalarTuple theta r 0)^2/fixedScalarTuple theta r 1=r := by
  have he := congrFun (fixedScalarTuple_scalars theta r) 0
  rw [scalarEquiv_short] at he
  exact he

theorem fixedScalarTuple_long_scalar (theta : ℕ) (r : G) :
    (fixedScalarTuple theta r 1)^2/(fixedScalarTuple theta r 0)^3=r^(3*theta) := by
  have he := congrFun (fixedScalarTuple_scalars theta r) 1
  rw [scalarEquiv_long] at he
  exact he

theorem fixedScalarTuple_power_relations (theta : ℕ) (r : G)
    (hcycle : r^(3*theta^2)=r) :
    fixedScalarTuple theta r 0=(fixedScalarTuple theta r 1)^theta ∧
      fixedScalarTuple theta r 1=(fixedScalarTuple theta r 0)^(3*theta) := by
  simp only [fixedScalarTuple_zero,fixedScalarTuple_one]
  constructor
  · symm
    calc
      (r^3*(r^(3*theta))^2)^theta=
          r^(3*theta)*(r^(3*theta^2))^2 := by
        simp only [mul_pow,←pow_mul]
        congr 1
        congr 1
        ring
      _=r^(3*theta)*r^2 := by rw [hcycle]
      _=r^2*r^(3*theta) := mul_comm _ _
  · symm
    calc
      (r^2*r^(3*theta))^(3*theta)=
          (r^(3*theta))^2*(r^(3*theta^2))^3 := by
        simp only [mul_pow,←pow_mul]
        congr 1 <;> congr 1 <;> ring
      _=(r^(3*theta))^2*r^3 := by rw [hcycle]
      _=r^3*(r^(3*theta))^2 := mul_comm _ _

theorem exceptional_card_exponent (m : ℕ) : 3*(3^m)^2=3^(2*m+1) := by
  calc
    3*(3^m)^2=(3^m)^2*3 := Nat.mul_comm _ _
    _=3^(m*2)*3 := by rw [pow_mul]
    _=3^(m*2+1) := by rw [pow_add,pow_one]
    _=3^(2*m+1) := by congr 1; omega

theorem original_unit_cycle (m : ℕ) (r : (Field m)ˣ) : r^(3*(3^m)^2)=r := by
  apply Units.ext
  change (r : Field m)^(3*(3^m)^2)=(r : Field m)
  rw [exceptional_card_exponent]
  exact field_cycle m r

def originalFixedScalarTuple (m : ℕ) (r : (Field m)ˣ) : Fin 2→(Field m)ˣ :=
  fixedScalarTuple (3^m) r

theorem originalFixedScalarTuple_short_scalar (m : ℕ) (r : (Field m)ˣ) :
    (originalFixedScalarTuple m r 0)^2/originalFixedScalarTuple m r 1=r :=
  fixedScalarTuple_short_scalar (3^m) r

theorem originalFixedScalarTuple_long_scalar (m : ℕ) (r : (Field m)ˣ) :
    (((originalFixedScalarTuple m r 1)^2/(originalFixedScalarTuple m r 0)^3 : (Field m)ˣ) : Field m)=
      alpha m (r : Field m) := by
  have he := congrArg (fun u : (Field m)ˣ=>(u : Field m))
    (fixedScalarTuple_long_scalar (3^m) r)
  simpa only [originalFixedScalarTuple,Units.val_pow_eq_pow_val,alpha_apply,pow_succ'] using he

theorem originalFixedScalarTuple_beta (m : ℕ) (r : (Field m)ˣ) :
    (originalFixedScalarTuple m r 0 : Field m)=
      beta m (originalFixedScalarTuple m r 1 : Field m) := by
  have he := congrArg (fun u : (Field m)ˣ=>(u : Field m))
    (fixedScalarTuple_power_relations (3^m) r (original_unit_cycle m r)).1
  simpa only [originalFixedScalarTuple,Units.val_pow_eq_pow_val,beta_apply] using he

theorem originalFixedScalarTuple_alpha (m : ℕ) (r : (Field m)ˣ) :
    (originalFixedScalarTuple m r 1 : Field m)=
      alpha m (originalFixedScalarTuple m r 0 : Field m) := by
  have he := congrArg (fun u : (Field m)ˣ=>(u : Field m))
    (fixedScalarTuple_power_relations (3^m) r (original_unit_cycle m r)).2
  simpa only [originalFixedScalarTuple,Units.val_pow_eq_pow_val,alpha_apply,pow_succ'] using he

/-- The tuple satisfies the EXACT swapped powers of the original
ReeG2 graph on parameters. Group covariance is a separate obligation. -/
theorem originalFixedScalarTuple_power_fixed (m : ℕ) (r : (Field m)ˣ) (i : Fin 2) :
    (originalFixedScalarTuple m r (CFSG.Models.reverseNode i) : Field m)=
      (originalFixedScalarTuple m r i : Field m)^(originalExponent m i) := by
  fin_cases i
  · exact originalFixedScalarTuple_alpha m r
  · exact originalFixedScalarTuple_beta m r

end SymmetricSubgroupAsymptotics.CFSGReeGTwoFixedScalarTuples
