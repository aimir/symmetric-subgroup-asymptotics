import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalCharacteristicThreeString

/-! A selected actual original root-action certificate. The short-root
operator on the long string is computed on the SAME integral tensor
space, with integral binomial coefficients before any reduction. In
particular its endpoint coefficient is literally t^3. No matrix-image
reflection or exceptional-automorphism assertion occurs here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalSimpleStringAction
open CFSG.Models.Chevalley CFSGGTwoOriginalPositiveSerreStrings
open CFSGGTwoOriginalCharacteristicThreeString
local notation "A" => CartanMatrix.G₂
variable (K : Type) [Field K]

private theorem one_tmul_nsmul (n : ℕ) (v : integralLattice A) :
    (1:K) ⊗ₜ[ℤ] (n • v)=(n:K) • ((1:K) ⊗ₜ[ℤ] v) := by
  induction n with
  | zero => simp only [zero_smul,TensorProduct.tmul_zero,Nat.cast_zero]
  | succ n ih =>
    rw [succ_nsmul,TensorProduct.tmul_add,ih,Nat.cast_succ,add_smul,one_smul]

theorem rootOperator_string (neg : Bool) (t : K) (l : ℕ) :
    rootOperator A K neg 0 t (stringElement K neg l)=
      ∑ k ∈ Finset.range 4,(((k+l).choose l:K)*t^k) • stringElement K neg (k+l) := by
  simp only [rootOperator,LinearMap.sum_apply,LinearMap.smul_apply,stringElement,
    LinearMap.baseChange_tmul,integral_string_operator]
  apply Finset.sum_congr rfl
  intro k _
  rw [one_tmul_nsmul,smul_smul,mul_comm]

theorem rootOperator_long_string (neg : Bool) (t : K) :
    rootOperator A K neg 0 t (stringElement K neg 0)=
      stringElement K neg 0+t • stringElement K neg 1+
        t^2 • stringElement K neg 2+t^3 • stringElement K neg 3 := by
  simpa only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.add_zero,Nat.choose_zero_right,
    Nat.cast_one,one_mul,pow_zero,pow_one,one_smul,zero_add] using
      rootOperator_string K neg t 0

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalSimpleStringAction
