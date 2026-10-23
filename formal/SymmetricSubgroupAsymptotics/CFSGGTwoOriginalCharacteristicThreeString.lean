import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalPositiveSerreStrings
import SymmetricSubgroupAsymptotics.CFSGSerreDividedPowers
import SymmetricSubgroupAsymptotics.CFSGSerreModelRootGeneration
import Lean.Elab.Tactic.Omega

/-! The coefficient-three degeneration occurs on the SAME original
base-changed Serre lattice. Every short simple root unit fixes the
second divided-power string vector in characteristic three. This is an
actual original operator identity, with no matrix-image reflection. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalCharacteristicThreeString
open CFSGGTwoOriginalPositiveSerreStrings CFSG.Models.Chevalley
open CFSGSerreDividedPowers CFSGSerreDiagram CFSGSerreModelRootGeneration
local notation "A" => CartanMatrix.G₂
local notation "L" => RationalLie A

theorem stringVector_eq_zero_of_four_le (neg : Bool) (k : ℕ) (hk : 4≤k) :
    stringVector neg k=0 := by
  have hfour : (LieAlgebra.ad ℚ L (shortVector neg)^4) (longVector neg)=0 := by
    simpa only [pow_succ',Module.End.mul_apply,LieAlgebra.ad_apply,pow_zero,Module.End.one_apply]
      using short_serre_four neg
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hk
  have he : k=d+4 := by omega
  change ((k.factorial:ℚ)⁻¹) • (LieAlgebra.ad ℚ L (shortVector neg)^k) (longVector neg)=0
  rw [he,pow_add,Module.End.mul_apply,hfour,map_zero,smul_zero]

theorem integralString_eq_zero_of_four_le (neg : Bool) (k : ℕ) (hk : 4≤k) :
    integralString neg k=0 := by
  apply Subtype.ext
  exact stringVector_eq_zero_of_four_le neg k hk

private def longIntegral (neg : Bool) : integralLattice A :=
  latticeGenerator A (if neg then .F 1 else .E 1)

theorem integral_string_operator (neg : Bool) (k l : ℕ) :
    integralOperator A neg 0 k (integralString neg l)=
      (k+l).choose l • integralString neg (k+l) := by
  have he := congrArg (fun F : Module.End ℤ (integralLattice A)=>F (longIntegral neg))
    (integralOperator_mul A neg 0 k l)
  exact he

theorem integral_short_second_higher_zero (neg : Bool) (k : ℕ) (hk : 2≤k) :
    integralOperator A neg 0 k (integralString neg 2)=0 := by
  rw [integral_string_operator,integralString_eq_zero_of_four_le neg (k+2) (by omega),smul_zero]

variable (K : Type) [Field K] [CharP K 3]

def stringElement (neg : Bool) (k : ℕ) : Space A K :=
  (1:K) ⊗ₜ[ℤ] integralString neg k

theorem short_first_operator_second_zero (neg : Bool) :
    (integralOperator A neg 0 1).baseChange K (stringElement K neg 2)=0 := by
  rw [stringElement,LinearMap.baseChange_tmul,integral_short_string_two]
  change (TensorProduct.mk ℤ K (integralLattice A) (1:K)) (3 • integralString neg 3)=0
  rw [map_nsmul,←Nat.cast_smul_eq_nsmul K,CharP.cast_eq_zero K 3,zero_smul]

theorem short_higher_operator_second_zero (neg : Bool) (k : ℕ) (hk : 2≤k) :
    (integralOperator A neg 0 k).baseChange K (stringElement K neg 2)=0 := by
  rw [stringElement,LinearMap.baseChange_tmul,integral_short_second_higher_zero neg k hk,
    TensorProduct.tmul_zero]

theorem rootOperator_fixes_second_string (neg : Bool) (t : K) :
    rootOperator A K neg 0 t (stringElement K neg 2)=stringElement K neg 2 := by
  simp only [rootOperator,Finset.sum_range_succ,Finset.sum_apply,LinearMap.add_apply,
    LinearMap.smul_apply,Finset.sum_range_zero,LinearMap.zero_apply,pow_zero,one_smul,
    short_first_operator_second_zero K neg,short_higher_operator_second_zero K neg 2 (by decide),
    short_higher_operator_second_zero K neg 3 (by decide),smul_zero,add_zero,zero_add]
  change (integralOperator A neg 0 0).baseChange K (stringElement K neg 2)=stringElement K neg 2
  rw [stringElement,LinearMap.baseChange_tmul,integralOperator_zero]
  rfl

theorem modelRoot_fixes_second_string (neg : Bool) (t : K) :
    (modelRoot A K neg 0 t).val (stringElement K neg 2)=stringElement K neg 2 :=
  rootOperator_fixes_second_string K neg t

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalCharacteristicThreeString
