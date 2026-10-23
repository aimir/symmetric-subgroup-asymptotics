import SymmetricSubgroupAsymptotics.CFSGSerreGeneratorRelations
import SymmetricSubgroupAsymptotics.CFSGSerreDiagramLattice
import Mathlib.Tactic.Module

/-! The literal original G2 positive Serre string, with rational divided
powers normalized before reduction. The coefficient three in the top
bracket is proved in the original quotient, not inferred from a matrix
image. No simplicity or faithfulness premise occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalPositiveSerreStrings
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence CFSGSerreDiagram
local notation "A" => CartanMatrix.G₂
local notation "L" => RationalLie A

def shortVector (neg : Bool) : L := rootVector A neg 0

def longVector (neg : Bool) : L := rootVector A neg 1

def stringVector (neg : Bool) (k : ℕ) : L :=
  dividedPower A neg 0 k (longVector neg)

def highestVector (neg : Bool) : L := ⁅longVector neg,stringVector neg 3⁆

private theorem dividedPower_one_apply (neg : Bool) (i : Fin 2) (v : L) :
    dividedPower A neg i 1 v=⁅rootVector A neg i,v⁆ := by
  simp [dividedPower]

theorem short_serre_four (neg : Bool) :
    ⁅shortVector neg,⁅shortVector neg,⁅shortVector neg,⁅shortVector neg,longVector neg⁆⁆⁆⁆=0 := by
  cases neg
  · have h := generator_adE A (0:Fin 2) 1
    change (LieAlgebra.ad ℚ L (generator A (.E 0))^4) (generator A (.E 1))=0 at h
    simpa only [pow_succ',Module.End.mul_apply,LieAlgebra.ad_apply,pow_zero,Module.End.one_apply,
      shortVector,longVector,rootVector,Bool.false_eq_true,if_false] using h
  · have h := generator_adF A (0:Fin 2) 1
    change (LieAlgebra.ad ℚ L (generator A (.F 0))^4) (generator A (.F 1))=0 at h
    simpa only [pow_succ',Module.End.mul_apply,LieAlgebra.ad_apply,pow_zero,Module.End.one_apply,
      shortVector,longVector,rootVector,if_true] using h

theorem long_serre_two (neg : Bool) :
    ⁅longVector neg,⁅longVector neg,shortVector neg⁆⁆=0 := by
  cases neg
  · have h := generator_adE A (1:Fin 2) 0
    change (LieAlgebra.ad ℚ L (generator A (.E 1))^2) (generator A (.E 0))=0 at h
    simpa only [pow_succ',Module.End.mul_apply,LieAlgebra.ad_apply,pow_zero,Module.End.one_apply,
      shortVector,longVector,rootVector,Bool.false_eq_true,if_false] using h
  · have h := generator_adF A (1:Fin 2) 0
    change (LieAlgebra.ad ℚ L (generator A (.F 1))^2) (generator A (.F 0))=0 at h
    simpa only [pow_succ',Module.End.mul_apply,LieAlgebra.ad_apply,pow_zero,Module.End.one_apply,
      shortVector,longVector,rootVector,if_true] using h

theorem string_zero (neg : Bool) : stringVector neg 0=longVector neg := by
  simp [stringVector,dividedPower]

theorem string_one (neg : Bool) : stringVector neg 1=⁅shortVector neg,longVector neg⁆ :=
  dividedPower_one_apply neg 0 _

theorem string_two (neg : Bool) :
    stringVector neg 2=(1/2:ℚ) • ⁅shortVector neg,⁅shortVector neg,longVector neg⁆⁆ := by
  norm_num [stringVector,dividedPower,Nat.factorial_succ,Nat.factorial_zero,pow_succ',Module.End.mul_apply,LieAlgebra.ad_apply,
    shortVector]

theorem string_three (neg : Bool) :
    stringVector neg 3=(1/6:ℚ) • ⁅shortVector neg,⁅shortVector neg,⁅shortVector neg,longVector neg⁆⁆⁆ := by
  norm_num [stringVector,dividedPower,Nat.factorial_succ,Nat.factorial_zero,pow_succ',Module.End.mul_apply,LieAlgebra.ad_apply,
    shortVector]

private theorem long_first_zero (neg : Bool) :
    ⁅longVector neg,⁅shortVector neg,longVector neg⁆⁆=0 := by
  have h := long_serre_two neg
  rw [←lie_skew (longVector neg) (shortVector neg),lie_neg] at h
  exact neg_eq_zero.mp h

private theorem long_second_zero (neg : Bool) :
    ⁅longVector neg,⁅shortVector neg,⁅shortVector neg,longVector neg⁆⁆⁆=0 := by
  rw [leibniz_lie,←lie_skew (longVector neg) (shortVector neg),neg_lie,lie_self,
    long_first_zero,lie_zero,neg_zero,zero_add]

theorem short_string_one (neg : Bool) :
    ⁅shortVector neg,stringVector neg 1⁆=(2:ℚ) • stringVector neg 2 := by
  rw [string_one,string_two]
  module

theorem short_string_two (neg : Bool) :
    ⁅shortVector neg,stringVector neg 2⁆=(3:ℚ) • stringVector neg 3 := by
  rw [string_two,string_three,lie_smul]
  module

theorem short_string_three (neg : Bool) : ⁅shortVector neg,stringVector neg 3⁆=0 := by
  rw [string_three,lie_smul,short_serre_four,smul_zero]

theorem long_string_one (neg : Bool) : ⁅longVector neg,stringVector neg 1⁆=0 := by
  rw [string_one,long_first_zero]

theorem long_string_two (neg : Bool) : ⁅longVector neg,stringVector neg 2⁆=0 := by
  rw [string_two,lie_smul,long_second_zero,smul_zero]

theorem string_one_two (neg : Bool) :
    ⁅stringVector neg 1,stringVector neg 2⁆=(-3:ℚ) • highestVector neg := by
  have h : ⁅⁅shortVector neg,longVector neg⁆,⁅shortVector neg,⁅shortVector neg,longVector neg⁆⁆⁆ =
      -⁅longVector neg,⁅shortVector neg,⁅shortVector neg,⁅shortVector neg,longVector neg⁆⁆⁆⁆ := by
    have he := leibniz_lie (longVector neg) (shortVector neg)
      ⁅shortVector neg,⁅shortVector neg,longVector neg⁆⁆
    rw [←lie_skew (longVector neg) (shortVector neg),neg_lie,long_second_zero,lie_zero,add_zero] at he
    exact neg_eq_iff_eq_neg.mp he.symm
  rw [string_one,string_two,lie_smul,h,highestVector,string_three,lie_smul]
  module

theorem stringVector_mem_integralLattice (neg : Bool) (k : ℕ) :
    stringVector neg k ∈ integralLattice A :=
  dividedPower_mem A neg 0 k (longVector neg)
    (generator_mem_integralLattice A (if neg then .F 1 else .E 1))

theorem highestVector_mem_integralLattice (neg : Bool) : highestVector neg ∈ integralLattice A := by
  have h := dividedPower_mem A neg 1 1 (stringVector neg 3)
    (stringVector_mem_integralLattice neg 3)
  simpa only [dividedPower_one_apply,highestVector,longVector] using h

def integralString (neg : Bool) (k : ℕ) : integralLattice A :=
  ⟨stringVector neg k,stringVector_mem_integralLattice neg k⟩

def integralHighest (neg : Bool) : integralLattice A :=
  ⟨highestVector neg,highestVector_mem_integralLattice neg⟩

theorem integral_short_string_two (neg : Bool) :
    integralOperator A neg 0 1 (integralString neg 2)=3 • integralString neg 3 := by
  apply Subtype.ext
  change dividedPower A neg 0 1 (stringVector neg 2)=3 • stringVector neg 3
  rw [dividedPower_one_apply]
  exact (short_string_two neg).trans (Nat.cast_smul_eq_nsmul ℚ 3 (stringVector neg 3))

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalPositiveSerreStrings
