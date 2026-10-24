import SymmetricSubgroupAsymptotics.CFSGSerreGeneratorRelations
import SymmetricSubgroupAsymptotics.CFSGSerreDiagramLattice
import Mathlib.Tactic.Module

/-! A selected original-source pilot for the F4 integral basis frontier.
The middle B2 string is normalized in the actual rational Serre quotient
before reduction, and its four vectors lie in the same least stable
integral lattice. Source identities use Serre relations and Jacobi, never
an assumed injective matrix representation. This is not a 52-vector basis
or original F4 correspondence theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleSerreStrings
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence CFSGSerreDiagram
local notation "A" => CartanMatrix.F₄
local notation "L" => RationalLie A

def shortVector (neg:Bool) : L := rootVector A neg 1
def longVector (neg:Bool) : L := rootVector A neg 2
def stringVector (neg:Bool) (k:ℕ) : L := dividedPower A neg 1 k (longVector neg)

theorem short_serre_three (neg:Bool) :
    ⁅shortVector neg,⁅shortVector neg,⁅shortVector neg,longVector neg⁆⁆⁆=0 := by
  cases neg
  · have h:=generator_adE A (1:Fin 4) 2
    change (LieAlgebra.ad ℚ L (generator A (.E 1))^3) (generator A (.E 2))=0 at h
    simpa only [pow_succ',Module.End.mul_apply,LieAlgebra.ad_apply,pow_zero,
      Module.End.one_apply,shortVector,longVector,rootVector,Bool.false_eq_true,if_false] using h
  · have h:=generator_adF A (1:Fin 4) 2
    change (LieAlgebra.ad ℚ L (generator A (.F 1))^3) (generator A (.F 2))=0 at h
    simpa only [pow_succ',Module.End.mul_apply,LieAlgebra.ad_apply,pow_zero,
      Module.End.one_apply,shortVector,longVector,rootVector,if_true] using h

theorem long_serre_two (neg:Bool) :
    ⁅longVector neg,⁅longVector neg,shortVector neg⁆⁆=0 := by
  cases neg
  · have h:=generator_adE A (2:Fin 4) 1
    change (LieAlgebra.ad ℚ L (generator A (.E 2))^2) (generator A (.E 1))=0 at h
    simpa only [pow_succ',Module.End.mul_apply,LieAlgebra.ad_apply,pow_zero,
      Module.End.one_apply,shortVector,longVector,rootVector,Bool.false_eq_true,if_false] using h
  · have h:=generator_adF A (2:Fin 4) 1
    change (LieAlgebra.ad ℚ L (generator A (.F 2))^2) (generator A (.F 1))=0 at h
    simpa only [pow_succ',Module.End.mul_apply,LieAlgebra.ad_apply,pow_zero,
      Module.End.one_apply,shortVector,longVector,rootVector,if_true] using h

theorem string_zero (neg:Bool) : stringVector neg 0=longVector neg := by
  simp [stringVector,dividedPower]

theorem string_one (neg:Bool) : stringVector neg 1=⁅shortVector neg,longVector neg⁆ := by
  simp [stringVector,dividedPower,shortVector]

theorem string_two (neg:Bool) :
    stringVector neg 2=(1/2:ℚ) • ⁅shortVector neg,⁅shortVector neg,longVector neg⁆⁆ := by
  norm_num [stringVector,dividedPower,Nat.factorial_succ,Nat.factorial_zero,pow_succ',
    Module.End.mul_apply,LieAlgebra.ad_apply,shortVector]

private theorem long_first_zero (neg:Bool) :
    ⁅longVector neg,⁅shortVector neg,longVector neg⁆⁆=0 := by
  have h:=long_serre_two neg
  rw [←lie_skew (longVector neg) (shortVector neg),lie_neg] at h
  exact neg_eq_zero.mp h

private theorem long_second_zero (neg:Bool) :
    ⁅longVector neg,⁅shortVector neg,⁅shortVector neg,longVector neg⁆⁆⁆=0 := by
  rw [leibniz_lie,←lie_skew (longVector neg) (shortVector neg),neg_lie,lie_self,
    long_first_zero,lie_zero,neg_zero,zero_add]

theorem short_string_one (neg:Bool) :
    ⁅shortVector neg,stringVector neg 1⁆=(2:ℚ) • stringVector neg 2 := by
  rw [string_one,string_two]
  module

theorem short_string_two (neg:Bool) : ⁅shortVector neg,stringVector neg 2⁆=0 := by
  rw [string_two,lie_smul,short_serre_three,smul_zero]

theorem long_string_one (neg:Bool) : ⁅longVector neg,stringVector neg 1⁆=0 := by
  rw [string_one,long_first_zero]

theorem long_string_two (neg:Bool) : ⁅longVector neg,stringVector neg 2⁆=0 := by
  rw [string_two,lie_smul,long_second_zero,smul_zero]

theorem string_one_two (neg:Bool) : ⁅stringVector neg 1,stringVector neg 2⁆=0 := by
  have h:=leibniz_lie (longVector neg) (shortVector neg)
    ⁅shortVector neg,⁅shortVector neg,longVector neg⁆⁆
  rw [short_serre_three,lie_zero,←lie_skew (longVector neg) (shortVector neg),
    neg_lie,long_second_zero,lie_zero,add_zero] at h
  have hz:⁅⁅shortVector neg,longVector neg⁆,⁅shortVector neg,⁅shortVector neg,longVector neg⁆⁆⁆=0 :=
    neg_eq_zero.mp h.symm
  rw [string_one,string_two,lie_smul,hz,smul_zero]

theorem shortVector_mem_integralLattice (neg:Bool) : shortVector neg∈integralLattice A :=
  generator_mem_integralLattice A (if neg then .F 1 else .E 1)

theorem longVector_mem_integralLattice (neg:Bool) : longVector neg∈integralLattice A :=
  generator_mem_integralLattice A (if neg then .F 2 else .E 2)

theorem stringVector_mem_integralLattice (neg:Bool) (k:ℕ) :
    stringVector neg k∈integralLattice A :=
  dividedPower_mem A neg 1 k _ (longVector_mem_integralLattice neg)

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleSerreStrings
