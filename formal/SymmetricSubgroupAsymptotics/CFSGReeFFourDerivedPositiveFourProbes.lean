import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOuterSaving
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOrderedRootWords

/-! Four literal derived-positive probes used by the fixed selected entry
constraints: x, yxy^-1, y², wm*x*wm^-1. This proves ONLY membership and
root-list binding, not a generation or common-centralizer assertion. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourDerivedPositiveFourProbes
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFieldParameters
open CFSGReeFFourOuterThreeWord CFSGReeFFourMiddleDerivedFiveWord
open CFSGReeFFourBinaryOuterSaving CFSGReeFFourMiddleSquareCommutator
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourRelativePositiveSubgroups
open CFSGReeFFourOuterFixedRoot CFSGReeFFourMiddleFixedSubgroup
open CFSGReeFFourMiddleFixedWords CFSGReeFFourDerivedAmbientHom
open CFSGReeFFourBinaryOrderedRootWords CFSGReeFFourMiddleDerivedFiveRootWords
open CFSGFFourNormPrimeFieldWords

private theorem outer_positive (m : ℕ) : outerInvolution m∈fixedPositive m :=
  fixedOuterHom_range_le_fixedPositive m ⟨Multiplicative.ofAdd 1,rfl⟩

private theorem middle_positive (m : ℕ) : fourCycle m∈fixedPositive m :=
  middleFixedSubgroup_le_fixedPositive m
    ⟨1,alpha m 1,0,alpha m 0+1^2*alpha m 1,rfl⟩

private theorem normal_conjugate {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (a g : G) (hg : g∈N) : a*g*a⁻¹∈N := by
  have h := (inferInstance : N.Normal).conj_mem' g hg a⁻¹
  simpa only [inv_inv] using h

def probes (m : ℕ) : Fin 4 → originalModelFixed m :=
  ![outerInvolution m,
    fourCycle m*outerInvolution m*(fourCycle m)⁻¹,
    (fourCycle m)^2,
    middleFixedWeyl m*outerInvolution m*(middleFixedWeyl m)⁻¹]

theorem probes_positive (m : ℕ) (i : Fin 4) : probes m i∈fixedPositive m := by
  fin_cases i
  · exact outer_positive m
  · exact (fixedPositive m).mul_mem
      ((fixedPositive m).mul_mem (middle_positive m) (outer_positive m))
      ((fixedPositive m).inv_mem (middle_positive m))
  · exact (fixedPositive m).pow_mem (middle_positive m) 2
  · exact middle_conjugate_fixedOuterHom_range_le m
      ⟨outerInvolution m,⟨Multiplicative.ofAdd 1,rfl⟩,rfl⟩

theorem probes_derived (m : ℕ) (i : Fin 4) :
    probes m i∈commutator (originalModelFixed m) := by
  fin_cases i
  · exact outer_mem_derived m
  · exact normal_conjugate _ (fourCycle m) (outerInvolution m) (outer_mem_derived m)
  · exact square_mem_derived m
  · exact normal_conjugate _ (middleFixedWeyl m) (outerInvolution m) (outer_mem_derived m)

def derivedProbe (m : ℕ) (i : Fin 4) : commutator (originalModelFixed m) :=
  ⟨probes m i,probes_derived m i⟩

theorem derivedProbe_mem_positive (m : ℕ) (i : Fin 4) :
    derivedProbe m i∈derivedPositive m := probes_positive m i

def probeLetters : Fin 4 → List Letter :=
  ![outerLetters,
    fourCycleLetters++outerLetters++fourCycleLetters.reverse,
    fourCycleLetters++fourCycleLetters,
    CFSGReeFFourBinarySeedMiddleWeylMatrix.letters++outerLetters++
      CFSGReeFFourBinarySeedMiddleWeylMatrix.letters.reverse]

theorem probe_letters_value (m : ℕ) (i : Fin 4) :
    wordValue (Field m) (probeLetters i)=(probes m i).val := by
  fin_cases i
  · exact outerLetters_value m
  · change wordValue (Field m)
      (fourCycleLetters++outerLetters++fourCycleLetters.reverse)=
        (fourCycle m*outerInvolution m*(fourCycle m)⁻¹).val
    simp only [wordValue_append,reversed_letters_value,fourCycleLetters_value,
      outerLetters_value,outerInvolution,Subgroup.coe_mul,Subgroup.coe_inv,mul_assoc]
  · change wordValue (Field m) (fourCycleLetters++fourCycleLetters)=((fourCycle m)^2).val
    rw [wordValue_append,fourCycleLetters_value,pow_two]
    rfl
  · change wordValue (Field m)
      (CFSGReeFFourBinarySeedMiddleWeylMatrix.letters++outerLetters++
        CFSGReeFFourBinarySeedMiddleWeylMatrix.letters.reverse)=
      (middleFixedWeyl m*outerInvolution m*(middleFixedWeyl m)⁻¹).val
    simp only [wordValue_append,reversed_letters_value,middle_weyl_letters_value,
      outerLetters_value,outerInvolution,middleFixedWeyl,Subgroup.coe_mul,Subgroup.coe_inv,mul_assoc]

end SymmetricSubgroupAsymptotics.CFSGReeFFourDerivedPositiveFourProbes
