import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalFourteenSpan
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! An explicit finite family for the proved original fourteen-vector
span. Every vector belongs to the SAME least divided-power-stable
integral lattice. No independence or base-change faithfulness is yet
asserted by this family interface. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalFourteenFamily
open CFSGGTwoOriginalPositiveSerreStrings CFSGGTwoOriginalPositiveBracketTable
open CFSGGTwoOriginalFourteenSpan CFSGSerreDiagram CFSG.Models.Chevalley
local notation "A" => CartanMatrix.G₂
local notation "L" => RationalLie A

abbrev Index := (Bool × Fin 6) ⊕ Fin 2

def vectors : Index → L := Sum.elim (fun z=>positiveVector z.1 z.2) (fun i=>generator A (.H i))

theorem span_vectors_eq_fourteenSpace : Submodule.span ℚ (Set.range vectors)=fourteenSpace := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    cases i with
    | inl z => exact positiveSpace_le z.1 (Submodule.subset_span ⟨z.2,rfl⟩)
    | inr j =>
      have hc : cartanSpace≤fourteenSpace := le_sup_right
      exact hc (Submodule.subset_span ⟨j,rfl⟩)
  · have hp (neg:Bool) : positiveSpace neg≤Submodule.span ℚ (Set.range vectors) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact Submodule.subset_span ⟨Sum.inl (neg,i),rfl⟩
    have hc : cartanSpace≤Submodule.span ℚ (Set.range vectors) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact Submodule.subset_span ⟨Sum.inr i,rfl⟩
    exact sup_le (sup_le (hp false) (hp true)) hc

theorem span_vectors_eq_top : Submodule.span ℚ (Set.range vectors)=⊤ :=
  span_vectors_eq_fourteenSpace.trans fourteenSpace_eq_top

def rationalCombination : (Index→ℚ) →ₗ[ℚ] L := Fintype.linearCombination ℚ vectors

theorem rationalCombination_surjective : Function.Surjective rationalCombination := by
  apply LinearMap.range_eq_top.mp
  exact (Fintype.range_linearCombination ℚ vectors).trans span_vectors_eq_top

theorem vectors_mem_integralLattice (i:Index) : vectors i∈integralLattice A := by
  cases i with
  | inl z =>
    obtain ⟨neg,j⟩ := z
    fin_cases j
    · exact generator_mem_integralLattice A (if neg then .F 0 else .E 0)
    · exact generator_mem_integralLattice A (if neg then .F 1 else .E 1)
    · exact stringVector_mem_integralLattice neg 1
    · exact stringVector_mem_integralLattice neg 2
    · exact stringVector_mem_integralLattice neg 3
    · exact highestVector_mem_integralLattice neg
  | inr j => exact generator_mem_integralLattice A (.H j)

def integralVectors (i:Index) : integralLattice A := ⟨vectors i,vectors_mem_integralLattice i⟩

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalFourteenFamily
