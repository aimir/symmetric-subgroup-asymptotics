import SymmetricSubgroupAsymptotics.CFSGFFourOriginalFiftyTwoFamily
import SymmetricSubgroupAsymptotics.CFSGSerreSimpleBracketLowering

/-! The first original source-span layer: all simple-simple brackets
belong to the displayed 24-root family, and their opposite lowerings
belong to the simple span. Only genuine Serre and Jacobi identities are
used. Full 52-vector spanning is not asserted here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightTwoSpan
open CFSG.Models.Chevalley CFSGFFourOriginalFiftyTwoFamily
open CFSGSerreLocalNilpotence CFSGSerreSignedRootWeights CFSGSerreSimpleBracketLowering
local notation "A" => CartanMatrix.F₄
local notation "L" => RationalLie A

def positiveFamilySpace (neg:Bool) : Submodule ℚ L :=
  Submodule.span ℚ (Set.range (fun j:Fin 24=>(rootVectors neg j).val))

def signedSimpleSpace (neg:Bool) : Submodule ℚ L :=
  Submodule.span ℚ (Set.range (rootVector A neg))

theorem path_four (neg:Bool) :
    (rootVectors neg 4).val=⁅rootVector A neg 3,rootVector A neg 2⁆ := by
  change dividedPower A neg 3 1 (rootVector A neg 2)=_
  simp [dividedPower]

theorem path_five (neg:Bool) :
    (rootVectors neg 5).val=⁅rootVector A neg 2,rootVector A neg 1⁆ := by
  change dividedPower A neg 2 1 (rootVector A neg 1)=_
  simp [dividedPower]

theorem path_six (neg:Bool) :
    (rootVectors neg 6).val=⁅rootVector A neg 1,rootVector A neg 0⁆ := by
  change dividedPower A neg 1 1 (rootVector A neg 0)=_
  simp [dividedPower]

theorem simple_mem_family (neg:Bool) (i:Fin 4) :
    rootVector A neg i∈positiveFamilySpace neg := by
  apply Submodule.subset_span
  fin_cases i
  · exact ⟨3,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨0,rfl⟩

private theorem path_mem (neg:Bool) (j:Fin 24) :
    (rootVectors neg j).val∈positiveFamilySpace neg := Submodule.subset_span ⟨j,rfl⟩

private theorem nonadjacent (neg:Bool) (i j:Fin 4) (hij:A i j=0) :
    ⁅rootVector A neg i,rootVector A neg j⁆=0 := by
  cases neg
  · have h:=generator_adE A i j
    rw [hij] at h
    exact h
  · have h:=generator_adF A i j
    rw [hij] at h
    exact h

theorem simple_bracket_mem_family (neg:Bool) (i j:Fin 4) :
    ⁅rootVector A neg i,rootVector A neg j⁆∈positiveFamilySpace neg := by
  fin_cases i <;> fin_cases j
  · simpa only [lie_self] using (positiveFamilySpace neg).zero_mem
  · change ⁅rootVector A neg 0,rootVector A neg 1⁆∈positiveFamilySpace neg
    rw [←lie_skew (rootVector A neg 0) (rootVector A neg 1),←path_six]
    exact (positiveFamilySpace neg).neg_mem (path_mem neg 6)
  · change ⁅rootVector A neg 0,rootVector A neg 2⁆∈positiveFamilySpace neg
    rw [nonadjacent neg 0 2 (by decide)]
    exact (positiveFamilySpace neg).zero_mem
  · change ⁅rootVector A neg 0,rootVector A neg 3⁆∈positiveFamilySpace neg
    rw [nonadjacent neg 0 3 (by decide)]
    exact (positiveFamilySpace neg).zero_mem
  · change ⁅rootVector A neg 1,rootVector A neg 0⁆∈positiveFamilySpace neg
    rw [←path_six]
    exact path_mem neg 6
  · simpa only [lie_self] using (positiveFamilySpace neg).zero_mem
  · change ⁅rootVector A neg 1,rootVector A neg 2⁆∈positiveFamilySpace neg
    rw [←lie_skew (rootVector A neg 1) (rootVector A neg 2),←path_five]
    exact (positiveFamilySpace neg).neg_mem (path_mem neg 5)
  · change ⁅rootVector A neg 1,rootVector A neg 3⁆∈positiveFamilySpace neg
    rw [nonadjacent neg 1 3 (by decide)]
    exact (positiveFamilySpace neg).zero_mem
  · change ⁅rootVector A neg 2,rootVector A neg 0⁆∈positiveFamilySpace neg
    rw [nonadjacent neg 2 0 (by decide)]
    exact (positiveFamilySpace neg).zero_mem
  · change ⁅rootVector A neg 2,rootVector A neg 1⁆∈positiveFamilySpace neg
    rw [←path_five]
    exact path_mem neg 5
  · simpa only [lie_self] using (positiveFamilySpace neg).zero_mem
  · change ⁅rootVector A neg 2,rootVector A neg 3⁆∈positiveFamilySpace neg
    rw [←lie_skew (rootVector A neg 2) (rootVector A neg 3),←path_four]
    exact (positiveFamilySpace neg).neg_mem (path_mem neg 4)
  · change ⁅rootVector A neg 3,rootVector A neg 0⁆∈positiveFamilySpace neg
    rw [nonadjacent neg 3 0 (by decide)]
    exact (positiveFamilySpace neg).zero_mem
  · change ⁅rootVector A neg 3,rootVector A neg 1⁆∈positiveFamilySpace neg
    rw [nonadjacent neg 3 1 (by decide)]
    exact (positiveFamilySpace neg).zero_mem
  · change ⁅rootVector A neg 3,rootVector A neg 2⁆∈positiveFamilySpace neg
    rw [←path_four]
    exact path_mem neg 4
  · simpa only [lie_self] using (positiveFamilySpace neg).zero_mem

theorem opposite_simple_bracket_mem_simpleSpace (neg:Bool) (k i j:Fin 4) :
    ⁅oppositeVector A neg k,⁅rootVector A neg i,rootVector A neg j⁆⁆∈signedSimpleSpace neg := by
  rw [opposite_simple_bracket]
  apply (signedSimpleSpace neg).add_mem
  · split_ifs
    · exact (signedSimpleSpace neg).smul_mem _ (Submodule.subset_span ⟨j,rfl⟩)
    · exact (signedSimpleSpace neg).zero_mem
  · split_ifs
    · exact (signedSimpleSpace neg).smul_mem _ (Submodule.subset_span ⟨i,rfl⟩)
    · exact (signedSimpleSpace neg).zero_mem

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightTwoSpan
