import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalPositiveBracketTable
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalSimpleLowering
import SymmetricSubgroupAsymptotics.CFSGSerreGeneratedInvariantSpan

/-! The actual six positive roots, six negative roots and two Cartan
generators span the ORIGINAL rational G2 Serre quotient. This is proved
from generator-action invariance and actual quotient generation; no
finite-dimensionality or representation-faithfulness premise occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalFourteenSpan
open CFSGGTwoOriginalPositiveSerreStrings CFSGGTwoOriginalPositiveBracketTable
open CFSGGTwoOriginalStringWeights CFSGGTwoOriginalSimpleLowering
open CFSGSerreGeneratedInvariantSpan CFSGSerreLocalNilpotence CFSG.Models.Chevalley
local notation "A" => CartanMatrix.G₂
local notation "L" => RationalLie A

def cartanSpace : Submodule ℚ L := Submodule.span ℚ (Set.range (fun i:Fin 2=>generator A (.H i)))

def fourteenSpace : Submodule ℚ L := (positiveSpace false ⊔ positiveSpace true) ⊔ cartanSpace

theorem positiveSpace_le (neg : Bool) : positiveSpace neg≤fourteenSpace := by
  cases neg
  · exact le_sup_left.trans le_sup_left
  · exact le_sup_right.trans le_sup_left

theorem root_mem (neg : Bool) (i : Fin 2) : rootVector A neg i∈fourteenSpace := by
  fin_cases i
  · exact positiveSpace_le neg (short_vector_mem neg)
  · exact positiveSpace_le neg (long_vector_mem neg)

theorem coroot_mem (neg : Bool) (i : Fin 2) : coroot neg i∈fourteenSpace := by
  have hc : cartanSpace≤fourteenSpace := le_sup_right
  have h : generator A (.H i)∈fourteenSpace := hc (Submodule.subset_span ⟨i,rfl⟩)
  cases neg
  · exact h
  · exact (fourteenSpace).neg_mem h

private theorem opposite_on_positive (neg : Bool) (i : Fin 2) :
    ∀v∈positiveSpace neg,⁅oppositeVector neg i,v⁆∈fourteenSpace := by
  apply Submodule.span_induction
  · rintro _ ⟨j,rfl⟩
    fin_cases i
    · fin_cases j
      · change ⁅oppositeVector neg 0,rootVector A neg 0⁆∈fourteenSpace
        rw [opposite_same]
        exact fourteenSpace.neg_mem (coroot_mem neg 0)
      · change ⁅oppositeVector neg 0,rootVector A neg 1⁆∈fourteenSpace
        rw [opposite_distinct neg 0 1 (by decide)]
        exact fourteenSpace.zero_mem
      · change ⁅oppositeVector neg 0,stringVector neg 1⁆∈fourteenSpace
        rw [opposite_short_string_one]
        exact fourteenSpace.smul_mem (3:ℚ) (positiveSpace_le neg (long_vector_mem neg))
      · change ⁅oppositeVector neg 0,stringVector neg 2⁆∈fourteenSpace
        rw [opposite_short_string_two]
        exact fourteenSpace.smul_mem (2:ℚ) (positiveSpace_le neg (string_vector_mem neg 0))
      · change ⁅oppositeVector neg 0,stringVector neg 3⁆∈fourteenSpace
        rw [opposite_short_string_three]
        exact positiveSpace_le neg (string_vector_mem neg 1)
      · change ⁅oppositeVector neg 0,highestVector neg⁆∈fourteenSpace
        rw [opposite_short_highest]
        exact fourteenSpace.zero_mem
    · fin_cases j
      · change ⁅oppositeVector neg 1,rootVector A neg 0⁆∈fourteenSpace
        rw [opposite_distinct neg 1 0 (by decide)]
        exact fourteenSpace.zero_mem
      · change ⁅oppositeVector neg 1,rootVector A neg 1⁆∈fourteenSpace
        rw [opposite_same]
        exact fourteenSpace.neg_mem (coroot_mem neg 1)
      · change ⁅oppositeVector neg 1,stringVector neg 1⁆∈fourteenSpace
        rw [opposite_long_string_one]
        exact fourteenSpace.neg_mem (positiveSpace_le neg (short_vector_mem neg))
      · change ⁅oppositeVector neg 1,stringVector neg 2⁆∈fourteenSpace
        rw [opposite_long_string_two]
        exact fourteenSpace.zero_mem
      · change ⁅oppositeVector neg 1,stringVector neg 3⁆∈fourteenSpace
        rw [opposite_long_string_three]
        exact fourteenSpace.zero_mem
      · change ⁅oppositeVector neg 1,highestVector neg⁆∈fourteenSpace
        rw [opposite_long_highest]
        exact positiveSpace_le neg (string_vector_mem neg 2)
  · simpa only [lie_zero] using fourteenSpace.zero_mem
  · intro x y _ _ hx hy
    rw [lie_add]
    exact fourteenSpace.add_mem hx hy
  · intro c x _ hx
    rw [lie_smul]
    exact fourteenSpace.smul_mem c hx

private theorem root_on_positive (neg side : Bool) (i : Fin 2) :
    ∀v∈positiveSpace side,⁅rootVector A neg i,v⁆∈fourteenSpace := by
  by_cases he : neg=side
  · subst neg
    intro v hv
    apply positiveSpace_le side
    fin_cases i
    · exact short_preserves_positiveSpace side v hv
    · exact long_preserves_positiveSpace side v hv
  · cases side <;> cases neg
    · exact (he rfl).elim
    · exact opposite_on_positive false i
    · exact opposite_on_positive true i
    · exact (he rfl).elim

private theorem root_on_cartan (neg : Bool) (i : Fin 2) :
    ∀v∈cartanSpace,⁅rootVector A neg i,v⁆∈fourteenSpace := by
  apply Submodule.span_induction
  · rintro _ ⟨j,rfl⟩
    cases neg
    · change ⁅generator A (.E i),generator A (.H j)⁆∈fourteenSpace
      rw [←lie_skew (generator A (.E i)) (generator A (.H j)),generator_HE]
      exact fourteenSpace.neg_mem (by
        simpa only [Int.cast_smul_eq_zsmul] using fourteenSpace.smul_mem (A j i : ℚ) (root_mem false i))
    · change ⁅generator A (.F i),generator A (.H j)⁆∈fourteenSpace
      rw [←lie_skew (generator A (.F i)) (generator A (.H j)),generator_HF,neg_neg]
      simpa only [Int.cast_smul_eq_zsmul] using fourteenSpace.smul_mem (A j i : ℚ) (root_mem true i)
  · simpa only [lie_zero] using fourteenSpace.zero_mem
  · intro x y _ _ hx hy
    rw [lie_add]
    exact fourteenSpace.add_mem hx hy
  · intro c x _ hx
    rw [lie_smul]
    exact fourteenSpace.smul_mem c hx

theorem root_preserves_fourteenSpace (neg : Bool) (i : Fin 2) :
    ∀v∈fourteenSpace,⁅rootVector A neg i,v⁆∈fourteenSpace := by
  intro v hv
  obtain ⟨u,hu,h,hh,rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨p,hp,n,hn,rfl⟩ := Submodule.mem_sup.mp hu
  rw [lie_add,lie_add]
  exact fourteenSpace.add_mem (fourteenSpace.add_mem
    (root_on_positive neg false i p hp) (root_on_positive neg true i n hn))
      (root_on_cartan neg i h hh)

theorem fourteenSpace_eq_top : fourteenSpace=⊤ := by
  apply eq_top_of_EF_stable A
  · intro i
    exact root_mem false i
  · intro i
    exact root_mem true i
  · intro i
    exact root_preserves_fourteenSpace false i
  · intro i
    exact root_preserves_fourteenSpace true i

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalFourteenSpan
