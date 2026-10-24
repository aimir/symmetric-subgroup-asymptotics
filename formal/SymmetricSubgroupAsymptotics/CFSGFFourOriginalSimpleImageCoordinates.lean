import SymmetricSubgroupAsymptotics.CFSGFiniteImageCoordinateSpan
import SymmetricSubgroupAsymptotics.CFSGFFourIntegralRealization
import SymmetricSubgroupAsymptotics.CFSGFFourE6NormSimpleCoefficientPilot
import SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientStepEntries

/-! Integral coordinates on the four actual original F4 positive simple
images. They give source injectivity on their four-vector span, which is
the initial faithful subspace for the selected height induction. No
faithfulness of the complete original representation is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalSimpleImageCoordinates
open CFSG.Models.Chevalley CFSGFFourSerreMatrices
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGFFourE6NormQuotientCoefficientPilot CFSGFFourE6NormSimpleCoefficientPilot
open CFSGFFourE6NormQuotientStepEntries CFSGFiniteImageCoordinateSpan
local instance : DecidableEq (Roots CartanMatrix.E₆):=Classical.decEq _
local notation "A" => CartanMatrix.F₄

def row (i:Fin 4) : Index:=Sum.inl (E6Index (representative i))
def col (i:Fin 4) : Index:=Sum.inr
  (negativeIndex CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
    (E6Index (representative i)))

def simpleEntryData (i j:Fin 4) : ℤ :=
  firstEntry j (.inl (representative i)) (.inr (-simpleVector (representative i)))

theorem simpleEntryData_eq : ∀i j:Fin 4,simpleEntryData i j=if i=j then 1 else 0 :=
  by decide +kernel

private theorem erase_row (i:Fin 4) : eraseGeck (row i)=.inl (representative i) := by
  simp only [row,eraseGeck,Equiv.symm_apply_apply]

private theorem erase_col (i:Fin 4) :
    eraseGeck (col i)=.inr (-simpleVector (representative i)) := by
  change Sum.inr (negativeIndex CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
    (E6Index (representative i))).val=Sum.inr (-simpleVector (representative i))
  rw [negative_val,E6Index_val]

theorem integer_coordinate (i j:Fin 4) : integerE j (row i) (col i)=simpleEntryData i j := by
  fin_cases j
  · change (e6EZ 0+e6EZ 5) (row i) (col i)=
      stepEntry 0 (.inl (representative i)) (.inr (-simpleVector (representative i)))+
        stepEntry 5 (.inl (representative i)) (.inr (-simpleVector (representative i)))
    rw [Matrix.add_apply,e6EZ_entry,e6EZ_entry,erase_row,erase_col]
  · change (e6EZ 2+e6EZ 4) (row i) (col i)=
      stepEntry 2 (.inl (representative i)) (.inr (-simpleVector (representative i)))+
        stepEntry 4 (.inl (representative i)) (.inr (-simpleVector (representative i)))
    rw [Matrix.add_apply,e6EZ_entry,e6EZ_entry,erase_row,erase_col]
  · change e6EZ 3 (row i) (col i)=
      stepEntry 3 (.inl (representative i)) (.inr (-simpleVector (representative i)))
    rw [e6EZ_entry,erase_row,erase_col]
  · change e6EZ 1 (row i) (col i)=
      stepEntry 1 (.inl (representative i)) (.inr (-simpleVector (representative i)))
    rw [e6EZ_entry,erase_row,erase_col]

def coordinates : Mat→ₗ[ℚ](Fin 4→ℚ) where
  toFun M i:=M (row i) (col i)
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

theorem positive_coordinate (i j:Fin 4) :
    positive j (row i) (col i)=if i=j then 1 else 0 := by
  have h:=congrArg (fun M:Mat=>M (row i) (col i)) (map_integerE j)
  change (integerE j (row i) (col i):ℚ)=positive j (row i) (col i) at h
  rw [←h,integer_coordinate,simpleEntryData_eq]
  split_ifs <;> rfl

theorem coordinates_generator (i:Fin 4) :
    coordinates (rationalRepresentation (generator A (.E i)))=Pi.single i 1 := by
  funext j
  change rationalRepresentation (generator A (.E i)) (row j) (col j)=
    (Pi.single i (1:ℚ):Fin 4→ℚ) j
  rw [rationalRepresentation_E,positive_coordinate]
  simp only [Pi.single_apply]

def simpleSpace : Submodule ℚ (RationalLie A) :=
  Submodule.span ℚ (Set.range (fun i:Fin 4=>generator A (.E i)))

theorem rationalRepresentation_injective_on_simpleSpace :
    Set.InjOn rationalRepresentation (simpleSpace:Set (RationalLie A)) :=
  injective_on_span rationalRepresentation.toLinearMap (fun i:Fin 4=>generator A (.E i))
    coordinates coordinates_generator

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalSimpleImageCoordinates
