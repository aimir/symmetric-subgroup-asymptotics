import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalFieldBasis
import SymmetricSubgroupAsymptotics.CFSGGTwoAxisCoordinates

/-! A literal seven-coordinate quotient map from the SAME original G2
integral tensor space onto the native axis hyperplane. The section is
constructed from the original fourteen-vector basis. This file asserts
surjectivity only; invariance and exceptional root covariance are
separate characteristic-three obligations. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalSevenProjection
open CFSG.Models.Chevalley CFSGGTwoSerreMatrices CFSGGTwoAxisCoordinates
open CFSGGTwoOriginalFieldBasis CFSGGTwoOriginalMatrixCoordinates
variable (K : Type) [Field K]

private def coordinateProjection : (BasisIndex → K) →ₗ[K] axisHyperplane K where
  toFun c := ⟨Sum.elim
    (fun i => match i.val with
      | 0 => c (Sum.inl (false,5))
      | 1 => c (Sum.inl (false,4))
      | 2 => c (Sum.inl (false,1))
      | _ => -c (Sum.inr 1))
    (fun i => match i.val with
      | 0 => c (Sum.inl (true,5))
      | 1 => -c (Sum.inl (true,4))
      | 2 => c (Sum.inl (true,1))
      | _ => -c (Sum.inr 1)),rfl⟩
  map_add' c d := by
    apply Subtype.ext
    funext i
    rcases i with j|j <;> fin_cases j
    · rfl
    · rfl
    · rfl
    · change -(c (Sum.inr 1)+d (Sum.inr 1))= -c (Sum.inr 1)+ -d (Sum.inr 1)
      exact neg_add _ _
    · rfl
    · change -(c (Sum.inl (true,4))+d (Sum.inl (true,4)))=
        -c (Sum.inl (true,4))+ -d (Sum.inl (true,4))
      exact neg_add _ _
    · rfl
    · change -(c (Sum.inr 1)+d (Sum.inr 1))= -c (Sum.inr 1)+ -d (Sum.inr 1)
      exact neg_add _ _
  map_smul' a c := by
    apply Subtype.ext
    funext i
    rcases i with j|j <;> fin_cases j <;> simp

def sevenProjection : Space CartanMatrix.G₂ K →ₗ[K] axisHyperplane K :=
  (coordinateProjection K).comp (fieldCoordinates K)

private def sectionCoefficients (v : axisHyperplane K) : BasisIndex → K :=
  Sum.elim (fun z => if z.1 then
    match z.2.val with
    | 1 => v.val (neg 2)
    | 4 => -v.val (neg 1)
    | 5 => v.val (neg 0)
    | _ => 0
    else match z.2.val with
    | 1 => v.val (pos 2)
    | 4 => v.val (pos 1)
    | 5 => v.val (pos 0)
    | _ => 0)
    (fun j => match j.val with | 0 => 0 | _ => -v.val (pos 3))

private theorem coordinateProjection_section (v : axisHyperplane K) :
    coordinateProjection K (sectionCoefficients K v)=v := by
  apply Subtype.ext
  funext i
  rcases i with j|j <;> fin_cases j <;>
    simp [coordinateProjection,sectionCoefficients,pos,neg]
  exact v.property

def sevenSection (v : axisHyperplane K) : Space CartanMatrix.G₂ K :=
  fieldCombination K (sectionCoefficients K v)

theorem sevenProjection_section (v : axisHyperplane K) :
    sevenProjection K (sevenSection K v)=v := by
  change coordinateProjection K (fieldCoordinates K
    (fieldCombination K (sectionCoefficients K v)))=v
  rw [fieldCoordinates_combination,coordinateProjection_section]

theorem sevenProjection_surjective : Function.Surjective (sevenProjection K) :=
  fun v => ⟨sevenSection K v,sevenProjection_section K v⟩

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalSevenProjection
