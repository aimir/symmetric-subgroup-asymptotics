import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryConjugation
import SymmetricSubgroupAsymptotics.CFSGSymplecticRootParameters

/-! The actual binary generating pair inside the literal elementary C
subgroup. The first element combines a disjoint order-three rotation and
short root; the second is the original checked Coxeter word. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped CharTwo
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryPairElements
open Matrix CFSGSymplecticSerreMatrices CFSGSymplecticBinaryRotationArrays
open CFSGSymplecticBinaryCoxeterMatrix CFSGSymplecticBinaryConjugation
variable (K : Type) [Field K] [CharP K 2]

def binaryRotation (s : ℕ) : elementaryRootGroup K (s+3) :=
  let W := coxeterWeyl K (s+2)
  (W*elementaryRoot K (s+3) true (Fin.last (s+2)) 1*W⁻¹)*
    (W*elementaryRoot K (s+3) false (Fin.last (s+2)) 1*W⁻¹)

def binaryFirst (s : ℕ) : elementaryRootGroup K (s+3) :=
  binaryRotation K s*elementaryRoot K (s+3) false (⟨1,by omega⟩ : Fin (s+3)) 1

def binarySecond (s : ℕ) : elementaryRootGroup K (s+3) := coxeterWeyl K (s+2)

omit [CharP K 2] in
theorem terminal_positive_array (s : ℕ) :
    ((elementaryRoot K (s+3) false (Fin.last (s+2)) 1).val : Mat K (s+3))=
      longArray (Sum.inl (Fin.last (s+2))) := by
  change 1+(1 : K) • positive K (s+3) (Fin.last (s+2))=_
  simp [positive,longArray,paired]

omit [CharP K 2] in
theorem terminal_negative_array (s : ℕ) :
    ((elementaryRoot K (s+3) true (Fin.last (s+2)) 1).val : Mat K (s+3))=
      longArray (Sum.inr (Fin.last (s+2))) := by
  change 1+(1 : K) • negative K (s+3) (Fin.last (s+2))=_
  simp [negative,positive,longArray,paired,Matrix.transpose_single]

theorem binaryRotation_array (s : ℕ) :
    ((binaryRotation K s).val : Mat K (s+3))=rotationArray (s+3) (by omega) := by
  change
    (((coxeterWeyl K (s+2)).val : Mat K (s+3))*
      ((elementaryRoot K (s+3) true (Fin.last (s+2)) 1).val : Mat K (s+3))*
      (↑((coxeterWeyl K (s+2)).val⁻¹) : Mat K (s+3)))*
    (((coxeterWeyl K (s+2)).val : Mat K (s+3))*
      ((elementaryRoot K (s+3) false (Fin.last (s+2)) 1).val : Mat K (s+3))*
      (↑((coxeterWeyl K (s+2)).val⁻¹) : Mat K (s+3)))=_
  rw [terminal_negative_array,terminal_positive_array,conjugation_long,conjugation_long,
    cyclePerm_negative_last,cyclePerm_positive_last]
  rfl

theorem short_one_array (s : ℕ) :
    ((elementaryRoot K (s+3) false (⟨1,by omega⟩ : Fin (s+3)) 1).val : Mat K (s+3))=
      shortArray (coord1 (s+3) (by omega)) (coord2 (s+3) (by omega)) := by
  change 1+(1 : K) • positive K (s+3) (⟨1,by omega⟩ : Fin (s+3))=_
  simp [positive,shortArray,coord1,coord2,paired,show 1+1<s+3 by omega]
  ext i j
  simp only [Matrix.add_apply,Matrix.sub_apply]
  rw [CharTwo.sub_eq_add]
  exact (add_assoc _ _ _).symm

theorem binaryFirst_array (s : ℕ) :
    ((binaryFirst K s).val : Mat K (s+3))=pairArray (s+3) (by omega) := by
  change ((binaryRotation K s).val : Mat K (s+3))*
    ((elementaryRoot K (s+3) false (⟨1,by omega⟩ : Fin (s+3)) 1).val : Mat K (s+3))=_
  rw [binaryRotation_array,short_one_array]
  rfl

end SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryPairElements
