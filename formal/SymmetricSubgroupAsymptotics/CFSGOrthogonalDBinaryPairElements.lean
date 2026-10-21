import SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryConjugation

/-! The binary D generating pair as literal elements of the original
elementary subgroup. Powers isolate a disjoint last chain root and an
A1 rotation on the first two hyperbolic pairs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped CharTwo
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryPairElements
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDBinaryRotationArrays
variable (K : Type) [Field K] [CharP K 2]

def firstIndex (s : ℕ) : Fin (s + 4) := 0
def secondIndex (s : ℕ) : Fin (s + 4) := ⟨1, by omega⟩
def penultimateIndex (s : ℕ) : Fin (s + 4) := (Fin.last (s + 2)).castSucc
def lastIndex (s : ℕ) : Fin (s + 4) := Fin.last (s + 3)

def binaryRotation (s : ℕ) : elementaryRootGroup K (s + 4) :=
  rootElement K (s + 4) false 0 1 * rootElement K (s + 4) true 0 1

def binaryFirst (s : ℕ) : elementaryRootGroup K (s + 4) :=
  binaryRotation K s * rootElement K (s + 4) false (penultimateIndex s) 1

def binarySecond (s : ℕ) : elementaryRootGroup K (s + 4) := coxeterWeyl K (s + 3)

theorem first_positive_array (s : ℕ) :
    ((rootElement K (s + 4) false 0 1).val : Mat K (s + 4)) =
      shortArray (firstIndex s) (secondIndex s) := by
  change 1 + (1 : K) • positive K (s + 4) 0 = _
  simp [positive, shortArray, firstIndex, secondIndex, sub_eq_add_neg] <;>
    (ext i j; simp only [Matrix.add_apply, Matrix.neg_apply, CharTwo.neg_eq] <;> abel)

theorem first_negative_array (s : ℕ) :
    ((rootElement K (s + 4) true 0 1).val : Mat K (s + 4)) =
      shortArray (secondIndex s) (firstIndex s) := by
  change 1 + (1 : K) • negative K (s + 4) 0 = _
  simp [negative, positive, shortArray, firstIndex, secondIndex, sub_eq_add_neg,
    Matrix.transpose_sub, Matrix.transpose_single] <;>
    (ext i j; simp only [Matrix.add_apply, Matrix.neg_apply, CharTwo.neg_eq] <;> abel)

theorem last_chain_array (s : ℕ) :
    ((rootElement K (s + 4) false (penultimateIndex s) 1).val : Mat K (s + 4)) =
      shortArray (penultimateIndex s) (lastIndex s) := by
  have hi : (penultimateIndex s).val + 1 < s + 4 := by
    change s + 2 + 1 < s + 4
    omega
  have hnext : (⟨(penultimateIndex s).val + 1, hi⟩ : Fin (s + 4)) = lastIndex s := by
    apply Fin.ext
    rfl
  change 1 + (1 : K) • positive K (s + 4) (penultimateIndex s) = _
  rw [positive, dif_pos hi, hnext]
  simp [shortArray, sub_eq_add_neg] <;>
    (ext i j; simp only [Matrix.add_apply, Matrix.neg_apply, CharTwo.neg_eq] <;> abel)

theorem binaryRotation_array (s : ℕ) :
    ((binaryRotation K s).val : Mat K (s + 4)) =
      rotationArray (firstIndex s) (secondIndex s) := by
  change ((rootElement K (s + 4) false 0 1).val : Mat K (s + 4)) *
    ((rootElement K (s + 4) true 0 1).val : Mat K (s + 4)) = _
  rw [first_positive_array, first_negative_array]
  rfl

theorem binaryFirst_array (s : ℕ) :
    ((binaryFirst K s).val : Mat K (s + 4)) =
      pairArray (firstIndex s) (secondIndex s) (penultimateIndex s) (lastIndex s) := by
  change ((binaryRotation K s).val : Mat K (s + 4)) *
    ((rootElement K (s + 4) false (penultimateIndex s) 1).val : Mat K (s + 4)) = _
  rw [binaryRotation_array, last_chain_array]
  rfl

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryPairElements
