import SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryCoxeterMatrix
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryStarArrays
import SymmetricSubgroupAsymptotics.CFSGTypeAMonomialRootAction

/-! Sparse root-array transport by the actual binary D Coxeter word.
The paired coordinate is retained in every conjugation formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryConjugation
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDBinaryCyclePermutation CFSGOrthogonalDBinaryCoxeterMatrix
open CFSGTypeAMonomialMatrices CFSGTypeAMonomialRootAction
variable {K : Type} [Field K] [CharP K 2]

def rootArray {r : ℕ} (a b : Index r) : Mat K r :=
  1 + Matrix.single a b 1 + Matrix.single (paired b) (paired a) 1

theorem rootArray_paired {r : ℕ} (a b : Index r) :
    rootArray (K := K) a b = rootArray (paired b) (paired a) := by
  cases a <;> cases b <;> simp only [rootArray, paired] <;> abel

theorem rootArray_same_side {r : ℕ} (a b : Fin r) :
    rootArray (K := K) (Sum.inl a) (Sum.inl b) =
      CFSGOrthogonalDBinaryRotationArrays.shortArray a b := rfl

theorem conjugation_single (s : ℕ) (a b : Index (s + 2)) :
    ((coxeterWeyl K (s + 1)).val : Mat K (s + 2)) * Matrix.single a b 1 *
      (↑((coxeterWeyl K (s + 1)).val⁻¹) : Mat K (s + 2)) =
      Matrix.single (cyclePerm s a) (cyclePerm s b) 1 := by
  have hm := monomial_mul_transvection (F := K) (cyclePerm s).symm (fun _ => 1) a b 1 one_ne_zero
  rw [← coxeter_binary_monomial (K := K) s] at hm
  simp only [Equiv.symm_symm, one_mul, div_one, Matrix.transvection] at hm
  have hc := congrArg (fun A : Mat K (s + 2) =>
    A * (↑((coxeterWeyl K (s + 1)).val⁻¹) : Mat K (s + 2))) hm
  have hh : (1 : Mat K (s + 2)) +
      ((coxeterWeyl K (s + 1)).val : Mat K (s + 2)) * Matrix.single a b 1 *
        (↑((coxeterWeyl K (s + 1)).val⁻¹) : Mat K (s + 2)) =
      1 + Matrix.single (cyclePerm s a) (cyclePerm s b) 1 := by
    simpa only [mul_add, add_mul, mul_one, one_mul, mul_assoc, Units.mul_inv] using hc
  exact add_left_cancel hh

theorem conjugation_rootArray (s : ℕ) (a b : Index (s + 2)) :
    ((coxeterWeyl K (s + 1)).val : Mat K (s + 2)) * rootArray a b *
      (↑((coxeterWeyl K (s + 1)).val⁻¹) : Mat K (s + 2)) =
      rootArray (cyclePerm s a) (cyclePerm s b) := by
  simp only [rootArray, mul_add, add_mul, mul_one, Units.mul_inv,
    conjugation_single, cyclePerm_paired]

theorem inverse_conjugation_rootArray (s : ℕ) (a b : Index (s + 2)) :
    (↑((coxeterWeyl K (s + 1)).val⁻¹) : Mat K (s + 2)) * rootArray a b *
      ((coxeterWeyl K (s + 1)).val : Mat K (s + 2)) =
      rootArray ((cyclePerm s).symm a) ((cyclePerm s).symm b) := by
  have hh := conjugation_rootArray (K := K) s ((cyclePerm s).symm a) ((cyclePerm s).symm b)
  simp only [Equiv.apply_symm_apply] at hh
  have hc := congrArg (fun A : Mat K (s + 2) =>
    (↑((coxeterWeyl K (s + 1)).val⁻¹) : Mat K (s + 2)) * A *
      ((coxeterWeyl K (s + 1)).val : Mat K (s + 2))) hh
  simpa only [mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, Units.mul_inv,
    one_mul, mul_one] using hc.symm

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryConjugation
