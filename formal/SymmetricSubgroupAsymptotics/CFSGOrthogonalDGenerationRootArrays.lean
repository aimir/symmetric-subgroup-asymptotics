import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationInitialRootMatrices

/-! Parameter-sensitive D root arrays and their sparse commutators.
These are matrix identities over every field; no root-sign cancellation
or ambient classical-group identification is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationRootArrays
open Matrix CFSGOrthogonalDSerreMatrices
open CFSGOrthogonalDGenerationInitialElements CFSGOrthogonalDGenerationForkTorus
open CFSGOrthogonalDGenerationInitialRootMatrices
variable {K : Type} [Field K] {r : ℕ}

def chainArray (i j : Fin r) (a : K) : Mat K r :=
  1 + Matrix.single (Sum.inl i) (Sum.inl j) a - Matrix.single (Sum.inr j) (Sum.inr i) a

def plusArray (i j : Fin r) (a : K) : Mat K r :=
  1 + Matrix.single (Sum.inl i) (Sum.inr j) a - Matrix.single (Sum.inl j) (Sum.inr i) a

def minusArray (i j : Fin r) (a : K) : Mat K r := (plusArray i j a).transpose

theorem chain_plus_commute (i j k : Fin r) (hij : i ≠ j) (hik : i ≠ k)
    (a b : K) :
    chainArray j i a * plusArray j k b = plusArray j k b * chainArray j i a := by
  simp [chainArray, plusArray, mul_add, add_mul, mul_sub, sub_mul,
    hij, hik, Ne.symm hij, Ne.symm hik]
  abel

theorem chain_plus_commutator (i j k : Fin r) (hij : i ≠ j) (_hik : i ≠ k) (hjk : j ≠ k)
    (a b : K) :
    chainArray i j a * plusArray j k b * chainArray i j (-a) * plusArray j k (-b) =
      plusArray i k (a * b) := by
  simp [chainArray, plusArray, mul_add, add_mul, mul_sub, sub_mul,
    hij, hjk, Ne.symm hij, Ne.symm hjk] <;>
    (ext x y; simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
      Matrix.single_apply]; split_ifs <;> ring)

theorem plus_minus_commutator (i j k : Fin r) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a b : K) :
    plusArray i k a * minusArray j k b * plusArray i k (-a) * minusArray j k (-b) =
      chainArray i j (a * b) := by
  simp [chainArray, plusArray, minusArray, Matrix.transpose_add, Matrix.transpose_sub,
    Matrix.transpose_one, Matrix.transpose_single, mul_add, add_mul, mul_sub, sub_mul,
    hij, hik, hjk, Ne.symm hij, Ne.symm hik, Ne.symm hjk] <;>
    (ext x y; simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
      Matrix.single_apply]; split_ifs <;> ring)

theorem initial_lines_commute (s : ℕ) (a b : K) :
    Commute (CFSGOrthogonalDGenerationInitialElements.initialShortRoot K s a)
      (CFSGOrthogonalDGenerationInitialElements.initialStarRoot K s false b) := by
  change initialShortRoot K s a * initialStarRoot K s false b =
    initialStarRoot K s false b * initialShortRoot K s a
  apply Subtype.ext
  apply Units.ext
  change ((initialShortRoot K s a).val : Mat K (s + 4)) *
      ((initialStarRoot K s false b).val : Mat K (s + 4)) =
    ((initialStarRoot K s false b).val : Mat K (s + 4)) *
      ((initialShortRoot K s a).val : Mat K (s + 4))
  rw [initialShortRoot_coe, initialStarRoot_coe]
  change chainArray (second s) (0 : Fin (s + 4)) a * plusArray (second s) (last (s + 2)) b =
    plusArray (second s) (last (s + 2)) b * chainArray (second s) (0 : Fin (s + 4)) a
  exact chain_plus_commute 0 (second s) (last (s + 2))
    (Ne.symm (second_ne_zero s)) (Ne.symm (last_ne_zero s)) a b

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationRootArrays
