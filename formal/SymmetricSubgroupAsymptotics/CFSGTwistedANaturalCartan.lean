import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
import SymmetricSubgroupAsymptotics.CFSGDiagonalMatrixLie
import Mathlib.Data.Matrix.Cartan

/-! Symbolic Cartan and mixed-root identities for the natural rank-r A
matrices. All ranks use the same sparse matrix-unit proofs; no rank census
or model equivalence is involved. -/

set_option autoImplicit false
set_option Elab.async false

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
variable (R : Type*) [CommRing R] (r : ℕ)

theorem cartan_eq (i : Fin r) :
    cartan R r i = Matrix.single i.castSucc i.castSucc 1 -
      Matrix.single i.succ i.succ 1 := by
  simp [cartan, positive, negative, Ring.lie_def]

theorem cartan_eq_diagonal (i : Fin r) :
    cartan R r i = Matrix.diagonal
      (Pi.single i.castSucc (1 : R) - Pi.single i.succ 1) := by
  simpa only [← Matrix.diagonal_single, Matrix.diagonal_sub] using cartan_eq R r i

theorem cartan_transpose (i : Fin r) : (cartan R r i).transpose = cartan R r i := by
  simp only [cartan_eq, Matrix.transpose_sub, Matrix.transpose_single]

theorem cartan_cartan (i j : Fin r) : ⁅cartan R r i, cartan R r j⁆ = 0 := by
  rw [cartan_eq_diagonal, cartan_eq_diagonal]
  exact sub_eq_zero.mpr (Matrix.commute_diagonal _ _).eq

theorem EF (i j : Fin r) :
    ⁅positive R r i, negative R r j⁆ = if i = j then cartan R r i else 0 := by
  by_cases hij : i = j
  · subst j
    exact (if_pos rfl).symm
  · have hs : i.succ ≠ j.succ := fun h => hij (Fin.succ_inj.mp h)
    have hc : i.castSucc ≠ j.castSucc := fun h => hij (Fin.castSucc_inj.mp h)
    simp [Ring.lie_def, positive, negative, hs, Ne.symm hc, hij]

def weight (r : ℕ) (i : Fin r) : Fin (r + 1) → ℤ :=
  Pi.single i.castSucc 1 - Pi.single i.succ 1

theorem weight_difference (i j : Fin r) :
    weight r i j.castSucc - weight r i j.succ = CartanMatrix.A r i j := by
  simp only [weight, Pi.sub_apply, Pi.single_apply, Fin.ext_iff,
    Fin.val_castSucc, Fin.val_succ, CartanMatrix.A, Matrix.of_apply]
  split_ifs <;> omega

theorem HE_integer (i j : Fin r) :
    ⁅cartan ℤ r i, positive ℤ r j⁆ = CartanMatrix.A r i j • positive ℤ r j := by
  rw [cartan_eq_diagonal]
  change ⁅Matrix.diagonal (weight r i), positive ℤ r j⁆ = _
  simp only [positive]
  rw [CFSGDiagonalMatrixLie.diagonal_lie_single]
  simp only [mul_one, one_mul, weight_difference,
    Matrix.smul_single, zsmul_eq_mul, Int.cast_id]

theorem HF_integer (i j : Fin r) :
    ⁅cartan ℤ r i, negative ℤ r j⁆ = -(CartanMatrix.A r i j • negative ℤ r j) := by
  have ht := congrArg Matrix.transpose (HE_integer r i j)
  have hh : ⁅negative ℤ r j, cartan ℤ r i⁆ = CartanMatrix.A r i j • negative ℤ r j := by
    simpa only [Ring.lie_def, Matrix.transpose_sub, Matrix.transpose_mul,
      cartan_transpose, Matrix.transpose_smul, negative] using ht
  exact (lie_skew (cartan ℤ r i) (negative ℤ r j)).symm.trans (congrArg Neg.neg hh)

theorem HE (i j : Fin r) :
    ⁅cartan R r i, positive R r j⁆ = CartanMatrix.A r i j • positive R r j := by
  have hh := congrArg (Int.castRingHom R).mapMatrix (HE_integer r i j)
  simpa only [Ring.lie_def, map_sub, map_mul, map_zsmul,
    map_cartan, map_positive] using hh

theorem HF (i j : Fin r) :
    ⁅cartan R r i, negative R r j⁆ = -(CartanMatrix.A r i j • negative R r j) := by
  have hh := congrArg (Int.castRingHom R).mapMatrix (HF_integer r i j)
  simpa only [Ring.lie_def, map_sub, map_mul, map_neg, map_zsmul,
    map_cartan, map_negative] using hh

end SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
