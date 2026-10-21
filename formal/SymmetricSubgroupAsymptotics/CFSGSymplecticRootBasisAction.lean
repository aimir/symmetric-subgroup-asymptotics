import SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

/-! Actual simple symplectic root matrices propagate the standard basis
from the terminal pair to every coordinate, in every characteristic. -/
set_option autoImplicit false
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
variable (R : Type*) [CommRing R] (r : ℕ)

theorem positive_castSucc_basis (i : Fin r) :
    positive R (r + 1) i.castSucc *ᵥ Pi.single (Sum.inl i.succ) 1 =
      Pi.single (Sum.inl i.castSucc) 1 := by
  rw [Matrix.mulVec_single_one]
  funext x
  simp [positive, Matrix.col, Matrix.single, Pi.single_apply, eq_comm, Fin.ext_iff]

theorem negative_castSucc_basis (i : Fin r) :
    negative R (r + 1) i.castSucc *ᵥ Pi.single (Sum.inr i.succ) 1 =
      -Pi.single (Sum.inr i.castSucc) 1 := by
  rw [Matrix.mulVec_single_one]
  funext x
  simp [negative, positive, Matrix.col, Matrix.single, Pi.single_apply, eq_comm, Fin.ext_iff]

theorem negative_last_basis :
    negative R (r + 1) (Fin.last r) *ᵥ Pi.single (Sum.inl (Fin.last r)) 1 =
      Pi.single (Sum.inr (Fin.last r)) 1 := by
  rw [Matrix.mulVec_single_one]
  funext x
  simp [negative, positive, Matrix.col, Matrix.single,
    Pi.single_apply, eq_comm]

theorem terminal_root_product :
    positive R (r + 1) (Fin.last r) * negative R (r + 1) (Fin.last r) =
      Matrix.single (Sum.inl (Fin.last r)) (Sum.inl (Fin.last r)) 1 := by
  simp [positive, negative, Matrix.transpose_single]

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
