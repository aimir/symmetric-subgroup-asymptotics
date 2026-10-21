import SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
import SymmetricSubgroupAsymptotics.CFSGSymplecticRootBasisAction

/-! The common chain-root basis actions are reused literally. The two
fork products together isolate one original coordinate projection. -/
set_option autoImplicit false
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
variable (R : Type*) [CommRing R]

theorem chain_positive_eq_symplectic (r : ℕ) (i : Fin r) (hi : i.val + 1 < r) :
    positive R r i = CFSGSymplecticSerreMatrices.positive R r i := by
  simp only [positive, CFSGSymplecticSerreMatrices.positive, dif_pos hi]

theorem positive_castSucc_basis (r : ℕ) (i : Fin r) :
    positive R (r + 1) i.castSucc *ᵥ Pi.single (Sum.inl i.succ) 1 =
      Pi.single (Sum.inl i.castSucc) 1 := by
  rw [chain_positive_eq_symplectic R (r + 1) i.castSucc (by simp)]
  exact CFSGSymplecticSerreMatrices.positive_castSucc_basis R r i

theorem negative_castSucc_basis (r : ℕ) (i : Fin r) :
    negative R (r + 1) i.castSucc *ᵥ Pi.single (Sum.inr i.succ) 1 =
      -Pi.single (Sum.inr i.castSucc) 1 := by
  rw [negative, chain_positive_eq_symplectic R (r + 1) i.castSucc
    (by simp)]
  exact CFSGSymplecticSerreMatrices.negative_castSucc_basis R r i

theorem negative_castSucc_positive_basis (r : ℕ) (i : Fin r) :
    negative R (r + 1) i.castSucc *ᵥ Pi.single (Sum.inl i.castSucc) 1 =
      Pi.single (Sum.inl i.succ) 1 := by
  rw [Matrix.mulVec_single_one]
  funext x
  simp [negative, positive, Matrix.col, Matrix.single, Pi.single_apply,
    eq_comm, Fin.succ]

theorem negative_fork_basis (r : ℕ) :
    negative R (r + 2) (Fin.last (r + 1)) *ᵥ
        Pi.single (Sum.inl (Fin.last r).castSucc) 1 =
      Pi.single (Sum.inr (Fin.last (r + 1))) 1 := by
  rw [Matrix.mulVec_single_one]
  funext x
  simp [negative, positive, previous, Matrix.col, Matrix.single,
    Pi.single_apply, eq_comm, Fin.ext_iff]

theorem fork_chain_projection (r : ℕ) :
    (positive R (r + 2) (Fin.last (r + 1)) * negative R (r + 2) (Fin.last (r + 1))) *
        (positive R (r + 2) (Fin.last r).castSucc * negative R (r + 2) (Fin.last r).castSucc) =
      Matrix.single (Sum.inl (Fin.last r).castSucc) (Sum.inl (Fin.last r).castSucc) 1 := by
  let j : Fin (r + 2) := (Fin.last r).castSucc
  let k : Fin (r + 2) := Fin.last (r + 1)
  have hj : j.val + 1 < r + 2 := by simp [j]
  have hk : ¬k.val + 1 < r + 2 := by simp [k]
  have hne : j ≠ k := by
    intro he
    have h := congrArg Fin.val he
    dsimp [j, k] at h
    omega
  have hnext : (⟨j.val + 1, hj⟩ : Fin (r + 2)) = k := by apply Fin.ext; rfl
  have hprev : previous (r + 2) k = j := by
    apply Fin.ext
    simp [previous, j, k]
  have hE : positive R (r + 2) j =
      Matrix.single (Sum.inl j) (Sum.inl k) 1 - Matrix.single (Sum.inr k) (Sum.inr j) 1 := by
    rw [positive, dif_pos hj, hnext]
  have hB : positive R (r + 2) k =
      Matrix.single (Sum.inl j) (Sum.inr k) 1 - Matrix.single (Sum.inl k) (Sum.inr j) 1 := by
    rw [positive, dif_neg hk, hprev]
  change (positive R (r + 2) k * negative R (r + 2) k) *
      (positive R (r + 2) j * negative R (r + 2) j) =
      Matrix.single (Sum.inl j) (Sum.inl j) 1
  simp [negative, hE, hB, Matrix.transpose_sub, Matrix.transpose_single,
    sub_mul, mul_sub, add_mul, mul_add, hne, hne.symm]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
