import SymmetricSubgroupAsymptotics.CFSGSymplecticCoordinateShortRoots
import SymmetricSubgroupAsymptotics.CFSGMatrixDiagonalBlockLift

/-! A literal SL₂ Borel cell embedded in any rank at least two. Its
natural middle block is injectively parameterized by Kˣ × K, and its
symplectic block lift is an actual word in the original elementary C
model. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
open CFSGMatrixDiagonalBlockLift CFSGMonomialUnitRootAction

def borelSecond (r : ℕ) (hr : 0 < r) : Fin (r + 1) := ⟨1, Nat.succ_lt_succ hr⟩

theorem borelSecond_ne_zero (r : ℕ) (hr : 0 < r) : borelSecond r hr ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  change 1 = 0 at hv
  omega

def borelDiagonal (K : Type) [Field K] (r : ℕ) (hr : 0 < r) (g : Kˣ) :
    Fin (r + 1) → Kˣ := fun i => if i = 0 then g else if i = borelSecond r hr then g⁻¹ else 1

def borelCellMiddle (K : Type) [Field K] (r : ℕ) (hr : 0 < r) (g : Kˣ) (t : K) :
    (Matrix (Fin (r + 1)) (Fin (r + 1)) K)ˣ :=
  diagonalUnit (borelDiagonal K r hr g) *
    transvectionUnit 0 (borelSecond r hr) (borelSecond_ne_zero r hr).symm t

theorem borelCellMiddle_zero_zero (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (g : Kˣ) (t : K) :
    (borelCellMiddle K r hr g t : Matrix (Fin (r + 1)) (Fin (r + 1)) K) 0 0 = g := by
  change (Matrix.diagonal (fun i => (borelDiagonal K r hr g i : K)) *
    Matrix.transvection 0 (borelSecond r hr) t) 0 0 = _
  simp [Matrix.diagonal_mul, Matrix.transvection, Matrix.one_apply,
    Matrix.single_apply, borelDiagonal, borelSecond_ne_zero r hr, Ne.symm (borelSecond_ne_zero r hr)]

theorem borelCellMiddle_zero_one (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (g : Kˣ) (t : K) :
    (borelCellMiddle K r hr g t : Matrix (Fin (r + 1)) (Fin (r + 1)) K)
      0 (borelSecond r hr) = (g : K) * t := by
  change (Matrix.diagonal (fun i => (borelDiagonal K r hr g i : K)) *
    Matrix.transvection 0 (borelSecond r hr) t) 0 (borelSecond r hr) = _
  simp [Matrix.diagonal_mul, Matrix.transvection, Matrix.one_apply,
    Matrix.single_apply, borelDiagonal, borelSecond_ne_zero r hr, Ne.symm (borelSecond_ne_zero r hr)]

theorem borelCellMiddle_injective (K : Type) [Field K] (r : ℕ) (hr : 0 < r) :
    Function.Injective (fun p : Kˣ × K => borelCellMiddle K r hr p.1 p.2) := by
  rintro ⟨g, t⟩ ⟨h, u⟩ he
  have hg := congrArg (fun A : (Matrix (Fin (r + 1)) (Fin (r + 1)) K)ˣ =>
    (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) 0 0) he
  simp only [borelCellMiddle_zero_zero] at hg
  have hgh : g = h := Units.ext hg
  subst h
  have ht := congrArg (fun A : (Matrix (Fin (r + 1)) (Fin (r + 1)) K)ˣ =>
    (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) 0 (borelSecond r hr)) he
  simp only [borelCellMiddle_zero_one] at ht
  have htu := mul_left_cancel₀ (Units.ne_zero g) ht
  subst u
  rfl

private theorem diagonal_lift_borel (K : Type) [Field K] (r : ℕ) (hr : 0 < r) (g : Kˣ) :
    lift (diagonalUnit (borelDiagonal K r hr g)) =
      coordinateTorusUnit K r 0 g * coordinateTorusUnit K r (borelSecond r hr) g⁻¹ := by
  apply Units.ext
  change Matrix.fromBlocks (Matrix.diagonal (fun i => (borelDiagonal K r hr g i : K))) 0 0
    (Matrix.diagonal (fun i => (↑((borelDiagonal K r hr g i)⁻¹) : K))).transpose = _
  rw [show (↑(coordinateTorusUnit K r 0 g *
      coordinateTorusUnit K r (borelSecond r hr) g⁻¹) : Mat K (r + 1)) =
      (coordinateTorusUnit K r 0 g : Mat K (r + 1)) *
        (coordinateTorusUnit K r (borelSecond r hr) g⁻¹ : Mat K (r + 1)) from rfl,
    coordinateTorusUnit_val, coordinateTorusUnit_val, Matrix.diagonal_mul_diagonal]
  have hne := borelSecond_ne_zero r hr
  ext x y
  cases x <;> cases y <;>
    simp [Matrix.fromBlocks, Matrix.diagonal_apply, borelDiagonal,
      coordinateTorusDiagonal, eq_comm] <;>
    split_ifs <;> simp_all

private theorem diagonal_lift_short (K : Type) [Field K] (r : ℕ)
    (i j : Fin (r + 1)) (hij : i ≠ j) (t : K) :
    lift (transvectionUnit i j hij t) = coordinateShortUnit K r i j hij t := by
  apply Units.ext
  rw [coordinateShortUnit_val]
  change Matrix.fromBlocks (Matrix.transvection i j t) 0 0
      (Matrix.transvection i j (-t)).transpose = _
  ext x y
  cases x <;> cases y <;>
    simp [Matrix.fromBlocks, Matrix.transvection, coordinateShortMatrix,
      Matrix.one_apply, Matrix.single_apply, smul_sub, Matrix.smul_single, smul_eq_mul] <;>
    split_ifs <;> simp_all

theorem borelCellMiddle_lift_mem (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (g : Kˣ) (t : K) :
    lift (borelCellMiddle K r hr g t) ∈ elementaryRootGroup K (r + 1) := by
  rw [borelCellMiddle, map_mul, diagonal_lift_borel, diagonal_lift_short]
  exact (elementaryRootGroup K (r + 1)).mul_mem
    ((elementaryRootGroup K (r + 1)).mul_mem
      (coordinateTorusUnit_mem K r 0 g) (coordinateTorusUnit_mem K r (borelSecond r hr) g⁻¹))
    (coordinateShortUnit_mem K r hr 0 (borelSecond r hr) (borelSecond_ne_zero r hr).symm t)

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
