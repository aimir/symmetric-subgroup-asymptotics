import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGeneralLinearForm
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBTailRootEmbedding

/-! The literal last-hyperbolic-pair diagonal homomorphism. Its matrix
is the actual GL determinant representative, and the original tail
embedding transports it exactly to the next last pair. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBLastDiagonal
open CFSGOrthogonalBSerreMatrices CFSGMatrixDiagonalBlockLift
open CFSGOrthogonalBGeneralLinearLift CFSGOrthogonalBGeneralLinearForm
open CFSGOrthogonalBTailCoordinates
variable (K : Type) [Field K]

def lastWeights (s : ℕ) (a : Kˣ) : Index (s + 1) → Kˣ
  | .inl (.inl i) => if i = Fin.last s then a else 1
  | .inl (.inr i) => if i = Fin.last s then a⁻¹ else 1
  | .inr _ => 1

def lastDiagonalHom (s : ℕ) : Kˣ →* (Mat K (s + 1))ˣ where
  toFun a := diagonalUnit (lastWeights K s a)
  map_one' := by
    apply Units.ext
    ext i j
    rcases i with (i | i) | ⟨⟩ <;> rcases j with (j | j) | ⟨⟩ <;>
      simp [diagonalUnit, lastWeights, Matrix.diagonal_apply, Matrix.one_apply]
  map_mul' a b := by
    apply Units.ext
    change Matrix.diagonal (fun i => (lastWeights K s (a * b) i : K)) =
      Matrix.diagonal (fun i => (lastWeights K s a i : K)) *
        Matrix.diagonal (fun i => (lastWeights K s b i : K))
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rcases i with (i | i) | ⟨⟩
    · by_cases hi : i = Fin.last s <;> simp [lastWeights, hi]
    · by_cases hi : i = Fin.last s <;> simp [lastWeights, hi, mul_comm]
    · simp [lastWeights]

theorem lastDiagonalHom_val (s : ℕ) (a : Kˣ) :
    (lastDiagonalHom K s a : Mat K (s + 1)) =
      Matrix.diagonal (fun i => (lastWeights K s a i : K)) := rfl

theorem lastDiagonalHom_eq_lift (s : ℕ) (a : Kˣ) :
    lastDiagonalHom K s a = generalLinearLift K (s + 1)
      (CFSGGeneralLinearDeterminantCosets.lastDiagonal K s a) := by
  apply Units.ext
  rw [lastDiagonalHom_val, generalLinearLift_val]
  ext i j
  rcases i with (i | i) | ⟨⟩ <;> rcases j with (j | j) | ⟨⟩
  all_goals simp only [CFSGGeneralLinearDeterminantCosets.lastDiagonal, diagonalUnit,
    lastWeights, Matrix.fromBlocks, Matrix.diagonal_apply]
  all_goals split_ifs <;> simp_all

theorem lastDiagonalHom_mem_special (s : ℕ) (a : Kˣ) :
    lastDiagonalHom K s a ∈ CFSGOrthogonalBSpecialFormGroup.specialFormUnits K (s + 1) := by
  rw [lastDiagonalHom_eq_lift]
  exact generalLinearLift_mem_special K (s + 1) _

theorem tailUnitHom_lastDiagonal (s : ℕ) (a : Kˣ) :
    tailUnitHom K (s + 1) (lastDiagonalHom K s a) = lastDiagonalHom K (s + 1) a := by
  apply Units.ext
  ext i j
  obtain ⟨i, rfl⟩ := (CFSGOrthogonalBTailCoordinates.tailEquiv (s + 1)).surjective i
  obtain ⟨j, rfl⟩ := (CFSGOrthogonalBTailCoordinates.tailEquiv (s + 1)).surjective j
  change tailMatrixHom K (s + 1) (lastDiagonalHom K s a : Mat K (s + 1))
      (CFSGOrthogonalBTailCoordinates.tailEquiv (s + 1) i)
      (CFSGOrthogonalBTailCoordinates.tailEquiv (s + 1) j) = _
  rw [tailMatrixHom_apply_equiv, lastDiagonalHom_val, lastDiagonalHom_val]
  have hl : Fin.last (s + 1) = (Fin.last s).succ := rfl
  have hw (x : Index (s + 1)) :
      lastWeights K (s + 1) a (tailIndex (s + 1) x) = lastWeights K s a x := by
    rcases x with (x | x) | ⟨⟩
    · change (if x.succ = Fin.last (s + 1) then a else 1) =
        (if x = Fin.last s then a else 1)
      simp only [hl, Fin.succ_inj]
    · change (if x.succ = Fin.last (s + 1) then a⁻¹ else 1) =
        (if x = Fin.last s then a⁻¹ else 1)
      simp only [hl, Fin.succ_inj]
    · rfl
  have hwE (x : Index (s + 1) ⊕ Fin 2) :
      lastWeights K (s + 1) a (CFSGOrthogonalBTailCoordinates.tailEquiv (s + 1) x) =
        Sum.elim (lastWeights K s a) (fun _ => 1) x := by
    rcases x with x | x
    · rw [CFSGOrthogonalBTailCoordinates.tailEquiv_inl]
      exact hw x
    · fin_cases x
      · change (if (0 : Fin (s + 1 + 1)) = Fin.last (s + 1) then a else 1) = 1
        rw [hl, if_neg (Ne.symm (Fin.succ_ne_zero _))]
      · change (if (0 : Fin (s + 1 + 1)) = Fin.last (s + 1) then a⁻¹ else 1) = 1
        rw [hl, if_neg (Ne.symm (Fin.succ_ne_zero _))]
  change Matrix.fromBlocks (Matrix.diagonal (fun x => (lastWeights K s a x : K))) 0 0
      (1 : Matrix (Fin 2) (Fin 2) K) i j =
    if CFSGOrthogonalBTailCoordinates.tailEquiv (s + 1) i =
        CFSGOrthogonalBTailCoordinates.tailEquiv (s + 1) j
      then (lastWeights K (s + 1) a (CFSGOrthogonalBTailCoordinates.tailEquiv (s + 1) i) : K)
      else 0
  simp only [(CFSGOrthogonalBTailCoordinates.tailEquiv (s + 1)).injective.eq_iff, hwE]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.diagonal_apply, Matrix.one_apply]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBLastDiagonal
