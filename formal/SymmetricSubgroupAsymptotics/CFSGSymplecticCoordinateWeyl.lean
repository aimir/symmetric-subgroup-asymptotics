import SymmetricSubgroupAsymptotics.CFSGSymplecticCoordinateLongRoots
import SymmetricSubgroupAsymptotics.CFSGMatrixPairRotationMonomial
import SymmetricSubgroupAsymptotics.CFSGMonomialUnitCoordinates

/-! The actual quarter-turn in any natural symplectic coordinate pair. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

def coordinateWeylUnit (K : Type) [Field K] (r : ℕ) (i : Fin (r + 1)) :
    (Mat K (r + 1))ˣ :=
  coordinateLongUnit K r false i (-1) * coordinateLongUnit K r true i 1 *
    coordinateLongUnit K r false i (-1)

theorem coordinateWeylUnit_mem (K : Type) [Field K] (r : ℕ) (i : Fin (r + 1)) :
    coordinateWeylUnit K r i ∈ elementaryRootGroup K (r + 1) :=
  (elementaryRootGroup K (r + 1)).mul_mem
    ((elementaryRootGroup K (r + 1)).mul_mem
      (coordinateLongUnit_mem K r false i _) (coordinateLongUnit_mem K r true i _))
    (coordinateLongUnit_mem K r false i _)

theorem coordinateWeylUnit_val (K : Type) [Field K] (r : ℕ) (i : Fin (r + 1)) :
    (coordinateWeylUnit K r i : Mat K (r + 1)) =
      CFSGMatrixPairRotation.rotation K (Sum.inl i) (Sum.inr i) := by
  change Matrix.transvection (Sum.inl i) (Sum.inr i) (-1) *
    Matrix.transvection (Sum.inr i) (Sum.inl i) 1 *
    Matrix.transvection (Sum.inl i) (Sum.inr i) (-1) = _
  have hn : (Matrix.single (Sum.inl i) (Sum.inr i) (-1 : K) : Mat K (r + 1)) =
      (-1 : K) • Matrix.single (Sum.inl i) (Sum.inr i) 1 := by
    simp only [Matrix.smul_single, smul_eq_mul, mul_one]
  simp only [Matrix.transvection, hn, neg_one_smul, ← sub_eq_add_neg]
  exact CFSGMatrixPairRotation.word_eq_rotation K _ _ (by intro h; cases h)

theorem coordinateWeylUnit_monomial (K : Type) [Field K] (r : ℕ) (i : Fin (r + 1)) :
    (coordinateWeylUnit K r i : Mat K (r + 1)) =
      CFSGTypeAMonomialMatrices.monomial (Equiv.swap (Sum.inl i) (Sum.inr i))
        (fun x => if x = Sum.inl i then -1 else 1) := by
  rw [coordinateWeylUnit_val]
  exact CFSGMatrixPairRotation.rotation_monomial K _ _ (by intro h; cases h)

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
