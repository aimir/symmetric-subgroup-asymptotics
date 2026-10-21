import SymmetricSubgroupAsymptotics.CFSGSymplecticCoordinateShortRoots
import SymmetricSubgroupAsymptotics.CFSGSymplecticCoordinateWeyl

/-! Every individual off-diagonal symmetric upper or lower shear is
an actual root line in the same elementary C model. No factor two is
divided out, so these statements include characteristic two. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
open CFSGActualMatrixRootLines

def symmetricRootMatrix (K : Type) [Field K] (r : ℕ) (side : Bool)
    (i j : Fin (r + 1)) : Mat K (r + 1) :=
  Matrix.single (coordinatePoint r side i) (coordinatePoint r (!side) j) 1 +
    Matrix.single (coordinatePoint r side j) (coordinatePoint r (!side) i) 1

theorem coordinateWeyl_short_upper (K : Type) [Field K] (r : ℕ)
    (i j : Fin (r + 1)) (hij : i ≠ j) :
    (coordinateWeylUnit K r j : Mat K (r + 1)) * coordinateShortMatrix K r i j *
      (↑((coordinateWeylUnit K r j)⁻¹) : Mat K (r + 1)) =
      symmetricRootMatrix K r false i j := by
  let d : Index (r + 1) → K := fun x => if x = Sum.inl j then -1 else 1
  have hc (a b : Index (r + 1)) (hd : d ((Equiv.swap (Sum.inl j) (Sum.inr j)).symm b) ≠ 0) :=
    CFSGMonomialUnitCoordinates.conjugation_single (coordinateWeylUnit K r j)
      (Equiv.swap (Sum.inl j) (Sum.inr j)) d (coordinateWeylUnit_monomial K r j) a b hd
  unfold coordinateShortMatrix
  rw [mul_sub, sub_mul, hc _ _ (by dsimp [d]; split_ifs <;> simp), hc _ _ (by dsimp [d]; split_ifs <;> simp)]
  simp [d, symmetricRootMatrix, coordinatePoint, Equiv.swap_apply_def, hij, hij.symm,
    sub_eq_add_neg]

theorem coordinateWeyl_short_lower (K : Type) [Field K] (r : ℕ)
    (i j : Fin (r + 1)) (hij : i ≠ j) :
    (coordinateWeylUnit K r i : Mat K (r + 1)) * coordinateShortMatrix K r i j *
      (↑((coordinateWeylUnit K r i)⁻¹) : Mat K (r + 1)) =
      symmetricRootMatrix K r true i j := by
  let d : Index (r + 1) → K := fun x => if x = Sum.inl i then -1 else 1
  have hc (a b : Index (r + 1)) (hd : d ((Equiv.swap (Sum.inl i) (Sum.inr i)).symm b) ≠ 0) :=
    CFSGMonomialUnitCoordinates.conjugation_single (coordinateWeylUnit K r i)
      (Equiv.swap (Sum.inl i) (Sum.inr i)) d (coordinateWeylUnit_monomial K r i) a b hd
  unfold coordinateShortMatrix
  rw [mul_sub, sub_mul, hc _ _ (by dsimp [d]; split_ifs <;> simp), hc _ _ (by dsimp [d]; split_ifs <;> simp)]
  simp [d, symmetricRootMatrix, coordinatePoint, Equiv.swap_apply_def, hij, hij.symm,
    sub_eq_add_neg]

theorem symmetric_root_line (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (side : Bool) (i j : Fin (r + 1)) (hij : i ≠ j) :
    HasRootLine (elementaryRootGroup K (r + 1)) (symmetricRootMatrix K r side i j) := by
  have hshort := coordinate_short_root_line K r hr i j hij
  cases side with
  | false =>
    apply hasRootLine_conjugate _ (coordinateWeylUnit K r j)
      (coordinateWeylUnit_mem K r j) _ _ 1 one_ne_zero _ hshort
    simpa only [one_smul] using coordinateWeyl_short_upper K r i j hij
  | true =>
    apply hasRootLine_conjugate _ (coordinateWeylUnit K r i)
      (coordinateWeylUnit_mem K r i) _ _ 1 one_ne_zero _ hshort
    simpa only [one_smul] using coordinateWeyl_short_lower K r i j hij

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
