import SymmetricSubgroupAsymptotics.CFSGOrthogonalBScaledCartanCoordinates
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBFullMatrixCoordinates

/-! Integer doubled coordinates for the actual B coroot/root family.
The terminal coroot is not primitive in the full matrix lattice; the
factor two is retained uniformly, including in the root coordinates. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBDoubledFamilyCoordinates
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBOriginalRootCandidates
open CFSGOrthogonalBFullMatrixCoordinates CFSGOrthogonalBScaledCartanCoordinates
open CFSGOrthogonalBIntegralParityCoordinates
variable (R : Type*) [CommRing R] (r : ℕ)
local instance : DecidableEq (BasisIndex r) := Classical.decEq _

def familyMatrix : BasisIndex r → Mat R r
  | .inl i => cartan R r i
  | .inr z => matrix R r (.inr z)

def doubled : Mat R r →ₗ[R] (BasisIndex r → R) where
  toFun M j := match j with
    | .inl i => doubledCoordinates R r M i
    | .inr z => 2 * coordinates R r M (.inr z)
  map_add' M N := by
    funext j
    cases j <;> simp only [map_add, Pi.add_apply, mul_add]
  map_smul' a M := by
    funext j
    cases j <;> simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] <;> ring

private theorem pair_ne (ij : Pair r) : ij.val.1 ≠ ij.val.2 := by
  intro h
  have hv := congrArg (fun i : Fin r => i.val) h
  have hp := ij.property
  omega

theorem root_entry_ne (z : Bool × RootIndex r) :
    (entry r (.inr z)).1 ≠ (entry r (.inr z)).2 := by
  rcases z with ⟨b, z⟩
  cases b <;> rcases z with ij | (i | ij)
  · exact fun h => pair_ne r ij (Sum.inl.inj (Sum.inl.inj h))
  · simp [entry, pos, middle]
  · simp [entry, pos, neg]
  · exact fun h => (pair_ne r ij).symm (Sum.inl.inj (Sum.inl.inj h))
  · simp [entry, neg, middle]
  · simp [entry, pos, neg]

private theorem single_diagonal_zero {a b : Index r} (hab : a ≠ b)
    (v : R) (k : Index r) : Matrix.single a b v k k = 0 := by
  apply Matrix.single_apply_of_ne
  rintro ⟨ha, hb⟩
  exact hab (ha.trans hb.symm)

theorem root_matrix_diagonal (z : Bool × RootIndex r) (a : Index r) :
    matrix R r (.inr z) a a = 0 := by
  rcases z with ⟨b, z⟩
  cases b <;> rcases z with ij | (i | ij) <;>
    simp [matrix, CFSGOrthogonalBUniformRootMatrixArithmetic.difference,
      CFSGOrthogonalBUniformRootMatrixArithmetic.short,
      CFSGOrthogonalBUniformRootMatrixArithmetic.sumRoot,
      Matrix.transpose_apply, Matrix.sub_apply, single_diagonal_zero,
      pos, neg, middle, pair_ne r, ne_comm]

theorem doubledCoordinates_root (z : Bool × RootIndex r) :
    doubledCoordinates R r (matrix R r (.inr z)) = 0 := by
  funext i
  simp [doubledCoordinates, prefixTrace, positiveTrace, root_matrix_diagonal]

theorem rootCoordinates_cartan (i : Fin r) (z : Bool × RootIndex r) :
    coordinates R r (cartan R r i) (.inr z) = 0 := by
  obtain ⟨d, hd⟩ := cartan_isDiagonal R r i
  change sign R r (.inr z) * cartan R r i (entry r (.inr z)).1
    (entry r (.inr z)).2 = 0
  rw [hd, Matrix.diagonal_apply_ne _ (root_entry_ne r z), mul_zero]

theorem doubled_familyMatrix (j : BasisIndex r) :
    doubled R r (familyMatrix R r j) = (2 : R) • Pi.single j 1 := by
  funext k
  cases j with
  | inl i =>
    cases k with
    | inl a =>
      change doubledCoordinates R r (cartan R r i) a = _
      rw [doubledCoordinates_cartan]
      simp only [Pi.smul_apply, Pi.single_apply, Sum.inl.injEq]
    | inr z =>
      change 2 * coordinates R r (cartan R r i) (.inr z) = _
      rw [rootCoordinates_cartan]
      simp
  | inr z =>
    cases k with
    | inl a =>
      change doubledCoordinates R r (matrix R r (.inr z)) a = _
      rw [doubledCoordinates_root]
      simp
    | inr w =>
      change 2 * coordinates R r (matrix R r (.inr z)) (.inr w) = _
      rw [coordinates_matrix]
      simp only [Pi.single_apply, Pi.smul_apply, smul_eq_mul]

theorem doubled_integerCast (M : Mat ℤ r) :
    doubled ℚ r (CFSGSerreSquareZeroMatrix.integerCast (Index r) M) =
      fun j => (doubled ℤ r M j : ℚ) := by
  funext j
  cases j with
  | inl i =>
    simp [doubled, doubledCoordinates, prefixTrace, positiveTrace,
      CFSGSerreSquareZeroMatrix.integerCast, Matrix.map_apply]
  | inr z =>
    rcases z with ⟨b, z⟩
    cases b <;> rcases z with ij | (i | ij) <;>
      simp [doubled, coordinates, sign, CFSGSerreSquareZeroMatrix.integerCast,
        Matrix.map_apply]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBDoubledFamilyCoordinates
