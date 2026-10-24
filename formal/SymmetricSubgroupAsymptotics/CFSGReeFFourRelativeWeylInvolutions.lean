import SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeSimpleWeyl

/-! Literal original-model inverses of the two relative reflections.
The characteristic-two Weyl squares are transported through the proved
injective original E6 matrix homomorphism. No equality of source words
is inferred from their lattice actions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeWeylInvolutions
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGFFourOriginalMiddleWords CFSGFFourE6RelativeWords CFSGSerreQuadraticMatrix
open CFSGTwistedE6GeckDiagramCovariance CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGSerreQuadraticWeylWord
open CFSGNormTwoGeckCharTwoFoldedBraid CFSGNormTwoGeckOrthogonalWeyl
open CFSGReeFFourFieldParameters CFSGReeFFourRelativeSimpleWeyl
local notation "F" => CFSGFFourSerreMatrices.realizationData
local notation "R" => CFSGTwistedE6GeckDiagramCovariance.rawData
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local instance : DecidableEq (Roots A) := Classical.decEq _

private theorem pair_square {G : Type*} [Group G] (a b : G)
    (hc : Commute a b) (ha : a^2=1) (hb : b^2=1) : (a*b)^2=1 := by
  rw [hc.mul_pow,ha,hb,mul_one]

theorem original_weyl_square (K : Type) [_root_.Field K] [Finite K] [CharP K 2]
    (i : Fin 4) : (weyl K i)^2=1 := by
  apply rawHom_injective K
  simp only [map_pow,map_one,rawHom_weyl]
  rw [foldedWeyl_eq_orbitWord]
  have hsquare (j : Fin 6) : (canonicalWeyl R K j)^2=1 :=
    canonicalWeyl_square_charTwo A hs hp E6Base E6Index K j
  fin_cases i
  · change (canonicalWeyl R K 0*(canonicalWeyl R K 5*1))^2=1
    rw [mul_one]
    exact pair_square _ _
      (orthogonal_weyls A hs hp E6Base E6Index K 0 5 (by rw [E6_cartan];decide))
      (hsquare 0) (hsquare 5)
  · change (canonicalWeyl R K 2*(canonicalWeyl R K 4*1))^2=1
    rw [mul_one]
    exact pair_square _ _
      (orthogonal_weyls A hs hp E6Base E6Index K 2 4 (by rw [E6_cartan];decide))
      (hsquare 2) (hsquare 4)
  · change (canonicalWeyl R K 3*1)^2=1
    rw [mul_one]
    exact hsquare 3
  · change (canonicalWeyl R K 1*1)^2=1
    rw [mul_one]
    exact hsquare 1

theorem original_weyl_inv (K : Type) [_root_.Field K] [Finite K] [CharP K 2]
    (i : Fin 4) : (weyl K i)⁻¹=weyl K i := by
  exact (eq_inv_of_mul_eq_one_left (show weyl K i*weyl K i=1 by
    simpa only [pow_two] using original_weyl_square K i)).symm

theorem outerRelativeWeyl_inv (m : ℕ) :
    (outerRelativeWeyl m)⁻¹=outerRelativeWeyl m := by
  simp only [outerRelativeWeyl,mul_inv_rev,original_weyl_inv]
  exact (outer_weyls_commute (Field m)).eq.symm

theorem middleRelativeWeyl_inv (m : ℕ) :
    (middleRelativeWeyl m)⁻¹=middleRelativeWeyl m := by
  simp only [middleRelativeWeyl,mul_inv_rev,original_weyl_inv]
  simpa only [mul_assoc] using (middle_weyl_braid (Field m)).symm

end SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeWeylInvolutions
