import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckCharTwoFoldedBraid
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleRootCovariance

/-! Two actual exceptional-fixed relative Weyl words in the original F4
Model. The middle four-term relation is transported from the same E6
A3 matrices by the checked injective original homomorphism. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeSimpleWeyl
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGFFourOriginalMiddleWords CFSGFFourE6RelativeWords CFSGSerreQuadraticMatrix
open CFSGTwistedE6GeckDiagramCovariance CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGSerreQuadraticWeylWord
open CFSGNormTwoGeckCharTwoFoldedBraid CFSGNormTwoGeckOrthogonalWeyl
open CFSGReeFFourFieldParameters CFSGReeFFourOriginalAutomorphism CFSGReeFFourMiddleRootCovariance
local notation "F" => CFSGFFourSerreMatrices.realizationData
local notation "R" => CFSGTwistedE6GeckDiagramCovariance.rawData
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local instance : DecidableEq (Roots A) := Classical.decEq _

theorem outer_weyls_commute (K : Type) [_root_.Field K] [Finite K] [CharP K 2] :
    Commute (weyl K 0) (weyl K 3) := by
  apply Commute.of_map (rawHom_injective K)
  simp only [rawHom_weyl]
  have h0 : canonicalWeyl F K 0=canonicalWeyl R K 0*canonicalWeyl R K 5 := by
    have h := foldedWeyl_eq_orbitWord K 0
    change canonicalWeyl F K 0=canonicalWord R K [0,5] at h
    simpa only [canonicalWord,mul_one] using h
  have h3 : canonicalWeyl F K 3=canonicalWeyl R K 1 := by
    have h := foldedWeyl_eq_orbitWord K 3
    change canonicalWeyl F K 3=canonicalWord R K [1] at h
    simpa only [canonicalWord,mul_one] using h
  rw [h0,h3]
  exact (orthogonal_weyls A hs hp E6Base E6Index K 0 1 (by rw [E6_cartan];decide)).mul_left
    (orthogonal_weyls A hs hp E6Base E6Index K 5 1 (by rw [E6_cartan];decide))

theorem middle_weyl_braid (K : Type) [_root_.Field K] [Finite K] [CharP K 2] :
    weyl K 1*weyl K 2*weyl K 1*weyl K 2=
      weyl K 2*weyl K 1*weyl K 2*weyl K 1 := by
  apply rawHom_injective K
  simp only [map_mul,rawHom_weyl]
  have h1 : canonicalWeyl F K 1=canonicalWeyl R K 2*canonicalWeyl R K 4 := by
    have h := foldedWeyl_eq_orbitWord K 1
    change canonicalWeyl F K 1=canonicalWord R K [2,4] at h
    simpa only [canonicalWord,mul_one] using h
  have h2 : canonicalWeyl F K 2=canonicalWeyl R K 3 := by
    have h := foldedWeyl_eq_orbitWord K 2
    change canonicalWeyl F K 2=canonicalWord R K [3] at h
    simpa only [canonicalWord,mul_one] using h
  rw [h1,h2]
  apply canonical_folded_a3_braid A hs hp E6Base E6Index K 2 3 4
  · change integerPairing A (Pi.single 2 (1:ℤ)) (Pi.single 3 1)= -1
    rw [integerPairing,Matrix.toBilin'_single]
    decide
  · change integerPairing A (Pi.single 4 (1:ℤ)) (Pi.single 3 1)= -1
    rw [integerPairing,Matrix.toBilin'_single]
    decide
  · rw [E6_cartan]
    decide

def outerRelativeWeyl (m : ℕ) : Model CartanMatrix.F₄ (Field m) :=
  weyl (Field m) 0*weyl (Field m) 3

def middleRelativeWeyl (m : ℕ) : Model CartanMatrix.F₄ (Field m) :=
  weyl (Field m) 1*weyl (Field m) 2*weyl (Field m) 1*weyl (Field m) 2

theorem outerRelativeWeyl_fixed (m : ℕ) :
    reeAutomorphism m (outerRelativeWeyl m)=outerRelativeWeyl m := by
  simp only [outerRelativeWeyl,map_mul,ree_weyl]
  change weyl (Field m) 3*weyl (Field m) 0=weyl (Field m) 0*weyl (Field m) 3
  exact (outer_weyls_commute (Field m)).eq.symm

theorem middleRelativeWeyl_fixed (m : ℕ) :
    reeAutomorphism m (middleRelativeWeyl m)=middleRelativeWeyl m := by
  simp only [middleRelativeWeyl,map_mul,ree_weyl]
  change weyl (Field m) 2*weyl (Field m) 1*weyl (Field m) 2*weyl (Field m) 1=
    weyl (Field m) 1*weyl (Field m) 2*weyl (Field m) 1*weyl (Field m) 2
  exact (middle_weyl_braid (Field m)).symm

end SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeSimpleWeyl
