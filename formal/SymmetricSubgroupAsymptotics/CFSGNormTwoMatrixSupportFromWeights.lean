import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCartan
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckCartanDegreeAction
import SymmetricSubgroupAsymptotics.CFSGNormTwoSimpleWeightSeparation
import Mathlib.Tactic.LinearCombination

/-! Rational Cartan eigenrelations recover the literal INTEGER grading
of a matrix. This theorem is applied before reduction; only the resulting
entrywise integer zeros are transported to arbitrary characteristic. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoMatrixSupportFromWeights
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoSimpleWeightSeparation CFSGGradedMatrixSupport
open CFSGNormTwoGeckLatticeDegree CFSGNormTwoGeckCartanDegreeAction

/-- Pairings are compared in characteristic zero and then converted back
to equality of literal integer labels; there is no reduced-field weight
separation premise. -/
theorem supported_of_eigen
    {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight : I → Fin r → ℤ) (d : Fin r → ℤ) (M : Matrix I I ℚ)
    (heigen : ∀ a : Fin r,
      ⁅Matrix.diagonal (fun i =>
        (integerPairing A (weight i) (Pi.single a 1) : ℚ)), M⁆ =
        (integerPairing A d (Pi.single a 1) : ℚ) • M) :
    Supported weight (fun w => w + d) M := by
  intro i j hne
  by_contra hm
  apply hne
  apply label_eq_of_simple_pairings A hs hp
  intro a
  have h := congrArg (fun N : Matrix I I ℚ => N i j) (heigen a)
  simp only [Ring.lie_def, Matrix.sub_apply, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul] at h
  have hz : ((integerPairing A (weight i) (Pi.single a 1) : ℚ) -
      (integerPairing A (weight j) (Pi.single a 1) : ℚ) -
      (integerPairing A d (Pi.single a 1) : ℚ)) * M i j = 0 := by
    linear_combination h
  have hc := (mul_eq_zero.mp hz).resolve_right hm
  have hq : (integerPairing A (weight i) (Pi.single a 1) : ℚ) =
      (integerPairing A (weight j) (Pi.single a 1) : ℚ) +
      (integerPairing A d (Pi.single a 1) : ℚ) := by linarith
  have hi : integerPairing A (weight i) (Pi.single a 1) =
      integerPairing A (weight j) (Pi.single a 1) +
      integerPairing A d (Pi.single a 1) := by exact_mod_cast hq
  rw [integer_symmetric A hs (Pi.single a 1) (weight i),
    integer_symmetric A hs (Pi.single a 1) (weight j + d),
    map_add, LinearMap.add_apply]
  exact hi

/-- The actual coordinate-base Geck Cartan matrices satisfy the preceding
literal diagonal formula. This is a converse to the checked homogeneous
Cartan action, and uses the SAME original integer lattice. -/
theorem geck_supported_of_eigen
    {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (hd : ∀ i, A i i = 2) (hs : A.transpose = A)
    (hp : (rationalMatrix A).PosDef) (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (d : Fin r → ℤ)
    (M : Matrix ((coordinateBase A hd hs hp ho).support ⊕ Roots A)
      ((coordinateBase A hd hs hp ho).support ⊕ Roots A) ℚ)
    (heigen : ∀ i : Fin r,
      ⁅RootPairing.GeckConstruction.h (coordinateIndexEquiv A hd hs hp ho i), M⁆ =
        (integerPairing A d (Pi.single i 1) : ℚ) • M) :
    Supported (latticeWeight A hs hp (coordinateBase A hd hs hp ho))
      (fun w => w + d) M := by
  apply supported_of_eigen A hs hp _ d M
  intro i
  have h := heigen i
  rw [cartan_eq_character_diagonal A hs hp (coordinateBase A hd hs hp ho)] at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGNormTwoMatrixSupportFromWeights
