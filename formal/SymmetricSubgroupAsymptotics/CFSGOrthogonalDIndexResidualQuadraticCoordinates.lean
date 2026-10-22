import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexResidualDecomposition
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPairProductQuadratic

/-! Exact quadratic and polar coordinates for the actual corrected
tail. The b*c term is retained, including in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexResidualQuadraticCoordinates
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDIndexResidualCorrection CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexPairProductQuadratic
variable (K : Type) [Field K]

theorem residualMap_polar (n : ℕ) (w : Index (n + 2) → K) (z z' : Index n → K) :
    (splitQuadraticForm K (n + 2)).polarBilin (residualMap K n w z) (residualMap K n w z') =
      (splitQuadraticForm K n).polarBilin z z' := by
  change QuadraticMap.polar (splitQuadraticForm K (n + 2))
      (residualMap K n w z) (residualMap K n w z') =
    QuadraticMap.polar (splitQuadraticForm K n) z z'
  simp only [QuadraticMap.polar, ← map_add, residualMap_quadratic]

theorem axes_polar_zero (n : ℕ) :
    (splitQuadraticForm K (n + 2)).polarBilin
      (Pi.single (Sum.inl (0 : Fin (n + 2))) 1)
      (Pi.single (Sum.inl (tailSecondIndex n)) 1) = 0 := by
  rw [positive_polar]
  simp only [Pi.single_apply, Sum.inr_ne_inl, if_false]

theorem quadratic_decomposition (n : ℕ) (w : Index (n + 2) → K)
    (hwQ : splitQuadraticForm K (n + 2) w = 0) (hw0 : w (Sum.inr 0) = 0)
    (hc : (splitQuadraticForm K (n + 2)).polarBilin w
      (Pi.single (Sum.inl (tailSecondIndex n)) 1) ≠ 0)
    (a b c : K) (z : Index n → K) :
    splitQuadraticForm K (n + 2)
      (a • Pi.single (Sum.inl (0 : Fin (n + 2))) 1 +
        b • Pi.single (Sum.inl (tailSecondIndex n)) 1 + c • w + residualMap K n w z) =
      b * c * (splitQuadraticForm K (n + 2)).polarBilin
        (Pi.single (Sum.inl (tailSecondIndex n)) 1) w + splitQuadraticForm K n z := by
  let Q := splitQuadraticForm K (n + 2)
  let u : Index (n + 2) → K := Pi.single (Sum.inl 0) 1
  let v : Index (n + 2) → K := Pi.single (Sum.inl (tailSecondIndex n)) 1
  have hu : Q u = 0 := positive_quadratic K (n + 2) 0
  have hv : Q v = 0 := positive_quadratic K (n + 2) (tailSecondIndex n)
  have huv : Q.polarBilin u v = 0 := axes_polar_zero K n
  have huw : Q.polarBilin u w = 0 := (positive_polar K (n + 2) 0 w).trans hw0
  have huj : Q.polarBilin u (residualMap K n w z) = 0 :=
    residualMap_perp_positive K n w z 0 (Or.inl rfl)
  have hvj : Q.polarBilin v (residualMap K n w z) = 0 :=
    residualMap_perp_positive K n w z _ (Or.inr rfl)
  have hwj : Q.polarBilin w (residualMap K n w z) = 0 := residualMap_perp_companion K n w hc z
  have hcross : Q.polarBilin (a • u + b • v + c • w) (residualMap K n w z) = 0 := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      huj, hvj, hwj, smul_zero, add_zero]
  have hadd := QuadraticMap.map_add (Q : (Index (n + 2) → K) → K)
    (a • u + b • v + c • w) (residualMap K n w z)
  change Q (_ + _) = Q _ + Q _ + Q.polarBilin _ _ at hadd
  rw [singular_shared_combination Q u v w hu hv hwQ huv huw a b c,
    hcross, add_zero] at hadd
  exact hadd.trans (congrArg (fun q => b * c * Q.polarBilin v w + q)
    (residualMap_quadratic K n w z))

theorem axis_pairing_decomposition (n : ℕ) (w : Index (n + 2) → K)
    (a b c : K) (z : Index n → K) :
    (splitQuadraticForm K (n + 2)).polarBilin (Pi.single (Sum.inl (tailSecondIndex n)) 1)
      (a • Pi.single (Sum.inl (0 : Fin (n + 2))) 1 +
        b • Pi.single (Sum.inl (tailSecondIndex n)) 1 + c • w + residualMap K n w z) =
      c * (splitQuadraticForm K (n + 2)).polarBilin
        (Pi.single (Sum.inl (tailSecondIndex n)) 1) w := by
  have hr : residualMap K n w z (Sum.inr (tailSecondIndex n)) = 0 :=
    (positive_polar K (n + 2) (tailSecondIndex n) _).symm.trans
      (residualMap_perp_positive K n w z _ (Or.inr rfl))
  rw [positive_polar, positive_polar]
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, Sum.inr_ne_inl,
    if_false, smul_eq_mul, mul_zero, zero_add, hr, add_zero]

theorem companion_pairing_decomposition (n : ℕ) (w : Index (n + 2) → K)
    (hwQ : splitQuadraticForm K (n + 2) w = 0) (hw0 : w (Sum.inr 0) = 0)
    (hc : (splitQuadraticForm K (n + 2)).polarBilin w
      (Pi.single (Sum.inl (tailSecondIndex n)) 1) ≠ 0)
    (a b c : K) (z : Index n → K) :
    (splitQuadraticForm K (n + 2)).polarBilin w
      (a • Pi.single (Sum.inl (0 : Fin (n + 2))) 1 +
        b • Pi.single (Sum.inl (tailSecondIndex n)) 1 + c • w + residualMap K n w z) =
      b * (splitQuadraticForm K (n + 2)).polarBilin w
        (Pi.single (Sum.inl (tailSecondIndex n)) 1) := by
  let Q := splitQuadraticForm K (n + 2)
  have hwu : Q.polarBilin w (Pi.single (Sum.inl (0 : Fin (n + 2))) 1) = 0 :=
    (QuadraticMap.polar_comm (Q : (Index (n + 2) → K) → K) _ _).trans
      ((positive_polar K (n + 2) 0 w).trans hw0)
  have hww : Q.polarBilin w w = 0 := by
    change QuadraticMap.polar Q w w = 0
    rw [Q.polar_self, hwQ, smul_zero]
  dsimp only [Q] at hwu hww
  simp only [map_add, map_smul, hwu, hww, residualMap_perp_companion K n w hc z,
    smul_eq_mul, mul_zero, zero_add, add_zero]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexResidualQuadraticCoordinates
