import SymmetricSubgroupAsymptotics.CFSGTwistedA2HighestRootUnits
import SymmetricSubgroupAsymptotics.CFSGTypeAElementaryMatrices
import Mathlib.Tactic.FieldSimp

/-! Actual determinant-one natural diagonal words for rank-two twisted A.
Two adjacent four-root words give diag(z,σz/z,(σz)^-1), with no assumed
membership in a full unitary group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2DiagonalTorus
open CFSGTwistedANaturalMatrices CFSGSerreSquareZeroMatrix
variable (K : Type) [Field K]

def adjacentDiagonal (i : Fin 2) (z : K) : NaturalElementary K 2 :=
  elementaryRoot K (naturalRootUnit K 2) false i (z - 1) *
    elementaryRoot K (naturalRootUnit K 2) true i 1 *
    elementaryRoot K (naturalRootUnit K 2) false i (z⁻¹ - 1) *
    elementaryRoot K (naturalRootUnit K 2) true i (-z)

theorem adjacentDiagonal_val (i : Fin 2) (z : K) (hz : z ≠ 0) :
    ((adjacentDiagonal K i z).val : Mat K 2) =
      Matrix.diagonal (fun k => if k = i.castSucc then z else if k = i.succ then z⁻¹ else 1) := by
  have hij : i.castSucc ≠ i.succ := by
    intro h
    have hv := congrArg (fun j : Fin 3 => j.val) h
    change i.val = i.val + 1 at hv
    omega
  change (1 + (z - 1) • positive K 2 i) * (1 + (1 : K) • negative K 2 i) *
    (1 + (z⁻¹ - 1) • positive K 2 i) * (1 + (-z) • negative K 2 i) = _
  simpa only [positive, negative, Matrix.transpose_single, Matrix.smul_single,
    smul_eq_mul, mul_one, Matrix.transvection] using
      CFSGTypeAElementaryMatrices.diagonal_pair hij z hz

def torusNatural (σ : K ≃+* K) (z : K) : NaturalElementary K 2 :=
  adjacentDiagonal K 0 z * adjacentDiagonal K 1 (σ z)

def torusWeights (σ : K ≃+* K) (z : K) : Fin 3 → K := ![z, σ z / z, (σ z)⁻¹]

theorem torusNatural_val (σ : K ≃+* K) (z : K) (hz : z ≠ 0) :
    ((torusNatural K σ z).val : Mat K 2) = Matrix.diagonal (torusWeights K σ z) := by
  change ((adjacentDiagonal K 0 z).val : Mat K 2) *
    ((adjacentDiagonal K 1 (σ z)).val : Mat K 2) = _
  rw [adjacentDiagonal_val K 0 z hz,
    adjacentDiagonal_val K 1 (σ z) ((map_ne_zero σ).mpr hz), Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  fin_cases i <;> simp [torusWeights, div_eq_mul_inv, mul_comm]

def torusInverseWeights (σ : K ≃+* K) (z : K) : Fin 3 → K := ![z⁻¹, z / σ z, σ z]

def torusUnit (σ : K ≃+* K) (z : K) (hz : z ≠ 0) : (Mat K 2)ˣ where
  val := Matrix.diagonal (torusWeights K σ z)
  inv := Matrix.diagonal (torusInverseWeights K σ z)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    fin_cases i <;> simp [torusWeights, torusInverseWeights, hz, (map_ne_zero σ).mpr hz]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    fin_cases i <;> simp [torusWeights, torusInverseWeights, hz, (map_ne_zero σ).mpr hz]

theorem torusNatural_unit (σ : K ≃+* K) (z : K) (hz : z ≠ 0) :
    (torusNatural K σ z).val = torusUnit K σ z hz := by
  apply Units.ext
  exact torusNatural_val K σ z hz

end SymmetricSubgroupAsymptotics.CFSGTwistedA2DiagonalTorus
