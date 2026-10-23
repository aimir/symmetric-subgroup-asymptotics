import SymmetricSubgroupAsymptotics.CFSGGTwoExceptionalCoefficients
import Mathlib.Data.ZMod.Basic

/-! A selected prime-coefficient certificate for the actual source-long
vector under the source short root. Only the constant field F3 is used
for kernel computation; explicit prime-ring transport gives the result
in EVERY characteristic-three field. No field elements are enumerated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGGTwoExceptionalCoefficientPilot
open CFSGGTwoSerreMatrices CFSGGTwoOriginalMatrixCoordinates
open CFSGGTwoExceptionalCoefficients

private theorem coefficient_one :
    column (ZMod 3) (sourceOperator (ZMod 3) false 0 1
      (matrixVectors (ZMod 3) (Sum.inl (false,1))))=0 := by
  decide +kernel

private theorem coefficient_two :
    column (ZMod 3) (sourceOperator (ZMod 3) false 0 2
      (matrixVectors (ZMod 3) (Sum.inl (false,1))))=0 := by
  decide +kernel

private theorem coefficient_three :
    column (ZMod 3) (sourceOperator (ZMod 3) false 0 3
      (matrixVectors (ZMod 3) (Sum.inl (false,1))))=
    rootMatrix (ZMod 3) false 1 *ᵥ
      column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (false,1))) := by
  decide +kernel

theorem prime_coefficients (k : Fin 4) :
    column (ZMod 3) (sourceOperator (ZMod 3) false 0 k
      (matrixVectors (ZMod 3) (Sum.inl (false,1))))=
    targetOperator (ZMod 3) false 0 k
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (false,1)))) := by
  fin_cases k
  · rfl
  · exact coefficient_one
  · exact coefficient_two
  · exact coefficient_three

theorem field_coefficients (K : Type) [Field K] [CharP K 3] (k : Fin 4) :
    column K (sourceOperator K false 0 k (matrixVectors K (Sum.inl (false,1))))=
    targetOperator K false 0 k (column K (matrixVectors K (Sum.inl (false,1)))) := by
  let f : ZMod 3 →+* K := ZMod.castHom (dvd_refl 3) K
  have hs := sourceOperator_map (ZMod 3) f false 0 k
    (matrixVectors (ZMod 3) (Sum.inl (false,1)))
  rw [map_matrixVectors] at hs
  have hb := column_map (ZMod 3) f (matrixVectors (ZMod 3) (Sum.inl (false,1)))
  rw [map_matrixVectors] at hb
  calc
    _=fun j => f (column (ZMod 3) (sourceOperator (ZMod 3) false 0 k
        (matrixVectors (ZMod 3) (Sum.inl (false,1)))) j) := by
      rw [←hs]
      exact column_map (ZMod 3) f _
    _=fun j => f (targetOperator (ZMod 3) false 0 k
        (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (false,1)))) j) :=
      congrArg (fun v : Index → ZMod 3 => fun j => f (v j)) (prime_coefficients k)
    _=_ := (targetOperator_map (ZMod 3) f false 0 k _).symm.trans
      (congrArg (targetOperator K false 0 k) hb.symm)

end SymmetricSubgroupAsymptotics.CFSGGTwoExceptionalCoefficientPilot
