import SymmetricSubgroupAsymptotics.CFSGGTwoExceptionalPositiveShortCoefficients
import SymmetricSubgroupAsymptotics.CFSGGTwoExceptionalNegativeShortCoefficients
import SymmetricSubgroupAsymptotics.CFSGGTwoExceptionalPositiveLongCoefficients
import SymmetricSubgroupAsymptotics.CFSGGTwoExceptionalNegativeLongCoefficients

/-! All four signed divided-power coefficient identities on the actual
fourteen basis vectors, transported from the explicit prime-ring tables.
The field is arbitrary of characteristic three; no finiteness, cardinality,
or simplicity is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoExceptionalAllCoefficients
open CFSGGTwoSerreMatrices CFSGGTwoOriginalMatrixCoordinates
open CFSGGTwoExceptionalCoefficients

theorem prime_coefficients (neg : Bool) (i : Fin 2) (k : Fin 4) (j : BasisIndex) :
    column (ZMod 3) (sourceOperator (ZMod 3) neg i k (matrixVectors (ZMod 3) j))=
    targetOperator (ZMod 3) neg i k (column (ZMod 3) (matrixVectors (ZMod 3) j)) := by
  cases neg <;> fin_cases i
  · exact CFSGGTwoExceptionalPositiveShortCoefficients.prime_coefficients k j
  · exact CFSGGTwoExceptionalPositiveLongCoefficients.prime_coefficients k j
  · exact CFSGGTwoExceptionalNegativeShortCoefficients.prime_coefficients k j
  · exact CFSGGTwoExceptionalNegativeLongCoefficients.prime_coefficients k j

theorem field_coefficients (K : Type) [Field K] [CharP K 3]
    (neg : Bool) (i : Fin 2) (k : Fin 4) (j : BasisIndex) :
    column K (sourceOperator K neg i k (matrixVectors K j))=
    targetOperator K neg i k (column K (matrixVectors K j)) := by
  let f : ZMod 3 →+* K := ZMod.castHom (dvd_refl 3) K
  have hs := sourceOperator_map (ZMod 3) f neg i k (matrixVectors (ZMod 3) j)
  rw [map_matrixVectors] at hs
  have hb := column_map (ZMod 3) f (matrixVectors (ZMod 3) j)
  rw [map_matrixVectors] at hb
  calc
    _=fun a => f (column (ZMod 3) (sourceOperator (ZMod 3) neg i k
        (matrixVectors (ZMod 3) j)) a) := by
      rw [←hs]
      exact column_map (ZMod 3) f _
    _=fun a => f (targetOperator (ZMod 3) neg i k
        (column (ZMod 3) (matrixVectors (ZMod 3) j)) a) :=
      congrArg (fun v : Index → ZMod 3 => fun a => f (v a)) (prime_coefficients neg i k j)
    _=_ := (targetOperator_map (ZMod 3) f neg i k _).symm.trans
      (congrArg (targetOperator K neg i k) hb.symm)

end SymmetricSubgroupAsymptotics.CFSGGTwoExceptionalAllCoefficients
