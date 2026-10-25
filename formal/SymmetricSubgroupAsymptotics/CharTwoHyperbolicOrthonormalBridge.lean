import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalSignedForm
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! A displayed trace-one change of basis for the ACTUAL signed-reversal
Hermitian form in dimension four, in characteristic two. Each reversed
coordinate pair uses columns (1,a), (1,a+1). No classification or
orthonormal-basis existence theorem is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CharTwoHyperbolicOrthonormalBridge
open CFSGTwistedANaturalMatrices
variable {K : Type*} [Field K]

/-- Columns0/1 occupy the original pair0/3; columns2/3 occupy pair1/2. -/
def basisMatrix (a : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1,1,0,0; 0,0,1,1; 0,0,a,a+1; a,a+1,0,0]

def inverseMatrix (a : K) : Matrix (Fin 4) (Fin 4) K :=
  !![a+1,0,0,-1; -a,0,0,1; 0,a+1,-1,0; 0,-a,1,0]

theorem inverse_identities (a : K) :
    basisMatrix a*inverseMatrix a=1 ∧ inverseMatrix a*basisMatrix a=1 := by
  constructor <;> funext i j <;> fin_cases i <;> fin_cases j <;>
    simp [basisMatrix, inverseMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

def basisUnit (a : K) : (Matrix (Fin 4) (Fin 4) K)ˣ :=
  ⟨basisMatrix a,inverseMatrix a,(inverse_identities a).1,(inverse_identities a).2⟩

/-- The original signed-reversal matrix itself, with its original labels. -/
theorem signed_reversal_charTwo [CharP K 2] :
    (signedReversalUnit K 3 : Mat K 3)=
      !![0,0,0,1; 0,0,1,0; 0,1,0,0; 1,0,0,0] := by
  have hneg : (-1 : K)=1 := CharTwo.neg_eq 1
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [signedReversalUnit_apply, signWeight, hneg, Fin.rev]

/-- A trace-one parameter gives an isometry FROM the identity form TO
that same signed-reversal form, not a replacement named form model. -/
theorem pullback_signed_reversal [CharP K 2] (sigma : K ≃+* K)
    (a : K) (ha : sigma a+a=1) :
    ((basisUnit a).val.map sigma).transpose*
      (signedReversalUnit K 3 : Mat K 3)*(basisUnit a).val=1 := by
  have hs : sigma a=1-a := eq_sub_iff_add_eq.mpr ha
  have htwo : (2 : K)=0 := CharP.cast_eq_zero K 2
  have hthree : (3 : K)=1 := by
    calc
      (3 : K)=(2 : K)+1 := by ring
      _=1 := by rw [htwo,zero_add]
  rw [signed_reversal_charTwo]
  change ((basisMatrix a).map sigma).transpose*
    !![0,0,0,1; 0,0,1,0; 0,1,0,0; 1,0,0,0]*basisMatrix a=1
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [basisMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.map_apply, Matrix.transpose_apply, hs] <;>
    ring_nf <;> simp_all [hthree]

end SymmetricSubgroupAsymptotics.CharTwoHyperbolicOrthonormalBridge
