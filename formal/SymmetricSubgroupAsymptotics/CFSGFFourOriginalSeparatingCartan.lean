import SymmetricSubgroupAsymptotics.CFSGFFourOriginalFiftyTwoFamily
import SymmetricSubgroupAsymptotics.CFSGFFourIntegralRealization

/-! One actual integral Cartan test separates the 24 displayed positive
source weights. This supplies rational eigenvalue separation, without
asserting that the vectors span or that their images are nonzero. The
integral-basis/tensor-faithfulness obligation remains separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalSeparatingCartan
open CFSG.Models.Chevalley CFSGFFourOriginalFiftyTwoFamily
open CFSGSerreSignedRootWeights CFSGFFourSerreMatrices
open CFSGNormTwoRootPairing
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
local notation "A" => CartanMatrix.F₄

def coefficients : Fin 4→ℤ := ![192,383,569,347]

def testWeight (j:Fin 24) : ℤ := ∑i,coefficients i*simpleWeight i j

theorem testWeight_positive : ∀j:Fin 24,0<testWeight j := by decide +kernel

theorem testWeight_injective : Function.Injective testWeight := by decide +kernel

def testCartan : RationalLie A :=
  ∑i:Fin 4,(coefficients i:ℚ) • coroot A false i

theorem testCartan_weight (j:Fin 24) :
    ⁅testCartan,(rootVectors false j).val⁆=
      (testWeight j:ℚ) • (rootVectors false j).val := by
  rw [testCartan,sum_lie]
  simp only [smul_lie,rootVectors_weight,smul_smul]
  rw [←Finset.sum_smul]
  simp only [testWeight,Int.cast_sum,Int.cast_mul]

theorem image_testCartan_weight (j:Fin 24) :
    ⁅rationalRepresentation testCartan,rationalRepresentation ((rootVectors false j).val)⁆=
      (testWeight j:ℚ) • rationalRepresentation ((rootVectors false j).val) := by
  rw [←LieHom.map_lie,testCartan_weight,map_smul]

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalSeparatingCartan
