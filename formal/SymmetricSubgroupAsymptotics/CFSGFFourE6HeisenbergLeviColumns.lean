import SymmetricSubgroupAsymptotics.CFSGFFourE6HeisenbergLeviRoots
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalRootColumn
import SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveRootUnits
import SymmetricSubgroupAsymptotics.CFSGFFourE6NegativeRootUnits

/-! Both signs of every actual folded Levi simple parameter fix the
highest and opposite highest E6 root columns pointwise. These are
literal original folded matrix actions, proved through their actual
E6 parameter factors. No central quadratic-column identity is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6HeisenbergLeviColumns
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGExceptionalCartanPositiveDefinite CFSGExceptionalNormTwoBases
open CFSGSerreQuadraticMatrix
open CFSGFFourSerreMatrices CFSGFFourE6PositiveRootUnits CFSGFFourE6NegativeRootUnits
open CFSGTwistedE6HeisenbergStableRootFamilies CFSGFFourE6HeisenbergLeviRoots
local instance fFourLeviColumnsRootsDecidableEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite

private theorem e6_parameter_fixes (K : Type) [CommRing K] (neg : Bool)
    (j : Fin 6) (k : Roots A)
    (hjk : integerPairing A (E6Index j : Roots A).val k.val=0) (t : K) :
    (canonicalRoot e6Data K neg j t : Matrix Index Index K) *ᵥ Pi.single (.inr k) 1 =
      Pi.single (.inr k) 1 := by
  cases neg
  · exact CFSGNormTwoGeckOrthogonalRootColumn.positive_fixes_orthogonal_column
      A hs hp E6Base E6Index K j k hjk t
  · exact CFSGNormTwoGeckOrthogonalRootColumn.negative_fixes_orthogonal_column
      A hs hp E6Base E6Index K j k hjk t

private theorem folded_fixes (K : Type) [CommRing K] (neg : Bool) (i : Fin 3)
    (k : Roots A) (hk : ∀ j : Fin 6, j≠1 → integerPairing A (E6Index j : Roots A).val k.val=0)
    (t : K) :
    (canonicalRoot realizationData K neg i.castSucc t : Matrix Index Index K) *ᵥ
      Pi.single (.inr k) 1 = Pi.single (.inr k) 1 := by
  have he (j : Fin 6) (hj : j≠1) := e6_parameter_fixes K neg j k (hk j hj) t
  cases neg
  · rw [folded_positive_root]
    fin_cases i
    · change ((canonicalRoot e6Data K false 0 t : Matrix Index Index K) *
          (canonicalRoot e6Data K false 5 t : Matrix Index Index K)) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, he 5 (by decide), he 0 (by decide)]
    · change ((canonicalRoot e6Data K false 2 t : Matrix Index Index K) *
          (canonicalRoot e6Data K false 4 t : Matrix Index Index K)) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, he 4 (by decide), he 2 (by decide)]
    · exact he 3 (by decide)
  · rw [folded_negative_root]
    fin_cases i
    · change ((canonicalRoot e6Data K true 0 t : Matrix Index Index K) *
          (canonicalRoot e6Data K true 5 t : Matrix Index Index K)) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, he 5 (by decide), he 0 (by decide)]
    · change ((canonicalRoot e6Data K true 2 t : Matrix Index Index K) *
          (canonicalRoot e6Data K true 4 t : Matrix Index Index K)) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, he 4 (by decide), he 2 (by decide)]
    · exact he 3 (by decide)

private theorem simple_highest_pairing (j : Fin 6) (hj : j≠1) :
    integerPairing A (E6Index j : Roots A).val configuration.z = 0 := by
  change integerPairing A (Pi.single j (1 : ℤ)) configuration.z = 0
  rw [integer_symmetric A hs, highest_pairing_eq_head]
  simp [Pi.single_apply,Ne.symm hj]

theorem folded_levi_fixes_highest (K : Type) [CommRing K] (neg : Bool) (i : Fin 3) (t : K) :
    (canonicalRoot realizationData K neg i.castSucc t : Matrix Index Index K) *ᵥ
      Pi.single (.inr configuration.zRoot.val) 1 = Pi.single (.inr configuration.zRoot.val) 1 := by
  apply folded_fixes K neg i configuration.zRoot.val
  intro j hj
  exact simple_highest_pairing j hj

theorem folded_levi_fixes_opposite (K : Type) [CommRing K] (neg : Bool) (i : Fin 3) (t : K) :
    (canonicalRoot realizationData K neg i.castSucc t : Matrix Index Index K) *ᵥ
      Pi.single (.inr (negativeIndex A hs hp configuration.zRoot.val)) 1 =
        Pi.single (.inr (negativeIndex A hs hp configuration.zRoot.val)) 1 := by
  apply folded_fixes K neg i (negativeIndex A hs hp configuration.zRoot.val)
  intro j hj
  rw [negative_val,map_neg]
  change -(integerPairing A (E6Index j : Roots A).val configuration.z)=0
  rw [simple_highest_pairing j hj,neg_zero]

end SymmetricSubgroupAsymptotics.CFSGFFourE6HeisenbergLeviColumns
