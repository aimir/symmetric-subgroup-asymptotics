import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalA2PairStabilizer
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSignedRootColumns

/-! The exact three root labels in a simple A2 reflection. These are
literal integral-lattice equalities, independent of coefficient fields. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateA2ReflectionLabels
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinatePositivePairCollecting
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

open CFSGNormTwoGeckColumns CFSGNormTwoGeckSignedRootColumns
open CFSGNormTwoGeckWeylWordDegree

def simple_pairing_eq_neg_one (j k : Fin r) (hjk : A j k = -1) :
    integerPairing A (s₀ j : Roots A).val (s₀ k : Roots A).val = -1 := by
  change integerPairing A (Pi.single j 1) (Pi.single k 1) = -1
  simpa only [integerPairing, Matrix.toBilin'_single] using hjk

 def simplePairSum (j k : Fin r) (hjk : A j k = -1) : Roots A :=
  sumRoot A hs (s₀ j) (s₀ k) (simple_pairing_eq_neg_one A hd hs hp ho j k hjk)

 theorem reflect_simple_self (j : Fin r) :
    wordRoot A hs hp b₀ s₀ [j] (s₀ j) = negativeIndex A hs hp (s₀ j) := rfl

 theorem reflect_adjacent_simple (j k : Fin r) (hjk : A j k = -1) :
    wordRoot A hs hp b₀ s₀ [j] (s₀ k) = simplePairSum A hd hs hp ho j k hjk := by
  apply Subtype.ext
  change ((rootPairing A hs hp).reflectionPerm (s₀ j) (s₀ k)).val = _
  rw [reflection_val]
  have hkj : integerPairing A (s₀ k : Roots A).val (s₀ j : Roots A).val = -1 := by
    rw [integer_symmetric A hs]
    exact simple_pairing_eq_neg_one A hd hs hp ho j k hjk
  rw [hkj]
  change (s₀ k : Roots A).val - (-1 : ℤ) • (s₀ j : Roots A).val =
    (s₀ j : Roots A).val + (s₀ k : Roots A).val
  module

 theorem reflect_simple_sum (j k : Fin r) (hjk : A j k = -1) :
    wordRoot A hs hp b₀ s₀ [j] (simplePairSum A hd hs hp ho j k hjk) = (s₀ k : Roots A) := by
  have he := reflect_adjacent_simple A hd hs hp ho j k hjk
  change (rootPairing A hs hp).reflectionPerm (s₀ j) (s₀ k) = _ at he
  change (rootPairing A hs hp).reflectionPerm (s₀ j)
    (simplePairSum A hd hs hp ho j k hjk) = (s₀ k : Roots A)
  rw [← he, RootPairing.reflectionPerm_self]

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateA2ReflectionLabels
