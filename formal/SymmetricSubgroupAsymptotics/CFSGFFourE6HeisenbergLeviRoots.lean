import SymmetricSubgroupAsymptotics.CFSGTwistedE6HeisenbergStableRootFamilies
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootPairCommute

/-! Actual highest-root centralization by every head-zero E6 root.
This includes the two signs of each folded Levi generator. The paired
central directions are checked to have the orthogonal A3 orientation;
no quadratic-column formula or Levi representation is assumed here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6HeisenbergLeviRoots
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGExceptionalCartanPositiveDefinite CFSGTwistedE6HeisenbergStableRootFamilies
open CFSGNormTwoGeckColumns CFSGNormTwoCoordinateSelectedRootElement
local instance fFourLeviRootsDecidableEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

def pairPick : Fin 3 → Fin 10 := ![2,3,6]

theorem paired_roots_orthogonal (i : Fin 3) :
    integerPairing A (configuration.x (pairPick i)) (configuration.x (partner (pairPick i))) = 0 ∧
    integerPairing A (configuration.y (pairPick i)) (configuration.y (partner (pairPick i))) = 0 := by
  fin_cases i <;> decide

theorem highest_pairing_eq_head (v : Fin 6 → ℤ) :
    integerPairing A configuration.z v = v 1 := by
  have hb (i : Fin 6) : integerPairing A configuration.z (Pi.single i (1 : ℤ)) =
      if i=1 then 1 else 0 := by
    fin_cases i <;> decide
  have hv : v = ∑ i : Fin 6, v i • Pi.single i (1 : ℤ) := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero]
    simp
  calc
    integerPairing A configuration.z v =
        integerPairing A configuration.z (∑ i : Fin 6, v i • Pi.single i (1 : ℤ)) :=
      congrArg (integerPairing A configuration.z) hv
    _ = ∑ i : Fin 6, v i * (if i=1 then 1 else 0) := by
      simp only [map_sum, map_smul, smul_eq_mul, hb]
    _ = v 1 := by simp

theorem head_zero_parameter_commutes_highest (K : Type) [CommRing K]
    (k : Roots A) (hk : k.val 1 = 0) (a b : K) :
    Commute (selectedRootElement A hd hs hp ho K k a)
      (selectedRootElement A hd hs hp ho K configuration.zRoot.val b) := by
  have hp0 : integerPairing A k.val configuration.z = 0 :=
    (integer_symmetric A hs k.val configuration.z).trans
      ((highest_pairing_eq_head k.val).trans hk)
  exact CFSGNormTwoCoordinateRootPairCommute.pair_commute A hd hs hp ho K
    k configuration.zRoot.val (Or.inl hp0) a b

theorem head_zero_parameter_commutes_opposite (K : Type) [CommRing K]
    (k : Roots A) (hk : k.val 1 = 0) (a b : K) :
    Commute (selectedRootElement A hd hs hp ho K k a)
      (selectedRootElement A hd hs hp ho K (negativeIndex A hs hp configuration.zRoot.val) b) := by
  have hp0 : integerPairing A k.val configuration.z = 0 :=
    (integer_symmetric A hs k.val configuration.z).trans
      ((highest_pairing_eq_head k.val).trans hk)
  have hn : integerPairing A k.val
      (negativeIndex A hs hp configuration.zRoot.val).val = 0 := by
    rw [negative_val, map_neg]
    change -(integerPairing A k.val configuration.z) = 0
    rw [hp0, neg_zero]
  exact CFSGNormTwoCoordinateRootPairCommute.pair_commute A hd hs hp ho K
    k (negativeIndex A hs hp configuration.zRoot.val) (Or.inl hn) a b

end SymmetricSubgroupAsymptotics.CFSGFFourE6HeisenbergLeviRoots
