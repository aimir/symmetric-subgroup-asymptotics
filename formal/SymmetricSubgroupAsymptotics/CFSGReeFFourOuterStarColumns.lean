import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckDiagramCovariance
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateChainStarStrings
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldRootSteps
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylCharTwoRoots

/-! Four literal outer E6 root columns under the pinned middle A3 nodes.
Positive simple units add the next column and actual Weyl units swap
adjacent columns. This identifies one selected four-column slice, not
the whole Ree-fixed head or any irreducible quotient module. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOuterStarColumns
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoRootStrings
open CFSGExceptionalChainStarData CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGTwistedE6GeckDiagramCovariance
open CFSGNormTwoGeckColumns CFSGNormTwoGeckFieldRootSteps
open CFSGNormTwoGeckWeylCharTwoRoots CFSGNormTwoCoordinateChainStarStrings
open CFSGSerreQuadraticMatrix
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite

def leftStar : ChainStar A 3 where
  row := ![![1,0,0,0,0,0], ![1,0,1,0,0,0],
    ![1,0,1,1,0,0], ![1,0,1,1,1,0]]
  step := ![2,3,4]
  head := 0
  norm := by decide
  positive := by decide
  injective := by decide
  head_one := by decide
  pair := by decide
  successor := by decide
  simple_pair := by decide

def starVector (K : Type) [CommRing K] (k : Fin 4) : GeckIndex → K :=
  Pi.single (.inr (leftStar.root k).val) 1

private theorem not_negative (j : Fin 3) (k : Fin 4) :
    (leftStar.root k).val ≠ negativeIndex A hs hp (E6Index (leftStar.step j)) := by
  intro h
  have hh := congrArg (fun q : Roots A => q.val 0) h
  change (leftStar.root k).val.val 0 =
    (negativeIndex A hs hp (E6Index (leftStar.step j))).val 0 at hh
  rw [negative_val] at hh
  change leftStar.row k 0 = -((E6Index (leftStar.step j) : Roots A).val 0) at hh
  have hone : leftStar.row k 0 = 1 := leftStar.head_one k
  have hmid : (E6Index (leftStar.step j) : Roots A).val 0 = 0 := by
    fin_cases j <;> rfl
  rw [hone,hmid] at hh
  norm_num at hh

theorem simple_column (K : Type) [CommRing K] (j : Fin 3) (k : Fin 4) :
    (canonicalRoot rawData K false (leftStar.step j) 1 : Matrix GeckIndex GeckIndex K) *ᵥ
      starVector K k = starVector K k + if k=j.castSucc then starVector K j.succ else 0 := by
  by_cases hk : k=j.castSucc
  · subst k
    rw [if_pos rfl]
    have hadd : (rootPairing A hs hp).root (leftStar.root j.succ).val =
        (rootPairing A hs hp).root (E6Index (leftStar.step j)) +
          (rootPairing A hs hp).root (leftStar.root j.castSucc).val := by
      ext i
      change (leftStar.row j.succ i : ℚ) =
        ((Pi.single (leftStar.step j) (1 : ℤ) : Fin 6 → ℤ) i : ℚ) +
          (leftStar.row j.castSucc i : ℚ)
      rw [leftStar.successor]
      simp only [Pi.add_apply,Int.cast_add,add_comm]
    exact unit_add_step A hs hp E6Base E6Index K (leftStar.step j)
      (leftStar.root j.castSucc).val (leftStar.root j.succ).val (not_negative j j.castSucc) hadd
  · rw [if_neg hk,add_zero]
    apply unit_zero_step A hs hp E6Base E6Index K (leftStar.step j)
      (leftStar.root k).val (not_negative j k)
    rintro ⟨l,hl⟩
    have hpair := pairing_of_root_add A hs hp hl
    change integerPairing A (Pi.single (leftStar.step j) 1) (leftStar.row k) = -1 at hpair
    rw [integer_symmetric A hs] at hpair
    have hh := leftStar.simple_pair j k
    rw [if_neg hk] at hh
    split_ifs at hh <;> omega

theorem weyl_column (K : Type) [CommRing K] [CharP K 2] (j : Fin 3) (k : Fin 4) :
    (canonicalWeyl rawData K (leftStar.step j) : Matrix GeckIndex GeckIndex K) *ᵥ
      starVector K k = starVector K (Equiv.swap j.castSucc j.succ k) := by
  change (canonicalWeyl rawData K (leftStar.step j) : Matrix GeckIndex GeckIndex K) *ᵥ
      Pi.single (.inr (leftStar.root k).val) 1 =
    Pi.single (.inr (leftStar.root (Equiv.swap j.castSucc j.succ k)).val) 1
  rw [weyl_root_column A hs hp E6Base E6Index K]
  apply congrArg (fun q : Roots A => (Pi.single (.inr q) (1 : K) : GeckIndex → K))
  apply Subtype.ext
  change leftStar.row k - integerPairing A (leftStar.row k)
      (Pi.single (leftStar.step j) 1) • Pi.single (leftStar.step j) 1 = _
  exact congrArg (fun q : Roots A => q.val)
    (reflected_root A CartanMatrix.E₆_diag hs hp CartanMatrix.E₆_off_diag_nonpos leftStar j k)

end SymmetricSubgroupAsymptotics.CFSGReeFFourOuterStarColumns
