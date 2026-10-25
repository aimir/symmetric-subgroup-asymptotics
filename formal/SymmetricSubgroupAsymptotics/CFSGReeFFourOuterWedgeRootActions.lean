import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterWedgeRootData
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCharTwoSimpleConjugation
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePairCommute
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSimpleRootParametrization
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWordRootElementSign

/-! Genuine root-unit A3 actions on the six selected node-1 E6 roots.
The positive action adds two disjoint strings; Weyl transport has its
integral signs removed only after characteristic two is installed.
Nothing here asserts fixedness of an individual root parameter. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOuterWedgeRootActions
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGReeFFourOuterStarColumns
open CFSGReeFFourOuterWedgeRootData CFSGTwistedE6GeckDiagramCovariance
open CFSGNormTwoCoordinateSelectedRootElement CFSGSerreQuadraticMatrix
open CFSGNormTwoCoordinateCharTwoSimpleConjugation
open CFSGNormTwoCoordinatePositivePairCommute CFSGNormTwoCoordinateSimpleRootParametrization
open CFSGNormTwoCoordinateWordRootElementSign
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

def parameter (K : Type) [CommRing K] (k : Fin 6) (a : K) :
    (Matrix GeckIndex GeckIndex K)ˣ :=
  selectedRootElement A hd hs hp ho K (wedgeRoot k).val a

private theorem commute_conjugate {G : Type*} [Group G] (u x : G)
    (h : Commute u x) : u*x*u⁻¹=x := by
  rw [h.eq,mul_assoc,mul_inv_cancel,mul_one]

theorem simple_raise (K : Type) [CommRing K] [CharP K 2]
    (j : Fin 3) (b : Fin 2) (t a : K) :
    canonicalRoot rawData K false (leftStar.step j) t*parameter K (raiseSource j b) a*
      (canonicalRoot rawData K false (leftStar.step j) t)⁻¹=
      parameter K (raiseSource j b) a*parameter K (raiseTarget j b) (t*a) := by
  have hb : raiseSource j b=raiseSource j 0 ∨ raiseSource j b=raiseSource j 1 := by
    fin_cases b
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hpair : integerPairing A (wedgeRoot (raiseSource j b)).val.val
      (E6Index (leftStar.step j) : Roots A).val= -1 := by
    simp only [simple_pair_shape,if_pos hb]
  have h := simple_positive_conjugate A hd hs hp ho K
    (wedgeRoot (raiseSource j b)).val (wedgeRoot (raiseSource j b)).property
    (leftStar.step j) hpair t a
  rw [CFSGReeFFourOuterWedgeRootData.raised_root j b hpair] at h
  exact h

theorem simple_fixed (K : Type) [CommRing K] (j : Fin 3) (k : Fin 6)
    (hk : ¬(k=raiseSource j 0 ∨ k=raiseSource j 1)) (t a : K) :
    canonicalRoot rawData K false (leftStar.step j) t*parameter K k a*
      (canonicalRoot rawData K false (leftStar.step j) t)⁻¹=parameter K k a := by
  have hsimple : ∀i,0≤(E6Index (leftStar.step j) : Roots A).val i := by
    change ∀i,0≤(Pi.single (leftStar.step j) (1:ℤ) : Fin 6 → ℤ) i
    intro i
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  have hpair : integerPairing A (wedgeRoot k).val.val
      (E6Index (leftStar.step j) : Roots A).val=0 ∨
      integerPairing A (wedgeRoot k).val.val
        (E6Index (leftStar.step j) : Roots A).val=1 := by
    simp only [simple_pair_shape,if_neg hk]
    by_cases ht : k=raiseTarget j 0 ∨ k=raiseTarget j 1
    · rw [if_pos ht]
      exact Or.inr rfl
    · rw [if_neg ht]
      exact Or.inl rfl
  obtain ⟨e,he,hroot⟩ := selected_simple_root_sign A hd hs hp ho (leftStar.step j)
  have hsquare : (e:K)*(e:K)=1 := by rcases he with rfl|rfl <;> norm_num
  have hc := positive_pair_commute A hd hs hp ho K (wedgeRoot k).val
    (E6Index (leftStar.step j)) (wedgeRoot k).property hsimple hpair a ((e:K)*t)
  have hr : selectedRootElement A hd hs hp ho K
      (E6Index (leftStar.step j)) ((e:K)*t)=
        canonicalRoot rawData K false (leftStar.step j) t := by
    calc
      _ = canonicalRoot rawData K false (leftStar.step j) ((e:K)*((e:K)*t)) :=
        hroot K ((e:K)*t)
      _ = _ := by rw [←mul_assoc,hsquare,one_mul]
  rw [hr] at hc
  exact commute_conjugate _ _ hc.symm

theorem weyl_conjugate (K : Type) [CommRing K] [CharP K 2]
    (j : Fin 3) (k : Fin 6) (a : K) :
    canonicalWeyl rawData K (leftStar.step j)*parameter K k a*
      (canonicalWeyl rawData K (leftStar.step j))⁻¹=parameter K (wedgeSwap j k) a := by
  obtain ⟨e,he,hw⟩ := word_selected_root_sign A hd hs hp ho
    [leftStar.step j] (wedgeRoot k).val
  have hsign : (e:K)=1 := by
    rcases he with rfl|rfl <;> simp only [Int.cast_one,Int.cast_neg,CharTwo.neg_eq]
  have h := hw K a
  have href : CFSGNormTwoGeckWeylWordDegree.wordRoot A hs hp
      (coordinateBase A hd hs hp ho) (coordinateIndexEquiv A hd hs hp ho)
      [leftStar.step j] (wedgeRoot k).val=(wedgeRoot (wedgeSwap j k)).val :=
    CFSGReeFFourOuterWedgeRootData.reflected_root j k
  rw [href] at h
  simpa only [CFSGSerreQuadraticWeylWord.canonicalWord,mul_one,hsign,one_mul] using h

end SymmetricSubgroupAsymptotics.CFSGReeFFourOuterWedgeRootActions
