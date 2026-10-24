import SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleWords
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWordRootCommute
import SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleRootDegrees
import SymmetricSubgroupAsymptotics.CFSGIntegerDominantSupport

/-! The literal highest middle root commutes with the two original F4
middle simple axes. Its E6 root has pairings 1,0,1 with nodes 2,3,4;
this argument uses actual root-line membership in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleLongCentrality
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration
open CFSGFFourOriginalMiddleWords CFSGFFourSerreMatrices
open CFSGTwistedE6GeckDiagramCovariance CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoRootPairing
open CFSGNormTwoGeckWeylWordDegree CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGNormTwoCoordinateWordRootCommute CFSGE6GeckMiddleRootDegrees
open CFSGE6GeckMiddleAThreeCollecting CFSGIntegerMatrixPairing CFSGIntegerDominantSupport
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

private theorem vec_six_two (a b c d e f : ℤ) : ![a,b,c,d,e,f] (2 : Fin 6)=c := rfl
private theorem vec_six_three (a b c d e f : ℤ) : ![a,b,c,d,e,f] (3 : Fin 6)=d := rfl
private theorem vec_six_four (a b c d e f : ℤ) : ![a,b,c,d,e,f] (4 : Fin 6)=e := rfl

private theorem highest_pairing (j : Fin 6) (hj : j=2 ∨ j=3 ∨ j=4) :
    integerPairing A (wordRoot A hs hp E6Base E6Index [2,4] (E6Index 3)).val
      (E6Index j : Roots A).val=0 ∨
    integerPairing A (wordRoot A hs hp E6Base E6Index [2,4] (E6Index 3)).val
      (E6Index j : Roots A).val=1 := by
  have he : (E6Index j : Roots A).val=(Pi.single j 1 : Fin 6→ℤ) := rfl
  simp only [he,highest_root_degree,matrix_pairing_single_right]
  rcases hj with rfl|rfl|rfl <;>
    norm_num [Fin.sum_univ_succ,CartanMatrix.E₆,vec_six_two,vec_six_three,vec_six_four]

variable (K : Type) [Field K] [Finite K] [CharP K 2]

theorem middleLong_commute_one (r t : K) :
    Commute (middleLong K r) (modelRoot CartanMatrix.F₄ K false 1 t) := by
  apply Commute.of_map (rawHom_injective K)
  rw [rawHom_middleLong,rawHom_root,
    CFSGFFourE6FixedGeneratedGroup.folded_root_eq_orbitParameter]
  change Commute (highestMiddle K r)
    (canonicalRoot rawData K false 2 t*canonicalRoot rawData K false 4 t)
  have h2 := positive_word_commute_simple A hd hs hp ho K [2,4] 3 2
    (highest_pairing 2 (Or.inl rfl)) r t
  have h4 := positive_word_commute_simple A hd hs hp ho K [2,4] 3 4
    (highest_pairing 4 (Or.inr (Or.inr rfl))) r t
  simp only [canonicalWord,mul_one] at h2 h4
  exact h2.mul_right h4

theorem middleLong_commute_two (r t : K) :
    Commute (middleLong K r) (modelRoot CartanMatrix.F₄ K false 2 t) := by
  apply Commute.of_map (rawHom_injective K)
  rw [rawHom_middleLong,rawHom_root,
    CFSGFFourE6FixedGeneratedGroup.folded_root_eq_orbitParameter]
  change Commute (highestMiddle K r) (canonicalRoot rawData K false 3 t)
  have h3 := positive_word_commute_simple A hd hs hp ho K [2,4] 3 3
    (highest_pairing 3 (Or.inr (Or.inl rfl))) r t
  simpa only [canonicalWord,mul_one,highestMiddle] using h3

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleLongCentrality
