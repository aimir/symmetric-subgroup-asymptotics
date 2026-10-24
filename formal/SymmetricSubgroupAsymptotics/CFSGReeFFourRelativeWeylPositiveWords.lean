import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOutsideWordConjugation
import SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleRootDegrees

/-! Selected positive root factors under the two ReeF4 relative words.
The outer word avoids every middle coordinate; the middle word avoids
the three outer coordinates. Only these bounded families are asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeWeylPositiveWords
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoRootPairing
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoCoordinateWeylRootMembership
open CFSGNormTwoCoordinateOutsideWordConjugation CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGE6GeckMiddleRootDegrees CFSGTwistedE6GeckPositiveTwist
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem outer_conjugate_middle_simple_mem (K : Type) [Field K]
    (i : Fin 6) (hi : i=2∨i=3∨i=4) (t : K) :
    wordUnit A hs hp E6Base E6Index K [0,5,1]*
      canonicalRoot (realizationData A hs hp E6Base E6Index) K false i t*
        (wordUnit A hs hp E6Base E6Index K [0,5,1])⁻¹∈Positive K := by
  apply conjugate_simple_mem_positive A hd hs hp ho K [0,5,1] i t
  rcases hi with rfl|rfl|rfl <;> decide

theorem outer_conjugate_middle_long_mem (K : Type) [Field K] (t : K) :
    wordUnit A hs hp b₀ s₀ K [0,5,1]*
      rootWord A hd hs hp ho K [2,4] 3 t*
        (wordUnit A hs hp b₀ s₀ K [0,5,1])⁻¹∈Positive K := by
  apply conjugate_rootWord_mem_positive A hd hs hp ho K [0,5,1] [2,4] 3 2 t
  · decide
  · change 0<(wordRoot A hs hp E6Base E6Index [2,4] (E6Index 3)).val 2
    rw [highest_root_degree]
    decide

theorem outer_conjugate_middle_pair_factor_mem (K : Type) [Field K]
    (i : Fin 6) (hi : i=2∨i=4) (t : K) :
    wordUnit A hs hp b₀ s₀ K [0,5,1]*
      rootWord A hd hs hp ho K [3] i t*
        (wordUnit A hs hp b₀ s₀ K [0,5,1])⁻¹∈Positive K := by
  rcases hi with rfl|rfl
  · apply conjugate_rootWord_mem_positive A hd hs hp ho K [0,5,1] [3] 2 2 t
    · decide
    · change 0<(wordRoot A hs hp E6Base E6Index [3] (E6Index 2)).val 2
      rw [paired_first_degree]
      decide
  · apply conjugate_rootWord_mem_positive A hd hs hp ho K [0,5,1] [3] 4 4 t
    · decide
    · change 0<(wordRoot A hs hp E6Base E6Index [3] (E6Index 4)).val 4
      rw [paired_second_degree]
      decide

theorem middle_conjugate_outer_simple_mem (K : Type) [Field K]
    (i : Fin 6) (hi : i=0∨i=5∨i=1) (t : K) :
    wordUnit A hs hp E6Base E6Index K [2,4,3,2,4,3]*
      canonicalRoot (realizationData A hs hp E6Base E6Index) K false i t*
        (wordUnit A hs hp E6Base E6Index K [2,4,3,2,4,3])⁻¹∈Positive K := by
  apply conjugate_simple_mem_positive A hd hs hp ho K [2,4,3,2,4,3] i t
  rcases hi with rfl|rfl|rfl <;> decide

end SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeWeylPositiveWords
