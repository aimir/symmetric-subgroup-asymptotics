import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleNegativeRootWords
import SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveMatrixWordValues

/-! Negative membership of the bounded middle four-coordinate family
under the actual middle relative word, in one coordinate realization. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleNegativeCoordinateFamily
open CFSGReeFFourFieldParameters CFSGReeFFourPositiveMatrixWordValues
open CFSGReeFFourMiddleNegativeRootWords CFSGNormTwoRootPairing
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoCoordinateWeylRootMembership
open CFSGTwistedE6GeckPositiveTwist CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem coordinateMiddleWord_middle_conjugate_mem_negative (m : ℕ)
    (a b c d : Field m) :
    wordUnit A hs hp b₀ s₀ (Field m) [2,4,3,2,4,3]*coordinateMiddleWord m a b c d*
      (wordUnit A hs hp b₀ s₀ (Field m) [2,4,3,2,4,3])⁻¹∈Negative (Field m) := by
  let S := wordUnit A hs hp b₀ s₀ (Field m) [2,4,3,2,4,3]
  let C := (MulAut.conj S).toMonoidHom
  have hsimple (i : Fin 6) (hi : i=2∨i=3∨i=4) (t : Field m) :
      C (rootWord A hd hs hp ho (Field m) [] i t)∈Negative (Field m) :=
    middle_conjugate_simple_mem_negative (Field m) i hi t
  have hR : C (rootWord A hd hs hp ho (Field m) [2,4] 3 d)∈Negative (Field m) :=
    middle_conjugate_long_mem_negative (Field m) d
  have hP2 : C (rootWord A hd hs hp ho (Field m) [3] 2 c)∈Negative (Field m) :=
    middle_conjugate_pair_factor_mem_negative (Field m) 2 (Or.inl rfl) c
  have hP4 : C (rootWord A hd hs hp ho (Field m) [3] 4 c)∈Negative (Field m) :=
    middle_conjugate_pair_factor_mem_negative (Field m) 4 (Or.inr rfl) c
  have hc : C (coordinateMiddleWord m a b c d)∈Negative (Field m) := by
    simp only [coordinateMiddleWord,map_mul]
    exact (Negative (Field m)).mul_mem
      ((Negative (Field m)).mul_mem
        ((Negative (Field m)).mul_mem
          ((Negative (Field m)).mul_mem (hsimple 2 (Or.inl rfl) a)
            (hsimple 4 (Or.inr (Or.inr rfl)) a))
          (hsimple 3 (Or.inr (Or.inl rfl)) b)) hR)
      ((Negative (Field m)).mul_mem hP2 hP4)
  exact hc

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleNegativeCoordinateFamily
