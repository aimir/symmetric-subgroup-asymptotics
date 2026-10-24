import SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveMatrixWordValues
import SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeWeylPositiveWords

/-! Positivity of the selected products entirely inside one coordinate
realization, before applying any original-source value identities. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourCoordinatePositiveFamilies
open CFSGReeFFourFieldParameters CFSGReeFFourPositiveMatrixWordValues
open CFSGReeFFourRelativeWeylPositiveWords CFSGNormTwoRootPairing
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoCoordinateWeylRootMembership
open CFSGNormTwoCoordinateOutsideWordConjugation CFSGTwistedE6GeckPositiveTwist
open CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem coordinateMiddleWord_outer_conjugate_mem (m : ℕ) (a b c d : Field m) :
    wordUnit A hs hp b₀ s₀ (Field m) [0,5,1]*coordinateMiddleWord m a b c d*
      (wordUnit A hs hp b₀ s₀ (Field m) [0,5,1])⁻¹∈Positive (Field m) := by
  let S := wordUnit A hs hp b₀ s₀ (Field m) [0,5,1]
  let C := (MulAut.conj S).toMonoidHom
  have hsimple (i : Fin 6) (hi : i=2∨i=3∨i=4) (t : Field m) :
      C (rootWord A hd hs hp ho (Field m) [] i t)∈Positive (Field m) := by
    apply conjugate_rootWord_mem_positive A hd hs hp ho (Field m) [0,5,1] [] i i t
    · rcases hi with rfl|rfl|rfl <;> decide
    · change 0<(Pi.single i (1:ℤ) : Fin 6→ℤ) i
      simp
  have hR : C (rootWord A hd hs hp ho (Field m) [2,4] 3 d)∈Positive (Field m) :=
    outer_conjugate_middle_long_mem (Field m) d
  have hP2 : C (rootWord A hd hs hp ho (Field m) [3] 2 c)∈Positive (Field m) :=
    outer_conjugate_middle_pair_factor_mem (Field m) 2 (Or.inl rfl) c
  have hP4 : C (rootWord A hd hs hp ho (Field m) [3] 4 c)∈Positive (Field m) :=
    outer_conjugate_middle_pair_factor_mem (Field m) 4 (Or.inr rfl) c
  have hc : C (coordinateMiddleWord m a b c d)∈Positive (Field m) := by
    simp only [coordinateMiddleWord,map_mul]
    exact (Positive (Field m)).mul_mem
      ((Positive (Field m)).mul_mem
        ((Positive (Field m)).mul_mem
          ((Positive (Field m)).mul_mem (hsimple 2 (Or.inl rfl) a)
            (hsimple 4 (Or.inr (Or.inr rfl)) a))
          (hsimple 3 (Or.inr (Or.inl rfl)) b)) hR)
      ((Positive (Field m)).mul_mem hP2 hP4)
  exact hc

theorem coordinateOuterWord_middle_conjugate_mem (m : ℕ) (a : Field m) :
    wordUnit A hs hp b₀ s₀ (Field m) [2,4,3,2,4,3]*coordinateOuterWord m a*
      (wordUnit A hs hp b₀ s₀ (Field m) [2,4,3,2,4,3])⁻¹∈Positive (Field m) := by
  let S := wordUnit A hs hp b₀ s₀ (Field m) [2,4,3,2,4,3]
  let C := (MulAut.conj S).toMonoidHom
  have hsimple (i : Fin 6) (hi : i=0∨i=5∨i=1) (t : Field m) :
      C (rootWord A hd hs hp ho (Field m) [] i t)∈Positive (Field m) := by
    apply conjugate_rootWord_mem_positive A hd hs hp ho (Field m) [2,4,3,2,4,3] [] i i t
    · rcases hi with rfl|rfl|rfl <;> decide
    · change 0<(Pi.single i (1:ℤ) : Fin 6→ℤ) i
      simp
  have hc : C (coordinateOuterWord m a)∈Positive (Field m) := by
    simp only [coordinateOuterWord,map_mul]
    exact (Positive (Field m)).mul_mem
      ((Positive (Field m)).mul_mem (hsimple 0 (Or.inl rfl) a)
        (hsimple 5 (Or.inr (Or.inl rfl)) a))
      (hsimple 1 (Or.inr (Or.inr rfl)) (alpha m a))
  exact hc

end SymmetricSubgroupAsymptotics.CFSGReeFFourCoordinatePositiveFamilies
