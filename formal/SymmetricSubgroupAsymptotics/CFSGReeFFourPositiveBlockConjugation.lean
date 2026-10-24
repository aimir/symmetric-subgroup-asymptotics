import SymmetricSubgroupAsymptotics.CFSGReeFFourCoordinatePositiveFamilies

/-! A finite root-sign certificate transports a whole actual outer or
middle coordinate block into the positive group. The field parameters
are unrestricted; only the integral signs of the displayed three or six
root factors enter the premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveBlockConjugation
open CFSGReeFFourFieldParameters CFSGReeFFourPositiveMatrixWordValues
open CFSGNormTwoRootPairing CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoCoordinateWeylRootMembership CFSGNormTwoCoordinateOutsideWordConjugation
open CFSGTwistedE6GeckPositiveTwist CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

def blockRoots (middle : Bool) : List (List (Fin 6) × Fin 6) :=
  if middle then [([],2),([],4),([],3),([2,4],3),([3],2),([3],4)]
  else [([],0),([],5),([],1)]

def positiveBlockSigns (middle : Bool) (v : List (Fin 6)) : Prop :=
  ∀ w i, (w,i)∈blockRoots middle →
    ∀ j, 0≤(wordRoot A hs hp b₀ s₀ (v++w) (s₀ i)).val j

private theorem root_factor_positive (m : ℕ) (v w : List (Fin 6)) (i : Fin 6)
    (hpos : ∀j,0≤(wordRoot A hs hp b₀ s₀ (v++w) (s₀ i)).val j) (t : Field m) :
    wordUnit A hs hp b₀ s₀ (Field m) v*rootWord A hd hs hp ho (Field m) w i t*
      (wordUnit A hs hp b₀ s₀ (Field m) v)⁻¹∈Positive (Field m) := by
  rw [conjugate_rootWord_eq]
  exact positive_word_mem A hd hs hp ho (Field m) (v++w) i t hpos

theorem coordinateMiddleWord_conjugate_mem (m : ℕ) (v : List (Fin 6))
    (hpos : positiveBlockSigns true v) (a b c d : Field m) :
    wordUnit A hs hp b₀ s₀ (Field m) v*coordinateMiddleWord m a b c d*
      (wordUnit A hs hp b₀ s₀ (Field m) v)⁻¹∈Positive (Field m) := by
  let C := (MulAut.conj (wordUnit A hs hp b₀ s₀ (Field m) v)).toMonoidHom
  have hf (w : List (Fin 6)) (i : Fin 6) (hi : (w,i)∈blockRoots true) (t : Field m) :
      C (rootWord A hd hs hp ho (Field m) w i t)∈Positive (Field m) :=
    root_factor_positive m v w i (hpos w i hi) t
  have hc : C (coordinateMiddleWord m a b c d)∈Positive (Field m) := by
    simp only [coordinateMiddleWord,map_mul]
    exact (Positive (Field m)).mul_mem
      ((Positive (Field m)).mul_mem
        ((Positive (Field m)).mul_mem
          ((Positive (Field m)).mul_mem (hf [] 2 (by simp [blockRoots]) a)
            (hf [] 4 (by simp [blockRoots]) a))
          (hf [] 3 (by simp [blockRoots]) b)) (hf [2,4] 3 (by simp [blockRoots]) d))
      ((Positive (Field m)).mul_mem (hf [3] 2 (by simp [blockRoots]) c)
        (hf [3] 4 (by simp [blockRoots]) c))
  exact hc

theorem coordinateOuterWord_conjugate_mem (m : ℕ) (v : List (Fin 6))
    (hpos : positiveBlockSigns false v) (a : Field m) :
    wordUnit A hs hp b₀ s₀ (Field m) v*coordinateOuterWord m a*
      (wordUnit A hs hp b₀ s₀ (Field m) v)⁻¹∈Positive (Field m) := by
  let C := (MulAut.conj (wordUnit A hs hp b₀ s₀ (Field m) v)).toMonoidHom
  have hf (i : Fin 6) (hi : ([],i)∈blockRoots false) (t : Field m) :
      C (rootWord A hd hs hp ho (Field m) [] i t)∈Positive (Field m) :=
    root_factor_positive m v [] i (hpos [] i hi) t
  have hc : C (coordinateOuterWord m a)∈Positive (Field m) := by
    simp only [coordinateOuterWord,map_mul]
    exact (Positive (Field m)).mul_mem
      ((Positive (Field m)).mul_mem (hf 0 (by simp [blockRoots]) a)
        (hf 5 (by simp [blockRoots]) a))
      (hf 1 (by simp [blockRoots]) (alpha m a))
  exact hc

end SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveBlockConjugation
