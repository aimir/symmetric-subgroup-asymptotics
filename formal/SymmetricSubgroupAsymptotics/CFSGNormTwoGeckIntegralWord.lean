import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticWeylWord
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordDegree

/-! The actual field-valued Geck word is the base change of a literal
unimodular INTEGER word. Its inverse remains integral as well. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckIntegralWord
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGSerreQuadraticWeylWord CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoGeckWeylWordDegree
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

local notation "D" => realizationData A hs hp b s

theorem word_eq_canonicalWord (K : Type) [Field K] (w : List (Fin r)) :
    wordUnit A hs hp b s K w=canonicalWord D K w := by
  induction w with
  | nil=>rfl
  | cons i w ih=>simp only [wordUnit,canonicalWord,ih]

theorem cast_integer_word (K : Type) [Field K] (w : List (Fin r)) :
    (Int.castRingHom K).mapMatrix (canonicalWord D ℤ w : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℤ)=
      (wordUnit A hs hp b s K w : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K) := by
  rw [map_word_val,word_eq_canonicalWord]

theorem cast_integer_word_inverse (K : Type) [Field K] (w : List (Fin r)) :
    (Int.castRingHom K).mapMatrix
      (((canonicalWord D ℤ w)⁻¹ : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℤ)ˣ) :
        Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℤ)=
      (((wordUnit A hs hp b s K w)⁻¹ : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ) :
        Matrix (b.support⊕Roots A) (b.support⊕Roots A) K) := by
  rw [map_word_inv_val,word_eq_canonicalWord]

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckIntegralWord
