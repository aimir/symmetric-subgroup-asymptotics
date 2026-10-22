import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordDegree

/-! Literal concatenation, inverse-word, and root-negation rules for the
same Geck Weyl words. Inverse letters are replaced by three identical
letters using their proved fourth power, without Coxeter recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordAlgebra
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylUnits CFSGSerreQuadraticMatrix
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

def inverseWord : List (Fin r)→List (Fin r)
  | []=>[]
  | i::w=>inverseWord w++[i,i,i]

theorem wordUnit_append (K : Type) [Field K] (v w : List (Fin r)) :
    wordUnit A hs hp b s K (v++w)=wordUnit A hs hp b s K v*wordUnit A hs hp b s K w := by
  induction v with
  | nil=>simp only [List.nil_append,wordUnit,one_mul]
  | cons i v ih=>rw [List.cons_append,wordUnit,ih,wordUnit,mul_assoc]

theorem wordUnit_inverseWord (K : Type) [Field K] (w : List (Fin r)) :
    wordUnit A hs hp b s K (inverseWord w)=(wordUnit A hs hp b s K w)⁻¹ := by
  induction w with
  | nil=>simp only [inverseWord,wordUnit,inv_one]
  | cons i w ih=>
    have hi : (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹=
        canonicalWeyl (realizationData A hs hp b s) K i*
          canonicalWeyl (realizationData A hs hp b s) K i*
            canonicalWeyl (realizationData A hs hp b s) K i := by
      apply inv_eq_of_mul_eq_one_right
      calc
        _=(canonicalWeyl (realizationData A hs hp b s) K i)^4 := by
          simp only [pow_succ,pow_zero,one_mul,mul_assoc]
        _=1 := weyl_four A hs hp b s K i
    rw [inverseWord,wordUnit_append,ih]
    simp only [wordUnit,mul_one,mul_inv_rev,hi,mul_assoc]

theorem wordRoot_append (v w : List (Fin r)) (k : Roots A) :
    wordRoot A hs hp b s (v++w) k=wordRoot A hs hp b s v (wordRoot A hs hp b s w k) := by
  induction v with
  | nil=>rfl
  | cons i v ih=>rw [List.cons_append,wordRoot,ih,wordRoot]

theorem wordRoot_negative_val (w : List (Fin r)) (k : Roots A) :
    (wordRoot A hs hp b s w (negativeIndex A hs hp k)).val=
      -(wordRoot A hs hp b s w k).val := by
  induction w with
  | nil=>exact negative_val A hs hp k
  | cons i w ih=>
    change reflectionEquiv A (s i)
      (wordRoot A hs hp b s w (negativeIndex A hs hp k)).val=
        -reflectionEquiv A (s i) (wordRoot A hs hp b s w k).val
    rw [ih,map_neg]

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordAlgebra
