import SymmetricSubgroupAsymptotics.FixedProductSignedWordPointEncoding
import SymmetricSubgroupAsymptotics.CFSGMathieuPrimeProductNecessaryRelations

/-! Literal signed words for the exact nine pinned M23 relators. The
seventh and ninth words are unexponentiated. This binds necessary raw
point checks to the pinned presentation; it supplies no presentation
converse and no finite acceptance/capacity assumption. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeSignedRelatorWords
open SignedPermutationWordPointEvaluation SignedPermutationWordPointEvaluation.Letter
open FixedProductSignedWordPointEncoding

/-- Values outside0..8 harmlessly select the final pinned word. -/
def relatorWord (r : ℕ) : List Letter :=
  match r with
  | 0 => powerWord [first] 2
  | 1 => powerWord [second] 4
  | 2 => powerWord [first,second] 23
  | 3 => powerWord [first,second,second] 6
  | 4 => powerWord [firstInv,secondInv,first,second] 6
  | 5 => powerWord [first,second,first,secondInv,first,second,second] 4
  | 6 => powerWord [first,second] 3 ++ [first,secondInv,first,second,second] ++
      powerWord [first,second,first,secondInv] 2 ++
      powerWord [first,second] 3 ++ powerWord [first,secondInv] 3
  | 7 => powerWord [first,second,first,second,second,first,second,second] 6
  | _ => powerWord [first,second,first,second,second] 3 ++
      powerWord [first,second,second,first,secondInv] 2 ++
      [first,second,first,second,second,first,second,first,secondInv,first,second,second]

theorem relatorWord_asFreeWord (r : Fin 9) :
    asFreeWord (relatorWord r.val) = CFSG.Models.Presentations.M23.relators.get r := by
  fin_cases r <;>
    dsimp only [CFSG.Models.Presentations.M23.relators, List.get_eq_getElem,
      List.getElem_cons_zero, List.getElem_cons_succ] <;>
    simp only [relatorWord,asFreeWord,eval_append,eval_power,eval, value,
      CFSG.Models.Presentations.M23.relators,CFSG.Models.commWord,
      List.get_eq_getElem,mul_one,pow_one] <;>
    simp only [pow_succ,pow_zero,one_mul,mul_assoc]

theorem raw_relator_point (h : Equiv.Perm (Fin 23))
    (hf hi af ai : ℕ → ℕ)
    (hhf : ∀ p : Fin 23, hf p.val = (h p).val)
    (hhi : ∀ p : Fin 23, hi p.val = (h.symm p).val)
    (haf : ∀ p : Fin 23, af p.val =
      (CFSGMathieuTwentyThreeProductNecessaryRelations.fixedProduct p).val)
    (hai : ∀ p : Fin 23, ai p.val =
      (CFSGMathieuTwentyThreeProductNecessaryRelations.fixedProduct.symm p).val)
    (hh : CFSGMathieuTwentyThreeProductNecessaryRelations.Accepts h)
    (r : Fin 9) (p : Fin 23) :
    applyWord hf hi af ai (fixedProductWord (relatorWord r.val)) p.val = p.val := by
  apply FixedProductSignedWordPointEncoding.raw_relator_point
    Fin.val h CFSGMathieuTwentyThreeProductNecessaryRelations.fixedProduct
      hf hi af ai hhf hhi haf hai
  rw [relatorWord_asFreeWord]
  exact CFSGMathieuTwentyThreeProductNecessaryRelations.accepts_at h hh r

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeSignedRelatorWords
