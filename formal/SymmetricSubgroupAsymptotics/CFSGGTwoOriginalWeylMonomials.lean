import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalBruhatUniqueness
import SymmetricSubgroupAsymptotics.CFSGGTwoWeylMonomial
import SymmetricSubgroupAsymptotics.CFSGMatrixUnitInverseTranspose
import SymmetricSubgroupAsymptotics.CFSGReeGTwoOrdinaryBorelTwist
import SymmetricSubgroupAsymptotics.CFSGRankTwoSixBraidWords

/-! Exact native monomial coordinates of original Weyl words and their
Ree images. The field-dependent row weights are retained, while the
permutation is computed solely from the two literal finite permutations. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalWeylMonomials
open CFSG.Models.Chevalley CFSGGTwoSerreMatrices CFSGGTwoWeylMonomial
open CFSGGTwoShortWeylMatrices CFSGGTwoOriginalPositiveRootWords
open CFSGGTwoOriginalBruhatUniqueness CFSGGTwoOriginalNaturalEquivalence
open CFSGGTwoSimpleBruhatComplement CFSGWeylWordBruhatCover
open CFSGMatrixUnitInverseTranspose CFSGMonomialProductCoordinates
open CFSGTypeAMonomialMatrices CFSGReeGTwoFieldParameters
open CFSGReeGTwoOriginalAutomorphism CFSGReeGTwoOrdinaryBorelTwist

def simplePermutation (i : Fin 2) : Equiv.Perm Index :=
  if i=0 then shortPermutation else longPermutation

private theorem simplePermutation_square (i : Fin 2) (x : Index) :
    simplePermutation i (simplePermutation i x)=x := by
  fin_cases i <;> rcases x with j|j <;> fin_cases j <;> decide +kernel

private theorem simplePermutation_symm (i : Fin 2) :
    (simplePermutation i).symm=simplePermutation i := by
  ext x
  apply (simplePermutation i).injective
  rw [Equiv.apply_symm_apply]
  exact (simplePermutation_square i x).symm

private theorem transpose_monomial {I L : Type*} [Fintype I] [DecidableEq I] [Field L]
    (sigma : Equiv.Perm I) (d : I→L) :
    (monomial sigma d).transpose=monomial sigma.symm (fun x=>d (sigma.symm x)) := by
  ext i j
  simp only [Matrix.transpose_apply,monomial_apply]
  by_cases h : sigma j=i
  · have hi : sigma.symm i=j := by rw [←h,Equiv.symm_apply_apply]
    rw [if_pos h,if_pos hi,hi]
  · have hi : sigma.symm i≠j := by
      intro he
      apply h
      rw [←he,Equiv.apply_symm_apply]
    rw [if_neg h,if_neg hi]

variable (K : Type) [Field K]

def simpleWeight (i : Fin 2) (x : Index) : K :=
  if i=0 then shortWeight K x else longWeight K x

private theorem simpleWeight_square (i : Fin 2) (x : Index) :
    simpleWeight K i x*simpleWeight K i x=1 := by
  unfold simpleWeight shortWeight longWeight
  split_ifs <;> simp

variable [CharP K 3]

omit [CharP K 3] in
theorem native_simple_monomial (i : Fin 2) :
    (nativeHom K (simpleWeyl K i):Mat K)=monomial (simplePermutation i) (simpleWeight K i) := by
  fin_cases i
  · exact (congrArg (fun u : naturalGroup K=>(u.val:Mat K)) (shortWord_native K)).trans
      (shortWeyl_monomial K)
  · exact (congrArg (fun u : naturalGroup K=>(u.val:Mat K)) (longWord_native K)).trans
      (longWeyl_monomial K)

theorem native_inverse_simple_monomial (i : Fin 2) :
    (nativeHom K ((simpleWeyl K i)⁻¹):Mat K)=
      monomial (simplePermutation i) (fun x=>simpleWeight K i (simplePermutation i x)) := by
  have hf := inverseTranspose_monomial (nativeHom K (simpleWeyl K i))
    (simplePermutation i) (simpleWeight K i) (native_simple_monomial K i)
    (simpleWeight_square K i)
  have he := congrArg (fun u : (Mat K)ˣ=>u.val.transpose) hf
  change ((nativeHom K (simpleWeyl K i))⁻¹).val.transpose.transpose=
    (nativeHom K (simpleWeyl K i)).val.transpose at he
  rw [Matrix.transpose_transpose] at he
  simp only [map_inv]
  rw [he,native_simple_monomial,transpose_monomial,simplePermutation_symm]

def wordPermutation : List (Fin 2)→Equiv.Perm Index
  | []=>1
  | i::w=>wordPermutation w*simplePermutation i

def wordWeight : List (Fin 2)→Index→K
  | []=>fun _=>1
  | i::w=>fun x=>simpleWeight K i x*wordWeight w (simplePermutation i x)

theorem native_word_monomial (w : List (Fin 2)) :
    (nativeHom K (wordValue (simpleWeyl K) w):Mat K)=
      monomial (wordPermutation w) (wordWeight K w) := by
  induction w with
  | nil=>
    ext i j
    simp [wordValue,wordPermutation,wordWeight,monomial_apply,Matrix.one_apply]
  | cons i w ih=>
    simp only [wordValue,map_mul,Units.val_mul,native_simple_monomial,ih,monomial_mul] <;> rfl

def twistedWeight : List (Fin 2)→Index→K
  | []=>fun _=>1
  | i::w=>fun x=>
      simpleWeight K (CFSG.Models.reverseNode i)
        (simplePermutation (CFSG.Models.reverseNode i) x)*
      twistedWeight w (simplePermutation (CFSG.Models.reverseNode i) x)

theorem native_ree_word_monomial (m : ℕ) (w : List (Fin 2)) :
    (nativeHom (Field m) (reeAutomorphism m (wordValue (simpleWeyl (Field m)) w)):
      Mat (Field m))=
      monomial (wordPermutation (w.map CFSG.Models.reverseNode)) (twistedWeight (Field m) w) := by
  induction w with
  | nil=>
    ext i j
    simp [wordValue,wordPermutation,twistedWeight,monomial_apply,Matrix.one_apply]
  | cons i w ih=>
    simp only [wordValue,map_mul,ree_simpleWeyl,Units.val_mul,
      native_inverse_simple_monomial,ih,monomial_mul,List.map_cons] <;> rfl

/-- One native coordinate distinguishes every non-fixed menu label. -/
theorem menu_fixed_permutation (k : Fin 12) :
    wordPermutation (CFSGRankTwoSixBraidWords.menuWord k) (pos 0)=
      wordPermutation ((CFSGRankTwoSixBraidWords.menuWord k).map CFSG.Models.reverseNode) (pos 0) ↔
      k=0 ∨ k=11 := by
  fin_cases k <;> decide +kernel

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalWeylMonomials
