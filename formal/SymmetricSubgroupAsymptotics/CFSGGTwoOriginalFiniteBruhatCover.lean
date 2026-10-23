import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalWordBruhatCover
import SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalOpposition
import SymmetricSubgroupAsymptotics.CFSGRankTwoSixBraidWords

/-! Actual twelve-cell coverage of the whole original G2 Model. The
six-letter braid is proved from the faithful natural signed-monomial
longest word, then the explicit finite word table is installed. There is
no ordinary G2 simplicity, supplied group order, or BN-pair premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalFiniteBruhatCover
open CFSG.Models.Chevalley CFSGGTwoSerreMatrices CFSGGTwoShortWeylMatrices
open CFSGGTwoOriginalNaturalEquivalence CFSGGTwoOriginalPositiveRootWords
open CFSGGTwoWeylMonomial CFSGGTwoLongestWeylMonomial CFSGMonomialProductCoordinates
open CFSGTypeAMonomialMatrices CFSGReeGTwoOriginalOpposition
open CFSGGTwoOriginalBorel CFSGGTwoSimpleBruhatComplement
open CFSGGTwoOriginalWordBruhatCover CFSGWeylWordBruhatCover

private theorem opposite_short_permutation :
    shortPermutation*oppositePermutation=oppositePermutation*shortPermutation := by
  ext x
  rcases x with i|i <;> fin_cases i <;> decide +kernel

variable (K : Type) [Field K]

private theorem opposite_short_weight (x : Index) :
    shortWeight K (oppositePermutation x)=shortWeight K x := by
  rcases x with i|i <;> fin_cases i <;>
    norm_num [shortWeight,oppositePermutation,pos,neg,Fin.ext_iff,
      Sum.inl_ne_inr,Sum.inr_ne_inl]

theorem longest_short_native : Commute (longestUnit K) (shortWeyl K) := by
  change longestUnit K*shortWeyl K=shortWeyl K*longestUnit K
  apply Units.ext
  simp only [Units.val_mul,longestUnit_val,shortWeyl_monomial,monomial_mul,
    opposite_short_permutation]
  apply congrArg (monomial (oppositePermutation*shortPermutation))
  funext x
  rw [opposite_short_weight]
  ring

theorem longest_short_commute : Commute (longestWord K) (shortWord K) := by
  change longestWord K*shortWord K=shortWord K*longestWord K
  apply (modelEquivNatural K).injective
  apply Subtype.ext
  simp only [map_mul,Subgroup.coe_mul,longestWord_native,shortWord_native]
  exact (longest_short_native K).eq

private theorem rotate_three {G : Type*} [Group G] (s t : G) :
    s⁻¹*(s*t)^3*s=(t*s)^3 := by
  simp only [pow_succ,pow_zero,one_mul]
  group

private theorem conjugate_fixed {G : Type*} [Group G] (s w : G) (h : Commute w s) :
    s⁻¹*w*s=w := by
  rw [mul_assoc,h.eq]
  group

theorem original_six_braid [CharP K 3] :
    wordValue (simpleWeyl K) [0,1,0,1,0,1]=
      wordValue (simpleWeyl K) [1,0,1,0,1,0] := by
  have hleft : wordValue (simpleWeyl K) [0,1,0,1,0,1]=longestWord K := by
    simp [wordValue,simpleWeyl,longestWord,pow_succ,mul_assoc]
  have hright : wordValue (simpleWeyl K) [1,0,1,0,1,0]=
      (longWord K*shortWord K)^3 := by
    simp [wordValue,simpleWeyl,pow_succ,mul_assoc]
  have hc : (shortWord K)⁻¹*longestWord K*shortWord K=longestWord K :=
    conjugate_fixed (shortWord K) (longestWord K) (longest_short_commute K)
  have hr := rotate_three (shortWord K) (longWord K)
  change (shortWord K)⁻¹*longestWord K*shortWord K=(longWord K*shortWord K)^3 at hr
  exact hleft.trans (hc.symm.trans (hr.trans hright.symm))

theorem original_finite_bruhat [Finite K] [CharP K 3] (g : Model CartanMatrix.G₂ K) :
    ∃k : Fin 12,DoubleCell (borel K)
      (CFSGRankTwoSixBraidWords.representative (simpleWeyl K) k) g :=
  CFSGRankTwoSixBraidWords.finite_word_cells (borel K) (torus K) (torus_le_borel K)
    (simpleWeyl K) (simple_square_mem_torus K) (simple_torus_normalizer K)
    (original_six_braid K) g (original_word_bruhat K g)

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalFiniteBruhatCover
