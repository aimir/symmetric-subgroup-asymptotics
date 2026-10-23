import SymmetricSubgroupAsymptotics.CFSGGTwoLongestWeylMonomial
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalExceptionalWeylWords
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalFieldRootWords
import SymmetricSubgroupAsymptotics.CFSGReeGTwoFixedModelEquivalence

/-! A literal ORIGINAL fixed opposition word. Its order and exceptional
image are proved before using it in any Bruhat or Sylow argument. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalOpposition
open CFSG.Models.Chevalley CFSGGTwoOriginalPositiveRootWords
open CFSGGTwoOriginalNaturalEquivalence CFSGGTwoLongestWeylMonomial
open CFSGGTwoOriginalExceptionalWeylWords CFSGGTwoOriginalExceptionalModel
open CFSGGTwoOriginalFieldRootWords CFSGReeGTwoFieldParameters
open CFSGReeGTwoOriginalAutomorphism CFSGReeGTwoFixedModelEquivalence

variable (K : Type) [Field K]

def longestWord : Model CartanMatrix.G₂ K := (shortWord K*longWord K)^3

theorem longestWord_native : (modelEquivNatural K (longestWord K)).val=longestUnit K := by
  simp only [longestWord,map_pow,map_mul,Subgroup.coe_pow,Subgroup.coe_mul,
    shortWord_native,longWord_native]
  rfl

theorem longestWord_square : longestWord K*longestWord K=1 := by
  apply (modelEquivNatural K).injective
  apply Subtype.ext
  simpa only [map_mul,map_one,Subgroup.coe_mul,Subgroup.coe_one,longestWord_native] using
    longestUnit_square K

theorem longestWord_inv : (longestWord K)⁻¹=longestWord K :=
  inv_eq_of_mul_eq_one_right (longestWord_square K)

theorem fieldModel_longestWord (sigma : K ≃+* K) :
    fieldModel K sigma (longestWord K)=longestWord K := by
  simp only [longestWord,map_pow,map_mul,fieldModel_shortWord,fieldModel_longWord]

theorem exceptional_longestWord [Finite K] [CharP K 3] :
    exceptionalModelEquiv K (longestWord K)=(longestWord K)⁻¹ := by
  simp only [longestWord,map_pow,map_mul,exceptional_shortWord,exceptional_longWord]
  rw [←mul_inv_rev,inv_pow]

/-- The actual opposition element belongs to the SAME original fixed group. -/
def fixedOpposition (m : ℕ) : originalModelFixed m :=
  ⟨longestWord (Field m),by
    change exceptionalModelEquiv (Field m)
      (fieldModel (Field m) (alphaEquiv m).symm (longestWord (Field m)))=longestWord (Field m)
    rw [fieldModel_longestWord,exceptional_longestWord,longestWord_inv]⟩

def originalOpposition (m : ℕ) :
    fixedSubgroup CartanMatrix.G₂ (Field m) CFSG.Models.reverseNode (originalExponent m) :=
  (originalFixedEquiv m).symm (fixedOpposition m)

theorem fixedOpposition_square (m : ℕ) : fixedOpposition m*fixedOpposition m=1 :=
  Subtype.ext (longestWord_square (Field m))

theorem originalOpposition_square (m : ℕ) : originalOpposition m*originalOpposition m=1 := by
  apply (originalFixedEquiv m).injective
  change (originalFixedEquiv m) (originalOpposition m*originalOpposition m)=_
  simp only [map_mul,map_one,originalOpposition,MulEquiv.apply_symm_apply]
  exact fixedOpposition_square m

end SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalOpposition
