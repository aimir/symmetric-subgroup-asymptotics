import SymmetricSubgroupAsymptotics.CFSGGTwoNaturalWeylTorusAction
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalRankTwoTorus

/-! The exact two Weyl transformations on the literal original torus,
transported through its unconditional faithful natural representation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalWeylTorusAction
open CFSGGTwoOriginalNaturalEquivalence CFSGGTwoOriginalPositiveRootWords
open CFSGGTwoOriginalRankTwoTorus CFSGGTwoNaturalWeylTorusAction
variable (K : Type) [Field K]

theorem shortWord_torusPair (t : Kˣ × Kˣ) :
    shortWord K*torusPair K t*(shortWord K)⁻¹=torusPair K (shortTransform K t) := by
  apply (modelEquivNatural K).injective
  simp only [map_mul,map_inv,shortWord_native,torusPair_native]
  exact shortWeyl_torusPair K t

theorem longWord_torusPair (t : Kˣ × Kˣ) :
    longWord K*torusPair K t*(longWord K)⁻¹=torusPair K (longTransform K t) := by
  apply (modelEquivNatural K).injective
  simp only [map_mul,map_inv,longWord_native,torusPair_native]
  exact longWeyl_torusPair K t

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalWeylTorusAction
