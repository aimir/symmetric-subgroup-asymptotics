import SymmetricSubgroupAsymptotics.CFSGGTwoNaturalPositiveTorusAction
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalRankTwoTorus
import SymmetricSubgroupAsymptotics.CFSGGTwoPositiveSixWord

/-! Conjugation of the literal six original positive root words by the
SAME original torus. The entire word transforms coordinatewise; the
faithful original/native equivalence is unconditional. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalPositiveTorusAction
open CFSG.Models.Chevalley CFSGGTwoOriginalNaturalEquivalence
open CFSGGTwoOriginalPositiveRootWords CFSGGTwoOriginalRankTwoTorus
open CFSGGTwoNaturalPositiveTorusAction CFSGGTwoPositiveSixWord
variable (K : Type) [Field K]
local notation "A" => CartanMatrix.G₂

theorem torusPair_positiveModel (t : Kˣ × Kˣ) (j : Fin 6) (a : K) :
    torusPair K t * positiveModel K j a * (torusPair K t)⁻¹ =
      positiveModel K j (a*(rootScale K t j : K)) := by
  apply (modelEquivNatural K).injective
  simp only [map_mul, map_inv, torusPair_native, positiveModel_native]
  exact torusPair_positiveRoot K t j a

def scaleCoordinates (t : Kˣ × Kˣ) (x : Fin 6 → K) : Fin 6 → K :=
  fun j => x j*(rootScale K t j : K)

theorem torusPair_modelWord (t : Kˣ × Kˣ) (x : Fin 6 → K) :
    torusPair K t * modelWord K x * (torusPair K t)⁻¹ =
      modelWord K (scaleCoordinates K t x) := by
  let c : MulAut (Model A K) := MulAut.conj (torusPair K t)
  have hc (j : Fin 6) (a : K) :
      c (positiveModel K j a) = positiveModel K j (a*(rootScale K t j : K)) :=
    torusPair_positiveModel K t j a
  change c (modelWord K x) = modelWord K (scaleCoordinates K t x)
  simp only [modelWord, map_mul, hc, scaleCoordinates]

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalPositiveTorusAction
