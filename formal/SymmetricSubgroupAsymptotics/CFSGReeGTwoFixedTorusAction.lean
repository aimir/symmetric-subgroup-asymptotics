import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalPositiveTorusAction
import SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalTorus
import SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalPositiveSubgroup

/-! The original fixed torus acts diagonally on the three free positive
coordinates. Fixed-word uniqueness supplies the other three coordinates;
no fixed-point lifting or ordinary G2 simplicity is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoFixedTorusAction
open CFSGReeGTwoFieldParameters CFSGReeGTwoOriginalTorus
open CFSGReeGTwoFixedModelEquivalence CFSGReeGTwoOriginalFixedWordChart
open CFSGReeGTwoFixedCoordinateArithmetic CFSGReeGTwoSixWordTwist
open CFSGReeGTwoOriginalAutomorphism CFSGGTwoPositiveSixWord
open CFSGGTwoOriginalPositiveTorusAction CFSGGTwoNaturalPositiveTorusAction

def fixedScaleCoordinates (m : ℕ) (t : (Field m)ˣ) (y : Fin 3 → Field m) :
    Fin 3 → Field m :=
  ![y 0*(rootScale (Field m) (t,unitsAlpha m t) 0 : Field m),
    y 1*(rootScale (Field m) (t,unitsAlpha m t) 2 : Field m),
    y 2*(rootScale (Field m) (t,unitsAlpha m t) 3 : Field m)]

theorem fixedTorus_fixedWord (m : ℕ) (t : (Field m)ˣ) (y : Fin 3 → Field m) :
    fixedTorusHom m t * fixedWord m y * (fixedTorusHom m t)⁻¹ =
      fixedWord m (fixedScaleCoordinates m t y) := by
  let g : originalModelFixed m :=
    fixedTorusHom m t * fixedWord m y * (fixedTorusHom m t)⁻¹
  let x : Fin 6 → Field m := scaleCoordinates (Field m) (t,unitsAlpha m t)
    (normalForm (alphaEquiv m) (y 0) (y 1) (y 2))
  have hg : g.val = modelWord (Field m) x := by
    change (fixedTorusHom m t).val * (fixedWord m y).val *
      ((fixedTorusHom m t).val)⁻¹ = modelWord (Field m) x
    rw [fixedTorusHom_val]
    exact torusPair_modelWord (Field m) (t,unitsAlpha m t)
      (normalForm (alphaEquiv m) (y 0) (y 1) (y 2))
  have hf : reeAutomorphism m (modelWord (Field m) x) = modelWord (Field m) x := by
    rw [←hg]
    exact g.property
  have hn : x = normalForm (alphaEquiv m) (x 0) (x 2) (x 3) :=
    (fixed_iff_normalForm (alphaEquiv m) (alpha_twice m) x).mp
      ((modelWord_fixed_iff m x).mp hf)
  apply Subtype.ext
  change g.val = modelWord (Field m) (normalForm (alphaEquiv m)
    (fixedScaleCoordinates m t y 0) (fixedScaleCoordinates m t y 1)
    (fixedScaleCoordinates m t y 2))
  exact hg.trans (congrArg (modelWord (Field m)) hn)

end SymmetricSubgroupAsymptotics.CFSGReeGTwoFixedTorusAction
