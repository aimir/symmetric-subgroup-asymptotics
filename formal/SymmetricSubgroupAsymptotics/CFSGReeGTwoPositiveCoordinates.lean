import SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalPositiveSubgroup

/-! The three free parameters carry the actual positive Ree group law.
Its remaining coordinates are recovered from the literal fixed-word
equations; the group law is never postulated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveCoordinates
open CFSGReeGTwoFieldParameters CFSGReeGTwoFixedModelEquivalence
open CFSGReeGTwoOriginalPositiveSubgroup CFSGReeGTwoOriginalFixedWordChart
open CFSGReeGTwoFixedCoordinateArithmetic CFSGReeGTwoSixWordTwist
open CFSGReeGTwoOriginalAutomorphism CFSGGTwoPositiveSixWord
open CFSGGTwoPositiveWordMultiplication CFSGGTwoPositiveWordSubgroup

def productCoordinates (m : ℕ) (x y : Fin 3 → Field m) : Fin 3 → Field m :=
  ![x 0+y 0,x 1+y 1-y 0*(alphaEquiv m (x 0)),
    x 2+y 2-y 0*x 1-(y 0)^2*(alphaEquiv m (x 0))]

theorem chart_mul (m : ℕ) (x y : Fin 3 → Field m) :
    fixedPositiveChart m x*fixedPositiveChart m y=
      fixedPositiveChart m (productCoordinates m x y) := by
  let g : originalModelFixed m := (fixedPositiveChart m x*fixedPositiveChart m y).val
  let z : Fin 6 → Field m := CFSGGTwoPositiveWordMultiplication.productCoordinates (Field m)
    (normalForm (alphaEquiv m) (x 0) (x 1) (x 2))
    (normalForm (alphaEquiv m) (y 0) (y 1) (y 2))
  have hg : g.val=modelWord (Field m) z :=
    modelWord_mul (Field m) _ _
  have hf : reeAutomorphism m (modelWord (Field m) z)=modelWord (Field m) z := by
    rw [←hg]
    exact g.property
  have hn : z=normalForm (alphaEquiv m) (z 0) (z 2) (z 3) :=
    (fixed_iff_normalForm (alphaEquiv m) (alpha_twice m) z).mp
      ((modelWord_fixed_iff m z).mp hf)
  apply Subtype.ext
  apply Subtype.ext
  change g.val=modelWord (Field m) (normalForm (alphaEquiv m)
    (productCoordinates m x y 0) (productCoordinates m x y 1) (productCoordinates m x y 2))
  exact hg.trans (congrArg (modelWord (Field m)) hn)

theorem chart_zero (m : ℕ) : fixedPositiveChart m 0=1 := by
  apply Subtype.ext
  apply Subtype.ext
  change modelWord (Field m) (normalForm (alphaEquiv m) 0 0 0)=1
  have he : normalForm (alphaEquiv m) 0 0 0=0 := by
    funext i
    fin_cases i <;> simp [normalForm]
  rw [he,modelWord_zero]

theorem chart_commute_iff (m : ℕ) (x y : Fin 3 → Field m) :
    Commute (fixedPositiveChart m x) (fixedPositiveChart m y) ↔
      productCoordinates m x y=productCoordinates m y x := by
  change fixedPositiveChart m x*fixedPositiveChart m y=
      fixedPositiveChart m y*fixedPositiveChart m x ↔ _
  rw [chart_mul,chart_mul]
  exact (fixedPositiveChart_injective m).eq_iff

end SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveCoordinates
