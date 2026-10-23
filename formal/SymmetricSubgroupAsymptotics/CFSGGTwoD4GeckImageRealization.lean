import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckRootUnits
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckImageAdjoint
import SymmetricSubgroupAsymptotics.CFSGSerreCubicMatrixActions

/-! The ORIGINAL G2 model and the literal folded D4 simple units act
on the SAME base-changed integral matrix image. All cubic coefficients,
higher-coefficient vanishing and unit polynomial formulas are discharged.
No source faithfulness, kernel centrality or projective equivalence is
asserted by this action-range comparison. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckImageRealization
open CFSGGTwoD4GeckGenerators CFSGGTwoD4GeckSerreRepresentation
open CFSGGTwoD4GeckIntegralCoefficients CFSGGTwoD4GeckIntegralRealization
open CFSGGTwoD4GeckRootUnits CFSGGTwoD4GeckImageAdjoint
open CFSG.Models.Chevalley

theorem rational_image_ad_four (neg : Bool) (i : Fin 2) (x : RationalLie CartanMatrix.G₂) :
    (LieAlgebra.ad ℚ Mat (CFSGSerreCubicMatrix.fieldRoot realizationData ℚ neg i)^4)
      (realizationData.rational x)=0 := by
  change (LieAlgebra.ad ℚ Mat ((Int.castRingHom ℚ).mapMatrix
    (integerGenerator (CFSGSerreSquareZeroMatrix.rootGenerator neg i)))^4) (rationalRepresentation x)=0
  rw [integerGenerator_root,map_integerRoot]
  exact folded_root_ad_four neg i x

abbrev Image (K : Type) [Field K] := (CFSGSerreCubicMatrix.baseChange realizationData K).range

abbrev sourceImageRepresentation (K : Type) [Field K] :
    Model CartanMatrix.G₂ K→*(Image K≃ₗ[K]Image K) :=
  CFSGSerreCubicMatrix.imageRepresentation realizationData K

abbrev foldedGroup (K : Type) [Field K] :=
  CFSGSerreCubicMatrix.elementaryGroup K (rootUnit K)

abbrev foldedRoot (K : Type) [Field K] :=
  CFSGSerreCubicMatrix.elementaryRoot K (rootUnit K)

abbrev foldedImageAction (K : Type) [Field K] :
    foldedGroup K→*(Image K≃ₗ[K]Image K) :=
  CFSGSerreCubicMatrix.elementaryImageAction realizationData K (rootUnit K)
    (rootUnit_val K) (rootUnit_inv_val K) rational_image_ad_four

theorem source_root_action (K : Type) [Field K] (neg : Bool) (i : Fin 2) (t : K) :
    sourceImageRepresentation K (CFSGSerreModelRootGeneration.modelRoot CartanMatrix.G₂ K neg i t)=
      foldedImageAction K (foldedRoot K neg i t) :=
  CFSGSerreCubicMatrix.source_root_action_eq_elementary realizationData K (rootUnit K)
    (rootUnit_val K) (rootUnit_inv_val K) rational_image_ad_four neg i t

theorem foldedImageAction_apply (K : Type) [Field K] (g : foldedGroup K) (y : Image K) :
    (foldedImageAction K g y).val=(g.val : Matrix GeckIndex GeckIndex K)*y.val*
      (↑(g.val⁻¹) : Matrix GeckIndex GeckIndex K) := rfl

theorem action_ranges_eq (K : Type) [Field K] :
    (sourceImageRepresentation K).range=(foldedImageAction K).range :=
  CFSGSerreCubicMatrix.action_ranges_eq realizationData K (rootUnit K)
    (rootUnit_val K) (rootUnit_inv_val K) rational_image_ad_four

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckImageRealization
