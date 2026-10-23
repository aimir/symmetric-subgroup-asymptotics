import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeTorus
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckMiddleGeneratedFactors
import SymmetricSubgroupAsymptotics.CFSGE6GeckMiddlePairedTorusScaling

/-! Literal J witnesses for the middle two factors and their torus
scalars, followed by the SAME original projection. These calculations
require neither source faithfulness nor a lift of an original Aut. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalMiddleTorus
open CFSGTwistedE6GeckRelativeTorus CFSGTwistedE6GeckOriginalMiddleCollecting
open CFSGTwistedE6GeckMiddleGeneratedFactors
open CFSGTwistedE6GeckOriginalPairedA2 CFSGTwistedE6GeckOriginalSingletonA2
open CFSGTwistedE6GeckOriginalProjection CFSGTwistedE6GeckOriginalSimpleParameters
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckDiagramCovariance
open CFSGE6GeckMiddleTorusScaling CFSGE6GeckMiddlePairedTorusScaling
open CFSGE6GeckMiddleAThreeCollecting CFSGE6GeckSignedSimpleParameters
open CFSGTwistedE6RelativeWeylOrbits CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGSerreOrdinaryTwists

theorem singleton_torus_middleShort (q : CFSG.PrimePower) (t : (Coefficient q)ˣ) (a : q.Extension 2) :
    singletonTorusGenerated q 1 t*middleShortInGenerated q a*(singletonTorusGenerated q 1 t)⁻¹=
      middleShortInGenerated q (a*((t : Coefficient q) : q.Extension 2)) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul,Subgroup.coe_inv,singletonTorusGenerated_val,middleShortInGenerated_val]
  exact middleShort_torus_scale (q.Extension 2) (definingFieldAutomorphism q 2) (coefficientUnit q t)
    (t : Coefficient q).property a

theorem paired_torus_middleLong (q : CFSG.PrimePower) (t : (q.Extension 2)ˣ) (a : Coefficient q) :
    pairedTorusGenerated q 1 t*middleLongInGenerated q a*(pairedTorusGenerated q 1 t)⁻¹=
      middleLongInGenerated q (normCoefficient q (t : q.Extension 2)*a) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul,Subgroup.coe_inv,pairedTorusGenerated_val,middleLongInGenerated_val]
  calc
    _=highestMiddle (q.Extension 2) ((a : q.Extension 2)*((t : q.Extension 2)*definingFieldAutomorphism q 2 (t : q.Extension 2))) :=
      middleLong_paired_torus_scale (q.Extension 2) (definingFieldAutomorphism q 2) t a
    _=_ := by congr 1; exact mul_comm _ _

theorem original_singleton_torus_middleShort (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (t : (Coefficient q)ˣ) (a : q.Extension 2) :
    generatedToOriginal q (singletonTorusGenerated q 1 t)*middleShortOriginalHom q (Multiplicative.ofAdd a)*
      (generatedToOriginal q (singletonTorusGenerated q 1 t))⁻¹=
      middleShortOriginalHom q (Multiplicative.ofAdd (a*((t : Coefficient q) : q.Extension 2))) := by
  simpa only [map_mul,map_inv,middleShortInGenerated_original] using
    congrArg (generatedToOriginal q) (singleton_torus_middleShort q t a)

theorem original_paired_torus_middleLong (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (t : (q.Extension 2)ˣ) (a : Coefficient q) :
    generatedToOriginal q (pairedTorusGenerated q 1 t)*middleLongOriginalHom q (Multiplicative.ofAdd a)*
      (generatedToOriginal q (pairedTorusGenerated q 1 t))⁻¹=
      middleLongOriginalHom q (Multiplicative.ofAdd (normCoefficient q (t : q.Extension 2)*a)) := by
  simpa only [map_mul,map_inv,middleLongInGenerated_original] using
    congrArg (generatedToOriginal q) (paired_torus_middleLong q t a)

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalMiddleTorus
