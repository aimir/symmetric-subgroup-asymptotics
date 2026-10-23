import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalMiddleCollecting
import SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleFactorInjective

/-! The two actual middle-factor witnesses lie in the literal fixed U.
Injectivity of the ORIGINAL positive restriction therefore transports
matrix leading-coordinate uniqueness to the original two-factor word.
No injectivity of the whole source projection is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckMiddleGeneratedFactors
open CFSGTwistedE6GeckOriginalMiddleCollecting CFSGTwistedE6GeckOriginalPairedA2
open CFSGTwistedE6GeckOriginalSingletonA2 CFSGTwistedE6GeckOriginalProjection
open CFSGTwistedE6GeckOriginalOppositeAlignment CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckRootGeneratedPGroup CFSGTwistedE6GeckDiagramCovariance
open CFSGE6GeckSignedSimpleParameters CFSGE6GeckMiddleAThreeCollecting
open CFSGE6GeckMiddleFactorInjective CFSGE6GeckMiddleRootDegrees
open CFSGTwistedE6RelativeWeylOrbits CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGSerreOrdinaryTwists

def middleLongInGenerated (q : CFSG.PrimePower) (a : Coefficient q) :
    fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2) :=
  simpleWeylGenerated q 1*singletonInGenerated q 1 (Multiplicative.ofAdd a)*(simpleWeylGenerated q 1)⁻¹

def middleShortInGenerated (q : CFSG.PrimePower) (a : q.Extension 2) :
    fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2) :=
  simpleWeylGenerated q 2*pairedInGenerated q 1 (Multiplicative.ofAdd a)*(simpleWeylGenerated q 2)⁻¹

theorem middleLongInGenerated_val (q : CFSG.PrimePower) (a : Coefficient q) :
    (middleLongInGenerated q a).val=highestMiddle (q.Extension 2) (a : q.Extension 2) := by
  have hw : (simpleWeylGenerated q 1).val=canonicalWeyl rawData (q.Extension 2) 2*canonicalWeyl rawData (q.Extension 2) 4 := by
    rw [simpleWeylGenerated_val]
    simp [orbitWord,canonicalWord]
  change (simpleWeylGenerated q 1).val*canonicalRoot rawData (q.Extension 2) false 3 (a : q.Extension 2)*
    (simpleWeylGenerated q 1).val⁻¹=_
  rw [hw]
  rfl

theorem middleShortInGenerated_val (q : CFSG.PrimePower) (a : q.Extension 2) :
    (middleShortInGenerated q a).val=canonicalWeyl rawData (q.Extension 2) 3*
      rawPairedHom (q.Extension 2) (definingFieldAutomorphism q 2) false 1 (Multiplicative.ofAdd a)*
      (canonicalWeyl rawData (q.Extension 2) 3)⁻¹ := by
  have hw : (simpleWeylGenerated q 2).val=canonicalWeyl rawData (q.Extension 2) 3 := by
    rw [simpleWeylGenerated_val]
    simp [orbitWord,canonicalWord]
  change (simpleWeylGenerated q 2).val*rawPairedHom (q.Extension 2) (definingFieldAutomorphism q 2) false 1
    (Multiplicative.ofAdd a)*(simpleWeylGenerated q 2).val⁻¹=_
  rw [hw]

theorem middleLongInGenerated_original (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (a : Coefficient q) : generatedToOriginal q (middleLongInGenerated q a)=
      middleLongOriginalHom q (Multiplicative.ofAdd a) := by
  simp only [middleLongInGenerated,map_mul,map_inv]
  rfl

theorem middleShortInGenerated_original (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (a : q.Extension 2) : generatedToOriginal q (middleShortInGenerated q a)=
      middleShortOriginalHom q (Multiplicative.ofAdd a) := by
  simp only [middleShortInGenerated,map_mul,map_inv]
  rfl

theorem middleLongInGenerated_mem_positive (q : CFSG.PrimePower) (a : Coefficient q) :
    middleLongInGenerated q a∈rootPart (q.Extension 2) (definingFieldAutomorphism q 2) false := by
  constructor
  · change (middleLongInGenerated q a).val∈CFSGTwistedE6GeckPositiveTwist.Positive (q.Extension 2)
    rw [middleLongInGenerated_val]
    exact highestMiddle_mem_positive (q.Extension 2) a
  · exact fixedRootGenerated_le_fixed (q.Extension 2) (definingFieldAutomorphism q 2)
      (middleLongInGenerated q a).property

theorem middleShortInGenerated_mem_positive (q : CFSG.PrimePower) (a : q.Extension 2) :
    middleShortInGenerated q a∈rootPart (q.Extension 2) (definingFieldAutomorphism q 2) false := by
  constructor
  · change (middleShortInGenerated q a).val∈CFSGTwistedE6GeckPositiveTwist.Positive (q.Extension 2)
    rw [middleShortInGenerated_val]
    exact middlePair_mem_positive (q.Extension 2) (definingFieldAutomorphism q 2) a
  · exact fixedRootGenerated_le_fixed (q.Extension 2) (definingFieldAutomorphism q 2)
      (middleShortInGenerated q a).property

theorem original_middleFactor_snd_eq (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (r r' : Coefficient q) (a a' : q.Extension 2)
    (he : middleLongOriginalHom q (Multiplicative.ofAdd r)*middleShortOriginalHom q (Multiplicative.ofAdd a)=
      middleLongOriginalHom q (Multiplicative.ofAdd r')*middleShortOriginalHom q (Multiplicative.ofAdd a')) : a=a' := by
  let U := rootPart (q.Extension 2) (definingFieldAutomorphism q 2) false
  let x : U := ⟨middleLongInGenerated q r*middleShortInGenerated q a,
    U.mul_mem (middleLongInGenerated_mem_positive q r) (middleShortInGenerated_mem_positive q a)⟩
  let y : U := ⟨middleLongInGenerated q r'*middleShortInGenerated q a',
    U.mul_mem (middleLongInGenerated_mem_positive q r') (middleShortInGenerated_mem_positive q a')⟩
  have hproj : generatedToOriginal q x.val=generatedToOriginal q y.val := by
    change generatedToOriginal q (middleLongInGenerated q r*middleShortInGenerated q a)=
      generatedToOriginal q (middleLongInGenerated q r'*middleShortInGenerated q a')
    simpa only [map_mul,middleLongInGenerated_original,middleShortInGenerated_original] using he
  have hxy : x=y := rootPart_positive_original_injective q hproj
  have hraw := congrArg (fun z : U=>z.val.val) hxy
  change (middleLongInGenerated q r).val*(middleShortInGenerated q a).val=
    (middleLongInGenerated q r').val*(middleShortInGenerated q a').val at hraw
  rw [middleLongInGenerated_val,middleShortInGenerated_val,
    middleLongInGenerated_val,middleShortInGenerated_val] at hraw
  exact middleFactor_snd_eq (q.Extension 2) (definingFieldAutomorphism q 2) r r' a a' hraw

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckMiddleGeneratedFactors
