import SymmetricSubgroupAsymptotics.CFSGTitsNegativeCentralRoot
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryCentralReflection
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleDerivedFiveSurvival
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedDerivedInversionFacts
import SymmetricSubgroupAsymptotics.OddInvolutionConjugateRecovery

/-! Recover an ACTUAL Tits reflection from the two intrinsic opposed
centre involutions. Its odd product survives the FULL derived-centre
quotient by the checked five-word theorem. No target automorphism is
lifted, and no ambient cyclic-four block is declared characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTitsCentralReflection
open CFSGTitsPositiveCentralRoot CFSGTitsNegativeCentralRoot CFSGTitsAmbientPairAlignment
open CFSGReeFFourBinaryCentralReflection CFSGReeFFourBinaryCentralWordProperties
open CFSGReeFFourBinaryPositiveCentralWord CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourOriginalPositiveSylow CFSGReeFFourAmbientCentralQuotientAction
open CFSGReeFFourMiddleDerivedFiveWord CFSGReeFFourMiddleDerivedFiveSurvival
open CFSGReeFFourFixedDerivedInversionFacts CFSGReeFFourRelativePositiveSubgroups
open CFSGReeFFourOppositionFixedPositiveNegative
private abbrev D := commutator (originalModelFixed 0)
private def rSource : D := ⟨centralReflection,centralReflection_mem_derived⟩
private def zSource : D := ⟨centralWord,centralWord_mem_derived⟩

private theorem map_period {G H : Type*} [Group G] [Group H]
    (f : G →* H) (x : G) (n : ℕ) (h : x^n=1) : (f x)^n=1 :=
  (map_pow f x n).symm.trans ((congrArg f h).trans (map_one f))

private theorem conjugate_product {G : Type*} [Group G] (k w s : G) :
    (k*w*k⁻¹)*(k*s*k⁻¹)=k*(w*s)*k⁻¹ := by group

private theorem positiveRoot_eq_image : positiveRoot=derivedReeHom 0 zSource :=
  positiveRoot_value

private theorem negativeRoot_eq_image :
    negativeRoot=derivedReeHom 0 (MulAut.conjNormal (oppositionFixed 0) zSource) := by
  rw [negativeRoot_value,positiveRoot_eq_image,ambientAction_apply]

def reflectionRoot : CFSG.Models.Tits := derivedReeHom 0 rSource

theorem reflectionRoot_square : reflectionRoot^2=1 :=
  map_period (derivedReeHom 0) rSource 2 (Subtype.ext centralReflection_square)

theorem positiveRoot_square : positiveRoot^2=1 := by
  have hz : centralWord^2=1 := by
    rw [centralWord_eq_conjugate]
    exact map_period (MulAut.conj centralConjugator).toMonoidHom
      ((fourCycle 0)^2) 2 (middle_square_square 0)
  rw [positiveRoot_eq_image]
  exact map_period (derivedReeHom 0) zSource 2 (Subtype.ext hz)

theorem negativeRoot_eq_reflection_conjugate :
    negativeRoot=reflectionRoot*positiveRoot*reflectionRoot⁻¹ := by
  have hs : MulAut.conjNormal (oppositionFixed 0) zSource=
      rSource*zSource*rSource⁻¹ := Subtype.ext negativeCentralWord_eq
  calc
    negativeRoot=derivedReeHom 0 (MulAut.conjNormal (oppositionFixed 0) zSource) :=
      negativeRoot_eq_image
    _=derivedReeHom 0 (rSource*zSource*rSource⁻¹) := congrArg (derivedReeHom 0) hs
    _=reflectionRoot*positiveRoot*reflectionRoot⁻¹ := by
      rw [map_mul,map_mul,map_inv,←positiveRoot_eq_image]
      rfl

theorem reflection_positive_product_order : orderOf (reflectionRoot*positiveRoot)=5 := by
  have hs : rSource*zSource=MulAut.conjNormal centralConjugator (derivedFiveWord 0) := by
    apply Subtype.ext
    change centralReflection*centralWord=centralConjugator*fiveWord 0*centralConjugator⁻¹
    rw [centralWord_eq_conjugate]
    simpa only [centralReflection,fiveWord] using
      conjugate_product centralConjugator (middleFixedWeyl 0) ((fourCycle 0)^2)
  have he : reflectionRoot*positiveRoot=
      ambientAction 0 centralConjugator (originalFiveWord 0) := by
    calc
      _=derivedReeHom 0 (rSource*zSource) := by
        rw [map_mul,←positiveRoot_eq_image]
        rfl
      _=derivedReeHom 0 (MulAut.conjNormal centralConjugator (derivedFiveWord 0)) :=
        congrArg (derivedReeHom 0) hs
      _=ambientAction 0 centralConjugator (originalFiveWord 0) :=
        (ambientAction_apply 0 centralConjugator (derivedFiveWord 0)).symm
  exact (congrArg orderOf he).trans
    ((orderOf_injective (ambientAction 0 centralConjugator).toMonoidHom
      (ambientAction 0 centralConjugator).injective (originalFiveWord 0)).trans
        titsFiveWord_order)

theorem reflectionRoot_recovery :
    reflectionRoot=positiveRoot*(negativeRoot*positiveRoot)^2 := by
  have hp : (reflectionRoot*positiveRoot)^(2*2+1)=1 := by
    change (reflectionRoot*positiveRoot)^5=1
    rw [←reflection_positive_product_order]
    exact pow_orderOf_eq_one _
  have hi : reflectionRoot⁻¹=reflectionRoot := inv_eq_of_mul_eq_one_right
    ((pow_two reflectionRoot).symm.trans reflectionRoot_square)
  have hn : reflectionRoot*positiveRoot*reflectionRoot=negativeRoot := by
    simpa only [hi] using negativeRoot_eq_reflection_conjugate.symm
  have hr := OddInvolutionConjugateRecovery.recovery reflectionRoot positiveRoot 2
    reflectionRoot_square positiveRoot_square hp
  rw [hn] at hr
  exact hr

theorem pairStabilizer_fixes_reflectionRoot (f : pairStabilizer) :
    f.val reflectionRoot=reflectionRoot := by
  calc
    _=f.val (positiveRoot*(negativeRoot*positiveRoot)^2) := congrArg f.val reflectionRoot_recovery
    _=positiveRoot*(negativeRoot*positiveRoot)^2 := by
      rw [map_mul,map_pow,map_mul,pairStabilizer_fixes_positiveRoot,
        pairStabilizer_fixes_negativeRoot]
    _=reflectionRoot := reflectionRoot_recovery.symm

end SymmetricSubgroupAsymptotics.CFSGTitsCentralReflection
