import SymmetricSubgroupAsymptotics.CFSGTitsOpposedMiddleSquare

/-! Recover the ACTUAL middle Weyl involution from the two intrinsic
middle-square flags, then the ACTUAL opposition inner automorphism.
The order-five input is the checked full-centre survival theorem. This
fixes specific target elements; it does not bound the pair stabilizer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTitsMiddleWeylRecovery
open CFSGTitsOpposedMiddleSquare CFSGTitsIntrinsicMiddleSquare CFSGTitsCentralReflection
open CFSGTitsAmbientPairAlignment CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourBinaryCentralReflection CFSGReeFFourBinaryReflectionMiddleFlag
open CFSGReeFFourBinaryPenultimateWeyl CFSGReeFFourBinaryDerivedGeneration
open CFSGReeFFourBinaryMiddleSquareOpposition
open CFSGReeFFourMiddleDerivedFiveWord CFSGReeFFourMiddleDerivedFiveSurvival
open CFSGReeFFourMiddleSquareCommutator CFSGReeFFourFixedDerivedInversionFacts
open CFSGReeFFourOriginalPositiveSylow CFSGReeFFourAmbientCentralQuotientAction
open CFSGReeFFourRelativePositiveSubgroups CFSGReeFFourOppositionFixedPositiveNegative
private abbrev D := commutator (originalModelFixed 0)
private def wSource : D := ⟨middleFixedWeyl 0,middle_weyl_mem_derived 0⟩
private def sSource : D := ⟨(fourCycle 0)^2,square_mem_derived 0⟩
private def rSource : D := ⟨centralReflection,centralReflection_mem_derived⟩

private theorem squareRoot_eq_image : middleSquareRoot=derivedReeHom 0 sSource :=
  middleSquareRoot_value

private theorem map_period {G H : Type*} [Group G] [Group H]
    (f : G →* H) (x : G) (n : ℕ) (h : x^n=1) : (f x)^n=1 :=
  (map_pow f x n).symm.trans ((congrArg f h).trans (map_one f))

def middleWeylRoot : CFSG.Models.Tits := derivedReeHom 0 wSource

theorem middleWeylRoot_square : middleWeylRoot^2=1 :=
  map_period (derivedReeHom 0) wSource 2 (Subtype.ext (middleWeyl_square 0))

theorem negativeMiddleSquareRoot_eq_conjugate :
    negativeMiddleSquareRoot=middleWeylRoot*middleSquareRoot*middleWeylRoot⁻¹ := by
  have hs : MulAut.conjNormal (oppositionFixed 0) sSource=wSource*sSource*wSource⁻¹ :=
    Subtype.ext binary_opposition_middle_square
  calc
    _=derivedReeHom 0 (MulAut.conjNormal (oppositionFixed 0) sSource) :=
      negativeMiddleSquareRoot_original_value
    _=derivedReeHom 0 (wSource*sSource*wSource⁻¹) := congrArg (derivedReeHom 0) hs
    _=middleWeylRoot*middleSquareRoot*middleWeylRoot⁻¹ := by
      rw [map_mul,map_mul,map_inv,←squareRoot_eq_image]
      rfl

theorem middleWeyl_square_product_order : orderOf (middleWeylRoot*middleSquareRoot)=5 := by
  have hs : wSource*sSource=derivedFiveWord 0 := Subtype.ext rfl
  have he : middleWeylRoot*middleSquareRoot=originalFiveWord 0 := by
    calc
      _=derivedReeHom 0 (wSource*sSource) := by
        rw [map_mul,←squareRoot_eq_image]
        rfl
      _=originalFiveWord 0 := congrArg (derivedReeHom 0) hs
  exact (congrArg orderOf he).trans titsFiveWord_order

theorem middleWeylRoot_recovery :
    middleWeylRoot=middleSquareRoot*(negativeMiddleSquareRoot*middleSquareRoot)^2 := by
  have hp : (middleWeylRoot*middleSquareRoot)^(2*2+1)=1 := by
    change (middleWeylRoot*middleSquareRoot)^5=1
    rw [←middleWeyl_square_product_order]
    exact pow_orderOf_eq_one _
  have hi : middleWeylRoot⁻¹=middleWeylRoot := inv_eq_of_mul_eq_one_right
    ((pow_two middleWeylRoot).symm.trans middleWeylRoot_square)
  have hn : middleWeylRoot*middleSquareRoot*middleWeylRoot=negativeMiddleSquareRoot := by
    simpa only [hi] using negativeMiddleSquareRoot_eq_conjugate.symm
  have hr := OddInvolutionConjugateRecovery.recovery middleWeylRoot middleSquareRoot 2
    middleWeylRoot_square middleSquareRoot_square hp
  rw [hn] at hr
  exact hr

theorem pairStabilizer_fixes_middleWeylRoot (f : pairStabilizer) :
    f.val middleWeylRoot=middleWeylRoot := by
  calc
    _=f.val (middleSquareRoot*(negativeMiddleSquareRoot*middleSquareRoot)^2) :=
      congrArg f.val middleWeylRoot_recovery
    _=middleSquareRoot*(negativeMiddleSquareRoot*middleSquareRoot)^2 := by
      rw [map_mul,map_pow,map_mul,pairStabilizer_fixes_middleSquareRoot,
        pairStabilizer_fixes_negativeMiddleSquareRoot]
    _=middleWeylRoot := middleWeylRoot_recovery.symm

private theorem opposition_product : centralReflection*middleFixedWeyl 0=oppositionFixed 0 := by
  rw [centralReflection_eq_penultimate,binary_short_thirteen_eq,mul_assoc,
    ←pow_two,middleWeyl_square,mul_one]

def oppositionRoot : CFSG.Models.Tits := reflectionRoot*middleWeylRoot

theorem pairStabilizer_fixes_oppositionRoot (f : pairStabilizer) :
    f.val oppositionRoot=oppositionRoot := by
  change f.val (reflectionRoot*middleWeylRoot)=reflectionRoot*middleWeylRoot
  rw [map_mul,pairStabilizer_fixes_reflectionRoot,pairStabilizer_fixes_middleWeylRoot]

theorem oppositionRoot_action :
    MulAut.conj oppositionRoot=ambientAction 0 (oppositionFixed 0) := by
  let o : D := rSource*wSource
  have hv : (o : originalModelFixed 0)=oppositionFixed 0 := opposition_product
  have hi : derivedReeHom 0 o=oppositionRoot := by
    change derivedReeHom 0 (rSource*wSource)=oppositionRoot
    rw [map_mul]
    rfl
  calc
    _=MulAut.conj (derivedReeHom 0 o) := congrArg MulAut.conj hi.symm
    _=ambientAction 0 (o : originalModelFixed 0) := (ambientAction_of_derived 0 o).symm
    _=ambientAction 0 (oppositionFixed 0) := congrArg (ambientAction 0) hv

end SymmetricSubgroupAsymptotics.CFSGTitsMiddleWeylRecovery
