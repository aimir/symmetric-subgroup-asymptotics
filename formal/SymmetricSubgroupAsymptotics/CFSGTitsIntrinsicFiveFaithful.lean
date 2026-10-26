import SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicFiveAction
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleGradedOriginalImage
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddlePositiveCommutatorIntersection

/-! The selected ACTUAL positive commutator belongs to the intrinsic
normal 2-layer and is moved by the order-five word. Faithful descent of
the OLD graded kernel is used only to transport this SAME witness.
The resulting cyclic order-five action is injective; no Frattini/head
dimension, irreducibility, or outer-order assertion is made. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicFiveFaithful
open CFSGTitsIntrinsicFiveAction CFSGTitsIntrinsicMiddleRadical CFSGTitsMiddleWeylRecovery
open CFSGTitsIntrinsicMiddleSquare CFSGReeFFourMiddleDerivedFiveWord
open CFSGReeFFourMiddleDerivedFiveSurvival CFSGReeFFourMiddleDerivedFiveRootWords
open CFSGReeFFourMiddleGradedOriginalImage CFSGReeFFourMiddleGradedDerivedAction
open CFSGReeFFourMiddleGradedKernel CFSGReeFFourMiddlePositiveKernelIntersection
open CFSGReeFFourMiddlePositiveIntersectionNormalizer CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourOriginalPositiveSylow CFSGReeFFourDerivedAmbientHom
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourRelativePositiveSubgroups
open CFSGReeFFourMiddleSquareCommutator CFSGReeFFourBinaryDerivedGeneration
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev D := commutator (originalModelFixed 0)
private instance derivedFinite : Finite D :=
  Finite.of_injective (derivedAmbientHom 0) (derivedAmbientHom_injective 0)
private instance titsFinite : Finite CFSG.Models.Tits :=
  Finite.of_surjective (derivedReeHom 0) (derivedReeHom_surjective 0)

private theorem map_pair {G H : Type*} [Group G] [Group H]
    (f : G →* H) (w s t : G) (a b : H)
    (ha : a=f w) (hb : b=f s) (ht : w*s=t) : a*b=f t := by
  rw [ha,hb,←map_mul,ht]

theorem fiveElement_original_value : fiveElement=originalFiveWord 0 := by
  let w : D := ⟨middleFixedWeyl 0,middle_weyl_mem_derived 0⟩
  let s : D := ⟨(fourCycle 0)^2,square_mem_derived 0⟩
  have hw : middleWeylRoot=derivedReeHom 0 w := rfl
  have hs : middleSquareRoot=derivedReeHom 0 s := middleSquareRoot_value
  have ht : w*s=derivedFiveWord 0 := Subtype.ext rfl
  exact map_pair (derivedReeHom 0) w s (derivedFiveWord 0)
    middleWeylRoot middleSquareRoot hw hs ht


private def cSource : D := (derivedPositiveCommutator 0).val

private theorem cSource_mem_intersection : cSource∈sourceIntersection :=
  CFSGReeFFourMiddlePositiveCommutatorIntersection.positiveCommutator_mem_intersection 0

def commutatorPoint : middleRadical :=
  ⟨derivedReeHom 0 cSource,by
    rw [←sourceIntersection_image]
    exact ⟨cSource,cSource_mem_intersection,rfl⟩⟩

private theorem commutatorPoint_original_value :
    (commutatorPoint : CFSG.Models.Tits)=kernelToOriginal 0 (kernelCommutator 0) := rfl

private theorem original_kernel_point_moved (m : ℕ) :
    CFSGReeFFourMiddleGradedDerivedAction.fiveAction m (kernelCommutator m)≠kernelCommutator m := by
  intro he
  have hd : derivedFiveWord m*kernelToDerived m (kernelCommutator m)*(derivedFiveWord m)⁻¹=
      kernelToDerived m (kernelCommutator m) :=
    (kernelToDerived_conjugation m (derivedParabolicFiveWord m) (kernelCommutator m)).symm.trans
      (congrArg (kernelToDerived m) he)
  have h := congrArg (fun z : commutator (originalModelFixed m) => z.val) hd
  change fiveWord m*positiveCommutator m*(fiveWord m)⁻¹=positiveCommutator m at h
  exact fiveWord_positiveCommutator_ne m (mul_inv_eq_iff_eq_mul.mp h)

private theorem aut_apply_eq_self {G : Type*} [Group G] (F : MulAut G)
    (h : F=1) (x : G) : F x=x := by rw [h]; rfl

private theorem conjugate_fixed_transport {G : Type*} [Group G] (a b c d : G)
    (ha : a=b) (hc : c=d) (h : a*c*a⁻¹=c) : b*d*b⁻¹=d := by
  simpa only [ha,hc] using h

theorem fiveAction_ne_one : CFSGTitsIntrinsicFiveAction.fiveAction≠1 := by
  intro he
  have hp := aut_apply_eq_self CFSGTitsIntrinsicFiveAction.fiveAction he commutatorPoint
  have hc : fiveElement*(commutatorPoint : CFSG.Models.Tits)*fiveElement⁻¹=commutatorPoint :=
    (CFSGTitsIntrinsicFiveAction.fiveAction_val commutatorPoint).symm.trans
      (congrArg Subtype.val hp)
  have hi : kernelToOriginal 0
      (CFSGReeFFourMiddleGradedDerivedAction.fiveAction 0 (kernelCommutator 0))=
      kernelToOriginal 0 (kernelCommutator 0) := by
    calc
      _=originalFiveWord 0*kernelToOriginal 0 (kernelCommutator 0)*(originalFiveWord 0)⁻¹ :=
        kernelToOriginal_fiveAction 0 (kernelCommutator 0)
      _=kernelToOriginal 0 (kernelCommutator 0) :=
        conjugate_fixed_transport (G := CFSG.Models.Tits) fiveElement (originalFiveWord 0)
          (commutatorPoint : CFSG.Models.Tits) (kernelToOriginal 0 (kernelCommutator 0))
          fiveElement_original_value commutatorPoint_original_value hc
  exact original_kernel_point_moved 0 (kernelToOriginal_injective 0 hi)

theorem fiveAction_order : orderOf CFSGTitsIntrinsicFiveAction.fiveAction=5 :=
  orderOf_eq_prime CFSGTitsIntrinsicFiveAction.fiveAction_pow_five fiveAction_ne_one

private theorem cyclic_le_carrier : Subgroup.zpowers fiveElement≤middleCarrier :=
  Subgroup.zpowers_le.mpr fiveElement_mem_carrier

def cyclicAction : Subgroup.zpowers fiveElement →* MulAut middleRadical :=
  carrierConjugation.comp (Subgroup.inclusion cyclic_le_carrier)

private theorem cyclic_injective {G H : Type*} [Group G] [Finite G] [Group H]
    (g : G) (a : H) (F : Subgroup.zpowers g →* H)
    (hg : orderOf g=5) (ha : orderOf a=5)
    (hF : F ⟨g,Subgroup.mem_zpowers g⟩=a) : Function.Injective F := by
  classical
  apply F.ker_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro x hx
  change F x=1 at hx
  obtain ⟨k,hk,he⟩ := Finset.mem_image.mp
    (mem_zpowers_iff_mem_range_orderOf.mp x.property)
  have hk5 : k<5 := by simpa only [hg] using Finset.mem_range.mp hk
  let u : Subgroup.zpowers g := ⟨g,Subgroup.mem_zpowers g⟩
  have hpow : x=u^k := Subtype.ext he.symm
  have hu : F u=a := hF
  rw [hpow,map_pow,hu] at hx
  have hd : 5∣k := by simpa only [ha] using orderOf_dvd_of_pow_eq_one hx
  have hk0 : k=0 := Nat.eq_zero_of_dvd_of_lt hd hk5
  exact Subgroup.mem_bot.mpr (hpow.trans (by rw [hk0,pow_zero]))

private theorem cyclicAction_generator : cyclicAction
    ⟨fiveElement,Subgroup.mem_zpowers fiveElement⟩=CFSGTitsIntrinsicFiveAction.fiveAction := rfl

theorem cyclicAction_injective : Function.Injective cyclicAction :=
  cyclic_injective fiveElement CFSGTitsIntrinsicFiveAction.fiveAction cyclicAction
    fiveElement_order fiveAction_order cyclicAction_generator

end SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicFiveFaithful
