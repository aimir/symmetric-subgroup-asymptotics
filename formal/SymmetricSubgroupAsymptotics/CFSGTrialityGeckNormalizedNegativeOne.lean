import SymmetricSubgroupAsymptotics.CFSGCentralRootNegativeOneRigidity
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortRankOneConstraint
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRankOneConstraint
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalSimpleParameterRanges
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSimpleSignedGeneration

/-! Fixing the positive parameter one forces both opposite negative
parameters minus one in the SAME original model. All rank-one word,
p-element, central quotient, and intrinsic range premises are discharged
from actual triality data. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckNormalizedNegativeOne
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckSignedSimpleParameters CFSGTrialityGeckOriginalSimpleParameters
open CFSGTrialityGeckOriginalSimpleParameterRanges CFSGTrialityGeckOriginalSignedRootAction
open CFSGTrialityGeckOriginalRootFamily CFSGTrialityGeckOriginalOppositeAlignment
open CFSGTrialityGeckOriginalNegativeRootIntersection CFSGTrialityGeckRootGeneratedPGroup
open CFSGTrialityGeckGeneratedPositiveSylow CFSGTrialityGeckGeneratedOriginalProjection
open CFSGTrialityGeckGeneratedOriginalCentralKernel CFSGTrialityGeckRelativeRootGenerated
open CFSGTrialityGeckFixedRootWords CFSGTrialityGeckSimpleChartWeyl
open CFSGTrialityGeckSimpleOrbitFlags CFSGTrialityGeckOvergroupWeylExtraction
open CFSGTrialityGeckShortRankOneConstraint CFSGNormTwoGeckRankOneConstraint
open CFSGCentralRootNegativeOneRigidity CFSGTrialityFixedField
open CFSGSerreOrdinaryTwists CFSGSerreQuadraticWeylWord CFSGSerreQuadraticMatrix
local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _

private theorem injective_subtype_of_eq {G H : Type*} [Group G] [Group H]
    (f : G→*H) (P Q : Subgroup G) (he : P=Q)
    (hinj : Function.Injective (f.comp Q.subtype)) : Function.Injective (f.comp P.subtype) := by
  subst P
  exact hinj

private theorem positive_sylow_injective (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    Function.Injective ((generatedToOriginal q).comp
      (generatedPositiveSylow q : Subgroup
        (fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3))).subtype) :=
  injective_subtype_of_eq (generatedToOriginal q) _ _
    (generatedPositiveSylow_coe q) (rootPart_positive_original_injective q)

private theorem short_p_element (q : CFSG.PrimePower) (neg : Bool)
    (t : Multiplicative (q.Extension 3)) : ∃k:ℕ,(shortGeneratedHom q neg t)^(q.prime^k)=1 := by
  obtain ⟨k,hk⟩ := (rootPart_isPGroup (q.Extension 3) (definingFieldAutomorphism q 3) q.prime neg)
    ⟨shortGeneratedHom q neg t,shortGeneratedHom_mem_rootPart q neg t⟩
  exact ⟨k,congrArg Subtype.val hk⟩

private theorem middle_p_element (q : CFSG.PrimePower) (neg : Bool)
    (t : Multiplicative (fixedField q)) : ∃k:ℕ,(middleGeneratedHom q neg t)^(q.prime^k)=1 := by
  obtain ⟨k,hk⟩ := (rootPart_isPGroup (q.Extension 3) (definingFieldAutomorphism q 3) q.prime neg)
    ⟨middleGeneratedHom q neg t,middleGeneratedHom_mem_rootPart q neg t⟩
  exact ⟨k,congrArg Subtype.val hk⟩

private theorem short_weyl_one (q : CFSG.PrimePower) :
    (shortGeneratedHom q false (Multiplicative.ofAdd 1)*shortGeneratedHom q true (Multiplicative.ofAdd (-1))*
        shortGeneratedHom q false (Multiplicative.ofAdd 1))*shortGeneratedHom q false (Multiplicative.ofAdd 1)*
      (shortGeneratedHom q false (Multiplicative.ofAdd 1)*shortGeneratedHom q true (Multiplicative.ofAdd (-1))*
        shortGeneratedHom q false (Multiplicative.ofAdd 1))⁻¹=
      shortGeneratedHom q true (Multiplicative.ofAdd (-1)) := by
  apply Subtype.ext
  have hw := orbit_word_parameter (q.Extension 3) (definingFieldAutomorphism q 3) false
  change canonicalWord rawData (q.Extension 3) (orbitWord false)=
    shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false 1*
      shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) true (-1)*
      shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false 1 at hw
  change (shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false 1*
    shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) true (-1)*
    shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false 1)*shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false 1*
    (shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false 1*
    shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) true (-1)*
    shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false 1)⁻¹=shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) true (-1)
  rw [←hw]
  exact short_word_conjugates _ _ 1

private theorem middle_weyl_one (q : CFSG.PrimePower) :
    (middleGeneratedHom q false (Multiplicative.ofAdd 1)*middleGeneratedHom q true (Multiplicative.ofAdd (-1))*
        middleGeneratedHom q false (Multiplicative.ofAdd 1))*middleGeneratedHom q false (Multiplicative.ofAdd 1)*
      (middleGeneratedHom q false (Multiplicative.ofAdd 1)*middleGeneratedHom q true (Multiplicative.ofAdd (-1))*
        middleGeneratedHom q false (Multiplicative.ofAdd 1))⁻¹=
      middleGeneratedHom q true (Multiplicative.ofAdd (-1)) := by
  apply Subtype.ext
  have hw := orbit_word_parameter (q.Extension 3) (definingFieldAutomorphism q 3) true
  change canonicalWord rawData (q.Extension 3) (orbitWord true)=
    canonicalRoot rawData (q.Extension 3) false 1 1*canonicalRoot rawData (q.Extension 3) true 1 (-1)*
      canonicalRoot rawData (q.Extension 3) false 1 1 at hw
  change (canonicalRoot rawData (q.Extension 3) false 1 1*canonicalRoot rawData (q.Extension 3) true 1 (-1)*
    canonicalRoot rawData (q.Extension 3) false 1 1)*canonicalRoot rawData (q.Extension 3) false 1 1*
    (canonicalRoot rawData (q.Extension 3) false 1 1*canonicalRoot rawData (q.Extension 3) true 1 (-1)*
    canonicalRoot rawData (q.Extension 3) false 1 1)⁻¹=canonicalRoot rawData (q.Extension 3) true 1 (-1)
  rw [←hw]
  exact middle_word_conjugates _ 1

theorem short_negative_one_fixed (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (f : MulAut (CFSG.Models.TrialityD4 q))
    (hp : (originalSylow q).map f.toMonoidHom=originalSylow q)
    (hn : (originalNegative q).map f.toMonoidHom=originalNegative q)
    (h1 : f (originalShortHom q false (Multiplicative.ofAdd 1))=
      originalShortHom q false (Multiplicative.ofAdd 1)) :
    f (originalShortHom q true (Multiplicative.ofAdd (-1)))=
      originalShortHom q true (Multiplicative.ofAdd (-1)) := by
  have hY : (originalShortHom q true).range.map f.toMonoidHom=(originalShortHom q true).range := by
    have hr : (originalShortHom q true).range=originalNegativeOrbitRoot q false := originalShortHom_range q true
    rw [hr]
    exact (original_pair_fixer_fixes_signed_roots q f hp hn).2 false
  apply negative_one_fixed (generatedToOriginal q) (generatedPositiveSylow q)
    (positive_sylow_injective q) (generatedToOriginal_kernel_le_center q)
    (shortGeneratedHom q false) (shortGeneratedHom q true) (originalShortHom_injective q true)
    (short_p_element q false) (short_p_element q true) (short_weyl_one q) _ f hY h1
  intro b hb hinter
  have he := congrArg (fun z : fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3)=>z.val) hinter
  have hc := short_word_inverse_constraint (q.Extension 3) (definingFieldAutomorphism q 3) 1 b 1 b hb he
  linear_combination hc

theorem middle_negative_one_fixed (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (f : MulAut (CFSG.Models.TrialityD4 q))
    (hp : (originalSylow q).map f.toMonoidHom=originalSylow q)
    (hn : (originalNegative q).map f.toMonoidHom=originalNegative q)
    (h1 : f (originalMiddleHom q false (Multiplicative.ofAdd 1))=
      originalMiddleHom q false (Multiplicative.ofAdd 1)) :
    f (originalMiddleHom q true (Multiplicative.ofAdd (-1)))=
      originalMiddleHom q true (Multiplicative.ofAdd (-1)) := by
  have hY : (originalMiddleHom q true).range.map f.toMonoidHom=(originalMiddleHom q true).range := by
    have hr : (originalMiddleHom q true).range=originalNegativeOrbitRoot q true := originalMiddleHom_range q true
    rw [hr]
    exact (original_pair_fixer_fixes_signed_roots q f hp hn).2 true
  apply negative_one_fixed (generatedToOriginal q) (generatedPositiveSylow q)
    (positive_sylow_injective q) (generatedToOriginal_kernel_le_center q)
    (middleGeneratedHom q false) (middleGeneratedHom q true) (originalMiddleHom_injective q true)
    (middle_p_element q false) (middle_p_element q true) (middle_weyl_one q) _ f hY h1
  intro b hb hinter
  have he := congrArg (fun z : fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3)=>z.val) hinter
  have hb0 : b.val≠0 := by intro h; exact hb (Subtype.ext h)
  have hc := canonical_word_inverse_constraint (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index (q.Extension 3) 1 1 b.val 1 b.val hb0 he
  apply Subtype.ext
  change b.val=(-1:q.Extension 3)
  linear_combination hc

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckNormalizedNegativeOne
