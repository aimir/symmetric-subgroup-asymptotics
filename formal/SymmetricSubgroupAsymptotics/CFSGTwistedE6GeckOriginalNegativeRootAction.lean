import SymmetricSubgroupAsymptotics.CFSGE6GeckNegativeParabolicRootIntersection
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalParabolicAction
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalSimpleParameters
import SymmetricSubgroupAsymptotics.CFSGKernelControlledIntersection

/-! Complete negative simple charts in the ORIGINAL twisted E6 group
are intrinsic intersections with the positive minimal parabolics. A
pair-preserving original automorphism therefore permutes this negative
family, without a source lift or folded-abelianization premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalNegativeRootAction
open CFSGE6GeckNegativeParabolicRootIntersection CFSGE6GeckNegativeOrbitRootGroups
open CFSGE6GeckFixedOrbitRootGroups CFSGE6GeckGeneratedParabolics
open CFSGTwistedE6GeckOriginalParabolicAction CFSGTwistedE6GeckOriginalUpperNormalizer
open CFSGTwistedE6GeckOriginalProjection CFSGTwistedE6GeckOriginalOppositeAlignment
open CFSGTwistedE6GeckOriginalSimpleParameters CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckRootGeneratedPGroup CFSGKernelControlledIntersection CFSGSerreOrdinaryTwists

def originalNegativeOrbitRoot (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (a : Fin 4) : Subgroup (CFSG.Models.TwistedE6 q) :=
  (fixedOrbitNegative (q.Extension 2) (definingFieldAutomorphism q 2) a).map
    (signedFixedToOriginal q true)

theorem negativeOrbitRootGenerated_map_original (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (a : Fin 4) :
    (negativeOrbitRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2) a).map
      (generatedToOriginal q)=originalNegativeOrbitRoot q a := by
  rw [negativeOrbitRootGenerated,Subgroup.map_map]
  rfl

theorem original_negative_inf_simpleParabolic (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (a : Fin 4) :
    originalNegative q⊓originalSimpleParabolic q a=originalNegativeOrbitRoot q a := by
  have hk : (generatedToOriginal q).ker≤parabolicGenerated (q.Extension 2)
      (definingFieldAutomorphism q 2) a :=
    (original_kernel_le_upperGenerated q).trans
      (upperGenerated_lt_parabolicGenerated (q.Extension 2) (definingFieldAutomorphism q 2) a).le
  have h := congrArg (fun S : Subgroup
      (fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2))=>
        S.map (generatedToOriginal q))
    (negative_rootPart_inf_parabolicGenerated (q.Extension 2)
      (definingFieldAutomorphism q 2) (coefficient_involutive q) a)
  dsimp only at h
  rw [map_inf_eq_of_kernel_le_right (generatedToOriginal q) _ _ hk,
    negativeOrbitRootGenerated_map_original] at h
  exact h

theorem originalNegativeOrbitRoot_paired (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (j : Fin 2) :
    originalNegativeOrbitRoot q (pairedOrbit j)=(pairedOriginalHom q true j).range := by
  rw [originalNegativeOrbitRoot,fixedOrbitNegative_paired (q.Extension 2)
    (definingFieldAutomorphism q 2) (coefficient_involutive q) j,MonoidHom.map_range]
  rfl

theorem originalNegativeOrbitRoot_singleton (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (j : Fin 2) :
    originalNegativeOrbitRoot q (singletonOrbit j)=(singletonOriginalHom q true j).range := by
  rw [originalNegativeOrbitRoot,fixedOrbitNegative_singleton,MonoidHom.map_range]
  rfl

theorem exists_original_negative_root_permutation (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (f : MulAut (CFSG.Models.TwistedE6 q))
    (hU : (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)).map f.toMonoidHom=
      (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)))
    (hV : (originalNegative q).map f.toMonoidHom=originalNegative q) :
    ∃sigma : Equiv.Perm (Fin 4),∀a : Fin 4,
      (originalNegativeOrbitRoot q a).map f.toMonoidHom=originalNegativeOrbitRoot q (sigma a) := by
  obtain ⟨sigma,hsigma⟩ := exists_original_parabolic_permutation q f hU
  refine ⟨sigma,fun a=>?_⟩
  rw [←original_negative_inf_simpleParabolic q a,
    Subgroup.map_inf _ _ _ f.injective,hV,hsigma a,original_negative_inf_simpleParabolic]

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalNegativeRootAction
