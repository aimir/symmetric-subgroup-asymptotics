import SymmetricSubgroupAsymptotics.CFSGE6GeckGeneratedRootIntersection
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalSimpleParameters
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalCentralKernel
import SymmetricSubgroupAsymptotics.CFSGKernelControlledIntersection

/-! Literal singleton/paired simple-root groups in the ORIGINAL twisted
E6 model are positive-Sylow intersections with the actual opposite
parabolics. Kernel containment, proved from actual centrality, justifies
the intersection image; global source faithfulness is not assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalRootIntersection
open CFSGE6GeckGeneratedRootIntersection CFSGE6GeckFixedOrbitRootGroups
open CFSGE6GeckFixedSimpleParameters CFSGTwistedE6GeckOriginalSimpleParameters
open CFSGTwistedE6GeckOriginalProjection CFSGTwistedE6GeckOriginalOppositeAlignment
open CFSGTwistedE6GeckOriginalCentralKernel CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckRootGeneratedPGroup CFSGKernelControlledIntersection
open CFSGSerreOrdinaryTwists

def originalOppositeParabolic (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (a : Fin 4) :
    Subgroup (CFSG.Models.TwistedE6 q) :=
  (oppositeParabolicGenerated (q.Extension 2) (definingFieldAutomorphism q 2) a).map
    (generatedToOriginal q)

def originalOrbitRoot (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (a : Fin 4) : Subgroup (CFSG.Models.TwistedE6 q) :=
  (fixedOrbitPositive (q.Extension 2) (definingFieldAutomorphism q 2) a).map
    (signedFixedToOriginal q false)

theorem orbitRootGenerated_map_original (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (a : Fin 4) :
    (orbitRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2) a).map
      (generatedToOriginal q)=originalOrbitRoot q a := by
  rw [orbitRootGenerated,Subgroup.map_map]
  rfl

theorem original_kernel_le_oppositeParabolicGenerated (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (a : Fin 4) :
    (generatedToOriginal q).ker≤
      oppositeParabolicGenerated (q.Extension 2) (definingFieldAutomorphism q 2) a :=
  (generatedToOriginal_kernel_le_center q).trans
    ((Subgroup.center_le_normalizer
      (rootPart (q.Extension 2) (definingFieldAutomorphism q 2) true :
        Set (fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2)))).trans
          (negative_normalizer_le_oppositeParabolicGenerated
            (q.Extension 2) (definingFieldAutomorphism q 2) a))

theorem original_positive_inf_oppositeParabolic (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (a : Fin 4) :
    (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q))⊓
      originalOppositeParabolic q a=originalOrbitRoot q a := by
  have h := congrArg (fun S : Subgroup
      (fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2))=>
        S.map (generatedToOriginal q))
    (rootPart_inf_oppositeParabolicGenerated (q.Extension 2)
      (definingFieldAutomorphism q 2) (coefficient_involutive q) a)
  dsimp only at h
  rw [map_inf_eq_of_kernel_le_right (generatedToOriginal q) _ _
    (original_kernel_le_oppositeParabolicGenerated q a),rootPart_positive_original_image,
      orbitRootGenerated_map_original] at h
  exact h

theorem originalOrbitRoot_paired (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (j : Fin 2) :
    originalOrbitRoot q (pairedOrbit j)=(pairedOriginalHom q false j).range := by
  rw [originalOrbitRoot,fixedOrbitPositive_paired (q.Extension 2)
    (definingFieldAutomorphism q 2) (coefficient_involutive q) j,MonoidHom.map_range]
  rfl

theorem originalOrbitRoot_singleton (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (j : Fin 2) :
    originalOrbitRoot q (singletonOrbit j)=(singletonOriginalHom q false j).range := by
  rw [originalOrbitRoot,fixedOrbitPositive_singleton,MonoidHom.map_range]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalRootIntersection
