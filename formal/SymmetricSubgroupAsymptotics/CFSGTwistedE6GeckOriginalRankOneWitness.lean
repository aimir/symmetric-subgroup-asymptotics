import SymmetricSubgroupAsymptotics.CFSGE6GeckRelativeSimpleHom
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalRootIntersection
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalNegativeRootAction
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalPairAlignment
import SymmetricSubgroupAsymptotics.CFSGRankOneNoncommutation

/-! Actual parameter-one witnesses distinguish matching opposite root
labels in the ORIGINAL group. Only literal rank-one word identities,
signed restriction injectivity and disjoint Sylows are used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalRankOneWitness
open CFSGE6GeckRelativeSimpleHom CFSGE6GeckFixedOrbitRootGroups
open CFSGE6GeckSignedSimpleParameters CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckRootGeneratedPGroup
open CFSGTwistedE6GeckOriginalProjection CFSGTwistedE6GeckOriginalOppositeAlignment
open CFSGTwistedE6GeckOriginalSimpleParameters CFSGTwistedE6GeckOriginalRootIntersection
open CFSGTwistedE6GeckOriginalNegativeRootAction CFSGTwistedE6GeckOriginalPairAlignment
open CFSGSerreOrdinaryTwists

def orbitOneInGenerated (q : CFSG.PrimePower) (neg : Bool) (a : Fin 4) :
    fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2) :=
  ⟨rawOrbitHom (q.Extension 2) (definingFieldAutomorphism q 2) neg a (Multiplicative.ofAdd 1),by
    rw [rawOrbitHom_one_parameter]
    exact orbitParameter_mem_generated (q.Extension 2) (definingFieldAutomorphism q 2) neg a 1
      (map_one _)⟩

def originalOrbitOne (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (neg : Bool) (a : Fin 4) : CFSG.Models.TwistedE6 q :=
  generatedToOriginal q (orbitOneInGenerated q neg a)

theorem originalOrbitOne_paired (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (neg : Bool) (j : Fin 2) :
    originalOrbitOne q neg (pairedOrbit j)=pairedOriginalHom q neg j (Multiplicative.ofAdd 1) := by
  apply congrArg (generatedToOriginal q)
  apply Subtype.ext
  fin_cases j <;> rfl

theorem originalOrbitOne_singleton (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (neg : Bool) (j : Fin 2) :
    originalOrbitOne q neg (singletonOrbit j)=singletonOriginalHom q neg j (Multiplicative.ofAdd 1) := by
  apply congrArg (generatedToOriginal q)
  apply Subtype.ext
  fin_cases j <;> rfl

private theorem one_parameter_ne_one {F G : Type*} [Field F] [Group G]
    (f : Multiplicative F→*G) (hf : Function.Injective f) : f (Multiplicative.ofAdd 1)≠1 := by
  intro he
  have h := hf (he.trans (map_one f).symm)
  have hz : (1 : F)=0 := congrArg (fun a : Multiplicative F=>a.toAdd) h
  exact one_ne_zero hz

theorem originalOrbitOne_ne_one (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (neg : Bool) (a : Fin 4) :
    originalOrbitOne q neg a≠1 := by
  have hp (j : Fin 2) : originalOrbitOne q neg (pairedOrbit j)≠1 := by
    rw [originalOrbitOne_paired]
    exact one_parameter_ne_one _ (pairedOriginalHom_injective q neg j)
  have hs (j : Fin 2) : originalOrbitOne q neg (singletonOrbit j)≠1 := by
    rw [originalOrbitOne_singleton]
    exact one_parameter_ne_one _ (singletonOriginalHom_injective q neg j)
  fin_cases a
  · exact hp 0
  · exact hp 1
  · exact hs 1
  · exact hs 0

theorem originalOrbitOne_positive_mem (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (a : Fin 4) :
    originalOrbitOne q false a∈originalOrbitRoot q a := by
  have hp (j : Fin 2) : originalOrbitOne q false (pairedOrbit j)∈originalOrbitRoot q (pairedOrbit j) := by
    rw [originalOrbitOne_paired,originalOrbitRoot_paired]
    exact ⟨Multiplicative.ofAdd 1,rfl⟩
  have hs (j : Fin 2) : originalOrbitOne q false (singletonOrbit j)∈originalOrbitRoot q (singletonOrbit j) := by
    rw [originalOrbitOne_singleton,originalOrbitRoot_singleton]
    exact ⟨Multiplicative.ofAdd 1,rfl⟩
  fin_cases a
  · exact hp 0
  · exact hp 1
  · exact hs 1
  · exact hs 0

theorem originalOrbitOne_negative_mem (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (a : Fin 4) :
    originalOrbitOne q true a∈originalNegativeOrbitRoot q a := by
  have hp (j : Fin 2) : originalOrbitOne q true (pairedOrbit j)∈originalNegativeOrbitRoot q (pairedOrbit j) := by
    rw [originalOrbitOne_paired,originalNegativeOrbitRoot_paired]
    exact ⟨Multiplicative.ofAdd 1,rfl⟩
  have hs (j : Fin 2) : originalOrbitOne q true (singletonOrbit j)∈originalNegativeOrbitRoot q (singletonOrbit j) := by
    rw [originalOrbitOne_singleton,originalNegativeOrbitRoot_singleton]
    exact ⟨Multiplicative.ofAdd 1,rfl⟩
  fin_cases a
  · exact hp 0
  · exact hp 1
  · exact hs 1
  · exact hs 0

theorem original_same_orbit_not_commute (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (a : Fin 4) :
    ¬Commute (originalOrbitOne q false a) (originalOrbitOne q true a) := by
  have hsep : originalOrbitOne q false a≠(originalOrbitOne q true a)⁻¹ := by
    intro he
    obtain ⟨S,hS,hdisj⟩ := original_negative_is_sylow q
    rw [hS] at hdisj
    have hU : originalOrbitOne q false a∈(originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)) :=
      (inf_le_left : (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q))⊓
        originalOppositeParabolic q a≤_) (by
          rw [original_positive_inf_oppositeParabolic]
          exact originalOrbitOne_positive_mem q a)
    have hV : originalOrbitOne q true a∈originalNegative q :=
      (inf_le_left : originalNegative q⊓CFSGTwistedE6GeckOriginalUpperNormalizer.originalSimpleParabolic q a≤_)
        (by rw [original_negative_inf_simpleParabolic];exact originalOrbitOne_negative_mem q a)
    have hm : originalOrbitOne q false a∈(originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q))⊓
        originalNegative q := ⟨hU,by rw [he];exact (originalNegative q).inv_mem hV⟩
    rw [hdisj,Subgroup.mem_bot] at hm
    exact originalOrbitOne_ne_one q false a hm
  apply CFSGRankOneNoncommutation.not_commute _ _ hsep
  have href :
      (orbitOneInGenerated q false a*(orbitOneInGenerated q true a)⁻¹*orbitOneInGenerated q false a)*
        orbitOneInGenerated q false a*
      (orbitOneInGenerated q false a*(orbitOneInGenerated q true a)⁻¹*orbitOneInGenerated q false a)⁻¹=
        (orbitOneInGenerated q true a)⁻¹ := by
    apply Subtype.ext
    change (rawOrbitHom (q.Extension 2) (definingFieldAutomorphism q 2) false a (Multiplicative.ofAdd 1)*
      (rawOrbitHom (q.Extension 2) (definingFieldAutomorphism q 2) true a (Multiplicative.ofAdd 1))⁻¹*
      rawOrbitHom (q.Extension 2) (definingFieldAutomorphism q 2) false a (Multiplicative.ofAdd 1))*_*
      (rawOrbitHom (q.Extension 2) (definingFieldAutomorphism q 2) false a (Multiplicative.ofAdd 1)*
      (rawOrbitHom (q.Extension 2) (definingFieldAutomorphism q 2) true a (Multiplicative.ofAdd 1))⁻¹*
      rawOrbitHom (q.Extension 2) (definingFieldAutomorphism q 2) false a (Multiplicative.ofAdd 1))⁻¹=_
    rw [←rawOrbitHom_word]
    exact rawOrbitHom_reflection (q.Extension 2) (definingFieldAutomorphism q 2) a
  simpa only [map_mul,map_inv] using congrArg (generatedToOriginal q) href

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalRankOneWitness
