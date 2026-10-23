import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSignedSimpleParameters
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalNegativeRootCardinality

/-! The four signed parameter homomorphisms inject into the SAME
original triality model. Separation uses its actual central quotient
and a proved Sylow injection, rather than faithfulness of a source Lie
representation. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalSimpleParameters
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckSignedSimpleParameters CFSGTrialityGeckRelativeRootGenerated
open CFSGTrialityGeckRootGeneratedPGroup CFSGTrialityGeckGeneratedOriginalProjection
open CFSGTrialityGeckGeneratedOriginalCentralKernel CFSGTrialityGeckGeneratedPositiveSylow
open CFSGTrialityGeckFixedRootWords CFSGTrialityGeckRootSubgroupTwist
open CFSGTrialityGeckMatrixTwist CFSGTrialityFixedField CFSGSerreOrdinaryTwists
open CFSGSerreQuadraticMatrix CFSGTrialityGeckFixedShortComplementFactor
local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _

private theorem injective_subtype_of_eq {G H : Type*} [Group G] [Group H]
    (f : G→*H) (P Q : Subgroup G) (he : P=Q)
    (hinj : Function.Injective (f.comp Q.subtype)) : Function.Injective (f.comp P.subtype) := by
  subst P
  exact hinj

theorem original_injective_on_rootPart (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (neg : Bool) :
    Function.Injective ((generatedToOriginal q).comp
      (rootPart (q.Extension 3) (definingFieldAutomorphism q 3) neg).subtype) := by
  have hpinj : Function.Injective ((generatedToOriginal q).comp
      (generatedPositiveSylow q : Subgroup
        (fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3))).subtype) :=
    injective_subtype_of_eq (generatedToOriginal q) _ _
      (generatedPositiveSylow_coe q) (rootPart_positive_original_injective q)
  exact CFSGCentralKernelPElements.p_subgroup_injective (generatedToOriginal q)
    (generatedPositiveSylow q) hpinj (generatedToOriginal_kernel_le_center q) _
    (rootPart_isPGroup _ _ q.prime neg)

theorem shortGeneratedHom_mem_rootPart (q : CFSG.PrimePower) (neg : Bool)
    (t : Multiplicative (q.Extension 3)) :
    shortGeneratedHom q neg t∈rootPart (q.Extension 3) (definingFieldAutomorphism q 3) neg :=
  ⟨shortOrbit_mem_rootGroup _ _ neg t.toAdd,
    CFSGTrialityGeckFixedRootWords.actual_shortOrbit_fixed q neg t.toAdd⟩

theorem middleGeneratedHom_mem_rootPart (q : CFSG.PrimePower) (neg : Bool)
    (t : Multiplicative (fixedField q)) :
    middleGeneratedHom q neg t∈rootPart (q.Extension 3) (definingFieldAutomorphism q 3) neg := by
  refine ⟨Subgroup.subset_closure ⟨(1,t.toAdd.val),rfl⟩,?_⟩
  change unitTwist (q.Extension 3) (definingFieldAutomorphism q 3)
    (canonicalRoot rawData (q.Extension 3) neg 1 t.toAdd.val)=
      canonicalRoot rawData (q.Extension 3) neg 1 t.toAdd.val
  rw [unitTwist_raw_root]
  have ht : definingFieldAutomorphism q 3 t.toAdd.val=t.toAdd.val := t.toAdd.property
  change canonicalRoot rawData (q.Extension 3) neg 1
    (definingFieldAutomorphism q 3 t.toAdd.val)=canonicalRoot rawData (q.Extension 3) neg 1 t.toAdd.val
  rw [ht]

def originalShortHom (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TrialityD4 q)]
    (neg : Bool) : Multiplicative (q.Extension 3)→*CFSG.Models.TrialityD4 q :=
  (generatedToOriginal q).comp (shortGeneratedHom q neg)

def originalMiddleHom (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TrialityD4 q)]
    (neg : Bool) : Multiplicative (fixedField q)→*CFSG.Models.TrialityD4 q :=
  (generatedToOriginal q).comp (middleGeneratedHom q neg)

theorem originalShortHom_injective (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (neg : Bool) :
    Function.Injective (originalShortHom q neg) := by
  intro t u he
  have hh := original_injective_on_rootPart q neg
    (show (generatedToOriginal q).comp (rootPart _ _ neg).subtype
        ⟨shortGeneratedHom q neg t,shortGeneratedHom_mem_rootPart q neg t⟩=
      (generatedToOriginal q).comp (rootPart _ _ neg).subtype
        ⟨shortGeneratedHom q neg u,shortGeneratedHom_mem_rootPart q neg u⟩ from he)
  have hraw := congrArg (fun z : rootPart (q.Extension 3) (definingFieldAutomorphism q 3) neg=>z.val.val) hh
  exact short_parameter_injective q neg hraw

theorem originalMiddleHom_injective (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (neg : Bool) :
    Function.Injective (originalMiddleHom q neg) := by
  intro t u he
  have hh := original_injective_on_rootPart q neg
    (show (generatedToOriginal q).comp (rootPart _ _ neg).subtype
        ⟨middleGeneratedHom q neg t,middleGeneratedHom_mem_rootPart q neg t⟩=
      (generatedToOriginal q).comp (rootPart _ _ neg).subtype
        ⟨middleGeneratedHom q neg u,middleGeneratedHom_mem_rootPart q neg u⟩ from he)
  exact middleRawHom_injective q neg
    (congrArg (fun z : rootPart (q.Extension 3) (definingFieldAutomorphism q 3) neg=>z.val.val) hh)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalSimpleParameters
