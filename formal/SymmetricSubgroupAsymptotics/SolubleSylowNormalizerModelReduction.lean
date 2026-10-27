import SymmetricSubgroupAsymptotics.SolubleSylowNormalizerSuzuki
import SymmetricSubgroupAsymptotics.CFSGClassificationTransport

/-! Actual model-to-simple transport for the weaker normalizer-pair
assembler. Classification contributes only the original group equivalence. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SolubleSylowNormalizerGeneration
open CFSGReduction

theorem simple_normalizerPairs_of_cfsg_models (hCFSG : CFSG.CFSGClassification)
    (models : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → ∃ p, SolubleSylowNormalizerPrime i.Model p)
    (T : Type) [Group T] [Finite T] [IsSimpleGroup T] (hT : ¬ IsMulCommutative T) :
    ∃ p, SolubleSylowNormalizerPrime T p := by
  let W := simpleModelWitness hCFSG T
  letI : Finite W.index.Model := W.finite_model
  letI : IsSimpleGroup W.index.Model := W.simple_model
  have hn : ¬ IsMulCommutative W.index.Model := by
    intro hc
    exact hT ((isMulCommutative_congr W.equiv).mpr hc)
  obtain ⟨p, hp⟩ := models W.index hn
  exact ⟨p, map W.equiv.symm hp⟩

theorem aschbacherGuralnick_of_cfsg_normalizerPair_models
    (hCFSG : CFSG.CFSGClassification)
    (models : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → ∃ p, SolubleSylowNormalizerPrime i.Model p) :
    MarkedC4.PublishedAschbacherGuralnickSolubleGeneration :=
  aschbacherGuralnick_of_simple_normalizerPairs
    (simple_normalizerPairs_of_cfsg_models hCFSG models)

end SymmetricSubgroupAsymptotics.SolubleSylowNormalizerGeneration
