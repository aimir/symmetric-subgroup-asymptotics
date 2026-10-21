import SymmetricSubgroupAsymptotics.CFSGSuzukiSolubleGeneration
import SymmetricSubgroupAsymptotics.CFSGClassificationTransport

/-! The concrete CFSG boundary of the generic Suzuki induction. The
model obligations remain explicit actual Sylow/normalizer/generation
statements; classification supplies only the original isomorphism. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

theorem simple_goodSylow_of_cfsg_models (hCFSG : CFSG.CFSGClassification)
    (models : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → ∃ p, GoodSylowPrime i.Model p)
    (T : Type) [Group T] [Finite T] [IsSimpleGroup T] (hT : ¬ IsMulCommutative T) :
    ∃ p, GoodSylowPrime T p := by
  let W := simpleModelWitness hCFSG T
  letI suzukiModel_finite : Finite W.index.Model := W.finite_model
  letI suzukiModel_simple : IsSimpleGroup W.index.Model := W.simple_model
  have hn : ¬ IsMulCommutative W.index.Model := by
    intro hc
    exact hT ((isMulCommutative_congr W.equiv).mpr hc)
  obtain ⟨p, hp⟩ := models W.index hn
  exact ⟨p, goodSylowPrime_map W.equiv.symm hp⟩

theorem aschbacherGuralnick_of_cfsg_goodSylow_models (hCFSG : CFSG.CFSGClassification)
    (models : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → ∃ p, GoodSylowPrime i.Model p) :
    MarkedC4.PublishedAschbacherGuralnickSolubleGeneration :=
  aschbacherGuralnick_of_simple_goodSylow (simple_goodSylow_of_cfsg_models hCFSG models)

end SymmetricSubgroupAsymptotics.CFSGReduction
