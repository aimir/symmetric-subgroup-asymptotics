import SymmetricSubgroupAsymptotics.RepresentationDualComp
import SymmetricSubgroupAsymptotics.CubicTwoOrbitDualSubquotientGenerators
import SymmetricSubgroupAsymptotics.OriginalKernelSectionOddRestriction

/-! The same two physical observations control every ORIGINAL normal
quotient, including normals that project nontrivially to the top. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalKernelModuleChart

variable {G T : Type} [Group G] [Group T]
    (pi : G →* T) (A : Rep.{0} (ZMod 2) T)
    (E : OriginalKernelModuleChart pi A)

/-- Exact original kernel-section dual generation; the normal axis is
retained through sectionProjectionOnBase and the descended top map. -/
theorem sectionDualGeneratedBy_two_of_cubic_observation
    (hpi : Function.Surjective pi) (cubic : CyclicThree →* T)
    (observation : A →ₗ[ZMod 2] (Fin 2 → ZMod 2))
    (hseparate : ∀ v : A,
      (∀ c : CyclicThree, observation (A.ρ (cubic c) v)=0) → v=0)
    (N : Subgroup G) [N.Normal] :
    RepresentationGeneratedBy (E.sectionRepresentation pi A N).ρ.dual 2 := by
  let sigma : Representation (ZMod 2) T (E.sectionModule pi A N) :=
    (E.sectionRepresentation pi A N).ρ.comp (sectionTop pi N hpi)
  have hg : RepresentationGeneratedBy sigma.dual 2 :=
    CubicTwoOrbitDualSubquotientGenerators.of_observation A.ρ sigma cubic
      observation hseparate (E.sectionProjectionOnBase pi A N hpi)
      (E.sectionProjectionOnBase_surjective pi A N hpi)
  exact RepresentationGeneratedBy.of_comp
    (E.sectionRepresentation pi A N).ρ.dual (sectionTop pi N hpi) (by
      change RepresentationGeneratedBy
        (Representation.dual ((E.sectionRepresentation pi A N).ρ.comp
          (sectionTop pi N hpi))) _ at hg
      rw [representation_dual_comp] at hg
      exact hg)

end SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
