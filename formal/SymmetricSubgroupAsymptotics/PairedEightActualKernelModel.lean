import SymmetricSubgroupAsymptotics.PairTopNaturalCoordinateDualTransport
import SymmetricSubgroupAsymptotics.PairedEightNaturalDualCapacityDispatch
import SymmetricSubgroupAsymptotics.OriginalKernelTargetEquivTransport

/-! A physical eight-pair frame and an ACTUAL permutation-coordinate
conjugacy to one checked top construct the original kernel source package. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PairedEightActualKernelModel
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoPairedEightSharedTops

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8)) (j : Fin 24)
    (e : F.top.range ≃* (interface j).top)
    (coords : Fin 8 ≃ Fin 8)
    (hact : ∀ (p : F.top.range) (i : Fin 8), coords ((p : Equiv.Perm (Fin 8)) i)=
      (e p : Equiv.Perm (Fin 8)) (coords i))

def top : U →* (interface j).top := e.toMonoidHom.comp F.top.rangeRestrict

theorem top_surjective : Function.Surjective (top F j e) :=
  e.surjective.comp F.top.rangeRestrict_surjective

def kernelModule : Rep (ZMod 2) (interface j).top :=
  OriginalKernelModuleChart.targetRep F.actualKernelModule e

def kernelChart : OriginalKernelModuleChart (top F j e) (kernelModule F j e) :=
  OriginalKernelModuleChart.ofTargetEquiv F.top.rangeRestrict F.actualKernelModule
    F.actualOriginalKernelChart e

include hact in
theorem kernel_dual_uniform : UniformSubrepresentationGeneratorBound
    (kernelModule F j e).ρ.dual (naturalCapacity j) := by
  have ha := PairTopNaturalCoordinateDualTransport.dual_uniform F.top.range
    (interface j).top e coords hact (natural_dual_uniform j)
  have hk := F.actualKernelDualUniform ha
  change UniformSubrepresentationGeneratorBound
    (Representation.dual ((F.actualKernelModule).ρ.comp e.symm.toMonoidHom)) _
  rw [representation_dual_comp]
  exact hk.comp_of_surjective _ e.symm.toMonoidHom e.symm.surjective

include hact in
theorem all_original_sections_dual_generated
    (N : Subgroup U) [N.Normal] :
    RepresentationGeneratedBy
      ((kernelChart F j e).sectionRepresentation (top F j e)
        (kernelModule F j e) N).ρ.dual (naturalCapacity j) :=
  (kernelChart F j e).sectionDualGeneratedBy_of_uniform (top F j e)
    (kernelModule F j e) (top_surjective F j e)
    (kernel_dual_uniform F j e coords hact) N

end SymmetricSubgroupAsymptotics.PairedEightActualKernelModel
