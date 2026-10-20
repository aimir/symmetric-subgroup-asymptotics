import SymmetricSubgroupAsymptotics.ProductQuartetAffineLinearProjection
import SymmetricSubgroupAsymptotics.BinaryPlaneWreathLinearAction
import SymmetricSubgroupAsymptotics.LinearSemidirectActualImageKernelChart
import SymmetricSubgroupAsymptotics.OriginalKernelSourceEquivTransport

/-! The actual original quartet translation module and its inclusion in
four physical plane coordinates. No splitting is supplied or inferred. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame.QuartetKernel
open BinaryPlanePermutationAffineEquiv
open BinaryPlaneAlternatingKernelPartition (Frame)
open LinearSemidirectSubgroupKernelChart
open BinaryPlaneWreathLinearAction (rho)
variable {X : Type} [Finite X] {T : Subgroup (Equiv.Perm X)}
  (C : ProductBlockFrame T (Fin 4) Plane)

abbrev affine : T →* LinearSemidirectCoprimeSocleBounds.Model rho := C.affineCoordinates
abbrev K := (affine C).range
abbrev originalEquiv : T ≃* K C := C.affineImageEquiv
abbrev B := Image rho (K C)
abbrev imageTop := LinearSemidirectActualImageKernelChart.top rho (K C)
abbrev pi : T →* B C := (imageTop C).comp (originalEquiv C).toMonoidHom
abbrev A := LinearSemidirectActualImageKernelChart.kernelModule rho (K C)

def E : OriginalKernelModuleChart (pi C) (A C) :=
  (LinearSemidirectActualImageKernelChart.originalKernelChart rho (K C)).ofSourceEquiv
    (imageTop C) (A C) (originalEquiv C)

 theorem pi_surjective : Function.Surjective (pi C) :=
  (projection rho (K C)).rangeRestrict_surjective.comp (originalEquiv C).surjective

def inclusion : Representation.IntertwiningMap (A C).ρ
    (BinaryPlaneCyclicWreathUniform.representation (B C)) :=
  LinearSemidirectActualImageKernelChart.inclusion rho (K C)

 theorem inclusion_injective : Function.Injective (inclusion C) :=
  LinearSemidirectActualImageKernelChart.inclusion_injective rho (K C)

 theorem linearImage_eq : B C=C.quartetLinearImage := by
  apply le_antisymm
  · rintro b ⟨k,hk⟩
    obtain ⟨u,hu⟩ := k.property
    refine ⟨u,?_⟩
    change (affine C u).right=b
    rw [hu]
    exact hk
  · rintro b ⟨u,hu⟩
    exact ⟨originalEquiv C u,hu⟩

@[simp] theorem pi_coe (u : T) :
    (pi C u : Frame)=C.quartetLinearProjection u := rfl

 theorem top_lift (h : Equiv.Perm (Fin 4)) (hh : h∈C.top.range) :
    ∃ b : B C,(b : Frame).right=h := by
  obtain ⟨u,hu⟩ := hh
  exact ⟨pi C u,hu⟩

end SymmetricSubgroupAsymptotics.ProductBlockFrame.QuartetKernel
