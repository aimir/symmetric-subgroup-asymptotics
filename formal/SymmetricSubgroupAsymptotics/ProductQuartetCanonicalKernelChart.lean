import SymmetricSubgroupAsymptotics.ProductQuartetCanonicalAffineCoordinates
import SymmetricSubgroupAsymptotics.BinaryPlaneFunctionLinearAction
import SymmetricSubgroupAsymptotics.LinearSemidirectActualImageKernelChart
import SymmetricSubgroupAsymptotics.OriginalKernelSourceEquivTransport

/-! The exact original translation chart for a canonical coarse-top
reindexing. The original source and its normal subgroups are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame.CanonicalQuartetKernel
open BinaryPlanePermutationAffineEquiv
open LinearSemidirectSubgroupKernelChart
open BinaryPlaneFunctionLinearAction (rho)

variable {X I R J : Type} [Finite X] [Fintype J] [DecidableEq J]
  [Group R] [MulAction R J]
  {T : Subgroup (Equiv.Perm X)}
  (C : ProductBlockFrame T I Plane) (e : C.top.range ≃* R) (c : I ≃ J)
  (hc : ∀ b : C.top.range,∀ i : I,c (b • i)=e b • c i)

def affine : T →* LinearSemidirectCoprimeSocleBounds.Model (rho (R := R) (I := J)) where
  toFun u := ⟨Multiplicative.ofAdd (fun j => ((C.canonicalAffine e c hc u).left j).toAdd),
    (C.canonicalAffine e c hc u).right⟩
  map_one' := by
    apply SemidirectProduct.ext
    · change Multiplicative.ofAdd (fun j => ((C.canonicalAffine e c hc 1).left j).toAdd)=1
      rw [map_one]
      rfl
    · change (C.canonicalAffine e c hc 1).right=1
      exact congrArg (fun z : BinaryPlanePermutationWreathCoordinates.Model (R := R) (I := J) => z.right)
        (C.canonicalAffine e c hc).map_one
  map_mul' u v := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      funext j
      exact congrArg (fun z => (z.left j).toAdd) ((C.canonicalAffine e c hc).map_mul u v)
    · change (C.canonicalAffine e c hc (u*v)).right=
        (C.canonicalAffine e c hc u).right*(C.canonicalAffine e c hc v).right
      exact congrArg (fun z : BinaryPlanePermutationWreathCoordinates.Model (R := R) (I := J) => z.right)
        ((C.canonicalAffine e c hc).map_mul u v)

theorem affine_injective : Function.Injective (affine C e c hc) := by
  intro u v h
  apply C.canonicalAffine_injective e c hc
  apply SemidirectProduct.ext
  · funext j
    apply Multiplicative.toAdd.injective
    exact congrArg (fun z => z.left.toAdd j) h
  · exact congrArg (fun z : LinearSemidirectCoprimeSocleBounds.Model
      (rho (R := R) (I := J)) => z.right) h

abbrev K := (affine C e c hc).range
abbrev originalEquiv : T ≃* K C e c hc :=
  MulEquiv.ofBijective (affine C e c hc).rangeRestrict
    ⟨fun _ _ h => affine_injective C e c hc (congrArg Subtype.val h),
      (affine C e c hc).rangeRestrict_surjective⟩
abbrev B := Image (rho (R := R) (I := J)) (K C e c hc)
abbrev imageTop := LinearSemidirectActualImageKernelChart.top
  (rho (R := R) (I := J)) (K C e c hc)
abbrev pi : T →* B C e c hc :=
  (imageTop C e c hc).comp (originalEquiv C e c hc).toMonoidHom
abbrev A := LinearSemidirectActualImageKernelChart.kernelModule
  (rho (R := R) (I := J)) (K C e c hc)

def E : OriginalKernelModuleChart (pi C e c hc) (A C e c hc) :=
  (LinearSemidirectActualImageKernelChart.originalKernelChart
    (rho (R := R) (I := J)) (K C e c hc)).ofSourceEquiv
      (imageTop C e c hc) (A C e c hc) (originalEquiv C e c hc)

 theorem pi_surjective : Function.Surjective (pi C e c hc) :=
  (projection (rho (R := R) (I := J)) (K C e c hc)).rangeRestrict_surjective.comp
    (originalEquiv C e c hc).surjective

def inclusion : Representation.IntertwiningMap (A C e c hc).ρ
    (BinaryPlaneCyclicWreathUniform.representation (B C e c hc)) :=
  LinearSemidirectActualImageKernelChart.inclusion
    (rho (R := R) (I := J)) (K C e c hc)

omit [Finite X] [DecidableEq J] in
 theorem inclusion_injective : Function.Injective (inclusion C e c hc) :=
  LinearSemidirectActualImageKernelChart.inclusion_injective
    (rho (R := R) (I := J)) (K C e c hc)

 theorem blocks_surjective : Function.Surjective
    ((PermutationalWreathProduct.rightHom :
      BinaryPlaneFunctionLinearAction.Frame (R := R) (I := J) →* R).comp
        (B C e c hc).subtype) := by
  intro r
  obtain ⟨b,hb⟩ := e.surjective r
  obtain ⟨u,hu⟩ := C.top.rangeRestrict_surjective b
  refine ⟨pi C e c hc u,?_⟩
  change e (C.top.rangeRestrict u)=r
  rw [hu,hb]

end SymmetricSubgroupAsymptotics.ProductBlockFrame.CanonicalQuartetKernel
