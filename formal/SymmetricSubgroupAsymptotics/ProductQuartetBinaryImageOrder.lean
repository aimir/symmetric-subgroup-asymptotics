import SymmetricSubgroupAsymptotics.ProductQuartetAffineLinearProjection
import SymmetricSubgroupAsymptotics.BinaryPlaneWreathLinearAction
import SymmetricSubgroupAsymptotics.LinearSemidirectActualImageKernelChart
import SymmetricSubgroupAsymptotics.QuartetOddKernelBinaryQuotientOrder
import SymmetricSubgroupAsymptotics.ProductBlockFrameTransitiveTop

/-! Every actual binary surjective image of the original quartet action
has order at most 128. Its correlated translation module is constructed
from the actual affine image, rather than supplied as a capacity premise. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame
open BinaryPlanePermutationAffineEquiv
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneWreathActualOddKernel
open LinearSemidirectSubgroupKernelChart
open BinaryPlaneWreathLinearAction (rho)

variable {X : Type} [Finite X] {T : Subgroup (Equiv.Perm X)}
  (C : ProductBlockFrame T (Fin 4) Plane)

 theorem binary_image_card_le [MulAction.IsPretransitive T X]
    (hO : oddKernel C.quartetLinearImage≠⊥)
    {Q : Type} [Group Q] (phi : T →* Q) (hphi : Function.Surjective phi)
    (hQ : IsPGroup 2 Q) : Nat.card Q≤2^7 := by
  let f : T →* LinearSemidirectCoprimeSocleBounds.Model rho := C.affineCoordinates
  let K := f.range
  let e : T ≃* K := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun _ _ h => C.affineCoordinates_injective (congrArg Subtype.val h),
      f.rangeRestrict_surjective⟩
  let B := Image rho K
  let pi := LinearSemidirectActualImageKernelChart.top rho K
  let A := LinearSemidirectActualImageKernelChart.kernelModule rho K
  let E := LinearSemidirectActualImageKernelChart.originalKernelChart rho K
  have hB : B=C.quartetLinearImage := by
    apply le_antisymm
    · rintro b ⟨k,hk⟩
      obtain ⟨u,hu⟩ := k.property
      refine ⟨u,?_⟩
      change (f u).right=b
      rw [hu]
      exact hk
    · rintro b ⟨u,hu⟩
      exact ⟨e u,hu⟩
  have hodd : oddKernel B≠⊥ := by rw [hB]; exact hO
  have htrans : ∀ i k : Fin 4,∃ b : B,(b : Frame).right • i=k := by
    intro i k
    obtain ⟨g,hg⟩ := C.top_range_transitive
      (fun x y => MulAction.exists_smul_eq T x y) i k
    obtain ⟨u,hu⟩ := g.property
    refine ⟨pi (e u),?_⟩
    change C.top u i=k
    rw [hu]
    exact hg
  let j : Representation.IntertwiningMap A.ρ
      (BinaryPlaneCyclicWreathUniform.representation B) :=
    LinearSemidirectActualImageKernelChart.inclusion rho K
  have hj : Function.Injective j :=
    LinearSemidirectActualImageKernelChart.inclusion_injective rho K
  let psi := phi.comp e.symm.toMonoidHom
  have hpsi : Function.Surjective psi := hphi.comp e.symm.surjective
  let eqQ := QuotientGroup.quotientKerEquivOfSurjective psi hpsi
  have hp : IsPGroup 2 (K ⧸ psi.ker) :=
    hQ.of_surjective eqQ.symm.toMonoidHom eqQ.symm.surjective
  have hc := QuartetOddKernelBinaryQuotientOrder.quotient_card_le B hodd htrans
    pi (projection rho K).rangeRestrict_surjective A E j hj psi.ker hp
  rw [Nat.card_congr eqQ.toEquiv] at hc
  exact hc

end SymmetricSubgroupAsymptotics.ProductBlockFrame
