import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalRoots
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticSourceCoefficients
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticSourceImageRange
import SymmetricSubgroupAsymptotics.CFSGSubmoduleActionKernelTransport

/-! Transporting only the literal source Cartan matrix leaves the root
units unchanged. The raw elementary group therefore acts on the SAME
transported original image. Kernel comparison uses shared conjugation
values, without unfolding a dependent image equivalence. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticTransportedAction
open CFSG.Models.Chevalley CFSGSerreQuadraticMatrix
variable {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (h : A=B) (D : Data A I)

theorem transported_root_eq (K : Type*) [CommRing K] (neg : Bool) (i : Fin n) (t : K) :
    canonicalRoot (transportSource h D) K neg i t=canonicalRoot D K neg i t := by
  cases h
  rfl

variable (K : Type) [Field K]
    (hfour : ∀neg i (x : Space B K),
      fieldSecond (transportSource h D) K neg i*baseChange (transportSource h D) K x*
        fieldSecond (transportSource h D) K neg i=0)

private theorem root_val (neg : Bool) (i : Fin n) (t : K) :
    (canonicalRoot D K neg i t : Matrix I I K)=
      1+t • fieldRoot (transportSource h D) K neg i+
        t^2 • fieldSecond (transportSource h D) K neg i := by
  rw [←transported_root_eq h D K neg i t]
  exact canonicalRoot_val (transportSource h D) K neg i t

private theorem root_inv_val (neg : Bool) (i : Fin n) (t : K) :
    (↑((canonicalRoot D K neg i t)⁻¹) : Matrix I I K)=
      1-t • fieldRoot (transportSource h D) K neg i+
        t^2 • fieldSecond (transportSource h D) K neg i := by
  rw [←transported_root_eq h D K neg i t]
  exact canonicalRoot_inv_val (transportSource h D) K neg i t

def matrixAction : canonicalElementaryGroup D K→*
    ((baseChange (transportSource h D) K).range≃ₗ[K](baseChange (transportSource h D) K).range) :=
  elementaryImageAction (transportSource h D) K (canonicalRoot D K)
    (root_val h D K) (root_inv_val h D K) hfour

theorem matrixAction_apply (g : canonicalElementaryGroup D K)
    (y : (baseChange (transportSource h D) K).range) :
    (matrixAction h D K hfour g y).val=(g.val : Matrix I I K)*y.val*(↑(g.val⁻¹) : Matrix I I K) := rfl

theorem source_root_action (neg : Bool) (i : Fin n) (t : K) :
    imageRepresentation (transportSource h D) K
        (CFSGSerreModelRootGeneration.modelRoot B K neg i t)=
      matrixAction h D K hfour (canonicalElementaryRoot D K neg i t) :=
  source_root_action_eq_elementary (transportSource h D) K (canonicalRoot D K)
    (root_val h D K) (root_inv_val h D K) hfour neg i t

theorem action_ranges_eq : (imageRepresentation (transportSource h D) K).range=
    (matrixAction h D K hfour).range :=
  CFSGSerreQuadraticMatrix.action_ranges_eq (transportSource h D) K (canonicalRoot D K)
    (root_val h D K) (root_inv_val h D K) hfour

theorem matrixAction_kernel_le_center
    (hraw : ∀neg i (x : Space A K),fieldSecond D K neg i*baseChange D K x*fieldSecond D K neg i=0)
    (hker : (canonicalImageAction D K hraw).ker≤Subgroup.center (canonicalElementaryGroup D K)) :
    (matrixAction h D K hfour).ker≤Subgroup.center (canonicalElementaryGroup D K) := by
  apply le_trans _ hker
  exact CFSGSubmoduleActionKernelTransport.kernel_le_of_shared_values
    (baseChange (transportSource h D) K).range (baseChange D K).range
    (transportSource_baseChange_range_eq h D K) (matrixAction h D K hfour)
    (canonicalImageAction D K hraw)
    (fun g y=>(g.val : Matrix I I K)*y*(↑(g.val⁻¹) : Matrix I I K))
    (matrixAction_apply h D K hfour) (fun _ _=>rfl)

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticTransportedAction
