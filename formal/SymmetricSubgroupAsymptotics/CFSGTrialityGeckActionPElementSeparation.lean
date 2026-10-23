import SymmetricSubgroupAsymptotics.CFSGTrialityGeckAmbientPositiveSylow
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckPositiveActionInjective
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMatrixActionCentralKernel
import SymmetricSubgroupAsymptotics.CFSGCentralKernelPElements

/-! The actual common-image action separates ALL defining-characteristic
p-elements. This keeps opposite intersections intact; no faithfulness of
the entire rational or integral Lie representation is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckActionPElementSeparation
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckAmbientPositiveSylow CFSGTrialityGeckPositiveActionInjective
open CFSGTrialityGeckMatrixActionCentralKernel

variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]

theorem ambientSylow_action_injective : Function.Injective ((matrixAction K).comp
    (ambientPositiveSylow K p : Subgroup (MatrixGroup K)).subtype) := by
  intro x y he
  have hx : x.val.val ∈ Positive K := x.property
  have hy : y.val.val ∈ Positive K := y.property
  have hp : positiveAction K ⟨x.val.val,hx⟩ = positiveAction K ⟨y.val.val,hy⟩ := he
  have hh := positiveAction_injective K p hp
  have hv : x.val.val = y.val.val := congrArg (fun u : Positive K => u.val) hh
  exact Subtype.ext (Subtype.ext hv)

theorem matrixAction_eq_of_p_elements (x y : MatrixGroup K)
    (hx : ∃ a : ℕ,x ^ p ^ a = 1) (hy : ∃ b : ℕ,y ^ p ^ b = 1)
    (he : matrixAction K x = matrixAction K y) : x = y :=
  CFSGCentralKernelPElements.eq_of_p_elements (matrixAction K) (ambientPositiveSylow K p)
    (ambientSylow_action_injective K p) (matrixAction_kernel_le_center K) x y hx hy he

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckActionPElementSeparation
