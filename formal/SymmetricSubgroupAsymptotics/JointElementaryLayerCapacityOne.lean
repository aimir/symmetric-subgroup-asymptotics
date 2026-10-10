import SymmetricSubgroupAsymptotics.JointElementaryLayerEnvelope
import SymmetricSubgroupAsymptotics.DualGeneratorSchurCapacity

/-!
# Capacity one from cyclic dual sections

The joint elementary-layer package deliberately separates its source exponent
from its finite fixed-top coefficient.  Consequently, once every literal
normal section has cyclic contragredient, the source exponent can be sharpened
to one without rebuilding the already proved fibre estimate.

This is the reusable bridge needed by the degree-three six- and twelve-block
identity comparator: the remaining isotype argument may prove cyclicity one
section at a time, while this file performs the uniform capacity assembly.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
variable {G B : Type} [Group G] [Finite G] [Group B] [Finite B]
variable (π : G →* B) (hπ : Function.Surjective π)
variable (A : Rep (ZMod p) B) [Finite A] [FiniteDimensional (ZMod p) A]
variable (E : OriginalKernelModuleChart π A)

namespace ElementaryLayerJointCapacityBound

/-- Replace the source exponent of a joint elementary-layer estimate by one
when every literal section has a cyclic contragredient.  The finite
fixed-top coefficient is retained literally. -/
noncomputable def sharpenToOne_of_sectionDualGenerated
    (H : ElementaryLayerJointCapacityBound p π hπ A E)
    (hcyclic : ∀ N : {N : Subgroup G // N.Normal},
      RepresentationGeneratedBy
        (E.sectionRepresentation π A N.1).ρ.dual 1) :
    ElementaryLayerJointCapacityBound p π hπ A E where
  capacity := 1
  capacity_nonneg := by norm_num
  section_capacity := by
    intro N
    letI : FiniteDimensional (ZMod p)
        (E.sectionRepresentation π A N.1) := by
      change FiniteDimensional (ZMod p)
        (A ⧸ E.normalSpace π A N.1)
      infer_instance
    simpa using representationSchurCapacity_le_of_dual_generated
      (E.sectionRepresentation π A N.1).ρ 1 (hcyclic N)
  coefficient := H.coefficient
  coefficient_nonneg := H.coefficient_nonneg
  fixed_top_fibre := H.fixed_top_fibre

@[simp] theorem sharpenToOne_of_sectionDualGenerated_capacity
    (H : ElementaryLayerJointCapacityBound p π hπ A E)
    (hcyclic : ∀ N : {N : Subgroup G // N.Normal},
      RepresentationGeneratedBy
        (E.sectionRepresentation π A N.1).ρ.dual 1) :
    (H.sharpenToOne_of_sectionDualGenerated p π hπ A E hcyclic).capacity = 1 :=
  rfl

@[simp] theorem sharpenToOne_of_sectionDualGenerated_coefficient
    (H : ElementaryLayerJointCapacityBound p π hπ A E)
    (hcyclic : ∀ N : {N : Subgroup G // N.Normal},
      RepresentationGeneratedBy
        (E.sectionRepresentation π A N.1).ρ.dual 1) :
    (H.sharpenToOne_of_sectionDualGenerated p π hπ A E hcyclic).coefficient =
      H.coefficient := rfl

end ElementaryLayerJointCapacityBound
end SymmetricSubgroupAsymptotics

end
