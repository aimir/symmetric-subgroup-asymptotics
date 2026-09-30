import SymmetricSubgroupAsymptotics.BinaryCarrierCrossVariableWordReconstruction

/-!
# Dependent intrinsic-key physical reconstruction

The canonical orbit word of an actual residual subgroup has an index type,
coordinate actions, and carrier products which vary with its orbit profile.
They must not be forced into one padded ambient product.  This file gives the
type-theoretic aggregation theorem needed instead.

The proof-level source type may depend on the already-counted pair consisting
of a bounded decoration and a physical target.  A dependent source code is
injective before physical realization, and the realization is injective
inside every fixed key.  If each code realizes its own physical target, then
the counted decoration/target pair is itself injective.  No cardinality of the
dependent key family is charged.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierDependentIntrinsicPhysicalEncoding

open SymmetricSubgroupAsymptotics.BinaryCarrierCrossVariableWordReconstruction

variable {Actual Decoration Physical : Type*}
  (blocks : Actual → Decoration) (target : Actual → Physical)
  (Source : Decoration × Physical → Type*)

/-- Package an actual source in the dependent type selected by its counted
decoration/target key. -/
def dependentCode
    (code : ∀ x, Source (blocks x,target x)) (x : Actual) :
    Σ k : Decoration × Physical, Source k :=
  ⟨(blocks x,target x),code x⟩

/-- A dependent source code followed by a fibrewise injective physical
realization makes the counted decoration/target pair injective. -/
theorem blocks_target_injective_of_dependent_intrinsic_code
    (code : ∀ x, Source (blocks x,target x))
    (codeSigmaInjective : Function.Injective
      (dependentCode blocks target Source code))
    (physicalize : ∀ k, Source k → Physical)
    (targetFactor : ∀ x,
      physicalize (blocks x,target x) (code x) = target x)
    (physicalizeInjective : ∀ k, Function.Injective (physicalize k)) :
    Function.Injective (fun x => (blocks x,target x)) := by
  intro x y hkey
  apply codeSigmaInjective
  apply sigmaDecoration_target_injective physicalize physicalizeInjective
  apply Prod.ext
  · exact hkey
  · calc
      physicalize (blocks x,target x) (code x) = target x := targetFactor x
      _ = target y := congrArg Prod.snd hkey
      _ = physicalize (blocks y,target y) (code y) := (targetFactor y).symm

end SymmetricSubgroupAsymptotics.BinaryCarrierDependentIntrinsicPhysicalEncoding
