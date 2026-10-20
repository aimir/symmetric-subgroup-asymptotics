import SymmetricSubgroupAsymptotics.BinaryPairInvariantAxes
import Mathlib.RepresentationTheory.Coinvariants

/-! A literal equality of the top permutation subgroup transports only
its type. The underlying physical axis and coordinates remain identical.
This is the bridge from original pair frames to the checked degree-eight
natural-module registries after point-conjugating the pair labels. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin w))
  (H : Subgroup (Equiv.Perm (Fin w))) (hH : F.top.range = H)

/-- The actual N-axis regarded under the identical literal model top. -/
def literalTopAxis (N : Subgroup U) [N.Normal] :
    Subrepresentation ((binaryPermutationRepresentation w).comp H.subtype) := by
  subst H
  exact F.axisSubrepresentation N

theorem literalTopAxis_space (N : Subgroup U) [N.Normal] :
    (F.literalTopAxis H hH N).toSubmodule = F.ambientAxis N := by
  subst H
  rfl

theorem literalTopAxis_head (N : Subgroup U) [N.Normal] :
    Module.finrank (ZMod 2) (F.literalTopAxis H hH N).toRepresentation.Coinvariants =
      Module.finrank (ZMod 2) (F.axisSubrepresentation N).toRepresentation.Coinvariants := by
  subst H
  rfl

theorem literalTopAxis_radical (N : Subgroup U) [N.Normal] :
    (Representation.Coinvariants.ker (F.literalTopAxis H hH N).toRepresentation).map
        (F.literalTopAxis H hH N).toSubmodule.subtype =
      (Representation.Coinvariants.ker (F.axisSubrepresentation N).toRepresentation).map
        (F.axisSubrepresentation N).toSubmodule.subtype := by
  subst H
  rfl

/-- The full correlated original kernel, with the identical model action. -/
def literalTopKernel :
    Subrepresentation ((binaryPermutationRepresentation w).comp H.subtype) := by
  subst H
  exact F.kernelSubrepresentation

theorem literalTopKernel_space :
    (F.literalTopKernel H hH).toSubmodule = F.kernelSpace := by
  subst H
  rfl

theorem literalTopKernel_head :
    Module.finrank (ZMod 2) (F.literalTopKernel H hH).toRepresentation.Coinvariants =
      Module.finrank (ZMod 2) F.kernelSubrepresentation.toRepresentation.Coinvariants := by
  subst H
  rfl

theorem literalTopKernel_radical :
    (Representation.Coinvariants.ker (F.literalTopKernel H hH).toRepresentation).map
        (F.literalTopKernel H hH).toSubmodule.subtype =
      (Representation.Coinvariants.ker F.kernelSubrepresentation.toRepresentation).map
        F.kernelSubrepresentation.toSubmodule.subtype := by
  subst H
  rfl

end SymmetricSubgroupAsymptotics.BinaryPairFrame
