import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow32OriginalGeometry
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow32OriginalDegreeTwoSections
import SymmetricSubgroupAsymptotics.BinaryPairLargeSectionCharacter

/-!
# The actual retained pair section in row 32

For every original normal subgroup, its retained flip module is a
displayed quotient of the original correlated flip space. The literal
row-32 typewise theorem therefore bounds its scalar degree-two simple
types by two, over the unchanged original normal quotient.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveRow32OriginalPairSection

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open PrimitiveAffineDegreeTwoTwelveRow32OriginalGeometry

variable {p : PreE7PairActionClass 12}
  (R : DegreeTwoPairTopRealization DegreeTwoTwelvePairFiniteCatalogue.row32Interface p)

abbrev originalNatural : Representation (ZMod 2) (preE7PairAction 12 p)
    (Fin 12 → ZMod 2) :=
  inflatedRepresentation (topMap R)
    PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.representation

theorem originalNatural_apply (g : preE7PairAction 12 p) (v : Fin 12 → ZMod 2) :
    originalNatural R g v = R.frame.coordinateTopAction (R.frame.top.rangeRestrict g) v := by
  change permutationFunctionRepresentation (ZMod 2)
    DegreeTwoTwelvePairFiniteCatalogue.row32Interface.top (Fin 12) (topMap R g) v = _
  rw [R.module_action_eq]
  change R.frame.coordinateTopAction
    (R.topEquiv (R.topEquiv.symm (R.frame.top.rangeRestrict g))) v = _
  rw [R.topEquiv.apply_symm_apply]

def kernelSubrepresentation : Subrepresentation (originalNatural R) where
  toSubmodule := R.frame.kernelSpace
  apply_mem_toSubmodule := by
    intro g v hv
    rw [originalNatural_apply]
    exact R.frame.kernelSubrepresentation.apply_mem_toSubmodule _ hv

variable (N : Subgroup (preE7PairAction 12 p)) [N.Normal]

/-- The action of the actual original quotient on its retained pair kernel. -/
abbrev sectionQuotientRepresentation :
    Representation (ZMod 2) (preE7PairAction 12 p ⧸ N)
      (R.frame.kernelSpace ⧸ R.frame.normalSpace N) :=
  inflatedRepresentation (R.frame.zeroCutBase N) (R.frame.sectionRepresentation N)

/-- The original flip quotient map, with the original group action retained. -/
def sectionIntertwiner :
    (kernelSubrepresentation R).toRepresentation.IntertwiningMap
      (inflatedRepresentation (QuotientGroup.mk' N) (sectionQuotientRepresentation R N)) where
  toLinearMap := (R.frame.normalSpace N).mkQ
  isIntertwining' := by
    intro g
    apply LinearMap.ext
    intro v
    have h := Representation.IntertwiningMap.isIntertwining _ _
      (R.frame.sectionTopIntertwiner N) (R.frame.top.rangeRestrict g) v
    change (R.frame.normalSpace N).mkQ
        (R.frame.kernelTopPermutationSubrepresentation.toRepresentation
          (R.frame.top.rangeRestrict g) v) =
      R.frame.sectionRepresentation N
        (R.frame.sectionTopQuotient N (R.frame.top.rangeRestrict g))
        ((R.frame.normalSpace N).mkQ v) at h
    rw [R.frame.sectionTopQuotient_apply] at h
    have hact : (kernelSubrepresentation R).toRepresentation g v =
        R.frame.kernelTopPermutationSubrepresentation.toRepresentation
          (R.frame.top.rangeRestrict g) v := by
      apply Subtype.ext
      exact originalNatural_apply R g v.val
    change (R.frame.normalSpace N).mkQ
        ((kernelSubrepresentation R).toRepresentation g v) =
      R.frame.sectionRepresentation N (QuotientGroup.mk' (R.frame.top.ker ⊔ N) g)
        ((R.frame.normalSpace N).mkQ v)
    exact (congrArg (R.frame.normalSpace N).mkQ hact).trans h

theorem sectionIntertwiner_surjective : Function.Surjective (sectionIntertwiner R N) :=
  (R.frame.normalSpace N).mkQ_surjective

/-- Every displayed simple scalar degree-two target occurs at most twice
in the actual retained pair section, over the original normal quotient. -/
theorem section_multiplicity_le_two
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (sigma : Representation (ZMod 2) (preE7PairAction 12 p ⧸ N) W)
    [IsSimpleModule (ZMod 2)[preE7PairAction 12 p ⧸ N] sigma.asModule]
    (hdim : Module.finrank (ZMod 2) W = 2)
    (hEnd : Module.finrank (ZMod 2)
      (Module.End (ZMod 2)[preE7PairAction 12 p ⧸ N] sigma.asModule) = 2) :
    schurSocleMultiplicity (k := ZMod 2) (R := (ZMod 2)[preE7PairAction 12 p ⧸ N])
      (A := (sectionQuotientRepresentation R N).asModule) (X := sigma.asModule) ≤ 2 := by
  let pi := QuotientGroup.mk' N
  let sigmaG := inflatedRepresentation pi sigma
  letI : IsSimpleModule (ZMod 2)[preE7PairAction 12 p] sigmaG.asModule :=
    representation_comp_isSimpleModule pi (QuotientGroup.mk'_surjective N) sigma
  have hEndG : Module.finrank (ZMod 2)
      (Module.End (ZMod 2)[preE7PairAction 12 p] sigmaG.asModule) = 2 :=
    (representationEnd_finrank_comp_eq pi (QuotientGroup.mk'_surjective N) sigma).trans hEnd
  have h := PrimitiveAffineDegreeTwoTwelveRow32OriginalDegreeTwoSections.section_multiplicity_le_two
    (topMap R) (topMap_surjective R) (topMap_kernel_isPGroup R)
    (inflatedRepresentation pi (sectionQuotientRepresentation R N)) sigmaG
    hdim hEndG (kernelSubrepresentation R) (sectionIntertwiner R N)
    (sectionIntertwiner_surjective R N)
  rwa [schurSocleMultiplicity_comp_eq_representation pi
    (QuotientGroup.mk'_surjective N) sigma (sectionQuotientRepresentation R N)] at h

end PrimitiveAffineDegreeTwoTwelveRow32OriginalPairSection
end SymmetricSubgroupAsymptotics

end
