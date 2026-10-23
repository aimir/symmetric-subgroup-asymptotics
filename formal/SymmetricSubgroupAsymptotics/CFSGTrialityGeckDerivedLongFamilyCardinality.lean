import SymmetricSubgroupAsymptotics.CFSGTrialityGeckDerivedLongLine
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedRootFamilyCardinality
import SymmetricSubgroupAsymptotics.CFSGConjugateFamilyTransport

/-! The conjugate family in the SAME original derived action image is
a cardinality factor of the already counted full fixed-matrix family. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckDerivedLongFamilyCardinality
open CFSGTrialityGeckDerivedLongLine CFSGTrialityGeckFixedLongLine
open CFSGTrialityGeckFixedDerivedMatrixLift CFSGTrialityGeckFixedPositiveImageSylow
open CFSGTrialityGeckDerivedSylowNormalizer CFSGTrialityGeckSourceWordAction
open CFSGTrialityGeckLongDerivedImage CFSGTrialityGeckFixedRootFamilyCardinality
open CFSGTrialityGeckSectionHeightMembership CFSGTrialityD4PositiveRootOrbits
open CFSGConjugateFamilyTransport

local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) :=
  Classical.decEq _
local instance (q : CFSG.PrimePower) : Finite (DerivedImage q) :=
  Finite.of_surjective (preimageToImage q) (preimageToImage_surjective q)

theorem derivedLongLine_ambient_image (q : CFSG.PrimePower) :
    (derivedLongLine q).map (DerivedImage q).subtype =
      (fixedLongLine q).map (fixedMatrixAction q) := by
  apply Subgroup.ext
  intro y
  constructor
  · rintro ⟨z,⟨x,rfl⟩,rfl⟩
    exact ⟨x.val,x.property,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨longToDerived q ⟨x,hx⟩,⟨⟨x,hx⟩,rfl⟩,rfl⟩

def derivedLongFamily (q : CFSG.PrimePower) :=
  Set.range (fun g : DerivedImage q =>
    (derivedLongLine q).map (MulAut.conj g).toMonoidHom)

theorem derived_long_family_card_le_fixed (q : CFSG.PrimePower) :
    Nat.card (derivedLongFamily q) ≤ Nat.card (fixedRootFamily q) := by
  let B := (fixedLongLine q).map (fixedMatrixAction q)
  calc
    _ ≤ Nat.card (Set.range (fun g : DerivedImage q =>
        ((derivedLongLine q).map (DerivedImage q).subtype).map
          (MulAut.conj g.val).toMonoidHom)) :=
      card_subgroup_family_le (DerivedImage q) (derivedLongLine q)
    _ = Nat.card (Set.range (fun g : DerivedImage q =>
        B.map (MulAut.conj g.val).toMonoidHom)) := by rw [derivedLongLine_ambient_image]
    _ ≤ Nat.card (Set.range (fun g : FixedMatrixGroup q =>
        B.map (MulAut.conj (fixedMatrixAction q g)).toMonoidHom)) :=
      card_family_le_of_range (fixedMatrixAction q) (DerivedImage q) B
        (derived_action_range_le_fixed_matrix_action q)
    _ ≤ Nat.card (fixedRootFamily q) :=
      card_comap_image_family_le (fixedRawInclusion q) (fixedMatrixAction q)
        (RootLine (q.Extension 3) (longRoot 2))

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckDerivedLongFamilyCardinality
