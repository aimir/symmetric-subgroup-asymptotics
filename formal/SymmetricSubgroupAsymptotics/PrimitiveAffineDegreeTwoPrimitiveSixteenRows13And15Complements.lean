import SymmetricSubgroupAsymptotics.FivePointSixConfigurationAction
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRows16And17Complements

/-! The alternative S5/A5 complements act through the exact six-label
configuration action. The displayed binary charts bind both generators
to the unchanged original row13/15 permutations. Surjective source maps
suffice to transport the normal chains; no complement-order assumption
or abstract replacement of the original action is made. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPrimitiveSixteenRows13And15Complements

open BinarySixDeletedRepresentation
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

abbrev sourceCycle := FivePointSixConfigurationAction.a
abbrev source13 := FivePointSixConfigurationAction.second13
abbrev source15 := FivePointSixConfigurationAction.second15

/-- Columns are masks [1,9,13,15] in the original binary labels. -/
def chart13 : LinearGroup where
  toFun v := ![v 0 + v 1 + v 2 + v 3, v 3, v 2 + v 3, v 1 + v 2 + v 3]
  invFun v := ![v 0 + v 3, v 2 + v 3, v 1 + v 2, v 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

/-- Columns are masks [1,11,6,8]. -/
def chart15 : LinearGroup where
  toFun v := ![v 0 + v 1, v 1 + v 2, v 2, v 1 + v 3]
  invFun v := ![v 0 + v 1 + v 2, v 1 + v 2, v 2, v 1 + v 2 + v 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

def hom13 : Equiv.Perm (Fin 5) →* LinearGroup :=
  (conjugateHom chart13).comp FivePointSixConfigurationAction.hom
def hom15 : Equiv.Perm (Fin 5) →* LinearGroup :=
  (conjugateHom chart15).comp FivePointSixConfigurationAction.hom

theorem hom13_alpha : hom13 sourceCycle = conjugateHom chart13 alpha := by
  change conjugateHom chart13 (FivePointSixConfigurationAction.hom sourceCycle) = _
  rw [FivePointSixConfigurationAction.hom_a]

theorem hom13_beta : hom13 source13 =
    conjugateHom chart13 FivePointSixConfigurationAction.beta13 := by
  change conjugateHom chart13 (FivePointSixConfigurationAction.hom source13) = _
  rw [FivePointSixConfigurationAction.hom_second13]

theorem hom15_alpha : hom15 sourceCycle = conjugateHom chart15 alpha := by
  change conjugateHom chart15 (FivePointSixConfigurationAction.hom sourceCycle) = _
  rw [FivePointSixConfigurationAction.hom_a]

theorem hom15_beta : hom15 source15 =
    conjugateHom chart15 FivePointSixConfigurationAction.beta15 := by
  change conjugateHom chart15 (FivePointSixConfigurationAction.hom source15) = _
  rw [FivePointSixConfigurationAction.hom_second15]

theorem hom13_alpha_original :
    BinaryFourAffineImage.linearPerm (hom13 sourceCycle) =
      DegreeTwoPrimitiveSixteenInterfaces.row13Generators 0 := by
  rw [hom13_alpha]
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem hom13_beta_original :
    BinaryFourAffineImage.linearPerm (hom13 source13) =
      DegreeTwoPrimitiveSixteenInterfaces.row13Generators 1 := by
  rw [hom13_beta]
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem hom15_alpha_original :
    BinaryFourAffineImage.linearPerm (hom15 sourceCycle) =
      DegreeTwoPrimitiveSixteenInterfaces.row15Generators 0 := by
  rw [hom15_alpha]
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem hom15_beta_original :
    BinaryFourAffineImage.linearPerm (hom15 source15) =
      DegreeTwoPrimitiveSixteenInterfaces.row15Generators 1 := by
  rw [hom15_beta]
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

abbrev R13 : Subgroup LinearGroup :=
  Subgroup.closure ({hom13 sourceCycle, hom13 source13} : Set LinearGroup)
abbrev R15 : Subgroup LinearGroup :=
  Subgroup.closure ({hom15 sourceCycle, hom15 source15} : Set LinearGroup)

theorem alpha_mem13 : hom13 sourceCycle ∈ R13 := Subgroup.subset_closure (by simp)
theorem beta_mem13 : hom13 source13 ∈ R13 := Subgroup.subset_closure (by simp)
theorem alpha_mem15 : hom15 sourceCycle ∈ R15 := Subgroup.subset_closure (by simp)
theorem beta_mem15 : hom15 source15 ∈ R15 := Subgroup.subset_closure (by simp)

def evenHom15 : alternatingGroup (Fin 5) →* LinearGroup :=
  hom15.comp (alternatingGroup (Fin 5)).subtype

theorem hom13_range : hom13.range = R13 := by
  rw [MonoidHom.range_eq_map, ← FivePointSixConfigurationAction.symmetric_generators,
    MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton]

theorem evenHom15_range : evenHom15.range = R15 := by
  change (hom15.comp (alternatingGroup (Fin 5)).subtype).range = R15
  rw [MonoidHom.range_comp, Subgroup.range_subtype,
    ← FivePointSixConfigurationAction.alternating_generators, MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton]

def complementMap13 : Equiv.Perm (Fin 5) →* R13 :=
  (MulEquiv.subgroupCongr hom13_range).toMonoidHom.comp hom13.rangeRestrict
def complementMap15 : alternatingGroup (Fin 5) →* R15 :=
  (MulEquiv.subgroupCongr evenHom15_range).toMonoidHom.comp evenHom15.rangeRestrict

theorem complementMap13_surjective : Function.Surjective complementMap13 :=
  (MulEquiv.subgroupCongr hom13_range).surjective.comp hom13.rangeRestrict_surjective
theorem complementMap15_surjective : Function.Surjective complementMap15 :=
  (MulEquiv.subgroupCongr evenHom15_range).surjective.comp evenHom15.rangeRestrict_surjective

theorem linear_normal_total13 (A B : Subgroup R13) (hA : A.Normal) (hB : B.Normal) :
    A ≤ B ∨ B ≤ A :=
  normalSubgroups_total_of_surjective (G := Equiv.Perm (Fin 5)) (H := R13)
    complementMap13 complementMap13_surjective
    (AlternatingSymmetricNormalChain.symmetric_normal_total (X := Fin 5) (by norm_num)) A B hA hB

theorem linear_normal_total15 (A B : Subgroup R15) (hA : A.Normal) (hB : B.Normal) :
    A ≤ B ∨ B ≤ A :=
  normalSubgroups_total_of_surjective (G := alternatingGroup (Fin 5)) (H := R15)
    complementMap15 complementMap15_surjective
    (AlternatingSymmetricNormalChain.alternating_normal_total (X := Fin 5) (by norm_num)) A B hA hB

theorem irreducible13 : AffineModel.Irreducible R13 := by
  change AffineModel.Irreducible (Subgroup.closure ({hom13 sourceCycle, hom13 source13} : Set LinearGroup))
  rw [hom13_alpha, hom13_beta]
  exact PrimitiveAffineDegreeTwoPrimitiveSixteenRows16And17Complements.irreducible_pair _ _

theorem irreducible15 : AffineModel.Irreducible R15 := by
  change AffineModel.Irreducible (Subgroup.closure ({hom15 sourceCycle, hom15 source15} : Set LinearGroup))
  rw [hom15_alpha, hom15_beta]
  exact PrimitiveAffineDegreeTwoPrimitiveSixteenRows16And17Complements.irreducible_pair _ _

end PrimitiveAffineDegreeTwoPrimitiveSixteenRows13And15Complements
end SymmetricSubgroupAsymptotics

end
